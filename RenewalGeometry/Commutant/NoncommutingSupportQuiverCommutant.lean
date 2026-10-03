/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.Commutant.ReciprocalWedderburnKronecker
import RenewalGeometry.Commutant.GraphSupportPolarDuality
import RenewalGeometry.Commutant.SMSTCommutant

/-!
# The noncommuting-support quiver theorem (`thm:quiver`)

Covers `def:multiplicity-quiver` and `thm:quiver` of the spacetime–gauge duality paper.

**Isotypic carrier.**  On `𝓜 ≅ ⊕_a V_a ⊗ N_a` (the carrier `Σ a, V a × N a`) the support
algebra is `𝒮_F = ⊕_a B(V_a) ⊗ I_{N_a}` (`actionBlockSet V N`).  For a finite `*`-closed family
`T = (T_j)` of further operators, the `(b, a)` block of `T_j` is expanded in the
Hilbert–Schmidt orthonormal matrix-unit basis `E^{ba}_{(v_b, v_a)}` of `B(V_a, V_b)`:
`(T_j)_{ba} = ∑ E^{ba}_{(v_b,v_a)} ⊗ B^{ba}_{j,(v_b,v_a)}` (`quiverCoeff`).  The arrow space
`𝔅_{ba}` is the span over `j` of the slices `(φ ⊗ id)((T_j)_{ba})` for all functionals
`φ ∈ B(V_a, V_b)^*` (`quiverArrowSpace`); `quiverArrowSpace_eq_span_coeff` identifies it with
the span of the basis coefficients.  `IsQuiverEnd` is `End 𝔔_F(T)`.

* `matCommutant_quiverGenerators` / `quiver_commutant_isotypic` — **`eq:quiver-commutant`**:
  `C^*(𝒮_F, T)' = {⊕_a I_{V_a} ⊗ X_a : (X_a) ∈ End 𝔔_F(T)}`.  The first step of the paper's
  proof (an operator commuting with `𝒮_F` is block-central) is *proved* via the Kronecker cut
  `matCommutant_actionBlockSet`, and the commutant of the generated `C^*`-algebra is reduced to
  the generators by `matCommutant_starAlgebra_adjoin`.
* `blockCentral` is an injective unital `*`-homomorphism (`blockCentral_mul`,
  `blockCentral_one`, `blockCentral_conjTranspose`, `blockCentral_injective`), so the
  identification is an algebra isomorphism `C^*(𝒮_F,T)' ≅ End 𝔔_F(T)`.
* `quiver_form_eq` / `quiver_form_eq_zero_iff` — **`eq:quiver-form`** and its kernel.
* `quiver_commutant` — the statement for an arbitrary unital `*`-subalgebra `𝒮_F ⊆ M_n(ℂ)`
  (e.g. `C^*(Z_λ, supp F_e^*F_e, supp F_eF_e^*)`): its canonical isotypic decomposition is
  produced by `reciprocal_wedderburn` (a unitary `W`), and conjugation by `W` carries
  `C^*(𝒮_F, T)'` onto the block-central realization of `End 𝔔_F(W^* T W)`.
-/

open Matrix Kronecker

namespace RenewalGeometry

namespace NoncommutingSupportQuiver

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {V N : ι → Type} [∀ a, Fintype (V a)] [∀ a, DecidableEq (V a)]
  [∀ a, Fintype (N a)] [∀ a, DecidableEq (N a)]

/-! ### Block-central operators -/

/-- The block-central operator `⊕_a I_{V_a} ⊗ X_a`. -/
def blockCentral (X : ∀ a, Matrix (N a) (N a) ℂ) :
    Matrix (Σ a, V a × N a) (Σ a, V a × N a) ℂ :=
  blockDiagonal' fun a => (1 : Matrix (V a) (V a) ℂ) ⊗ₖ X a

theorem blockCentral_mul (X Y : ∀ a, Matrix (N a) (N a) ℂ) :
    (blockCentral (V := V) (X * Y)) = blockCentral (V := V) X * blockCentral Y := by
  unfold blockCentral
  rw [← blockDiagonal'_mul]
  congr 1
  funext a
  rw [← mul_kronecker_mul, Matrix.one_mul]
  rfl

theorem blockCentral_one :
    blockCentral (V := V) (1 : ∀ a, Matrix (N a) (N a) ℂ) = 1 := by
  unfold blockCentral
  rw [← blockDiagonal'_one]
  congr 1
  funext a
  simp only [Pi.one_apply, Matrix.one_kronecker_one]

theorem blockCentral_conjTranspose (X : ∀ a, Matrix (N a) (N a) ℂ) :
    (blockCentral (V := V) X)ᴴ = blockCentral (V := V) (star X) := by
  unfold blockCentral
  rw [blockDiagonal'_conjTranspose]
  congr 1
  funext a
  rw [conjTranspose_kronecker, conjTranspose_one]
  rfl

theorem blockCentral_injective (hV : ∀ a, Nonempty (V a)) :
    Function.Injective (blockCentral (V := V) (N := N)) := by
  intro X Y h
  funext a
  ext i j
  obtain ⟨v⟩ := hV a
  have := congrFun (congrFun h ⟨a, (v, i)⟩) ⟨a, (v, j)⟩
  simpa [blockCentral, Matrix.kroneckerMap_apply] using this

/-- The multiplicity algebra `⊕_a 1 ⊗ M_{N_a}` is exactly the range of `blockCentral`. -/
theorem multBlockSet_eq_range :
    multBlockSet V N = Set.range (blockCentral (V := V) (N := N)) := by
  ext A
  constructor
  · rintro ⟨Y, rfl⟩
    exact ⟨Y, rfl⟩
  · rintro ⟨Y, rfl⟩
    exact ⟨Y, rfl⟩

/-! ### Quiver data of a family -/

/-- The Hilbert–Schmidt matrix-unit coefficient `B^{ba}_{(v_b,v_a)}` of the `(b, a)` block of
`T`: `T_{ba} = ∑_{v_b,v_a} E_{v_b v_a} ⊗ B^{ba}_{(v_b,v_a)}`. -/
def quiverCoeff (T : Matrix (Σ a, V a × N a) (Σ a, V a × N a) ℂ) (b a : ι) (vb : V b)
    (va : V a) : Matrix (N b) (N a) ℂ :=
  Matrix.of fun nb na => T ⟨b, (vb, nb)⟩ ⟨a, (va, na)⟩

/-- The slice `(φ ⊗ id)(T_{ba})` of the `(b, a)` block by a functional `φ ∈ B(V_a, V_b)^*`. -/
def quiverSlice {b a : ι} (φ : Matrix (V b) (V a) ℂ →ₗ[ℂ] ℂ)
    (T : Matrix (Σ a, V a × N a) (Σ a, V a × N a) ℂ) : Matrix (N b) (N a) ℂ :=
  Matrix.of fun nb na => φ (Matrix.of fun vb va => T ⟨b, (vb, nb)⟩ ⟨a, (va, na)⟩)

theorem quiverSlice_eq_sum (b a : ι) (φ : Matrix (V b) (V a) ℂ →ₗ[ℂ] ℂ)
    (T : Matrix (Σ a, V a × N a) (Σ a, V a × N a) ℂ) :
    quiverSlice (N := N) φ T =
      ∑ vb, ∑ va, φ (Matrix.single vb va 1) • quiverCoeff T b a vb va := by
  ext nb na
  simp only [quiverSlice, quiverCoeff, Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul]
  conv_lhs => rw [Matrix.matrix_eq_sum_single
    (Matrix.of fun vb va => T ⟨b, (vb, nb)⟩ ⟨a, (va, na)⟩)]
  rw [map_sum]
  refine Finset.sum_congr rfl fun vb _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun va _ => ?_
  rw [show ∀ x : ℂ, Matrix.single vb va x = x • Matrix.single vb va (1 : ℂ) from
    fun x => by rw [Matrix.smul_single, smul_eq_mul, mul_one], map_smul, smul_eq_mul,
    Matrix.of_apply, mul_comm]

theorem quiverCoeff_eq_slice (b a : ι) (vb : V b) (va : V a)
    (T : Matrix (Σ a, V a × N a) (Σ a, V a × N a) ℂ) :
    quiverCoeff T b a vb va = quiverSlice (Matrix.entryLinearMap ℂ ℂ vb va) T := by
  ext nb na
  simp [quiverCoeff, quiverSlice]

variable {J : Type*} [Fintype J]

/-- **`def:multiplicity-quiver`**: the arrow space
`𝔅_{ba} = span_{T ∈ 𝐓} {(φ ⊗ id)(T_{ba}) : φ ∈ B(V_a, V_b)^*}`. -/
def quiverArrowSpace (T : J → Matrix (Σ a, V a × N a) (Σ a, V a × N a) ℂ) (b a : ι) :
    Submodule ℂ (Matrix (N b) (N a) ℂ) :=
  Submodule.span ℂ (Set.range fun p : J × (Matrix (V b) (V a) ℂ →ₗ[ℂ] ℂ) =>
    quiverSlice (b := b) (a := a) p.2 (T p.1))

/-- The arrow space is spanned by the Hilbert–Schmidt basis coefficients. -/
theorem quiverArrowSpace_eq_span_coeff (T : J → Matrix (Σ a, V a × N a) (Σ a, V a × N a) ℂ)
    (b a : ι) :
    quiverArrowSpace T b a =
      Submodule.span ℂ (Set.range fun p : J × V b × V a => quiverCoeff (T p.1) b a p.2.1 p.2.2) := by
  apply le_antisymm
  · rw [quiverArrowSpace, Submodule.span_le]
    rintro _ ⟨⟨j, φ⟩, rfl⟩
    show quiverSlice φ (T j) ∈ _
    rw [quiverSlice_eq_sum]
    refine Submodule.sum_mem _ fun vb _ => Submodule.sum_mem _ fun va _ => ?_
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(j, vb, va), rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨⟨j, vb, va⟩, rfl⟩
    show quiverCoeff (T j) b a vb va ∈ _
    rw [quiverCoeff_eq_slice]
    exact Submodule.subset_span ⟨(j, Matrix.entryLinearMap ℂ ℂ vb va), rfl⟩

/-- **`End 𝔔_F(T)`**: families `(X_a)` with `X_b B = B X_a` for every `B ∈ 𝔅_{ba}`. -/
def IsQuiverEnd (T : J → Matrix (Σ a, V a × N a) (Σ a, V a × N a) ℂ)
    (X : ∀ a, Matrix (N a) (N a) ℂ) : Prop :=
  ∀ b a, ∀ B ∈ quiverArrowSpace T b a, X b * B = B * X a

/-- Membership in `End 𝔔_F(T)` reduces to the finitely many coefficient equations. -/
theorem isQuiverEnd_iff_coeff (T : J → Matrix (Σ a, V a × N a) (Σ a, V a × N a) ℂ)
    (X : ∀ a, Matrix (N a) (N a) ℂ) :
    IsQuiverEnd T X ↔ ∀ j b a (vb : V b) (va : V a),
      X b * quiverCoeff (T j) b a vb va = quiverCoeff (T j) b a vb va * X a := by
  constructor
  · intro h j b a vb va
    apply h b a
    rw [quiverArrowSpace_eq_span_coeff]
    exact Submodule.subset_span ⟨(j, vb, va), rfl⟩
  · intro h b a B hB
    rw [quiverArrowSpace_eq_span_coeff] at hB
    induction hB using Submodule.span_induction with
    | mem B hB =>
        obtain ⟨⟨j, vb, va⟩, rfl⟩ := hB
        exact h j b a vb va
    | zero => simp
    | add B C _ _ hB hC => rw [Matrix.mul_add, Matrix.add_mul, hB, hC]
    | smul c B _ hB => rw [Matrix.mul_smul, Matrix.smul_mul, hB]

/-! ### Block expansion of the commutator -/

theorem blockCentral_mul_apply (X : ∀ a, Matrix (N a) (N a) ℂ)
    (T : Matrix (Σ a, V a × N a) (Σ a, V a × N a) ℂ) (b a : ι) (vb : V b) (nb : N b)
    (va : V a) (na : N a) :
    (blockCentral (V := V) X * T) ⟨b, (vb, nb)⟩ ⟨a, (va, na)⟩ =
      (X b * quiverCoeff T b a vb va) nb na := by
  rw [blockCentral, blockDiagonal'_mul_apply, Fintype.sum_prod_type, Matrix.mul_apply]
  simp only [Matrix.kroneckerMap_apply, Matrix.one_apply, ite_mul, one_mul, zero_mul,
    quiverCoeff, Matrix.of_apply]
  rw [Finset.sum_eq_single vb (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
  simp

theorem mul_blockCentral_apply (X : ∀ a, Matrix (N a) (N a) ℂ)
    (T : Matrix (Σ a, V a × N a) (Σ a, V a × N a) ℂ) (b a : ι) (vb : V b) (nb : N b)
    (va : V a) (na : N a) :
    (T * blockCentral (V := V) X) ⟨b, (vb, nb)⟩ ⟨a, (va, na)⟩ =
      (quiverCoeff T b a vb va * X a) nb na := by
  rw [blockCentral, mul_blockDiagonal'_apply, Fintype.sum_prod_type, Matrix.mul_apply]
  simp only [Matrix.kroneckerMap_apply, Matrix.one_apply, mul_ite, ite_mul, one_mul,
    mul_one, zero_mul, mul_zero, quiverCoeff, Matrix.of_apply]
  rw [Finset.sum_eq_single va (fun x _ hx => by simp [hx]) (by simp)]
  simp

/-- The `(b, a)` block of `[⊕ I ⊗ X, T]` is `∑ E_{v_b v_a} ⊗ (X_b B - B X_a)`. -/
theorem commutator_blockCentral_apply (X : ∀ a, Matrix (N a) (N a) ℂ)
    (T : Matrix (Σ a, V a × N a) (Σ a, V a × N a) ℂ) (b a : ι) (vb : V b) (nb : N b)
    (va : V a) (na : N a) :
    (blockCentral (V := V) X * T - T * blockCentral (V := V) X) ⟨b, (vb, nb)⟩ ⟨a, (va, na)⟩ =
      (X b * quiverCoeff T b a vb va - quiverCoeff T b a vb va * X a) nb na := by
  rw [Matrix.sub_apply, blockCentral_mul_apply, mul_blockCentral_apply, Matrix.sub_apply]

/-- A block-central operator commutes with `T` iff its multiplicity family intertwines every
Hilbert–Schmidt coefficient of every block of `T`. -/
theorem blockCentral_commute_iff (X : ∀ a, Matrix (N a) (N a) ℂ)
    (T : Matrix (Σ a, V a × N a) (Σ a, V a × N a) ℂ) :
    blockCentral (V := V) X * T = T * blockCentral (V := V) X ↔
      ∀ b a (vb : V b) (va : V a),
        X b * quiverCoeff T b a vb va = quiverCoeff T b a vb va * X a := by
  constructor
  · intro h b a vb va
    ext nb na
    have := congrFun (congrFun h ⟨b, (vb, nb)⟩) ⟨a, (va, na)⟩
    rwa [blockCentral_mul_apply, mul_blockCentral_apply] at this
  · intro h
    ext ⟨b, vb, nb⟩ ⟨a, va, na⟩
    rw [blockCentral_mul_apply, mul_blockCentral_apply, h b a vb va]

/-! ### `eq:quiver-commutant` on the isotypic carrier -/

theorem actionBlockSet_starClosed :
    ∀ x ∈ actionBlockSet V N, xᴴ ∈ actionBlockSet V N := by
  rintro _ ⟨X, rfl⟩
  refine ⟨fun a => (X a)ᴴ, ?_⟩
  rw [blockDiagonal'_conjTranspose]
  congr 1
  funext a
  rw [conjTranspose_kronecker, conjTranspose_one]

/-- The generators `𝒮_F ∪ 𝐓`. -/
def quiverGenerators (T : J → Matrix (Σ a, V a × N a) (Σ a, V a × N a) ℂ) :
    Set (Matrix (Σ a, V a × N a) (Σ a, V a × N a) ℂ) :=
  actionBlockSet V N ∪ Set.range T

theorem quiverGenerators_starClosed (T : J → Matrix (Σ a, V a × N a) (Σ a, V a × N a) ℂ)
    (hT : ∀ j, ∃ j', T j' = (T j)ᴴ) :
    ∀ x ∈ quiverGenerators T, xᴴ ∈ quiverGenerators T := by
  rintro x (hx | ⟨j, rfl⟩)
  · exact Or.inl (actionBlockSet_starClosed x hx)
  · obtain ⟨j', hj'⟩ := hT j
    exact Or.inr ⟨j', hj'⟩

/-- The commutant of the generators `𝒮_F ∪ 𝐓` is the block-central realization of
`End 𝔔_F(T)`. -/
theorem matCommutant_quiverGenerators (T : J → Matrix (Σ a, V a × N a) (Σ a, V a × N a) ℂ) :
    matCommutant (quiverGenerators T) = blockCentral (V := V) '' {X | IsQuiverEnd T X} := by
  ext Y
  constructor
  · intro hY
    have hS : Y ∈ matCommutant (actionBlockSet V N) := fun a ha => hY a (Or.inl ha)
    rw [matCommutant_actionBlockSet, multBlockSet_eq_range] at hS
    obtain ⟨X, rfl⟩ := hS
    refine ⟨X, ?_, rfl⟩
    rw [Set.mem_ofPred_eq, isQuiverEnd_iff_coeff]
    intro j
    exact (blockCentral_commute_iff X (T j)).mp (hY _ (Or.inr ⟨j, rfl⟩))
  · rintro ⟨X, hX, rfl⟩ A hA
    rcases hA with hA | ⟨j, rfl⟩
    · have : blockCentral X ∈ matCommutant (actionBlockSet V N) := by
        rw [matCommutant_actionBlockSet, multBlockSet_eq_range]
        exact ⟨X, rfl⟩
      exact this A hA
    · exact (blockCentral_commute_iff X (T j)).mpr ((isQuiverEnd_iff_coeff T X).mp hX j)

/-- **`eq:quiver-commutant` (isotypic form).**  For every finite `*`-closed family `𝐓`,
`C^*(𝒮_F, 𝐓)' = {⊕_a I_{V_a} ⊗ X_a : (X_a) ∈ End 𝔔_F(𝐓)}` where
`𝒮_F = ⊕_a B(V_a) ⊗ I_{N_a}`. -/
theorem quiver_commutant_isotypic (T : J → Matrix (Σ a, V a × N a) (Σ a, V a × N a) ℂ)
    (hT : ∀ j, ∃ j', T j' = (T j)ᴴ) :
    matCommutant (SetLike.coe (StarAlgebra.adjoin ℂ (quiverGenerators T) :
        StarSubalgebra ℂ (Matrix (Σ a, V a × N a) (Σ a, V a × N a) ℂ))) =
      blockCentral (V := V) '' {X | IsQuiverEnd T X} := by
  rw [matCommutant_starAlgebra_adjoin _ (quiverGenerators_starClosed T hT),
    matCommutant_quiverGenerators]

/-! ### `eq:quiver-form` -/

/-- **`eq:quiver-form`.**  On block-central operators the ambient commutator form
`∑_j ‖[⊕ I ⊗ X_a, T_j]‖²_HS` equals `∑_{j,b,a,α} ‖X_b B^{ba}_{j,α} - B^{ba}_{j,α} X_a‖²_HS`. -/
theorem quiver_form_eq (T : J → Matrix (Σ a, V a × N a) (Σ a, V a × N a) ℂ)
    (X : ∀ a, Matrix (N a) (N a) ℂ) :
    ∑ j, quiverHSSq (blockCentral (V := V) X * T j - T j * blockCentral (V := V) X) =
      ∑ j, ∑ b, ∑ a, ∑ vb : V b, ∑ va : V a,
        quiverHSSq (X b * quiverCoeff (T j) b a vb va - quiverCoeff (T j) b a vb va * X a) := by
  refine Finset.sum_congr rfl fun j _ => ?_
  have hL : quiverHSSq (blockCentral (V := V) X * T j - T j * blockCentral (V := V) X) =
      ∑ b, ∑ vb : V b, ∑ nb : N b, ∑ a, ∑ va : V a, ∑ na : N a,
        Complex.normSq ((X b * quiverCoeff (T j) b a vb va -
          quiverCoeff (T j) b a vb va * X a) nb na) := by
    unfold quiverHSSq
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun vb _ => Finset.sum_congr rfl fun nb _ => ?_
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun va _ => Finset.sum_congr rfl fun na _ => ?_
    rw [commutator_blockCentral_apply]
  rw [hL]
  unfold quiverHSSq
  refine Finset.sum_congr rfl fun b _ => ?_
  calc _ = ∑ vb : V b, ∑ a, ∑ nb : N b, ∑ va : V a, ∑ na : N a,
        Complex.normSq ((X b * quiverCoeff (T j) b a vb va -
          quiverCoeff (T j) b a vb va * X a) nb na) :=
        Finset.sum_congr rfl fun vb _ => Finset.sum_comm
    _ = ∑ a, ∑ vb : V b, ∑ nb : N b, ∑ va : V a, ∑ na : N a,
        Complex.normSq ((X b * quiverCoeff (T j) b a vb va -
          quiverCoeff (T j) b a vb va * X a) nb na) := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun vb _ => Finset.sum_comm

/-- The kernel of the quiver form is exactly `End 𝔔_F(T)`. -/
theorem quiver_form_eq_zero_iff (T : J → Matrix (Σ a, V a × N a) (Σ a, V a × N a) ℂ)
    (X : ∀ a, Matrix (N a) (N a) ℂ) :
    ∑ j, quiverHSSq (blockCentral (V := V) X * T j - T j * blockCentral (V := V) X) = 0 ↔ IsQuiverEnd T X := by
  rw [isQuiverEnd_iff_coeff]
  simp only [← (blockCentral_commute_iff X _), ← sub_eq_zero (a := blockCentral X * _),
    ← quiverHSSq_eq_zero_iff]
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ => quiverHSSq_nonneg _)]
  simp

/-! ### `thm:quiver` for an arbitrary support algebra -/

/-- **`thm:quiver`, `eq:quiver-commutant`.**  Let `𝒮_F ⊆ M_n(ℂ)` be any unital `*`-subalgebra
(e.g. `C^*(Z_λ, supp F_e^*F_e, supp F_eF_e^*)`) and `𝐓 = (T_j)` a finite `*`-closed family.
The canonical isotypic decomposition `ℂⁿ ≅ ⊕_a V_a ⊗ N_a` (a unitary `W`, from
`reciprocal_wedderburn`) carries `𝒮_F` onto `⊕_a B(V_a) ⊗ I_{N_a}` and carries
`C^*(𝒮_F, 𝐓)'` onto `{⊕_a I_{V_a} ⊗ X_a : (X_a) ∈ End 𝔔_F(W^* 𝐓 W)}`; the realization
`(X_a) ↦ ⊕_a I_{V_a} ⊗ X_a` is an injective unital `*`-homomorphism (`blockCentral_mul`,
`blockCentral_one`, `blockCentral_conjTranspose`), hence `C^*(𝒮_F, 𝐓)' ≅ End 𝔔_F(𝐓)`. -/
theorem quiver_commutant {n : Type} [Fintype n] [DecidableEq n]
    (S : Subalgebra ℂ (Matrix n n ℂ)) (hS : ∀ a ∈ S, aᴴ ∈ S)
    {J : Type*} [Fintype J] (T : J → Matrix n n ℂ) (hT : ∀ j, ∃ j', T j' = (T j)ᴴ) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (V N : ι → Type)
      (_ : ∀ a, Fintype (V a)) (_ : ∀ a, DecidableEq (V a))
      (_ : ∀ a, Fintype (N a)) (_ : ∀ a, DecidableEq (N a))
      (W : Matrix n (Σ a, V a × N a) ℂ),
      Wᴴ * W = 1 ∧ W * Wᴴ = 1 ∧ (∀ a, Nonempty (V a)) ∧ (∀ a, Nonempty (N a)) ∧
      (fun x => Wᴴ * x * W) '' (S : Set (Matrix n n ℂ)) = actionBlockSet V N ∧
      (fun x => Wᴴ * x * W) '' matCommutant (SetLike.coe
          (StarAlgebra.adjoin ℂ ((S : Set (Matrix n n ℂ)) ∪ Set.range T))) =
        blockCentral (V := V) '' {X | IsQuiverEnd (fun j => Wᴴ * T j * W) X} ∧
      Function.Injective (blockCentral (V := V) (N := N)) := by
  obtain ⟨ι, hι1, hι2, V, N, hV1, hV2, hN1, hN2, W, hW1, hW2, hNV, hNN, hA, -⟩ :=
    reciprocal_wedderburn S hS
  refine ⟨ι, hι1, hι2, V, N, hV1, hV2, hN1, hN2, W, hW1, hW2, hNV, hNN, hA, ?_,
    blockCentral_injective hNV⟩
  have hgen : ∀ x ∈ (S : Set (Matrix n n ℂ)) ∪ Set.range T,
      xᴴ ∈ (S : Set (Matrix n n ℂ)) ∪ Set.range T := by
    rintro x (hx | ⟨j, rfl⟩)
    · exact Or.inl (hS x hx)
    · obtain ⟨j', hj'⟩ := hT j
      exact Or.inr ⟨j', hj'⟩
  rw [matCommutant_starAlgebra_adjoin _ hgen, ← matCommutant_image_conj W hW1 hW2,
    Set.image_union, hA]
  have hr : (fun x => Wᴴ * x * W) '' Set.range T = Set.range (fun j => Wᴴ * T j * W) := by
    rw [← Set.range_comp]
    rfl
  rw [hr]
  exact matCommutant_quiverGenerators (fun j => Wᴴ * T j * W)

/-- Non-vacuity: two isotypic blocks `ℂ² ⊗ ℂ³` with the self-adjoint family `{1}`. -/
example :
    matCommutant (SetLike.coe (StarAlgebra.adjoin ℂ (quiverGenerators
        (V := fun _ : Fin 2 => Fin 2) (N := fun _ : Fin 2 => Fin 3)
        (fun _ : Unit => (1 : Matrix (Σ _ : Fin 2, Fin 2 × Fin 3) (Σ _ : Fin 2, Fin 2 × Fin 3) ℂ))))) =
      blockCentral (V := fun _ : Fin 2 => Fin 2) '' {X | IsQuiverEnd
        (fun _ : Unit => (1 : Matrix (Σ _ : Fin 2, Fin 2 × Fin 3) (Σ _ : Fin 2, Fin 2 × Fin 3) ℂ)) X} :=
  quiver_commutant_isotypic _ fun _ => ⟨(), by rw [conjTranspose_one]⟩

end NoncommutingSupportQuiver

end RenewalGeometry
