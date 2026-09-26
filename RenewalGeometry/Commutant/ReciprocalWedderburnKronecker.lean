/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.Commutant.StarMatrixUnits
import RenewalGeometry.Commutant.CommonCentre
import RenewalGeometry.Commutant.GrandMultSaturation
import NCG.Algebra.MarkedFactor

open NCG
/-!
# Reciprocal Wedderburn structure: the unitary Kronecker form
  (`cor:reciprocal-wedderburn`, spacetime–gauge duality paper)

For a unital star-closed subalgebra `S` of a finite complex matrix algebra this
file proves the displayed reciprocal Kronecker form of
`cor:reciprocal-wedderburn`, equations `eq:wedderburn-H`,
`eq:wedderburn-action` and `eq:wedderburn-multiplicity`: there are a finite
sector set `ι`, finite action and multiplicity index types `I b`, `J b`
(the finite Hilbert spaces `H^act_b = ℂ^{I b}`, `H^mult_b = ℂ^{J b}`) and a
unitary `W : ℂ^{⊕_b I b × J b} → ℂ^n` (`Wᴴ W = 1`, `W Wᴴ = 1`) with

* `Wᴴ S W = ⊕_b M_{I b}(ℂ) ⊗ 1_{J b}` (`actionBlockSet`), and
* `Wᴴ S' W = ⊕_b 1_{I b} ⊗ M_{J b}(ℂ)` (`multBlockSet`).

The construction takes the corner form of the star unit system of `S`
(`StarUnits.star_unit_system_corner`: self-adjoint slot projections `p_j`,
partial isometries `v_j`, base slots, and the corner minimality
`p_j S p_j = ℂ p_j`), factors every base projection as `E Eᴴ` with `Eᴴ E = 1`
(`projection_factor`, spectral theorem) and assembles the columns
`v_j E_b` into `W`.  The commutant of a block-diagonal Kronecker algebra over
an arbitrary finite family of sectors is computed in
`matCommutant_actionBlockSet` / `matCommutant_multBlockSet`.

* `reciprocal_wedderburn`: the general statement for star-closed `S` (all sectors
  have nonempty action and multiplicity index types).
* `packet_reciprocal_wedderburn`: the packet form of the corollary, with the
  common-centre identity `eq:common-centre` and the shared central sector
  projections (`sectorProjection_mem`).
-/

open Matrix Kronecker

namespace RenewalGeometry

variable {n : Type} [Fintype n] [DecidableEq n]

/-! ### Factoring a projection through its range -/

/-- Every self-adjoint idempotent matrix factors as `q = E Eᴴ` with `Eᴴ E = 1` over a
finite index type: the columns of `E` are an orthonormal basis of the range of `q`
(eigenvectors of eigenvalue one). -/
theorem projection_factor (q : Matrix n n ℂ) (hq : qᴴ = q) (hidem : q * q = q) :
    ∃ (J : Type) (_ : Fintype J) (_ : DecidableEq J) (E : Matrix n J ℂ),
      Eᴴ * E = 1 ∧ E * Eᴴ = q := by
  have hA : q.IsHermitian := hq
  set V : Matrix n n ℂ := (hA.eigenvectorUnitary : Matrix n n ℂ) with hV
  have hVV : star V * V = 1 := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  have hVV' : V * star V = 1 := Unitary.coe_mul_star_self hA.eigenvectorUnitary
  set d : n → ℂ := fun k => (hA.eigenvalues k : ℂ) with hd
  have hspec : q = V * diagonal d * star V := by
    have h := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    exact h
  have hVqV : star V * q * V = diagonal d := by
    rw [hspec]
    calc star V * (V * diagonal d * star V) * V
        = (star V * V) * diagonal d * (star V * V) := by simp only [Matrix.mul_assoc]
      _ = diagonal d := by rw [hVV, Matrix.one_mul, Matrix.mul_one]
  have hD : diagonal d * diagonal d = diagonal d := by
    calc diagonal d * diagonal d = (star V * q * V) * (star V * q * V) := by rw [hVqV]
      _ = star V * (q * (V * star V) * q) * V := by simp only [Matrix.mul_assoc]
      _ = star V * q * V := by rw [hVV', Matrix.mul_one, hidem]
      _ = diagonal d := hVqV
  have hd01 : ∀ k, d k = 0 ∨ d k = 1 := by
    intro k
    have h := congrFun (congrFun hD k) k
    rw [diagonal_mul_diagonal, diagonal_apply_eq, diagonal_apply_eq] at h
    rcases eq_or_ne (d k) 0 with h0 | h0
    · exact Or.inl h0
    · right
      exact mul_left_cancel₀ h0 (by rw [h, mul_one])
  refine ⟨{k : n // d k = 1}, inferInstance, inferInstance, V.submatrix id Subtype.val, ?_, ?_⟩
  · ext k l
    have h := congrFun (congrFun hVV k.1) l.1
    rw [Matrix.mul_apply] at h ⊢
    simp only [conjTranspose_apply, submatrix_apply, id, star_apply] at h ⊢
    rw [Matrix.one_apply] at h ⊢
    rw [h]
    simp [Subtype.ext_iff]
  · ext i j
    rw [Matrix.mul_apply]
    simp only [conjTranspose_apply, submatrix_apply, id]
    rw [hspec, Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, star_apply]
    have hterm : ∀ k, V i k * d k * star (V j k) =
        if d k = 1 then V i k * star (V j k) else 0 := by
      intro k
      rcases hd01 k with h | h
      · rw [h, if_neg (by norm_num), mul_zero, zero_mul]
      · rw [h, if_pos rfl, mul_one]
    simp_rw [hterm]
    have hsub : ∑ k : {k : n // d k = 1}, V i k.1 * star (V j k.1) =
        ∑ k ∈ Finset.univ.filter (fun k => d k = 1), V i k * star (V j k) :=
      (Finset.sum_subtype (Finset.univ.filter fun k => d k = 1) (fun k => by simp)
        (fun k => V i k * star (V j k))).symm
    rw [hsub, Finset.sum_filter]

/-! ### Block Kronecker algebras over a finite family of sectors -/

section KroneckerCut

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The action algebra `⊕_b M_{I b}(ℂ) ⊗ 1_{J b}` on the carrier `⊕_b ℂ^{I b} ⊗ ℂ^{J b}`
(`eq:wedderburn-action`). -/
def actionBlockSet (I J : ι → Type) [∀ b, Fintype (J b)] [∀ b, DecidableEq (J b)] :
    Set (Matrix (Σ b, I b × J b) (Σ b, I b × J b) ℂ) :=
  {A | ∃ X : ∀ b, Matrix (I b) (I b) ℂ,
    A = blockDiagonal' fun b => X b ⊗ₖ (1 : Matrix (J b) (J b) ℂ)}

/-- The multiplicity algebra `⊕_b 1_{I b} ⊗ M_{J b}(ℂ)` (`eq:wedderburn-multiplicity`). -/
def multBlockSet (I J : ι → Type) [∀ b, Fintype (I b)] [∀ b, DecidableEq (I b)] :
    Set (Matrix (Σ b, I b × J b) (Σ b, I b × J b) ℂ) :=
  {A | ∃ Y : ∀ b, Matrix (J b) (J b) ℂ,
    A = blockDiagonal' fun b => (1 : Matrix (I b) (I b) ℂ) ⊗ₖ Y b}

variable {m : ι → Type} [∀ b, Fintype (m b)] {K : Type} [Fintype K]

/-- Rows of a block-diagonal matrix times a general matrix. -/
theorem blockDiagonal'_mul_apply (D : ∀ b, Matrix (m b) (m b) ℂ)
    (C : Matrix (Σ b, m b) K ℂ) (b : ι) (i : m b) (σ : K) :
    (blockDiagonal' D * C) ⟨b, i⟩ σ = ∑ i', D b i i' * C ⟨b, i'⟩ σ := by
  rw [Matrix.mul_apply, Fintype.sum_sigma]
  rw [Finset.sum_eq_single b]
  · simp only [blockDiagonal'_apply_eq]
  · intro b' _ hb'
    refine Finset.sum_eq_zero fun i' _ => ?_
    rw [blockDiagonal'_apply_ne _ _ _ (Ne.symm hb'), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ b) h

/-- A general matrix times a block-diagonal matrix, columnwise. -/
theorem mul_blockDiagonal'_apply (D : ∀ b, Matrix (m b) (m b) ℂ)
    (C : Matrix K (Σ b, m b) ℂ) (σ : K) (b : ι) (i : m b) :
    (C * blockDiagonal' D) σ ⟨b, i⟩ = ∑ i', C σ ⟨b, i'⟩ * D b i' i := by
  rw [Matrix.mul_apply, Fintype.sum_sigma]
  rw [Finset.sum_eq_single b]
  · simp only [blockDiagonal'_apply_eq]
  · intro b' _ hb'
    refine Finset.sum_eq_zero fun i' _ => ?_
    rw [blockDiagonal'_apply_ne _ _ _ hb', mul_zero]
  · intro h
    exact absurd (Finset.mem_univ b) h

variable {I J : ι → Type} [∀ b, Fintype (I b)] [∀ b, DecidableEq (I b)]
  [∀ b, Fintype (J b)] [∀ b, DecidableEq (J b)]

/-- A matrix over an empty index type is anything. -/
theorem matrix_eq_of_isEmpty {α β : Type} [IsEmpty α] (A B : Matrix (α × β) (α × β) ℂ) :
    A = B := by
  ext ⟨i, _⟩ _
  exact (IsEmpty.false i).elim

theorem matrix_eq_of_isEmpty' {α β : Type} [IsEmpty β] (A B : Matrix (α × β) (α × β) ℂ) :
    A = B := by
  ext ⟨_, j⟩ _
  exact (IsEmpty.false j).elim

/-- The two block Kronecker algebras commute. -/
theorem actionBlock_mul_multBlock (X : ∀ b, Matrix (I b) (I b) ℂ)
    (Y : ∀ b, Matrix (J b) (J b) ℂ) :
    (blockDiagonal' fun b => X b ⊗ₖ (1 : Matrix (J b) (J b) ℂ)) *
        (blockDiagonal' fun b => (1 : Matrix (I b) (I b) ℂ) ⊗ₖ Y b) =
      (blockDiagonal' fun b => (1 : Matrix (I b) (I b) ℂ) ⊗ₖ Y b) *
        (blockDiagonal' fun b => X b ⊗ₖ (1 : Matrix (J b) (J b) ℂ)) := by
  rw [← blockDiagonal'_mul, ← blockDiagonal'_mul]
  congr 1
  funext b
  rw [← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one,
    Matrix.one_mul, Matrix.mul_one]

/-- A matrix commuting with every block-diagonal element of the family `X b ⊗ 1`
has vanishing off-diagonal blocks. -/
theorem offDiagonal_eq_zero_of_comm (C : Matrix (Σ b, I b × J b) (Σ b, I b × J b) ℂ)
    (hcomm : ∀ b : ι,
      C * blockDiagonal' (fun b' =>
          (Pi.single (M := fun b => Matrix (I b) (I b) ℂ) b 1 b') ⊗ₖ
            (1 : Matrix (J b') (J b') ℂ)) =
        blockDiagonal' (fun b' =>
          (Pi.single (M := fun b => Matrix (I b) (I b) ℂ) b 1 b') ⊗ₖ
            (1 : Matrix (J b') (J b') ℂ)) * C)
    (b b' : ι) (x : I b × J b) (x' : I b' × J b') (hbb' : b ≠ b') :
    C ⟨b, x⟩ ⟨b', x'⟩ = 0 := by
  have h := congrFun (congrFun (hcomm b) ⟨b, x⟩) ⟨b', x'⟩
  rw [mul_blockDiagonal'_apply, blockDiagonal'_mul_apply, Pi.single_eq_same,
    Pi.single_eq_of_ne hbb'.symm, Matrix.zero_kronecker, Matrix.one_kronecker_one] at h
  simp only [Matrix.zero_apply, mul_zero, Finset.sum_const_zero, Matrix.one_apply, ite_mul,
    one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true] at h
  exact h.symm

/-- The same for the family `1 ⊗ Y b`. -/
theorem offDiagonal_eq_zero_of_comm' (C : Matrix (Σ b, I b × J b) (Σ b, I b × J b) ℂ)
    (hcomm : ∀ b : ι,
      C * blockDiagonal' (fun b' => (1 : Matrix (I b') (I b') ℂ) ⊗ₖ
          (Pi.single (M := fun b => Matrix (J b) (J b) ℂ) b 1 b')) =
        blockDiagonal' (fun b' => (1 : Matrix (I b') (I b') ℂ) ⊗ₖ
          (Pi.single (M := fun b => Matrix (J b) (J b) ℂ) b 1 b')) * C)
    (b b' : ι) (x : I b × J b) (x' : I b' × J b') (hbb' : b ≠ b') :
    C ⟨b, x⟩ ⟨b', x'⟩ = 0 := by
  have h := congrFun (congrFun (hcomm b) ⟨b, x⟩) ⟨b', x'⟩
  rw [mul_blockDiagonal'_apply, blockDiagonal'_mul_apply, Pi.single_eq_same,
    Pi.single_eq_of_ne hbb'.symm, Matrix.kronecker_zero, Matrix.one_kronecker_one] at h
  simp only [Matrix.zero_apply, mul_zero, Finset.sum_const_zero, Matrix.one_apply, ite_mul,
    one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true] at h
  exact h.symm

/-- **Kronecker cut, action side.**  The commutant of `⊕_b M_{I b} ⊗ 1` is
`⊕_b 1 ⊗ M_{J b}`. -/
theorem matCommutant_actionBlockSet :
    matCommutant (actionBlockSet I J) = multBlockSet I J := by
  ext C
  constructor
  · intro hC
    have hcomm : ∀ X : ∀ b, Matrix (I b) (I b) ℂ,
        C * blockDiagonal' (fun b => X b ⊗ₖ (1 : Matrix (J b) (J b) ℂ)) =
          blockDiagonal' (fun b => X b ⊗ₖ (1 : Matrix (J b) (J b) ℂ)) * C :=
      fun X => hC _ ⟨X, rfl⟩
    have hoff := offDiagonal_eq_zero_of_comm C (fun b => hcomm (Pi.single b 1))
    let Cb : ∀ b, Matrix (I b × J b) (I b × J b) ℂ :=
      fun b => Matrix.of fun x x' => C ⟨b, x⟩ ⟨b, x'⟩
    have hCeq : C = blockDiagonal' Cb := by
      ext ⟨b, x⟩ ⟨b', x'⟩
      by_cases hbb' : b = b'
      · subst hbb'
        rw [blockDiagonal'_apply_eq]
        rfl
      · rw [blockDiagonal'_apply_ne _ _ _ hbb', hoff b b' x x' hbb']
    have hblock : ∀ b (g : Matrix (I b) (I b) ℂ),
        (g ⊗ₖ (1 : Matrix (J b) (J b) ℂ)) * Cb b = Cb b * (g ⊗ₖ 1) := by
      intro b g
      ext x x'
      have h := congrFun (congrFun (hcomm (Pi.single b g)) ⟨b, x⟩) ⟨b, x'⟩
      rw [mul_blockDiagonal'_apply, blockDiagonal'_mul_apply, Pi.single_eq_same] at h
      rw [Matrix.mul_apply, Matrix.mul_apply]
      exact h.symm
    have hY : ∀ b, ∃ Y : Matrix (J b) (J b) ℂ, Cb b = (1 : Matrix (I b) (I b) ℂ) ⊗ₖ Y := by
      intro b
      rcases isEmpty_or_nonempty (I b) with hI | hI
      · exact ⟨0, matrix_eq_of_isEmpty _ _⟩
      · exact CommonOrigin.left_factor_commutant (Cb b) (hblock b)
    choose Y hY using hY
    refine ⟨Y, ?_⟩
    rw [hCeq]
    congr 1
    funext b
    exact hY b
  · rintro ⟨Y, rfl⟩ A ⟨X, rfl⟩
    exact (actionBlock_mul_multBlock X Y).symm

/-- **Kronecker cut, multiplicity side.**  The commutant of `⊕_b 1 ⊗ M_{J b}` is
`⊕_b M_{I b} ⊗ 1`. -/
theorem matCommutant_multBlockSet :
    matCommutant (multBlockSet I J) = actionBlockSet I J := by
  ext C
  constructor
  · intro hC
    have hcomm : ∀ Y : ∀ b, Matrix (J b) (J b) ℂ,
        C * blockDiagonal' (fun b => (1 : Matrix (I b) (I b) ℂ) ⊗ₖ Y b) =
          blockDiagonal' (fun b => (1 : Matrix (I b) (I b) ℂ) ⊗ₖ Y b) * C :=
      fun Y => hC _ ⟨Y, rfl⟩
    have hoff := offDiagonal_eq_zero_of_comm' C (fun b => hcomm (Pi.single b 1))
    let Cb : ∀ b, Matrix (I b × J b) (I b × J b) ℂ :=
      fun b => Matrix.of fun x x' => C ⟨b, x⟩ ⟨b, x'⟩
    have hCeq : C = blockDiagonal' Cb := by
      ext ⟨b, x⟩ ⟨b', x'⟩
      by_cases hbb' : b = b'
      · subst hbb'
        rw [blockDiagonal'_apply_eq]
        rfl
      · rw [blockDiagonal'_apply_ne _ _ _ hbb', hoff b b' x x' hbb']
    have hblock : ∀ b (g : Matrix (J b) (J b) ℂ),
        ((1 : Matrix (I b) (I b) ℂ) ⊗ₖ g) * Cb b = Cb b * (1 ⊗ₖ g) := by
      intro b g
      ext x x'
      have h := congrFun (congrFun (hcomm (Pi.single b g)) ⟨b, x⟩) ⟨b, x'⟩
      rw [mul_blockDiagonal'_apply, blockDiagonal'_mul_apply, Pi.single_eq_same] at h
      rw [Matrix.mul_apply, Matrix.mul_apply]
      exact h.symm
    have hX : ∀ b, ∃ X : Matrix (I b) (I b) ℂ, Cb b = X ⊗ₖ (1 : Matrix (J b) (J b) ℂ) := by
      intro b
      rcases isEmpty_or_nonempty (J b) with hJ | hJ
      · exact ⟨0, matrix_eq_of_isEmpty' _ _⟩
      · exact right_factor_commutant (Cb b) (hblock b)
    choose X hX using hX
    refine ⟨X, ?_⟩
    rw [hCeq]
    congr 1
    funext b
    exact hX b
  · rintro ⟨X, rfl⟩ A ⟨Y, rfl⟩
    exact actionBlock_mul_multBlock X Y

/-- The central sector projection `1_{I b} ⊗ 1_{J b}` on the `b`-th sector. -/
def sectorProjection (I J : ι → Type) [∀ b, Fintype (I b)] [∀ b, DecidableEq (I b)]
    [∀ b, Fintype (J b)] [∀ b, DecidableEq (J b)] (b : ι) :
    Matrix (Σ b, I b × J b) (Σ b, I b × J b) ℂ :=
  blockDiagonal' (Pi.single b (1 : Matrix (I b × J b) (I b × J b) ℂ))

/-- The sector projections lie in both algebras (hence in their common centre). -/
theorem sectorProjection_mem (b : ι) :
    sectorProjection I J b ∈ actionBlockSet I J ∧ sectorProjection I J b ∈ multBlockSet I J := by
  constructor
  · refine ⟨Pi.single b 1, ?_⟩
    unfold sectorProjection
    congr 1
    funext b'
    by_cases h : b' = b
    · subst h
      rw [Pi.single_eq_same, Pi.single_eq_same, Matrix.one_kronecker_one]
    · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, Matrix.zero_kronecker]
  · refine ⟨Pi.single b 1, ?_⟩
    unfold sectorProjection
    congr 1
    funext b'
    by_cases h : b' = b
    · subst h
      rw [Pi.single_eq_same, Pi.single_eq_same, Matrix.one_kronecker_one]
    · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, Matrix.kronecker_zero]

end KroneckerCut

/-! ### Transport along a rectangular unitary -/

/-- The commutant is antitone. -/
theorem matCommutant_anti {A B : Set (Matrix n n ℂ)} (h : A ⊆ B) :
    matCommutant B ⊆ matCommutant A :=
  fun _ hT a ha => hT a (h ha)

/-- A unitary identification `W : ℂ^K → ℂ^n` (`Wᴴ W = 1`, `W Wᴴ = 1`) transports commutants:
`(Wᴴ S W)' = Wᴴ S' W`. -/
theorem matCommutant_image_conj {K : Type} [Fintype K] [DecidableEq K]
    (W : Matrix n K ℂ) (h1 : Wᴴ * W = 1) (h2 : W * Wᴴ = 1) (S : Set (Matrix n n ℂ)) :
    matCommutant ((fun x => Wᴴ * x * W) '' S) = (fun x => Wᴴ * x * W) '' matCommutant S := by
  ext T
  constructor
  · intro hT
    refine ⟨W * T * Wᴴ, fun a ha => ?_, ?_⟩
    · have h := hT _ ⟨a, ha, rfl⟩
      calc W * T * Wᴴ * a = W * T * Wᴴ * a * (W * Wᴴ) := by rw [h2, Matrix.mul_one]
        _ = W * (T * (Wᴴ * a * W)) * Wᴴ := by simp only [Matrix.mul_assoc]
        _ = W * ((Wᴴ * a * W) * T) * Wᴴ := by rw [h]
        _ = (W * Wᴴ) * a * (W * T * Wᴴ) := by simp only [Matrix.mul_assoc]
        _ = a * (W * T * Wᴴ) := by rw [h2, Matrix.one_mul]
    · calc Wᴴ * (W * T * Wᴴ) * W = (Wᴴ * W) * T * (Wᴴ * W) := by simp only [Matrix.mul_assoc]
        _ = T := by rw [h1, Matrix.one_mul, Matrix.mul_one]
  · rintro ⟨T', hT', rfl⟩ _ ⟨a, ha, rfl⟩
    have h := hT' a ha
    calc Wᴴ * T' * W * (Wᴴ * a * W) = Wᴴ * (T' * (W * Wᴴ) * a) * W := by
          simp only [Matrix.mul_assoc]
      _ = Wᴴ * (T' * a) * W := by rw [h2, Matrix.mul_one]
      _ = Wᴴ * (a * T') * W := by rw [h]
      _ = Wᴴ * (a * (W * Wᴴ) * T') * W := by rw [h2, Matrix.mul_one]
      _ = Wᴴ * a * W * (Wᴴ * T' * W) := by simp only [Matrix.mul_assoc]

/-! ### Sector bookkeeping for a star unit system -/

namespace ReciprocalWedderburn

variable {M : ℕ}

/-- The sectors of a star unit system: its base slots. -/
abbrev Sector (base : Fin M → Fin M) : Type := {j : Fin M // base j = j}

/-- The sector of a slot. -/
def toSector (base : Fin M → Fin M) (hbb : ∀ j, base (base j) = base j) (j : Fin M) :
    Sector base :=
  ⟨base j, hbb j⟩

/-- The slots of a sector: the action index type `I b`. -/
abbrev Slot (base : Fin M → Fin M) (hbb : ∀ j, base (base j) = base j) (b : Sector base) :
    Type :=
  {j : Fin M // toSector base hbb j = b}

theorem toSector_eq_iff (base : Fin M → Fin M) (hbb : ∀ j, base (base j) = base j)
    (j k : Fin M) : toSector base hbb j = toSector base hbb k ↔ base j = base k :=
  Subtype.ext_iff

theorem Slot.base_eq (base : Fin M → Fin M) (hbb : ∀ j, base (base j) = base j)
    (b : Sector base) (j : Slot base hbb b) : base j.1 = b.1 :=
  congrArg Subtype.val j.2

instance (base : Fin M → Fin M) (hbb : ∀ j, base (base j) = base j) (b : Sector base) :
    Nonempty (Slot base hbb b) :=
  ⟨⟨b.1, Subtype.ext b.2⟩⟩

end ReciprocalWedderburn

open ReciprocalWedderburn in
/-- **Reciprocal Wedderburn structure (`cor:reciprocal-wedderburn`, Kronecker form).**
For every unital star-closed subalgebra `S` of `M_n(ℂ)` there are a finite sector set
`ι`, finite action and multiplicity index types `I b`, `J b`, and a unitary
`W : ℂ^{⊕_b I b × J b} → ℂ^n` (`Wᴴ W = 1`, `W Wᴴ = 1`, this is `eq:wedderburn-H`) with
`Wᴴ S W = ⊕_b M_{I b}(ℂ) ⊗ 1` (`eq:wedderburn-action`) and
`Wᴴ S' W = ⊕_b 1 ⊗ M_{J b}(ℂ)` (`eq:wedderburn-multiplicity`). -/
theorem reciprocal_wedderburn (S : Subalgebra ℂ (Matrix n n ℂ)) (hstar : ∀ a ∈ S, aᴴ ∈ S) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (I J : ι → Type)
      (_ : ∀ b, Fintype (I b)) (_ : ∀ b, DecidableEq (I b))
      (_ : ∀ b, Fintype (J b)) (_ : ∀ b, DecidableEq (J b))
      (W : Matrix n (Σ b, I b × J b) ℂ),
      Wᴴ * W = 1 ∧ W * Wᴴ = 1 ∧ (∀ b, Nonempty (I b)) ∧ (∀ b, Nonempty (J b)) ∧
      (fun x => Wᴴ * x * W) '' (S : Set (Matrix n n ℂ)) = actionBlockSet I J ∧
      (fun x => Wᴴ * x * W) '' matCommutant (S : Set (Matrix n n ℂ)) = multBlockSet I J := by
  classical
  obtain ⟨M, blk, p, v, base, hbase_blk, hbase_eq, hpS, hpH, hpidem, hporth, hpsum, hvS,
    hvlaw, hvv, hcent, hpne, hcorner⟩ := StarUnits.star_unit_system_corner S hstar
  have hbb : ∀ j, base (base j) = base j := fun j => hbase_eq (base j) j (hbase_blk j)
  -- multiplicity factors of the base projections
  have hfac : ∀ b : Sector base, ∃ (J : Type) (_ : Fintype J) (_ : DecidableEq J)
      (E : Matrix n J ℂ), Eᴴ * E = 1 ∧ E * Eᴴ = p b.1 :=
    fun b => projection_factor (p b.1) (hpH b.1) (hpidem b.1)
  choose J hJf hJd E hE1 hE2 using hfac
  letI : ∀ b, Fintype (J b) := hJf
  letI : ∀ b, DecidableEq (J b) := hJd
  -- absorption laws
  have habs : ∀ j, v j * p (base j) = v j := fun j =>
    StarUnits.isometry_absorb (hpH _) (hpidem _) (by rw [hvlaw j j, if_pos rfl])
  have habs' : ∀ j, p (base j) * (v j)ᴴ = (v j)ᴴ := by
    intro j
    have h := congrArg conjTranspose (habs j)
    rwa [conjTranspose_mul, hpH] at h
  have hvp : ∀ j, (v j)ᴴ * p j = (v j)ᴴ := by
    intro j
    rw [← hvv j, ← Matrix.mul_assoc, hvlaw j j, if_pos rfl, habs' j]
  have hpv : ∀ j, p j * v j = v j := by
    intro j
    rw [← hvv j, Matrix.mul_assoc, hvlaw j j, if_pos rfl, habs j]
  -- the unitary
  let W : Matrix n (Σ b : Sector base, Slot base hbb b × J b) ℂ :=
    Matrix.of fun i σ => (v σ.2.1.1 * E σ.1) i σ.2.2
  have hentry : ∀ (x : Matrix n n ℂ) (b b' : Sector base) (j : Slot base hbb b) (l : J b)
      (k : Slot base hbb b') (l' : J b'),
      (Wᴴ * x * W) ⟨b, (j, l)⟩ ⟨b', (k, l')⟩ =
        ((E b)ᴴ * ((v j.1)ᴴ * x * v k.1) * E b') l l' := by
    intro x b b' j l k l'
    have h : (Wᴴ * x * W) ⟨b, (j, l)⟩ ⟨b', (k, l')⟩ =
        ((v j.1 * E b)ᴴ * x * (v k.1 * E b')) l l' := by
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, W, Matrix.of_apply]
    rw [h]
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  -- `Wᴴ W = 1`
  have hW1 : Wᴴ * W = 1 := by
    ext ⟨b, j, l⟩ ⟨b', k, l'⟩
    have h := hentry 1 b b' j l k l'
    simp only [Matrix.mul_one] at h
    rw [h, hvlaw]
    by_cases hjk : j.1 = k.1
    · have hb : b = b' := by rw [← j.2, ← k.2, hjk]
      subst hb
      have hjk' : j = k := Subtype.ext hjk
      subst hjk'
      rw [if_pos rfl, Slot.base_eq base hbb b j, ← hE2 b, ← Matrix.mul_assoc, hE1 b,
        Matrix.one_mul, hE1 b]
      simp [Matrix.one_apply]
    · rw [if_neg hjk, Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_apply, Matrix.one_apply,
        if_neg]
      intro heq
      obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.mp heq
      exact hjk (congrArg (fun q : Slot base hbb b × J b => q.1.1) (eq_of_heq h2))
  -- `W Wᴴ = 1`
  have hW2 : W * Wᴴ = 1 := by
    ext i i'
    have hcol : ∀ (b : Sector base) (j : Slot base hbb b),
        ∑ l : J b, W i ⟨b, (j, l)⟩ * star (W i' ⟨b, (j, l)⟩) = p j.1 i i' := by
      intro b j
      have h : ∑ l : J b, W i ⟨b, (j, l)⟩ * star (W i' ⟨b, (j, l)⟩) =
          ((v j.1 * E b) * (v j.1 * E b)ᴴ) i i' := by
        simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, W, Matrix.of_apply]
      rw [h, conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (E b), hE2 b,
        ← Slot.base_eq base hbb b j, ← Matrix.mul_assoc, habs j.1, hvv j.1]
    rw [Matrix.mul_apply]
    simp only [Matrix.conjTranspose_apply]
    rw [Fintype.sum_sigma]
    simp only [Fintype.sum_prod_type]
    simp only [hcol]
    have hre : ∑ b : Sector base, ∑ j : Slot base hbb b, p j.1 = ∑ j, p j := by
      rw [← Fintype.sum_sigma (fun σ : Σ b : Sector base, Slot base hbb b => p σ.2.1)]
      exact Fintype.sum_equiv (Equiv.sigmaFiberEquiv (toSector base hbb)) _ _ (fun _ => rfl)
    have hfold : ∑ b : Sector base, ∑ j : Slot base hbb b, p j.1 i i' =
        (∑ b : Sector base, ∑ j : Slot base hbb b, p j.1) i i' := by
      rw [Matrix.sum_apply]
      exact Finset.sum_congr rfl fun b _ => (Matrix.sum_apply i i' _ _).symm
    rw [hfold, hre, hpsum]
  -- the zero law across sectors
  have hcross : ∀ (x : Matrix n n ℂ), x ∈ S → ∀ j k, base j ≠ base k →
      (v j)ᴴ * x * v k = 0 := by
    intro x hx j k hjk
    have hblk : blk j ≠ blk k := fun h => hjk (hbase_eq j k h)
    set P := ∑ i ∈ Finset.univ.filter (fun i => blk i = blk j), p i with hP
    have hjP : p j * P = p j := by
      rw [hP, Finset.mul_sum, Finset.sum_eq_single_of_mem
        (s := Finset.univ.filter fun i => blk i = blk j) j
        (Finset.mem_filter.mpr ⟨Finset.mem_univ j, rfl⟩)
        (fun i _ hij => hporth j i (Ne.symm hij)), hpidem]
    have hPk : P * p k = 0 := by
      rw [hP, Finset.sum_mul]
      refine Finset.sum_eq_zero fun i hi => ?_
      exact hporth i k fun h => hblk (h ▸ (Finset.mem_filter.mp hi).2).symm
    have hpxp : p j * x * p k = 0 := by
      calc p j * x * p k = p j * P * x * p k := by rw [hjP]
        _ = p j * (P * x) * p k := by rw [Matrix.mul_assoc (p j)]
        _ = p j * (x * P) * p k := by rw [hcent (blk j) x hx]
        _ = p j * x * (P * p k) := by simp only [Matrix.mul_assoc]
        _ = 0 := by rw [hPk, Matrix.mul_zero]
    calc (v j)ᴴ * x * v k = ((v j)ᴴ * p j) * x * (p k * v k) := by rw [hvp, hpv]
      _ = (v j)ᴴ * (p j * x * p k) * v k := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hpxp, Matrix.mul_zero, Matrix.zero_mul]
  -- image of `S` inside the action algebra
  have hΦS : (fun x => Wᴴ * x * W) '' (S : Set (Matrix n n ℂ)) ⊆ actionBlockSet _ J := by
    rintro _ ⟨x, hx, rfl⟩
    have hc : ∀ (b : Sector base) (j k : Slot base hbb b), ∃ c : ℂ,
        p b.1 * (((v j.1)ᴴ * x * v k.1) * p b.1) = c • p b.1 :=
      fun b j k => hcorner b.1 _ (S.mul_mem (S.mul_mem (hstar _ (hvS _)) hx) (hvS _))
    choose X hX using hc
    refine ⟨fun b => Matrix.of fun j k => X b j k, ?_⟩
    ext ⟨b, j, l⟩ ⟨b', k, l'⟩
    beta_reduce
    rw [hentry]
    by_cases hb : b = b'
    · subst hb
      rw [blockDiagonal'_apply_eq, Matrix.kroneckerMap_apply, Matrix.of_apply]
      have h1 : p b.1 * (v j.1)ᴴ = (v j.1)ᴴ := by
        rw [← Slot.base_eq base hbb b j]; exact habs' j.1
      have h2 : v k.1 * p b.1 = v k.1 := by
        rw [← Slot.base_eq base hbb b k]; exact habs k.1
      have hxc : (v j.1)ᴴ * x * v k.1 = X b j k • p b.1 := by
        rw [← hX b j k]
        calc (v j.1)ᴴ * x * v k.1 = (p b.1 * (v j.1)ᴴ) * x * (v k.1 * p b.1) := by
              rw [h1, h2]
          _ = p b.1 * ((v j.1)ᴴ * x * v k.1 * p b.1) := by simp only [Matrix.mul_assoc]
      rw [hxc, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, ← hE2 b,
        ← Matrix.mul_assoc (E b)ᴴ (E b) (E b)ᴴ, hE1 b, Matrix.one_mul, hE1 b, smul_eq_mul]
    · rw [blockDiagonal'_apply_ne _ _ _ hb, hcross x hx j.1 k.1, Matrix.mul_zero,
        Matrix.zero_mul, Matrix.zero_apply]
      intro h
      apply hb
      rw [← j.2, ← k.2]
      exact (toSector_eq_iff base hbb _ _).mpr h
  -- image of the commutant inside the multiplicity algebra
  have hΦS' : (fun x => Wᴴ * x * W) '' matCommutant (S : Set (Matrix n n ℂ)) ⊆
      multBlockSet (Slot base hbb) J := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨fun b => (E b)ᴴ * y * E b, ?_⟩
    ext ⟨b, j, l⟩ ⟨b', k, l'⟩
    beta_reduce
    rw [hentry]
    have hcomm : y * v k.1 = v k.1 * y := hy _ (hvS _)
    have hin : (v j.1)ᴴ * y * v k.1 = (if j.1 = k.1 then p (base j.1) else 0) * y := by
      rw [Matrix.mul_assoc, hcomm, ← Matrix.mul_assoc, hvlaw]
    rw [hin]
    by_cases hjk : j.1 = k.1
    · have hb : b = b' := by rw [← j.2, ← k.2, hjk]
      subst hb
      have hjk' : j = k := Subtype.ext hjk
      subst hjk'
      rw [if_pos rfl, blockDiagonal'_apply_eq, Matrix.kroneckerMap_apply, Matrix.one_apply_eq,
        one_mul, Slot.base_eq base hbb b j, ← hE2 b]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (E b)ᴴ (E b), hE1 b, Matrix.one_mul]
    · rw [if_neg hjk, Matrix.zero_mul, Matrix.mul_zero, Matrix.zero_mul, Matrix.zero_apply]
      by_cases hb : b = b'
      · subst hb
        rw [blockDiagonal'_apply_eq, Matrix.kroneckerMap_apply,
          Matrix.one_apply_ne (fun h => hjk (congrArg Subtype.val h)), zero_mul]
      · rw [blockDiagonal'_apply_ne _ _ _ hb]
  -- assembly through the mutual commutant
  have hSS : matCommutant (matCommutant (S : Set (Matrix n n ℂ))) = S :=
    FiniteStarSubalgebraMutualCommutant.mutualCommutants S hstar
  have htr := fun T => matCommutant_image_conj W hW1 hW2 T
  have hA : (fun x => Wᴴ * x * W) '' (S : Set (Matrix n n ℂ)) =
      actionBlockSet (Slot base hbb) J := by
    refine le_antisymm hΦS ?_
    rw [← matCommutant_multBlockSet]
    calc matCommutant (multBlockSet (Slot base hbb) J)
        ⊆ matCommutant ((fun x => Wᴴ * x * W) '' matCommutant (S : Set (Matrix n n ℂ))) :=
          matCommutant_anti hΦS'
      _ = (fun x => Wᴴ * x * W) '' matCommutant (matCommutant (S : Set (Matrix n n ℂ))) :=
          htr _
      _ = (fun x => Wᴴ * x * W) '' (S : Set (Matrix n n ℂ)) := by rw [hSS]
  have hMu : (fun x => Wᴴ * x * W) '' matCommutant (S : Set (Matrix n n ℂ)) =
      multBlockSet (Slot base hbb) J := by
    refine le_antisymm hΦS' ?_
    rw [← matCommutant_actionBlockSet, ← hA, htr]
  have hNJ : ∀ b, Nonempty (J b) := by
    intro b
    by_contra hne
    rw [not_nonempty_iff] at hne
    apply hpne b.1
    rw [← hE2 b]
    ext i i'
    rw [Matrix.mul_apply, Matrix.zero_apply]
    exact Finset.sum_of_isEmpty _
  exact ⟨Sector base, inferInstance, inferInstance, Slot base hbb, J, inferInstance,
    inferInstance, hJf, hJd, W, hW1, hW2, fun b => inferInstance, hNJ, hA, hMu⟩

/-- **`cor:reciprocal-wedderburn` for packets.**  For every source-complete joint duality
packet (the hypotheses of `thm:main-duality`), the action algebra and the multiplicity
algebra are simultaneously unitarily equivalent to the reciprocal Kronecker algebras
`⊕_b M_{I b} ⊗ 1` and `⊕_b 1 ⊗ M_{J b}` on `⊕_b ℂ^{I b} ⊗ ℂ^{J b}`
(`eq:wedderburn-H`, `eq:wedderburn-action`, `eq:wedderburn-multiplicity`), the common
centre is `𝒜_act ∩ 𝓜_type` (`eq:common-centre`), and every sector projection is a common
central projection of both algebras. -/
theorem packet_reciprocal_wedderburn {r QEnd : Type*} [Fintype r] [DecidableEq r]
    [Semiring QEnd] [Algebra ℂ QEnd] (P : SourceCompleteJointDualityPacket n r QEnd) :
    (∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (I J : ι → Type)
      (_ : ∀ b, Fintype (I b)) (_ : ∀ b, DecidableEq (I b))
      (_ : ∀ b, Fintype (J b)) (_ : ∀ b, DecidableEq (J b))
      (W : Matrix n (Σ b, I b × J b) ℂ),
      Wᴴ * W = 1 ∧ W * Wᴴ = 1 ∧ (∀ b, Nonempty (I b)) ∧ (∀ b, Nonempty (J b)) ∧
      (fun x => Wᴴ * x * W) '' (P.actionAlgebra : Set (Matrix n n ℂ)) = actionBlockSet I J ∧
      (fun x => Wᴴ * x * W) '' (P.multiplicityAlgebra : Set (Matrix n n ℂ)) =
        multBlockSet I J ∧
      (∀ b, sectorProjection I J b ∈ actionBlockSet I J ∧
        sectorProjection I J b ∈ multBlockSet I J ∧
        sectorProjection I J b ∈ matCentre (actionBlockSet I J) ∧
        sectorProjection I J b ∈ matCentre (multBlockSet I J))) ∧
    matCentre (P.actionAlgebra : Set (Matrix n n ℂ)) =
      (P.actionAlgebra : Set (Matrix n n ℂ)) ∩ (P.multiplicityAlgebra : Set (Matrix n n ℂ)) ∧
    matCentre (P.multiplicityAlgebra : Set (Matrix n n ℂ)) =
      (P.actionAlgebra : Set (Matrix n n ℂ)) ∩ (P.multiplicityAlgebra : Set (Matrix n n ℂ)) := by
  obtain ⟨ι, _, _, I, J, _, _, _, _, W, hW1, hW2, hNI, hNJ, hA, hM⟩ :=
    reciprocal_wedderburn P.actionAlgebra P.action_starClosed
  refine ⟨⟨ι, inferInstance, inferInstance, I, J, inferInstance, inferInstance, inferInstance,
    inferInstance, W, hW1, hW2, hNI, hNJ, hA, ?_, ?_⟩, (packet_common_centre P).1,
    (packet_common_centre P).2.1⟩
  · rw [← P.edgeCommutant]
    exact hM
  · intro b
    obtain ⟨h1, h2⟩ := sectorProjection_mem (I := I) (J := J) b
    refine ⟨h1, h2, ⟨h1, ?_⟩, ⟨h2, ?_⟩⟩
    · rw [matCommutant_actionBlockSet]
      exact h2
    · rw [matCommutant_multBlockSet]
      exact h1

end RenewalGeometry
