/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.StandardModel.FaithfulSMQuotientExact
import RenewalGeometry.Commutant.ArbitraryIncidenceDualityExact

/-!
# Kinematic typing algebra on the represented matter carrier (`prop:typed-matter-lift`)

`prop:typed-matter-lift` of the spacetime–gauge duality manuscript.  On the matter carrier

`ℋ_mat ≅ ℂ⁴ ⊗ ⊕_f V_f ⊗ N_f`

(the carrier `RepresentedJointPacket.Carrier V N = Σ f, (Fin 4 × V_f) × N_f`), the represented
gauge action is `r(g) = ⊕_f I_4 ⊗ ρ_f(g) ⊗ I_{N_f}` (`gaugeAction`) and the type projections are
`p_f = ⊕_{f'} I_4 ⊗ δ_{f f'} I ⊗ I` (`typeProj`).

* `typeAlgebra_eq_intAlgebra` (generic): for any family of representations whose images
  generate the full matrix algebras `B(V_f)` (irreducibility, in Burnside form),
  `𝒜_type = C^*(r(g), p_f) = ⊕_f I_4 ⊗ B(V_f) ⊗ I_{N_f}` (`eq:typed-matter-lift`);
* `su3_adjoin_eq_top`, `su2_adjoin_eq_top`: explicit elements of `SU(3)` (real sign-diagonal
  matrices and a cyclic permutation) and of `SU(2)` (`iσ_z`, `iσ_y`) generate `M_3`, `M_2`;
* `matterRep_adjoin_eq_top`: each represented fermion module `Q, u^c, d^c, L, e^c, ν^c` of
  `prop:faithful-SM-quotient` generates its full matrix algebra;
* `typed_matter_lift`: the assembled statement for any family of sectors `κ : Λ → MatterType`
  (in particular `{Q, u^c, d^c, L, e^c}` with or without `ν^c`): the equality
  `eq:typed-matter-lift`, commutation with `𝒜_Cl = 𝒜_ext`, the block sizes `(6,3,3,2,1)`, and,
  for an arbitrary represented incidence family on these sectors (any operator-Schmidt rank),
  the joint packet of `thm:main-duality` (its typed internal algebra is `𝒜_type` and its action
  algebra and typed multiplicity algebra are mutual commutants).

Renderings disclosed: the represented `G_det` action is realized through the cover
`SU(3) × SU(2) × U(1)_y` (`SMGaugeCover`); since the matter representations factor through
`G_det = G̃/ℤ₆` (`prop:faithful-SM-quotient`), the represented operator sets coincide.  The
carrier is fixed in its displayed coordinates.
-/

open Matrix
open scoped Kronecker

namespace RenewalGeometry
namespace TypedMatterLift

open RepresentedJointPacket FaithfulSMQuotient

set_option linter.unusedSectionVars false

/-! ### Generic block algebra -/

section Generic

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ]
variable {V N : Λ → Type*} [∀ l, Fintype (V l)] [∀ l, DecidableEq (V l)]
  [∀ l, Fintype (N l)] [∀ l, DecidableEq (N l)]

theorem intAction_add (b b' : ∀ l, Matrix (V l) (V l) ℂ) :
    intAction V N (b + b') = intAction V N b + intAction V N b' := by
  unfold intAction
  rw [← blockDiagonal'_add]
  congr 1
  funext l
  simp only [Pi.add_apply, Matrix.kronecker_add, Matrix.add_kronecker]

theorem intAction_smul (c : ℂ) (b : ∀ l, Matrix (V l) (V l) ℂ) :
    intAction V N (c • b) = c • intAction V N b := by
  unfold intAction
  rw [← blockDiagonal'_smul]
  congr 1
  funext l
  simp only [Pi.smul_apply, Matrix.kronecker_smul, Matrix.smul_kronecker]

theorem intAction_sum (b : ∀ l, Matrix (V l) (V l) ℂ) :
    intAction V N b = ∑ l, intAction V N (Pi.single l (b l)) := by
  have hsum : ∀ s : Finset Λ, intAction V N (∑ l ∈ s, Pi.single l (b l)) =
      ∑ l ∈ s, intAction V N (Pi.single l (b l)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      have := intAction_smul (V := V) (N := N) 0 0
      simpa using this
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, intAction_add, ih]
  rw [← hsum, Finset.univ_sum_single]

variable (V N)

/-- The represented gauge action `r(g) = ⊕_f I_4 ⊗ ρ_f(g) ⊗ I_{N_f}`. -/
def gaugeAction {G : Type*} [Monoid G] (ρ : ∀ l, G →* Matrix (V l) (V l) ℂ) (g : G) :
    Matrix (Carrier V N) (Carrier V N) ℂ :=
  intAction V N fun l => ρ l g

/-- The type projection `p_f`. -/
def typeProj (l : Λ) : Matrix (Carrier V N) (Carrier V N) ℂ :=
  intAction V N (Pi.single l 1)

/-- The kinematic typing algebra `𝒜_type = C^*(r(g), p_f : g, f)`. -/
def typeAlgebra {G : Type*} [Monoid G] (ρ : ∀ l, G →* Matrix (V l) (V l) ℂ) :
    StarSubalgebra ℂ (Matrix (Carrier V N) (Carrier V N) ℂ) :=
  StarAlgebra.adjoin ℂ (Set.range (gaugeAction V N ρ) ∪ Set.range (typeProj V N))

/-- The block algebra `⊕_f I_4 ⊗ B(V_f) ⊗ I_{N_f}` as a star subalgebra. -/
def blockStarSubalgebra : StarSubalgebra ℂ (Matrix (Carrier V N) (Carrier V N) ℂ) where
  carrier := intAlgebra V N
  mul_mem' := by
    rintro _ _ ⟨b, rfl⟩ ⟨b', rfl⟩
    exact ⟨b * b', intAction_mul b b'⟩
  add_mem' := by
    rintro _ _ ⟨b, rfl⟩ ⟨b', rfl⟩
    exact ⟨b + b', intAction_add b b'⟩
  algebraMap_mem' r := by
    refine ⟨r • 1, ?_⟩
    rw [intAction_smul, intAction_one, Algebra.algebraMap_eq_smul_one]
  star_mem' := by
    rintro _ ⟨b, rfl⟩
    exact ⟨star b, by rw [Matrix.star_eq_conjTranspose, intAction_conjTranspose]⟩

variable {V N}

theorem single_mul_family {G : Type*} [Monoid G] (ρ : ∀ l, G →* Matrix (V l) (V l) ℂ)
    (l : Λ) (g : G) :
    (Pi.single l (1 : Matrix (V l) (V l) ℂ) : ∀ l, Matrix (V l) (V l) ℂ) * (fun l' => ρ l' g) =
      Pi.single l (ρ l g) := by
  funext l'
  by_cases h : l' = l
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

/-- **`eq:typed-matter-lift` (generic form)**: if each `ρ_f(G)` generates `B(V_f)`, then
`C^*(r(g), p_f) = ⊕_f I_4 ⊗ B(V_f) ⊗ I_{N_f}`. -/
theorem typeAlgebra_eq_intAlgebra {G : Type*} [Monoid G]
    (ρ : ∀ l, G →* Matrix (V l) (V l) ℂ)
    (hgen : ∀ l, Algebra.adjoin ℂ (Set.range (ρ l)) = ⊤) :
    (typeAlgebra V N ρ : Set (Matrix (Carrier V N) (Carrier V N) ℂ)) = intAlgebra V N := by
  apply le_antisymm
  · have : typeAlgebra V N ρ ≤ blockStarSubalgebra V N := by
      refine StarAlgebra.adjoin_le ?_
      rintro _ (⟨g, rfl⟩ | ⟨l, rfl⟩)
      · exact ⟨_, rfl⟩
      · exact ⟨_, rfl⟩
    exact this
  · rintro _ ⟨b, rfl⟩
    rw [intAction_sum]
    refine sum_mem fun l _ => ?_
    have hM : ∀ M ∈ Algebra.adjoin ℂ (Set.range (ρ l)),
        intAction V N (Pi.single l M) ∈ typeAlgebra V N ρ := by
      intro M hM
      induction hM using Algebra.adjoin_induction with
      | mem x hx =>
        obtain ⟨g, rfl⟩ := hx
        have h1 : typeProj V N l ∈ typeAlgebra V N ρ :=
          StarAlgebra.subset_adjoin ℂ _ (Or.inr ⟨l, rfl⟩)
        have h2 : gaugeAction V N ρ g ∈ typeAlgebra V N ρ :=
          StarAlgebra.subset_adjoin ℂ _ (Or.inl ⟨g, rfl⟩)
        have := mul_mem h1 h2
        rwa [typeProj, gaugeAction, ← intAction_mul, single_mul_family] at this
      | algebraMap r =>
        have h1 : typeProj V N l ∈ typeAlgebra V N ρ :=
          StarAlgebra.subset_adjoin ℂ _ (Or.inr ⟨l, rfl⟩)
        have hs : (Pi.single l (r • (1 : Matrix (V l) (V l) ℂ)) : ∀ l, Matrix (V l) (V l) ℂ) =
            r • Pi.single l 1 := by
          funext l'
          by_cases h : l' = l
          · subst h; simp
          · simp [Pi.single_eq_of_ne h]
        rw [Algebra.algebraMap_eq_smul_one, hs, intAction_smul]
        exact SMulMemClass.smul_mem r h1
      | add x y _ _ hx hy =>
        rw [Pi.single_add, intAction_add]
        exact add_mem hx hy
      | mul x y _ _ hx hy =>
        have hs : (Pi.single l (x * y) : ∀ l, Matrix (V l) (V l) ℂ) =
            Pi.single l x * Pi.single l y := by
          funext l'
          by_cases h : l' = l
          · subst h; simp
          · simp [Pi.single_eq_of_ne h]
        rw [hs, intAction_mul]
        exact mul_mem hx hy
    exact hM (b l) (by rw [hgen l]; trivial)

end Generic

/-! ### Explicit generators of `M_3` and `M_2` inside `SU(3)`, `SU(2)` -/

/-- The cyclic permutation matrix in `SU(3)`. -/
def c3 : Matrix (Fin 3) (Fin 3) ℂ := !![0, 1, 0; 0, 0, 1; 1, 0, 0]
/-- `diag(1, -1, -1) ∈ SU(3)`. -/
def d1 : Matrix (Fin 3) (Fin 3) ℂ := !![1, 0, 0; 0, -1, 0; 0, 0, -1]
/-- `diag(-1, 1, -1) ∈ SU(3)`. -/
def d2 : Matrix (Fin 3) (Fin 3) ℂ := !![-1, 0, 0; 0, 1, 0; 0, 0, -1]
/-- `iσ_z = diag(i, -i) ∈ SU(2)`. -/
def sz : Matrix (Fin 2) (Fin 2) ℂ := !![Complex.I, 0; 0, -Complex.I]
/-- `iσ_y ∈ SU(2)`. -/
def sy : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]

theorem c3_mem : c3 ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
  refine ⟨?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [c3, Matrix.mul_apply, Fin.sum_univ_three]
  · simp [c3, Matrix.det_fin_three]

theorem d1_mem : d1 ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
  refine ⟨?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [d1, Matrix.mul_apply, Fin.sum_univ_three]
  · simp [d1, Matrix.det_fin_three]

theorem d2_mem : d2 ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
  refine ⟨?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [d2, Matrix.mul_apply, Fin.sum_univ_three]
  · simp [d2, Matrix.det_fin_three]

theorem sz_mem : sz ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
  refine ⟨?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [sz, Matrix.mul_apply, Fin.sum_univ_two]
  · simp [sz, Matrix.det_fin_two]

theorem sy_mem : sy ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff]
  refine ⟨?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [sy, Matrix.mul_apply, Fin.sum_univ_two]
  · simp [sy, Matrix.det_fin_two]

theorem c3_conj : c3.map (starRingEnd ℂ) = c3 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [c3]

theorem d1_conj : d1.map (starRingEnd ℂ) = d1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [d1]

theorem d2_conj : d2.map (starRingEnd ℂ) = d2 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [d2]

/-- A subalgebra containing all matrix units is everything. -/
theorem eq_top_of_singles {n : Type*} [Fintype n] [DecidableEq n]
    (A : Subalgebra ℂ (Matrix n n ℂ)) (h : ∀ i j, Matrix.single i j (1 : ℂ) ∈ A) : A = ⊤ := by
  rw [eq_top_iff]
  intro X _
  rw [Matrix.matrix_eq_sum_single X]
  refine sum_mem fun i _ => sum_mem fun j _ => ?_
  rw [show Matrix.single i j (X i j) = X i j • Matrix.single i j (1 : ℂ) by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]]
  exact A.smul_mem (h i j) _

/-- A subalgebra containing all diagonal matrix units and a matrix with no zero entry is
everything. -/
theorem eq_top_of_diag_singles {n : Type*} [Fintype n] [DecidableEq n]
    (A : Subalgebra ℂ (Matrix n n ℂ)) (hd : ∀ i, Matrix.single i i (1 : ℂ) ∈ A)
    (M : Matrix n n ℂ) (hM : M ∈ A) (hne : ∀ i j, M i j ≠ 0) : A = ⊤ := by
  refine eq_top_of_singles A fun i j => ?_
  have key : Matrix.single i i (1 : ℂ) * M * Matrix.single j j 1 =
      M i j • Matrix.single i j (1 : ℂ) := by
    ext a b
    simp only [Matrix.mul_apply, Matrix.single_apply, Matrix.smul_apply, smul_eq_mul]
    by_cases ha : i = a <;> by_cases hb : j = b <;> simp [ha, hb, Finset.sum_ite_eq']
  have h1 : M i j • Matrix.single i j (1 : ℂ) ∈ A := key ▸ mul_mem (mul_mem (hd i) hM) (hd j)
  have := A.smul_mem h1 (M i j)⁻¹
  rwa [smul_smul, inv_mul_cancel₀ (hne i j), one_smul] at this

/-- **`d₁, d₂, c₃` generate `M_3(ℂ)`.** -/
theorem su3_adjoin_eq_top (A : Subalgebra ℂ (Matrix (Fin 3) (Fin 3) ℂ)) (h1 : d1 ∈ A)
    (h2 : d2 ∈ A) (hc : c3 ∈ A) : A = ⊤ := by
  have e0 : Matrix.single (0 : Fin 3) (0 : Fin 3) (1 : ℂ) = (1 / 2 : ℂ) • (1 + d1) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [d1, Matrix.single_apply] <;> norm_num
  have e1 : Matrix.single (1 : Fin 3) (1 : Fin 3) (1 : ℂ) = (1 / 2 : ℂ) • (1 + d2) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [d2, Matrix.single_apply] <;> norm_num
  have e2 : Matrix.single (2 : Fin 3) (2 : Fin 3) (1 : ℂ) =
      1 - Matrix.single (0 : Fin 3) (0 : Fin 3) (1 : ℂ) -
        Matrix.single (1 : Fin 3) (1 : Fin 3) (1 : ℂ) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.single_apply, Matrix.one_apply]
  have m0 : Matrix.single (0 : Fin 3) (0 : Fin 3) (1 : ℂ) ∈ A := by
    rw [e0]; exact A.smul_mem (add_mem (one_mem _) h1) _
  have m1 : Matrix.single (1 : Fin 3) (1 : Fin 3) (1 : ℂ) ∈ A := by
    rw [e1]; exact A.smul_mem (add_mem (one_mem _) h2) _
  have m2 : Matrix.single (2 : Fin 3) (2 : Fin 3) (1 : ℂ) ∈ A := by
    rw [e2]; exact sub_mem (sub_mem (one_mem _) m0) m1
  refine eq_top_of_diag_singles A (fun i => by fin_cases i <;> assumption) (1 + c3 + c3 * c3)
    (add_mem (add_mem (one_mem _) hc) (mul_mem hc hc)) fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [c3, Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply]

/-- **`iσ_z, iσ_y` generate `M_2(ℂ)`.** -/
theorem su2_adjoin_eq_top (A : Subalgebra ℂ (Matrix (Fin 2) (Fin 2) ℂ)) (hz : sz ∈ A)
    (hy : sy ∈ A) : A = ⊤ := by
  have e0 : Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : ℂ) = (1 / 2 : ℂ) • (1 - Complex.I • sz) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [sz, Matrix.single_apply] <;> norm_num
  have e1 : Matrix.single (1 : Fin 2) (1 : Fin 2) (1 : ℂ) =
      1 - Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : ℂ) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.single_apply, Matrix.one_apply]
  have m0 : Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : ℂ) ∈ A := by
    rw [e0]; exact A.smul_mem (sub_mem (one_mem _) (A.smul_mem hz _)) _
  have m1 : Matrix.single (1 : Fin 2) (1 : Fin 2) (1 : ℂ) ∈ A := by
    rw [e1]; exact sub_mem (one_mem _) m0
  refine eq_top_of_diag_singles A (fun i => by fin_cases i <;> assumption) (1 + sy)
    (add_mem (one_mem _) hy) fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [sy, Matrix.one_apply]

/-! ### The represented fermion modules -/

/-- The fermion types `Q, u^c, d^c, L, e^c, ν^c`. -/
inductive MatterType
  | Q | uc | dc | L | ec | nuc
  deriving DecidableEq

instance : Fintype MatterType where
  elems := {.Q, .uc, .dc, .L, .ec, .nuc}
  complete x := by cases x <;> simp

/-- The carriers `V_f`. -/
def matterV : MatterType → Type
  | .Q => Fin 3 × Fin 2
  | .uc => Fin 3
  | .dc => Fin 3
  | .L => Fin 2
  | .ec => Unit
  | .nuc => Unit

instance matterV.fintype : ∀ t, Fintype (matterV t)
  | .Q => inferInstanceAs (Fintype (Fin 3 × Fin 2))
  | .uc => inferInstanceAs (Fintype (Fin 3))
  | .dc => inferInstanceAs (Fintype (Fin 3))
  | .L => inferInstanceAs (Fintype (Fin 2))
  | .ec => inferInstanceAs (Fintype Unit)
  | .nuc => inferInstanceAs (Fintype Unit)

instance matterV.decEq : ∀ t, DecidableEq (matterV t)
  | .Q => inferInstanceAs (DecidableEq (Fin 3 × Fin 2))
  | .uc => inferInstanceAs (DecidableEq (Fin 3))
  | .dc => inferInstanceAs (DecidableEq (Fin 3))
  | .L => inferInstanceAs (DecidableEq (Fin 2))
  | .ec => inferInstanceAs (DecidableEq Unit)
  | .nuc => inferInstanceAs (DecidableEq Unit)

/-- The represented actions `ρ_f` of `prop:faithful-SM-quotient`. -/
noncomputable def matterRep : ∀ t, SMGaugeCover →* Matrix (matterV t) (matterV t) ℂ
  | .Q => repQ
  | .uc => repUc
  | .dc => repDc
  | .L => repL
  | .ec => repEc
  | .nuc => repNuc

/-- A cover element with only a colour component. -/
noncomputable def colourElt (g : SMGaugeSU3) : SMGaugeCover := ((g, 1), 1)
/-- A cover element with only a weak component. -/
noncomputable def weakElt (g : SMGaugeSU2) : SMGaugeCover := ((1, g), 1)

/-- The left embedding `M ↦ M ⊗ I`. -/
def leftEmbed (m k : Type*) [Fintype m] [DecidableEq m] [Fintype k] [DecidableEq k] :
    Matrix m m ℂ →ₐ[ℂ] Matrix (m × k) (m × k) ℂ where
  toFun M := M ⊗ₖ (1 : Matrix k k ℂ)
  map_one' := Matrix.one_kronecker_one
  map_mul' M M' := by rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]
  map_zero' := Matrix.zero_kronecker _
  map_add' M M' := Matrix.add_kronecker _ _ _
  commutes' r := by
    simp only [Algebra.algebraMap_eq_smul_one, Matrix.smul_kronecker, Matrix.one_kronecker_one]

/-- The right embedding `M ↦ I ⊗ M`. -/
def rightEmbed (m k : Type*) [Fintype m] [DecidableEq m] [Fintype k] [DecidableEq k] :
    Matrix k k ℂ →ₐ[ℂ] Matrix (m × k) (m × k) ℂ where
  toFun M := (1 : Matrix m m ℂ) ⊗ₖ M
  map_one' := Matrix.one_kronecker_one
  map_mul' M M' := by rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]
  map_zero' := Matrix.kronecker_zero _
  map_add' M M' := Matrix.kronecker_add _ _ _
  commutes' r := by
    simp only [Algebra.algebraMap_eq_smul_one, Matrix.kronecker_smul, Matrix.one_kronecker_one]

theorem repQ_colour (g : SMGaugeSU3) :
    repQ (colourElt g) = leftEmbed (Fin 3) (Fin 2) g.1 := by
  simp [repQ, colourElt, leftEmbed]

theorem repQ_weak (g : SMGaugeSU2) : repQ (weakElt g) = rightEmbed (Fin 3) (Fin 2) g.1 := by
  simp [repQ, weakElt, rightEmbed]

theorem repUc_colour (g : SMGaugeSU3) : repUc (colourElt g) = g.1.map (starRingEnd ℂ) := by
  simp [repUc, colourElt]

theorem repDc_colour (g : SMGaugeSU3) : repDc (colourElt g) = g.1.map (starRingEnd ℂ) := by
  simp [repDc, colourElt]

theorem repL_weak (g : SMGaugeSU2) : repL (weakElt g) = g.1 := by
  simp [repL, weakElt]

theorem adjoin_repUc_eq_top : Algebra.adjoin ℂ (Set.range repUc) = ⊤ := by
  refine su3_adjoin_eq_top _ ?_ ?_ ?_
  · exact Algebra.subset_adjoin ⟨colourElt ⟨d1, d1_mem⟩, by rw [repUc_colour, d1_conj]⟩
  · exact Algebra.subset_adjoin ⟨colourElt ⟨d2, d2_mem⟩, by rw [repUc_colour, d2_conj]⟩
  · exact Algebra.subset_adjoin ⟨colourElt ⟨c3, c3_mem⟩, by rw [repUc_colour, c3_conj]⟩

theorem adjoin_repDc_eq_top : Algebra.adjoin ℂ (Set.range repDc) = ⊤ := by
  refine su3_adjoin_eq_top _ ?_ ?_ ?_
  · exact Algebra.subset_adjoin ⟨colourElt ⟨d1, d1_mem⟩, by rw [repDc_colour, d1_conj]⟩
  · exact Algebra.subset_adjoin ⟨colourElt ⟨d2, d2_mem⟩, by rw [repDc_colour, d2_conj]⟩
  · exact Algebra.subset_adjoin ⟨colourElt ⟨c3, c3_mem⟩, by rw [repDc_colour, c3_conj]⟩

theorem adjoin_repL_eq_top : Algebra.adjoin ℂ (Set.range repL) = ⊤ := by
  refine su2_adjoin_eq_top _ ?_ ?_
  · exact Algebra.subset_adjoin ⟨weakElt ⟨sz, sz_mem⟩, by rw [repL_weak]⟩
  · exact Algebra.subset_adjoin ⟨weakElt ⟨sy, sy_mem⟩, by rw [repL_weak]⟩

theorem unit_adjoin_eq_top (A : Subalgebra ℂ (Matrix Unit Unit ℂ)) : A = ⊤ := by
  refine eq_top_of_singles A fun i j => ?_
  have : Matrix.single i j (1 : ℂ) = (1 : Matrix Unit Unit ℂ) := by
    ext a b; simp [Matrix.single_apply, Matrix.one_apply]
  rw [this]; exact one_mem _

theorem adjoin_repQ_eq_top : Algebra.adjoin ℂ (Set.range repQ) = ⊤ := by
  set A := Algebra.adjoin ℂ (Set.range repQ)
  have hc : ∀ g : SMGaugeSU3, leftEmbed (Fin 3) (Fin 2) g.1 ∈ A := fun g =>
    Algebra.subset_adjoin ⟨colourElt g, repQ_colour g⟩
  have hw : ∀ g : SMGaugeSU2, rightEmbed (Fin 3) (Fin 2) g.1 ∈ A := fun g =>
    Algebra.subset_adjoin ⟨weakElt g, repQ_weak g⟩
  have h3 : A.comap (leftEmbed (Fin 3) (Fin 2)) = ⊤ :=
    su3_adjoin_eq_top _ (hc ⟨d1, d1_mem⟩) (hc ⟨d2, d2_mem⟩) (hc ⟨c3, c3_mem⟩)
  have h2 : A.comap (rightEmbed (Fin 3) (Fin 2)) = ⊤ :=
    su2_adjoin_eq_top _ (hw ⟨sz, sz_mem⟩) (hw ⟨sy, sy_mem⟩)
  refine eq_top_of_singles A fun ia jb => ?_
  obtain ⟨i, a⟩ := ia
  obtain ⟨j, b⟩ := jb
  have hl : leftEmbed (Fin 3) (Fin 2) (Matrix.single i j 1) ∈ A := by
    have : Matrix.single i j (1 : ℂ) ∈ A.comap (leftEmbed (Fin 3) (Fin 2)) := by
      rw [h3]; trivial
    exact this
  have hr : rightEmbed (Fin 3) (Fin 2) (Matrix.single a b 1) ∈ A := by
    have : Matrix.single a b (1 : ℂ) ∈ A.comap (rightEmbed (Fin 3) (Fin 2)) := by
      rw [h2]; trivial
    exact this
  have hsplit : (Matrix.single (i, a) (j, b) (1 : ℂ) : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ)
      = leftEmbed (Fin 3) (Fin 2) (Matrix.single i j 1) *
        rightEmbed (Fin 3) (Fin 2) (Matrix.single a b 1) := by
    show _ = (Matrix.single i j (1 : ℂ) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) *
      ((1 : Matrix (Fin 3) (Fin 3) ℂ) ⊗ₖ Matrix.single a b (1 : ℂ))
    rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul,
      Matrix.single_kronecker_single, mul_one]
  have h := mul_mem hl hr
  rwa [← hsplit] at h

/-- **Each represented fermion module generates its full matrix algebra** (irreducibility in
Burnside form). -/
theorem matterRep_adjoin_eq_top (t : MatterType) :
    Algebra.adjoin ℂ (Set.range (matterRep t)) = ⊤ := by
  cases t with
  | Q => exact adjoin_repQ_eq_top
  | uc => exact adjoin_repUc_eq_top
  | dc => exact adjoin_repDc_eq_top
  | L => exact adjoin_repL_eq_top
  | ec => exact unit_adjoin_eq_top _
  | nuc => exact unit_adjoin_eq_top _

/-- The abstract block sizes `(6, 3, 3, 2, 1)` (and `1` for `ν^c`). -/
theorem matter_block_sizes :
    Fintype.card (matterV .Q) = 6 ∧ Fintype.card (matterV .uc) = 3 ∧
      Fintype.card (matterV .dc) = 3 ∧ Fintype.card (matterV .L) = 2 ∧
      Fintype.card (matterV .ec) = 1 ∧ Fintype.card (matterV .nuc) = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl

/-- **`prop:typed-matter-lift`.**  For any family of represented fermion sectors
`κ : Λ → MatterType` (e.g. `{Q, u^c, d^c, L, e^c}` with or without `ν^c`) with multiplicity
spaces `N_f` on `ℋ_mat ≅ ℂ⁴ ⊗ ⊕_f V_f ⊗ N_f`:

* `𝒜_type = C^*(r(g), p_f) = ⊕_f I_4 ⊗ B(V_f) ⊗ I_{N_f}` (`eq:typed-matter-lift`);
* it commutes with `𝒜_Cl = {⊕ a ⊗ I ⊗ I}`;
* the abstract block sizes are `(6,3,3,2,1)` (plus `1` for `ν^c`);
* for every represented incidence family `Y_e` on these sectors (any operator-Schmidt rank,
  including non-factorizing incidences), the joint packet `P` has typed internal algebra
  `𝒜_type`, its action algebra is `C^*(𝒜_Cl, 𝒜_type, Y_e, Y_e^*)`, and the main duality
  `𝒜_act' = ι(𝓜_type)`, `ι(𝓜_type)' = 𝒜_act` of `thm:main-duality` holds. -/
theorem typed_matter_lift {Λ : Type*} [Fintype Λ] [DecidableEq Λ] (κ : Λ → MatterType)
    (N : Λ → Type*) [∀ l, Fintype (N l)] [∀ l, DecidableEq (N l)] :
    ((typeAlgebra (fun l => matterV (κ l)) N (fun l => matterRep (κ l)) :
        Set (Matrix (Carrier (fun l => matterV (κ l)) N) (Carrier (fun l => matterV (κ l)) N)
          ℂ)) = intAlgebra (fun l => matterV (κ l)) N) ∧
    (∀ x ∈ extAlgebra (fun l => matterV (κ l)) N,
      ∀ y ∈ (typeAlgebra (fun l => matterV (κ l)) N (fun l => matterRep (κ l)) :
        Set (Matrix (Carrier (fun l => matterV (κ l)) N) (Carrier (fun l => matterV (κ l)) N)
          ℂ)), x * y = y * x) ∧
    (Fintype.card (matterV .Q) = 6 ∧ Fintype.card (matterV .uc) = 3 ∧
      Fintype.card (matterV .dc) = 3 ∧ Fintype.card (matterV .L) = 2 ∧
      Fintype.card (matterV .ec) = 1 ∧ Fintype.card (matterV .nuc) = 1) ∧
    (∀ {E : Type*} [Fintype E] (P : RepresentedJointPacket Λ (fun l => matterV (κ l)) N E),
      P.actionAlgebra = jointActionAlgebra (extAlgebra (fun l => matterV (κ l)) N)
        (typeAlgebra (fun l => matterV (κ l)) N (fun l => matterRep (κ l)) :
          Set (Matrix (Carrier (fun l => matterV (κ l)) N)
            (Carrier (fun l => matterV (κ l)) N) ℂ)) P.incidenceOp ∧
      matCommutant (P.actionAlgebra : Set (Matrix (Carrier (fun l => matterV (κ l)) N)
          (Carrier (fun l => matterV (κ l)) N) ℂ)) =
        ArbitraryIncidenceDuality.iotaTypedMultiplicity P ∧
      matCommutant (ArbitraryIncidenceDuality.iotaTypedMultiplicity P) =
        (P.actionAlgebra : Set (Matrix (Carrier (fun l => matterV (κ l)) N)
          (Carrier (fun l => matterV (κ l)) N) ℂ))) := by
  have hT := typeAlgebra_eq_intAlgebra (V := fun l => matterV (κ l)) (N := N)
    (fun l => matterRep (κ l)) fun l => matterRep_adjoin_eq_top (κ l)
  refine ⟨hT, ?_, matter_block_sizes, fun P => ?_⟩
  · intro x hx y hy
    rw [hT] at hy
    exact extAlgebra_commute_intAlgebra x hx y hy
  · exact ⟨by rw [hT]; rfl, ArbitraryIncidenceDuality.actionAlgebra_commutant P,
      ArbitraryIncidenceDuality.typedMultiplicity_commutant P⟩

end TypedMatterLift
end RenewalGeometry
