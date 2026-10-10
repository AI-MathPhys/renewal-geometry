/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.BallUhlenbeckPackage
import RenewalGeometry.Analysis.MatrixDetExp
import RenewalGeometry.Continuum.EinsteinSMFieldSpaces

/-!
# The Standard-Model structure group `G_SM = S(U(3) × U(2))` as a gauge structure

Structure-group input of `prop:critical-uhlenbeck` and `thm:critical-quotient-defect` of the
Einstein–Standard-Model action-closure manuscript (`eq:gauge-group`:
`G_SM = S(U(3) × U(2))`, in its defining block representation on `ℂ³ ⊕ ℂ²`).

* `GSM` — `S(U(3) × U(2)) ⊂ U(5)`: unitary `5 × 5` matrices, block-diagonal for `ℂ³ ⊕ ℂ²`,
  with determinant one;
* `gSM` — its Lie algebra `𝔰(𝔲(3) ⊕ 𝔲(2))`: skew-Hermitian, block-diagonal, trace zero, as a real
  subspace of `M₅(ℂ)`;
* `mem_gSM_iff`, `gSM_eq_map`, `gSMEquivSmLie` — `gSM` is the ledger encoding
  `EinsteinSM.smLie` (on `Fin 5 → Fin 5 → ℂ`) transported along `Matrix.of`;
* `isSMBlock_iff_commute` — block-diagonality is commutation with the colour projector;
* **`isGaugeStructure_SM`** — `IsGaugeStructure GSM gSM` (closed, `G·G ⊆ G`, `exp 𝔤 ⊆ G`,
  `Ad_G 𝔤 ⊆ 𝔤`, `𝔤` a Lie subalgebra of skew-Hermitian matrices);
* non-vacuity: the hypercharge generator `hyperY = i·diag(2,2,2,-3,-3) ∈ gSM` (nonzero), its
  exponential lies in `GSM`, and `diag(-1,-1,1,1,1) ∈ GSM` is a non-identity element.
-/

open Set Matrix NormedSpace

noncomputable section

namespace RenewalGeometry.BallAnalysis.SMGaugeStructure

open UhlenbeckPackage EinsteinSM

/-- `5 × 5` complex matrices (defining representation of `G_SM` on `ℂ³ ⊕ ℂ²`). -/
abbrev M5 := Matrix (Fin 5) (Fin 5) ℂ

/-- Block-diagonality for `ℂ³ ⊕ ℂ²` (`eq:gauge-group`): entries between the colour and the weak
blocks vanish. -/
def IsSMBlock (X : M5) : Prop := ∀ i j, colourBlock i ≠ colourBlock j → X i j = 0

/-- The orthogonal projector onto the colour block `ℂ³ ⊂ ℂ³ ⊕ ℂ²`. -/
def colourProj : M5 := diagonal fun i => if colourBlock i then 1 else 0

/-- Block-diagonal matrices are exactly those commuting with the colour projector. -/
theorem isSMBlock_iff_commute (X : M5) : IsSMBlock X ↔ Commute colourProj X := by
  constructor
  · intro h
    change colourProj * X = X * colourProj
    ext i j
    simp only [colourProj, diagonal_mul, mul_diagonal]
    by_cases hij : colourBlock i = colourBlock j
    · rw [hij]; ring
    · rw [h i j hij]; simp
  · intro h i j hij
    have e := congrFun (congrFun (show colourProj * X = X * colourProj from h) i) j
    simp only [colourProj, diagonal_mul, mul_diagonal] at e
    cases hi : colourBlock i <;> cases hj : colourBlock j <;> simp_all

theorem star_colourProj : star colourProj = colourProj := by
  ext i j
  simp only [colourProj, star_eq_conjTranspose, conjTranspose_apply, diagonal_apply]
  by_cases h : j = i
  · subst h; split_ifs <;> simp
  · rw [if_neg h, if_neg (Ne.symm h), star_zero]

/-- **`G_SM = S(U(3) × U(2))`** in its defining block representation: unitary `5 × 5` matrices,
block-diagonal for `ℂ³ ⊕ ℂ²`, with determinant one (`eq:gauge-group`). -/
def GSM : Set M5 := {U | U ∈ unitaryGroup (Fin 5) ℂ ∧ IsSMBlock U ∧ U.det = 1}

/-- **The Lie algebra `𝔰(𝔲(3) ⊕ 𝔲(2))` of `G_SM`**: skew-Hermitian, block-diagonal for
`ℂ³ ⊕ ℂ²`, trace zero. -/
def gSM : Submodule ℝ M5 where
  carrier := {X | star X = -X ∧ IsSMBlock X ∧ X.trace = 0}
  add_mem' := by
    rintro X Y ⟨h1, h2, h3⟩ ⟨k1, k2, k3⟩
    refine ⟨?_, fun i j hij => ?_, ?_⟩
    · rw [star_add, h1, k1, neg_add]
    · simp [h2 i j hij, k2 i j hij]
    · rw [trace_add, h3, k3, add_zero]
  zero_mem' := ⟨by simp, fun i j _ => rfl, by simp⟩
  smul_mem' := by
    rintro s X ⟨h1, h2, h3⟩
    refine ⟨?_, fun i j hij => ?_, ?_⟩
    · rw [star_smul, h1, star_trivial, smul_neg]
    · simp [h2 i j hij]
    · rw [trace_smul, h3, smul_zero]

theorem GSM_subset_unitary : GSM ⊆ (unitaryGroup (Fin 5) ℂ : Set M5) := fun _ h => h.1

/-! ### Identification with the ledger encoding `EinsteinSM.smLie` -/

/-- **`gSM` is `smLie`** (the encoding of `𝔰(𝔲(3) ⊕ 𝔲(2))` on `Fin 5 → Fin 5 → ℂ` used by the
field spaces of `def:tests`), transported along `Matrix.of`. -/
theorem mem_gSM_iff (X : LieFibre) : Matrix.of X ∈ gSM ↔ X ∈ smLie := by
  have hs : star (Matrix.of X) = -(Matrix.of X) ↔ ∀ i j, X j i = -star (X i j) := by
    constructor
    · intro h i j
      have e := congrFun (congrFun h j) i
      simp only [star_eq_conjTranspose, conjTranspose_apply, Matrix.neg_apply, of_apply] at e
      rw [e, neg_neg]
    · intro h
      ext i j
      simp only [star_eq_conjTranspose, conjTranspose_apply, Matrix.neg_apply, of_apply]
      rw [h j i, neg_neg]
  change (star (Matrix.of X) = -(Matrix.of X) ∧ IsSMBlock (Matrix.of X) ∧ (Matrix.of X).trace = 0) ↔
    (∀ i j, X j i = -star (X i j)) ∧ (∀ i j, colourBlock i ≠ colourBlock j → X i j = 0) ∧
      ∑ i, X i i = 0
  rw [hs]
  exact Iff.rfl

theorem gSM_eq_map :
    gSM = smLie.map ((Matrix.ofLinearEquiv ℝ : LieFibre ≃ₗ[ℝ] M5) : LieFibre →ₗ[ℝ] M5) := by
  ext X
  rw [Submodule.mem_map_equiv, ← mem_gSM_iff]
  exact Iff.rfl

/-- The `ℝ`-linear identification `gSM ≃ smLie`. -/
def gSMEquivSmLie : gSM ≃ₗ[ℝ] smLie :=
  (LinearEquiv.ofEq _ _ gSM_eq_map).trans
    (LinearEquiv.submoduleMap (Matrix.ofLinearEquiv ℝ : LieFibre ≃ₗ[ℝ] M5) smLie).symm

theorem gSMEquivSmLie_apply (X : gSM) :
    ((gSMEquivSmLie X : smLie) : LieFibre) = Matrix.of.symm X :=
  rfl

/-! ### The gauge-structure axioms -/

theorem isClosed_GSM : IsClosed GSM := by
  have e : GSM = (unitaryGroup (Fin 5) ℂ : Set M5) ∩
      ({U | colourProj * U = U * colourProj} ∩ {U | U.det = 1}) := by
    ext U
    simp only [GSM, mem_setOf_eq, mem_inter_iff, SetLike.mem_coe, isSMBlock_iff_commute]
    exact Iff.rfl
  rw [e]
  exact isClosed_unitaryGroup.inter
    ((isClosed_eq (continuous_const.matrix_mul continuous_id)
      (continuous_id.matrix_mul continuous_const)).inter
      (isClosed_eq continuous_id.matrix_det continuous_const))

theorem mul_mem_GSM {g h : M5} (hg : g ∈ GSM) (hh : h ∈ GSM) : g * h ∈ GSM := by
  refine ⟨Submonoid.mul_mem _ hg.1 hh.1, ?_, ?_⟩
  · exact (isSMBlock_iff_commute _).2
      (((isSMBlock_iff_commute _).1 hg.2.1).mul_right ((isSMBlock_iff_commute _).1 hh.2.1))
  · rw [det_mul, hg.2.2, hh.2.2, one_mul]

theorem exp_mem_GSM {X : M5} (hX : X ∈ gSM) : exp X ∈ GSM := by
  refine ⟨exp_mem_unitaryGroup hX.1, ?_, ?_⟩
  · exact (isSMBlock_iff_commute _).2 ((isSMBlock_iff_commute X).1 hX.2.1).exp_right
  · rw [MatrixDetExp.det_exp_eq_exp_trace, hX.2.2, exp_zero]

theorem commute_star_of_commute {g : M5} (h : Commute colourProj g) :
    Commute colourProj (star g) := by
  have e : star (colourProj * g) = star (g * colourProj) := by
    rw [show colourProj * g = g * colourProj from h]
  rw [star_mul, star_mul, star_colourProj] at e
  exact e.symm

theorem ad_mem_gSM {g X : M5} (hg : g ∈ GSM) (hX : X ∈ gSM) : g * X * star g ∈ gSM := by
  refine ⟨?_, ?_, ?_⟩
  · have hX' : star X = -X := hX.1
    rw [star_mul, star_mul, star_star, hX']
    noncomm_ring
  · have hPg := (isSMBlock_iff_commute _).1 hg.2.1
    exact (isSMBlock_iff_commute _).2
      ((hPg.mul_right ((isSMBlock_iff_commute _).1 hX.2.1)).mul_right (commute_star_of_commute hPg))
  · have hgg : star g * g = 1 := Matrix.mem_unitaryGroup_iff'.mp hg.1
    calc (g * X * star g).trace = (star g * (g * X)).trace := trace_mul_comm _ _
      _ = ((star g * g) * X).trace := by rw [mul_assoc]
      _ = 0 := by rw [hgg, one_mul, hX.2.2]

theorem bracket_mem_gSM {X Y : M5} (hX : X ∈ gSM) (hY : Y ∈ gSM) : X * Y - Y * X ∈ gSM := by
  refine ⟨?_, ?_, ?_⟩
  · have hX' : star X = -X := hX.1
    have hY' : star Y = -Y := hY.1
    rw [star_sub, star_mul, star_mul, hX', hY']
    noncomm_ring
  · have hPX := (isSMBlock_iff_commute _).1 hX.2.1
    have hPY := (isSMBlock_iff_commute _).1 hY.2.1
    exact (isSMBlock_iff_commute _).2 ((hPX.mul_right hPY).sub_right (hPY.mul_right hPX))
  · rw [trace_sub, trace_mul_comm, sub_self]

/-- **`(G_SM, 𝔰(𝔲(3) ⊕ 𝔲(2)))` is a gauge structure**: `𝔤_SM` is a real Lie subalgebra of
skew-Hermitian matrices, `G_SM` is closed, closed under products, contains `exp 𝔤_SM`, and
`Ad_{G_SM} 𝔤_SM ⊆ 𝔤_SM`. -/
theorem isGaugeStructure_SM : IsGaugeStructure GSM gSM where
  skew := fun _ hX => hX.1
  bracket := fun _ hX _ hY => bracket_mem_gSM hX hY
  closed := isClosed_GSM
  mul_mem := fun _ hg _ hh => mul_mem_GSM hg hh
  exp_mem := fun _ hX => exp_mem_GSM hX
  ad_mem := fun _ hg _ hX => ad_mem_gSM hg hX

/-! ### Non-vacuity -/

/-- The hypercharge generator `i·diag(2,2,2,-3,-3) ∈ 𝔰(𝔲(3) ⊕ 𝔲(2))`. -/
def hyperY : M5 := diagonal fun i => if colourBlock i then 2 * Complex.I else -3 * Complex.I

theorem hyperY_mem : hyperY ∈ gSM := by
  refine ⟨?_, fun i j hij => ?_, ?_⟩
  · ext i j
    rcases eq_or_ne i j with rfl | h
    · simp only [hyperY, star_eq_conjTranspose, conjTranspose_apply, Matrix.neg_apply,
        diagonal_apply_eq]
      split_ifs <;> simp
    · simp [hyperY, diagonal_apply_ne _ h, diagonal_apply_ne _ h.symm]
  · have hne : i ≠ j := fun e => hij (e ▸ rfl)
    simp [hyperY, diagonal_apply_ne _ hne]
  · simp only [hyperY, trace_diagonal, Fin.sum_univ_five]
    simp [colourBlock]
    ring

theorem hyperY_ne_zero : hyperY ≠ 0 := by
  intro h
  have e := congrFun (congrFun h 0) 0
  simp [hyperY, colourBlock] at e

/-- `exp (t·Y) ∈ G_SM` for the hypercharge generator. -/
example (t : ℝ) : exp (t • hyperY) ∈ GSM := exp_mem_GSM (gSM.smul_mem t hyperY_mem)

/-- `diag(-1,-1,1,1,1) ∈ G_SM`, a non-identity element. -/
def flipTwo : M5 := diagonal fun i => if (i : ℕ) < 2 then -1 else 1

theorem flipTwo_mem : flipTwo ∈ GSM := by
  refine ⟨?_, fun i j hij => ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff]
    simp only [flipTwo, star_eq_conjTranspose, diagonal_conjTranspose, diagonal_mul_diagonal]
    rw [← diagonal_one]
    congr 1
    funext i
    simp only [Pi.star_apply]
    split_ifs <;> simp
  · have hne : i ≠ j := fun e => hij (e ▸ rfl)
    simp [flipTwo, diagonal_apply_ne _ hne]
  · simp [flipTwo, det_diagonal, Fin.prod_univ_five]

theorem flipTwo_ne_one : flipTwo ≠ 1 := by
  intro h
  have e := congrFun (congrFun h 0) 0
  simp [flipTwo] at e
  norm_num at e

example : ∃ g ∈ GSM, g ≠ 1 := ⟨flipTwo, flipTwo_mem, flipTwo_ne_one⟩

example : ∃ X ∈ gSM, X ≠ 0 ∧ ∀ t : ℝ, exp (t • X) ∈ GSM :=
  ⟨hyperY, hyperY_mem, hyperY_ne_zero, fun t => exp_mem_GSM (gSM.smul_mem t hyperY_mem)⟩

end RenewalGeometry.BallAnalysis.SMGaugeStructure
