/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.DiscreteAnalysis.GridFaaDiBrunoStability
import RenewalGeometry.Analysis.PeriodicGridResidualInverseEstimate
import RenewalGeometry.Analysis.IteratedDerivBounds

/-!
# Difference-quotient prolongation of characteristic Strang splitting and a uniform
  discrete Faà di Bruno bound (infrastructure for `eq:supp-gowdy-state-error`, `r ≥ 1`;
  emergent-spacetime supplement)

The `C^r_ℓ` analysis of a nonlinear grid scheme needs bounds for forward differences
`D₊ᵏ` of compositions `F(X_j)` of smooth maps with grid functions, uniform in the spacing `ℓ`
(a discrete Faà di Bruno / Moser estimate).  This file organises that estimate as a
**prolongation**: a grid state `X` is replaced by the pair array `(X_j, D₊X_j)`, and the
characteristic data `(Π±, Π₀, F, g±)` by the prolonged data on `V × V`

`F̃(z, w) = (F z, ℓ⁻¹ (F(z + ℓw) - F z))`,  `g̃±(z, w) = ℓ⁻¹ (g±(z + ℓw) - g±(z))`,
projections acting diagonally.

* `CharData.prol`, `CGrid.prol`; `prol_isSrc`, `prol_transport`, `prol_isSplit`: **the
  prolongation of a split step of the scheme is exactly a split step of the prolonged scheme**
  (the implicit-midpoint relation and the transport commute with `X ↦ (X, D₊X)`; no
  uniqueness of the implicit stages is used).
* `charCr`, `distK`: the characteristic `C^k_ℓ` distance
  `distK k X Y = max (max_{i ≤ k} sup_j charNorm (D₊ⁱ(X - Y))_j, ‖D₊ᵏ(λ - λ')‖_∞)`;
  `distK_prol`: `distK k` of the prolongations is `distK (k+1)` of the original states, and
  `distK_le_crNorm`, `crNorm_le_distK`: comparison with the `C^r_ℓ` norm
  `‖·‖_{r,∞,ℓ}` of `Analysis/PeriodicGridResidualInverseEstimate.lean`.
* `derivBound_diffQuot` (**uniform discrete Faà di Bruno bound**): if `f` is `C^∞` on an open
  convex set `U` with `‖Dⁱf‖ ≤ M` for `i ≤ m + 1`, then the difference quotient
  `(z, w) ↦ ℓ⁻¹(f(z + ℓw) - f z)` has `‖Dⁱ‖ ≤ M (ρ + m) 2^m` for `i ≤ m` on
  `{z ∈ U, z + ℓw ∈ U, ‖w‖ < ρ}`, uniformly in `0 < ℓ ≤ 1`.
* `lipschitz_of_derivBound`, `symm_of_derivBound`: Lipschitz and second-difference bounds from
  derivative bounds on convex sets.
-/

open Set Finset
open scoped BigOperators ContDiff

set_option linter.unusedSectionVars false

namespace RenewalGeometry.GridFaaDiBruno

noncomputable section

open PeriodicGridResidual IteratedDerivBounds

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-! ### Prolongation of data and grid states -/

namespace CharData

variable (c : CharData V) {N : ℕ}

/-- The difference-quotient prolongation of characteristic data with spacing `ℓ`. -/
def prol (ℓ : ℝ) : CharData (V × V) where
  Pp := c.Pp.prodMap c.Pp
  Pm := c.Pm.prodMap c.Pm
  P0 := c.P0.prodMap c.P0
  F x := (c.F x.1, ℓ⁻¹ • (c.F (x.1 + ℓ • x.2) - c.F x.1))
  gp x := ℓ⁻¹ * (c.gp (x.1 + ℓ • x.2) - c.gp x.1)
  gm x := ℓ⁻¹ * (c.gm (x.1 + ℓ • x.2) - c.gm x.1)

variable {c}

theorem prol_proj (hc : c.Proj) (ℓ : ℝ) : (c.prol ℓ).Proj where
  sum v := by
    refine Prod.ext ?_ ?_ <;> simp [prol, hc.sum]
  norm_Pp v := by
    simp only [prol, LinearMap.prodMap_apply, Prod.norm_def]
    exact max_le_max (hc.norm_Pp _) (hc.norm_Pp _)
  norm_Pm v := by
    simp only [prol, LinearMap.prodMap_apply, Prod.norm_def]
    exact max_le_max (hc.norm_Pm _) (hc.norm_Pm _)
  norm_P0 v := by
    simp only [prol, LinearMap.prodMap_apply, Prod.norm_def]
    exact max_le_max (hc.norm_P0 _) (hc.norm_P0 _)
  pp v := by simp [prol, hc.pp]
  pm v := by simp [prol, hc.pm]
  p0 v := by simp [prol, hc.p0]
  mp v := by simp [prol, hc.mp]
  mm v := by simp [prol, hc.mm]
  m0 v := by simp [prol, hc.m0]
  zp v := by simp [prol, hc.zp]
  zm v := by simp [prol, hc.zm]
  zz v := by simp [prol, hc.zz]

theorem charNorm_prol (ℓ : ℝ) (x : V × V) :
    (c.prol ℓ).charNorm x = max (c.charNorm x.1) (c.charNorm x.2) := by
  simp only [charNorm, prol, LinearMap.prodMap_apply, Prod.norm_def]
  apply le_antisymm
  · refine max_le (max_le ?_ ?_) (max_le (max_le ?_ ?_) (max_le ?_ ?_))
    · exact (le_max_left _ _).trans (le_max_left _ _)
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_left _ _)
    · exact ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
    · exact ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_left _ _)
    · exact ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  · refine max_le (max_le ?_ (max_le ?_ ?_)) (max_le ?_ (max_le ?_ ?_))
    · exact (le_max_left _ _).trans (le_max_left _ _)
    · exact (le_max_left _ _).trans ((le_max_left _ _).trans (le_max_right _ _))
    · exact (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
    · exact (le_max_right _ _).trans (le_max_left _ _)
    · exact (le_max_right _ _).trans ((le_max_left _ _).trans (le_max_right _ _))
    · exact (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))

end CharData

/-- The prolonged array `j ↦ (v_j, (D₊v)_j)`. -/
def prolArr {N : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (ℓ : ℝ)
    (v : ZMod N → E) : ZMod N → E × E :=
  fun j => (v j, PeriodicGridResidual.fwdDiff ℓ v j)

/-- The prolonged grid state `(X_j, D₊X_j)` with background `D₊λ`. -/
def CGrid.prol {N : ℕ} (ℓ : ℝ) (X : CGrid V N) : CGrid (V × V) N where
  site := prolArr ℓ X.site
  lam := PeriodicGridResidual.fwdDiff ℓ X.lam

namespace CharData

variable {c : CharData V} {N : ℕ}

theorem add_smul_fwdDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ℓ : ℝ}
    (hℓ : ℓ ≠ 0) (v : ZMod N → E) (j : ZMod N) : v j + ℓ • PeriodicGridResidual.fwdDiff ℓ v j = v (j + 1) := by
  simp only [PeriodicGridResidual.fwdDiff, smul_smul, mul_inv_cancel₀ hℓ, one_smul]
  abel

/-- **The prolongation of an implicit-midpoint source step is a source step of the prolonged
data.** -/
theorem prol_isSrc {ℓ σ : ℝ} (hℓ : ℓ ≠ 0) {X Y : CGrid V N} (h : c.IsSrc σ X Y) :
    (c.prol ℓ).IsSrc σ (X.prol ℓ) (Y.prol ℓ) := by
  refine ⟨fun j => ?_, by simp [CGrid.prol, h.2]⟩
  have hm : ∀ k, (1 / 2 : ℝ) • (X.site k + Y.site k) + ℓ • ((1 / 2 : ℝ) •
      (PeriodicGridResidual.fwdDiff ℓ X.site k + PeriodicGridResidual.fwdDiff ℓ Y.site k)) = (1 / 2 : ℝ) • (X.site (k + 1) + Y.site (k + 1)) := by
    intro k
    rw [← add_smul_fwdDiff hℓ X.site k, ← add_smul_fwdDiff hℓ Y.site k]
    module
  refine Prod.ext ?_ ?_
  · simp only [CGrid.prol, prolArr, prol, Prod.smul_mk, Prod.fst_add, Prod.smul_fst]
    exact h.1 j
  · simp only [CGrid.prol, prolArr, prol, Prod.smul_mk, Prod.snd_add, Prod.smul_snd,
      Prod.fst_add, Prod.smul_fst, Prod.snd_add]
    rw [hm j]
    have d1 : Y.site (j + 1) - X.site (j + 1) =
        σ • c.F ((1 / 2 : ℝ) • (X.site (j + 1) + Y.site (j + 1))) := by
      conv_lhs => rw [h.1 (j + 1)]
      abel
    have d0 : Y.site j - X.site j = σ • c.F ((1 / 2 : ℝ) • (X.site j + Y.site j)) := by
      conv_lhs => rw [h.1 j]
      abel
    have e : Y.site (j + 1) - Y.site j = (X.site (j + 1) - X.site j) +
        (σ • c.F ((1 / 2 : ℝ) • (X.site (j + 1) + Y.site (j + 1))) -
          σ • c.F ((1 / 2 : ℝ) • (X.site j + Y.site j))) := by
      rw [← d1, ← d0]; abel
    simp only [PeriodicGridResidual.fwdDiff]
    rw [e]
    module

theorem prol_transport {ℓ : ℝ} (hℓ : ℓ ≠ 0) (X : CGrid V N) :
    (c.transport ℓ X).prol ℓ = (c.prol ℓ).transport ℓ (X.prol ℓ) := by
  have hX := fun k => add_smul_fwdDiff hℓ X.site k
  ext j
  · simp [CGrid.prol, prolArr, transport, prol]
  · simp only [CGrid.prol, prolArr, transport, prol, LinearMap.prodMap_apply, Prod.snd_add,
      PeriodicGridResidual.fwdDiff, sub_add_cancel, add_sub_cancel_right]
    simp only [map_smul, map_sub, smul_add, smul_sub]
    abel
  · simp only [CGrid.prol, prolArr, transport, prol]
    rw [hX j, hX (j + 1), hX (j - 1), sub_add_cancel]
    simp only [PeriodicGridResidual.fwdDiff, smul_eq_mul, add_sub_cancel_right]
    field_simp
    ring

/-- **The prolongation of a split step is a split step of the prolonged data.** -/
theorem prol_isSplit {ℓ : ℝ} (hℓ : ℓ ≠ 0) {X A B : CGrid V N} (h : c.IsSplit ℓ X A B) :
    (c.prol ℓ).IsSplit ℓ (X.prol ℓ) (A.prol ℓ) (B.prol ℓ) := by
  refine ⟨prol_isSrc hℓ h.1, ?_⟩
  rw [← prol_transport hℓ]
  exact prol_isSrc hℓ h.2

end CharData

/-! ### Componentwise forward differences -/

section Arrays

variable {N : ℕ} {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E']
  [NormedSpace ℝ E']

theorem fwdDiff_pair (ℓ : ℝ) (a : ZMod N → E) (b : ZMod N → E') :
    PeriodicGridResidual.fwdDiff ℓ (fun j => (a j, b j)) = fun j => (PeriodicGridResidual.fwdDiff ℓ a j, PeriodicGridResidual.fwdDiff ℓ b j) := by
  funext j; simp [PeriodicGridResidual.fwdDiff]

theorem iterate_fwdDiff_pair (ℓ : ℝ) (k : ℕ) (a : ZMod N → E) (b : ZMod N → E') :
    (PeriodicGridResidual.fwdDiff ℓ)^[k] (fun j => (a j, b j)) =
      fun j => ((PeriodicGridResidual.fwdDiff ℓ)^[k] a j, (PeriodicGridResidual.fwdDiff ℓ)^[k] b j) := by
  induction k generalizing a b with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, fwdDiff_pair, ih, Function.iterate_succ_apply,
      Function.iterate_succ_apply]

theorem iterate_fwdDiff_prolArr (ℓ : ℝ) (k : ℕ) (v : ZMod N → E) :
    (PeriodicGridResidual.fwdDiff ℓ)^[k] (prolArr ℓ v) = prolArr ℓ ((PeriodicGridResidual.fwdDiff ℓ)^[k] v) := by
  unfold prolArr
  rw [iterate_fwdDiff_pair, ← Function.iterate_succ_apply' (PeriodicGridResidual.fwdDiff ℓ),
    Function.iterate_succ_apply]

theorem norm_pair_le [NeZero N] {a : ZMod N → E} {b : ZMod N → E'} {C : ℝ} (ha : ‖a‖ ≤ C)
    (hb : ‖b‖ ≤ C) : ‖fun j => (a j, b j)‖ ≤ C :=
  (pi_norm_le_iff_of_nonneg ((norm_nonneg _).trans ha)).2 fun j =>
    norm_prod_le_iff.2 ⟨(norm_le_pi_norm a j).trans ha, (norm_le_pi_norm b j).trans hb⟩

theorem norm_fst_le_pair [NeZero N] (a : ZMod N → E) (b : ZMod N → E') :
    ‖a‖ ≤ ‖fun j => (a j, b j)‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j =>
    (norm_fst_le ((fun j => (a j, b j)) j)).trans (norm_le_pi_norm (fun j => (a j, b j)) j)

theorem norm_snd_le_pair [NeZero N] (a : ZMod N → E) (b : ZMod N → E') :
    ‖b‖ ≤ ‖fun j => (a j, b j)‖ :=
  (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j =>
    (norm_snd_le ((fun j => (a j, b j)) j)).trans (norm_le_pi_norm (fun j => (a j, b j)) j)

theorem prolArr_sub (ℓ : ℝ) (v w : ZMod N → E) :
    prolArr ℓ v - prolArr ℓ w = prolArr ℓ (v - w) := by
  funext j
  simp only [prolArr, Pi.sub_apply, Prod.mk_sub_mk, PeriodicGridResidual.fwdDiff, smul_sub]
  congr 1
  abel

theorem fwdDiff_sub' (ℓ : ℝ) (v w : ZMod N → E) :
    PeriodicGridResidual.fwdDiff ℓ v - PeriodicGridResidual.fwdDiff ℓ w = PeriodicGridResidual.fwdDiff ℓ (v - w) := by
  funext j; simp only [PeriodicGridResidual.fwdDiff, Pi.sub_apply, ← smul_sub]; congr 1; abel

end Arrays

/-! ### The characteristic `C^k_ℓ` distance -/

namespace CharData

variable {c : CharData V} {N : ℕ} [NeZero N]

variable (c) in
/-- `charCr k v = max_{i ≤ k} sup_j charNorm ((D₊ⁱ v)_j)` (defined recursively). -/
def charCr (ℓ : ℝ) : ℕ → (ZMod N → V) → ℝ
  | 0, v => c.charSup v
  | k + 1, v => max (c.charSup v) (charCr ℓ k (PeriodicGridResidual.fwdDiff ℓ v))

variable (c) in
/-- The characteristic `C^k_ℓ` distance of two grid states. -/
def distK (k : ℕ) (ℓ : ℝ) (X Y : CGrid V N) : ℝ :=
  max (c.charCr ℓ k (X.site - Y.site)) ‖(PeriodicGridResidual.fwdDiff ℓ)^[k] (X.lam - Y.lam)‖

theorem distK_zero (ℓ : ℝ) (X Y : CGrid V N) : c.distK 0 ℓ X Y = c.dist0 X Y := rfl

theorem charSup_le_charCr (ℓ : ℝ) (k : ℕ) (v : ZMod N → V) : c.charSup v ≤ c.charCr ℓ k v := by
  cases k with
  | zero => exact le_rfl
  | succ k => exact le_max_left _ _

theorem charSup_iterate_le_charCr (ℓ : ℝ) {i k : ℕ} (hik : i ≤ k) (v : ZMod N → V) :
    c.charSup ((PeriodicGridResidual.fwdDiff ℓ)^[i] v) ≤ c.charCr ℓ k v := by
  induction k generalizing i v with
  | zero =>
    obtain rfl : i = 0 := Nat.le_zero.1 hik
    exact le_rfl
  | succ k ih =>
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · exact le_max_left _ _
    · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      rw [Function.iterate_succ_apply]
      exact (ih (by omega) _).trans (le_max_right _ _)

theorem charCr_le_of (ℓ : ℝ) {k : ℕ} {v : ZMod N → V} {C : ℝ}
    (h : ∀ i ≤ k, c.charSup ((PeriodicGridResidual.fwdDiff ℓ)^[i] v) ≤ C) : c.charCr ℓ k v ≤ C := by
  induction k generalizing v with
  | zero => exact h 0 le_rfl
  | succ k ih =>
    refine max_le (h 0 (Nat.zero_le _)) (ih fun i hi => ?_)
    rw [← Function.iterate_succ_apply]
    exact h (i + 1) (by omega)

theorem charCr_nonneg (ℓ : ℝ) (k : ℕ) (v : ZMod N → V) : 0 ≤ c.charCr ℓ k v :=
  (charSup_nonneg v).trans (charSup_le_charCr ℓ k v)

theorem charCr_add_le (ℓ : ℝ) (k : ℕ) (v w : ZMod N → V) :
    c.charCr ℓ k (v + w) ≤ c.charCr ℓ k v + c.charCr ℓ k w := by
  refine charCr_le_of ℓ fun i hi => ?_
  rw [iterate_fwdDiff_add]
  exact (charSup_add_le _ _).trans (add_le_add (charSup_iterate_le_charCr ℓ hi v)
    (charSup_iterate_le_charCr ℓ hi w))

theorem charSup_prol (ℓ : ℝ) (v : ZMod N → V) :
    (c.prol ℓ).charSup (prolArr ℓ v) = max (c.charSup v) (c.charSup (PeriodicGridResidual.fwdDiff ℓ v)) := by
  apply le_antisymm
  · refine charSup_le fun j => ?_
    rw [charNorm_prol]
    exact max_le_max (charNorm_le_charSup v j) (charNorm_le_charSup (PeriodicGridResidual.fwdDiff ℓ v) j)
  · refine max_le (charSup_le fun j => ?_) (charSup_le fun j => ?_)
    · refine le_trans ?_ (charNorm_le_charSup (c := c.prol ℓ) (prolArr ℓ v) j)
      rw [charNorm_prol]; exact le_max_left _ _
    · refine le_trans ?_ (charNorm_le_charSup (c := c.prol ℓ) (prolArr ℓ v) j)
      rw [charNorm_prol]; exact le_max_right _ _

/-- `charCr k` of a prolonged array is `charCr (k+1)` of the array. -/
theorem charCr_prol (ℓ : ℝ) (k : ℕ) (v : ZMod N → V) :
    (c.prol ℓ).charCr ℓ k (prolArr ℓ v) = c.charCr ℓ (k + 1) v := by
  induction k generalizing v with
  | zero => simp only [charCr, charSup_prol]
  | succ k ih =>
    simp only [charCr] at ih ⊢
    rw [charSup_prol]
    have hf : PeriodicGridResidual.fwdDiff ℓ (prolArr ℓ v) = prolArr ℓ (PeriodicGridResidual.fwdDiff ℓ v) := by
      have := iterate_fwdDiff_prolArr ℓ 1 v
      simpa using this
    rw [hf, ih]
    have h := charSup_le_charCr (c := c) ℓ (k + 1) (PeriodicGridResidual.fwdDiff ℓ v)
    simp only [charCr] at h
    rw [max_assoc, max_eq_right h]

/-- **`distK k` of the prolonged states is `distK (k+1)` of the states.** -/
theorem distK_prol (ℓ : ℝ) (k : ℕ) (X Y : CGrid V N) :
    (c.prol ℓ).distK k ℓ (X.prol ℓ) (Y.prol ℓ) = c.distK (k + 1) ℓ X Y := by
  unfold distK
  have hs : (X.prol ℓ).site - (Y.prol ℓ).site = prolArr ℓ (X.site - Y.site) :=
    prolArr_sub ℓ _ _
  have hl : (X.prol ℓ).lam - (Y.prol ℓ).lam = PeriodicGridResidual.fwdDiff ℓ (X.lam - Y.lam) := fwdDiff_sub' ℓ _ _
  rw [hs, hl, charCr_prol, ← Function.iterate_succ_apply]

theorem distK_nonneg (k : ℕ) (ℓ : ℝ) (X Y : CGrid V N) : 0 ≤ c.distK k ℓ X Y :=
  (norm_nonneg _).trans (le_max_right _ _)

theorem distK_triangle (k : ℕ) (ℓ : ℝ) (X Y Z : CGrid V N) :
    c.distK k ℓ X Z ≤ c.distK k ℓ X Y + c.distK k ℓ Y Z := by
  unfold distK
  have hs : X.site - Z.site = (X.site - Y.site) + (Y.site - Z.site) := by abel
  have hl : X.lam - Z.lam = (X.lam - Y.lam) + (Y.lam - Z.lam) := by abel
  rw [hs, hl, iterate_fwdDiff_add]
  refine max_le ((charCr_add_le ℓ k _ _).trans (add_le_add (le_max_left _ _)
    (le_max_left _ _))) ((norm_add_le _ _).trans (add_le_add (le_max_right _ _)
    (le_max_right _ _)))

/-- The error array `j ↦ (X_j - Y_j, λ_j - λ'_j)` of two grid states. -/
def errA (X Y : CGrid V N) : ZMod N → V × ℝ := fun j => (X.site j - Y.site j, X.lam j - Y.lam j)

theorem iterate_fwdDiff_errA (ℓ : ℝ) (i : ℕ) (X Y : CGrid V N) :
    (PeriodicGridResidual.fwdDiff ℓ)^[i] (errA X Y) =
      fun j => ((PeriodicGridResidual.fwdDiff ℓ)^[i] (X.site - Y.site) j, (PeriodicGridResidual.fwdDiff ℓ)^[i] (X.lam - Y.lam) j) := by
  unfold errA
  exact iterate_fwdDiff_pair ℓ i (X.site - Y.site) (X.lam - Y.lam)

/-- The characteristic `C^k_ℓ` distance is dominated by the `C^k_ℓ` norm of the error array. -/
theorem distK_le_crNorm (hc : c.Proj) (k : ℕ) (ℓ : ℝ) (X Y : CGrid V N) :
    c.distK k ℓ X Y ≤ crNorm k ℓ (errA X Y) := by
  have hle : ∀ i ≤ k, ‖(PeriodicGridResidual.fwdDiff ℓ)^[i] (errA X Y)‖ ≤ crNorm k ℓ (errA X Y) := fun i hi =>
    Finset.le_sup' (fun i => ‖(PeriodicGridResidual.fwdDiff ℓ)^[i] (errA X Y)‖) (mem_range.2 (Nat.lt_succ_of_le hi))
  refine max_le (charCr_le_of ℓ fun i hi => ?_) ?_
  · refine (charSup_le_norm hc _).trans ((le_of_eq ?_).trans ((norm_fst_le_pair
      ((PeriodicGridResidual.fwdDiff ℓ)^[i] (X.site - Y.site))
      ((PeriodicGridResidual.fwdDiff ℓ)^[i] (X.lam - Y.lam))).trans ?_))
    · rfl
    · rw [← iterate_fwdDiff_errA]; exact hle i hi
  · refine (norm_snd_le_pair ((PeriodicGridResidual.fwdDiff ℓ)^[k] (X.site - Y.site)) _).trans ?_
    rw [← iterate_fwdDiff_errA]; exact hle k le_rfl

/-- **The `C^r_ℓ` norm of the error array is at most `3 max_{k ≤ r} distK k`.** -/
theorem crNorm_le_distK (hc : c.Proj) (r : ℕ) (ℓ : ℝ) (X Y : CGrid V N) {B : ℝ}
    (h : ∀ k ≤ r, c.distK k ℓ X Y ≤ B) : crNorm r ℓ (errA X Y) ≤ 3 * B := by
  refine Finset.sup'_le _ _ fun i hi => ?_
  have hi' : i ≤ r := Nat.lt_succ_iff.1 (mem_range.1 hi)
  have hB := h i hi'
  have hB0 : 0 ≤ B := (distK_nonneg i ℓ X Y).trans hB
  rw [iterate_fwdDiff_errA]
  refine norm_pair_le ?_ ?_
  · refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
    refine (norm_le_three_mul_charNorm hc _).trans ?_
    have : c.charNorm ((PeriodicGridResidual.fwdDiff ℓ)^[i] (X.site - Y.site) j) ≤ c.distK i ℓ X Y :=
      (charNorm_le_charSup _ j).trans ((charSup_iterate_le_charCr ℓ le_rfl _).trans
        (le_max_left _ _))
    linarith
  · have : ‖(PeriodicGridResidual.fwdDiff ℓ)^[i] (X.lam - Y.lam)‖ ≤ c.distK i ℓ X Y := le_max_right _ _
    linarith

end CharData

/-! ### Calculus: derivative bounds give Lipschitz, second-difference and difference-quotient
bounds -/

section Calculus

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Mean value bound for an iterated derivative on a convex open set. -/
theorem norm_iteratedFDeriv_sub_le {f : E → F} {U : Set E} (hU : IsOpen U) (hUc : Convex ℝ U)
    {k : ℕ} {M : ℝ} (hf : DerivBound f U (k + 1) M) {x y : E} (hx : x ∈ U) (hy : y ∈ U) :
    ‖iteratedFDeriv ℝ k f y - iteratedFDeriv ℝ k f x‖ ≤ M * ‖y - x‖ := by
  refine hUc.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (fun z hz => ?_) (fun z hz => ?_) hx hy
  · exact (hf.contDiffAt hU hz).differentiableAt_iteratedFDeriv
      (by exact_mod_cast ENat.coe_lt_top k)
  · rw [norm_fderiv_iteratedFDeriv]; exact hf.bound z hz (k + 1) le_rfl

/-- **Lipschitz bound from a first-derivative bound** on a convex open set. -/
theorem lipschitz_of_derivBound {f : E → F} {U : Set E} (hU : IsOpen U) (hUc : Convex ℝ U)
    {K : ℕ} {M : ℝ} (hf : DerivBound f U K M) (hK : 1 ≤ K) {x y : E} (hx : x ∈ U) (hy : y ∈ U) :
    ‖f x - f y‖ ≤ M * ‖x - y‖ :=
  hUc.norm_image_sub_le_of_norm_fderiv_le (fun z hz => (hf.contDiffAt hU hz).differentiableAt
    (by simp)) (fun z hz => hf.norm_fderiv_le hK hz) hy hx

/-- **Second-difference bound from a second-derivative bound** on a convex open set:
`‖f x + f y - 2 f((x+y)/2)‖ ≤ M ‖x - y‖²`. -/
theorem symm_of_derivBound {f : E → F} {U : Set E} (hU : IsOpen U) (hUc : Convex ℝ U)
    {K : ℕ} {M : ℝ} (hf : DerivBound f U K M) (hK : 2 ≤ K) {x y : E} (hx : x ∈ U) (hy : y ∈ U) :
    ‖f x + f y - (2 : ℝ) • f ((1 / 2 : ℝ) • (x + y))‖ ≤ M * ‖x - y‖ ^ 2 := by
  set m := (1 / 2 : ℝ) • (x + y)
  set d := (1 / 2 : ℝ) • (y - x)
  have hm : m ∈ U := by
    have := hUc hx hy (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)
    simpa [m, smul_add] using this
  have hM : 0 ≤ M := hf.nonneg hx
  have hfd : DerivBound (fderiv ℝ f) U (K - 1) M := by
    have : DerivBound f U ((K - 1) + 1) M := by rwa [Nat.sub_add_cancel (by omega)]
    exact this.fderiv hU
  -- `g z = f z - Df(m) z` has derivative `Df z - Df m`
  have hlip : ∀ z ∈ U, ‖fderiv ℝ f z - fderiv ℝ f m‖ ≤ M * ‖z - m‖ := fun z hz =>
    lipschitz_of_derivBound hU hUc hfd (by omega) hz hm
  have hside : ∀ z ∈ U, (∀ s ∈ segment ℝ m z, s ∈ U) →
      ‖f z - f m - fderiv ℝ f m (z - m)‖ ≤ M * ‖z - m‖ * ‖z - m‖ := by
    intro z hz hseg
    have hg := (convex_segment m z).norm_image_sub_le_of_norm_fderiv_le
      (f := fun w => f w - fderiv ℝ f m w) (C := M * ‖z - m‖)
      (fun w hw => ((hf.contDiffAt hU (hseg w hw)).differentiableAt (by simp)).sub
        (fderiv ℝ f m).differentiableAt)
      (fun w hw => by
        have hd : fderiv ℝ (fun w => f w - fderiv ℝ f m w) w = fderiv ℝ f w - fderiv ℝ f m := by
          rw [fderiv_fun_sub ((hf.contDiffAt hU (hseg w hw)).differentiableAt (by simp))
            (fderiv ℝ f m).differentiableAt, ContinuousLinearMap.fderiv]
        rw [hd]
        refine (hlip w (hseg w hw)).trans (mul_le_mul_of_nonneg_left ?_ hM)
        rw [segment_eq_image'] at hw
        obtain ⟨t, ht, rfl⟩ := hw
        rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
        exact mul_le_of_le_one_left (norm_nonneg _) ht.2)
      (left_mem_segment ℝ m z) (right_mem_segment ℝ m z)
    have e : f z - fderiv ℝ f m z - (f m - fderiv ℝ f m m) = f z - f m - fderiv ℝ f m (z - m) := by
      rw [map_sub]; abel
    rw [← e]; exact hg
  have hseg : ∀ z ∈ U, ∀ s ∈ segment ℝ m z, s ∈ U := fun z hz s hs =>
    hUc.segment_subset hm hz hs
  have h1 := hside y hy (hseg y hy)
  have h2 := hside x hx (hseg x hx)
  have ey : y - m = d := by simp only [m, d]; module
  have ex : x - m = -d := by simp only [m, d]; module
  rw [ey] at h1
  rw [ex, map_neg, norm_neg] at h2
  have e : f x + f y - (2 : ℝ) • f m =
      (f y - f m - fderiv ℝ f m d) + (f x - f m - -fderiv ℝ f m d) := by
    rw [two_smul]; abel
  rw [e]
  have hd : ‖d‖ = ‖x - y‖ / 2 := by
    simp only [d, norm_smul, Real.norm_eq_abs]
    rw [norm_sub_rev]; norm_num; ring
  calc _ ≤ ‖f y - f m - fderiv ℝ f m d‖ + ‖f x - f m - -fderiv ℝ f m d‖ := norm_add_le _ _
    _ ≤ M * ‖d‖ * ‖d‖ + M * ‖d‖ * ‖d‖ := add_le_add h1 h2
    _ = M * ‖x - y‖ ^ 2 / 2 := by rw [hd]; ring
    _ ≤ M * ‖x - y‖ ^ 2 := by nlinarith [sq_nonneg ‖x - y‖]

/-- Difference of two right compositions of a multilinear map with continuous linear maps. -/
theorem norm_compCLM_sub_le {k : ℕ} (T : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) F)
    (A B : G →L[ℝ] E) {c : ℝ} (hA : ‖A‖ ≤ c) (hB : ‖B‖ ≤ c) :
    ‖T.compContinuousLinearMap (fun _ => A) - T.compContinuousLinearMap (fun _ => B)‖ ≤
      ‖T‖ * (k * (‖A - B‖ * c ^ (k - 1))) := by
  classical
  have hc : 0 ≤ c := (norm_nonneg _).trans hA
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun v => ?_
  simp only [ContinuousMultilinearMap.sub_apply,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  refine (T.norm_image_sub_le' _ _).trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hterm : ∀ i : Fin k, (∏ j, if j = i then ‖A (v i) - B (v i)‖ else
      max ‖A (v j)‖ ‖B (v j)‖) ≤ (‖A - B‖ * c ^ (k - 1)) * ∏ j, ‖v j‖ := by
    intro i
    calc (∏ j, if j = i then ‖A (v i) - B (v i)‖ else max ‖A (v j)‖ ‖B (v j)‖)
        ≤ ∏ j, ((if j = i then ‖A - B‖ else c) * ‖v j‖) := by
          refine Finset.prod_le_prod (fun j _ => by split_ifs <;> positivity) fun j _ => ?_
          split_ifs with h
          · subst h
            rw [← ContinuousLinearMap.sub_apply]
            exact (A - B).le_opNorm _
          · exact max_le ((A.le_opNorm _).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg _)))
              ((B.le_opNorm _).trans (mul_le_mul_of_nonneg_right hB (norm_nonneg _)))
      _ = (∏ j, if j = i then ‖A - B‖ else c) * ∏ j, ‖v j‖ := Finset.prod_mul_distrib
      _ = (‖A - B‖ * c ^ (k - 1)) * ∏ j, ‖v j‖ := by
          congr 1
          rw [← Finset.mul_prod_erase _ _ (mem_univ i), if_pos rfl]
          congr 1
          rw [Finset.prod_congr rfl (g := fun _ => c) (fun j hj => if_neg (ne_of_mem_erase hj)),
            Finset.prod_const, Finset.card_erase_of_mem (mem_univ i), Finset.card_univ,
            Fintype.card_fin]
  calc (∑ i : Fin k, ∏ j, if j = i then ‖A (v i) - B (v i)‖ else max ‖A (v j)‖ ‖B (v j)‖)
      ≤ ∑ _i : Fin k, (‖A - B‖ * c ^ (k - 1)) * ∏ j, ‖v j‖ := Finset.sum_le_sum fun i _ => hterm i
    _ = k * (‖A - B‖ * c ^ (k - 1)) * ∏ j, ‖v j‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- The domain `{(z, w) : z ∈ U, z + ℓw ∈ U, ‖w‖ < ρ}` of the difference quotient. -/
def diffDom (U : Set E) (ℓ ρ : ℝ) : Set (E × E) := {x | x.1 ∈ U ∧ x.1 + ℓ • x.2 ∈ U ∧ ‖x.2‖ < ρ}

theorem isOpen_diffDom {U : Set E} (hU : IsOpen U) (ℓ ρ : ℝ) : IsOpen (diffDom U ℓ ρ) := by
  show IsOpen ({x : E × E | x.1 ∈ U} ∩ ({x | x.1 + ℓ • x.2 ∈ U} ∩ {x | ‖x.2‖ < ρ}))
  refine (hU.preimage continuous_fst).inter ((hU.preimage ?_).inter
    (isOpen_lt (continuous_norm.comp continuous_snd) continuous_const))
  exact continuous_fst.add (continuous_snd.const_smul ℓ)

theorem convex_diffDom {U : Set E} (hU : Convex ℝ U) (ℓ ρ : ℝ) : Convex ℝ (diffDom U ℓ ρ) := by
  intro x hx y hy a b ha hb hab
  refine ⟨?_, ?_, ?_⟩
  · simpa using hU hx.1 hy.1 ha hb hab
  · have := hU hx.2.1 hy.2.1 ha hb hab
    convert this using 1
    simp only [Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd]
    module
  · have := (convex_ball (0 : E) ρ) (mem_ball_zero_iff.2 hx.2.2) (mem_ball_zero_iff.2 hy.2.2)
      ha hb hab
    simpa using mem_ball_zero_iff.1 this

/-- **Uniform discrete Faà di Bruno bound for the difference quotient.**  If `f` is `C^∞` on an
open convex set `U` with `‖Dⁱ f‖ ≤ M` for `i ≤ m + 1`, then for `0 < ℓ ≤ 1` the difference quotient
`G(z, w) = ℓ⁻¹ (f(z + ℓw) - f z)` satisfies `‖Dⁱ G‖ ≤ M (ρ + m) 2^m` for `i ≤ m` on
`{z ∈ U, z + ℓw ∈ U, ‖w‖ < ρ}` — uniformly in `ℓ`. -/
theorem derivBound_diffQuot {f : E → F} {U : Set E} (hU : IsOpen U) (hUc : Convex ℝ U)
    {m : ℕ} {M ℓ ρ : ℝ} (hf : DerivBound f U (m + 1) M) (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1)
    (hρ : 0 ≤ ρ) :
    DerivBound (fun x : E × E => ℓ⁻¹ • (f (x.1 + ℓ • x.2) - f x.1)) (diffDom U ℓ ρ) m
      (M * (ρ + m) * 2 ^ m) := by
  obtain ⟨A, hAdef⟩ : ∃ A : E × E →L[ℝ] E,
      A = ContinuousLinearMap.fst ℝ E E + ℓ • ContinuousLinearMap.snd ℝ E E := ⟨_, rfl⟩
  obtain ⟨π, hπdef⟩ : ∃ π : E × E →L[ℝ] E, π = ContinuousLinearMap.fst ℝ E E := ⟨_, rfl⟩
  have hA : ∀ x, A x = x.1 + ℓ • x.2 := fun x => by simp [hAdef]
  have hπ : ∀ x, π x = x.1 := fun x => by simp [hπdef]
  set U' := diffDom U ℓ ρ
  have hU' : IsOpen U' := isOpen_diffDom hU ℓ ρ
  have hmA : MapsTo A U' U := fun x hx => by rw [hA]; exact hx.2.1
  have hmπ : MapsTo π U' U := fun x hx => by rw [hπ]; exact hx.1
  have hcA : ContDiffOn ℝ ∞ (fun x => f (A x)) U' := hf.contDiffOn.comp A.contDiff.contDiffOn hmA
  have hcπ : ContDiffOn ℝ ∞ (fun x => f (π x)) U' :=
    hf.contDiffOn.comp π.contDiff.contDiffOn hmπ
  have hG : (fun x : E × E => ℓ⁻¹ • (f (x.1 + ℓ • x.2) - f x.1)) =
      fun x => ℓ⁻¹ • (f (A x) - f (π x)) := by
    funext x; rw [hA, hπ]
  rw [hG]
  refine ⟨(hcA.sub hcπ).const_smul ℓ⁻¹, fun x hx k hk => ?_⟩
  have hM : 0 ≤ M := hf.nonneg hx.1
  have hxA := hmA hx
  have hxπ := hmπ hx
  have hcAx : ContDiffAt ℝ ∞ (fun x => f (A x)) x := hcA.contDiffAt (hU'.mem_nhds hx)
  have hcπx : ContDiffAt ℝ ∞ (fun x => f (π x)) x := hcπ.contDiffAt (hU'.mem_nhds hx)
  have e1 : iteratedFDeriv ℝ k (fun y => ℓ⁻¹ • (f (A y) - f (π y))) x =
      ℓ⁻¹ • (iteratedFDeriv ℝ k (fun y => f (A y)) x - iteratedFDeriv ℝ k (fun y => f (π y)) x) := by
    rw [iteratedFDeriv_const_smul_apply' ((hcAx.sub hcπx).of_le (by exact_mod_cast le_top))]
    congr 1
    exact iteratedFDeriv_sub_apply (hcAx.of_le (by exact_mod_cast le_top))
      (hcπx.of_le (by exact_mod_cast le_top))
  rw [e1, DerivBound.iteratedFDeriv_comp_clm hf.contDiffOn hU A hxA k,
    DerivBound.iteratedFDeriv_comp_clm hf.contDiffOn hU π hxπ k]
  set T1 := iteratedFDeriv ℝ k f (A x)
  set T0 := iteratedFDeriv ℝ k f (π x)
  have hsplit : T1.compContinuousLinearMap (fun _ => A) - T0.compContinuousLinearMap (fun _ => π) =
      (T1 - T0).compContinuousLinearMap (fun _ => A) +
        (T0.compContinuousLinearMap (fun _ => A) - T0.compContinuousLinearMap (fun _ => π)) := by
    ext v; simp
  have hAn : ‖A‖ ≤ 2 := by
    rw [hAdef]
    calc _ ≤ ‖ContinuousLinearMap.fst ℝ E E‖ + ‖ℓ • ContinuousLinearMap.snd ℝ E E‖ :=
          norm_add_le _ _
      _ ≤ 1 + ℓ * 1 := by
          refine add_le_add (ContinuousLinearMap.norm_fst_le ℝ E E) ?_
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hℓ]
          exact mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_snd_le ℝ E E) hℓ.le
      _ ≤ 2 := by linarith
  have hπn : ‖π‖ ≤ 2 := by rw [hπdef]; exact (ContinuousLinearMap.norm_fst_le ℝ E E).trans (by norm_num)
  have hAπ : ‖A - π‖ ≤ ℓ := by
    have : A - π = ℓ • ContinuousLinearMap.snd ℝ E E := by
      ext v <;> simp [hAdef, hπdef]
    rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos hℓ]
    exact mul_le_of_le_one_right hℓ.le (ContinuousLinearMap.norm_snd_le ℝ E E)
  have hT0 : ‖T0‖ ≤ M := hf.bound (π x) hxπ k (by omega)
  have hT10 : ‖T1 - T0‖ ≤ M * (ℓ * ρ) := by
    have h := norm_iteratedFDeriv_sub_le hU hUc (hf.mono (K' := k + 1) (by omega) le_rfl) hxπ hxA
    refine h.trans (mul_le_mul_of_nonneg_left ?_ hM)
    rw [hA, hπ, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hℓ]
    exact mul_le_mul_of_nonneg_left hx.2.2.le hℓ.le
  have hP1 : ‖(T1 - T0).compContinuousLinearMap (fun _ => A)‖ ≤ M * (ℓ * ρ) * 2 ^ k := by
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact mul_le_mul hT10 (pow_le_pow_left₀ (norm_nonneg _) hAn k) (by positivity)
      (by positivity)
  have hP2 : ‖T0.compContinuousLinearMap (fun _ => A) -
      T0.compContinuousLinearMap (fun _ => π)‖ ≤ M * (k * (ℓ * 2 ^ (k - 1))) := by
    refine (norm_compCLM_sub_le T0 A π hAn hπn).trans ?_
    refine mul_le_mul hT0 ?_ (by positivity) hM
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hAπ (by positivity))
      (Nat.cast_nonneg k)
  rw [hsplit, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hℓ]
  have hk' : (k : ℝ) ≤ m := by exact_mod_cast hk
  have h2k : (2 : ℝ) ^ (k - 1) ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) (by omega)
  have h2k' : (2 : ℝ) ^ k ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hk
  calc ℓ⁻¹ * ‖(T1 - T0).compContinuousLinearMap (fun _ => A) +
        (T0.compContinuousLinearMap (fun _ => A) - T0.compContinuousLinearMap (fun _ => π))‖
      ≤ ℓ⁻¹ * (M * (ℓ * ρ) * 2 ^ k + M * (k * (ℓ * 2 ^ (k - 1)))) :=
        mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add hP1 hP2))
          (inv_nonneg.2 hℓ.le)
    _ = M * ρ * 2 ^ k + M * k * 2 ^ (k - 1) := by field_simp
    _ ≤ M * ρ * 2 ^ m + M * m * 2 ^ m := by
        have := mul_le_mul hk' h2k (by positivity) (Nat.cast_nonneg m)
        have := mul_le_mul_of_nonneg_left h2k' (mul_nonneg hM hρ)
        nlinarith
    _ = M * (ρ + m) * 2 ^ m := by ring

end Calculus

end

end RenewalGeometry.GridFaaDiBruno
