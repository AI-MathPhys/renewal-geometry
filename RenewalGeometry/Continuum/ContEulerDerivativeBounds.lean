/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Action.DiscreteEulerConsistency
import RenewalGeometry.Analysis.CompositionDifferenceBounds

/-!
# Derivative bounds for continuum Euler–Lagrange expressions of first-order densities

Generic infrastructure for `eq:native-source-tail` of the Einstein–Standard-Model action-closure
manuscript (`lem:native-tail-transfer`).  For a first-order density `L(θ; w, p)` (with a parameter
`θ`, the normalised scale `ν = 1/K` in the application) the continuum Euler expression
`E₀(Y) = ∂_wL(Y, ∂Y) - Σ_μ ∂_μ[∂_{p_μ}L(Y, ∂Y)]` (`DiscreteEulerConsistency.contEuler`) is
written through the gradient map `G(θ, w, p) = ∂_{(w,p)}L` as `eulerOp G θ Y`.

## Main results

* `norm_iteratedFDeriv_jet1_le`: `‖D^p(J¹Y)(z)‖ ≤ ‖D^pY(z)‖ + 4‖D^{p+1}Y(z)‖`.
* `contEuler_eq_eulerOp`: identification with `contEuler`.
* **`norm_iteratedFDeriv_eulerOp_le`**: `‖D^n E₀(Y)(z)‖ ≤ c_n M B^{n+1}`.
* **`norm_iteratedFDeriv_eulerOp_sub_le`** (difference / tail transfer):
  `‖D^n E₀(Y₁)(z) - D^n E₀(Y₀)(z)‖ ≤ c_n (n+2) M B^{n+1} η` whenever the first jets of
  `W = Y₁ - Y₀` satisfy `‖D^p(J¹W)(z)‖ ≤ η` for `p ≤ n + 1`, i.e. derivatives of `W` up to order
  `n + 2` only (the derivative count "at most `k + 2` field derivatives" of the manuscript).
  Here `M` bounds `D^kG`, `k ≤ n + 2`, on a convex set containing both jets, `B ≥ 1` bounds
  `D^p(J¹Y_i)(z)` for `1 ≤ p ≤ n + 1`, and `c_n = #OFP(n) + 4 #OFP(n+1)`.
-/

open Set Finset
open scoped ContDiff

namespace RenewalGeometry.ContEulerBounds

open DiscreteEulerConsistency (R4 evec jet1 contEuler norm_evec)

noncomputable section

set_option linter.unusedSectionVars false

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {Θ : Type*} [NormedAddCommGroup Θ] [NormedSpace ℝ Θ]

/-- The first-jet space `V × (Fin 4 → V)`. -/
abbrev JS (V : Type*) [NormedAddCommGroup V] := V × (Fin 4 → V)

/-- Covectors on the first-jet space (with the operator-norm topology induced by the norm of
`V`). -/
abbrev Cov (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] := JS V →L[ℝ] ℝ

/-- Covectors on `V`. -/
abbrev CovV (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] := V →L[ℝ] ℝ

/-- Continuous linear maps between normed spaces, with the topologies induced by the norms (used
to state types whose factors carry local norm instances, e.g. matrices). -/
abbrev NCLM (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] := E →L[ℝ] F

theorem natCast_le_infty (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top

/-- The value slot `V → V × V⁴` (norm topologies). -/
def inlJ (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] : NCLM V (JS V) :=
  ContinuousLinearMap.inl ℝ V (Fin 4 → V)

/-- The slot `p_μ` of `V × V⁴` (norm topologies). -/
def slotJ (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] (μ : Fin 4) : NCLM V (JS V) :=
  (ContinuousLinearMap.inr ℝ V (Fin 4 → V)).comp
    (ContinuousLinearMap.single ℝ (fun _ : Fin 4 => V) μ)

/-- The second factor `X → Θ × X` (norm topologies). -/
def inrP (Θ X : Type*) [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [NormedAddCommGroup X]
    [NormedSpace ℝ X] : NCLM X (Θ × X) := ContinuousLinearMap.inr ℝ Θ X

theorem inlJ_apply (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] (v : V) :
    inlJ V v = (v, 0) := rfl

theorem slotJ_apply (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] (μ : Fin 4) (v : V) :
    slotJ V μ v = (0, Pi.single μ v) := rfl

theorem inrP_apply (Θ X : Type*) [NormedAddCommGroup Θ] [NormedSpace ℝ Θ] [NormedAddCommGroup X]
    [NormedSpace ℝ X] (x : X) : inrP Θ X x = (0, x) := rfl

/-! ### Linear helpers -/

/-- `T ↦ (0, e_μ ⊗ T(e_μ))`. -/
def slotL (μ : Fin 4) : (R4 →L[ℝ] V) →L[ℝ] JS V :=
  (ContinuousLinearMap.inr ℝ V (Fin 4 → V)).comp
    ((ContinuousLinearMap.single ℝ (fun _ : Fin 4 => V) μ).comp
      (ContinuousLinearMap.apply ℝ V (evec μ)))

theorem norm_slotL_le (μ : Fin 4) : ‖(slotL μ : (R4 →L[ℝ] V) →L[ℝ] JS V)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun T => ?_
  simp only [slotL, ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.inr_apply, ContinuousLinearMap.apply_apply, one_mul]
  rw [Prod.norm_mk, norm_zero, max_eq_right (norm_nonneg _), ContinuousLinearMap.single_apply,
    Pi.norm_single]
  calc ‖T (evec μ)‖ ≤ ‖T‖ * ‖evec μ‖ := T.le_opNorm _
    _ = ‖T‖ := by rw [norm_evec, mul_one]

/-- Precomposition `T ↦ T ∘ ι` of covectors. -/
def preL {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
    [NormedSpace ℝ Y] (ι : X →L[ℝ] Y) : (Y →L[ℝ] ℝ) →L[ℝ] (X →L[ℝ] ℝ) :=
  (ContinuousLinearMap.compL ℝ X Y ℝ).flip ι

theorem preL_apply {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
    [NormedSpace ℝ Y] (ι : X →L[ℝ] Y) (T : Y →L[ℝ] ℝ) : preL ι T = T.comp ι := rfl

theorem norm_preL_le {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
    [NormedSpace ℝ Y] (ι : X →L[ℝ] Y) (hι : ‖ι‖ ≤ 1) : ‖preL ι‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun T => ?_
  rw [preL_apply, one_mul]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_of_le_one_right (norm_nonneg _) hι)

theorem norm_inl_le : ‖ContinuousLinearMap.inl ℝ V (Fin 4 → V)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => by simp

theorem norm_inr_single_le (μ : Fin 4) :
    ‖(ContinuousLinearMap.inr ℝ V (Fin 4 → V)).comp
      (ContinuousLinearMap.single ℝ (fun _ : Fin 4 => V) μ)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => by
    simp [Pi.norm_single]

/-! ### The first jet -/

theorem jet1_eq (Y : R4 → V) : jet1 Y = fun z =>
    ContinuousLinearMap.inl ℝ V (Fin 4 → V) (Y z) + ∑ μ, slotL μ (fderiv ℝ Y z) := by
  funext z
  refine Prod.ext ?_ ?_
  · simp [jet1, slotL, Prod.fst_sum]
  · simp only [jet1, slotL, Prod.snd_add, ContinuousLinearMap.inl_apply, Prod.snd_sum,
      ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.inr_apply,
      ContinuousLinearMap.apply_apply, ContinuousLinearMap.single_apply, zero_add]
    exact (Finset.univ_sum_single (fun μ => fderiv ℝ Y z (evec μ))).symm

theorem contDiff_jet1 {n : ℕ} {Y : R4 → V} (hY : ContDiff ℝ (n + 1) Y) :
    ContDiff ℝ n (jet1 Y) := by
  rw [jet1_eq]
  have hd : ContDiff ℝ n (fderiv ℝ Y) := hY.fderiv_right (by exact_mod_cast le_refl _)
  exact ((ContinuousLinearMap.inl ℝ V (Fin 4 → V)).contDiff.comp (hY.of_le
    (by exact_mod_cast Nat.le_succ n))).add
    (ContDiff.sum fun μ _ => (ContinuousLinearMap.contDiff (slotL (V := V) μ)).comp hd)

/-- `‖D^p(J¹Y)(z)‖ ≤ ‖D^pY(z)‖ + 4‖D^{p+1}Y(z)‖`. -/
theorem norm_iteratedFDeriv_jet1_le {p : ℕ} {Y : R4 → V} (hY : ContDiff ℝ (p + 1) Y) (z : R4) :
    ‖iteratedFDeriv ℝ p (jet1 Y) z‖ ≤
      ‖iteratedFDeriv ℝ p Y z‖ + 4 * ‖iteratedFDeriv ℝ (p + 1) Y z‖ := by
  rw [jet1_eq]
  have hd : ContDiff ℝ p (fderiv ℝ Y) := hY.fderiv_right (by exact_mod_cast le_refl _)
  have hY' : ContDiff ℝ p Y := hY.of_le (by exact_mod_cast Nat.le_succ p)
  have h1 : ContDiff ℝ p fun z => ContinuousLinearMap.inl ℝ V (Fin 4 → V) (Y z) :=
    (ContinuousLinearMap.inl ℝ V (Fin 4 → V)).contDiff.comp hY'
  have h2 : ∀ μ, ContDiff ℝ p fun z => (slotL μ : (R4 →L[ℝ] V) →L[ℝ] JS V) (fderiv ℝ Y z) :=
    fun μ => (ContinuousLinearMap.contDiff (slotL (V := V) μ)).comp hd
  rw [show (fun z => ContinuousLinearMap.inl ℝ V (Fin 4 → V) (Y z) +
      ∑ μ, (slotL μ : (R4 →L[ℝ] V) →L[ℝ] JS V) (fderiv ℝ Y z)) =
      (fun z => ContinuousLinearMap.inl ℝ V (Fin 4 → V) (Y z)) +
        (fun z => ∑ μ, (slotL μ : (R4 →L[ℝ] V) →L[ℝ] JS V) (fderiv ℝ Y z)) from rfl,
    iteratedFDeriv_add_apply h1.contDiffAt (ContDiff.sum fun μ _ => h2 μ).contDiffAt,
    iteratedFDeriv_sum (f := fun μ z => (slotL μ : (R4 →L[ℝ] V) →L[ℝ] JS V) (fderiv ℝ Y z))
      (fun μ _ => h2 μ)]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · have := ContinuousLinearMap.norm_iteratedFDeriv_comp_left
      (ContinuousLinearMap.inl ℝ V (Fin 4 → V)) hY'.contDiffAt (x := z) (n := p) le_rfl
    exact this.trans (mul_le_of_le_one_left (norm_nonneg _) norm_inl_le)
  · rw [Finset.sum_apply]
    refine (norm_sum_le _ _).trans ?_
    have : ∀ μ : Fin 4, ‖iteratedFDeriv ℝ p
        (fun z => (slotL μ : (R4 →L[ℝ] V) →L[ℝ] JS V) (fderiv ℝ Y z)) z‖ ≤
          ‖iteratedFDeriv ℝ (p + 1) Y z‖ := by
      intro μ
      have := ContinuousLinearMap.norm_iteratedFDeriv_comp_left
        (slotL μ : (R4 →L[ℝ] V) →L[ℝ] JS V) hd.contDiffAt (x := z) (n := p) le_rfl
      refine this.trans ?_
      rw [norm_iteratedFDeriv_fderiv]
      exact mul_le_of_le_one_left (norm_nonneg _) (norm_slotL_le μ)
    calc ∑ μ : Fin 4, ‖iteratedFDeriv ℝ p
          (fun z => (slotL μ : (R4 →L[ℝ] V) →L[ℝ] JS V) (fderiv ℝ Y z)) z‖
        ≤ ∑ _μ : Fin 4, ‖iteratedFDeriv ℝ (p + 1) Y z‖ := Finset.sum_le_sum fun μ _ => this μ
      _ = 4 * ‖iteratedFDeriv ℝ (p + 1) Y z‖ := by simp

theorem jet1_sub {Y₁ Y₀ : R4 → V} (h₁ : Differentiable ℝ Y₁) (h₀ : Differentiable ℝ Y₀) (z : R4) :
    jet1 Y₁ z - jet1 Y₀ z = jet1 (Y₁ - Y₀) z := by
  simp only [jet1, Prod.mk_sub_mk, Pi.sub_apply]
  congr 1
  funext μ
  rw [fderiv_sub (h₁ z) (h₀ z)]; rfl

/-! ### Parametrised jets and the Euler operator -/

/-- The parametrised first jet `(θ, J¹Y(z))`. -/
def jetP (θ : Θ) (Y : R4 → V) (z : R4) : Θ × JS V := (θ, jet1 Y z)

theorem jetP_eq (θ : Θ) (Y : R4 → V) :
    jetP θ Y = fun z => ((θ, 0) : Θ × JS V) + ContinuousLinearMap.inr ℝ Θ (JS V) (jet1 Y z) := by
  funext z; simp [jetP]

theorem contDiff_jetP {n : ℕ} (θ : Θ) {Y : R4 → V} (hY : ContDiff ℝ (n + 1) Y) :
    ContDiff ℝ n (jetP θ Y) := by
  rw [jetP_eq]
  exact contDiff_const.add ((ContinuousLinearMap.inr ℝ Θ (JS V)).contDiff.comp (contDiff_jet1 hY))

theorem iteratedFDeriv_jetP {n : ℕ} (hn : n ≠ 0) (θ : Θ) {Y : R4 → V} (hY : ContDiff ℝ (n + 1) Y)
    (z : R4) : iteratedFDeriv ℝ n (jetP θ Y) z =
      (ContinuousLinearMap.inr ℝ Θ (JS V)).compContinuousMultilinearMap
        (iteratedFDeriv ℝ n (jet1 Y) z) := by
  rw [jetP_eq]
  have h1 : ContDiffAt ℝ n (fun _ : R4 => ((θ, 0) : Θ × JS V)) z := contDiffAt_const
  have h2 : ContDiffAt ℝ n (fun z => ContinuousLinearMap.inr ℝ Θ (JS V) (jet1 Y z)) z :=
    ((ContinuousLinearMap.inr ℝ Θ (JS V)).contDiff.comp (contDiff_jet1 hY)).contDiffAt
  rw [show (fun z => ((θ, 0) : Θ × JS V) + ContinuousLinearMap.inr ℝ Θ (JS V) (jet1 Y z)) =
      (fun _ : R4 => ((θ, 0) : Θ × JS V)) +
        (fun z => ContinuousLinearMap.inr ℝ Θ (JS V) (jet1 Y z)) from rfl,
    iteratedFDeriv_add_apply h1 h2, iteratedFDeriv_const_of_ne hn, Pi.zero_apply, zero_add]
  exact (ContinuousLinearMap.inr ℝ Θ (JS V)).iteratedFDeriv_comp_left
    (contDiff_jet1 hY).contDiffAt le_rfl

theorem norm_inr_le : ‖ContinuousLinearMap.inr ℝ Θ (JS V)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => by simp

theorem norm_iteratedFDeriv_jetP_le {n : ℕ} (hn : n ≠ 0) (θ : Θ) {Y : R4 → V}
    (hY : ContDiff ℝ (n + 1) Y) (z : R4) :
    ‖iteratedFDeriv ℝ n (jetP θ Y) z‖ ≤ ‖iteratedFDeriv ℝ n (jet1 Y) z‖ := by
  rw [iteratedFDeriv_jetP hn θ hY]
  exact (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans
    (mul_le_of_le_one_left (norm_nonneg _) norm_inr_le)

theorem norm_iteratedFDeriv_jetP_sub_le {n : ℕ} (θ : Θ) {Y₁ Y₀ : R4 → V}
    (h₁ : ContDiff ℝ (n + 1) Y₁) (h₀ : ContDiff ℝ (n + 1) Y₀) (z : R4) :
    ‖iteratedFDeriv ℝ n (jetP θ Y₁) z - iteratedFDeriv ℝ n (jetP θ Y₀) z‖ ≤
      ‖iteratedFDeriv ℝ n (jet1 (Y₁ - Y₀)) z‖ := by
  have hd₁ : Differentiable ℝ Y₁ := h₁.differentiable (by simp)
  have hd₀ : Differentiable ℝ Y₀ := h₀.differentiable (by simp)
  have hfun : jetP θ Y₁ - jetP θ Y₀ =
      fun z => ContinuousLinearMap.inr ℝ Θ (JS V) (jet1 (Y₁ - Y₀) z) := by
    funext z; simp only [Pi.sub_apply, jetP, ← jet1_sub hd₁ hd₀ z]; simp
  rw [← iteratedFDeriv_sub_apply (contDiff_jetP θ h₁).contDiffAt (contDiff_jetP θ h₀).contDiffAt,
    hfun]
  have hW : ContDiff ℝ (n + 1) (Y₁ - Y₀) := h₁.sub h₀
  have := ContinuousLinearMap.norm_iteratedFDeriv_comp_left (ContinuousLinearMap.inr ℝ Θ (JS V))
    (contDiff_jet1 hW).contDiffAt (x := z) (n := n) le_rfl
  exact this.trans (mul_le_of_le_one_left (norm_nonneg _) norm_inr_le)

/-- **The Euler operator** of a gradient map `G(θ, w, p) ∈ (V × V⁴)^*`:
`E(Y)(z) = G(θ, J¹Y(z)) ∘ ι_w - Σ_μ ∂_μ[G(θ, J¹Y) ∘ ι_{p_μ}](z)`. -/
def eulerOp (G : Θ × JS V → (JS V →L[ℝ] ℝ)) (θ : Θ) (Y : R4 → V) (z : R4) : V →L[ℝ] ℝ :=
  (G (jetP θ Y z)).comp (ContinuousLinearMap.inl ℝ V (Fin 4 → V)) -
    ∑ μ, fderiv ℝ (fun z' => (G (jetP θ Y z')).comp ((ContinuousLinearMap.inr ℝ V (Fin 4 → V)).comp
      (ContinuousLinearMap.single ℝ (fun _ : Fin 4 => V) μ))) z (evec μ)

theorem eulerOp_slot (G : Θ × JS V → (JS V →L[ℝ] ℝ)) (θ : Θ) (Y : R4 → V) (z : R4) :
    eulerOp G θ Y z = (G (jetP θ Y z)).comp (inlJ V) -
      ∑ μ, fderiv ℝ (fun z' => (G (jetP θ Y z')).comp (slotJ V μ)) z (evec μ) := rfl

/-- `contEuler` of the slice `L(θ, ·)` is the Euler operator of its gradient map. -/
theorem contEuler_eq_eulerOp (L : Θ × JS V → ℝ) (G : Θ × JS V → (JS V →L[ℝ] ℝ)) (θ : Θ)
    (Y : R4 → V) (hG : ∀ z, G (θ, jet1 Y z) = fderiv ℝ (fun wp => L (θ, wp)) (jet1 Y z)) :
    contEuler (fun wp => L (θ, wp)) Y = eulerOp G θ Y := by
  funext z
  have hfun : ∀ μ : Fin 4, (fun z' => (fderiv ℝ (fun wp => L (θ, wp)) (jet1 Y z')).comp
      ((ContinuousLinearMap.inr ℝ V (Fin 4 → V)).comp
        (ContinuousLinearMap.single ℝ (fun _ : Fin 4 => V) μ))) =
      fun z' => (G (jetP θ Y z')).comp ((ContinuousLinearMap.inr ℝ V (Fin 4 → V)).comp
        (ContinuousLinearMap.single ℝ (fun _ : Fin 4 => V) μ)) := by
    intro μ; funext z'; rw [jetP, hG]
  unfold contEuler eulerOp
  simp only [hfun]
  rw [jetP, hG]

/-! ### Derivative bounds -/

section Bounds

variable {E F G' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedAddCommGroup G'] [NormedSpace ℝ G']

theorem norm_iteratedFDeriv_clm_comp_sub_le (A : F →L[ℝ] G') {h₁ h₀ : E → F} {n : ℕ} {z : E}
    (hh₁ : ContDiffAt ℝ n h₁ z) (hh₀ : ContDiffAt ℝ n h₀ z) :
    ‖iteratedFDeriv ℝ n (A ∘ h₁) z - iteratedFDeriv ℝ n (A ∘ h₀) z‖ ≤
      ‖A‖ * ‖iteratedFDeriv ℝ n h₁ z - iteratedFDeriv ℝ n h₀ z‖ := by
  rw [A.iteratedFDeriv_comp_left hh₁ le_rfl, A.iteratedFDeriv_comp_left hh₀ le_rfl]
  have : A.compContinuousMultilinearMap (iteratedFDeriv ℝ n h₁ z) -
      A.compContinuousMultilinearMap (iteratedFDeriv ℝ n h₀ z) =
      A.compContinuousMultilinearMap (iteratedFDeriv ℝ n h₁ z - iteratedFDeriv ℝ n h₀ z) := by
    ext v; simp
  rw [this]
  exact ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _

theorem norm_apply_clm_le (v : E) : ‖ContinuousLinearMap.apply ℝ F v‖ ≤ ‖v‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun T => by
    rw [ContinuousLinearMap.apply_apply, mul_comm]; exact T.le_opNorm v

/-- `‖D^n(Df₁)(z) - D^n(Df₀)(z)‖ = ‖D^{n+1}f₁(z) - D^{n+1}f₀(z)‖`. -/
theorem norm_iteratedFDeriv_fderiv_sub {f₁ f₀ : E → F} {n : ℕ}
    (hf₁ : ContDiff ℝ (n + 1) f₁) (hf₀ : ContDiff ℝ (n + 1) f₀) (z : E) :
    ‖iteratedFDeriv ℝ n (fderiv ℝ f₁) z - iteratedFDeriv ℝ n (fderiv ℝ f₀) z‖ =
      ‖iteratedFDeriv ℝ (n + 1) f₁ z - iteratedFDeriv ℝ (n + 1) f₀ z‖ := by
  have hd₁ : ContDiff ℝ n (fderiv ℝ f₁) := hf₁.fderiv_right (by exact_mod_cast le_refl _)
  have hd₀ : ContDiff ℝ n (fderiv ℝ f₀) := hf₀.fderiv_right (by exact_mod_cast le_refl _)
  have hdiff : fderiv ℝ f₁ - fderiv ℝ f₀ = fderiv ℝ (f₁ - f₀) := by
    funext x
    rw [Pi.sub_apply, fderiv_sub (hf₁.differentiable (by simp) x) (hf₀.differentiable (by simp) x)]
  rw [← iteratedFDeriv_sub_apply hd₁.contDiffAt hd₀.contDiffAt, hdiff,
    norm_iteratedFDeriv_fderiv,
    iteratedFDeriv_sub_apply hf₁.contDiffAt hf₀.contDiffAt]

/-- `‖D^n(∂_v f₁)(z) - D^n(∂_v f₀)(z)‖ ≤ ‖D^{n+1}f₁(z) - D^{n+1}f₀(z)‖ ‖v‖`. -/
theorem norm_iteratedFDeriv_fderiv_apply_sub_le {f₁ f₀ : E → F} {n : ℕ}
    (hf₁ : ContDiff ℝ (n + 1) f₁) (hf₀ : ContDiff ℝ (n + 1) f₀) (v z : E) :
    ‖iteratedFDeriv ℝ n (fun z => fderiv ℝ f₁ z v) z -
        iteratedFDeriv ℝ n (fun z => fderiv ℝ f₀ z v) z‖ ≤
      ‖iteratedFDeriv ℝ (n + 1) f₁ z - iteratedFDeriv ℝ (n + 1) f₀ z‖ * ‖v‖ := by
  have hd₁ : ContDiff ℝ n (fderiv ℝ f₁) := hf₁.fderiv_right (by exact_mod_cast le_refl _)
  have hd₀ : ContDiff ℝ n (fderiv ℝ f₀) := hf₀.fderiv_right (by exact_mod_cast le_refl _)
  have e₁ : (fun z => fderiv ℝ f₁ z v) = ⇑(ContinuousLinearMap.apply ℝ F v) ∘ fderiv ℝ f₁ := rfl
  have e₀ : (fun z => fderiv ℝ f₀ z v) = ⇑(ContinuousLinearMap.apply ℝ F v) ∘ fderiv ℝ f₀ := rfl
  rw [e₁, e₀]
  refine (norm_iteratedFDeriv_clm_comp_sub_le _ hd₁.contDiffAt hd₀.contDiffAt).trans ?_
  rw [norm_iteratedFDeriv_fderiv_sub hf₁ hf₀, mul_comm]
  exact mul_le_mul_of_nonneg_left (norm_apply_clm_le v) (norm_nonneg _)

/-- `‖D^n(∂_v f)(z)‖ ≤ ‖D^{n+1}f(z)‖ ‖v‖`. -/
theorem norm_iteratedFDeriv_fderiv_apply_le {f : E → F} {n : ℕ} (hf : ContDiff ℝ (n + 1) f)
    (v z : E) :
    ‖iteratedFDeriv ℝ n (fun z => fderiv ℝ f z v) z‖ ≤ ‖iteratedFDeriv ℝ (n + 1) f z‖ * ‖v‖ := by
  have hd : ContDiff ℝ n (fderiv ℝ f) := hf.fderiv_right (by exact_mod_cast le_refl _)
  have e : (fun z => fderiv ℝ f z v) = ⇑(ContinuousLinearMap.apply ℝ F v) ∘ fderiv ℝ f := rfl
  rw [e]
  refine (ContinuousLinearMap.norm_iteratedFDeriv_comp_left _ hd.contDiffAt le_rfl).trans ?_
  rw [norm_iteratedFDeriv_fderiv, mul_comm]
  exact mul_le_mul_of_nonneg_left (norm_apply_clm_le v) (norm_nonneg _)

end Bounds

/-- The constant `c_n = #OFP(n) + 4 #OFP(n+1)`. -/
def cE (n : ℕ) : ℝ :=
  Fintype.card (OrderedFinpartition n) + 4 * Fintype.card (OrderedFinpartition (n + 1))

theorem cE_nonneg (n : ℕ) : 0 ≤ cE n := by unfold cE; positivity

section Main

variable {G : Θ × JS V → (JS V →L[ℝ] ℝ)} {U C : Set (Θ × JS V)} {θ : Θ}

/-- Precomposition with the value slot. -/
def Aop : (JS V →L[ℝ] ℝ) →L[ℝ] (V →L[ℝ] ℝ) := preL (ContinuousLinearMap.inl ℝ V (Fin 4 → V))

/-- Precomposition with the slot `p_μ`. -/
def Bop (μ : Fin 4) : (JS V →L[ℝ] ℝ) →L[ℝ] (V →L[ℝ] ℝ) :=
  preL ((ContinuousLinearMap.inr ℝ V (Fin 4 → V)).comp
    (ContinuousLinearMap.single ℝ (fun _ : Fin 4 => V) μ))

theorem norm_Aop_le : ‖(Aop : (JS V →L[ℝ] ℝ) →L[ℝ] (V →L[ℝ] ℝ))‖ ≤ 1 :=
  norm_preL_le _ norm_inl_le

theorem norm_Bop_le (μ : Fin 4) : ‖(Bop μ : (JS V →L[ℝ] ℝ) →L[ℝ] (V →L[ℝ] ℝ))‖ ≤ 1 :=
  norm_preL_le _ (norm_inr_single_le μ)

theorem eulerOp_eq' (Y : R4 → V) : eulerOp G θ Y =
    (⇑(Aop (V := V)) ∘ (G ∘ jetP θ Y)) - (fun z => ∑ μ,
      (⇑(ContinuousLinearMap.apply ℝ (V →L[ℝ] ℝ) (evec μ)) ∘
        fderiv ℝ (⇑(Bop (V := V) μ) ∘ (G ∘ jetP θ Y))) z) := rfl

/-- The `n`-th derivative of the Euler operator. -/
theorem iteratedFDeriv_eulerOp {n : ℕ} {Y : R4 → V} (hh : ContDiff ℝ (n + 1) (G ∘ jetP θ Y))
    (z : R4) : iteratedFDeriv ℝ n (eulerOp G θ Y) z =
      (Aop (V := V)).compContinuousMultilinearMap (iteratedFDeriv ℝ n (G ∘ jetP θ Y) z) -
        ∑ μ, (ContinuousLinearMap.apply ℝ (V →L[ℝ] ℝ) (evec μ)).compContinuousMultilinearMap
          (iteratedFDeriv ℝ n (fderiv ℝ (⇑(Bop (V := V) μ) ∘ (G ∘ jetP θ Y))) z) := by
  have hhn : ContDiff ℝ n (G ∘ jetP θ Y) := hh.of_le (by exact_mod_cast Nat.le_succ n)
  have hB : ∀ μ, ContDiff ℝ n (fderiv ℝ (⇑(Bop (V := V) μ) ∘ (G ∘ jetP θ Y))) := fun μ =>
    ((Bop μ).contDiff.comp hh).fderiv_right (by exact_mod_cast le_refl _)
  have hS : ∀ μ, ContDiff ℝ n (⇑(ContinuousLinearMap.apply ℝ (V →L[ℝ] ℝ) (evec μ)) ∘
      fderiv ℝ (⇑(Bop (V := V) μ) ∘ (G ∘ jetP θ Y))) := fun μ =>
    (ContinuousLinearMap.apply ℝ (V →L[ℝ] ℝ) (evec μ)).contDiff.comp (hB μ)
  rw [eulerOp_eq', iteratedFDeriv_sub_apply ((Aop.contDiff.comp hhn).contDiffAt)
    ((ContDiff.sum fun μ _ => hS μ).contDiffAt),
    iteratedFDeriv_sum (fun μ _ => hS μ), Finset.sum_apply,
    (Aop (V := V)).iteratedFDeriv_comp_left hhn.contDiffAt le_rfl]
  congr 1
  refine Finset.sum_congr rfl fun μ _ => ?_
  exact (ContinuousLinearMap.apply ℝ (V →L[ℝ] ℝ) (evec μ)).iteratedFDeriv_comp_left
    (hB μ).contDiffAt le_rfl

theorem norm_compCMM_sub_le {F₁ F₂ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
    [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] {n : ℕ} (A : F₁ →L[ℝ] F₂)
    (a b : R4 [×n]→L[ℝ] F₁) :
    ‖A.compContinuousMultilinearMap a - A.compContinuousMultilinearMap b‖ ≤ ‖A‖ * ‖a - b‖ := by
  have : A.compContinuousMultilinearMap a - A.compContinuousMultilinearMap b =
      A.compContinuousMultilinearMap (a - b) := by ext v; simp
  rw [this]; exact ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _

theorem norm_apply_evec_le (μ : Fin 4) :
    ‖ContinuousLinearMap.apply ℝ (V →L[ℝ] ℝ) (evec μ)‖ ≤ 1 :=
  (norm_apply_clm_le (evec μ)).trans (le_of_eq (norm_evec μ))

-- the Faà di Bruno bookkeeping elaborates large multilinear-map terms
set_option maxHeartbeats 1000000 in
/-- **Difference bound for the Euler operator** (tail transfer). -/
theorem norm_iteratedFDeriv_eulerOp_sub_le {n : ℕ} (hU : IsOpen U)
    (hG : ContDiffOn ℝ (n + 1 + 1) G U) (hCU : C ⊆ U) (hC : Convex ℝ C) {M : ℝ}
    (hM : ∀ y ∈ C, ∀ k ≤ n + 1 + 1, ‖iteratedFDeriv ℝ k G y‖ ≤ M)
    {Y₀ Y₁ : R4 → V} (hY₀ : ContDiff ℝ (n + 1 + 1) Y₀) (hY₁ : ContDiff ℝ (n + 1 + 1) Y₁)
    (hU₀ : ∀ z, jetP θ Y₀ z ∈ U) (hU₁ : ∀ z, jetP θ Y₁ z ∈ U) {z : R4}
    (hz₀ : jetP θ Y₀ z ∈ C) (hz₁ : jetP θ Y₁ z ∈ C) {B η : ℝ} (hB1 : 1 ≤ B)
    (hB : ∀ p, 1 ≤ p → p ≤ n + 1 →
      ‖iteratedFDeriv ℝ p (jet1 Y₀) z‖ ≤ B ∧ ‖iteratedFDeriv ℝ p (jet1 Y₁) z‖ ≤ B)
    (hη : ∀ p ≤ n + 1, ‖iteratedFDeriv ℝ p (jet1 (Y₁ - Y₀)) z‖ ≤ η) :
    ‖iteratedFDeriv ℝ n (eulerOp G θ Y₁) z - iteratedFDeriv ℝ n (eulerOp G θ Y₀) z‖ ≤
      cE n * ((n + 2) * M * B ^ (n + 1)) * η := by
  have hB0 : 0 ≤ B := by linarith
  have hη0 : 0 ≤ η := (norm_nonneg _).trans (hη 0 (Nat.zero_le _))
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM _ hz₀ 0 (Nat.zero_le _))
  have hJ₀ : ContDiff ℝ (n + 1) (jetP θ Y₀) := contDiff_jetP θ hY₀
  have hJ₁ : ContDiff ℝ (n + 1) (jetP θ Y₁) := contDiff_jetP θ hY₁
  have hG1 : ContDiffOn ℝ (n + 1) G U := hG.of_le (by exact_mod_cast Nat.le_succ (n + 1))
  have hh₀ : ContDiff ℝ (n + 1) (G ∘ jetP θ Y₀) := hG1.comp_contDiff hJ₀ hU₀
  have hh₁ : ContDiff ℝ (n + 1) (G ∘ jetP θ Y₁) := hG1.comp_contDiff hJ₁ hU₁
  have hd₁ : Differentiable ℝ Y₁ := hY₁.differentiable (by simp)
  have hd₀ : Differentiable ℝ Y₀ := hY₀.differentiable (by simp)
  have hFdB : ∀ N ≤ n + 1, ‖iteratedFDeriv ℝ N (G ∘ jetP θ Y₁) z -
      iteratedFDeriv ℝ N (G ∘ jetP θ Y₀) z‖ ≤
        Fintype.card (OrderedFinpartition N) * ((N + 1) * M * B ^ N) * η := by
    intro N hN
    have hYN₀ : ContDiff ℝ (N + 1) Y₀ :=
      hY₀.of_le (by exact_mod_cast (show N + 1 ≤ n + 1 + 1 by omega))
    have hYN₁ : ContDiff ℝ (N + 1) Y₁ :=
      hY₁.of_le (by exact_mod_cast (show N + 1 ≤ n + 1 + 1 by omega))
    refine CompDiff.norm_iteratedFDeriv_comp_sub_le hU
      (hG.of_le (by exact_mod_cast (show N + 1 ≤ n + 1 + 1 by omega))) hCU hC
      (fun y hy k hk => hM y hy k (by omega))
      (contDiff_jetP θ hYN₀).contDiffAt (contDiff_jetP θ hYN₁).contDiffAt
      hz₀ hz₁ hB1 (fun p hp hpN => ⟨?_, ?_⟩) ?_ (fun p hp hpN => ?_)
    · exact (norm_iteratedFDeriv_jetP_le (by omega) θ
        (hY₀.of_le (by exact_mod_cast (show p + 1 ≤ n + 1 + 1 by omega))) z).trans
        (hB p hp (by omega)).1
    · exact (norm_iteratedFDeriv_jetP_le (by omega) θ
        (hY₁.of_le (by exact_mod_cast (show p + 1 ≤ n + 1 + 1 by omega))) z).trans
        (hB p hp (by omega)).2
    · have e : jetP θ Y₁ z - jetP θ Y₀ z = ((0 : Θ), jet1 (Y₁ - Y₀) z) := by
        simp only [jetP, Prod.mk_sub_mk, sub_self, jet1_sub hd₁ hd₀ z]
      rw [e, Prod.norm_mk, norm_zero, max_eq_right (norm_nonneg _)]
      have := hη 0 (Nat.zero_le _)
      rwa [norm_iteratedFDeriv_zero] at this
    · exact (norm_iteratedFDeriv_jetP_sub_le (n := p) θ
        (hY₁.of_le (by exact_mod_cast (show p + 1 ≤ n + 1 + 1 by omega)))
        (hY₀.of_le (by exact_mod_cast (show p + 1 ≤ n + 1 + 1 by omega))) z).trans
          (hη p (by omega))
  rw [iteratedFDeriv_eulerOp hh₁, iteratedFDeriv_eulerOp hh₀]
  set a₁ := iteratedFDeriv ℝ n (G ∘ jetP θ Y₁) z
  set a₀ := iteratedFDeriv ℝ n (G ∘ jetP θ Y₀) z
  set s₁ : Fin 4 → (R4 [×n]→L[ℝ] (V →L[ℝ] ℝ)) := fun μ =>
    (ContinuousLinearMap.apply ℝ (V →L[ℝ] ℝ) (evec μ)).compContinuousMultilinearMap
      (iteratedFDeriv ℝ n (fderiv ℝ (⇑(Bop (V := V) μ) ∘ (G ∘ jetP θ Y₁))) z)
  set s₀ : Fin 4 → (R4 [×n]→L[ℝ] (V →L[ℝ] ℝ)) := fun μ =>
    (ContinuousLinearMap.apply ℝ (V →L[ℝ] ℝ) (evec μ)).compContinuousMultilinearMap
      (iteratedFDeriv ℝ n (fderiv ℝ (⇑(Bop (V := V) μ) ∘ (G ∘ jetP θ Y₀))) z)
  have e : ((Aop (V := V)).compContinuousMultilinearMap a₁ - ∑ μ, s₁ μ) -
      ((Aop (V := V)).compContinuousMultilinearMap a₀ - ∑ μ, s₀ μ) =
      ((Aop (V := V)).compContinuousMultilinearMap a₁ -
        (Aop (V := V)).compContinuousMultilinearMap a₀) - ∑ μ, (s₁ μ - s₀ μ) := by
    have h := Finset.sum_sub_distrib (s := (Finset.univ : Finset (Fin 4))) (f := s₁) (g := s₀)
    rw [h]; abel
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  have hT1 : ‖(Aop (V := V)).compContinuousMultilinearMap a₁ -
      (Aop (V := V)).compContinuousMultilinearMap a₀‖ ≤
        Fintype.card (OrderedFinpartition n) * ((n + 1) * M * B ^ n) * η :=
    (norm_compCMM_sub_le _ _ _).trans ((mul_le_of_le_one_left (norm_nonneg _) norm_Aop_le).trans
      (hFdB n (Nat.le_succ n)))
  have hT2 : ∀ μ, ‖s₁ μ - s₀ μ‖ ≤
      Fintype.card (OrderedFinpartition (n + 1)) *
        ((((n + 1 : ℕ) : ℝ) + 1) * M * B ^ (n + 1)) * η := by
    intro μ
    have hap : ‖ContinuousLinearMap.apply ℝ (V →L[ℝ] ℝ) (evec μ)‖ ≤ 1 := norm_apply_evec_le μ
    have hc1 : ContDiff ℝ (n + 1) (⇑(Bop (V := V) μ) ∘ (G ∘ jetP θ Y₁)) := (Bop μ).contDiff.comp hh₁
    have hc0 : ContDiff ℝ (n + 1) (⇑(Bop (V := V) μ) ∘ (G ∘ jetP θ Y₀)) := (Bop μ).contDiff.comp hh₀
    have step1 : ‖s₁ μ - s₀ μ‖ ≤
        ‖iteratedFDeriv ℝ n (fderiv ℝ (⇑(Bop (V := V) μ) ∘ (G ∘ jetP θ Y₁))) z -
          iteratedFDeriv ℝ n (fderiv ℝ (⇑(Bop (V := V) μ) ∘ (G ∘ jetP θ Y₀))) z‖ := by
      have h := norm_compCMM_sub_le (ContinuousLinearMap.apply ℝ (V →L[ℝ] ℝ) (evec μ))
        (iteratedFDeriv ℝ n (fderiv ℝ (⇑(Bop (V := V) μ) ∘ (G ∘ jetP θ Y₁))) z)
        (iteratedFDeriv ℝ n (fderiv ℝ (⇑(Bop (V := V) μ) ∘ (G ∘ jetP θ Y₀))) z)
      exact h.trans (mul_le_of_le_one_left (norm_nonneg _) hap)
    have step2 := norm_iteratedFDeriv_fderiv_sub hc1 hc0 z
    have step3 := norm_iteratedFDeriv_clm_comp_sub_le (Bop (V := V) μ) hh₁.contDiffAt
      hh₀.contDiffAt (z := z) (n := n + 1)
    have step4 : ‖Bop (V := V) μ‖ * ‖iteratedFDeriv ℝ (n + 1) (G ∘ jetP θ Y₁) z -
        iteratedFDeriv ℝ (n + 1) (G ∘ jetP θ Y₀) z‖ ≤
          ‖iteratedFDeriv ℝ (n + 1) (G ∘ jetP θ Y₁) z -
            iteratedFDeriv ℝ (n + 1) (G ∘ jetP θ Y₀) z‖ :=
      mul_le_of_le_one_left (norm_nonneg _) (norm_Bop_le μ)
    have step5 := hFdB (n + 1) le_rfl
    rw [step2] at step1
    exact step1.trans (step3.trans (step4.trans step5))
  have hBn : B ^ n ≤ B ^ (n + 1) := pow_le_pow_right₀ hB1 (Nat.le_succ n)
  have hcard0 : (0 : ℝ) ≤ Fintype.card (OrderedFinpartition n) := by positivity
  have hcard1 : (0 : ℝ) ≤ Fintype.card (OrderedFinpartition (n + 1)) := by positivity
  have hsum : ‖∑ μ, (s₁ μ - s₀ μ)‖ ≤ 4 * (Fintype.card (OrderedFinpartition (n + 1)) *
      ((((n + 1 : ℕ) : ℝ) + 1) * M * B ^ (n + 1)) * η) := by
    have hn : ‖∑ μ, (s₁ μ - s₀ μ)‖ ≤ ∑ μ, ‖s₁ μ - s₀ μ‖ :=
      norm_sum_le (E := R4 [×n]→L[ℝ] (V →L[ℝ] ℝ)) _ _
    refine hn.trans ((Finset.sum_le_sum fun μ _ => hT2 μ).trans (le_of_eq ?_))
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; norm_num
  have hX : ((n : ℝ) + 1) * M * B ^ n ≤ (n + 2) * M * B ^ (n + 1) := by
    have h1 : M * B ^ n ≤ M * B ^ (n + 1) := mul_le_mul_of_nonneg_left hBn hM0
    have h2 : ((n : ℝ) + 1) * (M * B ^ n) ≤ (n + 2) * (M * B ^ (n + 1)) :=
      mul_le_mul (by linarith) h1 (by positivity) (by positivity)
    calc ((n : ℝ) + 1) * M * B ^ n = ((n : ℝ) + 1) * (M * B ^ n) := by ring
      _ ≤ (n + 2) * (M * B ^ (n + 1)) := h2
      _ = (n + 2) * M * B ^ (n + 1) := by ring
  have hpush : (((n + 1 : ℕ) : ℝ) + 1) = n + 2 := by push_cast; ring
  rw [hpush] at hsum
  have hfin := add_le_add hT1 hsum
  refine hfin.trans ?_
  unfold cE
  have hY : 0 ≤ (n + 2 : ℝ) * M * B ^ (n + 1) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hX (mul_nonneg hcard0 hη0)]

-- the Faà di Bruno bookkeeping elaborates large multilinear-map terms
set_option maxHeartbeats 1000000 in
/-- **Bound for the Euler operator**: `‖D^n E(Y)(z)‖ ≤ c_n M B^{n+1}`. -/
theorem norm_iteratedFDeriv_eulerOp_le {n : ℕ} (hU : IsOpen U)
    (hG : ContDiffOn ℝ (n + 1 + 1) G U) {M : ℝ} {Y : R4 → V} (hY : ContDiff ℝ (n + 1 + 1) Y)
    (hUY : ∀ z, jetP θ Y z ∈ U) {z : R4}
    (hM : ∀ k ≤ n + 1, ‖iteratedFDeriv ℝ k G (jetP θ Y z)‖ ≤ M) {B : ℝ} (hB1 : 1 ≤ B)
    (hB : ∀ p, 1 ≤ p → p ≤ n + 1 → ‖iteratedFDeriv ℝ p (jet1 Y) z‖ ≤ B) :
    ‖iteratedFDeriv ℝ n (eulerOp G θ Y) z‖ ≤ cE n * M * B ^ (n + 1) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (Nat.zero_le _))
  have hJ : ContDiff ℝ (n + 1) (jetP θ Y) := contDiff_jetP θ hY
  have hG1 : ContDiffOn ℝ (n + 1) G U := hG.of_le (by exact_mod_cast Nat.le_succ (n + 1))
  have hh : ContDiff ℝ (n + 1) (G ∘ jetP θ Y) := hG1.comp_contDiff hJ hUY
  have hGat : ContDiffAt ℝ (n + 1) G (jetP θ Y z) := hG1.contDiffAt (hU.mem_nhds (hUY z))
  have hFdB : ∀ N ≤ n + 1, ‖iteratedFDeriv ℝ N (G ∘ jetP θ Y) z‖ ≤
      Fintype.card (OrderedFinpartition N) * M * B ^ N := by
    intro N hN
    have hYN : ContDiff ℝ (N + 1) Y :=
      hY.of_le (by exact_mod_cast (show N + 1 ≤ n + 1 + 1 by omega))
    exact CompDiff.norm_iteratedFDeriv_comp_le_local (hGat.of_le (by exact_mod_cast hN))
      (contDiff_jetP θ hYN).contDiffAt hB1 (fun k hk => hM k (hk.trans hN))
      (fun p hp hpN => (norm_iteratedFDeriv_jetP_le (by omega) θ
        (hY.of_le (by exact_mod_cast (show p + 1 ≤ n + 1 + 1 by omega))) z).trans
          (hB p hp (by omega)))
  rw [iteratedFDeriv_eulerOp hh]
  refine (norm_sub_le _ _).trans ?_
  have hT1 : ‖(Aop (V := V)).compContinuousMultilinearMap
      (iteratedFDeriv ℝ n (G ∘ jetP θ Y) z)‖ ≤
        Fintype.card (OrderedFinpartition n) * M * B ^ n :=
    (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans
      ((mul_le_of_le_one_left (norm_nonneg _) norm_Aop_le).trans (hFdB n (Nat.le_succ n)))
  have hT2 : ∀ μ, ‖(ContinuousLinearMap.apply ℝ (V →L[ℝ] ℝ)
      (evec μ)).compContinuousMultilinearMap
      (iteratedFDeriv ℝ n (fderiv ℝ (⇑(Bop (V := V) μ) ∘ (G ∘ jetP θ Y))) z)‖ ≤
        Fintype.card (OrderedFinpartition (n + 1)) * M * B ^ (n + 1) := by
    intro μ
    have hap : ‖ContinuousLinearMap.apply ℝ (V →L[ℝ] ℝ) (evec μ)‖ ≤ 1 := norm_apply_evec_le μ
    have step1 := ContinuousLinearMap.norm_compContinuousMultilinearMap_le
      (ContinuousLinearMap.apply ℝ (V →L[ℝ] ℝ) (evec μ))
      (iteratedFDeriv ℝ n (fderiv ℝ (⇑(Bop (V := V) μ) ∘ (G ∘ jetP θ Y))) z)
    have step2 : ‖ContinuousLinearMap.apply ℝ (V →L[ℝ] ℝ) (evec μ)‖ *
        ‖iteratedFDeriv ℝ n (fderiv ℝ (⇑(Bop (V := V) μ) ∘ (G ∘ jetP θ Y))) z‖ ≤
          ‖iteratedFDeriv ℝ n (fderiv ℝ (⇑(Bop (V := V) μ) ∘ (G ∘ jetP θ Y))) z‖ :=
      mul_le_of_le_one_left (norm_nonneg _) hap
    rw [norm_iteratedFDeriv_fderiv] at step1 step2
    have step3 := ContinuousLinearMap.norm_iteratedFDeriv_comp_left (Bop (V := V) μ)
      hh.contDiffAt (x := z) (n := n + 1) le_rfl
    have step4 : ‖Bop (V := V) μ‖ * ‖iteratedFDeriv ℝ (n + 1) (G ∘ jetP θ Y) z‖ ≤
        ‖iteratedFDeriv ℝ (n + 1) (G ∘ jetP θ Y) z‖ :=
      mul_le_of_le_one_left (norm_nonneg _) (norm_Bop_le μ)
    exact step1.trans (step2.trans (step3.trans (step4.trans (hFdB (n + 1) le_rfl))))
  have hBn : B ^ n ≤ B ^ (n + 1) := pow_le_pow_right₀ hB1 (Nat.le_succ n)
  have hsum := (norm_sum_le _ _).trans
    (Finset.sum_le_sum fun μ (_ : μ ∈ Finset.univ) => hT2 μ)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  refine (add_le_add hT1 hsum).trans ?_
  unfold cE
  have hcard0 : (0 : ℝ) ≤ Fintype.card (OrderedFinpartition n) := by positivity
  have := mul_le_mul_of_nonneg_left hBn (mul_nonneg hcard0 hM0)
  push_cast
  nlinarith

end Main


/-! ### First-order operators -/

section FirstOrder

variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]

/-- The parametrised value `(θ, Y(z))`. -/
def jetQ (θ : Θ) (Y : R4 → V) (z : R4) : Θ × V := (θ, Y z)

theorem jetQ_eq (θ : Θ) (Y : R4 → V) :
    jetQ θ Y = fun z => ((θ, 0) : Θ × V) + inrP Θ V (Y z) := by
  funext z; simp [jetQ, inrP_apply]

theorem contDiff_jetQ {n : ℕ} (θ : Θ) {Y : R4 → V} (hY : ContDiff ℝ n Y) :
    ContDiff ℝ n (jetQ θ Y) := by
  rw [jetQ_eq]
  exact contDiff_const.add ((inrP Θ V).contDiff.comp hY)

theorem norm_inrP_le : ‖inrP Θ V‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => by simp [inrP_apply]

theorem norm_iteratedFDeriv_jetQ_le {n : ℕ} (hn : n ≠ 0) (θ : Θ) {Y : R4 → V}
    (hY : ContDiff ℝ n Y) (z : R4) :
    ‖iteratedFDeriv ℝ n (jetQ θ Y) z‖ ≤ ‖iteratedFDeriv ℝ n Y z‖ := by
  rw [jetQ_eq]
  have h1 : ContDiffAt ℝ n (fun _ : R4 => ((θ, 0) : Θ × V)) z := contDiffAt_const
  have h2 : ContDiffAt ℝ n (fun z => inrP Θ V (Y z)) z :=
    ((inrP Θ V).contDiff.comp hY).contDiffAt
  rw [show (fun z => ((θ, 0) : Θ × V) + inrP Θ V (Y z)) =
      (fun _ : R4 => ((θ, 0) : Θ × V)) + (fun z => inrP Θ V (Y z)) from rfl,
    iteratedFDeriv_add_apply h1 h2, iteratedFDeriv_const_of_ne hn, Pi.zero_apply, zero_add]
  have := ContinuousLinearMap.norm_iteratedFDeriv_comp_left (inrP Θ V) hY.contDiffAt
    (x := z) (n := n) le_rfl
  exact this.trans (mul_le_of_le_one_left (norm_nonneg _) norm_inrP_le)

theorem norm_iteratedFDeriv_jetQ_sub_le {n : ℕ} (θ : Θ) {Y₁ Y₀ : R4 → V}
    (h₁ : ContDiff ℝ n Y₁) (h₀ : ContDiff ℝ n Y₀) (z : R4) :
    ‖iteratedFDeriv ℝ n (jetQ θ Y₁) z - iteratedFDeriv ℝ n (jetQ θ Y₀) z‖ ≤
      ‖iteratedFDeriv ℝ n (Y₁ - Y₀) z‖ := by
  have hfun : jetQ θ Y₁ - jetQ θ Y₀ = fun z => inrP Θ V ((Y₁ - Y₀) z) := by
    funext z; simp [jetQ, inrP_apply]
  rw [← iteratedFDeriv_sub_apply (contDiff_jetQ θ h₁).contDiffAt (contDiff_jetQ θ h₀).contDiffAt,
    hfun]
  have := ContinuousLinearMap.norm_iteratedFDeriv_comp_left (inrP Θ V) (h₁.sub h₀).contDiffAt
    (x := z) (n := n) le_rfl
  exact this.trans (mul_le_of_le_one_left (norm_nonneg _) norm_inrP_le)

/-- **A first-order Euler-type operator**: `Ψ(Y)(z) = G₁(θ, J¹Y(z)) - Σ_μ ∂_μ[ℓ_μ(θ, Y)](z)`. -/
def foOp (G₁ : Θ × JS V → (S →L[ℝ] ℝ)) (ℓ : Fin 4 → Θ × V → (S →L[ℝ] ℝ)) (θ : Θ) (Y : R4 → V)
    (z : R4) : S →L[ℝ] ℝ :=
  G₁ (jetP θ Y z) - ∑ μ, fderiv ℝ (fun z' => ℓ μ (jetQ θ Y z')) z (evec μ)

variable {G₁ : Θ × JS V → (S →L[ℝ] ℝ)} {ℓ : Fin 4 → Θ × V → (S →L[ℝ] ℝ)}
  {U₁ C₁ : Set (Θ × JS V)} {U₀ C₀ : Set (Θ × V)} {θ : Θ}

theorem foOp_eq (Y : R4 → V) : foOp G₁ ℓ θ Y = (G₁ ∘ jetP θ Y) - (fun z => ∑ μ,
    (⇑(ContinuousLinearMap.apply ℝ (S →L[ℝ] ℝ) (evec μ)) ∘ fderiv ℝ (ℓ μ ∘ jetQ θ Y)) z) := rfl

theorem iteratedFDeriv_foOp {n : ℕ} {Y : R4 → V} (h1 : ContDiff ℝ n (G₁ ∘ jetP θ Y))
    (h0 : ∀ μ, ContDiff ℝ (n + 1) (ℓ μ ∘ jetQ θ Y)) (z : R4) :
    iteratedFDeriv ℝ n (foOp G₁ ℓ θ Y) z = iteratedFDeriv ℝ n (G₁ ∘ jetP θ Y) z -
      ∑ μ, (ContinuousLinearMap.apply ℝ (S →L[ℝ] ℝ) (evec μ)).compContinuousMultilinearMap
        (iteratedFDeriv ℝ n (fderiv ℝ (ℓ μ ∘ jetQ θ Y)) z) := by
  have hB : ∀ μ, ContDiff ℝ n (fderiv ℝ (ℓ μ ∘ jetQ θ Y)) := fun μ =>
    (h0 μ).fderiv_right (by exact_mod_cast le_refl _)
  have hS : ∀ μ, ContDiff ℝ n (⇑(ContinuousLinearMap.apply ℝ (S →L[ℝ] ℝ) (evec μ)) ∘
      fderiv ℝ (ℓ μ ∘ jetQ θ Y)) := fun μ =>
    (ContinuousLinearMap.apply ℝ (S →L[ℝ] ℝ) (evec μ)).contDiff.comp (hB μ)
  rw [foOp_eq, iteratedFDeriv_sub_apply h1.contDiffAt ((ContDiff.sum fun μ _ => hS μ).contDiffAt),
    iteratedFDeriv_sum (fun μ _ => hS μ), Finset.sum_apply]
  congr 1
  refine Finset.sum_congr rfl fun μ _ => ?_
  exact (ContinuousLinearMap.apply ℝ (S →L[ℝ] ℝ) (evec μ)).iteratedFDeriv_comp_left
    (hB μ).contDiffAt le_rfl

-- the Faà di Bruno bookkeeping elaborates large multilinear-map terms
set_option maxHeartbeats 1000000 in
/-- **Difference bound for a first-order operator** (tail transfer for the Dirac rows): only
derivatives of `W = Y₁ - Y₀` up to order `n + 1` enter. -/
theorem norm_iteratedFDeriv_foOp_sub_le {n : ℕ} (hU₁ : IsOpen U₁) (hG₁ : ContDiffOn ℝ (n + 1) G₁ U₁)
    (hCU₁ : C₁ ⊆ U₁) (hC₁ : Convex ℝ C₁) (hU₀ : IsOpen U₀)
    (hℓ : ∀ μ, ContDiffOn ℝ (n + 1 + 1) (ℓ μ) U₀) (hCU₀ : C₀ ⊆ U₀) (hC₀ : Convex ℝ C₀) {M : ℝ}
    (hM₁ : ∀ y ∈ C₁, ∀ k ≤ n + 1, ‖iteratedFDeriv ℝ k G₁ y‖ ≤ M)
    (hM₀ : ∀ μ, ∀ y ∈ C₀, ∀ k ≤ n + 1 + 1, ‖iteratedFDeriv ℝ k (ℓ μ) y‖ ≤ M)
    {Y₀ Y₁ : R4 → V} (hY₀ : ContDiff ℝ (n + 1) Y₀) (hY₁ : ContDiff ℝ (n + 1) Y₁)
    (hUY₀ : ∀ z, jetP θ Y₀ z ∈ U₁) (hUY₁ : ∀ z, jetP θ Y₁ z ∈ U₁)
    (hVY₀ : ∀ z, jetQ θ Y₀ z ∈ U₀) (hVY₁ : ∀ z, jetQ θ Y₁ z ∈ U₀) {z : R4}
    (hz₀ : jetP θ Y₀ z ∈ C₁) (hz₁ : jetP θ Y₁ z ∈ C₁) (hw₀ : jetQ θ Y₀ z ∈ C₀)
    (hw₁ : jetQ θ Y₁ z ∈ C₀) {B η : ℝ} (hB1 : 1 ≤ B)
    (hBJ : ∀ p, 1 ≤ p → p ≤ n →
      ‖iteratedFDeriv ℝ p (jet1 Y₀) z‖ ≤ B ∧ ‖iteratedFDeriv ℝ p (jet1 Y₁) z‖ ≤ B)
    (hBY : ∀ p, 1 ≤ p → p ≤ n + 1 →
      ‖iteratedFDeriv ℝ p Y₀ z‖ ≤ B ∧ ‖iteratedFDeriv ℝ p Y₁ z‖ ≤ B)
    (hηJ : ∀ p ≤ n, ‖iteratedFDeriv ℝ p (jet1 (Y₁ - Y₀)) z‖ ≤ η)
    (hηY : ∀ p ≤ n + 1, ‖iteratedFDeriv ℝ p (Y₁ - Y₀) z‖ ≤ η) :
    ‖iteratedFDeriv ℝ n (foOp G₁ ℓ θ Y₁) z - iteratedFDeriv ℝ n (foOp G₁ ℓ θ Y₀) z‖ ≤
      cE n * ((n + 2) * M * B ^ (n + 1)) * η := by
  have hB0 : 0 ≤ B := by linarith
  have hη0 : 0 ≤ η := (norm_nonneg _).trans (hηY 0 (Nat.zero_le _))
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM₁ _ hz₀ 0 (Nat.zero_le _))
  have hd₁ : Differentiable ℝ Y₁ := hY₁.differentiable (by simp)
  have hd₀ : Differentiable ℝ Y₀ := hY₀.differentiable (by simp)
  have hJ₀ : ContDiff ℝ n (jetP θ Y₀) := contDiff_jetP θ hY₀
  have hJ₁ : ContDiff ℝ n (jetP θ Y₁) := contDiff_jetP θ hY₁
  have hh₀ : ContDiff ℝ n (G₁ ∘ jetP θ Y₀) :=
    (hG₁.of_le (by exact_mod_cast Nat.le_succ n)).comp_contDiff hJ₀ hUY₀
  have hh₁ : ContDiff ℝ n (G₁ ∘ jetP θ Y₁) :=
    (hG₁.of_le (by exact_mod_cast Nat.le_succ n)).comp_contDiff hJ₁ hUY₁
  have hk₀ : ∀ μ, ContDiff ℝ (n + 1) (ℓ μ ∘ jetQ θ Y₀) := fun μ =>
    ((hℓ μ).of_le (by exact_mod_cast Nat.le_succ (n + 1))).comp_contDiff (contDiff_jetQ θ hY₀) hVY₀
  have hk₁ : ∀ μ, ContDiff ℝ (n + 1) (ℓ μ ∘ jetQ θ Y₁) := fun μ =>
    ((hℓ μ).of_le (by exact_mod_cast Nat.le_succ (n + 1))).comp_contDiff (contDiff_jetQ θ hY₁) hVY₁
  -- first term: Faà di Bruno with the first jets, order `n`
  have hT1 : ‖iteratedFDeriv ℝ n (G₁ ∘ jetP θ Y₁) z - iteratedFDeriv ℝ n (G₁ ∘ jetP θ Y₀) z‖ ≤
      Fintype.card (OrderedFinpartition n) * ((n + 1) * M * B ^ n) * η := by
    refine CompDiff.norm_iteratedFDeriv_comp_sub_le hU₁ hG₁ hCU₁ hC₁ hM₁
      hJ₀.contDiffAt hJ₁.contDiffAt hz₀ hz₁ hB1 (fun p hp hpN => ⟨?_, ?_⟩) ?_ (fun p hp hpN => ?_)
    · exact (norm_iteratedFDeriv_jetP_le (by omega) θ
        (hY₀.of_le (by exact_mod_cast (show p + 1 ≤ n + 1 by omega))) z).trans (hBJ p hp hpN).1
    · exact (norm_iteratedFDeriv_jetP_le (by omega) θ
        (hY₁.of_le (by exact_mod_cast (show p + 1 ≤ n + 1 by omega))) z).trans (hBJ p hp hpN).2
    · have e : jetP θ Y₁ z - jetP θ Y₀ z = ((0 : Θ), jet1 (Y₁ - Y₀) z) := by
        simp only [jetP, Prod.mk_sub_mk, sub_self, jet1_sub hd₁ hd₀ z]
      rw [e, Prod.norm_mk, norm_zero, max_eq_right (norm_nonneg _)]
      have := hηJ 0 (Nat.zero_le _)
      rwa [norm_iteratedFDeriv_zero] at this
    · exact (norm_iteratedFDeriv_jetP_sub_le (n := p) θ
        (hY₁.of_le (by exact_mod_cast (show p + 1 ≤ n + 1 by omega)))
        (hY₀.of_le (by exact_mod_cast (show p + 1 ≤ n + 1 by omega))) z).trans (hηJ p hpN)
  -- second term: Faà di Bruno with the values, order `n + 1`
  have hT2 : ∀ μ, ‖iteratedFDeriv ℝ (n + 1) (ℓ μ ∘ jetQ θ Y₁) z -
      iteratedFDeriv ℝ (n + 1) (ℓ μ ∘ jetQ θ Y₀) z‖ ≤
        Fintype.card (OrderedFinpartition (n + 1)) * (((n + 1 : ℕ) + 1 : ℝ) * M * B ^ (n + 1)) *
          η := by
    intro μ
    refine CompDiff.norm_iteratedFDeriv_comp_sub_le hU₀ (hℓ μ) hCU₀ hC₀ (hM₀ μ)
      (contDiff_jetQ θ hY₀).contDiffAt (contDiff_jetQ θ hY₁).contDiffAt hw₀ hw₁ hB1
      (fun p hp hpN => ⟨?_, ?_⟩) ?_ (fun p hp hpN => ?_)
    · exact (norm_iteratedFDeriv_jetQ_le (by omega) θ
        (hY₀.of_le (by exact_mod_cast hpN)) z).trans (hBY p hp hpN).1
    · exact (norm_iteratedFDeriv_jetQ_le (by omega) θ
        (hY₁.of_le (by exact_mod_cast hpN)) z).trans (hBY p hp hpN).2
    · have e : jetQ θ Y₁ z - jetQ θ Y₀ z = ((0 : Θ), (Y₁ - Y₀) z) := by
        simp [jetQ]
      rw [e, Prod.norm_mk, norm_zero, max_eq_right (norm_nonneg _)]
      have := hηY 0 (Nat.zero_le _)
      rwa [norm_iteratedFDeriv_zero] at this
    · exact (norm_iteratedFDeriv_jetQ_sub_le θ (hY₁.of_le (by exact_mod_cast hpN))
        (hY₀.of_le (by exact_mod_cast hpN)) z).trans (hηY p hpN)
  rw [iteratedFDeriv_foOp hh₁ hk₁, iteratedFDeriv_foOp hh₀ hk₀]
  set a₁ := iteratedFDeriv ℝ n (G₁ ∘ jetP θ Y₁) z
  set a₀ := iteratedFDeriv ℝ n (G₁ ∘ jetP θ Y₀) z
  set s₁ : Fin 4 → (R4 [×n]→L[ℝ] (S →L[ℝ] ℝ)) := fun μ =>
    (ContinuousLinearMap.apply ℝ (S →L[ℝ] ℝ) (evec μ)).compContinuousMultilinearMap
      (iteratedFDeriv ℝ n (fderiv ℝ (ℓ μ ∘ jetQ θ Y₁)) z)
  set s₀ : Fin 4 → (R4 [×n]→L[ℝ] (S →L[ℝ] ℝ)) := fun μ =>
    (ContinuousLinearMap.apply ℝ (S →L[ℝ] ℝ) (evec μ)).compContinuousMultilinearMap
      (iteratedFDeriv ℝ n (fderiv ℝ (ℓ μ ∘ jetQ θ Y₀)) z)
  have e : (a₁ - ∑ μ, s₁ μ) - (a₀ - ∑ μ, s₀ μ) = (a₁ - a₀) - ∑ μ, (s₁ μ - s₀ μ) := by
    have h := Finset.sum_sub_distrib (s := (Finset.univ : Finset (Fin 4))) (f := s₁) (g := s₀)
    rw [h]; abel
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  have hS2 : ∀ μ, ‖s₁ μ - s₀ μ‖ ≤
      Fintype.card (OrderedFinpartition (n + 1)) * (((n + 1 : ℕ) + 1 : ℝ) * M * B ^ (n + 1)) *
        η := by
    intro μ
    have hap : ‖ContinuousLinearMap.apply ℝ (S →L[ℝ] ℝ) (evec μ)‖ ≤ 1 :=
      (norm_apply_clm_le (evec μ)).trans (le_of_eq (norm_evec μ))
    have step1 : ‖s₁ μ - s₀ μ‖ ≤ ‖iteratedFDeriv ℝ n (fderiv ℝ (ℓ μ ∘ jetQ θ Y₁)) z -
        iteratedFDeriv ℝ n (fderiv ℝ (ℓ μ ∘ jetQ θ Y₀)) z‖ := by
      have h := norm_compCMM_sub_le (ContinuousLinearMap.apply ℝ (S →L[ℝ] ℝ) (evec μ))
        (iteratedFDeriv ℝ n (fderiv ℝ (ℓ μ ∘ jetQ θ Y₁)) z)
        (iteratedFDeriv ℝ n (fderiv ℝ (ℓ μ ∘ jetQ θ Y₀)) z)
      exact h.trans (mul_le_of_le_one_left (norm_nonneg _) hap)
    rw [norm_iteratedFDeriv_fderiv_sub (hk₁ μ) (hk₀ μ)] at step1
    exact step1.trans (hT2 μ)
  have hsum : ‖∑ μ, (s₁ μ - s₀ μ)‖ ≤ 4 * (Fintype.card (OrderedFinpartition (n + 1)) *
      (((n + 1 : ℕ) + 1 : ℝ) * M * B ^ (n + 1)) * η) := by
    have hn : ‖∑ μ, (s₁ μ - s₀ μ)‖ ≤ ∑ μ, ‖s₁ μ - s₀ μ‖ :=
      norm_sum_le (E := R4 [×n]→L[ℝ] (S →L[ℝ] ℝ)) _ _
    refine hn.trans ((Finset.sum_le_sum fun μ _ => hS2 μ).trans (le_of_eq ?_))
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; norm_num
  have hBn : B ^ n ≤ B ^ (n + 1) := pow_le_pow_right₀ hB1 (Nat.le_succ n)
  have hcard0 : (0 : ℝ) ≤ Fintype.card (OrderedFinpartition n) := by positivity
  have hX : ((n : ℝ) + 1) * M * B ^ n ≤ (n + 2) * M * B ^ (n + 1) := by
    have h1 : M * B ^ n ≤ M * B ^ (n + 1) := mul_le_mul_of_nonneg_left hBn hM0
    have h2 : ((n : ℝ) + 1) * (M * B ^ n) ≤ (n + 2) * (M * B ^ (n + 1)) :=
      mul_le_mul (by linarith) h1 (by positivity) (by positivity)
    calc ((n : ℝ) + 1) * M * B ^ n = ((n : ℝ) + 1) * (M * B ^ n) := by ring
      _ ≤ (n + 2) * (M * B ^ (n + 1)) := h2
      _ = (n + 2) * M * B ^ (n + 1) := by ring
  have hpush : (((n + 1 : ℕ) : ℝ) + 1) = n + 2 := by push_cast; ring
  rw [hpush] at hsum
  refine (add_le_add hT1 hsum).trans ?_
  unfold cE
  have hY : 0 ≤ (n + 2 : ℝ) * M * B ^ (n + 1) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hX (mul_nonneg hcard0 hη0)]

-- the Faà di Bruno bookkeeping elaborates large multilinear-map terms
set_option maxHeartbeats 1000000 in
/-- **Bound for a first-order operator**. -/
theorem norm_iteratedFDeriv_foOp_le {n : ℕ} (hU₁ : IsOpen U₁) (hG₁ : ContDiffOn ℝ (n + 1) G₁ U₁)
    (hU₀ : IsOpen U₀) (hℓ : ∀ μ, ContDiffOn ℝ (n + 1 + 1) (ℓ μ) U₀) {M : ℝ}
    {Y : R4 → V} (hY : ContDiff ℝ (n + 1) Y)
    (hUY : ∀ z, jetP θ Y z ∈ U₁) (hVY : ∀ z, jetQ θ Y z ∈ U₀) {z : R4}
    (hM₁ : ∀ k ≤ n, ‖iteratedFDeriv ℝ k G₁ (jetP θ Y z)‖ ≤ M)
    (hM₀ : ∀ μ, ∀ k ≤ n + 1, ‖iteratedFDeriv ℝ k (ℓ μ) (jetQ θ Y z)‖ ≤ M) {B : ℝ} (hB1 : 1 ≤ B)
    (hBJ : ∀ p, 1 ≤ p → p ≤ n → ‖iteratedFDeriv ℝ p (jet1 Y) z‖ ≤ B)
    (hBY : ∀ p, 1 ≤ p → p ≤ n + 1 → ‖iteratedFDeriv ℝ p Y z‖ ≤ B) :
    ‖iteratedFDeriv ℝ n (foOp G₁ ℓ θ Y) z‖ ≤ cE n * M * B ^ (n + 1) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM₁ 0 (Nat.zero_le _))
  have hJ : ContDiff ℝ n (jetP θ Y) := contDiff_jetP θ hY
  have hh : ContDiff ℝ n (G₁ ∘ jetP θ Y) :=
    (hG₁.of_le (by exact_mod_cast Nat.le_succ n)).comp_contDiff hJ hUY
  have hk : ∀ μ, ContDiff ℝ (n + 1) (ℓ μ ∘ jetQ θ Y) := fun μ =>
    ((hℓ μ).of_le (by exact_mod_cast Nat.le_succ (n + 1))).comp_contDiff (contDiff_jetQ θ hY) hVY
  have hT1 : ‖iteratedFDeriv ℝ n (G₁ ∘ jetP θ Y) z‖ ≤
      Fintype.card (OrderedFinpartition n) * M * B ^ n :=
    CompDiff.norm_iteratedFDeriv_comp_le_local
      ((hG₁.of_le (by exact_mod_cast Nat.le_succ n)).contDiffAt (hU₁.mem_nhds (hUY z)))
      hJ.contDiffAt hB1 hM₁ (fun p hp hpN => (norm_iteratedFDeriv_jetP_le (by omega) θ
        (hY.of_le (by exact_mod_cast (show p + 1 ≤ n + 1 by omega))) z).trans (hBJ p hp hpN))
  have hT2 : ∀ μ, ‖iteratedFDeriv ℝ (n + 1) (ℓ μ ∘ jetQ θ Y) z‖ ≤
      Fintype.card (OrderedFinpartition (n + 1)) * M * B ^ (n + 1) := fun μ =>
    CompDiff.norm_iteratedFDeriv_comp_le_local
      (((hℓ μ).of_le (by exact_mod_cast Nat.le_succ (n + 1))).contDiffAt
        (hU₀.mem_nhds (hVY z)))
      (contDiff_jetQ θ hY).contDiffAt hB1 (hM₀ μ) (fun p hp hpN =>
        (norm_iteratedFDeriv_jetQ_le (by omega) θ (hY.of_le (by exact_mod_cast hpN)) z).trans
          (hBY p hp hpN))
  rw [iteratedFDeriv_foOp hh hk]
  refine (norm_sub_le _ _).trans ?_
  have hS2 : ∀ μ, ‖(ContinuousLinearMap.apply ℝ (S →L[ℝ] ℝ) (evec μ)).compContinuousMultilinearMap
      (iteratedFDeriv ℝ n (fderiv ℝ (ℓ μ ∘ jetQ θ Y)) z)‖ ≤
        Fintype.card (OrderedFinpartition (n + 1)) * M * B ^ (n + 1) := by
    intro μ
    have hap : ‖ContinuousLinearMap.apply ℝ (S →L[ℝ] ℝ) (evec μ)‖ ≤ 1 :=
      (norm_apply_clm_le (evec μ)).trans (le_of_eq (norm_evec μ))
    have step1 := ContinuousLinearMap.norm_compContinuousMultilinearMap_le
      (ContinuousLinearMap.apply ℝ (S →L[ℝ] ℝ) (evec μ))
      (iteratedFDeriv ℝ n (fderiv ℝ (ℓ μ ∘ jetQ θ Y)) z)
    have step2 : ‖ContinuousLinearMap.apply ℝ (S →L[ℝ] ℝ) (evec μ)‖ *
        ‖iteratedFDeriv ℝ n (fderiv ℝ (ℓ μ ∘ jetQ θ Y)) z‖ ≤
          ‖iteratedFDeriv ℝ n (fderiv ℝ (ℓ μ ∘ jetQ θ Y)) z‖ :=
      mul_le_of_le_one_left (norm_nonneg _) hap
    rw [norm_iteratedFDeriv_fderiv] at step1 step2
    exact step1.trans (step2.trans (hT2 μ))
  have hsum := (norm_sum_le (E := R4 [×n]→L[ℝ] (S →L[ℝ] ℝ)) _ _).trans
    (Finset.sum_le_sum fun μ (_ : μ ∈ Finset.univ) => hS2 μ)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  refine (add_le_add hT1 hsum).trans ?_
  unfold cE
  have hBn : B ^ n ≤ B ^ (n + 1) := pow_le_pow_right₀ hB1 (Nat.le_succ n)
  have hcard0 : (0 : ℝ) ≤ Fintype.card (OrderedFinpartition n) := by positivity
  have := mul_le_mul_of_nonneg_left hBn (mul_nonneg hcard0 hM0)
  push_cast
  nlinarith

end FirstOrder


/-! ### Smoothness of the operators -/

section Smooth

theorem contDiff_jet1_infty {Y : R4 → V} (hY : ContDiff ℝ ∞ Y) : ContDiff ℝ ∞ (jet1 Y) := by
  rw [jet1_eq]
  have hd : ContDiff ℝ ∞ (fderiv ℝ Y) := hY.fderiv_right (by simp)
  exact ((ContinuousLinearMap.inl ℝ V (Fin 4 → V)).contDiff.comp hY).add
    (ContDiff.sum fun μ _ => (ContinuousLinearMap.contDiff (slotL (V := V) μ)).comp hd)

theorem contDiff_jetP_infty (θ : Θ) {Y : R4 → V} (hY : ContDiff ℝ ∞ Y) :
    ContDiff ℝ ∞ (jetP θ Y) := by
  rw [jetP_eq]
  exact contDiff_const.add ((ContinuousLinearMap.inr ℝ Θ (JS V)).contDiff.comp
    (contDiff_jet1_infty hY))

theorem contDiff_jetQ_infty (θ : Θ) {Y : R4 → V} (hY : ContDiff ℝ ∞ Y) :
    ContDiff ℝ ∞ (jetQ θ Y) := by
  rw [jetQ_eq]
  exact contDiff_const.add ((inrP Θ V).contDiff.comp hY)

theorem contDiff_eulerOp {G : Θ × JS V → (JS V →L[ℝ] ℝ)} {U : Set (Θ × JS V)} {θ : Θ}
    (hG : ContDiffOn ℝ ∞ G U) {Y : R4 → V} (hY : ContDiff ℝ ∞ Y) (hUY : ∀ z, jetP θ Y z ∈ U) :
    ContDiff ℝ ∞ (eulerOp G θ Y) := by
  have hh : ContDiff ℝ ∞ (G ∘ jetP θ Y) := hG.comp_contDiff (contDiff_jetP_infty θ hY) hUY
  rw [eulerOp_eq']
  refine ((Aop (V := V)).contDiff.comp hh).sub (ContDiff.sum fun μ _ => ?_)
  exact (ContinuousLinearMap.apply ℝ (V →L[ℝ] ℝ) (evec μ)).contDiff.comp
    (((Bop (V := V) μ).contDiff.comp hh).fderiv_right (m := ∞) (by simp))

theorem contDiff_foOp {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
    {G₁ : Θ × JS V → (S →L[ℝ] ℝ)} {ℓ : Fin 4 → Θ × V → (S →L[ℝ] ℝ)} {U₁ : Set (Θ × JS V)}
    {U₀ : Set (Θ × V)} {θ : Θ} (hG₁ : ContDiffOn ℝ ∞ G₁ U₁) (hℓ : ∀ μ, ContDiffOn ℝ ∞ (ℓ μ) U₀)
    {Y : R4 → V} (hY : ContDiff ℝ ∞ Y) (hUY : ∀ z, jetP θ Y z ∈ U₁)
    (hVY : ∀ z, jetQ θ Y z ∈ U₀) : ContDiff ℝ ∞ (foOp G₁ ℓ θ Y) := by
  rw [foOp_eq]
  refine (hG₁.comp_contDiff (contDiff_jetP_infty θ hY) hUY).sub (ContDiff.sum fun μ _ => ?_)
  exact (ContinuousLinearMap.apply ℝ (S →L[ℝ] ℝ) (evec μ)).contDiff.comp
    (((hℓ μ).comp_contDiff (contDiff_jetQ_infty θ hY) hVY).fderiv_right (m := ∞) (by simp))

end Smooth

end

end RenewalGeometry.ContEulerBounds
