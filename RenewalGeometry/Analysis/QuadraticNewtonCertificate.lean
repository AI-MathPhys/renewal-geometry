/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.ExactSlowBranchData

/-!
# Contraction certificate for an exactly quadratic map and analytic root continuation
  (`prop:supp-exact-slope-contraction`, `eq:supp-exact-slope-quadratic-Taylor`,
  `eq:supp-exact-slope-contraction-data`, `eq:supp-exact-slope-contraction-condition`,
  `eq:supp-exact-slope-slice`, `eq:supp-exact-slope-slice-map`;
  emergent-spacetime manuscript)

General part (any real Banach space `E`; the paper uses `E = ℝ²`):

* `quadratic_contraction_certificate`: let `F : E → E` satisfy the exact quadratic Taylor
  identity `F(ȳ + q) = F(ȳ) + J q + 𝔹[q, q]` (`eq:supp-exact-slope-quadratic-Taylor`),
  let `M` be invertible (injectivity suffices) and `r > 0`, and put `η = ‖M F(ȳ)‖`,
  `θ = ‖I - M J‖`, `β = 2 ‖M 𝔹‖`, `q_* = θ + β r`.  If `q_* < 1` and `η + q_* r < r`,
  then `F` has a unique zero in the closed ball `B̄(ȳ, r)`, and it lies in the open ball.
  (Symmetry of `𝔹` is not needed.)
* `analytic_root_continuation`: the parameterised implicit-function theorem in the
  analytic class (`ContDiffAt ℝ ω`, Mathlib's `ContDiffAt.implicitFunction`): a root of a
  map `G(s, y)` that is analytic near the root and whose partial derivative in `y` is
  invertible there continues to a unique local root curve `s ↦ ψ(s)`, analytic near `s₀`.

Slice part (`eq:supp-exact-slope-slice-map`): for the two-row quadratic map
`ℛ(c) = 2 𝔤₂(b_*, J_H c) + 𝔤₂(J_H c, J_H c)` of `Gravity/ExactSlowBranchData.lean`
(`ExactSlowBranch.scriptR`), the slice map `F_s(y) = ℛ(c_* + E y + s n) - y₀` is analytic
(`scriptR_contDiff`, `sliceMap_contDiff`), and `slope_contraction_certificate` is the
proposition: the certificate gives the unique zero of `F_{s₀}` in the closed `r`-ball about
`ȳ` (interior), and if the `y`-derivative of `(s, y) ↦ F_s(y)` at that root is invertible,
the slice roots continue to a local analytic root curve.
-/

namespace RenewalGeometry
namespace QuadraticNewton

open Metric Set Filter Topology
open scoped NNReal ContDiff

section Certificate

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The bilinear map `M 𝔹 : (q, q') ↦ M (𝔹[q, q'])`. -/
noncomputable def compBilin (M : E →L[ℝ] E) (B : E →L[ℝ] E →L[ℝ] E) : E →L[ℝ] E →L[ℝ] E :=
  (ContinuousLinearMap.compL ℝ E E E M).comp B

@[simp]
theorem compBilin_apply (M : E →L[ℝ] E) (B : E →L[ℝ] E →L[ℝ] E) (q q' : E) :
    compBilin M B q q' = M (B q q') := rfl

/-- The frozen Newton map `T(q) = q - M F(ȳ + q)` of `prop:supp-exact-slope-contraction`. -/
def newtonMap (F : E → E) (M : E →L[ℝ] E) (ybar q : E) : E := q - M (F (ybar + q))

/-- Under the exact quadratic Taylor identity,
`T(q) = (I - M J) q - M F(ȳ) - M 𝔹[q, q]`. -/
theorem newtonMap_eq {F : E → E} {ybar : E} {J : E →L[ℝ] E} {B : E →L[ℝ] E →L[ℝ] E}
    (M : E →L[ℝ] E) (hF : ∀ q, F (ybar + q) = F ybar + J q + B q q) (q : E) :
    newtonMap F M ybar q = (1 - M.comp J) q - M (F ybar) - compBilin M B q q := by
  simp only [newtonMap, hF, map_add, sub_apply,
    one_apply_eq_self, ContinuousLinearMap.comp_apply, compBilin_apply]
  abel

/-- `‖T(0)‖ = η = ‖M F(ȳ)‖`. -/
theorem norm_newtonMap_zero (F : E → E) (M : E →L[ℝ] E) (ybar : E) :
    ‖newtonMap F M ybar 0‖ = ‖M (F ybar)‖ := by
  simp [newtonMap]

/-- Lipschitz bound of the Newton map on the closed `r`-ball:
`‖T q - T q'‖ ≤ (θ + β r) ‖q - q'‖` with `θ = ‖I - M J‖`, `β = 2 ‖M 𝔹‖`. -/
theorem norm_newtonMap_sub_le {F : E → E} {ybar : E} {J : E →L[ℝ] E}
    {B : E →L[ℝ] E →L[ℝ] E} (M : E →L[ℝ] E) (hF : ∀ q, F (ybar + q) = F ybar + J q + B q q)
    {r : ℝ} {q q' : E} (hq : ‖q‖ ≤ r) (hq' : ‖q'‖ ≤ r) :
    ‖newtonMap F M ybar q - newtonMap F M ybar q'‖
      ≤ (‖1 - M.comp J‖ + 2 * ‖compBilin M B‖ * r) * ‖q - q'‖ := by
  set MB := compBilin M B
  have hsplit : newtonMap F M ybar q - newtonMap F M ybar q'
      = (1 - M.comp J) (q - q') - (MB q (q - q') + MB (q - q') q') := by
    rw [newtonMap_eq M hF, newtonMap_eq M hF]
    simp only [map_sub, sub_apply]
    abel
  rw [hsplit]
  have h1 : ‖(1 - M.comp J) (q - q')‖ ≤ ‖1 - M.comp J‖ * ‖q - q'‖ :=
    ContinuousLinearMap.le_opNorm _ _
  have h2 : ‖MB q (q - q')‖ ≤ ‖MB‖ * r * ‖q - q'‖ := by
    calc ‖MB q (q - q')‖ ≤ ‖MB‖ * ‖q‖ * ‖q - q'‖ := ContinuousLinearMap.le_opNorm₂ _ _ _
      _ ≤ ‖MB‖ * r * ‖q - q'‖ := by gcongr
  have h3 : ‖MB (q - q') q'‖ ≤ ‖MB‖ * r * ‖q - q'‖ := by
    calc ‖MB (q - q') q'‖ ≤ ‖MB‖ * ‖q - q'‖ * ‖q'‖ := ContinuousLinearMap.le_opNorm₂ _ _ _
      _ ≤ ‖MB‖ * ‖q - q'‖ * r := by gcongr
      _ = ‖MB‖ * r * ‖q - q'‖ := by ring
  calc ‖(1 - M.comp J) (q - q') - (MB q (q - q') + MB (q - q') q')‖
      ≤ ‖(1 - M.comp J) (q - q')‖ + (‖MB q (q - q')‖ + ‖MB (q - q') q'‖) :=
        (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
    _ ≤ ‖1 - M.comp J‖ * ‖q - q'‖ + (‖MB‖ * r * ‖q - q'‖ + ‖MB‖ * r * ‖q - q'‖) := by
        gcongr
    _ = (‖1 - M.comp J‖ + 2 * ‖MB‖ * r) * ‖q - q'‖ := by ring

/-- **`prop:supp-exact-slope-contraction`, contraction clause (general form).**
Let `F(ȳ + q) = F(ȳ) + J q + 𝔹[q, q]` exactly, `M` injective (in finite dimension:
invertible), `r > 0`, and `η = ‖M F(ȳ)‖`, `θ = ‖I - M J‖`, `β = 2 ‖M 𝔹‖`,
`q_* = θ + β r`.  If `q_* < 1` and `η + q_* r < r`, then `F` has a zero `y` in the closed
ball `B̄(ȳ, r)`, it lies in the open ball, and it is the only zero in the closed ball. -/
theorem quadratic_contraction_certificate [CompleteSpace E] (F : E → E) (ybar : E)
    (J : E →L[ℝ] E) (B : E →L[ℝ] E →L[ℝ] E) (M : E →L[ℝ] E) (hM : Function.Injective M)
    (hF : ∀ q, F (ybar + q) = F ybar + J q + B q q)
    (r η θ β qstar : ℝ) (hr : 0 < r) (hη : η = ‖M (F ybar)‖) (hθ : θ = ‖1 - M.comp J‖)
    (hβ : β = 2 * ‖compBilin M B‖) (hqstar : qstar = θ + β * r)
    (hq1 : qstar < 1) (hball : η + qstar * r < r) :
    ∃ y ∈ closedBall ybar r, F y = 0 ∧ y ∈ ball ybar r ∧
      ∀ y' ∈ closedBall ybar r, F y' = 0 → y' = y := by
  set T := newtonMap F M ybar with hT
  have hqnn : 0 ≤ qstar := by
    rw [hqstar, hθ, hβ]; positivity
  have hlip : ∀ q q' : E, ‖q‖ ≤ r → ‖q'‖ ≤ r → ‖T q - T q'‖ ≤ qstar * ‖q - q'‖ := by
    intro q q' hq hq'
    have := norm_newtonMap_sub_le M hF hq hq'
    rw [← hθ, ← hβ, ← hqstar] at this
    exact this
  have hT0 : ‖T 0‖ = η := by rw [hT, norm_newtonMap_zero, hη]
  -- `T` maps the closed ball into the open ball
  have hmaps_open : ∀ q : E, ‖q‖ ≤ r → ‖T q‖ < r := by
    intro q hq
    have h1 : ‖T q - T 0‖ ≤ qstar * ‖q - 0‖ := hlip q 0 hq (by simpa using hr.le)
    rw [sub_zero] at h1
    calc ‖T q‖ = ‖(T q - T 0) + T 0‖ := by rw [sub_add_cancel]
      _ ≤ ‖T q - T 0‖ + ‖T 0‖ := norm_add_le _ _
      _ ≤ qstar * ‖q‖ + η := by rw [hT0]; gcongr
      _ ≤ qstar * r + η := by gcongr
      _ < r := by linarith
  have hmaps : MapsTo T (closedBall (0 : E) r) (closedBall (0 : E) r) := by
    intro q hq
    rw [mem_closedBall_zero_iff] at hq ⊢
    exact (hmaps_open q hq).le
  have hcontr : ContractingWith ⟨qstar, hqnn⟩ (hmaps.restrict T _ _) := by
    refine ⟨by exact_mod_cast hq1, LipschitzWith.of_dist_le_mul fun a b => ?_⟩
    simp only [Subtype.dist_eq, MapsTo.val_restrict_apply, dist_eq_norm]
    exact hlip a b (mem_closedBall_zero_iff.mp a.2) (mem_closedBall_zero_iff.mp b.2)
  obtain ⟨q0, hq0s, hq0fix, -⟩ := hcontr.exists_fixedPoint' isClosed_closedBall.isComplete
    hmaps (mem_closedBall_self hr.le) (edist_ne_top _ _)
  have hq0 : ‖q0‖ ≤ r := mem_closedBall_zero_iff.mp hq0s
  -- fixed points of `T` are exactly zeros of `F(ȳ + ·)`
  have hfixzero : ∀ q, T q = q ↔ F (ybar + q) = 0 := by
    intro q
    simp only [hT, newtonMap, sub_eq_self]
    exact ⟨fun h => hM (by rw [h, map_zero]), fun h => by rw [h, map_zero]⟩
  refine ⟨ybar + q0, ?_, (hfixzero q0).mp hq0fix, ?_, ?_⟩
  · rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]; exact hq0
  · rw [mem_ball, dist_eq_norm, add_sub_cancel_left, ← hq0fix.eq]; exact hmaps_open q0 hq0
  · intro y' hy' hFy'
    set q' := y' - ybar with hq'def
    have hq' : ‖q'‖ ≤ r := by rw [hq'def, ← dist_eq_norm]; exact hy'
    have hfix' : T q' = q' := (hfixzero q').mpr (by rw [hq'def, add_sub_cancel]; exact hFy')
    have hle : ‖q' - q0‖ ≤ qstar * ‖q' - q0‖ := by
      have := hlip q' q0 hq' hq0
      rwa [hfix', hq0fix.eq] at this
    have hzero : ‖q' - q0‖ = 0 := by
      have hnn := norm_nonneg (q' - q0)
      nlinarith
    rw [norm_eq_zero, sub_eq_zero] at hzero
    rw [← hzero, hq'def, add_sub_cancel]

/-- **`prop:supp-exact-slope-contraction`, continuation clause (general form).** Let
`G : ℝ × E → E` be analytic (`ContDiffAt ℝ ω`) at `(s₀, y₀)`, `G(s₀, y₀) = 0`, and let the
partial derivative `∂_y G(s₀, y₀)` be invertible.  Then there is a root curve `ψ` with
`ψ(s₀) = y₀`, analytic at every `s` near `s₀`, `G(s, ψ(s)) = 0` for `s` near `s₀`, and
near `(s₀, y₀)` the zero set of `G` is exactly the graph of `ψ`. -/
theorem analytic_root_continuation [CompleteSpace E] (G : ℝ × E → E) (s₀ : ℝ) (y₀ : E)
    (hG : ContDiffAt ℝ ω G (s₀, y₀)) (hroot : G (s₀, y₀) = 0)
    (hinv : ((fderiv ℝ G (s₀, y₀)).comp (ContinuousLinearMap.inr ℝ ℝ E)).IsInvertible) :
    ∃ ψ : ℝ → E, ψ s₀ = y₀ ∧ (∀ᶠ s in 𝓝 s₀, AnalyticAt ℝ ψ s) ∧
      (∀ᶠ s in 𝓝 s₀, G (s, ψ s) = 0) ∧
      ∀ᶠ p in 𝓝 (s₀, y₀), G p = 0 ↔ ψ p.1 = p.2 := by
  have pn : (ω : WithTop ℕ∞) ≠ 0 := by simp
  refine ⟨hG.implicitFunction pn hinv, hG.implicitFunction_apply_self pn hinv, ?_, ?_, ?_⟩
  · exact (hG.contDiffAt_implicitFunction pn hinv).analyticAt.eventually_analyticAt
  · filter_upwards [hG.eventually_apply_implicitFunction pn hinv] with s hs
    rw [hs, hroot]
  · filter_upwards [hG.eventually_apply_eq_iff_implicitFunction pn hinv] with p hp
    rw [← hp, hroot]

end Certificate

/-! ## The slope slice map -/

section Slice

open ExactSlowBranch

variable {V Zg Y : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup Zg] [NormedSpace ℝ Zg] [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- The two-row quadratic map `ℛ` is a polynomial map, hence analytic. -/
theorem scriptR_contDiff (cg : V → Zg) (JH : Y →L[ℝ] V) (bstar : V) {n : WithTop ℕ∞} :
    ContDiff ℝ n (scriptR cg JH bstar) := by
  set Bil := fderiv ℝ (fderiv ℝ cg) 0
  have h : scriptR cg JH bstar = fun c => (2 : ℝ) • Bil bstar (JH c) + Bil (JH c) (JH c) := rfl
  rw [h]
  have h1 : ContDiff ℝ n fun c => Bil bstar (JH c) := ((Bil bstar).comp JH).contDiff
  have h2 : ContDiff ℝ n fun c => Bil (JH c) := (Bil.comp JH).contDiff
  exact (h1.const_smul _).add (h2.clm_apply JH.contDiff)

/-- The slice map `F_s(y) = ℛ(c_* + E y + s n) - y₀` of `eq:supp-exact-slope-slice-map`,
as a function of `(s, y)`. -/
noncomputable def sliceMap {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (cg : V → Zg) (JH : Y →L[ℝ] V) (bstar : V) (cstar : Y) (Esl : P →L[ℝ] Y) (nvec : Y)
    (y0 : Zg) (p : ℝ × P) : Zg :=
  scriptR cg JH bstar (cstar + Esl p.2 + p.1 • nvec) - y0

/-- The slice map is analytic in `(s, y)`. -/
theorem sliceMap_contDiff {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (cg : V → Zg) (JH : Y →L[ℝ] V) (bstar : V) (cstar : Y) (Esl : P →L[ℝ] Y) (nvec : Y)
    (y0 : Zg) {n : WithTop ℕ∞} :
    ContDiff ℝ n (sliceMap cg JH bstar cstar Esl nvec y0) := by
  unfold sliceMap
  have hin : ContDiff ℝ n fun p : ℝ × P => cstar + Esl p.2 + p.1 • nvec :=
    (contDiff_const.add (Esl.contDiff.comp contDiff_snd)).add
      (contDiff_fst.smul contDiff_const)
  exact ((scriptR_contDiff cg JH bstar).comp hin).sub contDiff_const

/-- **`prop:supp-exact-slope-contraction`.** Fix `s = s₀`, a centre `ȳ`, `M` invertible
(injective) and `r > 0`, and write `F_{s₀}(ȳ + q) = F_{s₀}(ȳ) + J q + 𝔹[q, q]`
(`eq:supp-exact-slope-quadratic-Taylor`) for the slice map
`F_s(y) = ℛ(c_* + E y + s n) - y₀`.  With `η = ‖M F_{s₀}(ȳ)‖`, `θ = ‖I - M J‖`,
`β = 2 ‖M 𝔹‖`, `q_* = θ + β r`, the conditions `q_* < 1`, `η + q_* r < r` give a unique
zero `y_*` of `F_{s₀}` in the closed `r`-ball about `ȳ`, lying in its interior.  If the
`y`-derivative of `(s, y) ↦ F_s(y)` at `(s₀, y_*)` is invertible, the slice roots continue
to a local root curve `s ↦ ψ(s)` through `y_*`, analytic near `s₀`, which is locally the
whole zero set. -/
theorem slope_contraction_certificate {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [CompleteSpace P] (cg : V → P) (JH : Y →L[ℝ] V) (bstar : V) (cstar : Y)
    (Esl : P →L[ℝ] Y) (nvec : Y) (y0 : P) (s₀ : ℝ) (ybar : P) (J : P →L[ℝ] P)
    (B : P →L[ℝ] P →L[ℝ] P) (M : P →L[ℝ] P) (hM : Function.Injective M)
    (hF : ∀ q, sliceMap cg JH bstar cstar Esl nvec y0 (s₀, ybar + q)
      = sliceMap cg JH bstar cstar Esl nvec y0 (s₀, ybar) + J q + B q q)
    (r η θ β qstar : ℝ) (hr : 0 < r)
    (hη : η = ‖M (sliceMap cg JH bstar cstar Esl nvec y0 (s₀, ybar))‖)
    (hθ : θ = ‖1 - M.comp J‖) (hβ : β = 2 * ‖compBilin M B‖) (hqstar : qstar = θ + β * r)
    (hq1 : qstar < 1) (hball : η + qstar * r < r) :
    ∃ ystar ∈ closedBall ybar r,
      sliceMap cg JH bstar cstar Esl nvec y0 (s₀, ystar) = 0 ∧ ystar ∈ ball ybar r ∧
      (∀ y' ∈ closedBall ybar r, sliceMap cg JH bstar cstar Esl nvec y0 (s₀, y') = 0 →
        y' = ystar) ∧
      (((fderiv ℝ (sliceMap cg JH bstar cstar Esl nvec y0) (s₀, ystar)).comp
          (ContinuousLinearMap.inr ℝ ℝ P)).IsInvertible →
        ∃ ψ : ℝ → P, ψ s₀ = ystar ∧ (∀ᶠ s in 𝓝 s₀, AnalyticAt ℝ ψ s) ∧
          (∀ᶠ s in 𝓝 s₀, sliceMap cg JH bstar cstar Esl nvec y0 (s, ψ s) = 0) ∧
          ∀ᶠ p in 𝓝 (s₀, ystar), sliceMap cg JH bstar cstar Esl nvec y0 p = 0 ↔ ψ p.1 = p.2) := by
  obtain ⟨ystar, hmem, hzero, hint, huniq⟩ :=
    quadratic_contraction_certificate (fun y => sliceMap cg JH bstar cstar Esl nvec y0 (s₀, y))
      ybar J B M hM hF r η θ β qstar hr hη hθ hβ hqstar hq1 hball
  refine ⟨ystar, hmem, hzero, hint, huniq, fun hinv => ?_⟩
  exact analytic_root_continuation _ s₀ ystar
    (sliceMap_contDiff cg JH bstar cstar Esl nvec y0).contDiffAt hzero hinv

end Slice

end QuadraticNewton
end RenewalGeometry
