/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Action.NativeDensitiesExact

/-!
# Shifted-first-jet normal form of the local action and its uniform Hessian scale
  (`lem:native-firstjet-normal-form`, `lem:native-action-Hessian`,
   Einstein–Standard-Model action-closure manuscript)

* **Curl decomposition of the plaquette logarithm.**  With `L(z) = 1 + z L₁(z)`
  (`logQuotient_eq_one_add`, `L₁` an `ofScalars` series of radius `1`) and the explicit quotient
  `Q = (a - b) + G(h; X, Y, ha, hb)` of `lem:native-plaquette` (`quotientPoly_eq_remQuotient`),
  the plaquette logarithm is
  `Φ(h; X, Y, a, b) = (a - b) + Rem(h; X, Y, ha, hb)` (`logPlaquette_eq_curl_add_rem`),
  where `Rem = G + ((A - B) + hG)² L₁(h((A - B) + hG))` (`remPlaquette`) is jointly analytic near
  `h = 0` and depends on `a, b` only through the shifted values `ha, hb`.
* **The divided difference of the Palatini coefficient** (`eq:native-C-firstjet`, in algebraic
  form): `det(e₀ + hp) - det e₀ = h · dqDet(e₀, e₀ + hp, p)` by row telescoping
  (`det_add_smul_sub_det`), `(e₀+hp)⁻¹ - e₀⁻¹ = -h (e₀+hp)⁻¹ p e₀⁻¹`, and hence
  `C(e₀ + hp) - C(e₀) = h · dqPal(h; e₀, p)` (`smul_dqPal_eq`) for the antisymmetrised Palatini
  coefficient `C^{μν}(e) = v(e)/(2κ)(e_a^μ e^{bν} - e_a^ν e^{bμ})` on the oriented chart
  `det e > 0`; `dqPal` is smooth in `(h, e₀, p)` wherever `e₀` and `e₀ + hp` are invertible.
* **`lem:native-firstjet-normal-form`** (`localAction_eq_action_firstJetDensity`): on the
  oriented nondegenerate logarithm chart, `S_h^{loc}[y] = h⁴ Σ_x F_h^{(1)}(Ξ_h^{(1)} y(x))`
  exactly on the periodic grid (`ShiftedJetAction.action`), where `Ξ_h^{(1)}` is the stencil of
  shifted values and normalised first differences over the shifts `0, ±e_μ`
  (`ShiftedJetAction.stencil`) and `F_h^{(1)} = firstJetDensity D (h, ·)`; the Cartan curl is
  converted by the discrete summation by parts `eq:native-SBP` (`sum_mul_fwdDiff`) and
  `eq:native-C-firstjet`; on a sub-box the same identity holds up to the explicit collar
  functional (`localAction_box_eq`).  `F^{(1)}` is smooth in `(h, jet)` at `h = 0` on the chart
  (`contDiffAt_firstJetDensity`) with all fixed-order derivatives bounded uniformly for small `h`
  on compact subsets of the chart (`exists_uniform_bound_firstJetDensity`).
* **`lem:native-action-Hessian`** (`abs_iteratedFDeriv_localAction_le`,
  `abs_iteratedFDeriv_localAction_le_mass`, `abs_localAction_sub_le`): on a compact set of jets
  inside the chart there are `h₀ > 0` and constants `C₁, K₀, D₀` independent of `h ≤ h₀` and of the
  number of nodes such that `|D²S_h^{loc}(y)[u,v]| ≤ C₁ ‖u‖_{1,h} ‖v‖_{1,h}`,
  `|D²S_h^{loc}(y)[u,v]| ≤ K₀ h⁻² ‖u‖_{0,h} ‖v‖_{0,h}` and
  `|S_h^{loc}(y) - S_h^{loc}(y')| ≤ D₀ · (h⁴ n⁴)` for all records whose stencils lie in the
  compact set.
-/

open NormedSpace Finset Filter Topology
open scoped ContDiff

namespace RenewalGeometry

/-! ### `L(z) = 1 + z L₁(z)` and the curl decomposition of the plaquette logarithm -/

namespace ShiftedPlaquette

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄]

/-- Coefficients of `L₁(z) = (L(z) - 1)/z = Σ_{n ≥ 0} (-1)^{n+1} z^n/(n+2)`. -/
noncomputable def logQuotientCoeff₁ (n : ℕ) : ℝ := logQuotientCoeff (n + 1)

/-- The scalar power series of `L₁`. -/
noncomputable def logQuotientSeries₁ (𝔄 : Type*) [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] :
    FormalMultilinearSeries ℝ 𝔄 𝔄 :=
  FormalMultilinearSeries.ofScalars 𝔄 logQuotientCoeff₁

/-- `L₁(z) = Σ_{n ≥ 0} (-1)^{n+1} z^n/(n+2)`, so that `L(z) = 1 + z L₁(z)`. -/
noncomputable def logQuotient₁ (z : 𝔄) : 𝔄 := (logQuotientSeries₁ 𝔄).sum z

theorem norm_logQuotientCoeff₁ (n : ℕ) : ‖logQuotientCoeff₁ n‖ = 1 / ((n : ℝ) + 2) := by
  rw [logQuotientCoeff₁, norm_logQuotientCoeff]
  push_cast
  ring

variable [NormOneClass 𝔄]

/-- `L₁` has radius of convergence exactly `1`. -/
theorem logQuotientSeries₁_radius : (logQuotientSeries₁ 𝔄).radius = 1 := by
  have hr : Tendsto (fun n : ℕ => ‖logQuotientCoeff₁ n‖ / ‖logQuotientCoeff₁ n.succ‖)
      atTop (𝓝 ((1 : NNReal) : ℝ)) := by
    have heq : (fun n : ℕ => ‖logQuotientCoeff₁ n‖ / ‖logQuotientCoeff₁ n.succ‖) =
        fun n : ℕ => 1 + 1 / (((n + 1 : ℕ) : ℝ) + 1) := by
      funext n
      rw [norm_logQuotientCoeff₁, norm_logQuotientCoeff₁, Nat.succ_eq_add_one]
      push_cast
      field_simp
      ring
    rw [heq]
    have h0 : Tendsto (fun n : ℕ => (1 : ℝ) + 1 / (((n + 1 : ℕ) : ℝ) + 1)) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add
        ((tendsto_add_atTop_iff_nat 1).mpr tendsto_one_div_add_atTop_nhds_zero_nat)
    simpa using h0
  have := FormalMultilinearSeries.ofScalars_radius_eq_of_tendsto 𝔄 logQuotientCoeff₁
    (r := 1) one_ne_zero hr
  simpa [logQuotientSeries₁] using this

theorem hasFPowerSeriesOnBall_logQuotient₁ :
    HasFPowerSeriesOnBall (logQuotient₁ (𝔄 := 𝔄)) (logQuotientSeries₁ 𝔄) 0 1 := by
  have := (logQuotientSeries₁ 𝔄).hasFPowerSeriesOnBall
    (by rw [logQuotientSeries₁_radius]; exact one_pos)
  rwa [logQuotientSeries₁_radius] at this

theorem analyticAt_logQuotient₁ {z : 𝔄} (hz : ‖z‖ < 1) : AnalyticAt ℝ logQuotient₁ z := by
  refine hasFPowerSeriesOnBall_logQuotient₁.analyticAt_of_mem ?_
  rw [Metric.mem_eball, edist_dist, dist_zero_right, ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg (norm_nonneg z) |>.mpr hz

theorem hasSum_logQuotient₁ {z : 𝔄} (hz : ‖z‖ < 1) :
    HasSum (fun n => logQuotientCoeff₁ n • z ^ n) (logQuotient₁ z) := by
  have hmem : z ∈ Metric.eball (0 : 𝔄) 1 := by
    rw [Metric.mem_eball, edist_zero_right, ← ofReal_norm, ← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (norm_nonneg z)).mpr hz
  have := hasFPowerSeriesOnBall_logQuotient₁ (𝔄 := 𝔄) |>.hasSum hmem
  simpa [logQuotientSeries₁, FormalMultilinearSeries.ofScalars_apply_eq] using this

/-- `L(z) = 1 + z L₁(z)` for `‖z‖ < 1`. -/
theorem logQuotient_eq_one_add {z : 𝔄} (hz : ‖z‖ < 1) :
    logQuotient z = 1 + z * logQuotient₁ z := by
  have hs : Summable fun n : ℕ => logQuotientCoeff n • z ^ n := (hasSum_logQuotient hz).summable
  rw [logQuotient_eq_tsum, ← hs.sum_add_tsum_nat_add 1]
  have hshift : (fun n : ℕ => logQuotientCoeff (n + 1) • z ^ (n + 1)) =
      fun n => z * (logQuotientCoeff₁ n • z ^ n) := by
    funext n
    rw [pow_succ', mul_smul_comm]
    rfl
  rw [hshift, ((hasSum_logQuotient₁ hz).mul_left z).tsum_eq]
  simp [logQuotientCoeff]

/-- The part `G` of the explicit quotient `Q = (a - b) + G` of `lem:native-plaquette`, written
in the shifted variables `A = ha`, `B = hb`. -/
noncomputable def remQuotient (h : ℝ) (X Y A B : 𝔄) : 𝔄 :=
  (X ^ 2 * expRemainder (h • X) + (Y + A) ^ 2 * expRemainder (h • (Y + A)) +
      (-(X + B)) ^ 2 * expRemainder (h • -(X + B)) + (-Y) ^ 2 * expRemainder (h • -Y)) +
    (linkExp h X * linkExp h (Y + A) + linkExp h X * linkExp h (-(X + B)) +
      linkExp h X * linkExp h (-Y) + linkExp h (Y + A) * linkExp h (-(X + B)) +
      linkExp h (Y + A) * linkExp h (-Y) + linkExp h (-(X + B)) * linkExp h (-Y)) +
    h • (linkExp h X * linkExp h (Y + A) * linkExp h (-(X + B)) +
      linkExp h X * linkExp h (Y + A) * linkExp h (-Y) +
      linkExp h X * linkExp h (-(X + B)) * linkExp h (-Y) +
      linkExp h (Y + A) * linkExp h (-(X + B)) * linkExp h (-Y)) +
    h ^ 2 • (linkExp h X * linkExp h (Y + A) * linkExp h (-(X + B)) * linkExp h (-Y))

/-- `Q(h; X, Y, a, b) = (a - b) + G(h; X, Y, ha, hb)`: every term of the explicit quotient other
than `a - b` depends on `a, b` only through the shifted values `ha, hb`. -/
theorem quotientPoly_eq_remQuotient (h : ℝ) (X Y a b : 𝔄) :
    quotientPoly h X Y a b = (a - b) + remQuotient h X Y (h • a) (h • b) := by
  unfold quotientPoly remQuotient
  abel

/-- The remainder `Rem(h; X, Y, A, B) = G + ((A - B) + hG)² L₁(h((A - B) + hG))` of the curl
decomposition, as a function of the joint variable `(h, X, Y, A, B)`. -/
noncomputable def remPlaquette (p : ℝ × 𝔄 × 𝔄 × 𝔄 × 𝔄) : 𝔄 :=
  remQuotient p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 +
    ((p.2.2.2.1 - p.2.2.2.2) + p.1 • remQuotient p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) ^ 2 *
      logQuotient₁ (p.1 • ((p.2.2.2.1 - p.2.2.2.2) +
        p.1 • remQuotient p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2))

/-- **Curl decomposition of the plaquette logarithm:** on the logarithm chart `‖h² Q‖ < 1`,
`Φ(h; X, Y, a, b) = (a - b) + Rem(h; X, Y, ha, hb)`. -/
theorem logPlaquette_eq_curl_add_rem (X Y a b : 𝔄) {h : ℝ}
    (hQ : ‖h ^ 2 • quotientPoly h X Y a b‖ < 1) :
    logPlaquette X Y a b h = (a - b) + remPlaquette (h, X, Y, h • a, h • b) := by
  rw [logPlaquette, quotient_eq_quotientPoly, logQuotient_eq_one_add hQ]
  unfold remPlaquette
  simp only []
  rw [quotientPoly_eq_remQuotient] at hQ ⊢
  set G := remQuotient h X Y (h • a) (h • b) with hG
  have hA : (h • a - h • b) + h • G = h • ((a - b) + G) := by
    rw [smul_add, smul_sub]
  rw [hA, smul_smul, ← sq, smul_pow, mul_add, mul_one, ← mul_assoc, mul_smul_comm, ← sq]
  abel

attribute [local fun_prop] analyticAt_fst analyticAt_snd

/-- `G` is jointly analytic in `(h, X, Y, A, B)`. -/
theorem analyticAt_remQuotient (p : ℝ × 𝔄 × 𝔄 × 𝔄 × 𝔄) :
    AnalyticAt ℝ (fun q : ℝ × 𝔄 × 𝔄 × 𝔄 × 𝔄 => remQuotient q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2)
      p := by
  unfold remQuotient linkExp
  fun_prop

theorem continuous_remQuotient :
    Continuous (fun q : ℝ × 𝔄 × 𝔄 × 𝔄 × 𝔄 => remQuotient q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2) :=
  continuous_iff_continuousAt.mpr fun p => (analyticAt_remQuotient p).continuousAt

/-- `Rem` is jointly analytic wherever `‖h((A - B) + hG)‖ < 1`, in particular at `h = 0`. -/
theorem analyticAt_remPlaquette {p : ℝ × 𝔄 × 𝔄 × 𝔄 × 𝔄}
    (hp : ‖p.1 • ((p.2.2.2.1 - p.2.2.2.2) +
      p.1 • remQuotient p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)‖ < 1) :
    AnalyticAt ℝ remPlaquette p := by
  have hG := analyticAt_remQuotient p
  have hin : AnalyticAt ℝ (fun q : ℝ × 𝔄 × 𝔄 × 𝔄 × 𝔄 => q.1 • ((q.2.2.2.1 - q.2.2.2.2) +
      q.1 • remQuotient q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2)) p := by
    have h1 : AnalyticAt ℝ (fun q : ℝ × 𝔄 × 𝔄 × 𝔄 × 𝔄 => q.1) p := analyticAt_fst
    have h2 : AnalyticAt ℝ (fun q : ℝ × 𝔄 × 𝔄 × 𝔄 × 𝔄 => q.2.2.2.1 - q.2.2.2.2) p := by
      fun_prop
    exact h1.smul (h2.add (h1.smul hG))
  have hL : AnalyticAt ℝ logQuotient₁ (p.1 • ((p.2.2.2.1 - p.2.2.2.2) +
      p.1 • remQuotient p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)) := analyticAt_logQuotient₁ hp
  have hcomp : AnalyticAt ℝ (logQuotient₁ ∘ fun q : ℝ × 𝔄 × 𝔄 × 𝔄 × 𝔄 =>
      q.1 • ((q.2.2.2.1 - q.2.2.2.2) + q.1 • remQuotient q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2)) p :=
    AnalyticAt.comp (g := logQuotient₁) (x := p) hL hin
  have h3 : AnalyticAt ℝ (fun q : ℝ × 𝔄 × 𝔄 × 𝔄 × 𝔄 => (q.2.2.2.1 - q.2.2.2.2) +
      q.1 • remQuotient q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2) p := by
    have h1 : AnalyticAt ℝ (fun q : ℝ × 𝔄 × 𝔄 × 𝔄 × 𝔄 => q.1) p := analyticAt_fst
    have h2 : AnalyticAt ℝ (fun q : ℝ × 𝔄 × 𝔄 × 𝔄 × 𝔄 => q.2.2.2.1 - q.2.2.2.2) p := by
      fun_prop
    exact h2.add (h1.smul hG)
  exact hG.add ((h3.pow 2).mul hcomp)

end ShiftedPlaquette


/-! ### The divided difference of the Palatini coefficient (`eq:native-C-firstjet`) -/

namespace NativeDensity

open ShiftedJetAction (Grid unitVec fwdDiff stencil)
open NativeScaling (Mat eta metric readerOmega omegaLink)
open ShiftedPlaquette

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-- Rows `r < i` from `e₁`, rows `r ≥ i` from `e₀`. -/
def rowsBelow (e₀ e₁ : Mat) (i : ℕ) : Mat := fun r => if (r : ℕ) < i then e₁ r else e₀ r

/-- Rows `r < i` from `e₁`, row `i` from `p`, rows `r > i` from `e₀`. -/
def rowsMix (e₀ e₁ p : Mat) (i : Fin 4) : Mat := (rowsBelow e₀ e₁ i).updateRow i (p i)

/-- The divided difference of the determinant: `det e₁ - det e₀ = h · dqDet` when `e₁ = e₀ + hp`. -/
noncomputable def dqDet (e₀ e₁ p : Mat) : ℝ := ∑ i, (rowsMix e₀ e₁ p i).det

theorem rowsBelow_zero (e₀ e₁ : Mat) : rowsBelow e₀ e₁ 0 = e₀ := by
  ext r j
  simp [rowsBelow]

theorem rowsBelow_four (e₀ e₁ : Mat) : rowsBelow e₀ e₁ 4 = e₁ := by
  ext r j
  simp [rowsBelow, r.isLt]

theorem rowsBelow_succ (e₀ e₁ : Mat) (i : Fin 4) :
    rowsBelow e₀ e₁ (i + 1) = (rowsBelow e₀ e₁ i).updateRow i (e₁ i) := by
  ext r j
  simp only [rowsBelow, Matrix.updateRow_apply]
  by_cases hr : r = i
  · subst hr
    simp
  · have hne : (r : ℕ) ≠ i := fun h => hr (Fin.ext h)
    have : ((r : ℕ) < (i : ℕ) + 1) ↔ ((r : ℕ) < i) := by omega
    simp [hr, this]

theorem rowsBelow_apply_self (e₀ e₁ : Mat) (i : Fin 4) : rowsBelow e₀ e₁ i i = e₀ i := by
  simp [rowsBelow]

/-- Row telescoping: `det(e₀ + hp) - det e₀ = h · dqDet(e₀, e₀ + hp, p)`. -/
theorem det_add_smul_sub_det (e₀ p : Mat) (h : ℝ) :
    (e₀ + h • p).det - e₀.det = h * dqDet e₀ (e₀ + h • p) p := by
  set e₁ := e₀ + h • p with he₁
  have step : ∀ i : Fin 4, (rowsBelow e₀ e₁ (i + 1)).det - (rowsBelow e₀ e₁ i).det =
      h * (rowsMix e₀ e₁ p i).det := by
    intro i
    have hrow : e₁ i = rowsBelow e₀ e₁ i i + h • p i := by
      rw [rowsBelow_apply_self, he₁]
      rfl
    rw [rowsBelow_succ, hrow, Matrix.det_updateRow_add, Matrix.det_updateRow_smul,
      Matrix.updateRow_eq_self]
    unfold rowsMix
    ring
  have tele : ∑ i : Fin 4, ((rowsBelow e₀ e₁ (i + 1)).det - (rowsBelow e₀ e₁ i).det) =
      (rowsBelow e₀ e₁ 4).det - (rowsBelow e₀ e₁ 0).det := by
    simp only [Fin.sum_univ_four, Fin.val_zero, Fin.val_one, Fin.val_two]
    have h3 : ((3 : Fin 4) : ℕ) = 3 := rfl
    rw [h3]
    ring
  unfold dqDet
  rw [mul_sum]
  simp only [← step]
  rw [tele, rowsBelow_four, rowsBelow_zero]

theorem contDiff_dqDet {k : WithTop ℕ∞} :
    ContDiff ℝ k (fun q : Mat × Mat × Mat => dqDet q.1 q.2.1 q.2.2) := by
  unfold dqDet rowsMix rowsBelow Matrix.updateRow
  refine ContDiff.sum fun i _ => ?_
  simp only [Matrix.det_apply', Matrix.of_apply, Function.update_apply, ite_apply]
  refine ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun r _ => ?_)
  split_ifs <;> fun_prop

@[fun_prop]
theorem ContDiff.dqDet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : WithTop ℕ∞}
    {f g l : E → Mat} (hf : ContDiff ℝ k f) (hg : ContDiff ℝ k g) (hl : ContDiff ℝ k l) :
    ContDiff ℝ k (fun x => NativeDensity.dqDet (f x) (g x) (l x)) := by
  have h := ContDiff.comp (g := fun q : Mat × Mat × Mat => NativeDensity.dqDet q.1 q.2.1 q.2.2)
    (f := fun x => (f x, g x, l x)) contDiff_dqDet (hf.prodMk (hg.prodMk hl))
  simp only [Function.comp_def] at h
  exact h

@[fun_prop]
theorem ContDiffAt.dqDet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : WithTop ℕ∞}
    {f g l : E → Mat} {x : E} (hf : ContDiffAt ℝ k f x) (hg : ContDiffAt ℝ k g x)
    (hl : ContDiffAt ℝ k l x) :
    ContDiffAt ℝ k (fun x => NativeDensity.dqDet (f x) (g x) (l x)) x := by
  have h := ContDiffAt.comp (g := fun q : Mat × Mat × Mat => NativeDensity.dqDet q.1 q.2.1 q.2.2)
    (f := fun x => (f x, g x, l x)) x contDiff_dqDet.contDiffAt (hf.prodMk (hg.prodMk hl))
  simp only [Function.comp_def] at h
  exact h

/-- The bilinear form `X_{μa} (Yη)_{νb} - X_{νa} (Yη)_{μb}` entering the antisymmetrised
Palatini coefficient. -/
noncomputable def palBil (X Y : Mat) (μ ν a b : Fin 4) : ℝ :=
  X μ a * ∑ c, Y ν c * eta c b - X ν a * ∑ c, Y μ c * eta c b

/-- The antisymmetrised Palatini coefficient `C^{μν}(e) = pal^{μν} - pal^{νμ}`. -/
noncomputable def palA (κ : ℝ) (e : Mat) (μ ν a b : Fin 4) : ℝ :=
  pal κ e μ ν a b - pal κ e ν μ a b

theorem palA_eq (κ : ℝ) (e : Mat) (μ ν a b : Fin 4) :
    palA κ e μ ν a b = volume e / (2 * κ) * palBil e⁻¹ e⁻¹ μ ν a b := by
  unfold palA pal palBil invEntry
  ring

theorem palBil_add_smul (X Δ : Mat) (h : ℝ) (μ ν a b : Fin 4) :
    palBil (X + h • Δ) (X + h • Δ) μ ν a b =
      palBil X X μ ν a b + h * palBil Δ X μ ν a b + h * palBil X Δ μ ν a b +
        h ^ 2 * palBil Δ Δ μ ν a b := by
  simp only [palBil, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, add_mul, sum_add_distrib,
    mul_assoc, ← mul_sum]
  ring

theorem palBil_add_smul_right (Δ X : Mat) (h : ℝ) (μ ν a b : Fin 4) :
    palBil Δ (X + h • Δ) μ ν a b = palBil Δ X μ ν a b + h * palBil Δ Δ μ ν a b := by
  simp only [palBil, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, add_mul, sum_add_distrib,
    mul_assoc, ← mul_sum]
  ring

/-- The divided difference `dqPal(h; e₀, p)` of the antisymmetrised Palatini coefficient:
`C(e₀ + hp) - C(e₀) = h · dqPal(h; e₀, p)` on the oriented chart. -/
noncomputable def dqPal (κ h : ℝ) (e₀ p : Mat) (μ ν a b : Fin 4) : ℝ :=
  (2 * κ)⁻¹ * (dqDet e₀ (e₀ + h • p) p * palBil (e₀ + h • p)⁻¹ (e₀ + h • p)⁻¹ μ ν a b +
    volume e₀ * (palBil (-((e₀ + h • p)⁻¹ * p * e₀⁻¹)) (e₀ + h • p)⁻¹ μ ν a b +
      palBil e₀⁻¹ (-((e₀ + h • p)⁻¹ * p * e₀⁻¹)) μ ν a b))

/-- `(e₀ + hp)⁻¹ - e₀⁻¹ = -h (e₀ + hp)⁻¹ p e₀⁻¹` for invertible `e₀`, `e₀ + hp`. -/
theorem inv_add_smul_sub_inv (e₀ p : Mat) (h : ℝ) (h0 : e₀.det ≠ 0) (h1 : (e₀ + h • p).det ≠ 0) :
    (e₀ + h • p)⁻¹ = e₀⁻¹ + h • -((e₀ + h • p)⁻¹ * p * e₀⁻¹) := by
  have hu0 : IsUnit e₀ := (Matrix.isUnit_iff_isUnit_det e₀).mpr (isUnit_iff_ne_zero.mpr h0)
  have hu1 : IsUnit (e₀ + h • p) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr h1)
  have := Matrix.inv_sub_inv (A := e₀ + h • p) (B := e₀) ⟨fun _ => hu0, fun _ => hu1⟩
  rw [sub_eq_iff_eq_add] at this
  conv_lhs => rw [this]
  rw [add_comm]
  congr 1
  rw [show e₀ - (e₀ + h • p) = -(h • p) by abel, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul,
    Matrix.smul_mul, smul_neg]

/-- **`eq:native-C-firstjet` in algebraic form:** on the oriented chart,
`h · dqPal(h; e₀, p) = C(e₀ + hp) - C(e₀)`. -/
theorem smul_dqPal_eq (κ h : ℝ) (e₀ p : Mat) (h0 : 0 < e₀.det) (h1 : 0 < (e₀ + h • p).det)
    (μ ν a b : Fin 4) :
    h * dqPal κ h e₀ p μ ν a b = palA κ (e₀ + h • p) μ ν a b - palA κ e₀ μ ν a b := by
  have hinv := inv_add_smul_sub_inv e₀ p h h0.ne' h1.ne'
  have hd := det_add_smul_sub_det e₀ p h
  unfold dqPal
  rw [palA_eq, palA_eq, volume_of_det_pos h0, volume_of_det_pos h1]
  set Δ := -((e₀ + h • p)⁻¹ * p * e₀⁻¹) with hΔ
  set d := dqDet e₀ (e₀ + h • p) p with hd_def
  rw [hinv, palBil_add_smul, palBil_add_smul_right]
  have hd' : (e₀ + h • p).det = e₀.det + h * d := by linarith
  rw [hd']
  simp only [div_eq_mul_inv]
  ring

/-- `dqPal` is smooth in `(h, e₀, p)` wherever `e₀` and `e₀ + hp` are invertible. -/
theorem contDiffAt_dqPal (κ : ℝ) (μ ν a b : Fin 4) {q : ℝ × Mat × Mat} (h0 : q.2.1.det ≠ 0)
    (h1 : (q.2.1 + q.1 • q.2.2).det ≠ 0) :
    ContDiffAt ℝ ∞ (fun q : ℝ × Mat × Mat => dqPal κ q.1 q.2.1 q.2.2 μ ν a b) q := by
  unfold dqPal palBil
  simp only [Matrix.neg_apply, Matrix.mul_apply, ← invEntry_apply]
  fun_prop (disch := assumption)


/-! ### The shifted-first-jet density `F_h^{(1)}` and the normal form -/

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
variable (D : Data 𝔄 𝓗 𝓢)
variable {n : ℕ} [NeZero n]

/-- The coframe connection `ω_ν` at the node shifted by `+e_μ`, as a function of the jet:
`Ω_ν(e(x+e_μ), δ⁺e(x+e_μ))`. -/
noncomputable def jetOmegaShift (ν μ : Fin 4) (ξ : Jet (Field 𝔄 𝓗 𝓢)) : Mat :=
  readerOmega (ξ.1 (some (true, μ))).1 (fun lam => (ξ.2 (some (true, μ), lam)).1) ν

/-- The coframe at the node shifted by `-e_μ`. -/
def jetEm (μ : Fin 4) (ξ : Jet (Field 𝔄 𝓗 𝓢)) : Mat := (ξ.1 (some (false, μ))).1

/-- The normalised first difference `δ⁺_μ e` at the node shifted by `-e_μ`. -/
def jetPm (μ : Fin 4) (ξ : Jet (Field 𝔄 𝓗 𝓢)) : Mat := (ξ.2 (some (false, μ), μ)).1

/-- The Cartan remainder `Rem(h; ω_μ, ω_ν, ω_ν(x+e_μ) - ω_ν(x), ω_μ(x+e_ν) - ω_μ(x))` of the curl
decomposition, as a function of `(h, jet)`. -/
noncomputable def remCartan (μ ν : Fin 4) (q : ℝ × Jet (Field 𝔄 𝓗 𝓢)) : Op :=
  remPlaquette (q.1, matToOp (jetOmega μ q.2), matToOp (jetOmega ν q.2),
    matToOp (jetOmegaShift ν μ q.2 - jetOmega ν q.2),
    matToOp (jetOmegaShift μ ν q.2 - jetOmega μ q.2))

/-- The gravitational shifted-first-jet bulk density: the remainder part of the Cartan plaquette,
the cosmological term, and the summation-by-parts form `-⟨δ⁻_μ C, ω_ν⟩` of the curl with the
divided difference `dqPal` of `eq:native-C-firstjet`. -/
noncomputable def gravFirstJet (q : ℝ × Jet (Field 𝔄 𝓗 𝓢)) : ℝ :=
  (∑ μ, ∑ ν, ∑ a, ∑ b, pal D.κ (q.2.1 none).1 μ ν a b *
      opEntry (antisym (fun μ ν => remCartan μ ν q) μ ν) a b) -
    D.Λ / D.κ * volume (q.2.1 none).1 -
    ∑ μ, ∑ ν, ∑ a, ∑ b, dqPal D.κ q.1 (jetEm μ q.2) (jetPm μ q.2) μ ν a b * jetOmega ν q.2 a b

/-- **The shifted-first-jet density `F_h^{(1)}`** of `eq:native-firstjet-normal-form`, as a function
of `(h, Ξ_h^{(1)} y(x))`. -/
noncomputable def firstJetDensity (q : ℝ × Jet (Field 𝔄 𝓗 𝓢)) : ℝ :=
  gravFirstJet D q + normYM D (q.1, 1, q.2) + normHiggs D (q.1, 1, q.2) + normD D (q.1, 1, q.2)

/-- The Cartan plaquette `L_μ(x) L_ν(x+he_μ) L_μ(x+he_ν)⁻¹ L_ν(x)⁻¹` in the operator algebra. -/
noncomputable def cartanPlaquette (h : ℝ) (e : Grid n → Mat) (x : Grid n) (μ ν : Fin 4) : Op :=
  NativeScaling.gaugePlaquette h (fun μ x => matToOp (omegaLink h e x μ)) x μ ν

/-! #### Discrete summation by parts (`eq:native-SBP`, scalar form) -/

theorem shiftVec_some_false (μ : Fin 4) : shiftVec n (some (false, μ)) = -unitVec n μ := rfl

/-- The pointwise product rule `C δ⁺_μ W = -(δ⁻_μ C) W + δ⁻_μ (C · T_μ W)`. -/
theorem mul_fwdDiff_eq (h : ℝ) (μ : Fin 4) (C W : Grid n → ℝ) (x : Grid n) :
    C x * fwdDiff h μ W x = -(ShiftedFirstJet.bwdDiff h μ C x * W x) +
      ShiftedFirstJet.bwdDiff h μ (fun z => C z * W (z + unitVec n μ)) x := by
  unfold ShiftedJetAction.fwdDiff ShiftedFirstJet.bwdDiff
  simp only [smul_eq_mul, sub_add_cancel]
  ring

/-- Periodic summation by parts `Σ_x C δ⁺_μ W = -Σ_x (δ⁻_μ C) W`. -/
theorem sum_mul_fwdDiff (h : ℝ) (μ : Fin 4) (C W : Grid n → ℝ) :
    ∑ x, C x * fwdDiff h μ W x = -∑ x, ShiftedFirstJet.bwdDiff h μ C x * W x := by
  simp_rw [mul_fwdDiff_eq]
  rw [sum_add_distrib, ShiftedFirstJet.sum_bwdDiff, sum_neg_distrib, add_zero]

/-- Summation by parts on a sub-box with the exact collar functional. -/
theorem sum_mul_fwdDiff_box (h : ℝ) (μ : Fin 4) (C W : Grid n → ℝ) (S : Finset (Grid n)) :
    ∑ x ∈ S, C x * fwdDiff h μ W x = -∑ x ∈ S, ShiftedFirstJet.bwdDiff h μ C x * W x +
      h⁻¹ * (∑ x ∈ S, C x * W (x + unitVec n μ) -
        ∑ x ∈ S.map (Equiv.subRight (unitVec n μ)).toEmbedding, C x * W (x + unitVec n μ)) := by
  simp_rw [mul_fwdDiff_eq]
  rw [sum_add_distrib, sum_neg_distrib, ShiftedFirstJet.sum_bwdDiff_eq_collar]

/-! #### Pointwise identities -/

theorem antisym_eq_self {α : Type*} [AddCommGroup α] [Module ℝ α] (P : Fin 4 → Fin 4 → α)
    (hP : ∀ μ ν, P ν μ = -P μ ν) : antisym P = P := by
  funext μ ν
  unfold antisym
  split_ifs with h1 h2
  · rfl
  · rw [hP, neg_neg]
  · have hμν : μ = ν := le_antisymm (not_lt.mp h2) (not_lt.mp h1)
    subst hμν
    have h2 : (2 : ℝ) • P μ μ = 0 := by
      rw [two_smul]
      nth_rewrite 2 [hP μ μ]
      exact add_neg_cancel _
    exact ((smul_eq_zero.mp h2).resolve_left two_ne_zero).symm

theorem sum_pal_curl (pal u : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    ∑ μ, ∑ ν, ∑ a, ∑ b, pal μ ν a b * (u μ ν a b - u ν μ a b) =
      ∑ μ, ∑ ν, ∑ a, ∑ b, (pal μ ν a b - pal ν μ a b) * u μ ν a b := by
  simp only [mul_sub, sub_mul, sum_sub_distrib]
  congr 1
  exact Finset.sum_comm

theorem jetOmegaShift_stencil (h : ℝ) (y : Grid n → Field 𝔄 𝓗 𝓢) (x : Grid n) (ν μ : Fin 4) :
    jetOmegaShift ν μ (stencil h (shiftVec n) x y) = omegaLink h (coframe y) (x + unitVec n μ) ν := by
  simp only [jetOmegaShift, stencil_fst, stencil_snd, shiftVec_some_true, fwdDiff_coframe,
    omegaLink, coframe]

theorem jetEm_stencil (h : ℝ) (y : Grid n → Field 𝔄 𝓗 𝓢) (x : Grid n) (μ : Fin 4) :
    jetEm μ (stencil h (shiftVec n) x y) = coframe y (x - unitVec n μ) := by
  simp only [jetEm, stencil_fst, shiftVec_some_false, coframe, sub_eq_add_neg]

theorem jetPm_stencil (h : ℝ) (y : Grid n → Field 𝔄 𝓗 𝓢) (x : Grid n) (μ : Fin 4) :
    jetPm μ (stencil h (shiftVec n) x y) = fwdDiff h μ (coframe y) (x - unitVec n μ) := by
  simp only [jetPm, stencil_snd, shiftVec_some_false, fwdDiff_coframe, sub_eq_add_neg]

theorem smul_fwdDiff {V : Type*} [AddCommGroup V] [Module ℝ V] {h : ℝ} (hh : h ≠ 0) (μ : Fin 4)
    (f : Grid n → V) (x : Grid n) : h • fwdDiff h μ f x = f (x + unitVec n μ) - f x := by
  unfold ShiftedJetAction.fwdDiff
  rw [smul_smul, mul_inv_cancel₀ hh, one_smul]

/-- The curl decomposition of the Cartan curvature on the logarithm chart:
`R^h_{μν}(x) = δ⁺_μ ω_ν - δ⁺_ν ω_μ + Rem_{μν}(h; Ξ_h y(x))`. -/
theorem cartanCurvature_eq_curl_add_rem {h : ℝ} (hh : h ≠ 0) (y : Grid n → Field 𝔄 𝓗 𝓢)
    (x : Grid n) (μ ν : Fin 4) (hlog : ‖cartanPlaquette h (coframe y) x μ ν - 1‖ < 1) :
    cartanCurvature h (coframe y) x μ ν =
      matToOp (fwdDiff h μ (fun z => omegaLink h (coframe y) z ν) x -
        fwdDiff h ν (fun z => omegaLink h (coframe y) z μ) x) +
      remCartan μ ν (h, stencil h (shiftVec n) x y) := by
  unfold cartanCurvature
  rw [NativeScaling.fieldStrength_eq_logPlaquette hh]
  have hQ : ‖h ^ 2 • quotientPoly h (matToOp (omegaLink h (coframe y) x μ))
      (matToOp (omegaLink h (coframe y) x ν))
      (fwdDiff h μ (fun z => matToOp (omegaLink h (coframe y) z ν)) x)
      (fwdDiff h ν (fun z => matToOp (omegaLink h (coframe y) z μ)) x)‖ < 1 := by
    rw [← product_sub_one_eq]
    unfold cartanPlaquette at hlog
    rwa [NativeScaling.gaugePlaquette_eq_product hh] at hlog
  rw [logPlaquette_eq_curl_add_rem _ _ _ _ hQ]
  unfold remCartan
  simp only [jetOmega_stencil, jetOmegaShift_stencil, fwdDiff_matToOp, ← map_sub, ← map_smul,
    smul_fwdDiff hh]

/-- The curl part of the Palatini contraction at one node. -/
theorem sum_pal_opEntry_curl (κ : ℝ) (e : Mat) (u : Fin 4 → Fin 4 → Mat) :
    ∑ μ, ∑ ν, ∑ a, ∑ b, pal κ e μ ν a b * opEntry (matToOp (u μ ν - u ν μ)) a b =
      ∑ μ, ∑ ν, ∑ a, ∑ b, palA κ e μ ν a b * u μ ν a b := by
  simp only [map_sub, opEntry_sub, opEntry_matToOp]
  exact sum_pal_curl (fun μ ν a b => pal κ e μ ν a b) (fun μ ν a b => u μ ν a b)

/-- `eq:native-C-firstjet` on the record: the backward difference of the Palatini coefficient is
the divided difference `dqPal` evaluated at the shifted first jet. -/
theorem bwdDiff_palA_eq {h : ℝ} (hh : h ≠ 0) (κ : ℝ) (e : Grid n → Mat)
    (hdet : ∀ x, 0 < (e x).det) (x : Grid n) (μ ν a b : Fin 4) :
    ShiftedFirstJet.bwdDiff h μ (fun z => palA κ (e z) μ ν a b) x =
      dqPal κ h (e (x - unitVec n μ)) (fwdDiff h μ e (x - unitVec n μ)) μ ν a b := by
  have hrec : e x = e (x - unitVec n μ) + h • fwdDiff h μ e (x - unitVec n μ) := by
    rw [smul_fwdDiff hh, sub_add_cancel, add_sub_cancel]
  have key := smul_dqPal_eq κ h (e (x - unitVec n μ)) (fwdDiff h μ e (x - unitVec n μ))
    (hdet _) (by rw [← hrec]; exact hdet x) μ ν a b
  rw [← hrec] at key
  unfold ShiftedFirstJet.bwdDiff
  rw [smul_eq_mul, ← key, inv_mul_cancel_left₀ hh]

/-- The gravitational density at one node, on the chart: `⟨pal, antisym(Rem)⟩ - Λ/κ v` plus the curl
term `Σ palA · δ⁺_μ ω_ν`. -/
theorem gravityDensity_eq_curl {h : ℝ} (hh : h ≠ 0) (y : Grid n → Field 𝔄 𝓗 𝓢) (x : Grid n)
    (hlog : ∀ μ ν, ‖cartanPlaquette h (coframe y) x μ ν - 1‖ < 1) :
    gravityDensity D h y x =
      ((∑ μ, ∑ ν, ∑ a, ∑ b, pal D.κ (coframe y x) μ ν a b *
          opEntry (antisym (fun μ ν => remCartan μ ν (h, stencil h (shiftVec n) x y)) μ ν) a b) -
        D.Λ / D.κ * volume (coframe y x)) +
      ∑ μ, ∑ ν, ∑ a, ∑ b, palA D.κ (coframe y x) μ ν a b *
        fwdDiff h μ (fun z => omegaLink h (coframe y) z ν a b) x := by
  unfold gravityDensity
  have hR : cartanCurvature h (coframe y) x = fun μ ν =>
      matToOp (fwdDiff h μ (fun z => omegaLink h (coframe y) z ν) x -
        fwdDiff h ν (fun z => omegaLink h (coframe y) z μ) x) +
      remCartan μ ν (h, stencil h (shiftVec n) x y) := by
    funext μ ν
    exact cartanCurvature_eq_curl_add_rem hh y x μ ν (hlog μ ν)
  rw [hR]
  set u : Fin 4 → Fin 4 → Mat := fun μ ν => fwdDiff h μ (fun z => omegaLink h (coframe y) z ν) x
    with hu
  have hanti : antisym (fun μ ν => matToOp (u μ ν - u ν μ)) = fun μ ν => matToOp (u μ ν - u ν μ) :=
    antisym_eq_self _ fun μ ν => by rw [← map_neg, neg_sub]
  have hsplit : antisym (fun μ ν => matToOp (u μ ν - u ν μ) +
      remCartan μ ν (h, stencil h (shiftVec n) x y)) = fun μ ν =>
      matToOp (u μ ν - u ν μ) + antisym (fun μ ν => remCartan μ ν (h, stencil h (shiftVec n) x y)) μ ν := by
    funext μ ν
    rw [antisym_add, hanti]
  rw [hsplit]
  simp only [opEntry_add, mul_add, sum_add_distrib]
  rw [sum_pal_opEntry_curl]
  have hu' : ∀ μ ν a b, u μ ν a b = fwdDiff h μ (fun z => omegaLink h (coframe y) z ν a b) x := by
    intro μ ν a b
    simp only [hu, ShiftedJetAction.fwdDiff, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  simp only [hu']
  ring

/-- The sum over a set `S` of the curl term, by summation by parts. -/
theorem sum_curl_eq {h : ℝ} (hh : h ≠ 0) (y : Grid n → Field 𝔄 𝓗 𝓢) (hdet : ∀ x, 0 < (coframe y x).det)
    (S : Finset (Grid n)) :
    ∑ x ∈ S, ∑ μ, ∑ ν, ∑ a, ∑ b, palA D.κ (coframe y x) μ ν a b *
        fwdDiff h μ (fun z => omegaLink h (coframe y) z ν a b) x =
      -∑ x ∈ S, ∑ μ, ∑ ν, ∑ a, ∑ b, dqPal D.κ h (jetEm μ (stencil h (shiftVec n) x y))
          (jetPm μ (stencil h (shiftVec n) x y)) μ ν a b * jetOmega ν (stencil h (shiftVec n) x y) a b +
      ∑ μ, ∑ ν, ∑ a, ∑ b, h⁻¹ * (∑ x ∈ S, palA D.κ (coframe y x) μ ν a b *
          omegaLink h (coframe y) (x + unitVec n μ) ν a b -
        ∑ x ∈ S.map (Equiv.subRight (unitVec n μ)).toEmbedding, palA D.κ (coframe y x) μ ν a b *
          omegaLink h (coframe y) (x + unitVec n μ) ν a b) := by
  simp only [jetEm_stencil, jetPm_stencil, jetOmega_stencil]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := S)]
  rw [← sum_neg_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun μ _ => ?_
  rw [← sum_neg_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun ν _ => ?_
  rw [← sum_neg_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun a _ => ?_
  rw [← sum_neg_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun b _ => ?_
  rw [sum_mul_fwdDiff_box (C := fun z => palA D.κ (coframe y z) μ ν a b)
    (W := fun z => omegaLink h (coframe y) z ν a b)]
  simp only [bwdDiff_palA_eq hh D.κ (coframe y) hdet, sum_neg_distrib]

/-- **`lem:native-firstjet-normal-form`, periodic form:** on the oriented nondegenerate logarithm
chart, the local action `eq:native-local-action` is exactly the shifted-first-jet action
`h⁴ Σ_x F_h^{(1)}(Ξ_h^{(1)} y(x))` (`ShiftedJetAction.action`), with no collar term on the
periodic grid. -/
theorem localAction_eq_action_firstJetDensity {h : ℝ} (hh : h ≠ 0) (y : Grid n → Field 𝔄 𝓗 𝓢)
    (hdet : ∀ x, 0 < (coframe y x).det)
    (hlog : ∀ x μ ν, ‖cartanPlaquette h (coframe y) x μ ν - 1‖ < 1) :
    localAction D h y =
      ShiftedJetAction.action (fun ξ => firstJetDensity D (h, ξ)) h (shiftVec n) y := by
  unfold localAction ShiftedJetAction.action
  congr 1
  have hpt : ∀ x, nativeDensity D h y x =
      gravityDensity D h y x + (normYM D (h, 1, stencil h (shiftVec n) x y) +
        normHiggs D (h, 1, stencil h (shiftVec n) x y) + normD D (h, 1, stencil h (shiftVec n) x y)) := by
    intro x
    unfold nativeDensity
    rw [ymDensity_eq_scaled D hh one_ne_zero, higgsDensity_eq_scaled D hh one_ne_zero,
      diracDensity_eq_scaled D hh one_ne_zero]
    simp only [mul_one, inv_one, one_pow, one_mul]
    ring
  simp only [hpt, gravityDensity_eq_curl D hh y _ (hlog _), sum_add_distrib]
  have hcurl := sum_curl_eq D hh y hdet univ
  have hcollar : ∀ (g : Grid n → ℝ) (μ : Fin 4),
      ∑ x ∈ (univ : Finset (Grid n)).map (Equiv.subRight (unitVec n μ)).toEmbedding, g x =
        ∑ x, g x := by
    intro g μ
    rw [sum_map]
    exact Equiv.sum_comp (Equiv.subRight (unitVec n μ)) g
  simp only [hcollar, sub_self, mul_zero, sum_const_zero, add_zero] at hcurl
  rw [hcurl]
  unfold firstJetDensity gravFirstJet
  simp only [sum_add_distrib, sum_sub_distrib, sum_neg_distrib, stencil_fst, shiftVec_none,
    add_zero, coframe]
  ring

/-- The collar functional `𝓑_h[y]` of the sub-box representation: the lattice divergence of the
summation by parts, which involves the record only through the two boundary layers
`S \ (S - e_μ)` and `(S - e_μ) \ S` of the box. -/
noncomputable def collar (h : ℝ) (y : Grid n → Field 𝔄 𝓗 𝓢) (S : Finset (Grid n)) : ℝ :=
  h ^ 4 * ∑ μ, ∑ ν, ∑ a, ∑ b, h⁻¹ * (∑ x ∈ S, palA D.κ (coframe y x) μ ν a b *
      omegaLink h (coframe y) (x + unitVec n μ) ν a b -
    ∑ x ∈ S.map (Equiv.subRight (unitVec n μ)).toEmbedding, palA D.κ (coframe y x) μ ν a b *
      omegaLink h (coframe y) (x + unitVec n μ) ν a b)

/-- **`lem:native-firstjet-normal-form`, sub-box form (`eq:native-firstjet-normal-form`):** on a
sub-box `S`, `h⁴ Σ_{x ∈ S} 𝓛_h(y)(x) = h⁴ Σ_{x ∈ S} F_h^{(1)}(Ξ_h^{(1)} y(x)) + 𝓑_h[y]` with the
explicit collar functional `𝓑_h`. -/
theorem localAction_box_eq {h : ℝ} (hh : h ≠ 0) (y : Grid n → Field 𝔄 𝓗 𝓢)
    (hdet : ∀ x, 0 < (coframe y x).det)
    (hlog : ∀ x μ ν, ‖cartanPlaquette h (coframe y) x μ ν - 1‖ < 1) (S : Finset (Grid n)) :
    h ^ 4 * ∑ x ∈ S, nativeDensity D h y x =
      h ^ 4 * ∑ x ∈ S, firstJetDensity D (h, stencil h (shiftVec n) x y) + collar D h y S := by
  have hpt : ∀ x, nativeDensity D h y x =
      gravityDensity D h y x + (normYM D (h, 1, stencil h (shiftVec n) x y) +
        normHiggs D (h, 1, stencil h (shiftVec n) x y) + normD D (h, 1, stencil h (shiftVec n) x y)) := by
    intro x
    unfold nativeDensity
    rw [ymDensity_eq_scaled D hh one_ne_zero, higgsDensity_eq_scaled D hh one_ne_zero,
      diracDensity_eq_scaled D hh one_ne_zero]
    simp only [mul_one, inv_one, one_pow, one_mul]
    ring
  simp only [hpt, gravityDensity_eq_curl D hh y _ (hlog _), sum_add_distrib]
  rw [sum_curl_eq D hh y hdet S]
  unfold firstJetDensity gravFirstJet collar
  simp only [sum_add_distrib, sum_sub_distrib, sum_neg_distrib, stencil_fst, shiftVec_none,
    add_zero, coframe]
  ring


/-! ### Regularity of `F_h^{(1)}` on the chart -/

/-- The nondegenerate chart in jet space: invertible coframes at all shifts of the stencil. -/
def JetChart (ξ : Jet (Field 𝔄 𝓗 𝓢)) : Prop := ∀ s : Shift, (ξ.1 s).1.det ≠ 0

theorem contDiffAt_jetOmegaShift (ν μ : Fin 4) {ξ : Jet (Field 𝔄 𝓗 𝓢)}
    (he : (ξ.1 (some (true, μ))).1.det ≠ 0) : ContDiffAt ℝ ∞ (jetOmegaShift ν μ) ξ := by
  unfold jetOmegaShift
  have h1 : ContDiffAt ℝ ∞ (fun ξ : Jet (Field 𝔄 𝓗 𝓢) =>
      ((ξ.1 (some (true, μ))).1, fun lam => (ξ.2 (some (true, μ), lam)).1)) ξ := by fun_prop
  refine contDiffAt_pi.mpr fun a => contDiffAt_pi.mpr fun b => ?_
  exact (contDiffAt_readerOmega_entry ν a b
    (q := ((ξ.1 (some (true, μ))).1, fun lam => (ξ.2 (some (true, μ), lam)).1)) he).comp ξ h1

@[fun_prop]
theorem contDiff_jetEm (μ : Fin 4) {k : WithTop ℕ∞} : ContDiff ℝ k (jetEm (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢) μ) := by
  unfold jetEm
  fun_prop

@[fun_prop]
theorem contDiff_jetPm (μ : Fin 4) {k : WithTop ℕ∞} : ContDiff ℝ k (jetPm (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢) μ) := by
  unfold jetPm
  fun_prop

/-- `Rem ∘ g` is smooth wherever `g` is smooth and its mesh coordinate vanishes. -/
theorem contDiffAt_remPlaquette_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {𝔅 : Type*} [NormedRing 𝔅] [NormedAlgebra ℝ 𝔅] [CompleteSpace 𝔅] [NormOneClass 𝔅]
    {g : E → ℝ × 𝔅 × 𝔅 × 𝔅 × 𝔅} {z : E} (hg : ContDiffAt ℝ ∞ g z) (h0 : (g z).1 = 0) :
    ContDiffAt ℝ ∞ (fun z => remPlaquette (g z)) z := by
  refine ContDiffAt.comp z (analyticAt_remPlaquette ?_).contDiffAt hg
  simp [h0]

theorem contDiffAt_remCartan (μ ν : Fin 4) {q : ℝ × Jet (Field 𝔄 𝓗 𝓢)} (hq : q.1 = 0)
    (hc : JetChart q.2) : ContDiffAt ℝ ∞ (remCartan μ ν) q := by
  have hΩ : ∀ μ, ContDiffAt ℝ ∞ (jetOmega μ) q.2 := fun μ => contDiffAt_jetOmega μ (hc none)
  have hΩs : ∀ ν μ, ContDiffAt ℝ ∞ (jetOmegaShift ν μ) q.2 := fun ν μ =>
    contDiffAt_jetOmegaShift ν μ (hc _)
  unfold remCartan
  refine contDiffAt_remPlaquette_comp ?_ hq
  simp only [← matToOpL_apply]
  fun_prop

/-- Composition form of the smoothness of `dqPal`. -/
@[fun_prop]
theorem ContDiffAt.dqPal {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (κ : ℝ)
    (μ ν a b : Fin 4) {f : E → ℝ} {g l : E → Mat} {x : E} (hf : ContDiffAt ℝ ∞ f x)
    (hg : ContDiffAt ℝ ∞ g x) (hl : ContDiffAt ℝ ∞ l x) (h0 : (g x).det ≠ 0)
    (h1 : (g x + f x • l x).det ≠ 0) :
    ContDiffAt ℝ ∞ (fun x => NativeDensity.dqPal κ (f x) (g x) (l x) μ ν a b) x := by
  have h := ContDiffAt.comp (g := fun q : ℝ × Mat × Mat => NativeDensity.dqPal κ q.1 q.2.1 q.2.2 μ ν a b)
    (f := fun x => (f x, g x, l x)) x (contDiffAt_dqPal κ μ ν a b (q := (f x, g x, l x)) h0 h1)
    (hf.prodMk (hg.prodMk hl))
  simp only [Function.comp_def] at h
  exact h

theorem contDiffAt_gravFirstJet {q : ℝ × Jet (Field 𝔄 𝓗 𝓢)} (hq : q.1 = 0) (hc : JetChart q.2) :
    ContDiffAt ℝ ∞ (gravFirstJet D) q := by
  have hR : ∀ μ ν, ContDiffAt ℝ ∞ (remCartan μ ν) q := fun μ ν => contDiffAt_remCartan μ ν hq hc
  have hΩ : ∀ ν, ContDiffAt ℝ ∞ (jetOmega ν) q.2 := fun ν => contDiffAt_jetOmega ν (hc none)
  have he0 : (q.2.1 none).1.det ≠ 0 := hc none
  have hEm : ∀ μ, (jetEm μ q.2).det ≠ 0 := fun μ => hc _
  have hseg : ∀ μ, (jetEm μ q.2 + q.1 • jetPm μ q.2).det ≠ 0 := by
    intro μ
    rw [hq, zero_smul, add_zero]
    exact hEm μ
  unfold gravFirstJet
  fun_prop (disch := solve_by_elim)

/-- **`lem:native-firstjet-normal-form`, regularity clause:** `F^{(1)}` is smooth in `(h, jet)` at
`h = 0` on the nondegenerate chart. -/
theorem contDiffAt_firstJetDensity {q : ℝ × Jet (Field 𝔄 𝓗 𝓢)} (hq : q.1 = 0) (hc : JetChart q.2) :
    ContDiffAt ℝ ∞ (firstJetDensity D) q := by
  have h1 := contDiffAt_gravFirstJet D hq hc
  have hproj : ContDiffAt ℝ ∞ (fun q : ℝ × Jet (Field 𝔄 𝓗 𝓢) => (q.1, (1 : ℝ), q.2)) q := by
    fun_prop
  have h2 := ContDiffAt.comp (g := normYM D)
    (f := fun q : ℝ × Jet (Field 𝔄 𝓗 𝓢) => (q.1, (1 : ℝ), q.2)) q
    (contDiffAt_normYM D (p := (q.1, 1, q.2)) hq (hc none)) hproj
  have h3 := ContDiffAt.comp (g := normHiggs D)
    (f := fun q : ℝ × Jet (Field 𝔄 𝓗 𝓢) => (q.1, (1 : ℝ), q.2)) q
    (contDiffAt_normHiggs D (p := (q.1, 1, q.2)) (hc none)) hproj
  have h4 := ContDiffAt.comp (g := normD D)
    (f := fun q : ℝ × Jet (Field 𝔄 𝓗 𝓢) => (q.1, (1 : ℝ), q.2)) q
    (contDiffAt_normD D (p := (q.1, 1, q.2)) (hc none)) hproj
  simp only [Function.comp_def] at h2 h3 h4
  show ContDiffAt ℝ ∞ (fun q : ℝ × Jet (Field 𝔄 𝓗 𝓢) => gravFirstJet D q + normYM D (q.1, 1, q.2) +
    normHiggs D (q.1, 1, q.2) + normD D (q.1, 1, q.2)) q
  refine ContDiffAt.add (ContDiffAt.add (ContDiffAt.add ?_ h2) h3) h4
  exact h1

/-- **`lem:native-firstjet-normal-form`, uniform bounds:** all fixed-order derivatives of `F^{(1)}`
in `(h, jet)` are bounded uniformly for `|h| ≤ h₀` and jets in a compact subset of the chart. -/
theorem exists_uniform_bound_firstJetDensity (k : ℕ) {K : Set (Jet (Field 𝔄 𝓗 𝓢))}
    (hK : IsCompact K) (hKc : ∀ ξ ∈ K, JetChart ξ) :
    ∃ h₀ > 0, ∃ C : ℝ, ∀ h : ℝ, |h| ≤ h₀ → ∀ ξ ∈ K,
      ContDiffAt ℝ k (firstJetDensity D) (h, ξ) ∧
        ‖iteratedFDeriv ℝ k (firstJetDensity D) (h, ξ)‖ ≤ C :=
  exists_uniform_bound_of_contDiffAt k hK fun ξ hξ =>
    (contDiffAt_firstJetDensity D (q := (0, ξ)) rfl (hKc ξ hξ)).of_le (by exact_mod_cast le_top)

/-! ### `lem:native-action-Hessian`: the uniform upper Hessian scale of the local action -/

section HessianTools

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G]
  [NormedSpace ℝ G]

/-- Chain rule for the iterated derivative of a composition with a continuous linear map, under
a local smoothness hypothesis. -/
theorem iteratedFDeriv_comp_clm_of_contDiffAt {F : E → ℝ} (L : G →L[ℝ] E) {x : G}
    {m : WithTop ℕ∞} (hF : ContDiffAt ℝ m F (L x)) (k : ℕ) (hk : (k : WithTop ℕ∞) ≤ m)
    (hm : m ≠ ∞) :
    iteratedFDeriv ℝ k (F ∘ L) x =
      (iteratedFDeriv ℝ k F (L x)).compContinuousLinearMap fun _ => L := by
  have hF' : ContDiffWithinAt ℝ m F Set.univ (L x) := hF.contDiffWithinAt
  obtain ⟨u, hu, hFu⟩ := (contDiffWithinAt_iff_contDiffOn_nhds hm).mp hF'
  rw [Set.insert_eq_of_mem (Set.mem_univ _), nhdsWithin_univ] at hu
  obtain ⟨t, htu, hto, hxt⟩ := mem_nhds_iff.mp hu
  have hFt : ContDiffOn ℝ m F t := hFu.mono htu
  have hxt' : x ∈ L ⁻¹' t := hxt
  rw [← iteratedFDerivWithin_of_isOpen k hto hxt,
    ← iteratedFDerivWithin_of_isOpen k (hto.preimage L.continuous) hxt']
  exact L.iteratedFDerivWithin_comp_right hFt hto.uniqueDiffOn
    (hto.preimage L.continuous).uniqueDiffOn hxt hk

/-- The derivative in the jet variable of `f(h, ·)` is bounded by the joint derivative. -/
theorem norm_iteratedFDeriv_partial_le {f : ℝ × E → ℝ} {h : ℝ} {ξ : E} (k : ℕ)
    (hf : ContDiffAt ℝ k f (h, ξ)) :
    ‖iteratedFDeriv ℝ k (fun ξ => f (h, ξ)) ξ‖ ≤ ‖iteratedFDeriv ℝ k f (h, ξ)‖ := by
  set L : E →L[ℝ] ℝ × E := ContinuousLinearMap.inr ℝ ℝ E with hL
  have heq : (fun ξ => f (h, ξ)) = (fun p : ℝ × E => f ((h, 0) + p)) ∘ L := by
    funext ξ
    simp [hL]
  have hshift : ContDiffAt ℝ k (fun p : ℝ × E => f ((h, 0) + p)) (L ξ) := by
    have : L ξ = (0, ξ) := by simp [hL]
    rw [this]
    have hf' : ContDiffAt ℝ k f ((h, 0) + (0, ξ)) := by simpa using hf
    exact hf'.comp (0, ξ) (contDiffAt_const.add contDiffAt_id)
  rw [heq, iteratedFDeriv_comp_clm_of_contDiffAt L hshift k le_rfl (by exact_mod_cast ENat.coe_ne_top k),
    iteratedFDeriv_comp_add_left]
  have hLξ : ((h, 0) + L ξ : ℝ × E) = (h, ξ) := by simp [hL]
  rw [hLξ]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hprod : ∏ _i : Fin k, ‖L‖ ≤ 1 :=
    Finset.prod_le_one (fun _ _ => norm_nonneg _) fun _ _ => ContinuousLinearMap.norm_inr_le_one ℝ ℝ E
  calc ‖iteratedFDeriv ℝ k f (h, ξ)‖ * ∏ _i : Fin k, ‖L‖
      ≤ ‖iteratedFDeriv ℝ k f (h, ξ)‖ * 1 := by gcongr
    _ = ‖iteratedFDeriv ℝ k f (h, ξ)‖ := mul_one _

end HessianTools

namespace ShiftedJetActionLocal

open ShiftedJetAction

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {ι : Type*} [Fintype ι]
variable {F : (ι → V) × (ι × Fin 4 → V) → ℝ} {h : ℝ} {σ : ι → Grid n}

/-- The chain rule `D²𝒜_h(y)[u,v] = h⁴ Σ_x D²F(Ξ_x y)[Ξ_x u, Ξ_x v]` under local smoothness of the
density along the record. -/
theorem iteratedFDeriv_action_of_contDiffAt {y : Grid n → V}
    (hF : ∀ x, ContDiffAt ℝ 2 F (stencil h σ x y)) (u v : Grid n → V) :
    iteratedFDeriv ℝ 2 (action F h σ) y ![u, v] =
      h ^ 4 * ∑ x, iteratedFDeriv ℝ 2 F (stencil h σ x y)
        ![stencil h σ x u, stencil h σ x v] := by
  have hcomp : ∀ x, ContDiffAt ℝ 2 (fun y : Grid n → V => F (stencil h σ x y)) y := by
    intro x
    have := ContDiffAt.comp (g := F) (f := stencil h σ x) y (hF x)
      (stencil_contDiff h σ x).contDiffAt
    simpa only [Function.comp_def] using this
  have hsum : ContDiffAt ℝ 2 (fun y : Grid n → V => ∑ x, F (stencil h σ x y)) y :=
    ContDiffAt.sum fun x _ => hcomp x
  have e1 : action F h σ = fun y => (h ^ 4) • (∑ x, F (stencil h σ x y)) := by
    funext y
    simp [action]
  rw [e1, iteratedFDeriv_const_smul_apply' hsum, ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  congr 1
  have hcomp' : ∀ x, ContDiffAt ℝ 2 (F ∘ stencil h σ x) y := fun x =>
    ContDiffAt.comp y (hF x) (stencil_contDiff h σ x).contDiffAt
  have e3 : iteratedFDeriv ℝ 2 (fun y : Grid n → V => ∑ x, F (stencil h σ x y)) y =
      ∑ x, iteratedFDeriv ℝ 2 (F ∘ stencil h σ x) y := by
    have := iteratedFDeriv_fun_sum_apply (𝕜 := ℝ) (f := fun x => F ∘ stencil h σ x) (u := univ)
      (n := 2) (x := y) (fun x _ => hcomp' x)
    exact this
  rw [e3, ContinuousMultilinearMap.sum_apply]
  refine sum_congr rfl fun x _ => ?_
  have hcl := iteratedFDeriv_comp_clm_of_contDiffAt (stencil h σ x) (m := 2) (x := y) (hF x) 2
    (by norm_num) (by simp)
  rw [hcl, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

/-- `eq:action-Hessian-bilinear` under local smoothness of the density along the record. -/
theorem abs_iteratedFDeriv_action_le_of_contDiffAt (hh : h ≠ 0) {y : Grid n → V}
    (hF : ∀ x, ContDiffAt ℝ 2 F (stencil h σ x y))
    {M : ℝ} (hM : ∀ x, ‖iteratedFDeriv ℝ 2 F (stencil h σ x y)‖ ≤ M) (u v : Grid n → V) :
    |iteratedFDeriv ℝ 2 (action F h σ) y ![u, v]| ≤
      M * Fintype.card ι * (Real.sqrt (firstNormSq h u) * Real.sqrt (firstNormSq h v)) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  rw [iteratedFDeriv_action_of_contDiffAt hF]
  have hterm : ∀ x, |iteratedFDeriv ℝ 2 F (stencil h σ x y)
      ![stencil h σ x u, stencil h σ x v]| ≤ M * (‖stencil h σ x u‖ * ‖stencil h σ x v‖) := by
    intro x
    rw [← Real.norm_eq_abs]
    calc ‖iteratedFDeriv ℝ 2 F (stencil h σ x y) ![stencil h σ x u, stencil h σ x v]‖
        ≤ ‖iteratedFDeriv ℝ 2 F (stencil h σ x y)‖ *
          ∏ i, ‖(![stencil h σ x u, stencil h σ x v] : Fin 2 → _) i‖ :=
          ContinuousMultilinearMap.le_opNorm _ _
      _ = ‖iteratedFDeriv ℝ 2 F (stencil h σ x y)‖ *
          (‖stencil h σ x u‖ * ‖stencil h σ x v‖) := by
          simp [Fin.prod_univ_two]
      _ ≤ M * (‖stencil h σ x u‖ * ‖stencil h σ x v‖) := by
          gcongr
          exact hM x
  have hcs : ∑ x, ‖stencil h σ x u‖ * ‖stencil h σ x v‖ ≤
      Real.sqrt (∑ x, stencilSq h σ x u) * Real.sqrt (∑ x, stencilSq h σ x v) := by
    refine (Real.sum_mul_le_sqrt_mul_sqrt _ _ _).trans ?_
    gcongr with x _ x _
    · exact (le_of_eq rfl).trans
        (by rw [← Real.le_sqrt (norm_nonneg _) (stencilSq_nonneg h σ x u)]
            exact norm_stencil_le h σ x u)
    · rw [← Real.le_sqrt (norm_nonneg _) (stencilSq_nonneg h σ x v)]
      exact norm_stencil_le h σ x v
  have hkey : h ^ 4 * (Real.sqrt ((Fintype.card ι : ℝ) * (h ^ 4)⁻¹) *
      Real.sqrt ((Fintype.card ι : ℝ) * (h ^ 4)⁻¹)) = Fintype.card ι := by
    rw [Real.mul_self_sqrt (by positivity)]
    field_simp
  calc |h ^ 4 * ∑ x, iteratedFDeriv ℝ 2 F (stencil h σ x y)
        ![stencil h σ x u, stencil h σ x v]|
      = h ^ 4 * |∑ x, iteratedFDeriv ℝ 2 F (stencil h σ x y)
        ![stencil h σ x u, stencil h σ x v]| := by
        rw [abs_mul, abs_of_nonneg (by positivity)]
    _ ≤ h ^ 4 * ∑ x, |iteratedFDeriv ℝ 2 F (stencil h σ x y)
        ![stencil h σ x u, stencil h σ x v]| := by
        gcongr
        exact abs_sum_le_sum_abs _ _
    _ ≤ h ^ 4 * ∑ x, M * (‖stencil h σ x u‖ * ‖stencil h σ x v‖) := by
        gcongr with x _
        exact hterm x
    _ = h ^ 4 * M * ∑ x, ‖stencil h σ x u‖ * ‖stencil h σ x v‖ := by
        rw [← mul_sum]
        ring
    _ ≤ h ^ 4 * M * (Real.sqrt (∑ x, stencilSq h σ x u) *
        Real.sqrt (∑ x, stencilSq h σ x v)) := by
        gcongr
    _ = M * Fintype.card ι * (Real.sqrt (firstNormSq h u) * Real.sqrt (firstNormSq h v)) := by
        rw [sum_stencilSq hh, sum_stencilSq hh,
          Real.sqrt_mul (x := (Fintype.card ι : ℝ) * (h ^ 4)⁻¹) (by positivity),
          Real.sqrt_mul (x := (Fintype.card ι : ℝ) * (h ^ 4)⁻¹) (by positivity)]
        linear_combination
          (M * Real.sqrt (firstNormSq h u) * Real.sqrt (firstNormSq h v)) * hkey

/-- `eq:action-Hessian-scale` under local smoothness of the density along the record. -/
theorem abs_iteratedFDeriv_action_le_mass_of_contDiffAt (hh : 0 < h) (hh1 : h ≤ 1)
    {y : Grid n → V} (hF : ∀ x, ContDiffAt ℝ 2 F (stencil h σ x y))
    {M : ℝ} (hM : ∀ x, ‖iteratedFDeriv ℝ 2 F (stencil h σ x y)‖ ≤ M) (u v : Grid n → V) :
    |iteratedFDeriv ℝ 2 (action F h σ) y ![u, v]| ≤
      (17 * M * Fintype.card ι) * h⁻¹ ^ 2 *
        (Real.sqrt (massNormSq h u) * Real.sqrt (massNormSq h v)) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  refine (abs_iteratedFDeriv_action_le_of_contDiffAt hh.ne' hF hM u v).trans ?_
  have hsq : ∀ w : Grid n → V, Real.sqrt (firstNormSq h w) ≤
      Real.sqrt 17 * h⁻¹ * Real.sqrt (massNormSq h w) := by
    intro w
    have hinv : 0 ≤ h⁻¹ := by positivity
    rw [← Real.sqrt_sq hinv, ← Real.sqrt_mul (by norm_num), ← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt (firstNormSq_le hh hh1 w)
  have h17 : Real.sqrt 17 * Real.sqrt 17 = 17 := Real.mul_self_sqrt (by norm_num)
  calc M * Fintype.card ι * (Real.sqrt (firstNormSq h u) * Real.sqrt (firstNormSq h v))
      ≤ M * Fintype.card ι * ((Real.sqrt 17 * h⁻¹ * Real.sqrt (massNormSq h u)) *
          (Real.sqrt 17 * h⁻¹ * Real.sqrt (massNormSq h v))) := by
        gcongr
        · exact hsq u
        · exact hsq v
    _ = (17 * M * Fintype.card ι) * h⁻¹ ^ 2 *
        (Real.sqrt (massNormSq h u) * Real.sqrt (massNormSq h v)) := by
        linear_combination (M * Fintype.card ι * h⁻¹ ^ 2 * Real.sqrt (massNormSq h u) *
          Real.sqrt (massNormSq h v)) * h17

end ShiftedJetActionLocal


/-! ### The Hessian bounds for the local action on the chart -/

/-- `ω_{μ,h}(z)` as a function of the record. -/
noncomputable def omegaAt (h : ℝ) (z : Grid n) (μ : Fin 4) (y : Grid n → Field 𝔄 𝓗 𝓢) : Mat :=
  omegaLink h (coframe y) z μ

theorem continuousAt_omegaAt (h : ℝ) (z : Grid n) (μ : Fin 4) {y : Grid n → Field 𝔄 𝓗 𝓢}
    (hy : (coframe y z).det ≠ 0) : ContinuousAt (omegaAt h z μ) y := by
  unfold omegaAt omegaLink
  have h1 : ContDiffAt ℝ ∞ (fun y : Grid n → Field 𝔄 𝓗 𝓢 =>
      (coframe y z, fun lam => fwdDiff h lam (coframe y) z)) y := by
    unfold coframe ShiftedJetAction.fwdDiff
    fun_prop
  have h2 : ContDiffAt ℝ ∞ (fun y : Grid n → Field 𝔄 𝓗 𝓢 =>
      readerOmega (coframe y z) (fun lam => fwdDiff h lam (coframe y) z) μ) y := by
    refine contDiffAt_pi.mpr fun a => contDiffAt_pi.mpr fun b => ?_
    exact (contDiffAt_readerOmega_entry μ a b
      (q := (coframe y z, fun lam => fwdDiff h lam (coframe y) z)) hy).comp y h1
  exact h2.continuousAt

theorem cartanPlaquette_eq_omegaAt (h : ℝ) (y : Grid n → Field 𝔄 𝓗 𝓢) (x : Grid n) (μ ν : Fin 4) :
    cartanPlaquette h (coframe y) x μ ν =
      exp (h • matToOpL (omegaAt h x μ y)) * exp (h • matToOpL (omegaAt h (x + unitVec n μ) ν y)) *
        exp (-(h • matToOpL (omegaAt h (x + unitVec n ν) μ y))) *
        exp (-(h • matToOpL (omegaAt h x ν y))) := rfl

theorem continuousAt_cartanPlaquette (h : ℝ) (x : Grid n) (μ ν : Fin 4) {y : Grid n → Field 𝔄 𝓗 𝓢}
    (hy : ∀ z, (coframe y z).det ≠ 0) :
    ContinuousAt (fun y => cartanPlaquette h (coframe y) x μ ν) y := by
  simp only [cartanPlaquette_eq_omegaAt]
  have hω : ∀ z μ, ContinuousAt (omegaAt h z μ) y := fun z μ => continuousAt_omegaAt h z μ (hy z)
  have hexp : Continuous (exp : Op → Op) :=
    continuous_iff_continuousAt.mpr fun x => (exp_analytic (𝕂 := ℝ) x).continuousAt
  fun_prop

/-- The chart conditions are open in the record. -/
theorem eventually_chart (h : ℝ) {y : Grid n → Field 𝔄 𝓗 𝓢} (hdet : ∀ x, 0 < (coframe y x).det)
    (hlog : ∀ x μ ν, ‖cartanPlaquette h (coframe y) x μ ν - 1‖ < 1) :
    ∀ᶠ y' in 𝓝 y, (∀ x, 0 < (coframe y' x).det) ∧
      ∀ x μ ν, ‖cartanPlaquette h (coframe y') x μ ν - 1‖ < 1 := by
  have hdet' : ∀ᶠ y' in 𝓝 y, ∀ x, 0 < (coframe y' x).det := by
    rw [Filter.eventually_all]
    intro x
    have hc : ContinuousAt (fun y' : Grid n → Field 𝔄 𝓗 𝓢 => (coframe y' x).det) y := by
      unfold coframe
      exact ((contDiff_det (k := 1)).continuous.comp (continuous_apply x).fst).continuousAt
    exact continuousAt_const.eventually_lt hc (hdet x)
  have hlog' : ∀ᶠ y' in 𝓝 y, ∀ x μ ν, ‖cartanPlaquette h (coframe y') x μ ν - 1‖ < 1 := by
    rw [Filter.eventually_all]
    intro x
    rw [Filter.eventually_all]
    intro μ
    rw [Filter.eventually_all]
    intro ν
    have hc : ContinuousAt (fun y' : Grid n → Field 𝔄 𝓗 𝓢 =>
        ‖cartanPlaquette h (coframe y') x μ ν - 1‖) y :=
      ((continuousAt_cartanPlaquette h x μ ν fun z => (hdet z).ne').sub continuousAt_const).norm
    exact hc.eventually_lt continuousAt_const (hlog x μ ν)
  exact hdet'.and hlog'

/-- On the chart, the local action coincides near `y` with the shifted-first-jet action. -/
theorem localAction_eventuallyEq {h : ℝ} (hh : h ≠ 0) {y : Grid n → Field 𝔄 𝓗 𝓢}
    (hdet : ∀ x, 0 < (coframe y x).det)
    (hlog : ∀ x μ ν, ‖cartanPlaquette h (coframe y) x μ ν - 1‖ < 1) :
    localAction D h =ᶠ[𝓝 y]
      ShiftedJetAction.action (fun ξ => firstJetDensity D (h, ξ)) h (shiftVec n) := by
  filter_upwards [eventually_chart h hdet hlog] with y' hy'
  exact localAction_eq_action_firstJetDensity D hh y' hy'.1 hy'.2

/-- **`lem:native-action-Hessian`** (`eq:action-Hessian-bilinear`, `eq:action-Hessian-scale`,
`eq:action-span`): for every compact set `K` of shifted first jets inside the nondegenerate chart
there are `h₀ > 0` and constants `C₁, K₀, D₀`, independent of `h ≤ h₀` and of the number of nodes,
such that for every record `y` on the oriented logarithm chart whose stencils lie in `K`,
`|D²S_h^{loc}(y)[u,v]| ≤ C₁ ‖u‖_{1,h} ‖v‖_{1,h}`,
`|D²S_h^{loc}(y)[u,v]| ≤ K₀ h⁻² ‖u‖_{0,h} ‖v‖_{0,h}`, and the oscillation of `S_h^{loc}` over such
records is at most `D₀ · (h⁴ n⁴)`, the fixed `h⁴ × (number of cells)` volume factor. -/
theorem exists_hessian_bounds {K : Set (Jet (Field 𝔄 𝓗 𝓢))} (hK : IsCompact K)
    (hKc : ∀ ξ ∈ K, JetChart ξ) :
    ∃ h₀ > 0, ∃ C₁ K₀ D₀ : ℝ, ∀ h : ℝ, 0 < h → h ≤ h₀ →
      ∀ y : Grid n → Field 𝔄 𝓗 𝓢, (∀ x, stencil h (shiftVec n) x y ∈ K) →
        (∀ x, 0 < (coframe y x).det) →
        (∀ x μ ν, ‖cartanPlaquette h (coframe y) x μ ν - 1‖ < 1) →
        (∀ u v, |iteratedFDeriv ℝ 2 (localAction D h) y ![u, v]| ≤
          C₁ * (Real.sqrt (ShiftedJetAction.firstNormSq h u) *
            Real.sqrt (ShiftedJetAction.firstNormSq h v))) ∧
        (∀ u v, |iteratedFDeriv ℝ 2 (localAction D h) y ![u, v]| ≤
          K₀ * h⁻¹ ^ 2 * (Real.sqrt (ShiftedJetAction.massNormSq h u) *
            Real.sqrt (ShiftedJetAction.massNormSq h v))) ∧
        (∀ y' : Grid n → Field 𝔄 𝓗 𝓢, (∀ x, stencil h (shiftVec n) x y' ∈ K) →
          (∀ x, 0 < (coframe y' x).det) →
          (∀ x μ ν, ‖cartanPlaquette h (coframe y') x μ ν - 1‖ < 1) →
          |localAction D h y - localAction D h y'| ≤ D₀ * (h ^ 4 * (n : ℝ) ^ 4)) := by
  obtain ⟨h₂, hh₂, C₂, hC₂⟩ := exists_uniform_bound_firstJetDensity D 2 hK hKc
  obtain ⟨h₃, hh₃, C₀, hC₀⟩ := exists_uniform_bound_firstJetDensity D 0 hK hKc
  refine ⟨min (min h₂ h₃) 1, by positivity, C₂ * Fintype.card Shift,
    17 * C₂ * Fintype.card Shift, 2 * C₀, ?_⟩
  intro h hh hh0 y hyK hdet hlog
  have hh2 : |h| ≤ h₂ := by
    rw [abs_of_pos hh]
    exact hh0.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hh3 : |h| ≤ h₃ := by
    rw [abs_of_pos hh]
    exact hh0.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hh1 : h ≤ 1 := hh0.trans (min_le_right _ _)
  set F : Jet (Field 𝔄 𝓗 𝓢) → ℝ := fun ξ => firstJetDensity D (h, ξ) with hF
  have hFsm : ∀ x, ContDiffAt ℝ 2 F (stencil h (shiftVec n) x y) := by
    intro x
    have h1 := (hC₂ h hh2 _ (hyK x)).1
    have h2 : ContDiffAt ℝ 2 (fun ξ : Jet (Field 𝔄 𝓗 𝓢) => ((h, ξ) : ℝ × Jet (Field 𝔄 𝓗 𝓢)))
        (stencil h (shiftVec n) x y) := by fun_prop
    have := ContDiffAt.comp (g := firstJetDensity D)
      (f := fun ξ : Jet (Field 𝔄 𝓗 𝓢) => ((h, ξ) : ℝ × Jet (Field 𝔄 𝓗 𝓢))) _ h1 h2
    simpa only [Function.comp_def, hF, Nat.cast_ofNat] using this
  have hM : ∀ x, ‖iteratedFDeriv ℝ 2 F (stencil h (shiftVec n) x y)‖ ≤ C₂ := fun x =>
    (norm_iteratedFDeriv_partial_le 2 (hC₂ h hh2 _ (hyK x)).1).trans (hC₂ h hh2 _ (hyK x)).2
  have hiter : iteratedFDeriv ℝ 2 (localAction D h) y =
      iteratedFDeriv ℝ 2 (ShiftedJetAction.action F h (shiftVec n)) y :=
    ((localAction_eventuallyEq D hh.ne' hdet hlog).iteratedFDeriv ℝ 2).eq_of_nhds
  refine ⟨fun u v => ?_, fun u v => ?_, fun y' hyK' hdet' hlog' => ?_⟩
  · rw [hiter]
    exact ShiftedJetActionLocal.abs_iteratedFDeriv_action_le_of_contDiffAt hh.ne' hFsm hM u v
  · rw [hiter]
    exact ShiftedJetActionLocal.abs_iteratedFDeriv_action_le_mass_of_contDiffAt hh hh1 hFsm hM u v
  · rw [localAction_eq_action_firstJetDensity D hh.ne' y hdet hlog,
      localAction_eq_action_firstJetDensity D hh.ne' y' hdet' hlog']
    have hB : ∀ (z : Grid n → Field 𝔄 𝓗 𝓢), (∀ x, stencil h (shiftVec n) x z ∈ K) →
        ∀ x, |F (stencil h (shiftVec n) x z)| ≤ C₀ := by
      intro z hz x
      have := (hC₀ h hh3 _ (hz x)).2
      rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
    exact ShiftedJetAction.abs_action_sub_le (hB y hyK) (hB y' hyK')

/-- The collar functional only involves the two boundary layers `S \ (S - e_μ)` and
`(S - e_μ) \ S` of the box (the "fixed collars"): the contributions of the common interior cancel
exactly. -/
theorem collar_eq_layers (h : ℝ) (y : Grid n → Field 𝔄 𝓗 𝓢) (S : Finset (Grid n)) :
    collar D h y S = h ^ 4 * ∑ μ, ∑ ν, ∑ a, ∑ b, h⁻¹ *
      (∑ x ∈ S \ S.map (Equiv.subRight (unitVec n μ)).toEmbedding,
          palA D.κ (coframe y x) μ ν a b * omegaLink h (coframe y) (x + unitVec n μ) ν a b -
        ∑ x ∈ S.map (Equiv.subRight (unitVec n μ)).toEmbedding \ S,
          palA D.κ (coframe y x) μ ν a b * omegaLink h (coframe y) (x + unitVec n μ) ν a b) := by
  unfold collar
  simp only [Finset.sum_sdiff_sub_sum_sdiff]

/-- `lem:native-firstjet-normal-form`, variational clause: on the chart the interior Euler covector
of the local action is exactly that of the shifted-first-jet bulk representative. -/
theorem fderiv_localAction_eq {h : ℝ} (hh : h ≠ 0) {y : Grid n → Field 𝔄 𝓗 𝓢}
    (hdet : ∀ x, 0 < (coframe y x).det)
    (hlog : ∀ x μ ν, ‖cartanPlaquette h (coframe y) x μ ν - 1‖ < 1) :
    fderiv ℝ (localAction D h) y =
      fderiv ℝ (ShiftedJetAction.action (fun ξ => firstJetDensity D (h, ξ)) h (shiftVec n)) y :=
  (localAction_eventuallyEq D hh hdet hlog).fderiv_eq

/-- All mixed physical derivatives of the local action agree with those of the bulk
representative on the chart. -/
theorem iteratedFDeriv_localAction_eq {h : ℝ} (hh : h ≠ 0) {y : Grid n → Field 𝔄 𝓗 𝓢}
    (hdet : ∀ x, 0 < (coframe y x).det)
    (hlog : ∀ x μ ν, ‖cartanPlaquette h (coframe y) x μ ν - 1‖ < 1) (k : ℕ) :
    iteratedFDeriv ℝ k (localAction D h) y =
      iteratedFDeriv ℝ k (ShiftedJetAction.action (fun ξ => firstJetDensity D (h, ξ)) h
        (shiftVec n)) y :=
  ((localAction_eventuallyEq D hh hdet hlog).iteratedFDeriv ℝ k).eq_of_nhds

end NativeDensity

end RenewalGeometry
