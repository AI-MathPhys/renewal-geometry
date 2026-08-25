/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The complete leading-ray equation

Machinery for `thm:SM-localizer-jets` (RG.3i).  For a marginal graph
`z(s) = s r + s² z₂ + o(s²)` and a gauge step `γ(s) = s + β s² + o(s²)` satisfying the reduced
marginal recurrence

`z(γ(s)) = z(s) + s² b + Q(z(s), z(s)) - s K₁ z(s) + o(s²)`,

matching the `s²` coefficients forces the complete leading equation

`b + Q(r, r) - K₁ r - β r = 0` (`leading_ray_eq`).

The second jet contributes only at the next order and cannot repair a failed leading follower
condition, exactly as stated in the manuscript.
-/

open Asymptotics Filter
open scoped Topology

namespace NCG
namespace LeadingRay

/-! ### Small-order helpers -/

theorem abs_le_one_eventually : ∀ᶠ s : ℝ in 𝓝 0, |s| ≤ 1 := by
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with s hs
  rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hs
  exact hs.le

theorem sq_isBigO_id : (fun s : ℝ => s ^ 2) =O[𝓝 0] fun s : ℝ => s := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [abs_le_one_eventually] with s hs
  rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, pow_two, abs_mul]
  exact mul_le_of_le_one_left (abs_nonneg s) hs

theorem sq_mul_id_isLittleO_sq : (fun s : ℝ => s ^ 2 * s) =o[𝓝 0] fun s : ℝ => s ^ 2 := by
  rw [isLittleO_iff]
  intro ε hε
  have hball : ∀ᶠ s : ℝ in 𝓝 0, |s| ≤ ε := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hε] with s hs
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hs
    exact hs.le
  filter_upwards [hball] with s hs
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
  calc |s ^ 2| * |s| ≤ |s ^ 2| * ε := mul_le_mul_of_nonneg_left hs (abs_nonneg _)
    _ = ε * |s ^ 2| := mul_comm _ _

theorem id_mul_sq_isLittleO_sq : (fun s : ℝ => s * s ^ 2) =o[𝓝 0] fun s : ℝ => s ^ 2 := by
  have h := sq_mul_id_isLittleO_sq
  refine h.congr' ?_ (by rfl)
  filter_upwards with s
  ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem id_smul_const_isBigO (v : E) :
    (fun s : ℝ => s • v) =O[𝓝 0] fun s : ℝ => s := by
  refine IsBigO.of_bound ‖v‖ ?_
  filter_upwards with s
  rw [norm_smul, mul_comm]

theorem sq_smul_const_isBigO (v : E) :
    (fun s : ℝ => s ^ 2 • v) =O[𝓝 0] fun s : ℝ => s ^ 2 := by
  refine IsBigO.of_bound ‖v‖ ?_
  filter_upwards with s
  rw [norm_smul, mul_comm]

theorem smul_isBigO {w : ℝ → E} {g : ℝ → ℝ} (h : w =O[𝓝 0] g) :
    (fun s => s • w s) =O[𝓝 0] fun s => s * g s := by
  obtain ⟨C, hC⟩ := h.isBigOWith
  refine IsBigO.of_bound C ?_
  filter_upwards [hC.bound] with s hs
  rw [norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
  calc |s| * ‖w s‖ ≤ |s| * (C * ‖g s‖) := by
        exact mul_le_mul_of_nonneg_left hs (abs_nonneg s)
    _ = C * (|s| * |g s|) := by rw [Real.norm_eq_abs]; ring

theorem smul_const_of_isLittleO {c : ℝ → ℝ} {g : ℝ → ℝ} (h : c =o[𝓝 0] g) (v : E) :
    (fun s => c s • v) =o[𝓝 0] g := by
  rw [isLittleO_iff]
  intro ε hε
  have hpos : 0 < ε / (‖v‖ + 1) := by positivity
  filter_upwards [(isLittleO_iff.mp h) hpos] with s hs
  rw [norm_smul]
  calc ‖c s‖ * ‖v‖ ≤ (ε / (‖v‖ + 1) * ‖g s‖) * ‖v‖ :=
        mul_le_mul_of_nonneg_right hs (norm_nonneg v)
    _ ≤ ε * ‖g s‖ := by
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        have h1 : 0 ≤ ε * ‖g s‖ := by positivity
        nlinarith [norm_nonneg v, norm_nonneg (g s)]

theorem smul_const_of_isBigO {c : ℝ → ℝ} {g : ℝ → ℝ} (h : c =O[𝓝 0] g) (v : E) :
    (fun s => c s • v) =O[𝓝 0] g := by
  obtain ⟨C, hC⟩ := h.isBigOWith
  refine IsBigO.of_bound (C * ‖v‖) ?_
  filter_upwards [hC.bound] with s hs
  rw [norm_smul]
  calc ‖c s‖ * ‖v‖ ≤ (C * ‖g s‖) * ‖v‖ := mul_le_mul_of_nonneg_right hs (norm_nonneg v)
    _ = C * ‖v‖ * ‖g s‖ := by ring

/-- Uniqueness of second-order coefficients: `s² • v = o(s²)` forces `v = 0`. -/
theorem eq_zero_of_sq_smul_isLittleO {v : E}
    (h : (fun s : ℝ => s ^ 2 • v) =o[𝓝 0] fun s : ℝ => s ^ 2) : v = 0 := by
  by_contra hv
  have hnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have h2 := (isLittleO_iff.mp h) (show 0 < ‖v‖ / 2 by positivity)
  rw [Metric.eventually_nhds_iff] at h2
  obtain ⟨δ, hδ, hδ'⟩ := h2
  have hslt : dist (δ / 2) (0 : ℝ) < δ := by
    rw [dist_zero_right, Real.norm_eq_abs, abs_of_pos (by positivity)]
    linarith
  have h3 := hδ' hslt
  rw [norm_smul, Real.norm_eq_abs] at h3
  have hspos : 0 < |(δ / 2 : ℝ) ^ 2| := by positivity
  nlinarith [h3, hspos]

/-! ### The leading-ray equation -/

/-- **(RG.3i)**: the complete leading equation.  For a marginal graph
`z(s) = s r + s² z₂ + o(s²)`, a gauge step `γ(s) = s + β s² + o(s²)`, and the reduced marginal
recurrence `z(γ(s)) = z(s) + s² b + Q(z s)(z s) - s K₁ (z s) + o(s²)`, one has
`b + Q(r,r) - K₁ r - β r = 0`. -/
theorem leading_ray_eq (Q : E →L[ℝ] E →L[ℝ] E) (K₁ : E →L[ℝ] E) (z : ℝ → E) (γ : ℝ → ℝ)
    (r z₂ b : E) (β : ℝ)
    (hz : (fun s => z s - s • r - s ^ 2 • z₂) =o[𝓝 0] fun s : ℝ => s ^ 2)
    (hγ : (fun s => γ s - s - β * s ^ 2) =o[𝓝 0] fun s : ℝ => s ^ 2)
    (hrec : (fun s => z (γ s) - (z s + s ^ 2 • b + Q (z s) (z s) - s • K₁ (z s)))
      =o[𝓝 0] fun s : ℝ => s ^ 2) :
    b + Q r r - K₁ r - β • r = 0 := by
  classical
  set e : ℝ → E := fun s => z s - s • r - s ^ 2 • z₂ with he
  -- gauge-step asymptotics
  have hβsq : (fun s : ℝ => β * s ^ 2) =O[𝓝 0] fun s : ℝ => s ^ 2 :=
    (isBigO_refl (fun s : ℝ => s ^ 2) (𝓝 0)).const_mul_left β
  have hγd : (fun s => γ s - s) =O[𝓝 0] fun s : ℝ => s ^ 2 := by
    have h1 := hγ.isBigO.add hβsq
    refine h1.congr' ?_ (by rfl)
    filter_upwards with s
    ring
  have hγO : γ =O[𝓝 0] fun s : ℝ => s := by
    have h1 := (hγd.trans sq_isBigO_id).add (isBigO_refl (fun s : ℝ => s) (𝓝 0))
    refine h1.congr' ?_ (by rfl)
    filter_upwards with s
    ring
  have hγ0 : Tendsto γ (𝓝 0) (𝓝 0) := by
    have h0 : Tendsto (fun s : ℝ => s) (𝓝 (0 : ℝ)) (𝓝 0) := tendsto_id
    exact hγO.trans_tendsto h0
  have hγsq : (fun s => γ s ^ 2) =O[𝓝 0] fun s : ℝ => s ^ 2 := by
    have h1 := hγO.mul hγO
    refine h1.congr' (by filter_upwards with s; ring) (by filter_upwards with s; ring)
  -- graph asymptotics
  have hw : (fun s => z s - s • r) =O[𝓝 0] fun s : ℝ => s ^ 2 := by
    have h1 := hz.isBigO.add (sq_smul_const_isBigO z₂)
    refine h1.congr' ?_ (by rfl)
    filter_upwards with s
    simp [he]
  have hzO : z =O[𝓝 0] fun s : ℝ => s := by
    have h1 := (hw.trans sq_isBigO_id).add (id_smul_const_isBigO r)
    refine h1.congr' ?_ (by rfl)
    filter_upwards with s
    abel
  -- the six error terms
  have hE1 : (fun s => (γ s - s - β * s ^ 2) • r) =o[𝓝 0] fun s : ℝ => s ^ 2 :=
    smul_const_of_isLittleO hγ r
  have hE2 : (fun s => (γ s ^ 2 - s ^ 2) • z₂) =o[𝓝 0] fun s : ℝ => s ^ 2 := by
    have hdiff : (fun s => γ s ^ 2 - s ^ 2) =O[𝓝 0] fun s : ℝ => s ^ 2 * s := by
      have hadd : (fun s => γ s + s) =O[𝓝 0] fun s : ℝ => s :=
        hγO.add (isBigO_refl (fun s : ℝ => s) (𝓝 0))
      have h1 : (fun s => (γ s - s) * (γ s + s)) =O[𝓝 0] fun s : ℝ => s ^ 2 * s :=
        hγd.mul hadd
      refine h1.congr' ?_ (by rfl)
      filter_upwards with s
      ring
    exact (smul_const_of_isBigO hdiff z₂).trans_isLittleO sq_mul_id_isLittleO_sq
  have hE3 : (fun s => e (γ s)) =o[𝓝 0] fun s : ℝ => s ^ 2 :=
    (hz.comp_tendsto hγ0).trans_isBigO hγsq
  have hE4 : e =o[𝓝 0] fun s : ℝ => s ^ 2 := hz
  have hE5 : (fun s => Q (z s) (z s) - s ^ 2 • Q r r) =o[𝓝 0] fun s : ℝ => s ^ 2 := by
    have hsplit : ∀ s, Q (z s) (z s) - s ^ 2 • Q r r
        = Q (z s - s • r) (z s) + s • Q r (z s - s • r) := by
      intro s
      have e1 : Q (z s) (z s) = Q (z s - s • r) (z s) + s • Q r (z s) := by
        have h2 : Q (z s) = Q (z s - s • r) + s • Q r := by
          rw [← map_smul, ← map_add]
          congr 1
          abel
        rw [h2]
        rfl
      have e3 : Q r (z s) = Q r (z s - s • r) + s • Q r r := by
        rw [map_sub, map_smul]
        abel
      rw [e1, e3, smul_add, smul_smul, pow_two]
      abel
    have h1 : (fun s => Q (z s - s • r) (z s)) =O[𝓝 0] fun s : ℝ => s ^ 2 * s := by
      have hb : (fun s => Q (z s - s • r) (z s))
          =O[𝓝 0] fun s => ‖z s - s • r‖ * ‖z s‖ := by
        refine IsBigO.of_bound ‖Q‖ ?_
        filter_upwards with s
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        calc ‖Q (z s - s • r) (z s)‖ ≤ ‖Q‖ * ‖z s - s • r‖ * ‖z s‖ := Q.le_opNorm₂ _ _
          _ = ‖Q‖ * (‖z s - s • r‖ * ‖z s‖) := by ring
      exact hb.trans (hw.norm_left.mul hzO.norm_left)
    have h2 : (fun s => s • Q r (z s - s • r)) =O[𝓝 0] fun s : ℝ => s * s ^ 2 := by
      have hc : (fun s => Q r (z s - s • r)) =O[𝓝 0] fun s : ℝ => s ^ 2 :=
        ((Q r).isBigO_comp _ _).trans hw
      exact smul_isBigO hc
    have h3 := (h1.trans_isLittleO sq_mul_id_isLittleO_sq).add
      (h2.trans_isLittleO id_mul_sq_isLittleO_sq)
    refine h3.congr' ?_ (by rfl)
    filter_upwards with s
    exact (hsplit s).symm
  have hE6 : (fun s => s • K₁ (z s) - s ^ 2 • K₁ r) =o[𝓝 0] fun s : ℝ => s ^ 2 := by
    have hsplit : ∀ s, s • K₁ (z s) - s ^ 2 • K₁ r = s • K₁ (z s - s • r) := by
      intro s
      rw [map_sub, map_smul, smul_sub, smul_smul, pow_two]
    have hc : (fun s => K₁ (z s - s • r)) =O[𝓝 0] fun s : ℝ => s ^ 2 :=
      (K₁.isBigO_comp _ _).trans hw
    have h1 := (smul_isBigO hc).trans_isLittleO id_mul_sq_isLittleO_sq
    refine h1.congr' ?_ (by rfl)
    filter_upwards with s
    exact (hsplit s).symm
  -- assemble
  set v : E := β • r - b - Q r r + K₁ r with hv
  have hpt : ∀ s, s ^ 2 • v
      = (z (γ s) - (z s + s ^ 2 • b + Q (z s) (z s) - s • K₁ (z s)))
        - (γ s - s - β * s ^ 2) • r - (γ s ^ 2 - s ^ 2) • z₂ - e (γ s) + e s
        + (Q (z s) (z s) - s ^ 2 • Q r r) - (s • K₁ (z s) - s ^ 2 • K₁ r) := by
    intro s
    have hzs : z s = s • r + s ^ 2 • z₂ + e s := by
      simp [he]
    have hzγ : z (γ s) = γ s • r + γ s ^ 2 • z₂ + e (γ s) := by
      simp [he]
    rw [hzγ, hzs, hv]
    module
  have hfinal : (fun s : ℝ => s ^ 2 • v) =o[𝓝 0] fun s : ℝ => s ^ 2 := by
    have h := (((((hrec.sub hE1).sub hE2).sub hE3).add hE4).add hE5).sub hE6
    refine h.congr' ?_ (by rfl)
    filter_upwards with s
    exact (hpt s).symm
  have hv0 : v = 0 := eq_zero_of_sq_smul_isLittleO hfinal
  have : b + Q r r - K₁ r - β • r = -v := by
    rw [hv]
    abel
  rw [this, hv0, neg_zero]

end LeadingRay
end NCG
