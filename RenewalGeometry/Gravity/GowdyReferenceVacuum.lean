/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.GowdyVacuumRicci

/-!
# The Gowdy reference is a vacuum metric
  (vacuum clause of `thm:supp-gowdy-full-curvature`; emergent-spacetime supplement)

* `HasJ2`, `HasJ2.mul/exp/add/cmul/congr`, `hasJ2_jetOf/const/clock/logClock`: actual
  second-order jets (`dP`, `dQ`, mixed) of functions on `ℝ²` obey the `J2` calculus.
* `GowdySmoothReference.gowdyJet_ref_eq`: the metric 2-jet of `g_* = g(t, P, Q, λ)` equals
  `jetOfEntries (g_*⁻¹) (gowdyEntryJets …)` built from the jets of the reference fields.
* `GowdySmoothReference.ricci_flat_interior`, `ricci_flat` (**vacuum**): for a smooth reference
  (frame system + coordinate constraints), `Ric(g_*) = 0` at every point of the slab
  (`t₀ < t₁`; interior points by differentiating the frame relations, the boundary by continuity,
  `continuousAt_ricci_ref`).
* `GowdySmoothReference.readout_full_curvature_vacuum`: `thm:supp-gowdy-full-curvature` with all
  clauses, including the unconditional `‖Ric(g_h)‖ ≤ C h`.
-/

open Set Filter Topology
open scoped BigOperators ContDiff

set_option linter.unusedSectionVars false

namespace RenewalGeometry.GowdyStaggered.HermiteReadout

open CubicHermiteRemainder CoordinateCurvatureJet

noncomputable section
/-! ### Second-order jets of functions on `ℝ²` -/

/-- Mixed second derivative `D_v (D_w F)` at `z`. -/
def D2 (w v : ℝ × ℝ) (F : ℝ × ℝ → ℝ) (z : ℝ × ℝ) : ℝ := fderiv ℝ (fun y => fderiv ℝ F y w) z v

/-- `F` has the 2-jet `j` at `z`. -/
def HasJ2 (F : ℝ × ℝ → ℝ) (z : ℝ × ℝ) (j : J2) : Prop :=
  ContDiffAt ℝ 2 F z ∧ F z = j.v ∧ dP F z = j.t ∧ dQ F z = j.θ ∧ dP (dP F) z = j.tt ∧
    dP (dQ F) z = j.tθ ∧ dQ (dQ F) z = j.θθ

theorem dP_dP_eq_D2 (F : ℝ × ℝ → ℝ) (z : ℝ × ℝ) : dP (dP F) z = D2 (1, 0) (1, 0) F z := rfl
theorem dP_dQ_eq_D2 (F : ℝ × ℝ → ℝ) (z : ℝ × ℝ) : dP (dQ F) z = D2 (0, 1) (1, 0) F z := rfl
theorem dQ_dQ_eq_D2 (F : ℝ × ℝ → ℝ) (z : ℝ × ℝ) : dQ (dQ F) z = D2 (0, 1) (0, 1) F z := rfl

theorem differentiableAt_fderiv_apply {F : ℝ × ℝ → ℝ} {z : ℝ × ℝ} (hF : ContDiffAt ℝ 2 F z)
    (w : ℝ × ℝ) : DifferentiableAt ℝ (fun y => fderiv ℝ F y w) z :=
  ((hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).clm_apply
    (differentiableAt_const w)

/-- Symmetry of the mixed second derivative for `C²` functions. -/
theorem D2_symm {F : ℝ × ℝ → ℝ} {z : ℝ × ℝ} (hF : ContDiffAt ℝ 2 F z) (w v : ℝ × ℝ) :
    D2 w v F z = D2 v w F z := by
  have hs := hF.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])
  have hd : DifferentiableAt ℝ (fderiv ℝ F) z :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  unfold D2
  rw [fderiv_clm_apply hd (differentiableAt_const _), fderiv_clm_apply hd (differentiableAt_const _)]
  simpa using hs v w

theorem dQ_dP_eq {F : ℝ × ℝ → ℝ} {z : ℝ × ℝ} (hF : ContDiffAt ℝ 2 F z) :
    dQ (dP F) z = dP (dQ F) z := D2_symm hF (1, 0) (0, 1)

theorem eventually_differentiableAt {F : ℝ × ℝ → ℝ} {z : ℝ × ℝ} (hF : ContDiffAt ℝ 2 F z) :
    ∀ᶠ y in 𝓝 z, DifferentiableAt ℝ F y :=
  (hF.eventually (by simp)).mono fun _ hy => hy.differentiableAt (by norm_num)

/-- First-order product rule along `w`. -/
theorem fderiv_mul_apply {F G : ℝ × ℝ → ℝ} {y : ℝ × ℝ} (hF : DifferentiableAt ℝ F y)
    (hG : DifferentiableAt ℝ G y) (w : ℝ × ℝ) :
    fderiv ℝ (fun x => F x * G x) y w = fderiv ℝ F y w * G y + F y * fderiv ℝ G y w := by
  rw [fderiv_fun_mul hF hG]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem fderiv_exp_apply {F : ℝ × ℝ → ℝ} {y : ℝ × ℝ} (hF : DifferentiableAt ℝ F y)
    (w : ℝ × ℝ) : fderiv ℝ (fun x => Real.exp (F x)) y w = Real.exp (F y) * fderiv ℝ F y w := by
  rw [(hF.hasFDerivAt.exp).fderiv]
  simp

theorem fderiv_add_apply {F G : ℝ × ℝ → ℝ} {y : ℝ × ℝ} (hF : DifferentiableAt ℝ F y)
    (hG : DifferentiableAt ℝ G y) (w : ℝ × ℝ) :
    fderiv ℝ (fun x => F x + G x) y w = fderiv ℝ F y w + fderiv ℝ G y w := by
  rw [fderiv_fun_add hF hG]; rfl

theorem fderiv_cmul_apply {F : ℝ × ℝ → ℝ} {y : ℝ × ℝ} (hF : DifferentiableAt ℝ F y) (c : ℝ)
    (w : ℝ × ℝ) : fderiv ℝ (fun x => c * F x) y w = c * fderiv ℝ F y w := by
  rw [fderiv_const_mul hF]; rfl

theorem HasJ2.congr {F G : ℝ × ℝ → ℝ} {z : ℝ × ℝ} {j : J2} (h : HasJ2 F z j)
    (hFG : F =ᶠ[𝓝 z] G) : HasJ2 G z j := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := h
  have e0 : fderiv ℝ F z = fderiv ℝ G z := hFG.fderiv_eq
  have e1 : fderiv ℝ F =ᶠ[𝓝 z] fderiv ℝ G := hFG.fderiv
  have ew : ∀ w v : ℝ × ℝ, D2 w v F z = D2 w v G z := fun w v => by
    have : (fun y => fderiv ℝ F y w) =ᶠ[𝓝 z] (fun y => fderiv ℝ G y w) :=
      e1.mono fun y hy => by simp only [hy]
    unfold D2; rw [this.fderiv_eq]
  refine ⟨h0.congr_of_eventuallyEq hFG.symm, hFG.eq_of_nhds.symm.trans h1, ?_, ?_, ?_, ?_, ?_⟩
  · show fderiv ℝ G z (1, 0) = _; rw [← e0]; exact h2
  · show fderiv ℝ G z (0, 1) = _; rw [← e0]; exact h3
  · rw [dP_dP_eq_D2, ← ew]; exact h4
  · rw [dP_dQ_eq_D2, ← ew]; exact h5
  · rw [dQ_dQ_eq_D2, ← ew]; exact h6

/-- Second-order product rule. -/
theorem D2_mul {F G : ℝ × ℝ → ℝ} {z : ℝ × ℝ} (hF : ContDiffAt ℝ 2 F z)
    (hG : ContDiffAt ℝ 2 G z) (w v : ℝ × ℝ) :
    D2 w v (fun x => F x * G x) z = D2 w v F z * G z + fderiv ℝ F z w * fderiv ℝ G z v +
      fderiv ℝ F z v * fderiv ℝ G z w + F z * D2 w v G z := by
  have hev : (fun y => fderiv ℝ (fun x => F x * G x) y w) =ᶠ[𝓝 z]
      (fun y => fderiv ℝ F y w * G y + F y * fderiv ℝ G y w) :=
    ((eventually_differentiableAt hF).and (eventually_differentiableAt hG)).mono
      fun y hy => fderiv_mul_apply hy.1 hy.2 w
  unfold D2
  rw [hev.fderiv_eq]
  have dF := differentiableAt_fderiv_apply hF w
  have dG := differentiableAt_fderiv_apply hG w
  have dF0 := hF.differentiableAt (by norm_num)
  have dG0 := hG.differentiableAt (by norm_num)
  have a1 : DifferentiableAt ℝ (fun y => fderiv ℝ F y w * G y) z := dF.mul dG0
  have a2 : DifferentiableAt ℝ (fun y => F y * fderiv ℝ G y w) z := dF0.mul dG
  rw [fderiv_add_apply a1 a2, fderiv_mul_apply dF dG0, fderiv_mul_apply dF0 dG]
  ring

/-- Second-order chain rule for `exp`. -/
theorem D2_exp {F : ℝ × ℝ → ℝ} {z : ℝ × ℝ} (hF : ContDiffAt ℝ 2 F z) (w v : ℝ × ℝ) :
    D2 w v (fun x => Real.exp (F x)) z =
      Real.exp (F z) * (fderiv ℝ F z w * fderiv ℝ F z v + D2 w v F z) := by
  have hev : (fun y => fderiv ℝ (fun x => Real.exp (F x)) y w) =ᶠ[𝓝 z]
      (fun y => Real.exp (F y) * fderiv ℝ F y w) :=
    (eventually_differentiableAt hF).mono fun y hy => fderiv_exp_apply hy w
  unfold D2
  rw [hev.fderiv_eq]
  have dF := differentiableAt_fderiv_apply hF w
  have dF0 := hF.differentiableAt (by norm_num)
  have a1 : DifferentiableAt ℝ (fun y => Real.exp (F y)) z := dF0.exp
  rw [fderiv_mul_apply a1 dF, fderiv_exp_apply dF0]
  ring

theorem D2_add {F G : ℝ × ℝ → ℝ} {z : ℝ × ℝ} (hF : ContDiffAt ℝ 2 F z)
    (hG : ContDiffAt ℝ 2 G z) (w v : ℝ × ℝ) :
    D2 w v (fun x => F x + G x) z = D2 w v F z + D2 w v G z := by
  have hev : (fun y => fderiv ℝ (fun x => F x + G x) y w) =ᶠ[𝓝 z]
      (fun y => fderiv ℝ F y w + fderiv ℝ G y w) :=
    ((eventually_differentiableAt hF).and (eventually_differentiableAt hG)).mono
      fun y hy => fderiv_add_apply hy.1 hy.2 w
  unfold D2
  rw [hev.fderiv_eq, fderiv_add_apply (differentiableAt_fderiv_apply hF w)
    (differentiableAt_fderiv_apply hG w)]

theorem D2_cmul {F : ℝ × ℝ → ℝ} {z : ℝ × ℝ} (hF : ContDiffAt ℝ 2 F z) (c : ℝ) (w v : ℝ × ℝ) :
    D2 w v (fun x => c * F x) z = c * D2 w v F z := by
  have hev : (fun y => fderiv ℝ (fun x => c * F x) y w) =ᶠ[𝓝 z]
      (fun y => c * fderiv ℝ F y w) :=
    (eventually_differentiableAt hF).mono fun y hy => fderiv_cmul_apply hy c w
  unfold D2
  rw [hev.fderiv_eq, fderiv_cmul_apply (differentiableAt_fderiv_apply hF w)]

/-! ### Jet calculus -/

theorem HasJ2.parts {F : ℝ × ℝ → ℝ} {z : ℝ × ℝ} {j : J2} (h : HasJ2 F z j) :
    ContDiffAt ℝ 2 F z ∧ F z = j.v ∧ fderiv ℝ F z (1, 0) = j.t ∧ fderiv ℝ F z (0, 1) = j.θ ∧
      D2 (1, 0) (1, 0) F z = j.tt ∧ D2 (0, 1) (1, 0) F z = j.tθ ∧ D2 (0, 1) (0, 1) F z = j.θθ :=
  h

theorem HasJ2.of_parts {F : ℝ × ℝ → ℝ} {z : ℝ × ℝ} {j : J2} (h0 : ContDiffAt ℝ 2 F z)
    (h1 : F z = j.v) (h2 : fderiv ℝ F z (1, 0) = j.t) (h3 : fderiv ℝ F z (0, 1) = j.θ)
    (h4 : D2 (1, 0) (1, 0) F z = j.tt) (h5 : D2 (0, 1) (1, 0) F z = j.tθ)
    (h6 : D2 (0, 1) (0, 1) F z = j.θθ) : HasJ2 F z j :=
  ⟨h0, h1, h2, h3, h4, h5, h6⟩

theorem HasJ2.mul {F G : ℝ × ℝ → ℝ} {z : ℝ × ℝ} {j k : J2} (hF : HasJ2 F z j)
    (hG : HasJ2 G z k) : HasJ2 (fun x => F x * G x) z (J2.mul j k) := by
  obtain ⟨c0, v0, t0, θ0, tt0, tθ0, θθ0⟩ := hF.parts
  obtain ⟨c1, v1, t1, θ1, tt1, tθ1, θθ1⟩ := hG.parts
  have d0 := c0.differentiableAt (by norm_num)
  have d1 := c1.differentiableAt (by norm_num)
  have s0 : D2 (1, 0) (0, 1) F z = j.tθ := by rw [D2_symm c0]; exact tθ0
  have s1 : D2 (1, 0) (0, 1) G z = k.tθ := by rw [D2_symm c1]; exact tθ1
  refine HasJ2.of_parts (c0.mul c1) (by simp [J2.mul, v0, v1]) ?_ ?_ ?_ ?_ ?_
  · rw [fderiv_mul_apply d0 d1, t0, t1, v0, v1]; simp only [J2.mul]
  · rw [fderiv_mul_apply d0 d1, θ0, θ1, v0, v1]; simp only [J2.mul]
  · rw [D2_mul c0 c1, tt0, tt1, t0, t1, v0, v1]; simp only [J2.mul]; ring
  · rw [D2_mul c0 c1, tθ0, tθ1, t0, t1, θ0, θ1, v0, v1]; simp only [J2.mul]; ring
  · rw [D2_mul c0 c1, θθ0, θθ1, θ0, θ1, v0, v1]; simp only [J2.mul]; ring

theorem HasJ2.exp {F : ℝ × ℝ → ℝ} {z : ℝ × ℝ} {j : J2} (hF : HasJ2 F z j) :
    HasJ2 (fun x => Real.exp (F x)) z (J2.exp j) := by
  obtain ⟨c0, v0, t0, θ0, tt0, tθ0, θθ0⟩ := hF.parts
  have d0 := c0.differentiableAt (by norm_num)
  refine HasJ2.of_parts (Real.contDiff_exp.contDiffAt.comp z c0) (by simp [J2.exp, v0])
    ?_ ?_ ?_ ?_ ?_
  · rw [fderiv_exp_apply d0, t0, v0]; simp only [J2.exp]
  · rw [fderiv_exp_apply d0, θ0, v0]; simp only [J2.exp]
  · rw [D2_exp c0, tt0, t0, v0]; simp only [J2.exp]; ring
  · rw [D2_exp c0, tθ0, t0, θ0, v0]; simp only [J2.exp]; ring
  · rw [D2_exp c0, θθ0, θ0, v0]; simp only [J2.exp]; ring

theorem HasJ2.add {F G : ℝ × ℝ → ℝ} {z : ℝ × ℝ} {j k : J2} (hF : HasJ2 F z j)
    (hG : HasJ2 G z k) : HasJ2 (fun x => F x + G x) z (J2.add j k) := by
  obtain ⟨c0, v0, t0, θ0, tt0, tθ0, θθ0⟩ := hF.parts
  obtain ⟨c1, v1, t1, θ1, tt1, tθ1, θθ1⟩ := hG.parts
  have d0 := c0.differentiableAt (by norm_num)
  have d1 := c1.differentiableAt (by norm_num)
  refine HasJ2.of_parts (c0.add c1) (by simp [J2.add, v0, v1]) ?_ ?_ ?_ ?_ ?_
  · rw [fderiv_add_apply d0 d1, t0, t1]; rfl
  · rw [fderiv_add_apply d0 d1, θ0, θ1]; rfl
  · rw [D2_add c0 c1, tt0, tt1]; rfl
  · rw [D2_add c0 c1, tθ0, tθ1]; rfl
  · rw [D2_add c0 c1, θθ0, θθ1]; rfl

theorem HasJ2.cmul {F : ℝ × ℝ → ℝ} {z : ℝ × ℝ} {j : J2} (hF : HasJ2 F z j) (c : ℝ) :
    HasJ2 (fun x => c * F x) z (J2.cmul c j) := by
  obtain ⟨c0, v0, t0, θ0, tt0, tθ0, θθ0⟩ := hF.parts
  have d0 := c0.differentiableAt (by norm_num)
  refine HasJ2.of_parts (contDiffAt_const.mul c0) (by simp [J2.cmul, v0]) ?_ ?_ ?_ ?_ ?_
  · rw [fderiv_cmul_apply d0, t0]; rfl
  · rw [fderiv_cmul_apply d0, θ0]; rfl
  · rw [D2_cmul c0, tt0]; rfl
  · rw [D2_cmul c0, tθ0]; rfl
  · rw [D2_cmul c0, θθ0]; rfl

/-- The jet of a smooth function. -/
def jetOf (F : ℝ × ℝ → ℝ) (z : ℝ × ℝ) : J2 :=
  ⟨F z, dP F z, dQ F z, dP (dP F) z, dP (dQ F) z, dQ (dQ F) z⟩

theorem hasJ2_jetOf {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (z : ℝ × ℝ) :
    HasJ2 F z (jetOf F z) :=
  ⟨hF.contDiffAt.of_le (by norm_cast), rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem hasJ2_const (c : ℝ) (z : ℝ × ℝ) : HasJ2 (fun _ => c) z ⟨c, 0, 0, 0, 0, 0⟩ := by
  have h := hasJ2_jetOf (contDiff_const (c := c)) z
  have e1 : dP (fun _ : ℝ × ℝ => c) = fun _ => 0 := by funext y; simp [dP]
  have e2 : dQ (fun _ : ℝ × ℝ => c) = fun _ => 0 := by funext y; simp [dQ]
  have e : jetOf (fun _ : ℝ × ℝ => c) z = ⟨c, 0, 0, 0, 0, 0⟩ := by
    simp only [jetOf, e1, e2]; simp [dP, dQ]
  rwa [e] at h

theorem hasJ2_clock (z : ℝ × ℝ) : HasJ2 (fun y => y.1) z (jClock z.1) := by
  have h := hasJ2_jetOf (contDiff_fst (𝕜 := ℝ) (E := ℝ) (F := ℝ)) z
  have hf : fderiv ℝ (fun y : ℝ × ℝ => y.1) = fun _ => ContinuousLinearMap.fst ℝ ℝ ℝ := by
    funext y; exact fderiv_fst
  have e1 : dP (fun y : ℝ × ℝ => y.1) = fun _ => 1 := by funext y; simp [dP, hf]
  have e2 : dQ (fun y : ℝ × ℝ => y.1) = fun _ => 0 := by funext y; simp [dQ, hf]
  have e : jetOf (fun y : ℝ × ℝ => y.1) z = jClock z.1 := by
    simp only [jetOf, jClock, e1, e2]; simp [dP, dQ]
  rwa [e] at h

theorem hasJ2_logClock {z : ℝ × ℝ} (hz : 0 < z.1) :
    HasJ2 (fun y => Real.log y.1) z (jLogClock z.1) := by
  have hc : ContDiffAt ℝ 2 (fun y : ℝ × ℝ => Real.log y.1) z :=
    (Real.contDiffAt_log.2 hz.ne').comp z contDiff_fst.contDiffAt
  have hd : ∀ y : ℝ × ℝ, 0 < y.1 → ∀ w : ℝ × ℝ,
      fderiv ℝ (fun y : ℝ × ℝ => Real.log y.1) y w = w.1 / y.1 := by
    intro y hy w
    rw [(hasFDerivAt_fst.log hy.ne').fderiv]
    simp [div_eq_inv_mul]
  have hev : ∀ w : ℝ × ℝ, (fun y => fderiv ℝ (fun y : ℝ × ℝ => Real.log y.1) y w) =ᶠ[𝓝 z]
      (fun y => w.1 * (y.1)⁻¹) := by
    intro w
    have : ∀ᶠ y in 𝓝 z, 0 < y.1 :=
      continuous_fst.continuousAt.eventually (lt_mem_nhds hz)
    exact this.mono fun y hy => by
      show fderiv ℝ (fun y : ℝ × ℝ => Real.log y.1) y w = w.1 * (y.1)⁻¹
      rw [hd y hy w]; ring
  have h2 : ∀ w v : ℝ × ℝ, D2 w v (fun y : ℝ × ℝ => Real.log y.1) z = -(w.1 * v.1 / z.1 ^ 2) := by
    intro w v
    unfold D2
    rw [(hev w).fderiv_eq]
    have h1 : HasFDerivAt (fun y : ℝ × ℝ => y.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) z :=
      hasFDerivAt_fst
    have h2 := ((hasFDerivAt_inv (𝕜 := ℝ) hz.ne').comp z h1).const_mul w.1
    rw [show (fun y : ℝ × ℝ => w.1 * (y.1)⁻¹) =
      fun y => w.1 * ((fun x : ℝ => x⁻¹) ∘ (fun y : ℝ × ℝ => y.1)) y from rfl, h2.fderiv]
    simp
    field_simp
  refine ⟨hc, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · show fderiv ℝ _ z (1, 0) = _; rw [hd z hz]; simp [jLogClock]
  · show fderiv ℝ _ z (0, 1) = _; rw [hd z hz]; simp [jLogClock]
  · rw [dP_dP_eq_D2, h2]; simp [jLogClock]
  · rw [dP_dQ_eq_D2, h2]; simp [jLogClock]
  · rw [dQ_dQ_eq_D2, h2]; simp [jLogClock]


/-! ### The metric jet of the reference -/

theorem exp_half_sub_log (a : ℝ) {t : ℝ} (ht : 0 < t) :
    Real.exp (1 / 2 * a + -(1 / 2) * Real.log t) = Real.exp (a / 2) / Real.sqrt t := by
  rw [Real.exp_add, show -(1 / 2) * Real.log t = -(Real.log t / 2) by ring, Real.exp_neg,
    Real.sqrt_eq_rpow, Real.rpow_def_of_pos ht]
  ring_nf

theorem fderiv_fderiv_clm_comp_at {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (L : F →L[ℝ] G) {f : ℝ × ℝ → F} {z : ℝ × ℝ}
    (hf : ContDiffAt ℝ 2 f z) (v w : ℝ × ℝ) :
    fderiv ℝ (fderiv ℝ (fun y => L (f y))) z v w = L (fderiv ℝ (fderiv ℝ f) z v w) := by
  have hev : fderiv ℝ (fun y => L (f y)) =ᶠ[𝓝 z]
      fun y => (ContinuousLinearMap.compL ℝ (ℝ × ℝ) F G L) (fderiv ℝ f y) :=
    ((hf.eventually (by simp)).mono fun y hy => hy.differentiableAt (by norm_num)).mono
      fun y hy => (L.hasFDerivAt.comp y hy.hasFDerivAt).fderiv
  rw [hev.fderiv_eq]
  have hd : DifferentiableAt ℝ (fderiv ℝ f) z :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h2 := ((ContinuousLinearMap.compL ℝ (ℝ × ℝ) F G L).hasFDerivAt.comp z hd.hasFDerivAt)
  have h3 : fderiv ℝ (fun y => (ContinuousLinearMap.compL ℝ (ℝ × ℝ) F G L) (fderiv ℝ f y)) z =
      (ContinuousLinearMap.compL ℝ (ℝ × ℝ) F G L).comp (fderiv ℝ (fderiv ℝ f) z) := h2.fderiv
  rw [h3]
  rfl

theorem fderiv_fderiv_apply_at {F : ℝ × ℝ → ℝ} {z : ℝ × ℝ} (hF : ContDiffAt ℝ 2 F z)
    (v w : ℝ × ℝ) : fderiv ℝ (fderiv ℝ F) z v w = D2 w v F z := by
  have hd : DifferentiableAt ℝ (fderiv ℝ F) z :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  unfold D2
  rw [fderiv_clm_apply hd (differentiableAt_const w)]
  simp

namespace GowdySmoothReference

variable {t₀ t₁ : ℝ} (sol : GowdySmoothReference t₀ t₁)

/-- The reference metric is `C²` near every point with `t > 0`. -/
theorem contDiffAt_refMetric {z : ℝ × ℝ} (hz : 0 < z.1) :
    ContDiffAt ℝ 2 (fun y => gowdyMetric (stateMap sol.fld y)) z :=
  ((contDiffOn_gowdyMetric.contDiffAt (isOpen_posTime.mem_nhds (show
    stateMap sol.fld z ∈ posTime from hz))).comp z
    (contDiff_stateMap sol.smooth_fld).contDiffAt).of_le (by norm_cast)

/-- **Jets of the reference metric entries** (chain rule for the Gowdy metric). -/
theorem hasJ2_refEntry {z : ℝ × ℝ} (hz : 0 < z.1) (e j : Fin 4) :
    HasJ2 (fun y => gowdyMetric (stateMap sol.fld y) e j) z
      (gowdyEntryJets (jClock z.1) (jLogClock z.1) (jetOf (sol.fld 0) z) (jetOf (sol.fld 1) z)
        (jetOf (sol.fld 2) z) e j) := by
  have hT := hasJ2_clock z
  have hl := hasJ2_logClock hz
  have hP := hasJ2_jetOf (sol.smooth_fld 0) z
  have hQ := hasJ2_jetOf (sol.smooth_fld 1) z
  have hL := hasJ2_jetOf (sol.smooth_fld 2) z
  have hA := ((hL.cmul (1 / 2)).add (hl.cmul (-(1 / 2)))).exp
  have hpos : ∀ᶠ y in 𝓝 z, 0 < y.1 := continuous_fst.continuousAt.eventually (lt_mem_nhds hz)
  have hz0 := hasJ2_const 0 z
  fin_cases e <;> fin_cases j
  · refine (hA.cmul (-1)).congr (hpos.mono fun y hy => ?_)
    show -1 * Real.exp (1 / 2 * sol.fld 2 y + -(1 / 2) * Real.log y.1) =
      -(Real.exp (sol.fld 2 y / 2) / Real.sqrt y.1)
    rw [exp_half_sub_log _ hy]; ring
  all_goals first
    | exact hz0.congr (Filter.Eventually.of_forall fun y => by simp [gowdyMetric])
    | skip
  · refine hA.congr (hpos.mono fun y hy => ?_)
    show Real.exp (1 / 2 * sol.fld 2 y + -(1 / 2) * Real.log y.1) =
      Real.exp (sol.fld 2 y / 2) / Real.sqrt y.1
    rw [exp_half_sub_log _ hy]
  · exact (hT.mul hP.exp).congr (Filter.Eventually.of_forall fun y => by
      simp [gowdyMetric, stateMap])
  · exact ((hT.mul hP.exp).mul hQ).congr (Filter.Eventually.of_forall fun y => by
      simp [gowdyMetric, stateMap])
  · exact ((hT.mul hP.exp).mul hQ).congr (Filter.Eventually.of_forall fun y => by
      simp [gowdyMetric, stateMap])
  · refine (((hT.mul hP.exp).mul (hQ.mul hQ)).add (hT.mul (hP.cmul (-1)).exp)).congr
      (Filter.Eventually.of_forall fun y => ?_)
    simp [gowdyMetric, stateMap]
    ring

/-- **The metric 2-jet of the reference** in terms of the jets of `t, log t, P, Q, λ`. -/
theorem gowdyJet_ref_eq {z : ℝ × ℝ} (hz : 0 < z.1) :
    gowdyJet (stateMap sol.fld) z =
      jetOfEntries (gowdyInvMetric (stateMap sol.fld z))
        (gowdyEntryJets (jClock z.1) (jLogClock z.1) (jetOf (sol.fld 0) z)
          (jetOf (sol.fld 1) z) (jetOf (sol.fld 2) z)) := by
  have hg := sol.contDiffAt_refMetric hz
  have hgd := hg.differentiableAt (by norm_num)
  set E := gowdyEntryJets (jClock z.1) (jLogClock z.1) (jetOf (sol.fld 0) z)
    (jetOf (sol.fld 1) z) (jetOf (sol.fld 2) z)
  have hE := sol.hasJ2_refEntry hz
  set L : ∀ e j : Fin 4, (Fin 4 → Fin 4 → ℝ) →L[ℝ] ℝ := fun e j =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) j).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => Fin 4 → ℝ) e)
  have c1 : ∀ e j v, fderiv ℝ (fun y => gowdyMetric (stateMap sol.fld y)) z v e j =
      fderiv ℝ (fun y => gowdyMetric (stateMap sol.fld y) e j) z v := fun e j v =>
    (SecondOrderChainRule.fderiv_clm_comp' (L e j) hgd v).symm
  have c2 : ∀ e j v w, fderiv ℝ (fderiv ℝ (fun y => gowdyMetric (stateMap sol.fld y))) z v w e j =
      D2 w v (fun y => gowdyMetric (stateMap sol.fld y) e j) z := fun e j v w => by
    rw [← fderiv_fderiv_apply_at (hE e j).1]
    exact (fderiv_fderiv_clm_comp_at (L e j) hg v w).symm
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · funext i e j
    show fderiv ℝ (fun y => gowdyMetric (stateMap sol.fld y)) z (coordDir i) e j = _
    rw [c1]
    obtain ⟨-, -, ht, hθ, -⟩ := hE e j
    fin_cases i
    · exact ht
    · exact hθ
    · simp [coordDir, jetOfEntries]
    · simp [coordDir, jetOfEntries]
  · funext d i e j
    show fderiv ℝ (fderiv ℝ (fun y => gowdyMetric (stateMap sol.fld y))) z (coordDir d)
      (coordDir i) e j = _
    rw [c2]
    obtain ⟨hc, -, -, -, htt, htθ, hθθ⟩ := hE e j
    have hs := D2_symm hc (1, 0) (0, 1)
    fin_cases d <;> fin_cases i
    · exact htt
    · exact htθ
    · simp [coordDir, jetOfEntries, D2]
    · simp [coordDir, jetOfEntries, D2]
    · show D2 (1, 0) (0, 1) _ z = _
      rw [hs]; exact htθ
    · exact hθθ
    all_goals simp [coordDir, jetOfEntries, D2]

end GowdySmoothReference


/-! ### The frame relations at second order and Ricci flatness -/

namespace GowdySmoothReference

variable {t₀ t₁ : ℝ} (sol : GowdySmoothReference t₀ t₁)

/-- **The Gowdy reference metric is Ricci flat at interior points of the slab**: the frame
system `eq:supp-gowdy-frame-system` with the coordinate constraints
`eq:supp-gowdy-coordinate-constraints` is the vacuum system for `eq:supp-gowdy-metric`. -/
theorem ricci_flat_interior (h0 : 0 < t₀) {z : ℝ × ℝ} (hz : z.1 ∈ Ioo t₀ t₁) :
    ricciJet (gowdyJet (stateMap sol.fld) z) = 0 := by
  have hz0 : 0 < z.1 := h0.trans hz.1
  have hzI : z.1 ∈ Icc t₀ t₁ := Ioo_subset_Icc_self hz
  have hev : ∀ᶠ y in 𝓝 z, y.1 ∈ Icc t₀ t₁ :=
    (continuous_fst.continuousAt.eventually (Ioo_mem_nhds hz.1 hz.2)).mono
      fun y hy => Ioo_subset_Icc_self hy
  set P := sol.fld 0 with hPdef
  set Q := sol.fld 1 with hQdef
  set L := sol.fld 2 with hLdef
  have hPs : ContDiff ℝ ∞ P := sol.smooth_fld 0
  have hQs : ContDiff ℝ ∞ Q := sol.smooth_fld 1
  have hLs : ContDiff ℝ ∞ L := sol.smooth_fld 2
  -- frame fields through the potentials
  have pa : ∀ y : ℝ × ℝ, y.1 ∈ Icc t₀ t₁ → sol.a y = dP P y := fun y hy => (sol.eq_P y hy).symm
  have pb : ∀ y : ℝ × ℝ, y.1 ∈ Icc t₀ t₁ → sol.b y = dQ P y :=
    fun y hy => (sol.constraint_P y hy).symm
  have pc : ∀ y : ℝ × ℝ, y.1 ∈ Icc t₀ t₁ → sol.c y = Real.exp (P y) * dP Q y := by
    intro y hy
    have h := sol.eq_Q y hy
    show sol.c y = Real.exp (sol.P y) * dT sol.Q y
    rw [h, ← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
  have pd : ∀ y : ℝ × ℝ, y.1 ∈ Icc t₀ t₁ → sol.d y = Real.exp (P y) * dQ Q y :=
    fun y hy => (sol.constraint_Q y hy).symm
  have ea : sol.a =ᶠ[𝓝 z] dP P := hev.mono pa
  have eb : sol.b =ᶠ[𝓝 z] dQ P := hev.mono pb
  have ec : sol.c =ᶠ[𝓝 z] fun y => Real.exp (P y) * dP Q y := hev.mono pc
  have ed : sol.d =ᶠ[𝓝 z] fun y => Real.exp (P y) * dQ Q y := hev.mono pd
  have dPd := (hPs.differentiable (by simp)) z
  have dEd : DifferentiableAt ℝ (fun y => Real.exp (P y)) z := dPd.exp
  have dQt : DifferentiableAt ℝ (dP Q) z := ((contDiff_dP hQs).differentiable (by simp)) z
  have dQθ : DifferentiableAt ℝ (dQ Q) z := ((contDiff_dQ hQs).differentiable (by simp)) z
  -- second-order relations for `P`
  have k1 : dP (dP P) z = dQ (dQ P) z - dP P z / z.1 +
      Real.exp (P z) ^ 2 * (dP Q z ^ 2 - dQ Q z ^ 2) := by
    have h := sol.eq_a z hzI
    have hda : dT sol.a z = dP (dP P) z := by
      show fderiv ℝ sol.a z (1, 0) = fderiv ℝ (dP P) z (1, 0); rw [ea.fderiv_eq]
    have hdb : dΘ sol.b z = dQ (dQ P) z := by
      show fderiv ℝ sol.b z (0, 1) = fderiv ℝ (dQ P) z (0, 1); rw [eb.fderiv_eq]
    rw [hda, hdb, pa z hzI, pc z hzI, pd z hzI] at h
    rw [h]; ring
  -- second-order relations for `Q`
  have k2 : dP (dP Q) z = dQ (dQ Q) z - dP Q z / z.1 - 2 * dP P z * dP Q z +
      2 * dQ P z * dQ Q z := by
    have h := sol.eq_c z hzI
    have hdc : dT sol.c z = Real.exp (P z) * dP P z * dP Q z + Real.exp (P z) * dP (dP Q) z := by
      show fderiv ℝ sol.c z (1, 0) = _
      rw [ec.fderiv_eq, fderiv_mul_apply dEd dQt, fderiv_exp_apply dPd]; rfl
    have hdd : dΘ sol.d z = Real.exp (P z) * dQ P z * dQ Q z + Real.exp (P z) * dQ (dQ Q) z := by
      show fderiv ℝ sol.d z (0, 1) = _
      rw [ed.fderiv_eq, fderiv_mul_apply dEd dQθ, fderiv_exp_apply dPd]; rfl
    rw [hdc, hdd, pa z hzI, pb z hzI, pc z hzI, pd z hzI] at h
    have he := Real.exp_pos (P z)
    have hz' := hz0.ne'
    apply mul_left_cancel₀ he.ne'
    field_simp
    field_simp at h
    linear_combination h
  -- the `λ` constraints and their derivatives
  have pLt : ∀ y : ℝ × ℝ, y.1 ∈ Icc t₀ t₁ → dP L y = y.1 * (dP P y * dP P y + dQ P y * dQ P y +
      Real.exp (P y) * Real.exp (P y) * (dP Q y * dP Q y + dQ Q y * dQ Q y)) := by
    intro y hy
    have h := sol.eq_lam y hy
    show dT sol.lam y = _
    rw [h, pa y hy, pb y hy, pc y hy, pd y hy]; ring
  have pLθ : ∀ y : ℝ × ℝ, y.1 ∈ Icc t₀ t₁ → dQ L y = 2 * y.1 * (dP P y * dQ P y +
      Real.exp (P y) * Real.exp (P y) * dP Q y * dQ Q y) := by
    intro y hy
    have h := sol.constraint_lam y hy
    show dΘ sol.lam y = _
    rw [h, pa y hy, pb y hy, pc y hy, pd y hy]; ring
  have hT := hasJ2_clock z
  have hP := hasJ2_jetOf hPs z
  have hPt := hasJ2_jetOf (contDiff_dP hPs) z
  have hPθ := hasJ2_jetOf (contDiff_dQ hPs) z
  have hQt := hasJ2_jetOf (contDiff_dP hQs) z
  have hQθ := hasJ2_jetOf (contDiff_dQ hQs) z
  have hFl := hT.mul (((hPt.mul hPt).add (hPθ.mul hPθ)).add
    ((hP.exp.mul hP.exp).mul ((hQt.mul hQt).add (hQθ.mul hQθ))))
  have hGl := (hT.cmul 2).mul ((hPt.mul hPθ).add (((hP.exp.mul hP.exp).mul hQt).mul hQθ))
  have eFl : dP L =ᶠ[𝓝 z] fun y => y.1 * (dP P y * dP P y + dQ P y * dQ P y +
      Real.exp (P y) * Real.exp (P y) * (dP Q y * dP Q y + dQ Q y * dQ Q y)) := hev.mono pLt
  have eGl : dQ L =ᶠ[𝓝 z] fun y => 2 * y.1 * (dP P y * dQ P y +
      Real.exp (P y) * Real.exp (P y) * dP Q y * dQ Q y) := hev.mono pLθ
  obtain ⟨-, -, Ft, Fθ, -, -, -⟩ := hFl.parts
  obtain ⟨-, -, -, Gθ, -, -, -⟩ := hGl.parts
  have sP := dQ_dP_eq (hPs.contDiffAt.of_le (by norm_cast) : ContDiffAt ℝ 2 P z)
  have sQ := dQ_dP_eq (hQs.contDiffAt.of_le (by norm_cast) : ContDiffAt ℝ 2 Q z)
  have sL := dQ_dP_eq (hLs.contDiffAt.of_le (by norm_cast) : ContDiffAt ℝ 2 L z)
  have k5 : dP (dP L) z = (dP P z ^ 2 + dQ P z ^ 2 + Real.exp (P z) ^ 2 *
      (dP Q z ^ 2 + dQ Q z ^ 2)) + z.1 * (2 * dP P z * dP (dP P) z + 2 * dQ P z * dP (dQ P) z +
      2 * Real.exp (P z) ^ 2 * dP P z * (dP Q z ^ 2 + dQ Q z ^ 2) +
      Real.exp (P z) ^ 2 * (2 * dP Q z * dP (dP Q) z + 2 * dQ Q z * dP (dQ Q) z)) := by
    have e1 : dP (dP L) z = fderiv ℝ (fun y => y.1 * (dP P y * dP P y + dQ P y * dQ P y +
        Real.exp (P y) * Real.exp (P y) * (dP Q y * dP Q y + dQ Q y * dQ Q y))) z (1, 0) := by
      show fderiv ℝ (dP L) z (1, 0) = _; rw [eFl.fderiv_eq]
    rw [e1, Ft]
    simp only [J2.mul, J2.add, J2.exp, jetOf, jClock]
    ring
  have k6 : dP (dQ L) z = z.1 * (2 * dP P z * dP (dQ P) z + 2 * dQ P z * dQ (dQ P) z +
      2 * Real.exp (P z) ^ 2 * dQ P z * (dP Q z ^ 2 + dQ Q z ^ 2) +
      Real.exp (P z) ^ 2 * (2 * dP Q z * dP (dQ Q) z + 2 * dQ Q z * dQ (dQ Q) z)) := by
    have e1 : dP (dQ L) z = fderiv ℝ (fun y => y.1 * (dP P y * dP P y + dQ P y * dQ P y +
        Real.exp (P y) * Real.exp (P y) * (dP Q y * dP Q y + dQ Q y * dQ Q y))) z (0, 1) := by
      rw [← sL]; show fderiv ℝ (dP L) z (0, 1) = _; rw [eFl.fderiv_eq]
    rw [e1, Fθ]
    simp only [J2.mul, J2.add, J2.exp, jetOf, jClock]
    rw [sP, sQ]
    ring
  have k7 : dQ (dQ L) z = 2 * z.1 * (dP (dQ P) z * dQ P z + dP P z * dQ (dQ P) z +
      2 * Real.exp (P z) ^ 2 * dQ P z * dP Q z * dQ Q z +
      Real.exp (P z) ^ 2 * (dP (dQ Q) z * dQ Q z + dP Q z * dQ (dQ Q) z)) := by
    have e1 : dQ (dQ L) z = fderiv ℝ (fun y => 2 * y.1 * (dP P y * dQ P y +
        Real.exp (P y) * Real.exp (P y) * dP Q y * dQ Q y)) z (0, 1) := by
      show fderiv ℝ (dQ L) z (0, 1) = _; rw [eGl.fderiv_eq]
    rw [e1, Gθ]
    simp only [J2.mul, J2.add, J2.exp, J2.cmul, jetOf, jClock]
    rw [sP, sQ]
    ring
  have k3 : dP L z = z.1 * (dP P z ^ 2 + dQ P z ^ 2 + Real.exp (P z) ^ 2 *
      (dP Q z ^ 2 + dQ Q z ^ 2)) := by rw [pLt z hzI]; ring
  have k4 : dQ L z = 2 * z.1 * (dP P z * dQ P z + Real.exp (P z) ^ 2 * dP Q z * dQ Q z) := by
    rw [pLθ z hzI]; ring
  have key := ricci_gowdy_algebraic (Q := Q z) (L := L z) hz0 k1 k2 k3 k4 k5 k6 k7
  rw [sol.gowdyJet_ref_eq hz0]
  exact key

/-- `ricciJet ∘ gowdyJet` of the reference is continuous at points with `t > 0`. -/
theorem continuousAt_ricci_ref {z : ℝ × ℝ} (hz : 0 < z.1) :
    ContinuousAt (fun y => ricciJet (gowdyJet (stateMap sol.fld) y)) z := by
  set V : Set (ℝ × ℝ) := {y | 0 < y.1}
  have hV : IsOpen V := isOpen_lt continuous_const continuous_fst
  have hzV : z ∈ V := hz
  have hg : ContDiffOn ℝ ∞ (fun y => gowdyMetric (stateMap sol.fld y)) V := by
    intro y hy
    exact ((contDiffOn_gowdyMetric.contDiffAt (isOpen_posTime.mem_nhds (show
      stateMap sol.fld y ∈ posTime from hy))).comp y
      (contDiff_stateMap sol.smooth_fld).contDiffAt).contDiffWithinAt
  have hd1 : ContinuousAt (fderiv ℝ (fun y => gowdyMetric (stateMap sol.fld y))) z :=
    ((hg.continuousOn_fderiv_of_isOpen hV (by simp)).continuousAt (hV.mem_nhds hzV))
  have hd2 : ContinuousAt (fderiv ℝ (fderiv ℝ (fun y => gowdyMetric (stateMap sol.fld y)))) z :=
    (((hg.fderiv_of_isOpen hV (m := 1) (by first | (norm_num; norm_cast) | norm_cast)).continuousOn_fderiv_of_isOpen hV
      (by simp)).continuousAt (hV.mem_nhds hzV))
  have hi : ContinuousAt (fun y => gowdyInvMetric (stateMap sol.fld y)) z :=
    (contDiffOn_gowdyInvMetric.continuousOn.continuousAt (isOpen_posTime.mem_nhds (show
      stateMap sol.fld z ∈ posTime from hz))).comp
      (contDiff_stateMap sol.smooth_fld).continuous.continuousAt
  have m1 : ContinuousAt (fun y => metricD1 (fun y => gowdyMetric (stateMap sol.fld y)) y) z := by
    refine continuousAt_pi.2 fun i => continuousAt_pi.2 fun e => continuousAt_pi.2 fun j => ?_
    exact (continuous_apply j).continuousAt.comp ((continuous_apply e).continuousAt.comp
      (hd1.clm_apply continuousAt_const))
  have m2 : ContinuousAt (fun y => metricD2 (fun y => gowdyMetric (stateMap sol.fld y)) y) z := by
    refine continuousAt_pi.2 fun d => continuousAt_pi.2 fun i => continuousAt_pi.2 fun e =>
      continuousAt_pi.2 fun j => ?_
    exact (continuous_apply j).continuousAt.comp ((continuous_apply e).continuousAt.comp
      ((hd2.clm_apply continuousAt_const).clm_apply continuousAt_const))
  exact contDiff_ricciJet.continuous.continuousAt.comp (hi.prodMk (m1.prodMk m2))

/-- **The Gowdy reference metric is Ricci flat on the closed slab** (`t₀ < t₁`). -/
theorem ricci_flat (h0 : 0 < t₀) (h01 : t₀ < t₁) {z : ℝ × ℝ} (hz : z.1 ∈ Icc t₀ t₁) :
    ricciJet (gowdyJet (stateMap sol.fld) z) = 0 := by
  have hz0 : 0 < z.1 := lt_of_lt_of_le h0 hz.1
  have hcl : z ∈ closure {y : ℝ × ℝ | y.1 ∈ Ioo t₀ t₁} := by
    have e : {y : ℝ × ℝ | y.1 ∈ Ioo t₀ t₁} = Ioo t₀ t₁ ×ˢ (univ : Set ℝ) := by ext y; simp
    rw [e, closure_prod_eq, closure_Ioo h01.ne, closure_univ]
    exact ⟨hz, mem_univ _⟩
  have hc := sol.continuousAt_ricci_ref hz0
  by_contra hne
  have hopen : ∀ᶠ y in 𝓝 z, ricciJet (gowdyJet (stateMap sol.fld) y) ≠ 0 :=
    hc.eventually (isOpen_ne.mem_nhds hne)
  obtain ⟨y, hy1, hy2⟩ := mem_closure_iff_nhds.1 hcl _ hopen
  exact hy1 (sol.ricci_flat_interior h0 hy2)

end GowdySmoothReference


/-! ### The full-curvature theorem with the vacuum clause -/

namespace GowdySmoothReference

variable {t₀ t₁ : ℝ}

open CoordinateCurvatureJet in
/-- **Pathwise full-curvature control on the Gowdy alphabet** (`thm:supp-gowdy-full-curvature`,
all clauses): `readout_full_curvature` together with the Ricci flatness of the reference
(`ricci_flat`), so `‖Ric(g_h)‖ ≤ C h` holds on every cell; the reference curvature is identified as
the Levi–Civita curvature of the vacuum metric `g_*`. -/
theorem readout_full_curvature_vacuum (sol : GowdySmoothReference t₀ t₁) (h0 : 0 < t₀) {R : ℝ}
    (hR : sol.chartRadius h0 ≤ R) {c₀ C₁ : ℝ} (hc₀ : 0 ≤ c₀) (hC₁ : 0 ≤ C₁) :
    ∃ C ℓ₀ : ℝ, 0 ≤ C ∧ 0 < ℓ₀ ∧ ∀ (N : ℕ) [NeZero N], 2 * Real.pi / N ≤ ℓ₀ →
      ∀ (τ₀ : ℝ) (n₀ : ℕ) (X A B : ℕ → GridState N),
        sol.PathwiseHistory h0 R c₀ C₁ N τ₀ n₀ X A B →
        ∀ n < n₀, ∀ (j : ZMod N),
        ∀ x ∈ Icc (τ₀ + n * (2 * Real.pi / N)) (τ₀ + n * (2 * Real.pi / N) + 2 * Real.pi / N),
        ∀ y ∈ Icc (sampleAngle N j) (sampleAngle N j + 2 * Real.pi / N),
          ‖gowdyMetric (stateMap (cellReadout X τ₀ n j) (x, y)) -
              gowdyMetric (stateMap sol.fld (x, y))‖ ≤ C * (2 * Real.pi / N) ^ 2 ∧
          ‖fderiv ℝ (fun z => gowdyMetric (stateMap (cellReadout X τ₀ n j) z)) (x, y) -
              fderiv ℝ (fun z => gowdyMetric (stateMap sol.fld z)) (x, y)‖ ≤
            C * (2 * Real.pi / N) ^ 2 ∧
          ‖fderiv ℝ (fderiv ℝ (fun z => gowdyMetric (stateMap (cellReadout X τ₀ n j) z))) (x, y) -
              fderiv ℝ (fderiv ℝ (fun z => gowdyMetric (stateMap sol.fld z))) (x, y)‖ ≤
            C * (2 * Real.pi / N) ∧
          ‖riemJet (gowdyJet (stateMap (cellReadout X τ₀ n j)) (x, y)) -
              riemJet (gowdyJet (stateMap sol.fld) (x, y))‖ ≤ C * (2 * Real.pi / N) ∧
          ‖riemJet (gowdyJet (stateMap (cellReadout X τ₀ n j)) (x, y))‖ ≤ C ∧
          ricciJet (gowdyJet (stateMap sol.fld) (x, y)) = 0 ∧
          ‖ricciJet (gowdyJet (stateMap (cellReadout X τ₀ n j)) (x, y))‖ ≤
            C * (2 * Real.pi / N) := by
  obtain ⟨C, ℓ₀, hC, hℓ₀, h⟩ := sol.readout_full_curvature h0 hR hc₀ hC₁
  refine ⟨C, ℓ₀, hC, hℓ₀, fun N _ hN τ₀ n₀ X A B H n hn j x hx y hy => ?_⟩
  obtain ⟨m0, m1, m2, m3, m4, m5⟩ := h N hN τ₀ n₀ X A B H n hn j x hx y hy
  have hℓ : 0 < 2 * Real.pi / N := by
    have : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N))
    positivity
  have h1 := H.time_mem (m := n) hn.le
  have h2 := H.time_mem (m := n + 1) hn
  push_cast at h2
  have hxs : x ∈ Icc t₀ t₁ := ⟨h1.1.trans hx.1, hx.2.trans (by linarith [h2.2])⟩
  have h01 : t₀ < t₁ := by
    have : 0 ≤ (n : ℝ) * (2 * Real.pi / N) := by positivity
    linarith [h2.2, H.start]
  have hvac := sol.ricci_flat h0 h01 (z := (x, y)) hxs
  exact ⟨m0, m1, m2, m3, m4, hvac, m5 hvac⟩

end GowdySmoothReference

end

end RenewalGeometry.GowdyStaggered.HermiteReadout
