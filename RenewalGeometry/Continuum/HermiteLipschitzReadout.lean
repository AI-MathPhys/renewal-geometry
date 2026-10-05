/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.SpectralGalerkinMidpoint

/-!
# Taylor, midpoint and cubic Hermite estimates under Lipschitz derivative bounds

Generic infrastructure (normed spaces, no renewal notions) for `thm:generated-dynamics` of the
Einstein–Standard-Model action-closure manuscript (`eq:generated-time-rate`,
`eq:generated-Hermite`).  The trajectories of the semidiscrete (spectral Galerkin) system are
`C²` in time with a **Lipschitz** second derivative (the generator is only `C¹`, so a third
derivative is not available); the estimates of `SpectralGalerkin` (which assume a bounded third
derivative) are re-proved here under the Lipschitz hypotheses and with one-sided derivatives
**within** the time interval `[a, b]` (the Galerkin ODE holds within `[0, T]`).

* `norm_le_of_deriv_within_segment` — the comparison principle on a segment from derivatives
  within the segment.
* `taylor_lip1`, `taylor_lip2` — `‖g(t+h) - g(t) - h g'(t)‖ ≤ L h²/2` if `g'` is `L`-Lipschitz, and
  `‖z(t+h) - z(t) - h z'(t) - (h²/2) z''(t)‖ ≤ L h³/6` if `z''` is `L`-Lipschitz.
* **`midpoint_consistency_lip`** — `‖(z(t) + z(t+τ))/2 - z(t+τ/2)‖ ≤ 3M₂τ²/8` (`z'` `M₂`-Lipschitz)
  and `‖z(t+τ) - z(t) - τ z'(t+τ/2)‖ ≤ 7L₃τ³/24` (`z''` `L₃`-Lipschitz): the local truncation
  residual of the implicit midpoint rule is `O(τ²)`.
* **`hermite_accuracy_lip`**, **`hermite_error_lip`** — the cubic Hermite readout
  (`SpectralGalerkin.hermite`) of exact nodal data is accurate to `2M₂τ²` (values), `2L₃τ²` (first
  derivatives) and `4L₃τ` (second derivatives), and with perturbed nodal data the errors add the
  stability terms of `SpectralGalerkin.hermite_stability` (the mechanism of `eq:generated-Hermite`).
-/

open Set Filter Topology Metric

namespace RenewalGeometry.HermiteLip

noncomputable section

open CubicHermite SpectralGalerkin

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Comparison principle on a segment** from derivatives within the segment. -/
theorem norm_le_of_deriv_within_segment {f f' : ℝ → F} {t h : ℝ} {B B' : ℝ → ℝ} (hh : 0 ≤ h)
    (hf : ∀ x ∈ Icc t (t + h), HasDerivWithinAt f (f' x) (Icc t (t + h)) x)
    (h0 : ‖f t‖ ≤ B t) (hB : ∀ x, HasDerivAt B (B' x) x)
    (hb : ∀ x ∈ Ico t (t + h), ‖f' x‖ ≤ B' x) : ‖f (t + h)‖ ≤ B (t + h) :=
  image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (fun x hx => (hf x hx).continuousWithinAt)
    (fun x hx => (hf x (Ico_subset_Icc_self hx)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem hx)) h0 hB hb ⟨by linarith, le_rfl⟩

theorem hasDerivAt_quad (L t x : ℝ) :
    HasDerivAt (fun x => L * (x - t) ^ 2 / 2) (L * (x - t)) x := by
  have h1 : HasDerivAt (fun x : ℝ => x - t) 1 x := (hasDerivAt_id' x).sub_const t
  exact (((h1.fun_pow 2).const_mul L).div_const 2).congr_deriv (by norm_num; ring)

theorem hasDerivAt_cub (L t x : ℝ) :
    HasDerivAt (fun x => L * (x - t) ^ 3 / 6) (L * (x - t) ^ 2 / 2) x := by
  have h1 : HasDerivAt (fun x : ℝ => x - t) 1 x := (hasDerivAt_id' x).sub_const t
  exact (((h1.fun_pow 3).const_mul L).div_const 6).congr_deriv (by norm_num; ring)

/-- **First-order Taylor bound with a Lipschitz derivative**: if `g` has derivative `g'` within
`[a, b]` and `‖g'(x) - g'(y)‖ ≤ L|x - y|` there, then `‖g(t+h) - g(t) - h g'(t)‖ ≤ L h²/2`. -/
theorem taylor_lip1 {g g' : ℝ → F} {a b L : ℝ}
    (hg : ∀ x ∈ Icc a b, HasDerivWithinAt g (g' x) (Icc a b) x)
    (hL : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, ‖g' x - g' y‖ ≤ L * |x - y|)
    {t h : ℝ} (ht : a ≤ t) (hh : 0 ≤ h) (hth : t + h ≤ b) :
    ‖g (t + h) - g t - h • g' t‖ ≤ L * h ^ 2 / 2 := by
  have hsub : Icc t (t + h) ⊆ Icc a b := Icc_subset_Icc ht hth
  set f : ℝ → F := fun x => g x - g t - (x - t) • g' t with hf
  have hfd : ∀ x ∈ Icc t (t + h), HasDerivWithinAt f (g' x - g' t) (Icc t (t + h)) x := by
    intro x hx
    have h1 := (hg x (hsub hx)).mono hsub
    have h2 : HasDerivWithinAt (fun x : ℝ => (x - t) • g' t) (g' t) (Icc t (t + h)) x := by
      simpa using (((hasDerivAt_id x).sub_const t).smul_const (g' t)).hasDerivWithinAt
    exact (h1.sub_const (g t)).sub h2
  have key := norm_le_of_deriv_within_segment (f := f) (B := fun x => L * (x - t) ^ 2 / 2)
    (B' := fun x => L * (x - t)) hh hfd (by simp [hf]) (fun x => hasDerivAt_quad L t x)
    (fun x hx => by
      have := hL x (hsub (Ico_subset_Icc_self hx)) t (hsub ⟨le_rfl, by linarith⟩)
      rwa [abs_of_nonneg (by linarith [hx.1])] at this)
  simpa [hf] using key

/-- **Second-order Taylor bound with a Lipschitz second derivative**:
`‖z(t+h) - z(t) - h z'(t) - (h²/2) z''(t)‖ ≤ L h³/6`. -/
theorem taylor_lip2 {z z' z'' : ℝ → F} {a b L : ℝ}
    (hz : ∀ x ∈ Icc a b, HasDerivWithinAt z (z' x) (Icc a b) x)
    (hz' : ∀ x ∈ Icc a b, HasDerivWithinAt z' (z'' x) (Icc a b) x)
    (hL : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, ‖z'' x - z'' y‖ ≤ L * |x - y|)
    {t h : ℝ} (ht : a ≤ t) (hh : 0 ≤ h) (hth : t + h ≤ b) :
    ‖z (t + h) - z t - h • z' t - (h ^ 2 / 2) • z'' t‖ ≤ L * h ^ 3 / 6 := by
  have hsub : Icc t (t + h) ⊆ Icc a b := Icc_subset_Icc ht hth
  set f : ℝ → F := fun x => z x - z t - (x - t) • z' t - ((x - t) ^ 2 / 2) • z'' t with hf
  have hfd : ∀ x ∈ Icc t (t + h), HasDerivWithinAt f (z' x - z' t - (x - t) • z'' t)
      (Icc t (t + h)) x := by
    intro x hx
    have h1 := (hz x (hsub hx)).mono hsub
    have h2 : HasDerivWithinAt (fun x : ℝ => (x - t) • z' t) (z' t) (Icc t (t + h)) x := by
      simpa using (((hasDerivAt_id x).sub_const t).smul_const (z' t)).hasDerivWithinAt
    have h3 : HasDerivWithinAt (fun x : ℝ => ((x - t) ^ 2 / 2) • z'' t) ((x - t) • z'' t)
        (Icc t (t + h)) x := by
      have h1 : HasDerivAt (fun x : ℝ => x - t) 1 x := (hasDerivAt_id' x).sub_const t
      exact (((h1.fun_pow 2).div_const 2).smul_const (z'' t)).hasDerivWithinAt.congr_deriv
        (by norm_num)
    exact ((h1.sub_const (z t)).sub h2).sub h3
  have key := norm_le_of_deriv_within_segment (f := f) (B := fun x => L * (x - t) ^ 3 / 6)
    (B' := fun x => L * (x - t) ^ 2 / 2) hh hfd (by simp [hf]) (fun x => hasDerivAt_cub L t x)
    (fun x hx => by
      have := taylor_lip1 hz' hL ht (h := x - t) (by linarith [hx.1])
        (by linarith [hx.2, hth])
      simpa using this)
  simpa [hf] using key

theorem lip_of_deriv_bound {g g' : ℝ → F} {a b M : ℝ}
    (hg : ∀ x ∈ Icc a b, HasDerivWithinAt g (g' x) (Icc a b) x)
    (hM : ∀ x ∈ Icc a b, ‖g' x‖ ≤ M) :
    ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, ‖g x - g y‖ ≤ M * |x - y| := by
  intro x hx y hy
  rcases le_total y x with hxy | hxy
  · have := norm_image_sub_le_of_norm_deriv_le_segment' (f := g) (a := y) (b := x)
      (fun z hz => (hg z ⟨hy.1.trans hz.1, hz.2.trans hx.2⟩).mono
        (Icc_subset_Icc hy.1 hx.2))
      (fun z hz => hM z ⟨hy.1.trans hz.1, hz.2.le.trans hx.2⟩) x ⟨hxy, le_rfl⟩
    rwa [abs_of_nonneg (by linarith)]
  · have := norm_image_sub_le_of_norm_deriv_le_segment' (f := g) (a := x) (b := y)
      (fun z hz => (hg z ⟨hx.1.trans hz.1, hz.2.trans hy.2⟩).mono
        (Icc_subset_Icc hx.1 hy.2))
      (fun z hz => hM z ⟨hx.1.trans hz.1, hz.2.le.trans hy.2⟩) y ⟨hxy, le_rfl⟩
    rw [norm_sub_rev, abs_sub_comm, abs_of_nonneg (by linarith)]
    exact this

/-- **Midpoint average under a Lipschitz derivative**:
`‖(z(t) + z(t+τ))/2 - z(t+τ/2)‖ ≤ 3M₂τ²/8` when `z'` is `M₂`-Lipschitz. -/
theorem midpoint_avg_lip {z z' : ℝ → F} {a b M₂ : ℝ}
    (hz : ∀ x ∈ Icc a b, HasDerivWithinAt z (z' x) (Icc a b) x)
    (hM₂ : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, ‖z' x - z' y‖ ≤ M₂ * |x - y|)
    {t τ : ℝ} (ht : a ≤ t) (hτ : 0 ≤ τ) (htτ : t + τ ≤ b) :
    ‖(1 / 2 : ℝ) • (z t + z (t + τ)) - z (t + τ / 2)‖ ≤ 3 * M₂ * τ ^ 2 / 8 := by
  have h1 := taylor_lip1 hz hM₂ ht hτ htτ
  have h2 := taylor_lip1 hz hM₂ ht (by linarith : 0 ≤ τ / 2) (by linarith)
  have e : (1 / 2 : ℝ) • (z t + z (t + τ)) - z (t + τ / 2) =
      (1 / 2 : ℝ) • (z (t + τ) - z t - τ • z' t) - (z (t + τ / 2) - z t - (τ / 2) • z' t) := by
    rw [smul_sub, smul_sub, smul_add, smul_smul]; module
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  nlinarith

/-- **Midpoint step under a Lipschitz second derivative**:
`‖z(t+τ) - z(t) - τ z'(t+τ/2)‖ ≤ 7L₃τ³/24` when `z''` is `L₃`-Lipschitz. -/
theorem midpoint_step_lip {z z' z'' : ℝ → F} {a b L₃ : ℝ}
    (hz : ∀ x ∈ Icc a b, HasDerivWithinAt z (z' x) (Icc a b) x)
    (hz' : ∀ x ∈ Icc a b, HasDerivWithinAt z' (z'' x) (Icc a b) x)
    (hL₃ : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, ‖z'' x - z'' y‖ ≤ L₃ * |x - y|)
    {t τ : ℝ} (ht : a ≤ t) (hτ : 0 ≤ τ) (htτ : t + τ ≤ b) :
    ‖z (t + τ) - z t - τ • z' (t + τ / 2)‖ ≤ 7 * L₃ * τ ^ 3 / 24 := by
  have h1 := taylor_lip2 hz hz' hL₃ ht hτ htτ
  have h2 := taylor_lip1 hz' hL₃ ht (by linarith : 0 ≤ τ / 2) (by linarith)
  have e : z (t + τ) - z t - τ • z' (t + τ / 2) =
      (z (t + τ) - z t - τ • z' t - (τ ^ 2 / 2) • z'' t) -
        τ • (z' (t + τ / 2) - z' t - (τ / 2) • z'' t) := by
    rw [smul_sub, smul_sub, smul_smul]; module
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ]
  have : τ * ‖z' (t + τ / 2) - z' t - (τ / 2) • z'' t‖ ≤ τ * (L₃ * (τ / 2) ^ 2 / 2) :=
    mul_le_mul_of_nonneg_left h2 hτ
  nlinarith

/-- **Consistency of the midpoint rule under Lipschitz bounds** (both estimates). -/
theorem midpoint_consistency_lip {z z' z'' : ℝ → F} {a b M₂ L₃ : ℝ}
    (hz : ∀ x ∈ Icc a b, HasDerivWithinAt z (z' x) (Icc a b) x)
    (hz' : ∀ x ∈ Icc a b, HasDerivWithinAt z' (z'' x) (Icc a b) x)
    (hM₂ : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, ‖z' x - z' y‖ ≤ M₂ * |x - y|)
    (hL₃ : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, ‖z'' x - z'' y‖ ≤ L₃ * |x - y|)
    {t τ : ℝ} (ht : a ≤ t) (hτ : 0 ≤ τ) (htτ : t + τ ≤ b) :
    ‖(1 / 2 : ℝ) • (z t + z (t + τ)) - z (t + τ / 2)‖ ≤ 3 * M₂ * τ ^ 2 / 8 ∧
      ‖z (t + τ) - z t - τ • z' (t + τ / 2)‖ ≤ 7 * L₃ * τ ^ 3 / 24 :=
  ⟨midpoint_avg_lip hz hM₂ ht hτ htτ, midpoint_step_lip hz hz' hL₃ ht hτ htτ⟩

/-- **Accuracy of the Hermite readout on exact data, Lipschitz form**: for a `C²` trajectory on
`[t₀, t₀ + τ]` (derivatives within the cell) with `z'` `M₂`-Lipschitz and `z''` `M₃`-Lipschitz, the Hermite interpolant of the exact nodal values
and slopes satisfies (`θ ∈ [0, 1]`)
`‖hermite - z‖ ≤ 2 M₂ τ²`, `‖hermiteD - z'‖ ≤ 2 M₃ τ²`, `‖hermiteDD - z''‖ ≤ 4 M₃ τ`. -/
theorem hermite_accuracy_lip {z z' z'' : ℝ → F} {t₀ τ M₂ M₃ θ : ℝ} (hτ : 0 < τ)
    (hθ : θ ∈ Icc (0 : ℝ) 1)
    (hz : ∀ x ∈ Icc t₀ (t₀ + τ), HasDerivWithinAt z (z' x) (Icc t₀ (t₀ + τ)) x)
    (hz' : ∀ x ∈ Icc t₀ (t₀ + τ), HasDerivWithinAt z' (z'' x) (Icc t₀ (t₀ + τ)) x)
    (hM₂ : ∀ x ∈ Icc t₀ (t₀ + τ), ∀ y ∈ Icc t₀ (t₀ + τ), ‖z' x - z' y‖ ≤ M₂ * |x - y|)
    (hM₃ : ∀ x ∈ Icc t₀ (t₀ + τ), ∀ y ∈ Icc t₀ (t₀ + τ), ‖z'' x - z'' y‖ ≤ M₃ * |x - y|) :
    ‖hermite τ (z t₀) (z (t₀ + τ)) (z' t₀) (z' (t₀ + τ)) θ - z (t₀ + θ * τ)‖ ≤ 2 * M₂ * τ ^ 2 ∧
      ‖hermiteD τ (z t₀) (z (t₀ + τ)) (z' t₀) (z' (t₀ + τ)) θ - z' (t₀ + θ * τ)‖ ≤
        2 * M₃ * τ ^ 2 ∧
      ‖hermiteDD τ (z t₀) (z (t₀ + τ)) (z' t₀) (z' (t₀ + τ)) θ - z'' (t₀ + θ * τ)‖ ≤
        4 * M₃ * τ := by
  obtain ⟨hθ0, hθ1⟩ := hθ
  have hθτ0 : 0 ≤ θ * τ := mul_nonneg hθ0 hτ.le
  have hθτ1 : t₀ + θ * τ ≤ t₀ + τ := by nlinarith
  have hH := abs_basisH_le ⟨hθ0, hθ1⟩
  have hG := abs_basisG_le ⟨hθ0, hθ1⟩
  have hHD := abs_basisHD_le ⟨hθ0, hθ1⟩
  have hGD := abs_basisGD_le ⟨hθ0, hθ1⟩
  have hHDD := abs_basisHDD_le ⟨hθ0, hθ1⟩
  have hGDD := abs_basisGDD_le ⟨hθ0, hθ1⟩
  have hmem0 : t₀ ∈ Icc t₀ (t₀ + τ) := ⟨le_rfl, by linarith⟩
  have hmem1 : t₀ + τ ∈ Icc t₀ (t₀ + τ) := ⟨by linarith, le_rfl⟩
  have hM₂0 : 0 ≤ M₂ := by
    have h := (norm_nonneg _).trans (hM₂ (t₀ + τ) hmem1 t₀ hmem0)
    rw [show t₀ + τ - t₀ = τ by ring, abs_of_pos hτ] at h
    exact nonneg_of_mul_nonneg_left h hτ
  have hM₃0 : 0 ≤ M₃ := by
    have h := (norm_nonneg _).trans (hM₃ (t₀ + τ) hmem1 t₀ hmem0)
    rw [show t₀ + τ - t₀ = τ by ring, abs_of_pos hτ] at h
    exact nonneg_of_mul_nonneg_left h hτ
  have hτi : τ⁻¹ * τ = 1 := inv_mul_cancel₀ hτ.ne'
  -- basis identities
  have i1 : basisH 0 θ + basisH 1 θ = 1 := basisH_sum θ
  have i2 : basisH 1 θ + basisG 0 θ + basisG 1 θ = θ := by
    rw [basisH_one, basisG_zero, basisG_one]; ring
  have i3 : basisHD 0 θ + basisHD 1 θ = 0 := basisHD_sum θ
  have i4 : basisHD 1 θ + basisGD 0 θ + basisGD 1 θ = 1 := by
    rw [basisHD_one, basisGD_zero, basisGD_one]; ring
  have i5 : basisHD 1 θ / 2 + basisGD 1 θ = θ := by
    rw [basisHD_one, basisGD_one]; ring
  have i6 : basisHDD 0 θ + basisHDD 1 θ = 0 := basisHDD_sum θ
  have i7 : basisHDD 1 θ + basisGDD 0 θ + basisGDD 1 θ = 0 := by
    rw [basisHDD_one, basisGDD_zero, basisGDD_one]; ring
  have i8 : basisHDD 1 θ / 2 + basisGDD 1 θ = 1 := by
    rw [basisHDD_one, basisGDD_one]; ring
  refine ⟨?_, ?_, ?_⟩
  · -- values
    set R1 := z (t₀ + τ) - z t₀ - τ • z' t₀
    set R2 := z' (t₀ + τ) - z' t₀
    set R3 := z (t₀ + θ * τ) - z t₀ - (θ * τ) • z' t₀
    have b1 : ‖R1‖ ≤ M₂ * τ ^ 2 / 2 := taylor_lip1 hz hM₂ le_rfl hτ.le le_rfl
    have b3 : ‖R3‖ ≤ M₂ * (θ * τ) ^ 2 / 2 := taylor_lip1 hz hM₂ le_rfl hθτ0 hθτ1
    have b2 : ‖R2‖ ≤ M₂ * τ := by
      have := hM₂ (t₀ + τ) hmem1 t₀ hmem0
      rwa [show t₀ + τ - t₀ = τ by ring, abs_of_pos hτ] at this
    have e : hermite τ (z t₀) (z (t₀ + τ)) (z' t₀) (z' (t₀ + τ)) θ - z (t₀ + θ * τ) =
        basisH 1 θ • R1 + (τ * basisG 1 θ) • R2 - R3 := by
      have hz1 : z (t₀ + τ) = z t₀ + τ • z' t₀ + R1 := by simp only [R1]; abel
      have hz1' : z' (t₀ + τ) = z' t₀ + R2 := by simp only [R2]; abel
      have hzθ : z (t₀ + θ * τ) = z t₀ + (θ * τ) • z' t₀ + R3 := by simp only [R3]; abel
      unfold hermite
      rw [hz1, hz1', hzθ]
      have h0 : basisH 0 θ = 1 - basisH 1 θ := by linarith
      have hG0 : basisG 0 θ = θ - basisH 1 θ - basisG 1 θ := by linarith
      rw [h0, hG0]
      simp only [smul_add, add_smul, sub_smul, smul_smul, one_smul]
      module
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    refine (add_le_add (norm_add_le _ _) le_rfl).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_pos hτ]
    have := norm_nonneg R1; have := norm_nonneg R2
    have hθ2 : (θ * τ) ^ 2 ≤ τ ^ 2 := by
      have : θ * τ ≤ τ := by nlinarith
      exact pow_le_pow_left₀ hθτ0 this 2
    calc |basisH 1 θ| * ‖R1‖ + τ * |basisG 1 θ| * ‖R2‖ + ‖R3‖
        ≤ 1 * (M₂ * τ ^ 2 / 2) + τ * 1 * (M₂ * τ) + M₂ * (θ * τ) ^ 2 / 2 := by
          gcongr
          · exact hH 1
          · exact hG 1
      _ ≤ 1 * (M₂ * τ ^ 2 / 2) + τ * 1 * (M₂ * τ) + M₂ * τ ^ 2 / 2 := by gcongr
      _ = 2 * M₂ * τ ^ 2 := by ring
  · -- first derivatives
    set R1 := z (t₀ + τ) - z t₀ - τ • z' t₀ - (τ ^ 2 / 2) • z'' t₀
    set R2 := z' (t₀ + τ) - z' t₀ - τ • z'' t₀
    set R3 := z' (t₀ + θ * τ) - z' t₀ - (θ * τ) • z'' t₀
    have b1 : ‖R1‖ ≤ M₃ * τ ^ 3 / 6 := taylor_lip2 hz hz' hM₃ le_rfl hτ.le le_rfl
    have b2 : ‖R2‖ ≤ M₃ * τ ^ 2 / 2 := taylor_lip1 hz' hM₃ le_rfl hτ.le le_rfl
    have b3 : ‖R3‖ ≤ M₃ * (θ * τ) ^ 2 / 2 := taylor_lip1 hz' hM₃ le_rfl hθτ0 hθτ1
    have e : hermiteD τ (z t₀) (z (t₀ + τ)) (z' t₀) (z' (t₀ + τ)) θ - z' (t₀ + θ * τ) =
        (τ⁻¹ * basisHD 1 θ) • R1 + basisGD 1 θ • R2 - R3 := by
      have hz1 : z (t₀ + τ) = z t₀ + τ • z' t₀ + (τ ^ 2 / 2) • z'' t₀ + R1 := by
        simp only [R1]; abel
      have hz1' : z' (t₀ + τ) = z' t₀ + τ • z'' t₀ + R2 := by simp only [R2]; abel
      have hzθ : z' (t₀ + θ * τ) = z' t₀ + (θ * τ) • z'' t₀ + R3 := by simp only [R3]; abel
      unfold hermiteD
      rw [hz1, hz1', hzθ]
      have h0 : basisHD 0 θ = -basisHD 1 θ := by linarith
      have hG0 : basisGD 0 θ = 1 - basisHD 1 θ - basisGD 1 θ := by linarith
      have hG1 : basisGD 1 θ = θ - basisHD 1 θ / 2 := by linarith
      rw [h0, hG0]
      simp only [smul_add, add_smul, sub_smul, smul_smul, one_smul, neg_smul, smul_neg]
      have k1 : τ⁻¹ * (basisHD 1 θ * τ) = basisHD 1 θ := by
        rw [mul_comm, mul_assoc, mul_comm τ, hτi, mul_one]
      have k2 : τ⁻¹ * (basisHD 1 θ * (τ ^ 2 / 2)) = (basisHD 1 θ / 2) * τ := by
        field_simp
      rw [k1, k2]
      conv_lhs => rw [show basisGD 1 θ * τ = (θ - basisHD 1 θ / 2) * τ by rw [hG1]]
      simp only [sub_smul, mul_smul]
      module
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    refine (add_le_add (norm_add_le _ _) le_rfl).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
      abs_of_pos (inv_pos.mpr hτ)]
    have := norm_nonneg R1; have := norm_nonneg R2
    have hθ2 : (θ * τ) ^ 2 ≤ τ ^ 2 := by
      have : θ * τ ≤ τ := by nlinarith
      exact pow_le_pow_left₀ hθτ0 this 2
    calc τ⁻¹ * |basisHD 1 θ| * ‖R1‖ + |basisGD 1 θ| * ‖R2‖ + ‖R3‖
        ≤ τ⁻¹ * (3 / 2) * (M₃ * τ ^ 3 / 6) + 1 * (M₃ * τ ^ 2 / 2) + M₃ * (θ * τ) ^ 2 / 2 := by
          gcongr
          · exact hHD 1
          · exact hGD 1
      _ ≤ τ⁻¹ * (3 / 2) * (M₃ * τ ^ 3 / 6) + 1 * (M₃ * τ ^ 2 / 2) + M₃ * τ ^ 2 / 2 := by gcongr
      _ = (τ⁻¹ * τ) * (M₃ * τ ^ 2 / 4) + M₃ * τ ^ 2 := by ring
      _ ≤ 2 * M₃ * τ ^ 2 := by rw [hτi]; nlinarith [sq_nonneg τ]
  · -- second derivatives
    set R1 := z (t₀ + τ) - z t₀ - τ • z' t₀ - (τ ^ 2 / 2) • z'' t₀
    set R2 := z' (t₀ + τ) - z' t₀ - τ • z'' t₀
    set R3 := z'' (t₀ + θ * τ) - z'' t₀
    have b1 : ‖R1‖ ≤ M₃ * τ ^ 3 / 6 := taylor_lip2 hz hz' hM₃ le_rfl hτ.le le_rfl
    have b2 : ‖R2‖ ≤ M₃ * τ ^ 2 / 2 := taylor_lip1 hz' hM₃ le_rfl hτ.le le_rfl
    have b3 : ‖R3‖ ≤ M₃ * (θ * τ) := by
      have := hM₃ (t₀ + θ * τ) ⟨by linarith, hθτ1⟩ t₀ hmem0
      rwa [show t₀ + θ * τ - t₀ = θ * τ by ring, abs_of_nonneg hθτ0] at this
    have e : hermiteDD τ (z t₀) (z (t₀ + τ)) (z' t₀) (z' (t₀ + τ)) θ - z'' (t₀ + θ * τ) =
        (τ⁻¹ ^ 2 * basisHDD 1 θ) • R1 + (τ⁻¹ * basisGDD 1 θ) • R2 - R3 := by
      have hz1 : z (t₀ + τ) = z t₀ + τ • z' t₀ + (τ ^ 2 / 2) • z'' t₀ + R1 := by
        simp only [R1]; abel
      have hz1' : z' (t₀ + τ) = z' t₀ + τ • z'' t₀ + R2 := by simp only [R2]; abel
      have hzθ : z'' (t₀ + θ * τ) = z'' t₀ + R3 := by simp only [R3]; abel
      unfold hermiteDD
      rw [hz1, hz1', hzθ]
      have h0 : basisHDD 0 θ = -basisHDD 1 θ := by linarith
      have hG0 : basisGDD 0 θ = -basisHDD 1 θ - basisGDD 1 θ := by linarith
      have hG1 : basisGDD 1 θ = 1 - basisHDD 1 θ / 2 := by linarith
      rw [h0, hG0]
      simp only [smul_add, add_smul, sub_smul, smul_smul, one_smul, neg_smul, smul_neg]
      have k1 : τ⁻¹ ^ 2 * (basisHDD 1 θ * τ) = τ⁻¹ * basisHDD 1 θ := by
        field_simp
      have k2 : τ⁻¹ ^ 2 * (basisHDD 1 θ * (τ ^ 2 / 2)) = basisHDD 1 θ / 2 := by
        field_simp
      have k3 : τ⁻¹ * (basisGDD 1 θ * τ) = basisGDD 1 θ := by
        field_simp
      rw [k1, k2, k3, hG1]
      simp only [sub_smul, neg_sub, smul_sub, one_smul, neg_smul]
      module
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    refine (add_le_add (norm_add_le _ _) le_rfl).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_pos (by positivity : (0 : ℝ) < τ⁻¹ ^ 2), abs_of_pos (inv_pos.mpr hτ)]
    have := norm_nonneg R1; have := norm_nonneg R2
    have hθ1' : θ * τ ≤ τ := by nlinarith
    calc τ⁻¹ ^ 2 * |basisHDD 1 θ| * ‖R1‖ + τ⁻¹ * |basisGDD 1 θ| * ‖R2‖ + ‖R3‖
        ≤ τ⁻¹ ^ 2 * 6 * (M₃ * τ ^ 3 / 6) + τ⁻¹ * 4 * (M₃ * τ ^ 2 / 2) + M₃ * (θ * τ) := by
          gcongr
          · exact hHDD 1
          · exact hGDD 1
      _ ≤ τ⁻¹ ^ 2 * 6 * (M₃ * τ ^ 3 / 6) + τ⁻¹ * 4 * (M₃ * τ ^ 2 / 2) + M₃ * τ := by gcongr
      _ = (τ⁻¹ * τ) ^ 2 * (M₃ * τ) + (τ⁻¹ * τ) * (2 * M₃ * τ) + M₃ * τ := by ring
      _ = 4 * M₃ * τ := by rw [hτi]; ring

/-- **Error of the Hermite readout, Lipschitz form** (`eq:generated-Hermite` mechanism): nodal value errors
`δU_a = U_a - z(t_a)`, nodal slope errors `δV_a = V_a - z'(t_a)` and the exact-data accuracy add up:
values `≤ ‖δU₀‖ + ‖δU₁‖ + τ(‖δV₀‖ + ‖δV₁‖) + 2M₂τ²`, first derivatives
`≤ (3/2)τ⁻¹‖δU₁ - δU₀‖ + ‖δV₀‖ + ‖δV₁‖ + 2M₃τ²`, second derivatives
`≤ 6τ⁻²‖δU₁ - δU₀‖ + 4τ⁻¹(‖δV₀‖ + ‖δV₁‖) + 4M₃τ`. -/
theorem hermite_error_lip {z z' z'' : ℝ → F} {t₀ τ M₂ M₃ θ : ℝ} (hτ : 0 < τ)
    (hθ : θ ∈ Icc (0 : ℝ) 1)
    (hz : ∀ x ∈ Icc t₀ (t₀ + τ), HasDerivWithinAt z (z' x) (Icc t₀ (t₀ + τ)) x)
    (hz' : ∀ x ∈ Icc t₀ (t₀ + τ), HasDerivWithinAt z' (z'' x) (Icc t₀ (t₀ + τ)) x)
    (hM₂ : ∀ x ∈ Icc t₀ (t₀ + τ), ∀ y ∈ Icc t₀ (t₀ + τ), ‖z' x - z' y‖ ≤ M₂ * |x - y|)
    (hM₃ : ∀ x ∈ Icc t₀ (t₀ + τ), ∀ y ∈ Icc t₀ (t₀ + τ), ‖z'' x - z'' y‖ ≤ M₃ * |x - y|)
    (U₀ U₁ V₀ V₁ : F) :
    ‖hermite τ U₀ U₁ V₀ V₁ θ - z (t₀ + θ * τ)‖ ≤
        ‖U₀ - z t₀‖ + ‖U₁ - z (t₀ + τ)‖ + τ * (‖V₀ - z' t₀‖ + ‖V₁ - z' (t₀ + τ)‖) +
          2 * M₂ * τ ^ 2 ∧
      ‖hermiteD τ U₀ U₁ V₀ V₁ θ - z' (t₀ + θ * τ)‖ ≤
        3 / 2 * τ⁻¹ * ‖(U₁ - z (t₀ + τ)) - (U₀ - z t₀)‖ +
          (‖V₀ - z' t₀‖ + ‖V₁ - z' (t₀ + τ)‖) + 2 * M₃ * τ ^ 2 ∧
      ‖hermiteDD τ U₀ U₁ V₀ V₁ θ - z'' (t₀ + θ * τ)‖ ≤
        6 * τ⁻¹ ^ 2 * ‖(U₁ - z (t₀ + τ)) - (U₀ - z t₀)‖ +
          4 * τ⁻¹ * (‖V₀ - z' t₀‖ + ‖V₁ - z' (t₀ + τ)‖) + 4 * M₃ * τ := by
  obtain ⟨a1, a2, a3⟩ := hermite_accuracy_lip (θ := θ) hτ hθ hz hz' hM₂ hM₃
  obtain ⟨s1, s2, s3⟩ := hermite_stability hτ hθ (U₀ - z t₀) (U₁ - z (t₀ + τ)) (V₀ - z' t₀)
    (V₁ - z' (t₀ + τ))
  refine ⟨?_, ?_, ?_⟩
  · have e : hermite τ U₀ U₁ V₀ V₁ θ - z (t₀ + θ * τ) =
        (hermite τ U₀ U₁ V₀ V₁ θ - hermite τ (z t₀) (z (t₀ + τ)) (z' t₀) (z' (t₀ + τ)) θ) +
          (hermite τ (z t₀) (z (t₀ + τ)) (z' t₀) (z' (t₀ + τ)) θ - z (t₀ + θ * τ)) := by abel
    rw [e, hermite_sub]
    exact (norm_add_le _ _).trans (add_le_add s1 a1)
  · have e : hermiteD τ U₀ U₁ V₀ V₁ θ - z' (t₀ + θ * τ) =
        (hermiteD τ U₀ U₁ V₀ V₁ θ - hermiteD τ (z t₀) (z (t₀ + τ)) (z' t₀) (z' (t₀ + τ)) θ) +
          (hermiteD τ (z t₀) (z (t₀ + τ)) (z' t₀) (z' (t₀ + τ)) θ - z' (t₀ + θ * τ)) := by abel
    rw [e, hermiteD_sub]
    exact (norm_add_le _ _).trans (add_le_add s2 a2)
  · have e : hermiteDD τ U₀ U₁ V₀ V₁ θ - z'' (t₀ + θ * τ) =
        (hermiteDD τ U₀ U₁ V₀ V₁ θ - hermiteDD τ (z t₀) (z (t₀ + τ)) (z' t₀) (z' (t₀ + τ)) θ) +
          (hermiteDD τ (z t₀) (z (t₀ + τ)) (z' t₀) (z' (t₀ + τ)) θ - z'' (t₀ + θ * τ)) := by
      abel
    rw [e, hermiteDD_sub]
    exact (norm_add_le _ _).trans (add_le_add s3 a3)


end

end RenewalGeometry.HermiteLip
