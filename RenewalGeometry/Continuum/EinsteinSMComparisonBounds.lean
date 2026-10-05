/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.EinsteinSMComparisonRegulator

/-!
# Uniform bounds for the comparison regulator (reconstructions, tests and lifts)

Infrastructure for `EinsteinSMMeshConsistency.lean` (`prop:mesh-consistency`, Einstein–Standard-Model
action-closure manuscript):

* `isC11_recon_samp` (**`eq:smooth-reconstruction-estimate`** in `C^{1,1}` form): the
  reconstruction of the samples of a `C^{1,1}` function with constant `B` is `C^{1,1}` with constant
  `cRec B`, uniformly in `h ≤ 1`; `norm_recon_samp_sub_le'`, `norm_fderiv_recon_samp_sub_le` give
  the `O(h)` value and derivative errors.
* `isC11_of_isCylTest`: a test section is `C^{1,1}` with constant `‖·‖_{C^r}` (`r ≥ 2`).
* `tper`: the time periodization (period `P`) of a section supported in a time window
  `[a,b] ⊂ (0,P)`; `isC11_tper`, `tper_periodic`, `tper_eq` (equal to the section on the
  fundamental period).
* `liftRec_eq_sampleRec_tper`: the test lift `𝓘_h v` is the nodal sampling of the time-periodized
  complete variation `v̂`.
-/

open MeasureTheory Filter Topology Set Metric
open scoped ContDiff ENNReal NNReal

noncomputable section

set_option linter.unusedSectionVars false

namespace RenewalGeometry
namespace EinsteinSM
namespace Comparison

open SobolevOpen (pd)
open CardinalQI C11Calculus

/-! ### Reconstructions of sampled `C^{1,1}` functions -/

section Recon

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The constant of `isC11_recon_samp` in dimension `4`. -/
def cRec : ℝ := 1 + cVal 4 + cDer 4 + cLip 4

theorem one_le_cRec : 1 ≤ cRec := by
  unfold cRec
  have := cVal_nonneg (d := 4); have := cDer_nonneg (d := 4); have := cLip_nonneg (d := 4)
  linarith

/-- **`eq:smooth-reconstruction-estimate`** (`C^{1,1}` form): for `0 < h ≤ 1`, the reconstruction
of the samples of a `C^{1,1}` function with constant `B` is `C^{1,1}` with constant `cRec B`. -/
theorem isC11_recon_samp {g : E4 → W} {B : ℝ} (hg : IsC11 g B) {h : ℝ} (hh : 0 < h)
    (hh1 : h ≤ 1) : IsC11 (recon h (samp h g)) (cRec * B) := by
  have hB := hg.nonneg
  have hv := cVal_nonneg (d := 4); have hd := cDer_nonneg (d := 4); have hl := cLip_nonneg (d := 4)
  have hf : ∀ y, HasFDerivAt g (fderiv ℝ g y) y := hg.hasFDerivAt
  refine ⟨fun y => by rw [fderiv_recon hh]; exact hasFDerivAt_recon hh _ y, fun y => ?_,
    fun y => ?_, fun y z => ?_⟩
  · have e1 := norm_recon_samp_sub_le hh hf hg.norm_fderiv_le y
    calc ‖recon h (samp h g) y‖ ≤ ‖g y‖ + ‖recon h (samp h g) y - g y‖ := by
          have := norm_add_le (g y) (recon h (samp h g) y - g y)
          rwa [add_sub_cancel] at this
      _ ≤ B + cVal 4 * B * h := add_le_add (hg.norm_le y) e1
      _ ≤ cRec * B := by
          have : cVal 4 * B * h ≤ cVal 4 * B := mul_le_of_le_one_right (by positivity) hh1
          unfold cRec; nlinarith [mul_nonneg hd hB, mul_nonneg hl hB]
  · rw [fderiv_recon hh]
    have e1 := norm_reconD_samp_sub_le hh hB hf hg.lip y
    calc ‖reconD h (samp h g) y‖ ≤ ‖fderiv ℝ g y‖ + ‖reconD h (samp h g) y - fderiv ℝ g y‖ := by
          have := norm_add_le (fderiv ℝ g y) (reconD h (samp h g) y - fderiv ℝ g y)
          rwa [add_sub_cancel] at this
      _ ≤ B + cDer 4 * B * h := add_le_add (hg.norm_fderiv_le y) e1
      _ ≤ cRec * B := by
          have : cDer 4 * B * h ≤ cDer 4 * B := mul_le_of_le_one_right (by positivity) hh1
          unfold cRec; nlinarith [mul_nonneg hv hB, mul_nonneg hl hB]
  · rw [fderiv_recon hh, fderiv_recon hh]
    refine (norm_reconD_samp_sub_reconD_le hh hB hf hg.lip y z).trans ?_
    have : cLip 4 ≤ cRec := by unfold cRec; linarith
    gcongr

theorem norm_recon_samp_sub_le' {g : E4 → W} {B : ℝ} (hg : IsC11 g B) {h : ℝ} (hh : 0 < h)
    (y : E4) : ‖recon h (samp h g) y - g y‖ ≤ cVal 4 * B * h :=
  norm_recon_samp_sub_le hh hg.hasFDerivAt hg.norm_fderiv_le y

theorem norm_fderiv_recon_samp_sub_le {g : E4 → W} {B : ℝ} (hg : IsC11 g B) {h : ℝ}
    (hh : 0 < h) (y : E4) :
    ‖fderiv ℝ (recon h (samp h g)) y - fderiv ℝ g y‖ ≤ cDer 4 * B * h := by
  rw [fderiv_recon hh]
  exact norm_reconD_samp_sub_le hh hg.nonneg hg.hasFDerivAt hg.lip y

end Recon

/-! ### Tests are `C^{1,1}` -/

section Tests

variable {T : ℝ} {K : CylRegion T} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem norm_fderiv_fderiv_le_crNorm {f : E4 → F} (hf : IsCylTest K f) {r : ℕ} (hr : 2 ≤ r)
    (x : E4) : ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ crNorm r f := by
  refine le_trans ?_ (iSup_le_crNorm hf hr)
  have e : ‖fderiv ℝ (fderiv ℝ f) x‖ = ‖iteratedFDeriv ℝ 2 f x‖ := by
    rw [← norm_iteratedFDeriv_one (𝕜 := ℝ) (f := fderiv ℝ f), norm_iteratedFDeriv_fderiv]
  rw [e]
  exact le_ciSup (hf.bddAbove_norm_iteratedFDeriv 2) x

/-- **A test section is `C^{1,1}` with constant `‖f‖_{C^r}`** (`r ≥ 2`). -/
theorem isC11_of_isCylTest {f : E4 → F} (hf : IsCylTest K f) {r : ℕ} (hr : 2 ≤ r) :
    IsC11 f (crNorm r f) := by
  have hd : Differentiable ℝ f := hf.smooth.differentiable (by simp)
  have hd2 : Differentiable ℝ (fderiv ℝ f) :=
    (hf.smooth.fderiv_right (m := ∞) le_rfl).differentiable (by simp)
  refine ⟨fun y => (hd y).hasFDerivAt, fun y => norm_le_crNorm hf r y,
    fun y => norm_fderiv_le_crNorm hf (by omega) y, fun y z => ?_⟩
  exact convex_univ.norm_image_sub_le_of_norm_fderiv_le (fun w _ => (hd2 w))
    (fun w _ => norm_fderiv_fderiv_le_crNorm hf hr w) (mem_univ z) (mem_univ y)

end Tests

/-! ### Time periodization -/

section Periodization

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The time unit vector `e₀`. -/
def e0 : E4 := Pi.single 0 1

/-- **Time periodization** `(tper P g)(y) = g(y - P⌊y⁰/P⌋ e₀)`. -/
def tper (P : ℕ) (g : E4 → W) (y : E4) : W := g (y - ((P : ℝ) * ⌊y 0 / P⌋) • e0)

@[simp] theorem e0_zero : e0 0 = 1 := by simp [e0]

theorem e0_succ (i : Fin 3) : e0 i.succ = 0 := by simp [e0]

theorem sub_smul_e0_zero (y : E4) (c : ℝ) : (y - c • e0) 0 = y 0 - c := by simp [e0]

/-- On the open strip `(kP + b - P, (k+1)P + a)` the periodization is the translate by `kP`. -/
theorem tper_eq_translate {P : ℕ} (hP : 0 < P) {g : E4 → W} {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hb : b < P) (hg : ∀ y, y 0 ∉ Icc a b → g y = 0) (k : ℤ) {y : E4}
    (hy1 : (k : ℝ) * P + b - P < y 0) (hy2 : y 0 < ((k : ℝ) + 1) * P + a) :
    tper P g y = g (y - ((P : ℝ) * k) • e0) := by
  have hP' : (0 : ℝ) < P := by exact_mod_cast hP
  unfold tper
  set n := ⌊y 0 / P⌋ with hn
  have hn1 : (n : ℝ) ≤ y 0 / P := Int.floor_le _
  have hn2 : y 0 / P < n + 1 := Int.lt_floor_add_one _
  have hn1' : (n : ℝ) * P ≤ y 0 := by rwa [le_div_iff₀ hP'] at hn1
  have hn2' : y 0 < ((n : ℝ) + 1) * P := by rwa [div_lt_iff₀ hP'] at hn2
  -- `n ∈ {k-1, k, k+1}`
  have hlo : k - 1 ≤ n := by
    have : ((k : ℝ) - 1) * P < ((n : ℝ) + 1) * P := by nlinarith
    have : (k : ℝ) - 1 < n + 1 := lt_of_mul_lt_mul_right this hP'.le
    have : k - 1 < n + 1 := by exact_mod_cast this
    omega
  have hhi : n ≤ k + 1 := by
    have : (n : ℝ) * P < ((k : ℝ) + 2) * P := by nlinarith
    have : (n : ℝ) < k + 2 := lt_of_mul_lt_mul_right this hP'.le
    have : n < k + 2 := by exact_mod_cast this
    omega
  rcases (show n = k - 1 ∨ n = k ∨ n = k + 1 by omega) with h | h | h
  · have hnP : (n : ℝ) * P = (k : ℝ) * P - P := by rw [h]; push_cast; ring
    rw [hg, hg]
    · rw [sub_smul_e0_zero]; intro hm
      have := hm.1
      nlinarith [hn2']
    · rw [sub_smul_e0_zero]; intro hm
      have := hm.2
      push_cast [h] at this
      nlinarith [hy1]
  · rw [h]
  · have hnP : (n : ℝ) * P = (k : ℝ) * P + P := by rw [h]; push_cast; ring
    rw [hg, hg]
    · rw [sub_smul_e0_zero]; intro hm
      have := hm.2
      nlinarith [hn1', hb]
    · rw [sub_smul_e0_zero]; intro hm
      have := hm.1
      push_cast [h] at this
      nlinarith [hy2]

theorem tper_eventuallyEq {P : ℕ} (hP : 0 < P) {g : E4 → W} {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) (hb : b < P) (hg : ∀ y, y 0 ∉ Icc a b → g y = 0) (k : ℤ) {y : E4}
    (hy1 : (k : ℝ) * P + b - P < y 0) (hy2 : y 0 < ((k : ℝ) + 1) * P + a) :
    tper P g =ᶠ[𝓝 y] fun x => g (x - ((P : ℝ) * k) • e0) := by
  have hc : Continuous fun x : E4 => x 0 := continuous_apply 0
  have ho : IsOpen {x : E4 | (k : ℝ) * P + b - P < x 0 ∧ x 0 < ((k : ℝ) + 1) * P + a} :=
    (isOpen_lt continuous_const hc).inter (isOpen_lt hc continuous_const)
  filter_upwards [ho.mem_nhds ⟨hy1, hy2⟩] with x hx
  exact tper_eq_translate hP ha hab hb hg k hx.1 hx.2

theorem mem_strip_floor {P : ℕ} (hP : 0 < P) {a b : ℝ} (ha : 0 < a) (hb : b < P) (y : E4) :
    ((⌊y 0 / P⌋ : ℤ) : ℝ) * P + b - P < y 0 ∧ y 0 < (((⌊y 0 / P⌋ : ℤ) : ℝ) + 1) * P + a := by
  have hP' : (0 : ℝ) < P := by exact_mod_cast hP
  have hn1 : ((⌊y 0 / P⌋ : ℤ) : ℝ) ≤ y 0 / P := Int.floor_le _
  have hn2 : y 0 / P < ⌊y 0 / P⌋ + 1 := Int.lt_floor_add_one _
  rw [le_div_iff₀ hP'] at hn1
  rw [div_lt_iff₀ hP'] at hn2
  constructor <;> nlinarith

/-- **The periodization of a time-windowed `C^{1,1}` section is `C^{1,1}`.** -/
theorem isC11_tper {P : ℕ} (hP : 0 < P) {g : E4 → W} {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hb : b < P) (hg : ∀ y, y 0 ∉ Icc a b → g y = 0) {B : ℝ} (hgB : IsC11 g B) :
    IsC11 (tper P g) (max B (2 * B / (P + a - b))) := by
  have hB := hgB.nonneg
  have hP' : (0 : ℝ) < P := by exact_mod_cast hP
  have hδ : 0 < (P : ℝ) + a - b := by linarith
  -- local derivative
  have hloc : ∀ (k : ℤ) (y : E4), (k : ℝ) * P + b - P < y 0 → y 0 < ((k : ℝ) + 1) * P + a →
      HasFDerivAt (tper P g) (fderiv ℝ g (y - ((P : ℝ) * k) • e0)) y := by
    intro k y h1 h2
    have := (hgB.hasFDerivAt (y - ((P : ℝ) * k) • e0)).comp y
      ((hasFDerivAt_id y).sub_const (((P : ℝ) * k) • e0))
    simp only [ContinuousLinearMap.comp_id] at this
    exact this.congr_of_eventuallyEq (tper_eventuallyEq hP ha hab hb hg k h1 h2)
  have hfd : ∀ y, fderiv ℝ (tper P g) y =
      fderiv ℝ g (y - ((P : ℝ) * ⌊y 0 / P⌋) • e0) := fun y =>
    (hloc _ y (mem_strip_floor hP ha hb y).1 (mem_strip_floor hP ha hb y).2).fderiv
  refine ⟨fun y => (hloc _ y (mem_strip_floor hP ha hb y).1 (mem_strip_floor hP ha hb y).2).congr_fderiv
    (hfd y).symm, fun y => (hgB.norm_le _).trans (le_max_left _ _),
    fun y => by rw [hfd]; exact (hgB.norm_fderiv_le _).trans (le_max_left _ _), fun y z => ?_⟩
  -- the derivative is Lipschitz
  wlog hyz : y 0 ≤ z 0 generalizing y z
  · rw [norm_sub_rev, norm_sub_rev y z]; exact this z y (by linarith)
  by_cases hclose : z 0 - y 0 < (P : ℝ) + a - b
  · -- both points lie in one strip
    set n := ⌊y 0 / P⌋
    obtain ⟨hy1, hy2⟩ := mem_strip_floor hP ha hb y
    have hn1 : (n : ℝ) * P ≤ y 0 := by
      have := Int.floor_le (y 0 / P); rwa [le_div_iff₀ hP'] at this
    have hn2 : y 0 < ((n : ℝ) + 1) * P := by
      have := Int.lt_floor_add_one (y 0 / P); rwa [div_lt_iff₀ hP'] at this
    obtain ⟨k, hk1, hk2, hk3, hk4⟩ : ∃ k : ℤ, (k : ℝ) * P + b - P < y 0 ∧
        y 0 < ((k : ℝ) + 1) * P + a ∧ (k : ℝ) * P + b - P < z 0 ∧ z 0 < ((k : ℝ) + 1) * P + a := by
      by_cases hyb : y 0 ≤ n * P + b
      · exact ⟨n, hy1, hy2, by linarith, by linarith⟩
      · refine ⟨n + 1, ?_, ?_, ?_, ?_⟩ <;> push_cast <;> nlinarith
    rw [(hloc k y hk1 hk2).fderiv, (hloc k z hk3 hk4).fderiv]
    refine (hgB.lip _ _).trans ?_
    rw [sub_sub_sub_cancel_right]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  · push_neg at hclose
    have hyz' : (P : ℝ) + a - b ≤ ‖y - z‖ := by
      have := norm_le_pi_norm (y - z) 0
      rw [Pi.sub_apply, Real.norm_eq_abs, abs_sub_comm, abs_of_nonneg (by linarith)] at this
      linarith
    calc ‖fderiv ℝ (tper P g) y - fderiv ℝ (tper P g) z‖
        ≤ ‖fderiv ℝ (tper P g) y‖ + ‖fderiv ℝ (tper P g) z‖ := norm_sub_le _ _
      _ ≤ B + B := by
          rw [hfd, hfd]; exact add_le_add (hgB.norm_fderiv_le _) (hgB.norm_fderiv_le _)
      _ = (2 * B / (P + a - b)) * (P + a - b) := by field_simp; ring
      _ ≤ max B (2 * B / (P + a - b)) * ‖y - z‖ := by
          gcongr
          · exact le_max_right _ _

theorem tper_eq {P : ℕ} (hP : 0 < P) {g : E4 → W} {y : E4} (h0 : 0 ≤ y 0) (h1 : y 0 < P) :
    tper P g y = g y := by
  have hP' : (0 : ℝ) < P := by exact_mod_cast hP
  have : ⌊y 0 / P⌋ = 0 := by
    rw [Int.floor_eq_zero_iff]; constructor
    · positivity
    · rw [div_lt_one hP']; exact h1
  simp [tper, this]

/-- Periodization commutes with pointwise maps. -/
theorem tper_comp {W' : Type*} (P : ℕ) (Λ : W → W') (g : E4 → W) (y : E4) :
    Λ (tper P g y) = tper P (fun x => Λ (g x)) y := rfl

end Periodization

/-! ### The test lift is the sampling of the periodized variation -/

section Lift

variable {Ysec : Type} [Fintype Ysec] (FC : FermionCarrier Ysec)

/-- The time periodization of a field tuple. -/
def tperTuple (P : ℕ) (w : FieldTuple FC.C) : FieldTuple FC.C :=
  FieldTuple.mk (tper P w.e) (tper P w.A) (tper P w.H) (tper P w.Ψ) (tper P w.Ψb)

theorem smul_jc_reduceIdx {P N : ℕ} (hP : 0 < P) (hN : 0 < N) (j : Fin 4 → ℤ) :
    ((1 : ℝ) / N) • jc (reduceIdx P N j) =
      ((1 : ℝ) / N) • jc j - ((P : ℝ) * ⌊(((1 : ℝ) / N) • jc j) 0 / P⌋) • e0 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hP' : (0 : ℝ) < P := by exact_mod_cast hP
  have hfl : ⌊1 / (N : ℝ) * (j 0 : ℝ) / P⌋ = j 0 / ((P * N : ℕ) : ℤ) := by
    have e : 1 / (N : ℝ) * (j 0 : ℝ) / P = ((j 0 : ℤ) : ℝ) / ((P * N : ℕ) : ℝ) := by
      push_cast; field_simp
    rw [e, Int.floor_div_natCast, Int.floor_intCast]
  have hm : ((j 0 % ((P * N : ℕ) : ℤ) : ℤ) : ℝ) =
      (j 0 : ℝ) - ((P * N : ℕ) : ℝ) * ((j 0 / ((P * N : ℕ) : ℤ) : ℤ) : ℝ) := by
    rw [Int.emod_def]; push_cast; ring
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp only [Pi.smul_apply, Pi.sub_apply, jc, reduceIdx, smul_eq_mul, e0_zero,
      mul_one, if_true]
    rw [hfl, hm]
    push_cast
    field_simp
  · simp [jc, reduceIdx, e0_succ, Fin.succ_ne_zero]

/-- **The test lift is the nodal sampling of the time-periodized complete variation.** -/
theorem liftRec_eq_sampleRec_tper {P N : ℕ} (hP : 0 < P) (hN : 0 < N) (z v : FieldTuple FC.C) :
    liftRec FC P N (1 / N) z v = sampleRec FC (1 / N) (tperTuple FC P (variationDirection z v)) := by
  funext j
  simp only [liftRec, sampleRec, tperTuple, FieldTuple.mk, FieldTuple.e, FieldTuple.A, FieldTuple.H,
    FieldTuple.Ψ, FieldTuple.Ψb, tper]
  rw [smul_jc_reduceIdx hP hN j]

end Lift

end Comparison
end EinsteinSM
end RenewalGeometry
