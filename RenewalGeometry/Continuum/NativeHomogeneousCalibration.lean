/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.NativeHomogeneousLapse
import RenewalGeometry.Continuum.NativeCalibrationWitness
import RenewalGeometry.Continuum.NativeLocalCalibrationBackreacting
import RenewalGeometry.Gravity.HomogeneousEinsteinHiggsExact

/-!
# The backreacting homogeneous Einstein–Higgs example in the native slab gauges

Einstein–Standard-Model action-closure manuscript, `cor:local-calibration-nonempty`, last
sentence: "A backreacting Einstein–Higgs example is supplied by `prop:homogeneous`, after a regular
gauge change on a smaller slab."

Corrected encoding (gauge rows in the gauge Lie algebra, g11).  For every solution
`(a, φ, π, ℋ)` of `eq:homogeneous-ODE` (cosmic time, `prop:homogeneous`) satisfying the Friedmann
constraint, the **regular gauge change** is:

* harmonic time `τ` with cosmic time `S(τ)`, `dS/dτ = a(S)³`, `S(π) = 0` (Picard–Lindelöf,
  `exists_harmonic_time`); in harmonic time the FLRW metric is `-a⁶dτ² + a²dx²` and the
  coordinates are harmonic (`C^l = 0`);
* adapted coframe `diag(a³, a, a, a)`, `A = 0`, Higgs field `H = φ(S(τ))/√2` (real Higgs line,
  `h₀ = 1`), `Ψ = Ψ̄ = 0`;
* restriction to a smaller slab around `τ = π`, smooth cut-off to constant values outside it and
  `2π`-periodic extension in time (`exists_periodic_ext`).

The resulting native field of the Einstein–Higgs slab model `ehSlab` (trivial gauge algebra
`gl(1)` with `𝔤 = 0`, Higgs line, Dirac spinors, couplings `κ, Λ, λ_H, v_H`) satisfies every
hypothesis of `LocalCalibrationClosed.local_calibration_nonempty`
(`homogeneous_calibration_hyps`): smooth, `2π`-periodic, fixed gauges, compact coframe chart,
Lorentzian chart, the **physical** native Euler equations on the buffered slab (all coframe rows
including the local Lorentz ones, Higgs, spinor and co-spinor rows; `native_euler_profile` with the
Friedmann, Raychaudhuri and Klein–Gordon equations in harmonic time) and the harmonic gauge of the
dilated metric.  Hence `cor:local-calibration-nonempty` holds for it
(`local_calibration_nonempty_homogeneous`).  The example is backreacting whenever `π(0) ≠ 0`, and
then it **violates the complete (all-`𝔄`) system** (`homogeneous_violates_complete`, via
`CalibrationBackreacting.no_backreacting_homogeneous`): exactly the unphysical unit row that the
corrected encoding removed.  A concrete backreacting instance: `homogeneous_backreacting_instance`.
-/

open Set Filter Topology Finset
open scoped ContDiff Real

noncomputable section

namespace RenewalGeometry.HomogeneousCalibration

open NativeDensity NativeModel NativeModelExample SlabData

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 400000

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-! ### The Einstein–Higgs slab model -/

/-- **The Einstein–Higgs native model**: the concrete model `diracModel` (trivial gauge algebra
`ℝ`, real Higgs line with `⟨x, y⟩ = xy`, Dirac spinors `ℂ⁴`) with couplings `κ, Λ, λ_H, v_H`. -/
def ehModel (κ Λ lamH vH : ℝ) : Model ℝ ℝ Sp :=
  { diracModel with κ := κ, Λ := Λ, lamH := lamH, vH := vH }

/-- **The Einstein–Higgs slab model** (`gl(1)`, gauge Lie algebra `𝔤 = 0`, `κ ≠ 0`). -/
def ehSlab (κ Λ lamH vH : ℝ) (hκ : κ ≠ 0) : SlabModel ℝ ℝ Sp 1 where
  toModel := ehModel κ Λ lamH vH
  φ := phi1
  yukawa_cl H a b := by simp [ehModel, diracModel]
  yukawa_eq A H := by simp [ehModel, diracModel]
  gSub := ⊥
  gLie_eq := by simp [ehModel, diracModel]
  gSub_lie a ha b hb := by
    rw [Submodule.mem_bot] at ha hb ⊢
    simp [ha, hb]
  ipA_nondeg_g x hx _ := (Submodule.mem_bot ℝ).1 hx
  κ_ne := hκ

theorem ehSlab_πg (κ Λ lamH vH : ℝ) (hκ : κ ≠ 0) (x : ℝ) : (ehSlab κ Λ lamH vH hκ).πg x = 0 :=
  (Submodule.mem_bot ℝ).1 ((ehSlab κ Λ lamH vH hκ).πg_mem x)

/-! ### Smooth periodic extensions of functions given near `π` -/

section Periodic

/-- The periodization `t ↦ Σ_k g(t - 2πk)`. -/
def perSum (g : ℝ → ℝ) (t : ℝ) : ℝ := ∑ᶠ k : ℤ, g (t - k * (2 * π))

theorem perSum_periodic (g : ℝ → ℝ) : Function.Periodic (perSum g) (2 * π) := by
  intro t
  unfold perSum
  have e : (fun k : ℤ => g (t + 2 * π - k * (2 * π))) =
      (fun k : ℤ => g (t - k * (2 * π))) ∘ (Equiv.subRight (1 : ℤ)) := by
    funext k
    simp only [Function.comp_apply, Equiv.subRight_apply]
    congr 1
    push_cast
    ring
  rw [e]
  exact finsum_comp_equiv (f := fun k : ℤ => g (t - k * (2 * π))) (Equiv.subRight (1 : ℤ))

/-- Support condition: `g` vanishes outside `[α, β] ⊂ (0, 2π)`. -/
def SuppIn (g : ℝ → ℝ) (α β : ℝ) : Prop := ∀ s, g s ≠ 0 → s ∈ Icc α β

theorem perSum_support_unique {g : ℝ → ℝ} {α β : ℝ} (hα : 0 < α) (hβ : β < 2 * π)
    (hg : SuppIn g α β) {t : ℝ} {k k' : ℤ} (hk : g (t - k * (2 * π)) ≠ 0)
    (hk' : g (t - k' * (2 * π)) ≠ 0) : k = k' := by
  have h1 := hg _ hk
  have h2 := hg _ hk'
  have hpi := Real.pi_pos
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have : (k : ℝ) + 1 ≤ k' := by exact_mod_cast hlt
    nlinarith [h1.1, h1.2, h2.1, h2.2]
  · have : (k' : ℝ) + 1 ≤ k := by exact_mod_cast hlt
    nlinarith [h1.1, h1.2, h2.1, h2.2]

theorem perSum_eq_of {g : ℝ → ℝ} {α β : ℝ} (hα : 0 < α) (hβ : β < 2 * π) (hg : SuppIn g α β)
    (t : ℝ) (k : ℤ) (hk : ∀ k' : ℤ, k' ≠ k → g (t - k' * (2 * π)) = 0) :
    perSum g t = g (t - k * (2 * π)) := by
  unfold perSum
  exact finsum_eq_single _ k hk

/-- The periodization is one of the translates or zero. -/
theorem perSum_cases {g : ℝ → ℝ} {α β : ℝ} (hα : 0 < α) (hβ : β < 2 * π) (hg : SuppIn g α β)
    (t : ℝ) : perSum g t = 0 ∨ ∃ k : ℤ, perSum g t = g (t - k * (2 * π)) := by
  by_cases h : ∃ k : ℤ, g (t - k * (2 * π)) ≠ 0
  · obtain ⟨k, hk⟩ := h
    refine Or.inr ⟨k, perSum_eq_of hα hβ hg t k fun k' hk' => ?_⟩
    by_contra hne
    exact hk' (perSum_support_unique hα hβ hg hne hk)
  · push Not at h
    left
    unfold perSum
    exact finsum_eq_zero_of_forall_eq_zero h

theorem perSum_eq_self {g : ℝ → ℝ} {α β : ℝ} (hα : 0 < α) (hβ : β < 2 * π) (hg : SuppIn g α β)
    {t : ℝ} (ht : t ∈ Ioo 0 (2 * π)) : perSum g t = g t := by
  have h := perSum_eq_of hα hβ hg t 0 fun k' hk' => by
    by_contra hne
    have h1 := hg _ hne
    have hpi := Real.pi_pos
    rcases lt_or_gt_of_ne hk' with hlt | hlt
    · have : (k' : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hlt
      nlinarith [ht.1, ht.2, h1.1, h1.2]
    · have : (1 : ℝ) ≤ k' := by exact_mod_cast hlt
      nlinarith [ht.1, ht.2, h1.1, h1.2]
  simpa using h

theorem contDiff_perSum {g : ℝ → ℝ} {α β : ℝ} (hα : 0 < α) (hβ : β < 2 * π) (hg : SuppIn g α β)
    (hgs : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (perSum g) := by
  refine contDiff_iff_contDiffAt.mpr fun t₀ => ?_
  set k₀ : ℤ := ⌊t₀ / (2 * π)⌋ with hk₀
  set F : Finset ℤ := Finset.Icc (k₀ - 2) (k₀ + 2)
  have hpi := Real.pi_pos
  have hev : perSum g =ᶠ[𝓝 t₀] fun t => ∑ k ∈ F, g (t - k * (2 * π)) := by
    filter_upwards [Ioo_mem_nhds (show t₀ - π < t₀ by linarith) (show t₀ < t₀ + π by linarith)]
      with t ht
    unfold perSum
    refine finsum_eq_sum_of_support_subset _ fun k hk => ?_
    have h1 := hg _ hk
    show k ∈ ((Finset.Icc (k₀ - 2) (k₀ + 2) : Finset ℤ) : Set ℤ)
    rw [Finset.mem_coe, Finset.mem_Icc]
    have hfl := Int.floor_le (t₀ / (2 * π))
    have hfl2 := Int.lt_floor_add_one (t₀ / (2 * π))
    rw [← hk₀] at hfl hfl2
    have e1 : (k₀ : ℝ) * (2 * π) ≤ t₀ := by
      have := mul_le_mul_of_nonneg_right hfl (by positivity : (0 : ℝ) ≤ 2 * π)
      rwa [div_mul_cancel₀ _ (by positivity)] at this
    have e2 : t₀ < ((k₀ : ℝ) + 1) * (2 * π) := by
      have := mul_lt_mul_of_pos_right hfl2 (by positivity : (0 : ℝ) < 2 * π)
      rwa [div_mul_cancel₀ _ (by positivity)] at this
    constructor
    · by_contra hlt
      push Not at hlt
      have : (k : ℝ) ≤ k₀ - 3 := by exact_mod_cast Int.le_sub_one_of_lt hlt |>.trans (by omega)
      nlinarith [ht.1, ht.2, h1.1, h1.2]
    · by_contra hlt
      push Not at hlt
      have : (k₀ : ℝ) + 3 ≤ k := by exact_mod_cast (show k₀ + 3 ≤ k by omega)
      nlinarith [ht.1, ht.2, h1.1, h1.2]
  refine ContDiffAt.congr_of_eventuallyEq ?_ hev
  exact (ContDiff.sum fun k _ => hgs.comp (contDiff_id.sub contDiff_const)).contDiffAt

/-- **Smooth periodic extension**: a smooth function `f` on `(π - r, π + r)` (`0 < r ≤ π`) agrees on
`(π - r/2, π + r/2)` with a smooth `2π`-periodic function, equal to the constant `c` far from
`π + 2πℤ`, and positive if `f` and `c` are. -/
theorem exists_periodic_ext {f : ℝ → ℝ} {r : ℝ} (hr : 0 < r) (hrπ : r ≤ π)
    (hf : ContDiffOn ℝ ∞ f (Ioo (π - r) (π + r))) (c : ℝ) :
    ∃ F : ℝ → ℝ, ContDiff ℝ ∞ F ∧ Function.Periodic F (2 * π) ∧
      (∀ t ∈ Ioo (π - r / 2) (π + r / 2), F t = f t) ∧
      ((0 < c ∧ ∀ t ∈ Ioo (π - r) (π + r), 0 < f t) → ∀ t, 0 < F t) := by
  set χ : ContDiffBump (π : ℝ) := ⟨r / 2, 3 * r / 4, by positivity, by linarith⟩ with hχ
  set g : ℝ → ℝ := fun t => χ t * (f t - c) with hg
  have hpi := Real.pi_pos
  -- `χ` is supported in the closed ball of radius `3r/4`
  have hχ0 : ∀ t, 3 * r / 4 ≤ |t - π| → χ t = 0 := fun t ht =>
    χ.zero_of_le_dist (by rw [Real.dist_eq]; exact ht)
  have hχ1 : ∀ t, |t - π| ≤ r / 2 → χ t = 1 := fun t ht =>
    χ.one_of_mem_closedBall (by rw [Metric.mem_closedBall, Real.dist_eq]; exact ht)
  have hsupp : SuppIn g (π - 3 * r / 4) (π + 3 * r / 4) := by
    intro s hs
    by_contra hn
    apply hs
    have : 3 * r / 4 ≤ |s - π| := by
      rw [Set.mem_Icc, not_and_or] at hn
      rcases hn with hn | hn
      · push Not at hn; rw [abs_of_neg (by linarith)]; linarith
      · push Not at hn; rw [abs_of_pos (by linarith)]; linarith
    simp [hg, hχ0 s this]
  have hα : 0 < π - 3 * r / 4 := by linarith
  have hβ : π + 3 * r / 4 < 2 * π := by linarith
  have hgs : ContDiff ℝ ∞ g := by
    refine contDiff_iff_contDiffAt.mpr fun t => ?_
    by_cases ht : |t - π| < r
    · have hmem : t ∈ Ioo (π - r) (π + r) := by
        rw [abs_lt] at ht; exact ⟨by linarith, by linarith⟩
      have hfa : ContDiffAt ℝ ∞ f t := hf.contDiffAt (Ioo_mem_nhds hmem.1 hmem.2)
      exact χ.contDiff.contDiffAt.mul (hfa.sub contDiffAt_const)
    · push Not at ht
      have ho : IsOpen {s : ℝ | 3 * r / 4 < |s - π|} :=
        isOpen_lt continuous_const ((continuous_id.sub continuous_const).abs)
      have hev : g =ᶠ[𝓝 t] fun _ => 0 :=
        Filter.eventually_of_mem (ho.mem_nhds (show 3 * r / 4 < |t - π| by linarith))
          fun s hs => by simp [hg, hχ0 s (le_of_lt hs)]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  refine ⟨fun t => c + perSum g t, contDiff_const.add (contDiff_perSum hα hβ hsupp hgs),
    fun t => by simp only [perSum_periodic g t], fun t ht => ?_, fun ⟨hc, hfp⟩ t => ?_⟩
  · have ht' : t ∈ Ioo 0 (2 * π) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    show c + perSum g t = f t
    rw [perSum_eq_self hα hβ hsupp ht']
    have : |t - π| ≤ r / 2 := by
      rw [abs_le]; exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    simp [hg, hχ1 t this]
  · show 0 < c + perSum g t
    rcases perSum_cases hα hβ hsupp t with h0 | ⟨k, hk⟩
    · rw [h0, add_zero]; exact hc
    · rw [hk]
      set s := t - k * (2 * π)
      have hχnn : 0 ≤ χ s := χ.nonneg
      have hχle : χ s ≤ 1 := χ.le_one
      by_cases hs : |s - π| < r
      · have hmem : s ∈ Ioo (π - r) (π + r) := by
          rw [abs_lt] at hs; exact ⟨by linarith, by linarith⟩
        have hfs := hfp s hmem
        show 0 < c + χ s * (f s - c)
        have e : c + χ s * (f s - c) = (1 - χ s) * c + χ s * f s := by ring
        rw [e]
        rcases eq_or_lt_of_le hχle with h1 | h1
        · rw [h1]; simpa using hfs
        · have : 0 < (1 - χ s) * c := mul_pos (by linarith) hc
          have : 0 ≤ χ s * f s := mul_nonneg hχnn hfs.le
          linarith
      · push Not at hs
        simp [hg, hχ0 s (by linarith)]
        exact hc

end Periodic


/-! ### Harmonic time -/

section HarmonicTime

/-- **Harmonic time** (the regular gauge change): for a scale factor `a` smooth on `(-ε, ε)`, the
cosmic time `S(τ)` as a function of the harmonic time `τ` (`dS/dτ = a(S)³`, `S(π) = 0`) exists on
an interval around `π`, is smooth there and stays in `(-ε, ε)`. -/
theorem exists_harmonic_time {a : ℝ → ℝ} {ε : ℝ} (hε : 0 < ε)
    (ha : ContDiffOn ℝ ∞ a (Ioo (-ε) ε)) :
    ∃ r : ℝ, 0 < r ∧ r ≤ π ∧ ∃ S : ℝ → ℝ, S π = 0 ∧
      (∀ τ ∈ Ioo (π - r) (π + r), S τ ∈ Ioo (-ε) ε ∧ HasDerivAt S (a (S τ) ^ 3) τ) ∧
      ContDiffOn ℝ ∞ S (Ioo (π - r) (π + r)) := by
  have h0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
  have hf : ContDiffAt ℝ 1 (fun x => a x ^ 3) 0 :=
    ((ha.contDiffAt (Ioo_mem_nhds h0.1 h0.2)).pow 3).of_le (by exact_mod_cast le_top)
  obtain ⟨S, hS0, ε₁, hε₁, hS⟩ :=
    hf.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ π
  have hπ1 : π ∈ Ioo (π - ε₁) (π + ε₁) := ⟨by linarith, by linarith⟩
  have hcont : ContinuousAt S π := (hS π hπ1).continuousAt
  have hev : ∀ᶠ τ in 𝓝 π, S τ ∈ Ioo (-ε) ε := by
    have := hcont.eventually (Ioo_mem_nhds (show -ε < S π by rw [hS0]; linarith)
      (show S π < ε by rw [hS0]; exact hε))
    exact this
  obtain ⟨δ, hδ, hδS⟩ := Metric.eventually_nhds_iff.1 hev
  have hpi := Real.pi_pos
  set r : ℝ := min (min ε₁ δ) π / 2 with hr
  have hr0 : 0 < r := by positivity
  have hrε : r < ε₁ := by
    have : min (min ε₁ δ) π ≤ ε₁ := (min_le_left _ _).trans (min_le_left _ _)
    linarith
  have hrδ : r < δ := by
    have : min (min ε₁ δ) π ≤ δ := (min_le_left _ _).trans (min_le_right _ _)
    linarith
  have hrπ : r ≤ π := by
    have : min (min ε₁ δ) π ≤ π := min_le_right _ _
    linarith
  have hIcc : ∀ τ ∈ Icc (π - r) (π + r), τ ∈ Ioo (π - ε₁) (π + ε₁) ∧ S τ ∈ Ioo (-ε) ε := by
    intro τ hτ
    refine ⟨⟨by linarith [hτ.1], by linarith [hτ.2]⟩, hδS ?_⟩
    rw [Real.dist_eq, abs_lt]
    exact ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
  have hsmooth : ContDiffOn ℝ ∞ S (Icc (π - r) (π + r)) := by
    refine ODE.contDiffOn_enat_Icc_of_hasDerivWithinAt
      (f := fun _ x => a x ^ 3) (u := Ioo (-ε) ε) ?_ ?_ ?_
    · have : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => a p.2) (Icc (π - r) (π + r) ×ˢ Ioo (-ε) ε) :=
        ha.comp contDiff_snd.contDiffOn fun p hp => hp.2
      exact this.pow 3
    · intro τ hτ
      exact (hS τ (hIcc τ hτ).1).hasDerivWithinAt
    · intro τ hτ
      exact (hIcc τ hτ).2
  refine ⟨r, hr0, hrπ, S, hS0, fun τ hτ => ?_, hsmooth.mono Ioo_subset_Icc_self⟩
  have hτ' : τ ∈ Icc (π - r) (π + r) := Ioo_subset_Icc_self hτ
  exact ⟨(hIcc τ hτ').2, hS τ (hIcc τ hτ').1⟩

end HarmonicTime

/-! ### The homogeneous family in harmonic time -/

section HarmonicProfiles

open HomogeneousEinsteinHiggs

/-- Equality of functions on an open set transfers derivatives. -/
theorem deriv_eq_of_eqOn_open {f g : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) (hfg : EqOn f g U)
    {τ : ℝ} (hτ : τ ∈ U) : deriv f τ = deriv g τ :=
  Filter.EventuallyEq.deriv_eq (Filter.eventually_of_mem (hU.mem_nhds hτ) hfg)

/-- **The homogeneous Einstein–Higgs family in harmonic time, cut off and periodically extended**.
For a solution `(a, φ, π, ℋ)` of `eq:homogeneous-ODE` on `(-ε, ε)` with `a > 0`, smooth `a, φ`,
there are `0 < r ≤ π`, the cosmic time `S` of harmonic time (`S(π) = 0`, `S' = a(S)³`) and smooth
`2π`-periodic profiles `N, A > 0`, `h` that agree on `(π - r/2, π + r/2)` with the harmonic-time
fields `N = a(S)³`, `A = a(S)`, `h = φ(S)/√2`, with the derivatives given by the chain rule. -/
theorem exists_harmonic_profiles {κ lamH vH ε : ℝ} {a φ πh ℋ : ℝ → ℝ} (hε : 0 < ε)
    (sol : IsSolution κ lamH vH a φ πh ℋ (Ioo (-ε) ε)) (hapos : ∀ t ∈ Ioo (-ε) ε, 0 < a t)
    (has : ContDiffOn ℝ ∞ a (Ioo (-ε) ε)) (hφs : ContDiffOn ℝ ∞ φ (Ioo (-ε) ε)) :
    ∃ r : ℝ, 0 < r ∧ r ≤ π ∧ ∃ S FN FA Fh : ℝ → ℝ,
      S π = 0 ∧ HasDerivAt S (a 0 ^ 3) π ∧
      ContDiff ℝ ∞ FN ∧ ContDiff ℝ ∞ FA ∧ ContDiff ℝ ∞ Fh ∧
      Function.Periodic FN (2 * π) ∧ Function.Periodic FA (2 * π) ∧
      Function.Periodic Fh (2 * π) ∧ (∀ t, 0 < FN t) ∧ (∀ t, 0 < FA t) ∧
      (∀ τ ∈ Ioo (π - r / 2) (π + r / 2), S τ ∈ Ioo (-ε) ε ∧
        Fh τ = φ (S τ) / Real.sqrt 2 ∧ FA τ = a (S τ) ∧ FN τ = a (S τ) ^ 3 ∧
        deriv FA τ = a (S τ) ^ 4 * ℋ (S τ) ∧
        deriv (deriv FA) τ = a (S τ) ^ 7 * (4 * ℋ (S τ) ^ 2 - κ / 2 * πh (S τ) ^ 2) ∧
        deriv FN τ = 3 * a (S τ) ^ 6 * ℋ (S τ) ∧
        deriv Fh τ = πh (S τ) * a (S τ) ^ 3 / Real.sqrt 2 ∧
        deriv (deriv Fh) τ = -(a (S τ) ^ 6 * higgsPotentialDeriv lamH vH (φ (S τ))) /
          Real.sqrt 2) := by
  obtain ⟨r, hr, hrπ, S, hS0, hS, hSs⟩ := exists_harmonic_time hε has
  set I := Ioo (π - r) (π + r) with hI
  have hmaps : MapsTo S I (Ioo (-ε) ε) := fun τ hτ => (hS τ hτ).1
  -- local fields
  have hAloc : ContDiffOn ℝ ∞ (fun τ => a (S τ)) I := has.comp hSs hmaps
  have hNloc : ContDiffOn ℝ ∞ (fun τ => a (S τ) ^ 3) I := hAloc.pow 3
  have hhloc : ContDiffOn ℝ ∞ (fun τ => φ (S τ) / Real.sqrt 2) I :=
    (hφs.comp hSs hmaps).div_const _
  obtain ⟨FA, hFAs, hFAp, hFAeq, hFApos⟩ := exists_periodic_ext hr hrπ hAloc 1
  obtain ⟨FN, hFNs, hFNp, hFNeq, hFNpos⟩ := exists_periodic_ext hr hrπ hNloc 1
  obtain ⟨Fh, hFhs, hFhp, hFheq, -⟩ := exists_periodic_ext hr hrπ hhloc 0
  have hpI : ∀ τ ∈ I, 0 < a (S τ) := fun τ hτ => hapos _ (hS τ hτ).1
  have hFApos' : ∀ t, 0 < FA t := hFApos ⟨one_pos, hpI⟩
  have hFNpos' : ∀ t, 0 < FN t := hFNpos ⟨one_pos, fun τ hτ => pow_pos (hpI τ hτ) 3⟩
  -- chain rule along `S`
  have hd : ∀ τ ∈ I,
      HasDerivAt (fun τ => a (S τ)) (a (S τ) * ℋ (S τ) * a (S τ) ^ 3) τ ∧
      HasDerivAt (fun τ => ℋ (S τ)) (-(κ / 2) * πh (S τ) ^ 2 * a (S τ) ^ 3) τ ∧
      HasDerivAt (fun τ => φ (S τ)) (πh (S τ) * a (S τ) ^ 3) τ ∧
      HasDerivAt (fun τ => πh (S τ))
        ((-3 * ℋ (S τ) * πh (S τ) - higgsPotentialDeriv lamH vH (φ (S τ))) * a (S τ) ^ 3) τ := by
    intro τ hτ
    obtain ⟨hSτ, hSd⟩ := hS τ hτ
    exact ⟨(sol.a_deriv _ hSτ).comp τ hSd, (sol.ℋ_deriv _ hSτ).comp τ hSd,
      (sol.φ_deriv _ hSτ).comp τ hSd, (sol.π_deriv _ hSτ).comp τ hSd⟩
  set J := Ioo (π - r / 2) (π + r / 2) with hJ
  have hJI : J ⊆ I := fun τ hτ => ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
  have hJo : IsOpen J := isOpen_Ioo
  -- first derivatives on `J`
  have hdA : ∀ τ ∈ J, deriv FA τ = a (S τ) ^ 4 * ℋ (S τ) := by
    intro τ hτ
    rw [deriv_eq_of_eqOn_open hJo (fun t ht => hFAeq t ht) hτ, ((hd τ (hJI hτ)).1).deriv]
    ring
  have hdN : ∀ τ ∈ J, deriv FN τ = 3 * a (S τ) ^ 6 * ℋ (S τ) := by
    intro τ hτ
    rw [deriv_eq_of_eqOn_open hJo (fun t ht => hFNeq t ht) hτ, ((hd τ (hJI hτ)).1.fun_pow 3).deriv]
    ring
  have hdh : ∀ τ ∈ J, deriv Fh τ = πh (S τ) * a (S τ) ^ 3 / Real.sqrt 2 := by
    intro τ hτ
    rw [deriv_eq_of_eqOn_open hJo (fun t ht => hFheq t ht) hτ,
      ((hd τ (hJI hτ)).2.2.1.div_const (Real.sqrt 2)).deriv]
  refine ⟨r, hr, hrπ, S, FN, FA, Fh, hS0, ?_, hFNs, hFAs, hFhs, hFNp, hFAp, hFhp, hFNpos',
    hFApos', fun τ hτ => ⟨(hS τ (hJI hτ)).1, hFheq τ hτ, hFAeq τ hτ, hFNeq τ hτ, hdA τ hτ, ?_,
      hdN τ hτ, hdh τ hτ, ?_⟩⟩
  · have := (hS π ⟨by linarith, by linarith⟩).2
    rwa [hS0] at this
  · -- second derivative of `A`
    have hev : deriv FA =ᶠ[𝓝 τ] fun t => a (S t) ^ 4 * ℋ (S t) :=
      Filter.eventually_of_mem (hJo.mem_nhds hτ) hdA
    rw [hev.deriv_eq]
    obtain ⟨h1, h2, -, -⟩ := hd τ (hJI hτ)
    rw [((h1.fun_pow 4).fun_mul h2).deriv]
    ring
  · have hev : deriv Fh =ᶠ[𝓝 τ] fun t => πh (S t) * a (S t) ^ 3 / Real.sqrt 2 :=
      Filter.eventually_of_mem (hJo.mem_nhds hτ) hdh
    rw [hev.deriv_eq]
    obtain ⟨h1, -, -, h4⟩ := hd τ (hJI hτ)
    rw [((h4.fun_mul (h1.fun_pow 3)).div_const (Real.sqrt 2)).deriv]
    ring

end HarmonicProfiles

/-! ### The Einstein–Higgs equations in harmonic time -/

section Algebra

open HomogeneousEinsteinHiggs

/-- **The Friedmann, Raychaudhuri and Klein–Gordon equations in harmonic time**, from the
homogeneous ODE in cosmic time and the Friedmann constraint (pure algebra: `N = a³`, `A' = a⁴ℋ`,
`A'' = a⁷(4ℋ² - (κ/2)π²)`, `N' = 3a⁶ℋ`, `h = φ/√2`, `h' = πa³/√2`, `h'' = -a⁶U'(φ)/√2`). -/
theorem harmonic_equations {κ Λ lamH vH av ℋv πv φv : ℝ} (hav : 0 < av)
    (hcon : 3 * ℋv ^ 2 = Λ + κ * (πv ^ 2 / 2 + higgsPotential lamH vH φv)) :
    let A := av; let N := av ^ 3; let h := φv / Real.sqrt 2
    let A1 := av ^ 4 * ℋv; let A2 := av ^ 7 * (4 * ℋv ^ 2 - κ / 2 * πv ^ 2)
    let N1 := 3 * av ^ 6 * ℋv; let h1 := πv * av ^ 3 / Real.sqrt 2
    let h2 := -(av ^ 6 * higgsPotentialDeriv lamH vH φv) / Real.sqrt 2
    (3 * A1 ^ 2 / A ^ 2 - Λ * N ^ 2 - κ * (h1 * h1 + N ^ 2 * (lamH * (h * h - vH ^ 2) ^ 2)) = 0) ∧
    (-(2 * A * A2 / N ^ 2 - 2 * A * A1 * N1 / N ^ 3 + A1 ^ 2 / N ^ 2) + Λ * A ^ 2 -
      κ * (A ^ 2 * (h1 * h1 / N ^ 2 - lamH * (h * h - vH ^ 2) ^ 2)) = 0) ∧
    (∀ η : ℝ, 2 * (η * (-(N ^ 2)⁻¹ * (h2 - N1 / N * h1 + 3 * A1 / A * h1))) =
      lamH * (2 * (h * h - vH ^ 2) * (η * h + h * η))) := by
  intro A N h A1 A2 N1 h1 h2
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : Real.sqrt 2 ≠ 0 := by positivity
  have hav0 : av ≠ 0 := hav.ne'
  have hhh : h * h = φv ^ 2 / 2 := by
    simp only [h]; rw [div_mul_div_comm, ← pow_two, ← pow_two, hs]
  have hh1 : h1 * h1 = πv ^ 2 * av ^ 6 / 2 := by
    have hss : Real.sqrt 2 * Real.sqrt 2 = 2 := by rw [← pow_two, hs]
    simp only [h1]; rw [div_mul_div_comm, hss]
    ring
  unfold higgsPotential at hcon
  refine ⟨?_, ?_, fun η => ?_⟩
  · rw [hh1, hhh]
    simp only [A, N, A1]
    field_simp
    linear_combination (4 * av ^ 6) * hcon
  · rw [hh1, hhh]
    simp only [A, N, A1, A2, N1]
    field_simp
    linear_combination (-(4 * av ^ 2)) * hcon
  · rw [hhh]
    simp only [A, N, A1, N1, h1, h2, h]
    unfold higgsPotentialDeriv
    field_simp
    ring_nf
    try (rw [hs]; ring)

end Algebra

/-! ### The hypothesis packet of `local_calibration_nonempty` -/

section Packet

open HomogeneousNative CalibrationSampling RecordTuple NativeFrameBridge NativeStressEuler
  NativeBosonicEuler FieldScaling LocalCalibrationClosed PalatiniEuler ActualJetFrame
open DiscreteEulerConsistency (R4 evec jet1 contEuler limDensity IsPeriodic)
open NativeScaling (Mat eta metric)
open SobolevOpen (pd)
open ActualJetSystem (ginvOf)

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
variable [FiniteDimensional ℝ 𝔄] [FiniteDimensional ℝ 𝓗] [FiniteDimensional ℝ 𝓢]

/-- **The field hypotheses of `LocalCalibrationClosed.local_calibration_nonempty`** for a native
field `Y` of a slab model on the slab `[t₀, t₁]` buffered by `b` (the corollary's own parameters
`k`, `C_k`, the cutoffs and the coordinates are left free): smooth, `2π`-periodic, fixed gauges,
compact coframe chart, Lorentzian chart, the physical native Euler equations on the buffered slab
and the harmonic gauge of the dilated metric. -/
structure CalibHyps {m : ℕ} (M : SlabModel 𝔄 𝓗 𝓢 m) (Y : R4 → Field 𝔄 𝓗 𝓢) (t₀ t₁ b : ℝ) :
    Prop where
  smooth : ContDiff ℝ ∞ Y
  per : IsPeriodic (2 * π) Y
  gauge : FieldGauge M Y
  chart : ∃ Ke₀ : Set Mat, IsCompact Ke₀ ∧ (∀ e ∈ Ke₀, 0 < e.det) ∧ ∀ z, (Y z).1 ∈ Ke₀
  lor : ∀ z, IsLorChart (ginvS (Y z).1)
  hb : 0 < b
  h0 : b < t₀
  h1 : t₁ + b ≤ 2 * π
  h01 : t₀ < t₁
  sol : ∀ z ∈ NativeZeroSource.bufSlab (t₀ - b) (t₁ + b),
    (contEuler (limDensity (ι := Shift) (firstJetDensity M.toData)) Y z).comp
      (NativeTail.physF M.πg) = 0
  harm : ∀ x : R4, x 0 ∈ Icc 0 (slabT t₀ t₁) → ∀ l,
    ActualJetWriter.C (ginvOf (gF (eF (dilField t₀ Y)) x))
      (fun α => pd (gF (eF (dilField t₀ Y))) α x) l = 0

theorem smul_diagE (c n b : ℝ) : c • diagE n b = diagE (c * n) (c * b) := by
  ext i j
  simp only [Matrix.smul_apply, diagE_apply, smul_eq_mul]
  split_ifs <;> ring

theorem isLorChart_giV {n b : ℝ} (hn : 0 < n) (hb : 0 < b) : IsLorChart (giV n b) := by
  have hH : ∀ i j : Fin 3, hInv (giV n b) i j = if i = j then (b ^ 2)⁻¹ else 0 := by
    intro i j
    unfold hInv giV
    fin_cases i <;> fin_cases j <;> simp
  have hL10 : L10 (giV n b) = 0 := by unfold L10; rw [hH]; simp
  have hL20 : L20 (giV n b) = 0 := by unfold L20; rw [hH]; simp
  unfold IsLorChart L21 L11
  simp only [hH, hL10, hL20]
  simp [giV]
  exact ⟨by positivity, by positivity⟩

theorem ginvS_diagE {n b : ℝ} (hn : 0 < n) (hb : 0 < b) :
    ginvS (diagE n b) = giV (2 * π * n) (2 * π * b) := by
  unfold ginvS
  rw [smul_diagE]
  have : (fun i j => metric (diagE (2 * π * n) (2 * π * b)) i j) = gV (2 * π * n) (2 * π * b) :=
    funext fun i => funext fun j => metric_diagE _ _ i j
  rw [this, ginvOf_gV (by positivity) (by positivity)]

theorem isAdaptedCoframe_diagE {n b : ℝ} (hn : 0 < n) (hb : 0 < b) :
    IsAdaptedCoframe (diagE n b) := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [diagE_apply, if_neg hij.ne]
  · rw [diagE_apply, if_pos rfl]
    split_ifs <;> assumption

variable {N a : ℝ → ℝ} {h : ℝ → 𝓗}

theorem profY_periodic (hN : Function.Periodic N (2 * π)) (ha : Function.Periodic a (2 * π))
    (hh : Function.Periodic h (2 * π)) :
    IsPeriodic (2 * π) (profY (𝔄 := 𝔄) (𝓢 := 𝓢) N a h) := by
  intro z μ
  show profF N a h ((z + Pi.single μ (2 * π) : R4) 0) = profF N a h (z 0)
  by_cases hμ : μ = 0
  · subst hμ
    simp only [Pi.add_apply, Pi.single_eq_same]
    unfold profF
    rw [hN, ha, hh]
  · simp [Pi.single_eq_of_ne (Ne.symm hμ)]

/-- The dilation of a profile field is a profile field. -/
theorem dilField_profY (t₀ : ℝ) :
    dilField t₀ (profY (𝔄 := 𝔄) (𝓢 := 𝓢) N a h) =
      profY (fun s => 2 * π * N (2 * π * s + t₀)) (fun s => 2 * π * a (2 * π * s + t₀))
        (fun s => h (2 * π * s + t₀)) := by
  funext x
  rw [dilField_apply, fieldScale_apply]
  have hs : ((2 * π) • x + Pi.single 0 t₀ : R4) 0 = 2 * π * x 0 + t₀ := by
    simp [smul_eq_mul]
  show ((2 * π) • (diagE (N (((2 * π) • x + Pi.single 0 t₀ : R4) 0))
      (a (((2 * π) • x + Pi.single 0 t₀ : R4) 0))), (2 * π) • (0 : Fin 4 → 𝔄),
      h (((2 * π) • x + Pi.single 0 t₀ : R4) 0), (0 : 𝓢), (0 : CoSpinor 𝓢)) = _
  rw [hs, smul_diagE, smul_zero]
  rfl

end Packet

/-! ### The homogeneous example satisfies the hypotheses of the corollary -/

section Main

open HomogeneousNative CalibrationSampling RecordTuple NativeFrameBridge NativeStressEuler
  NativeBosonicEuler FieldScaling LocalCalibrationClosed PalatiniEuler ActualJetFrame
  HomogeneousEinsteinHiggs
open DiscreteEulerConsistency (R4 evec jet1 contEuler limDensity IsPeriodic)
open NativeScaling (Mat eta metric)
open SobolevOpen (pd)
open ActualJetSystem (ginvOf)

/-- The native data of the Einstein–Higgs model. -/
theorem ehModel_data (κ Λ lamH vH : ℝ) :
    (ehModel κ Λ lamH vH).κ = κ ∧ (ehModel κ Λ lamH vH).Λ = Λ ∧
      (ehModel κ Λ lamH vH).lamH = lamH ∧ (ehModel κ Λ lamH vH).vH = vH ∧
      ∀ x y : ℝ, (ehModel κ Λ lamH vH).hermH x y = x * y := by
  refine ⟨rfl, rfl, rfl, rfl, fun x y => ?_⟩
  simp [ehModel, diracModel]

/-- **`cor:local-calibration-nonempty`, last sentence: the backreacting homogeneous
Einstein–Higgs family in the native slab gauges.**  For couplings `κ ≠ 0`, `Λ`, `λ_H`, `v_H` and
every solution `(a, φ, π, ℋ)` of `eq:homogeneous-ODE` on `(-ε, ε)` with `a > 0`, smooth `a, φ` and the
Friedmann constraint at `0` (`prop:homogeneous`), there are the cosmic time `S` of harmonic time
(`S(π) = 0`, `S'(π) = a(0)³ ≠ 0`: a regular gauge change), smooth `2π`-periodic profiles
`N, A > 0`, `h` and a slab `[t₀, t₁]` buffered by `b` around `τ = π` such that
* near `τ = π` the Higgs profile is the homogeneous Higgs field in harmonic time,
  `√2 h(τ) = φ(S(τ))`;
* the homogeneous native field `Y = (diag(N, A, A, A), 0, h, 0, 0)` of the Einstein–Higgs slab
  model satisfies every field hypothesis of `local_calibration_nonempty` (`CalibHyps`), in
  particular the physical native Euler equations on the buffered slab. -/
theorem homogeneous_calibHyps {κ Λ lamH vH : ℝ} (hκ : κ ≠ 0) {ε : ℝ} {a φ πh ℋ : ℝ → ℝ}
    (hε : 0 < ε) (sol : IsSolution κ lamH vH a φ πh ℋ (Ioo (-ε) ε))
    (hapos : ∀ t ∈ Ioo (-ε) ε, 0 < a t) (has : ContDiffOn ℝ ∞ a (Ioo (-ε) ε))
    (hφs : ContDiffOn ℝ ∞ φ (Ioo (-ε) ε))
    (hcon : 3 * ℋ 0 ^ 2 = Λ + κ * (πh 0 ^ 2 / 2 + higgsPotential lamH vH (φ 0))) :
    ∃ (S FN FA Fh : ℝ → ℝ) (t₀ t₁ b : ℝ),
      S π = 0 ∧ HasDerivAt S (a 0 ^ 3) π ∧ π ∈ Ioo (t₀ - b) (t₁ + b) ∧
      (∀ᶠ τ in 𝓝 π, Real.sqrt 2 * Fh τ = φ (S τ)) ∧
      CalibHyps (ehSlab κ Λ lamH vH hκ) (profY (𝔄 := ℝ) (𝓢 := Sp) FN FA Fh) t₀ t₁ b := by
  obtain ⟨r, hr, hrπ, S, FN, FA, Fh, hS0, hSd, hFNs, hFAs, hFhs, hFNp, hFAp, hFhp, hFNpos,
    hFApos, hJ⟩ := exists_harmonic_profiles hε sol hapos has hφs
  have hpi := Real.pi_pos
  set M := ehSlab κ Λ lamH vH hκ with hM
  set t₀ : ℝ := π - r / 4 with ht₀def
  set t₁ : ℝ := π + r / 4 with ht₁def
  set b : ℝ := r / 8 with hbdef
  have hp : Profiles FN FA Fh := ⟨hFNs, hFAs, hFhs, hFNpos, hFApos⟩
  set Y := profY (𝔄 := ℝ) (𝓢 := Sp) FN FA Fh with hYdef
  have hbJ : ∀ τ ∈ Icc (t₀ - b) (t₁ + b), τ ∈ Ioo (π - r / 2) (π + r / 2) := fun τ hτ =>
    ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
  have hMκ : M.κ = κ := rfl
  have hMΛ : M.Λ = Λ := rfl
  have hMl : M.lamH = lamH := rfl
  have hMv : M.vH = vH := rfl
  have hMh : ∀ x y : ℝ, M.hermH x y = x * y := fun x y => by
    simp [M, ehSlab, ehModel, diracModel]
  -- the Einstein–Higgs equations on `J`
  have heqs : ∀ τ ∈ Ioo (π - r / 2) (π + r / 2),
      fried0 M.toData FN FA Fh τ = 0 ∧ friedK M.toData FN FA Fh τ = 0 ∧
      ∀ η : ℝ, 2 * (η * (-(FN τ ^ 2)⁻¹ * (deriv (deriv Fh) τ - deriv FN τ / FN τ * deriv Fh τ +
        3 * deriv FA τ / FA τ * deriv Fh τ))) =
        lamH * (2 * (Fh τ * Fh τ - vH ^ 2) * (η * Fh τ + Fh τ * η)) := by
    intro τ hτ
    obtain ⟨hSτ, hh, hA, hN, hA1, hA2, hN1, hh1, hh2⟩ := hJ τ hτ
    have hc := friedmann_constraint_propagates hε sol Λ hcon (S τ) hSτ
    obtain ⟨e0, ek, ew⟩ := harmonic_equations (κ := κ) (lamH := lamH) (vH := vH)
      (hapos _ hSτ) hc
    refine ⟨?_, ?_, fun η => ?_⟩
    · unfold fried0 KKv potential
      rw [hMκ, hMΛ, hMl, hMv, hMh, hMh, hA, hN, hA1, hh1, hh]
      simpa using e0
    · unfold friedK KKv potential
      rw [hMκ, hMΛ, hMl, hMv, hMh, hMh, hA, hN, hA1, hA2, hN1, hh1, hh]
      simpa using ek
    · rw [hA, hN, hA1, hN1, hh1, hh2, hh]
      exact ew η
  refine ⟨S, FN, FA, Fh, t₀, t₁, b, hS0, hSd, ⟨by linarith, by linarith⟩, ?_, ?_⟩
  · filter_upwards [Ioo_mem_nhds (show π - r / 2 < π by linarith) (show π < π + r / 2 by linarith)]
      with τ hτ
    rw [(hJ τ hτ).2.1]
    field_simp
  refine ⟨hp.smooth, profY_periodic hFNp hFAp hFhp, ?_, ?_, ?_, by positivity, by linarith,
    by linarith, by linarith, ?_, ?_⟩
  · -- the fixed gauges
    exact ⟨fun z => isAdaptedCoframe_diagE (hFNpos _) (hFApos _), fun z => rfl,
      fun z μ => M.gSub.zero_mem, fun z => fun x => by simp [Y, profY, profF]⟩
  · -- the compact coframe chart
    refine ⟨Set.range fun z => (Y z).1, isCompact_range_of_periodic
      (continuous_fst.comp hp.smooth.continuous) two_pi_pos fun z μ => ?_, ?_,
      fun z => ⟨z, rfl⟩⟩
    · exact congrArg Prod.fst (profY_periodic hFNp hFAp hFhp z μ)
    · rintro _ ⟨z, rfl⟩
      exact hp.det_pos z
  · -- the Lorentzian chart
    intro z
    show IsLorChart (ginvS (diagE (FN (z 0)) (FA (z 0))))
    rw [ginvS_diagE (hFNpos _) (hFApos _)]
    exact isLorChart_giV (by have := hFNpos (z 0); positivity) (by have := hFApos (z 0); positivity)
  · -- the physical native Euler equations on the buffered slab
    intro z hz
    have hz0 : z 0 ∈ Ioo (π - r / 2) (π + r / 2) := hbJ _ ⟨hz.1.1, hz.1.2.le⟩
    obtain ⟨e0, ek, ew⟩ := heqs (z 0) hz0
    rw [comp_physF_eq_zero_iff]
    intro w hw
    have hw0 : w.2.1 = 0 := funext fun μ => (Submodule.mem_bot ℝ).1 (hw μ)
    refine native_euler_profile M.toData M.κ_ne M.hermH_symm M.cliff M.sigma_eq M.gauge_cliff hp
      two_pi_pos hFNp hFAp z e0 ek (fun η => ?_) w hw0
    rw [hp.waveN_profY M.toData z]
    have := ew η
    simp only [hMh, potGrad, hMl, hMv, smul_eq_mul] at this ⊢
    exact this
  · -- the harmonic gauge of the dilated metric
    intro x hx l
    rw [dilField_profY]
    set Nd : ℝ → ℝ := fun s => 2 * π * FN (2 * π * s + t₀)
    set ad : ℝ → ℝ := fun s => 2 * π * FA (2 * π * s + t₀)
    set hd : ℝ → ℝ := fun s => Fh (2 * π * s + t₀)
    have hpd : Profiles Nd ad hd := by
      have haff : ContDiff ℝ ∞ (fun s : ℝ => 2 * π * s + t₀) :=
        (contDiff_const.mul contDiff_id).add contDiff_const
      exact ⟨contDiff_const.mul (hFNs.comp haff), contDiff_const.mul (hFAs.comp haff),
        hFhs.comp haff, fun s => by have := hFNpos (2 * π * s + t₀); positivity,
        fun s => by have := hFApos (2 * π * s + t₀); positivity⟩
    have hdF : (fun α => pd (gF (eF (profY (𝔄 := ℝ) (𝓢 := Sp) Nd ad hd))) α x) =
        dgV (Nd (x 0)) (deriv Nd (x 0)) (ad (x 0)) (deriv ad (x 0)) := by
      rw [← hpd.dF_profY (𝔄 := ℝ) (𝓢 := Sp) x]
      rfl
    unfold ActualJetWriter.C
    rw [hpd.ginvOf_profY, hdF, cUp_lapse (hpd.N_pos _).ne' (hpd.a_pos _).ne']
    split_ifs with hl
    · -- harmonic time: `N'/N = 3A'/A`
      set τ : ℝ := 2 * π * x 0 + t₀
      have hτ : τ ∈ Ioo (π - r / 2) (π + r / 2) := by
        have hx1 : 0 ≤ x 0 := hx.1
        have hx2 : x 0 ≤ slabT t₀ t₁ := hx.2
        have hT : 2 * π * slabT t₀ t₁ = t₁ - t₀ := by unfold slabT; field_simp
        constructor <;> nlinarith
      obtain ⟨hSτ, -, hA, hN, hA1, -, hN1, -, -⟩ := hJ τ hτ
      have hdN : deriv Nd (x 0) = 2 * π * (2 * π * deriv FN τ) := by
        have h1 : HasDerivAt (fun s : ℝ => 2 * π * s + t₀) (2 * π) (x 0) := by
          simpa using ((hasDerivAt_id (x 0)).const_mul (2 * π)).add_const t₀
        have h2 := ((hFNs.differentiable (by simp) τ).hasDerivAt.comp (x 0) h1).const_mul (2 * π)
        calc deriv Nd (x 0) = 2 * π * (deriv FN τ * (2 * π)) := h2.deriv
          _ = 2 * π * (2 * π * deriv FN τ) := by ring
      have hdA : deriv ad (x 0) = 2 * π * (2 * π * deriv FA τ) := by
        have h1 : HasDerivAt (fun s : ℝ => 2 * π * s + t₀) (2 * π) (x 0) := by
          simpa using ((hasDerivAt_id (x 0)).const_mul (2 * π)).add_const t₀
        have h2 := ((hFAs.differentiable (by simp) τ).hasDerivAt.comp (x 0) h1).const_mul (2 * π)
        calc deriv ad (x 0) = 2 * π * (deriv FA τ * (2 * π)) := h2.deriv
          _ = 2 * π * (2 * π * deriv FA τ) := by ring
      have hav := hapos _ hSτ
      rw [hdN, hdA]
      show (3 * (2 * π * (2 * π * deriv FA τ)) / (2 * π * FA τ) -
        2 * π * (2 * π * deriv FN τ) / (2 * π * FN τ)) / (2 * π * FN τ) ^ 2 = 0
      rw [hA, hN, hA1, hN1]
      field_simp
      ring
    · rfl

end Main

/-! ### `cor:local-calibration-nonempty` for the homogeneous example -/

section Final

open HomogeneousNative CalibrationSampling RecordTuple NativeFrameBridge NativeStressEuler
  NativeBosonicEuler FieldScaling LocalCalibrationClosed PalatiniEuler ActualJetFrame
  HomogeneousEinsteinHiggs CoupledBootstrap SlabSymmetric ActualJetCompleteForcing ActualJetState
  ActualJetSmooth
open DiscreteEulerConsistency (R4 evec jet1 contEuler limDensity IsPeriodic samp)
open NativeScaling (Mat eta metric)
open LocalCalibration (oddN meshOdd)
open NativeRate (forcingBudget)
open TrigInterp (tau)

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
variable [FiniteDimensional ℝ 𝔄] [FiniteDimensional ℝ 𝓗] [FiniteDimensional ℝ 𝓢]

/-- **`cor:local-calibration-nonempty` from the hypothesis packet** (`CalibHyps`): the reference
tuple is exact on the slab, the sampled records eventually satisfy every record hypothesis of
`thm:native-closure`, the forcing budget tends to zero and the closure distance tends to zero
(`LocalCalibrationClosed.local_calibration_nonempty`, main clauses). -/
theorem local_calibration_of_hyps {m : ℕ} (M : SlabModel 𝔄 𝓗 𝓢 m) {Y : R4 → Field 𝔄 𝓗 𝓢}
    {t₀ t₁ b : ℝ} (H : CalibHyps M Y t₀ t₁ b) {k : ℕ} (hk : 4 ≤ k) {Ck : ℝ} (hCk : 0 < Ck)
    {β c₁ c₂ : ℝ} (hβ : 0 < β) (hβk : β < 1 / (k + 4)) (hc₁ : 0 < c₁) (Kh : ℕ → ℝ)
    (hKh : ∀ᶠ m in atTop, 1 ≤ Kh m ∧ c₁ * meshOdd m ^ (-β) ≤ Kh m ∧
      Kh m ≤ c₂ * meshOdd m ^ (-β))
    {na nb : ℕ} (eY : (Fin na → ℝ) ≃L[ℝ] BosP m (HSp M))
    (eYD : (Fin nb → ℝ) ≃L[ℝ] 𝓢 × CoSpinor 𝓢) :
    ∃ (δ : ℝ) (hδ : 0 < δ) (hT : TupleHyp M δ (dilField t₀ Y)) (Ke : Set Mat) (A Cσ : ℝ),
      ExactOn (toSMData M δ) (slabT t₀ t₁) (toTuple hδ hT) ∧
      (∀ᶠ m in atTop, RecordHyp M δ Ke A t₀ t₁ b (oddN m) (samp (n := oddN m) (meshOdd m) Y)
        (Kh m) (Cσ * meshOdd m)) ∧
      Tendsto (fun m => forcingBudget k Ck (Cσ * meshOdd m) (meshOdd m) (Kh m)
          (tau (oddN m) (Kh m) 2 (samp (n := oddN m) (meshOdd m) Y))
          (tau (oddN m) (Kh m) (k + 2) (samp (n := oddN m) (meshOdd m) Y))) atTop (𝓝 0) ∧
      Tendsto (fun m => dist ((slabMod M hδ eY eYD k H.h01).obs
            (recTuple M hδ t₀ (oddN m) (samp (n := oddN m) (meshOdd m) Y) (toTuple hδ hT)))
          ((slabMod M hδ eY eYD k H.h01).obs (toTuple hδ hT))) atTop (𝓝 0) := by
  obtain ⟨Ke₀, hKe₀, hdet₀, hYe⟩ := H.chart
  obtain ⟨δ, hδ, hT, Ke, A, Cσ, C, Kr, R₁, -, -, -, -, -, -, -, hex, -, hrec, -, -, -, -, -,
    hF, -, hdist⟩ := local_calibration_nonempty M H.smooth H.per H.gauge hKe₀ hdet₀ hYe H.lor hk
      hCk H.hb H.h0 H.h1 H.h01 H.sol H.harm hβ hβk hc₁ Kh hKh eY eYD
  exact ⟨δ, hδ, hT, Ke, A, Cσ, hex, hrec, hF, hdist⟩

/-- **`cor:local-calibration-nonempty`, last sentence (corrected encoding)**: for every
backreacting-capable solution of `eq:homogeneous-ODE` (`prop:homogeneous`: `a > 0`, smooth, with the
Friedmann constraint), after the regular gauge change to harmonic time on a smaller slab (cosmic
time `S`, `S(π) = 0`, `S'(π) = a(0)³`), with the adapted coframe, cut-off and periodic extension,
the homogeneous native field `Y` of the Einstein–Higgs slab model has Higgs component
`φ(S(τ))/√2` near `τ = π` and realises `cor:local-calibration-nonempty`: for every `k ≥ 4`,
cutoff family `K_h ≍ h^{-β}` and coordinates, the reference tuple is exact, the sampled records
satisfy the record hypotheses of `thm:native-closure` eventually, `F_{h,k} → 0` and the closure
distance tends to zero. -/
theorem local_calibration_nonempty_homogeneous {κ Λ lamH vH : ℝ} (hκ : κ ≠ 0) {ε : ℝ}
    {a φ πh ℋ : ℝ → ℝ} (hε : 0 < ε) (sol : IsSolution κ lamH vH a φ πh ℋ (Ioo (-ε) ε))
    (hapos : ∀ t ∈ Ioo (-ε) ε, 0 < a t) (has : ContDiffOn ℝ ∞ a (Ioo (-ε) ε))
    (hφs : ContDiffOn ℝ ∞ φ (Ioo (-ε) ε))
    (hcon : 3 * ℋ 0 ^ 2 = Λ + κ * (πh 0 ^ 2 / 2 + higgsPotential lamH vH (φ 0))) :
    ∃ (S : ℝ → ℝ) (Y : R4 → Field ℝ ℝ Sp) (t₀ t₁ b : ℝ) (H : CalibHyps (ehSlab κ Λ lamH vH hκ) Y t₀ t₁ b),
      S π = 0 ∧ HasDerivAt S (a 0 ^ 3) π ∧ π ∈ Ioo (t₀ - b) (t₁ + b) ∧
      (∀ᶠ τ in 𝓝 π, ∀ y : R4, y 0 = τ → Real.sqrt 2 * (Y y).2.2.1 = φ (S τ)) ∧
      ∀ {k : ℕ} (hk : 4 ≤ k) {Ck : ℝ} (hCk : 0 < Ck) {β c₁ c₂ : ℝ} (hβ : 0 < β)
        (hβk : β < 1 / (k + 4)) (hc₁ : 0 < c₁) (Kh : ℕ → ℝ)
        (hKh : ∀ᶠ m in atTop, 1 ≤ Kh m ∧ c₁ * meshOdd m ^ (-β) ≤ Kh m ∧
          Kh m ≤ c₂ * meshOdd m ^ (-β))
        {na nb : ℕ} (eY : (Fin na → ℝ) ≃L[ℝ] BosP 1 (HSp (ehSlab κ Λ lamH vH hκ)))
        (eYD : (Fin nb → ℝ) ≃L[ℝ] Sp × CoSpinor Sp),
      ∃ (δ : ℝ) (hδ : 0 < δ) (hT : TupleHyp (ehSlab κ Λ lamH vH hκ) δ (dilField t₀ Y))
        (Ke : Set Mat) (A Cσ : ℝ),
        ExactOn (toSMData (ehSlab κ Λ lamH vH hκ) δ) (slabT t₀ t₁) (toTuple hδ hT) ∧
        (∀ᶠ m in atTop, RecordHyp (ehSlab κ Λ lamH vH hκ) δ Ke A t₀ t₁ b (oddN m)
          (samp (n := oddN m) (meshOdd m) Y) (Kh m) (Cσ * meshOdd m)) ∧
        Tendsto (fun m => forcingBudget k Ck (Cσ * meshOdd m) (meshOdd m) (Kh m)
            (tau (oddN m) (Kh m) 2 (samp (n := oddN m) (meshOdd m) Y))
            (tau (oddN m) (Kh m) (k + 2) (samp (n := oddN m) (meshOdd m) Y))) atTop (𝓝 0) ∧
        Tendsto (fun m => dist ((slabMod (ehSlab κ Λ lamH vH hκ) hδ eY eYD k H.h01).obs
              (recTuple (ehSlab κ Λ lamH vH hκ) hδ t₀ (oddN m) (samp (n := oddN m) (meshOdd m) Y)
                (toTuple hδ hT)))
            ((slabMod (ehSlab κ Λ lamH vH hκ) hδ eY eYD k H.h01).obs (toTuple hδ hT))) atTop
          (𝓝 0) := by
  obtain ⟨S, FN, FA, Fh, t₀, t₁, b, hS0, hSd, hπ, hφ, H⟩ :=
    homogeneous_calibHyps hκ hε sol hapos has hφs hcon
  refine ⟨S, _, t₀, t₁, b, H, hS0, hSd, hπ, ?_,
    fun {k} hk {Ck} hCk {β c₁ c₂} hβ hβk hc₁ Kh hKh {na nb} eY eYD =>
      local_calibration_of_hyps _ H hk hCk hβ hβk hc₁ Kh hKh eY eYD⟩
  filter_upwards [hφ] with τ hτ y hy
  rw [← hτ, ← hy]
  rfl

/-- **The example violates the complete (all-`𝔄`) system**: if the solution is backreacting
(`π(0) ≠ 0`), the homogeneous native field of `homogeneous_calibHyps` — which satisfies the
physical native Euler equations — does **not** satisfy the complete Euler equations on the buffered
slab (the unit gauge row `-2v g^{σν}⟨H, ∂_νH⟩` is nonzero; `CalibrationBackreacting`).  This is the
row the corrected encoding removed. -/
theorem homogeneous_violates_complete {κ Λ lamH vH : ℝ} (hκ : κ ≠ 0) {ε : ℝ}
    {a φ πh ℋ : ℝ → ℝ} (hε : 0 < ε) (sol : IsSolution κ lamH vH a φ πh ℋ (Ioo (-ε) ε))
    (hapos : ∀ t ∈ Ioo (-ε) ε, 0 < a t) (has : ContDiffOn ℝ ∞ a (Ioo (-ε) ε))
    (hφs : ContDiffOn ℝ ∞ φ (Ioo (-ε) ε))
    (hcon : 3 * ℋ 0 ^ 2 = Λ + κ * (πh 0 ^ 2 / 2 + higgsPotential lamH vH (φ 0)))
    (hπ : πh 0 ≠ 0) :
    ∃ (Y : R4 → Field ℝ ℝ Sp) (t₀ t₁ b : ℝ), CalibHyps (ehSlab κ Λ lamH vH hκ) Y t₀ t₁ b ∧
      ¬ ∀ z ∈ NativeZeroSource.bufSlab (t₀ - b) (t₁ + b),
        contEuler (limDensity (ι := Shift) (firstJetDensity (ehSlab κ Λ lamH vH hκ).toData)) Y z = 0 := by
  obtain ⟨S, FN, FA, Fh, t₀, t₁, b, hS0, hSd, hπs, hφ, H⟩ :=
    homogeneous_calibHyps hκ hε sol hapos has hφs hcon
  refine ⟨_, t₀, t₁, b, H, ?_⟩
  obtain ⟨Ke₀, -, hdet₀, hYe⟩ := H.chart
  have hs0 : Real.sqrt 2 ≠ 0 := by positivity
  have hh0 : (ehSlab κ Λ lamH vH hκ).hermH (Real.sqrt 2)⁻¹ (Real.sqrt 2)⁻¹ ≠ 0 := by
    have : (ehSlab κ Λ lamH vH hκ).hermH (Real.sqrt 2)⁻¹ (Real.sqrt 2)⁻¹ =
        (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ := by simp [ehSlab, ehModel, diracModel]
    rw [this]
    positivity
  have hHf : ∀ y : R4, (profY (𝔄 := ℝ) (𝓢 := Sp) FN FA Fh y).2.2.1 =
      (fun s => Real.sqrt 2 * Fh s) (y 0) • (Real.sqrt 2)⁻¹ := by
    intro y
    show Fh (y 0) = (Real.sqrt 2 * Fh (y 0)) * (Real.sqrt 2)⁻¹
    field_simp
  have hφ' : (fun s => Real.sqrt 2 * Fh s) =ᶠ[𝓝 π] φ ∘ S := hφ
  exact CalibrationBackreacting.slab_hsol_fails_backreacting (ehSlab κ Λ lamH vH hκ) sol hε hπ
    hS0 hSd (pow_ne_zero 3 (hapos 0 ⟨by linarith, hε⟩).ne') hπs H.smooth
    (fun z => hdet₀ _ (hYe z)) (fun y => rfl) (fun y => rfl) hh0 hHf hφ'


/-- **A concrete backreacting instance** (`κ = 1`, `Λ = λ_H = v_H = 0`, initial data `a₀ = 1`,
`φ₀ = 0`, `π₀ = 1`, `ℋ₀ = 1/√6` on the Friedmann constraint): the homogeneous family of
`prop:homogeneous` is backreacting (`ℋ'(0) = -½ < 0`), its harmonic-time native field satisfies
every field hypothesis of `local_calibration_nonempty` (hence realises the corollary), and it
violates the complete all-`𝔄` system. -/
theorem homogeneous_backreacting_instance :
    ∃ (ε : ℝ) (a φ πh ℋ : ℝ → ℝ) (Y : R4 → Field ℝ ℝ Sp) (t₀ t₁ b : ℝ),
      HomogeneousEinsteinHiggs.IsSolution 1 0 0 a φ πh ℋ (Ioo (-ε) ε) ∧ 0 < ε ∧
      HasDerivAt ℋ (-(1 / 2) * πh 0 ^ 2) 0 ∧ -(1 / 2) * πh 0 ^ 2 < 0 ∧
      CalibHyps (ehSlab 1 0 0 0 one_ne_zero) Y t₀ t₁ b ∧
      ¬ ∀ z ∈ NativeZeroSource.bufSlab (t₀ - b) (t₁ + b),
        contEuler (limDensity (ι := Shift) (firstJetDensity (ehSlab 1 0 0 0 one_ne_zero).toData))
          Y z = 0 := by
  obtain ⟨ε, hε, a, φ, πh, ℋ, ha0, hφ0, hπ0, hℋ0, sol, hapos, has, hφs, -, -⟩ :=
    HomogeneousEinsteinHiggs.exists_local_solution 1 0 0 1 0 1 (Real.sqrt 6)⁻¹ one_pos
  have hcon : 3 * ℋ 0 ^ 2 = 0 + 1 * (πh 0 ^ 2 / 2 + HomogeneousEinsteinHiggs.higgsPotential 0 0 (φ 0)) := by
    rw [hℋ0, hπ0, hφ0]
    unfold HomogeneousEinsteinHiggs.higgsPotential
    have h6 : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
    rw [inv_pow, h6]
    norm_num
  have hπ : πh 0 ≠ 0 := by rw [hπ0]; norm_num
  obtain ⟨Y, t₀, t₁, b, H, hviol⟩ :=
    homogeneous_violates_complete one_ne_zero hε sol hapos has hφs hcon hπ
  have h0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
  obtain ⟨hd, hneg⟩ := HomogeneousEinsteinHiggs.backreaction_of_pi_ne_zero sol one_pos h0 hπ
  exact ⟨ε, a, φ, πh, ℋ, Y, t₀, t₁, b, sol, hε, by simpa using hd, by simpa using hneg, H, hviol⟩
end Final
end RenewalGeometry.HomogeneousCalibration
