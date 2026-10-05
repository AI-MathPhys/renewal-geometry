/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.SymmetricHyperbolicEnergy
import RenewalGeometry.Continuum.SlabSobolevAlgebra
import RenewalGeometry.Analysis.ODECutoffContinuation

/-!
# `H^k` energy estimate and first-exit bootstrap for first-order symmetric hyperbolic systems

Generic infrastructure (no renewal notions) for `prop:coupled-bootstrap`
(`eq:actual-jet-gauge-energy`, `eq:actual-jet-integrated-stability`) of the Einstein–Standard-Model
action-closure manuscript.

Space-time is `ℝ^{1+d}` (`SymHypEnergy` conventions: time coordinate `0`, points `Fin.cons t y`,
fields `ℤ^d`-periodic in space, slices integrated over `[0,1]^d`).  A first-order system
`∂_tW + Σ_j A^j∂_jW = G` with Hermitian `A^j` (the realified block-symmetric systems of
`prop:actual-jet-writer` are a special case: real symmetric matrices are Hermitian) is written with
`A⁰ = 1` (`IsUnitTime`).

* `integral_gronwall` — `φ(t) ≤ A + B∫₀ᵗφ` ⇒ `φ(t) ≤ A e^{Bt}` (continuous `φ`, `B ≥ 0`).
* `vsd w α` — iterated spatial derivative along a word `α`; `EK k w t = Σ_{|α| ≤ k} ‖∂^αw(t)‖²_{L²}`
  (the `H^k` energy).
* **`hk_energy_estimate`** — if every `∂^αw`, `|α| ≤ k`, satisfies the hypotheses of the `L²`
  estimate (`SymHypEnergy.SymHyp`: Hermitian `W^{1,∞}` coefficients) and the commuted forcing
  obeys `Σ_α ‖Σ_μ A^μ∂_μ∂^αw(t)‖²_{L²} ≤ K₁ E_k(t) + Φ(t)`, then
  `E_k(t) ≤ e^{KT}(|N|²C_b E_k(0) + |N|∫₀ᵀΦ) · exp(e^{KT}|N|K₁ t)` on `[0, T]` — the symmetric
  hyperbolic `H^k` energy inequality with Gronwall (`eq:actual-jet-gauge-energy`,
  `eq:actual-jet-integrated-stability`).
* **`first_exit_bootstrap`** — the first-exit argument of the proof of `prop:coupled-bootstrap`:
  if on every initial interval inside the tube `E_k ≤ ρ²` the coefficient hypotheses and the
  commuted forcing bound hold with constants depending only on `ρ`, and the resulting bound is
  `< ρ²`, then `E_k` never leaves the tube and the bound holds on all of `[0, T]`; no a priori
  all-time bound is assumed.
-/

open MeasureTheory Filter Topology Set
open scoped BigOperators ENNReal NNReal ContDiff

noncomputable section

namespace RenewalGeometry.FOSymHk

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy

set_option linter.unusedSectionVars false

/-! ### Integral Gronwall -/

/-- **Integral Gronwall inequality.**  If `φ` is continuous on `[0, T]` and
`φ(t) ≤ A + B ∫₀ᵗ φ` there, with `B ≥ 0`, then `φ(t) ≤ A e^{Bt}` on `[0, T]`. -/
theorem integral_gronwall {φ : ℝ → ℝ} {T A B : ℝ} (hT : 0 ≤ T) (hB : 0 ≤ B)
    (hφ : ContinuousOn φ (Icc 0 T))
    (h : ∀ t ∈ Icc 0 T, φ t ≤ A + B * ∫ s in (0 : ℝ)..t, φ s) :
    ∀ t ∈ Icc 0 T, φ t ≤ A * Real.exp (B * t) := by
  set Ψ : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, φ s with hΨ
  have hint : ∀ t ∈ Icc 0 T, IntervalIntegrable φ volume 0 t := fun t ht =>
    (hφ.mono (Icc_subset_Icc le_rfl ht.2)).intervalIntegrable_of_Icc ht.1
  have hΨc : ContinuousOn Ψ (Icc 0 T) := by
    have : ContinuousOn (fun t => ∫ s in (0 : ℝ)..t, φ s) (uIcc 0 T) :=
      intervalIntegral.continuousOn_primitive_interval' (hφ.intervalIntegrable_of_Icc hT)
        (by simp [hT])
    rwa [uIcc_of_le hT] at this
  have hder : ∀ x ∈ Ico 0 T, HasDerivWithinAt Ψ (φ x) (Ici x) x := by
    intro x hx
    have hxT : x ∈ Icc 0 T := Ico_subset_Icc_self hx
    have hcont : ContinuousOn φ (Icc x T) := hφ.mono (Icc_subset_Icc hx.1 le_rfl)
    have hmeas : StronglyMeasurableAtFilter φ (𝓝[>] x) volume :=
      (hcont.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc x).filter_mono
        (nhdsWithin_le_of_mem (Icc_mem_nhdsGT hx.2))
    have hcw : ContinuousWithinAt φ (Ioi x) x :=
      (hcont x ⟨le_rfl, hx.2.le⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsGT hx.2)
    exact intervalIntegral.integral_hasDerivWithinAt_right (hint x hxT) hmeas hcw
  have hG : ∀ t ∈ Icc 0 T, Ψ t ≤ gronwallBound 0 B A (t - 0) :=
    le_gronwallBound_of_liminf_deriv_right_le hΨc
      (fun x hx r hr => (hder x hx).liminf_right_slope_le hr)
      (by simp [hΨ]) (fun x hx => by
        have := h x (Ico_subset_Icc_self hx)
        simp only [hΨ]; linarith)
  intro t ht
  have h1 := h t ht
  have h2 := hG t ht
  rw [sub_zero] at h2
  by_cases hB0 : B = 0
  · subst hB0; simpa using h1
  · rw [gronwallBound_of_K_ne_0 hB0] at h2
    have hBp : 0 < B := lt_of_le_of_ne hB (Ne.symm hB0)
    calc φ t ≤ A + B * Ψ t := h1
      _ ≤ A + B * (0 * Real.exp (B * t) + A / B * (Real.exp (B * t) - 1)) := by
          gcongr
      _ = A * Real.exp (B * t) := by field_simp; ring

/-! ### Iterated spatial derivatives and the `H^k` energy -/

variable {d : ℕ} {N : Type*} [Fintype N] [DecidableEq N]

/-- The iterated spatial derivative `∂^α w` along a word `α` (innermost letter first). -/
def vsd : List (Fin d) → ((Fin (d + 1) → ℝ) → N → ℂ) → (Fin (d + 1) → ℝ) → N → ℂ
  | [], w => w
  | i :: l, w => vsd l (pd w i.succ)

/-- The `H^k` energy `E_k(t) = Σ_{|α| ≤ k} ‖∂^αw(t)‖²_{L²([0,1]^d)}`. -/
def EK (k : ℕ) (w : (Fin (d + 1) → ℝ) → N → ℂ) (t : ℝ) : ℝ :=
  ∑ α ∈ SlabSobAlg.wordsLE d k, l2sq (vsd α w) t

/-- The time coefficient is the identity: `∂_tW + Σ_j A^j∂_jW`. -/
def IsUnitTime (A : Fin (d + 1) → (Fin (d + 1) → ℝ) → N → N → ℂ) : Prop :=
  ∀ x, A 0 x = fun i j => if i = j then 1 else 0

/-- The constant of the `L²` estimate for `A⁰ = 1` (`c = 1`, `K₀ = 0`). -/
def Kc (d : ℕ) (N : Type*) [Fintype N] (L : ℝ≥0) : ℝ :=
  (((d : ℝ) + 1) * ((Fintype.card N : ℝ) ^ 2 * L) + Fintype.card N * (1 + 2 * 0)) / 1 + 1

theorem Kc_nonneg (L : ℝ≥0) : 0 ≤ Kc d N L := by unfold Kc; positivity

variable {A : Fin (d + 1) → (Fin (d + 1) → ℝ) → N → N → ℂ} {w : (Fin (d + 1) → ℝ) → N → ℂ}
  {a b T : ℝ} {L : ℝ≥0} {Cb : ℝ}

/-- Restriction of the `L²` hypotheses to a subslab. -/
theorem restrictSymHyp {t₀ t₁ s₀ s₁ : ℝ} (h : SymHyp A w a t₀ t₁ b L Cb) (h0 : t₀ ≤ s₀)
    (h01 : s₀ < s₁) (h1 : s₁ ≤ t₁) : SymHyp A w a s₀ s₁ b L Cb where
  ha := h.ha.trans_le h0
  h01 := h01
  hb := h1.trans_lt h.hb
  smooth := h.smooth
  wper := h.wper
  Aper := h.Aper
  herm := h.herm
  lip := fun μ => (h.lip μ).mono fun x hx => ⟨h0.trans hx.1, hx.2.trans h1⟩
  bound := fun μ x hx => h.bound μ x ⟨h0.trans hx.1, hx.2.trans h1⟩

theorem unitTime_pos (hA0 : IsUnitTime A) (x : Fin (d + 1) → ℝ) (ξ : N → ℂ) :
    1 * ∑ i, ‖ξ i‖ ^ 2 ≤ ip ξ (mv (A 0 x) ξ) := by
  have hA0' : A 0 x = fun i j => if i = j then 1 else 0 := hA0 x
  rw [hA0', one_mul]
  unfold ip mv
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [Complex.re_sum]
  refine le_of_eq (Finset.sum_congr rfl fun i _ => ?_)
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp [Complex.mul_re]

theorem one_le_Cb [Nonempty N] (h : SymHyp A w a 0 T b L Cb) (hA0 : IsUnitTime A) :
    1 ≤ Cb := by
  have hx : (Fin.cons 0 0 : Fin (d + 1) → ℝ) ∈ slab 0 T := (cons_mem_slab _).mpr
    ⟨le_rfl, h.h01.le⟩
  have hb := h.bound 0 _ hx
  have hA0' : A 0 (Fin.cons 0 0) = fun i j => if i = j then 1 else 0 := hA0 _
  obtain ⟨i⟩ := (inferInstance : Nonempty N)
  have e : (1 : ℂ) = A 0 (Fin.cons 0 0) i i := by rw [hA0']; simp
  have key : ‖(1 : ℂ)‖ ≤ ‖A 0 (Fin.cons 0 0)‖ := by
    rw [e]
    exact (norm_le_pi_norm (A 0 (Fin.cons 0 0) i) i).trans (norm_le_pi_norm (A 0 (Fin.cons 0 0)) i)
  rw [norm_one] at key
  linarith

theorem l2sq_nonneg (v : (Fin (d + 1) → ℝ) → N → ℂ) (t : ℝ) : 0 ≤ l2sq v t :=
  setIntegral_nonneg measurableSet_Icc fun _ _ => sq_nonneg _

theorem l2sq_continuousOn (h : SymHyp A w a 0 T b L Cb) : ContinuousOn (l2sq w) (Icc 0 T) :=
  continuousOn_sliceIntegral (Φ := fun x => ‖w x‖ ^ 2) h.h01.le
    ((h.w_cont.mono h.sub).norm.pow 2)

/-- The squared `L²` norm of the principal part on the slice. -/
def princSq (A : Fin (d + 1) → (Fin (d + 1) → ℝ) → N → N → ℂ) (v : (Fin (d + 1) → ℝ) → N → ℂ)
    (t : ℝ) : ℝ :=
  ∫ y in Icc (0 : Fin d → ℝ) 1, ‖princ A v (Fin.cons t y)‖ ^ 2

theorem princSq_continuousOn (h : SymHyp A w a 0 T b L Cb) :
    ContinuousOn (princSq A w) (Icc 0 T) :=
  continuousOn_sliceIntegral (Φ := fun x => ‖princ A w x‖ ^ 2) h.h01.le (h.princ_cont.norm.pow 2)

theorem princSq_nonneg (v : (Fin (d + 1) → ℝ) → N → ℂ) (t : ℝ) : 0 ≤ princSq A v t :=
  setIntegral_nonneg measurableSet_Icc fun _ _ => sq_nonneg _

/-- **The `L²` estimate for one derivative, on `[0, t]`:**
`‖v(t)‖² ≤ e^{KT}(|N|²C_b‖v(0)‖² + |N|∫₀ᵗ‖Σ_μA^μ∂_μv‖²)` for `t ∈ [0, T]`. -/
theorem word_estimate (h : SymHyp A w a 0 T b L Cb) (hA0 : IsUnitTime A) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    l2sq w t ≤ Real.exp (Kc d N L * T) * ((Fintype.card N : ℝ) ^ 2 * Cb * l2sq w 0 +
      Fintype.card N * ∫ τ in (0 : ℝ)..t, princSq A w τ) := by
  have hT : 0 < T := h.h01
  have hK := Kc_nonneg (d := d) (N := N) L
  rcases isEmpty_or_nonempty N with hN | hN
  · have : l2sq w t = 0 := by
      unfold l2sq
      simp [Subsingleton.elim (w _) 0]
    rw [this]
    have h0 : l2sq w 0 = 0 := by unfold l2sq; simp [Subsingleton.elim (w _) 0]
    simp [h0]
  rcases ht.1.lt_or_eq with htpos | ht0
  · have hr := restrictSymHyp h le_rfl htpos ht.2
    have hest := l2_energy_estimate hr one_pos le_rfl (fun x _ ξ => unitTime_pos hA0 x ξ)
      (m := fun x => ‖princ A w x‖) (hr.princ_cont.norm) (fun x _ => by simp) t
      ⟨htpos.le, le_rfl⟩
    rw [one_mul] at hest
    have hCb : 0 ≤ Cb := zero_le_one.trans (one_le_Cb h hA0)
    refine hest.trans (mul_le_mul_of_nonneg_right ?_ ?_)
    · rw [Real.exp_le_exp, sub_zero]
      exact mul_le_mul_of_nonneg_left ht.2 (by positivity)
    · exact add_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) hCb) (l2sq_nonneg _ _))
        (mul_nonneg (Nat.cast_nonneg _) (intervalIntegral.integral_nonneg htpos.le fun τ _ =>
          setIntegral_nonneg measurableSet_Icc fun _ _ => sq_nonneg _))
  · subst ht0
    simp only [intervalIntegral.integral_same, mul_zero, add_zero]
    have hCb := one_le_Cb h hA0
    have hn : (1 : ℝ) ≤ Fintype.card N := by
      exact_mod_cast Fintype.card_pos
    have he : 1 ≤ Real.exp (Kc d N L * T) := Real.one_le_exp (by positivity)
    have hl := l2sq_nonneg w 0
    have h1 : (1 : ℝ) ≤ (Fintype.card N : ℝ) ^ 2 * Cb := by nlinarith
    calc l2sq w 0 = 1 * (1 * l2sq w 0) := by ring
      _ ≤ Real.exp (Kc d N L * T) * ((Fintype.card N : ℝ) ^ 2 * Cb * l2sq w 0) := by
          gcongr

theorem Cb_nonneg (h : SymHyp A w a 0 T b L Cb) : 0 ≤ Cb := by
  have hx : (Fin.cons 0 0 : Fin (d + 1) → ℝ) ∈ slab 0 T := (cons_mem_slab _).mpr
    ⟨le_rfl, h.h01.le⟩
  exact (norm_nonneg _).trans (h.bound 0 _ hx)

theorem EK_nonneg (k : ℕ) (w : (Fin (d + 1) → ℝ) → N → ℂ) (t : ℝ) : 0 ≤ EK k w t :=
  Finset.sum_nonneg fun α _ => l2sq_nonneg _ _

/-- The bound of the `H^k` energy estimate. -/
def hkBound (d : ℕ) (N : Type*) [Fintype N] (L : ℝ≥0) (Cb K₁ E0 S T t : ℝ) : ℝ :=
  Real.exp (Kc d N L * T) * ((Fintype.card N : ℝ) ^ 2 * Cb * E0 + Fintype.card N * S) *
    Real.exp (Real.exp (Kc d N L * T) * Fintype.card N * K₁ * t)

/-- **The `H^k` energy estimate for a first-order symmetric hyperbolic system**
(`eq:actual-jet-gauge-energy` integrated with Gronwall, `eq:actual-jet-integrated-stability`).
If every `∂^αw`, `|α| ≤ k`, satisfies the `L²` hypotheses (`SymHyp`: Hermitian, bounded,
Lipschitz coefficients, `A⁰ = 1`) on `[0, T]`, and the commuted forcing satisfies
`Σ_α ‖Σ_μ A^μ∂_μ∂^αw(t)‖²_{L²} ≤ K₁E_k(t) + Φ(t)` with `Φ ≥ 0` continuous, then for `t ∈ [0, T]`
`E_k(t) ≤ e^{KT}(|N|²C_bE_k(0) + |N|∫₀ᵀΦ) exp(e^{KT}|N|K₁t)`. -/
theorem hk_energy_estimate {k : ℕ} {K₁ : ℝ} {Φ : ℝ → ℝ} (hA0 : IsUnitTime A)
    (hS : ∀ α ∈ SlabSobAlg.wordsLE d k, SymHyp A (vsd α w) a 0 T b L Cb)
    (hK₁ : 0 ≤ K₁) (hΦc : ContinuousOn Φ (Icc 0 T)) (hΦ0 : ∀ t ∈ Icc 0 T, 0 ≤ Φ t)
    (hforce : ∀ t ∈ Icc 0 T,
      ∑ α ∈ SlabSobAlg.wordsLE d k, princSq A (vsd α w) t ≤ K₁ * EK k w t + Φ t) :
    ∀ t ∈ Icc 0 T, EK k w t ≤
      hkBound d N L Cb K₁ (EK k w 0) (∫ s in (0 : ℝ)..T, Φ s) T t := by
  have hT : 0 ≤ T := (hS [] (SlabSobAlg.nil_mem_wordsLE k)).h01.le
  set Ce := Real.exp (Kc d N L * T) with hCe
  set n : ℝ := (Fintype.card N : ℝ) with hn
  have hCe0 : 0 ≤ Ce := (Real.exp_pos _).le
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  have hCb : 0 ≤ Cb := Cb_nonneg (hS [] (SlabSobAlg.nil_mem_wordsLE k))
  have hEc : ContinuousOn (EK k w) (Icc 0 T) :=
    continuousOn_finsetSum _ fun α hα => l2sq_continuousOn (hS α hα)
  have hPc : ∀ α ∈ SlabSobAlg.wordsLE d k, ContinuousOn (princSq A (vsd α w)) (Icc 0 T) :=
    fun α hα => princSq_continuousOn (hS α hα)
  have hii : ∀ t ∈ Icc 0 T, ∀ {f : ℝ → ℝ}, ContinuousOn f (Icc 0 T) →
      IntervalIntegrable f volume 0 t := fun t ht f hf =>
    (hf.mono (Icc_subset_Icc le_rfl ht.2)).intervalIntegrable_of_Icc ht.1
  have step : ∀ t ∈ Icc 0 T, EK k w t ≤ Ce * (n ^ 2 * Cb * EK k w 0 + n * ∫ s in (0 : ℝ)..T, Φ s)
      + Ce * n * K₁ * ∫ s in (0 : ℝ)..t, EK k w s := by
    intro t ht
    have h1 : EK k w t ≤ ∑ α ∈ SlabSobAlg.wordsLE d k, Ce * (n ^ 2 * Cb * l2sq (vsd α w) 0 +
        n * ∫ τ in (0 : ℝ)..t, princSq A (vsd α w) τ) :=
      Finset.sum_le_sum fun α hα => word_estimate (hS α hα) hA0 ht
    have h2 : ∑ α ∈ SlabSobAlg.wordsLE d k, Ce * (n ^ 2 * Cb * l2sq (vsd α w) 0 +
        n * ∫ τ in (0 : ℝ)..t, princSq A (vsd α w) τ) =
        Ce * (n ^ 2 * Cb * EK k w 0 +
          n * ∫ τ in (0 : ℝ)..t, ∑ α ∈ SlabSobAlg.wordsLE d k, princSq A (vsd α w) τ) := by
      rw [intervalIntegral.integral_finsetSum fun α hα => hii t ht (hPc α hα)]
      unfold EK
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
    have h3 : ∫ τ in (0 : ℝ)..t, ∑ α ∈ SlabSobAlg.wordsLE d k, princSq A (vsd α w) τ ≤
        ∫ τ in (0 : ℝ)..t, (K₁ * EK k w τ + Φ τ) :=
      intervalIntegral.integral_mono_on ht.1
        (hii t ht (continuousOn_finsetSum _ hPc))
        (hii t ht ((continuousOn_const.mul hEc).add hΦc))
        fun τ hτ => hforce τ ⟨hτ.1, hτ.2.trans ht.2⟩
    have h4 : ∫ τ in (0 : ℝ)..t, (K₁ * EK k w τ + Φ τ) =
        K₁ * (∫ τ in (0 : ℝ)..t, EK k w τ) + ∫ τ in (0 : ℝ)..t, Φ τ := by
      rw [intervalIntegral.integral_add ((hii t ht hEc).const_mul K₁) (hii t ht hΦc),
        intervalIntegral.integral_const_mul]
    have h5 : ∫ τ in (0 : ℝ)..t, Φ τ ≤ ∫ τ in (0 : ℝ)..T, Φ τ := by
      refine intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2 ?_
        (hΦc.intervalIntegrable_of_Icc hT)
      refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun τ hτ => ?_)
      exact hΦ0 τ ⟨hτ.1.le, hτ.2⟩
    have hmono : n * ∫ τ in (0 : ℝ)..t, ∑ α ∈ SlabSobAlg.wordsLE d k, princSq A (vsd α w) τ ≤
        n * (K₁ * (∫ τ in (0 : ℝ)..t, EK k w τ) + ∫ τ in (0 : ℝ)..T, Φ τ) := by
      refine mul_le_mul_of_nonneg_left ?_ hn0
      rw [← h4.symm.le.antisymm h4.le] at h3
      linarith
    calc EK k w t ≤ _ := h1
      _ = _ := h2
      _ ≤ Ce * (n ^ 2 * Cb * EK k w 0 +
          n * (K₁ * (∫ τ in (0 : ℝ)..t, EK k w τ) + ∫ τ in (0 : ℝ)..T, Φ τ)) := by
        gcongr
      _ = _ := by ring
  have hg := integral_gronwall hT (by positivity) hEc step
  intro t ht
  refine (hg t ht).trans (le_of_eq ?_)
  unfold hkBound
  rw [← hCe, ← hn]

/-- Monotonicity of the bound in the time interval (for `Φ ≥ 0`). -/
theorem hkBound_mono {L : ℝ≥0} {Cb K₁ E0 : ℝ} {Φ : ℝ → ℝ} {t T : ℝ} (hCb : 0 ≤ Cb)
    (hK₁ : 0 ≤ K₁) (hE0 : 0 ≤ E0) (ht : 0 ≤ t) (htT : t ≤ T) (hΦc : ContinuousOn Φ (Icc 0 T))
    (hΦ0 : ∀ s ∈ Icc 0 T, 0 ≤ Φ s) :
    hkBound d N L Cb K₁ E0 (∫ s in (0 : ℝ)..t, Φ s) t t ≤
      hkBound d N L Cb K₁ E0 (∫ s in (0 : ℝ)..T, Φ s) T T := by
  have hK : 0 ≤ Kc d N L := Kc_nonneg L
  have hS0 : 0 ≤ ∫ s in (0 : ℝ)..t, Φ s :=
    intervalIntegral.integral_nonneg ht fun s hs => hΦ0 s ⟨hs.1, hs.2.trans htT⟩
  have hS : ∫ s in (0 : ℝ)..t, Φ s ≤ ∫ s in (0 : ℝ)..T, Φ s := by
    refine intervalIntegral.integral_mono_interval le_rfl ht htT ?_
      (hΦc.intervalIntegrable_of_Icc (ht.trans htT))
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun τ hτ => ?_)
    exact hΦ0 τ ⟨hτ.1.le, hτ.2⟩
  have he1 : Real.exp (Kc d N L * t) ≤ Real.exp (Kc d N L * T) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left htT hK)
  have hn0 : (0 : ℝ) ≤ Fintype.card N := Nat.cast_nonneg _
  have hB1 : 0 ≤ (Fintype.card N : ℝ) ^ 2 * Cb * E0 + Fintype.card N * ∫ s in (0 : ℝ)..t, Φ s :=
    add_nonneg (by positivity) (mul_nonneg hn0 hS0)
  have hB12 : (Fintype.card N : ℝ) ^ 2 * Cb * E0 + Fintype.card N * ∫ s in (0 : ℝ)..t, Φ s ≤
      (Fintype.card N : ℝ) ^ 2 * Cb * E0 + Fintype.card N * ∫ s in (0 : ℝ)..T, Φ s := by
    gcongr
  have he2 : Real.exp (Real.exp (Kc d N L * t) * Fintype.card N * K₁ * t) ≤
      Real.exp (Real.exp (Kc d N L * T) * Fintype.card N * K₁ * T) := by
    rw [Real.exp_le_exp]
    have : Real.exp (Kc d N L * t) * Fintype.card N * K₁ ≤
        Real.exp (Kc d N L * T) * Fintype.card N * K₁ := by gcongr
    have h0 : 0 ≤ Real.exp (Kc d N L * T) * Fintype.card N * K₁ := by positivity
    calc _ ≤ Real.exp (Kc d N L * T) * Fintype.card N * K₁ * t := by gcongr
      _ ≤ _ := mul_le_mul_of_nonneg_left htT h0
  unfold hkBound
  exact mul_le_mul (mul_le_mul he1 hB12 hB1 (Real.exp_pos _).le) he2 (Real.exp_pos _).le
    (mul_nonneg (Real.exp_pos _).le (hB1.trans hB12))

/-- **First-exit bootstrap** (`prop:coupled-bootstrap`, proof of `eq:bootstrap-state`).  Let
`E_k` be continuous on `[0, T]` (the smooth actual record exists on the slab; no a priori bound
is assumed).  Suppose that on every initial interval `[0, t₁]` on which the state stays in the tube
`E_k ≤ ρ`, all `∂^αw` satisfy the `L²` hypotheses with **uniform** constants `L, C_b` and the
commuted forcing satisfies `Σ_α‖Σ_μA^μ∂_μ∂^αw‖² ≤ K₁E_k + Φ` (with `K₁, Φ` independent of `t₁`).
If the initial state lies in the smaller tube and the bound is below the tube radius,
`E_k(0) ≤ B < ρ` with `B = hkBound(E_k(0), ∫₀ᵀΦ)`, then `E_k ≤ B` on all of `[0, T]`. -/
theorem first_exit_bootstrap {k : ℕ} {ρ K₁ : ℝ} {Φ : ℝ → ℝ} (hA0 : IsUnitTime A)
    (hcont : ContinuousOn (EK k w) (Icc 0 T)) (hCb : 0 ≤ Cb) (hK₁ : 0 ≤ K₁)
    (hΦc : ContinuousOn Φ (Icc 0 T)) (hΦ0 : ∀ t ∈ Icc 0 T, 0 ≤ Φ t)
    (htube : ∀ t₁ ∈ Ioc 0 T, (∀ s ∈ Icc 0 t₁, EK k w s ≤ ρ) →
      (∀ α ∈ SlabSobAlg.wordsLE d k, SymHyp A (vsd α w) a 0 t₁ b L Cb) ∧
      ∀ t ∈ Icc 0 t₁,
        ∑ α ∈ SlabSobAlg.wordsLE d k, princSq A (vsd α w) t ≤ K₁ * EK k w t + Φ t)
    (h0 : EK k w 0 ≤ hkBound d N L Cb K₁ (EK k w 0) (∫ s in (0 : ℝ)..T, Φ s) T T)
    (hsmall : hkBound d N L Cb K₁ (EK k w 0) (∫ s in (0 : ℝ)..T, Φ s) T T < ρ) :
    ∀ t ∈ Icc 0 T, EK k w t ≤ hkBound d N L Cb K₁ (EK k w 0) (∫ s in (0 : ℝ)..T, Φ s) T T := by
  refine ODECutoff.firstExit_le hcont hsmall h0 fun t ht hle => ?_
  rcases ht.1.lt_or_eq with htpos | ht0
  · obtain ⟨hS, hF⟩ := htube t ⟨htpos, ht.2⟩ hle
    have hΦc' : ContinuousOn Φ (Icc 0 t) := hΦc.mono (Icc_subset_Icc le_rfl ht.2)
    have hΦ0' : ∀ s ∈ Icc 0 t, 0 ≤ Φ s := fun s hs => hΦ0 s ⟨hs.1, hs.2.trans ht.2⟩
    have := hk_energy_estimate hA0 hS hK₁ hΦc' hΦ0' hF t ⟨htpos.le, le_rfl⟩
    exact this.trans (hkBound_mono hCb hK₁ (EK_nonneg k w 0) htpos.le ht.2 hΦc hΦ0)
  · rw [← ht0]; exact h0

/-! ### Non-vacuity: constant coefficients and a constant state -/

section NonVacuity

/-- `A⁰ = 1`, `A^j = 0`. -/
def unitA (d : ℕ) (N : Type*) [DecidableEq N] : Fin (d + 1) → (Fin (d + 1) → ℝ) → N → N → ℂ :=
  fun μ _ i j => if μ = 0 then (if i = j then 1 else 0) else 0

theorem unitA_unitTime : IsUnitTime (unitA d N) := fun x => by
  funext i j; simp [unitA]

theorem pd_const' (c : N → ℂ) (μ : Fin (d + 1)) :
    pd (fun _ : Fin (d + 1) → ℝ => c) μ = fun _ => 0 := by
  funext x; simp [SobolevOpen.pd]

theorem vsd_const (c : N → ℂ) :
    ∀ α : List (Fin d), α ≠ [] → vsd α (fun _ : Fin (d + 1) → ℝ => c) = fun _ => 0
  | [], h => absurd rfl h
  | i :: l, _ => by
    rw [vsd, pd_const']
    rcases l with _ | ⟨j, l⟩
    · rfl
    · exact vsd_const 0 (j :: l) (List.cons_ne_nil _ _)

theorem vsd_const_eq (c : N → ℂ) (α : List (Fin d)) :
    ∃ c' : N → ℂ, vsd α (fun _ : Fin (d + 1) → ℝ => c) = fun _ => c' := by
  by_cases h : α = []
  · exact ⟨c, by rw [h]; rfl⟩
  · exact ⟨0, vsd_const c α h⟩

theorem norm_unitA_le (μ : Fin (d + 1)) (x : Fin (d + 1) → ℝ) : ‖unitA d N μ x‖ ≤ 1 := by
  refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => ?_
  refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun j => ?_
  unfold unitA
  split_ifs <;> simp

/-- The constant state satisfies the `L²` hypotheses for every word. -/
theorem symHyp_const (c : N → ℂ) (α : List (Fin d)) {T : ℝ} (hT : 0 < T) :
    SymHyp (unitA d N) (vsd α (fun _ : Fin (d + 1) → ℝ => c)) (-1) 0 T (T + 1) 0 1 := by
  obtain ⟨c', hc'⟩ := vsd_const_eq c α
  rw [hc']
  exact
    { ha := by norm_num
      h01 := hT
      hb := by linarith
      smooth := contDiffOn_const
      wper := fun _ _ => rfl
      Aper := fun _ _ _ => rfl
      herm := fun μ x i k => by
        unfold unitA
        split_ifs <;> simp_all [eq_comm]
      lip := fun μ => by
        have : unitA d N μ = fun _ => unitA d N μ 0 := rfl
        rw [this]
        exact (LipschitzWith.const _).lipschitzOnWith
      bound := fun μ x _ => norm_unitA_le μ x }

/-- **Non-vacuity of `hk_energy_estimate`:** a constant state of the constant-coefficient system
`∂_tW = 0` satisfies every hypothesis (with `K₁ = 0`, `Φ = 0`). -/
theorem hk_energy_estimate_const (c : N → ℂ) (k : ℕ) {T : ℝ} (hT : 0 < T) :
    ∀ t ∈ Icc 0 T, EK k (fun _ : Fin (d + 1) → ℝ => c) t ≤
      hkBound d N 0 1 0 (EK k (fun _ : Fin (d + 1) → ℝ => c) 0) (∫ s in (0 : ℝ)..T, (0 : ℝ)) T t := by
  refine hk_energy_estimate (Φ := fun _ => 0) unitA_unitTime
    (fun α _ => symHyp_const c α hT) le_rfl continuousOn_const (fun _ _ => le_rfl)
    fun t _ => ?_
  have hz : ∀ α : List (Fin d), princSq (unitA d N) (vsd α (fun _ => c)) t = 0 := by
    intro α
    obtain ⟨c', hc'⟩ := vsd_const_eq c α
    rw [hc']
    have hmv : ∀ B : N → N → ℂ, mv B 0 = 0 := fun B => by
      funext i; simp [PeriodicCube.mv]
    unfold princSq princ
    simp [pd_const', hmv]
  simp only [hz, Finset.sum_const_zero, zero_mul, add_zero, le_refl]

end NonVacuity

end RenewalGeometry.FOSymHk
