/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.BallInteriorRegularity

/-!
# Higher-order Sobolev spaces `H^k(Ω)` by weak derivatives, and smooth approximation classes

Generic infrastructure (no renewal notions) for `prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript (stage C4b of the ball rendering of Uhlenbeck's
small-energy gauge theorem).  Real-valued functions on `ℝⁿ = Fin n → ℝ`, open sets `Ω`.

* `MemHk Ω k u` — **`u ∈ H^k(Ω)`**, recursively: `u ∈ L²(Ω)` and every weak partial derivative
  `∂_i u` exists and lies in `H^{k-1}(Ω)`.  API: `MemHk.memLp`, `MemHk.mono`, `MemHk.congr_ae`,
  `MemHk.restrict`, `MemHk.add`/`smul`/`sub`/`neg`, `memHk_const`,
  `MemHk.mul_smooth` (**multiplication by smooth functions** on bounded `Ω`, Leibniz rule for
  weak derivatives `HasWeakPartialR.mul_smooth`), `MemHk.mul_test_univ` (cut-off to `ℝⁿ`),
  `MemHk.deriv` (any weak derivative of an `H^{k+1}` function is in `H^k`).
* `ConvHk Ω k φ u` — `u` is the `H^k(Ω)` limit of the smooth functions `φ_m` (all classical
  derivatives up to order `k` converge in `L²(Ω)`); `ConvHk.memHk` (the limit is in `H^k(Ω)`, its
  weak derivatives being the limits of the classical ones), `ConvHk.mono`, `.add`, `.sub`,
  `.mul_smooth`, `ConvHk.pd`.
-/

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

noncomputable section

namespace RenewalGeometry.BallAnalysis.BallReg

open SobolevOpen

set_option linter.unusedSectionVars false

variable {n : ℕ}

/-! ### Weak derivatives: generic calculus -/

section WeakCalc

variable {Ω : Set (Fin n → ℝ)}

theorem integral_test_eq_setIntegral' {φ v : (Fin n → ℝ) → ℝ} (hφ : IsTest Ω φ) :
    ∫ x, φ x * v x = ∫ x in Ω, φ x * v x := by
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_).symm
  rw [isTest_vanish hφ x hx, zero_mul]

theorem HasWeakPartialR.congr_ae' {i : Fin n} {u u' g g' : (Fin n → ℝ) → ℝ}
    (h : HasWeakPartialR Ω i u g) (hu : u =ᵐ[volume.restrict Ω] u')
    (hg : g =ᵐ[volume.restrict Ω] g') : HasWeakPartialR Ω i u' g' := by
  intro φ hφ
  rw [integral_test_eq_setIntegral' (isTest_pd hφ i), integral_test_eq_setIntegral' hφ]
  have h1 := h φ hφ
  rw [integral_test_eq_setIntegral' (isTest_pd hφ i), integral_test_eq_setIntegral' hφ] at h1
  have e1 : ∫ x in Ω, pd φ i x * u x = ∫ x in Ω, pd φ i x * u' x :=
    integral_congr_ae (hu.mono fun x hx => by simp only [hx])
  have e2 : ∫ x in Ω, φ x * g x = ∫ x in Ω, φ x * g' x :=
    integral_congr_ae (hg.mono fun x hx => by simp only [hx])
  rw [← e1, ← e2]
  exact h1

theorem HasWeakPartialR.mono_set {Ω' : Set (Fin n → ℝ)} {i : Fin n} {u g : (Fin n → ℝ) → ℝ}
    (h : HasWeakPartialR Ω i u g) (hΩ : Ω' ⊆ Ω) : HasWeakPartialR Ω' i u g :=
  h.congr_left hΩ fun _ _ => rfl

theorem HasWeakPartialR.add {i : Fin n} {u v g h : (Fin n → ℝ) → ℝ}
    (hu : HasWeakPartialR Ω i u g) (hv : HasWeakPartialR Ω i v h)
    (huL : MemLp u 2 (volume.restrict Ω)) (hvL : MemLp v 2 (volume.restrict Ω))
    (hgL : MemLp g 2 (volume.restrict Ω)) (hhL : MemLp h 2 (volume.restrict Ω)) :
    HasWeakPartialR Ω i (fun x => u x + v x) (fun x => g x + h x) := by
  intro φ hφ
  have i1 := integrable_mul_of_memLp_restrict (isTest_pd hφ i).continuous
    (isTest_pd hφ i).compact (isTest_pd hφ i).subset huL
  have i2 := integrable_mul_of_memLp_restrict (isTest_pd hφ i).continuous
    (isTest_pd hφ i).compact (isTest_pd hφ i).subset hvL
  have i3 := integrable_mul_of_memLp_restrict hφ.continuous hφ.compact hφ.subset hgL
  have i4 := integrable_mul_of_memLp_restrict hφ.continuous hφ.compact hφ.subset hhL
  simp only [mul_add]
  rw [integral_add i1 i2, integral_add i3 i4, hu φ hφ, hv φ hφ]; ring

theorem HasWeakPartialR.const_mul {i : Fin n} {u g : (Fin n → ℝ) → ℝ}
    (hu : HasWeakPartialR Ω i u g) (a : ℝ) :
    HasWeakPartialR Ω i (fun x => a * u x) (fun x => a * g x) := by
  intro φ hφ
  have e1 : (fun x => pd φ i x * (a * u x)) = fun x => a * (pd φ i x * u x) := by
    funext x; ring
  have e2 : (fun x => φ x * (a * g x)) = fun x => a * (φ x * g x) := by funext x; ring
  rw [e1, e2, integral_const_mul, integral_const_mul, hu φ hφ]; ring

theorem hasWeakPartialR_const (i : Fin n) (a : ℝ) :
    HasWeakPartialR Ω i (fun _ => a) (fun _ => 0) := by
  intro φ hφ
  have := hasWeakPartialR_of_contDiff Ω (contDiff_const (c := a)) i φ hφ
  simpa [pd] using this

/-- **Leibniz rule for weak derivatives** with a smooth factor. -/
theorem HasWeakPartialR.mul_smooth {i : Fin n} {u g a : (Fin n → ℝ) → ℝ}
    (hu : HasWeakPartialR Ω i u g) (ha : ContDiff ℝ ∞ a)
    (huL : MemLp u 2 (volume.restrict Ω)) (hgL : MemLp g 2 (volume.restrict Ω)) :
    HasWeakPartialR Ω i (fun x => a x * u x) (fun x => pd a i x * u x + a x * g x) := by
  intro φ hφ
  have ha1 : ContDiff ℝ 1 a := ha.of_le (by simp)
  have hφ1 : ContDiff ℝ 1 φ := hφ.smooth.of_le (by simp)
  have hT : IsTest Ω (fun x => φ x * a x) := hφ.mul_smooth ha
  have hT' : IsTest Ω (fun x => φ x * pd a i x) := hφ.mul_smooth (contDiff_pd ha i)
  have key := hu _ hT
  have hpd : ∀ x, pd (fun x => φ x * a x) i x = pd φ i x * a x + φ x * pd a i x :=
    fun x => pd_mul hφ1 ha1 i x
  simp only [hpd] at key
  have i1 := integrable_mul_of_memLp_restrict (isTest_pd hT i).continuous (isTest_pd hT i).compact
    (isTest_pd hT i).subset huL
  have i2 := integrable_mul_of_memLp_restrict hT'.continuous hT'.compact hT'.subset huL
  have i3 := integrable_mul_of_memLp_restrict hT.continuous hT.compact hT.subset hgL
  have e1 : ∫ x, pd φ i x * (a x * u x) =
      (∫ x, pd (fun x => φ x * a x) i x * u x) - ∫ x, (φ x * pd a i x) * u x := by
    rw [← integral_sub i1 i2]; congr 1; funext x; rw [hpd]; ring
  have e2 : ∫ x, φ x * (pd a i x * u x + a x * g x) =
      (∫ x, (φ x * pd a i x) * u x) + ∫ x, (φ x * a x) * g x := by
    rw [← integral_add i2 i3]; congr 1; funext x; ring
  have key' : ∫ x, pd (fun x => φ x * a x) i x * u x = -∫ x, (φ x * a x) * g x := by
    rw [← key]; congr 1; funext x; rw [hpd]
  rw [e1, e2, key']; ring

end WeakCalc

/-! ### `H^k(Ω)` -/

/-- **`u ∈ H^k(Ω)`**: `u ∈ L²(Ω)` with weak derivatives up to order `k` in `L²(Ω)` (recursive). -/
def MemHk (Ω : Set (Fin n → ℝ)) : ℕ → ((Fin n → ℝ) → ℝ) → Prop
  | 0, u => MemLp u 2 (volume.restrict Ω)
  | m + 1, u => MemLp u 2 (volume.restrict Ω) ∧
      ∀ i, ∃ g, HasWeakPartialR Ω i u g ∧ MemHk Ω m g

section MemHkAPI

variable {Ω : Set (Fin n → ℝ)}

theorem memHk_zero_iff {u : (Fin n → ℝ) → ℝ} : MemHk Ω 0 u ↔ MemLp u 2 (volume.restrict Ω) :=
  Iff.rfl

theorem memHk_succ_iff {m : ℕ} {u : (Fin n → ℝ) → ℝ} :
    MemHk Ω (m + 1) u ↔ MemLp u 2 (volume.restrict Ω) ∧
      ∀ i, ∃ g, HasWeakPartialR Ω i u g ∧ MemHk Ω m g := Iff.rfl

theorem MemHk.memLp {m : ℕ} {u : (Fin n → ℝ) → ℝ} (h : MemHk Ω m u) :
    MemLp u 2 (volume.restrict Ω) := by
  cases m with
  | zero => exact h
  | succ m => exact h.1

theorem MemHk.mono {m m' : ℕ} (hm : m' ≤ m) {u : (Fin n → ℝ) → ℝ} (h : MemHk Ω m u) :
    MemHk Ω m' u := by
  induction m' generalizing m u with
  | zero => exact h.memLp
  | succ m' ih =>
    obtain ⟨m, rfl⟩ : ∃ m'', m = m'' + 1 := ⟨m - 1, by omega⟩
    refine ⟨h.1, fun i => ?_⟩
    obtain ⟨g, hg, hgm⟩ := h.2 i
    exact ⟨g, hg, ih (by omega) hgm⟩

theorem MemHk.congr_ae {m : ℕ} {u u' : (Fin n → ℝ) → ℝ} (h : MemHk Ω m u)
    (hu : u =ᵐ[volume.restrict Ω] u') : MemHk Ω m u' := by
  cases m with
  | zero => exact (memLp_congr_ae hu).mp h
  | succ m =>
    refine ⟨(memLp_congr_ae hu).mp h.1, fun i => ?_⟩
    obtain ⟨g, hg, hgm⟩ := h.2 i
    exact ⟨g, hg.congr_ae' hu (Filter.EventuallyEq.refl _ _), hgm⟩

theorem MemHk.restrict {m : ℕ} {Ω' : Set (Fin n → ℝ)} (hΩ : Ω' ⊆ Ω) {u : (Fin n → ℝ) → ℝ}
    (h : MemHk Ω m u) : MemHk Ω' m u := by
  induction m generalizing u with
  | zero => exact h.mono_measure (Measure.restrict_mono hΩ le_rfl)
  | succ m ih =>
    refine ⟨h.1.mono_measure (Measure.restrict_mono hΩ le_rfl), fun i => ?_⟩
    obtain ⟨g, hg, hgm⟩ := h.2 i
    exact ⟨g, hg.mono_set hΩ, ih hgm⟩

theorem MemHk.add {m : ℕ} {u v : (Fin n → ℝ) → ℝ} (hu : MemHk Ω m u) (hv : MemHk Ω m v) :
    MemHk Ω m (fun x => u x + v x) := by
  induction m generalizing u v with
  | zero => exact MemLp.add (f := u) (g := v) hu hv
  | succ m ih =>
    refine ⟨MemLp.add (f := u) (g := v) hu.1 hv.1, fun i => ?_⟩
    obtain ⟨g, hg, hgm⟩ := hu.2 i
    obtain ⟨h, hh, hhm⟩ := hv.2 i
    exact ⟨_, hg.add hh hu.1 hv.1 hgm.memLp hhm.memLp, ih hgm hhm⟩

theorem MemHk.const_mul {m : ℕ} {u : (Fin n → ℝ) → ℝ} (hu : MemHk Ω m u) (a : ℝ) :
    MemHk Ω m (fun x => a * u x) := by
  induction m generalizing u with
  | zero => exact MemLp.const_mul (f := u) hu a
  | succ m ih =>
    refine ⟨MemLp.const_mul (f := u) hu.1 a, fun i => ?_⟩
    obtain ⟨g, hg, hgm⟩ := hu.2 i
    exact ⟨_, hg.const_mul a, ih hgm⟩

theorem MemHk.neg {m : ℕ} {u : (Fin n → ℝ) → ℝ} (hu : MemHk Ω m u) :
    MemHk Ω m (fun x => -u x) := by
  have := hu.const_mul (-1)
  simpa using this

theorem MemHk.sub {m : ℕ} {u v : (Fin n → ℝ) → ℝ} (hu : MemHk Ω m u) (hv : MemHk Ω m v) :
    MemHk Ω m (fun x => u x - v x) := by
  have := hu.add hv.neg
  simpa [sub_eq_add_neg] using this

theorem memHk_zero_fn (m : ℕ) : MemHk Ω m (fun _ => (0 : ℝ)) := by
  induction m with
  | zero => exact MemLp.zero'
  | succ m ih => exact ⟨MemLp.zero', fun i => ⟨fun _ => 0, hasWeakPartialR_const i 0, ih⟩⟩

/-- Finite sums in `H^k` (any `Ω`). -/
theorem MemHk.sum' {m : ℕ} {ι : Type*} (s : Finset ι) {u : ι → (Fin n → ℝ) → ℝ}
    (hu : ∀ k ∈ s, MemHk Ω m (u k)) : MemHk Ω m (fun x => ∑ k ∈ s, u k x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using memHk_zero_fn (Ω := Ω) m
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hu a (Finset.mem_insert_self a s)).add (ih fun k hk => hu k (Finset.mem_insert_of_mem hk))

theorem memHk_const {m : ℕ} (hΩ : volume Ω ≠ ⊤) (a : ℝ) : MemHk Ω m (fun _ => a) := by
  have : IsFiniteMeasure (volume.restrict Ω) := ⟨by rw [Measure.restrict_apply_univ]; exact hΩ.lt_top⟩
  induction m generalizing a with
  | zero => exact memLp_const a
  | succ m ih => exact ⟨memLp_const a, fun i => ⟨fun _ => 0, hasWeakPartialR_const i a, ih 0⟩⟩

theorem MemHk.sum {m : ℕ} {ι : Type*} (s : Finset ι) {u : ι → (Fin n → ℝ) → ℝ}
    (hu : ∀ k ∈ s, MemHk Ω m (u k)) (hΩ : volume Ω ≠ ⊤) :
    MemHk Ω m (fun x => ∑ k ∈ s, u k x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact memHk_const hΩ 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hu a (Finset.mem_insert_self a s)).add (ih fun k hk => hu k (Finset.mem_insert_of_mem hk))

/-- Uniqueness of real weak derivatives on an open set. -/
theorem weakR_ae_eq (hΩ : IsOpen Ω) {i : Fin n}
    {u g g' : (Fin n → ℝ) → ℝ} (h : HasWeakPartialR Ω i u g) (h' : HasWeakPartialR Ω i u g')
    (hg : MemLp g 2 (volume.restrict Ω)) (hg' : MemLp g' 2 (volume.restrict Ω)) :
    ∀ᵐ x, x ∈ Ω → g x = g' x := by
  have := (hasWeakPartialR_iff.mp h).ae_eq hΩ (hasWeakPartialR_iff.mp h')
    (locallyIntegrableOn_of_memLp hg.ofReal) (locallyIntegrableOn_of_memLp hg'.ofReal)
  filter_upwards [this] with x hx hxΩ
  exact_mod_cast hx hxΩ

/-- Any (square-integrable) weak derivative of an `H^{k+1}` function is in `H^k`. -/
theorem MemHk.deriv {m : ℕ} (hΩ : IsOpen Ω) {u g : (Fin n → ℝ) → ℝ} (hu : MemHk Ω (m + 1) u)
    {i : Fin n} (hg : HasWeakPartialR Ω i u g) (hgL : MemLp g 2 (volume.restrict Ω)) :
    MemHk Ω m g := by
  obtain ⟨g', hg', hg'm⟩ := hu.2 i
  have hae := weakR_ae_eq hΩ hg' hg hg'm.memLp hgL
  refine hg'm.congr_ae ?_
  rw [EventuallyEq, ae_restrict_iff' hΩ.measurableSet]
  exact hae

/-- Bounded continuous functions on a bounded set: a bound for `|a|` on `Ω`. -/
theorem exists_abs_le_on_bounded {a : (Fin n → ℝ) → ℝ} (ha : Continuous a)
    (hΩ : Bornology.IsBounded Ω) : ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ Ω, |a x| ≤ M := by
  obtain ⟨M, hM⟩ := (hΩ.isCompact_closure.image ha).isBounded.exists_norm_le
  refine ⟨max M 0, le_max_right _ _, fun x hx => ?_⟩
  have := hM (a x) ⟨x, subset_closure hx, rfl⟩
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

theorem memLp_mul_bounded {a u : (Fin n → ℝ) → ℝ} (ha : Continuous a) (hΩ : Bornology.IsBounded Ω)
    (hΩm : MeasurableSet Ω) (hu : MemLp u 2 (volume.restrict Ω)) :
    MemLp (fun x => a x * u x) 2 (volume.restrict Ω) := by
  obtain ⟨M, -, hM⟩ := exists_abs_le_on_bounded ha hΩ
  exact hu.of_le_mul (c := M) (ha.aestronglyMeasurable.mul hu.1)
    ((ae_restrict_mem hΩm).mono fun x hx => by
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hM x hx) (norm_nonneg _))

/-- **Multiplication by smooth functions preserves `H^k(Ω)`** (bounded `Ω`). -/
theorem MemHk.mul_smooth {m : ℕ} (hΩ : Bornology.IsBounded Ω) (hΩm : MeasurableSet Ω)
    {a u : (Fin n → ℝ) → ℝ} (ha : ContDiff ℝ ∞ a) (hu : MemHk Ω m u) :
    MemHk Ω m (fun x => a x * u x) := by
  induction m generalizing a u with
  | zero => exact memLp_mul_bounded ha.continuous hΩ hΩm hu
  | succ m ih =>
    refine ⟨memLp_mul_bounded ha.continuous hΩ hΩm hu.1, fun i => ?_⟩
    obtain ⟨g, hg, hgm⟩ := hu.2 i
    exact ⟨_, hg.mul_smooth ha hu.1 hgm.memLp,
      (ih (contDiff_pd ha i) (hu.mono (Nat.le_succ m))).add (ih ha hgm)⟩

/-- **Cut-off to the whole space**: `χ u ∈ H^k(ℝⁿ)` for `u ∈ H^k(Ω)` and `χ ∈ C_c^∞(Ω)`. -/
theorem MemHk.mul_test_univ {m : ℕ} (hΩ : IsOpen Ω) {χ u : (Fin n → ℝ) → ℝ}
    (hχ : IsTest Ω χ) (hu : MemHk Ω m u) : MemHk univ m (fun x => χ x * u x) := by
  induction m generalizing χ u with
  | zero =>
    obtain ⟨M, -, hM⟩ := exists_abs_bound_of_test hχ
    rw [memHk_zero_iff, Measure.restrict_univ]
    exact memLp_mul_of_vanish_R hΩ.measurableSet hχ.continuous (isTest_vanish hχ) hM hu
  | succ m ih =>
    obtain ⟨M, -, hM⟩ := exists_abs_bound_of_test hχ
    have hL : MemLp (fun x => χ x * u x) 2 (volume.restrict univ) := by
      rw [Measure.restrict_univ]
      exact memLp_mul_of_vanish_R hΩ.measurableSet hχ.continuous (isTest_vanish hχ) hM hu.1
    refine ⟨hL, fun i => ?_⟩
    obtain ⟨g, hg, hgm⟩ := hu.2 i
    refine ⟨_, hg.mul_test hu.1 hgm.memLp hχ, ?_⟩
    have h1 := ih hχ hgm
    have h2 := ih (isTest_pd hχ i) (hu.mono (Nat.le_succ m))
    exact h1.add h2

end MemHkAPI

/-! ### Smooth approximation classes -/

/-- `ConvHk Ω k φ u`: the smooth functions `φ_m` converge to `u` in `H^k(Ω)` (every classical
derivative of order `≤ k` converges in `L²(Ω)`, to a square-integrable limit). -/
def ConvHk (Ω : Set (Fin n → ℝ)) : ℕ → (ℕ → (Fin n → ℝ) → ℝ) → ((Fin n → ℝ) → ℝ) → Prop
  | 0, φ, u => MemLp u 2 (volume.restrict Ω) ∧
      Tendsto (fun m => eLpNorm (φ m - u) 2 (volume.restrict Ω)) atTop (𝓝 0)
  | k + 1, φ, u => (MemLp u 2 (volume.restrict Ω) ∧
      Tendsto (fun m => eLpNorm (φ m - u) 2 (volume.restrict Ω)) atTop (𝓝 0)) ∧
      ∀ i, ∃ g, ConvHk Ω k (fun m => pd (φ m) i) g

section ConvHkAPI

variable {Ω : Set (Fin n → ℝ)}

theorem ConvHk.base {k : ℕ} {φ : ℕ → (Fin n → ℝ) → ℝ} {u : (Fin n → ℝ) → ℝ}
    (h : ConvHk Ω k φ u) : MemLp u 2 (volume.restrict Ω) ∧
      Tendsto (fun m => eLpNorm (φ m - u) 2 (volume.restrict Ω)) atTop (𝓝 0) := by
  cases k with
  | zero => exact h
  | succ k => exact h.1

theorem ConvHk.mono {k k' : ℕ} (hk : k' ≤ k) {φ : ℕ → (Fin n → ℝ) → ℝ} {u : (Fin n → ℝ) → ℝ}
    (h : ConvHk Ω k φ u) : ConvHk Ω k' φ u := by
  induction k' generalizing k φ u with
  | zero => exact h.base
  | succ k' ih =>
    obtain ⟨k, rfl⟩ : ∃ k'', k = k'' + 1 := ⟨k - 1, by omega⟩
    refine ⟨h.1, fun i => ?_⟩
    obtain ⟨g, hg⟩ := h.2 i
    exact ⟨g, ih (by omega) hg⟩

/-- Weak derivatives are limits of classical ones (bounded `Ω`). -/
theorem hasWeakPartialR_of_conv (hΩ : Bornology.IsBounded Ω) (hΩm : MeasurableSet Ω)
    {φ : ℕ → (Fin n → ℝ) → ℝ} (hφ : ∀ m, ContDiff ℝ ∞ (φ m)) {u g : (Fin n → ℝ) → ℝ} {i : Fin n}
    (hu : MemLp u 2 (volume.restrict Ω)) (hg : MemLp g 2 (volume.restrict Ω))
    (hcu : Tendsto (fun m => eLpNorm (φ m - u) 2 (volume.restrict Ω)) atTop (𝓝 0))
    (hcg : Tendsto (fun m => eLpNorm (pd (φ m) i - g) 2 (volume.restrict Ω)) atTop (𝓝 0)) :
    HasWeakPartialR Ω i u g := by
  intro ψ hψ
  have hψ1 : ContDiff ℝ 1 ψ := hψ.smooth.of_le (by simp)
  have hcl : ∀ m, ∫ x, pd ψ i x * φ m x = -∫ x, ψ x * pd (φ m) i x := fun m =>
    hasWeakPartialR_of_contDiff Ω ((hφ m).of_le (by simp)) i ψ hψ
  have hpψ : IsTest Ω (pd ψ i) := isTest_pd hψ i
  have hfin : IsFiniteMeasure (volume.restrict Ω) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hΩ.measure_lt_top⟩
  have hb : ∀ (χ : (Fin n → ℝ) → ℝ), IsTest Ω χ → MemLp χ 2 (volume.restrict Ω) := fun χ hχ =>
    (hχ.continuous.memLp_of_hasCompactSupport hχ.compact).restrict Ω
  have hφL : ∀ m, MemLp (φ m) 2 (volume.restrict Ω) := fun m => by
    simpa using memLp_mul_bounded (u := fun _ => (1 : ℝ)) (hφ m).continuous hΩ hΩm (memLp_const 1)
  have hpφL : ∀ m, MemLp (pd (φ m) i) 2 (volume.restrict Ω) := fun m => by
    simpa using memLp_mul_bounded (u := fun _ => (1 : ℝ)) (continuous_pd ((hφ m).of_le (by simp)) i)
      hΩ hΩm (memLp_const 1)
  have h1 : Tendsto (fun m => ∫ x, pd ψ i x * φ m x) atTop (𝓝 (∫ x, pd ψ i x * u x)) := by
    simp only [integral_test_eq_setIntegral' hpψ]
    refine tendsto_integral_of_le_mul_L2 (μ := volume.restrict Ω) (fun m => ?_)
      ((hb _ hpψ).aestronglyMeasurable.mul hu.aestronglyMeasurable) (hb _ hpψ)
      (fun m => ((hφL m).sub hu).aestronglyMeasurable) hcu
      (fun m => Eventually.of_forall fun x => ?_)
    · exact (integrable_mul_of_memLp_restrict hpψ.continuous hpψ.compact hpψ.subset
        (hφL m)).integrableOn
    · rw [← mul_sub, norm_mul, Pi.sub_apply]
  have h2 : Tendsto (fun m => ∫ x, ψ x * pd (φ m) i x) atTop (𝓝 (∫ x, ψ x * g x)) := by
    simp only [integral_test_eq_setIntegral' hψ]
    refine tendsto_integral_of_le_mul_L2 (μ := volume.restrict Ω) (fun m => ?_)
      ((hb _ hψ).aestronglyMeasurable.mul hg.aestronglyMeasurable) (hb _ hψ)
      (fun m => ((hpφL m).sub hg).aestronglyMeasurable) hcg
      (fun m => Eventually.of_forall fun x => ?_)
    · exact (integrable_mul_of_memLp_restrict hψ.continuous hψ.compact hψ.subset
        (hpφL m)).integrableOn
    · rw [← mul_sub, norm_mul, Pi.sub_apply]
  exact tendsto_nhds_unique (h1.congr hcl) h2.neg

/-- **`H^k` limits of smooth functions are in `H^k`** (bounded open `Ω`). -/
theorem ConvHk.memHk {k : ℕ} (hΩ : Bornology.IsBounded Ω) (hΩm : MeasurableSet Ω)
    {φ : ℕ → (Fin n → ℝ) → ℝ} (hφ : ∀ m, ContDiff ℝ ∞ (φ m)) {u : (Fin n → ℝ) → ℝ}
    (h : ConvHk Ω k φ u) : MemHk Ω k u := by
  induction k generalizing φ u with
  | zero => exact h.1
  | succ k ih =>
    refine ⟨h.1.1, fun i => ?_⟩
    obtain ⟨g, hg⟩ := h.2 i
    refine ⟨g, hasWeakPartialR_of_conv hΩ hΩm hφ h.1.1 hg.base.1 h.1.2 hg.base.2, ?_⟩
    exact ih (fun m => contDiff_pd (hφ m) i) hg

theorem tendsto_eLpNorm_add {μ : Measure (Fin n → ℝ)} {φ ψ : ℕ → (Fin n → ℝ) → ℝ}
    {u v : (Fin n → ℝ) → ℝ} (hφ : ∀ m, AEStronglyMeasurable (φ m) μ)
    (hψ : ∀ m, AEStronglyMeasurable (ψ m) μ) (hu : AEStronglyMeasurable u μ)
    (hv : AEStronglyMeasurable v μ)
    (h1 : Tendsto (fun m => eLpNorm (φ m - u) 2 μ) atTop (𝓝 0))
    (h2 : Tendsto (fun m => eLpNorm (ψ m - v) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun m => eLpNorm ((fun x => φ m x + ψ m x) - fun x => u x + v x) 2 μ) atTop
      (𝓝 0) := by
  have h3 := h1.add h2
  rw [add_zero] at h3
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h3 (fun m => zero_le)
    fun m => ?_
  have e : ((fun x => φ m x + ψ m x) - fun x => u x + v x) = (φ m - u) + (ψ m - v) := by
    funext x; simp only [Pi.sub_apply, Pi.add_apply]; ring
  rw [e]
  exact eLpNorm_add_le ((hφ m).sub hu) ((hψ m).sub hv) (by norm_num)

theorem ConvHk.add {k : ℕ} {φ ψ : ℕ → (Fin n → ℝ) → ℝ} (hφ : ∀ m, ContDiff ℝ ∞ (φ m))
    (hψ : ∀ m, ContDiff ℝ ∞ (ψ m)) {u v : (Fin n → ℝ) → ℝ}
    (hu : ConvHk Ω k φ u) (hv : ConvHk Ω k ψ v) :
    ConvHk Ω k (fun m x => φ m x + ψ m x) (fun x => u x + v x) := by
  induction k generalizing φ ψ u v with
  | zero =>
    exact ⟨MemLp.add (f := u) (g := v) hu.1 hv.1, tendsto_eLpNorm_add
      (fun m => (hφ m).continuous.aestronglyMeasurable)
      (fun m => (hψ m).continuous.aestronglyMeasurable) hu.1.1 hv.1.1 hu.2 hv.2⟩
  | succ k ih =>
    refine ⟨⟨MemLp.add (f := u) (g := v) hu.1.1 hv.1.1, tendsto_eLpNorm_add
      (fun m => (hφ m).continuous.aestronglyMeasurable)
      (fun m => (hψ m).continuous.aestronglyMeasurable) hu.1.1.1 hv.1.1.1 hu.1.2 hv.1.2⟩,
      fun i => ?_⟩
    obtain ⟨g, hg⟩ := hu.2 i
    obtain ⟨h, hh⟩ := hv.2 i
    refine ⟨fun x => g x + h x, ?_⟩
    have e : (fun m => pd (fun x => φ m x + ψ m x) i) =
        fun m x => pd (φ m) i x + pd (ψ m) i x := by
      funext m x
      exact pd_add_real ((hφ m).differentiable (by simp) x) ((hψ m).differentiable (by simp) x) i
    rw [e]
    exact ih (fun m => contDiff_pd (hφ m) i) (fun m => contDiff_pd (hψ m) i) hg hh

/-- Convergence is preserved by multiplication by a constant. -/
theorem convBase_const_mul {φ : ℕ → (Fin n → ℝ) → ℝ} {u : (Fin n → ℝ) → ℝ} (a : ℝ)
    (h : MemLp u 2 (volume.restrict Ω) ∧
      Tendsto (fun m => eLpNorm (φ m - u) 2 (volume.restrict Ω)) atTop (𝓝 0)) :
    MemLp (fun x => a * u x) 2 (volume.restrict Ω) ∧
      Tendsto (fun m => eLpNorm ((fun x => a * φ m x) - fun x => a * u x) 2
        (volume.restrict Ω)) atTop (𝓝 0) := by
  refine ⟨MemLp.const_mul (f := u) h.1 a, ?_⟩
  have e : ∀ m, ((fun x => a * φ m x) - fun x => a * u x) = a • (φ m - u) := by
    intro m; funext x; simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
  simp only [e]
  have h2 := ENNReal.Tendsto.const_mul h.2 (a := (‖a‖₊ : ℝ≥0∞)) (Or.inr ENNReal.coe_ne_top)
  rw [mul_zero] at h2
  refine h2.congr fun m => ?_
  rw [eLpNorm_const_smul]; rfl

theorem ConvHk.const_mul {k : ℕ} {φ : ℕ → (Fin n → ℝ) → ℝ} (hφ : ∀ m, ContDiff ℝ ∞ (φ m))
    {u : (Fin n → ℝ) → ℝ} (hu : ConvHk Ω k φ u) (a : ℝ) :
    ConvHk Ω k (fun m x => a * φ m x) (fun x => a * u x) := by
  induction k generalizing φ u with
  | zero => exact convBase_const_mul a hu
  | succ k ih =>
    refine ⟨convBase_const_mul a hu.1, fun i => ?_⟩
    obtain ⟨g, hg⟩ := hu.2 i
    refine ⟨fun x => a * g x, ?_⟩
    have e : (fun m => pd (fun x => a * φ m x) i) = fun m x => a * pd (φ m) i x := by
      funext m x
      exact pd_mul contDiff_const ((hφ m).of_le (by simp)) i x |>.trans (by simp [pd])
    rw [e]
    exact ih (fun m => contDiff_pd (hφ m) i) hg

theorem ConvHk.sub {k : ℕ} {φ ψ : ℕ → (Fin n → ℝ) → ℝ} (hφ : ∀ m, ContDiff ℝ ∞ (φ m))
    (hψ : ∀ m, ContDiff ℝ ∞ (ψ m)) {u v : (Fin n → ℝ) → ℝ}
    (hu : ConvHk Ω k φ u) (hv : ConvHk Ω k ψ v) :
    ConvHk Ω k (fun m x => φ m x - ψ m x) (fun x => u x - v x) := by
  have := hu.add hφ (fun m => contDiff_const.mul (hψ m)) (hv.const_mul hψ (-1))
  simpa [sub_eq_add_neg] using this

/-- Convergence is preserved by multiplication by a smooth function (bounded `Ω`). -/
theorem convBase_mul_smooth (hΩ : Bornology.IsBounded Ω) (hΩm : MeasurableSet Ω)
    {a : (Fin n → ℝ) → ℝ} (ha : ContDiff ℝ ∞ a) {φ : ℕ → (Fin n → ℝ) → ℝ}
    {u : (Fin n → ℝ) → ℝ} (h : MemLp u 2 (volume.restrict Ω) ∧
      Tendsto (fun m => eLpNorm (φ m - u) 2 (volume.restrict Ω)) atTop (𝓝 0)) :
    MemLp (fun x => a x * u x) 2 (volume.restrict Ω) ∧
      Tendsto (fun m => eLpNorm ((fun x => a x * φ m x) - fun x => a x * u x) 2
        (volume.restrict Ω)) atTop (𝓝 0) := by
  refine ⟨memLp_mul_bounded ha.continuous hΩ hΩm h.1, ?_⟩
  obtain ⟨M, hM0, hM⟩ := exists_abs_le_on_bounded ha.continuous hΩ
  have h2 := ENNReal.Tendsto.const_mul h.2 (a := ENNReal.ofReal M) (Or.inr ENNReal.ofReal_ne_top)
  rw [mul_zero] at h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2 (fun m => zero_le)
    fun m => ?_
  refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul ?_ 2
  filter_upwards [ae_restrict_mem hΩm] with x hx
  simp only [Pi.sub_apply, ← mul_sub, norm_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hM x hx) (abs_nonneg _)

/-- **Multiplication by smooth functions preserves `H^k` convergence** (bounded `Ω`). -/
theorem ConvHk.mul_smooth {k : ℕ} (hΩ : Bornology.IsBounded Ω) (hΩm : MeasurableSet Ω)
    {a : (Fin n → ℝ) → ℝ} (ha : ContDiff ℝ ∞ a) {φ : ℕ → (Fin n → ℝ) → ℝ}
    (hφ : ∀ m, ContDiff ℝ ∞ (φ m)) {u : (Fin n → ℝ) → ℝ} (hu : ConvHk Ω k φ u) :
    ConvHk Ω k (fun m x => a x * φ m x) (fun x => a x * u x) := by
  induction k generalizing a φ u with
  | zero => exact convBase_mul_smooth hΩ hΩm ha hu
  | succ k ih =>
    refine ⟨convBase_mul_smooth hΩ hΩm ha hu.1, fun i => ?_⟩
    obtain ⟨g, hg⟩ := hu.2 i
    have hu' : ConvHk Ω k φ u := hu.mono (Nat.le_succ k)
    refine ⟨fun x => pd a i x * u x + a x * g x, ?_⟩
    have e : (fun m => pd (fun x => a x * φ m x) i) =
        fun m x => pd a i x * φ m x + a x * pd (φ m) i x := by
      funext m x
      exact pd_mul (ha.of_le (by simp)) ((hφ m).of_le (by simp)) i x
    rw [e]
    exact (ih (contDiff_pd ha i) hφ hu').add (fun m => (contDiff_pd ha i).mul (hφ m))
      (fun m => ha.mul (contDiff_pd (hφ m) i)) (ih ha (fun m => contDiff_pd (hφ m) i) hg)

end ConvHkAPI

/-! ### Higher-order whole-space and interior regularity -/

section HigherReg

/-- **The weak Laplacian of a cut-off solution**: if `Δu = f` weakly on `Ω` (weak gradient `g`)
and `χ ∈ C_c^∞(Ω)`, then `Δ(χu) = χ f + 2 ∇χ·g + Σ_k ∂_k∂_kχ u` weakly on `ℝⁿ`, with weak gradient
`χ g_k + ∂_kχ u`. -/
theorem weak_laplacian_cutoff {Ω : Set (Fin n → ℝ)} {u f : (Fin n → ℝ) → ℝ}
    {g : Fin n → (Fin n → ℝ) → ℝ} (hu : MemLp u 2 (volume.restrict Ω))
    (hg : ∀ k, MemLp (g k) 2 (volume.restrict Ω)) (hf : MemLp f 2 (volume.restrict Ω))
    (hweak : ∀ k, HasWeakPartialR Ω k u (g k))
    (heq : ∀ φ, IsTest Ω φ → ∑ k, ∫ x, pd φ k x * g k x = -∫ x, φ x * f x)
    {χ : (Fin n → ℝ) → ℝ} (hχ : IsTest Ω χ) :
    ∀ φ, IsTest univ φ → ∑ k, ∫ x, pd φ k x * (χ x * g k x + pd χ k x * u x) =
      -∫ x, φ x * (χ x * f x + 2 * ∑ k, pd χ k x * g k x + ∑ k, pd (pd χ k) k x * u x) := by
  have hχ1 : ContDiff ℝ 1 χ := hχ.smooth.of_le (by simp)
  have hpdT : ∀ k, IsTest Ω (pd χ k) := fun k => isTest_pd hχ k
  have hpdpdT : ∀ k, IsTest Ω (pd (pd χ k) k) := fun k => isTest_pd (isTest_pd hχ k) k
  intro φ hφ
  have hφ1 : ContDiff ℝ 1 φ := hφ.smooth.of_le (by simp)
  have hT1 : IsTest Ω (fun x => χ x * φ x) := hχ.mul_smooth hφ.smooth
  have hT2 : ∀ k, IsTest Ω (fun x => pd χ k x * φ x) := fun k => (hpdT k).mul_smooth hφ.smooth
  have hT3 : ∀ k, IsTest Ω (fun x => pd (pd χ k) k x * φ x) := fun k =>
    (hpdpdT k).mul_smooth hφ.smooth
  have iT := fun (ψ : (Fin n → ℝ) → ℝ) (hψ : IsTest Ω ψ) (v : (Fin n → ℝ) → ℝ)
    (hv : MemLp v 2 (volume.restrict Ω)) =>
    integrable_mul_of_memLp_restrict hψ.continuous hψ.compact hψ.subset hv
  have hk : ∀ k, ∫ x, pd φ k x * (χ x * g k x + pd χ k x * u x) =
      (∫ x, pd (fun y => χ y * φ y) k x * g k x) -
        2 * (∫ x, (pd χ k x * φ x) * g k x) - ∫ x, (pd (pd χ k) k x * φ x) * u x := by
    intro k
    have hpt : ∀ x, pd φ k x * (χ x * g k x + pd χ k x * u x) =
        pd (fun y => χ y * φ y) k x * g k x - (pd χ k x * φ x) * g k x +
          (pd (fun y => pd χ k y * φ y) k x * u x - (pd (pd χ k) k x * φ x) * u x) := by
      intro x
      rw [pd_mul hχ1 hφ1, pd_mul ((hpdT k).smooth.of_le (by simp)) hφ1]
      ring
    simp only [hpt]
    rw [integral_sub_add_sub (iT _ (isTest_pd hT1 k) _ (hg k)) (iT _ (hT2 k) _ (hg k))
      (iT _ (isTest_pd (hT2 k) k) _ hu) (iT _ (hT3 k) _ hu), hweak k _ (hT2 k)]
    ring
  simp only [hk]
  simp only [Finset.sum_sub_distrib]
  rw [heq _ hT1]
  have hpt2 : ∀ x, φ x * (χ x * f x + 2 * ∑ k, pd χ k x * g k x + ∑ k, pd (pd χ k) k x * u x) =
      (χ x * φ x) * f x + 2 * ∑ k, (pd χ k x * φ x) * g k x +
        ∑ k, (pd (pd χ k) k x * φ x) * u x := by
    intro x
    have s1 : ∑ k, (pd χ k x * φ x) * g k x = φ x * ∑ k, pd χ k x * g k x := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    have s2 : ∑ k, (pd (pd χ k) k x * φ x) * u x = φ x * ∑ k, pd (pd χ k) k x * u x := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    rw [s1, s2]
    ring
  simp only [hpt2]
  rw [integral_add_two_mul_add (iT _ hT1 _ hf) (fun k => iT _ (hT2 k) _ (hg k))
    (fun k => iT _ (hT3 k) _ hu)]
  rw [← Finset.mul_sum]
  ring

/-- **Symmetry of weak second derivatives**: `∂_l∂_i u = ∂_i∂_l u` a.e. -/
theorem weakR_symm {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) {u gi gl H1 H2 : (Fin n → ℝ) → ℝ}
    {i l : Fin n} (hi : HasWeakPartialR Ω i u gi) (hl : HasWeakPartialR Ω l u gl)
    (h1 : HasWeakPartialR Ω l gi H1) (h2 : HasWeakPartialR Ω i gl H2)
    (hH1 : MemLp H1 2 (volume.restrict Ω)) (hH2 : MemLp H2 2 (volume.restrict Ω)) :
    ∀ᵐ x, x ∈ Ω → H1 x = H2 x := by
  have h2' : HasWeakPartialR Ω l gi H2 := by
    intro φ hφ
    have e1 := hi (pd φ l) (isTest_pd hφ l)
    have e2 := hl (pd φ i) (isTest_pd hφ i)
    have e3 := h2 φ hφ
    have hs : pd (pd φ l) i = pd (pd φ i) l := funext fun x =>
      pd_pd_symm (hφ.smooth.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))) i l x
    rw [hs] at e1
    linarith
  exact weakR_ae_eq hΩ h1 h2' hH1 hH2

/-- Weak derivatives of a compactly supported function vanish a.e. off its support. -/
theorem weakR_ae_zero_off {w g : (Fin n → ℝ) → ℝ} {i : Fin n}
    (hw : HasWeakPartialR univ i w g) (hgL : MemLp g 2 volume) :
    ∀ᵐ x, x ∉ tsupport w → g x = 0 := by
  have hO : IsOpen (tsupport w)ᶜ := (isClosed_tsupport w).isOpen_compl
  have h1 : HasWeakPartialR (tsupport w)ᶜ i w g := hw.mono_set (subset_univ _)
  have h0 : HasWeakPartialR (tsupport w)ᶜ i w (fun _ => 0) := by
    have := (hasWeakPartialR_const (Ω := (tsupport w)ᶜ) i (0 : ℝ))
    refine this.congr_left subset_rfl fun x hx => ?_
    exact (image_eq_zero_of_notMem_tsupport hx).symm
  have h00 : MemLp (fun _ : Fin n → ℝ => (0 : ℝ)) 2 (volume.restrict (tsupport w)ᶜ) :=
    MemLp.zero'
  have := weakR_ae_eq hO h1 h0 (hgL.restrict _) h00
  filter_upwards [this] with x hx hxs
  exact hx hxs

/-- **Whole-space higher regularity**: a compactly supported `w ∈ H^{m+1}(ℝⁿ)` with weak gradient
`g` and weak Laplacian `F ∈ H^m(ℝⁿ)` lies in `H^{m+2}(ℝⁿ)`. -/
theorem whole_space_Hk (m : ℕ) : ∀ {w F : (Fin n → ℝ) → ℝ} {g : Fin n → (Fin n → ℝ) → ℝ},
    HasCompactSupport w → MemHk univ (m + 1) w → (∀ k, HasWeakPartialR univ k w (g k)) →
    (∀ k, MemHk univ m (g k)) → MemHk univ m F →
    (∀ φ, IsTest univ φ → ∑ k, ∫ x, pd φ k x * g k x = -∫ x, φ x * F x) →
    MemHk univ (m + 2) w := by
  induction m with
  | zero =>
    intro w F g hwc hw hwk hg hF hΔ
    have hwL : MemLp w 2 volume := by simpa using hw.memLp
    have hgL : ∀ k, MemLp (g k) 2 volume := fun k => by simpa using (hg k).memLp
    have hFL : MemLp F 2 volume := by simpa using hF.memLp
    obtain ⟨G, hGL, hGw, -⟩ := whole_space_H2 hwc hwL hgL hFL hwk hΔ
    refine ⟨hw.memLp, fun k => ⟨g k, hwk k, (hg k).memLp, fun l => ⟨G k l, hGw k l, ?_⟩⟩⟩
    show MemLp (G k l) 2 (volume.restrict univ)
    rw [Measure.restrict_univ]; exact hGL k l
  | succ m ih =>
    intro w F g hwc hw hwk hg hF hΔ
    refine ⟨hw.memLp, fun i => ?_⟩
    -- the compactly supported representative of `∂_i w`
    have hgL : MemLp (g i) 2 volume := by simpa using (hg i).memLp
    set gi : (Fin n → ℝ) → ℝ := (tsupport w).indicator (g i)
    have hae : g i =ᵐ[volume] gi := by
      filter_upwards [weakR_ae_zero_off (hwk i) hgL] with x hx
      by_cases hxs : x ∈ tsupport w
      · simp [gi, hxs]
      · simp [gi, hxs, hx hxs]
    have hae' : g i =ᵐ[volume.restrict univ] gi := by rw [Measure.restrict_univ]; exact hae
    have hgic : HasCompactSupport gi := by
      refine HasCompactSupport.intro hwc fun x hx => ?_
      simp [gi, hx]
    have hgiw : HasWeakPartialR univ i w gi := (hwk i).congr_ae' (Filter.EventuallyEq.refl _ _) hae'
    have hgim : MemHk univ (m + 1) gi := (hg i).congr_ae hae'
    -- gradient of `∂_i w` and the derivative of `F`
    have hgradi : ∀ l, ∃ h, HasWeakPartialR univ l (g i) h ∧ MemHk univ m h := (hg i).2
    choose h hh hhm using hgradi
    obtain ⟨Fi, hFi, hFim⟩ := hF.2 i
    -- the weak Laplacian of `∂_i w`
    have hΔi : ∀ φ, IsTest univ φ → ∑ l, ∫ x, pd φ l x * h l x = -∫ x, φ x * Fi x := by
      intro φ hφ
      have hsym : ∀ l, ∫ x, pd φ l x * h l x = -∫ x, pd (pd φ i) l x * g l x := by
        intro l
        obtain ⟨h', hh', hh'm⟩ := (hg l).2 i
        have hs := weakR_symm isOpen_univ (hwk i) (hwk l) (hh l) hh' (hhm l).memLp hh'm.memLp
        have hs' : h l =ᵐ[volume] h' := by
          filter_upwards [hs] with x hx using hx (mem_univ x)
        have e1 : ∫ x, pd φ l x * h l x = ∫ x, pd φ l x * h' x :=
          integral_congr_ae (hs'.mono fun x hx => by simp only [hx])
        have e2 := hh' (pd φ l) (isTest_pd hφ l)
        have e3 : pd (pd φ l) i = pd (pd φ i) l := funext fun x =>
          pd_pd_symm (hφ.smooth.of_le (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))) i l x
        rw [e3] at e2
        rw [e1]; linarith
      simp only [hsym, Finset.sum_neg_distrib]
      rw [hΔ _ (isTest_pd hφ i), neg_neg]
      exact hFi φ hφ
    have hh' : ∀ l, HasWeakPartialR univ l gi (h l) := fun l =>
      (hh l).congr_ae' hae' (Filter.EventuallyEq.refl _ _)
    exact ⟨gi, hgiw, ih hgic hgim hh' hhm hFim hΔi⟩

end HigherReg

end RenewalGeometry.BallAnalysis.BallReg
