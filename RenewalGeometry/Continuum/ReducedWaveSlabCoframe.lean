/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.ReducedWaveSlabLimit

/-!
# `thm:hyperbolic`, coframe clause: compatible coframes converge in the geometric topology

(Einstein–Standard-Model action-closure manuscript, "Common-slab metric stability": "compatible
coframes chosen on one compact frame chart converge in the geometric topology of
`eq:strong-geometry`".)

A locally fixed coframe depends smoothly on the metric: `e_h(x) = Φ(g_h(x))` for a `C¹` map `Φ`
from metric components to `4 × 4` matrices, the metrics taking values in a compact set `K` of the
chart on the slab, with compatibility `Φ(G)ᵀ η Φ(G) = G` on `K` (so `e_h` is an orthonormal coframe
of `g_h`).  (A `C¹` map on an open neighbourhood of `K` agrees on `K` with a global `C¹` map after a
smooth cut-off; the global form is used.)

* `uniformCauchy_g`, `uniformCauchy_dg` — under the hypotheses of `thm:hyperbolic`, the metrics
  and all their first partial derivatives are uniformly Cauchy on `[0, T] × ℝ³`;
* **`coframe_convergence`** — `e_h` and all first partial derivatives `∂_μe_h` are uniformly Cauchy
  on the slab (hence converge uniformly; in particular in `L^∞(K) ∩ W^{1,∞}(K) ⊂ L^∞(K) ∩ H¹(K)`
  on every compact `K` of the slab), and `sup_h(‖e_h‖_∞ + ‖e_h⁻¹‖_∞) < ∞`
  (`e_h⁻¹ = g_h⁻¹ e_hᵀ η`, bounded by the inverse-metric bound).
-/

open MeasureTheory Filter Topology Set
open scoped BigOperators ContDiff

noncomputable section

namespace RenewalGeometry.ReducedWaveStab

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk SlabSobAlg

set_option linter.unusedSectionVars false

variable {κ : Type} [Fintype κ]

/-- The Minkowski matrix `η = diag(-1, 1, 1, 1)`. -/
def etaM (μ ν : Fin 4) : ℝ := if μ = ν then (if μ = 0 then -1 else 1) else 0

theorem abs_etaM_le (μ ν : Fin 4) : |etaM μ ν| ≤ 1 := by
  unfold etaM; split_ifs <;> simp

/-- The metric components at a point, as a vector. -/
def gvec (g : Idx → X → ℝ) (x : X) : Idx → ℝ := fun c => g c x

/-- The first partial derivatives of the components along `μ`, as a vector. -/
def dgvec (g : Idx → X → ℝ) (μ : Fin 4) (x : X) : Idx → ℝ := fun c => pd (g c) μ x

/-- Uniform Cauchy property from the `L^∞_tH^m` Cauchy property (`m ≥ 2`). -/
theorem uniformCauchy_of_Q {T CS : ℝ} (hCS : 0 ≤ CS)
    (hsup : ∀ f : X → ℝ, ContDiff ℝ ∞ f → IsSPeriodic f → ∀ (t : ℝ) (y : Fin 3 → ℝ),
      f (Fin.cons t y) ^ 2 ≤ CS * Q 2 f t) {m : ℕ} (hm : 2 ≤ m) {F : ℕ → X → ℝ}
    (sF : ∀ i, ContDiff ℝ ∞ (F i)) (pF : ∀ i, IsSPeriodic (F i))
    (hc : ∀ ε > 0, ∃ N, ∀ i j, N ≤ i → N ≤ j → ∀ t ∈ Icc 0 T,
      Q m (fun x => F i x - F j x) t ≤ ε) :
    ∀ ε > 0, ∃ N, ∀ i j, N ≤ i → N ≤ j → ∀ x : X, x 0 ∈ Icc 0 T → |F i x - F j x| ≤ ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := hc (ε ^ 2 / (CS + 1)) (by positivity)
  refine ⟨N, fun i j hi hj x hx => ?_⟩
  have h1 := hsup _ ((sF i).sub (sF j)) (fun k y => by
    show F i _ - F j _ = _; rw [pF i k y, pF j k y]) (x 0) (Fin.tail x)
  rw [Fin.cons_self_tail] at h1
  have h2 := (Q_mono hm _ (x 0)).trans (hN i j hi hj (x 0) hx)
  have h3 : (F i x - F j x) ^ 2 ≤ ε ^ 2 := by
    calc (F i x - F j x) ^ 2 ≤ CS * (ε ^ 2 / (CS + 1)) := h1.trans
          (mul_le_mul_of_nonneg_left h2 hCS)
      _ ≤ ε ^ 2 := by
          rw [mul_div_assoc', div_le_iff₀ (by positivity)]
          nlinarith [sq_nonneg ε]
  exact abs_le.2 (abs_le_of_sq_le_sq' h3 hε.le)

/-- A uniform pointwise bound from the `L^∞_tH^m` bound (`m ≥ 2`). -/
theorem abs_le_of_Q_bound {T CS K : ℝ} (hCS : 0 ≤ CS)
    (hsup : ∀ f : X → ℝ, ContDiff ℝ ∞ f → IsSPeriodic f → ∀ (t : ℝ) (y : Fin 3 → ℝ),
      f (Fin.cons t y) ^ 2 ≤ CS * Q 2 f t) {m : ℕ} (hm : 2 ≤ m) {f : X → ℝ}
    (sf : ContDiff ℝ ∞ f) (pf : IsSPeriodic f) (hK : ∀ t ∈ Icc 0 T, Q m f t ≤ K) {x : X}
    (hx : x 0 ∈ Icc 0 T) : |f x| ≤ Real.sqrt (CS * K) :=
  SlabSobAlg.abs_le_of_Q hCS hsup sf pf (fun t ht => (Q_mono hm f t).trans (hK t ht)) hx

/-- The chain rule for `x ↦ Φ(g(x))`. -/
theorem pd_coframe {Φ : (Idx → ℝ) → (Fin 4 → Fin 4 → ℝ)} (hΦ : ContDiff ℝ 1 Φ)
    {g : Idx → X → ℝ} (sg : ∀ c, ContDiff ℝ ∞ (g c)) (μ a : Fin 4) (ν : Fin 4) (x : X) :
    pd (fun y => Φ (gvec g y) μ a) ν x = fderiv ℝ Φ (gvec g x) (dgvec g ν x) μ a := by
  have hl : HasDerivAt (fun s : ℝ => gvec g (x + s • ev ν)) (dgvec g ν x) 0 := by
    rw [hasDerivAt_pi]
    intro c
    exact hasDerivAt_line_pd (sg c) x ν
  have hΦd : HasFDerivAt Φ (fderiv ℝ Φ (gvec g x)) (gvec g (x + (0 : ℝ) • ev ν)) := by
    rw [zero_smul, add_zero]
    exact ((hΦ.differentiable one_ne_zero) _).hasFDerivAt
  have hc := hΦd.comp_hasDerivAt (0 : ℝ) hl
  have hca : HasDerivAt (fun s : ℝ => Φ (gvec g (x + s • ev ν)) μ a)
      (fderiv ℝ Φ (gvec g x) (dgvec g ν x) μ a) 0 := by
    have h1 := (hasDerivAt_pi.mp hc) μ
    exact (hasDerivAt_pi.mp h1) a
  have hsm : ContDiff ℝ 1 (fun y => Φ (gvec g y) μ a) := by
    have hg : ContDiff ℝ 1 (gvec g) := contDiff_pi.mpr fun c => (sg c).of_le (by norm_cast)
    exact (contDiff_apply ℝ ℝ a).comp ((contDiff_apply ℝ (Fin 4 → ℝ) μ).comp (hΦ.comp hg))
  have hl' := hasDerivAt_line (f := fun y => Φ (gvec g y) μ a) (x := x) ν (s := 0)
    (by rw [zero_smul, add_zero]; exact (hsm.differentiable one_ne_zero) _)
  simp only [zero_smul, add_zero] at hl'
  exact hl'.unique hca

theorem abs_entry_le_norm (M : Fin 4 → Fin 4 → ℝ) (μ a : Fin 4) : |M μ a| ≤ ‖M‖ :=
  (norm_le_pi_norm (M μ) a).trans (norm_le_pi_norm M μ) |>.trans_eq' (Real.norm_eq_abs _).symm

/-- **`thm:hyperbolic`, coframe clause.**  Under the hypotheses of `thm:hyperbolic` (as in
`common_slab_cauchy`), let `Φ` be a `C¹` coframe map (metric components ↦ `4 × 4` matrix
`e^μ{}_a`) with `Φ(G)ᵀ η Φ(G) = G` on a compact set `K` containing all values `g_h(x)` on the
slab.  Then the coframes `e_h = Φ ∘ g_h` and all their first partial derivatives are uniformly
Cauchy on `[0, T] × ℝ³`, and `sup_h(‖e_h‖_∞ + ‖e_h⁻¹‖_∞) < ∞`; hence `e_h` converges in
`L^∞(K') ∩ H¹(K')` (indeed in `C¹`) on every compact `K'` of the slab, with uniform bounds on
`e_h, e_h⁻¹` — the geometric topology of `eq:strong-geometry`. -/
theorem coframe_convergence {Np : Idx → MvPolynomial (NV κ) ℝ} {θ : κ → X → ℝ}
    {T a0 lam Λ K0 : ℝ} {s : ℕ} (hs : 5 ≤ s) (hT : 0 < T) (ha : 0 < a0) (hlam : 0 < lam)
    {g : ℕ → Idx → X → ℝ} {gi : ℕ → Fin 4 → Fin 4 → X → ℝ} {S : ℕ → Idx → X → ℝ}
    (hg : ∀ h, MetricHyp Np θ s T a0 lam Λ K0 (g h) (gi h) (S h))
    (hinit : Tendsto (fun p : ℕ × ℕ => ∑ c, (Q (s - 1) (fun x => g p.1 c x - g p.2 c x) 0 +
      Q (s - 2) (fun x => pd (g p.1 c) 0 x - pd (g p.2 c) 0 x) 0)) atTop (𝓝 0))
    (hsrc : Tendsto (fun p : ℕ × ℕ => ∫ t in (0)..T,
      Real.sqrt (∑ c, Q (s - 2) (fun x => S p.1 c x - S p.2 c x) t)) atTop (𝓝 0))
    {Φ : (Idx → ℝ) → (Fin 4 → Fin 4 → ℝ)} (hΦ : ContDiff ℝ 1 Φ) {Kc : Set (Idx → ℝ)}
    (hKc : IsCompact Kc) (hval : ∀ h (x : X), x 0 ∈ Icc 0 T → gvec (g h) x ∈ Kc)
    (hcompat : ∀ G ∈ Kc, ∀ a b, ∑ μ, ∑ ν, Φ G μ a * etaM μ ν * Φ G ν b = G (a, b)) :
    (∀ ε > 0, ∃ N, ∀ i j, N ≤ i → N ≤ j → ∀ x : X, x 0 ∈ Icc 0 T → ∀ μ a,
      |Φ (gvec (g i) x) μ a - Φ (gvec (g j) x) μ a| ≤ ε) ∧
    (∀ ε > 0, ∃ N, ∀ i j, N ≤ i → N ≤ j → ∀ x : X, x 0 ∈ Icc 0 T → ∀ ν μ a,
      |pd (fun y => Φ (gvec (g i) y) μ a) ν x - pd (fun y => Φ (gvec (g j) y) μ a) ν x| ≤ ε) ∧
    (∃ C : ℝ, ∀ h (x : X), x 0 ∈ Icc 0 T → ∀ μ a, |Φ (gvec (g h) x) μ a| ≤ C ∧
      |(Matrix.of fun μ a => Φ (gvec (g h) x) μ a)⁻¹ μ a| ≤ C) := by
  obtain ⟨CS, hCS, hsup⟩ := MetricHyp.exists_CS
  have hcau := common_slab_cauchy hs hT ha hlam hg hinit hsrc
  have hN := cauchy_N (P := fun i j ε => ∀ t ∈ Icc 0 T, ∑ c, (Q (s - 1)
    (fun x => g i c x - g j c x) t + Q (s - 2) (fun x => pd (g i c) 0 x - pd (g j c) 0 x) t) ≤ ε)
    hcau
  have hterm : ∀ i j t c, Q (s - 1) (fun x => g i c x - g j c x) t +
      Q (s - 2) (fun x => pd (g i c) 0 x - pd (g j c) 0 x) t ≤ ∑ c, (Q (s - 1)
        (fun x => g i c x - g j c x) t + Q (s - 2) (fun x => pd (g i c) 0 x - pd (g j c) 0 x) t) :=
    fun i j t c => Finset.single_le_sum (f := fun c => Q (s - 1) (fun x => g i c x - g j c x) t +
      Q (s - 2) (fun x => pd (g i c) 0 x - pd (g j c) 0 x) t)
      (fun c _ => add_nonneg (Q_nonneg _ _ _) (Q_nonneg _ _ _)) (Finset.mem_univ c)
  have hc1 : ∀ c, ∀ ε > 0, ∃ N, ∀ i j, N ≤ i → N ≤ j → ∀ t ∈ Icc 0 T,
      Q (s - 1) (fun x => g i c x - g j c x) t ≤ ε := by
    intro c ε hε
    obtain ⟨N, hN'⟩ := hN ε hε
    refine ⟨N, fun i j hi hj t ht => ?_⟩
    have h1 := hterm i j t c
    have h2 := hN' i j hi hj t ht
    have h3 := Q_nonneg (s - 2) (fun x => pd (g i c) 0 x - pd (g j c) 0 x) t
    linarith
  have hcd : ∀ c (ν : Fin 4), ∀ ε > 0, ∃ N, ∀ i j, N ≤ i → N ≤ j → ∀ t ∈ Icc 0 T,
      Q (s - 2) (fun x => pd (g i c) ν x - pd (g j c) ν x) t ≤ ε := by
    intro c ν ε hε
    obtain ⟨N, hN'⟩ := hN ε hε
    refine ⟨N, fun i j hi hj t ht => ?_⟩
    have h1 := hterm i j t c
    have h2 := hN' i j hi hj t ht
    induction ν using Fin.cases with
    | zero =>
      have h3 := Q_nonneg (s - 1) (fun x => g i c x - g j c x) t
      linarith
    | succ k =>
      have e : (fun x => pd (g i c) k.succ x - pd (g j c) k.succ x) =
          pd (fun x => g i c x - g j c x) k.succ := by
        have := pd_lincomb ((hg i).sg c) ((hg j).sg c) 1 (-1) k.succ
        simp only [one_mul, neg_one_mul, ← sub_eq_add_neg] at this
        exact this.symm
      rw [e]
      have h4 := Q_pd_le (k := s - 2) k (fun x => g i c x - g j c x) t
      rw [show s - 2 + 1 = s - 1 by omega] at h4
      have h3 := Q_nonneg (s - 2) (fun x => pd (g i c) 0 x - pd (g j c) 0 x) t
      linarith
  -- uniform Cauchy property of the metric and its derivatives
  have ug : ∀ c, ∀ ε > 0, ∃ N, ∀ i j, N ≤ i → N ≤ j → ∀ x : X, x 0 ∈ Icc 0 T →
      |g i c x - g j c x| ≤ ε := fun c =>
    uniformCauchy_of_Q hCS hsup (m := s - 1) (by omega) (fun i => (hg i).sg c)
      (fun i => (hg i).pg c) (hc1 c)
  have udg : ∀ c ν, ∀ ε > 0, ∃ N, ∀ i j, N ≤ i → N ≤ j → ∀ x : X, x 0 ∈ Icc 0 T →
      |pd (g i c) ν x - pd (g j c) ν x| ≤ ε := fun c ν =>
    uniformCauchy_of_Q hCS hsup (m := s - 2) (by omega)
      (fun i => contDiff_pd_top ((hg i).sg c) ν) (fun i => isSPeriodic_pd ((hg i).pg c) ν)
      (hcd c ν)
  -- in sup norm over the components
  have ugv : ∀ ε > 0, ∃ N, ∀ i j, N ≤ i → N ≤ j → ∀ x : X, x 0 ∈ Icc 0 T →
      ‖gvec (g i) x - gvec (g j) x‖ ≤ ε := by
    intro ε hε
    choose Nc hNc using fun c => ug c ε hε
    refine ⟨∑ c, Nc c, fun i j hi hj x hx => (pi_norm_le_iff_of_nonneg hε.le).2 fun c => ?_⟩
    have hle := Finset.single_le_sum (f := Nc) (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
    rw [Real.norm_eq_abs]
    exact hNc c i j (by omega) (by omega) x hx
  have udgv : ∀ ν, ∀ ε > 0, ∃ N, ∀ i j, N ≤ i → N ≤ j → ∀ x : X, x 0 ∈ Icc 0 T →
      ‖dgvec (g i) ν x - dgvec (g j) ν x‖ ≤ ε := by
    intro ν ε hε
    choose Nc hNc using fun c => udg c ν ε hε
    refine ⟨∑ c, Nc c, fun i j hi hj x hx => (pi_norm_le_iff_of_nonneg hε.le).2 fun c => ?_⟩
    have hle := Finset.single_le_sum (f := Nc) (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
    rw [Real.norm_eq_abs]
    exact hNc c i j (by omega) (by omega) x hx
  -- the bound on the derivatives of the metric
  set Bd := Real.sqrt (CS * K0)
  have hBd : 0 ≤ Bd := Real.sqrt_nonneg _
  have bdg : ∀ h ν (x : X), x 0 ∈ Icc 0 T → ‖dgvec (g h) ν x‖ ≤ Bd := by
    intro h ν x hx
    refine (pi_norm_le_iff_of_nonneg hBd).2 fun c => ?_
    rw [Real.norm_eq_abs]
    refine abs_le_of_Q_bound hCS hsup (m := s - 1) (by omega) (contDiff_pd_top ((hg h).sg c) ν)
      (isSPeriodic_pd ((hg h).pg c) ν) (fun t ht => ?_) hx
    induction ν using Fin.cases with
    | zero => exact (hg h).hst t ht c
    | succ k =>
      have := Q_pd_le (k := s - 1) k (g h c) t
      rw [show s - 1 + 1 = s by omega] at this
      exact this.trans ((hg h).hsg t ht c)
  -- uniform continuity and bounds of `Φ`, `DΦ` on the compact set
  have hUΦ := Metric.uniformContinuousOn_iff.mp (hKc.uniformContinuousOn_of_continuous hΦ.continuous.continuousOn)
  have hcD : Continuous (fderiv ℝ Φ) := hΦ.continuous_fderiv one_ne_zero
  have hUD := Metric.uniformContinuousOn_iff.mp (hKc.uniformContinuousOn_of_continuous hcD.continuousOn)
  obtain ⟨BΦ, hBΦ⟩ := hKc.exists_bound_of_continuousOn hΦ.continuous.continuousOn
  obtain ⟨BD, hBD⟩ := hKc.exists_bound_of_continuousOn hcD.continuousOn
  refine ⟨?_, ?_, ?_⟩
  · intro ε hε
    obtain ⟨δ, hδ, hδf⟩ := hUΦ ε hε
    obtain ⟨N, hN'⟩ := ugv (δ / 2) (by positivity)
    refine ⟨N, fun i j hi hj x hx μ a => ?_⟩
    have h1 := hδf _ (hval i x hx) _ (hval j x hx)
      (by rw [dist_eq_norm]; exact (hN' i j hi hj x hx).trans_lt (by linarith))
    rw [dist_eq_norm] at h1
    have := abs_entry_le_norm (Φ (gvec (g i) x) - Φ (gvec (g j) x)) μ a
    simp only [Pi.sub_apply] at this
    linarith
  · intro ε hε
    obtain ⟨δ, hδ, hδf⟩ := hUD (ε / (2 * (Bd + 1))) (by positivity)
    obtain ⟨N1, hN1⟩ := ugv (δ / 2) (by positivity)
    have hBD' : ∀ G ∈ Kc, ‖fderiv ℝ Φ G‖ ≤ |BD| := fun G hG => (hBD G hG).trans (le_abs_self _)
    choose N2 hN2 using fun ν => udgv ν (ε / (2 * (|BD| + 1))) (by positivity)
    refine ⟨N1 + ∑ ν, N2 ν, fun i j hi hj x hx ν μ a => ?_⟩
    have hle := Finset.single_le_sum (f := N2) (fun _ _ => Nat.zero_le _) (Finset.mem_univ ν)
    rw [pd_coframe hΦ (hg i).sg μ a ν x, pd_coframe hΦ (hg j).sg μ a ν x]
    set Di := fderiv ℝ Φ (gvec (g i) x)
    set Dj := fderiv ℝ Φ (gvec (g j) x)
    set vi := dgvec (g i) ν x
    set vj := dgvec (g j) ν x
    have h1 : ‖Di - Dj‖ < ε / (2 * (Bd + 1)) := by
      have := hδf _ (hval i x hx) _ (hval j x hx)
        (by rw [dist_eq_norm]; exact (hN1 i j (by omega) (by omega) x hx).trans_lt (by linarith))
      rwa [dist_eq_norm] at this
    have h2 : ‖vi - vj‖ ≤ ε / (2 * (|BD| + 1)) := hN2 ν i j (by omega) (by omega) x hx
    have h3 : ‖vi‖ ≤ Bd := bdg i ν x hx
    have h4 : ‖Dj‖ ≤ |BD| := hBD' _ (hval j x hx)
    have e : Di vi - Dj vj = (Di - Dj) vi + Dj (vi - vj) := by
      simp [map_sub]
    have hn : ‖Di vi - Dj vj‖ ≤ ε := by
      rw [e]
      calc ‖(Di - Dj) vi + Dj (vi - vj)‖ ≤ ‖Di - Dj‖ * ‖vi‖ + ‖Dj‖ * ‖vi - vj‖ :=
            (norm_add_le _ _).trans (add_le_add ((Di - Dj).le_opNorm vi) (Dj.le_opNorm _))
        _ ≤ ε / (2 * (Bd + 1)) * Bd + |BD| * (ε / (2 * (|BD| + 1))) := by
            gcongr
        _ ≤ ε / 2 + ε / 2 := by
            gcongr
            · rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
              nlinarith
            · rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
              nlinarith [abs_nonneg BD]
        _ = ε := by ring
    have := abs_entry_le_norm (Di vi - Dj vj) μ a
    simp only [Pi.sub_apply] at this
    linarith
  · refine ⟨(1 + 16 * |Λ|) * |BΦ|, fun h x hx μ a => ⟨?_, ?_⟩⟩
    · have := (abs_entry_le_norm _ μ a).trans (hBΦ _ (hval h x hx))
      have h0 : BΦ ≤ |BΦ| := le_abs_self _
      have : 0 ≤ 16 * |Λ| * |BΦ| := by positivity
      nlinarith [abs_nonneg BΦ]
    · set G := gvec (g h) x
      have hG := hval h x hx
      set E : Matrix (Fin 4) (Fin 4) ℝ := Matrix.of fun μ a => Φ G μ a
      set L : Matrix (Fin 4) (Fin 4) ℝ :=
        Matrix.of fun a μ => ∑ b, ∑ ν, gi h a b x * Φ G ν b * etaM ν μ
      -- `g⁻¹ g = 1` at `x`
      have hGH : (Matrix.of fun a c => g h (a, c) x) * (Matrix.of fun a b => gi h a b x) = 1 := by
        ext a b
        simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
        exact (hg h).inv x hx a b
      have hHG := mul_eq_one_comm.mp hGH
      have hLE : L * E = 1 := by
        ext a c
        have hc := congrFun (congrFun hHG a) c
        simp only [Matrix.mul_apply, Matrix.of_apply] at hc
        simp only [Matrix.mul_apply, Matrix.of_apply, L, E]
        rw [← hc]
        have e1 : ∀ b, ∑ ν, ∑ μ, Φ G ν b * etaM ν μ * Φ G μ c = g h (b, c) x := fun b =>
          hcompat G hG b c
        calc ∑ μ, (∑ b, ∑ ν, gi h a b x * Φ G ν b * etaM ν μ) * Φ G μ c =
            ∑ b, gi h a b x * ∑ ν, ∑ μ, Φ G ν b * etaM ν μ * Φ G μ c := by
              simp only [Finset.sum_mul, Finset.mul_sum]
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun b _ => ?_
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun μ _ => by ring
          _ = _ := Finset.sum_congr rfl fun b _ => by rw [e1 b]
      rw [Matrix.inv_eq_left_inv hLE]
      simp only [L, Matrix.of_apply]
      have hΦb : ∀ ν b, |Φ G ν b| ≤ |BΦ| := fun ν b =>
        ((abs_entry_le_norm _ ν b).trans (hBΦ _ hG)).trans (le_abs_self _)
      have hgi : ∀ b, |gi h μ b x| ≤ |Λ| := fun b =>
        ((hg h).bnd x hx μ b).trans (le_abs_self _)
      calc |∑ b, ∑ ν, gi h μ b x * Φ G ν b * etaM ν a| ≤
          ∑ _b : Fin 4, ∑ _ν : Fin 4, |Λ| * |BΦ| := by
            refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => ?_)
            refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun ν _ => ?_)
            rw [abs_mul, abs_mul]
            calc |gi h μ b x| * |Φ G ν b| * |etaM ν a| ≤ |Λ| * |BΦ| * 1 :=
                  mul_le_mul (mul_le_mul (hgi b) (hΦb ν b) (abs_nonneg _) (abs_nonneg _))
                    (abs_etaM_le ν a) (abs_nonneg _) (by positivity)
              _ = _ := by ring
        _ = 16 * |Λ| * |BΦ| := by simp; ring
        _ ≤ (1 + 16 * |Λ|) * |BΦ| := by nlinarith [abs_nonneg BΦ]

/-- Non-vacuity of `coframe_convergence`: the constant flat sequence with the identity coframe
`e = 1` (`1ᵀ η 1 = η`), `s = 5`. -/
example (T : ℝ) (hT : 0 < T) :=
  coframe_convergence (κ := Empty) (s := 5) (by norm_num) hT one_pos one_pos
    (g := fun _ => etaF) (gi := fun _ => etaInv) (S := fun _ _ _ => 0)
    (fun _ => flat_metricHyp 5 T) (by simp [Q_const]) (by simp [Q_const])
    (Φ := fun _ μ a => if μ = a then 1 else 0) contDiff_const (Kc := {gvec etaF 0})
    isCompact_singleton (fun _ x _ => by rw [Set.mem_singleton_iff]; rfl)
    (fun G hG a b => by
      simp only [Set.mem_singleton_iff] at hG
      subst hG
      fin_cases a <;> fin_cases b <;> simp [etaM, gvec, etaF, Fin.sum_univ_four])

end ReducedWaveStab

end RenewalGeometry
