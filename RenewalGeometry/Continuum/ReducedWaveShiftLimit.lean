/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.ReducedWaveSlabCoframe
import RenewalGeometry.Continuum.ReducedWaveShiftCauchy

/-!
# `thm:hyperbolic` with a nonzero shift: the limits and the coframe clause

The limit and coframe statements of `ReducedWaveSlabLimit.lean`, `ReducedWaveSlabCoframe.lean`
use the hyperbolicity only through `common_slab_cauchy`; here they are restated under the paper's
hypothesis (`MetricHypSh`: uniform hyperbolicity with a common time function, any bounded shift)
through `common_slab_cauchy_sh`.

* **`common_slab_limit_sh`** — `g_h → g` in `C_tH^{s-1}`, `∂ₜg_h → ∂ₜg` in `C_tH^{s-2}`
  (uniformly on the slab, with `ġ = ∂ₜg` and the slice-derivative limits);
* **`coframe_convergence_sh`** — compatible coframes converge in the geometric topology of
  `eq:strong-geometry`.
-/

open MeasureTheory Filter Topology Set
open scoped BigOperators ContDiff

noncomputable section

namespace RenewalGeometry.ReducedWaveShift

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk SlabSobAlg ReducedWaveStab SlabWaveShift

set_option linter.unusedSectionVars false

variable {κ : Type} [Fintype κ]

/-- **`thm:hyperbolic`, the first two limits, with the paper's hyperbolicity hypothesis (nonzero
shift).** Under the hypotheses of `thm:hyperbolic` (`MetricHypSh`)
(`Σ = 𝕋³`, `s ≥ 5`, common constants; initial data Cauchy in `H^{s-1} × H^{s-2}`, sources Cauchy
in `L¹_tH^{s-2}`) there are a limit metric `g` and its time derivative `ġ` on the slab with:
(i) `g_h → g`, `∂ₜg_h → ġ` uniformly on `[0, T] × ℝ³`; (ii) `g, ġ` continuous on the slab and
`g(t, y) = g(0, y) + ∫₀ᵗ ġ(s, y) ds` (so `ġ = ∂ₜg`); (iii) `g_h → g` in `C_tH^{s-1}`: the slice
derivatives `∂^w g_h(t)`, `|w| ≤ s - 1`, converge in `L²([0,1]³)` uniformly in `t ∈ [0, T]` to
`G_w(t)`, `t ↦ G_w(t)` continuous, `G_∅(t) = [g(t, ·)]`; (iv) `∂ₜg_h → ġ` in `C_tH^{s-2}` in the
same sense, `G'_∅(t) = [ġ(t, ·)]`. -/
theorem common_slab_limit_sh {Np : Idx → MvPolynomial (NV κ) ℝ} {θ : κ → X → ℝ}
    {T a0 lamS Λ K0 : ℝ} {s : ℕ} (hs : 5 ≤ s) (hT : 0 < T) (ha : 0 < a0) (hlamS : 0 < lamS)
    {g : ℕ → Idx → X → ℝ} {gi : ℕ → Fin 4 → Fin 4 → X → ℝ} {S : ℕ → Idx → X → ℝ}
    (hg : ∀ h, MetricHypSh Np θ s T a0 lamS Λ K0 (g h) (gi h) (S h))
    (hinit : Tendsto (fun p : ℕ × ℕ => ∑ c, (Q (s - 1) (fun x => g p.1 c x - g p.2 c x) 0 +
      Q (s - 2) (fun x => pd (g p.1 c) 0 x - pd (g p.2 c) 0 x) 0)) atTop (𝓝 0))
    (hsrc : Tendsto (fun p : ℕ × ℕ => ∫ t in (0)..T,
      Real.sqrt (∑ c, Q (s - 2) (fun x => S p.1 c x - S p.2 c x) t)) atTop (𝓝 0)) :
    ∃ (gl gt : Idx → X → ℝ) (G G' : Idx → List (Fin 3) → ℝ → Lp ℝ 2 μc),
      (∀ ε > 0, ∃ N, ∀ h, N ≤ h → ∀ x : X, x 0 ∈ Icc 0 T → ∀ c,
        |g h c x - gl c x| ≤ ε ∧ |pd (g h c) 0 x - gt c x| ≤ ε) ∧
      (∀ c, ContinuousOn (gl c) {x : X | x 0 ∈ Icc 0 T} ∧
        ContinuousOn (gt c) {x : X | x 0 ∈ Icc 0 T}) ∧
      (∀ c (x : X), x 0 ∈ Icc 0 T → gl c x = gl c (Fin.cons 0 (Fin.tail x)) +
        ∫ σ in (0)..(x 0), gt c (Fin.cons σ (Fin.tail x))) ∧
      (∀ ε > 0, ∃ N, ∀ h, N ≤ h → ∀ t ∈ Icc 0 T, ∀ c (w : List (Fin 3)), w.length ≤ s - 1 →
        ‖toL2 (fun y => sd w (g h c) (Fin.cons t y)) - G c w t‖ ≤ ε) ∧
      (∀ ε > 0, ∃ N, ∀ h, N ≤ h → ∀ t ∈ Icc 0 T, ∀ c (w : List (Fin 3)), w.length ≤ s - 2 →
        ‖toL2 (fun y => sd w (pd (g h c) 0) (Fin.cons t y)) - G' c w t‖ ≤ ε) ∧
      (∀ c w, ContinuousOn (G c w) (Icc 0 T) ∧ ContinuousOn (G' c w) (Icc 0 T)) ∧
      (∀ c, ∀ t ∈ Icc 0 T, G c [] t = toL2 (fun y => gl c (Fin.cons t y)) ∧
        G' c [] t = toL2 (fun y => gt c (Fin.cons t y))) := by
  obtain ⟨CS, hCS, hsup⟩ := MetricHyp.exists_CS
  have hcau := common_slab_cauchy_sh hs hT ha hlamS hg hinit hsrc
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
  have hc2 : ∀ c, ∀ ε > 0, ∃ N, ∀ i j, N ≤ i → N ≤ j → ∀ t ∈ Icc 0 T,
      Q (s - 2) (fun x => pd (g i c) 0 x - pd (g j c) 0 x) t ≤ ε := by
    intro c ε hε
    obtain ⟨N, hN'⟩ := hN ε hε
    refine ⟨N, fun i j hi hj t ht => ?_⟩
    have h1 := hterm i j t c
    have h2 := hN' i j hi hj t ht
    have h3 := Q_nonneg (s - 1) (fun x => g i c x - g j c x) t
    linarith
  -- uniform limits on the slab
  choose gl hgl hglc using fun c => exists_slab_limit hCS hsup (m := s - 1) (by omega)
    (fun i => (hg i).sg c) (fun i => (hg i).pg c) (hc1 c)
  choose gt hgt hgtc using fun c => exists_slab_limit hCS hsup (m := s - 2) (by omega)
    (fun i => contDiff_pd_top ((hg i).sg c) 0) (fun i => isSPeriodic_pd ((hg i).pg c) 0) (hc2 c)
  -- limits of the slice derivatives
  have hG : ∀ c (w : List (Fin 3)), ∃ G : ℝ → Lp ℝ 2 μc, ContinuousOn G (Icc 0 T) ∧
      (w.length ≤ s - 1 → ∀ ε > 0, ∃ N, ∀ i, N ≤ i → ∀ t ∈ Icc 0 T,
        ‖toL2 (fun y => sd w (g i c) (Fin.cons t y)) - G t‖ ≤ ε) := by
    intro c w
    by_cases hw : w.length ≤ s - 1
    · obtain ⟨G, h1, h2⟩ := exists_word_limit (fun i => (hg i).sg c) (hc1 c) w hw
      exact ⟨G, h2, fun _ => h1⟩
    · exact ⟨fun _ => 0, continuousOn_const, fun h => absurd h hw⟩
  choose G hGc hGl using hG
  have hG' : ∀ c (w : List (Fin 3)), ∃ G : ℝ → Lp ℝ 2 μc, ContinuousOn G (Icc 0 T) ∧
      (w.length ≤ s - 2 → ∀ ε > 0, ∃ N, ∀ i, N ≤ i → ∀ t ∈ Icc 0 T,
        ‖toL2 (fun y => sd w (pd (g i c) 0) (Fin.cons t y)) - G t‖ ≤ ε) := by
    intro c w
    by_cases hw : w.length ≤ s - 2
    · obtain ⟨G, h1, h2⟩ := exists_word_limit (fun i => contDiff_pd_top ((hg i).sg c) 0) (hc2 c)
        w hw
      exact ⟨G, h2, fun _ => h1⟩
    · exact ⟨fun _ => 0, continuousOn_const, fun h => absurd h hw⟩
  choose G' hGc' hGl' using hG'
  refine ⟨gl, gt, G, G', ?_, fun c => ⟨hglc c, hgtc c⟩,
    fun c x hx => ftc_limit (fun i => (hg i).sg c) (hgl c) (hgt c) (hgtc c) x hx, ?_, ?_,
    fun c w => ⟨hGc c w, hGc' c w⟩, fun c t ht => ⟨?_, ?_⟩⟩
  · -- uniform convergence, uniformly in the components
    intro ε hε
    have h : ∀ c, ∃ N, ∀ i, N ≤ i → ∀ x : X, x 0 ∈ Icc 0 T →
        |g i c x - gl c x| ≤ ε ∧ |pd (g i c) 0 x - gt c x| ≤ ε := by
      intro c
      obtain ⟨N1, h1⟩ := hgl c ε hε
      obtain ⟨N2, h2⟩ := hgt c ε hε
      exact ⟨N1 + N2, fun i hi x hx => ⟨h1 i (by omega) x hx, h2 i (by omega) x hx⟩⟩
    choose Nc hNc using h
    refine ⟨∑ c, Nc c, fun i hi x hx c => hNc c i ?_ x hx⟩
    exact le_trans (Finset.single_le_sum (f := Nc) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ c)) hi
  · intro ε hε
    have h : ∀ c (w : List (Fin 3)), ∃ N, w.length ≤ s - 1 → ∀ i, N ≤ i → ∀ t ∈ Icc 0 T,
        ‖toL2 (fun y => sd w (g i c) (Fin.cons t y)) - G c w t‖ ≤ ε := by
      intro c w
      by_cases hw : w.length ≤ s - 1
      · obtain ⟨N, hN⟩ := hGl c w hw ε hε
        exact ⟨N, fun _ => hN⟩
      · exact ⟨0, fun h => absurd h hw⟩
    choose Nc hNc using h
    refine ⟨∑ c, ∑ w ∈ wordsLE 3 (s - 1), Nc c w, fun i hi t ht c w hw => hNc c w hw i ?_ t ht⟩
    have h1 := Finset.single_le_sum (f := fun w => Nc c w) (fun _ _ => Nat.zero_le _)
      (mem_wordsLE.mpr hw)
    have h2 := Finset.single_le_sum (f := fun c => ∑ w ∈ wordsLE 3 (s - 1), Nc c w)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
    omega
  · intro ε hε
    have h : ∀ c (w : List (Fin 3)), ∃ N, w.length ≤ s - 2 → ∀ i, N ≤ i → ∀ t ∈ Icc 0 T,
        ‖toL2 (fun y => sd w (pd (g i c) 0) (Fin.cons t y)) - G' c w t‖ ≤ ε := by
      intro c w
      by_cases hw : w.length ≤ s - 2
      · obtain ⟨N, hN⟩ := hGl' c w hw ε hε
        exact ⟨N, fun _ => hN⟩
      · exact ⟨0, fun h => absurd h hw⟩
    choose Nc hNc using h
    refine ⟨∑ c, ∑ w ∈ wordsLE 3 (s - 2), Nc c w, fun i hi t ht c w hw => hNc c w hw i ?_ t ht⟩
    have h1 := Finset.single_le_sum (f := fun w => Nc c w) (fun _ _ => Nat.zero_le _)
      (mem_wordsLE.mpr hw)
    have h2 := Finset.single_le_sum (f := fun c => ∑ w ∈ wordsLE 3 (s - 2), Nc c w)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
    omega
  · exact toL2_limit_eq (fun i => (hg i).sg c) (hgl c) (hglc c) (hGl c [] (by simp)) ht
  · exact toL2_limit_eq (fun i => contDiff_pd_top ((hg i).sg c) 0) (hgt c) (hgtc c)
      (hGl' c [] (by simp)) ht


/-- **`thm:hyperbolic`, coframe clause, with the paper's hyperbolicity hypothesis (nonzero
shift).**  Under the hypotheses of `thm:hyperbolic` (`MetricHypSh`, as in `common_slab_cauchy_sh`), let `Φ` be a `C¹` coframe map (metric components ↦ `4 × 4` matrix
`e^μ{}_a`) with `Φ(G)ᵀ η Φ(G) = G` on a compact set `K` containing all values `g_h(x)` on the
slab.  Then the coframes `e_h = Φ ∘ g_h` and all their first partial derivatives are uniformly
Cauchy on `[0, T] × ℝ³`, and `sup_h(‖e_h‖_∞ + ‖e_h⁻¹‖_∞) < ∞`; hence `e_h` converges in
`L^∞(K') ∩ H¹(K')` (indeed in `C¹`) on every compact `K'` of the slab, with uniform bounds on
`e_h, e_h⁻¹` — the geometric topology of `eq:strong-geometry`. -/
theorem coframe_convergence_sh {Np : Idx → MvPolynomial (NV κ) ℝ} {θ : κ → X → ℝ}
    {T a0 lamS Λ K0 : ℝ} {s : ℕ} (hs : 5 ≤ s) (hT : 0 < T) (ha : 0 < a0) (hlamS : 0 < lamS)
    {g : ℕ → Idx → X → ℝ} {gi : ℕ → Fin 4 → Fin 4 → X → ℝ} {S : ℕ → Idx → X → ℝ}
    (hg : ∀ h, MetricHypSh Np θ s T a0 lamS Λ K0 (g h) (gi h) (S h))
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
  have hcau := common_slab_cauchy_sh hs hT ha hlamS hg hinit hsrc
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


/-- Non-vacuity of `common_slab_limit_sh` (the constant shifted metric, `∂ₜ` spacelike). -/
example (T : ℝ) (hT : 0 < T) :=
  common_slab_limit_sh (κ := Empty) (s := 5) (by norm_num) hT one_pos one_pos
    (g := fun _ => gShift) (gi := fun _ => giShift) (S := fun _ _ _ => 0)
    (fun _ => shifted_metricHypSh 5 T) (by simp [Q_const]) (by simp [Q_const])

end RenewalGeometry.ReducedWaveShift
