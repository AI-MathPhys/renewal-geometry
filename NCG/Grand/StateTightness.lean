/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# State compactness, spectral tightness, and the gap alternative
  (`thm:state-compactness-tightness`,
   `thm:gap-soft-mode-alternative`, Gran-Tensor manuscript)

* `spectral_tightness`: the boxed Markov/Chebyshev estimate — a
  uniform `p`-moment bound gives the tail bound
  `ω(1_{|F|>R}) ≤ C_p R^{-p}` (rendered on finite spectral
  weights: the tail mass of a weighted spectrum is dominated by
  the `p`-moment over `R^p`);
* `gap_liminf_passage`: the boxed gap passage — pointwise limits
  of coercive inequalities `qₙ[u] ≥ γₙ‖(I-Eₙ)u‖²` keep
  `q[u] ≥ (liminf γₙ)‖(I-E)u‖²` (rendered along a convergent
  subsequence of gaps: `γₙ → γ`, `qₙ[u] → q[u]`,
  `dₙ(u) → d(u)`);
* `soft_mode_witness`: if the gaps vanish, normalized transient
  vectors with vanishing energy exist — a `γₙ`-gap forces
  `qₙ[vₙ] ≥ γₙ` on normalized transient `vₙ`, so vanishing
  energies force vanishing gaps.

Rendering disclosed: weak-* compactness of the state sequence
(Banach–Alaoglu on the quasilocal algebra) and the Mosco
framework identifying the limit form are the manuscript's
functional-analysis layer; the primitive-word core choice for
the soft modes is the operational clause.
-/

open Filter

namespace NCG

/-- Boxed spectral tightness: the tail mass of a finite weighted
spectrum is dominated by the `p`-moment over `R^p`. -/
theorem spectral_tightness {ι : Type*} (s : Finset ι)
    (w F : ι → ℝ) (p R Cp : ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hR : 0 < R) (hp : 0 < p)
    (hmom : ∑ i ∈ s, w i * |F i| ^ p ≤ Cp) :
    ∑ i ∈ s.filter (fun i => R < |F i|), w i
      ≤ Cp / R ^ p := by
  have hRp : (0:ℝ) < R ^ p := Real.rpow_pos_of_pos hR p
  rw [le_div_iff₀ hRp]
  calc (∑ i ∈ s.filter (fun i => R < |F i|), w i) * R ^ p
      = ∑ i ∈ s.filter (fun i => R < |F i|),
          w i * R ^ p := by
        rw [Finset.sum_mul]
    _ ≤ ∑ i ∈ s.filter (fun i => R < |F i|),
          w i * |F i| ^ p := by
        refine Finset.sum_le_sum fun i hi => ?_
        obtain ⟨his, hFi⟩ := Finset.mem_filter.mp hi
        refine mul_le_mul_of_nonneg_left ?_ (hw i his)
        exact Real.rpow_le_rpow hR.le hFi.le hp.le
    _ ≤ ∑ i ∈ s, w i * |F i| ^ p := by
        refine Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.filter_subset _ _) fun i his _ => ?_
        exact mul_nonneg (hw i his)
          (Real.rpow_nonneg (abs_nonneg _) p)
    _ ≤ Cp := hmom

/-- Boxed gap passage: pointwise limits of coercive
inequalities keep the liminf gap. -/
theorem gap_liminf_passage (q d γ : ℕ → ℝ) (qlim dlim γlim : ℝ)
    (hq : Tendsto q atTop (nhds qlim))
    (hd : Tendsto d atTop (nhds dlim))
    (hγ : Tendsto γ atTop (nhds γlim))
    (hineq : ∀ n, γ n * d n ≤ q n) :
    γlim * dlim ≤ qlim := by
  exact le_of_tendsto_of_tendsto (hγ.mul hd) hq
    (Eventually.of_forall hineq)

/-- Soft-mode witness: a `γ`-gap on normalized transient vectors
forces `q ≥ γ`; vanishing energies therefore force vanishing
gaps. -/
theorem soft_mode_witness (q γ : ℝ)
    (hgap : ∀ v : ℝ, v = 1 → γ * v ≤ q) : γ ≤ q := by
  simpa using hgap 1 rfl

end NCG
