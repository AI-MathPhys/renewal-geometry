/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.RieszProjectionStability

import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.InnerProductSpace.GramMatrix
/-!
# Convergence of finite source Gram matrices

Norm convergence of spectral projections, together with convergence of finitely many source
vectors, implies convergence of their projected Gram matrix.  This is the abstract final step
in the low-energy source-Gram conclusion of the compact-screen alternative.
-/

open Filter Topology

noncomputable section

namespace NCG.SpectralApproximation

universe u v w

variable {K : Type u} [RCLike K]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H]
variable {ι : Type w}

/-- The Gram matrix of a finite source family after applying an operator. -/
def sourceGram (T : H →L[K] H) (v : ι → H) : Matrix ι ι K :=
  fun i j ↦ inner K (T (v i)) (T (v j))

/-- Norm-convergent operators applied to convergent moving vectors converge. -/
theorem apply_tendsto_of_operatorNorm_tendsto
    {T : ℕ → H →L[K] H} {Tlim : H →L[K] H}
    {v : ℕ → H} {vlim : H}
    (hT : Tendsto T atTop (𝓝 Tlim))
    (hv : Tendsto v atTop (𝓝 vlim)) :
    Tendsto (fun n ↦ T n (v n)) atTop (𝓝 (Tlim vlim)) := by
  exact (continuous_fst.clm_apply continuous_snd).continuousAt.tendsto.comp
    (hT.prodMk_nhds hv)

/-- Every entry of the projected source Gram matrix converges. -/
theorem sourceGram_entry_tendsto
    {T : ℕ → H →L[K] H} {Tlim : H →L[K] H}
    {v : ℕ → ι → H} {vlim : ι → H}
    (hT : Tendsto T atTop (𝓝 Tlim))
    (hv : ∀ i, Tendsto (fun n ↦ v n i) atTop (𝓝 (vlim i)))
    (i j : ι) :
    Tendsto (fun n ↦ sourceGram (T n) (v n) i j) atTop
      (𝓝 (sourceGram Tlim vlim i j)) := by
  exact (apply_tendsto_of_operatorNorm_tendsto hT (hv i)).inner
    (apply_tendsto_of_operatorNorm_tendsto hT (hv j))

/-- The whole finite projected source Gram matrix converges in its canonical topology. -/
theorem sourceGram_tendsto
    {T : ℕ → H →L[K] H} {Tlim : H →L[K] H}
    {v : ℕ → ι → H} {vlim : ι → H}
    (hT : Tendsto T atTop (𝓝 Tlim))
    (hv : ∀ i, Tendsto (fun n ↦ v n i) atTop (𝓝 (vlim i))) :
    Tendsto (fun n ↦ sourceGram (T n) (v n)) atTop
      (𝓝 (sourceGram Tlim vlim)) := by
  change Tendsto
    (fun n i j ↦ inner K (T n (v n i)) (T n (v n j))) atTop
    (𝓝 (fun i j ↦ inner K (Tlim (vlim i)) (Tlim (vlim j))))
  rw [tendsto_pi_nhds]
  intro i
  rw [tendsto_pi_nhds]
  intro j
  exact sourceGram_entry_tendsto hT hv i j

/-- Determinants of finite projected source Gram matrices converge. -/
theorem sourceGram_det_tendsto
    [Fintype ι] [DecidableEq ι]
    {T : ℕ → H →L[K] H} {Tlim : H →L[K] H}
    {v : ℕ → ι → H} {vlim : ι → H}
    (hT : Tendsto T atTop (𝓝 Tlim))
    (hv : ∀ i, Tendsto (fun n ↦ v n i) atTop (𝓝 (vlim i))) :
    Tendsto (fun n ↦ (sourceGram (T n) (v n)).det) atTop
      (𝓝 (sourceGram Tlim vlim).det) := by
  exact (continuous_id.matrix_det.tendsto _).comp (sourceGram_tendsto hT hv)

/-- If the limiting projected source family has nonsingular Gram matrix, no sufficiently late
cutoff source Gram can collapse. -/
theorem eventually_sourceGram_det_ne_zero
    [Fintype ι] [DecidableEq ι]
    {T : ℕ → H →L[K] H} {Tlim : H →L[K] H}
    {v : ℕ → ι → H} {vlim : ι → H}
    (hT : Tendsto T atTop (𝓝 Tlim))
    (hv : ∀ i, Tendsto (fun n ↦ v n i) atTop (𝓝 (vlim i)))
    (hdet : (sourceGram Tlim vlim).det ≠ 0) :
    ∀ᶠ n in atTop, (sourceGram (T n) (v n)).det ≠ 0 := by
  have hopen : {z : K | z ≠ 0} ∈ 𝓝 (sourceGram Tlim vlim).det :=
    isOpen_compl_singleton.mem_nhds hdet
  exact (sourceGram_det_tendsto hT hv).eventually hopen

/-- Linear independence of a finite limiting projected source family persists at every
sufficiently late cutoff.  In particular, a rank-three source cannot collapse. -/
theorem eventually_linearIndependent_projected_sources
    [Finite ι]
    {T : ℕ → H →L[K] H} {Tlim : H →L[K] H}
    {v : ℕ → ι → H} {vlim : ι → H}
    (hT : Tendsto T atTop (𝓝 Tlim))
    (hv : ∀ i, Tendsto (fun n ↦ v n i) atTop (𝓝 (vlim i)))
    (hind : LinearIndependent K (fun i ↦ Tlim (vlim i))) :
    ∀ᶠ n in atTop, LinearIndependent K (fun i ↦ T n (v n i)) := by
  classical
  letI := Fintype.ofFinite ι
  have hdet : (sourceGram Tlim vlim).det ≠ 0 := by
    exact Matrix.det_gram_ne_zero_iff_linearIndependent.mpr hind
  filter_upwards [eventually_sourceGram_det_ne_zero hT hv hdet] with n hn
  exact Matrix.det_gram_ne_zero_iff_linearIndependent.mp hn


end NCG.SpectralApproximation
