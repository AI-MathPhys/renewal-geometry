/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.StrongInterpolationConvergenceExact
import NCG.Grand.WeakStrongBilinearPairingExact

/-!
# Weak--strong Palatini curvature limit

This file formalizes the analytic product passage in hypothesis (E4) of
`thm:Palatini`.  An interpolation estimate upgrades the coframe convergence,
the bounded wedge map gives strong convergence of the coframe bivector, and
bounded weak curvature convergence then passes the Palatini/Holst pairing.
-/

open Filter Topology

noncomputable section

namespace NCG.PalatiniWeakStrongLimit

variable {K E Biv Curv : Type*} [RCLike K]
variable [NormedAddCommGroup E] [NormedSpace K E]
variable [NormedAddCommGroup Biv] [NormedSpace K Biv]
variable [NormedAddCommGroup Curv] [NormedSpace K Curv]

/-- Exact weak--strong product passage for the Palatini and Holst densities. -/
theorem curvature_pairing_tendsto_of_coframe_interpolation
    {ι : Type*} {l : Filter ι}
    (wedge : E →L[K] (E →L[K] Biv))
    (pairing : Biv →L[K] (Curv →L[K] K))
    (coframe : ι → E) (coframeLimit : E)
    (curvature : ι → Curv) (curvatureLimit : Curv)
    (lowError : ι → ℝ) (C theta curvatureBound : ℝ)
    (hC : 0 ≤ C) (htheta : 0 < theta)
    (hlow : Tendsto lowError l (𝓝 0))
    (hinterpolation : ∀ i,
      ‖coframe i - coframeLimit‖ ≤ C * (lowError i) ^ theta)
    (hcurvatureBound : ∀ i, ‖curvature i‖ ≤ curvatureBound)
    (hcurvatureBoundNonneg : 0 ≤ curvatureBound)
    (hcurvatureWeak : Tendsto
      (fun i => toWeakSpace K Curv (curvature i)) l
      (𝓝 (toWeakSpace K Curv curvatureLimit))) :
    Tendsto
      (fun i => pairing (wedge (coframe i) (coframe i)) (curvature i)) l
      (𝓝 (pairing (wedge coframeLimit coframeLimit) curvatureLimit)) := by
  have hcoframe : Tendsto coframe l (𝓝 coframeLimit) :=
    NCG.StrongInterpolationConvergence.tendsto_of_norm_interpolation
      coframe coframeLimit lowError C theta hC htheta hlow hinterpolation
  have hbivector : Tendsto (fun i => wedge (coframe i) (coframe i)) l
      (𝓝 (wedge coframeLimit coframeLimit)) :=
    NCG.StrongInterpolationConvergence.tendsto_diagonal_bilinear
      wedge coframe coframeLimit hcoframe
  exact NCG.WeakStrongBilinearPairing.tendsto_of_strong_of_bounded_weak
    pairing (fun i => wedge (coframe i) (coframe i))
    (wedge coframeLimit coframeLimit) curvature curvatureLimit curvatureBound
    hcurvatureBoundNonneg hcurvatureBound hbivector hcurvatureWeak

/-- A pair of bounded Lorentz contractions (identity and Hodge-star) passes
simultaneously, giving both Palatini and Holst limits from the same E4 data. -/
theorem palatini_and_holst_pairings_tendsto
    {ι : Type*} {l : Filter ι}
    (wedge : E →L[K] (E →L[K] Biv))
    (palatini holst : Biv →L[K] (Curv →L[K] K))
    (coframe : ι → E) (coframeLimit : E)
    (curvature : ι → Curv) (curvatureLimit : Curv)
    (lowError : ι → ℝ) (C theta curvatureBound : ℝ)
    (hC : 0 ≤ C) (htheta : 0 < theta)
    (hlow : Tendsto lowError l (𝓝 0))
    (hinterpolation : ∀ i,
      ‖coframe i - coframeLimit‖ ≤ C * (lowError i) ^ theta)
    (hcurvatureBound : ∀ i, ‖curvature i‖ ≤ curvatureBound)
    (hcurvatureBoundNonneg : 0 ≤ curvatureBound)
    (hcurvatureWeak : Tendsto
      (fun i => toWeakSpace K Curv (curvature i)) l
      (𝓝 (toWeakSpace K Curv curvatureLimit))) :
    Tendsto
      (fun i => (palatini (wedge (coframe i) (coframe i)) (curvature i),
        holst (wedge (coframe i) (coframe i)) (curvature i))) l
      (𝓝 (palatini (wedge coframeLimit coframeLimit) curvatureLimit,
        holst (wedge coframeLimit coframeLimit) curvatureLimit)) := by
  exact (curvature_pairing_tendsto_of_coframe_interpolation wedge palatini
    coframe coframeLimit curvature curvatureLimit lowError C theta curvatureBound
    hC htheta hlow hinterpolation hcurvatureBound hcurvatureBoundNonneg
    hcurvatureWeak).prodMk_nhds
    (curvature_pairing_tendsto_of_coframe_interpolation wedge holst
      coframe coframeLimit curvature curvatureLimit lowError C theta curvatureBound
      hC htheta hlow hinterpolation hcurvatureBound hcurvatureBoundNonneg
      hcurvatureWeak)

end NCG.PalatiniWeakStrongLimit
