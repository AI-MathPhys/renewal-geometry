/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.AffineBkmLocalUniformLimitExact
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

/-!
# Exact affine derivative of a matrix-log pairing

Finite resolvent cutoffs have derivatives equal to the corresponding
truncated BKM curvatures.  Local Dini convergence of those curvatures and
pointwise convergence of the cutoff log pairings therefore identify the
derivative of the exact spectral matrix-log pairing.
-/

open Matrix Filter Topology
open scoped ComplexOrder Matrix.Norms.L2Operator

namespace NCG
namespace QRE

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {σ v : Matrix n n ℂ}

/-- **Exact affine matrix-log derivative.**  Throughout a faithful affine
interval, the derivative of `Re Tr(v log(σ+t v))` is the BKM quadratic form
at the current base point. -/
theorem affineMatrixLogPairing_hasDerivAt
    (hσ : σ.IsHermitian) (hv : v.IsHermitian) {A B t : ℝ}
    (hpos : ∀ u ∈ Set.Ioo A B, (σ + u • v).PosDef)
    (ht : t ∈ Set.Ioo A B) :
    HasDerivAt
      (fun u : ℝ =>
        (Matrix.trace (v * matLog (affineMatrix_isHermitian hσ hv u))).re)
      (affineBkmForm hσ hv t) t := by
  let f : ℕ → ℝ → ℝ := fun N u =>
    truncatedAffineMatrixLogPairing hσ hv (N : ℝ) u
  let f' : ℕ → ℝ → ℝ := fun N u =>
    affineTruncatedBkmCurvature σ v N u
  let g : ℝ → ℝ := fun u =>
    (Matrix.trace (v * matLog (affineMatrix_isHermitian hσ hv u))).re
  have hf' : TendstoLocallyUniformlyOn f' (affineBkmForm hσ hv)
      atTop (Set.Ioo A B) := by
    simpa only [f'] using
      tendstoLocallyUniformlyOn_affineTruncatedBkmCurvature hσ hv hpos
  have hfderiv : ∀ᶠ N in atTop, ∀ x ∈ Set.Ioo A B,
      HasDerivAt (f N) (f' N x) x := by
    filter_upwards with N
    intro x hx
    let δ : ℝ := min (x - A) (B - x) / 2
    have hmin : 0 < min (x - A) (B - x) :=
      lt_min (by linarith [hx.1]) (by linarith [hx.2])
    have hδ : 0 < δ := by dsimp [δ]; linarith
    have hδleft : δ < x - A := by
      have hle := min_le_left (x - A) (B - x)
      dsimp [δ]
      linarith
    have hδright : δ < B - x := by
      have hle := min_le_right (x - A) (B - x)
      dsimp [δ]
      linarith
    have hposIcc : ∀ y ∈ Set.Icc (x - δ) (x + δ),
        (σ + y • v).PosDef := by
      intro y hy
      apply hpos y
      constructor <;> linarith [hy.1, hy.2]
    have hd := truncatedAffineMatrixLogPairing_hasDerivAt hσ hv
      hδ hposIcc (Nat.cast_nonneg N)
    have hxpos : (σ + x • v).PosDef := hpos x hx
    have hcurv := affineTruncatedBkmCurvature_eq_truncated
      hσ hv (N := N) hxpos
    change HasDerivAt
      (fun u : ℝ => truncatedAffineMatrixLogPairing hσ hv (N : ℝ) u)
      (affineTruncatedBkmCurvature σ v N x) x
    exact hd.congr_deriv hcurv.symm
  have hfg : ∀ x ∈ Set.Ioo A B,
      Tendsto (fun N : ℕ => f N x) atTop (𝓝 (g x)) := by
    intro x hx
    let hx' : (σ + x • v).PosDef :=
      ⟨affineMatrix_isHermitian hσ hv x, (hpos x hx).2⟩
    have hlim := (tendsto_truncatedMatrixLogPairing hv hx').comp
      tendsto_natCast_atTop_atTop
    change Tendsto
      (fun N : ℕ => truncatedMatrixLogPairing v hx'.1 (N : ℝ)) atTop
      (𝓝 ((Matrix.trace (v * matLog hx'.1)).re))
    apply hlim.congr'
    filter_upwards with N
    rfl
  exact hasDerivAt_of_tendstoLocallyUniformlyOn isOpen_Ioo
    hf' hfderiv hfg ht

end QRE
end NCG
