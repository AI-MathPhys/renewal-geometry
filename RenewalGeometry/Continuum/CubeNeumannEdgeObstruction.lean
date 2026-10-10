/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.UhlenbeckGaugeTheorem

/-!
# Two structural facts for the continuity method of Uhlenbeck's theorem on cubes and balls:
  the edge obstruction of the Neumann condition, and the radial gauge along dilations

Generic infrastructure (no renewal notions) for `prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript (findings of the cube rendering, batch g3).

* `pd_eq_zero_of_vanish_hyperplane`: a function differentiable at `p` and vanishing on the
  hyperplane `{x_i = p_i}` near `p` has zero partial derivative at `p` in every tangential
  direction `e_j`, `j ≠ i`.
* `curvature_edge_zero` (**edge obstruction**): if a connection `B` is differentiable at a point
  `p` of an edge `{x_i = p_i} ∩ {x_j = p_j}` (`i ≠ j`) and its normal components vanish on the two
  faces near `p` (`B_i = 0` on `{x_i = p_i}`, `B_j = 0` on `{x_j = p_j}`: the Neumann condition
  `B·ν = 0` on both faces), then `F^B_{ij}(p) = ∂_i B_j - ∂_j B_i + [B_i, B_j] = 0`.  Since
  `|F^{R·A}| = |F^A|` pointwise for `C²` unitary gauges, a Neumann Coulomb gauge of a connection
  with `F^A_{ij} ≠ 0` on an edge of the cube is never `C²` up to that edge.  Consequence for the
  continuity method on a cube: along the dilation path the gauges satisfy the inhomogeneous
  condition `∂_ν u = u A_ν` on the faces, their even reflections have kinks (only `H^{3/2-}`), and
  the Hilbert-scale implicit-function step in the reflected (cosine) class is not available; an
  `L^p` framework (gauges in `W^{1,p}`, `p > 4`) or a smooth domain is needed.
* `dilateConn_radial` (**radial gauge is preserved by dilations**): if `Σ_μ (x - c)_μ A_μ(x) = 0`
  (radial / exponential gauge about `c`), then every dilation `A_t = dilateConn t c A` satisfies
  the same identity.  On a Euclidean ball centred at `c` the normal component `A·ν` of the whole
  dilation path therefore vanishes on the boundary sphere, and the Neumann condition for the
  gauges of Uhlenbeck's continuity method becomes homogeneous (`∂_r u = 0`).
-/

open MeasureTheory Filter Topology Set Matrix
open scoped ENNReal NNReal ContDiff

noncomputable section

namespace RenewalGeometry.CubeEdge

open SobolevOpen CriticalGauge UhlenbeckGauge

set_option linter.unusedSectionVars false

/-- A function vanishing on the hyperplane `{x_i = p_i}` near `p` has vanishing tangential
partial derivatives at `p`. -/
theorem pd_eq_zero_of_vanish_hyperplane {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : (Fin 4 → ℝ) → F} {p : Fin 4 → ℝ} {i j : Fin 4} (hij : i ≠ j)
    (hf : DifferentiableAt ℝ f p) (hv : ∀ᶠ x in 𝓝 p, x i = p i → f x = 0) : pd f j p = 0 := by
  set γ : ℝ → Fin 4 → ℝ := fun t => p + t • Pi.single j 1
  have hγ : HasDerivAt γ (Pi.single j 1) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single j (1 : ℝ) : Fin 4 → ℝ)).const_add p
    simpa [γ] using this
  have hγ0 : γ 0 = p := by simp [γ]
  have hcomp : HasDerivAt (f ∘ γ) (fderiv ℝ f p (Pi.single j 1)) 0 := by
    have hf' : HasFDerivAt f (fderiv ℝ f p) (γ 0) := by rw [hγ0]; exact hf.hasFDerivAt
    exact hf'.comp_hasDerivAt 0 hγ
  have hcont : Tendsto γ (𝓝 0) (𝓝 p) := by
    have := hγ.continuousAt.tendsto; rwa [hγ0] at this
  have hev : (f ∘ γ) =ᶠ[𝓝 0] fun _ => (0 : F) := by
    filter_upwards [hcont.eventually hv] with t ht
    apply ht
    simp [γ, Pi.single_apply, Ne.symm hij]
  have h0 : HasDerivAt (f ∘ γ) 0 0 := (hasDerivAt_const (0 : ℝ) (0 : F)).congr_of_eventuallyEq hev
  exact hcomp.unique h0

/-- **The edge obstruction for the Neumann condition on a cube.**  If `B` is differentiable at a
point `p` and its normal components vanish on the two faces through `p` near `p`
(`B_i = 0` on `{x_i = p_i}`, `B_j = 0` on `{x_j = p_j}`, `i ≠ j`), then the curvature component
`F^B_{ij}(p)` vanishes. -/
theorem curvature_edge_zero {m : ℕ} (B : MConn m) {p : Fin 4 → ℝ} {i j : Fin 4} (hij : i ≠ j)
    (hdiff : ∀ ν c e, DifferentiableAt ℝ (fun y => B ν y c e) p)
    (hi : ∀ᶠ x in 𝓝 p, x i = p i → B i x = 0) (hj : ∀ᶠ x in 𝓝 p, x j = p j → B j x = 0)
    (c e : Fin m) : curvatureW (entries B) (entryGrad B) i j c e p = 0 := by
  have h1 : entryGrad B j c e i p = 0 :=
    pd_eq_zero_of_vanish_hyperplane (Ne.symm hij) (hdiff j c e)
      (hj.mono fun x hx hxj => by rw [hx hxj]; rfl)
  have h2 : entryGrad B i c e j p = 0 :=
    pd_eq_zero_of_vanish_hyperplane hij (hdiff i c e)
      (hi.mono fun x hx hxi => by rw [hx hxi]; rfl)
  have h3 : B i p = 0 := hi.self_of_nhds rfl
  simp [curvatureW, entries, h1, h2, h3]

/-- **Dilations preserve the radial gauge** `Σ_μ (x - c)_μ A_μ(x) = 0`. -/
theorem dilateConn_radial {m : ℕ} {A : MConn m} {c : Fin 4 → ℝ}
    (hrad : ∀ x, ∑ μ, ((x μ - c μ : ℝ) : ℂ) • A μ x = 0) (t : ℝ) (y : Fin 4 → ℝ) :
    ∑ μ, ((y μ - c μ : ℝ) : ℂ) • dilateConn t c A μ y = 0 := by
  have h := hrad (c + t • (y - c))
  simp only [dilateConn, smul_smul]
  have e : ∀ μ, ((y μ - c μ : ℝ) : ℂ) * (t : ℂ) =
      (((c + t • (y - c)) μ - c μ : ℝ) : ℂ) := fun μ => by
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, add_sub_cancel_left]
    push_cast; ring
  simp only [e]
  exact h

/-- Non-vacuity of the edge lemma: the zero connection. -/
example (p : Fin 4 → ℝ) : curvatureW (entries (fun _ _ => (0 : Matrix (Fin 1) (Fin 1) ℂ)))
    (entryGrad (fun _ _ => (0 : Matrix (Fin 1) (Fin 1) ℂ))) 0 1 0 0 p = 0 :=
  curvature_edge_zero _ (by decide) (fun _ _ _ => differentiableAt_const _)
    (Eventually.of_forall fun _ _ => rfl) (Eventually.of_forall fun _ _ => rfl) 0 0

end RenewalGeometry.CubeEdge
