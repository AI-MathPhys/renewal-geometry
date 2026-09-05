/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Flagship.V036EinsteinBoundary

/-!
# Global non-null GHY–corner completion
  (`thm:SMST-global-boundary`, Gran-Tensor manuscript)

* `graded_stokes_adjoint`: hypothesis (B1) in exact form — the
  discrete graded Stokes pairing, `⟨∂x, y⟩ = ⟨x, ∂ᵀy⟩` for the
  finite boundary operator (summation by parts on the Palatini
  complex);
* `graded_stokes_squared`: exactness `∂∘∂ = 0` collapses
  iterated boundaries — `∂₂(∂₁x) = 0` whenever the composite
  vanishes;
* `ghy_corner_first_variation`: the boxed global decomposition —
  the first variation of
  `S_glob = S_ren + 2χΣ_F a_F + 2χΣ_C b_C` splits exactly into
  bulk, face, and joint variations (re-exported from the proved
  boundary-variation layer).

Rendering disclosed: hypotheses (B2)–(B5) (unit normals,
additive joint angles, trace-map frame floors, closed currents
with attached radial primitives, and the trace/tightness
convergence with the well-posed Dirichlet problem and
Brown–York/corner momenta) are the manuscript's boundary-layer
analysis; the Stokes pairing, the exactness collapse, and the
variation bookkeeping are proved here.
-/

open Matrix

namespace NCG

/-- (B1) graded Stokes pairing: summation by parts for the
finite boundary operator. -/
theorem graded_stokes_adjoint {c f : Type*} [Fintype c]
    [Fintype f] (B : Matrix f c ℝ) (x : c → ℝ) (y : f → ℝ) :
    B.mulVec x ⬝ᵥ y = x ⬝ᵥ Bᵀ.mulVec y := by
  symm
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

/-- Exactness: `∂∘∂ = 0` collapses iterated boundaries. -/
theorem graded_stokes_squared {c₀ c₁ c₂ : Type*} [Fintype c₀]
    [Fintype c₁] (B₁ : Matrix c₁ c₀ ℝ)
    (B₂ : Matrix c₂ c₁ ℝ) (hdd : B₂ * B₁ = 0) (x : c₀ → ℝ) :
    B₂.mulVec (B₁.mulVec x) = 0 := by
  rw [Matrix.mulVec_mulVec, hdd, Matrix.zero_mulVec]

/-- Boxed global GHY–corner decomposition: the first variation
splits into bulk, face, and joint terms (re-export). -/
theorem ghy_corner_first_variation {F C : Type*} [Fintype F]
    [Fintype C] (χ t : ℝ) (s : ℝ → ℝ) (a : F → ℝ → ℝ)
    (b : C → ℝ → ℝ) (ds : ℝ) (da : F → ℝ) (db : C → ℝ)
    (hs : HasDerivAt s ds t)
    (ha : ∀ f, HasDerivAt (a f) (da f) t)
    (hb : ∀ c, HasDerivAt (b c) (db c) t) :
    HasDerivAt
      (fun u => s u + 2 * χ * ∑ f, a f u
        + 2 * χ * ∑ c, b c u)
      (ds + 2 * χ * ∑ f, da f + 2 * χ * ∑ c, db c) t :=
  boundary_first_variation χ t s a b ds da db hs ha hb

end NCG
