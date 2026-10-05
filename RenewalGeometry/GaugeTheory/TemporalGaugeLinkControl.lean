/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Spatial links in the causal temporal gauge (`eq:gauge-temporal`, zeroth order)

Clause-level infrastructure for `cor:gauge-robust-reader` (Einstein–SM action-closure manuscript,
`app:gauge-reader`: "the algebraic Higgs frame need not be temporal gauge; starting with
`g_{0,x} = I` and defining causally `g_{j+1,x} = g_{j,x} W_0(j,x)` sets the transformed temporal
links to the identity; ... discrete Grönwall shows that ... controls the transformed spatial
links").

For links `W_0(j, x)` (temporal) and `W_i(j, x)` (spatial, `x ↦ x + e_i` written `sh`) in any
group, the causal gauge `g_{j+1} = g_j W_0(j)` transforms the spatial links to
`W'_i(j, x) = g_j(x) W_i(j, x) g_j(x + e_i)⁻¹`; then

* `temporal_spatial_link_step` (**exact recursion**): `W'_i(j+1) = (g_j P_{0i}(j) g_j⁻¹) W'_i(j)`,
  with the temporal–spatial plaquette `P_{0i}(j,x) = W_0(j,x) W_i(j+1,x) W_0(j,x+e_i)⁻¹ W_i(j,x)⁻¹`;
* `size_temporal_spatial_link_le` (**discrete Grönwall at order zero**): for every
  subadditive conjugation-invariant size `δ` (e.g. `δ(U) = ‖U - 1‖` on the unitary group of a
  C*-algebra, `unitary_size_*`), `δ(W'_i(J)) ≤ δ(W_i(0)) + Σ_{j<J} δ(P_{0i}(j))` — the transformed
  spatial links are controlled by the initial links and the time-integrated plaquette deviation,
  with no smallness of the original links and no derivative of the frame.

Higher orders (the finite-difference hierarchy of `h⁻¹ log W'_i` through order `s`) are not
formalised here.
-/

noncomputable section

namespace RenewalGeometry.TemporalGaugeLinks

variable {G X : Type*} [Group G]

/-- The causally transformed spatial link `W'(j, x) = g_j(x) W(j, x) g_j(sh x)⁻¹`. -/
def transLink (g : ℕ → X → G) (W : ℕ → X → G) (sh : X → X) (j : ℕ) (x : X) : G :=
  g j x * W j x * (g j (sh x))⁻¹

/-- The temporal–spatial plaquette `P(j, x) = W_0(j,x) W(j+1,x) W_0(j,sh x)⁻¹ W(j,x)⁻¹`. -/
def plaquette (W₀ W : ℕ → X → G) (sh : X → X) (j : ℕ) (x : X) : G :=
  W₀ j x * W (j + 1) x * (W₀ j (sh x))⁻¹ * (W j x)⁻¹

/-- **Exact recursion of the transformed spatial links in the causal temporal gauge**:
`W'(j+1) = (g_j P(j) g_j⁻¹) W'(j)`. -/
theorem temporal_spatial_link_step (W₀ W : ℕ → X → G) (sh : X → X) (g : ℕ → X → G)
    (hg : ∀ j x, g (j + 1) x = g j x * W₀ j x) (j : ℕ) (x : X) :
    transLink g W sh (j + 1) x =
      (g j x * plaquette W₀ W sh j x * (g j x)⁻¹) * transLink g W sh j x := by
  simp only [transLink, plaquette, hg]
  group

/-- **Discrete Grönwall at order zero**: for a subadditive conjugation-invariant size `δ`, the
transformed spatial links satisfy `δ(W'(J)) ≤ δ(W(0)) + Σ_{j<J} δ(P(j))` (`g_0 = 1`). -/
theorem size_temporal_spatial_link_le (W₀ W : ℕ → X → G) (sh : X → X) (g : ℕ → X → G)
    (hg0 : ∀ x, g 0 x = 1) (hg : ∀ j x, g (j + 1) x = g j x * W₀ j x) (δ : G → ℝ)
    (hδ : ∀ a b, δ (a * b) ≤ δ a + δ b) (hconj : ∀ a b, δ (a * b * a⁻¹) = δ b) (x : X) :
    ∀ J : ℕ, δ (transLink g W sh J x) ≤ δ (W 0 x) + ∑ j ∈ Finset.range J, δ (plaquette W₀ W sh j x)
  | 0 => by simp [transLink, hg0]
  | J + 1 => by
    rw [temporal_spatial_link_step W₀ W sh g hg J x, Finset.sum_range_succ]
    have h1 := hδ (g J x * plaquette W₀ W sh J x * (g J x)⁻¹) (transLink g W sh J x)
    rw [hconj] at h1
    have h2 := size_temporal_spatial_link_le W₀ W sh g hg0 hg δ hδ hconj x J
    linarith

/-! ### The unitary size `δ(U) = ‖U - 1‖` -/

section Unitary

variable {E : Type*} [NormedRing E] [StarRing E] [CStarRing E]

theorem coe_mul_unitary (A B : unitary E) : ((A * B : unitary E) : E) = (A : E) * (B : E) := rfl

/-- The size `δ(U) = ‖U - 1‖` of a unitary. -/
def unitarySize (U : unitary E) : ℝ := ‖(U : E) - 1‖

theorem unitarySize_mul_le (U V : unitary E) :
    unitarySize (U * V) ≤ unitarySize U + unitarySize V := by
  unfold unitarySize
  have e : ((U * V : unitary E) : E) - 1 = (U : E) * ((V : E) - 1) + ((U : E) - 1) := by
    rw [coe_mul_unitary, mul_sub, mul_one]; abel
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [CStarRing.norm_coe_unitary_mul]
  linarith

theorem unitarySize_conj (U V : unitary E) : unitarySize (U * V * U⁻¹) = unitarySize V := by
  unfold unitarySize
  have e : ((U * V * U⁻¹ : unitary E) : E) - 1 = (U : E) * ((V : E) - 1) * ((U⁻¹ : unitary E) : E) := by
    have h1 : (U : E) * ((U⁻¹ : unitary E) : E) = 1 := by
      rw [← coe_mul_unitary, mul_inv_cancel]; rfl
    rw [coe_mul_unitary, coe_mul_unitary, mul_sub, sub_mul, mul_one, h1]
  rw [e, CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul]

/-- **The causal temporal gauge for unitary links** (e.g. `SU(2)` in `M₂(ℂ)`):
`‖W'(J) - 1‖ ≤ ‖W(0) - 1‖ + Σ_{j<J} ‖P(j) - 1‖`. -/
theorem unitary_temporal_spatial_link_le (W₀ W : ℕ → X → unitary E) (sh : X → X)
    (g : ℕ → X → unitary E) (hg0 : ∀ x, g 0 x = 1) (hg : ∀ j x, g (j + 1) x = g j x * W₀ j x)
    (x : X) (J : ℕ) :
    ‖((transLink g W sh J x : unitary E) : E) - 1‖ ≤ ‖((W 0 x : unitary E) : E) - 1‖ +
      ∑ j ∈ Finset.range J, ‖((plaquette W₀ W sh j x : unitary E) : E) - 1‖ :=
  size_temporal_spatial_link_le W₀ W sh g hg0 hg unitarySize unitarySize_mul_le
    unitarySize_conj x J

end Unitary

/-- Non-vacuity of the unitary hypotheses: the trivial gauge (`g = 1`, `W₀ = 1`). -/
example {E : Type*} [NormedRing E] [StarRing E] [CStarRing E] (W : ℕ → ℤ → unitary E) (J : ℕ) :
    ‖((transLink (fun _ _ => 1) W (· + 1) J 0 : unitary E) : E) - 1‖ ≤
      ‖((W 0 0 : unitary E) : E) - 1‖ + ∑ j ∈ Finset.range J,
        ‖((plaquette (fun _ _ => 1) W (· + 1) j 0 : unitary E) : E) - 1‖ :=
  unitary_temporal_spatial_link_le _ W _ _ (fun _ => rfl) (fun _ _ => by simp) 0 J

end RenewalGeometry.TemporalGaugeLinks
