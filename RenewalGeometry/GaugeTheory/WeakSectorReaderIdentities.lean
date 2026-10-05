/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Exact finite identities of the gauge-covariant weak-sector reader (`app:gauge-reader`)

Clause-level infrastructure for `cor:gauge-robust-reader` (Einstein–SM action-closure manuscript,
"Gauge-covariant realization of the weak-sector reader").  On a grid (any additive group `X`
with unit steps `e_i`) with unitary represented links `ρ(U_i(x))` (linear isometries of a real
normed fibre `V`):

* `covShift`, `covDiff` (`eq:gauge-covdiff`): `T_i^U F(x) = ρ(U_i(x)) F(x + e_i)`,
  `D_i^U F = h⁻¹(T_i^U F - F)`.
* `abs_kato_le` (**discrete Kato inequality `eq:gauge-Kato`**):
  `|δ_i |F|(x)| ≤ |D_i^U F(x)|`.
* `normalizedLink`, `normalizedJet` (`eq:gauge-normalized`): for a unitary algebraic frame `Q_x`,
  `W_i(x) = Q_x⁻¹ ρ(U_i(x)) Q_{x+e_i}`, `a_i = h⁻¹(W_i - I)`, `J = Q⁻¹ G`.
* `fwdDiff_normalizedJet` and `norm_shift_eq_frame` (**the exact identities `eq:gauge-closed`**):
  `δ_i J_I = J_{iI} - a_i T_i J_I` and `|H_{x+e_i}| = | |H_x| e_1 + h J_i(x) |` when
  `Q_x⁻¹ H_x = |H_x| e_1`.
* `temporal_gauge_link_eq_one` (**`eq:gauge-temporal`**): the causal gauge
  `g_{j+1} = g_j W_0(j)`, `g_0 = 1`, sets the transformed temporal links `g_j W_0(j) g_{j+1}⁻¹` to
  the identity.
-/

noncomputable section

namespace RenewalGeometry.WeakReader

variable {X : Type*} [AddCommGroup X] {ι : Type*} (e : ι → X)
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The covariant shift `T_i^U F(x) = ρ(U_i(x)) F(x + e_i)` (`eq:gauge-covdiff`). -/
def covShift (ρU : X → ι → V →L[ℝ] V) (i : ι) (F : X → V) (x : X) : V :=
  ρU x i (F (x + e i))

/-- The covariant difference `D_i^U F = h⁻¹(T_i^U F - F)` (`eq:gauge-covdiff`). -/
def covDiff (h : ℝ) (ρU : X → ι → V →L[ℝ] V) (i : ι) (F : X → V) (x : X) : V :=
  h⁻¹ • (covShift e ρU i F x - F x)

/-- **Discrete Kato inequality** `eq:gauge-Kato`: for unitary links,
`|(|F(x + e_i)| - |F(x)|)/h| ≤ |D_i^U F(x)|`. -/
theorem abs_kato_le {h : ℝ} (hh : 0 < h) {ρU : X → ι → V →L[ℝ] V}
    (hiso : ∀ x i (v : V), ‖ρU x i v‖ = ‖v‖) (i : ι) (F : X → V) (x : X) :
    |(‖F (x + e i)‖ - ‖F x‖) / h| ≤ ‖covDiff e h ρU i F x‖ := by
  rw [covDiff, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hh, abs_div, abs_of_pos hh,
    div_eq_inv_mul]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hh.le)
  rw [← hiso x i (F (x + e i))]
  exact abs_norm_sub_norm_le _ _

/-- The normalized link `W_i(x) = Q_x⁻¹ ρ(U_i(x)) Q_{x+e_i}` (`eq:gauge-normalized`). -/
def normalizedLink (Q : X → V ≃ₗᵢ[ℝ] V) (ρU : X → ι → V →L[ℝ] V) (i : ι) (x : X) : V →L[ℝ] V :=
  ((Q x).symm.toContinuousLinearEquiv : V →L[ℝ] V).comp
    ((ρU x i).comp ((Q (x + e i)).toContinuousLinearEquiv : V →L[ℝ] V))

/-- The normalized jet `J = Q⁻¹ G`. -/
def normalizedJet (Q : X → V ≃ₗᵢ[ℝ] V) (G : X → V) (x : X) : V := (Q x).symm (G x)

/-- **`eq:gauge-closed`, first identity**: with `a_i = h⁻¹(W_i - I)`,
`δ_i J(x) = J_{i}(x) - a_i(x) J(x + e_i)`, where `J = Q⁻¹ G` and `J_i = Q⁻¹ D_i^U G`. -/
theorem fwdDiff_normalizedJet {h : ℝ} (hh : h ≠ 0) (Q : X → V ≃ₗᵢ[ℝ] V)
    (ρU : X → ι → V →L[ℝ] V) (i : ι) (G : X → V) (x : X) :
    h⁻¹ • (normalizedJet Q G (x + e i) - normalizedJet Q G x) =
      normalizedJet Q (covDiff e h ρU i G) x -
        (h⁻¹ • (normalizedLink e Q ρU i x - 1)) (normalizedJet Q G (x + e i)) := by
  simp only [normalizedJet, covDiff, covShift, normalizedLink, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply,
    map_smul, map_sub]
  simp only [ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    LinearIsometryEquiv.apply_symm_apply]
  rw [smul_sub, smul_sub, smul_sub]
  abel

/-- **`eq:gauge-closed`, second identity**: if the algebraic frame sends `e_1` to `H_x/|H_x|`,
i.e. `Q_x⁻¹ H_x = |H_x| e_1`, then `|H_{x+e_i}| = | |H_x| e_1 + h J_i(x) |` with
`J_i = Q⁻¹ D_i^U H`. -/
theorem norm_shift_eq_frame {h : ℝ} (hh : h ≠ 0) (Q : X → V ≃ₗᵢ[ℝ] V)
    {ρU : X → ι → V →L[ℝ] V} (hiso : ∀ x i (v : V), ‖ρU x i v‖ = ‖v‖) (i : ι) (H : X → V)
    (x : X) (e₁ : V) (hQ : (Q x).symm (H x) = ‖H x‖ • e₁) :
    ‖H (x + e i)‖ = ‖‖H x‖ • e₁ + h • normalizedJet Q (covDiff e h ρU i H) x‖ := by
  have : ‖H x‖ • e₁ + h • normalizedJet Q (covDiff e h ρU i H) x =
      (Q x).symm (ρU x i (H (x + e i))) := by
    simp only [normalizedJet, covDiff, covShift, map_smul, map_sub, smul_smul,
      mul_inv_cancel₀ hh, one_smul, ← hQ]
    abel
  rw [this, LinearIsometryEquiv.norm_map, hiso]

/-- **`eq:gauge-temporal`**: the causal gauge `g_0 = 1`, `g_{j+1} = g_j W_0(j)` sets every
transformed temporal link `g_j W_0(j) g_{j+1}⁻¹` to the identity (any group). -/
theorem temporal_gauge_link_eq_one {G : Type*} [Group G] (W₀ : ℕ → G) (g : ℕ → G)
    (hg : ∀ j, g (j + 1) = g j * W₀ j) (j : ℕ) : g j * W₀ j * (g (j + 1))⁻¹ = 1 := by
  rw [hg, mul_inv_cancel]

end RenewalGeometry.WeakReader
