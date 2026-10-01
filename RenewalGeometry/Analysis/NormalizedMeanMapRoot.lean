/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.LyapunovSchmidtRangeReduction

/-!
# Uniform chord-Newton roots and the normalized mean map

General machinery behind the four-mean contraction in the proof of
`thm:supp-action-prepared-chart` (emergent-spacetime manuscript), stated in arbitrary real
normed spaces with **explicit constants** (hence uniform over any family with uniform data).

* `chord_root`: a preconditioned chord-Newton / Kantorovich root theorem.  If
  `‖DG(θ) - A‖ ≤ η` on the closed ball `B̄(θ_*, r)`, `‖A⁻¹‖ ≤ M`, `M η < 1` and
  `M ‖G(θ_*)‖ ≤ (1 - M η) r`, then `G` has exactly one zero in `B̄(θ_*, r)`, at distance
  `≤ M ‖G(θ_*)‖ / (1 - M η)` from `θ_*` (the map `θ ↦ θ - A⁻¹G(θ)` is a contraction).
* `ray_second_order`: second-order Taylor control.  If `Θ(0) = 0`, `DΘ(0) = 0` and
  `‖D²Θ(x) - D²Θ(0)‖ ≤ K ‖x‖` on `B(0, ρ)` with `D²Θ(0)` symmetric, then
  `‖DΘ(x) - D²Θ(0)x‖ ≤ K ‖x‖²` and `‖Θ(x) - ½ D²Θ(0)(x, x)‖ ≤ K ‖x‖³`.
* `normalized_ray_bounds`: hence, for `t ≠ 0`, the normalized map
  `𝒬(t, x) = t⁻² Θ(t x)` (`eq:supp-initial-normalized-mean`) and its `x`-derivative
  `t⁻¹ DΘ(t x)` are within `K |t| ‖x‖³`, `K |t| ‖x‖²` of the quadratic jet
  `½ D²Θ(0)(x, x)` and of `D²Θ(0) x`: the extension through `t = 0` by the quadratic jet is
  `C¹`-close to it uniformly, with explicit constants.
* `normalized_mean_root`: the four-mean contraction.  Seed `Z(θ) = Z₀ + Z_l θ` (affine in the
  balancing parameter `θ`), free record `w`.  If the quadratic jet `θ ↦ ½ D²Θ(0)(Z θ, Z θ)` has a
  root `θ_*` whose derivative `A = D²Θ(0)(Z θ_*) ∘ Z_l` is invertible with `‖A⁻¹‖ ≤ M`, then for
  radii satisfying the explicit conditions `chartOK`, every `0 < |t| ≤ t₀` and `‖w‖ ≤ ρ_W`
  admits exactly one `θ ∈ B̄(θ_*, r)` with `Θ(t (Z θ + w)) = 0`.
* `exists_chartOK`: admissible `(r, ρ_W, t₀)` exist and depend only on the constants
  `(K, b, ζ, M, m, ρ)` (`‖D²Θ(0)‖ ≤ b`, `‖Z₀‖, ‖Z_l‖ ≤ ζ`, `‖θ_*‖ ≤ m`).
* `prepared_record_exact_zero`: combined with the range reduction
  (`Analysis/LyapunovSchmidtRangeReduction.lean`): when `Θ` is the mean map of a
  `LyapunovSchmidt.RangeData` and satisfies the hypotheses above, the prepared record
  `I(t, w) = x + R y(x)`, `x = t (Z θ(t, w) + w)` (`eq:supp-initial-prepared-record`) is an
  **exact zero** of the full map, with `‖I(t, w)‖ ≤ C |t|` (`eq:supp-initial-exact-zero`).
* `bordered_right_inverse` (`eq:supp-initial-full-inverse`): if `T = L + B` with `‖B‖ ≤ β` and
  the mean block `P₀ B J` along balancing directions `J ⊂ ker L` is `ε|t|`-close to `t A`
  (`A` invertible), then `T` has a bounded linear right inverse `S` whose range part costs
  `O(1)` and whose mean part costs `O(|t|⁻¹)`; `exists_inv_one_add` is the Neumann inverse used.
* `range_derivative_identities`, `mean_block_bound`: at a record `I = ι x + R y(ι x)`, the
  derivative of the range solution is `Dy = -P DN(I)(ι + R Dy)` (so `‖Dy‖ ≤ 2 p β`,
  `β ≥ ‖DN(I)‖`), the reduced mean derivative is `DΘ = P₀ DN(I)(ι + R Dy)`, and the mean block
  `P₀ DN(I) ι` differs from `DΘ` by at most `‖P₀‖ β a (2 p β)`; this links
  `bordered_right_inverse` to `normalized_ray_bounds`.
-/

open Metric Set Filter
open scoped Topology NNReal

namespace RenewalGeometry
namespace NormalizedMeanRoot

/-! ### A preconditioned chord-Newton root theorem -/

section Chord

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- **Chord-Newton root theorem with explicit constants.**  Let `A : V ≃L W` with
`‖A⁻¹‖ ≤ M`, and let `G` have derivative `DG` on the closed ball `B̄(θ_*, r)` with
`‖DG(θ) - A‖ ≤ η` there.  If `M η < 1` and `M ‖G(θ_*)‖ ≤ (1 - M η) r`, then `G` has a zero
`θ` in the ball, `‖θ - θ_*‖ ≤ M ‖G(θ_*)‖ / (1 - M η)`, and it is the only zero in the ball. -/
theorem chord_root (G : V → W) (DG : V → V →L[ℝ] W) (A : V ≃L[ℝ] W) {θs : V} {r M η : ℝ}
    (hM : ‖(A.symm : W →L[ℝ] V)‖ ≤ M)
    (hG : ∀ θ ∈ closedBall θs r, HasFDerivWithinAt G (DG θ) (closedBall θs r) θ)
    (hD : ∀ θ ∈ closedBall θs r, ‖DG θ - (A : V →L[ℝ] W)‖ ≤ η) (hη : 0 ≤ η)
    (hκ : M * η < 1) (hr : 0 ≤ r) (h0 : M * ‖G θs‖ ≤ (1 - M * η) * r) :
    ∃ θ ∈ closedBall θs r, G θ = 0 ∧ ‖θ - θs‖ ≤ M * ‖G θs‖ / (1 - M * η) ∧
      ∀ θ' ∈ closedBall θs r, G θ' = 0 → θ' = θ := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans hM
  have hκ0 : 0 ≤ M * η := mul_nonneg hM0 hη
  set Φ : V → V := fun θ => θ - A.symm (G θ) with hΦ
  have hΦd : ∀ θ ∈ closedBall θs r, HasFDerivWithinAt Φ
      (ContinuousLinearMap.id ℝ V - (A.symm : W →L[ℝ] V) ∘L DG θ) (closedBall θs r) θ :=
    fun θ hθ => (hasFDerivWithinAt_id θ _).sub
      ((A.symm : W →L[ℝ] V).hasFDerivAt.comp_hasFDerivWithinAt θ (hG θ hθ))
  have hΦb : ∀ θ ∈ closedBall θs r,
      ‖ContinuousLinearMap.id ℝ V - (A.symm : W →L[ℝ] V) ∘L DG θ‖ ≤ M * η := by
    intro θ hθ
    have heq : ContinuousLinearMap.id ℝ V - (A.symm : W →L[ℝ] V) ∘L DG θ =
        (A.symm : W →L[ℝ] V) ∘L ((A : V →L[ℝ] W) - DG θ) := by
      ext v; simp
    rw [heq]
    calc _ ≤ ‖(A.symm : W →L[ℝ] V)‖ * ‖(A : V →L[ℝ] W) - DG θ‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ M * η := mul_le_mul hM (by rw [norm_sub_rev]; exact hD θ hθ) (norm_nonneg _) hM0
  have hlip : ∀ x ∈ closedBall θs r, ∀ y ∈ closedBall θs r, ‖Φ x - Φ y‖ ≤ M * η * ‖x - y‖ :=
    fun x hx y hy => (convex_closedBall θs r).norm_image_sub_le_of_norm_hasFDerivWithin_le
      hΦd hΦb hy hx
  have hΦs : ‖Φ θs - θs‖ ≤ M * ‖G θs‖ := by
    simp only [hΦ, sub_sub_cancel_left, norm_neg]
    exact ((A.symm : W →L[ℝ] V).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right hM (norm_nonneg _))
  have hθs : θs ∈ closedBall θs r := mem_closedBall_self hr
  have hmaps : MapsTo Φ (closedBall θs r) (closedBall θs r) := by
    intro θ hθ
    rw [mem_closedBall, dist_eq_norm]
    have h1 := hlip θ hθ θs hθs
    have h2 : ‖θ - θs‖ ≤ r := by rw [← dist_eq_norm]; exact hθ
    calc ‖Φ θ - θs‖ ≤ ‖Φ θ - Φ θs‖ + ‖Φ θs - θs‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ M * η * r + M * ‖G θs‖ :=
          add_le_add (h1.trans (mul_le_mul_of_nonneg_left h2 hκ0)) hΦs
      _ ≤ r := by linarith
  have hfix_iff : ∀ θ, Φ θ = θ ↔ G θ = 0 := by
    intro θ
    simp only [hΦ, sub_eq_self]
    constructor
    · intro h; simpa using congrArg A h
    · intro h; simp [h]
  have hcontr : ContractingWith (M * η).toNNReal (hmaps.restrict Φ _ _) := by
    refine ⟨?_, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
    · rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hκ0]; simpa using hκ
    · rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm,
        Real.coe_toNNReal _ hκ0]
      exact hlip x x.2 y y.2
  obtain ⟨θ, hθ, hθfix, -⟩ :=
    hcontr.exists_fixedPoint' isClosed_closedBall.isComplete hmaps hθs (edist_ne_top _ _)
  have hθfix' : Φ θ = θ := hθfix
  refine ⟨θ, hθ, (hfix_iff θ).mp hθfix', ?_, ?_⟩
  · have h1 := hlip θ hθ θs hθs
    rw [hθfix'] at h1
    have h3 : ‖θ - θs‖ ≤ M * η * ‖θ - θs‖ + M * ‖G θs‖ := by
      calc ‖θ - θs‖ ≤ ‖θ - Φ θs‖ + ‖Φ θs - θs‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ _ := add_le_add h1 hΦs
    rw [le_div_iff₀ (by linarith)]
    nlinarith
  · intro θ' hθ' hG'
    have h1 := hlip θ' hθ' θ hθ
    rw [(hfix_iff θ').mpr hG', hθfix'] at h1
    have : ‖θ' - θ‖ = 0 := by nlinarith [norm_nonneg (θ' - θ)]
    exact sub_eq_zero.mp (norm_eq_zero.mp this)

end Chord

/-! ### Second-order Taylor control along rays -/

section Taylor

variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- **Second-order Taylor control.**  If `Θ(0) = 0`, `DΘ(0) = 0`, `D²Θ(0)` is symmetric and
`‖D²Θ(x) - D²Θ(0)‖ ≤ K ‖x‖` on `B(0, ρ)`, then on `B(0, ρ)`
`‖DΘ(x) - D²Θ(0) x‖ ≤ K ‖x‖²` and `‖Θ(x) - ½ D²Θ(0)(x, x)‖ ≤ K ‖x‖³`. -/
theorem ray_second_order {Θ : E → W} {DΘ : E → E →L[ℝ] W} {D2 : E → E →L[ℝ] E →L[ℝ] W}
    {ρ K : ℝ} (hΘ : ∀ x ∈ ball (0 : E) ρ, HasFDerivAt Θ (DΘ x) x)
    (hDΘ : ∀ x ∈ ball (0 : E) ρ, HasFDerivAt DΘ (D2 x) x)
    (hL : ∀ x ∈ ball (0 : E) ρ, ‖D2 x - D2 0‖ ≤ K * ‖x‖) (hK : 0 ≤ K)
    (h0 : Θ 0 = 0) (hd0 : DΘ 0 = 0) (hsymm : ∀ u v, D2 0 u v = D2 0 v u) :
    (∀ x ∈ ball (0 : E) ρ, ‖DΘ x - D2 0 x‖ ≤ K * ‖x‖ ^ 2) ∧
      (∀ x ∈ ball (0 : E) ρ, ‖Θ x - (1 / 2 : ℝ) • D2 0 x x‖ ≤ K * ‖x‖ ^ 3) := by
  have h1 : ∀ x ∈ ball (0 : E) ρ, ‖DΘ x - D2 0 x‖ ≤ K * ‖x‖ ^ 2 :=
    (LyapunovSchmidt.taylor_remainder_bounds hDΘ hL hK hd0).2
  refine ⟨h1, fun x hx => ?_⟩
  set g : E → W := fun y => Θ y - (1 / 2 : ℝ) • D2 0 y y with hg
  have hgd : ∀ y ∈ ball (0 : E) ρ, HasFDerivAt g (DΘ y - D2 0 y) y := by
    intro y hy
    have hb := (D2 0).hasFDerivAt_of_bilinear (hasFDerivAt_id y) (hasFDerivAt_id y)
    refine ((hΘ y hy).sub (hb.const_smul (1 / 2 : ℝ))).congr_fderiv ?_
    ext v
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.precompR_apply,
      ContinuousLinearMap.precompL_apply, ContinuousLinearMap.id_apply, id,
      ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply]
    rw [hsymm v y, ← two_smul ℝ, smul_smul]
    norm_num
  have hxρ : ‖x‖ < ρ := mem_ball_zero_iff.mp hx
  have hsub : closedBall (0 : E) ‖x‖ ⊆ ball 0 ρ := closedBall_subset_ball hxρ
  have hbound : ∀ y ∈ closedBall (0 : E) ‖x‖, ‖DΘ y - D2 0 y‖ ≤ K * ‖x‖ ^ 2 := by
    intro y hy
    have hy' : ‖y‖ ≤ ‖x‖ := mem_closedBall_zero_iff.mp hy
    refine (h1 y (hsub hy)).trans ?_
    gcongr
  have hmv := (convex_closedBall (0 : E) ‖x‖).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun y hy => (hgd y (hsub hy)).hasFDerivWithinAt) hbound
    (mem_closedBall_self (norm_nonneg x)) (mem_closedBall_zero_iff.mpr le_rfl)
  have hg0 : g 0 = 0 := by simp [hg, h0]
  rw [hg0, sub_zero, sub_zero] at hmv
  calc ‖Θ x - (1 / 2 : ℝ) • D2 0 x x‖ = ‖g x‖ := rfl
    _ ≤ K * ‖x‖ ^ 2 * ‖x‖ := hmv
    _ = K * ‖x‖ ^ 3 := by ring

/-- **Normalized ray bounds** (`eq:supp-initial-normalized-mean`): under the hypotheses of
`ray_second_order`, for `t ≠ 0` and `|t| ‖x‖ < ρ`, the normalized map `t⁻² Θ(t x)` and its
`x`-derivative `t⁻¹ DΘ(t x)` are within `K |t| ‖x‖³` and `K |t| ‖x‖²` of the quadratic jet
`½ D²Θ(0)(x, x)` and of `D²Θ(0) x`. -/
theorem normalized_ray_bounds {Θ : E → W} {DΘ : E → E →L[ℝ] W}
    {D2 : E → E →L[ℝ] E →L[ℝ] W} {ρ K : ℝ}
    (hΘ : ∀ x ∈ ball (0 : E) ρ, HasFDerivAt Θ (DΘ x) x)
    (hDΘ : ∀ x ∈ ball (0 : E) ρ, HasFDerivAt DΘ (D2 x) x)
    (hL : ∀ x ∈ ball (0 : E) ρ, ‖D2 x - D2 0‖ ≤ K * ‖x‖) (hK : 0 ≤ K)
    (h0 : Θ 0 = 0) (hd0 : DΘ 0 = 0) (hsymm : ∀ u v, D2 0 u v = D2 0 v u)
    {t : ℝ} (ht : t ≠ 0) {x : E} (hx : |t| * ‖x‖ < ρ) :
    ‖(t ^ 2)⁻¹ • Θ (t • x) - (1 / 2 : ℝ) • D2 0 x x‖ ≤ K * |t| * ‖x‖ ^ 3 ∧
      ‖t⁻¹ • DΘ (t • x) - D2 0 x‖ ≤ K * |t| * ‖x‖ ^ 2 := by
  obtain ⟨h1, h2⟩ := ray_second_order hΘ hDΘ hL hK h0 hd0 hsymm
  have htx : t • x ∈ ball (0 : E) ρ := by
    rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs]; exact hx
  have htpos : 0 < |t| := abs_pos.mpr ht
  have hnorm : ‖t • x‖ = |t| * ‖x‖ := by rw [norm_smul, Real.norm_eq_abs]
  constructor
  · have h := h2 _ htx
    have hexp : (1 / 2 : ℝ) • D2 0 (t • x) (t • x) = t ^ 2 • ((1 / 2 : ℝ) • D2 0 x x) := by
      simp only [map_smul, ContinuousLinearMap.smul_apply, smul_smul]
      congr 1; ring
    rw [hexp, hnorm] at h
    have heq : (t ^ 2)⁻¹ • Θ (t • x) - (1 / 2 : ℝ) • D2 0 x x =
        (t ^ 2)⁻¹ • (Θ (t • x) - t ^ 2 • ((1 / 2 : ℝ) • D2 0 x x)) := by
      rw [smul_sub, smul_smul, inv_mul_cancel₀ (pow_ne_zero 2 ht), one_smul]
    rw [heq, norm_smul, Real.norm_eq_abs, abs_inv, abs_pow]
    calc (|t| ^ 2)⁻¹ * ‖Θ (t • x) - t ^ 2 • ((1 / 2 : ℝ) • D2 0 x x)‖
        ≤ (|t| ^ 2)⁻¹ * (K * (|t| * ‖x‖) ^ 3) := by gcongr
      _ = K * |t| * ‖x‖ ^ 3 := by field_simp
  · have h := h1 _ htx
    rw [map_smul, hnorm] at h
    have heq : t⁻¹ • DΘ (t • x) - D2 0 x = t⁻¹ • (DΘ (t • x) - t • D2 0 x) := by
      rw [smul_sub, smul_smul, inv_mul_cancel₀ ht, one_smul]
    rw [heq, norm_smul, Real.norm_eq_abs, abs_inv]
    calc |t|⁻¹ * ‖DΘ (t • x) - t • D2 0 x‖ ≤ |t|⁻¹ * (K * (|t| * ‖x‖) ^ 2) := by gcongr
      _ = K * |t| * ‖x‖ ^ 2 := by field_simp

end Taylor

/-! ### The four-mean contraction for the normalized mean map -/

section Chart

variable {Z V W : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The explicit smallness conditions on the balancing radius `r`, the free-record radius
`ρ_W` and the time scale `t₀` of the normalized mean contraction, in terms of the Lipschitz
constant `K` of `D²Θ`, `b ≥ ‖D²Θ(0)‖`, the seed bound `ζ`, `M ≥ ‖A⁻¹‖`, `m ≥ ‖θ_*‖` and the
radius `ρ` of the ball of control. -/
def chartOK (K b ζ M m ρ r ρW t0 : ℝ) : Prop :=
  0 < r ∧ 0 < ρW ∧ 0 < t0 ∧ t0 * (ζ * (1 + m + r) + ρW) < ρ ∧
    M * (ζ * (K * t0 * (ζ * (1 + m + r) + ρW) ^ 2 + b * (ζ * r + ρW))) ≤ 1 / 2 ∧
    M * (K * t0 * (ζ * (1 + m + r) + ρW) ^ 3 + b * ρW * (ζ * (1 + m) + ρW)) ≤ r / 2

/-- **The four-mean contraction** (proof of `thm:supp-action-prepared-chart`).  Let `Θ` have
the second-order Taylor control of `ray_second_order` on `B(0, ρ)`, with `‖D²Θ(0)‖ ≤ b`.
Let `Z(θ) = Z₀ + Z_l θ` be an affine seed with `‖Z₀‖, ‖Z_l‖ ≤ ζ`, and let `θ_*` (`‖θ_*‖ ≤ m`)
be a root of the quadratic jet, `D²Θ(0)(Z θ_*, Z θ_*) = 0`, whose derivative
`A = D²Θ(0)(Z θ_*) ∘ Z_l` is invertible with `‖A⁻¹‖ ≤ M`.  For radii satisfying `chartOK`,
every `0 < |t| ≤ t₀` and every free record `‖w‖ ≤ ρ_W`, there is exactly one balancing
parameter `θ ∈ B̄(θ_*, r)` with `Θ(t (Z θ + w)) = 0`, i.e. with vanishing normalized mean map
`t⁻² Θ(t (Z θ + w))`. -/
theorem normalized_mean_root {Θ : Z → W} {DΘ : Z → Z →L[ℝ] W}
    {D2 : Z → Z →L[ℝ] Z →L[ℝ] W} {ρ K b ζ M m : ℝ}
    (hΘ : ∀ x ∈ ball (0 : Z) ρ, HasFDerivAt Θ (DΘ x) x)
    (hDΘ : ∀ x ∈ ball (0 : Z) ρ, HasFDerivAt DΘ (D2 x) x)
    (hL : ∀ x ∈ ball (0 : Z) ρ, ‖D2 x - D2 0‖ ≤ K * ‖x‖) (hK : 0 ≤ K)
    (h0 : Θ 0 = 0) (hd0 : DΘ 0 = 0) (hsymm : ∀ u v, D2 0 u v = D2 0 v u)
    (hb : ‖D2 0‖ ≤ b) (Z0 : Z) (Zl : V →L[ℝ] Z) (hZ0 : ‖Z0‖ ≤ ζ) (hZl : ‖Zl‖ ≤ ζ)
    {θs : V} (hθs : ‖θs‖ ≤ m) (hroot : D2 0 (Z0 + Zl θs) (Z0 + Zl θs) = 0)
    (A : V ≃L[ℝ] W) (hA : (A : V →L[ℝ] W) = (D2 0 (Z0 + Zl θs)).comp Zl)
    (hM : ‖(A.symm : W →L[ℝ] V)‖ ≤ M)
    {r ρW t0 : ℝ} (hc : chartOK K b ζ M m ρ r ρW t0)
    {t : ℝ} (ht : t ≠ 0) (htt : |t| ≤ t0) {w : Z} (hw : ‖w‖ ≤ ρW) :
    ∃ θ ∈ closedBall θs r, Θ (t • (Z0 + Zl θ + w)) = 0 ∧
      ∀ θ' ∈ closedBall θs r, Θ (t • (Z0 + Zl θ' + w)) = 0 → θ' = θ := by
  obtain ⟨hr, hρW, ht0, hρ, hη, hg⟩ := hc
  have hζ : 0 ≤ ζ := (norm_nonneg _).trans hZ0
  have hm : 0 ≤ m := (norm_nonneg _).trans hθs
  have hb0 : 0 ≤ b := (ContinuousLinearMap.opNorm_nonneg _).trans hb
  have hM0 : 0 ≤ M := (norm_nonneg _).trans hM
  have hat : 0 ≤ |t| := abs_nonneg t
  set ξ := ζ * (1 + m + r) + ρW with hξ
  have hξ0 : 0 ≤ ξ := by positivity
  set X : V → Z := fun θ => Z0 + Zl θ + w with hX
  set Xs : Z := Z0 + Zl θs with hXs
  have hXnorm : ∀ θ ∈ closedBall θs r, ‖X θ‖ ≤ ξ := by
    intro θ hθ
    have hθ' : ‖θ‖ ≤ m + r := by
      have := norm_le_of_mem_closedBall hθ
      linarith
    calc ‖X θ‖ ≤ ‖Z0‖ + ‖Zl θ‖ + ‖w‖ := norm_add₃_le
      _ ≤ ζ + ζ * (m + r) + ρW := by
          gcongr
          exact (Zl.le_opNorm θ).trans (mul_le_mul hZl hθ' (norm_nonneg _) hζ)
      _ = ξ := by ring
  have htX : ∀ θ ∈ closedBall θs r, |t| * ‖X θ‖ < ρ := by
    intro θ hθ
    calc |t| * ‖X θ‖ ≤ t0 * ξ := mul_le_mul htt (hXnorm θ hθ) (norm_nonneg _) ht0.le
      _ < ρ := hρ
  have htXball : ∀ θ ∈ closedBall θs r, t • X θ ∈ ball (0 : Z) ρ := by
    intro θ hθ
    rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs]; exact htX θ hθ
  set G : V → W := fun θ => (t ^ 2)⁻¹ • Θ (t • X θ) with hG
  set DG : V → V →L[ℝ] W := fun θ => (t⁻¹ • DΘ (t • X θ)).comp Zl with hDG
  have hGd : ∀ θ ∈ closedBall θs r, HasFDerivWithinAt G (DG θ) (closedBall θs r) θ := by
    intro θ hθ
    have hin : HasFDerivAt (fun θ => t • X θ) (t • Zl) θ :=
      ((Zl.hasFDerivAt.const_add Z0).add_const w).const_smul t
    have hcomp := ((hΘ _ (htXball θ hθ)).comp θ hin).const_smul (t ^ 2)⁻¹
    refine (hcomp.congr_fderiv ?_).hasFDerivWithinAt
    ext v
    simp only [hDG, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, map_smul,
      smul_smul]
    congr 1
    field_simp
  -- derivative bound
  have hDb : ∀ θ ∈ closedBall θs r,
      ‖DG θ - (A : V →L[ℝ] W)‖ ≤ ζ * (K * t0 * ξ ^ 2 + b * (ζ * r + ρW)) := by
    intro θ hθ
    have hθr : ‖θ - θs‖ ≤ r := by rw [← dist_eq_norm]; exact hθ
    have heq : DG θ - (A : V →L[ℝ] W) = (t⁻¹ • DΘ (t • X θ) - D2 0 Xs).comp Zl := by
      rw [hA, hDG]; ext v; simp
    have h1 := (normalized_ray_bounds hΘ hDΘ hL hK h0 hd0 hsymm ht (htX θ hθ)).2
    have hXX : X θ - Xs = Zl (θ - θs) + w := by
      simp only [hX, hXs, map_sub]; abel
    have hXXn : ‖X θ - Xs‖ ≤ ζ * r + ρW := by
      rw [hXX]
      calc ‖Zl (θ - θs) + w‖ ≤ ‖Zl (θ - θs)‖ + ‖w‖ := norm_add_le _ _
        _ ≤ ζ * r + ρW := by
            gcongr
            exact (Zl.le_opNorm _).trans (mul_le_mul hZl hθr (norm_nonneg _) hζ)
    have h2 : ‖D2 0 (X θ) - D2 0 Xs‖ ≤ b * (ζ * r + ρW) := by
      rw [← map_sub]
      exact ((D2 0).le_opNorm _).trans (mul_le_mul hb hXXn (norm_nonneg _) hb0)
    have h3 : ‖t⁻¹ • DΘ (t • X θ) - D2 0 Xs‖ ≤ K * t0 * ξ ^ 2 + b * (ζ * r + ρW) := by
      calc ‖t⁻¹ • DΘ (t • X θ) - D2 0 Xs‖
          ≤ ‖t⁻¹ • DΘ (t • X θ) - D2 0 (X θ)‖ + ‖D2 0 (X θ) - D2 0 Xs‖ :=
            norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ K * |t| * ‖X θ‖ ^ 2 + b * (ζ * r + ρW) := add_le_add h1 h2
        _ ≤ K * t0 * ξ ^ 2 + b * (ζ * r + ρW) := by
            gcongr
            exact hXnorm θ hθ
    rw [heq]
    calc ‖(t⁻¹ • DΘ (t • X θ) - D2 0 Xs).comp Zl‖
        ≤ ‖t⁻¹ • DΘ (t • X θ) - D2 0 Xs‖ * ‖Zl‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (K * t0 * ξ ^ 2 + b * (ζ * r + ρW)) * ζ :=
          mul_le_mul h3 hZl (norm_nonneg _) (by positivity)
      _ = ζ * (K * t0 * ξ ^ 2 + b * (ζ * r + ρW)) := by ring
  -- residual at the quadratic root
  have hθsmem : θs ∈ closedBall θs r := mem_closedBall_self hr.le
  have hG0 : ‖G θs‖ ≤ K * t0 * ξ ^ 3 + b * ρW * (ζ * (1 + m) + ρW) := by
    have h1 := (normalized_ray_bounds hΘ hDΘ hL hK h0 hd0 hsymm ht (htX θs hθsmem)).1
    have hXθs : X θs = Xs + w := rfl
    have hexp : (1 / 2 : ℝ) • D2 0 (X θs) (X θs) =
        D2 0 Xs w + (1 / 2 : ℝ) • D2 0 w w := by
      rw [hXθs]
      simp only [map_add, ContinuousLinearMap.add_apply, hroot, hsymm w Xs]
      module
    have hXsn : ‖Xs‖ ≤ ζ * (1 + m) := by
      calc ‖Xs‖ ≤ ‖Z0‖ + ‖Zl θs‖ := norm_add_le _ _
        _ ≤ ζ + ζ * m := by
            gcongr
            exact (Zl.le_opNorm _).trans (mul_le_mul hZl hθs (norm_nonneg _) hζ)
        _ = ζ * (1 + m) := by ring
    have h2 : ‖D2 0 Xs w + (1 / 2 : ℝ) • D2 0 w w‖ ≤ b * ρW * (ζ * (1 + m) + ρW) := by
      have e1 : ‖D2 0 Xs w‖ ≤ b * (ζ * (1 + m)) * ρW := by
        refine ((D2 0).le_opNorm₂ Xs w).trans ?_
        gcongr
      have e2 : ‖(1 / 2 : ℝ) • D2 0 w w‖ ≤ b * ρW * ρW := by
        rw [norm_smul]
        have := (D2 0).le_opNorm₂ w w
        have h3 : ‖D2 0‖ * ‖w‖ * ‖w‖ ≤ b * ρW * ρW := by gcongr
        have : ‖(1 / 2 : ℝ)‖ ≤ 1 := by norm_num
        nlinarith [norm_nonneg (D2 0 w w), norm_nonneg ((1 / 2 : ℝ))]
      calc ‖D2 0 Xs w + (1 / 2 : ℝ) • D2 0 w w‖
          ≤ ‖D2 0 Xs w‖ + ‖(1 / 2 : ℝ) • D2 0 w w‖ := norm_add_le _ _
        _ ≤ b * (ζ * (1 + m)) * ρW + b * ρW * ρW := add_le_add e1 e2
        _ = b * ρW * (ζ * (1 + m) + ρW) := by ring
    have hXθsn := hXnorm θs hθsmem
    calc ‖G θs‖ ≤ ‖G θs - (1 / 2 : ℝ) • D2 0 (X θs) (X θs)‖ +
          ‖(1 / 2 : ℝ) • D2 0 (X θs) (X θs)‖ := norm_le_norm_sub_add _ _
      _ ≤ K * |t| * ‖X θs‖ ^ 3 + b * ρW * (ζ * (1 + m) + ρW) :=
          add_le_add h1 (by rw [hexp]; exact h2)
      _ ≤ K * t0 * ξ ^ 3 + b * ρW * (ζ * (1 + m) + ρW) := by gcongr
  -- apply the chord root theorem
  have hη0 : 0 ≤ ζ * (K * t0 * ξ ^ 2 + b * (ζ * r + ρW)) := by positivity
  have hκ : M * (ζ * (K * t0 * ξ ^ 2 + b * (ζ * r + ρW))) < 1 := by linarith
  have hres : M * ‖G θs‖ ≤ (1 - M * (ζ * (K * t0 * ξ ^ 2 + b * (ζ * r + ρW)))) * r := by
    have h1 := mul_le_mul_of_nonneg_left hG0 hM0
    have h2 := mul_le_mul_of_nonneg_right
      (show (1 : ℝ) / 2 ≤ 1 - M * (ζ * (K * t0 * ξ ^ 2 + b * (ζ * r + ρW))) by linarith) hr.le
    calc M * ‖G θs‖ ≤ M * (K * t0 * ξ ^ 3 + b * ρW * (ζ * (1 + m) + ρW)) := h1
      _ ≤ r / 2 := hg
      _ = 1 / 2 * r := by ring
      _ ≤ _ := h2
  obtain ⟨θ, hθ, hGθ, -, huniq⟩ := chord_root G DG A hM hGd hDb hη0 hκ hr.le hres
  have hiff : ∀ θ', G θ' = 0 ↔ Θ (t • (Z0 + Zl θ' + w)) = 0 := by
    intro θ'
    simp only [hG, hX, smul_eq_zero, inv_eq_zero, pow_eq_zero_iff, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, ht, false_or]
  refine ⟨θ, hθ, (hiff θ).mp hGθ, fun θ' hθ' h' => huniq θ' hθ' ((hiff θ').mpr h')⟩

/-- A choice `0 < x ≤ 1` with `c x ≤ ε`. -/
theorem exists_small {c ε : ℝ} (hc : 0 ≤ c) (hε : 0 < ε) :
    ∃ x : ℝ, 0 < x ∧ x ≤ 1 ∧ c * x ≤ ε := by
  refine ⟨min 1 (ε / (c + 1)), lt_min one_pos (by positivity), min_le_left _ _, ?_⟩
  have h1 : min 1 (ε / (c + 1)) ≤ ε / (c + 1) := min_le_right _ _
  have h2 : 0 < min 1 (ε / (c + 1)) := lt_min one_pos (by positivity)
  calc c * min 1 (ε / (c + 1)) ≤ (c + 1) * min 1 (ε / (c + 1)) := by nlinarith
    _ ≤ (c + 1) * (ε / (c + 1)) := mul_le_mul_of_nonneg_left h1 (by linarith)
    _ = ε := by field_simp

/-- **Admissible radii exist and depend only on the constants** `(K, b, ζ, M, m, ρ)`; in
particular they are uniform over any family (e.g. indexed by the cutoff) with uniform
constants. -/
theorem exists_chartOK {K b ζ M m ρ : ℝ} (hK : 0 ≤ K) (hb : 0 ≤ b) (hζ : 0 ≤ ζ) (hM : 0 ≤ M)
    (hm : 0 ≤ m) (hρ : 0 < ρ) : ∃ r ρW t0, chartOK K b ζ M m ρ r ρW t0 := by
  set Ξ := ζ * (2 + m) + 1 with hΞ
  have hΞ1 : 1 ≤ Ξ := by have := mul_nonneg hζ (by linarith : (0 : ℝ) ≤ 2 + m); linarith
  have hΞ0 : 0 ≤ Ξ := by linarith
  obtain ⟨r, hr0, hr1, hr⟩ := exists_small (c := M * b * ζ ^ 2) (ε := 1 / 8) (by positivity)
    (by norm_num)
  obtain ⟨ρW, hρW0, hρW1, hρW⟩ := exists_small (c := M * ζ * b + M * b * (ζ * (1 + m) + 1))
    (ε := min (1 / 8) (r / 4)) (by positivity) (lt_min (by norm_num) (by positivity))
  obtain ⟨t0, ht00, -, ht0⟩ := exists_small (c := M * ζ * K * Ξ ^ 2 + M * K * Ξ ^ 3 + Ξ)
    (ε := min (min (1 / 4) (r / 4)) (ρ / 2)) (by positivity)
    (lt_min (lt_min (by norm_num) (by positivity)) (by positivity))
  set ξ := ζ * (1 + m + r) + ρW with hξ
  have hξ0 : 0 ≤ ξ := by positivity
  have hξΞ : ξ ≤ Ξ := by
    have : ζ * (1 + m + r) ≤ ζ * (2 + m) := mul_le_mul_of_nonneg_left (by linarith) hζ
    linarith
  have hεt := ht0
  have hεt1 : (M * ζ * K * Ξ ^ 2 + M * K * Ξ ^ 3 + Ξ) * t0 ≤ 1 / 4 :=
    hεt.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hεt2 : (M * ζ * K * Ξ ^ 2 + M * K * Ξ ^ 3 + Ξ) * t0 ≤ r / 4 :=
    hεt.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hεt3 : (M * ζ * K * Ξ ^ 2 + M * K * Ξ ^ 3 + Ξ) * t0 ≤ ρ / 2 :=
    hεt.trans (min_le_right _ _)
  have hερ1 : (M * ζ * b + M * b * (ζ * (1 + m) + 1)) * ρW ≤ 1 / 8 :=
    hρW.trans (min_le_left _ _)
  have hερ2 : (M * ζ * b + M * b * (ζ * (1 + m) + 1)) * ρW ≤ r / 4 :=
    hρW.trans (min_le_right _ _)
  have hA1 : 0 ≤ M * ζ * K * Ξ ^ 2 := by positivity
  have hA2 : 0 ≤ M * K * Ξ ^ 3 := by positivity
  have hB1 : 0 ≤ M * ζ * b := by positivity
  have hB2 : 0 ≤ M * b * (ζ * (1 + m) + 1) := by positivity
  have hξ2 : ξ ^ 2 ≤ Ξ ^ 2 := pow_le_pow_left₀ hξ0 hξΞ 2
  have hξ3 : ξ ^ 3 ≤ Ξ ^ 3 := pow_le_pow_left₀ hξ0 hξΞ 3
  set c1 := M * ζ * K * Ξ ^ 2 + M * K * Ξ ^ 3 + Ξ with hc1
  set c2 := M * ζ * b + M * b * (ζ * (1 + m) + 1) with hc2
  have hsplit1 : c1 * t0 = M * ζ * K * Ξ ^ 2 * t0 + M * K * Ξ ^ 3 * t0 + Ξ * t0 := by ring
  have hsplit2 : c2 * ρW = M * ζ * b * ρW + M * b * (ζ * (1 + m) + 1) * ρW := by ring
  have p1 : 0 ≤ M * ζ * K * Ξ ^ 2 * t0 := by positivity
  have p2 : 0 ≤ M * K * Ξ ^ 3 * t0 := by positivity
  have p3 : 0 ≤ Ξ * t0 := by positivity
  have q1 : 0 ≤ M * ζ * b * ρW := by positivity
  have q2 : 0 ≤ M * b * (ζ * (1 + m) + 1) * ρW := by positivity
  refine ⟨r, ρW, t0, hr0, hρW0, ht00, ?_, ?_, ?_⟩
  · calc t0 * ξ ≤ t0 * Ξ := mul_le_mul_of_nonneg_left hξΞ ht00.le
      _ = Ξ * t0 := by ring
      _ ≤ c1 * t0 := by rw [hsplit1]; linarith
      _ ≤ ρ / 2 := hεt3
      _ < ρ := by linarith
  · have e1 : M * ζ * K * t0 * ξ ^ 2 ≤ M * ζ * K * Ξ ^ 2 * t0 := by
      calc M * ζ * K * t0 * ξ ^ 2 = (M * ζ * K * t0) * ξ ^ 2 := by ring
        _ ≤ (M * ζ * K * t0) * Ξ ^ 2 :=
            mul_le_mul_of_nonneg_left hξ2 (by positivity)
        _ = M * ζ * K * Ξ ^ 2 * t0 := by ring
    have e2 : M * ζ * K * Ξ ^ 2 * t0 ≤ 1 / 4 := by linarith
    have e3 : M * b * ζ ^ 2 * r ≤ 1 / 8 := hr
    have e4 : M * ζ * b * ρW ≤ 1 / 8 := by linarith
    calc M * (ζ * (K * t0 * ξ ^ 2 + b * (ζ * r + ρW)))
        = M * ζ * K * t0 * ξ ^ 2 + M * b * ζ ^ 2 * r + M * ζ * b * ρW := by ring
      _ ≤ 1 / 4 + 1 / 8 + 1 / 8 := by linarith
      _ = 1 / 2 := by norm_num
  · have e1 : M * K * t0 * ξ ^ 3 ≤ M * K * Ξ ^ 3 * t0 := by
      calc M * K * t0 * ξ ^ 3 = (M * K * t0) * ξ ^ 3 := by ring
        _ ≤ (M * K * t0) * Ξ ^ 3 := mul_le_mul_of_nonneg_left hξ3 (by positivity)
        _ = M * K * Ξ ^ 3 * t0 := by ring
    have e2 : M * K * Ξ ^ 3 * t0 ≤ r / 4 := by linarith
    have e3 : M * b * ρW * (ζ * (1 + m) + ρW) ≤ M * b * (ζ * (1 + m) + 1) * ρW := by
      have h1 : ζ * (1 + m) + ρW ≤ ζ * (1 + m) + 1 := by linarith
      calc M * b * ρW * (ζ * (1 + m) + ρW) ≤ M * b * ρW * (ζ * (1 + m) + 1) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = M * b * (ζ * (1 + m) + 1) * ρW := by ring
    have e4 : M * b * (ζ * (1 + m) + 1) * ρW ≤ r / 4 := by linarith
    calc M * (K * t0 * ξ ^ 3 + b * ρW * (ζ * (1 + m) + ρW))
        = M * K * t0 * ξ ^ 3 + M * b * ρW * (ζ * (1 + m) + ρW) := by ring
      _ ≤ r / 4 + r / 4 := by linarith
      _ = r / 2 := by ring

end Chart

/-! ### Assembly with the range reduction: exact prepared records -/

section Assembly

open LyapunovSchmidt

variable {E F V W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

omit [CompleteSpace V] in
/-- Size of the seeded free record: `‖Z₀ + Z_l θ + w‖ ≤ ζ (1 + m + r) + ρ_W` on `B̄(θ_*, r)`. -/
theorem norm_seed_le {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z] {Z0 : Z}
    {Zl : V →L[ℝ] Z} {ζ m r ρW : ℝ} (hZ0 : ‖Z0‖ ≤ ζ) (hZl : ‖Zl‖ ≤ ζ) {θs θ : V}
    (hθs : ‖θs‖ ≤ m) (hθ : θ ∈ closedBall θs r) {w : Z} (hw : ‖w‖ ≤ ρW) :
    ‖Z0 + Zl θ + w‖ ≤ ζ * (1 + m + r) + ρW := by
  have hζ : 0 ≤ ζ := (norm_nonneg _).trans hZ0
  have hθ' : ‖θ‖ ≤ m + r := by
    have := norm_le_of_mem_closedBall hθ
    linarith
  calc ‖Z0 + Zl θ + w‖ ≤ ‖Z0‖ + ‖Zl θ‖ + ‖w‖ := norm_add₃_le
    _ ≤ ζ + ζ * (m + r) + ρW := by
        gcongr
        exact (Zl.le_opNorm θ).trans (mul_le_mul hZl hθ' (norm_nonneg _) hζ)
    _ = ζ * (1 + m + r) + ρW := by ring

/-- **Exact finite preparation, abstract form** (`thm:supp-action-prepared-chart`, first
assertions: `eq:supp-initial-prepared-record`, `eq:supp-initial-exact-zero`).  Let `D` be a
range-reduction packet (`LyapunovSchmidt.RangeData`) with admissible radii `σ, δ`, and let the
free records be parametrized by a normed space `Z` through `ι : Z → ker L` with `‖ι z‖ ≤ ‖z‖`.
Suppose the mean map `Θ = D.meanMap ∘ ι` has the second-order Taylor control of
`ray_second_order` on `B(0, ρ)`, `ρ ≤ δ`, and that its quadratic jet on the affine seed
`Z(θ) = Z₀ + Z_l θ` has a root `θ_*` with invertible derivative.  Then for radii satisfying
`chartOK`, every `0 < |t| ≤ t₀` and every free record `‖w‖ ≤ ρ_W` there is `θ ∈ B̄(θ_*, r)`
such that the prepared record `I = x + R y(x)`, `x = ι(t (Z θ + w))`, is an exact zero of the
full map `𝒞 = L + N`, with `‖I‖ ≤ (1 + 2 a p C δ) (ζ (1 + m + r) + ρ_W) |t|`; and `θ` is the
only balancing parameter in `B̄(θ_*, r)` whose prepared record is an exact zero. -/
theorem prepared_record_exact_zero {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (D : RangeData E F W) {σ δ : ℝ} (hr : radiiOK D.a D.p D.C D.ρ σ δ)
    (ι : Z →L[ℝ] E) (hιL : ∀ z, D.L (ι z) = 0) (hιn : ∀ z, ‖ι z‖ ≤ ‖z‖)
    {DΘ : Z → Z →L[ℝ] W} {D2 : Z → Z →L[ℝ] Z →L[ℝ] W} {ρ K b ζ M m : ℝ}
    (hρδ : ρ ≤ δ)
    (hΘ : ∀ x ∈ ball (0 : Z) ρ, HasFDerivAt (fun z => D.meanMap σ δ (ι z)) (DΘ x) x)
    (hDΘ : ∀ x ∈ ball (0 : Z) ρ, HasFDerivAt DΘ (D2 x) x)
    (hL : ∀ x ∈ ball (0 : Z) ρ, ‖D2 x - D2 0‖ ≤ K * ‖x‖) (hK : 0 ≤ K)
    (hd0 : DΘ 0 = 0) (hsymm : ∀ u v, D2 0 u v = D2 0 v u) (hb : ‖D2 0‖ ≤ b)
    (Z0 : Z) (Zl : V →L[ℝ] Z) (hZ0 : ‖Z0‖ ≤ ζ) (hZl : ‖Zl‖ ≤ ζ)
    {θs : V} (hθs : ‖θs‖ ≤ m) (hroot : D2 0 (Z0 + Zl θs) (Z0 + Zl θs) = 0)
    (A : V ≃L[ℝ] W) (hA : (A : V →L[ℝ] W) = (D2 0 (Z0 + Zl θs)).comp Zl)
    (hM : ‖(A.symm : W →L[ℝ] V)‖ ≤ M)
    {r ρW t0 : ℝ} (hc : chartOK K b ζ M m ρ r ρW t0)
    {t : ℝ} (ht : t ≠ 0) (htt : |t| ≤ t0) {w : Z} (hw : ‖w‖ ≤ ρW) :
    ∃ θ ∈ closedBall θs r,
      D.full (ι (t • (Z0 + Zl θ + w)) + D.R (D.sol σ δ (ι (t • (Z0 + Zl θ + w))))) = 0 ∧
      ‖ι (t • (Z0 + Zl θ + w)) + D.R (D.sol σ δ (ι (t • (Z0 + Zl θ + w))))‖ ≤
        (1 + 2 * D.a * D.p * D.C * δ) * ((ζ * (1 + m + r) + ρW) * |t|) ∧
      ∀ θ' ∈ closedBall θs r,
        D.full (ι (t • (Z0 + Zl θ' + w)) + D.R (D.sol σ δ (ι (t • (Z0 + Zl θ' + w))))) = 0 →
          θ' = θ := by
  have h0 : (fun z => D.meanMap σ δ (ι z)) 0 = 0 := by
    simpa using D.meanMap_zero hr
  obtain ⟨θ, hθ, hzero, huniq⟩ := normalized_mean_root (Θ := fun z => D.meanMap σ δ (ι z))
    hΘ hDΘ hL hK h0 hd0 hsymm hb Z0 Zl hZ0 hZl hθs hroot A hA hM hc ht htt hw
  obtain ⟨-, -, ht0, hρ, -, -⟩ := hc
  -- every seeded point lies in the `δ`-ball of the kernel
  have hpt : ∀ θ' ∈ closedBall θs r,
      ‖ι (t • (Z0 + Zl θ' + w))‖ ≤ (ζ * (1 + m + r) + ρW) * |t| ∧
      ‖ι (t • (Z0 + Zl θ' + w))‖ ≤ δ := by
    intro θ' hθ'
    have hn := norm_seed_le hZ0 hZl hθs hθ' hw
    have hξ0 : 0 ≤ ζ * (1 + m + r) + ρW := (norm_nonneg _).trans hn
    have h1 : ‖ι (t • (Z0 + Zl θ' + w))‖ ≤ (ζ * (1 + m + r) + ρW) * |t| := by
      refine (hιn _).trans ?_
      rw [norm_smul, Real.norm_eq_abs, mul_comm]
      exact mul_le_mul_of_nonneg_right hn (abs_nonneg t)
    refine ⟨h1, ?_⟩
    calc ‖ι (t • (Z0 + Zl θ' + w))‖ ≤ (ζ * (1 + m + r) + ρW) * |t| := h1
      _ ≤ (ζ * (1 + m + r) + ρW) * t0 := mul_le_mul_of_nonneg_left htt hξ0
      _ = t0 * (ζ * (1 + m + r) + ρW) := by ring
      _ ≤ δ := (hρ.trans_le hρδ).le
  obtain ⟨hxn, hxδ⟩ := hpt θ hθ
  have hxL := hιL (t • (Z0 + Zl θ + w))
  refine ⟨θ, hθ, D.full_zero_of_meanMap_eq_zero hr hxL hxδ hzero, ?_, ?_⟩
  · refine (D.norm_record_le hr hxL hxδ).trans ?_
    have h1 : 0 ≤ 1 + 2 * D.a * D.p * D.C * δ := by
      have : 0 ≤ δ := hr.2.1
      have := mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
        D.a_nonneg) D.p_nonneg) D.hC) this
      linarith
    exact mul_le_mul_of_nonneg_left hxn h1
  · intro θ' hθ' hfull
    refine huniq θ' hθ' ?_
    show D.P0 (D.full _) = 0
    rw [hfull, map_zero]

end Assembly

/-! ### The bordered right inverse with the `|t|⁻¹` mean term -/

section RightInverse

open LyapunovSchmidt

variable {E F V W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

omit [CompleteSpace F] [CompleteSpace V] in
/-- Neumann inverse of a perturbation of the identity: if `‖x‖ ≤ ½` then `1 + x` has a
two-sided inverse of norm `≤ 2`. -/
theorem exists_inv_one_add {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (x : X →L[ℝ] X) (hx : ‖x‖ ≤ 1 / 2) :
    ∃ y : X →L[ℝ] X, (1 + x) * y = 1 ∧ y * (1 + x) = 1 ∧ ‖y‖ ≤ 2 := by
  have hnx : ‖-x‖ = ‖x‖ := norm_neg x
  have hlt : ‖-x‖ < 1 := by rw [hnx]; linarith
  refine ⟨∑' n : ℕ, (-x) ^ n, ?_, ?_, ?_⟩
  · have := mul_neg_geom_series (-x) hlt
    rwa [sub_neg_eq_add] at this
  · have := geom_series_mul_neg (-x) hlt
    rwa [sub_neg_eq_add] at this
  · have h1 := tsum_geometric_le_of_norm_lt_one (-x) hlt
    have h2 : ‖(1 : X →L[ℝ] X)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
    have h4 : (1 - ‖-x‖)⁻¹ ≤ 2 := by
      have h5 : (1 : ℝ) / 2 ≤ 1 - ‖-x‖ := by rw [hnx]; linarith
      calc (1 - ‖-x‖)⁻¹ ≤ (1 / 2)⁻¹ := inv_anti₀ (by norm_num) h5
        _ = 2 := by norm_num
    linarith

omit [CompleteSpace F] [CompleteSpace V] in
/-- Operator-norm bound for an application, in the form used in chains of estimates. -/
theorem norm_apply_le_mul {X Y : Type*} [SeminormedAddCommGroup X] [NormedSpace ℝ X]
    [SeminormedAddCommGroup Y] [NormedSpace ℝ Y] (T : X →L[ℝ] Y) {a c : ℝ} {x : X}
    (hT : ‖T‖ ≤ a) (hx : ‖x‖ ≤ c) (ha : 0 ≤ a) : ‖T x‖ ≤ a * c :=
  (T.le_opNorm _).trans (mul_le_mul hT hx (norm_nonneg _) ha)

/-- **Bordered right inverse with a small parameter** (`eq:supp-initial-full-inverse`).
Let `D` be a range packet (`L R = I` on `{P y = y}`, `P L = L`, `P₀ L = 0`, `(P, P₀)` jointly
injective) with moreover `P₀ P = 0`.  Let `T = L + B` with `‖B‖ ≤ β`, and let `J : V → ker L`
(balancing directions) be such that the mean block `P₀ B J` is `ε|t|`-close to `t A` with `A`
invertible, `‖A⁻¹‖ ≤ M`, `M ε ≤ ½`.  If the bordered coupling is small,
`p β a + p β j (2M/|t|) ‖P₀‖ β a ≤ ½`, then `T` has a bounded linear right inverse `S` with
`‖S f‖ ≤ a·2(‖P f‖ + γ ‖P₀ f‖) + j (2M/|t|)(‖P₀ f‖ + ‖P₀‖ β a · 2(‖P f‖ + γ ‖P₀ f‖))`,
`γ = p β j (2M/|t|)`: the range block costs `O(1)` and the mean block costs `O(|t|⁻¹)`. -/
theorem bordered_right_inverse (D : RangeData E F W) (hP0P : ∀ w, D.P0 (D.P w) = 0)
    (B : E →L[ℝ] F) {β : ℝ} (hB : ‖B‖ ≤ β) (J : V →L[ℝ] E) {j : ℝ} (hJ : ‖J‖ ≤ j)
    (hLJ : ∀ v, D.L (J v) = 0) (A : V ≃L[ℝ] W) {M ε : ℝ}
    (hM : ‖(A.symm : W →L[ℝ] V)‖ ≤ M) {t : ℝ} (ht : t ≠ 0)
    (hE : ‖D.P0 ∘L B ∘L J - t • (A : V →L[ℝ] W)‖ ≤ ε * |t|) (hMε : M * ε ≤ 1 / 2)
    (hq : D.p * β * D.a + D.p * β * j * (2 * M / |t|) * (‖D.P0‖ * β * D.a) ≤ 1 / 2) :
    ∃ S : F →L[ℝ] E, (∀ f, D.L (S f) + B (S f) = f) ∧
      ∀ f, ‖S f‖ ≤ D.a * (2 * (‖D.P f‖ + D.p * β * j * (2 * M / |t|) * ‖D.P0 f‖)) +
        j * (2 * M / |t| * (‖D.P0 f‖ + ‖D.P0‖ * β * D.a *
          (2 * (‖D.P f‖ + D.p * β * j * (2 * M / |t|) * ‖D.P0 f‖)))) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans hM
  have hβ0 : 0 ≤ β := (norm_nonneg _).trans hB
  have hj0 : 0 ≤ j := (norm_nonneg _).trans hJ
  have hat : 0 < |t| := abs_pos.mpr ht
  have ha0 := D.a_nonneg
  have hp0 := D.p_nonneg
  set Ai : W →L[ℝ] V := (A.symm : W →L[ℝ] V) with hAi
  set At : V →L[ℝ] W := D.P0 ∘L B ∘L J with hAt
  -- invert the mean block
  set X : V →L[ℝ] V := t⁻¹ • (Ai ∘L (At - t • (A : V →L[ℝ] W))) with hX
  have hXn : ‖X‖ ≤ 1 / 2 := by
    calc ‖X‖ = ‖t⁻¹‖ * ‖Ai ∘L (At - t • (A : V →L[ℝ] W))‖ := by rw [hX, norm_smul]
      _ ≤ |t|⁻¹ * (M * (ε * |t|)) := by
          rw [Real.norm_eq_abs, abs_inv]
          gcongr
          exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
            (mul_le_mul hM hE (norm_nonneg _) hM0)
      _ = M * ε := by field_simp
      _ ≤ 1 / 2 := hMε
  obtain ⟨Y, hY1, -, hYn⟩ := exists_inv_one_add X hXn
  set Ati : W →L[ℝ] V := Y ∘L (t⁻¹ • Ai) with hAti
  have hfact : ∀ v, At v = t • A ((1 + X) v) := by
    intro v
    have h : A ((1 + X) v) = A v + t⁻¹ • (At v - t • A v) := by
      simp only [hX, hAi, ContinuousLinearMap.add_apply, ContinuousLinearMap.one_apply,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.sub_apply, map_add, map_smul, ContinuousLinearEquiv.coe_coe,
        ContinuousLinearEquiv.apply_symm_apply]
    rw [h, smul_add, smul_smul, mul_inv_cancel₀ ht, one_smul]
    abel
  have hAtAti : ∀ w, At (Ati w) = w := by
    intro w
    rw [hfact]
    have h1 : (1 + X) (Y (t⁻¹ • Ai w)) = t⁻¹ • Ai w := by
      have := congrArg (fun T : V →L[ℝ] V => T (t⁻¹ • Ai w)) hY1
      simpa [ContinuousLinearMap.mul_apply] using this
    simp only [hAti, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply]
    rw [h1, map_smul, smul_smul, mul_inv_cancel₀ ht, one_smul, hAi,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
  have hAtin : ‖Ati‖ ≤ 2 * M / |t| := by
    calc ‖Ati‖ ≤ ‖Y‖ * ‖t⁻¹ • Ai‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 2 * (|t|⁻¹ * M) := by
          gcongr
          rw [norm_smul, Real.norm_eq_abs, abs_inv]; gcongr
      _ = 2 * M / |t| := by field_simp
  -- the mean-zero block
  have hsubn : ‖D.M.subtypeL‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => by simp
  set Bm : D.M →L[ℝ] D.M := D.Pc ∘L B ∘L D.R ∘L D.M.subtypeL -
      D.Pc ∘L B ∘L J ∘L Ati ∘L D.P0 ∘L B ∘L D.R ∘L D.M.subtypeL with hBm
  have hBmn : ‖Bm‖ ≤ 1 / 2 := by
    have e1 : ‖D.Pc ∘L B ∘L D.R ∘L D.M.subtypeL‖ ≤ D.p * β * D.a := by
      calc _ ≤ ‖D.Pc‖ * (‖B‖ * (‖D.R‖ * ‖D.M.subtypeL‖)) := by
            refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
            gcongr
            refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
            gcongr
            exact ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ D.p * (β * (D.a * 1)) := by
            gcongr
            · exact D.norm_Pc_le
            · exact D.ha
        _ = D.p * β * D.a := by ring
    have e2 : ‖D.Pc ∘L B ∘L J ∘L Ati ∘L D.P0 ∘L B ∘L D.R ∘L D.M.subtypeL‖ ≤
        D.p * β * j * (2 * M / |t|) * (‖D.P0‖ * β * D.a) := by
      calc _ ≤ ‖D.Pc‖ * (‖B‖ * (‖J‖ * (‖Ati‖ * (‖D.P0‖ * (‖B‖ * (‖D.R‖ *
            ‖D.M.subtypeL‖)))))) := by
            refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_; gcongr
            refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_; gcongr
            refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_; gcongr
            refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_; gcongr
            refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_; gcongr
            refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_; gcongr
            exact ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ D.p * (β * (j * (2 * M / |t| * (‖D.P0‖ * (β * (D.a * 1)))))) := by
            gcongr
            · exact D.norm_Pc_le
            · exact D.ha
        _ = D.p * β * j * (2 * M / |t|) * (‖D.P0‖ * β * D.a) := by ring
    rw [hBm]
    exact ((norm_sub_le (E := D.M →L[ℝ] D.M) _ _).trans (add_le_add e1 e2)).trans hq
  obtain ⟨U, hU1, -, hUn⟩ := exists_inv_one_add Bm hBmn
  set gmap : F →L[ℝ] D.M := U ∘L (D.Pc - D.Pc ∘L B ∘L J ∘L Ati ∘L D.P0) with hgmap
  set ηmap : F →L[ℝ] V := Ati ∘L (D.P0 - D.P0 ∘L B ∘L D.R ∘L D.M.subtypeL ∘L gmap) with hηmap
  refine ⟨D.R ∘L D.M.subtypeL ∘L gmap + J ∘L ηmap, ?_, ?_⟩
  · intro f
    set g : D.M := gmap f with hg
    set η : V := ηmap f with hη
    have hgP : D.P (g : F) = g := D.mem_M.mp g.2
    -- the mean-zero equation
    have hUg : (1 + Bm) g = (D.Pc - D.Pc ∘L B ∘L J ∘L Ati ∘L D.P0) f := by
      have := congrArg (fun T : D.M →L[ℝ] D.M => T ((D.Pc - D.Pc ∘L B ∘L J ∘L Ati ∘L D.P0) f)) hU1
      simpa [ContinuousLinearMap.mul_apply, hg, hgmap] using this
    have hstar : (g : F) + D.P (B (D.R g)) - D.P (B (J (Ati (D.P0 (B (D.R g)))))) =
        D.P f - D.P (B (J (Ati (D.P0 f)))) := by
      have := congrArg (fun m : D.M => (m : F)) hUg
      simpa [hBm, RangeData.coe_Pc, ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
        sub_eq_add_neg, add_assoc] using this
    -- the mean equation
    have hη' : D.P0 (B (J η)) = D.P0 f - D.P0 (B (D.R g)) := by
      have := hAtAti (D.P0 f - D.P0 (B (D.R g)))
      simpa [hAt, hη, hηmap, hg] using this
    set w := D.L ((D.R ∘L D.M.subtypeL ∘L gmap + J ∘L ηmap) f) +
      B ((D.R ∘L D.M.subtypeL ∘L gmap + J ∘L ηmap) f) - f with hw
    have hSf : (D.R ∘L D.M.subtypeL ∘L gmap + J ∘L ηmap) f = D.R g + J η := rfl
    have hLS : D.L (D.R g + J η) = g := by
      rw [map_add, D.hLR _ hgP, hLJ, add_zero]
    have hPw : D.P w = 0 := by
      have hηexp : D.P (B (J η)) = D.P (B (J (Ati (D.P0 f)))) -
          D.P (B (J (Ati (D.P0 (B (D.R g)))))) := by
        simp only [hη, hηmap, ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
          map_sub, hg]
        rfl
      rw [hw, hSf, hLS, map_sub, map_add, map_add, map_add, hgP, hηexp]
      rw [← sub_eq_zero] at hstar
      rw [← hstar]
      abel
    have hP0w : D.P0 w = 0 := by
      rw [hw, hSf, hLS, map_sub, map_add, map_add, map_add, hη']
      have : D.P0 (g : F) = 0 := by rw [← hgP]; exact hP0P _
      rw [this]
      abel
    exact sub_eq_zero.mp (D.hsplit w hPw hP0w)
  · intro f
    have h2M : 0 ≤ 2 * M / |t| := by positivity
    have hr2 : ‖D.Pc (B (J (Ati (D.P0 f))))‖ ≤
        D.p * (β * (j * (2 * M / |t| * ‖D.P0 f‖))) :=
      norm_apply_le_mul _ D.norm_Pc_le (norm_apply_le_mul _ hB (norm_apply_le_mul _ hJ (norm_apply_le_mul _ hAtin le_rfl h2M) hj0) hβ0) hp0
    have hr : ‖(D.Pc - D.Pc ∘L B ∘L J ∘L Ati ∘L D.P0) f‖ ≤
        ‖D.P f‖ + D.p * β * j * (2 * M / |t|) * ‖D.P0 f‖ := by
      have e : (D.Pc - D.Pc ∘L B ∘L J ∘L Ati ∘L D.P0) f =
          D.Pc f - D.Pc (B (J (Ati (D.P0 f)))) := rfl
      rw [e]
      refine (norm_sub_le _ _).trans (add_le_add (le_of_eq ?_) (hr2.trans (le_of_eq (by ring))))
      rw [Submodule.coe_norm, RangeData.coe_Pc]
    have hgn' : ‖gmap f‖ ≤ 2 * (‖D.P f‖ + D.p * β * j * (2 * M / |t|) * ‖D.P0 f‖) :=
      norm_apply_le_mul U hUn hr (by norm_num)
    have hgn : ‖((gmap f : D.M) : F)‖ ≤ 2 * (‖D.P f‖ + D.p * β * j * (2 * M / |t|) * ‖D.P0 f‖) := by
      rw [← Submodule.coe_norm]; exact hgn'
    set G := 2 * (‖D.P f‖ + D.p * β * j * (2 * M / |t|) * ‖D.P0 f‖) with hG
    have hG0 : 0 ≤ G := (norm_nonneg _).trans hgn
    have hη1 : ‖D.P0 (B (D.R ((gmap f : D.M) : F)))‖ ≤ ‖D.P0‖ * (β * (D.a * G)) :=
      norm_apply_le_mul _ le_rfl (norm_apply_le_mul _ hB (norm_apply_le_mul _ D.ha hgn ha0) hβ0) (norm_nonneg _)
    have hηn : ‖ηmap f‖ ≤ 2 * M / |t| * (‖D.P0 f‖ + ‖D.P0‖ * β * D.a * G) := by
      have e : ηmap f = Ati (D.P0 f - D.P0 (B (D.R ((gmap f : D.M) : F)))) := rfl
      rw [e]
      refine norm_apply_le_mul _ hAtin ((norm_sub_le _ _).trans (add_le_add le_rfl ?_)) h2M
      exact hη1.trans (le_of_eq (by ring))
    have e : (D.R ∘L D.M.subtypeL ∘L gmap + J ∘L ηmap) f =
        D.R ((gmap f : D.M) : F) + J (ηmap f) := rfl
    rw [e]
    calc ‖D.R ((gmap f : D.M) : F) + J (ηmap f)‖
        ≤ ‖D.R ((gmap f : D.M) : F)‖ + ‖J (ηmap f)‖ := norm_add_le _ _
      _ ≤ D.a * G + j * (2 * M / |t| * (‖D.P0 f‖ + ‖D.P0‖ * β * D.a * G)) :=
          add_le_add (norm_apply_le_mul _ D.ha hgn ha0) (norm_apply_le_mul _ hJ hηn hj0)

end RightInverse

/-! ### Derivatives of the reduced maps at a prepared record -/

section Link

open LyapunovSchmidt

variable {E F W Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- **Derivative identities of the range reduction.**  Let `ι : Z → ker L` and let
`I = ι x + R y(ι x)` be the record over a free point with `‖ι x‖ < δ`.  If `z ↦ y(ι z)` is
differentiable at `x` with derivative `Dy` and the mean map `z ↦ Θ(ι z)` has derivative `DΘ`,
then `Dy = -P DN(I)(ι + R Dy)` and `DΘ = P₀ DN(I)(ι + R Dy)`. -/
theorem range_derivative_identities (D : RangeData E F W) {σ δ : ℝ}
    (hr : radiiOK D.a D.p D.C D.ρ σ δ) (ι : Z →L[ℝ] E) (hιL : ∀ z, D.L (ι z) = 0) {x : Z}
    (hx : ‖ι x‖ < δ) {Dy : Z →L[ℝ] F} (hDy : HasFDerivAt (fun z => D.sol σ δ (ι z)) Dy x)
    {DΘ : Z →L[ℝ] W} (hΘ : HasFDerivAt (fun z => D.meanMap σ δ (ι z)) DΘ x) :
    Dy = -(D.P ∘L D.DN (ι x + D.R (D.sol σ δ (ι x))) ∘L (ι + D.R ∘L Dy)) ∧
      DΘ = D.P0 ∘L D.DN (ι x + D.R (D.sol σ δ (ι x))) ∘L (ι + D.R ∘L Dy) := by
  set I := ι x + D.R (D.sol σ δ (ι x)) with hI
  have hsolx := D.sol_spec hr (hιL x) hx.le
  have hIball : I ∈ Metric.ball (0 : E) D.ρ :=
    mem_ball_zero_iff.mpr ((D.norm_arg_le hx.le hsolx.1).trans_lt hr.2.2.1)
  have hrec : HasFDerivAt (fun z => ι z + D.R (D.sol σ δ (ι z))) (ι + D.R ∘L Dy) x :=
    ι.hasFDerivAt.add (D.R.hasFDerivAt.comp x hDy)
  have hNc : HasFDerivAt (fun z => D.N (ι z + D.R (D.sol σ δ (ι z))))
      (D.DN I ∘L (ι + D.R ∘L Dy)) x := (D.hN I hIball).comp x hrec
  refine ⟨?_, ?_⟩
  · -- differentiate the fixed-point identity `y = -P N(ι z + R y)` near `x`
    have hev : (fun z => D.sol σ δ (ι z)) =ᶠ[𝓝 x]
        (fun z => -(D.P (D.N (ι z + D.R (D.sol σ δ (ι z)))))) := by
      have hopen : IsOpen {z : Z | ‖ι z‖ < δ} :=
        isOpen_lt (continuous_norm.comp ι.continuous) continuous_const
      filter_upwards [hopen.mem_nhds hx] with z hz
      exact (D.T_sol hr (hιL z) (le_of_lt hz)).symm
    have h2 : HasFDerivAt (fun z => D.sol σ δ (ι z))
        (-(D.P ∘L (D.DN I ∘L (ι + D.R ∘L Dy)))) x :=
      ((D.P.hasFDerivAt.comp x hNc).neg).congr_of_eventuallyEq hev
    exact hDy.unique h2
  · have heq : (fun z => D.meanMap σ δ (ι z)) =
        (fun z => D.P0 (D.N (ι z + D.R (D.sol σ δ (ι z))))) := by
      funext z; exact D.meanMap_eq σ δ (ι z)
    have h2 : HasFDerivAt (fun z => D.meanMap σ δ (ι z)) (D.P0 ∘L (D.DN I ∘L (ι + D.R ∘L Dy)))
        x := by
      rw [heq]; exact D.P0.hasFDerivAt.comp x hNc
    exact hΘ.unique h2

/-- **The mean block at a prepared record is the reduced mean derivative up to `O(β²)`.**
With `β ≥ ‖DN(I)‖`, `‖ι‖ ≤ 1` and `p β a ≤ ½`: `‖Dy‖ ≤ 2 p β` and
`‖P₀ DN(I) ι - DΘ‖ ≤ ‖P₀‖ β a (2 p β)`.  Combined with `normalized_ray_bounds`
(`DΘ(t X) Z_l ≈ t A`) this is the hypothesis `hE` of `bordered_right_inverse` for
`B = DN(I)`, `J = ι Z_l`. -/
theorem mean_block_bound (D : RangeData E F W) {σ δ : ℝ}
    (hr : radiiOK D.a D.p D.C D.ρ σ δ) (ι : Z →L[ℝ] E) (hιL : ∀ z, D.L (ι z) = 0)
    (hι1 : ‖ι‖ ≤ 1) {x : Z} (hx : ‖ι x‖ < δ) {Dy : Z →L[ℝ] F}
    (hDy : HasFDerivAt (fun z => D.sol σ δ (ι z)) Dy x)
    {DΘ : Z →L[ℝ] W} (hΘ : HasFDerivAt (fun z => D.meanMap σ δ (ι z)) DΘ x) {β : ℝ}
    (hβ : ‖D.DN (ι x + D.R (D.sol σ δ (ι x)))‖ ≤ β) (hsmall : D.p * β * D.a ≤ 1 / 2) :
    ‖Dy‖ ≤ 2 * D.p * β ∧
      ‖D.P0 ∘L D.DN (ι x + D.R (D.sol σ δ (ι x))) ∘L ι - DΘ‖ ≤
        ‖D.P0‖ * β * D.a * (2 * D.p * β) := by
  obtain ⟨h1, h2⟩ := range_derivative_identities D hr ι hιL hx hDy hΘ
  set B := D.DN (ι x + D.R (D.sol σ δ (ι x))) with hB
  have hβ0 : 0 ≤ β := (norm_nonneg _).trans hβ
  have hp0 := D.p_nonneg
  have ha0 := D.a_nonneg
  have hDy : ‖Dy‖ ≤ D.p * β * (1 + D.a * ‖Dy‖) := by
    calc ‖Dy‖ = ‖D.P ∘L B ∘L (ι + D.R ∘L Dy)‖ := by
          rw [congrArg norm h1, norm_neg]
      _ ≤ ‖D.P‖ * (‖B‖ * ‖ι + D.R ∘L Dy‖) := by
          refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
          gcongr
          exact ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ D.p * (β * (1 + D.a * ‖Dy‖)) := by
          gcongr
          · exact D.hp
          · refine (norm_add_le _ _).trans (add_le_add hι1 ?_)
            exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (by gcongr; exact D.ha)
      _ = D.p * β * (1 + D.a * ‖Dy‖) := by ring
  have hDyb : ‖Dy‖ ≤ 2 * D.p * β := by
    have : ‖Dy‖ ≤ D.p * β + (D.p * β * D.a) * ‖Dy‖ := by nlinarith
    have h3 : (D.p * β * D.a) * ‖Dy‖ ≤ 1 / 2 * ‖Dy‖ :=
      mul_le_mul_of_nonneg_right hsmall (norm_nonneg _)
    linarith
  refine ⟨hDyb, ?_⟩
  have heq : D.P0 ∘L B ∘L ι - DΘ = -(D.P0 ∘L B ∘L D.R ∘L Dy) := by
    rw [h2]; ext v; simp
  rw [heq, norm_neg]
  calc ‖D.P0 ∘L B ∘L D.R ∘L Dy‖ ≤ ‖D.P0‖ * (‖B‖ * (‖D.R‖ * ‖Dy‖)) := by
        refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
        gcongr
        refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
        gcongr
        exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖D.P0‖ * (β * (D.a * (2 * D.p * β))) := by
        gcongr
        exact D.ha
    _ = ‖D.P0‖ * β * D.a * (2 * D.p * β) := by ring

end Link

end NormalizedMeanRoot
end RenewalGeometry
