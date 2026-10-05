/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Initial-layer obstruction and the tangency functional: generic parts

Emergent-spacetime manuscript, `thm:supp-exact-initial-layer` and
`thm:supp-exact-upstream-deformation` (subsection "Dynamical tangency").

**Time-rescaling limit.**  The proof of `thm:supp-exact-initial-layer` rescales `t = a³ s`, and the
rescaled finite-dimensional vector field converges on every fixed `s`-interval to a linear
displacement system.  `ExactInitialLayer.rescaled_tendsto` proves the underlying continuous
dependence: if `x_a' = G_a(x_a)`, `x_0' = G_0(x_0)` with `G_0` Lipschitz,
`‖G_a - G_0‖ ≤ η(a) → 0` along the trajectory and `‖x_a(0) - x_0(0)‖ ≤ δ(a) → 0`, then
`x_a → x_0` uniformly on `[0, S]` (Grönwall); `ExactInitialLayer.rescaled_tendsto_displacement` is
the linear-displacement case `G_0 ≡ v`, `x_0(s) = x_0(0) + s v`.

**Contradiction argument.**  `ExactInitialLayer.no_fixed_time_linear_bound`: if the normalized
curvature `a⁻¹ R(a, a³ s)` converges for every `s ≥ 0` to an unbounded limit `ψ(s)` (a nonzero
limiting slope: `ExactInitialLayer.unbounded_of_slope`), then no `T, C, a₀ > 0` give
`sup_{0 ≤ t ≤ T} ‖R(a, t)‖ ≤ C a` for all `0 < a < a₀` (`eq:supp-exact-no-linear-fixed-time`).
`ExactInitialLayer.layer_bound` is the positive half: uniform convergence on `[0,S]` gives
`‖R(a, a³ s)‖ ≤ C a` on the shrinking layer `0 ≤ t ≤ a³ S`.
`ExactInitialLayer.initial_layer_obstruction` assembles the two: rescaled convergence to a linear
displacement `x₀ + s v`, a readout `a⁻¹R(a, a³s) = Φ(x_a(s)) + o(1)` with `Φ v ≠ 0` (the nonzero
limiting curvature slope) exclude any fixed-time linear bound.

**Tangency functional.**  With the first Poisson matrix `𝕂₁(Y)` linear in the canonical jet, the
derivative `Dd_{2,W}(Y)[Z, ν]` of the quadratic weak drift bilinear in `(Y, Z)`, and linear maps
`F₁`, `G`, the functional `eq:supp-exact-tangency-functional`
`Δ_ν(Y, ℓ) = Dd_{2,W}(Y)[F₁Y + Gℓ, ν] + 𝕂₁(F₁Y + Gℓ)[ν, ℓ]` is a quadratic form in `(Y, ℓ)`
(`ExactInitialLayer.TangencyData.delta_smul`); along a line it is exactly
`Δ(Y + εZ, ℓ + εm) = Δ(Y, ℓ) + ε DΔ(Y,ℓ)[Z,m] + ε² Δ(Z, m)` with the polarized derivative
`DΔ` (`delta_line`, `hasDerivAt_delta_line`) — "its derivative is obtained exactly by
polarization"; Poisson-nullity to first order along `Z` persists exactly
(`weakNull_line`); and `DΔ ≠ 0` makes the obstruction non-invariant under the deformation
(`deformable_of_polarized_ne_zero`).  The nonzero rational value of `DΔ_{ν⋄}(Y,ℓ)[Z₂,m₂]` is a
finite evaluation on data (`𝕂₁`, `d_{2,W}`, `F₁`, `G`, `𝓛`, `Y`, `ℓ`, `Z₂`, `m₂`, `ν⋄`) that the
manuscript does not write; it is not formalized.
-/

open Filter Set Metric Topology
open scoped NNReal

namespace RenewalGeometry
namespace ExactInitialLayer

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- `gronwallBound δ K ε S → 0` as `δ, ε → 0`. -/
theorem tendsto_gronwallBound {ι : Type*} {l : Filter ι} {δ η : ι → ℝ} (K S : ℝ)
    (hδ : Tendsto δ l (𝓝 0)) (hη : Tendsto η l (𝓝 0)) :
    Tendsto (fun i => gronwallBound (δ i) K (η i) S) l (𝓝 0) := by
  by_cases hK : K = 0
  · subst hK
    simp only [gronwallBound_K0]
    simpa using hδ.add (hη.mul_const S)
  · simp only [gronwallBound_of_K_ne_0 hK]
    have := (hδ.mul_const (Real.exp (K * S))).add
      ((hη.div_const K).mul_const (Real.exp (K * S) - 1))
    simpa using this


/-- **Uniform convergence of rescaled trajectories** (continuous dependence on the amplitude). -/
theorem rescaled_tendsto {ι : Type*} {l : Filter ι} {G : ι → E → E} {G₀ : E → E} {K : ℝ≥0}
    (hG₀ : LipschitzWith K G₀) {x : ι → ℝ → E} {x₀ : ℝ → E} {S : ℝ}
    (hx : ∀ i, ContinuousOn (x i) (Icc 0 S))
    (hxd : ∀ i, ∀ s ∈ Ico 0 S, HasDerivWithinAt (x i) (G i (x i s)) (Ici s) s)
    (hx₀ : ContinuousOn x₀ (Icc 0 S))
    (hx₀d : ∀ s ∈ Ico 0 S, HasDerivWithinAt x₀ (G₀ (x₀ s)) (Ici s) s)
    {η δ : ι → ℝ} (hη0 : ∀ i, 0 ≤ η i)
    (hη : ∀ i, ∀ s ∈ Ico 0 S, ‖G i (x i s) - G₀ (x i s)‖ ≤ η i)
    (hδ : ∀ i, ‖x i 0 - x₀ 0‖ ≤ δ i) (hηt : Tendsto η l (𝓝 0)) (hδt : Tendsto δ l (𝓝 0)) :
    ∀ ε > 0, ∀ᶠ i in l, ∀ s ∈ Icc 0 S, ‖x i s - x₀ s‖ ≤ ε := by
  intro ε hε
  have hlim := tendsto_gronwallBound (K : ℝ) S hδt hηt
  filter_upwards [hlim.eventually (gt_mem_nhds hε)] with i hi s hs
  have hδ0 : 0 ≤ δ i := (norm_nonneg _).trans (hδ i)
  have hb := dist_le_of_approx_trajectories_ODE (v := fun _ => G₀) (K := K) (δ := δ i)
    (εf := η i) (εg := 0) (fun _ => hG₀)
    (hx i) (hxd i) (fun s hs => by rw [dist_eq_norm]; exact hη i s hs) hx₀ hx₀d
    (fun s _ => (dist_self _).le) (by rw [dist_eq_norm]; exact hδ i) s hs
  rw [add_zero, sub_zero, dist_eq_norm] at hb
  exact hb.trans ((gronwallBound_mono hδ0 (hη0 i) K.2 hs.2).trans hi.le)

/-- **Linear displacement limit**: if the limiting rescaled field is the constant `v`, the
rescaled trajectories converge uniformly on `[0, S]` to `x₀ + s v`. -/
theorem rescaled_tendsto_displacement {ι : Type*} {l : Filter ι} {G : ι → E → E} (v x₀ : E)
    {x : ι → ℝ → E} {S : ℝ} (hx : ∀ i, ContinuousOn (x i) (Icc 0 S))
    (hxd : ∀ i, ∀ s ∈ Ico 0 S, HasDerivWithinAt (x i) (G i (x i s)) (Ici s) s)
    {η δ : ι → ℝ} (hη0 : ∀ i, 0 ≤ η i) (hη : ∀ i, ∀ s ∈ Ico 0 S, ‖G i (x i s) - v‖ ≤ η i)
    (hδ : ∀ i, ‖x i 0 - x₀‖ ≤ δ i) (hηt : Tendsto η l (𝓝 0)) (hδt : Tendsto δ l (𝓝 0)) :
    ∀ ε > 0, ∀ᶠ i in l, ∀ s ∈ Icc 0 S, ‖x i s - (x₀ + s • v)‖ ≤ ε := by
  have hlin : ∀ s, HasDerivAt (fun s : ℝ => x₀ + s • v) v s := fun s => by
    simpa using ((hasDerivAt_id s).smul_const v).const_add x₀
  exact rescaled_tendsto (G₀ := fun _ => v) (K := 0) (LipschitzWith.const v) hx hxd
    (by fun_prop) (fun s _ => (hlin s).hasDerivWithinAt) hη0 hη
    (fun i => by simpa using hδ i) hηt hδt

/-- A nonzero limiting slope makes the limit unbounded. -/
theorem unbounded_of_slope {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (ψ₀ σ : F)
    (hσ : σ ≠ 0) : ∀ C : ℝ, ∃ s ≥ (0 : ℝ), C < ‖ψ₀ + s • σ‖ := by
  intro C
  have hσ' : 0 < ‖σ‖ := norm_pos_iff.2 hσ
  set t := (|C| + ‖ψ₀‖ + 1) / ‖σ‖ with ht
  refine ⟨t, by positivity, ?_⟩
  have h1 : ‖t • σ‖ = |C| + ‖ψ₀‖ + 1 := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity), ht, div_mul_cancel₀ _ hσ'.ne']
  have h2 : ‖t • σ‖ - ‖ψ₀‖ ≤ ‖ψ₀ + t • σ‖ := by
    have := norm_sub_norm_le (t • σ) (-ψ₀)
    rwa [sub_neg_eq_add, norm_neg, add_comm] at this
  linarith [le_abs_self C]

/-- **No fixed-time linear curvature bound** (`eq:supp-exact-no-linear-fixed-time`, the
contradiction argument of `thm:supp-exact-initial-layer`): if for every `s ≥ 0` the normalized
readout `a⁻¹ R(a, a³ s)` converges as `a → 0⁺` to `ψ(s)`, and `ψ` is unbounded on `[0, ∞)`, then
no `T, C, a₀ > 0` satisfy `‖R(a, t)‖ ≤ C a` for all `0 < a < a₀`, `0 ≤ t ≤ T`. -/
theorem no_fixed_time_linear_bound {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (R : ℝ → ℝ → F) (ψ : ℝ → F)
    (hlim : ∀ s ≥ (0 : ℝ), Tendsto (fun a => a⁻¹ • R a (a ^ 3 * s)) (𝓝[>] 0) (𝓝 (ψ s)))
    (hunb : ∀ C : ℝ, ∃ s ≥ (0 : ℝ), C < ‖ψ s‖) :
    ¬ ∃ T > (0 : ℝ), ∃ C : ℝ, ∃ a₀ > (0 : ℝ),
      ∀ a ∈ Ioo 0 a₀, ∀ t ∈ Icc 0 T, ‖R a t‖ ≤ C * a := by
  rintro ⟨T, hT, C, a₀, ha₀, hbd⟩
  obtain ⟨s, hs, hC⟩ := hunb C
  have hsmall : Tendsto (fun a : ℝ => a ^ 3 * s) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun a : ℝ => a ^ 3 * s) (𝓝 0) (𝓝 (0 ^ 3 * s)) :=
      ((continuous_pow 3).mul continuous_const).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ a in 𝓝[>] (0 : ℝ), ‖a⁻¹ • R a (a ^ 3 * s)‖ ≤ C := by
    filter_upwards [hsmall.eventually (ge_mem_nhds hT), Ioo_mem_nhdsGT ha₀] with a hT' ha
    have ht : a ^ 3 * s ∈ Icc 0 T := ⟨by have := ha.1; positivity, hT'⟩
    have := hbd a ha _ ht
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ha.1.le)]
    calc a⁻¹ * ‖R a (a ^ 3 * s)‖ ≤ a⁻¹ * (C * a) :=
          mul_le_mul_of_nonneg_left this (inv_nonneg.2 ha.1.le)
      _ = C := by rw [mul_comm C a, ← mul_assoc, inv_mul_cancel₀ ha.1.ne', one_mul]
  have hle : ‖ψ s‖ ≤ C := le_of_tendsto (hlim s hs).norm hev
  linarith

/-- **The shrinking layer** (positive half of `thm:supp-exact-initial-layer`): if
`a⁻¹ R(a, a³ s)` converges uniformly on `[0, S]` to `ψ` with `‖ψ‖ ≤ C_ψ`, then for some `a₀`
`‖R(a, a³ s)‖ ≤ (C_ψ + 1) a` on `0 ≤ s ≤ S` for `0 < a < a₀`. -/
theorem layer_bound {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (R : ℝ → ℝ → F) (ψ : ℝ → F) {S Cψ : ℝ} (hψ : ∀ s ∈ Icc 0 S, ‖ψ s‖ ≤ Cψ)
    (hunif : ∀ ε > 0, ∀ᶠ a in 𝓝[>] (0 : ℝ), ∀ s ∈ Icc 0 S,
      ‖a⁻¹ • R a (a ^ 3 * s) - ψ s‖ ≤ ε) :
    ∃ a₀ : ℝ, 0 < a₀ ∧ ∀ a ∈ Ioo 0 a₀, ∀ s ∈ Icc 0 S, ‖R a (a ^ 3 * s)‖ ≤ (Cψ + 1) * a := by
  obtain ⟨a₀, ha₀, h⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 (hunif 1 one_pos)
  refine ⟨a₀, ha₀, fun a ha s hs => ?_⟩
  have h1 := h ha s hs
  have h2 : ‖a⁻¹ • R a (a ^ 3 * s)‖ ≤ Cψ + 1 := by
    have := norm_le_insert' (a⁻¹ • R a (a ^ 3 * s)) (ψ s)
    linarith [hψ s hs]
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ha.1.le)] at h2
  have := mul_le_mul_of_nonneg_left h2 ha.1.le
  rw [← mul_assoc, mul_inv_cancel₀ ha.1.ne', one_mul] at this
  linarith

/-- **Initial-layer obstruction, assembled** (`thm:supp-exact-initial-layer`, generic form): if the
rescaled trajectories `x_a(s)` (`t = a³ s`) converge on every `[0, S]` to the linear displacement
`x₀ + s v`, and the normalized curvature readout is `a⁻¹ R(a, a³ s) = Φ(x_a(s)) + O(ρ(a))` with
`Φ` continuous linear, `ρ(a) → 0`, and nonzero limiting slope `Φ v ≠ 0`, then no fixed-time bound
`sup_{0 ≤ t ≤ T} ‖R(a,t)‖ ≤ C a` holds for all small `a`. -/
theorem initial_layer_obstruction {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (R : ℝ → ℝ → F) (x : ℝ → ℝ → E) (x₀ v : E) (Φ : E →L[ℝ] F) (ρ : ℝ → ℝ)
    (hconv : ∀ S ≥ (0 : ℝ), ∀ ε > 0, ∀ᶠ a in 𝓝[>] (0 : ℝ), ∀ s ∈ Icc 0 S,
      ‖x a s - (x₀ + s • v)‖ ≤ ε)
    (hread : ∀ a > (0 : ℝ), ∀ s ≥ (0 : ℝ), ‖a⁻¹ • R a (a ^ 3 * s) - Φ (x a s)‖ ≤ ρ a)
    (hρ : Tendsto ρ (𝓝[>] 0) (𝓝 0)) (hslope : Φ v ≠ 0) :
    ¬ ∃ T > (0 : ℝ), ∃ C : ℝ, ∃ a₀ > (0 : ℝ),
      ∀ a ∈ Ioo 0 a₀, ∀ t ∈ Icc 0 T, ‖R a t‖ ≤ C * a := by
  refine no_fixed_time_linear_bound R (fun s => Φ x₀ + s • Φ v) (fun s hs => ?_) ?_
  · rw [Metric.tendsto_nhds]
    intro ε hε
    have hΦ : 0 < ‖Φ‖ + 1 := by positivity
    filter_upwards [hconv s hs (ε / 2 / (‖Φ‖ + 1)) (by positivity),
      hρ.eventually (gt_mem_nhds (half_pos hε)), self_mem_nhdsWithin] with a h1 h2 ha
    have hx := h1 s ⟨hs, le_rfl⟩
    have hr := hread a ha s hs
    rw [dist_eq_norm]
    have heq : a⁻¹ • R a (a ^ 3 * s) - (Φ x₀ + s • Φ v)
        = (a⁻¹ • R a (a ^ 3 * s) - Φ (x a s)) + Φ (x a s - (x₀ + s • v)) := by
      rw [map_sub, map_add, map_smul]; abel
    rw [heq]
    have hΦx : ‖Φ (x a s - (x₀ + s • v))‖ ≤ ε / 2 := by
      refine (Φ.le_opNorm _).trans ?_
      calc ‖Φ‖ * ‖x a s - (x₀ + s • v)‖ ≤ (‖Φ‖ + 1) * (ε / 2 / (‖Φ‖ + 1)) :=
            mul_le_mul (by linarith) hx (norm_nonneg _) hΦ.le
        _ = ε / 2 := by field_simp
    calc _ ≤ ‖a⁻¹ • R a (a ^ 3 * s) - Φ (x a s)‖ + ‖Φ (x a s - (x₀ + s • v))‖ := norm_add_le _ _
      _ < ε := by linarith
  · exact unbounded_of_slope (Φ x₀) (Φ v) hslope

/-! ### The tangency functional -/

/-- Typed inputs of the tangency functional `eq:supp-exact-tangency-functional`: the first Poisson
matrix `𝕂₁(Y)[ν, μ]` (linear in the canonical jet `Y`), the derivative `Dd_{2,W}(Y)[Z, ν]` of the
quadratic weak drift (bilinear in `(Y, Z)`), the leading maps `F₁`, `G`, and the weak curl-free
multiplier space `𝒲`. -/
structure TangencyData (X Λ : Type*) [AddCommGroup X] [Module ℝ X] [AddCommGroup Λ]
    [Module ℝ Λ] where
  K1 : X →ₗ[ℝ] Λ →ₗ[ℝ] Λ →ₗ[ℝ] ℝ
  Dd2 : X →ₗ[ℝ] X →ₗ[ℝ] Λ →ₗ[ℝ] ℝ
  F1 : X →ₗ[ℝ] X
  G : Λ →ₗ[ℝ] X
  W : Submodule ℝ Λ

namespace TangencyData

variable {X Λ : Type*} [AddCommGroup X] [Module ℝ X] [AddCommGroup Λ] [Module ℝ Λ]
  (T : TangencyData X Λ)

/-- The weak null space `eq:supp-exact-weak-null`. -/
def weakNull (Y : X) : Set Λ := {ν | ν ∈ T.W ∧ ∀ μ, T.K1 Y ν μ = 0}

/-- The first tangency functional `eq:supp-exact-tangency-functional`. -/
def delta (ν : Λ) (Y : X) (ℓ : Λ) : ℝ :=
  T.Dd2 Y (T.F1 Y + T.G ℓ) ν + T.K1 (T.F1 Y + T.G ℓ) ν ℓ

/-- Its polarized derivative `DΔ_ν(Y, ℓ)[Z, m]`. -/
def polar (ν : Λ) (Y : X) (ℓ : Λ) (Z : X) (m : Λ) : ℝ :=
  T.Dd2 Z (T.F1 Y + T.G ℓ) ν + T.Dd2 Y (T.F1 Z + T.G m) ν
    + T.K1 (T.F1 Z + T.G m) ν ℓ + T.K1 (T.F1 Y + T.G ℓ) ν m

/-- `Δ_ν` is a quadratic form in `(Y, ℓ)`. -/
theorem delta_smul (ν : Λ) (Y : X) (ℓ : Λ) (r : ℝ) :
    T.delta ν (r • Y) (r • ℓ) = r ^ 2 * T.delta ν Y ℓ := by
  simp only [delta, map_smul, ← smul_add, LinearMap.smul_apply, smul_eq_mul]
  ring

/-- **Exact expansion along a line**:
`Δ(Y + εZ, ℓ + εm) = Δ(Y,ℓ) + ε DΔ(Y,ℓ)[Z,m] + ε² Δ(Z,m)`. -/
theorem delta_line (ν : Λ) (Y : X) (ℓ : Λ) (Z : X) (m : Λ) (ε : ℝ) :
    T.delta ν (Y + ε • Z) (ℓ + ε • m)
      = T.delta ν Y ℓ + ε * T.polar ν Y ℓ Z m + ε ^ 2 * T.delta ν Z m := by
  simp only [delta, polar, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul]
  ring

/-- **The derivative of the tangency functional is its polarization.** -/
theorem hasDerivAt_delta_line (ν : Λ) (Y : X) (ℓ : Λ) (Z : X) (m : Λ) :
    HasDerivAt (fun ε : ℝ => T.delta ν (Y + ε • Z) (ℓ + ε • m)) (T.polar ν Y ℓ Z m) 0 := by
  have h : (fun ε : ℝ => T.delta ν (Y + ε • Z) (ℓ + ε • m))
      = fun ε => T.delta ν Y ℓ + ε * T.polar ν Y ℓ Z m + ε ^ 2 * T.delta ν Z m :=
    funext fun ε => T.delta_line ν Y ℓ Z m ε
  rw [h]
  have h1 := ((hasDerivAt_id (0 : ℝ)).mul_const (T.polar ν Y ℓ Z m)).const_add (T.delta ν Y ℓ)
  have h2 := (hasDerivAt_pow 2 (0 : ℝ)).mul_const (T.delta ν Z m)
  refine (h1.add h2).congr_deriv ?_
  simp

/-- **Poisson-nullity to first order persists**: if `ν` is weak-null at `Y` and
`𝕂₁(Z)[ν, ·] = 0` (zero first variation of the null condition), then `ν` is weak-null at every
`Y + εZ` (`𝕂₁` is linear in the jet). -/
theorem weakNull_line {ν : Λ} {Y Z : X} (hν : ν ∈ T.weakNull Y) (hZ : ∀ μ, T.K1 Z ν μ = 0)
    (ε : ℝ) : ν ∈ T.weakNull (Y + ε • Z) := by
  refine ⟨hν.1, fun μ => ?_⟩
  have h1 : T.K1 Y ν μ = 0 := hν.2 μ
  have h2 : T.K1 Z ν μ = 0 := hZ μ
  rw [map_add, map_smul, LinearMap.add_apply, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.smul_apply, h1, h2, smul_zero, add_zero]

/-- **Deformability** (`thm:supp-exact-upstream-deformation`, conclusion): if the polarized
derivative is nonzero, the tangency obstruction changes along the deformation at arbitrarily
small amplitudes `ε ≠ 0`. -/
theorem deformable_of_polarized_ne_zero {ν : Λ} {Y : X} {ℓ : Λ} {Z : X} {m : Λ}
    (h : T.polar ν Y ℓ Z m ≠ 0) :
    ∀ ε₀ > 0, ∃ ε : ℝ, 0 < |ε| ∧ |ε| < ε₀ ∧
      T.delta ν (Y + ε • Z) (ℓ + ε • m) ≠ T.delta ν Y ℓ := by
  intro ε₀ hε₀
  set P := T.polar ν Y ℓ Z m
  set Q := T.delta ν Z m
  have hP : 0 < |P| := abs_pos.2 h
  set ε := min (ε₀ / 2) (|P| / (2 * (|Q| + 1))) with hεdef
  have hε : 0 < ε := lt_min (by linarith) (by positivity)
  have hεQ : ε * |Q| < |P| := by
    have h1 : ε ≤ |P| / (2 * (|Q| + 1)) := min_le_right _ _
    have h2 : ε * |Q| ≤ |P| / (2 * (|Q| + 1)) * |Q| :=
      mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
    have h3 : |P| / (2 * (|Q| + 1)) * |Q| < |P| := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [abs_nonneg Q]
    linarith
  refine ⟨ε, by rw [abs_of_pos hε]; exact hε, by
    rw [abs_of_pos hε]; exact lt_of_le_of_lt (min_le_left _ _) (by linarith), ?_⟩
  rw [T.delta_line]
  intro heq
  have h0 : ε * (P + ε * Q) = 0 := by linarith
  rcases mul_eq_zero.1 h0 with h0 | h0
  · exact hε.ne' h0
  · have : |P| = ε * |Q| := by
      rw [show P = -(ε * Q) by linarith, abs_neg, abs_mul, abs_of_pos hε]
    linarith

end TangencyData

end ExactInitialLayer
end RenewalGeometry
