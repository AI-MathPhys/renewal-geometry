/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.HessianLoewnerGradientBounds
import RenewalGeometry.Action.NonstationaryActionGapExact

/-!
# Accepted-action stationarity on a compact convex chart
  (`thm:supp-action-stationarity`, `prop:supp-nonstationary-action-gap`,
  `prop:supp-physical-test-stationarity` clause 1, `thm:main-action-stationarity`;
  emergent-spacetime manuscript)

This file restates the Fisher–Bregman stationarity estimates on the manuscript's chart: a
**compact convex** set `Θ` of a real inner product space, with every hypothesis imposed only on
`Θ` (or on an open neighbourhood `U ⊇ Θ` for the first derivatives).

**The chart data** (`ProximalChart`) are exactly the manuscript's hypotheses
(`eq:main-fisher-metric`, `eq:main-action-hessian`): the operational potential `Ψ` and the
reconstructed action `𝒜` have gradients `gΨ, g𝒜` on an open `U ⊇ Θ` and Hessians `HΨ, H𝒜`
(the derivatives of the gradients) at every point of `Θ`, with the Loewner bounds
`m I ⪯ G ⪯ M I` (`G = HΨ`) and `-λ G ⪯ D²𝒜 ⪯ L G` on `Θ` (as quadratic-form inequalities),
`λ, L ≥ 0`, `η > 0`, `ηλ < 1`.  Nothing else is assumed: the gradient-level inequalities
(strong/upper monotonicity, Lipschitz bounds), the symmetry of the Hessians, the strong
convexity `μ_Φ` and smoothness `Λ_Φ` of the proximal objective are *derived*
(`RenewalGeometry.HessianBounds`).

**The proximal minimizer.**  `Φ_θ(y) = 𝒜(y) + η⁻¹ D_Ψ(y, θ)` attains its minimum on `Θ`
(`exists_isMinOn_prox`), and the minimizer is unique (`eq_of_isMinOn_prox`); `y*_θ` enters the
theorems through its defining property `IsMinOn Φ_θ Θ (y*_θ)`, and the canonical choice
`argminProx` is provided.  Interiority is the manuscript's hypothesis `y*_θ ∈ interior Θ` for
supported sources; the vanishing of `∇Φ_θ(y*_θ)` is derived from it (`grad_prox_eq_zero`).

**Pointwise layer** (no descent lemma, no whole-space hypothesis): `‖y - y*‖² ≤ 2Δ/μ_Φ`,
`‖∇Φ_θ(y)‖² ≤ (2Λ_Φ²/μ_Φ) Δ` and
`m⁻¹ ‖∇𝒜(θ)‖² ≤ C₁ Δ + (2(1+ηℓ)²M²/(mη²)) ‖y - θ‖²` with `C₁ = 4Λ_Φ²/(mμ_Φ)`.

**Integrated layer.**
* `coupling_action_gap` (`prop:supp-nonstationary-action-gap`): for any finite coupling `π`
  supported in `Θ × Θ` with interior minimizers at the sources,
  `E_π D_Ψ ≤ η(Δ̄_π + d_𝒜)`, `E_π ‖y-θ‖² ≤ (2η/m)(Δ̄_π + d_𝒜)` and
  `E_α 𝔖 ≤ (C₁ + C₂) Δ̄_π + C₂ d_𝒜`, also with `(d_𝒜)₊`, and the physical-test bound
  `E_α |D𝒜[v]|² ≤ B² [(C₁+C₂) Δ̄_π + C₂ (d_𝒜)₊]`.
* `chart_action_stationarity` (`thm:supp-action-stationarity`): for the lazy kernel
  `K = (1-ϑ) I + ϑ K^acc` (`0 < ϑ ≤ 1`) with stationary law `ν` supported in `Θ`, the identity
  `ν K^acc = ν` is *derived* (`comp_eq_of_lazyKernel_comp_eq`), and
  `∫ D_Ψ dνK^acc ≤ η Δ̄_Ψ`, `∫ ‖y-θ‖² dνK^acc ≤ (2η/m) Δ̄_Ψ`,
  `∫ 𝔖 dν ≤ (4Λ_Φ²/(mμ_Φ) + 4M²(1+ηℓ)²/(m²η)) Δ̄_Ψ` with the manuscript's constant
  `eq:supp-stationarity-constant`, and `Δ̄_Ψ = 0` forces `∇𝒜 = 0` `ν`-a.e.
* `chart_physical_test_stationarity` (`eq:main-physical-stationarity`).

`𝔖(θ) = ⟪∇𝒜(θ), G(θ)⁻¹ ∇𝒜(θ)⟫` is the actual inverse-Fisher form (`stationarityForm`, with
`G(θ)⁻¹` the inverse operator, which exists in finite dimension by coercivity).

Standing technical assumptions (disclosed): the gap integrand is `π`-integrable (this is what
makes `Δ̄` a number), and `𝔖`, resp. the test pairing, is a.e.-strongly measurable.
Integrability of `𝒜`, `D_Ψ`, `‖y-θ‖²`, `‖∇𝒜‖²` is *derived* from compactness of `Θ`.
-/

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped RealInnerProductSpace ENNReal

namespace RenewalGeometry
namespace ChartStationarity

open BregmanStationarity HessianBounds

/-- The manuscript's convex-chart hypotheses for `thm:supp-action-stationarity`
(`eq:main-fisher-metric`, `eq:main-action-hessian`). -/
structure ProximalChart (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] where
  /-- the compact convex chart -/
  Θ : Set E
  /-- an open neighbourhood of the chart carrying the first derivatives -/
  U : Set E
  /-- the operational potential -/
  Ψ : E → ℝ
  /-- the reconstructed common action -/
  𝒜 : E → ℝ
  gΨ : E → E
  g𝒜 : E → E
  /-- the Fisher metric `G = ∇²Ψ` -/
  HΨ : E → E →L[ℝ] E
  /-- the action Hessian `D²𝒜` -/
  H𝒜 : E → E →L[ℝ] E
  m : ℝ
  M : ℝ
  lam : ℝ
  L : ℝ
  η : ℝ
  convex : Convex ℝ Θ
  compact : IsCompact Θ
  isOpen_U : IsOpen U
  subset_U : Θ ⊆ U
  hasGradient_Ψ : ∀ x ∈ U, HasGradientAt Ψ (gΨ x) x
  hasGradient_𝒜 : ∀ x ∈ U, HasGradientAt 𝒜 (g𝒜 x) x
  hasHessian_Ψ : ∀ x ∈ Θ, HasFDerivAt gΨ (HΨ x) x
  hasHessian_𝒜 : ∀ x ∈ Θ, HasFDerivAt g𝒜 (H𝒜 x) x
  m_pos : 0 < m
  /-- `m I ⪯ G(θ)` on the chart -/
  fisher_lower : ∀ x ∈ Θ, ∀ v, m * ‖v‖ ^ 2 ≤ ⟪HΨ x v, v⟫
  /-- `G(θ) ⪯ M I` on the chart -/
  fisher_upper : ∀ x ∈ Θ, ∀ v, ⟪HΨ x v, v⟫ ≤ M * ‖v‖ ^ 2
  lam_nonneg : 0 ≤ lam
  L_nonneg : 0 ≤ L
  /-- `-λ G(θ) ⪯ D²𝒜(θ)` on the chart -/
  action_lower : ∀ x ∈ Θ, ∀ v, -lam * ⟪HΨ x v, v⟫ ≤ ⟪H𝒜 x v, v⟫
  /-- `D²𝒜(θ) ⪯ L G(θ)` on the chart -/
  action_upper : ∀ x ∈ Θ, ∀ v, ⟪H𝒜 x v, v⟫ ≤ L * ⟪HΨ x v, v⟫
  η_pos : 0 < η
  η_lam_lt_one : η * lam < 1

namespace ProximalChart

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (C : ProximalChart E)

/-! ### Constants (`eq:supp-action-constants`, `eq:supp-stationarity-constant`) -/

/-- `μ_Φ = (η⁻¹ - λ) m`. -/
noncomputable def μΦ : ℝ := (C.η⁻¹ - C.lam) * C.m
/-- `Λ_Φ = (η⁻¹ + L) M`. -/
noncomputable def ΛΦ : ℝ := (C.η⁻¹ + C.L) * C.M
/-- `ℓ = max(λ, L)`. -/
noncomputable def ℓ : ℝ := max C.lam C.L
/-- `C₁ = 4 Λ_Φ² / (m μ_Φ)`. -/
noncomputable def C₁ : ℝ := 4 * C.ΛΦ ^ 2 / (C.m * C.μΦ)
/-- `C₂ = 4 M² (1 + ηℓ)² / (m² η)`. -/
noncomputable def C₂ : ℝ := 4 * C.M ^ 2 * (1 + C.η * C.ℓ) ^ 2 / (C.m ^ 2 * C.η)
/-- The manuscript's admissible constant `C_{Ψ,𝒜,η} = C₁ + C₂`
(`eq:supp-stationarity-constant`). -/
noncomputable def stationarityConstant : ℝ := C.C₁ + C.C₂

/-- The proximal objective `Φ_θ(y) = 𝒜(y) + η⁻¹ D_Ψ(y, θ)` of the chart. -/
noncomputable def proxΦ (θ y : E) : ℝ := prox C.Ψ C.𝒜 C.gΨ C.η θ y

/-- The gradient `∇Φ_θ(y) = ∇𝒜(y) + η⁻¹ (∇Ψ(y) - ∇Ψ(θ))`. -/
noncomputable def gradΦ (θ y : E) : E := C.g𝒜 y + C.η⁻¹ • (C.gΨ y - C.gΨ θ)

/-- The Hessian `D²Φ_θ = D²𝒜 + η⁻¹ G`. -/
noncomputable def hessΦ (x : E) : E →L[ℝ] E := C.H𝒜 x + C.η⁻¹ • C.HΨ x

theorem inv_η_sub_lam_pos : 0 < C.η⁻¹ - C.lam := by
  have hη := C.η_pos
  have e : C.η⁻¹ - C.lam = (1 - C.η * C.lam) / C.η := by field_simp
  rw [e]
  exact div_pos (by linarith [C.η_lam_lt_one]) hη

theorem μΦ_pos : 0 < C.μΦ := mul_pos C.inv_η_sub_lam_pos C.m_pos

theorem ℓ_nonneg : 0 ≤ C.ℓ := le_trans C.lam_nonneg (le_max_left _ _)

/-! ### Regularity on the chart -/

theorem hasGradient_Ψ_nhds {x : E} (hx : x ∈ C.Θ) :
    ∀ᶠ y in 𝓝 x, HasGradientAt C.Ψ (C.gΨ y) y :=
  Filter.eventually_of_mem (C.isOpen_U.mem_nhds (C.subset_U hx)) C.hasGradient_Ψ

theorem hasGradient_𝒜_nhds {x : E} (hx : x ∈ C.Θ) :
    ∀ᶠ y in 𝓝 x, HasGradientAt C.𝒜 (C.g𝒜 y) y :=
  Filter.eventually_of_mem (C.isOpen_U.mem_nhds (C.subset_U hx)) C.hasGradient_𝒜

/-- Schwarz: the Fisher metric `G(x) = ∇²Ψ(x)` is symmetric on the chart. -/
theorem HΨ_symm {x : E} (hx : x ∈ C.Θ) (v w : E) : ⟪C.HΨ x v, w⟫ = ⟪v, C.HΨ x w⟫ :=
  hessian_symmetric_of_hasGradientAt (C.hasGradient_Ψ_nhds hx) (C.hasHessian_Ψ x hx) v w

/-- Schwarz: the action Hessian is symmetric on the chart. -/
theorem H𝒜_symm {x : E} (hx : x ∈ C.Θ) (v w : E) : ⟪C.H𝒜 x v, w⟫ = ⟪v, C.H𝒜 x w⟫ :=
  hessian_symmetric_of_hasGradientAt (C.hasGradient_𝒜_nhds hx) (C.hasHessian_𝒜 x hx) v w

theorem continuousOn_gΨ : ContinuousOn C.gΨ C.Θ := fun x hx =>
  (C.hasHessian_Ψ x hx).continuousAt.continuousWithinAt

theorem continuousOn_g𝒜 : ContinuousOn C.g𝒜 C.Θ := fun x hx =>
  (C.hasHessian_𝒜 x hx).continuousAt.continuousWithinAt

theorem continuousOn_Ψ : ContinuousOn C.Ψ C.Θ := fun x hx =>
  (C.hasGradient_Ψ x (C.subset_U hx)).hasFDerivAt.continuousAt.continuousWithinAt

theorem continuousOn_𝒜 : ContinuousOn C.𝒜 C.Θ := fun x hx =>
  (C.hasGradient_𝒜 x (C.subset_U hx)).hasFDerivAt.continuousAt.continuousWithinAt

theorem fisher_nonneg {x : E} (hx : x ∈ C.Θ) (v : E) : 0 ≤ ⟪C.HΨ x v, v⟫ :=
  le_trans (mul_nonneg C.m_pos.le (sq_nonneg _)) (C.fisher_lower x hx v)

/-! ### Gradient-level inequalities derived from the Loewner bounds -/

/-- `m ‖a-b‖² ≤ ⟪∇Ψ a - ∇Ψ b, a-b⟫ ≤ M ‖a-b‖²` on the chart. -/
theorem gΨ_monotone {a b : E} (ha : a ∈ C.Θ) (hb : b ∈ C.Θ) :
    C.m * ‖a - b‖ ^ 2 ≤ ⟪C.gΨ a - C.gΨ b, a - b⟫
      ∧ ⟪C.gΨ a - C.gΨ b, a - b⟫ ≤ C.M * ‖a - b‖ ^ 2 :=
  inner_sub_bounds_of_hessian C.convex C.hasHessian_Ψ ha hb
    (fun x hx => C.fisher_lower x hx _) (fun x hx => C.fisher_upper x hx _)

/-- `‖∇Ψ a - ∇Ψ b‖ ≤ M ‖a-b‖` on the chart. -/
theorem gΨ_lipschitz {a b : E} (ha : a ∈ C.Θ) (hb : b ∈ C.Θ) :
    ‖C.gΨ a - C.gΨ b‖ ≤ C.M * ‖a - b‖ :=
  norm_sub_le_of_hessian C.convex C.hasHessian_Ψ (fun x hx => C.HΨ_symm hx)
    (fun x hx v => by
      have h1 := C.fisher_nonneg hx v
      have h2 := C.fisher_upper x hx v
      rw [abs_le]; constructor <;> linarith) ha hb

/-- `‖∇𝒜 a - ∇𝒜 b‖ ≤ ℓ M ‖a-b‖` on the chart, `ℓ = max(λ, L)`. -/
theorem g𝒜_lipschitz {a b : E} (ha : a ∈ C.Θ) (hb : b ∈ C.Θ) :
    ‖C.g𝒜 a - C.g𝒜 b‖ ≤ C.ℓ * C.M * ‖a - b‖ := by
  refine norm_sub_le_of_hessian C.convex C.hasHessian_𝒜 (fun x hx => C.H𝒜_symm hx)
    (fun x hx v => ?_) ha hb
  have h0 := C.fisher_nonneg hx v
  have h1 := C.fisher_upper x hx v
  have h2 := C.action_lower x hx v
  have h3 := C.action_upper x hx v
  have hl : C.lam ≤ C.ℓ := le_max_left _ _
  have hL : C.L ≤ C.ℓ := le_max_right _ _
  have hMv : 0 ≤ C.M * ‖v‖ ^ 2 := le_trans h0 h1
  have hlam := C.lam_nonneg
  have hL0 := C.L_nonneg
  rw [abs_le]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left h1 hlam, mul_le_mul_of_nonneg_right hl hMv]
  · nlinarith [mul_le_mul_of_nonneg_left h1 hL0, mul_le_mul_of_nonneg_right hL hMv]

theorem hasFDerivAt_gradΦ (θ : E) {x : E} (hx : x ∈ C.Θ) :
    HasFDerivAt (C.gradΦ θ) (C.hessΦ x) x := by
  unfold gradΦ hessΦ
  exact (C.hasHessian_𝒜 x hx).add (((C.hasHessian_Ψ x hx).sub_const (C.gΨ θ)).const_smul C.η⁻¹)

theorem hessΦ_inner (x v : E) :
    ⟪C.hessΦ x v, v⟫ = ⟪C.H𝒜 x v, v⟫ + C.η⁻¹ * ⟪C.HΨ x v, v⟫ := by
  simp [hessΦ, inner_add_left, real_inner_smul_left]

theorem hessΦ_symm {x : E} (hx : x ∈ C.Θ) (v w : E) :
    ⟪C.hessΦ x v, w⟫ = ⟪v, C.hessΦ x w⟫ := by
  simp only [hessΦ, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    C.H𝒜_symm hx, C.HΨ_symm hx]

/-- The proximal Hessian lies between `μ_Φ I` and `Λ_Φ I` on the chart. -/
theorem hessΦ_bounds {x : E} (hx : x ∈ C.Θ) (v : E) :
    C.μΦ * ‖v‖ ^ 2 ≤ ⟪C.hessΦ x v, v⟫ ∧ ⟪C.hessΦ x v, v⟫ ≤ C.ΛΦ * ‖v‖ ^ 2 := by
  rw [C.hessΦ_inner]
  have h0 := C.fisher_lower x hx v
  have h1 := C.fisher_upper x hx v
  have h2 := C.action_lower x hx v
  have h3 := C.action_upper x hx v
  have hμ := C.inv_η_sub_lam_pos
  have hηi : 0 < C.η⁻¹ := inv_pos.mpr C.η_pos
  have hL0 := C.L_nonneg
  unfold μΦ ΛΦ
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left h0 hμ.le]
  · nlinarith [mul_le_mul_of_nonneg_left h1 (add_pos_of_pos_of_nonneg hηi hL0).le]

/-- Strong monotonicity of `∇Φ_θ` on the chart: `μ_Φ ‖a-b‖² ≤ ⟪∇Φ_θ a - ∇Φ_θ b, a-b⟫`. -/
theorem gradΦ_strongMono (θ : E) {a b : E} (ha : a ∈ C.Θ) (hb : b ∈ C.Θ) :
    C.μΦ * ‖a - b‖ ^ 2 ≤ ⟪C.gradΦ θ a - C.gradΦ θ b, a - b⟫ :=
  (inner_sub_bounds_of_hessian C.convex (fun x hx => C.hasFDerivAt_gradΦ θ hx) ha hb
    (fun x hx => (C.hessΦ_bounds hx _).1) (fun x hx => (C.hessΦ_bounds hx _).2)).1

/-- `∇Φ_θ` is `Λ_Φ`-Lipschitz on the chart. -/
theorem gradΦ_lipschitz (θ : E) {a b : E} (ha : a ∈ C.Θ) (hb : b ∈ C.Θ) :
    ‖C.gradΦ θ a - C.gradΦ θ b‖ ≤ C.ΛΦ * ‖a - b‖ := by
  refine norm_sub_le_of_hessian C.convex (fun x hx => C.hasFDerivAt_gradΦ θ hx)
    (fun x hx => C.hessΦ_symm hx) (fun x hx v => ?_) ha hb
  have h := C.hessΦ_bounds hx v
  have hμv : 0 ≤ C.μΦ * ‖v‖ ^ 2 := mul_nonneg C.μΦ_pos.le (sq_nonneg _)
  rw [abs_le]; constructor <;> linarith [h.1, h.2]

/-! ### The proximal objective and its minimizer -/

/-- The gradient of `Φ_θ` at points of the neighbourhood `U`. -/
theorem hasGradientAt_proxΦ (θ : E) {y : E} (hy : y ∈ C.U) :
    HasGradientAt (C.proxΦ θ) (C.gradΦ θ y) y := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h𝒜 := (C.hasGradient_𝒜 y hy).hasFDerivAt
  have hΨ := (C.hasGradient_Ψ y hy).hasFDerivAt
  have hlin : HasFDerivAt (fun z : E => ⟪C.gΨ θ, z - θ⟫)
      (InnerProductSpace.toDual ℝ E (C.gΨ θ)) y := by
    have hfun : (fun z : E => ⟪C.gΨ θ, z - θ⟫)
        = fun z : E => (InnerProductSpace.toDual ℝ E (C.gΨ θ)) z - ⟪C.gΨ θ, θ⟫ := by
      funext z
      rw [InnerProductSpace.toDual_apply_apply, inner_sub_right]
    rw [hfun]
    exact ((InnerProductSpace.toDual ℝ E (C.gΨ θ)).hasFDerivAt).sub_const _
  have hD : HasFDerivAt (fun z => bregmanD C.Ψ C.gΨ z θ)
      ((InnerProductSpace.toDual ℝ E (C.gΨ y)) - InnerProductSpace.toDual ℝ E (C.gΨ θ)) y :=
    (hΨ.sub_const (C.Ψ θ)).sub hlin
  have hsum := h𝒜.add (hD.const_mul C.η⁻¹)
  have hclm : (InnerProductSpace.toDual ℝ E (C.g𝒜 y))
      + C.η⁻¹ • ((InnerProductSpace.toDual ℝ E (C.gΨ y))
        - InnerProductSpace.toDual ℝ E (C.gΨ θ))
      = InnerProductSpace.toDual ℝ E (C.gradΦ θ y) := by
    ext w
    simp only [gradΦ, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.sub_apply, InnerProductSpace.toDual_apply_apply, inner_add_left,
      smul_eq_mul]
    rw [real_inner_smul_left, inner_sub_left]
  rw [← hclm]
  exact hsum

theorem proxΦ_self (θ : E) : C.proxΦ θ θ = C.𝒜 θ := by
  simp [proxΦ, prox, bregmanD]

theorem continuousOn_proxΦ (θ : E) : ContinuousOn (C.proxΦ θ) C.Θ := fun y hy =>
  (C.hasGradientAt_proxΦ θ (C.subset_U hy)).hasFDerivAt.continuousAt.continuousWithinAt

/-- The Bregman floor on the chart: `D_Ψ(y, θ) ≥ (m/2) ‖y - θ‖²` for `θ, y ∈ Θ`. -/
theorem bregmanD_floor {θ y : E} (hθ : θ ∈ C.Θ) (hy : y ∈ C.Θ) :
    C.m / 2 * ‖y - θ‖ ^ 2 ≤ bregmanD C.Ψ C.gΨ y θ :=
  floor_of_inner_sub_ge C.convex (fun x hx => C.hasGradient_Ψ x (C.subset_U hx))
    (fun x hx z hz => (C.gΨ_monotone hx hz).1) hθ hy

/-- The proximal floor on the chart:
`Φ_θ(y) - Φ_θ(a) - ⟪∇Φ_θ(a), y - a⟫ ≥ (μ_Φ/2) ‖y - a‖²` for `a, y ∈ Θ`. -/
theorem proxΦ_floor (θ : E) {a y : E} (ha : a ∈ C.Θ) (hy : y ∈ C.Θ) :
    C.μΦ / 2 * ‖y - a‖ ^ 2 ≤ C.proxΦ θ y - C.proxΦ θ a - ⟪C.gradΦ θ a, y - a⟫ :=
  floor_of_inner_sub_ge C.convex (fun x hx => C.hasGradientAt_proxΦ θ (C.subset_U hx))
    (fun x hx z hz => C.gradΦ_strongMono θ hx hz) ha hy

/-- Existence of the proximal minimizer on the compact chart. -/
theorem exists_isMinOn_proxΦ (hne : C.Θ.Nonempty) (θ : E) :
    ∃ y ∈ C.Θ, IsMinOn (C.proxΦ θ) C.Θ y :=
  C.compact.exists_isMinOn hne (C.continuousOn_proxΦ θ)

/-- **The minimum is unique** (strong convexity of `Φ_θ` on the convex chart). -/
theorem eq_of_isMinOn_proxΦ (θ : E) {y₁ y₂ : E} (h₁ : y₁ ∈ C.Θ) (h₂ : y₂ ∈ C.Θ)
    (hm₁ : IsMinOn (C.proxΦ θ) C.Θ y₁) (hm₂ : IsMinOn (C.proxΦ θ) C.Θ y₂) : y₁ = y₂ := by
  set c : E := (1 / 2 : ℝ) • (y₁ + y₂) with hc
  have hcmem : c ∈ C.Θ := by
    have := C.convex h₁ h₂ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num)
    simpa [hc, smul_add] using this
  have f1 := C.proxΦ_floor θ hcmem h₁
  have f2 := C.proxΦ_floor θ hcmem h₂
  have e2 : y₂ - c = -(y₁ - c) := by
    rw [hc]; module
  rw [e2, inner_neg_right, norm_neg] at f2
  have m1 : C.proxΦ θ y₁ ≤ C.proxΦ θ c := hm₁ hcmem
  have m2 : C.proxΦ θ y₂ ≤ C.proxΦ θ c := hm₂ hcmem
  have hμ := C.μΦ_pos
  have hsq : ‖y₁ - c‖ ^ 2 ≤ 0 := by nlinarith
  have h0 : y₁ - c = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg (y₁ - c)])
  have : y₁ - y₂ = (2 : ℝ) • (y₁ - c) := by rw [hc]; module
  rw [h0, smul_zero] at this
  exact sub_eq_zero.mp this

open Classical in
/-- The canonical proximal minimizer `y*_θ = argmin_{y ∈ Θ} Φ_θ(y)` (`θ` itself if no
minimizer exists, which happens only for an empty chart). -/
noncomputable def argminProx (θ : E) : E :=
  if h : ∃ y ∈ C.Θ, IsMinOn (C.proxΦ θ) C.Θ y then h.choose else θ

theorem argminProx_spec (hne : C.Θ.Nonempty) (θ : E) :
    C.argminProx θ ∈ C.Θ ∧ IsMinOn (C.proxΦ θ) C.Θ (C.argminProx θ) := by
  have h := C.exists_isMinOn_proxΦ hne θ
  simp only [argminProx, dif_pos h]
  exact h.choose_spec

/-- **Interiority gives the ordinary first-order condition** `∇Φ_θ(y*_θ) = 0`. -/
theorem gradΦ_eq_zero (θ : E) {y : E} (hint : y ∈ interior C.Θ)
    (hmin : IsMinOn (C.proxΦ θ) C.Θ y) : C.gradΦ θ y = 0 := by
  have hloc : IsLocalMin (C.proxΦ θ) y :=
    hmin.isLocalMin (mem_interior_iff_mem_nhds.mp hint)
  have hg := C.hasGradientAt_proxΦ θ (C.subset_U (interior_subset hint))
  have h0 := hloc.hasFDerivAt_eq_zero hg.hasFDerivAt
  exact (InnerProductSpace.toDual ℝ E).map_eq_zero_iff.mp h0

/-! ### The pointwise stationarity layer -/

/-- The proximal-minimality inequality `𝒜(y) - 𝒜(θ) + η⁻¹ D_Ψ(y,θ) ≤ Δ_Ψ(θ,y)` for a source
`θ ∈ Θ`. -/
theorem action_bregman_le_gap {ystar : E → E} {θ : E} (hθ : θ ∈ C.Θ)
    (hmin : IsMinOn (C.proxΦ θ) C.Θ (ystar θ)) (y : E) :
    C.𝒜 y - C.𝒜 θ + C.η⁻¹ * bregmanD C.Ψ C.gΨ y θ ≤ gap C.Ψ C.𝒜 C.gΨ C.η ystar θ y := by
  have h1 : C.proxΦ θ (ystar θ) ≤ C.proxΦ θ θ := hmin hθ
  rw [C.proxΦ_self] at h1
  unfold gap
  simp only [proxΦ] at h1
  unfold prox at h1 ⊢
  linarith

theorem gap_nonneg {ystar : E → E} {θ y : E} (hy : y ∈ C.Θ)
    (hmin : IsMinOn (C.proxΦ θ) C.Θ (ystar θ)) : 0 ≤ gap C.Ψ C.𝒜 C.gΨ C.η ystar θ y :=
  sub_nonneg.mpr (hmin hy)

/-- Strong convexity at an interior minimizer: `‖y - y*_θ‖² ≤ 2 Δ_Ψ(θ,y)/μ_Φ`. -/
theorem sq_dist_argmin_le {ystar : E → E} {θ y : E} (hy : y ∈ C.Θ)
    (hint : ystar θ ∈ interior C.Θ) (hmin : IsMinOn (C.proxΦ θ) C.Θ (ystar θ)) :
    ‖y - ystar θ‖ ^ 2 ≤ 2 / C.μΦ * gap C.Ψ C.𝒜 C.gΨ C.η ystar θ y := by
  have h := C.proxΦ_floor θ (interior_subset hint) hy
  rw [C.gradΦ_eq_zero θ hint hmin, inner_zero_left, sub_zero] at h
  have hμ := C.μΦ_pos
  unfold gap
  simp only [proxΦ] at h
  rw [div_mul_eq_mul_div, le_div_iff₀ hμ]
  nlinarith

/-- `‖∇Φ_θ(y)‖² ≤ (2 Λ_Φ² / μ_Φ) Δ_Ψ(θ, y)` at an interior minimizer. -/
theorem gradΦ_sq_le {ystar : E → E} {θ y : E} (hy : y ∈ C.Θ)
    (hint : ystar θ ∈ interior C.Θ) (hmin : IsMinOn (C.proxΦ θ) C.Θ (ystar θ)) :
    ‖C.gradΦ θ y‖ ^ 2 ≤ 2 * C.ΛΦ ^ 2 / C.μΦ * gap C.Ψ C.𝒜 C.gΨ C.η ystar θ y := by
  have hlip := C.gradΦ_lipschitz θ hy (interior_subset hint)
  rw [C.gradΦ_eq_zero θ hint hmin, sub_zero] at hlip
  have hd := C.sq_dist_argmin_le hy hint hmin
  have hΛ0 : 0 ≤ C.ΛΦ * ‖y - ystar θ‖ := le_trans (norm_nonneg _) hlip
  have hsq : ‖C.gradΦ θ y‖ ^ 2 ≤ C.ΛΦ ^ 2 * ‖y - ystar θ‖ ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hlip 2
  calc ‖C.gradΦ θ y‖ ^ 2 ≤ C.ΛΦ ^ 2 * ‖y - ystar θ‖ ^ 2 := hsq
    _ ≤ C.ΛΦ ^ 2 * (2 / C.μΦ * gap C.Ψ C.𝒜 C.gΨ C.η ystar θ y) :=
        mul_le_mul_of_nonneg_left hd (sq_nonneg _)
    _ = 2 * C.ΛΦ ^ 2 / C.μΦ * gap C.Ψ C.𝒜 C.gΨ C.η ystar θ y := by ring

/-- Reconstruction of the action gradient from the proximal gradient and the displacement:
`‖∇𝒜(θ)‖² ≤ 2 ‖∇Φ_θ(y)‖² + 2 η⁻² (1+ηℓ)² M² ‖y-θ‖²` for `θ, y ∈ Θ`. -/
theorem g𝒜_sq_le {θ y : E} (hθ : θ ∈ C.Θ) (hy : y ∈ C.Θ) :
    ‖C.g𝒜 θ‖ ^ 2 ≤ 2 * ‖C.gradΦ θ y‖ ^ 2
      + 2 * C.η⁻¹ ^ 2 * ((1 + C.η * C.ℓ) ^ 2 * C.M ^ 2 * ‖y - θ‖ ^ 2) := by
  have hη := C.η_pos
  have hid : C.η • C.g𝒜 θ = C.η • C.gradΦ θ y - (C.gΨ y - C.gΨ θ)
      - C.η • (C.g𝒜 y - C.g𝒜 θ) := by
    simp only [gradΦ, smul_add, smul_sub, smul_smul, mul_inv_cancel₀ hη.ne', one_smul]
    abel
  have h1 := C.gΨ_lipschitz hy hθ
  have h2 := C.g𝒜_lipschitz hy hθ
  have hnorm : C.η * ‖C.g𝒜 θ‖
      ≤ C.η * ‖C.gradΦ θ y‖ + (1 + C.η * C.ℓ) * C.M * ‖y - θ‖ := by
    have e : C.η * ‖C.g𝒜 θ‖ = ‖C.η • C.g𝒜 θ‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hη]
    rw [e, hid]
    have t1 := norm_sub_le (C.η • C.gradΦ θ y - (C.gΨ y - C.gΨ θ)) (C.η • (C.g𝒜 y - C.g𝒜 θ))
    have t2 := norm_sub_le (C.η • C.gradΦ θ y) (C.gΨ y - C.gΨ θ)
    have t3 : ‖C.η • C.gradΦ θ y‖ = C.η * ‖C.gradΦ θ y‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hη]
    have t4 : ‖C.η • (C.g𝒜 y - C.g𝒜 θ)‖ = C.η * ‖C.g𝒜 y - C.g𝒜 θ‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hη]
    have t5 := mul_le_mul_of_nonneg_left h2 hη.le
    nlinarith
  have hsq : (C.η * ‖C.g𝒜 θ‖) ^ 2
      ≤ 2 * (C.η * ‖C.gradΦ θ y‖) ^ 2 + 2 * ((1 + C.η * C.ℓ) * C.M * ‖y - θ‖) ^ 2 := by
    have h0 : 0 ≤ C.η * ‖C.g𝒜 θ‖ := by positivity
    nlinarith [sq_nonneg (C.η * ‖C.gradΦ θ y‖ - (1 + C.η * C.ℓ) * C.M * ‖y - θ‖)]
  have hη2 : 0 < C.η ^ 2 := by positivity
  have key : C.η ^ 2 * ‖C.g𝒜 θ‖ ^ 2 ≤ C.η ^ 2 * (2 * ‖C.gradΦ θ y‖ ^ 2
      + 2 * C.η⁻¹ ^ 2 * ((1 + C.η * C.ℓ) ^ 2 * C.M ^ 2 * ‖y - θ‖ ^ 2)) := by
    have e : C.η ^ 2 * (2 * ‖C.gradΦ θ y‖ ^ 2
        + 2 * C.η⁻¹ ^ 2 * ((1 + C.η * C.ℓ) ^ 2 * C.M ^ 2 * ‖y - θ‖ ^ 2))
        = 2 * (C.η * ‖C.gradΦ θ y‖) ^ 2 + 2 * ((1 + C.η * C.ℓ) * C.M * ‖y - θ‖) ^ 2 := by
      field_simp
    rw [e]
    nlinarith [hsq]
  exact le_of_mul_le_mul_left key hη2

/-- **The pointwise stationarity bound**: for a source `θ ∈ Θ`, a target `y ∈ Θ` and an
interior proximal minimizer,
`m⁻¹ ‖∇𝒜(θ)‖² ≤ C₁ Δ_Ψ(θ,y) + (2(1+ηℓ)²M²/(mη²)) ‖y-θ‖²`, `C₁ = 4Λ_Φ²/(mμ_Φ)`. -/
theorem envelope_le {ystar : E → E} {θ y : E} (hθ : θ ∈ C.Θ) (hy : y ∈ C.Θ)
    (hint : ystar θ ∈ interior C.Θ) (hmin : IsMinOn (C.proxΦ θ) C.Θ (ystar θ)) :
    C.m⁻¹ * ‖C.g𝒜 θ‖ ^ 2 ≤ C.C₁ * gap C.Ψ C.𝒜 C.gΨ C.η ystar θ y
      + 2 * (1 + C.η * C.ℓ) ^ 2 * C.M ^ 2 / (C.m * C.η ^ 2) * ‖y - θ‖ ^ 2 := by
  have h1 := C.g𝒜_sq_le hθ hy
  have h2 := C.gradΦ_sq_le hy hint hmin
  have hm := C.m_pos
  have hμ := C.μΦ_pos
  have hη := C.η_pos
  have h3 : ‖C.g𝒜 θ‖ ^ 2 ≤ 2 * (2 * C.ΛΦ ^ 2 / C.μΦ * gap C.Ψ C.𝒜 C.gΨ C.η ystar θ y)
      + 2 * C.η⁻¹ ^ 2 * ((1 + C.η * C.ℓ) ^ 2 * C.M ^ 2 * ‖y - θ‖ ^ 2) := by linarith
  have h4 := mul_le_mul_of_nonneg_left h3 (inv_nonneg.mpr hm.le)
  have e : C.m⁻¹ * (2 * (2 * C.ΛΦ ^ 2 / C.μΦ * gap C.Ψ C.𝒜 C.gΨ C.η ystar θ y)
      + 2 * C.η⁻¹ ^ 2 * ((1 + C.η * C.ℓ) ^ 2 * C.M ^ 2 * ‖y - θ‖ ^ 2))
      = C.C₁ * gap C.Ψ C.𝒜 C.gΨ C.η ystar θ y
        + 2 * (1 + C.η * C.ℓ) ^ 2 * C.M ^ 2 / (C.m * C.η ^ 2) * ‖y - θ‖ ^ 2 := by
    unfold C₁
    field_simp
    ring
  linarith

end ProximalChart

/-! ### The inverse-Fisher stationarity form -/

/-- The stationarity form `𝔖(θ) = ⟪∇𝒜(θ), G(θ)⁻¹ ∇𝒜(θ)⟫` (`eq:main-stationarity-gap`), with
`G(θ)⁻¹` the inverse operator. -/
noncomputable def stationarityForm {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (H : E → E →L[ℝ] E) (g : E → E) (θ : E) : ℝ :=
  ⟪g θ, (H θ).inverse (g θ)⟫

/-- A coercive operator `m ‖v‖² ≤ ⟪T v, v⟫` on a finite-dimensional space is invertible, and
`0 ≤ ⟪g, T⁻¹ g⟫ ≤ m⁻¹ ‖g‖²` (`G⁻¹ ⪯ m⁻¹ I`). -/
theorem inverse_form_bounds {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (T : E →L[ℝ] E) {m : ℝ} (hm : 0 < m)
    (hT : ∀ v, m * ‖v‖ ^ 2 ≤ ⟪T v, v⟫) (g : E) :
    T (T.inverse g) = g ∧ 0 ≤ ⟪g, T.inverse g⟫ ∧ ⟪g, T.inverse g⟫ ≤ m⁻¹ * ‖g‖ ^ 2 := by
  have hinj : Function.Injective T := by
    intro a b hab
    have h := hT (a - b)
    rw [map_sub, hab, sub_self, inner_zero_left] at h
    have hx : ‖a - b‖ ^ 2 ≤ 0 := by
      by_contra hc
      push Not at hc
      have := mul_pos hm hc
      linarith
    have h0 : ‖a - b‖ = 0 :=
      pow_eq_zero_iff two_ne_zero |>.mp (le_antisymm hx (sq_nonneg _))
    exact sub_eq_zero.mp (norm_eq_zero.mp h0)
  have hsurj : Function.Surjective T :=
    (LinearMap.injective_iff_surjective (f := (T : E →ₗ[ℝ] E))).mp hinj
  let e : E ≃L[ℝ] E :=
    (LinearEquiv.ofBijective (T : E →ₗ[ℝ] E) ⟨hinj, hsurj⟩).toContinuousLinearEquiv
  have hTe : (e : E →L[ℝ] E) = T := by
    ext x
    rfl
  have hinv : T.inverse = (e.symm : E →L[ℝ] E) := by
    rw [← hTe, ContinuousLinearMap.inverse_equiv]
  set w := T.inverse g with hw
  have hTw : T w = g := by
    rw [hw, hinv, ← hTe]
    exact e.apply_symm_apply g
  have hpos : m * ‖w‖ ^ 2 ≤ ⟪g, w⟫ := by
    have := hT w
    rwa [hTw] at this
  have hcs : ⟪g, w⟫ ≤ ‖g‖ * ‖w‖ := real_inner_le_norm g w
  refine ⟨hTw, le_trans (by positivity) hpos, ?_⟩
  have hw' : m * ‖w‖ ≤ ‖g‖ := by
    rcases (norm_nonneg w).lt_or_eq with h | h
    · nlinarith
    · rw [← h, mul_zero]; exact norm_nonneg g
  have : ‖g‖ * ‖w‖ ≤ m⁻¹ * ‖g‖ ^ 2 := by
    have h1 : ‖w‖ ≤ m⁻¹ * ‖g‖ := by
      rw [le_inv_mul_iff₀ hm]; exact hw'
    calc ‖g‖ * ‖w‖ ≤ ‖g‖ * (m⁻¹ * ‖g‖) := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = m⁻¹ * ‖g‖ ^ 2 := by ring
  linarith

/-! ### Measure-theoretic helpers -/

/-- A function continuous on a compact set carrying almost all the mass of a finite measure
is integrable. -/
theorem integrable_of_continuousOn_of_ae_mem {X : Type*} [TopologicalSpace X] [T2Space X]
    [MeasurableSpace X] [OpensMeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {K : Set X} (hK : IsCompact K) {f : X → ℝ} (hf : ContinuousOn f K)
    (hae : ∀ᵐ x ∂μ, x ∈ K) : Integrable f μ := by
  rw [← Measure.restrict_eq_self_of_ae_mem hae]
  exact hf.integrableOn_compact hK

/-! ### The lazy kernel -/

section Lazy

variable {E : Type} [MeasurableSpace E]

/-- The lazy kernel `K = (1-ϑ) I + ϑ K^acc`. -/
noncomputable def lazyKernel (ϑ : ℝ) (Kacc : Kernel E E) : Kernel E E where
  toFun θ := ENNReal.ofReal (1 - ϑ) • Measure.dirac θ + ENNReal.ofReal ϑ • Kacc θ
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    simp only [Measure.add_apply, Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ hs]
    exact (measurable_const.mul (measurable_one.indicator hs)).add
      (measurable_const.mul (Kacc.measurable_coe hs))

theorem lazyKernel_apply (ϑ : ℝ) (Kacc : Kernel E E) (θ : E) :
    lazyKernel ϑ Kacc θ = ENNReal.ofReal (1 - ϑ) • Measure.dirac θ + ENNReal.ofReal ϑ • Kacc θ :=
  rfl

/-- `ν K = (1-ϑ) ν + ϑ ν K^acc` for the lazy kernel. -/
theorem lazyKernel_comp (ϑ : ℝ) (Kacc : Kernel E E) (ν : Measure E) :
    lazyKernel ϑ Kacc ∘ₘ ν = ENNReal.ofReal (1 - ϑ) • ν + ENNReal.ofReal ϑ • (Kacc ∘ₘ ν) := by
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _), Measure.add_apply, Measure.smul_apply,
    Measure.smul_apply, Measure.bind_apply hs (Kernel.aemeasurable _), smul_eq_mul, smul_eq_mul]
  have hpt : ∀ θ, lazyKernel ϑ Kacc θ s
      = ENNReal.ofReal (1 - ϑ) * s.indicator 1 θ + ENNReal.ofReal ϑ * Kacc θ s := by
    intro θ
    rw [lazyKernel_apply, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
      Measure.dirac_apply' _ hs, smul_eq_mul, smul_eq_mul]
  simp_rw [hpt]
  rw [lintegral_add_left ((measurable_one.indicator hs).const_mul _),
    lintegral_const_mul _ (measurable_one.indicator hs),
    lintegral_const_mul _ (Kacc.measurable_coe hs), lintegral_indicator_one hs]

/-- **Stationarity of the accepted kernel from the lazy kernel**: if
`K = (1-ϑ) I + ϑ K^acc` with state-independent `0 < ϑ ≤ 1` has stationary law `ν` (finite),
then `ν K^acc = ν`. -/
theorem comp_eq_of_lazyKernel_comp_eq {ν : Measure E} [IsFiniteMeasure ν] {Kacc : Kernel E E}
    {ϑ : ℝ} (hϑ0 : 0 < ϑ) (hϑ1 : ϑ ≤ 1) (h : lazyKernel ϑ Kacc ∘ₘ ν = ν) :
    Kacc ∘ₘ ν = ν := by
  ext s hs
  have h1 := congrArg (fun μ : Measure E => μ s) h
  simp only [lazyKernel_comp, Measure.add_apply, Measure.smul_apply, smul_eq_mul] at h1
  have hsum : ENNReal.ofReal (1 - ϑ) + ENNReal.ofReal ϑ = 1 := by
    rw [← ENNReal.ofReal_add (by linarith) hϑ0.le, sub_add_cancel, ENNReal.ofReal_one]
  have h2 : ν s = ENNReal.ofReal (1 - ϑ) * ν s + ENNReal.ofReal ϑ * ν s := by
    rw [← add_mul, hsum, one_mul]
  have hfin : ENNReal.ofReal (1 - ϑ) * ν s ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top ν s)
  have h3 : ENNReal.ofReal ϑ * (Kacc ∘ₘ ν) s = ENNReal.ofReal ϑ * ν s := by
    have := h1.trans h2
    exact (ENNReal.add_right_inj hfin).mp this
  exact (ENNReal.mul_right_inj (ENNReal.ofReal_pos.mpr hϑ0).ne' ENNReal.ofReal_ne_top).mp h3

end Lazy

/-! ### Integrated layer against an arbitrary coupling -/

namespace ProximalChart

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (C : ProximalChart E)
variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {π : Measure (E × E)} [IsFiniteMeasure π] {ystar : E → E}

theorem ae_fst_mem (hsupp : ∀ᵐ p ∂π, p.1 ∈ C.Θ ∧ p.2 ∈ C.Θ) :
    ∀ᵐ θ ∂(π.map Prod.fst), θ ∈ C.Θ :=
  (ae_map_iff measurable_fst.aemeasurable C.compact.isClosed.measurableSet).mpr
    (hsupp.mono fun _ hp => hp.1)

theorem ae_snd_mem (hsupp : ∀ᵐ p ∂π, p.1 ∈ C.Θ ∧ p.2 ∈ C.Θ) :
    ∀ᵐ y ∂(π.map Prod.snd), y ∈ C.Θ :=
  (ae_map_iff measurable_snd.aemeasurable C.compact.isClosed.measurableSet).mpr
    (hsupp.mono fun _ hp => hp.2)

theorem ae_mem_prod (hsupp : ∀ᵐ p ∂π, p.1 ∈ C.Θ ∧ p.2 ∈ C.Θ) :
    ∀ᵐ p ∂π, p ∈ C.Θ ×ˢ C.Θ := hsupp

theorem integrable_pair {f : E × E → ℝ} (hf : ContinuousOn f (C.Θ ×ˢ C.Θ))
    (hsupp : ∀ᵐ p ∂π, p.1 ∈ C.Θ ∧ p.2 ∈ C.Θ) : Integrable f π :=
  integrable_of_continuousOn_of_ae_mem (C.compact.prod C.compact) hf hsupp

/-- The action drop as an integral against the coupling (integrability from compactness). -/
theorem actionDrop_eq (hsupp : ∀ᵐ p ∂π, p.1 ∈ C.Θ ∧ p.2 ∈ C.Θ) :
    actionDrop π C.𝒜 = ∫ p, C.𝒜 p.1 ∂π - ∫ p, C.𝒜 p.2 ∂π := by
  have h1 : Integrable C.𝒜 (π.map Prod.fst) :=
    integrable_of_continuousOn_of_ae_mem C.compact C.continuousOn_𝒜 (C.ae_fst_mem hsupp)
  have h2 : Integrable C.𝒜 (π.map Prod.snd) :=
    integrable_of_continuousOn_of_ae_mem C.compact C.continuousOn_𝒜 (C.ae_snd_mem hsupp)
  unfold actionDrop
  rw [integral_map measurable_fst.aemeasurable h1.aestronglyMeasurable,
    integral_map measurable_snd.aemeasurable h2.aestronglyMeasurable]

theorem integrable_𝒜_fst (hsupp : ∀ᵐ p ∂π, p.1 ∈ C.Θ ∧ p.2 ∈ C.Θ) :
    Integrable (fun p : E × E => C.𝒜 p.1) π :=
  C.integrable_pair (C.continuousOn_𝒜.comp continuousOn_fst fun _ hp => hp.1) hsupp

theorem integrable_𝒜_snd (hsupp : ∀ᵐ p ∂π, p.1 ∈ C.Θ ∧ p.2 ∈ C.Θ) :
    Integrable (fun p : E × E => C.𝒜 p.2) π :=
  C.integrable_pair (C.continuousOn_𝒜.comp continuousOn_snd fun _ hp => hp.2) hsupp

theorem integrable_bregmanD (hsupp : ∀ᵐ p ∂π, p.1 ∈ C.Θ ∧ p.2 ∈ C.Θ) :
    Integrable (fun p : E × E => bregmanD C.Ψ C.gΨ p.2 p.1) π := by
  refine C.integrable_pair ?_ hsupp
  unfold bregmanD
  refine ContinuousOn.sub (ContinuousOn.sub ?_ ?_) ?_
  · exact C.continuousOn_Ψ.comp continuousOn_snd fun _ hp => hp.2
  · exact C.continuousOn_Ψ.comp continuousOn_fst fun _ hp => hp.1
  · exact ContinuousOn.inner (C.continuousOn_gΨ.comp continuousOn_fst fun _ hp => hp.1)
      (continuous_snd.sub continuous_fst).continuousOn

theorem integrable_sq_disp (hsupp : ∀ᵐ p ∂π, p.1 ∈ C.Θ ∧ p.2 ∈ C.Θ) :
    Integrable (fun p : E × E => ‖p.2 - p.1‖ ^ 2) π :=
  C.integrable_pair ((continuous_snd.sub continuous_fst).norm.pow 2).continuousOn hsupp

theorem integrable_envelope_fst (hsupp : ∀ᵐ p ∂π, p.1 ∈ C.Θ ∧ p.2 ∈ C.Θ) :
    Integrable (fun θ : E => C.m⁻¹ * ‖C.g𝒜 θ‖ ^ 2) (π.map Prod.fst) :=
  integrable_of_continuousOn_of_ae_mem C.compact
    (continuousOn_const.mul (C.continuousOn_g𝒜.norm.pow 2)) (C.ae_fst_mem hsupp)

/-- **First bound of `eq:supp-nonstationary-gap`** on the chart:
`E_π D_Ψ(y,θ) ≤ η (Δ̄_π + d_𝒜)`. -/
theorem coupling_bregman_le (hsupp : ∀ᵐ p ∂π, p.1 ∈ C.Θ ∧ p.2 ∈ C.Θ)
    (hmin : ∀ θ ∈ C.Θ, IsMinOn (C.proxΦ θ) C.Θ (ystar θ))
    (higap : Integrable (fun p : E × E => gap C.Ψ C.𝒜 C.gΨ C.η ystar p.1 p.2) π) :
    ∫ p, bregmanD C.Ψ C.gΨ p.2 p.1 ∂π
      ≤ C.η * (∫ p, gap C.Ψ C.𝒜 C.gΨ C.η ystar p.1 p.2 ∂π + actionDrop π C.𝒜) := by
  have hη := C.η_pos
  have hiD := C.integrable_bregmanD hsupp
  have h1 := C.integrable_𝒜_fst hsupp
  have h2 := C.integrable_𝒜_snd hsupp
  have hpt : ∀ᵐ p ∂π, C.η⁻¹ * bregmanD C.Ψ C.gΨ p.2 p.1
      ≤ gap C.Ψ C.𝒜 C.gΨ C.η ystar p.1 p.2 + C.𝒜 p.1 - C.𝒜 p.2 := by
    filter_upwards [hsupp] with p hp
    have := C.action_bregman_le_gap hp.1 (hmin p.1 hp.1) p.2
    linarith
  have hint := integral_mono_ae (hiD.const_mul C.η⁻¹) ((higap.add h1).sub h2) hpt
  have e1 : ∫ p, (gap C.Ψ C.𝒜 C.gΨ C.η ystar p.1 p.2 + C.𝒜 p.1 - C.𝒜 p.2) ∂π
      = ∫ p, gap C.Ψ C.𝒜 C.gΨ C.η ystar p.1 p.2 ∂π + ∫ p, C.𝒜 p.1 ∂π - ∫ p, C.𝒜 p.2 ∂π := by
    have h' := integral_sub (higap.add h1) h2
    have h'' := integral_add higap h1
    simp only [Pi.add_apply] at h'
    rw [h', h'']
  simp only [Pi.add_apply, Pi.sub_apply] at hint
  rw [e1, integral_const_mul] at hint
  rw [C.actionDrop_eq hsupp]
  have h3 : ∫ p, bregmanD C.Ψ C.gΨ p.2 p.1 ∂π
      = C.η * (C.η⁻¹ * ∫ p, bregmanD C.Ψ C.gΨ p.2 p.1 ∂π) := by
    field_simp
  rw [h3]
  refine mul_le_mul_of_nonneg_left ?_ hη.le
  linarith

/-- The displacement bound against the coupling: `E_π ‖y-θ‖² ≤ (2η/m)(Δ̄_π + d_𝒜)`. -/
theorem coupling_sq_le (hsupp : ∀ᵐ p ∂π, p.1 ∈ C.Θ ∧ p.2 ∈ C.Θ)
    (hmin : ∀ θ ∈ C.Θ, IsMinOn (C.proxΦ θ) C.Θ (ystar θ))
    (higap : Integrable (fun p : E × E => gap C.Ψ C.𝒜 C.gΨ C.η ystar p.1 p.2) π) :
    ∫ p, ‖p.2 - p.1‖ ^ 2 ∂π
      ≤ 2 * C.η / C.m * (∫ p, gap C.Ψ C.𝒜 C.gΨ C.η ystar p.1 p.2 ∂π + actionDrop π C.𝒜) := by
  have hm := C.m_pos
  have hpt : ∀ᵐ p ∂π, ‖p.2 - p.1‖ ^ 2 ≤ 2 / C.m * bregmanD C.Ψ C.gΨ p.2 p.1 := by
    filter_upwards [hsupp] with p hp
    have h := C.bregmanD_floor hp.1 hp.2
    calc ‖p.2 - p.1‖ ^ 2 = 2 / C.m * (C.m / 2 * ‖p.2 - p.1‖ ^ 2) := by field_simp
      _ ≤ 2 / C.m * bregmanD C.Ψ C.gΨ p.2 p.1 := mul_le_mul_of_nonneg_left h (by positivity)
  have hint := integral_mono_ae (C.integrable_sq_disp hsupp)
    ((C.integrable_bregmanD hsupp).const_mul (2 / C.m)) hpt
  rw [integral_const_mul] at hint
  have hD := C.coupling_bregman_le hsupp hmin higap
  calc ∫ p, ‖p.2 - p.1‖ ^ 2 ∂π ≤ 2 / C.m * ∫ p, bregmanD C.Ψ C.gΨ p.2 p.1 ∂π := hint
    _ ≤ 2 / C.m * (C.η * (∫ p, gap C.Ψ C.𝒜 C.gΨ C.η ystar p.1 p.2 ∂π + actionDrop π C.𝒜)) :=
        mul_le_mul_of_nonneg_left hD (by positivity)
    _ = _ := by ring

/-- **Second bound of `eq:supp-nonstationary-gap`** for the inverse-Fisher envelope:
`E_α m⁻¹‖∇𝒜‖² ≤ (C₁ + C₂) Δ̄_π + C₂ d_𝒜`. -/
theorem coupling_envelope_le (hsupp : ∀ᵐ p ∂π, p.1 ∈ C.Θ ∧ p.2 ∈ C.Θ)
    (hmin : ∀ θ ∈ C.Θ, IsMinOn (C.proxΦ θ) C.Θ (ystar θ))
    (hint : ∀ᵐ p ∂π, ystar p.1 ∈ interior C.Θ)
    (higap : Integrable (fun p : E × E => gap C.Ψ C.𝒜 C.gΨ C.η ystar p.1 p.2) π) :
    ∫ θ, C.m⁻¹ * ‖C.g𝒜 θ‖ ^ 2 ∂(π.map Prod.fst)
      ≤ (C.C₁ + C.C₂) * ∫ p, gap C.Ψ C.𝒜 C.gΨ C.η ystar p.1 p.2 ∂π
        + C.C₂ * actionDrop π C.𝒜 := by
  have hm := C.m_pos
  have hη := C.η_pos
  have hienv := C.integrable_envelope_fst hsupp
  rw [integral_map measurable_fst.aemeasurable hienv.aestronglyMeasurable]
  set c₃ : ℝ := 2 * (1 + C.η * C.ℓ) ^ 2 * C.M ^ 2 / (C.m * C.η ^ 2) with hc₃
  have hc₃0 : 0 ≤ c₃ := by positivity
  have hpt : ∀ᵐ p ∂π, C.m⁻¹ * ‖C.g𝒜 p.1‖ ^ 2
      ≤ C.C₁ * gap C.Ψ C.𝒜 C.gΨ C.η ystar p.1 p.2 + c₃ * ‖p.2 - p.1‖ ^ 2 := by
    filter_upwards [hsupp, hint] with p hp hi
    exact C.envelope_le hp.1 hp.2 hi (hmin p.1 hp.1)
  have hienvπ : Integrable (fun p : E × E => C.m⁻¹ * ‖C.g𝒜 p.1‖ ^ 2) π :=
    C.integrable_pair (continuousOn_const.mul
      ((C.continuousOn_g𝒜.comp continuousOn_fst fun _ hp => hp.1).norm.pow 2)) hsupp
  have hisq := C.integrable_sq_disp hsupp
  have h1 := integral_mono_ae hienvπ ((higap.const_mul C.C₁).add (hisq.const_mul c₃)) hpt
  simp only [Pi.add_apply] at h1
  rw [integral_add (higap.const_mul C.C₁) (hisq.const_mul c₃), integral_const_mul C.C₁,
    integral_const_mul c₃] at h1
  have h2 := C.coupling_sq_le hsupp hmin higap
  have h3 := mul_le_mul_of_nonneg_left h2 hc₃0
  have e : c₃ * (2 * C.η / C.m) = C.C₂ := by
    rw [hc₃]; unfold C₂; field_simp; ring
  have e2 : c₃ * (2 * C.η / C.m * (∫ p, gap C.Ψ C.𝒜 C.gΨ C.η ystar p.1 p.2 ∂π
      + actionDrop π C.𝒜)) = C.C₂ * (∫ p, gap C.Ψ C.𝒜 C.gΨ C.η ystar p.1 p.2 ∂π
      + actionDrop π C.𝒜) := by rw [← e]; ring
  rw [e2] at h3
  nlinarith [h1, h3]

/-- **`eq:supp-nonstationary-gap`, second bound, for the inverse-Fisher form `𝔖`**:
`E_α 𝔖 ≤ (C₁ + C₂) Δ̄_π + C₂ d_𝒜`. -/
theorem coupling_stationarityForm_le [FiniteDimensional ℝ E]
    (hsupp : ∀ᵐ p ∂π, p.1 ∈ C.Θ ∧ p.2 ∈ C.Θ)
    (hmin : ∀ θ ∈ C.Θ, IsMinOn (C.proxΦ θ) C.Θ (ystar θ))
    (hint : ∀ᵐ p ∂π, ystar p.1 ∈ interior C.Θ)
    (higap : Integrable (fun p : E × E => gap C.Ψ C.𝒜 C.gΨ C.η ystar p.1 p.2) π)
    (h𝔖m : AEStronglyMeasurable (stationarityForm C.HΨ C.g𝒜) (π.map Prod.fst)) :
    ∫ θ, stationarityForm C.HΨ C.g𝒜 θ ∂(π.map Prod.fst)
      ≤ (C.C₁ + C.C₂) * ∫ p, gap C.Ψ C.𝒜 C.gΨ C.η ystar p.1 p.2 ∂π
        + C.C₂ * actionDrop π C.𝒜 := by
  have hienv := C.integrable_envelope_fst hsupp
  have hbd : ∀ᵐ θ ∂(π.map Prod.fst),
      0 ≤ stationarityForm C.HΨ C.g𝒜 θ ∧ stationarityForm C.HΨ C.g𝒜 θ ≤ C.m⁻¹ * ‖C.g𝒜 θ‖ ^ 2 := by
    filter_upwards [C.ae_fst_mem hsupp] with θ hθ
    have h := inverse_form_bounds (C.HΨ θ) C.m_pos (C.fisher_lower θ hθ) (C.g𝒜 θ)
    exact ⟨h.2.1, h.2.2⟩
  have hi𝔖 : Integrable (stationarityForm C.HΨ C.g𝒜) (π.map Prod.fst) := by
    refine Integrable.mono' hienv h𝔖m ?_
    filter_upwards [hbd] with θ hθ
    rw [Real.norm_eq_abs, abs_of_nonneg hθ.1]
    exact hθ.2
  exact le_trans (integral_mono_ae hi𝔖 hienv (hbd.mono fun _ h => h.2))
    (C.coupling_envelope_le hsupp hmin hint higap)

/-- **`eq:supp-nonstationary-test`** on the chart: for a represented physical test lift `v`
with budget `‖v(θ)‖²_{G(θ)} = ⟪v, G v⟫ ≤ B²` for `α`-almost every source (`G = ∇²Ψ` the Fisher
metric), `E_α |D𝒜[v]|² ≤ B² [(C₁ + C₂) Δ̄_π + C₂ (d_𝒜)₊]`. -/
theorem coupling_physical_test_le (hsupp : ∀ᵐ p ∂π, p.1 ∈ C.Θ ∧ p.2 ∈ C.Θ)
    (hmin : ∀ θ ∈ C.Θ, IsMinOn (C.proxΦ θ) C.Θ (ystar θ))
    (hint : ∀ᵐ p ∂π, ystar p.1 ∈ interior C.Θ)
    (higap : Integrable (fun p : E × E => gap C.Ψ C.𝒜 C.gΨ C.η ystar p.1 p.2) π)
    (v : E → E) (hv : AEStronglyMeasurable (fun θ => ⟪C.g𝒜 θ, v θ⟫) (π.map Prod.fst))
    {b : ℝ} (hb : 0 ≤ b) (hbudget : ∀ᵐ θ ∂(π.map Prod.fst), ⟪v θ, C.HΨ θ (v θ)⟫ ≤ b) :
    ∫ θ, ⟪C.g𝒜 θ, v θ⟫ ^ 2 ∂(π.map Prod.fst)
      ≤ b * ((C.C₁ + C.C₂) * ∫ p, gap C.Ψ C.𝒜 C.gΨ C.η ystar p.1 p.2 ∂π
        + C.C₂ * max (actionDrop π C.𝒜) 0) := by
  have hienv := C.integrable_envelope_fst hsupp
  have hpt : ∀ᵐ θ ∂(π.map Prod.fst), ⟪C.g𝒜 θ, v θ⟫ ^ 2 ≤ b * (C.m⁻¹ * ‖C.g𝒜 θ‖ ^ 2) := by
    filter_upwards [C.ae_fst_mem hsupp, hbudget] with θ hθ hbθ
    have h := inner_sq_le_of_gram_budget C.m_pos (C.HΨ θ)
      (fun x => by rw [real_inner_comm]; exact C.fisher_lower θ hθ x) (C.g𝒜 θ) (v θ) hbθ
    linarith
  have hisq : Integrable (fun θ => ⟪C.g𝒜 θ, v θ⟫ ^ 2) (π.map Prod.fst) := by
    refine Integrable.mono' (hienv.const_mul b) (hv.pow 2) ?_
    filter_upwards [hpt] with θ hθ
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hθ
  have h1 := integral_mono_ae hisq (hienv.const_mul b) hpt
  rw [integral_const_mul] at h1
  have h2 := C.coupling_envelope_le hsupp hmin hint higap
  have hC₂ : 0 ≤ C.C₂ := by unfold C₂; have := C.m_pos; have := C.η_pos; positivity
  have h3 : C.C₂ * actionDrop π C.𝒜 ≤ C.C₂ * max (actionDrop π C.𝒜) 0 :=
    mul_le_mul_of_nonneg_left (le_max_left _ _) hC₂
  calc ∫ θ, ⟪C.g𝒜 θ, v θ⟫ ^ 2 ∂(π.map Prod.fst)
      ≤ b * ∫ θ, C.m⁻¹ * ‖C.g𝒜 θ‖ ^ 2 ∂(π.map Prod.fst) := h1
    _ ≤ b * ((C.C₁ + C.C₂) * ∫ p, gap C.Ψ C.𝒜 C.gΨ C.η ystar p.1 p.2 ∂π
        + C.C₂ * max (actionDrop π C.𝒜) 0) :=
        mul_le_mul_of_nonneg_left (by linarith) hb

/-- **`prop:supp-nonstationary-action-gap`** (convex chart, interior minimizers, any finite
coupling `π` with source `α = π ∘ fst⁻¹` and target `β = π ∘ snd⁻¹` supported in the chart;
no invariant law): with `Δ̄_π = E_π Δ_Ψ`, `d_𝒜 = E_α 𝒜 - E_β 𝒜`,
`C₁ = 4Λ_Φ²/(mμ_Φ)`, `C₂ = 4M²(1+ηℓ)²/(m²η)`:
(1) `E_π D_Ψ(y,θ) ≤ η(Δ̄_π + d_𝒜)`; (2) `E_π ‖y-θ‖² ≤ (2η/m)(Δ̄_π + d_𝒜)`;
(3) `E_α 𝔖 ≤ (C₁+C₂) Δ̄_π + C₂ d_𝒜`; (4) the same with `(d_𝒜)₊`; (5) for every represented
test lift with budget `B²`, `E_α |D𝒜[v]|² ≤ B²[(C₁+C₂) Δ̄_π + C₂ (d_𝒜)₊]`; (6) equal
marginals give `d_𝒜 = 0` (recovering the stationary estimate). -/
theorem chart_nonstationary_action_gap [FiniteDimensional ℝ E]
    (hsupp : ∀ᵐ p ∂π, p.1 ∈ C.Θ ∧ p.2 ∈ C.Θ)
    (hmin : ∀ θ ∈ C.Θ, IsMinOn (C.proxΦ θ) C.Θ (ystar θ))
    (hint : ∀ᵐ p ∂π, ystar p.1 ∈ interior C.Θ)
    (higap : Integrable (fun p : E × E => gap C.Ψ C.𝒜 C.gΨ C.η ystar p.1 p.2) π)
    (h𝔖m : AEStronglyMeasurable (stationarityForm C.HΨ C.g𝒜) (π.map Prod.fst)) :
    (∫ p, bregmanD C.Ψ C.gΨ p.2 p.1 ∂π
        ≤ C.η * (∫ p, gap C.Ψ C.𝒜 C.gΨ C.η ystar p.1 p.2 ∂π + actionDrop π C.𝒜))
    ∧ (∫ p, ‖p.2 - p.1‖ ^ 2 ∂π
        ≤ 2 * C.η / C.m * (∫ p, gap C.Ψ C.𝒜 C.gΨ C.η ystar p.1 p.2 ∂π + actionDrop π C.𝒜))
    ∧ (∫ θ, stationarityForm C.HΨ C.g𝒜 θ ∂(π.map Prod.fst)
        ≤ (C.C₁ + C.C₂) * ∫ p, gap C.Ψ C.𝒜 C.gΨ C.η ystar p.1 p.2 ∂π
          + C.C₂ * actionDrop π C.𝒜)
    ∧ (∫ θ, stationarityForm C.HΨ C.g𝒜 θ ∂(π.map Prod.fst)
        ≤ (C.C₁ + C.C₂) * ∫ p, gap C.Ψ C.𝒜 C.gΨ C.η ystar p.1 p.2 ∂π
          + C.C₂ * max (actionDrop π C.𝒜) 0)
    ∧ (∀ (v : E → E), AEStronglyMeasurable (fun θ => ⟪C.g𝒜 θ, v θ⟫) (π.map Prod.fst) →
        ∀ b : ℝ, 0 ≤ b → (∀ᵐ θ ∂(π.map Prod.fst), ⟪v θ, C.HΨ θ (v θ)⟫ ≤ b) →
        ∫ θ, ⟪C.g𝒜 θ, v θ⟫ ^ 2 ∂(π.map Prod.fst)
          ≤ b * ((C.C₁ + C.C₂) * ∫ p, gap C.Ψ C.𝒜 C.gΨ C.η ystar p.1 p.2 ∂π
            + C.C₂ * max (actionDrop π C.𝒜) 0))
    ∧ (π.map Prod.fst = π.map Prod.snd → actionDrop π C.𝒜 = 0) := by
  have h3 := C.coupling_stationarityForm_le hsupp hmin hint higap h𝔖m
  have hC₂ : 0 ≤ C.C₂ := by unfold C₂; have := C.m_pos; have := C.η_pos; positivity
  refine ⟨C.coupling_bregman_le hsupp hmin higap, C.coupling_sq_le hsupp hmin higap, h3, ?_,
    fun v hv b hb hbudget => C.coupling_physical_test_le hsupp hmin hint higap v hv hb hbudget,
    fun h => actionDrop_eq_zero_of_marginals_eq π C.𝒜 h⟩
  have := mul_le_mul_of_nonneg_left (le_max_left (actionDrop π C.𝒜) 0) hC₂
  linarith

end ProximalChart

/-! ### The stationary theorem -/

namespace ProximalChart

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (C : ProximalChart E)
variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {ν : Measure E} [IsProbabilityMeasure ν] {Kacc : Kernel E E} [IsMarkovKernel Kacc]
  {ystar : E → E}

/-- Transport of the stationary hypotheses to the accepted pair law `ν ⊗ K^acc`. -/
theorem stationary_pair_hyps (hstat : Kacc ∘ₘ ν = ν) (hνΘ : ∀ᵐ θ ∂ν, θ ∈ C.Θ)
    (hint : ∀ᵐ θ ∂ν, ystar θ ∈ interior C.Θ) :
    (∀ᵐ p ∂(ν ⊗ₘ Kacc), p.1 ∈ C.Θ ∧ p.2 ∈ C.Θ)
    ∧ (∀ᵐ p ∂(ν ⊗ₘ Kacc), ystar p.1 ∈ interior C.Θ)
    ∧ (ν ⊗ₘ Kacc).map Prod.fst = ν ∧ actionDrop (ν ⊗ₘ Kacc) C.𝒜 = 0 := by
  have hfst : (ν ⊗ₘ Kacc).map Prod.fst = ν := fst_pair_eq (ν := ν) (K := Kacc)
  have hsnd : (ν ⊗ₘ Kacc).map Prod.snd = ν := snd_pair_eq (ν := ν) (K := Kacc) hstat
  have h1 : ∀ᵐ p ∂(ν ⊗ₘ Kacc), p.1 ∈ C.Θ :=
    ae_of_ae_map measurable_fst.aemeasurable (by rw [hfst]; exact hνΘ)
  have h2 : ∀ᵐ p ∂(ν ⊗ₘ Kacc), p.2 ∈ C.Θ :=
    ae_of_ae_map measurable_snd.aemeasurable (by rw [hsnd]; exact hνΘ)
  refine ⟨h1.and h2, ae_of_ae_map measurable_fst.aemeasurable (by rw [hfst]; exact hint), hfst,
    actionDrop_eq_zero_of_marginals_eq _ _ (hfst.trans hsnd.symm)⟩

/-- **`thm:supp-action-stationarity`** (quantitative accepted-action stationarity on the
compact convex chart).  Let `K = (1-ϑ) I + ϑ K^acc` (`0 < ϑ ≤ 1` state independent) have
stationary law `ν` supported in `Θ`, let `y*_θ` minimize `Φ_θ` over `Θ`, and let the
minimizers of `ν`-almost every source be interior.  Then `ν K^acc = ν` and, with
`Δ̄_Ψ = ∫ Δ_Ψ d(ν ⊗ K^acc)`,
`∫ D_Ψ(y,θ) d(ν⊗K^acc) ≤ η Δ̄_Ψ` (`eq:supp-bregman-bound`),
`∫ ‖y-θ‖² d(ν⊗K^acc) ≤ (2η/m) Δ̄_Ψ` (`eq:supp-displacement-bound`),
`∫ 𝔖 dν ≤ C_{Ψ,𝒜,η} Δ̄_Ψ` with
`C_{Ψ,𝒜,η} = 4Λ_Φ²/(mμ_Φ) + 4M²(1+ηℓ)²/(m²η)` (`eq:supp-stationarity-bound`,
`eq:supp-stationarity-constant`), and `Δ̄_Ψ = 0` forces `∇𝒜 = 0` `ν`-almost surely
(`thm:main-action-stationarity`). -/
theorem chart_action_stationarity [FiniteDimensional ℝ E]
    {ϑ : ℝ} (hϑ0 : 0 < ϑ) (hϑ1 : ϑ ≤ 1) (hlazy : lazyKernel ϑ Kacc ∘ₘ ν = ν)
    (hνΘ : ∀ᵐ θ ∂ν, θ ∈ C.Θ)
    (hmin : ∀ θ ∈ C.Θ, IsMinOn (C.proxΦ θ) C.Θ (ystar θ))
    (hint : ∀ᵐ θ ∂ν, ystar θ ∈ interior C.Θ)
    (higap : Integrable (fun p : E × E => gap C.Ψ C.𝒜 C.gΨ C.η ystar p.1 p.2) (ν ⊗ₘ Kacc))
    (h𝔖m : AEStronglyMeasurable (stationarityForm C.HΨ C.g𝒜) ν) :
    Kacc ∘ₘ ν = ν
    ∧ ∫ p, bregmanD C.Ψ C.gΨ p.2 p.1 ∂(ν ⊗ₘ Kacc)
        ≤ C.η * ∫ p, gap C.Ψ C.𝒜 C.gΨ C.η ystar p.1 p.2 ∂(ν ⊗ₘ Kacc)
    ∧ ∫ p, ‖p.2 - p.1‖ ^ 2 ∂(ν ⊗ₘ Kacc)
        ≤ 2 * C.η / C.m * ∫ p, gap C.Ψ C.𝒜 C.gΨ C.η ystar p.1 p.2 ∂(ν ⊗ₘ Kacc)
    ∧ ∫ θ, stationarityForm C.HΨ C.g𝒜 θ ∂ν
        ≤ C.stationarityConstant * ∫ p, gap C.Ψ C.𝒜 C.gΨ C.η ystar p.1 p.2 ∂(ν ⊗ₘ Kacc)
    ∧ (∫ p, gap C.Ψ C.𝒜 C.gΨ C.η ystar p.1 p.2 ∂(ν ⊗ₘ Kacc) = 0 → ∀ᵐ θ ∂ν, C.g𝒜 θ = 0) := by
  have hstat := comp_eq_of_lazyKernel_comp_eq hϑ0 hϑ1 hlazy
  obtain ⟨hsupp, hint', hfst, hdrop⟩ := C.stationary_pair_hyps hstat hνΘ hint
  have h1 := C.coupling_bregman_le hsupp hmin higap
  have h2 := C.coupling_sq_le hsupp hmin higap
  have h3 := C.coupling_stationarityForm_le hsupp hmin hint' higap (by rw [hfst]; exact h𝔖m)
  have h4 := C.coupling_envelope_le hsupp hmin hint' higap
  rw [hdrop, add_zero] at h1 h2
  rw [hdrop, mul_zero, add_zero, hfst] at h3 h4
  refine ⟨hstat, h1, h2, h3, fun hzero => ?_⟩
  rw [hzero, mul_zero] at h4
  have hienv : Integrable (fun θ : E => C.m⁻¹ * ‖C.g𝒜 θ‖ ^ 2) ν := by
    have := C.integrable_envelope_fst hsupp
    rwa [hfst] at this
  have hm := C.m_pos
  have h0 : ∫ θ, C.m⁻¹ * ‖C.g𝒜 θ‖ ^ 2 ∂ν = 0 :=
    le_antisymm h4 (integral_nonneg fun θ => by positivity)
  rw [integral_eq_zero_iff_of_nonneg (fun θ => by positivity) hienv] at h0
  filter_upwards [h0] with θ hθ
  have hθ' : C.m⁻¹ * ‖C.g𝒜 θ‖ ^ 2 = 0 := hθ
  have h5 : ‖C.g𝒜 θ‖ ^ 2 = 0 := (mul_eq_zero.mp hθ').resolve_left (inv_ne_zero hm.ne')
  exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h5)

/-- `thm:supp-action-stationarity` with the canonical minimizer `y*_θ = argminProx θ` (its
existence and uniqueness are proved, `exists_isMinOn_proxΦ`, `eq_of_isMinOn_proxΦ`). -/
theorem chart_action_stationarity_argmin [FiniteDimensional ℝ E]
    {ϑ : ℝ} (hϑ0 : 0 < ϑ) (hϑ1 : ϑ ≤ 1) (hlazy : lazyKernel ϑ Kacc ∘ₘ ν = ν)
    (hνΘ : ∀ᵐ θ ∂ν, θ ∈ C.Θ)
    (hint : ∀ᵐ θ ∂ν, C.argminProx θ ∈ interior C.Θ)
    (higap : Integrable (fun p : E × E => gap C.Ψ C.𝒜 C.gΨ C.η C.argminProx p.1 p.2)
      (ν ⊗ₘ Kacc))
    (h𝔖m : AEStronglyMeasurable (stationarityForm C.HΨ C.g𝒜) ν) :
    ∫ θ, stationarityForm C.HΨ C.g𝒜 θ ∂ν
      ≤ C.stationarityConstant
          * ∫ p, gap C.Ψ C.𝒜 C.gΨ C.η C.argminProx p.1 p.2 ∂(ν ⊗ₘ Kacc) := by
  have hne : C.Θ.Nonempty := hνΘ.exists
  exact (C.chart_action_stationarity hϑ0 hϑ1 hlazy hνΘ
    (fun θ _ => (C.argminProx_spec hne θ).2) hint higap h𝔖m).2.2.2.1

/-- **`eq:main-physical-stationarity`** (`prop:supp-physical-test-stationarity`, clause 1, on
the compact convex chart): for a represented lift `v` of a physical test with budget
`B² ≥ ⟪v(θ), G(θ) v(θ)⟫` for `ν`-almost every field value (`eq:main-test-lift-budget`,
`G = ∇²Ψ`), `E_ν |D𝒜[v]|² ≤ B² C_X Δ̄_Ψ` with `C_X = C_{Ψ,𝒜,η}` of
`chart_action_stationarity`. -/
theorem chart_physical_test_stationarity
    {ϑ : ℝ} (hϑ0 : 0 < ϑ) (hϑ1 : ϑ ≤ 1) (hlazy : lazyKernel ϑ Kacc ∘ₘ ν = ν)
    (hνΘ : ∀ᵐ θ ∂ν, θ ∈ C.Θ)
    (hmin : ∀ θ ∈ C.Θ, IsMinOn (C.proxΦ θ) C.Θ (ystar θ))
    (hint : ∀ᵐ θ ∂ν, ystar θ ∈ interior C.Θ)
    (higap : Integrable (fun p : E × E => gap C.Ψ C.𝒜 C.gΨ C.η ystar p.1 p.2) (ν ⊗ₘ Kacc))
    (v : E → E) (hv : AEStronglyMeasurable (fun θ => ⟪C.g𝒜 θ, v θ⟫) ν)
    {b : ℝ} (hb : 0 ≤ b) (hbudget : ∀ᵐ θ ∂ν, ⟪v θ, C.HΨ θ (v θ)⟫ ≤ b) :
    ∫ θ, ⟪C.g𝒜 θ, v θ⟫ ^ 2 ∂ν
      ≤ b * (C.stationarityConstant
          * ∫ p, gap C.Ψ C.𝒜 C.gΨ C.η ystar p.1 p.2 ∂(ν ⊗ₘ Kacc)) := by
  have hstat := comp_eq_of_lazyKernel_comp_eq hϑ0 hϑ1 hlazy
  obtain ⟨hsupp, hint', hfst, hdrop⟩ := C.stationary_pair_hyps hstat hνΘ hint
  have h := C.coupling_physical_test_le hsupp hmin hint' higap v (by rw [hfst]; exact hv) hb
    (by rw [hfst]; exact hbudget)
  rw [hdrop, max_self, mul_zero, add_zero, hfst] at h
  exact h

/-- `eq:main-physical-stationarity` with the manuscript's literal hypotheses on the support:
interiority of `y*_θ` for every `θ ∈ supp ν` and the budget
`B² = sup_{θ ∈ supp ν} ‖v(θ)‖²_{G(θ)} ≤ b` (`eq:main-test-lift-budget`). -/
theorem chart_physical_test_stationarity_support
    {ϑ : ℝ} (hϑ0 : 0 < ϑ) (hϑ1 : ϑ ≤ 1) (hlazy : lazyKernel ϑ Kacc ∘ₘ ν = ν)
    (hνΘ : ∀ᵐ θ ∂ν, θ ∈ C.Θ)
    (hmin : ∀ θ ∈ C.Θ, IsMinOn (C.proxΦ θ) C.Θ (ystar θ))
    (hint : ∀ θ ∈ ν.support, ystar θ ∈ interior C.Θ)
    (higap : Integrable (fun p : E × E => gap C.Ψ C.𝒜 C.gΨ C.η ystar p.1 p.2) (ν ⊗ₘ Kacc))
    (v : E → E) (hv : AEStronglyMeasurable (fun θ => ⟪C.g𝒜 θ, v θ⟫) ν)
    {b : ℝ} (hb : 0 ≤ b) (hbudget : ∀ θ ∈ ν.support, ⟪v θ, C.HΨ θ (v θ)⟫ ≤ b) :
    ∫ θ, ⟪C.g𝒜 θ, v θ⟫ ^ 2 ∂ν
      ≤ b * (C.stationarityConstant
          * ∫ p, gap C.Ψ C.𝒜 C.gΨ C.η ystar p.1 p.2 ∂(ν ⊗ₘ Kacc)) := by
  have hsupp : ∀ᵐ θ ∂ν, θ ∈ ν.support := Measure.support_mem_ae
  exact C.chart_physical_test_stationarity hϑ0 hϑ1 hlazy hνΘ hmin
    (hsupp.mono fun θ hθ => hint θ hθ) higap v hv hb (hsupp.mono fun θ hθ => hbudget θ hθ)

/-- `thm:supp-action-stationarity` with interiority of `y*_θ` assumed, as in the manuscript,
for every supported source `θ ∈ supp ν`. -/
theorem chart_action_stationarity_support [FiniteDimensional ℝ E]
    {ϑ : ℝ} (hϑ0 : 0 < ϑ) (hϑ1 : ϑ ≤ 1) (hlazy : lazyKernel ϑ Kacc ∘ₘ ν = ν)
    (hνΘ : ∀ᵐ θ ∂ν, θ ∈ C.Θ)
    (hmin : ∀ θ ∈ C.Θ, IsMinOn (C.proxΦ θ) C.Θ (ystar θ))
    (hint : ∀ θ ∈ ν.support, ystar θ ∈ interior C.Θ)
    (higap : Integrable (fun p : E × E => gap C.Ψ C.𝒜 C.gΨ C.η ystar p.1 p.2) (ν ⊗ₘ Kacc))
    (h𝔖m : AEStronglyMeasurable (stationarityForm C.HΨ C.g𝒜) ν) :
    ∫ θ, stationarityForm C.HΨ C.g𝒜 θ ∂ν
      ≤ C.stationarityConstant * ∫ p, gap C.Ψ C.𝒜 C.gΨ C.η ystar p.1 p.2 ∂(ν ⊗ₘ Kacc) := by
  have hsupp : ∀ᵐ θ ∂ν, θ ∈ ν.support := Measure.support_mem_ae
  exact (C.chart_action_stationarity hϑ0 hϑ1 hlazy hνΘ hmin
    (hsupp.mono fun θ hθ => hint θ hθ) higap h𝔖m).2.2.2.1

end ProximalChart

/-! ### Non-vacuity -/

/-- A non-trivial chart: `Θ = [-1, 1] ⊂ ℝ`, `Ψ(x) = x²/2` (`G = 1`), `𝒜(x) = x²/2`
(`D²𝒜 = 1 = 1·G`, so `L = 1`, `λ = 0`), `η = 1/2`. -/
noncomputable def exampleChart : ProximalChart ℝ where
  Θ := Set.Icc (-1) 1
  U := Set.univ
  Ψ := fun x => x ^ 2 / 2
  𝒜 := fun x => x ^ 2 / 2
  gΨ := fun x => x
  g𝒜 := fun x => x
  HΨ := fun _ => ContinuousLinearMap.id ℝ ℝ
  H𝒜 := fun _ => ContinuousLinearMap.id ℝ ℝ
  m := 1
  M := 1
  lam := 0
  L := 1
  η := 1 / 2
  convex := convex_Icc _ _
  compact := isCompact_Icc
  isOpen_U := isOpen_univ
  subset_U := Set.subset_univ _
  hasGradient_Ψ := fun x _ => by
    have h := ((hasDerivAt_pow 2 x).div_const 2).hasGradientAt
    have e : (starRingEnd ℝ) ((2 : ℕ) * x ^ (2 - 1) / 2) = x := by simp
    rwa [e] at h
  hasGradient_𝒜 := fun x _ => by
    have h := ((hasDerivAt_pow 2 x).div_const 2).hasGradientAt
    have e : (starRingEnd ℝ) ((2 : ℕ) * x ^ (2 - 1) / 2) = x := by simp
    rwa [e] at h
  hasHessian_Ψ := fun x _ => hasFDerivAt_id x
  hasHessian_𝒜 := fun x _ => hasFDerivAt_id x
  m_pos := one_pos
  fisher_lower := fun _ _ v => by simp [real_inner_self_eq_norm_sq]
  fisher_upper := fun _ _ v => by simp [real_inner_self_eq_norm_sq]
  lam_nonneg := le_rfl
  L_nonneg := zero_le_one
  action_lower := fun _ _ v => by simp only [neg_zero, zero_mul]; simp [real_inner_self_eq_norm_sq]; positivity
  action_upper := fun _ _ v => by simp
  η_pos := by norm_num
  η_lam_lt_one := by norm_num

/-- In the example chart the proximal minimizer of a source `θ ∈ [-1,1]` is `2θ/3`, an
interior point: the interiority hypothesis is satisfiable. -/
example (θ : ℝ) (hθ : θ ∈ Set.Icc (-1 : ℝ) 1) :
    (2 * θ / 3) ∈ interior exampleChart.Θ
    ∧ IsMinOn (exampleChart.proxΦ θ) exampleChart.Θ (2 * θ / 3) := by
  have hΘ : exampleChart.Θ = Set.Icc (-1) 1 := rfl
  refine ⟨?_, ?_⟩
  · rw [hΘ, interior_Icc]
    constructor <;> linarith [hθ.1, hθ.2]
  · intro z _
    simp only [Set.mem_setOf_eq, ProximalChart.proxΦ, prox, bregmanD, exampleChart]
    simp only [RCLike.inner_apply, conj_trivial]
    nlinarith [sq_nonneg (z - 2 * θ / 3)]

end ChartStationarity
end RenewalGeometry
