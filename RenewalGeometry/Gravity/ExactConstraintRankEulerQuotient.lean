/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.SupplementExactConstraintRankExact

/-!
# Finite characteristic quotient on a regular one-null branch: Euler homogeneity and the quotient
  (`thm:supp-exact-constraint-rank`, `eq:supp-exact-canonical-objects`,
  `eq:supp-exact-homogeneity`, `eq:supp-exact-dirac-matrix`, `eq:supp-exact-dirac-rank`;
  emergent-spacetime manuscript)

`RenewalGeometry.Gravity.SupplementExactConstraintRankExact` proves the block-matrix kernel and
rank of the Dirac matrix `𝔇 = [[0, -M], [M, 𝒜]]` *given* `𝒜λ = B`.  This file derives the
remaining two pieces from the canonical Hamiltonian:

## (i) `𝒜λ = B` from multiplier homogeneity

Let `X ∈ E` (the paper's `ℝ^{12V}`) and `λ ∈ L` (`ℝ^{4V}`), both finite-dimensional real inner
product spaces, `H : E → L → ℝ` the canonical Hamiltonian with `H(X, cλ) = c H(X, λ)` for
`c > 0`, `P(X, ·) = ∇_λ H(X, ·)`, `F^{can} = 𝕁 ∇_X H`, `B = D_X P F^{can}`, `M = D_λ P`,
`𝒜 = D_X P 𝕁 (D_X P)^*` (`eq:supp-exact-canonical-objects`, `eq:supp-exact-dirac-matrix`).

* `euler_identity` — Euler's identity `H(X, λ) = ⟪λ, P(X, λ)⟫` (derivative of `c ↦ H(X, cλ)` at
  `c = 1`).
* `hasGradientAt_X_eq_adjoint` — `∇_X H(X, λ) = (D_X P)^* λ` (differentiate the Euler identity
  in `X`).
* `bracket_lambda_eq_source` — hence `𝒜λ = B`, with `B` built from the actual gradient
  `∇_X H` (Mathlib's `gradient`).
* `multiplierHessian_symm` — `M = D_λ P` is self-adjoint (`M` is the `λ`-Hessian of `H`).

## (ii) The local characteristic quotient by rank–nullity

The extended phase is `W = E × L × L ∋ (X, λ, μ)` (`μ` the multiplier momenta; dimension
`12V + 4V + 4V = 20V`).  The linearised primary and secondary constraints `μ = 0`, `P = 0` give
`constraintMap (ξ, η, ζ) = (ζ, D_X P ξ + M η)`; it is onto because `D_X P` is onto
(`constraintMap_surjective`), so `dim ker = dim E` by rank–nullity (`finrank_ker_constraintMap`).
The Hamiltonian vector field of the constraint combination `⟨r, μ⟩ + ⟨s, P⟩` is
`characteristicMap (r, s) = (𝕁 (D_X P)^* s, r, -M^* s)`; with `M` self-adjoint,
`constraintMap ∘ characteristicMap = 𝔇` (`constraintMap_comp_characteristicMap`), so
`characteristicMap` maps `ker 𝔇` injectively (𝕁 injective, `D_X P` onto) into the linearised
constraint surface: the characteristic directions.  The local characteristic quotient
`charQuotient = ker(constraintMap) ⧸ characteristic directions` then has
`dim = dim E - 2` (`finrank_charQuotient`), i.e. `12V - 2`.

* `supp_exact_constraint_rank` — **`thm:supp-exact-constraint-rank`** assembled: under
  multiplier homogeneity, `D_X P` onto, `ker M = span{λ}` (`λ ≠ 0`) and solvability of
  `B + M λ̇ = 0`, the kernel of `𝔇` is `span{(λ, 0), (-M^†B, λ)}` (any particular solution
  `r₀ = -λ̇` of `M r₀ = B`), `rank 𝔇 = 8V - 2`, and the characteristic quotient has dimension
  `12V - 2`, where `V` enters only through `dim E = 12V`, `dim L = 4V`.
* `supp_exact_constraint_rank_nonvacuous` — the hypotheses are jointly satisfiable
  (`E = ℂ`, `L = ℝ`, `H(X, λ) = λ re X`, `𝕁 = i`).
-/

open scoped InnerProductSpace RealInnerProductSpace Gradient
open Filter Topology Module

namespace RenewalGeometry
namespace ExactConstraintRank

variable {E L : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup L] [InnerProductSpace ℝ L] [FiniteDimensional ℝ L]

/-! ### (i) Euler homogeneity -/

/-- **Euler's identity** for a positively `1`-homogeneous function of the multiplier:
if `H(X, cλ) = c H(X, λ)` for `c > 0` and `P = ∇_λ H` at `λ`, then `H(X, λ) = ⟪λ, P(X, λ)⟫`. -/
theorem euler_identity (Hx : L → ℝ) (lam p : L)
    (hhom : ∀ c : ℝ, 0 < c → Hx (c • lam) = c * Hx lam) (hP : HasGradientAt Hx p lam) :
    Hx lam = ⟪lam, p⟫ := by
  have hline : HasDerivAt (fun c : ℝ => c • lam) lam 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).smul_const lam
  have hcomp : HasDerivAt (fun c : ℝ => Hx (c • lam))
      (InnerProductSpace.toDual ℝ L p lam) 1 :=
    hP.hasFDerivAt.comp_hasDerivAt_of_eq 1 hline (one_smul ℝ lam).symm
  have hlin : HasDerivAt (fun c : ℝ => c * Hx lam) (Hx lam) 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).mul_const (Hx lam)
  have hev : (fun c : ℝ => Hx (c • lam)) =ᶠ[𝓝 1] fun c => c * Hx lam := by
    filter_upwards [lt_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with c hc
    exact hhom c hc
  have h2 : HasDerivAt (fun c : ℝ => Hx (c • lam)) (Hx lam) 1 := hlin.congr_of_eventuallyEq hev
  have := hcomp.unique h2
  rw [InnerProductSpace.toDual_apply_apply] at this
  rw [← this, real_inner_comm]

/-- **`∇_X H = (D_X P)^* λ`.**  Differentiating the Euler identity `H(X, λ) = ⟪λ, P(X, λ)⟫` in
`X` (with `λ` fixed) gives the `X`-gradient of the Hamiltonian. -/
theorem hasGradientAt_X_eq_adjoint (H : E → L → ℝ) (P : E → L → L) (lam : L) (X₀ : E)
    (DXP : E →L[ℝ] L)
    (hhom : ∀ X, ∀ c : ℝ, 0 < c → H X (c • lam) = c * H X lam)
    (hP : ∀ X, HasGradientAt (H X) (P X lam) lam)
    (hDXP : HasFDerivAt (fun X => P X lam) DXP X₀) :
    HasGradientAt (fun X => H X lam) (ContinuousLinearMap.adjoint DXP lam) X₀ := by
  have hfun : (fun X => H X lam) = fun X => innerSL ℝ lam (P X lam) := by
    funext X
    rw [euler_identity (H X) lam (P X lam) (hhom X) (hP X), innerSL_apply_apply]
  rw [hfun, hasGradientAt_iff_hasFDerivAt]
  have h := (innerSL ℝ lam).hasFDerivAt.comp X₀ hDXP
  refine h.congr_fderiv ?_
  ext v
  simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, innerSL_apply_apply,
    InnerProductSpace.toDual_apply_apply, ContinuousLinearMap.adjoint_inner_left]

/-- The constraint bracket `𝒜 = D_X P 𝕁 (D_X P)^*` (`eq:supp-exact-dirac-matrix`). -/
noncomputable def bracket (DXP : E →L[ℝ] L) (J : E →L[ℝ] E) : L →L[ℝ] L :=
  DXP ∘L J ∘L ContinuousLinearMap.adjoint DXP

/-- The consistency source `B = D_X P F^{can}` with `F^{can} = 𝕁 ∇_X H`
(`eq:supp-exact-canonical-objects`), built from the actual `X`-gradient of `H`. -/
noncomputable def source (H : E → L → ℝ) (lam : L) (X₀ : E) (DXP : E →L[ℝ] L)
    (J : E →L[ℝ] E) : L :=
  DXP (J (∇ (fun X => H X lam) X₀))

/-- **`𝒜λ = B` from homogeneity** (`thm:supp-exact-constraint-rank`, proof step). -/
theorem bracket_lambda_eq_source (H : E → L → ℝ) (P : E → L → L) (lam : L) (X₀ : E)
    (DXP : E →L[ℝ] L) (J : E →L[ℝ] E)
    (hhom : ∀ X, ∀ c : ℝ, 0 < c → H X (c • lam) = c * H X lam)
    (hP : ∀ X, HasGradientAt (H X) (P X lam) lam)
    (hDXP : HasFDerivAt (fun X => P X lam) DXP X₀) :
    bracket DXP J lam = source H lam X₀ DXP J := by
  unfold bracket source
  rw [(hasGradientAt_X_eq_adjoint H P lam X₀ DXP hhom hP hDXP).gradient]
  rfl

/-- **`M = D_λ P` is self-adjoint**: it is the `λ`-Hessian of `H(X₀, ·)`. -/
theorem multiplierHessian_symm (Hx : L → ℝ) (Px : L → L) (lam : L) (M : L →L[ℝ] L)
    (hP : ∀ᶠ μ in 𝓝 lam, HasGradientAt Hx (Px μ) μ) (hM : HasFDerivAt Px M lam) (v w : L) :
    ⟪M v, w⟫ = ⟪v, M w⟫ := by
  have hf : ∀ᶠ μ in 𝓝 lam, HasFDerivAt Hx (innerSL ℝ (Px μ)) μ := by
    filter_upwards [hP] with μ hμ
    refine hμ.hasFDerivAt.congr_fderiv ?_
    ext u
    simp only [InnerProductSpace.toDual_apply_apply, innerSL_apply_apply]
  have hx : HasFDerivAt (fun μ => innerSL ℝ (Px μ)) ((innerSL ℝ : L →L[ℝ] L →L[ℝ] ℝ) ∘L M) lam :=
    (innerSL ℝ : L →L[ℝ] L →L[ℝ] ℝ).hasFDerivAt.comp lam hM
  have := second_derivative_symmetric_of_eventually_of_real hf hx v w
  change ⟪M v, w⟫ = ⟪M w, v⟫ at this
  rw [this, real_inner_comm]

theorem adjoint_eq_self_of_symm {M : L →L[ℝ] L} (hM : ∀ v w, ⟪M v, w⟫ = ⟪v, M w⟫) :
    ContinuousLinearMap.adjoint M = M := by
  ext v
  refine ext_inner_right ℝ fun w => ?_
  rw [ContinuousLinearMap.adjoint_inner_left]
  exact (hM v w).symm

/-! ### (ii) The extended phase and the characteristic quotient -/

/-- The linearised primary and secondary constraints on the extended phase `E × L × L`:
`(ξ, η, ζ) ↦ (ζ, D_X P ξ + M η)` (primary `μ = 0`, secondary `P = 0`). -/
noncomputable def constraintMap (DXP : E →L[ℝ] L) (M : L →L[ℝ] L) : E × L × L →ₗ[ℝ] L × L :=
  LinearMap.prod ((LinearMap.snd ℝ L L).comp (LinearMap.snd ℝ E (L × L)))
    ((DXP : E →ₗ[ℝ] L).comp (LinearMap.fst ℝ E (L × L)) +
      (M : L →ₗ[ℝ] L).comp ((LinearMap.fst ℝ L L).comp (LinearMap.snd ℝ E (L × L))))

@[simp] theorem constraintMap_apply (DXP : E →L[ℝ] L) (M : L →L[ℝ] L) (p : E × L × L) :
    constraintMap DXP M p = (p.2.2, DXP p.1 + M p.2.1) := rfl

/-- The Hamiltonian vector field of the constraint combination `⟨r, μ⟩ + ⟨s, P⟩`:
`(r, s) ↦ (𝕁 (D_X P)^* s, r, -M^* s)` — the characteristic directions. -/
noncomputable def characteristicMap (DXP : E →L[ℝ] L) (M : L →L[ℝ] L) (J : E →L[ℝ] E) :
    L × L →ₗ[ℝ] E × L × L :=
  LinearMap.prod (((J ∘L ContinuousLinearMap.adjoint DXP : L →L[ℝ] E) : L →ₗ[ℝ] E).comp
      (LinearMap.snd ℝ L L))
    (LinearMap.prod (LinearMap.fst ℝ L L)
      (-((ContinuousLinearMap.adjoint M : L →L[ℝ] L) : L →ₗ[ℝ] L).comp (LinearMap.snd ℝ L L)))

@[simp] theorem characteristicMap_apply (DXP : E →L[ℝ] L) (M : L →L[ℝ] L) (J : E →L[ℝ] E)
    (k : L × L) :
    characteristicMap DXP M J k =
      (J (ContinuousLinearMap.adjoint DXP k.2), k.1, -(ContinuousLinearMap.adjoint M k.2)) := rfl

/-- With `M` self-adjoint, the linearised constraints along the characteristic field are the
Dirac matrix: `constraintMap ∘ characteristicMap = 𝔇`. -/
theorem constraintMap_comp_characteristicMap (DXP : E →L[ℝ] L) (M : L →L[ℝ] L) (J : E →L[ℝ] E)
    (hMsa : ContinuousLinearMap.adjoint M = M) :
    (constraintMap DXP M).comp (characteristicMap DXP M J) =
      diracMatrix (M : L →ₗ[ℝ] L) (bracket DXP J : L →ₗ[ℝ] L) := by
  apply LinearMap.ext
  rintro ⟨r, s⟩
  refine Prod.ext ?_ ?_
  · simp [hMsa]
  · simp only [LinearMap.comp_apply, characteristicMap_apply, constraintMap_apply,
      diracMatrix_apply, bracket, ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply]
    abel

/-- `D_X P` onto makes the linearised constraint map onto. -/
theorem constraintMap_surjective (DXP : E →L[ℝ] L) (M : L →L[ℝ] L)
    (honto : Function.Surjective DXP) : Function.Surjective (constraintMap DXP M) := by
  rintro ⟨a, b⟩
  obtain ⟨ξ, hξ⟩ := honto b
  exact ⟨(ξ, 0, a), by simp [hξ]⟩

/-- **Rank–nullity**: the linearised constraint surface has dimension `dim E`
(`20V - 8V = 12V`). -/
theorem finrank_ker_constraintMap (DXP : E →L[ℝ] L) (M : L →L[ℝ] L)
    (honto : Function.Surjective DXP) :
    finrank ℝ (LinearMap.ker (constraintMap DXP M)) = finrank ℝ E := by
  have h := LinearMap.finrank_range_add_finrank_ker (constraintMap DXP M)
  rw [LinearMap.range_eq_top.mpr (constraintMap_surjective DXP M honto), finrank_top,
    finrank_prod, finrank_prod, finrank_prod] at h
  omega

/-- `D_X P` onto makes its adjoint injective. -/
theorem adjoint_injective_of_surjective (DXP : E →L[ℝ] L) (honto : Function.Surjective DXP) :
    Function.Injective (ContinuousLinearMap.adjoint DXP) := by
  intro s t hst
  obtain ⟨ξ, hξ⟩ := honto (s - t)
  have hs : ContinuousLinearMap.adjoint DXP (s - t) = 0 := by rw [map_sub, hst, sub_self]
  have : ⟪s - t, s - t⟫ = 0 := by
    calc ⟪s - t, s - t⟫ = ⟪s - t, DXP ξ⟫ := by rw [hξ]
      _ = ⟪ContinuousLinearMap.adjoint DXP (s - t), ξ⟫ :=
          (ContinuousLinearMap.adjoint_inner_left _ _ _).symm
      _ = 0 := by rw [hs, inner_zero_left]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp this)

/-- The characteristic map is injective (`𝕁` injective, `D_X P` onto). -/
theorem characteristicMap_injective (DXP : E →L[ℝ] L) (M : L →L[ℝ] L) (J : E →L[ℝ] E)
    (honto : Function.Surjective DXP) (hJ : Function.Injective J) :
    Function.Injective (characteristicMap DXP M J) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  rintro ⟨r, s⟩ h
  have h1 : J (ContinuousLinearMap.adjoint DXP s) = 0 := congrArg Prod.fst h
  have h2 : r = 0 := congrArg (fun p : E × L × L => p.2.1) h
  have hs : ContinuousLinearMap.adjoint DXP s = 0 := hJ (by rw [h1, map_zero])
  have : s = 0 := adjoint_injective_of_surjective DXP honto (by rw [hs, map_zero])
  rw [h2, this]; rfl

/-- The characteristic directions: the image of `ker 𝔇` under the characteristic field. -/
noncomputable def characteristicDirections (DXP : E →L[ℝ] L) (M : L →L[ℝ] L) (J : E →L[ℝ] E) :
    Submodule ℝ (E × L × L) :=
  (LinearMap.ker (diracMatrix (M : L →ₗ[ℝ] L) (bracket DXP J : L →ₗ[ℝ] L))).map
    (characteristicMap DXP M J)

theorem characteristicDirections_le (DXP : E →L[ℝ] L) (M : L →L[ℝ] L) (J : E →L[ℝ] E)
    (hMsa : ContinuousLinearMap.adjoint M = M) :
    characteristicDirections DXP M J ≤ LinearMap.ker (constraintMap DXP M) := by
  rintro _ ⟨k, hk, rfl⟩
  rw [LinearMap.mem_ker, ← LinearMap.comp_apply, constraintMap_comp_characteristicMap DXP M J hMsa]
  exact hk

/-- **The local characteristic quotient**: the linearised constraint surface modulo the
characteristic directions. -/
abbrev charQuotient (DXP : E →L[ℝ] L) (M : L →L[ℝ] L) (J : E →L[ℝ] E) : Type _ :=
  LinearMap.ker (constraintMap DXP M) ⧸
    (characteristicDirections DXP M J).comap (LinearMap.ker (constraintMap DXP M)).subtype

/-- **Dimension of the characteristic quotient** (rank–nullity, not arithmetic):
`dim(charQuotient) + 2 = dim E`, given `D_X P` onto, `𝕁` injective, `M` self-adjoint and a
two-dimensional `ker 𝔇`. -/
theorem finrank_charQuotient (DXP : E →L[ℝ] L) (M : L →L[ℝ] L) (J : E →L[ℝ] E)
    (honto : Function.Surjective DXP) (hJ : Function.Injective J)
    (hMsa : ContinuousLinearMap.adjoint M = M)
    (hker2 : finrank ℝ (LinearMap.ker (diracMatrix (M : L →ₗ[ℝ] L) (bracket DXP J : L →ₗ[ℝ] L)))
      = 2) :
    finrank ℝ (charQuotient DXP M J) + 2 = finrank ℝ E := by
  have hle := characteristicDirections_le DXP M J hMsa
  have h1 := Submodule.finrank_quotient_add_finrank
    ((characteristicDirections DXP M J).comap (LinearMap.ker (constraintMap DXP M)).subtype)
  have h2 : finrank ℝ ((characteristicDirections DXP M J).comap
      (LinearMap.ker (constraintMap DXP M)).subtype) = 2 := by
    rw [(Submodule.comapSubtypeEquivOfLe hle).finrank_eq]
    unfold characteristicDirections
    rw [← (Submodule.equivMapOfInjective _ (characteristicMap_injective DXP M J honto hJ)
      _).finrank_eq, hker2]
  rw [h2, finrank_ker_constraintMap DXP M honto] at h1
  exact h1

/-! ### The theorem -/

/-- **`thm:supp-exact-constraint-rank`.**  Let `H : E → L → ℝ` be the canonical Hamiltonian,
positively `1`-homogeneous in the multiplier (`eq:supp-exact-homogeneity`), with
`P = ∇_λ H` (at the branch multiplier `λ` for every `X`, and near `λ` at the base point `X₀`),
`D_X P` its `X`-derivative at `(X₀, λ)` — **onto** — and `M = D_λ P` its multiplier derivative,
with `ker M = span{λ}`, `λ ≠ 0`, and the first consistency condition `B + M λ̇ = 0` solvable,
where `B = D_X P 𝕁 ∇_X H` and `𝕁` is injective.  Then, with `𝒜 = D_X P 𝕁 (D_X P)^*`:
* `𝒜 λ = B` (derived from homogeneity);
* `ker 𝔇 = span{(λ, 0), (-r₀, λ)}` with `r₀ = -λ̇` (i.e. `M r₀ = B`, the paper's `M^†B`);
* `rank 𝔇 = 8V - 2` and the local characteristic quotient has dimension `12V - 2`, when
  `dim E = 12V`, `dim L = 4V`. -/
theorem supp_exact_constraint_rank (V : ℕ) (hE : finrank ℝ E = 12 * V) (hL : finrank ℝ L = 4 * V)
    (H : E → L → ℝ) (P : E → L → L) (lam : L) (X₀ : E) (J : E →L[ℝ] E)
    (DXP : E →L[ℝ] L) (M : L →L[ℝ] L)
    (hhom : ∀ X, ∀ μ : L, ∀ c : ℝ, 0 < c → H X (c • μ) = c * H X μ)
    (hP : ∀ X, HasGradientAt (H X) (P X lam) lam)
    (hPloc : ∀ᶠ μ in 𝓝 lam, HasGradientAt (H X₀) (P X₀ μ) μ)
    (hDXP : HasFDerivAt (fun X => P X lam) DXP X₀) (honto : Function.Surjective DXP)
    (hM : HasFDerivAt (P X₀) M lam)
    (hker : LinearMap.ker (M : L →ₗ[ℝ] L) = Submodule.span ℝ {lam}) (hlam : lam ≠ 0)
    (hJ : Function.Injective J)
    (lamDot : L) (hcons : source H lam X₀ DXP J + M lamDot = 0) :
    bracket DXP J lam = source H lam X₀ DXP J ∧
    LinearMap.ker (diracMatrix (M : L →ₗ[ℝ] L) (bracket DXP J : L →ₗ[ℝ] L))
      = Submodule.span ℝ {(lam, (0 : L)), (lamDot, lam)} ∧
    finrank ℝ (LinearMap.range (diracMatrix (M : L →ₗ[ℝ] L) (bracket DXP J : L →ₗ[ℝ] L)))
      = 8 * V - 2 ∧
    finrank ℝ (charQuotient DXP M J) = 12 * V - 2 := by
  have hAB := bracket_lambda_eq_source H P lam X₀ DXP J (fun X => hhom X lam) hP hDXP
  have hr₀ : (M : L →ₗ[ℝ] L) (-lamDot) = source H lam X₀ DXP J := by
    have h1 : M lamDot = -source H lam X₀ DXP J := by
      rw [eq_neg_iff_add_eq_zero, add_comm]; exact hcons
    rw [map_neg, ContinuousLinearMap.coe_coe, h1, neg_neg]
  have hker' := ker_diracMatrix (M : L →ₗ[ℝ] L) (bracket DXP J : L →ₗ[ℝ] L) hker
    (B := source H lam X₀ DXP J) hAB hr₀
  rw [neg_neg] at hker'
  have hrank := finrank_range_diracMatrix_of_dim (M : L →ₗ[ℝ] L) (bracket DXP J : L →ₗ[ℝ] L)
    V hL hker hlam hAB hr₀
  have hker2 := finrank_ker_diracMatrix (M : L →ₗ[ℝ] L) (bracket DXP J : L →ₗ[ℝ] L) hker hlam
    hAB hr₀
  have hsym := multiplierHessian_symm (H X₀) (P X₀) lam M hPloc hM
  have hq := finrank_charQuotient DXP M J honto hJ (adjoint_eq_self_of_symm hsym) hker2
  refine ⟨hAB, hker', hrank, ?_⟩
  omega

/-! ### Non-vacuity -/

/-- **Non-vacuity**: `E = ℂ` (as a real inner product space), `L = ℝ`,
`H(X, λ) = λ · re X` (positively `1`-homogeneous), `P(X, λ) = re X`, `D_X P = re` (onto),
`M = 0` (`ker M = ℝ = span{1}`), `𝕁 = i·` (injective), `λ̇ = 0`. -/
theorem supp_exact_constraint_rank_nonvacuous :
    ∃ (H : ℂ → ℝ → ℝ) (P : ℂ → ℝ → ℝ) (J : ℂ →L[ℝ] ℂ) (DXP : ℂ →L[ℝ] ℝ),
      (∀ X, ∀ μ : ℝ, ∀ c : ℝ, 0 < c → H X (c • μ) = c * H X μ) ∧
      (∀ X, HasGradientAt (H X) (P X 1) 1) ∧
      (∀ᶠ μ in 𝓝 (1 : ℝ), HasGradientAt (H 0) (P 0 μ) μ) ∧
      HasFDerivAt (fun X => P X 1) DXP 0 ∧ Function.Surjective DXP ∧
      HasFDerivAt (P 0) (0 : ℝ →L[ℝ] ℝ) 1 ∧
      LinearMap.ker ((0 : ℝ →L[ℝ] ℝ) : ℝ →ₗ[ℝ] ℝ) = Submodule.span ℝ {(1 : ℝ)} ∧
      Function.Injective J ∧
      source H 1 0 DXP J + (0 : ℝ →L[ℝ] ℝ) 0 = 0 := by
  refine ⟨fun X μ => μ * X.re, fun X _ => X.re, Complex.I • ContinuousLinearMap.id ℝ ℂ,
    Complex.reCLM, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro X μ c _; simp [smul_eq_mul]; ring
  · intro X
    have : HasDerivAt (fun μ : ℝ => μ * X.re) X.re 1 := by
      simpa using (hasDerivAt_id (1 : ℝ)).mul_const X.re
    simpa using this.hasGradientAt
  · filter_upwards with μ
    have : HasDerivAt (fun μ : ℝ => μ * (0 : ℂ).re) (0 : ℂ).re μ := by
      simpa using (hasDerivAt_id μ).mul_const (0 : ℂ).re
    simpa using this.hasGradientAt
  · exact Complex.reCLM.hasFDerivAt
  · intro x; exact ⟨x, by simp⟩
  · exact hasFDerivAt_const _ _
  · ext x; simp
  · intro x y h
    have := congrArg (fun z => -Complex.I * z) h
    simpa [← mul_assoc] using this
  · simp only [zero_apply, add_zero, source]
    have hg : ∇ (fun X : ℂ => (1 : ℝ) * X.re) (0 : ℂ) = 1 := by
      have h0 : HasFDerivAt (fun X : ℂ => (1 : ℝ) * X.re) Complex.reCLM 0 := by
        have hfe : (fun X : ℂ => (1 : ℝ) * X.re) = Complex.reCLM := by
          funext X; simp
        rw [hfe]; exact Complex.reCLM.hasFDerivAt
      have : HasGradientAt (fun X : ℂ => (1 : ℝ) * X.re) 1 0 := by
        rw [hasGradientAt_iff_hasFDerivAt]
        refine h0.congr_fderiv ?_
        ext z
        simp [InnerProductSpace.toDual_apply_apply, Complex.inner]
      exact this.gradient
    rw [hg]
    simp

end ExactConstraintRank
end RenewalGeometry
