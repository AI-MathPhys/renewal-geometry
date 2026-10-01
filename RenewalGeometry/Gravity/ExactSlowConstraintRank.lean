/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.ExactSlowBranchData

/-!
# Rank and cokernel of the leading slow constraint
  (`prop:supp-exact-slow-rank`, `eq:supp-exact-critical-dimensions`,
  `eq:supp-exact-weak-decomposition`; emergent-spacetime manuscript)

The leading slow constraint is `Φ₀(x, z) = C_red x + B z` on `ℝ²⁹⁴ ⊕ ℝ²⁹`
(`ExactSlowBranch.leadingConstraint`).  The proposition assumes the direct decomposition
`ℝ²⁹ = Ran B ⊕ 𝒵_g ⊕ ℋ` with the two indicated projections `p_g, p_H` annihilating
`Ran B` (`ExactSlowBranch.WeakDecomposition`) and the coupling tests `p_H C_red = 0`,
`p_g C_red` onto `𝒵_g`.  Under exactly these hypotheses, in arbitrary finite dimension:

* `finrank_weak_eq`: `dim W = rank B + dim 𝒵_g + dim ℋ` (the decomposition is direct);
* `finrank_range_leadingConstraint`: `rank Φ₀ = rank B + dim 𝒵_g = dim W - dim ℋ`;
* `finrank_ker_leadingConstraint`: `dim ker Φ₀ = dim Xs + dim W - rank Φ₀`;
* `cokernelEquiv`: `W ⧸ Ran Φ₀ ≃ ℋ` (via `p_H`, using `Ran Φ₀ = ker p_H`,
  `ExactSlowBranch.range_leadingConstraint`).

`slow_rank_critical_dimensions` is `eq:supp-exact-critical-dimensions` in the paper's
dimensions (`dim Xs = 294`, `dim W = 29`, `dim 𝒵_g = 2`, `dim ℋ = 3`; then necessarily
`rank B = 24`): `rank Φ₀ = 26`, `dim ker Φ₀ = 297`, `coker Φ₀ ≅ ℋ`.  A non-vacuity witness
(`exampleWeakDecomposition`) realises every hypothesis in these dimensions.
-/

namespace RenewalGeometry
namespace ExactSlowConstraintRank

open ExactSlowBranch Module

variable {Xs W Zg Hs : Type*}
  [NormedAddCommGroup Xs] [NormedSpace ℝ Xs] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup Zg] [NormedSpace ℝ Zg] [NormedAddCommGroup Hs] [NormedSpace ℝ Hs]
  {Cred : Xs →L[ℝ] W} {B : W →L[ℝ] W} {Jg : Zg →L[ℝ] W} {JH : Hs →L[ℝ] W}
  {pg : W →L[ℝ] Zg} {pH : W →L[ℝ] Hs}

/-- The joint projection `w ↦ (p_g w, p_H w)`. -/
def jointProjection (pg : W →L[ℝ] Zg) (pH : W →L[ℝ] Hs) : W →ₗ[ℝ] Zg × Hs :=
  (pg : W →ₗ[ℝ] Zg).prod (pH : W →ₗ[ℝ] Hs)

theorem jointProjection_surjective (hD : WeakDecomposition B Jg JH pg pH) :
    Function.Surjective (jointProjection pg pH) := by
  rintro ⟨z, h⟩
  refine ⟨Jg z + JH h, ?_⟩
  simp [jointProjection, hD.pg_Jg, hD.pH_JH, hD.pg_JH, hD.pH_Jg]

/-- The kernel of the joint projection is `Ran B`. -/
theorem ker_jointProjection (hD : WeakDecomposition B Jg JH pg pH) :
    LinearMap.ker (jointProjection pg pH) = LinearMap.range (B : W →ₗ[ℝ] W) := by
  ext w
  simp only [LinearMap.mem_ker, jointProjection, LinearMap.prod_apply,
    LinearMap.mem_range, ContinuousLinearMap.coe_coe]
  constructor
  · intro h
    rw [Prod.ext_iff] at h
    exact hD.mem_range_of_proj_zero h.1 h.2
  · rintro ⟨z, rfl⟩
    exact Prod.ext (hD.pg_B z) (hD.pH_B z)

/-- `p_H` is onto `ℋ`. -/
theorem pH_surjective (hD : WeakDecomposition B Jg JH pg pH) : Function.Surjective pH :=
  fun h => ⟨JH h, hD.pH_JH h⟩

/-- **Directness of `ℝ²⁹ = Ran B ⊕ 𝒵_g ⊕ ℋ`.** `dim W = rank B + dim 𝒵_g + dim ℋ`. -/
theorem finrank_weak_eq [FiniteDimensional ℝ W] [FiniteDimensional ℝ Zg]
    [FiniteDimensional ℝ Hs] (hD : WeakDecomposition B Jg JH pg pH) :
    finrank ℝ W = finrank ℝ (LinearMap.range (B : W →ₗ[ℝ] W)) + finrank ℝ Zg + finrank ℝ Hs := by
  have h := (jointProjection pg pH).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (jointProjection_surjective hD), finrank_top,
    finrank_prod, ker_jointProjection hD] at h
  omega

/-- **Rank of `Φ₀`.** `rank Φ₀ = dim W - dim ℋ`, i.e. `rank Φ₀ + dim ℋ = dim W`. -/
theorem finrank_range_leadingConstraint_add [FiniteDimensional ℝ W] [FiniteDimensional ℝ Hs]
    (hD : WeakDecomposition B Jg JH pg pH) (hHC : ∀ x, pH (Cred x) = 0)
    (hgC : Function.Surjective fun x => pg (Cred x)) :
    finrank ℝ (LinearMap.range (leadingConstraint Cred B : Xs × W →ₗ[ℝ] W)) + finrank ℝ Hs
      = finrank ℝ W := by
  rw [range_leadingConstraint hD hHC hgC]
  have h := (pH : W →ₗ[ℝ] Hs).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (pH_surjective hD), finrank_top] at h
  omega

/-- **Rank of `Φ₀` (`prop:supp-exact-slow-rank`, first clause).**
`rank Φ₀ = rank B + dim 𝒵_g`: the image of `B` contributes `rank B` directions and `C_red`
exactly the `dim 𝒵_g` directions of `𝒵_g` modulo `Ran B`. -/
theorem finrank_range_leadingConstraint [FiniteDimensional ℝ W] [FiniteDimensional ℝ Zg]
    [FiniteDimensional ℝ Hs] (hD : WeakDecomposition B Jg JH pg pH)
    (hHC : ∀ x, pH (Cred x) = 0) (hgC : Function.Surjective fun x => pg (Cred x)) :
    finrank ℝ (LinearMap.range (leadingConstraint Cred B : Xs × W →ₗ[ℝ] W))
      = finrank ℝ (LinearMap.range (B : W →ₗ[ℝ] W)) + finrank ℝ Zg := by
  have h1 := finrank_range_leadingConstraint_add hD hHC hgC
  have h2 := finrank_weak_eq hD
  omega

/-- **Kernel dimension of `Φ₀` (`prop:supp-exact-slow-rank`, second clause).**
Rank–nullity on the domain `Xs × W`. -/
theorem finrank_ker_leadingConstraint [FiniteDimensional ℝ Xs] [FiniteDimensional ℝ W]
    (Cred : Xs →L[ℝ] W) (B : W →L[ℝ] W) :
    finrank ℝ (LinearMap.ker (leadingConstraint Cred B : Xs × W →ₗ[ℝ] W))
      = finrank ℝ Xs + finrank ℝ W
        - finrank ℝ (LinearMap.range (leadingConstraint Cred B : Xs × W →ₗ[ℝ] W)) := by
  have h := (leadingConstraint Cred B : Xs × W →ₗ[ℝ] W).finrank_range_add_finrank_ker
  rw [finrank_prod] at h
  omega

/-- **Cokernel of `Φ₀` (`prop:supp-exact-slow-rank`, third clause).**
`coker Φ₀ = W ⧸ Ran Φ₀ ≅ ℋ`, induced by `p_H`. -/
noncomputable def cokernelEquiv (hD : WeakDecomposition B Jg JH pg pH)
    (hHC : ∀ x, pH (Cred x) = 0) (hgC : Function.Surjective fun x => pg (Cred x)) :
    (W ⧸ LinearMap.range (leadingConstraint Cred B : Xs × W →ₗ[ℝ] W)) ≃ₗ[ℝ] Hs :=
  (Submodule.quotEquivOfEq _ _ (range_leadingConstraint hD hHC hgC)).trans
    ((pH : W →ₗ[ℝ] Hs).quotKerEquivOfSurjective (pH_surjective hD))

/-- The cokernel isomorphism is induced by `p_H`. -/
theorem cokernelEquiv_mk (hD : WeakDecomposition B Jg JH pg pH)
    (hHC : ∀ x, pH (Cred x) = 0) (hgC : Function.Surjective fun x => pg (Cred x)) (w : W) :
    cokernelEquiv hD hHC hgC (Submodule.Quotient.mk w) = pH w := rfl

/-- **`prop:supp-exact-slow-rank`, `eq:supp-exact-critical-dimensions`.**  In the paper's
dimensions `dim Xs = 294` (the regular slow variable), `dim W = 29` (weak multipliers),
`dim 𝒵_g = 2`, `dim ℋ = 3`, under the weak decomposition `ℝ²⁹ = Ran B ⊕ 𝒵_g ⊕ ℋ` (which
forces `rank B = 24`) and the coupling tests `p_H C_red = 0`, `p_g C_red` onto `𝒵_g`:
`rank Φ₀ = 26`, `dim ker Φ₀ = 297` and `coker Φ₀ ≅ ℋ`. -/
theorem slow_rank_critical_dimensions [FiniteDimensional ℝ Xs] [FiniteDimensional ℝ W]
    [FiniteDimensional ℝ Zg] [FiniteDimensional ℝ Hs]
    (hXs : finrank ℝ Xs = 294) (hW : finrank ℝ W = 29) (hZg : finrank ℝ Zg = 2)
    (hHs : finrank ℝ Hs = 3)
    (hD : WeakDecomposition B Jg JH pg pH) (hHC : ∀ x, pH (Cred x) = 0)
    (hgC : Function.Surjective fun x => pg (Cred x)) :
    finrank ℝ (LinearMap.range (B : W →ₗ[ℝ] W)) = 24 ∧
      finrank ℝ (LinearMap.range (leadingConstraint Cred B : Xs × W →ₗ[ℝ] W)) = 26 ∧
      finrank ℝ (LinearMap.ker (leadingConstraint Cred B : Xs × W →ₗ[ℝ] W)) = 297 ∧
      Nonempty ((W ⧸ LinearMap.range (leadingConstraint Cred B : Xs × W →ₗ[ℝ] W))
        ≃ₗ[ℝ] Hs) := by
  have h1 := finrank_weak_eq hD
  have h2 := finrank_range_leadingConstraint hD hHC hgC
  have h3 := finrank_ker_leadingConstraint Cred B
  refine ⟨by omega, by omega, by omega, ⟨cokernelEquiv hD hHC hgC⟩⟩

/-! ### Non-vacuity witness in the paper's dimensions -/

section Witness

/-- Model weak space `ℝ²⁴ × ℝ² × ℝ³ ≅ ℝ²⁹`. -/
abbrev WModel := (Fin 24 → ℝ) × (Fin 2 → ℝ) × (Fin 3 → ℝ)

/-- `B` = projection onto the `ℝ²⁴` factor (rank `24`). -/
noncomputable def modelB : WModel →L[ℝ] WModel :=
  (ContinuousLinearMap.inl ℝ (Fin 24 → ℝ) ((Fin 2 → ℝ) × (Fin 3 → ℝ))).comp
    (ContinuousLinearMap.fst ℝ (Fin 24 → ℝ) ((Fin 2 → ℝ) × (Fin 3 → ℝ)))

/-- `J_g` = insertion of the `ℝ²` factor. -/
noncomputable def modelJg : (Fin 2 → ℝ) →L[ℝ] WModel :=
  (ContinuousLinearMap.inr ℝ (Fin 24 → ℝ) ((Fin 2 → ℝ) × (Fin 3 → ℝ))).comp
    (ContinuousLinearMap.inl ℝ (Fin 2 → ℝ) (Fin 3 → ℝ))

/-- `J_H` = insertion of the `ℝ³` factor. -/
noncomputable def modelJH : (Fin 3 → ℝ) →L[ℝ] WModel :=
  (ContinuousLinearMap.inr ℝ (Fin 24 → ℝ) ((Fin 2 → ℝ) × (Fin 3 → ℝ))).comp
    (ContinuousLinearMap.inr ℝ (Fin 2 → ℝ) (Fin 3 → ℝ))

/-- `p_g`. -/
noncomputable def modelPg : WModel →L[ℝ] (Fin 2 → ℝ) :=
  (ContinuousLinearMap.fst ℝ (Fin 2 → ℝ) (Fin 3 → ℝ)).comp
    (ContinuousLinearMap.snd ℝ (Fin 24 → ℝ) ((Fin 2 → ℝ) × (Fin 3 → ℝ)))

/-- `p_H`. -/
noncomputable def modelPH : WModel →L[ℝ] (Fin 3 → ℝ) :=
  (ContinuousLinearMap.snd ℝ (Fin 2 → ℝ) (Fin 3 → ℝ)).comp
    (ContinuousLinearMap.snd ℝ (Fin 24 → ℝ) ((Fin 2 → ℝ) × (Fin 3 → ℝ)))

/-- `C_red x = J_g (x₀, x₁)`. -/
noncomputable def modelCred : (Fin 294 → ℝ) →L[ℝ] WModel :=
  modelJg.comp (ContinuousLinearMap.pi fun i : Fin 2 =>
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 294 => ℝ) (Fin.castLE (by norm_num) i))

theorem exampleWeakDecomposition :
    WeakDecomposition modelB modelJg modelJH modelPg modelPH where
  pg_Jg z := by simp [modelPg, modelJg]
  pH_JH h := by simp [modelPH, modelJH]
  pg_JH h := by simp [modelPg, modelJH]
  pH_Jg z := by simp [modelPH, modelJg]
  pg_B w := by simp [modelPg, modelB]
  pH_B w := by simp [modelPH, modelB]
  split w := ⟨w, by
    obtain ⟨a, b, c⟩ := w
    simp [modelB, modelJg, modelJH, modelPg, modelPH]⟩

theorem example_pH_Cred (x : Fin 294 → ℝ) : modelPH (modelCred x) = 0 := by
  simp [modelPH, modelCred, modelJg]

theorem example_pg_Cred_surjective : Function.Surjective fun x => modelPg (modelCred x) := by
  intro z
  refine ⟨fun j => if h : j.val < 2 then z ⟨j.val, h⟩ else 0, ?_⟩
  funext i
  simp only [modelPg, modelCred, modelJg]
  simp
  intro h
  have := i.isLt
  omega

/-- Non-vacuity: the hypotheses of `slow_rank_critical_dimensions` are jointly satisfiable
in the paper's dimensions. -/
example :
    finrank ℝ (LinearMap.range (modelB : WModel →ₗ[ℝ] WModel)) = 24 ∧
      finrank ℝ (LinearMap.range
        (leadingConstraint modelCred modelB : (Fin 294 → ℝ) × WModel →ₗ[ℝ] WModel)) = 26 ∧
      finrank ℝ (LinearMap.ker
        (leadingConstraint modelCred modelB : (Fin 294 → ℝ) × WModel →ₗ[ℝ] WModel)) = 297 ∧
      Nonempty ((WModel ⧸ LinearMap.range
        (leadingConstraint modelCred modelB : (Fin 294 → ℝ) × WModel →ₗ[ℝ] WModel))
          ≃ₗ[ℝ] (Fin 3 → ℝ)) :=
  slow_rank_critical_dimensions (by simp) (by simp [WModel]) (by simp) (by simp)
    exampleWeakDecomposition example_pH_Cred example_pg_Cred_surjective

end Witness

end ExactSlowConstraintRank
end RenewalGeometry
