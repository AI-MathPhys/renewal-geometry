/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.QuantumCylinderInverseLimitExact

/-!
# Summable cutoff correction and reflection-positive projective limit (record theorem)

Exact encoding of `thm:SMST-quantum-projective-limit` on a tower of finite oriented quantum
cylinders with reflection-equivariant cutoff maps (`CylinderTower`). If every cylinder weight
is a reflection-positive probability and the total-variation defects
`δ_X = ‖(π_{X+1,X})_* μ_{X+1} - μ_X‖_TV` are summable, then:

* (TV limits) for every `m` the pushed measures `(π_{n,m})_* μ_n` converge in total variation
  to a probability `μ̄_m` (`tendsto_tv_marg`, `limitWeights_nonneg`, `sum_limitWeights`);
* (compatibility) `(π_m)_* μ̄_{m+1} = μ̄_m` (`limitFamily.compat`);
* (QRP.6) `‖μ̄_m - μ_m‖_TV ≤ ∑_{j ≥ m} δ_j` (`tv_limit_le`);
* (inverse limit) there is a unique cylinder probability on `Π n, Ω n` with coordinate laws `μ̄_m`
  carried by the inverse-limit relations (`existsUnique_inverseLimit`);
* (reflection positivity) every `μ̄_m` is reflection positive on the finite positive-time algebra
  `A m` (`limit_reflection_positive`).

The whole package is collected in `quantum_projective_limit`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Finset
open NCG.SMSTReflectionPositivity NCG.QuantumCylinderProjectiveLimit NCG.QuantumCylinderInverseLimit
open scoped ComplexOrder

namespace NCG
namespace SMSTQuantumProjectiveLimit

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

variable {Ω : ℕ → Type*} [∀ n, Fintype (Ω n)] [∀ n, DecidableEq (Ω n)]
  [∀ n, MeasurableSpace (Ω n)] [∀ n, DiscreteMeasurableSpace (Ω n)]
variable (T : CylinderTower Ω)

/-- The limit weights `μ̄_m`. -/
noncomputable def limitWeights (hδ : Summable (defect T.π T.μ)) (m : ℕ) : Ω m → ℝ :=
  WithLp.ofLp (limMarg T.π T.μ hδ m)

theorem limitWeights_nonneg (hδ : Summable (defect T.π T.μ)) (m : ℕ) (ω : Ω m) :
    0 ≤ limitWeights T hδ m ω :=
  limMarg_nonneg T.π T.μ (fun n => (T.C n).μ_nonneg) hδ m ω

theorem sum_limitWeights (hμ1 : ∀ n, ∑ ω, T.μ n ω = 1) (hδ : Summable (defect T.π T.μ)) (m : ℕ) :
    ∑ ω, limitWeights T hδ m ω = 1 :=
  sum_limMarg T.π T.μ hμ1 hδ m

/-- The limit weights form a projectively compatible family. -/
noncomputable def limitFamily (hμ1 : ∀ n, ∑ ω, T.μ n ω = 1) (hδ : Summable (defect T.π T.μ)) :
    CompatibleFamily T.π where
  ν := limitWeights T hδ
  nonneg := limitWeights_nonneg T hδ
  sum_eq_one := sum_limitWeights T hμ1 hδ
  compat := push_limMarg T.π T.μ hδ

/-- **(TV convergence)**: `(π_{n,m})_* μ_n → μ̄_m` in total variation. -/
theorem tendsto_tv_marg (hδ : Summable (defect T.π T.μ)) (m : ℕ) :
    Tendsto (fun n => tv (WithLp.ofLp (marg T.π T.μ m n) - limitWeights T hδ m)) atTop (𝓝 0) := by
  have h := (tendsto_marg T.π T.μ hδ m).dist tendsto_const_nhds (b := limMarg T.π T.μ hδ m)
  rw [dist_self] at h
  refine h.congr fun n => ?_
  rw [← dist_toLp_eq_tv]
  rfl

/-- For `n ≥ m` the pushed marginal is `(π_{n,m})_* μ_n`. -/
theorem marg_eq_push {m n : ℕ} (h : m ≤ n) :
    WithLp.ofLp (marg T.π T.μ m n) = push (πLe T.π h) (T.μ n) := by
  rw [marg_of_le T.π T.μ h]

/-- **(QRP.6)**: `‖μ̄_m - μ_m‖_TV ≤ ∑_{j ≥ m} δ_j`. -/
theorem tv_limit_le (hδ : Summable (defect T.π T.μ)) (m : ℕ) :
    tv (T.μ m - limitWeights T hδ m) ≤ ∑' j, defect T.π T.μ (m + j) :=
  tv_limMarg_le T.π T.μ hδ m

/-- **(Inverse limit)**: there is a unique cylinder probability with marginals `μ̄_m` carried by
the inverse-limit relations. -/
theorem existsUnique_inverseLimit (hμ1 : ∀ n, ∑ ω, T.μ n ω = 1)
    (hδ : Summable (defect T.π T.μ)) :
    ∃! Q : Measure (Π n, Ω n), IsProbabilityMeasure Q ∧
      (∀ n, Q.map (fun ω => ω n) = discrete (limitWeights T hδ n)) ∧
      (∀ᵐ ω ∂Q, ∀ n, T.π n (ω (n + 1)) = ω n) := by
  refine ⟨inverseLimit (limitFamily T hμ1 hδ), ⟨inferInstance,
    inverseLimit_map_eval (limitFamily T hμ1 hδ), inverseLimit_ae_rel (limitFamily T hμ1 hδ)⟩, ?_⟩
  rintro Q ⟨_, hQ, hrel⟩
  exact inverseLimit_unique (limitFamily T hμ1 hδ) Q hQ hrel

/-- **(Reflection positivity)** of every limit marginal. -/
theorem limit_reflection_positive (hδ : Summable (defect T.π T.μ)) (A : ∀ n, Set (Ω n → ℂ))
    (hpull : ∀ m n (h : m ≤ n), ∀ F ∈ A m, F ∘ πLe T.π h ∈ A n)
    (hRP : ∀ n, ReflectionPositiveOn (T.C n) (A n)) (m : ℕ) :
    ReflectionPositiveOn (limCylinder T hδ m) (A m) :=
  limMarg_reflection_positive T hδ A hpull hRP m

/-- **Summable cutoff correction and reflection-positive projective limit.** -/
theorem quantum_projective_limit (hμ1 : ∀ n, ∑ ω, T.μ n ω = 1)
    (hδ : Summable (defect T.π T.μ)) (A : ∀ n, Set (Ω n → ℂ))
    (hpull : ∀ m n (h : m ≤ n), ∀ F ∈ A m, F ∘ πLe T.π h ∈ A n)
    (hRP : ∀ n, ReflectionPositiveOn (T.C n) (A n)) :
    (∀ m, Tendsto (fun n => tv (WithLp.ofLp (marg T.π T.μ m n) - limitWeights T hδ m)) atTop
        (𝓝 0)) ∧
      (∀ m ω, 0 ≤ limitWeights T hδ m ω) ∧ (∀ m, ∑ ω, limitWeights T hδ m ω = 1) ∧
      (∀ m, push (T.π m) (limitWeights T hδ (m + 1)) = limitWeights T hδ m) ∧
      (∀ m, tv (T.μ m - limitWeights T hδ m) ≤ ∑' j, defect T.π T.μ (m + j)) ∧
      (∃! Q : Measure (Π n, Ω n), IsProbabilityMeasure Q ∧
        (∀ n, Q.map (fun ω => ω n) = discrete (limitWeights T hδ n)) ∧
        (∀ᵐ ω ∂Q, ∀ n, T.π n (ω (n + 1)) = ω n)) ∧
      (∀ m, ReflectionPositiveOn (limCylinder T hδ m) (A m)) :=
  ⟨tendsto_tv_marg T hδ, limitWeights_nonneg T hδ, sum_limitWeights T hμ1 hδ,
    push_limMarg T.π T.μ hδ, tv_limit_le T hδ, existsUnique_inverseLimit T hμ1 hδ,
    limit_reflection_positive T hδ A hpull hRP⟩

end SMSTQuantumProjectiveLimit
end NCG
