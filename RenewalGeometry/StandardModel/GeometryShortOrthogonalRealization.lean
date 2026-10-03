/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.Predictive.ExactSourceSchurResidual
import RenewalGeometry.StandardModel.GeometryShortQuotientExact

/-!
# The geometry short on the orthogonal active realization (`eq:geometry-short`)

Covers the clause `eq:geometry-short` of `thm:geometry-short` (spacetime–gauge duality paper)
for the actual shorted Gram `G_{int|ST} = sourceSchurResidual S_ST S_int`
(`= G_int − C G_ST^† C^*`, `C = S_int^* S_ST`, Moore–Penrose inverse by functional calculus).

The orthogonal active realization: the accepted contrast synthesis
`S_acc : E_acc^0 → ℋ_acc`, `E_acc^0 = E_ST^cat ⊕ E_int^cat`, has scalar Gram
`S_acc^* S_acc = ϑ I`; the complete spacetime source is `S_ST = [S_acc|_{E_ST^cat}, S_extra]`
where the additional spacetime scores `S_extra` (waiting-time, calibration, … directions) are
orthogonal to the accepted categorical source, `S_extra^* S_int = 0`; and
`S_int = S_acc|_{E_int^cat}`.  From these *hypotheses of the paper* (not from the vanishing of
the mixed block, which is derived) we prove `G_{int|ST} = ϑ I` (`geometry_short_active`), its
orthogonal-residual form `S_int^*(I − P_ST) S_int = ϑ I`, and for `ϑ ≠ 0` that the
source-minimal carrier has full dimension.  `geometry_short_active_twelve` is the paper's
instance `E_ST^cat = P_0 ⊗ t_0` (dimension 11), `E_int^cat` of dimension 12.
-/

open Matrix Module
open scoped ComplexOrder MatrixOrder

namespace RenewalGeometry

namespace GeometryShortActive

set_option linter.unusedDecidableInType false

variable {h nST nInt k : ℕ}

/-- If the mixed block `S₁^* S₂` vanishes, the Schur residual is the Gram of `S₂`. -/
theorem sourceSchurResidual_of_mixed_zero {e₁ e₂ : ℕ} (S₁ : Matrix (Fin h) (Fin e₁) ℂ)
    (S₂ : Matrix (Fin h) (Fin e₂) ℂ) (hmix : S₁ᴴ * S₂ = 0) :
    sourceSchurResidual S₁ S₂ = S₂ᴴ * S₂ := by
  simp [sourceSchurResidual, hmix]

/-- The accepted internal categorical source `S_int = S_acc|_{E_int^cat}`. -/
def activeInternalSource (Sacc : Matrix (Fin h) (Fin nST ⊕ Fin nInt) ℂ) :
    Matrix (Fin h) (Fin nInt) ℂ :=
  Matrix.of fun i m => Sacc i (Sum.inr m)

/-- The accepted categorical spacetime source `S_acc|_{E_ST^cat}`. -/
def activeCategoricalSTSource (Sacc : Matrix (Fin h) (Fin nST ⊕ Fin nInt) ℂ) :
    Matrix (Fin h) (Fin nST) ℂ :=
  Matrix.of fun i a => Sacc i (Sum.inl a)

/-- The complete represented spacetime source `S_ST = [S_acc|_{E_ST^cat}, S_extra]` on
`E_ST = E_ST^cat ⊕ ℂ^k` (the extra columns are the independently reconstructed spacetime
directions). -/
def activeSpacetimeSource (Sacc : Matrix (Fin h) (Fin nST ⊕ Fin nInt) ℂ)
    (Sextra : Matrix (Fin h) (Fin k) ℂ) : Matrix (Fin h) (Fin (nST + k)) ℂ :=
  Matrix.of fun i j =>
    Sum.elim (fun a => Sacc i (Sum.inl a)) (fun b => Sextra i b) (finSumFinEquiv.symm j)

/-- **The mixed block vanishes** on the orthogonal active realization: from
`S_acc^* S_acc = ϑ I` and `S_extra^* S_int = 0`, `C^* = S_ST^* S_int = 0`. -/
theorem mixed_block_eq_zero (θ : ℝ) (Sacc : Matrix (Fin h) (Fin nST ⊕ Fin nInt) ℂ)
    (Sextra : Matrix (Fin h) (Fin k) ℂ)
    (hacc : Saccᴴ * Sacc = (θ : ℂ) • (1 : Matrix (Fin nST ⊕ Fin nInt) _ ℂ))
    (horth : Sextraᴴ * activeInternalSource Sacc = 0) :
    (activeSpacetimeSource Sacc Sextra)ᴴ * activeInternalSource Sacc = 0 := by
  ext j m
  obtain ⟨j', rfl⟩ := finSumFinEquiv.surjective j
  rcases j' with a | b
  · have := congrFun (congrFun hacc (Sum.inl a)) (Sum.inr m)
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.smul_apply,
      Matrix.one_apply, reduceCtorEq, ite_false, smul_zero] at this
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, activeSpacetimeSource,
      activeInternalSource, Matrix.of_apply, Equiv.symm_apply_apply, Sum.elim_inl,
      Matrix.zero_apply]
    exact this
  · have := congrFun (congrFun horth b) m
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.zero_apply] at this
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, activeSpacetimeSource,
      Matrix.of_apply, Equiv.symm_apply_apply, Sum.elim_inr, Matrix.zero_apply]
    exact this

/-- The internal Gram on the orthogonal active realization is `ϑ I`. -/
theorem internal_gram_eq (θ : ℝ) (Sacc : Matrix (Fin h) (Fin nST ⊕ Fin nInt) ℂ)
    (hacc : Saccᴴ * Sacc = (θ : ℂ) • (1 : Matrix (Fin nST ⊕ Fin nInt) _ ℂ)) :
    (activeInternalSource Sacc)ᴴ * activeInternalSource Sacc =
      (θ : ℂ) • (1 : Matrix (Fin nInt) (Fin nInt) ℂ) := by
  ext m m'
  have := congrFun (congrFun hacc (Sum.inr m)) (Sum.inr m')
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.smul_apply,
    Matrix.one_apply, Sum.inr.injEq] at this
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, activeInternalSource,
    Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply]
  exact this

/-- **`eq:geometry-short`.**  On the orthogonal active realization
(`S_acc^* S_acc = ϑ I`, extra spacetime scores orthogonal to the accepted categorical source),
the shorted Gram of the accepted internal source by the complete spacetime source is
`G_{int|ST} = G_int − C G_ST^† C^* = ϑ I`. -/
theorem geometry_short_active (θ : ℝ) (Sacc : Matrix (Fin h) (Fin nST ⊕ Fin nInt) ℂ)
    (Sextra : Matrix (Fin h) (Fin k) ℂ)
    (hacc : Saccᴴ * Sacc = (θ : ℂ) • (1 : Matrix (Fin nST ⊕ Fin nInt) _ ℂ))
    (horth : Sextraᴴ * activeInternalSource Sacc = 0) :
    sourceSchurResidual (activeSpacetimeSource Sacc Sextra) (activeInternalSource Sacc) =
      (θ : ℂ) • (1 : Matrix (Fin nInt) (Fin nInt) ℂ) := by
  rw [sourceSchurResidual_of_mixed_zero _ _ (mixed_block_eq_zero θ Sacc Sextra hacc horth),
    internal_gram_eq θ Sacc hacc]

/-- `eq:geometry-short` in the orthogonal-residual form `S_int^*(I − P_ST) S_int = ϑ I`. -/
theorem geometry_short_active_orthogonalResidual (θ : ℝ)
    (Sacc : Matrix (Fin h) (Fin nST ⊕ Fin nInt) ℂ) (Sextra : Matrix (Fin h) (Fin k) ℂ)
    (hacc : Saccᴴ * Sacc = (θ : ℂ) • (1 : Matrix (Fin nST ⊕ Fin nInt) _ ℂ))
    (horth : Sextraᴴ * activeInternalSource Sacc = 0) :
    (activeInternalSource Sacc)ᴴ * (1 - sourceRangeProjection (activeSpacetimeSource Sacc Sextra))
        * activeInternalSource Sacc =
      (θ : ℂ) • (1 : Matrix (Fin nInt) (Fin nInt) ℂ) := by
  rw [← sourceSchurResidual_eq_orthogonalResidual, geometry_short_active θ Sacc Sextra hacc horth]

/-- For `ϑ ≠ 0` the source-minimal internal carrier `E_int^cat / Ker G_{int|ST}` has the full
dimension `nInt` (`eq:geometry-short-quotient` on the active realization). -/
theorem finrank_minimalCarrier_active (θ : ℝ) (hθ : θ ≠ 0)
    (Sacc : Matrix (Fin h) (Fin nST ⊕ Fin nInt) ℂ) (Sextra : Matrix (Fin h) (Fin k) ℂ)
    (hacc : Saccᴴ * Sacc = (θ : ℂ) • (1 : Matrix (Fin nST ⊕ Fin nInt) _ ℂ))
    (horth : Sextraᴴ * activeInternalSource Sacc = 0) :
    finrank ℂ (GeometryShortQuotient.minimalCarrier
      (sourceSchurResidual (activeSpacetimeSource Sacc Sextra) (activeInternalSource Sacc))) =
      nInt := by
  rw [GeometryShortQuotient.finrank_minimalCarrier, geometry_short_active θ Sacc Sextra hacc horth]
  have hu : IsUnit ((θ : ℂ) • (1 : Matrix (Fin nInt) (Fin nInt) ℂ)) := by
    have : IsUnit (θ : ℂ) := isUnit_iff_ne_zero.mpr (by exact_mod_cast hθ)
    rw [← Algebra.algebraMap_eq_smul_one]
    exact this.map _
  rw [Matrix.rank_of_isUnit _ hu, Fintype.card_fin]

/-- The paper's instance: `E_ST^cat = P_0 ⊗ t_0` of dimension 11 and
`E_int^cat = (ℝ1_Φ ⊗ t_1) ⊕ (P_0 ⊗ t_1)` of dimension 12, with any number `k` of additional
spacetime directions: `G_{int|ST} = ϑ I_{12}`. -/
theorem geometry_short_active_twelve (θ : ℝ) (Sacc : Matrix (Fin h) (Fin 11 ⊕ Fin 12) ℂ)
    (Sextra : Matrix (Fin h) (Fin k) ℂ)
    (hacc : Saccᴴ * Sacc = (θ : ℂ) • (1 : Matrix (Fin 11 ⊕ Fin 12) _ ℂ))
    (horth : Sextraᴴ * activeInternalSource Sacc = 0) :
    sourceSchurResidual (activeSpacetimeSource Sacc Sextra) (activeInternalSource Sacc) =
      (θ : ℂ) • (1 : Matrix (Fin 12) (Fin 12) ℂ) :=
  geometry_short_active θ Sacc Sextra hacc horth

/-- The isometric accepted synthesis `E_acc^0 = E_ST^cat ⊕ E_int^cat ≅ ℂ^{23}`, `S_acc^*S_acc = I`. -/
theorem isometric_accepted_synthesis :
    ((1 : Matrix (Fin 23) (Fin 23) ℂ).submatrix id
        (finSumFinEquiv : Fin 11 ⊕ Fin 12 ≃ Fin 23))ᴴ *
        (1 : Matrix (Fin 23) (Fin 23) ℂ).submatrix id (finSumFinEquiv : Fin 11 ⊕ Fin 12 ≃ Fin 23) =
      ((1 : ℝ) : ℂ) • (1 : Matrix (Fin 11 ⊕ Fin 12) _ ℂ) := by
  rw [Matrix.conjTranspose_submatrix, ← Matrix.submatrix_mul _ _ _ id _ Function.bijective_id,
    conjTranspose_one, Matrix.one_mul, Matrix.submatrix_one_equiv]
  simp

/-- Non-vacuity: the hypotheses of `geometry_short_active_twelve` hold on the isometric
accepted synthesis with no extra spacetime direction, giving `G_{int|ST} = I_{12}`. -/
example :
    sourceSchurResidual
        (activeSpacetimeSource ((1 : Matrix (Fin 23) (Fin 23) ℂ).submatrix id
          (finSumFinEquiv : Fin 11 ⊕ Fin 12 ≃ Fin 23)) (0 : Matrix (Fin 23) (Fin 0) ℂ))
        (activeInternalSource ((1 : Matrix (Fin 23) (Fin 23) ℂ).submatrix id
          (finSumFinEquiv : Fin 11 ⊕ Fin 12 ≃ Fin 23))) =
      ((1 : ℝ) : ℂ) • (1 : Matrix (Fin 12) (Fin 12) ℂ) :=
  geometry_short_active_twelve 1 _ _ isometric_accepted_synthesis (by simp)

end GeometryShortActive

end RenewalGeometry
