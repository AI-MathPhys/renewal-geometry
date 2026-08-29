/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.LockedOpportunityNaimarkFrame
import Mathlib.LinearAlgebra.Matrix.Vec

/-!
# Exact locked synchronized opportunity instrument

This file closes the remaining fidelity gap in
`thm:locked-opportunity-instrument`.  Starting from the manuscript's actual
twenty-four operators—linear independence, Kraus completeness, and
`∑ A_j = √2 I`—we construct their Choi synthesis, prove its rank is twenty
four, derive `Bc = vec(I)`, and derive (rather than assume) the total Choi
factorization `J_opp = B M_θ Bᴴ`.  The minimal-environment POVM and explicit
one-dimensional Naimark excess are supplied by the compiled companion module.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace NCG.LockedOpportunityInstrumentExact

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- The concrete locked twenty-four-branch assumptions stated in the
manuscript. -/
structure OpportunityData (n : Type*) [Fintype n] [DecidableEq n] where
  operator : Fin 24 → Matrix n n ℂ
  krausComplete : ∑ j, (operator j)ᴴ * operator j = 1
  lockedSum : ∑ j, operator j = (Real.sqrt 2 : ℂ) • 1
  independent : LinearIndependent ℂ operator

/-- Vectorization as an injective complex-linear map. -/
def vecLinear : Matrix n n ℂ →ₗ[ℂ] (n × n → ℂ) where
  toFun := Matrix.vec
  map_add' := Matrix.vec_add
  map_smul' := Matrix.vec_smul

theorem vecLinear_ker : LinearMap.ker (vecLinear (n := n)) = ⊥ := by
  rw [LinearMap.ker_eq_bot]
  intro A B h
  exact Matrix.vec_inj.mp h

/-- The accepted Choi-vector synthesis `B`. -/
noncomputable def acceptedSynthesis (d : OpportunityData n) :
    Matrix (n × n) (Fin 24) ℂ :=
  fun p j => Matrix.vec (d.operator j) p

/-- The locked coefficient vector `c = 2^{-1/2}(1,…,1)`. -/
noncomputable def uniformCoefficient : Fin 24 → ℂ :=
  fun _ => (Real.sqrt 2 : ℂ)⁻¹

/-- Linear independence of the concrete Kraus operators gives a full
twenty-four-dimensional accepted Choi synthesis. -/
theorem acceptedSynthesis_rank (d : OpportunityData n) :
    (acceptedSynthesis d).rank = 24 := by
  have hvec : LinearIndependent ℂ (fun j => Matrix.vec (d.operator j)) :=
    d.independent.map' (vecLinear (n := n)) vecLinear_ker
  have hrows : LinearIndependent ℂ (acceptedSynthesis d)ᵀ.row := by
    change LinearIndependent ℂ (fun j p => Matrix.vec (d.operator j) p)
    exact hvec
  have hr := hrows.rank_matrix
  simpa only [Matrix.rank_transpose, Fintype.card_fin] using hr

/-- The locked sum identity puts the no-response Choi vector in the accepted
span: `Bc = vec(I)`. -/
theorem synthesis_mul_uniform (d : OpportunityData n) :
    acceptedSynthesis d *ᵥ uniformCoefficient =
      Matrix.vec (1 : Matrix n n ℂ) := by
  funext p
  have hs := congrFun (congrFun d.lockedSum p.2) p.1
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.one_apply] at hs
  simp only [smul_eq_mul] at hs
  rw [Matrix.mulVec, dotProduct]
  simp only [acceptedSynthesis, uniformCoefficient, Matrix.vec]
  calc
    ∑ j, d.operator j p.2 p.1 * (Real.sqrt 2 : ℂ)⁻¹ =
        (∑ j, d.operator j p.2 p.1) * (Real.sqrt 2 : ℂ)⁻¹ := by
          rw [Finset.sum_mul]
    _ = ((Real.sqrt 2 : ℂ) * if p.2 = p.1 then 1 else 0) *
        (Real.sqrt 2 : ℂ)⁻¹ := by rw [hs]
    _ = if p.2 = p.1 then 1 else 0 := by
      have hsqrt : (Real.sqrt 2 : ℂ) ≠ 0 := by positivity
      split_ifs <;> simp [hsqrt]

/-- The coefficient matrix `M_θ = θI + (1-θ)ccᴴ`. -/
noncomputable def mixingMatrix (θ : ℝ) : Matrix (Fin 24) (Fin 24) ℂ :=
  (θ : ℂ) • 1 + ((1 - θ : ℝ) : ℂ) •
    Matrix.vecMulVec uniformCoefficient (star uniformCoefficient)

/-- The branchwise coarse Choi sum: twenty-four accepted dyads plus the
no-response dyad. -/
noncomputable def totalOpportunityChoi (θ : ℝ) (d : OpportunityData n) :
    Matrix (n × n) (n × n) ℂ :=
  let B := acceptedSynthesis d
  let v₀ := Matrix.vec (1 : Matrix n n ℂ)
  (θ : ℂ) • (B * Bᴴ) + ((1 - θ : ℝ) : ℂ) •
    Matrix.vecMulVec v₀ (star v₀)

private theorem synthesis_dyad (d : OpportunityData n) :
    acceptedSynthesis d *
        Matrix.vecMulVec uniformCoefficient (star uniformCoefficient) *
        (acceptedSynthesis d)ᴴ =
      Matrix.vecMulVec (Matrix.vec (1 : Matrix n n ℂ))
        (star (Matrix.vec (1 : Matrix n n ℂ))) := by
  ext p q
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply,
    Matrix.conjTranspose_apply, Pi.star_apply]
  have hp := congrFun (synthesis_mul_uniform d) p
  have hq := congrFun (synthesis_mul_uniform d) q
  simp only [Matrix.mulVec, dotProduct] at hp hq
  calc
    ∑ j, (∑ i, acceptedSynthesis d p i *
          (uniformCoefficient i * star (uniformCoefficient j))) *
          star (acceptedSynthesis d q j) =
      ∑ j, ((∑ i, acceptedSynthesis d p i * uniformCoefficient i) *
          star (uniformCoefficient j)) *
          star (acceptedSynthesis d q j) := by
            apply Finset.sum_congr rfl
            intro j _
            congr 1
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro i _
            ring
    _ = (∑ x, acceptedSynthesis d p x * uniformCoefficient x) *
        star (∑ x, acceptedSynthesis d q x * uniformCoefficient x) := by
          simp only [star_sum, star_mul]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
    _ = Matrix.vec (1 : Matrix n n ℂ) p *
        star (Matrix.vec (1 : Matrix n n ℂ) q) := by rw [hp, hq]

/-- The advertised total Choi factorization is derived from the concrete
branch operators. -/
theorem totalChoi_factorization (θ : ℝ) (d : OpportunityData n) :
    totalOpportunityChoi θ d =
      acceptedSynthesis d * mixingMatrix θ * (acceptedSynthesis d)ᴴ := by
  rw [totalOpportunityChoi, mixingMatrix, Matrix.mul_add, Matrix.add_mul]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
  rw [synthesis_dyad]

set_option maxHeartbeats 800000

/-- Positivity of `M_θ` is now applied to the derived factorization, so both
accepted and total Choi ranks are twenty four. -/
theorem accepted_and_total_Choi_rank (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (d : OpportunityData n) :
    (acceptedSynthesis d * (acceptedSynthesis d)ᴴ).rank = 24 ∧
      (totalOpportunityChoi θ d).rank = 24 := by
  have hM : (mixingMatrix θ).PosDef := by
    exact (locked_opportunity_instrument uniformCoefficient θ hθ hθ1).2.2.1
  have hSu : IsUnit (CFC.sqrt (mixingMatrix θ)) := sqrt_isUnit hM
  have hS : IsUnit (CFC.sqrt (mixingMatrix θ)).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hSu
  have hfac : CFC.sqrt (mixingMatrix θ) * (CFC.sqrt (mixingMatrix θ))ᴴ =
      mixingMatrix θ := by
    rw [sqrt_isHermitian, sqrt_mul_self_eq _ hM.posSemidef]
  rw [totalChoi_factorization]
  have hr := lockedOpportunityChoiRanks (acceptedSynthesis d)
    (CFC.sqrt (mixingMatrix θ)) (acceptedSynthesis_rank d) hS
  exact ⟨hr.1, by simpa [hfac] using hr.2⟩

/-- Every accepted concrete operator is nonzero, so all twenty-four accepted
records are genuine. -/
theorem accepted_records_nonzero (d : OpportunityData n) :
    ∀ j, d.operator j ≠ 0 :=
  d.independent.ne_zero

/-- Bundled closure of the formerly conditional theorem. -/
theorem locked_opportunity_instrument_exact (d : OpportunityData n) :
    let θ := lockedOpportunityTheta
    (∀ j, d.operator j ≠ 0) ∧
      acceptedSynthesis d *ᵥ uniformCoefficient = Matrix.vec (1 : Matrix n n ℂ) ∧
      totalOpportunityChoi θ d =
        acceptedSynthesis d * mixingMatrix θ * (acceptedSynthesis d)ᴴ ∧
      (acceptedSynthesis d * (acceptedSynthesis d)ᴴ).rank = 24 ∧
      (totalOpportunityChoi θ d).rank = 24 ∧
      (∀ v, lockedRawFrame θ *ᵥ v = 0 ↔
        ∃ z : ℝ, v = z • lockedNaimarkNullDirection θ) ∧
      lockedRawFrame θ *ᵥ lockedNaimarkNullVector θ = 0 ∧
      (∑ k, (lockedNaimarkNullVector θ k) ^ 2 = 1) := by
  dsimp only
  have hθ := lockedOpportunityTheta_bounds
  have hrank := accepted_and_total_Choi_rank lockedOpportunityTheta hθ.1 hθ.2.le d
  exact ⟨accepted_records_nonzero d,
    synthesis_mul_uniform d,
    totalChoi_factorization lockedOpportunityTheta d,
    hrank.1, hrank.2,
    lockedRawFrame_kernel lockedOpportunityTheta hθ.1,
    lockedRawFrame_nullVector lockedOpportunityTheta hθ.1.le,
    lockedNaimarkNullVector_normalized lockedOpportunityTheta hθ.1.le hθ.2⟩

end NCG.LockedOpportunityInstrumentExact
