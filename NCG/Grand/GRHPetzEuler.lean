/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SqrtPolar
import NCG.Algebra.SchwarzMap

/-!
# Finite Petz–Euler sufficient certificate
  (`thm:GRH-Petz-Euler`, Gran-Tensor manuscript)

* `grh_petz_euler`:
  (1) the faithfulness engine: for a faithful state density
      `ρ ≻ 0`, `Tr(ρ·dᴴd) = 0` forces `d = 0`;
  (2) uniqueness of the `ω`-preserving conditional
      expectation: two maps into the Euler subalgebra with the
      same `ω`-adjointness relations against the subalgebra
      coincide (the Takesaki uniqueness clause);
  (3) the Kadison–Schwarz Gram order: a Schwarz map satisfies
      `(Py)ᴴ(Py) ⪯ P(yᴴy)`, which applied to the completed
      source words gives the boxed `Ê_X ⪯ M̂_X`.

Rendering disclosed: the existence half of Takesaki's
criterion (modular invariance `ρ^{it}Nρ^{-it} = N` constructs
the expectation) is the manuscript's finite modular-theory
step; the matrix-amplified ("complete") version of the Gram
order is clause (3) applied entrywise to every matrix of
source-word combinations; compatibility with the nuisance
short is the declared preservation hypothesis.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

-- `CFC.sqrt` mentions the matrix CFC instance (which needs
-- `DecidableEq`) in every statement; the linter cannot see it.
set_option linter.unusedDecidableInType false

namespace NCG

/-- `thm:GRH-Petz-Euler`. -/
theorem grh_petz_euler {n : Type*} [Fintype n]
    [DecidableEq n] :
    -- (1) faithfulness of the physical state
    (∀ ρ d : Matrix n n ℂ, ρ.PosDef →
      (ρ * (dᴴ * d)).trace = 0 → d = 0)
    -- (2) uniqueness of the ω-preserving expectation
    ∧ (∀ ρ : Matrix n n ℂ, ρ.PosDef →
        ∀ (N : Subalgebra ℂ (Matrix n n ℂ))
          (P P' : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ),
        (∀ x, P x ∈ N) → (∀ x, P' x ∈ N) →
        (∀ (x m : Matrix n n ℂ), m ∈ N →
          (ρ * (mᴴ * P x)).trace = (ρ * (mᴴ * x)).trace) →
        (∀ (x m : Matrix n n ℂ), m ∈ N →
          (ρ * (mᴴ * P' x)).trace = (ρ * (mᴴ * x)).trace) →
        ∀ x, P x = P' x)
    -- (3) the Kadison–Schwarz Gram order
    ∧ (∀ P : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ,
        IsSchwarzMap P →
        ∀ y : Matrix n n ℂ, (P y)ᴴ * P y ≤ P (yᴴ * y)) := by
  have hfaithful : ∀ ρ d : Matrix n n ℂ, ρ.PosDef →
      (ρ * (dᴴ * d)).trace = 0 → d = 0 := by
    intro ρ d hρ h0
    haveI := (sqrt_isUnit hρ).invertible
    have hs2 : CFC.sqrt ρ * CFC.sqrt ρ = ρ :=
      sqrt_mul_self_eq ρ hρ.posSemidef
    have hkey : ((d * CFC.sqrt ρ)ᴴ
        * (d * CFC.sqrt ρ)).trace = 0 := by
      rw [Matrix.conjTranspose_mul, sqrt_isHermitian]
      calc (CFC.sqrt ρ * dᴴ * (d * CFC.sqrt ρ)).trace
          = ((CFC.sqrt ρ * (dᴴ * d)) * CFC.sqrt ρ).trace := by
            congr 1
            simp only [Matrix.mul_assoc]
        _ = (CFC.sqrt ρ * (CFC.sqrt ρ * (dᴴ * d))).trace :=
            Matrix.trace_mul_comm _ _
        _ = (ρ * (dᴴ * d)).trace := by
            rw [← Matrix.mul_assoc, hs2]
        _ = 0 := h0
    have hzero : d * CFC.sqrt ρ = 0 :=
      Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp hkey
    have h := congrArg (fun M => M * (CFC.sqrt ρ)⁻¹) hzero
    simpa [Matrix.mul_assoc, Matrix.mul_inv_of_invertible]
      using h
  refine ⟨hfaithful, ?_, ?_⟩
  · intro ρ hρ N P P' hPN hP'N hPadj hP'adj x
    have hd : P x - P' x ∈ N := sub_mem (hPN x) (hP'N x)
    have h0 : (ρ * ((P x - P' x)ᴴ * (P x - P' x))).trace
        = 0 := by
      rw [show (P x - P' x)ᴴ * (P x - P' x)
          = (P x - P' x)ᴴ * P x - (P x - P' x)ᴴ * P' x from
        Matrix.mul_sub _ _ _,
        Matrix.mul_sub, Matrix.trace_sub,
        hPadj x _ hd, hP'adj x _ hd, sub_self]
    have := hfaithful ρ (P x - P' x) hρ h0
    exact sub_eq_zero.mp this
  · intro P hP y
    have h := hP y
    rwa [Matrix.star_eq_conjTranspose,
      Matrix.star_eq_conjTranspose] at h

end NCG
