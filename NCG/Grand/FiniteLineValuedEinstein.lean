/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.LineValuedEinstein

/-!
# Finite line-valued quantum action and Einstein residual

This file supplies the finite connection/curvature layer omitted from the
original scalar treatment of `thm:SMST-line-valued-Einstein`.  A protected
finite configuration uses a cochain complex

`C⁰ --d₀--> C¹ --d₁--> C²`,  `d₁ d₀ = 0`.

For a polar amplitude `Z = exp(-S) s` with unit phase section and connection
cochain `α`, its logarithmic covariant response is
`Ξ = -dS + i α`.  We prove both boxed identities, exact gauge removal on the
trivial-holonomy branch, and the equivalence between flatness and trivial
holonomy when the protected complex is exact in degree one.  The existing
positive-metric residual theorem supplies the real/phase noncancellation
clause.
-/

open Matrix
open scoped ComplexOrder

namespace NCG

/-- Pointwise logarithmic connection coefficient of a nowhere-zero finite
amplitude section. -/
theorem finite_log_derivative_unique {X : Type*}
    (z dz : X → ℂ) (hz : ∀ x, z x ≠ 0) :
    ∃! Xi : X → ℂ, ∀ x, dz x = Xi x * z x := by
  refine ⟨fun x => dz x / z x, ?_, ?_⟩
  · intro x
    exact (div_mul_cancel₀ (dz x) (hz x)).symm
  · intro Xi hXi
    funext x
    rw [hXi x, mul_div_cancel_right₀ _ (hz x)]

/-- The logarithmic covariant response `Ξ = -dS + iα`. -/
def finitePhaseLogResponse {v e : Type*} [Fintype v]
    (d0 : Matrix e v ℂ) (S : v → ℂ) (alpha : e → ℂ) : e → ℂ :=
  -(d0 *ᵥ S) + Complex.I • alpha

/-- The finite phase curvature `Ω = d₁ α`. -/
def finitePhaseCurvature {e f : Type*} [Fintype e]
    (d1 : Matrix f e ℂ) (alpha : e → ℂ) : f → ℂ :=
  d1 *ᵥ alpha

/-- First boxed identity: `-Ξ = dS - iα`. -/
theorem neg_finitePhaseLogResponse {v e : Type*} [Fintype v]
    (d0 : Matrix e v ℂ) (S : v → ℂ) (alpha : e → ℂ) :
    -finitePhaseLogResponse d0 S alpha = d0 *ᵥ S - Complex.I • alpha := by
  unfold finitePhaseLogResponse
  abel

/-- Second boxed identity: `dΞ = iΩ`, using `d₁d₀ = 0`. -/
theorem differential_finitePhaseLogResponse {v e f : Type*}
    [Fintype v] [Fintype e]
    (d0 : Matrix e v ℂ) (d1 : Matrix f e ℂ)
    (hd : d1 * d0 = 0) (S : v → ℂ) (alpha : e → ℂ) :
    d1 *ᵥ finitePhaseLogResponse d0 S alpha =
      Complex.I • finitePhaseCurvature d1 alpha := by
  simp only [finitePhaseLogResponse, finitePhaseCurvature,
    Matrix.mulVec_add, Matrix.mulVec_neg, Matrix.mulVec_smul,
    Matrix.mulVec_mulVec, hd, Matrix.zero_mulVec, neg_zero, zero_add]

/-- Trivial holonomy in the protected finite complex: the connection cochain
is an exact gauge. -/
def FinitePhaseHolonomyTrivial {v e : Type*} [Fintype v]
    (d0 : Matrix e v ℂ) (alpha : e → ℂ) : Prop :=
  ∃ phi : v → ℂ, alpha = d0 *ᵥ phi

/-- Exactness in degree one. -/
def ExactAtFinitePhaseOne {v e f : Type*} [Fintype v] [Fintype e]
    (d0 : Matrix e v ℂ) (d1 : Matrix f e ℂ) : Prop :=
  ∀ alpha : e → ℂ, d1 *ᵥ alpha = 0 →
    ∃ phi : v → ℂ, alpha = d0 *ᵥ phi

/-- An exact phase gauge removes the imaginary connection response globally. -/
theorem trivialHolonomy_gauge_removal {v e : Type*} [Fintype v]
    (d0 : Matrix e v ℂ) (S : v → ℂ) (alpha : e → ℂ)
    (htriv : FinitePhaseHolonomyTrivial d0 alpha) :
    ∃ phi : v → ℂ,
      finitePhaseLogResponse d0 S alpha -
        Complex.I • (d0 *ᵥ phi) = -(d0 *ᵥ S) := by
  rcases htriv with ⟨phi, rfl⟩
  exact ⟨phi, by simp [finitePhaseLogResponse]⟩


/-- Existence of an ordinary scalar phase gauge: after one global phase
potential is chosen, the covariant logarithmic response is purely real. -/
def GlobalScalarPhaseGauge {v e : Type*} [Fintype v]
    (d0 : Matrix e v ℂ) (S : v → ℂ) (alpha : e → ℂ) : Prop :=
  ∃ phi : v → ℂ,
    finitePhaseLogResponse d0 S alpha -
      Complex.I • (d0 *ᵥ phi) = -(d0 *ᵥ S)

/-- A global ordinary scalar action exists exactly on the zero-curvature,
trivial-holonomy branch. -/
theorem globalScalarPhaseGauge_iff_flat_trivialHolonomy
    {v e f : Type*} [Fintype v] [Fintype e]
    (d0 : Matrix e v ℂ) (d1 : Matrix f e ℂ)
    (hd : d1 * d0 = 0) (S : v → ℂ) (alpha : e → ℂ) :
    GlobalScalarPhaseGauge d0 S alpha ↔
      finitePhaseCurvature d1 alpha = 0 ∧
        FinitePhaseHolonomyTrivial d0 alpha := by
  constructor
  · rintro ⟨phi, hphi⟩
    have hphase : Complex.I • alpha =
        Complex.I • (d0 *ᵥ phi) := by
      unfold finitePhaseLogResponse at hphi
      apply sub_eq_zero.mp
      calc
        Complex.I • alpha - Complex.I • (d0 *ᵥ phi) =
            (-(d0 *ᵥ S) + Complex.I • alpha -
              Complex.I • (d0 *ᵥ phi)) + d0 *ᵥ S := by abel
        _ = -(d0 *ᵥ S) + d0 *ᵥ S := by rw [hphi]
        _ = 0 := by abel
    have halpha : alpha = d0 *ᵥ phi :=
      smul_right_injective (e → ℂ) Complex.I_ne_zero hphase
    constructor
    · rw [finitePhaseCurvature, halpha, Matrix.mulVec_mulVec, hd,
        Matrix.zero_mulVec]
    · exact ⟨phi, halpha⟩
  · rintro ⟨_, htriv⟩
    exact trivialHolonomy_gauge_removal d0 S alpha htriv
/-- On an exact protected complex, zero curvature is equivalent to trivial
holonomy; exact connections are automatically flat. -/
theorem curvature_zero_iff_trivialHolonomy {v e f : Type*}
    [Fintype v] [Fintype e]
    (d0 : Matrix e v ℂ) (d1 : Matrix f e ℂ)
    (hd : d1 * d0 = 0) (hexact : ExactAtFinitePhaseOne d0 d1)
    (alpha : e → ℂ) :
    finitePhaseCurvature d1 alpha = 0 ↔
      FinitePhaseHolonomyTrivial d0 alpha := by
  constructor
  · intro hzero
    exact hexact alpha hzero
  · rintro ⟨phi, rfl⟩
    simp only [finitePhaseCurvature, Matrix.mulVec_mulVec, hd,
      Matrix.zero_mulVec]

/-- `thm:SMST-line-valued-Einstein`, finite protected-complex form. -/
theorem finite_line_valued_Einstein
    {X v e f n : Type*} [Fintype v] [Fintype e]
    [Fintype n] [DecidableEq n]
    (z dz : X → ℂ) (hz : ∀ x, z x ≠ 0)
    (d0 : Matrix e v ℂ) (d1 : Matrix f e ℂ)
    (hd : d1 * d0 = 0)
    (S : v → ℂ) (alpha : e → ℂ)
    (G : Matrix n n ℂ) (hG : G.PosDef) (E t : n → ℂ) :
    (∃! Xi : X → ℂ, ∀ x, dz x = Xi x * z x) ∧
    (-finitePhaseLogResponse d0 S alpha =
      d0 *ᵥ S - Complex.I • alpha) ∧
    (d1 *ᵥ finitePhaseLogResponse d0 S alpha =
      Complex.I • finitePhaseCurvature d1 alpha) ∧
    (GlobalScalarPhaseGauge d0 S alpha ↔
      finitePhaseCurvature d1 alpha = 0 ∧
        FinitePhaseHolonomyTrivial d0 alpha) ∧
    (((star E ⬝ᵥ G⁻¹.mulVec E).re +
      (star t ⬝ᵥ G⁻¹.mulVec t).re = 0) ↔ E = 0 ∧ t = 0) := by
  exact ⟨finite_log_derivative_unique z dz hz,
    neg_finitePhaseLogResponse d0 S alpha,
    differential_finitePhaseLogResponse d0 d1 hd S alpha,
    globalScalarPhaseGauge_iff_flat_trivialHolonomy d0 d1 hd S alpha,
    covariant_residual_split G hG E t⟩

end NCG
