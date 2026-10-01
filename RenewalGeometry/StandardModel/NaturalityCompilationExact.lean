/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Finite functional and word-moment realization
  (`prop:naturality-compilation`, spacetime–gauge duality manuscript)

Two routes to the naturality defect `d_nat = Tr(H_nat J_D)`.

**Contextual route.**  A contextual test bank determines the numbers `Tr(F_ℓ J_D)`.
If the real linear span of the tested functionals `F_ℓ` contains `H_nat` and the
identity, then `d_nat` and `Tr J_D` are determined by those numbers, without
determining `J_D` itself:

* `trace_determined_of_mem_span`: `H ∈ span_ℝ {F_ℓ}` and `Tr(F_ℓ J) = Tr(F_ℓ J')` for
  all `ℓ` imply `Tr(H J) = Tr(H J')`;
* `naturality_defect_and_trace_determined`: the two functionals `H_nat`, `I` together;
* `trace_determined_modulo_constants`: the refinement where the functional lies in the
  span modulo a functional constant on the declared feasible Choi class.

**Word-moment route.**  With a historical amplitude bank `(T_a)`,
`J_D = ∑_a |T_a⟩⟩⟨⟨T_a|` and `H_nat = ∑_X R_X* R_X + ∑_Y S_Y* S_Y`
(`eq:naturality-operator`),

`d_nat = ∑_a (∑_X ‖R_X T_a‖²_HS + ∑_Y ‖S_Y T_a‖²_HS)`   (`eq:word-naturality-defect`)

is a finite sum of squared Hilbert–Schmidt norms of inserted amplitudes
(`word_naturality_defect`).

Rendering disclosed: the port is an abstract finite coordinate space `p → ℂ`
(the amplitude space `Matrix m n ℂ` in Hilbert–Schmidt coordinates, `p = m × n`), the
inserted actions `R_X`, `S_Y` are matrices on it, and `‖·‖²_HS` is the coordinate
sum of `Complex.normSq`.  That each squared norm is a "word moment" evaluated by the
flat multiplication table (`thm:inserted-word-moments`) is the paper's interpretation
of the right-hand side and is not restated.  The "without determining the full Choi
operator" clause is the observation that the tested numbers do not pin down `J_D`; the
theorems only use them, never `J_D`.
-/

open Matrix

namespace RenewalGeometry
namespace NaturalityCompilation

section Contextual

variable {n ι : Type*} [Fintype n]

/-- **`prop:naturality-compilation`, contextual determinacy**: a functional in the real
span of the tested functionals is determined by the tested numbers. -/
theorem trace_determined_of_mem_span (F : ι → Matrix n n ℂ) (H : Matrix n n ℂ)
    (hH : H ∈ Submodule.span ℝ (Set.range F)) (J J' : Matrix n n ℂ)
    (hJ : ∀ ℓ, (F ℓ * J).trace = (F ℓ * J').trace) :
    (H * J).trace = (H * J').trace := by
  induction hH using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨ℓ, rfl⟩ := hx
      exact hJ ℓ
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul, add_mul, trace_add, trace_add, hx, hy]
  | smul r x _ hx => rw [Matrix.smul_mul, Matrix.smul_mul, trace_smul, trace_smul, hx]

/-- **`prop:naturality-compilation`, first clause**: if the real span of the tested
functionals contains `H_nat` and the identity, the bank determines `d_nat = Tr(H_nat J_D)`
and `Tr J_D`. -/
theorem naturality_defect_and_trace_determined [DecidableEq n]
    (F : ι → Matrix n n ℂ) (Hnat : Matrix n n ℂ)
    (hH : Hnat ∈ Submodule.span ℝ (Set.range F))
    (hI : (1 : Matrix n n ℂ) ∈ Submodule.span ℝ (Set.range F))
    (J J' : Matrix n n ℂ)
    (hJ : ∀ ℓ, (F ℓ * J).trace = (F ℓ * J').trace) :
    (Hnat * J).trace = (Hnat * J').trace ∧ J.trace = J'.trace := by
  refine ⟨trace_determined_of_mem_span F Hnat hH J J' hJ, ?_⟩
  have h := trace_determined_of_mem_span F 1 hI J J' hJ
  rwa [one_mul, one_mul] at h

/-- **`prop:naturality-compilation`, refinement**: it suffices that the functional lie
in the span modulo a functional `c` constant on the declared feasible Choi class. -/
theorem trace_determined_modulo_constants (F : ι → Matrix n n ℂ)
    (feasible : Set (Matrix n n ℂ)) (H H₀ c : Matrix n n ℂ)
    (hH : H = H₀ + c) (hH₀ : H₀ ∈ Submodule.span ℝ (Set.range F))
    (hc : ∀ J ∈ feasible, ∀ J' ∈ feasible, (c * J).trace = (c * J').trace)
    (J J' : Matrix n n ℂ) (hJf : J ∈ feasible) (hJ'f : J' ∈ feasible)
    (hJ : ∀ ℓ, (F ℓ * J).trace = (F ℓ * J').trace) :
    (H * J).trace = (H * J').trace := by
  rw [hH, add_mul, add_mul, trace_add, trace_add,
    trace_determined_of_mem_span F H₀ hH₀ J J' hJ, hc J hJf J' hJ'f]

end Contextual

section WordMoment

variable {p ιC ιW ιA : Type*} [Fintype p] [Fintype ιC] [Fintype ιW] [Fintype ιA]

/-- The naturality operator `H_nat = ∑_X R_X* R_X + ∑_Y S_Y* S_Y`
(`eq:naturality-operator`) on the port coordinates. -/
noncomputable def naturalityOperator (R : ιC → Matrix p p ℂ) (S : ιW → Matrix p p ℂ) :
    Matrix p p ℂ :=
  ∑ X, (R X)ᴴ * R X + ∑ Y, (S Y)ᴴ * S Y

/-- The Choi operator `J_D = ∑_a |T_a⟩⟩⟨⟨T_a|` of a historical amplitude bank. -/
noncomputable def amplitudeChoi (T : ιA → (p → ℂ)) : Matrix p p ℂ :=
  ∑ a, vecMulVec (T a) (star (T a))

/-- The naturality defect `d_nat = Tr(H_nat J_D)`. -/
noncomputable def naturalityDefect (R : ιC → Matrix p p ℂ) (S : ιW → Matrix p p ℂ)
    (J : Matrix p p ℂ) : ℂ :=
  (naturalityOperator R S * J).trace

/-- The squared Hilbert–Schmidt norm of a port vector. -/
noncomputable def portNormSq (v : p → ℂ) : ℝ := ∑ i, Complex.normSq (v i)

/-- `Tr(M* M |v⟩⟨v|) = ‖M v‖²`. -/
theorem trace_gram_mul_vecMulVec (M : Matrix p p ℂ) (v : p → ℂ) :
    (Mᴴ * M * vecMulVec v (star v)).trace = (portNormSq (M *ᵥ v) : ℂ) := by
  rw [mul_vecMulVec, trace_vecMulVec, ← mulVec_mulVec, dotProduct_comm,
    dotProduct_mulVec, ← star_mulVec, portNormSq]
  push_cast
  simp only [dotProduct, Pi.star_apply, Complex.normSq_eq_conj_mul_self, Complex.star_def]

/-- **`prop:naturality-compilation`, word-moment route** (`eq:word-naturality-defect`):
for a historical amplitude bank, the naturality defect is the finite sum of squared
Hilbert–Schmidt norms of the inserted amplitudes `R_X T_a`, `S_Y T_a`. -/
theorem word_naturality_defect (R : ιC → Matrix p p ℂ) (S : ιW → Matrix p p ℂ)
    (T : ιA → (p → ℂ)) :
    naturalityDefect R S (amplitudeChoi T)
      = ((∑ a, (∑ X, portNormSq (R X *ᵥ T a) + ∑ Y, portNormSq (S Y *ᵥ T a)) : ℝ) : ℂ) := by
  simp only [naturalityDefect, naturalityOperator, amplitudeChoi, Finset.mul_sum,
    Finset.sum_mul, add_mul, trace_add, trace_sum, trace_gram_mul_vecMulVec]
  push_cast
  rw [Finset.sum_add_distrib, Finset.sum_comm (f := fun a X => (portNormSq (R X *ᵥ T a) : ℂ)),
    Finset.sum_comm (f := fun a Y => (portNormSq (S Y *ᵥ T a) : ℂ))]

end WordMoment

end NaturalityCompilation
end RenewalGeometry

