/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Algebra.CliffordGenerates
import NCG.Grand.ControlledCompiler

/-!
# Score-pulse control, `su(4)` coverage, and the canonical
  controlled-history compiler
  (`thm:canonical-score-control-master`,
  `cor:external-su4-score-master`,
  `thm:canonical-history-compiler-master`, flagship manuscript)

* `score_pulse_group`: clause (i) — the Ising pulses
  `E(θ) = exp(-iθ Z_ε⊗Z_c)` form the exact one-parameter group
  `E(θ)E(θ') = E(θ+θ')`;
* `controlled_z_exact`: the boxed clause (iii) — the exact gate
  identity
  `CZ = e^{-iπ/4}·e^{iπZ_ε/4}·e^{iπZ_c/4}·e^{-iπZ_εZ_c/4}`,
  verified entrywise through the diagonal exponentials;
* `external_su4_span`: the corollary's finite core — the
  sixteen Pauli–Kronecker words span the full two-clock
  external factor `M₄(ℂ)` (re-exported from the proved
  `pauliKron_span`), so nothing outside the generated algebra
  survives;
* `canonical_compiler_master`: the compiler content — exact
  one-sided controlled lift `diag(1,U)` unitary, controlled
  letters multiplying to controlled words, and compiled
  controlled powers `Λ(U)ᵏ = Λ(Uᵏ)` (re-exported from the
  proved controlled-compiler multiplication table), the sense
  in which `G^ctrl = 0` for every primitive generator.

Rendering disclosed: the pulse-word implementation of `E(θ)`
from the raw Store flow, the branch-kickback supply of local
phases, the dynamical-Lie-algebra closure `⊕ⱼ su(2)ⱼ` and the
`su(4)` bracket generation (only the span is certified here),
and the dilation-carrier compilation of irreversible histories
are the manuscript's control-theoretic layer.
-/

open Matrix Kronecker

namespace NCG

/-- The Ising pulse generator `Z_ε ⊗ Z_c = diag(1,-1,-1,1)`. -/
noncomputable def pulseZZ : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.diagonal ![1, -1, -1, 1]

attribute [-instance]
  Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
open NormedSpace in
open scoped Norms.Operator in
/-- Clause (i): the Ising pulses form an exact one-parameter
group, `E(θ)E(θ') = E(θ+θ')`. -/
theorem score_pulse_group (θ θ' : ℝ) :
    exp ((-Complex.I * θ) • pulseZZ)
        * exp ((-Complex.I * θ') • pulseZZ)
      = exp ((-Complex.I * (θ + θ')) • pulseZZ) := by
  have hcomm : Commute ((-Complex.I * θ) • pulseZZ)
      ((-Complex.I * θ') • pulseZZ) :=
    ((Commute.refl pulseZZ).smul_left _).smul_right _
  rw [← Matrix.exp_add_of_commute _ _ hcomm]
  congr 1
  rw [mul_add, add_smul]

attribute [-instance]
  Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
open NormedSpace in
open scoped Norms.Operator in
/-- Boxed clause (iii): the exact controlled-`Z` gate
`CZ = e^{-iπ/4}·e^{iπZ_ε/4}·e^{iπZ_c/4}·e^{-iπZ_εZ_c/4}`. -/
theorem controlled_z_exact :
    Complex.exp (-(Real.pi / 4) * Complex.I) •
      (exp (((Real.pi / 4 : ℝ) * Complex.I) •
          Matrix.diagonal (![1, 1, -1, -1] : Fin 4 → ℂ))
        * exp (((Real.pi / 4 : ℝ) * Complex.I) •
          Matrix.diagonal (![1, -1, 1, -1] : Fin 4 → ℂ))
        * exp ((-(Real.pi / 4 : ℝ) * Complex.I) •
          Matrix.diagonal (![1, -1, -1, 1] : Fin 4 → ℂ)))
    = Matrix.diagonal ![1, 1, 1, -1] := by
  rw [show (((Real.pi / 4 : ℝ) * Complex.I) •
      Matrix.diagonal (![1, 1, -1, -1] : Fin 4 → ℂ))
    = Matrix.diagonal
        (((Real.pi / 4 : ℝ) * Complex.I) •
          (![1, 1, -1, -1] : Fin 4 → ℂ)) from
    (Matrix.diagonal_smul _ _).symm]
  rw [show (((Real.pi / 4 : ℝ) * Complex.I) •
      Matrix.diagonal (![1, -1, 1, -1] : Fin 4 → ℂ))
    = Matrix.diagonal
        (((Real.pi / 4 : ℝ) * Complex.I) •
          (![1, -1, 1, -1] : Fin 4 → ℂ)) from
    (Matrix.diagonal_smul _ _).symm]
  rw [show ((-(Real.pi / 4 : ℝ) * Complex.I) •
      Matrix.diagonal (![1, -1, -1, 1] : Fin 4 → ℂ))
    = Matrix.diagonal
        ((-(Real.pi / 4 : ℝ) * Complex.I) •
          (![1, -1, -1, 1] : Fin 4 → ℂ)) from
    (Matrix.diagonal_smul _ _).symm]
  rw [Matrix.exp_diagonal, Matrix.exp_diagonal,
    Matrix.exp_diagonal, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_smul]
  congr 1
  funext k
  rw [Pi.smul_apply]
  rw [Pi.coe_exp, Pi.coe_exp, Pi.coe_exp, Pi.smul_apply,
    Pi.smul_apply, Pi.smul_apply, ← Complex.exp_eq_exp_ℂ]
  have hone : ∀ z : ℂ, z = 0 → Complex.exp z = 1 :=
    fun z hz => hz ▸ Complex.exp_zero
  have hepi : Complex.exp (-((Real.pi : ℂ) * Complex.I)) = -1 := by
    rw [Complex.exp_neg, Complex.exp_pi_mul_I]
    norm_num
  have hnegone : ∀ z : ℂ,
      z = -((Real.pi : ℂ) * Complex.I) → Complex.exp z = -1 :=
    fun z hz => hz ▸ hepi
  fin_cases k <;> simp [smul_eq_mul] <;>
    rw [← Complex.exp_add, ← Complex.exp_add,
      ← Complex.exp_add] <;>
    first
      | exact hone _ (by ring)
      | exact hnegone _ (by ring)

/-- The corollary's finite core: the sixteen Pauli–Kronecker
words span the full two-clock external factor `M₄(ℂ)`. -/
theorem external_su4_span :
    Submodule.span ℂ
      (Set.range NCG.CommonOrigin.pauliKron) = ⊤ :=
  NCG.CommonOrigin.pauliKron_span

/-- The canonical compiler content: exact one-sided controlled
lift, controlled letters multiplying to controlled words, and
compiled controlled powers — `G^ctrl = 0` for every primitive
generator. -/
theorem canonical_compiler_master {n m : Type*} [Fintype n]
    [Fintype m] [DecidableEq n] [DecidableEq m]
    (P : Matrix n n ℂ) (hP : P * P = P) (U V : Matrix m m ℂ)
    (hU : Uᴴ * U = 1) (k : ℕ) :
    ((Matrix.fromBlocks (1 : Matrix n n ℂ) 0 0 U)ᴴ
        * Matrix.fromBlocks 1 0 0 U = 1)
    ∧ ((P ⊗ₖ U + (1 - P) ⊗ₖ (1 : Matrix m m ℂ))
        * (P ⊗ₖ V + (1 - P) ⊗ₖ (1 : Matrix m m ℂ))
        = P ⊗ₖ (U * V) + (1 - P) ⊗ₖ (1 : Matrix m m ℂ))
    ∧ ((P ⊗ₖ U + (1 - P) ⊗ₖ (1 : Matrix m m ℂ)) ^ k
        = P ⊗ₖ (U ^ k) + (1 - P) ⊗ₖ (1 : Matrix m m ℂ)) :=
  ⟨controlled_lift_unitary U hU,
    controlled_letters_multiply P hP U V,
    controlled_word_power P hP U k⟩

end NCG
