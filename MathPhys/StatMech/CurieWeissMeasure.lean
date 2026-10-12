/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The Curie–Weiss measure and its single-site heat-bath weights

Split out of `MathPhys.StatMech.CurieWeiss`: the finite-volume Curie–Weiss measure
`μ_{N,λ,h}(η) ∝ exp(λ M²/(2N) + h M)` on `Fin N → Bool` (`cwWeight`, `cwPartition`,
`cwMeasure`), its spin-flip (deck) invariance at zero field, the single-site heat-bath
(Glauber) conditional weights `q_i(s|η_{-i}) = e^{s(λ M_{-i}/N + h)}/(2 cosh(λ M_{-i}/N + h))`
(`cwCond`), and single-site detailed balance (`cw_detailed_balance`).
-/

namespace MathPhys.Upstream


/-- The spin value of a cell orientation. -/
def spin (b : Bool) : ℝ := if b then 1 else -1

@[simp] theorem spin_true : spin true = 1 := rfl
@[simp] theorem spin_false : spin false = -1 := rfl

variable (N : ℕ)

/-- The total orientation `M_N(η) = ∑ η_i`. -/
def magSum (η : Fin N → Bool) : ℝ := ∑ i, spin (η i)

/-- **Definition `def:cw-renewal-measure` (Gibbs weight)**:
`exp(λ M²/(2N) + h M)` (which is `exp(N(λ m²/2 + h m))`). -/
noncomputable def cwWeight (lam h : ℝ) (η : Fin N → Bool) : ℝ :=
  Real.exp (lam / (2 * N) * (magSum N η) ^ 2 + h * magSum N η)

/-- The partition function `Z_{N,λ,h}`. -/
noncomputable def cwPartition (lam h : ℝ) : ℝ :=
  ∑ η : Fin N → Bool, cwWeight N lam h η

/-- **Definition `def:cw-renewal-measure`**: the finite-volume
orientation measure. -/
noncomputable def cwMeasure (lam h : ℝ) (η : Fin N → Bool) : ℝ :=
  cwWeight N lam h η / cwPartition N lam h

theorem cwWeight_pos (lam h : ℝ) (η : Fin N → Bool) :
    0 < cwWeight N lam h η := Real.exp_pos _

theorem cwPartition_pos (lam h : ℝ) : 0 < cwPartition N lam h :=
  Finset.sum_pos (fun η _ => cwWeight_pos N lam h η)
    ⟨fun _ => true, Finset.mem_univ _⟩

/-- The deck transformation flips every cell. -/
def deckFlip (η : Fin N → Bool) : Fin N → Bool := fun i => !(η i)

theorem magSum_deckFlip (η : Fin N → Bool) :
    magSum N (deckFlip N η) = -magSum N η := by
  unfold magSum deckFlip
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  cases η i <;> simp

/-- **Definition `def:cw-renewal-measure` (deck invariance at zero
field)**: the quadratic term rewards coherence but prefers neither
sheet. -/
theorem cwWeight_deck_invariant (lam : ℝ) (η : Fin N → Bool) :
    cwWeight N lam 0 (deckFlip N η) = cwWeight N lam 0 η := by
  unfold cwWeight
  rw [magSum_deckFlip]
  ring_nf

/-- The residual magnetization `M_{-i}(η) = M_N(η) − η_i`. -/
def magRes (η : Fin N → Bool) (i : Fin N) : ℝ :=
  magSum N η - spin (η i)

/-- **Definition `def:cw-heat-bath` (conditional weights)**:
`q_i(s|η_{-i}) = e^{s(λ M_{-i}/N + h)}/(2 cosh(λ M_{-i}/N + h))`. -/
noncomputable def cwCond (lam h : ℝ) (η : Fin N → Bool) (i : Fin N)
    (s : Bool) : ℝ :=
  Real.exp (spin s * (lam * magRes N η i / N + h))
    / (2 * Real.cosh (lam * magRes N η i / N + h))

/-- The conditional weights are strictly positive and normalized. -/
theorem cwCond_pos (lam h : ℝ) (η : Fin N → Bool) (i : Fin N)
    (s : Bool) : 0 < cwCond N lam h η i s := by
  unfold cwCond
  have hc : 0 < Real.cosh (lam * magRes N η i / N + h) :=
    Real.cosh_pos _
  positivity

theorem cwCond_sum (lam h : ℝ) (η : Fin N → Bool) (i : Fin N) :
    ∑ s : Bool, cwCond N lam h η i s = 1 := by
  unfold cwCond
  rw [Fintype.sum_bool, spin_true, spin_false, one_mul, neg_one_mul]
  set x : ℝ := lam * magRes N η i / N + h with hx
  rw [Real.cosh_eq]
  have he1 : (0 : ℝ) < Real.exp x + Real.exp (-x) := by positivity
  field_simp

theorem spin_sq (b : Bool) : spin b ^ 2 = 1 := by
  cases b <;> norm_num [spin]

theorem spin_not (b : Bool) : spin (!b) = -spin b := by
  cases b <;> simp [spin]

theorem cwMeasure_pos (lam h : ℝ) (η : Fin N → Bool) :
    0 < cwMeasure N lam h η :=
  div_pos (cwWeight_pos N lam h η) (cwPartition_pos N lam h)

theorem magSum_update (η : Fin N → Bool) (i : Fin N) (s : Bool) :
    magSum N (Function.update η i s)
      = magSum N η - spin (η i) + spin s := by
  unfold magSum
  rw [← Finset.sum_erase_add Finset.univ _ (Finset.mem_univ i),
    ← Finset.sum_erase_add Finset.univ (fun j => spin (η j))
      (Finset.mem_univ i), Function.update_self]
  have herase : ∑ j ∈ Finset.univ.erase i,
      spin (Function.update η i s j)
      = ∑ j ∈ Finset.univ.erase i, spin (η j) :=
    Finset.sum_congr rfl fun j hj => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [herase]
  ring

theorem magRes_update (η : Fin N → Bool) (i : Fin N) (s : Bool) :
    magRes N (Function.update η i s) i = magRes N η i := by
  unfold magRes
  rw [magSum_update, Function.update_self]
  ring

/-- **Theorem `thm:cw-finite-renewal` (reversibility)**: single-cell
detailed balance of the heat-bath weights with respect to the
Curie-Weiss orientation measure. -/
theorem cw_detailed_balance (lam h : ℝ) (η : Fin N → Bool)
    (i : Fin N) (s : Bool) :
    cwMeasure N lam h η * cwCond N lam h η i s
      = cwMeasure N lam h (Function.update η i s)
        * cwCond N lam h (Function.update η i s) i (η i) := by
  unfold cwMeasure cwCond
  rw [magRes_update]
  rw [div_mul_div_comm, div_mul_div_comm]
  congr 1
  unfold cwWeight
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  rw [magSum_update]
  have hs := spin_sq s
  have he := spin_sq (η i)
  unfold magRes
  linear_combination (lam / (2 * (N : ℝ))) * (he - hs)

end MathPhys.Upstream
