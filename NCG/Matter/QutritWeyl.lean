/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The qutrit Weyl pair: relations, traces, and the Weyl basis
  (machinery for `thm:projective-revision`, `thm:revision-MUB`,
   `thm:v5-relative-revision`, `cor:v5-bell-dephasing`,
   SM_emergence)

The clock-and-shift pair on `ℂ³` with `ω = e^{2πi/3}`:

* `qOmega_pow_three` / `qOmega_sq_add` / `qOmega_conj` — the cube
  root of unity and its algebra;
* `qZ_mul_qX` — the Weyl commutation `ZX = ω·XZ`;
* `qW_mul` — the Weyl word calculus
  `W(a,b)·W(c,d) = ω^{bc}·W(a+c,b+d)`;
* `qW_cube` — every Weyl word cubes to the identity;
* `qW_trace_eq_zero` — nonidentity Weyl words are traceless;
* `qW_conjTranspose` — `W(a,b)† = ω^{ab}·W(2a,2b)` (unitarity);
* `qW_linearIndependent` / `qW_span_top` — the nine Weyl words are
  a basis of `M₃(ℂ)` (Hilbert–Schmidt orthogonality).
-/

namespace NCG

open Matrix Complex

noncomputable section

/-- The primitive cube root of unity `ω = e^{2πi/3}`. -/
def qOmega : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3)

@[simp] lemma qOmega_pow_three : qOmega ^ 3 = 1 := by
  rw [qOmega, ← Complex.exp_nat_mul]
  rw [show (3 : ℕ) * (2 * (Real.pi : ℂ) * Complex.I / 3)
      = 2 * Real.pi * Complex.I by push_cast; ring]
  exact Complex.exp_two_pi_mul_I

lemma qOmega_ne_zero : qOmega ≠ 0 := Complex.exp_ne_zero _

lemma qOmega_ne_one : qOmega ≠ 1 := by
  rw [qOmega]
  intro h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
  have hpi : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  field_simp at hn
  have hz : (1 : ℤ) = 3 * n := by exact_mod_cast hn
  omega

lemma qOmega_sq_add : qOmega ^ 2 + qOmega + 1 = 0 := by
  have h : (qOmega - 1) * (qOmega ^ 2 + qOmega + 1) = 0 := by
    linear_combination qOmega_pow_three
  rcases mul_eq_zero.mp h with h1 | h2
  · exact absurd (by linear_combination h1) qOmega_ne_one
  · exact h2

lemma qOmega_mul_sq : qOmega * qOmega ^ 2 = 1 := by
  linear_combination qOmega_pow_three

lemma qOmega_conj : (starRingEnd ℂ) qOmega = qOmega ^ 2 := by
  have hnorm : ‖qOmega‖ = 1 := by
    rw [qOmega, Complex.norm_exp]
    rw [show (2 * (Real.pi : ℂ) * Complex.I / 3).re = 0 by simp]
    exact Real.exp_zero
  have h1 : (starRingEnd ℂ) qOmega * qOmega = 1 := by
    rw [mul_comm, Complex.mul_conj]
    rw [show (Complex.normSq qOmega : ℂ) = (‖qOmega‖ : ℝ) ^ 2 by
      rw [Complex.normSq_eq_norm_sq]; push_cast; ring]
    rw [hnorm]
    norm_num
  have h2 : qOmega ^ 2 * qOmega = 1 := by
    linear_combination qOmega_pow_three
  exact mul_right_cancel₀ qOmega_ne_zero (h1.trans h2.symm)

lemma qOmega_pow_mod (m : ℕ) : qOmega ^ m = qOmega ^ (m % 3) := by
  conv_lhs => rw [← Nat.div_add_mod m 3]
  rw [pow_add, pow_mul, qOmega_pow_three, one_pow, one_mul]

/-- The unbiased-sum identity `1 + ω^m + ω^{2m} = 0` for `3 ∤ m`. -/
lemma qOmega_sum_of_not_dvd {m : ℕ} (h : ¬ 3 ∣ m) :
    1 + qOmega ^ m + qOmega ^ (2 * m) = 0 := by
  rw [qOmega_pow_mod m, qOmega_pow_mod (2 * m)]
  have hm : m % 3 = 1 ∨ m % 3 = 2 := by omega
  rcases hm with hm | hm
  · rw [hm, show 2 * m % 3 = 2 by omega]
    linear_combination qOmega_sq_add
  · rw [hm, show 2 * m % 3 = 1 by omega]
    linear_combination qOmega_sq_add

lemma qOmega_sq_ne_one : qOmega ^ 2 ≠ 1 := by
  intro h
  have hw : qOmega = -2 := by linear_combination qOmega_sq_add - h
  rw [hw] at h
  norm_num at h

lemma qOmega_ne_sq : qOmega ≠ qOmega ^ 2 := by
  intro h
  have h0 : qOmega * (1 - qOmega) = 0 := by linear_combination h
  rcases mul_eq_zero.mp h0 with h1 | h1
  · exact qOmega_ne_zero h1
  · exact qOmega_ne_one (by linear_combination - h1)

lemma qOmega_pow_ne {k l : ℕ} (hk : k < 3) (hl : l < 3)
    (hne : k ≠ l) : qOmega ^ k ≠ qOmega ^ l := by
  interval_cases k <;> interval_cases l
  · exact absurd rfl hne
  · intro h
    rw [pow_zero, pow_one] at h
    exact qOmega_ne_one h.symm
  · intro h
    rw [pow_zero] at h
    exact qOmega_sq_ne_one h.symm
  · intro h
    rw [pow_zero, pow_one] at h
    exact qOmega_ne_one h
  · exact absurd rfl hne
  · intro h
    rw [pow_one] at h
    exact qOmega_ne_sq h
  · intro h
    rw [pow_zero] at h
    exact qOmega_sq_ne_one h
  · intro h
    rw [pow_one] at h
    exact qOmega_ne_sq h.symm
  · exact absurd rfl hne

/-- The qutrit shift `X|j⟩ = |j+1⟩`. -/
def qX : Matrix (Fin 3) (Fin 3) ℂ := !![0, 0, 1; 1, 0, 0; 0, 1, 0]

/-- The qutrit clock `Z|j⟩ = ω^j|j⟩`. -/
def qZ : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1, 0, 0; 0, qOmega, 0; 0, 0, qOmega ^ 2]

lemma qX_pow_two : qX ^ 2 = !![0, 1, 0; 0, 0, 1; 1, 0, 0] := by
  rw [pow_two, qX]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three]

lemma qX_pow_three : qX ^ 3 = 1 := by
  rw [pow_succ, qX_pow_two, qX]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three]

lemma qZ_pow_two : qZ ^ 2
    = !![1, 0, 0; 0, qOmega ^ 2, 0; 0, 0, qOmega] := by
  rw [pow_two, qZ]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three]
  · ring
  · linear_combination qOmega * qOmega_pow_three

lemma qZ_pow_three : qZ ^ 3 = 1 := by
  rw [pow_succ, qZ_pow_two, qZ]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three]
  · linear_combination qOmega_pow_three
  · linear_combination qOmega_pow_three

/-- The Weyl commutation relation `ZX = ω·XZ`. -/
lemma qZ_mul_qX : qZ * qX = qOmega • (qX * qZ) := by
  rw [qZ, qX]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, smul_eq_mul]
  · linear_combination - qOmega_pow_three
  · ring

lemma qZ_mul_qX_pow (c : ℕ) :
    qZ * qX ^ c = qOmega ^ c • (qX ^ c * qZ) := by
  induction c with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ← mul_assoc, ih, Matrix.smul_mul, mul_assoc,
      qZ_mul_qX, Matrix.mul_smul, smul_smul, ← mul_assoc,
      ← pow_succ, ← pow_succ]

lemma qZ_pow_mul_qX_pow (b c : ℕ) :
    qZ ^ b * qX ^ c = qOmega ^ (b * c) • (qX ^ c * qZ ^ b) := by
  induction b with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, mul_assoc, qZ_mul_qX_pow, Matrix.mul_smul,
      ← mul_assoc, ih, Matrix.smul_mul, smul_smul, mul_assoc,
      ← pow_succ, ← pow_add]
    rw [show c + n * c = (n + 1) * c by ring]

/-- The Weyl word `W(a,b) = X^a Z^b`. -/
def qW (a b : ℕ) : Matrix (Fin 3) (Fin 3) ℂ := qX ^ a * qZ ^ b

@[simp] lemma qW_zero_zero : qW 0 0 = 1 := by simp [qW]

/-- The Weyl multiplication law
`W(a,b)·W(c,d) = ω^{bc}·W(a+c, b+d)`. -/
lemma qW_mul (a b c d : ℕ) :
    qW a b * qW c d = qOmega ^ (b * c) • qW (a + c) (b + d) := by
  rw [qW, qW, qW, mul_assoc, ← mul_assoc (qZ ^ b),
    qZ_pow_mul_qX_pow, Matrix.smul_mul, Matrix.mul_smul]
  rw [mul_assoc, ← mul_assoc, ← mul_assoc, ← pow_add, mul_assoc,
    ← pow_add]

/-- Weyl words only depend on the exponents mod `3`. -/
lemma qW_mod (a b : ℕ) : qW a b = qW (a % 3) (b % 3) := by
  rw [qW, qW]
  congr 1
  · conv_lhs => rw [← Nat.div_add_mod a 3]
    rw [pow_add, pow_mul, qX_pow_three, one_pow, one_mul]
  · conv_lhs => rw [← Nat.div_add_mod b 3]
    rw [pow_add, pow_mul, qZ_pow_three, one_pow, one_mul]

/-- Every Weyl word cubes to the identity. -/
lemma qW_cube (a b : ℕ) : qW a b ^ 3 = 1 := by
  have h2 : qW a b ^ 2 = qOmega ^ (b * a) • qW (a + a) (b + b) := by
    rw [pow_two, qW_mul]
  have h3 : qW a b ^ 3
      = qOmega ^ (b * a) • (qW (a + a) (b + b) * qW a b) := by
    rw [pow_succ, h2, Matrix.smul_mul]
  rw [h3, qW_mul, smul_smul, ← pow_add, qW_mod,
    show (a + a + a) % 3 = 0 by omega,
    show (b + b + b) % 3 = 0 by omega, qW_zero_zero,
    show b * a + (b + b) * a = 3 * (a * b) by ring,
    qOmega_pow_mod, Nat.mul_mod_right, pow_zero, one_smul]

lemma trace_qX : qX.trace = 0 := by
  rw [qX]
  simp [Matrix.trace_fin_three]

lemma trace_qX_sq : (qX ^ 2).trace = 0 := by
  rw [qX_pow_two]
  simp [Matrix.trace_fin_three]

lemma trace_qZ : qZ.trace = 0 := by
  rw [qZ]
  simp [Matrix.trace_fin_three]
  linear_combination qOmega_sq_add

lemma trace_qZ_sq : (qZ ^ 2).trace = 0 := by
  rw [qZ_pow_two]
  simp [Matrix.trace_fin_three]
  linear_combination qOmega_sq_add

lemma trace_qXZ : (qX * qZ).trace = 0 := by
  rw [qX, qZ]
  simp [Matrix.trace_fin_three]

lemma trace_qXZ2 : (qX * qZ ^ 2).trace = 0 := by
  rw [qZ_pow_two, qX]
  simp [Matrix.trace_fin_three]

lemma trace_qX2Z : (qX ^ 2 * qZ).trace = 0 := by
  rw [qX_pow_two, qZ]
  simp [Matrix.trace_fin_three]

lemma trace_qX2Z2 : (qX ^ 2 * qZ ^ 2).trace = 0 := by
  rw [qX_pow_two, qZ_pow_two]
  simp [Matrix.trace_fin_three]

/-- Nonidentity Weyl words are traceless. -/
lemma qW_trace_zero {a b : ℕ} (h : ¬ (a % 3 = 0 ∧ b % 3 = 0)) :
    (qW a b).trace = 0 := by
  rw [qW_mod, qW]
  have ha : a % 3 < 3 := Nat.mod_lt _ (by norm_num)
  have hb : b % 3 < 3 := Nat.mod_lt _ (by norm_num)
  interval_cases (a % 3) <;> interval_cases (b % 3)
  · exact absurd ⟨rfl, rfl⟩ h
  · simpa using trace_qZ
  · simpa using trace_qZ_sq
  · simpa using trace_qX
  · rw [pow_one, pow_one]
    exact trace_qXZ
  · rw [pow_one]
    exact trace_qXZ2
  · simpa using trace_qX_sq
  · rw [pow_one]
    exact trace_qX2Z
  · exact trace_qX2Z2

lemma qX_conjTranspose : qXᴴ = qX ^ 2 := by
  rw [qX_pow_two, qX]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.conjTranspose_apply]

lemma qZ_conjTranspose : qZᴴ = qZ ^ 2 := by
  rw [qZ_pow_two, qZ]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.conjTranspose_apply, qOmega_conj]
  linear_combination qOmega * qOmega_pow_three

/-- `W(a,b)† = ω^{ab}·W(2a,2b)`. -/
lemma qW_conjTranspose (a b : ℕ) :
    (qW a b)ᴴ = qOmega ^ (a * b) • qW (2 * a) (2 * b) := by
  rw [qW, Matrix.conjTranspose_mul, Matrix.conjTranspose_pow,
    Matrix.conjTranspose_pow, qX_conjTranspose, qZ_conjTranspose,
    ← pow_mul, ← pow_mul, mul_comm (2 : ℕ) a, mul_comm (2 : ℕ) b,
    qZ_pow_mul_qX_pow, ← qW]
  rw [show b * 2 * (a * 2) = a * b + 3 * (a * b) by ring,
    qOmega_pow_mod, Nat.add_mul_mod_self_left, ← qOmega_pow_mod]

/-- Hilbert–Schmidt pairing of Weyl words: `⟨W(a,b), W(c,d)⟩ = 3δ`. -/
lemma qW_pairing {a b c d : ℕ} (ha : a < 3) (hb : b < 3)
    (hc : c < 3) (hd : d < 3) :
    ((qW a b)ᴴ * qW c d).trace
      = if a = c ∧ b = d then 3 else 0 := by
  rw [qW_conjTranspose, Matrix.smul_mul, qW_mul, smul_smul,
    Matrix.trace_smul, smul_eq_mul]
  by_cases h : a = c ∧ b = d
  · obtain ⟨rfl, rfl⟩ := h
    rw [if_pos ⟨rfl, rfl⟩, qW_mod,
      show (2 * a + a) % 3 = 0 by omega,
      show (2 * b + b) % 3 = 0 by omega, qW_zero_zero,
      Matrix.trace_one, ← pow_add,
      show a * b + 2 * b * a = 3 * (a * b) by ring,
      qOmega_pow_mod, Nat.mul_mod_right, pow_zero, one_mul]
    simp
  · rw [if_neg h, qW_trace_zero (by omega), mul_zero]

/-- The nine Weyl words indexed by `𝔽₃²`. -/
def qWfam (p : Fin 3 × Fin 3) : Matrix (Fin 3) (Fin 3) ℂ :=
  qW (p.1 : ℕ) (p.2 : ℕ)

/-- The nine Weyl words are linearly independent
(Hilbert–Schmidt orthogonality). -/
lemma qW_linearIndependent : LinearIndependent ℂ qWfam := by
  rw [Fintype.linearIndependent_iff]
  intro c hc p
  have hp := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ =>
    ((qWfam p)ᴴ * M).trace) hc
  simp only [Finset.mul_sum, Matrix.mul_smul, Matrix.trace_sum,
    Matrix.trace_smul, Matrix.mul_zero, Matrix.trace_zero,
    smul_eq_mul] at hp
  rw [Finset.sum_eq_single p] at hp
  · simp only [qWfam] at hp
    rw [qW_pairing p.1.isLt p.2.isLt p.1.isLt p.2.isLt,
      if_pos ⟨rfl, rfl⟩] at hp
    have h3 : (3 : ℂ) ≠ 0 := by norm_num
    exact (mul_eq_zero.mp hp).resolve_right h3
  · intro q _ hqp
    simp only [qWfam]
    rw [qW_pairing p.1.isLt p.2.isLt q.1.isLt q.2.isLt, if_neg,
      mul_zero]
    intro hco
    exact hqp (Prod.ext (Fin.ext hco.1.symm) (Fin.ext hco.2.symm))
  · intro hmem
    exact absurd (Finset.mem_univ p) hmem

/-- The nine Weyl words span `M₃(ℂ)`. -/
lemma qW_span_top : Submodule.span ℂ (Set.range qWfam) = ⊤ := by
  apply LinearIndependent.span_eq_top_of_card_eq_finrank
    qW_linearIndependent
  simp [Module.finrank_matrix]

end

end NCG
