/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Flagship.ClockQuarterRoot

/-!
# Score-bus entangler and exact canonical writer
  (`lem:score-bus-entangler`, `thm:canonical-writer`,
   Gran-Tensor manuscript)

* `entangler_kraus_prob` / `entangler_povm` /
  `entangler_unitary` / `entangler_quarter`: the fresh
  score-sign Kraus operators `K_m = ½(I - imZ_A⊗Z_B)` form an
  exact POVM with state-independent outcome probability `½`
  (`K_mᴴK_m = ½·I`), each `√2·K_m` is unitary with adjoint the
  opposite outcome (so the available branch correction
  identifies the two outcomes), and the quarter-rotation
  property `(√2K_m)² = -im·Z_A⊗Z_B` holds — the algebraic form
  of `√2K_m = e^{-imπZ_AZ_B/4}`;
* `canonical_writer`: for a Hermitian projection `P` the writer
  `U_P = I⊗Q + X⊗P` (`Q = I - P`) is a self-adjoint involution,
  commutes with `I⊗P`, records the blank inclusion
  (`U_P(|0⟩⊗ψ) = |0⟩⊗Qψ + |1⟩⊗Pψ`), and has exact phase
  kickback `U_P(Z⊗I)U_P = Z⊗(I-2P)` — unitary, nondemolition,
  lossless, and derived rather than postulated.

Rendering disclosed: the derivation of `K_m` from
`CZ_{Q,A}CZ_{Q,B}` and the `|y_m⟩` resolution is the
manuscript's circuit bookkeeping; the displayed operator
identities proved here are its content.  The retained bit is a
fixed fair coin because `K_mᴴK_m = ½·I` is state independent.
-/

open Matrix Kronecker

namespace NCG

noncomputable section

/-- The two-clock `Z⊗Z` word. -/
def zzWord : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  clockZ ⊗ₖ clockZ

/-- The score-sign Kraus operator `K_m = ½(I - imZ⊗Z)`,
`m = ±1`. -/
def entanglerK (m : ℤ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  (1 / 2 : ℂ) • (1 - ((m : ℂ) * Complex.I) • zzWord)

private lemma zz_sq : zzWord * zzWord = 1 := by
  rw [zzWord, ← Matrix.mul_kronecker_mul,
    pauli_relations.2.1.2.2, Matrix.one_kronecker_one]

private lemma zz_herm : zzWordᴴ = zzWord := by
  rw [zzWord]
  rw [show (clockZ ⊗ₖ clockZ)ᴴ = clockZᴴ ⊗ₖ clockZᴴ from by
    ext ⟨a, b⟩ ⟨c, d⟩
    simp [Matrix.conjTranspose_apply,
      Matrix.kroneckerMap_apply]]
  rw [pauli_relations.1.2.2]

private lemma entanglerK_conjTranspose (m : ℤ) :
    (entanglerK m)ᴴ = entanglerK (-m) := by
  rw [entanglerK, entanglerK, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_sub, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one, zz_herm]
  congr 2
  · simp
  · push_cast
    simp

private lemma entangler_mul (m m' : ℤ) :
    entanglerK m * entanglerK m'
      = (1 / 4 : ℂ) •
        ((1 - ((m : ℂ) * (m' : ℂ)) • (1 : Matrix (Fin 2 × Fin 2)
            (Fin 2 × Fin 2) ℂ))
          - (((m : ℂ) + (m' : ℂ)) * Complex.I) • zzWord) := by
  rw [entanglerK, entanglerK, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub,
    Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, zz_sq]
  rw [show ((m : ℂ) * Complex.I * ((m' : ℂ) * Complex.I))
      = -((m : ℂ) * (m' : ℂ)) from by
    ring_nf
    rw [Complex.I_sq]
    ring]
  rw [show (1 / 2 * (1 / 2) : ℂ) = 1 / 4 from by norm_num]
  match_scalars <;> ring

/-- Outcome probability is `½` independently of the target:
`K_mᴴK_m = ½·I`. -/
theorem entangler_kraus_prob (m : ℤ) (hm : m = 1 ∨ m = -1) :
    (entanglerK m)ᴴ * entanglerK m
      = (1 / 2 : ℂ) • (1 : Matrix (Fin 2 × Fin 2)
          (Fin 2 × Fin 2) ℂ) := by
  rw [entanglerK_conjTranspose, entangler_mul]
  rcases hm with h | h <;> subst h <;>
    · push_cast
      match_scalars <;> ring

/-- The POVM completeness relation `K₊ᴴK₊ + K₋ᴴK₋ = I`. -/
theorem entangler_povm :
    (entanglerK 1)ᴴ * entanglerK 1
      + (entanglerK (-1))ᴴ * entanglerK (-1) = 1 := by
  rw [entangler_kraus_prob 1 (Or.inl rfl),
    entangler_kraus_prob (-1) (Or.inr rfl)]
  match_scalars
  ring

/-- Both outcomes are unitary after normalization and mutually
adjoint — the available branch correction identifies them. -/
theorem entangler_unitary (m : ℤ) (hm : m = 1 ∨ m = -1) :
    ((Real.sqrt 2 : ℂ) • entanglerK m)ᴴ
        * ((Real.sqrt 2 : ℂ) • entanglerK m) = 1
    ∧ ((Real.sqrt 2 : ℂ) • entanglerK m)ᴴ
      = (Real.sqrt 2 : ℂ) • entanglerK (-m) := by
  have h2 : ((Real.sqrt 2 : ℂ)) * (Real.sqrt 2 : ℂ) = 2 := by
    rw [← Complex.ofReal_mul]
    norm_num [Real.mul_self_sqrt]
  have hstar : star ((Real.sqrt 2 : ℝ) : ℂ)
      = ((Real.sqrt 2 : ℝ) : ℂ) := by
    simp
  constructor
  · rw [Matrix.conjTranspose_smul, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, hstar,
      entangler_kraus_prob m hm, h2]
    match_scalars
    ring
  · rw [Matrix.conjTranspose_smul, entanglerK_conjTranspose,
      hstar]

/-- The quarter-rotation property `(√2K_m)² = -im·Z⊗Z` — the
algebraic form of `√2K_m = e^{-imπZ_AZ_B/4}`. -/
theorem entangler_quarter (m : ℤ) (hm : m = 1 ∨ m = -1) :
    ((Real.sqrt 2 : ℂ) • entanglerK m)
        * ((Real.sqrt 2 : ℂ) • entanglerK m)
      = (-(m : ℂ) * Complex.I) • zzWord := by
  have h2 : ((Real.sqrt 2 : ℂ)) * (Real.sqrt 2 : ℂ) = 2 := by
    rw [← Complex.ofReal_mul]
    norm_num [Real.mul_self_sqrt]
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, h2,
    entangler_mul]
  rcases hm with h | h <;> subst h <;>
    · push_cast
      match_scalars <;> ring

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
private lemma neg_kron (A : Matrix (Fin 2) (Fin 2) ℂ)
    (B : Matrix n n ℂ) : (-A) ⊗ₖ B = -(A ⊗ₖ B) := by
  rw [show -A = (-1 : ℂ) • A from by simp,
    Matrix.smul_kronecker]
  simp

omit [Fintype n] [DecidableEq n] in
private lemma kron_sub (A : Matrix (Fin 2) (Fin 2) ℂ)
    (B C : Matrix n n ℂ) :
    A ⊗ₖ (B - C) = A ⊗ₖ B - A ⊗ₖ C := by
  rw [sub_eq_add_neg, Matrix.kronecker_add,
    show -C = (-1 : ℂ) • C from by simp,
    Matrix.kronecker_smul]
  simp [sub_eq_add_neg]

/-- The canonical writer `U_P = I⊗Q + X⊗P` on
`writer ⊗ target`. -/
def writerU (P : Matrix n n ℂ) :
    Matrix (Fin 2 × n) (Fin 2 × n) ℂ :=
  (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (1 - P) + clockX ⊗ₖ P

/-- The blank state `|0⟩⊗ψ`. -/
def blankVec (ψ : n → ℂ) : Fin 2 × n → ℂ :=
  fun p => if p.1 = 0 then ψ p.2 else 0

/-- The recorded state `|0⟩⊗Qψ + |1⟩⊗Pψ`. -/
def recordVec (P : Matrix n n ℂ) (ψ : n → ℂ) :
    Fin 2 × n → ℂ :=
  fun p => if p.1 = 0 then ((1 - P) *ᵥ ψ) p.2
    else (P *ᵥ ψ) p.2

omit [DecidableEq n] in
private lemma kron_mulVec_blank
    (A : Matrix (Fin 2) (Fin 2) ℂ) (B : Matrix n n ℂ)
    (ψ : n → ℂ) (i : Fin 2) (a : n) :
    ((A ⊗ₖ B) *ᵥ blankVec ψ) (i, a)
      = A i 0 * (B *ᵥ ψ) a := by
  rw [Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
  rw [Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl
    fun b _ => show (A ⊗ₖ B) (i, a) (j, b) * blankVec ψ (j, b)
      = (if j = 0 then A i j * (B a b * ψ b) else 0) from by
    by_cases hj : j = 0 <;>
      simp [hj, blankVec, Matrix.kroneckerMap_apply, mul_assoc]]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun b _ => by
    rw [Finset.sum_ite_eq' Finset.univ (0 : Fin 2)
      (fun j => A i j * (B a b * ψ b))]]
  simp [Matrix.mulVec, dotProduct, Finset.mul_sum]

/-- `thm:canonical-writer`: the writer is a self-adjoint
involution, commutes with `I⊗P`, records the blank state, and
has exact phase kickback `U_P(Z⊗I)U_P = Z⊗(I-2P)`. -/
theorem canonical_writer (P : Matrix n n ℂ)
    (hidem : P * P = P) (hherm : Pᴴ = P) :
    (writerU P)ᴴ = writerU P
    ∧ writerU P * writerU P = 1
    ∧ writerU P * ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ P)
      = ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ P) * writerU P
    ∧ (∀ ψ : n → ℂ, writerU P *ᵥ blankVec ψ = recordVec P ψ)
    ∧ writerU P * (clockZ ⊗ₖ (1 : Matrix n n ℂ)) * writerU P
      = clockZ ⊗ₖ (1 - 2 • P) := by
  obtain ⟨⟨hXh, -, -⟩, ⟨hXX, -, -⟩, ⟨-, -, hZX⟩⟩ :=
    pauli_relations
  have hQ : (1 - P) * (1 - P) = 1 - P := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul,
      Matrix.one_mul, hidem]
    abel
  have hQP : (1 - P) * P = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, hidem, sub_self]
  have hPQ : P * (1 - P) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, hidem, sub_self]
  have hXZ : clockX * clockZ = -(clockZ * clockX) := by
    have h := congrArg (fun M => M - clockZ * clockX) hZX
    simpa using h
  have hXZX : clockX * clockZ * clockX = -clockZ := by
    rw [hXZ, Matrix.neg_mul, Matrix.mul_assoc, hXX,
      Matrix.mul_one]
  have hkronH : ∀ (A : Matrix (Fin 2) (Fin 2) ℂ)
      (B : Matrix n n ℂ), (A ⊗ₖ B)ᴴ = Aᴴ ⊗ₖ Bᴴ := by
    intro A B
    ext ⟨a, b⟩ ⟨c, d⟩
    simp [Matrix.conjTranspose_apply,
      Matrix.kroneckerMap_apply]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [writerU, Matrix.conjTranspose_add, hkronH, hkronH,
      Matrix.conjTranspose_one, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_one, hherm, hXh]
  · rw [writerU, Matrix.add_mul, Matrix.mul_add,
      Matrix.mul_add]
    simp only [← Matrix.mul_kronecker_mul, Matrix.one_mul,
      Matrix.mul_one, hXX, hQ, hQP, hPQ, hidem,
      Matrix.kronecker_zero, add_zero, zero_add]
    rw [← Matrix.kronecker_add, sub_add_cancel,
      Matrix.one_kronecker_one]
  · rw [writerU, Matrix.add_mul, Matrix.mul_add]
    simp only [← Matrix.mul_kronecker_mul, Matrix.one_mul,
      Matrix.mul_one, hQP, hPQ, hidem]
  · intro ψ
    funext ⟨i, a⟩
    rw [writerU, Matrix.add_mulVec, Pi.add_apply,
      kron_mulVec_blank, kron_mulVec_blank, recordVec]
    fin_cases i <;>
      simp [clockX, Matrix.one_apply]
  · rw [writerU, Matrix.add_mul, Matrix.add_mul,
      Matrix.mul_add, Matrix.mul_add]
    simp only [← Matrix.mul_kronecker_mul, Matrix.one_mul,
      Matrix.mul_one, hQ, hQP, hPQ, hidem, hXZX,
      Matrix.kronecker_zero, add_zero, zero_add, neg_kron]
    rw [show (1 : Matrix n n ℂ) - 2 • P = 1 - P - P from by
      rw [two_smul]
      abel]
    rw [kron_sub, kron_sub, kron_sub]
    abel

end

end NCG
