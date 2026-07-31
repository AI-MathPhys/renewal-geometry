/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Grading ambiguity of a signed protected block
  (`thm:grading-ambiguity-main`, SM_emergence)

For a traceless Hermitian `2×2` block `S = s·n̂·σ` and a trace-zero
grading `J = m̂·σ`:

* `pauliVec` — the Pauli vector `v·σ`;
* `pauli_square` — `(v·σ)² = |v|²·1`;
* `pauli_sandwich` — the reflection identity
  `(m·σ)(n·σ)(m·σ) = 2(m·n)(m·σ) - |m|²(n·σ)`;
* `grading_odd_part_sq` — the `J`-odd part of `S` squares to
  `m_J²·1` with `m_J² = s²(1-(n̂·m̂)²)`: its singular value is
  `m_J = s·√(1-(n̂·m̂)²)`;
* `grading_ambiguity_range` — as the grading axis `m̂` varies,
  `m_J` attains every value in `[0, s]`.

Hence a signed spectrum alone does not determine a physical
left–right split.
-/

namespace NCG

open Matrix

/-- The Euclidean dot product on three-vectors. -/
def dot3 (v w : Fin 3 → ℝ) : ℝ :=
  v 0 * w 0 + v 1 * w 1 + v 2 * w 2

/-- The Pauli vector `v·σ = v₁σ₁ + v₂σ₂ + v₃σ₃`. -/
noncomputable def pauliVec (v : Fin 3 → ℝ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![(v 2 : ℂ), (v 0 : ℂ) - (v 1 : ℂ) * Complex.I;
     (v 0 : ℂ) + (v 1 : ℂ) * Complex.I, -(v 2 : ℂ)]

set_option linter.flexible false in
/-- `(v·σ)² = |v|²·1`. -/
theorem pauli_square (v : Fin 3 → ℝ) :
    pauliVec v * pauliVec v
      = ((dot3 v v : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliVec, dot3, Matrix.mul_apply, Fin.sum_univ_two,
      Complex.ext_iff] <;>
    (try constructor) <;> ring

set_option linter.flexible false in
/-- The reflection identity
`(m·σ)(n·σ)(m·σ) = 2(m·n)(m·σ) - |m|²(n·σ)`. -/
theorem pauli_sandwich (n m : Fin 3 → ℝ) :
    pauliVec m * pauliVec n * pauliVec m
      = ((2 * dot3 m n : ℝ) : ℂ) • pauliVec m
        - ((dot3 m m : ℝ) : ℂ) • pauliVec n := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliVec, dot3, Matrix.mul_apply, Fin.sum_univ_two,
      Complex.ext_iff] <;>
    (try constructor) <;> ring

/-- `thm:grading-ambiguity-main` (odd-part singular value): for
`S = s·n̂·σ` and grading `J = m̂·σ` with unit axes, the `J`-odd part
`(S - JSJ)/2` squares to `s²(1-(n̂·m̂)²)·1`, so its singular value is
`m_J = s√(1-(n̂·m̂)²)`. -/
theorem grading_odd_part_sq (s : ℝ) (n m : Fin 3 → ℝ)
    (hn : dot3 n n = 1) (hm : dot3 m m = 1) :
    (((1 : ℂ) / 2) • ((s : ℂ) • pauliVec n
        - pauliVec m * ((s : ℂ) • pauliVec n) * pauliVec m))
      * (((1 : ℂ) / 2) • ((s : ℂ) • pauliVec n
        - pauliVec m * ((s : ℂ) • pauliVec n) * pauliVec m))
      = ((s ^ 2 * (1 - (dot3 n m) ^ 2) : ℝ) : ℂ)
        • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have hsw : pauliVec m * ((s : ℂ) • pauliVec n) * pauliVec m
      = ((2 * dot3 m n : ℝ) : ℂ) • ((s : ℂ) • pauliVec m)
        - ((s : ℂ) • pauliVec n) := by
    rw [Matrix.mul_smul, Matrix.smul_mul, pauli_sandwich n m, hm]
    push_cast
    rw [smul_sub]
    simp only [smul_smul, one_smul]
    congr 1
    ring_nf
  rw [hsw]
  -- odd part = s • pauliVec (n - (m·n)m)
  have hodd : ((1 : ℂ) / 2) • ((s : ℂ) • pauliVec n
      - (((2 * dot3 m n : ℝ) : ℂ) • ((s : ℂ) • pauliVec m)
        - ((s : ℂ) • pauliVec n)))
      = (s : ℂ) • (pauliVec n
        - ((dot3 m n : ℝ) : ℂ) • pauliVec m) := by
    push_cast
    module
  rw [hodd]
  -- pauliVec is linear in its vector argument
  have hlin : pauliVec n - ((dot3 m n : ℝ) : ℂ) • pauliVec m
      = pauliVec (fun i => n i - dot3 m n * m i) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pauliVec, Complex.ext_iff] <;>
      ring
  rw [hlin]
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, pauli_square]
  rw [smul_smul]
  congr 1
  have hw : dot3 (fun i => n i - dot3 m n * m i)
      (fun i => n i - dot3 m n * m i)
      = 1 - (dot3 n m) ^ 2 := by
    simp only [dot3] at hn hm ⊢
    linear_combination hn
      + ((m 0 * n 0 + m 1 * n 1 + m 2 * n 2) ^ 2) * hm
  rw [hw]
  push_cast
  ring

/-- `thm:grading-ambiguity-main` (range): as the grading axis
varies, the odd singular value attains every value in `[0, s]`:
for each `t ∈ [0, s]` there is a unit axis `m̂` with
`s²(1-(n̂·m̂)²) = t²` (with `n̂ = e₃`). -/
theorem grading_ambiguity_range (s t : ℝ) (hs : 0 < s)
    (ht0 : 0 ≤ t) (hts : t ≤ s) :
    ∃ m : Fin 3 → ℝ, dot3 m m = 1
      ∧ s ^ 2 * (1 - (dot3 ![0, 0, 1] m) ^ 2) = t ^ 2 := by
  have hc1 : (t / s) ^ 2 ≤ 1 := by
    rw [div_pow, div_le_one (by positivity)]
    nlinarith
  refine ⟨![t / s, 0, Real.sqrt (1 - (t / s) ^ 2)], ?_, ?_⟩
  · change t / s * (t / s) + 0 * 0
        + Real.sqrt (1 - (t / s) ^ 2)
          * Real.sqrt (1 - (t / s) ^ 2) = 1
    rw [Real.mul_self_sqrt (by linarith)]
    ring
  · change s ^ 2 * (1 - (0 * (t / s) + 0 * 0
        + 1 * Real.sqrt (1 - (t / s) ^ 2)) ^ 2) = t ^ 2
    have hs' : s ≠ 0 := ne_of_gt hs
    rw [show (0 * (t / s) + 0 * 0
        + 1 * Real.sqrt (1 - (t / s) ^ 2))
      = Real.sqrt (1 - (t / s) ^ 2) from by ring]
    rw [Real.sq_sqrt (by linarith)]
    rw [show (1 : ℝ) - (1 - (t / s) ^ 2) = (t / s) ^ 2 from by ring]
    rw [div_pow]
    field_simp

end NCG
