/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Matter.QutritWeyl

/-!
# Revision lines and the tetrahedral MUB frames
  (`thm:revision-MUB`, SM_emergence)

The four projective lines of `𝔽₃²` with generators
`X, Z, XZ, XZ²` each carry a spectral triple of projectors
`P_{L,k} = (1/3)Σ_t ω^{-kt} R_L^t`:

* `mubProj_idem` / `mubProj_herm` / `mubProj_trace` — the twelve
  projectors are rank-one (Hermitian idempotents of unit trace);
* `mubProj_orth` / `mubProj_sum` — each line is a complete
  orthogonal resolution of the identity;
* `mubProj_cross_trace` — for distinct lines
  `Tr(P_{L,k}P_{M,ℓ}) = 1/3`: the four lines are a complete set of
  mutually unbiased qutrit bases;
* `lineGen_commutant` — the commutant of each line generator is
  exactly `span{1, R_L, R_L²}`: each `𝓜_L` is maximal abelian.
-/

namespace NCG

open Matrix

noncomputable section

/-- Generators of the four projective revision lines of `𝔽₃²`. -/
def lineVec : Fin 4 → ℕ × ℕ := ![(1, 0), (0, 1), (1, 1), (1, 2)]

/-- The unitary generator of line `L`. -/
def lineGen (L : Fin 4) : Matrix (Fin 3) (Fin 3) ℂ :=
  qW (lineVec L).1 (lineVec L).2

lemma lineGen_cube (L : Fin 4) : lineGen L ^ 3 = 1 := qW_cube _ _

lemma qW_pow_two (a b : ℕ) :
    (qW a b) ^ 2 = qOmega ^ (a * b) • qW (2 * a) (2 * b) := by
  rw [pow_two, qW_mul, mul_comm b a, two_mul, two_mul]

lemma qW_pow_fin (a b : ℕ) (t : Fin 3) :
    (qW a b) ^ (t : ℕ)
      = qOmega ^ ((t : ℕ) * ((t : ℕ) - 1) / 2 * (a * b))
          • qW ((t : ℕ) * a) ((t : ℕ) * b) := by
  fin_cases t
  · simp
  · simp
  · norm_num
    rw [qW_pow_two]

lemma lineGen_conjTranspose (L : Fin 4) :
    (lineGen L)ᴴ = lineGen L ^ 2 := by
  rw [lineGen, qW_conjTranspose, qW_pow_two,
    mul_comm ((lineVec L).1) ((lineVec L).2)]

lemma lineGen_trace (L : Fin 4) : (lineGen L).trace = 0 :=
  qW_trace_zero (by revert L; decide)

lemma lineGen_sq_trace (L : Fin 4) : (lineGen L ^ 2).trace = 0 := by
  rw [lineGen, qW_pow_two, Matrix.trace_smul,
    qW_trace_zero (by revert L; decide), smul_zero]

/-- The spectral projector `P_{L,k} = (1/3)Σ_t ω^{-kt}R_L^t`. -/
def mubProj (L : Fin 4) (k : ℕ) : Matrix (Fin 3) (Fin 3) ℂ :=
  (3 : ℂ)⁻¹ • (1 + qOmega ^ (2 * k) • lineGen L
    + qOmega ^ k • lineGen L ^ 2)

/-- Product expansion in the cyclic algebra of a cube root. -/
lemma cube_expand {g : Matrix (Fin 3) (Fin 3) ℂ} (hg3 : g ^ 3 = 1)
    (α β γ δ : ℂ) :
    (1 + α • g + β • g ^ 2) * (1 + γ • g + δ • g ^ 2)
      = (1 + α * δ + β * γ) • (1 : Matrix (Fin 3) (Fin 3) ℂ)
        + (α + γ + β * δ) • g + (β + δ + α * γ) • g ^ 2 := by
  have hg4 : g ^ 4 = g := by
    rw [pow_succ, hg3, one_mul]
  have e1 : g * g = g ^ 2 := (pow_two g).symm
  have e2 : g * g ^ 2 = 1 := by
    rw [show g * g ^ 2 = g ^ 3 from (pow_succ' g 2).symm, hg3]
  have e3 : g ^ 2 * g = 1 := by
    rw [show g ^ 2 * g = g ^ 3 from (pow_succ g 2).symm, hg3]
  have e4 : g ^ 2 * g ^ 2 = g := by
    rw [show g ^ 2 * g ^ 2 = g ^ 4 from (pow_add g 2 2).symm, hg4]
  simp only [add_mul, mul_add, one_mul, mul_one,
    smul_mul_smul_comm, e1, e2, e3, e4]
  module

lemma coefA (k : ℕ) : qOmega ^ (2 * k) * qOmega ^ k = 1 := by
  rw [← pow_add, show 2 * k + k = 3 * k by ring, qOmega_pow_mod,
    Nat.mul_mod_right, pow_zero]

lemma coefB (k : ℕ) :
    qOmega ^ (2 * k) * qOmega ^ (2 * k) = qOmega ^ k := by
  rw [← pow_add, qOmega_pow_mod,
    show (2 * k + 2 * k) % 3 = k % 3 by omega, ← qOmega_pow_mod]

lemma coefC (k : ℕ) : qOmega ^ k * qOmega ^ k = qOmega ^ (2 * k) := by
  rw [← pow_add, show k + k = 2 * k by ring]

/-- `thm:revision-MUB` (idempotence). -/
theorem mubProj_idem (L : Fin 4) (k : ℕ) :
    mubProj L k * mubProj L k = mubProj L k := by
  rw [mubProj, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    cube_expand (lineGen_cube L)]
  match_scalars
  · linear_combination (2 / 9 : ℂ) * coefA k
  · linear_combination (1 / 9 : ℂ) * coefC k
  · linear_combination (1 / 9 : ℂ) * coefB k

/-- `thm:revision-MUB` (unit trace: the projectors are rank one). -/
theorem mubProj_trace (L : Fin 4) (k : ℕ) :
    (mubProj L k).trace = 1 := by
  rw [mubProj, Matrix.trace_smul, Matrix.trace_add,
    Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
    Matrix.trace_one, lineGen_trace, lineGen_sq_trace,
    smul_zero, smul_zero, add_zero, add_zero]
  norm_num

/-- `thm:revision-MUB` (hermiticity). -/
theorem mubProj_herm (L : Fin 4) (k : ℕ) :
    (mubProj L k)ᴴ = mubProj L k := by
  have hg4 : lineGen L ^ 4 = lineGen L := by
    rw [pow_succ, lineGen_cube, one_mul]
  have hcb : star (qOmega ^ k) = qOmega ^ (2 * k) := by
    rw [show star (qOmega ^ k) = (starRingEnd ℂ) (qOmega ^ k)
        from rfl,
      map_pow, qOmega_conj, ← pow_mul, mul_comm]
  have hca : star (qOmega ^ (2 * k)) = qOmega ^ k := by
    rw [show star (qOmega ^ (2 * k))
        = (starRingEnd ℂ) (qOmega ^ (2 * k)) from rfl,
      map_pow, qOmega_conj, ← pow_mul, qOmega_pow_mod,
      show 2 * (2 * k) % 3 = k % 3 by omega, ← qOmega_pow_mod]
  have hc3 : star ((3 : ℂ)⁻¹) = (3 : ℂ)⁻¹ := by
    rw [show star ((3 : ℂ)⁻¹) = (starRingEnd ℂ) ((3 : ℂ)⁻¹)
        from rfl,
      map_inv₀, map_ofNat]
  rw [mubProj, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_add, Matrix.conjTranspose_add,
    Matrix.conjTranspose_one, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_pow,
    lineGen_conjTranspose, ← pow_mul, hg4, hca, hcb, hc3]
  module

/-- `thm:revision-MUB` (same-line orthogonality). -/
theorem mubProj_orth (L : Fin 4) {k l : Fin 3} (hkl : k ≠ l) :
    mubProj L (k : ℕ) * mubProj L (l : ℕ) = 0 := by
  rw [mubProj, mubProj, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, cube_expand (lineGen_cube L)]
  fin_cases k <;> fin_cases l <;>
    first
      | exact absurd rfl hkl
      | (match_scalars <;>
         first
           | linear_combination (1 / 9 : ℂ) * qOmega_sq_add
           | linear_combination (qOmega ^ 2 / 9) * qOmega_sq_add
           | linear_combination (1 / 9 : ℂ) * qOmega_sq_add
               + (qOmega / 9) * qOmega_pow_three
           | linear_combination (1 / 9 : ℂ) * qOmega_sq_add
               + ((qOmega + qOmega ^ 2) / 9) * qOmega_pow_three
           | linear_combination (1 / 9 : ℂ) * qOmega_sq_add
               + ((qOmega ^ 3 + 1) / 9) * qOmega_pow_three)

/-- `thm:revision-MUB` (resolution of the identity). -/
theorem mubProj_sum (L : Fin 4) :
    ∑ k : Fin 3, mubProj L (k : ℕ) = 1 := by
  rw [Fin.sum_univ_three]
  simp only [mubProj, Fin.val_zero, Fin.val_one, Fin.val_two]
  match_scalars
  · norm_num
  · norm_num
    linear_combination (1 / 3 : ℂ) * qOmega_sq_add
      + (qOmega / 3) * qOmega_pow_three
  · norm_num
    linear_combination (1 / 3 : ℂ) * qOmega_sq_add

lemma line_word_ne {L M : Fin 4} (hLM : L ≠ M) (t s : Fin 3)
    (hts : ¬((t : ℕ) = 0 ∧ (s : ℕ) = 0)) :
    ¬ (((t : ℕ) * (lineVec L).1 + (s : ℕ) * (lineVec M).1) % 3 = 0
      ∧ ((t : ℕ) * (lineVec L).2
          + (s : ℕ) * (lineVec M).2) % 3 = 0) := by
  revert hts hLM
  revert t s
  revert L M
  decide

lemma line_cross_word_trace {L M : Fin 4} (hLM : L ≠ M)
    (t s : Fin 3) (hts : ¬((t : ℕ) = 0 ∧ (s : ℕ) = 0)) :
    ((lineGen L) ^ (t : ℕ) * (lineGen M) ^ (s : ℕ)).trace = 0 := by
  rw [lineGen, lineGen, qW_pow_fin, qW_pow_fin, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, qW_mul, smul_smul,
    Matrix.trace_smul, qW_trace_zero (line_word_ne hLM t s hts),
    smul_zero]

/-- `thm:revision-MUB` (mutual unbiasedness): for distinct lines
the projector overlap is exactly `1/3`. -/
theorem mubProj_cross_trace {L M : Fin 4} (hLM : L ≠ M)
    (k l : Fin 3) :
    (mubProj L (k : ℕ) * mubProj M (l : ℕ)).trace = 1 / 3 := by
  have h01 : (lineGen M).trace = 0 := by
    simpa using line_cross_word_trace hLM 0 1 (by norm_num)
  have h02 : (lineGen M ^ 2).trace = 0 := by
    simpa using line_cross_word_trace hLM 0 2 (by norm_num)
  have h10 : (lineGen L).trace = 0 := by
    simpa using line_cross_word_trace hLM 1 0 (by norm_num)
  have h20 : (lineGen L ^ 2).trace = 0 := by
    simpa using line_cross_word_trace hLM 2 0 (by norm_num)
  have h11 : (lineGen L * lineGen M).trace = 0 := by
    simpa using line_cross_word_trace hLM 1 1 (by norm_num)
  have h12 : (lineGen L * lineGen M ^ 2).trace = 0 := by
    simpa using line_cross_word_trace hLM 1 2 (by norm_num)
  have h21 : (lineGen L ^ 2 * lineGen M).trace = 0 := by
    simpa using line_cross_word_trace hLM 2 1 (by norm_num)
  have h22 : (lineGen L ^ 2 * lineGen M ^ 2).trace = 0 := by
    simpa using line_cross_word_trace hLM 2 2 (by norm_num)
  rw [mubProj, mubProj, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul]
  simp only [add_mul, mul_add, one_mul, mul_one, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, Matrix.trace_smul,
    Matrix.trace_add]
  rw [h01, h02, h10, h20, h11, h12, h21, h22, Matrix.trace_one]
  simp only [smul_eq_mul]
  norm_num

/-- Conjugation by a Weyl word acts on Weyl words through the
symplectic character. -/
lemma qW_conj_word (v₁ v₂ p₁ p₂ : ℕ) :
    qW v₁ v₂ * qW p₁ p₂ * (qW v₁ v₂) ^ 2
      = qOmega ^ ((v₂ * p₁ + 2 * v₁ * p₂) % 3)
          • qW (p₁ % 3) (p₂ % 3) := by
  rw [qW_pow_two, qW_mul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, qW_mul, smul_smul, ← pow_add, ← pow_add,
    qW_mod (v₁ + p₁ + 2 * v₁),
    show (v₁ + p₁ + 2 * v₁) % 3 = p₁ % 3 by omega,
    show (v₂ + p₂ + 2 * v₂) % 3 = p₂ % 3 by omega,
    show v₂ * p₁ + v₁ * v₂ + (v₂ + p₂) * (2 * v₁)
      = (v₂ * p₁ + 2 * v₁ * p₂) + 3 * (v₁ * v₂) by ring,
    qOmega_pow_mod, Nat.add_mul_mod_self_left]

lemma qW22_mem_span : qW 2 2 ∈ Submodule.span ℂ
    ({1, qW 1 1, qW 1 1 ^ 2}
      : Set (Matrix (Fin 3) (Fin 3) ℂ)) := by
  have h : qW 1 1 ^ 2 = qOmega • qW 2 2 := by
    rw [qW_pow_two]
    norm_num
  have h2 : qW 2 2 = qOmega ^ 2 • qW 1 1 ^ 2 := by
    rw [h, smul_smul, show qOmega ^ 2 * qOmega = 1 from by
      linear_combination qOmega_pow_three, one_smul]
  rw [h2]
  exact Submodule.smul_mem _ _ (Submodule.subset_span
    (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)))

lemma qW21_mem_span : qW 2 1 ∈ Submodule.span ℂ
    ({1, qW 1 2, qW 1 2 ^ 2}
      : Set (Matrix (Fin 3) (Fin 3) ℂ)) := by
  have h : qW 1 2 ^ 2 = qOmega ^ 2 • qW 2 4 := by
    rw [qW_pow_two]
  have h4 : qW 2 4 = qW 2 1 := by
    rw [qW_mod]
  have h2 : qW 2 1 = qOmega • qW 1 2 ^ 2 := by
    rw [h, h4, smul_smul, qOmega_mul_sq, one_smul]
  rw [h2]
  exact Submodule.smul_mem _ _ (Submodule.subset_span
    (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)))

lemma qWfam_mem_line_span (L : Fin 4) (p : Fin 3 × Fin 3)
    (hp : ((lineVec L).2 * (p.1 : ℕ)
      + 2 * (lineVec L).1 * (p.2 : ℕ)) % 3 = 0) :
    qWfam p ∈ Submodule.span ℂ
      ({1, lineGen L, lineGen L ^ 2}
        : Set (Matrix (Fin 3) (Fin 3) ℂ)) := by
  fin_cases L <;> fin_cases p <;>
    simp only [lineVec, lineGen, qWfam] at hp ⊢ <;>
    first
      | exact absurd hp (by decide)
      | exact qW22_mem_span
      | exact qW21_mem_span
      | (norm_num [qW_pow_two]
         first
           | exact Submodule.subset_span (Set.mem_insert _ _)
           | exact Submodule.subset_span
               (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
           | exact Submodule.subset_span
               (Set.mem_insert_of_mem _
                 (Set.mem_insert_of_mem _ (Set.mem_singleton _))))

/-- `thm:revision-MUB` (maximal abelianness): the commutant of a
line generator is exactly `span{1, R_L, R_L²}`. -/
theorem lineGen_commutant (L : Fin 4)
    (M : Matrix (Fin 3) (Fin 3) ℂ) :
    M * lineGen L = lineGen L * M
      ↔ M ∈ Submodule.span ℂ
          ({1, lineGen L, lineGen L ^ 2}
            : Set (Matrix (Fin 3) (Fin 3) ℂ)) := by
  constructor
  · intro hM
    have hg3 := lineGen_cube L
    have hconj : lineGen L * M * lineGen L ^ 2 = M := by
      rw [show lineGen L * M = M * lineGen L from hM.symm,
        mul_assoc,
        show lineGen L * lineGen L ^ 2 = lineGen L ^ 3 from
          (pow_succ' _ 2).symm, hg3, mul_one]
    have hspan : M ∈ Submodule.span ℂ (Set.range qWfam) := by
      rw [qW_span_top]
      exact Submodule.mem_top
    rw [Submodule.mem_span_range_iff_exists_fun] at hspan
    obtain ⟨c, hc⟩ := hspan
    have hWconj : ∀ p : Fin 3 × Fin 3,
        lineGen L * qWfam p * lineGen L ^ 2
          = qOmega ^ (((lineVec L).2 * (p.1 : ℕ)
              + 2 * (lineVec L).1 * (p.2 : ℕ)) % 3)
            • qWfam p := by
      intro p
      rw [lineGen, qWfam, qW_conj_word,
        Nat.mod_eq_of_lt p.1.isLt, Nat.mod_eq_of_lt p.2.isLt]
    have hstep : lineGen L
          * (∑ p : Fin 3 × Fin 3, c p • qWfam p)
          * lineGen L ^ 2
        = ∑ p : Fin 3 × Fin 3,
            (qOmega ^ (((lineVec L).2 * (p.1 : ℕ)
                + 2 * (lineVec L).1 * (p.2 : ℕ)) % 3) * c p)
              • qWfam p := by
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p _
      rw [Matrix.mul_smul, Matrix.smul_mul, hWconj p, smul_smul,
        mul_comm (c p)]
    have hM2 : ∑ p : Fin 3 × Fin 3,
        (qOmega ^ (((lineVec L).2 * (p.1 : ℕ)
            + 2 * (lineVec L).1 * (p.2 : ℕ)) % 3) * c p)
          • qWfam p
        = ∑ p : Fin 3 × Fin 3, c p • qWfam p :=
      calc ∑ p : Fin 3 × Fin 3, _ • qWfam p
          = lineGen L * (∑ p : Fin 3 × Fin 3, c p • qWfam p)
              * lineGen L ^ 2 := hstep.symm
        _ = lineGen L * M * lineGen L ^ 2 := by rw [hc]
        _ = M := hconj
        _ = ∑ p : Fin 3 × Fin 3, c p • qWfam p := hc.symm
    have hdiff : ∑ p : Fin 3 × Fin 3,
        ((qOmega ^ (((lineVec L).2 * (p.1 : ℕ)
            + 2 * (lineVec L).1 * (p.2 : ℕ)) % 3) - 1) * c p)
          • qWfam p = 0 := by
      have h0 := sub_eq_zero.mpr hM2
      rw [← Finset.sum_sub_distrib] at h0
      calc ∑ p : Fin 3 × Fin 3, _ • qWfam p
          = ∑ p : Fin 3 × Fin 3,
              ((qOmega ^ (((lineVec L).2 * (p.1 : ℕ)
                  + 2 * (lineVec L).1 * (p.2 : ℕ)) % 3) * c p)
                • qWfam p - c p • qWfam p) := by
            apply Finset.sum_congr rfl
            intro p _
            rw [sub_mul, sub_smul, one_mul]
        _ = 0 := h0
    have hcoeff := Fintype.linearIndependent_iff.mp
      qW_linearIndependent _ hdiff
    have hzero : ∀ p : Fin 3 × Fin 3,
        ((lineVec L).2 * (p.1 : ℕ)
          + 2 * (lineVec L).1 * (p.2 : ℕ)) % 3 ≠ 0 →
        c p = 0 := by
      intro p hp
      rcases mul_eq_zero.mp (hcoeff p) with h1 | h1
      · exfalso
        have hone : qOmega ^ (((lineVec L).2 * (p.1 : ℕ)
            + 2 * (lineVec L).1 * (p.2 : ℕ)) % 3) = 1 := by
          linear_combination h1
        have hne := qOmega_pow_ne
          (Nat.mod_lt _ (by norm_num) :
            ((lineVec L).2 * (p.1 : ℕ)
              + 2 * (lineVec L).1 * (p.2 : ℕ)) % 3 < 3)
          (by norm_num : (0 : ℕ) < 3) hp
        rw [pow_zero] at hne
        exact hne hone
      · exact h1
    rw [← hc]
    apply Submodule.sum_mem
    intro p _
    by_cases hp : ((lineVec L).2 * (p.1 : ℕ)
        + 2 * (lineVec L).1 * (p.2 : ℕ)) % 3 = 0
    · exact Submodule.smul_mem _ _ (qWfam_mem_line_span L p hp)
    · rw [hzero p hp, zero_smul]
      exact Submodule.zero_mem _
  · intro hM
    induction hM using Submodule.span_induction with
    | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · rw [one_mul, mul_one]
      · rfl
      · rw [show lineGen L ^ 2 * lineGen L = lineGen L ^ 3 from
          (pow_succ _ 2).symm,
          show lineGen L ^ 3 = lineGen L * lineGen L ^ 2 from
            pow_succ' _ 2]
    | zero => rw [zero_mul, mul_zero]
    | add x y _ _ hx hy => rw [add_mul, mul_add, hx, hy]
    | smul t x _ hx => rw [Matrix.smul_mul, Matrix.mul_smul, hx]

end

end NCG
