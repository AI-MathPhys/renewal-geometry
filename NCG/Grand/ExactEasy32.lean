import NCG.Grand.LoadingDeformations

/-! # Exact EASY batch 32: normalized Peano extension -/

open Matrix

namespace NCG

/-- The intrinsic chronology-word formula for truncated Peano multiplication. -/
theorem peano_chronology_word {X : ℕ} (hX : 0 < X)
    (a : ℕ) (ha : 1 ≤ a) :
    peanoL X a = ∑ b ∈ Finset.Icc 1 (X / a),
      recS X ^ (a * b - 1) * (1 - recS X * (recS X)ᴴ)
        * (recS X ^ (b - 1))ᴴ := by
  ext j i
  simp only [peanoL, Matrix.of_apply, Matrix.sum_apply]
  by_cases hji : (j : ℕ) + 1 = a * ((i : ℕ) + 1)
  · rw [if_pos hji]
    have habX : a * ((i : ℕ) + 1) ≤ X := by omega
    have hib : (i : ℕ) + 1 ≤ X / a :=
      (Nat.le_div_iff_mul_le (by omega)).2
        (by simpa [Nat.mul_comm] using habX)
    have hiMem : (i : ℕ) + 1 ∈ Finset.Icc 1 (X / a) :=
      Finset.mem_Icc.mpr ⟨by omega, hib⟩
    rw [Finset.sum_eq_single_of_mem ((i : ℕ) + 1) hiMem]
    · have hjX : a * ((i : ℕ) + 1) - 1 < X := by omega
      have hiX : (i : ℕ) + 1 - 1 < X := by omega
      rw [recS_unit (show 1 ≤ X by omega)
        (⟨a * ((i : ℕ) + 1) - 1, hjX⟩ : Fin X)
        (⟨(i : ℕ) + 1 - 1, hiX⟩ : Fin X)]
      simp only [Matrix.single_apply, Fin.ext_iff]
      rw [if_pos]
      exact ⟨by omega, by omega⟩
    · intro b hb hne
      have hbI := Finset.mem_Icc.mp hb
      have hab : a * b ≤ X := by
        have hba := (Nat.le_div_iff_mul_le (by omega)).1 hbI.2
        simpa [Nat.mul_comm] using hba
      have hablt : a * b - 1 < X := by omega
      have hblt : b - 1 < X := by
        have hbX : b ≤ X := le_trans
          (Nat.le_mul_of_pos_left b (by omega)) hab
        omega
      rw [recS_unit (show 1 ≤ X by omega)
        (⟨a * b - 1, hablt⟩ : Fin X) (⟨b - 1, hblt⟩ : Fin X)]
      simp only [Matrix.single_apply, Fin.ext_iff]
      rw [if_neg]
      intro hpair
      apply hne
      omega
  · rw [if_neg hji]
    symm
    apply Finset.sum_eq_zero
    intro b hb
    have hbI := Finset.mem_Icc.mp hb
    have hab : a * b ≤ X := by
      have hba := (Nat.le_div_iff_mul_le (by omega)).1 hbI.2
      simpa [Nat.mul_comm] using hba
    have hablt : a * b - 1 < X := by omega
    have hblt : b - 1 < X := by
      have hbX : b ≤ X := le_trans
        (Nat.le_mul_of_pos_left b (by omega)) hab
      omega
    rw [recS_unit (show 1 ≤ X by omega)
      (⟨a * b - 1, hablt⟩ : Fin X) (⟨b - 1, hblt⟩ : Fin X)]
    simp only [Matrix.single_apply, Fin.ext_iff]
    rw [if_neg]
    intro hpair
    apply hji
    have habpos : 0 < a * b := Nat.mul_pos (by omega) hbI.1
    have hj1 : (j : ℕ) + 1 = a * b := by omega
    have hi1 : (i : ℕ) + 1 = b := by omega
    rw [hj1, hi1]

/-- `thm:ar-Peano-multiplication`: uniqueness, the chronology-word formula,
identity, multiplicativity, and commutativity. -/
theorem peano_multiplication_exact {X : ℕ} (hX : 0 < X)
    (a : ℕ) (ha : 1 ≤ a) :
    (∀ M : Matrix (Fin X) (Fin X) ℂ,
      M *ᵥ Pi.single (⟨0, hX⟩ : Fin X) 1
          = recS X ^ (a - 1) *ᵥ Pi.single (⟨0, hX⟩ : Fin X) 1 →
      M * recS X = recS X ^ a * M → M = peanoL X a)
    ∧ peanoL X a = ∑ b ∈ Finset.Icc 1 (X / a),
      recS X ^ (a * b - 1) * (1 - recS X * (recS X)ᴴ)
        * (recS X ^ (b - 1))ᴴ
    ∧ peanoL X 1 = 1
    ∧ (∀ b : ℕ, 1 ≤ b → peanoL X a * peanoL X b = peanoL X (a * b))
    ∧ (∀ b : ℕ, 1 ≤ b → peanoL X a * peanoL X b
        = peanoL X b * peanoL X a) := by
  refine ⟨?_, peano_chronology_word hX a ha, ?_, ?_, ?_⟩
  · intro M hη hS
    simpa using loading_deformation hX a ha M 1 hS (by simpa using hη)
  · ext j i
    simp [peanoL, Matrix.one_apply, Fin.ext_iff]
  · intro b hb
    exact peano_product a b ha hb
  · intro b hb
    rw [peano_product a b ha hb, peano_product b a hb ha, Nat.mul_comm]

end NCG
