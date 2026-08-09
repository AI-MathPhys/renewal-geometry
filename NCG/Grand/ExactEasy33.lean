import NCG.Grand.ExactEasy32
import NCG.Grand.PeanoStability

/-! # Exact EASY batch 33: Peano naturality between realizations -/

open Matrix

namespace NCG

/-- `thm:ar-Peano-naturality`, two-realization clause.  Any unitary carrying
the anchored chronology to a second anchored chronology automatically carries
the uniquely normalized count and every normalized Peano history. -/
theorem peano_naturality_two_realizations {X : ℕ} (hX : 0 < X)
    (U : Matrix (Fin X) (Fin X) ℂ)
    (η' : Fin X → ℂ) (S' N' : Matrix (Fin X) (Fin X) ℂ)
    (L' : ℕ → Matrix (Fin X) (Fin X) ℂ)
    (hUl : Uᴴ * U = 1) (hUr : U * Uᴴ = 1)
    (hη : Matrix.mulVec U (Pi.single (⟨0, hX⟩ : Fin X) 1) = η')
    (hS : U * recS X = S' * U)
    (hNη : Matrix.mulVec N' η' = η')
    (hNS : N' * S' - S' * N' = S')
    (hLη : ∀ a : ℕ, 1 ≤ a →
      Matrix.mulVec (L' a) η' = Matrix.mulVec (S' ^ (a - 1)) η')
    (hLS : ∀ a : ℕ, 1 ≤ a → L' a * S' = S' ^ a * L' a) :
    U * Matrix.diagonal (fun i : Fin X => ((i : ℕ) + 1 : ℂ)) = N' * U
      ∧ ∀ a : ℕ, 1 ≤ a → U * peanoL X a = L' a * U := by
  let η : Fin X → ℂ := Pi.single (⟨0, hX⟩ : Fin X) 1
  have hηback : Matrix.mulVec Uᴴ η' = η := by
    rw [← hη, Matrix.mulVec_mulVec, hUl, Matrix.one_mulVec]
  have hpow : ∀ k : ℕ, U * recS X ^ k = S' ^ k * U := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, pow_succ, ← Matrix.mul_assoc, ih,
        Matrix.mul_assoc, hS, ← Matrix.mul_assoc]
  have hcountConj : Uᴴ * N' * U
      = Matrix.diagonal (fun i : Fin X => ((i : ℕ) + 1 : ℂ)) := by
    apply count_rigidity hX
    · calc
        Matrix.mulVec (Uᴴ * N' * U) η
            = Matrix.mulVec Uᴴ (Matrix.mulVec N' (Matrix.mulVec U η)) := by
                simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
        _ = Matrix.mulVec Uᴴ (Matrix.mulVec N' η') := by rw [hη]
        _ = Matrix.mulVec Uᴴ η' := by rw [hNη]
        _ = η := hηback
    · calc
        (Uᴴ * N' * U) * recS X - recS X * (Uᴴ * N' * U)
            = Uᴴ * (N' * S' - S' * N') * U := by
                rw [Matrix.mul_sub, Matrix.sub_mul]
                apply congrArg₂ (· - ·)
                · calc
                    Uᴴ * N' * U * recS X
                        = Uᴴ * N' * (U * recS X) := by
                            simp only [Matrix.mul_assoc]
                    _ = Uᴴ * N' * (S' * U) := by rw [hS]
                    _ = Uᴴ * (N' * S') * U := by
                            simp only [Matrix.mul_assoc]
                · have hSback : Uᴴ * S' * U = recS X := by
                    calc
                      Uᴴ * S' * U = Uᴴ * (S' * U) := by
                        simp only [Matrix.mul_assoc]
                      _ = Uᴴ * (U * recS X) := by rw [← hS]
                      _ = recS X := by rw [← Matrix.mul_assoc, hUl,
                        Matrix.one_mul]
                  calc
                    recS X * (Uᴴ * N' * U)
                        = (Uᴴ * S' * U) * (Uᴴ * N' * U) := by rw [hSback]
                    _ = Uᴴ * (S' * N') * U := by
                      simp only [Matrix.mul_assoc]
                      rw [← Matrix.mul_assoc U Uᴴ (N' * U), hUr,
                        Matrix.one_mul]
        _ = Uᴴ * S' * U := by rw [hNS]
        _ = recS X := by
          calc
            Uᴴ * S' * U = Uᴴ * (S' * U) := by
              simp only [Matrix.mul_assoc]
            _ = Uᴴ * (U * recS X) := by rw [← hS]
            _ = recS X := by rw [← Matrix.mul_assoc, hUl, Matrix.one_mul]
  constructor
  · calc
      U * Matrix.diagonal (fun i : Fin X => ((i : ℕ) + 1 : ℂ))
          = U * (Uᴴ * N' * U) := by rw [hcountConj]
      _ = (U * Uᴴ) * N' * U := by simp only [Matrix.mul_assoc]
      _ = N' * U := by rw [hUr, Matrix.one_mul]
  · intro a ha
    have hLconj : Uᴴ * L' a * U = peanoL X a := by
      have hcov : (Uᴴ * L' a * U) * recS X
          = recS X ^ a * (Uᴴ * L' a * U) := by
        calc
          (Uᴴ * L' a * U) * recS X
              = Uᴴ * L' a * (U * recS X) := by
                  simp only [Matrix.mul_assoc]
          _ = Uᴴ * L' a * (S' * U) := by rw [hS]
          _ = Uᴴ * (L' a * S') * U := by simp only [Matrix.mul_assoc]
          _ = Uᴴ * (S' ^ a * L' a) * U := by rw [hLS a ha]
          _ = (Uᴴ * S' ^ a * U) * (Uᴴ * L' a * U) := by
              simp only [Matrix.mul_assoc]
              rw [← Matrix.mul_assoc U Uᴴ (L' a * U), hUr,
                Matrix.one_mul]
          _ = recS X ^ a * (Uᴴ * L' a * U) := by
              have hp := hpow a
              have hback : Uᴴ * S' ^ a * U = recS X ^ a := by
                calc
                  Uᴴ * S' ^ a * U = Uᴴ * (S' ^ a * U) := by
                    simp only [Matrix.mul_assoc]
                  _ = Uᴴ * (U * recS X ^ a) := by rw [← hp]
                  _ = recS X ^ a := by
                    rw [← Matrix.mul_assoc, hUl, Matrix.one_mul]
              rw [hback]
      have hanchor : Matrix.mulVec (Uᴴ * L' a * U) η
          = (1 : ℂ) • Matrix.mulVec (recS X ^ (a - 1)) η := by
        calc
          Matrix.mulVec (Uᴴ * L' a * U) η
              = Matrix.mulVec Uᴴ
                  (Matrix.mulVec (L' a) (Matrix.mulVec U η)) := by
                    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
          _ = Matrix.mulVec Uᴴ (Matrix.mulVec (L' a) η') := by rw [hη]
          _ = Matrix.mulVec Uᴴ (Matrix.mulVec (S' ^ (a - 1)) η') := by
                rw [hLη a ha]
          _ = Matrix.mulVec Uᴴ
                (Matrix.mulVec (S' ^ (a - 1)) (Matrix.mulVec U η)) := by rw [hη]
          _ = Matrix.mulVec (recS X ^ (a - 1)) η := by
              rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
              have hp := hpow (a - 1)
              have hback : Uᴴ * S' ^ (a - 1) * U = recS X ^ (a - 1) := by
                calc
                  Uᴴ * S' ^ (a - 1) * U
                      = Uᴴ * (S' ^ (a - 1) * U) := by
                          simp only [Matrix.mul_assoc]
                  _ = Uᴴ * (U * recS X ^ (a - 1)) := by rw [← hp]
                  _ = recS X ^ (a - 1) := by
                    rw [← Matrix.mul_assoc, hUl, Matrix.one_mul]
              rw [hback]
          _ = (1 : ℂ) • Matrix.mulVec (recS X ^ (a - 1)) η := by simp
      simpa [η] using
        loading_deformation hX a ha (Uᴴ * L' a * U) (1 : ℂ) hcov hanchor
    calc
      U * peanoL X a = U * (Uᴴ * L' a * U) := by rw [hLconj]
      _ = (U * Uᴴ) * L' a * U := by simp only [Matrix.mul_assoc]
      _ = L' a * U := by rw [hUr, Matrix.one_mul]

end NCG
