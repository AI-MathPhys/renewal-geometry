/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GTCharacterShort
import NCG.Grand.BrandNewEasy01
import NCG.Grand.BrandNewEasy03

/-!
# Character-invariant Moore--Penrose shorting

This completes the singular and nuisance-shorted clauses of
`thm:GT-character-short`.  Moore--Penrose uniqueness shows that the spectral
pseudoinverse of a Hermitian action commutes with every commuting unitary.
The same finite character projectors therefore reduce the pseudoinverse, an
invariant nuisance projection, and the corresponding compressed action.
-/

open Matrix Finset

namespace NCG
namespace CharacterInvariantShort



variable {n : Type} [Fintype n] [DecidableEq n]

/-- Any Moore--Penrose inverse commutes with a commuting unitary symmetry. -/
theorem moorePenrose_commutes_unitary
    (L G U : Matrix n n ℂ) (hL : Lᴴ = L)
    (hG1 : L * G * L = L) (hG2 : G * L * G = G)
    (hG3 : (L * G)ᴴ = L * G) (hG4 : (G * L)ᴴ = G * L)
    (hLU : L * U = U * L)
    (hUleft : Uᴴ * U = 1) (hUright : U * Uᴴ = 1) :
    G * U = U * G := by
  let W : Matrix n n ℂ := U * G * Uᴴ
  have hconjMul (X Y : Matrix n n ℂ) :
      (U * X * Uᴴ) * (U * Y * Uᴴ) = U * (X * Y) * Uᴴ := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᴴ U (Y * Uᴴ), hUleft, Matrix.one_mul]
  have hconjHerm {X : Matrix n n ℂ} (hX : Xᴴ = X) :
      (U * X * Uᴴ)ᴴ = U * X * Uᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hX]
    simp only [Matrix.mul_assoc]
  have hconjL : U * L * Uᴴ = L := by
    calc
      U * L * Uᴴ = L * U * Uᴴ := by rw [hLU]
      _ = L := by rw [Matrix.mul_assoc, hUright, Matrix.mul_one]
  have hW1 : L * W * L = L := by
    calc
      L * W * L =
          (U * L * Uᴴ) * (U * G * Uᴴ) * (U * L * Uᴴ) := by
            rw [hconjL]
      _ = U * (L * G) * Uᴴ * (U * L * Uᴴ) := by rw [hconjMul]
      _ = U * (L * G * L) * Uᴴ := by rw [hconjMul]
      _ = U * L * Uᴴ := by rw [hG1]
      _ = L := hconjL
  have hW2 : W * L * W = W := by
    calc
      W * L * W =
          (U * G * Uᴴ) * (U * L * Uᴴ) * (U * G * Uᴴ) := by
            rw [hconjL]
      _ = U * (G * L) * Uᴴ * (U * G * Uᴴ) := by rw [hconjMul]
      _ = U * (G * L * G) * Uᴴ := by rw [hconjMul]
      _ = U * G * Uᴴ := by rw [hG2]
      _ = W := rfl
  have hLW : L * W = U * (L * G) * Uᴴ := by
    conv_lhs => rw [← hconjL]
    change (U * L * Uᴴ) * (U * G * Uᴴ) = U * (L * G) * Uᴴ
    exact hconjMul L G
  have hWL : W * L = U * (G * L) * Uᴴ := by
    conv_lhs => rw [← hconjL]
    change (U * G * Uᴴ) * (U * L * Uᴴ) = U * (G * L) * Uᴴ
    exact hconjMul G L
  have hW3 : (L * W)ᴴ = L * W := by
    rw [hLW]
    exact hconjHerm hG3
  have hW4 : (W * L)ᴴ = W * L := by
    rw [hWL]
    exact hconjHerm hG4
  have hGW : G = W :=
    SMOSSeparateWardShorts.moorePenrose_unique L G W
      hG1 hG2 hG3 hG4 hW1 hW2 hW3 hW4
  calc
    G * U = W * U := by rw [hGW]
    _ = U * G := by
      dsimp [W]
      simp only [Matrix.mul_assoc]
      rw [hUleft, Matrix.mul_one]
/-- `thm:GT-character-short`, including the genuine singular pseudoinverse,
an invariant nuisance projection, the nuisance-compressed action, character
block diagonality, and the exact cross-character zero router. -/
theorem character_pseudoinverse_and_nuisance_short_exact
    {G₀ : Type} [Fintype G₀] [CommGroup G₀]
    (U : G₀ → Matrix n n ℂ)
    (hU : ∀ g h, U (g * h) = U g * U h)
    (hUH : ∀ g, (U g)ᴴ = U g⁻¹)
    (hUleft : ∀ g, (U g)ᴴ * U g = 1)
    (hUright : ∀ g, U g * (U g)ᴴ = 1)
    (χ ψ : G₀ → ℂ)
    (hχ : ∀ g h, χ (g * h) = χ g * χ h)
    (hψ : ∀ g h, ψ (g * h) = ψ g * ψ h)
    (hχu : ∀ g, star (χ g) * χ g = 1)
    (hψu : ∀ g, star (ψ g) * ψ g = 1)
    (hne : ∃ g₀, χ g₀ ≠ ψ g₀)
    (L : Matrix n n ℂ) (hL : Lᴴ = L)
    (hLU : ∀ g, L * U g = U g * L)
    (PN : Matrix n n ℂ) (hPNH : PNᴴ = PN) (hPN2 : PN * PN = PN)
    (hPNU : ∀ g, PN * U g = U g * PN) :
    let Pχ := (Fintype.card G₀ : ℂ)⁻¹ • ∑ g, star (χ g) • U g
    let Pψ := (Fintype.card G₀ : ℂ)⁻¹ • ∑ g, star (ψ g) • U g
    let Ldag := HermitianMoorePenroseInverse.hermitianMoorePenroseInverse L (show L.IsHermitian from hL)
    let QN := (1 : Matrix n n ℂ) - PN
    let Lshort := QN * L * QN
    Ldag * Pχ = Pχ * Ldag
      ∧ PN * Pχ = Pχ * PN
      ∧ Lshort * Pχ = Pχ * Lshort
      ∧ Pχ * Ldag * Pψ = 0
      ∧ Pχ * Lshort * Pψ = 0
      ∧ (∀ {k m : Type*} [Fintype k] [Fintype m]
          (A : Matrix n k ℂ) (Z : Matrix n m ℂ),
          Pχ * A = A → Pψ * Z = Z → Aᴴ * (Ldag * Z) = 0) := by
  dsimp only
  let Pχ : Matrix n n ℂ :=
    (Fintype.card G₀ : ℂ)⁻¹ • ∑ g, star (χ g) • U g
  let Pψ : Matrix n n ℂ :=
    (Fintype.card G₀ : ℂ)⁻¹ • ∑ g, star (ψ g) • U g
  let Ldag : Matrix n n ℂ := HermitianMoorePenroseInverse.hermitianMoorePenroseInverse L (show L.IsHermitian from hL)
  let QN : Matrix n n ℂ := 1 - PN
  let Lshort : Matrix n n ℂ := QN * L * QN
  have hdagH : Ldagᴴ = Ldag :=
    HermitianMoorePenroseInverse.hermitianMoorePenroseInverse_isHermitian L
      (show L.IsHermitian from hL)
  have hdag1 : L * Ldag * L = L :=
    HermitianMoorePenroseInverse.hermitianMoorePenroseInverse_penrose_left L
      (show L.IsHermitian from hL)
  have hdag2 : Ldag * L * Ldag = Ldag :=
    HermitianMoorePenroseInverse.hermitianMoorePenroseInverse_penrose_right L
      (show L.IsHermitian from hL)
  have hdagComm : L * Ldag = Ldag * L :=
    smqg_hermitian_pinv_comm L (show L.IsHermitian from hL)
  have hdag3 : (L * Ldag)ᴴ = L * Ldag := by
    rw [Matrix.conjTranspose_mul, hdagH, hL, hdagComm]
  have hdag4 : (Ldag * L)ᴴ = Ldag * L := by
    rw [Matrix.conjTranspose_mul, hdagH, hL, hdagComm]
  have hLdagU : ∀ g, Ldag * U g = U g * Ldag := by
    intro g
    exact moorePenrose_commutes_unitary L Ldag (U g) hL
      hdag1 hdag2 hdag3 hdag4 (hLU g) (hUleft g) (hUright g)
  letI : Invertible (1 : Matrix n n ℂ) := invertibleOne
  have hbase := gt_character_short U hU hUH χ ψ hχ hψ hχu hψu
    (1 : Matrix n n ℂ) (fun g => by simp) hne
  have hPP : Pχ * Pψ = 0 := by
    simpa [Pχ, Pψ] using hbase.2.2.1
  have hPχH : Pχᴴ = Pχ := by
    simpa [Pχ] using hbase.2.2.2.1
  have commute_sum (X : Matrix n n ℂ)
      (hXU : ∀ g, X * U g = U g * X) (φ : G₀ → ℂ) :
      X * ((Fintype.card G₀ : ℂ)⁻¹ • ∑ g, star (φ g) • U g) =
        ((Fintype.card G₀ : ℂ)⁻¹ • ∑ g, star (φ g) • U g) * X := by
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sum, Matrix.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro g hg
    rw [Matrix.mul_smul, Matrix.smul_mul, hXU g]
  have hLdagPχ : Ldag * Pχ = Pχ * Ldag := by
    simpa [Pχ] using commute_sum Ldag hLdagU χ
  have hLdagPψ : Ldag * Pψ = Pψ * Ldag := by
    simpa [Pψ] using commute_sum Ldag hLdagU ψ
  have hPNPχ : PN * Pχ = Pχ * PN := by
    simpa [Pχ] using commute_sum PN hPNU χ
  have hPNPψ : PN * Pψ = Pψ * PN := by
    simpa [Pψ] using commute_sum PN hPNU ψ
  have hLPχ : L * Pχ = Pχ * L := by
    simpa [Pχ] using commute_sum L hLU χ
  have hLPψ : L * Pψ = Pψ * L := by
    simpa [Pψ] using commute_sum L hLU ψ
  have hQNPχ : QN * Pχ = Pχ * QN := by
    dsimp [QN]
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hPNPχ]
  have hQNPψ : QN * Pψ = Pψ * QN := by
    dsimp [QN]
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hPNPψ]
  have short_comm (P : Matrix n n ℂ)
      (hQP : QN * P = P * QN) (hLP : L * P = P * L) :
      Lshort * P = P * Lshort := by
    dsimp [Lshort]
    calc
      QN * L * QN * P = QN * L * (QN * P) := by
        simp only [Matrix.mul_assoc]
      _ = QN * L * (P * QN) := by rw [hQP]
      _ = QN * (L * P) * QN := by simp only [Matrix.mul_assoc]
      _ = QN * (P * L) * QN := by rw [hLP]
      _ = (QN * P) * L * QN := by simp only [Matrix.mul_assoc]
      _ = (P * QN) * L * QN := by rw [hQP]
      _ = P * (QN * L * QN) := by simp only [Matrix.mul_assoc]
  have hshortPχ : Lshort * Pχ = Pχ * Lshort :=
    short_comm Pχ hQNPχ hLPχ
  have hshortPψ : Lshort * Pψ = Pψ * Lshort :=
    short_comm Pψ hQNPψ hLPψ
  have hdagBlock : Pχ * Ldag * Pψ = 0 := by
    calc
      Pχ * Ldag * Pψ = Pχ * Pψ * Ldag := by
        simp only [Matrix.mul_assoc]
        rw [← hLdagPψ]
      _ = 0 := by rw [hPP, Matrix.zero_mul]
  have hshortBlock : Pχ * Lshort * Pψ = 0 := by
    calc
      Pχ * Lshort * Pψ = Pχ * (Lshort * Pψ) := by
        simp only [Matrix.mul_assoc]
      _ = Pχ * (Pψ * Lshort) := by rw [hshortPψ]
      _ = (Pχ * Pψ) * Lshort := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hPP, Matrix.zero_mul]
  refine ⟨hLdagPχ, hPNPχ, hshortPχ, hdagBlock, hshortBlock, ?_⟩
  intro k m _ _ A Z hA hZ
  calc
    Aᴴ * (Ldag * Z) = (Pχ * A)ᴴ * (Ldag * (Pψ * Z)) := by rw [hA, hZ]
    _ = (Aᴴ * Pχ) * (Pψ * (Ldag * Z)) := by
      rw [Matrix.conjTranspose_mul, hPχH,
        ← Matrix.mul_assoc Ldag Pψ Z, hLdagPψ]
      simp only [Matrix.mul_assoc]
    _ = Aᴴ * ((Pχ * Pψ) * (Ldag * Z)) := by
      simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hPP, Matrix.zero_mul, Matrix.mul_zero]

end CharacterInvariantShort
end NCG
