/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Flagship.CharacterLeakage

/-!
# Character-projected Hankel saturation

The character projector enters through its projected Krylov synthesis.  Its
Gram is the zero-shift character Hankel matrix, so rank, survival, and flat
future saturation are finite linear-algebra consequences.  The last theorem
records the exact `pi tensor multiplicity` dimension formula.
-/

open Matrix
open scoped ComplexOrder

namespace NCG
namespace CharacterHankelSectorSaturation

/-- The depth-`n` controllability matrix after applying a character projector. -/
def characterControllability
    {h f : Type*} [Fintype h] [Fintype f] [DecidableEq h]
    (P T : Matrix h h ℂ) (S : Matrix h f ℂ) (n : ℕ) :
    Matrix h (Fin n × f) ℂ :=
  fun i jf => (P * T ^ (jf.1 : ℕ) * S) i jf.2

/-- The character-projected moment `S* P T^k S`. -/
def characterMoment
    {h f : Type*} [Fintype h] [Fintype f] [DecidableEq h]
    (P T : Matrix h h ℂ) (S : Matrix h f ℂ) (k : ℕ) : Matrix f f ℂ :=
  Sᴴ * P * T ^ k * S

/-- The manuscript's zero-shift character Hankel matrix, assembled from the
projected moments at indices `i+j`. -/
def characterHankel
    {h f : Type*} [Fintype h] [Fintype f] [DecidableEq h]
    (P T : Matrix h h ℂ) (S : Matrix h f ℂ) (n : ℕ) :
    Matrix (Fin n × f) (Fin n × f) ℂ :=
  fun ia jb => characterMoment P T S (ia.1 + jb.1) ia.2 jb.2

/-- The zero-shift character Hankel matrix is the Gram of the projected
controllability synthesis. -/
def characterHankelZero
    {h f : Type*} [Fintype h] [Fintype f] [DecidableEq h]
    (P T : Matrix h h ℂ) (S : Matrix h f ℂ) (n : ℕ) :
    Matrix (Fin n × f) (Fin n × f) ℂ :=
  (characterControllability P T S n)ᴴ * characterControllability P T S n

/-- A self-adjoint projector commuting with a self-adjoint transition turns
the Gram of two projected Krylov blocks into the corresponding projected
moment. -/
theorem projected_block_gram_eq_moment
    {h f : Type*} [Fintype h] [Fintype f] [DecidableEq h]
    (P T : Matrix h h ℂ) (S : Matrix h f ℂ)
    (hPstar : Pᴴ = P) (hPid : P * P = P)
    (hTstar : Tᴴ = T) (hcomm : P * T = T * P) (i j : ℕ) :
    (P * T ^ i * S)ᴴ * (P * T ^ j * S) =
      characterMoment P T S (i + j) := by
  have hpowcomm : T ^ i * P = P * T ^ i :=
    ((show Commute P T from hcomm).pow_right i).eq.symm
  rw [conjTranspose_mul, conjTranspose_mul, Matrix.conjTranspose_pow,
    hPstar, hTstar]
  simp only [characterMoment, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc P P, hPid,
    ← Matrix.mul_assoc (T ^ i) P, hpowcomm,
    Matrix.mul_assoc P (T ^ i), ← Matrix.mul_assoc (T ^ i) (T ^ j), ← pow_add]

/-- Under the character-projector identities, the moment Hankel matrix is
literally the Gram of the projected controllability synthesis. -/
theorem characterHankelZero_eq_characterHankel
    {h f : Type*} [Fintype h] [Fintype f] [DecidableEq h]
    (P T : Matrix h h ℂ) (S : Matrix h f ℂ) (n : ℕ)
    (hPstar : Pᴴ = P) (hPid : P * P = P)
    (hTstar : Tᴴ = T) (hcomm : P * T = T * P) :
    characterHankelZero P T S n = characterHankel P T S n := by
  ext ia jb
  simpa only [characterHankelZero, characterHankel,
    characterControllability, Matrix.mul_apply, conjTranspose_apply] using
    congrArg (fun A : Matrix f f ℂ => A ia.2 jb.2)
      (projected_block_gram_eq_moment P T S hPstar hPid hTstar hcomm
        (ia.1 : ℕ) (jb.1 : ℕ))

theorem characterHankel_rank_eq_projectedKrylov_rank
    {h f : Type*} [Fintype h] [Fintype f] [DecidableEq h]
    (P T : Matrix h h ℂ) (S : Matrix h f ℂ) (n : ℕ)
    (hPstar : Pᴴ = P) (hPid : P * P = P)
    (hTstar : Tᴴ = T) (hcomm : P * T = T * P) :
    (characterHankel P T S n).rank =
      (characterControllability P T S n).rank := by
  rw [← characterHankelZero_eq_characterHankel P T S n hPstar hPid hTstar hcomm]
  exact Matrix.rank_conjTranspose_mul_self _

/-- A character sector survives exactly when its finite projected synthesis,
equivalently its character Hankel Gram, is nonzero. -/
theorem character_sector_survives_iff_hankel_nonzero
    {h f : Type*} [Fintype h] [Fintype f] [DecidableEq h]
    (P T : Matrix h h ℂ) (S : Matrix h f ℂ) (n : ℕ)
    (hPstar : Pᴴ = P) (hPid : P * P = P)
    (hTstar : Tᴴ = T) (hcomm : P * T = T * P) :
    characterControllability P T S n ≠ 0 ↔
      characterHankel P T S n ≠ 0 := by
  rw [← characterHankelZero_eq_characterHankel P T S n hPstar hPid hTstar hcomm,
    characterHankelZero]
  exact (not_congr Matrix.conjTranspose_mul_self_eq_zero).symm

/-- Nonzero sector survival has a concrete character-projected moment entry
witness at some horizon below `n`. -/
theorem character_sector_survival_witness
    {h f : Type*} [Fintype h] [Fintype f] [DecidableEq h]
    (P T : Matrix h h ℂ) (S : Matrix h f ℂ) (n : ℕ)
    (hsurvives : characterControllability P T S n ≠ 0) :
    ∃ i : h, ∃ j : Fin n, ∃ a : f,
      (P * T ^ (j : ℕ) * S) i a ≠ 0 := by
  by_contra h
  push Not at h
  apply hsurvives
  ext i ja
  exact h i ja.1 ja.2

/-- A surviving sector is equivalently witnessed by a nonzero entry of one
of the character-projected moments occurring in the finite Hankel window. -/
theorem character_sector_survives_iff_projected_moment_nonzero
    {h f : Type*} [Fintype h] [Fintype f] [DecidableEq h]
    (P T : Matrix h h ℂ) (S : Matrix h f ℂ) (n : ℕ)
    (hPstar : Pᴴ = P) (hPid : P * P = P)
    (hTstar : Tᴴ = T) (hcomm : P * T = T * P) :
    characterControllability P T S n ≠ 0 ↔
      ∃ i j : Fin n, ∃ a b : f,
        characterMoment P T S ((i : ℕ) + (j : ℕ)) a b ≠ 0 := by
  rw [character_sector_survives_iff_hankel_nonzero P T S n
    hPstar hPid hTstar hcomm]
  constructor
  · intro hH
    by_contra h
    push Not at h
    apply hH
    ext ia jb
    exact h ia.1 jb.1 ia.2 jb.2
  · rintro ⟨i, j, a, b, hij⟩ hzero
    exact hij (congrArg (fun A => A (i, a) (j, b)) hzero)

/-- In isotypic coordinates `pi tensor M`, the represented dimension is
exactly `d_pi * multiplicity`; hence it is divisible by `d_pi`, and division
recovers the multiplicity. -/
theorem isotypic_dimension_and_multiplicity (d : ℕ) (M : Type*) [Fintype M] :
    Fintype.card (Fin d × M) = d * Fintype.card M
      ∧ d ∣ Fintype.card (Fin d × M) := by
  rw [Fintype.card_prod, Fintype.card_fin]
  exact ⟨rfl, dvd_mul_right d (Fintype.card M)⟩

/-- If the projected Krylov carrier is the `π ⊗ M` isotypic block, Hankel
rank is `dπ` times the represented multiplicity, and division by the positive
irreducible dimension recovers that multiplicity. -/
theorem characterHankel_isotypic_rank_and_multiplicity
    {h f : Type*} [Fintype h] [Fintype f] [DecidableEq h]
    (P T : Matrix h h ℂ) (S : Matrix h f ℂ) (n d : ℕ)
    (M : Type*) [Fintype M]
    (hPstar : Pᴴ = P) (hPid : P * P = P)
    (hTstar : Tᴴ = T) (hcomm : P * T = T * P)
    (hisotypic : (characterControllability P T S n).rank =
      Fintype.card (Fin d × M)) (hd : d ≠ 0) :
    (characterHankel P T S n).rank = d * Fintype.card M
      ∧ d ∣ (characterHankel P T S n).rank
      ∧ (characterHankel P T S n).rank / d = Fintype.card M := by
  have hrank : (characterHankel P T S n).rank = d * Fintype.card M := by
    rw [characterHankel_rank_eq_projectedKrylov_rank P T S n
      hPstar hPid hTstar hcomm, hisotypic, Fintype.card_prod, Fintype.card_fin]
  refine ⟨hrank, hrank ▸ dvd_mul_right d (Fintype.card M), ?_⟩
  rw [hrank]
  simpa [Nat.mul_comm] using
    (Nat.mul_div_left (Fintype.card M) (Nat.pos_of_ne_zero hd))

/-- Consecutive equality for the actual projected Krylov recursion forces
transition invariance and therefore reconstructs every later represented
future layer. -/
theorem projectedKrylov_consecutive_rank_saturation
    {E : Type*} [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    (K : ℕ → Submodule ℂ E) (T : E →ₗ[ℂ] E) (n : ℕ)
    (hmono : ∀ k, K k ≤ K (k + 1))
    (hforward : ∀ k, Submodule.map T (K k) ≤ K (k + 1))
    (hstep : ∀ k, K (k + 1) ≤ K k ⊔ Submodule.map T (K k))
    (heq : Module.finrank ℂ (K (n + 1)) ≤ Module.finrank ℂ (K n)) :
    K (n + 1) = K n ∧ ∀ j, n ≤ j → K j = K n := by
  obtain ⟨hflat, hfreeze⟩ := krylov_stabilization K T n hmono hstep heq
  refine ⟨hflat, hfreeze ?_⟩
  simpa only [hflat] using hforward n

end CharacterHankelSectorSaturation
end NCG
