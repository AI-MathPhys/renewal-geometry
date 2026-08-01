/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Dark-parity selection rule (`thm:dark-parity`, SM manuscript)

Let `J` be the retained block-centre parity (`J² = 1`) and `K_α`
the resolved coefficients.  If the parity leakage

  `ε = (1/4) Σ_α ‖[J, K_α]‖²_HS`

vanishes, then every resolved coefficient commutes with `J`
(multiplicative-domain rigidity in leakage form), so with
`P_± = (I ± J)/2` every visible–dark Dirac portal vanishes,

  `P₊ K_α P₋ = P₋ K_α P₊ = 0`,

each coefficient is parity block diagonal
(`K_α = P₊K_αP₊ + P₋K_αP₋` — internal odd–odd blocks such as
Majorana pairings remain allowed), and the odd sector has no
transition channel into the even (visible) sector:
`P₊ (K_α (P₋ρP₋) K_α†) P₊ = 0` — the lightest odd state is
absolutely stable (`dark_parity_selection`).  The premise clauses
`|K_ch| = 2` and the loaded odd neutral character locate the
theorem in the manuscript's dark-parity dictionary and are
interpretive; the formal content is leakage rigidity plus the
parity superselection identities.
-/

open Matrix

namespace NCG

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]

/-- The even parity projector `P₊ = (I + J)/2`. -/
noncomputable def parityPlus (J : Matrix n n ℂ) : Matrix n n ℂ :=
  (1/2 : ℂ) • (1 + J)

/-- The odd parity projector `P₋ = (I - J)/2`. -/
noncomputable def parityMinus (J : Matrix n n ℂ) : Matrix n n ℂ :=
  (1/2 : ℂ) • (1 - J)

omit [Fintype n] in
/-- The two parity projectors resolve the identity. -/
lemma parity_sum (J : Matrix n n ℂ) :
    parityPlus J + parityMinus J = 1 := by
  rw [parityPlus, parityMinus]
  module

omit [DecidableEq n] in
/-- Vanishing Hilbert–Schmidt leakage forces every coefficient to
commute with the parity. -/
lemma leakage_commute (J : Matrix n n ℂ) (K : ι → Matrix n n ℂ)
    (hleak : (1/4 : ℝ) * (∑ α, ((J * K α - K α * J)ᴴ
      * (J * K α - K α * J)).trace).re = 0) :
    ∀ α, J * K α = K α * J := by
  open scoped ComplexOrder in
  have hnn : ∀ α ∈ Finset.univ, (0 : ℂ) ≤ ((J * K α - K α * J)ᴴ
      * (J * K α - K α * J)).trace := fun α _ =>
    (Matrix.posSemidef_conjTranspose_mul_self _).trace_nonneg
  have hz : (∑ α, ((J * K α - K α * J)ᴴ
      * (J * K α - K α * J)).trace) = 0 := by
    open scoped ComplexOrder in
    have h0 : (0 : ℂ) ≤ ∑ α, ((J * K α - K α * J)ᴴ
        * (J * K α - K α * J)).trace := Finset.sum_nonneg hnn
    rw [Complex.nonneg_iff] at h0
    have hre : (∑ α, ((J * K α - K α * J)ᴴ
        * (J * K α - K α * J)).trace).re = 0 := by linarith
    exact Complex.ext hre h0.2.symm
  intro α
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hz α
    (Finset.mem_univ α)
  have h2 := Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp h1
  rw [sub_eq_zero] at h2
  exact h2

/-- The core cancellation: a commuting coefficient has vanishing
cross-parity blocks. -/
lemma cross_block_zero (J A : Matrix n n ℂ) (hJ2 : J * J = 1)
    (hcomm : J * A = A * J) :
    (1 + J) * A * (1 - J) = 0 ∧ (1 - J) * A * (1 + J) = 0 := by
  constructor
  · rw [Matrix.add_mul, Matrix.one_mul, Matrix.add_mul,
      Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_one,
      hcomm, Matrix.mul_assoc, hJ2, Matrix.mul_one]
    abel
  · rw [Matrix.sub_mul, Matrix.one_mul, Matrix.sub_mul,
      Matrix.mul_add, Matrix.mul_add, Matrix.mul_one, Matrix.mul_one,
      hcomm, Matrix.mul_assoc, hJ2, Matrix.mul_one]
    abel

/-- `thm:dark-parity`: with vanishing parity leakage, every
resolved coefficient commutes with `J`, every visible–dark portal
vanishes, coefficients are parity block diagonal, and the odd
sector has no transition channel into the even sector. -/
theorem dark_parity_selection (J : Matrix n n ℂ)
    (K : ι → Matrix n n ℂ) (hJ2 : J * J = 1)
    (hleak : (1/4 : ℝ) * (∑ α, ((J * K α - K α * J)ᴴ
      * (J * K α - K α * J)).trace).re = 0) :
    ∀ α, (J * K α = K α * J)
      ∧ (parityPlus J * K α * parityMinus J = 0)
      ∧ (parityMinus J * K α * parityPlus J = 0)
      ∧ (K α = parityPlus J * K α * parityPlus J
          + parityMinus J * K α * parityMinus J)
      ∧ ∀ ρ : Matrix n n ℂ,
          parityPlus J * (K α * (parityMinus J * ρ * parityMinus J)
            * (K α)ᴴ) * parityPlus J = 0 := by
  intro α
  have hcomm := leakage_commute J K hleak α
  obtain ⟨hc1, hc2⟩ := cross_block_zero J (K α) hJ2 hcomm
  have hp1 : parityPlus J * K α * parityMinus J = 0 := by
    rw [parityPlus, parityMinus, Matrix.smul_mul, Matrix.smul_mul,
      Matrix.mul_smul, hc1, smul_zero, smul_zero]
  have hp2 : parityMinus J * K α * parityPlus J = 0 := by
    rw [parityPlus, parityMinus, Matrix.smul_mul, Matrix.smul_mul,
      Matrix.mul_smul, hc2, smul_zero, smul_zero]
  refine ⟨hcomm, hp1, hp2, ?_, ?_⟩
  · have hK : (parityPlus J + parityMinus J) * K α
        * (parityPlus J + parityMinus J) = K α := by
      rw [parity_sum, Matrix.one_mul, Matrix.mul_one]
    calc K α = (parityPlus J + parityMinus J) * K α
        * (parityPlus J + parityMinus J) := hK.symm
      _ = parityPlus J * K α * parityPlus J
          + parityPlus J * K α * parityMinus J
          + (parityMinus J * K α * parityPlus J
            + parityMinus J * K α * parityMinus J) := by
        rw [Matrix.add_mul, Matrix.add_mul, Matrix.mul_add,
          Matrix.mul_add]
      _ = parityPlus J * K α * parityPlus J
          + parityMinus J * K α * parityMinus J := by
        rw [hp1, hp2]
        abel
  · intro ρ
    have h : parityPlus J * (K α * (parityMinus J * ρ * parityMinus J)
        * (K α)ᴴ) * parityPlus J
        = (parityPlus J * K α * parityMinus J)
          * (ρ * parityMinus J * (K α)ᴴ * parityPlus J) := by
      simp only [Matrix.mul_assoc]
    rw [h, hp1, Matrix.zero_mul]

end NCG
