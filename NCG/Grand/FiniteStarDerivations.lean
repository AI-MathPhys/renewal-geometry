/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import NCG.Grand.InnerDerivationConditioning

/-!
# Finite star derivations are inner

This module gives the exact finite matrix-algebra theorem used by
`thm:SMST-finite-inner-derivation`.  Vanishing Leibniz and star residuals on
the matrix-unit basis force a linear map to be a derivation commuting with
the adjoint.  The standard matrix-unit implementer is then reduced to its
unique traceless Hermitian representative.
-/

open Matrix Finset

namespace NCG

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The Leibniz defect for one ordered pair of matrix units. -/
def leibnizUnitDefect (L : Matrix d d ℂ →ₗ[ℂ] Matrix d d ℂ)
    (p : d × d × d × d) : Matrix d d ℂ :=
  L (Matrix.single p.1 p.2.1 1 * Matrix.single p.2.2.1 p.2.2.2 1)
    - L (Matrix.single p.1 p.2.1 1) * Matrix.single p.2.2.1 p.2.2.2 1
    - Matrix.single p.1 p.2.1 1 * L (Matrix.single p.2.2.1 p.2.2.2 1)

/-- Sum-of-squares Leibniz defect on the matrix-unit basis.  The product index
is merely a flattened notation for the manuscript's four nested sums. -/
def leibnizResidual (L : Matrix d d ℂ →ₗ[ℂ] Matrix d d ℂ) : ℝ :=
  ∑ p : d × d × d × d, hsFrobSq (leibnizUnitDefect L p)

/-- The adjoint defect for one matrix unit. -/
def starUnitDefect (L : Matrix d d ℂ →ₗ[ℂ] Matrix d d ℂ)
    (p : d × d) : Matrix d d ℂ :=
  L (Matrix.single p.1 p.2 1)ᴴ - (L (Matrix.single p.1 p.2 1))ᴴ

/-- Sum-of-squares adjoint defect on the matrix-unit basis. -/
def starResidual (L : Matrix d d ℂ →ₗ[ℂ] Matrix d d ℂ) : ℝ :=
  ∑ p : d × d, hsFrobSq (starUnitDefect L p)

private lemma leibniz_units_of_residual_zero
    (L : Matrix d d ℂ →ₗ[ℂ] Matrix d d ℂ)
    (hL : leibnizResidual L = 0) (a b c e : d) :
    L (Matrix.single a b 1 * Matrix.single c e 1)
      = L (Matrix.single a b 1) * Matrix.single c e 1
        + Matrix.single a b 1 * L (Matrix.single c e 1) := by
  have hterm : hsFrobSq
      (L (Matrix.single a b 1 * Matrix.single c e 1)
        - L (Matrix.single a b 1) * Matrix.single c e 1
        - Matrix.single a b 1 * L (Matrix.single c e 1)) = 0 := by
    have hp := (Finset.sum_eq_zero_iff_of_nonneg
      (fun p _ => hsFrobSq_nonneg (leibnizUnitDefect L p))).mp hL
      (a, b, c, e) (mem_univ _)
    exact hp
  have hz := (hsFrobSq_eq_zero_iff _).mp hterm
  apply sub_eq_zero.mp
  calc
    L (Matrix.single a b 1 * Matrix.single c e 1)
        - (L (Matrix.single a b 1) * Matrix.single c e 1
          + Matrix.single a b 1 * L (Matrix.single c e 1))
      = L (Matrix.single a b 1 * Matrix.single c e 1)
          - L (Matrix.single a b 1) * Matrix.single c e 1
          - Matrix.single a b 1 * L (Matrix.single c e 1) := by abel
    _ = 0 := hz

private lemma star_units_of_residual_zero
    (L : Matrix d d ℂ →ₗ[ℂ] Matrix d d ℂ)
    (hstar : starResidual L = 0) (a b : d) :
    L (Matrix.single a b 1)ᴴ = (L (Matrix.single a b 1))ᴴ := by
  have hab := (Finset.sum_eq_zero_iff_of_nonneg
    (fun p _ => hsFrobSq_nonneg (starUnitDefect L p))).mp hstar
    (a, b) (mem_univ _)
  exact sub_eq_zero.mp ((hsFrobSq_eq_zero_iff _).mp hab)

/-- The standard implementer assembled from the first matrix-unit column. -/
noncomputable def derivationImplementer (o : d)
    (L : Matrix d d ℂ →ₗ[ℂ] Matrix d d ℂ) : Matrix d d ℂ :=
  ∑ k, L (Matrix.single k o 1) * Matrix.single o k 1

private theorem derivationImplementer_units
    (o : d)
    (L : Matrix d d ℂ →ₗ[ℂ] Matrix d d ℂ)
    (hLeib : ∀ a b c e : d,
      L (Matrix.single a b 1 * Matrix.single c e 1)
        = L (Matrix.single a b 1) * Matrix.single c e 1
          + Matrix.single a b 1 * L (Matrix.single c e 1))
    (i j : d) :
    L (Matrix.single i j 1)
      = derivationImplementer o L * Matrix.single i j 1
        - Matrix.single i j 1 * derivationImplementer o L := by
  have hfactor : Matrix.single i j (1 : ℂ) =
      Matrix.single i o 1 * Matrix.single o j 1 := by simp
  have hone : ∑ k : d, Matrix.single k k (1 : ℂ) = 1 :=
    Matrix.sum_single_one
  have hright : Matrix.single i j 1 * derivationImplementer o L =
      L (Matrix.single i o 1) * Matrix.single o j 1
        - L (Matrix.single i j 1) := by
    rw [derivationImplementer, Matrix.mul_sum]
    have hk : ∀ k : d,
        Matrix.single i j 1 * L (Matrix.single k o 1)
            * Matrix.single o k 1
          = (if j = k then
              L (Matrix.single i o 1) * Matrix.single o k 1 else 0)
              - L (Matrix.single i j 1) * Matrix.single k k 1 := by
      intro k
      have h := hLeib i j k o
      have hm := congrArg (fun X => X * Matrix.single o k (1 : ℂ)) h
      by_cases hjk : j = k
      · subst k
        rw [add_mul] at hm
        simp [Matrix.mul_assoc] at hm
        rw [if_pos rfl]
        rw [hm]
        simp only [Matrix.mul_assoc]
        abel
      · rw [add_mul] at hm
        simp [hjk, Matrix.mul_assoc] at hm
        rw [if_neg hjk]
        simp only [zero_sub, Matrix.mul_assoc]
        exact eq_neg_of_add_eq_zero_right hm.symm
    simp_rw [← Matrix.mul_assoc, hk]
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq Finset.univ j,
      ← Matrix.mul_sum, hone, Matrix.mul_one]
    simp only [Finset.mem_univ, if_true]
  have hleft : derivationImplementer o L * Matrix.single i j 1 =
      L (Matrix.single i o 1) * Matrix.single o j 1 := by
    rw [derivationImplementer, Matrix.sum_mul]
    simp only [Matrix.mul_assoc]
    rw [Finset.sum_eq_single i]
    · simp [Matrix.single_mul_single_same]
    · intro k _ hki
      simp [hki]
    · intro hi
      exact (hi (mem_univ i)).elim
  rw [hleft, hright]
  abel

/-- Vanishing finite Leibniz and star residuals characterize a unique
traceless Hermitian Hamiltonian implementer. -/
theorem finite_star_derivation_inner [Nonempty d]
    (L : Matrix d d ℂ →ₗ[ℂ] Matrix d d ℂ)
    (hLeib : leibnizResidual L = 0) (hstar : starResidual L = 0) :
    ∃! H : Matrix d d ℂ,
      Hᴴ = H ∧ Matrix.trace H = 0 ∧
        ∀ X, L X = (-Complex.I) • (H * X - X * H) := by
  have hLeibUnits := leibniz_units_of_residual_zero L hLeib
  have hstarUnits := star_units_of_residual_zero L hstar
  let o := Classical.choice ‹Nonempty d›
  let A := derivationImplementer o L
  have hAunits : ∀ i j : d,
      L (Matrix.single i j 1) = A * Matrix.single i j 1
        - Matrix.single i j 1 * A :=
    derivationImplementer_units o L hLeibUnits
  have hcentral : ∀ i j : d,
      Matrix.single i j 1 * (A + Aᴴ) = (A + Aᴴ) * Matrix.single i j 1 := by
    intro i j
    have hs := hstarUnits j i
    rw [Matrix.conjTranspose_single] at hs
    simp only [star_one] at hs
    rw [hAunits i j, hAunits j i, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_single] at hs
    rw [sub_eq_sub_iff_add_eq_add] at hs
    rw [Matrix.mul_add, add_mul]
    simpa only [star_one, add_comm] using hs.symm
  obtain ⟨z, hz⟩ := Matrix.mem_range_scalar_iff_commute_single'.mpr hcentral
  let K : Matrix d d ℂ := (2 : ℂ)⁻¹ • (A - Aᴴ)
  let Hraw : Matrix d d ℂ := Complex.I • K
  have hKcomm : ∀ X : Matrix d d ℂ,
      A * X - X * A = K * X - X * K := by
    intro X
    have hscalar : A + Aᴴ = z • 1 := by
      rw [← hz]
      ext i j
      by_cases hij : i = j <;> simp [Matrix.scalar_apply, hij]
    have htwo : A = K + (2 : ℂ)⁻¹ • (A + Aᴴ) := by
      dsimp [K]
      module
    rw [htwo, hscalar]
    simp only [add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one]
    module
  have hHraw : Hrawᴴ = Hraw := by
    dsimp [Hraw, K]
    rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose]
    simp
    module
  let H := Hraw - (Matrix.trace Hraw / (Fintype.card d : ℂ)) • 1
  have htraceReal : star (Matrix.trace Hraw) = Matrix.trace Hraw := by
    rw [← Matrix.trace_conjTranspose, hHraw]
  have hH : Hᴴ = H := by
    dsimp [H]
    rw [Matrix.conjTranspose_sub, hHraw, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_one]
    simp [htraceReal]
  have htr : Matrix.trace H = 0 := by
    dsimp only [H]
    simp only [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul]
    have hd0 : (Fintype.card d : ℂ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    rw [div_mul_cancel₀ _ hd0, sub_self]
  have hUnitImpl : ∀ i j : d,
      L (Matrix.single i j 1) = (-Complex.I) •
        (H * Matrix.single i j 1 - Matrix.single i j 1 * H) := by
    intro i j
    rw [hAunits i j, hKcomm]
    have hHcomm : H * Matrix.single i j 1 - Matrix.single i j 1 * H =
        Hraw * Matrix.single i j 1 - Matrix.single i j 1 * Hraw := by
      dsimp [H]
      simp only [sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.one_mul, Matrix.mul_one]
      module
    rw [hHcomm]
    dsimp [Hraw]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_sub, smul_smul]
    norm_num
  have hLX : ∀ X, L X = (-Complex.I) • (H * X - X * H) := by
    intro X
    induction X using Matrix.induction_on' with
    | h_zero => simp
    | h_add P Q hP hQ =>
        rw [map_add, hP, hQ, Matrix.mul_add, add_mul]
        module
    | h_std_basis i j x =>
        have hx : Matrix.single i j x = x • Matrix.single i j (1 : ℂ) := by
          rw [Matrix.smul_single, smul_eq_mul, mul_one]
        rw [hx, map_smul, hUnitImpl]
        simp only [Matrix.mul_smul, Matrix.smul_mul, ← smul_sub, smul_smul]
        module
  refine ⟨H, ⟨hH, htr, hLX⟩, ?_⟩
  intro H' hH'
  obtain ⟨hH'star, hH'tr, hH'impl⟩ := hH'
  apply inner_derivation_injective_on_traceless H' H hH'star hH hH'tr htr
  intro a b
  have h1 := hH'impl (Matrix.single a b 1)
  have h2 := hLX (Matrix.single a b 1)
  rw [h1] at h2
  have hi : (-Complex.I : ℂ) ≠ 0 := by norm_num
  exact smul_right_injective (Matrix d d ℂ) hi h2

end NCG
