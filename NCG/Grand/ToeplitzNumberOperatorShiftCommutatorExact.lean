import NCG.Grand.ToeplitzNumberOperatorCompactResolventExact

/-!
# Number-operator coordinates and the Toeplitz shift commutator

The resolvent-defined number operator acts coordinatewise by
`(Nx)_n=n x_n`.  Hence `Ne_n=n e_n`, the unilateral shift satisfies
`[N,S]e_n=Se_n`, and any bounded operator commuting with `N` on the standard
basis core is diagonal in that basis.
-/

noncomputable section

open scoped lp

namespace NCG
namespace ToeplitzScreenObstruction

/-- The resolvent-range equivalence recovers the preimage coordinate from a
domain vector. -/
theorem numberResolventRangeEquiv_symm_coordinate
    (x : numberOperator.domain) (n : ℕ) :
    numberResolventRangeEquiv.symm x n =
      ((n : ℂ) - Complex.I) * (x : H) n := by
  let y : H := numberResolventRangeEquiv.symm x
  have hxy : numberResolvent y = (x : H) := by
    have heq := numberResolventRangeEquiv.apply_symm_apply x
    exact congrArg Subtype.val heq
  have hn : ((n : ℂ) - Complex.I)⁻¹ * y n = (x : H) n := by
    simpa only [numberResolvent_apply] using congrArg (fun f : H ↦ f n) hxy
  change y n = ((n : ℂ) - Complex.I) * (x : H) n
  rw [← hn]
  field_simp [natCast_sub_I_ne_zero n]

/-- The resolvent-defined number operator acts by multiplication by the
coordinate index. -/
theorem numberOperator_apply_coordinate
    (x : numberOperator.domain) (n : ℕ) :
    numberOperator x n = (n : ℂ) * (x : H) n := by
  rw [numberOperator_apply]
  change numberResolventRangeEquiv.symm x n +
      Complex.I * (x : H) n = (n : ℂ) * (x : H) n
  rw [numberResolventRangeEquiv_symm_coordinate]
  ring

/-- Each standard basis vector is an eigenvector of the number operator with
eigenvalue `n`. -/
theorem numberOperator_basisVector (n : ℕ) :
    numberOperator
      ⟨basisVector n, basisVector_mem_numberOperatorDomain n⟩ =
        (n : ℂ) • basisVector n := by
  apply lp.ext
  funext j
  rw [numberOperator_apply_coordinate]
  by_cases hj : j = n <;> simp [basisVector_apply, hj]

/-- The unilateral shift obeys `[N,S]e_n=Se_n` on every standard basis
vector. -/
theorem numberOperator_comm_unilateralShift_basisVector (n : ℕ) :
    numberOperator
        ⟨unilateralShift (basisVector n), by
          rw [unilateralShift_basisVector]
          exact basisVector_mem_numberOperatorDomain (n + 1)⟩ -
      unilateralShift
        (numberOperator
          ⟨basisVector n, basisVector_mem_numberOperatorDomain n⟩) =
        unilateralShift (basisVector n) := by
  simp only [unilateralShift_basisVector]
  rw [numberOperator_basisVector, numberOperator_basisVector, map_smul,
    unilateralShift_basisVector]
  module

/-- A bounded operator that commutes with the number operator on the standard
basis core maps each basis vector into its one-dimensional eigenspace. -/
theorem diagonal_on_basis_of_commutes_numberOperator
    (P : H →L[ℂ] H)
    (hpres : ∀ n, P (basisVector n) ∈ numberOperator.domain)
    (hcomm : ∀ n,
      numberOperator ⟨P (basisVector n), hpres n⟩ =
        P (numberOperator
          ⟨basisVector n, basisVector_mem_numberOperatorDomain n⟩)) :
    ∀ n, P (basisVector n) =
      (P (basisVector n) n) • basisVector n := by
  intro n
  apply lp.ext
  funext j
  by_cases hj : j = n
  · subst j
    simp [basisVector_apply]
  · have hcoord := congrArg (fun f : H ↦ f j) (hcomm n)
    rw [numberOperator_apply_coordinate] at hcoord
    rw [numberOperator_basisVector, map_smul] at hcoord
    change (j : ℂ) * P (basisVector n) j =
      (n : ℂ) * P (basisVector n) j at hcoord
    have hcast : (j : ℂ) - (n : ℂ) ≠ 0 := by
      exact sub_ne_zero.mpr (by exact_mod_cast hj)
    have hzero : ((j : ℂ) - (n : ℂ)) * P (basisVector n) j = 0 := by
      linear_combination hcoord
    have hz : P (basisVector n) j = 0 :=
      (mul_eq_zero.mp hzero).resolve_left hcast
    simp [basisVector_apply, hj, hz]

end ToeplitzScreenObstruction
end NCG
