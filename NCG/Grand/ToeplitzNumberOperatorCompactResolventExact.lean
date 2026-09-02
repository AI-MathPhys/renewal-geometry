import NCG.Grand.ToeplitzNumberResolventExact
import NCG.SpectralTriple.Basic

/-!
# The Toeplitz number operator as an unbounded operator

The number operator is defined on the range of its explicit compact
resolvent `R=(N-i)⁻¹`.  Injectivity of `R` identifies its range with the
ambient Hilbert space; on a range vector `x=Ry` we set `Nx=y+i x`.
Consequently `N-i` and `R` are exact two-sided inverses.  The domain is dense
because it contains every standard basis vector and hence every canonical
finite coordinate approximation.
-/

noncomputable section

open Filter Topology
open scoped lp

namespace NCG
namespace ToeplitzScreenObstruction

/-- The domain of the number operator, expressed as the range of its
resolvent. -/
abbrev numberOperatorDomain : Submodule ℂ H :=
  LinearMap.range numberResolvent.toLinearMap

/-- The resolvent identifies `H` linearly with the number-operator domain. -/
def numberResolventRangeEquiv : H ≃ₗ[ℂ] numberOperatorDomain :=
  LinearEquiv.ofInjective numberResolvent.toLinearMap numberResolvent_injective

/-- The unbounded number operator recovered from `R=(N-i)⁻¹`. -/
def numberOperator : H →ₗ.[ℂ] H where
  domain := numberOperatorDomain
  toFun := numberResolventRangeEquiv.symm.toLinearMap +
    Complex.I • numberOperatorDomain.subtype

@[simp]
theorem numberOperator_apply (x : numberOperator.domain) :
    numberOperator x = numberResolventRangeEquiv.symm x + Complex.I • (x : H) :=
  rfl

theorem natCast_sub_I_ne_zero (n : ℕ) : (n : ℂ) - Complex.I ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  norm_num at him

/-- Every standard basis vector belongs to the number-operator domain. -/
theorem basisVector_mem_numberOperatorDomain (n : ℕ) :
    basisVector n ∈ numberOperator.domain := by
  refine ⟨((n : ℂ) - Complex.I) • basisVector n, ?_⟩
  apply lp.ext
  funext j
  by_cases hj : j = n
  · subst j
    simp [numberResolvent_apply, basisVector_apply,
      natCast_sub_I_ne_zero]
  · simp [numberResolvent_apply, basisVector_apply, hj]

/-- A finite coordinate screen is the corresponding finite basis expansion. -/
theorem l2FinsetScreen_eq_sum_basisVector
    (s : Finset ℕ) (f : H) :
    l2FinsetScreen (E := ℂ) s f =
      ∑ n ∈ s, f n • basisVector n := by
  apply lp.ext
  funext j
  rw [l2FinsetScreen_apply]
  rw [lp.coeFn_sum, Finset.sum_apply]
  simp_rw [lp.coeFn_smul, Pi.smul_apply, basisVector_apply]
  by_cases hj : j ∈ s <;> simp [hj]

/-- Every canonical finite coordinate approximation lies in the unbounded
number-operator domain. -/
theorem l2FinsetScreen_mem_numberOperatorDomain
    (s : Finset ℕ) (f : H) :
    l2FinsetScreen (E := ℂ) s f ∈ numberOperator.domain := by
  rw [l2FinsetScreen_eq_sum_basisVector]
  exact Submodule.sum_mem numberOperator.domain fun n hn ↦
    Submodule.smul_mem numberOperator.domain (f n)
      (basisVector_mem_numberOperatorDomain n)

/-- The number-operator domain is dense. -/
theorem numberOperator_dense_domain :
    Dense (numberOperator.domain : Set H) := by
  rw [dense_iff_closure_eq, Set.eq_univ_iff_forall]
  intro f
  exact mem_closure_of_tendsto
    (tendsto_l2FinsetScreen_range_apply f)
    (Eventually.of_forall fun n ↦
      l2FinsetScreen_mem_numberOperatorDomain (Finset.range n) f)

/-- The explicit resolvent maps every vector into the number-operator
domain. -/
theorem numberResolvent_mem_numberOperatorDomain (y : H) :
    numberResolvent y ∈ numberOperator.domain :=
  ⟨y, rfl⟩

/-- The range equivalence sends a vector to its resolvent image. -/
theorem numberResolventRangeEquiv_apply (y : H) :
    (numberResolventRangeEquiv y : H) = numberResolvent y :=
  rfl

/-- The inverse range equivalence recovers the resolvent preimage. -/
theorem numberResolventRangeEquiv_symm_apply_resolvent (y : H) :
    numberResolventRangeEquiv.symm
      ⟨numberResolvent y, numberResolvent_mem_numberOperatorDomain y⟩ = y := by
  have harg :
      (⟨numberResolvent y, numberResolvent_mem_numberOperatorDomain y⟩ :
          numberOperatorDomain) = numberResolventRangeEquiv y := by
    apply Subtype.ext
    rfl
  rw [harg, LinearEquiv.symm_apply_apply]

/-- `R=(N-i)⁻¹` is a right inverse of `N-i`. -/
theorem numberResolvent_right_inverse (y : H) :
    numberOperator
        ⟨numberResolvent y, numberResolvent_mem_numberOperatorDomain y⟩ -
      Complex.I • numberResolvent y = y := by
  rw [numberOperator_apply]
  change numberResolventRangeEquiv.symm
      (⟨numberResolvent y, numberResolvent_mem_numberOperatorDomain y⟩ :
        numberOperatorDomain) +
      Complex.I • numberResolvent y - Complex.I • numberResolvent y = y
  rw [numberResolventRangeEquiv_symm_apply_resolvent]
  abel

/-- `R=(N-i)⁻¹` is a left inverse of `N-i` on the number-operator domain. -/
theorem numberResolvent_left_inverse (x : numberOperator.domain) :
    numberResolvent (numberOperator x - Complex.I • (x : H)) = x := by
  rw [numberOperator_apply]
  have hcancel : numberResolventRangeEquiv.symm x + Complex.I • (x : H) -
      Complex.I • (x : H) = numberResolventRangeEquiv.symm x := by abel
  rw [hcancel]
  have heq := numberResolventRangeEquiv.apply_symm_apply x
  exact congrArg Subtype.val heq

/-- The number operator has the explicit compact two-sided resolvent at `i`. -/
theorem numberOperator_compact_resolvent :
    ∃ (R : H →L[ℂ] H) (hmem : ∀ y : H, R y ∈ numberOperator.domain),
      IsCompactOperator (R : H → H) ∧
      (∀ y : H, numberOperator ⟨R y, hmem y⟩ - Complex.I • R y = y) ∧
      (∀ x : numberOperator.domain,
        R (numberOperator x - Complex.I • (x : H)) = x) :=
  ⟨numberResolvent, numberResolvent_mem_numberOperatorDomain,
    numberResolvent_isCompactOperator, numberResolvent_right_inverse,
    numberResolvent_left_inverse⟩

end ToeplitzScreenObstruction
end NCG
