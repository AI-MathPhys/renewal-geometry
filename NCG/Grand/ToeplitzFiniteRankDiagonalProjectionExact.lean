import NCG.Grand.ToeplitzNumberOperatorShiftCommutatorExact

/-!
# Finite-rank diagonal projections are finite coordinate screens

A bounded operator diagonal on the standard `ℓ²` basis and having
finite-dimensional range has finite diagonal support.  If it is idempotent,
its diagonal coefficients are zero or one, so it is exactly the coordinate
screen associated with that finite support.
-/

noncomputable section

open scoped lp

namespace NCG
namespace ToeplitzScreenObstruction

/-- The standard basis of `ℓ²(ℕ,ℂ)` is orthonormal. -/
theorem basis_orthonormal : Orthonormal ℂ basisVector := by
  rw [orthonormal_iff_ite]
  intro i j
  simp [basisVector, lp.inner_single_left, lp.single_apply, Pi.single_apply]

/-- Indices on which a bounded operator does not kill the standard basis. -/
def diagonalSupport (P : H →L[ℂ] H) : Set ℕ :=
  {n | P (basisVector n) ≠ 0}

/-- A diagonal bounded operator with finite-dimensional range has finite
support on the standard basis. -/
theorem diagonalSupport_finite_of_finiteDimensional_range
    (P : H →L[ℂ] H)
    [FiniteDimensional ℂ (LinearMap.range P.toLinearMap)]
    (hdiag : ∀ n, P (basisVector n) =
      (P (basisVector n) n) • basisVector n) :
    (diagonalSupport P).Finite := by
  let S := diagonalSupport P
  let v : S → LinearMap.range P.toLinearMap := fun n ↦
    ⟨basisVector n, by
      let c : ℂ := P (basisVector n) n
      have hc : c ≠ 0 := by
        intro hc0
        apply n.prop
        rw [hdiag n]
        simp [c, hc0]
      refine ⟨c⁻¹ • basisVector n, ?_⟩
      rw [map_smul]
      change c⁻¹ • P (basisVector n) = basisVector n
      rw [hdiag n]
      change c⁻¹ • c • basisVector n = basisVector n
      simp [c, hc]⟩
  have hstd : LinearIndependent ℂ (fun n : S ↦ basisVector (n : ℕ)) :=
    (basis_orthonormal.comp Subtype.val Subtype.val_injective).linearIndependent
  have hv : LinearIndependent ℂ v := by
    apply LinearIndependent.of_comp (LinearMap.range P.toLinearMap).subtype
    have hvcoe :
        (LinearMap.range P.toLinearMap).subtype ∘ v =
          fun n : S ↦ basisVector (n : ℕ) := by
      funext n
      rfl
    rw [hvcoe]
    exact hstd
  letI : Finite S := hv.finite
  exact Set.toFinite S

/-- The finite support of a finite-rank diagonal bounded operator. -/
def diagonalSupportFinset
    (P : H →L[ℂ] H)
    [FiniteDimensional ℂ (LinearMap.range P.toLinearMap)]
    (hdiag : ∀ n, P (basisVector n) =
      (P (basisVector n) n) • basisVector n) : Finset ℕ :=
  (diagonalSupport_finite_of_finiteDimensional_range P hdiag).toFinset

@[simp]
theorem mem_diagonalSupportFinset
    (P : H →L[ℂ] H)
    [FiniteDimensional ℂ (LinearMap.range P.toLinearMap)]
    (hdiag : ∀ n, P (basisVector n) =
      (P (basisVector n) n) • basisVector n) (n : ℕ) :
    n ∈ diagonalSupportFinset P hdiag ↔ P (basisVector n) ≠ 0 := by
  simp [diagonalSupportFinset, diagonalSupport]

/-- An idempotent diagonal operator has only zero-one diagonal
coefficients. -/
theorem diagonalCoefficient_eq_zero_or_one_of_idempotent
    (P : H →L[ℂ] H)
    (hdiag : ∀ n, P (basisVector n) =
      (P (basisVector n) n) • basisVector n)
    (hidem : P.comp P = P) (n : ℕ) :
    P (basisVector n) n = 0 ∨ P (basisVector n) n = 1 := by
  have h := congrArg (fun T : H →L[ℂ] H ↦ T (basisVector n) n) hidem
  rw [ContinuousLinearMap.comp_apply, hdiag n, map_smul, hdiag n] at h
  simp [basisVector_apply] at h
  have hfactor : P (basisVector n) n * (P (basisVector n) n - 1) = 0 := by
    linear_combination h
  rcases mul_eq_zero.mp hfactor with hzero | hone
  · exact Or.inl hzero
  · exact Or.inr (sub_eq_zero.mp hone)

/-- A finite-rank diagonal idempotent acts on basis vectors exactly like its
finite coordinate support screen. -/
theorem diagonalIdempotent_basisVector
    (P : H →L[ℂ] H)
    [FiniteDimensional ℂ (LinearMap.range P.toLinearMap)]
    (hdiag : ∀ n, P (basisVector n) =
      (P (basisVector n) n) • basisVector n)
    (hidem : P.comp P = P) (n : ℕ) :
    P (basisVector n) =
      l2FinsetScreen (E := ℂ) (diagonalSupportFinset P hdiag)
        (basisVector n) := by
  rw [screen_basisVector]
  by_cases hn : n ∈ diagonalSupportFinset P hdiag
  · rw [if_pos hn, hdiag n]
    have hPne : P (basisVector n) ≠ 0 :=
      (mem_diagonalSupportFinset P hdiag n).mp hn
    have hcne : P (basisVector n) n ≠ 0 := by
      intro hc
      apply hPne
      rw [hdiag n]
      simp [hc]
    rcases diagonalCoefficient_eq_zero_or_one_of_idempotent P hdiag hidem n with
      hzero | hone
    · exact (hcne hzero).elim
    · simp [hone]
  · rw [if_neg hn]
    exact not_ne_iff.mp ((mem_diagonalSupportFinset P hdiag n).not.mp hn)

/-- A finite-rank diagonal idempotent is exactly a finite coordinate screen. -/
theorem diagonalIdempotent_eq_l2FinsetScreen
    (P : H →L[ℂ] H)
    [FiniteDimensional ℂ (LinearMap.range P.toLinearMap)]
    (hdiag : ∀ n, P (basisVector n) =
      (P (basisVector n) n) • basisVector n)
    (hidem : P.comp P = P) :
    P = l2FinsetScreen (E := ℂ) (diagonalSupportFinset P hdiag) := by
  apply ContinuousLinearMap.ext
  intro f
  have hsum := lp.hasSum_single (E := fun _ : ℕ ↦ ℂ)
    (p := (2 : ENNReal)) ENNReal.ofNat_ne_top f
  have hP := hsum.map P P.continuous
  have hQ := hsum.map
    (l2FinsetScreen (E := ℂ) (diagonalSupportFinset P hdiag))
    (l2FinsetScreen (E := ℂ) (diagonalSupportFinset P hdiag)).continuous
  apply hP.unique
  convert hQ using 1
  funext n
  change P (lp.single 2 n (f n)) =
    l2FinsetScreen (E := ℂ) (diagonalSupportFinset P hdiag)
      (lp.single 2 n (f n))
  have hsingle : lp.single 2 n (f n) = (f n) • basisVector n := by
    apply lp.ext
    funext j
    simp [basisVector, lp.single_apply, Pi.single_apply]
  rw [hsingle, map_smul, map_smul,
    diagonalIdempotent_basisVector P hdiag hidem n]

/-- The full Toeplitz obstruction: every nonzero finite-rank idempotent that
commutes with the number operator on the standard core has shift-commutator
norm at least one. -/
theorem one_le_norm_commutator_of_finiteRank_idempotent_commutes_numberOperator
    (P : H →L[ℂ] H)
    [FiniteDimensional ℂ (LinearMap.range P.toLinearMap)]
    (hpres : ∀ n, P (basisVector n) ∈ numberOperator.domain)
    (hcomm : ∀ n,
      numberOperator ⟨P (basisVector n), hpres n⟩ =
        P (numberOperator
          ⟨basisVector n, basisVector_mem_numberOperatorDomain n⟩))
    (hidem : P.comp P = P) (hne : P ≠ 0) :
    1 ≤ ‖P.comp unilateralShift - unilateralShift.comp P‖ := by
  have hdiag := diagonal_on_basis_of_commutes_numberOperator P hpres hcomm
  let s := diagonalSupportFinset P hdiag
  have hPeq : P = l2FinsetScreen (E := ℂ) s := by
    simpa only [s] using diagonalIdempotent_eq_l2FinsetScreen P hdiag hidem
  have hs : s.Nonempty := by
    by_contra hs0
    have hsempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs0
    apply hne
    rw [hPeq, hsempty]
    apply ContinuousLinearMap.ext
    intro f
    apply lp.ext
    funext n
    simp [l2FinsetScreen_apply]
  have hbound := one_le_norm_screenShiftCommutator s hs
  simpa only [screenShiftCommutator, ← hPeq] using hbound

end ToeplitzScreenObstruction
end NCG
