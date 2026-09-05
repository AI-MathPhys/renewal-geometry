/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.UnitaryConjugationIrreducible

/-!
# Schur uniqueness for conjugation-covariant operators

Machinery for `thm:SM-colour-orbit`: a linear operator on `Matrix n n ℂ` that is
covariant under every unitary conjugation and preserves tracelessness acts as a
scalar on the traceless block (`covariant_traceless_scalar`) and as a scalar on the
identity line (`covariant_one_scalar`), hence decomposes exactly as
`c·Π₁ + λ·Π_ad` (`covariant_operator_decomposes`) — the uniqueness half of the
boxed Haar-covariance identity `∫ |URU*⟩⟨URU*| dU = Π₁ + (1/5)Π₁₅`.

* `central_of_unitary_comm`: the commutant of the unitary group is the scalar line;
* `covariant_traceless_scalar`: an eigenvalue of the restricted operator exists over
  `ℂ`; its eigenspace is conjugation-invariant and contains a non-scalar element, so
  by `NCG.ConjIrreducible.traceless_le_of_nonscalar` it is the whole traceless block.
-/

open Finset Matrix NCG.ConjIrreducible

namespace NCG
namespace SchurCovariant

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The commutant of the unitary group consists of the scalar matrices. -/
theorem central_of_unitary_comm [Nonempty n] {B : Matrix n n ℂ}
    (h : ∀ U ∈ Matrix.unitaryGroup n ℂ, U * B = B * U) :
    ∃ c : ℂ, B = c • 1 := by
  have hoff : ∀ i l : n, i ≠ l → B i l = 0 := by
    intro i l hil
    have h1 := h (phase i (-1)) (phase_mem i (by simp))
    have h2 := congrFun (congrFun h1 i) l
    rw [phase, Matrix.diagonal_mul, Matrix.mul_diagonal, if_pos rfl,
      if_neg (Ne.symm hil)] at h2
    linear_combination (-(2⁻¹ : ℂ)) * h2
  have hdiag : ∀ i j : n, B i i = B j j := by
    intro i j
    by_cases hij : i = j
    · rw [hij]
    · have h1 := h (Matrix.swap ℂ i j) (swap_mem i j)
      have h2 : Matrix.swap ℂ i j * B * Matrix.swap ℂ i j = B := by
        rw [h1, Matrix.mul_assoc, Matrix.swap_mul_self, Matrix.mul_one]
      have h3 := congrFun (congrFun h2 i) i
      rw [swap_conj_apply, Equiv.swap_apply_left] at h3
      exact h3.symm
  obtain ⟨x⟩ := (inferInstance : Nonempty n)
  refine ⟨B x x, ?_⟩
  ext k l
  by_cases hkl : k = l
  · rw [hkl, Matrix.smul_apply, Matrix.one_apply_eq, hdiag l x, smul_eq_mul, mul_one]
  · rw [hoff k l hkl, Matrix.smul_apply, Matrix.one_apply_ne hkl, smul_zero]

/-- A conjugation-covariant operator is scalar on the identity line. -/
theorem covariant_one_scalar [Nonempty n] (T : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ)
    (hcov : ∀ U ∈ Matrix.unitaryGroup n ℂ, ∀ A, T (U * A * star U) = U * T A * star U) :
    ∃ c : ℂ, T 1 = c • 1 := by
  refine central_of_unitary_comm fun U hU => ?_
  have hUU : U * star U = 1 := Matrix.mem_unitaryGroup_iff.mp hU
  have h1 : T 1 = U * T 1 * star U := by
    conv_lhs => rw [show (1 : Matrix n n ℂ) = U * 1 * star U by
      rw [Matrix.mul_one, hUU]]
    rw [hcov U hU 1]
  calc U * T 1 = U * T 1 * (star U * U) := by
        rw [Matrix.mem_unitaryGroup_iff'.mp hU, Matrix.mul_one]
    _ = (U * T 1 * star U) * U := by
        rw [← Matrix.mul_assoc]
    _ = T 1 * U := by rw [← h1]

/-- A nonzero traceless matrix has a non-scalar witness pair. -/
theorem exists_nonscalar_witness [Nonempty n] {v : Matrix n n ℂ} (hv0 : v ≠ 0)
    (htr : Matrix.trace v = 0) :
    ∃ k l, k ≠ l ∧ (v k l ≠ 0 ∨ v k k ≠ v l l) := by
  by_contra hcon
  have hall : ∀ k l : n, k ≠ l → v k l = 0 ∧ v k k = v l l := by
    intro k l hkl
    constructor
    · by_contra hne
      exact hcon ⟨k, l, hkl, Or.inl hne⟩
    · by_contra hne
      exact hcon ⟨k, l, hkl, Or.inr hne⟩
  obtain ⟨x⟩ := (inferInstance : Nonempty n)
  have hdiagall : ∀ k : n, v k k = v x x := by
    intro k
    by_cases hk : k = x
    · rw [hk]
    · exact (hall k x hk).2
  have htr' : (Fintype.card n : ℂ) * v x x = 0 := by
    calc (Fintype.card n : ℂ) * v x x = ∑ _k : n, v x x := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      _ = ∑ k, v k k := Finset.sum_congr rfl fun k _ => (hdiagall k).symm
      _ = Matrix.trace v := rfl
      _ = 0 := htr
  have hc : v x x = 0 := by
    rcases mul_eq_zero.mp htr' with h | h
    · exact absurd h (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
    · exact h
  refine hv0 ?_
  ext k l
  rw [Matrix.zero_apply]
  by_cases hkl : k = l
  · rw [hkl, hdiagall l, hc]
  · exact (hall k l hkl).1

/-- **Schur uniqueness on the traceless block**: a conjugation-covariant operator
preserving tracelessness is a scalar on every traceless matrix. -/
theorem covariant_traceless_scalar [Nontrivial n]
    (T : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ)
    (hcov : ∀ U ∈ Matrix.unitaryGroup n ℂ, ∀ A, T (U * A * star U) = U * T A * star U)
    (hsl : ∀ A : Matrix n n ℂ, Matrix.trace A = 0 → Matrix.trace (T A) = 0) :
    ∃ lam : ℂ, ∀ A : Matrix n n ℂ, Matrix.trace A = 0 → T A = lam • A := by
  classical
  set sl : Submodule ℂ (Matrix n n ℂ) := LinearMap.ker (Matrix.traceLinearMap n ℂ ℂ)
    with hsldef
  have hmem_sl : ∀ A : Matrix n n ℂ, A ∈ sl ↔ Matrix.trace A = 0 := by
    intro A
    rw [hsldef, LinearMap.mem_ker]
    rfl
  have hmaps : ∀ x ∈ sl, T x ∈ sl := fun x hx =>
    (hmem_sl _).mpr (hsl x ((hmem_sl _).mp hx))
  have hsl_nontrivial : Nontrivial sl := by
    obtain ⟨x, y, hxy⟩ := exists_pair_ne n
    have hmem : Matrix.single x y (1 : ℂ) ∈ sl := by
      rw [hmem_sl]
      calc Matrix.trace (Matrix.single x y (1 : ℂ))
          = ∑ k, Matrix.single x y (1 : ℂ) k k := rfl
        _ = 0 := Finset.sum_eq_zero fun k _ => by
            rw [Matrix.single_apply, if_neg (fun hcon => hxy (hcon.1.trans hcon.2.symm))]
    refine ⟨⟨⟨Matrix.single x y 1, hmem⟩, 0, fun hcon => ?_⟩⟩
    have h1 : Matrix.single x y (1 : ℂ) = 0 := (Submodule.mk_eq_zero _ _).mp hcon
    have h2 := congrFun (congrFun h1 x) y
    rw [Matrix.single_apply_same, Matrix.zero_apply] at h2
    exact one_ne_zero h2
  haveI := hsl_nontrivial
  obtain ⟨lam, hlam⟩ := Module.End.exists_eigenvalue (T.restrict hmaps)
  obtain ⟨v, hv⟩ := hlam.exists_hasEigenvector
  have hveq : T v.1 = lam • v.1 := by
    have h1 := congrArg Subtype.val hv.apply_eq_smul
    rwa [LinearMap.coe_restrict_apply, Submodule.coe_smul] at h1
  set W : Submodule ℂ (Matrix n n ℂ) := LinearMap.ker (T - lam • LinearMap.id) ⊓ sl
    with hWdef
  have hWinv : ConjInvariant W := by
    intro U hU A hA
    obtain ⟨hA1, hA2⟩ := Submodule.mem_inf.mp hA
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, sub_eq_zero] at hA1
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.id_apply, sub_eq_zero, hcov U hU A, hA1, Matrix.mul_smul,
        Matrix.smul_mul]
    · rw [hmem_sl] at hA2 ⊢
      rw [Matrix.trace_mul_cycle, Matrix.mem_unitaryGroup_iff'.mp hU,
        Matrix.one_mul, hA2]
  have hvW : v.1 ∈ W := by
    refine Submodule.mem_inf.mpr ⟨?_, v.2⟩
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, hveq, sub_self]
  have hv0 : (v : Matrix n n ℂ) ≠ 0 := fun h =>
    hv.2 (Submodule.coe_eq_zero.mp h)
  obtain ⟨k, l, hkl, hcase⟩ :=
    exists_nonscalar_witness hv0 ((hmem_sl _).mp v.2)
  have hall := traceless_le_of_nonscalar hWinv hvW ⟨k, l, hkl, hcase⟩
  refine ⟨lam, fun A hA => ?_⟩
  have hAW := (Submodule.mem_inf.mp (hall A hA)).1
  rwa [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero] at hAW

/-- **Schur decomposition of a covariant operator**: `T = c·Π₁ + λ·Π_ad` exactly. -/
theorem covariant_operator_decomposes [Nontrivial n]
    (T : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ)
    (hcov : ∀ U ∈ Matrix.unitaryGroup n ℂ, ∀ A, T (U * A * star U) = U * T A * star U)
    (hsl : ∀ A : Matrix n n ℂ, Matrix.trace A = 0 → Matrix.trace (T A) = 0) :
    ∃ c lam : ℂ, ∀ A : Matrix n n ℂ,
      T A = (c * (Matrix.trace A / (Fintype.card n : ℂ))) • 1
        + lam • (A - (Matrix.trace A / (Fintype.card n : ℂ)) • 1) := by
  obtain ⟨c, hc⟩ := covariant_one_scalar T hcov
  obtain ⟨lam, hlam⟩ := covariant_traceless_scalar T hcov hsl
  refine ⟨c, lam, fun A => ?_⟩
  have hcard : (Fintype.card n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  set s : ℂ := Matrix.trace A / (Fintype.card n : ℂ) with hs
  have htr0 : Matrix.trace (A - s • 1) = 0 := by
    rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul, hs]
    field_simp
    ring
  have hsplit : A = s • 1 + (A - s • 1) := by
    rw [add_sub_cancel]
  calc T A = T (s • 1 + (A - s • 1)) := by rw [← hsplit]
    _ = s • T 1 + T (A - s • 1) := by rw [map_add, map_smul]
    _ = s • (c • 1) + lam • (A - s • 1) := by rw [hc, hlam _ htr0]
    _ = (c * s) • 1 + lam • (A - s • 1) := by
        rw [smul_smul, mul_comm]

end SchurCovariant
end NCG
