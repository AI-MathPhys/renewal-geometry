/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Skolem–Noether uniqueness for matrix algebra realizations

The abstract uniqueness input of `thm:external-core` /
`thm:projective-revision` (flagship): **any two unital algebra
realizations of the marked matrix factor inside the total factor are
conjugate**.  Mathlib has no Skolem–Noether theorem, so it is proved
here from scratch for the case the manuscript consumes
(`M_n(ℂ) → M_N(ℂ)`), by the classical matrix-unit argument:

* `isIdempotentElem_equiv_of_finrank` — two idempotent endomorphisms
  with equal-dimensional ranges are equivalent: there are `w, w'`
  with `qwp = w`, `pw'q = w'`, `ww' = q`, `w'w = p` (transport
  through a linear equivalence of the ranges);
* `matrix_idem_equiv_of_trace` — the matrix version, with the rank
  hypothesis reduced to a **trace** identity via
  `LinearMap.IsProj.trace` (over `ℂ` the trace of an idempotent is
  the dimension of its range);
* `skolem_noether` — **the uniqueness theorem**: for any two unital
  algebra homomorphisms `φ ψ : M_n(ℂ) →ₐ M_N(ℂ)` there is a unit
  `u` with `ψ(a) = u φ(a) u⁻¹` for all `a`.  The images of the
  matrix units under `φ` and `ψ` are families of orthogonal
  equivalent idempotents of equal trace `N/n`, and the intertwiner
  is the explicit sum `u = ∑ᵢ ψ(Eᵢ₀) w φ(E₀ᵢ)`.

Consequently any two realizations of the marked external Clifford
factor — in particular any irreducible one and the concrete
`γ ⊗ 1` model of `NCG/Algebra/MarkedFactor.lean` — are conjugate:
the finite Stone–von Neumann uniqueness previously listed as outside
the library.
-/

namespace NCG

open Module LinearMap

/-! ## Equivalence of idempotents of equal rank -/

/-- An idempotent fixes its range. -/
theorem IsIdempotentElem.apply_coe_range {V : Type*} [AddCommGroup V]
    [Module ℂ V] {p : Module.End ℂ V} (hp : IsIdempotentElem p)
    (z : LinearMap.range p) : p ↑z = ↑z := by
  obtain ⟨-, u, rfl⟩ := z
  change p (p u) = p u
  rw [← Module.End.mul_apply, hp]

/-- **Equivalence of idempotents of equal rank**: two idempotent
endomorphisms of a finite-dimensional space whose ranges have the
same dimension admit `w, w'` with `qwp = w`, `pw'q = w'`, `ww' = q`,
`w'w = p`. -/
theorem isIdempotentElem_equiv_of_finrank {V : Type*} [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] {p q : Module.End ℂ V}
    (hp : IsIdempotentElem p) (hq : IsIdempotentElem q)
    (hrank : finrank ℂ (LinearMap.range p)
      = finrank ℂ (LinearMap.range q)) :
    ∃ w w' : Module.End ℂ V,
      q * w * p = w ∧ p * w' * q = w' ∧ w * w' = q ∧ w' * w = p := by
  set e : LinearMap.range p ≃ₗ[ℂ] LinearMap.range q :=
    LinearEquiv.ofFinrankEq _ _ hrank with he
  set w : Module.End ℂ V :=
    (LinearMap.range q).subtype ∘ₗ e.toLinearMap ∘ₗ p.rangeRestrict
    with hw
  set w' : Module.End ℂ V :=
    (LinearMap.range p).subtype ∘ₗ e.symm.toLinearMap
      ∘ₗ q.rangeRestrict with hw'
  have hfixp := IsIdempotentElem.apply_coe_range hp
  have hfixq := IsIdempotentElem.apply_coe_range hq
  have hrrp : ∀ z : LinearMap.range p, p.rangeRestrict ↑z = z := by
    intro z
    exact Subtype.ext (by simp [hfixp z])
  have hrrq : ∀ z : LinearMap.range q, q.rangeRestrict ↑z = z := by
    intro z
    exact Subtype.ext (by simp [hfixq z])
  have hqw : q * w = w := by
    ext v
    change q (w v) = w v
    rw [hw]
    exact hfixq _
  have hwp : w * p = w := by
    ext v
    change w (p v) = w v
    rw [hw]
    simp only [LinearMap.coe_comp, Function.comp_apply]
    congr 2
    exact Subtype.ext (by
      simp only [LinearMap.codRestrict_apply]
      rw [← Module.End.mul_apply, hp])
  have hpw' : p * w' = w' := by
    ext v
    change p (w' v) = w' v
    rw [hw']
    exact hfixp _
  have hw'q : w' * q = w' := by
    ext v
    change w' (q v) = w' v
    rw [hw']
    simp only [LinearMap.coe_comp, Function.comp_apply]
    congr 2
    exact Subtype.ext (by
      simp only [LinearMap.codRestrict_apply]
      rw [← Module.End.mul_apply, hq])
  refine ⟨w, w', ?_, ?_, ?_, ?_⟩
  · rw [mul_assoc, hwp, hqw]
  · rw [mul_assoc, hw'q, hpw']
  · ext v
    change w (w' v) = q v
    rw [hw, hw']
    simp only [LinearMap.coe_comp, Function.comp_apply,
      Submodule.coe_subtype, LinearEquiv.coe_toLinearMap]
    rw [hrrp (e.symm (q.rangeRestrict v)),
      LinearEquiv.apply_symm_apply]
    simp
  · ext v
    change w' (w v) = p v
    rw [hw, hw']
    simp only [LinearMap.coe_comp, Function.comp_apply,
      Submodule.coe_subtype, LinearEquiv.coe_toLinearMap]
    rw [hrrq (e (p.rangeRestrict v)),
      LinearEquiv.symm_apply_apply]
    simp

/-! ## The matrix version via traces -/

/-- Over `ℂ` the trace of an idempotent matrix is the dimension of
its range. -/
theorem trace_isIdempotentElem {N : ℕ}
    {P : Matrix (Fin N) (Fin N) ℂ} (hP : P * P = P) :
    P.trace = (finrank ℂ
      (LinearMap.range (Matrix.toLin' P)) : ℂ) := by
  have hidem : IsIdempotentElem (Matrix.toLin' P) := by
    change Matrix.toLin' P * Matrix.toLin' P = Matrix.toLin' P
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hP]
  have htr := (IsIdempotentElem.isProj_range _ hidem).trace
  have hmat : LinearMap.trace ℂ (Fin N → ℂ) (Matrix.toLin' P)
      = P.trace := by
    rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin N))]
    congr 1
    rw [LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']
  rw [← hmat, htr]

/-- **Matrix idempotents with equal traces are equivalent.** -/
theorem matrix_idem_equiv_of_trace {N : ℕ}
    {P Q : Matrix (Fin N) (Fin N) ℂ}
    (hP : P * P = P) (hQ : Q * Q = Q) (htr : P.trace = Q.trace) :
    ∃ w w' : Matrix (Fin N) (Fin N) ℂ,
      Q * w * P = w ∧ P * w' * Q = w' ∧ w * w' = Q ∧ w' * w = P := by
  have hrank : finrank ℂ (LinearMap.range (Matrix.toLin' P))
      = finrank ℂ (LinearMap.range (Matrix.toLin' Q)) := by
    have h1 := trace_isIdempotentElem hP
    have h2 := trace_isIdempotentElem hQ
    rw [h1, h2] at htr
    exact_mod_cast htr
  -- transfer through the algebra equivalence with endomorphisms
  set Ψ : Matrix (Fin N) (Fin N) ℂ ≃ₐ[ℂ]
      ((Fin N → ℂ) →ₗ[ℂ] (Fin N → ℂ)) :=
    Matrix.toLinAlgEquiv' with hΨ
  have hΨP : Ψ P = Matrix.toLin' P := rfl
  have hΨQ : Ψ Q = Matrix.toLin' Q := rfl
  have hidemP : IsIdempotentElem (Ψ P) := by
    change Ψ P * Ψ P = Ψ P
    rw [← map_mul, hP]
  have hidemQ : IsIdempotentElem (Ψ Q) := by
    change Ψ Q * Ψ Q = Ψ Q
    rw [← map_mul, hQ]
  obtain ⟨w, w', h1, h2, h3, h4⟩ :=
    isIdempotentElem_equiv_of_finrank hidemP hidemQ
      (by rw [hΨP, hΨQ]; exact hrank)
  refine ⟨Ψ.symm w, Ψ.symm w', ?_, ?_, ?_, ?_⟩
  · have h := congrArg Ψ.symm h1
    rwa [map_mul, map_mul, AlgEquiv.symm_apply_apply,
      AlgEquiv.symm_apply_apply] at h
  · have h := congrArg Ψ.symm h2
    rwa [map_mul, map_mul, AlgEquiv.symm_apply_apply,
      AlgEquiv.symm_apply_apply] at h
  · have h := congrArg Ψ.symm h3
    rwa [map_mul, AlgEquiv.symm_apply_apply] at h
  · have h := congrArg Ψ.symm h4
    rwa [map_mul, AlgEquiv.symm_apply_apply] at h

/-! ## The Skolem–Noether theorem -/

/-- The diagonal matrix units sum to the identity. -/
theorem sum_single_diag_eq_one {n : ℕ} :
    (∑ i : Fin n, Matrix.single i i (1:ℂ)) = 1 := by
  ext a b
  rw [Matrix.sum_apply]
  by_cases hab : a = b
  · subst hab
    simp [Matrix.single_apply]
  · simp [Matrix.single_apply, hab]

/-- **The Skolem–Noether theorem for complex matrix algebras**
(finite Stone–von Neumann uniqueness): any two unital algebra
homomorphisms `M_n(ℂ) →ₐ M_N(ℂ)` are conjugate by a unit. -/
theorem skolem_noether {n N : ℕ} [NeZero n]
    (φ ψ : Matrix (Fin n) (Fin n) ℂ →ₐ[ℂ] Matrix (Fin N) (Fin N) ℂ) :
    ∃ u : (Matrix (Fin N) (Fin N) ℂ)ˣ,
      ∀ a, ψ a = (u : Matrix (Fin N) (Fin N) ℂ) * φ a
        * ((u⁻¹ : (Matrix (Fin N) (Fin N) ℂ)ˣ)
          : Matrix (Fin N) (Fin N) ℂ) := by
  classical
  set E : Fin n → Fin n → Matrix (Fin n) (Fin n) ℂ :=
    fun i j => Matrix.single i j 1 with hE
  have hEmul : ∀ i j k l,
      E i j * E k l = if j = k then E i l else 0 := by
    intro i j k l
    simp only [hE]
    by_cases hjk : j = k
    · subst hjk
      rw [if_pos rfl, Matrix.single_mul_single_same, one_mul]
    · have h0 : Matrix.single i j (1:ℂ) * Matrix.single k l (1:ℂ)
          = 0 :=
        Matrix.single_mul_single_of_ne (c := (1:ℂ)) i j k hjk 1
      rw [if_neg hjk, h0]
  have hEsum : (∑ i, E i i) = 1 := sum_single_diag_eq_one
  -- the two idempotents
  have hPidem : φ (E 0 0) * φ (E 0 0) = φ (E 0 0) := by
    rw [← map_mul, hEmul]
    simp
  have hQidem : ψ (E 0 0) * ψ (E 0 0) = ψ (E 0 0) := by
    rw [← map_mul, hEmul]
    simp
  -- all diagonal images share one trace, and `n` copies make `N`
  have htr_all : ∀ (χ : Matrix (Fin n) (Fin n) ℂ →ₐ[ℂ]
      Matrix (Fin N) (Fin N) ℂ) (i : Fin n),
      (χ (E i i)).trace = (χ (E 0 0)).trace := by
    intro χ i
    have h1 : E i i = E i 0 * E 0 i := by rw [hEmul]; simp
    have h2 : E 0 0 = E 0 i * E i 0 := by rw [hEmul]; simp
    rw [h1, map_mul, Matrix.trace_mul_comm, ← map_mul, ← h2]
  have htotal : ∀ (χ : Matrix (Fin n) (Fin n) ℂ →ₐ[ℂ]
      Matrix (Fin N) (Fin N) ℂ),
      (n : ℂ) * (χ (E 0 0)).trace = (N : ℂ) := by
    intro χ
    have h1 : (∑ i, χ (E i i)) = 1 := by
      rw [← map_sum, hEsum, map_one]
    have h2 := congrArg Matrix.trace h1
    rw [Matrix.trace_sum, Matrix.trace_one] at h2
    calc (n : ℂ) * (χ (E 0 0)).trace
        = ∑ _i : Fin n, (χ (E 0 0)).trace := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
      _ = ∑ i : Fin n, (χ (E i i)).trace :=
          Finset.sum_congr rfl fun i _ => (htr_all χ i).symm
      _ = (N : ℂ) := by
          rw [h2]
          simp
  have htrPQ : (φ (E 0 0)).trace = (ψ (E 0 0)).trace := by
    have hn : (n : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (NeZero.ne n)
    exact mul_left_cancel₀ hn ((htotal φ).trans (htotal ψ).symm)
  -- the equivalence data for the two idempotents
  obtain ⟨w, w', hw1, hw2, hw3, hw4⟩ :=
    matrix_idem_equiv_of_trace hPidem hQidem htrPQ
  -- absorption identities
  have hwP : w * φ (E 0 0) = w := by
    conv_lhs => rw [← hw1]
    rw [mul_assoc (ψ (E 0 0) * w), hPidem, hw1]
  have hw'Q : w' * ψ (E 0 0) = w' := by
    conv_lhs => rw [← hw2]
    rw [mul_assoc (φ (E 0 0) * w'), hQidem, hw2]
  have habs : w * φ (E 0 0) * w' = ψ (E 0 0) := by
    rw [hwP, hw3]
  have habs' : w' * ψ (E 0 0) * w = φ (E 0 0) := by
    rw [hw'Q, hw4]
  -- the intertwiner and its inverse
  set u : Matrix (Fin N) (Fin N) ℂ :=
    ∑ i, ψ (E i 0) * w * φ (E 0 i) with hu
  set u' : Matrix (Fin N) (Fin N) ℂ :=
    ∑ i, φ (E i 0) * w' * ψ (E 0 i) with hu'
  -- intertwining on the matrix units
  have hint : ∀ j k, u * φ (E j k) = ψ (E j k) * u := by
    intro j k
    rw [hu, Finset.sum_mul, Finset.mul_sum]
    have hL : ∀ i, ψ (E i 0) * w * φ (E 0 i) * φ (E j k)
        = if i = j then ψ (E j 0) * w * φ (E 0 k) else 0 := by
      intro i
      rw [mul_assoc (ψ (E i 0) * w), ← map_mul, hEmul]
      by_cases hij : i = j
      · subst hij
        simp
      · simp [hij]
    have hR : ∀ i, ψ (E j k) * (ψ (E i 0) * w * φ (E 0 i))
        = if i = k then ψ (E j 0) * w * φ (E 0 k) else 0 := by
      intro i
      rw [← mul_assoc, ← mul_assoc, ← map_mul, hEmul]
      by_cases hik : k = i
      · subst hik
        simp
      · rw [if_neg hik]
        simp [Ne.symm hik]
    rw [Finset.sum_congr rfl fun i _ => hL i,
      Finset.sum_congr rfl fun i _ => hR i]
    simp
  -- intertwining everywhere by linearity
  have hintAll : ∀ a, u * φ a = ψ a * u := by
    intro a
    induction a using Matrix.induction_on' with
    | h_zero => simp
    | h_add p q hp hq => rw [map_add, map_add, mul_add, add_mul,
        hp, hq]
    | h_std_basis i j x =>
      have hxsm : Matrix.single i j x = x • E i j := by
        rw [hE, Matrix.smul_single, smul_eq_mul, mul_one]
      rw [hxsm, map_smul, map_smul, mul_smul_comm, smul_mul_assoc,
        hint i j]
  -- `u` and `u'` are mutually inverse
  have hterm : ∀ i j,
      (ψ (E i 0) * w * φ (E 0 i)) * (φ (E j 0) * w' * ψ (E 0 j))
      = if i = j then ψ (E i i) else 0 := by
    intro i j
    have hgrp : (ψ (E i 0) * w * φ (E 0 i))
          * (φ (E j 0) * w' * ψ (E 0 j))
        = ψ (E i 0) * w * (φ (E 0 i) * φ (E j 0))
          * w' * ψ (E 0 j) := by
      noncomm_ring
    rw [hgrp, ← map_mul, hEmul]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, if_pos rfl]
      have hmid : ψ (E i 0) * w * φ (E 0 0) * w' * ψ (E 0 i)
          = ψ (E i 0) * (w * φ (E 0 0) * w') * ψ (E 0 i) := by
        noncomm_ring
      rw [hmid, habs, ← map_mul, ← map_mul, hEmul]
      rw [if_pos rfl, hEmul, if_pos rfl]
    · rw [if_neg hij, if_neg hij]
      simp
  have hterm' : ∀ i j,
      (φ (E i 0) * w' * ψ (E 0 i)) * (ψ (E j 0) * w * φ (E 0 j))
      = if i = j then φ (E i i) else 0 := by
    intro i j
    have hgrp : (φ (E i 0) * w' * ψ (E 0 i))
          * (ψ (E j 0) * w * φ (E 0 j))
        = φ (E i 0) * w' * (ψ (E 0 i) * ψ (E j 0))
          * w * φ (E 0 j) := by
      noncomm_ring
    rw [hgrp, ← map_mul, hEmul]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, if_pos rfl]
      have hmid : φ (E i 0) * w' * ψ (E 0 0) * w * φ (E 0 i)
          = φ (E i 0) * (w' * ψ (E 0 0) * w) * φ (E 0 i) := by
        noncomm_ring
      rw [hmid, habs', ← map_mul, ← map_mul, hEmul]
      rw [if_pos rfl, hEmul, if_pos rfl]
    · rw [if_neg hij, if_neg hij]
      simp
  have huu' : u * u' = 1 := by
    rw [hu, hu', Finset.sum_mul_sum]
    rw [Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => hterm i j]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [← map_sum, hEsum, map_one]
  have hu'u : u' * u = 1 := by
    rw [hu, hu', Finset.sum_mul_sum]
    rw [Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => hterm' i j]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [← map_sum, hEsum, map_one]
  -- package as a unit
  refine ⟨⟨u, u', huu', hu'u⟩, fun a => ?_⟩
  change ψ a = u * φ a * u'
  calc ψ a = ψ a * (u * u') := by rw [huu', mul_one]
    _ = ψ a * u * u' := by rw [mul_assoc]
    _ = u * φ a * u' := by rw [← hintAll a]

/-- Intertwiner form of Skolem–Noether: `u φ(a) = ψ(a) u`. -/
theorem skolem_noether_intertwine {n N : ℕ} [NeZero n]
    (φ ψ : Matrix (Fin n) (Fin n) ℂ →ₐ[ℂ] Matrix (Fin N) (Fin N) ℂ) :
    ∃ u : (Matrix (Fin N) (Fin N) ℂ)ˣ,
      ∀ a, (u : Matrix (Fin N) (Fin N) ℂ) * φ a
        = ψ a * (u : Matrix (Fin N) (Fin N) ℂ) := by
  obtain ⟨u, hu⟩ := skolem_noether φ ψ
  refine ⟨u, fun a => ?_⟩
  rw [hu a, mul_assoc, mul_assoc]
  congr 1
  rw [Units.inv_mul, mul_one]

end NCG
