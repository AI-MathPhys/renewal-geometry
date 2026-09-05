/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.StoreBlockDecomposition

/-!
# The commutant of assembled Pauli Store blocks

This file supplies the multiplicity-space assembly missing from the elementary
single-block calculation in `StoreBlockDecomposition`.  Distinct positive
frequencies are indexed by `j`; the carrier of block `j` is an arbitrary finite
type `M j`.  The theorem identifies the simultaneous commutant of
`sigma_z ⊗ I` and `mu_j sigma_x ⊗ I` exactly.
-/

open Matrix

namespace NCG
namespace PauliStoreBlockCommutant

abbrev MultiplicityIndex (J : Type*) (M : J → Type*) := Σ j, M j

abbrev StoreIndex (J : Type*) (M : J → Type*) :=
  Bool × MultiplicityIndex J M

def pauliSign : Bool → ℂ
  | false => 1
  | true => -1

def flipStoreIndex {J : Type*} {M : J → Type*}
    (i : StoreIndex J M) : StoreIndex J M := (!i.1, i.2)

@[simp] theorem flipStoreIndex_involutive {J : Type*} {M : J → Type*}
    (i : StoreIndex J M) : flipStoreIndex (flipStoreIndex i) = i := by
  cases i with
  | mk b a => cases b <;> rfl

/-- The assembled grading `sigma_z ⊗ I`. -/
def storeGrading {J : Type*} {M : J → Type*}
    [DecidableEq (StoreIndex J M)] :
    Matrix (StoreIndex J M) (StoreIndex J M) ℂ :=
  Matrix.diagonal fun i => pauliSign i.1

/-- The assembled dwell operator `mu_j sigma_x ⊗ I`. -/
def storeDwell {J : Type*} {M : J → Type*}
    [DecidableEq (StoreIndex J M)]
    (mu : J → ℝ) : Matrix (StoreIndex J M) (StoreIndex J M) ℂ :=
  fun i k => if k = flipStoreIndex i then (mu i.2.1 : ℂ) else 0

/-- An arbitrary element of `⊕_j (I_2 ⊗ B(M_j))`, written entrywise. -/
def multiplicityOperator {J : Type*} {M : J → Type*}
    [DecidableEq J]
    (K : Matrix (MultiplicityIndex J M) (MultiplicityIndex J M) ℂ) :
    Matrix (StoreIndex J M) (StoreIndex J M) ℂ :=
  fun i k => if i.1 = k.1 ∧ i.2.1 = k.2.1 then K i.2 k.2 else 0

theorem storeGrading_mul_apply
    {J : Type*} {M : J → Type*}
    [Fintype (StoreIndex J M)] [DecidableEq (StoreIndex J M)]
    (R : Matrix (StoreIndex J M) (StoreIndex J M) ℂ)
    (i k : StoreIndex J M) :
    ((storeGrading (J := J) (M := M)) * R) i k =
      pauliSign i.1 * R i k := by
  simp [storeGrading, Matrix.diagonal_mul]

theorem mul_storeGrading_apply
    {J : Type*} {M : J → Type*}
    [Fintype (StoreIndex J M)] [DecidableEq (StoreIndex J M)]
    (R : Matrix (StoreIndex J M) (StoreIndex J M) ℂ)
    (i k : StoreIndex J M) :
    (R * (storeGrading (J := J) (M := M))) i k =
      R i k * pauliSign k.1 := by
  simp [storeGrading, Matrix.mul_diagonal]

theorem storeDwell_mul_apply
    {J : Type*} {M : J → Type*}
    [Fintype (StoreIndex J M)] [DecidableEq (StoreIndex J M)]
    (mu : J → ℝ)
    (R : Matrix (StoreIndex J M) (StoreIndex J M) ℂ)
    (i k : StoreIndex J M) :
    ((storeDwell (M := M) mu) * R) i k =
      (mu i.2.1 : ℂ) * R (flipStoreIndex i) k := by
  classical
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (flipStoreIndex i)]
  · simp [storeDwell]
  · intro b _ hb
    simp [storeDwell, hb]
  · intro hmem
    exact absurd (Finset.mem_univ (flipStoreIndex i)) hmem

theorem mul_storeDwell_apply
    {J : Type*} {M : J → Type*}
    [Fintype (StoreIndex J M)] [DecidableEq (StoreIndex J M)]
    (mu : J → ℝ)
    (R : Matrix (StoreIndex J M) (StoreIndex J M) ℂ)
    (i k : StoreIndex J M) :
    (R * (storeDwell (M := M) mu)) i k =
      R i (flipStoreIndex k) * (mu k.2.1 : ℂ) := by
  classical
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (flipStoreIndex k)]
  · change R i (flipStoreIndex k) *
        (if k = flipStoreIndex (flipStoreIndex k)
          then (mu (flipStoreIndex k).2.1 : ℂ) else 0) =
      R i (flipStoreIndex k) * (mu k.2.1 : ℂ)
    rw [if_pos (flipStoreIndex_involutive k).symm]
    rfl
  · intro b _ hb
    have hne : k ≠ flipStoreIndex b := by
      intro h
      apply hb
      have hh := congrArg flipStoreIndex h
      simpa using hh.symm
    simp [storeDwell, hne]
  · intro hmem
    exact absurd (Finset.mem_univ (flipStoreIndex k)) hmem

/-- Commutation with the grading kills the two Pauli-off-diagonal corners. -/
theorem grading_commutant_offDiagonal_zero
    {J : Type*} {M : J → Type*}
    [Fintype (StoreIndex J M)] [DecidableEq (StoreIndex J M)]
    (R : Matrix (StoreIndex J M) (StoreIndex J M) ℂ)
    (hR : R * (storeGrading (J := J) (M := M)) =
      (storeGrading (J := J) (M := M)) * R)
    (i k : StoreIndex J M) (hparity : i.1 ≠ k.1) :
    R i k = 0 := by
  have h := congrFun (congrFun hR i) k
  rw [mul_storeGrading_apply, storeGrading_mul_apply] at h
  cases hi : i.1 <;> cases hk : k.1 <;> simp [hi, hk, pauliSign] at hparity h
  all_goals
    have hs : R i k = -R i k := by first | exact h | exact h.symm
    have htwo : (2 : ℂ) * R i k = 0 := by
      simpa [two_mul] using (eq_neg_iff_add_eq_zero.mp hs)
    exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- The two diagonal Pauli corners satisfy the two singular-frequency
intertwining equations. -/
theorem dwell_commutant_diagonal_relations
    {J : Type*} {M : J → Type*}
    [Fintype (StoreIndex J M)] [DecidableEq (StoreIndex J M)]
    (mu : J → ℝ)
    (R : Matrix (StoreIndex J M) (StoreIndex J M) ℂ)
    (hR : R * storeDwell (M := M) mu = storeDwell (M := M) mu * R)
    (a b : MultiplicityIndex J M) :
    (mu a.1 : ℂ) * R (true, a) (true, b) =
        R (false, a) (false, b) * (mu b.1 : ℂ)
      ∧
    (mu a.1 : ℂ) * R (false, a) (false, b) =
        R (true, a) (true, b) * (mu b.1 : ℂ) := by
  constructor
  · have h := congrFun (congrFun hR (false, a)) (true, b)
    rw [mul_storeDwell_apply, storeDwell_mul_apply] at h
    simpa [flipStoreIndex] using h.symm
  · have h := congrFun (congrFun hR (true, a)) (false, b)
    rw [mul_storeDwell_apply, storeDwell_mul_apply] at h
    simpa [flipStoreIndex] using h.symm

/-- For distinct nonzero squared frequencies, the joint commutant is exactly
the direct sum of arbitrary multiplicity operators, copied identically into
the two Pauli coordinates.  This is the entrywise content of
`{sigma_z⊗I, ⊕_j mu_j sigma_x⊗I}' = ⊕_j I_2⊗B(M_j)`. -/
theorem joint_commutant_eq_multiplicity_operators
    {J : Type*} {M : J → Type*}
    [Fintype (StoreIndex J M)] [DecidableEq (StoreIndex J M)]
    [DecidableEq J]
    (mu : J → ℝ) (hmu0 : ∀ j, mu j ≠ 0)
    (hmuSq : Function.Injective fun j => (mu j : ℂ) ^ 2)
    (R : Matrix (StoreIndex J M) (StoreIndex J M) ℂ) :
    (R * storeGrading (J := J) (M := M) =
        storeGrading (J := J) (M := M) * R
      ∧ R * storeDwell (M := M) mu = storeDwell (M := M) mu * R) ↔
      ∃ K : Matrix (MultiplicityIndex J M) (MultiplicityIndex J M) ℂ,
        R = multiplicityOperator K := by
  constructor
  · rintro ⟨hZ, hL⟩
    let K : Matrix (MultiplicityIndex J M) (MultiplicityIndex J M) ℂ :=
      fun a b => R (false, a) (false, b)
    refine ⟨K, ?_⟩
    ext i k
    obtain ⟨si, a⟩ := i
    obtain ⟨sk, b⟩ := k
    by_cases hp : si = sk
    · subst sk
      by_cases hj : a.1 = b.1
      · cases si
        · simp [multiplicityOperator, K, hj]
        · have hrel := (dwell_commutant_diagonal_relations mu R hL a b).1
          have hm : mu a.1 = mu b.1 := congrArg mu hj
          have hca : (mu a.1 : ℂ) ≠ 0 := by exact_mod_cast hmu0 a.1
          have heq : R (true, a) (true, b) = R (false, a) (false, b) := by
            apply (mul_left_cancel₀ hca)
            rw [hrel, hm]
            ring
          simp [multiplicityOperator, K, hj, heq]
      · have hrel := dwell_commutant_diagonal_relations mu R hL a b
        let ca : ℂ := mu a.1
        let cb : ℂ := mu b.1
        have hsq : ca ^ 2 ≠ cb ^ 2 := by
          intro h
          exact hj (hmuSq h)
        have hB : R (true, a) (true, b) = 0 := by
          have hprod : (ca ^ 2 - cb ^ 2) * R (true, a) (true, b) = 0 := by
            calc
              (ca ^ 2 - cb ^ 2) * R (true, a) (true, b) =
                  ca ^ 2 * R (true, a) (true, b) -
                    cb ^ 2 * R (true, a) (true, b) := by ring
              _ = 0 := by
                dsimp only [ca, cb]
                rw [show (mu a.1 : ℂ) ^ 2 * R (true, a) (true, b) =
                    (mu b.1 : ℂ) ^ 2 * R (true, a) (true, b) by
                  calc
                    (mu a.1 : ℂ) ^ 2 * R (true, a) (true, b) =
                        (mu a.1 : ℂ) *
                          ((mu a.1 : ℂ) * R (true, a) (true, b)) := by ring
                    _ = (mu a.1 : ℂ) *
                          (R (false, a) (false, b) * (mu b.1 : ℂ)) := by
                            rw [hrel.1]
                    _ = ((mu a.1 : ℂ) * R (false, a) (false, b)) *
                          (mu b.1 : ℂ) := by ring
                    _ = (R (true, a) (true, b) * (mu b.1 : ℂ)) *
                          (mu b.1 : ℂ) := by rw [hrel.2]
                    _ = (mu b.1 : ℂ) ^ 2 * R (true, a) (true, b) := by ring]
                ring
          exact (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr hsq)
        have hA : R (false, a) (false, b) = 0 := by
          have hca : (mu a.1 : ℂ) ≠ 0 := by exact_mod_cast hmu0 a.1
          apply (mul_eq_zero.mp ?_).resolve_left hca
          rw [hrel.2, hB, zero_mul]
        cases si <;> simp [multiplicityOperator, K, hj, hA, hB]
    · have hz := grading_commutant_offDiagonal_zero R hZ
          (si, a) (sk, b) hp
      simp [multiplicityOperator, hp, hz]
  · rintro ⟨K, rfl⟩
    constructor <;> ext i k
    · rw [mul_storeGrading_apply, storeGrading_mul_apply]
      by_cases hp : i.1 = k.1
      · rw [hp]
        ring
      · simp [multiplicityOperator, hp]
    · rw [mul_storeDwell_apply, storeDwell_mul_apply]
      obtain ⟨si, a⟩ := i
      obtain ⟨sk, b⟩ := k
      by_cases hj : a.1 = b.1
      <;> cases si <;> cases sk
      <;> simp [multiplicityOperator, flipStoreIndex, hj]
      <;> ring

theorem squared_frequency_injective
    {J : Type*} (mu : J → ℝ)
    (hpos : ∀ j, 0 < mu j) (hinj : Function.Injective mu) :
    Function.Injective fun j => (mu j : ℂ) ^ 2 := by
  intro i j hij
  apply hinj
  have hijReal : mu i ^ 2 = mu j ^ 2 := by
    have h := congrArg Complex.re hij
    simpa [pow_two, Complex.mul_re] using h
  nlinarith [hpos i, hpos j]

theorem storeGrading_hermitian
    {J : Type*} {M : J → Type*}
    [Fintype (StoreIndex J M)] [DecidableEq (StoreIndex J M)] :
    (storeGrading (J := J) (M := M))ᴴ = storeGrading := by
  ext i k
  by_cases h : i = k
  · subst k
    cases hi : i.1 <;>
      simp [storeGrading, pauliSign, conjTranspose_apply, hi]
  · simp [storeGrading, conjTranspose_apply, h, Ne.symm h]

theorem storeDwell_hermitian
    {J : Type*} {M : J → Type*}
    [Fintype (StoreIndex J M)] [DecidableEq (StoreIndex J M)]
    (mu : J → ℝ) :
    (storeDwell (M := M) mu)ᴴ = storeDwell mu := by
  ext i k
  by_cases h : k = flipStoreIndex i
  · subst k
    simp [storeDwell, conjTranspose_apply]
    rfl
  · have hrev : i ≠ flipStoreIndex k := by
      intro h'
      apply h
      have hh := congrArg flipStoreIndex h'
      simpa using hh.symm
    simp [storeDwell, conjTranspose_apply, h, hrev]

theorem storeGrading_anticommutes_storeDwell
    {J : Type*} {M : J → Type*}
    [Fintype (StoreIndex J M)] [DecidableEq (StoreIndex J M)]
    (mu : J → ℝ) :
    storeGrading (J := J) (M := M) * storeDwell mu =
      -(storeDwell mu * storeGrading) := by
  ext i k
  rw [Matrix.neg_apply, storeGrading_mul_apply, mul_storeGrading_apply]
  by_cases h : k = flipStoreIndex i
  · subst k
    cases hi : i.1 <;>
      simp [storeDwell, flipStoreIndex, hi, pauliSign]
  · simp [storeDwell, h]

/-- Full certificate for the assembled Pauli normal form with distinct
positive frequencies and arbitrary multiplicity spaces. -/
theorem assembled_pauli_store_block_certificate
    {J : Type*} {M : J → Type*}
    [Fintype (StoreIndex J M)] [DecidableEq (StoreIndex J M)]
    [DecidableEq J]
    (mu : J → ℝ) (hpos : ∀ j, 0 < mu j)
    (hinj : Function.Injective mu) :
    (storeGrading (J := J) (M := M))ᴴ =
        storeGrading (J := J) (M := M)
      ∧ (storeDwell (M := M) mu)ᴴ = storeDwell (M := M) mu
      ∧ storeGrading (J := J) (M := M) * storeDwell (M := M) mu =
        -(storeDwell (M := M) mu * storeGrading (J := J) (M := M))
      ∧ ∀ R : Matrix (StoreIndex J M) (StoreIndex J M) ℂ,
        (R * storeGrading (J := J) (M := M) =
            storeGrading (J := J) (M := M) * R ∧
          R * storeDwell (M := M) mu = storeDwell (M := M) mu * R) ↔
          ∃ K : Matrix (MultiplicityIndex J M) (MultiplicityIndex J M) ℂ,
            R = multiplicityOperator K := by
  refine ⟨storeGrading_hermitian (J := J) (M := M), storeDwell_hermitian mu,
    storeGrading_anticommutes_storeDwell mu, ?_⟩
  intro R
  exact joint_commutant_eq_multiplicity_operators mu
    (fun j => (hpos j).ne') (squared_frequency_injective mu hpos hinj) R

end PauliStoreBlockCommutant
end NCG
