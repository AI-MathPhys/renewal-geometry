/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The exact protected amplitude carrier of `K₄`
  (`thm:exact-oriented-carrier`, SM_emergence)

For the amplitude nonbacktracking operator `B₀` on the twelve
ordered edges of `K₄`:

* `bZero_annihilator` — `B₀` satisfies its claimed characteristic
  polynomial: `(B₀-2)(B₀-1)³(B₀+1)²(B₀²+B₀+2)³ = 0` (certified by
  exact integer arithmetic);
* `carrier_in_kernel` / `carrier_independent` — the three harmonic
  cycle injections `Jα` lie in `Ker(B₀-1)` and are independent;
* `carrier_kernel_complete` — every rational vector of `Ker(B₀-1)`
  is a combination of the three cycle injections (certified by an
  explicit pseudo-inverse `2P·(B₀-1) = 2(1-N)`), so
  `Ker(B₀-I) = JH¹(K₄)` has dimension exactly three.

The algebraic-multiplicity display for the remaining eigenvalues
and the `S₄`-isotypic decomposition are the declared remainder.
-/

namespace NCG

open Matrix

noncomputable section

/-- The amplitude nonbacktracking operator of `K₄` on ordered
edges `(01,02,03,10,12,13,20,21,23,30,31,32)`, over `ℤ`. -/
def bZeroZ : Matrix (Fin 12) (Fin 12) ℤ :=
  !![0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1;
    0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1;
    1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0;
    1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]

/-- The three harmonic triangle injections `Jα` (integer form). -/
def carrierZ1 : Fin 12 → ℤ := ![1, -1, 0, -1, 1, 0, 1, -1, 0, 0, 0, 0]

def carrierZ2 : Fin 12 → ℤ := ![1, 0, -1, -1, 0, 1, 0, 0, 0, 1, -1, 0]

def carrierZ3 : Fin 12 → ℤ := ![0, 1, -1, 0, 0, 0, -1, 0, 1, 1, 0, -1]

/-- The kernel projector onto the carrier coordinates. -/
def nProjZ : Matrix (Fin 12) (Fin 12) ℤ :=
  !![0, 0, 0, 0, 0, 0, 0, -1, 0, 0, -1, 0;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0;
    0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 1;
    0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, -1;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]

/-- Twice the pseudo-inverse certificate. -/
def pTwiceZ : Matrix (Fin 12) (Fin 12) ℤ :=
  !![0, 2, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0;
    1, -2, 1, 0, 1, 1, 1, 0, -1, 0, 0, 0;
    0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    1, -2, -1, -2, 1, 1, 1, 0, -1, 0, 0, 0;
    1, 2, -1, 0, -1, 1, -1, 0, 1, 2, 0, 0;
    1, 0, 1, 0, 1, -1, 1, 0, 1, 0, 0, 0;
    0, 2, -2, 0, 0, 0, -2, 0, 2, 2, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    1, 0, 1, 0, 1, 1, 1, 0, -1, 0, 0, 0;
    1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

set_option maxRecDepth 40000 in
set_option maxHeartbeats 4000000 in
-- the 12×12 integer decide-certificate needs an enlarged kernel budget
/-- `thm:exact-oriented-carrier` (annihilating certificate): `B₀`
satisfies its claimed characteristic polynomial. -/
theorem bZero_annihilator :
    (bZeroZ - 2) * (bZeroZ - 1) ^ 3 * (bZeroZ + 1) ^ 2
      * (bZeroZ ^ 2 + bZeroZ + 2) ^ 3 = 0 := by
  decide

set_option maxRecDepth 40000 in
set_option maxHeartbeats 1000000 in
-- the kernel-membership decide-certificates need an enlarged budget
/-- The three cycle injections lie in `Ker(B₀ - 1)`. -/
theorem carrier_in_kernel :
    (bZeroZ - 1) *ᵥ carrierZ1 = 0
    ∧ (bZeroZ - 1) *ᵥ carrierZ2 = 0
    ∧ (bZeroZ - 1) *ᵥ carrierZ3 = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

set_option maxRecDepth 40000 in
set_option maxHeartbeats 2000000 in
-- the 12×12 product certificate needs an enlarged kernel budget
/-- The pseudo-inverse identity `2P·(B₀-1) = 2(1 - N)`. -/
theorem pTwice_eq :
    pTwiceZ * (bZeroZ - 1) = (1 - nProjZ) + (1 - nProjZ) := by
  decide

/-- The three cycle injections are linearly independent. -/
theorem carrier_independent (a b c : ℚ)
    (h : a • (fun i => ((carrierZ1 i : ℤ) : ℚ))
        + b • (fun i => ((carrierZ2 i : ℤ) : ℚ))
        + c • (fun i => ((carrierZ3 i : ℤ) : ℚ)) = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  have h7 := congrFun h 7
  have h10 := congrFun h 10
  have h11 := congrFun h 11
  have e17 : carrierZ1 7 = -1 := rfl
  have e27 : carrierZ2 7 = 0 := rfl
  have e37 : carrierZ3 7 = 0 := rfl
  have e110 : carrierZ1 10 = 0 := rfl
  have e210 : carrierZ2 10 = -1 := rfl
  have e310 : carrierZ3 10 = 0 := rfl
  have e111 : carrierZ1 11 = 0 := rfl
  have e211 : carrierZ2 11 = 0 := rfl
  have e311 : carrierZ3 11 = -1 := rfl
  simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply,
    smul_eq_mul, e17, e27, e37, e110, e210, e310, e111, e211,
    e311] at h7 h10 h11
  push_cast at h7 h10 h11
  exact ⟨by linarith, by linarith, by linarith⟩

set_option maxHeartbeats 2000000 in
-- the 12-fold sum expansions need an enlarged elaboration budget
/-- `thm:exact-oriented-carrier` (kernel): every rational kernel
vector of `B₀ - 1` is a combination of the three harmonic cycle
injections — `Ker(B₀-I) = JH¹(K₄)`, of dimension exactly three. -/
theorem carrier_kernel_complete (w : Fin 12 → ℚ)
    (hw : (bZeroZ.map (Int.cast : ℤ → ℚ) - 1) *ᵥ w = 0) :
    w = (-(w 7)) • (fun i => ((carrierZ1 i : ℤ) : ℚ))
      + (-(w 10)) • (fun i => ((carrierZ2 i : ℤ) : ℚ))
      + (-(w 11)) • (fun i => ((carrierZ3 i : ℤ) : ℚ)) := by
  have hcert : (pTwiceZ.map (Int.cast : ℤ → ℚ))
      * (bZeroZ.map (Int.cast : ℤ → ℚ) - 1)
      = (1 - nProjZ.map (Int.cast : ℤ → ℚ))
        + (1 - nProjZ.map (Int.cast : ℤ → ℚ)) := by
    have h2 := congrArg
      (fun M => (RingHom.mapMatrix (Int.castRingHom ℚ)) M)
      pTwice_eq
    simp only [map_mul, map_sub, map_add, map_one,
      RingHom.mapMatrix_apply, Int.coe_castRingHom] at h2
    exact h2
  have h1 : (pTwiceZ.map (Int.cast : ℤ → ℚ))
      *ᵥ ((bZeroZ.map (Int.cast : ℤ → ℚ) - 1) *ᵥ w) = 0 := by
    rw [hw, Matrix.mulVec_zero]
  rw [Matrix.mulVec_mulVec, hcert] at h1
  have h2 : w = (nProjZ.map (Int.cast : ℤ → ℚ)) *ᵥ w := by
    funext i
    have hh := congrFun h1 i
    simp only [Matrix.add_mulVec, Matrix.sub_mulVec,
      Matrix.one_mulVec, Pi.add_apply, Pi.sub_apply,
      Pi.zero_apply] at hh
    linarith
  have hcol7 : ∀ i, nProjZ i 7 = -(carrierZ1 i) := by decide
  have hcol10 : ∀ i, nProjZ i 10 = -(carrierZ2 i) := by decide
  have hcol11 : ∀ i, nProjZ i 11 = -(carrierZ3 i) := by decide
  have hz : ∀ i : Fin 12, nProjZ i 0 = 0 ∧ nProjZ i 1 = 0
      ∧ nProjZ i 2 = 0 ∧ nProjZ i 3 = 0 ∧ nProjZ i 4 = 0
      ∧ nProjZ i 5 = 0 ∧ nProjZ i 6 = 0 ∧ nProjZ i 8 = 0
      ∧ nProjZ i 9 = 0 := by decide
  conv_lhs => rw [h2]
  funext i
  rw [Matrix.mulVec, dotProduct]
  rw [show (∑ j, (nProjZ.map (Int.cast : ℤ → ℚ)) i j * w j)
      = ∑ j ∈ ({7, 10, 11} : Finset (Fin 12)),
          (nProjZ.map (Int.cast : ℤ → ℚ)) i j * w j from
    (Finset.sum_subset (Finset.subset_univ _) (by
      intro j _ hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      push Not at hj
      fin_cases j <;>
        first
          | exact absurd rfl hj.1
          | exact absurd rfl hj.2.1
          | exact absurd rfl hj.2.2
          | (refine mul_eq_zero_of_left ?_ _
             rw [Matrix.map_apply]
             exact_mod_cast (hz i).1)
          | (refine mul_eq_zero_of_left ?_ _
             rw [Matrix.map_apply]
             exact_mod_cast (hz i).2.1)
          | (refine mul_eq_zero_of_left ?_ _
             rw [Matrix.map_apply]
             exact_mod_cast (hz i).2.2.1)
          | (refine mul_eq_zero_of_left ?_ _
             rw [Matrix.map_apply]
             exact_mod_cast (hz i).2.2.2.1)
          | (refine mul_eq_zero_of_left ?_ _
             rw [Matrix.map_apply]
             exact_mod_cast (hz i).2.2.2.2.1)
          | (refine mul_eq_zero_of_left ?_ _
             rw [Matrix.map_apply]
             exact_mod_cast (hz i).2.2.2.2.2.1)
          | (refine mul_eq_zero_of_left ?_ _
             rw [Matrix.map_apply]
             exact_mod_cast (hz i).2.2.2.2.2.2.1)
          | (refine mul_eq_zero_of_left ?_ _
             rw [Matrix.map_apply]
             exact_mod_cast (hz i).2.2.2.2.2.2.2.1)
          | (refine mul_eq_zero_of_left ?_ _
             rw [Matrix.map_apply]
             exact_mod_cast (hz i).2.2.2.2.2.2.2.2))).symm]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp only [Matrix.map_apply, hcol7, hcol10, hcol11,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

end

end NCG
