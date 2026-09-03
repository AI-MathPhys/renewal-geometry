/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteControlledUnitaryMarkedInstrumentExact
import NCG.Grand.FiniteProcessCombTomography

/-!
# Finite controlled-unitary process combs

The Choi factors of a normalized finite controlled-unitary instrument are
assembled into a block-diagonal one-step process comb.  The classical output
leg records the mark and the quantum output leg records the matrix index.
Two-sided unitarity proves the causal output-trace equation.  Consequently the
existing finite-comb theorem supplies canonical linked support-minimal
purifications.
-/

open Matrix Finset
open scoped ComplexOrder MatrixOrder

namespace NCG

variable {H M : Type} [Fintype H] [DecidableEq H]
  [Fintype M] [DecidableEq M]

/-- The vectorized one-Kraus Choi factor, supported on one classical mark. -/
noncomputable def markedUnitaryCombVector
    (c : M → ℂ) (U : M → Matrix H H ℂ) (m : M) :
    CombCarrier (M × H) H 1 → ℂ :=
  fun p => if p.1.1 = m then
    star ((c m • U m) p.2.1 p.1.2)
  else 0

@[simp]
theorem star_markedUnitaryCombVector_apply
    (c : M → ℂ) (U : M → Matrix H H ℂ) (m : M)
    (p : CombCarrier (M × H) H 1) :
    (star (markedUnitaryCombVector c U m)) p =
      if p.1.1 = m then (c m • U m) p.2.1 p.1.2 else 0 := by
  by_cases h : p.1.1 = m
  · simp [markedUnitaryCombVector, Pi.star_apply, h, map_mul]
  · simp [markedUnitaryCombVector, Pi.star_apply, h]

@[simp]
theorem markedUnitaryCombVector_mk
    (c : M → ℂ) (U : M → Matrix H H ℂ) (m : M)
    (o : M × H) (i : H)
    (x : CombCarrier (M × H) H 0) :
    markedUnitaryCombVector c U m (o, (i, x)) =
      if o.1 = m then star ((c m • U m) i o.2) else 0 := rfl

@[simp]
theorem star_markedUnitaryCombVector_mk
    (c : M → ℂ) (U : M → Matrix H H ℂ) (m : M)
    (o : M × H) (i : H)
    (x : CombCarrier (M × H) H 0) :
    (star (markedUnitaryCombVector c U m)) (o, (i, x)) =
      if o.1 = m then (c m • U m) i o.2 else 0 :=
  star_markedUnitaryCombVector_apply c U m _

/-- The one-step block-diagonal Choi tensor of the marked unitary bank. -/
noncomputable def controlledUnitaryCombTerminal
    (c : M → ℂ) (U : M → Matrix H H ℂ) :
    Matrix (CombCarrier (M × H) H 1)
      (CombCarrier (M × H) H 1) ℂ :=
  ∑ m, vecMulVec (markedUnitaryCombVector c U m)
    (star (markedUnitaryCombVector c U m))

@[simp]
theorem controlledUnitaryCombTerminal_apply
    (c : M → ℂ) (U : M → Matrix H H ℂ)
    (p q : CombCarrier (M × H) H 1) :
    controlledUnitaryCombTerminal c U p q =
      ∑ m, markedUnitaryCombVector c U m p *
        (star (markedUnitaryCombVector c U m)) q := by
  simp [controlledUnitaryCombTerminal, Matrix.sum_apply,
    vecMulVec_apply]

/-- The block-diagonal terminal Choi tensor is positive semidefinite. -/
theorem controlledUnitaryCombTerminal_posSemidef
    (c : M → ℂ) (U : M → Matrix H H ℂ) :
    (controlledUnitaryCombTerminal c U).PosSemidef := by
  classical
  unfold controlledUnitaryCombTerminal
  exact Finset.sum_induction _ _ (fun A B hA hB => hA.add hB)
    Matrix.PosSemidef.zero
    (fun m _ => posSemidef_vecMulVec_self_star
      (markedUnitaryCombVector c U m))

/-- Prefix family with the normalized scalar prefix at depth zero, the marked
Choi tensor at depth one, and zero outside the asserted horizon. -/
noncomputable def controlledUnitaryOneStepPrefixes
    (c : M → ℂ) (U : M → Matrix H H ℂ) :
    CombPrefixFamily (M × H) H
  | 0 => 1
  | 1 => controlledUnitaryCombTerminal c U
  | _ + 2 => 0

@[simp]
theorem controlledUnitaryOneStepPrefixes_zero
    (c : M → ℂ) (U : M → Matrix H H ℂ) :
    controlledUnitaryOneStepPrefixes c U 0 = 1 := rfl

@[simp]
theorem controlledUnitaryOneStepPrefixes_one
    (c : M → ℂ) (U : M → Matrix H H ℂ) :
    controlledUnitaryOneStepPrefixes c U 1 =
      controlledUnitaryCombTerminal c U := rfl

/-- The output trace of the one-step terminal tensor is the identity prefix.
This is the process-comb form of normalization of the marked instrument. -/
theorem controlledUnitaryCombTerminal_outputTrace
    (c : M → ℂ) (U : M → Matrix H H ℂ)
    (hU : ∀ m, U m * (U m)ᴴ = 1)
    (hc : ∑ m, star (c m) * c m = 1) :
    combOutputTrace (controlledUnitaryCombTerminal c U) =
      combIdentityExtension (1 :
        Matrix (CombCarrier (M × H) H 0)
          (CombCarrier (M × H) H 0) ℂ) := by
  classical
  ext ⟨i, x⟩ ⟨j, y⟩
  have hxy : x = y := by
    change PUnit at x y
    exact Subsingleton.elim x y
  subst y
  change (∑ o : M × H,
      controlledUnitaryCombTerminal c U (o, (i, x)) (o, (j, x))) =
    if i = j then 1 else 0
  have hterminal (o : M × H) :
      controlledUnitaryCombTerminal c U (o, (i, x)) (o, (j, x)) =
        ∑ m, markedUnitaryCombVector c U m (o, (i, x)) *
          (star (markedUnitaryCombVector c U m)) (o, (j, x)) :=
    controlledUnitaryCombTerminal_apply c U _ _
  simp_rw [hterminal]
  rw [Fintype.sum_prod_type]
  simp only [markedUnitaryCombVector_mk,
    star_markedUnitaryCombVector_mk]
  simp only [ite_mul, zero_mul, mul_ite, mul_zero]
  have hcollapse (a : M) (k : H) :
      (∑ m : M, if a = m then if a = m then
        star ((c m • U m) i k) * (c m • U m) j k else 0 else 0) =
          star ((c a • U a) i k) * (c a • U a) j k := by
    rw [Finset.sum_eq_single a]
    · simp
    · intro m _ hma
      simp [Ne.symm hma]
    · simp
  rw [show (∑ a : M, ∑ k : H, ∑ m : M, if a = m then if a = m then
      star ((c m • U m) i k) * (c m • U m) j k else 0 else 0) =
      ∑ a : M, ∑ k : H,
        star ((c a • U a) i k) * (c a • U a) j k by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro k _
    exact hcollapse a k]
  have hrow : ∀ m,
      ∑ k : H, star ((c m • U m) i k) * (c m • U m) j k =
        (star (c m) * c m) * if i = j then 1 else 0 := by
    intro m
    rw [show (∑ k : H,
        star ((c m • U m) i k) * (c m • U m) j k) =
        (star (c m) * c m) * (U m * (U m)ᴴ) j i by
      simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [star_mul]
      ring]
    rw [hU]
    simp [Matrix.one_apply, eq_comm]
  simp_rw [hrow]
  rw [← Finset.sum_mul, hc, one_mul]

/-- The controlled-unitary prefix family satisfies the exact deterministic
comb criterion through one step. -/
theorem controlledUnitary_isDeterministicCombThrough
    (c : M → ℂ) (U : M → Matrix H H ℂ)
    (hU : ∀ m, U m * (U m)ᴴ = 1)
    (hc : ∑ m, star (c m) * c m = 1) :
    IsDeterministicCombThrough
      (controlledUnitaryOneStepPrefixes c U) 1 := by
  refine ⟨rfl, ?_, ?_⟩
  · intro k hk
    interval_cases k
    · exact Matrix.PosSemidef.one
    · simpa using controlledUnitaryCombTerminal_posSemidef c U
  · intro k hk
    have hk0 : k = 0 := Nat.lt_one_iff.mp hk
    subst k
    simpa using controlledUnitaryCombTerminal_outputTrace c U hU hc

/-- Hence a normalized two-sided controlled-unitary bank has a legitimate
finite deterministic comb with canonical linked support-minimal purification. -/
theorem controlledUnitary_finiteDeterministicComb_exists
    (c : M → ℂ) (U : M → Matrix H H ℂ)
    (hU : ∀ m, U m * (U m)ᴴ = 1)
    (hc : ∑ m, star (c m) * c m = 1) :
    Nonempty (FiniteDeterministicComb
      (controlledUnitaryOneStepPrefixes c U) 1) :=
  finiteDeterministicComb_iff.mpr
    (controlledUnitary_isDeterministicCombThrough c U hU hc)

/-- Canonical equal amplitudes make the finite comb construction
unconditional for every nonempty two-sided unitary bank. -/
theorem exists_controlledUnitary_finiteDeterministicComb
    [Nonempty M] (U : M → Matrix H H ℂ)
    (hU : ∀ m, U m * (U m)ᴴ = 1) :
    ∃ c : M → ℂ,
      Nonempty (FiniteDeterministicComb
        (controlledUnitaryOneStepPrefixes c U) 1) := by
  refine ⟨uniformMarkAmplitude M, ?_⟩
  exact controlledUnitary_finiteDeterministicComb_exists _ U hU
    (uniformMarkAmplitude_normalized M)

end NCG
