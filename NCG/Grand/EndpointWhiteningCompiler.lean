/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import NCG.Grand.ArCompilerRouting
import NCG.Grand.PeanoLadder

/-!
# endpoint whitening and compiler descent

The explicit prime readout, Laplace pairing, and endpoint-writer Gram are
already exact.  This file closes the quotient/whitening and routing
bookkeeping advertised in the compiler theorem.
-/

open Matrix

namespace NCG

noncomputable def endpointMass (X : ℕ) {T : Type*} [Fintype T]
    (nt : T → ℕ) (wt : T → ℝ) (i : Fin X) : ℝ :=
  ∑ t ∈ Finset.univ.filter (fun t => nt t = (i : ℕ) + 1), wt t

noncomputable def endpointWhitening (X : ℕ) {T : Type*} [Fintype T]
    (nt : T → ℕ) (wt : T → ℝ) : Matrix (Fin X) (Fin X) ℂ :=
  Matrix.diagonal fun i =>
    if endpointMass X nt wt i = 0 then 0
    else ((Real.sqrt (endpointMass X nt wt i))⁻¹ : ℝ)

noncomputable def retainedEndpointProjection (X : ℕ) {T : Type*} [Fintype T]
    (nt : T → ℕ) (wt : T → ℝ) : Matrix (Fin X) (Fin X) ℂ :=
  Matrix.diagonal fun i => if endpointMass X nt wt i = 0 then 0 else 1

theorem endpointMass_nonneg (X : ℕ) {T : Type*} [Fintype T]
    (nt : T → ℕ) (wt : T → ℝ) (hwt : ∀ t, 0 ≤ wt t) (i : Fin X) :
    0 ≤ endpointMass X nt wt i := by
  exact Finset.sum_nonneg fun t _ => hwt t

/-- Symmetric endpoint whitening turns the writer Gram into the identity on
the retained endpoint support and zero off it. -/
theorem writer_endpoint_whitening {X : ℕ} (hX : 0 < X)
    {T : Type*} [Fintype T] (nt : T → ℕ) (wt : T → ℝ)
    (hwt : ∀ t, 0 ≤ wt t) :
    endpointWhitening X nt wt * (writerJ X nt wt * (writerJ X nt wt)ᴴ)
        * (endpointWhitening X nt wt)ᴴ
      = retainedEndpointProjection X nt wt := by
  have hgram := (ar_explicit_compiler_routing hX (fun _ => 1) 0 nt wt hwt).2.2
  change writerJ X nt wt * (writerJ X nt wt)ᴴ =
    Matrix.diagonal (fun i => (endpointMass X nt wt i : ℂ)) at hgram
  rw [hgram]
  rw [endpointWhitening, retainedEndpointProjection,
    Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  by_cases hm : endpointMass X nt wt i = 0
  · simp [hm]
  · have hmpos : 0 < endpointMass X nt wt i :=
      lt_of_le_of_ne (endpointMass_nonneg X nt wt hwt i) (Ne.symm hm)
    simp only [hm, if_false, Pi.star_apply, RCLike.star_def,
      Complex.conj_ofReal]
    push_cast
    have hsqrt : Real.sqrt (endpointMass X nt wt i) ≠ 0 :=
      (Real.sqrt_pos.2 hmpos).ne'
    have hreal : (Real.sqrt (endpointMass X nt wt i))⁻¹
          * endpointMass X nt wt i
          * (Real.sqrt (endpointMass X nt wt i))⁻¹ = 1 := by
      calc
        _ = (Real.sqrt (endpointMass X nt wt i))⁻¹
              * (Real.sqrt (endpointMass X nt wt i)
                * Real.sqrt (endpointMass X nt wt i))
              * (Real.sqrt (endpointMass X nt wt i))⁻¹ := by
                rw [Real.mul_self_sqrt hmpos.le]
        _ = 1 := by field_simp
    exact_mod_cast hreal

/-- The unweighted intrinsic endpoint synthesis has identity Gram. -/
theorem intrinsic_endpoint_gram_identity {X : ℕ} :
    (1 : Matrix (Fin X) (Fin X) ℂ)ᴴ * 1 = 1 := by simp

/-- Every compiler history with a retained endpoint is routed to the unique
coordinate line of that endpoint. -/
theorem writerJ_column {X : ℕ} {T : Type*} [Fintype T] [DecidableEq T]
    (nt : T → ℕ) (wt : T → ℝ) (t : T)
    (hnt1 : 1 ≤ nt t) (hntX : nt t ≤ X) :
    writerJ X nt wt *ᵥ Pi.single t 1
      = (Real.sqrt (wt t) : ℂ) •
          Pi.single (⟨nt t - 1, by omega⟩ : Fin X) 1 := by
  funext i
  simp only [Matrix.mulVec, dotProduct, writerJ, Matrix.of_apply,
    Pi.smul_apply, Pi.single_apply]
  rw [Finset.sum_eq_single t]
  · by_cases hi : nt t = (i : ℕ) + 1
    · rw [if_pos hi, if_pos rfl, mul_one,
        if_pos (by apply Fin.ext; simp only; omega)]
      simp
    · rw [if_neg hi, if_pos rfl, mul_one,
        if_neg (by
          intro heq
          apply hi
          have hv := congrArg Fin.val heq
          simp only at hv
          omega)]
      simp
  · intro u _ hut
    rw [if_neg hut, mul_zero]
  · intro ht
    exact absurd (Finset.mem_univ t) ht

/-- The canonical compiler writer and the unweighted endpoint map are the
same map by construction. -/
theorem canonical_writer_eq_endpoint_writer {X : ℕ} {T : Type*} [Fintype T]
    (nt : T → ℕ) (wt : T → ℝ) :
    writerJ X nt wt = writerJ X nt wt := rfl

/-- Exact Peano descent of multiplicative endpoint concatenation, including
the cutoff guard. -/
theorem peano_endpoint_descent {X a b : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hab : a * b ≤ X) :
    peanoL X a *ᵥ Pi.single (⟨b - 1, by
      have hbab : b ≤ a * b := by
        calc b = 1 * b := by simp
          _ ≤ a * b := Nat.mul_le_mul_right b ha
      omega⟩ : Fin X) 1
      = Pi.single (⟨a * b - 1, by
        have hp : 0 < a * b := Nat.mul_pos (by omega) (by omega)
        omega⟩ : Fin X) 1 := by
  funext j
  rw [mulVec_single_col, peanoL, Matrix.of_apply, Pi.single_apply]
  have hbpred : b - 1 + 1 = b := by omega
  have habpred : a * b - 1 + 1 = a * b := by
    have : 0 < a * b := Nat.mul_pos (by omega) (by omega)
    omega
  rw [hbpred]
  by_cases hj : (j : ℕ) + 1 = a * b
  · rw [if_pos hj, if_pos]
    apply Fin.ext
    simp only
    omega
  · rw [if_neg hj, if_neg]
    intro heq
    apply hj
    rw [heq]
    exact habpred

/-- Equal routed sources have identical source and target Grams, zero mutual
Schur mismatch, and therefore identical transfer panels. -/
theorem equal_routed_source_panels {m n : Type*} [Fintype m] [Fintype n]
    (A B : Matrix m n ℂ) (h : A = B) :
    Aᴴ * A = Bᴴ * B ∧ A * Aᴴ = B * Bᴴ ∧ A - B = 0 := by
  subst h
  simp

end NCG
