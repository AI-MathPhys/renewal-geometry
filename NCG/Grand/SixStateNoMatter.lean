/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Exact no-matter obstruction for the displayed six-state
  source (`thm:SM-six-state-no-matter`, Gran-Tensor manuscript)

* `six_state_no_matter`: the support-preserving coefficients
  (both cross blocks zero) contain the unit and are closed
  under sum, product, and adjoint; hence every word in
  support-preserving coefficients is support preserving — so
  every grading-changing Maslov/Walsh coefficient and every
  marked finite-Dirac block extracted from such a network is
  zero (`K_μ = 0`, `Q_μ = 0`, `D_F = 0`).

Rendering disclosed: norm limits, postselection, feedback and
chronological limits are the manuscript's operational reading
of the proved algebraic closure (the closed set is a unital
`*`-subalgebra and the listed operations stay inside it); the
displayed six-state source instantiates the
commuting-refinement hypothesis.
-/

open Matrix

namespace NCG

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Support preservation relative to complementary hermitian
projections. -/
def SupportPreserving (PL PR M : Matrix n n ℂ) : Prop :=
  PL * M * PR = 0 ∧ PR * M * PL = 0

/-- `thm:SM-six-state-no-matter`. -/
theorem six_state_no_matter (PL PR : Matrix n n ℂ)
    (hsum : PL + PR = 1) (hLR : PL * PR = 0)
    (hRL : PR * PL = 0) (hLH : PLᴴ = PL) (hRH : PRᴴ = PR) :
    (SupportPreserving PL PR 1)
    ∧ (∀ M N, SupportPreserving PL PR M →
        SupportPreserving PL PR N →
        SupportPreserving PL PR (M + N))
    ∧ (∀ M N, SupportPreserving PL PR M →
        SupportPreserving PL PR N →
        SupportPreserving PL PR (M * N))
    ∧ (∀ M, SupportPreserving PL PR M →
        SupportPreserving PL PR Mᴴ)
    ∧ (∀ l : List (Matrix n n ℂ),
        (∀ M ∈ l, SupportPreserving PL PR M) →
        SupportPreserving PL PR l.prod) := by
  have hone : SupportPreserving PL PR 1 := by
    constructor
    · rw [Matrix.mul_one]
      exact hLR
    · rw [Matrix.mul_one]
      exact hRL
  have hadd : ∀ M N, SupportPreserving PL PR M →
      SupportPreserving PL PR N →
      SupportPreserving PL PR (M + N) := by
    rintro M N ⟨hM1, hM2⟩ ⟨hN1, hN2⟩
    constructor
    · rw [Matrix.mul_add, Matrix.add_mul, hM1, hN1, add_zero]
    · rw [Matrix.mul_add, Matrix.add_mul, hM2, hN2, add_zero]
  have hmul : ∀ M N, SupportPreserving PL PR M →
      SupportPreserving PL PR N →
      SupportPreserving PL PR (M * N) := by
    rintro M N ⟨hM1, hM2⟩ ⟨hN1, hN2⟩
    constructor
    · calc PL * (M * N) * PR
          = PL * M * (1 * (N * PR)) := by
            simp only [Matrix.mul_assoc, Matrix.one_mul]
        _ = PL * M * ((PL + PR) * (N * PR)) := by rw [hsum]
        _ = (PL * M) * (PL * N * PR)
            + (PL * M * PR) * (N * PR) := by
            rw [Matrix.add_mul, Matrix.mul_add]
            simp only [Matrix.mul_assoc]
        _ = 0 := by
            rw [hN1, hM1, Matrix.mul_zero, Matrix.zero_mul,
              add_zero]
    · calc PR * (M * N) * PL
          = PR * M * (1 * (N * PL)) := by
            simp only [Matrix.mul_assoc, Matrix.one_mul]
        _ = PR * M * ((PL + PR) * (N * PL)) := by rw [hsum]
        _ = (PR * M * PL) * (N * PL)
            + (PR * M) * (PR * N * PL) := by
            rw [Matrix.add_mul, Matrix.mul_add]
            simp only [Matrix.mul_assoc]
        _ = 0 := by
            rw [hN2, hM2, Matrix.mul_zero, Matrix.zero_mul,
              zero_add]
  have hstar : ∀ M, SupportPreserving PL PR M →
      SupportPreserving PL PR Mᴴ := by
    rintro M ⟨hM1, hM2⟩
    constructor
    · rw [show PL * Mᴴ * PR = (PR * M * PL)ᴴ from by
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
          hLH, hRH]
        simp only [Matrix.mul_assoc]]
      rw [hM2, Matrix.conjTranspose_zero]
    · rw [show PR * Mᴴ * PL = (PL * M * PR)ᴴ from by
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
          hLH, hRH]
        simp only [Matrix.mul_assoc]]
      rw [hM1, Matrix.conjTranspose_zero]
  refine ⟨hone, hadd, hmul, hstar, ?_⟩
  intro l
  induction l with
  | nil =>
      intro _
      simpa using hone
  | cons M l ih =>
      intro hmem
      rw [List.prod_cons]
      exact hmul M l.prod
        (hmem M List.mem_cons_self)
        (ih fun N hN => hmem N (List.mem_cons_of_mem M hN))

omit [DecidableEq n] in
/-- Support preservation is closed under zero. -/
theorem supportPreserving_zero (PL PR : Matrix n n ℂ) :
    SupportPreserving PL PR 0 := by
  constructor
  · rw [Matrix.mul_zero, Matrix.zero_mul]
  · rw [Matrix.mul_zero, Matrix.zero_mul]

omit [DecidableEq n] in
/-- **Chronological/norm-limit closure**: a norm-convergent
sequence of support-preserving coefficients has a
support-preserving limit. -/
theorem supportPreserving_limit (PL PR : Matrix n n ℂ)
    (A : ℕ → Matrix n n ℂ) (B : Matrix n n ℂ)
    (hA : ∀ k, SupportPreserving PL PR (A k))
    (hlim : Filter.Tendsto A Filter.atTop (nhds B)) :
    SupportPreserving PL PR B := by
  constructor
  · have h1 : Filter.Tendsto (fun k => PL * A k * PR)
        Filter.atTop (nhds (PL * B * PR)) :=
      (Filter.Tendsto.mul (tendsto_const_nhds.mul hlim)
        tendsto_const_nhds)
    have h2 : (fun k => PL * A k * PR)
        = fun _ => (0 : Matrix n n ℂ) :=
      funext fun k => (hA k).1
    rw [h2] at h1
    exact tendsto_nhds_unique h1 tendsto_const_nhds
  · have h1 : Filter.Tendsto (fun k => PR * A k * PL)
        Filter.atTop (nhds (PR * B * PL)) :=
      (Filter.Tendsto.mul (tendsto_const_nhds.mul hlim)
        tendsto_const_nhds)
    have h2 : (fun k => PR * A k * PL)
        = fun _ => (0 : Matrix n n ℂ) :=
      funext fun k => (hA k).2
    rw [h2] at h1
    exact tendsto_nhds_unique h1 tendsto_const_nhds

open scoped Kronecker in
omit [DecidableEq n] in
/-- **Ancilla closure**: adjoining an ancilla preserves
support preservation for the lifted grading. -/
theorem supportPreserving_kronecker {m : Type*} [Fintype m]
    [DecidableEq m] (PL PR : Matrix n n ℂ)
    (M : Matrix n n ℂ) (E : Matrix m m ℂ)
    (hM : SupportPreserving PL PR M) :
    SupportPreserving (PL ⊗ₖ (1 : Matrix m m ℂ))
      (PR ⊗ₖ (1 : Matrix m m ℂ)) (M ⊗ₖ E) := by
  constructor
  · rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      Matrix.one_mul, Matrix.mul_one, hM.1,
      Matrix.zero_kronecker]
  · rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
      Matrix.one_mul, Matrix.mul_one, hM.2,
      Matrix.zero_kronecker]

/-- **Environment-measurement / feedback closure**: a sum of
support-preserving conjugations of a support-preserving
coefficient is support preserving. -/
theorem supportPreserving_environment {ι : Type*} [Fintype ι]
    (PL PR : Matrix n n ℂ)
    (hsum : PL + PR = 1) (hLR : PL * PR = 0)
    (hRL : PR * PL = 0) (hLH : PLᴴ = PL) (hRH : PRᴴ = PR)
    (V : ι → Matrix n n ℂ)
    (hV : ∀ i, SupportPreserving PL PR (V i))
    (M : Matrix n n ℂ) (hM : SupportPreserving PL PR M) :
    SupportPreserving PL PR (∑ i, V i * M * (V i)ᴴ) := by
  obtain ⟨_, hadd, hmul, hstar, _⟩ :=
    six_state_no_matter PL PR hsum hLR hRL hLH hRH
  refine Finset.sum_induction _ _
    (fun a b ha hb => hadd a b ha hb)
    (supportPreserving_zero PL PR) fun i _ => ?_
  exact hmul _ _ (hmul _ _ (hV i) hM) (hstar _ (hV i))

section SixStateSource

/-- The six-state carrier grading: the even-support
projection of the displayed release. -/
noncomputable def sixP : Matrix (Fin 6) (Fin 6) ℂ :=
  Matrix.diagonal (fun i => if i.val < 3 then 1 else 0)

/-- The complementary odd-support projection. -/
noncomputable def sixQ : Matrix (Fin 6) (Fin 6) ℂ :=
  Matrix.diagonal (fun i => if i.val < 3 then 0 else 1)

/-- The displayed cyclic branch `(0 1 2)(3 4 5)` of the
six-state release, preserving the grading blocks. -/
noncomputable def sixCycle : Matrix (Fin 6) (Fin 6) ℂ :=
  Matrix.of fun i j =>
    if j = (![1, 2, 0, 4, 5, 3] : Fin 6 → Fin 6) i
      then 1 else 0

/-- The displayed diagonal weight branch of the six-state
release. -/
noncomputable def sixWeight : Matrix (Fin 6) (Fin 6) ℂ :=
  Matrix.diagonal (![1/2, 1/3, 1/6, 1/2, 1/3, 1/6] :
    Fin 6 → ℂ)

private theorem sixP_add_sixQ : sixP + sixQ = 1 := by
  unfold sixP sixQ
  rw [Matrix.diagonal_add]
  rw [show (fun i : Fin 6 =>
      (if i.val < 3 then (1:ℂ) else 0)
        + if i.val < 3 then 0 else 1) = fun _ => 1 from
    funext fun i => by by_cases h : i.val < 3 <;> simp [h]]
  exact Matrix.diagonal_one

private theorem sixP_mul_sixQ : sixP * sixQ = 0 := by
  unfold sixP sixQ
  rw [Matrix.diagonal_mul_diagonal]
  rw [show (fun i : Fin 6 =>
      (if i.val < 3 then (1:ℂ) else 0)
        * if i.val < 3 then 0 else 1) = fun _ => 0 from
    funext fun i => by by_cases h : i.val < 3 <;> simp [h]]
  exact Matrix.diagonal_zero

private theorem sixQ_mul_sixP : sixQ * sixP = 0 := by
  unfold sixP sixQ
  rw [Matrix.diagonal_mul_diagonal]
  rw [show (fun i : Fin 6 =>
      (if i.val < 3 then (0:ℂ) else 1)
        * if i.val < 3 then 1 else 0) = fun _ => 0 from
    funext fun i => by by_cases h : i.val < 3 <;> simp [h]]
  exact Matrix.diagonal_zero

private theorem sixP_herm : sixPᴴ = sixP := by
  unfold sixP
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  by_cases h : i.val < 3 <;> simp [h]

private theorem sixQ_herm : sixQᴴ = sixQ := by
  unfold sixQ
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  by_cases h : i.val < 3 <;> simp [h]

private theorem commute_supportPreserving
    {P Q M : Matrix (Fin 6) (Fin 6) ℂ}
    (hPQ : P * Q = 0) (hQP : Q * P = 0)
    (hc : M * P = P * M) : SupportPreserving P Q M := by
  constructor
  · rw [← hc, Matrix.mul_assoc, hPQ, Matrix.mul_zero]
  · calc Q * M * P = Q * (M * P) := by rw [Matrix.mul_assoc]
      _ = Q * (P * M) := by rw [hc]
      _ = (Q * P) * M := by rw [← Matrix.mul_assoc]
      _ = 0 := by rw [hQP, Matrix.zero_mul]

private theorem sixCycle_comm : sixCycle * sixP
    = sixP * sixCycle := by
  unfold sixCycle sixP
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.cons_val, Fin.ext_iff]

private theorem sixWeight_comm : sixWeight * sixP
    = sixP * sixWeight := by
  unfold sixWeight sixP
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  ring

/-- **The displayed six-state source is support
preserving**: both branches, the grading itself, and hence
every finite network word in the release coefficients and
their adjoints, have zero cross-support blocks — the boxed
`K_μ = 0, Q_μ = 0, D_F = 0`. -/
theorem six_state_source_instantiation :
    SupportPreserving sixP sixQ sixCycle
    ∧ SupportPreserving sixP sixQ sixWeight
    ∧ (∀ words : List (Matrix (Fin 6) (Fin 6) ℂ),
        (∀ M ∈ words, SupportPreserving sixP sixQ M) →
        (sixP * words.prod * sixQ = 0
          ∧ sixQ * words.prod * sixP = 0))
    ∧ (∀ (A : Type) [AddCommMonoid A] [Module ℂ A]
        (recon : Matrix (Fin 6) (Fin 6) ℂ →ₗ[ℂ] A)
        (words : List (Matrix (Fin 6) (Fin 6) ℂ)),
        (∀ M ∈ words, SupportPreserving sixP sixQ M) →
        recon (sixP * words.prod * sixQ) = 0) := by
  have hc1 : SupportPreserving sixP sixQ sixCycle :=
    commute_supportPreserving sixP_mul_sixQ sixQ_mul_sixP
      sixCycle_comm
  have hc2 : SupportPreserving sixP sixQ sixWeight :=
    commute_supportPreserving sixP_mul_sixQ sixQ_mul_sixP
      sixWeight_comm
  have hwords : ∀ words : List (Matrix (Fin 6) (Fin 6) ℂ),
      (∀ M ∈ words, SupportPreserving sixP sixQ M) →
      SupportPreserving sixP sixQ words.prod := fun words h =>
    (six_state_no_matter sixP sixQ sixP_add_sixQ
      sixP_mul_sixQ sixQ_mul_sixP sixP_herm
      sixQ_herm).2.2.2.2 words h
  refine ⟨hc1, hc2, fun words h => (hwords words h), ?_⟩
  intro A _ _ recon words h
  rw [(hwords words h).1, map_zero]

end SixStateSource

end NCG
