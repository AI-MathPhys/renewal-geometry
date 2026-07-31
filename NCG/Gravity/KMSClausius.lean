/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The local KMS–Clausius identity
  (`prop:kms`, GR_emergence)

The two mechanisms behind `δQ = T δS_bulk` at `T = a/2π` are proved
in the finite-dimensional Gibbs model:

* `finite_kms` — the KMS identity for the Gibbs functional
  `ω(X) = Tr(e^{-βH}X)`: for the (complex-time) modular flow
  `σ_w(B) = e^{wH}Be^{-wH}`,
  `ω(A·σ_w(B)) = ω(σ_{w+β}(B)·A)` — the boundary-value relation
  that identifies the modular group of the Gibbs state at inverse
  temperature `β`;
* `gibbs_normalization_derivative` — the perturbation of a
  normalized family has zero total derivative;
* `entropy_first_law` — along any differentiable perturbation of a
  Gibbs state, `δS = β·δ⟨E⟩` — the modular/thermodynamic first law;
* `clausius_identity` — hence `δQ := δ⟨E⟩ = T·δS` with `T = 1/β`.

The identification of the modular flow with the local boost flow at
`T = a/2π` (the Rindler/Bisognano–Wichmann input of
`hyp:calibration`) and the boost-energy integral form of `K_mod` are
the declared inputs, exactly as in the manuscript proof.
-/

namespace NCG

open Matrix NormedSpace

variable {n : ℕ}

/-- The complex-time modular flow of the Hamiltonian. -/
noncomputable def modularFlow (H : Matrix (Fin n) (Fin n) ℂ) (w : ℂ)
    (B : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  exp (w • H) * B * exp ((-w) • H)

/-- `prop:kms` (KMS identity): the Gibbs functional
`ω = Tr(e^{-βH}·)` satisfies the KMS boundary relation
`ω(A σ_w(B)) = ω(σ_{w+β}(B) A)` for the modular flow of `H`. -/
theorem finite_kms (H A B : Matrix (Fin n) (Fin n) ℂ) (beta w : ℂ) :
    Matrix.trace (exp ((-beta) • H) * A * modularFlow H w B)
      = Matrix.trace (exp ((-beta) • H)
          * modularFlow H (w + beta) B * A) := by
  classical
  have hcomm : ∀ a b : ℂ, Commute (a • H) (b • H) :=
    fun a b => ((Commute.refl H).smul_left a).smul_right b
  have key : ∀ a b : ℂ,
      exp (a • H) * exp (b • H) = exp ((a + b) • H) := by
    intro a b
    rw [add_smul]
    exact (Matrix.exp_add_of_commute _ _ (hcomm a b)).symm
  unfold modularFlow
  have hL : Matrix.trace (exp ((-beta) • H) * A
        * (exp (w • H) * B * exp ((-w) • H)))
      = Matrix.trace (A * exp (w • H) * B
          * exp ((-w + -beta) • H)) := by
    rw [show exp ((-beta) • H) * A
          * (exp (w • H) * B * exp ((-w) • H))
        = exp ((-beta) • H)
          * (A * exp (w • H) * B * exp ((-w) • H)) from by
        simp only [Matrix.mul_assoc]]
    rw [Matrix.trace_mul_comm]
    rw [show A * exp (w • H) * B * exp ((-w) • H) * exp ((-beta) • H)
        = A * exp (w • H) * B
          * (exp ((-w) • H) * exp ((-beta) • H)) from by
        simp only [Matrix.mul_assoc]]
    rw [key]
  have hR : Matrix.trace (exp ((-beta) • H)
        * (exp ((w + beta) • H) * B * exp ((-(w + beta)) • H)) * A)
      = Matrix.trace (A * exp (w • H) * B
          * exp ((-w + -beta) • H)) := by
    rw [show exp ((-beta) • H)
          * (exp ((w + beta) • H) * B * exp ((-(w + beta)) • H)) * A
        = exp ((-beta) • H) * exp ((w + beta) • H)
          * (B * exp ((-(w + beta)) • H) * A) from by
        simp only [Matrix.mul_assoc]]
    rw [key, show (-beta + (w + beta)) = w from by ring]
    rw [Matrix.trace_mul_comm]
    rw [show B * exp ((-(w + beta)) • H) * A * exp (w • H)
        = B * (exp ((-(w + beta)) • H) * A * exp (w • H)) from by
        simp only [Matrix.mul_assoc]]
    rw [Matrix.trace_mul_comm]
    rw [show exp ((-(w + beta)) • H) * A * exp (w • H) * B
        = exp ((-(w + beta)) • H) * (A * exp (w • H) * B) from by
        simp only [Matrix.mul_assoc]]
    rw [Matrix.trace_mul_comm]
    rw [show (-(w + beta)) = -w + -beta from by ring]
  rw [hL, hR]

/-- The perturbation of a normalized family has zero total
derivative. -/
theorem gibbs_normalization_derivative {I : Type*} [Fintype I]
    {p : ℝ → I → ℝ} {p' : I → ℝ}
    (hp : ∀ i, HasDerivAt (fun u => p u i) (p' i) 0)
    (hnorm : ∀ u, ∑ i, p u i = 1) :
    ∑ i, p' i = 0 := by
  have hsum : HasDerivAt (fun u => ∑ i, p u i) (∑ i, p' i) 0 :=
    HasDerivAt.fun_sum (fun i _ => hp i)
  have hconst : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 0 :=
    hasDerivAt_const 0 1
  have hfun : (fun u => ∑ i, p u i) = fun _ : ℝ => (1 : ℝ) :=
    funext hnorm
  rw [hfun] at hsum
  exact hsum.unique hconst

/-- `prop:kms` (first law): along any differentiable perturbation of
a Gibbs state `p_i = e^{-βE_i}/Z`, the entropy variation is `β`
times the energy variation: `δS = β·δ⟨E⟩`. -/
theorem entropy_first_law {I : Type*} [Fintype I]
    {p : ℝ → I → ℝ} {p' : I → ℝ} {E : I → ℝ} {beta Z : ℝ}
    (hp : ∀ i, HasDerivAt (fun u => p u i) (p' i) 0)
    (hpos : ∀ i, 0 < p 0 i) (hZ : 0 < Z)
    (hgibbs : ∀ i, p 0 i = Real.exp (-(beta * E i)) / Z)
    (hnorm : ∀ u, ∑ i, p u i = 1) :
    HasDerivAt (fun u => ∑ i, -(p u i * Real.log (p u i)))
      (beta * ∑ i, p' i * E i) 0 := by
  have hsum0 := gibbs_normalization_derivative hp hnorm
  have hterm : ∀ i, HasDerivAt
      (fun u => -(p u i * Real.log (p u i)))
      (-(p' i * (Real.log (p 0 i) + 1))) 0 := by
    intro i
    have hlog : HasDerivAt (fun u => Real.log (p u i))
        (p' i / p 0 i) 0 := by
      have := (hp i).log (hpos i).ne'
      exact this
    have hmul := (hp i).fun_mul hlog
    have := hmul.neg
    apply this.congr_deriv
    have hne : p 0 i ≠ 0 := (hpos i).ne'
    field_simp
  have hS : HasDerivAt (fun u => ∑ i, -(p u i * Real.log (p u i)))
      (∑ i, -(p' i * (Real.log (p 0 i) + 1))) 0 :=
    HasDerivAt.fun_sum (fun i _ => hterm i)
  apply hS.congr_deriv
  have hlogval : ∀ i, Real.log (p 0 i) = -(beta * E i) - Real.log Z := by
    intro i
    rw [hgibbs i, Real.log_div (Real.exp_pos _).ne' hZ.ne',
      Real.log_exp]
  calc (∑ i, -(p' i * (Real.log (p 0 i) + 1)))
      = ∑ i, (beta * (p' i * E i)
          + (Real.log Z - 1) * p' i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hlogval i]
        ring
  _ = beta * (∑ i, p' i * E i) + (Real.log Z - 1) * ∑ i, p' i := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  _ = beta * ∑ i, p' i * E i := by
        rw [hsum0, mul_zero, add_zero]

/-- `prop:kms` (Clausius identity): with `T = 1/β`, the heat flux is
`δQ = δ⟨E⟩ = T·δS`. -/
theorem clausius_identity {dS dE T beta : ℝ} (hbeta : beta ≠ 0)
    (hT : T = 1 / beta) (hfirst : dS = beta * dE) :
    dE = T * dS := by
  rw [hT, hfirst]
  field_simp

end NCG
