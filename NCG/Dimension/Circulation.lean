/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Oriented reset circulation and the survival criterion

**Definition `def:circulation`** and the algebraic core of
**Theorem `thm:survival-criterion`**: the coarse-grained two-reset
response pairs the reset-pair law `p_{ab}` against an *alternating*
bilinear map (the commutator/wedge of Clifford directions), so only the
antisymmetric part `p^{[ab]} = (p_{ab} − p_{ba})/2` of the law survives:

* `NCG.pairResponse_eq_antisym` — `b_ren[ν] = Γ(Ξ(ν))`: the response
  equals its antisymmetrisation (the oriented-circulation form);
* `NCG.pairResponse_eq_zero_of_symm` — a parity (time-reversal)
  symmetric law (`p_{ab} = p_{ba}`) has vanishing response, **regardless
  of dimension**;
* `NCG.circulation`, `NCG.circulation_eq_zero_of_symm` — the oriented
  circulation bivector `Ξ(ν) ∈ ⋀²V` realised in the exterior algebra.

The degree bookkeeping (`Im H_ren ⊆ V_sp` iff `d = 3`) lives in
`thm:rg-eigenvalue`/`cor:relevance`; here we prove the statistical half:
survival under coarse-graining is exactly nonzero oriented circulation
(chirality) of the reset law. -/

namespace NCG

open Finset

variable {ι : Type*} [Fintype ι] {V W : Type*}
  [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

/-- The **two-reset pair response**: the reset-pair law `p` summed
against a bilinear pairing `w` of the reset directions `θ`
(Theorem `thm:survival-criterion`). -/
def pairResponse (p : ι → ι → ℝ) (θ : ι → V)
    (w : V →ₗ[ℝ] V →ₗ[ℝ] W) : W :=
  ∑ a, ∑ b, p a b • w (θ a) (θ b)

/-- An alternating pairing is skew. -/
theorem skew_of_alternating (w : V →ₗ[ℝ] V →ₗ[ℝ] W)
    (halt : ∀ v, w v v = 0) (u v : V) : w u v = -w v u := by
  have h := halt (u + v)
  simp only [map_add, LinearMap.add_apply, halt u, halt v, add_zero,
    zero_add] at h
  have h' : w u v + w v u = 0 := by
    rw [add_comm]
    exact h
  exact eq_neg_of_add_eq_zero_left h'

/-- Pairing a **symmetric** law against an alternating form gives zero —
the cancellation behind time-reversal symmetry killing the response. -/
theorem pairResponse_eq_zero_of_symm (p : ι → ι → ℝ) (θ : ι → V)
    (w : V →ₗ[ℝ] V →ₗ[ℝ] W) (halt : ∀ v, w v v = 0)
    (hp : ∀ a b, p a b = p b a) :
    pairResponse p θ w = 0 := by
  have key : pairResponse p θ w + pairResponse p θ w = 0 := by
    unfold pairResponse
    nth_rewrite 2 [Finset.sum_comm]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [hp b a, skew_of_alternating w halt (θ b) (θ a), smul_neg]
    exact add_neg_cancel _
  have h2 : (2:ℝ) • pairResponse p θ w = 0 := by
    rw [two_smul]
    exact key
  exact (smul_eq_zero.mp h2).resolve_left (by norm_num)

/-- **`b_ren[ν] = Γ(Ξ(ν))`** (Theorem `thm:survival-criterion`, algebraic
core): against an alternating pairing, the two-reset response equals the
response of the **antisymmetrised** law `p^{[ab]} = (p_{ab} − p_{ba})/2` —
only oriented circulation survives coarse-graining. -/
theorem pairResponse_eq_antisym (p : ι → ι → ℝ) (θ : ι → V)
    (w : V →ₗ[ℝ] V →ₗ[ℝ] W) (halt : ∀ v, w v v = 0) :
    pairResponse p θ w
      = pairResponse (fun a b => (p a b - p b a) / 2) θ w := by
  have hsym : pairResponse (fun a b => (p a b + p b a) / 2) θ w = 0 :=
    pairResponse_eq_zero_of_symm _ θ w halt fun a b => by ring
  have hsplit : pairResponse p θ w
      = pairResponse (fun a b => (p a b - p b a) / 2) θ w
        + pairResponse (fun a b => (p a b + p b a) / 2) θ w := by
    unfold pairResponse
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← add_smul]
    congr 1
    ring
  rw [hsplit, hsym, add_zero]

/-- **Definition `def:circulation`**: the **oriented reset circulation**
`Ξ(ν) = Σ p_{ab} θ_a ∧ θ_b ∈ ⋀²V` of a reset-pair law, realised in the
exterior algebra. -/
noncomputable def circulation (p : ι → ι → ℝ) (θ : ι → V) :
    ExteriorAlgebra ℝ V :=
  ∑ a, ∑ b, p a b •
    (ExteriorAlgebra.ι ℝ (θ a) * ExteriorAlgebra.ι ℝ (θ b))

/-- The wedge pairing as a bilinear map into the exterior algebra. -/
noncomputable def wedgePairing :
    V →ₗ[ℝ] V →ₗ[ℝ] ExteriorAlgebra ℝ V :=
  (LinearMap.mul ℝ (ExteriorAlgebra ℝ V)).compl₁₂
    (ExteriorAlgebra.ι ℝ) (ExteriorAlgebra.ι ℝ)

theorem wedgePairing_apply (u v : V) :
    wedgePairing u v = ExteriorAlgebra.ι ℝ u * ExteriorAlgebra.ι ℝ v :=
  rfl

theorem wedgePairing_alt (v : V) : wedgePairing (V := V) v v = 0 := by
  rw [wedgePairing_apply]
  exact ExteriorAlgebra.ι_sq_zero v

theorem circulation_eq_pairResponse (p : ι → ι → ℝ) (θ : ι → V) :
    circulation p θ = pairResponse p θ wedgePairing := rfl

/-- **Parity kills circulation** (Definition `def:circulation` /
Theorem `thm:survival-criterion`, vanishing half): a parity- (time-
reversal-) symmetric reset law has zero oriented circulation, hence zero
coarse-grained volume-dual response — in every dimension. -/
theorem circulation_eq_zero_of_symm (p : ι → ι → ℝ) (θ : ι → V)
    (hp : ∀ a b, p a b = p b a) :
    circulation p θ = 0 :=
  pairResponse_eq_zero_of_symm p θ wedgePairing wedgePairing_alt hp

/-- The circulation only sees the antisymmetric part of the law. -/
theorem circulation_eq_antisym (p : ι → ι → ℝ) (θ : ι → V) :
    circulation p θ
      = circulation (fun a b => (p a b - p b a) / 2) θ :=
  pairResponse_eq_antisym p θ wedgePairing wedgePairing_alt

/-- **Survival requires chirality** (Theorem `thm:survival-criterion` /
Theorem `thm:minimal-field` input): a reset law with nonzero oriented
circulation cannot be parity symmetric — some ordered pair is traversed
with a genuine handedness. -/
theorem chirality_of_circulation_ne_zero (p : ι → ι → ℝ) (θ : ι → V)
    (h : circulation p θ ≠ 0) : ∃ a b, p a b ≠ p b a := by
  by_contra hall
  push_neg at hall
  exact h (circulation_eq_zero_of_symm p θ hall)

/-- **Definition `def:degree-k-observable`** (algebraic encoding): the
canonical degree-`k` reset-interference observable — the `k`-fold
antisymmetrised reset difference, realised in the exterior algebra as
`𝒪ₖ = Σ_{a₁<…<a_k} (Π s_{a_l}) · θ_{a₁} ∧ … ∧ θ_{a_k}` with scalar
multipliers `s_a` (the reset-difference symbols of
`def:reset-differences`). -/
noncomputable def degreeKObservable {m : ℕ} (θ : Fin m → V)
    (s : Fin m → ℝ) (k : ℕ) : ExteriorAlgebra ℝ V :=
  ∑ A ∈ Finset.univ.powersetCard k,
    (∏ a ∈ A, s a) •
      ((A.sort (· ≤ ·)).map fun a => ExteriorAlgebra.ι ℝ (θ a)).prod

/-- Degree zero is the unit observable. -/
theorem degreeKObservable_zero {m : ℕ} (θ : Fin m → V)
    (s : Fin m → ℝ) : degreeKObservable θ s 0 = 1 := by
  simp [degreeKObservable]

end NCG
