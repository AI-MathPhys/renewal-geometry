/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Upstream.PointerAlgebra

/-!
# No-signalling for local record instruments (wavefunction, Phase 2)

`prop:no-signalling`: for a bipartite state `ρ_{AB}` and a
trace-preserving local record instrument on Alice's side
(`Σ_i K_i† K_i = 1`), Bob's nonselective reduced state is unchanged:

  `Σ_i Tr_A[(𝓘_i^A ⊗ id_B)(ρ)] = Tr_A ρ`.

Alice's factor is the pointer index `P`, Bob's the environment
index `E` of the existing `NCG.Upstream.slice` calculus; Bob's
reduced state is `Σ_a slice a a ρ`.

* `slice_kronOne_mul`, `slice_mul_kronOne` — how Alice-side
  operators `K ⊗ 1` act on slices;
* `bobState` — Bob's reduced state (partial trace over Alice);
* `no_signalling` — the nonselective invariance.  Bob can condition
  on Alice's outcome only after the record label itself enters his
  accessible algebra.
-/

namespace NCG
namespace Upstream

open Matrix Kronecker

variable {P E : Type*} [Fintype P] [Fintype E] [DecidableEq P]
  [DecidableEq E]

omit [DecidableEq P] in
/-- Left multiplication by an Alice-side operator `M ⊗ 1` mixes the
pointer row of a slice. -/
theorem slice_kronOne_mul (M : Matrix P P ℂ)
    (H : Matrix (P × E) (P × E) ℂ) (a b : P) :
    slice a b ((M ⊗ₖ (1 : Matrix E E ℂ)) * H)
      = ∑ p, M a p • slice p b H := by
  ext c d
  rw [slice_apply, Matrix.mul_apply]
  rw [Fintype.sum_prod_type]
  rw [Matrix.sum_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Matrix.smul_apply, slice_apply, smul_eq_mul]
  rw [Finset.sum_eq_single c]
  · rw [Matrix.kroneckerMap_apply, Matrix.one_apply_eq, mul_one]
  · intro e _ he
    rw [Matrix.kroneckerMap_apply, Matrix.one_apply_ne (Ne.symm he),
      mul_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ c) h

omit [DecidableEq P] in
/-- Right multiplication by an Alice-side operator `N ⊗ 1` mixes the
pointer column of a slice. -/
theorem slice_mul_kronOne (N : Matrix P P ℂ)
    (H : Matrix (P × E) (P × E) ℂ) (a b : P) :
    slice a b (H * (N ⊗ₖ (1 : Matrix E E ℂ)))
      = ∑ q, N q b • slice a q H := by
  ext c d
  rw [slice_apply, Matrix.mul_apply]
  rw [Fintype.sum_prod_type]
  rw [Matrix.sum_apply]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Matrix.smul_apply, slice_apply, smul_eq_mul]
  rw [Finset.sum_eq_single d]
  · rw [Matrix.kroneckerMap_apply, Matrix.one_apply_eq, mul_one]
    ring
  · intro e _ he
    rw [Matrix.kroneckerMap_apply, Matrix.one_apply_ne he,
      mul_zero, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ d) h

/-- Bob's reduced state: the partial trace of the bipartite state
over Alice's (pointer) factor. -/
def bobState (rho : Matrix (P × E) (P × E) ℂ) : Matrix E E ℂ :=
  ∑ a, slice a a rho

/-- `prop:no-signalling`: a trace-preserving local record instrument
on Alice's side (`Σ_i K_i† K_i = 1`) leaves Bob's nonselective
reduced state unchanged. -/
theorem no_signalling {κ : Type*} [Fintype κ]
    (K : κ → Matrix P P ℂ) (rho : Matrix (P × E) (P × E) ℂ)
    (hTP : ∑ i, (K i)ᴴ * K i = 1) :
    ∑ i, bobState ((K i ⊗ₖ (1 : Matrix E E ℂ)) * rho
        * ((K i)ᴴ ⊗ₖ (1 : Matrix E E ℂ)))
      = bobState rho := by
  unfold bobState
  have hslice : ∀ (i : κ) (a : P),
      slice a a ((K i ⊗ₖ (1 : Matrix E E ℂ)) * rho
        * ((K i)ᴴ ⊗ₖ (1 : Matrix E E ℂ)))
      = ∑ q, ∑ p, ((K i)ᴴ q a * K i a p) • slice p q rho := by
    intro i a
    rw [slice_mul_kronOne]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [slice_kronOne_mul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [smul_smul]
  calc ∑ i, ∑ a, slice a a ((K i ⊗ₖ (1 : Matrix E E ℂ)) * rho
        * ((K i)ᴴ ⊗ₖ (1 : Matrix E E ℂ)))
      = ∑ i, ∑ a, ∑ q, ∑ p,
          ((K i)ᴴ q a * K i a p) • slice p q rho := by
        refine Finset.sum_congr rfl fun i _ => ?_
        exact Finset.sum_congr rfl fun a _ => hslice i a
    _ = ∑ i, ∑ q, ∑ a, ∑ p,
          ((K i)ᴴ q a * K i a p) • slice p q rho := by
        refine Finset.sum_congr rfl fun i _ => ?_
        exact Finset.sum_comm
    _ = ∑ i, ∑ q, ∑ p, ∑ a,
          ((K i)ᴴ q a * K i a p) • slice p q rho := by
        refine Finset.sum_congr rfl fun i _ => ?_
        refine Finset.sum_congr rfl fun q _ => ?_
        exact Finset.sum_comm
    _ = ∑ q, ∑ i, ∑ p, ∑ a,
          ((K i)ᴴ q a * K i a p) • slice p q rho :=
        Finset.sum_comm
    _ = ∑ q, ∑ p, ∑ i, ∑ a,
          ((K i)ᴴ q a * K i a p) • slice p q rho := by
        refine Finset.sum_congr rfl fun q _ => ?_
        exact Finset.sum_comm
    _ = ∑ q, ∑ p, (∑ i, ∑ a, (K i)ᴴ q a * K i a p) • slice p q rho := by
        refine Finset.sum_congr rfl fun q _ => ?_
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.sum_smul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_smul]
    _ = ∑ q, ∑ p, ((1 : Matrix P P ℂ) q p) • slice p q rho := by
        refine Finset.sum_congr rfl fun q _ => ?_
        refine Finset.sum_congr rfl fun p _ => ?_
        congr 1
        calc ∑ i, ∑ a, (K i)ᴴ q a * K i a p
            = ∑ i, ((K i)ᴴ * K i) q p := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [Matrix.mul_apply]
          _ = (∑ i, (K i)ᴴ * K i) q p := by
              rw [Matrix.sum_apply]
          _ = (1 : Matrix P P ℂ) q p := by rw [hTP]
    _ = ∑ a, slice a a rho := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.sum_eq_single p]
        · rw [Matrix.one_apply_eq, one_smul]
        · intro q _ hq
          rw [Matrix.one_apply_ne hq, zero_smul]
        · intro h
          exact absurd (Finset.mem_univ p) h

end Upstream
end NCG
