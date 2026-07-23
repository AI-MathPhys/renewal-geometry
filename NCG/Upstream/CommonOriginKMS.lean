/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Upstream.CommonOriginUCP

/-!
# KMS self-adjointness of the common-origin channel

The channel-level clause of `thm:common-origin-balance`
(`manuscripts/renewal_emergence/renewal_emergence.tex`): the complete resolved channel `K̂_Λ` is
self-adjoint for the symmetric KMS pairing of the resolved Gibbs
state `μ̂_{Λ,θ} = μ_{Λ,θ} ⊗ τ_S`,

`⟨K̂_Λ F, G⟩_μ = ⟨F, K̂_Λ G⟩_μ`,
`⟨F, G⟩_μ = Σ_η μ(η) Tr(F(η)* G(η))`.

The proof combines, per elementary branch `(i, s, a, b)`:

* the Hilbert–Schmidt self-adjointness of the internal map
  (hypothesis `hΨsa`, proved for the manuscript instances by
  `adMap_hs_selfadjoint`/`trMap_hs_selfadjoint`);
* the **boxed resolved transition balance** (`resolved_balance`);
* reindexing by the elementary-transition involution
  `(η, s) ↦ (η^{i,s}, η_i)` on configurations × redraw values
  (`exchangeEquiv`).

Configurations are enumerated as Boolean spin assignments through
`spinCfg`; the pairing uses the unnormalized trace (the `1/4` of
`τ_S` scales both sides equally).
-/

namespace NCG.CommonOrigin

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The spin value of a Boolean label. -/
def spinVal (t : Bool) : ℝ := if t then 1 else -1

/-- The spin configuration of a Boolean assignment. -/
def spinCfg (β : ι → Bool) : ι → ℝ := fun j => spinVal (β j)

omit [Fintype ι] in
theorem spinCfg_update (β : ι → Bool) (i : ι) (t : Bool) :
    spinCfg (Function.update β i t)
      = Function.update (spinCfg β) i (spinVal t) := by
  funext j
  by_cases hj : j = i
  · rw [hj]
    change spinVal (Function.update β i t i)
      = Function.update (spinCfg β) i (spinVal t) i
    rw [Function.update_self, Function.update_self]
  · change spinVal (Function.update β i t j)
      = Function.update (spinCfg β) i (spinVal t) j
    rw [Function.update_of_ne hj, Function.update_of_ne hj]
    rfl

/-- The elementary-transition exchange `(η, s) ↦ (η^{i,s}, η_i)`. -/
def exchangeMap (i : ι) :
    ((ι → Bool) × Bool) → ((ι → Bool) × Bool) :=
  fun p => (Function.update p.1 i p.2, p.1 i)

omit [Fintype ι] in
theorem exchangeMap_involutive (i : ι) :
    Function.Involutive (exchangeMap (ι := ι) i) := by
  rintro ⟨β, t⟩
  refine Prod.ext ?_ ?_
  · change Function.update (Function.update β i t) i (β i) = β
    funext j
    by_cases hj : j = i
    · rw [hj, Function.update_self]
    · rw [Function.update_of_ne hj, Function.update_of_ne hj]
  · change (Function.update β i t) i = t
    rw [Function.update_self]

/-- The exchange as a permutation of elementary transitions. -/
def exchangeEquiv (i : ι) :
    Equiv.Perm ((ι → Bool) × Bool) :=
  Function.Involutive.toPerm _ (exchangeMap_involutive i)

omit [Fintype ι] in
@[simp] theorem exchangeEquiv_apply (i : ι)
    (p : (ι → Bool) × Bool) :
    exchangeEquiv i p = (Function.update p.1 i p.2, p.1 i) := rfl

namespace IsingData

variable (D : IsingData ι)

/-- The symmetric KMS pairing of the resolved Gibbs state
(unnormalized trace on the internal factor). -/
noncomputable def kmsPair (F G : Obs ι) : ℂ :=
  ∑ β : ι → Bool, ((D.gibbs (spinCfg β) : ℝ) : ℂ)
    * ((F (spinCfg β))ᴴ * G (spinCfg β)).trace

/-- **Elementary KMS exchange**: for a single branch label
`(i, a, b)`, summing the balanced weights against the exchanged
observables over all elementary transitions is symmetric — by the
boxed resolved balance, the internal self-adjointness, and the
transition involution. -/
theorem branch_kms_exchange (ν : ι → ℝ) (r : ι → Fin 3 → ℝ → ℝ)
    (κ : Fin 3 → ℝ)
    (Ψ : Fin 3 → Fin 3 →
      (Matrix (Fin 4) (Fin 4) ℂ →ₗ[ℂ] Matrix (Fin 4) (Fin 4) ℂ))
    (i : ι) (a b : Fin 3)
    (hΨsa : ∀ X Y : Matrix (Fin 4) (Fin 4) ℂ,
      ((Ψ a b X)ᴴ * Y).trace = (Xᴴ * Ψ a b Y).trace)
    (F G : Obs ι) :
    ∑ p : (ι → Bool) × Bool,
      ((D.gibbs (spinCfg p.1) : ℝ) : ℂ)
        * (((D.w ν r κ i (spinVal p.2) a b (spinCfg p.1) : ℝ) : ℂ)
          * ((Ψ a b (F (Function.update (spinCfg p.1) i
                (spinVal p.2))))ᴴ * G (spinCfg p.1)).trace)
    = ∑ p : (ι → Bool) × Bool,
      ((D.gibbs (spinCfg p.1) : ℝ) : ℂ)
        * (((D.w ν r κ i (spinVal p.2) a b (spinCfg p.1) : ℝ) : ℂ)
          * ((F (spinCfg p.1))ᴴ
            * Ψ a b (G (Function.update (spinCfg p.1) i
                (spinVal p.2)))).trace) := by
  set Rf : (ι → Bool) × Bool → ℂ := fun p =>
    ((D.gibbs (spinCfg p.1) : ℝ) : ℂ)
      * (((D.w ν r κ i (spinVal p.2) a b (spinCfg p.1) : ℝ) : ℂ)
        * ((F (spinCfg p.1))ᴴ
          * Ψ a b (G (Function.update (spinCfg p.1) i
              (spinVal p.2)))).trace) with hRf
  have hpt : ∀ p : (ι → Bool) × Bool,
      ((D.gibbs (spinCfg p.1) : ℝ) : ℂ)
        * (((D.w ν r κ i (spinVal p.2) a b (spinCfg p.1) : ℝ) : ℂ)
          * ((Ψ a b (F (Function.update (spinCfg p.1) i
                (spinVal p.2))))ᴴ * G (spinCfg p.1)).trace)
      = Rf (exchangeEquiv i p) := by
    rintro ⟨β, t⟩
    rw [hRf]
    dsimp only [exchangeEquiv_apply]
    rw [spinCfg_update]
    have hcol : Function.update
        (Function.update (spinCfg β) i (spinVal t)) i
          (spinVal (β i)) = spinCfg β := by
      rw [show spinVal (β i) = spinCfg β i from rfl,
        Function.update_idem, Function.update_eq_self]
    rw [hcol]
    have hbal := D.resolved_balance ν r κ i (spinVal t) a b
      (spinCfg β)
    have hbalC :
        ((D.gibbs (spinCfg β) : ℝ) : ℂ)
          * ((D.w ν r κ i (spinVal t) a b (spinCfg β) : ℝ) : ℂ)
        = ((D.gibbs (Function.update (spinCfg β) i (spinVal t))
              : ℝ) : ℂ)
          * ((D.w ν r κ i (spinCfg β i) a b
              (Function.update (spinCfg β) i (spinVal t)) : ℝ) : ℂ)
        := by
      exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) hbal
    rw [hΨsa, ← mul_assoc, ← mul_assoc,
      show spinVal (β i) = spinCfg β i from rfl, ← hbalC]
  calc ∑ p : (ι → Bool) × Bool,
      ((D.gibbs (spinCfg p.1) : ℝ) : ℂ)
        * (((D.w ν r κ i (spinVal p.2) a b (spinCfg p.1) : ℝ) : ℂ)
          * ((Ψ a b (F (Function.update (spinCfg p.1) i
                (spinVal p.2))))ᴴ * G (spinCfg p.1)).trace)
      = ∑ p : (ι → Bool) × Bool, Rf (exchangeEquiv i p) :=
        Finset.sum_congr rfl fun p _ => hpt p
    _ = ∑ p : (ι → Bool) × Bool, Rf p :=
        Equiv.sum_comp (exchangeEquiv i) Rf

omit [Fintype ι] in
/-- Trace expansion of a single branch against a test observable. -/
theorem branch_trace_left (ν : ι → ℝ) (r : ι → Fin 3 → ℝ → ℝ)
    (κ : Fin 3 → ℝ)
    (Ψ : Fin 3 → Fin 3 →
      (Matrix (Fin 4) (Fin 4) ℂ →ₗ[ℂ] Matrix (Fin 4) (Fin 4) ℂ))
    (i : ι) (s : ℝ) (a b : Fin 3) (F G : Obs ι) (η : ι → ℝ) :
    ((D.branch ν r κ Ψ i s a b F η)ᴴ * G η).trace
      = ((D.w ν r κ i s a b η : ℝ) : ℂ)
        * ((Ψ a b (F (Function.update η i s)))ᴴ * G η).trace := by
  change ((((D.w ν r κ i s a b η : ℝ) : ℂ)
      • Ψ a b (F (Function.update η i s)))ᴴ * G η).trace = _
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul,
    Matrix.trace_smul, smul_eq_mul, Complex.star_def,
    Complex.conj_ofReal]

omit [Fintype ι] in
/-- Trace expansion of a test observable against a single branch. -/
theorem branch_trace_right (ν : ι → ℝ) (r : ι → Fin 3 → ℝ → ℝ)
    (κ : Fin 3 → ℝ)
    (Ψ : Fin 3 → Fin 3 →
      (Matrix (Fin 4) (Fin 4) ℂ →ₗ[ℂ] Matrix (Fin 4) (Fin 4) ℂ))
    (i : ι) (s : ℝ) (a b : Fin 3) (F G : Obs ι) (η : ι → ℝ) :
    ((F η)ᴴ * D.branch ν r κ Ψ i s a b G η).trace
      = ((D.w ν r κ i s a b η : ℝ) : ℂ)
        * ((F η)ᴴ
          * Ψ a b (G (Function.update η i s))).trace := by
  change ((F η)ᴴ * (((D.w ν r κ i s a b η : ℝ) : ℂ)
      • Ψ a b (G (Function.update η i s)))).trace = _
  rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]

/-- **Theorem `thm:common-origin-balance` (KMS self-adjointness)**:
the complete resolved channel is self-adjoint for the symmetric KMS
pairing of the resolved Gibbs state. -/
theorem totalChannel_kms_selfadjoint (ν : ι → ℝ)
    (r : ι → Fin 3 → ℝ → ℝ) (κ : Fin 3 → ℝ)
    (Ψ : Fin 3 → Fin 3 →
      (Matrix (Fin 4) (Fin 4) ℂ →ₗ[ℂ] Matrix (Fin 4) (Fin 4) ℂ))
    (hΨsa : ∀ (a b : Fin 3) (X Y : Matrix (Fin 4) (Fin 4) ℂ),
      ((Ψ a b X)ᴴ * Y).trace = (Xᴴ * Ψ a b Y).trace)
    (F G : Obs ι) :
    D.kmsPair (D.totalChannel ν r κ Ψ F) G
      = D.kmsPair F (D.totalChannel ν r κ Ψ G) := by
  have hboolL : ∀ (β : ι → Bool) (i : ι) (a b : Fin 3),
      ((D.w ν r κ i 1 a b (spinCfg β) : ℝ) : ℂ)
          * ((Ψ a b (F (Function.update (spinCfg β) i 1)))ᴴ
            * G (spinCfg β)).trace
        + ((D.w ν r κ i (-1) a b (spinCfg β) : ℝ) : ℂ)
          * ((Ψ a b (F (Function.update (spinCfg β) i (-1))))ᴴ
            * G (spinCfg β)).trace
      = ∑ t : Bool,
          ((D.w ν r κ i (spinVal t) a b (spinCfg β) : ℝ) : ℂ)
            * ((Ψ a b (F (Function.update (spinCfg β) i
                (spinVal t))))ᴴ * G (spinCfg β)).trace := by
    intro β i a b
    rw [Fintype.sum_bool]
    rfl
  have hboolR : ∀ (β : ι → Bool) (i : ι) (a b : Fin 3),
      ((D.w ν r κ i 1 a b (spinCfg β) : ℝ) : ℂ)
          * ((F (spinCfg β))ᴴ
            * Ψ a b (G (Function.update (spinCfg β) i 1))).trace
        + ((D.w ν r κ i (-1) a b (spinCfg β) : ℝ) : ℂ)
          * ((F (spinCfg β))ᴴ
            * Ψ a b (G (Function.update (spinCfg β) i
                (-1)))).trace
      = ∑ t : Bool,
          ((D.w ν r κ i (spinVal t) a b (spinCfg β) : ℝ) : ℂ)
            * ((F (spinCfg β))ᴴ
              * Ψ a b (G (Function.update (spinCfg β) i
                  (spinVal t)))).trace := by
    intro β i a b
    rw [Fintype.sum_bool]
    rfl
  have hL : D.kmsPair (D.totalChannel ν r κ Ψ F) G
      = ∑ i, ∑ a, ∑ b, ∑ p : (ι → Bool) × Bool,
          ((D.gibbs (spinCfg p.1) : ℝ) : ℂ)
            * (((D.w ν r κ i (spinVal p.2) a b (spinCfg p.1)
                : ℝ) : ℂ)
              * ((Ψ a b (F (Function.update (spinCfg p.1) i
                    (spinVal p.2))))ᴴ * G (spinCfg p.1)).trace)
      := by
    rw [kmsPair]
    have h1 : ∀ β : ι → Bool,
        ((D.gibbs (spinCfg β) : ℝ) : ℂ)
          * (((D.totalChannel ν r κ Ψ F) (spinCfg β))ᴴ
            * G (spinCfg β)).trace
        = ∑ i, ∑ a, ∑ b, ∑ t : Bool,
            ((D.gibbs (spinCfg β) : ℝ) : ℂ)
              * (((D.w ν r κ i (spinVal t) a b (spinCfg β)
                  : ℝ) : ℂ)
                * ((Ψ a b (F (Function.update (spinCfg β) i
                      (spinVal t))))ᴴ * G (spinCfg β)).trace) := by
      intro β
      have h2 : (((D.totalChannel ν r κ Ψ F) (spinCfg β))ᴴ
          * G (spinCfg β)).trace
          = ∑ i, ∑ a, ∑ b,
              (((D.branch ν r κ Ψ i 1 a b F (spinCfg β))ᴴ
                  * G (spinCfg β)).trace
                + ((D.branch ν r κ Ψ i (-1) a b F (spinCfg β))ᴴ
                    * G (spinCfg β)).trace) := by
        change ((∑ i, ∑ a, ∑ b,
            (D.branch ν r κ Ψ i 1 a b F (spinCfg β)
              + D.branch ν r κ Ψ i (-1) a b F (spinCfg β)))ᴴ
          * G (spinCfg β)).trace = _
        simp only [Matrix.conjTranspose_sum,
          Matrix.conjTranspose_add, Finset.sum_mul,
          Matrix.add_mul, Matrix.trace_sum, Matrix.trace_add]
      rw [h2]
      simp only [D.branch_trace_left, hboolL β]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.mul_sum]
    rw [Finset.sum_congr rfl fun β _ => h1 β]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    exact (Fintype.sum_prod_type
      (f := fun p : (ι → Bool) × Bool =>
        ((D.gibbs (spinCfg p.1) : ℝ) : ℂ)
          * (((D.w ν r κ i (spinVal p.2) a b (spinCfg p.1)
              : ℝ) : ℂ)
            * ((Ψ a b (F (Function.update (spinCfg p.1) i
                  (spinVal p.2))))ᴴ
              * G (spinCfg p.1)).trace))).symm
  have hR : D.kmsPair F (D.totalChannel ν r κ Ψ G)
      = ∑ i, ∑ a, ∑ b, ∑ p : (ι → Bool) × Bool,
          ((D.gibbs (spinCfg p.1) : ℝ) : ℂ)
            * (((D.w ν r κ i (spinVal p.2) a b (spinCfg p.1)
                : ℝ) : ℂ)
              * ((F (spinCfg p.1))ᴴ
                * Ψ a b (G (Function.update (spinCfg p.1) i
                    (spinVal p.2)))).trace)
      := by
    rw [kmsPair]
    have h1 : ∀ β : ι → Bool,
        ((D.gibbs (spinCfg β) : ℝ) : ℂ)
          * ((F (spinCfg β))ᴴ
            * (D.totalChannel ν r κ Ψ G) (spinCfg β)).trace
        = ∑ i, ∑ a, ∑ b, ∑ t : Bool,
            ((D.gibbs (spinCfg β) : ℝ) : ℂ)
              * (((D.w ν r κ i (spinVal t) a b (spinCfg β)
                  : ℝ) : ℂ)
                * ((F (spinCfg β))ᴴ
                  * Ψ a b (G (Function.update (spinCfg β) i
                      (spinVal t)))).trace) := by
      intro β
      have h2 : ((F (spinCfg β))ᴴ
          * (D.totalChannel ν r κ Ψ G) (spinCfg β)).trace
          = ∑ i, ∑ a, ∑ b,
              (((F (spinCfg β))ᴴ
                  * D.branch ν r κ Ψ i 1 a b G (spinCfg β)).trace
                + ((F (spinCfg β))ᴴ
                    * D.branch ν r κ Ψ i (-1) a b G
                        (spinCfg β)).trace) := by
        change ((F (spinCfg β))ᴴ * (∑ i, ∑ a, ∑ b,
            (D.branch ν r κ Ψ i 1 a b G (spinCfg β)
              + D.branch ν r κ Ψ i (-1) a b G
                  (spinCfg β)))).trace = _
        simp only [Finset.mul_sum, Matrix.mul_add,
          Matrix.trace_sum, Matrix.trace_add]
      rw [h2]
      simp only [D.branch_trace_right, hboolR β]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.mul_sum]
    rw [Finset.sum_congr rfl fun β _ => h1 β]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    exact (Fintype.sum_prod_type
      (f := fun p : (ι → Bool) × Bool =>
        ((D.gibbs (spinCfg p.1) : ℝ) : ℂ)
          * (((D.w ν r κ i (spinVal p.2) a b (spinCfg p.1)
              : ℝ) : ℂ)
            * ((F (spinCfg p.1))ᴴ
              * Ψ a b (G (Function.update (spinCfg p.1) i
                  (spinVal p.2)))).trace))).symm
  rw [hL, hR]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun a _ => ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  exact D.branch_kms_exchange ν r κ Ψ i a b (hΨsa a b) F G

end IsingData

end NCG.CommonOrigin
