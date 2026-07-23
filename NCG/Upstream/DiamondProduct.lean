/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Lorentz.HeatBathPrimitivity

/-!
# The diamond product model and Gibbs-state invariance

Finite clauses of `cor:full-phase-nonempty` and clause (i) of
`thm:common-origin-phase` (`manuscripts/renewal_emergence/renewal_emergence.tex`):

* `gibbs_state_invariant` — the resolved Gibbs state `μ̂ = μ ⊗ τ` is
  **stationary** for the complete resolved channel:
  `⟨1, K̂F⟩_μ = ⟨1, F⟩_μ` (a corollary of the KMS self-adjointness
  and unitality);
* `diamondKernel` — the two-state diamond kernel `K_⋄(ζ,ζ') = 1/2`,
  idempotent, exchange covariant, with the uniform stationary law
  and **zero mean defect** for every exchange-odd test
  (`diamond_zero_defect`);
* `heatBathMatrix_deck` — the heat-bath marginal is deck covariant:
  `K(−β, −β') = K(β, β')`;
* `productKernel` — the local product `K ⊗ₖ K_⋄` of the
  common-origin marginal with the diamond kernel: row-stochastic
  (`productKernel_rowSum`), **entrywise positive at the `|Λ|`-th
  power** (`productKernel_pow_pos` — primitivity), exchange
  covariant (`productKernel_exchange`,
  `productKernel_deck_exchange`), and stationary for the product
  `π ⊗ (1/2)` of any stationary law with the uniform diamond law
  (`productKernel_stationary`).

The remaining clause of `cor:full-phase-nonempty` (criterion (C4) of
`ass:lorentzian-phase`: two extremal deck-related orientation states
with a selection) requires the thermodynamic limit and stays
unformalized, as does the continuum-regularity caveat the corollary
itself flags.
-/

namespace NCG.CommonOrigin

open Matrix Kronecker

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The spin box bound for Boolean configurations. -/
theorem spinCfg_box (β : ι → Bool) (j : ι) : |spinCfg β j| ≤ 1 := by
  show |spinVal (β j)| ≤ 1
  cases hb : β j <;> norm_num [spinVal]

/-- **Clause (i) of `thm:common-origin-phase` (stationarity)**: the
resolved Gibbs state is invariant under the complete resolved
channel. -/
theorem gibbs_state_invariant (D : IsingData ι) (ν : ι → ℝ)
    (r : ι → Fin 3 → ℝ → ℝ) (κ : Fin 3 → ℝ)
    (Ψ : Fin 3 → Fin 3 →
      (Matrix (Fin 4) (Fin 4) ℂ →ₗ[ℂ] Matrix (Fin 4) (Fin 4) ℂ))
    (hΨsa : ∀ (a b : Fin 3) (X Y : Matrix (Fin 4) (Fin 4) ℂ),
      ((Ψ a b X)ᴴ * Y).trace = (Xᴴ * Ψ a b Y).trace)
    (hΨ1 : ∀ a b, Ψ a b 1 = 1) (hν1 : ∑ i, ν i = 1)
    (hκ1 : ∑ b, κ b = 1)
    (hr1 : ∀ i u, |u| ≤ 1 → ∑ a, r i a u = 1) (F : Obs ι) :
    D.kmsPair (1 : Obs ι) (D.totalChannel ν r κ Ψ F)
      = D.kmsPair (1 : Obs ι) F := by
  have h1 := D.totalChannel_kms_selfadjoint ν r κ Ψ hΨsa
    (1 : Obs ι) F
  rw [← h1, IsingData.kmsPair, IsingData.kmsPair]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [D.totalChannel_unital hΨ1 hν1 hκ1 hr1 (spinCfg_box β)]
  rfl

/-! ## The two-state diamond kernel -/

/-- The two-state diamond kernel `K_⋄(ζ,ζ') = 1/2`. -/
noncomputable def diamondKernel : Matrix Bool Bool ℝ :=
  Matrix.of fun _ _ => (1 / 2 : ℝ)

theorem diamondKernel_pos (z z' : Bool) :
    0 < diamondKernel z z' := by
  norm_num [diamondKernel]

theorem diamondKernel_rowSum (z : Bool) :
    ∑ z', diamondKernel z z' = 1 := by
  rw [Fintype.sum_bool]
  norm_num [diamondKernel]

theorem diamondKernel_idem :
    diamondKernel * diamondKernel = diamondKernel := by
  ext z z'
  rw [Matrix.mul_apply, Fintype.sum_bool]
  norm_num [diamondKernel]

/-- Exchange covariance of the diamond kernel. -/
theorem diamondKernel_exchange (z z' : Bool) :
    diamondKernel (!z) (!z') = diamondKernel z z' := rfl

/-- The uniform diamond law is stationary. -/
theorem diamond_uniform_stationary (z' : Bool) :
    ∑ z, (1 / 2 : ℝ) * diamondKernel z z' = 1 / 2 := by
  rw [Fintype.sum_bool]
  norm_num [diamondKernel]

/-- **Zero mean defect**: every exchange-odd test has zero mean in
the uniform diamond law. -/
theorem diamond_zero_defect (d : Bool → ℝ)
    (hodd : ∀ z, d (!z) = -d z) :
    ∑ z, (1 / 2 : ℝ) * d z = 0 := by
  rw [Fintype.sum_bool]
  have h1 := hodd true
  simp only [Bool.not_true] at h1
  rw [h1]
  ring

/-! ## Deck covariance of the heat-bath marginal -/

theorem spinCfg_flip (γ : ι → Bool) :
    spinCfg (fun j => !γ j) = -(spinCfg γ) := by
  funext j
  show spinVal (!γ j) = -(spinVal (γ j))
  cases hb : γ j <;> norm_num [spinVal]

theorem spinVal_not (t : Bool) : spinVal (!t) = -spinVal t := by
  cases t <;> norm_num [spinVal]

/-- The Boolean flip as a permutation. -/
def notPerm : Equiv.Perm Bool :=
  Function.Involutive.toPerm Bool.not fun b => Bool.not_not b

@[simp] theorem notPerm_apply (b : Bool) : notPerm b = !b := rfl

/-- **Deck covariance of the heat-bath marginal**:
`K(−β, −β') = K(β, β')`. -/
theorem heatBathMatrix_deck (D : IsingData ι) (ν : ι → ℝ)
    (β β' : ι → Bool) :
    heatBathMatrix D ν (fun j => !β j) (fun j => !β' j)
      = heatBathMatrix D ν β β' := by
  classical
  have hupd : ∀ (i : ι) (t : Bool),
      ((fun j => !β' j) = Function.update (fun j => !β j) i t)
        ↔ β' = Function.update β i (!t) := by
    intro i t
    constructor
    · intro h
      funext j
      have h1 := congrFun h j
      by_cases hj : j = i
      · rw [hj] at h1 ⊢
        rw [Function.update_self] at h1 ⊢
        rw [← h1, Bool.not_not]
      · rw [Function.update_of_ne hj] at h1 ⊢
        cases hb : β' j <;> cases hc : β j <;> simp_all
    · intro h
      funext j
      have h1 := congrFun h j
      by_cases hj : j = i
      · rw [hj] at h1 ⊢
        rw [Function.update_self] at h1 ⊢
        rw [h1, Bool.not_not]
      · rw [Function.update_of_ne hj] at h1 ⊢
        rw [h1]
  show (∑ i, ∑ t : Bool,
      (if (fun j => !β' j) = Function.update (fun j => !β j) i t
        then ν i * D.q i (spinVal t) (spinCfg fun j => !β j)
        else 0))
    = ∑ i, ∑ t : Bool,
      (if β' = Function.update β i t
        then ν i * D.q i (spinVal t) (spinCfg β) else 0)
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Eq.trans (Finset.sum_congr rfl fun t _ => ?_)
    (Equiv.sum_comp notPerm (fun t : Bool =>
      if β' = Function.update β i t
        then ν i * D.q i (spinVal t) (spinCfg β) else 0))
  show (if (fun j => !β' j) = Function.update (fun j => !β j) i t
      then ν i * D.q i (spinVal t) (spinCfg fun j => !β j)
      else 0)
    = (if β' = Function.update β i (!t)
        then ν i * D.q i (spinVal (!t)) (spinCfg β) else 0)
  rw [spinCfg_flip, D.q_deck, ← spinVal_not]
  exact if_congr (hupd i t) rfl rfl

/-! ## The local product model -/

/-- The local product of the common-origin heat-bath marginal with
the two-state diamond kernel. -/
noncomputable def productKernel (D : IsingData ι) (ν : ι → ℝ) :
    Matrix ((ι → Bool) × Bool) ((ι → Bool) × Bool) ℝ :=
  heatBathMatrix D ν ⊗ₖ diamondKernel

theorem productKernel_apply (D : IsingData ι) (ν : ι → ℝ)
    (p p' : (ι → Bool) × Bool) :
    productKernel D ν p p'
      = heatBathMatrix D ν p.1 p'.1 * diamondKernel p.2 p'.2 := rfl

/-- The product kernel is row-stochastic. -/
theorem productKernel_rowSum (D : IsingData ι) (ν : ι → ℝ)
    (hν1 : ∑ i, ν i = 1) (p : (ι → Bool) × Bool) :
    ∑ p', productKernel D ν p p' = 1 := by
  rw [Fintype.sum_prod_type]
  have h1 : ∀ β' : ι → Bool,
      ∑ z' : Bool, productKernel D ν p (β', z')
        = heatBathMatrix D ν p.1 β' := by
    intro β'
    rw [show ∑ z' : Bool, productKernel D ν p (β', z')
        = ∑ z' : Bool, heatBathMatrix D ν p.1 β'
            * diamondKernel p.2 z' from rfl]
    rw [← Finset.mul_sum, diamondKernel_rowSum, mul_one]
  rw [Finset.sum_congr rfl fun β' _ => h1 β']
  exact heatBathMatrix_rowSum D ν hν1 p.1

/-- Kronecker powers factor. -/
theorem kron_pow (A : Matrix (ι → Bool) (ι → Bool) ℝ)
    (B : Matrix Bool Bool ℝ) (k : ℕ) :
    (A ⊗ₖ B) ^ k = (A ^ k) ⊗ₖ (B ^ k) := by
  induction k with
  | zero =>
    rw [pow_zero, pow_zero, pow_zero, Matrix.one_kronecker_one]
  | succ k ih =>
    rw [pow_succ, pow_succ, pow_succ, ih,
      Matrix.mul_kronecker_mul]

theorem diamondKernel_pow (k : ℕ) (hk : 1 ≤ k) :
    diamondKernel ^ k = diamondKernel := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · rw [pow_one]
    · rw [pow_succ, ih hkpos, diamondKernel_idem]

/-- **Primitivity of the product kernel**: the `|Λ|`-th power is
entrywise positive. -/
theorem productKernel_pow_pos [Nonempty ι] (D : IsingData ι)
    (ν : ι → ℝ) (hν : ∀ i, 0 < ν i)
    (p p' : (ι → Bool) × Bool) :
    0 < (productKernel D ν ^ Fintype.card ι) p p' := by
  have hN : 1 ≤ Fintype.card ι := Fintype.card_pos
  rw [productKernel, kron_pow, diamondKernel_pow _ hN]
  rcases p with ⟨β, z⟩
  rcases p' with ⟨β', z'⟩
  show 0 < (heatBathMatrix D ν ^ Fintype.card ι) β β'
    * diamondKernel z z'
  exact mul_pos (heatBathMatrix_pow_pos D ν hν β β')
    (diamondKernel_pos z z')

/-- Exchange covariance in the diamond factor. -/
theorem productKernel_exchange (D : IsingData ι) (ν : ι → ℝ)
    (p p' : (ι → Bool) × Bool) :
    productKernel D ν (p.1, !p.2) (p'.1, !p'.2)
      = productKernel D ν p p' := rfl

/-- Joint deck–diamond exchange covariance. -/
theorem productKernel_deck_exchange (D : IsingData ι) (ν : ι → ℝ)
    (p p' : (ι → Bool) × Bool) :
    productKernel D ν ((fun j => !p.1 j), !p.2)
        ((fun j => !p'.1 j), !p'.2)
      = productKernel D ν p p' := by
  rw [productKernel_apply, productKernel_apply,
    heatBathMatrix_deck]
  rfl

/-- **Stationarity of the product law**: the product of a stationary
law with the uniform diamond law is stationary for the product
kernel. -/
theorem productKernel_stationary (D : IsingData ι) (ν : ι → ℝ)
    {π : (ι → Bool) → ℝ}
    (hπ : ∀ β', ∑ β, π β * heatBathMatrix D ν β β' = π β')
    (p' : (ι → Bool) × Bool) :
    ∑ p, (π p.1 * (1 / 2)) * productKernel D ν p p'
      = π p'.1 * (1 / 2) := by
  rw [Fintype.sum_prod_type]
  have h1 : ∀ β : ι → Bool,
      ∑ z : Bool, (π β * (1 / 2))
          * productKernel D ν (β, z) p'
        = π β * heatBathMatrix D ν β p'.1 * (1 / 2) := by
    intro β
    rw [show ∑ z : Bool, (π β * (1 / 2))
        * productKernel D ν (β, z) p'
        = ∑ z : Bool, (π β * (1 / 2))
            * (heatBathMatrix D ν β p'.1
              * diamondKernel z p'.2) from rfl]
    rw [Fintype.sum_bool]
    show π β * (1 / 2) * (heatBathMatrix D ν β p'.1 * (1 / 2))
        + π β * (1 / 2) * (heatBathMatrix D ν β p'.1 * (1 / 2))
      = π β * heatBathMatrix D ν β p'.1 * (1 / 2)
    ring
  rw [Finset.sum_congr rfl fun β _ => h1 β, ← Finset.sum_mul]
  rw [Finset.sum_congr rfl fun β (_ : β ∈ Finset.univ) => rfl]
  rw [hπ p'.1]

end NCG.CommonOrigin
