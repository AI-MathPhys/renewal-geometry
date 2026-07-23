/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Lorentz.DobrushinMixing

/-!
# Convergence to the stationary state

The ergodic capstone of the mixing clause of
`thm:common-origin-balance` (`manuscripts/renewal_emergence/renewal_emergence.tex`): the geometric
`ℓ¹` rate bound of `heatBath_exponential_mixing` upgrades to actual
**convergence**.

* `kernelPow_stationary` — a stationary law of a kernel is stationary
  for all its iterates;
* `heatBath_converges` — for any initial probability law `π₀` and any
  stationary probability law `π`, the `ℓ¹` distance
  `‖π₀ K^{|Λ|·k} − π‖₁ → 0` as `k → ∞`.

Combined with `heatBath_stationary_unique` (uniqueness of the
stationary probability law) and `gibbs_stationary` (existence, via
the normalized Gibbs weight), this is the finite-volume ergodic
content of the manuscript's exponential-mixing conclusion: the
resolved Gibbs law is the unique faithful finite-volume stationary
state and the dynamics converges to it from every start.
-/

namespace NCG.CommonOrigin

open Matrix Filter Topology

variable {D : Type*} [Fintype D] [DecidableEq D] [Nonempty D]

/-- A stationary law of a kernel is stationary for all iterates. -/
theorem kernelPow_stationary {Q : D → D → ℝ} {π : D → ℝ}
    (hstat : ∀ b, ∑ a, π a * Q a b = π b) :
    ∀ (k : ℕ) (b : D), ∑ a, π a * kernelPow Q k a b = π b := by
  intro k
  induction k with
  | zero =>
    intro b
    have h : ∀ a, π a * (kernelPow Q 0) a b
        = if a = b then π a else 0 := by
      intro a
      show π a * (if a = b then (1 : ℝ) else 0)
        = if a = b then π a else 0
      split <;> simp
    rw [Finset.sum_congr rfl fun a _ => h a,
      Finset.sum_ite_eq' Finset.univ b π]
    simp
  | succ k ih =>
    intro b
    have hrec : ∑ a, π a * (kernelPow Q (k + 1)) a b
        = ∑ c, (∑ a, π a * Q a c) * (kernelPow Q k) c b := by
      have hexp : ∀ a, π a * (kernelPow Q (k + 1)) a b
          = ∑ c, π a * Q a c * (kernelPow Q k) c b := by
        intro a
        rw [kernelPow_succ, Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        ring
      rw [Finset.sum_congr rfl fun a _ => hexp a, Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.sum_mul]
    rw [hrec, Finset.sum_congr rfl fun c _ => by rw [hstat c]]
    exact ih b

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **Convergence to the stationary state**
(`thm:common-origin-balance`, mixing clause, ergodic form): from any
initial probability law the heat-bath dynamics converges in `ℓ¹` to
any stationary probability law. -/
theorem heatBath_converges [Nonempty ι]
    (D : IsingData ι) (ν : ι → ℝ) (hν : ∀ i, 0 < ν i)
    (hν1 : ∑ i, ν i = 1)
    {π₀ π : (ι → Bool) → ℝ} (h0 : ∑ β, π₀ β = 1)
    (hπsum : ∑ β, π β = 1)
    (hπstat : ∀ β',
      ∑ β, π β * (heatBathMatrix D ν ^ Fintype.card ι) β β'
        = π β') :
    Tendsto (fun k => ∑ β',
        |(∑ β, π₀ β
          * (kernelPow
            (fun a b => (heatBathMatrix D ν
              ^ Fintype.card ι) a b) k) β β') - π β'|)
      atTop (nhds 0) := by
  classical
  obtain ⟨δ, hδpos, hcardδ, hmix⟩ :=
    heatBath_exponential_mixing D ν hν hν1
  set Q : (ι → Bool) → (ι → Bool) → ℝ :=
    fun a b => (heatBathMatrix D ν ^ Fintype.card ι) a b with hQ
  have hπpow : ∀ (k : ℕ) (β'),
      ∑ β, π β * (kernelPow Q k) β β' = π β' :=
    kernelPow_stationary hπstat
  -- contraction factor lies in [0, 1)
  have hcard1 : (1 : ℝ) ≤ Fintype.card (ι → Bool) := by
    have := Fintype.card_pos (α := ι → Bool)
    exact_mod_cast this
  have hcardδpos : 0 < Fintype.card (ι → Bool) * δ :=
    mul_pos (lt_of_lt_of_le one_pos hcard1) hδpos
  set ρ : ℝ := 1 - Fintype.card (ι → Bool) * δ with hρ
  have hρ0 : 0 ≤ ρ := by rw [hρ]; linarith
  have hρ1 : ρ < 1 := by rw [hρ]; linarith
  have hpow0 : Tendsto (fun k : ℕ => ρ ^ k) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1
  have hmaj : Tendsto
      (fun k : ℕ => ρ ^ k * ∑ β, |π₀ β - π β|) atTop
      (nhds 0) := by
    have h := hpow0.mul_const (∑ β, |π₀ β - π β|)
    rwa [zero_mul] at h
  refine squeeze_zero (fun k => ?_) (fun k => ?_) hmaj
  · exact Finset.sum_nonneg fun β' _ => abs_nonneg _
  · have heq : ∑ β', |(∑ β, π₀ β * (kernelPow Q k) β β') - π β'|
        = ∑ β', |(∑ β, π₀ β * (kernelPow Q k) β β')
            - (∑ β, π β * (kernelPow Q k) β β')| := by
      refine Finset.sum_congr rfl fun β' _ => ?_
      rw [hπpow k β']
    rw [heq]
    exact hmix k π₀ π h0 hπsum

end NCG.CommonOrigin
