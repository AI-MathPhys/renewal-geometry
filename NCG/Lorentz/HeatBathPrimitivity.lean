/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Lorentz.StochasticPressure
import NCG.Lorentz.StationaryExchange

/-!
# Primitivity and the unique stationary law of the heat-bath chain

The primitivity/uniqueness tail of `thm:common-origin-balance`
(`manuscripts/renewal_emergence/renewal_emergence.tex`), at the level of the classical scalar
marginal (the random-scan heat-bath chain `K_Λ` of
`prop:common-origin-ucp`):

* `heatBathMatrix_pow_pos` — **primitivity**: with all site weights
  positive, the `|Λ|`-th power of the heat-bath kernel has strictly
  positive entries (mismatch induction with lazy padding on the
  positive diagonal);
* `gibbs_stationary` — the Gibbs weight is **stationary**:
  `Σ_β μ(β) K(β,β') = μ(β')`, by resolving each transition against
  classical single-site detailed balance;
* `heatBath_stationary_unique` — **uniqueness**: any two stationary
  probability laws of the chain coincide (both are stationary for
  the entrywise-positive power, and the Dobrushin `L¹`-contraction
  uniqueness `stationary_unique_of_pos` applies).

Together with the exact resolved balance and KMS self-adjointness
already proved, this leaves only the resolved-channel (internal
factor) primitivity and the quantitative mixing rate of
`thm:common-origin-balance` unformalized.
-/

namespace NCG.CommonOrigin

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Positivity of powers by mismatch induction with lazy padding. -/
theorem pow_entry_pos_of_mismatch [Nonempty ι] (D : IsingData ι)
    (ν : ι → ℝ) (hν : ∀ i, 0 < ν i) :
    ∀ (n : ℕ) (β β' : ι → Bool),
      (Finset.univ.filter fun j => β j ≠ β' j).card ≤ n →
      0 < (heatBathMatrix D ν ^ n) β β' := by
  intro n
  induction n with
  | zero =>
    intro β β' hb
    have h1 : (Finset.univ.filter fun j => β j ≠ β' j) = ∅ :=
      Finset.card_eq_zero.mp (Nat.le_zero.mp hb)
    have h2 : β = β' := by
      funext j
      by_contra hj
      have h3 : j ∈ Finset.univ.filter fun j => β j ≠ β' j :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩
      rw [h1] at h3
      exact absurd h3 (Finset.notMem_empty j)
    rw [h2, pow_zero, Matrix.one_apply_eq]
    exact one_pos
  | succ n ih =>
    intro β β' hb
    have hstep : ∀ b1 : ι → Bool,
        0 < heatBathMatrix D ν β b1 →
        0 < (heatBathMatrix D ν ^ n) b1 β' →
        0 < (heatBathMatrix D ν ^ (n + 1)) β β' := by
      intro b1 h1 h2
      rw [pow_succ']
      have h3 : (heatBathMatrix D ν * heatBathMatrix D ν ^ n) β β'
          = ∑ w, heatBathMatrix D ν β w
              * (heatBathMatrix D ν ^ n) w β' := Matrix.mul_apply
      rw [h3]
      refine Finset.sum_pos' (fun w _ => mul_nonneg
        (heatBathMatrix_nonneg D ν (fun i => (hν i).le) β w)
        (entryNonneg_pow
          (heatBathMatrix_nonneg D ν fun i => (hν i).le) n w β'))
        ⟨b1, Finset.mem_univ b1, mul_pos h1 h2⟩
    by_cases hbeq : β = β'
    · refine hstep β ?_ (ih β β' (by
        have h4 : (Finset.univ.filter
            fun j => β j ≠ β' j).card = 0 := by
          rw [Finset.card_eq_zero]
          rw [Finset.filter_eq_empty_iff]
          intro j _
          rw [hbeq]
          exact not_ne_iff.mpr rfl
        omega))
      · exact heatBathMatrix_diag_pos D ν (fun i => (hν i).le)
          (Classical.arbitrary ι) (hν _) β
    · obtain ⟨i, hi⟩ := Function.ne_iff.mp hbeq
      refine hstep (Function.update β i (β' i))
        (heatBathMatrix_update_pos D ν hν β i (β' i))
        (ih _ β' ?_)
      have hfilter :
          (Finset.univ.filter
            fun j => Function.update β i (β' i) j ≠ β' j)
            = (Finset.univ.filter fun j => β j ≠ β' j).erase i := by
        ext j
        rw [Finset.mem_erase, Finset.mem_filter, Finset.mem_filter]
        constructor
        · intro hj
          by_cases hji : j = i
          · exfalso
            apply hj.2
            rw [hji, Function.update_self]
          · refine ⟨hji, Finset.mem_univ j, ?_⟩
            have h4 : Function.update β i (β' i) j = β j :=
              Function.update_of_ne hji _ _
            rw [← h4]
            exact hj.2
        · intro hj
          refine ⟨Finset.mem_univ j, ?_⟩
          have h4 : Function.update β i (β' i) j = β j :=
            Function.update_of_ne hj.1 _ _
          rw [h4]
          exact hj.2.2
      have hmem : i ∈ Finset.univ.filter fun j => β j ≠ β' j :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
      rw [hfilter, Finset.card_erase_of_mem hmem]
      omega

/-- **Primitivity of the heat-bath chain**: the `|Λ|`-th power of
the kernel is entrywise positive. -/
theorem heatBathMatrix_pow_pos [Nonempty ι] (D : IsingData ι)
    (ν : ι → ℝ) (hν : ∀ i, 0 < ν i) (β β' : ι → Bool) :
    0 < (heatBathMatrix D ν ^ Fintype.card ι) β β' := by
  refine pow_entry_pos_of_mismatch D ν hν _ β β' ?_
  calc (Finset.univ.filter fun j => β j ≠ β' j).card
      ≤ (Finset.univ : Finset ι).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
    _ = Fintype.card ι := Finset.card_univ

/-- The two-point redraw fibre: configurations `β` with
`β^{i,t} = β'` are exactly the `β'^{i,u}`, provided `β'_i = t`. -/
theorem redraw_fibre_sum (f : (ι → Bool) → ℝ) (β' : ι → Bool)
    (i : ι) (t : Bool) (hti : β' i = t) :
    ∑ β : ι → Bool, (if β' = Function.update β i t
        then f β else 0)
      = ∑ u : Bool, f (Function.update β' i u) := by
  classical
  have hkey : ∀ β : ι → Bool,
      β' = Function.update β i t
        ↔ ∃ u : Bool, β = Function.update β' i u := by
    intro β
    constructor
    · intro h
      refine ⟨β i, ?_⟩
      funext j
      by_cases hj : j = i
      · rw [hj, Function.update_self]
      · rw [Function.update_of_ne hj]
        have h6 := congrFun h j
        rw [Function.update_of_ne hj] at h6
        exact h6.symm
    · rintro ⟨u, rfl⟩
      funext j
      by_cases hj : j = i
      · rw [hj, Function.update_self]
        exact hti
      · rw [Function.update_of_ne hj, Function.update_of_ne hj]
  have hne : Function.update β' i true
      ≠ Function.update β' i false := by
    intro h
    have h1 := congrFun h i
    rw [Function.update_self, Function.update_self] at h1
    exact Bool.noConfusion h1
  have hsub : ∑ β : ι → Bool,
      (if β' = Function.update β i t then f β else 0)
      = ∑ β ∈ ({Function.update β' i true,
          Function.update β' i false} : Finset (ι → Bool)),
          (if β' = Function.update β i t then f β else 0) := by
    refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro β _ hβ
    rw [if_neg]
    intro hcon
    obtain ⟨u, hu⟩ := (hkey β).mp hcon
    apply hβ
    rw [Finset.mem_insert, Finset.mem_singleton]
    cases u
    · right
      exact hu
    · left
      exact hu
  rw [hsub, Finset.sum_pair hne, Fintype.sum_bool]
  have hcond : ∀ u : Bool,
      β' = Function.update (Function.update β' i u) i t := by
    intro u
    have h7 := (hkey (Function.update β' i u)).mpr ⟨u, rfl⟩
    exact h7
  rw [if_pos (hcond true), if_pos (hcond false)]

/-- **Stationarity of the Gibbs weight** for the heat-bath chain:
`Σ_β μ(β) K(β,β') = μ(β')` (the finite-volume stationary state of
`thm:common-origin-balance`, unnormalized). -/
theorem gibbs_stationary (D : IsingData ι) (ν : ι → ℝ)
    (hν1 : ∑ i, ν i = 1) (β' : ι → Bool) :
    ∑ β : ι → Bool, D.gibbs (spinCfg β) * heatBathMatrix D ν β β'
      = D.gibbs (spinCfg β') := by
  classical
  have h1 : ∑ β : ι → Bool,
      D.gibbs (spinCfg β) * heatBathMatrix D ν β β'
      = ∑ i, ∑ t : Bool, ∑ β : ι → Bool,
          (if β' = Function.update β i t
            then D.gibbs (spinCfg β)
              * (ν i * D.q i (spinVal t) (spinCfg β)) else 0) := by
    have h2 : ∀ β : ι → Bool,
        D.gibbs (spinCfg β) * heatBathMatrix D ν β β'
        = ∑ i, ∑ t : Bool,
            (if β' = Function.update β i t
              then D.gibbs (spinCfg β)
                * (ν i * D.q i (spinVal t) (spinCfg β)) else 0)
        := by
      intro β
      have h3 : heatBathMatrix D ν β β' = ∑ i, ∑ t : Bool,
          (if β' = Function.update β i t
            then ν i * D.q i (spinVal t) (spinCfg β) else 0) := rfl
      rw [h3, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      split
      · rfl
      · rw [mul_zero]
    rw [Finset.sum_congr rfl fun β _ => h2 β, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_comm
  rw [h1]
  have h4 : ∀ (i : ι) (t : Bool), ∑ β : ι → Bool,
      (if β' = Function.update β i t
        then D.gibbs (spinCfg β)
          * (ν i * D.q i (spinVal t) (spinCfg β)) else 0)
      = (if β' i = t then ν i * D.gibbs (spinCfg β') else 0) := by
    intro i t
    by_cases hti : β' i = t
    · rw [if_pos hti]
      rw [redraw_fibre_sum
        (fun β => D.gibbs (spinCfg β)
          * (ν i * D.q i (spinVal t) (spinCfg β))) β' i t hti]
      -- balance each fibre term back to β'
      have h5 : ∀ u : Bool,
          D.gibbs (spinCfg (Function.update β' i u))
            * (ν i * D.q i (spinVal t)
                (spinCfg (Function.update β' i u)))
          = ν i * (D.gibbs (spinCfg β')
              * D.q i (spinVal u) (spinCfg β')) := by
        intro u
        have hbal := D.heat_bath_balance i
          (spinCfg (Function.update β' i u)) (spinVal t)
        have harg : Function.update
            (spinCfg (Function.update β' i u)) i (spinVal t)
            = spinCfg β' := by
          rw [← spinCfg_update, Function.update_idem, ← hti,
            Function.update_eq_self]
        have hival : spinCfg (Function.update β' i u) i
            = spinVal u := by
          rw [spinCfg_update, Function.update_self]
        rw [harg, hival] at hbal
        calc D.gibbs (spinCfg (Function.update β' i u))
              * (ν i * D.q i (spinVal t)
                  (spinCfg (Function.update β' i u)))
            = ν i * (D.gibbs (spinCfg (Function.update β' i u))
                * D.q i (spinVal t)
                    (spinCfg (Function.update β' i u))) := by ring
          _ = ν i * (D.gibbs (spinCfg β')
                * D.q i (spinVal u) (spinCfg β')) := by rw [hbal]
      rw [Finset.sum_congr rfl fun u _ => h5 u]
      rw [Fintype.sum_bool]
      have h8 : spinVal true = (1 : ℝ) := rfl
      have h9 : spinVal false = (-1 : ℝ) := rfl
      rw [h8, h9, ← mul_add, ← mul_add, D.q_sum, mul_one]
    · rw [if_neg hti]
      refine Finset.sum_eq_zero fun β _ => ?_
      rw [if_neg]
      intro hcon
      apply hti
      have h6 := congrFun hcon i
      rw [Function.update_self] at h6
      exact h6
  rw [Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun t _ => h4 i t]
  have h7 : ∀ i : ι, ∑ t : Bool,
      (if β' i = t then ν i * D.gibbs (spinCfg β') else 0)
      = ν i * D.gibbs (spinCfg β') := by
    intro i
    rw [Finset.sum_ite_eq Finset.univ (β' i)
      (fun _ => ν i * D.gibbs (spinCfg β'))]
    rw [if_pos (Finset.mem_univ _)]
  rw [Finset.sum_congr rfl fun i _ => h7 i, ← Finset.sum_mul, hν1,
    one_mul]

/-- Stationary laws are stationary for every power. -/
theorem stationary_pow {K : Matrix (ι → Bool) (ι → Bool) ℝ}
    {π : (ι → Bool) → ℝ}
    (hπ : ∀ β', ∑ β, π β * K β β' = π β') :
    ∀ (n : ℕ) (β' : ι → Bool), ∑ β, π β * (K ^ n) β β' = π β' := by
  intro n
  induction n with
  | zero =>
    intro β'
    rw [Finset.sum_eq_single β']
    · rw [pow_zero, Matrix.one_apply_eq, mul_one]
    · intro β _ hβ
      rw [pow_zero, Matrix.one_apply_ne hβ, mul_zero]
    · intro hβ'
      exact absurd (Finset.mem_univ β') hβ'
  | succ n ih =>
    intro β'
    have h1 : ∀ β, π β * (K ^ (n + 1)) β β'
        = ∑ z, (π β * (K ^ n) β z) * K z β' := by
      intro β
      rw [pow_succ]
      have h2 : (K ^ n * K) β β' = ∑ z, (K ^ n) β z * K z β' :=
        Matrix.mul_apply
      rw [h2, Finset.mul_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      ring
    rw [Finset.sum_congr rfl fun β _ => h1 β, Finset.sum_comm]
    have h3 : ∀ z, ∑ β, (π β * (K ^ n) β z) * K z β'
        = π z * K z β' := by
      intro z
      rw [← Finset.sum_mul, ih z]
    rw [Finset.sum_congr rfl fun z _ => h3 z]
    exact hπ β'

/-- **Uniqueness of the stationary law**
(`thm:common-origin-balance`, uniqueness clause at the scalar
marginal level): any two stationary probability laws of the
heat-bath chain coincide. -/
theorem heatBath_stationary_unique [Nonempty ι] (D : IsingData ι)
    (ν : ι → ℝ) (hν : ∀ i, 0 < ν i) (hν1 : ∑ i, ν i = 1)
    {π π' : (ι → Bool) → ℝ}
    (hπ1 : ∑ β, π β = 1) (hπ'1 : ∑ β, π' β = 1)
    (hπ : ∀ β', ∑ β, π β * heatBathMatrix D ν β β' = π β')
    (hπ' : ∀ β', ∑ β, π' β * heatBathMatrix D ν β β' = π' β') :
    π = π' := by
  refine NCG.stationary_unique_of_pos
    (Q := fun β β' =>
      (heatBathMatrix D ν ^ Fintype.card ι) β β')
    (fun β β' => heatBathMatrix_pow_pos D ν hν β β')
    (fun β => rowStochastic_pow
      (heatBathMatrix_rowSum D ν hν1) (Fintype.card ι) β)
    hπ1 hπ'1 ?_ ?_
  · exact stationary_pow hπ (Fintype.card ι)
  · exact stationary_pow hπ' (Fintype.card ι)

end NCG.CommonOrigin
