/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Lorentz.PerronPressure
import NCG.Upstream.CommonOriginKMS

/-!
# The pressure zero of the depth-one transfer

The pressure-zero clause of `prop:common-origin-pressure-frame`
(`manuscripts/renewal_emergence/renewal_emergence.tex`): for an activity `𝔞 > 1` the depth-one
pressure transfer `B̂_z = 𝔞 e^{−z} K̂_Λ` has unique pressure zero
`β = log 𝔞`, and its Doob-normalized channel at the zero is `K̂_Λ`
itself.

In the eigenvector-free pressure development the spectral radius is
the Gelfand–Fekete growth rate `pRad`.  We prove:

* `pRad_stochastic` — a row-stochastic nonnegative kernel has
  `pRad = 1` (its entry-sum gauge is constant `= card V`);
* `heatBathMatrix` — the classical random-scan heat-bath marginal of
  the common-origin instrument as a transition matrix on Boolean spin
  configurations, with `heatBathMatrix_rowSum` (stochastic),
  `heatBathMatrix_nonneg`, and `heatBathMatrix_diag_pos`;
* `depth_one_transfer_rate` — `pRad(𝔞 e^{−z} • P) = 𝔞 e^{−z}` for
  any such stochastic kernel;
* `pressure_zero_unique` — `log pRad(B̂_z) = 0 ↔ z = log 𝔞`;
* `doob_normalized_at_zero` — at `z = log 𝔞` the transfer **is** the
  channel: `𝔞 e^{−log 𝔞} • P = P`.

The remaining clauses of the record (cover connectivity from
primitivity) stay conditional.
-/

namespace NCG

open Filter

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-- Row-stochasticity of a kernel. -/
def RowStochastic (P : Matrix V V ℝ) : Prop := ∀ x, ∑ y, P x y = 1

omit [Nonempty V] in
theorem rowStochastic_pow {P : Matrix V V ℝ}
    (hP : RowStochastic P) : ∀ k : ℕ, RowStochastic (P ^ k) := by
  intro k
  induction k with
  | zero =>
    intro x
    rw [pow_zero]
    rw [Finset.sum_eq_single x]
    · rw [Matrix.one_apply_eq]
    · intro y _ hy
      rw [Matrix.one_apply_ne (Ne.symm hy)]
    · intro hx
      exact absurd (Finset.mem_univ x) hx
  | succ k ih =>
    intro x
    rw [pow_succ']
    have h1 : ∀ y : V, (P * P ^ k) x y = ∑ z, P x z * (P ^ k) z y :=
      fun y => Matrix.mul_apply
    rw [Finset.sum_congr rfl fun y _ => h1 y, Finset.sum_comm]
    have h2 : ∀ z : V, ∑ y, P x z * (P ^ k) z y = P x z := by
      intro z
      rw [← Finset.mul_sum, ih z, mul_one]
    rw [Finset.sum_congr rfl fun z _ => h2 z]
    exact hP x

omit [Nonempty V] in
/-- The entry-sum gauge of a stochastic power is the state count. -/
theorem entrySum_pow_stochastic {P : Matrix V V ℝ}
    (hP : RowStochastic P) (k : ℕ) :
    entrySum (P ^ k) = (Fintype.card V : ℝ) := by
  rw [entrySum, Finset.sum_congr rfl fun x _ =>
    rowStochastic_pow hP k x]
  rw [Finset.sum_const]
  simp [Finset.card_univ]

/-- **A stochastic kernel has Gelfand–Fekete growth rate `1`.** -/
theorem pRad_stochastic {P : Matrix V V ℝ} (hne : EntryNonneg P)
    (hw : HasDiagWitness P) (hP : RowStochastic P) :
    pRad P = 1 := by
  have h1 := tendsto_growthSeq hne hw
  have h2 : (fun k : ℕ => growthSeq P k / k)
      = fun k : ℕ => Real.log (Fintype.card V) / k := by
    funext k
    rw [growthSeq, entrySum_pow_stochastic hP]
  rw [h2] at h1
  have h3 : Tendsto (fun k : ℕ => Real.log (Fintype.card V) / k)
      atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have h4 : Real.log (pRad P) = 0 := tendsto_nhds_unique h1 h3
  have h5 : pRad P = Real.exp (Real.log (pRad P)) :=
    (Real.exp_log (pRad_pos P)).symm
  rw [h5, h4, Real.exp_zero]

/-- **The depth-one pressure transfer rate**:
`pRad(𝔞 e^{−z} • P) = 𝔞 e^{−z}` for a stochastic kernel. -/
theorem depth_one_transfer_rate {P : Matrix V V ℝ}
    (hne : EntryNonneg P) (hw : HasDiagWitness P)
    (hP : RowStochastic P) {𝔞 : ℝ} (h𝔞 : 0 < 𝔞) (z : ℝ) :
    pRad ((𝔞 * Real.exp (-z)) • P) = 𝔞 * Real.exp (-z) := by
  have hc : 0 < 𝔞 * Real.exp (-z) :=
    mul_pos h𝔞 (Real.exp_pos _)
  rw [pRad_smul hne hw hc, pRad_stochastic hne hw hP, mul_one]

/-- **Unique pressure zero at `β = log 𝔞`**
(`prop:common-origin-pressure-frame`, pressure clause). -/
theorem pressure_zero_unique {P : Matrix V V ℝ}
    (hne : EntryNonneg P) (hw : HasDiagWitness P)
    (hP : RowStochastic P) {𝔞 : ℝ} (h𝔞 : 0 < 𝔞) (z : ℝ) :
    Real.log (pRad ((𝔞 * Real.exp (-z)) • P)) = 0
      ↔ z = Real.log 𝔞 := by
  rw [depth_one_transfer_rate hne hw hP h𝔞 z,
    Real.log_mul h𝔞.ne' (Real.exp_ne_zero _), Real.log_exp]
  constructor
  · intro h
    linarith
  · intro h
    rw [h]
    ring

omit [DecidableEq V] [Fintype V] in
omit [DecidableEq V] [Fintype V] [Nonempty V] in
/-- **Doob normalization at the pressure zero**: at `z = log 𝔞` the
depth-one transfer is the channel itself. -/
theorem doob_normalized_at_zero {𝔞 : ℝ} (h𝔞 : 0 < 𝔞)
    (P : Matrix V V ℝ) :
    (𝔞 * Real.exp (-Real.log 𝔞)) • P = P := by
  rw [Real.exp_neg, Real.exp_log h𝔞, mul_inv_cancel₀ h𝔞.ne',
    one_smul]

namespace CommonOrigin

open NCG.CommonOrigin

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The classical random-scan heat-bath marginal of the
common-origin instrument, as a transition matrix on Boolean spin
configurations. -/
noncomputable def heatBathMatrix (D : NCG.CommonOrigin.IsingData ι)
    (ν : ι → ℝ) : Matrix (ι → Bool) (ι → Bool) ℝ :=
  Matrix.of fun β β' => ∑ i, ∑ t : Bool,
    (if β' = Function.update β i t
      then ν i * D.q i (spinVal t) (spinCfg β) else 0)

theorem heatBathMatrix_nonneg (D : NCG.CommonOrigin.IsingData ι)
    (ν : ι → ℝ) (hν : ∀ i, 0 ≤ ν i) :
    EntryNonneg (heatBathMatrix D ν) := by
  intro β β'
  refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun t _ => ?_
  split
  · exact mul_nonneg (hν i) (D.q_pos i _ _).le
  · exact le_refl 0

/-- The heat-bath marginal is row-stochastic. -/
theorem heatBathMatrix_rowSum (D : NCG.CommonOrigin.IsingData ι)
    (ν : ι → ℝ) (hν1 : ∑ i, ν i = 1) :
    RowStochastic (heatBathMatrix D ν) := by
  intro β
  have h1 : ∑ β', heatBathMatrix D ν β β'
      = ∑ i, ∑ t : Bool, ∑ β' : ι → Bool,
          (if β' = Function.update β i t
            then ν i * D.q i (spinVal t) (spinCfg β) else 0) := by
    rw [show ∑ β', heatBathMatrix D ν β β'
        = ∑ β' : ι → Bool, ∑ i, ∑ t : Bool,
            (if β' = Function.update β i t
              then ν i * D.q i (spinVal t) (spinCfg β) else 0)
        from rfl]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
  rw [h1]
  have h2 : ∀ (i : ι) (t : Bool), ∑ β' : ι → Bool,
      (if β' = Function.update β i t
        then ν i * D.q i (spinVal t) (spinCfg β) else 0)
      = ν i * D.q i (spinVal t) (spinCfg β) := by
    intro i t
    rw [Finset.sum_ite_eq' Finset.univ (Function.update β i t)]
    rw [if_pos (Finset.mem_univ _)]
  rw [Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun t _ => h2 i t]
  have h3 : ∀ i : ι, ∑ t : Bool,
      ν i * D.q i (spinVal t) (spinCfg β) = ν i := by
    intro i
    rw [Fintype.sum_bool]
    have h4 : spinVal true = (1 : ℝ) := rfl
    have h5 : spinVal false = (-1 : ℝ) := rfl
    rw [h4, h5, ← mul_add, D.q_sum, mul_one]
  rw [Finset.sum_congr rfl fun i _ => h3 i]
  exact hν1

/-- The heat-bath marginal has a positive diagonal entry (redraw the
current value at a positively weighted site). -/
theorem heatBathMatrix_diag_pos (D : NCG.CommonOrigin.IsingData ι)
    (ν : ι → ℝ) (hν : ∀ i, 0 ≤ ν i) (i₀ : ι) (hν₀ : 0 < ν i₀)
    (β : ι → Bool) :
    0 < heatBathMatrix D ν β β := by
  have h1 : heatBathMatrix D ν β β
      = ∑ i, ∑ t : Bool,
          (if β = Function.update β i t
            then ν i * D.q i (spinVal t) (spinCfg β) else 0) := rfl
  rw [h1]
  refine Finset.sum_pos' (fun i _ => Finset.sum_nonneg
    fun t _ => ?_) ⟨i₀, Finset.mem_univ i₀, ?_⟩
  · split
    · exact mul_nonneg (hν i) (D.q_pos i _ _).le
    · exact le_refl 0
  · refine Finset.sum_pos' (fun t _ => ?_) ⟨β i₀, Finset.mem_univ _,
      ?_⟩
    · split
      · exact mul_nonneg (hν i₀) (D.q_pos i₀ _ _).le
      · exact le_refl 0
    · rw [if_pos (Function.update_eq_self i₀ β).symm]
      exact mul_pos hν₀ (D.q_pos i₀ _ _)

/-- The heat-bath marginal admits a diagonal growth witness. -/
theorem heatBathMatrix_diagWitness
    (D : NCG.CommonOrigin.IsingData ι) (ν : ι → ℝ)
    (hν : ∀ i, 0 ≤ ν i) (i₀ : ι) (hν₀ : 0 < ν i₀) :
    HasDiagWitness (heatBathMatrix D ν) := by
  refine ⟨Classical.arbitrary (ι → Bool), 1, le_refl 1, ?_⟩
  rw [pow_one]
  exact heatBathMatrix_diag_pos D ν hν i₀ hν₀ _

/-- **The pressure clause of `prop:common-origin-pressure-frame`
for the common-origin heat-bath marginal**: the depth-one transfer
`𝔞 e^{−z} • K_Λ` has growth rate `𝔞 e^{−z}`, unique pressure zero
`z = log 𝔞`, and Doob-normalized channel `K_Λ` at the zero. -/
theorem common_origin_pressure_zero
    (D : NCG.CommonOrigin.IsingData ι) (ν : ι → ℝ)
    (hν : ∀ i, 0 ≤ ν i) (hν1 : ∑ i, ν i = 1) (i₀ : ι)
    (hν₀ : 0 < ν i₀) {𝔞 : ℝ} (h𝔞 : 0 < 𝔞) (z : ℝ) :
    pRad ((𝔞 * Real.exp (-z)) • heatBathMatrix D ν)
        = 𝔞 * Real.exp (-z)
      ∧ (Real.log (pRad ((𝔞 * Real.exp (-z))
            • heatBathMatrix D ν)) = 0 ↔ z = Real.log 𝔞)
      ∧ (𝔞 * Real.exp (-Real.log 𝔞)) • heatBathMatrix D ν
          = heatBathMatrix D ν := by
  have hne := heatBathMatrix_nonneg D ν hν
  have hw := heatBathMatrix_diagWitness D ν hν i₀ hν₀
  have hst := heatBathMatrix_rowSum D ν hν1
  exact ⟨depth_one_transfer_rate hne hw hst h𝔞 z,
    pressure_zero_unique hne hw hst h𝔞 z,
    doob_normalized_at_zero h𝔞 _⟩

/-- Positivity of the single-flip transition entries. -/
theorem heatBathMatrix_update_pos (D : NCG.CommonOrigin.IsingData ι)
    (ν : ι → ℝ) (hν : ∀ i, 0 < ν i) (β : ι → Bool) (i : ι)
    (t : Bool) :
    0 < heatBathMatrix D ν β (Function.update β i t) := by
  have h1 : heatBathMatrix D ν β (Function.update β i t)
      = ∑ i', ∑ t' : Bool,
          (if Function.update β i t = Function.update β i' t'
            then ν i' * D.q i' (spinVal t') (spinCfg β) else 0)
      := rfl
  rw [h1]
  refine Finset.sum_pos' (fun i' _ => Finset.sum_nonneg
    fun t' _ => ?_) ⟨i, Finset.mem_univ i, ?_⟩
  · split
    · exact mul_nonneg (hν i').le (D.q_pos i' _ _).le
    · exact le_refl 0
  · refine Finset.sum_pos' (fun t' _ => ?_)
      ⟨t, Finset.mem_univ t, ?_⟩
    · split
      · exact mul_nonneg (hν i).le (D.q_pos i _ _).le
      · exact le_refl 0
    · rw [if_pos rfl]
      exact mul_pos (hν i) (D.q_pos i _ _)

/-- **Connectivity of the positive-support graph** (the clause of
`prop:common-origin-pressure-frame` that the manuscript derives from
primitivity): with all site weights positive, any configuration is
reachable from any other along positive-probability single-site
redraws. -/
theorem heatBathMatrix_support_connected
    (D : NCG.CommonOrigin.IsingData ι) (ν : ι → ℝ)
    (hν : ∀ i, 0 < ν i) (β β' : ι → Bool) :
    Relation.ReflTransGen
      (fun b b' => 0 < heatBathMatrix D ν b b') β β' := by
  classical
  have H : ∀ n : ℕ, ∀ b : ι → Bool,
      (Finset.univ.filter fun j => b j ≠ β' j).card ≤ n →
      Relation.ReflTransGen
        (fun b b' => 0 < heatBathMatrix D ν b b') b β' := by
    intro n
    induction n with
    | zero =>
      intro b hb
      have h1 : (Finset.univ.filter fun j => b j ≠ β' j) = ∅ :=
        Finset.card_eq_zero.mp (Nat.le_zero.mp hb)
      have h2 : b = β' := by
        funext j
        by_contra hj
        have h3 : j ∈ Finset.univ.filter fun j => b j ≠ β' j :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩
        rw [h1] at h3
        exact absurd h3 (Finset.notMem_empty j)
      rw [h2]
    | succ n ih =>
      intro b hb
      by_cases hbeq : b = β'
      · rw [hbeq]
      · obtain ⟨i, hi⟩ := Function.ne_iff.mp hbeq
        set b1 := Function.update b i (β' i) with hb1
        have hedge : 0 < heatBathMatrix D ν b b1 :=
          heatBathMatrix_update_pos D ν hν b i (β' i)
        have hfilter :
            (Finset.univ.filter fun j => b1 j ≠ β' j)
              = (Finset.univ.filter fun j => b j ≠ β' j).erase i
            := by
          ext j
          rw [Finset.mem_erase, Finset.mem_filter,
            Finset.mem_filter]
          constructor
          · intro hj
            by_cases hji : j = i
            · exfalso
              apply hj.2
              rw [hji, hb1, Function.update_self]
            · refine ⟨hji, Finset.mem_univ j, ?_⟩
              have h4 : b1 j = b j := by
                rw [hb1]
                exact Function.update_of_ne hji _ _
              rw [← h4]
              exact hj.2
          · intro hj
            refine ⟨Finset.mem_univ j, ?_⟩
            have h4 : b1 j = b j := by
              rw [hb1]
              exact Function.update_of_ne hj.1 _ _
            rw [h4]
            exact hj.2.2
        have hmem : i ∈ Finset.univ.filter fun j => b j ≠ β' j :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
        have hcard :
            (Finset.univ.filter fun j => b1 j ≠ β' j).card ≤ n := by
          rw [hfilter, Finset.card_erase_of_mem hmem]
          omega
        exact Relation.ReflTransGen.head hedge (ih b1 hcard)
  exact H _ β (le_refl _)

end CommonOrigin

end NCG
