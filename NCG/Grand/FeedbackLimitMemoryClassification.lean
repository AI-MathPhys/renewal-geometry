/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import NCG.Grand.FeedbackRealization

/-!
# Corrected feedback-limit memory classification

This file supplies the non-tautological scalar core of
`thm:feedback-limit-classification`: finite feedback rank is encoded by a
monic constant-coefficient recurrence, and the four summability/rank branches
are inhabited by explicit kernels.
-/

namespace NCG
namespace FeedbackLimitMemoryClassification

/-- A scalar feedback kernel has finite rational memory when one fixed monic
constant-coefficient recurrence propagates every delay. -/
def HasFiniteRecurrence (K : ℕ → ℝ) : Prop :=
  ∃ m : ℕ, 0 < m ∧ ∃ a : Fin m → ℝ,
    ∀ k, K (k + m) = ∑ j, a j * K (k + j)

def stableRationalMemory (K : ℕ → ℝ) : Prop :=
  HasFiniteRecurrence K ∧ Summable K

def persistentRationalMemory (K : ℕ → ℝ) : Prop :=
  HasFiniteRecurrence K ∧ ¬Summable K

def infiniteDimensionalShortMemory (K : ℕ → ℝ) : Prop :=
  ¬HasFiniteRecurrence K ∧ Summable K

def infiniteDimensionalLongMemory (K : ℕ → ℝ) : Prop :=
  ¬HasFiniteRecurrence K ∧ ¬Summable K

/-- A sparse, positive kernel supported on the positive perfect squares. -/
noncomputable def squareSpikeKernel (k : ℕ) : ℝ :=
  if (Nat.sqrt k) ^ 2 = k ∧ 0 < k then ((k + 1 : ℕ) : ℝ)⁻¹ ^ 2 else 0

theorem squareSpikeKernel_nonneg (k : ℕ) : 0 ≤ squareSpikeKernel k := by
  unfold squareSpikeKernel
  split_ifs
  · positivity
  · exact le_rfl

theorem squareSpikeKernel_le_pSeries (k : ℕ) :
    squareSpikeKernel k ≤ 1 / ((k + 1 : ℕ) : ℝ) ^ 2 := by
  unfold squareSpikeKernel
  split_ifs
  · simp [one_div, inv_pow]
  · positivity

theorem squareSpikeKernel_summable : Summable squareSpikeKernel := by
  apply Summable.of_nonneg_of_le squareSpikeKernel_nonneg
    squareSpikeKernel_le_pSeries
  have hp : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (2 : ℕ)) :=
    Real.summable_one_div_nat_pow.mpr (by omega)
  simpa [Function.comp_def] using hp.comp_injective Nat.succ_injective

private theorem positiveSquare_injective :
    Function.Injective (fun n : ℕ => (n + 1) ^ 2) := by
  intro a b h
  have hab : a + 1 = b + 1 := Nat.pow_left_injective (by omega) h
  omega

theorem squareSpikeKernel_at_square (n : ℕ) :
    squareSpikeKernel ((n + 1) ^ 2) =
      ((((n + 1) ^ 2 + 1 : ℕ) : ℝ)⁻¹) ^ 2 := by
  unfold squareSpikeKernel
  rw [if_pos]
  constructor
  · rw [Nat.sqrt_eq']
  · positivity

private theorem no_positive_square_immediately_before
    (m d : ℕ) (hm : 0 < m) (hd : 0 < d) (hdm : d ≤ m) :
    ¬((Nat.sqrt ((m + 1) ^ 2 - d)) ^ 2 = (m + 1) ^ 2 - d ∧
      0 < (m + 1) ^ 2 - d) := by
  rintro ⟨hsq, _⟩
  let n := Nat.sqrt ((m + 1) ^ 2 - d)
  have hdN : d ≤ (m + 1) ^ 2 := by nlinarith
  have hsub : (m + 1) ^ 2 - d < (m + 1) ^ 2 :=
    Nat.sub_lt (by positivity) hd
  have hlt : n ^ 2 < (m + 1) ^ 2 := by
    rw [show n ^ 2 = (m + 1) ^ 2 - d from hsq]
    exact hsub
  have hnm : n < m + 1 :=
    (Nat.pow_lt_pow_iff_left (by omega : 2 ≠ 0)).mp hlt
  have hupper : n ^ 2 ≤ m ^ 2 := by
    exact Nat.pow_le_pow_left (by omega) 2
  have hlower : m ^ 2 < (m + 1) ^ 2 - d := by
    apply Nat.lt_sub_of_add_lt
    nlinarith
  rw [hsq] at hupper
  omega

theorem squareSpikeKernel_before_square
    (m d : ℕ) (hm : 0 < m) (hd : 0 < d) (hdm : d ≤ m) :
    squareSpikeKernel ((m + 1) ^ 2 - d) = 0 := by
  unfold squareSpikeKernel
  rw [if_neg (no_positive_square_immediately_before m d hm hd hdm)]

theorem squareSpikeKernel_hasNoFiniteRecurrence :
    ¬HasFiniteRecurrence squareSpikeKernel := by
  rintro ⟨m, hm, a, hrec⟩
  let N := (m + 1) ^ 2
  have hmN : m ≤ N := by
    dsimp [N]
    nlinarith
  have hleft := hrec (N - m)
  have hNm : N - m + m = N := Nat.sub_add_cancel hmN
  rw [hNm] at hleft
  have hzero : ∀ j : Fin m, squareSpikeKernel (N - m + j) = 0 := by
    intro j
    let d := m - (j : ℕ)
    have hjlt : (j : ℕ) < m := j.isLt
    have hd : 0 < d := by dsimp [d]; omega
    have hdm : d ≤ m := Nat.sub_le _ _
    have hindex : N - m + (j : ℕ) = N - d := by
      dsimp [d]
      omega
    rw [hindex]
    exact squareSpikeKernel_before_square m d hm hd hdm
  simp_rw [hzero, mul_zero, Finset.sum_const_zero] at hleft
  rw [show N = (m + 1) ^ 2 from rfl,
    squareSpikeKernel_at_square m] at hleft
  have hpos :
      0 < (((((m + 1) ^ 2 + 1 : ℕ) : ℝ)⁻¹) ^ 2) := by positivity
  linarith

/-- The non-summable long-memory witness is a constant persistent background
plus the sparse infinite-rank perturbation. -/
noncomputable def longSpikeKernel (k : ℕ) : ℝ := 1 + squareSpikeKernel k

theorem longSpikeKernel_not_summable : ¬Summable longSpikeKernel := by
  intro h
  have hlim := h.tendsto_atTop_zero
  have hone : (1 : ℝ) ≤ 0 := ge_of_tendsto' hlim fun k => by
    unfold longSpikeKernel
    linarith [squareSpikeKernel_nonneg k]
  norm_num at hone

theorem geometricHalf_hasFiniteRecurrence :
    HasFiniteRecurrence (fun k : ℕ => ((1 : ℝ) / 2) ^ k) := by
  refine ⟨1, by omega, fun _ => (1 : ℝ) / 2, ?_⟩
  intro k
  simp [pow_succ]
  ring

theorem constantOne_hasFiniteRecurrence :
    HasFiniteRecurrence (fun _ : ℕ => (1 : ℝ)) := by
  refine ⟨1, by omega, fun _ => (1 : ℝ), ?_⟩
  intro k
  simp

theorem geometricHalf_summable :
    Summable (fun k : ℕ => ((1 : ℝ) / 2) ^ k) := by
  exact summable_geometric_of_lt_one (by norm_num) (by norm_num)

theorem constantOne_not_summable :
    ¬Summable (fun _ : ℕ => (1 : ℝ)) := by
  intro h
  have hlim := h.tendsto_atTop_zero
  have hone : (1 : ℝ) ≤ 0 := ge_of_tendsto' hlim fun _ => le_rfl
  norm_num at hone

theorem longSpikeKernel_hasNoFiniteRecurrence :
    ¬HasFiniteRecurrence longSpikeKernel := by
  rintro ⟨m, hm, a, hrec⟩
  let M := 2 * m
  let N := (M + 1) ^ 2
  have hM : 0 < M := by dsimp [M]; omega
  have hMN : M ≤ N := by dsimp [N]; nlinarith
  have hbefore : ∀ d, 0 < d → d ≤ M → longSpikeKernel (N - d) = 1 := by
    intro d hd hdM
    unfold longSpikeKernel
    rw [squareSpikeKernel_before_square M d hM hd hdM]
    ring
  have hbase := hrec (N - M)
  have hbaseTarget : N - M + m = N - m := by
    dsimp [M]
    omega
  rw [hbaseTarget, hbefore m hm (by dsimp [M]; omega)] at hbase
  have hbaseInput : ∀ j : Fin m, longSpikeKernel (N - M + j) = 1 := by
    intro j
    let d := M - (j : ℕ)
    have hd : 0 < d := by dsimp [d, M]; omega
    have hdM : d ≤ M := Nat.sub_le _ _
    have hindex : N - M + (j : ℕ) = N - d := by
      dsimp [d]
      omega
    rw [hindex, hbefore d hd hdM]
  simp_rw [hbaseInput, mul_one] at hbase
  have hspike := hrec (N - m)
  have hmN : m ≤ N := le_trans (by dsimp [M]; omega) hMN
  have hspikeTarget : N - m + m = N := Nat.sub_add_cancel hmN
  rw [hspikeTarget] at hspike
  have hspikeInput : ∀ j : Fin m, longSpikeKernel (N - m + j) = 1 := by
    intro j
    let d := m - (j : ℕ)
    have hd : 0 < d := by dsimp [d]; omega
    have hdM : d ≤ M := by dsimp [d, M]; omega
    have hindex : N - m + (j : ℕ) = N - d := by
      dsimp [d]
      omega
    rw [hindex, hbefore d hd hdM]
  simp_rw [hspikeInput, mul_one, ← hbase] at hspike
  unfold longSpikeKernel at hspike
  rw [show N = (M + 1) ^ 2 from rfl,
    squareSpikeKernel_at_square M] at hspike
  have hpos :
      0 < (((((M + 1) ^ 2 + 1 : ℕ) : ℝ)⁻¹) ^ 2) := by positivity
  linarith

/-- Every kernel lies in exactly one cell of the actual summability × finite
recurrence table. -/
theorem everyKernel_exactlyOneMemoryBranch (K : ℕ → ℝ) :
    (stableRationalMemory K ∨ persistentRationalMemory K ∨
      infiniteDimensionalShortMemory K ∨ infiniteDimensionalLongMemory K) ∧
    ¬(stableRationalMemory K ∧ persistentRationalMemory K) ∧
    ¬(stableRationalMemory K ∧ infiniteDimensionalShortMemory K) ∧
    ¬(stableRationalMemory K ∧ infiniteDimensionalLongMemory K) ∧
    ¬(persistentRationalMemory K ∧ infiniteDimensionalShortMemory K) ∧
    ¬(persistentRationalMemory K ∧ infiniteDimensionalLongMemory K) ∧
    ¬(infiniteDimensionalShortMemory K ∧ infiniteDimensionalLongMemory K) := by
  unfold stableRationalMemory persistentRationalMemory
    infiniteDimensionalShortMemory infiniteDimensionalLongMemory
  tauto

/-- All four corrected feedback-memory branches occur, with explicit kernels. -/
theorem allFourMemoryBranches_occur :
    (∃ K, stableRationalMemory K) ∧
    (∃ K, persistentRationalMemory K) ∧
    (∃ K, infiniteDimensionalShortMemory K) ∧
    (∃ K, infiniteDimensionalLongMemory K) := by
  refine ⟨⟨fun k => ((1 : ℝ) / 2) ^ k,
      geometricHalf_hasFiniteRecurrence, geometricHalf_summable⟩,
    ⟨fun _ => (1 : ℝ), constantOne_hasFiniteRecurrence,
      constantOne_not_summable⟩,
    ⟨squareSpikeKernel, squareSpikeKernel_hasNoFiniteRecurrence,
      squareSpikeKernel_summable⟩,
    ⟨longSpikeKernel, longSpikeKernel_hasNoFiniteRecurrence,
      longSpikeKernel_not_summable⟩⟩

/-- One recurrence reusable for an entire family of scalar geometric memories. -/
def HasReusableGeometricRecurrence (nodes : ℕ → ℝ) : Prop :=
  ∃ m : ℕ, 0 < m ∧ ∃ a : Fin m → ℝ,
    ∀ n k, nodes n ^ (k + m) = ∑ j, a j * nodes n ^ (k + j)

/-- Infinitely many distinct scalar transition poles cannot share one fixed
finite recurrence, even though each individual kernel has rank one. -/
theorem distinctPoles_haveNoReusableRecurrence
    (nodes : ℕ → ℝ) (hnodes : Function.Injective nodes) :
    ¬HasReusableGeometricRecurrence nodes := by
  rintro ⟨m, hm, a, hrec⟩
  let p : Polynomial ℝ :=
    Polynomial.X ^ m - ∑ j : Fin m,
      Polynomial.C (a j) * Polynomial.X ^ (j : ℕ)
  have hp : p ≠ 0 := by
    intro hp0
    have hsumzero :
        (∑ j : Fin m,
          Polynomial.C (a j) * Polynomial.X ^ (j : ℕ)).coeff m = 0 := by
      change Polynomial.lcoeff ℝ m
        (∑ j : Fin m, Polynomial.C (a j) * Polynomial.X ^ (j : ℕ)) = 0
      rw [map_sum]
      apply Finset.sum_eq_zero
      intro j _
      change (Polynomial.C (a j) * Polynomial.X ^ (j : ℕ)).coeff m = 0
      rw [Polynomial.coeff_C_mul]
      simp [show m ≠ (j : ℕ) from ne_of_gt j.isLt]
    have hcoeff : p.coeff m = 1 := by
      dsimp [p]
      rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, if_pos rfl,
        hsumzero]
      ring
    rw [hp0, Polynomial.coeff_zero] at hcoeff
    norm_num at hcoeff
  have hroot : Set.range nodes ⊆ {x : ℝ | p.IsRoot x} := by
    rintro x ⟨n, rfl⟩
    change p.eval (nodes n) = 0
    dsimp [p]
    rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
    have heval :
        Polynomial.eval (nodes n)
          (∑ j : Fin m, Polynomial.C (a j) * Polynomial.X ^ (j : ℕ)) =
          ∑ j : Fin m, a j * nodes n ^ (j : ℕ) := by
      change Polynomial.evalRingHom (nodes n)
          (∑ j : Fin m, Polynomial.C (a j) * Polynomial.X ^ (j : ℕ)) = _
      rw [map_sum]
      simp
    rw [heval]
    have h := hrec n 0
    simp only [zero_add] at h
    linarith
  have hrange : Set.Infinite (Set.range nodes) :=
    Set.infinite_range_of_injective hnodes
  have hinf : Set.Infinite {x : ℝ | p.IsRoot x} := hrange.mono hroot
  exact hp (Polynomial.eq_zero_of_infinite_isRoot p hinf)

/-- Companion transition attached to a monic scalar recurrence. -/
noncomputable def companionTransition {m : ℕ} (a : Fin m → ℝ) :
    Matrix (Fin m) (Fin m) ℝ := fun i j =>
  if h : (i : ℕ) + 1 < m then
    if (j : ℕ) = (i : ℕ) + 1 then 1 else 0
  else a j

def recurrenceState {m : ℕ} (K : ℕ → ℝ) (k : ℕ) : Fin m → ℝ :=
  fun j => K (k + (j : ℕ))

theorem companionTransition_mulVec_recurrenceState
    {m : ℕ} (hm : 0 < m) (a : Fin m → ℝ) (K : ℕ → ℝ)
    (hrec : ∀ k, K (k + m) = ∑ j, a j * K (k + j)) (k : ℕ) :
    Matrix.mulVec (companionTransition a) (recurrenceState K k) =
      recurrenceState K (k + 1) := by
  funext i
  change (∑ j, companionTransition a i j * recurrenceState K k j) = _
  unfold companionTransition recurrenceState
  by_cases hi : (i : ℕ) + 1 < m
  · simp only [dif_pos hi]
    rw [Finset.sum_eq_single ⟨(i : ℕ) + 1, hi⟩]
    · simp
      congr 1
      omega
    · intro j _ hj
      have hne : (j : ℕ) ≠ (i : ℕ) + 1 := by
        intro h
        apply hj
        exact Fin.ext h
      simp [hne]
    · simp
  · simp only [dif_neg hi]
    have hilast : (i : ℕ) + 1 = m := by omega
    rw [← hrec k]
    congr 1
    omega

/-- A common monic recurrence gives the usual one fixed companion carrier,
transition, source state and output coordinate reusable at every cutoff. -/
theorem commonRecurrence_companionRealization
    (K : ℕ → ℝ) {m : ℕ} (hm : 0 < m) (a : Fin m → ℝ)
    (hrec : ∀ k, K (k + m) = ∑ j, a j * K (k + j)) :
    let D := companionTransition a
    let source := recurrenceState K 0
    let output : (Fin m → ℝ) → ℝ := fun v => v ⟨0, hm⟩
    ∀ k, output (Matrix.mulVec (D ^ k) source) = K k := by
  dsimp only
  have hstate : ∀ k,
      Matrix.mulVec (companionTransition a ^ k) (recurrenceState K 0) =
        recurrenceState K k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ', ← Matrix.mulVec_mulVec, ih,
          companionTransition_mulVec_recurrenceState hm a K hrec]
  intro k
  rw [hstate]
  unfold recurrenceState
  simp

/-- Arbitrarily sampled finite scalar Hankel minor. -/
def sampledHankel (K : ℕ → ℝ) {r : ℕ}
    (rows cols : Fin r → ℕ) : Matrix (Fin r) (Fin r) ℝ :=
  fun i j => K (rows i + cols j)

/-- Rank at most `M`, expressed intrinsically by vanishing of every sampled
Hankel minor of order larger than `M`. -/
def HankelRankAtMost (M : ℕ) (K : ℕ → ℝ) : Prop :=
  ∀ (r : ℕ) (rows cols : Fin r → ℕ), M < r →
    Matrix.det (sampledHankel K rows cols) = 0

theorem sampledHankel_tendsto_of_fixedDelayConvergence
    (family : ℕ → ℕ → ℝ) (K : ℕ → ℝ)
    (hconv : ∀ k, Filter.Tendsto (fun n => family n k)
      Filter.atTop (nhds (K k)))
    {r : ℕ} (rows cols : Fin r → ℕ) :
    Filter.Tendsto (fun n => sampledHankel (family n) rows cols)
      Filter.atTop (nhds (sampledHankel K rows cols)) := by
  apply tendsto_pi_nhds.2
  intro i
  apply tendsto_pi_nhds.2
  intro j
  exact hconv (rows i + cols j)

/-- Every finite Hankel minor passes to a fixed-delay pointwise limit. -/
theorem sampledHankelDet_tendsto_of_fixedDelayConvergence
    (family : ℕ → ℕ → ℝ) (K : ℕ → ℝ)
    (hconv : ∀ k, Filter.Tendsto (fun n => family n k)
      Filter.atTop (nhds (K k)))
    {r : ℕ} (rows cols : Fin r → ℕ) :
    Filter.Tendsto
      (fun n => Matrix.det (sampledHankel (family n) rows cols))
      Filter.atTop (nhds (Matrix.det (sampledHankel K rows cols))) := by
  exact (continuous_id.matrix_det.tendsto _).comp
    (sampledHankel_tendsto_of_fixedDelayConvergence family K hconv rows cols)

/-- A uniform finite-stage Hankel-rank bound survives fixed-delay convergence.
This is the finite-minor passage used before the canonical Hankel realization. -/
theorem hankelRankAtMost_limit
    (family : ℕ → ℕ → ℝ) (K : ℕ → ℝ) (M : ℕ)
    (hconv : ∀ k, Filter.Tendsto (fun n => family n k)
      Filter.atTop (nhds (K k)))
    (hrank : ∀ n, HankelRankAtMost M (family n)) :
    HankelRankAtMost M K := by
  intro r rows cols hMr
  have hlim := sampledHankelDet_tendsto_of_fixedDelayConvergence
    family K hconv rows cols
  apply tendsto_nhds_unique hlim
  have hconst : Filter.Tendsto (fun _ : ℕ => (0 : ℝ))
      Filter.atTop (nhds 0) := tendsto_const_nhds
  apply hconst.congr'
  exact Filter.Eventually.of_forall fun n => (hrank n r rows cols hMr).symm

/-- Exact corrected feedback-memory package: exclusive classification, four
inhabited branches, closure of bounded Hankel rank under fixed-delay limits,
the distinct-pole obstruction to one reusable recurrence, and the companion
realization supplied by any common recurrence. -/
theorem correctedFeedbackMemoryClassification :
    (∀ K : ℕ → ℝ, stableRationalMemory K ∨ persistentRationalMemory K ∨
      infiniteDimensionalShortMemory K ∨ infiniteDimensionalLongMemory K) ∧
    ((∃ K, stableRationalMemory K) ∧
      (∃ K, persistentRationalMemory K) ∧
      (∃ K, infiniteDimensionalShortMemory K) ∧
      (∃ K, infiniteDimensionalLongMemory K)) ∧
    (∀ (family : ℕ → ℕ → ℝ) (K : ℕ → ℝ) (M : ℕ),
      (∀ k, Filter.Tendsto (fun n => family n k)
        Filter.atTop (nhds (K k))) →
      (∀ n, HankelRankAtMost M (family n)) → HankelRankAtMost M K) ∧
    (∀ (nodes : ℕ → ℝ), Function.Injective nodes →
      ¬HasReusableGeometricRecurrence nodes) := by
  refine ⟨fun K => (everyKernel_exactlyOneMemoryBranch K).1,
    allFourMemoryBranches_occur, ?_, distinctPoles_haveNoReusableRecurrence⟩
  intro family K M hconv hrank
  exact hankelRankAtMost_limit family K M hconv hrank

end FeedbackLimitMemoryClassification
end NCG
