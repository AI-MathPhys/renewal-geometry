/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.MarkedCycleChannel
import NCG.Grand.MarkedFirstReturnReconstruction
import NCG.Upstream.PrimitiveWeight

/-!
# Exact norm and stationary-state analysis for marked boundary cycles

This module starts from the survivor-effect estimate in the manuscript rather
than assuming decay of the return coefficients.  It derives the exponential
coefficient window, norm convergence, every polynomial duration moment in the
same window, closedness transfer to the limit channel, stationary-density
existence, and the stationary GNS contraction.
-/

open Matrix
open Filter
open scoped ComplexOrder MatrixOrder

namespace NCG

/-- Survivor-effect domination of each next first-return coefficient. -/
structure MarkedReturnExponentialWindow (V : Type*) [Norm V] [Zero V] where
  firstReturn : ℕ → V
  survivorEffectNorm : ℕ → ℝ
  boundConstant : ℝ
  decayRate : ℝ
  boundConstant_nonneg : 0 ≤ boundConstant
  decayRate_pos : 0 < decayRate
  zero : firstReturn 0 = 0
  return_le_survivor : ∀ n, ‖firstReturn (n + 1)‖ ≤ survivorEffectNorm n
  survivor_decay : ∀ n, survivorEffectNorm n ≤
    boundConstant * Real.exp (-(decayRate * (n : ℝ)))

namespace MarkedReturnExponentialWindow

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [CompleteSpace V]

/-- The manuscript's survivor bound implies exponential decay of the actual
first-return maps, with the harmless index-shift factor `exp α`. -/
theorem firstReturn_decay (W : MarkedReturnExponentialWindow V) :
    ∀ n, ‖W.firstReturn n‖ ≤
      (W.boundConstant * Real.exp W.decayRate) *
        Real.exp (-(W.decayRate * (n : ℝ))) := by
  intro n
  cases n with
  | zero =>
      rw [W.zero, norm_zero]
      exact mul_nonneg (mul_nonneg W.boundConstant_nonneg
        (Real.exp_nonneg _)) (Real.exp_nonneg _)
  | succ k =>
      calc
        ‖W.firstReturn (k + 1)‖ ≤ W.survivorEffectNorm k :=
          W.return_le_survivor k
        _ ≤ W.boundConstant * Real.exp (-(W.decayRate * (k : ℝ))) :=
          W.survivor_decay k
        _ = (W.boundConstant * Real.exp W.decayRate) *
            Real.exp (-(W.decayRate * ((k : ℝ) + 1))) := by
          rw [mul_assoc, ← Real.exp_add]
          congr 1
          ring
        _ = (W.boundConstant * Real.exp W.decayRate) *
            Real.exp (-(W.decayRate * ((k + 1 : ℕ) : ℝ))) := by
          norm_num

/-- The boundary-cycle series and every scalar-weighted pencil inside the
exponential disc converge in norm. -/
theorem firstReturn_and_pencil_summable
    (W : MarkedReturnExponentialWindow V) :
    Summable W.firstReturn ∧
      ∀ z : ℂ, ‖z‖ < Real.exp W.decayRate →
        Summable fun n : ℕ => ‖z‖ ^ n * ‖W.firstReturn n‖ := by
  have hdecay : ∀ n, ‖W.firstReturn n‖ ≤
      (W.boundConstant * Real.exp W.decayRate) *
        Real.exp (-W.decayRate * (n : ℝ)) := by
    intro n
    simpa only [neg_mul] using W.firstReturn_decay n
  have h := marked_cycle_channel W.firstReturn
    (W.boundConstant * Real.exp W.decayRate) W.decayRate
    W.decayRate_pos hdecay
  exact ⟨h.1, h.2.1⟩

/-- Every finite duration moment is normally summable throughout the same
disc.  At `z = 1`, these are precisely all finite return-duration moments. -/
theorem all_duration_moments_summable
    (W : MarkedReturnExponentialWindow V) (k : ℕ) (z : ℂ)
    (hz : ‖z‖ < Real.exp W.decayRate) :
    Summable fun n : ℕ =>
      (n : ℝ) ^ k * ‖z‖ ^ n * ‖W.firstReturn n‖ := by
  let r : ℝ := ‖z‖ * Real.exp (-W.decayRate)
  have hr0 : 0 ≤ r := mul_nonneg (norm_nonneg z) (Real.exp_nonneg _)
  have hr1 : r < 1 := by
    have h := mul_lt_mul_of_pos_right hz (Real.exp_pos (-W.decayRate))
    rwa [← Real.exp_add, add_neg_cancel, Real.exp_zero] at h
  have hs : Summable fun n : ℕ =>
      (W.boundConstant * Real.exp W.decayRate) * ((n : ℝ) ^ k * r ^ n) := by
    exact (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) k
      (by simpa [Real.norm_eq_abs, abs_of_nonneg hr0] using hr1)).mul_left _
  apply Summable.of_nonneg_of_le (fun _ => by positivity) _ hs
  intro n
  calc
    (n : ℝ) ^ k * ‖z‖ ^ n * ‖W.firstReturn n‖
        ≤ (n : ℝ) ^ k * ‖z‖ ^ n *
            ((W.boundConstant * Real.exp W.decayRate) *
              Real.exp (-(W.decayRate * (n : ℝ)))) := by
          exact mul_le_mul_of_nonneg_left (W.firstReturn_decay n) (by positivity)
    _ = (W.boundConstant * Real.exp W.decayRate) *
        ((n : ℝ) ^ k * r ^ n) := by
      simp only [r, mul_pow, ← Real.exp_nat_mul]
      ring

end MarkedReturnExponentialWindow

/-- A norm limit inherits every closed channel property enjoyed by all
finite partial first-return sums.  Instantiating the closed set with the
finite-dimensional CPTP cone gives the manuscript's limit-channel clause. -/
theorem summable_limit_mem_closed_channel_class
    {V : Type*} [NormedAddCommGroup V] [CompleteSpace V]
    (F : ℕ → V) (hF : Summable F) (K : Set V) (hK : IsClosed K)
    (hpartial : ∀ N, (∑ n ∈ Finset.range N, F n) ∈ K) :
    (∑' n, F n) ∈ K := by
  apply hK.mem_of_tendsto hF.hasSum.tendsto_sum_nat
  exact Filter.Eventually.of_forall hpartial

/-- The positive-semidefinite cone is closed for matrices over every finite
index type. -/
theorem isClosed_posSemidef_finite {ι : Type*} [Fintype ι] :
    IsClosed {A : Matrix ι ι ℂ | A.PosSemidef} := by
  have hentry : ∀ i j : ι,
      Continuous fun A : Matrix ι ι ℂ => A i j := fun i j =>
    (continuous_apply j).comp (continuous_apply i)
  have hquad : ∀ x : ι → ℂ,
      Continuous fun A : Matrix ι ι ℂ => star x ⬝ᵥ (A *ᵥ x) := by
    intro x
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply]
    refine continuous_finsetSum _ fun i _ => Continuous.mul continuous_const ?_
    exact continuous_finsetSum _ fun j _ =>
      Continuous.mul (hentry i j) continuous_const
  have heq : {A : Matrix ι ι ℂ | A.PosSemidef} =
      {A : Matrix ι ι ℂ | A.IsHermitian} ∩
        ⋂ x : ι → ℂ, {A : Matrix ι ι ℂ | 0 ≤ star x ⬝ᵥ (A *ᵥ x)} := by
    ext A
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    exact posSemidef_iff_dotProduct_mulVec
  rw [heq]
  refine IsClosed.inter ?_ (isClosed_iInter fun x => ?_)
  · refine isClosed_eq ?_ continuous_id
    refine continuous_matrix fun i j => ?_
    exact Continuous.star (hentry j i)
  · have hpre : {A : Matrix ι ι ℂ | 0 ≤ star x ⬝ᵥ (A *ᵥ x)} =
        (fun A : Matrix ι ι ℂ => star x ⬝ᵥ (A *ᵥ x)) ⁻¹'
          {z : ℂ | 0 ≤ z} := rfl
    rw [hpre]
    refine IsClosed.preimage (hquad x) ?_
    have horder : {z : ℂ | 0 ≤ z} =
        {z : ℂ | 0 ≤ z.re} ∩ {z : ℂ | z.im = 0} := by
      ext z
      simpa [eq_comm] using (Complex.nonneg_iff (z := z))
    rw [horder]
    exact (isClosed_le continuous_const Complex.continuous_re).inter
      (isClosed_eq Complex.continuous_im continuous_const)

/-- Complete positivity is closed under pointwise limits of finite matrix
operations. -/
theorem matrixCompletelyPositive_of_pointwise_limit {d : ℕ}
    (Φn : ℕ → FiniteMatrixOperation d) (Φ : FiniteMatrixOperation d)
    (hcp : ∀ n, IsMatrixCompletelyPositive (Φn n))
    (hlim : ∀ X, Filter.Tendsto (fun n => Φn n X) Filter.atTop
      (nhds (Φ X))) :
    IsMatrixCompletelyPositive Φ := by
  rw [choi_criterion]
  have hconv : Filter.Tendsto (fun n : ℕ => choiMatrix (Φn n))
      Filter.atTop (nhds (choiMatrix Φ)) := by
    refine tendsto_pi_nhds.mpr fun p => tendsto_pi_nhds.mpr fun q => ?_
    exact tendsto_pi_nhds.mp (tendsto_pi_nhds.mp
      (hlim (Matrix.single p.1 q.1 1)) p.2) q.2
  have hmem : ∀ᶠ n : ℕ in Filter.atTop,
      (choiMatrix (Φn n)).PosSemidef :=
    Filter.Eventually.of_forall fun n =>
      ((choi_criterion (Φn n)).mp (hcp n))
  exact (isClosed_posSemidef_finite
    (ι := Fin d × Fin d)).mem_of_tendsto hconv hmem

/-- Trace preservation is closed under pointwise limits. -/
theorem tracePreserving_of_pointwise_limit {d : ℕ}
    (Φn : ℕ → FiniteMatrixOperation d) (Φ : FiniteMatrixOperation d)
    (htrace : ∀ n X, (Φn n X).trace = X.trace)
    (hlim : ∀ X, Filter.Tendsto (fun n => Φn n X) Filter.atTop
      (nhds (Φ X))) :
    ∀ X, (Φ X).trace = X.trace := by
  intro X
  have ht : Filter.Tendsto (fun n => (Φn n X).trace) Filter.atTop
      (nhds ((Φ X).trace)) :=
    (Upstream.PrimitiveWeight.continuous_matrix_trace.tendsto _).comp (hlim X)
  have hc : Filter.Tendsto (fun _ : ℕ => X.trace) Filter.atTop
      (nhds X.trace) :=
    tendsto_const_nhds
  exact tendsto_nhds_unique ht (hc.congr' <|
    Filter.Eventually.of_forall fun n => (htrace n X).symm)

/-- A finite trace-preserving positive boundary channel has a stationary
density matrix.  This is the compact-Cesàro theorem used in the manuscript. -/
theorem markedCycle_exists_stationary_boundary_state {d : ℕ} (hd : 0 < d)
    (R : FiniteMatrixOperation d)
    (htrace : ∀ A, (R A).trace = A.trace)
    (hpositive : ∀ A : Matrix (Fin d) (Fin d) ℂ,
      A.PosSemidef → (R A).PosSemidef) :
    ∃ ρ ∈ Upstream.PrimitiveWeight.densitySet d ℂ, R ρ = ρ :=
  Upstream.PrimitiveWeight.exists_stationary_density hd htrace hpositive

/-- Kadison--Schwarz plus stationarity is exactly contraction of the
stationary GNS quadratic form. -/
theorem stationarySchwarz_gns_contraction
    {A : Type*} [Star A] [Mul A] [Preorder A]
    (Φ : A → A) (ω : A → ℝ)
    (hωmono : ∀ {a b}, a ≤ b → ω a ≤ ω b)
    (hstationary : ∀ a, ω (Φ a) = ω a)
    (hSchwarz : ∀ a, star (Φ a) * Φ a ≤ Φ (star a * a))
    (a : A) :
    ω (star (Φ a) * Φ a) ≤ ω (star a * a) := by
  calc
    ω (star (Φ a) * Φ a) ≤ ω (Φ (star a * a)) := hωmono (hSchwarz a)
    _ = ω (star a * a) := hstationary _

end NCG
