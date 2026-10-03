/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.RelationalSchedulerADM

/-!
# The winner–waiting score of a finite exponential race (`lem:supp-race-score`,
  emergent-spacetime manuscript)

Let a finite family of branches `ι` race with positive rates `k : ι → ℝ`, total rate
`K = Σ_a k_a`.  The joint law of the winner `A` and the first waiting time `T` is
`ℙ(A = a, T ∈ dt) = k_a e^{-K t} dt` on `t > 0` (`raceDensity`); expectations of observables
`F(A, T)` are `raceExpectation k F = Σ_a ∫_{t>0} F(a,t) k_a e^{-Kt} dt`.

For an ARBITRARY finite index type (in particular the twelve oriented `A₃` roots
`OrientedRoot = Fin 6 × Bool`):

* `raceExpectation_one`, `raceExpectation_winner`, `raceExpectation_waiting`,
  `raceExpectation_waiting_sq`, `raceDensity_factor`: the race law is a probability law, the
  winner has probability `p_b = k_b / K`, `𝔼T = 1/K`, `𝔼T² = 2/K²`, and the density factorizes
  as `p_a · K e^{-Kt}` (winner and waiting time are independent, `T ~ Exp(K)`).
* `hasDerivAt_log_raceDensity`: `s_b = 1_{A=b} - k_b T` is the derivative of the
  log-likelihood `log(k_A e^{-KT})` with respect to `log k_b` (the log-rate score).
* `scoreGram_eq` (`eq:supp-race-score-gram`): `𝔼[s_b s_c] = δ_{bc} k_b / K`;
  `scoreGram_posDef`: the score Gram is diagonal and positive definite.
* `winnerCovarianceGram_eq`: the winner indicators have covariance
  `𝔼[(1_{A=b} - p_b)(1_{A=c} - p_c)] = (diag(p) - p pᵀ)_{bc}`;
  `winnerCovariance_mulVec_one`, `winnerCovariance_det_eq_zero`,
  `winnerCovariance_not_posDef`: this covariance is singular in the all-ones direction;
  `winnerProb_smul`: winner probabilities are invariant under common rescaling (they lose the
  common rate scale), while `raceExpectation_waiting` shows `𝔼T` is not.
* `rates_eq_of_winner_waiting`: the rates are recovered as `k_b = ℙ(A=b)/𝔼T`, so the
  winner–waiting statistics are a faithful coordinate system for all positive rates;
  `exists_rates_ne_winnerProb_eq`: winner probabilities alone are not.
* `orientedRootRace_score_faithful`: the instantiation at the twelve oriented roots
  `±r_a` of the `A₃` root race (`Fintype.card OrientedRoot = 12`).
-/

open MeasureTheory Set Matrix Finset

noncomputable section

namespace RenewalGeometry
namespace RootRaceScore

/-- Exponential moments `∫₀^∞ tⁿ e^{-Kt} dt = n!/K^{n+1}`. -/
theorem integral_pow_mul_exp_neg (K : ℝ) (hK : 0 < K) (n : ℕ) :
    ∫ t in Ioi (0 : ℝ), t ^ n * Real.exp (-(K * t)) = n.factorial / K ^ (n + 1) := by
  have hsub := integral_comp_mul_left_Ioi (fun x => x ^ n * Real.exp (-x)) 0 hK
  simp only [mul_zero] at hsub
  have hL : (∫ x in Ioi (0 : ℝ), (K * x) ^ n * Real.exp (-(K * x)))
      = K ^ n * ∫ x in Ioi (0 : ℝ), x ^ n * Real.exp (-(K * x)) := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x _
    simp only [mul_pow]
    ring
  have hG : (∫ x in Ioi (0 : ℝ), x ^ n * Real.exp (-x)) = n.factorial := by
    have h1 := Real.Gamma_eq_integral (s := (n : ℝ) + 1) (by positivity)
    have h2 := Real.Gamma_nat_eq_factorial n
    rw [h1] at h2
    rw [← h2]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x _
    simp only [add_sub_cancel_right, Real.rpow_natCast]
    ring
  rw [hL, hG] at hsub
  have hKne : K ≠ 0 := ne_of_gt hK
  rw [smul_eq_mul] at hsub
  rw [pow_succ]
  field_simp at hsub ⊢
  nlinarith [hsub]

/-- Integrability of `tⁿ e^{-Kt}` on `(0, ∞)`. -/
theorem integrableOn_pow_mul_exp_neg (K : ℝ) (hK : 0 < K) (n : ℕ) :
    IntegrableOn (fun t : ℝ => t ^ n * Real.exp (-(K * t))) (Ioi 0) := by
  have h0 := Real.GammaIntegral_convergent (s := (n : ℝ) + 1) (by positivity)
  have h1 : IntegrableOn (fun x : ℝ => x ^ n * Real.exp (-x)) (Ioi 0) := by
    apply h0.congr_fun _ measurableSet_Ioi
    intro x _
    simp only [add_sub_cancel_right, Real.rpow_natCast]
    ring
  have h2 := (integrableOn_Ioi_comp_mul_left_iff
    (fun x : ℝ => x ^ n * Real.exp (-x)) 0 hK).mpr (by simpa using h1)
  have h3 : IntegrableOn
      (fun x : ℝ => (K ^ n)⁻¹ * ((K * x) ^ n * Real.exp (-(K * x)))) (Ioi 0) :=
    h2.const_mul _
  apply h3.congr_fun _ measurableSet_Ioi
  intro x _
  have hKpne : (K : ℝ) ^ n ≠ 0 := pow_ne_zero n (ne_of_gt hK)
  simp only [mul_pow]
  field_simp

set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Total rate `K = Σ_a k_a`. -/
def totalRate (k : ι → ℝ) : ℝ := ∑ j, k j

/-- The race law density `ℙ(A = a, T ∈ dt) = k_a e^{-Kt} dt`. -/
def raceDensity (k : ι → ℝ) (a : ι) (t : ℝ) : ℝ := k a * Real.exp (-(totalRate k * t))

/-- Expectation of an observable `F(A, T)` of the winner and the first waiting time. -/
def raceExpectation (k : ι → ℝ) (F : ι → ℝ → ℝ) : ℝ :=
  ∑ a, ∫ t in Ioi (0 : ℝ), F a t * raceDensity k a t

/-- The winner indicator `1_{A=b}` evaluated at the outcome `A = a`. -/
def winnerIndicator (b a : ι) : ℝ := if a = b then 1 else 0

/-- The log-rate score `s_b = 1_{A=b} - k_b T` (`eq:supp-race-score`) at outcome `(a, t)`. -/
def score (k : ι → ℝ) (b a : ι) (t : ℝ) : ℝ := winnerIndicator b a - k b * t

/-- Winner probabilities `p_b = k_b / K`. -/
def winnerProb (k : ι → ℝ) (b : ι) : ℝ := k b / totalRate k

/-- The score Gram matrix `(𝔼[s_b s_c])_{b,c}`. -/
def scoreGram (k : ι → ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun b c => raceExpectation k fun a t => score k b a t * score k c a t

/-- The winner-indicator covariance matrix `(𝔼[(1_{A=b} - p_b)(1_{A=c} - p_c)])_{b,c}`. -/
def winnerCovarianceGram (k : ι → ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun b c => raceExpectation k fun a _ =>
    (winnerIndicator b a - winnerProb k b) * (winnerIndicator c a - winnerProb k c)

/-- The matrix `diag(p) - p pᵀ`. -/
def winnerCovariance (p : ι → ℝ) : Matrix ι ι ℝ := diagonal p - vecMulVec p p

theorem totalRate_pos {k : ι → ℝ} (hk : ∀ a, 0 < k a) (b : ι) : 0 < totalRate k :=
  Finset.sum_pos (fun a _ => hk a) ⟨b, Finset.mem_univ b⟩

/-- Closed form of the race expectation of an observable that is quadratic in the waiting
time. -/
theorem raceExpectation_quadratic {k : ι → ℝ} (hk : ∀ a, 0 < k a) (b : ι)
    (α β γ : ι → ℝ) :
    raceExpectation k (fun a t => α a + β a * t + γ a * t ^ 2)
      = ∑ a, k a * (α a / totalRate k + β a / totalRate k ^ 2
          + 2 * γ a / totalRate k ^ 3) := by
  set K := totalRate k with hKdef
  have hK : 0 < K := totalRate_pos hk b
  have hI0 := integral_pow_mul_exp_neg K hK 0
  have hI1 := integral_pow_mul_exp_neg K hK 1
  have hI2 := integral_pow_mul_exp_neg K hK 2
  have hJ0 := integrableOn_pow_mul_exp_neg K hK 0
  have hJ1 := integrableOn_pow_mul_exp_neg K hK 1
  have hJ2 := integrableOn_pow_mul_exp_neg K hK 2
  unfold raceExpectation
  refine Finset.sum_congr rfl fun a _ => ?_
  have hfun : Set.EqOn
      (fun t : ℝ => (α a + β a * t + γ a * t ^ 2) * raceDensity k a t)
      (fun t : ℝ => (k a * α a) * (t ^ 0 * Real.exp (-(K * t)))
        + (k a * β a) * (t ^ 1 * Real.exp (-(K * t)))
        + (k a * γ a) * (t ^ 2 * Real.exp (-(K * t)))) (Ioi 0) := by
    intro t _
    simp only [raceDensity, ← hKdef]
    ring
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hfun]
  have hA : IntegrableOn (fun t : ℝ => (k a * α a) * (t ^ 0 * Real.exp (-(K * t)))
      + (k a * β a) * (t ^ 1 * Real.exp (-(K * t)))) (Ioi 0) :=
    (hJ0.const_mul _).add (hJ1.const_mul _)
  rw [MeasureTheory.integral_add hA (hJ2.const_mul _)]
  rw [MeasureTheory.integral_add (hJ0.const_mul _) (hJ1.const_mul _)]
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul, hI0, hI1, hI2]
  simp only [Nat.factorial]
  push_cast
  field_simp

/-- The race law is a probability law. -/
theorem raceExpectation_one {k : ι → ℝ} (hk : ∀ a, 0 < k a) (b : ι) :
    raceExpectation k (fun _ _ => 1) = 1 := by
  have h := raceExpectation_quadratic hk b (fun _ => 1) (fun _ => 0) (fun _ => 0)
  simp only [zero_mul, add_zero, mul_zero, zero_div] at h
  rw [h, ← Finset.sum_mul]
  have hK := (totalRate_pos hk b).ne'
  change totalRate k * (1 / totalRate k) = 1
  field_simp

/-- The winner has probability `ℙ(A = b) = k_b / K`. -/
theorem raceExpectation_winner {k : ι → ℝ} (hk : ∀ a, 0 < k a) (b : ι) :
    raceExpectation k (fun a _ => winnerIndicator b a) = winnerProb k b := by
  have h := raceExpectation_quadratic hk b (fun a => winnerIndicator b a) (fun _ => 0)
    (fun _ => 0)
  simp only [zero_mul, add_zero, mul_zero, zero_div] at h
  rw [h, Finset.sum_eq_single b]
  · simp [winnerIndicator, winnerProb, div_eq_mul_inv]
  · intro a _ hab
    simp [winnerIndicator, hab]
  · intro hb
    exact absurd (Finset.mem_univ b) hb

/-- The mean waiting time is `𝔼T = 1/K`. -/
theorem raceExpectation_waiting {k : ι → ℝ} (hk : ∀ a, 0 < k a) (b : ι) :
    raceExpectation k (fun _ t => t) = 1 / totalRate k := by
  have h := raceExpectation_quadratic hk b (fun _ => 0) (fun _ => 1) (fun _ => 0)
  simp only [zero_mul, add_zero, mul_zero, zero_div, zero_add, one_mul] at h
  rw [h, ← Finset.sum_mul]
  have hK := (totalRate_pos hk b).ne'
  change totalRate k * (1 / totalRate k ^ 2) = 1 / totalRate k
  field_simp

/-- The second moment of the waiting time is `𝔼T² = 2/K²`. -/
theorem raceExpectation_waiting_sq {k : ι → ℝ} (hk : ∀ a, 0 < k a) (b : ι) :
    raceExpectation k (fun _ t => t ^ 2) = 2 / totalRate k ^ 2 := by
  have h := raceExpectation_quadratic hk b (fun _ => 0) (fun _ => 0) (fun _ => 1)
  simp only [zero_mul, add_zero, zero_div, zero_add, mul_one, one_mul] at h
  rw [h, ← Finset.sum_mul]
  have hK := (totalRate_pos hk b).ne'
  change totalRate k * (2 / totalRate k ^ 3) = 2 / totalRate k ^ 2
  field_simp

/-- Independence of winner and waiting time: the race density factorizes as
`p_a · K e^{-Kt}` (winner law times the `Exp(K)` density). -/
theorem raceDensity_factor {k : ι → ℝ} (hk : ∀ a, 0 < k a) (a : ι) (t : ℝ) :
    raceDensity k a t = winnerProb k a * (totalRate k * Real.exp (-(totalRate k * t))) := by
  have hK := (totalRate_pos hk a).ne'
  unfold raceDensity winnerProb
  field_simp

/-- `s_b = 1_{A=b} - k_b T` is the log-rate score: the derivative of the log-likelihood
`log(k_A e^{-KT})` with respect to `θ = log k_b` (all other rates fixed), at the true rates. -/
theorem hasDerivAt_log_raceDensity {k : ι → ℝ} (hk : ∀ a, 0 < k a) (b a : ι) (t : ℝ) :
    HasDerivAt (fun θ : ℝ => Real.log (raceDensity (Function.update k b (Real.exp θ)) a t))
      (score k b a t) (Real.log (k b)) := by
  have hform : (fun θ : ℝ => Real.log (raceDensity (Function.update k b (Real.exp θ)) a t))
      = fun θ => (if a = b then θ else Real.log (k a))
          - (Real.exp θ + (totalRate k - k b)) * t := by
    funext θ
    have hsum : totalRate (Function.update k b (Real.exp θ))
        = Real.exp θ + (totalRate k - k b) := by
      unfold totalRate
      rw [Finset.sum_update_of_mem (Finset.mem_univ b)]
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ b), Finset.sdiff_singleton_eq_erase]
      ring
    have hpos : 0 < Function.update k b (Real.exp θ) a := by
      by_cases hab : a = b
      · subst hab; simp [Real.exp_pos]
      · rw [Function.update_of_ne hab]; exact hk a
    unfold raceDensity
    rw [Real.log_mul hpos.ne' (Real.exp_pos _).ne', Real.log_exp, hsum]
    by_cases hab : a = b
    · subst hab; simp; ring
    · rw [Function.update_of_ne hab, if_neg hab]; ring
  rw [hform]
  have h1 : HasDerivAt (fun θ : ℝ => if a = b then θ else Real.log (k a))
      (if a = b then 1 else 0) (Real.log (k b)) := by
    by_cases hab : a = b
    · simp only [hab, if_true]; exact hasDerivAt_id _
    · simp only [hab, if_false]; exact hasDerivAt_const _ _
  have h2 : HasDerivAt (fun θ : ℝ => (Real.exp θ + (totalRate k - k b)) * t)
      (Real.exp (Real.log (k b)) * t) (Real.log (k b)) :=
    ((Real.hasDerivAt_exp _).add_const _).mul_const t
  have h := h1.sub h2
  rw [Real.exp_log (hk b)] at h
  exact h

/-- **`eq:supp-race-score-gram`**: `𝔼[s_b s_c] = δ_{bc} k_b / K`, for any finite family of
positive rates. -/
theorem scoreGram_eq {k : ι → ℝ} (hk : ∀ a, 0 < k a) :
    scoreGram k = diagonal (winnerProb k) := by
  ext b c
  have hK := (totalRate_pos hk b).ne'
  have h := raceExpectation_quadratic hk b
    (fun a => winnerIndicator b a * winnerIndicator c a)
    (fun a => -(winnerIndicator b a * k c + winnerIndicator c a * k b))
    (fun _ => k b * k c)
  have hfun : (fun a t => score k b a t * score k c a t)
      = (fun a t => winnerIndicator b a * winnerIndicator c a
          + -(winnerIndicator b a * k c + winnerIndicator c a * k b) * t
          + k b * k c * t ^ 2) := by
    funext a t; simp only [score]; ring
  simp only [scoreGram, Matrix.of_apply, hfun, h]
  have hsplit : ∀ a, k a * (winnerIndicator b a * winnerIndicator c a / totalRate k
      + -(winnerIndicator b a * k c + winnerIndicator c a * k b) / totalRate k ^ 2
      + 2 * (k b * k c) / totalRate k ^ 3)
      = (k a * winnerIndicator b a * winnerIndicator c a) / totalRate k
        - (k a * winnerIndicator b a) * k c / totalRate k ^ 2
        - (k a * winnerIndicator c a) * k b / totalRate k ^ 2
        + k a * (2 * (k b * k c) / totalRate k ^ 3) := fun a => by ring
  simp only [hsplit, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_div,
    ← Finset.sum_mul, ← Finset.mul_sum]
  have hsel : ∀ d : ι, ∑ a, k a * winnerIndicator d a = k d := by
    intro d
    rw [Finset.sum_eq_single d]
    · simp [winnerIndicator]
    · intro a _ had; simp [winnerIndicator, had]
    · intro hd; exact absurd (Finset.mem_univ d) hd
  have hsel2 : ∑ a, k a * winnerIndicator b a * winnerIndicator c a
      = if b = c then k b else 0 := by
    rw [Finset.sum_eq_single b]
    · by_cases hbc : b = c
      · subst hbc; simp [winnerIndicator]
      · simp [winnerIndicator, hbc, Ne.symm hbc]
    · intro a _ hab; simp [winnerIndicator, hab]
    · intro hb; exact absurd (Finset.mem_univ b) hb
  rw [hsel2, hsel b, hsel c]
  change (if b = c then k b else 0) / totalRate k - k b * k c / totalRate k ^ 2
      - k c * k b / totalRate k ^ 2 + totalRate k * (2 * (k b * k c) / totalRate k ^ 3)
    = diagonal (winnerProb k) b c
  by_cases hbc : b = c
  · subst hbc
    simp only [if_true, diagonal_apply_eq, winnerProb]
    field_simp
    ring
  · simp only [hbc, if_false, diagonal_apply_ne _ hbc]
    field_simp
    ring

/-- The score Gram is positive definite (faithful). -/
theorem scoreGram_posDef {k : ι → ℝ} (hk : ∀ a, 0 < k a) : (scoreGram k).PosDef := by
  rw [scoreGram_eq hk, Matrix.posDef_diagonal_iff]
  intro b
  exact div_pos (hk b) (totalRate_pos hk b)

theorem sum_winnerProb {k : ι → ℝ} (hk : ∀ a, 0 < k a) (b : ι) :
    ∑ a, winnerProb k a = 1 := by
  unfold winnerProb
  rw [← Finset.sum_div]
  exact div_self (totalRate_pos hk b).ne'

/-- The winner indicators have covariance `diag(p) - p pᵀ`. -/
theorem winnerCovarianceGram_eq {k : ι → ℝ} (hk : ∀ a, 0 < k a) :
    winnerCovarianceGram k = winnerCovariance (winnerProb k) := by
  ext b c
  have h := raceExpectation_quadratic hk b
    (fun a => (winnerIndicator b a - winnerProb k b) * (winnerIndicator c a - winnerProb k c))
    (fun _ => 0) (fun _ => 0)
  simp only [zero_mul, add_zero, mul_zero, zero_div] at h
  simp only [winnerCovarianceGram, Matrix.of_apply, h]
  have hp := sum_winnerProb hk b
  have hterm : ∀ a, k a * ((winnerIndicator b a - winnerProb k b)
      * (winnerIndicator c a - winnerProb k c) / totalRate k)
      = winnerProb k a * winnerIndicator b a * winnerIndicator c a
        - winnerProb k a * winnerIndicator b a * winnerProb k c
        - winnerProb k a * winnerIndicator c a * winnerProb k b
        + winnerProb k a * (winnerProb k b * winnerProb k c) := fun a => by
    unfold winnerProb; ring
  simp only [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, hp,
    one_mul]
  have hsel : ∀ d : ι, ∑ a, winnerProb k a * winnerIndicator d a = winnerProb k d := by
    intro d
    rw [Finset.sum_eq_single d]
    · simp [winnerIndicator]
    · intro a _ had; simp [winnerIndicator, had]
    · intro hd; exact absurd (Finset.mem_univ d) hd
  have hsel2 : ∑ a, winnerProb k a * winnerIndicator b a * winnerIndicator c a
      = if b = c then winnerProb k b else 0 := by
    rw [Finset.sum_eq_single b]
    · by_cases hbc : b = c
      · subst hbc; simp [winnerIndicator]
      · simp [winnerIndicator, hbc, Ne.symm hbc]
    · intro a _ hab; simp [winnerIndicator, hab]
    · intro hb; exact absurd (Finset.mem_univ b) hb
  rw [hsel2, hsel b, hsel c]
  by_cases hbc : b = c
  · subst hbc
    simp [winnerCovariance, diagonal_apply_eq, vecMulVec_apply]
  · simp [winnerCovariance, hbc, diagonal_apply_ne _ hbc, vecMulVec_apply]
    ring

/-- `diag(p) - p pᵀ` annihilates the all-ones vector when `Σ p = 1`. -/
theorem winnerCovariance_mulVec_one (p : ι → ℝ) (hp : ∑ a, p a = 1) :
    winnerCovariance p *ᵥ (fun _ => 1) = 0 := by
  rw [winnerCovariance, Matrix.sub_mulVec]
  funext i
  have h1 : (diagonal p *ᵥ (fun _ => (1 : ℝ))) i = p i := by
    simp [Matrix.mulVec_diagonal]
  have h2 : (vecMulVec p p *ᵥ (fun _ => (1 : ℝ))) i = p i := by
    simp only [Matrix.mulVec, dotProduct, vecMulVec_apply, mul_one]
    rw [← Finset.mul_sum, hp, mul_one]
  rw [Pi.sub_apply, h1, h2, sub_self, Pi.zero_apply]

/-- The winner covariance of a positive race is singular (it loses the all-ones rate
direction). -/
theorem winnerCovariance_det_eq_zero {k : ι → ℝ} (hk : ∀ a, 0 < k a) (b : ι) :
    (winnerCovariance (winnerProb k)).det = 0 := by
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨fun _ => 1, ?_, winnerCovariance_mulVec_one _ (sum_winnerProb hk b)⟩
  intro h
  have := congrFun h b
  simp at this

/-- The winner covariance of a positive race is not positive definite. -/
theorem winnerCovariance_not_posDef {k : ι → ℝ} (hk : ∀ a, 0 < k a) (b : ι) :
    ¬ (winnerCovariance (winnerProb k)).PosDef := by
  intro hpd
  have h := hpd.det_pos
  rw [winnerCovariance_det_eq_zero hk b] at h
  exact lt_irrefl _ h

/-- Winner probabilities are invariant under a common rescaling of the rates. -/
theorem winnerProb_smul (k : ι → ℝ) {c : ℝ} (hc : c ≠ 0) :
    winnerProb (c • k) = winnerProb k := by
  funext b
  unfold winnerProb totalRate
  simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  exact mul_div_mul_left _ _ hc

/-- Rates are recovered from the winner–waiting statistics: `k_b = ℙ(A = b)/𝔼T`. -/
theorem rate_eq_winner_div_waiting {k : ι → ℝ} (hk : ∀ a, 0 < k a) (b : ι) :
    k b = raceExpectation k (fun a _ => winnerIndicator b a)
      / raceExpectation k (fun _ t => t) := by
  rw [raceExpectation_winner hk, raceExpectation_waiting hk b]
  have hK := (totalRate_pos hk b).ne'
  unfold winnerProb
  field_simp

/-- Faithfulness: two positive rate vectors with the same winner probabilities and the same
mean waiting time are equal. -/
theorem rates_eq_of_winner_waiting {k k' : ι → ℝ} (hk : ∀ a, 0 < k a) (hk' : ∀ a, 0 < k' a)
    (hwin : ∀ b, raceExpectation k (fun a _ => winnerIndicator b a)
      = raceExpectation k' (fun a _ => winnerIndicator b a))
    (hwait : raceExpectation k (fun _ t => t) = raceExpectation k' (fun _ t => t)) :
    k = k' := by
  funext b
  rw [rate_eq_winner_div_waiting hk b, rate_eq_winner_div_waiting hk' b, hwin b, hwait]

/-- Winner probabilities alone are not faithful: `k` and `2k` have the same winner law but
different rates (and different mean waiting times). -/
theorem exists_rates_ne_winnerProb_eq [Nonempty ι] {k : ι → ℝ} (hk : ∀ a, 0 < k a) :
    (2 : ℝ) • k ≠ k ∧ winnerProb ((2 : ℝ) • k) = winnerProb k ∧
      raceExpectation ((2 : ℝ) • k) (fun _ t => t) ≠ raceExpectation k (fun _ t => t) := by
  obtain ⟨b⟩ := ‹Nonempty ι›
  have hk2 : ∀ a, 0 < ((2 : ℝ) • k) a := fun a => by
    simp only [Pi.smul_apply, smul_eq_mul]; linarith [hk a]
  refine ⟨fun h => ?_, winnerProb_smul k two_ne_zero, ?_⟩
  · have := congrFun h b
    simp only [Pi.smul_apply, smul_eq_mul] at this
    linarith [hk b]
  · rw [raceExpectation_waiting hk2 b, raceExpectation_waiting hk b]
    have hK := totalRate_pos hk b
    have h2 : totalRate ((2 : ℝ) • k) = 2 * totalRate k := by
      unfold totalRate; simp [Finset.mul_sum]
    rw [h2]
    intro h
    field_simp at h
    linarith

/-! ### The twelve oriented `A₃` roots -/

/-- The twelve oriented roots `±r_a` of the `A₃` root race: `(a, true) ↦ r_a`,
`(a, false) ↦ -r_a`. -/
abbrev OrientedRoot : Type := Fin 6 × Bool

/-- The vector of an oriented root. -/
def orientedRootVector : OrientedRoot → Fin 3 → ℝ
  | (a, true) => a3SchedulerRoot a
  | (a, false) => -a3SchedulerRoot a

theorem card_orientedRoot : Fintype.card OrientedRoot = 12 := by simp

/-- **`lem:supp-race-score` at the twelve oriented roots.**  For positive rates `k_a^±`, the
score Gram is `δ_{bc} k_b / K` and positive definite, the winner covariance is
`diag(p) - p pᵀ`, singular in the all-ones direction, and invariant under common rescaling,
while the rates are recovered from winner probabilities and mean waiting time. -/
theorem orientedRootRace_score_faithful (k : OrientedRoot → ℝ) (hk : ∀ a, 0 < k a) :
    scoreGram k = diagonal (winnerProb k) ∧ (scoreGram k).PosDef ∧
      winnerCovarianceGram k = winnerCovariance (winnerProb k) ∧
      winnerCovariance (winnerProb k) *ᵥ (fun _ => 1) = 0 ∧
      ¬ (winnerCovariance (winnerProb k)).PosDef ∧
      (∀ c : ℝ, c ≠ 0 → winnerProb (c • k) = winnerProb k) ∧
      (∀ k' : OrientedRoot → ℝ, (∀ a, 0 < k' a) →
        (∀ b, raceExpectation k (fun a _ => winnerIndicator b a)
          = raceExpectation k' (fun a _ => winnerIndicator b a)) →
        raceExpectation k (fun _ t => t) = raceExpectation k' (fun _ t => t) → k = k') :=
  ⟨scoreGram_eq hk, scoreGram_posDef hk, winnerCovarianceGram_eq hk,
    winnerCovariance_mulVec_one _ (sum_winnerProb hk (0, true)),
    winnerCovariance_not_posDef hk (0, true), fun _ hc => winnerProb_smul k hc,
    fun _ hk' hwin hwait => rates_eq_of_winner_waiting hk hk' hwin hwait⟩

/-- Non-vacuity: unit rates on the twelve oriented roots. -/
example : (scoreGram (fun _ : OrientedRoot => (1 : ℝ))).PosDef :=
  (orientedRootRace_score_faithful _ fun _ => one_pos).2.1

end RootRaceScore
end RenewalGeometry
