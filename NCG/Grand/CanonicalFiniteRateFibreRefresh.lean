/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.UniversalMarkovRetract
import NCG.Grand.DiscreteClock
import Mathlib.LinearAlgebra.Matrix.Bilinear

/-!
# Canonical finite-rate fibre refresh

The exact exponential splitting, Markov-generator criterion, retained
quotient dynamics, and small-time obstruction for the canonical Poisson
refresh construction.
-/

open Matrix NormedSpace Finset

namespace NCG
namespace CanonicalFiniteRateFibreRefresh

/-- Powers preserve an intertwiner, including rectangular intertwiners. -/
theorem power_intertwine_rect
    {U Z : Type*} [Fintype U] [Fintype Z] [DecidableEq U] [DecidableEq Z]
    (B : Matrix U U ℝ) (A : Matrix Z Z ℝ) (C : Matrix U Z ℝ)
    (hBC : B * C = C * A) (n : ℕ) :
    B ^ n * C = C * A ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Matrix.mul_assoc, hBC, ← Matrix.mul_assoc, ih,
        Matrix.mul_assoc, ← pow_succ]

attribute [-instance]
  Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
open scoped Norms.Operator in
/-- Exponentiating a finite rectangular intertwining relation. -/
theorem exp_intertwine_rect
    {U Z : Type*} [Fintype U] [Fintype Z] [DecidableEq U] [DecidableEq Z]
    (B : Matrix U U ℝ) (A : Matrix Z Z ℝ) (C : Matrix U Z ℝ)
    (hBC : B * C = C * A) (t : ℝ) :
    exp (t • B) * C = C * exp (t • A) := by
  rw [exp_eq_tsum (𝕂 := ℝ) (𝔸 := Matrix U U ℝ),
    exp_eq_tsum (𝕂 := ℝ) (𝔸 := Matrix Z Z ℝ)]
  have hsB : Summable
      (fun n : ℕ => ((n.factorial : ℝ)⁻¹) • (t • B) ^ n) :=
    expSeries_summable' (𝕂 := ℝ) (t • B)
  have hsA : Summable
      (fun n : ℕ => ((n.factorial : ℝ)⁻¹) • (t • A) ^ n) :=
    expSeries_summable' (𝕂 := ℝ) (t • A)
  let mulC : Matrix U U ℝ →L[ℝ] Matrix U Z ℝ :=
    LinearMap.toContinuousLinearMap (mulRightLinearMap U ℝ C)
  let Cmul : Matrix Z Z ℝ →L[ℝ] Matrix U Z ℝ :=
    LinearMap.toContinuousLinearMap (mulLeftLinearMap Z ℝ C)
  change mulC (∑' n : ℕ, ((n.factorial : ℝ)⁻¹) • (t • B) ^ n) =
    Cmul (∑' n : ℕ, ((n.factorial : ℝ)⁻¹) • (t • A) ^ n)
  rw [ContinuousLinearMap.map_tsum mulC hsB,
    ContinuousLinearMap.map_tsum Cmul hsA]
  refine tsum_congr fun n => ?_
  change (((n.factorial : ℝ)⁻¹) • (t • B) ^ n) * C =
    C * (((n.factorial : ℝ)⁻¹) • (t • A) ^ n)
  have hscaled : (t • B) * C = C * (t • A) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, hBC]
  calc
    (((n.factorial : ℝ)⁻¹) • (t • B) ^ n) * C =
        ((n.factorial : ℝ)⁻¹) • ((t • B) ^ n * C) := by
      rw [Matrix.smul_mul]
    _ = ((n.factorial : ℝ)⁻¹) • (C * (t • A) ^ n) := by
      rw [power_intertwine_rect (t • B) (t • A) C hscaled n]
    _ = C * (((n.factorial : ℝ)⁻¹) • (t • A) ^ n) := by
      rw [Matrix.mul_smul]

/-- The embedded coarse generator is supported on the decoded quotient
corner, while the complementary fibre projection is annihilated. -/
theorem corner_and_fibre_annihilation
    {U Z : Type*} [Fintype U] [Fintype Z] [DecidableEq U] [DecidableEq Z]
    (C : Matrix U Z ℝ) (R : Matrix Z U ℝ) (A : Matrix Z Z ℝ)
    (hRC : R * C = 1) :
    let E := C * R
    let B := C * A * R
    let Q := (1 : Matrix U U ℝ) - E
    E * E = E ∧ B * E = B ∧ E * B = B ∧ B * Q = 0 ∧ Q * B = 0 := by
  dsimp
  have hE2 : (C * R) * (C * R) = C * R := by
    calc
      (C * R) * (C * R) = C * (R * C) * R := by simp [Matrix.mul_assoc]
      _ = C * R := by rw [hRC]; simp
  have hBE : (C * A * R) * (C * R) = C * A * R := by
    calc
      (C * A * R) * (C * R) = C * A * (R * C) * R := by
        simp [Matrix.mul_assoc]
      _ = C * A * R := by rw [hRC]; simp
  have hEB : (C * R) * (C * A * R) = C * A * R := by
    calc
      (C * R) * (C * A * R) = C * (R * C) * A * R := by
        simp [Matrix.mul_assoc]
      _ = C * A * R := by rw [hRC]; simp
  refine ⟨hE2, hBE, hEB, ?_, ?_⟩
  · rw [Matrix.mul_sub, Matrix.mul_one, hBE, sub_self]
  · rw [Matrix.sub_mul, Matrix.one_mul, hEB, sub_self]

attribute [-instance]
  Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
open scoped Norms.Operator in
/-- Exponential of the embedded coarse generator: coarse evolution on the
decoded corner and the identity on the hidden fibre complement. -/
theorem exp_embedded_coarse_generator
    {U Z : Type*} [Fintype U] [Fintype Z] [DecidableEq U] [DecidableEq Z]
    (C : Matrix U Z ℝ) (R : Matrix Z U ℝ) (A : Matrix Z Z ℝ)
    (hRC : R * C = 1) (t : ℝ) :
    exp (t • (C * A * R)) =
      C * exp (t • A) * R + ((1 : Matrix U U ℝ) - C * R) := by
  let B := C * A * R
  let E := C * R
  let Q := (1 : Matrix U U ℝ) - E
  have hdata := corner_and_fibre_annihilation C R A hRC
  have hBC : B * C = C * A := by
    dsimp [B]
    calc
      (C * A * R) * C = C * A * (R * C) := by simp [Matrix.mul_assoc]
      _ = C * A := by rw [hRC]; simp
  have hBQ : B * Q = Q * (0 : Matrix U U ℝ) := by
    simpa [B, Q, E] using hdata.2.2.2.1
  have hC := exp_intertwine_rect B A C hBC t
  have hQ := exp_intertwine_rect B (0 : Matrix U U ℝ) Q hBQ t
  have hIQ : (1 : Matrix U U ℝ) = E + Q := by simp [E, Q]
  calc
    exp (t • (C * A * R)) = exp (t • B) * 1 := by simp [B]
    _ = exp (t • B) * (E + Q) := by rw [← hIQ]
    _ = (exp (t • B) * C) * R + exp (t • B) * Q := by
      simp [E, Matrix.mul_add, Matrix.mul_assoc]
    _ = (C * exp (t • A)) * R + Q * exp (t • (0 : Matrix U U ℝ)) := by
      rw [hC, hQ]
    _ = C * exp (t • A) * R + Q := by simp
    _ = C * exp (t • A) * R + (1 - C * R) := rfl

/-- Canonical fine generator with Poisson refresh rate `lam`. -/
def refreshGenerator
    {U Z : Type*} [Fintype U] [Fintype Z] [DecidableEq U]
    (C : Matrix U Z ℝ) (R : Matrix Z U ℝ) (A : Matrix Z Z ℝ)
    (lam : ℝ) : Matrix U U ℝ :=
  C * A * R + lam • (C * R - 1)

attribute [-instance]
  Matrix.SpecialLinearGroup.hasCoeToGeneralLinearGroup in
open scoped Norms.Operator in
/-- The boxed Poisson-refresh semigroup identity. -/
theorem refreshGenerator_exp
    {U Z : Type*} [Fintype U] [Fintype Z] [DecidableEq U] [DecidableEq Z]
    (C : Matrix U Z ℝ) (R : Matrix Z U ℝ) (A : Matrix Z Z ℝ)
    (hRC : R * C = 1) (lam t : ℝ) :
    exp (t • refreshGenerator C R A lam) =
      C * exp (t • A) * R + Real.exp (-lam * t) •
        ((1 : Matrix U U ℝ) - C * R) := by
  let E := C * R
  let B := C * A * R
  let Q := (1 : Matrix U U ℝ) - E
  have hdata := corner_and_fibre_annihilation C R A hRC
  have hE2 : E * E = E := hdata.1
  have hBQ : B * Q = 0 := hdata.2.2.2.1
  have hQB : Q * B = 0 := hdata.2.2.2.2
  have hcomm : Commute (t • B) ((-lam * t) • Q) := by
    apply Commute.smul_left
    apply Commute.smul_right
    exact (show B * Q = Q * B by rw [hBQ, hQB])
  have hsplit : t • refreshGenerator C R A lam =
      t • B + (-lam * t) • Q := by
    dsimp [refreshGenerator, B, Q, E]
    module
  rw [hsplit, Matrix.exp_add_of_commute _ _ hcomm,
    exp_embedded_coarse_generator C R A hRC t]
  have hQexp := exp_one_sub_idem E hE2 (-lam * t)
  change exp ((-lam * t) • Q) = 1 +
      (Real.exp (-lam * t) - 1) • Q at hQexp
  rw [hQexp]
  have hRQ : R * Q = 0 := by
    dsimp [Q, E]
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hRC,
      Matrix.one_mul, sub_self]
  have hcornerQ : (C * exp (t • A) * R) * Q = 0 := by
    rw [Matrix.mul_assoc, hRQ, Matrix.mul_zero]
  have hQ2 : Q * Q = Q := by
    change (1 - E) * (1 - E) = 1 - E
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hE2]
    module
  let X := C * exp (t • A) * R
  let r := Real.exp (-lam * t)
  have hXQ : X * Q = 0 := by simpa [X] using hcornerQ
  change (X + Q) * (1 + (r - 1) • Q) = X + r • Q
  calc
    (X + Q) * (1 + (r - 1) • Q) =
        X + (r - 1) • (X * Q) + Q + (r - 1) • (Q * Q) := by
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_one,
        Matrix.mul_smul]
      rw [smul_add]
      abel
    _ = X + Q + (r - 1) • Q := by rw [hXQ, hQ2]; simp
    _ = X + r • Q := by module

/-- Row-convention finite-state Markov generator: nonnegative off-diagonal
rates and zero row sums. -/
def IsFiniteMarkovGenerator
    {U : Type*} [Fintype U] (L : Matrix U U ℝ) : Prop :=
  (∀ u v, u ≠ v → 0 ≤ L u v) ∧ (∀ u, ∑ v, L u v = 0)

/-- A concrete sufficient-large-rate criterion.  `threshold` certifies all
off-diagonal rates at one refresh rate; nonnegative off-diagonal entries of
the stochastic projection make every larger rate valid. -/
theorem refreshGenerator_isMarkov_for_large_rate
    {U Z : Type*} [Fintype U] [Fintype Z] [DecidableEq U]
    (C : Matrix U Z ℝ) (R : Matrix Z U ℝ) (A : Matrix Z Z ℝ)
    (threshold lam : ℝ) (hlam : threshold ≤ lam)
    (hBsum : ∀ u, ∑ v, (C * A * R) u v = 0)
    (hEsum : ∀ u, ∑ v, (C * R) u v = 1)
    (hEoff : ∀ u v, u ≠ v → 0 ≤ (C * R) u v)
    (hthreshold : ∀ u v, u ≠ v →
      0 ≤ (C * A * R) u v + threshold * (C * R) u v) :
    IsFiniteMarkovGenerator (refreshGenerator C R A lam) := by
  constructor
  · intro u v huv
    have hdelta : (1 : Matrix U U ℝ) u v = 0 := by
      simp [Matrix.one_apply, huv]
    simp only [refreshGenerator, Matrix.add_apply, Matrix.smul_apply,
      Matrix.sub_apply, hdelta, sub_zero, smul_eq_mul]
    nlinarith [hEoff u v huv, hthreshold u v huv]
  · intro u
    simp only [refreshGenerator, Matrix.add_apply, Matrix.smul_apply,
      Matrix.sub_apply, smul_eq_mul]
    calc
      ∑ v, ((C * A * R) u v +
          lam * ((C * R) u v - (1 : Matrix U U ℝ) u v)) =
          (∑ v, (C * A * R) u v) +
            lam * ((∑ v, (C * R) u v) -
              ∑ v, (1 : Matrix U U ℝ) u v) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum,
          Finset.sum_sub_distrib]
      _ = 0 := by
        have hone : ∑ v, (1 : Matrix U U ℝ) u v = 1 := by
          classical
          rw [Fintype.sum_eq_single u]
          · simp [Matrix.one_apply]
          · intro v hv
            simp [Matrix.one_apply, Ne.symm hv]
        rw [hBsum u, hEsum u, hone]
        ring

/-- An explicit finite domination threshold for negative embedded coarse
rates, obtained by summing the finitely many required rate ratios. -/
noncomputable def sufficientRefreshRate
    {U : Type*} [Fintype U]
    (B E : Matrix U U ℝ) : ℝ :=
  ∑ uv : U × U, max 0 (-B uv.1 uv.2 / E uv.1 uv.2)

theorem sufficientRefreshRate_dominates_negative_entry
    {U : Type*} [Fintype U]
    (B E : Matrix U U ℝ) (u v : U)
    (hB : B u v < 0) (hE : 0 < E u v) :
    0 ≤ B u v + sufficientRefreshRate B E * E u v := by
  classical
  have hterm : max 0 (-B u v / E u v) ≤ sufficientRefreshRate B E := by
    change max 0 (-B u v / E u v) ≤
      ∑ uv : U × U, max 0 (-B uv.1 uv.2 / E uv.1 uv.2)
    exact Finset.single_le_sum
      (s := Finset.univ)
      (f := fun uv : U × U => max 0 (-B uv.1 uv.2 / E uv.1 uv.2))
      (fun uv _ => le_max_left _ _) (Finset.mem_univ (u, v))
  have hratio : -B u v / E u v ≤ sufficientRefreshRate B E :=
    (le_max_right 0 _).trans hterm
  have hmul : -B u v ≤ sufficientRefreshRate B E * E u v :=
    (div_le_iff₀ hE).mp hratio
  linarith

/-- Hence a finite sufficient refresh rate exists whenever every negative
off-diagonal embedded coarse rate lies on a positive refresh edge. -/
theorem exists_rate_making_all_larger_refreshes_markov
    {U Z : Type*} [Fintype U] [Fintype Z] [DecidableEq U]
    (C : Matrix U Z ℝ) (R : Matrix Z U ℝ) (A : Matrix Z Z ℝ)
    (hBsum : ∀ u, ∑ v, (C * A * R) u v = 0)
    (hEsum : ∀ u, ∑ v, (C * R) u v = 1)
    (hEoff : ∀ u v, u ≠ v → 0 ≤ (C * R) u v)
    (hsupport : ∀ u v, u ≠ v → (C * A * R) u v < 0 →
      0 < (C * R) u v) :
    ∃ threshold : ℝ, ∀ lam ≥ threshold,
      IsFiniteMarkovGenerator (refreshGenerator C R A lam) := by
  let B := C * A * R
  let E := C * R
  refine ⟨sufficientRefreshRate B E, ?_⟩
  intro lam hlam
  apply refreshGenerator_isMarkov_for_large_rate C R A
    (sufficientRefreshRate B E) lam hlam hBsum hEsum hEoff
  intro u v huv
  by_cases hBnonneg : 0 ≤ B u v
  · have hthresholdNonneg : 0 ≤ sufficientRefreshRate B E := by
      exact Finset.sum_nonneg fun uv _ => le_max_left _ _
    exact add_nonneg hBnonneg (mul_nonneg hthresholdNonneg (hEoff u v huv))
  · exact sufficientRefreshRate_dominates_negative_entry B E u v
      (lt_of_not_ge hBnonneg) (hsupport u v huv (lt_of_not_ge hBnonneg))

/-- The refresh term is invisible to both quotient legs, so the fine
generator retains the exact coarse dynamics. -/
theorem refreshGenerator_exact_quotient_dynamics
    {U Z : Type*} [Fintype U] [Fintype Z] [DecidableEq U] [DecidableEq Z]
    (C : Matrix U Z ℝ) (R : Matrix Z U ℝ) (A : Matrix Z Z ℝ)
    (hRC : R * C = 1) (lam : ℝ) :
    refreshGenerator C R A lam * C = C * A ∧
      R * refreshGenerator C R A lam = A * R := by
  have hleft : (C * R - 1) * C = 0 := by
    rw [Matrix.sub_mul, Matrix.mul_assoc, hRC, Matrix.one_mul,
      Matrix.mul_one, sub_self]
  have hright : R * (C * R - 1) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hRC,
      Matrix.one_mul, sub_self]
  constructor
  · simp only [refreshGenerator, Matrix.add_mul, Matrix.smul_mul, hleft,
      smul_zero, add_zero]
    rw [Matrix.mul_assoc (C * A) R C, hRC, Matrix.mul_one]
  · simp only [refreshGenerator, Matrix.mul_add, Matrix.mul_smul, hright,
      smul_zero, add_zero]
    calc
      R * (C * A * R) = (R * C) * A * R := by simp [Matrix.mul_assoc]
      _ = A * R := by rw [hRC]; simp

/-- If a strongly continuous family is an exact nontrivial reset at every
member of a sequence approaching time zero, its idempotent must be the
identity.  This is the manuscript's `t ↓ 0` obstruction. -/
theorem exact_reset_at_arbitrarily_small_times_forces_identity
    {U : Type*} [Fintype U] [DecidableEq U]
    (E : Matrix U U ℝ) (hE2 : E * E = E)
    (S : ℕ → Matrix U U ℝ)
    (hcontinuous : Filter.Tendsto S Filter.atTop (nhds 1))
    (hreset : ∀ n, S n = E * S n * E) :
    E = 1 := by
  have hresetLimit : Filter.Tendsto (fun n => E * S n * E)
      Filter.atTop (nhds (E * 1 * E)) :=
    (hcontinuous.const_mul E).mul_const E
  have hsecond : Filter.Tendsto S Filter.atTop (nhds (E * 1 * E)) :=
    hresetLimit.congr' (Filter.Eventually.of_forall fun n => (hreset n).symm)
  have hlimit : (1 : Matrix U U ℝ) = E * 1 * E :=
    tendsto_nhds_unique hcontinuous hsecond
  simpa [hE2] using hlimit.symm

end CanonicalFiniteRateFibreRefresh
end NCG
