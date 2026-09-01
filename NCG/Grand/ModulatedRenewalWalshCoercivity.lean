/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.HardCoreDegreeBandedModulation
import NCG.Grand.RenewalInterchangeWalshGap

/-!
# Coercivity of the one-direction modulated renewal model

This file supplies the rate comparison and Walsh-sector estimates used in
`thm:modulated-renewal-Schur-Mori`.  In particular, the estimates below are
for the actual Boolean score and the actual state-dependent torus swap rate,
not for a supplied scalar lower bound.
-/

open Finset

namespace NCG
namespace ModulatedRenewalWalshCoercivity

open FlipInterchange
open InterchangeAudit
open RenewalInterchangeWalshGap

/-- The centered one-site phase score in the renewal equilibrium with
probabilities `P = 6/11` and `H = 5/11`. -/
noncomputable def phaseScore (b : Bool) : ℝ :=
  if b then 5 / Real.sqrt 30 else -6 / Real.sqrt 30

/-- The exact sup-norm of the phase score. -/
noncomputable def qPhi : ℝ := 6 / Real.sqrt 30

theorem qPhi_pos : 0 < qPhi := by
  unfold qPhi
  positivity

theorem phaseScore_centered :
    (6 / 11 : ℝ) * phaseScore true + (5 / 11 : ℝ) * phaseScore false = 0 := by
  simp [phaseScore]
  ring

theorem abs_phaseScore_le (b : Bool) : |phaseScore b| ≤ qPhi := by
  have hs : 0 < Real.sqrt 30 := Real.sqrt_pos.2 (by norm_num)
  cases b
  · simp only [phaseScore, Bool.false_eq_true, ↓reduceIte, qPhi]
    have h6 : 0 < 6 / Real.sqrt 30 := by positivity
    rw [show -6 / Real.sqrt 30 = -(6 / Real.sqrt 30) by ring,
      abs_neg, abs_of_pos h6]
  · simp only [phaseScore, ↓reduceIte, qPhi]
    have h5 : 0 < 5 / Real.sqrt 30 := by positivity
    rw [abs_of_pos h5]
    exact div_le_div_of_nonneg_right (by norm_num) hs.le

/-- A bounded multiplier cannot reduce `1 + θφ` below
`1 - |θ|q`. -/
theorem modulationFactor_floor {θ φ q : ℝ}
    (hφ : |φ| ≤ q) :
    1 - |θ| * q ≤ 1 + θ * φ := by
  have hscale : |θ| * |φ| ≤ |θ| * q :=
    mul_le_mul_of_nonneg_left hφ (abs_nonneg θ)
  have hprod : -( |θ| * |φ| ) ≤ θ * φ := by
    simpa [abs_mul] using neg_abs_le (θ * φ)
  linarith

theorem phase_modulationFactor_floor (θ : ℝ) (b : Bool) :
    1 - |θ| * qPhi ≤ 1 + θ * phaseScore b :=
  modulationFactor_floor (abs_phaseScore_le b)

theorem phase_modulationFactor_pos {θ : ℝ}
    (hθ : |θ| * qPhi < 1) (b : Bool) :
    0 < 1 + θ * phaseScore b :=
  lt_of_lt_of_le (sub_pos.2 hθ) (phase_modulationFactor_floor θ b)

/-- On the selected positive `e₁` edges, the actual rate is bounded below by
the manuscript's uniformly elliptic rate. -/
theorem longitudinal_swapRate_floor {N : ℕ} [NeZero N]
    {κ θ : ℝ} (hκ : 0 ≤ κ) (η : Config N) (x : Site N) :
    κ * (N : ℝ) ^ 2 * (1 - |θ| * qPhi) ≤
      swapRate κ θ phaseScore η x 0 := by
  rw [swapRate, modFactor, if_pos rfl]
  exact mul_le_mul_of_nonneg_left
    (phase_modulationFactor_floor θ (η (x + 2 • unitVec 0)))
    (mul_nonneg hκ (sq_nonneg _))

/-- The two transverse directed rates are literally unchanged. -/
theorem transverse_swapRate_exact {N : ℕ} [NeZero N]
    (κ θ : ℝ) (η : Config N) (x : Site N) (j : Fin 3) (hj : j ≠ 0) :
    swapRate κ θ phaseScore η x j = κ * (N : ℝ) ^ 2 := by
  simp [swapRate, modFactor, hj]

/-- Admissibility makes every actual state-dependent swap rate nonnegative. -/
theorem swapRate_nonneg {N : ℕ} [NeZero N]
    {κ θ : ℝ} (hκ : 0 ≤ κ) (hθ : |θ| * qPhi < 1)
    (η : Config N) (x : Site N) (j : Fin 3) :
    0 ≤ swapRate κ θ phaseScore η x j := by
  unfold swapRate modFactor
  apply mul_nonneg (mul_nonneg hκ (sq_nonneg _))
  split_ifs with hj
  · exact (phase_modulationFactor_pos hθ _).le
  · exact zero_le_one

/-- Coefficients supported in Walsh degree at least two. -/
def HigherChaos {V : Type*} (f : Finset V → ℝ) : Prop :=
  ∀ A, A.card < 2 → f A = 0

/-- Coefficients supported exactly in the first Walsh sector. -/
def FirstChaos {V : Type*} (f : Finset V → ℝ) : Prop :=
  ∀ A, A.card ≠ 1 → f A = 0

theorem firstChaosCoefficients_firstChaos {V : Type*}
    [Fintype V] [DecidableEq V] (c : V → ℝ) :
    FirstChaos (firstChaosCoefficients c) := by
  intro A hA
  unfold firstChaosCoefficients
  apply Finset.sum_eq_zero
  intro v _
  have hne : A ≠ {v} := by
    intro h
    apply hA
    simp [h]
  simp [hne]

/-- The local renewal number operator has the exact floor `2g` on higher
Walsh chaos. -/
theorem renewalWalshEnergy_higherChaos_floor {V : Type*} [Fintype V]
    {g : ℝ} (hg : 0 ≤ g) (f : Finset V → ℝ) (hf : HigherChaos f) :
    2 * g * walshNormSq f ≤ renewalWalshEnergy g f := by
  rw [walshNormSq, renewalWalshEnergy, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro A _
  by_cases hcard : A.card < 2
  · rw [hf A hcard]
    norm_num
  · have hcardNat : 2 ≤ A.card := by omega
    have hcardReal : (2 : ℝ) ≤ A.card := by exact_mod_cast hcardNat
    have hsquare : 0 ≤ (f A) ^ 2 := sq_nonneg _
    calc
      2 * g * (f A) ^ 2 ≤ g * (A.card : ℝ) * (f A) ^ 2 := by
        exact mul_le_mul_of_nonneg_right
          (by simpa [mul_comm] using mul_le_mul_of_nonneg_left hcardReal hg)
          hsquare
      _ = g * ↑A.card * (f A) ^ 2 := rfl

/-- Adding any nonnegative interchange energy preserves the higher-chaos
`2g` floor. -/
theorem renewalInterchange_higherChaos_floor {V : Type*}
    [Fintype V] [DecidableEq V]
    {g : ℝ} (hg : 0 ≤ g) (edges : Finset (V × V))
    (rate : V → V → ℝ) (hrate : ∀ p ∈ edges, 0 ≤ rate p.1 p.2)
    (f : Finset V → ℝ) (hf : HigherChaos f) :
    2 * g * walshNormSq f ≤
      renewalWalshEnergy g f + interchangeWalshEnergy edges rate f := by
  exact (renewalWalshEnergy_higherChaos_floor hg f hf).trans
    (le_add_of_nonneg_right (interchangeWalshEnergy_nonneg edges rate hrate f))

/-- Monotonicity of the genuine Walsh interchange Dirichlet energy in every
edge rate. -/
theorem interchangeWalshEnergy_mono {V : Type*}
    [Fintype V] [DecidableEq V]
    (edges : Finset (V × V)) {rate₀ rate₁ : V → V → ℝ}
    (h : ∀ p ∈ edges, rate₀ p.1 p.2 ≤ rate₁ p.1 p.2)
    (f : Finset V → ℝ) :
    interchangeWalshEnergy edges rate₀ f ≤
      interchangeWalshEnergy edges rate₁ f := by
  unfold interchangeWalshEnergy
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro p hp
  exact mul_le_mul_of_nonneg_right (h p hp)
    (Finset.sum_nonneg fun _ _ => sq_nonneg _)

private theorem swap_card {V : Type*} [DecidableEq V]
    (i j : V) (A : Finset V) :
    (swapSupport i j A).card = A.card := by
  exact Finset.card_image_of_injective A (Equiv.swap i j).injective

/-- A transposition preserves Walsh degree, so the squared edge difference
has no cross term between first and higher chaos. -/
theorem swapDifference_sq_add {V : Type*} [DecidableEq V]
    {f₁ f₂ : Finset V → ℝ} (hf₁ : FirstChaos f₁)
    (hf₂ : HigherChaos f₂) (i j : V) (A : Finset V) :
    ((f₁ + f₂) A - (f₁ + f₂) (swapSupport i j A)) ^ 2 =
      (f₁ A - f₁ (swapSupport i j A)) ^ 2 +
        (f₂ A - f₂ (swapSupport i j A)) ^ 2 := by
  have hcard := swap_card i j A
  by_cases hA : A.card = 1
  · have hlt : A.card < 2 := by omega
    have hswaplt : (swapSupport i j A).card < 2 := by omega
    simp only [Pi.add_apply]
    rw [hf₂ A hlt, hf₂ _ hswaplt]
    ring
  · have hswap : (swapSupport i j A).card ≠ 1 := by simpa [hcard] using hA
    simp only [Pi.add_apply]
    rw [hf₁ A hA, hf₁ _ hswap]
    ring

/-- The diagonal renewal form splits exactly across the first/higher
decomposition. -/
theorem renewalWalshEnergy_first_add_higher {V : Type*} [Fintype V]
    (g : ℝ) {f₁ f₂ : Finset V → ℝ}
    (hf₁ : FirstChaos f₁) (hf₂ : HigherChaos f₂) :
    renewalWalshEnergy g (f₁ + f₂) =
      renewalWalshEnergy g f₁ + renewalWalshEnergy g f₂ := by
  unfold renewalWalshEnergy
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro A _
  by_cases hA : A.card = 1
  · have hlt : A.card < 2 := by omega
    simp only [Pi.add_apply]
    rw [hf₂ A hlt]
    ring
  · simp only [Pi.add_apply]
    rw [hf₁ A hA]
    ring

/-- Every constant-rate interchange form splits exactly across first and
higher Walsh chaos. -/
theorem interchangeWalshEnergy_first_add_higher {V : Type*}
    [Fintype V] [DecidableEq V]
    (edges : Finset (V × V)) (rate : V → V → ℝ)
    {f₁ f₂ : Finset V → ℝ} (hf₁ : FirstChaos f₁)
    (hf₂ : HigherChaos f₂) :
    interchangeWalshEnergy edges rate (f₁ + f₂) =
      interchangeWalshEnergy edges rate f₁ +
        interchangeWalshEnergy edges rate f₂ := by
  unfold interchangeWalshEnergy
  simp_rw [swapDifference_sq_add hf₁ hf₂]
  simp_rw [Finset.sum_add_distrib, mul_add]
  rw [Finset.sum_add_distrib]
  ring

/-- Renewal acts with exactly the mass `g` on the whole first Walsh sector. -/
theorem renewalWalshEnergy_firstChaos_exact {V : Type*} [Fintype V]
    (g : ℝ) (f : Finset V → ℝ) (hf : FirstChaos f) :
    renewalWalshEnergy g f = g * walshNormSq f := by
  rw [renewalWalshEnergy, walshNormSq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A _
  by_cases hA : A.card = 1
  · simp [hA]
  · rw [hf A hA]
    simp

/-- Directed-axis Dirichlet energy for the actual configuration-dependent
swap rates.  No reversibility assumption is needed for rate comparison. -/
noncomputable def axisSwapEnergy {N : ℕ} [NeZero N]
    (μ : Config N → ℝ)
    (rate : Config N → Site N → Fin 3 → ℝ) (j : Fin 3)
    (f : Config N → ℝ) : ℝ :=
  (2 : ℝ)⁻¹ * ∑ η, μ η * ∑ x, rate η x j *
    (f η - f (swapAt η x (x + unitVec j))) ^ 2

theorem axisSwapEnergy_mono {N : ℕ} [NeZero N]
    (μ : Config N → ℝ) (hμ : ∀ η, 0 ≤ μ η)
    {rate₀ rate₁ : Config N → Site N → Fin 3 → ℝ} (j : Fin 3)
    (hrate : ∀ η x, rate₀ η x j ≤ rate₁ η x j)
    (f : Config N → ℝ) :
    axisSwapEnergy μ rate₀ j f ≤ axisSwapEnergy μ rate₁ j f := by
  unfold axisSwapEnergy
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro η _
  apply mul_le_mul_of_nonneg_left _ (hμ η)
  apply Finset.sum_le_sum
  intro x _
  exact mul_le_mul_of_nonneg_right (hrate η x) (sq_nonneg _)

/-- The actual longitudinal Dirichlet form dominates the constant form with
coefficient `κ N² (1 - |θ|qφ)`. -/
theorem longitudinal_axisSwapEnergy_floor {N : ℕ} [NeZero N]
    {κ θ : ℝ} (hκ : 0 ≤ κ) (μ : Config N → ℝ)
    (hμ : ∀ η, 0 ≤ μ η) (f : Config N → ℝ) :
    axisSwapEnergy μ
        (fun _ _ _ => κ * (N : ℝ) ^ 2 * (1 - |θ| * qPhi)) 0 f ≤
      axisSwapEnergy μ (swapRate κ θ phaseScore) 0 f := by
  apply axisSwapEnergy_mono μ hμ
  intro η x
  exact longitudinal_swapRate_floor hκ η x

/-- On either transverse axis the actual Dirichlet form is the unmodulated
constant-rate form exactly. -/
theorem transverse_axisSwapEnergy_exact {N : ℕ} [NeZero N]
    (κ θ : ℝ) (μ : Config N → ℝ) (f : Config N → ℝ)
    (j : Fin 3) (hj : j ≠ 0) :
    axisSwapEnergy μ (swapRate κ θ phaseScore) j f =
      axisSwapEnergy μ (fun _ _ _ => κ * (N : ℝ) ^ 2) j f := by
  unfold axisSwapEnergy
  simp_rw [transverse_swapRate_exact κ θ _ _ j hj]

end ModulatedRenewalWalshCoercivity
end NCG
