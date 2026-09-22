/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.Certificates.OrientationCalibrationResidualExact
import RenewalGeometry.Gravity.RelationalSchedulerADM

/-!
# Exact calibration fibre and minimum anchor bank
  (`thm:supp-calibration-fibre`, emergent-spacetime manuscript)

Log-affine calibration coordinates `x ∈ ℝ^N`, incidence relations `Lx = b`
with one solution `x₀`:

* (K1) the calibration fibre is `x₀ + ker L`, of dimension `N − rank L`;
* (K2) exactly `dim ker L` independent scalar anchors are necessary (every
  separating linear anchor bank on `ker L` has at least `dim ker L`
  coordinates) and sufficient (a bijective bank with exactly `dim ker L`
  coordinates exists);
* (K3) with unit conventions `U : ℝ^d → ℝ^N`, `LU = 0`, the intrinsic residual
  is `ker L / Im U`, of dimension `N − rank L − d` for injective `U`, and one
  anchor per quotient direction is necessary and sufficient;
* (K4) the root race: multiplying all directed rates by one positive constant
  leaves the winner law `p_b = k_b / Σ k` unchanged, while the total rate
  `K = Σ k` — the scale of the exponential waiting time, whose mean is `1/K` —
  is multiplied by that constant and, together with the winner law,
  determines every rate `k_b = p_b K`.

Main declaration: `RenewalGeometry.calibration_fibre_anchor_bank`.  The
kernel-level clauses (K1)–(K3, dimension) reuse
`RenewalGeometry.OrientationCalibrationResidual`; the quotient anchor count
and the race clauses are new. -/

open Matrix MeasureTheory Set Module
open RenewalGeometry.OrientationCalibrationResidual

namespace RenewalGeometry

section AnchorBank

variable {Q : Type*} [AddCommGroup Q] [Module ℝ Q] [Module.Finite ℝ Q]

omit [Module.Finite ℝ Q] in
/-- Any separating (injective) linear anchor bank on a finite-dimensional
direction space has at least `dim` scalar anchors
(`thm:supp-calibration-fibre` (K2)/(K3), necessity). -/
theorem anchor_bank_necessary (k : ℕ) (A : Q →ₗ[ℝ] (Fin k → ℝ))
    (hA : Function.Injective A) : finrank ℝ Q ≤ k := by
  have h := A.finrank_le_finrank_of_injective hA
  simpa using h

/-- A basis and its coordinate functionals give a bijective anchor bank with
exactly `dim` scalar anchors (`thm:supp-calibration-fibre` (K2)/(K3),
sufficiency). -/
theorem anchor_bank_sufficient :
    ∃ A : Q →ₗ[ℝ] (Fin (finrank ℝ Q) → ℝ), Function.Bijective A := by
  let e : Q ≃ₗ[ℝ] (Fin (finrank ℝ Q) → ℝ) :=
    LinearEquiv.ofFinrankEq _ _ (by simp)
  exact ⟨e.toLinearMap, e.bijective⟩

end AnchorBank

section Race

/-- Exponential moments of the race clock:
`∫₀^∞ tⁿ e^{-Kt} dt = n! / K^{n+1}`. -/
private lemma race_exp_moment (K : ℝ) (hK : 0 < K) (n : ℕ) :
    ∫ t in Ioi (0 : ℝ), t ^ n * Real.exp (-(K * t))
      = n.factorial / K ^ (n + 1) := by
  have hsub := integral_comp_mul_left_Ioi
    (fun x => x ^ n * Real.exp (-x)) 0 hK
  simp only [mul_zero] at hsub
  have hL : (∫ x in Ioi (0 : ℝ),
      (K * x) ^ n * Real.exp (-(K * x)))
      = K ^ n * ∫ x in Ioi (0 : ℝ),
        x ^ n * Real.exp (-(K * x)) := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.setIntegral_congr_fun
      measurableSet_Ioi
    intro x _
    simp only [mul_pow]
    ring
  have hG : (∫ x in Ioi (0 : ℝ),
      x ^ n * Real.exp (-x)) = n.factorial := by
    have h1 := Real.Gamma_eq_integral
      (s := (n : ℝ) + 1) (by positivity)
    have h2 := Real.Gamma_nat_eq_factorial n
    rw [h1] at h2
    rw [← h2]
    apply MeasureTheory.setIntegral_congr_fun
      measurableSet_Ioi
    intro x _
    simp only [add_sub_cancel_right, Real.rpow_natCast]
    ring
  rw [hL, hG] at hsub
  have hKne : K ≠ 0 := ne_of_gt hK
  rw [smul_eq_mul] at hsub
  rw [pow_succ]
  field_simp at hsub ⊢
  nlinarith [hsub]

/-- The exponential waiting time of total rate `K` has mean `1/K`: the
waiting-time scale is the inverse total rate
(`thm:supp-calibration-fibre` (K4)). -/
theorem race_waiting_time_mean (K : ℝ) (hK : 0 < K) :
    ∫ t in Ioi (0 : ℝ), t * (K * Real.exp (-(K * t))) = K⁻¹ := by
  have h1 := race_exp_moment K hK 1
  have hfun : (fun t : ℝ => t * (K * Real.exp (-(K * t))))
      = fun t : ℝ => K * (t ^ 1 * Real.exp (-(K * t))) := by
    funext t
    ring
  rw [hfun, MeasureTheory.integral_const_mul, h1]
  have hKne : K ≠ 0 := ne_of_gt hK
  simp only [Nat.factorial_one, Nat.cast_one]
  field_simp

end Race

/-- **Theorem `thm:supp-calibration-fibre`** (K1)–(K4), for log-affine
calibration coordinates `x ∈ ℝ^N`, incidence relations `Lx = b` with one
solution `x₀`, and injective unit conventions `U : ℝ^d → ℝ^N` with `LU = 0`.
Anchor banks are linear maps to `ℝ^k`; "determining one calibration" is
injectivity on the direction space. -/
theorem calibration_fibre_anchor_bank {N M d : ℕ}
    (L : (Fin N → ℝ) →ₗ[ℝ] (Fin M → ℝ)) (b : Fin M → ℝ)
    (x₀ : Fin N → ℝ) (hx₀ : L x₀ = b)
    (U : (Fin d → ℝ) →ₗ[ℝ] (Fin N → ℝ)) (hLU : L.comp U = 0)
    (hU : Function.Injective U) :
    -- (K1) the calibration fibre is `x₀ + ker L`, of dimension `N − rank L`
    (({x | L x = b} : Set (Fin N → ℝ)) = {x | x - x₀ ∈ LinearMap.ker L}
      ∧ finrank ℝ (LinearMap.ker L) = N - finrank ℝ (LinearMap.range L))
    -- (K2) exactly `dim ker L` scalar anchors are necessary and sufficient
    ∧ ((∀ (k : ℕ) (A : LinearMap.ker L →ₗ[ℝ] (Fin k → ℝ)),
          Function.Injective A → finrank ℝ (LinearMap.ker L) ≤ k)
      ∧ ∃ A : LinearMap.ker L →ₗ[ℝ]
          (Fin (finrank ℝ (LinearMap.ker L)) → ℝ), Function.Bijective A)
    -- (K3) the physical residual `ker L / Im U` and its anchor count
    ∧ (finrank ℝ (PhysicalResidual L U hLU)
          = N - finrank ℝ (LinearMap.range L) - d
      ∧ (∀ (k : ℕ) (A : PhysicalResidual L U hLU →ₗ[ℝ] (Fin k → ℝ)),
          Function.Injective A → finrank ℝ (PhysicalResidual L U hLU) ≤ k)
      ∧ ∃ A : PhysicalResidual L U hLU →ₗ[ℝ]
          (Fin (finrank ℝ (PhysicalResidual L U hLU)) → ℝ),
          Function.Bijective A)
    -- (K4) the root race: the winner law is invariant under a common
    -- rescaling of the rates …
    ∧ ((∀ (k : Fin 6 → ℝ) (lam : ℝ), 0 < lam → (∀ a, 0 < k a) → ∀ b,
          (lam * k b) / (∑ j, lam * k j) = k b / (∑ j, k j))
      -- … while the total rate (the waiting-time scale) is rescaled …
      ∧ (∀ (k : Fin 6 → ℝ) (lam : ℝ),
          (∑ j, lam * k j) = lam * ∑ j, k j)
      ∧ (∀ (k : Fin 6 → ℝ) (lam : ℝ), 0 < lam → (∀ a, 0 < k a) →
          lam ≠ 1 → (∑ j, lam * k j) ≠ ∑ j, k j)
      -- … the exponential waiting time of total rate `K` has mean `1/K` …
      ∧ (∀ K : ℝ, 0 < K →
          ∫ t in Ioi (0 : ℝ), t * (K * Real.exp (-(K * t))) = K⁻¹)
      -- … and the winner law together with the total rate fixes every rate
      ∧ (∀ (k : Fin 6 → ℝ), (∀ a, 0 < k a) → ∀ b,
          k b = (k b / ∑ j, k j) * ∑ j, k j)) := by
  obtain ⟨_, _, _, hA3', _, _⟩ := relational_scheduler_ADM
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨hA3', ?_, ?_, ?_, ?_⟩⟩
  · -- (K1) fibre
    exact affineFibre_eq_kernelTranslate L b x₀ hx₀
  · -- (K1) dimension
    have h := calibration_kernel_dimension L
    simpa only [finrank_pi, Fintype.card_fin] using h
  · -- (K2) necessity
    intro k A hA
    exact anchor_bank_lower_bound L k A hA
  · -- (K2) sufficiency
    exact exists_minimal_anchor_bank L
  · -- (K3) dimension
    have h := physicalResidual_dimension L U hLU hU
    simpa only [finrank_pi, Fintype.card_fin] using h
  · -- (K3) necessity on the quotient
    intro k A hA
    exact anchor_bank_necessary k A hA
  · -- (K3) sufficiency on the quotient
    exact anchor_bank_sufficient
  · -- (K4) the total rate is rescaled
    intro k lam
    rw [Finset.mul_sum]
  · -- (K4) a nontrivial rescaling changes the total rate
    intro k lam hlam hk hlam1
    rw [← Finset.mul_sum]
    have hKpos : 0 < ∑ j, k j :=
      Finset.sum_pos (fun a _ => hk a) Finset.univ_nonempty
    intro h
    have : (lam - 1) * ∑ j, k j = 0 := by linarith
    rcases mul_eq_zero.mp this with h1 | h1
    · exact hlam1 (by linarith)
    · exact absurd h1 (ne_of_gt hKpos)
  · -- (K4) mean waiting time
    intro K hK
    exact race_waiting_time_mean K hK
  · -- (K4) rates from winner law and total rate
    intro k hk b
    have hKpos : 0 < ∑ j, k j :=
      Finset.sum_pos (fun a _ => hk a) Finset.univ_nonempty
    field_simp

end RenewalGeometry
-- AXIOMCHECK
#print axioms RenewalGeometry.calibration_fibre_anchor_bank
#print axioms RenewalGeometry.anchor_bank_necessary
#print axioms RenewalGeometry.anchor_bank_sufficient
#print axioms RenewalGeometry.race_waiting_time_mean
