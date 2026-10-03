/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.SupplementStochasticCurvature

/-!
# Uniform expected squared spacetime curvature norm
  (`cor:supp-stochastic-curvature`, middle sentence; emergent-spacetime manuscript)

`SupplementStochasticCurvature` proves `eq:supp-expected-curvature`
(`expected_curvature_energy_bound`) and the pathwise upgrade.  This file proves the sentence
*"together with the stable interpolation and lapse bounds, uniformity of these budgets gives a
uniform expected squared spacetime curvature norm"*:

* `sq_l2_curvature_le_sup_sq` — pathwise: the interpolation/lapse/reconstruction budget of
  `derived_l2_curvature_bound` (`‖R‖_{L²(K)} ≤ (∫₀^{T_*} N ρ²)^{1/2} + C_ζ`, `0 ≤ ρ ≤ C_I z`,
  `0 ≤ N ≤ N_*`), squared:
  `‖R‖²_{L²(K)} ≤ 2 C_I² N_* T_* sup_{t ≤ T_*} z(t)² + 2 C_ζ²`;
* `expected_l2_curvature_bound` — integrating in `ω` and combining with
  `eq:supp-expected-curvature`:
  `𝔼 ‖R‖²_{L²(K)} ≤ 2 C_I² N_* T_* · 2e^{2A_*}[𝔼 z(0)² + 2T_* ∫ Γ̄ C Δ + 2T_* 𝔼 ∫ ‖r^{src}‖²_H]
    + 2 C_ζ²`;
* `uniform_expected_l2_curvature_bound` — for a family of cutoffs `X` with uniform budgets
  (`𝔼 z_X(0)² ≤ Z₀`, `𝔼 ∫ ‖r_X^{src}‖² ≤ ϱ`, deterministic supported bounds `Γ_X ≤ Γ̄`,
  `𝔼 ‖𝔞_X(t)‖²_{G⁻¹} ≤ C(t) Δ(t)` with `∫ Γ̄ C Δ < ∞`, common `A_*`, `T_*`, `C_I`, `N_*`, `C_ζ`):
  `sup_X 𝔼 ‖R_X‖²_{L²(K)} < ∞`, with the explicit bound above.

Expectations are lintegrals of the nonnegative quantities against a probability measure.
-/

open scoped InnerProductSpace ENNReal
open MeasureTheory Filter

namespace RenewalGeometry

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Pathwise squared `L²` curvature bound from the interpolation, lapse and reconstruction
budgets: `‖R‖² ≤ 2 C_I² (N_* T) sup_{t ≤ T} z(t)² + 2 C_ζ²` (as extended reals). -/
theorem sq_l2_curvature_le_sup_sq (z ρ N : ℝ → ℝ) {T Nstar CI Cζ RL2 : ℝ}
    (hT : 0 ≤ T) (hCI : 0 ≤ CI) (hRL0 : 0 ≤ RL2)
    (hzB : ∃ B, ∀ t ∈ Set.Icc 0 T, z t ≤ B)
    (hz0 : ∀ t ∈ Set.Icc 0 T, 0 ≤ z t)
    (hρ : ∀ t ∈ Set.Icc 0 T, 0 ≤ ρ t ∧ ρ t ≤ CI * z t)
    (hN : ∀ t ∈ Set.Icc 0 T, 0 ≤ N t ∧ N t ≤ Nstar)
    (hint : IntervalIntegrable (fun t => N t * ρ t ^ 2) volume 0 T)
    (hR : RL2 ≤ Real.sqrt (∫ t in (0:ℝ)..T, N t * ρ t ^ 2) + Cζ) :
    ENNReal.ofReal (RL2 ^ 2) ≤
      ENNReal.ofReal (2 * (CI ^ 2 * (Nstar * T))) * (⨆ t ∈ Set.Icc 0 T, ENNReal.ofReal (z t ^ 2))
        + ENNReal.ofReal (2 * Cζ ^ 2) := by
  have hNstar : 0 ≤ Nstar := ((hN 0 ⟨le_rfl, hT⟩).1).trans (hN 0 ⟨le_rfl, hT⟩).2
  set S : ℝ≥0∞ := ⨆ t ∈ Set.Icc 0 T, ENNReal.ofReal (z t ^ 2) with hS
  obtain ⟨B, hB⟩ := hzB
  have hSfin : S ≠ ∞ := by
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := max B 0 ^ 2)) ?_
    refine iSup₂_le fun t ht => ENNReal.ofReal_le_ofReal ?_
    exact pow_le_pow_left₀ (hz0 t ht) ((hB t ht).trans (le_max_left _ _)) 2
  set B₀ : ℝ := Real.sqrt S.toReal with hB₀
  have hzB₀ : ∀ t ∈ Set.Icc 0 T, z t ≤ B₀ := fun t ht => by
    have h1 : ENNReal.ofReal (z t ^ 2) ≤ S := le_iSup₂ (f := fun t _ => ENNReal.ofReal (z t ^ 2)) t ht
    have h2 : z t ^ 2 ≤ S.toReal := (ENNReal.ofReal_le_iff_le_toReal hSfin).1 h1
    rw [← Real.sqrt_sq (hz0 t ht)]
    exact Real.sqrt_le_sqrt h2
  have hRL := derived_l2_curvature_bound z ρ N hT hCI (Real.sqrt_nonneg _) hzB₀ hz0 hρ hN hint hR
  set a : ℝ := CI * Real.sqrt (Nstar * T) * B₀ with ha
  have ha0 : 0 ≤ a := by positivity
  have hsq : RL2 ^ 2 ≤ 2 * (CI ^ 2 * (Nstar * T)) * S.toReal + 2 * Cζ ^ 2 := by
    have h1 : RL2 ^ 2 ≤ (a + Cζ) ^ 2 := pow_le_pow_left₀ hRL0 hRL 2
    have h2 : (a + Cζ) ^ 2 ≤ 2 * a ^ 2 + 2 * Cζ ^ 2 := by nlinarith [sq_nonneg (a - Cζ)]
    have h3 : a ^ 2 = CI ^ 2 * (Nstar * T) * S.toReal := by
      rw [ha, mul_pow, mul_pow, Real.sq_sqrt (by positivity), hB₀,
        Real.sq_sqrt ENNReal.toReal_nonneg]
    nlinarith [h1, h2, h3]
  calc ENNReal.ofReal (RL2 ^ 2)
      ≤ ENNReal.ofReal (2 * (CI ^ 2 * (Nstar * T)) * S.toReal + 2 * Cζ ^ 2) :=
        ENNReal.ofReal_le_ofReal hsq
    _ = ENNReal.ofReal (2 * (CI ^ 2 * (Nstar * T))) * S + ENNReal.ofReal (2 * Cζ ^ 2) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hSfin]

/-- **Expected squared spacetime curvature norm** (`cor:supp-stochastic-curvature`).  Under the
hypotheses of `expected_curvature_energy_bound` (pathwise propagation estimate, incidence of the
forcing, deterministic supported bound `Γ ≤ Γ̄`, `𝔼‖𝔞(t)‖²_{G⁻¹} ≤ C(t)Δ(t)`) and the pathwise
interpolation/lapse/reconstruction budgets of `derived_l2_curvature_bound`,
`𝔼 ‖R‖²_{L²(K)} ≤ 2 C_I² N_* T_* · 2e^{2A_*}[𝔼 z(0)² + 2T_* ∫ Γ̄ C Δ + 2T_* 𝔼 ∫ ‖r^{src}‖²_H]
  + 2 C_ζ²`. -/
theorem expected_l2_curvature_bound {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {T A : ℝ} (hT : 0 ≤ T)
    (z : Ω → ℝ → ℝ) (G : Ω → ℝ → E →L[ℝ] E) (H : Ω → ℝ → F →L[ℝ] F)
    (R : ∀ ω t, GramSqrt (G ω t)) (S : ∀ ω t, GramSqrt (H ω t))
    (Tr : Ω → ℝ → E →L[ℝ] F) (𝔞 : Ω → ℝ → E) (r f : Ω → ℝ → F) (Γbar C Δ : ℝ → ℝ)
    (hz : ∀ ω t, 0 ≤ z ω t)
    (hpath : ∀ ω, ∀ t ∈ Set.Icc 0 T, z ω t ≤
      Real.exp A * (z ω 0 + ∫ s in Set.Icc 0 T, gramNorm (H ω s) (f ω s)))
    (hfL2 : ∀ ω, MemLp (fun s => gramNorm (H ω s) (f ω s)) 2 (volume.restrict (Set.Icc 0 T)))
    (hinc : ∀ ω t, f ω t = Tr ω t (𝔞 ω t) + r ω t)
    (hΓ0 : ∀ t, 0 ≤ Γbar t) (hΓ : ∀ ω t, amplification (R ω t) (S ω t) (Tr ω t) ≤ Γbar t)
    (hcert : ∀ t ∈ Set.Icc 0 T,
      (∫⁻ ω, ENNReal.ofReal (dualNormSq (R ω t) (𝔞 ω t)) ∂μ) ≤ ENNReal.ofReal (C t * Δ t))
    (hz0meas : AEMeasurable (fun ω => z ω 0) μ)
    (hmeas_t : ∀ ω, AEMeasurable (fun t => Γbar t * dualNormSq (R ω t) (𝔞 ω t))
      (volume.restrict (Set.Icc 0 T)))
    (hmeas : AEMeasurable (fun p : Ω × ℝ => Γbar p.2 * dualNormSq (R p.1 p.2) (𝔞 p.1 p.2))
      (μ.prod (volume.restrict (Set.Icc 0 T))))
    -- pathwise interpolation, lapse and reconstruction budgets
    (ρ N : Ω → ℝ → ℝ) (RL2 : Ω → ℝ) {Nstar CI Cζ : ℝ} (hCI : 0 ≤ CI)
    (hRL0 : ∀ ω, 0 ≤ RL2 ω)
    (hρ : ∀ ω, ∀ t ∈ Set.Icc 0 T, 0 ≤ ρ ω t ∧ ρ ω t ≤ CI * z ω t)
    (hN : ∀ ω, ∀ t ∈ Set.Icc 0 T, 0 ≤ N ω t ∧ N ω t ≤ Nstar)
    (hint : ∀ ω, IntervalIntegrable (fun t => N ω t * ρ ω t ^ 2) volume 0 T)
    (hR : ∀ ω, RL2 ω ≤ Real.sqrt (∫ t in (0:ℝ)..T, N ω t * ρ ω t ^ 2) + Cζ) :
    (∫⁻ ω, ENNReal.ofReal (RL2 ω ^ 2) ∂μ) ≤
      ENNReal.ofReal (2 * (CI ^ 2 * (Nstar * T))) *
        (ENNReal.ofReal (2 * Real.exp (2 * A)) *
          ((∫⁻ ω, ENNReal.ofReal (z ω 0 ^ 2) ∂μ)
            + ENNReal.ofReal (2 * T) *
                (∫⁻ t in Set.Icc 0 T, ENNReal.ofReal (Γbar t * (C t * Δ t)))
            + ENNReal.ofReal (2 * T) *
                (∫⁻ ω, (∫⁻ t in Set.Icc 0 T, ENNReal.ofReal (gramNormSq (H ω t) (r ω t))) ∂μ)))
        + ENNReal.ofReal (2 * Cζ ^ 2) := by
  have hexp := expected_curvature_energy_bound μ hT z G H R S Tr 𝔞 r f Γbar C Δ hz hpath hfL2
    hinc hΓ0 hΓ hcert hz0meas hmeas_t hmeas
  have hpw : ∀ ω, ENNReal.ofReal (RL2 ω ^ 2) ≤
      ENNReal.ofReal (2 * (CI ^ 2 * (Nstar * T))) *
        (⨆ t ∈ Set.Icc 0 T, ENNReal.ofReal (z ω t ^ 2)) + ENNReal.ofReal (2 * Cζ ^ 2) :=
    fun ω => sq_l2_curvature_le_sup_sq (z ω) (ρ ω) (N ω) hT hCI (hRL0 ω)
      ⟨_, hpath ω⟩ (fun t _ => hz ω t) (hρ ω) (hN ω) (hint ω) (hR ω)
  calc (∫⁻ ω, ENNReal.ofReal (RL2 ω ^ 2) ∂μ)
      ≤ ∫⁻ ω, (ENNReal.ofReal (2 * (CI ^ 2 * (Nstar * T))) *
          (⨆ t ∈ Set.Icc 0 T, ENNReal.ofReal (z ω t ^ 2)) + ENNReal.ofReal (2 * Cζ ^ 2)) ∂μ :=
        lintegral_mono hpw
    _ = ENNReal.ofReal (2 * (CI ^ 2 * (Nstar * T))) *
          (∫⁻ ω, ⨆ t ∈ Set.Icc 0 T, ENNReal.ofReal (z ω t ^ 2) ∂μ)
          + ENNReal.ofReal (2 * Cζ ^ 2) := by
        rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const, measure_univ, mul_one]
    _ ≤ _ := by gcongr

/-- **Uniform expected squared spacetime curvature norm** (`cor:supp-stochastic-curvature`):
for a family of cutoffs `X` satisfying the hypotheses of `expected_l2_curvature_bound` with
uniform budgets — common `T_*`, `A_*`, deterministic supported bounds `Γ_X ≤ Γ̄`,
`𝔼 ‖𝔞_X(t)‖²_{G⁻¹} ≤ C(t) Δ(t)` with `∫ Γ̄ C Δ < ∞`, `𝔼 z_X(0)² ≤ Z₀ < ∞`,
`𝔼 ∫ ‖r_X^{src}‖²_H ≤ ϱ < ∞`, and common interpolation/lapse constants `C_I`, `N_*`, `C_ζ` — the
expected squared curvature norms are uniformly bounded: `sup_X 𝔼 ‖R_X‖²_{L²(K)} < ∞`, with
`𝔼 ‖R_X‖² ≤ 2C_I² N_* T_* · 2e^{2A_*}[Z₀ + 2T_* ∫ Γ̄ C Δ + 2T_* ϱ] + 2C_ζ²` for every `X`. -/
theorem uniform_expected_l2_curvature_bound {ι Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {T A : ℝ} (hT : 0 ≤ T)
    (z : ι → Ω → ℝ → ℝ) (G : ι → Ω → ℝ → E →L[ℝ] E) (H : ι → Ω → ℝ → F →L[ℝ] F)
    (R : ∀ X ω t, GramSqrt (G X ω t)) (S : ∀ X ω t, GramSqrt (H X ω t))
    (Tr : ι → Ω → ℝ → E →L[ℝ] F) (𝔞 : ι → Ω → ℝ → E) (r f : ι → Ω → ℝ → F)
    (Γbar C Δ : ℝ → ℝ)
    (hz : ∀ X ω t, 0 ≤ z X ω t)
    (hpath : ∀ X ω, ∀ t ∈ Set.Icc 0 T, z X ω t ≤
      Real.exp A * (z X ω 0 + ∫ s in Set.Icc 0 T, gramNorm (H X ω s) (f X ω s)))
    (hfL2 : ∀ X ω,
      MemLp (fun s => gramNorm (H X ω s) (f X ω s)) 2 (volume.restrict (Set.Icc 0 T)))
    (hinc : ∀ X ω t, f X ω t = Tr X ω t (𝔞 X ω t) + r X ω t)
    (hΓ0 : ∀ t, 0 ≤ Γbar t)
    (hΓ : ∀ X ω t, amplification (R X ω t) (S X ω t) (Tr X ω t) ≤ Γbar t)
    (hcert : ∀ X, ∀ t ∈ Set.Icc 0 T,
      (∫⁻ ω, ENNReal.ofReal (dualNormSq (R X ω t) (𝔞 X ω t)) ∂μ) ≤ ENNReal.ofReal (C t * Δ t))
    (hz0meas : ∀ X, AEMeasurable (fun ω => z X ω 0) μ)
    (hmeas_t : ∀ X ω, AEMeasurable (fun t => Γbar t * dualNormSq (R X ω t) (𝔞 X ω t))
      (volume.restrict (Set.Icc 0 T)))
    (hmeas : ∀ X, AEMeasurable
      (fun p : Ω × ℝ => Γbar p.2 * dualNormSq (R X p.1 p.2) (𝔞 X p.1 p.2))
      (μ.prod (volume.restrict (Set.Icc 0 T))))
    (ρ N : ι → Ω → ℝ → ℝ) (RL2 : ι → Ω → ℝ) {Nstar CI Cζ : ℝ} (hCI : 0 ≤ CI)
    (hRL0 : ∀ X ω, 0 ≤ RL2 X ω)
    (hρ : ∀ X ω, ∀ t ∈ Set.Icc 0 T, 0 ≤ ρ X ω t ∧ ρ X ω t ≤ CI * z X ω t)
    (hN : ∀ X ω, ∀ t ∈ Set.Icc 0 T, 0 ≤ N X ω t ∧ N X ω t ≤ Nstar)
    (hint : ∀ X ω, IntervalIntegrable (fun t => N X ω t * ρ X ω t ^ 2) volume 0 T)
    (hR : ∀ X ω, RL2 X ω ≤ Real.sqrt (∫ t in (0:ℝ)..T, N X ω t * ρ X ω t ^ 2) + Cζ)
    -- uniform budgets
    (Z₀ ϱ : ℝ≥0∞) (hZ₀ : Z₀ ≠ ∞) (hϱ : ϱ ≠ ∞)
    (hΓCΔ : (∫⁻ t in Set.Icc 0 T, ENNReal.ofReal (Γbar t * (C t * Δ t))) ≠ ∞)
    (hinit : ∀ X, (∫⁻ ω, ENNReal.ofReal (z X ω 0 ^ 2) ∂μ) ≤ Z₀)
    (hsrc : ∀ X,
      (∫⁻ ω, (∫⁻ t in Set.Icc 0 T, ENNReal.ofReal (gramNormSq (H X ω t) (r X ω t))) ∂μ) ≤ ϱ) :
    (∀ X, (∫⁻ ω, ENNReal.ofReal (RL2 X ω ^ 2) ∂μ) ≤
      ENNReal.ofReal (2 * (CI ^ 2 * (Nstar * T))) *
        (ENNReal.ofReal (2 * Real.exp (2 * A)) *
          (Z₀ + ENNReal.ofReal (2 * T) *
              (∫⁻ t in Set.Icc 0 T, ENNReal.ofReal (Γbar t * (C t * Δ t)))
            + ENNReal.ofReal (2 * T) * ϱ))
        + ENNReal.ofReal (2 * Cζ ^ 2)) ∧
    (⨆ X, ∫⁻ ω, ENNReal.ofReal (RL2 X ω ^ 2) ∂μ) ≠ ∞ := by
  set Bd : ℝ≥0∞ := ENNReal.ofReal (2 * (CI ^ 2 * (Nstar * T))) *
        (ENNReal.ofReal (2 * Real.exp (2 * A)) *
          (Z₀ + ENNReal.ofReal (2 * T) *
              (∫⁻ t in Set.Icc 0 T, ENNReal.ofReal (Γbar t * (C t * Δ t)))
            + ENNReal.ofReal (2 * T) * ϱ))
        + ENNReal.ofReal (2 * Cζ ^ 2) with hBd
  have hall : ∀ X, (∫⁻ ω, ENNReal.ofReal (RL2 X ω ^ 2) ∂μ) ≤ Bd := fun X => by
    refine (expected_l2_curvature_bound μ hT (z X) (G X) (H X) (R X) (S X) (Tr X) (𝔞 X) (r X)
      (f X) Γbar C Δ (hz X) (hpath X) (hfL2 X) (hinc X) hΓ0 (hΓ X) (hcert X) (hz0meas X)
      (hmeas_t X) (hmeas X) (ρ X) (N X) (RL2 X) hCI (hRL0 X) (hρ X) (hN X) (hint X)
      (hR X)).trans ?_
    rw [hBd]
    gcongr
    · exact hinit X
    · exact hsrc X
  have hBdfin : Bd ≠ ∞ := by
    rw [hBd]
    refine ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_), ENNReal.ofReal_ne_top⟩
    exact ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨hZ₀,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hΓCΔ⟩, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hϱ⟩
  exact ⟨hall, ne_top_of_le_ne_top hBdfin (iSup_le hall)⟩

/-- The trivial Gram square root of the identity (used for the non-vacuity check). -/
def gramSqrtId : GramSqrt (ContinuousLinearMap.id ℝ ℝ) where
  sqrt := ContinuousLinearEquiv.refl ℝ ℝ
  selfAdjoint := fun _ _ => rfl
  mul_self := fun _ => rfl

/-- Non-vacuity: the hypothesis packet of `uniform_expected_l2_curvature_bound` is satisfiable
(scalar Grams, the zero forcing and curvature on a one-point probability space, a constant
nonzero initial energy is allowed through `Z₀`). -/
example : (⨆ _X : ℕ, ∫⁻ _ω, ENNReal.ofReal ((0 : ℝ) ^ 2) ∂(Measure.dirac ())) ≠ ∞ := by
  have h := uniform_expected_l2_curvature_bound (ι := ℕ) (E := ℝ) (F := ℝ) (Measure.dirac ())
    (T := 1) (A := 0) zero_le_one (fun _ _ _ => 0) (fun _ _ _ => ContinuousLinearMap.id ℝ ℝ)
    (fun _ _ _ => ContinuousLinearMap.id ℝ ℝ) (fun _ _ _ => gramSqrtId) (fun _ _ _ => gramSqrtId)
    (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ => 0) (fun _ => 0)
    (fun _ => 0) (fun _ _ _ => le_rfl) (fun _ _ t _ => by simp [gramNorm, gramNormSq])
    (fun _ _ => by simp [gramNorm, gramNormSq]) (fun _ _ _ => by simp) (fun _ => le_rfl)
    (fun _ _ _ => by simp [amplification, normalizedTransfer])
    (fun _ t _ => by simp [dualNormSq, GramSqrt.gramInv]) (fun _ => aemeasurable_const)
    (fun _ _ => by simp) (fun _ => by simp)
    (fun _ _ _ => 0) (fun _ _ _ => 0) (fun _ _ => 0) (Nstar := 0) (CI := 0) (Cζ := 0) le_rfl
    (fun _ _ => le_rfl) (fun _ _ _ _ => by simp) (fun _ _ _ _ => by simp)
    (fun _ _ => by simp) (fun _ _ => by simp) 0 0 ENNReal.zero_ne_top ENNReal.zero_ne_top
    (by simp) (fun _ => by simp) (fun _ => by simp [gramNormSq])
  exact h.2

end RenewalGeometry
