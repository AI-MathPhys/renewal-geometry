/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.TorusWaveEnergyUniqueness

/-!
# Forced wave energy on `[0, T] × 𝕋³` with an `L¹`-in-time source and an integrable potential

Generic infrastructure (no renewal notions) for `prop:subsidiary` (`eq:constraint-bound`) and
`thm:hyperbolic` (`eq:hyperbolic-energy`) of the Einstein–Standard-Model action-closure manuscript.

* `sqrt_energy_gronwall` (**square-root Gronwall with an `L¹` source**): if `E ≥ 0` is continuous on
  `[0, T]`, differentiable on `(0, T)` with `E' ≤ k E + 2 w √E` for continuous `k, w ≥ 0`, then
  `√E(t) ≤ (√E(0) + ∫₀ᵗ w) exp(½∫₀ᵗ k)`.  The proof applies the scalar inequality to
  `(E + δ)^{1/2}` and lets `δ ↓ 0`, exactly as in the manuscript; the source enters through its
  `L¹` norm, not a squared norm.
* `ForcedSolves` — a classical solution of the linear second-order system of
  `TorusWaveEnergyUniqueness` (`a ∂ₜ²u_b = 2βⁱ∂ᵢ∂ₜu_b + γ^{ij}∂ᵢ∂ⱼu_b + L_b`) whose non-principal part
  splits as `L = L₀ + W` with a lower-order part `Σ_b L₀,b² ≤ m(t)² Σ_b(|∂ₜu_b|² + |∇u_b|² + u_b²)`
  (a time-integrable potential `m`, e.g. an `L¹_t L^∞_x` curvature potential) and an arbitrary
  continuous forcing `W`.
* `ForcedSolves.energy_deriv_le` — `E' ≤ ((16M + 2 + 2m(t))/c) E + 2 c^{-1/2} ‖W(t)‖_{L²} √E`,
  `c = min(a₀, λ, 1)`.
* **`ForcedSolves.sqrt_energy_le`** — `√E(t) ≤ (√E(0) + c^{-1/2}∫₀ᵗ‖W‖_{L²}) exp(½∫₀ᵗ k)`.
* **`ForcedSolves.size_bound`** — the `L^∞_t L²_x` bound of `(u, ∂ₜu, ∇u)` by the initial data and
  `‖W‖_{L¹_t L²_x}` (`eq:constraint-bound` for an abstract one-form wave system).
-/

open MeasureTheory Filter Topology UnitAddTorus Set
open scoped BigOperators

namespace RenewalGeometry.TorusWaveEnergyForced

open TorusSobolevTransfer TorusWaveEnergy

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : MeasureTheory.IsProbabilityMeasure
    (MeasureTheory.volume : MeasureTheory.Measure UnitAddCircle) :=
  inferInstanceAs (MeasureTheory.IsProbabilityMeasure AddCircle.haarAddCircle)

local instance : MeasureTheory.Measure.IsAddHaarMeasure
    (MeasureTheory.volume : MeasureTheory.Measure UnitAddCircle) :=
  inferInstanceAs (MeasureTheory.Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

noncomputable section

set_option linter.unusedSectionVars false

/-! ### The square-root Gronwall inequality with an `L¹` source -/

/-- For `δ > 0` the bound for `(E + δ)^{1/2}`. -/
theorem sqrt_add_gronwall {E E' k w : ℝ → ℝ} {T δ : ℝ} (hδ : 0 < δ)
    (hEc : ContinuousOn E (Icc 0 T)) (hE0 : ∀ t ∈ Icc 0 T, 0 ≤ E t)
    (hEd : ∀ t ∈ Ioo 0 T, HasDerivAt E (E' t) t)
    (hk : Continuous k) (hw : Continuous w) (hk0 : ∀ t, 0 ≤ k t) (hw0 : ∀ t, 0 ≤ w t)
    (hineq : ∀ t ∈ Ioo 0 T, E' t ≤ k t * E t + 2 * w t * Real.sqrt (E t)) :
    ∀ t ∈ Icc 0 T, Real.sqrt (E t + δ) ≤
      (Real.sqrt (E 0 + δ) + ∫ s in (0)..t, w s) * Real.exp ((∫ s in (0)..t, k s) / 2) := by
  set K : ℝ → ℝ := fun t => (∫ s in (0)..t, k s) / 2 with hK
  set Wi : ℝ → ℝ := fun t => ∫ s in (0)..t, w s with hWi
  set φ : ℝ → ℝ := fun t => Real.sqrt (E t + δ) with hφ
  set ψ : ℝ → ℝ := fun t => φ t * Real.exp (-K t) - Wi t with hψ
  have hKd : ∀ t, HasDerivAt K (k t / 2) t := fun t =>
    (intervalIntegral.integral_hasDerivAt_right (hk.intervalIntegrable _ _) hk.aestronglyMeasurable.stronglyMeasurableAtFilter
      hk.continuousAt).div_const 2
  have hWd : ∀ t, HasDerivAt Wi (w t) t := fun t =>
    intervalIntegral.integral_hasDerivAt_right (hw.intervalIntegrable _ _) hw.aestronglyMeasurable.stronglyMeasurableAtFilter
      hw.continuousAt
  have hpos : ∀ t ∈ Icc 0 T, 0 < E t + δ := fun t ht => by linarith [hE0 t ht]
  have hφd : ∀ t ∈ Ioo 0 T, HasDerivAt φ (E' t / (2 * Real.sqrt (E t + δ))) t := fun t ht =>
    ((hEd t ht).add_const δ).sqrt (hpos t (Ioo_subset_Icc_self ht)).ne'
  have hψd : ∀ t ∈ Ioo 0 T, HasDerivAt ψ (E' t / (2 * Real.sqrt (E t + δ)) * Real.exp (-K t) +
      φ t * (Real.exp (-K t) * (-(k t / 2))) - w t) t := fun t ht =>
    ((hφd t ht).mul ((hKd t).neg.exp)).sub (hWd t)
  have hψc : ContinuousOn ψ (Icc 0 T) := by
    have h1 : ContinuousOn φ (Icc 0 T) := (hEc.add continuousOn_const).sqrt
    have h2 : Continuous K := continuous_iff_continuousAt.2 fun t => (hKd t).continuousAt
    have h3 : Continuous Wi := continuous_iff_continuousAt.2 fun t => (hWd t).continuousAt
    exact (h1.mul (h2.neg.rexp.continuousOn)).sub h3.continuousOn
  have hderiv_nonpos : ∀ t ∈ Ioo 0 T, E' t / (2 * Real.sqrt (E t + δ)) * Real.exp (-K t) +
      φ t * (Real.exp (-K t) * (-(k t / 2))) - w t ≤ 0 := by
    intro t ht
    have htc := Ioo_subset_Icc_self ht
    have hE := hE0 t htc
    have hs : 0 < Real.sqrt (E t + δ) := Real.sqrt_pos.2 (hpos t htc)
    have hsq : Real.sqrt (E t + δ) ^ 2 = E t + δ := Real.sq_sqrt (hpos t htc).le
    have hsE : Real.sqrt (E t) ≤ Real.sqrt (E t + δ) := Real.sqrt_le_sqrt (by linarith)
    have hK0 : 0 ≤ K t := by
      have : 0 ≤ ∫ s in (0)..t, k s := intervalIntegral.integral_nonneg ht.1.le fun s _ => hk0 s
      simp only [hK]; linarith
    have hexp : Real.exp (-K t) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have hexp0 : 0 < Real.exp (-K t) := Real.exp_pos _
    -- `E'/(2φ) ≤ (k/2) φ + w`
    have h1 : E' t / (2 * Real.sqrt (E t + δ)) ≤ k t / 2 * Real.sqrt (E t + δ) + w t := by
      rw [div_le_iff₀ (by positivity)]
      have := hineq t ht
      have hkE : k t * E t ≤ k t * (E t + δ) := mul_le_mul_of_nonneg_left (by linarith) (hk0 t)
      have hwE : 2 * w t * Real.sqrt (E t) ≤ 2 * w t * Real.sqrt (E t + δ) :=
        mul_le_mul_of_nonneg_left hsE (by linarith [hw0 t])
      nlinarith
    have h2 : E' t / (2 * Real.sqrt (E t + δ)) * Real.exp (-K t) ≤
        (k t / 2 * Real.sqrt (E t + δ) + w t) * Real.exp (-K t) :=
      mul_le_mul_of_nonneg_right h1 hexp0.le
    have h3 : w t * Real.exp (-K t) ≤ w t := by
      have := mul_le_mul_of_nonneg_left hexp (hw0 t); linarith
    simp only [hφ]
    nlinarith
  have hanti : AntitoneOn ψ (Icc 0 T) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 T) hψc ?_ ?_
    · rw [interior_Icc]
      exact fun s hs => (hψd s hs).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro s hs
      rw [(hψd s hs).deriv]
      exact hderiv_nonpos s hs
  intro t ht
  have h0mem : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, ht.1.trans ht.2⟩
  have hle := hanti h0mem ht ht.1
  have hK0 : K 0 = 0 := by simp [hK]
  have hW0 : Wi 0 = 0 := by simp [hWi]
  simp only [hψ, hK0, hW0, neg_zero, Real.exp_zero, mul_one, sub_zero] at hle
  have hexpK : Real.exp (-K t) * Real.exp (K t) = 1 := by rw [← Real.exp_add]; simp
  have : φ t ≤ (φ 0 + Wi t) * Real.exp (K t) := by
    have h := mul_le_mul_of_nonneg_right (by linarith : φ t * Real.exp (-K t) ≤ φ 0 + Wi t)
      (Real.exp_pos (K t)).le
    calc φ t = φ t * Real.exp (-K t) * Real.exp (K t) := by rw [mul_assoc, hexpK, mul_one]
      _ ≤ (φ 0 + Wi t) * Real.exp (K t) := h
  simpa only [hφ, hWi, hK] using this

/-- **Square-root Gronwall with an `L¹` source** (`eq:hyperbolic-energy`, `eq:constraint-bound`):
if `E ≥ 0` is continuous on `[0, T]`, differentiable on `(0, T)`, and
`E' ≤ k E + 2 w √E` there with continuous `k, w ≥ 0`, then for `t ∈ [0, T]`
`√E(t) ≤ (√E(0) + ∫₀ᵗ w) exp(½∫₀ᵗ k)`. -/
theorem sqrt_energy_gronwall {E E' k w : ℝ → ℝ} {T : ℝ}
    (hEc : ContinuousOn E (Icc 0 T)) (hE0 : ∀ t ∈ Icc 0 T, 0 ≤ E t)
    (hEd : ∀ t ∈ Ioo 0 T, HasDerivAt E (E' t) t)
    (hk : Continuous k) (hw : Continuous w) (hk0 : ∀ t, 0 ≤ k t) (hw0 : ∀ t, 0 ≤ w t)
    (hineq : ∀ t ∈ Ioo 0 T, E' t ≤ k t * E t + 2 * w t * Real.sqrt (E t)) :
    ∀ t ∈ Icc 0 T, Real.sqrt (E t) ≤
      (Real.sqrt (E 0) + ∫ s in (0)..t, w s) * Real.exp ((∫ s in (0)..t, k s) / 2) := by
  intro t ht
  set B := Real.exp ((∫ s in (0)..t, k s) / 2)
  have hB : 0 < B := Real.exp_pos _
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  -- choose `δ` with `√δ B < ε`
  set δ := (ε / (2 * B)) ^ 2 with hδdef
  have hδ : 0 < δ := by positivity
  have h := sqrt_add_gronwall hδ hEc hE0 hEd hk hw hk0 hw0 hineq t ht
  have h0mem : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, ht.1.trans ht.2⟩
  have hs1 : Real.sqrt (E t) ≤ Real.sqrt (E t + δ) := Real.sqrt_le_sqrt (by linarith)
  have hs2 : Real.sqrt (E 0 + δ) ≤ Real.sqrt (E 0) + Real.sqrt δ := by
    rw [Real.sqrt_le_left (by positivity)]
    have := Real.sq_sqrt (hE0 0 h0mem)
    have := Real.sq_sqrt hδ.le
    nlinarith [Real.sqrt_nonneg (E 0), Real.sqrt_nonneg δ]
  have hsδ : Real.sqrt δ = ε / (2 * B) := by
    rw [hδdef, Real.sqrt_sq (by positivity)]
  have hWi : 0 ≤ ∫ s in (0)..t, w s := intervalIntegral.integral_nonneg ht.1 fun s _ => hw0 s
  calc Real.sqrt (E t) ≤ (Real.sqrt (E 0 + δ) + ∫ s in (0)..t, w s) * B := hs1.trans h
    _ ≤ (Real.sqrt (E 0) + Real.sqrt δ + ∫ s in (0)..t, w s) * B :=
        mul_le_mul_of_nonneg_right (by linarith) hB.le
    _ = (Real.sqrt (E 0) + ∫ s in (0)..t, w s) * B + ε / 2 := by
        rw [hsδ]; field_simp; ring
    _ < (Real.sqrt (E 0) + ∫ s in (0)..t, w s) * B + ε := by linarith

/-! ### The forced linear wave system -/

variable {ι : Type*} [Fintype ι]

/-- A classical solution of the linear wave system `D` (the normal form of
`TorusWaveEnergyUniqueness`) whose non-principal part splits as `L = L₀ + W`: a lower-order part
with `Σ_b L₀,b² ≤ m(t)² · size` for a continuous `m ≥ 0` (a time-integrable potential) and a
continuous forcing `W`.  The remaining hypotheses are those of `WaveData.Solves` without its
uniform lower-order bound. -/
structure ForcedSolves (D : WaveData ι) (L₀ W : ℝ → T3 → ι → ℝ) (m : ℝ → ℝ)
    (T a₀ lam M : ℝ) : Prop where
  cont_u : ∀ b, Continuous fun p : ℝ × T3 => D.u p.1 p.2 b
  cont_ut : ∀ b, Continuous fun p : ℝ × T3 => D.ut p.1 p.2 b
  cont_utt : ∀ b, Continuous fun p : ℝ × T3 => D.utt p.1 p.2 b
  cont_ux : ∀ i b, Continuous fun p : ℝ × T3 => D.ux p.1 i p.2 b
  cont_uxt : ∀ i b, Continuous fun p : ℝ × T3 => D.uxt p.1 i p.2 b
  cont_uxx : ∀ i j b, Continuous fun p : ℝ × T3 => D.uxx p.1 i j p.2 b
  cont_a : Continuous fun p : ℝ × T3 => D.a p.1 p.2
  cont_at : Continuous fun p : ℝ × T3 => D.at' p.1 p.2
  cont_β : ∀ i, Continuous fun p : ℝ × T3 => D.β p.1 i p.2
  cont_βdiv : ∀ i, Continuous fun p : ℝ × T3 => D.βdiv p.1 i p.2
  cont_γ : ∀ i j, Continuous fun p : ℝ × T3 => D.γ p.1 i j p.2
  cont_γt : ∀ i j, Continuous fun p : ℝ × T3 => D.γt p.1 i j p.2
  cont_γx : ∀ i j, Continuous fun p : ℝ × T3 => D.γx p.1 i j p.2
  cont_L0 : ∀ b, Continuous fun p : ℝ × T3 => L₀ p.1 p.2 b
  cont_W : ∀ b, Continuous fun p : ℝ × T3 => W p.1 p.2 b
  cont_m : Continuous m
  L_eq : ∀ t x b, D.L t x b = L₀ t x b + W t x b
  dt_u : ∀ t ∈ Ioo 0 T, ∀ x b, HasDerivAt (fun s => D.u s x b) (D.ut t x b) t
  dt_ut : ∀ t ∈ Ioo 0 T, ∀ x b, HasDerivAt (fun s => D.ut s x b) (D.utt t x b) t
  dt_ux : ∀ t ∈ Ioo 0 T, ∀ i x b, HasDerivAt (fun s => D.ux s i x b) (D.uxt t i x b) t
  dt_a : ∀ t ∈ Ioo 0 T, ∀ x, HasDerivAt (fun s => D.a s x) (D.at' t x) t
  dt_γ : ∀ t ∈ Ioo 0 T, ∀ i j x, HasDerivAt (fun s => D.γ s i j x) (D.γt t i j x) t
  dx_u : ∀ t ∈ Icc 0 T, ∀ i b, IsLineDeriv i (fun x => D.u t x b) (fun x => D.ux t i x b)
  dx_ut : ∀ t ∈ Ioo 0 T, ∀ i b, IsLineDeriv i (fun x => D.ut t x b) (fun x => D.uxt t i x b)
  dx_ux : ∀ t ∈ Ioo 0 T, ∀ i j b, IsLineDeriv i (fun x => D.ux t j x b) (fun x => D.uxx t i j x b)
  dx_β : ∀ t ∈ Ioo 0 T, ∀ i, IsLineDeriv i (D.β t i) (D.βdiv t i)
  dx_γ : ∀ t ∈ Ioo 0 T, ∀ i j, IsLineDeriv i (D.γ t i j) (D.γx t i j)
  γ_symm : ∀ t i j x, D.γ t i j x = D.γ t j i x
  eqn : ∀ t ∈ Ioo 0 T, ∀ x b, D.a t x * D.utt t x b =
    2 * ∑ i, D.β t i x * D.uxt t i x b + ∑ i, ∑ j, D.γ t i j x * D.uxx t i j x b + D.L t x b
  coer_a : ∀ t ∈ Icc 0 T, ∀ x, a₀ ≤ D.a t x
  coer_γ : ∀ t ∈ Icc 0 T, ∀ x (ξ : Fin 3 → ℝ),
    lam * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, D.γ t i j x * ξ i * ξ j
  bnd_at : ∀ t ∈ Icc 0 T, ∀ x, |D.at' t x| ≤ M
  bnd_βdiv : ∀ t ∈ Icc 0 T, ∀ i x, |D.βdiv t i x| ≤ M
  bnd_γt : ∀ t ∈ Icc 0 T, ∀ i j x, |D.γt t i j x| ≤ M
  bnd_γx : ∀ t ∈ Icc 0 T, ∀ i j x, |D.γx t i j x| ≤ M
  m_nonneg : ∀ t, 0 ≤ m t
  bnd_L0 : ∀ t ∈ Icc 0 T, ∀ x, ∑ b, L₀ t x b ^ 2 ≤ m t ^ 2 * D.size t x

namespace ForcedSolves

variable {D : WaveData ι} {L₀ W : ℝ → T3 → ι → ℝ} {m : ℝ → ℝ} {T a₀ lam M : ℝ}

theorem cont_L (h : ForcedSolves D L₀ W m T a₀ lam M) (b : ι) :
    Continuous fun p : ℝ × T3 => D.L p.1 p.2 b := by
  simp only [h.L_eq]
  exact (h.cont_L0 b).add (h.cont_W b)

theorem continuous_dens (h : ForcedSolves D L₀ W m T a₀ lam M) :
    Continuous fun p : ℝ × T3 => D.dens p.1 p.2 := by
  unfold WaveData.dens
  have := h.cont_u; have := h.cont_ut; have := h.cont_ux; have := h.cont_a; have := h.cont_γ
  fun_prop

theorem continuous_densT (h : ForcedSolves D L₀ W m T a₀ lam M) :
    Continuous fun p : ℝ × T3 => D.densT p.1 p.2 := by
  unfold WaveData.densT
  have := h.cont_u; have := h.cont_ut; have := h.cont_ux; have := h.cont_a; have := h.cont_γ
  have := h.cont_at; have := h.cont_γt; have := h.cont_utt; have := h.cont_uxt
  fun_prop

theorem hasDerivAt_dens (h : ForcedSolves D L₀ W m T a₀ lam M) {t : ℝ} (ht : t ∈ Ioo 0 T)
    (x : T3) : HasDerivAt (fun s => D.dens s x) (D.densT t x) t := by
  unfold WaveData.dens WaveData.densT
  refine HasDerivAt.fun_sum fun b _ => ?_
  have hu := h.dt_u t ht x b
  have hut := h.dt_ut t ht x b
  have ha := h.dt_a t ht x
  have h1 := ha.fun_mul (hut.fun_pow 2)
  have h3 := hu.fun_pow 2
  have h2 : HasDerivAt (fun s => ∑ i, ∑ j, D.γ s i j x * D.ux s i x b * D.ux s j x b)
      (∑ i, ∑ j, (D.γt t i j x * D.ux t i x b * D.ux t j x b +
        D.γ t i j x * D.uxt t i x b * D.ux t j x b +
        D.γ t i j x * D.ux t i x b * D.uxt t j x b)) t := by
    refine HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun j _ => ?_
    refine (((h.dt_γ t ht i j x).fun_mul (h.dt_ux t ht i x b)).fun_mul
      (h.dt_ux t ht j x b)).congr_deriv ?_
    ring
  refine ((h1.add h2).add h3).congr_deriv ?_
  simp only [Nat.cast_ofNat]
  ring

theorem densT_sub_densG (h : ForcedSolves D L₀ W m T a₀ lam M) {t : ℝ} (ht : t ∈ Ioo 0 T)
    (x : T3) :
    D.densT t x - D.densG t x = ∑ b, (∑ i, 2 * (D.βdiv t i x * D.ut t x b ^ 2 +
        D.β t i x * (2 * D.ut t x b * D.uxt t i x b)) +
      ∑ i, ∑ j, 2 * (D.γx t i j x * D.ut t x b * D.ux t j x b +
        D.γ t i j x * D.uxt t i x b * D.ux t j x b +
        D.γ t i j x * D.ut t x b * D.uxx t i j x b)) := by
  unfold WaveData.densT WaveData.densG
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  have he := h.eqn t ht x b
  have g10 := h.γ_symm t 1 0 x
  have g20 := h.γ_symm t 2 0 x
  have g21 := h.γ_symm t 2 1 x
  simp only [Fin.sum_univ_three] at he ⊢
  rw [g10, g20, g21] at *
  linear_combination (2 * D.ut t x b) * he

/-- **The energy identity** `∫ densT = ∫ densG` on `(0, T)` (integration by parts on `𝕋³`). -/
theorem integral_densT_eq (h : ForcedSolves D L₀ W m T a₀ lam M) {t : ℝ} (ht : t ∈ Ioo 0 T) :
    ∫ x, D.densT t x = ∫ x, D.densG t x := by
  have cs := fun {f : ℝ × T3 → ℝ} (hf : Continuous f) => WaveData.continuous_slice hf t
  have hP : ∀ b i, ∫ x, 2 * (D.βdiv t i x * D.ut t x b ^ 2 +
      D.β t i x * (2 * D.ut t x b * D.uxt t i x b)) = 0 := by
    intro b i
    refine integral_lineDeriv_eq_zero (i := i) (F := fun x => 2 * (D.β t i x * D.ut t x b ^ 2))
      ?_ ?_ ?_
    · have := cs (h.cont_β i); have := cs (h.cont_ut b); fun_prop
    · have := cs (h.cont_β i); have := cs (h.cont_ut b); have := cs (h.cont_βdiv i)
      have := cs (h.cont_uxt i b); fun_prop
    · have h1 := (h.dx_β t ht i).mul ((h.dx_ut t ht i b).mul (h.dx_ut t ht i b))
      have h2 := WaveData.isLineDeriv_const_mul 2 h1
      intro x
      have := h2 x
      simp only [] at this
      convert this using 1
      · funext s; ring
      · ring
  have hQ : ∀ b i j, ∫ x, 2 * (D.γx t i j x * D.ut t x b * D.ux t j x b +
      D.γ t i j x * D.uxt t i x b * D.ux t j x b +
      D.γ t i j x * D.ut t x b * D.uxx t i j x b) = 0 := by
    intro b i j
    refine integral_lineDeriv_eq_zero (i := i)
      (F := fun x => 2 * (D.γ t i j x * D.ut t x b * D.ux t j x b)) ?_ ?_ ?_
    · have := cs (h.cont_γ i j); have := cs (h.cont_ut b); have := cs (h.cont_ux j b); fun_prop
    · have := cs (h.cont_γ i j); have := cs (h.cont_ut b); have := cs (h.cont_ux j b)
      have := cs (h.cont_γx i j); have := cs (h.cont_uxt i b); have := cs (h.cont_uxx i j b)
      fun_prop
    · have h1 := ((h.dx_γ t ht i j).mul (h.dx_ut t ht i b)).mul (h.dx_ux t ht i j b)
      have h2 := WaveData.isLineDeriv_const_mul 2 h1
      intro x
      convert h2 x using 1
      ring
  have hint : ∀ {f : T3 → ℝ}, Continuous f → Integrable f := fun hf => integrable_of_continuous hf
  have hT : Integrable fun x => D.densT t x := hint (cs (continuous_densT h))
  have hG : Integrable fun x => D.densG t x := by
    unfold WaveData.densG
    have := fun b => cs (h.cont_u b); have := fun b => cs (h.cont_ut b)
    have := fun i b => cs (h.cont_ux i b); have := cs h.cont_at
    have := fun i => cs (h.cont_βdiv i); have := fun i j => cs (h.cont_γx i j)
    have := fun i j => cs (h.cont_γt i j); have := fun b => cs (h.cont_L b)
    exact hint (by fun_prop)
  have hPb : ∀ b, ∫ x, ∑ i, 2 * (D.βdiv t i x * D.ut t x b ^ 2 +
      D.β t i x * (2 * D.ut t x b * D.uxt t i x b)) = 0 := by
    intro b
    rw [integral_finsetSum _ fun i _ => ?_]
    · exact Finset.sum_eq_zero fun i _ => hP b i
    · have := cs (h.cont_β i); have := cs (h.cont_ut b); have := cs (h.cont_βdiv i)
      have := cs (h.cont_uxt i b)
      exact hint (by fun_prop)
  have hQb : ∀ b, ∫ x, ∑ i, ∑ j, 2 * (D.γx t i j x * D.ut t x b * D.ux t j x b +
      D.γ t i j x * D.uxt t i x b * D.ux t j x b +
      D.γ t i j x * D.ut t x b * D.uxx t i j x b) = 0 := by
    intro b
    rw [integral_finsetSum _ fun i _ => ?_]
    · refine Finset.sum_eq_zero fun i _ => ?_
      rw [integral_finsetSum _ fun j _ => ?_]
      · exact Finset.sum_eq_zero fun j _ => hQ b i j
      · have := cs (h.cont_γ i j); have := cs (h.cont_ut b); have := cs (h.cont_ux j b)
        have := cs (h.cont_γx i j); have := cs (h.cont_uxt i b); have := cs (h.cont_uxx i j b)
        exact hint (by fun_prop)
    · have := fun j => cs (h.cont_γ i j); have := cs (h.cont_ut b)
      have := fun j => cs (h.cont_ux j b)
      have := fun j => cs (h.cont_γx i j); have := cs (h.cont_uxt i b)
      have := fun j => cs (h.cont_uxx i j b)
      exact hint (by fun_prop)
  rw [← sub_eq_zero, ← integral_sub hT hG]
  simp only [densT_sub_densG h ht]
  rw [integral_finsetSum _ fun b _ => ?_]
  · refine Finset.sum_eq_zero fun b _ => ?_
    rw [MeasureTheory.integral_add, hPb, hQb, add_zero]
    · have := fun i => cs (h.cont_β i); have := cs (h.cont_ut b)
      have := fun i => cs (h.cont_βdiv i)
      have := fun i => cs (h.cont_uxt i b)
      exact hint (by fun_prop)
    · have := fun i j => cs (h.cont_γ i j); have := cs (h.cont_ut b)
      have := fun j => cs (h.cont_ux j b)
      have := fun i j => cs (h.cont_γx i j); have := fun i => cs (h.cont_uxt i b)
      have := fun i j => cs (h.cont_uxx i j b)
      exact hint (by fun_prop)
  · have := fun i => cs (h.cont_β i); have := cs (h.cont_ut b)
    have := fun i => cs (h.cont_βdiv i)
    have := fun i => cs (h.cont_uxt i b)
    have := fun i j => cs (h.cont_γ i j)
    have := fun j => cs (h.cont_ux j b)
    have := fun i j => cs (h.cont_γx i j)
    have := fun i j => cs (h.cont_uxx i j b)
    exact hint (by fun_prop)

theorem continuous_energy (h : ForcedSolves D L₀ W m T a₀ lam M) : Continuous D.energy := by
  have := continuous_parametric_integral_of_continuous (μ := (volume : Measure T3))
    (f := fun t x => D.dens t x) (continuous_dens h) (s := Set.univ) isCompact_univ
  unfold WaveData.energy
  simpa only [Measure.restrict_univ] using this

theorem hasDerivAt_energy (h : ForcedSolves D L₀ W m T a₀ lam M) {t : ℝ} (ht : t ∈ Ioo 0 T) :
    HasDerivAt D.energy (∫ x, D.densT t x) t := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).prod (isCompact_univ (X := T3))
    |>.exists_bound_of_continuousOn (continuous_densT h).continuousOn
  have cs := fun {f : ℝ × T3 → ℝ} (hf : Continuous f) (s : ℝ) => WaveData.continuous_slice hf s
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (volume : Measure T3))
    (F := fun s x => D.dens s x) (F' := fun s x => D.densT s x) (x₀ := t) (s := Ioo 0 T)
    (bound := fun _ => C) (isOpen_Ioo.mem_nhds ht)
    (Eventually.of_forall fun s => (cs (continuous_dens h) s).aestronglyMeasurable)
    (integrable_of_continuous (cs (continuous_dens h) t))
    (cs (continuous_densT h) t).aestronglyMeasurable
    (Eventually.of_forall fun x s hs => hC (s, x) ⟨Ioo_subset_Icc_self hs, Set.mem_univ _⟩)
    (integrable_const C)
    (Eventually.of_forall fun x s hs => hasDerivAt_dens h hs x)
  exact key.2

end ForcedSolves

/-! ### Elementary inequalities -/

/-- `X ≤ √P √Q` when `X ≤ (εP + Q/ε)/2` for every `ε > 0`. -/
theorem le_sqrt_mul_sqrt_of_forall {X P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (h : ∀ ε > 0, X ≤ (ε * P + Q / ε) / 2) : X ≤ Real.sqrt P * Real.sqrt Q := by
  set p := Real.sqrt P
  set q := Real.sqrt Q
  have hp : 0 ≤ p := Real.sqrt_nonneg _
  have hq : 0 ≤ q := Real.sqrt_nonneg _
  have hpP : p ^ 2 = P := Real.sq_sqrt hP
  have hqQ : q ^ 2 = Q := Real.sq_sqrt hQ
  refine le_of_forall_pos_lt_add fun η hη => ?_
  set δ := η / (p + q + 1) with hδ
  have hδ0 : 0 < δ := by positivity
  have hε : 0 < (q + δ) / (p + δ) := by positivity
  have h1 := h _ hε
  have e1 : (q + δ) / (p + δ) * P ≤ (q + δ) * p := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity), ← hpP]
    have : 0 ≤ (q + δ) * p * δ := by positivity
    nlinarith
  have e2 : Q / ((q + δ) / (p + δ)) ≤ q * (p + δ) := by
    rw [div_div_eq_mul_div, div_le_iff₀ (by positivity), ← hqQ]
    have : 0 ≤ q * (p + δ) * δ := by positivity
    nlinarith
  have e3 : δ * (p + q) < η := by
    rw [hδ, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  nlinarith

/-- **Cauchy–Schwarz in `L²(𝕋³; ℝ^ι)`**: `∫ Σ_b f_b g_b ≤ ‖f‖_{L²} ‖g‖_{L²}` for continuous `f, g`. -/
theorem integral_sum_mul_le {f g : T3 → ι → ℝ} (hf : ∀ b, Continuous fun x => f x b)
    (hg : ∀ b, Continuous fun x => g x b) :
    ∫ x, ∑ b, f x b * g x b ≤
      Real.sqrt (∫ x, ∑ b, f x b ^ 2) * Real.sqrt (∫ x, ∑ b, g x b ^ 2) := by
  have hint : ∀ {F : T3 → ℝ}, Continuous F → Integrable F := fun hF => integrable_of_continuous hF
  refine le_sqrt_mul_sqrt_of_forall (integral_nonneg fun x => Finset.sum_nonneg fun b _ =>
    sq_nonneg _) (integral_nonneg fun x => Finset.sum_nonneg fun b _ => sq_nonneg _)
    fun ε hε => ?_
  have hpt : ∀ x, ∑ b, f x b * g x b ≤ (ε * ∑ b, f x b ^ 2 + (∑ b, g x b ^ 2) / ε) / 2 := by
    intro x
    rw [Finset.mul_sum, Finset.sum_div, ← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_le_sum fun b _ => ?_
    have : 0 ≤ (ε * f x b - g x b) ^ 2 / ε := by positivity
    have e : (ε * f x b - g x b) ^ 2 / ε = ε * f x b ^ 2 + g x b ^ 2 / ε - 2 * (f x b * g x b) := by
      field_simp; ring
    linarith
  calc ∫ x, ∑ b, f x b * g x b ≤ ∫ x, (ε * ∑ b, f x b ^ 2 + (∑ b, g x b ^ 2) / ε) / 2 :=
        integral_mono (hint (by fun_prop)) (hint (by fun_prop)) hpt
    _ = (ε * (∫ x, ∑ b, f x b ^ 2) + (∫ x, ∑ b, g x b ^ 2) / ε) / 2 := by
        rw [integral_div, integral_add (hint (by fun_prop)) (hint (by fun_prop)),
          integral_const_mul, integral_div]

namespace ForcedSolves

variable {D : WaveData ι} {L₀ W : ℝ → T3 → ι → ℝ} {m : ℝ → ℝ} {T a₀ lam M : ℝ}

/-- The `L²(𝕋³)` norm of the forcing at time `t`. -/
def wnorm (W : ℝ → T3 → ι → ℝ) (t : ℝ) : ℝ := Real.sqrt (∫ x, ∑ b, W t x b ^ 2)

theorem continuous_wnorm (h : ForcedSolves D L₀ W m T a₀ lam M) : Continuous (wnorm W) := by
  have hc : Continuous fun p : ℝ × T3 => ∑ b, W p.1 p.2 b ^ 2 := by
    have := h.cont_W; fun_prop
  have := continuous_parametric_integral_of_continuous (μ := (volume : Measure T3))
    (f := fun t x => ∑ b, W t x b ^ 2) hc (s := Set.univ) isCompact_univ
  simp only [Measure.restrict_univ] at this
  exact this.sqrt

theorem wnorm_nonneg (W : ℝ → T3 → ι → ℝ) (t : ℝ) : 0 ≤ wnorm W t := Real.sqrt_nonneg _

theorem size_nonneg (D : WaveData ι) (t : ℝ) (x : T3) : 0 ≤ D.size t x :=
  Finset.sum_nonneg fun b _ => by positivity

theorem size_le_dens (h : ForcedSolves D L₀ W m T a₀ lam M) {c : ℝ} (hc : c ≤ a₀)
    (hc' : c ≤ lam) (hc1 : c ≤ 1) {t : ℝ} (ht : t ∈ Icc 0 T) (x : T3) :
    c * D.size t x ≤ D.dens t x := by
  unfold WaveData.size WaveData.dens
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun b _ => ?_
  have hco := h.coer_γ t ht x (fun i => D.ux t i x b)
  have ha := h.coer_a t ht x
  have h1 : c * D.ut t x b ^ 2 ≤ D.a t x * D.ut t x b ^ 2 :=
    mul_le_mul_of_nonneg_right (hc.trans ha) (sq_nonneg _)
  have h2 : c * ∑ i, D.ux t i x b ^ 2 ≤ lam * ∑ i, D.ux t i x b ^ 2 :=
    mul_le_mul_of_nonneg_right hc' (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have h3 : c * D.u t x b ^ 2 ≤ D.u t x b ^ 2 := by
    have := sq_nonneg (D.u t x b); nlinarith
  have hc'' : ∑ i, ∑ j, D.γ t i j x * D.ux t i x b * D.ux t j x b =
      ∑ i, ∑ j, D.γ t i j x * (fun i => D.ux t i x b) i * (fun i => D.ux t i x b) j := rfl
  rw [hc'']
  nlinarith

/-- The coercivity constant `c = min(a₀, λ, 1)`. -/
def cmin (a₀ lam : ℝ) : ℝ := min a₀ (min lam 1)

theorem cmin_pos {a₀ lam : ℝ} (ha₀ : 0 < a₀) (hlam : 0 < lam) : 0 < cmin a₀ lam :=
  lt_min ha₀ (lt_min hlam one_pos)

theorem size_le_dens' (h : ForcedSolves D L₀ W m T a₀ lam M) {t : ℝ} (ht : t ∈ Icc 0 T)
    (x : T3) : cmin a₀ lam * D.size t x ≤ D.dens t x :=
  size_le_dens h (min_le_left _ _) ((min_le_right _ _).trans (min_le_left _ _))
    ((min_le_right _ _).trans (min_le_right _ _)) ht x

theorem dens_nonneg (h : ForcedSolves D L₀ W m T a₀ lam M) (ha₀ : 0 < a₀) (hlam : 0 < lam)
    {t : ℝ} (ht : t ∈ Icc 0 T) (x : T3) : 0 ≤ D.dens t x :=
  le_trans (mul_nonneg (cmin_pos ha₀ hlam).le (size_nonneg D t x)) (size_le_dens' h ht x)

theorem energy_nonneg (h : ForcedSolves D L₀ W m T a₀ lam M) (ha₀ : 0 < a₀) (hlam : 0 < lam)
    {t : ℝ} (ht : t ∈ Icc 0 T) : 0 ≤ D.energy t :=
  integral_nonneg fun x => dens_nonneg h ha₀ hlam ht x

/-- `c ∫ size ≤ E`. -/
theorem integral_size_le (h : ForcedSolves D L₀ W m T a₀ lam M) {t : ℝ} (ht : t ∈ Icc 0 T) :
    cmin a₀ lam * ∫ x, D.size t x ≤ D.energy t := by
  rw [← integral_const_mul]
  refine integral_mono ?_ ?_ fun x => size_le_dens' h ht x
  · refine (integrable_of_continuous ?_).const_mul _
    unfold WaveData.size
    have := fun b => WaveData.continuous_slice (h.cont_u b) t
    have := fun b => WaveData.continuous_slice (h.cont_ut b) t
    have := fun i b => WaveData.continuous_slice (h.cont_ux i b) t
    fun_prop
  · exact integrable_of_continuous (WaveData.continuous_slice (continuous_dens h) t)

/-- The non-forcing part of the energy density derivative. -/
def densG0 (D : WaveData ι) (L₀ : ℝ → T3 → ι → ℝ) (t : ℝ) (x : T3) : ℝ :=
  ∑ b, (D.at' t x * D.ut t x b ^ 2 - 2 * ∑ i, D.βdiv t i x * D.ut t x b ^ 2 -
    2 * ∑ i, ∑ j, D.γx t i j x * D.ut t x b * D.ux t j x b +
    ∑ i, ∑ j, D.γt t i j x * D.ux t i x b * D.ux t j x b +
    2 * D.u t x b * D.ut t x b + 2 * D.ut t x b * L₀ t x b)

theorem densG_eq (h : ForcedSolves D L₀ W m T a₀ lam M) (t : ℝ) (x : T3) :
    D.densG t x = densG0 D L₀ t x + 2 * ∑ b, D.ut t x b * W t x b := by
  unfold WaveData.densG densG0
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [h.L_eq]
  ring

theorem densG0_le (h : ForcedSolves D L₀ W m T a₀ lam M) {t : ℝ} (ht : t ∈ Icc 0 T) (x : T3) :
    densG0 D L₀ t x ≤ (16 * M + 2 + 2 * m t) * D.size t x := by
  have hb : ∀ b, (D.at' t x * D.ut t x b ^ 2 - 2 * ∑ i, D.βdiv t i x * D.ut t x b ^ 2 -
      2 * ∑ i, ∑ j, D.γx t i j x * D.ut t x b * D.ux t j x b +
      ∑ i, ∑ j, D.γt t i j x * D.ux t i x b * D.ux t j x b +
      2 * D.u t x b * D.ut t x b + 2 * D.ut t x b * 0) ≤
      (16 * M + 2) * (D.ut t x b ^ 2 + ∑ i, D.ux t i x b ^ 2 + D.u t x b ^ 2) + 0 ^ 2 :=
    fun b => WaveData.densG_term_le M _ _ _ _ _ _ _ _ (h.bnd_at t ht x)
      (fun i => h.bnd_βdiv t ht i x) (fun i j => h.bnd_γx t ht i j x)
      (fun i j => h.bnd_γt t ht i j x)
  -- the lower-order part by Cauchy–Schwarz
  have hCS : ∑ b, D.ut t x b * L₀ t x b ≤ m t * D.size t x := by
    have h1 := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun b => D.ut t x b)
      (fun b => L₀ t x b)
    have h2 : Real.sqrt (∑ b, D.ut t x b ^ 2) ≤ Real.sqrt (D.size t x) := by
      refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun b _ => ?_)
      have : 0 ≤ ∑ i, D.ux t i x b ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
      nlinarith [sq_nonneg (D.u t x b)]
    have h3 : Real.sqrt (∑ b, L₀ t x b ^ 2) ≤ m t * Real.sqrt (D.size t x) := by
      rw [← Real.sqrt_sq (h.m_nonneg t), ← Real.sqrt_mul (sq_nonneg _)]
      exact Real.sqrt_le_sqrt (h.bnd_L0 t ht x)
    have hs := Real.mul_self_sqrt (size_nonneg D t x)
    calc ∑ b, D.ut t x b * L₀ t x b ≤ Real.sqrt (∑ b, D.ut t x b ^ 2) *
          Real.sqrt (∑ b, L₀ t x b ^ 2) := h1
      _ ≤ Real.sqrt (D.size t x) * (m t * Real.sqrt (D.size t x)) :=
          mul_le_mul h2 h3 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = m t * D.size t x := by rw [mul_left_comm, hs]
  have hsplit : densG0 D L₀ t x = ∑ b, (D.at' t x * D.ut t x b ^ 2 -
      2 * ∑ i, D.βdiv t i x * D.ut t x b ^ 2 -
      2 * ∑ i, ∑ j, D.γx t i j x * D.ut t x b * D.ux t j x b +
      ∑ i, ∑ j, D.γt t i j x * D.ux t i x b * D.ux t j x b +
      2 * D.u t x b * D.ut t x b + 2 * D.ut t x b * 0) +
      2 * ∑ b, D.ut t x b * L₀ t x b := by
    unfold densG0
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [hsplit]
  have hs1 : ∑ b, (D.at' t x * D.ut t x b ^ 2 - 2 * ∑ i, D.βdiv t i x * D.ut t x b ^ 2 -
      2 * ∑ i, ∑ j, D.γx t i j x * D.ut t x b * D.ux t j x b +
      ∑ i, ∑ j, D.γt t i j x * D.ux t i x b * D.ux t j x b +
      2 * D.u t x b * D.ut t x b + 2 * D.ut t x b * 0) ≤ (16 * M + 2) * D.size t x := by
    calc _ ≤ ∑ b, ((16 * M + 2) * (D.ut t x b ^ 2 + ∑ i, D.ux t i x b ^ 2 + D.u t x b ^ 2) +
          0 ^ 2) := Finset.sum_le_sum fun b _ => hb b
      _ = (16 * M + 2) * D.size t x := by
          simp only [WaveData.size, Finset.mul_sum]; simp
  nlinarith

/-- The energy growth rate `k(t) = (16M + 2 + 2m(t))/c`. -/
def kcoef (M : ℝ) (m : ℝ → ℝ) (c : ℝ) (t : ℝ) : ℝ := (16 * M + 2 + 2 * m t) / c

/-- **The forced energy inequality**: on `(0, T)`,
`E' ≤ k(t) E + 2 (c^{-1/2} ‖W(t)‖_{L²}) √E`, `k(t) = (16M + 2 + 2m(t))/c`, `c = min(a₀, λ, 1)`. -/
theorem energy_deriv_le (h : ForcedSolves D L₀ W m T a₀ lam M) (ha₀ : 0 < a₀) (hlam : 0 < lam)
    {t : ℝ} (ht : t ∈ Ioo 0 T) :
    ∫ x, D.densT t x ≤ kcoef M m (cmin a₀ lam) t * D.energy t +
      2 * ((Real.sqrt (cmin a₀ lam))⁻¹ * wnorm W t) * Real.sqrt (D.energy t) := by
  set c := cmin a₀ lam with hcdef
  have hc0 : 0 < c := cmin_pos ha₀ hlam
  have htc : t ∈ Icc 0 T := Ioo_subset_Icc_self ht
  have hM : 0 ≤ M := (abs_nonneg _).trans (h.bnd_at t htc (0 : T3))
  have cs := fun {f : ℝ × T3 → ℝ} (hf : Continuous f) => WaveData.continuous_slice hf t
  have hint : ∀ {f : T3 → ℝ}, Continuous f → Integrable f := fun hf => integrable_of_continuous hf
  have hG0c : Continuous fun x => densG0 D L₀ t x := by
    unfold densG0
    have := fun b => cs (h.cont_u b); have := fun b => cs (h.cont_ut b)
    have := fun i b => cs (h.cont_ux i b); have := cs h.cont_at
    have := fun i => cs (h.cont_βdiv i); have := fun i j => cs (h.cont_γx i j)
    have := fun i j => cs (h.cont_γt i j); have := fun b => cs (h.cont_L0 b)
    fun_prop
  have hWc : Continuous fun x => ∑ b, D.ut t x b * W t x b := by
    have := fun b => cs (h.cont_ut b); have := fun b => cs (h.cont_W b); fun_prop
  have hsc : Continuous fun x => D.size t x := by
    unfold WaveData.size
    have := fun b => cs (h.cont_u b); have := fun b => cs (h.cont_ut b)
    have := fun i b => cs (h.cont_ux i b)
    fun_prop
  rw [integral_densT_eq h ht]
  simp only [densG_eq h]
  rw [integral_add (hint hG0c) ((hint hWc).const_mul 2), integral_const_mul]
  -- the non-forcing part
  have hA : ∫ x, densG0 D L₀ t x ≤ kcoef M m c t * D.energy t := by
    have hk0 : 0 ≤ (16 * M + 2 + 2 * m t) := by nlinarith [h.m_nonneg t]
    calc ∫ x, densG0 D L₀ t x ≤ ∫ x, (16 * M + 2 + 2 * m t) * D.size t x :=
          integral_mono (hint hG0c) ((hint hsc).const_mul _) fun x => densG0_le h htc x
      _ = (16 * M + 2 + 2 * m t) / c * (c * ∫ x, D.size t x) := by
          rw [integral_const_mul]; field_simp
      _ ≤ kcoef M m c t * D.energy t :=
          mul_le_mul_of_nonneg_left (integral_size_le h htc) (div_nonneg hk0 hc0.le)
  -- the forcing part
  have hB : ∫ x, ∑ b, D.ut t x b * W t x b ≤
      (Real.sqrt c)⁻¹ * wnorm W t * Real.sqrt (D.energy t) := by
    have h1 := integral_sum_mul_le (f := fun x b => D.ut t x b) (g := fun x b => W t x b)
      (fun b => cs (h.cont_ut b)) (fun b => cs (h.cont_W b))
    have h2 : ∫ x, ∑ b, D.ut t x b ^ 2 ≤ D.energy t / c := by
      rw [le_div_iff₀ hc0]
      refine le_trans ?_ (integral_size_le h htc)
      rw [mul_comm]
      refine mul_le_mul_of_nonneg_left (integral_mono (hint (by
        have := fun b => cs (h.cont_ut b); fun_prop)) (hint hsc) fun x => ?_) hc0.le
      refine Finset.sum_le_sum fun b _ => ?_
      have : 0 ≤ ∑ i, D.ux t i x b ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
      nlinarith [sq_nonneg (D.u t x b)]
    have h3 : Real.sqrt (∫ x, ∑ b, D.ut t x b ^ 2) ≤ (Real.sqrt c)⁻¹ * Real.sqrt (D.energy t) := by
      calc Real.sqrt (∫ x, ∑ b, D.ut t x b ^ 2) ≤ Real.sqrt (D.energy t / c) :=
            Real.sqrt_le_sqrt h2
        _ = (Real.sqrt c)⁻¹ * Real.sqrt (D.energy t) := by
            rw [Real.sqrt_div' _ hc0.le, div_eq_inv_mul]
    calc ∫ x, ∑ b, D.ut t x b * W t x b ≤ Real.sqrt (∫ x, ∑ b, D.ut t x b ^ 2) * wnorm W t := h1
      _ ≤ (Real.sqrt c)⁻¹ * Real.sqrt (D.energy t) * wnorm W t :=
          mul_le_mul_of_nonneg_right h3 (wnorm_nonneg W t)
      _ = (Real.sqrt c)⁻¹ * wnorm W t * Real.sqrt (D.energy t) := by ring
  nlinarith

theorem continuous_kcoef (h : ForcedSolves D L₀ W m T a₀ lam M) (c : ℝ) :
    Continuous (kcoef M m c) := by
  unfold kcoef; have := h.cont_m; fun_prop

/-- **The square-root energy bound with an `L¹_t L²_x` source and an integrable potential**:
for `t ∈ [0, T]`,
`√E(t) ≤ (√E(0) + c^{-1/2} ∫₀ᵗ ‖W‖_{L²}) exp(½ ∫₀ᵗ (16M + 2 + 2m)/c)`. -/
theorem sqrt_energy_le (h : ForcedSolves D L₀ W m T a₀ lam M) (ha₀ : 0 < a₀) (hlam : 0 < lam) :
    ∀ t ∈ Icc 0 T, Real.sqrt (D.energy t) ≤
      (Real.sqrt (D.energy 0) + ∫ s in (0)..t, (Real.sqrt (cmin a₀ lam))⁻¹ * wnorm W s) *
        Real.exp ((∫ s in (0)..t, kcoef M m (cmin a₀ lam) s) / 2) := by
  intro t ht
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hM : 0 ≤ M := (abs_nonneg _).trans (h.bnd_at 0 ⟨le_rfl, hT⟩ (0 : T3))
  have hc0 := cmin_pos ha₀ hlam
  refine sqrt_energy_gronwall (E' := fun s => ∫ x, D.densT s x)
    (h.continuous_energy.continuousOn) (fun s hs => energy_nonneg h ha₀ hlam hs)
    (fun s hs => hasDerivAt_energy h hs) (continuous_kcoef h _)
    (continuous_const.mul (continuous_wnorm h)) (fun s => ?_) (fun s => ?_)
    (fun s hs => energy_deriv_le h ha₀ hlam hs) t ht
  · unfold kcoef
    have := h.m_nonneg s
    positivity
  · exact mul_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _)) (wnorm_nonneg W s)

theorem gamma_quad_le (γ : Fin 3 → Fin 3 → ℝ) (ξ : Fin 3 → ℝ) {A : ℝ}
    (h : ∀ i j, |γ i j| ≤ A) : ∑ i, ∑ j, γ i j * ξ i * ξ j ≤ 3 * A * ∑ i, ξ i ^ 2 := by
  have hb : ∀ i j, γ i j * ξ i * ξ j ≤ A * (ξ i ^ 2 + ξ j ^ 2) / 2 := fun i j =>
    WaveData.abs_mul_le_half _ _ _ _ (h i j)
  have h00 := hb 0 0; have h01 := hb 0 1; have h02 := hb 0 2
  have h10 := hb 1 0; have h11 := hb 1 1; have h12 := hb 1 2
  have h20 := hb 2 0; have h21 := hb 2 1; have h22 := hb 2 2
  simp only [Fin.sum_univ_three]
  linarith

/-- The initial energy is bounded by the initial size when `a ≤ A₁` and `|γ^{ij}| ≤ A₁`. -/
theorem energy_le_size (D : WaveData ι) {t A₁ : ℝ} (ha : ∀ x, D.a t x ≤ A₁)
    (hγ : ∀ i j x, |D.γ t i j x| ≤ A₁) (hcu : ∀ b, Continuous fun x => D.u t x b)
    (hcut : ∀ b, Continuous fun x => D.ut t x b) (hcux : ∀ i b, Continuous fun x => D.ux t i x b)
    (hca : Continuous fun x => D.a t x) (hcγ : ∀ i j, Continuous fun x => D.γ t i j x) :
    D.energy t ≤ (3 * A₁ + 1) * ∫ x, D.size t x := by
  have hA : 0 ≤ A₁ := (abs_nonneg _).trans (hγ 0 0 0)
  rw [← integral_const_mul]
  refine integral_mono ?_ ?_ fun x => ?_
  · unfold WaveData.dens
    exact integrable_of_continuous (by fun_prop)
  · unfold WaveData.size
    exact (integrable_of_continuous (by fun_prop)).const_mul _
  · unfold WaveData.dens WaveData.size
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun b _ => ?_
    have h1 := gamma_quad_le (fun i j => D.γ t i j x) (fun i => D.ux t i x b) (fun i j => hγ i j x)
    have h2 : D.a t x * D.ut t x b ^ 2 ≤ A₁ * D.ut t x b ^ 2 :=
      mul_le_mul_of_nonneg_right (ha x) (sq_nonneg _)
    have h3 : 0 ≤ ∑ i, D.ux t i x b ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have := sq_nonneg (D.ut t x b); have := sq_nonneg (D.u t x b)
    nlinarith

/-- **The `L^∞_t L²_x` bound of `(u, ∂ₜu, ∇u)` by the initial data and the `L¹_t L²_x` norm of the
forcing** (`eq:constraint-bound` for an abstract wave system): if moreover `a(0) ≤ A₁` and
`|γ^{ij}(0)| ≤ A₁`, then for `t ∈ [0, T]`
`‖(u, ∂u)(t)‖_{L²} ≤ C_T (‖(u, ∂u)(0)‖_{L²} + ∫₀ᵀ ‖W‖_{L²})`, with
`C_T = c^{-1/2} max(√(3A₁+1), c^{-1/2}) exp(((16M + 2)T + 2∫₀ᵀ m)/(2c))` depending only on
`a₀, λ, M, A₁, T` and `∫₀ᵀ m` (the `L¹` norm of the potential). -/
theorem size_bound (h : ForcedSolves D L₀ W m T a₀ lam M) (ha₀ : 0 < a₀) (hlam : 0 < lam)
    {A₁ : ℝ} (hA₁a : ∀ x, D.a 0 x ≤ A₁) (hA₁γ : ∀ i j x, |D.γ 0 i j x| ≤ A₁) :
    ∀ t ∈ Icc 0 T, Real.sqrt (∫ x, D.size t x) ≤
      (Real.sqrt (cmin a₀ lam))⁻¹ * max (Real.sqrt (3 * A₁ + 1)) (Real.sqrt (cmin a₀ lam))⁻¹ *
        Real.exp (((16 * M + 2) * T + 2 * ∫ s in (0)..T, m s) / (2 * cmin a₀ lam)) *
        (Real.sqrt (∫ x, D.size 0 x) + ∫ s in (0)..T, wnorm W s) := by
  intro t ht
  have hT : 0 ≤ T := ht.1.trans ht.2
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT⟩
  have hM : 0 ≤ M := (abs_nonneg _).trans (h.bnd_at 0 h0 (0 : T3))
  set c := cmin a₀ lam with hcdef
  have hc0 : 0 < c := cmin_pos ha₀ hlam
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.2 hc0
  have hA : 0 ≤ A₁ := (abs_nonneg _).trans (hA₁γ 0 0 0)
  set S0 := ∫ x, D.size 0 x
  have hS0 : 0 ≤ S0 := integral_nonneg fun x => size_nonneg D 0 x
  set Wi := ∫ s in (0)..T, wnorm W s
  have hwc := continuous_wnorm h
  have hWi : ∫ s in (0)..t, wnorm W s ≤ Wi :=
    intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2 (Eventually.of_forall fun s =>
      wnorm_nonneg W s) (hwc.intervalIntegrable _ _)
  have hWi0 : 0 ≤ ∫ s in (0)..t, wnorm W s :=
    intervalIntegral.integral_nonneg ht.1 fun s _ => wnorm_nonneg W s
  -- the exponent
  have hkint : (∫ s in (0)..t, kcoef M m c s) ≤ ((16 * M + 2) * T + 2 * ∫ s in (0)..T, m s) / c := by
    have hmc := h.cont_m
    have e : ∀ τ, (∫ s in (0)..τ, kcoef M m c s) = ((16 * M + 2) * τ + 2 * ∫ s in (0)..τ, m s) / c := by
      intro τ
      unfold kcoef
      rw [intervalIntegral.integral_div, intervalIntegral.integral_add
        (f := fun _ : ℝ => 16 * M + 2) (g := fun s => 2 * m s)
        (continuous_const.intervalIntegrable _ _)
        ((continuous_const.mul hmc).intervalIntegrable _ _), intervalIntegral.integral_const,
        intervalIntegral.integral_const_mul]
      simp only [sub_zero, smul_eq_mul]
      ring
    rw [e t, div_le_div_iff_of_pos_right hc0]
    have hm : ∫ s in (0)..t, m s ≤ ∫ s in (0)..T, m s :=
      intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2 (Eventually.of_forall fun s =>
        h.m_nonneg s) (hmc.intervalIntegrable _ _)
    nlinarith [ht.2]
  have hexp : Real.exp ((∫ s in (0)..t, kcoef M m c s) / 2) ≤
      Real.exp (((16 * M + 2) * T + 2 * ∫ s in (0)..T, m s) / (2 * c)) := by
    refine Real.exp_le_exp.2 ?_
    rw [show ((16 * M + 2) * T + 2 * ∫ s in (0)..T, m s) / (2 * c) =
      (((16 * M + 2) * T + 2 * ∫ s in (0)..T, m s) / c) / 2 by field_simp]
    linarith
  -- the energy bound
  have hE := sqrt_energy_le h ha₀ hlam t ht
  rw [intervalIntegral.integral_const_mul] at hE
  have hE0 : Real.sqrt (D.energy 0) ≤ Real.sqrt (3 * A₁ + 1) * Real.sqrt S0 := by
    rw [← Real.sqrt_mul (by positivity)]
    refine Real.sqrt_le_sqrt (energy_le_size D hA₁a hA₁γ
      (fun b => WaveData.continuous_slice (h.cont_u b) 0)
      (fun b => WaveData.continuous_slice (h.cont_ut b) 0)
      (fun i b => WaveData.continuous_slice (h.cont_ux i b) 0)
      (WaveData.continuous_slice h.cont_a 0) (fun i j => WaveData.continuous_slice (h.cont_γ i j) 0))
  have hsize : Real.sqrt (∫ x, D.size t x) ≤ (Real.sqrt c)⁻¹ * Real.sqrt (D.energy t) := by
    have h1 := integral_size_le h ht
    rw [← div_eq_inv_mul, le_div_iff₀ hsc, ← Real.sqrt_mul' _ hc0.le]
    refine Real.sqrt_le_sqrt ?_
    linarith
  set mx := max (Real.sqrt (3 * A₁ + 1)) (Real.sqrt c)⁻¹
  have hmx1 : Real.sqrt (3 * A₁ + 1) ≤ mx := le_max_left _ _
  have hmx2 : (Real.sqrt c)⁻¹ ≤ mx := le_max_right _ _
  set X := Real.exp ((∫ s in (0)..t, kcoef M m c s) / 2)
  set Y := Real.exp (((16 * M + 2) * T + 2 * ∫ s in (0)..T, m s) / (2 * c))
  have hX : 0 < X := Real.exp_pos _
  have hinner : Real.sqrt (D.energy 0) + (Real.sqrt c)⁻¹ * ∫ s in (0)..t, wnorm W s ≤
      mx * (Real.sqrt S0 + Wi) := by
    have := Real.sqrt_nonneg S0
    have h1 : (Real.sqrt c)⁻¹ * ∫ s in (0)..t, wnorm W s ≤ mx * Wi :=
      mul_le_mul hmx2 hWi hWi0 ((inv_nonneg.2 hsc.le).trans hmx2)
    have h2 : Real.sqrt (3 * A₁ + 1) * Real.sqrt S0 ≤ mx * Real.sqrt S0 :=
      mul_le_mul_of_nonneg_right hmx1 this
    nlinarith
  have hinner0 : 0 ≤ mx * (Real.sqrt S0 + Wi) := by
    have := Real.sqrt_nonneg (D.energy 0)
    have : 0 ≤ (Real.sqrt c)⁻¹ * ∫ s in (0)..t, wnorm W s := mul_nonneg (inv_nonneg.2 hsc.le) hWi0
    linarith
  calc Real.sqrt (∫ x, D.size t x) ≤ (Real.sqrt c)⁻¹ * Real.sqrt (D.energy t) := hsize
    _ ≤ (Real.sqrt c)⁻¹ * ((Real.sqrt (D.energy 0) +
          (Real.sqrt c)⁻¹ * ∫ s in (0)..t, wnorm W s) * X) :=
        mul_le_mul_of_nonneg_left hE (inv_nonneg.2 hsc.le)
    _ ≤ (Real.sqrt c)⁻¹ * ((mx * (Real.sqrt S0 + Wi)) * Y) := by
        refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hsc.le)
        exact mul_le_mul hinner hexp hX.le hinner0
    _ = (Real.sqrt c)⁻¹ * mx * Y * (Real.sqrt S0 + Wi) := by ring

end ForcedSolves

/-! ### Non-vacuity: a forced scalar wave on `𝕋³` -/

/-- The scalar system `∂ₜ²u = Δu + W` with the explicit solution `u = t²/2`, `W = 1`, written in
the forced normal form (`L₀ = 0`, `m = 0`). -/
def quadSol : WaveData Unit where
  u := fun t _ _ => t ^ 2 / 2
  ut := fun t _ _ => t
  utt := fun _ _ _ => 1
  ux := fun _ _ _ _ => 0
  uxt := fun _ _ _ _ => 0
  uxx := fun _ _ _ _ _ => 0
  a := fun _ _ => 1
  at' := fun _ _ => 0
  β := fun _ _ _ => 0
  βdiv := fun _ _ _ => 0
  γ := fun _ i j _ => if i = j then 1 else 0
  γt := fun _ _ _ _ => 0
  γx := fun _ _ _ _ => 0
  L := fun _ _ _ => 1

theorem quadSol_forced (T : ℝ) :
    ForcedSolves quadSol (fun _ _ _ => 0) (fun _ _ _ => 1) (fun _ => 0) T 1 1 0 where
  cont_u := fun _ => by simp only [quadSol]; fun_prop
  cont_ut := fun _ => by simp only [quadSol]; fun_prop
  cont_utt := fun _ => continuous_const
  cont_ux := fun _ _ => continuous_const
  cont_uxt := fun _ _ => continuous_const
  cont_uxx := fun _ _ _ => continuous_const
  cont_a := continuous_const
  cont_at := continuous_const
  cont_β := fun _ => continuous_const
  cont_βdiv := fun _ => continuous_const
  cont_γ := fun _ _ => continuous_const
  cont_γt := fun _ _ => continuous_const
  cont_γx := fun _ _ => continuous_const
  cont_L0 := fun _ => continuous_const
  cont_W := fun _ => continuous_const
  cont_m := continuous_const
  L_eq := fun _ _ _ => by simp [quadSol]
  dt_u := fun t _ _ _ => by
    simp only [quadSol]
    have := (hasDerivAt_pow 2 t).div_const 2
    refine this.congr_deriv ?_
    norm_num
  dt_ut := fun t _ _ _ => by simp only [quadSol]; exact hasDerivAt_id t
  dt_ux := fun _ _ _ _ _ => hasDerivAt_const _ _
  dt_a := fun _ _ _ => hasDerivAt_const _ _
  dt_γ := fun _ _ i j _ => hasDerivAt_const _ _
  dx_u := fun _ _ i _ => WaveData.isLineDeriv_const i _
  dx_ut := fun _ _ i _ => WaveData.isLineDeriv_const i _
  dx_ux := fun _ _ i _ _ => WaveData.isLineDeriv_const i 0
  dx_β := fun _ _ i => WaveData.isLineDeriv_const i 0
  dx_γ := fun _ _ i j => WaveData.isLineDeriv_const i _
  γ_symm := fun _ i j _ => by simp only [quadSol, eq_comm]
  eqn := fun _ _ _ _ => by simp [quadSol]
  coer_a := fun _ _ _ => le_rfl
  coer_γ := fun _ _ _ ξ => by
    simp only [quadSol, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    simp [sq]
  bnd_at := fun _ _ _ => by simp [quadSol]
  bnd_βdiv := fun _ _ _ _ => by simp [quadSol]
  bnd_γt := fun _ _ _ _ _ => by simp [quadSol]
  bnd_γx := fun _ _ _ _ _ => by simp [quadSol]
  m_nonneg := fun _ => le_rfl
  bnd_L0 := fun _ _ _ => by simp [quadSol]

example (T : ℝ) := ForcedSolves.size_bound (quadSol_forced T) one_pos one_pos (A₁ := 1)
  (fun _ => le_rfl) (fun i j x => by simp only [quadSol]; split_ifs <;> simp)

end

end RenewalGeometry.TorusWaveEnergyForced
