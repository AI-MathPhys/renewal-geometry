/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.GeneratedHermiteRecord

/-!
# Slice energies of the Hermite record on a cell

Generic infrastructure (no renewal notions) for `thm:generated-dynamics` (Einstein–Standard-Model
action-closure manuscript, `eq:generated-Hermite`, classical-norm form): the Fourier-form Hermite
rates of `GenRatesId.generated_dynamics_rates_id` on a cell `[jτ, (j+1)τ]` inside the interval
where the limit solution coincides with a smooth solution `V` become classical slice-norm bounds
for the record field `W = recW` and its time derivatives:
`Σ_b Q_{s+2}(W_b - V_b) ≤ e₂`, `Σ_b Q_{s+2}(∂_tW_b - ∂_tV_b) ≤ e₂`,
`Σ_b Q_s(∂_t²W_b - ∂_t²V_b) ≤ e₁` (Parseval, `GenHermite.sum_Q_le_of_sum_le`).

* **`cell_energies`**.
-/

open MeasureTheory Filter Topology Set
open scoped BigOperators ContDiff Real

noncomputable section

namespace RenewalGeometry.GenHermite

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk SlabSobAlg QLEnergy KatoGalerkin SpectralGalerkin

set_option linter.unusedSectionVars false

variable {d n : ℕ}

theorem isSPeriodic_recW {q N : ℕ} (τ t₀ : ℝ) (U₀ U₁ V₀ V₁ : GS d n N) (b : Fin n) :
    IsSPeriodic (recW τ t₀ U₀ U₁ V₀ V₁ q b) := isSPeriodic_fldc q _ b

theorem isSPeriodic_recWD {q N : ℕ} (τ t₀ : ℝ) (U₀ U₁ V₀ V₁ : GS d n N) (b : Fin n) :
    IsSPeriodic (recWD τ t₀ U₀ U₁ V₀ V₁ q b) := isSPeriodic_fldc q _ b

theorem contDiff_recWDD {q N : ℕ} (τ t₀ : ℝ) (U₀ U₁ V₀ V₁ : GS d n N) (b : Fin n) :
    ContDiff ℝ ∞ (recWDD τ t₀ U₀ U₁ V₀ V₁ q b) := by
  refine contDiff_fldc q ?_ b
  unfold hcDD hermiteDD CubicHermite.basisHDD CubicHermite.basisGDD CubicHermite.cubicDD
  fun_prop

theorem isSPeriodic_recWDD {q N : ℕ} (τ t₀ : ℝ) (U₀ U₁ V₀ V₁ : GS d n N) (b : Fin n) :
    IsSPeriodic (recWDD τ t₀ U₀ U₁ V₀ V₁ q b) := isSPeriodic_fldc q _ b

/-- **The slice energies of the Hermite record on a cell.** -/
theorem cell_energies {q s N : ℕ} {τ : ℝ} (hτ : 0 < τ) {j : ℕ} {Uj Uj1 Gj Gj1 : GS d n N}
    {U V Ut : Fin n → ST d → ℝ} {D₂ : Fin n → (Fin d → ℤ) → ℝ → ℝ} {t₁ : ℝ}
    (hV : ∀ b, ContDiff ℝ ∞ (V b)) (hVp : ∀ b, IsSPeriodic (V b))
    (hUV : ∀ x ∈ slab (d := d) 0 t₁, ∀ b, U b x = V b x)
    (hVt : ∀ b, ∀ t ∈ Icc 0 t₁, ∀ y, pd (V b) 0 (Fin.cons t y) = Ut b (Fin.cons t y))
    (hVtt : ∀ b k, ∀ t ∈ Icc 0 t₁, coef (pd (pd (V b) 0) 0) t k = D₂ b k t)
    {e₁ e₂ : ℝ}
    (h0 : ∀ θ ∈ Icc (0 : ℝ) 1, ∀ S : Finset (Fin d → ℤ), ∑ b, ∑ k ∈ S, wq (s + 2) k *
      (cf q (hermite τ Uj Uj1 Gj Gj1 θ) b k - coef (U b) (j * τ + θ * τ) k) ^ 2 ≤ e₂)
    (h1 : ∀ θ ∈ Icc (0 : ℝ) 1, ∀ S : Finset (Fin d → ℤ), ∑ b, ∑ k ∈ S, wq (s + 2) k *
      (cf q (hermiteD τ Uj Uj1 Gj Gj1 θ) b k - coef (Ut b) (j * τ + θ * τ) k) ^ 2 ≤ e₂)
    (h2 : ∀ θ ∈ Icc (0 : ℝ) 1, ∀ S : Finset (Fin d → ℤ), ∑ b, ∑ k ∈ S, wq s k *
      (cf q (hermiteDD τ Uj Uj1 Gj Gj1 θ) b k - D₂ b k (j * τ + θ * τ)) ^ 2 ≤ e₁)
    {t : ℝ} (ht : t ∈ Icc ((j : ℝ) * τ) (((j : ℝ) + 1) * τ)) (ht₁ : ((j : ℝ) + 1) * τ ≤ t₁) :
    ∑ b, Q (s + 2) (fun x => recW τ (j * τ) Uj Uj1 Gj Gj1 q b x - V b x) t ≤ e₂ ∧
    ∑ b, Q (s + 2) (fun x => pd (recW τ (j * τ) Uj Uj1 Gj Gj1 q b) 0 x - pd (V b) 0 x) t ≤ e₂ ∧
    ∑ b, Q s (fun x => pd (pd (recW τ (j * τ) Uj Uj1 Gj Gj1 q b) 0) 0 x -
      pd (pd (V b) 0) 0 x) t ≤ e₁ := by
  set θ := (t - j * τ) / τ with hθ
  have hθt : (j : ℝ) * τ + θ * τ = t := by rw [hθ]; field_simp; ring
  have hθI : θ ∈ Icc (0 : ℝ) 1 := by
    rw [hθ]
    constructor
    · exact div_nonneg (by linarith [ht.1]) hτ.le
    · rw [div_le_one hτ]; linarith [ht.2]
  have ht0 : t ∈ Icc 0 t₁ := ⟨le_trans (by positivity) ht.1, ht.2.trans ht₁⟩
  have hslice : ∀ y : Fin d → ℝ, (Fin.cons t y : ST d) ∈ slab (d := d) 0 t₁ := fun y => by
    show (Fin.cons t y : ST d) 0 ∈ Icc 0 t₁; simpa using ht0
  have hτ0 : τ ≠ 0 := hτ.ne'
  have hWt : ∀ b, pd (recW τ (j * τ) Uj Uj1 Gj Gj1 q b) 0 = recWD τ (j * τ) Uj Uj1 Gj Gj1 q b :=
    fun b => funext fun x => pd_recW_zero τ _ Uj Uj1 Gj Gj1 hτ0 b x
  have hWtt : ∀ b, pd (pd (recW τ (j * τ) Uj Uj1 Gj Gj1 q b) 0) 0 =
      recWDD τ (j * τ) Uj Uj1 Gj Gj1 q b := fun b => by
    rw [hWt b]; exact funext fun x => pd_recWD_zero τ _ Uj Uj1 Gj Gj1 b x
  refine ⟨?_, ?_, ?_⟩
  · refine sum_Q_le_of_sum_le (s + 2) (fun b => (contDiff_recW τ _ _ _ _ _ b).sub (hV b))
      (fun b k x => by simp only [isSPeriodic_recW τ _ _ _ _ _ b k x, hVp b k x]) fun S => ?_
    refine le_of_eq_of_le ?_ (h0 θ hθI S)
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => ?_
    rw [coef_sub (contDiff_recW τ _ _ _ _ _ b).continuous (hV b).continuous, coef_recW, hθt,
      GenGalCons.coef_congr_slice (f := V b) (g := U b) (fun y => (hUV _ (hslice y) b).symm) k]
  · simp only [hWt]
    refine sum_Q_le_of_sum_le (s + 2) (fun b => (contDiff_recWD τ _ _ _ _ _ b).sub
        (contDiff_pd_top (hV b) 0))
      (fun b k x => by simp only [isSPeriodic_recWD τ _ _ _ _ _ b k x,
        isSPeriodic_pd (hVp b) 0 k x]) fun S => ?_
    refine le_of_eq_of_le ?_ (h1 θ hθI S)
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => ?_
    rw [coef_sub (contDiff_recWD τ _ _ _ _ _ b).continuous (contDiff_pd_top (hV b) 0).continuous,
      coef_recWD, hθt, GenGalCons.coef_congr_slice (f := pd (V b) 0) (g := Ut b)
        (fun y => hVt b t ht0 y) k]
  · simp only [hWtt]
    refine sum_Q_le_of_sum_le s (fun b => (contDiff_recWDD τ _ _ _ _ _ b).sub
        (contDiff_pd_top (contDiff_pd_top (hV b) 0) 0))
      (fun b k x => by simp only [isSPeriodic_recWDD τ _ _ _ _ _ b k x,
        isSPeriodic_pd (isSPeriodic_pd (hVp b) 0) 0 k x]) fun S => ?_
    refine le_of_eq_of_le ?_ (h2 θ hθI S)
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun k _ => ?_
    rw [coef_sub (contDiff_recWDD τ _ _ _ _ _ b).continuous
      (contDiff_pd_top (contDiff_pd_top (hV b) 0) 0).continuous, coef_recWDD, hθt,
      hVtt b k t ht0]

end RenewalGeometry.GenHermite
