/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.ActualJetKatoRealization
import RenewalGeometry.Continuum.KatoGeneratedDynamics

/-!
# The generated dynamics of the actual-jet system: rates

Einstein–Standard-Model action-closure manuscript, `thm:generated-dynamics` on the coupled
actual-jet system `eq:generated-symmetric-system` (`Σ = 𝕋³`).  The generic rates of
`KatoGenDyn.generated_dynamics_rates` are instantiated on the realized actual-jet system of
`ActualJetKato.actual_jet_kato_realization`: in the Euclidean coordinates `κ` of the block inner
product of `prop:actual-jet-writer`, for every compact chart set `K` there are smooth symmetric
coefficient maps which **are** the actual-jet principal operators and forcing on `K`, and for
every data radius the full rate package `KatoGenDyn.GeneratedRates` holds:
`eq:generated-midpoint`/`-CFL`/`-uniform` with general finite data `U_{0,N}`
(`‖U_{0,N} - U₀‖_{H^{s+4}} ≤ δ`), `eq:generated-Galerkin-rate` (`a = 2`: second time derivative
of the Kato solution), `eq:generated-time-rate` (`‖U^j - U(t_j)‖_{H^{s+4}} ≤ C(τ² + δ + N^{-p})`)
and the state-level Hermite readout `eq:generated-Hermite`
(`H^{s+2}` values and first time derivatives `O(τ² + δ + N^{-p})`, `H^s` second time derivatives
`O(τ + δ + N^{-p})`).  The physical heads are linear readouts of the state (the coordinates `κ`),
so `eq:generated-first` follows at the head level from the state-level bounds.

* **`actual_jet_generated_rates`** — the instantiation (`d = 3`, `m_s = 2`, `s ≥ 3`, `p ≥ 1`,
  `q = s + p + 8`; the manuscript has `s ≥ 5`).
* `sum_linear_readout_le` — linear (head) readouts inherit the state-level coefficient bounds.
* Non-vacuity: `generatedRates_example` (the system `∂_tU + σ₁∂₁U = -U` on `𝕋³`).

Disclosed rendering (as in `ActualJetKatoRealization`): `Σ = 𝕋³`; the coefficient maps are smooth
cutoff extensions from the compact chart set `K`; the evolved system is the independent symmetric
extension `eq:generated-extension`; the realized solution solves the actual-jet system where its
values stay in `K` (`ActualJetKato.solves_actual_jet_on_margin`).
-/

open Finset Set Filter Topology
open scoped ContDiff

noncomputable section

namespace RenewalGeometry.ActualJetGenRates

open ActualJetSystem ActualJetSmooth ActualJetWriter FrameCurvature TwistedHalfRicci ActualJetKato

set_option linter.unusedSectionVars false

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable {SM : SMData (MatLie m) V S S'} {bG : MatLie m →ₗ[ℝ] MatLie m →ₗ[ℝ] ℝ}
  {bV : V →ₗ[ℝ] V →ₗ[ℝ] ℝ} {bS : S →ₗ[ℝ] S →ₗ[ℝ] ℝ} {bS' : S' →ₗ[ℝ] S' →ₗ[ℝ] ℝ}

/-- **The fully finite approximation branch of the actual-jet system: rates**
(`thm:generated-dynamics`, `Σ = 𝕋³`): for theory data with smooth sources and forms satisfying
the positivity and Clifford unitarity relations of `prop:actual-jet-writer`, in the Euclidean
coordinates `κ` of the block inner product, for every compact set `K` of states in the Lorentzian
chart there are smooth symmetric coefficient maps that are the actual-jet principal operators
and forcing on `K`, and for every data radius `R₀` the generated dynamics has the rates
`KatoGenDyn.GeneratedRates` (`q = s + p + 8`, `2m_s ≤ s + 1`, `m_s ≤ p + 3`, `m_s > 3/2`). -/
theorem actual_jet_generated_rates (hS : SMSmooth SM) (hU : UnitaryForms SM bG bV bS bS')
    {ms s p : ℕ} (hms : (3 : ℝ) / 2 < ms) (hs : 2 * ms ≤ s + 1) (hp : 1 ≤ p)
    (hmsp : ms ≤ p + 3) :
    ∃ κ : StateP m V S S' ≃ₗ[ℝ] (Fin (dimS m V S S') → ℝ),
      (∀ v w, ipP bG bV bS bS' (κ.symm v) (κ.symm w) = ∑ i, v i * w i) ∧
      ∀ K : Set (Fin (dimS m V S S') → ℝ), IsCompact K → (∀ v ∈ K, MetChart (κ.symm v).1) →
      ∃ (A : Fin 3 → Fin (dimS m V S S') → Fin (dimS m V S S') →
          (Fin (dimS m V S S') → ℝ) → ℝ) (F : Fin (dimS m V S S') →
          (Fin (dimS m V S S') → ℝ) → ℝ),
        (∀ v ∈ K, ∀ j a (w : Fin (dimS m V S S') → ℝ), ∑ b, A j a b v * w b =
          κ (toS (princ (frameU (ginvOf (κ.symm v).1.1)) SM.D.Fr SM.Db.Fr j
            (ofP (κ.symm w)))) a) ∧
        (∀ v ∈ K, ∀ a, F a v = κ (toS (Fsys SM (ofP (κ.symm v)))) a) ∧
        ∀ R₀ : ℝ, 0 ≤ R₀ → KatoGenDyn.GeneratedRates A F s p R₀ := by
  obtain ⟨κ, hκ, hreal⟩ := actual_jet_kato_realization hS hU
  refine ⟨κ, hκ, fun K hK hKc => ?_⟩
  obtain ⟨A, F, hA, hsym, hF, hAK, hFK⟩ := hreal K hK hKc
  exact ⟨A, F, hAK, hFK, fun R₀ hR₀ =>
    KatoGenDyn.generated_dynamics_rates (d := 3) hms hs hp hmsp hA hsym hF hR₀⟩

/-- **Non-vacuity of the rate package** on `𝕋³` (`m_s = 2`, `s = 3`, `p = 1`, `q = 12`) for the
symmetric system `∂_tU + σ₁∂₁U = -U`. -/
theorem generatedRates_example :
    KatoGenDyn.GeneratedRates (d := 3) (n := 2) KatoGalerkin.exampleA (fun a v => -v a) 3 1 1 :=
  KatoGenDyn.generated_dynamics_rates (ms := 2) (by norm_num) (by norm_num) le_rfl (by norm_num)
    (fun _ _ _ => by unfold KatoGalerkin.exampleA; exact contDiff_const)
    (fun i a b v => by
      unfold KatoGalerkin.exampleA
      fin_cases i <;> fin_cases a <;> fin_cases b <;> simp)
    (fun a => (contDiff_apply ℝ ℝ a).neg) zero_le_one

/-- **Linear readouts of the state** (the physical heads in the coordinates `κ`,
`eq:generated-first`): for every real matrix `Λ` (head components `b'` as linear combinations of
state components `b`) the weighted coefficient error of the readout is bounded by
`(Σ Λ²)` times that of the state. -/
theorem sum_linear_readout_le {n n' d : ℕ} (Λ : Fin n' → Fin n → ℝ) (S : Finset (Fin d → ℤ))
    (w : (Fin d → ℤ) → ℝ) (hw : ∀ k, 0 ≤ w k) (e : Fin n → (Fin d → ℤ) → ℝ) :
    ∑ b', ∑ k ∈ S, w k * (∑ b, Λ b' b * e b k) ^ 2 ≤
      (∑ b', ∑ b, Λ b' b ^ 2) * ∑ b, ∑ k ∈ S, w k * e b k ^ 2 := by
  have h1 : ∀ b' k, w k * (∑ b, Λ b' b * e b k) ^ 2 ≤
      (∑ b, Λ b' b ^ 2) * ∑ b, w k * e b k ^ 2 := fun b' k => by
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun b => Λ b' b) (fun b => e b k)
    rw [← Finset.mul_sum]
    calc w k * (∑ b, Λ b' b * e b k) ^ 2 ≤ w k * ((∑ b, Λ b' b ^ 2) * ∑ b, e b k ^ 2) :=
          mul_le_mul_of_nonneg_left this (hw k)
      _ = (∑ b, Λ b' b ^ 2) * (w k * ∑ b, e b k ^ 2) := by ring
  calc ∑ b', ∑ k ∈ S, w k * (∑ b, Λ b' b * e b k) ^ 2
      ≤ ∑ b', ∑ k ∈ S, (∑ b, Λ b' b ^ 2) * ∑ b, w k * e b k ^ 2 :=
        Finset.sum_le_sum fun b' _ => Finset.sum_le_sum fun k _ => h1 b' k
    _ = ∑ b', (∑ b, Λ b' b ^ 2) * ∑ b, ∑ k ∈ S, w k * e b k ^ 2 := by
        refine Finset.sum_congr rfl fun b' _ => ?_
        rw [← Finset.mul_sum, Finset.sum_comm]
    _ = (∑ b', ∑ b, Λ b' b ^ 2) * ∑ b, ∑ k ∈ S, w k * e b k ^ 2 := by
        rw [Finset.sum_mul]

end RenewalGeometry.ActualJetGenRates
