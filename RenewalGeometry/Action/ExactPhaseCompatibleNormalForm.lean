/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Action.ExactPhaseCompatibleAction

/-!
# The connection normal form of the completed action (time integration by parts)
  (`eq:supp-exact-completed-action`, `eq:supp-exact-connection-normal-form`,
  `eq:supp-exact-connection-load`; emergent-spacetime manuscript)

Continuation of `Action/ExactPhaseCompatibleAction.lean`.

* `norm_entry_le`, `abs_pairing_le`: in the `ℓ∞`-operator norm, `|X_{ab}| ≤ ‖X‖` and
  `|b(X, Y)| ≤ 4‖X‖‖Y‖`; `hasDerivAt_pairing`: the product rule for `b` along paths.
* `nfDensity`: the integrand of the connection normal form
  `-2χΛ det e + f_h(e)·A + q_e(A) + r_h(e, A)` with
  `f_{h,0} = Σ_i D_i^-Π_i`, `f_{h,i} = -∂_tΠ_i - Σ_{j≠i} D_j^-Σ_ji` (`eq:supp-exact-connection-load`;
  `∂_tΠ_i` is supplied as the time derivative `Πdot` of `t ↦ Π_i(e(t))`).
* `gridPair_completedDensity_eq`: `⟨completed density, 1⟩_h = ⟨nfDensity, 1⟩_h + d/dt (boundary)`.
* **`completedAction_eq_normalForm`** (`eq:supp-exact-connection-normal-form`): for differentiable
  connection paths and coframe paths (with `Π_i ∘ e` differentiable), the completed action equals
  `∫₀ᵀ ⟨-2χΛ det e + f_h(e)·A + q_e(A) + r_h(e, A), 1⟩_h dt`: the boundary term of
  `eq:supp-exact-completed-action` is exactly the boundary term of the time integration by parts of
  `⟨b(Π_i, Ȧ_i), 1⟩_h`, so the normal form contains no connection velocity.
-/

open Finset NormedSpace

noncomputable section

namespace RenewalGeometry.ExactPhaseAction

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

set_option linter.unusedSectionVars false

open LogBCH

/-! ### Norm bounds for entries and the pairing -/

theorem norm_entry_le (X : M4) (a b : Fin 4) : |X a b| ≤ ‖X‖ := by
  rw [Matrix.linfty_opNorm_def]
  have h1 : (‖X a b‖₊ : ℝ) ≤ ((∑ j, ‖X a j‖₊ : NNReal) : ℝ) := by
    exact_mod_cast Finset.single_le_sum (f := fun j => ‖X a j‖₊) (fun _ _ => by positivity)
      (Finset.mem_univ b)
  have h2 : ((∑ j, ‖X a j‖₊ : NNReal) : ℝ) ≤
      ((Finset.univ.sup fun i => ∑ j, ‖X i j‖₊ : NNReal) : ℝ) := by
    exact_mod_cast Finset.le_sup (f := fun i => ∑ j, ‖X i j‖₊) (Finset.mem_univ a)
  have : |X a b| = (‖X a b‖₊ : ℝ) := by simp [Real.norm_eq_abs]
  rw [this]
  exact h1.trans h2

theorem abs_pairing_le (X Y : M4) : |pairing X Y| ≤ 4 * (‖X‖ * ‖Y‖) := by
  unfold pairing Matrix.trace Matrix.diag
  calc |∑ a, (X * Y) a a| ≤ ∑ a : Fin 4, |(X * Y) a a| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a : Fin 4, ‖X * Y‖ := Finset.sum_le_sum fun a _ => norm_entry_le _ a a
    _ = 4 * ‖X * Y‖ := by simp
    _ ≤ 4 * (‖X‖ * ‖Y‖) := by gcongr; exact norm_mul_le X Y

/-- A linear map with a norm bound commutes with derivatives of paths (generic helper, stated
for arbitrary normed spaces so that it applies to `M4` with its `ℓ∞`-operator norm). -/
theorem hasDerivAt_linear_comp {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (L : F →ₗ[ℝ] G) (C : ℝ) (hL : ∀ x, ‖L x‖ ≤ C * ‖x‖)
    {γ : ℝ → F} {v : F} {t : ℝ} (h : HasDerivAt γ v t) :
    HasDerivAt (fun s => L (γ s)) (L v) t :=
  (L.mkContinuous C hL).hasFDerivAt.comp_hasDerivAt t h

theorem abs_trace_le (X : M4) : |Matrix.trace X| ≤ 4 * ‖X‖ := by
  unfold Matrix.trace Matrix.diag
  calc |∑ a, X a a| ≤ ∑ a : Fin 4, |X a a| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a : Fin 4, ‖X‖ := Finset.sum_le_sum fun a _ => norm_entry_le _ a a
    _ = 4 * ‖X‖ := by simp

/-- Product rule for the pairing along paths. -/
theorem hasDerivAt_pairing {P Q : ℝ → M4} {P' Q' : M4} {t : ℝ} (hP : HasDerivAt P P' t)
    (hQ : HasDerivAt Q Q' t) :
    HasDerivAt (fun s => pairing (P s) (Q s)) (pairing P' (Q t) + pairing (P t) Q') t := by
  have hm : HasDerivAt (fun s => P s * Q s) (P' * Q t + P t * Q') t := hP.fun_mul hQ
  have := hasDerivAt_linear_comp (Matrix.traceLinearMap (Fin 4) ℝ ℝ) 4
    (fun X => by rw [Real.norm_eq_abs]; exact abs_trace_le X) hm
  simpa [pairing, Matrix.traceLinearMap_apply, Matrix.trace_add] using this

/-! ### The normal-form integrand -/

variable {N : ℕ} [NeZero N]

/-- The integrand of the connection normal form `eq:supp-exact-connection-normal-form`:
`-2χΛ det e + f_{h,0}·A₀ + Σ_i f_{h,i}·A_i + q_e(A) + r_h(e, A)` with
`f_{h,i} = -∂_tΠ_i - Σ_{j≠i} D_j^-Σ_ji` (`Pidot i x = ∂_tΠ_i(x)`). -/
def nfDensity (χ Λ h : ℝ) (e : Site N → M4) (Pidot : Fin 3 → Site N → M4) (A0 : Site N → M4)
    (A : Fin 3 → Site N → M4) (x : Site N) : ℝ :=
  -2 * χ * Λ * (e x).det + pairing (load0 χ h e x) (A0 x) +
    (∑ i, pairing (-Pidot i x + loadSp χ h e i x) (A i x)) + qc χ e A0 A x +
    remDensity χ h e A0 A x

theorem gridPair_add (h : ℝ) (f g : Site N → ℝ) :
    gridPair h (fun x => f x + g x) = gridPair h f + gridPair h g := by
  simp [gridPair, Finset.sum_add_distrib, mul_add]

/-- Grid-level normal form: the completed density equals the normal-form density plus the
exact time derivative of the boundary density `Σ_i b(Π_i, A_i)`. -/
theorem gridPair_completedDensity_eq {h : ℝ} (hh : h ≠ 0) (χ Λ : ℝ) (e A0 : Site N → M4)
    (A Adot Pidot : Fin 3 → Site N → M4) :
    gridPair h (completedDensity χ Λ h e A0 A Adot) =
      gridPair h (nfDensity χ Λ h e Pidot A0 A) +
        gridPair h (fun x => ∑ i, (pairing (Pidot i x) (A i x) +
          pairing (piArr χ (e x) i) (Adot i x))) := by
  unfold gridPair
  rw [← mul_add]
  congr 1
  rw [Finset.sum_congr rfl fun x _ => completedDensity_eq hh χ Λ e A0 A Adot x]
  have hsbp0 : ∑ x, ∑ i, pairing (piArr χ (e x) i) (Dp h i A0 x) =
      -∑ x, pairing (load0 χ h e x) (A0 x) := by
    rw [Finset.sum_comm]
    simp only [sum_pairing_Dp h _ (fun y => piArr χ (e y) _), load0, pairing_sum_left,
      Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
  have hsbp := sumLt_sigma_Dp χ h e A
  unfold nfDensity
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, pairing_add_left, pairing_neg_left,
    Finset.sum_neg_distrib] at *
  rw [hsbp0, hsbp]
  ring

/-- **The connection normal form of the completed action** (`eq:supp-exact-connection-normal-form`):
for paths with `A` differentiable (velocity `deriv A`), `Π_i ∘ e` differentiable with derivative
`Πdot`, and the two integrands integrable,
`𝒫^c_{h,D} = ∫₀ᵀ ⟨-2χΛ det e + f_h(e)·A + q_e(A) + r_h(e, A), 1⟩_h dt`. -/
theorem completedAction_eq_normalForm {h : ℝ} (hh : h ≠ 0) (χ Λ T : ℝ)
    (e A0 : ℝ → Site N → M4) (A : ℝ → Fin 3 → Site N → M4) (Pidot : ℝ → Fin 3 → Site N → M4)
    (hA : ∀ t, HasDerivAt A (deriv A t) t)
    (hPi : ∀ t i x, HasDerivAt (fun s => piArr χ (e s x) i) (Pidot t i x) t)
    (hint : IntervalIntegrable
      (fun t => gridPair h (nfDensity χ Λ h (e t) (Pidot t) (A0 t) (A t))) MeasureTheory.volume 0 T)
    (hdint : IntervalIntegrable
      (fun t => gridPair h (fun x => ∑ i, (pairing (Pidot t i x) (A t i x) +
        pairing (piArr χ (e t x) i) (deriv A t i x)))) MeasureTheory.volume 0 T) :
    completedAction χ Λ h T e A0 A =
      ∫ t in (0 : ℝ)..T, gridPair h (nfDensity χ Λ h (e t) (Pidot t) (A0 t) (A t)) := by
  unfold completedAction
  have hpt := fun t => gridPair_completedDensity_eq hh χ Λ (e t) (A0 t) (A t) (deriv A t) (Pidot t)
  simp only [hpt]
  rw [intervalIntegral.integral_add hint hdint]
  have hB : ∀ t, HasDerivAt (fun s => boundaryTerm χ h (e s) (A s))
      (gridPair h (fun x => ∑ i, (pairing (Pidot t i x) (A t i x) +
        pairing (piArr χ (e t x) i) (deriv A t i x)))) t := by
    intro t
    unfold boundaryTerm gridPair
    beta_reduce
    refine HasDerivAt.const_mul _ (HasDerivAt.fun_sum fun x _ => HasDerivAt.fun_sum fun i _ => ?_)
    have hAi : HasDerivAt (fun s => A s i x) (deriv A t i x) t := by
      have h1 := (hasDerivAt_pi.1 (hA t)) i
      exact (hasDerivAt_pi.1 h1) x
    exact hasDerivAt_pairing (hPi t i x) hAi
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hB t) hdint]
  ring

end RenewalGeometry.ExactPhaseAction
