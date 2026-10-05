/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.HarmonicSubsidiaryJet

/-!
# The subsidiary equation with sources (`eq:subsidiary`, Einstein–Standard-Model action-closure
  manuscript, `prop:subsidiary`)

Exact jet algebra at a point, over an arbitrary finite index type, on top of
`Gravity/ContractedBianchiJet.lean` and `Gravity/HarmonicSubsidiaryJet.lean`.  For a valid metric
3-jet `J`, a covector 2-jet `(C, dC, ddC)` (the harmonic gauge covector), constants `Λ, κ`, and
symmetric 2-tensor 1-jets `(T, dT)` (stress) and `(r, dr)` (residual):

* `divS J S dS` — the covariant divergence `∇^a S_{ab} = G^{ea}(∂_e S - Γ_e^T S - S Γ_e)_{ab}`;
* `divS_add`, `divS_smul`, `divS_metric` (`∇^a g_{ab} = 0`, metric compatibility);
* **`subsidiary_with_source`** (`eq:subsidiary`): if the reduced Einstein equation
  `Ĝ + Λg = κT + r` holds together with its first derivatives, where
  `Ĝ = G - ∇_{(μ}C_{ν)} + ½ g ∇^αC_α` (`eq:reduced-Einstein`; the library's `resM`), then
  `□C_ν + Ric_ν{}^μ C_μ = -2 𝒲_ν`, `𝒲_ν = κ ∇^μT_{μν} + ∇^μ r_{μν}` — the covariant divergence
  of the reduced equation, by the contracted Bianchi identity (`contracted_bianchi`) and the
  commutation identity `2∇^μ∇_{(μ}C_{ν)} - ∇_ν∇^αC_α = □C_ν + Ric_ν{}^μC_μ` (`divH_eq`).
-/

open Finset Matrix
open scoped BigOperators

namespace RenewalGeometry.ContractedBianchiJet
namespace SubsidiarySource

noncomputable section

set_option linter.unusedSectionVars false

variable {n : Type*} [Fintype n] [DecidableEq n]

open Jet3

/-- The covariant divergence `∇^a S_{ab}` of a 2-tensor 1-jet `(S, dS)`. -/
def divS (J : Jet3 n) (S : Matrix n n ℝ) (dS : n → Matrix n n ℝ) (b : n) : ℝ :=
  ∑ e, ∑ a, J.G e a * (dS e - (J.chr e)ᵀ * S - S * J.chr e) a b

theorem divS_add (J : Jet3 n) (S S' : Matrix n n ℝ) (dS dS' : n → Matrix n n ℝ) (b : n) :
    divS J (S + S') (fun e => dS e + dS' e) b = divS J S dS b + divS J S' dS' b := by
  unfold divS
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.sub_apply, Matrix.add_apply]
  ring

theorem divS_smul (J : Jet3 n) (k : ℝ) (S : Matrix n n ℝ) (dS : n → Matrix n n ℝ) (b : n) :
    divS J (k • S) (fun e => k • dS e) b = k * divS J S dS b := by
  unfold divS
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- `∇^a g_{ab} = 0` (metric compatibility). -/
theorem divS_metric {J : Jet3 n} (hv : J.Valid) (b : n) : divS J J.g J.dg b = 0 := by
  unfold divS
  refine Finset.sum_eq_zero fun e _ => Finset.sum_eq_zero fun a _ => ?_
  rw [metric_compat hv e]
  simp

theorem divRes_eq_divS (J : Jet3 n) (c : n → ℝ) (dc : Matrix n n ℝ) (ddc : n → Matrix n n ℝ)
    (b : n) : J.divRes c dc ddc b = divS J (J.resM c dc) (J.dresM c dc ddc) b := rfl

/-- **`eq:subsidiary`**: for a valid metric 3-jet, a harmonic gauge covector 2-jet `(C, dC, ddC)`
with symmetric second jet, and the reduced Einstein equation `Ĝ + Λ g = κ T + r` holding with
its first derivatives (`Ĝ = resM`), the gauge covector satisfies
`□C_b + Ric^l{}_b C_l = -2 (κ ∇^aT_{ab} + ∇^a r_{ab})`. -/
theorem subsidiary_with_source {J : Jet3 n} (hv : J.Valid) (C : n → ℝ) (dC : Matrix n n ℝ)
    (ddC : n → Matrix n n ℝ) (hddC : ∀ e a, ddC e a = ddC a e) (Λ κ : ℝ) (T r : Matrix n n ℝ)
    (dT dr : n → Matrix n n ℝ) (heq : J.resM C dC + Λ • J.g = κ • T + r)
    (hdeq : ∀ e, J.dresM C dC ddC e + Λ • J.dg e = κ • dT e + dr e) (b : n) :
    J.boxC C dC ddC b + J.ricC C b = -2 * (κ * divS J T dT b + divS J r dr b) := by
  rw [forced_subsidiary hv C dC ddC hddC b, divRes_eq_divS]
  have hres : J.resM C dC = (κ • T + r) + (-Λ) • J.g := by
    rw [← heq]; simp
  have hdres : J.dresM C dC ddC = fun e => (κ • dT e + dr e) + (-Λ) • J.dg e := by
    funext e; rw [← hdeq e]; simp
  rw [hres, hdres, divS_add, divS_smul, divS_metric hv, mul_zero, add_zero]
  have : divS J (κ • T + r) (fun e => κ • dT e + dr e) b = κ * divS J T dT b + divS J r dr b := by
    rw [divS_add, divS_smul]
  rw [this]

/-- Non-vacuity: for every valid metric 3-jet and covector 2-jet, the hypotheses are met with
`κ = 1`, `Λ = 0`, `r = 0` and the stress jet `T = Ĝ`; and the flat metric jet is valid. -/
example {J : Jet3 n} (hv : J.Valid) (C : n → ℝ) (dC : Matrix n n ℝ) (ddC : n → Matrix n n ℝ)
    (hddC : ∀ e a, ddC e a = ddC a e) (b : n) :
    J.boxC C dC ddC b + J.ricC C b =
      -2 * (1 * divS J (J.resM C dC) (J.dresM C dC ddC) b + divS J 0 (fun _ => 0) b) :=
  subsidiary_with_source hv C dC ddC hddC 0 1 (J.resM C dC) 0 (J.dresM C dC ddC) (fun _ => 0)
    (by simp) (fun e => by simp) b

example : (⟨1, 1, fun _ => 0, fun _ _ => 0, fun _ _ _ => 0⟩ : Jet3 (Fin 4)).Valid :=
  ⟨by simp, by simp, by simp, fun _ => by simp, fun _ _ => by simp, fun _ _ => rfl,
    fun _ _ _ => by simp, fun _ _ _ => rfl, fun _ _ _ => rfl⟩

end

end SubsidiarySource
end RenewalGeometry.ContractedBianchiJet
