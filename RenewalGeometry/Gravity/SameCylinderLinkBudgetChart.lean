/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.GaugeTheory.LiteralLinkCompactnessLimit

/-!
# From the high-order link budget to the literal-link chart and energy
  (`prop:supp-same-cylinder-link-budget`, final sentence; `eq:supp-same-cylinder-link-budget`,
  `eq:main-link-chart`, `eq:main-link-energy`; emergent-spacetime manuscript)

The last sentence of `prop:supp-same-cylinder-link-budget` says that the high-order budget
`eq:supp-same-cylinder-link-budget`,
`sup_h (‖A_h‖_{L^∞_t H^s_h} + ‖∂ₜA_h‖_{L^∞_t H^{s-1}_h} + ‖A_{0,h}‖_{L²} + ‖E_h‖_{L²} + ‖F_h‖_{L²}) < ∞`
(`s ≥ 3`), implies the hypotheses `eq:main-link-chart`–`eq:main-link-energy` of
`thm:main-literal-link-compactness` on every sufficiently fine cutoff.  This file proves that
implication for the spatial connection (the `A₀`, `E`, `F` bounds are common to both budgets):

* `inv_mul_norm_le_of_matSobSq`: uniform discrete `H² ⊂ L^∞` gives
  `h ‖A(x)‖ ≤ h √(K B)` when `‖A‖²_{s,h} ≤ B`, `s ≥ 2`;
* `link_chart_eventually`: for every `δ > 0`, the chart `h |A_{i,h}| ≤ δ` holds on a cofinal tail
  of cutoffs `h = 1/N_m → 0` (`eq:main-link-chart`, "Sobolev embedding gives `h‖A_h‖_∞ → 0`");
* `link_energy_of_budget`: `‖A(t)‖²_h ≤ B` and `∫₀ᵀ Σ_i ‖A_i‖²_{1,h} ≤ 3 B T`, i.e. the
  `L^∞_t L²_h` and `L²_t H¹_h` parts of `eq:main-link-energy`, in exactly the form of the
  hypotheses `hAinf`, `hAH1` of `LiteralLinkLimit.literal_link_compactness`.

What is NOT proved here (and keeps `prop:supp-same-cylinder-link-budget` open): the budget itself,
which needs the finite-cutoff spinless Cartan reconstruction `e_h ↦ (A_h, A_{0,h})` (not written
in the manuscript) and the cutoff-uniform metric-jet bounds of the open
`thm:main-open-3plus1` / `thm:main-open-law-basin`.
-/

namespace RenewalGeometry
namespace SameCylinderLinkBudget

open MeasureTheory Filter Topology
open scoped Matrix.Norms.Frobenius
open PeriodicGridSobolev LiteralLink LiteralLinkLimit

variable {n : ℕ}

/-- Uniform discrete `H^s ⊂ L^∞` (`s ≥ 2`) for matrix arrays: if `‖φ‖²_{s,h} ≤ B` then
`h ‖φ(x)‖ ≤ h √(K B)` with the cutoff-independent constant `K = Kprod`. -/
theorem inv_mul_norm_le_of_matSobSq {N : ℕ} [NeZero N] {s : ℕ} (hs : 2 ≤ s) {B : ℝ}
    (φ : MatArr N n) (hφ : matSobSq s φ ≤ B) (x : Grid N) :
    (N : ℝ)⁻¹ * ‖φ x‖ ≤ (N : ℝ)⁻¹ * Real.sqrt (Kprod * B) := by
  have h2 : matSobSq 2 φ ≤ matSobSq s φ :=
    Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => sobSq_mono hs _
  have hsq : ‖φ x‖ ^ 2 ≤ Kprod * B :=
    (norm_sq_le_matSobSq_two φ x).trans
      (mul_le_mul_of_nonneg_left (h2.trans hφ) Kprod_nonneg)
  have : ‖φ x‖ ≤ Real.sqrt (Kprod * B) := Real.le_sqrt_of_sq_le hsq
  exact mul_le_mul_of_nonneg_left this (by positivity)

/-- **The literal-link chart on a cofinal tail** (`eq:main-link-chart`).  If `N_m → ∞` and
`‖A_{i}(t)‖²_{s,h} ≤ B` (`s ≥ 2`) for all `t` in a time set `I`, then for every `δ > 0`,
eventually `h ‖A_i(t, x)‖ ≤ δ` for all `t ∈ I`, `i`, `x`. -/
theorem link_chart_eventually {s : ℕ} (hs : 2 ≤ s) {B δ : ℝ} (hδ : 0 < δ) (I : Set ℝ)
    {Nm : ℕ → ℕ} [∀ m, NeZero (Nm m)] (hN : Tendsto Nm atTop atTop)
    (A : ∀ m, ℝ → Fin 3 → MatArr (Nm m) n)
    (hbud : ∀ m, ∀ t ∈ I, ∀ i, matSobSq s (A m t i) ≤ B) :
    ∀ᶠ m in atTop, ∀ t ∈ I, ∀ i x, (Nm m : ℝ)⁻¹ * ‖A m t i x‖ ≤ δ := by
  have hlim : Tendsto (fun m => (Nm m : ℝ)⁻¹ * Real.sqrt (Kprod * B)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun m => ((Nm m : ℕ) : ℝ)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hN)
    simpa using h1.mul_const (Real.sqrt (Kprod * B))
  filter_upwards [(hlim.eventually (gt_mem_nhds hδ))] with m hm t ht i x
  exact (inv_mul_norm_le_of_matSobSq hs (A m t i) (hbud m t ht i) x).trans hm.le

/-- **The `L^∞_t L²_h` and `L²_t H¹_h` parts of the link energy** (`eq:main-link-energy`), in the
form of the hypotheses `hAinf`, `hAH1` of `LiteralLinkLimit.literal_link_compactness`: from
`‖A_i(t)‖²_{s,h} ≤ B` (`s ≥ 1`) on `(0,T]`,
`‖A_i(t)‖²_h ≤ B` and `∫_{(0,T]} Σ_i (‖A_i‖²_h + Σ_j ‖D_j⁺A_i‖²_h) ≤ 3 B T`. -/
theorem link_energy_of_budget {s : ℕ} (hs : 1 ≤ s) {B T : ℝ} (hT : 0 ≤ T)
    {Nm : ℕ → ℕ} [∀ m, NeZero (Nm m)] (A : ∀ m, ℝ → Fin 3 → MatArr (Nm m) n)
    (hbud : ∀ m, ∀ t ∈ Set.Ioc 0 T, ∀ i, matSobSq s (A m t i) ≤ B) :
    (∀ m, ∀ t ∈ Set.Ioc 0 T, ∀ i, matNormSq (A m t i) ≤ B) ∧
    (∀ m, ∫ t in Set.Ioc 0 T,
      ∑ i, (matNormSq (A m t i) + ∑ j, matNormSq (matDp j (A m t i))) ≤ 3 * B * T) := by
  have hone : ∀ {N : ℕ} [NeZero N] (u : MatArr N n),
      matNormSq u + ∑ j, matNormSq (matDp j u) ≤ matSobSq s u := by
    intro N _ u
    rw [← sum_sobSq_one_eq]
    exact Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => sobSq_mono hs _
  refine ⟨fun m t ht i => ?_, fun m => ?_⟩
  · have h0 : matNormSq (A m t i) ≤ matNormSq (A m t i) + ∑ j, matNormSq (matDp j (A m t i)) :=
      le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => matNormSq_nonneg _)
    exact h0.trans ((hone _).trans (hbud m t ht i))
  · have hC : ∀ t ∈ Set.Ioc 0 T,
        ‖∑ i, (matNormSq (A m t i) + ∑ j, matNormSq (matDp j (A m t i)))‖ ≤ 3 * B := by
      intro t ht
      have hnn : 0 ≤ ∑ i, (matNormSq (A m t i) + ∑ j, matNormSq (matDp j (A m t i))) :=
        Finset.sum_nonneg fun i _ => add_nonneg (matNormSq_nonneg _)
          (Finset.sum_nonneg fun j _ => matNormSq_nonneg _)
      rw [Real.norm_of_nonneg hnn]
      calc ∑ i, (matNormSq (A m t i) + ∑ j, matNormSq (matDp j (A m t i)))
          ≤ ∑ _i : Fin 3, B := Finset.sum_le_sum fun i _ => (hone _).trans (hbud m t ht i)
        _ = 3 * B := by simp
    have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Set.Ioc 0 T)
      (by simp) hC
    rw [Real.volume_real_Ioc_of_le hT, sub_zero] at this
    exact (le_abs_self _).trans ((Real.norm_eq_abs _).symm ▸ this)

/-- Non-vacuity: the budget hypothesis holds for the zero connection (with `B = 0`), and the
chart then holds on the tail with `δ = 1/16`. -/
example : ∀ᶠ m in atTop, ∀ t ∈ Set.Ioc (0 : ℝ) 1, ∀ (i : Fin 3) x,
    ((m + 1 : ℕ) : ℝ)⁻¹ * ‖((fun _ _ => 0 : ℝ → Fin 3 → MatArr (m + 1) 2) t i) x‖ ≤ 1 / 16 :=
  link_chart_eventually (s := 2) le_rfl (B := 0) (by norm_num) _ (Nm := fun m => m + 1)
    (tendsto_add_atTop_nat 1) (fun m _ _ => 0) (fun m t _ i => by
      have h0 : ∀ a b, entry (0 : MatArr (m + 1) 2) a b = 0 := fun _ _ => rfl
      simp [matSobSq, sobSq, h0, gridNormSq])

end SameCylinderLinkBudget
end RenewalGeometry
