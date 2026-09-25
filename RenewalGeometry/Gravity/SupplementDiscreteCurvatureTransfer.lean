/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.DiscreteCurvatureCertificateExact
import RenewalGeometry.Gravity.CurvatureEnergyPropagationExact
import RenewalGeometry.Action.ActionCurrentCertificateExact

/-!
# Midpoint propagation with the physical Gram transfer
  (`thm:supp-discrete-curvature`; emergent-spacetime manuscript, supplement)

The supplement theorem restates the fully discrete certificate
`thm:main-discrete-curvature` (proved in
`RenewalGeometry/Gravity/DiscreteCurvatureCertificateExact.lean` as
`discrete_curvature_certificate`) and adds the two clauses of its proof that
the main text leaves implicit:

* the **physical Gram transfer**: for raw curvature records `y_j` with Grams
  `M_j = (M_j^{1/2})²` and actual recorded frame/transport maps `𝒯_j`, the
  normalized records are `Y_j = M_j^{1/2} y_j` and the normalized transfer is
  `T_j = M_{j+1}^{1/2} 𝒯_j M_j^{-1/2}` (`gramTransfer`), so that
  `T_j Y_j = M_{j+1}^{1/2} 𝒯_j y_j` (`gramTransfer_apply_normalized`),
  `‖Y_j‖² = y_jᵀ M_j y_j` (`normalized_norm_sq`), and the norm excess of the
  transfer is bounded by the product of the three factor norms
  (`norm_gramTransfer_le`; the manuscript retains it in `d_j`);
* the **`L²(K)` clause**: with the stable interval interpolation
  (`ρ(t) ≤ C_I ‖Y_{j(t)}‖` for an endpoint `j(t)` of the interval containing
  `t`), the lapse bound `0 ≤ N ≤ N_*`, and the slice decomposition
  `‖R_X‖_{L²(K)} ≤ √(∫₀^{T_X} N ρ²) + C_ζ` (bounded reconstruction error),
  one gets
  `‖R_X‖_{L²(K)} ≤ C_I √(N_* T_X) e^{D_X + A_X^d/(1-b)} (‖Y_0‖ + √(T_X 𝒟_X)/(1-b)) + C_ζ`.

`supplement_discrete_curvature` packages all three conclusions (unique
solvability of each recorded step, the boxed bound
`eq:main-discrete-curvature-bound` for the normalized records, and the
`L²(K)` bound) under the hypotheses of `thm:supp-discrete-curvature` stated
for the raw records and the Gram transfer.

Scoped hypotheses disclosed: the record space is a finite-dimensional real
inner-product space; the Gram square roots `M_j^{1/2}` are supplied as data
(`GramSqrt`); the interpolation, lapse and reconstruction budgets are
abstracted exactly as in `derived_l2_curvature_bound` (the manuscript's
"stable interval interpolation ... integrating with the physical lapse and
adding the bounded reconstruction error").
-/

open scoped BigOperators InnerProductSpace
open Finset MeasureTheory

namespace RenewalGeometry

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The physical Gram transfer `T_j = M_{j+1}^{1/2} 𝒯_j M_j^{-1/2}` between the
normalized records of successive Grams (`thm:supp-discrete-curvature`). -/
def gramTransfer {M M' : V →L[ℝ] V} (R : GramSqrt M) (R' : GramSqrt M')
    (𝒯 : V →L[ℝ] V) : V →L[ℝ] V :=
  (R'.sqrt : V →L[ℝ] V) ∘L 𝒯 ∘L (R.sqrt.symm : V →L[ℝ] V)

/-- On the normalized record `Y = M^{1/2} y` the Gram transfer acts as the raw
transport followed by the next normalization: `T (M^{1/2} y) = M'^{1/2} (𝒯 y)`. -/
theorem gramTransfer_apply_normalized {M M' : V →L[ℝ] V} (R : GramSqrt M) (R' : GramSqrt M')
    (𝒯 : V →L[ℝ] V) (y : V) :
    gramTransfer R R' 𝒯 (R.sqrt y) = R'.sqrt (𝒯 y) := by
  simp [gramTransfer]

/-- The squared norm of the normalized record is the Gram energy of the raw
record: `‖M^{1/2} y‖² = yᵀ M y`. -/
theorem normalized_norm_sq {M : V →L[ℝ] V} (R : GramSqrt M) (y : V) :
    ‖R.sqrt y‖ ^ 2 = ⟪y, M y⟫_ℝ :=
  (gramNormSq_eq R y).symm

/-- The norm excess of the Gram transfer is controlled by the three factors
`‖M'^{1/2}‖ ‖𝒯‖ ‖M^{-1/2}‖` (retained in `d_j` by the manuscript). -/
theorem norm_gramTransfer_le {M M' : V →L[ℝ] V} (R : GramSqrt M) (R' : GramSqrt M')
    (𝒯 : V →L[ℝ] V) :
    ‖gramTransfer R R' 𝒯‖ ≤
      ‖(R'.sqrt : V →L[ℝ] V)‖ * ‖𝒯‖ * ‖(R.sqrt.symm : V →L[ℝ] V)‖ := by
  unfold gramTransfer
  calc ‖(R'.sqrt : V →L[ℝ] V) ∘L 𝒯 ∘L (R.sqrt.symm : V →L[ℝ] V)‖
      ≤ ‖(R'.sqrt : V →L[ℝ] V)‖ * ‖𝒯 ∘L (R.sqrt.symm : V →L[ℝ] V)‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖(R'.sqrt : V →L[ℝ] V)‖ * (‖𝒯‖ * ‖(R.sqrt.symm : V →L[ℝ] V)‖) := by
        gcongr
        exact ContinuousLinearMap.opNorm_comp_le _ _
    _ = _ := by ring

/-- `thm:supp-discrete-curvature`: for raw curvature records `y_j` with Grams
`M_j`, normalized records `Y_j = M_j^{1/2} y_j` and Gram transfer
`T_j = M_{j+1}^{1/2} 𝒯_j M_j^{-1/2}`, the recorded midpoint step
`eq:main-discrete-curvature-update` with `‖T_j‖_op ≤ e^{d_j}`, `K_j` skew,
`(L_j + L_jᵀ)/2 ≼ a_j I`, `a_j, d_j ≥ 0`, `s_j > 0` and `s_j a_j/2 ≤ b < 1`
gives: unique solvability of every recorded step; the boxed bound
`eq:main-discrete-curvature-bound` for `max_j ‖Y_j‖`; and, with a stable
interval interpolation, a lapse bound and a bounded reconstruction error, the
`L²(K)` curvature bound
`‖R_X‖_{L²(K)} ≤ C_I √(N_* T_X) e^{D_X + A_X^d/(1-b)} (‖Y_0‖ + √(T_X 𝒟_X)/(1-b)) + C_ζ`. -/
theorem supplement_discrete_curvature [FiniteDimensional ℝ V] (M : ℕ) (s a d : ℕ → ℝ)
    (Gram : ℕ → V →L[ℝ] V) (R : ∀ j, GramSqrt (Gram j))
    (K L 𝒯 : ℕ → V →L[ℝ] V) (y ε : ℕ → V) (b : ℝ) (hb1 : b < 1)
    (hs : ∀ j < M, 0 < s j) (ha : ∀ j < M, 0 ≤ a j) (hd : ∀ j < M, 0 ≤ d j)
    (hK : ∀ j < M, ∀ x z, ⟪K j x, z⟫_ℝ = -⟪x, K j z⟫_ℝ)
    (hL : ∀ j < M, ∀ x, ⟪x, L j x⟫_ℝ ≤ a j * ‖x‖ ^ 2)
    (hT : ∀ j < M, ‖gramTransfer (R j) (R (j + 1)) (𝒯 j)‖ ≤ Real.exp (d j))
    (hb : ∀ j < M, s j * a j / 2 ≤ b)
    (hupd : ∀ j < M,
      (R (j + 1)).sqrt (y (j + 1)) - gramTransfer (R j) (R (j + 1)) (𝒯 j) ((R j).sqrt (y j)) =
        s j • (K j + L j) ((1 / 2 : ℝ) •
          ((R (j + 1)).sqrt (y (j + 1)) +
            gramTransfer (R j) (R (j + 1)) (𝒯 j) ((R j).sqrt (y j)))) + ε j)
    -- interpolation, lapse and reconstruction budgets on `[0, T_X]`
    (ρ N : ℝ → ℝ) {Nstar CI Cζ RL2 : ℝ} (hCI : 0 ≤ CI)
    (hρ : ∀ t ∈ Set.Icc 0 (∑ i ∈ range M, s i),
      0 ≤ ρ t ∧ ∃ j ≤ M, ρ t ≤ CI * ‖(R j).sqrt (y j)‖)
    (hN : ∀ t ∈ Set.Icc 0 (∑ i ∈ range M, s i), 0 ≤ N t ∧ N t ≤ Nstar)
    (hint : IntervalIntegrable (fun t => N t * ρ t ^ 2) volume 0 (∑ i ∈ range M, s i))
    (hR : RL2 ≤ Real.sqrt (∫ t in (0:ℝ)..(∑ i ∈ range M, s i), N t * ρ t ^ 2) + Cζ) :
    (∀ j < M, ∀ r : V, ∃! w : V, w - (s j / 2) • (K j + L j) w = r) ∧
    (∀ j ≤ M, ‖(R j).sqrt (y j)‖ ≤
      Real.exp (∑ i ∈ range M, d i + (∑ i ∈ range M, s i * a i) / (1 - b)) *
        (‖(R 0).sqrt (y 0)‖ +
          Real.sqrt ((∑ i ∈ range M, s i) * ∑ i ∈ range M, ‖ε i‖ ^ 2 / s i) / (1 - b))) ∧
    RL2 ≤ CI * Real.sqrt (Nstar * ∑ i ∈ range M, s i) *
      (Real.exp (∑ i ∈ range M, d i + (∑ i ∈ range M, s i * a i) / (1 - b)) *
        (‖(R 0).sqrt (y 0)‖ +
          Real.sqrt ((∑ i ∈ range M, s i) * ∑ i ∈ range M, ‖ε i‖ ^ 2 / s i) / (1 - b))) +
      Cζ := by
  -- the normalized records and transfers
  set Y : ℕ → V := fun j => (R j).sqrt (y j) with hY
  set T : ℕ → V →L[ℝ] V := fun j => gramTransfer (R j) (R (j + 1)) (𝒯 j) with hTdef
  have hupd' : ∀ j < M, Y (j + 1) - T j (Y j) =
      s j • (K j + L j) ((1 / 2 : ℝ) • (Y (j + 1) + T j (Y j))) + ε j := fun j hj => hupd j hj
  obtain ⟨hsolv, hbound⟩ := discrete_curvature_certificate M s a d K L T Y ε b hb1 hs ha hd hK hL
    (fun j hj => hT j hj) hb hupd'
  refine ⟨hsolv, fun j hj => hbound j hj, ?_⟩
  -- the `L²(K)` clause
  set B : ℝ := Real.exp (∑ i ∈ range M, d i + (∑ i ∈ range M, s i * a i) / (1 - b)) *
    (‖(R 0).sqrt (y 0)‖ +
      Real.sqrt ((∑ i ∈ range M, s i) * ∑ i ∈ range M, ‖ε i‖ ^ 2 / s i) / (1 - b)) with hB
  set TX : ℝ := ∑ i ∈ range M, s i with hTX
  have hTX0 : 0 ≤ TX := sum_nonneg fun i hi => (hs i (mem_range.mp hi)).le
  have hb0 : 0 < 1 - b := by linarith
  have hB0 : 0 ≤ B := by
    rw [hB]
    have : 0 ≤ Real.sqrt ((∑ i ∈ range M, s i) * ∑ i ∈ range M, ‖ε i‖ ^ 2 / s i) / (1 - b) :=
      div_nonneg (Real.sqrt_nonneg _) hb0.le
    positivity
  have hρ' : ∀ t ∈ Set.Icc 0 TX, 0 ≤ ρ t ∧ ρ t ≤ CI * (fun _ : ℝ => B) t := by
    intro t ht
    obtain ⟨h0, j, hjM, hj⟩ := hρ t ht
    refine ⟨h0, ?_⟩
    calc ρ t ≤ CI * ‖(R j).sqrt (y j)‖ := hj
      _ ≤ CI * B := mul_le_mul_of_nonneg_left (hbound j hjM) hCI
  exact derived_l2_curvature_bound (fun _ => B) ρ N hTX0 hCI hB0 (fun _ _ => le_refl B)
    (fun _ _ => hB0) hρ' hN hint hR

end RenewalGeometry
