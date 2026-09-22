/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.Gravity.RelationalSchedulerADM

/-!
# The complete finite ADM frame: uniqueness of the inversion
  (`thm:supp-adm-frame`, emergent-spacetime manuscript)

`relational_scheduler_ADM` (Gravity/RelationalSchedulerADM.lean) proves that
the six root dyadics are a basis of `Sym₃` (rate sums ↦ `𝓑_h`), that the
rate-difference map has rank three onto `ℝ³` with the three-dimensional
tetrahedral circulation kernel, and that the boxed inversion formula
`eq:adm-inversion-main` *solves* `𝓑 = N² g⁻¹`, `ϱ = √det g`.  This file adds
the missing clause of `thm:supp-adm-frame`:

* `RenewalGeometry.adm_inversion_unique` — for `𝓑` with `det 𝓑 > 0` and
  `ϱ > 0`, every solution `(N, g)` with `N > 0`, `det g > 0` of
  `𝓑 = N² g⁻¹`, `ϱ = √det g` is the boxed one
  `N = ϱ^{1/3}(det 𝓑)^{1/6}`, `g = ϱ^{2/3}(det 𝓑)^{1/3}𝓑⁻¹`;
* `RenewalGeometry.adm_frame_complete` — the bundled theorem: (A1) basis,
  (A2) rank/kernel, existence and uniqueness of the inversion. -/

open Matrix Module

namespace RenewalGeometry

/-- **Theorem `thm:supp-adm-frame`, uniqueness clause**: the boxed ADM
inversion `eq:adm-inversion-main` is the *unique* positive solution of
`𝓑 = N² g⁻¹`, `ϱ = √det g`.  Taking determinants gives `N⁶ = ϱ² det 𝓑`,
positivity fixes `N`, and substituting back gives `g = N² 𝓑⁻¹`. -/
theorem adm_inversion_unique (B g : Matrix (Fin 3) (Fin 3) ℝ) (ϱ N : ℝ)
    (hϱ : 0 < ϱ) (hB : 0 < B.det) (hN : 0 < N) (hg : 0 < g.det)
    (hBN : B = (N ^ 2) • g⁻¹) (hϱg : ϱ = Real.sqrt g.det) :
    N = ϱ ^ ((1 : ℝ) / 3) * B.det ^ ((1 : ℝ) / 6)
    ∧ g = (ϱ ^ ((2 : ℝ) / 3) * B.det ^ ((1 : ℝ) / 3)) • B⁻¹ := by
  have hgu : IsUnit g.det := isUnit_iff_ne_zero.mpr (ne_of_gt hg)
  -- `det g = ϱ²`
  have hdetg : g.det = ϱ ^ 2 := by
    rw [hϱg, Real.sq_sqrt (le_of_lt hg)]
  -- `det 𝓑 = N⁶ / ϱ²`
  have hdetB : B.det = N ^ 6 * (ϱ ^ 2)⁻¹ := by
    rw [hBN, Matrix.det_smul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv,
      hdetg]
    simp only [Fintype.card_fin]
    ring
  have hN6 : N ^ 6 = ϱ ^ 2 * B.det := by
    rw [hdetB]
    field_simp
  -- the boxed lapse has the same sixth power
  set c : ℝ := ϱ ^ ((1 : ℝ) / 3) * B.det ^ ((1 : ℝ) / 6) with hc
  have hcpos : 0 < c := by
    rw [hc]
    positivity
  have hc6 : c ^ 6 = ϱ ^ 2 * B.det := by
    have ha : ((1 : ℝ) / 3) * ((6 : ℕ) : ℝ) = ((2 : ℕ) : ℝ) := by norm_num
    have hb : ((1 : ℝ) / 6) * ((6 : ℕ) : ℝ) = ((1 : ℕ) : ℝ) := by norm_num
    rw [hc, mul_pow,
      ← Real.rpow_natCast (ϱ ^ ((1 : ℝ) / 3)) 6,
      ← Real.rpow_natCast (B.det ^ ((1 : ℝ) / 6)) 6,
      ← Real.rpow_mul (le_of_lt hϱ),
      ← Real.rpow_mul (le_of_lt hB), ha, hb,
      Real.rpow_natCast, Real.rpow_natCast]
    norm_num
  have hNc : N = c := by
    have h6 : N ^ 6 = c ^ 6 := by rw [hN6, hc6]
    exact (pow_left_inj₀ (le_of_lt hN) (le_of_lt hcpos)
      (by norm_num : (6 : ℕ) ≠ 0)).mp h6
  refine ⟨hNc, ?_⟩
  -- `𝓑⁻¹ = N⁻² g`, hence `g = N² 𝓑⁻¹`
  have hN2 : (N ^ 2 : ℝ) ≠ 0 := pow_ne_zero 2 (ne_of_gt hN)
  have hBinv : B⁻¹ = (N ^ 2)⁻¹ • g := by
    apply Matrix.inv_eq_right_inv
    rw [hBN, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      mul_inv_cancel₀ hN2, Matrix.nonsing_inv_mul g hgu, one_smul]
  -- `N² = ϱ^{2/3}(det 𝓑)^{1/3}`
  have hN2c : N ^ 2 = ϱ ^ ((2 : ℝ) / 3) * B.det ^ ((1 : ℝ) / 3) := by
    have ha : ((1 : ℝ) / 3) * ((2 : ℕ) : ℝ) = (2 : ℝ) / 3 := by norm_num
    have hb : ((1 : ℝ) / 6) * ((2 : ℕ) : ℝ) = (1 : ℝ) / 3 := by norm_num
    rw [hNc, hc, mul_pow,
      ← Real.rpow_natCast (ϱ ^ ((1 : ℝ) / 3)) 2,
      ← Real.rpow_natCast (B.det ^ ((1 : ℝ) / 6)) 2,
      ← Real.rpow_mul (le_of_lt hϱ),
      ← Real.rpow_mul (le_of_lt hB), ha, hb]
  rw [← hN2c, hBinv, smul_smul, mul_inv_cancel₀ hN2, one_smul]

/-- **Theorem `thm:supp-adm-frame`**: the six rate sums map isomorphically
onto `Sym₃` (A1), the six rate differences map with rank three onto `ℝ³`
with the three-dimensional tetrahedral circulation kernel (A2), and for
every `𝓑 ≻ 0` (here: `det 𝓑 > 0`) and `ϱ > 0` the boxed formula
`eq:adm-inversion-main` is the unique positive solution of
`𝓑 = N² g⁻¹`, `ϱ = √det g` (existence and uniqueness).  Hence root rates,
waiting-time scale and speed density reconstruct the six spatial metric
components, the three shift components and the lapse. -/
theorem adm_frame_complete :
    -- (A1) the six root dyadics are a basis of `Sym₃`
    (∀ S : Matrix (Fin 3) (Fin 3) ℝ, S.IsSymm →
      ∃! c : Fin 6 → ℝ,
        (∑ a, c a • vecMulVec (a3SchedulerRoot a)
          (a3SchedulerRoot a)) = S)
    -- (A2) rank three onto the shift, three-dimensional circulation kernel
    ∧ (LinearMap.range a3ShiftMap = ⊤
        ∧ LinearMap.ker a3ShiftMap
          = Submodule.span ℝ (Set.range a3Cycle)
        ∧ finrank ℝ (LinearMap.ker a3ShiftMap) = 3)
    -- existence: the boxed formula solves the characterization
    ∧ (∀ (B : Matrix (Fin 3) (Fin 3) ℝ) (ϱ : ℝ),
        0 < ϱ → 0 < B.det →
        (Real.sqrt (((ϱ ^ ((2 : ℝ)/3)
            * B.det ^ ((1 : ℝ)/3)) • B⁻¹).det) = ϱ
        ∧ ((ϱ ^ ((1 : ℝ)/3) * B.det ^ ((1 : ℝ)/6)) ^ 2)
            • ((ϱ ^ ((2 : ℝ)/3)
              * B.det ^ ((1 : ℝ)/3)) • B⁻¹)⁻¹ = B))
    -- uniqueness: every positive solution is the boxed one
    ∧ (∀ (B g : Matrix (Fin 3) (Fin 3) ℝ) (ϱ N : ℝ),
        0 < ϱ → 0 < B.det → 0 < N → 0 < g.det →
        B = (N ^ 2) • g⁻¹ → ϱ = Real.sqrt g.det →
        N = ϱ ^ ((1 : ℝ) / 3) * B.det ^ ((1 : ℝ) / 6)
        ∧ g = (ϱ ^ ((2 : ℝ) / 3) * B.det ^ ((1 : ℝ) / 3)) • B⁻¹) := by
  obtain ⟨h1, h2, _, _, h4, _⟩ := relational_scheduler_ADM
  exact ⟨h1, h2, h4, fun B g ϱ N hϱ hB hN hg hBN hϱg =>
    adm_inversion_unique B g ϱ N hϱ hB hN hg hBN hϱg⟩

end RenewalGeometry
-- AXIOMCHECK
#print axioms RenewalGeometry.adm_frame_complete
#print axioms RenewalGeometry.adm_inversion_unique
