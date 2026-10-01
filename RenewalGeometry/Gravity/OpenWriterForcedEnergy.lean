/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.OpenWriterLifespan

/-!
# The forced shifted energy of the open writer (`eq:supp-open-forced-energy`)

`cor:supp-open-lifespan`, second clause: if an acceleration defect `f_h` is added to the open
writer (`q_t = v`, `v_t = V_{0,h}(q, v) + f_h`), then on the same chart
`(𝓔_{s,h}^{1/2})' ≤ C_s 𝓔_{s,h}^{1/2} + C_s 𝓔_{s,h} + C_s ‖f_h‖_{s,h}`.

* `Fnorm r f`: the `H^r_h` norm of a ten-component force;
* `forcedRate`: the exact time derivative of the shifted energy along a forced history
  (`hasDerivAt_shiftedEnergy_forced`): the unforced rate plus `Σ_α ⟨v_α, a_α D^α f⟩_h`
  (`forcedRate_eq`);
* `forced_energy_inequality`: in the chart, `d𝓔/dt ≤ 2 𝓔^{1/2} (C 𝓔^{1/2} + C 𝓔 + C ‖f‖_{s,h})`
  and, where `𝓔 > 0`, `(𝓔^{1/2})' ≤ C 𝓔^{1/2} + C 𝓔 + C ‖f‖_{s,h}`
  (**`eq:supp-open-forced-energy`**), with `C` independent of the mesh.
-/

open Set Metric Filter Topology Finset
open scoped NNReal BigOperators

namespace RenewalGeometry.OpenWriterLifespan

open RootParityConnector OpenWriterGridBridge OpenWriterChart OpenWriterEnergy HarmonicWriter
  OpenWriterEnergyEstimate

noncomputable section

set_option linter.unusedSectionVars false

variable {N : ℕ} [NeZero N]

/-- The `H^r_h` norm `‖f‖_{r,h}` of a ten-component record array. -/
def Fnorm (r : ℕ) (f : Grid N → MetricRec) : ℝ :=
  Real.sqrt (∑ κ : Upper, PeriodicGridSobolev.sobSq r (cx (comp f κ.1.1 κ.1.2)))

theorem Fnorm_nonneg (r : ℕ) (f : Grid N → MetricRec) : 0 ≤ Fnorm r f := Real.sqrt_nonneg _

theorem sobNorm_le_Fnorm (r : ℕ) (f : Grid N → MetricRec) (κ : Upper) :
    PeriodicGridSobolev.sobNorm r (cx (comp f κ.1.1 κ.1.2)) ≤ Fnorm r f := by
  refine Real.sqrt_le_sqrt ?_
  exact single_le_sum (f := fun κ : Upper => PeriodicGridSobolev.sobSq r (cx (comp f κ.1.1 κ.1.2)))
    (fun _ _ => PeriodicGridSobolev.sobSq_nonneg _ _) (mem_univ κ)

/-- The rate of the shifted energy along a forced history. -/
def forcedRate (s : ℕ) (q v f : Grid N → MetricRec) : ℝ :=
  ∑ α ∈ PeriodicGridSobolev.multiIndices s, ((N : ℝ) ^ 3)⁻¹ * ∑ κ : Upper, ∑ x,
    ((1 / 2) * (DαR α (comp v κ.1.1 κ.1.2) x * (SαR α (adot q v) x * DαR α (comp v κ.1.1 κ.1.2) x)) +
      (1 / 2) * ∑ i, ∑ j, OpenWriterEnergy.Dp i (DαR α (comp q κ.1.1 κ.1.2)) x *
        (SαR α (cdot q v i j) x * OpenWriterEnergy.Dp j (DαR α (comp q κ.1.1 κ.1.2)) x) +
      DαR α (comp q κ.1.1 κ.1.2) x * DαR α (comp v κ.1.1 κ.1.2) x +
      DαR α (comp v κ.1.1 κ.1.2) x * (Rrow α q v κ.1.1 κ.1.2 x +
        SαR α (aArr q) x * DαR α (comp f κ.1.1 κ.1.2) x))

/-- The forcing contribution `Σ_α ⟨v_α, a_α D^α f⟩_h`. -/
def forcingTerm (s : ℕ) (q v f : Grid N → MetricRec) : ℝ :=
  ∑ α ∈ PeriodicGridSobolev.multiIndices s, ∑ κ : Upper, ((N : ℝ) ^ 3)⁻¹ * ∑ x,
    DαR α (comp v κ.1.1 κ.1.2) x * (SαR α (aArr q) x * DαR α (comp f κ.1.1 κ.1.2) x)

theorem forcedRate_eq (s : ℕ) (q v f : Grid N → MetricRec) :
    forcedRate s q v f = energyRate s q v + forcingTerm s q v f := by
  unfold forcedRate energyRate forcingTerm
  rw [← sum_add_distrib]
  refine sum_congr rfl fun α _ => ?_
  rw [← Finset.mul_sum (s := univ) (f := fun κ : Upper => ∑ x,
    DαR α (comp v κ.1.1 κ.1.2) x * (SαR α (aArr q) x * DαR α (comp f κ.1.1 κ.1.2) x)),
    ← mul_add, ← sum_add_distrib]
  congr 1
  refine sum_congr rfl fun κ _ => ?_
  rw [← sum_add_distrib]
  refine sum_congr rfl fun x _ => ?_
  ring

/-- **Exact energy identity along a forced history** `q_t = v`, `v_t = V_{0,h}(q, v) + f`. -/
theorem hasDerivAt_shiftedEnergy_forced (s : ℕ) (q v f : ℝ → Grid N → MetricRec) (t : ℝ)
    (hsym : IsSymRec (q t))
    (hq : ∀ x, HasDerivAt (fun τ => q τ x) (v t x) t)
    (hv : ∀ x (κ : Upper), HasDerivAt (fun τ => v τ x κ.1.1 κ.1.2)
      (harmonicWriterAcceleration (q t) (v t) x κ.1.1 κ.1.2 + f t x κ.1.1 κ.1.2) t)
    (hdA : ∀ x, DifferentiableAt ℝ harmA (minkowski + q t x))
    (hdC : ∀ x i j, DifferentiableAt ℝ (harmC i j) (minkowski + q t x)) :
    HasDerivAt (fun τ => shiftedEnergy s (q τ) (v τ)) (forcedRate s (q t) (v t) (f t)) t := by
  unfold shiftedEnergy forcedRate
  refine HasDerivAt.fun_sum fun α _ => ?_
  have hg : ∀ y, HasDerivAt (fun τ => minkowski + q τ y) (v t y) t := fun y =>
    (hq y).const_add minkowski
  have hcomp : ∀ (μ ν : Fin 4) x, HasDerivAt (fun τ => comp (q τ) μ ν x) (comp (v t) μ ν x) t := by
    intro μ ν x
    have h1 := hasDerivAt_pi.1 (hq x) μ
    exact hasDerivAt_pi.1 h1 ν
  refine hasDerivAt_energy (fun τ (κ : Upper) => DαR α (comp (q τ) κ.1.1 κ.1.2))
    (fun τ (κ : Upper) => DαR α (comp (v τ) κ.1.1 κ.1.2)) (fun τ => SαR α (aArr (q τ)))
    (fun τ i j => SαR α (cArr (q τ) i j)) (fun i => SαR α (bArr (q t) i))
    (fun κ => DαR α (comp (harmonicWriterAcceleration (q t) (v t)) κ.1.1 κ.1.2) +
      DαR α (comp (f t) κ.1.1 κ.1.2))
    (SαR α (adot (q t) (v t))) (fun i j => SαR α (cdot (q t) (v t) i j))
    (fun κ x => Rrow α (q t) (v t) κ.1.1 κ.1.2 x +
      SαR α (aArr (q t)) x * DαR α (comp (f t) κ.1.1 κ.1.2) x) t ?_ ?_ ?_ ?_ ?_ ?_
  · intro κ x
    exact hasDerivAt_DαR (fun y => hcomp κ.1.1 κ.1.2 y) α x
  · intro κ x
    have h := hasDerivAt_DαR (u := fun τ => comp (v τ) κ.1.1 κ.1.2)
      (u' := comp (harmonicWriterAcceleration (q t) (v t)) κ.1.1 κ.1.2 + comp (f t) κ.1.1 κ.1.2)
      (fun y => hv y κ) α x
    rw [DαR_add] at h
    exact h
  · intro x
    exact (hdA (x + svec α)).hasFDerivAt.comp_hasDerivAt t (hg (x + svec α))
  · intro i j x
    exact (hdC (x + svec α) i j).hasFDerivAt.comp_hasDerivAt t (hg (x + svec α))
  · intro i j x
    simp only [SαR, cArr]
    refine harmC_symm _ (fun μ ν => ?_) i j
    simp only [Pi.add_apply]
    rw [minkowski_symm, hsym]
  · intro κ x
    simp only [Rrow, Pi.add_apply]
    ring

/-- Pointwise multiplier bound in the grid `ℓ²` norm. -/
theorem gridNorm_cx_mul_le {a w : Grid N → ℝ} {K : ℝ} (hK : 0 ≤ K) (ha : ∀ x, |a x| ≤ K) :
    PeriodicGridSobolev.gridNorm (cx fun x => a x * w x) ≤
      K * PeriodicGridSobolev.gridNorm (cx w) := by
  unfold PeriodicGridSobolev.gridNorm
  rw [gridNormSq_cx, gridNormSq_cx, ← Real.sqrt_sq hK, ← Real.sqrt_mul (sq_nonneg K)]
  refine Real.sqrt_le_sqrt ?_
  have hN : (0 : ℝ) ≤ ((N : ℝ) ^ 3)⁻¹ := by positivity
  calc ((N : ℝ) ^ 3)⁻¹ * ∑ x, (a x * w x) ^ 2 ≤ ((N : ℝ) ^ 3)⁻¹ * ∑ x, K ^ 2 * w x ^ 2 := by
        refine mul_le_mul_of_nonneg_left (sum_le_sum fun x _ => ?_) hN
        rw [mul_pow]
        have h1 : a x ^ 2 ≤ K ^ 2 := by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (ha x) 2
        exact mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
    _ = K ^ 2 * (((N : ℝ) ^ 3)⁻¹ * ∑ x, w x ^ 2) := by rw [← mul_sum]; ring

/-- **`eq:supp-open-forced-energy`** (`cor:supp-open-lifespan`, second clause).  For every
`s ≥ 3` there are a chart radius `δ > 0` and `C ≥ 0`, independent of the mesh, such that along
every history solving the writer with an added acceleration defect `f`
(`q_t = v`, `v_t = V_{0,h}(q, v) + f` on the ten components, symmetric records) and lying at
time `t` in the chart `‖X‖_{X^s_h} ≤ δ`:
* `𝓔_{s,h}` is differentiable at `t` with derivative `forcedRate`, `¼ ‖X‖² ≤ 𝓔`;
* `d𝓔/dt ≤ 2 𝓔^{1/2} (C 𝓔^{1/2} + C 𝓔 + C ‖f‖_{s,h})`;
* if `𝓔 > 0` at `t`, then `𝓔^{1/2}` is differentiable at `t` and
  `(𝓔^{1/2})' ≤ C 𝓔^{1/2} + C 𝓔 + C ‖f‖_{s,h}`. -/
theorem forced_energy_inequality (s : ℕ) (hs : 3 ≤ s) :
    ∃ δ > 0, ∃ C ≥ 0, ∀ (N : ℕ) [NeZero N] (q v f : ℝ → Grid N → MetricRec) (t : ℝ),
      IsSymRec (q t) → IsSymRec (v t) →
      (∀ x, HasDerivAt (fun τ => q τ x) (v t x) t) →
      (∀ x (κ : Upper), HasDerivAt (fun τ => v τ x κ.1.1 κ.1.2)
        (harmonicWriterAcceleration (q t) (v t) x κ.1.1 κ.1.2 + f t x κ.1.1 κ.1.2) t) →
      Xnorm s (q t) (v t) ≤ δ →
      HasDerivAt (fun τ => shiftedEnergy s (q τ) (v τ)) (forcedRate s (q t) (v t) (f t)) t ∧
      Xsq s (q t) (v t) / 4 ≤ shiftedEnergy s (q t) (v t) ∧
      forcedRate s (q t) (v t) (f t) ≤ 2 * Real.sqrt (shiftedEnergy s (q t) (v t)) *
        (C * Real.sqrt (shiftedEnergy s (q t) (v t)) + C * shiftedEnergy s (q t) (v t) +
          C * Fnorm s (f t)) ∧
      (0 < shiftedEnergy s (q t) (v t) →
        HasDerivAt (fun τ => Real.sqrt (shiftedEnergy s (q τ) (v τ)))
          (forcedRate s (q t) (v t) (f t) / (2 * Real.sqrt (shiftedEnergy s (q t) (v t)))) t ∧
        forcedRate s (q t) (v t) (f t) / (2 * Real.sqrt (shiftedEnergy s (q t) (v t))) ≤
          C * Real.sqrt (shiftedEnergy s (q t) (v t)) + C * shiftedEnergy s (q t) (v t) +
            C * Fnorm s (f t)) := by
  obtain ⟨δ1, hδ1, K, hK, hstat⟩ := static_bounds s hs
  obtain ⟨ε, hε, M, hM, hchart⟩ := exists_chart
  have hL := supConst_nonneg
  set δ : ℝ := min δ1 (ε / (2 * (supConst + 1)))
  have hδ : 0 < δ := by positivity
  set cM : ℝ := ((PeriodicGridSobolev.multiIndices s).card : ℝ)
  set cU : ℝ := (Fintype.card Upper : ℝ)
  set C : ℝ := 2 * K + 4 * K + 3 / 2 * cM * cU
  refine ⟨δ, hδ, C, by positivity, fun N _ q v f t hqs hvs hq hv hX => ?_⟩
  have hX1 : Xnorm s (q t) (v t) ≤ δ1 := hX.trans (min_le_left _ _)
  obtain ⟨hdA, hdC, hlow, hrate⟩ := hstat N (q t) (v t) hqs hvs hX1
  have hd := hasDerivAt_shiftedEnergy_forced s q v f t hqs hq hv hdA hdC
  set E := shiftedEnergy s (q t) (v t)
  set X := Xnorm s (q t) (v t)
  have hX0 : 0 ≤ X := Xnorm_nonneg _ _ _
  have hXsq : Xsq s (q t) (v t) = X ^ 2 := (Xnorm_sq _ _ _).symm
  have hE0 : 0 ≤ E := le_trans (by rw [hXsq]; positivity) hlow
  have hX2 : X ^ 2 ≤ 4 * E := by rw [← hXsq]; linarith
  have hXs : X ≤ 2 * Real.sqrt E := by
    have : X = Real.sqrt (X ^ 2) := (Real.sqrt_sq hX0).symm
    rw [this, show 2 * Real.sqrt E = Real.sqrt (4 * E) by
      rw [Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]]
    exact Real.sqrt_le_sqrt hX2
  -- pointwise chart bound on `a`
  have hqy : ∀ y, ‖q t y‖ < ε := by
    intro y
    have h1 := norm_q_le s (by omega) hqs (v t) y
    have h2 : supConst * X ≤ supConst * (ε / (2 * (supConst + 1))) :=
      mul_le_mul_of_nonneg_left (hX.trans (min_le_right _ _)) hL
    have h3 : supConst * (ε / (2 * (supConst + 1))) < ε := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  have ha : ∀ y, |aArr (q t) y| ≤ 3 / 2 := fun y => by
    have := (hchart (minkowski + q t y) (by rw [add_sub_cancel_left]; exact hqy y)).1.2.2
    simp only [aArr]; rw [abs_le] at this ⊢; constructor <;> linarith
  -- the forcing term
  have hF : forcingTerm s (q t) (v t) (f t) ≤ 3 / 2 * cM * cU * X * Fnorm s (f t) := by
    unfold forcingTerm
    have hper : ∀ α ∈ PeriodicGridSobolev.multiIndices s, ∀ κ : Upper,
        ((N : ℝ) ^ 3)⁻¹ * ∑ x, DαR α (comp (v t) κ.1.1 κ.1.2) x *
          (SαR α (aArr (q t)) x * DαR α (comp (f t) κ.1.1 κ.1.2) x) ≤
        X * (3 / 2 * Fnorm s (f t)) := by
      intro α hα κ
      have hdeg := PeriodicGridSobolev.mem_multiIndices.mp hα
      refine (le_abs_self _).trans ((abs_inner_le _ _).trans ?_)
      refine mul_le_mul ?_ ?_ (PeriodicGridSobolev.gridNorm_nonneg _) hX0
      · exact (gridNorm_cx_DαR_le hdeg _).trans (sobNorm_v_le s (q t) hvs _ _ le_rfl)
      · refine (gridNorm_cx_mul_le (by norm_num) (fun x => ha (x + svec α))).trans ?_
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        exact (gridNorm_cx_DαR_le hdeg _).trans (sobNorm_le_Fnorm s (f t) κ)
    calc _ ≤ ∑ _α ∈ PeriodicGridSobolev.multiIndices s, ∑ _κ : Upper,
          X * (3 / 2 * Fnorm s (f t)) := sum_le_sum fun α hα => sum_le_sum fun κ _ => hper α hα κ
      _ = 3 / 2 * cM * cU * X * Fnorm s (f t) := by
          simp only [sum_const, card_univ, nsmul_eq_mul, cM, cU]; ring
  have hFn := Fnorm_nonneg s (f t)
  have hsE := Real.sqrt_nonneg E
  have hsq : Real.sqrt E ^ 2 = E := Real.sq_sqrt hE0
  have hmain : forcedRate s (q t) (v t) (f t) ≤ 2 * Real.sqrt E *
      (C * Real.sqrt E + C * E + C * Fnorm s (f t)) := by
    rw [forcedRate_eq]
    rw [hXsq] at hrate
    have h1 : K * X ^ 2 ≤ K * (4 * E) := mul_le_mul_of_nonneg_left hX2 hK
    have h2 : K * X ^ 3 ≤ K * (8 * (E * Real.sqrt E)) := by
      refine mul_le_mul_of_nonneg_left ?_ hK
      have h3 : X ^ 3 ≤ (2 * Real.sqrt E) ^ 3 := pow_le_pow_left₀ hX0 hXs 3
      have h4 : (2 * Real.sqrt E) ^ 3 = 8 * (Real.sqrt E ^ 2 * Real.sqrt E) := by ring
      rw [hsq] at h4
      linarith
    have h5 : 3 / 2 * cM * cU * X * Fnorm s (f t) ≤
        3 / 2 * cM * cU * (2 * Real.sqrt E) * Fnorm s (f t) := by
      have : 0 ≤ 3 / 2 * cM * cU := by positivity
      gcongr
    have hcMU : 0 ≤ cM * cU := by positivity
    have hEs : E * Real.sqrt E ≥ 0 := mul_nonneg hE0 hsE
    have hexp : 2 * Real.sqrt E * (C * Real.sqrt E + C * E + C * Fnorm s (f t)) =
        2 * C * E + 2 * C * (E * Real.sqrt E) + 2 * C * (Real.sqrt E * Fnorm s (f t)) := by
      have h := Real.mul_self_sqrt hE0
      linear_combination (2 * C) * h
    rw [hexp]
    have hC1 : 4 * K ≤ 2 * C := by simp only [C]; nlinarith
    have hC2 : 8 * K ≤ 2 * C := by simp only [C]; nlinarith
    have hC3 : 3 * (cM * cU) ≤ 2 * C := by simp only [C]; nlinarith
    have hsF : 0 ≤ Real.sqrt E * Fnorm s (f t) := mul_nonneg hsE hFn
    nlinarith
  refine ⟨hd, hlow, hmain, fun hpos => ?_⟩
  have hsqpos : 0 < Real.sqrt E := Real.sqrt_pos.mpr hpos
  refine ⟨?_, ?_⟩
  · have h := (Real.hasDerivAt_sqrt hpos.ne').comp t hd
    refine h.congr_deriv ?_
    rw [one_div, inv_mul_eq_div]
  · rw [div_le_iff₀ (by positivity)]
    linarith [hmain]

end

end RenewalGeometry.OpenWriterLifespan
