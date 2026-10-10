/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.EquivariantNativeBudgets

/-!
# Calculus of the continuum Euler–Lagrange covector on the periodic cube

Generic infrastructure (no renewal notions) for identifying the continuum Euler–Lagrange
covector `DiscreteEulerConsistency.contEuler L Y` of a first-order density `L(w, p)` on `ℝ⁴`
(used for bridge step P3 of `thm:native-closure`, Einstein–Standard-Model action-closure
manuscript).

* `contDiff_contEuler` — for a density smooth on an open set containing the first jets of a smooth
  field, the Euler covector is a smooth covector field;
* `eq_zero_of_integral_periodic` — **fundamental lemma on the periodic cube** for smooth periodic
  covector fields: if `∫_{[0,1]⁴} Y(z)(v(z)) dz = 0` for every smooth `ℤ⁴`-periodic test `v`, then
  `Y = 0`;
* `hasDerivAt_pd_shift` — the mixed-partial identity
  `∂_t|₀ ∂_μ[F(J + tK)] = ∂_μ[DF(J)K]` (symmetry of the second derivative of `F`);
* **`contEuler_eq_of_pointwise`** — if, for every smooth periodic test `v`, the first variation
  density `DL(J¹Y)(v, ∂v)` equals `X(z)(v(z))` plus the divergence of a `C¹` periodic flux, and
  `X` is a smooth periodic covector field, then `contEuler L Y = X`.
-/

namespace RenewalGeometry

namespace ContEulerCalc

open MeasureTheory Set Filter Topology
open DiscreteEulerConsistency (R4 evec jet1 contEuler)
open SobolevOpen (pd)
open PeriodicCube (IsZPeriodic)
open scoped ContDiff

noncomputable section

set_option linter.unusedSectionVars false

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-! ### Smoothness of the Euler covector -/

theorem contDiff_fderiv_jet1 {L : V × (Fin 4 → V) → ℝ} {U : Set (V × (Fin 4 → V))}
    (hU : IsOpen U) (hL : ContDiffOn ℝ ∞ L U) {Y : R4 → V} (hY : ContDiff ℝ ∞ Y)
    (hJU : ∀ y, jet1 Y y ∈ U) : ContDiff ℝ ∞ (fun z => fderiv ℝ L (jet1 Y z)) := by
  have hJ := ContEulerBounds.contDiff_jet1_infty hY
  have hDL : ContDiffOn ℝ ∞ (fderiv ℝ L) U := hL.fderiv_of_isOpen hU (by simp)
  exact hDL.comp_contDiff hJ hJU

/-- **The Euler covector of a smooth density along a smooth field is smooth.** -/
theorem contDiff_contEuler {L : V × (Fin 4 → V) → ℝ} {U : Set (V × (Fin 4 → V))}
    (hU : IsOpen U) (hL : ContDiffOn ℝ ∞ L U) {Y : R4 → V} (hY : ContDiff ℝ ∞ Y)
    (hJU : ∀ y, jet1 Y y ∈ U) : ContDiff ℝ ∞ (contEuler L Y) := by
  have hF := contDiff_fderiv_jet1 hU hL hY hJU
  have hG : ∀ μ : Fin 4, ContDiff ℝ ∞ (fun z' => (fderiv ℝ L (jet1 Y z')).comp
      ((ContinuousLinearMap.inr ℝ V (Fin 4 → V)).comp
        (ContinuousLinearMap.single ℝ (fun _ : Fin 4 => V) μ))) := fun μ =>
    hF.clm_comp contDiff_const
  unfold contEuler
  refine (hF.clm_comp contDiff_const).sub ?_
  refine ContDiff.sum fun μ _ => ?_
  exact ((hG μ).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

/-! ### The fundamental lemma on the periodic cube -/

/-- The open unit cube `(0,1)⁴`. -/
def openCube : Set R4 := Set.pi univ fun _ => Ioo (0 : ℝ) 1

theorem isOpen_openCube : IsOpen openCube := isOpen_set_pi finite_univ fun _ _ => isOpen_Ioo

theorem openCube_subset : openCube ⊆ Icc (0 : R4) 1 := by
  intro x hx
  refine ⟨fun i => (hx i (mem_univ i)).1.le, fun i => (hx i (mem_univ i)).2.le⟩

theorem fract_mem_closure_openCube (x : R4) :
    (fun i => Int.fract (x i)) ∈ closure openCube := by
  unfold openCube
  rw [closure_pi_set]
  intro i _
  rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
  exact ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩

/-- **The fundamental lemma of the calculus of variations on the periodic cube** for smooth
periodic covector fields. -/
theorem eq_zero_of_integral_periodic [FiniteDimensional ℝ V] {Y : R4 → V →L[ℝ] ℝ}
    (hY : ContDiff ℝ ∞ Y) (hper : IsZPeriodic Y)
    (h : ∀ v : R4 → V, ContDiff ℝ ∞ v → IsZPeriodic v → ∫ z in Icc (0 : R4) 1, Y z (v z) = 0) :
    Y = 0 := by
  set b := Module.finBasis ℝ V
  set v : R4 → V := fun z => ∑ i, Y z (b i) • b i with hv
  have hvs : ContDiff ℝ ∞ v :=
    ContDiff.sum fun i _ => (hY.clm_apply contDiff_const).smul contDiff_const
  have hvp : IsZPeriodic v := fun k x => by simp only [hv, hper k x]
  have hYv : ∀ z, Y z (v z) = ∑ i, (Y z (b i)) ^ 2 := fun z => by
    simp only [hv, map_sum, map_smul, smul_eq_mul, sq]
  set f : R4 → ℝ := fun z => ∑ i, (Y z (b i)) ^ 2 with hf
  have hfc : Continuous f :=
    continuous_finsetSum _ fun i _ => ((hY.continuous.clm_apply continuous_const).pow 2)
  have hf0 : 0 ≤ f := fun z => Finset.sum_nonneg fun i _ => sq_nonneg _
  have hint : ∫ z in Icc (0 : R4) 1, f z = 0 := by
    rw [← h v hvs hvp]
    exact integral_congr_ae (Eventually.of_forall fun z => (hYv z).symm)
  have hae : f =ᵐ[volume.restrict (Icc (0 : R4) 1)] 0 :=
    (integral_eq_zero_iff_of_nonneg hf0
      (PeriodicCube.integrableOn_cube_of_continuousOn hfc.continuousOn)).1 hint
  have hae' : f =ᵐ[volume.restrict openCube] 0 := ae_restrict_of_ae_restrict_of_subset
    openCube_subset hae
  have hEq : EqOn f 0 openCube := Measure.eqOn_open_of_ae_eq hae' isOpen_openCube
    hfc.continuousOn continuousOn_const
  have hEqc : EqOn f 0 (closure openCube) := hEq.closure hfc continuous_const
  have hfz : ∀ z, f z = 0 := by
    intro z
    have hfp : IsZPeriodic f := fun k x => by simp only [hf, hper k x]
    rw [← hfp.apply_fract z]
    exact hEqc (fract_mem_closure_openCube z)
  ext z w
  have hcoord : ∀ i, Y z (b i) = 0 := by
    intro i
    have h1 := hfz z
    have h2 : (Y z (b i)) ^ 2 ≤ f z :=
      Finset.single_le_sum (f := fun i => (Y z (b i)) ^ 2) (fun j _ => sq_nonneg _)
        (Finset.mem_univ i)
    rw [h1] at h2
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (le_antisymm h2 (sq_nonneg _))
  have hYz : Y z = 0 := by
    refine ContinuousLinearMap.coe_injective (b.ext fun i => ?_)
    simp [hcoord i]
  simp [hYz]

/-! ### Mixed partial derivatives along a shifted family -/

/-- **Mixed partials**: for `F` smooth on an open set containing `J(z)`,
`∂_t|_{t=0} ∂_μ[F(J + tK)](z) = ∂_μ[DF(J)K](z)`. -/
theorem hasDerivAt_pd_shift {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] {F : P → ℝ}
    {U : Set P} (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) {J K : R4 → P} (hJ : ContDiff ℝ ∞ J)
    (hK : ContDiff ℝ ∞ K) {z : R4} (hz : J z ∈ U) (μ : Fin 4) :
    HasDerivAt (fun t : ℝ => pd (fun y => F (J y + t • K y)) μ z)
      (pd (fun y => fderiv ℝ F (J y) (K y)) μ z) 0 := by
  have hJd : Differentiable ℝ J := hJ.differentiable (by simp)
  have hKd : Differentiable ℝ K := hK.differentiable (by simp)
  have hFd : ∀ p ∈ U, DifferentiableAt ℝ F p := fun p hp =>
    (hF.contDiffAt (hU.mem_nhds hp)).differentiableAt (by simp)
  have hDF : ContDiffOn ℝ ∞ (fderiv ℝ F) U := hF.fderiv_of_isOpen hU (by simp)
  have hDFd : DifferentiableAt ℝ (fderiv ℝ F) (J z) :=
    (hDF.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)
  set J' := fderiv ℝ J z (evec μ)
  set K' := fderiv ℝ K z (evec μ)
  -- the curve `t ↦ J z + t K z` stays in `U` near `0`
  have hc : HasDerivAt (fun t : ℝ => J z + t • K z) (K z) 0 :=
    (((hasDerivAt_id (0 : ℝ)).smul_const (K z)).const_add (J z)).congr_deriv (one_smul _ _)
  have hevU : ∀ᶠ t in 𝓝 (0 : ℝ), J z + t • K z ∈ U :=
    hc.continuousAt.preimage_mem_nhds (by simpa using hU.mem_nhds hz)
  -- the partial derivative for fixed `t`
  have hpd_t : ∀ᶠ t in 𝓝 (0 : ℝ), pd (fun y => F (J y + t • K y)) μ z =
      fderiv ℝ F (J z + t • K z) (J' + t • K') := by
    filter_upwards [hevU] with t ht
    have hin : HasFDerivAt (fun y => J y + t • K y) (fderiv ℝ J z + t • fderiv ℝ K z) z :=
      (hJd z).hasFDerivAt.add ((hKd z).hasFDerivAt.const_smul t)
    have := ((hFd _ ht).hasFDerivAt.comp z hin).fderiv
    unfold SobolevOpen.pd
    rw [show (fun y => F (J y + t • K y)) = F ∘ fun y => J y + t • K y from rfl, this]
    rfl
  -- its `t`-derivative
  have hA : HasDerivAt (fun t : ℝ => fderiv ℝ F (J z + t • K z))
      (fderiv ℝ (fderiv ℝ F) (J z) (K z)) 0 :=
    hDFd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hc (by simp)
  have hd : HasDerivAt (fun t : ℝ => J' + t • K') K' 0 :=
    (((hasDerivAt_id (0 : ℝ)).smul_const K').const_add J').congr_deriv (one_smul _ _)
  have hf := hA.clm_apply hd
  simp only [zero_smul, add_zero] at hf
  -- the partial derivative of `DF(J)K`
  have hpdR : pd (fun y => fderiv ℝ F (J y) (K y)) μ z =
      fderiv ℝ (fderiv ℝ F) (J z) J' (K z) + fderiv ℝ F (J z) K' := by
    have h1 : HasFDerivAt (fun y => fderiv ℝ F (J y)) ((fderiv ℝ (fderiv ℝ F) (J z)).comp
        (fderiv ℝ J z)) z := hDFd.hasFDerivAt.comp z (hJd z).hasFDerivAt
    have h2 := h1.clm_apply (hKd z).hasFDerivAt
    unfold SobolevOpen.pd
    rw [h2.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply]
    rw [add_comm]
    rfl
  have hF2 : ContDiffAt ℝ 2 F (J z) := (hF.contDiffAt (hU.mem_nhds hz)).of_le (by norm_cast)
  have hsymm := hF2.isSymmSndFDerivAt (by simp)
  rw [hpdR, hsymm J' (K z)]
  exact (hf.congr_of_eventuallyEq (hpd_t.mono fun t ht => ht)).congr_deriv (by rw [add_comm])

/-- Smoothness of `y ↦ DF(J(y))K(y)` for `F` smooth on an open set containing the values of `J`. -/
theorem contDiff_fderiv_apply {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] {F : P → ℝ}
    {U : Set P} (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) {J K : R4 → P} (hJ : ContDiff ℝ ∞ J)
    (hK : ContDiff ℝ ∞ K) (hJU : ∀ y, J y ∈ U) :
    ContDiff ℝ ∞ (fun y => fderiv ℝ F (J y) (K y)) := by
  have hDF : ContDiffOn ℝ ∞ (fderiv ℝ F) U := hF.fderiv_of_isOpen hU (by simp)
  exact (hDF.comp_contDiff hJ hJU).clm_apply hK

/-! ### Identification of the Euler covector from a pointwise variation formula -/

/-- **Identification of the Euler covector.**  Let `L` be smooth on an open set `U` containing the
first jets of a smooth `ℤ⁴`-periodic field `Y`, and `X` a smooth periodic covector field.  If for
every smooth periodic test `v` the first-variation density is `X(z)(v(z))` plus the divergence of
a `C¹` periodic flux, then `contEuler L Y = X`. -/
theorem contEuler_eq_of_pointwise [FiniteDimensional ℝ V] {L : V × (Fin 4 → V) → ℝ}
    {U : Set (V × (Fin 4 → V))} (hU : IsOpen U) (hL : ContDiffOn ℝ ∞ L U) {Y : R4 → V}
    (hY : ContDiff ℝ ∞ Y) (hYp : IsZPeriodic Y) (hJU : ∀ y, jet1 Y y ∈ U)
    {X : R4 → V →L[ℝ] ℝ} (hX : ContDiff ℝ ∞ X) (hXp : IsZPeriodic X)
    (hvar : ∀ v : R4 → V, ContDiff ℝ ∞ v → IsZPeriodic v → ∃ B : Fin 4 → R4 → ℝ,
      (∀ μ, ContDiff ℝ 1 (B μ)) ∧ (∀ μ, IsZPeriodic (B μ)) ∧
      ∀ z, fderiv ℝ L (jet1 Y z) (v z, fun μ => fderiv ℝ v z (evec μ)) =
        X z (v z) + ∑ μ, pd (B μ) μ z) :
    contEuler L Y = X := by
  have hE := contDiff_contEuler hU hL hY hJU
  have hEp : IsZPeriodic (contEuler L Y) := by
    have hJp : IsZPeriodic (jet1 Y) := fun k x => by
      simp only [jet1, hYp k x, hYp.fderiv k x]
    have hDp : ∀ k x, fderiv ℝ L (jet1 Y (x + PeriodicCube.zvec k)) = fderiv ℝ L (jet1 Y x) :=
      fun k x => by rw [hJp k x]
    intro k x
    unfold contEuler
    congr 1
    · rw [hDp k x]
    · refine Finset.sum_congr rfl fun μ _ => ?_
      have hG : IsZPeriodic (fun z' => (fderiv ℝ L (jet1 Y z')).comp
          ((ContinuousLinearMap.inr ℝ V (Fin 4 → V)).comp
            (ContinuousLinearMap.single ℝ (fun _ : Fin 4 => V) μ))) := fun k x => by
        show (fderiv ℝ L (jet1 Y (x + PeriodicCube.zvec k))).comp _ = (fderiv ℝ L (jet1 Y x)).comp _
        rw [hDp k x]
      rw [hG.fderiv k x]
  have hD : contEuler L Y - X = 0 := by
    refine eq_zero_of_integral_periodic (hE.sub hX) (fun k x => by
      simp only [Pi.sub_apply, hEp k x, hXp k x]) fun v hv hvp => ?_
    obtain ⟨B, hBc, hBp, hB⟩ := hvar v hv hvp
    have hv1 : ContDiff ℝ 1 v := hv.of_le (by simp)
    have hIBP := EquivariantBudgets.contVar_eq_integral_contEuler hU
      (hL.of_le (by norm_cast)) (hY.of_le (by norm_cast)) hJU hv1 hYp hvp
    have hc1 : Continuous fun z => X z (v z) :=
      hX.continuous.clm_apply hv.continuous
    have hc2 : ∀ μ, Continuous (pd (B μ) μ) := fun μ =>
      ((hBc μ).continuous_fderiv (by norm_num)).clm_apply continuous_const
    have hcE : Continuous fun z => contEuler L Y z (v z) :=
      hE.continuous.clm_apply hv.continuous
    have hcont : ∫ z in Icc (0 : R4) 1, contEuler L Y z (v z) =
        ∫ z in Icc (0 : R4) 1, X z (v z) := by
      rw [← hIBP]
      unfold EquivariantBudgets.contVar
      simp only [hB]
      rw [integral_add (PeriodicCube.integrableOn_cube_of_continuousOn hc1.continuousOn)
        (PeriodicCube.integrableOn_cube_of_continuousOn
          (continuous_finsetSum _ fun μ _ => hc2 μ).continuousOn),
        integral_finsetSum _ fun μ _ =>
          PeriodicCube.integrableOn_cube_of_continuousOn (hc2 μ).continuousOn]
      simp [PeriodicCube.integral_pd_eq_zero (hBc _) (hBp _)]
    simp only [ContinuousLinearMap.sub_apply, Pi.sub_apply]
    rw [integral_sub (PeriodicCube.integrableOn_cube_of_continuousOn hcE.continuousOn)
      (PeriodicCube.integrableOn_cube_of_continuousOn hc1.continuousOn), hcont, sub_self]
  exact sub_eq_zero.1 hD

end

end ContEulerCalc

end RenewalGeometry
