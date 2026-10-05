/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Action.NativeEulerConsistency
import RenewalGeometry.Analysis.PeriodicCubeCalculus
import RenewalGeometry.Analysis.LipschitzRiemannSumError
import RenewalGeometry.Continuum.ContEulerDerivativeBounds
import RenewalGeometry.Continuum.NativeTailTransferBounds
import RenewalGeometry.Continuum.NativeLinkCovectorNorm
import RenewalGeometry.Continuum.DeterminantResolvedExtraction

/-!
# The consistency budget of the equivariant native first variation
  (`prop:equivariant-native-budgets`, `eq:eq-native-consistency`; Einstein–SM action closure)

Generic part (any first-order density `L(w, p)` on a normed field space `V`, the unit periodic
box `[0,1]⁴`, the grid `(ℤ/n)⁴` of mesh `h = 1/n`):

* `fderiv_eq_sum_eulerRow`: the derivative of a lattice action is the nodal pairing with its raw
  Euler rows, `DA(y)[w] = h⁴ Σ_x E_h(y)(x)(w(x))`.
* `contVar` (the continuum first variation `D𝒮(Y)[v] = ∫ DL(J¹Y)(v, ∂v)`) and
  `contVar_eq_integral_contEuler` (**continuum integration by parts**: for `ℤ⁴`-periodic `C²`
  fields, `C¹` tests and a `C²` density, `D𝒮(Y)[v] = ∫_{[0,1]⁴} E₀(Y)(v)`).
* `cellAvg` (the cell-average test lift `Q_h v(x) = h⁻⁴ ∫_{C_x} v`, the covariant average of
  `lem:covariant-quadrature` for the flat comparison connection), `sum_norm_cellAvg_le`
  (Jensen: `h⁴ Σ_x ‖Q_h v(x)‖ ≤ ‖v‖_{L¹}`) and `abs_quadrature_sub_le` (**cell quadrature for a
  Lipschitz covector field**: `|h⁴ Σ_x X(x)(Q_h v(x)) - ∫ X(v)| ≤ L h ‖v‖_{L¹}`).
-/

open MeasureTheory Set Filter Topology Finset
open scoped BigOperators ContDiff

noncomputable section

namespace RenewalGeometry.EquivariantBudgets

open DiscreteEulerConsistency (R4 evec jet1 contEuler eulerRow pos)
open ShiftedJetAction (Grid)
open UnitCubeRiemannSum (cell gridPoint)

set_option linter.unusedSectionVars false

/-! ### The lattice nodes as cube grid points -/

section Index

variable {n : ℕ} [NeZero n]

/-- The node `x ∈ (ℤ/n)⁴` of a cube index `k ∈ {0, …, n-1}⁴`. -/
def gidx (k : Fin 4 → Fin n) : Grid n := fun μ => ((k μ : ℕ) : ZMod n)

theorem val_gidx (k : Fin 4 → Fin n) (μ : Fin 4) : (gidx k μ).val = k μ := by
  simp only [gidx, ZMod.val_natCast]
  exact Nat.mod_eq_of_lt (k μ).2

theorem gidx_bijective : Function.Bijective (gidx (n := n)) := by
  constructor
  · intro k k' hk
    funext μ
    have := congrArg (fun x : Grid n => (x μ).val) hk
    simp only [val_gidx] at this
    exact Fin.ext this
  · intro x
    refine ⟨fun μ => ⟨(x μ).val, ZMod.val_lt _⟩, ?_⟩
    funext μ
    simp [gidx]

theorem pos_gidx (k : Fin 4 → Fin n) : pos ((n : ℝ)⁻¹) (gidx k) = gridPoint n k := by
  funext μ
  simp only [pos, gridPoint, val_gidx]
  ring

theorem sum_grid_eq {M : Type*} [AddCommMonoid M] (f : Grid n → M) :
    ∑ x, f x = ∑ k : Fin 4 → Fin n, f (gidx k) :=
  (Fintype.sum_bijective _ gidx_bijective _ _ fun _ => rfl).symm

end Index

/-! ### The derivative of a lattice action -/

section Action

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {n : ℕ} [NeZero n]

/-- **The derivative of a lattice action is the nodal pairing with its raw Euler rows**:
`DA(y)[w] = h⁴ Σ_x E_h(y)(x)(w(x))`. -/
theorem fderiv_eq_sum_eulerRow (A : (Grid n → V) → ℝ) {h : ℝ} (hh : h ≠ 0) (y w : Grid n → V) :
    fderiv ℝ A y w = h ^ 4 * ∑ x, eulerRow A h y x (w x) := by
  have hw : w = ∑ x, Pi.single x (w x) := (Finset.univ_sum_single w).symm
  conv_lhs => rw [hw]
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [eulerRow, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.single_apply, smul_eq_mul]
  rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 4 hh), one_mul]

end Action

/-! ### The cell average and the quadrature -/

section Quadrature

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
variable {n : ℕ} [NeZero n]

/-- **The cell-average test lift** `Q_h v(x_k) = h⁻⁴ ∫_{C_k} v` (`eq:covariant-test-average` for
the flat comparison connection), `h = 1/n`. -/
def cellAvg (n : ℕ) (v : R4 → V) (k : Fin 4 → Fin n) : V := ((n : ℝ) ^ 4) • ∫ y in cell n k, v y

/-- The cell-average lift as a nodal field on `(ℤ/n)⁴`. -/
def cellLift (n : ℕ) [NeZero n] (v : R4 → V) : Grid n → V :=
  fun x => cellAvg n v (fun μ => ⟨(x μ).val, ZMod.val_lt _⟩)

theorem cellLift_gidx (v : R4 → V) (k : Fin 4 → Fin n) : cellLift n v (gidx k) = cellAvg n v k := by
  unfold cellLift
  congr 1
  funext μ
  exact Fin.ext (val_gidx k μ)

theorem npos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)

/-- `h⁴ X(Q_h v(x_k)) = ∫_{C_k} X(v)`. -/
theorem cellVol_mul_apply_cellAvg (X : V →L[ℝ] ℝ) {v : R4 → V} (k : Fin 4 → Fin n)
    (hv : IntegrableOn v (cell n k)) :
    ((n : ℝ)⁻¹) ^ 4 * X (cellAvg n v k) = ∫ y in cell n k, X (v y) := by
  rw [cellAvg, map_smul, smul_eq_mul, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ npos.ne', one_pow,
    one_mul, ← X.integral_comp_comm hv]

/-- **Jensen**: `‖Q_h v(x_k)‖ ≤ h⁻⁴ ∫_{C_k} ‖v‖`. -/
theorem norm_cellAvg_le {v : R4 → V} (k : Fin 4 → Fin n) :
    ((n : ℝ)⁻¹) ^ 4 * ‖cellAvg n v k‖ ≤ ∫ y in cell n k, ‖v y‖ := by
  rw [cellAvg, norm_smul, Real.norm_of_nonneg (by positivity), ← mul_assoc, ← mul_pow,
    inv_mul_cancel₀ npos.ne', one_pow, one_mul]
  exact norm_integral_le_integral_norm _

/-- **Jensen, summed**: `h⁴ Σ_x ‖Q_h v(x)‖ ≤ ‖v‖_{L¹([0,1]⁴)}`. -/
theorem sum_norm_cellAvg_le {v : R4 → V} (hv : IntegrableOn v (Icc (0 : R4) 1)) :
    ((n : ℝ)⁻¹) ^ 4 * ∑ k : Fin 4 → Fin n, ‖cellAvg n v k‖ ≤ ∫ y in Icc (0 : R4) 1, ‖v y‖ := by
  rw [LipschitzRiemannSum.setIntegral_Icc_eq_sum_cell_of_integrableOn
    (Nat.pos_of_ne_zero (NeZero.ne n)) _ hv.norm, Finset.mul_sum]
  exact Finset.sum_le_sum fun k _ => norm_cellAvg_le k

/-- **Cell quadrature for a Lipschitz covector field**: if `‖X(y) - X(z)‖ ≤ L ‖y - z‖` on the
cube, then `|h⁴ Σ_k X(x_k)(Q_h v(x_k)) - ∫_{[0,1]⁴} X(y)(v(y)) dy| ≤ L h ‖v‖_{L¹}`. -/
theorem abs_quadrature_sub_le {X : R4 → V →L[ℝ] ℝ} {L : ℝ} (hL0 : 0 ≤ L)
    (hX : ∀ y ∈ Icc (0 : R4) 1, ∀ z ∈ Icc (0 : R4) 1, ‖X y - X z‖ ≤ L * ‖y - z‖)
    {v : R4 → V} (hv : IntegrableOn v (Icc (0 : R4) 1)) :
    |((n : ℝ)⁻¹) ^ 4 * ∑ k : Fin 4 → Fin n, X (gridPoint n k) (cellAvg n v k) -
        ∫ y in Icc (0 : R4) 1, X y (v y)| ≤ L * (n : ℝ)⁻¹ * ∫ y in Icc (0 : R4) 1, ‖v y‖ := by
  have hn0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hcont : ContinuousOn X (Icc (0 : R4) 1) := by
    intro y hy
    refine Metric.continuousWithinAt_iff.2 fun ε hε => ⟨ε / (L + 1), by positivity, fun z hz hd => ?_⟩
    rw [dist_eq_norm] at hd ⊢
    calc ‖X z - X y‖ ≤ L * ‖z - y‖ := hX z hz y hy
      _ ≤ (L + 1) * ‖z - y‖ := by nlinarith [norm_nonneg (z - y)]
      _ < (L + 1) * (ε / (L + 1)) := by gcongr
      _ = ε := by field_simp
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : R4)) (b := 1)).exists_bound_of_continuousOn hcont
  have hXv : IntegrableOn (fun y => X y (v y)) (Icc (0 : R4) 1) := by
    refine Integrable.mono' (hv.norm.const_mul C) ?_ ?_
    · exact isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable₂
        (hcont.aestronglyMeasurable measurableSet_Icc) hv.aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun y hy => ?_)
      exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (hC y hy) (norm_nonneg _))
  have hvk : ∀ k : Fin 4 → Fin n, IntegrableOn v (cell n k) := fun k =>
    hv.mono_set (UnitCubeRiemannSum.cell_subset_Icc hn0 k)
  rw [Finset.mul_sum, LipschitzRiemannSum.setIntegral_Icc_eq_sum_cell_of_integrableOn hn0 _ hXv,
    LipschitzRiemannSum.setIntegral_Icc_eq_sum_cell_of_integrableOn hn0 _ hv.norm,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [cellVol_mul_apply_cellAvg _ k (hvk k),
    ← integral_sub ((X (gridPoint n k)).integrable_comp (hvk k))
      (hXv.mono_set (UnitCubeRiemannSum.cell_subset_Icc hn0 k)), ← Real.norm_eq_abs,
    ← integral_const_mul]
  refine norm_integral_le_of_norm_le (((hvk k).norm).const_mul _) ?_
  refine (ae_restrict_iff' (UnitCubeRiemannSum.measurableSet_cell n k)).2
    (Eventually.of_forall fun y hy => ?_)
  have hyc := UnitCubeRiemannSum.cell_subset_Icc hn0 k hy
  have hd := UnitCubeRiemannSum.dist_lt_of_mem_cell hn0 k hy
  rw [dist_eq_norm] at hd
  have h1 : ‖X (gridPoint n k) - X y‖ ≤ L * (n : ℝ)⁻¹ := by
    refine (hX _ (UnitCubeRiemannSum.gridPoint_mem_Icc hn0 k) y hyc).trans ?_
    rw [norm_sub_rev, ← one_div]
    exact mul_le_mul_of_nonneg_left hd.le hL0
  calc ‖X (gridPoint n k) (v y) - X y (v y)‖ = ‖(X (gridPoint n k) - X y) (v y)‖ := rfl
    _ ≤ ‖X (gridPoint n k) - X y‖ * ‖v y‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ L * (n : ℝ)⁻¹ * ‖v y‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)

end Quadrature

/-! ### The continuum first variation and integration by parts -/

section IBP

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **The continuum first variation** of `𝒮(Y) = ∫_{[0,1]⁴} L(J¹Y)` along a test `v`:
`D𝒮(Y)[v] = ∫ DL(J¹Y)(v, ∂v)`. -/
def contVar (L : V × (Fin 4 → V) → ℝ) (Y v : R4 → V) : ℝ :=
  ∫ y in Icc (0 : R4) 1, fderiv ℝ L (jet1 Y y) (v y, fun μ => fderiv ℝ v y (evec μ))

/-- The momentum covector `P_μ(z) = ∂_{p_μ} L(J¹Y(z))`. -/
def momentum (L : V × (Fin 4 → V) → ℝ) (Y : R4 → V) (μ : Fin 4) (z : R4) : V →L[ℝ] ℝ :=
  (fderiv ℝ L (jet1 Y z)).comp ((ContinuousLinearMap.inr ℝ V (Fin 4 → V)).comp
    (ContinuousLinearMap.single ℝ (fun _ : Fin 4 => V) μ))

theorem pair_decomp (T : V × (Fin 4 → V) →L[ℝ] ℝ) (a : V) (p : Fin 4 → V) :
    T (a, p) = T (ContinuousLinearMap.inl ℝ V (Fin 4 → V) a) +
      ∑ μ, T (ContinuousLinearMap.inr ℝ V (Fin 4 → V) (Pi.single μ (p μ))) := by
  rw [← map_sum, ← map_add]
  congr 1
  refine Prod.ext ?_ ?_
  · simp [Prod.fst_sum]
  · simp only [Prod.snd_add, ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply,
      Prod.snd_sum, zero_add]
    exact (Finset.univ_sum_single p).symm

theorem contDiff_fderiv_jet {L : V × (Fin 4 → V) → ℝ} {U : Set (V × (Fin 4 → V))} (hU : IsOpen U)
    (hL : ContDiffOn ℝ 2 L U) {Y : R4 → V} (hY : ContDiff ℝ 2 Y) (hJU : ∀ y, jet1 Y y ∈ U) :
    ContDiff ℝ 1 (fun y => fderiv ℝ L (jet1 Y y)) := by
  have hJ : ContDiff ℝ 1 (jet1 Y) := ContEulerBounds.contDiff_jet1 (n := 1) (hY.of_le (by norm_num))
  have hDL : ContDiffOn ℝ 1 (fderiv ℝ L) U := hL.fderiv_of_isOpen hU (by norm_num)
  exact hDL.comp_contDiff hJ hJU

theorem contDiff_momentum {L : V × (Fin 4 → V) → ℝ} {U : Set (V × (Fin 4 → V))} (hU : IsOpen U)
    (hL : ContDiffOn ℝ 2 L U) {Y : R4 → V} (hY : ContDiff ℝ 2 Y) (hJU : ∀ y, jet1 Y y ∈ U)
    (μ : Fin 4) : ContDiff ℝ 1 (momentum L Y μ) :=
  ((ContinuousLinearMap.compL ℝ (V) (V × (Fin 4 → V)) ℝ).flip
    ((ContinuousLinearMap.inr ℝ V (Fin 4 → V)).comp
      (ContinuousLinearMap.single ℝ (fun _ : Fin 4 => V) μ))).contDiff.comp
    (contDiff_fderiv_jet hU hL hY hJU)

/-- **Continuum integration by parts** (`D𝒮(Y)[v] = ∫ 𝓔₀(Y)(v)`): for a density `L` that is `C²`
on an open set containing the first jets of a `C²` `ℤ⁴`-periodic field `Y`, and a `C¹`
`ℤ⁴`-periodic test `v`, the first variation of the continuum action over the unit periodic box
is the pairing with the continuum Euler–Lagrange expression. -/
theorem contVar_eq_integral_contEuler {L : V × (Fin 4 → V) → ℝ} {U : Set (V × (Fin 4 → V))}
    (hU : IsOpen U) (hL : ContDiffOn ℝ 2 L U)
    {Y v : R4 → V} (hY : ContDiff ℝ 2 Y) (hJU : ∀ y, jet1 Y y ∈ U) (hv : ContDiff ℝ 1 v)
    (hYp : PeriodicCube.IsZPeriodic Y) (hvp : PeriodicCube.IsZPeriodic v) :
    contVar L Y v = ∫ y in Icc (0 : R4) 1, contEuler L Y y (v y) := by
  have hDLJ := contDiff_fderiv_jet hU hL hY hJU
  have hP := fun μ => contDiff_momentum hU hL hY hJU μ
  have hdv : Continuous (fderiv ℝ v) := hv.continuous_fderiv (by norm_num)
  -- the boundary terms `g_μ = P_μ(v)`
  set g : Fin 4 → R4 → ℝ := fun μ z => momentum L Y μ z (v z) with hg
  have hgC : ∀ μ, ContDiff ℝ 1 (g μ) := fun μ => (hP μ).clm_apply hv
  have hJp : PeriodicCube.IsZPeriodic (jet1 Y) := fun k x => by
    simp only [jet1, hYp k x, hYp.fderiv k x]
  have hgp : ∀ μ, PeriodicCube.IsZPeriodic (g μ) := fun μ k x => by
    simp only [hg, momentum, hJp k x, hvp k x]
  have hpd : ∀ μ z, SobolevOpen.pd (g μ) μ z =
      fderiv ℝ (momentum L Y μ) z (evec μ) (v z) + momentum L Y μ z (fderiv ℝ v z (evec μ)) := by
    intro μ z
    have h1 : HasFDerivAt (g μ) ((momentum L Y μ z).comp (fderiv ℝ v z) +
        (fderiv ℝ (momentum L Y μ) z).flip (v z)) z :=
      ((hP μ).differentiable (by norm_num) z).hasFDerivAt.clm_apply
        ((hv.differentiable (by norm_num) z).hasFDerivAt)
    unfold SobolevOpen.pd
    rw [h1.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.flip_apply, evec]
    ring
  have hint : ∀ μ, ∫ z in Icc (0 : R4) 1, SobolevOpen.pd (g μ) μ z = 0 := fun μ =>
    PeriodicCube.integral_pd_eq_zero (hgC μ) (hgp μ) μ
  -- the pointwise identity
  have hpt : ∀ z, fderiv ℝ L (jet1 Y z) (v z, fun μ => fderiv ℝ v z (evec μ)) =
      contEuler L Y z (v z) + ∑ μ, SobolevOpen.pd (g μ) μ z := by
    intro z
    have hm : ∀ μ, momentum L Y μ = fun z' => (fderiv ℝ L (jet1 Y z')).comp
        ((ContinuousLinearMap.inr ℝ V (Fin 4 → V)).comp
          (ContinuousLinearMap.single ℝ (fun _ : Fin 4 => V) μ)) := fun μ => rfl
    rw [pair_decomp]
    simp only [contEuler, hpd, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.coe_sum', Finset.sum_apply, Finset.sum_add_distrib, hm]
    simp only [ContinuousLinearMap.single_apply, ContinuousLinearMap.comp_apply]
    abel
  -- integrability
  have hc1 : Continuous fun z => contEuler L Y z (v z) := by
    have : Continuous (contEuler L Y) := by
      unfold contEuler
      refine hDLJ.continuous.clm_comp continuous_const |>.sub ?_
      refine continuous_finset_sum _ fun μ _ => ?_
      exact (ContinuousLinearMap.apply ℝ _ (evec μ)).continuous.comp
        ((hP μ).continuous_fderiv (by norm_num))
    exact isBoundedBilinearMap_apply.continuous.comp (this.prodMk hv.continuous)
  have hc2 : ∀ μ, Continuous (SobolevOpen.pd (g μ) μ) := fun μ =>
    ((hgC μ).continuous_fderiv (by norm_num)).clm_apply continuous_const
  unfold contVar
  simp only [hpt]
  rw [integral_add (PeriodicCube.integrableOn_cube_of_continuousOn hc1.continuousOn)
    (PeriodicCube.integrableOn_cube_of_continuousOn (continuous_finset_sum _ fun μ _ =>
      hc2 μ).continuousOn), integral_finset_sum _ fun μ _ =>
      PeriodicCube.integrableOn_cube_of_continuousOn (hc2 μ).continuousOn]
  simp [hint]

end IBP

/-! ### The native Einstein–Standard-Model action -/

section Native

open NativeScaling (Mat)
open NativeDensity
open DiscreteEulerConsistency (limDensity samp IsPeriodic)
open ContEulerBounds (JS jetP eulerOp)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
  [FiniteDimensional ℝ 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
  [FiniteDimensional ℝ 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
  [FiniteDimensional ℝ 𝓢]
variable (D : Data 𝔄 𝓗 𝓢)

/-- The continuum Einstein–Standard-Model Lagrangian `L₀ = F^{(1)}_0` of the unchanged local
action (`NativeEulerConsistency`, all four sectors). -/
abbrev L0 : Field 𝔄 𝓗 𝓢 × (Fin 4 → Field 𝔄 𝓗 𝓢) → ℝ :=
  limDensity (ι := Shift) (firstJetDensity D)

/-- **`eq:eq-euler-jets` (the `𝔻𝓔₀` bound), in Lipschitz form**: under the growing-band bounds
`‖D^j Y‖ ≤ B K^j` (`j ≤ 3`), coframes in a compact oriented chart and `|Y| ≤ A`, the continuum
Euler covector is `C K³`-Lipschitz: `‖𝓔₀(Y)(x) - 𝓔₀(Y)(x')‖ ≤ C K³ ‖x - x'‖`, with `C`
independent of `K` and `Y`. -/
theorem native_euler_lipschitz {Ke : Set Mat} (hKe : IsCompact Ke) (hdet : ∀ e ∈ Ke, 0 < e.det)
    (A B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ K : ℝ, 1 ≤ K → ∀ Y : R4 → Field 𝔄 𝓗 𝓢, ContDiff ℝ ∞ Y →
      (∀ z, (Y z).1 ∈ Ke) → (∀ z, ‖Y z‖ ≤ A) →
      (∀ z, ‖iteratedFDeriv ℝ 1 Y z‖ ≤ B * K) → (∀ z, ‖iteratedFDeriv ℝ 2 Y z‖ ≤ B * K ^ 2) →
      (∀ z, ‖iteratedFDeriv ℝ 3 Y z‖ ≤ B * K ^ 3) →
      ∀ x x', ‖contEuler (L0 D) Y x - contEuler (L0 D) Y x'‖ ≤ C * K ^ 3 * ‖x - x'‖ := by
  set Bp := max B 0 with hBp
  have hBp0 : 0 ≤ Bp := le_max_right _ _
  set B' := max 1 (5 * Bp) with hB'
  have hB'1 : 1 ≤ B' := le_max_left _ _
  obtain ⟨δ, hδ, M, hM0, hsU, -, hbd, -⟩ := NativeTail.exists_native_constants D hKe hdet A Bp 2
  refine ⟨ContEulerBounds.cE 1 * M * B' ^ (1 + 1), by
    have := ContEulerBounds.cE_nonneg 1; positivity, ?_⟩
  intro K hK Y hY hYe hYA h1 h2 h3 x x'
  have hK0 : 0 < K := lt_of_lt_of_le one_pos hK
  set Yt := NativeTail.resc K Y with hYt
  have hYts : ContDiff ℝ ∞ Yt := hY.comp (contDiff_const_smul K⁻¹)
  -- unit-band bounds of the rescaled field
  have hbnd : ∀ j : ℕ, (∀ z, ‖iteratedFDeriv ℝ j Y z‖ ≤ B * K ^ j) →
      ∀ ξ, ‖iteratedFDeriv ℝ j Yt ξ‖ ≤ Bp := by
    intro j hj ξ
    refine (NativeTail.norm_iteratedFDeriv_comp_smul_le hY K⁻¹ j ξ).trans ?_
    rw [abs_of_pos (inv_pos.2 hK0), inv_pow]
    calc (K ^ j)⁻¹ * ‖iteratedFDeriv ℝ j Y (K⁻¹ • ξ)‖ ≤ (K ^ j)⁻¹ * (B * K ^ j) :=
          mul_le_mul_of_nonneg_left (hj _) (by positivity)
      _ = B := by field_simp
      _ ≤ Bp := le_max_left _ _
  have hb1 := hbnd 1 (fun z => by rw [pow_one]; exact h1 z)
  have hb2 := hbnd 2 h2
  have hb3 := hbnd 3 h3
  -- the normalised jets lie in the compact jet set
  have hmem : ∀ ξ, jetP K⁻¹ Yt ξ ∈ NativeTail.jetSet (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢) Ke A Bp := by
    intro ξ
    refine ⟨⟨inv_nonneg.mpr hK0.le, inv_le_one_of_one_le₀ hK⟩, ⟨hYe _, ?_⟩, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right]; exact hYA _
    · rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hBp0]
      intro μ
      have h2' := (iteratedFDeriv ℝ 1 Yt ξ).le_opNorm (fun _ => evec μ)
      rw [iteratedFDeriv_one_apply] at h2'
      simp only [DiscreteEulerConsistency.norm_evec, Finset.prod_const_one, mul_one] at h2'
      exact h2'.trans (hb1 ξ)
  have hthick : ∀ ξ, jetP K⁻¹ Yt ξ ∈ Metric.cthickening δ
      (NativeTail.jetSet (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢) Ke A Bp) := fun ξ =>
    Metric.self_subset_cthickening _ (hmem ξ)
  have hch : ∀ ξ, ((K⁻¹, jet1 Yt ξ) : ℝ × JS (Field 𝔄 𝓗 𝓢)) ∈ NativeTail.chartU :=
    fun ξ => hsU (hthick ξ)
  -- the derivative bound of the normalised Euler operator
  have hD : ∀ ξ, ‖fderiv ℝ (eulerOp (NativeTail.Gd D) K⁻¹ Yt) ξ‖ ≤
      ContEulerBounds.cE 1 * M * B' ^ (1 + 1) := by
    intro ξ
    rw [← norm_iteratedFDeriv_one]
    refine ContEulerBounds.norm_iteratedFDeriv_eulerOp_le (n := 1) NativeTail.isOpen_chartU
      ((NativeTail.contDiffOn_Gd D).of_le (ContEulerBounds.natCast_le_infty _))
      (hYts.of_le (ContEulerBounds.natCast_le_infty _)) hch
      (fun k hk => (hbd _ (hthick ξ) k (by omega)).1) hB'1 ?_
    intro p hp1 hp2
    have hJ := ContEulerBounds.norm_iteratedFDeriv_jet1_le (p := p)
      (hYts.of_le (ContEulerBounds.natCast_le_infty _)) ξ
    have hp : p = 1 ∨ p = 2 := by omega
    rcases hp with rfl | rfl
    · have : ‖iteratedFDeriv ℝ 1 Yt ξ‖ + 4 * ‖iteratedFDeriv ℝ (1 + 1) Yt ξ‖ ≤ 5 * Bp := by
        have := hb2 ξ; have := hb1 ξ; linarith
      exact hJ.trans (this.trans (le_max_right _ _))
    · have : ‖iteratedFDeriv ℝ 2 Yt ξ‖ + 4 * ‖iteratedFDeriv ℝ (2 + 1) Yt ξ‖ ≤ 5 * Bp := by
        have := hb2 ξ; have := hb3 ξ; linarith
      exact hJ.trans (this.trans (le_max_right _ _))
  have hdiff : Differentiable ℝ (eulerOp (NativeTail.Gd D) K⁻¹ Yt) :=
    (ContEulerBounds.contDiff_eulerOp (NativeTail.contDiffOn_Gd D) hYts hch).differentiable
      (by simp)
  have hmvt := convex_univ.norm_image_sub_le_of_norm_fderiv_le (fun z _ => hdiff z)
    (fun z _ => hD z) (Set.mem_univ (K • x')) (Set.mem_univ (K • x))
  -- the native scaling `𝓔₀(Y)(x) = K² E_ν(Ỹ)(K x)`
  have hsc : ∀ z, contEuler (L0 D) Y z = K ^ 2 • eulerOp (NativeTail.Gd D) K⁻¹ Yt (K • z) :=
    fun z => NativeTail.Rfull_scale D hK0.ne' Y hch z
  rw [hsc x, hsc x', ← smul_sub, norm_smul, Real.norm_of_nonneg (by positivity)]
  rw [← smul_sub, norm_smul, Real.norm_of_nonneg hK0.le] at hmvt
  calc K ^ 2 * ‖eulerOp (NativeTail.Gd D) K⁻¹ Yt (K • x) - eulerOp (NativeTail.Gd D) K⁻¹ Yt (K • x')‖
      ≤ K ^ 2 * (ContEulerBounds.cE 1 * M * B' ^ (1 + 1) * (K * ‖x - x'‖)) :=
        mul_le_mul_of_nonneg_left hmvt (by positivity)
    _ = ContEulerBounds.cE 1 * M * B' ^ (1 + 1) * K ^ 3 * ‖x - x'‖ := by ring

/-- The continuum Lagrangian is the normalised density at `ν = 1`. -/
theorem L0_eq_Ldens (wp : Field 𝔄 𝓗 𝓢 × (Fin 4 → Field 𝔄 𝓗 𝓢)) :
    L0 D wp = NativeTail.Ldens D (1, wp) := by
  have h := NativeEulerConsistency.limDensity_eq_scaled D (one_ne_zero) wp
  rw [one_pow, one_mul] at h
  rw [L0, h]
  have e : DiscreteEulerConsistency.scalePE (Field 𝔄 𝓗 𝓢) (one_ne_zero (α := ℝ)) wp = wp := by
    rw [DiscreteEulerConsistency.scalePE_apply]
    simp
  rw [e, inv_one]
  rfl

/-- `L₀` is smooth on the oriented chart `det e ≠ 0`. -/
theorem contDiffOn_L0 :
    ContDiffOn ℝ ∞ (L0 D) {wp : Field 𝔄 𝓗 𝓢 × (Fin 4 → Field 𝔄 𝓗 𝓢) | wp.1.1.det ≠ 0} := by
  have h : (L0 D) = (NativeTail.Ldens D) ∘ fun wp => ((1 : ℝ), wp) := by
    funext wp; exact L0_eq_Ldens D wp
  rw [h]
  exact (NativeTail.contDiffOn_Ldens D).comp (contDiff_const.prodMk contDiff_id).contDiffOn
    fun wp hwp => hwp

theorem isOpen_chartL0 :
    IsOpen {wp : Field 𝔄 𝓗 𝓢 × (Fin 4 → Field 𝔄 𝓗 𝓢) | wp.1.1.det ≠ 0} :=
  isOpen_ne_fun (Continuous.matrix_det (continuous_fst.comp continuous_fst)) continuous_const

theorem isPeriodic_one_of_isZPeriodic {W : Type*} {Y : R4 → W} (hY : PeriodicCube.IsZPeriodic Y) :
    IsPeriodic 1 Y := by
  intro z μ
  have h := hY (Pi.single μ 1) z
  have e : PeriodicCube.zvec (Pi.single μ (1 : ℤ)) = (Pi.single μ (1 : ℝ) : R4) := by
    funext i
    by_cases hi : i = μ
    · subst hi; simp [PeriodicCube.zvec]
    · simp [PeriodicCube.zvec, Pi.single_apply, hi]
  rw [e] at h
  exact h

set_option maxHeartbeats 1600000 in
-- the assembly elaborates large field-space terms
/-- **`prop:equivariant-native-budgets`, consistency clause `eq:eq-native-consistency`** (unit
periodic box `[0,1]⁴`, grid `(ℤ/n)⁴`, mesh `h = 1/n`; flat comparison connection, so that the
covariant cell-average lift is the plain cell average `𝓘_h^cov ṽ = Q_h ṽ`, `cellLift`).  For a
compact oriented coframe chart `K_e`, an amplitude bound `A` and a band constant `B`, there are
`C` and `c_res > 0` such that for every `K ≥ 1` and `n` with `hK ≤ c_res`, every smooth
`ℤ⁴`-periodic field tuple `Y` with coframes in `K_e`, `|Y| ≤ A` and the growing-band bounds
`‖D^j Y‖ ≤ B K^j` (`j ≤ 3`; `eq:eq-growing-band`), and every `C¹` periodic physical-coordinate
test `ṽ`:
`|D S_h^{loc}(𝖲_h Y)[Q_h ṽ] - D𝒮(Y)[ṽ]| ≤ C h K³ ‖ṽ‖_{L¹}`,
where `D𝒮(Y)[ṽ] = ∫ DL₀(J¹Y)(ṽ, ∂ṽ)` is the first variation of the continuum
Einstein–Standard-Model action (`contVar`).  The proof is the manuscript's: the pointwise
`O(hK³)` Euler-row consistency (`NativeEulerConsistency.native_consistency`) paired with the
averaged test (Jensen), the cell quadrature against `X = 𝓔₀(Y)` with `‖𝔻𝓔₀‖ ≤ C K³`
(`native_euler_lipschitz`), and continuum integration by parts
(`contVar_eq_integral_contEuler`). -/
theorem native_consistency_budget {Ke : Set Mat} (hKe : IsCompact Ke)
    (hdet : ∀ e ∈ Ke, 0 < e.det) (A B : ℝ) :
    ∃ C c_res : ℝ, 0 ≤ C ∧ 0 < c_res ∧ ∀ K : ℝ, 1 ≤ K → ∀ (n : ℕ) [NeZero n],
      (n : ℝ)⁻¹ * K ≤ c_res →
      ∀ Y : R4 → Field 𝔄 𝓗 𝓢, ContDiff ℝ ∞ Y → PeriodicCube.IsZPeriodic Y →
      (∀ z, (Y z).1 ∈ Ke) → (∀ z, ‖Y z‖ ≤ A) →
      (∀ z, ‖iteratedFDeriv ℝ 1 Y z‖ ≤ B * K) → (∀ z, ‖iteratedFDeriv ℝ 2 Y z‖ ≤ B * K ^ 2) →
      (∀ z, ‖iteratedFDeriv ℝ 3 Y z‖ ≤ B * K ^ 3) →
      ∀ v : R4 → Field 𝔄 𝓗 𝓢, ContDiff ℝ 1 v → PeriodicCube.IsZPeriodic v →
      |fderiv ℝ (localAction D (n : ℝ)⁻¹) (samp (n : ℝ)⁻¹ Y : Grid n → Field 𝔄 𝓗 𝓢)
          (cellLift n v) - contVar (L0 D) Y v| ≤
        C * (n : ℝ)⁻¹ * K ^ 3 * ∫ y in Icc (0 : R4) 1, ‖v y‖ := by
  obtain ⟨C₁, c_res, hc, hcons⟩ := NativeEulerConsistency.native_consistency D hKe hdet A B
  obtain ⟨C₂, hC₂, hlip⟩ := native_euler_lipschitz D hKe hdet A B
  refine ⟨max C₁ 0 + C₂, c_res, by positivity, hc, ?_⟩
  intro K hK n _ hnK Y hY hYp hYe hYA h1 h2 h3 v hv hvp
  have hK0 : 0 < K := lt_of_lt_of_le one_pos hK
  set h : ℝ := (n : ℝ)⁻¹ with hh
  have hpos : 0 < h := inv_pos.2 npos
  have hper : IsPeriodic ((n : ℝ) * h) Y := by
    rw [hh, mul_inv_cancel₀ npos.ne']; exact isPeriodic_one_of_isZPeriodic hYp
  obtain ⟨-, -, hnode⟩ := hcons K hK h hpos hnK n Y (hY.of_le (ContEulerBounds.natCast_le_infty 3)) hper hYe
    hYA h1 h2 h3
  -- the two sides as pairings
  have hvi := PeriodicCube.integrableOn_cube_of_continuousOn (ι := Fin 4) hv.continuous.continuousOn
  have hJU : ∀ y, jet1 Y y ∈ {wp : Field 𝔄 𝓗 𝓢 × (Fin 4 → Field 𝔄 𝓗 𝓢) | wp.1.1.det ≠ 0} :=
    fun y => (hdet _ (hYe y)).ne'
  have hU := isOpen_chartL0 (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢)
  have hL2 := (contDiffOn_L0 D).of_le (ContEulerBounds.natCast_le_infty 2)
  have hY2 := hY.of_le (ContEulerBounds.natCast_le_infty 2)
  have hIBP := contVar_eq_integral_contEuler hU hL2 hY2 hJU hv hYp hvp
  have hF := fderiv_eq_sum_eulerRow (localAction D h) hpos.ne' (samp h Y : Grid n → Field 𝔄 𝓗 𝓢)
    (cellLift n v)
  have hF' : fderiv ℝ (localAction D h) (samp h Y : Grid n → Field 𝔄 𝓗 𝓢) (cellLift n v) =
      h ^ 4 * ∑ x, eulerRow (localAction D h) h (samp h Y : Grid n → Field 𝔄 𝓗 𝓢) x
        (cellLift n v x) := hF
  rw [hIBP, hF', sum_grid_eq]
  simp only [cellLift_gidx]
  set E₀ := contEuler (L0 D) Y with hE₀
  set Eh := eulerRow (localAction D h) h (samp h Y : Grid n → Field 𝔄 𝓗 𝓢) with hEh
  have e : h ^ 4 * ∑ k : Fin 4 → Fin n, Eh (gidx k) (cellAvg n v k) -
      ∫ y in Icc (0 : R4) 1, E₀ y (v y) =
      h ^ 4 * ∑ k : Fin 4 → Fin n, (Eh (gidx k) - E₀ (gridPoint n k)) (cellAvg n v k) +
        (h ^ 4 * ∑ k : Fin 4 → Fin n, E₀ (gridPoint n k) (cellAvg n v k) -
          ∫ y in Icc (0 : R4) 1, E₀ y (v y)) := by
    simp only [ContinuousLinearMap.sub_apply, Finset.sum_sub_distrib, mul_sub]
    ring
  rw [e]
  have hL1 : 0 ≤ ∫ y in Icc (0 : R4) 1, ‖v y‖ := integral_nonneg fun _ => norm_nonneg _
  -- the pointwise consistency term
  have hT1 : |h ^ 4 * ∑ k : Fin 4 → Fin n, (Eh (gidx k) - E₀ (gridPoint n k)) (cellAvg n v k)| ≤
      max C₁ 0 * h * K ^ 3 * ∫ y in Icc (0 : R4) 1, ‖v y‖ := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    calc h ^ 4 * |∑ k : Fin 4 → Fin n, (Eh (gidx k) - E₀ (gridPoint n k)) (cellAvg n v k)|
        ≤ h ^ 4 * ∑ k : Fin 4 → Fin n, (max C₁ 0 * h * K ^ 3) * ‖cellAvg n v k‖ := by
          refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun k _ => ?_)) (by positivity)
          rw [← Real.norm_eq_abs]
          refine (ContinuousLinearMap.le_opNorm _ _).trans
            (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
          have := hnode (gidx k)
          rw [pos_gidx] at this
          exact this.trans (by gcongr; exact le_max_left _ _)
      _ = max C₁ 0 * h * K ^ 3 * (h ^ 4 * ∑ k : Fin 4 → Fin n, ‖cellAvg n v k‖) := by
          rw [← Finset.mul_sum]; ring
      _ ≤ max C₁ 0 * h * K ^ 3 * ∫ y in Icc (0 : R4) 1, ‖v y‖ :=
          mul_le_mul_of_nonneg_left (by rw [hh]; exact sum_norm_cellAvg_le hvi) (by positivity)
  -- the quadrature term
  have hT2 : |h ^ 4 * ∑ k : Fin 4 → Fin n, E₀ (gridPoint n k) (cellAvg n v k) -
      ∫ y in Icc (0 : R4) 1, E₀ y (v y)| ≤ C₂ * K ^ 3 * h * ∫ y in Icc (0 : R4) 1, ‖v y‖ :=
    abs_quadrature_sub_le (X := E₀) (by positivity)
      (fun y _ z _ => hlip K hK Y hY hYe hYA h1 h2 h3 y z) hvi
  calc |h ^ 4 * ∑ k : Fin 4 → Fin n, (Eh (gidx k) - E₀ (gridPoint n k)) (cellAvg n v k) +
        (h ^ 4 * ∑ k : Fin 4 → Fin n, E₀ (gridPoint n k) (cellAvg n v k) -
          ∫ y in Icc (0 : R4) 1, E₀ y (v y))|
      ≤ (max C₁ 0 * h * K ^ 3 * ∫ y in Icc (0 : R4) 1, ‖v y‖) +
          C₂ * K ^ 3 * h * ∫ y in Icc (0 : R4) 1, ‖v y‖ :=
        (abs_add_le _ _).trans (add_le_add hT1 hT2)
    _ = (max C₁ 0 + C₂) * h * K ^ 3 * ∫ y in Icc (0 : R4) 1, ‖v y‖ := by ring

end Native

/-! ### The physical test lift, the equivariant test size and the two budgets -/

section Paper

open NativeScaling (Mat)
open NativeDensity
open DiscreteEulerConsistency (limDensity samp IsPeriodic)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
  [Nontrivial 𝔄] [FiniteDimensional ℝ 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
  [FiniteDimensional ℝ 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
  [FiniteDimensional ℝ 𝓢]

/-- The supremum of `‖f‖` over the unit periodic box. -/
def supN {E : Type*} [NormedAddCommGroup E] (f : R4 → E) : ℝ :=
  sSup ((fun y => ‖f y‖) '' Icc (0 : R4) 1)

/-- The `L²` norm over the unit periodic box. -/
def l2N {E : Type*} [NormedAddCommGroup E] (f : R4 → E) : ℝ :=
  (eLpNorm f 2 (volume.restrict (Icc (0 : R4) 1))).toReal

theorem supN_nonneg {E : Type*} [NormedAddCommGroup E] (f : R4 → E) : 0 ≤ supN f :=
  Real.sSup_nonneg fun _ ⟨_, _, hr⟩ => hr ▸ norm_nonneg _

theorem le_supN {E : Type*} [NormedAddCommGroup E] {f : R4 → E} (hf : Continuous f) {y : R4}
    (hy : y ∈ Icc (0 : R4) 1) : ‖f y‖ ≤ supN f := by
  refine le_csSup ?_ ⟨y, hy, rfl⟩
  exact (isCompact_Icc.image (continuous_norm.comp hf)).bddAbove

/-- **The physical coframe lift** `ṽ_z = (ė, a, η_H, η_Ψ, η_Ψ̄)` of a physical test
`v = (k, a, η_H, η_Ψ, η_Ψ̄)`: the symmetric coframe variation `ė = -½ e k g(e)`
(`NativeGravityFirstJet.liftM`, `eq:metric-lift`) and the unchanged gauge and matter components. -/
def liftTest (Y v : R4 → Field 𝔄 𝓗 𝓢) : R4 → Field 𝔄 𝓗 𝓢 :=
  fun y => (NativeGravityFirstJet.liftM (Y y).1 (v y).1, (v y).2)

/-- **The covariant cell-average physical test lift** `𝓘_h^cov v = Q_h ṽ_z` (flat comparison
connection on the coordinate bundles). -/
def Icov (n : ℕ) [NeZero n] (Y v : R4 → Field 𝔄 𝓗 𝓢) : Grid n → Field 𝔄 𝓗 𝓢 :=
  cellLift n (liftTest Y v)

/-- The gauge covariant derivative `(D_A a)_{μν} = ∂_μ a_ν + [A_μ, a_ν]`. -/
def covA (Y v : R4 → Field 𝔄 𝓗 𝓢) (y : R4) : Fin 4 → Fin 4 → 𝔄 := fun μ ν =>
  fderiv ℝ (fun y => (v y).2.1 ν) y (evec μ) +
    ((Y y).2.1 μ * (v y).2.1 ν - (v y).2.1 ν * (Y y).2.1 μ)

/-- `(D_A η_H)_μ = ∂_μ η_H + ρ_H(A_μ) η_H`. -/
def covH (D : Data 𝔄 𝓗 𝓢) (Y v : R4 → Field 𝔄 𝓗 𝓢) (y : R4) : Fin 4 → 𝓗 := fun μ =>
  fderiv ℝ (fun y => (v y).2.2.1) y (evec μ) + D.ρHL ((Y y).2.1 μ) (v y).2.2.1

/-- `(∇^{ref,A} η_Ψ)_μ = ∂_μ η_Ψ + ρ_S(A_μ) η_Ψ` (`eq:reference-gauge-spin-derivative`, with the
flat reference connection of the fixed comparison geometry). -/
def covS (D : Data 𝔄 𝓗 𝓢) (Y v : R4 → Field 𝔄 𝓗 𝓢) (y : R4) : Fin 4 → 𝓢 := fun μ =>
  fderiv ℝ (fun y => (v y).2.2.2.1) y (evec μ) + D.ρSL ((Y y).2.1 μ) (v y).2.2.2.1

/-- `(∇^{ref,A} η_Ψ̄)_μ = ∂_μ η_Ψ̄ - η_Ψ̄ ρ_S(A_μ)`. -/
def covSb (D : Data 𝔄 𝓗 𝓢) (Y v : R4 → Field 𝔄 𝓗 𝓢) (y : R4) : Fin 4 → CoSpinor 𝓢 := fun μ =>
  fderiv ℝ (fun y => (v y).2.2.2.2) y (evec μ) - ((v y).2.2.2.2).comp (D.ρSL ((Y y).2.1 μ))

/-- **The equivariant test size** `𝔫_z(v)` (`eq:equivariant-test-size`) on the unit periodic
box: `‖k‖_{W^{1,∞}} + ‖a‖_∞ + ‖D_A a‖_2 + ‖η_H‖_∞ + ‖D_A η_H‖_2 + ‖η_Ψ‖_∞ + ‖∇^{ref,A}η_Ψ‖_2 +
‖η_Ψ̄‖_∞ + ‖∇^{ref,A}η_Ψ̄‖_2`. -/
def testSize (D : Data 𝔄 𝓗 𝓢) (Y v : R4 → Field 𝔄 𝓗 𝓢) : ℝ :=
  supN (fun y => (v y).1) + supN (fun y μ => fderiv ℝ (fun y => (v y).1) y (evec μ)) +
    supN (fun y => (v y).2.1) + l2N (covA Y v) +
    supN (fun y => (v y).2.2.1) + l2N (covH D Y v) +
    supN (fun y => (v y).2.2.2.1) + l2N (covS D Y v) +
    supN (fun y => (v y).2.2.2.2) + l2N (covSb D Y v)

theorem testSize_nonneg (D : Data 𝔄 𝓗 𝓢) (Y v : R4 → Field 𝔄 𝓗 𝓢) : 0 ≤ testSize D Y v := by
  unfold testSize l2N
  have := supN_nonneg (fun y => (v y).1)
  have := supN_nonneg (fun y μ => fderiv ℝ (fun y => (v y).1) y (evec μ))
  have := supN_nonneg (fun y => (v y).2.1)
  have := supN_nonneg (fun y => (v y).2.2.1)
  have := supN_nonneg (fun y => (v y).2.2.2.1)
  have := supN_nonneg (fun y => (v y).2.2.2.2)
  positivity

theorem norm_field_le (w : Field 𝔄 𝓗 𝓢) :
    ‖w‖ ≤ ‖w.1‖ + ‖w.2.1‖ + ‖w.2.2.1‖ + ‖w.2.2.2.1‖ + ‖w.2.2.2.2‖ := by
  have h1 := norm_nonneg w.1
  have h2 := norm_nonneg w.2.1
  have h3 := norm_nonneg w.2.2.1
  have h4 := norm_nonneg w.2.2.2.1
  have h5 := norm_nonneg w.2.2.2.2
  rw [Prod.norm_def, Prod.norm_def, Prod.norm_def, Prod.norm_def]
  refine max_le (by linarith) (max_le (by linarith) (max_le (by linarith) (max_le (by linarith)
    (by linarith))))

/-- The symmetric coframe lift is uniformly bounded on a compact coframe chart. -/
theorem exists_liftM_bound_mat {Ke : Set Mat} (hKe : IsCompact Ke) :
    ∃ Kl, 0 ≤ Kl ∧ ∀ e ∈ Ke, ∀ k : Mat, ‖NativeGravityFirstJet.liftM e k‖ ≤ Kl * ‖k‖ := by
  have hc : Continuous fun p : Mat × Mat => ‖NativeGravityFirstJet.liftM p.1 p.2‖ := by
    refine continuous_norm.comp ?_
    unfold NativeGravityFirstJet.liftM NativeScaling.metric
    fun_prop
  obtain ⟨Kb, hKb⟩ := (hKe.prod (isCompact_closedBall (0 : Mat) 1)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max Kb 0, le_max_right _ _, fun e he k => ?_⟩
  rcases eq_or_ne k 0 with rfl | hk
  · have : NativeGravityFirstJet.liftM e 0 = 0 := by simp [NativeGravityFirstJet.liftM]
    rw [this, norm_zero]; positivity
  · have hkpos : 0 < ‖k‖ := norm_pos_iff.2 hk
    have hmem : ((e, ‖k‖⁻¹ • k) : Mat × Mat) ∈ Ke ×ˢ Metric.closedBall (0 : Mat) 1 := by
      refine ⟨he, ?_⟩
      rw [Metric.mem_closedBall, dist_zero_right, norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ hkpos.ne']
    have h1 := hKb _ hmem
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at h1
    have e2 : NativeGravityFirstJet.liftM e k = ‖k‖ • NativeGravityFirstJet.liftM e (‖k‖⁻¹ • k) := by
      simp only [NativeGravityFirstJet.liftM, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
      rw [show ‖k‖ * (-(1 / 2) * ‖k‖⁻¹) = -(1 / 2 : ℝ) by field_simp]
    rw [e2, norm_smul, norm_norm, mul_comm]
    exact mul_le_mul_of_nonneg_right (h1.trans (le_max_left _ _)) (norm_nonneg _)

theorem contDiff_liftTest {Y v : R4 → Field 𝔄 𝓗 𝓢} (hY : ContDiff ℝ 1 Y) (hv : ContDiff ℝ 1 v) :
    ContDiff ℝ 1 (liftTest Y v) := by
  unfold liftTest
  refine ContDiff.prodMk ?_ (contDiff_snd.comp hv)
  have he : ContDiff ℝ 1 (fun y => (Y y).1) := contDiff_fst.comp hY
  have hk : ContDiff ℝ 1 (fun y => (v y).1) := contDiff_fst.comp hv
  have hg : ContDiff ℝ 1 (fun y => NativeScaling.metric (Y y).1) :=
    NativeDensity.contDiff_metric.comp he
  have hent : ∀ {f : R4 → Mat}, ContDiff ℝ 1 f → ∀ i j, ContDiff ℝ 1 (fun y => f y i j) :=
    fun hf i j => contDiff_pi.mp (contDiff_pi.mp hf i) j
  refine contDiff_pi.mpr fun a => contDiff_pi.mpr fun μ => ?_
  simp only [NativeGravityFirstJet.liftM_apply]
  refine contDiff_const.mul (ContDiff.sum fun α _ => ContDiff.sum fun β _ => ?_)
  exact ((hent he a α).mul (hent hg μ β)).mul (hent hk α β)

theorem isZPeriodic_liftTest {Y v : R4 → Field 𝔄 𝓗 𝓢} (hY : PeriodicCube.IsZPeriodic Y)
    (hv : PeriodicCube.IsZPeriodic v) : PeriodicCube.IsZPeriodic (liftTest Y v) := fun k x => by
  simp only [liftTest, hY k x, hv k x]

/-- The lifted test is pointwise bounded by the test size: `‖ṽ_z‖ ≤ max(K_l, 1) 𝔫_z(v)` on the
box. -/
theorem norm_liftTest_le {Ke : Set Mat} {Kl : ℝ} (hKl0 : 0 ≤ Kl)
    (hKl : ∀ e ∈ Ke, ∀ k : Mat, ‖NativeGravityFirstJet.liftM e k‖ ≤ Kl * ‖k‖)
    (D : Data 𝔄 𝓗 𝓢) {Y v : R4 → Field 𝔄 𝓗 𝓢} (hYe : ∀ z, (Y z).1 ∈ Ke) (hv : Continuous v)
    {y : R4} (hy : y ∈ Icc (0 : R4) 1) :
    ‖liftTest Y v y‖ ≤ max Kl 1 * testSize D Y v := by
  have hm := le_max_left Kl 1
  have h1m := le_max_right Kl 1
  have e1 := le_supN (f := fun y => (v y).1) (continuous_fst.comp hv) hy
  have e2 := le_supN (f := fun y => (v y).2.1) ((continuous_fst.comp continuous_snd).comp hv) hy
  have e3 := le_supN (f := fun y => (v y).2.2.1)
    ((continuous_fst.comp (continuous_snd.comp continuous_snd)).comp hv) hy
  have e4 := le_supN (f := fun y => (v y).2.2.2.1)
    ((continuous_fst.comp (continuous_snd.comp (continuous_snd.comp continuous_snd))).comp hv) hy
  have e5 := le_supN (f := fun y => (v y).2.2.2.2)
    ((continuous_snd.comp (continuous_snd.comp (continuous_snd.comp continuous_snd))).comp hv) hy
  have hl := hKl _ (hYe y) (v y).1
  have hS := testSize_nonneg D Y v
  have hD1 := supN_nonneg (fun y μ => fderiv ℝ (fun y => (v y).1) y (evec μ))
  have hL1 : 0 ≤ l2N (covA Y v) := ENNReal.toReal_nonneg
  have hL2 : 0 ≤ l2N (covH D Y v) := ENNReal.toReal_nonneg
  have hL3 : 0 ≤ l2N (covS D Y v) := ENNReal.toReal_nonneg
  have hL4 : 0 ≤ l2N (covSb D Y v) := ENNReal.toReal_nonneg
  refine (norm_field_le _).trans ?_
  simp only [liftTest]
  have hsum : Kl * ‖(v y).1‖ + ‖(v y).2.1‖ + ‖(v y).2.2.1‖ + ‖(v y).2.2.2.1‖ +
      ‖(v y).2.2.2.2‖ ≤ max Kl 1 * testSize D Y v := by
    unfold testSize
    set M := max Kl 1
    have hM0 : 0 ≤ M := by positivity
    have a1 : Kl * ‖(v y).1‖ ≤ M * supN (fun y => (v y).1) :=
      mul_le_mul hm e1 (norm_nonneg _) hM0
    have a2 : ‖(v y).2.1‖ ≤ M * supN (fun y => (v y).2.1) :=
      e2.trans (le_mul_of_one_le_left (supN_nonneg _) h1m)
    have a3 : ‖(v y).2.2.1‖ ≤ M * supN (fun y => (v y).2.2.1) :=
      e3.trans (le_mul_of_one_le_left (supN_nonneg _) h1m)
    have a4 : ‖(v y).2.2.2.1‖ ≤ M * supN (fun y => (v y).2.2.2.1) :=
      e4.trans (le_mul_of_one_le_left (supN_nonneg _) h1m)
    have a5 : ‖(v y).2.2.2.2‖ ≤ M * supN (fun y => (v y).2.2.2.2) :=
      e5.trans (le_mul_of_one_le_left (supN_nonneg _) h1m)
    have b1 := mul_nonneg hM0 hD1
    have b2 := mul_nonneg hM0 hL1
    have b3 := mul_nonneg hM0 hL2
    have b4 := mul_nonneg hM0 hL3
    have b5 := mul_nonneg hM0 hL4
    simp only [mul_add]
    linarith
  linarith

end Paper

/-! ### `prop:equivariant-native-budgets` -/

section Budgets

open NativeScaling (Mat)
open NativeDensity NativeGauge NativeLinkCov
open DiscreteEulerConsistency (limDensity samp IsPeriodic)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
  [Nontrivial 𝔄] [FiniteDimensional ℝ 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
  [FiniteDimensional ℝ 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
  [FiniteDimensional ℝ 𝓢]

theorem measureReal_cell {n : ℕ} [NeZero n] (k : Fin 4 → Fin n) :
    volume.real (cell n k) = ((n : ℝ)⁻¹) ^ 4 := by
  have hn : (0 : ℝ) < n := npos
  rw [measureReal_def, cell, Real.volume_pi_Ico]
  have e : ∀ i, ((k i : ℝ) + 1) / n - (k i : ℝ) / n = (n : ℝ)⁻¹ := fun i => by
    field_simp; ring
  simp only [e, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal (inv_nonneg.2 hn.le)]

/-- `‖Q_h v(x_k)‖ ≤ m` if `‖v‖ ≤ m` on the cell. -/
theorem norm_cellAvg_le_of_le {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {n : ℕ} [NeZero n] {v : R4 → V} (k : Fin 4 → Fin n) {m : ℝ}
    (hm : ∀ y ∈ cell n k, ‖v y‖ ≤ m) : ‖cellAvg n v k‖ ≤ m := by
  have hn : (0 : ℝ) < n := npos
  have h1 := norm_cellAvg_le (v := v) k
  have h2 : ∫ y in cell n k, ‖v y‖ ≤ m * ((n : ℝ)⁻¹) ^ 4 := by
    have := norm_setIntegral_le_of_norm_le_const (s := cell n k) (f := fun y => ‖v y‖) (C := m)
      (UnitCubeRiemannSum.volume_cell_lt_top (Nat.pos_of_ne_zero (NeZero.ne n)) k)
      fun y hy => by rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]; exact hm y hy
    rw [measureReal_cell, Real.norm_eq_abs] at this
    exact (le_abs_self _).trans this
  have h3 : ((n : ℝ)⁻¹) ^ 4 * ‖cellAvg n v k‖ ≤ ((n : ℝ)⁻¹) ^ 4 * m := by linarith
  exact le_of_mul_le_mul_left h3 (by positivity)

/-- The first variation along a line is the Fréchet derivative. -/
theorem deriv_line_eq_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ}
    {y : E} (hd : DifferentiableAt ℝ f y) (w : E) :
    deriv (fun s : ℝ => f (y + s • w)) 0 = fderiv ℝ f y w := by
  have hl : HasDerivAt (fun s : ℝ => y + s • w) w 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add y
  have := (by simpa using hd.hasFDerivAt : HasFDerivAt f (fderiv ℝ f y) (y + (0 : ℝ) • w))
  exact (this.comp_hasDerivAt (0 : ℝ) hl).deriv

set_option maxHeartbeats 1600000 in
-- the assembly of the two budgets
/-- **`prop:equivariant-native-budgets`** (unit periodic box `[0,1]⁴`, grid `(ℤ/n)⁴`, mesh
`h = 1/n`; flat positive comparison connection on the coordinate bundles, flat reference spin
connection; periodic `C¹` physical tests).  For a covariant data packet `C`, fixed positive
link/matter mass metrics `M`, a compact oriented coframe chart `K_e`, an amplitude bound `A` and a
band constant `B`, there are `C₀ ≥ 0` and `c_res > 0` such that for every `K ≥ 1` and `n` with
`hK ≤ c_res`, every smooth periodic field tuple `z = Y` with coframes in `K_e`, `|Y| ≤ A` and the
growing-band bounds `‖D^j Y‖ ≤ B K^j` (`j ≤ 3`, `eq:eq-growing-band`), and every periodic `C¹`
physical test `v = (k, a, η_H, η_Ψ, η_Ψ̄)`, the unchanged local action and the covariant
cell-average physical test lift `𝓘_h^cov v = Q_h ṽ_z` (`Icov`, `ṽ_z` the symmetric coframe lift
`liftTest`) satisfy
* `eq:eq-native-consistency`: `|D S_h^{loc}[𝓘_h^cov v] - D𝒮(z)[v]| ≤ C₀ h K³ 𝔫_z(v)`, and
* `eq:eq-native-stationarity`: `|D S_h^{loc}[𝓘_h^cov v]| ≤ C₀ σ_h^{link} 𝔫_z(v)`,
where `D𝒮(z)[v] = ∫ DL₀(J¹z)(ṽ_z, ∂ṽ_z)` is the first variation of the continuum
Einstein–Standard-Model action along the physical test (`contVar`), `𝔫_z(v)` is the equivariant
test size `eq:equivariant-test-size` (`testSize`), and `σ_h^{link}` is the dual norm of the
complete action covector in the link/matter mass metric (`NativeLinkCov.covNormP`).  Hence the
budgets `eq:equivariant-consistency`–`eq:equivariant-stationarity` hold with
`c_h^{eq} ≤ C₀ h K³`, `ε_h^{eq} ≤ C₀ σ_h^{link}` (`eq:eq-native-budgets`); the exact site-gauge
invariance of `σ_h^{link}` is `NativeLinkCov.covNormP_record_gauge`. -/
theorem equivariant_native_budgets (C : CovData 𝔄 𝓗 𝓢) (M : MassMetric 𝔄 𝓗) {Ke : Set Mat}
    (hKe : IsCompact Ke) (hdet : ∀ e ∈ Ke, 0 < e.det) (A B : ℝ) :
    ∃ C₀ c_res : ℝ, 0 ≤ C₀ ∧ 0 < c_res ∧ ∀ K : ℝ, 1 ≤ K → ∀ (n : ℕ) [NeZero n],
      (n : ℝ)⁻¹ * K ≤ c_res →
      ∀ Y : R4 → Field 𝔄 𝓗 𝓢, ContDiff ℝ ∞ Y → PeriodicCube.IsZPeriodic Y →
      (∀ z, (Y z).1 ∈ Ke) → (∀ z, ‖Y z‖ ≤ A) →
      (∀ z, ‖iteratedFDeriv ℝ 1 Y z‖ ≤ B * K) → (∀ z, ‖iteratedFDeriv ℝ 2 Y z‖ ≤ B * K ^ 2) →
      (∀ z, ‖iteratedFDeriv ℝ 3 Y z‖ ≤ B * K ^ 3) →
      ∀ v : R4 → Field 𝔄 𝓗 𝓢, ContDiff ℝ 1 v → PeriodicCube.IsZPeriodic v →
      |fderiv ℝ (localAction C.toData (n : ℝ)⁻¹) (samp (n : ℝ)⁻¹ Y : Grid n → Field 𝔄 𝓗 𝓢)
          (Icov n Y v) - contVar (L0 C.toData) Y (liftTest Y v)| ≤
        C₀ * (n : ℝ)⁻¹ * K ^ 3 * testSize C.toData Y v ∧
      |fderiv ℝ (localAction C.toData (n : ℝ)⁻¹) (samp (n : ℝ)⁻¹ Y : Grid n → Field 𝔄 𝓗 𝓢)
          (Icov n Y v)| ≤
        C₀ * covNormP C M (n : ℝ)⁻¹ (toLinks (n : ℝ)⁻¹ (samp (n : ℝ)⁻¹ Y : Grid n → Field 𝔄 𝓗 𝓢)) *
          testSize C.toData Y v := by
  obtain ⟨C₁, c₁, hC₁, hc₁, hbud⟩ := native_consistency_budget C.toData hKe hdet A B
  obtain ⟨C₂, c₂, hc₂, hcons⟩ := NativeEulerConsistency.native_consistency C.toData hKe hdet A B
  obtain ⟨Kl, hKl0, hKl⟩ := exists_liftM_bound_mat hKe
  set Ap := max A 0 with hAp
  set c_res := min c₁ (min c₂ (1 / (512 * (Ap + 1)))) with hcres
  have hcres0 : 0 < c_res := lt_min hc₁ (lt_min hc₂ (by positivity))
  set Lm := max Kl 1 with hLm
  set sK := Real.sqrt (1 + 4 * ‖M.gm‖ + ‖M.hm‖) * Real.sqrt 8 with hsK
  refine ⟨C₁ * Lm + sK * Lm, c_res, by positivity, hcres0, ?_⟩
  intro K hK n _ hnK Y hY hYp hYe hYA h1 h2 h3 v hv hvp
  have hK0 : 0 < K := lt_of_lt_of_le one_pos hK
  set h : ℝ := (n : ℝ)⁻¹ with hh
  have hpos : 0 < h := inv_pos.2 npos
  have hh1 : h ≤ c_res := by
    calc h = h * 1 := (mul_one h).symm
      _ ≤ h * K := mul_le_mul_of_nonneg_left hK hpos.le
      _ ≤ c_res := hnK
  -- the lifted test
  set vt := liftTest Y v with hvt
  have hvt1 : ContDiff ℝ 1 vt := contDiff_liftTest (hY.of_le (by simp)) hv
  have hvtp : PeriodicCube.IsZPeriodic vt := isZPeriodic_liftTest hYp hvp
  set m := Lm * testSize C.toData Y v with hm
  have hm0 : 0 ≤ m := mul_nonneg (by positivity) (testSize_nonneg _ _ _)
  have hvtm : ∀ y ∈ Icc (0 : R4) 1, ‖vt y‖ ≤ m := fun y hy =>
    norm_liftTest_le hKl0 hKl C.toData hYe hv.continuous hy
  have hL1 : ∫ y in Icc (0 : R4) 1, ‖vt y‖ ≤ m := by
    have := norm_setIntegral_le_of_norm_le_const (s := Icc (0 : R4) 1) (f := fun y => ‖vt y‖)
      (C := m) (by rw [PeriodicCube.volume_cube]; exact ENNReal.one_lt_top)
      fun y hy => by rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]; exact hvtm y hy
    rw [measureReal_def, PeriodicCube.volume_cube, ENNReal.toReal_one, mul_one,
      Real.norm_eq_abs] at this
    exact (le_abs_self _).trans this
  refine ⟨?_, ?_⟩
  · -- consistency
    have hb := hbud K hK n (hnK.trans (min_le_left _ _)) Y hY hYp hYe hYA h1 h2 h3 vt hvt1 hvtp
    refine hb.trans ?_
    have hn0 : 0 ≤ C₁ * h * K ^ 3 := by positivity
    calc C₁ * h * K ^ 3 * ∫ y in Icc (0 : R4) 1, ‖vt y‖ ≤ C₁ * h * K ^ 3 * m :=
          mul_le_mul_of_nonneg_left hL1 hn0
      _ ≤ (C₁ * Lm + sK * Lm) * h * K ^ 3 * testSize C.toData Y v := by
          have := testSize_nonneg C.toData Y v
          have : 0 ≤ sK * Lm * h * K ^ 3 * testSize C.toData Y v := by positivity
          rw [hm]; nlinarith
  · -- stationarity
    set y0 : Grid n → Field 𝔄 𝓗 𝓢 := samp h Y with hy0
    obtain ⟨hdet', hlog, -⟩ := hcons K hK h hpos (hnK.trans ((min_le_right _ _).trans
      (min_le_left _ _))) n Y (hY.of_le (ContEulerBounds.natCast_le_infty 3))
      (by rw [hh, mul_inv_cancel₀ npos.ne']; exact isPeriodic_one_of_isZPeriodic hYp)
      hYe hYA h1 h2 h3
    have hgA : ∀ μ x, h * ‖NativeDensity.gauge y0 μ x‖ ≤ 1 / 512 := by
      intro μ x
      have hg : ‖NativeDensity.gauge y0 μ x‖ ≤ Ap := by
        change ‖(Y (DiscreteEulerConsistency.pos h x)).2.1 μ‖ ≤ Ap
        refine (norm_le_pi_norm _ μ).trans ((norm_fst_le _).trans ((norm_snd_le _).trans
          ((hYA _).trans (le_max_left _ _))))
      have hc3 : h ≤ 1 / (512 * (Ap + 1)) := hh1.trans ((min_le_right _ _).trans (min_le_right _ _))
      calc h * ‖NativeDensity.gauge y0 μ x‖ ≤ 1 / (512 * (Ap + 1)) * Ap :=
            mul_le_mul hc3 hg (norm_nonneg _) (by positivity)
        _ ≤ 1 / 512 := by
            rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by norm_num)]
            nlinarith [le_max_right A 0]
    have hs : ∀ μ x, ‖(n : ℝ)⁻¹ • NativeDensity.gauge y0 μ x‖ < 1 / 32 := by
      intro μ x
      rw [norm_smul, Real.norm_of_nonneg hpos.le]
      linarith [hgA μ x]
    have hd : DifferentiableAt ℝ (localAction C.toData (n : ℝ)⁻¹) y0 :=
      NativeFrechet.differentiableAt_localAction _ hpos.ne' (fun x => (hdet' x).ne')
        (fun x μ ν _ => hlog x μ ν)
        (fun x μ ν _ => (DeterminantResolved.norm_gaugePlaquette_sub_one_le
          (NativeDensity.gauge y0) (fun μ x => hgA μ x) x μ ν).trans_lt (by norm_num))
    have hst := abs_deriv_localAction_le C M hs hd (Icov n Y v)
    rw [deriv_line_eq_fderiv hd] at hst
    refine hst.trans ?_
    -- the nodal mass of the averaged test
    have hQ : ∀ x, ‖Icov n Y v x‖ ≤ m := by
      intro x
      refine norm_cellAvg_le_of_le _ fun y hy => hvtm y
        (UnitCubeRiemannSum.cell_subset_Icc (Nat.pos_of_ne_zero (NeZero.ne n)) _ hy)
    have hnod : nodalL2Sq (n : ℝ)⁻¹ (Icov n Y v) ≤ 8 * m ^ 2 := by
      unfold nodalL2Sq
      have hpt : ∀ x, ‖(Icov n Y v x).1‖ ^ 2 + ∑ μ, ‖(Icov n Y v x).2.1 μ‖ ^ 2 +
          ‖(Icov n Y v x).2.2.1‖ ^ 2 + ‖(Icov n Y v x).2.2.2.1‖ ^ 2 +
          ‖(Icov n Y v x).2.2.2.2‖ ^ 2 ≤ 8 * m ^ 2 := by
        intro x
        set w := Icov n Y v x
        have hw := hQ x
        have c1 : ‖w.1‖ ≤ m := (norm_fst_le w).trans hw
        have c2 : ∀ μ, ‖w.2.1 μ‖ ≤ m := fun μ =>
          (norm_le_pi_norm _ μ).trans ((norm_fst_le _).trans ((norm_snd_le w).trans hw))
        have c3 : ‖w.2.2.1‖ ≤ m :=
          (norm_fst_le _).trans ((norm_snd_le _).trans ((norm_snd_le w).trans hw))
        have c4 : ‖w.2.2.2.1‖ ≤ m := (norm_fst_le _).trans ((norm_snd_le _).trans
          ((norm_snd_le _).trans ((norm_snd_le w).trans hw)))
        have c5 : ‖w.2.2.2.2‖ ≤ m := (norm_snd_le _).trans ((norm_snd_le _).trans
          ((norm_snd_le _).trans ((norm_snd_le w).trans hw)))
        have s2 : ∑ μ, ‖w.2.1 μ‖ ^ 2 ≤ ∑ _μ : Fin 4, m ^ 2 := Finset.sum_le_sum fun μ _ =>
          pow_le_pow_left₀ (norm_nonneg _) (c2 μ) 2
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at s2
        have p1 := pow_le_pow_left₀ (norm_nonneg _) c1 2
        have p3 := pow_le_pow_left₀ (norm_nonneg _) c3 2
        have p4 := pow_le_pow_left₀ (norm_nonneg _) c4 2
        have p5 := pow_le_pow_left₀ (norm_nonneg _) c5 2
        push_cast at s2
        linarith
      calc ((n : ℝ)⁻¹) ^ 4 * ∑ x, (‖(Icov n Y v x).1‖ ^ 2 + ∑ μ, ‖(Icov n Y v x).2.1 μ‖ ^ 2 +
            ‖(Icov n Y v x).2.2.1‖ ^ 2 + ‖(Icov n Y v x).2.2.2.1‖ ^ 2 +
            ‖(Icov n Y v x).2.2.2.2‖ ^ 2)
          ≤ ((n : ℝ)⁻¹) ^ 4 * ∑ _x : Grid n, 8 * m ^ 2 :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => hpt x) (by positivity)
        _ = 8 * m ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            have hc : (Fintype.card (Grid n) : ℝ) = (n : ℝ) ^ 4 := by simp [ZMod.card]
            rw [hc, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ npos.ne', one_pow, one_mul]
    have hcov0 : 0 ≤ covNormP C M (n : ℝ)⁻¹ (toLinks (n : ℝ)⁻¹ y0) :=
      Real.sSup_nonneg fun _ ⟨_, _, hr⟩ => hr ▸ abs_nonneg _
    have hsq : Real.sqrt (nodalL2Sq (n : ℝ)⁻¹ (Icov n Y v)) ≤ Real.sqrt 8 * m := by
      calc Real.sqrt (nodalL2Sq (n : ℝ)⁻¹ (Icov n Y v)) ≤ Real.sqrt (8 * m ^ 2) :=
            Real.sqrt_le_sqrt hnod
        _ = Real.sqrt 8 * m := by rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq hm0]
    have hS := testSize_nonneg C.toData Y v
    calc covNormP C M (n : ℝ)⁻¹ (toLinks (n : ℝ)⁻¹ y0) *
          (Real.sqrt (1 + 4 * ‖M.gm‖ + ‖M.hm‖) * Real.sqrt (nodalL2Sq (n : ℝ)⁻¹ (Icov n Y v)))
        ≤ covNormP C M (n : ℝ)⁻¹ (toLinks (n : ℝ)⁻¹ y0) *
          (Real.sqrt (1 + 4 * ‖M.gm‖ + ‖M.hm‖) * (Real.sqrt 8 * m)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq (Real.sqrt_nonneg _)) hcov0
      _ = sK * Lm * covNormP C M (n : ℝ)⁻¹ (toLinks (n : ℝ)⁻¹ y0) * testSize C.toData Y v := by
          rw [hm, hsK]; ring
      _ ≤ (C₁ * Lm + sK * Lm) * covNormP C M (n : ℝ)⁻¹ (toLinks (n : ℝ)⁻¹ y0) *
            testSize C.toData Y v := by
          have : 0 ≤ C₁ * Lm * covNormP C M (n : ℝ)⁻¹ (toLinks (n : ℝ)⁻¹ y0) *
            testSize C.toData Y v := by positivity
          nlinarith

end Budgets

/-! ### Non-vacuity -/

section NonVacuity

open NativeDensity
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-- Non-vacuity of the field hypotheses of `equivariant_native_budgets`: a constant field tuple is
smooth, `ℤ⁴`-periodic and satisfies the growing-band bounds with `B = 0` (all derivatives of order
`≥ 1` vanish); with `K_e = {e₀}`, `det e₀ > 0`, the chart and amplitude conditions hold. -/
theorem const_field_hyps {𝔄 𝓗 𝓢 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄]
    [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢]
    (w : Field 𝔄 𝓗 𝓢) :
    ContDiff ℝ ∞ (fun _ : R4 => w) ∧ PeriodicCube.IsZPeriodic (fun _ : R4 => w) ∧
      ∀ j : ℕ, 1 ≤ j → ∀ z, ‖iteratedFDeriv ℝ j (fun _ : R4 => w) z‖ = 0 := by
  refine ⟨contDiff_const, fun _ _ => rfl, fun j hj z => ?_⟩
  rw [iteratedFDeriv_const_of_ne (by omega), Pi.zero_apply, norm_zero]

end NonVacuity

end RenewalGeometry.EquivariantBudgets
