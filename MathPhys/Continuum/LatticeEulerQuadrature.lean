/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import MathPhys.Analysis.PeriodicCubeCalculus
import MathPhys.Analysis.LipschitzRiemannSumError
import MathPhys.Analysis.UnitCubeRiemannSum
import MathPhys.Continuum.ContEulerDerivativeBounds

/-!
# Lattice Euler rows, cell quadrature and continuum integration by parts

Generic part of `prop:equivariant-native-budgets` (any first-order density `L(w, p)` on a normed
field space `V`, the unit periodic box `[0,1]⁴`, the grid `(ℤ/n)⁴` of mesh `h = 1/n`):

* `fderiv_eq_sum_eulerRow`: the derivative of a lattice action is the nodal pairing with its raw
  Euler rows, `DA(y)[w] = h⁴ Σ_x E_h(y)(x)(w(x))`.
* `cellAvg`, `sum_norm_cellAvg_le`, `abs_quadrature_sub_le`: cell-average test lifts and cell
  quadrature for a Lipschitz covector field.
* `contVar`, `contVar_eq_integral_contEuler`: the continuum first variation and continuum
  integration by parts for `ℤ⁴`-periodic fields.

Split out of `MathPhys.Continuum.EquivariantNativeBudgets` (which re-exports it); names are
unchanged.
-/

open MeasureTheory Set Filter Topology Finset
open scoped BigOperators ContDiff

noncomputable section

namespace MathPhys.EquivariantBudgets

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

end MathPhys.EquivariantBudgets
