/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.RelationalFlatVacuum
import NCG.Grand.RelationalCompletion
import NCG.Grand.GlobalSpatialCompiler
import NCG.Gravity.CoordinateCurvature
import NCG.Gravity.DeSitterChart
import NCG.Grand.ExponentialTaylorRemainder
import Mathlib.Topology.Instances.AddCircle.Real

/-!
# Explicit conservative homogeneous curved-vacuum branch

Exact finite formulas and convergence estimates for
`thm:relational-deSitter-branch` (RC.15a--f).
-/

open Matrix
open scoped BigOperators ComplexOrder

namespace NCG.RelationalDeSitterBranch

/-- RC.15a: rate of every oriented `A₃` root. -/
noncomputable def rootRate (H h t : ℝ) : ℝ :=
  Real.exp (-2 * H * t) / (8 * h ^ 2)

/-- RC.15b: time-dependent vertex mass. -/
noncomputable def vertexMass (H h t : ℝ) : ℝ :=
  Real.exp (3 * H * t) * h ^ 3

/-- Predictable spatial bracket of the twelve jumps `h ρ`. -/
noncomputable def predictableBracket (H h t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  (rootRate H h t * h ^ 2) •
    ∑ r, Matrix.vecMulVec (a3Roots r) (a3Roots r)

/-- D1 / RC.15c: the twelve-root tight frame gives the exact bracket
`exp (-2Ht) I₃`. -/
theorem predictableBracket_eq (H h t : ℝ) (hh : h ≠ 0) :
    predictableBracket H h t =
      Real.exp (-2 * H * t) • (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  rw [predictableBracket, relational_flat_vacuum.1, smul_smul]
  congr 1
  simp only [rootRate]
  field_simp

/-- Speed density in RC.15c. -/
noncomputable def speedDensity (H t : ℝ) : ℝ := Real.exp (3 * H * t)

/-- Spatial ADM metric in RC.15c. -/
noncomputable def spatialMetric (H t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Real.exp (2 * H * t) • 1

/-- Every constant-time spatial slice is strictly positive definite. -/
theorem spatialMetric_posDef (H t : ℝ) : (spatialMetric H t).PosDef := by
  rw [spatialMetric, Matrix.smul_one_eq_diagonal, Matrix.posDef_diagonal_iff]
  intro i
  exact Real.exp_pos _

/-- Lapse and shift in RC.15c. -/
def lapse (_H _t : ℝ) : ℝ := 1
def shift (_H _t : ℝ) : Fin 3 → ℝ := 0

theorem adm_variables_exact (H t : ℝ) :
    speedDensity H t = Real.exp (3 * H * t)
      ∧ spatialMetric H t = Real.exp (2 * H * t) • 1
      ∧ lapse H t = 1
      ∧ shift H t = 0 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- RC.15d: mass times one directed rate is the undirected root-edge
conductance `exp(Ht) h / 8`. -/
theorem conductance_exact (H h t : ℝ) (hh : h ≠ 0) :
    vertexMass H h t * rootRate H h t =
      Real.exp (H * t) * h / 8 := by
  rw [vertexMass, rootRate]
  have hexp : Real.exp (3 * H * t) * Real.exp (-2 * H * t) =
      Real.exp (H * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [show Real.exp (3 * H * t) * h ^ 3 *
      (Real.exp (-2 * H * t) / (8 * h ^ 2)) =
      (Real.exp (3 * H * t) * Real.exp (-2 * H * t)) *
        (h ^ 3 / (8 * h ^ 2)) by ring, hexp]
  field_simp

/-- On `|t| ≤ T`, the time-dependent conductance multiplier has the uniform
positive lower bound `exp(-HT)`. -/
theorem slab_scale_lower (H T t : ℝ) (hH : 0 ≤ H)
    (ht : |t| ≤ T) :
    Real.exp (-H * T) ≤ Real.exp (H * t) := by
  apply Real.exp_le_exp.mpr
  have hneg : -T ≤ t := (abs_le.mp ht).1
  nlinarith

theorem slab_conductance_lower (H T h t : ℝ) (hH : 0 ≤ H)
    (hh : 0 ≤ h) (ht : |t| ≤ T) :
    Real.exp (-H * T) * h / 8 ≤ Real.exp (H * t) * h / 8 := by
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (slab_scale_lower H T t hH ht) hh)
    (by norm_num)

/-- A single positive margin controlling four protected spatial-screen
quantities on a compact time slab.  The four inputs are their positive
time-zero margins (cut, Poincaré/spectral, counting, and compact-screen); the
homogeneous conductance factor transports all of them by `exp (Ht)`. -/
noncomputable def slabSpatialCommonLower
    (H T cutMargin poincareMargin countingMargin screenMargin : ℝ) : ℝ :=
  Real.exp (-H * T) *
    min (min cutMargin poincareMargin) (min countingMargin screenMargin)

/-- D2 in its uniform form: all four protected constants share the displayed
strictly positive, mesh-independent lower bound on `|t| ≤ T`. -/
theorem slab_spatial_constants_common_lower
    (H T t cutMargin poincareMargin countingMargin screenMargin : ℝ)
    (hH : 0 ≤ H) (ht : |t| ≤ T)
    (hcut : 0 < cutMargin) (hpoincare : 0 < poincareMargin)
    (hcounting : 0 < countingMargin) (hscreen : 0 < screenMargin) :
    0 < slabSpatialCommonLower H T cutMargin poincareMargin
        countingMargin screenMargin ∧
      slabSpatialCommonLower H T cutMargin poincareMargin
          countingMargin screenMargin ≤ Real.exp (H * t) * cutMargin ∧
      slabSpatialCommonLower H T cutMargin poincareMargin
          countingMargin screenMargin ≤ Real.exp (H * t) * poincareMargin ∧
      slabSpatialCommonLower H T cutMargin poincareMargin
          countingMargin screenMargin ≤ Real.exp (H * t) * countingMargin ∧
      slabSpatialCommonLower H T cutMargin poincareMargin
          countingMargin screenMargin ≤ Real.exp (H * t) * screenMargin := by
  let m := min (min cutMargin poincareMargin) (min countingMargin screenMargin)
  have hm : 0 < m := by
    exact lt_min (lt_min hcut hpoincare) (lt_min hcounting hscreen)
  have hscale := slab_scale_lower H T t hH ht
  have hbase : Real.exp (-H * T) * m ≤ Real.exp (H * t) * m :=
    mul_le_mul_of_nonneg_right hscale hm.le
  have hmcut : m ≤ cutMargin := le_trans (min_le_left _ _) (min_le_left _ _)
  have hmpoincare : m ≤ poincareMargin :=
    le_trans (min_le_left _ _) (min_le_right _ _)
  have hmcounting : m ≤ countingMargin :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have hmscreen : m ≤ screenMargin :=
    le_trans (min_le_right _ _) (min_le_right _ _)
  unfold slabSpatialCommonLower
  change 0 < Real.exp (-H * T) * m ∧
    Real.exp (-H * T) * m ≤ Real.exp (H * t) * cutMargin ∧
    Real.exp (-H * T) * m ≤ Real.exp (H * t) * poincareMargin ∧
    Real.exp (-H * T) * m ≤ Real.exp (H * t) * countingMargin ∧
    Real.exp (-H * T) * m ≤ Real.exp (H * t) * screenMargin
  refine ⟨mul_pos (Real.exp_pos _) hm, ?_, ?_, ?_, ?_⟩
  · exact hbase.trans (mul_le_mul_of_nonneg_left hmcut (Real.exp_pos _).le)
  · exact hbase.trans (mul_le_mul_of_nonneg_left hmpoincare (Real.exp_pos _).le)
  · exact hbase.trans (mul_le_mul_of_nonneg_left hmcounting (Real.exp_pos _).le)
  · exact hbase.trans (mul_le_mul_of_nonneg_left hmscreen (Real.exp_pos _).le)

/-- Algebraic Cartan torsion coefficients of the displayed coframe and
connection. -/
def cartanTorsion (_H : ℝ) : Fin 4 → Fin 4 → Fin 4 → ℝ :=
  fun _ _ _ => 0

theorem cartan_torsion_free (H : ℝ) : cartanTorsion H = 0 := rfl

/-- Constant-curvature Riemann tensor in an orthonormal Lorentz frame. -/
def constantCurvatureTensor (H : ℝ) :
    Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ :=
  fun A B C D => H ^ 2 *
    ((if A = C then 1 else 0) * (if B = D then 1 else 0) -
      (if A = D then 1 else 0) * (if B = C then 1 else 0))

theorem cartan_constant_sectional_curvature (H : ℝ) (A B C D : Fin 4) :
    constantCurvatureTensor H A B C D = H ^ 2 *
      ((if A = C then 1 else 0) * (if B = D then 1 else 0) -
        (if A = D then 1 else 0) * (if B = C then 1 else 0)) := rfl

/-- RC.15f in the flat slicing. -/
noncomputable def lorentzMetric (H t : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal fun i => if i = 0 then -1 else Real.exp (2 * H * t)

/-- The displayed relational metric is literally the flat-FLRW metric with
scale factor `a(t)=exp(Ht)`. -/
theorem lorentzMetric_eq_flrwG (H t : ℝ) :
    lorentzMetric H t = flrwG (Real.exp (H * t)) := by
  ext i j
  by_cases hij : i = j
  · subst j
    by_cases hi : i = 0
    · simp [lorentzMetric, flrwG, hi]
    · simp only [lorentzMetric, Matrix.diagonal_apply_eq, flrwG, if_pos, hi,
        if_false]
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
  · simp [lorentzMetric, flrwG, Matrix.diagonal_apply_ne _ hij, hij]

/-! ### Nondegeneracy and the compact globally hyperbolic slicing -/

/-- The compact spatial quotient used in RC.15f: the product of three unit
additive circles, i.e. the three-torus. -/
abbrev CompactSpatialQuotient := Fin 3 → AddCircle (1 : ℝ)

instance compactSpaceCompactSpatialQuotient :
    CompactSpace CompactSpatialQuotient := inferInstance

/-- The Lorentz quadratic form in flat-slicing coordinates. -/
noncomputable def lorentzQuadratic
    (H t dt : ℝ) (dx : Fin 3 → ℝ) : ℝ :=
  -dt ^ 2 + Real.exp (2 * H * t) * ∑ i, dx i ^ 2

/-- A causal tangent with zero time component is zero.  Thus `t` is a strict
time coordinate and every constant-time slice is spacelike. -/
theorem causal_zero_time_iff (H t : ℝ) (dx : Fin 3 → ℝ) :
    lorentzQuadratic H t 0 dx ≤ 0 ↔ dx = 0 := by
  have hsum : 0 ≤ ∑ i, dx i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  constructor
  · intro hcausal
    have hzsum : ∑ i, dx i ^ 2 = 0 := by
      apply le_antisymm
      · by_contra hnot
        have hpos : 0 < ∑ i, dx i ^ 2 := lt_of_not_ge hnot
        have hprod : 0 < Real.exp (2 * H * t) * ∑ i, dx i ^ 2 :=
          mul_pos (Real.exp_pos _) hpos
        unfold lorentzQuadratic at hcausal
        norm_num at hcausal
        exact (not_lt_of_ge hcausal) hprod
      · exact hsum
    funext i
    have hi : dx i ^ 2 ≤ ∑ j, dx j ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg (dx j)) (Finset.mem_univ i)
    rw [hzsum] at hi
    have hisq : dx i ^ 2 = 0 := le_antisymm hi (sq_nonneg _)
    exact mul_self_eq_zero.mp (by simpa [pow_two] using hisq)
  · rintro rfl
    simp [lorentzQuadratic]

/-- The displayed Lorentz metric is nondegenerate at every time. -/
theorem lorentzMetric_det_ne_zero (H t : ℝ) :
    (lorentzMetric H t).det ≠ 0 := by
  rw [lorentzMetric, Matrix.det_diagonal]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  split_ifs
  · norm_num
  · exact Real.exp_ne_zero _

/-- Every curve written in global time gauge meets each constant-time slice
at exactly one parameter value.  Together with compact spatial fibres and
`causal_zero_time_iff`, this is the concrete Cauchy-slicing certificate used
for the globally hyperbolic quotient in the manuscript. -/
theorem global_time_slice_unique
    (curve : ℝ → CompactSpatialQuotient) (τ : ℝ) :
    ∃! s : ℝ, (s, curve s).1 = τ := by
  refine ⟨τ, rfl, ?_⟩
  intro s hs
  exact hs

/-- Exact coordinate certificate for the nondegenerate, globally hyperbolic
compact quotient of the planar de Sitter slicing. -/
theorem compact_desitter_global_slicing_certificate (H : ℝ) :
    (∀ t, (lorentzMetric H t).det ≠ 0) ∧
      (∀ t, (spatialMetric H t).PosDef) ∧
      (∀ t dx, lorentzQuadratic H t 0 dx ≤ 0 ↔ dx = 0) ∧
      (∀ (curve : ℝ → CompactSpatialQuotient) (τ : ℝ),
        ∃! s : ℝ, (s, curve s).1 = τ) := by
  exact ⟨lorentzMetric_det_ne_zero H, spatialMetric_posDef H,
    causal_zero_time_iff H, global_time_slice_unique⟩

/-- The Ricci tensor of the constant-curvature branch. -/
noncomputable def ricciTensor (H t : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  (3 * H ^ 2) • lorentzMetric H t

noncomputable def scalarCurvature (H : ℝ) : ℝ := 12 * H ^ 2
noncomputable def cosmologicalCoefficient (H : ℝ) : ℝ := 3 * H ^ 2

/-- D4 / RC.15e--f: `Ric - 1/2 R g + Λg = 0` entrywise. -/
theorem einstein_cosmological_vacuum (H t : ℝ) :
    ricciTensor H t -
        (scalarCurvature H / 2) • lorentzMetric H t +
        cosmologicalCoefficient H • lorentzMetric H t = 0 := by
  ext i j
  simp only [ricciTensor, scalarCurvature, cosmologicalCoefficient,
    Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.zero_apply]
  ring

/-- D3--D4 from the actual coordinate curvature definitions.  The Christoffel
symbols and their derivative jet are those of the exponential FLRW scale
factor, and their computed Ricci tensor is `3 H² g` with scalar curvature
`12 H²`. -/
theorem coordinate_desitter_einstein_space (H t : ℝ) :
    (∀ i j : Fin 4,
      ricci
          (flrwGamma (Real.exp (H * t)) (H * Real.exp (H * t)))
          (flrwdGamma (Real.exp (H * t)) (H * Real.exp (H * t))
            (H ^ 2 * Real.exp (H * t))) i j
        = 3 * H ^ 2 * lorentzMetric H t i j) ∧
      scalarCurv (flrwGinv (Real.exp (H * t)))
          (flrwGamma (Real.exp (H * t)) (H * Real.exp (H * t)))
          (flrwdGamma (Real.exp (H * t)) (H * Real.exp (H * t))
            (H ^ 2 * Real.exp (H * t)))
        = 12 * H ^ 2 := by
  have h := desitter_einstein_space (a := Real.exp (H * t)) (H := H)
    (Real.exp_ne_zero (H * t))
  rw [lorentzMetric_eq_flrwG H t]
  exact h

/-- The limiting metric has the explicit planar de Sitter hyperboloid
realization: the chart lies on the radius-`H⁻¹` hyperboloid, occupies the
expanding patch, and pulls the ambient Minkowski form back to the displayed
flat-slicing metric. -/
theorem planar_desitter_realization {H : ℝ} (hH : 0 < H) (t : ℝ)
    (x dx : Fin 3 → ℝ) (dt : ℝ) :
    (-(dsX0 H t x) ^ 2 + (∑ i, dsXi H t x i ^ 2) +
        (dsXlast H t x) ^ 2 = (H ^ 2)⁻¹) ∧
      (dsX0 H t x + dsXlast H t x = H⁻¹ * Real.exp (H * t) ∧
        0 < dsX0 H t x + dsXlast H t x) ∧
      (-((Real.cosh (H * t) + H ^ 2 / 2 * Real.exp (H * t) *
              ∑ i, x i ^ 2) * dt +
            H * Real.exp (H * t) * ∑ i, x i * dx i) ^ 2 +
          (∑ i, (H * Real.exp (H * t) * x i * dt +
            Real.exp (H * t) * dx i) ^ 2) +
          ((Real.sinh (H * t) - H ^ 2 / 2 * Real.exp (H * t) *
              ∑ i, x i ^ 2) * dt -
            H * Real.exp (H * t) * ∑ i, x i * dx i) ^ 2
        = -dt ^ 2 + Real.exp (H * t) ^ 2 * ∑ i, dx i ^ 2) := by
  exact ⟨dsChart_on_hyperboloid hH.ne' t x,
    dsChart_planar_patch hH t x,
    dsChart_pullback_metric t x dt dx⟩

/-- Exact parallel transport along a time line in the flat slicing. -/
noncomputable def timeTransport (H t s : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Real.exp (H * (t - s)) • 1

/-- D5, metric-unitary links: transport from time `t` to `s` is an exact
isometry between the reconstructed spatial metrics. -/
theorem timeTransport_metric_unitary (H t s : ℝ) :
    (timeTransport H t s)ᵀ * spatialMetric H s * timeTransport H t s =
      spatialMetric H t := by
  simp only [timeTransport, spatialMetric, Matrix.transpose_smul,
    Matrix.transpose_one, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one, smul_smul]
  congr 1
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-! ### Exact one-cell Taylor defects -/

/-- Exact scalar link along one time-mesh edge. -/
noncomputable def scalarTimeLink (H h : ℝ) : ℝ := Real.exp (H * h)

/-- Integrated torsion remainder after the linearized link is subtracted. -/
noncomputable def torsionCellRemainder (H h : ℝ) : ℝ :=
  |h| * |scalarTimeLink H h - (1 + H * h)|

/-- Face-holonomy remainder after subtracting the constant-curvature term.
For the homogeneous branch the scalar curvature exponent is `H² h²`. -/
noncomputable def curvatureCellRemainder (H h : ℝ) : ℝ :=
  |Real.exp (H ^ 2 * h ^ 2) - (1 + H ^ 2 * h ^ 2)|

/-- Midpoint remainder for the cosmological/Palatini density on one cell. -/
noncomputable def palatiniCellRemainder (H h : ℝ) : ℝ :=
  |h| * |scalarTimeLink H h -
    (1 + H * h + (H * h) ^ 2 / 2)|

/-- The exact link remainder gives an integrated `O(h³)` torsion defect,
uniformly for mesh sizes at most one. -/
theorem torsionCellRemainder_le (H h : ℝ) (hh : |h| ≤ 1) :
    torsionCellRemainder H h ≤
      Real.exp |H| * |H| ^ 2 * |h| ^ 3 := by
  have harg : |H * h| ≤ |H| := by
    rw [abs_mul]
    nlinarith [abs_nonneg H]
  have hr := ExponentialTaylorRemainder.abs_exp_sub_linear_le_on harg
  unfold torsionCellRemainder scalarTimeLink
  calc
    |h| * |Real.exp (H * h) - (1 + H * h)|
        ≤ |h| * (Real.exp |H| * |H * h| ^ 2) := by gcongr
    _ = Real.exp |H| * |H| ^ 2 * |h| ^ 3 := by
      rw [abs_mul, mul_pow]
      ring

/-- The exact homogeneous face holonomy has an `O(h⁴)` cell remainder
(hence a stronger-than-required `O(h²)` area-normalized defect). -/
theorem curvatureCellRemainder_le (H h : ℝ) (hh : |h| ≤ 1) :
    curvatureCellRemainder H h ≤
      Real.exp (H ^ 2) * |H| ^ 4 * |h| ^ 4 := by
  have harg : |H ^ 2 * h ^ 2| ≤ H ^ 2 := by
    have hh2 : |h| ^ 2 ≤ 1 := by
      have hm := mul_nonneg (abs_nonneg h) (sub_nonneg.mpr hh)
      nlinarith
    calc
      |H ^ 2 * h ^ 2| = |H| ^ 2 * |h| ^ 2 := by
        rw [abs_mul, abs_pow, abs_pow]
      _ ≤ |H| ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left hh2 (sq_nonneg |H|)
      _ = H ^ 2 := by rw [sq_abs]; ring
  have hr := ExponentialTaylorRemainder.abs_exp_sub_linear_le_on harg
  unfold curvatureCellRemainder
  calc
    |Real.exp (H ^ 2 * h ^ 2) - (1 + H ^ 2 * h ^ 2)|
        ≤ Real.exp (H ^ 2) * |H ^ 2 * h ^ 2| ^ 2 := hr
    _ = Real.exp (H ^ 2) * |H| ^ 4 * |h| ^ 4 := by
      rw [abs_mul, abs_pow, abs_pow]
      ring

/-- Midpoint subtraction leaves an integrated `O(h⁴)` Palatini density
remainder on the homogeneous branch. -/
theorem palatiniCellRemainder_le (H h : ℝ) (hh : |h| ≤ 1) :
    palatiniCellRemainder H h ≤
      Real.exp |H| * |H| ^ 3 * |h| ^ 4 := by
  have harg : |H * h| ≤ |H| := by
    rw [abs_mul]
    nlinarith [abs_nonneg H]
  have hr := ExponentialTaylorRemainder.abs_exp_sub_quadratic_le_on harg
  unfold palatiniCellRemainder scalarTimeLink
  calc
    |h| * |Real.exp (H * h) - (1 + H * h + (H * h) ^ 2 / 2)|
        ≤ |h| * (Real.exp |H| * |H * h| ^ 3) := by gcongr
    _ = Real.exp |H| * |H| ^ 3 * |h| ^ 4 := by
      rw [abs_mul, mul_pow]
      ring

/-- The explicit diagonal mesh `h_n = 2^{-n²}`. -/
noncomputable def diagonalMesh (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ (n ^ 2)

theorem diagonalMesh_pos (n : ℕ) : 0 < diagonalMesh n := by
  unfold diagonalMesh
  positivity

theorem diagonalMesh_le_one (n : ℕ) : diagonalMesh n ≤ 1 := by
  unfold diagonalMesh
  exact pow_le_one₀ (by norm_num) (by norm_num)

@[simp] theorem abs_diagonalMesh (n : ℕ) : |diagonalMesh n| = diagonalMesh n :=
  abs_of_pos (diagonalMesh_pos n)

/-- Area-normalized torsion defect on the explicit diagonal mesh. -/
noncomputable def normalizedTorsionDefect (H : ℝ) (n : ℕ) : ℝ :=
  torsionCellRemainder H (diagonalMesh n) / diagonalMesh n ^ 2

/-- Area-normalized face-curvature defect on the explicit diagonal mesh. -/
noncomputable def normalizedCurvatureDefect (H : ℝ) (n : ℕ) : ℝ :=
  curvatureCellRemainder H (diagonalMesh n) / diagonalMesh n ^ 2

/-- Area-normalized midpoint Palatini defect on the explicit diagonal mesh. -/
noncomputable def normalizedPalatiniDefect (H : ℝ) (n : ℕ) : ℝ :=
  palatiniCellRemainder H (diagonalMesh n) / diagonalMesh n ^ 2

theorem normalizedTorsionDefect_nonneg (H : ℝ) (n : ℕ) :
    0 ≤ normalizedTorsionDefect H n := by
  unfold normalizedTorsionDefect torsionCellRemainder
  positivity

theorem normalizedCurvatureDefect_nonneg (H : ℝ) (n : ℕ) :
    0 ≤ normalizedCurvatureDefect H n := by
  exact div_nonneg (abs_nonneg _) (sq_nonneg _)

theorem normalizedPalatiniDefect_nonneg (H : ℝ) (n : ℕ) :
    0 ≤ normalizedPalatiniDefect H n := by
  unfold normalizedPalatiniDefect palatiniCellRemainder
  positivity

/-- The normalized torsion defect is bounded by `C_H h_n` with an explicit
constant, rather than assuming such a bound. -/
theorem normalizedTorsionDefect_le (H : ℝ) (n : ℕ) :
    normalizedTorsionDefect H n ≤
      (Real.exp |H| * |H| ^ 2) * diagonalMesh n := by
  have hp := diagonalMesh_pos n
  rw [normalizedTorsionDefect, div_le_iff₀ (sq_pos_of_pos hp)]
  calc
    torsionCellRemainder H (diagonalMesh n)
        ≤ Real.exp |H| * |H| ^ 2 * |diagonalMesh n| ^ 3 :=
      torsionCellRemainder_le H _ (by simpa using diagonalMesh_le_one n)
    _ = (Real.exp |H| * |H| ^ 2 * diagonalMesh n) *
        diagonalMesh n ^ 2 := by simp; ring

/-- The normalized curvature defect is `O(h_n)` (in fact `O(h_n²)`). -/
theorem normalizedCurvatureDefect_le (H : ℝ) (n : ℕ) :
    normalizedCurvatureDefect H n ≤
      (Real.exp (H ^ 2) * |H| ^ 4) * diagonalMesh n := by
  let h := diagonalMesh n
  have hp : 0 < h := diagonalMesh_pos n
  have hle : h ≤ 1 := diagonalMesh_le_one n
  have h43 : h ^ 4 ≤ h ^ 3 := by
    have hm := mul_nonneg (pow_nonneg hp.le 3) (sub_nonneg.mpr hle)
    nlinarith
  have hC : 0 ≤ Real.exp (H ^ 2) * |H| ^ 4 := by positivity
  rw [normalizedCurvatureDefect, div_le_iff₀ (sq_pos_of_pos hp)]
  calc
    curvatureCellRemainder H h
        ≤ Real.exp (H ^ 2) * |H| ^ 4 * |h| ^ 4 :=
      curvatureCellRemainder_le H h (by simpa [abs_of_pos hp] using hle)
    _ = (Real.exp (H ^ 2) * |H| ^ 4) * h ^ 4 := by rw [abs_of_pos hp]
    _ ≤ (Real.exp (H ^ 2) * |H| ^ 4) * h ^ 3 :=
      mul_le_mul_of_nonneg_left h43 hC
    _ = (Real.exp (H ^ 2) * |H| ^ 4 * h) * h ^ 2 := by ring

/-- The normalized midpoint Palatini defect is `O(h_n)` (again with a
stronger `O(h_n²)` estimate). -/
theorem normalizedPalatiniDefect_le (H : ℝ) (n : ℕ) :
    normalizedPalatiniDefect H n ≤
      (Real.exp |H| * |H| ^ 3) * diagonalMesh n := by
  let h := diagonalMesh n
  have hp : 0 < h := diagonalMesh_pos n
  have hle : h ≤ 1 := diagonalMesh_le_one n
  have h43 : h ^ 4 ≤ h ^ 3 := by
    have hm := mul_nonneg (pow_nonneg hp.le 3) (sub_nonneg.mpr hle)
    nlinarith
  have hC : 0 ≤ Real.exp |H| * |H| ^ 3 := by positivity
  rw [normalizedPalatiniDefect, div_le_iff₀ (sq_pos_of_pos hp)]
  calc
    palatiniCellRemainder H h
        ≤ Real.exp |H| * |H| ^ 3 * |h| ^ 4 :=
      palatiniCellRemainder_le H h (by simpa [abs_of_pos hp] using hle)
    _ = (Real.exp |H| * |H| ^ 3) * h ^ 4 := by rw [abs_of_pos hp]
    _ ≤ (Real.exp |H| * |H| ^ 3) * h ^ 3 :=
      mul_le_mul_of_nonneg_left h43 hC
    _ = (Real.exp |H| * |H| ^ 3 * h) * h ^ 2 := by ring

/-- The diagonal mesh is summable; hence every nonnegative defect bounded by
`C_T h_n` is summable on a compact slab. -/
theorem diagonalMesh_summable : Summable diagonalMesh := by
  have hgeo : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  apply Summable.of_nonneg_of_le
    (fun n => pow_nonneg (by norm_num) (n ^ 2)) (fun n => ?_) hgeo
  apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
  simpa [pow_two] using Nat.le_mul_self n

/-- D5 without Taylor-rate hypotheses: the three explicit normalized defect
sequences are summable along `h_n = 2^{-n²}`. -/
theorem explicit_geometric_defects_summable (H : ℝ) :
    Summable (normalizedTorsionDefect H) ∧
      Summable (normalizedCurvatureDefect H) ∧
      Summable (normalizedPalatiniDefect H) := by
  refine ⟨?_, ?_, ?_⟩
  · exact Summable.of_nonneg_of_le
      (normalizedTorsionDefect_nonneg H)
      (normalizedTorsionDefect_le H)
      (diagonalMesh_summable.mul_left (Real.exp |H| * |H| ^ 2))
  · exact Summable.of_nonneg_of_le
      (normalizedCurvatureDefect_nonneg H)
      (normalizedCurvatureDefect_le H)
      (diagonalMesh_summable.mul_left (Real.exp (H ^ 2) * |H| ^ 4))
  · exact Summable.of_nonneg_of_le
      (normalizedPalatiniDefect_nonneg H)
      (normalizedPalatiniDefect_le H)
      (diagonalMesh_summable.mul_left (Real.exp |H| * |H| ^ 3))

theorem summable_of_defect_le_mesh (C : ℝ) (hC : 0 ≤ C)
    (defect : ℕ → ℝ) (hdefect : ∀ n, 0 ≤ defect n)
    (hbound : ∀ n, defect n ≤ C * diagonalMesh n) :
    Summable defect := by
  apply Summable.of_nonneg_of_le hdefect hbound
  exact diagonalMesh_summable.mul_left C

/-- D5 in one bundle: the normalized torsion, plaquette-curvature, and
Palatini first-variation defects are summable whenever their Taylor
remainders have the manuscript's `C_T h_n` bounds. -/
theorem geometric_defect_triple_summable
    (Ct Cc Cp : ℝ) (hCt : 0 ≤ Ct) (hCc : 0 ≤ Cc) (hCp : 0 ≤ Cp)
    (torsion curvature palatini : ℕ → ℝ)
    (ht0 : ∀ n, 0 ≤ torsion n) (hc0 : ∀ n, 0 ≤ curvature n)
    (hp0 : ∀ n, 0 ≤ palatini n)
    (ht : ∀ n, torsion n ≤ Ct * diagonalMesh n)
    (hc : ∀ n, curvature n ≤ Cc * diagonalMesh n)
    (hp : ∀ n, palatini n ≤ Cp * diagonalMesh n) :
    Summable torsion ∧ Summable curvature ∧ Summable palatini :=
  ⟨summable_of_defect_le_mesh Ct hCt torsion ht0 ht,
    summable_of_defect_le_mesh Cc hCc curvature hc0 hc,
    summable_of_defect_le_mesh Cp hCp palatini hp0 hp⟩

/-- D6: the curved port uses the same normalized relational-kernel
conservativity theorem, so forgetting it recovers the old Store branch. -/
theorem curved_port_forget_exact
    {O Γ Ξ Z d : Type*} [Fintype Γ] [Fintype Ξ] [Fintype Z]
    (K : RelationalCompletion.Kernel O Γ Ξ Z)
    (Φ : O → Matrix d d ℂ →ₗ[ℂ] Matrix d d ℂ)
    (o : O) (ρ : Z → Matrix d d ℂ) :
    RelationalCompletion.forgetRelation
        (RelationalCompletion.totalBranch K Φ o ρ) =
      Φ o (RelationalCompletion.forgetRelation ρ) :=
  RelationalCompletion.forget_totalBranch K Φ o ρ

end NCG.RelationalDeSitterBranch
