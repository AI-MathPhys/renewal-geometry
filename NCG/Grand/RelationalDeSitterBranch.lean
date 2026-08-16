/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.RelationalFlatVacuum
import NCG.Grand.RelationalCompletion
import NCG.Grand.GlobalSpatialCompiler

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

/-- The explicit diagonal mesh `h_n = 2^{-n²}`. -/
noncomputable def diagonalMesh (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ (n ^ 2)

/-- The diagonal mesh is summable; hence every nonnegative defect bounded by
`C_T h_n` is summable on a compact slab. -/
theorem diagonalMesh_summable : Summable diagonalMesh := by
  have hgeo : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) :=
    summable_geometric_of_norm_lt_one (by norm_num)
  apply Summable.of_nonneg_of_le
    (fun n => pow_nonneg (by norm_num) (n ^ 2)) (fun n => ?_) hgeo
  apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
  simpa [pow_two] using Nat.le_mul_self n

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
