/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Numerics.IntervalKit

/-!
# The canonical modular CKM boundary certificate
  (`cert:canonical-ckm-main`, SM_emergence)

The certificate panel

  `|V_CKM| = [[0.9720205, 0.2348641, 0.0038712],
              [0.2347165, 0.9712079, 0.0407858],
              [0.0091827, 0.0399268, 0.9991604]]`,
  `|J_CKM| = 3.43619·10⁻⁵`, `δ_CKM = 72.5700°`

is realized by an explicit unitary matrix: `CKM.V` below is the
exact PDG product `U₂₃ · U₁₃(δ) · U₁₂` built from four exact
rational parameters (three sines and the tangent of the phase).

* `V_unitary` — `V V† = 1` exactly;
* `ckm_panel` — all nine moduli match the printed panel to half an
  ulp (`5·10⁻⁸`);
* `ckm_jarlskog` — the rephasing-invariant Jarlskog determinant
  matches `3.43619·10⁻⁵` within `5·10⁻¹¹`;
* `ckm_delta_deg` — the phase `δ = arctan t_δ` matches `72.5700°`
  within `5·10⁻⁵` degrees (`arctan` Taylor bracket + Mathlib's
  20-digit `π` bounds).

All inequalities are exact rational arithmetic.  The structural fact
making the certificate small: after eliminating `cos² = 1 - sin²`
and `cos²δ + sin²δ = 1`, every squared modulus is
`rational + rational · P` for the single irrational
`P = c₁₂c₂₃cos δ`, and the Jarlskog invariant is `rational · Q` for
`Q = c₁₂c₂₃sin δ`.
-/

namespace NCG

namespace CKM

open Complex Matrix

noncomputable section

/-- Exact rational boundary parameter `sin θ₁₂`. -/
def s12 : ℝ := 234865884089 / 1000000000000

/-- `sin θ₁₃`. -/
def s13 : ℝ := 193561 / 50000000

/-- `sin θ₂₃`. -/
def s23 : ℝ := 8157221123 / 200000000000

/-- `tan δ` — the CP phase has exact rational tangent. -/
def tD : ℝ := 796290765719 / 250000000000

/-- `cos θ₁₂`. -/
def c12 : ℝ := Real.sqrt (1 - s12 ^ 2)

/-- `cos θ₁₃`. -/
def c13 : ℝ := Real.sqrt (1 - s13 ^ 2)

/-- `cos θ₂₃`. -/
def c23 : ℝ := Real.sqrt (1 - s23 ^ 2)

/-- The phase hypotenuse `√(1 + tan²δ)`. -/
def hD : ℝ := Real.sqrt (1 + tD ^ 2)

/-- `cos δ = 1/√(1 + tan²δ)`. -/
def cD : ℝ := 1 / hD

/-- `sin δ = tan δ/√(1 + tan²δ)`. -/
def sD : ℝ := tD / hD

/-- `e^{-iδ}`. -/
def eD : ℂ := (cD : ℂ) - (sD : ℂ) * Complex.I

/-- `e^{+iδ}`. -/
def eDbar : ℂ := (cD : ℂ) + (sD : ℂ) * Complex.I

theorem c12_sq : c12 ^ 2 = 1 - s12 ^ 2 :=
  Real.sq_sqrt (by norm_num [s12])

theorem c13_sq : c13 ^ 2 = 1 - s13 ^ 2 :=
  Real.sq_sqrt (by norm_num [s13])

theorem c23_sq : c23 ^ 2 = 1 - s23 ^ 2 :=
  Real.sq_sqrt (by norm_num [s23])

theorem hD_sq : hD ^ 2 = 1 + tD ^ 2 :=
  Real.sq_sqrt (by positivity)

theorem hD_pos : 0 < hD :=
  Real.sqrt_pos.mpr (by positivity)

theorem phase_sq : cD ^ 2 + sD ^ 2 = 1 := by
  have h := hD_sq
  have h0 : hD ≠ 0 := hD_pos.ne'
  rw [cD, sD]
  field_simp
  linarith

/-- The `1-2` rotation factor. -/
def U12 : Matrix (Fin 3) (Fin 3) ℂ :=
  !![(c12 : ℂ), (s12 : ℂ), 0; -(s12 : ℂ), (c12 : ℂ), 0; 0, 0, 1]

/-- The `2-3` rotation factor. -/
def U23 : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1, 0, 0; 0, (c23 : ℂ), (s23 : ℂ); 0, -(s23 : ℂ), (c23 : ℂ)]

/-- The complex `1-3` rotation factor carrying the phase. -/
def U13 : Matrix (Fin 3) (Fin 3) ℂ :=
  !![(c13 : ℂ), 0, (s13 : ℂ) * eD; 0, 1, 0;
     -(s13 : ℂ) * eDbar, 0, (c13 : ℂ)]

/-- The exact modular CKM matrix in PDG order. -/
def V : Matrix (Fin 3) (Fin 3) ℂ := U23 * U13 * U12

theorem U12_unitary : U12 * U12.conjTranspose = 1 := by
  have h := c12_sq
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [U12, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.conjTranspose_apply, Complex.ext_iff,
      Complex.mul_re, Complex.mul_im] <;>
    nlinarith [h]

theorem U23_unitary : U23 * U23.conjTranspose = 1 := by
  have h := c23_sq
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [U23, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.conjTranspose_apply, Complex.ext_iff,
      Complex.mul_re, Complex.mul_im] <;>
    nlinarith [h]

set_option linter.flexible false in
theorem U13_unitary : U13 * U13.conjTranspose = 1 := by
  have h := c13_sq
  have hp := phase_sq
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [U13, eD, eDbar, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.conjTranspose_apply, Complex.ext_iff,
      Complex.mul_re, Complex.mul_im] <;>
    first
      | rfl
      | ring1
      | (constructor <;>
          first
            | trivial
            | (linear_combination h + s13 ^ 2 * hp)
            | ring1)

/-- The certificate matrix is exactly unitary. -/
theorem V_unitary : V * V.conjTranspose = 1 := by
  have hassoc : V * V.conjTranspose =
      U23 * (U13 * ((U12 * U12.conjTranspose) * U13.conjTranspose)) *
        U23.conjTranspose := by
    rw [V, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
    noncomm_ring
  rw [hassoc, U12_unitary, Matrix.one_mul, U13_unitary,
    Matrix.mul_one, U23_unitary]

/-! ## Squared moduli in `rational + rational · P` form -/

theorem nsq00 :
    Complex.normSq (V 0 0) = (1 - s12 ^ 2) * (1 - s13 ^ 2) := by
  have h : V 0 0 = (c13 : ℂ) * c12 := by
    simp [V, U12, U13, U23, Matrix.mul_apply, Fin.sum_univ_three]
  rw [h]
  simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  linear_combination (1 - s12 ^ 2) * c13_sq + c13 ^ 2 * c12_sq

theorem nsq01 : Complex.normSq (V 0 1) = s12 ^ 2 * (1 - s13 ^ 2) := by
  have h : V 0 1 = (c13 : ℂ) * s12 := by
    simp [V, U12, U13, U23, Matrix.mul_apply, Fin.sum_univ_three]
  rw [h]
  simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  linear_combination s12 ^ 2 * c13_sq

theorem nsq02 : Complex.normSq (V 0 2) = s13 ^ 2 := by
  have h : V 0 2 = (s13 : ℂ) * eD := by
    simp [V, U12, U13, U23, Matrix.mul_apply, Fin.sum_univ_three]
  rw [h]
  simp [Complex.normSq_apply, eD, Complex.mul_re, Complex.mul_im,
    Complex.sub_re, Complex.sub_im]
  linear_combination s13 ^ 2 * phase_sq

theorem nsq12 : Complex.normSq (V 1 2) = s23 ^ 2 * (1 - s13 ^ 2) := by
  have h : V 1 2 = (s23 : ℂ) * c13 := by
    simp [V, U12, U13, U23, Matrix.mul_apply, Fin.sum_univ_three]
  rw [h]
  simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  linear_combination s23 ^ 2 * c13_sq

theorem nsq22 :
    Complex.normSq (V 2 2) = (1 - s23 ^ 2) * (1 - s13 ^ 2) := by
  have h : V 2 2 = (c23 : ℂ) * c13 := by
    simp [V, U12, U13, U23, Matrix.mul_apply, Fin.sum_univ_three]
  rw [h]
  simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  linear_combination (1 - s23 ^ 2) * c13_sq + c13 ^ 2 * c23_sq

theorem nsq10 : Complex.normSq (V 1 0) =
    s12 ^ 2 * (1 - s23 ^ 2) + (1 - s12 ^ 2) * s23 ^ 2 * s13 ^ 2
      + 2 * (s12 * s23 * s13) * (c12 * c23 * cD) := by
  have h : V 1 0 = -(s12 : ℂ) * c23 - (c12 : ℂ) * s23 * s13 * eDbar := by
    simp [V, U12, U13, U23, Matrix.mul_apply, Fin.sum_univ_three]
    ring
  rw [h]
  simp [Complex.normSq_apply, eDbar, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im]
  linear_combination s12 ^ 2 * c23_sq
    + s23 ^ 2 * s13 ^ 2 * c12 ^ 2 * phase_sq
    + s23 ^ 2 * s13 ^ 2 * c12_sq

theorem nsq11 : Complex.normSq (V 1 1) =
    (1 - s12 ^ 2) * (1 - s23 ^ 2) + s12 ^ 2 * s23 ^ 2 * s13 ^ 2
      - 2 * (s12 * s23 * s13) * (c12 * c23 * cD) := by
  have h : V 1 1 = (c12 : ℂ) * c23 - (s12 : ℂ) * s23 * s13 * eDbar := by
    simp [V, U12, U13, U23, Matrix.mul_apply, Fin.sum_univ_three]
    ring
  rw [h]
  simp [Complex.normSq_apply, eDbar, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im]
  linear_combination c23 ^ 2 * c12_sq + (1 - s12 ^ 2) * c23_sq
    + s12 ^ 2 * s23 ^ 2 * s13 ^ 2 * phase_sq

theorem nsq20 : Complex.normSq (V 2 0) =
    s12 ^ 2 * s23 ^ 2 + (1 - s12 ^ 2) * (1 - s23 ^ 2) * s13 ^ 2
      - 2 * (s12 * s23 * s13) * (c12 * c23 * cD) := by
  have h : V 2 0 = (s12 : ℂ) * s23 - (c12 : ℂ) * c23 * s13 * eDbar := by
    simp [V, U12, U13, U23, Matrix.mul_apply, Fin.sum_univ_three]
    ring
  rw [h]
  simp [Complex.normSq_apply, eDbar, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im]
  linear_combination s13 ^ 2 * c23 ^ 2 * c12 ^ 2 * phase_sq
    + s13 ^ 2 * c23 ^ 2 * c12_sq + s13 ^ 2 * (1 - s12 ^ 2) * c23_sq

theorem nsq21 : Complex.normSq (V 2 1) =
    (1 - s12 ^ 2) * s23 ^ 2 + s12 ^ 2 * (1 - s23 ^ 2) * s13 ^ 2
      + 2 * (s12 * s23 * s13) * (c12 * c23 * cD) := by
  have h : V 2 1 = -(c12 : ℂ) * s23 - (s12 : ℂ) * c23 * s13 * eDbar := by
    simp [V, U12, U13, U23, Matrix.mul_apply, Fin.sum_univ_three]
    ring
  rw [h]
  simp [Complex.normSq_apply, eDbar, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im]
  linear_combination s23 ^ 2 * c12_sq
    + s12 ^ 2 * s13 ^ 2 * c23 ^ 2 * phase_sq + s12 ^ 2 * s13 ^ 2 * c23_sq

/-- The Jarlskog invariant in `rational · Q` form. -/
theorem jarlskog_eq :
    (V 0 1 * V 1 2 * (starRingEnd ℂ) (V 0 2) *
      (starRingEnd ℂ) (V 1 1)).im =
    s12 * s23 * s13 * (1 - s13 ^ 2) * (c12 * c23 * sD) := by
  have h01 : V 0 1 = (c13 : ℂ) * s12 := by
    simp [V, U12, U13, U23, Matrix.mul_apply, Fin.sum_univ_three]
  have h12 : V 1 2 = (s23 : ℂ) * c13 := by
    simp [V, U12, U13, U23, Matrix.mul_apply, Fin.sum_univ_three]
  have h02 : V 0 2 = (s13 : ℂ) * eD := by
    simp [V, U12, U13, U23, Matrix.mul_apply, Fin.sum_univ_three]
  have h11 : V 1 1 = (c12 : ℂ) * c23 - (s12 : ℂ) * s23 * s13 * eDbar := by
    simp [V, U12, U13, U23, Matrix.mul_apply, Fin.sum_univ_three]
    ring
  rw [h01, h12, h02, h11]
  simp [eD, eDbar, Complex.mul_re, Complex.mul_im, Complex.add_re,
    Complex.add_im, Complex.sub_re, Complex.sub_im, map_sub, map_mul,
    Complex.conj_ofReal, Complex.conj_I]
  linear_combination (s12 * s23 * s13 * c12 * c23 * sD) * c13_sq

/-! ## Certified enclosures -/

theorem c12_bounds :
    (0.9720277858637027 : ℝ) ≤ c12 ∧ c12 ≤ 0.9720277858637028 :=
  sqrt_mem_Icc (by norm_num) (by norm_num) (by norm_num [s12])
    (by norm_num [s12])

theorem c23_bounds :
    (0.9991679005996750 : ℝ) ≤ c23 ∧ c23 ≤ 0.9991679005996751 :=
  sqrt_mem_Icc (by norm_num) (by norm_num) (by norm_num [s23])
    (by norm_num [s23])

theorem hD_bounds :
    (3.3384522966652708 : ℝ) ≤ hD ∧ hD ≤ 3.3384522966652709 :=
  sqrt_mem_Icc (by norm_num) (by norm_num) (by norm_num [tD])
    (by norm_num [tD])

theorem cD_bounds :
    (0.2995399997174991 : ℝ) ≤ cD ∧ cD ≤ 0.2995399997174994 := by
  obtain ⟨hl, hr⟩ := hD_bounds
  have hp : (0 : ℝ) < hD := hD_pos
  constructor
  · unfold cD
    rw [le_div_iff₀ hp]
    nlinarith
  · unfold cD
    rw [div_le_iff₀ hp]
    nlinarith

theorem sD_bounds :
    (0.9540837429540660 : ℝ) ≤ sD ∧ sD ≤ 0.9540837429540663 := by
  obtain ⟨hl, hr⟩ := hD_bounds
  have hp : (0 : ℝ) < hD := hD_pos
  have htv : tD = 796290765719 / 250000000000 := rfl
  constructor
  · unfold sD
    rw [le_div_iff₀ hp]
    nlinarith [htv]
  · unfold sD
    rw [div_le_iff₀ hp]
    nlinarith [htv]

/-- The product atom `P = c₁₂c₂₃cos δ`. -/
theorem P_bounds :
    (0.2909189276408474 : ℝ) ≤ c12 * c23 * cD ∧
      c12 * c23 * cD ≤ 0.2909189276408484 := by
  obtain ⟨h12l, h12r⟩ := c12_bounds
  obtain ⟨h23l, h23r⟩ := c23_bounds
  obtain ⟨hcl, hcr⟩ := cD_bounds
  have hcc_l : (0.9712189621259861 : ℝ) ≤ c12 * c23 := by
    nlinarith [mul_le_mul h12l h23l (by norm_num) (by linarith)]
  have hcc_r : c12 * c23 ≤ (0.9712189621259866 : ℝ) := by
    nlinarith [mul_le_mul h12r h23r (by linarith) (by norm_num)]
  constructor
  · nlinarith [mul_le_mul hcc_l hcl (by norm_num) (by linarith)]
  · nlinarith [mul_le_mul hcc_r hcr (by linarith) (by norm_num)]

/-- The product atom `Q = c₁₂c₂₃sin δ`. -/
theorem Q_bounds :
    (0.9266242226131233 : ℝ) ≤ c12 * c23 * sD ∧
      c12 * c23 * sD ≤ 0.9266242226131257 := by
  obtain ⟨h12l, h12r⟩ := c12_bounds
  obtain ⟨h23l, h23r⟩ := c23_bounds
  obtain ⟨hsl, hsr⟩ := sD_bounds
  have hcc_l : (0.9712189621259861 : ℝ) ≤ c12 * c23 := by
    nlinarith [mul_le_mul h12l h23l (by norm_num) (by linarith)]
  have hcc_r : c12 * c23 ≤ (0.9712189621259866 : ℝ) := by
    nlinarith [mul_le_mul h12r h23r (by linarith) (by norm_num)]
  constructor
  · nlinarith [mul_le_mul hcc_l hsl (by norm_num) (by linarith)]
  · nlinarith [mul_le_mul hcc_r hsr (by linarith) (by norm_num)]

/-! ## The certificate panels -/

private theorem norm_as_sqrt (z : ℂ) :
    ‖z‖ = Real.sqrt (Complex.normSq z) := by
  rw [Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]

private theorem modulus_close (z : ℂ) (p t lo hi : ℝ)
    (hlo : 0 ≤ lo) (hnsq_lo : lo ^ 2 ≤ Complex.normSq z)
    (hnsq_hi : Complex.normSq z ≤ hi ^ 2) (hhi : 0 ≤ hi)
    (hplo : p - t ≤ lo) (hphi : hi ≤ p + t) :
    |‖z‖ - p| ≤ t := by
  rw [norm_as_sqrt, abs_le]
  constructor
  · linarith [le_sqrt_of_sq_le hlo hnsq_lo]
  · linarith [sqrt_le_of_le_sq hhi hnsq_hi]

theorem V00_close : |‖V 0 0‖ - 0.9720205| ≤ 5e-8 :=
  modulus_close _ _ _ 0.97202045 0.97202055 (by norm_num)
    (by rw [nsq00]; norm_num [s12, s13])
    (by rw [nsq00]; norm_num [s12, s13])
    (by norm_num) (by norm_num) (by norm_num)

theorem V01_close : |‖V 0 1‖ - 0.2348641| ≤ 5e-8 :=
  modulus_close _ _ _ 0.23486405 0.23486415 (by norm_num)
    (by rw [nsq01]; norm_num [s12, s13])
    (by rw [nsq01]; norm_num [s12, s13])
    (by norm_num) (by norm_num) (by norm_num)

theorem V02_close : |‖V 0 2‖ - 0.0038712| ≤ 5e-8 :=
  modulus_close _ _ _ 0.00387115 0.00387125 (by norm_num)
    (by rw [nsq02]; norm_num [s13])
    (by rw [nsq02]; norm_num [s13])
    (by norm_num) (by norm_num) (by norm_num)

theorem V12_close : |‖V 1 2‖ - 0.0407858| ≤ 5e-8 :=
  modulus_close _ _ _ 0.04078575 0.04078585 (by norm_num)
    (by rw [nsq12]; norm_num [s23, s13])
    (by rw [nsq12]; norm_num [s23, s13])
    (by norm_num) (by norm_num) (by norm_num)

theorem V22_close : |‖V 2 2‖ - 0.9991604| ≤ 5e-8 :=
  modulus_close _ _ _ 0.99916035 0.99916045 (by norm_num)
    (by rw [nsq22]; norm_num [s23, s13])
    (by rw [nsq22]; norm_num [s23, s13])
    (by norm_num) (by norm_num) (by norm_num)

theorem V10_close : |‖V 1 0‖ - 0.2347165| ≤ 5e-8 := by
  obtain ⟨hPl, hPr⟩ := P_bounds
  refine modulus_close _ _ _ 0.23471645 0.23471655 (by norm_num)
    ?_ ?_ (by norm_num) (by norm_num) (by norm_num)
  · rw [nsq10]
    simp only [s12, s13, s23]
    nlinarith
  · rw [nsq10]
    simp only [s12, s13, s23]
    nlinarith

theorem V11_close : |‖V 1 1‖ - 0.9712079| ≤ 5e-8 := by
  obtain ⟨hPl, hPr⟩ := P_bounds
  refine modulus_close _ _ _ 0.97120785 0.97120795 (by norm_num)
    ?_ ?_ (by norm_num) (by norm_num) (by norm_num)
  · rw [nsq11]
    simp only [s12, s13, s23]
    nlinarith
  · rw [nsq11]
    simp only [s12, s13, s23]
    nlinarith

theorem V20_close : |‖V 2 0‖ - 0.0091827| ≤ 5e-8 := by
  obtain ⟨hPl, hPr⟩ := P_bounds
  refine modulus_close _ _ _ 0.00918265 0.00918275 (by norm_num)
    ?_ ?_ (by norm_num) (by norm_num) (by norm_num)
  · rw [nsq20]
    simp only [s12, s13, s23]
    nlinarith
  · rw [nsq20]
    simp only [s12, s13, s23]
    nlinarith

theorem V21_close : |‖V 2 1‖ - 0.0399268| ≤ 5e-8 := by
  obtain ⟨hPl, hPr⟩ := P_bounds
  refine modulus_close _ _ _ 0.03992675 0.03992685 (by norm_num)
    ?_ ?_ (by norm_num) (by norm_num) (by norm_num)
  · rw [nsq21]
    simp only [s12, s13, s23]
    nlinarith
  · rw [nsq21]
    simp only [s12, s13, s23]
    nlinarith

/-- The printed decimal panel. -/
def panel : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0.9720205, 0.2348641, 0.0038712;
     0.2347165, 0.9712079, 0.0407858;
     0.0091827, 0.0399268, 0.9991604]

/-- `cert:canonical-ckm-main` (moduli): every entry of `|V|` matches
the printed decimal panel to half an ulp. -/
theorem ckm_panel : ∀ i j, |‖V i j‖ - panel i j| ≤ 5e-8 := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp only [panel] <;>
    first
    | simpa using V00_close
    | simpa using V01_close
    | simpa using V02_close
    | simpa using V10_close
    | simpa using V11_close
    | simpa using V12_close
    | simpa using V20_close
    | simpa using V21_close
    | simpa using V22_close

/-- `cert:canonical-ckm-main` (CP invariant): the Jarlskog
determinant of the certificate matrix is `3.43619·10⁻⁵` to half an
ulp of the printed value. -/
theorem ckm_jarlskog :
    |(V 0 1 * V 1 2 * (starRingEnd ℂ) (V 0 2) *
        (starRingEnd ℂ) (V 1 1)).im - 3.43619e-5| ≤ 5e-11 := by
  obtain ⟨hQl, hQr⟩ := Q_bounds
  rw [jarlskog_eq, abs_le]
  simp only [s12, s13, s23]
  constructor <;> nlinarith

/-- `cert:canonical-ckm-main` (phase): `δ = arctan t_δ` is
`72.5700°` to within `5·10⁻⁵` degrees. -/
theorem ckm_delta_deg :
    |Real.arctan tD * 180 / Real.pi - 72.5700| ≤ 5e-5 := by
  have ht : (0 : ℝ) < tD := by norm_num [tD]
  have hul : (0.3139556689123047 : ℝ) ≤ tD⁻¹ := by
    rw [tD]
    norm_num
  have hur : tD⁻¹ ≤ (0.3139556689123048 : ℝ) := by
    rw [tD]
    norm_num
  have hAlo : (0.30421047908 : ℝ) ≤ Real.arctan tD⁻¹ := by
    have h1 : (0.30421047908 : ℝ) ≤ atanLow 0.3139556689123047 := by
      unfold atanLow
      norm_num
    have h2 := atanLow_le_arctan
      (show (0 : ℝ) ≤ 0.3139556689123047 by norm_num)
    have h3 := Real.arctan_strictMono.monotone hul
    linarith
  have hAhi : Real.arctan tD⁻¹ ≤ (0.30421047925 : ℝ) := by
    have h1 : atanHigh 0.3139556689123048 ≤ (0.30421047925 : ℝ) := by
      unfold atanHigh atanLow
      norm_num
    have h2 := arctan_le_atanHigh
      (show (0 : ℝ) ≤ 0.3139556689123048 by norm_num)
    have h3 := Real.arctan_strictMono.monotone hur
    linarith
  have hπl : (3.14159265358979323846 : ℝ) < Real.pi := Real.pi_gt_d20
  have hπr : Real.pi < 3.14159265358979323847 := Real.pi_lt_d20
  have hπ0 : (0 : ℝ) < Real.pi := by linarith
  have hkey : Real.arctan tD * 180 / Real.pi
      = 90 - 180 * Real.arctan tD⁻¹ / Real.pi := by
    rw [arctan_inv_eq ht]
    field_simp
    ring
  have hd_hi : 180 * Real.arctan tD⁻¹ / Real.pi ≤
      180 * 0.30421047925 / 3.14159265358979323846 := by
    rw [div_le_div_iff₀ hπ0 (by norm_num)]
    nlinarith
  have hd_lo : 180 * 0.30421047908 / 3.14159265358979323847 ≤
      180 * Real.arctan tD⁻¹ / Real.pi := by
    rw [div_le_div_iff₀ (by norm_num) hπ0]
    nlinarith
  have hv_hi : (180 : ℝ) * 0.30421047925 / 3.14159265358979323846
      ≤ 17.43003 := by norm_num
  have hv_lo : (17.42997 : ℝ) ≤
      180 * 0.30421047908 / 3.14159265358979323847 := by norm_num
  rw [hkey, abs_le]
  constructor <;> linarith

end

end CKM

end NCG
