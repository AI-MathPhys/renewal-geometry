/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.StandardModel.FiniteInterfaceRepresentationTable
import RenewalGeometry.Action.NativeDensitiesExact

/-!
# The lattice carrier of the renewal realization of the finite interface
  (`prop:renewal-interface`, items (I1)–(I3); Einstein–Standard-Model action-closure manuscript)

This file builds the finite carrier on which `RenewalGeometry.RenewalRealization` realizes
`def:finite-interface` on the minimal Standard-Model branch of `tab:SM-representations`.

* **Lorentzian coframe chart (I1).**  `chartCoframe p = L(p) U(p)` (`lowerF`, `upperF`): the
  Gauss (LU) chart of `GL(4, ℝ)` with `L` lower unitriangular and `U` upper triangular with
  diagonal `exp(p_ii)`.  It is a smooth chart of the 16 coframe components around the flat coframe
  (`chartCoframe_zero`), every chart coframe is oriented (`det_chartCoframe = exp(Σ p_ii) > 0`)
  and time-oriented (`chartCoframe_zero_zero = exp(p_00) > 0`), hence its metric `eᵀηe` is
  Lorentzian (`FiniteInterface.metric_det_neg`).
* **Link extension of the table representation (I2)/(I3).**  The gauge links of the realization are
  matrices `(L₃, L₂) ∈ M₃(ℂ) × M₂(ℂ)` in the defining representation of `G_SM = S(U(3) × U(2))`.
  `extRep L₃ L₂` extends the one-generation table representation `tableRepM` multiplicatively
  to all such pairs (`U₃ ⊗ U₂`, `\overline{det U₂} U₂`, `det U₂ · U₃`, `U₃`, `\overline{det U₂}`):
  `extRep_mul` and `extRep_smGauge : extRep (U₃(y)) (U₂(y)) = tableRepM y` (the inverse
  determinant is the conjugate determinant on the unitary group).
* **Yukawa blocks on the tabulated carrier (I3).**  `genEquiv : Fin 3 × Row ≃ MinIdx` identifies the
  generation-times-table-row carrier with the carrier of `lem:SM-descent`; under it the descent
  representation `rhoMin` is `tableRep ⊗ 1_gen` (`rhoMin_genEquiv`), and the covariant Yukawa map
  `yukawaMin` of `lem:SM-descent` becomes the generation-mixing operator `yukOp`, covariant under
  `G_SM` (`yukOp_covariant`).
-/

open Matrix
open scoped Kronecker

noncomputable section

namespace RenewalGeometry
namespace RenewalRealization

open NativeScaling (Mat)
open FiniteInterfaceTable SMDescentYukawa

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-! ### The Lorentzian coframe chart -/

/-- The lower unitriangular Gauss factor `L(p)`. -/
def lowerF (p : Mat) : Mat := fun i j => if i = j then 1 else if j < i then p i j else 0

/-- The upper triangular Gauss factor `U(p)` with positive diagonal `exp(p_ii)`. -/
def upperF (p : Mat) : Mat :=
  fun i j => if i = j then Real.exp (p i i) else if i < j then p i j else 0

/-- **The coframe chart** `e(p) = L(p) U(p)`: sixteen local coframe variables `p ∈ M₄(ℝ)`. -/
def chartCoframe (p : Mat) : Mat := lowerF p * upperF p

theorem lowerF_isLowerTriangular (p : Mat) : (lowerF p).IsLowerTriangular := by
  intro i j hij
  have hij' : i < j := hij
  simp [lowerF, hij'.ne, not_lt.mpr hij'.le]

theorem upperF_isUpperTriangular (p : Mat) : (upperF p).IsUpperTriangular := by
  intro i j hij
  have hij' : j < i := hij
  simp [upperF, hij'.ne', not_lt.mpr hij'.le]

theorem det_lowerF (p : Mat) : (lowerF p).det = 1 := by
  rw [det_of_isLowerTriangular _ (lowerF_isLowerTriangular p)]
  simp [lowerF]

theorem det_upperF (p : Mat) : (upperF p).det = Real.exp (∑ i, p i i) := by
  rw [det_of_isUpperTriangular (upperF_isUpperTriangular p), Real.exp_sum]
  simp [upperF]

/-- The chart determinant: `det e(p) = exp(Σ p_ii)`. -/
theorem det_chartCoframe (p : Mat) : (chartCoframe p).det = Real.exp (∑ i, p i i) := by
  rw [chartCoframe, det_mul, det_lowerF, det_upperF, one_mul]

/-- (I1) Every chart coframe is oriented. -/
theorem det_chartCoframe_pos (p : Mat) : 0 < (chartCoframe p).det := by
  rw [det_chartCoframe]; exact Real.exp_pos _

theorem det_chartCoframe_ne_zero (p : Mat) : (chartCoframe p).det ≠ 0 :=
  (det_chartCoframe_pos p).ne'

/-- The temporal component `e⁰₀(p) = exp(p₀₀)`. -/
theorem chartCoframe_zero_zero (p : Mat) : chartCoframe p 0 0 = Real.exp (p 0 0) := by
  simp [chartCoframe, Matrix.mul_apply, lowerF, upperF]

/-- (I1) Every chart coframe is time-oriented. -/
theorem chartCoframe_timeOriented (p : Mat) : 0 < chartCoframe p 0 0 := by
  rw [chartCoframe_zero_zero]; exact Real.exp_pos _

/-- The chart is centred at the flat coframe `e = 1` (`g = η`). -/
theorem chartCoframe_zero : chartCoframe 0 = 1 := by
  have hL : lowerF 0 = 1 := by
    ext i j; by_cases h : i = j <;> simp [lowerF, Matrix.one_apply, h]
  have hU : upperF 0 = 1 := by
    ext i j; by_cases h : i = j <;> simp [upperF, Matrix.one_apply, h]
  rw [chartCoframe, hL, hU, Matrix.one_mul]

/-- The chart entries are smooth. -/
theorem contDiff_chartCoframe_entry (a b : Fin 4) {k : WithTop ℕ∞} :
    ContDiff ℝ k (fun p : Mat => chartCoframe p a b) := by
  simp only [chartCoframe, Matrix.mul_apply]
  refine ContDiff.sum fun c _ => ContDiff.mul ?_ ?_
  · simp only [lowerF]
    split_ifs
    · exact contDiff_const
    · exact (contDiff_apply_apply ℝ ℝ a c)
    · exact contDiff_const
  · simp only [upperF]
    split_ifs with h
    · subst h; exact Real.contDiff_exp.comp (contDiff_apply_apply ℝ ℝ c c)
    · exact (contDiff_apply_apply ℝ ℝ c b)
    · exact contDiff_const

/-! ### The minimal-branch one-generation rows and the link extension of `tableRep` -/

/-- The one-generation row index of the minimal branch of `tab:SM-representations`
(`TableRow .minimal`, with its block structure unfolded). -/
abbrev Row : Type := LeftRow ⊕ RightRowMin

/-- The one-generation table representation of the minimal branch on `Row`. -/
def tableRepM : SMGaugeGroup →* Matrix Row Row ℂ := tableRep (NeutrinoBranch.minimal)

theorem tableRepM_apply (y : SMGaugeGroup) : tableRepM y =
    fromBlocks (fromBlocks (smU3 y ⊗ₖ smU2 y) 0 0 ((smU2 y).det ^ (-1 : ℤ) • smU2 y)) 0 0
      (fromBlocks (fromBlocks ((smU2 y).det ^ (1 : ℤ) • smU3 y) 0 0 (smU3 y)) 0 0
        ((smU2 y).det ^ (-1 : ℤ) • (1 : Matrix Unit Unit ℂ))) := rfl

/-- **The multiplicative link extension of the table representation**:
`(L₃, L₂) ↦ diag(L₃ ⊗ L₂, \overline{det L₂} L₂ | det L₂ · L₃, L₃, \overline{det L₂})` on the rows
`Q_L, L_L | u_R, d_R, e_R`. -/
def extRep (A3 : Matrix (Fin 3) (Fin 3) ℂ) (A2 : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix Row Row ℂ :=
  fromBlocks (fromBlocks (A3 ⊗ₖ A2) 0 0 (star A2.det • A2)) 0 0
    (fromBlocks (fromBlocks (A2.det • A3) 0 0 A3) 0 0 (star A2.det • (1 : Matrix Unit Unit ℂ)))

theorem extRep_mul (A3 B3 : Matrix (Fin 3) (Fin 3) ℂ) (A2 B2 : Matrix (Fin 2) (Fin 2) ℂ) :
    extRep (A3 * B3) (A2 * B2) = extRep A3 A2 * extRep B3 B2 := by
  simp only [extRep, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
    det_mul, star_mul', mul_kronecker_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.one_mul, mul_comm (star B2.det), mul_comm B2.det, smul_zero]

theorem extRep_one : extRep 1 1 = 1 := by
  simp [extRep, fromBlocks_one]

/-- On the unitary group the inverse determinant is the conjugate determinant. -/
theorem smChi_zpow_neg_one (y : SMGaugeGroup) : smChi y ^ (-1 : ℤ) = star (smU2 y).det := by
  have h := smChi_star y
  rw [_root_.zpow_neg_one]
  exact (eq_inv_of_mul_eq_one_left h).symm

/-- **The link extension restricts to the table representation on `G_SM`.** -/
theorem extRep_smGauge (y : SMGaugeGroup) :
    extRep (smU3 y) (smU2 y) = tableRepM y := by
  have h1 := smChi_zpow_neg_one y
  simp only [smChi_apply] at h1
  rw [tableRepM_apply, h1, zpow_one]
  rfl

/-- `U₃(y⁻¹) = U₃(y)^*`. -/
theorem smU3_inv (y : SMGaugeGroup) : smU3 y⁻¹ = star (smU3 y) := rfl

/-- `U₂(y⁻¹) = U₂(y)^*`. -/
theorem smU2_inv (y : SMGaugeGroup) : smU2 y⁻¹ = star (smU2 y) := rfl

theorem extRep_star_smGauge (y : SMGaugeGroup) :
    extRep (star (smU3 y)) (star (smU2 y)) = tableRepM y⁻¹ := by
  rw [← smU3_inv, ← smU2_inv, extRep_smGauge]

theorem tableRep_inv_mul (y : SMGaugeGroup) :
    tableRepM y⁻¹ * tableRepM y = 1 := by
  rw [← map_mul, inv_mul_cancel, map_one]

theorem tableRep_mul_inv (y : SMGaugeGroup) :
    tableRepM y * tableRepM y⁻¹ = 1 := by
  rw [← map_mul, mul_inv_cancel, map_one]

theorem smU3_star_mul (y : SMGaugeGroup) : star (smU3 y) * smU3 y = 1 :=
  (Unitary.mem_iff.mp (smU3_mem y)).1

theorem smU3_mul_star (y : SMGaugeGroup) : smU3 y * star (smU3 y) = 1 :=
  (Unitary.mem_iff.mp (smU3_mem y)).2

theorem smU2_star_mul (y : SMGaugeGroup) : star (smU2 y) * smU2 y = 1 :=
  (Unitary.mem_iff.mp (smU2_mem y)).1

theorem smU2_mul_star (y : SMGaugeGroup) : smU2 y * star (smU2 y) = 1 :=
  (Unitary.mem_iff.mp (smU2_mem y)).2

/-- Covariance of the extended link transport:
`extRep(g L g'^*) = tableRep(g) extRep(L) tableRep(g')⁻¹`. -/
theorem extRep_gauge (y y' : SMGaugeGroup) (A3 : Matrix (Fin 3) (Fin 3) ℂ)
    (A2 : Matrix (Fin 2) (Fin 2) ℂ) :
    extRep (smU3 y * A3 * star (smU3 y')) (smU2 y * A2 * star (smU2 y')) =
      tableRepM y * extRep A3 A2 * tableRepM y'⁻¹ := by
  rw [extRep_mul, extRep_mul, extRep_smGauge, extRep_star_smGauge]

/-! ### Yukawa blocks on the generation × table-row carrier -/

/-- The identification `Fin 3 × Row ≃ MinIdx` of the generation-times-table-row carrier with the
carrier `(Q_L ⊕ L_L) ⊕ (u_R ⊕ d_R ⊕ e_R)` (generation inside) of `lem:SM-descent`. -/
def genEquiv : Fin 3 × Row ≃ MinIdx where
  toFun p := match p with
    | (g, .inl (.inl q)) => .inl (.inl (q, g))
    | (g, .inl (.inr l)) => .inl (.inr (l, g))
    | (g, .inr (.inl (.inl u))) => .inr (.inl (.inl (u, g)))
    | (g, .inr (.inl (.inr d))) => .inr (.inl (.inr (d, g)))
    | (g, .inr (.inr e)) => .inr (.inr (e, g))
  invFun i := match i with
    | .inl (.inl (q, g)) => (g, .inl (.inl q))
    | .inl (.inr (l, g)) => (g, .inl (.inr l))
    | .inr (.inl (.inl (u, g))) => (g, .inr (.inl (.inl u)))
    | .inr (.inl (.inr (d, g))) => (g, .inr (.inl (.inr d)))
    | .inr (.inr (e, g)) => (g, .inr (.inr e))
  left_inv p := by
    rcases p with ⟨g, (q | l) | ((u | d) | e)⟩ <;> rfl
  right_inv i := by
    rcases i with (⟨q, g⟩ | ⟨l, g⟩) | ((⟨u, g⟩ | ⟨d, g⟩) | ⟨e, g⟩) <;> rfl

/-- Under `genEquiv` the descent representation is `tableRep ⊗ 1_gen`. -/
theorem rhoMin_genEquiv (y : SMGaugeGroup) (p p' : Fin 3 × Row) :
    rhoMin y (genEquiv p) (genEquiv p') =
      tableRepM y p.2 p'.2 * (1 : Matrix (Fin 3) (Fin 3) ℂ) p.1 p'.1 := by
  rcases p with ⟨g, (q | l) | ((u | d) | e)⟩ <;>
  rcases p' with ⟨g', (q' | l') | ((u' | d') | e')⟩ <;>
  first | rfl | exact (zero_mul (M₀ := ℂ) _).symm

/-- The minimal Yukawa bank built from the three Yukawa sectors `u, d, e` of a coefficient bank. -/
def ybank (θ : CoefficientBank (Fin 3)) : YukawaBank where
  Yu := θ.yukawa 0
  Yd := θ.yukawa 1
  Ye := θ.yukawa 2
  Yn := 0
  MR := 0
  MR_symm := by simp

/-- Flattening of generation-times-row spinors. -/
def flat (φ : Fin 3 → Row → ℂ) : Fin 3 × Row → ℂ := fun p => φ p.1 p.2

/-- The Yukawa matrix of `lem:SM-descent` on the generation-times-row carrier. -/
def yM (θ : CoefficientBank (Fin 3)) (H : Fin 2 → ℂ) : Matrix (Fin 3 × Row) (Fin 3 × Row) ℂ :=
  (yukawaMin (ybank θ) H).submatrix genEquiv genEquiv

/-- **The Yukawa operator** `𝓜_𝐘(H)` of `lem:SM-descent` on generation-times-table-row spinors
`φ : Fin 3 → Row → ℂ`. -/
def yukOp (θ : CoefficientBank (Fin 3)) (H : Fin 2 → ℂ) (φ : Fin 3 → Row → ℂ) :
    Fin 3 → Row → ℂ :=
  fun g r => (yM θ H *ᵥ flat φ) (g, r)

theorem yukOp_add (θ : CoefficientBank (Fin 3)) (H : Fin 2 → ℂ) (φ φ' : Fin 3 → Row → ℂ) :
    yukOp θ H (φ + φ') = yukOp θ H φ + yukOp θ H φ' := by
  have : flat (φ + φ') = flat φ + flat φ' := rfl
  funext g r
  simp only [yukOp, this, Matrix.mulVec_add, Pi.add_apply]

theorem yukOp_smul (θ : CoefficientBank (Fin 3)) (H : Fin 2 → ℂ) (c : ℂ)
    (φ : Fin 3 → Row → ℂ) : yukOp θ H (c • φ) = c • yukOp θ H φ := by
  have : flat (c • φ) = c • flat φ := rfl
  funext g r
  simp only [yukOp, this, Matrix.mulVec_smul, Pi.smul_apply]

/-- The reindexed descent representation acts row-wise by the table representation. -/
theorem rhoMin_submatrix_mulVec (y : SMGaugeGroup) (φ : Fin 3 → Row → ℂ) :
    (rhoMin y).submatrix genEquiv genEquiv *ᵥ flat φ =
      flat (fun g => tableRepM y *ᵥ φ g) := by
  funext ⟨g, r⟩
  simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply, rhoMin_genEquiv, flat,
    Fintype.sum_prod_type, Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  rw [Finset.sum_eq_single g (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
  simp

/-- **Covariance of the Yukawa operator**: `𝓜(ρ_H(g) H)(ρ(g) φ) = ρ(g) 𝓜(H) φ`. -/
theorem yukOp_covariant (θ : CoefficientBank (Fin 3)) (y : SMGaugeGroup) (H : Fin 2 → ℂ)
    (φ : Fin 3 → Row → ℂ) (g : Fin 3) :
    yukOp θ (smU2 y *ᵥ H) (fun g' => tableRepM y *ᵥ φ g') g =
      tableRepM y *ᵥ yukOp θ H φ g := by
  have hcov : yM θ (smU2 y *ᵥ H) * (rhoMin y).submatrix genEquiv genEquiv =
      (rhoMin y).submatrix genEquiv genEquiv * yM θ H := by
    have := yukawaMin_covariant (ybank θ) y H
    simp only [yM, Matrix.submatrix_mul_equiv]
    rw [show repH y = smU2 y from rfl] at this
    rw [this]
  funext r
  have h3 := congrFun (rhoMin_submatrix_mulVec y (yukOp θ H φ)) (g, r)
  simp only [flat] at h3
  rw [← h3]
  have hflat : flat (yukOp θ H φ) = yM θ H *ᵥ flat φ := rfl
  simp only [yukOp, ← rhoMin_submatrix_mulVec, Matrix.mulVec_mulVec, hcov]
  rw [← Matrix.mulVec_mulVec, ← hflat]

/-! ### The finite configuration space `𝒬_h` -/

open ShiftedJetAction (Grid unitVec)

/-- The real coordinates of one lattice site: the sixteen coframe chart variables, the Higgs
doublet, the colour and weak link matrices of the four forward links, and the spinor and
independent dual spinor (generation × table row), complex entries split into real and imaginary
parts (`false`/`true`). -/
inductive Coord : Type
  | frame (a b : Fin 4)
  | higgs (i : Fin 2) (c : Bool)
  | l3 (μ : Fin 4) (a b : Fin 3) (c : Bool)
  | l2 (μ : Fin 4) (a b : Fin 2) (c : Bool)
  | psi (g : Fin 3) (r : Row) (c : Bool)
  | psib (g : Fin 3) (r : Row) (c : Bool)
  deriving DecidableEq, Fintype

/-- **The finite configuration space** `𝒬_h = ℝ^{sites × coordinates}` with its Euclidean
structure, on the periodic lattice `(ℤ/n)⁴`. -/
abbrev Config (n : ℕ) [NeZero n] := EuclideanSpace ℝ (Grid n × Coord)

/-- A complex number from its real and imaginary coordinates. -/
def cpx (a b : ℝ) : ℂ := ⟨a, b⟩

/-- The real (`false`) or imaginary (`true`) part. -/
def cpart : Bool → ℂ → ℝ
  | false, z => z.re
  | true, z => z.im

@[simp] theorem cpx_cpart (z : ℂ) : cpx (cpart false z) (cpart true z) = z := rfl

theorem cpx_eq (a b : ℝ) : cpx a b = (a : ℂ) + (b : ℂ) * Complex.I := by
  apply Complex.ext <;> simp [cpx]

variable {n : ℕ} [NeZero n]

/-- The coframe chart variables at a site. -/
def prm (q : Config n) (x : Grid n) : Mat := fun a b => q (x, .frame a b)

/-- (I1) **The local coframe** `e(x) = L(p(x)) U(p(x))`. -/
def frameE (q : Config n) (x : Grid n) : Mat := chartCoframe (prm q x)

/-- (I2) The Higgs doublet at a site. -/
def hig (q : Config n) (x : Grid n) : Fin 2 → ℂ :=
  fun i => cpx (q (x, .higgs i false)) (q (x, .higgs i true))

/-- The colour link `L₃,μ(x)` from `x` to `x + e_μ`. -/
def lk3 (q : Config n) (μ : Fin 4) (x : Grid n) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun a b => cpx (q (x, .l3 μ a b false)) (q (x, .l3 μ a b true))

/-- The weak link `L₂,μ(x)` from `x` to `x + e_μ`. -/
def lk2 (q : Config n) (μ : Fin 4) (x : Grid n) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun a b => cpx (q (x, .l2 μ a b false)) (q (x, .l2 μ a b true))

/-- The spinor at a site (generation × table row). -/
def psiF (q : Config n) (x : Grid n) : Fin 3 → Row → ℂ :=
  fun g r => cpx (q (x, .psi g r false)) (q (x, .psi g r true))

/-- The independent dual spinor at a site. -/
def psibF (q : Config n) (x : Grid n) : Fin 3 → Row → ℂ :=
  fun g r => cpx (q (x, .psib g r false)) (q (x, .psib g r true))

/-! ### Site gauge transformations -/

/-- The transformed coordinates under a site gauge `γ : Grid → G_SM`:
`H ↦ U₂(γ_x) H`, `L_μ(x) ↦ γ_x L_μ(x) γ_{x+e_μ}^*` (colour and weak blocks),
`Ψ ↦ ρ(γ_x) Ψ`, `Ψ̄ ↦ Ψ̄ ρ(γ_x)⁻¹`; the coframe is internal-gauge neutral. -/
def gaugeCoord (γ : Grid n → SMGaugeGroup) (q : Config n) (x : Grid n) : Coord → ℝ
  | .frame a b => q (x, .frame a b)
  | .higgs i c => cpart c ((smU2 (γ x) *ᵥ hig q x) i)
  | .l3 μ a b c => cpart c ((smU3 (γ x) * lk3 q μ x * star (smU3 (γ (x + unitVec n μ)))) a b)
  | .l2 μ a b c => cpart c ((smU2 (γ x) * lk2 q μ x * star (smU2 (γ (x + unitVec n μ)))) a b)
  | .psi g r c => cpart c ((tableRepM (γ x) *ᵥ psiF q x g) r)
  | .psib g r c => cpart c ((psibF q x g ᵥ* tableRepM (γ x)⁻¹) r)

/-- **The finite gauge action** of site gauges `γ : Grid → G_SM` on `𝒬_h`. -/
def gaugeAct (γ : Grid n → SMGaugeGroup) (q : Config n) : Config n :=
  WithLp.toLp 2 fun p => gaugeCoord γ q p.1 p.2

@[simp] theorem prm_gaugeAct (γ : Grid n → SMGaugeGroup) (q : Config n) (x : Grid n) :
    prm (gaugeAct γ q) x = prm q x := by
  funext a b; simp [prm, gaugeAct, gaugeCoord]

@[simp] theorem frameE_gaugeAct (γ : Grid n → SMGaugeGroup) (q : Config n) (x : Grid n) :
    frameE (gaugeAct γ q) x = frameE q x := by
  simp [frameE]

@[simp] theorem hig_gaugeAct (γ : Grid n → SMGaugeGroup) (q : Config n) (x : Grid n) :
    hig (gaugeAct γ q) x = smU2 (γ x) *ᵥ hig q x := by
  funext i; simp [hig, gaugeAct, gaugeCoord]

@[simp] theorem lk3_gaugeAct (γ : Grid n → SMGaugeGroup) (q : Config n) (μ : Fin 4)
    (x : Grid n) :
    lk3 (gaugeAct γ q) μ x = smU3 (γ x) * lk3 q μ x * star (smU3 (γ (x + unitVec n μ))) := by
  funext a b; simp [lk3, gaugeAct, gaugeCoord]

@[simp] theorem lk2_gaugeAct (γ : Grid n → SMGaugeGroup) (q : Config n) (μ : Fin 4)
    (x : Grid n) :
    lk2 (gaugeAct γ q) μ x = smU2 (γ x) * lk2 q μ x * star (smU2 (γ (x + unitVec n μ))) := by
  funext a b; simp [lk2, gaugeAct, gaugeCoord]

@[simp] theorem psiF_gaugeAct (γ : Grid n → SMGaugeGroup) (q : Config n) (x : Grid n) :
    psiF (gaugeAct γ q) x = fun g => tableRepM (γ x) *ᵥ psiF q x g := by
  funext g r; simp [psiF, gaugeAct, gaugeCoord]

@[simp] theorem psibF_gaugeAct (γ : Grid n → SMGaugeGroup) (q : Config n) (x : Grid n) :
    psibF (gaugeAct γ q) x = fun g => psibF q x g ᵥ* tableRepM (γ x)⁻¹ := by
  funext g r; simp [psibF, gaugeAct, gaugeCoord]

/-! ### (I3) The gauge-covariant finite Dirac/Yukawa incidence operator -/

/-- The backward-transported link `L_μ(x - e_μ)^*` (colour block). -/
def bk3 (q : Config n) (μ : Fin 4) (x : Grid n) : Matrix (Fin 3) (Fin 3) ℂ :=
  star (lk3 q μ (x - unitVec n μ))

/-- The backward-transported link `L_μ(x - e_μ)^*` (weak block). -/
def bk2 (q : Config n) (μ : Fin 4) (x : Grid n) : Matrix (Fin 2) (Fin 2) ℂ :=
  star (lk2 q μ (x - unitVec n μ))

/-- **The finite Dirac/Yukawa incidence operator** at cutoff `h` on spinor fields
`ψ : Grid → Fin 3 → Row → ℂ`: the link-transported central lattice difference
`Σ_μ (2h)⁻¹ [ρ(L_μ(x)) ψ(x + e_μ) - ρ(L_μ(x - e_μ)^*) ψ(x - e_μ)]` plus the covariant Yukawa
blocks `𝓜_𝐘(H(x)) ψ(x)` of `lem:SM-descent`. -/
def diracFun (θ : CoefficientBank (Fin 3)) (h : ℝ) (q : Config n)
    (ψ : Grid n → Fin 3 → Row → ℂ) (x : Grid n) (g : Fin 3) : Row → ℂ :=
  (∑ μ, (2 * h)⁻¹ • (extRep (lk3 q μ x) (lk2 q μ x) *ᵥ ψ (x + unitVec n μ) g -
      extRep (bk3 q μ x) (bk2 q μ x) *ᵥ ψ (x - unitVec n μ) g)) +
    yukOp θ (hig q x) (ψ x) g

/-- The incidence operator as a `ℂ`-linear map on spinor fields. -/
def diracOp (θ : CoefficientBank (Fin 3)) (h : ℝ) (q : Config n) :
    (Grid n → Fin 3 → Row → ℂ) →ₗ[ℂ] (Grid n → Fin 3 → Row → ℂ) where
  toFun ψ := fun x g => diracFun θ h q ψ x g
  map_add' ψ ψ' := by
    funext x g
    simp only [diracFun, Pi.add_apply, Matrix.mulVec_add]
    rw [yukOp_add]
    simp only [Pi.add_apply, smul_sub, smul_add, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    abel
  map_smul' c ψ := by
    funext x g
    simp only [diracFun, Pi.smul_apply, Matrix.mulVec_smul, RingHom.id_apply]
    rw [yukOp_smul]
    simp only [Pi.smul_apply, smul_add, Finset.smul_sum, smul_sub]
    congr 1
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [smul_comm c (2 * h)⁻¹, smul_comm c (2 * h)⁻¹]

theorem diracOp_apply (θ : CoefficientBank (Fin 3)) (h : ℝ) (q : Config n)
    (ψ : Grid n → Fin 3 → Row → ℂ) (x : Grid n) (g : Fin 3) :
    diracOp θ h q ψ x g = diracFun θ h q ψ x g := rfl

theorem star_gauge_link {m : Type*} [Fintype m] [DecidableEq m] (a b L : Matrix m m ℂ) :
    star (a * L * star b) = b * star L * star a := by
  simp only [star_mul, star_star, Matrix.mul_assoc]

/-- **(I3) Gauge covariance of the incidence operator**:
`D_{γ·q}(ρ(γ) ψ)(x) = ρ(γ_x) D_q ψ(x)`. -/
theorem diracFun_covariant (θ : CoefficientBank (Fin 3)) (h : ℝ) (γ : Grid n → SMGaugeGroup)
    (q : Config n) (ψ : Grid n → Fin 3 → Row → ℂ) (x : Grid n) (g : Fin 3) :
    diracFun θ h (gaugeAct γ q) (fun y m => tableRepM (γ y) *ᵥ ψ y m) x g =
      tableRepM (γ x) *ᵥ diracFun θ h q ψ x g := by
  have hb3 : ∀ μ, bk3 (gaugeAct γ q) μ x =
      smU3 (γ x) * bk3 q μ x * star (smU3 (γ (x - unitVec n μ))) := by
    intro μ
    simp only [bk3, lk3_gaugeAct, sub_add_cancel, star_gauge_link]
  have hb2 : ∀ μ, bk2 (gaugeAct γ q) μ x =
      smU2 (γ x) * bk2 q μ x * star (smU2 (γ (x - unitVec n μ))) := by
    intro μ
    simp only [bk2, lk2_gaugeAct, sub_add_cancel, star_gauge_link]
  simp only [diracFun, lk3_gaugeAct, lk2_gaugeAct, hb3, hb2, extRep_gauge, hig_gaugeAct,
    yukOp_covariant]
  simp only [Matrix.mulVec_add, Matrix.mulVec_sum, Matrix.mulVec_smul, Matrix.mulVec_sub,
    Matrix.mulVec_mulVec, Matrix.mul_assoc, tableRep_inv_mul, Matrix.mul_one]

end RenewalRealization
end RenewalGeometry
