/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.UhlenbeckStandardModel

/-!
# `G_SM`-valued gauges preserve `𝔰(𝔲(3) ⊕ 𝔲(2))`-valued connections
  (`thm:critical-quotient-defect`, `lem:equivariant-tests`; Einstein–Standard-Model
  action-closure manuscript)

For a differentiable gauge `R : U → G_SM = S(U(3) × U(2))` on an open set `U ⊆ ℝ⁴`, the
Maurer–Cartan form `(∂_μR) R⁻¹ = (∂_μR) R^*` takes values in the Lie algebra
`𝔤_SM = 𝔰(𝔲(3) ⊕ 𝔲(2))` (`pdM_mul_star_mem_gSM`), shown directly from the explicit description of
`G_SM`:

* **skew-Hermitian**: `∂R R^* + R ∂R^* = 0` (derivative of `R R^* = 1`);
* **block-diagonal**: the off-block entries of `R` vanish identically near `x`, so do their
  derivatives (`isSMBlock_pdM`);
* **trace zero**: `tr(R^* ∂R) = ∂_μ det(R^*(x) R(·))|_x = 0` (`trace_star_mul_pdM_eq_zero`), from
  the Leibniz derivative of the determinant along a real line (`hasDerivAt_det_real`) and
  `detDerivAt 1 D = tr D` (`MatrixDetExp.detDerivAt_one`); `det(R^*(x) R(y)) = 1` near `x`.

Consequently the gauge-transformed connection `R·A = R A R^* - (∂R) R^*` of an
`𝔰(𝔲(3) ⊕ 𝔲(2))`-valued connection is again `𝔰(𝔲(3) ⊕ 𝔲(2))`-valued (`gaugeConn_mem_gSM`,
`gaugeConn_mem_smLie`), and the transported matter fields transform in the `G_SM`
representations: the defining representation `ℂ³ ⊕ ℂ²` (spinors), its restriction to the weak
block `ℂ²` (the Higgs doublet, `mulVec_doublet`), and the conjugate representation
`R ↦ R̄ = (R^*)ᵀ ∈ G_SM` (dual spinors, `dualGauge_mem_GSM`).  `uhlenbeck_cover_SM_lie` records the
consequence for the Coulomb charts of `UhlenbeckStandardModel`.
-/

open MeasureTheory Filter Topology Set Matrix
open scoped ENNReal NNReal ContDiff ComplexConjugate

noncomputable section

namespace RenewalGeometry.SMGaugeLie

open SobolevOpen CriticalGauge CriticalQuotient BallAnalysis.SMGaugeStructure EinsteinSM

set_option linter.unusedSectionVars false

/-! ### `G_SM` is closed under `^*` and under entrywise conjugation -/

theorem isSMBlock_star {X : M5} (h : IsSMBlock X) : IsSMBlock (star X) := by
  intro i j hij
  simp only [star_apply]
  rw [h j i (Ne.symm hij), star_zero]

theorem isSMBlock_transpose {X : M5} (h : IsSMBlock X) : IsSMBlock Xᵀ := fun i j hij =>
  h j i (Ne.symm hij)

theorem star_mem_GSM {g : M5} (hg : g ∈ GSM) : star g ∈ GSM := by
  refine ⟨Unitary.star_mem hg.1, isSMBlock_star hg.2.1, ?_⟩
  rw [star_eq_conjTranspose, det_conjTranspose, hg.2.2, star_one]

/-- The conjugate representation: `R̄ = (R^*)ᵀ ∈ G_SM` for `R ∈ G_SM`. -/
theorem conjTranspose_transpose_mem_GSM {g : M5} (hg : g ∈ GSM) : (star g)ᵀ ∈ GSM := by
  have hs := star_mem_GSM hg
  refine ⟨?_, isSMBlock_transpose hs.2.1, by rw [det_transpose, hs.2.2]⟩
  rw [mem_unitaryGroup_iff]
  have h := mem_unitaryGroup_iff.mp hg.1
  rw [star_eq_conjTranspose, star_eq_conjTranspose,
    conjTranspose_transpose_eq_transpose_conjTranspose, conjTranspose_conjTranspose,
    ← transpose_mul, ← star_eq_conjTranspose, h, transpose_one]

/-- The dual gauge of a `G_SM`-valued gauge is `G_SM`-valued. -/
theorem dualGauge_mem_GSM {R : (Fin 4 → ℝ) → M5} {y : Fin 4 → ℝ} (hR : R y ∈ GSM) :
    dualGauge R y ∈ GSM :=
  conjTranspose_transpose_mem_GSM hR

/-! ### Derivatives of off-block entries -/

theorem pd_eq_zero_of_eventually {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : (Fin 4 → ℝ) → F} {x : Fin 4 → ℝ} (h : f =ᶠ[𝓝 x] fun _ => 0) (μ : Fin 4) :
    pd f μ x = 0 := by
  unfold pd; rw [h.fderiv_eq]; simp

/-- The derivative of a block-diagonal-valued map is block-diagonal. -/
theorem isSMBlock_pdM {R : (Fin 4 → ℝ) → M5} {U : Set (Fin 4 → ℝ)} (hU : IsOpen U)
    (hR : ∀ y ∈ U, IsSMBlock (R y)) {x : Fin 4 → ℝ} (hx : x ∈ U) (μ : Fin 4) :
    IsSMBlock (pdM R μ x) := by
  intro i j hij
  simp only [pdM, of_apply]
  refine pd_eq_zero_of_eventually ?_ μ
  filter_upwards [hU.mem_nhds hx] with y hy using hR y hy i j hij

/-! ### The derivative of the determinant along a real line -/

/-- **Leibniz derivative of `det` along a real curve of complex matrices**: if every entry of
`γ : ℝ → Mₙ(ℂ)` has derivative `D a b` at `t`, then `s ↦ det (γ s)` has derivative
`detDerivAt (γ t) D` at `t`. -/
theorem hasDerivAt_det_real {n : Type*} [Fintype n] [DecidableEq n] {γ : ℝ → Matrix n n ℂ}
    {D : Matrix n n ℂ} {t : ℝ} (h : ∀ a b, HasDerivAt (fun s => γ s a b) (D a b) t) :
    HasDerivAt (fun s => (γ s).det) (MatrixDetExp.detDerivAt (γ t) D) t := by
  have hfun : (fun s => (γ s).det) =
      fun s => ∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, γ s (σ i) i := by
    funext s
    rw [Matrix.det_apply']
  rw [hfun]
  unfold MatrixDetExp.detDerivAt
  apply HasDerivAt.fun_sum
  intro σ _
  apply HasDerivAt.const_mul
  have := HasDerivAt.fun_finsetProd (u := Finset.univ) (f := fun i s => γ s (σ i) i)
    (f' := fun i => D (σ i) i) (fun i _ => h _ _)
  simpa [smul_eq_mul] using this

/-- The partial derivative as a derivative along the coordinate line. -/
theorem hasDerivAt_line {f : (Fin 4 → ℝ) → ℂ} {x : Fin 4 → ℝ} (hf : DifferentiableAt ℝ f x)
    (μ : Fin 4) :
    HasDerivAt (fun s : ℝ => f (x + s • Pi.single μ (1 : ℝ))) (pd f μ x) 0 := by
  have hl : HasDerivAt (fun s : ℝ => x + s • (Pi.single μ (1 : ℝ) : Fin 4 → ℝ))
      (Pi.single μ (1 : ℝ)) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single μ (1 : ℝ) : Fin 4 → ℝ)).const_add x
  have hf' : HasFDerivAt f (fderiv ℝ f x) (x + (0 : ℝ) • (Pi.single μ (1 : ℝ) : Fin 4 → ℝ)) := by
    simpa using hf.hasFDerivAt
  exact hf'.comp_hasDerivAt (0 : ℝ) hl

/-- **`tr(R^* ∂_μR) = 0`** for a differentiable map into `{det = 1}` that is unitary at `x`. -/
theorem trace_star_mul_pdM_eq_zero {R : (Fin 4 → ℝ) → M5} {U : Set (Fin 4 → ℝ)}
    (hU : IsOpen U) (hdet : ∀ y ∈ U, (R y).det = 1) {x : Fin 4 → ℝ} (hx : x ∈ U)
    (hRu : R x ∈ unitaryGroup (Fin 5) ℂ) (hR : MDiffAt R x) (μ : Fin 4) :
    (star (R x) * pdM R μ x).trace = 0 := by
  set γ : ℝ → M5 := fun s => star (R x) * R (x + s • Pi.single μ (1 : ℝ))
  have hent : ∀ a b, HasDerivAt (fun s => γ s a b) ((star (R x) * pdM R μ x) a b) 0 := by
    intro a b
    simp only [γ, Matrix.mul_apply, pdM, of_apply]
    exact HasDerivAt.fun_sum fun k _ => (hasDerivAt_line (hR k b) μ).const_mul _
  have hd := hasDerivAt_det_real hent
  have hγ0 : γ 0 = 1 := by
    simp only [γ, zero_smul, add_zero]
    exact mem_unitaryGroup_iff'.mp hRu
  rw [hγ0, MatrixDetExp.detDerivAt_one] at hd
  -- `det γ = 1` near `0`
  have hline : Continuous fun s : ℝ => x + s • (Pi.single μ (1 : ℝ) : Fin 4 → ℝ) := by
    fun_prop
  have hev : ∀ᶠ s in 𝓝 (0 : ℝ), (γ s).det = 1 := by
    have hmem : U ∈ 𝓝 (x + (0 : ℝ) • (Pi.single μ (1 : ℝ) : Fin 4 → ℝ)) := by
      simpa using hU.mem_nhds hx
    filter_upwards [hline.continuousAt.preimage_mem_nhds hmem] with s hs
    simp only [γ, det_mul, hdet _ hs, mul_one, star_eq_conjTranspose, det_conjTranspose,
      hdet x hx, star_one]
  have hc : HasDerivAt (fun s => (γ s).det) 0 0 :=
    (hasDerivAt_const (0 : ℝ) (1 : ℂ)).congr_of_eventuallyEq hev
  exact hd.unique hc

/-! ### The Maurer–Cartan form lies in `𝔰(𝔲(3) ⊕ 𝔲(2))` -/

/-- **`(∂_μR) R^* ∈ 𝔰(𝔲(3) ⊕ 𝔲(2))`** for a gauge `R` with values in `G_SM` on an open set `U`,
differentiable at `x ∈ U`. -/
theorem pdM_mul_star_mem_gSM {R : (Fin 4 → ℝ) → M5} {U : Set (Fin 4 → ℝ)} (hU : IsOpen U)
    (hRG : ∀ y ∈ U, R y ∈ GSM) {x : Fin 4 → ℝ} (hx : x ∈ U) (hR : MDiffAt R x) (μ : Fin 4) :
    pdM R μ x * star (R x) ∈ gSM := by
  have hRu : ∀ y ∈ U, R y ∈ unitaryGroup (Fin 5) ℂ := fun y hy => (hRG y hy).1
  have hz := pdM_unitary_on hU hRu hx hR μ
  refine ⟨?_, ?_, ?_⟩
  · rw [star_mul, star_star]
    exact eq_neg_of_add_eq_zero_right hz
  · have h1 := isSMBlock_pdM hU (fun y hy => (hRG y hy).2.1) hx μ
    exact (isSMBlock_iff_commute _).2 (((isSMBlock_iff_commute _).1 h1).mul_right
      (commute_star_of_commute ((isSMBlock_iff_commute _).1 (hRG x hx).2.1)))
  · rw [trace_mul_comm]
    exact trace_star_mul_pdM_eq_zero hU (fun y hy => (hRG y hy).2.2) hx (hRu x hx) hR μ

/-- **A `G_SM`-valued gauge maps an `𝔰(𝔲(3) ⊕ 𝔲(2))`-valued connection to an
`𝔰(𝔲(3) ⊕ 𝔲(2))`-valued one**: `R·A = R A R^* - (∂R) R^* ∈ 𝔤_SM` at every point of the open set
where `R` is `G_SM`-valued and differentiable. -/
theorem gaugeConn_mem_gSM {R : (Fin 4 → ℝ) → M5} {U : Set (Fin 4 → ℝ)} (hU : IsOpen U)
    (hRG : ∀ y ∈ U, R y ∈ GSM) {x : Fin 4 → ℝ} (hx : x ∈ U) (hR : MDiffAt R x)
    {A : MConn 5} (hA : ∀ μ, A μ x ∈ gSM) (μ : Fin 4) : gaugeConn R A μ x ∈ gSM :=
  gSM.sub_mem (ad_mem_gSM (hRG x hx) (hA μ)) (pdM_mul_star_mem_gSM hU hRG hx hR μ)

/-- The same in the ledger encoding `smLie` of `def:tests`. -/
theorem gaugeConn_mem_smLie {R : (Fin 4 → ℝ) → M5} {U : Set (Fin 4 → ℝ)} (hU : IsOpen U)
    (hRG : ∀ y ∈ U, R y ∈ GSM) {x : Fin 4 → ℝ} (hx : x ∈ U) (hR : MDiffAt R x)
    {A : MConn 5} (hA : ∀ μ, Matrix.of.symm (A μ x) ∈ smLie) (μ : Fin 4) :
    Matrix.of.symm (gaugeConn R A μ x) ∈ smLie := by
  have h := gaugeConn_mem_gSM hU hRG hx hR
    (fun ν => BallAnalysis.UhlenbeckStandardModel.mem_gSM_of_smLie (hA ν)) μ
  rw [← mem_gSM_iff, Equiv.apply_symm_apply]
  exact h

/-- Entrywise smoothness on an open set gives `MDiffAt`. -/
theorem mDiffAt_of_contDiffOn {m : ℕ} {R : (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ}
    {U : Set (Fin 4 → ℝ)} (hU : IsOpen U) (hR : ∀ c e, ContDiffOn ℝ ∞ (fun y => R y c e) U)
    {x : Fin 4 → ℝ} (hx : x ∈ U) : MDiffAt R x := fun c e =>
  ((hR c e).contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)

/-! ### The matter representations -/

/-- The weak (Higgs-doublet) block `ℂ² ⊂ ℂ³ ⊕ ℂ²` is `G_SM`-invariant: a block-diagonal matrix
maps doublet vectors (vanishing colour components) to doublet vectors. -/
theorem mulVec_doublet {g : M5} (hg : IsSMBlock g) {v : Fin 5 → ℂ}
    (hv : ∀ i, colourBlock i = true → v i = 0) (i : Fin 5) (hi : colourBlock i = true) :
    (g *ᵥ v) i = 0 := by
  simp only [mulVec, dotProduct]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hj : colourBlock j = true
  · rw [hv j hj, mul_zero]
  · rw [hg i j (by rw [hi]; exact fun h => hj h.symm), zero_mul]

/-- Gauge transformations act unitarily on the transported matter: `|R(y) u(y)| = |u(y)|`
(defining representation of `G_SM ⊂ U(5)`). -/
theorem fibreNorm_transp {R : (Fin 4 → ℝ) → M5} {y : Fin 4 → ℝ} (hR : R y ∈ GSM)
    (u : (Fin 4 → ℝ) → Fin 5 → ℂ) :
    fibreNorm (fun c => transp R u c y) = fibreNorm (u y) :=
  fibreNorm_mulVec_unitary hR.1 (u y)

/-- **Consequence for the Coulomb charts of `prop:critical-uhlenbeck`** (Standard-Model
structure group): on every ball of the Uhlenbeck cover, the Coulomb connections
`Ã_{h,j} = R_{h,j}·A_h` of `smLie`-valued smooth connections are `smLie`-valued. -/
theorem uhlenbeck_cover_SM_lie {a b : Fin 4 → ℝ} (A : ℕ → MConn 5)
    (hA : ∀ h, IsSmoothUnitaryConn (A h)) (hsm : ∀ h μ y, Matrix.of.symm (A h μ y) ∈ smLie)
    (hUI : CriticalCurvatureUI volume (box a b) (fun h x => curvVec (A h) x))
    {K' : Set (Fin 4 → ℝ)} (hK' : IsCompact K') (hK'Q : K' ⊆ box a b) {η : ℝ≥0} (hη : 0 < η) :
    ∃ (N : ℕ) (ctr : Fin N → Fin 4 → ℝ) (r : ℝ), 0 < r ∧ (∀ j, eBall (ctr j) r ⊆ box a b) ∧
      K' ⊆ ⋃ j, innerCube (ctr j) r ∧
      ∃ R : ℕ → Fin N → (Fin 4 → ℝ) → M5,
        (∀ h j, ∀ y ∈ eBall (ctr j) r, R h j y ∈ GSM) ∧
        (∀ h j c e, ContDiffOn ℝ ∞ (fun y => R h j y c e) (eBall (ctr j) r)) ∧
        (∀ h j, ∀ y ∈ eBall (ctr j) r, ∀ μ,
          Matrix.of.symm (gaugeConn (R h j) (A h) μ y) ∈ smLie) := by
  obtain ⟨N, ctr, r, hr, hball, hcov, R, hRG, hRs, -, -, -⟩ :=
    UhlenbeckGauge.uhlenbeck_ball_cover_in
      BallAnalysis.UhlenbeckStandardModel.uhlenbeckSmallEnergyGaugeIn_SM A hA
      (fun h μ y => BallAnalysis.UhlenbeckStandardModel.mem_gSM_of_smLie (hsm h μ y)) hUI hK'
      hK'Q hη
  exact ⟨N, ctr, r, hr, hball, hcov, R, hRG, hRs, fun h j y hy μ =>
    gaugeConn_mem_smLie (isOpen_eBall _ _) (hRG h j) hy
      (mDiffAt_of_contDiffOn (isOpen_eBall _ _) (hRs h j) hy) (fun ν => hsm h ν y) μ⟩

/-! ### Non-vacuity -/

/-- A nonconstant `G_SM`-valued gauge: `R(y) = exp(y₀ Y)` with the hypercharge generator `Y`;
its Maurer–Cartan form is the (nonzero) generator `Y ∈ 𝔤_SM`. -/
example : ∃ X ∈ gSM, X ≠ 0 := ⟨hyperY, hyperY_mem, hyperY_ne_zero⟩

end RenewalGeometry.SMGaugeLie
