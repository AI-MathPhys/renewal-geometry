/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.EinsteinHilbertCurveVariation
import RenewalGeometry.Action.NativeEulerConsistency
import RenewalGeometry.Continuum.ContEulerCalculus

/-!
# The Euler rows of the native first-order Palatini density are the Einstein equations

Einstein–Standard-Model action-closure manuscript, bridge step P3 of `thm:native-closure`
("the Euler rows of the native Lagrangian are the physical field equations up to smooth
invertible algebraic coefficients"), gravitational sector.

The native continuum gravitational Lagrangian is the first-order Palatini density
`L^{(1)}(e, ∂e) = NativeGravityJet.palatiniFirstOrder κ Λ` (the `h → 0` limit of the Cartan
plaquette row of `eq:native-densities`, with the torsion-free reader connection
`ω = Ω(e, ∂e)`).  For a smooth coframe field `e` with `det e > 0` put `g = eᵀ η e` (`gF`).

## Main results

* `dF_gF` — the coordinate first jet of `g = eᵀηe` is the reader jet `G_λ = (∂_λe)ᵀηe + eᵀη∂_λe`;
* `gamMat_eq_chr`, `fderiv_gamMat_eq_dchr` — the reader Christoffel symbols and their
  derivatives are the jets `chr`, `dchr` of `Gravity/HarmonicDefectForcingExact.lean` for `g`;
* `sum_riemMat_eq_ricci` — the contraction of `riemMat` is the Ricci jet `ricciJ`;
* `pal_contract` — `Σ_{ab} pal^{μν}_{ab}(e M e⁻¹)_{ab} = v/(2κ) (M g⁻¹)_{μν}`;
* **`palatini_cartan`** — the Cartan structure identity at the level of Lagrangians:
  `L^{(1)}(e, ∂e) = v(e)/(2κ) R(g) - (Λ/κ) v(e) + Σ_μ ∂_μ Z^μ` with the explicit flux
  `Z^μ = -Σ palA^{μν}_{ab} (ω_ν)_{ab}` (`cartanFlux`);
* `palatini_variation_pointwise` — the pointwise first-variation formula
  `DL^{(1)}(J¹e)(J¹v) = -(v/(2κ))(G^{μν} + Λg^{μν})δg_{μν} + Σ_μ ∂_μB^μ` (Cartan identity along the
  line `e + tv`, `EHFieldVariation.hasDerivAt_volScal_curve`, `EHJetVariation.eh_jet_variation`,
  `EHFieldVariation.sum_pd_flux_eq`, mixed partials `ContEulerCalc.hasDerivAt_pd_shift`);
* **`palatini_euler`** — **the variational identity, gravitational sector**: for a smooth
  `ℤ⁴`-periodic coframe with `det e > 0`,
  `contEuler L^{(1)} e = einsteinCov κ Λ e`, i.e.
  `𝓔₀(e)[δe] = -(v(e)/(2κ)) (G^{μν}(g) + Λ g^{μν}) (δeᵀηe + eᵀηδe)_{μν}` with the library Einstein
  tensor `HarmonicDefect.einstein` of the metric 2-jet of `g = eᵀηe`;
* **`palatini_euler_period`** — the same for fields of any period `L > 0` (the period-`2π` box of
  `thm:native-source`), by the dilation `x ↦ Lx` (`DiscreteEulerConsistency.contEuler_scale`,
  `einsteinCov_scale`, homogeneity `einsteinUp_scale`).

Scope (disclosed): this is the pure-gravity row of the native continuum Lagrangian
`L₀ = palatiniFirstOrder + YM + Higgs + Dirac` (`NativeEulerConsistency.limDensity_firstJetDensity_eq`);
the matter rows and the matter contribution `T^{SM}` to the coframe row are not treated here.
Fields are smooth and periodic in all four coordinates, as the reconstructions of
`thm:native-source` are.
-/

namespace RenewalGeometry

namespace PalatiniEuler

open Finset HarmonicDefect EHJetVariation EHFieldVariation ActualJetSystem
open NativeScaling (Mat eta metric readerOmega readerG readerGamma)
open NativeDensity (pal palA volume invEntry matToOp opEntry)
open NativeEulerConsistency (omega0 contCartan gamMat riemMat)
open DiscreteEulerConsistency (R4 evec jet1 contEuler)
open PeriodicCube (IsZPeriodic)
open Filter Topology Set
open SobolevOpen (pd)
open scoped ContDiff Matrix

noncomputable section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 400000

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-! ### The metric of a coframe field and its jets -/

/-- The metric field `g = eᵀ η e` of a coframe field, as a two-index array. -/
def gF (e : R4 → Mat) (z : R4) : Fin 4 → Fin 4 → ℝ := fun i j => metric (e z) i j

theorem metric_apply' (e : Mat) (i j : Fin 4) :
    metric e i j = ∑ l, ∑ k, e l i * eta l k * e k j := by
  simp only [metric, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem readerG_apply' (e : Mat) (q : Fin 4 → Mat) (lam i j : Fin 4) :
    readerG e q lam i j = ∑ l, ∑ k, (q lam l i * eta l k * e k j + e l i * eta l k * q lam k j) := by
  simp only [readerG, Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul,
    Finset.sum_add_distrib]
  rw [Finset.sum_comm, Finset.sum_comm (f := fun x y => e y i * eta y x * q lam x j)]

theorem eta_symm (a b : Fin 4) : eta a b = eta b a := by
  unfold eta
  by_cases h : a = b
  · subst h; rfl
  · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ (Ne.symm h)]

theorem metric_symm (e : Mat) (i j : Fin 4) : metric e i j = metric e j i := by
  rw [metric_apply', metric_apply', Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  rw [eta_symm]; ring

theorem readerG_symm (e : Mat) (q : Fin 4 → Mat) (lam i j : Fin 4) :
    readerG e q lam i j = readerG e q lam j i := by
  rw [readerG_apply', readerG_apply', Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
  rw [eta_symm l k]; ring

theorem hasDerivAt_line_mat {f : R4 → Mat} {z : R4} (lam : Fin 4) (hf : DifferentiableAt ℝ f z)
    (a b : Fin 4) :
    HasDerivAt (fun s : ℝ => f (z + s • Pi.single lam 1) a b) (fderiv ℝ f z (evec lam) a b) 0 :=
  hasDerivAt_pi.1 (hasDerivAt_pi.1 (hasDerivAt_line' lam hf) a) b

section Coframe

variable {e : R4 → Mat}

theorem differentiable_gF (he : Differentiable ℝ e) : Differentiable ℝ (gF e) := by
  intro z
  have h : DifferentiableAt ℝ (fun y => metric (e y)) z :=
    ((NativeDensity.contDiff_metric (k := 1)).differentiable one_ne_zero (e z)).comp z (he z)
  exact h

theorem contDiff_gF (he : ContDiff ℝ ∞ e) : ContDiff ℝ ∞ (gF e) := by
  have h : ContDiff ℝ ∞ (fun y => metric (e y)) := NativeDensity.contDiff_metric.comp he
  exact h

theorem gF_symm (z : R4) (i j : Fin 4) : gF e z i j = gF e z j i := metric_symm _ i j

/-- **The coordinate first jet of `g = eᵀηe` is the reader jet** `G_λ = (∂_λe)ᵀηe + eᵀη∂_λe`. -/
theorem dF_gF (he : Differentiable ℝ e) (z : R4) (lam i j : Fin 4) :
    dF (gF e) z lam i j = readerG (e z) (fun l => fderiv ℝ e z (evec l)) lam i j := by
  unfold dF
  have hline : HasDerivAt (fun s : ℝ => gF e (z + s • Pi.single lam 1))
      (fun i j => readerG (e z) (fun l => fderiv ℝ e z (evec l)) lam i j) 0 := by
    refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => ?_
    simp only [gF, metric_apply', readerG_apply']
    refine HasDerivAt.fun_sum fun l _ => HasDerivAt.fun_sum fun k _ => ?_
    have h1 := hasDerivAt_line_mat lam (he z) l i
    have h2 := hasDerivAt_line_mat lam (he z) k j
    refine ((h1.mul_const (eta l k)).fun_mul h2).congr_deriv ?_
    simp only [zero_smul, add_zero]
  rw [pd_eq_of_line' (differentiable_gF he z) hline]

/-- The reader Christoffel symbols are the Christoffel symbols of `g = eᵀηe`. -/
theorem gamMat_eq_chr (he : Differentiable ℝ e) (z : R4) (μ ρ σ : Fin 4) :
    gamMat e z μ ρ σ = chr (ginvOf (gF e z)) (dF (gF e) z) ρ μ σ := by
  unfold gamMat readerGamma chr
  have hinv : ∀ a b, (metric (e z))⁻¹ a b = ginvOf (gF e z) a b := fun a b => rfl
  simp only [hinv, dF_gF he z]
  congr 1
  · norm_num
  · refine Finset.sum_congr rfl fun s _ => ?_
    rw [readerG_symm (e z) _ μ σ s, readerG_symm (e z) _ σ μ s]

theorem dF_gF_symm (he : Differentiable ℝ e) (z : R4) (α i j : Fin 4) :
    dF (gF e) z α i j = dF (gF e) z α j i := by
  rw [dF_gF he, dF_gF he, readerG_symm]

theorem pd_symm_of_symm {F : R4 → Fin 4 → Fin 4 → ℝ} (hF : ∀ y, DifferentiableAt ℝ F y)
    (hs : ∀ y i j, F y i j = F y j i) (α : Fin 4) (y : R4) (i j : Fin 4) :
    pd F α y i j = pd F α y j i := by
  rw [← pd_apply₂ (hF y), ← pd_apply₂ (hF y)]
  exact congrArg (fun G => pd G α y) (funext fun y => hs y i j)

theorem ddF_gF_symm (he : ContDiff ℝ ∞ e) (z : R4) (β α i j : Fin 4) :
    ddF (gF e) z β α i j = ddF (gF e) z β α j i := by
  have hd : Differentiable ℝ e := he.differentiable (by simp)
  have hg := contDiff_gF he
  have hpd : ∀ y, DifferentiableAt ℝ (pd (gF e) α) y := fun y =>
    (contDiff_pd' hg α).differentiable (by simp) y
  unfold ddF
  exact pd_symm_of_symm hpd (fun y i j => dF_gF_symm hd y α i j) β z i j

theorem ddF_gF_comm (he : ContDiff ℝ ∞ e) (z : R4) (β α i j : Fin 4) :
    ddF (gF e) z β α i j = ddF (gF e) z α β i j := by
  have hg := contDiff_gF he
  unfold ddF
  have h2 : ContDiff ℝ 2 (gF e) := hg.of_le (by norm_cast)
  have hdd : DifferentiableAt ℝ (fderiv ℝ (gF e)) z :=
    ((h2.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) z
  have hsymm := (h2.contDiffAt (x := z)).isSymmSndFDerivAt (by simp)
  have e1 : pd (pd (gF e) α) β z = fderiv ℝ (fderiv ℝ (gF e)) z (Pi.single β 1) (Pi.single α 1) := by
    show fderiv ℝ (fun y => fderiv ℝ (gF e) y (Pi.single α 1)) z (Pi.single β 1) = _
    rw [fderiv_clm_apply hdd (differentiableAt_const _)]
    simp
  have e2 : pd (pd (gF e) β) α z = fderiv ℝ (fderiv ℝ (gF e)) z (Pi.single α 1) (Pi.single β 1) := by
    show fderiv ℝ (fun y => fderiv ℝ (gF e) y (Pi.single β 1)) z (Pi.single α 1) = _
    rw [fderiv_clm_apply hdd (differentiableAt_const _)]
    simp
  rw [e1, e2, hsymm]

end Coframe


/-! ### Symmetry of the Christoffel jet -/

theorem dchr_symm {n : Type*} [Fintype n] [DecidableEq n] (gi : n → n → ℝ) (dg : n → n → n → ℝ)
    (ddg : n → n → n → n → ℝ) (hdg : ∀ α μ ν, dg α μ ν = dg α ν μ)
    (hddg : ∀ β α μ ν, ddg β α μ ν = ddg β α ν μ) (α l μ ν : n) :
    dchr gi dg ddg α l μ ν = dchr gi dg ddg α l ν μ := by
  unfold dchr dchr1 dchr2
  congr 1
  · congr 1
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [hdg σ μ ν]; ring
  · congr 1
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [hddg α σ μ ν]; ring

section Coframe2

variable {e : R4 → Mat}

/-- **The derivatives of the reader Christoffel symbols** are the Christoffel jet `dchr` of
`g = eᵀηe`. -/
theorem fderiv_gamMat_eq_dchr (he : ContDiff ℝ ∞ e) (hdet : ∀ z, (e z).det ≠ 0) (z : R4)
    (μ ν ρ σ : Fin 4) :
    fderiv ℝ (fun z => gamMat e z ν) z (evec μ) ρ σ =
      dchr (ginvOf (gF e z)) (dF (gF e) z) (ddF (gF e) z) μ ρ ν σ := by
  have hd : Differentiable ℝ e := he.differentiable (by simp)
  have hd2 : ContDiff ℝ 2 e := he.of_le (by norm_cast)
  have hg := contDiff_gF he
  have hgd : ∀ y, DifferentiableAt ℝ (gF e) y := fun y => hg.differentiable (by simp) y
  have hpd : ∀ α y, DifferentiableAt ℝ (pd (gF e) α) y := fun α y =>
    (contDiff_pd' hg α).differentiable (by simp) y
  set ℓ : ℝ → R4 := fun s => z + s • Pi.single μ 1 with hℓ
  have hℓ0 : ℓ 0 = z := by simp [hℓ]
  have h1 := hasDerivAt_line_mat μ (NativeEulerConsistency.differentiableAt_gamMat hd2 (hdet z) ν)
    ρ σ
  have hG : ∀ a b, HasDerivAt (fun s => gF e (ℓ s) a b) (dF (gF e) (ℓ 0) μ a b) 0 := by
    intro a b
    rw [hℓ0]; exact hasDerivAt_line_apply μ (hgd z) a b
  have hgi : ∀ l σ', HasDerivAt (fun s => ginvOf (gF e (ℓ s)) l σ')
      (dginv (ginvOf (gF e (ℓ 0))) (dF (gF e) (ℓ 0)) μ l σ') 0 := by
    intro l σ'
    have hdet' : (Matrix.of (gF e (ℓ 0))).det ≠ 0 := by
      rw [hℓ0]
      show (metric (e z)).det ≠ 0
      exact NativeDensity.det_metric_ne_zero (hdet z)
    exact JetCurve.hasDerivAt_ginvOf (g := fun s => gF e (ℓ s)) μ (fun a b => hG a b) hdet' l σ'
  have hdg : ∀ α a b, HasDerivAt (fun s => dF (gF e) (ℓ s) α a b) (ddF (gF e) z μ α a b) 0 :=
    fun α a b => hasDerivAt_line_apply μ (hpd α z) a b
  have h2 := JetCurve.hasDerivAt_chr (gi := fun s => ginvOf (gF e (ℓ s)))
    (dg := fun s => dF (gF e) (ℓ s)) (t := 0) (ddg := ddF (gF e) z) μ hgi hdg ρ ν σ
  rw [hℓ0] at h2
  have hfun : (fun s => gamMat e (z + s • Pi.single μ 1) ν ρ σ) =
      fun s => chr (ginvOf (gF e (ℓ s))) (dF (gF e) (ℓ s)) ρ ν σ := by
    funext s
    exact gamMat_eq_chr hd _ ν ρ σ
  rw [hfun] at h1
  exact h1.unique h2

/-- **The Ricci contraction of the coordinate curvature** `riemMat` is the Ricci jet of
`g = eᵀηe`: `Σ_μ R^μ_{σμν} = Ric_{σν}`. -/
theorem sum_riemMat_eq_ricci (he : ContDiff ℝ ∞ e) (hdet : ∀ z, (e z).det ≠ 0) (z : R4)
    (ν σ : Fin 4) :
    ∑ μ, riemMat e z μ ν μ σ = ricci (ginvOf (gF e z)) (dF (gF e) z) (ddF (gF e) z) σ ν := by
  have hd : Differentiable ℝ e := he.differentiable (by simp)
  simp only [NativeEulerConsistency.riemMat_apply, fderiv_gamMat_eq_dchr he hdet,
    gamMat_eq_chr hd]
  unfold ricci ricciJ
  set gi := ginvOf (gF e z)
  set dg := dF (gF e) z
  set ddg := ddF (gF e) z
  have hdgs : ∀ α a b, dg α a b = dg α b a := fun α a b => dF_gF_symm hd z α a b
  have hddgs : ∀ β α a b, ddg β α a b = ddg β α b a := fun β α a b => ddF_gF_symm he z β α a b
  have hΓ : ∀ l a b, chr gi dg l a b = chr gi dg l b a := chr_symm gi dg hdgs
  have hD : ∀ α l a b, dchr gi dg ddg α l a b = dchr gi dg ddg α l b a :=
    dchr_symm gi dg ddg hdgs hddgs
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have e1 : ∑ μ, dchr gi dg ddg μ μ ν σ = ∑ α, dchr gi dg ddg α α σ ν :=
    Finset.sum_congr rfl fun α _ => hD α α ν σ
  have e2 : ∑ μ, dchr gi dg ddg ν μ μ σ = ∑ α, dchr gi dg ddg ν α σ α :=
    Finset.sum_congr rfl fun α _ => hD ν α α σ
  have e3 : ∑ μ, ∑ l, chr gi dg μ μ l * chr gi dg l ν σ =
      ∑ α, ∑ l, chr gi dg α α l * chr gi dg l σ ν :=
    Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun l _ => by rw [hΓ l ν σ]
  have e4 : ∑ μ, ∑ l, chr gi dg μ ν l * chr gi dg l μ σ =
      ∑ α, ∑ l, chr gi dg α ν l * chr gi dg l σ α :=
    Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun l _ => by rw [hΓ l α σ]
  rw [e1, e2, e3, e4]
  ring

end Coframe2

/-! ### Contraction with the Palatini coefficient -/

theorem eta_mul_eta : eta * eta = 1 := by
  unfold eta
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp

theorem eta_transpose : etaᵀ = eta := by
  unfold eta; rw [Matrix.diagonal_transpose]

/-- `(eᵀηe)⁻¹ = e⁻¹ η e⁻ᵀ`. -/
theorem metric_inv_eq (e : Mat) (he : e.det ≠ 0) : (metric e)⁻¹ = e⁻¹ * eta * (e⁻¹)ᵀ := by
  have hu : IsUnit e.det := isUnit_iff_ne_zero.mpr he
  refine Matrix.inv_eq_left_inv ?_
  have h1 : (e⁻¹)ᵀ * eᵀ = 1 := by
    rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv e hu, Matrix.transpose_one]
  calc e⁻¹ * eta * (e⁻¹)ᵀ * metric e = e⁻¹ * eta * ((e⁻¹)ᵀ * eᵀ) * eta * e := by
        unfold metric; simp only [Matrix.mul_assoc]
    _ = 1 := by
        rw [h1, Matrix.mul_one, Matrix.mul_assoc e⁻¹, eta_mul_eta, Matrix.mul_one,
          Matrix.nonsing_inv_mul e hu]

/-- **Contraction with the Palatini coefficient**:
`Σ_{ab} pal^{μν}_{ab}(e M e⁻¹)_{ab} = v/(2κ) Σ_σ M_{μσ} g^{σν}`. -/
theorem pal_contract (κ : ℝ) (e : Mat) (he : e.det ≠ 0) (M : Mat) (μ ν : Fin 4) :
    ∑ a, ∑ b, pal κ e μ ν a b * (e * M * e⁻¹) a b =
      volume e / (2 * κ) * ∑ σ, M μ σ * (metric e)⁻¹ σ ν := by
  have hu : IsUnit e.det := isUnit_iff_ne_zero.mpr he
  have key : e⁻¹ * (e * M * e⁻¹) * (e⁻¹ * eta)ᵀ = M * (metric e)⁻¹ := by
    rw [metric_inv_eq e he, Matrix.transpose_mul, eta_transpose]
    simp only [← Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul e hu, Matrix.one_mul]
  set N := e * M * e⁻¹ with hN
  set B := e⁻¹ * eta with hB
  have hBe : ∀ b, ∑ c, invEntry ν c e * eta c b = B ν b := fun b => by
    rw [hB, Matrix.mul_apply]; rfl
  have hent : (e⁻¹ * N * Bᵀ) μ ν = ∑ a, ∑ b, e⁻¹ μ a * N a b * B ν b := by
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hrhs : (M * (metric e)⁻¹) μ ν = ∑ σ, M μ σ * (metric e)⁻¹ σ ν := Matrix.mul_apply
  rw [← hrhs, ← key, hent]
  unfold pal
  simp only [hBe, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [NativeDensity.invEntry_apply]
  ring


/-! ### The Cartan structure identity for the first-order Palatini density -/

/-- The Cartan flux `Z^μ = -Σ_{ν,a,b} palA^{μν}_{ab}(e) (ω_ν)_{ab}` of a coframe field. -/
def cartanFlux (κ : ℝ) (e : R4 → Mat) (μ : Fin 4) (z : R4) : ℝ :=
  -∑ ν, ∑ a, ∑ b, palA κ (e z) μ ν a b * omega0 e z ν a b

section Cartan

variable {e : R4 → Mat}

theorem differentiableAt_omega0' (he : ContDiff ℝ ∞ e) {z : R4} (hz : (e z).det ≠ 0) (ν : Fin 4) :
    DifferentiableAt ℝ (fun y => omega0 e y ν) z := by
  have hd2 : ContDiff ℝ 2 e := he.of_le (by norm_cast)
  refine differentiableAt_pi.2 fun a => differentiableAt_pi.2 fun b => ?_
  show DifferentiableAt ℝ ((fun q : Mat × (Fin 4 → Mat) => readerOmega q.1 q.2 ν a b) ∘
    (fun z => (e z, fun lam => fderiv ℝ e z (evec lam)))) z
  exact ((NativeDensity.contDiffAt_readerOmega_entry ν a b
    (q := (e z, fun lam => fderiv ℝ e z (evec lam))) hz).differentiableAt (by simp)).comp z
    (NativeEulerConsistency.differentiable_jetPair hd2 z)

theorem differentiableAt_palA_comp (κ : ℝ) (he : Differentiable ℝ e) {z : R4} (hz : (e z).det ≠ 0)
    (μ ν a b : Fin 4) : DifferentiableAt ℝ (fun y => palA κ (e y) μ ν a b) z := by
  have h1 := (NativeDensity.contDiffAt_pal κ μ ν a b (k := 1) hz).differentiableAt one_ne_zero
  have h2 := (NativeDensity.contDiffAt_pal κ ν μ a b (k := 1) hz).differentiableAt one_ne_zero
  have : (fun y => palA κ (e y) μ ν a b) =
      fun y => pal κ (e y) μ ν a b - pal κ (e y) ν μ a b := rfl
  rw [this]
  exact (h1.comp z (he z)).sub (h2.comp z (he z))

/-- The derivative of the Palatini coefficient along the coordinate line is the chain-rule
derivative `∂_t palA(e + t ∂_μe)|₀ = ∂_μ(palA ∘ e)`. -/
theorem deriv_palA_line (κ : ℝ) (he : Differentiable ℝ e) {z : R4} (hz : (e z).det ≠ 0)
    (μ ν a b : Fin 4) :
    deriv (fun t : ℝ => palA κ (e z + t • fderiv ℝ e z (evec μ)) μ ν a b) 0 =
      pd (fun y => palA κ (e y) μ ν a b) μ z := by
  have h1 := (NativeDensity.contDiffAt_pal κ μ ν a b (k := 1) hz).differentiableAt one_ne_zero
  have h2 := (NativeDensity.contDiffAt_pal κ ν μ a b (k := 1) hz).differentiableAt one_ne_zero
  have hP : DifferentiableAt ℝ (fun w : Mat => palA κ w μ ν a b) (e z) := by
    have : (fun w : Mat => palA κ w μ ν a b) = fun w => pal κ w μ ν a b - pal κ w ν μ a b := rfl
    rw [this]; exact h1.sub h2
  have hl : HasDerivAt (fun t : ℝ => e z + t • fderiv ℝ e z (evec μ)) (fderiv ℝ e z (evec μ)) 0 :=
    (((hasDerivAt_id (0 : ℝ)).smul_const (fderiv ℝ e z (evec μ))).const_add (e z)).congr_deriv
      (one_smul _ _)
  have hline := hP.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  rw [show (fun t : ℝ => palA κ (e z + t • fderiv ℝ e z (evec μ)) μ ν a b) =
    ((fun w : Mat => palA κ w μ ν a b) ∘ fun t : ℝ => e z + t • fderiv ℝ e z (evec μ)) from rfl,
    hline.deriv]
  unfold SobolevOpen.pd
  rw [show (fun y => palA κ (e y) μ ν a b) = (fun w : Mat => palA κ w μ ν a b) ∘ e from rfl,
    fderiv_comp z hP (he z)]
  rfl

/-- **The Cartan structure identity for the first-order Palatini density**: for a smooth coframe
field with `det e > 0`,
`L^{(1)}(e, ∂e) = v(e)/(2κ) R(g) - (Λ/κ) v(e) + Σ_μ ∂_μ Z^μ`, `g = eᵀηe`, with the explicit
Cartan flux `Z^μ = -Σ palA^{μν}_{ab}(ω_ν)_{ab}` (`cartanFlux`). -/
theorem palatini_cartan (κ Λ : ℝ) (he : ContDiff ℝ ∞ e) (hdet : ∀ z, 0 < (e z).det) (z : R4) :
    NativeGravityJet.palatiniFirstOrder κ Λ (e z) (fun μ => fderiv ℝ e z (evec μ)) =
      volume (e z) / (2 * κ) * scal (ginvOf (gF e z)) (dF (gF e) z) (ddF (gF e) z) -
        Λ / κ * volume (e z) + ∑ μ, pd (cartanFlux κ e μ) μ z := by
  have hd : Differentiable ℝ e := he.differentiable (by simp)
  have hd2 : ContDiff ℝ 2 e := he.of_le (by norm_cast)
  have hne : ∀ y, (e y).det ≠ 0 := fun y => (hdet y).ne'
  rw [NativeGravityJet.palatiniFirstOrder_eq κ Λ (hdet z)]
  set q : Fin 4 → Mat := fun μ => fderiv ℝ e z (evec μ) with hq
  set dω : Fin 4 → Fin 4 → Mat := fun μ ν => fderiv ℝ (fun y => omega0 e y ν) z (evec μ) with hdω
  have hω : ∀ μ, readerOmega (e z) q μ = omega0 e z μ := fun μ => rfl
  -- the Cartan structure equation entrywise
  have hC : ∀ μ ν a b, (omega0 e z μ * omega0 e z ν - omega0 e z ν * omega0 e z μ) a b =
      (e z * riemMat e z μ ν * (e z)⁻¹) a b - dω μ ν a b + dω ν μ a b := by
    intro μ ν a b
    have h := NativeEulerConsistency.contCartan_eq_riem hd2 hne z μ ν
    unfold NativeEulerConsistency.contCartan at h
    have h' := congrArg (fun T => opEntry T a b) h
    simp only [NativeDensity.opEntry_matToOp, Matrix.add_apply, Matrix.sub_apply] at h'
    simp only [hdω, Matrix.sub_apply]
    linarith
  -- the Cartan flux divergence
  have hZ : ∀ μ, pd (cartanFlux κ e μ) μ z =
      -∑ ν, ∑ a, ∑ b, (pd (fun y => palA κ (e y) μ ν a b) μ z * omega0 e z ν a b +
        palA κ (e z) μ ν a b * dω μ ν a b) := by
    intro μ
    have hPd : ∀ ν a b, DifferentiableAt ℝ (fun y => palA κ (e y) μ ν a b) z :=
      fun ν a b => differentiableAt_palA_comp κ hd (hne z) μ ν a b
    have hOd : ∀ ν, DifferentiableAt ℝ (fun y => omega0 e y ν) z := fun ν =>
      differentiableAt_omega0' he (hne z) ν
    have hOe : ∀ ν a b, DifferentiableAt ℝ (fun y => omega0 e y ν a b) z := fun ν a b =>
      differentiableAt_pi.1 (differentiableAt_pi.1 (hOd ν) a) b
    have hdiff : DifferentiableAt ℝ (cartanFlux κ e μ) z := by
      unfold cartanFlux
      fun_prop (disch := assumption)
    refine pd_eq_of_line' hdiff ?_
    unfold cartanFlux
    refine HasDerivAt.fun_neg ?_
    refine HasDerivAt.fun_sum fun ν _ => HasDerivAt.fun_sum fun a _ => HasDerivAt.fun_sum fun b _ => ?_
    have h1 := hasDerivAt_line' μ (hPd ν a b)
    have h2 := hasDerivAt_line_mat μ (hOd ν) a b
    refine (h1.fun_mul h2).congr_deriv ?_
    simp only [zero_smul, add_zero, hdω]
  rw [Finset.sum_congr rfl fun μ _ => hZ μ]
  simp only [hω, hC, deriv_palA_line κ hd (hne z)]
  -- the curvature term
  have hR : ∑ μ, ∑ ν, ∑ a, ∑ b, pal κ (e z) μ ν a b * (e z * riemMat e z μ ν * (e z)⁻¹) a b =
      volume (e z) / (2 * κ) * scal (ginvOf (gF e z)) (dF (gF e) z) (ddF (gF e) z) := by
    simp only [pal_contract κ (e z) (hne z)]
    simp_rw [← Finset.mul_sum]
    congr 1
    unfold scal trG
    simp only [← sum_riemMat_eq_ricci he hne z, Finset.mul_sum]
    refine sum3_reindex _ _
      { toFun := fun x => (x.2.2, x.2.1, x.1)
        invFun := fun x => (x.2.2, x.2.1, x.1)
        left_inv := fun x => rfl
        right_inv := fun x => rfl } fun x => ?_
    simp only [Equiv.coe_fn_mk]
    rw [mul_comm]
    rfl
  -- the antisymmetrisation of the derivative terms
  have hA : ∑ μ, ∑ ν, ∑ a, ∑ b, pal κ (e z) μ ν a b * dω ν μ a b =
      ∑ μ, ∑ ν, ∑ a, ∑ b, pal κ (e z) ν μ a b * dω μ ν a b := Finset.sum_comm
  have hsplit : ∑ μ, ∑ ν, ∑ a, ∑ b, pal κ (e z) μ ν a b *
      ((e z * riemMat e z μ ν * (e z)⁻¹) a b - dω μ ν a b + dω ν μ a b) =
      ∑ μ, ∑ ν, ∑ a, ∑ b, pal κ (e z) μ ν a b * (e z * riemMat e z μ ν * (e z)⁻¹) a b -
        ∑ μ, ∑ ν, ∑ a, ∑ b, palA κ (e z) μ ν a b * dω μ ν a b := by
    have e1 : ∑ μ, ∑ ν, ∑ a, ∑ b, pal κ (e z) μ ν a b *
        ((e z * riemMat e z μ ν * (e z)⁻¹) a b - dω μ ν a b + dω ν μ a b) =
        ∑ μ, ∑ ν, ∑ a, ∑ b, pal κ (e z) μ ν a b * (e z * riemMat e z μ ν * (e z)⁻¹) a b -
          ∑ μ, ∑ ν, ∑ a, ∑ b, pal κ (e z) μ ν a b * dω μ ν a b +
          ∑ μ, ∑ ν, ∑ a, ∑ b, pal κ (e z) μ ν a b * dω ν μ a b := by
      simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [e1, hA]
    unfold palA
    simp only [sub_mul, Finset.sum_sub_distrib]
    ring
  rw [hsplit, hR]
  simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib]
  ring

end Cartan


/-! ### Variations of the coframe and of the metric -/

/-- The shifted coframe field `e + t v`. -/
def shiftF (e v : R4 → Mat) (t : ℝ) : R4 → Mat := fun y => e y + t • v y

theorem shiftF_zero (e v : R4 → Mat) : shiftF e v 0 = e := by
  funext y; simp [shiftF]

/-- The metric variation `δg = vᵀηe + eᵀηv` induced by a coframe variation `v`. -/
def metricVarM (e δ : Mat) : Mat := δᵀ * eta * e + eᵀ * eta * δ

/-- The metric variation field `k = vᵀηe + eᵀηv`. -/
def kF (e v : R4 → Mat) (z : R4) : Fin 4 → Fin 4 → ℝ := fun i j => metricVarM (e z) (v z) i j

theorem metric_add_smul (A B : Mat) (t : ℝ) :
    metric (A + t • B) = metric A + t • metricVarM A B + t ^ 2 • metric B := by
  unfold metric metricVarM
  simp only [Matrix.transpose_add, Matrix.transpose_smul, Matrix.add_mul, Matrix.mul_add,
    Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul]
  rw [sq]
  abel

theorem gF_shift (e v : R4 → Mat) (t : ℝ) :
    gF (shiftF e v t) = fun y i j => gF e y i j + t * kF e v y i j + t ^ 2 * gF v y i j := by
  funext y i j
  simp only [gF, shiftF, kF, metric_add_smul, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]

theorem kF_symm (e v : R4 → Mat) (z : R4) (i j : Fin 4) : kF e v z i j = kF e v z j i := by
  unfold kF metricVarM
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [add_comm]
  congr 1
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
    rw [eta_symm]; ring
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
    rw [eta_symm]; ring

theorem contDiff_kF {e v : R4 → Mat} (he : ContDiff ℝ ∞ e) (hv : ContDiff ℝ ∞ v) :
    ContDiff ℝ ∞ (kF e v) := by
  have hea : ∀ a b, ContDiff ℝ ∞ (fun y => e y a b) := fun a b =>
    contDiff_pi.1 (contDiff_pi.1 he a) b
  have hva : ∀ a b, ContDiff ℝ ∞ (fun y => v y a b) := fun a b =>
    contDiff_pi.1 (contDiff_pi.1 hv a) b
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  simp only [kF, metricVarM, Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply]
  fun_prop

/-- Partial derivatives of a quadratic combination of fields. -/
theorem pd_comb {F G H : R4 → Fin 4 → Fin 4 → ℝ} {z : R4} (hF : DifferentiableAt ℝ F z)
    (hG : DifferentiableAt ℝ G z) (hH : DifferentiableAt ℝ H z) (t : ℝ) (α : Fin 4) :
    pd (fun y i j => F y i j + t * G y i j + t ^ 2 * H y i j) α z =
      fun i j => pd F α z i j + t * pd G α z i j + t ^ 2 * pd H α z i j := by
  have hfun : (fun y i j => F y i j + t * G y i j + t ^ 2 * H y i j) =
      fun y => F y + t • G y + t ^ 2 • H y := by
    funext y i j; simp [smul_eq_mul]
  rw [hfun]
  unfold SobolevOpen.pd
  have h := (hF.hasFDerivAt.add (hG.hasFDerivAt.const_smul t)).add (hH.hasFDerivAt.const_smul (t ^ 2))
  rw [show (fun y => F y + t • G y + t ^ 2 • H y) = F + t • G + t ^ 2 • H from rfl, h.fderiv]
  funext i j
  simp [smul_eq_mul]

theorem hasDerivAt_quad (a b c : ℝ) :
    HasDerivAt (fun t : ℝ => a + t * b + t ^ 2 * c) b 0 := by
  have h := (((hasDerivAt_id (0 : ℝ)).mul_const b).const_add a).add
    ((hasDerivAt_pow 2 (0 : ℝ)).mul_const c)
  refine h.congr_deriv ?_
  simp

theorem jet1_shiftF {e v : R4 → Mat} (he : Differentiable ℝ e) (hv : Differentiable ℝ v) (t : ℝ)
    (y : R4) : jet1 (shiftF e v t) y = jet1 e y + t • jet1 v y := by
  unfold jet1 shiftF
  have h := (he y).hasFDerivAt.add ((hv y).hasFDerivAt.const_smul t)
  rw [show (fun y => e y + t • v y) = e + t • v from rfl, h.fderiv]
  refine Prod.ext (by simp) (funext fun μ => ?_)
  simp only [Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply]
  rfl

/-- Nondegeneracy persists along small coframe variations of a periodic field. -/
theorem eventually_det_pos {e v : R4 → Mat} (he : Continuous e) (hv : Continuous v)
    (hep : IsZPeriodic e) (hvp : IsZPeriodic v) (hdet : ∀ z, 0 < (e z).det) :
    ∀ᶠ t in 𝓝 (0 : ℝ), ∀ y, 0 < (shiftF e v t y).det := by
  have hc : Continuous fun p : ℝ × R4 => (e p.2 + p.1 • v p.2).det :=
    (he.comp continuous_snd).add (continuous_fst.smul (hv.comp continuous_snd)) |>.matrix_det
  have hK : ∀ y ∈ Icc (0 : R4) 1, ∀ᶠ p : ℝ × R4 in 𝓝 ((0 : ℝ), y), 0 < (e p.2 + p.1 • v p.2).det := by
    intro y _
    have h0 : 0 < (e ((0 : ℝ), y).2 + ((0 : ℝ), y).1 • v ((0 : ℝ), y).2).det := by simpa using hdet y
    exact hc.continuousAt.eventually (lt_mem_nhds h0)
  have hev := (isCompact_Icc (a := (0 : R4)) (b := 1)).eventually_forall_of_forall_eventually
    (P := fun t y => 0 < (e y + t • v y).det) hK
  filter_upwards [hev] with t ht y
  have hp : IsZPeriodic fun y => (e y + t • v y).det := fun k x => by
    simp only [hep k x, hvp k x]
  show 0 < (e y + t • v y).det
  rw [← hp.apply_fract y]
  exact ht _ ⟨fun i => Int.fract_nonneg _, fun i => (Int.fract_lt_one _).le⟩


/-! ### The pointwise first-variation formula -/

/-- The first-order Palatini density as a density on coframe first jets. -/
def Lg (κ Λ : ℝ) (w : Mat × (Fin 4 → Mat)) : ℝ := NativeGravityJet.palatiniFirstOrder κ Λ w.1 w.2

/-- The Cartan flux as a function of the coframe first jet. -/
def FZ (κ : ℝ) (μ : Fin 4) (w : Mat × (Fin 4 → Mat)) : ℝ :=
  -∑ ν, ∑ a, ∑ b, palA κ w.1 μ ν a b * readerOmega w.1 w.2 ν a b

/-- The nondegenerate coframe chart of first jets. -/
def chartJ : Set (Mat × (Fin 4 → Mat)) := {w | w.1.det ≠ 0}

theorem isOpen_chartJ : IsOpen chartJ :=
  isOpen_ne.preimage (Continuous.matrix_det continuous_fst)

theorem contDiffOn_Lg (κ Λ : ℝ) : ContDiffOn ℝ ∞ (Lg κ Λ) chartJ := fun _w hw =>
  (NativeGravityFirstJet.contDiffAt_palatiniL κ Λ hw).contDiffWithinAt

theorem contDiffOn_FZ (κ : ℝ) (μ : Fin 4) : ContDiffOn ℝ ∞ (FZ κ μ) chartJ := by
  intro w hw
  refine ContDiffAt.contDiffWithinAt ?_
  have hpal : ∀ ν a b, ContDiffAt ℝ ∞ (fun w : Mat × (Fin 4 → Mat) => palA κ w.1 μ ν a b) w := by
    intro ν a b
    have h1 := (NativeDensity.contDiffAt_pal κ μ ν a b (k := ∞) hw).comp w contDiffAt_fst
    have h2 := (NativeDensity.contDiffAt_pal κ ν μ a b (k := ∞) hw).comp w contDiffAt_fst
    exact h1.sub h2
  have hom : ∀ ν a b, ContDiffAt ℝ ∞ (fun w : Mat × (Fin 4 → Mat) => readerOmega w.1 w.2 ν a b) w :=
    fun ν a b => NativeDensity.contDiffAt_readerOmega_entry ν a b hw
  unfold FZ
  refine ContDiffAt.neg ?_
  refine ContDiffAt.sum fun ν _ => ContDiffAt.sum fun a _ => ContDiffAt.sum fun b _ => ?_
  exact (hpal ν a b).mul (hom ν a b)

theorem cartanFlux_eq_FZ (κ : ℝ) (e : R4 → Mat) (μ : Fin 4) :
    cartanFlux κ e μ = fun y => FZ κ μ (jet1 e y) := rfl

theorem det_gF_neg {e : R4 → Mat} (hdet : ∀ z, 0 < (e z).det) (z : R4) :
    (Matrix.of (gF e z)).det < 0 := by
  show (metric (e z)).det < 0
  rw [NativeDensity.det_metric]
  have := hdet z
  nlinarith [sq_nonneg (e z).det, pow_pos this 2]

theorem gF_mul_ginvOf {e : R4 → Mat} (hdet : ∀ z, 0 < (e z).det) (z : R4) (a c : Fin 4) :
    ∑ b, gF e z a b * ginvOf (gF e z) b c = if a = c then 1 else 0 := by
  have hne : (Matrix.of (gF e z)).det ≠ 0 := (det_gF_neg hdet z).ne
  have h := Matrix.mul_nonsing_inv (Matrix.of (gF e z)) (isUnit_iff_ne_zero.mpr hne)
  have := congrFun (congrFun h a) c
  rw [Matrix.mul_apply, Matrix.one_apply] at this
  simpa [ginvOf] using this

/-- The partial derivatives of the shifted metric field are the quadratic combinations of those
of `g`, `k`, `vᵀηv`. -/
theorem pd_gF_shift {e v : R4 → Mat} (he : ContDiff ℝ ∞ e) (hv : ContDiff ℝ ∞ v) (t : ℝ)
    (α : Fin 4) :
    pd (gF (shiftF e v t)) α =
      fun y i j => pd (gF e) α y i j + t * pd (kF e v) α y i j + t ^ 2 * pd (gF v) α y i j := by
  funext y
  rw [gF_shift]
  exact pd_comb ((contDiff_gF he).differentiable (by simp) y)
    ((contDiff_kF he hv).differentiable (by simp) y) ((contDiff_gF hv).differentiable (by simp) y) t α

/-- **The pointwise first-variation formula of the first-order Palatini density**: for a smooth
periodic coframe with `det e > 0` and a smooth periodic coframe variation `v`, with `g = eᵀηe`,
`k = vᵀηe + eᵀηv`,
`DL^{(1)}(J¹e)(J¹v) = -(v(e)/(2κ)) (G^{μν} + Λ g^{μν}) k_{μν} + Σ_μ ∂_μ B^μ`, where the flux
`B^μ = (2κ)⁻¹ W^μ + DZ^μ(J¹e)(J¹v)` combines the Palatini flux of `δΓ` and the variation of the
Cartan flux. -/
theorem palatini_variation_pointwise (κ Λ : ℝ) {e v : R4 → Mat} (he : ContDiff ℝ ∞ e)
    (hv : ContDiff ℝ ∞ v) (hep : IsZPeriodic e) (hvp : IsZPeriodic v)
    (hdet : ∀ z, 0 < (e z).det) (z : R4) :
    fderiv ℝ (Lg κ Λ) (jet1 e z) (jet1 v z) =
      -(volume (e z) / (2 * κ)) * ∑ μ, ∑ ν, (einsteinUp (gF e z) (ginvOf (gF e z)) (dF (gF e) z)
          (ddF (gF e) z) μ ν + Λ * ginvOf (gF e z) μ ν) * kF e v z μ ν +
        ∑ μ, pd (fun y => (2 * κ)⁻¹ * palatiniFlux (gF e) (kF e v) μ y +
          fderiv ℝ (FZ κ μ) (jet1 e y) (jet1 v y)) μ z := by
  have hd : Differentiable ℝ e := he.differentiable (by simp)
  have hvd : Differentiable ℝ v := hv.differentiable (by simp)
  have hJe : ContDiff ℝ ∞ (jet1 e) := ContEulerBounds.contDiff_jet1_infty he
  have hJv : ContDiff ℝ ∞ (jet1 v) := ContEulerBounds.contDiff_jet1_infty hv
  have hjz : jet1 e z ∈ chartJ := (hdet z).ne'
  have hg := contDiff_gF he
  have hk := contDiff_kF he hv
  have hgv := contDiff_gF hv
  -- (1) the left side is the derivative along the line of jets
  have hL : HasDerivAt (fun t : ℝ => Lg κ Λ (jet1 e z + t • jet1 v z))
      (fderiv ℝ (Lg κ Λ) (jet1 e z) (jet1 v z)) 0 := by
    have hLd : DifferentiableAt ℝ (Lg κ Λ) (jet1 e z) :=
      ((contDiffOn_Lg κ Λ).contDiffAt (isOpen_chartJ.mem_nhds hjz)).differentiableAt (by simp)
    have hl : HasDerivAt (fun t : ℝ => jet1 e z + t • jet1 v z) (jet1 v z) 0 :=
      (((hasDerivAt_id (0 : ℝ)).smul_const (jet1 v z)).const_add (jet1 e z)).congr_deriv
        (one_smul _ _)
    exact hLd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  -- (2) the Cartan identity along the line
  set G : ℝ → Fin 4 → Fin 4 → ℝ := fun t => gF (shiftF e v t) z with hGdef
  set dG : ℝ → Fin 4 → Fin 4 → Fin 4 → ℝ := fun t => dF (gF (shiftF e v t)) z with hdGdef
  set ddG : ℝ → Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ := fun t => ddF (gF (shiftF e v t)) z
    with hddGdef
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), Lg κ Λ (jet1 e z + t • jet1 v z) =
      (2 * κ)⁻¹ * (volM (G t) * scal (ginvOf (G t)) (dG t) (ddG t)) - Λ / κ * volM (G t) +
        ∑ μ, pd (fun y => FZ κ μ (jet1 e y + t • jet1 v y)) μ z := by
    filter_upwards [eventually_det_pos he.continuous hv.continuous hep hvp hdet] with t ht
    have het : ContDiff ℝ ∞ (shiftF e v t) := he.add (hv.const_smul t)
    have hc := palatini_cartan κ Λ het ht z
    rw [← jet1_shiftF hd hvd t z]
    have hflux : ∀ μ, cartanFlux κ (shiftF e v t) μ = fun y => FZ κ μ (jet1 e y + t • jet1 v y) :=
      fun μ => by
        rw [cartanFlux_eq_FZ]
        funext y
        rw [jet1_shiftF hd hvd t y]
    simp only [hflux] at hc
    show NativeGravityJet.palatiniFirstOrder κ Λ (shiftF e v t z)
      (fun μ => fderiv ℝ (shiftF e v t) z (evec μ)) = _
    rw [hc]
    simp only [hGdef, hdGdef, hddGdef]
    rw [show volM (gF (shiftF e v t) z) = volume (shiftF e v t z) from rfl]
    ring
  -- (3) the derivative of the right side
  have hG : ∀ μ ν, HasDerivAt (fun t => G t μ ν) (kF e v z μ ν) 0 := by
    intro μ ν
    simp only [hGdef, gF_shift]
    exact hasDerivAt_quad _ _ _
  have hdG : ∀ α μ ν, HasDerivAt (fun t => dG t α μ ν) (dF (kF e v) z α μ ν) 0 := by
    intro α μ ν
    simp only [hdGdef, dF, pd_gF_shift he hv]
    exact hasDerivAt_quad _ _ _
  have hddG : ∀ β α μ ν, HasDerivAt (fun t => ddG t β α μ ν) (ddF (kF e v) z β α μ ν) 0 := by
    intro β α μ ν
    have hpd : ∀ t, pd (pd (gF (shiftF e v t)) α) β z =
        fun i j => pd (pd (gF e) α) β z i j + t * pd (pd (kF e v) α) β z i j +
          t ^ 2 * pd (pd (gF v) α) β z i j := by
      intro t
      rw [pd_gF_shift he hv t α]
      exact pd_comb ((contDiff_pd' hg α).differentiable (by simp) z)
        ((contDiff_pd' hk α).differentiable (by simp) z)
        ((contDiff_pd' hgv α).differentiable (by simp) z) t β
    simp only [hddGdef, ddF, hpd]
    exact hasDerivAt_quad _ _ _
  have hG0 : G 0 = gF e z := by simp only [hGdef, shiftF_zero]
  have hdG0 : dG 0 = dF (gF e) z := by simp only [hdGdef, shiftF_zero]
  have hddG0 : ddG 0 = ddF (gF e) z := by simp only [hddGdef, shiftF_zero]
  have hdet0 : (Matrix.of (G 0)).det < 0 := by rw [hG0]; exact det_gF_neg hdet z
  have hsym0 : ∀ μ ν, G 0 μ ν = G 0 ν μ := by rw [hG0]; exact gF_symm z
  have hVS := hasDerivAt_volScal_curve hG hdG hddG hdet0 hsym0
  have hV := hasDerivAt_volM_curve hG hdet0 hsym0
  rw [hG0, hdG0, hddG0] at hVS
  rw [hG0] at hV
  have hZ : HasDerivAt (fun t : ℝ => ∑ μ, pd (fun y => FZ κ μ (jet1 e y + t • jet1 v y)) μ z)
      (∑ μ, pd (fun y => fderiv ℝ (FZ κ μ) (jet1 e y) (jet1 v y)) μ z) 0 :=
    HasDerivAt.fun_sum fun μ _ =>
      ContEulerCalc.hasDerivAt_pd_shift isOpen_chartJ (contDiffOn_FZ κ μ) hJe hJv hjz μ
  have hR := ((hVS.const_mul (2 * κ)⁻¹).sub (hV.const_mul (Λ / κ))).add hZ
  have huniq := hL.unique (hR.congr_of_eventuallyEq hev)
  rw [huniq]
  -- (4) the Einstein–Hilbert variation and the Palatini flux
  set gi := ginvOf (gF e z)
  have hgis : ∀ a b, gi a b = gi b a := ginvOf_symm' (gF_symm z)
  have hdgs : ∀ α a b, dF (gF e) z α a b = dF (gF e) z α b a := dF_gF_symm hd z
  have hdks : ∀ α a b, dF (kF e v) z α a b = dF (kF e v) z α b a := by
    intro α a b
    exact pd_symm_of_symm (fun y => hk.differentiable (by simp) y) (kF_symm e v) α z a b
  have hEH := eh_jet_variation (gF e z) gi (dF (gF e) z) (ddF (gF e) z) (kF e v z) (dF (kF e v) z)
    (ddF (kF e v) z) (volM (gF e z)) hgis (gF_mul_ginvOf hdet z) hdgs hdks
  have hflux := sum_pd_flux_eq hg hk (fun y => gF_symm y) (det_gF_neg hdet) z
  -- (5) linearity of the divergence
  have hWd : ∀ μ, DifferentiableAt ℝ (palatiniFlux (gF e) (kF e v) μ) z := by
    intro μ
    have hgic : ∀ a b, DifferentiableAt ℝ (fun y => ginvOf (gF e y) a b) z := fun a b =>
      ((ActualJetSmooth.ContDiffAt.ginvOf hg.contDiffAt (det_gF_neg hdet z).ne a b).differentiableAt
        (by simp))
    have hdgc : ∀ α a b, DifferentiableAt ℝ (fun y => dF (gF e) y α a b) z := fun α a b =>
      differentiableAt_pi.1 (differentiableAt_pi.1
        ((contDiff_pd' hg α).differentiable (by simp) z) a) b
    have hdkc : ∀ α a b, DifferentiableAt ℝ (fun y => dF (kF e v) y α a b) z := fun α a b =>
      differentiableAt_pi.1 (differentiableAt_pi.1
        ((contDiff_pd' hk α).differentiable (by simp) z) a) b
    have hkc : ∀ a b, DifferentiableAt ℝ (fun y => kF e v y a b) z := fun a b =>
      differentiableAt_pi.1 (differentiableAt_pi.1 (hk.differentiable (by simp) z) a) b
    have hvold : DifferentiableAt ℝ (fun y => volM (gF e y)) z := by
      unfold volM
      have hdetd : DifferentiableAt ℝ (fun y => (Matrix.of (gF e y)).det) z :=
        (differentiable_det (gF e z)).comp z (hg.differentiable (by simp) z)
      exact hdetd.neg.sqrt (by have := det_gF_neg hdet z; intro h; simp only [Pi.neg_apply] at h; linarith)
    unfold palatiniFlux fluxV chrVar chr ginvVar
    fun_prop (disch := assumption)
  have hDZd : ∀ μ, DifferentiableAt ℝ (fun y => fderiv ℝ (FZ κ μ) (jet1 e y) (jet1 v y)) z :=
    fun μ => (ContEulerCalc.contDiff_fderiv_apply isOpen_chartJ (contDiffOn_FZ κ μ) hJe hJv
      (fun y => (hdet y).ne')).differentiable (by simp) z
  have hpdB : ∀ μ, pd (fun y => (2 * κ)⁻¹ * palatiniFlux (gF e) (kF e v) μ y +
      fderiv ℝ (FZ κ μ) (jet1 e y) (jet1 v y)) μ z =
      (2 * κ)⁻¹ * pd (palatiniFlux (gF e) (kF e v) μ) μ z +
        pd (fun y => fderiv ℝ (FZ κ μ) (jet1 e y) (jet1 v y)) μ z := by
    intro μ
    unfold SobolevOpen.pd
    rw [fderiv_fun_add ((hWd μ).const_mul _) (hDZd μ), fderiv_const_mul (hWd μ)]
    simp
  simp only [hpdB, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hflux]
  have hvol : volM (gF e z) = volume (e z) := rfl
  rw [← hvol]
  have hsplit : ∑ μ, ∑ ν, (einsteinUp (gF e z) gi (dF (gF e) z) (ddF (gF e) z) μ ν +
      Λ * gi μ ν) * kF e v z μ ν =
      ∑ μ, ∑ ν, einsteinUp (gF e z) gi (dF (gF e) z) (ddF (gF e) z) μ ν * kF e v z μ ν +
        Λ * trG gi (kF e v z) := by
    unfold trG
    simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
    ring
  rw [hsplit]
  linear_combination (2 * κ)⁻¹ * hEH


/-! ### The Einstein covector and the Euler identity -/

/-- An additive continuous map as a continuous `ℝ`-linear map. -/
def addL' {V₁ W : Type*} [NormedAddCommGroup V₁] [NormedSpace ℝ V₁] [FiniteDimensional ℝ V₁]
    [NormedAddCommGroup W] [NormedSpace ℝ W] (f : V₁ → W) (h : ∀ x y, f (x + y) = f x + f y)
    (hc : Continuous f) : ContEulerBounds.NCLM V₁ W :=
  (AddMonoidHom.mk' f h).toRealLinearMap hc

/-- The metric variation component `δ ↦ (δᵀηe + eᵀηδ)_{μν}` as a continuous bilinear map in
`(e, δ)`. -/
def mvBil (μ ν : Fin 4) : ContEulerBounds.NCLM Mat (ContEulerBounds.CovV Mat) :=
  addL' (fun e => addL' (fun δ => metricVarM e δ μ ν)
      (fun δ δ' => by
        simp only [metricVarM, Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add,
          Matrix.add_apply]; ring)
      (by unfold metricVarM; fun_prop))
    (fun e e' => ContinuousLinearMap.ext fun δ => by
      show metricVarM (e + e') δ μ ν = metricVarM e δ μ ν + metricVarM e' δ μ ν
      simp only [metricVarM, Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add,
        Matrix.add_apply]; ring)
    (continuous_clm_apply.mpr fun δ => by
      show Continuous fun e => metricVarM e δ μ ν
      unfold metricVarM; fun_prop)

theorem mvBil_apply (μ ν : Fin 4) (e δ : Mat) : mvBil μ ν e δ = metricVarM e δ μ ν := rfl

/-- **The Einstein covector** `δ ↦ -(v(e)/(2κ)) (G^{μν} + Λ g^{μν}) (δᵀηe + eᵀηδ)_{μν}` of a
coframe field (`g = eᵀηe`). -/
def einsteinCov (κ Λ : ℝ) (e : R4 → Mat) (z : R4) : ContEulerBounds.CovV Mat :=
  ∑ μ, ∑ ν, (-(volume (e z) / (2 * κ)) * (einsteinUp (gF e z) (ginvOf (gF e z)) (dF (gF e) z)
    (ddF (gF e) z) μ ν + Λ * ginvOf (gF e z) μ ν)) • mvBil μ ν (e z)

theorem einsteinCov_apply (κ Λ : ℝ) (e : R4 → Mat) (z : R4) (δ : Mat) :
    einsteinCov κ Λ e z δ = -(volume (e z) / (2 * κ)) * ∑ μ, ∑ ν,
      (einsteinUp (gF e z) (ginvOf (gF e z)) (dF (gF e) z) (ddF (gF e) z) μ ν +
        Λ * ginvOf (gF e z) μ ν) * metricVarM (e z) δ μ ν := by
  simp only [einsteinCov, ContinuousLinearMap.coe_sum', Finset.sum_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply, mvBil_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
  ring

section Smooth

variable {e : R4 → Mat}

theorem metric_jets_smooth (he : ContDiff ℝ ∞ e) (hdet : ∀ z, 0 < (e z).det) :
    (∀ a b, ContDiff ℝ ∞ (fun z => gF e z a b)) ∧
      (∀ a b, ContDiff ℝ ∞ (fun z => ginvOf (gF e z) a b)) ∧
      (∀ α a b, ContDiff ℝ ∞ (fun z => dF (gF e) z α a b)) ∧
      (∀ β α a b, ContDiff ℝ ∞ (fun z => ddF (gF e) z β α a b)) := by
  have hg := contDiff_gF he
  refine ⟨fun a b => contDiff_pi.1 (contDiff_pi.1 hg a) b, fun a b => ?_, fun α a b => ?_,
    fun β α a b => ?_⟩
  · exact contDiff_iff_contDiffAt.2 fun z =>
      ActualJetSmooth.ContDiffAt.ginvOf hg.contDiffAt (det_gF_neg hdet z).ne a b
  · exact contDiff_pi.1 (contDiff_pi.1 (contDiff_pd' hg α) a) b
  · exact contDiff_pi.1 (contDiff_pi.1 (contDiff_pd' (contDiff_pd' hg α) β) a) b

theorem contDiff_einsteinUp (he : ContDiff ℝ ∞ e) (hdet : ∀ z, 0 < (e z).det) (μ ν : Fin 4) :
    ContDiff ℝ ∞ (fun z => einsteinUp (gF e z) (ginvOf (gF e z)) (dF (gF e) z) (ddF (gF e) z) μ ν) := by
  obtain ⟨h1, h2, h3, h4⟩ := metric_jets_smooth he hdet
  exact contDiff_einsteinUp_field h1 h2 h3 h4 μ ν

theorem contDiff_volume_comp (he : ContDiff ℝ ∞ e) (hdet : ∀ z, 0 < (e z).det) :
    ContDiff ℝ ∞ (fun z => volume (e z)) :=
  contDiff_iff_contDiffAt.2 fun z =>
    (NativeDensity.contDiffAt_volume (hdet z).ne').comp z he.contDiffAt

theorem contDiff_einsteinCov (κ Λ : ℝ) (he : ContDiff ℝ ∞ e) (hdet : ∀ z, 0 < (e z).det) :
    ContDiff ℝ ∞ (einsteinCov κ Λ e) := by
  obtain ⟨-, h2, -, -⟩ := metric_jets_smooth he hdet
  have hv := contDiff_volume_comp he hdet
  unfold einsteinCov
  refine ContDiff.sum fun μ _ => ContDiff.sum fun ν _ => ?_
  refine ContDiff.smul (𝕜' := ℝ) ?_ ((mvBil μ ν).contDiff.comp he)
  exact ((hv.div_const _).neg).mul ((contDiff_einsteinUp he hdet μ ν).add
    (contDiff_const.mul (h2 μ ν)))

theorem gF_periodic (hep : IsZPeriodic e) : IsZPeriodic (gF e) := fun k x => by
  show (fun i j => metric (e (x + PeriodicCube.zvec k)) i j) = fun i j => metric (e x) i j
  rw [hep k x]

theorem dF_periodic {F : R4 → Fin 4 → Fin 4 → ℝ} (hF : IsZPeriodic F) : IsZPeriodic (dF F) :=
  fun k x => by
    funext α i j
    unfold dF
    rw [hF.pd α k x]

theorem ddF_periodic {F : R4 → Fin 4 → Fin 4 → ℝ} (hF : IsZPeriodic F) : IsZPeriodic (ddF F) :=
  fun k x => by
    funext β α i j
    unfold ddF
    rw [(hF.pd α).pd β k x]

theorem einsteinCov_periodic (κ Λ : ℝ) (hep : IsZPeriodic e) : IsZPeriodic (einsteinCov κ Λ e) :=
  fun k x => by
    have h1 := gF_periodic hep k x
    have h2 := dF_periodic (gF_periodic hep) k x
    have h3 := ddF_periodic (gF_periodic hep) k x
    unfold einsteinCov
    rw [h1, h2, h3, hep k x]

end Smooth

/-- **The Euler identity of the first-order Palatini density** (bridge step P3, gravitational
sector, `thm:native-closure`): for a smooth `ℤ⁴`-periodic coframe field with `det e > 0`, the
continuum Euler–Lagrange covector of `L^{(1)} = palatiniFirstOrder κ Λ` is the Einstein covector
`δ ↦ -(v(e)/(2κ)) (G^{μν}(g) + Λ g^{μν}) δg_{μν}`, `g = eᵀηe`, `δg = δᵀηe + eᵀηδ`, with
`G^{μν} = g^{μa}g^{νb}G_{ab}` the Einstein tensor of the library (`HarmonicDefect.einstein`) of the
metric 2-jet `(g, ∂g, ∂∂g)`. -/
theorem palatini_euler (κ Λ : ℝ) {e : R4 → Mat} (he : ContDiff ℝ ∞ e) (hep : IsZPeriodic e)
    (hdet : ∀ z, 0 < (e z).det) : contEuler (Lg κ Λ) e = einsteinCov κ Λ e := by
  refine ContEulerCalc.contEuler_eq_of_pointwise isOpen_chartJ (contDiffOn_Lg κ Λ) he hep
    (fun y => (hdet y).ne') (contDiff_einsteinCov κ Λ he hdet) (einsteinCov_periodic κ Λ hep)
    fun v hv hvp => ?_
  have hJe : ContDiff ℝ ∞ (jet1 e) := ContEulerBounds.contDiff_jet1_infty he
  have hJv : ContDiff ℝ ∞ (jet1 v) := ContEulerBounds.contDiff_jet1_infty hv
  have hg := contDiff_gF he
  have hk := contDiff_kF he hv
  have hkp : IsZPeriodic (kF e v) := fun k x => by
    show (fun i j => metricVarM (e (x + PeriodicCube.zvec k)) (v (x + PeriodicCube.zvec k)) i j) =
      fun i j => metricVarM (e x) (v x) i j
    rw [hep k x, hvp k x]
  have hJep : IsZPeriodic (jet1 e) := fun k x => by simp only [jet1, hep k x, hep.fderiv k x]
  have hJvp : IsZPeriodic (jet1 v) := fun k x => by simp only [jet1, hvp k x, hvp.fderiv k x]
  refine ⟨fun μ y => (2 * κ)⁻¹ * palatiniFlux (gF e) (kF e v) μ y +
      fderiv ℝ (FZ κ μ) (jet1 e y) (jet1 v y), fun μ => ?_, fun μ => ?_, fun z => ?_⟩
  · -- smoothness of the flux
    have hW : ContDiff ℝ ∞ (palatiniFlux (gF e) (kF e v) μ) := by
      obtain ⟨h1, h2, h3, -⟩ := metric_jets_smooth he hdet
      have hk1 : ∀ a b, ContDiff ℝ ∞ (fun z => kF e v z a b) := fun a b =>
        contDiff_pi.1 (contDiff_pi.1 hk a) b
      have hk2 : ∀ α a b, ContDiff ℝ ∞ (fun z => dF (kF e v) z α a b) := fun α a b =>
        contDiff_pi.1 (contDiff_pi.1 (contDiff_pd' hk α) a) b
      have hvol : ContDiff ℝ ∞ (fun z => volM (gF e z)) := contDiff_volume_comp he hdet
      exact hvol.mul (contDiff_fluxV_field h2 (contDiff_chrVar_field h2 h3 hk1 hk2) μ)
    exact ((contDiff_const.mul hW).add (ContEulerCalc.contDiff_fderiv_apply isOpen_chartJ
      (contDiffOn_FZ κ μ) hJe hJv (fun y => (hdet y).ne'))).of_le (by simp)
  · -- periodicity of the flux
    intro k x
    have h1 := gF_periodic hep k x
    have h2 := dF_periodic (gF_periodic hep) k x
    have h3 := dF_periodic hkp k x
    show (2 * κ)⁻¹ * palatiniFlux (gF e) (kF e v) μ (x + PeriodicCube.zvec k) +
        fderiv ℝ (FZ κ μ) (jet1 e (x + PeriodicCube.zvec k)) (jet1 v (x + PeriodicCube.zvec k)) = _
    unfold palatiniFlux
    rw [h1, h2, h3, hkp k x, hJep k x, hJvp k x]
  · -- the pointwise formula
    rw [einsteinCov_apply]
    exact palatini_variation_pointwise κ Λ he hv hep hvp hdet z


/-! ### Arbitrary periods: the dilation `x ↦ L x` (bridge step P4 for the gravitational row) -/

theorem dchr2_smul {n : Type*} [Fintype n] [DecidableEq n] (gi : n → n → ℝ)
    (ddg : n → n → n → n → ℝ) (c : ℝ) :
    dchr2 gi (fun β α a b => c * ddg β α a b) = fun α l μ ν => c * dchr2 gi ddg α l μ ν := by
  funext α l μ ν
  simp only [dchr2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  ring

/-- **Homogeneity of the Einstein tensor in the jets**: scaling `∂g ↦ c ∂g`, `∂∂g ↦ c² ∂∂g`
scales `G^{μν}` by `c²`. -/
theorem einsteinUp_scale {n : Type*} [Fintype n] [DecidableEq n] (g gi : n → n → ℝ)
    (dg : n → n → n → ℝ) (ddg : n → n → n → n → ℝ) (c : ℝ) (μ ν : n) :
    einsteinUp g gi (fun α a b => c * dg α a b) (fun β α a b => c ^ 2 * ddg β α a b) μ ν =
      c ^ 2 * einsteinUp g gi dg ddg μ ν := by
  have hR : ∀ a b, ricci gi (fun α a b => c * dg α a b) (fun β α a b => c ^ 2 * ddg β α a b) a b =
      c ^ 2 * ricci gi dg ddg a b := by
    intro a b
    unfold ricci
    have hD : dchr gi (fun α a b => c * dg α a b) (fun β α a b => c ^ 2 * ddg β α a b) =
        fun α l a b => c ^ 2 * dchr gi dg ddg α l a b := by
      funext α l a b
      unfold dchr
      rw [dchr1_smul, dchr2_smul]
      ring
    rw [chr_smul, hD, ricciJ_smul]
  have hRf : ricci gi (fun α a b => c * dg α a b) (fun β α a b => c ^ 2 * ddg β α a b) =
      fun a b => c ^ 2 * ricci gi dg ddg a b := funext fun a => funext fun b => hR a b
  have hT : trG gi (fun a b => c ^ 2 * ricci gi dg ddg a b) = c ^ 2 * trG gi (ricci gi dg ddg) := by
    unfold trG
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  have hE : ∀ a b, einstein g gi (fun α a b => c * dg α a b) (fun β α a b => c ^ 2 * ddg β α a b) a b =
      c ^ 2 * einstein g gi dg ddg a b := by
    intro a b
    unfold einstein
    rw [hRf, hT]
    ring
  unfold einsteinUp
  simp only [hE, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem pd_comp_smul {F : R4 → Fin 4 → Fin 4 → ℝ} (_hF : Differentiable ℝ F) (L : ℝ)
    (α : Fin 4) (x : R4) : pd (fun y => F (L • y)) α x = L • pd F α (L • x) := by
  unfold SobolevOpen.pd
  rw [fderiv_comp_smul (f := F) L]
  simp

theorem dF_gF_scale {e : R4 → Mat} (he : ContDiff ℝ ∞ e) (L : ℝ) (x : R4) :
    dF (gF fun y => e (L • y)) x = fun α a b => L * dF (gF e) (L • x) α a b := by
  have hg := contDiff_gF he
  funext α a b
  unfold dF
  have : gF (fun y => e (L • y)) = fun y => gF e (L • y) := rfl
  rw [this, pd_comp_smul (hg.differentiable (by simp)) L α x]
  simp

theorem ddF_gF_scale {e : R4 → Mat} (he : ContDiff ℝ ∞ e) (L : ℝ) (x : R4) :
    ddF (gF fun y => e (L • y)) x = fun β α a b => L ^ 2 * ddF (gF e) (L • x) β α a b := by
  have hg := contDiff_gF he
  funext β α a b
  unfold ddF
  have h1 : pd (gF fun y => e (L • y)) α = fun y => L • pd (gF e) α (L • y) := by
    funext y
    exact pd_comp_smul (hg.differentiable (by simp)) L α y
  rw [h1]
  have h2 : pd (fun y => L • pd (gF e) α (L • y)) β x =
      L • pd (fun y => pd (gF e) α (L • y)) β x := by
    have hdf : DifferentiableAt ℝ (fun y => pd (gF e) α (L • y)) x :=
      (((contDiff_pd' hg α).differentiable (by simp)) (L • x)).comp x
        (differentiableAt_id.const_smul L)
    have hh := (hdf.hasFDerivAt.const_smul L).fderiv
    unfold SobolevOpen.pd
    rw [show (fun y => L • (fderiv ℝ (gF e) (L • y)) (Pi.single α 1)) =
      L • fun y => pd (gF e) α (L • y) from rfl, hh]
    rfl
  rw [h2, pd_comp_smul ((contDiff_pd' hg α).differentiable (by simp)) L β x]
  simp [sq, mul_assoc]

theorem einsteinCov_scale {e : R4 → Mat} (he : ContDiff ℝ ∞ e) (κ Λ L : ℝ) (x : R4) :
    einsteinCov κ (Λ * L ^ 2) (fun y => e (L • y)) x = L ^ 2 • einsteinCov κ Λ e (L • x) := by
  ext δ
  rw [ContinuousLinearMap.smul_apply, einsteinCov_apply, einsteinCov_apply, smul_eq_mul]
  have hg : gF (fun y => e (L • y)) x = gF e (L • x) := rfl
  rw [dF_gF_scale he, ddF_gF_scale he, hg]
  simp only [einsteinUp_scale, Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
  ring

/-- `ℤ⁴`-periodicity of a dilated field. -/
def IsLPeriodic (L : ℝ) (e : R4 → Mat) : Prop := IsZPeriodic fun x => e (L • x)

/-- **The Euler identity of the first-order Palatini density for fields of any period `L > 0`**
(in particular the period-`2π` box of `thm:native-source`): for a smooth coframe field with
`e(x + L k) = e(x)` (`k ∈ ℤ⁴`) and `det e > 0`, `contEuler L^{(1)} e = einsteinCov κ Λ e`. -/
theorem palatini_euler_period (κ Λ : ℝ) {L : ℝ} (hL : 0 < L) {e : R4 → Mat}
    (he : ContDiff ℝ ∞ e) (hep : IsLPeriodic L e) (hdet : ∀ z, 0 < (e z).det) :
    contEuler (Lg κ Λ) e = einsteinCov κ Λ e := by
  have hL0 : L ≠ 0 := hL.ne'
  have hLi : L⁻¹ ≠ 0 := inv_ne_zero hL0
  set et : R4 → Mat := fun x => e (L • x) with het
  have het_s : ContDiff ℝ ∞ et := he.comp (contDiff_const_smul L)
  have het_det : ∀ z, 0 < (et z).det := fun z => hdet _
  have hEt := palatini_euler κ (Λ * L ^ 2) het_s hep het_det
  have hscale : ∀ wp : Mat × (Fin 4 → Mat), Lg κ Λ wp =
      (L⁻¹) ^ 2 * Lg κ (Λ * L ^ 2) (DiscreteEulerConsistency.scalePE Mat hLi wp) := by
    intro wp
    rw [DiscreteEulerConsistency.scalePE_apply, inv_inv]
    unfold Lg NativeGravityJet.palatiniFirstOrder
    have hq := NativeGravityJet.gravCurv_scale κ 0 L⁻¹ hLi (fun _ => wp.1)
      (fun sl => wp.2 sl.2)
    rw [inv_inv, zero_mul] at hq
    have hcj : NativeGravityJet.constJet wp.1 (L • wp.2) =
        ((fun _ => wp.1), L • fun sl : NativeDensity.Shift × Fin 4 => wp.2 sl.2) := rfl
    have hcj0 : NativeGravityJet.constJet wp.1 wp.2 =
        ((fun _ => wp.1), fun sl : NativeDensity.Shift × Fin 4 => wp.2 sl.2) := rfl
    rw [hcj, hcj0, hq]
    field_simp
  funext z
  have hfun : (fun z => et (L⁻¹ • z)) = e := by
    funext z
    simp [het, smul_smul, mul_inv_cancel₀ hL0]
  have h := DiscreteEulerConsistency.contEuler_scale (V := Mat) hLi hscale et z
  rw [hfun] at h
  rw [h, hEt, einsteinCov_scale he κ Λ L, smul_smul, smul_smul, inv_pow,
    inv_mul_cancel₀ (pow_ne_zero 2 hL0), one_smul]
  congr 1
  simp [mul_inv_cancel₀ hL0]


/-- Non-vacuity: the flat coframe `e ≡ 1` satisfies the hypotheses of `palatini_euler` (and of
`palatini_euler_period` for every period). -/
example (κ Λ : ℝ) : contEuler (Lg κ Λ) (fun _ : R4 => (1 : Mat)) =
    einsteinCov κ Λ (fun _ : R4 => (1 : Mat)) :=
  palatini_euler κ Λ contDiff_const (fun _ _ => rfl) (fun _ => by simp)

example (κ Λ : ℝ) : contEuler (Lg κ Λ) (fun _ : R4 => (1 : Mat)) =
    einsteinCov κ Λ (fun _ : R4 => (1 : Mat)) :=
  palatini_euler_period κ Λ (L := 2 * Real.pi) (by positivity) contDiff_const (fun _ _ => rfl)
    (fun _ => by simp)

end

end PalatiniEuler

end RenewalGeometry
