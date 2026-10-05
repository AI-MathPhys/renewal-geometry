/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Action.NativeFirstJetNormalFormExact
import RenewalGeometry.Algebra.SeriesLogChart

/-!
# Fréchet differentiability of the native local action on its chart

The finite local common action `S_h^{loc}` (`NativeDensity.localAction`, `eq:native-local-action`
of the Einstein–SM action-closure manuscript) is a smooth function of the complete nodal record
`y : (ℤ/n)⁴ → (e, A, H, Ψ, Ψ̄)` at every record in its admissible chart:

* the coframes are nondegenerate, `det e(x) ≠ 0`;
* the Cartan plaquettes are in the logarithm chart, `‖L_{μν}(x) - 1‖ < 1`;
* the gauge plaquettes are in the logarithm chart, `‖U_{μν}(x) - 1‖ < 1`.

`contDiffAt_localAction` proves `C^∞` regularity at **every fixed mesh `h ≠ 0`** (not only near
`h = 0`, as the jet-level regularity of `lem:native-firstjet-normal-form`), by composing the
analytic logarithm `log(1 + z)` (`‖z‖ < 1`), the exponential, the smooth Cartan reader, the
inverse metric, the volume form and the gamma matrices.  This is the regularity input of the
`(F5)` ⟹ stationarity step of `thm:finite-Wilson-zero-defect` and of the stationarity clause of
`prop:equivariant-native-budgets` (the derivative along any differentiable curve of records is
the Fréchet derivative applied to its velocity).
-/

open NormedSpace Finset Filter Topology
open scoped ContDiff

namespace RenewalGeometry.NativeFrechet

open ShiftedJetAction (Grid unitVec stencil)
open NativeScaling (Mat omegaLink readerOmega)
open ShiftedPlaquette NativeDensity

noncomputable section

set_option linter.unusedSectionVars false

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-! ### Building blocks -/

section Blocks

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {𝔅 : Type*} [NormedRing 𝔅] [NormedAlgebra ℝ 𝔅] [CompleteSpace 𝔅]

/-- `exp ∘ f` is smooth wherever `f` is. -/
@[fun_prop]
theorem ContDiffAt.nexp {f : E → 𝔅} {z : E} (hf : ContDiffAt ℝ ∞ f z) :
    ContDiffAt ℝ ∞ (fun z => exp (f z)) z :=
  (exp_analytic (𝕂 := ℝ) (f z)).contDiffAt.comp z hf

variable [NormOneClass 𝔅]

/-- `log(1 + ·) ∘ f` is smooth wherever `f` is smooth with `‖f‖ < 1`. -/
theorem ContDiffAt.logOneAdd {f : E → 𝔅} {z : E} (hf : ContDiffAt ℝ ∞ f z) (hz : ‖f z‖ < 1) :
    ContDiffAt ℝ ∞ (fun z => logOneAdd (f z)) z :=
  (SeriesLogChart.analyticAt_logOneAdd hz).contDiffAt.comp z hf

variable {n : ℕ} [NeZero n]

/-- **The logarithmic field strength is smooth on its chart**: for any smooth family of
connections `F(z)`, `z ↦ F^h_{μν}[F(z)](x) = h⁻² log(plaquette)` is smooth at every `z` whose
plaquette is in the logarithm chart. -/
theorem contDiffAt_fieldStrength {F : E → Fin 4 → Grid n → 𝔅} {z : E}
    (hF : ∀ μ x, ContDiffAt ℝ ∞ (fun z => F z μ x) z) (h : ℝ) (x : Grid n) (μ ν : Fin 4)
    (hP : ‖NativeScaling.gaugePlaquette h (F z) x μ ν - 1‖ < 1) :
    ContDiffAt ℝ ∞ (fun z => NativeScaling.fieldStrength h (F z) x μ ν) z := by
  unfold NativeScaling.fieldStrength
  refine ContDiffAt.const_smul _ (ContDiffAt.logOneAdd ?_ hP)
  unfold NativeScaling.gaugePlaquette
  have h1 := hF μ x
  have h2 := hF ν (x + unitVec n μ)
  have h3 := hF μ (x + unitVec n ν)
  have h4 := hF ν x
  fun_prop

/-- The antisymmetric extension of a smooth packet is smooth. -/
theorem contDiffAt_antisym {α : Type*} [NormedAddCommGroup α] [NormedSpace ℝ α]
    {P : E → Fin 4 → Fin 4 → α} {z : E} (μ ν : Fin 4)
    (hP : ∀ μ ν, μ < ν → ContDiffAt ℝ ∞ (fun z => P z μ ν) z) :
    ContDiffAt ℝ ∞ (fun z => antisym (P z) μ ν) z := by
  unfold antisym
  by_cases h1 : μ < ν
  · simp only [h1, ite_true]; exact hP μ ν h1
  · by_cases h2 : ν < μ
    · simp only [h1, h2, ite_false, ite_true]; exact (hP ν μ h2).neg
    · simp only [h1, h2, ite_false]; exact contDiffAt_const

end Blocks

/-! ### The four densities -/

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
variable (D : Data 𝔄 𝓗 𝓢) {n : ℕ} [NeZero n]

theorem contDiff_coframe (x : Grid n) :
    ContDiff ℝ ∞ (fun y : Grid n → Field 𝔄 𝓗 𝓢 => coframe y x) := by
  unfold coframe; fun_prop

theorem contDiff_gauge (μ : Fin 4) (x : Grid n) :
    ContDiff ℝ ∞ (fun y : Grid n → Field 𝔄 𝓗 𝓢 => NativeDensity.gauge y μ x) := by
  unfold NativeDensity.gauge; fun_prop

/-- The Yang–Mills density is smooth on the gauge-plaquette chart. -/
theorem contDiffAt_ymDensity (h : ℝ) {y : Grid n → Field 𝔄 𝓗 𝓢} (x : Grid n)
    (hdet : (coframe y x).det ≠ 0)
    (hP : ∀ μ ν, μ < ν → ‖NativeScaling.gaugePlaquette h (NativeDensity.gauge y) x μ ν - 1‖ < 1) :
    ContDiffAt ℝ ∞ (fun y : Grid n → Field 𝔄 𝓗 𝓢 => ymDensity D h y x) y := by
  have hF : ∀ μ ν, μ < ν → ContDiffAt ℝ ∞ (fun y : Grid n → Field 𝔄 𝓗 𝓢 =>
      NativeScaling.fieldStrength h (NativeDensity.gauge y) x μ ν) y := fun μ ν hμν =>
    contDiffAt_fieldStrength (F := fun y : Grid n → Field 𝔄 𝓗 𝓢 => NativeDensity.gauge y)
      (fun μ x => (contDiff_gauge μ x).contDiffAt) h x μ ν (hP μ ν hμν)
  have hA : ∀ μ ν, ContDiffAt ℝ ∞ (fun y : Grid n → Field 𝔄 𝓗 𝓢 =>
      antisym (NativeScaling.fieldStrength h (NativeDensity.gauge y) x) μ ν) y := fun μ ν =>
    contDiffAt_antisym (P := fun y : Grid n → Field 𝔄 𝓗 𝓢 =>
      NativeScaling.fieldStrength h (NativeDensity.gauge y) x) μ ν hF
  have he : ContDiffAt ℝ ∞ (fun y : Grid n → Field 𝔄 𝓗 𝓢 => coframe y x) y :=
    (contDiff_coframe x).contDiffAt
  have hv : ContDiffAt ℝ ∞ (fun y : Grid n → Field 𝔄 𝓗 𝓢 => volume (coframe y x)) y :=
    ContDiffAt.comp (g := volume) y (contDiffAt_volume hdet) he
  have hg : ∀ μ ν, ContDiffAt ℝ ∞ (fun y : Grid n → Field 𝔄 𝓗 𝓢 => ginv (coframe y x) μ ν) y :=
    fun μ ν => ContDiffAt.comp (g := fun e => ginv e μ ν) y (contDiffAt_ginv μ ν hdet) he
  unfold ymDensity
  fun_prop

/-- The coframe-derived connection `ω_{μ,h}(x)` is smooth where the coframe is nondegenerate. -/
theorem contDiffAt_omegaLink (h : ℝ) {y : Grid n → Field 𝔄 𝓗 𝓢} (z : Grid n) (μ : Fin 4)
    (hy : (coframe y z).det ≠ 0) :
    ContDiffAt ℝ ∞ (fun y : Grid n → Field 𝔄 𝓗 𝓢 => omegaLink h (coframe y) z μ) y := by
  unfold omegaLink
  have h1 : ContDiffAt ℝ ∞ (fun y : Grid n → Field 𝔄 𝓗 𝓢 =>
      (coframe y z, fun lam => ShiftedJetAction.fwdDiff h lam (coframe y) z)) y := by
    unfold coframe ShiftedJetAction.fwdDiff
    fun_prop
  refine contDiffAt_pi.mpr fun a => contDiffAt_pi.mpr fun b => ?_
  exact (contDiffAt_readerOmega_entry μ a b
    (q := (coframe y z, fun lam => ShiftedJetAction.fwdDiff h lam (coframe y) z)) hy).comp y h1

/-- The gravitational (Cartan) density is smooth on the Cartan-plaquette chart. -/
theorem contDiffAt_gravityDensity (h : ℝ) {y : Grid n → Field 𝔄 𝓗 𝓢} (x : Grid n)
    (hdet : ∀ z, (coframe y z).det ≠ 0)
    (hP : ∀ μ ν, μ < ν → ‖cartanPlaquette h (coframe y) x μ ν - 1‖ < 1) :
    ContDiffAt ℝ ∞ (fun y : Grid n → Field 𝔄 𝓗 𝓢 => gravityDensity D h y x) y := by
  have hω : ∀ μ z, ContDiffAt ℝ ∞ (fun y : Grid n → Field 𝔄 𝓗 𝓢 =>
      matToOp (omegaLink h (coframe y) z μ)) y := fun μ z => by
    simp only [← matToOpL_apply]
    exact matToOpL.contDiff.contDiffAt.comp y (contDiffAt_omegaLink h z μ (hdet z))
  have hF : ∀ μ ν, μ < ν → ContDiffAt ℝ ∞ (fun y : Grid n → Field 𝔄 𝓗 𝓢 =>
      cartanCurvature h (coframe y) x μ ν) y := fun μ ν hμν =>
    contDiffAt_fieldStrength (F := fun (y : Grid n → Field 𝔄 𝓗 𝓢) μ z =>
      matToOp (omegaLink h (coframe y) z μ)) (fun μ z => hω μ z) h x μ ν (hP μ ν hμν)
  have hA : ∀ μ ν, ContDiffAt ℝ ∞ (fun y : Grid n → Field 𝔄 𝓗 𝓢 =>
      antisym (cartanCurvature h (coframe y) x) μ ν) y := fun μ ν =>
    contDiffAt_antisym (P := fun y : Grid n → Field 𝔄 𝓗 𝓢 =>
      cartanCurvature h (coframe y) x) μ ν hF
  have he : ContDiffAt ℝ ∞ (fun y : Grid n → Field 𝔄 𝓗 𝓢 => coframe y x) y :=
    (contDiff_coframe x).contDiffAt
  have hv : ContDiffAt ℝ ∞ (fun y : Grid n → Field 𝔄 𝓗 𝓢 => volume (coframe y x)) y :=
    ContDiffAt.comp (g := volume) y (contDiffAt_volume (hdet x)) he
  have hp : ∀ μ ν a b, ContDiffAt ℝ ∞ (fun y : Grid n → Field 𝔄 𝓗 𝓢 =>
      pal D.κ (coframe y x) μ ν a b) y := fun μ ν a b =>
    ContDiffAt.comp (g := fun e => pal D.κ e μ ν a b) y (contDiffAt_pal D.κ μ ν a b (hdet x)) he
  unfold gravityDensity
  fun_prop

/-- The jet of a record at a node, at the mesh `h` and `ν = 1`. -/
theorem contDiff_stencilTriple (h : ℝ) (x : Grid n) :
    ContDiff ℝ ∞ (fun y : Grid n → Field 𝔄 𝓗 𝓢 =>
      ((h * 1, (1 : ℝ)⁻¹, stencil (h * 1) (shiftVec n) x y) :
        ℝ × ℝ × Jet (Field 𝔄 𝓗 𝓢))) := by
  have := (stencil (h * 1) (shiftVec n) x : (Grid n → Field 𝔄 𝓗 𝓢) →L[ℝ] _).contDiff
    (n := ∞)
  fun_prop

theorem stencil_center (h : ℝ) (x : Grid n) (y : Grid n → Field 𝔄 𝓗 𝓢) :
    ((stencil h (shiftVec n) x y).1 none).1 = coframe y x := by
  rw [ShiftedJetAction.stencil_apply]
  simp [shiftVec_none, coframe]

/-- The Higgs density is smooth wherever the coframe is nondegenerate. -/
theorem contDiffAt_higgsDensity {h : ℝ} (hh : h ≠ 0) {y : Grid n → Field 𝔄 𝓗 𝓢} (x : Grid n)
    (hdet : (coframe y x).det ≠ 0) :
    ContDiffAt ℝ ∞ (fun y : Grid n → Field 𝔄 𝓗 𝓢 => higgsDensity D h y x) y := by
  have e : (fun y : Grid n → Field 𝔄 𝓗 𝓢 => higgsDensity D h y x) = fun y =>
      (1 : ℝ) ^ 2 * normHiggs D (h * 1, (1 : ℝ)⁻¹, stencil (h * 1) (shiftVec n) x y) :=
    funext fun y => higgsDensity_eq_scaled D hh one_ne_zero y x
  rw [e]
  refine ContDiffAt.mul contDiffAt_const ?_
  refine ContDiffAt.comp (g := normHiggs D) y ?_ (contDiff_stencilTriple h x).contDiffAt
  refine contDiffAt_normHiggs D ?_
  simpa [mul_one] using (stencil_center (h * 1) x y).symm ▸ hdet

/-- The Dirac–Yukawa density is smooth wherever the coframe is nondegenerate. -/
theorem contDiffAt_diracDensity {h : ℝ} (hh : h ≠ 0) {y : Grid n → Field 𝔄 𝓗 𝓢} (x : Grid n)
    (hdet : (coframe y x).det ≠ 0) :
    ContDiffAt ℝ ∞ (fun y : Grid n → Field 𝔄 𝓗 𝓢 => diracDensity D h y x) y := by
  have e : (fun y : Grid n → Field 𝔄 𝓗 𝓢 => diracDensity D h y x) = fun y =>
      (1 : ℝ) * normD D (h * 1, (1 : ℝ)⁻¹, stencil (h * 1) (shiftVec n) x y) :=
    funext fun y => diracDensity_eq_scaled D hh one_ne_zero y x
  rw [e]
  refine ContDiffAt.mul contDiffAt_const ?_
  refine ContDiffAt.comp (g := normD D) y ?_ (contDiff_stencilTriple h x).contDiffAt
  refine contDiffAt_normD D ?_
  simpa [mul_one] using (stencil_center (h * 1) x y).symm ▸ hdet

/-- **The native local action is smooth on its chart** (every fixed mesh `h ≠ 0`):
nondegenerate coframes, Cartan and gauge plaquettes in the logarithm chart. -/
theorem contDiffAt_localAction {h : ℝ} (hh : h ≠ 0) {y : Grid n → Field 𝔄 𝓗 𝓢}
    (hdet : ∀ x, (coframe y x).det ≠ 0)
    (hC : ∀ x μ ν, μ < ν → ‖cartanPlaquette h (coframe y) x μ ν - 1‖ < 1)
    (hG : ∀ x μ ν, μ < ν → ‖NativeScaling.gaugePlaquette h (NativeDensity.gauge y) x μ ν - 1‖ < 1) :
    ContDiffAt ℝ ∞ (localAction D h) y := by
  unfold localAction nativeDensity
  refine ContDiffAt.mul contDiffAt_const (ContDiffAt.sum fun x _ => ?_)
  exact (((contDiffAt_gravityDensity D h x hdet (hC x)).add
    (contDiffAt_ymDensity D h x (hdet x) (hG x))).add
    (contDiffAt_higgsDensity D hh x (hdet x))).add (contDiffAt_diracDensity D hh x (hdet x))

theorem differentiableAt_localAction {h : ℝ} (hh : h ≠ 0) {y : Grid n → Field 𝔄 𝓗 𝓢}
    (hdet : ∀ x, (coframe y x).det ≠ 0)
    (hC : ∀ x μ ν, μ < ν → ‖cartanPlaquette h (coframe y) x μ ν - 1‖ < 1)
    (hG : ∀ x μ ν, μ < ν → ‖NativeScaling.gaugePlaquette h (NativeDensity.gauge y) x μ ν - 1‖ < 1) :
    DifferentiableAt ℝ (localAction D h) y :=
  (contDiffAt_localAction D hh hdet hC hG).differentiableAt (by simp)

end

end RenewalGeometry.NativeFrechet
