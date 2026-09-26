/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Action.NativeScalingRegularityExact
import RenewalGeometry.Action.ShiftedFirstJetNormalFormExact

/-!
# The four native densities and their amplitude-preserving scaling
  (`eq:native-densities`, `lem:native-scaling`, Einstein–Standard-Model action-closure manuscript)

This file assembles the local density `eq:native-densities` of the finite action
`eq:native-local-action` from the link data of `NativeScalingBlocksExact` and proves
`lem:native-scaling`.

* **Fields.**  A nodal record `y : Grid n → Field` carries at every node the coframe `e^a_μ`
  (a real `4 × 4` matrix), the gauge potentials `A_μ` (in a real Banach algebra `𝔄`, the gauge
  Lie algebra in its representation), the Higgs field `H ∈ 𝓗`, the spinor `Ψ ∈ 𝓢` and the
  co-spinor `Ψ̄ ∈ 𝓢 →L[ℝ] ℂ` (a complex-valued functional, so that `Ψ̄ ⋯ Ψ` is a complex
  number whose real part enters the density).
* **Coefficient bank and representation data** (`Data`): `κ, Λ`, the Higgs potential
  `V(H) = λ_H (|H|² - v_H²)²` with `|H|² = Re⟨H, H⟩` (`potential`), the invariant form
  `⟨·,·⟩_𝐠` on the gauge algebra, the Hermitian form `Re⟨·,·⟩` on the Higgs space, the Higgs
  and spin representations `ρ_H, ρ_S` (continuous algebra homomorphisms, so that
  `ρ(e^{hA}) = e^{h dρ(A)}`), the spin representation `σ` of the Lorentz Lie algebra (continuous
  linear), the gamma matrices `γ^a` (operators on `𝓢`) and the Yukawa map `H ↦ 𝓜_𝐘(H)`
  (continuous linear in `H`).
* **The densities** (`gravityDensity`, `ymDensity`, `higgsDensity`, `diracDensity`,
  `nativeDensity`): `v(e) = √(-det g)` (`volume`), `g^{μν} = (g_{μν})⁻¹` (`ginv`),
  `e_a^μ e^{bν} = (e⁻¹)^μ_a (e⁻¹ η)^ν_b` (`pal`), `γ^μ(e) = (e⁻¹)^μ_a γ^a` (`gammaMu`), the
  Cartan plaquette `R^h_{μν} = h⁻² log(L_μ L_ν L_μ⁻¹ L_ν⁻¹)` with `L_μ = e^{h ω_{μ,h}}`
  computed in the operator algebra of `ℝ⁴` (`cartanCurvature`, entries `opEntry`), the gauge
  field strength `F^h` of `NativeScalingBlocksExact`, the Higgs link `K^h_μ`, the covariant
  Dirac differences `∇^h_μ Ψ`, `∇^{h,∨}_μ Ψ̄` with the spin link `V_μ = e^{hσ(ω)} ρ_S(U_μ)` and
  its inverse `V_μ⁻¹ = ρ_S(U_μ⁻¹) e^{-hσ(ω)}` (`spinLinkInv`, `spinLink_mul_spinLinkInv`).
  The plaquettes are defined for `μ < ν` and extended antisymmetrically (`antisym`).
* **`lem:native-scaling`** (`nativeDensity_eq_scaled`): with `ρ = hK`, `ν = K⁻¹` and the
  nodal amplitudes unchanged,
  `𝓛_h(y)(x) = K² 𝓛̃^B(ρ, ν; Ξ_ρ ỹ(x)) + K 𝓛̃^D(ρ, ν; Ξ_ρ ỹ(x))`
  exactly, where `Ξ_ρ ỹ(x)` is the shifted first jet (shifted values and `ρ`-normalised first
  differences over the shifts `0, ±e_μ`) of the record together with that of the normalised
  coframe connection `ω̃_ρ = Ω(e, δ⁺_ρ e)`, and `𝓛̃^B` (`normB`), `𝓛̃^D` (`normD`) are the
  normalised bosonic and Dirac stencil densities.  The potential, mass and cosmological
  coefficients appear with the factors `ν², ν, ν²`.  The summed form and the Euler rows
  (`sum_nativeDensity_eq_scaled`, `fderiv_sum_nativeDensity`) carry the same factors.
* **Regularity clause** (`contDiffAt_normB`, `contDiffAt_normD`,
  `exists_uniform_bound_normB`, `exists_uniform_bound_normD`): both normalised densities are
  smooth in `(ρ, ν, jet)` at every point with `ρ = 0`, every `ν`, and nondegenerate coframe
  `det e ≠ 0`, and all their fixed-order derivatives are bounded uniformly for `|ρ| ≤ ρ₀`,
  `0 ≤ ν ≤ 1` and jets in a compact set of the nondegenerate chart.

Scoped hypotheses (disclosed): `𝔄` is a real Banach algebra with `‖1‖ = 1`; the Higgs and
spinor spaces are real Banach spaces (their complex structure is not used) with the Hermitian
forms rendered as real continuous bilinear forms; `ρ_H, ρ_S` are continuous algebra
homomorphisms; the gamma matrices, the Yukawa map and the invariant forms are arbitrary
continuous (bi)linear data; the matrix logarithm of the Cartan plaquette is the series
logarithm of `lem:native-plaquette` computed in the operator algebra of `ℝ⁴`.
-/

open NormedSpace Finset
open scoped ContDiff

namespace RenewalGeometry
namespace NativeDensity

open ShiftedJetAction (Grid unitVec fwdDiff stencil)
open NativeScaling (Mat eta metric readerOmega omegaLink)
open ShiftedPlaquette

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-! ### Smooth coefficient functions of the coframe -/

theorem contDiff_det {k : WithTop ℕ∞} : ContDiff ℝ k (fun M : Mat => M.det) := by
  simp only [Matrix.det_apply']
  fun_prop

theorem contDiff_adjugate_entry (i j : Fin 4) {k : WithTop ℕ∞} :
    ContDiff ℝ k (fun A : Mat => A.adjugate i j) := by
  simp only [Matrix.adjugate_apply, Matrix.det_apply', Matrix.updateRow_apply]
  refine ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun k _ => ?_)
  split_ifs <;> fun_prop

/-- The `(i, j)` entry of the matrix inverse, as a named function. -/
noncomputable def invEntry (i j : Fin 4) (e : Mat) : ℝ := e⁻¹ i j

theorem invEntry_apply (i j : Fin 4) (e : Mat) : invEntry i j e = e⁻¹ i j := rfl

@[fun_prop]
theorem contDiffAt_invEntry (i j : Fin 4) {k : WithTop ℕ∞} {A : Mat} (hA : A.det ≠ 0) :
    ContDiffAt ℝ k (invEntry i j) A := by
  have : invEntry i j = fun M : Mat => (M.det)⁻¹ * M.adjugate i j := by
    funext M
    rw [invEntry, Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul]
  rw [this]
  exact ((contDiffAt_inv ℝ hA).comp A contDiff_det.contDiffAt).mul
    (contDiff_adjugate_entry i j).contDiffAt

theorem det_metric (e : Mat) : (metric e).det = -(e.det) ^ 2 := by
  simp [metric, Matrix.det_mul, Matrix.det_transpose, eta, Matrix.det_diagonal,
    Fin.prod_univ_four]
  ring

theorem det_metric_ne_zero {e : Mat} (he : e.det ≠ 0) : (metric e).det ≠ 0 := by
  rw [det_metric]
  simpa using he

theorem contDiff_metric {k : WithTop ℕ∞} : ContDiff ℝ k (fun e : Mat => metric e) := by
  refine contDiff_pi.mpr fun i => contDiff_pi.mpr fun j => ?_
  simp only [metric, Matrix.mul_apply, Matrix.transpose_apply]
  fun_prop

/-- The volume density `v(e) = √(-det g)`, `g = eᵀ η e`. -/
noncomputable def volume (e : Mat) : ℝ := Real.sqrt (-(metric e).det)

theorem volume_eq_abs_det (e : Mat) : volume e = |e.det| := by
  rw [volume, det_metric, neg_neg, Real.sqrt_sq_eq_abs]

theorem volume_of_det_pos {e : Mat} (he : 0 < e.det) : volume e = e.det := by
  rw [volume_eq_abs_det, abs_of_pos he]

@[fun_prop]
theorem contDiffAt_volume {k : WithTop ℕ∞} {e : Mat} (he : e.det ≠ 0) :
    ContDiffAt ℝ k volume e := by
  have h1 : ContDiffAt ℝ k (fun M : Mat => -(metric M).det) e := by
    have : (fun M : Mat => -(metric M).det) = fun M : Mat => (M.det) ^ 2 :=
      funext fun M => by rw [det_metric, neg_neg]
    rw [this]
    exact (contDiff_det.pow 2).contDiffAt
  have h2 : -(metric e).det ≠ 0 := by
    rw [det_metric, neg_neg]
    exact pow_ne_zero 2 he
  exact (Real.contDiffAt_sqrt h2).comp e h1

/-- The inverse metric `g^{μν}`. -/
noncomputable def ginv (e : Mat) (μ ν : Fin 4) : ℝ := invEntry μ ν (metric e)

@[fun_prop]
theorem contDiffAt_ginv (μ ν : Fin 4) {k : WithTop ℕ∞} {e : Mat} (he : e.det ≠ 0) :
    ContDiffAt ℝ k (fun e => ginv e μ ν) e :=
  (contDiffAt_invEntry μ ν (det_metric_ne_zero he)).comp e contDiff_metric.contDiffAt

/-- The Palatini coefficient `e_a^μ e^{bν} v(e)/(2κ) = v(e)/(2κ) (e⁻¹)^μ_a (e⁻¹ η)^ν_b`. -/
noncomputable def pal (κ : ℝ) (e : Mat) (μ ν a b : Fin 4) : ℝ :=
  volume e / (2 * κ) * (invEntry μ a e * ∑ c, invEntry ν c e * eta c b)

@[fun_prop]
theorem contDiffAt_pal (κ : ℝ) (μ ν a b : Fin 4) {k : WithTop ℕ∞} {e : Mat} (he : e.det ≠ 0) :
    ContDiffAt ℝ k (fun e => pal κ e μ ν a b) e := by
  unfold pal
  fun_prop (disch := assumption)

/-- The operator algebra of `ℝ⁴`, in which the Cartan plaquette logarithm is computed. -/
abbrev Op := (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ)

/-- Matrices as operators on `ℝ⁴` (algebra homomorphism). -/
noncomputable def matToOp : Mat →ₐ[ℝ] Op where
  toFun M := LinearMap.toContinuousLinearMap (Matrix.toLin' M)
  map_one' := by ext; simp
  map_mul' M N := by ext; simp [Matrix.toLin'_mul]
  map_zero' := by ext; simp
  map_add' M N := by ext; simp [map_add]
  commutes' r := by
    ext v i
    simp [Matrix.algebraMap_eq_diagonal, Matrix.mulVec_diagonal]

theorem matToOp_apply (M : Mat) (v : Fin 4 → ℝ) : matToOp M v = M.mulVec v := rfl

theorem continuous_matToOp : Continuous matToOp :=
  LinearMap.continuous_of_finiteDimensional matToOp.toLinearMap

/-- `matToOp` as a continuous linear map. -/
noncomputable def matToOpL : Mat →L[ℝ] Op := ⟨matToOp.toLinearMap, continuous_matToOp⟩

theorem matToOpL_apply (M : Mat) : matToOpL M = matToOp M := rfl

/-- The `(a, b)` matrix entry of an operator on `ℝ⁴`. -/
def opEntry (T : Op) (a b : Fin 4) : ℝ := T (Pi.single b 1) a

theorem opEntry_matToOp (M : Mat) (a b : Fin 4) : opEntry (matToOp M) a b = M a b := by
  simp [opEntry, matToOp_apply, Matrix.mulVec_single]

theorem opEntry_smul (c : ℝ) (T : Op) (a b : Fin 4) : opEntry (c • T) a b = c * opEntry T a b := by
  simp [opEntry]

theorem opEntry_add (S T : Op) (a b : Fin 4) : opEntry (S + T) a b = opEntry S a b + opEntry T a b := by
  simp [opEntry]

theorem opEntry_sub (S T : Op) (a b : Fin 4) : opEntry (S - T) a b = opEntry S a b - opEntry T a b := by
  simp [opEntry]

@[fun_prop]
theorem ContDiff.opEntry {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : WithTop ℕ∞}
    {T : E → Op} (hT : ContDiff ℝ k T) (a b : Fin 4) :
    ContDiff ℝ k (fun z => NativeDensity.opEntry (T z) a b) := by
  unfold NativeDensity.opEntry
  fun_prop

@[fun_prop]
theorem ContDiffAt.opEntry {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : WithTop ℕ∞}
    {T : E → Op} {z : E} (hT : ContDiffAt ℝ k T z) (a b : Fin 4) :
    ContDiffAt ℝ k (fun z => NativeDensity.opEntry (T z) a b) z := by
  unfold NativeDensity.opEntry
  fun_prop

/-- Antisymmetric extension of a quantity defined for `μ < ν`. -/
def antisym {α : Type*} [Zero α] [Neg α] (P : Fin 4 → Fin 4 → α) (μ ν : Fin 4) : α :=
  if μ < ν then P μ ν else if ν < μ then -P ν μ else 0

theorem antisym_smul {α : Type*} [AddCommGroup α] [Module ℝ α] (c : ℝ) (P : Fin 4 → Fin 4 → α)
    (μ ν : Fin 4) : antisym (fun μ ν => c • P μ ν) μ ν = c • antisym P μ ν := by
  unfold antisym
  split_ifs <;> simp

theorem antisym_add {α : Type*} [AddCommGroup α] (P Q : Fin 4 → Fin 4 → α) (μ ν : Fin 4) :
    antisym (fun μ ν => P μ ν + Q μ ν) μ ν = antisym P μ ν + antisym Q μ ν := by
  unfold antisym
  split_ifs <;> simp only [neg_add, add_zero]

@[fun_prop]
theorem ContDiffAt.antisym {E α : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup α] [NormedSpace ℝ α] {k : WithTop ℕ∞} {P : E → Fin 4 → Fin 4 → α} {z : E}
    (hP : ∀ μ ν, ContDiffAt ℝ k (fun z => P z μ ν) z) (μ ν : Fin 4) :
    ContDiffAt ℝ k (fun z => NativeDensity.antisym (P z) μ ν) z := by
  unfold NativeDensity.antisym
  split_ifs <;> fun_prop

/-! ### Auxiliary smoothness lemmas -/

@[fun_prop]
theorem ContDiff.complex_re {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : WithTop ℕ∞}
    {f : E → ℂ} (hf : ContDiff ℝ k f) : ContDiff ℝ k (fun x => (f x).re) :=
  Complex.reCLM.contDiff.comp hf

@[fun_prop]
theorem ContDiffAt.complex_re {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k : WithTop ℕ∞} {f : E → ℂ} {x : E} (hf : ContDiffAt ℝ k f x) :
    ContDiffAt ℝ k (fun x => (f x).re) x :=
  Complex.reCLM.contDiff.contDiffAt.comp x hf

@[fun_prop]
theorem ContDiff.complex_im {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : WithTop ℕ∞}
    {f : E → ℂ} (hf : ContDiff ℝ k f) : ContDiff ℝ k (fun x => (f x).im) :=
  Complex.imCLM.contDiff.comp hf

@[fun_prop]
theorem ContDiffAt.complex_im {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k : WithTop ℕ∞} {f : E → ℂ} {x : E} (hf : ContDiffAt ℝ k f x) :
    ContDiffAt ℝ k (fun x => (f x).im) x :=
  Complex.imCLM.contDiff.contDiffAt.comp x hf

@[fun_prop]
theorem ContDiff.clm_comp' {X E F G : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {k : WithTop ℕ∞}
    {g : X → F →L[ℝ] G} {f : X → E →L[ℝ] F} (hg : ContDiff ℝ k g) (hf : ContDiff ℝ k f) :
    ContDiff ℝ k fun x => (g x).comp (f x) :=
  hg.clm_comp hf

@[fun_prop]
theorem ContDiffAt.clm_comp' {X E F G : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {k : WithTop ℕ∞}
    {g : X → F →L[ℝ] G} {f : X → E →L[ℝ] F} {x : X} (hg : ContDiffAt ℝ k g x)
    (hf : ContDiffAt ℝ k f x) : ContDiffAt ℝ k (fun x => (g x).comp (f x)) x :=
  hg.clm_comp hf

@[fun_prop]
theorem contDiff_expRemainder {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄]
    [NormOneClass 𝔄] {k : WithTop ℕ∞} : ContDiff ℝ k (expRemainder : 𝔄 → 𝔄) :=
  contDiff_iff_contDiffAt.mpr fun x => (analyticAt_expRemainder x).contDiffAt

@[fun_prop]
theorem ContDiff.linkExp {E 𝔄 : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedRing 𝔄]
    [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄] {k : WithTop ℕ∞} {r : E → ℝ}
    {v : E → 𝔄} (hr : ContDiff ℝ k r) (hv : ContDiff ℝ k v) :
    ContDiff ℝ k (fun z => ShiftedPlaquette.linkExp (r z) (v z)) := by
  unfold ShiftedPlaquette.linkExp
  fun_prop

@[fun_prop]
theorem ContDiffAt.linkExp {E 𝔄 : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedRing 𝔄]
    [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄] {k : WithTop ℕ∞} {r : E → ℝ}
    {v : E → 𝔄} {z : E} (hr : ContDiffAt ℝ k r z) (hv : ContDiffAt ℝ k v z) :
    ContDiffAt ℝ k (fun z => ShiftedPlaquette.linkExp (r z) (v z)) z := by
  unfold ShiftedPlaquette.linkExp
  fun_prop

/-- Continuous algebra homomorphisms commute with `exp`. -/
theorem algHom_map_exp {𝔄 𝔹 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄]
    [NormedRing 𝔹] [NormedAlgebra ℝ 𝔹] (f : 𝔄 →ₐ[ℝ] 𝔹) (hf : Continuous f) (x : 𝔄) :
    f (exp x) = exp (f x) := by
  let +nondep : NormedAlgebra ℚ 𝔄 := .restrictScalars ℚ ℝ 𝔄
  let +nondep : NormedAlgebra ℚ 𝔹 := .restrictScalars ℚ ℝ 𝔹
  exact map_exp f hf x

theorem exp_mul_exp_neg {𝔖 : Type*} [NormedRing 𝔖] [NormedAlgebra ℝ 𝔖] [CompleteSpace 𝔖]
    (u : 𝔖) : exp u * exp (-u) = 1 := by
  let +nondep : NormedAlgebra ℚ 𝔖 := .restrictScalars ℚ ℝ 𝔖
  rw [← exp_add_of_commute (Commute.refl _).neg_right, add_neg_cancel, exp_zero]

theorem exp_neg_mul_exp {𝔖 : Type*} [NormedRing 𝔖] [NormedAlgebra ℝ 𝔖] [CompleteSpace 𝔖]
    (u : 𝔖) : exp (-u) * exp u = 1 := by
  let +nondep : NormedAlgebra ℚ 𝔖 := .restrictScalars ℚ ℝ 𝔖
  rw [← exp_add_of_commute (Commute.refl _).neg_left, neg_add_cancel, exp_zero]

/-- Product of two links: `e^{ρ u} e^{(ρν) w} = 1 + ρ (w(ρ,u) + ν w(ρν, w) + ρν w(ρ,u) w(ρν,w))`. -/
theorem exp_mul_exp_eq {𝔖 : Type*} [NormedRing 𝔖] [NormedAlgebra ℝ 𝔖] [CompleteSpace 𝔖]
    [NormOneClass 𝔖] (ρ ν : ℝ) (u w : 𝔖) :
    exp (ρ • u) * exp ((ρ * ν) • w) =
      1 + ρ • (linkExp ρ u + ν • linkExp (ρ * ν) w +
        (ρ * ν) • (linkExp ρ u * linkExp (ρ * ν) w)) := by
  rw [exp_smul_eq_linkExp, exp_smul_eq_linkExp]
  simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_smul_comm, smul_add, smul_smul]
  module

/-! ### Fields, coefficient bank and representation data -/

/-- Shifts of the stencils: `0`, `+e_μ` and `-e_μ`. -/
abbrev Shift := Option (Bool × Fin 4)

/-- The lattice vector of a shift. -/
def shiftVec (n : ℕ) : Shift → Grid n
  | none => 0
  | some (true, μ) => unitVec n μ
  | some (false, μ) => -unitVec n μ

/-- The space of operators on the spinor space. -/
abbrev Spin (𝓢 : Type*) [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] := 𝓢 →L[ℝ] 𝓢

/-- Co-spinors `Ψ̄`: complex-valued continuous functionals on the spinor space. -/
abbrev CoSpinor (𝓢 : Type*) [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] := 𝓢 →L[ℝ] ℂ

/-- The nodal field tuple `(e, A, H, Ψ, Ψ̄)`. -/
abbrev Field (𝔄 𝓗 𝓢 : Type*) [NormedRing 𝔄] [NormedAddCommGroup 𝓗] [NormedAddCommGroup 𝓢]
    [NormedSpace ℝ 𝓢] :=
  Mat × (Fin 4 → 𝔄) × 𝓗 × 𝓢 × CoSpinor 𝓢

/-- The coframe connection field `μ ↦ ω_μ`. -/
abbrev Conn := Fin 4 → Mat

/-- The shifted first jet space of a field type `V`: shifted values and normalised first
differences over the shifts `0, ±e_μ` (the target of `ShiftedJetAction.stencil`). -/
abbrev Jet (V : Type*) := (Shift → V) × (Shift × Fin 4 → V)

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]

/-- The coefficient bank of `eq:total-action` and the finite representation data entering
`eq:native-densities`. -/
structure Data (𝔄 𝓗 𝓢 : Type*) [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [NormedAddCommGroup 𝓗]
    [NormedSpace ℝ 𝓗] [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] where
  /-- gravitational coupling `κ` -/
  κ : ℝ
  /-- cosmological constant `Λ` -/
  Λ : ℝ
  /-- Higgs self-coupling `λ_H` -/
  lamH : ℝ
  /-- Higgs vacuum value `v_H` -/
  vH : ℝ
  /-- the invariant form `⟨·,·⟩_𝐠` on the gauge algebra -/
  ipA : 𝔄 →L[ℝ] 𝔄 →L[ℝ] ℝ
  /-- the Hermitian form `Re⟨·,·⟩` on the Higgs space -/
  hermH : 𝓗 →L[ℝ] 𝓗 →L[ℝ] ℝ
  /-- the Higgs representation `ρ_H` -/
  ρH : 𝔄 →ₐ[ℝ] (𝓗 →L[ℝ] 𝓗)
  ρH_cont : Continuous ρH
  /-- the gauge representation `ρ_S` on spinors -/
  ρS : 𝔄 →ₐ[ℝ] Spin 𝓢
  ρS_cont : Continuous ρS
  /-- the spin representation `σ` of the Lorentz Lie algebra -/
  σ : Mat →L[ℝ] Spin 𝓢
  /-- the gamma matrices `γ^a` -/
  γ : Fin 4 → Spin 𝓢
  /-- the Yukawa map `H ↦ 𝓜_𝐘(H)` -/
  yukawa : 𝓗 →L[ℝ] Spin 𝓢

variable (D : Data 𝔄 𝓗 𝓢)

/-- `ρ_H` as a continuous linear map. -/
noncomputable def Data.ρHL : 𝔄 →L[ℝ] (𝓗 →L[ℝ] 𝓗) := ⟨D.ρH.toLinearMap, D.ρH_cont⟩

theorem Data.ρHL_apply (A : 𝔄) : D.ρHL A = D.ρH A := rfl

/-- `ρ_S` as a continuous linear map. -/
noncomputable def Data.ρSL : 𝔄 →L[ℝ] Spin 𝓢 := ⟨D.ρS.toLinearMap, D.ρS_cont⟩

theorem Data.ρSL_apply (A : 𝔄) : D.ρSL A = D.ρS A := rfl

/-- The Higgs potential `V(H) = λ_H (|H|² - v_H²)²`. -/
noncomputable def potential (H : 𝓗) : ℝ := D.lamH * (D.hermH H H - D.vH ^ 2) ^ 2

/-- `γ^μ(e) = (e⁻¹)^μ_a γ^a`. -/
noncomputable def gammaMu (e : Mat) (μ : Fin 4) : Spin 𝓢 := ∑ a, invEntry μ a e • D.γ a

variable {n : ℕ} [NeZero n]

/-- The coframe component of a record. -/
def coframe (y : Grid n → Field 𝔄 𝓗 𝓢) (x : Grid n) : Mat := (y x).1

/-- The gauge components of a record. -/
def gauge (y : Grid n → Field 𝔄 𝓗 𝓢) (μ : Fin 4) (x : Grid n) : 𝔄 := (y x).2.1 μ

/-- The Higgs component of a record. -/
def higgs (y : Grid n → Field 𝔄 𝓗 𝓢) (x : Grid n) : 𝓗 := (y x).2.2.1

/-- The spinor component of a record. -/
def psi (y : Grid n → Field 𝔄 𝓗 𝓢) (x : Grid n) : 𝓢 := (y x).2.2.2.1

/-- The co-spinor component of a record. -/
def psiBar (y : Grid n → Field 𝔄 𝓗 𝓢) (x : Grid n) : CoSpinor 𝓢 := (y x).2.2.2.2

/-! ### The exact densities `eq:native-densities` -/

/-- The Cartan plaquette logarithm `R^h_{μν} = h⁻² log(L_μ(x) L_ν(x+he_μ) L_μ(x+he_ν)⁻¹ L_ν(x)⁻¹)`,
`L_μ = exp(h ω_{μ,h})`, computed in the operator algebra of `ℝ⁴` (`eq:native-plaquettes`). -/
noncomputable def cartanCurvature (h : ℝ) (e : Grid n → Mat) (x : Grid n) (μ ν : Fin 4) : Op :=
  NativeScaling.fieldStrength h (fun μ x => matToOp (omegaLink h e x μ)) x μ ν

/-- The gravitational density
`𝓛_{g,h} = v(e)/(2κ) e_a^μ e^{bν} (R^h_{μν})^a_b - (Λ/κ) v(e)`. -/
noncomputable def gravityDensity (h : ℝ) (y : Grid n → Field 𝔄 𝓗 𝓢) (x : Grid n) : ℝ :=
  (∑ μ, ∑ ν, ∑ a, ∑ b, pal D.κ (coframe y x) μ ν a b *
      opEntry (antisym (cartanCurvature h (coframe y) x) μ ν) a b) -
    D.Λ / D.κ * volume (coframe y x)

/-- The Yang–Mills density `𝓛_{YM,h} = -¼ v(e) g^{μρ} g^{νσ} ⟨F^h_{μν}, F^h_{ρσ}⟩_𝐠`. -/
noncomputable def ymDensity (h : ℝ) (y : Grid n → Field 𝔄 𝓗 𝓢) (x : Grid n) : ℝ :=
  -(4⁻¹ * volume (coframe y x) * ∑ μ, ∑ ν, ∑ ρ, ∑ σ,
    ginv (coframe y x) μ ρ * ginv (coframe y x) ν σ *
      D.ipA (antisym (NativeScaling.fieldStrength h (gauge y) x) μ ν)
        (antisym (NativeScaling.fieldStrength h (gauge y) x) ρ σ))

/-- The Higgs link `K^h_μ` of `eq:native-matter-links` with the representation `ρ_H`. -/
noncomputable def higgsLink (h : ℝ) (y : Grid n → Field 𝔄 𝓗 𝓢) (x : Grid n) (μ : Fin 4) : 𝓗 :=
  NativeScaling.higgsLink h (fun U => ⇑(D.ρH U)) (gauge y) (higgs y) x μ

/-- The Higgs density `𝓛_{H,h} = -v(e) g^{μν} Re⟨K^h_μ, K^h_ν⟩ - v(e) V(H)`. -/
noncomputable def higgsDensity (h : ℝ) (y : Grid n → Field 𝔄 𝓗 𝓢) (x : Grid n) : ℝ :=
  -(volume (coframe y x) * ∑ μ, ∑ ν, ginv (coframe y x) μ ν *
      D.hermH (higgsLink D h y x μ) (higgsLink D h y x ν)) -
    volume (coframe y x) * potential D (higgs y x)

/-- The spin link `V_μ = e^{hσ(ω_{μ,h})} ρ_S(U_μ)`. -/
noncomputable def spinLink (h : ℝ) (y : Grid n → Field 𝔄 𝓗 𝓢) (x : Grid n) (μ : Fin 4) :
    Spin 𝓢 :=
  NativeScaling.spinLink h (D.σ : Mat →ₗ[ℝ] Spin 𝓢) (fun U => D.ρS U) (coframe y) (gauge y) x μ

/-- The inverse spin link `V_μ⁻¹ = ρ_S(e^{-hA_μ}) e^{-hσ(ω_{μ,h})}`. -/
noncomputable def spinLinkInv (h : ℝ) (y : Grid n → Field 𝔄 𝓗 𝓢) (x : Grid n) (μ : Fin 4) :
    Spin 𝓢 :=
  D.ρS (exp (-(h • gauge y μ x))) * exp (-(h • D.σ (omegaLink h (coframe y) x μ)))

theorem spinLink_mul_spinLinkInv (h : ℝ) (y : Grid n → Field 𝔄 𝓗 𝓢) (x : Grid n) (μ : Fin 4) :
    spinLink D h y x μ * spinLinkInv D h y x μ = 1 := by
  unfold spinLink spinLinkInv NativeScaling.spinLink
  simp only [ContinuousLinearMap.coe_coe]
  have h1 : D.ρS (exp (h • gauge y μ x)) * D.ρS (exp (-(h • gauge y μ x))) = 1 := by
    rw [← map_mul, exp_mul_exp_neg, map_one]
  calc _ = exp (h • D.σ (omegaLink h (coframe y) x μ)) *
        (D.ρS (exp (h • gauge y μ x)) * D.ρS (exp (-(h • gauge y μ x)))) *
        exp (-(h • D.σ (omegaLink h (coframe y) x μ))) := by
          simp only [mul_assoc]
    _ = 1 := by rw [h1, mul_one, exp_mul_exp_neg]

theorem spinLinkInv_mul_spinLink (h : ℝ) (y : Grid n → Field 𝔄 𝓗 𝓢) (x : Grid n) (μ : Fin 4) :
    spinLinkInv D h y x μ * spinLink D h y x μ = 1 := by
  unfold spinLink spinLinkInv NativeScaling.spinLink
  simp only [ContinuousLinearMap.coe_coe]
  have h1 : D.ρS (exp (-(h • gauge y μ x))) * D.ρS (exp (h • gauge y μ x)) = 1 := by
    rw [← map_mul, exp_neg_mul_exp, map_one]
  calc _ = D.ρS (exp (-(h • gauge y μ x))) *
        (exp (-(h • D.σ (omegaLink h (coframe y) x μ))) *
          exp (h • D.σ (omegaLink h (coframe y) x μ))) *
        D.ρS (exp (h • gauge y μ x)) := by
          simp only [mul_assoc]
    _ = 1 := by rw [exp_neg_mul_exp, mul_one, h1]

/-- The covariant Dirac difference `∇^h_μ Ψ = (V_μ Ψ(x+he_μ) - Ψ(x))/h`. -/
noncomputable def diracDiff (h : ℝ) (y : Grid n → Field 𝔄 𝓗 𝓢) (x : Grid n) (μ : Fin 4) : 𝓢 :=
  NativeScaling.diracDiff (fun (T : Spin 𝓢) v => T v) h (D.σ : Mat →ₗ[ℝ] Spin 𝓢)
    (fun U => D.ρS U) (coframe y) (gauge y) (psi y) x μ

/-- The transported co-spinor difference `∇^{h,∨}_μ Ψ̄ = (Ψ̄(x+he_μ) V_μ⁻¹ - Ψ̄(x))/h`. -/
noncomputable def diracDiffBar (h : ℝ) (y : Grid n → Field 𝔄 𝓗 𝓢) (x : Grid n) (μ : Fin 4) :
    CoSpinor 𝓢 :=
  h⁻¹ • ((psiBar y (x + unitVec n μ)).comp (spinLinkInv D h y x μ) - psiBar y x)

/-- The Dirac density
`𝓛_{D,h} = v(e) Re{ (i/2)[Ψ̄ γ^μ(e) ∇^h_μ Ψ - (∇^{h,∨}_μ Ψ̄) γ^μ(e) Ψ] - Ψ̄ 𝓜_𝐘(H) Ψ }`. -/
noncomputable def diracDensity (h : ℝ) (y : Grid n → Field 𝔄 𝓗 𝓢) (x : Grid n) : ℝ :=
  volume (coframe y x) *
    (Complex.I / 2 * ∑ μ, (psiBar y x (gammaMu D (coframe y x) μ (diracDiff D h y x μ)) -
        diracDiffBar D h y x μ (gammaMu D (coframe y x) μ (psi y x))) -
      psiBar y x (D.yukawa (higgs y x) (psi y x))).re

/-- The full local density `𝓛_h = 𝓛_{g,h} + 𝓛_{YM,h} + 𝓛_{H,h} + 𝓛_{D,h}` of
`eq:native-densities`. -/
noncomputable def nativeDensity (h : ℝ) (y : Grid n → Field 𝔄 𝓗 𝓢) (x : Grid n) : ℝ :=
  gravityDensity D h y x + ymDensity D h y x + higgsDensity D h y x + diracDensity D h y x

/-- The finite local common action `S_h^{loc} = h⁴ Σ_x 𝓛_h(x)` (`eq:native-local-action`) on the
periodic grid. -/
noncomputable def localAction (h : ℝ) (y : Grid n → Field 𝔄 𝓗 𝓢) : ℝ :=
  h ^ 4 * ∑ x, nativeDensity D h y x

/-! ### The normalised stencil densities of `lem:native-scaling` -/

/-- `e^{(ρν) u} e^{ρ w} = 1 + ρ (ν w(ρν, u) + w(ρ, w) + ρν w(ρν,u) w(ρ,w))`. -/
theorem exp_mul_exp_eq' {𝔖 : Type*} [NormedRing 𝔖] [NormedAlgebra ℝ 𝔖] [CompleteSpace 𝔖]
    [NormOneClass 𝔖] (ρ ν : ℝ) (u w : 𝔖) :
    exp ((ρ * ν) • u) * exp (ρ • w) =
      1 + ρ • (ν • linkExp (ρ * ν) u + linkExp ρ w +
        (ρ * ν) • (linkExp (ρ * ν) u * linkExp ρ w)) := by
  rw [exp_smul_eq_linkExp, exp_smul_eq_linkExp]
  simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_smul_comm, smul_add, smul_smul]
  module

/-- The normalised Higgs link `K̃_μ = ν w(ρν, dρ_H(A_μ)) H(ξ+ρe_μ) + δ⁺_ρ H`, with
`K^h_μ = K K̃_μ`. -/
noncomputable def nuHiggsLink (ρ ν : ℝ) (A : 𝔄) (Hp dH : 𝓗) : 𝓗 :=
  ν • (linkExp (ρ * ν) (D.ρHL A)) Hp + dH

/-- The normalised spin-link quotient `W` with `V_μ = e^{ρσ(ω̃)} e^{ρν dρ_S(A)} = 1 + ρ W`. -/
noncomputable def nuSpinQuot (ρ ν : ℝ) (om : Mat) (A : 𝔄) : Spin 𝓢 :=
  linkExp ρ (D.σ om) + ν • linkExp (ρ * ν) (D.ρSL A) +
    (ρ * ν) • (linkExp ρ (D.σ om) * linkExp (ρ * ν) (D.ρSL A))

/-- The normalised inverse spin-link quotient `W'` with `V_μ⁻¹ = 1 + ρ W'`. -/
noncomputable def nuSpinQuotInv (ρ ν : ℝ) (om : Mat) (A : 𝔄) : Spin 𝓢 :=
  ν • linkExp (ρ * ν) (-D.ρSL A) + linkExp ρ (-D.σ om) +
    (ρ * ν) • (linkExp (ρ * ν) (-D.ρSL A) * linkExp ρ (-D.σ om))

/-- The normalised Dirac difference `∇̃_μ Ψ = W Ψ(ξ+ρe_μ) + δ⁺_ρ Ψ`, with `∇^h_μ Ψ = K ∇̃_μ Ψ`. -/
noncomputable def nuDiracDiff (ρ ν : ℝ) (om : Mat) (A : 𝔄) (Ψp dΨ : 𝓢) : 𝓢 :=
  nuSpinQuot D ρ ν om A Ψp + dΨ

/-- The normalised transported co-spinor difference `∇̃^∨_μ Ψ̄ = Ψ̄(ξ+ρe_μ) W' + δ⁺_ρ Ψ̄`. -/
noncomputable def nuDiracDiffBar (ρ ν : ℝ) (om : Mat) (A : 𝔄) (Ψbp dΨb : CoSpinor 𝓢) :
    CoSpinor 𝓢 :=
  Ψbp.comp (nuSpinQuotInv D ρ ν om A) + dΨb

/-- The normalised coframe connection at the base node, `ω̃_μ = Ω_μ(e, δ⁺_ρ e)`, as a function of
the shifted first jet of the record. -/
noncomputable def jetOmega (ξ : Jet (Field 𝔄 𝓗 𝓢)) (μ : Fin 4) : Mat :=
  readerOmega (ξ.1 none).1 (fun lam => (ξ.2 (none, lam)).1) μ

/-- The normalised Cartan curvature `Φ(ρ; ω̃_μ, ω̃_ν, δ⁺_μ ω̃_ν, δ⁺_ν ω̃_μ)` as a function of
`(ρ, ν, jet of the record, jet of ω̃)`. -/
noncomputable def nuCartanCurv (μ ν : Fin 4) (p : ℝ × ℝ × (Jet (Field 𝔄 𝓗 𝓢) × Jet Conn)) : Op :=
  jointLogPlaquette (p.1, matToOp (p.2.2.2.1 none μ), matToOp (p.2.2.2.1 none ν),
    matToOp (p.2.2.2.2 (none, μ) ν), matToOp (p.2.2.2.2 (none, ν) μ))

/-- The ν-normalised field strength `F̃(ρ, ν; A_μ, A_ν, δ⁺_μ A_ν, δ⁺_ν A_μ)` as a function of
`(ρ, ν, jet of the record)`. -/
noncomputable def nuFieldStrength (μ ν : Fin 4) (p : ℝ × ℝ × Jet (Field 𝔄 𝓗 𝓢)) : 𝔄 :=
  jointNuLogPlaquette (p.1, p.2.1, (p.2.2.1 none).2.1 μ, (p.2.2.1 none).2.1 ν,
    (p.2.2.2 (none, μ)).2.1 ν, (p.2.2.2 (none, ν)).2.1 μ)

/-- The normalised Higgs link as a function of `(ρ, ν, jet of the record)`. -/
noncomputable def nuHiggsLinkJet (μ : Fin 4) (p : ℝ × ℝ × Jet (Field 𝔄 𝓗 𝓢)) : 𝓗 :=
  nuHiggsLink D p.1 p.2.1 ((p.2.2.1 none).2.1 μ) (p.2.2.1 (some (true, μ))).2.2.1
    (p.2.2.2 (none, μ)).2.2.1

/-- The normalised Dirac difference as a function of `(ρ, ν, jet of the record)`. -/
noncomputable def nuDiracDiffJet (μ : Fin 4) (p : ℝ × ℝ × Jet (Field 𝔄 𝓗 𝓢)) : 𝓢 :=
  nuDiracDiff D p.1 p.2.1 (jetOmega p.2.2 μ) ((p.2.2.1 none).2.1 μ)
    (p.2.2.1 (some (true, μ))).2.2.2.1 (p.2.2.2 (none, μ)).2.2.2.1

/-- The normalised transported co-spinor difference as a function of `(ρ, ν, jet of the record)`. -/
noncomputable def nuDiracDiffBarJet (μ : Fin 4) (p : ℝ × ℝ × Jet (Field 𝔄 𝓗 𝓢)) : CoSpinor 𝓢 :=
  nuDiracDiffBar D p.1 p.2.1 (jetOmega p.2.2 μ) ((p.2.2.1 none).2.1 μ)
    (p.2.2.1 (some (true, μ))).2.2.2.2 (p.2.2.2 (none, μ)).2.2.2.2

/-- The normalised Cartan sector: `v(e)/(2κ) e_a^μ e^{bν} Φ(ρ; ω̃_μ, ω̃_ν, δ⁺_μ ω̃_ν, δ⁺_ν ω̃_μ)^a_b
- ν² (Λ/κ) v(e)`, as a function of `(ρ, ν, jet of the record, jet of ω̃)`. -/
noncomputable def normCartan (p : ℝ × ℝ × (Jet (Field 𝔄 𝓗 𝓢) × Jet Conn)) : ℝ :=
  (∑ μ, ∑ ν, ∑ a, ∑ b, pal D.κ (p.2.2.1.1 none).1 μ ν a b *
      opEntry (antisym (fun μ ν => nuCartanCurv μ ν p) μ ν) a b) -
    p.2.1 ^ 2 * (D.Λ / D.κ) * volume (p.2.2.1.1 none).1

/-- The normalised Yang–Mills density `-¼ v(e) g^{μρ} g^{νσ} ⟨F̃_{μν}, F̃_{ρσ}⟩_𝐠` with the
ν-normalised field strength `F̃(ρ, ν; A_μ, A_ν, δ⁺_μ A_ν, δ⁺_ν A_μ)`. -/
noncomputable def normYM (p : ℝ × ℝ × Jet (Field 𝔄 𝓗 𝓢)) : ℝ :=
  -(4⁻¹ * volume (p.2.2.1 none).1 * ∑ μ, ∑ ν, ∑ ρ, ∑ σ,
    ginv (p.2.2.1 none).1 μ ρ * ginv (p.2.2.1 none).1 ν σ *
      D.ipA (antisym (fun μ ν => nuFieldStrength μ ν p) μ ν)
        (antisym (fun μ ν => nuFieldStrength μ ν p) ρ σ))

/-- The normalised Higgs density `-v(e) g^{μν} Re⟨K̃_μ, K̃_ν⟩ - ν² v(e) V(H)`. -/
noncomputable def normHiggs (p : ℝ × ℝ × Jet (Field 𝔄 𝓗 𝓢)) : ℝ :=
  -(volume (p.2.2.1 none).1 * ∑ μ, ∑ ν, ginv (p.2.2.1 none).1 μ ν *
      D.hermH (nuHiggsLinkJet D μ p) (nuHiggsLinkJet D ν p)) -
    p.2.1 ^ 2 * volume (p.2.2.1 none).1 * potential D (p.2.2.1 none).2.2.1

/-- The normalised bosonic stencil density `𝓛̃^B_{ρ,ν}` of `lem:native-scaling`. -/
noncomputable def normB (p : ℝ × ℝ × (Jet (Field 𝔄 𝓗 𝓢) × Jet Conn)) : ℝ :=
  normCartan D p + normYM D (p.1, p.2.1, p.2.2.1) + normHiggs D (p.1, p.2.1, p.2.2.1)

/-- The normalised Dirac stencil density `𝓛̃^D_{ρ,ν}` of `lem:native-scaling`:
`v(e) Re{(i/2)[Ψ̄ γ^μ(e) ∇̃_μ Ψ - (∇̃^∨_μ Ψ̄) γ^μ(e) Ψ] - ν Ψ̄ 𝓜_𝐘(H) Ψ}`. -/
noncomputable def normD (p : ℝ × ℝ × Jet (Field 𝔄 𝓗 𝓢)) : ℝ :=
  volume (p.2.2.1 none).1 *
    (Complex.I / 2 * ∑ μ, ((p.2.2.1 none).2.2.2.2 (gammaMu D (p.2.2.1 none).1 μ
          (nuDiracDiffJet D μ p)) -
        nuDiracDiffBarJet D μ p (gammaMu D (p.2.2.1 none).1 μ (p.2.2.1 none).2.2.2.1)) -
      (p.2.1 : ℂ) * (p.2.2.1 none).2.2.2.2 (D.yukawa (p.2.2.1 none).2.2.1 (p.2.2.1 none).2.2.2.1)).re

/-- The normalised coframe connection field `x ↦ (μ ↦ ω̃_{μ,ρ}(x))`. -/
noncomputable def omegaField (ρ : ℝ) (e : Grid n → Mat) (x : Grid n) : Conn :=
  fun μ => omegaLink ρ e x μ

/-! ### Block scaling identities -/

theorem shiftVec_none : shiftVec n none = 0 := rfl

theorem shiftVec_some_true (μ : Fin 4) : shiftVec n (some (true, μ)) = unitVec n μ := rfl

theorem stencil_fst {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (h : ℝ)
    (x : Grid n) (u : Grid n → V) (i : Shift) :
    (stencil h (shiftVec n) x u).1 i = u (x + shiftVec n i) := by
  rw [ShiftedJetAction.stencil_apply]

theorem stencil_snd {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (h : ℝ)
    (x : Grid n) (u : Grid n → V) (i : Shift) (μ : Fin 4) :
    (stencil h (shiftVec n) x u).2 (i, μ) = fwdDiff h μ u (x + shiftVec n i) := by
  rw [ShiftedJetAction.stencil_apply]

theorem fwdDiff_pi {ι V : Type*} [AddCommGroup V] [Module ℝ V] (h : ℝ) (μ : Fin 4)
    (f : Grid n → ι → V) (x : Grid n) (i : ι) :
    fwdDiff h μ f x i = fwdDiff h μ (fun z => f z i) x := by
  simp [ShiftedJetAction.fwdDiff]

theorem fwdDiff_coframe (h : ℝ) (μ : Fin 4) (y : Grid n → Field 𝔄 𝓗 𝓢) (x : Grid n) :
    (fwdDiff h μ y x).1 = fwdDiff h μ (coframe y) x := by
  simp [ShiftedJetAction.fwdDiff, coframe]

theorem fwdDiff_gauge (h : ℝ) (μ : Fin 4) (y : Grid n → Field 𝔄 𝓗 𝓢) (x : Grid n) (ν : Fin 4) :
    (fwdDiff h μ y x).2.1 ν = fwdDiff h μ (gauge y ν) x := by
  simp [ShiftedJetAction.fwdDiff, gauge]

theorem fwdDiff_higgs (h : ℝ) (μ : Fin 4) (y : Grid n → Field 𝔄 𝓗 𝓢) (x : Grid n) :
    (fwdDiff h μ y x).2.2.1 = fwdDiff h μ (higgs y) x := by
  simp [ShiftedJetAction.fwdDiff, higgs]

theorem fwdDiff_psi (h : ℝ) (μ : Fin 4) (y : Grid n → Field 𝔄 𝓗 𝓢) (x : Grid n) :
    (fwdDiff h μ y x).2.2.2.1 = fwdDiff h μ (psi y) x := by
  simp [ShiftedJetAction.fwdDiff, psi]

theorem fwdDiff_psiBar (h : ℝ) (μ : Fin 4) (y : Grid n → Field 𝔄 𝓗 𝓢) (x : Grid n) :
    (fwdDiff h μ y x).2.2.2.2 = fwdDiff h μ (psiBar y) x := by
  simp [ShiftedJetAction.fwdDiff, psiBar]

theorem fwdDiff_matToOp (h : ℝ) (μ : Fin 4) (f : Grid n → Mat) (x : Grid n) :
    fwdDiff h μ (fun z => matToOp (f z)) x = matToOp (fwdDiff h μ f x) := by
  simp [ShiftedJetAction.fwdDiff, map_sub, map_smul]

/-- The normalised connection at the base node is the reader of the jet of the record. -/
theorem jetOmega_stencil (ρ : ℝ) (y : Grid n → Field 𝔄 𝓗 𝓢) (x : Grid n) (μ : Fin 4) :
    jetOmega (stencil ρ (shiftVec n) x y) μ = omegaLink ρ (coframe y) x μ := by
  simp only [jetOmega, stencil_fst, stencil_snd, shiftVec_none, add_zero, fwdDiff_coframe,
    omegaLink, coframe]

/-- `lem:native-scaling`, Cartan sector: `R^h_{μν} = K² Φ(ρ; ω̃_μ, ω̃_ν, δ⁺_ρ ω̃_ν, δ⁺_ρ ω̃_μ)`
with `ω̃ = ω̃_ρ` the normalised connection. -/
theorem cartanCurvature_eq_scaled {h K : ℝ} (hh : h ≠ 0) (hK : K ≠ 0) (e : Grid n → Mat)
    (x : Grid n) (μ ν : Fin 4) :
    cartanCurvature h e x μ ν = K ^ 2 • jointLogPlaquette (h * K,
      matToOp (omegaLink (h * K) e x μ), matToOp (omegaLink (h * K) e x ν),
      matToOp (fwdDiff (h * K) μ (fun z => omegaLink (h * K) e z ν) x),
      matToOp (fwdDiff (h * K) ν (fun z => omegaLink (h * K) e z μ) x)) := by
  unfold cartanCurvature
  rw [NativeScaling.fieldStrength_scale hK]
  have hA : (K⁻¹ • fun μ x => matToOp (omegaLink h e x μ)) =
      fun μ x => matToOp (omegaLink (h * K) e x μ) := by
    funext μ x
    simp only [Pi.smul_apply]
    rw [NativeScaling.omegaLink_scale hK, map_smul, smul_smul, inv_mul_cancel₀ hK, one_smul]
  rw [hA, NativeScaling.fieldStrength_eq_logPlaquette (mul_ne_zero hh hK), jointLogPlaquette_eq,
    fwdDiff_matToOp, fwdDiff_matToOp]

/-- `lem:native-scaling`, Higgs sector: `K^h_μ = K K̃_μ(ρ, ν; A_μ, H(x+e_μ), δ⁺_ρ H)`. -/
theorem higgsLink_eq_scaled {h K : ℝ} (hh : h ≠ 0) (hK : K ≠ 0) (y : Grid n → Field 𝔄 𝓗 𝓢)
    (x : Grid n) (μ : Fin 4) :
    higgsLink D h y x μ = K • nuHiggsLink D (h * K) K⁻¹ (gauge y μ x) (higgs y (x + unitVec n μ))
      (fwdDiff (h * K) μ (higgs y) x) := by
  unfold higgsLink NativeScaling.higgsLink nuHiggsLink
  beta_reduce
  have h1 : D.ρH (exp (h • gauge y μ x)) =
      1 + h • linkExp (𝔄 := 𝓗 →L[ℝ] 𝓗) h (D.ρH (gauge y μ x)) := by
    rw [algHom_map_exp D.ρH D.ρH_cont, map_smul]
    exact exp_smul_eq_linkExp (𝔄 := 𝓗 →L[ℝ] 𝓗) h _
  rw [h1, mul_inv_cancel_right₀ hK, ContinuousLinearMap.add_apply, ContinuousLinearMap.one_apply,
    ContinuousLinearMap.smul_apply, Data.ρHL_apply, add_sub_right_comm]
  simp only [smul_add, smul_smul]
  rw [inv_mul_cancel₀ hh, mul_inv_cancel₀ hK, one_smul, add_comm]
  congr 1
  rw [← NativeScaling.fwdDiff_scale hK]
  rfl

/-- `lem:native-scaling`, spin link: `V_μ = e^{ρσ(ω̃_ρ)} e^{ρν dρ_S(A_μ)} = 1 + ρ W(ρ, ν; ω̃_μ, A_μ)`. -/
theorem spinLink_eq_scaled {h K : ℝ} (hK : K ≠ 0) (y : Grid n → Field 𝔄 𝓗 𝓢) (x : Grid n)
    (μ : Fin 4) :
    spinLink D h y x μ = 1 + (h * K) • nuSpinQuot D (h * K) K⁻¹
      (omegaLink (h * K) (coframe y) x μ) (gauge y μ x) := by
  unfold spinLink NativeScaling.spinLink nuSpinQuot
  simp only [ContinuousLinearMap.coe_coe]
  have h1 : exp (h • D.σ (omegaLink h (coframe y) x μ)) =
      1 + (h * K) • linkExp (𝔄 := Spin 𝓢) (h * K) (D.σ (omegaLink (h * K) (coframe y) x μ)) := by
    rw [NativeScaling.omegaLink_scale hK, map_smul, smul_smul]
    exact exp_smul_eq_linkExp (𝔄 := Spin 𝓢) _ _
  have h2 : D.ρS (exp (h • gauge y μ x)) =
      1 + (h * K * K⁻¹) • linkExp (𝔄 := Spin 𝓢) (h * K * K⁻¹) (D.ρS (gauge y μ x)) := by
    rw [mul_inv_cancel_right₀ hK, algHom_map_exp D.ρS D.ρS_cont, map_smul]
    exact exp_smul_eq_linkExp (𝔄 := Spin 𝓢) _ _
  rw [h1, h2]
  simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_smul_comm, smul_add, smul_smul,
    Data.ρSL_apply, mul_inv_cancel_right₀ hK]
  module

/-- `lem:native-scaling`, inverse spin link: `V_μ⁻¹ = 1 + ρ W'(ρ, ν; ω̃_μ, A_μ)`. -/
theorem spinLinkInv_eq_scaled {h K : ℝ} (hK : K ≠ 0) (y : Grid n → Field 𝔄 𝓗 𝓢) (x : Grid n)
    (μ : Fin 4) :
    spinLinkInv D h y x μ = 1 + (h * K) • nuSpinQuotInv D (h * K) K⁻¹
      (omegaLink (h * K) (coframe y) x μ) (gauge y μ x) := by
  unfold spinLinkInv nuSpinQuotInv
  have h1 : exp (-(h • D.σ (omegaLink h (coframe y) x μ))) =
      1 + (h * K) • linkExp (𝔄 := Spin 𝓢) (h * K) (-D.σ (omegaLink (h * K) (coframe y) x μ)) := by
    rw [NativeScaling.omegaLink_scale hK, map_smul, smul_smul, ← smul_neg]
    exact exp_smul_eq_linkExp (𝔄 := Spin 𝓢) _ _
  have h2 : D.ρS (exp (-(h • gauge y μ x))) =
      1 + (h * K * K⁻¹) • linkExp (𝔄 := Spin 𝓢) (h * K * K⁻¹) (-D.ρS (gauge y μ x)) := by
    rw [mul_inv_cancel_right₀ hK, algHom_map_exp D.ρS D.ρS_cont, map_neg, map_smul, ← smul_neg]
    exact exp_smul_eq_linkExp (𝔄 := Spin 𝓢) _ _
  rw [h1, h2]
  simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_smul_comm, smul_add, smul_smul,
    Data.ρSL_apply, mul_inv_cancel_right₀ hK]
  module

/-- `lem:native-scaling`, Dirac sector: `∇^h_μ Ψ = K ∇̃_μ Ψ`. -/
theorem diracDiff_eq_scaled {h K : ℝ} (hh : h ≠ 0) (hK : K ≠ 0) (y : Grid n → Field 𝔄 𝓗 𝓢)
    (x : Grid n) (μ : Fin 4) :
    diracDiff D h y x μ = K • nuDiracDiff D (h * K) K⁻¹ (omegaLink (h * K) (coframe y) x μ)
      (gauge y μ x) (psi y (x + unitVec n μ)) (fwdDiff (h * K) μ (psi y) x) := by
  unfold diracDiff NativeScaling.diracDiff nuDiracDiff
  change h⁻¹ • (spinLink D h y x μ (psi y (x + unitVec n μ)) - psi y x) = _
  rw [spinLink_eq_scaled D hK, ContinuousLinearMap.add_apply, ContinuousLinearMap.one_apply,
    ContinuousLinearMap.smul_apply, add_sub_right_comm]
  simp only [smul_add, smul_smul]
  rw [inv_mul_cancel_left₀ hh, add_comm]
  congr 1
  rw [← NativeScaling.fwdDiff_scale hK]
  rfl

/-- `lem:native-scaling`, Dirac sector: `∇^{h,∨}_μ Ψ̄ = K ∇̃^∨_μ Ψ̄`. -/
theorem diracDiffBar_eq_scaled {h K : ℝ} (hh : h ≠ 0) (hK : K ≠ 0) (y : Grid n → Field 𝔄 𝓗 𝓢)
    (x : Grid n) (μ : Fin 4) :
    diracDiffBar D h y x μ = K • nuDiracDiffBar D (h * K) K⁻¹ (omegaLink (h * K) (coframe y) x μ)
      (gauge y μ x) (psiBar y (x + unitVec n μ)) (fwdDiff (h * K) μ (psiBar y) x) := by
  unfold diracDiffBar nuDiracDiffBar
  rw [spinLinkInv_eq_scaled D hK, ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_smul,
    ContinuousLinearMap.one_def, ContinuousLinearMap.comp_id, add_sub_right_comm]
  simp only [smul_add, smul_smul]
  rw [inv_mul_cancel_left₀ hh, add_comm]
  congr 1
  rw [← NativeScaling.fwdDiff_scale hK]
  rfl


/-! ### `lem:native-scaling`: the exact density identity -/

/-- The Cartan sector carries the factor `K²`. -/
theorem gravityDensity_eq_scaled {h K : ℝ} (hh : h ≠ 0) (hK : K ≠ 0) (y : Grid n → Field 𝔄 𝓗 𝓢)
    (x : Grid n) :
    gravityDensity D h y x = K ^ 2 * normCartan D (h * K, K⁻¹, (stencil (h * K) (shiftVec n) x y,
      stencil (h * K) (shiftVec n) x (omegaField (h * K) (coframe y)))) := by
  unfold gravityDensity normCartan nuCartanCurv
  simp only [stencil_fst, stencil_snd, shiftVec_none, add_zero, fwdDiff_pi]
  obtain ⟨P, hP⟩ : ∃ P : Fin 4 → Fin 4 → Op, ∀ μ ν, P μ ν = jointLogPlaquette (h * K,
      matToOp (omegaField (h * K) (coframe y) x μ), matToOp (omegaField (h * K) (coframe y) x ν),
      matToOp (fwdDiff (h * K) μ (fun z => omegaField (h * K) (coframe y) z ν) x),
      matToOp (fwdDiff (h * K) ν (fun z => omegaField (h * K) (coframe y) z μ) x)) :=
    ⟨_, fun _ _ => rfl⟩
  simp only [← hP]
  have hc : cartanCurvature h (coframe y) x = fun μ ν => K ^ 2 • P μ ν := by
    funext μ ν
    rw [hP, cartanCurvature_eq_scaled hh hK (coframe y) x μ ν]
    simp only [omegaField]
  have ha : antisym (fun μ ν => K ^ 2 • P μ ν) = fun μ ν => K ^ 2 • antisym P μ ν := by
    funext μ ν
    exact antisym_smul (K ^ 2) P μ ν
  rw [hc, ha]
  simp only [opEntry_smul, coframe]
  rw [mul_sub]
  simp only [Finset.mul_sum]
  congr 1
  · refine sum_congr rfl fun μ _ => sum_congr rfl fun ν _ => sum_congr rfl fun a _ =>
      sum_congr rfl fun b _ => ?_
    generalize opEntry (antisym P μ ν) a b = t
    generalize pal D.κ (y x).1 μ ν a b = q
    ring
  · field_simp

/-- The Yang–Mills sector carries the factor `K²`. -/
theorem ymDensity_eq_scaled {h K : ℝ} (hh : h ≠ 0) (hK : K ≠ 0) (y : Grid n → Field 𝔄 𝓗 𝓢)
    (x : Grid n) :
    ymDensity D h y x = K ^ 2 * normYM D (h * K, K⁻¹, stencil (h * K) (shiftVec n) x y) := by
  unfold ymDensity normYM nuFieldStrength
  simp only [stencil_fst, stencil_snd, shiftVec_none, add_zero, fwdDiff_gauge]
  have hF : NativeScaling.fieldStrength h (gauge y) x = fun μ ν => K • jointNuLogPlaquette
      (h * K, K⁻¹, (y x).2.1 μ, (y x).2.1 ν, fwdDiff (h * K) μ (gauge y ν) x,
        fwdDiff (h * K) ν (gauge y μ) x) := by
    funext μ ν
    exact NativeScaling.fieldStrength_eq_nu_normalised hh hK (gauge y) x μ ν
  rw [hF]
  simp only [antisym_smul, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, coframe,
    mul_neg, Finset.mul_sum]
  congr 1
  refine sum_congr rfl fun μ _ => sum_congr rfl fun ν _ => sum_congr rfl fun ρ _ =>
    sum_congr rfl fun σ _ => ?_
  ring

/-- The Higgs sector carries the factor `K²`. -/
theorem higgsDensity_eq_scaled {h K : ℝ} (hh : h ≠ 0) (hK : K ≠ 0) (y : Grid n → Field 𝔄 𝓗 𝓢)
    (x : Grid n) :
    higgsDensity D h y x = K ^ 2 * normHiggs D (h * K, K⁻¹, stencil (h * K) (shiftVec n) x y) := by
  unfold higgsDensity normHiggs nuHiggsLinkJet
  simp only [stencil_fst, stencil_snd, shiftVec_none, shiftVec_some_true, add_zero, fwdDiff_higgs,
    higgsLink_eq_scaled D hh hK, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, coframe,
    gauge, higgs]
  rw [mul_sub, mul_neg]
  simp only [Finset.mul_sum]
  congr 1
  · congr 1
    refine sum_congr rfl fun μ _ => sum_congr rfl fun ν _ => ?_
    ring
  · field_simp

/-- Complex bookkeeping for the Dirac sector. -/
theorem dirac_scaling_aux {K : ℝ} (hK : K ≠ 0) (v : ℝ) (a b : Fin 4 → ℂ) (c : ℂ) :
    v * (Complex.I / 2 * ∑ μ, (K • a μ - K • b μ) - c).re =
      K * (v * (Complex.I / 2 * ∑ μ, (a μ - b μ) - ((K⁻¹ : ℝ) : ℂ) * c).re) := by
  have hK' : (K : ℂ) ≠ 0 := by exact_mod_cast hK
  have key : Complex.I / 2 * ∑ μ, (K • a μ - K • b μ) - c =
      (K : ℂ) * (Complex.I / 2 * ∑ μ, (a μ - b μ) - ((K⁻¹ : ℝ) : ℂ) * c) := by
    simp only [Complex.real_smul, ← mul_sub, ← Finset.mul_sum]
    push_cast
    field_simp
  rw [key, Complex.re_ofReal_mul]
  ring

/-- The Dirac sector carries the factor `K`. -/
theorem diracDensity_eq_scaled {h K : ℝ} (hh : h ≠ 0) (hK : K ≠ 0) (y : Grid n → Field 𝔄 𝓗 𝓢)
    (x : Grid n) :
    diracDensity D h y x = K * normD D (h * K, K⁻¹, stencil (h * K) (shiftVec n) x y) := by
  unfold diracDensity normD nuDiracDiffJet nuDiracDiffBarJet
  simp only [stencil_fst, stencil_snd, shiftVec_none, shiftVec_some_true, add_zero, fwdDiff_psi,
    fwdDiff_psiBar, jetOmega_stencil, diracDiff_eq_scaled D hh hK, diracDiffBar_eq_scaled D hh hK,
    map_smul, ContinuousLinearMap.smul_apply, coframe, gauge, higgs, psi, psiBar]
  exact dirac_scaling_aux hK _ _ _ _

/-- **`lem:native-scaling`** (`eq:native-density-scaling`): with `ρ = hK`, `ν = K⁻¹` and the nodal
amplitudes unchanged, the exact density `eq:native-densities` is
`𝓛_h(y)(x) = K² 𝓛̃^B(ρ, ν; Ξ_ρ ỹ(x)) + K 𝓛̃^D(ρ, ν; Ξ_ρ ỹ(x))`, where `Ξ_ρ ỹ(x)` is the shifted
first jet of the record together with that of the normalised coframe connection
`ω̃_ρ = Ω(e, δ⁺_ρ e)`. -/
theorem nativeDensity_eq_scaled {h K : ℝ} (hh : h ≠ 0) (hK : K ≠ 0) (y : Grid n → Field 𝔄 𝓗 𝓢)
    (x : Grid n) :
    nativeDensity D h y x =
      K ^ 2 * normB D (h * K, K⁻¹, (stencil (h * K) (shiftVec n) x y,
        stencil (h * K) (shiftVec n) x (omegaField (h * K) (coframe y)))) +
      K * normD D (h * K, K⁻¹, stencil (h * K) (shiftVec n) x y) := by
  unfold nativeDensity normB
  rw [gravityDensity_eq_scaled D hh hK, ymDensity_eq_scaled D hh hK, higgsDensity_eq_scaled D hh hK,
    diracDensity_eq_scaled D hh hK]
  ring

/-- The summed form: `S_h^{loc}[y] = K² h⁴ Σ_x 𝓛̃^B + K h⁴ Σ_x 𝓛̃^D`. -/
theorem localAction_eq_scaled {h K : ℝ} (hh : h ≠ 0) (hK : K ≠ 0) (y : Grid n → Field 𝔄 𝓗 𝓢) :
    localAction D h y =
      K ^ 2 * (h ^ 4 * ∑ x, normB D (h * K, K⁻¹, (stencil (h * K) (shiftVec n) x y,
        stencil (h * K) (shiftVec n) x (omegaField (h * K) (coframe y))))) +
      K * (h ^ 4 * ∑ x, normD D (h * K, K⁻¹, stencil (h * K) (shiftVec n) x y)) := by
  unfold localAction
  simp only [nativeDensity_eq_scaled D hh hK, sum_add_distrib, ← Finset.mul_sum]
  ring

/-- The normalised bosonic action `h⁴ Σ_x 𝓛̃^B(ρ, ν; Ξ_ρ ỹ(x))` as a function of the record. -/
noncomputable def normActionB (h K : ℝ) (y : Grid n → Field 𝔄 𝓗 𝓢) : ℝ :=
  h ^ 4 * ∑ x, normB D (h * K, K⁻¹, (stencil (h * K) (shiftVec n) x y,
    stencil (h * K) (shiftVec n) x (omegaField (h * K) (coframe y))))

/-- The normalised Dirac action `h⁴ Σ_x 𝓛̃^D(ρ, ν; Ξ_ρ ỹ(x))` as a function of the record. -/
noncomputable def normActionD (h K : ℝ) (y : Grid n → Field 𝔄 𝓗 𝓢) : ℝ :=
  h ^ 4 * ∑ x, normD D (h * K, K⁻¹, stencil (h * K) (shiftVec n) x y)

/-- `S_h^{loc} = K² 𝒜̃^B + K 𝒜̃^D` as functions of the record. -/
theorem localAction_eq_scaled_fun {h K : ℝ} (hh : h ≠ 0) (hK : K ≠ 0) :
    localAction D h = fun y : Grid n → Field 𝔄 𝓗 𝓢 =>
      K ^ 2 * normActionB D h K y + K * normActionD D h K y :=
  funext fun y => localAction_eq_scaled D hh hK y

/-- `lem:native-scaling`, Euler rows: since the varied nodal amplitudes are not rescaled,
differentiation of the finite sum leaves exactly the factors `K²` and `K`. -/
theorem fderiv_localAction_eq_scaled {h K : ℝ} (hh : h ≠ 0) (hK : K ≠ 0)
    {y : Grid n → Field 𝔄 𝓗 𝓢} (hB : DifferentiableAt ℝ (normActionB D h K) y)
    (hD : DifferentiableAt ℝ (normActionD D h K) y) :
    fderiv ℝ (localAction D h) y =
      K ^ 2 • fderiv ℝ (normActionB D h K) y + K • fderiv ℝ (normActionD D h K) y := by
  rw [localAction_eq_scaled_fun D hh hK]
  exact ((hB.hasFDerivAt.const_mul (K ^ 2)).add (hD.hasFDerivAt.const_mul K)).fderiv

end NativeDensity
end RenewalGeometry
