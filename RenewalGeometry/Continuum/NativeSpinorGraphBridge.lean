/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.CovariantGraphCompactness
import RenewalGeometry.Continuum.NativeSpinorVariation

/-!
# The native spinor graph bridge (`prop:native-spinor-variation`, both assertions)

Einstein–SM action-closure manuscript, `prop:native-spinor-variation`: under the positive
internal-link graph bound `eq:native-spinor-graph`, strong `L⁴` connection convergence, the Higgs
conclusions of `prop:native-Higgs-compactness`, strong `H¹` coframe convergence on one compact
nondegenerate chart and the scaled spin-link margin, after extraction the spinors converge weakly
in the reconstructed `H¹` class and the complete finite Dirac–Yukawa first variation converges to
its continuum counterpart.

Unit-torus rendering as in `NativeSpinorVariation` (grid `(ℤ/N)⁴`, `h = 1/N`, `R_h^0 = pc`), on
the literal records of `NativeDensity` (spinor fibre `𝓢` a finite-dimensional real normed space,
co-spinors `Ψ̄ ∈ CoSpinor 𝓢 = 𝓢 →L[ℝ] ℂ`, read with the identity frame `κ = id`).

**What the graph bound controls.**  The manuscript's graph `eq:native-spinor-graph` uses the
internal links only (`eq:native-internal-graph`: "for spinors the positive graph uses only the
compact internal representation; the coframe-derived Lorentz spin transport remains in the
physical Dirac term and is treated separately"):
`𝒟^U_μ Ψ = (ρ_S(U_μ) T_μ Ψ - Ψ)/h` (`spinGraph`) and
`𝒟^{U,∨}_μ Ψ̄ = (Ψ̄(x+e_μ) ρ_S(U_μ)⁻¹ - Ψ̄)/h` (`dualGraph`), `U_μ = e^{hA_μ}`.  The spin
coefficient `σ(ω_h)` (only `L²`-bounded for `H¹` coframes) never enters the graph identity
`D⁺Ψ = 𝒟^UΨ - B^ρ TΨ`: there `B^ρ = (ρ_S(U) - 1)/h` is the internal link coefficient, which
converges strongly in `L⁴` (`eq:native-link-coeff`), so Kato + Hölder give the ordinary discrete
`H¹` bound exactly as in `lem:native-critical-grid`.  The spin coefficient appears only in the
physical Dirac term, where `NativeSpinorVariation.native_spinor_variation` pairs it (strongly in
`L²`) with the spinor bilinears.

* `covGraph_spin`, `covGraph_dual`: the literal internal graphs are the covariant graphs of
  `CovariantGraph` for the representation `ρ_S` and its contragredient `dualRep`
  (`ψ̄ ↦ -ψ̄ ∘ ρ_S(A)`), using `ρ_S(e^{hA}) = e^{h ρ_S(A)}` and `e^{h dualRep(A)} ψ̄ = ψ̄ ∘ ρ_S(e^{-hA})`.
* `norm_comp_inv_link`: a unitary (fibre-norm preserving) internal spin link makes the
  contragredient link norm preserving on co-spinors (operator norm).
* `native_spinor_extraction` (**first assertion**): `eq:native-spinor-graph` + unitary internal
  links + strong `L⁴` connections + strong `L²` Higgs ⟹ after extraction the hypotheses `SpinHyp`
  of `native_spinor_variation` (strong `L²` values, uniform `L⁴` bounds), a bounded weak `L²` limit
  `u₀` of the first differences `(D⁺Ψ, D⁺Ψ̄)` in the dual-pairing form required there, and
  `u₀ = (∂Ψ, ∂Ψ̄)`: every frame component of `Ψ` and `Ψ̄` is in `H¹` with weak derivatives the
  frame components of `u₀`.
* `native_spinor_variation_of_graph` (**`prop:native-spinor-variation`**): the conclusion of
  `native_spinor_variation` along the extraction, from the paper's hypotheses.
-/

open MeasureTheory Set Finset Filter Topology Metric NormedSpace
open scoped BigOperators ENNReal NNReal

namespace RenewalGeometry.NativeSpinorGraph

noncomputable section

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 200000

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The unit torus `𝕋⁴`. -/
local notation "𝕋" => UnitAddTorus (Fin 4)

local notation "L²(" α ")" => Lp ℂ 2 (volume : Measure α)

open TorusPiecewiseConstantTranslation (pc stronglyMeasurable_pc gridNorm gridNorm_nonneg)
open ShiftedJetAction (Grid unitVec fwdDiff)
open NativeDensity NativeDirac NativeDiracConv NativeDiracLimit NativeDiracConvergence
open CovariantGraph

/-! ### The contragredient representation on co-spinors -/

section Dual

/-! The co-spinor fibre is `CoSpinor 𝓢 = 𝓢 →L[ℝ] ℂ`.  Typeclass search does not find the
topological-ring structure of `End(𝓢 →L[ℝ] ℂ)` directly, so the exponential identities are proved
for an arbitrary normed fibre `X` carrying a continuous ring homomorphism from the opposite spin
operator algebra (then instantiated at `X = CoSpinor 𝓢`). -/

variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢]

/-- **Continuous anti-homomorphisms commute with the exponential**: for a continuous ring
homomorphism `f : End(𝓢)ᵐᵒᵖ → End(X)`, `exp (f (op T)) = f (op (exp T))`. -/
theorem exp_ringHom_op [CompleteSpace 𝓢] {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] (f : (Spin 𝓢)ᵐᵒᵖ →+* (X →L[ℝ] X)) (hf : Continuous f) (T : Spin 𝓢) :
    exp (f (MulOpposite.op T)) = f (MulOpposite.op (exp T)) := by
  let +nondep : NormedAlgebra ℚ (Spin 𝓢)ᵐᵒᵖ := .restrictScalars ℚ ℝ _
  let +nondep : NormedAlgebra ℚ (X →L[ℝ] X) := .restrictScalars ℚ ℝ _
  have h := NormedSpace.map_exp f hf (MulOpposite.op T)
  rw [NormedSpace.exp_op] at h
  exact h.symm

/-- Precomposition `T ↦ (ψ̄ ↦ ψ̄ ∘ T)` on co-spinors. -/
def precomp : Spin 𝓢 →L[ℝ] (CoSpinor 𝓢 →L[ℝ] CoSpinor 𝓢) :=
  (ContinuousLinearMap.compL ℝ 𝓢 𝓢 ℂ).flip

theorem precomp_apply (T : Spin 𝓢) (ψ : CoSpinor 𝓢) : precomp T ψ = ψ.comp T := rfl

/-- Precomposition as a ring homomorphism on the opposite operator algebra. -/
def precompHom : (Spin 𝓢)ᵐᵒᵖ →+* (CoSpinor 𝓢 →L[ℝ] CoSpinor 𝓢) where
  toFun T := precomp T.unop
  map_one' := by ext ψ v; simp [precomp_apply]
  map_mul' S T := by ext ψ v; simp [precomp_apply]
  map_zero' := by ext ψ v; simp [precomp_apply]
  map_add' S T := by ext ψ v; simp [precomp_apply]

theorem precompHom_apply (T : (Spin 𝓢)ᵐᵒᵖ) : precompHom T = precomp T.unop := rfl

theorem continuous_precompHom : Continuous (precompHom (𝓢 := 𝓢)) :=
  (precomp (𝓢 := 𝓢)).continuous.comp MulOpposite.continuous_unop

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable [CompleteSpace 𝓢] [Nontrivial 𝓢]

/-- **The contragredient internal representation** on co-spinors, `A ↦ (ψ̄ ↦ -ψ̄ ∘ ρ_S(A))`. -/
def dualRep (D : Data 𝔄 𝓗 𝓢) : 𝔄 →L[ℝ] (CoSpinor 𝓢 →L[ℝ] CoSpinor 𝓢) :=
  (precomp (𝓢 := 𝓢)).comp (-D.ρSL)

theorem smul_dualRep (D : Data 𝔄 𝓗 𝓢) (h : ℝ) (A : 𝔄) :
    h • dualRep D A = precompHom (MulOpposite.op (-(h • D.ρS A))) := by
  ext ψ v
  simp [dualRep, precompHom_apply, precomp_apply, Data.ρSL_apply]

theorem ρS_exp_neg (D : Data 𝔄 𝓗 𝓢) (h : ℝ) (A : 𝔄) :
    D.ρS (exp (-(h • A))) = exp (-(h • D.ρS A)) := by
  rw [algHom_map_exp D.ρS D.ρS_cont]
  simp [map_neg, map_smul]

theorem exp_ρSL (D : Data 𝔄 𝓗 𝓢) (h : ℝ) (A : 𝔄) :
    exp (h • D.ρSL A) = D.ρS (exp (h • A)) := by
  rw [algHom_map_exp D.ρS D.ρS_cont, map_smul, Data.ρSL_apply]

/-- **Unitary internal links act isometrically on co-spinors**: if `ρ_S(e^{hA})` preserves the
spinor norm, then `ψ̄ ↦ ψ̄ ∘ ρ_S(e^{-hA})` preserves the operator norm of co-spinors. -/
theorem norm_comp_inv_link (D : Data 𝔄 𝓗 𝓢) (h : ℝ) (A : 𝔄)
    (hU : ∀ v, ‖D.ρS (exp (h • A)) v‖ = ‖v‖) (ψ : CoSpinor 𝓢) :
    ‖ψ.comp (D.ρS (exp (-(h • A))))‖ = ‖ψ‖ := by
  set S := D.ρS (exp (h • A))
  set T := D.ρS (exp (-(h • A)))
  have hST : S * T = 1 := by
    simp only [S, T]; rw [← map_mul, exp_mul_exp_neg, map_one]
  have hTS : T * S = 1 := by
    simp only [S, T]; rw [← map_mul, exp_neg_mul_exp, map_one]
  have hT : ∀ v, ‖T v‖ = ‖v‖ := by
    intro v
    rw [← hU (T v)]
    change ‖(S * T) v‖ = ‖v‖
    rw [hST]; rfl
  have hTn : ‖T‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
    rw [hT, one_mul]
  have hSn : ‖S‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
    rw [hU, one_mul]
  refine le_antisymm ?_ ?_
  · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_of_le_one_right (norm_nonneg _) hTn)
  · have e : ψ = (ψ.comp T).comp S := by
      rw [ContinuousLinearMap.comp_assoc]
      change ψ = ψ.comp (T * S)
      rw [hTS]; rfl
    calc ‖ψ‖ = ‖(ψ.comp T).comp S‖ := by rw [← e]
      _ ≤ ‖ψ.comp T‖ * ‖S‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖ψ.comp T‖ := mul_le_of_le_one_right (norm_nonneg _) hSn

end Dual

/-! ### The literal internal-link graphs of a native record -/

section Graphs

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
variable (D : Data 𝔄 𝓗 𝓢) {N : ℕ} [NeZero N]

/-- **The positive internal-link spinor graph** `𝒟^U_μ Ψ = (ρ_S(U_μ) T_μ Ψ - Ψ)/h`,
`U_μ = e^{hA_μ}` (`eq:native-internal-graph`, compact internal representation only). -/
def spinGraph (h : ℝ) (y : Grid N → Field 𝔄 𝓗 𝓢) (x : Grid N) (μ : Fin 4) : 𝓢 :=
  h⁻¹ • (D.ρS (exp (h • gauge y μ x)) (psi y (x + unitVec N μ)) - psi y x)

/-- **The positive internal-link dual-spinor graph**
`𝒟^{U,∨}_μ Ψ̄ = (Ψ̄(x+e_μ) ρ_S(U_μ)⁻¹ - Ψ̄)/h`, `ρ_S(U_μ)⁻¹ = ρ_S(e^{-hA_μ})`. -/
def dualGraph (h : ℝ) (y : Grid N → Field 𝔄 𝓗 𝓢) (x : Grid N) (μ : Fin 4) : CoSpinor 𝓢 :=
  h⁻¹ • ((psiBar y (x + unitVec N μ)).comp (D.ρS (exp (-(h • gauge y μ x)))) - psiBar y x)

/-- The connection array of a record. -/
def gaugeArr (y : Grid N → Field 𝔄 𝓗 𝓢) : Grid N → Fin 4 → 𝔄 := fun x μ => gauge y μ x

theorem covGraph_spin (y : Grid N → Field 𝔄 𝓗 𝓢) (x : Grid N) (μ : Fin 4) :
    covGraph N D.ρSL (gaugeArr y) (psi y) μ x = spinGraph D (N : ℝ)⁻¹ y x μ := by
  simp only [covGraph, spinGraph, gaugeArr, exp_ρSL, inv_inv]
  rfl

theorem covGraph_dual (y : Grid N → Field 𝔄 𝓗 𝓢) (x : Grid N) (μ : Fin 4) :
    covGraph N (dualRep D) (gaugeArr y) (psiBar y) μ x = dualGraph D (N : ℝ)⁻¹ y x μ := by
  rw [covGraph, dualGraph, inv_inv]
  simp only [gaugeArr]
  rw [smul_dualRep, exp_ringHom_op precompHom continuous_precompHom, precompHom_apply,
    MulOpposite.unop_op, precomp_apply, ← ρS_exp_neg]
  rfl

theorem DpV_eq_fwdDiff {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (μ : Fin 4)
    (u : Grid N → V) : NativeHiggs.DpV μ u = ShiftedJetAction.fwdDiff (N : ℝ)⁻¹ μ u := by
  funext x
  simp only [NativeHiggs.DpV, ShiftedJetAction.fwdDiff, inv_inv]
  rfl

end Graphs

/-! ### First differences of spinor/co-spinor pairs -/

section Difs

variable {𝓢 W' : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [NormedAddCommGroup W']
  [NormedSpace ℝ W']

/-- The spinor slot embedding `𝓢 → Dif`, direction `μ`. -/
def L1 (μ : Fin 4) : 𝓢 →L[ℝ] Dif 𝓢 W' :=
  (ContinuousLinearMap.inl ℝ (Fin 4 → 𝓢) (Fin 4 → W')).comp
    (ContinuousLinearMap.single ℝ (fun _ : Fin 4 => 𝓢) μ)

/-- The co-spinor slot embedding `W' → Dif`, direction `μ`. -/
def L2 (μ : Fin 4) : W' →L[ℝ] Dif 𝓢 W' :=
  (ContinuousLinearMap.inr ℝ (Fin 4 → 𝓢) (Fin 4 → W')).comp
    (ContinuousLinearMap.single ℝ (fun _ : Fin 4 => W') μ)

theorem dif_decomp (w : Dif 𝓢 W') : w = ∑ μ, L1 μ (w.1 μ) + ∑ μ, L2 μ (w.2 μ) := by
  ext ν <;> simp [L1, L2, Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Pi.single_apply]

/-- Integrals of a scalar `L²` function against a functional of a `Dif`-valued field split along the
slots. -/
theorem integral_mul_dif (ℓ : Dif 𝓢 W' →L[ℝ] ℝ) {φ : 𝕋 → ℝ} (hφ : MemLp φ 2 volume)
    {u : 𝕋 → Dif 𝓢 W'} (hu1 : ∀ μ, MemLp (fun z => (u z).1 μ) 2 volume)
    (hu2 : ∀ μ, MemLp (fun z => (u z).2 μ) 2 volume) :
    ∫ z, φ z * ℓ (u z) = ∑ μ, (∫ z, φ z * (ℓ.comp (L1 μ)) ((u z).1 μ)) +
      ∑ μ, ∫ z, φ z * (ℓ.comp (L2 μ)) ((u z).2 μ) := by
  have i1 : ∀ μ, Integrable (fun z => φ z * (ℓ.comp (L1 μ)) ((u z).1 μ)) volume := fun μ =>
    hφ.integrable_mul ((ℓ.comp (L1 μ)).comp_memLp' (hu1 μ))
  have i2 : ∀ μ, Integrable (fun z => φ z * (ℓ.comp (L2 μ)) ((u z).2 μ)) volume := fun μ =>
    hφ.integrable_mul ((ℓ.comp (L2 μ)).comp_memLp' (hu2 μ))
  have e : ∀ z, φ z * ℓ (u z) = ∑ μ, φ z * (ℓ.comp (L1 μ)) ((u z).1 μ) +
      ∑ μ, φ z * (ℓ.comp (L2 μ)) ((u z).2 μ) := by
    intro z
    conv_lhs => rw [dif_decomp (u z)]
    simp only [map_add, map_sum, ContinuousLinearMap.comp_apply, mul_add, Finset.mul_sum]
  simp_rw [e]
  rw [integral_add (integrable_finset_sum _ fun μ _ => i1 μ)
      (integrable_finset_sum _ fun μ _ => i2 μ), integral_finset_sum _ fun μ _ => i1 μ,
    integral_finset_sum _ fun μ _ => i2 μ]

end Difs

/-! ### Extraction from the graph bound -/

section Extraction

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
  [FiniteDimensional ℝ 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
  [FiniteDimensional ℝ 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
  [FiniteDimensional ℝ 𝓢]
variable {n : ℕ → ℕ} [∀ k, NeZero (n k)] {y : ∀ k, Grid (n k) → Field 𝔄 𝓗 𝓢}
variable {r r' : ℕ} [NeZero r] [NeZero r']

/-- The co-spinor frame `κ = id` (co-spinors read as themselves). -/
abbrev κid (𝓢 : Type*) [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] :
    CoSpinor 𝓢 →L[ℝ] CoSpinor 𝓢 := ContinuousLinearMap.id ℝ (CoSpinor 𝓢)

set_option maxHeartbeats 1600000 in
/-- **`prop:native-spinor-variation`, first assertion, on the literal records.**  Let
`R^0 A_h → A₀` strongly in `L⁴`, `R^0 H_h → H₀` strongly in `L²`, let the internal spin links
`ρ_S(e^{hA_μ})` preserve the spinor norm (unitary compact internal representation), and assume
the positive internal-link graph bound `eq:native-spinor-graph`:
`‖Ψ_h‖_{2,h}, ‖𝒟^U_μ Ψ_h‖_{2,h}, ‖Ψ̄_h‖_{2,h}, ‖𝒟^{U,∨}_μ Ψ̄_h‖_{2,h} ≤ B`.  Then after extraction:
the hypotheses `SpinHyp` of `native_spinor_variation` hold (co-spinor frame `κ = id`), the first
differences `R^0(D⁺Ψ_h, D⁺Ψ̄_h)` are bounded in `L²` and converge weakly (in the dual-pairing form
of `native_spinor_variation`) to `u₀ ∈ L²`, and `u₀ = (∂Ψ, ∂Ψ̄)`: in any linear frames `Θ, Θ'` of
the spinor and co-spinor fibres, every frame component of the limits is in `H¹` with weak
derivatives the frame components of `u₀`. -/
theorem native_spinor_extraction (D : Data 𝔄 𝓗 𝓢)
    (Θ : 𝓢 ≃L[ℝ] EuclideanSpace ℝ (Fin r)) (Θ' : CoSpinor 𝓢 ≃L[ℝ] EuclideanSpace ℝ (Fin r'))
    (hn : Tendsto n atTop atTop) {A₀ : Fin 4 → 𝕋 → 𝔄}
    (hA : ∀ μ, LpTendsto MeasureTheory.volume 4 (fun k => pc (gauge (y k) μ)) (A₀ μ))
    {H₀ : 𝕋 → 𝓗} (hH : LpTendsto MeasureTheory.volume 2 (fun k => pc (higgs (y k))) H₀)
    (hU : ∀ k x μ (v : 𝓢), ‖D.ρS (exp ((n k : ℝ)⁻¹ • gauge (y k) μ x)) v‖ = ‖v‖)
    {B : ℝ} (hΨ : ∀ k, gridNorm (psi (y k)) ≤ B)
    (hK : ∀ k μ, gridNorm (fun x => spinGraph D (n k : ℝ)⁻¹ (y k) x μ) ≤ B)
    (hΨb : ∀ k, gridNorm (psiBar (y k)) ≤ B)
    (hKb : ∀ k μ, gridNorm (fun x => dualGraph D (n k : ℝ)⁻¹ (y k) x μ) ≤ B) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ S : SpinHyp (κid 𝓢) (fun k => y (φ k)),
      ∃ u₀ : 𝕋 → Dif 𝓢 (CoSpinor 𝓢), S.H₀ = H₀ ∧ MemLp u₀ 2 MeasureTheory.volume ∧
      (∃ C, ∀ k, (eLpNorm (pc (difs (y (φ k)) (S.χ k))) 2 MeasureTheory.volume).toReal ≤ C) ∧
      (∀ g : 𝕋 → Dif 𝓢 (CoSpinor 𝓢) →L[ℝ] ℝ, MemLp g 2 MeasureTheory.volume →
        Tendsto (fun k => ∫ z, g z (pc (difs (y (φ k)) (S.χ k)) z)) atTop
          (𝓝 (∫ z, g z (u₀ z)))) ∧
      (∀ j, ∃ f : L²(𝕋), ((f : 𝕋 → ℂ) =ᵐ[MeasureTheory.volume] fun z => ((Θ (S.Ψ₀ z) j : ℝ) : ℂ)) ∧
        TorusSobolev.MemH 1 f ∧ ∀ μ, (TorusSobolev.weakDeriv μ f : 𝕋 → ℂ) =ᵐ[MeasureTheory.volume]
          fun z => ((Θ ((u₀ z).1 μ) j : ℝ) : ℂ)) ∧
      (∀ j, ∃ f : L²(𝕋), ((f : 𝕋 → ℂ) =ᵐ[MeasureTheory.volume] fun z => ((Θ' (S.χ₀ z) j : ℝ) : ℂ)) ∧
        TorusSobolev.MemH 1 f ∧ ∀ μ, (TorusSobolev.weakDeriv μ f : 𝕋 → ℂ) =ᵐ[MeasureTheory.volume]
          fun z => ((Θ' ((u₀ z).2 μ) j : ℝ) : ℂ)) := by
  classical
  -- the spinor graph
  have hA' : ∀ μ, LpTendsto MeasureTheory.volume 4
      (fun k => pc (fun x => gaugeArr (y k) x μ)) (A₀ μ) := hA
  have hUs : ∀ k x μ (v : 𝓢),
      ‖exp ((n k : ℝ)⁻¹ • D.ρSL (gaugeArr (y k) x μ)) v‖ = ‖v‖ := by
    intro k x μ v; rw [exp_ρSL]; exact hU k x μ v
  have hKs : ∀ k μ, gridNorm (covGraph (n k) D.ρSL (gaugeArr (y k)) (psi (y k)) μ) ≤ B := by
    intro k μ
    have e : covGraph (n k) D.ρSL (gaugeArr (y k)) (psi (y k)) μ =
        fun x => spinGraph D (n k : ℝ)⁻¹ (y k) x μ := funext fun x => covGraph_spin D (y k) x μ
    rw [e]; exact hK k μ
  obtain ⟨⟨C4, hC4, h4⟩, ⟨BD, hBD⟩, φ₁, hφ₁, Ψ₀, uΨ, hΨ2, -, huΨ, hwΨ, hidΨ⟩ :=
    covariant_graph_weak_compactness Θ hn D.ρSL hA' hUs hΨ hKs
  -- the dual graph, along the first extraction
  have hn₁ : Tendsto (fun k => n (φ₁ k)) atTop atTop := hn.comp hφ₁.tendsto_atTop
  have hKd : ∀ k μ, gridNorm (covGraph (n (φ₁ k)) (dualRep D) (gaugeArr (y (φ₁ k)))
      (psiBar (y (φ₁ k))) μ) ≤ B := by
    intro k μ
    have e : covGraph (n (φ₁ k)) (dualRep D) (gaugeArr (y (φ₁ k))) (psiBar (y (φ₁ k))) μ =
        fun x => dualGraph D (n (φ₁ k) : ℝ)⁻¹ (y (φ₁ k)) x μ :=
      funext fun x => covGraph_dual D (y (φ₁ k)) x μ
    rw [e]; exact hKb (φ₁ k) μ
  obtain ⟨⟨C4', hC4', h4'⟩, ⟨BD', hBD'⟩, φ₂, hφ₂, χ₀, uχ, hχ2, -, huχ, hwχ, hidχ⟩ :=
    covariant_graph_weak_compactness Θ' hn₁ (dualRep D) (A := fun k => gaugeArr (y (φ₁ k)))
      (fun μ => (hA' μ).comp_strictMono hφ₁) (fun k x μ v => by
        rw [smul_dualRep, exp_ringHom_op precompHom continuous_precompHom, precompHom_apply,
          MulOpposite.unop_op, precomp_apply, ← ρS_exp_neg]
        exact norm_comp_inv_link D _ _ (hU (φ₁ k) x μ) v) (fun k => hΨb (φ₁ k)) hKd
  have hφ : StrictMono (fun k => φ₁ (φ₂ k)) := hφ₁.comp hφ₂
  -- the spinor hypotheses along the extraction
  let S : SpinHyp (κid 𝓢) (fun k => y (φ₁ (φ₂ k))) :=
    { H₀ := H₀
      hH := hH.comp_strictMono hφ
      χ := fun k => psiBar (y (φ₁ (φ₂ k)))
      hχ := fun k => rfl
      Ψ₀ := Ψ₀
      hΨ := hΨ2.comp_strictMono hφ₂
      χ₀ := χ₀
      hχ₀ := hχ2
      B4 := max C4 C4'
      hB4 := (max_lt hC4.lt_top hC4'.lt_top).ne
      hΨ4 := fun k => (h4 _).trans (le_max_left _ _)
      hχ4 := fun k => (h4' _).trans (le_max_right _ _) }
  set u₀ : 𝕋 → Dif 𝓢 (CoSpinor 𝓢) := fun z => (fun μ => uΨ μ z, fun μ => uχ μ z) with hu₀def
  have hu₀ : MemLp u₀ 2 MeasureTheory.volume :=
    memLp_prod_iff.2 ⟨memLp_pi_iff.2 huΨ, memLp_pi_iff.2 huχ⟩
  -- the first differences of the records
  have hd1 : ∀ k z μ, (pc (difs (y (φ₁ (φ₂ k))) (S.χ k)) z).1 μ =
      pc (NativeHiggs.DpV μ (psi (y (φ₁ (φ₂ k))))) z := by
    intro k z μ; simp only [pc, difs, DpV_eq_fwdDiff]
  have hd2 : ∀ k z μ, (pc (difs (y (φ₁ (φ₂ k))) (S.χ k)) z).2 μ =
      pc (NativeHiggs.DpV μ (psiBar (y (φ₁ (φ₂ k))))) z := by
    intro k z μ; simp only [pc, difs, DpV_eq_fwdDiff]; rfl
  have hpt : ∀ k x, ‖difs (y (φ₁ (φ₂ k))) (S.χ k) x‖ ≤
      ∑ μ, ‖NativeHiggs.DpV μ (psi (y (φ₁ (φ₂ k)))) x‖ +
        ∑ μ, ‖NativeHiggs.DpV μ (psiBar (y (φ₁ (φ₂ k)))) x‖ := by
    intro k x
    have h1 : ‖(difs (y (φ₁ (φ₂ k))) (S.χ k) x).1‖ ≤
        ∑ μ, ‖NativeHiggs.DpV μ (psi (y (φ₁ (φ₂ k)))) x‖ := by
      refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun μ _ => norm_nonneg _)).2 fun μ => ?_
      refine le_of_eq_of_le ?_ (Finset.single_le_sum (f := fun μ =>
        ‖NativeHiggs.DpV μ (psi (y (φ₁ (φ₂ k)))) x‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ μ))
      simp only [difs, DpV_eq_fwdDiff]
    have h2 : ‖(difs (y (φ₁ (φ₂ k))) (S.χ k) x).2‖ ≤
        ∑ μ, ‖NativeHiggs.DpV μ (psiBar (y (φ₁ (φ₂ k)))) x‖ := by
      refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun μ _ => norm_nonneg _)).2 fun μ => ?_
      refine le_of_eq_of_le ?_ (Finset.single_le_sum (f := fun μ =>
        ‖NativeHiggs.DpV μ (psiBar (y (φ₁ (φ₂ k)))) x‖) (fun _ _ => norm_nonneg _)
          (Finset.mem_univ μ))
      simp only [difs, DpV_eq_fwdDiff]
      rfl
    rw [Prod.norm_def]
    exact max_le (h1.trans (le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => norm_nonneg _)))
      (h2.trans (le_add_of_nonneg_left (Finset.sum_nonneg fun _ _ => norm_nonneg _)))
  set C : ℝ := 4 * BD + 4 * BD'
  have hub : ∀ k, (eLpNorm (pc (difs (y (φ₁ (φ₂ k))) (S.χ k))) 2 MeasureTheory.volume).toReal ≤
      C := by
    intro k
    rw [NativeGridLp.eLpNorm_pc_two_eq, ENNReal.toReal_ofReal (gridNorm_nonneg _)]
    refine (TorusPiecewiseConstantTranslation.gridNorm_mono (v := fun x =>
      ∑ μ, ‖NativeHiggs.DpV μ (psi (y (φ₁ (φ₂ k)))) x‖ +
        ∑ μ, ‖NativeHiggs.DpV μ (psiBar (y (φ₁ (φ₂ k)))) x‖) fun x => ?_).trans ?_
    · refine (hpt k x).trans (le_of_eq ?_)
      rw [Real.norm_of_nonneg (add_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)
        (Finset.sum_nonneg fun _ _ => norm_nonneg _))]
    · have e : (fun x => ∑ μ, ‖NativeHiggs.DpV μ (psi (y (φ₁ (φ₂ k)))) x‖ +
          ∑ μ, ‖NativeHiggs.DpV μ (psiBar (y (φ₁ (φ₂ k)))) x‖) =
          (∑ μ, fun x => ‖NativeHiggs.DpV μ (psi (y (φ₁ (φ₂ k)))) x‖) +
            ∑ μ, fun x => ‖NativeHiggs.DpV μ (psiBar (y (φ₁ (φ₂ k)))) x‖ := by
        funext x; simp only [Pi.add_apply, Finset.sum_apply]
      rw [e]
      refine (TorusPiecewiseConstantTranslation.gridNorm_add_le _ _).trans (add_le_add ?_ ?_)
      · refine (TorusPiecewiseConstantTranslation.gridNorm_sum_le _ _).trans ?_
        calc ∑ μ, gridNorm (fun x => ‖NativeHiggs.DpV μ (psi (y (φ₁ (φ₂ k)))) x‖)
            ≤ ∑ _μ : Fin 4, BD := Finset.sum_le_sum fun μ _ =>
              (TorusPiecewiseConstantTranslation.gridNorm_mono fun x => (norm_norm _).le).trans
                (hBD _ μ)
          _ = 4 * BD := by simp
      · refine (TorusPiecewiseConstantTranslation.gridNorm_sum_le _ _).trans ?_
        calc ∑ μ, gridNorm (fun x => ‖NativeHiggs.DpV μ (psiBar (y (φ₁ (φ₂ k)))) x‖)
            ≤ ∑ _μ : Fin 4, BD' := Finset.sum_le_sum fun μ _ =>
              (TorusPiecewiseConstantTranslation.gridNorm_mono fun x => (norm_norm _).le).trans
                (hBD' _ μ)
          _ = 4 * BD' := by simp
  -- weak convergence of the first differences, in the dual-pairing form
  have hw : ∀ g : 𝕋 → Dif 𝓢 (CoSpinor 𝓢) →L[ℝ] ℝ, MemLp g 2 MeasureTheory.volume →
      Tendsto (fun k => ∫ z, g z (pc (difs (y (φ₁ (φ₂ k))) (S.χ k)) z)) atTop
        (𝓝 (∫ z, g z (u₀ z))) := by
    refine tendsto_integral_of_weak_functional (fun k => NativeYMIdentification.memLp_pc_gen _ 2)
      hu₀ fun ℓ φ' hφ' => ?_
    have h1 : ∀ μ, MemLp (fun z => (u₀ z).1 μ) 2 MeasureTheory.volume := huΨ
    have h2 : ∀ μ, MemLp (fun z => (u₀ z).2 μ) 2 MeasureTheory.volume := huχ
    rw [integral_mul_dif ℓ hφ' h1 h2]
    have e : ∀ k, ∫ z, φ' z * ℓ (pc (difs (y (φ₁ (φ₂ k))) (S.χ k)) z) =
        ∑ μ, (∫ z, φ' z * (ℓ.comp (L1 μ)) (pc (NativeHiggs.DpV μ (psi (y (φ₁ (φ₂ k))))) z)) +
        ∑ μ, ∫ z, φ' z * (ℓ.comp (L2 μ)) (pc (NativeHiggs.DpV μ (psiBar (y (φ₁ (φ₂ k))))) z) := by
      intro k
      rw [integral_mul_dif ℓ hφ'
        (fun μ => by simp only [hd1]; exact NativeYMIdentification.memLp_pc_gen _ 2)
        (fun μ => by simp only [hd2]; exact NativeYMIdentification.memLp_pc_gen _ 2)]
      simp only [hd1, hd2]
    simp_rw [e]
    refine Tendsto.add (tendsto_finset_sum _ fun μ _ => ?_) (tendsto_finset_sum _ fun μ _ => ?_)
    · exact (hwΨ μ (ℓ.comp (L1 μ)) φ' hφ').comp hφ₂.tendsto_atTop
    · exact hwχ μ (ℓ.comp (L2 μ)) φ' hφ'
  refine ⟨fun k => φ₁ (φ₂ k), hφ, S, u₀, rfl, hu₀, ⟨C, hub⟩, hw, fun j => ?_, fun j => ?_⟩
  · obtain ⟨f, hf1, hf2, hf3, -⟩ := hidΨ j
    exact ⟨f, hf1, hf2, hf3⟩
  · obtain ⟨f, hf1, hf2, hf3, -⟩ := hidχ j
    exact ⟨f, hf1, hf2, hf3⟩

/-- The coframe/connection hypotheses along a subsequence. -/
def coHypSubseq (H : CoHyp n y) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    CoHyp (fun k => n (φ k)) (fun k => y (φ k)) where
  hn := H.hn.comp hφ.tendsto_atTop
  Ke := H.Ke
  hKe := H.hKe
  hKdet := H.hKdet
  hval k x := H.hval (φ k) x
  c := H.c
  hmar k x μ := H.hmar (φ k) x μ
  e₀ := H.e₀
  he := H.he.comp_strictMono hφ
  p := H.p
  hp lam := (H.hp lam).comp_strictMono hφ
  A₀ := H.A₀
  hA μ := (H.hA μ).comp_strictMono hφ

/-- **`prop:native-spinor-variation`** (unit-torus rendering, literal records, co-spinors read
with `κ = id`).  Assume
* `CoHyp`: strong `H¹` (first-jet) coframe convergence on one compact nondegenerate chart, the
  scaled spin-link margin `eq:native-gravity-log-margin`, and strong `L⁴` connection convergence;
* the Higgs fields converge strongly in `L²` (a consequence of the conclusions of
  `prop:native-Higgs-compactness`);
* the internal spin links `ρ_S(e^{hA_μ})` are unitary (preserve the spinor norm);
* the positive internal-link graph bound `eq:native-spinor-graph`.
Then after extraction the spinors and co-spinors converge strongly in `L²` with weak `L²` limits
`u₀ = (∂Ψ, ∂Ψ̄)` of their first differences (frame components in `H¹`, weak derivatives = frame
components of `u₀`; first assertion, `native_spinor_extraction`), and the complete finite
Dirac–Yukawa first variation along the nodal test record — including the full metric variation
of the coframe-derived spin connection — converges to the continuum Dirac–Yukawa covector
uniformly on the `C²` unit ball: for every `ε > 0`, eventually
`|D S_{D,h}(y_h)[𝓘_h v] - 𝒟_D(y)[v]| ≤ ε ‖v‖_{C²}` for **all** tests `v` (hence convergence in
`(V^r_K)^*` for every `r ≥ 2`).  Strong convergence of the spinor first differences is not
used. -/
theorem native_spinor_variation_of_graph (D : Data 𝔄 𝓗 𝓢)
    (Θ : 𝓢 ≃L[ℝ] EuclideanSpace ℝ (Fin r)) (Θ' : CoSpinor 𝓢 ≃L[ℝ] EuclideanSpace ℝ (Fin r'))
    (H : CoHyp n y) {H₀ : 𝕋 → 𝓗} (hH : LpTendsto MeasureTheory.volume 2
      (fun k => pc (higgs (y k))) H₀)
    (hU : ∀ k x μ (v : 𝓢), ‖D.ρS (exp ((n k : ℝ)⁻¹ • gauge (y k) μ x)) v‖ = ‖v‖)
    {B : ℝ} (hΨ : ∀ k, gridNorm (psi (y k)) ≤ B)
    (hK : ∀ k μ, gridNorm (fun x => spinGraph D (n k : ℝ)⁻¹ (y k) x μ) ≤ B)
    (hΨb : ∀ k, gridNorm (psiBar (y k)) ≤ B)
    (hKb : ∀ k μ, gridNorm (fun x => dualGraph D (n k : ℝ)⁻¹ (y k) x μ) ≤ B) :
    ∃ φ : ℕ → ℕ, ∃ hφ : StrictMono φ, ∃ S : SpinHyp (κid 𝓢) (fun k => y (φ k)),
      ∃ u₀ : 𝕋 → Dif 𝓢 (CoSpinor 𝓢), S.H₀ = H₀ ∧
      (∀ j, ∃ f : L²(𝕋), ((f : 𝕋 → ℂ) =ᵐ[MeasureTheory.volume] fun z => ((Θ (S.Ψ₀ z) j : ℝ) : ℂ)) ∧
        TorusSobolev.MemH 1 f ∧ ∀ μ, (TorusSobolev.weakDeriv μ f : 𝕋 → ℂ) =ᵐ[MeasureTheory.volume]
          fun z => ((Θ ((u₀ z).1 μ) j : ℝ) : ℂ)) ∧
      (∀ j, ∃ f : L²(𝕋), ((f : 𝕋 → ℂ) =ᵐ[MeasureTheory.volume] fun z => ((Θ' (S.χ₀ z) j : ℝ) : ℂ)) ∧
        TorusSobolev.MemH 1 f ∧ ∀ μ, (TorusSobolev.weakDeriv μ f : 𝕋 → ℂ) =ᵐ[MeasureTheory.volume]
          fun z => ((Θ' ((u₀ z).2 μ) j : ℝ) : ℂ)) ∧
      ∀ ε > 0, ∀ᶠ k in atTop, ∀ τ : DTest 𝔄 𝓗 𝓢 (CoSpinor 𝓢),
        |dVar D (n (φ k) : ℝ)⁻¹ (y (φ k)) (testRec (κid 𝓢) (n (φ k)) (y (φ k)) τ) -
          NativeSpinorVariation.contDiracVar D (κid 𝓢) (coHypSubseq H hφ) S u₀ τ| ≤
            ε * τ.norm := by
  obtain ⟨φ, hφ, S, u₀, hS, hu₀, ⟨C, hub⟩, hw, hid1, hid2⟩ :=
    native_spinor_extraction D Θ Θ' H.hn H.hA hH hU hΨ hK hΨb hKb
  exact ⟨φ, hφ, S, u₀, hS, hid1, hid2,
    NativeSpinorVariation.native_spinor_variation D (κid 𝓢) (coHypSubseq H hφ) S hu₀ hub hw⟩

end Extraction

end

end RenewalGeometry.NativeSpinorGraph
