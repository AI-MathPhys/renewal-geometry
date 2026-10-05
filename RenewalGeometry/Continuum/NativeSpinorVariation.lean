/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.NativeDiracConvergence

/-!
# The complete Dirac–Yukawa first variation converges (`prop:native-spinor-variation`)

Second assertion of `prop:native-spinor-variation` (Einstein–SM action-closure manuscript), in the
unit-torus rendering (grid `(ℤ/N)⁴`, `h = 1/N`, raw reconstructions `R^0 = pc`; the paper's box of
side `L` is the dilation `x ↦ x/L`, which rescales every term by fixed powers of `L`).

**Theorem** (`native_spinor_variation`).  Let `y_k` be native records whose coframes lie in one
compact oriented chart, satisfy the scaled spin-link margin and converge with their first
differences strongly in `L²`, whose gauge connections converge strongly in `L⁴` (`CoHyp`), whose
Higgs fields converge strongly in `L²`, and whose spinors `Ψ_k` and co-spinor frame fields `χ_k`
(`Ψ̄_k = κ χ_k`) converge strongly in `L²` with uniform `L⁴` bounds (`SpinHyp`), while their first
differences `(δ⁺Ψ_k, δ⁺χ_k)` converge weakly and boundedly in `L²` to `u₀` — exactly the outputs
of the first assertion (`native_spinor_weak_compactness`, `native_spinor_pair_bilinear`), which
identify `u₀ = (∂Ψ, ∂χ)`.  Then the literal directional derivative of the finite Dirac–Yukawa
action `S_{D,h} = h⁴ Σ_x 𝓛_{D,h}` (`NativeDirac.dAct`, built from `NativeDensity.diracDensity`)
along the nodal test record `𝓘_h v` — **including the metric variation of the coframe-derived
spin connection** inside the spin links `exp(h σ(ω_{μ,h}))` — converges to the continuum
Dirac–Yukawa covector `contDiracVar`, **uniformly on the `C²` unit ball of tests**:
for every `ε > 0`, eventually `|D S_{D,h}(y_h)[𝓘_h v] - 𝒟_D(y)[v]| ≤ ε ‖v‖_{C²}` for all `v`.

The continuum covector is the same operator-field formula evaluated at the continuum slots
(`contSlots`: `h = 0`, `T_μΨ = Ψ`, `W_μ = B_μ = σ(Ω_μ(e, ∂e)) + ρ_S(A_μ)`, `W'_μ = -B_μ`,
`δW_μ = σ(δω_μ) + ρ_S(a_μ)` with `δω_μ` the variation of the Levi-Civita connection along the
lifted coframe test), with the derivative slots filled by the weak limits `u₀`:
`𝒟_D(y)[v] = ∫ (G(J_v) + Λ(J_v)(u₀))`.

Proof: exact nodal identity (`NativeDiracLimit.nodal_identity`), operator-field convergence
(`SpinHyp.lpTendsto_Gop` in `L¹`, `SpinHyp.lpTendsto_Λop` in `L²`), test-jet consistency
(`norm_pc_sampleJet_sub_le`), and the weak–strong pairing theorem
`WeakJetPairing.weak_jet_variation` (Arzelà–Ascoli net for uniformity on the test ball).
-/

open MeasureTheory Set Finset Filter Topology Metric NormedSpace
open scoped BigOperators ENNReal NNReal

namespace RenewalGeometry.NativeSpinorVariation

noncomputable section

set_option linter.unusedSectionVars false

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- The unit torus `𝕋⁴`. -/
local notation "𝕋" => UnitAddTorus (Fin 4)

open TorusPiecewiseConstantTranslation (pc stronglyMeasurable_pc)
open ShiftedJetAction (Grid unitVec fwdDiff)
open NativeScaling (Mat readerOmega omegaLink)
open NativeGravityFirstJet (M4 asM4 coframeM liftM liftL dqLift dqLiftL)
open NativeDensity NativeDirac NativeDiracConv NativeDiracLimit NativeDiracConvergence
open TorusC2Tests

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
  [FiniteDimensional ℝ 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
  [FiniteDimensional ℝ 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
  [FiniteDimensional ℝ 𝓢]
variable {W' : Type*} [NormedAddCommGroup W'] [NormedSpace ℝ W'] [FiniteDimensional ℝ W']

/-! ### The continuum test jet -/

section Jets

/-- **The continuum test jet** `J_v = (k, ∂k, a, η, ψ, ∂ψ, ψ̄, ∂ψ̄)`. -/
def contJet (τ : DTest 𝔄 𝓗 𝓢 W') (z : 𝕋) : Jet 𝔄 𝓗 𝓢 W' :=
  (τ.k.f z, fun lam => τ.k.df lam z, τ.a.f z, τ.η.f z, τ.ψ.f z, fun lam => τ.ψ.df lam z,
    τ.ψb.f z, fun lam => τ.ψb.df lam z)

theorem continuous_contJet (τ : DTest 𝔄 𝓗 𝓢 W') : Continuous (contJet τ) :=
  τ.k.f.continuous.prodMk ((continuous_pi fun lam => (τ.k.df lam).continuous).prodMk
    (τ.a.f.continuous.prodMk (τ.η.f.continuous.prodMk (τ.ψ.f.continuous.prodMk
      ((continuous_pi fun lam => (τ.ψ.df lam).continuous).prodMk (τ.ψb.f.continuous.prodMk
        (continuous_pi fun lam => (τ.ψb.df lam).continuous)))))))

section C2

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem norm_f_le' (k : C2Test F) (z : 𝕋) : ‖k.f z‖ ≤ k.norm :=
  (k.f.norm_coe_le_norm z).trans k.f_le

theorem norm_df_le' (k : C2Test F) (z : 𝕋) : ‖fun lam => k.df lam z‖ ≤ k.norm :=
  (pi_norm_le_iff_of_nonneg k.norm_nonneg).2 fun lam =>
    ((k.df lam).norm_coe_le_norm z).trans (k.df_le lam)

theorem coord_le_dist (z z' : 𝕋) (i : Fin 4) : ‖z i - z' i‖ ≤ dist z z' := by
  rw [← dist_eq_norm]; exact dist_le_pi_dist z z' i

theorem norm_f_sub_le' (k : C2Test F) (z z' : 𝕋) :
    ‖k.f z - k.f z'‖ ≤ k.norm * dist z z' := by
  have := k.norm_f_sub_le_of_coord (y := z') (y' := z) (δ := dist z z') (coord_le_dist z z')
  refine this.trans ?_
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right k.sum_df_le dist_nonneg

theorem norm_df_sub_le' (k : C2Test F) (z z' : 𝕋) :
    ‖(fun lam => k.df lam z) - fun lam => k.df lam z'‖ ≤ k.norm * dist z z' := by
  refine (pi_norm_le_iff_of_nonneg (by have := k.norm_nonneg; positivity)).2 fun lam => ?_
  have := k.norm_df_sub_le_of_coord lam (y := z') (y' := z) (δ := dist z z')
    (coord_le_dist z z')
  refine this.trans ?_
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right (k.sum_ddf_le lam) dist_nonneg

end C2

theorem _root_.RenewalGeometry.NativeDiracLimit.DTest.k_le (τ : DTest 𝔄 𝓗 𝓢 W') : τ.k.norm ≤ τ.norm := by
  unfold DTest.norm
  have := τ.a.norm_nonneg; have := τ.η.norm_nonneg; have := τ.ψ.norm_nonneg
  have := τ.ψb.norm_nonneg; linarith
theorem _root_.RenewalGeometry.NativeDiracLimit.DTest.a_le (τ : DTest 𝔄 𝓗 𝓢 W') : τ.a.norm ≤ τ.norm := by
  unfold DTest.norm
  have := τ.k.norm_nonneg; have := τ.η.norm_nonneg; have := τ.ψ.norm_nonneg
  have := τ.ψb.norm_nonneg; linarith
theorem _root_.RenewalGeometry.NativeDiracLimit.DTest.η_le (τ : DTest 𝔄 𝓗 𝓢 W') : τ.η.norm ≤ τ.norm := by
  unfold DTest.norm
  have := τ.k.norm_nonneg; have := τ.a.norm_nonneg; have := τ.ψ.norm_nonneg
  have := τ.ψb.norm_nonneg; linarith
theorem _root_.RenewalGeometry.NativeDiracLimit.DTest.ψ_le (τ : DTest 𝔄 𝓗 𝓢 W') : τ.ψ.norm ≤ τ.norm := by
  unfold DTest.norm
  have := τ.k.norm_nonneg; have := τ.a.norm_nonneg; have := τ.η.norm_nonneg
  have := τ.ψb.norm_nonneg; linarith
theorem _root_.RenewalGeometry.NativeDiracLimit.DTest.ψb_le (τ : DTest 𝔄 𝓗 𝓢 W') : τ.ψb.norm ≤ τ.norm := by
  unfold DTest.norm
  have := τ.k.norm_nonneg; have := τ.a.norm_nonneg; have := τ.η.norm_nonneg
  have := τ.ψ.norm_nonneg; linarith

theorem norm_contJet_le (τ : DTest 𝔄 𝓗 𝓢 W') (z : 𝕋) : ‖contJet τ z‖ ≤ τ.norm := by
  refine norm_prod_le_iff.2 ⟨(norm_f_le' _ z).trans τ.k_le, norm_prod_le_iff.2
    ⟨(norm_df_le' _ z).trans τ.k_le, norm_prod_le_iff.2 ⟨(norm_f_le' _ z).trans τ.a_le,
      norm_prod_le_iff.2 ⟨(norm_f_le' _ z).trans τ.η_le, norm_prod_le_iff.2
        ⟨(norm_f_le' _ z).trans τ.ψ_le, norm_prod_le_iff.2 ⟨(norm_df_le' _ z).trans τ.ψ_le,
          norm_prod_le_iff.2 ⟨(norm_f_le' _ z).trans τ.ψb_le,
            (norm_df_le' _ z).trans τ.ψb_le⟩⟩⟩⟩⟩⟩⟩

theorem norm_contJet_sub_le (τ : DTest 𝔄 𝓗 𝓢 W') (z z' : 𝕋) :
    ‖contJet τ z - contJet τ z'‖ ≤ τ.norm * dist z z' := by
  have hd := dist_nonneg (x := z) (y := z')
  have m : ∀ {a : ℝ}, a ≤ τ.norm → a * dist z z' ≤ τ.norm * dist z z' := fun h =>
    mul_le_mul_of_nonneg_right h hd
  refine norm_prod_le_iff.2 ⟨(norm_f_sub_le' _ z z').trans (m τ.k_le), norm_prod_le_iff.2
    ⟨(norm_df_sub_le' _ z z').trans (m τ.k_le), norm_prod_le_iff.2
      ⟨(norm_f_sub_le' _ z z').trans (m τ.a_le), norm_prod_le_iff.2
        ⟨(norm_f_sub_le' _ z z').trans (m τ.η_le), norm_prod_le_iff.2
          ⟨(norm_f_sub_le' _ z z').trans (m τ.ψ_le), norm_prod_le_iff.2
            ⟨(norm_df_sub_le' _ z z').trans (m τ.ψ_le), norm_prod_le_iff.2
              ⟨(norm_f_sub_le' _ z z').trans (m τ.ψb_le),
                (norm_df_sub_le' _ z z').trans (m τ.ψb_le)⟩⟩⟩⟩⟩⟩⟩

section Sampling

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {N : ℕ} [NeZero N]

theorem hcoord (z : 𝕋) (i : Fin 4) :
    ‖TorusCellEmbedding.samplePt (TorusPiecewiseConstantTranslation.index N z) i - z i‖ ≤
      2 * (N : ℝ)⁻¹ := by
  have := norm_samplePt_index_add_sub_le z (0 : Fin 4 → ZMod N) (Or.inl rfl) i
  rwa [add_zero] at this

theorem norm_samp_sub_le (k : C2Test F) (z : 𝕋) :
    ‖samp N k.f (TorusPiecewiseConstantTranslation.index N z) - k.f z‖ ≤
      3 * (N : ℝ)⁻¹ * k.norm := by
  have hN : (0 : ℝ) ≤ (N : ℝ)⁻¹ := by positivity
  have h := norm_f_samplePt_sub_le k z _ (hcoord (N := N) z)
  refine h.trans ?_
  have := k.norm_nonneg
  nlinarith

theorem norm_sampD_sub_le (k : C2Test F) (z : 𝕋) :
    ‖(fun lam => fwdDiff (N : ℝ)⁻¹ lam (samp N k.f) (TorusPiecewiseConstantTranslation.index N z))
      - fun lam => k.df lam z‖ ≤ 3 * (N : ℝ)⁻¹ * k.norm := by
  have hN : (0 : ℝ) ≤ (N : ℝ)⁻¹ := by positivity
  refine (pi_norm_le_iff_of_nonneg (by have := k.norm_nonneg; positivity)).2 fun lam => ?_
  have h := norm_fd_samplePt_sub_le k z (TorusPiecewiseConstantTranslation.index N z) lam
    (hcoord (N := N) z)
  have e : fwdDiff (N : ℝ)⁻¹ lam (samp N k.f) (TorusPiecewiseConstantTranslation.index N z) =
      (N : ℝ) • (k.f (TorusCellEmbedding.samplePt (TorusPiecewiseConstantTranslation.index N z +
        Pi.single lam 1)) - k.f (TorusCellEmbedding.samplePt
          (TorusPiecewiseConstantTranslation.index N z))) := by
    simp only [ShiftedJetAction.fwdDiff, samp, inv_inv, unitVec]
  simp only [Pi.sub_apply]
  rw [e]
  refine h.trans (le_of_eq ?_)
  ring

end Sampling

/-- **Test-jet consistency**: the raw reconstruction of the sampled test jet is uniformly within
`3/N ‖v‖_{C²}` of the continuum test jet. -/
theorem norm_pc_sampleJet_sub_le {N : ℕ} [NeZero N] (τ : DTest 𝔄 𝓗 𝓢 W') (z : 𝕋) :
    ‖pc (sampleJet N τ) z - contJet τ z‖ ≤ 3 * (N : ℝ)⁻¹ * τ.norm := by
  have hN : (0 : ℝ) ≤ 3 * (N : ℝ)⁻¹ := by positivity
  have m : ∀ {a : ℝ}, a ≤ τ.norm → 3 * (N : ℝ)⁻¹ * a ≤ 3 * (N : ℝ)⁻¹ * τ.norm := fun h =>
    mul_le_mul_of_nonneg_left h hN
  refine norm_prod_le_iff.2 ⟨(norm_samp_sub_le _ z).trans (m τ.k_le), norm_prod_le_iff.2
    ⟨(norm_sampD_sub_le _ z).trans (m τ.k_le), norm_prod_le_iff.2
      ⟨(norm_samp_sub_le _ z).trans (m τ.a_le), norm_prod_le_iff.2
        ⟨(norm_samp_sub_le _ z).trans (m τ.η_le), norm_prod_le_iff.2
          ⟨(norm_samp_sub_le _ z).trans (m τ.ψ_le), norm_prod_le_iff.2
            ⟨(norm_sampD_sub_le _ z).trans (m τ.ψ_le), norm_prod_le_iff.2
              ⟨(norm_samp_sub_le _ z).trans (m τ.ψb_le),
                (norm_sampD_sub_le _ z).trans (m τ.ψb_le)⟩⟩⟩⟩⟩⟩⟩

end Jets

/-! ### The first variation as an integral of the operator fields -/

section Integral

variable (D : NativeDensity.Data 𝔄 𝓗 𝓢) (κ : W' →L[ℝ] CoSpinor 𝓢)

/-- **The finite first variation as a pairing**: along the nodal test record, the literal
directional derivative of the finite Dirac–Yukawa action is the integral of the operator fields
`G`, `Λ` of the raw reconstructions, evaluated at the reconstructed sampled test jet and the
reconstructed first differences. -/
theorem dVar_eq_integral {N : ℕ} [NeZero N] (y : Grid N → Field 𝔄 𝓗 𝓢) (χ : Grid N → W')
    (hχ : psiBar y = fun x => κ (χ x)) (hdet : ∀ x, (coframe y x).det ≠ 0)
    (τ : DTest 𝔄 𝓗 𝓢 W') :
    dVar D (N : ℝ)⁻¹ y (testRec κ N y τ) =
      ∫ z, (Gop D κ (pc (fun x => gridSlots (W' := W') D y x) z) (pc (sampleJet N τ) z) +
        Λop κ (pc (fun x => gridSlots (W' := W') D y x) z) (pc (sampleJet N τ) z)
          (pc (difs y χ) z)) := by
  have hfun : (fun z => Gop D κ (pc (fun x => gridSlots (W' := W') D y x) z)
      (pc (sampleJet N τ) z) + Λop κ (pc (fun x => gridSlots (W' := W') D y x) z)
        (pc (sampleJet N τ) z) (pc (difs y χ) z)) =
      pc (fun x => Gfun D κ (gridSlots D y x) (sampleJet N τ x) +
        Λfun κ (gridSlots D y x) (sampleJet N τ x) (difs y χ x)) := rfl
  rw [hfun, NativeGravityFirstJet.integral_pc_real, dVar_eq D _ y _ hdet]
  simp only [form]
  rw [← mul_add, ← mul_add, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun x _ => nodal_identity D κ y χ hχ τ x (hdet x)

end Integral

/-! ### The continuum covector and the main theorem -/

section Main

variable {n : ℕ → ℕ} [∀ k, NeZero (n k)] {y : ∀ k, Grid (n k) → Field 𝔄 𝓗 𝓢}
variable (D : NativeDensity.Data 𝔄 𝓗 𝓢) (κ : W' →L[ℝ] CoSpinor 𝓢)

/-- **The continuum Dirac–Yukawa covector** `𝒟_D(y)[v] = ∫ (G(J_v) + Λ(J_v)(u₀))` at the
continuum slots (`h = 0`, `W = B`, `W' = -B`, `δW = σ(δω) + ρ_S(a)`, `T_μ = id`), with the
derivative slots filled by `u₀ = (∂Ψ, ∂χ)`. -/
def contDiracVar (H : CoHyp n y) (P : SpinHyp κ y) (u₀ : 𝕋 → Dif 𝓢 W')
    (τ : DTest 𝔄 𝓗 𝓢 W') : ℝ :=
  ∫ z, (Gop D κ (S0 D κ H P z) (contJet τ z) + Λop κ (S0 D κ H P z) (contJet τ z) (u₀ z))

/-- **`prop:native-spinor-variation`, second assertion** (unit-torus rendering).  Along records
satisfying the coframe/connection hypotheses `CoHyp`, the spinor/co-spinor/Higgs hypotheses
`SpinHyp` (strong `L²` convergence with uniform `L⁴` bounds) and weak bounded `L²` convergence
of the first differences `R^0(δ⁺Ψ_h, δ⁺χ_h) ⇀ u₀` (the outputs of the first assertion), the
complete finite Dirac–Yukawa first variation along the nodal test record — including the metric
variation of the coframe-derived spin connection — converges to the continuum Dirac–Yukawa
covector **uniformly on the `C²` unit ball**: for every `ε > 0`, eventually
`|D S_{D,h}(y_h)[𝓘_h v] - 𝒟_D(y)[v]| ≤ ε ‖v‖_{C²}` for every test `v`. -/
theorem native_spinor_variation (H : CoHyp n y) (P : SpinHyp κ y) {u₀ : 𝕋 → Dif 𝓢 W'}
    (hu₀ : MemLp u₀ 2 volume) {C : ℝ}
    (hub : ∀ k, (eLpNorm (pc (difs (y k) (P.χ k))) 2 volume).toReal ≤ C)
    (hw : ∀ g : 𝕋 → Dif 𝓢 W' →L[ℝ] ℝ, MemLp g 2 volume →
      Tendsto (fun k => ∫ z, g z (pc (difs (y k) (P.χ k)) z)) atTop (𝓝 (∫ z, g z (u₀ z)))) :
    ∀ ε > 0, ∀ᶠ k in atTop, ∀ τ : DTest 𝔄 𝓗 𝓢 W',
      |dVar D (n k : ℝ)⁻¹ (y k) (testRec κ (n k) (y k) τ) - contDiracVar D κ H P u₀ τ| ≤
        ε * τ.norm := by
  intro ε hε
  have hδ : Tendsto (fun k => 3 * ((n k : ℝ))⁻¹) atTop (𝓝 0) := by
    simpa using H.tendsto_h.const_mul 3
  have key := WeakJetPairing.weak_jet_variation (P.lpTendsto_Gop (D := D) H)
    (P.lpTendsto_Λop (D := D) H) (u := fun k => pc (difs (y k) (P.χ k)))
    (fun k => TorusPiecewiseConstantTranslation.memLp_pc _) hu₀ hub hw DTest.norm contJet
    continuous_contJet norm_contJet_le norm_contJet_sub_le
    (fun k τ => pc (sampleJet (n k) τ))
    (fun k τ => (stronglyMeasurable_pc _).aestronglyMeasurable) hδ
    (fun k => by positivity) (fun k τ z => norm_pc_sampleJet_sub_le τ z) ε hε
  filter_upwards [key] with k hk τ
  have hdet : ∀ x, (coframe (y k) x).det ≠ 0 := fun x => H.hKdet _ (H.hval k x)
  rw [dVar_eq_integral D κ (y k) (P.χ k) (P.hχ k) hdet τ]
  exact hk τ

end Main

/-! ### Non-vacuity -/

section NonVacuity

/-- A Dirac–Yukawa packet over `𝔄 = 𝓗 = 𝓢 = ℝ` with nonzero gamma matrices and Yukawa map. -/
def exData : NativeDensity.Data ℝ ℝ ℝ where
  κ := 1
  Λ := 0
  lamH := 1
  vH := 1
  ipA := ContinuousLinearMap.mul ℝ ℝ
  hermH := ContinuousLinearMap.mul ℝ ℝ
  ρH := Algebra.ofId ℝ (ℝ →L[ℝ] ℝ)
  ρH_cont := LinearMap.continuous_of_finiteDimensional (Algebra.ofId ℝ (ℝ →L[ℝ] ℝ)).toLinearMap
  ρS := Algebra.ofId ℝ (ℝ →L[ℝ] ℝ)
  ρS_cont := LinearMap.continuous_of_finiteDimensional (Algebra.ofId ℝ (ℝ →L[ℝ] ℝ)).toLinearMap
  σ := 0
  γ := fun _ => 1
  yukawa := ContinuousLinearMap.mul ℝ ℝ

/-- The co-spinor frame `r ↦ (s ↦ r s)`. -/
def exκ : ℝ →L[ℝ] CoSpinor ℝ := (ContinuousLinearMap.id ℝ ℝ).smulRight Complex.ofRealCLM

/-- Flat records with a constant nonzero spinor and co-spinor. -/
def exRec (N : ℕ) : Grid N → Field ℝ ℝ ℝ := fun _ => ((1 : Mat), 0, 0, (1 : ℝ), exκ 1)

theorem coframe_exRec (N : ℕ) :
    coframe (exRec N) = coframe (NativeGravityFirstJet.flatRecord (𝔄 := ℝ) (𝓗 := ℝ) (𝓢 := ℝ) N) :=
  rfl

/-- The coframe hypotheses hold for the flat records. -/
def exCoHyp : CoHyp (fun k => k + 1) (fun k => exRec (k + 1)) where
  hn := tendsto_add_atTop_nat 1
  Ke := {asM4 1}
  hKe := isCompact_singleton
  hKdet M hM := by
    rw [Set.mem_singleton_iff.1 hM]
    exact (by simp : Matrix.det (1 : Mat) ≠ 0)
  hval k x := rfl
  c := 0
  hmar k x μ := by
    simp only [ωM]
    rw [coframe_exRec, NativeGravityFirstJet.omegaLink_flat]
    have : asM4 (0 : Mat) = 0 := by funext i j; rfl
    rw [this, norm_zero, mul_zero]
  e₀ := fun _ => asM4 1
  he := (LpTendsto.const (u := fun _ : 𝕋 => asM4 1) (memLp_const _)).congr
    (fun k => Eventually.of_forall fun z => rfl) (Eventually.of_forall fun _ => rfl)
  p := fun _ _ => 0
  hp lam := (LpTendsto.const (u := fun _ : 𝕋 => (0 : M4)) (memLp_const _)).congr
    (fun k => Eventually.of_forall fun z => by
      funext i j
      simp only [qM, pc, ShiftedJetAction.fwdDiff, coframe, exRec]
      show (0 : ℝ) = (((k + 1 : ℕ) : ℝ)⁻¹)⁻¹ * ((1 : Mat) i j - (1 : Mat) i j)
      ring)
    (Eventually.of_forall fun _ => rfl)
  A₀ := fun _ _ => 0
  hA μ := (LpTendsto.const (u := fun _ : 𝕋 => (0 : ℝ)) (memLp_const _)).congr
    (fun k => Eventually.of_forall fun z => rfl) (Eventually.of_forall fun _ => rfl)

/-- The spinor hypotheses hold for the constant spinors. -/
def exSpinHyp : SpinHyp (W' := ℝ) exκ (fun k => exRec (k + 1)) where
  H₀ := fun _ => 0
  hH := (LpTendsto.const (u := fun _ : 𝕋 => (0 : ℝ)) (memLp_const _)).congr
    (fun k => Eventually.of_forall fun z => rfl) (Eventually.of_forall fun _ => rfl)
  χ k := fun _ => 1
  hχ k := rfl
  Ψ₀ := fun _ => 1
  hΨ := (LpTendsto.const (u := fun _ : 𝕋 => (1 : ℝ)) (memLp_const _)).congr
    (fun k => Eventually.of_forall fun z => rfl) (Eventually.of_forall fun _ => rfl)
  χ₀ := fun _ => 1
  hχ₀ := (LpTendsto.const (u := fun _ : 𝕋 => (1 : ℝ)) (memLp_const _)).congr
    (fun k => Eventually.of_forall fun z => rfl) (Eventually.of_forall fun _ => rfl)
  B4 := ‖(1 : ℝ)‖ₑ
  hB4 := enorm_ne_top
  hΨ4 k := eLpNorm_const_le (1 : ℝ)
  hχ4 k := eLpNorm_const_le (1 : ℝ)

theorem pc_difs_exRec (k : ℕ) :
    pc (difs (exRec (k + 1)) (exSpinHyp.χ k)) = fun _ => (0 : Dif ℝ ℝ) := by
  funext z
  simp [difs, pc, ShiftedJetAction.fwdDiff, psi, exRec, exSpinHyp]
  rfl

/-- **Non-vacuity of `native_spinor_variation`**: flat coframes, vanishing gauge and Higgs fields
and constant nonzero spinor and co-spinor fields (with nonzero gamma matrices and Yukawa map)
satisfy every hypothesis, with `u₀ = 0`. -/
example : ∀ ε > 0, ∀ᶠ k in atTop, ∀ τ : DTest ℝ ℝ ℝ ℝ,
    |dVar exData ((k + 1 : ℕ) : ℝ)⁻¹ (exRec (k + 1)) (testRec exκ (k + 1) (exRec (k + 1)) τ) -
      contDiracVar exData exκ exCoHyp exSpinHyp (fun _ => 0) τ| ≤ ε * τ.norm := by
  refine native_spinor_variation exData exκ exCoHyp exSpinHyp (memLp_const _) (C := 0)
    (fun k => ?_) (fun g hg => ?_)
  · rw [pc_difs_exRec]
    simp
  · simp only [pc_difs_exRec]
    exact tendsto_const_nhds

end NonVacuity

/-! ### Faithfulness: the continuum covector is the derivative of the continuum density -/

section Faithful

variable (D : NativeDensity.Data 𝔄 𝓗 𝓢) (κ : W' →L[ℝ] CoSpinor 𝓢)

/-- **The continuum Dirac–Yukawa density** at one point, in the frame-read form
`v(e) [Σ_μ Re(i/2 (Ψ̄ γ^μ ∇_μΨ - (∇_μΨ̄) γ^μ Ψ)) - Re(Ψ̄ 𝓜_𝐘(H) Ψ)]` with
`∇_μΨ = ∂_μΨ + B_μΨ`, `∇_μΨ̄ = ∂_μΨ̄ - Ψ̄ B_μ`, `B_μ = σ(Ω_μ(e, ∂e)) + ρ_S(A_μ)`, `Ψ̄ = κ χ`; the
arguments are the values of the coframe `e`, its derivatives `p`, the gauge connection `A`, the
Higgs field `H`, the spinor `Ψ` and its derivatives `dΨ`, the co-spinor frame field `χ` and its
derivatives `dχ`. -/
def contDens (e : M4) (p : Fin 4 → M4) (A : Fin 4 → 𝔄) (H : 𝓗) (Ψ : 𝓢) (dΨ : Fin 4 → 𝓢)
    (χ : W') (dχ : Fin 4 → W') : ℝ :=
  (∑ μ, (volM e * bI (κ χ) (gammaM D μ e (dΨ μ)) +
      volM e * bI (κ χ) ((gammaM D μ e * contB D e p A μ) Ψ) -
      volM e * bI (κ (dχ μ)) (gammaM D μ e Ψ) +
      volM e * bI (κ χ) ((contB D e p A μ * gammaM D μ e) Ψ))) -
    volM e * bR (κ χ) (D.yukawa H Ψ)

theorem hasDerivAt_lin {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (a b : V) :
    HasDerivAt (fun t : ℝ => a + t • b) b 0 := by
  simpa using ((hasDerivAt_id (0 : ℝ)).smul_const b).const_add a

/-- The variation of the continuum connection `B_μ` along the lifted coframe test, the gauge test
and the lifted first-derivative test is `δB_μ = σ(δω_μ) + ρ_S(a_μ)`. -/
theorem hasDerivAt_contB (e : M4) (p : Fin 4 → M4) (A : Fin 4 → 𝔄) (J : Jet 𝔄 𝓗 𝓢 W')
    (μ : Fin 4) (he : Matrix.det (show Mat from e) ≠ 0) :
    HasDerivAt (fun t : ℝ => contB D (e + t • εL e J)
      (p + t • fun lam => DεL e (fun _ => e) p lam J) (A + t • J.2.2.1) μ)
      (contdB D e p μ J) 0 := by
  have hω : HasDerivAt (fun t : ℝ => ∑ lam, ∑ i, ∑ j,
      (p lam i j + t * DεL e (fun _ => e) p lam J i j) •
        omegaCoef μ lam i j (e + t • εL e J))
      (δωL e (fun _ => e) p μ J) 0 := by
    rw [δωL_apply]
    refine HasDerivAt.fun_sum fun lam _ => HasDerivAt.fun_sum fun i _ =>
      HasDerivAt.fun_sum fun j _ => ?_
    have h1 : HasDerivAt (fun t : ℝ => p lam i j + t * DεL e (fun _ => e) p lam J i j)
        (DεL e (fun _ => e) p lam J i j) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (DεL e (fun _ => e) p lam J i j)).const_add
        (p lam i j)
    have h2 := hasDerivAt_omegaCoef_line μ lam i j he (εL e J)
    have := h1.smul h2
    simp only [zero_mul, add_zero, zero_smul] at this
    exact this.congr_deriv (add_comm _ _)
  have heq : (fun t : ℝ => asM4 (readerOmega (e + t • εL e J)
      (p + t • fun lam => DεL e (fun _ => e) p lam J) μ)) = fun t : ℝ => ∑ lam, ∑ i, ∑ j,
      (p lam i j + t * DεL e (fun _ => e) p lam J i j) • omegaCoef μ lam i j (e + t • εL e J) := by
    funext t
    exact readerOmega_expand _ _ μ
  have hσ : HasDerivAt (fun t : ℝ => σL D (asM4 (readerOmega (e + t • εL e J)
      (p + t • fun lam => DεL e (fun _ => e) p lam J) μ))) (σL D (δωL e (fun _ => e) p μ J)) 0 := by
    have hω' : HasDerivAt (fun t : ℝ => asM4 (readerOmega (e + t • εL e J)
        (p + t • fun lam => DεL e (fun _ => e) p lam J) μ)) (δωL e (fun _ => e) p μ J) 0 := by
      rw [heq]; exact hω
    exact (σL D).hasFDerivAt.comp_hasDerivAt 0 hω'
  have hA : HasDerivAt (fun t : ℝ => D.ρSL ((A + t • J.2.2.1) μ)) (D.ρSL (J.2.2.1 μ)) 0 := by
    have : (fun t : ℝ => D.ρSL ((A + t • J.2.2.1) μ)) = fun t : ℝ =>
        D.ρSL (A μ) + t • D.ρSL (J.2.2.1 μ) := by
      funext t; simp
    rw [this]
    exact hasDerivAt_lin _ _
  exact hσ.add hA

/-- **Faithfulness of the limit covector**: at every point where the coframe is invertible, the
value `G(J) + Λ(J)(dΨ, dχ)` of the operator fields at the continuum slots is the derivative of
the continuum Dirac–Yukawa density along the jet line
`(e + tε, ∂e + t∂ε, A + ta, H + tη, Ψ + tψ, ∂Ψ + t∂ψ, χ + tψ̄, ∂χ + t∂ψ̄)`, where `ε = lift(e, k)`
is the lifted inverse-metric test and `∂ε = lift(e, ∂k) + D lift(e)[∂e](k)`.  Hence
`contDiracVar` is the first variation of the continuum Dirac–Yukawa action. -/
theorem hasDerivAt_contDens (e : M4) (p : Fin 4 → M4) (A : Fin 4 → 𝔄) (H : 𝓗) (Ψ : 𝓢)
    (dΨ : Fin 4 → 𝓢) (χ : W') (dχ : Fin 4 → W') (J : Jet 𝔄 𝓗 𝓢 W')
    (he : Matrix.det (show Mat from e) ≠ 0) :
    HasDerivAt (fun t : ℝ => contDens D κ (e + t • εL e J)
      (p + t • fun lam => DεL e (fun _ => e) p lam J) (A + t • J.2.2.1) (H + t • J.2.2.2.1)
      (Ψ + t • J.2.2.2.2.1) (dΨ + t • J.2.2.2.2.2.1) (χ + t • J.2.2.2.2.2.2.1)
      (dχ + t • J.2.2.2.2.2.2.2))
      (Gfun D κ (contSlots D κ e p A H Ψ χ) J + Λfun κ (contSlots D κ e p A H Ψ χ) J (dΨ, dχ))
      0 := by
  set ε := εL (W' := W') e J
  have hvd : DifferentiableAt ℝ volM e :=
    (NativeGravityFirstJet.contDiffAt_volM he).differentiableAt (by simp)
  have hv : HasDerivAt (fun t : ℝ => volM (e + t • ε)) (fderiv ℝ volM e ε) 0 :=
    hasDerivAt_comp_line hvd ε
  have hγ : ∀ μ, HasDerivAt (fun t : ℝ => gammaM D μ (e + t • ε))
      (fderiv ℝ (gammaM D μ) e ε) 0 := fun μ =>
    hasDerivAt_comp_line ((contDiffAt_gammaM D μ he).differentiableAt (by simp)) ε
  have hB := fun μ => hasDerivAt_contB D e p A J μ he
  have hΨ := hasDerivAt_lin Ψ J.2.2.2.2.1
  have hχ : HasDerivAt (fun t : ℝ => κ (χ + t • J.2.2.2.2.2.2.1)) (κ J.2.2.2.2.2.2.1) 0 :=
    κ.hasFDerivAt.comp_hasDerivAt 0 (hasDerivAt_lin χ J.2.2.2.2.2.2.1)
  have hdΨ : ∀ μ, HasDerivAt (fun t : ℝ => (dΨ + t • J.2.2.2.2.2.1) μ) (J.2.2.2.2.2.1 μ) 0 :=
    fun μ => by simpa using hasDerivAt_lin (dΨ μ) (J.2.2.2.2.2.1 μ)
  have hdχ : ∀ μ, HasDerivAt (fun t : ℝ => κ ((dχ + t • J.2.2.2.2.2.2.2) μ))
      (κ (J.2.2.2.2.2.2.2 μ)) 0 := fun μ =>
    κ.hasFDerivAt.comp_hasDerivAt 0 (by simpa using hasDerivAt_lin (dχ μ) (J.2.2.2.2.2.2.2 μ))
  have hY : HasDerivAt (fun t : ℝ => D.yukawa (H + t • J.2.2.2.1)) (D.yukawa J.2.2.2.1) 0 :=
    D.yukawa.hasFDerivAt.comp_hasDerivAt 0 (hasDerivAt_lin H J.2.2.2.1)
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) fun μ (_ : μ ∈ Finset.univ) =>
    (((hv.mul (hasDerivAt_tri (bI (𝓢 := 𝓢)) hχ (hγ μ) (hdΨ μ))).add
      (hv.mul (hasDerivAt_tri (bI (𝓢 := 𝓢)) hχ ((hγ μ).mul (hB μ)) hΨ))).sub
      (hv.mul (hasDerivAt_tri (bI (𝓢 := 𝓢)) (hdχ μ) (hγ μ) hΨ))).add
      (hv.mul (hasDerivAt_tri (bI (𝓢 := 𝓢)) hχ ((hB μ).mul (hγ μ)) hΨ))
  have hyuk := hv.mul (hasDerivAt_tri (bR (𝓢 := 𝓢)) hχ hY hΨ)
  have := hsum.sub hyuk
  refine this.congr_deriv ?_
  simp only [zero_smul, add_zero, Pi.mul_apply, Gfun, Λfun]
  rw [sum2_aux]
  congr 1
  · refine Finset.sum_congr rfl fun μ _ => ?_
    simp only [Gμ, Λμ, contSlots, contdB, bI, zero_smul, zero_mul, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.neg_apply, ContinuousLinearMap.coe_comp', Function.comp_apply,
      spin_mul_apply', map_add, map_neg, map_smul, smul_eq_mul, Pi.add_apply, Pi.smul_apply,
      ContinuousLinearMap.mul_apply', neg_mul, mul_neg, ε]
    ring
  · simp only [G0, contSlots, bR, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_comp',
      Function.comp_apply, map_add, map_smul, smul_eq_mul, Pi.add_apply, Pi.smul_apply, ε]
    ring

end Faithful

section FaithfulIntegral

variable {n : ℕ → ℕ} [∀ k, NeZero (n k)] {y : ∀ k, Grid (n k) → Field 𝔄 𝓗 𝓢}
variable (D : NativeDensity.Data 𝔄 𝓗 𝓢) (κ : W' →L[ℝ] CoSpinor 𝓢)

/-- **The limit covector is the integrated first variation of the continuum Dirac–Yukawa
density**: `𝒟_D(y)[v] = ∫ d/dt|₀ 𝓛_D(fields + t · (lifted tests))`, the derivative taken pointwise
along the lifted test line (coframe `e + t lift(e, k)`, its derivatives
`∂e + t(lift(e, ∂k) + D lift(e)[∂e](k))`, `A + ta`, `H + tη`, `Ψ + tψ`, `∂Ψ + t∂ψ`, `χ + tψ̄`,
`∂χ + t∂ψ̄`), with `(∂Ψ, ∂χ) = u₀`. -/
theorem contDiracVar_eq_integral_deriv (H : CoHyp n y) (P : SpinHyp κ y) (u₀ : 𝕋 → Dif 𝓢 W')
    (τ : DTest 𝔄 𝓗 𝓢 W') :
    contDiracVar D κ H P u₀ τ = ∫ z, deriv (fun t : ℝ => contDens D κ
      (H.e₀ z + t • εL (H.e₀ z) (contJet τ z))
      ((fun lam => H.p lam z) + t • fun lam =>
        DεL (H.e₀ z) (fun _ => H.e₀ z) (fun lam => H.p lam z) lam (contJet τ z))
      ((fun μ => H.A₀ μ z) + t • (contJet τ z).2.2.1) (P.H₀ z + t • (contJet τ z).2.2.2.1)
      (P.Ψ₀ z + t • (contJet τ z).2.2.2.2.1) ((u₀ z).1 + t • (contJet τ z).2.2.2.2.2.1)
      (P.χ₀ z + t • (contJet τ z).2.2.2.2.2.2.1) ((u₀ z).2 + t • (contJet τ z).2.2.2.2.2.2.2)) 0 := by
  refine integral_congr_ae ?_
  filter_upwards [H.e₀_mem] with z hz
  rw [(hasDerivAt_contDens D κ (H.e₀ z) (fun lam => H.p lam z) (fun μ => H.A₀ μ z) (P.H₀ z)
    (P.Ψ₀ z) (u₀ z).1 (P.χ₀ z) (u₀ z).2 (contJet τ z) (H.hKdet _ hz)).deriv]
  rfl

end FaithfulIntegral

end

end RenewalGeometry.NativeSpinorVariation
