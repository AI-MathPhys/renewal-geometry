/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.EinsteinSMGravityFirstOrder
import RenewalGeometry.Continuum.EinsteinSMWeakMatterEquations

/-!
# The first-variation bound on bounded weak packets by the covariant test size
  (`lem:equivariant-tests`, `eq:equivariant-firstvariation-bound`; Einstein–Standard-Model
  action-closure manuscript)

Rendering: the slab box `Q = (t₀,t₁) × (0,1)³` with the flat comparison measure (the rendering of
`EinsteinSMFieldSpaces.lean`: trivialised bundles, flat comparison data, so the reference spin
connection is `Γ_ref = 0`); fibre norms are the sup norms of the `Pi` types (uniformly equivalent to
the Hermitian / Frobenius norms of `CriticalGaugeEstimates.equivTestSize`).  The complete minimally
coupled first variation at a weak packet `z = (e, ∂e, A, F, H, D_AH, Ψ, ∂Ψ, Ψ̄, ∂Ψ̄)` is the covector
formula on its jet (gravity in the first-order representative + Yang–Mills + Higgs + Dirac–Yukawa,
`completeLimitVariation`; for smooth fields it is the first variation, `actionVariation_eq_cov`).

* `πD`, `ιD`: the derivative slots `(∂a, ∂η_H, ∂η, ∂η̄)` of a test jet and their inclusion;
  `abs_integral_jet_le`: `|∫ Λ(j¹v)| ≤ ‖Λ‖_{L¹}‖j¹v - ι_Dπ_Dj¹v‖_{L^∞} + ‖Λ∘ι_D‖_{L²}‖π_Dj¹v‖_{L²}`.
* `covTestSizeSM` (`eq:equivariant-test-size`): `‖k‖_{W^{1,∞}} + ‖a‖_∞ + ‖η_H‖_∞ + ‖η‖_∞ + ‖η̄‖_∞ +
  Σ_μ (‖D_μa‖_2 + ‖D_μη_H‖_2 + ‖∇^{A}_μη‖_2 + ‖∇^{A}_μη̄‖_2)`;
  `eLpNorm_derPart_le`: `‖π_Dj¹v‖_{L²} ≤ (1 + c‖A‖_{L²}) 𝔫_z(v)` (covariant minus raw derivatives
  are zeroth order in the test, controlled by `‖A‖_{L²}` and the sup norms).
* `WeakPacket`: `e, e⁻¹ ∈ L^∞` (values in a compact subset of the coframe chart), `e ∈ H¹`,
  `A ∈ L⁴`, `F_A, D_AH ∈ L²`, `H, Ψ, Ψ̄ ∈ H¹`.
* `packet_cov_L1`, `packet_cov_der_L2`: the complete covector is in `L¹(Q)` and its restriction to
  the derivative slots is in `L²(Q)` (the Yang–Mills row pairs `F` with `∂a`, the Higgs row `D_AH`
  with `∂η_H`, the Dirac row the spinors with `∂η, ∂η̄`; gravity has no matter-derivative slot).
* **`equivariant_firstVariation_bound`** (`eq:equivariant-firstvariation-bound`): on every bounded
  weak packet there is `C_K < ∞` with `|D𝒮_θ(z)[v]| ≤ C_K 𝔫_z(v)` for all tests `v`.
-/

open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal

noncomputable section

set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000
set_option linter.unusedSectionVars false

namespace RenewalGeometry
namespace EinsteinSM

open SobolevOpen (pd box IsTest MemW12)

/-! ### Derivative slots of a test jet -/

section JetSplit

variable {C : Type} [Fintype C]

/-- The matter-derivative slots `(∂a, ∂η_H, ∂η, ∂η̄)` of a jet. -/
abbrev DerVal (C : Type) [Fintype C] : Type :=
  (Fin 4 → ConnFibre) × (Fin 4 → HiggsFibre) × (Fin 4 → SpinorFibre C) × (Fin 4 → SpinorFibre C)

/-- Projection onto the matter-derivative slots. -/
def πD : RJet C →L[ℝ] DerVal C := πF.prod (πK.prod (πdΨ.prod πdΨb))

/-- Inclusion of the matter-derivative slots (all other slots zero). -/
def ιD : DerVal C →L[ℝ] RJet C :=
  mkLinL (fun d => RJet.mk 0 0 0 d.1 0 d.2.1 0 d.2.2.1 0 d.2.2.2)
    (fun d d' => by simp only [RJet.mk, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk, add_zero])
    (fun c d => by simp only [RJet.mk, Prod.smul_fst, Prod.smul_snd, Prod.smul_mk, smul_zero])

@[simp] theorem ιD_e (d : DerVal C) : (ιD d).e = 0 := rfl
@[simp] theorem ιD_de (d : DerVal C) : (ιD d).de = 0 := rfl
@[simp] theorem ιD_A (d : DerVal C) : (ιD d).A = 0 := rfl
@[simp] theorem ιD_F (d : DerVal C) : (ιD d).F = d.1 := rfl
@[simp] theorem ιD_H (d : DerVal C) : (ιD d).H = 0 := rfl
@[simp] theorem ιD_K (d : DerVal C) : (ιD d).K = d.2.1 := rfl
@[simp] theorem ιD_Ψ (d : DerVal C) : (ιD d).Ψ = 0 := rfl
@[simp] theorem ιD_dΨ (d : DerVal C) : (ιD d).dΨ = d.2.2.1 := rfl
@[simp] theorem ιD_Ψb (d : DerVal C) : (ιD d).Ψb = 0 := rfl
@[simp] theorem ιD_dΨb (d : DerVal C) : (ιD d).dΨb = d.2.2.2 := rfl

/-- The value part `T - ι_Dπ_D T` of a jet (matter-derivative slots removed). -/
def valPart (T : RJet C) : RJet C := T - ιD (πD T)

theorem valPart_eq (T : RJet C) :
    valPart T = RJet.mk T.e T.de T.A 0 T.H 0 T.Ψ 0 T.Ψb 0 := by
  simp only [valPart, πD, ιD, mkLinL_apply, ContinuousLinearMap.prod_apply, RJet.mk]
  refine Prod.ext (sub_zero _) (Prod.ext (sub_zero _) (Prod.ext (sub_zero _) (Prod.ext ?_
    (Prod.ext (sub_zero _) (Prod.ext ?_ (Prod.ext (sub_zero _) (Prod.ext ?_
    (Prod.ext (sub_zero _) ?_))))))))
  · exact sub_self _
  · exact sub_self _
  · exact sub_self _
  · exact sub_self _

theorem norm_valPart_le (T : RJet C) :
    ‖valPart T‖ ≤ ‖T.e‖ + ‖T.de‖ + ‖T.A‖ + ‖T.H‖ + ‖T.Ψ‖ + ‖T.Ψb‖ := by
  rw [valPart_eq]
  have h1 := norm_nonneg T.e; have h2 := norm_nonneg T.de; have h3 := norm_nonneg T.A
  have h4 := norm_nonneg T.H; have h5 := norm_nonneg T.Ψ; have h6 := norm_nonneg T.Ψb
  simp only [RJet.mk, norm_prod_le_iff, norm_zero]
  refine ⟨by linarith, by linarith, by linarith, by positivity, by linarith, by positivity,
    by linarith, by positivity, by linarith, by positivity⟩

theorem norm_πD_le (T : RJet C) : ‖πD T‖ ≤ ‖T.F‖ + ‖T.K‖ + ‖T.dΨ‖ + ‖T.dΨb‖ := by
  have h1 := norm_nonneg T.F; have h2 := norm_nonneg T.K
  have h3 := norm_nonneg T.dΨ; have h4 := norm_nonneg T.dΨb
  simp only [πD, ContinuousLinearMap.prod_apply, norm_prod_le_iff]
  exact ⟨by rw [πF_apply]; linarith, by rw [πK_apply]; linarith, by rw [πdΨ_apply]; linarith,
    by rw [πdΨb_apply]; linarith⟩

theorem apply_split (Λ : RJet C →L[ℝ] ℝ) (T : RJet C) :
    Λ T = Λ (valPart T) + (Λ.comp ιD) (πD T) := by
  simp [valPart, map_sub]

end JetSplit

/-! ### The abstract bound -/

section AbstractBound

variable {C : Type} [Fintype C] {μ : Measure E4}

theorem holderTriple_two_two_one_jet : ENNReal.HolderTriple 2 2 1 :=
  ⟨by rw [ENNReal.inv_two_add_inv_two, inv_one]⟩

/-- **The jet-split Hölder bound**: for an operator field `Λ ∈ L¹` whose restriction to the
matter-derivative slots is in `L²`, and a measurable jet field `τ`,
`|∫ Λ(τ)| ≤ ‖Λ‖_{L¹}‖τ - ι_Dπ_Dτ‖_{L^∞} + ‖Λ∘ι_D‖_{L²}‖π_Dτ‖_{L²}`. -/
theorem abs_integral_jet_le {Λ : E4 → RJet C →L[ℝ] ℝ} (hΛ : AEStronglyMeasurable Λ μ)
    {τ : E4 → RJet C} (hτ : AEStronglyMeasurable τ μ) :
    ENNReal.ofReal |∫ x, Λ x (τ x) ∂μ| ≤
      eLpNorm Λ 1 μ * eLpNorm (fun x => valPart (τ x)) ⊤ μ +
        eLpNorm (fun x => (Λ x).comp ιD) 2 μ * eLpNorm (fun x => πD (τ x)) 2 μ := by
  have hv : AEStronglyMeasurable (fun x => valPart (τ x)) μ :=
    (continuous_id.sub (ιD.continuous.comp πD.continuous)).comp_aestronglyMeasurable hτ
  have hd : AEStronglyMeasurable (fun x => πD (τ x)) μ :=
    πD.continuous.comp_aestronglyMeasurable hτ
  have hΛD : AEStronglyMeasurable (fun x => (Λ x).comp ιD) μ :=
    ((ContinuousLinearMap.compL ℝ (DerVal C) (RJet C) ℝ).flip ιD).continuous.comp_aestronglyMeasurable
      hΛ
  have g1m : AEStronglyMeasurable (fun x => ‖Λ x‖ * ‖valPart (τ x)‖) μ := hΛ.norm.mul hv.norm
  have g2m : AEStronglyMeasurable (fun x => ‖(Λ x).comp ιD‖ * ‖πD (τ x)‖) μ :=
    hΛD.norm.mul hd.norm
  have hpt : ∀ x, ‖Λ x (τ x)‖ ≤ ‖Λ x‖ * ‖valPart (τ x)‖ + ‖(Λ x).comp ιD‖ * ‖πD (τ x)‖ := by
    intro x
    rw [apply_split (Λ x) (τ x)]
    exact (norm_add_le _ _).trans (add_le_add ((Λ x).le_opNorm _) (((Λ x).comp ιD).le_opNorm _))
  calc ENNReal.ofReal |∫ x, Λ x (τ x) ∂μ| = ‖∫ x, Λ x (τ x) ∂μ‖ₑ := by
        rw [Real.enorm_eq_ofReal_abs]
    _ ≤ ∫⁻ x, ‖Λ x (τ x)‖ₑ ∂μ := enorm_integral_le_lintegral_enorm _
    _ = eLpNorm (fun x => Λ x (τ x)) 1 μ := eLpNorm_one_eq_lintegral_enorm.symm
    _ ≤ eLpNorm (fun x => ‖Λ x‖ * ‖valPart (τ x)‖ + ‖(Λ x).comp ιD‖ * ‖πD (τ x)‖) 1 μ :=
        eLpNorm_mono_real fun x => hpt x
    _ ≤ eLpNorm (fun x => ‖Λ x‖ * ‖valPart (τ x)‖) 1 μ +
          eLpNorm (fun x => ‖(Λ x).comp ιD‖ * ‖πD (τ x)‖) 1 μ :=
        eLpNorm_add_le g1m g2m le_rfl
    _ ≤ _ := by
        gcongr
        · have := eLpNorm_smul_le_mul_eLpNorm (p := 1) (q := ⊤) (r := 1) hv.norm hΛ.norm
          simp only [eLpNorm_norm] at this
          exact (le_of_eq rfl).trans this
        · have h221 := holderTriple_two_two_one_jet
          have := eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := 2) (r := 1) hd.norm hΛD.norm
          simp only [eLpNorm_norm] at this
          exact (le_of_eq rfl).trans this

end AbstractBound

/-! ### The covariant test size in the field-tuple rendering -/

section TestSize

/-- `(A, a) ↦ ([A_μ, a_ν])_ν`. -/
def adActL (μ : Fin 4) : ConnFibre →L[ℝ] ConnFibre →L[ℝ] ConnFibre :=
  mkBilinL (fun A a ν => comm (A μ) (a ν))
    (fun A A' a => by funext ν; simp only [Pi.add_apply, comm, mmul_add_left', mmul_add_right']; abel)
    (fun c A a => by
      funext ν; simp only [Pi.smul_apply, comm, mmul_smul_left', mmul_smul_right', smul_sub])
    (fun A a a' => by funext ν; simp only [Pi.add_apply, comm, mmul_add_left', mmul_add_right']; abel)
    (fun c A a => by
      funext ν; simp only [Pi.smul_apply, comm, mmul_smul_left', mmul_smul_right', smul_sub])

theorem adActL_apply (μ : Fin 4) (A a : ConnFibre) : adActL μ A a = fun ν => comm (A μ) (a ν) :=
  rfl

variable {Ysec : Type} (FC : FermionCarrier Ysec)

/-- `(A, η) ↦ ρ_F(A_μ)η`. -/
def spinActL (μ : Fin 4) : ConnFibre →L[ℝ] SpinorFibre FC.C →L[ℝ] SpinorFibre FC.C :=
  mkBilinL (fun A η s c => ∑ c', FC.rho (A μ) c c' * η s c')
    (fun A A' η => by
      funext s c; simp only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib])
    (fun r A η => by
      funext s c
      simp only [Pi.smul_apply, map_smul, Complex.real_smul, mul_assoc, Finset.mul_sum])
    (fun A η η' => by
      funext s c; simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib])
    (fun r A η => by
      funext s c
      simp only [Pi.smul_apply, Complex.real_smul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring)

/-- `(A, η̄) ↦ η̄ρ_F(A_μ)`. -/
def cospinActL (μ : Fin 4) : ConnFibre →L[ℝ] SpinorFibre FC.C →L[ℝ] SpinorFibre FC.C :=
  mkBilinL (fun A η s c => ∑ c', η s c' * FC.rho (A μ) c' c)
    (fun A A' η => by
      funext s c; simp only [Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib])
    (fun r A η => by
      funext s c
      simp only [Pi.smul_apply, map_smul, Complex.real_smul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring)
    (fun A η η' => by
      funext s c; simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib])
    (fun r A η => by
      funext s c
      simp only [Pi.smul_apply, Complex.real_smul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring)

/-- Covariant derivative of an `ad P`-valued one-form test: `(D_μa)_ν = ∂_μa_ν + [A_μ, a_ν]`. -/
def adCov (A a : E4 → ConnFibre) (μ : Fin 4) (x : E4) : ConnFibre :=
  pd a μ x + adActL μ (A x) (a x)

/-- Covariant derivative of a spinor test: `∇^A_μη = ∂_μη + ρ_F(A_μ)η` (flat reference spin
connection of the trivialised comparison geometry). -/
def spinCovA (A : E4 → ConnFibre) (η : E4 → SpinorFibre FC.C) (μ : Fin 4) (x : E4) :
    SpinorFibre FC.C :=
  pd η μ x + spinActL FC μ (A x) (η x)

/-- Covariant derivative of a dual spinor test: `∇^A_μη̄ = ∂_μη̄ - η̄ρ_F(A_μ)`. -/
def cospinCovA (A : E4 → ConnFibre) (η : E4 → SpinorFibre FC.C) (μ : Fin 4) (x : E4) :
    SpinorFibre FC.C :=
  pd η μ x - cospinActL FC μ (A x) (η x)

variable {T : ℝ}

/-- The sup part of the test size: `‖k‖_∞ + ‖∂k‖_∞ + ‖a‖_∞ + ‖η_H‖_∞ + ‖η‖_∞ + ‖η̄‖_∞` on `Q`. -/
def supPartSM (Q : ChartBox T) (v : FieldTuple FC.C) : ℝ≥0∞ :=
  eLpNorm v.e ⊤ Q.μ + eLpNorm (fun x => fun i => pd v.e i x) ⊤ Q.μ + eLpNorm v.A ⊤ Q.μ +
    eLpNorm v.H ⊤ Q.μ + eLpNorm v.Ψ ⊤ Q.μ + eLpNorm v.Ψb ⊤ Q.μ

/-- The covariant-derivative part of the test size:
`Σ_μ (‖D_μa‖_2 + ‖D_μη_H‖_2 + ‖∇^A_μη‖_2 + ‖∇^A_μη̄‖_2)` on `Q`. -/
def derPartSM (Q : ChartBox T) (A : E4 → ConnFibre) (v : FieldTuple FC.C) : ℝ≥0∞ :=
  ∑ μ, (eLpNorm (adCov A v.A μ) 2 Q.μ + eLpNorm (fun x => covDerivHiggs A v.H x μ) 2 Q.μ +
    eLpNorm (spinCovA FC A v.Ψ μ) 2 Q.μ + eLpNorm (cospinCovA FC A v.Ψb μ) 2 Q.μ)

/-- **The covariant test size `𝔫_z(v)`** (`eq:equivariant-test-size`) at a configuration with
connection `A`, in the field-tuple rendering on the chart `Q`:
`‖k‖_{W^{1,∞}} + ‖a‖_∞ + ‖D_Aa‖_2 + ‖η_H‖_∞ + ‖D_Aη_H‖_2 + ‖η_Ψ‖_∞ + ‖∇^{A}η_Ψ‖_2 + ‖η_Ψ̄‖_∞ +
‖∇^{A}η_Ψ̄‖_2`. -/
def covTestSizeSM (Q : ChartBox T) (A : E4 → ConnFibre) (v : FieldTuple FC.C) : ℝ≥0∞ :=
  supPartSM FC Q v + derPartSM FC Q A v

end TestSize

/-! ### Control of the test jet by the test size -/

section TestJetControl

variable {Ysec : Type} (FC : FermionCarrier Ysec) {T : ℝ} {r : ℕ} {K : CylRegion T}

theorem aesm_test {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E4 → F}
    (hf : IsCylTest K f) (μ : Measure E4) : AEStronglyMeasurable f μ :=
  hf.smooth.continuous.aestronglyMeasurable

theorem aesm_pd_test {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E4 → F}
    (hf : IsCylTest K f) (i : Fin 4) (μ : Measure E4) :
    AEStronglyMeasurable (fun x => pd f i x) μ :=
  (SobolevOpen.continuous_pd (contDiff_test hf) i).aestronglyMeasurable

/-- **The value part of the test jet is controlled by the sup part of the test size.** -/
theorem eLpNorm_valPart_le (Q : ChartBox T) (v : CrTest FC.left r K) :
    eLpNorm (fun x => valPart (testJet v.val x)) ⊤ Q.μ ≤ supPartSM FC Q v.val := by
  have ce : Continuous v.val.e := (isCylTest_e v).smooth.continuous
  have cA : Continuous v.val.A := (isCylTest_A v).smooth.continuous
  have cH : Continuous v.val.H := (isCylTest_H v).smooth.continuous
  have cΨ : Continuous v.val.Ψ := (isCylTest_Ψ v).smooth.continuous
  have cΨb : Continuous v.val.Ψb := (isCylTest_Ψb v).smooth.continuous
  have cde : Continuous (fun x => fun i => pd v.val.e i x) :=
    continuous_pi fun i => SobolevOpen.continuous_pd (contDiff_test (isCylTest_e v)) i
  calc _ ≤ eLpNorm (fun x => ‖v.val.e x‖ + ‖fun i => pd v.val.e i x‖ + ‖v.val.A x‖ +
        ‖v.val.H x‖ + ‖v.val.Ψ x‖ + ‖v.val.Ψb x‖) ⊤ Q.μ :=
        eLpNorm_mono_real fun x => norm_valPart_le _
    _ ≤ _ := by
        unfold supPartSM
        refine (eLpNorm_add_le ((((ce.norm.add cde.norm).add cA.norm).add cH.norm).add
          cΨ.norm).aestronglyMeasurable cΨb.norm.aestronglyMeasurable le_top).trans ?_
        rw [eLpNorm_norm]
        gcongr
        refine (eLpNorm_add_le (((ce.norm.add cde.norm).add cA.norm).add
          cH.norm).aestronglyMeasurable cΨ.norm.aestronglyMeasurable le_top).trans ?_
        rw [eLpNorm_norm]
        gcongr
        refine (eLpNorm_add_le ((ce.norm.add cde.norm).add cA.norm).aestronglyMeasurable
          cH.norm.aestronglyMeasurable le_top).trans ?_
        rw [eLpNorm_norm]
        gcongr
        refine (eLpNorm_add_le (ce.norm.add cde.norm).aestronglyMeasurable
          cA.norm.aestronglyMeasurable le_top).trans ?_
        rw [eLpNorm_norm]
        gcongr
        refine (eLpNorm_add_le ce.norm.aestronglyMeasurable cde.norm.aestronglyMeasurable
          le_top).trans ?_
        rw [eLpNorm_norm, eLpNorm_norm]

theorem norm_pi_fin4_le_sum {F : Type*} [SeminormedAddCommGroup F] (f : Fin 4 → F) :
    ‖f‖ ≤ ∑ i, ‖f i‖ :=
  (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => norm_nonneg _)).mpr fun i =>
    Finset.single_le_sum (f := fun i => ‖f i‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i)

/-- The constant of the zeroth-order (connection) terms. -/
def actConst : ℝ :=
  ∑ μ, (‖adActL μ‖ + ‖higgsActL‖ + ‖spinActL FC μ‖ + ‖cospinActL FC μ‖)

theorem actConst_nonneg : 0 ≤ actConst FC := by unfold actConst; positivity

set_option maxHeartbeats 1000000 in
/-- Pointwise: the raw test derivatives are the covariant ones minus zeroth-order terms. -/
theorem norm_πD_testJet_le (A : E4 → ConnFibre) (v : FieldTuple FC.C) (x : E4) :
    ‖πD (testJet v x)‖ ≤ ∑ μ, (‖adCov A v.A μ x‖ + ‖covDerivHiggs A v.H x μ‖ +
        ‖spinCovA FC A v.Ψ μ x‖ + ‖cospinCovA FC A v.Ψb μ x‖) +
      actConst FC * (‖A x‖ * (‖v.A x‖ + ‖v.H x‖ + ‖v.Ψ x‖ + ‖v.Ψb x‖)) := by
  refine (norm_πD_le _).trans ?_
  show ‖fun i => pd v.A i x‖ + ‖fun i => pd v.H i x‖ + ‖fun i => pd v.Ψ i x‖ +
    ‖fun i => pd v.Ψb i x‖ ≤ _
  have hA : ∀ μ, ‖pd v.A μ x‖ ≤ ‖adCov A v.A μ x‖ + ‖adActL μ‖ * ‖A x‖ * ‖v.A x‖ := fun μ => by
    have : pd v.A μ x = adCov A v.A μ x - adActL μ (A x) (v.A x) := by
      rw [adCov, add_sub_cancel_right]
    have h2 : ‖adActL μ (A x) (v.A x)‖ ≤ ‖adActL μ‖ * ‖A x‖ * ‖v.A x‖ :=
      (adActL μ).le_opNorm₂ (A x) (v.A x)
    have h3 := norm_sub_le (adCov A v.A μ x) (adActL μ (A x) (v.A x))
    rw [this]
    linarith
  have hH : ∀ μ, ‖pd v.H μ x‖ ≤ ‖covDerivHiggs A v.H x μ‖ + ‖higgsActL‖ * ‖A x‖ * ‖v.H x‖ :=
    fun μ => by
    have : pd v.H μ x = covDerivHiggs A v.H x μ - higgsActL (A x) (v.H x) μ := by
      rw [show higgsActL (A x) (v.H x) μ = higgsAct (A x μ) (v.H x) from rfl, covDerivHiggs,
        add_sub_cancel_right]
    have h2 : ‖higgsActL (A x) (v.H x) μ‖ ≤ ‖higgsActL‖ * ‖A x‖ * ‖v.H x‖ :=
      (norm_le_pi_norm (higgsActL (A x) (v.H x)) μ).trans (higgsActL.le_opNorm₂ (A x) (v.H x))
    have h3 := norm_sub_le (covDerivHiggs A v.H x μ) (higgsActL (A x) (v.H x) μ)
    rw [this]
    linarith
  have hΨ : ∀ μ, ‖pd v.Ψ μ x‖ ≤ ‖spinCovA FC A v.Ψ μ x‖ + ‖spinActL FC μ‖ * ‖A x‖ * ‖v.Ψ x‖ :=
    fun μ => by
    have : pd v.Ψ μ x = spinCovA FC A v.Ψ μ x - spinActL FC μ (A x) (v.Ψ x) := by
      rw [spinCovA, add_sub_cancel_right]
    have h2 : ‖spinActL FC μ (A x) (v.Ψ x)‖ ≤ ‖spinActL FC μ‖ * ‖A x‖ * ‖v.Ψ x‖ :=
      (spinActL FC μ).le_opNorm₂ (A x) (v.Ψ x)
    have h3 := norm_sub_le (spinCovA FC A v.Ψ μ x) (spinActL FC μ (A x) (v.Ψ x))
    rw [this]
    linarith
  have hΨb : ∀ μ, ‖pd v.Ψb μ x‖ ≤ ‖cospinCovA FC A v.Ψb μ x‖ +
      ‖cospinActL FC μ‖ * ‖A x‖ * ‖v.Ψb x‖ := fun μ => by
    have : pd v.Ψb μ x = cospinCovA FC A v.Ψb μ x + cospinActL FC μ (A x) (v.Ψb x) := by
      rw [cospinCovA, sub_add_cancel]
    have h2 : ‖cospinActL FC μ (A x) (v.Ψb x)‖ ≤ ‖cospinActL FC μ‖ * ‖A x‖ * ‖v.Ψb x‖ :=
      (cospinActL FC μ).le_opNorm₂ (A x) (v.Ψb x)
    have h3 := norm_add_le (cospinCovA FC A v.Ψb μ x) (cospinActL FC μ (A x) (v.Ψb x))
    rw [this]
    linarith
  have hsA := (norm_pi_fin4_le_sum (fun i => pd v.A i x)).trans (Finset.sum_le_sum fun μ _ => hA μ)
  have hsH := (norm_pi_fin4_le_sum (fun i => pd v.H i x)).trans (Finset.sum_le_sum fun μ _ => hH μ)
  have hsΨ := (norm_pi_fin4_le_sum (fun i => pd v.Ψ i x)).trans (Finset.sum_le_sum fun μ _ => hΨ μ)
  have hsΨb := (norm_pi_fin4_le_sum (fun i => pd v.Ψb i x)).trans
    (Finset.sum_le_sum fun μ _ => hΨb μ)
  have hn := norm_nonneg (A x)
  have h1 := norm_nonneg (v.A x); have h2 := norm_nonneg (v.H x)
  have h3 := norm_nonneg (v.Ψ x); have h4 := norm_nonneg (v.Ψb x)
  have hc : ∀ μ, ‖adActL μ‖ * ‖A x‖ * ‖v.A x‖ + ‖higgsActL‖ * ‖A x‖ * ‖v.H x‖ +
      ‖spinActL FC μ‖ * ‖A x‖ * ‖v.Ψ x‖ + ‖cospinActL FC μ‖ * ‖A x‖ * ‖v.Ψb x‖ ≤
      (‖adActL μ‖ + ‖higgsActL‖ + ‖spinActL FC μ‖ + ‖cospinActL FC μ‖) *
        (‖A x‖ * (‖v.A x‖ + ‖v.H x‖ + ‖v.Ψ x‖ + ‖v.Ψb x‖)) := fun μ => by
    have c1 := norm_nonneg (adActL μ); have c2 := norm_nonneg higgsActL
    have c3 := norm_nonneg (spinActL FC μ); have c4 := norm_nonneg (cospinActL FC μ)
    have p1 := mul_nonneg hn h1; have p2 := mul_nonneg hn h2
    have p3 := mul_nonneg hn h3; have p4 := mul_nonneg hn h4
    nlinarith [mul_nonneg c1 p2, mul_nonneg c1 p3, mul_nonneg c1 p4, mul_nonneg c2 p1,
      mul_nonneg c2 p3, mul_nonneg c2 p4, mul_nonneg c3 p1, mul_nonneg c3 p2, mul_nonneg c3 p4,
      mul_nonneg c4 p1, mul_nonneg c4 p2, mul_nonneg c4 p3]
  calc _ ≤ ∑ μ, (‖adCov A v.A μ x‖ + ‖adActL μ‖ * ‖A x‖ * ‖v.A x‖) +
        ∑ μ, (‖covDerivHiggs A v.H x μ‖ + ‖higgsActL‖ * ‖A x‖ * ‖v.H x‖) +
        ∑ μ, (‖spinCovA FC A v.Ψ μ x‖ + ‖spinActL FC μ‖ * ‖A x‖ * ‖v.Ψ x‖) +
        ∑ μ, (‖cospinCovA FC A v.Ψb μ x‖ + ‖cospinActL FC μ‖ * ‖A x‖ * ‖v.Ψb x‖) := by
        gcongr
    _ = ∑ μ, (‖adCov A v.A μ x‖ + ‖covDerivHiggs A v.H x μ‖ + ‖spinCovA FC A v.Ψ μ x‖ +
          ‖cospinCovA FC A v.Ψb μ x‖) +
        ∑ μ, (‖adActL μ‖ * ‖A x‖ * ‖v.A x‖ + ‖higgsActL‖ * ‖A x‖ * ‖v.H x‖ +
          ‖spinActL FC μ‖ * ‖A x‖ * ‖v.Ψ x‖ + ‖cospinActL FC μ‖ * ‖A x‖ * ‖v.Ψb x‖) := by
        simp only [Finset.sum_add_distrib]; ring
    _ ≤ _ := by
        gcongr
        unfold actConst
        rw [Finset.sum_mul]
        exact Finset.sum_le_sum fun μ _ => hc μ

end TestJetControl

/-! ### `L²` control of the derivative slots -/

section DerControl

variable {Ysec : Type} (FC : FermionCarrier Ysec) {T : ℝ} {r : ℕ} {K : CylRegion T}

theorem aesm_clm₂ {V W U : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup U] [NormedSpace ℝ U]
    (B : V →L[ℝ] W →L[ℝ] U) {μ : Measure E4} {f : E4 → V} {g : E4 → W}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    AEStronglyMeasurable (fun x => B (f x) (g x)) μ :=
  B.continuous₂.comp_aestronglyMeasurable₂ hf hg

set_option maxHeartbeats 2000000 in
/-- **`‖π_D j¹v‖_{L²(Q)} ≤ (1 + c‖A‖_{L²(Q)}) 𝔫_z(v)`**: the raw matter-derivative slots of a test
jet are controlled by the covariant test size, the zeroth-order connection terms costing the
`L²` norm of the connection times the sup norms of the test. -/
theorem eLpNorm_derPart_le (Q : ChartBox T) {A : E4 → ConnFibre}
    (hA : AEStronglyMeasurable A Q.μ) (v : CrTest FC.left r K) :
    eLpNorm (fun x => πD (testJet v.val x)) 2 Q.μ ≤
      (1 + ENNReal.ofReal (actConst FC) * eLpNorm A 2 Q.μ) * covTestSizeSM FC Q A v.val := by
  have cA : Continuous v.val.A := (isCylTest_A v).smooth.continuous
  have cH : Continuous v.val.H := (isCylTest_H v).smooth.continuous
  have cΨ : Continuous v.val.Ψ := (isCylTest_Ψ v).smooth.continuous
  have cΨb : Continuous v.val.Ψb := (isCylTest_Ψb v).smooth.continuous
  have pA : ∀ μ, Continuous fun x => pd v.val.A μ x := fun μ =>
    SobolevOpen.continuous_pd (contDiff_test (isCylTest_A v)) μ
  have pH : ∀ μ, Continuous fun x => pd v.val.H μ x := fun μ =>
    SobolevOpen.continuous_pd (contDiff_test (isCylTest_H v)) μ
  have pΨ : ∀ μ, Continuous fun x => pd v.val.Ψ μ x := fun μ =>
    SobolevOpen.continuous_pd (contDiff_test (isCylTest_Ψ v)) μ
  have pΨb : ∀ μ, Continuous fun x => pd v.val.Ψb μ x := fun μ =>
    SobolevOpen.continuous_pd (contDiff_test (isCylTest_Ψb v)) μ
  have m1 : ∀ μ, AEStronglyMeasurable (adCov A v.val.A μ) Q.μ := fun μ =>
    (pA μ).aestronglyMeasurable.add (aesm_clm₂ (adActL μ) hA cA.aestronglyMeasurable)
  have m2 : ∀ μ, AEStronglyMeasurable (fun x => covDerivHiggs A v.val.H x μ) Q.μ := fun μ =>
    (pH μ).aestronglyMeasurable.add
      ((continuous_apply μ).comp_aestronglyMeasurable (aesm_clm₂ higgsActL hA
        cH.aestronglyMeasurable))
  have m3 : ∀ μ, AEStronglyMeasurable (spinCovA FC A v.val.Ψ μ) Q.μ := fun μ =>
    (pΨ μ).aestronglyMeasurable.add (aesm_clm₂ (spinActL FC μ) hA cΨ.aestronglyMeasurable)
  have m4 : ∀ μ, AEStronglyMeasurable (cospinCovA FC A v.val.Ψb μ) Q.μ := fun μ =>
    (pΨb μ).aestronglyMeasurable.sub (aesm_clm₂ (cospinActL FC μ) hA cΨb.aestronglyMeasurable)
  set S : E4 → ℝ := fun x => ‖v.val.A x‖ + ‖v.val.H x‖ + ‖v.val.Ψ x‖ + ‖v.val.Ψb x‖ with hS
  have mS : AEStronglyMeasurable S Q.μ :=
    (((cA.norm.add cH.norm).add cΨ.norm).add cΨb.norm).aestronglyMeasurable
  set G : E4 → ℝ := fun x => ∑ μ, (‖adCov A v.val.A μ x‖ + ‖covDerivHiggs A v.val.H x μ‖ +
      ‖spinCovA FC A v.val.Ψ μ x‖ + ‖cospinCovA FC A v.val.Ψb μ x‖) with hG
  have mG4 : ∀ μ, AEStronglyMeasurable (fun x => ‖adCov A v.val.A μ x‖ +
      ‖covDerivHiggs A v.val.H x μ‖ + ‖spinCovA FC A v.val.Ψ μ x‖ +
      ‖cospinCovA FC A v.val.Ψb μ x‖) Q.μ := fun μ =>
    (((m1 μ).norm.add (m2 μ).norm).add (m3 μ).norm).add (m4 μ).norm
  have mG : AEStronglyMeasurable G Q.μ := by
    have := Finset.aestronglyMeasurable_sum (μ := Q.μ) Finset.univ fun μ _ => mG4 μ
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp [hG, Finset.sum_apply]
  have mAS : AEStronglyMeasurable (fun x => ‖A x‖ * S x) Q.μ := hA.norm.mul mS
  -- `‖S‖_∞ ≤` the sup part
  have hSsup : eLpNorm S ⊤ Q.μ ≤ supPartSM FC Q v.val := by
    unfold supPartSM
    calc eLpNorm S ⊤ Q.μ ≤ eLpNorm v.val.A ⊤ Q.μ + eLpNorm v.val.H ⊤ Q.μ +
          eLpNorm v.val.Ψ ⊤ Q.μ + eLpNorm v.val.Ψb ⊤ Q.μ := by
          refine (eLpNorm_add_le ((cA.norm.add cH.norm).add cΨ.norm).aestronglyMeasurable
            cΨb.norm.aestronglyMeasurable le_top).trans ?_
          rw [eLpNorm_norm]
          gcongr
          refine (eLpNorm_add_le (cA.norm.add cH.norm).aestronglyMeasurable
            cΨ.norm.aestronglyMeasurable le_top).trans ?_
          rw [eLpNorm_norm]
          gcongr
          refine (eLpNorm_add_le cA.norm.aestronglyMeasurable cH.norm.aestronglyMeasurable
            le_top).trans ?_
          rw [eLpNorm_norm, eLpNorm_norm]
      _ ≤ _ := by
          calc _ ≤ eLpNorm v.val.e ⊤ Q.μ + eLpNorm (fun x => fun i => pd v.val.e i x) ⊤ Q.μ +
                (eLpNorm v.val.A ⊤ Q.μ + eLpNorm v.val.H ⊤ Q.μ + eLpNorm v.val.Ψ ⊤ Q.μ +
                  eLpNorm v.val.Ψb ⊤ Q.μ) := le_add_self
            _ = _ := by ring
  -- `‖G‖_2 ≤` the derivative part
  have hGder : eLpNorm G 2 Q.μ ≤ derPartSM FC Q A v.val := by
    unfold derPartSM
    have hsum : G = ∑ μ, fun x => ‖adCov A v.val.A μ x‖ + ‖covDerivHiggs A v.val.H x μ‖ +
        ‖spinCovA FC A v.val.Ψ μ x‖ + ‖cospinCovA FC A v.val.Ψb μ x‖ := by
      funext x; simp [hG, Finset.sum_apply]
    rw [hsum]
    refine (eLpNorm_sum_le (p := 2) (fun μ _ => mG4 μ) (by norm_num)).trans ?_
    exact Finset.sum_le_sum fun μ _ => by
      refine (eLpNorm_add_le (((m1 μ).norm.add (m2 μ).norm).add (m3 μ).norm) (m4 μ).norm
        (by norm_num)).trans ?_
      rw [eLpNorm_norm]
      gcongr
      refine (eLpNorm_add_le ((m1 μ).norm.add (m2 μ).norm) (m3 μ).norm (by norm_num)).trans ?_
      rw [eLpNorm_norm]
      gcongr
      refine (eLpNorm_add_le (m1 μ).norm (m2 μ).norm (by norm_num)).trans ?_
      rw [eLpNorm_norm, eLpNorm_norm]
  calc eLpNorm (fun x => πD (testJet v.val x)) 2 Q.μ
      ≤ eLpNorm (fun x => G x + actConst FC * (‖A x‖ * S x)) 2 Q.μ :=
        eLpNorm_mono_real fun x => norm_πD_testJet_le FC A v.val x
    _ ≤ eLpNorm G 2 Q.μ + eLpNorm (fun x => actConst FC * (‖A x‖ * S x)) 2 Q.μ :=
        eLpNorm_add_le mG (mAS.const_mul _) (by norm_num)
    _ ≤ derPartSM FC Q A v.val +
          ENNReal.ofReal (actConst FC) * (eLpNorm A 2 Q.μ * supPartSM FC Q v.val) := by
        gcongr
        have e1 : (fun x => actConst FC * (‖A x‖ * S x)) =
            actConst FC • (fun x => ‖A x‖ * S x) := rfl
        rw [e1, eLpNorm_const_smul, Real.enorm_eq_ofReal (actConst_nonneg FC)]
        gcongr
        have := eLpNorm_smul_le_mul_eLpNorm (p := 2) (q := ⊤) (r := 2) mS hA.norm
        simp only [eLpNorm_norm] at this
        exact ((le_of_eq rfl).trans this).trans (by gcongr)
    _ ≤ _ := by
        unfold covTestSizeSM
        have hd : derPartSM FC Q A v.val ≤ supPartSM FC Q v.val + derPartSM FC Q A v.val :=
          le_add_self
        have hs : supPartSM FC Q v.val ≤ supPartSM FC Q v.val + derPartSM FC Q A v.val :=
          le_self_add
        calc _ ≤ (supPartSM FC Q v.val + derPartSM FC Q A v.val) +
              ENNReal.ofReal (actConst FC) * (eLpNorm A 2 Q.μ *
                (supPartSM FC Q v.val + derPartSM FC Q A v.val)) := by gcongr
          _ = _ := by ring

end DerControl

/-! ### Bounded weak packets -/

section Packet

variable {C : Type} [Fintype C] {T : ℝ}

/-- **A bounded weak packet** on the chart `Q` (`lem:equivariant-tests`): `e, e⁻¹ ∈ L^∞` (values in
a fixed compact subset of the coframe chart), `e ∈ H¹`, `A ∈ L⁴`, `F_A ∈ L²` (identified as the
curvature of `A` in `𝒟'(Q)`), `H ∈ H¹`, `D_AH ∈ L²` (identified in `𝒟'(Q)`), `Ψ, Ψ̄ ∈ H¹`. -/
structure WeakPacket (Q : ChartBox T) (L : LimitFields C) : Prop where
  coframe_chart : ∃ Ke, IsCompactCoframeSet Ke ∧ ∀ᵐ x ∂Q.μ, L.e x ∈ Ke
  coframe_mem : MemH1 Q (coframeC L.e) L.de
  conn_mem : MemLp L.A 4 Q.μ
  curv_mem : MemLp L.F 2 Q.μ
  curv_weak : HasWeakCurvature Q L.A L.F
  higgs_mem : ∃ dH : E4 → Fin 4 → Fin 2 → ℂ, MemH1 Q L.H dH
  covgrad_mem : MemLp L.K 2 Q.μ
  covgrad_weak : HasWeakCovGrad Q L.A L.H L.K
  spinor_mem : MemH1 Q (spinorC L.Ψ) L.dΨ
  cospinor_mem : MemH1 Q (spinorC L.Ψb) L.dΨb

variable {ι : Type} [Fintype ι]

theorem memLp_of_memH1 {Q : ChartBox T} {u : E4 → ι → ℂ} {g : E4 → Fin 4 → ι → ℂ}
    (h : MemH1 Q u g) : MemLp u 2 Q.μ ∧ MemLp g 2 Q.μ :=
  ⟨memLp_pi_iff.mpr fun c => (h c).memLp,
    memLp_pi_iff.mpr fun i => memLp_pi_iff.mpr fun c => (h c).memLp_grad i⟩

/-- A fixed `H¹` field is a weakly convergent constant sequence. -/
theorem weakH1Tendsto_of_memH1 {Q : ChartBox T} {u : E4 → ι → ℂ} {g : E4 → Fin 4 → ι → ℂ}
    (h : MemH1 Q u g) : WeakH1Tendsto Q (fun _ => u) (fun _ => g) u g := by
  obtain ⟨hu, hg⟩ := memLp_of_memH1 h
  exact ⟨fun _ => h, h, ⟨h1Norm Q u g, ENNReal.add_ne_top.mpr ⟨hu.eLpNorm_ne_top,
    hg.eLpNorm_ne_top⟩, fun _ => le_rfl⟩, fun _ _ _ => tendsto_const_nhds,
    fun _ _ _ _ => tendsto_const_nhds⟩

/-- The real coframe components from the complex packet. -/
def coframeReL : (Fin 4 × Fin 4 → ℂ) →L[ℝ] CoframeFibre :=
  ContinuousLinearMap.pi fun a => ContinuousLinearMap.pi fun μ =>
    Complex.reCLM.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 × Fin 4 => ℂ) (a, μ))

theorem aesm_coframe {Q : ChartBox T} {e : E4 → CoframeFibre} {de : E4 → Fin 4 → Fin 4 × Fin 4 → ℂ}
    (h : MemH1 Q (coframeC e) de) : AEStronglyMeasurable e Q.μ := by
  have := coframeReL.continuous.comp_aestronglyMeasurable (memLp_of_memH1 h).1.1
  refine this.congr (Eventually.of_forall fun x => ?_)
  funext a μ
  simp [coframeReL, coframeC]

/-- The constant coframe sequence of a packet satisfies `CoframeConv`. -/
theorem coframeConv_const {Q : ChartBox T} {e : E4 → CoframeFibre}
    {de : E4 → Fin 4 → Fin 4 × Fin 4 → ℂ} (h : MemH1 Q (coframeC e) de) {Ke : Set CoframeFibre}
    (hKe : IsCompactCoframeSet Ke) (hin : ∀ᵐ x ∂Q.μ, e x ∈ Ke) :
    CoframeConv Q.μ Ke (fun _ x => e x) (fun x => e x) :=
  ⟨hKe.1, hKe.2.trans coframeChart_subset_GL, fun _ => (aesm_coframe h).aemeasurable,
    fun _ => hin, hin, tendstoInMeasure_of_tendsto_ae (fun _ => aesm_coframe h)
      (Eventually.of_forall fun _ => tendsto_const_nhds)⟩

end Packet

/-! ### The complete covector on a weak packet -/

section PacketCov

variable {Ysec : Type} (FC : FermionCarrier Ysec) {T : ℝ}

/-- The complete covector field `T ↦ (gravCov + bosonCov + diracCov)(z)(T)` at the jet of a packet. -/
def packetCov (θ : CoefficientBank Ysec) (L : LimitFields FC.C) (x : E4) : RJet FC.C →L[ℝ] ℝ :=
  gravCov θ (limitJet L x) + bosonCov θ (limitJet L x) + diracCov FC θ (limitJet L x)

/-- **The complete minimally coupled first variation at a weak packet** (`D𝒮_θ(z)[v]`): the
covector formula of the complete action (first-order gravitational representative + Yang–Mills +
Higgs + Dirac–Yukawa) on the jet of the packet; for smooth fields it is the first variation
(`gravVariation_eq_cov`, `smVariation_eq_cov`). -/
def completeLimitVariation (θ : CoefficientBank Ysec) (Q : ChartBox T) (L : LimitFields FC.C)
    {r : ℕ} {K : CylRegion T} (v : CrTest FC.left r K) : ℝ :=
  ∫ x in Q.set, packetCov FC θ L x (testJet v.val x)

theorem gravCov_ιD (θ : CoefficientBank Ysec) (R : RJet FC.C) (d : DerVal FC.C) :
    gravCov θ R (ιD d) = 0 := by
  simp [gravCov, gravCovF, gravC1, gravC2, gravC3, addTrilinL_apply, addBilinL_apply]

theorem bosonCov_ιD (θ : CoefficientBank Ysec) (R : RJet FC.C) (d : DerVal FC.C) :
    bosonCov θ R (ιD d) = ∑ j, gaugeScalars θ j * ymDaCoeff j R.e R.F (ιD d) +
      higgsDCoeff R.e R.K (ιD d) := by
  simp [bosonCov, ymMetCoeff, ymACoeff, higgsMetCoeff, higgsHCoeff, higgsACoeff, potHCoeff,
    potVCoeff]

theorem diracCov_ιD (θ : CoefficientBank Ysec) (R : RJet FC.C) (d : DerVal FC.C) :
    diracCov FC θ R (ιD d) = kinCoeff R.e (R.Ψb, R.Ψ) (d.2.2.1, d.2.2.2) := by
  have hπ : πτ (ιD d) = 0 := by
    simp only [πτ, ContinuousLinearMap.prod_apply, πe_apply, πΨb_apply, πΨ_apply, ιD_e, ιD_Ψb,
      ιD_Ψ, Prod.mk_zero_zero]
  have h2 : strongCoeff2 FC R.e (potVar' FC θ R) R.Ψb R.Ψ (ιD d) = 0 := by
    have : strongCoeff2 FC R.e (potVar' FC θ R) R.Ψb R.Ψ (ιD d) =
        strongCoeff2 FC R.e (potVar' FC θ R) R.Ψb R.Ψ 0 := by
      rw [strongCoeff2_apply, strongCoeff2_apply]; rfl
    rw [this, map_zero]
  simp only [diracCov, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, hπ,
    map_zero, add_zero, strongCoeff1, addTrilinL_apply, ιD_dΨ, ιD_dΨb, ιD_Ψ, ιD_Ψb,
    potVar', potVar, pU, ContinuousLinearMap.prod_apply, πΨb_apply, πΨ_apply,
    ContinuousLinearMap.zero_apply, one_mul]
  simp only [potVar', potVar] at h2
  rw [h2, add_zero]

end PacketCov

/-! ### Integrability of the complete covector on a weak packet -/

section PacketIntegrability

variable {Ysec : Type} (FC : FermionCarrier Ysec) {T : ℝ}

/-- The weak part of the fermionic covector as a jointly continuous function of the weak
coefficient and the spinor gradients. -/
def weakPairL (Ω : TestVal FC.C →L[ℝ] GradVal FC.C →L[ℝ] ℝ) (w : GradVal FC.C) :
    RJet FC.C →L[ℝ] ℝ :=
  (Ω.flip w).comp πτ

theorem continuous_weakPairL :
    Continuous fun p : (TestVal FC.C →L[ℝ] GradVal FC.C →L[ℝ] ℝ) × GradVal FC.C =>
      weakPairL FC p.1 p.2 := by
  have h1 : Continuous fun p : (TestVal FC.C →L[ℝ] GradVal FC.C →L[ℝ] ℝ) × GradVal FC.C =>
      p.1.flip p.2 :=
    ((ContinuousLinearMap.flipₗᵢ ℝ (TestVal FC.C) (GradVal FC.C) ℝ).continuous.comp
      continuous_fst).clm_apply continuous_snd
  exact ((ContinuousLinearMap.compL ℝ (RJet FC.C) (TestVal FC.C) ℝ).flip πτ).continuous.comp h1

theorem norm_weakPairL_le (Ω : TestVal FC.C →L[ℝ] GradVal FC.C →L[ℝ] ℝ) (w : GradVal FC.C) :
    ‖weakPairL FC Ω w‖ ≤ ‖πτ (C := FC.C)‖ * (‖Ω‖ * ‖w‖) := by
  unfold weakPairL
  calc ‖(Ω.flip w).comp πτ‖ ≤ ‖Ω.flip w‖ * ‖πτ (C := FC.C)‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (‖Ω.flip‖ * ‖w‖) * ‖πτ (C := FC.C)‖ := by gcongr; exact Ω.flip.le_opNorm w
    _ = ‖πτ (C := FC.C)‖ * (‖Ω‖ * ‖w‖) := by rw [ContinuousLinearMap.opNorm_flip]; ring

theorem diracCov_limitJet_eq (θ : CoefficientBank Ysec) (L : LimitFields FC.C) (x : E4) :
    diracCov FC θ (limitJet L x) =
      (strongCoeff1 FC (L.e x) (potVar' FC θ (limitJet L x)) (L.Ψb x, L.Ψ x) +
        strongCoeff2 FC (L.e x) (potVar' FC θ (limitJet L x)) (L.Ψb x) (L.Ψ x)) +
      weakPairL FC (weakCoeff (L.e x) ((1 : ℝ), (L.Ψb x, L.Ψ x)))
        (pW FC (limitJet L x)) := rfl

set_option maxHeartbeats 4000000 in
/-- **The complete covector of a weak packet is in `L¹(Q)`**, and its restriction to the
matter-derivative slots is in `L²(Q)`. -/
theorem packetCov_mem (θ : CoefficientBank Ysec) (Q : ChartBox T) {L : LimitFields FC.C}
    (hL : WeakPacket Q L) :
    MemLp (packetCov FC θ L) 1 Q.μ ∧ MemLp (fun x => (packetCov FC θ L x).comp ιD) 2 Q.μ := by
  obtain ⟨Ke, hKe, hLKe⟩ := hL.coframe_chart
  have he := coframeConv_const hL.coframe_mem hKe hLKe
  have hKGL : Ke ⊆ coframeGL := hKe.2.trans coframeChart_subset_GL
  -- the field data, as constant sequences
  have hde : RenewalGeometry.LpTendsto Q.μ 2 (fun _ x => toJet (reJet L.de x))
      (fun x => toJet (reJet L.de x)) :=
    coframeJet_L2_tendsto (e := fun _ => L.e) (de := fun _ => L.de) (fun _ => hL.coframe_mem)
      hL.coframe_mem (by simp [H1Tendsto, h1Norm])
  have hF := RenewalGeometry.LpTendsto.const hL.curv_mem
  have hK := RenewalGeometry.LpTendsto.const hL.covgrad_mem
  have hA4 := RenewalGeometry.LpTendsto.const hL.conn_mem
  have hA2 := RenewalGeometry.LpTendsto.const (hL.conn_mem.mono_exponent (p := 2) (by norm_num))
  obtain ⟨dH, hHm⟩ := hL.higgs_mem
  obtain ⟨hH2, MH, hMHt, hMH⟩ := weakH1_chart_data Q (weakH1Tendsto_of_memH1 hHm)
  have hH4m : MemLp L.H 4 Q.μ := ⟨hH2.memLp_lim.1, (hMH 0).trans_lt hMHt.lt_top⟩
  have hH4 := RenewalGeometry.LpTendsto.const hH4m
  obtain ⟨hΨ2, ⟨MΨ, hMΨt, hMΨ⟩, -, hgΨ₀, -, -⟩ :=
    spinor_chart_data Q (u := fun _ => L.Ψ) (weakH1Tendsto_of_memH1 hL.spinor_mem)
  obtain ⟨hΨb2, ⟨MΨb, hMΨbt, hMΨb⟩, -, hgΨb₀, -, -⟩ :=
    spinor_chart_data Q (u := fun _ => L.Ψb) (weakH1Tendsto_of_memH1 hL.cospinor_mem)
  -- gravity
  have hg1 := (gravCov_tendsto (C := FC.C) he hde (θ := fun _ => θ) (θ₀ := θ) tendsto_const_nhds
    tendsto_const_nhds).memLp_lim
  -- bosons
  have hb1 := (bosonCov_tendsto (C := FC.C) (R := fun _ => limitJet L) (R₀ := limitJet L) he hF
    hA4 hK hH4 (θ := fun _ => θ) (θ₀ := θ) (fun _ => tendsto_const_nhds) tendsto_const_nhds
    tendsto_const_nhds).memLp_lim
  -- Dirac, strong part
  have hM : MemLp (fun x => FC.yukawa θ (L.H x)) 2 Q.μ := by
    have := ((yukL FC θ).comp_memLp' hH2.memLp_lim).add (memLp_const (FC.yukawa θ 0))
    exact this.ae_eq (Eventually.of_forall fun x => (yukawa_eq FC θ (L.H x)).symm)
  have hYm : MemLp (fun x => potVar' FC θ (limitJet L x)) 2 Q.μ :=
    memLp_prodMk (memLp_prodMk hde.memLp_lim (memLp_prodMk hA2.memLp_lim
      (memLp_prodMk hM (memLp_const (1 : ℝ))))) (memLp_const _)
  have hs1 := (diracStrong_tendsto FC he (RenewalGeometry.LpTendsto.const hYm) hΨb2 hΨ2
    (M := MΨ + MΨb) (ENNReal.add_ne_top.mpr ⟨hMΨt, hMΨbt⟩) (fun _ => (hMΨb 0).trans le_add_self)
    (fun _ => (hMΨ 0).trans le_self_add)).memLp_lim
  -- Dirac, weak part
  have hΩ := (diracWeak_tendsto FC he hΨb2 hΨ2).memLp_lim
  have hW : MemLp (fun x => pW FC (limitJet L x)) 2 Q.μ :=
    memLp_prodMk ((gradCurryL FC.C).comp_memLp' hgΨ₀) ((gradCurryL FC.C).comp_memLp' hgΨb₀)
  have hwm : AEStronglyMeasurable (fun x => weakPairL FC (weakCoeff (L.e x)
      ((1 : ℝ), (L.Ψb x, L.Ψ x))) (pW FC (limitJet L x))) Q.μ :=
    (continuous_weakPairL FC).comp_aestronglyMeasurable₂ hΩ.1 hW.1
  have hw1 : MemLp (fun x => weakPairL FC (weakCoeff (L.e x) ((1 : ℝ), (L.Ψb x, L.Ψ x)))
      (pW FC (limitJet L x))) 1 Q.μ := by
    have hprod : MemLp (fun x => ‖πτ (C := FC.C)‖ * (‖weakCoeff (L.e x)
        ((1 : ℝ), (L.Ψb x, L.Ψ x))‖ * ‖pW FC (limitJet L x)‖)) 1 Q.μ := by
      have h221 := holderTriple_two_two_one_jet
      exact (hW.norm.mul' hΩ.norm).const_mul _
    refine hprod.of_le hwm (Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact norm_weakPairL_le FC _ _
  have hd1 : MemLp (fun x => diracCov FC θ (limitJet L x)) 1 Q.μ :=
    (hs1.add hw1).ae_eq (Eventually.of_forall fun x => (diracCov_limitJet_eq FC θ L x).symm)
  have hΛ : MemLp (packetCov FC θ L) 1 Q.μ := (hg1.add hb1).add hd1
  refine ⟨hΛ, ?_⟩
  -- the derivative slots
  choose M₁ hM₁ using fun j => hKe.1.exists_bound_of_continuousOn
    (f := fun e => ymDaCoeff (C := FC.C) j e) ((continuousOn_ymDaCoeff (C := FC.C) j).mono hKGL)
  obtain ⟨M₂, hM₂⟩ := hKe.1.exists_bound_of_continuousOn
    (f := fun e => higgsDCoeff (C := FC.C) e) ((continuousOn_higgsDCoeff (C := FC.C)).mono hKGL)
  obtain ⟨M₃, hM₃⟩ := hKe.1.exists_bound_of_continuousOn
    (f := fun e => kinCoeff (C := FC.C) e)
    ((contDiffOn_kinCoeff (C := FC.C) (n := 0)).continuousOn.mono hKGL)
  set s := ∑ j, |gaugeScalars θ j| * M₁ j with hs
  have hFn := hL.curv_mem.norm
  have hKn := hL.covgrad_mem.norm
  have hUn : MemLp (fun x => ‖((L.Ψb x, L.Ψ x) : SpinorFibre FC.C × SpinorFibre FC.C)‖) 2 Q.μ :=
    (memLp_prodMk hΨb2.memLp_lim hΨ2.memLp_lim).norm
  have hdom : MemLp (fun x => ‖ιD (C := FC.C)‖ * s * ‖L.F x‖ +
      ‖ιD (C := FC.C)‖ * M₂ * ‖L.K x‖ + M₃ * ‖((L.Ψb x, L.Ψ x) : SpinorFibre FC.C ×
        SpinorFibre FC.C)‖) 2 Q.μ :=
    ((hFn.const_mul _).add (hKn.const_mul _)).add (hUn.const_mul _)
  have hDm : AEStronglyMeasurable (fun x => (packetCov FC θ L x).comp ιD) Q.μ :=
    ((ContinuousLinearMap.compL ℝ (DerVal FC.C) (RJet FC.C) ℝ).flip ιD).continuous.comp_aestronglyMeasurable
      hΛ.1
  refine hdom.of_le hDm ?_
  filter_upwards [hLKe] with x hx
  have hM₁x : ∀ j, ‖ymDaCoeff (C := FC.C) j (L.e x)‖ ≤ M₁ j := fun j => hM₁ j _ hx
  have hM₂x := hM₂ _ hx
  have hM₃x := hM₃ _ hx
  have hM₁0 : ∀ j, 0 ≤ M₁ j := fun j =>
    (norm_nonneg (ymDaCoeff (C := FC.C) j (L.e x))).trans (hM₁x j)
  have hM₂0 : 0 ≤ M₂ := (norm_nonneg (higgsDCoeff (C := FC.C) (L.e x))).trans hM₂x
  have hM₃0 : 0 ≤ M₃ := (norm_nonneg (kinCoeff (C := FC.C) (L.e x))).trans hM₃x
  have hs0 : 0 ≤ s := Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (hM₁0 j)
  rw [Real.norm_of_nonneg (by positivity)]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun d => ?_
  simp only [ContinuousLinearMap.comp_apply, packetCov, ContinuousLinearMap.add_apply,
    gravCov_ιD, bosonCov_ιD, diracCov_ιD, zero_add]
  have hd : ‖ιD d‖ ≤ ‖ιD (C := FC.C)‖ * ‖d‖ := ιD.le_opNorm d
  have hd2 : ‖((d.2.2.1, d.2.2.2) : (Fin 4 → SpinorFibre FC.C) × (Fin 4 → SpinorFibre FC.C))‖ ≤
      ‖d‖ := (norm_snd_le d.2).trans (norm_snd_le d)
  have hFx := norm_nonneg (L.F x)
  have hKx := norm_nonneg (L.K x)
  have hιd := norm_nonneg (ιD d)
  have t1 : ∀ j, |gaugeScalars θ j * ymDaCoeff (C := FC.C) j (L.e x) (L.F x) (ιD d)| ≤
      |gaugeScalars θ j| * M₁ j * (‖L.F x‖ * (‖ιD (C := FC.C)‖ * ‖d‖)) := fun j => by
    have h := (ymDaCoeff (C := FC.C) j (L.e x)).le_opNorm₂ (L.F x) (ιD d)
    rw [Real.norm_eq_abs] at h
    rw [abs_mul, mul_assoc]
    gcongr
    calc _ ≤ ‖ymDaCoeff (C := FC.C) j (L.e x)‖ * ‖L.F x‖ * ‖ιD d‖ := h
      _ ≤ M₁ j * ‖L.F x‖ * (‖ιD (C := FC.C)‖ * ‖d‖) :=
          mul_le_mul (mul_le_mul_of_nonneg_right (hM₁x j) hFx) hd hιd
            (mul_nonneg (hM₁0 j) hFx)
      _ = _ := by ring
  have t2 : |higgsDCoeff (C := FC.C) (L.e x) (L.K x) (ιD d)| ≤
      M₂ * ‖L.K x‖ * (‖ιD (C := FC.C)‖ * ‖d‖) := by
    have h := (higgsDCoeff (C := FC.C) (L.e x)).le_opNorm₂ (L.K x) (ιD d)
    rw [Real.norm_eq_abs] at h
    calc _ ≤ ‖higgsDCoeff (C := FC.C) (L.e x)‖ * ‖L.K x‖ * ‖ιD d‖ := h
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_right hM₂x hKx) hd hιd (mul_nonneg hM₂0 hKx)
  have t3 : |kinCoeff (C := FC.C) (L.e x) (L.Ψb x, L.Ψ x) (d.2.2.1, d.2.2.2)| ≤
      M₃ * ‖((L.Ψb x, L.Ψ x) : SpinorFibre FC.C × SpinorFibre FC.C)‖ * ‖d‖ := by
    have h := (kinCoeff (C := FC.C) (L.e x)).le_opNorm₂ (L.Ψb x, L.Ψ x) (d.2.2.1, d.2.2.2)
    rw [Real.norm_eq_abs] at h
    calc _ ≤ _ := h
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_right hM₃x (norm_nonneg _)) hd2 (norm_nonneg _)
          (mul_nonneg hM₃0 (norm_nonneg _))
  have tsum : |∑ j, gaugeScalars θ j * ymDaCoeff (C := FC.C) j (L.e x) (L.F x) (ιD d)| ≤
      s * (‖L.F x‖ * (‖ιD (C := FC.C)‖ * ‖d‖)) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [hs, Finset.sum_mul]
    exact Finset.sum_le_sum fun j _ => t1 j
  rw [Real.norm_eq_abs]
  calc _ ≤ |∑ j, gaugeScalars θ j * ymDaCoeff (C := FC.C) j (L.e x) (L.F x) (ιD d)| +
        |higgsDCoeff (C := FC.C) (L.e x) (L.K x) (ιD d)| +
        |kinCoeff (C := FC.C) (L.e x) (L.Ψb x, L.Ψ x) (d.2.2.1, d.2.2.2)| := abs_add_three _ _ _
    _ ≤ s * (‖L.F x‖ * (‖ιD (C := FC.C)‖ * ‖d‖)) +
        M₂ * ‖L.K x‖ * (‖ιD (C := FC.C)‖ * ‖d‖) +
        M₃ * ‖((L.Ψb x, L.Ψ x) : SpinorFibre FC.C × SpinorFibre FC.C)‖ * ‖d‖ := by gcongr
    _ = _ := by ring

end PacketIntegrability

/-! ### `eq:equivariant-firstvariation-bound` -/

section MainBound

variable {Ysec : Type} (FC : FermionCarrier Ysec) {T : ℝ}

/-- **`lem:equivariant-tests`, `eq:equivariant-firstvariation-bound`** (field-tuple rendering on a
chart `Q`).  On every bounded weak packet `z` (`e, e⁻¹ ∈ L^∞`, `e ∈ H¹`, `A ∈ L⁴`, `F_A, D_AH ∈ L²`,
`H, Ψ, Ψ̄ ∈ H¹`) there is a finite constant `C_K` such that the complete minimally coupled first
variation satisfies `|D𝒮_θ(z)[v]| ≤ C_K 𝔫_z(v)` for every test `v` (any `C^r` test space).
Explicitly `C_K = ‖Λ_z‖_{L¹} + ‖Λ_z∘ι_D‖_{L²}(1 + c‖A‖_{L²})`, with `Λ_z` the complete covector:
the Yang–Mills row pairs `F_A` with `D_Aa`, the Higgs row `D_AH` with `D_Aη_H + ρ_H(a)H`, the quartic
force is integrable by `H¹ ⊂ L⁴`, the Dirac rows use one `L²` spinor derivative and bounded test
coefficients, and the gravitational (first-order) and spin-connection metric variations involve
`k, ∂k` with `L²` coframe derivatives only. -/
theorem equivariant_firstVariation_bound (θ : CoefficientBank Ysec) (Q : ChartBox T)
    {L : LimitFields FC.C} (hL : WeakPacket Q L) :
    ∃ CK : ℝ≥0∞, CK ≠ ⊤ ∧ ∀ {r : ℕ} {K : CylRegion T} (v : CrTest FC.left r K),
      ENNReal.ofReal |completeLimitVariation FC θ Q L v| ≤ CK * covTestSizeSM FC Q L.A v.val := by
  obtain ⟨hΛ, hΛD⟩ := packetCov_mem FC θ Q hL
  have hA2 : MemLp L.A 2 Q.μ := hL.conn_mem.mono_exponent (p := 2) (by norm_num)
  refine ⟨eLpNorm (packetCov FC θ L) 1 Q.μ + eLpNorm (fun x => (packetCov FC θ L x).comp ιD) 2
      Q.μ * (1 + ENNReal.ofReal (actConst FC) * eLpNorm L.A 2 Q.μ), ?_, fun {r K} v => ?_⟩
  · exact ENNReal.add_ne_top.mpr ⟨hΛ.eLpNorm_ne_top, ENNReal.mul_ne_top hΛD.eLpNorm_ne_top
      (ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        hA2.eLpNorm_ne_top⟩)⟩
  have hτ : AEStronglyMeasurable (fun x => testJet v.val x) Q.μ :=
    (continuous_testJet v).aestronglyMeasurable
  have h := abs_integral_jet_le (μ := Q.μ) hΛ.1 hτ
  have hv := eLpNorm_valPart_le FC Q v
  have hd := eLpNorm_derPart_le FC Q hA2.1 v
  have hsup : supPartSM FC Q v.val ≤ covTestSizeSM FC Q L.A v.val := le_self_add
  unfold completeLimitVariation
  calc _ ≤ _ := h
    _ ≤ eLpNorm (packetCov FC θ L) 1 Q.μ * covTestSizeSM FC Q L.A v.val +
        eLpNorm (fun x => (packetCov FC θ L x).comp ιD) 2 Q.μ *
          ((1 + ENNReal.ofReal (actConst FC) * eLpNorm L.A 2 Q.μ) *
            covTestSizeSM FC Q L.A v.val) := by
        gcongr
        exact hv.trans hsup
    _ = _ := by ring

end MainBound

/-! ### Non-vacuity -/

/-- The flat limit fields form a bounded weak packet on every chart box. -/
theorem flatLimit_weakPacket {T : ℝ} (Q : ChartBox T) : WeakPacket Q flatLimit :=
  ⟨⟨{flatCoframe}, isCompactCoframeSet_flat, Eventually.of_forall fun _ => rfl⟩,
    memH1_const Q (fun p : Fin 4 × Fin 4 => (flatCoframe p.1 p.2 : ℂ)), MemLp.zero, MemLp.zero,
    hasWeakCurvature_zero Q,
    ⟨fun _ _ => 0, memH1_const Q 0⟩, MemLp.zero, hasWeakCovGrad_zero Q, memH1_const Q 0,
    memH1_const Q 0⟩

/-- **Non-vacuity of `equivariant_firstVariation_bound`**: the flat packet (trivial carrier). -/
example {T : ℝ} (θ : CoefficientBank Unit) (Q : ChartBox T) :
    ∃ CK : ℝ≥0∞, CK ≠ ⊤ ∧ ∀ {r : ℕ} {K : CylRegion T} (v : CrTest (trivialCarrier Unit).left r K),
      ENNReal.ofReal |completeLimitVariation (trivialCarrier Unit) θ Q flatLimit v| ≤
        CK * covTestSizeSM (trivialCarrier Unit) Q flatLimit.A v.val :=
  equivariant_firstVariation_bound (trivialCarrier Unit) θ Q (flatLimit_weakPacket Q)

end EinsteinSM
end RenewalGeometry
