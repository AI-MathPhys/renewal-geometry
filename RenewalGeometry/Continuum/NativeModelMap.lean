/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.NativeDiracEulerRows

/-!
# The native model map: physical representation data and the matter field equations

Einstein–Standard-Model action-closure manuscript, bridge step P1 of `thm:native-closure`.

`NativeDensity.Data` carries the coefficient bank and representation data of
`eq:native-densities` as arbitrary (bi)linear data.  A **native model** (`Model`) adds the
structure the physical reading of `eq:native-densities` presupposes:

* a symmetric, ad-invariant, nondegenerate invariant form `⟨·,·⟩_𝐠` on the gauge algebra;
* a symmetric nondegenerate real Hermitian form `Re⟨·,·⟩` on the Higgs space, for which the
  gauge Lie algebra `gLie ⊆ 𝔄` acts by skew operators;
* the Clifford relations `γ^aγ^b + γ^bγ^a = 2η^{ab}`, the spin representation
  `σ(ω) = ¼ω_{ab}γ^aγ^b` and a gauge action commuting with Clifford multiplication;
* a **complex structure** `J` on the spinor space (`J² = -1`) commuting with `γ^a`, `ρ_S` and the
  Yukawa map; physical co-spinors are the `ℂ`-linear ones, `Ψ̄(Jx) = iΨ̄(x)` (`IsCLin`).

## Results

* `cliffordFrame` — the Clifford frame `c_a = Jγ^a` in the convention of the actual-jet system
  (`c_ac_b + c_bc_a = -2ε_aδ_{ab}`, `ε = (-1, 1, 1, 1)`, `ActualJetWriter.IsLorentzian`): the
  Clifford datum of `ActualJetSystem.DiracData`.
* `diracRes`, `psibar_row_model` — on physical co-spinor directions the `Ψ̄`-row is
  `v(e) Re φ(r_D)` with the Dirac residual `r_D = c^μ∇_μΨ - 𝓜_𝐘(H)Ψ`, `c^μ = Jγ^μ(e)`;
  `psibar_rows_vanish_iff` — the `Ψ̄`-rows vanish on all physical directions iff `r_D = 0`
  (Hahn–Banach separation by `ℂ`-linear functionals, `exists_clin_re_ne`).  This fixes the
  rendering issue of the real-linear co-spinor space noted in the previous pass.
* `exists_current` — the matter current is represented through the invariant form and the
  inverse metric (finite-dimensional gauge algebra); `ym_rows_vanish_iff` — the gauge rows vanish
  iff the Yang–Mills residual `ActualJetGauge.ymRes` with that current vanishes.
* `exists_higgs_source`, `higgs_rows_vanish_iff` — likewise for the Higgs rows and the covariant
  wave equation `□_AH = S_H`.
* `diracResBar`, `psi_row_model`, `psi_rows_vanish_iff` — for a physical co-spinor field the
  `Ψ`-rows are `-v(e) Re r̄_D(χ)` with the dual Dirac residual `r̄_D = (∇_μΨ̄)c^μ + Ψ̄𝓜_𝐘(H)`, and
  they vanish iff `r̄_D = 0` (the derivative of a physical co-spinor field is physical,
  `isCLin_pd`).
* **`matter_equations`** — an exact native critical point (vanishing Euler covector in all matter
  directions) solves the Yang–Mills equation with the represented current (slab-model residual
  `ActualJetGauge.ymRes = 0`), the Higgs equation `□_AH = S_H`, the Dirac equation
  `c^μ∇_μΨ = 𝓜_𝐘(H)Ψ` and the dual Dirac equation.

Disclosed renderings: the model is stated in the native frame `e` (the slab model of
`prop:coupled-bootstrap` uses the algebraic adapted frame `frU(g⁻¹)`; the spin lift relating the
two, bridge step P2, is not part of this file); the gauge algebra is the associative algebra `𝔄`
of `NativeDensity.Data` (not `ActualJetSmooth.MatLie m` with a Lie module); finite-dimensional
gauge algebra and Higgs space for the existence of currents and sources.
-/

namespace RenewalGeometry

namespace NativeModel

open Finset HarmonicDefect EHFieldVariation ActualJetSystem PalatiniEuler NativeMatterEuler
  NativeBosonicEuler
  NativeDiracEuler
open NativeScaling (Mat eta metric)
open NativeDensity
open DiscreteEulerConsistency (R4 evec jet1 contEuler)
open SobolevOpen (pd)
open scoped ContDiff

noncomputable section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 400000

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]

/-- **A native model**: the representation data of `eq:native-densities` with the structure
presupposed by its physical reading (see the module docstring). -/
structure Model (𝔄 𝓗 𝓢 : Type*) [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [NormedAddCommGroup 𝓗]
    [NormedSpace ℝ 𝓗] [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] extends Data 𝔄 𝓗 𝓢 where
  ipA_symm : ∀ x y, ipA x y = ipA y x
  ipA_inv : ∀ a x y, ipA (a * x - x * a) y = -ipA x (a * y - y * a)
  ipA_nondeg : ∀ x, (∀ y, ipA y x = 0) → x = 0
  hermH_symm : ∀ x y, hermH x y = hermH y x
  hermH_nondeg : ∀ x, (∀ y, hermH y x = 0) → x = 0
  /-- the gauge Lie algebra inside `𝔄` -/
  gLie : Set 𝔄
  rhoH_skew : ∀ a ∈ gLie, ∀ x y, hermH (ρH a x) y = -hermH x (ρH a y)
  cliff : ∀ a b, γ a * γ b + γ b * γ a = (2 * eta a b) • 1
  sigma_eq : ∀ om, σ om = sigmaOf γ om
  gauge_cliff : ∀ A a, ρS A * γ a = γ a * ρS A
  /-- the complex structure of the spinor space -/
  J : Spin 𝓢
  J_sq : J * J = -1
  J_gamma : ∀ a, J * γ a = γ a * J
  J_rhoS : ∀ A, J * ρS A = ρS A * J
  J_yukawa : ∀ H, J * yukawa H = yukawa H * J

variable (M : Model 𝔄 𝓗 𝓢)

/-- Physical (`ℂ`-linear) co-spinors: `φ(Jx) = iφ(x)`. -/
def IsCLin (φ : CoSpinor 𝓢) : Prop := ∀ x, φ (M.J x) = Complex.I * φ x

/-! ### The Clifford frame of the actual-jet system -/

theorem eta_eq_ite (a b : Fin 4) : eta a b = if a = b then ActualJetSystem.lorentzSign a else 0 := by
  fin_cases a <;> fin_cases b <;> simp [eta, ActualJetSystem.lorentzSign]

/-- **The Clifford frame `c_a = Jγ^a`** in the convention `c_ac_b + c_bc_a = -2ε_aδ_{ab}` of the
actual-jet system, with Lorentzian signs. -/
def cliffordFrame : TwistedHalfRicci.CliffordFrame (Fin 4) (Spin 𝓢) where
  c a := M.J * M.γ a
  ε := ActualJetSystem.lorentzSign
  sign_sq a := by unfold ActualJetSystem.lorentzSign; split_ifs <;> norm_num
  anticomm a b := by
    have h := M.cliff a b
    calc M.J * M.γ a * (M.J * M.γ b) + M.J * M.γ b * (M.J * M.γ a) =
        (M.J * M.J) * (M.γ a * M.γ b + M.γ b * M.γ a) := by
          rw [mul_add, mul_assoc M.J, ← mul_assoc (M.γ a), ← M.J_gamma a, mul_assoc M.J (M.γ b),
            ← mul_assoc (M.γ b), ← M.J_gamma b]
          noncomm_ring
      _ = _ := by
          rw [M.J_sq, h, eta_eq_ite]
          simp only [neg_mul, one_mul, mul_smul_comm, mul_one, neg_smul]
          split_ifs <;> simp

theorem cliffordFrame_lorentzian : ActualJetWriter.IsLorentzian (cliffordFrame M) :=
  ⟨by simp [cliffordFrame, ActualJetSystem.lorentzSign],
    fun a => by simp [cliffordFrame, ActualJetSystem.lorentzSign, Fin.succ_ne_zero]⟩

/-! ### The Dirac rows in residual form -/

variable {Y : R4 → Field 𝔄 𝓗 𝓢}

/-- **The native Dirac residual** `r_D = c^μ∇_μΨ - 𝓜_𝐘(H)Ψ`, `c^μ = Jγ^μ(e)`. -/
def diracRes (Y : R4 → Field 𝔄 𝓗 𝓢) (z : R4) : 𝓢 :=
  M.J (∑ μ, gammaMu M.toData μ (Y z).1 (DPsi M.toData (jet1 Y z) μ)) -
    M.yukawa (Y z).2.2.1 (Y z).2.2.2.1

/-- The residual in Clifford-frame form `r_D = Σ_μ e_a^μ c^a ∇_μΨ - 𝓜Ψ`. -/
theorem diracRes_eq_frame (z : R4) :
    diracRes M Y z = ∑ μ, ∑ a, ((Y z).1)⁻¹ μ a • (cliffordFrame M).c a
        (DPsi M.toData (jet1 Y z) μ) - M.yukawa (Y z).2.2.1 (Y z).2.2.2.1 := by
  unfold diracRes cliffordFrame
  simp only [gammaMu_eq, map_sum, ContinuousLinearMap.coe_sum', Finset.sum_apply,
    ContinuousLinearMap.smul_apply, map_smul, ContinuousLinearMap.mul_apply]

/-- **The `Ψ̄`-row on physical co-spinor directions is `v(e)` times the Dirac residual**:
`𝓔₀(Y)(z)[(0, 0, 0, 0, φ)] = v(e) Re φ(c^μ∇_μΨ - 𝓜Ψ)` for every `ℂ`-linear `φ`. -/
theorem psibar_row_model (hY : ContDiff ℝ ∞ Y) (hdet : ∀ z, 0 < ((Y z).1).det) (z : R4)
    {φ : CoSpinor 𝓢} (hφ : IsCLin M φ) :
    contEuler (L0 M.toData) Y z (psiBarDir φ) = volume (Y z).1 * (φ (diracRes M Y z)).re := by
  rw [psibar_euler_row M.toData M.cliff M.sigma_eq M.gauge_cliff hY hdet z φ]
  unfold diracRes
  rw [map_sub, hφ]

/-- Separation of spinors by physical co-spinors: every nonzero spinor has a `ℂ`-linear
co-spinor with nonzero real part on it. -/
theorem exists_clin_re_ne {w : 𝓢} (hw : w ≠ 0) : ∃ φ : CoSpinor 𝓢, IsCLin M φ ∧ (φ w).re ≠ 0 := by
  obtain ⟨ℓ, -, hℓ⟩ := exists_dual_vector ℝ w (norm_ne_zero_iff.2 hw)
  set φ : CoSpinor 𝓢 := Complex.ofRealCLM.comp ℓ - Complex.I • Complex.ofRealCLM.comp (ℓ.comp M.J)
  refine ⟨φ, fun x => ?_, ?_⟩
  · have hJJ : M.J (M.J x) = -x := by
      rw [← ContinuousLinearMap.mul_apply, M.J_sq]; simp
    simp only [φ, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smul_apply, Complex.ofRealCLM_apply, hJJ, map_neg, smul_eq_mul]
    ring_nf
    rw [Complex.I_sq]
    ring
  · simp only [φ, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smul_apply, Complex.ofRealCLM_apply, smul_eq_mul, Complex.sub_re,
      Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im, hℓ]
    simpa using hw

/-- **The `Ψ̄`-rows vanish on all physical directions iff the Dirac equation holds**:
`(∀ φ ℂ-linear, 𝓔₀(Y)(z)[(0,0,0,0,φ)] = 0) ↔ c^μ∇_μΨ = 𝓜_𝐘(H)Ψ`. -/
theorem psibar_rows_vanish_iff (hY : ContDiff ℝ ∞ Y) (hdet : ∀ z, 0 < ((Y z).1).det) (z : R4) :
    (∀ φ : CoSpinor 𝓢, IsCLin M φ → contEuler (L0 M.toData) Y z (psiBarDir φ) = 0) ↔
      diracRes M Y z = 0 := by
  have hv : volume (Y z).1 ≠ 0 := by
    rw [volume_of_det_pos (hdet z)]; exact (hdet z).ne'
  constructor
  · intro h
    by_contra hne
    obtain ⟨φ, hφ, hre⟩ := exists_clin_re_ne M hne
    have := h φ hφ
    rw [psibar_row_model M hY hdet z hφ] at this
    exact hre ((mul_eq_zero.1 this).resolve_left hv)
  · intro h φ hφ
    rw [psibar_row_model M hY hdet z hφ, h, map_zero, Complex.zero_re, mul_zero]

/-! ### The gauge rows: currents and the Yang–Mills equation -/

section Gauge

variable [FiniteDimensional ℝ 𝔄]

/-- **Representation of a gauge current**: for an invertible symmetric inverse metric `g⁻¹`,
`v ≠ 0` and a nondegenerate form, every linear functional on gauge directions is
`X ↦ v g^{νσ}⟨X_ν, J_σ⟩` for a unique current `J`. -/
theorem exists_current (g gi : Fin 4 → Fin 4 → ℝ)
    (hinv : ∀ a c, ∑ b, g a b * gi b c = if a = c then 1 else 0) {v : ℝ} (hv : v ≠ 0)
    (c : (Fin 4 → 𝔄) →ₗ[ℝ] ℝ) :
    ∃ Jc : Fin 4 → 𝔄, ∀ X : Fin 4 → 𝔄, v * ∑ ν, ∑ σ, gi ν σ * M.ipA (X ν) (Jc σ) = c X := by
  set Φ : (Fin 4 → 𝔄) →ₗ[ℝ] Module.Dual ℝ (Fin 4 → 𝔄) :=
    { toFun := fun Jc =>
        { toFun := fun X => v * ∑ ν, ∑ σ, gi ν σ * M.ipA (X ν) (Jc σ)
          map_add' := fun X X' => by
            simp only [Pi.add_apply, map_add, ContinuousLinearMap.add_apply, mul_add,
              Finset.sum_add_distrib]
          map_smul' := fun r X => by
            simp only [Pi.smul_apply, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul,
              RingHom.id_apply, Finset.mul_sum]
            refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun σ _ => ?_
            ring }
      map_add' := fun Jc Jc' => by
        refine LinearMap.ext fun X => ?_
        simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, Pi.add_apply, map_add,
          mul_add, Finset.sum_add_distrib]
      map_smul' := fun r Jc => by
        refine LinearMap.ext fun X => ?_
        simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, Pi.smul_apply, map_smul,
          smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun σ _ => ?_
        ring } with hΦ
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro Jc hJc
    have hw : ∀ ν, ∑ σ, gi ν σ • Jc σ = 0 := by
      intro ν
      refine M.ipA_nondeg _ fun x => ?_
      have h := LinearMap.congr_fun hJc (Pi.single ν x)
      simp only [hΦ, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.zero_apply] at h
      have h' : ∑ ν', ∑ σ, gi ν' σ * M.ipA ((Pi.single ν x : Fin 4 → 𝔄) ν') (Jc σ) =
          ∑ σ, gi ν σ * M.ipA x (Jc σ) := by
        rw [Finset.sum_eq_single ν (fun b _ hb => by simp [Pi.single_eq_of_ne hb]) (by simp)]
        simp
      rw [h'] at h
      rw [map_sum]
      simp only [map_smul, smul_eq_mul]
      exact (mul_eq_zero.1 h).resolve_left hv
    funext μ
    have : Jc μ = ∑ ν, g μ ν • ∑ σ, gi ν σ • Jc σ := by
      simp only [Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp only [← Finset.sum_smul, hinv, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
        Finset.mem_univ, ite_true]
    rw [this]
    simp [hw]
  have hsurj : Function.Surjective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (Subspace.dual_finrank_eq).symm).1 hinj
  obtain ⟨Jc, hJc⟩ := hsurj c
  exact ⟨Jc, fun X => LinearMap.congr_fun hJc X⟩

end Gauge

/-! ### Vanishing of the bosonic matter rows -/

section BosonicVanishing

attribute [local instance 100] LieRing.ofAssociativeRing

variable {Y : R4 → Field 𝔄 𝓗 𝓢}

theorem volume_ne_zero_of_pos {E : Mat} (h : 0 < E.det) : volume E ≠ 0 := by
  rw [volume_of_det_pos h]; exact h.ne'

/-- The inverse metric of a coframe field is the inverse of `g`. -/
theorem gF_ginv (hdet : ∀ z, 0 < ((Y z).1).det) (z : R4) :
    ∀ a c, ∑ b, gF (eF Y) z a b * ginvOf (gF (eF Y) z) b c = if a = c then 1 else 0 :=
  gF_mul_ginvOf (e := eF Y) hdet z

/-- A gauge covector `X ↦ v g^{νσ}⟨X_ν, r_σ⟩` vanishes iff `r = 0`. -/
theorem gauge_covector_eq_zero_iff (g gi : Fin 4 → Fin 4 → ℝ)
    (hinv : ∀ a c, ∑ b, g a b * gi b c = if a = c then 1 else 0) {v : ℝ} (hv : v ≠ 0)
    (r : Fin 4 → 𝔄) :
    (∀ X : Fin 4 → 𝔄, v * ∑ ν, ∑ σ, gi ν σ * M.ipA (X ν) (r σ) = 0) ↔ r = 0 := by
  constructor
  · intro h
    have hw : ∀ ν, ∑ σ, gi ν σ • r σ = 0 := by
      intro ν
      refine M.ipA_nondeg _ fun x => ?_
      have h1 := h (Pi.single ν x)
      have h' : ∑ ν', ∑ σ, gi ν' σ * M.ipA ((Pi.single ν x : Fin 4 → 𝔄) ν') (r σ) =
          ∑ σ, gi ν σ * M.ipA x (r σ) := by
        rw [Finset.sum_eq_single ν (fun b _ hb => by simp [Pi.single_eq_of_ne hb]) (by simp)]
        simp
      rw [h'] at h1
      rw [map_sum]
      simp only [map_smul, smul_eq_mul]
      exact (mul_eq_zero.1 h1).resolve_left hv
    funext μ
    have : r μ = ∑ ν, g μ ν • ∑ σ, gi ν σ • r σ := by
      simp only [Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp only [← Finset.sum_smul, hinv, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq,
        Finset.mem_univ, ite_true]
    rw [this]
    simp [hw]
  · rintro rfl X
    simp

/-- **The gauge rows vanish iff the Yang–Mills equation holds**: with a current `J` representing
the matter current covector (`exists_current`), `𝓔₀(Y)(z)[(0, X, 0, 0, 0)] = 0` for all `X` iff
`r^A = ActualJetGauge.ymRes A ∂A ∂∂A g⁻¹ Γ J = 0`. -/
theorem ym_rows_vanish_iff (hY : ContDiff ℝ ∞ Y) (hdet : ∀ z, 0 < ((Y z).1).det) (z : R4)
    (Jc : Fin 4 → 𝔄)
    (hJ : ∀ X : Fin 4 → 𝔄, volume (Y z).1 * ∑ ν, ∑ σ, ginvOf (gF (eF Y) z) ν σ *
      M.ipA (X ν) (Jc σ) = -gaugeCur M.toData (jet1 Y z) X) :
    (∀ X : Fin 4 → 𝔄, contEuler (L0 M.toData) Y z (gaugeDir X) = 0) ↔
      ActualJetGauge.ymRes (Af Y z) (dAf Y z) (ddAf Y z) (ginvOf (gF (eF Y) z))
        (chr (ginvOf (gF (eF Y) z)) (dF (gF (eF Y)) z)) Jc = 0 := by
  simp only [ym_euler_row_ymRes M.toData M.ipA_symm M.ipA_inv hY hdet z Jc hJ]
  exact gauge_covector_eq_zero_iff M _ _ (gF_ginv hdet z) (volume_ne_zero_of_pos (hdet z)) _

/-- **The Higgs rows vanish iff the covariant wave equation holds**: with a source `S_H`
representing the potential and Yukawa covector,
`2v⟨η, S_H⟩ = v DV(H)[η] + v Re Ψ̄𝓜_𝐘(η)Ψ` for all `η`, the Higgs rows vanish for all `η` iff
`□_AH = S_H` (`waveN`). -/
theorem higgs_rows_vanish_iff (hY : ContDiff ℝ ∞ Y) (hA𝔤 : ∀ z μ, (Y z).2.1 μ ∈ M.gLie)
    (hdet : ∀ z, 0 < ((Y z).1).det) (z : R4) (SH : 𝓗)
    (hS : ∀ η : 𝓗, 2 * volume (Y z).1 * M.hermH η SH = volume (Y z).1 * potGrad M.toData
      (Y z).2.2.1 η + volume (Y z).1 * ((Y z).2.2.2.2 (M.yukawa η (Y z).2.2.2.1)).re) :
    (∀ η : 𝓗, contEuler (L0 M.toData) Y z (higgsDir η) = 0) ↔ waveN M.toData Y z = SH := by
  have hv : volume (Y z).1 ≠ 0 := volume_ne_zero_of_pos (hdet z)
  have hrow : ∀ η, contEuler (L0 M.toData) Y z (higgsDir η) =
      2 * volume (Y z).1 * M.hermH η (waveN M.toData Y z - SH) := by
    intro η
    rw [higgs_euler_row M.toData M.hermH_symm M.gLie M.rhoH_skew hY hA𝔤 hdet z η, map_sub,
      mul_sub, hS η]
    ring
  simp only [hrow]
  constructor
  · intro h
    rw [← sub_eq_zero]
    refine M.hermH_nondeg _ fun y => ?_
    have := h y
    rw [mul_eq_zero] at this
    exact this.resolve_left (mul_ne_zero two_ne_zero hv)
  · intro h η
    rw [h, sub_self, map_zero, mul_zero]

end BosonicVanishing

/-! ### The spinor rows: the dual Dirac residual -/

section DualDirac

variable {Y : R4 → Field 𝔄 𝓗 𝓢}

theorem J_sigmaOf (om : Mat) : M.J * sigmaOf M.γ om = sigmaOf M.γ om * M.J := by
  unfold sigmaOf
  rw [mul_smul_comm, smul_mul_assoc, Finset.mul_sum, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [mul_smul_comm, smul_mul_assoc]
  congr 1
  rw [← mul_assoc, M.J_gamma, mul_assoc, M.J_gamma, mul_assoc]

theorem J_gammaMu (μ : Fin 4) (E : Mat) :
    M.J * gammaMu M.toData μ E = gammaMu M.toData μ E * M.J := by
  rw [gammaMu_eq, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [mul_smul_comm, smul_mul_assoc, M.J_gamma]

theorem isCLin_comp {φ : CoSpinor 𝓢} (hφ : IsCLin M φ) {T : Spin 𝓢} (hT : M.J * T = T * M.J) :
    IsCLin M (φ.comp T) := fun x => by
  have : T (M.J x) = M.J (T x) := by
    rw [← ContinuousLinearMap.mul_apply, ← hT, ContinuousLinearMap.mul_apply]
  simp only [ContinuousLinearMap.comp_apply, this]
  exact hφ _

theorem isCLin_add {φ ψ : CoSpinor 𝓢} (hφ : IsCLin M φ) (hψ : IsCLin M ψ) : IsCLin M (φ + ψ) :=
  fun x => by simp only [ContinuousLinearMap.add_apply, hφ x, hψ x, mul_add]

/-- The defect operator `φ ↦ φ∘J - iφ` whose kernel is the physical co-spinors. -/
def clinDefect : CoSpinor 𝓢 →L[ℝ] CoSpinor 𝓢 :=
  (ContinuousLinearMap.compL ℝ 𝓢 𝓢 ℂ).flip M.J - Complex.I • ContinuousLinearMap.id ℝ _

theorem isCLin_iff_defect (φ : CoSpinor 𝓢) : IsCLin M φ ↔ clinDefect M φ = 0 := by
  constructor
  · intro h
    ext x
    simp [clinDefect, h x]
  · intro h x
    have := congrArg (fun ψ : CoSpinor 𝓢 => ψ x) h
    simp only [clinDefect, ContinuousLinearMap.sub_apply, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.zero_apply, smul_eq_mul] at this
    exact sub_eq_zero.1 this

/-- The derivative of a physical co-spinor field is physical. -/
theorem isCLin_pd (hY : Differentiable ℝ Y) (hΨb : ∀ y, IsCLin M ((Y y).2.2.2.2)) (z : R4)
    (μ : Fin 4) : IsCLin M (pd (fun y => (Y y).2.2.2.2) μ z) := by
  rw [isCLin_iff_defect]
  have hd : DifferentiableAt ℝ (fun y => (Y y).2.2.2.2) z :=
    ((psiBarL (𝔄 := 𝔄) (𝓗 := 𝓗) (𝓢 := 𝓢)).differentiableAt).comp z (hY z)
  rw [← pd_clm (clinDefect M) hd μ]
  have h0 : (fun y => clinDefect M ((Y y).2.2.2.2)) = fun _ => 0 :=
    funext fun y => (isCLin_iff_defect M _).1 (hΨb y)
  rw [h0]
  unfold SobolevOpen.pd
  simp

/-- **The native dual Dirac residual** `r̄_D = (∇_μΨ̄)c^μ + Ψ̄𝓜_𝐘(H)` (`c^μ = Jγ^μ(e)` acting on
the right), a co-spinor. -/
def diracResBar (Y : R4 → Field 𝔄 𝓗 𝓢) (z : R4) : CoSpinor 𝓢 :=
  ∑ μ, (DPsiBar M.toData (jet1 Y z) μ).comp (gammaMu M.toData μ (Y z).1 * M.J) +
    (Y z).2.2.2.2.comp (M.yukawa (Y z).2.2.1)

theorem isCLin_DPsiBar (hY : Differentiable ℝ Y) (hΨb : ∀ y, IsCLin M ((Y y).2.2.2.2)) (z : R4)
    (μ : Fin 4) : IsCLin M (DPsiBar M.toData (jet1 Y z) μ) := by
  unfold DPsiBar
  refine isCLin_add M (isCLin_comp M (hΨb z) ?_) ?_
  · rw [M.sigma_eq, mul_sub, sub_mul, mul_neg, neg_mul, M.J_rhoS, J_sigmaOf]
  · rw [jet1_psiBar hY]
    exact isCLin_pd M hY hΨb z μ

theorem isCLin_diracResBar (hY : Differentiable ℝ Y) (hΨb : ∀ y, IsCLin M ((Y y).2.2.2.2))
    (z : R4) : IsCLin M (diracResBar M Y z) := by
  unfold diracResBar
  refine isCLin_add M ?_ (isCLin_comp M (hΨb z) (M.J_yukawa _))
  have hsum : ∀ s : Finset (Fin 4), IsCLin M (∑ μ ∈ s, (DPsiBar M.toData (jet1 Y z) μ).comp
      (gammaMu M.toData μ (Y z).1 * M.J)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => intro x; simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      refine isCLin_add M (isCLin_comp M (isCLin_DPsiBar M hY hΨb z a) ?_) ih
      rw [← mul_assoc, J_gammaMu, mul_assoc]
  exact hsum _

/-- **The `Ψ`-row is `-v(e)` times the dual Dirac residual** for a physical co-spinor field:
`𝓔₀(Y)(z)[(0, 0, 0, χ, 0)] = -v(e) Re r̄_D(χ)`. -/
theorem psi_row_model (hY : ContDiff ℝ ∞ Y) (hdet : ∀ z, 0 < ((Y z).1).det)
    (hΨb : ∀ y, IsCLin M ((Y y).2.2.2.2)) (z : R4) (χ : 𝓢) :
    contEuler (L0 M.toData) Y z (psiDir χ) = -(volume (Y z).1 * (diracResBar M Y z χ).re) := by
  have hYd : Differentiable ℝ Y := hY.differentiable (by simp)
  rw [psi_euler_row M.toData M.cliff M.sigma_eq M.gauge_cliff hY hdet z χ]
  unfold diracResBar
  congr 3
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_sum', Finset.sum_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [← isCLin_DPsiBar M hYd hΨb z μ, ← ContinuousLinearMap.mul_apply, J_gammaMu,
    ContinuousLinearMap.mul_apply]

/-- **The `Ψ`-rows vanish iff the dual Dirac equation holds** (physical co-spinor field):
`(∀ χ, 𝓔₀(Y)(z)[(0, 0, 0, χ, 0)] = 0) ↔ (∇_μΨ̄)c^μ + Ψ̄𝓜_𝐘(H) = 0`. -/
theorem psi_rows_vanish_iff (hY : ContDiff ℝ ∞ Y) (hdet : ∀ z, 0 < ((Y z).1).det)
    (hΨb : ∀ y, IsCLin M ((Y y).2.2.2.2)) (z : R4) :
    (∀ χ : 𝓢, contEuler (L0 M.toData) Y z (psiDir χ) = 0) ↔ diracResBar M Y z = 0 := by
  have hYd : Differentiable ℝ Y := hY.differentiable (by simp)
  have hv : volume (Y z).1 ≠ 0 := volume_ne_zero_of_pos (hdet z)
  simp only [psi_row_model M hY hdet hΨb z, neg_eq_zero, mul_eq_zero, hv, false_or]
  constructor
  · intro h
    ext x
    have hR := isCLin_diracResBar M hYd hΨb z
    apply Complex.ext
    · simpa using h x
    · have h2 := h (M.J x)
      rw [hR x, Complex.mul_re, Complex.I_re, Complex.I_im] at h2
      simpa using h2
  · intro h χ
    rw [h]
    simp

end DualDirac

/-! ### Currents and sources of a native field; exact native critical points -/

section Sources

variable {Y : R4 → Field 𝔄 𝓗 𝓢}

theorem gaugeCur_eq (wp : FJ 𝔄 𝓗 𝓢) (X : Fin 4 → 𝔄) :
    gaugeCur M.toData wp X =
      -(volume wp.1.1 * ∑ μ, ∑ ν, ginv wp.1.1 μ ν *
        (M.hermH (M.ρH (X μ) wp.1.2.2.1) (KH M.toData wp ν) +
          M.hermH (KH M.toData wp μ) (M.ρH (X ν) wp.1.2.2.1))) +
      volume wp.1.1 * ∑ μ, (Complex.I / 2 * (wp.1.2.2.2.2 (gammaMu M.toData μ wp.1.1
        (M.ρS (X μ) wp.1.2.2.2.1)) + wp.1.2.2.2.2 (M.ρS (X μ)
          (gammaMu M.toData μ wp.1.1 wp.1.2.2.2.1)))).re := by
  unfold gaugeCur
  congr 2
  rw [Finset.mul_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply, map_neg,
    sub_neg_eq_add]

theorem re_half_smul (r : ℝ) (a b : ℂ) :
    (Complex.I / 2 * ((r : ℂ) * a + (r : ℂ) * b)).re = r * (Complex.I / 2 * (a + b)).re := by
  rw [show Complex.I / 2 * ((r : ℂ) * a + (r : ℂ) * b) = (r : ℂ) * (Complex.I / 2 * (a + b)) by
    ring, Complex.re_ofReal_mul]

/-- The matter current covector `X ↦ ∂_A(L_H + L_D)[X]` as a linear functional. -/
def gaugeCurL (wp : FJ 𝔄 𝓗 𝓢) : (Fin 4 → 𝔄) →ₗ[ℝ] ℝ where
  toFun X := gaugeCur M.toData wp X
  map_add' X X' := by
    simp only [gaugeCur_eq, Pi.add_apply, map_add, ContinuousLinearMap.add_apply, Complex.add_re,
      mul_add, Finset.sum_add_distrib]
    ring
  map_smul' r X := by
    simp only [gaugeCur_eq, Pi.smul_apply, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul,
      Complex.real_smul, RingHom.id_apply, re_half_smul]
    simp only [Finset.mul_sum, mul_add, mul_neg]
    ring_nf
    rw [neg_add_eq_sub]
    congr 1
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

/-- The Higgs source covector `η ↦ v DV(H)[η] + v Re Ψ̄𝓜_𝐘(η)Ψ` as a linear functional. -/
def higgsSrcL (E : Mat) (H : 𝓗) (Ψ : 𝓢) (Ψb : CoSpinor 𝓢) : 𝓗 →ₗ[ℝ] ℝ where
  toFun η := volume E * potGrad M.toData H η + volume E * (Ψb (M.yukawa η Ψ)).re
  map_add' η η' := by
    simp only [potGrad, map_add, ContinuousLinearMap.add_apply, Complex.add_re]
    ring
  map_smul' r η := by
    simp only [potGrad, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, RingHom.id_apply,
      Complex.real_smul, Complex.re_ofReal_mul]
    ring

variable [FiniteDimensional ℝ 𝓗]

/-- **The Higgs source of a native field**: `S_H` with
`2v⟨η, S_H⟩ = v DV(H)[η] + v Re Ψ̄𝓜_𝐘(η)Ψ` for all `η` (finite-dimensional Higgs space,
nondegenerate form). -/
theorem exists_higgs_source {v : ℝ} (hv : v ≠ 0) (c : 𝓗 →ₗ[ℝ] ℝ) :
    ∃ SH : 𝓗, ∀ η, 2 * v * M.hermH η SH = c η := by
  set Φ : 𝓗 →ₗ[ℝ] Module.Dual ℝ 𝓗 :=
    { toFun := fun S => (2 * v) • (M.hermH.flip S : 𝓗 →L[ℝ] ℝ).toLinearMap
      map_add' := fun S S' => by
        refine LinearMap.ext fun η => ?_
        simp
      map_smul' := fun r S => by
        refine LinearMap.ext fun η => ?_
        simp only [LinearMap.smul_apply, ContinuousLinearMap.coe_coe, map_smul,
          ContinuousLinearMap.smul_apply, ContinuousLinearMap.flip_apply, smul_eq_mul,
          RingHom.id_apply]
        ring } with hΦ
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro S hS
    refine M.hermH_nondeg S fun y => ?_
    have h := LinearMap.congr_fun hS y
    simp only [hΦ, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply,
      ContinuousLinearMap.coe_coe, ContinuousLinearMap.flip_apply, smul_eq_mul,
      LinearMap.zero_apply] at h
    exact (mul_eq_zero.1 h).resolve_left (mul_ne_zero two_ne_zero hv)
  have hsurj : Function.Surjective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (Subspace.dual_finrank_eq).symm).1 hinj
  obtain ⟨S, hS⟩ := hsurj c
  refine ⟨S, fun η => ?_⟩
  have h := LinearMap.congr_fun hS η
  simp only [hΦ, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply,
    ContinuousLinearMap.coe_coe, ContinuousLinearMap.flip_apply, smul_eq_mul] at h
  exact h

variable [FiniteDimensional ℝ 𝔄]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- **Exact native critical points solve the matter field equations** (bridge steps P1/P3,
matter sector): if the native continuum Euler covector vanishes at `z` in all gauge, Higgs,
spinor and physical co-spinor directions (in particular if `𝓔₀(Y)(z) = 0`), then at `z`
* the Yang–Mills equation `∇^μF_{μσ} + [A^μ, F_{μσ}] = J_σ` holds with the represented matter
  current (`ActualJetGauge.ymRes = 0`),
* the Higgs equation `□_AH = S_H` holds with the represented potential/Yukawa source,
* the Dirac equation `c^μ∇_μΨ = 𝓜_𝐘(H)Ψ` and the dual Dirac equation
  `(∇_μΨ̄)c^μ + Ψ̄𝓜_𝐘(H) = 0` hold (`c^μ = Jγ^μ(e)`). -/
theorem matter_equations (hY : ContDiff ℝ ∞ Y) (hA𝔤 : ∀ z μ, (Y z).2.1 μ ∈ M.gLie)
    (hdet : ∀ z, 0 < ((Y z).1).det) (hΨb : ∀ y, IsCLin M ((Y y).2.2.2.2)) (z : R4)
    (hcrit : ∀ w : Field 𝔄 𝓗 𝓢, contEuler (L0 M.toData) Y z w = 0) :
    (∃ Jc : Fin 4 → 𝔄, (∀ X : Fin 4 → 𝔄, volume (Y z).1 * ∑ ν, ∑ σ,
        ginvOf (gF (eF Y) z) ν σ * M.ipA (X ν) (Jc σ) = -gaugeCur M.toData (jet1 Y z) X) ∧
      ActualJetGauge.ymRes (Af Y z) (dAf Y z) (ddAf Y z) (ginvOf (gF (eF Y) z))
        (chr (ginvOf (gF (eF Y) z)) (dF (gF (eF Y)) z)) Jc = 0) ∧
    (∃ SH : 𝓗, (∀ η, 2 * volume (Y z).1 * M.hermH η SH = volume (Y z).1 * potGrad M.toData
        (Y z).2.2.1 η + volume (Y z).1 * ((Y z).2.2.2.2 (M.yukawa η (Y z).2.2.2.1)).re) ∧
      waveN M.toData Y z = SH) ∧
    diracRes M Y z = 0 ∧ diracResBar M Y z = 0 := by
  have hv : volume (Y z).1 ≠ 0 := volume_ne_zero_of_pos (hdet z)
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨Jc, hJc⟩ := exists_current M (gF (eF Y) z) (ginvOf (gF (eF Y) z)) (gF_ginv hdet z)
      hv (-gaugeCurL M (jet1 Y z))
    exact ⟨Jc, hJc, (ym_rows_vanish_iff M hY hdet z Jc hJc).1 fun X => hcrit _⟩
  · obtain ⟨SH, hSH⟩ := exists_higgs_source M hv
      (higgsSrcL M (Y z).1 (Y z).2.2.1 (Y z).2.2.2.1 (Y z).2.2.2.2)
    have hS : ∀ η, 2 * volume (Y z).1 * M.hermH η SH = volume (Y z).1 * potGrad M.toData
        (Y z).2.2.1 η + volume (Y z).1 * ((Y z).2.2.2.2 (M.yukawa η (Y z).2.2.2.1)).re :=
      fun η => hSH η
    exact ⟨SH, hS, (higgs_rows_vanish_iff M hY hA𝔤 hdet z SH hS).1 fun η => hcrit _⟩
  · exact (psibar_rows_vanish_iff M hY hdet z).1 fun φ _ => hcrit _
  · exact (psi_rows_vanish_iff M hY hdet hΨb z).1 fun χ => hcrit _

end Sources

end

end NativeModel

end RenewalGeometry
