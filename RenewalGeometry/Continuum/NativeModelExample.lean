/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.NativeModelMap

/-!
# A concrete native model and the flat vacuum (non-vacuity of the matter-row theorems)

Einstein–Standard-Model action-closure manuscript, bridge step P1 of `thm:native-closure`.

The hypothesis packet of `NativeModel.Model` is satisfiable: `diracModel` is a native model with
spinor space `ℂ⁴` (as a real space, complex structure `J = i`), the Dirac matrices
`γ^0 = iσ_2 ⊗ 1`, `γ^k = σ_1 ⊗ σ_k` (`γ^aγ^b + γ^bγ^a = 2η^{ab}`, `η = diag(-1, 1, 1, 1)`,
checked entrywise), `σ(ω) = ¼ω_{ab}γ^aγ^b`, the trivial gauge algebra `ℝ` acting by scalars,
real Higgs line, invariant forms given by multiplication.  On the flat vacuum
(`e = 1`, `A = H = Ψ = Ψ̄ = 0`) all four families of matter rows vanish, through the
`…_rows_vanish_iff` theorems of `NativeModelMap` with every hypothesis discharged.
-/

namespace RenewalGeometry

namespace NativeModelExample

open NativeModel NativeDiracEuler NativeBosonicEuler NativeDensity NativeMatterEuler
open NativeScaling (Mat eta)
open DiscreteEulerConsistency (R4 jet1 contEuler)
open Matrix
open scoped ContDiff

noncomputable section

set_option linter.unusedSectionVars false

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/-- The spinor space `ℂ² ⊗ ℂ² = ℂ⁴`. -/
abbrev Sp := Fin 2 × Fin 2 → ℂ

/-- The index type of `ℂ² ⊗ ℂ²`. -/
abbrev I4 := Fin 2 × Fin 2

/-- Complex `4 × 4` matrices as real operators on `ℂ⁴`. -/
def toSpin (A : Matrix I4 I4 ℂ) : Spin Sp :=
  ((Matrix.toLin' A).restrictScalars ℝ).toContinuousLinearMap

theorem toSpin_apply (A : Matrix I4 I4 ℂ) (v : Sp) : toSpin A v = A.mulVec v := rfl

theorem toSpin_mul (A B : Matrix I4 I4 ℂ) : toSpin (A * B) = toSpin A * toSpin B := by
  ext v : 1
  simp [toSpin_apply, Matrix.mulVec_mulVec]

theorem toSpin_add (A B : Matrix I4 I4 ℂ) : toSpin (A + B) = toSpin A + toSpin B := by
  ext v : 1
  simp [toSpin_apply, Matrix.add_mulVec]

theorem toSpin_real_smul_one (c : ℝ) : toSpin ((c : ℂ) • (1 : Matrix I4 I4 ℂ)) =
    c • (1 : Spin Sp) := by
  ext v i
  simp [toSpin_apply, Matrix.smul_mulVec, Complex.real_smul]

/-- The left factors `iσ_2, σ_1, σ_1, σ_1`. -/
def Am : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![!![0, 1; -1, 0], !![0, 1; 1, 0], !![0, 1; 1, 0], !![0, 1; 1, 0]]

/-- The right factors `1, σ_1, σ_2, σ_3`. -/
def Bm : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![!![1, 0; 0, 1], !![0, 1; 1, 0], !![0, -Complex.I; Complex.I, 0], !![1, 0; 0, -1]]

/-- The Dirac matrices `γ^a = A_a ⊗ B_a`: `γ^0 = iσ_2 ⊗ 1`, `γ^k = σ_1 ⊗ σ_k`. -/
def Γ (a : Fin 4) : Matrix I4 I4 ℂ := Matrix.kroneckerMap (· * ·) (Am a) (Bm a)

set_option maxHeartbeats 2000000 in
/-- **The Clifford relations** `γ^aγ^b + γ^bγ^a = 2η^{ab}` for the Dirac matrices. -/
theorem Γ_cliff (a b : Fin 4) :
    Γ a * Γ b + Γ b * Γ a = ((2 * eta a b : ℝ) : ℂ) • (1 : Matrix I4 I4 ℂ) := by
  unfold Γ
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  fin_cases a <;> fin_cases b <;>
  · ext ⟨i, j⟩ ⟨k, l⟩
    simp only [Am, Bm, Matrix.add_apply,
      Matrix.kroneckerMap_apply, Matrix.smul_apply, Matrix.one_apply, Prod.mk.injEq, eta,
      Matrix.diagonal_apply, smul_eq_mul]
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      simp <;> ring_nf

/-- The gamma matrices as operators on the spinor space. -/
def γS (a : Fin 4) : Spin Sp := toSpin (Γ a)

theorem γS_cliff (a b : Fin 4) : γS a * γS b + γS b * γS a = (2 * eta a b) • (1 : Spin Sp) := by
  unfold γS
  rw [← toSpin_mul, ← toSpin_mul, ← toSpin_add, Γ_cliff, toSpin_real_smul_one]

/-- `σ` as a continuous linear map `Mat → Spin`. -/
def sigmaL : Mat →L[ℝ] Spin Sp :=
  LinearMap.toContinuousLinearMap
    { toFun := fun om => sigmaOf γS om
      map_add' := fun om om' => by
        unfold sigmaOf
        rw [← smul_add, ← Finset.sum_add_distrib]
        congr 1
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [← add_smul]
        congr 1
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [Matrix.add_apply, mul_add]
      map_smul' := fun r om => by
        unfold sigmaOf
        simp only [RingHom.id_apply, Finset.smul_sum, smul_smul]
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
        congr 1
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [Matrix.smul_apply, smul_eq_mul]
        ring }

/-- The complex structure `J = i` of `ℂ⁴`. -/
def JS : Spin Sp := toSpin (Complex.I • (1 : Matrix I4 I4 ℂ))

theorem JS_comm (A : Matrix I4 I4 ℂ) : JS * toSpin A = toSpin A * JS := by
  unfold JS
  rw [← toSpin_mul, ← toSpin_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one]

theorem JS_sq : JS * JS = -1 := by
  unfold JS
  rw [← toSpin_mul, smul_mul_smul_comm, Matrix.one_mul, Complex.I_mul_I]
  have h := toSpin_real_smul_one (-1)
  push_cast at h
  rw [h, neg_one_smul]

theorem continuous_algHom_real {B : Type*} [NormedRing B] [NormedAlgebra ℝ B]
    (f : ℝ →ₐ[ℝ] B) : Continuous f :=
  f.toLinearMap.continuous_of_finiteDimensional

/-- **A concrete native model**: trivial gauge algebra `ℝ`, real Higgs line, spinor space `ℂ⁴`
with the Dirac matrices and `J = i`. -/
def diracModel : Model ℝ ℝ Sp where
  κ := 1
  Λ := 0
  lamH := 0
  vH := 0
  ipA := ContinuousLinearMap.mul ℝ ℝ
  hermH := ContinuousLinearMap.mul ℝ ℝ
  ρH := Algebra.ofId ℝ (ℝ →L[ℝ] ℝ)
  ρH_cont := continuous_algHom_real _
  ρS := Algebra.ofId ℝ (Spin Sp)
  ρS_cont := continuous_algHom_real _
  σ := sigmaL
  γ := γS
  yukawa := 0
  ipA_symm x y := by simp [mul_comm]
  ipA_inv a x y := by simp [mul_comm]
  ipA_nondeg x h := by simpa using h 1
  hermH_symm x y := by simp [mul_comm]
  hermH_nondeg x h := by simpa using h 1
  gLie := {0}
  rhoH_skew a ha x y := by
    rw [Set.mem_singleton_iff] at ha
    subst ha
    simp
  cliff := γS_cliff
  sigma_eq om := rfl
  gauge_cliff A a := Algebra.commutes A (γS a)
  J := JS
  J_sq := JS_sq
  J_gamma a := JS_comm (Γ a)
  J_rhoS A := (Algebra.commutes A JS).symm
  J_yukawa H := by simp

/-! ### The flat vacuum -/

/-- The flat vacuum `e = 1`, `A = H = Ψ = Ψ̄ = 0`. -/
def flat : R4 → Field ℝ ℝ Sp := fun _ => ((1 : Mat), 0)

theorem flat_smooth : ContDiff ℝ ∞ flat := contDiff_const

theorem flat_det : ∀ z, 0 < ((flat z).1).det := fun z => by simp [flat]

theorem jet1_flat (z : R4) : jet1 flat z = (((1 : Mat), 0), 0) := by
  unfold jet1 flat
  simp
  rfl

/-- On the flat vacuum the native Dirac residual vanishes. -/
theorem diracRes_flat (z : R4) : diracRes diracModel flat z = 0 := by
  unfold diracRes DPsi
  rw [jet1_flat]
  simp [flat, diracModel]

/-- **Non-vacuity of the co-spinor rows**: on the flat vacuum of the concrete model every
physical co-spinor row vanishes (`psibar_rows_vanish_iff`, all hypotheses discharged). -/
theorem flat_psibar_rows (z : R4) (φ : CoSpinor Sp) (hφ : IsCLin diracModel φ) :
    contEuler (L0 diracModel.toData) flat z (psiBarDir φ) = 0 :=
  (psibar_rows_vanish_iff diracModel flat_smooth flat_det z).2 (diracRes_flat z) φ hφ

theorem flat_clin (y : R4) : IsCLin diracModel ((flat y).2.2.2.2) := fun x => by simp [flat]

/-- On the flat vacuum the native dual Dirac residual vanishes. -/
theorem diracResBar_flat (z : R4) : diracResBar diracModel flat z = 0 := by
  unfold diracResBar DPsiBar
  rw [jet1_flat]
  ext x
  simp [flat, diracModel]

/-- **Non-vacuity of the spinor rows** (`psi_rows_vanish_iff`). -/
theorem flat_psi_rows (z : R4) (χ : Sp) :
    contEuler (L0 diracModel.toData) flat z (psiDir χ) = 0 :=
  (psi_rows_vanish_iff diracModel flat_smooth flat_det flat_clin z).2 (diracResBar_flat z) χ

attribute [local instance 100] LieRing.ofAssociativeRing

theorem pd_const_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Fin 4) (z : R4) :
    SobolevOpen.pd (fun _ : R4 => (0 : E)) μ z = 0 := by
  unfold SobolevOpen.pd; simp

theorem Af_flat (y : R4) : Af flat y = 0 := by funext μ; simp [Af, flat]

theorem dAf_flat (y : R4) : dAf flat y = 0 := by
  funext γ μ
  unfold dAf
  simp only [Af_flat, Pi.zero_apply]
  exact pd_const_zero γ y

theorem ddAf_flat (y : R4) : ddAf flat y = 0 := by
  funext α γ μ
  unfold ddAf
  simp only [dAf_flat, Pi.zero_apply]
  exact pd_const_zero α y

theorem gaugeCur_flat (z : R4) (X : Fin 4 → ℝ) :
    gaugeCur diracModel.toData (jet1 flat z) X = 0 := by
  rw [jet1_flat]
  simp [gaugeCur, KH, flat, diracModel]

/-- **Non-vacuity of the gauge rows** (`ym_rows_vanish_iff`, all hypotheses discharged, zero
current). -/
theorem flat_ym_rows (z : R4) (X : Fin 4 → ℝ) :
    contEuler (L0 diracModel.toData) flat z (gaugeDir X) = 0 := by
  refine (ym_rows_vanish_iff diracModel flat_smooth flat_det z 0 (fun X => ?_)).2 ?_ X
  · rw [gaugeCur_flat]; simp
  · rw [Af_flat, dAf_flat, ddAf_flat]
    funext σ
    simp [ActualJetGauge.ymRes, ActualJetGauge.ymDiv, ActualJetGauge.dFm, ActualJetGauge.Fm,
      ActualJetWriter.fieldStrength]

theorem Kf_flat (y : R4) (μ : Fin 4) : Kf diracModel.toData flat y μ = 0 := by
  unfold Kf KH
  rw [jet1_flat]
  simp [diracModel]

theorem waveN_flat (z : R4) : waveN diracModel.toData flat z = 0 := by
  unfold waveN
  have h : ∀ μ, (fun y => Kf diracModel.toData flat y μ) = fun _ => (0 : ℝ) := fun μ =>
    funext fun y => Kf_flat y μ
  simp only [h, pd_const_zero, Kf_flat, map_zero, smul_zero, sub_zero, add_zero,
    Finset.sum_const_zero]

/-- **Non-vacuity of the Higgs rows** (`higgs_rows_vanish_iff`, all hypotheses discharged, zero
source). -/
theorem flat_higgs_rows (z : R4) (η : ℝ) :
    contEuler (L0 diracModel.toData) flat z (higgsDir η) = 0 := by
  refine (higgs_rows_vanish_iff diracModel flat_smooth (fun z μ => by simp [flat, diracModel])
    flat_det z 0 (fun η => ?_)).2 (waveN_flat z) η
  simp [potGrad, flat, diracModel]

end

end NativeModelExample

end RenewalGeometry
