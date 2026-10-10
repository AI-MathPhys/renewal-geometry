/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.NativeStressEulerRow

/-!
# The native frame and the slab frame (bridge step P2 of `thm:native-closure`)

Einstein–Standard-Model action-closure manuscript, bridge step P2 of `thm:native-closure`: the
native Euler rows live in the native coframe `e` (spinors in the frame `e_a = (e⁻¹)^·_a`), the
slab model of `prop:coupled-bootstrap` in the algebraic adapted frame `frU(g⁻¹)` of the metric
`g = eᵀηe` (`AdaptedFrameOfMetric.frU`: lapse/shift/Cholesky, an upper-triangular frame with
positive diagonal).

**Obstruction (disclosed).** For a general coframe the pointwise Lorentz map
`L(x) = (frame of e)⁻¹ · frU(g(x)⁻¹)` takes values in `SO(1,3)`, and a periodic spin lift
`x ↦ S(L(x))` need not exist: e.g. a coframe rotated by the angle `x¹` about a spatial axis gives
a loop in `SO(3)` with nontrivial class in `π₁`, whose lift changes sign around the period.  The
lift also fails off the identity component (time-reversed coframes).  We therefore use the
**adapted Lorentz gauge**: the record coframes are lower triangular with positive diagonal
(`IsAdaptedCoframe`).  This is a *linear* pointwise gauge condition on the nodal values (plus the
chart positivity), hence it is preserved by the trigonometric reconstruction, and in this gauge
the two frames coincide, so the spin lift is the identity.

## Results

* `upper_unique` — **Lorentz–Cholesky uniqueness**: two upper-triangular `4 × 4` matrices with
  positive diagonal and the same `Fᵀ η F` are equal;
* `frU_upper`, `frU_diag_pos`, `frU_metric` — `frU(g⁻¹)` is upper triangular with positive
  diagonal and `frUᵀ η frU = g⁻¹`;
* **`frU_eq_of_adapted`** — in the adapted Lorentz gauge `frU(g⁻¹)_A{}^μ = (e⁻¹)^μ_A`: the
  native frame *is* the slab frame;
* `slabCliff` — the Clifford frame `c_a = ε_a Jγ^a` of a native model, in the convention of the
  actual-jet system (`c_ac_b + c_bc_a = -2ε_aδ_{ab}`, Lorentzian); with it the slab Dirac operator
  `Σ_b ε_b c_b X_b` is `Jγ^b X_b` (`slab_dirac_eq`) — note that the Clifford datum
  `NativeModel.cliffordFrame` (`c_a = Jγ^a`, no sign) of the previous pass gives the operator
  `Jγ_b X_b` instead, so `slabCliff` is the correct datum for `ActualJetSystem.DiracData`;
* **`spinPart_slabCliff`** — `¼Σ ε_cε_d W_{cd} c_cc_d = σ(-ηW)`: the slab spin connection of a
  frame-connection array `G_{acd}` is the native `σ(ω_a)` iff `(ηω_a)_{cd} = -G_{acd}`;
* **`Gfun_eq_readerOmega`** — the slab frame connection coefficients
  `G_{ABC} = ⟨∇_{e_A}e_B, e_C⟩` (`ActualJetSystem.Gfun`) of the frame `e⁻ᵀ` with the frame jets
  `∂(e⁻ᵀ) = -(e⁻¹∂e e⁻¹)ᵀ` are `-(ηΩ_A)_{BC}` with the native reader connection
  `Ω_A = e_A{}^γ Ω_γ(e, ∂e)` (any coframe, no gauge condition needed);
* **`slab_cov_eq_native`**, **`slab_resD_eq_native`** — consequently the slab covariant
  derivatives `X_B = e_B{}^γ∂_γΨ + ω_BΨ` and the slab Dirac residual
  `Σ_b ε_b c_b X_b - 𝓜(H)Ψ` (`SpinorProlongation.resD`) are the native ones,
  `X_B = e_B{}^γ∇_γΨ`, `r_D = Jγ^μ∇_μΨ - 𝓜_𝐘(H)Ψ` (`NativeModel.diracRes`).
-/

namespace RenewalGeometry

namespace NativeFrameBridge

open Finset HarmonicDefect PalatiniEuler NativeDiracEuler NativeBosonicEuler NativeStressEuler
open NativeScaling (Mat eta metric readerOmega readerG readerGamma)
open NativeDensity NativeModel
open ActualJetWriter (AdaptedFrame)
open ActualJetFrame
open scoped Matrix

noncomputable section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 2048
set_option synthInstance.maxHeartbeats 400000

/-! ### Lorentz–Cholesky uniqueness -/

theorem eta_mul_apply (F : Mat) (i j : Fin 4) :
    (Fᵀ * eta * F) i j = -(F 0 i * F 0 j) + F 1 i * F 1 j + F 2 i * F 2 j + F 3 i * F 3 j := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, eta, Matrix.diagonal_apply,
    Fin.sum_univ_four]
  simp

/-- **Lorentz–Cholesky uniqueness**: upper-triangular matrices with positive diagonal are
determined by `Fᵀ η F`. -/
theorem upper_unique {F F' : Mat} (hF : ∀ i j : Fin 4, j < i → F i j = 0)
    (hF' : ∀ i j : Fin 4, j < i → F' i j = 0) (hd : ∀ i, 0 < F i i) (hd' : ∀ i, 0 < F' i i)
    (h : Fᵀ * eta * F = F'ᵀ * eta * F') : F = F' := by
  have E : ∀ i j, (Fᵀ * eta * F) i j = (F'ᵀ * eta * F') i j := fun i j => by rw [h]
  have z := fun i j (hij : j < i) => hF i j hij
  have z' := fun i j (hij : j < i) => hF' i j hij
  have z10 := z 1 0 (by decide); have z20 := z 2 0 (by decide); have z30 := z 3 0 (by decide)
  have z21 := z 2 1 (by decide); have z31 := z 3 1 (by decide); have z32 := z 3 2 (by decide)
  have y10 := z' 1 0 (by decide); have y20 := z' 2 0 (by decide); have y30 := z' 3 0 (by decide)
  have y21 := z' 2 1 (by decide); have y31 := z' 3 1 (by decide); have y32 := z' 3 2 (by decide)
  simp only [eta_mul_apply] at E
  have e00 := E 0 0; have e01 := E 0 1; have e02 := E 0 2; have e03 := E 0 3
  have e11 := E 1 1; have e12 := E 1 2; have e13 := E 1 3
  have e22 := E 2 2; have e23 := E 2 3; have e33 := E 3 3
  simp only [z10, z20, z30, z21, z31, z32, y10, y20, y30, y21, y31, y32, mul_zero, zero_mul,
    add_zero] at e00 e01 e02 e03 e11 e12 e13 e22 e23 e33
  have p0 := hd 0; have q0 := hd' 0; have p1 := hd 1; have q1 := hd' 1
  have p2 := hd 2; have q2 := hd' 2; have p3 := hd 3; have q3 := hd' 3
  have a00 : F 0 0 = F' 0 0 := (sq_eq_sq₀ p0.le q0.le).1 (by linear_combination -e00)
  rw [a00] at e01 e02 e03
  have a01 : F 0 1 = F' 0 1 := mul_left_cancel₀ q0.ne' (by linear_combination -e01)
  have a02 : F 0 2 = F' 0 2 := mul_left_cancel₀ q0.ne' (by linear_combination -e02)
  have a03 : F 0 3 = F' 0 3 := mul_left_cancel₀ q0.ne' (by linear_combination -e03)
  rw [a01] at e11
  have a11 : F 1 1 = F' 1 1 := (sq_eq_sq₀ p1.le q1.le).1 (by linear_combination e11)
  rw [a01, a02, a11] at e12
  rw [a01, a03, a11] at e13
  have a12 : F 1 2 = F' 1 2 := mul_left_cancel₀ q1.ne' (by linear_combination e12)
  have a13 : F 1 3 = F' 1 3 := mul_left_cancel₀ q1.ne' (by linear_combination e13)
  rw [a02, a12] at e22
  have a22 : F 2 2 = F' 2 2 := (sq_eq_sq₀ p2.le q2.le).1 (by linear_combination e22)
  rw [a02, a03, a12, a13, a22] at e23
  have a23 : F 2 3 = F' 2 3 := mul_left_cancel₀ q2.ne' (by linear_combination e23)
  rw [a03, a13, a23] at e33
  have a33 : F 3 3 = F' 3 3 := (sq_eq_sq₀ p3.le q3.le).1 (by linear_combination e33)
  ext i j
  fin_cases i <;> fin_cases j
  · exact a00
  · exact a01
  · exact a02
  · exact a03
  · exact z10.trans y10.symm
  · exact a11
  · exact a12
  · exact a13
  · exact z20.trans y20.symm
  · exact z21.trans y21.symm
  · exact a22
  · exact a23
  · exact z30.trans y30.symm
  · exact z31.trans y31.symm
  · exact z32.trans y32.symm
  · exact a33

/-! ### The adapted frame of the metric -/

open ActualJetSystem (lorentzSign)

theorem frU_upper (gi : Fin 4 → Fin 4 → ℝ) (A μ : Fin 4) (h : μ < A) : frU gi A μ = 0 := by
  fin_cases A <;> fin_cases μ <;> simp_all [frU, Lmat] <;> rfl

theorem frU_diag_pos {gi : Fin 4 → Fin 4 → ℝ} (h : IsLorChart gi) (A : Fin 4) : 0 < frU gi A A := by
  have h0 := inv_pos.2 (lapse_pos h)
  have h1 := L00_pos h
  have h2 := L11_pos h
  have h3 : 0 < L22 gi := Real.sqrt_pos.mpr h.2.2.2
  have h4 := lapse_pos h
  fin_cases A <;> simpa [frU, Lmat] using ‹_›

theorem frU_metric {gi : Fin 4 → Fin 4 → ℝ} (hs : ∀ μ ν, gi μ ν = gi ν μ) (h : IsLorChart gi) :
    (Matrix.of (frU gi))ᵀ * eta * Matrix.of (frU gi) = Matrix.of gi := by
  ext μ ν
  rw [eta_mul_apply]
  have ha := frameOf_adapted hs h μ ν
  simp only [Fin.sum_univ_three] at ha
  simp only [Matrix.of_apply]
  rw [ha]
  simp only [← frU_eq h]
  rw [show (Fin.succ (0 : Fin 3) : Fin 4) = 1 from rfl, show (Fin.succ (1 : Fin 3) : Fin 4) = 2 from rfl,
    show (Fin.succ (2 : Fin 3) : Fin 4) = 3 from rfl]
  ring

/-- **The adapted Lorentz gauge**: a lower-triangular coframe with positive diagonal (a linear
pointwise gauge condition on the coframe values, plus the chart positivity). -/
def IsAdaptedCoframe (e : Mat) : Prop := (∀ a μ : Fin 4, a < μ → e a μ = 0) ∧ ∀ a, 0 < e a a

theorem inv_transpose_upper {e : Mat} (he : IsAdaptedCoframe e) (hdet : e.det ≠ 0) :
    (∀ i j : Fin 4, j < i → (e⁻¹)ᵀ i j = 0) ∧ ∀ i, 0 < (e⁻¹)ᵀ i i := by
  have hU : Matrix.BlockTriangular eᵀ id := fun i j hij => by
    rw [Matrix.transpose_apply]; exact he.1 j i hij
  have : Invertible eᵀ := Matrix.invertibleOfIsUnitDet _ (by rw [Matrix.det_transpose]; exact hdet.isUnit)
  have hUi : Matrix.BlockTriangular (eᵀ)⁻¹ id := Matrix.blockTriangular_inv_of_blockTriangular hU
  rw [← Matrix.transpose_nonsing_inv] at hUi
  refine ⟨fun i j hij => hUi hij, fun i => ?_⟩
  have h1 : (e⁻¹ * e) i i = 1 := by rw [Matrix.nonsing_inv_mul e hdet.isUnit, Matrix.one_apply_eq]
  rw [Matrix.mul_apply, Finset.sum_eq_single i] at h1
  · rw [Matrix.transpose_apply]
    have hii := he.2 i
    by_contra hneg
    rw [not_lt] at hneg
    nlinarith
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with hlt | hgt
    · rw [he.1 k i hlt]; ring
    · have : (e⁻¹)ᵀ k i = 0 := hUi hgt
      rw [Matrix.transpose_apply] at this
      rw [this]; ring
  · simp

/-- **In the adapted Lorentz gauge the native frame is the slab frame**:
`frU(g⁻¹)_A{}^μ = (e⁻¹)^μ_A` for `g = eᵀηe`. -/
theorem frU_eq_of_adapted {e : Mat} (he : IsAdaptedCoframe e) (hdet : e.det ≠ 0)
    (hchart : IsLorChart (fun a b => (metric e)⁻¹ a b)) (A μ : Fin 4) :
    frU (fun a b => (metric e)⁻¹ a b) A μ = e⁻¹ μ A := by
  have hs : ∀ μ ν, (fun a b => (metric e)⁻¹ a b) μ ν = (fun a b => (metric e)⁻¹ a b) ν μ :=
    fun μ ν => NativeBosonicEuler.ginv_symm' e μ ν
  obtain ⟨hup, hpos⟩ := inv_transpose_upper he hdet
  have h := upper_unique (F := Matrix.of (frU fun a b => (metric e)⁻¹ a b)) (F' := (e⁻¹)ᵀ)
    (fun i j hij => frU_upper _ i j hij) hup (fun i => frU_diag_pos hchart i) hpos (by
      rw [frU_metric hs hchart, Matrix.transpose_transpose, ← metric_inv_eq e hdet]
      rfl)
  have := congrFun (congrFun h A) μ
  simpa using this

/-! ### Non-vacuity -/

theorem metric_one_inv : (metric (1 : Mat))⁻¹ = eta := by
  have h1 : metric (1 : Mat) = eta := by simp [metric]
  rw [h1]
  exact Matrix.inv_eq_left_inv PalatiniEuler.eta_mul_eta

theorem isLorChart_eta : IsLorChart (fun a b => eta a b) := by
  have e00 : eta 0 0 = -1 := by simp [eta]
  have h0 : hInv (fun a b => eta a b) 0 0 = 1 := by simp [hInv, eta]
  have h10 : hInv (fun a b => eta a b) 1 0 = 0 := by simp [hInv, eta]
  have h11 : hInv (fun a b => eta a b) 1 1 = 1 := by simp [hInv, eta]
  have h20 : hInv (fun a b => eta a b) 2 0 = 0 := by simp [hInv, eta]
  have h21 : hInv (fun a b => eta a b) 2 1 = 0 := by simp [hInv, eta]
  have h22 : hInv (fun a b => eta a b) 2 2 = 1 := by simp [hInv, eta]
  have hL00 : L00 (fun a b => eta a b) = 1 := by simp [L00, h0]
  have hL10 : L10 (fun a b => eta a b) = 0 := by simp [L10, h10]
  have hL20 : L20 (fun a b => eta a b) = 0 := by simp [L20, h20]
  have hL11 : L11 (fun a b => eta a b) = 1 := by simp [L11, h11, hL10]
  have hL21 : L21 (fun a b => eta a b) = 0 := by simp [L21, h21, hL20]
  refine ⟨by simp only [e00]; norm_num, by rw [h0]; norm_num, by rw [h11, hL10]; norm_num,
    by rw [h22, hL20, hL21]; norm_num⟩

/-- Non-vacuity of `frU_eq_of_adapted`: the flat coframe `e = 1` is adapted, its metric is in the
Lorentzian chart, and its frame is the slab frame `frU(η)`. -/
theorem frU_flat (A μ : Fin 4) :
    frU (fun a b => (metric (1 : Mat))⁻¹ a b) A μ = (1 : Mat)⁻¹ μ A :=
  frU_eq_of_adapted ⟨fun a μ h => by simp [h.ne], fun a => by simp⟩
    (by simp) (by rw [metric_one_inv]; exact isLorChart_eta) A μ

/-! ### The Clifford frame of the slab model -/

section Cliff

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
variable (M : Model 𝔄 𝓗 𝓢)

theorem lorentzSign_sq (a : Fin 4) : lorentzSign a * lorentzSign a = 1 := by
  unfold lorentzSign; split_ifs <;> norm_num

theorem eta_eq_sign (a b : Fin 4) : eta a b = if a = b then lorentzSign a else 0 :=
  NativeModel.eta_eq_ite a b

/-- **The slab Clifford frame** `c_a = ε_a Jγ^a` (lower-index Clifford generators). -/
def slabCliff : TwistedHalfRicci.CliffordFrame (Fin 4) (Spin 𝓢) where
  c a := lorentzSign a • (M.J * M.γ a)
  ε := lorentzSign
  sign_sq a := by rw [sq, lorentzSign_sq]
  anticomm a b := by
    have h := (cliffordFrame M).anticomm a b
    simp only [cliffordFrame] at h
    rw [smul_mul_smul_comm, smul_mul_smul_comm, mul_comm (lorentzSign b) (lorentzSign a),
      ← smul_add, h, smul_smul]
    congr 1
    split_ifs with hab
    · subst hab; rw [← mul_assoc, lorentzSign_sq, one_mul]
    · ring

theorem slabCliff_lorentzian : ActualJetWriter.IsLorentzian (slabCliff M) :=
  ⟨by simp [slabCliff, lorentzSign], fun a => by simp [slabCliff, lorentzSign, Fin.succ_ne_zero]⟩

theorem slabCliff_c (a : Fin 4) : (slabCliff M).c a = lorentzSign a • (M.J * M.γ a) := rfl

theorem slabCliff_ε : (slabCliff M).ε = lorentzSign := rfl

/-- **The slab spin part is the native spin representation**: `¼Σ ε_cε_d W_{cd}c_cc_d = σ(-ηW)`. -/
theorem spinPart_slabCliff (W : Fin 4 → Fin 4 → ℝ) :
    SpinorProlongation.spinPart (slabCliff M) W = M.σ (-(eta * Matrix.of W)) := by
  rw [M.sigma_eq]
  unfold SpinorProlongation.spinPart sigmaOf
  congr 1
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
  have hJ : M.J * M.γ c * (M.J * M.γ d) = -(M.γ c * M.γ d) := by
    calc M.J * M.γ c * (M.J * M.γ d) = M.J * (M.γ c * M.J) * M.γ d := by noncomm_ring
      _ = M.J * (M.J * M.γ c) * M.γ d := by rw [M.J_gamma c]
      _ = (M.J * M.J) * (M.γ c * M.γ d) := by noncomm_ring
      _ = -(M.γ c * M.γ d) := by rw [M.J_sq]; noncomm_ring
  have hW : ∑ e, eta c e * (-(eta * Matrix.of W)) e d = -W c d := by
    have : (eta * (-(eta * Matrix.of W))) c d = -W c d := by
      rw [Matrix.mul_neg, ← Matrix.mul_assoc, PalatiniEuler.eta_mul_eta, Matrix.one_mul]
      rfl
    rw [Matrix.mul_apply] at this
    exact this
  simp only [slabCliff, smul_mul_smul_comm, hJ, smul_neg, smul_smul, hW]
  rw [show lorentzSign c * lorentzSign d * W c d * (lorentzSign c * lorentzSign d) =
      W c d * (lorentzSign c * lorentzSign c) * (lorentzSign d * lorentzSign d) by ring,
    lorentzSign_sq, lorentzSign_sq, neg_smul]
  simp

end Cliff

/-! ### The slab frame connection of the native frame -/

/-- `∇_γ e_B{}^μ = (e⁻¹Ω_γ)^μ_B` for the frame `e_B{}^μ = (e⁻¹)^μ_B` with jets
`∂_γ(e⁻¹) = -e⁻¹q_γe⁻¹`. -/
theorem cv1_eq {E : Mat} (hE : E.det ≠ 0) (q : Fin 4 → Mat) (γ B μ : Fin 4) :
    FrameCurvature.cv1 (chr (fun a b => (metric E)⁻¹ a b) (readerG E q)) (fun μ => E⁻¹ μ B)
      (fun γ μ => -(E⁻¹ * q γ * E⁻¹) μ B) γ μ = (E⁻¹ * readerOmega E q γ) μ B := by
  have hEiE : E⁻¹ * E = 1 := Matrix.nonsing_inv_mul E hE.isUnit
  have h : E⁻¹ * readerOmega E q γ = gam E q γ * E⁻¹ - E⁻¹ * q γ * E⁻¹ := by
    rw [readerOmega_eq, Matrix.mul_sub, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, hEiE, Matrix.one_mul, Matrix.mul_assoc]
  rw [h, Matrix.sub_apply, Matrix.mul_apply]
  unfold FrameCurvature.cv1
  rw [add_comm]
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [← readerGamma_eq_chr]
  rfl

/-- **The slab frame connection coefficients of the native frame**:
`G_{ABC} = ⟨∇_{e_A}e_B, e_C⟩ = -(ηΩ_A)_{BC}` with `Ω_A = e_A{}^γΩ_γ(e, q)`. -/
theorem Gfun_eq {E : Mat} (hE : E.det ≠ 0) (q : Fin 4 → Mat) (A B C : Fin 4) :
    ActualJetSystem.Gfun (fun a b => metric E a b) (fun a b => (metric E)⁻¹ a b) (readerG E q)
      (fun A μ => E⁻¹ μ A) (fun γ B μ => -(E⁻¹ * q γ * E⁻¹) μ B) A B C =
      -(eta * frameOf E (readerOmega E q) A) B C := by
  have hEEi : E * E⁻¹ = 1 := Matrix.mul_nonsing_inv E hE.isUnit
  have hEt : (E⁻¹)ᵀ * Eᵀ = 1 := by
    rw [← Matrix.transpose_mul, hEEi, Matrix.transpose_one]
  have hinner : ∀ γ, FrameCurvature.ipg (fun a b => metric E a b)
      (fun μ => FrameCurvature.cv1 (chr (fun a b => (metric E)⁻¹ a b) (readerG E q))
        (fun μ => E⁻¹ μ B) (fun γ μ => -(E⁻¹ * q γ * E⁻¹) μ B) γ μ) (fun μ => E⁻¹ μ C) =
      -(eta * readerOmega E q γ) B C := by
    intro γ
    simp only [cv1_eq hE]
    have hm : (E⁻¹ * readerOmega E q γ)ᵀ * metric E * E⁻¹ = -(eta * readerOmega E q γ) := by
      have hanti := readerOmega_antisym hE q γ
      have h2 : (readerOmega E q γ)ᵀ * eta = -(eta * readerOmega E q γ) :=
        eq_neg_of_add_eq_zero_right hanti
      rw [Matrix.transpose_mul, metric]
      calc (readerOmega E q γ)ᵀ * (E⁻¹)ᵀ * (Eᵀ * eta * E) * E⁻¹ =
            (readerOmega E q γ)ᵀ * ((E⁻¹)ᵀ * Eᵀ) * eta * (E * E⁻¹) := by noncomm_ring
        _ = -(eta * readerOmega E q γ) := by rw [hEt, hEEi, Matrix.mul_one, Matrix.mul_one, h2]
    have := congrFun (congrFun hm B) C
    rw [Matrix.neg_apply] at this
    rw [← this]
    simp only [FrameCurvature.ipg, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun x _ => by ring
  unfold ActualJetSystem.Gfun
  simp only [hinner]
  unfold NativeStressEuler.frameOf
  rw [Matrix.mul_sum, Matrix.sum_apply, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [Matrix.mul_smul, Matrix.smul_apply, smul_eq_mul]
  ring

/-! ### The slab Dirac operator of the native frame -/

section SlabDirac

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
variable (M : Model 𝔄 𝓗 𝓢)

/-- The slab twisted spin connection `ω_B = ¼Σε_cε_dG_{Bcd}c_cc_d + e_B{}^μρ(A_μ)` of the native
frame, in the slab Clifford frame. -/
def slabOmega (E : Mat) (q : Fin 4 → Mat) (A : Fin 4 → 𝔄) (B : Fin 4) : Spin 𝓢 :=
  SpinorProlongation.spinPart (slabCliff M)
      (ActualJetSystem.Gfun (fun a b => metric E a b) (fun a b => (metric E)⁻¹ a b) (readerG E q)
        (fun A μ => E⁻¹ μ A) (fun γ B μ => -(E⁻¹ * q γ * E⁻¹) μ B) B) +
    ∑ μ, E⁻¹ μ B • M.ρS (A μ)

/-- **The slab spin connection is the native one**: `ω_B = σ(Ω_B) + e_B{}^μρ_S(A_μ)`. -/
theorem slabOmega_eq {E : Mat} (hE : E.det ≠ 0) (q : Fin 4 → Mat) (A : Fin 4 → 𝔄) (B : Fin 4) :
    slabOmega M E q A B = ∑ γ, E⁻¹ γ B • (M.σ (readerOmega E q γ) + M.ρS (A γ)) := by
  unfold slabOmega
  rw [spinPart_slabCliff]
  have hG : (Matrix.of fun C D => ActualJetSystem.Gfun (fun a b => metric E a b)
      (fun a b => (metric E)⁻¹ a b) (readerG E q) (fun A μ => E⁻¹ μ A)
      (fun γ B μ => -(E⁻¹ * q γ * E⁻¹) μ B) B C D) = -(eta * frameOf E (readerOmega E q) B) := by
    ext C D
    rw [Matrix.of_apply, Gfun_eq hE, Matrix.neg_apply]
  rw [hG, Matrix.mul_neg, neg_neg, ← Matrix.mul_assoc, PalatiniEuler.eta_mul_eta, Matrix.one_mul]
  unfold NativeStressEuler.frameOf
  rw [map_sum]
  simp only [map_smul, smul_add, Finset.sum_add_distrib]

/-- **The slab covariant derivative is the native one**: `X_B = e_B{}^γ∇_γΨ`. -/
theorem slab_cov_eq {E : Mat} (hE : E.det ≠ 0) (q : Fin 4 → Mat) (A : Fin 4 → 𝔄) (ψ : 𝓢)
    (dψ : Fin 4 → 𝓢) (B : Fin 4) :
    SpinorProlongation.cov (slabOmega M E q A) ψ (fun B => ∑ γ, E⁻¹ γ B • dψ γ) B =
      ∑ γ, E⁻¹ γ B • ((M.σ (readerOmega E q γ) + M.ρS (A γ)) ψ + dψ γ) := by
  unfold SpinorProlongation.cov
  rw [slabOmega_eq M hE]
  simp only [ContinuousLinearMap.smul_def, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, smul_add,
    Finset.sum_add_distrib]
  abel

/-- **The slab Dirac residual is the native one**: with the slab Clifford frame, the mass map
`𝓜 = 0 + 𝓜_𝐘` and the native frame,
`Σ_b ε_b c_b X_b - 𝓜(H)Ψ = Jγ^μ(e)∇_μΨ - 𝓜_𝐘(H)Ψ`. -/
theorem slab_resD_eq {E : Mat} (hE : E.det ≠ 0) (q : Fin 4 → Mat) (A : Fin 4 → 𝔄) (H : 𝓗)
    (ψ : 𝓢) (dψ : Fin 4 → 𝓢) :
    SpinorProlongation.resD (slabCliff M) (slabOmega M E q A) (0 : Spin 𝓢)
        (M.yukawa : 𝓗 →ₗ[ℝ] Spin 𝓢) H ψ (fun B => ∑ γ, E⁻¹ γ B • dψ γ) =
      M.J (∑ γ, gammaMu M.toData γ E ((M.σ (readerOmega E q γ) + M.ρS (A γ)) ψ + dψ γ)) -
        M.yukawa H ψ := by
  unfold SpinorProlongation.resD SpinorProlongation.dirac SpinorProlongation.mass
  simp only [slab_cov_eq M hE, slabCliff_c, ContinuousLinearMap.smul_def,
    ContinuousLinearMap.smul_apply, smul_smul, zero_add, ContinuousLinearMap.mul_apply]
  congr 1
  rw [map_sum]
  simp only [gammaMu, invEntry, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    map_sum, map_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [slabCliff_ε, lorentzSign_sq, one_smul]

end SlabDirac

end

end NativeFrameBridge

end RenewalGeometry
