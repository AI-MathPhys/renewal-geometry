/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.CriticalQuotientTestPullback

/-!
# The covariant test size of pulled-back tests
  (`lem:equivariant-tests`, `eq:equivariant-test-size`, `thm:critical-quotient-defect`;
  Einstein–Standard-Model action-closure manuscript)

`nSize μ A v` is the covariant test size `𝔫_z(v)` of `eq:equivariant-test-size` in the
field-tuple rendering (the formula of `EinsteinSM.covTestSizeSM`, on an arbitrary measure; for a
chart box it coincides with `covTestSizeSM` on the defining carrier, `nSize_eq_covTestSizeSM`):
`‖k‖_∞ + ‖∂k‖_∞ + ‖a‖_∞ + ‖η_H‖_∞ + ‖η‖_∞ + ‖η̄‖_∞ + Σ_μ (‖D_μa‖_2 + ‖D_μη_H‖_2 + ‖∇^A_μη‖_2 +
‖∇^A_μη̄‖_2)` (flat reference spin connection, sup fibre norms).

* `covDerAd_gauge_at`: local gauge covariance of the adjoint covariant derivative;
* `adCov_pullTest`, `covDerivHiggs_pullTest`, `spinCov_pullTest`, `cospinCov_pullTest`: the
  covariant derivatives of the pulled-back test along the original connection are the pulled-back
  covariant derivatives of the fixed test along the Coulomb connection (no derivative of the gauge);
* **`nSize_pullTest_le`**: `𝔫_{z}(R^*·v) ≤ 25 · 𝔫_{R·z}(v)` (sup fibre norms; the factor `25`
  bounds unitary conjugation in the sup norm), the uniform control of the pulled-back test size
  ("Pulling back fixed normalized tests preserves their `𝔫`-size");
* `nSize_le_of_L2`: the size of a fixed test in a chart is bounded in terms of `‖A‖_{L²}`.
-/

open MeasureTheory Filter Topology Set Matrix
open scoped ENNReal NNReal ContDiff ComplexConjugate

noncomputable section

namespace RenewalGeometry.CriticalQuotientRows

open SobolevOpen CriticalGauge CriticalQuotient BallAnalysis.SMGaugeStructure SMGaugeLie
  EinsteinSM SMGaugeJet CurvatureCovariance

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

/-! ### The covariant test size -/

/-- Spinor test covariant derivative `∇^A_μη = ∂_μη + A_μη` (defining representation, flat
reference spin connection). -/
def spinCov5 (A : E4 → ConnFibre) (η : E4 → SpinorFibre (Fin 5)) (μ : Fin 4) (x : E4) :
    SpinorFibre (Fin 5) :=
  fun s => covDerV (connM A) (fun y => η y s) μ x

/-- Dual spinor test covariant derivative `∇^A_μη̄ = ∂_μη̄ - η̄A_μ` (column form `∂ - Aᵀ`). -/
def cospinCov5 (A : E4 → ConnFibre) (η : E4 → SpinorFibre (Fin 5)) (μ : Fin 4) (x : E4) :
    SpinorFibre (Fin 5) :=
  fun s => covDerV (dualConnM (connM A)) (fun y => η y s) μ x

/-- **The covariant test size `𝔫_z(v)`** (`eq:equivariant-test-size`) at a configuration with
connection `A`, on the measure `μ`. -/
def nSize (μ : Measure E4) (A : E4 → ConnFibre) (v : FieldTuple (Fin 5)) : ℝ≥0∞ :=
  eLpNorm v.e ⊤ μ + eLpNorm (fun x => fun i => pd v.e i x) ⊤ μ + eLpNorm v.A ⊤ μ +
    eLpNorm v.H ⊤ μ + eLpNorm v.Ψ ⊤ μ + eLpNorm v.Ψb ⊤ μ +
    ∑ μ', (eLpNorm (adCov A v.A μ') 2 μ + eLpNorm (fun x => covDerivHiggs A v.H x μ') 2 μ +
      eLpNorm (spinCov5 A v.Ψ μ') 2 μ + eLpNorm (cospinCov5 A v.Ψb μ') 2 μ)

theorem spinCovA_eq {Ysec : Type} (mY : CoefficientBank Ysec → ℂ) {A : E4 → ConnFibre}
    {η : E4 → SpinorFibre (Fin 5)} {x : E4} (hη : DifferentiableAt ℝ η x) (μ : Fin 4) :
    spinCovA (defCarrier Ysec mY) A η μ x = spinCov5 A η μ x := by
  funext s c
  simp only [spinCovA, spinCov5, covDerV, spinActL, mkBilinL_apply, Pi.add_apply, pdV,
    defCarrier_rho, mulVec, dotProduct, connM, of_apply, LinearMap.id_apply]
  rw [pd_apply_gen (differentiableAt_apply_gen hη s) μ c, pd_apply_gen hη μ s]

theorem cospinCovA_eq {Ysec : Type} (mY : CoefficientBank Ysec → ℂ) {A : E4 → ConnFibre}
    {η : E4 → SpinorFibre (Fin 5)} {x : E4} (hη : DifferentiableAt ℝ η x) (μ : Fin 4) :
    cospinCovA (defCarrier Ysec mY) A η μ x = cospinCov5 A η μ x := by
  funext s c
  simp only [cospinCovA, cospinCov5, covDerV, cospinActL, mkBilinL_apply, Pi.sub_apply,
    Pi.add_apply, pdV, defCarrier_rho, mulVec, dotProduct, connM, dualConnM, of_apply,
    neg_apply, transpose_apply, neg_mul, Finset.sum_neg_distrib, ← sub_eq_add_neg,
    LinearMap.id_apply]
  rw [pd_apply_gen (differentiableAt_apply_gen hη s) μ c, pd_apply_gen hη μ s, sub_eq_add_neg,
    ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Matrix.neg_apply, transpose_apply, of_apply]
  ring

/-! ### Unitary bounds in the sup norm -/

theorem norm_entry_le_one {U : M5} (hU : U ∈ unitaryGroup (Fin 5) ℂ) (i j : Fin 5) :
    ‖U i j‖ ≤ 1 := by
  have h := congrFun (congrFun (mem_unitaryGroup_iff'.mp hU) j) j
  simp only [Matrix.mul_apply, star_apply, one_apply_eq] at h
  have h' : ∑ k, ((Complex.normSq (U k j) : ℝ) : ℂ) = 1 := by
    rw [← h]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.normSq_eq_conj_mul_self]
    rfl
  have hs : ∑ k, Complex.normSq (U k j) = 1 := by exact_mod_cast h'
  have : Complex.normSq (U i j) ≤ 1 := hs ▸ Finset.single_le_sum
    (f := fun k => Complex.normSq (U k j)) (fun k _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
  rw [← Complex.sq_norm] at this
  nlinarith [norm_nonneg (U i j)]

theorem norm_mulVec_le {U : M5} (hU : U ∈ unitaryGroup (Fin 5) ℂ) (w : Fin 5 → ℂ) :
    ‖U *ᵥ w‖ ≤ 5 * ‖w‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
  simp only [mulVec, dotProduct]
  calc ‖∑ k, U i k * w k‖ ≤ ∑ k, ‖U i k * w k‖ := norm_sum_le _ _
    _ ≤ ∑ _k : Fin 5, ‖w‖ := Finset.sum_le_sum fun k _ => by
        rw [norm_mul]
        calc ‖U i k‖ * ‖w k‖ ≤ 1 * ‖w‖ := mul_le_mul (norm_entry_le_one hU i k)
              (norm_le_pi_norm w k) (norm_nonneg _) zero_le_one
          _ = ‖w‖ := one_mul _
    _ = 5 * ‖w‖ := by simp

theorem norm_conj_le {U : M5} (hU : U ∈ unitaryGroup (Fin 5) ℂ) (X : LieFibre) :
    ‖(fun i j => (U * Matrix.of X * star U) i j : LieFibre)‖ ≤ 25 * ‖X‖ := by
  have hX : ∀ k l, ‖X k l‖ ≤ ‖X‖ := fun k l =>
    (norm_le_pi_norm (X k) l).trans (norm_le_pi_norm X k)
  have h0 : 0 ≤ 25 * ‖X‖ := by positivity
  refine (pi_norm_le_iff_of_nonneg h0).mpr fun i => (pi_norm_le_iff_of_nonneg h0).mpr fun j => ?_
  simp only [Matrix.mul_apply, star_apply, of_apply]
  calc ‖∑ l, (∑ k, U i k * X k l) * star (U j l)‖ ≤ ∑ l, ∑ k, ‖X k l‖ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
        rw [norm_mul, norm_star]
        refine (mul_le_of_le_one_right (norm_nonneg _) (norm_entry_le_one hU j l)).trans ?_
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
        rw [norm_mul]
        exact mul_le_of_le_one_left (norm_nonneg _) (norm_entry_le_one hU i k)
    _ ≤ ∑ _l : Fin 5, ∑ _k : Fin 5, ‖X‖ :=
        Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun k _ => hX k l
    _ = 25 * ‖X‖ := by simp; ring


theorem norm_mulVec_le_of_entries {M : M5} (hM : ∀ i j, ‖M i j‖ ≤ 1) (w : Fin 5 → ℂ) :
    ‖M *ᵥ w‖ ≤ 5 * ‖w‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
  simp only [mulVec, dotProduct]
  calc ‖∑ k, M i k * w k‖ ≤ ∑ k, ‖M i k * w k‖ := norm_sum_le _ _
    _ ≤ ∑ _k : Fin 5, ‖w‖ := Finset.sum_le_sum fun k _ => by
        rw [norm_mul]
        calc ‖M i k‖ * ‖w k‖ ≤ 1 * ‖w‖ := mul_le_mul (hM i k)
              (norm_le_pi_norm w k) (norm_nonneg _) zero_le_one
          _ = ‖w‖ := one_mul _
    _ = 5 * ‖w‖ := by simp

theorem entries_star_le {U : M5} (hU : U ∈ unitaryGroup (Fin 5) ℂ) (i j : Fin 5) :
    ‖star U i j‖ ≤ 1 := by
  rw [star_apply, norm_star]; exact norm_entry_le_one hU j i

theorem entries_transpose_le {U : M5} (hU : U ∈ unitaryGroup (Fin 5) ℂ) (i j : Fin 5) :
    ‖Uᵀ i j‖ ≤ 1 := by
  rw [transpose_apply]; exact norm_entry_le_one hU j i

theorem norm_higgsG_le {g : M5} (hg : g ∈ unitaryGroup (Fin 5) ℂ) (v : HiggsFibre) :
    ‖higgsG g v‖ ≤ 25 * ‖v‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
  simp only [higgsG, mulVec, dotProduct, wk, submatrix_apply]
  calc ‖∑ k, g (Fin.natAdd 3 i) (Fin.natAdd 3 k) * v k‖ ≤ ∑ k, ‖v‖ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
        rw [norm_mul]
        calc ‖g _ _‖ * ‖v k‖ ≤ 1 * ‖v‖ := mul_le_mul (norm_entry_le_one hg _ _)
              (norm_le_pi_norm v k) (norm_nonneg _) zero_le_one
          _ = ‖v‖ := one_mul _
    _ = 2 * ‖v‖ := by simp
    _ ≤ 25 * ‖v‖ := by nlinarith [norm_nonneg v]

theorem norm_spin_le {M : M5} (hM : ∀ i j, ‖M i j‖ ≤ 1) (ψ : SpinorFibre (Fin 5)) :
    ‖(fun s => M *ᵥ ψ s : SpinorFibre (Fin 5))‖ ≤ 25 * ‖ψ‖ :=
  (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun s =>
    (norm_mulVec_le_of_entries hM (ψ s)).trans (by nlinarith [norm_le_pi_norm ψ s, norm_nonneg (ψ s)])

theorem norm_adG_star_le {U : M5} (hU : U ∈ unitaryGroup (Fin 5) ℂ) (X : LieFibre) :
    ‖adG (star U) X‖ ≤ 25 * ‖X‖ := by
  have hU' : star U ∈ unitaryGroup (Fin 5) ℂ := Unitary.star_mem hU
  exact norm_conj_le hU' X

/-! ### Local covariance of the test covariant derivatives -/

theorem pdM_unitary_at {R : E4 → M5} {x : E4}
    (hRu : ∀ᶠ y in 𝓝 x, R y ∈ unitaryGroup (Fin 5) ℂ) (hR : MDiffAt R x) (μ : Fin 4) :
    pdM R μ x * star (R x) + R x * star (pdM R μ x) = 0 := by
  have hs := star_pdM_of_unitary hRu hR μ
  have h1 : R x * star (R x) = 1 := mem_unitaryGroup_iff.mp hRu.self_of_nhds
  rw [hs, Matrix.mul_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul, add_neg_cancel]

/-- **Local gauge covariance, adjoint representation**:
`D_{R·𝒜}(R a R^*) = R (D_𝒜 a) R^*` at a point near which `R` is unitary. -/
theorem covDerAd_gauge_at {R : E4 → M5} {x : E4}
    (hRu : ∀ᶠ y in 𝓝 x, R y ∈ unitaryGroup (Fin 5) ℂ) (hR : MDiffAt R x) (𝒜 : MConn 5)
    {a : E4 → M5} (ha : MDiffAt a x) (μ : Fin 4) :
    covDerAd (gaugeConn R 𝒜) (fun y => R y * a y * star (R y)) μ x =
      R x * covDerAd 𝒜 a μ x * star (R x) := by
  have hu : star (R x) * R x = 1 := Matrix.mem_unitaryGroup_iff'.mp hRu.self_of_nhds
  have hz := pdM_unitary_at hRu hR μ
  have hd : pdM (fun y => R y * a y * star (R y)) μ x =
      pdM R μ x * a x * star (R x) + R x * pdM a μ x * star (R x) +
        R x * a x * star (pdM R μ x) := by
    rw [pdM_mul (hR.mul ha) hR.star, pdM_mul hR ha, pdM_star hR]
    noncomm_ring
  have hk : R x * a x * star (pdM R μ x) =
      -(R x * a x * star (R x) * (pdM R μ x * star (R x))) := by
    have : star (pdM R μ x) = -(star (R x) * (pdM R μ x * star (R x))) := by
      have h3 : R x * star (pdM R μ x) = -(pdM R μ x * star (R x)) :=
        eq_neg_of_add_eq_zero_right hz
      calc star (pdM R μ x) = star (R x) * (R x * star (pdM R μ x)) := by
            rw [← Matrix.mul_assoc, hu, Matrix.one_mul]
        _ = -(star (R x) * (pdM R μ x * star (R x))) := by rw [h3, Matrix.mul_neg]
    rw [this, Matrix.mul_neg]
    simp only [Matrix.mul_assoc]
  simp only [covDerAd, gaugeConn, hd, hk]
  have e1 : (R x * 𝒜 μ x * star (R x) - pdM R μ x * star (R x)) * (R x * a x * star (R x)) =
      R x * 𝒜 μ x * a x * star (R x) - pdM R μ x * a x * star (R x) := by
    simp only [Matrix.sub_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star (R x)) (R x), hu, Matrix.one_mul]
  have e2 : R x * a x * star (R x) * (R x * 𝒜 μ x * star (R x) - pdM R μ x * star (R x)) =
      R x * a x * 𝒜 μ x * star (R x) - R x * a x * star (R x) * (pdM R μ x * star (R x)) := by
    simp only [Matrix.mul_sub, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star (R x)) (R x), hu, Matrix.one_mul]
  rw [e1, e2]
  noncomm_ring

theorem pdM_congr {a b : E4 → M5} {x : E4} (h : a =ᶠ[𝓝 x] b) (μ : Fin 4) :
    pdM a μ x = pdM b μ x := by
  ext c e
  simp only [pdM, of_apply]
  exact pd_congr_ev (h.mono fun y hy => by rw [hy]) μ

theorem covDerAd_congr {𝒜 : MConn 5} {a b : E4 → M5} {x : E4} (h : a =ᶠ[𝓝 x] b) (μ : Fin 4) :
    covDerAd 𝒜 a μ x = covDerAd 𝒜 b μ x := by
  simp only [covDerAd, pdM_congr h μ, h.self_of_nhds]

theorem covDerV_congr {𝒜 : MConn 5} {a b : E4 → Fin 5 → ℂ} {x : E4} (h : a =ᶠ[𝓝 x] b)
    (μ : Fin 4) : covDerV 𝒜 a μ x = covDerV 𝒜 b μ x := by
  have hp : pdV a μ x = pdV b μ x := by
    funext c; exact pd_congr_ev (h.mono fun y hy => by rw [hy]) μ
  simp only [covDerV, hp, h.self_of_nhds]

theorem adCov_eq_covDerAd {A b : E4 → ConnFibre} {x : E4} (hb : DifferentiableAt ℝ b x)
    (μ ν : Fin 4) :
    Matrix.of (adCov A b μ x ν) = covDerAd (connM A) (fun y => Matrix.of (b y ν)) μ x := by
  ext c e
  simp only [adCov, adActL, mkBilinL_apply, Pi.add_apply, covDerAd, Matrix.add_apply,
    Matrix.sub_apply, pdM, of_apply, connM, EinsteinSM.comm, mmul, Matrix.mul_apply,
    Pi.sub_apply]
  rw [← pd_apply_gen hb μ ν, ← pd_apply_gen (differentiableAt_apply_gen hb ν) μ c,
    ← pd_apply_gen (differentiableAt_apply_gen (differentiableAt_apply_gen hb ν) c) μ e]

theorem covDerivHiggs_eq_proj {A : E4 → ConnFibre} {H : E4 → HiggsFibre} {x : E4}
    (hH : DifferentiableAt ℝ H x) (μ : Fin 4) :
    covDerivHiggs A H x μ = projH (covDerV (connM A) (fun y => embH (H y)) μ x) := by
  simp only [covDerivHiggs, covDerV]
  funext i
  simp only [Pi.add_apply, projH]
  rw [show pdV (fun y => embH (H y)) μ x (Fin.natAdd 3 i) = pd H μ x i from
    congrFun (pdV_embH hH μ) i, higgsAct_eq_proj]
  rfl

/-- Pulled-back covariance in the fundamental representation: `∇^𝒜(R^* w) = R^* ∇^{R·𝒜} w`. -/
theorem covDerV_pull {R : E4 → M5} {x : E4}
    (hRu : ∀ᶠ y in 𝓝 x, R y ∈ unitaryGroup (Fin 5) ℂ) (hR : MDiffAt R x) (𝒜 : MConn 5)
    {w : E4 → Fin 5 → ℂ} (hw : VDiffAt w x) (μ : Fin 4) :
    covDerV 𝒜 (fun y => star (R y) *ᵥ w y) μ x = star (R x) *ᵥ covDerV (gaugeConn R 𝒜) w μ x := by
  have hRs : MDiffAt (fun y => star (R y)) x := hR.star
  have h := covDerV_gauge_at hRu.self_of_nhds 𝒜 hR (VDiffAt.mulVec hRs hw) μ
  have hev : (fun y => R y *ᵥ (star (R y) *ᵥ w y)) =ᶠ[𝓝 x] w := hRu.mono fun y hy => by
    show R y *ᵥ (star (R y) *ᵥ w y) = w y
    rw [mulVec_mulVec, mem_unitaryGroup_iff.mp hy, one_mulVec]
  rw [covDerV_congr hev μ] at h
  rw [h, mulVec_mulVec, mem_unitaryGroup_iff'.mp hRu.self_of_nhds, one_mulVec]

/-- Local dual gauge law `R̄·(-𝒜ᵀ) = -(R·𝒜)ᵀ`. -/
theorem gaugeConn_dual_at {R : E4 → M5} {x : E4}
    (hRu : ∀ᶠ y in 𝓝 x, R y ∈ unitaryGroup (Fin 5) ℂ) (hR : MDiffAt R x) (𝒜 : MConn 5)
    (μ : Fin 4) : gaugeConn (dualGauge R) (dualConnM 𝒜) μ x = dualConnM (gaugeConn R 𝒜) μ x := by
  have hz := pdM_unitary_at hRu hR μ
  have hz' : (R x * star (pdM R μ x))ᵀ = -(pdM R μ x * star (R x))ᵀ := by
    rw [← Matrix.transpose_neg]; congr 1; exact eq_neg_of_add_eq_zero_right hz
  simp only [gaugeConn, dualConnM, pdM_dualGauge hR, dualGauge]
  have e1 : star ((star (R x))ᵀ) = (R x)ᵀ := by
    rw [Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_transpose_eq_transpose_conjTranspose, Matrix.conjTranspose_conjTranspose]
  rw [e1]
  have e2 : (star (pdM R μ x))ᵀ * (R x)ᵀ = (R x * star (pdM R μ x))ᵀ := by
    rw [Matrix.transpose_mul]
  have e3 : (star (R x))ᵀ * -(𝒜 μ x)ᵀ * (R x)ᵀ = -(R x * 𝒜 μ x * star (R x))ᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.mul_neg, Matrix.neg_mul,
      Matrix.mul_assoc]
  rw [e2, e3, hz', Matrix.transpose_sub]
  abel

theorem dualGauge_unitary_at {R : E4 → M5} {x : E4}
    (hRu : ∀ᶠ y in 𝓝 x, R y ∈ unitaryGroup (Fin 5) ℂ) :
    ∀ᶠ y in 𝓝 x, dualGauge R y ∈ unitaryGroup (Fin 5) ℂ := hRu.mono fun y hy => by
  rw [mem_unitaryGroup_iff]
  have h := mem_unitaryGroup_iff.mp hy
  show (star (R y))ᵀ * star ((star (R y))ᵀ) = 1
  rw [Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_transpose_eq_transpose_conjTranspose, Matrix.conjTranspose_conjTranspose,
    ← Matrix.transpose_mul, ← Matrix.star_eq_conjTranspose, h, Matrix.transpose_one]

/-- Pulled-back covariance in the dual representation: `∇^{𝒜∨}(Rᵀ w) = Rᵀ ∇^{(R·𝒜)∨} w`. -/
theorem covDerV_dual_pull {R : E4 → M5} {x : E4}
    (hRu : ∀ᶠ y in 𝓝 x, R y ∈ unitaryGroup (Fin 5) ℂ) (hR : MDiffAt R x) (𝒜 : MConn 5)
    {w : E4 → Fin 5 → ℂ} (hw : VDiffAt w x) (μ : Fin 4) :
    covDerV (dualConnM 𝒜) (fun y => (R y)ᵀ *ᵥ w y) μ x =
      (R x)ᵀ *ᵥ covDerV (dualConnM (gaugeConn R 𝒜)) w μ x := by
  have hD := dualGauge_unitary_at hRu
  have hDd : MDiffAt (dualGauge R) x := hR.dualGauge
  have hT : MDiffAt (fun y => (R y)ᵀ) x := fun c e => hR e c
  have h := covDerV_gauge_at hD.self_of_nhds (dualConnM 𝒜) hDd (VDiffAt.mulVec hT hw) μ
  have hinv : ∀ y, R y ∈ unitaryGroup (Fin 5) ℂ → dualGauge R y * (R y)ᵀ = 1 := fun y hy => by
    simp only [dualGauge]
    rw [← Matrix.transpose_mul, mem_unitaryGroup_iff.mp hy, Matrix.transpose_one]
  have hev : (fun y => dualGauge R y *ᵥ ((R y)ᵀ *ᵥ w y)) =ᶠ[𝓝 x] w := hRu.mono fun y hy => by
    show dualGauge R y *ᵥ ((R y)ᵀ *ᵥ w y) = w y
    rw [mulVec_mulVec, hinv y hy, one_mulVec]
  rw [covDerV_congr hev μ] at h
  have hdual : (fun μ y => gaugeConn (dualGauge R) (dualConnM 𝒜) μ y) μ x =
      dualConnM (gaugeConn R 𝒜) μ x := gaugeConn_dual_at hRu hR 𝒜 μ
  have hc : covDerV (gaugeConn (dualGauge R) (dualConnM 𝒜)) w μ x =
      covDerV (dualConnM (gaugeConn R 𝒜)) w μ x := by
    simp only [covDerV, hdual]
  rw [hc] at h
  have hinv' : (R x)ᵀ * dualGauge R x = 1 := by
    simp only [dualGauge]
    rw [← Matrix.transpose_mul, mem_unitaryGroup_iff'.mp hRu.self_of_nhds, Matrix.transpose_one]
  rw [h, mulVec_mulVec, hinv', one_mulVec]


/-! ### Covariant derivatives of pulled-back tests -/

theorem of_pullTest_A (R : E4 → M5) (v : FieldTuple (Fin 5)) (y : E4) (ν : Fin 4) :
    Matrix.of ((pullTest R v).A y ν) = star (R y) * Matrix.of (v.A y ν) * R y := by
  ext i j
  show (star (R y) * Matrix.of (v.A y ν) * star (star (R y))) i j = _
  rw [star_star]

theorem adCov_pullTest {R : E4 → M5} {x : E4} (hR : GaugeAt R x) (z : FieldTuple (Fin 5))
    {v : FieldTuple (Fin 5)} (hv : DiffAt v x) (hp : DiffAt (pullTest R v) x) (μ ν : Fin 4) :
    Matrix.of (adCov z.A (pullTest R v).A μ x ν) =
      star (R x) * Matrix.of (adCov (gaugeTuple R z).A v.A μ x ν) * R x := by
  have hu : R x * star (R x) = 1 := mem_unitaryGroup_iff.mp hR.unitary.self_of_nhds
  have hu' : star (R x) * R x = 1 := mem_unitaryGroup_iff'.mp hR.unitary.self_of_nhds
  set a : E4 → M5 := fun y => Matrix.of (v.A y ν)
  have ha : MDiffAt a x := mdiffAt_connM hv.A ν
  have hb : MDiffAt (fun y => star (R y) * a y * R y) x := (hR.mdiff.star.mul ha).mul hR.mdiff
  have h := covDerAd_gauge_at hR.unitary hR.mdiff (connM z.A) hb μ
  have hev : (fun y => R y * (star (R y) * a y * R y) * star (R y)) =ᶠ[𝓝 x] a :=
    hR.unitary.mono fun y hy => by
      show R y * (star (R y) * a y * R y) * star (R y) = a y
      have h1 : R y * star (R y) = 1 := mem_unitaryGroup_iff.mp hy
      simp only [Matrix.mul_assoc]
      rw [h1, Matrix.mul_one, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  rw [covDerAd_congr hev μ] at h
  rw [adCov_eq_covDerAd hp.A, adCov_eq_covDerAd hv.A, connM_gaugeTuple]
  have e : (fun y => Matrix.of ((pullTest R v).A y ν)) = fun y => star (R y) * a y * R y :=
    funext fun y => of_pullTest_A R v y ν
  rw [e, h]
  simp only [Matrix.mul_assoc]
  rw [hu', Matrix.mul_one, ← Matrix.mul_assoc, hu', Matrix.one_mul]

theorem covDerivHiggs_pullTest {R : E4 → M5} {x : E4} (hR : GaugeAt R x)
    (z : FieldTuple (Fin 5)) {v : FieldTuple (Fin 5)} (hv : DiffAt v x)
    (hp : DiffAt (pullTest R v) x) (μ : Fin 4) :
    covDerivHiggs z.A (pullTest R v).H x μ =
      higgsG (star (R x)) (covDerivHiggs (gaugeTuple R z).A v.H x μ) := by
  have hblock : ∀ᶠ y in 𝓝 x, IsSMBlock (star (R y)) :=
    hR.mem.mono fun y hy => (star_mem_GSM hy).2.1
  have hev : (fun y => embH ((pullTest R v).H y)) =ᶠ[𝓝 x]
      fun y => star (R y) *ᵥ embH (v.H y) :=
    hblock.mono fun y hy => embH_higgsG hy (v.H y)
  rw [covDerivHiggs_eq_proj hp.H, covDerV_congr hev μ,
    covDerV_pull hR.unitary hR.mdiff (connM z.A) (vDiffAt_embH hv.H) μ,
    projH_mulVec hblock.self_of_nhds, covDerivHiggs_eq_proj hv.H, connM_gaugeTuple]

theorem spinCov5_pullTest {R : E4 → M5} {x : E4} (hR : GaugeAt R x) (z : FieldTuple (Fin 5))
    {v : FieldTuple (Fin 5)} (hv : DiffAt v x) (μ : Fin 4) (s : Fin 4) :
    spinCov5 z.A (pullTest R v).Ψ μ x s = star (R x) *ᵥ spinCov5 (gaugeTuple R z).A v.Ψ μ x s := by
  have hw : VDiffAt (fun y => v.Ψ y s) x := fun c =>
    differentiableAt_apply_gen (differentiableAt_apply_gen hv.Ψ s) c
  have := covDerV_pull hR.unitary hR.mdiff (connM z.A) hw μ
  show covDerV (connM z.A) (fun y => star (R y) *ᵥ v.Ψ y s) μ x =
    star (R x) *ᵥ covDerV (connM (gaugeTuple R z).A) (fun y => v.Ψ y s) μ x
  rw [connM_gaugeTuple]
  exact this

theorem cospinCov5_pullTest {R : E4 → M5} {x : E4} (hR : GaugeAt R x) (z : FieldTuple (Fin 5))
    {v : FieldTuple (Fin 5)} (hv : DiffAt v x) (μ : Fin 4) (s : Fin 4) :
    cospinCov5 z.A (pullTest R v).Ψb μ x s =
      (R x)ᵀ *ᵥ cospinCov5 (gaugeTuple R z).A v.Ψb μ x s := by
  have hw : VDiffAt (fun y => v.Ψb y s) x := fun c =>
    differentiableAt_apply_gen (differentiableAt_apply_gen hv.Ψb s) c
  have := covDerV_dual_pull hR.unitary hR.mdiff (connM z.A) hw μ
  have e : (fun y => (pullTest R v).Ψb y s) = fun y => (R y)ᵀ *ᵥ v.Ψb y s := by
    funext y; show (star (star (R y)))ᵀ *ᵥ v.Ψb y s = _; rw [star_star]
  simp only [cospinCov5, connM_gaugeTuple]
  rw [e]
  exact this

/-! ### Comparison of sizes -/

theorem eLpNorm_le_restrict {F G : Type*} [NormedAddCommGroup F] [NormedAddCommGroup G]
    {f : E4 → F} {g : E4 → G} {S Q : Set E4} (hS : MeasurableSet S) (hQ : MeasurableSet Q)
    (hQS : Q ⊆ S) {c : ℝ} (hin : ∀ x ∈ Q, ‖f x‖ ≤ c * ‖g x‖) (hout : ∀ x ∈ S, x ∉ Q → f x = 0)
    (p : ℝ≥0∞) :
    eLpNorm f p (volume.restrict S) ≤ ENNReal.ofReal c * eLpNorm g p (volume.restrict Q) := by
  have e1 : eLpNorm f p (volume.restrict S) = eLpNorm f p (volume.restrict Q) := by
    have hfi : f =ᵐ[volume.restrict S] Q.indicator f := by
      refine (ae_restrict_iff' hS).mpr (Eventually.of_forall fun x hx => ?_)
      by_cases hxQ : x ∈ Q
      · rw [indicator_of_mem hxQ]
      · rw [indicator_of_notMem hxQ, hout x hx hxQ]
    rw [eLpNorm_congr_ae hfi, eLpNorm_indicator_eq_eLpNorm_restrict hQ,
      Measure.restrict_restrict hQ, inter_eq_left.mpr hQS]
  rw [e1]
  exact eLpNorm_le_mul_eLpNorm_of_ae_le_mul ((ae_restrict_iff' hQ).mpr
    (Eventually.of_forall hin)) p

/-- **`𝔫_z(R^*·v) ≤ 25 · 𝔫_{R·z}(v)`**: the covariant test size of a pulled-back test along the
original connection is controlled by the test size of the fixed test along the Coulomb
connection (sup fibre norms; no derivative of the gauge). -/
theorem nSize_pullTest_le {R : E4 → M5} {B S Q : Set E4} (hB : IsOpen B)
    (hRs : ∀ c e, ContDiffOn ℝ ∞ (fun y => R y c e) B) (hRG : ∀ y ∈ B, R y ∈ GSM)
    (z : FieldTuple (Fin 5)) {v : FieldTuple (Fin 5)} (hv : IsSetTest Q v) (hQB : Q ⊆ B)
    (hQS : Q ⊆ S) (hS : MeasurableSet S) (hQ : MeasurableSet Q) :
    nSize (volume.restrict S) z.A (pullTest R v) ≤
      ENNReal.ofReal 25 * nSize (volume.restrict Q) (gaugeTuple R z).A v := by
  obtain ⟨Kc, hKc, hKQ, h0⟩ := hv.supp
  have hloc : ∀ x, x ∉ Kc → ∀ᶠ y in 𝓝 x, VanishesAt v y := fun x hx =>
    Filter.mem_of_superset (hKc.isClosed.isOpen_compl.mem_nhds hx) fun y hy => h0 y hy
  have hp := isSetTest_pullTest hB hRs hRG hv hQB
  have hGx : ∀ x ∈ Q, GaugeAt R x := fun x hx =>
    ⟨fun c e => (show ContDiffAt ℝ 2 (fun y => R y c e) x from
      ((hRs c e).contDiffAt (hB.mem_nhds (hQB hx))).of_le (WithTop.coe_le_coe.mpr le_top)),
      Filter.mem_of_superset (hB.mem_nhds (hQB hx)) fun y hy => hRG y hy⟩
  have hU : ∀ x ∈ Q, R x ∈ unitaryGroup (Fin 5) ℂ := fun x hx => (hRG x (hQB hx)).1
  -- vanishing of all the pulled-back quantities outside `Kc`
  have hvan : ∀ x, x ∉ Kc → ∀ᶠ y in 𝓝 x, VanishesAt (pullTest R v) y := fun x hx =>
    eventually_vanishes_pullTest (hloc x hx)
  have hpd0 : ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E4 → F} {x : E4},
      (∀ᶠ y in 𝓝 x, f y = 0) → ∀ i, pd f i x = 0 := fun {F} _ _ {f} {x} h i =>
    pd_eq_zero_of_eventually (f := f) (h.mono fun y hy => hy) i
  have hout : ∀ x ∈ S, x ∉ Q → x ∉ Kc := fun x _ hxQ h => hxQ (hKQ h)
  have h25 : (0 : ℝ) ≤ 25 := by norm_num
  have h1_25 : ENNReal.ofReal 1 ≤ ENNReal.ofReal 25 := ENNReal.ofReal_le_ofReal (by norm_num)
  -- the sup parts
  have s1 : eLpNorm (pullTest R v).e ⊤ (volume.restrict S) ≤
      ENNReal.ofReal 25 * eLpNorm v.e ⊤ (volume.restrict Q) :=
    (eLpNorm_le_restrict hS hQ hQS (c := 1) (fun x _ => by rw [one_mul]; exact le_rfl)
      (fun x hx hxQ => (hvan x (hout x hx hxQ)).self_of_nhds.1) ⊤).trans
      (mul_le_mul_of_nonneg_right h1_25 bot_le)
  have s2 : eLpNorm (fun x => fun i => pd (pullTest R v).e i x) ⊤ (volume.restrict S) ≤
      ENNReal.ofReal 25 * eLpNorm (fun x => fun i => pd v.e i x) ⊤ (volume.restrict Q) :=
    (eLpNorm_le_restrict hS hQ hQS (c := 1) (fun x _ => by rw [one_mul]; exact le_rfl)
      (fun x hx hxQ => funext fun i => hpd0 ((hvan x (hout x hx hxQ)).mono fun y hy => hy.1) i)
      ⊤).trans (mul_le_mul_of_nonneg_right h1_25 bot_le)
  have s3 : eLpNorm (pullTest R v).A ⊤ (volume.restrict S) ≤
      ENNReal.ofReal 25 * eLpNorm v.A ⊤ (volume.restrict Q) :=
    eLpNorm_le_restrict hS hQ hQS (fun x hx => (pi_norm_le_iff_of_nonneg (by positivity)).mpr
      fun ν => (norm_adG_star_le (hU x hx) _).trans (mul_le_mul_of_nonneg_left
        (norm_le_pi_norm (v.A x) ν) h25))
      (fun x hx hxQ => (hvan x (hout x hx hxQ)).self_of_nhds.2.1) ⊤
  have s4 : eLpNorm (pullTest R v).H ⊤ (volume.restrict S) ≤
      ENNReal.ofReal 25 * eLpNorm v.H ⊤ (volume.restrict Q) :=
    eLpNorm_le_restrict hS hQ hQS (fun x hx => norm_higgsG_le (Unitary.star_mem (hU x hx)) _)
      (fun x hx hxQ => (hvan x (hout x hx hxQ)).self_of_nhds.2.2.1) ⊤
  have s5 : eLpNorm (pullTest R v).Ψ ⊤ (volume.restrict S) ≤
      ENNReal.ofReal 25 * eLpNorm v.Ψ ⊤ (volume.restrict Q) :=
    eLpNorm_le_restrict hS hQ hQS (fun x hx => norm_spin_le (entries_star_le (hU x hx)) _)
      (fun x hx hxQ => (hvan x (hout x hx hxQ)).self_of_nhds.2.2.2.1) ⊤
  have s6 : eLpNorm (pullTest R v).Ψb ⊤ (volume.restrict S) ≤
      ENNReal.ofReal 25 * eLpNorm v.Ψb ⊤ (volume.restrict Q) := by
    refine eLpNorm_le_restrict hS hQ hQS (fun x hx => ?_)
      (fun x hx hxQ => (hvan x (hout x hx hxQ)).self_of_nhds.2.2.2.2) ⊤
    have e : (pullTest R v).Ψb x = fun s => (R x)ᵀ *ᵥ v.Ψb x s := by
      funext s; show (star (star (R x)))ᵀ *ᵥ v.Ψb x s = _; rw [star_star]
    rw [e]
    exact norm_spin_le (entries_transpose_le (hU x hx)) _
  -- the derivative parts
  have d1 : ∀ μ, eLpNorm (adCov z.A (pullTest R v).A μ) 2 (volume.restrict S) ≤
      ENNReal.ofReal 25 * eLpNorm (adCov (gaugeTuple R z).A v.A μ) 2 (volume.restrict Q) := by
    intro μ
    refine eLpNorm_le_restrict hS hQ hQS (fun x hx => ?_) (fun x hx hxQ => ?_) 2
    · refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun ν => ?_
      have e := adCov_pullTest (hGx x hx) z (hv.diffAt x) (hp.diffAt x) μ ν
      have e' : adCov z.A (pullTest R v).A μ x ν =
          adG (star (R x)) (adCov (gaugeTuple R z).A v.A μ x ν) := by
        funext i j
        have := congrFun (congrFun e i) j
        simp only [of_apply] at this
        simp only [adG, star_star]
        exact this
      rw [e']
      exact (norm_adG_star_le (hU x hx) _).trans (mul_le_mul_of_nonneg_left
        (norm_le_pi_norm _ ν) h25)
    · have hv0 := hvan x (hout x hx hxQ)
      simp only [adCov, hpd0 (hv0.mono fun y hy => hy.2.1) μ, hv0.self_of_nhds.2.1, map_zero,
        add_zero]
  have d2 : ∀ μ, eLpNorm (fun x => covDerivHiggs z.A (pullTest R v).H x μ) 2 (volume.restrict S) ≤
      ENNReal.ofReal 25 * eLpNorm (fun x => covDerivHiggs (gaugeTuple R z).A v.H x μ) 2
        (volume.restrict Q) := by
    intro μ
    refine eLpNorm_le_restrict hS hQ hQS (fun x hx => ?_) (fun x hx hxQ => ?_) 2
    · rw [covDerivHiggs_pullTest (hGx x hx) z (hv.diffAt x) (hp.diffAt x) μ]
      exact norm_higgsG_le (Unitary.star_mem (hU x hx)) _
    · have hv0 := hvan x (hout x hx hxQ)
      simp only [covDerivHiggs, hpd0 (hv0.mono fun y hy => hy.2.2.1) μ, hv0.self_of_nhds.2.2.1]
      funext i; simp [higgsAct]
  have d3 : ∀ μ, eLpNorm (spinCov5 z.A (pullTest R v).Ψ μ) 2 (volume.restrict S) ≤
      ENNReal.ofReal 25 * eLpNorm (spinCov5 (gaugeTuple R z).A v.Ψ μ) 2 (volume.restrict Q) := by
    intro μ
    refine eLpNorm_le_restrict hS hQ hQS (fun x hx => ?_) (fun x hx hxQ => ?_) 2
    · have e : spinCov5 z.A (pullTest R v).Ψ μ x =
          fun s => star (R x) *ᵥ spinCov5 (gaugeTuple R z).A v.Ψ μ x s :=
        funext fun s => spinCov5_pullTest (hGx x hx) z (hv.diffAt x) μ s
      rw [e]
      exact norm_spin_le (entries_star_le (hU x hx)) _
    · have hv0 := hvan x (hout x hx hxQ)
      funext s c
      simp only [spinCov5, covDerV, pdV, Pi.add_apply, Pi.zero_apply]
      rw [hpd0 ((hv0.mono fun y hy => hy.2.2.2.1).mono fun y hy => by rw [hy]; rfl) μ]
      simp [hv0.self_of_nhds.2.2.2.1]
  have d4 : ∀ μ, eLpNorm (cospinCov5 z.A (pullTest R v).Ψb μ) 2 (volume.restrict S) ≤
      ENNReal.ofReal 25 * eLpNorm (cospinCov5 (gaugeTuple R z).A v.Ψb μ) 2
        (volume.restrict Q) := by
    intro μ
    refine eLpNorm_le_restrict hS hQ hQS (fun x hx => ?_) (fun x hx hxQ => ?_) 2
    · have e : cospinCov5 z.A (pullTest R v).Ψb μ x =
          fun s => (R x)ᵀ *ᵥ cospinCov5 (gaugeTuple R z).A v.Ψb μ x s :=
        funext fun s => cospinCov5_pullTest (hGx x hx) z (hv.diffAt x) μ s
      rw [e]
      exact norm_spin_le (entries_transpose_le (hU x hx)) _
    · have hv0 := hvan x (hout x hx hxQ)
      funext s c
      simp only [cospinCov5, covDerV, pdV, Pi.add_apply, Pi.zero_apply]
      rw [hpd0 ((hv0.mono fun y hy => hy.2.2.2.2).mono fun y hy => by rw [hy]; rfl) μ]
      simp [hv0.self_of_nhds.2.2.2.2]
  unfold nSize
  calc _ ≤ ENNReal.ofReal 25 * eLpNorm v.e ⊤ (volume.restrict Q) +
        ENNReal.ofReal 25 * eLpNorm (fun x => fun i => pd v.e i x) ⊤ (volume.restrict Q) +
        ENNReal.ofReal 25 * eLpNorm v.A ⊤ (volume.restrict Q) +
        ENNReal.ofReal 25 * eLpNorm v.H ⊤ (volume.restrict Q) +
        ENNReal.ofReal 25 * eLpNorm v.Ψ ⊤ (volume.restrict Q) +
        ENNReal.ofReal 25 * eLpNorm v.Ψb ⊤ (volume.restrict Q) +
        ∑ μ, (ENNReal.ofReal 25 * eLpNorm (adCov (gaugeTuple R z).A v.A μ) 2 (volume.restrict Q) +
          ENNReal.ofReal 25 * eLpNorm (fun x => covDerivHiggs (gaugeTuple R z).A v.H x μ) 2
            (volume.restrict Q) +
          ENNReal.ofReal 25 * eLpNorm (spinCov5 (gaugeTuple R z).A v.Ψ μ) 2 (volume.restrict Q) +
          ENNReal.ofReal 25 * eLpNorm (cospinCov5 (gaugeTuple R z).A v.Ψb μ) 2
            (volume.restrict Q)) :=
        add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add s1 s2) s3) s4) s5)
          s6) (Finset.sum_le_sum fun μ _ =>
            add_le_add (add_le_add (add_le_add (d1 μ) (d2 μ)) (d3 μ)) (d4 μ))
    _ = _ := by simp only [mul_add, Finset.mul_sum]


/-! ### The size of a fixed test along a connection bounded in `L²` -/

theorem eLpNorm_le_add_mul {F A' P : Type*} [NormedAddCommGroup F] [NormedAddCommGroup A']
    [NormedAddCommGroup P] {μ : Measure E4} {f : E4 → F} {g : E4 → P} {A : E4 → A'} {c : ℝ}
    (hc : 0 ≤ c) (hg : AEStronglyMeasurable g μ) (hA : AEStronglyMeasurable A μ)
    (h : ∀ x, ‖f x‖ ≤ ‖g x‖ + c * ‖A x‖) {p : ℝ≥0∞} (hp : 1 ≤ p) :
    eLpNorm f p μ ≤ eLpNorm g p μ + ENNReal.ofReal c * eLpNorm A p μ := by
  calc eLpNorm f p μ ≤ eLpNorm (fun x => ‖g x‖ + c * ‖A x‖) p μ :=
        eLpNorm_mono_real fun x => h x
    _ ≤ eLpNorm (fun x => ‖g x‖) p μ + eLpNorm (fun x => c * ‖A x‖) p μ :=
        eLpNorm_add_le hg.norm (hA.norm.const_mul c) hp
    _ = eLpNorm g p μ + ENNReal.ofReal c * eLpNorm A p μ := by
        rw [eLpNorm_norm]
        have e : (fun x => c * ‖A x‖) = c • fun x => ‖A x‖ := rfl
        rw [e, eLpNorm_const_smul, eLpNorm_norm, Real.enorm_eq_ofReal hc]

theorem norm_higgsAct_le (X : LieFibre) (v : HiggsFibre) : ‖higgsAct X v‖ ≤ 2 * ‖X‖ * ‖v‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
  simp only [higgsAct]
  calc ‖∑ j, X (Fin.natAdd 3 i) (Fin.natAdd 3 j) * v j‖ ≤ ∑ _j : Fin 2, ‖X‖ * ‖v‖ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [norm_mul]
        exact mul_le_mul ((norm_le_pi_norm (X _) _).trans (norm_le_pi_norm X _))
          (norm_le_pi_norm v j) (norm_nonneg _) (norm_nonneg _)
    _ = 2 * ‖X‖ * ‖v‖ := by simp; ring

theorem norm_of_mulVec_le (X : LieFibre) (w : Fin 5 → ℂ) :
    ‖Matrix.of X *ᵥ w‖ ≤ 5 * ‖X‖ * ‖w‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
  simp only [mulVec, dotProduct, of_apply]
  calc ‖∑ k, X i k * w k‖ ≤ ∑ _k : Fin 5, ‖X‖ * ‖w‖ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
        rw [norm_mul]
        exact mul_le_mul ((norm_le_pi_norm (X i) k).trans (norm_le_pi_norm X i))
          (norm_le_pi_norm w k) (norm_nonneg _) (norm_nonneg _)
    _ = 5 * ‖X‖ * ‖w‖ := by simp; ring

theorem norm_dual_mulVec_le (X : LieFibre) (w : Fin 5 → ℂ) :
    ‖(-(Matrix.of X)ᵀ) *ᵥ w‖ ≤ 5 * ‖X‖ * ‖w‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_
  simp only [mulVec, dotProduct, Matrix.neg_apply, transpose_apply, of_apply]
  calc ‖∑ k, -X k i * w k‖ ≤ ∑ _k : Fin 5, ‖X‖ * ‖w‖ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
        rw [norm_mul, norm_neg]
        exact mul_le_mul ((norm_le_pi_norm (X k) i).trans (norm_le_pi_norm X k))
          (norm_le_pi_norm w k) (norm_nonneg _) (norm_nonneg _)
    _ = 5 * ‖X‖ * ‖w‖ := by simp; ring

/-- Bounded continuous functions with compact-complement vanishing are bounded. -/
theorem exists_bound_of_test {F : Type*} [NormedAddCommGroup F] {f : E4 → F}
    (hf : Continuous f) {Kc : Set E4} (hKc : IsCompact Kc) (h0 : ∀ y ∉ Kc, f y = 0) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖f x‖ ≤ M := by
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : x ∈ Kc
  · exact (hM x hx).trans (le_max_left _ _)
  · rw [h0 x hx, norm_zero]; exact le_max_right _ _

theorem memLp_of_bound {F : Type*} [NormedAddCommGroup F] {μ : Measure E4} [IsFiniteMeasure μ]
    {f : E4 → F} (hf : Continuous f) {M : ℝ} (hM : ∀ x, ‖f x‖ ≤ M) (p : ℝ≥0∞) :
    eLpNorm f p μ ≠ ⊤ :=
  (MemLp.of_bound hf.aestronglyMeasurable M (Eventually.of_forall hM)).eLpNorm_ne_top

/-- **The covariant size of a fixed test grows at most linearly in `‖A‖_{L²}`**:
`𝔫_A(v) ≤ C₀ + C₁ ‖A‖_{L²}` with finite constants depending only on the test. -/
theorem nSize_le_of_L2 {S : Set E4} {v : FieldTuple (Fin 5)} (hv : IsSetTest S v)
    {μ : Measure E4} [IsFiniteMeasure μ] :
    ∃ C₀ C₁ : ℝ≥0∞, C₀ ≠ ⊤ ∧ C₁ ≠ ⊤ ∧ ∀ A : E4 → ConnFibre, AEStronglyMeasurable A μ →
      nSize μ A v ≤ C₀ + C₁ * eLpNorm A 2 μ := by
  obtain ⟨Kc, hKc, -, h0⟩ := hv.supp
  have hc : ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E4 → F},
      ContDiff ℝ ∞ f → Continuous f := fun hf => hf.continuous
  have hpdc : ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E4 → F},
      ContDiff ℝ ∞ f → ∀ i, Continuous (fun x => pd f i x) := fun {F} _ _ {f} hf i =>
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have hloc : ∀ x, x ∉ Kc → ∀ᶠ y in 𝓝 x, VanishesAt v y := fun x hx =>
    Filter.mem_of_superset (hKc.isClosed.isOpen_compl.mem_nhds hx) fun y hy => h0 y hy
  have hpd0 : ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E4 → F},
      (∀ y ∉ Kc, f y = 0) → ∀ i y, y ∉ Kc → pd f i y = 0 := by
    intro F _ _ f hf i y hy
    exact pd_eq_zero_of_eventually (Filter.mem_of_superset
      (hKc.isClosed.isOpen_compl.mem_nhds hy) fun y' hy' => hf y' hy') i
  -- bounds for the values
  obtain ⟨Ma, hMa0, hMa⟩ := exists_bound_of_test (hc hv.smooth_A) hKc fun y hy => (h0 y hy).2.1
  obtain ⟨MH, hMH0, hMH⟩ := exists_bound_of_test (hc hv.smooth_H) hKc fun y hy => (h0 y hy).2.2.1
  obtain ⟨MΨ, hMΨ0, hMΨ⟩ := exists_bound_of_test (hc hv.smooth_Ψ) hKc
    fun y hy => (h0 y hy).2.2.2.1
  obtain ⟨MΨb, hMΨb0, hMΨb⟩ := exists_bound_of_test (hc hv.smooth_Ψb) hKc
    fun y hy => (h0 y hy).2.2.2.2
  -- bounds for derivatives
  have hpdb : ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E4 → F},
      ContDiff ℝ ∞ f → (∀ y ∉ Kc, f y = 0) → ∀ i, ∃ M : ℝ, ∀ x, ‖pd f i x‖ ≤ M :=
    fun hf hf0 i => let ⟨M, _, hM⟩ := exists_bound_of_test (hpdc hf i) hKc (hpd0 hf0 i); ⟨M, hM⟩
  set C₀ : ℝ≥0∞ := eLpNorm v.e ⊤ μ + eLpNorm (fun x => fun i => pd v.e i x) ⊤ μ + eLpNorm v.A ⊤ μ +
    eLpNorm v.H ⊤ μ + eLpNorm v.Ψ ⊤ μ + eLpNorm v.Ψb ⊤ μ +
    ∑ μ', (eLpNorm (fun x => pd v.A μ' x) 2 μ + eLpNorm (fun x => pd v.H μ' x) 2 μ +
      eLpNorm (fun x => pd v.Ψ μ' x) 2 μ + eLpNorm (fun x => pd v.Ψb μ' x) 2 μ)
  set cA : Fin 4 → ℝ := fun μ' => ‖adActL μ'‖ * Ma
  set C₁ : ℝ≥0∞ := ∑ μ', (ENNReal.ofReal (cA μ') + ENNReal.ofReal (2 * MH) +
    ENNReal.ofReal (5 * MΨ) + ENNReal.ofReal (5 * MΨb))
  have hfin : ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E4 → F},
      ContDiff ℝ ∞ f → (∀ y ∉ Kc, f y = 0) → ∀ p, eLpNorm f p μ ≠ ⊤ := fun {F} _ _ {f} hf hf0 p =>
    let ⟨M, _, hM⟩ := exists_bound_of_test (hc hf) hKc hf0; memLp_of_bound (hc hf) hM p
  have hfinpd : ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E4 → F},
      ContDiff ℝ ∞ f → (∀ y ∉ Kc, f y = 0) → ∀ i p, eLpNorm (fun x => pd f i x) p μ ≠ ⊤ :=
    fun {F} _ _ {f} hf hf0 i p =>
      let ⟨M, hM⟩ := hpdb hf hf0 i; memLp_of_bound (hpdc hf i) hM p
  refine ⟨C₀, C₁, ?_, ?_, fun A hA => ?_⟩
  · refine ENNReal.add_ne_top.mpr ⟨?_, ENNReal.sum_ne_top.mpr fun μ' _ => ?_⟩
    · refine ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr
        ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hfin hv.smooth_e (fun y hy =>
          (h0 y hy).1) ⊤, ?_⟩, hfin hv.smooth_A (fun y hy => (h0 y hy).2.1) ⊤⟩,
          hfin hv.smooth_H (fun y hy => (h0 y hy).2.2.1) ⊤⟩,
          hfin hv.smooth_Ψ (fun y hy => (h0 y hy).2.2.2.1) ⊤⟩,
          hfin hv.smooth_Ψb (fun y hy => (h0 y hy).2.2.2.2) ⊤⟩
      have hb : ∀ i, ∃ M : ℝ, ∀ x, ‖pd v.e i x‖ ≤ M := hpdb hv.smooth_e (fun y hy => (h0 y hy).1)
      choose M hM using hb
      refine memLp_of_bound (f := fun x => fun i => pd v.e i x)
        (continuous_pi fun i => hpdc hv.smooth_e i) (M := ∑ i, |M i|) (fun x => ?_) ⊤
      refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)).mpr
        fun i => (hM i x).trans ((le_abs_self _).trans (Finset.single_le_sum
          (f := fun i => |M i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)))
    · exact ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr
        ⟨hfinpd hv.smooth_A (fun y hy => (h0 y hy).2.1) μ' 2,
          hfinpd hv.smooth_H (fun y hy => (h0 y hy).2.2.1) μ' 2⟩,
          hfinpd hv.smooth_Ψ (fun y hy => (h0 y hy).2.2.2.1) μ' 2⟩,
          hfinpd hv.smooth_Ψb (fun y hy => (h0 y hy).2.2.2.2) μ' 2⟩
  · refine ENNReal.sum_ne_top.mpr fun μ' _ => ?_
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr
      ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩, ENNReal.ofReal_ne_top⟩, ENNReal.ofReal_ne_top⟩
  -- the derivative pieces
  have hdA : ∀ x, DifferentiableAt ℝ v.A x := fun x => (hv.smooth_A.differentiable (by simp)) x
  have hdΨ : ∀ x, DifferentiableAt ℝ v.Ψ x := fun x => (hv.smooth_Ψ.differentiable (by simp)) x
  have hdΨb : ∀ x, DifferentiableAt ℝ v.Ψb x := fun x =>
    (hv.smooth_Ψb.differentiable (by simp)) x
  have p1 : ∀ μ', eLpNorm (adCov A v.A μ') 2 μ ≤
      eLpNorm (fun x => pd v.A μ' x) 2 μ + ENNReal.ofReal (cA μ') * eLpNorm A 2 μ := by
    intro μ'
    refine eLpNorm_le_add_mul (by positivity) (hpdc hv.smooth_A μ').aestronglyMeasurable hA
      (fun x => ?_) (by norm_num)
    simp only [adCov]
    refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
    calc ‖adActL μ' (A x) (v.A x)‖ ≤ ‖adActL μ'‖ * ‖A x‖ * ‖v.A x‖ :=
          (adActL μ').le_opNorm₂ _ _
      _ ≤ ‖adActL μ'‖ * ‖A x‖ * Ma := by gcongr; exact hMa x
      _ = cA μ' * ‖A x‖ := by ring
  have p2 : ∀ μ', eLpNorm (fun x => covDerivHiggs A v.H x μ') 2 μ ≤
      eLpNorm (fun x => pd v.H μ' x) 2 μ + ENNReal.ofReal (2 * MH) * eLpNorm A 2 μ := by
    intro μ'
    refine eLpNorm_le_add_mul (by positivity) (hpdc hv.smooth_H μ').aestronglyMeasurable hA
      (fun x => ?_) (by norm_num)
    simp only [covDerivHiggs]
    refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
    calc ‖higgsAct (A x μ') (v.H x)‖ ≤ 2 * ‖A x μ'‖ * ‖v.H x‖ := norm_higgsAct_le _ _
      _ ≤ 2 * ‖A x‖ * MH := by
          gcongr
          · exact norm_le_pi_norm (A x) μ'
          · exact hMH x
      _ = 2 * MH * ‖A x‖ := by ring
  have p3 : ∀ μ', eLpNorm (spinCov5 A v.Ψ μ') 2 μ ≤
      eLpNorm (fun x => pd v.Ψ μ' x) 2 μ + ENNReal.ofReal (5 * MΨ) * eLpNorm A 2 μ := by
    intro μ'
    refine eLpNorm_le_add_mul (by positivity) (hpdc hv.smooth_Ψ μ').aestronglyMeasurable hA
      (fun x => ?_) (by norm_num)
    have e : spinCov5 A v.Ψ μ' x = pd v.Ψ μ' x + fun s => connM A μ' x *ᵥ v.Ψ x s := by
      funext s c
      simp only [spinCov5, covDerV, pdV, Pi.add_apply]
      rw [pd_apply_gen (differentiableAt_apply_gen (hdΨ x) s) μ' c, pd_apply_gen (hdΨ x) μ' s]
    rw [e]
    refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun s => ?_
    calc ‖connM A μ' x *ᵥ v.Ψ x s‖ ≤ 5 * ‖A x μ'‖ * ‖v.Ψ x s‖ := norm_of_mulVec_le _ _
      _ ≤ 5 * ‖A x‖ * MΨ := by
          gcongr
          · exact norm_le_pi_norm (A x) μ'
          · exact (norm_le_pi_norm (v.Ψ x) s).trans (hMΨ x)
      _ = 5 * MΨ * ‖A x‖ := by ring
  have p4 : ∀ μ', eLpNorm (cospinCov5 A v.Ψb μ') 2 μ ≤
      eLpNorm (fun x => pd v.Ψb μ' x) 2 μ + ENNReal.ofReal (5 * MΨb) * eLpNorm A 2 μ := by
    intro μ'
    refine eLpNorm_le_add_mul (by positivity) (hpdc hv.smooth_Ψb μ').aestronglyMeasurable hA
      (fun x => ?_) (by norm_num)
    have e : cospinCov5 A v.Ψb μ' x = pd v.Ψb μ' x +
        fun s => (-(Matrix.of (A x μ'))ᵀ) *ᵥ v.Ψb x s := by
      funext s c
      simp only [cospinCov5, covDerV, pdV, Pi.add_apply, dualConnM, connM]
      rw [pd_apply_gen (differentiableAt_apply_gen (hdΨb x) s) μ' c, pd_apply_gen (hdΨb x) μ' s]
    rw [e]
    refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun s => ?_
    calc ‖(-(Matrix.of (A x μ'))ᵀ) *ᵥ v.Ψb x s‖ ≤ 5 * ‖A x μ'‖ * ‖v.Ψb x s‖ :=
          norm_dual_mulVec_le _ _
      _ ≤ 5 * ‖A x‖ * MΨb := by
          gcongr
          · exact norm_le_pi_norm (A x) μ'
          · exact (norm_le_pi_norm (v.Ψb x) s).trans (hMΨb x)
      _ = 5 * MΨb * ‖A x‖ := by ring
  unfold nSize
  calc _ ≤ (eLpNorm v.e ⊤ μ + eLpNorm (fun x => fun i => pd v.e i x) ⊤ μ + eLpNorm v.A ⊤ μ +
        eLpNorm v.H ⊤ μ + eLpNorm v.Ψ ⊤ μ + eLpNorm v.Ψb ⊤ μ) +
        ∑ μ', ((eLpNorm (fun x => pd v.A μ' x) 2 μ + ENNReal.ofReal (cA μ') * eLpNorm A 2 μ) +
          (eLpNorm (fun x => pd v.H μ' x) 2 μ + ENNReal.ofReal (2 * MH) * eLpNorm A 2 μ) +
          (eLpNorm (fun x => pd v.Ψ μ' x) 2 μ + ENNReal.ofReal (5 * MΨ) * eLpNorm A 2 μ) +
          (eLpNorm (fun x => pd v.Ψb μ' x) 2 μ + ENNReal.ofReal (5 * MΨb) * eLpNorm A 2 μ)) :=
        add_le_add le_rfl (Finset.sum_le_sum fun μ' _ =>
          add_le_add (add_le_add (add_le_add (p1 μ') (p2 μ')) (p3 μ')) (p4 μ'))
    _ = C₀ + C₁ * eLpNorm A 2 μ := by
        simp only [C₀, C₁, Finset.sum_mul, add_mul, Finset.sum_add_distrib]
        ring

end RenewalGeometry.CriticalQuotientRows
