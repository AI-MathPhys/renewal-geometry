/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.UhlenbeckCubeGauge
import RenewalGeometry.Analysis.CubeNeumannSobolevAffine
import RenewalGeometry.Analysis.CubeGaffney

/-!
# Reduction of the cube Prop to the single cube `Q₀ = (0,1/2)⁴` by rescaling
  (stage D assembly, cube route)

Generic infrastructure for `prop:critical-uhlenbeck` of the Einstein–Standard-Model
action-closure manuscript.

The four-dimensional Yang–Mills energy and the `L⁴` norm of a connection are scale invariant, the
Coulomb condition is preserved by affine changes of variables and gauge transformations commute
with them.  Hence Uhlenbeck's theorem on all cubes `cubeC c r` follows from the theorem on the
single cube `Q₀` of the reflection framework (`CubeNeumann.Q0`), which is the target of stage C:

* `affConn z L A = L · A ∘ affMap z L` (pull-back of a connection by `x ↦ z + L x`);
  `entryGrad_affConn`, `curvVec_affConn` (`F_{affConn A}(x) = L² F_A(z + L x)`),
  `curvEnergy_affConn` (`∫_{affMap⁻¹ T} |F_{affConn A}|² = ∫_T |F_A|²`, scale invariance);
* `gaugeConn_comp_affInv`: `(Rh ∘ affInv)·A = L⁻¹ (Rh·affConn A) ∘ affInv`;
* `UhlenbeckQ0In m G 𝔤` — **Uhlenbeck's small-energy gauge theorem on `Q₀`** (the clauses of
  `UhlenbeckSmallEnergyGaugeCubeIn` for the one cube `Q₀`);
* `cubeIn_of_Q0In` (**reduction**): for `𝔤` closed under real scalars (a Lie algebra),
  `UhlenbeckQ0In m G 𝔤 → UhlenbeckSmallEnergyGaugeCubeIn m G 𝔤`, with `C_U` unchanged and
  `C_r = (4r + 1) C₀`.
-/

open MeasureTheory Filter Topology Set Matrix
open scoped ENNReal NNReal ContDiff

noncomputable section

namespace RenewalGeometry.UhlenbeckCube

open SobolevOpen CriticalGauge CriticalQuotient UhlenbeckGauge CubeNeumann

set_option linter.unusedSectionVars false

variable {m : ℕ} {z : Fin 4 → ℝ} {L : ℝ}

/-! ### Unconditional chain rules for affine maps -/

/-- Scaling by `L ≠ 0` as a continuous linear equivalence. -/
def scaleCLE (hL : L ≠ 0) : (Fin 4 → ℝ) ≃L[ℝ] (Fin 4 → ℝ) :=
  (LinearEquiv.smulOfNeZero ℝ (Fin 4 → ℝ) L hL).toContinuousLinearEquiv

theorem scaleCLE_apply (hL : L ≠ 0) (x : Fin 4 → ℝ) : scaleCLE hL x = L • x := rfl

theorem pd_comp_affMap' (hL : L ≠ 0) (f : (Fin 4 → ℝ) → ℂ) (i : Fin 4) (x : Fin 4 → ℝ) :
    pd (fun x => f (affMap z L x)) i x = (L : ℂ) * pd f i (affMap z L x) := by
  have e : (fun x => f (affMap z L x)) = (fun w => f (w + z)) ∘ scaleCLE hL := by
    funext x; simp [affMap, scaleCLE_apply, add_comm]
  unfold pd
  rw [e, ContinuousLinearEquiv.comp_right_fderiv, fderiv_comp_add_right]
  simp only [ContinuousLinearMap.coe_comp', ContinuousLinearEquiv.coe_coe, Function.comp_apply,
    scaleCLE_apply]
  rw [show L • (Pi.single i 1 : Fin 4 → ℝ) = L • Pi.single i 1 from rfl, map_smul,
    show L • x + z = affMap z L x by simp [affMap, add_comm], Complex.real_smul]

theorem pd_comp_affInv' (hL : L ≠ 0) (f : (Fin 4 → ℝ) → ℂ) (i : Fin 4) (y : Fin 4 → ℝ) :
    pd (fun y => f (affInv z L y)) i y = ((L⁻¹ : ℝ) : ℂ) * pd f i (affInv z L y) := by
  rw [affInv_eq_affMap]
  exact pd_comp_affMap' (inv_ne_zero hL) f i y

theorem pd_ofReal_mul (s : ℝ) (f : (Fin 4 → ℝ) → ℂ) (i : Fin 4) (x : Fin 4 → ℝ) :
    pd (fun y => (s : ℂ) * f y) i x = (s : ℂ) * pd f i x := by
  unfold pd
  have e : (fun y => (s : ℂ) * f y) = s • f := by funext y; simp [Complex.real_smul]
  rw [e, fderiv_const_smul_field]
  simp [Complex.real_smul]

/-! ### Pull-back of connections -/

/-- The pull-back `L · A(z + L x)` of a connection by the affine map `x ↦ z + L x`. -/
def affConn (z : Fin 4 → ℝ) (L : ℝ) (A : MConn m) : MConn m :=
  fun μ y => ((L : ℝ) : ℂ) • A μ (affMap z L y)

theorem entries_affConn (A : MConn m) (ν : Fin 4) (c e : Fin m) (y : Fin 4 → ℝ) :
    entries (affConn z L A) ν c e y = (L : ℂ) * entries A ν c e (affMap z L y) := by
  simp [entries, affConn, Matrix.smul_apply]

theorem entryGrad_affConn (hL : L ≠ 0) (A : MConn m) (ν : Fin 4) (c e : Fin m) (μ : Fin 4)
    (y : Fin 4 → ℝ) :
    entryGrad (affConn z L A) ν c e μ y = (L : ℂ) ^ 2 * entryGrad A ν c e μ (affMap z L y) := by
  have e1 : (fun y => affConn z L A ν y c e) =
      fun y => (L : ℂ) * (fun w => A ν w c e) (affMap z L y) := by
    funext y; exact entries_affConn A ν c e y
  simp only [entryGrad]
  have h2 := pd_comp_affMap' (z := z) hL (fun w => A ν w c e) μ y
  rw [e1, pd_ofReal_mul]
  simp only at h2 ⊢
  rw [h2]
  ring

/-- `F_{affConn A}(y) = L² F_A(z + L y)`. -/
theorem curvVec_affConn (hL : L ≠ 0) (A : MConn m) (y : Fin 4 → ℝ) :
    curvVec (affConn z L A) y = ((L : ℂ) ^ 2) • curvVec A (affMap z L y) := by
  ext p
  simp only [curvVec, curvatureW, PiLp.smul_apply, smul_eq_mul, entryGrad_affConn hL,
    entries_affConn]
  rw [mul_add, Finset.mul_sum]
  congr 1
  · ring
  · refine Finset.sum_congr rfl fun k _ => ?_
    ring

/-- **Scale invariance of the Yang–Mills energy under affine pull-back.** -/
theorem curvEnergy_affConn (hL : 0 < L) (A : MConn m) (T : Set (Fin 4 → ℝ)) :
    curvEnergy (affConn z L A) (affMap z L ⁻¹' T) = curvEnergy A T := by
  have hmp := measurePreserving_affine (ι := Fin 4) z hL
  simp only [Fintype.card_fin] at hmp
  have hemb : MeasurableEmbedding (affMap z L) := by
    have e : affMap z L = ⇑(affHomeo z hL.ne') := funext fun x => (affHomeo_apply hL.ne' x).symm
    rw [e]; exact (affHomeo z hL.ne').measurableEmbedding
  unfold curvEnergy
  have hpt : ∀ y, ‖curvVec (affConn z L A) y‖ₑ ^ 2 =
      ENNReal.ofReal (L ^ 4) * ‖curvVec A (affMap z L y)‖ₑ ^ 2 := by
    intro y
    rw [curvVec_affConn hL.ne', enorm_smul, mul_pow]
    congr 1
    rw [← ofReal_norm_eq_enorm, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL,
      ← ENNReal.ofReal_pow (by positivity)]
    ring_nf
  simp only [hpt]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have h := hmp.setLIntegral_comp_preimage_emb hemb (fun x => ‖curvVec A x‖ₑ ^ 2) T
  change ENNReal.ofReal (L ^ 4) * ∫⁻ a in (fun y => z + L • y) ⁻¹' T, ‖curvVec A (z + L • a)‖ₑ ^ 2 = _
  rw [h, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul, ← mul_assoc,
    ← ENNReal.ofReal_mul (by positivity), mul_inv_cancel₀ (by positivity), ENNReal.ofReal_one,
    one_mul]

theorem isSmoothUnitaryConn_affConn {A : MConn m} (hA : IsSmoothUnitaryConn A) (z : Fin 4 → ℝ)
    (L : ℝ) : IsSmoothUnitaryConn (affConn z L A) := by
  refine ⟨fun μ c e => ?_, fun μ y => ?_⟩
  · have e1 : (fun y => affConn z L A μ y c e) =
        fun y => (L : ℂ) * (fun w => A μ w c e) (affMap z L y) := by
      funext y; exact entries_affConn A μ c e y
    rw [e1]
    exact contDiff_const.mul ((hA.smooth μ c e).comp (contDiff_affMap z L))
  · simp only [affConn, star_smul, hA.skew, Complex.star_def, Complex.conj_ofReal, smul_neg]

/-! ### Gauge transformations and affine pull-back -/

theorem pdM_comp_affInv (hL : L ≠ 0) (R : (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ) (μ : Fin 4)
    (y : Fin 4 → ℝ) :
    pdM (fun y => R (affInv z L y)) μ y = ((L⁻¹ : ℝ) : ℂ) • pdM R μ (affInv z L y) := by
  ext c e
  simp only [pdM, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  exact pd_comp_affInv' hL (fun w => R w c e) μ y

/-- `(Rh ∘ affInv)·A = L⁻¹ (Rh·affConn A) ∘ affInv`. -/
theorem gaugeConn_comp_affInv (hL : L ≠ 0) (R : (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ)
    (A : MConn m) (μ : Fin 4) (y : Fin 4 → ℝ) :
    gaugeConn (fun y => R (affInv z L y)) A μ y =
      ((L⁻¹ : ℝ) : ℂ) • gaugeConn R (affConn z L A) μ (affInv z L y) := by
  simp only [gaugeConn, pdM_comp_affInv hL, affConn, affMap_affInv hL]
  rw [smul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul]
  congr 2
  rw [← Complex.ofReal_mul, inv_mul_cancel₀ hL, Complex.ofReal_one, one_smul]

theorem entries_gaugeConn_comp_affInv (hL : L ≠ 0) (R : (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ)
    (A : MConn m) (ν : Fin 4) (c e : Fin m) :
    entries (gaugeConn (fun y => R (affInv z L y)) A) ν c e =
      fun y => ((L⁻¹ : ℝ) : ℂ) * entries (gaugeConn R (affConn z L A)) ν c e (affInv z L y) := by
  funext y
  simp [entries, gaugeConn_comp_affInv hL, Matrix.smul_apply]

theorem entryGrad_gaugeConn_comp_affInv (hL : L ≠ 0)
    (R : (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ) (A : MConn m) (ν : Fin 4) (c e : Fin m)
    (μ : Fin 4) (y : Fin 4 → ℝ) :
    entryGrad (gaugeConn (fun y => R (affInv z L y)) A) ν c e μ y =
      ((L⁻¹ : ℝ) : ℂ) * (((L⁻¹ : ℝ) : ℂ) *
        entryGrad (gaugeConn R (affConn z L A)) ν c e μ (affInv z L y)) := by
  have e1 : (fun y => gaugeConn (fun y => R (affInv z L y)) A ν y c e) =
      fun y => ((L⁻¹ : ℝ) : ℂ) * (fun w => gaugeConn R (affConn z L A) ν w c e) (affInv z L y) :=
    entries_gaugeConn_comp_affInv hL R A ν c e
  simp only [entryGrad]
  have h2 := pd_comp_affInv' (z := z) hL (fun w => gaugeConn R (affConn z L A) ν w c e) μ y
  rw [e1, pd_ofReal_mul]
  simp only at h2 ⊢
  rw [h2]

/-! ### `W^{1,2}` with constant factors -/

theorem memW12_const_mul {Ω : Set (Fin 4 → ℝ)} {u : (Fin 4 → ℝ) → ℂ}
    {g : Fin 4 → (Fin 4 → ℝ) → ℂ} (hW : MemW12 Ω u g) (s : ℂ) :
    MemW12 Ω (fun x => s * u x) (fun i x => s * g i x) := by
  refine ⟨hW.memLp.const_mul s, fun i => (hW.memLp_grad i).const_mul s, fun i φ hφ => ?_⟩
  have h := hW.weak i φ hφ
  have e1 : (fun x => ((pd φ i x : ℝ) : ℂ) * (s * u x)) =
      fun x => s * (((pd φ i x : ℝ) : ℂ) * u x) := by funext x; ring
  have e2 : (fun x => ((φ x : ℝ) : ℂ) * (s * g i x)) = fun x => s * (((φ x : ℝ) : ℂ) * g i x) := by
    funext x; ring
  rw [e1, e2, integral_const_mul, integral_const_mul, h]; ring

theorem w12Norm_const_mul {Ω : Set (Fin 4 → ℝ)} (u : (Fin 4 → ℝ) → ℂ)
    (g : Fin 4 → (Fin 4 → ℝ) → ℂ) (s : ℂ) :
    w12Norm Ω (fun x => s * u x) (fun i x => s * g i x) = ‖s‖ₑ * w12Norm Ω u g := by
  unfold w12Norm
  rw [show (fun x => s * u x) = s • u from rfl, eLpNorm_const_smul, mul_add, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show (fun i x => s * g i x) i = s • g i from rfl, eLpNorm_const_smul]

/-! ### The theorem on `Q₀` and the reduction -/

/-- **Uhlenbeck's small-energy gauge theorem on the cube `Q₀ = (0,1/2)⁴`** (the stage-C target
of the reflection framework): the clauses of `UhlenbeckSmallEnergyGaugeCubeIn` for the single
cube `Q₀`. -/
def UhlenbeckQ0In (m : ℕ) (G 𝔤 : Set (Matrix (Fin m) (Fin m) ℂ)) : Prop :=
  ∃ εU : ℝ≥0, 0 < εU ∧ ∃ CU C0 : ℝ≥0,
    ∀ A : MConn m, IsSmoothUnitaryConn A → (∀ μ y, A μ y ∈ 𝔤) → curvEnergy A Q0 ≤ εU →
      ∃ R : (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ,
        (∀ y ∈ Q0, R y ∈ G) ∧
        (∀ c' e', ContDiffOn ℝ ∞ (fun y => R y c' e') Q0) ∧
        (∀ x ∈ Q0, ∀ c' e', ∑ μ, entryGrad (gaugeConn R A) μ c' e' μ x = 0) ∧
        (∀ ν c' e', MemW12 Q0 (entries (gaugeConn R A) ν c' e')
          (entryGrad (gaugeConn R A) ν c' e')) ∧
        (∀ ν c' e', w12Norm Q0 (entries (gaugeConn R A) ν c' e')
          (entryGrad (gaugeConn R A) ν c' e') ≤ C0 * curvEnergy A Q0 ^ (1 / 2 : ℝ)) ∧
        (∀ ν c' e', eLpNorm (entries (gaugeConn R A) ν c' e') 4 (volume.restrict Q0) ≤
          CU * curvEnergy A Q0 ^ (1 / 2 : ℝ))

theorem affMap_preimage_cubeC (c : Fin 4 → ℝ) {r : ℝ} (hr : 0 < r) :
    affMap (fun i => c i - r) (4 * r) ⁻¹' cubeC c r = Q0 := by
  ext y
  simp only [mem_preimage, cubeC, mem_box, affMap, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Pi.zero_apply, halfB]
  refine forall_congr' fun i => ?_
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> nlinarith
  · rintro ⟨h1, h2⟩; constructor <;> nlinarith

theorem affInv_preimage_Q0 (c : Fin 4 → ℝ) {r : ℝ} (hr : 0 < r) :
    affInv (fun i => c i - r) (4 * r) ⁻¹' Q0 = cubeC c r := by
  rw [preimage_affInv_eq_image (by positivity), ← affMap_preimage_cubeC c hr,
    image_preimage_eq _ ?_]
  intro y; exact ⟨affInv _ _ y, affMap_affInv (by positivity) y⟩

/-- **Reduction of Uhlenbeck's theorem on cubes to the single cube `Q₀`** by affine rescaling
(scale invariance of the energy and of the `L⁴` norm). -/
theorem cubeIn_of_Q0In {G 𝔤 : Set (Matrix (Fin m) (Fin m) ℂ)}
    (h𝔤 : ∀ (s : ℝ), ∀ X ∈ 𝔤, (s : ℂ) • X ∈ 𝔤) (hQ : UhlenbeckQ0In m G 𝔤) :
    UhlenbeckSmallEnergyGaugeCubeIn m G 𝔤 := by
  obtain ⟨εU, hεU, CU, C0, hU⟩ := hQ
  refine ⟨εU, hεU, CU, fun c r hr => ?_⟩
  set L : ℝ := 4 * r
  have hL : 0 < L := by positivity
  set z : Fin 4 → ℝ := fun i => c i - r
  refine ⟨C0 * (L + 1).toNNReal, fun A hA h𝔤A hE => ?_⟩
  set Ah := affConn z L A
  have hEeq : curvEnergy Ah Q0 = curvEnergy A (cubeC c r) := by
    rw [← affMap_preimage_cubeC c hr]; exact curvEnergy_affConn hL A _
  obtain ⟨Rh, hRG, hRs, hRC, hRW, hRw, hR4⟩ := hU Ah (isSmoothUnitaryConn_affConn hA z L)
    (fun μ y => h𝔤 L _ (h𝔤A μ _)) (hEeq ▸ hE)
  rw [hEeq] at hRw hR4
  set R : (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ := fun y => Rh (affInv z L y)
  have hmaps : ∀ y ∈ cubeC c r, affInv z L y ∈ Q0 := fun y hy => by
    rw [← affInv_preimage_Q0 c hr] at hy; exact hy
  have hpre : affInv z L ⁻¹' Q0 = cubeC c r := affInv_preimage_Q0 c hr
  have hLinv : ‖((L⁻¹ : ℝ) : ℂ)‖ₑ = ENNReal.ofReal L⁻¹ := by
    rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.2 hL)]
  refine ⟨R, fun y hy => hRG _ (hmaps y hy), fun c' e' => ?_, fun x hx c' e' => ?_,
    fun ν c' e' => ?_, fun ν c' e' => ?_, fun ν c' e' => ?_⟩
  · exact (hRs c' e').comp (contDiff_affInv z L).contDiffOn hmaps
  · simp only [R, entryGrad_gaugeConn_comp_affInv hL.ne']
    rw [← Finset.mul_sum, ← Finset.mul_sum, hRC _ (hmaps x hx) c' e', mul_zero, mul_zero]
  · have h1 := memW12_comp_affInv (z := z) hL (hRW ν c' e')
    rw [hpre] at h1
    have h2 := memW12_const_mul h1 ((L⁻¹ : ℝ) : ℂ)
    rw [entries_gaugeConn_comp_affInv hL.ne']
    convert h2 using 2
    funext y
    exact entryGrad_gaugeConn_comp_affInv hL.ne' Rh A ν c' e' _ y
  · -- the `W^{1,2}` bound
    rw [entries_gaugeConn_comp_affInv hL.ne']
    have hg : (entryGrad (gaugeConn R A) ν c' e') = fun i y => ((L⁻¹ : ℝ) : ℂ) *
        (((L⁻¹ : ℝ) : ℂ) * entryGrad (gaugeConn Rh Ah) ν c' e' i (affInv z L y)) := by
      funext i y; exact entryGrad_gaugeConn_comp_affInv hL.ne' Rh A ν c' e' i y
    rw [hg, w12Norm_const_mul, hLinv]
    have hW := hRW ν c' e'
    have hu := memLp_comp_affInv (z := z) hL (by norm_num) hW.memLp
    have hgi := fun i => memLp_comp_affInv (z := z) hL (by norm_num) (hW.memLp_grad i)
    rw [hpre] at hu
    simp only [hpre] at hgi
    unfold w12Norm
    have e2 : ∀ i, eLpNorm (fun y => ((L⁻¹ : ℝ) : ℂ) * entryGrad (gaugeConn Rh Ah) ν c' e' i
        (affInv z L y)) 2 (volume.restrict (cubeC c r)) =
        ENNReal.ofReal L⁻¹ * (ENNReal.ofReal (L ^ 4) ^ (1 / (2 : ℝ≥0∞)).toReal *
          eLpNorm (entryGrad (gaugeConn Rh Ah) ν c' e' i) 2 (volume.restrict Q0)) := by
      intro i
      rw [show (fun y => ((L⁻¹ : ℝ) : ℂ) * entryGrad (gaugeConn Rh Ah) ν c' e' i (affInv z L y)) =
        ((L⁻¹ : ℝ) : ℂ) • fun y => entryGrad (gaugeConn Rh Ah) ν c' e' i (affInv z L y) from rfl,
        eLpNorm_const_smul, hLinv, (hgi i).2]
    rw [hu.2]
    simp only [e2]
    have hsq : ENNReal.ofReal (L ^ 4) ^ (1 / (2 : ℝ≥0∞)).toReal = ENNReal.ofReal (L ^ 2) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
      congr 1
      rw [show (1 / (2 : ℝ≥0∞)).toReal = 1 / 2 by norm_num, ← Real.rpow_natCast,
        ← Real.rpow_mul hL.le]
      norm_num
    rw [hsq]
    set W0 := w12Norm Q0 (entries (gaugeConn Rh Ah) ν c' e') (entryGrad (gaugeConn Rh Ah) ν c' e')
    have hW0 := hRw ν c' e'
    -- `L⁻¹ (L² ‖u‖ + Σ L⁻¹ L² ‖g‖) ≤ (L + 1) W0`
    have hcoef1 : ENNReal.ofReal L⁻¹ * ENNReal.ofReal (L ^ 2) = ENNReal.ofReal L := by
      rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; field_simp
    have hcoef2 : ENNReal.ofReal L⁻¹ * ENNReal.ofReal L⁻¹ * ENNReal.ofReal (L ^ 2) = 1 := by
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      rw [show L⁻¹ * L⁻¹ * L ^ 2 = 1 by field_simp]; simp
    calc ENNReal.ofReal L⁻¹ * (ENNReal.ofReal (L ^ 2) *
          eLpNorm (entries (gaugeConn Rh Ah) ν c' e') 2 (volume.restrict Q0) +
          ∑ i, ENNReal.ofReal L⁻¹ * (ENNReal.ofReal (L ^ 2) *
            eLpNorm (entryGrad (gaugeConn Rh Ah) ν c' e' i) 2 (volume.restrict Q0)))
        = ENNReal.ofReal L * eLpNorm (entries (gaugeConn Rh Ah) ν c' e') 2 (volume.restrict Q0) +
          ∑ i, eLpNorm (entryGrad (gaugeConn Rh Ah) ν c' e' i) 2 (volume.restrict Q0) := by
          rw [mul_add, ← mul_assoc, hcoef1, Finset.mul_sum]
          congr 1
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← mul_assoc, ← mul_assoc, hcoef2, one_mul]
      _ ≤ (ENNReal.ofReal L + 1) * W0 := by
          unfold W0 w12Norm
          rw [add_mul, one_mul, mul_add]
          gcongr ?_ + ?_
          · exact le_self_add
          · exact le_add_left le_rfl
      _ ≤ (ENNReal.ofReal L + 1) * (C0 * curvEnergy A (cubeC c r) ^ (1 / 2 : ℝ)) := by gcongr
      _ = ((C0 * (L + 1).toNNReal : ℝ≥0) : ℝ≥0∞) * curvEnergy A (cubeC c r) ^ (1 / 2 : ℝ) := by
          have hc : ((C0 * (L + 1).toNNReal : ℝ≥0) : ℝ≥0∞) = C0 * (ENNReal.ofReal L + 1) := by
            rw [ENNReal.coe_mul]
            congr 1
            rw [show (((L + 1).toNNReal : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (L + 1) from rfl,
              ENNReal.ofReal_add hL.le zero_le_one, ENNReal.ofReal_one]
          rw [hc]; ring
  · -- the `L⁴` bound (scale invariant)
    rw [entries_gaugeConn_comp_affInv hL.ne']
    have hm4 : MemLp (entries (gaugeConn Rh Ah) ν c' e') 4 (volume.restrict Q0) :=
      (sobolev_cube (hRW ν c' e')).1
    have h4 := memLp_comp_affInv (z := z) hL (by norm_num) hm4
    rw [hpre] at h4
    rw [show (fun y => ((L⁻¹ : ℝ) : ℂ) * entries (gaugeConn Rh Ah) ν c' e' (affInv z L y)) =
      ((L⁻¹ : ℝ) : ℂ) • fun y => entries (gaugeConn Rh Ah) ν c' e' (affInv z L y) from rfl,
      eLpNorm_const_smul, hLinv, h4.2]
    have hq : ENNReal.ofReal (L ^ 4) ^ (1 / (4 : ℝ≥0∞)).toReal = ENNReal.ofReal L := by
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
      congr 1
      rw [show (1 / (4 : ℝ≥0∞)).toReal = 1 / 4 by norm_num, ← Real.rpow_natCast,
        ← Real.rpow_mul hL.le]
      norm_num
    rw [hq, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ hL.ne',
      ENNReal.ofReal_one, one_mul]
    exact hR4 ν c' e'

end RenewalGeometry.UhlenbeckCube
