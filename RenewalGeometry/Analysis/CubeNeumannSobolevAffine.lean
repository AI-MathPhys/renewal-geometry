/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.CubeNeumannSobolev

/-!
# `W^{1,2}` and `L^p` under affine changes of variables of `ℝ⁴`
  (stage D support: transferring the cube `Q₀ = (0,1/2)⁴` to arbitrary cubes)

Generic infrastructure (no renewal notions) for `prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript.

For `L > 0` and `z ∈ ℝ⁴`, `affMap z L x = z + L x` and its inverse `affInv z L y = L⁻¹(y - z)`:

* `pd_comp_affMap`: `∂_i (f ∘ affMap) = L (∂_i f) ∘ affMap` (chain rule);
* `hasWeakPartial_comp_affInv`: if `g` is the weak `i`-th partial of `u` on an open `Ω`, then
  `L⁻¹ g ∘ affInv` is the weak `i`-th partial of `u ∘ affInv` on `affInv⁻¹' Ω = affMap '' Ω`;
* `memLp_comp_affInv`, `eLpNorm_comp_affInv`: `‖u ∘ affInv‖_{L^p(affInv⁻¹'Ω)} = L^{4/p} ‖u‖_{L^p(Ω)}`;
* `memW12_comp_affInv`: `W^{1,2}` is preserved.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff

noncomputable section

namespace RenewalGeometry.CubeNeumann

open SobolevOpen

set_option linter.unusedSectionVars false

/-- The affine map `x ↦ z + L x`. -/
def affMap (z : Fin 4 → ℝ) (L : ℝ) (x : Fin 4 → ℝ) : Fin 4 → ℝ := z + L • x

/-- Its inverse `y ↦ L⁻¹ (y - z)`. -/
def affInv (z : Fin 4 → ℝ) (L : ℝ) (y : Fin 4 → ℝ) : Fin 4 → ℝ := L⁻¹ • (y - z)

variable {z : Fin 4 → ℝ} {L : ℝ}

theorem affMap_affInv (hL : L ≠ 0) (y : Fin 4 → ℝ) : affMap z L (affInv z L y) = y := by
  simp [affMap, affInv, smul_smul, mul_inv_cancel₀ hL]

theorem affInv_affMap (hL : L ≠ 0) (x : Fin 4 → ℝ) : affInv z L (affMap z L x) = x := by
  simp [affMap, affInv, smul_smul, inv_mul_cancel₀ hL]

theorem affInv_eq_affMap (z : Fin 4 → ℝ) (L : ℝ) :
    affInv z L = affMap (-(L⁻¹ • z)) L⁻¹ := by
  funext y; simp [affInv, affMap, smul_sub]; abel

/-- The affine map as a homeomorphism. -/
def affHomeo (z : Fin 4 → ℝ) (hL : L ≠ 0) : (Fin 4 → ℝ) ≃ₜ (Fin 4 → ℝ) :=
  (Homeomorph.smulOfNeZero L hL).trans (Homeomorph.addLeft z)

theorem affHomeo_apply (hL : L ≠ 0) (x : Fin 4 → ℝ) : affHomeo z hL x = affMap z L x := by
  simp [affHomeo, affMap]

theorem contDiff_affMap (z : Fin 4 → ℝ) (L : ℝ) : ContDiff ℝ ∞ (affMap z L) := by
  unfold affMap; fun_prop

theorem contDiff_affInv (z : Fin 4 → ℝ) (L : ℝ) : ContDiff ℝ ∞ (affInv z L) := by
  unfold affInv; fun_prop

theorem hasFDerivAt_affMap (z : Fin 4 → ℝ) (L : ℝ) (x : Fin 4 → ℝ) :
    HasFDerivAt (affMap z L) (L • ContinuousLinearMap.id ℝ (Fin 4 → ℝ)) x := by
  have h1 : HasFDerivAt (fun x : Fin 4 → ℝ => (L • ContinuousLinearMap.id ℝ (Fin 4 → ℝ)) x)
      (L • ContinuousLinearMap.id ℝ (Fin 4 → ℝ)) x :=
    (L • ContinuousLinearMap.id ℝ (Fin 4 → ℝ)).hasFDerivAt
  have := h1.const_add z
  simpa [affMap] using this

/-- **Chain rule for affine maps**: `∂_i (f ∘ affMap) = L (∂_i f) ∘ affMap`. -/
theorem pd_comp_affMap {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : (Fin 4 → ℝ) → F} {x : Fin 4 → ℝ} (hf : DifferentiableAt ℝ f (affMap z L x)) (i : Fin 4) :
    pd (fun x => f (affMap z L x)) i x = L • pd f i (affMap z L x) := by
  have h := hf.hasFDerivAt.comp x (hasFDerivAt_affMap z L x)
  unfold pd
  rw [show (fun x => f (affMap z L x)) = f ∘ affMap z L from rfl, h.fderiv]
  simp

/-- **Weak derivatives under affine changes of variables.** -/
theorem hasWeakPartial_comp_affInv (hL : 0 < L) {Ω : Set (Fin 4 → ℝ)} {i : Fin 4}
    {u g : (Fin 4 → ℝ) → ℂ} (h : HasWeakPartial Ω i u g) :
    HasWeakPartial (affInv z L ⁻¹' Ω) i (fun y => u (affInv z L y))
      (fun y => ((L⁻¹ : ℝ) : ℂ) * g (affInv z L y)) := by
  intro φ hφ
  set ψ : (Fin 4 → ℝ) → ℝ := fun x => φ (affMap z L x)
  have hψ : IsTest Ω ψ := by
    refine ⟨hφ.smooth.comp (contDiff_affMap z L), ?_, ?_⟩
    · have := hφ.compact.comp_homeomorph (affHomeo z hL.ne')
      convert this using 1
      funext x; simp [ψ, affHomeo_apply]
    · intro x hx
      have hx' : affMap z L x ∈ tsupport φ := by
        have h1 : tsupport ψ = (affHomeo z hL.ne') ⁻¹' tsupport φ := by
          have := tsupport_comp_eq_preimage φ (affHomeo z hL.ne')
          convert this using 2
          funext x; simp [ψ, affHomeo_apply]
        rw [h1] at hx
        simpa [affHomeo_apply] using hx
      have := hφ.subset hx'
      simpa [affInv_affMap hL.ne'] using this
  have key := h ψ hψ
  have hpdψ : ∀ x, pd ψ i x = L * pd φ i (affMap z L x) := fun x => by
    have := pd_comp_affMap (z := z) (L := L)
      ((hφ.smooth.differentiable (by simp)) (affMap z L x)) i (x := x)
    simpa [ψ, smul_eq_mul] using this
  have hcv : ∀ f : (Fin 4 → ℝ) → ℂ, ∫ y, f y = ((L ^ 4 : ℝ) : ℂ) * ∫ x, f (affMap z L x) := by
    intro f
    have := integral_comp_affine (ι := Fin 4) f z hL
    simp only [Fintype.card_fin] at this
    rw [show (fun x => f (affMap z L x)) = fun x => f (z + L • x) from rfl, this]
    rw [Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ (by positivity),
      Complex.ofReal_one, one_mul]
  have L1 := hcv (fun y => ((pd φ i y : ℝ) : ℂ) * u (affInv z L y))
  have R1 := hcv (fun y => ((φ y : ℝ) : ℂ) * (((L⁻¹ : ℝ) : ℂ) * g (affInv z L y)))
  simp only [affInv_affMap hL.ne'] at L1 R1
  rw [L1, R1]
  have hL0 : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have e1 : (fun x => ((pd φ i (affMap z L x) : ℝ) : ℂ) * u x) =
      fun x => ((L⁻¹ : ℝ) : ℂ) * (((pd ψ i x : ℝ) : ℂ) * u x) := by
    funext x; rw [hpdψ x]; push_cast; field_simp
  have e2 : (fun x => ((φ (affMap z L x) : ℝ) : ℂ) * (((L⁻¹ : ℝ) : ℂ) * g x)) =
      fun x => ((L⁻¹ : ℝ) : ℂ) * (((ψ x : ℝ) : ℂ) * g x) := by
    funext x; simp only [ψ]; ring
  rw [e1, e2, integral_const_mul, integral_const_mul, key]
  ring

theorem measurePreserving_affInv_restrict (hL : 0 < L) (Ω : Set (Fin 4 → ℝ)) :
    MeasurePreserving (affInv z L) (volume.restrict (affInv z L ⁻¹' Ω))
      ((ENNReal.ofReal (L ^ 4) • volume).restrict Ω) := by
  have hL' : 0 < L⁻¹ := inv_pos.2 hL
  have hmp := measurePreserving_affine (ι := Fin 4) (-(L⁻¹ • z)) hL'
  simp only [Fintype.card_fin, inv_pow, inv_inv] at hmp
  rw [show (fun y : Fin 4 → ℝ => -(L⁻¹ • z) + L⁻¹ • y) = affInv z L by
    rw [affInv_eq_affMap]; rfl] at hmp
  have hemb : MeasurableEmbedding (affInv z L) := by
    have e : affInv z L = ⇑(affHomeo (-(L⁻¹ • z)) hL'.ne') := by
      rw [affInv_eq_affMap]; funext y; exact (affHomeo_apply hL'.ne' y).symm
    rw [e]; exact (affHomeo (-(L⁻¹ • z)) hL'.ne').measurableEmbedding
  exact hmp.restrict_preimage_emb hemb Ω

/-- **`L^p` under affine changes of variables** (`p ≠ ∞`). -/
theorem memLp_comp_affInv (hL : 0 < L) {Ω : Set (Fin 4 → ℝ)} {u : (Fin 4 → ℝ) → ℂ}
    {p : ℝ≥0∞} (hp : p ≠ ⊤) (hu : MemLp u p (volume.restrict Ω)) :
    MemLp (fun y => u (affInv z L y)) p (volume.restrict (affInv z L ⁻¹' Ω)) ∧
      eLpNorm (fun y => u (affInv z L y)) p (volume.restrict (affInv z L ⁻¹' Ω)) =
        ENNReal.ofReal (L ^ 4) ^ (1 / p).toReal * eLpNorm u p (volume.restrict Ω) := by
  have hmp := measurePreserving_affInv_restrict (z := z) hL Ω
  have hu' : MemLp u p ((ENNReal.ofReal (L ^ 4) • volume).restrict Ω) := by
    rw [Measure.restrict_smul]; exact hu.smul_measure ENNReal.ofReal_ne_top
  refine ⟨hu'.comp_measurePreserving hmp, ?_⟩
  rw [show (fun y => u (affInv z L y)) = u ∘ affInv z L from rfl,
    eLpNorm_comp_measurePreserving hu'.1 hmp, Measure.restrict_smul,
    eLpNorm_smul_measure_of_ne_top hp]
  rfl

/-- **`W^{1,2}` under affine changes of variables.** -/
theorem memW12_comp_affInv (hL : 0 < L) {Ω : Set (Fin 4 → ℝ)} {u : (Fin 4 → ℝ) → ℂ}
    {g : Fin 4 → (Fin 4 → ℝ) → ℂ} (hW : MemW12 Ω u g) :
    MemW12 (affInv z L ⁻¹' Ω) (fun y => u (affInv z L y))
      (fun i y => ((L⁻¹ : ℝ) : ℂ) * g i (affInv z L y)) :=
  ⟨(memLp_comp_affInv hL (by norm_num) hW.memLp).1, fun i =>
    ((memLp_comp_affInv hL (by norm_num) (hW.memLp_grad i)).1).const_mul _,
    fun i => hasWeakPartial_comp_affInv hL (hW.weak i)⟩

theorem preimage_affInv_eq_image (hL : L ≠ 0) (Ω : Set (Fin 4 → ℝ)) :
    affInv z L ⁻¹' Ω = affMap z L '' Ω := by
  ext y
  constructor
  · intro hy; exact ⟨affInv z L y, hy, affMap_affInv hL y⟩
  · rintro ⟨x, hx, rfl⟩; simpa [mem_preimage, affInv_affMap hL] using hx

end RenewalGeometry.CubeNeumann
