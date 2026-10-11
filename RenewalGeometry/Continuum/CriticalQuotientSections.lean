/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.CriticalQuotientChart

/-!
# Standard-Model matter as sections of the defining representation
  (`thm:critical-quotient-defect`; Einstein–Standard-Model action-closure manuscript)

The Coulomb-chart extraction transports sections of the defining representation `ℂ³ ⊕ ℂ²` of
`G_SM`.  The Standard-Model matter of the defining-carrier rendering is organized as such
sections (`matterSec`): the Higgs doublet embedded in the weak block, the spinor components
`Ψ_s` (`s` the Dirac index), and the complex conjugates of the dual-spinor components `Ψ̄_s`
(which transform in the defining representation because `Ψ̄ ↦ Ψ̄ R^*`).

* `covDerV_matterSec_*`: the covariant derivatives of these sections are the embedded
  `D_AH` (block-diagonal `A`), the spinor derivative `∇^{ref,A}Ψ` and the conjugate of the dual
  derivative `∇^{ref,A}Ψ̄` (flat reference connection): the hypothesis (Q3)/(Q4) in the
  `covDerV` form is exactly `eq:critical-spinor-bound` and the Higgs bound of (Q3);
* `redJet_gaugeTuple_*`: every slot of the reduced jet of the gauge-transformed fields is read off
  from the transported sections `R u`, their classical derivatives `tgrad`, the entries of the
  Coulomb connection and its curvature.
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

/-- Index of the matter sections: the Higgs doublet (`none`), the spinor components `Ψ_s`
(`some (inl s)`) and the conjugated dual-spinor components (`some (inr s)`). -/
abbrev MIdx : Type := Option (Fin 4 ⊕ Fin 4)

/-- **The matter sections** of a field tuple in the defining representation `ℂ³ ⊕ ℂ²`. -/
def matterSec (z : FieldTuple (Fin 5)) : MIdx → E4 → Fin 5 → ℂ
  | none => fun y => embH (z.H y)
  | some (Sum.inl s) => fun y => z.Ψ y s
  | some (Sum.inr s) => fun y c => star (z.Ψb y s c)

theorem contDiff_matterSec {z : FieldTuple (Fin 5)} (hH : ContDiff ℝ ∞ z.H)
    (hΨ : ContDiff ℝ ∞ z.Ψ) (hΨb : ContDiff ℝ ∞ z.Ψb) (s : MIdx) : ContDiff ℝ ∞ (matterSec z s) := by
  rcases s with _ | s | s
  · exact embHL.contDiff.comp hH
  · exact contDiff_pi.mpr fun c => (contDiff_apply ℝ ℂ c).comp ((contDiff_apply ℝ _ s).comp hΨ)
  · refine contDiff_pi.mpr fun c => ?_
    have h1 : ContDiff ℝ ∞ (fun y => z.Ψb y s c) :=
      (contDiff_apply ℝ ℂ c).comp ((contDiff_apply ℝ _ s).comp hΨb)
    have e : (fun y => matterSec z (some (Sum.inr s)) y c) =
        Complex.conjCLE ∘ (fun y => z.Ψb y s c) := by
      funext y; simp [matterSec, Complex.conjCLE_apply]
    rw [e]
    exact (Complex.conjCLE.contDiff (n := ∞)).comp h1

theorem pd_star_complex {f : E4 → ℂ} {x : E4} (hf : DifferentiableAt ℝ f x) (μ : Fin 4) :
    pd (fun y => star (f y)) μ x = star (pd f μ x) :=
  pd_conj_complex hf μ

/-! ### Covariant derivatives of the matter sections -/

theorem embH_covDerivHiggs {A : E4 → ConnFibre} {H : E4 → HiggsFibre} {x : E4}
    (hA : ∀ μ, IsSMBlock (Matrix.of (A x μ))) (hH : DifferentiableAt ℝ H x) (μ : Fin 4) :
    covDerV (connM A) (fun y => embH (H y)) μ x = embH (covDerivHiggs A H x μ) := by
  funext k
  refine Fin.addCases (m := 3) (n := 2)
    (motive := fun k => covDerV (connM A) (fun y => embH (H y)) μ x k =
      embH (covDerivHiggs A H x μ) k) (fun k => ?_) (fun k => ?_) k
  · rw [embH_castAdd]
    simp only [covDerV, Pi.add_apply, pdV, embH_castAdd]
    rw [pd_eq_zero_of_eventually (Eventually.of_forall fun y => rfl), zero_add]
    simp only [mulVec, dotProduct, connM]
    rw [sum_fin5]
    simp only [embH_castAdd, mul_zero, Finset.sum_const_zero, zero_add, embH_natAdd]
    exact Finset.sum_eq_zero fun j _ => by
      rw [hA μ _ _ (by rw [colourBlock_castAdd, colourBlock_natAdd]; decide), zero_mul]
  · rw [embH_natAdd, covDerivHiggs_eq_proj hH]
    rfl

/-- The Higgs section: `∇^A(H ↪ ℂ³ ⊕ ℂ²) = (0, D_AH)` for `𝔰(𝔲(3) ⊕ 𝔲(2))`-valued `A`. -/
theorem covDerV_matterSec_higgs {z : FieldTuple (Fin 5)} {x : E4}
    (hA : ∀ μ, z.A x μ ∈ smLie) (hH : DifferentiableAt ℝ z.H x) (μ : Fin 4) :
    covDerV (connM z.A) (matterSec z none) μ x = embH (covDerivHiggs z.A z.H x μ) :=
  embH_covDerivHiggs (fun μ => ((mem_gSM_iff (z.A x μ)).2 (hA μ)).2.1) hH μ

/-- The spinor sections: `∇^A Ψ_s` (flat reference spin connection). -/
theorem covDerV_matterSec_spin (z : FieldTuple (Fin 5)) (x : E4) (μ s : Fin 4) :
    covDerV (connM z.A) (matterSec z (some (Sum.inl s))) μ x = spinCov5 z.A z.Ψ μ x s := rfl

/-- The conjugated dual-spinor sections: `∇^A(Ψ̄_s^*) = (∇^A Ψ̄)_s^*` for skew-Hermitian `A`. -/
theorem covDerV_matterSec_cospin {z : FieldTuple (Fin 5)} {x : E4}
    (hA : ∀ μ, z.A x μ ∈ smLie) (hΨb : DifferentiableAt ℝ z.Ψb x) (μ s : Fin 4) (c : Fin 5) :
    covDerV (connM z.A) (matterSec z (some (Sum.inr s))) μ x c =
      star (cospinCov5 z.A z.Ψb μ x s c) := by
  have hd : DifferentiableAt ℝ (fun y => z.Ψb y s c) x :=
    differentiableAt_apply_gen (differentiableAt_apply_gen hΨb s) c
  simp only [cospinCov5, covDerV, Pi.add_apply, pdV, matterSec, mulVec, dotProduct, connM,
    dualConnM, of_apply, Matrix.neg_apply, transpose_apply, star_add, star_sum, star_mul',
    star_neg]
  rw [pd_star_complex hd]
  congr 1
  refine Finset.sum_congr rfl fun d _ => ?_
  have hs := (hA μ).1 d c
  rw [hs]

/-! ### The reduced jet of the transformed fields from the transported sections -/

section Jets

variable {R : E4 → M5} {z : FieldTuple (Fin 5)}

theorem gaugeTuple_H_eq (y : E4) :
    (gaugeTuple R z).H y = projH (fun c => transp R (matterSec z none) c y) := by
  show higgsG (R y) (z.H y) = projH (R y *ᵥ embH (z.H y))
  rw [higgsG_eq_proj]

theorem gaugeTuple_Ψ_eq (y : E4) (s : Fin 4) (c : Fin 5) :
    (gaugeTuple R z).Ψ y s c = transp R (matterSec z (some (Sum.inl s))) c y := rfl

theorem gaugeTuple_Ψb_eq (y : E4) (s : Fin 4) (c : Fin 5) :
    (gaugeTuple R z).Ψb y s c = star (transp R (matterSec z (some (Sum.inr s))) c y) := by
  show ((star (R y))ᵀ *ᵥ z.Ψb y s) c = star ((R y *ᵥ fun c => star (z.Ψb y s c)) c)
  simp only [mulVec, dotProduct, transpose_apply, star_apply, star_sum, star_mul', star_star]

theorem redJet_gaugeTuple_A (x : E4) (μ : Fin 4) (c e : Fin 5) :
    (redJet (gaugeTuple R z) x).A μ c e = entries (gaugeConn R (connM z.A)) μ c e x := rfl

theorem redJet_gaugeTuple_F {x : E4} (hR : GaugeAt R x) (hA : DifferentiableAt ℝ z.A x)
    (μ ν : Fin 4) (c e : Fin 5) :
    (redJet (gaugeTuple R z) x).F μ ν c e =
      curvatureW (entries (gaugeConn R (connM z.A))) (entryGrad (gaugeConn R (connM z.A)))
        μ ν c e x := by
  show curvatureF (gaugeTuple R z).A x μ ν c e = _
  rw [curvatureF_eq_curvM (differentiableAt_gaugeTuple_A hR hA), connM_gaugeTuple,
    curvatureW_eq_curvM]

theorem redJet_gaugeTuple_K {x : E4} (hR : GaugeAt R x) (hH : DifferentiableAt ℝ z.H x)
    (μ : Fin 4) (i : Fin 2) :
    (redJet (gaugeTuple R z) x).K μ i =
      tgrad R (matterSec z none) (Fin.natAdd 3 i) μ x +
        ∑ e, entries (gaugeConn R (connM z.A)) μ (Fin.natAdd 3 i) e x *
          transp R (matterSec z none) e x := by
  have hblock : ∀ᶠ y in 𝓝 x, IsSMBlock (R y) := hR.mem.mono fun _ hy => hy.2.1
  have hHd' : DifferentiableAt ℝ (gaugeTuple R z).H x := differentiableAt_higgsG hR.mdiff hH
  have hev : (fun y => embH ((gaugeTuple R z).H y)) =ᶠ[𝓝 x]
      fun y => R y *ᵥ matterSec z none y :=
    hblock.mono fun y hy => embH_higgsG hy (z.H y)
  show covDerivHiggs (gaugeTuple R z).A (gaugeTuple R z).H x μ i = _
  rw [covDerivHiggs_eq_proj hHd', covDerV_congr hev μ, connM_gaugeTuple]
  simp only [projH, covDerV, Pi.add_apply, pdV, tgrad, transp, mulVec, dotProduct, entries]
  rfl

theorem redJet_gaugeTuple_dΨ {x : E4} (hR : GaugeAt R x) (hΨ : DifferentiableAt ℝ z.Ψ x)
    (μ s : Fin 4) (c : Fin 5) :
    (redJet (gaugeTuple R z) x).dΨ μ s c = tgrad R (matterSec z (some (Sum.inl s))) c μ x := by
  have hd := differentiableAt_spinG hR.mdiff hΨ
  show pd (fun y => spinG (R y) (z.Ψ y)) μ x s c = _
  rw [← pd_apply_gen hd μ s, ← pd_apply_gen (differentiableAt_apply_gen hd s) μ c]
  rfl

theorem redJet_gaugeTuple_dΨb {x : E4} (hR : GaugeAt R x) (hΨb : DifferentiableAt ℝ z.Ψb x)
    (μ s : Fin 4) (c : Fin 5) :
    (redJet (gaugeTuple R z) x).dΨb μ s c =
      star (tgrad R (matterSec z (some (Sum.inr s))) c μ x) := by
  have hd := differentiableAt_cospinG hR.mdiff hΨb
  have hd' : DifferentiableAt ℝ (fun y => transp R (matterSec z (some (Sum.inr s))) c y) x := by
    have : (fun y => transp R (matterSec z (some (Sum.inr s))) c y) =
        fun y => star (cospinG (R y) (z.Ψb y) s c) := by
      funext y
      have := gaugeTuple_Ψb_eq (R := R) (z := z) y s c
      rw [show (gaugeTuple R z).Ψb y s c = cospinG (R y) (z.Ψb y) s c from rfl] at this
      rw [this, star_star]
    rw [this]
    exact (Complex.conjCLE.toContinuousLinearMap.differentiableAt).comp x
      (differentiableAt_apply_gen (differentiableAt_apply_gen hd s) c)
  show pd (fun y => cospinG (R y) (z.Ψb y)) μ x s c = _
  rw [← pd_apply_gen hd μ s, ← pd_apply_gen (differentiableAt_apply_gen hd s) μ c]
  have e : (fun y => cospinG (R y) (z.Ψb y) s c) =
      fun y => star (transp R (matterSec z (some (Sum.inr s))) c y) := by
    funext y; exact gaugeTuple_Ψb_eq (R := R) (z := z) y s c
  rw [e, pd_star_complex hd']
  rfl

end Jets

end RenewalGeometry.CriticalQuotientRows
