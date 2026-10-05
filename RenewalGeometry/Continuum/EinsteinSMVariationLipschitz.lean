/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.EinsteinSMCovectorSmoothness
import RenewalGeometry.Continuum.EinsteinSMCofinalTransport

/-!
# First-variation Lipschitz estimates on a bounded strong packet (`prop:variation-continuity`,
  Einstein–Standard-Model action-closure manuscript)

Rendering as in `EinsteinSMReducedClosure.lean` / `EinsteinSMCofinalTransport.lean`.

## Generic Hölder bookkeeping

`eLpNorm_term1`, `eLpNorm_term2`, `eLpNorm_term3`: for coefficient fields `Φᵢ(x)` (linear,
bilinear or trilinear maps) and packets `Xᵢ, Yᵢ, Wᵢ`, the `L¹` norm of
`Φ₁(X₁, Y₁, W₁) - Φ₂(X₂, Y₂, W₂)` is bounded by the `L^∞` norm of `Φ₁ - Φ₂` times the packet norms
plus the `L^∞` bound of `Φ₂` times the packet differences (Hölder `(∞, 2)`, `(∞, 2, 2)`,
`(∞, 2, 4, 4)`).

## Coefficients

`exists_lipschitz_bound`: a `C¹` map on the open chart `coframeGL` is bounded and Lipschitz on every
compact subset (`LocallyLipschitzOn.exists_lipschitzOnWith_of_compact`); applied to the coefficient
maps of the covectors (`CovSmooth`).
-/

open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal NNReal

noncomputable section

set_option synthInstance.maxSize 1024

namespace RenewalGeometry
namespace EinsteinSM
namespace VarLip

/-! ### Hölder bookkeeping -/

section Holder

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

instance holderTriple_221 : ENNReal.HolderTriple 2 2 1 :=
  ⟨by rw [ENNReal.inv_two_add_inv_two, inv_one]⟩

theorem eLpNorm_top_mul {a f : X → ℝ} (ha : AEStronglyMeasurable a μ)
    (hf : AEStronglyMeasurable f μ) (p : ℝ≥0∞) :
    eLpNorm (fun x => a x * f x) p μ ≤ eLpNorm a ⊤ μ * eLpNorm f p μ := by
  have := eLpNorm_le_eLpNorm_top_mul_eLpNorm p a hf (fun s t => s * t) 1
    (Eventually.of_forall fun x => by simp [nnnorm_mul])
  simpa using this

theorem eLpNorm_mul_two_two {f g : X → ℝ} (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) :
    eLpNorm (fun x => f x * g x) 1 μ ≤ eLpNorm f 2 μ * eLpNorm g 2 μ := by
  have := eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm (p := 2) (q := 2) (r := 1) hf hg
    (fun s t => s * t) 1 (Eventually.of_forall fun x => by simp [nnnorm_mul])
  simpa using this

theorem eLpNorm_mul_four_four {f g : X → ℝ} (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) :
    eLpNorm (fun x => f x * g x) 2 μ ≤ eLpNorm f 4 μ * eLpNorm g 4 μ := by
  have := eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm (p := 4) (q := 4) (r := 2) hf hg
    (fun s t => s * t) 1 (Eventually.of_forall fun x => by simp [nnnorm_mul])
  simpa using this

variable {V W U Z : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
  [NormedSpace ℝ W] [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup Z]
  [NormedSpace ℝ Z]

theorem aesm_norm {f : X → V} (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun x => ‖f x‖) μ := hf.norm

/-- **Linear coefficient terms**: `‖Φ₁X₁ - Φ₂X₂‖_{L¹} ≤ ‖Φ₁-Φ₂‖_∞‖X₁‖_{L¹} + ‖Φ₂‖_∞‖X₁-X₂‖_{L¹}`. -/
theorem eLpNorm_term1 {Φ₁ Φ₂ : X → V →L[ℝ] Z} {X₁ X₂ : X → V}
    (hΦ₁ : AEStronglyMeasurable Φ₁ μ) (hΦ₂ : AEStronglyMeasurable Φ₂ μ)
    (hX₁ : AEStronglyMeasurable X₁ μ) (hX₂ : AEStronglyMeasurable X₂ μ) :
    eLpNorm (fun x => Φ₁ x (X₁ x) - Φ₂ x (X₂ x)) 1 μ ≤
      eLpNorm (fun x => Φ₁ x - Φ₂ x) ⊤ μ * eLpNorm X₁ 1 μ +
        eLpNorm Φ₂ ⊤ μ * eLpNorm (fun x => X₁ x - X₂ x) 1 μ := by
  have hd : AEStronglyMeasurable (fun x => Φ₁ x - Φ₂ x) μ := hΦ₁.sub hΦ₂
  have hdX : AEStronglyMeasurable (fun x => X₁ x - X₂ x) μ := hX₁.sub hX₂
  have hpt : ∀ x, ‖Φ₁ x (X₁ x) - Φ₂ x (X₂ x)‖ ≤
      ‖Φ₁ x - Φ₂ x‖ * ‖X₁ x‖ + ‖Φ₂ x‖ * ‖X₁ x - X₂ x‖ := by
    intro x
    have e : Φ₁ x (X₁ x) - Φ₂ x (X₂ x) = (Φ₁ x - Φ₂ x) (X₁ x) + Φ₂ x (X₁ x - X₂ x) := by
      simp [map_sub]
    rw [e]
    exact (norm_add_le _ _).trans (add_le_add ((Φ₁ x - Φ₂ x).le_opNorm _) ((Φ₂ x).le_opNorm _))
  have m1 : AEStronglyMeasurable (fun x => ‖Φ₁ x - Φ₂ x‖ * ‖X₁ x‖) μ := hd.norm.mul hX₁.norm
  have m2 : AEStronglyMeasurable (fun x => ‖Φ₂ x‖ * ‖X₁ x - X₂ x‖) μ := hΦ₂.norm.mul hdX.norm
  have b1 : eLpNorm (fun x => ‖Φ₁ x - Φ₂ x‖ * ‖X₁ x‖) 1 μ ≤
      eLpNorm (fun x => Φ₁ x - Φ₂ x) ⊤ μ * eLpNorm X₁ 1 μ := by
    have := eLpNorm_top_mul hd.norm hX₁.norm 1 (μ := μ)
    rwa [eLpNorm_norm, eLpNorm_norm] at this
  have b2 : eLpNorm (fun x => ‖Φ₂ x‖ * ‖X₁ x - X₂ x‖) 1 μ ≤
      eLpNorm Φ₂ ⊤ μ * eLpNorm (fun x => X₁ x - X₂ x) 1 μ := by
    have := eLpNorm_top_mul hΦ₂.norm hdX.norm 1 (μ := μ)
    rwa [eLpNorm_norm, eLpNorm_norm] at this
  calc eLpNorm (fun x => Φ₁ x (X₁ x) - Φ₂ x (X₂ x)) 1 μ
      ≤ eLpNorm (fun x => ‖Φ₁ x - Φ₂ x‖ * ‖X₁ x‖ + ‖Φ₂ x‖ * ‖X₁ x - X₂ x‖) 1 μ :=
        eLpNorm_mono_real fun x => hpt x
    _ ≤ eLpNorm (fun x => ‖Φ₁ x - Φ₂ x‖ * ‖X₁ x‖) 1 μ +
          eLpNorm (fun x => ‖Φ₂ x‖ * ‖X₁ x - X₂ x‖) 1 μ := eLpNorm_add_le m1 m2 le_rfl
    _ ≤ _ := add_le_add b1 b2

theorem eLpNorm_top_two_two {a f g : X → ℝ} (ha : AEStronglyMeasurable a μ)
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    eLpNorm (fun x => a x * (f x * g x)) 1 μ ≤
      eLpNorm a ⊤ μ * (eLpNorm f 2 μ * eLpNorm g 2 μ) :=
  (eLpNorm_top_mul ha (hf.mul hg) 1).trans (by gcongr; exact eLpNorm_mul_two_two hf hg)

/-- **Bilinear coefficient terms**, Hölder `(∞, 2, 2)`. -/
theorem eLpNorm_term2 {Φ₁ Φ₂ : X → V →L[ℝ] W →L[ℝ] Z} {X₁ X₂ : X → V} {Y₁ Y₂ : X → W}
    (hΦ₁ : AEStronglyMeasurable Φ₁ μ) (hΦ₂ : AEStronglyMeasurable Φ₂ μ)
    (hX₁ : AEStronglyMeasurable X₁ μ) (hX₂ : AEStronglyMeasurable X₂ μ)
    (hY₁ : AEStronglyMeasurable Y₁ μ) (hY₂ : AEStronglyMeasurable Y₂ μ) :
    eLpNorm (fun x => Φ₁ x (X₁ x) (Y₁ x) - Φ₂ x (X₂ x) (Y₂ x)) 1 μ ≤
      eLpNorm (fun x => Φ₁ x - Φ₂ x) ⊤ μ * (eLpNorm X₁ 2 μ * eLpNorm Y₁ 2 μ) +
        eLpNorm Φ₂ ⊤ μ * (eLpNorm (fun x => X₁ x - X₂ x) 2 μ * eLpNorm Y₁ 2 μ) +
        eLpNorm Φ₂ ⊤ μ * (eLpNorm X₂ 2 μ * eLpNorm (fun x => Y₁ x - Y₂ x) 2 μ) := by
  have hd : AEStronglyMeasurable (fun x => Φ₁ x - Φ₂ x) μ := hΦ₁.sub hΦ₂
  have hdX : AEStronglyMeasurable (fun x => X₁ x - X₂ x) μ := hX₁.sub hX₂
  have hdY : AEStronglyMeasurable (fun x => Y₁ x - Y₂ x) μ := hY₁.sub hY₂
  have hpt : ∀ x, ‖Φ₁ x (X₁ x) (Y₁ x) - Φ₂ x (X₂ x) (Y₂ x)‖ ≤
      ‖Φ₁ x - Φ₂ x‖ * (‖X₁ x‖ * ‖Y₁ x‖) + ‖Φ₂ x‖ * (‖X₁ x - X₂ x‖ * ‖Y₁ x‖) +
        ‖Φ₂ x‖ * (‖X₂ x‖ * ‖Y₁ x - Y₂ x‖) := by
    intro x
    have e : Φ₁ x (X₁ x) (Y₁ x) - Φ₂ x (X₂ x) (Y₂ x) = (Φ₁ x - Φ₂ x) (X₁ x) (Y₁ x) +
        Φ₂ x (X₁ x - X₂ x) (Y₁ x) + Φ₂ x (X₂ x) (Y₁ x - Y₂ x) := by
      simp only [ContinuousLinearMap.sub_apply, map_sub]; abel
    rw [e]
    refine (norm_add₃_le).trans (add_le_add (add_le_add ?_ ?_) ?_)
    · rw [← mul_assoc]; exact (Φ₁ x - Φ₂ x).le_opNorm₂ _ _
    · rw [← mul_assoc]; exact (Φ₂ x).le_opNorm₂ _ _
    · rw [← mul_assoc]; exact (Φ₂ x).le_opNorm₂ _ _
  have m1 : AEStronglyMeasurable (fun x => ‖Φ₁ x - Φ₂ x‖ * (‖X₁ x‖ * ‖Y₁ x‖)) μ :=
    hd.norm.mul (hX₁.norm.mul hY₁.norm)
  have m2 : AEStronglyMeasurable (fun x => ‖Φ₂ x‖ * (‖X₁ x - X₂ x‖ * ‖Y₁ x‖)) μ :=
    hΦ₂.norm.mul (hdX.norm.mul hY₁.norm)
  have m3 : AEStronglyMeasurable (fun x => ‖Φ₂ x‖ * (‖X₂ x‖ * ‖Y₁ x - Y₂ x‖)) μ :=
    hΦ₂.norm.mul (hX₂.norm.mul hdY.norm)
  have b1 := eLpNorm_top_two_two hd.norm hX₁.norm hY₁.norm (μ := μ)
  have b2 := eLpNorm_top_two_two hΦ₂.norm hdX.norm hY₁.norm (μ := μ)
  have b3 := eLpNorm_top_two_two hΦ₂.norm hX₂.norm hdY.norm (μ := μ)
  simp only [eLpNorm_norm] at b1 b2 b3
  calc eLpNorm (fun x => Φ₁ x (X₁ x) (Y₁ x) - Φ₂ x (X₂ x) (Y₂ x)) 1 μ
      ≤ eLpNorm (fun x => ‖Φ₁ x - Φ₂ x‖ * (‖X₁ x‖ * ‖Y₁ x‖) +
          ‖Φ₂ x‖ * (‖X₁ x - X₂ x‖ * ‖Y₁ x‖) + ‖Φ₂ x‖ * (‖X₂ x‖ * ‖Y₁ x - Y₂ x‖)) 1 μ :=
        eLpNorm_mono_real fun x => hpt x
    _ ≤ eLpNorm (fun x => ‖Φ₁ x - Φ₂ x‖ * (‖X₁ x‖ * ‖Y₁ x‖)) 1 μ +
          eLpNorm (fun x => ‖Φ₂ x‖ * (‖X₁ x - X₂ x‖ * ‖Y₁ x‖)) 1 μ +
          eLpNorm (fun x => ‖Φ₂ x‖ * (‖X₂ x‖ * ‖Y₁ x - Y₂ x‖)) 1 μ :=
        (eLpNorm_add_le (m1.add m2) m3 le_rfl).trans
          (add_le_add (eLpNorm_add_le m1 m2 le_rfl) le_rfl)
    _ ≤ _ := add_le_add (add_le_add b1 b2) b3

theorem eLpNorm_top_two_four_four {a f g h : X → ℝ} (ha : AEStronglyMeasurable a μ)
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hh : AEStronglyMeasurable h μ) :
    eLpNorm (fun x => a x * (f x * (g x * h x))) 1 μ ≤
      eLpNorm a ⊤ μ * (eLpNorm f 2 μ * (eLpNorm g 4 μ * eLpNorm h 4 μ)) :=
  (eLpNorm_top_mul ha (hf.mul (hg.mul hh)) 1).trans (by
    gcongr
    exact (eLpNorm_mul_two_two hf (hg.mul hh)).trans
      (by gcongr; exact eLpNorm_mul_four_four hg hh))

/-- **Trilinear coefficient terms**, Hölder `(∞, 2, 4, 4)`. -/
theorem eLpNorm_term3 {Φ₁ Φ₂ : X → V →L[ℝ] W →L[ℝ] U →L[ℝ] Z} {X₁ X₂ : X → V} {Y₁ Y₂ : X → W}
    {W₁ W₂ : X → U}
    (hΦ₁ : AEStronglyMeasurable Φ₁ μ) (hΦ₂ : AEStronglyMeasurable Φ₂ μ)
    (hX₁ : AEStronglyMeasurable X₁ μ) (hX₂ : AEStronglyMeasurable X₂ μ)
    (hY₁ : AEStronglyMeasurable Y₁ μ) (hY₂ : AEStronglyMeasurable Y₂ μ)
    (hW₁ : AEStronglyMeasurable W₁ μ) (hW₂ : AEStronglyMeasurable W₂ μ) :
    eLpNorm (fun x => Φ₁ x (X₁ x) (Y₁ x) (W₁ x) - Φ₂ x (X₂ x) (Y₂ x) (W₂ x)) 1 μ ≤
      eLpNorm (fun x => Φ₁ x - Φ₂ x) ⊤ μ *
          (eLpNorm X₁ 2 μ * (eLpNorm Y₁ 4 μ * eLpNorm W₁ 4 μ)) +
        eLpNorm Φ₂ ⊤ μ * (eLpNorm (fun x => X₁ x - X₂ x) 2 μ * (eLpNorm Y₁ 4 μ * eLpNorm W₁ 4 μ)) +
        eLpNorm Φ₂ ⊤ μ * (eLpNorm X₂ 2 μ * (eLpNorm (fun x => Y₁ x - Y₂ x) 4 μ * eLpNorm W₁ 4 μ)) +
        eLpNorm Φ₂ ⊤ μ * (eLpNorm X₂ 2 μ * (eLpNorm Y₂ 4 μ * eLpNorm (fun x => W₁ x - W₂ x) 4 μ)) := by
  have hd : AEStronglyMeasurable (fun x => Φ₁ x - Φ₂ x) μ := hΦ₁.sub hΦ₂
  have hdX : AEStronglyMeasurable (fun x => X₁ x - X₂ x) μ := hX₁.sub hX₂
  have hdY : AEStronglyMeasurable (fun x => Y₁ x - Y₂ x) μ := hY₁.sub hY₂
  have hdW : AEStronglyMeasurable (fun x => W₁ x - W₂ x) μ := hW₁.sub hW₂
  have b3 : ∀ (B : V →L[ℝ] W →L[ℝ] U →L[ℝ] Z) (v : V) (w : W) (u : U),
      ‖B v w u‖ ≤ ‖B‖ * (‖v‖ * (‖w‖ * ‖u‖)) := fun B v w u => by
    calc ‖B v w u‖ ≤ ‖B v w‖ * ‖u‖ := (B v w).le_opNorm u
      _ ≤ ‖B v‖ * ‖w‖ * ‖u‖ := by gcongr; exact (B v).le_opNorm w
      _ ≤ ‖B‖ * ‖v‖ * ‖w‖ * ‖u‖ := by gcongr; exact B.le_opNorm v
      _ = _ := by ring
  have hpt : ∀ x, ‖Φ₁ x (X₁ x) (Y₁ x) (W₁ x) - Φ₂ x (X₂ x) (Y₂ x) (W₂ x)‖ ≤
      ‖Φ₁ x - Φ₂ x‖ * (‖X₁ x‖ * (‖Y₁ x‖ * ‖W₁ x‖)) +
        ‖Φ₂ x‖ * (‖X₁ x - X₂ x‖ * (‖Y₁ x‖ * ‖W₁ x‖)) +
        ‖Φ₂ x‖ * (‖X₂ x‖ * (‖Y₁ x - Y₂ x‖ * ‖W₁ x‖)) +
        ‖Φ₂ x‖ * (‖X₂ x‖ * (‖Y₂ x‖ * ‖W₁ x - W₂ x‖)) := by
    intro x
    have e : Φ₁ x (X₁ x) (Y₁ x) (W₁ x) - Φ₂ x (X₂ x) (Y₂ x) (W₂ x) =
        (Φ₁ x - Φ₂ x) (X₁ x) (Y₁ x) (W₁ x) + Φ₂ x (X₁ x - X₂ x) (Y₁ x) (W₁ x) +
          Φ₂ x (X₂ x) (Y₁ x - Y₂ x) (W₁ x) + Φ₂ x (X₂ x) (Y₂ x) (W₁ x - W₂ x) := by
      simp only [ContinuousLinearMap.sub_apply, map_sub]; abel
    rw [e]
    exact (norm_add_le _ _).trans (add_le_add ((norm_add₃_le).trans
      (add_le_add (add_le_add (b3 _ _ _ _) (b3 _ _ _ _)) (b3 _ _ _ _))) (b3 _ _ _ _))
  have m1 : AEStronglyMeasurable (fun x => ‖Φ₁ x - Φ₂ x‖ * (‖X₁ x‖ * (‖Y₁ x‖ * ‖W₁ x‖))) μ :=
    hd.norm.mul (hX₁.norm.mul (hY₁.norm.mul hW₁.norm))
  have m2 : AEStronglyMeasurable (fun x => ‖Φ₂ x‖ * (‖X₁ x - X₂ x‖ * (‖Y₁ x‖ * ‖W₁ x‖))) μ :=
    hΦ₂.norm.mul (hdX.norm.mul (hY₁.norm.mul hW₁.norm))
  have m3 : AEStronglyMeasurable (fun x => ‖Φ₂ x‖ * (‖X₂ x‖ * (‖Y₁ x - Y₂ x‖ * ‖W₁ x‖))) μ :=
    hΦ₂.norm.mul (hX₂.norm.mul (hdY.norm.mul hW₁.norm))
  have m4 : AEStronglyMeasurable (fun x => ‖Φ₂ x‖ * (‖X₂ x‖ * (‖Y₂ x‖ * ‖W₁ x - W₂ x‖))) μ :=
    hΦ₂.norm.mul (hX₂.norm.mul (hY₂.norm.mul hdW.norm))
  have c1 := eLpNorm_top_two_four_four hd.norm hX₁.norm hY₁.norm hW₁.norm (μ := μ)
  have c2 := eLpNorm_top_two_four_four hΦ₂.norm hdX.norm hY₁.norm hW₁.norm (μ := μ)
  have c3 := eLpNorm_top_two_four_four hΦ₂.norm hX₂.norm hdY.norm hW₁.norm (μ := μ)
  have c4 := eLpNorm_top_two_four_four hΦ₂.norm hX₂.norm hY₂.norm hdW.norm (μ := μ)
  simp only [eLpNorm_norm] at c1 c2 c3 c4
  calc eLpNorm (fun x => Φ₁ x (X₁ x) (Y₁ x) (W₁ x) - Φ₂ x (X₂ x) (Y₂ x) (W₂ x)) 1 μ
      ≤ eLpNorm (fun x => ‖Φ₁ x - Φ₂ x‖ * (‖X₁ x‖ * (‖Y₁ x‖ * ‖W₁ x‖)) +
          ‖Φ₂ x‖ * (‖X₁ x - X₂ x‖ * (‖Y₁ x‖ * ‖W₁ x‖)) +
          ‖Φ₂ x‖ * (‖X₂ x‖ * (‖Y₁ x - Y₂ x‖ * ‖W₁ x‖)) +
          ‖Φ₂ x‖ * (‖X₂ x‖ * (‖Y₂ x‖ * ‖W₁ x - W₂ x‖))) 1 μ :=
        eLpNorm_mono_real fun x => hpt x
    _ ≤ eLpNorm (fun x => ‖Φ₁ x - Φ₂ x‖ * (‖X₁ x‖ * (‖Y₁ x‖ * ‖W₁ x‖))) 1 μ +
          eLpNorm (fun x => ‖Φ₂ x‖ * (‖X₁ x - X₂ x‖ * (‖Y₁ x‖ * ‖W₁ x‖))) 1 μ +
          eLpNorm (fun x => ‖Φ₂ x‖ * (‖X₂ x‖ * (‖Y₁ x - Y₂ x‖ * ‖W₁ x‖))) 1 μ +
          eLpNorm (fun x => ‖Φ₂ x‖ * (‖X₂ x‖ * (‖Y₂ x‖ * ‖W₁ x - W₂ x‖))) 1 μ := by
        refine (eLpNorm_add_le ((m1.add m2).add m3) m4 le_rfl).trans (add_le_add ?_ le_rfl)
        refine (eLpNorm_add_le (m1.add m2) m3 le_rfl).trans (add_le_add ?_ le_rfl)
        exact eLpNorm_add_le m1 m2 le_rfl
    _ ≤ _ := add_le_add (add_le_add (add_le_add c1 c2) c3) c4

end Holder

/-! ### Coefficients are bounded and Lipschitz on compact chart sets -/

section Coeff

/-- A `C¹` map on the open chart `coframeGL` is bounded and Lipschitz on every compact subset. -/
theorem exists_lipschitz_bound {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Φ : CoframeFibre → F} (hΦ : ContDiffOn ℝ 1 Φ coframeGL) {Ke : Set CoframeFibre}
    (hKe : IsCompact Ke) (hsub : Ke ⊆ coframeGL) :
    ∃ L M : ℝ, 0 ≤ L ∧ 0 ≤ M ∧ (∀ e ∈ Ke, ‖Φ e‖ ≤ M) ∧
      ∀ e ∈ Ke, ∀ e' ∈ Ke, ‖Φ e - Φ e'‖ ≤ L * ‖e - e'‖ := by
  have hloc : LocallyLipschitzOn Ke Φ := by
    intro x hx
    obtain ⟨K, t, ht, hK⟩ := ((hΦ.contDiffAt (isOpen_coframeGL.mem_nhds (hsub hx)))).exists_lipschitzOnWith
    exact ⟨K, t, mem_nhdsWithin_of_mem_nhds ht, hK⟩
  obtain ⟨K, hK⟩ := hloc.exists_lipschitzOnWith_of_compact hKe
  obtain ⟨M, hM⟩ := hKe.exists_bound_of_continuousOn (hΦ.continuousOn.mono hsub)
  refine ⟨K, max M 0, K.2, le_max_right _ _, fun e he => (hM e he).trans (le_max_left _ _),
    fun e he e' he' => ?_⟩
  rw [← dist_eq_norm, ← dist_eq_norm]
  exact hK.dist_le_mul e he e' he'

end Coeff


/-! ### Assembly of term bounds -/

section Assembly

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
variable {V W U Z : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
  [NormedSpace ℝ W] [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup Z]
  [NormedSpace ℝ Z]

theorem term1_bound {Φ₁ Φ₂ : X → V →L[ℝ] Z} {X₁ X₂ : X → V}
    (hΦ₁ : AEStronglyMeasurable Φ₁ μ) (hΦ₂ : AEStronglyMeasurable Φ₂ μ)
    (hX₁ : AEStronglyMeasurable X₁ μ) (hX₂ : AEStronglyMeasurable X₂ μ)
    {D Lc Mc BX KX : ℝ≥0∞} (hΦd : eLpNorm (fun x => Φ₁ x - Φ₂ x) ⊤ μ ≤ Lc * D)
    (hΦb : eLpNorm Φ₂ ⊤ μ ≤ Mc) (hX : eLpNorm X₁ 1 μ ≤ BX)
    (hdX : eLpNorm (fun x => X₁ x - X₂ x) 1 μ ≤ KX * D) :
    eLpNorm (fun x => Φ₁ x (X₁ x) - Φ₂ x (X₂ x)) 1 μ ≤ (Lc * BX + Mc * KX) * D := by
  refine (eLpNorm_term1 hΦ₁ hΦ₂ hX₁ hX₂).trans ?_
  calc _ ≤ Lc * D * BX + Mc * (KX * D) := by gcongr
    _ = _ := by ring

theorem term2_bound {Φ₁ Φ₂ : X → V →L[ℝ] W →L[ℝ] Z} {X₁ X₂ : X → V} {Y₁ Y₂ : X → W}
    (hΦ₁ : AEStronglyMeasurable Φ₁ μ) (hΦ₂ : AEStronglyMeasurable Φ₂ μ)
    (hX₁ : AEStronglyMeasurable X₁ μ) (hX₂ : AEStronglyMeasurable X₂ μ)
    (hY₁ : AEStronglyMeasurable Y₁ μ) (hY₂ : AEStronglyMeasurable Y₂ μ)
    {D Lc Mc BX BY KX KY : ℝ≥0∞} (hΦd : eLpNorm (fun x => Φ₁ x - Φ₂ x) ⊤ μ ≤ Lc * D)
    (hΦb : eLpNorm Φ₂ ⊤ μ ≤ Mc) (hX₁b : eLpNorm X₁ 2 μ ≤ BX) (hX₂b : eLpNorm X₂ 2 μ ≤ BX)
    (hY₁b : eLpNorm Y₁ 2 μ ≤ BY) (hdX : eLpNorm (fun x => X₁ x - X₂ x) 2 μ ≤ KX * D)
    (hdY : eLpNorm (fun x => Y₁ x - Y₂ x) 2 μ ≤ KY * D) :
    eLpNorm (fun x => Φ₁ x (X₁ x) (Y₁ x) - Φ₂ x (X₂ x) (Y₂ x)) 1 μ ≤
      (Lc * (BX * BY) + Mc * (KX * BY) + Mc * (BX * KY)) * D := by
  refine (eLpNorm_term2 hΦ₁ hΦ₂ hX₁ hX₂ hY₁ hY₂).trans ?_
  calc _ ≤ Lc * D * (BX * BY) + Mc * (KX * D * BY) + Mc * (BX * (KY * D)) := by gcongr
    _ = _ := by ring

theorem term3_bound {Φ₁ Φ₂ : X → V →L[ℝ] W →L[ℝ] U →L[ℝ] Z} {X₁ X₂ : X → V} {Y₁ Y₂ : X → W}
    {W₁ W₂ : X → U}
    (hΦ₁ : AEStronglyMeasurable Φ₁ μ) (hΦ₂ : AEStronglyMeasurable Φ₂ μ)
    (hX₁ : AEStronglyMeasurable X₁ μ) (hX₂ : AEStronglyMeasurable X₂ μ)
    (hY₁ : AEStronglyMeasurable Y₁ μ) (hY₂ : AEStronglyMeasurable Y₂ μ)
    (hW₁ : AEStronglyMeasurable W₁ μ) (hW₂ : AEStronglyMeasurable W₂ μ)
    {D Lc Mc BX BY BW KX KY KW : ℝ≥0∞} (hΦd : eLpNorm (fun x => Φ₁ x - Φ₂ x) ⊤ μ ≤ Lc * D)
    (hΦb : eLpNorm Φ₂ ⊤ μ ≤ Mc) (hX₁b : eLpNorm X₁ 2 μ ≤ BX) (hX₂b : eLpNorm X₂ 2 μ ≤ BX)
    (hY₁b : eLpNorm Y₁ 4 μ ≤ BY) (hY₂b : eLpNorm Y₂ 4 μ ≤ BY) (hW₁b : eLpNorm W₁ 4 μ ≤ BW)
    (hdX : eLpNorm (fun x => X₁ x - X₂ x) 2 μ ≤ KX * D)
    (hdY : eLpNorm (fun x => Y₁ x - Y₂ x) 4 μ ≤ KY * D)
    (hdW : eLpNorm (fun x => W₁ x - W₂ x) 4 μ ≤ KW * D) :
    eLpNorm (fun x => Φ₁ x (X₁ x) (Y₁ x) (W₁ x) - Φ₂ x (X₂ x) (Y₂ x) (W₂ x)) 1 μ ≤
      (Lc * (BX * (BY * BW)) + Mc * (KX * (BY * BW)) + Mc * (BX * (KY * BW)) +
        Mc * (BX * (BY * KW))) * D := by
  refine (eLpNorm_term3 hΦ₁ hΦ₂ hX₁ hX₂ hY₁ hY₂ hW₁ hW₂).trans ?_
  calc _ ≤ Lc * D * (BX * (BY * BW)) + Mc * (KX * D * (BY * BW)) +
        Mc * (BX * (KY * D * BW)) + Mc * (BX * (BY * (KW * D))) := by gcongr
    _ = _ := by ring

/-- Comparison of `L^p` norms on a finite measure space. -/
theorem eLpNorm_le_of_le_exp [IsFiniteMeasure μ] {E : Type*} [NormedAddCommGroup E]
    {f : X → E} (hf : AEStronglyMeasurable f μ) {p q : ℝ≥0∞} (hpq : p ≤ q) :
    eLpNorm f p μ ≤ eLpNorm f q μ * μ univ ^ (1 / p.toReal - 1 / q.toReal) :=
  eLpNorm_le_eLpNorm_mul_rpow_measure_univ hpq hf

/-- An a.e. bound gives an `L^∞` bound. -/
theorem eLpNorm_top_le_of_ae {E : Type*} [NormedAddCommGroup E] {f : X → E} {C : ℝ}
    (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) : eLpNorm f ⊤ μ ≤ ENNReal.ofReal C := by
  have := eLpNorm_le_of_ae_bound (p := ⊤) h
  simpa using this

end Assembly

/-! ### Coefficient fields -/

section CoeffField

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- **Coefficient fields `Ψ(e(x))`**: `L^∞` bound and Lipschitz dependence on `e`. -/
theorem coeff_field {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Ψ : CoframeFibre → F} {Ke : Set CoframeFibre} {L M : ℝ} (hL : 0 ≤ L)
    (hb : ∀ e ∈ Ke, ‖Ψ e‖ ≤ M) (hl : ∀ e ∈ Ke, ∀ e' ∈ Ke, ‖Ψ e - Ψ e'‖ ≤ L * ‖e - e'‖)
    {e₁ e₂ : X → CoframeFibre} (h₁ : ∀ᵐ x ∂μ, e₁ x ∈ Ke) (h₂ : ∀ᵐ x ∂μ, e₂ x ∈ Ke) :
    eLpNorm (fun x => Ψ (e₁ x) - Ψ (e₂ x)) ⊤ μ ≤
        ENNReal.ofReal L * eLpNorm (fun x => e₁ x - e₂ x) ⊤ μ ∧
      eLpNorm (fun x => Ψ (e₂ x)) ⊤ μ ≤ ENNReal.ofReal M := by
  constructor
  · have hpt : ∀ᵐ x ∂μ, ‖Ψ (e₁ x) - Ψ (e₂ x)‖ ≤ L * ‖e₁ x - e₂ x‖ := by
      filter_upwards [h₁, h₂] with x hx₁ hx₂
      exact hl _ hx₁ _ hx₂
    have := eLpNorm_mono_ae_real (p := ⊤) hpt
    refine this.trans (le_of_eq ?_)
    have h2 := eLpNorm_const_smul L (fun x => ‖e₁ x - e₂ x‖) ⊤ μ
    have e2 : (L • fun x => ‖e₁ x - e₂ x‖) = fun x => L * ‖e₁ x - e₂ x‖ := by
      funext x; simp [smul_eq_mul]
    rw [e2, eLpNorm_norm, Real.enorm_eq_ofReal_abs, abs_of_nonneg hL] at h2
    exact h2
  · refine eLpNorm_top_le_of_ae ?_
    filter_upwards [h₂] with x hx
    exact hb _ hx

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- **Scalar factors**: `‖c₁A₁ - c₂A₂‖₁ ≤ |c₁| ‖A₁ - A₂‖₁ + |c₁ - c₂| ‖A₂‖₁`. -/
theorem scaled_term_bound {A₁ A₂ : X → Z} (hA₁ : AEStronglyMeasurable A₁ μ)
    (hA₂ : AEStronglyMeasurable A₂ μ) {c₁ c₂ Mc : ℝ} (hc₁ : |c₁| ≤ Mc) :
    eLpNorm (fun x => c₁ • A₁ x - c₂ • A₂ x) 1 μ ≤
      ENNReal.ofReal Mc * eLpNorm (fun x => A₁ x - A₂ x) 1 μ +
        ENNReal.ofReal |c₁ - c₂| * eLpNorm A₂ 1 μ := by
  have e : (fun x => c₁ • A₁ x - c₂ • A₂ x) =
      (c₁ • fun x => A₁ x - A₂ x) + (c₁ - c₂) • A₂ := by
    funext x
    show _ = c₁ • (A₁ x - A₂ x) + (c₁ - c₂) • A₂ x
    rw [smul_sub, sub_smul]; abel
  rw [e]
  refine (eLpNorm_add_le ((hA₁.sub hA₂).const_smul _) (hA₂.const_smul _) le_rfl).trans ?_
  rw [eLpNorm_const_smul, eLpNorm_const_smul, Real.enorm_eq_ofReal_abs,
    Real.enorm_eq_ofReal_abs]
  gcongr <;> exact le_rfl

end CoeffField

/-! ### Single-field bounds -/

section Apply

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
variable {V W U Z : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
  [NormedSpace ℝ W] [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup Z]
  [NormedSpace ℝ Z]

theorem eLpNorm_apply1_le {Φ : X → V →L[ℝ] Z} {f : X → V} (hΦ : AEStronglyMeasurable Φ μ)
    (hf : AEStronglyMeasurable f μ) (p : ℝ≥0∞) :
    eLpNorm (fun x => Φ x (f x)) p μ ≤ eLpNorm Φ ⊤ μ * eLpNorm f p μ := by
  refine (eLpNorm_mono_real (fun x => (Φ x).le_opNorm (f x))).trans ?_
  have := eLpNorm_top_mul hΦ.norm hf.norm p (μ := μ)
  rwa [eLpNorm_norm, eLpNorm_norm] at this

theorem eLpNorm_apply2_le {Φ : X → V →L[ℝ] W →L[ℝ] Z} {f : X → V} {g : X → W}
    (hΦ : AEStronglyMeasurable Φ μ) (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) :
    eLpNorm (fun x => Φ x (f x) (g x)) 1 μ ≤ eLpNorm Φ ⊤ μ * (eLpNorm f 2 μ * eLpNorm g 2 μ) := by
  refine (eLpNorm_mono_real (g := fun x => ‖Φ x‖ * (‖f x‖ * ‖g x‖)) (fun x => ?_)).trans ?_
  · rw [← mul_assoc]; exact (Φ x).le_opNorm₂ (f x) (g x)
  · have := eLpNorm_top_two_two hΦ.norm hf.norm hg.norm (μ := μ)
    simpa only [eLpNorm_norm] using this

theorem eLpNorm_apply3_le {Φ : X → V →L[ℝ] W →L[ℝ] U →L[ℝ] Z} {f : X → V} {g : X → W}
    {h : X → U} (hΦ : AEStronglyMeasurable Φ μ) (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) (hh : AEStronglyMeasurable h μ) :
    eLpNorm (fun x => Φ x (f x) (g x) (h x)) 1 μ ≤
      eLpNorm Φ ⊤ μ * (eLpNorm f 2 μ * (eLpNorm g 4 μ * eLpNorm h 4 μ)) := by
  refine (eLpNorm_mono_real (g := fun x => ‖Φ x‖ * (‖f x‖ * (‖g x‖ * ‖h x‖))) (fun x => ?_)).trans ?_
  · calc ‖Φ x (f x) (g x) (h x)‖ ≤ ‖Φ x (f x) (g x)‖ * ‖h x‖ := (Φ x (f x) (g x)).le_opNorm _
      _ ≤ ‖Φ x (f x)‖ * ‖g x‖ * ‖h x‖ := by gcongr; exact (Φ x (f x)).le_opNorm _
      _ ≤ ‖Φ x‖ * ‖f x‖ * ‖g x‖ * ‖h x‖ := by gcongr; exact (Φ x).le_opNorm _
      _ = _ := by ring
  · have := eLpNorm_top_two_four_four hΦ.norm hf.norm hg.norm hh.norm (μ := μ)
    simpa only [eLpNorm_norm] using this

end Apply


/-! ### Jet fields with uniform packet bounds -/

section Jets

variable {T : ℝ} {C : Type} [Fintype C]

/-- **Uniformly bounded strong-packet jet field on a chart** (`eq:strong-geometry`–
`eq:strong-spinors` bounds): coframe values a.e. in the compact chart set `Ke`, the packets
bounded by `B` in their norms (`∂e, F, K, ∂Ψ, ∂Ψ̄` in `L²`; `A, H, Ψ, Ψ̄` in `L⁴`). -/
structure JetBound (Q : ChartBox T) (Ke : Set CoframeFibre) (B : ℝ≥0∞) (R : E4 → RJet C) :
    Prop where
  meas : AEStronglyMeasurable R Q.μ
  chart : ∀ᵐ x ∂Q.μ, (R x).e ∈ Ke
  de : eLpNorm (fun x => (R x).de) 2 Q.μ ≤ B
  A : eLpNorm (fun x => (R x).A) 4 Q.μ ≤ B
  F : eLpNorm (fun x => (R x).F) 2 Q.μ ≤ B
  H : eLpNorm (fun x => (R x).H) 4 Q.μ ≤ B
  K : eLpNorm (fun x => (R x).K) 2 Q.μ ≤ B
  Ψ : eLpNorm (fun x => (R x).Ψ) 4 Q.μ ≤ B
  dΨ : eLpNorm (fun x => (R x).dΨ) 2 Q.μ ≤ B
  Ψb : eLpNorm (fun x => (R x).Ψb) 4 Q.μ ≤ B
  dΨb : eLpNorm (fun x => (R x).dΨb) 2 Q.μ ≤ B

/-- **The packet distance of two jet fields** (the field part of `d_K`). -/
def jetDist (Q : ChartBox T) (R₁ R₂ : E4 → RJet C) : ℝ≥0∞ :=
  eLpNorm (fun x => (R₁ x).e - (R₂ x).e) ⊤ Q.μ + eLpNorm (fun x => (R₁ x).de - (R₂ x).de) 2 Q.μ +
    eLpNorm (fun x => (R₁ x).A - (R₂ x).A) 4 Q.μ + eLpNorm (fun x => (R₁ x).F - (R₂ x).F) 2 Q.μ +
    eLpNorm (fun x => (R₁ x).H - (R₂ x).H) 4 Q.μ + eLpNorm (fun x => (R₁ x).K - (R₂ x).K) 2 Q.μ +
    eLpNorm (fun x => (R₁ x).Ψ - (R₂ x).Ψ) 4 Q.μ +
    eLpNorm (fun x => (R₁ x).dΨ - (R₂ x).dΨ) 2 Q.μ +
    eLpNorm (fun x => (R₁ x).Ψb - (R₂ x).Ψb) 4 Q.μ +
    eLpNorm (fun x => (R₁ x).dΨb - (R₂ x).dΨb) 2 Q.μ

variable {Q : ChartBox T} {Ke : Set CoframeFibre} {B : ℝ≥0∞} {R R₁ R₂ : E4 → RJet C}

theorem JetBound.m_e (h : JetBound Q Ke B R) : AEStronglyMeasurable (fun x => (R x).e) Q.μ :=
  (πe (C := C)).continuous.comp_aestronglyMeasurable h.meas
theorem JetBound.m_de (h : JetBound Q Ke B R) : AEStronglyMeasurable (fun x => (R x).de) Q.μ :=
  (πde (C := C)).continuous.comp_aestronglyMeasurable h.meas
theorem JetBound.m_A (h : JetBound Q Ke B R) : AEStronglyMeasurable (fun x => (R x).A) Q.μ :=
  (πA (C := C)).continuous.comp_aestronglyMeasurable h.meas
theorem JetBound.m_F (h : JetBound Q Ke B R) : AEStronglyMeasurable (fun x => (R x).F) Q.μ :=
  (πF (C := C)).continuous.comp_aestronglyMeasurable h.meas
theorem JetBound.m_H (h : JetBound Q Ke B R) : AEStronglyMeasurable (fun x => (R x).H) Q.μ :=
  (πH (C := C)).continuous.comp_aestronglyMeasurable h.meas
theorem JetBound.m_K (h : JetBound Q Ke B R) : AEStronglyMeasurable (fun x => (R x).K) Q.μ :=
  (πK (C := C)).continuous.comp_aestronglyMeasurable h.meas
theorem JetBound.m_Ψ (h : JetBound Q Ke B R) : AEStronglyMeasurable (fun x => (R x).Ψ) Q.μ :=
  (πΨ (C := C)).continuous.comp_aestronglyMeasurable h.meas
theorem JetBound.m_dΨ (h : JetBound Q Ke B R) : AEStronglyMeasurable (fun x => (R x).dΨ) Q.μ :=
  (πdΨ (C := C)).continuous.comp_aestronglyMeasurable h.meas
theorem JetBound.m_Ψb (h : JetBound Q Ke B R) : AEStronglyMeasurable (fun x => (R x).Ψb) Q.μ :=
  (πΨb (C := C)).continuous.comp_aestronglyMeasurable h.meas
theorem JetBound.m_dΨb (h : JetBound Q Ke B R) : AEStronglyMeasurable (fun x => (R x).dΨb) Q.μ :=
  (πdΨb (C := C)).continuous.comp_aestronglyMeasurable h.meas

/-- Coefficient fields of the jet coframe are measurable. -/
theorem JetBound.m_coeff {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [SecondCountableTopology F] (h : JetBound Q Ke B R)
    (hsub : Ke ⊆ coframeGL) {Ψ : CoframeFibre → F} (hΨ : ContinuousOn Ψ coframeGL) :
    AEStronglyMeasurable (fun x => Ψ (R x).e) Q.μ := by
  borelize F
  exact aestronglyMeasurable_comp_of_continuousOn isOpen_coframeGL hΨ h.m_e.aemeasurable
    (h.chart.mono fun _ hx => hsub hx)
theorem le_jetDist_e :
    eLpNorm (fun x => (R₁ x).e - (R₂ x).e) ⊤ Q.μ ≤ jetDist Q R₁ R₂ :=
  le_add_right (le_add_right (le_add_right (le_add_right (le_add_right (le_add_right (le_add_right (le_add_right (le_add_right (le_rfl)))))))))

theorem le_jetDist_de :
    eLpNorm (fun x => (R₁ x).de - (R₂ x).de) 2 Q.μ ≤ jetDist Q R₁ R₂ :=
  le_add_right (le_add_right (le_add_right (le_add_right (le_add_right (le_add_right (le_add_right (le_add_right (le_add_left le_rfl))))))))

theorem le_jetDist_A :
    eLpNorm (fun x => (R₁ x).A - (R₂ x).A) 4 Q.μ ≤ jetDist Q R₁ R₂ :=
  le_add_right (le_add_right (le_add_right (le_add_right (le_add_right (le_add_right (le_add_right (le_add_left le_rfl)))))))

theorem le_jetDist_F :
    eLpNorm (fun x => (R₁ x).F - (R₂ x).F) 2 Q.μ ≤ jetDist Q R₁ R₂ :=
  le_add_right (le_add_right (le_add_right (le_add_right (le_add_right (le_add_right (le_add_left le_rfl))))))

theorem le_jetDist_H :
    eLpNorm (fun x => (R₁ x).H - (R₂ x).H) 4 Q.μ ≤ jetDist Q R₁ R₂ :=
  le_add_right (le_add_right (le_add_right (le_add_right (le_add_right (le_add_left le_rfl)))))

theorem le_jetDist_K :
    eLpNorm (fun x => (R₁ x).K - (R₂ x).K) 2 Q.μ ≤ jetDist Q R₁ R₂ :=
  le_add_right (le_add_right (le_add_right (le_add_right (le_add_left le_rfl))))

theorem le_jetDist_Ψ :
    eLpNorm (fun x => (R₁ x).Ψ - (R₂ x).Ψ) 4 Q.μ ≤ jetDist Q R₁ R₂ :=
  le_add_right (le_add_right (le_add_right (le_add_left le_rfl)))

theorem le_jetDist_dΨ :
    eLpNorm (fun x => (R₁ x).dΨ - (R₂ x).dΨ) 2 Q.μ ≤ jetDist Q R₁ R₂ :=
  le_add_right (le_add_right (le_add_left le_rfl))

theorem le_jetDist_Ψb :
    eLpNorm (fun x => (R₁ x).Ψb - (R₂ x).Ψb) 4 Q.μ ≤ jetDist Q R₁ R₂ :=
  le_add_right (le_add_left le_rfl)

theorem le_jetDist_dΨb :
    eLpNorm (fun x => (R₁ x).dΨb - (R₂ x).dΨb) 2 Q.μ ≤ jetDist Q R₁ R₂ :=
  le_add_left le_rfl

end Jets


/-! ### Banks -/

section Bank

variable {Ysec : Type} [Fintype Ysec]

/-- The bank part `|θ₁ - θ₂|` of `d_K`. -/
def bankDist (θ₁ θ₂ : CoefficientBank Ysec) : ℝ≥0∞ := edist (bankVec θ₁) (bankVec θ₂)

theorem ofReal_abs_coord_le (θ₁ θ₂ : CoefficientBank Ysec) (i : Fin 7) :
    ENNReal.ofReal |(bankCoords θ₁).1 i - (bankCoords θ₂).1 i| ≤ bankDist θ₁ θ₂ := by
  have h1 : ENNReal.ofReal |(bankCoords θ₁).1 i - (bankCoords θ₂).1 i| =
      edist ((bankVec θ₁).1 i) ((bankVec θ₂).1 i) := by
    rw [edist_dist, Real.dist_eq]; rfl
  rw [h1]
  exact (edist_le_pi_edist _ _ i).trans (by rw [bankDist, Prod.edist_eq]; exact le_max_left _ _)

theorem kappa_le (θ₁ θ₂ : CoefficientBank Ysec) :
    ENNReal.ofReal |θ₁.kappa - θ₂.kappa| ≤ bankDist θ₁ θ₂ := by
  simpa [bankCoords] using ofReal_abs_coord_le θ₁ θ₂ 0
theorem Lambda_le (θ₁ θ₂ : CoefficientBank Ysec) :
    ENNReal.ofReal |θ₁.Lambda - θ₂.Lambda| ≤ bankDist θ₁ θ₂ := by
  simpa [bankCoords] using ofReal_abs_coord_le θ₁ θ₂ 1
theorem g1_le (θ₁ θ₂ : CoefficientBank Ysec) :
    ENNReal.ofReal |θ₁.g1 - θ₂.g1| ≤ bankDist θ₁ θ₂ := by
  simpa [bankCoords] using ofReal_abs_coord_le θ₁ θ₂ 2
theorem g2_le (θ₁ θ₂ : CoefficientBank Ysec) :
    ENNReal.ofReal |θ₁.g2 - θ₂.g2| ≤ bankDist θ₁ θ₂ := by
  simpa [bankCoords] using ofReal_abs_coord_le θ₁ θ₂ 3
theorem g3_le (θ₁ θ₂ : CoefficientBank Ysec) :
    ENNReal.ofReal |θ₁.g3 - θ₂.g3| ≤ bankDist θ₁ θ₂ := by
  simpa [bankCoords] using ofReal_abs_coord_le θ₁ θ₂ 4
theorem lambdaH_le (θ₁ θ₂ : CoefficientBank Ysec) :
    ENNReal.ofReal |θ₁.lambdaH - θ₂.lambdaH| ≤ bankDist θ₁ θ₂ := by
  simpa [bankCoords] using ofReal_abs_coord_le θ₁ θ₂ 5
theorem vH_le (θ₁ θ₂ : CoefficientBank Ysec) :
    ENNReal.ofReal |θ₁.vH - θ₂.vH| ≤ bankDist θ₁ θ₂ := by
  simpa [bankCoords] using ofReal_abs_coord_le θ₁ θ₂ 6

/-- `|a⁻¹ - b⁻¹| ≤ c⁻² |a - b|` for `a, b ≥ c > 0`. -/
theorem abs_inv_sub_le {a b c : ℝ} (hc : 0 < c) (ha : c ≤ a) (hb : c ≤ b) :
    |a⁻¹ - b⁻¹| ≤ (c ^ 2)⁻¹ * |a - b| := by
  have ha0 : 0 < a := hc.trans_le ha
  have hb0 : 0 < b := hc.trans_le hb
  rw [inv_sub_inv ha0.ne' hb0.ne', abs_div, abs_of_pos (mul_pos ha0 hb0), abs_sub_comm,
    div_eq_inv_mul]
  refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
  exact inv_anti₀ (by positivity) (by nlinarith)

/-- `|f₁g₁ - f₂g₂| ≤ |f₁||g₁ - g₂| + |g₂||f₁ - f₂|`. -/
theorem abs_mul_sub_mul_le (f₁ f₂ g₁ g₂ : ℝ) :
    |f₁ * g₁ - f₂ * g₂| ≤ |f₁| * |g₁ - g₂| + |g₂| * |f₁ - f₂| := by
  have e : f₁ * g₁ - f₂ * g₂ = f₁ * (g₁ - g₂) + g₂ * (f₁ - f₂) := by ring
  rw [e]
  exact (abs_add_le _ _).trans (by rw [abs_mul, abs_mul])

end Bank

/-! ### Measurability of term fields -/

section Meas

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W]
  [NormedSpace ℝ W]

theorem aesm_apply {Φ : X → V →L[ℝ] W} {f : X → V} (hΦ : AEStronglyMeasurable Φ μ)
    (hf : AEStronglyMeasurable f μ) : AEStronglyMeasurable (fun x => Φ x (f x)) μ :=
  (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := V) (F := W)).continuous.comp_aestronglyMeasurable
    (hΦ.prodMk hf)

end Meas

/-! ### The gravitational sector -/

section Gravity

variable {T : ℝ} {C : Type} [Fintype C] {Ysec : Type} [Fintype Ysec]

theorem gravCov_eq_terms (θ : CoefficientBank Ysec) (R : RJet C) :
    gravCov θ R = (2 * θ.kappa)⁻¹ • gravC1 (C := C) R.e R.de R.de +
      (2 * θ.kappa)⁻¹ • gravC2 (C := C) R.e R.de +
      ((2 * θ.kappa)⁻¹ * (-(2 * θ.Lambda))) • gravC3 (C := C) R.e 1 := by
  simp only [gravCov, gravCovF, smul_add, smul_smul, ContinuousLinearMap.add_apply]

/-- Combining the unscaled bound with scalar factors. -/
theorem scaled_combine {X : Type*} [MeasurableSpace X] {μ : Measure X} {Z : Type*}
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] {A₁ A₂ : X → Z} (hA₁ : AEStronglyMeasurable A₁ μ)
    (hA₂ : AEStronglyMeasurable A₂ μ) {c₁ c₂ Mc : ℝ} (hc₁ : |c₁| ≤ Mc) {K N Lθ D : ℝ≥0∞}
    (hK : eLpNorm (fun x => A₁ x - A₂ x) 1 μ ≤ K * D) (hN : eLpNorm A₂ 1 μ ≤ N)
    (hθ : ENNReal.ofReal |c₁ - c₂| ≤ Lθ * D) :
    eLpNorm (fun x => c₁ • A₁ x - c₂ • A₂ x) 1 μ ≤ (ENNReal.ofReal Mc * K + Lθ * N) * D :=
  (scaled_term_bound hA₁ hA₂ hc₁).trans (by
    calc ENNReal.ofReal Mc * eLpNorm (fun x => A₁ x - A₂ x) 1 μ +
          ENNReal.ofReal |c₁ - c₂| * eLpNorm A₂ 1 μ
        ≤ ENNReal.ofReal Mc * (K * D) + Lθ * D * N := by gcongr
      _ = _ := by ring)

theorem bank_le_D {R₁ R₂ : E4 → RJet C} {Q : ChartBox T} (θ₁ θ₂ : CoefficientBank Ysec) :
    bankDist θ₁ θ₂ ≤ jetDist Q R₁ R₂ + bankDist θ₁ θ₂ := le_add_self

theorem e_le_D {R₁ R₂ : E4 → RJet C} {Q : ChartBox T} (θ₁ θ₂ : CoefficientBank Ysec) :
    eLpNorm (fun x => (R₁ x).e - (R₂ x).e) ⊤ Q.μ ≤ jetDist Q R₁ R₂ + bankDist θ₁ θ₂ :=
  le_jetDist_e.trans le_self_add

/-- `|(2a)⁻¹ - (2b)⁻¹| ≤ k |a - b|` for `a, b ≥ c > 0`. -/
theorem abs_half_inv_sub_le {a b c : ℝ} (hc : 0 < c) (ha : c ≤ a) (hb : c ≤ b) :
    |(2 * a)⁻¹ - (2 * b)⁻¹| ≤ (2 * ((2 * c) ^ 2)⁻¹) * |a - b| := by
  have := abs_inv_sub_le (by positivity : 0 < 2 * c) (by linarith : 2 * c ≤ 2 * a)
    (by linarith : 2 * c ≤ 2 * b)
  rw [show 2 * a - 2 * b = 2 * (a - b) by ring, abs_mul, abs_two] at this
  linarith

theorem abs_half_inv_le {a c : ℝ} (hc : 0 < c) (ha : c ≤ a) : |(2 * a)⁻¹| ≤ (2 * c)⁻¹ := by
  have ha0 : 0 < a := hc.trans_le ha
  rw [abs_of_pos (by positivity)]
  exact inv_anti₀ (by positivity) (by linarith)

/-- Bank-scalar bound for `(2κ)⁻¹·(-2Λ)`. -/
theorem bank_c3_le {c Mb Lc1 : ℝ} (hc : 0 < c) (hMb : 0 ≤ Mb)
    (hLc1 : Lc1 = 2 * ((2 * c) ^ 2)⁻¹) {θ₁ θ₂ : CoefficientBank Ysec} (hκ₁ : c ≤ θ₁.kappa)
    (hκ₂ : c ≤ θ₂.kappa) (hΛ₂ : |θ₂.Lambda| ≤ Mb) :
    ENNReal.ofReal |(2 * θ₁.kappa)⁻¹ * (-(2 * θ₁.Lambda)) -
      (2 * θ₂.kappa)⁻¹ * (-(2 * θ₂.Lambda))| ≤
      (ENNReal.ofReal ((2 * c)⁻¹ * 2) + ENNReal.ofReal (2 * Mb * Lc1)) * bankDist θ₁ θ₂ := by
  have h1 := abs_mul_sub_mul_le ((2 * θ₁.kappa)⁻¹) ((2 * θ₂.kappa)⁻¹) (-(2 * θ₁.Lambda))
    (-(2 * θ₂.Lambda))
  have h2 : |-(2 * θ₁.Lambda) - -(2 * θ₂.Lambda)| = 2 * |θ₁.Lambda - θ₂.Lambda| := by
    rw [show -(2 * θ₁.Lambda) - -(2 * θ₂.Lambda) = -(2 * (θ₁.Lambda - θ₂.Lambda)) by ring,
      abs_neg, abs_mul, abs_two]
  have h3 : |-(2 * θ₂.Lambda)| ≤ 2 * Mb := by
    rw [abs_neg, abs_mul, abs_two]; linarith
  have h4 := abs_half_inv_sub_le hc hκ₁ hκ₂
  rw [← hLc1] at h4
  have h5 := abs_half_inv_le hc hκ₁
  have hLp : 0 ≤ Lc1 := by rw [hLc1]; positivity
  have t1 := mul_le_mul h3 h4 (abs_nonneg _) (by positivity)
  have t2 := mul_le_mul_of_nonneg_right h5
    (by positivity : (0 : ℝ) ≤ 2 * |θ₁.Lambda - θ₂.Lambda|)
  have hb : |(2 * θ₁.kappa)⁻¹ * (-(2 * θ₁.Lambda)) - (2 * θ₂.kappa)⁻¹ * (-(2 * θ₂.Lambda))| ≤
      ((2 * c)⁻¹ * 2) * |θ₁.Lambda - θ₂.Lambda| + (2 * Mb * Lc1) * |θ₁.kappa - θ₂.kappa| := by
    refine h1.trans ?_
    rw [h2]
    calc |(2 * θ₁.kappa)⁻¹| * (2 * |θ₁.Lambda - θ₂.Lambda|) +
          |-(2 * θ₂.Lambda)| * |(2 * θ₁.kappa)⁻¹ - (2 * θ₂.kappa)⁻¹|
        ≤ (2 * c)⁻¹ * (2 * |θ₁.Lambda - θ₂.Lambda|) + 2 * Mb * (Lc1 * |θ₁.kappa - θ₂.kappa|) :=
          add_le_add t2 t1
      _ = _ := by ring
  have hc2 : (0 : ℝ) ≤ (2 * c)⁻¹ * 2 := by positivity
  have hm2 : (0 : ℝ) ≤ 2 * Mb * Lc1 := by positivity
  calc ENNReal.ofReal |(2 * θ₁.kappa)⁻¹ * (-(2 * θ₁.Lambda)) -
        (2 * θ₂.kappa)⁻¹ * (-(2 * θ₂.Lambda))|
      ≤ ENNReal.ofReal (((2 * c)⁻¹ * 2) * |θ₁.Lambda - θ₂.Lambda| +
          (2 * Mb * Lc1) * |θ₁.kappa - θ₂.kappa|) := ENNReal.ofReal_le_ofReal hb
    _ = ENNReal.ofReal ((2 * c)⁻¹ * 2) * ENNReal.ofReal |θ₁.Lambda - θ₂.Lambda| +
          ENNReal.ofReal (2 * Mb * Lc1) * ENNReal.ofReal |θ₁.kappa - θ₂.kappa| := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul hc2,
          ENNReal.ofReal_mul hm2]
    _ ≤ ENNReal.ofReal ((2 * c)⁻¹ * 2) * bankDist θ₁ θ₂ +
          ENNReal.ofReal (2 * Mb * Lc1) * bankDist θ₁ θ₂ := by
        gcongr
        · exact Lambda_le θ₁ θ₂
        · exact kappa_le θ₁ θ₂
    _ = _ := by ring

set_option maxHeartbeats 4000000 in
/-- **`prop:variation-continuity`, gravitational sector, jet form**: on uniformly bounded
strong-packet jet fields, `‖gravCov_{θ₁}(R₁) - gravCov_{θ₂}(R₂)‖_{L¹(Q)} ≤ C (d(R₁,R₂) + |θ₁-θ₂|)`. -/
theorem grav_lipschitz {Q : ChartBox T} {Ke : Set CoframeFibre} (hKe : IsCompact Ke)
    (hsub : Ke ⊆ coframeGL) {P : Set (CoefficientBank Ysec)} {c Mb : ℝ} (hc : 0 < c)
    (hMb : 0 ≤ Mb) (hP : ∀ θ ∈ P, c ≤ θ.kappa ∧ |θ.Lambda| ≤ Mb) {B : ℝ≥0∞} (hB : B ≠ ⊤) :
    ∃ Cg : ℝ≥0∞, Cg ≠ ⊤ ∧ ∀ (R₁ R₂ : E4 → RJet C) (θ₁ θ₂ : CoefficientBank Ysec),
      θ₁ ∈ P → θ₂ ∈ P → JetBound Q Ke B R₁ → JetBound Q Ke B R₂ →
        eLpNorm (fun x => gravCov θ₁ (R₁ x) - gravCov θ₂ (R₂ x)) 1 Q.μ ≤
          Cg * (jetDist Q R₁ R₂ + bankDist θ₁ θ₂) := by
  obtain ⟨L1, M1, hL1, hM1, hb1, hl1⟩ :=
    exists_lipschitz_bound (CovSmooth.contDiffOn_gravC1 (C := C) (n := 1)) hKe hsub
  obtain ⟨L2, M2, hL2, hM2, hb2, hl2⟩ :=
    exists_lipschitz_bound (CovSmooth.contDiffOn_gravC2 (C := C) (n := 1)) hKe hsub
  obtain ⟨L3, M3, hL3, hM3, hb3, hl3⟩ :=
    exists_lipschitz_bound (CovSmooth.contDiffOn_gravC3 (C := C) (n := 1)) hKe hsub
  have hc1 : ContinuousOn (gravC1 (C := C)) coframeGL :=
    (CovSmooth.contDiffOn_gravC1 (C := C) (n := 0)).continuousOn
  have hc2 : ContinuousOn (gravC2 (C := C)) coframeGL :=
    (CovSmooth.contDiffOn_gravC2 (C := C) (n := 0)).continuousOn
  have hc3 : ContinuousOn (gravC3 (C := C)) coframeGL :=
    (CovSmooth.contDiffOn_gravC3 (C := C) (n := 0)).continuousOn
  obtain ⟨VQ, hVQd⟩ : ∃ v, v = Q.μ univ := ⟨_, rfl⟩
  have hVQ : VQ ≠ ⊤ := by rw [hVQd]; exact measure_ne_top _ _
  obtain ⟨cQ, hcQd⟩ : ∃ v : ℝ≥0∞,
      v = Q.μ univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) := ⟨_, rfl⟩
  have hcQ : cQ ≠ ⊤ := by rw [hcQd]; exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top _ _)
  obtain ⟨Mc1, hMc1⟩ : ∃ r : ℝ, r = (2 * c)⁻¹ := ⟨_, rfl⟩
  obtain ⟨Lc1, hLc1⟩ : ∃ r : ℝ, r = 2 * ((2 * c) ^ 2)⁻¹ := ⟨_, rfl⟩
  obtain ⟨Mc3, hMc3⟩ : ∃ r : ℝ, r = 2 * Mb * (2 * c)⁻¹ := ⟨_, rfl⟩
  have hLc1p : 0 ≤ Lc1 := by rw [hLc1]; positivity
  obtain ⟨K1, hK1⟩ : ∃ k : ℝ≥0∞, k = ENNReal.ofReal Mc1 * (ENNReal.ofReal L1 * (B * B) +
      ENNReal.ofReal M1 * (1 * B) + ENNReal.ofReal M1 * (B * 1)) +
      ENNReal.ofReal Lc1 * (ENNReal.ofReal M1 * (B * B)) := ⟨_, rfl⟩
  obtain ⟨K2, hK2⟩ : ∃ k : ℝ≥0∞, k = ENNReal.ofReal Mc1 * (ENNReal.ofReal L2 * (B * cQ) +
      ENNReal.ofReal M2 * cQ) + ENNReal.ofReal Lc1 * (ENNReal.ofReal M2 * (B * cQ)) := ⟨_, rfl⟩
  obtain ⟨K3, hK3⟩ : ∃ k : ℝ≥0∞, k = ENNReal.ofReal Mc3 * (ENNReal.ofReal L3 * VQ +
      ENNReal.ofReal M3 * 0) + (ENNReal.ofReal ((2 * c)⁻¹ * 2) + ENNReal.ofReal (2 * Mb * Lc1)) *
        (ENNReal.ofReal M3 * VQ) := ⟨_, rfl⟩
  have hfin : K1 + K2 + K3 ≠ ⊤ := by
    rw [hK1, hK2, hK3]
    finiteness
  refine ⟨K1 + K2 + K3, hfin, ?_⟩
  intro R₁ R₂ θ₁ θ₂ hθ₁ hθ₂ h₁ h₂
  obtain ⟨D, hD⟩ : ∃ d, d = jetDist Q R₁ R₂ + bankDist θ₁ θ₂ := ⟨_, rfl⟩
  obtain ⟨hκ₁, hΛ₁⟩ := hP θ₁ hθ₁
  obtain ⟨hκ₂, hΛ₂⟩ := hP θ₂ hθ₂
  have hDe : eLpNorm (fun x => (R₁ x).e - (R₂ x).e) ⊤ Q.μ ≤ D := by
    rw [hD]; exact e_le_D θ₁ θ₂
  have hDθ : bankDist θ₁ θ₂ ≤ D := by rw [hD]; exact bank_le_D θ₁ θ₂
  have hDde : eLpNorm (fun x => (R₁ x).de - (R₂ x).de) 2 Q.μ ≤ 1 * D := by
    rw [one_mul, hD]; exact le_jetDist_de.trans le_self_add
  -- bank scalars
  have hcs1 : ENNReal.ofReal |(2 * θ₁.kappa)⁻¹ - (2 * θ₂.kappa)⁻¹| ≤ ENNReal.ofReal Lc1 * D := by
    refine (ENNReal.ofReal_le_ofReal (abs_half_inv_sub_le hc hκ₁ hκ₂)).trans ?_
    rw [← hLc1, ENNReal.ofReal_mul hLc1p]
    gcongr
    exact (kappa_le θ₁ θ₂).trans hDθ
  have hcs3 : ENNReal.ofReal |(2 * θ₁.kappa)⁻¹ * (-(2 * θ₁.Lambda)) -
      (2 * θ₂.kappa)⁻¹ * (-(2 * θ₂.Lambda))| ≤
      (ENNReal.ofReal ((2 * c)⁻¹ * 2) + ENNReal.ofReal (2 * Mb * Lc1)) * D :=
    (bank_c3_le hc hMb hLc1 hκ₁ hκ₂ hΛ₂).trans (by gcongr)
  have habs1 : ∀ θ ∈ P, |(2 * θ.kappa)⁻¹| ≤ Mc1 := fun θ hθ => by
    rw [hMc1]; exact abs_half_inv_le hc (hP θ hθ).1
  have habs3 : ∀ θ ∈ P, |(2 * θ.kappa)⁻¹ * (-(2 * θ.Lambda))| ≤ Mc3 := fun θ hθ => by
    rw [abs_mul, abs_neg, abs_mul, abs_two]
    have := abs_half_inv_le hc (hP θ hθ).1
    have := (hP θ hθ).2
    calc |(2 * θ.kappa)⁻¹| * (2 * |θ.Lambda|) ≤ (2 * c)⁻¹ * (2 * Mb) := by gcongr
      _ = Mc3 := by rw [hMc3]; ring
  -- term 1
  have cf1 := coeff_field hL1 hb1 hl1 h₁.chart h₂.chart
  have hm11 : AEStronglyMeasurable (fun x => gravC1 (C := C) (R₁ x).e) Q.μ := h₁.m_coeff hsub hc1
  have hm12 : AEStronglyMeasurable (fun x => gravC1 (C := C) (R₂ x).e) Q.μ := h₂.m_coeff hsub hc1
  have hΔ1 : eLpNorm (fun x => gravC1 (C := C) (R₁ x).e - gravC1 (C := C) (R₂ x).e) ⊤ Q.μ ≤
      ENNReal.ofReal L1 * D := cf1.1.trans (by gcongr)
  have hB1 : eLpNorm (fun x => gravC1 (C := C) (R₂ x).e) ⊤ Q.μ ≤ ENNReal.ofReal M1 := cf1.2
  have U1 : eLpNorm (fun x => gravC1 (C := C) (R₁ x).e (R₁ x).de (R₁ x).de -
      gravC1 (C := C) (R₂ x).e (R₂ x).de (R₂ x).de) 1 Q.μ ≤
      (ENNReal.ofReal L1 * (B * B) + ENNReal.ofReal M1 * (1 * B) +
        ENNReal.ofReal M1 * (B * 1)) * D :=
    term2_bound (Φ₁ := fun x => gravC1 (C := C) (R₁ x).e)
      (Φ₂ := fun x => gravC1 (C := C) (R₂ x).e) (X₁ := fun x => (R₁ x).de)
      (X₂ := fun x => (R₂ x).de) (Y₁ := fun x => (R₁ x).de) (Y₂ := fun x => (R₂ x).de)
      hm11 hm12 h₁.m_de h₂.m_de h₁.m_de h₂.m_de hΔ1 hB1 h₁.de h₂.de h₁.de hDde hDde
  have N1 : eLpNorm (fun x => gravC1 (C := C) (R₂ x).e (R₂ x).de (R₂ x).de) 1 Q.μ ≤
      ENNReal.ofReal M1 * (B * B) :=
    (eLpNorm_apply2_le (Φ := fun x => gravC1 (C := C) (R₂ x).e) (f := fun x => (R₂ x).de)
      (g := fun x => (R₂ x).de) hm12 h₂.m_de h₂.m_de).trans
      (mul_le_mul' hB1 (mul_le_mul' h₂.de h₂.de))
  have T1 : eLpNorm (fun x => (2 * θ₁.kappa)⁻¹ • gravC1 (C := C) (R₁ x).e (R₁ x).de (R₁ x).de -
      (2 * θ₂.kappa)⁻¹ • gravC1 (C := C) (R₂ x).e (R₂ x).de (R₂ x).de) 1 Q.μ ≤ K1 * D := by
    rw [hK1]
    exact scaled_combine (A₁ := fun x => gravC1 (C := C) (R₁ x).e (R₁ x).de (R₁ x).de)
      (A₂ := fun x => gravC1 (C := C) (R₂ x).e (R₂ x).de (R₂ x).de)
      (aesm_apply (aesm_apply hm11 h₁.m_de) h₁.m_de)
      (aesm_apply (aesm_apply hm12 h₂.m_de) h₂.m_de) (habs1 θ₁ hθ₁) U1 N1 hcs1
  -- term 2
  have cf2 := coeff_field hL2 hb2 hl2 h₁.chart h₂.chart
  have hm21 : AEStronglyMeasurable (fun x => gravC2 (C := C) (R₁ x).e) Q.μ := h₁.m_coeff hsub hc2
  have hm22 : AEStronglyMeasurable (fun x => gravC2 (C := C) (R₂ x).e) Q.μ := h₂.m_coeff hsub hc2
  have hΔ2 : eLpNorm (fun x => gravC2 (C := C) (R₁ x).e - gravC2 (C := C) (R₂ x).e) ⊤ Q.μ ≤
      ENNReal.ofReal L2 * D := cf2.1.trans (by gcongr)
  have hB2 : eLpNorm (fun x => gravC2 (C := C) (R₂ x).e) ⊤ Q.μ ≤ ENNReal.ofReal M2 := cf2.2
  have hde1 : eLpNorm (fun x => (R₁ x).de) 1 Q.μ ≤ B * cQ :=
    (eLpNorm_le_of_le_exp h₁.m_de (q := 2) (by norm_num)).trans (by rw [hcQd]; gcongr; exact h₁.de)
  have hde2 : eLpNorm (fun x => (R₂ x).de) 1 Q.μ ≤ B * cQ :=
    (eLpNorm_le_of_le_exp h₂.m_de (q := 2) (by norm_num)).trans (by rw [hcQd]; gcongr; exact h₂.de)
  have hdde1 : eLpNorm (fun x => (R₁ x).de - (R₂ x).de) 1 Q.μ ≤ cQ * D :=
    (eLpNorm_le_of_le_exp (h₁.m_de.sub h₂.m_de) (q := 2) (by norm_num)).trans
      (by rw [mul_comm cQ, hcQd, hD]; gcongr; exact le_jetDist_de.trans le_self_add)
  have U2 : eLpNorm (fun x => gravC2 (C := C) (R₁ x).e (R₁ x).de -
      gravC2 (C := C) (R₂ x).e (R₂ x).de) 1 Q.μ ≤
      (ENNReal.ofReal L2 * (B * cQ) + ENNReal.ofReal M2 * cQ) * D :=
    term1_bound (Φ₁ := fun x => gravC2 (C := C) (R₁ x).e)
      (Φ₂ := fun x => gravC2 (C := C) (R₂ x).e) (X₁ := fun x => (R₁ x).de)
      (X₂ := fun x => (R₂ x).de) hm21 hm22 h₁.m_de h₂.m_de hΔ2 hB2 hde1 hdde1
  have N2 : eLpNorm (fun x => gravC2 (C := C) (R₂ x).e (R₂ x).de) 1 Q.μ ≤
      ENNReal.ofReal M2 * (B * cQ) :=
    (eLpNorm_apply1_le (Φ := fun x => gravC2 (C := C) (R₂ x).e) (f := fun x => (R₂ x).de)
      hm22 h₂.m_de 1).trans (mul_le_mul' hB2 hde2)
  have T2 : eLpNorm (fun x => (2 * θ₁.kappa)⁻¹ • gravC2 (C := C) (R₁ x).e (R₁ x).de -
      (2 * θ₂.kappa)⁻¹ • gravC2 (C := C) (R₂ x).e (R₂ x).de) 1 Q.μ ≤ K2 * D := by
    rw [hK2]
    exact scaled_combine (A₁ := fun x => gravC2 (C := C) (R₁ x).e (R₁ x).de)
      (A₂ := fun x => gravC2 (C := C) (R₂ x).e (R₂ x).de)
      (aesm_apply hm21 h₁.m_de) (aesm_apply hm22 h₂.m_de) (habs1 θ₁ hθ₁) U2 N2 hcs1
  -- term 3
  have cf3 := coeff_field hL3 hb3 hl3 h₁.chart h₂.chart
  have hm31 : AEStronglyMeasurable (fun x => gravC3 (C := C) (R₁ x).e) Q.μ := h₁.m_coeff hsub hc3
  have hm32 : AEStronglyMeasurable (fun x => gravC3 (C := C) (R₂ x).e) Q.μ := h₂.m_coeff hsub hc3
  have hΔ3 : eLpNorm (fun x => gravC3 (C := C) (R₁ x).e - gravC3 (C := C) (R₂ x).e) ⊤ Q.μ ≤
      ENNReal.ofReal L3 * D := cf3.1.trans (by gcongr)
  have hB3 : eLpNorm (fun x => gravC3 (C := C) (R₂ x).e) ⊤ Q.μ ≤ ENNReal.ofReal M3 := cf3.2
  have hone : eLpNorm (fun _ : E4 => (1 : ℝ)) 1 Q.μ ≤ VQ := by
    have := eLpNorm_le_of_ae_bound (μ := Q.μ) (p := 1) (f := fun _ : E4 => (1 : ℝ)) (C := 1)
      (Eventually.of_forall fun _ => by simp)
    rw [hVQd]; simpa using this
  have hzero : eLpNorm (fun _ : E4 => (1 : ℝ) - 1) 1 Q.μ ≤ 0 * D := by simp
  have U3 : eLpNorm (fun x => gravC3 (C := C) (R₁ x).e 1 - gravC3 (C := C) (R₂ x).e 1) 1 Q.μ ≤
      (ENNReal.ofReal L3 * VQ + ENNReal.ofReal M3 * 0) * D :=
    term1_bound (Φ₁ := fun x => gravC3 (C := C) (R₁ x).e)
      (Φ₂ := fun x => gravC3 (C := C) (R₂ x).e) (X₁ := fun _ => (1 : ℝ))
      (X₂ := fun _ => (1 : ℝ)) hm31 hm32 aestronglyMeasurable_const aestronglyMeasurable_const
      hΔ3 hB3 hone hzero
  have N3 : eLpNorm (fun x => gravC3 (C := C) (R₂ x).e 1) 1 Q.μ ≤ ENNReal.ofReal M3 * VQ :=
    (eLpNorm_apply1_le (Φ := fun x => gravC3 (C := C) (R₂ x).e) (f := fun _ => (1 : ℝ))
      hm32 aestronglyMeasurable_const 1).trans (mul_le_mul' hB3 hone)
  have T3 : eLpNorm (fun x => ((2 * θ₁.kappa)⁻¹ * (-(2 * θ₁.Lambda))) • gravC3 (C := C) (R₁ x).e 1 -
      ((2 * θ₂.kappa)⁻¹ * (-(2 * θ₂.Lambda))) • gravC3 (C := C) (R₂ x).e 1) 1 Q.μ ≤ K3 * D := by
    rw [hK3]
    exact scaled_combine (A₁ := fun x => gravC3 (C := C) (R₁ x).e 1)
      (A₂ := fun x => gravC3 (C := C) (R₂ x).e 1)
      (aesm_apply (f := fun _ => (1 : ℝ)) hm31 aestronglyMeasurable_const)
      (aesm_apply (f := fun _ => (1 : ℝ)) hm32 aestronglyMeasurable_const) (habs3 θ₁ hθ₁) U3 N3 hcs3
  -- assembly
  have e : (fun x => gravCov θ₁ (R₁ x) - gravCov θ₂ (R₂ x)) = fun x =>
      ((2 * θ₁.kappa)⁻¹ • gravC1 (C := C) (R₁ x).e (R₁ x).de (R₁ x).de -
        (2 * θ₂.kappa)⁻¹ • gravC1 (C := C) (R₂ x).e (R₂ x).de (R₂ x).de) +
      ((2 * θ₁.kappa)⁻¹ • gravC2 (C := C) (R₁ x).e (R₁ x).de -
        (2 * θ₂.kappa)⁻¹ • gravC2 (C := C) (R₂ x).e (R₂ x).de) +
      (((2 * θ₁.kappa)⁻¹ * (-(2 * θ₁.Lambda))) • gravC3 (C := C) (R₁ x).e 1 -
        ((2 * θ₂.kappa)⁻¹ * (-(2 * θ₂.Lambda))) • gravC3 (C := C) (R₂ x).e 1) := by
    funext x
    rw [gravCov_eq_terms, gravCov_eq_terms]
    abel
  have m1 := ((aesm_apply (aesm_apply hm11 h₁.m_de) h₁.m_de).const_smul ((2 * θ₁.kappa)⁻¹)).sub
    ((aesm_apply (aesm_apply hm12 h₂.m_de) h₂.m_de).const_smul ((2 * θ₂.kappa)⁻¹))
  have m2 := ((aesm_apply hm21 h₁.m_de).const_smul ((2 * θ₁.kappa)⁻¹)).sub
    ((aesm_apply hm22 h₂.m_de).const_smul ((2 * θ₂.kappa)⁻¹))
  have m3 := ((aesm_apply (f := fun _ => (1 : ℝ)) hm31 aestronglyMeasurable_const).const_smul
    ((2 * θ₁.kappa)⁻¹ * (-(2 * θ₁.Lambda)))).sub
    ((aesm_apply (f := fun _ => (1 : ℝ)) hm32 aestronglyMeasurable_const).const_smul
      ((2 * θ₂.kappa)⁻¹ * (-(2 * θ₂.Lambda))))
  rw [e, ← hD]
  calc _ ≤ _ + _ := eLpNorm_add_le (m1.add m2) m3 le_rfl
    _ ≤ (_ + _) + _ := add_le_add (eLpNorm_add_le m1 m2 le_rfl) le_rfl
    _ ≤ K1 * D + K2 * D + K3 * D := add_le_add (add_le_add T1 T2) T3
    _ = (K1 + K2 + K3) * D := by ring

end Gravity

end VarLip
end EinsteinSM
end RenewalGeometry
