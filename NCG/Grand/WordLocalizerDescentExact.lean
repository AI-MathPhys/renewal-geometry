/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.WordLocalizerScoreAndInfluence

/-!
# Word-localizer descent: kernel inclusion, occurrence trace, whitened localizer

Completes `thm:GT-word-localizer-descent` on top of
`ExactSourceSchurResidual` and `WordLocalizerScoreAndInfluence`.

Let `W` synthesize the returned words and `S` the score family on the same
coefficient list, `H = W^* W`, `G = S^* S`, and let `Q_H = H^† H` be the
orthogonal projection onto the supported coefficient quotient `(Ker H)^⊥`.

* `mulVec_gram_eq_zero_iff`: `Ker (S^* S) = Ker S`;
* `occurrence_defect_eq`: `Δ_occ(H,G) = Re Tr((I - Q_H) G) = ‖S (I - Q_H)‖²_HS`;
* `occurrence_defect_eq_zero_iff`, `ker_inclusion_iff_supported`,
  `word_localizer_descent` (NL.1): `Ker H ⊆ Ker G` ⇔ `Δ_occ = 0` ⇔
  `S = S Q_H`;
* `wordLocalizer` (NL.2): the localizer `Λ = W^{†*} G W^{†}` (with
  `W^† = H^† W^*`) is positive, supported on `Ran W`, and on the zero branch
  satisfies `W^* Λ W = G` (`wordLocalizer_represents`); it is the **unique**
  operator supported on the word range with this property
  (`wordLocalizer_unique`);
* `word_relation_descends` (NL.3, zero branch): `R_w = 0` gives `V = W T` with
  the explicit reduced relation `T = H^† W^* V`;
* the innovation package (NL.3) and the score-relation identity (NL.4) are
  `WordLocalizerScoreAndInfluence.word_localizer_innovation_package` and
  `score_relation_residual_identity` / `score_relation_residual_eq_zero_iff`.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace NCG
namespace WordLocalizerDescent

set_option linter.unusedDecidableInType false

variable {h e : ℕ}

/-- The coefficient-support projection `Q_H = H^† H` (= `H H^†`). -/
noncomputable def supportProjection (W : Matrix (Fin h) (Fin e) ℂ) : Matrix (Fin e) (Fin e) ℂ :=
  sourceGramPseudoinverse W * (Wᴴ * W)

theorem supportProjection_props (W : Matrix (Fin h) (Fin e) ℂ) :
    (supportProjection W)ᴴ = supportProjection W ∧
      supportProjection W * supportProjection W = supportProjection W ∧
      W * supportProjection W = W :=
  sourceCoefficientSupport_properties W

theorem supportProjection_comm (W : Matrix (Fin h) (Fin e) ℂ) :
    supportProjection W = (Wᴴ * W) * sourceGramPseudoinverse W := by
  unfold supportProjection
  rw [sourceGramPseudoinverse_commutes]

/-- `Ker (S^* S) = Ker S` for any finite synthesis. -/
theorem mulVec_gram_eq_zero_iff (S : Matrix (Fin h) (Fin e) ℂ) (x : Fin e → ℂ) :
    (Sᴴ * S) *ᵥ x = 0 ↔ S *ᵥ x = 0 := by
  constructor
  · intro hx
    have h1 : star x ⬝ᵥ ((Sᴴ * S) *ᵥ x) = 0 := by rw [hx, dotProduct_zero]
    rw [← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec] at h1
    exact dotProduct_star_self_eq_zero.mp h1
  · intro hx
    rw [← mulVec_mulVec, hx, mulVec_zero]

/-- Vectors in `Ker W` are annihilated by the support projection. -/
theorem supportProjection_mulVec_eq_zero (W : Matrix (Fin h) (Fin e) ℂ) (x : Fin e → ℂ)
    (hx : W *ᵥ x = 0) : supportProjection W *ᵥ x = 0 := by
  unfold supportProjection
  rw [← mulVec_mulVec, ← mulVec_mulVec, hx, mulVec_zero, mulVec_zero]

/-- `(I - Q_H) x ∈ Ker W` for every `x`. -/
theorem mulVec_one_sub_supportProjection (W : Matrix (Fin h) (Fin e) ℂ) (x : Fin e → ℂ) :
    W *ᵥ ((1 - supportProjection W) *ᵥ x) = 0 := by
  rw [mulVec_mulVec, Matrix.mul_sub, Matrix.mul_one, (supportProjection_props W).2.2, sub_self,
    zero_mulVec]

/-- **Kernel inclusion ⇔ support**: `Ker W ⊆ Ker S` iff `S = S Q_H`. -/
theorem ker_inclusion_iff_supported (W S : Matrix (Fin h) (Fin e) ℂ) :
    (∀ x, W *ᵥ x = 0 → S *ᵥ x = 0) ↔ S * supportProjection W = S := by
  constructor
  · intro hker
    rw [ext_iff_mulVec]
    intro v
    have h0 := hker _ (mulVec_one_sub_supportProjection W v)
    rw [mulVec_mulVec, Matrix.mul_sub, Matrix.mul_one, sub_mulVec, sub_eq_zero] at h0
    exact h0.symm
  · intro hS x hx
    rw [← hS, ← mulVec_mulVec, supportProjection_mulVec_eq_zero W x hx, mulVec_zero]

/-- The occurrence defect `Δ_occ = Re Tr((I - Q_H) G)`. -/
noncomputable def occurrenceDefect (W S : Matrix (Fin h) (Fin e) ℂ) : ℝ :=
  (trace ((1 - supportProjection W) * (Sᴴ * S))).re

/-- Squared Hilbert–Schmidt norm of a rectangular matrix as `Re Tr(M M^*)`. -/
theorem re_trace_mul_conjTranspose_self (M : Matrix (Fin h) (Fin e) ℂ) :
    (trace (M * Mᴴ)).re = ∑ i, ∑ j, ‖M i j‖ ^ 2 := by
  simp only [trace, Matrix.diag, mul_apply, conjTranspose_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

theorem hs_sum_eq_zero_iff (M : Matrix (Fin h) (Fin e) ℂ) :
    (∑ i, ∑ j, ‖M i j‖ ^ 2) = 0 ↔ M = 0 := by
  constructor
  · intro hz
    have hall := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ => sq_nonneg _).mp hz
    ext i j
    have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg _).mp
      (hall i (Finset.mem_univ i)) j (Finset.mem_univ j)
    rw [sq_eq_zero_iff, norm_eq_zero] at this
    simpa using this
  · intro hM
    simp [hM]

/-- `Δ_occ = ‖S (I - Q_H)‖²_HS`. -/
theorem occurrence_defect_eq (W S : Matrix (Fin h) (Fin e) ℂ) :
    occurrenceDefect W S
      = ∑ i, ∑ j, ‖(S * (1 - supportProjection W) : Matrix (Fin h) (Fin e) ℂ) i j‖ ^ 2 := by
  obtain ⟨hQH, hQQ, _⟩ := supportProjection_props W
  have hidem : (1 - supportProjection W) * (1 - supportProjection W)
      = 1 - supportProjection W := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hQQ]
    abel
  have hH : (1 - supportProjection W)ᴴ = 1 - supportProjection W := by
    rw [conjTranspose_sub, conjTranspose_one, hQH]
  unfold occurrenceDefect
  rw [← Matrix.mul_assoc, trace_mul_comm, ← Matrix.mul_assoc]
  have h2 : S * (1 - supportProjection W) * Sᴴ
      = (S * (1 - supportProjection W)) * (S * (1 - supportProjection W))ᴴ := by
    rw [conjTranspose_mul, hH]
    calc S * (1 - supportProjection W) * Sᴴ
        = S * ((1 - supportProjection W) * (1 - supportProjection W)) * Sᴴ := by rw [hidem]
      _ = S * (1 - supportProjection W) * ((1 - supportProjection W) * Sᴴ) := by
          simp only [Matrix.mul_assoc]
  rw [h2, re_trace_mul_conjTranspose_self]

theorem occurrence_defect_nonneg (W S : Matrix (Fin h) (Fin e) ℂ) : 0 ≤ occurrenceDefect W S := by
  rw [occurrence_defect_eq]
  exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _

/-- `Δ_occ = 0` iff `S (I - Q_H) = 0`. -/
theorem occurrence_defect_eq_zero_iff (W S : Matrix (Fin h) (Fin e) ℂ) :
    occurrenceDefect W S = 0 ↔ S * supportProjection W = S := by
  rw [occurrence_defect_eq, hs_sum_eq_zero_iff, Matrix.mul_sub, Matrix.mul_one, sub_eq_zero]
  exact eq_comm

/-- **(NL.1)**: kernel inclusion ⇔ zero occurrence defect ⇔ support condition. -/
theorem word_localizer_descent (W S : Matrix (Fin h) (Fin e) ℂ) :
    ((∀ x, (Wᴴ * W) *ᵥ x = 0 → (Sᴴ * S) *ᵥ x = 0) ↔ occurrenceDefect W S = 0) ∧
      (occurrenceDefect W S = 0 ↔ S * supportProjection W = S) := by
  refine ⟨?_, occurrence_defect_eq_zero_iff W S⟩
  rw [occurrence_defect_eq_zero_iff, ← ker_inclusion_iff_supported]
  constructor
  · intro hk x hx
    exact (mulVec_gram_eq_zero_iff S x).mp (hk x ((mulVec_gram_eq_zero_iff W x).mpr hx))
  · intro hk x hx
    exact (mulVec_gram_eq_zero_iff S x).mpr (hk x ((mulVec_gram_eq_zero_iff W x).mp hx))

/-! ### The whitened localizer (NL.2) -/

/-- The score localizer on the word range, `Λ = W^{†*} G W^{†}` with
`W^† = H^† W^*`. -/
noncomputable def wordLocalizer (W S : Matrix (Fin h) (Fin e) ℂ) : Matrix (Fin h) (Fin h) ℂ :=
  W * sourceGramPseudoinverse W * (Sᴴ * S) * sourceGramPseudoinverse W * Wᴴ

theorem wordLocalizer_posSemidef (W S : Matrix (Fin h) (Fin e) ℂ) :
    (wordLocalizer W S).PosSemidef := by
  have hJ := (sourceGramPseudoinverse_projection W).1
  have : wordLocalizer W S
      = (S * sourceGramPseudoinverse W * Wᴴ)ᴴ * (S * sourceGramPseudoinverse W * Wᴴ) := by
    unfold wordLocalizer
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hJ]
    simp only [Matrix.mul_assoc]
  rw [this]
  exact posSemidef_conjTranspose_mul_self _

/-- The localizer is supported on the word range: `P Λ P = Λ`. -/
theorem wordLocalizer_supported (W S : Matrix (Fin h) (Fin e) ℂ) :
    sourceRangeProjection W * wordLocalizer W S * sourceRangeProjection W = wordLocalizer W S := by
  obtain ⟨_, _, _, hPH, _, hPW⟩ := sourceGramPseudoinverse_projection W
  have hWP : Wᴴ * sourceRangeProjection W = Wᴴ := by
    have := congrArg conjTranspose hPW
    rwa [conjTranspose_mul, hPH] at this
  unfold wordLocalizer
  calc sourceRangeProjection W * (W * sourceGramPseudoinverse W * (Sᴴ * S)
        * sourceGramPseudoinverse W * Wᴴ) * sourceRangeProjection W
      = (sourceRangeProjection W * W) * sourceGramPseudoinverse W * (Sᴴ * S)
        * sourceGramPseudoinverse W * (Wᴴ * sourceRangeProjection W) := by
        simp only [Matrix.mul_assoc]
    _ = W * sourceGramPseudoinverse W * (Sᴴ * S) * sourceGramPseudoinverse W * Wᴴ := by
        rw [hPW, hWP]

/-- `W^* Λ W = Q_H G Q_H`, hence `= G` on the zero branch (**NL.2**). -/
theorem wordLocalizer_represents (W S : Matrix (Fin h) (Fin e) ℂ) :
    Wᴴ * wordLocalizer W S * W = supportProjection W * (Sᴴ * S) * supportProjection W ∧
      (S * supportProjection W = S → Wᴴ * wordLocalizer W S * W = Sᴴ * S) := by
  have hQ : Wᴴ * (W * sourceGramPseudoinverse W) = supportProjection W := by
    rw [supportProjection_comm, Matrix.mul_assoc]
  have hQ' : sourceGramPseudoinverse W * Wᴴ * W = supportProjection W := by
    unfold supportProjection; rw [Matrix.mul_assoc]
  have hrep : Wᴴ * wordLocalizer W S * W
      = supportProjection W * (Sᴴ * S) * supportProjection W := by
    unfold wordLocalizer
    calc Wᴴ * (W * sourceGramPseudoinverse W * (Sᴴ * S) * sourceGramPseudoinverse W * Wᴴ) * W
        = (Wᴴ * (W * sourceGramPseudoinverse W)) * (Sᴴ * S)
          * (sourceGramPseudoinverse W * Wᴴ * W) := by simp only [Matrix.mul_assoc]
      _ = supportProjection W * (Sᴴ * S) * supportProjection W := by rw [hQ, hQ']
  refine ⟨hrep, fun hS => ?_⟩
  rw [hrep]
  have hQH := (supportProjection_props W).1
  have hSQ : supportProjection W * Sᴴ = Sᴴ := by
    have := congrArg conjTranspose hS
    rwa [conjTranspose_mul, hQH] at this
  calc supportProjection W * (Sᴴ * S) * supportProjection W
      = (supportProjection W * Sᴴ) * (S * supportProjection W) := by
        simp only [Matrix.mul_assoc]
    _ = Sᴴ * S := by rw [hSQ, hS]

/-- **Uniqueness**: any operator supported on the word range whose pullback
along `W` is `G` equals `wordLocalizer`. -/
theorem wordLocalizer_unique (W S : Matrix (Fin h) (Fin e) ℂ) (Λ : Matrix (Fin h) (Fin h) ℂ)
    (hsupp : sourceRangeProjection W * Λ * sourceRangeProjection W = Λ)
    (hrep : Wᴴ * Λ * W = Sᴴ * S) :
    Λ = wordLocalizer W S := by
  unfold wordLocalizer
  rw [← hrep]
  calc Λ = sourceRangeProjection W * Λ * sourceRangeProjection W := hsupp.symm
    _ = (W * sourceGramPseudoinverse W * Wᴴ) * Λ * (W * sourceGramPseudoinverse W * Wᴴ) := rfl
    _ = W * sourceGramPseudoinverse W * (Wᴴ * Λ * W) * sourceGramPseudoinverse W * Wᴴ := by
        simp only [Matrix.mul_assoc]

/-! ### Zero word innovation descends the relation (NL.3) -/

/-- On the zero-innovation branch the extension bank is a word relation with
the explicit reduced relation `T = H^† W^* V`. -/
theorem word_relation_descends {e₁ : ℕ} (W : Matrix (Fin h) (Fin e) ℂ)
    (V : Matrix (Fin h) (Fin e₁) ℂ) (hzero : sourceSchurResidual W V = 0) :
    V = W * (sourceGramPseudoinverse W * (Wᴴ * V)) := by
  obtain ⟨T, hT⟩ := (sourceSchurResidual_eq_zero_iff_rangeIncluded W V).mp hzero
  have hWQ := (supportProjection_props W).2.2
  calc V = W * T := hT
    _ = (W * supportProjection W) * T := by rw [hWQ]
    _ = W * (sourceGramPseudoinverse W * (Wᴴ * (W * T))) := by
        unfold supportProjection; simp only [Matrix.mul_assoc]
    _ = W * (sourceGramPseudoinverse W * (Wᴴ * V)) := by rw [← hT]

end WordLocalizerDescent
end NCG
