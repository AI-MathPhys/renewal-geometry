/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GramSqrtPinvExact
import NCG.Grand.SourceTerminalNonduplicationExact

/-!
# Source-minimal one-letter word/action extension

Machinery for `thm:GT-word-localizer-extension`.  `W : E →L[ℝ] K` synthesises the retained
words, `V : F →L[ℝ] K` the proposed one-letter extensions, and `L` is a positive localizer on
the common carrier `K`.  With `H = W†W`, `C = W†V`, `D = V†V`, `G = W†LW`, `J = W†LV`,
`Kₗ = V†LV`, `T = H†C`, `P_W = W H† W†` and `N = (I - P_W) V`:

* (NL.4a) `R_w = D - C† H† C = N†N ⪰ 0` (`wordGram_eq`, `wordGram_isPositive`);
* (NL.4b) `rank R_w + dim ran W = dim ran (W, V)` (`finrank_wordGram_add`);
* (NL.4c) the polar synthesis `𝒥_w = N R_w^{†/2}` is a partial isometry with initial space
  `ran R_w` and final space `ran N`, realises `N = 𝒥_w R_w^{1/2}`, and is the unique such factor
  vanishing on `ker N` (`polar_*`);
* (NL.4d)–(NL.4g) in the orthogonal frame `(W H^{†/2}, 𝒥_w)` the localizer is represented by the
  positive block operator with `A = H^{†/2} G H^{†/2}`, `B = H^{†/2}(J - GT) R_w^{†/2}`,
  `D_n = R_w^{†/2}(Kₗ - T†J - J†T + T†GT) R_w^{†/2}` (`blockA_eq`, `blockB_eq`, `blockD_eq`,
  `block_quadratic`, `block_nonneg`).
-/

open ContinuousLinearMap Submodule Module NCG.MoorePenrose NCG.GramSqrt
open scoped RealInnerProductSpace InnerProduct

namespace NCG
namespace WordLocalizer

variable {E F K : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [CompleteSpace F] [NormedAddCommGroup K] [InnerProductSpace ℝ K] [FiniteDimensional ℝ K]
  [CompleteSpace K]

variable (W : E →L[ℝ] K) (V : F →L[ℝ] K) (L : K →L[ℝ] K)

/-! ### Words, transfer and the new-word residual -/

/-- `T = H† C`. -/
noncomputable def transfer : F →L[ℝ] E := gramPinv W ∘L crossGram W V

/-- `P_W = W H† W†`. -/
noncomputable def projW : K →L[ℝ] K := W ∘L gramPinv W ∘L W†

/-- `P_W` is the orthogonal projection onto `ran W`. -/
theorem projW_eq : projW W = (LinearMap.range W.toLinearMap).starProjection :=
  ContinuousLinearMap.ext fun y => comp_gramPinv_comp_adjoint W y

/-- `N = (I - P_W) V`. -/
noncomputable def newWord : F →L[ℝ] K := residual W V

omit [FiniteDimensional ℝ F] [CompleteSpace F] [FiniteDimensional ℝ K] in
/-- `W T = P_W V`. -/
theorem comp_transfer : W ∘L transfer W V = projW W ∘L V :=
  ContinuousLinearMap.ext fun _ => rfl

omit [FiniteDimensional ℝ F] [CompleteSpace F] in
/-- `N = V - W T`. -/
theorem newWord_eq : newWord W V = V - W ∘L transfer W V := by
  refine ContinuousLinearMap.ext fun x => ?_
  rw [newWord, residual_apply, sub_apply, comp_transfer, comp_apply, projW_eq]

omit [FiniteDimensional ℝ F] [CompleteSpace F] [FiniteDimensional ℝ K] in
/-- `W† N = 0`. -/
theorem adjoint_comp_newWord : W† ∘L newWord W V = 0 := by
  refine ContinuousLinearMap.ext fun x => ?_
  refine ext_inner_right ℝ fun y => ?_
  rw [comp_apply, adjoint_inner_left, zero_apply, inner_zero_left]
  exact residual_inner_eq_zero W V x y

/-! ### (NL.4a): the new word Gram -/

/-- The new word Gram `R_w = D - C† H† C`. -/
noncomputable def wordGram : F →L[ℝ] F :=
  gram V - (crossGram W V)† ∘L gramPinv W ∘L crossGram W V

omit [FiniteDimensional ℝ F] in
/-- **(NL.4a)**: `R_w = N† N`. -/
theorem wordGram_eq : wordGram W V = gram (newWord W V) :=
  (SourceTerminal.fresh_gram W V).symm

omit [FiniteDimensional ℝ F] in
theorem wordGram_isPositive : (wordGram W V).IsPositive := by
  rw [wordGram_eq]
  exact gram_isPositive _

omit [FiniteDimensional ℝ F] in
theorem gramRange_newWord :
    gramRange (newWord W V) = LinearMap.range (wordGram W V).toLinearMap := by
  rw [gramRange, wordGram_eq]

omit [FiniteDimensional ℝ F] [CompleteSpace F] in
theorem starProjection_congr {K₁ K₂ : Submodule ℝ F} [K₁.HasOrthogonalProjection]
    [K₂.HasOrthogonalProjection] (h : K₁ = K₂) : K₁.starProjection = K₂.starProjection := by
  subst h
  rfl

theorem starProjection_gramRange_newWord :
    (gramRange (newWord W V)).starProjection
      = (LinearMap.range (wordGram W V).toLinearMap).starProjection :=
  starProjection_congr (gramRange_newWord W V)

/-! ### (NL.4b): rank -/

omit [FiniteDimensional ℝ F] [CompleteSpace F] in
/-- `ran (W, V) = ran W ⊕ ran N`. -/
theorem range_sup_eq :
    LinearMap.range W.toLinearMap ⊔ LinearMap.range V.toLinearMap
      = LinearMap.range W.toLinearMap ⊔ LinearMap.range (newWord W V).toLinearMap := by
  refine le_antisymm (sup_le le_sup_left ?_) (sup_le le_sup_left ?_)
  · rintro _ ⟨x, rfl⟩
    have h : V x = W (transfer W V x) + newWord W V x := by
      rw [newWord_eq, sub_apply, comp_apply]
      abel
    change V x ∈ _
    rw [h]
    exact Submodule.add_mem _ (Submodule.mem_sup_left ⟨_, rfl⟩)
      (Submodule.mem_sup_right ⟨_, rfl⟩)
  · rintro _ ⟨x, rfl⟩
    change newWord W V x ∈ _
    rw [newWord, residual_apply]
    exact Submodule.sub_mem _ (Submodule.mem_sup_right ⟨_, rfl⟩)
      (Submodule.mem_sup_left ((LinearMap.range W.toLinearMap).starProjection_apply_mem _))

omit [CompleteSpace E] [FiniteDimensional ℝ F] [CompleteSpace F] [FiniteDimensional ℝ K]
  [CompleteSpace K] in
theorem range_newWord_le_orthogonal :
    LinearMap.range (newWord W V).toLinearMap ≤ (LinearMap.range W.toLinearMap)ᗮ := by
  rintro _ ⟨x, rfl⟩
  rw [Submodule.mem_orthogonal]
  rintro _ ⟨y, rfl⟩
  rw [real_inner_comm]
  exact residual_inner_eq_zero W V x y

/-- **(NL.4b)**: `rank R_w + dim ran W = dim ran (W, V)`. -/
theorem finrank_wordGram_add :
    finrank ℝ (LinearMap.range (wordGram W V).toLinearMap)
        + finrank ℝ (LinearMap.range W.toLinearMap)
      = finrank ℝ ↥(LinearMap.range W.toLinearMap ⊔ LinearMap.range V.toLinearMap) := by
  rw [wordGram_eq, finrank_range_gram, range_sup_eq]
  have h := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range W.toLinearMap)
    (LinearMap.range (newWord W V).toLinearMap)
  have hinf : LinearMap.range W.toLinearMap ⊓ LinearMap.range (newWord W V).toLinearMap = ⊥ := by
    refine le_antisymm ?_ bot_le
    refine le_trans (inf_le_inf_left _ (range_newWord_le_orthogonal W V)) ?_
    rw [Submodule.inf_orthogonal_eq_bot]
  rw [hinf, finrank_bot, add_zero] at h
  omega

/-! ### (NL.4c): the polar synthesis -/

/-- `R_w^{†/2}`. -/
noncomputable def wordHalfPinv : F →L[ℝ] F := sqrtPinv (newWord W V)

/-- `R_w^{1/2}`. -/
noncomputable def wordHalf : F →L[ℝ] F := sqrtGram (newWord W V)

/-- The polar synthesis `𝒥_w = N R_w^{†/2}`. -/
noncomputable def polar : F →L[ℝ] K := frame (newWord W V)

omit [CompleteSpace E] [FiniteDimensional ℝ K] in
theorem polar_eq : polar W V = newWord W V ∘L wordHalfPinv W V := rfl

omit [CompleteSpace E] [FiniteDimensional ℝ K] in
theorem wordHalfPinv_mul_self : wordHalfPinv W V ∘L wordHalfPinv W V = gramPinv (newWord W V) :=
  sqrtPinv_mul_self _

theorem wordHalf_mul_self : wordHalf W V ∘L wordHalf W V = wordGram W V := by
  rw [wordGram_eq]; exact sqrtGram_mul_self _

/-- `R_w†` is the Moore–Penrose inverse of `R_w`. -/
theorem isMoorePenrose_wordGram : IsMoorePenrose (wordGram W V) (gramPinv (newWord W V)) := by
  rw [wordGram_eq]; exact isMoorePenrose_gramPinv _

/-- `𝒥_w† 𝒥_w = P_{ran R_w}`: the polar synthesis is a partial isometry with initial space
`ran R_w`. -/
theorem adjoint_polar_comp_polar :
    (polar W V)† ∘L polar W V = (LinearMap.range (wordGram W V).toLinearMap).starProjection := by
  rw [← starProjection_gramRange_newWord]; exact adjoint_frame_comp_frame _

omit [CompleteSpace E] [FiniteDimensional ℝ K] in
/-- The polar synthesis maps onto the new-word range `ran N`. -/
theorem range_polar :
    LinearMap.range (polar W V).toLinearMap = LinearMap.range (newWord W V).toLinearMap :=
  range_frame _

omit [CompleteSpace E] [FiniteDimensional ℝ K] in
/-- Polar decomposition `N = 𝒥_w R_w^{1/2}`. -/
theorem polar_comp_wordHalf : polar W V ∘L wordHalf W V = newWord W V :=
  frame_comp_sqrtGram _

/-- Uniqueness: any `U` with `U R_w^{1/2} = N` vanishing on `(ran R_w)ᗮ = ker N` is `𝒥_w`. -/
theorem polar_unique {U : F →L[ℝ] K} (hU : U ∘L wordHalf W V = newWord W V)
    (hP : U ∘L (LinearMap.range (wordGram W V).toLinearMap).starProjection = U) :
    U = polar W V := by
  rw [← starProjection_gramRange_newWord] at hP
  exact frame_unique _ hU hP

/-! ### (NL.4d)–(NL.4g): the enlarged localizer -/

/-- The old supported isometry `W H^{†/2}`. -/
noncomputable def oldFrame : E →L[ℝ] K := frame W

/-- `H^{†/2}`. -/
noncomputable def oldHalfPinv : E →L[ℝ] E := sqrtPinv W

/-- `G = W† L W`. -/
noncomputable def actG : E →L[ℝ] E := W† ∘L L ∘L W

/-- `J = W† L V`. -/
noncomputable def actJ : F →L[ℝ] E := W† ∘L L ∘L V

/-- `Kₗ = V† L V`. -/
noncomputable def actK : F →L[ℝ] F := V† ∘L L ∘L V

/-- (NL.4e) `A = H^{†/2} G H^{†/2}`. -/
noncomputable def blockA : E →L[ℝ] E := oldHalfPinv W ∘L actG W L ∘L oldHalfPinv W

/-- (NL.4f) `B = H^{†/2} (J - G T) R_w^{†/2}`. -/
noncomputable def blockB : F →L[ℝ] E :=
  oldHalfPinv W ∘L (actJ W V L - actG W L ∘L transfer W V) ∘L wordHalfPinv W V

/-- (NL.4g) `D_n = R_w^{†/2} (Kₗ - T†J - J†T + T†GT) R_w^{†/2}`. -/
noncomputable def blockD : F →L[ℝ] F :=
  wordHalfPinv W V ∘L (actK V L - (transfer W V)† ∘L actJ W V L - (actJ W V L)† ∘L transfer W V
    + (transfer W V)† ∘L actG W L ∘L transfer W V) ∘L wordHalfPinv W V

omit [FiniteDimensional ℝ K] in
/-- `(W H^{†/2})† (W H^{†/2}) = P_{ran H}`. -/
theorem adjoint_oldFrame_comp_oldFrame :
    (oldFrame W)† ∘L oldFrame W = (gramRange W).starProjection :=
  adjoint_frame_comp_frame W

omit [FiniteDimensional ℝ K] in
theorem range_oldFrame :
    LinearMap.range (oldFrame W).toLinearMap = LinearMap.range W.toLinearMap :=
  range_frame W

omit [FiniteDimensional ℝ K] in
/-- The old and new frames have orthogonal ranges. -/
theorem adjoint_oldFrame_comp_polar : (oldFrame W)† ∘L polar W V = 0 := by
  have h := adjoint_comp_newWord W V
  refine ContinuousLinearMap.ext fun x => ?_
  simp only [oldFrame, frame, polar, comp_apply, adjoint_comp, zero_apply,
    isSelfAdjoint_iff'.mp (isSelfAdjoint_sqrtPinv W)]
  have hx := congrArg (fun T : F →L[ℝ] E => T (sqrtPinv (newWord W V) x)) h
  simp only [comp_apply, zero_apply] at hx
  rw [hx, map_zero]

omit [FiniteDimensional ℝ K] in
/-- **(NL.4e)**: `(W H^{†/2})† L (W H^{†/2}) = H^{†/2} G H^{†/2}`. -/
theorem blockA_eq : (oldFrame W)† ∘L L ∘L oldFrame W = blockA W L := by
  refine ContinuousLinearMap.ext fun x => ?_
  simp only [oldFrame, frame, blockA, oldHalfPinv, actG, comp_apply, adjoint_comp,
    isSelfAdjoint_iff'.mp (isSelfAdjoint_sqrtPinv W)]

omit [FiniteDimensional ℝ F] [CompleteSpace F] in
/-- `W† L N = J - G T`. -/
theorem adjoint_comp_L_comp_newWord :
    W† ∘L L ∘L newWord W V = actJ W V L - actG W L ∘L transfer W V := by
  rw [newWord_eq, comp_sub, comp_sub]
  rfl

/-- **(NL.4f)**: `(W H^{†/2})† L 𝒥_w = H^{†/2} (J - G T) R_w^{†/2}`. -/
theorem blockB_eq : (oldFrame W)† ∘L L ∘L polar W V = blockB W V L := by
  rw [blockB, ← adjoint_comp_L_comp_newWord]
  refine ContinuousLinearMap.ext fun x => ?_
  simp only [oldFrame, frame, polar, oldHalfPinv, wordHalfPinv, comp_apply, adjoint_comp,
    isSelfAdjoint_iff'.mp (isSelfAdjoint_sqrtPinv W)]

omit [FiniteDimensional ℝ F] in
/-- `N† L N = Kₗ - T†J - J†T + T†GT` for self-adjoint `L`. -/
theorem adjoint_newWord_comp_L_comp_newWord (hL : IsSelfAdjoint L) :
    (newWord W V)† ∘L L ∘L newWord W V
      = actK V L - (transfer W V)† ∘L actJ W V L - (actJ W V L)† ∘L transfer W V
        + (transfer W V)† ∘L actG W L ∘L transfer W V := by
  have hL' : L† = L := isSelfAdjoint_iff'.mp hL
  rw [newWord_eq]
  refine ContinuousLinearMap.ext fun x => ?_
  simp only [actK, actJ, actG, comp_apply, sub_apply, add_apply, map_sub, adjoint_comp, hL',
    adjoint_adjoint]
  abel

/-- **(NL.4g)**: `𝒥_w† L 𝒥_w = R_w^{†/2} (Kₗ - T†J - J†T + T†GT) R_w^{†/2}`. -/
theorem blockD_eq (hL : IsSelfAdjoint L) : (polar W V)† ∘L L ∘L polar W V = blockD W V L := by
  rw [blockD, ← adjoint_newWord_comp_L_comp_newWord W V L hL]
  refine ContinuousLinearMap.ext fun x => ?_
  simp only [polar, frame, wordHalfPinv, comp_apply, adjoint_comp,
    isSelfAdjoint_iff'.mp (isSelfAdjoint_sqrtPinv (newWord W V))]

/-- **(NL.4d)**: the block operator `Λ⁺ = [[A, B], [B†, D_n]]` is the compression of `L` to the
orthogonal frame `(W H^{†/2}, 𝒥_w)`: its quadratic form on `(x, y)` is `⟨L z, z⟩` with
`z = W H^{†/2} x + 𝒥_w y`. -/
theorem block_quadratic (hL : IsSelfAdjoint L) (x : E) (y : F) :
    ⟪blockA W L x, x⟫ + 2 * ⟪blockB W V L y, x⟫ + ⟪blockD W V L y, y⟫
      = ⟪L (oldFrame W x + polar W V y), oldFrame W x + polar W V y⟫ := by
  rw [← blockA_eq, ← blockB_eq, ← blockD_eq W V L hL]
  simp only [comp_apply, adjoint_inner_left]
  have hL' : L† = L := isSelfAdjoint_iff'.mp hL
  have hsym : ⟪L (polar W V y), oldFrame W x⟫ = ⟪L (oldFrame W x), polar W V y⟫ := by
    rw [← adjoint_inner_right, hL', real_inner_comm]
  rw [map_add, inner_add_left, inner_add_right, inner_add_right, hsym]
  ring

/-- `Λ⁺ ⪰ 0` for a positive localizer. -/
theorem block_nonneg (hL : L.IsPositive) (x : E) (y : F) :
    0 ≤ ⟪blockA W L x, x⟫ + 2 * ⟪blockB W V L y, x⟫ + ⟪blockD W V L y, y⟫ := by
  rw [block_quadratic W V L hL.isSelfAdjoint]
  have := hL.2 (oldFrame W x + polar W V y)
  rwa [reApplyInnerSelf_apply, RCLike.re_to_real] at this

/-- **`thm:GT-word-localizer-extension`**: (NL.4a) the new word Gram is the positive Gram of the
residual `N`; (NL.4b) its rank counts the new directions; (NL.4c) the polar synthesis is the
unique partial isometry onto `ran N` factoring `N`; (NL.4d)–(NL.4g) the localizer compressed to
the orthogonal frame `(W H^{†/2}, 𝒥_w)` is the positive block operator with the displayed
blocks. -/
theorem word_localizer_extension (hL : L.IsPositive) :
    wordGram W V = gram (newWord W V) ∧ (wordGram W V).IsPositive ∧
      finrank ℝ (LinearMap.range (wordGram W V).toLinearMap)
          + finrank ℝ (LinearMap.range W.toLinearMap)
        = finrank ℝ ↥(LinearMap.range W.toLinearMap ⊔ LinearMap.range V.toLinearMap) ∧
      (polar W V)† ∘L polar W V
        = (LinearMap.range (wordGram W V).toLinearMap).starProjection ∧
      LinearMap.range (polar W V).toLinearMap = LinearMap.range (newWord W V).toLinearMap ∧
      polar W V ∘L wordHalf W V = newWord W V ∧
      (∀ U : F →L[ℝ] K, U ∘L wordHalf W V = newWord W V →
        U ∘L (LinearMap.range (wordGram W V).toLinearMap).starProjection = U → U = polar W V) ∧
      (oldFrame W)† ∘L oldFrame W = (gramRange W).starProjection ∧
      LinearMap.range (oldFrame W).toLinearMap = LinearMap.range W.toLinearMap ∧
      (oldFrame W)† ∘L polar W V = 0 ∧
      (oldFrame W)† ∘L L ∘L oldFrame W = blockA W L ∧
      (oldFrame W)† ∘L L ∘L polar W V = blockB W V L ∧
      (polar W V)† ∘L L ∘L polar W V = blockD W V L ∧
      ∀ (x : E) (y : F),
        ⟪blockA W L x, x⟫ + 2 * ⟪blockB W V L y, x⟫ + ⟪blockD W V L y, y⟫
            = ⟪L (oldFrame W x + polar W V y), oldFrame W x + polar W V y⟫ ∧
          0 ≤ ⟪blockA W L x, x⟫ + 2 * ⟪blockB W V L y, x⟫ + ⟪blockD W V L y, y⟫ :=
  ⟨wordGram_eq W V, wordGram_isPositive W V, finrank_wordGram_add W V,
    adjoint_polar_comp_polar W V, range_polar W V, polar_comp_wordHalf W V,
    fun _ hU hP => polar_unique W V hU hP, adjoint_oldFrame_comp_oldFrame W, range_oldFrame W,
    adjoint_oldFrame_comp_polar W V, blockA_eq W L, blockB_eq W V L,
    blockD_eq W V L hL.isSelfAdjoint, fun x y =>
      ⟨block_quadratic W V L hL.isSelfAdjoint x y, block_nonneg W V L hL x y⟩⟩

end WordLocalizer
end NCG
