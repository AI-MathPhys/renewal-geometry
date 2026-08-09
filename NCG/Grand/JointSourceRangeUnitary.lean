import NCG.Grand.JointSourceUniversality

/-! # unique joint-source range unitary -/

open Matrix
open scoped ComplexOrder

namespace NCG

/-- `thm:joint-source-universality`, unique-unitary clause.  Two finite source
factors with the same complete Gram have a unique linear equivalence between
their source ranges; it fixes every source coefficient and preserves the
ambient inner product.  This uniqueness is also the asserted invariance under
Gram-preserving gauges and unread refinements. -/
theorem joint_source_unique_range_unitary
    {h h' e : Type*} [Fintype h] [Fintype h'] [Fintype e]
    (S : Matrix h e ℂ) (T : Matrix h' e ℂ)
    (hGram : Sᴴ * S = Tᴴ * T) :
    ∃! U : LinearMap.range S.mulVecLin ≃ₗ[ℂ]
      LinearMap.range T.mulVecLin,
      (∀ u : e → ℂ,
        U (S.mulVecLin.rangeRestrict u) = T.mulVecLin.rangeRestrict u)
      ∧ (∀ x y : LinearMap.range S.mulVecLin,
        star (x : h → ℂ) ⬝ᵥ (y : h → ℂ)
          = star (U x : h' → ℂ) ⬝ᵥ (U y : h' → ℂ)) := by
  classical
  have hker : LinearMap.ker S.mulVecLin = LinearMap.ker T.mulVecLin := by
    ext u
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply]
    constructor
    · intro hSu
      have hq : star u ⬝ᵥ ((Tᴴ * T) *ᵥ u) = 0 := by
        rw [← hGram, ← gram_realization_inner, hSu]
        simp
      have : star (T *ᵥ u) ⬝ᵥ (T *ᵥ u) = 0 := by
        rw [gram_realization_inner]
        exact hq
      exact dotProduct_star_self_eq_zero.mp this
    · intro hTu
      have hq : star u ⬝ᵥ ((Sᴴ * S) *ᵥ u) = 0 := by
        rw [hGram, ← gram_realization_inner, hTu]
        simp
      have : star (S *ᵥ u) ⬝ᵥ (S *ᵥ u) = 0 := by
        rw [gram_realization_inner]
        exact hq
      exact dotProduct_star_self_eq_zero.mp this
  let U : LinearMap.range S.mulVecLin ≃ₗ[ℂ]
      LinearMap.range T.mulVecLin :=
    S.mulVecLin.quotKerEquivRange.symm ≪≫ₗ
      Submodule.quotEquivOfEq (LinearMap.ker S.mulVecLin)
        (LinearMap.ker T.mulVecLin) hker ≪≫ₗ
        T.mulVecLin.quotKerEquivRange
  have hU : ∀ u : e → ℂ,
      U (S.mulVecLin.rangeRestrict u) = T.mulVecLin.rangeRestrict u := by
    intro u
    let su : LinearMap.range S.mulVecLin :=
      ⟨S.mulVecLin u, ⟨u, rfl⟩⟩
    have hrs : S.mulVecLin.rangeRestrict u = su := by
      apply Subtype.ext
      rfl
    apply Subtype.ext
    rw [hrs]
    change ((U su :
      LinearMap.range T.mulVecLin) : h' → ℂ) = T.mulVecLin u
    have hsu : S.mulVecLin.quotKerEquivRange.symm su
        = (LinearMap.ker S.mulVecLin).mkQ u := by
      have h := S.mulVecLin.quotKerEquivRange_symm_apply_image u su.property
      convert h using 1
    simp only [U, LinearEquiv.trans_apply]
    rw [hsu]
    simp only [Submodule.mkQ_apply]
    rw [Submodule.quotEquivOfEq_mk,
      LinearMap.quotKerEquivRange_apply_mk]
  have hinner : ∀ x y : LinearMap.range S.mulVecLin,
      star (x : h → ℂ) ⬝ᵥ (y : h → ℂ)
        = star (U x : h' → ℂ) ⬝ᵥ (U y : h' → ℂ) := by
    rintro ⟨_, ⟨u, rfl⟩⟩ ⟨_, ⟨v, rfl⟩⟩
    change star (S *ᵥ u) ⬝ᵥ (S *ᵥ v)
      = star (U (S.mulVecLin.rangeRestrict u) : h' → ℂ)
        ⬝ᵥ (U (S.mulVecLin.rangeRestrict v) : h' → ℂ)
    rw [hU u, hU v]
    change star (S *ᵥ u) ⬝ᵥ (S *ᵥ v)
      = star (T *ᵥ u) ⬝ᵥ (T *ᵥ v)
    rw [gram_realization_inner, gram_realization_inner, hGram]
  refine ⟨U, ⟨hU, hinner⟩, ?_⟩
  intro V hV
  apply LinearEquiv.ext
  rintro ⟨_, ⟨u, rfl⟩⟩
  change V (S.mulVecLin.rangeRestrict u) =
    U (S.mulVecLin.rangeRestrict u)
  rw [hV.1 u, hU u]

end NCG
