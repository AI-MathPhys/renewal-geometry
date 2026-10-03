/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.StandardModel.FiniteInternalLandingExact
import RenewalGeometry.StandardModel.InternalSeedSaturationWords
import RenewalGeometry.StandardModel.LabelledCensusExact

/-!
# The finite internal landing alternative for actual represented words
  (`thm:finite-internal-landing-alternative`)

`FiniteInternalLandingExact.lean` proves (A1)–(A3) and the dimension table; its (A4) was
stated on the census-carrier model generators only.  Here (A4) is proved **for actual
represented words** `x : β → 𝒜'_tet,r`, by instantiating `thm:internal-seed-saturation`
(`InternalSeedWords.internal_seed_saturation_words`):

* the complete census is the labelled five-entry census `(3, 0, 2, 1, 1)` of
  `eq:SM-complete-census` (`LabelledCensus.labelledCensus`, injective sector labels), with
  the sectors identified with the blocks by the assignment (`lab = place ∘ e`), from which
  the block multiplicities `(3, 2, 1, 1)` follow (`card_of_labelledCensus`);
* a positive colour residual: some word has `δ_col = ω_col > 0`;
* a positive weak-router residual: two represented rank-one projections `p_t, p_h` of the
  weak plane with `δ_wk = ‖[p_t, p_h]‖²_HS > 0` (which forces them distinct and
  non-orthogonal, `ne_and_overlap_ne_of_weakResidual7_pos`);
* central separation of the two scalar characters.

`finite_internal_landing_alternative_words` assembles (A1)–(A3), the new (A4) and the
dimension table.
-/

open Matrix Module
open RenewalGeometry.InternalAssembly (blockAlgebra)

namespace RenewalGeometry
namespace FiniteLandingWords

open InternalSeedWords InternalSeedSaturation LabelledCensus

/-- The weak-router residual `δ_wk(p_t, p_h) = ‖[p_t, p_h]‖²_HS` on the census carrier. -/
noncomputable def weakResidual7 (t h : Fin 7 → ℂ) : ℝ :=
  BridgeRouter.frobSq (rk1 t * rk1 h - rk1 h * rk1 t)

/-- A positive weak-router residual forces distinct, non-orthogonal projections. -/
theorem ne_and_overlap_ne_of_weakResidual7_pos {t h : Fin 7 → ℂ}
    (hpos : 0 < weakResidual7 t h) : rk1 t ≠ rk1 h ∧ star t ⬝ᵥ h ≠ 0 := by
  constructor
  · intro heq
    rw [weakResidual7, heq, sub_self, frobSq_zero] at hpos
    exact lt_irrefl _ hpos
  · intro h0
    have h0' : star h ⬝ᵥ t = 0 := by rw [star_dotProduct, h0, star_zero]
    rw [weakResidual7, rk1, rk1, vecMulVec_star_mul, vecMulVec_star_mul, h0, h0', zero_smul,
      zero_smul, sub_zero, frobSq_zero] at hpos
    exact lt_irrefl _ hpos

variable {ι : Type} [Fintype ι] [DecidableEq ι] {J : ι → Type} [∀ b, Fintype (J b)]
  [∀ b, DecidableEq (J b)]

/-- The block multiplicities `(3, 2, 1, 1)` from the labelled census `(3, 0, 2, 1, 1)` and an
assignment-compatible identification of the sectors with the blocks. -/
theorem card_of_labelledCensus {lab : ι → Fin 5} (hlab : Function.Injective lab)
    (hcen : labelledCensus lab J = smCensus) (e : ι ≃ Fin 4) (hle : ∀ b, lab b = place (e b))
    (k : Fin 4) : Fintype.card (J (e.symm k)) = ![3, 2, 1, 1] k := by
  rw [← labelledCensus_lab hlab, hcen, hle, e.apply_symm_apply, smCensus_place]

variable {n : Type} [Fintype n] [DecidableEq n] {G : Type} [Group G] {I : ι → Type}
  [∀ b, Fintype (I b)] [∀ b, DecidableEq (I b)]

/-- **(A4) for actual represented words.**  At the complete census `(3, 0, 2, 1, 1)`
(labelled, with the assignment of colour/weak/scalar blocks), if a represented word has a
positive colour residual relative to the coherent realisation `T ⊕ H_priv` whose private
algebra `M₂(H_priv)` is represented, two represented weak rank-one projections have a
positive router residual, and the two scalar characters are centrally separated, then the
represented internal word algebra `C^*(x_j)` equals the full relative commutant
`𝒜'_tet,r ≅ M₃ ⊕ M₂ ⊕ ℂ ⊕ ℂ` (dimension `15`). -/
theorem landing_saturation_words (ρ : G →* Matrix n n ℂ)
    (W : Matrix n (Σ b, I b × J b) ℂ) (hW1 : Wᴴ * W = 1) (hW2 : W * Wᴴ = 1)
    (hNI : ∀ b, Nonempty (I b))
    (hM : (fun x => Wᴴ * x * W) ''
      matCommutant (Algebra.adjoin ℂ (Set.range ρ) : Set (Matrix n n ℂ)) = multBlockSet I J)
    {lab : ι → Fin 5} (hlab : Function.Injective lab) (hcen : labelledCensus lab J = smCensus)
    (e : ι ≃ Fin 4) (hle : ∀ b, lab b = place (e b))
    {β : Type} [Fintype β] (x : β → Matrix n n ℂ) (hx : ∀ j, x j ∈ extCommutant ρ)
    {τ : Fin 7 → ℂ} (hτ : BlockSupported 0 τ) (hτu : IsUnitVec τ)
    (hpriv : ∀ X : Matrix (Fin 7) (Fin 7) ℂ, pHpriv τ * X * pHpriv τ ∈
      coordAlgebra ρ W hW1 hW2 hNI hM e (card_of_labelledCensus hlab hcen e hle) x hx)
    (hcol : ∃ j, 0 < omegaCol τ
      (wordCoords ρ W hW1 hW2 hNI hM e (card_of_labelledCensus hlab hcen e hle) x hx j))
    {t h : Fin 7 → ℂ} (ht : BlockSupported 1 t) (hh : BlockSupported 1 h)
    (htu : IsUnitVec t) (hhu : IsUnitVec h)
    (hPt : rk1 t ∈ coordAlgebra ρ W hW1 hW2 hNI hM e (card_of_labelledCensus hlab hcen e hle) x hx)
    (hPh : rk1 h ∈ coordAlgebra ρ W hW1 hW2 hNI hM e (card_of_labelledCensus hlab hcen e hle) x hx)
    (hwk : 0 < weakResidual7 t h)
    (hsep : (Matrix.single 5 5 1 ∈
          coordAlgebra ρ W hW1 hW2 hNI hM e (card_of_labelledCensus hlab hcen e hle) x hx ∧
        Matrix.single 6 6 1 ∈
          coordAlgebra ρ W hW1 hW2 hNI hM e (card_of_labelledCensus hlab hcen e hle) x hx) ∨
      0 < CentralSeparation.etaCen
        (wordCoords ρ W hW1 hW2 hNI hM e (card_of_labelledCensus hlab hcen e hle) x hx)) :
    starAdjoin (Set.range x) = extCommutant ρ ∧
      Nonempty (blockAlgebra ≃ₐ[ℂ] extCommutant ρ) ∧ finrank ℂ (extCommutant ρ) = 15 := by
  obtain ⟨hne, hov⟩ := ne_and_overlap_ne_of_weakResidual7_pos hwk
  obtain ⟨hsat, -, h15, -⟩ := internal_seed_saturation_words ρ W hW1 hW2 hNI hM e
    (card_of_labelledCensus hlab hcen e hle) x hx hτ hτu hpriv (Or.inl hcol) ht hh htu hhu
    hPt hPh hne hov hsep
  exact ⟨hsat, ⟨censusCommutantEquiv ρ W hW1 hW2 hNI hM e
    (card_of_labelledCensus hlab hcen e hle)⟩, h15⟩

/-- **`thm:finite-internal-landing-alternative`** with (A4) for actual represented words:
(A1) flat obstruction, (A2) reducible colour block at zero bridge residual, (A3) commutative
weak algebra at zero router residual (from `FiniteInternalLandingExact`), (A4)
`landing_saturation_words`, the dimension table `9 / 11 / 13 / 15` of
`thm:internal-deficit-alternatives`, and the `14`-dimensional scalar-locked terminal branch
without central separation (`ColourBridgeComplete`-independent form:
`CentralSeparation.finrank_lockedAlgebra`). -/
theorem finite_internal_landing_alternative_words :
    -- (A1)–(A3) and the dimension table
    ((∀ {E : Type} [AddCommGroup E] [Module ℂ E] {ι G : Type} {W : Type} [AddCommGroup W]
      [Module ℂ W] [FiniteDimensional ℂ E] [FiniteDimensional ℂ W]
      (L : ι → E →ₗ[ℂ] E) (V0 : Submodule ℂ E) (ρ : G → E →ₗ[ℂ] E) (σ : G → W →ₗ[ℂ] W) (r : ℕ),
      Module.finrank ℂ (wordSpan L V0 (r + 1)) ≤ Module.finrank ℂ (wordSpan L V0 r) →
      FlatMultiplicity.mult L V0 ρ σ r < 3 →
      ∀ s, ∀ f : Matrix (Fin 3) (Fin 3) ℂ →ₗ[ℂ] FlatMultiplicity.lambdaBlock L V0 ρ σ s,
        ¬ Function.Injective f) ∧
    (∀ U : Set (Matrix (Fin 3) (Fin 3) ℂ), (∀ u ∈ U, BridgeRouter.colourResidual u = 0) →
      Algebra.adjoin ℂ (FiniteLanding.bridgeFamilyGens U) = InternalSeed.blockDiag) ∧
    (∀ T : Set (Fin 2 → ℂ), (∀ t ∈ T, ∀ h ∈ T, BridgeRouter.weakResidual t h = 0) →
      ∀ x ∈ Algebra.adjoin ℂ (BridgeRouter.proj '' T),
        ∀ y ∈ Algebra.adjoin ℂ (BridgeRouter.proj '' T), x * y = y * x)) ∧
    -- (A4) for actual words (see `landing_saturation_words`)
    (∀ {n : Type} [Fintype n] [DecidableEq n] {G : Type} [Group G]
      {ι : Type} [Fintype ι] [DecidableEq ι] {I J : ι → Type}
      [∀ b, Fintype (I b)] [∀ b, DecidableEq (I b)] [∀ b, Fintype (J b)] [∀ b, DecidableEq (J b)]
      (ρ : G →* Matrix n n ℂ) (W : Matrix n (Σ b, I b × J b) ℂ) (hW1 : Wᴴ * W = 1)
      (hW2 : W * Wᴴ = 1) (hNI : ∀ b, Nonempty (I b))
      (hM : (fun x => Wᴴ * x * W) ''
        matCommutant (Algebra.adjoin ℂ (Set.range ρ) : Set (Matrix n n ℂ)) = multBlockSet I J)
      {lab : ι → Fin 5} (hlab : Function.Injective lab)
      (hcen : labelledCensus lab J = smCensus) (e : ι ≃ Fin 4) (hle : ∀ b, lab b = place (e b))
      {β : Type} [Fintype β] (x : β → Matrix n n ℂ) (hx : ∀ j, x j ∈ extCommutant ρ)
      {τ : Fin 7 → ℂ}, BlockSupported 0 τ → IsUnitVec τ →
      (∀ X : Matrix (Fin 7) (Fin 7) ℂ, pHpriv τ * X * pHpriv τ ∈
        coordAlgebra ρ W hW1 hW2 hNI hM e (card_of_labelledCensus hlab hcen e hle) x hx) →
      (∃ j, 0 < omegaCol τ
        (wordCoords ρ W hW1 hW2 hNI hM e (card_of_labelledCensus hlab hcen e hle) x hx j)) →
      ∀ {t h : Fin 7 → ℂ}, BlockSupported 1 t → BlockSupported 1 h → IsUnitVec t →
      IsUnitVec h →
      rk1 t ∈ coordAlgebra ρ W hW1 hW2 hNI hM e (card_of_labelledCensus hlab hcen e hle) x hx →
      rk1 h ∈ coordAlgebra ρ W hW1 hW2 hNI hM e (card_of_labelledCensus hlab hcen e hle) x hx →
      0 < weakResidual7 t h →
      ((Matrix.single 5 5 1 ∈
            coordAlgebra ρ W hW1 hW2 hNI hM e (card_of_labelledCensus hlab hcen e hle) x hx ∧
          Matrix.single 6 6 1 ∈
            coordAlgebra ρ W hW1 hW2 hNI hM e (card_of_labelledCensus hlab hcen e hle) x hx) ∨
        0 < CentralSeparation.etaCen
          (wordCoords ρ W hW1 hW2 hNI hM e (card_of_labelledCensus hlab hcen e hle) x hx)) →
      starAdjoin (Set.range x) = extCommutant ρ ∧
        Nonempty (blockAlgebra ≃ₐ[ℂ] extCommutant ρ) ∧ finrank ℂ (extCommutant ρ) = 15) ∧
    -- the dimension table and the scalar-locked terminal branch
    (∀ (u : Matrix (Fin 7) (Fin 7) ℂ) (h : Fin 7 → ℂ), InternalAssembly.ColourSupported u →
      (InternalAssembly.omega7 u = 0 →
        Module.finrank ℂ (Algebra.adjoin ℂ (InternalDeficit.baseGens ∪
          InternalDeficit.bridgeGens u)) = 9) ∧
      (InternalAssembly.omega7 u = 0 → InternalDeficit.Router h →
        Module.finrank ℂ (Algebra.adjoin ℂ (InternalDeficit.baseGens ∪
          InternalDeficit.bridgeGens u ∪ InternalDeficit.routerGen h)) = 11) ∧
      (0 < InternalAssembly.omega7 u →
        Module.finrank ℂ (Algebra.adjoin ℂ (InternalDeficit.baseGens ∪
          InternalDeficit.bridgeGens u)) = 13) ∧
      (0 < InternalAssembly.omega7 u → InternalDeficit.Router h →
        Module.finrank ℂ (Algebra.adjoin ℂ (InternalDeficit.baseGens ∪
          InternalDeficit.bridgeGens u ∪ InternalDeficit.routerGen h)) = 15)) ∧
    Module.finrank ℂ CentralSeparation.lockedAlgebra = 14 := by
  obtain ⟨hA1, hA2, hA3, -, htab⟩ := FiniteLanding.finite_internal_landing_alternative
  refine ⟨⟨hA1, hA2, hA3⟩, ?_, htab, CentralSeparation.finrank_lockedAlgebra⟩
  intro n _ _ G _ ι _ _ I J _ _ _ _ ρ W hW1 hW2 hNI hM lab hlab hcen e hle β _ x hx τ hτ hτu
    hpriv hcol t h ht hh htu hhu hPt hPh hwk hsep
  exact landing_saturation_words ρ W hW1 hW2 hNI hM hlab hcen e hle x hx hτ hτu hpriv hcol ht hh
    htu hhu hPt hPh hwk hsep

end FiniteLandingWords
end RenewalGeometry
