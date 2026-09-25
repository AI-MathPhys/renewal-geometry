/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Predictive.FlatMultiplicityObstruction
import RenewalGeometry.StandardModel.BridgeRouterResidualsExact
import RenewalGeometry.StandardModel.InternalDeficitAlternativesExact

/-!
# The finite internal landing alternative

`thm:finite-internal-landing-alternative` of the spacetime–gauge duality paper: the four
branches of the colour/weak landing decision tree, each with its finite algebraic witness,
together with the dimension table of `thm:internal-deficit-alternatives`.

* **(A1)** `landing_flat_obstruction`: at a flat word depth `r` with `m_{λ,r} < 3`, no
  internal `M₃(ℂ)` factor on the `λ`-multiplicity space exists at any depth
  (`cor:flat-multiplicity-obstruction` with `n = 3`, `FlatMultiplicityObstruction.lean`);
* **(A2)** `landing_reducible_colour`: if every represented type–private bridge `u ∈ U` on
  the displayed three-space `T ⊕ H_priv` has `δ_col(u) = 0`, the colour algebra generated
  by `p_T`, the private matrix units and all bridges is **exactly** the reducible block
  algebra `M₂ ⊕ ℂ` (`thm:colour-bridge`, `BridgeRouterResidualsExact.lean`);
* **(A3)** `landing_commutative_weak`: if every pair of represented rank-one carriers on
  the weak multiplicity plane has `δ_wk = 0`, the represented weak algebra is commutative
  (`lem:weak-M2`: the carriers pairwise commute);
* **(A4)** `landing_saturation`: on the census `(3,2,1,1)` carrier `ℂ³ ⊕ ℂ² ⊕ ℂ ⊕ ℂ`, a
  colour-supported bridge with `δ_col > 0` and a weak router with `δ_wk > 0` (relative
  to the represented weak line `e₃`) make the represented internal word algebra the full
  block algebra `M₃ ⊕ M₂ ⊕ ℂ ⊕ ℂ` (`thm:internal-seed-saturation` in the concrete form of
  `InternalDeficitAlternativesExact.lean`); `router_iff_weakResidual_pos` identifies the
  router condition of that file with `δ_wk(e₃, h) > 0`;
* the dimension table `9 / 11 / 13 / 15` is `InternalDeficit.internal_deficit_alternatives`.

`finite_internal_landing_alternative` assembles the five clauses.  The paper's phrase
"exactly one of the outcomes applies" is the decision-tree reading of these four
implications (their hypotheses are the successive branch tests); the mathematical content
is the four implications with their explicit witnesses, which is what is formalized.
-/

open Finset Matrix

namespace RenewalGeometry
namespace FiniteLanding

open FlatMultiplicity BridgeRouter InternalSeed InternalAssembly InternalDeficit

/-! ### (A1) Flat depth with `m_{0,r} < 3` -/

/-- **(A1)**: at a flat word depth `r` with `m_{λ,r} < 3`, no internal `M₃(ℂ)` factor is
carried by the `λ`-multiplicity space at any depth (no injective linear map, a fortiori no
unital algebra homomorphism `M₃(ℂ) → End(M_λ(𝒱_s))`). -/
theorem landing_flat_obstruction {E : Type*} [AddCommGroup E] [Module ℂ E] {ι G : Type*}
    {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ E] [FiniteDimensional ℂ W]
    (L : ι → E →ₗ[ℂ] E) (V0 : Submodule ℂ E) (ρ : G → E →ₗ[ℂ] E) (σ : G → W →ₗ[ℂ] W) (r : ℕ)
    (hflat : Module.finrank ℂ (wordSpan L V0 (r + 1)) ≤ Module.finrank ℂ (wordSpan L V0 r))
    (hm : mult L V0 ρ σ r < 3) :
    (∀ s, mult L V0 ρ σ s < 3) ∧
    (∀ s, ∀ f : Matrix (Fin 3) (Fin 3) ℂ →ₗ[ℂ] lambdaBlock L V0 ρ σ s, ¬ Function.Injective f) ∧
    (∀ s, 0 < mult L V0 ρ σ s →
      ∀ _φ : Matrix (Fin 3) (Fin 3) ℂ →ₐ[ℂ] lambdaBlock L V0 ρ σ s, False) := by
  obtain ⟨-, h1, h2, h3⟩ := flat_multiplicity_obstruction L V0 ρ σ r 3 hflat hm
  exact ⟨h1, h2, fun s hs φ => h3 s hs φ⟩

/-! ### (A2) Every bridge has `δ_col = 0` -/

/-- The colour generators for a family `U` of represented type–private bridges: `p_T`, the
private matrix units, and every `u ∈ U` with its adjoint. -/
def bridgeFamilyGens (U : Set (Matrix (Fin 3) (Fin 3) ℂ)) : Set (Matrix (Fin 3) (Fin 3) ℂ) :=
  InternalSeed.gens 0 ∪ U ∪ (fun u => uᴴ) '' U

theorem colourResidual_zero : colourResidual (0 : Matrix (Fin 3) (Fin 3) ℂ) = 0 := by
  rw [colourResidual_eq_omegaCol, InternalSeed.omegaCol]
  simp

/-- **(A2)**: if every represented bridge has `δ_col = 0`, the colour algebra is exactly the
reducible block algebra `M₂ ⊕ ℂ` (and in particular not `M₃`). -/
theorem landing_reducible_colour (U : Set (Matrix (Fin 3) (Fin 3) ℂ))
    (hU : ∀ u ∈ U, colourResidual u = 0) :
    Algebra.adjoin ℂ (bridgeFamilyGens U) = InternalSeed.blockDiag ∧
      Algebra.adjoin ℂ (bridgeFamilyGens U) ≠ ⊤ := by
  have heq : Algebra.adjoin ℂ (bridgeFamilyGens U) = InternalSeed.blockDiag := by
    refine le_antisymm (Algebra.adjoin_le ?_) ?_
    · rintro X ((hX | hX) | ⟨u, hu, rfl⟩)
      · exact gens_subset_blockDiag colourResidual_zero hX
      · exact gens_subset_blockDiag (hU X hX) (by simp [InternalSeed.gens])
      · exact gens_subset_blockDiag (hU u hu) (by simp [InternalSeed.gens])
    · exact (blockDiag_le_adjoin 0).trans
        (Algebra.adjoin_mono (Set.subset_union_left.trans Set.subset_union_left))
  exact ⟨heq, by rw [heq]; exact blockDiag_ne_top⟩

/-! ### (A3) Every weak pair has `δ_wk = 0` -/

/-- Vanishing weak residual means the two carriers commute. -/
theorem commute_of_weakResidual_zero (t h : Fin 2 → ℂ) (h0 : weakResidual t h = 0) :
    proj t * proj h = proj h * proj t := by
  rw [weakResidual, frobSq] at h0
  have hrow := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _).mp h0
  rw [← sub_eq_zero]
  ext i j
  have hij := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => Complex.normSq_nonneg _).mp
    (hrow i (Finset.mem_univ i)) j (Finset.mem_univ j)
  rw [Matrix.zero_apply]
  exact Complex.normSq_eq_zero.mp hij

/-- **(A3)**: if every pair of represented carriers on the weak plane has `δ_wk = 0`, the
represented weak multiplicity algebra is commutative. -/
theorem landing_commutative_weak (T : Set (Fin 2 → ℂ))
    (hT : ∀ t ∈ T, ∀ h ∈ T, weakResidual t h = 0) :
    ∀ x ∈ Algebra.adjoin ℂ (proj '' T), ∀ y ∈ Algebra.adjoin ℂ (proj '' T), x * y = y * x := by
  have hgen : ∀ a ∈ proj '' T, ∀ b ∈ proj '' T, Commute a b := by
    rintro _ ⟨t, ht, rfl⟩ _ ⟨h, hh, rfl⟩
    exact commute_of_weakResidual_zero t h (hT t ht h hh)
  intro x hx y hy
  have hgy : ∀ g ∈ proj '' T, Commute g y := fun g hg =>
    Algebra.commute_of_mem_adjoin_of_forall_mem_commute hy (hgen g hg)
  have hyx : Commute y x :=
    Algebra.commute_of_mem_adjoin_of_forall_mem_commute hx fun g hg => (hgy g hg).symm
  exact hyx.symm

/-! ### (A4) Positive colour and weak residuals on the census `(3,2,1,1)` carrier -/

/-- The weak-plane coordinates of a router vector on the assembled carrier. -/
def weakPart (h : Fin 7 → ℂ) : Fin 2 → ℂ := ![h 3, h 4]

/-- The represented weak line `e₃` (the projection `E₃₃` of `baseGens`). -/
def weakTail : Fin 2 → ℂ := ![1, 0]

theorem normSqVec_weakTail : normSqVec weakTail = 1 := by
  simp [normSqVec, weakTail, Fin.sum_univ_two]

theorem overlap_weakTail (h : Fin 7 → ℂ) : overlap weakTail (weakPart h) = h 3 := by
  simp [overlap, weakTail, weakPart, Fin.sum_univ_two]

/-- **The router condition is a positive weak residual**: for a unit vector `h` on the weak
plane, `Router h` (both weak coordinates nonzero) iff `δ_wk(e₃, h) > 0`. -/
theorem router_iff_weakResidual_pos (h : Fin 7 → ℂ) (hw : WeakSupported h)
    (hunit : normSqVec (weakPart h) = 1) :
    Router h ↔ 0 < weakResidual weakTail (weakPart h) := by
  rw [weakResidual_pos_iff _ _ normSqVec_weakTail hunit, overlap_weakTail, Router]
  have hsum : Complex.normSq (h 3) + Complex.normSq (h 4) = 1 := by
    simpa [normSqVec, weakPart, Fin.sum_univ_two] using hunit
  have hne : proj weakTail ≠ proj (weakPart h) ↔ h 4 ≠ 0 := by
    rw [Ne, proj_eq_iff _ _ normSqVec_weakTail hunit, overlap_weakTail]
    constructor
    · intro h1 h4
      apply h1
      rw [h4, Complex.normSq_zero, add_zero] at hsum
      exact hsum
    · intro h4 h3
      apply h4
      rw [h3] at hsum
      exact Complex.normSq_eq_zero.mp (by linarith)
  rw [hne]
  constructor
  · rintro ⟨-, h3, h4⟩; exact ⟨h4, h3⟩
  · rintro ⟨h4, h3⟩; exact ⟨hw, h3, h4⟩

/-- **(A4)**: on the census `(3,2,1,1)` carrier, a colour-supported bridge with `δ_col > 0`
(`omega7`) and a unit weak router with `δ_wk(e₃, h) > 0` make the represented internal
word algebra the full block algebra `M₃ ⊕ M₂ ⊕ ℂ ⊕ ℂ`, of dimension `15`. -/
theorem landing_saturation {u : Matrix (Fin 7) (Fin 7) ℂ} (hsupp : ColourSupported u)
    (hpos : 0 < omega7 u) {h : Fin 7 → ℂ} (hw : WeakSupported h)
    (hunit : normSqVec (weakPart h) = 1) (hres : 0 < weakResidual weakTail (weakPart h)) :
    Algebra.adjoin ℂ (baseGens ∪ bridgeGens u ∪ routerGen h) = InternalAssembly.blockAlgebra ∧
    Module.finrank ℂ (Algebra.adjoin ℂ (baseGens ∪ bridgeGens u ∪ routerGen h)) = 15 := by
  have hr : Router h := (router_iff_weakResidual_pos h hw hunit).mpr hres
  exact ⟨adjoin_both_eq_blockAlgebra hsupp hpos hr, finrank_both hsupp hpos hr⟩

/-! ### The assembled alternative -/

/-- **`thm:finite-internal-landing-alternative`** (spacetime–gauge duality paper): the four
branches (A1)–(A4) with their finite algebraic witnesses, and the dimension table of
`thm:internal-deficit-alternatives` on the census `(3,2,1,1)`. -/
theorem finite_internal_landing_alternative :
    -- (A1)
    (∀ {E : Type} [AddCommGroup E] [Module ℂ E] {ι G : Type} {W : Type} [AddCommGroup W]
      [Module ℂ W] [FiniteDimensional ℂ E] [FiniteDimensional ℂ W]
      (L : ι → E →ₗ[ℂ] E) (V0 : Submodule ℂ E) (ρ : G → E →ₗ[ℂ] E) (σ : G → W →ₗ[ℂ] W) (r : ℕ),
      Module.finrank ℂ (wordSpan L V0 (r + 1)) ≤ Module.finrank ℂ (wordSpan L V0 r) →
      mult L V0 ρ σ r < 3 →
      ∀ s, ∀ f : Matrix (Fin 3) (Fin 3) ℂ →ₗ[ℂ] lambdaBlock L V0 ρ σ s, ¬ Function.Injective f) ∧
    -- (A2)
    (∀ U : Set (Matrix (Fin 3) (Fin 3) ℂ), (∀ u ∈ U, colourResidual u = 0) →
      Algebra.adjoin ℂ (bridgeFamilyGens U) = InternalSeed.blockDiag) ∧
    -- (A3)
    (∀ T : Set (Fin 2 → ℂ), (∀ t ∈ T, ∀ h ∈ T, weakResidual t h = 0) →
      ∀ x ∈ Algebra.adjoin ℂ (proj '' T), ∀ y ∈ Algebra.adjoin ℂ (proj '' T), x * y = y * x) ∧
    -- (A4)
    (∀ (u : Matrix (Fin 7) (Fin 7) ℂ) (h : Fin 7 → ℂ), ColourSupported u → 0 < omega7 u →
      WeakSupported h → normSqVec (weakPart h) = 1 → 0 < weakResidual weakTail (weakPart h) →
      Algebra.adjoin ℂ (baseGens ∪ bridgeGens u ∪ routerGen h) = InternalAssembly.blockAlgebra) ∧
    -- the dimension table of `thm:internal-deficit-alternatives`
    (∀ (u : Matrix (Fin 7) (Fin 7) ℂ) (h : Fin 7 → ℂ), ColourSupported u →
      (omega7 u = 0 → Module.finrank ℂ (Algebra.adjoin ℂ (baseGens ∪ bridgeGens u)) = 9) ∧
      (omega7 u = 0 → Router h →
        Module.finrank ℂ (Algebra.adjoin ℂ (baseGens ∪ bridgeGens u ∪ routerGen h)) = 11) ∧
      (0 < omega7 u → Module.finrank ℂ (Algebra.adjoin ℂ (baseGens ∪ bridgeGens u)) = 13) ∧
      (0 < omega7 u → Router h →
        Module.finrank ℂ (Algebra.adjoin ℂ (baseGens ∪ bridgeGens u ∪ routerGen h)) = 15)) :=
  ⟨fun L V0 ρ σ r hflat hm => (landing_flat_obstruction L V0 ρ σ r hflat hm).2.1,
    fun U hU => (landing_reducible_colour U hU).1,
    landing_commutative_weak,
    fun u h hsupp hpos hw hunit hres => (landing_saturation hsupp hpos hw hunit hres).1,
    fun u h hsupp => internal_deficit_alternatives hsupp (h := h)⟩

end FiniteLanding
end RenewalGeometry
