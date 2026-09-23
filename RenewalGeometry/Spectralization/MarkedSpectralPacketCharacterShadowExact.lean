/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Spectralization.CoordinateFiniteSpectralPacketMarkedRenewalRealizationExact
/-!
# Marked spectral packets and the character shadow of frame holonomy

This file covers, for `papers/predictive_spectral_geometry`,

* `def:supp-marked-spectral-packet` — a marked finite spectral packet
  `𝖲 = (𝒜, ℋ, D, J, γ; 𝔪)` (`MarkedFiniteSpectralPacket`) together with its
  automorphism group `G_𝖲 = Aut(𝖲)` (`MarkedFiniteSpectralPacket.autGroup`):
  the subgroup of the finite unitary group of the carrier consisting of the
  unitaries commuting with `D`, `γ`, `J` (`packetAutomorphisms`), respecting the
  declared algebra automorphism convention (`algebraConventionSubgroup`:
  pointwise fixing or setwise normalizing the represented algebra) and
  stabilizing the declared marking data `𝔪` (the marking is an element of an
  arbitrary type carrying an action of the unitary group, so "preserving the
  marks" is the stabilizer condition).  Compactness of `G_𝖲` is not proved
  here.
* `thm:supp-character-shadow` — trivial frame holonomy forces trivial character
  holonomies (`characters_trivial_of_holonomy_trivial`), and the converse holds
  for all monodromies of a free group of positive rank exactly when the joint
  kernel of the characters is trivial (`characters_detect_holonomy_iff`);
  specialised to `U(1)`-valued (`Circle`) and sign-valued (`ℤˣ`) characters of
  `G_𝖲` in `characters_detect_holonomy_iff_autGroup`.
-/

open Matrix

namespace RenewalGeometry
namespace MarkedSpectralPacketCharacterShadow

open CoordinateFiniteSpectralPacketMarkedRenewalRealizationExact

universe u

/-! ## Unitary automorphisms of a finite real even packet -/

section Packet

variable {A : Type u} {K : Type} [Ring A] [Algebra ℂ A] [StarRing A]
  [StarModule ℂ A] [Fintype K] [DecidableEq K]

/-- The unitary automorphisms of the operator data `(D, γ, J)` of a finite real
even spectral packet: unitaries commuting with the Dirac operator, the grading
and the real operation. -/
def packetAutomorphisms (P : CoordinateFiniteRealEvenSpectralPacket A K) :
    Subgroup (Matrix.unitaryGroup K ℂ) where
  carrier := {U | (U : Matrix K K ℂ) * P.dirac = P.dirac * U ∧
    (U : Matrix K K ℂ) * P.grading = P.grading * U ∧
    ∀ x : K → ℂ, P.realOperation ((U : Matrix K K ℂ) *ᵥ x) =
      (U : Matrix K K ℂ) *ᵥ P.realOperation x}
  one_mem' := by
    refine ⟨?_, ?_, fun x => ?_⟩ <;> simp
  mul_mem' := by
    intro U V hU hV
    refine ⟨?_, ?_, fun x => ?_⟩
    · rw [Matrix.UnitaryGroup.mul_val, mul_assoc, hV.1, ← mul_assoc, hU.1, mul_assoc]
    · rw [Matrix.UnitaryGroup.mul_val, mul_assoc, hV.2.1, ← mul_assoc, hU.2.1, mul_assoc]
    · rw [Matrix.UnitaryGroup.mul_val, ← mulVec_mulVec, hU.2.2, hV.2.2, mulVec_mulVec]
  inv_mem' := by
    intro U hU
    have h1 : star (U : Matrix K K ℂ) * U = 1 := Matrix.UnitaryGroup.star_mul_self U
    have h2 : (U : Matrix K K ℂ) * star (U : Matrix K K ℂ) = 1 := Unitary.mul_star_self_of_mem U.2
    refine ⟨?_, ?_, fun x => ?_⟩
    · rw [Matrix.UnitaryGroup.inv_val]
      calc star (U : Matrix K K ℂ) * P.dirac
          = star (U : Matrix K K ℂ) * P.dirac * (U * star (U : Matrix K K ℂ)) := by rw [h2, mul_one]
        _ = star (U : Matrix K K ℂ) * (P.dirac * U) * star (U : Matrix K K ℂ) := by simp only [mul_assoc]
        _ = star (U : Matrix K K ℂ) * (U * P.dirac) * star (U : Matrix K K ℂ) := by rw [hU.1]
        _ = P.dirac * star (U : Matrix K K ℂ) := by rw [← mul_assoc, h1, one_mul]
    · rw [Matrix.UnitaryGroup.inv_val]
      calc star (U : Matrix K K ℂ) * P.grading
          = star (U : Matrix K K ℂ) * P.grading * (U * star (U : Matrix K K ℂ)) := by rw [h2, mul_one]
        _ = star (U : Matrix K K ℂ) * (P.grading * U) * star (U : Matrix K K ℂ) := by simp only [mul_assoc]
        _ = star (U : Matrix K K ℂ) * (U * P.grading) * star (U : Matrix K K ℂ) := by rw [hU.2.1]
        _ = P.grading * star (U : Matrix K K ℂ) := by rw [← mul_assoc, h1, one_mul]
    · rw [Matrix.UnitaryGroup.inv_val]
      have h3 := hU.2.2 (star (U : Matrix K K ℂ) *ᵥ x)
      rw [mulVec_mulVec, h2, one_mulVec] at h3
      calc P.realOperation (star (U : Matrix K K ℂ) *ᵥ x)
          = star (U : Matrix K K ℂ) *ᵥ ((U : Matrix K K ℂ) *ᵥ
              P.realOperation (star (U : Matrix K K ℂ) *ᵥ x)) := by
            rw [mulVec_mulVec, h1, one_mulVec]
        _ = star (U : Matrix K K ℂ) *ᵥ P.realOperation x := by rw [← h3]

/-- Membership in `packetAutomorphisms` unfolded. -/
theorem mem_packetAutomorphisms_iff {P : CoordinateFiniteRealEvenSpectralPacket A K}
    {U : Matrix.unitaryGroup K ℂ} :
    U ∈ packetAutomorphisms P ↔
      (U : Matrix K K ℂ) * P.dirac = P.dirac * U ∧
        (U : Matrix K K ℂ) * P.grading = P.grading * U ∧
        ∀ x : K → ℂ, P.realOperation ((U : Matrix K K ℂ) *ᵥ x) =
          (U : Matrix K K ℂ) *ᵥ P.realOperation x :=
  Iff.rfl

/-- The two declared algebra automorphism conventions: a packet automorphism
either fixes the represented algebra pointwise (`pointwise`) or normalises it
as a set (`setwise`). -/
inductive AlgebraConvention
  | pointwise
  | setwise

/-- Unitaries fixing every represented algebra element: `U π(b) U* = π(b)`. -/
def pointwiseAlgebraFixing (P : CoordinateFiniteRealEvenSpectralPacket A K) :
    Subgroup (Matrix.unitaryGroup K ℂ) where
  carrier := {U | ∀ b : A,
    (U : Matrix K K ℂ) * P.representation b * star (U : Matrix K K ℂ) = P.representation b}
  one_mem' := by intro b; simp
  mul_mem' := by
    intro U V hU hV b
    rw [Matrix.UnitaryGroup.mul_val, star_mul]
    calc (U : Matrix K K ℂ) * V * P.representation b * (star (V : Matrix K K ℂ) * star (U : Matrix K K ℂ))
        = (U : Matrix K K ℂ) * (V * P.representation b * star (V : Matrix K K ℂ)) * star (U : Matrix K K ℂ) := by
          simp only [mul_assoc]
      _ = P.representation b := by rw [hV b, hU b]
  inv_mem' := by
    intro U hU b
    have h1 : star (U : Matrix K K ℂ) * U = 1 := Matrix.UnitaryGroup.star_mul_self U
    rw [Matrix.UnitaryGroup.inv_val, star_star]
    calc star (U : Matrix K K ℂ) * P.representation b * U
        = star (U : Matrix K K ℂ) *
            ((U : Matrix K K ℂ) * P.representation b * star (U : Matrix K K ℂ)) * U := by rw [hU b]
      _ = (star (U : Matrix K K ℂ) * U) * P.representation b * (star (U : Matrix K K ℂ) * U) := by
          simp only [mul_assoc]
      _ = P.representation b := by rw [h1, one_mul, mul_one]

/-- Unitaries normalising the represented algebra setwise:
`U π(𝒜) U* = π(𝒜)`. -/
def setwiseAlgebraNormalizing (P : CoordinateFiniteRealEvenSpectralPacket A K) :
    Subgroup (Matrix.unitaryGroup K ℂ) where
  carrier := {U |
    (∀ b : A, ∃ b' : A,
      (U : Matrix K K ℂ) * P.representation b * star (U : Matrix K K ℂ) = P.representation b') ∧
    (∀ b : A, ∃ b' : A,
      star (U : Matrix K K ℂ) * P.representation b * U = P.representation b')}
  one_mem' := ⟨fun b => ⟨b, by simp⟩, fun b => ⟨b, by simp⟩⟩
  mul_mem' := by
    intro U V hU hV
    refine ⟨fun b => ?_, fun b => ?_⟩
    · obtain ⟨b₁, hb₁⟩ := hV.1 b
      obtain ⟨b₂, hb₂⟩ := hU.1 b₁
      refine ⟨b₂, ?_⟩
      rw [Matrix.UnitaryGroup.mul_val, star_mul, ← hb₂, ← hb₁]
      simp only [mul_assoc]
    · obtain ⟨b₁, hb₁⟩ := hU.2 b
      obtain ⟨b₂, hb₂⟩ := hV.2 b₁
      refine ⟨b₂, ?_⟩
      rw [Matrix.UnitaryGroup.mul_val, star_mul, ← hb₂, ← hb₁]
      simp only [mul_assoc]
  inv_mem' := by
    intro U hU
    refine ⟨fun b => ?_, fun b => ?_⟩
    · obtain ⟨b', hb'⟩ := hU.2 b
      exact ⟨b', by rw [Matrix.UnitaryGroup.inv_val, star_star, hb']⟩
    · obtain ⟨b', hb'⟩ := hU.1 b
      exact ⟨b', by rw [Matrix.UnitaryGroup.inv_val, star_star, hb']⟩

/-- The subgroup cut out by a declared algebra automorphism convention. -/
def algebraConventionSubgroup (P : CoordinateFiniteRealEvenSpectralPacket A K) :
    AlgebraConvention → Subgroup (Matrix.unitaryGroup K ℂ)
  | .pointwise => pointwiseAlgebraFixing P
  | .setwise => setwiseAlgebraNormalizing P

/-- `def:supp-marked-spectral-packet` (Marked spectral packet): a finite real
even spectral packet `(𝒜, ℋ, D, J, γ)` in orthonormal coordinates, together
with declared auxiliary marking data `𝔪` (an element of a type `Mark` carrying
an action of the unitary group of the carrier, so that "preserved by a unitary"
means "stabilised") and a declared algebra automorphism convention. -/
structure MarkedFiniteSpectralPacket (A : Type u) (K : Type)
    [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]
    [Fintype K] [DecidableEq K] where
  /-- The underlying finite real even spectral packet `(𝒜, ℋ, D, J, γ)`. -/
  packet : CoordinateFiniteRealEvenSpectralPacket A K
  /-- The type of declared auxiliary marking data (orientation, modular,
  calibration, frame, determinant-line markings, ...). -/
  Mark : Type
  /-- How unitaries of the carrier transport the marking data. -/
  [markAction : MulAction (Matrix.unitaryGroup K ℂ) Mark]
  /-- The declared marking `𝔪`. -/
  mark : Mark
  /-- The declared algebra automorphism convention. -/
  convention : AlgebraConvention

attribute [instance] MarkedFiniteSpectralPacket.markAction

/-- `G_𝖲 = Aut(𝖲)` (eq:supp-marked-aut): the group of unitary packet
automorphisms preserving the markings and the declared algebra automorphism
convention. -/
def MarkedFiniteSpectralPacket.autGroup (S : MarkedFiniteSpectralPacket A K) :
    Subgroup (Matrix.unitaryGroup K ℂ) :=
  packetAutomorphisms S.packet ⊓ algebraConventionSubgroup S.packet S.convention ⊓
    MulAction.stabilizer (Matrix.unitaryGroup K ℂ) S.mark

/-- Membership in `G_𝖲` unfolded: commutation with `D`, `γ`, `J`, the algebra
convention, and stabilisation of the marking. -/
theorem MarkedFiniteSpectralPacket.mem_autGroup_iff (S : MarkedFiniteSpectralPacket A K)
    (U : Matrix.unitaryGroup K ℂ) :
    U ∈ S.autGroup ↔
      ((U : Matrix K K ℂ) * S.packet.dirac = S.packet.dirac * U ∧
        (U : Matrix K K ℂ) * S.packet.grading = S.packet.grading * U ∧
        ∀ x : K → ℂ, S.packet.realOperation ((U : Matrix K K ℂ) *ᵥ x) =
          (U : Matrix K K ℂ) *ᵥ S.packet.realOperation x) ∧
      U ∈ algebraConventionSubgroup S.packet S.convention ∧
      U • S.mark = S.mark := by
  simp only [MarkedFiniteSpectralPacket.autGroup, Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
  exact ⟨fun h => ⟨mem_packetAutomorphisms_iff.mp h.1.1, h.1.2, h.2⟩,
    fun h => ⟨⟨mem_packetAutomorphisms_iff.mpr h.1, h.2.1⟩, h.2.2⟩⟩

end Packet

/-! ## Line characters as shadows of frame holonomy -/

section Characters

variable {F G L M : Type*} [Group F] [Group G] [Group L] [Group M] {ι κ : Type*}

/-- The joint kernel `⋂_j Ker χ_j ∩ ⋂_k Ker ε_k` of two families of characters
(eq:supp-character-faithfulness). -/
def jointCharacterKernel (χ : ι → G →* L) (ε : κ → G →* M) : Subgroup G :=
  (⨅ j, (χ j).ker) ⊓ (⨅ k, (ε k).ker)

theorem mem_jointCharacterKernel_iff (χ : ι → G →* L) (ε : κ → G →* M) (g : G) :
    g ∈ jointCharacterKernel χ ε ↔ (∀ j, χ j g = 1) ∧ ∀ k, ε k g = 1 := by
  simp [jointCharacterKernel, Subgroup.mem_inf, Subgroup.mem_iInf, MonoidHom.mem_ker]

/-- `thm:supp-character-shadow`, first half: trivial frame holonomy `ρ = 1`
implies triviality of every induced character holonomy `χ_j ∘ ρ`, `ε_k ∘ ρ`. -/
theorem characters_trivial_of_holonomy_trivial (ρ : F →* G) (hρ : ρ = 1)
    (χ : ι → G →* L) (ε : κ → G →* M) :
    (∀ j, (χ j).comp ρ = 1) ∧ ∀ k, (ε k).comp ρ = 1 := by
  subst hρ
  exact ⟨fun j => by ext; simp, fun k => by ext; simp⟩

/-- If the joint kernel is trivial, then trivial character holonomies force
trivial frame holonomy, for monodromies of an arbitrary group `F`. -/
theorem holonomy_trivial_of_characters_trivial (χ : ι → G →* L) (ε : κ → G →* M)
    (hker : jointCharacterKernel χ ε = ⊥) (ρ : F →* G)
    (hχ : ∀ j, (χ j).comp ρ = 1) (hε : ∀ k, (ε k).comp ρ = 1) : ρ = 1 := by
  ext x
  have hmem : ρ x ∈ jointCharacterKernel χ ε := by
    rw [mem_jointCharacterKernel_iff]
    exact ⟨fun j => by simpa using DFunLike.congr_fun (hχ j) x,
      fun k => by simpa using DFunLike.congr_fun (hε k) x⟩
  rw [hker, Subgroup.mem_bot] at hmem
  simpa using hmem

/-- `thm:supp-character-shadow`, second half: over a free fundamental group of
positive rank `b₁ ≥ 1` (generators indexed by a nonempty type `β`), the
character holonomies detect the frame holonomy of every monodromy
`ρ : π₁ → G` exactly when the joint kernel of the characters is trivial. -/
theorem characters_detect_holonomy_iff {β : Type*} [Nonempty β]
    (χ : ι → G →* L) (ε : κ → G →* M) :
    (∀ ρ : FreeGroup β →* G,
        (∀ j, (χ j).comp ρ = 1) → (∀ k, (ε k).comp ρ = 1) → ρ = 1) ↔
      jointCharacterKernel χ ε = ⊥ := by
  constructor
  · intro h
    rw [Subgroup.eq_bot_iff_forall]
    intro g hg
    rw [mem_jointCharacterKernel_iff] at hg
    let ρ : FreeGroup β →* G := FreeGroup.lift fun _ => g
    have hρ : ρ = 1 := by
      refine h ρ (fun j => ?_) (fun k => ?_)
      · exact FreeGroup.ext_hom _ _ fun a => by simp [ρ, FreeGroup.lift_apply_of, hg.1 j]
      · exact FreeGroup.ext_hom _ _ fun a => by simp [ρ, FreeGroup.lift_apply_of, hg.2 k]
    have := DFunLike.congr_fun hρ (FreeGroup.of (Classical.arbitrary β))
    simpa [ρ, FreeGroup.lift_apply_of] using this
  · intro hker ρ hχ hε
    exact holonomy_trivial_of_characters_trivial χ ε hker ρ hχ hε

end Characters

section AutGroupCharacters

variable {A : Type u} {K : Type} [Ring A] [Algebra ℂ A] [StarRing A]
  [StarModule ℂ A] [Fintype K] [DecidableEq K]

/-- `thm:supp-character-shadow` for the automorphism group `G_𝖲` of a marked
packet, with `U(1)`-valued line characters `χ_j : G_𝖲 → Circle` and real
Pfaffian-sign characters `ε_k : G_𝖲 → {±1} = ℤˣ`, and monodromies of the free
group `π₁(Γ)` on `b₁(Γ) ≥ 1` generators. -/
theorem characters_detect_holonomy_iff_autGroup (S : MarkedFiniteSpectralPacket A K)
    {ι κ β : Type*} [Nonempty β]
    (χ : ι → S.autGroup →* Circle) (ε : κ → S.autGroup →* ℤˣ) :
    (∀ ρ : FreeGroup β →* S.autGroup,
        (∀ j, (χ j).comp ρ = 1) → (∀ k, (ε k).comp ρ = 1) → ρ = 1) ↔
      jointCharacterKernel χ ε = ⊥ :=
  characters_detect_holonomy_iff χ ε

/-- Trivial frame holonomy in `G_𝖲` forces trivial line and sign holonomies. -/
theorem characters_trivial_of_holonomy_trivial_autGroup (S : MarkedFiniteSpectralPacket A K)
    {ι κ : Type*} {F : Type*} [Group F] (ρ : F →* S.autGroup) (hρ : ρ = 1)
    (χ : ι → S.autGroup →* Circle) (ε : κ → S.autGroup →* ℤˣ) :
    (∀ j, (χ j).comp ρ = 1) ∧ ∀ k, (ε k).comp ρ = 1 :=
  characters_trivial_of_holonomy_trivial ρ hρ χ ε

end AutGroupCharacters

end MarkedSpectralPacketCharacterShadow
end RenewalGeometry
