/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CanonicalArithmeticLoading
import NCG.Grand.CanonicalLoadedSubhierarchyAssembly
import NCG.Grand.ArithmeticForwardCutoffNaturality
import NCG.Grand.AbsorbingCutoff

/-!
# Exact canonical arithmetic-loading assembly

This module closes the two clauses that were compressed in the first
`CanonicalArithmeticLoadingCertificate`.

* A source-fixing chronology unitary is the identity, so it intertwines every
  member of the residue/character/affine/Mellin/heat/depth packet (indeed every
  matrix on the protected finite carrier).
* Every admissible arithmetic loaded-word datum has the complete canonical
  subhierarchy certificate: positive Grams, finite panel expansion, source
  admission, the represented kernel quotient, finite flat source-minimal
  reconstruction, exact cutoff Gram congruence, and represented products and
  adjoints.
* Forward arithmetic histories descend through a unital algebra homomorphism,
  and absorbing corners compose transitively.
-/

open Matrix

namespace NCG
namespace CanonicalArithmeticLoadingExact

/-- A source-and-writer-fixing chronology unitary intertwines the complete
finite arithmetic packet.  The conclusion is deliberately stronger than a
list of named histories: it commutes with every matrix on the carrier. -/
theorem sourceFixingChronology_intertwines_completePacket
    (X : ℕ) (hX : 0 < X)
    (U : Matrix (Fin X) (Fin X) ℂ)
    (hUleft : Uᴴ * U = 1) (hUright : U * Uᴴ = 1)
    (hchron : U * recS X = recS X * U)
    (hsource : U *ᵥ Pi.single (⟨0, hX⟩ : Fin X) 1 =
      Pi.single (⟨0, hX⟩ : Fin X) 1) :
    ∀ A : Matrix (Fin X) (Fin X) ℂ, U * A = A * U := by
  have hUid : U = 1 :=
    (peano_naturality hX U hUleft hUright hchron).2.2 hsource
  subst U
  intro A
  simp

/-- Exact assembly of the canonical arithmetic loading, including the
previously compressed complete-packet naturality and loaded-word
reconstruction clauses. -/
theorem canonical_arithmetic_loading_exact (X : ℕ) (hX : 0 < X) :
    CanonicalArithmeticLoadingCertificate X hX
    ∧ (∀ (U : Matrix (Fin X) (Fin X) ℂ),
        Uᴴ * U = 1 → U * Uᴴ = 1 →
        U * recS X = recS X * U →
        U *ᵥ Pi.single (⟨0, hX⟩ : Fin X) 1 =
          Pi.single (⟨0, hX⟩ : Fin X) 1 →
        ∀ A : Matrix (Fin X) (Fin X) ℂ, U * A = A * U)
    ∧ (∀ {h e panel selected A B eY : Type}
        [Fintype h] [Fintype e] [Fintype panel] [Fintype eY]
        [Ring A] [StarRing A] [Ring B] [StarRing B]
        (L : AdmissibleLoadedSubhierarchyData
          h e panel selected A B eY),
        CanonicalLoadedSubhierarchyCertificate L)
    ∧ (∀ {Y : ℕ} (hXY : X ≤ Y),
        (ArithmeticForwardCutoffNaturality.forwardCutoffAlgHom hXY
          (1 : forwardAlg Y) = 1)
        ∧ ((cornerJ X Y)ᴴ * recS Y * cornerJ X Y = recS X)
        ∧ ((cornerJ X Y)ᴴ * countN Y * cornerJ X Y = countN X)
        ∧ (∀ a, (cornerJ X Y)ᴴ * peanoL Y a * cornerJ X Y =
          peanoL X a)
        ∧ ((cornerJ X Y)ᴴ * zetaX Y * cornerJ X Y = zetaX X)
        ∧ (∀ f, (cornerJ X Y)ᴴ * diagFn Y f * cornerJ X Y =
          diagFn X f))
    ∧ (∀ {Y Z : ℕ} (hXY : X ≤ Y) (hYZ : Y ≤ Z)
        (A : Matrix (Fin Z) (Fin Z) ℂ),
        cornerJ Y Z * cornerJ X Y = cornerJ X Z
        ∧ (cornerJ X Z)ᴴ * A * cornerJ X Z =
          (cornerJ X Y)ᴴ *
            ((cornerJ Y Z)ᴴ * A * cornerJ Y Z) * cornerJ X Y) := by
  refine ⟨canonical_arithmetic_loading X hX, ?_, ?_, ?_, ?_⟩
  · intro U hUl hUr hchron hsource
    exact sourceFixingChronology_intertwines_completePacket
      X hX U hUl hUr hchron hsource
  · intro h e panel selected A B eY _ _ _ _ _ _ _ _ L
    exact canonicalLoadedSubhierarchyAssembly L
  · intro Y hXY
    have h :=
      ArithmeticForwardCutoffNaturality.forward_arithmetic_cutoff_naturality hXY
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
      h.2.2.2.2.2.2.2.2.1⟩
  · intro Y Z hXY hYZ A
    exact absorbing_cutoff hXY hYZ A

end CanonicalArithmeticLoadingExact
end NCG
