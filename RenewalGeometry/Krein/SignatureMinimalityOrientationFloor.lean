/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Krein.SupplementSignatureMinimality
import RenewalGeometry.Predictive.OperationalEntranceCategory

/-!
# Irreducible sign and Lorentzian inertia, with the orientation floor
  (`thm:supp-signature-minimality`, emergent-spacetime manuscript)

`supp_signature_minimality` (Krein/SupplementSignatureMinimality.lean) proves the inertia
conclusion `eq:supp-signature-inertia` from positivity of the spatial form and the one-line
signed-extension condition (`def:main-signed-extension`).  The remaining premise of the
statement, that the protected orientation row is independent of the complete positive packet
(`thm:supp-relative-primitive-floor`), is now a theorem
(`OperationalEntrance.relative_primitive_floor`, Predictive/OperationalEntranceCategory.lean):
reversing the protected orientation of any finite typed operational-predictive model leaves
every other row (occurrence, complete predictive law, calibration) unchanged, gives
anchored-isomorphic reducts and non-isomorphic full models, and this survives every common
conservative refinement.  `supp_signature_minimality_with_floor` bundles both.
-/

open Matrix Module
open scoped ComplexOrder

namespace RenewalGeometry

open OperationalEntrance

/-- **`thm:supp-signature-minimality`.**  (Independence of the signed row) for every finite
typed operational-predictive model `M` over any anchored grammar, reversing the protected
orientation keeps the occurrence, predictive and calibration rows and is a separating pair for
the orientation row, which stays separating under every common conservative refinement; (the
positive packet supplies no negative direction) a positive definite spatial form `D` on
`W₄ = Fin 3` has nonnegative quadratic form and no negative inertia; (one-line signed
extension) for the orthogonal extension by one independent line with negative coefficient `c`,
`c = -a²` for a unique `a > 0`, `q(τ t + w) = -a² τ² + g(w, w)`, the inertia is `(1, 3, 0)`,
that of `-q` is `(3, 1, 0)`, invariantly under every invertible change of basis. -/
theorem supp_signature_minimality_with_floor (c : ℝ) (hc : c < 0)
    (D : Matrix (Fin 3) (Fin 3) ℂ) (hD : D.PosDef) :
    (∀ {𝔊 : AnchoredGrammar} (M : OperationalEntrance.Model 𝔊),
      (M.withOrientation (-M.orientation)).occurs = M.occurs ∧
      (M.withOrientation (-M.orientation)).law = M.law ∧
      (M.withOrientation (-M.orientation)).calibration = M.calibration ∧
      IsSeparatingPair .orientation M (M.withOrientation (-M.orientation)) ∧
      ∀ {Y : Type} {rel : (Row → Prop) → Y → Y → Prop} (F : ConservativeRefinement 𝔊 Y rel),
        rel (forgetting .orientation) (F.extend M) (F.extend (M.withOrientation (-M.orientation)))
          ∧ ¬ rel full (F.extend M) (F.extend (M.withOrientation (-M.orientation)))) ∧
    ((∀ w : Fin 3 → ℂ, 0 ≤ quadForm D w) ∧ negInertia D = 0) ∧
    ∃! a : ℝ, 0 < a ∧ c = -a ^ 2 ∧
      (∀ (τ : ℝ) (w : Fin 3 → ℂ),
        quadForm (oneLineSignedExtension c D) (Sum.elim (fun _ : Fin 1 => (τ : ℂ)) w)
          = -a ^ 2 * τ ^ 2 + quadForm D w) ∧
      (negInertia (oneLineSignedExtension c D) = 1 ∧
        posInertia (oneLineSignedExtension c D) = 3 ∧
        nullInertia (oneLineSignedExtension c D) = 0) ∧
      (negInertia (-(oneLineSignedExtension c D)) = 3 ∧
        posInertia (-(oneLineSignedExtension c D)) = 1 ∧
        nullInertia (-(oneLineSignedExtension c D)) = 0) ∧
      (∀ X : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℂ, IsUnit X.det →
        negInertia (Xᴴ * oneLineSignedExtension c D * X) = 1 ∧
          posInertia (Xᴴ * oneLineSignedExtension c D * X) = 3 ∧
          nullInertia (Xᴴ * oneLineSignedExtension c D * X) = 0) := by
  obtain ⟨h1, h2⟩ := supp_signature_minimality c hc D hD
  refine ⟨fun M => ⟨rfl, rfl, rfl, separating_reverseOrientation M,
    fun F => refinement_preserves_separation F (separating_reverseOrientation M)⟩, h1, h2⟩

/-- Non-vacuity: the hypotheses are satisfiable (`c = -1`, `D = 1`). -/
example : True := by
  have := supp_signature_minimality_with_floor (-1) (by norm_num) 1 Matrix.PosDef.one
  trivial

end RenewalGeometry
