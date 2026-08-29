/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GrassmannPairCalculusExact

/-!
# Exact orientation-positive ghost-quartet cancellation

This file proves `thm:SMFS-ghost-quartet`.  The fermionic factor is not an
opaque determinant assumption: it is the top Grassmann coefficient supplied
by `Grassmann.fermionic_gaussian`.  A positive Faddeev--Popov block has
nonzero determinant, so its normalized bosonic Gaussian factor cancels the
fermionic determinant exactly.  The corresponding infinitesimal determinant
responses cancel algebraically.  Finally, a finite nilpotent BRST differential
with a no-boundary Berezin functional kills every exact score direction.
-/

open ExteriorAlgebra
open scoped ComplexOrder

namespace NCG.GhostQuartetCancellation

variable {r : ℕ}

/-- The normalized positive bosonic gauge-fixing Gaussian evaluation. -/
noncomputable def bosonicGaugeFactor (L : Matrix (Fin r) (Fin r) ℂ) : ℂ :=
  L.det⁻¹

/-- The ghost Gaussian evaluation in the fixed positive Berezin orientation. -/
noncomputable def ghostGaugeFactor (L : Matrix (Fin r) (Fin r) ℂ) : ℂ :=
  L.det

/-- The completely assembled quartet factor. -/
noncomputable def quartetFactor (L : Matrix (Fin r) (Fin r) ℂ) : ℂ :=
  bosonicGaugeFactor L * ghostGaugeFactor L

/-- The concrete top Grassmann monomial before coefficient extraction. -/
noncomputable def ghostTopTerm (L : Matrix (Fin r) (Fin r) ℂ) :
    ExteriorAlgebra ℂ (Grassmann.Doubled r) :=
  (List.ofFn fun i => Grassmann.psibar i *
    ι ℂ (Grassmann.psiEmbed (L i))).prod

/-- The selected positive Berezin orientation. -/
noncomputable def ghostOrientation :
    ExteriorAlgebra ℂ (Grassmann.Doubled r) :=
  (List.ofFn fun i : Fin r => Grassmann.psibar i * Grassmann.psi i).prod

/-- The actual finite Grassmann Gaussian is the determinant times the selected
orientation. -/
theorem ghost_top_term_eq_det_smul (L : Matrix (Fin r) (Fin r) ℂ) :
    ghostTopTerm L = L.det • ghostOrientation := by
  exact Grassmann.fermionic_gaussian L

/-- `FS.31`: positivity makes the determinant nonzero, so the normalized
bosonic factor and the oriented ghost factor multiply to one. -/
theorem orientation_positive_quartet_cancellation
    (L : Matrix (Fin r) (Fin r) ℂ) (hL : L.PosDef) :
    quartetFactor L = 1 := by
  have hdet : L.det ≠ 0 := hL.det_pos.ne'
  simp [quartetFactor, bosonicGaugeFactor, ghostGaugeFactor, hdet]

/-- Logarithmic response of the bosonic inverse determinant. -/
noncomputable def bosonicDeterminantResponse (detValue detVariation : ℂ) : ℂ :=
  -(detValue⁻¹ * detVariation)

/-- Logarithmic response of the ghost determinant. -/
noncomputable def ghostDeterminantResponse (detValue detVariation : ℂ) : ℂ :=
  detValue⁻¹ * detVariation

/-- Every parameter variation cancels after complete quartet assembly. -/
theorem determinant_responses_cancel (detValue detVariation : ℂ) :
    bosonicDeterminantResponse detValue detVariation +
      ghostDeterminantResponse detValue detVariation = 0 := by
  simp [bosonicDeterminantResponse, ghostDeterminantResponse]

section BRST

variable {A : Type*} [AddCommGroup A] [Module ℂ A]

/-- A finite BRST/Berezin packet.  Nilpotency records `s²=0`; `noBoundary`
is the finite integration-by-parts statement `∫ s(a)=0`. -/
structure BRSTPacket (A : Type*) [AddCommGroup A] [Module ℂ A] where
  differential : A →ₗ[ℂ] A
  berezinIntegral : A →ₗ[ℂ] ℂ
  nilpotent : differential.comp differential = 0
  noBoundary : berezinIntegral.comp differential = 0

/-- A coefficient direction is BRST exact when it lies in the range of `s`. -/
def IsExact (p : BRSTPacket A) (x : A) : Prop :=
  ∃ ψ, x = p.differential ψ

/-- BRST nilpotency makes every exact direction closed. -/
theorem exact_is_closed (p : BRSTPacket A) {x : A} (hx : IsExact p x) :
    p.differential x = 0 := by
  obtain ⟨ψ, rfl⟩ := hx
  have h := LinearMap.congr_fun p.nilpotent ψ
  simpa [LinearMap.comp_apply] using h

/-- No-boundary Berezin integration kills every BRST-exact partition-score
direction. -/
theorem exact_partition_score_zero
    (p : BRSTPacket A) {x : A} (hx : IsExact p x) :
    p.berezinIntegral x = 0 := by
  obtain ⟨ψ, rfl⟩ := hx
  have h := LinearMap.congr_fun p.noBoundary ψ
  simpa [LinearMap.comp_apply] using h

/-- Bundled exact conclusion of `thm:SMFS-ghost-quartet`. -/
theorem ghost_quartet_and_BRST_descent
    (L : Matrix (Fin r) (Fin r) ℂ) (hL : L.PosDef)
    (detVariation : ℂ) (p : BRSTPacket A) {score : A}
    (hscore : IsExact p score) :
    ghostTopTerm L = L.det • ghostOrientation ∧
      quartetFactor L = 1 ∧
      (bosonicDeterminantResponse L.det detVariation +
        ghostDeterminantResponse L.det detVariation = 0) ∧
      p.differential score = 0 ∧
      p.berezinIntegral score = 0 := by
  exact ⟨ghost_top_term_eq_det_smul L,
    orientation_positive_quartet_cancellation L hL,
    determinant_responses_cancel L.det detVariation,
    exact_is_closed p hscore,
    exact_partition_score_zero p hscore⟩

end BRST

end NCG.GhostQuartetCancellation
