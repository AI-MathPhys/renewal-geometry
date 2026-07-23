/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Upstream.CommonOriginUCP

/-!
# Clifford generation partials for the common-origin factor

The provable finite clauses of `thm:common-origin-clifford`
(`manuscripts/renewal_emergence/renewal_emergence.tex`):

* `adMap_comp` — conjugations compose: `Ad(U) ∘ Ad(V) = Ad(UV)`;
* `ad_pair_generates` — the conditioned predictive units generate
  the sheet conjugation: `β_a ∘ α_a = Ad(JR_a) ∘ Ad(R_a) = Ad(J)`
  for a Hermitian involutive implementer `R_a`;
* `commForm` / `commForm_det` — the commutator form `Ω` of the
  implementing monomials on `H = F₂⁴` (`Ω_{μν} = 1 − δ_{μν}`) is
  **nondegenerate** over `F₂` (`det Ω = 1`).

The twisted-group-algebra identification
`ℂ_σ[H] ≅ Cl₄(ℂ) ≅ M₄(ℂ)` (finite Stone–von Neumann) is not
formalized; the record stays conditional with these lemmas recorded
as proved partial content.
-/

namespace NCG.CommonOrigin

open Matrix

/-- Conjugations compose: `Ad(U)(Ad(V)(X)) = Ad(UV)(X)`. -/
theorem adMap_comp (U V X : Matrix (Fin 4) (Fin 4) ℂ) :
    adMap U (adMap V X) = adMap (U * V) X := by
  rw [adMap_apply, adMap_apply, adMap_apply,
    Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

/-- **Theorem `thm:common-origin-clifford` (generation clause)**:
the conditioned predictive units generate the sheet conjugation —
`β_a α_a = Ad(JR_a) Ad(R_a) = Ad(J)` whenever the direction
implementer is Hermitian and involutive. -/
theorem ad_pair_generates (J R : Matrix (Fin 4) (Fin 4) ℂ)
    (_hR : Rᴴ = R) (hRR : R * R = 1)
    (X : Matrix (Fin 4) (Fin 4) ℂ) :
    adMap (J * R) (adMap R X) = adMap J X := by
  rw [adMap_comp]
  have h1 : J * R * R = J := by
    rw [Matrix.mul_assoc, hRR, Matrix.mul_one]
  rw [h1]

/-- The commutator form of the implementing monomials on
`H = F₂⁴`: `Ω_{μν} = 0` on the diagonal and `1` off it. -/
def commForm : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  Matrix.of fun μ ν => if μ = ν then 0 else 1

/-- **Theorem `thm:common-origin-clifford` (nondegeneracy)**: the
commutator form is nondegenerate over `F₂`. -/
theorem commForm_det : commForm.det = 1 := by decide

end NCG.CommonOrigin
