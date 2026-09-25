/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Predictive.ExactSourceSchurResidual

/-!
# The source-minimal quotient carrier and endpoint-block survival

Machinery for `thm:geometry-short` of the spacetime–gauge duality paper, beyond the
general Schur short (`ExactSourceSchurResidual`) and the scalar active realization
(`SMActiveResidualExact`):

* `finrank_minimalCarrier`: `eq:geometry-short-quotient` — for any Gram matrix `G`
  on the internal categorical carrier, `E^min := E / Ker G` has dimension `rank G`;
  `finrank_minimalCarrier_short` specialises to the shorted Gram
  `G_{int|ST} = sourceSchurResidual S_ST S_int`.
* `block_survives`: endpoint survival — if the Hermitian form of `G` does not vanish
  on nonzero vectors of a block `Ran Q` (`Q` idempotent; in particular if `G` is
  strictly positive there), the block meets `Ker G` trivially and injects into the
  quotient with its full rank.
-/

open Matrix Module

namespace RenewalGeometry
namespace GeometryShortQuotient

variable {e : ℕ}

/-- The source-minimal carrier `E^min = E / Ker G`. -/
abbrev minimalCarrier (G : Matrix (Fin e) (Fin e) ℂ) : Type :=
  (Fin e → ℂ) ⧸ LinearMap.ker G.mulVecLin

/-- `eq:geometry-short-quotient`: `dim (E / Ker G) = rank G`. -/
theorem finrank_minimalCarrier (G : Matrix (Fin e) (Fin e) ℂ) :
    finrank ℂ (minimalCarrier G) = G.rank := by
  have h1 := Submodule.finrank_quotient_add_finrank (LinearMap.ker G.mulVecLin)
  have h2 := LinearMap.finrank_range_add_finrank_ker G.mulVecLin
  unfold minimalCarrier Matrix.rank
  omega

/-- The quotient clause for the shorted Gram `G_{int|ST}`. -/
theorem finrank_minimalCarrier_short {h e₁ : ℕ}
    (S_ST : Matrix (Fin h) (Fin e₁) ℂ) (S_int : Matrix (Fin h) (Fin e) ℂ) :
    finrank ℂ (minimalCarrier (sourceSchurResidual S_ST S_int))
      = (sourceSchurResidual S_ST S_int).rank :=
  finrank_minimalCarrier _

/-- **Endpoint-block survival**: if the form of `G` does not vanish on nonzero
vectors of the block `Ran Q` (`Q * Q = Q`), then `Ran Q ∩ Ker G = 0` and the block
injects into `E / Ker G` with dimension `rank Q`. -/
theorem block_survives (G Q : Matrix (Fin e) (Fin e) ℂ) (hQ : Q * Q = Q)
    (hpos : ∀ v : Fin e → ℂ, Q *ᵥ v = v → v ≠ 0 → star v ⬝ᵥ (G *ᵥ v) ≠ 0) :
    LinearMap.range Q.mulVecLin ⊓ LinearMap.ker G.mulVecLin = ⊥ ∧
    finrank ℂ ((LinearMap.range Q.mulVecLin).map (LinearMap.ker G.mulVecLin).mkQ)
      = Q.rank := by
  have hdisj : LinearMap.range Q.mulVecLin ⊓ LinearMap.ker G.mulVecLin = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_inf, LinearMap.mem_range, LinearMap.mem_ker] at hv
    obtain ⟨⟨w, hw⟩, hG⟩ := hv
    rw [Matrix.mulVecLin_apply] at hw hG
    rw [Submodule.mem_bot]
    by_contra hne
    apply hpos v _ hne
    · rw [hG, dotProduct_zero]
    · rw [← hw, Matrix.mulVec_mulVec, hQ]
  refine ⟨hdisj, ?_⟩
  set p := LinearMap.range Q.mulVecLin
  set K := LinearMap.ker G.mulVecLin
  have h1 := LinearMap.finrank_range_add_finrank_ker (K.mkQ.domRestrict p)
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict, Submodule.ker_mkQ] at h1
  have hcomap : K.comap p.subtype = ⊥ := by
    rw [← Submodule.disjoint_iff_comap_eq_bot, disjoint_iff]
    exact hdisj
  rw [hcomap, finrank_bot, add_zero] at h1
  rw [h1]
  rfl

end GeometryShortQuotient
end RenewalGeometry
