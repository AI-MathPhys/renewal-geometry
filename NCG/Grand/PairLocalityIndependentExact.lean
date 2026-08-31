/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.BrandNewEasy00

/-!
# Pair locality is independent of the complete first-response packet

This file packages the already exact two-site Duhamel calculation into the
logical independence assertion of cor:GTLOC-pair-locality-independent.  The
first selected response vanishes for every duration, while the quadratic
response at unit duration is nonzero and its ordered route visits a site at an
arbitrarily prescribed distance.
-/

open Matrix

namespace NCG
namespace PairLocalityIndependent

/-- The physical two-site metric whose second site is at distance N from the
source site. -/
def twoSiteDistance (N : ℕ) (i j : Fin 2) : ℕ :=
  if i = j then 0 else N

@[simp] theorem source_far_distance (N : ℕ) :
    twoSiteDistance N 0 1 = N := by
  simp [twoSiteDistance]

/-- The complete first-response packet can vanish at every duration while the
pair response is nonzero and its ordered route reaches a site at any prescribed
positive distance. -/
theorem pair_locality_is_independent (N : ℕ) (hN : 0 < N) :
    (∀ t : ℝ,
      star (Pi.single (0 : Fin 2) (1 : ℂ))
        ⬝ᵥ (duhamelFirst 0 longHop t *ᵥ Pi.single 0 1) = 0) ∧
    star (Pi.single (0 : Fin 2) (1 : ℂ))
        ⬝ᵥ (duhamelPair 0 longHop longHop 1 *ᵥ Pi.single 0 1) = 1 ∧
    longHop *ᵥ Pi.single (0 : Fin 2) (1 : ℂ) = Pi.single 1 1 ∧
    twoSiteDistance N 0 1 = N ∧ 0 < twoSiteDistance N 0 1 := by
  refine ⟨longHop_first_response_zero, ?_, longHop_route_excursion,
    source_far_distance N, ?_⟩
  · simpa using longHop_pair_response 1
  · simpa [source_far_distance] using hN

/-- Existential form: there is no implication from complete vanishing of the
first packet to vanishing of the pair packet. -/
theorem first_packet_does_not_determine_pair :
    ∃ (H V : Matrix (Fin 2) (Fin 2) ℂ),
      (∀ t : ℝ,
        star (Pi.single (0 : Fin 2) (1 : ℂ))
          ⬝ᵥ (duhamelFirst H V t *ᵥ Pi.single 0 1) = 0) ∧
      star (Pi.single (0 : Fin 2) (1 : ℂ))
          ⬝ᵥ (duhamelPair H V V 1 *ᵥ Pi.single 0 1) ≠ 0 := by
  refine ⟨0, longHop, longHop_first_response_zero, ?_⟩
  rw [longHop_pair_response]
  norm_num

end PairLocalityIndependent
end NCG
