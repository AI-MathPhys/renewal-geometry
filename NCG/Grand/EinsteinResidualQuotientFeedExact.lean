/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteProjectionAndReturnIdentities

/-!
# Exact Einstein residual quotient and feed alternative

This adds the uniqueness of the descended quotient propagator and makes the
zero-feed/triangular-extension prose of
`thm:SMST-Einstein-residual-quotient` literal.
-/

open Matrix

namespace NCG
namespace FiniteProjectionAndReturnIdentities

/-- The induced residual propagator is the unique map intertwining the
quotient projection with the original propagator. -/
theorem residual_quotient_propagator_unique
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (K : Submodule ℝ V) (P : V →ₗ[ℝ] V) (h : K ≤ K.comap P)
    (L : V ⧸ K →ₗ[ℝ] V ⧸ K)
    (hL : L.comp K.mkQ = K.mkQ.comp P) :
    L = Submodule.mapQ K K P h := by
  apply LinearMap.ext
  intro x
  obtain ⟨v, rfl⟩ := K.mkQ_surjective x
  have hLv := LinearMap.congr_fun hL v
  have hcanonical := LinearMap.congr_fun
    (residual_quotient_propagator K P h) v
  exact hLv.trans hcanonical.symm

/-- Exact finite block alternative.  Invariance of `K` is the vanishing
lower-left block `(1-Q)PQ=0`; the upper-right feed block is the only coupling
left in the triangular decomposition. -/
theorem einstein_feed_alternative_exact
    {n : Type*} [Fintype n] [DecidableEq n]
    (Q P : Matrix n n ℝ) (hQ : Q * Q = Q)
    (hK : (1 - Q) * P * Q = 0) :
    (feedDefect Q P = 0 ↔ Q * P = P * Q)
    ∧ (feedDefect Q P = 0 ↔ Q * P * (1 - Q) = 0)
    ∧ P = Q * P * Q + Q * P * (1 - Q) + (1 - Q) * P * (1 - Q)
    ∧ (feedDefect Q P = 0 →
        P = Q * P * Q + (1 - Q) * P * (1 - Q))
    ∧ (0 < feedDefect Q P → Q * P * (1 - Q) ≠ 0) := by
  have hcomm := feed_zero_iff_commute_iff_complement_invariant Q P hQ hK
  have hfeed : feedDefect Q P = 0 ↔ Q * P * (1 - Q) = 0 := by
    rw [feedDefect, matrixEnergy_eq_zero_iff]
  have hsplit : Q + (1 - Q) = (1 : Matrix n n ℝ) := by module
  have htri :
      P = Q * P * Q + Q * P * (1 - Q) + (1 - Q) * P * (1 - Q) := by
    calc
      P = 1 * P * 1 := by simp
      _ = (Q + (1 - Q)) * P * (Q + (1 - Q)) := by rw [hsplit]
      _ = Q * P * Q + Q * P * (1 - Q) +
          (1 - Q) * P * Q + (1 - Q) * P * (1 - Q) := by
            noncomm_ring
      _ = Q * P * Q + Q * P * (1 - Q) +
          (1 - Q) * P * (1 - Q) := by rw [hK]; module
  refine ⟨hcomm, hfeed, htri, ?_, ?_⟩
  · intro hz
    calc
      P = Q * P * Q + Q * P * (1 - Q) +
          (1 - Q) * P * (1 - Q) := htri
      _ = Q * P * Q + (1 - Q) * P * (1 - Q) := by
        rw [hfeed.mp hz, add_zero]
  · intro hpos hzero
    have hz : feedDefect Q P = 0 := hfeed.mpr hzero
    linarith

end FiniteProjectionAndReturnIdentities
end NCG
