/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GTProtectedAngle

/-!
# Protected-angle localizer for an assembled packet

The arithmetic carrier is instantiated explicitly: a fixed predictor removes
the predictable parts of the total and phase sources before the localizer and
readout are formed.
-/

open scoped InnerProductSpace

namespace NCG
namespace AssembledProtectedAngleLocalizerExact

/-- Exact protected-angle corollary with the residual sources explicitly
constructed from the independently fixed predictor. -/
theorem assembled_packet_protected_angle_localizer
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (P : V →L[ℝ] V) (t p : V) (η pf f : ℝ)
    (hη : 0 ≤ η)
    (ht : (1 - P) t ≠ 0) (hp : (1 - P) p ≠ 0)
    (hf : f = pf + ⟪(1 - P) t, (1 - P) p⟫_ℝ) :
    ((∀ x y : ℝ,
      0 ≤ η * ‖(1 - P) t‖ ^ 2 * x ^ 2
        - 2 * ⟪(1 - P) t, (1 - P) p⟫_ℝ * x * y
        + η * ‖(1 - P) p‖ ^ 2 * y ^ 2) ↔
      |⟪(1 - P) t, (1 - P) p⟫_ℝ| ≤
        η * (‖(1 - P) t‖ * ‖(1 - P) p‖)) ∧
    (|⟪(1 - P) t, (1 - P) p⟫_ℝ| ≤
        η * (‖(1 - P) t‖ * ‖(1 - P) p‖) →
      |f| ≤ |pf| + η * (‖(1 - P) t‖ * ‖(1 - P) p‖)) := by
  have hpacket := gt_protected_angle ((1 - P) t) ((1 - P) p) η hη ht hp
  refine ⟨hpacket.1, ?_⟩
  intro hangle
  exact hpacket.2 f pf |pf| hf (le_rfl) hangle

end AssembledProtectedAngleLocalizerExact
end NCG
