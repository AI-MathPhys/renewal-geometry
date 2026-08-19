/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CollectivelyCompactResolventShiftPropagation
import NCG.Grand.PositiveRealResolventShiftPropagation
import NCG.Grand.CompressedOperatorNormConvergence

/-!
# One-shift collective compactness upgrades every positive resolvent shift

This compiler starts with strong convergence and collective compactness at one positive shift.
The two orientations of the resolvent identity propagate, respectively, strong convergence and
collective compactness.  Symmetry and asymptotic density then yield operator-norm convergence of
the literal common-carrier compressions at every positive shift.
-/

open Filter Topology

noncomputable section

namespace NCG.VaryingHilbert.System

universe u v w

variable {K : Type u} [RCLike K]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H]
  [CompleteSpace H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace K (Hn n)]
  [∀ n, CompleteSpace (Hn n)]

/-- Strong convergence and collective compactness at one positive real resolvent shift imply
operator-norm convergence of the compressed resolvents at every positive shift. -/
theorem compressedResolvents_tendsto_operatorNorm_allPositive_of_oneShift
    (J : System (K := K) (H := H) (Hn := Hn))
    (Rn : ℝ → ∀ n, Hn n →L[K] Hn n) (R : ℝ → H →L[K] H)
    (a : ℝ) (haPos : 0 < a)
    (hdense : J.IsAsymptoticallyDense)
    (haStrong : J.StrongOperatorConverges J (Rn a) (R a))
    (haCompact : J.CollectivelyCompact (Rn a))
    (hbound : ∀ b, 0 < b → ∃ C : ℝ, ∀ n, ‖Rn b n‖ ≤ C)
    (hstage : ∀ a b, 0 < a → 0 < b → ∀ n,
      Rn b n - Rn a n = (((a - b : ℝ) : K)) •
        ((Rn b n).comp (Rn a n)))
    (hstageReversed : ∀ b, 0 < b → ∀ n,
      Rn b n = Rn a n + (((a - b : ℝ) : K)) •
        ((Rn a n).comp (Rn b n)))
    (hlimit : ∀ a b, 0 < a → 0 < b →
      R a - R b = (((b - a : ℝ) : K)) • ((R a).comp (R b)))
    (hsymm : ∀ b, 0 < b → ∀ n,
      LinearMap.IsSymmetric (Rn b n).toLinearMap)
    (hlimSymm : ∀ b, 0 < b → LinearMap.IsSymmetric (R b).toLinearMap) :
    ∀ b, 0 < b →
      IsCompactOperator (R b) ∧
        Tendsto (J.compressedOperator (Rn b)) atTop (𝓝 (R b)) := by
  have hallStrong : ∀ b, 0 < b →
      J.StrongOperatorConverges J (Rn b) (R b) :=
    haStrong.allPositiveRealResolventShifts J Rn R a haPos hdense
      hbound hstage hlimit
  have hallCompact : ∀ b, 0 < b → J.CollectivelyCompact (Rn b) :=
    haCompact.allPositiveRealResolventShifts J Rn a hbound hstageReversed
  intro b hbPos
  have hbCompact : J.CollectivelyCompact (Rn b) := hallCompact b hbPos
  have hcompressedStrong :
      ∀ x : H, Tendsto (fun n ↦ J.compressedOperator (Rn b) n x)
        atTop (𝓝 (R b x)) :=
    J.compressedOperator_tendsto (Rn b) (R b) hdense (hallStrong b hbPos)
  have hbLimitCompact : IsCompactOperator (R b) :=
    (hbCompact.compressedOperator J (Rn b)).isCompactOperator_limit
      (J.compressedOperator (Rn b)) (R b) hcompressedStrong
  exact ⟨hbLimitCompact, J.compressedOperator_tendsto_operatorNorm
    (Rn b) (R b) hdense (hallStrong b hbPos) hbCompact
    (hsymm b hbPos) (hlimSymm b hbPos)⟩

end NCG.VaryingHilbert.System
