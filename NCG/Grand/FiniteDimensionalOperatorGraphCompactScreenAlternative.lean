/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteDimensionalUniformGraphScreenAlternative
import NCG.Grand.OperatorGraphResolventCompactScreenAlternative

/-!
# Finite-cutoff operator-graph compact-screen alternative

For finite-dimensional cutoff carriers, the canonical weak-resolvent graph maps are stagewise
compact automatically. The operator-graph compact-screen alternative therefore needs no separate
stage compactness premise: compact screens yield either collective compactness of the physical
resolvents or the exact cofinal graph-mass-escape witness.
-/

open Filter Topology

noncomputable section

namespace NCG.VaryingHilbert.System

universe u v w z z'

variable {K : Type u} [RCLike K]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H]
  [CompleteSpace H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace K (Hn n)]
  [∀ n, FiniteDimensional K (Hn n)]
variable {F : Type z} [NormedAddCommGroup F] [InnerProductSpace K F]
  [CompleteSpace F]
variable {Fn : ℕ → Type z'}
variable [∀ n, NormedAddCommGroup (Fn n)] [∀ n, InnerProductSpace K (Fn n)]

/-- Exact compactness-or-mass-escape alternative for canonical operator graph maps at
finite-dimensional cutoffs. -/
theorem operatorGraphResolvent_collectivelyCompact_or_massEscape_of_finiteDimensional
    (J : System (K := K) (H := H) (Hn := Hn))
    (L : System (K := K) (H := WithLp 2 (H × F))
      (Hn := fun n ↦ WithLp 2 (Hn n × Fn n)))
    (Dn : ∀ n, Submodule K (Hn n))
    (An : ∀ n, Dn n →ₗ[K] Fn n)
    (Rn : ∀ n, Hn n →L[K] Hn n)
    (lam : ℝ) (hlam : 0 < lam)
    (hEquation : ∀ n (f : Hn n),
      OperatorGraphResolventEquation (Dn n) (An n) lam f (Rn n f))
    (screen : ℕ → WithLp 2 (H × F) →L[K] WithLp 2 (H × F))
    (hcompact : ∀ cutoff, IsCompactOperator (screen cutoff))
    (hfst : ∀ n y, J.embedding n y.fst = (L.embedding n y).fst) :
    J.CollectivelyCompact Rn ∨
      ∃ ε > 0, ∃ radius cutoff : ℕ → ℕ,
        ∃ f : ∀ j, Hn (cutoff j),
          Tendsto radius atTop atTop ∧ Tendsto cutoff atTop atTop ∧
          ∀ j, ‖f j‖ ≤ 1 ∧
            ε ≤ ‖L.embedding (cutoff j)
                (operatorGraphResolventHilbertGraph
                  (Dn (cutoff j)) (An (cutoff j)) (Rn (cutoff j))
                  lam hlam (hEquation (cutoff j)) (f j)) -
              screen (radius j)
                (L.embedding (cutoff j)
                  (operatorGraphResolventHilbertGraph
                    (Dn (cutoff j)) (An (cutoff j)) (Rn (cutoff j))
                    lam hlam (hEquation (cutoff j)) (f j)))‖ := by
  apply J.operatorGraphResolvent_collectivelyCompact_or_massEscape
    L Dn An Rn lam hlam hEquation screen
  · intro n
    letI : ProperSpace (Hn n) :=
      FiniteDimensional.proper_rclike K (Hn n)
    exact isCompactOperator_of_locallyCompactSpace_rng _
  · exact hcompact
  · exact hfst

end NCG.VaryingHilbert.System
