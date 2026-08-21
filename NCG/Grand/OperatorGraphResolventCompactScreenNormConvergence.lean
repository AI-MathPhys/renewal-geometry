/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.OperatorGraphResolventCompactScreenAlternative

/-!
# Compact limit and norm convergence from asymptotic graph screens

This file closes the positive half of the operator-graph screen alternative. Monotone eventual
screen tightness produces collective compactness; symmetric varying-space strong convergence then
gives a compact limiting resolvent and operator-norm convergence of the literal common-carrier
compressions.
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
  [∀ n, CompleteSpace (Hn n)]
variable {F : Type z} [NormedAddCommGroup F] [InnerProductSpace K F]
  [CompleteSpace F]
variable {Fn : ℕ → Type z'}
variable [∀ n, NormedAddCommGroup (Fn n)] [∀ n, InnerProductSpace K (Fn n)]

/-- An asymptotically tight compact graph screen upgrades strong resolvent convergence to a
compact limit and literal operator-norm convergence. -/
theorem operatorGraphResolvent_compactLimit_and_normConvergence_of_uniformGraphScreenTight
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
    (hstage : ∀ n, IsCompactOperator
      (L.embeddedOperator
        (fun m ↦ operatorGraphResolventHilbertGraph
          (Dn m) (An m) (Rn m) lam hlam (hEquation m)) n))
    (hcompact : ∀ cutoff, IsCompactOperator (screen cutoff))
    (htight : NCG.VaryingHilbert.UniformGraphScreenTight
      (fun n f ↦ L.embedding n
        (operatorGraphResolventHilbertGraph
          (Dn n) (An n) (Rn n) lam hlam (hEquation n) f))
      (fun cutoff y ↦ y - screen cutoff y)
      (fun _ f ↦ ‖f‖ ≤ 1))
    (hfst : ∀ n y, J.embedding n y.fst = (L.embedding n y).fst)
    (T : H →L[K] H)
    (hdense : J.IsAsymptoticallyDense)
    (hstrong : J.StrongOperatorConverges J Rn T)
    (hsymm : ∀ n, LinearMap.IsSymmetric (Rn n).toLinearMap)
    (hlimSymm : LinearMap.IsSymmetric T.toLinearMap) :
    IsCompactOperator T ∧
      Tendsto (J.compressedOperator Rn) atTop (𝓝 T) := by
  have hcollective : J.CollectivelyCompact Rn :=
    J.operatorGraphResolvent_collectivelyCompact_of_uniformGraphScreenTight
      L Dn An Rn lam hlam hEquation screen hstage hcompact htight hfst
  have hcompressedCollective := hcollective.compressedOperator J Rn
  have hcompressedStrong : ∀ x : H,
      Tendsto (fun n ↦ J.compressedOperator Rn n x) atTop (𝓝 (T x)) :=
    J.compressedOperator_tendsto Rn T hdense hstrong
  have hTcompact : IsCompactOperator T :=
    hcompressedCollective.isCompactOperator_limit
      (J.compressedOperator Rn) T hcompressedStrong
  exact ⟨hTcompact,
    J.compressedOperator_tendsto_operatorNorm
      Rn T hdense hstrong hcollective hsymm hlimSymm⟩

end NCG.VaryingHilbert.System
