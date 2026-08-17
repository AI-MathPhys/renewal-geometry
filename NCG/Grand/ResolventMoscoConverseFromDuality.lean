/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ResolventMoscoConverse
import NCG.Grand.ResolventEnvelopeDetermination
import NCG.Grand.ResolventEnergyCore

/-!
# Mosco converse from envelope duality and dense resolvent range

This is the bounded-form specialization of the abstract strong-resolvent converse.  Approximate
Fenchel--Moreau duality discharges envelope determination, while continuity of the limit form and
dense range of one resolvent discharge the energy-core hypothesis.
-/

open Filter Topology

noncomputable section

namespace NCG.VaryingHilbert.System

universe u v w

variable {K : Type u} [RCLike K]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H] [CompleteSpace H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace K (Hn n)]
variable (J : System (K := K) (H := H) (Hn := Hn))

/-- Strong resolvents imply real Mosco convergence for a norm-continuous limit form once
shifted-envelope duality and dense range of one limit resolvent are known. -/
theorem realMoscoConverges_of_strongResolvents_of_envelopeDuality_of_denseRange
    (q : (n : ℕ) → Hn n → ℝ) (qlim : H → ℝ)
    (Tn : ℝ → ∀ n, Hn n →L[K] Hn n) (T : ℝ → H →L[K] H)
    (hdense : J.IsAsymptoticallyDense)
    (hT : ∀ (φ : ℕ → ℕ), Tendsto φ atTop atTop →
      ∀ lam, 0 < lam →
        (J.reindex φ).StrongOperatorConverges (J.reindex φ)
          (fun n ↦ Tn lam (φ n)) (T lam))
    (hstageEnergy : ∀ lam, 0 < lam → ∀ n (f : Hn n),
      q n (Tn lam n f) + lam * ‖Tn lam n f‖ ^ 2 =
        RCLike.re (inner K (Tn lam n f) f))
    (hlimitEnergy : ∀ lam, 0 < lam → ∀ f : H,
      qlim (T lam f) + lam * ‖T lam f‖ ^ 2 =
        RCLike.re (inner K (T lam f) f))
    (hstageMin : ∀ lam, 0 < lam → ∀ n (f z : Hn n),
      resolventObjective (K := K) (q n) lam f (Tn lam n f) ≤
        resolventObjective (K := K) (q n) lam f z)
    (hdual : HasResolventEnvelopeDuality (K := K) qlim T)
    (hqCobounded : ∀ (φ : ℕ → ℕ), Tendsto φ atTop atTop →
      ∀ (x : ∀ n, Hn (φ n)) (xlim : H),
        (J.reindex φ).WeaklyConverges x xlim →
          IsCoboundedUnder (· ≥ ·) atTop (fun n ↦ q (φ n) (x n)))
    (lam0 : ℝ) (hlam0 : 0 < lam0)
    (hqlimContinuous : Continuous qlim) (hDenseRange : DenseRange (T lam0)) :
    J.RealMoscoConverges q qlim := by
  apply realMoscoConverges_of_strongResolvents J q qlim Tn T hdense hT
    hstageEnergy hlimitEnergy hstageMin
    hdual.isDeterminedByResolventEnvelopes hqCobounded lam0 hlam0
  exact resolventEnergyCore_of_denseRange_of_continuous
    (K := K) qlim (T lam0) hDenseRange hqlimContinuous

end NCG.VaryingHilbert.System
