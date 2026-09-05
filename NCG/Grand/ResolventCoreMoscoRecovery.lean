/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.DiagonalMoscoRecovery
import NCG.Grand.ResolventEnvelopeConvergence

/-!
# Mosco recovery from a resolvent core

Strong resolvent convergence gives recovery sequences on the range of the limit resolvent.  If
such resolvent images approximate an arbitrary vector both strongly and in form energy, diagonal
selection promotes those range recoveries to a recovery sequence for that vector.
-/

open Filter Topology

noncomputable section

namespace NCG.VaryingHilbert.System

universe u v w

variable {K : Type u} [RCLike K]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace K (Hn n)]
variable (J : System (K := K) (H := H) (Hn := Hn))

/-- One energy-core approximation by limit resolvent images yields a full varying-space recovery
sequence under strong resolvent convergence. -/
theorem exists_recovery_of_resolventCore_approximation
    (q : (n : ℕ) → Hn n → ℝ) (qlim : H → ℝ) (lam : ℝ)
    (Tn : ∀ n, Hn n →L[K] Hn n) (T : H →L[K] H)
    (hdense : J.IsAsymptoticallyDense)
    (hT : J.StrongOperatorConverges J Tn T)
    (hstageEnergy : ∀ n (f : Hn n),
      q n (Tn n f) + lam * ‖Tn n f‖ ^ 2 =
        RCLike.re (inner K (Tn n f) f))
    (hlimitEnergy : ∀ f : H,
      qlim (T f) + lam * ‖T f‖ ^ 2 =
        RCLike.re (inner K (T f) f))
    (xlim : H) (source : ℕ → H)
    (hcore : Tendsto (fun m ↦ T (source m)) atTop (𝓝 xlim))
    (hcoreEnergy : Tendsto (fun m ↦ qlim (T (source m))) atTop
      (𝓝 (qlim xlim))) :
    ∃ x : ∀ n, Hn n,
      J.StronglyConverges x xlim ∧
        Tendsto (fun n ↦ q n (x n)) atTop (𝓝 (qlim xlim)) := by
  apply exists_recovery_of_tendsto_approximants J q qlim
    (fun m ↦ T (source m)) xlim hcore hcoreEnergy
  intro m
  exact exists_resolventImage_recovery J q qlim lam Tn T
    hdense hT hstageEnergy hlimitEnergy (source m)

/-- If the range of the limit resolvent is an energy core, strong resolvent convergence supplies
the recovery clause of real Mosco convergence at every limit vector. -/
theorem recovery_of_strongResolvent_of_resolventCore
    (q : (n : ℕ) → Hn n → ℝ) (qlim : H → ℝ) (lam : ℝ)
    (Tn : ∀ n, Hn n →L[K] Hn n) (T : H →L[K] H)
    (hdense : J.IsAsymptoticallyDense)
    (hT : J.StrongOperatorConverges J Tn T)
    (hstageEnergy : ∀ n (f : Hn n),
      q n (Tn n f) + lam * ‖Tn n f‖ ^ 2 =
        RCLike.re (inner K (Tn n f) f))
    (hlimitEnergy : ∀ f : H,
      qlim (T f) + lam * ‖T f‖ ^ 2 =
        RCLike.re (inner K (T f) f))
    (hcore : ∀ xlim : H, ∃ source : ℕ → H,
      Tendsto (fun m ↦ T (source m)) atTop (𝓝 xlim) ∧
        Tendsto (fun m ↦ qlim (T (source m))) atTop (𝓝 (qlim xlim))) :
    ∀ xlim : H, ∃ x : ∀ n, Hn n,
      J.StronglyConverges x xlim ∧
        Tendsto (fun n ↦ q n (x n)) atTop (𝓝 (qlim xlim)) := by
  intro xlim
  obtain ⟨source, hsource, hsourceEnergy⟩ := hcore xlim
  exact exists_recovery_of_resolventCore_approximation J
    q qlim lam Tn T hdense hT hstageEnergy hlimitEnergy
      xlim source hsource hsourceEnergy

end NCG.VaryingHilbert.System
