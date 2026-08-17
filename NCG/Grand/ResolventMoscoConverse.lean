/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ResolventCoreMoscoRecovery
import NCG.Grand.ResolventEnvelopeFormLiminf
import NCG.Grand.VaryingHilbertWeakBoundedness

/-!
# Converse from strong resolvents to real Mosco convergence

This file assembles the two Moreau-envelope halves.  Cofinal strong resolvent convergence and an
envelope representation give the weak liminf clause; an energy-dense limit resolvent range and
diagonal selection give recovery.  The result is a complete real-valued Mosco record under
explicit analytic hypotheses.
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

omit [CompleteSpace H] in
/-- Asymptotic density passes to every cofinal reindexing. -/
theorem IsAsymptoticallyDense.reindex
    (hdense : J.IsAsymptoticallyDense)
    (φ : ℕ → ℕ) (hφ : Tendsto φ atTop atTop) :
    (J.reindex φ).IsAsymptoticallyDense := by
  intro xlim
  obtain ⟨x, hx⟩ := hdense xlim
  exact ⟨fun n ↦ x (φ n), hx.reindex J hφ⟩

/-- Cofinal strong resolvent convergence, envelope determination of the limit form, and an
energy-dense resolvent core imply real Mosco convergence.  Banach--Steinhaus supplies uniform
weak bounds automatically; real-liminf coboundedness remains explicit because it depends on the
form's energy bounds. -/
theorem realMoscoConverges_of_strongResolvents
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
    (hdet : IsDeterminedByResolventEnvelopes (K := K) qlim T)
    (hqCobounded : ∀ (φ : ℕ → ℕ), Tendsto φ atTop atTop →
      ∀ (x : ∀ n, Hn (φ n)) (xlim : H),
        (J.reindex φ).WeaklyConverges x xlim →
          IsCoboundedUnder (· ≥ ·) atTop (fun n ↦ q (φ n) (x n)))
    (lam0 : ℝ) (hlam0 : 0 < lam0)
    (hcore : ∀ xlim : H, ∃ source : ℕ → H,
      Tendsto (fun m ↦ T lam0 (source m)) atTop (𝓝 xlim) ∧
        Tendsto (fun m ↦ qlim (T lam0 (source m))) atTop
          (𝓝 (qlim xlim))) :
    J.RealMoscoConverges q qlim where
  liminf_le := by
    intro φ hφ x xlim hx
    obtain ⟨C, hC, hxBound⟩ := hx.exists_uniform_norm_bound (J.reindex φ)
    apply formValue_le_liminf_of_strongResolvents (J.reindex φ)
      (fun n z ↦ q (φ n) z) qlim
      (fun lam n ↦ Tn lam (φ n)) T
      (hdense.reindex J φ hφ)
      (fun lam hlam ↦ hT φ hφ lam hlam)
      (fun lam hlam n f ↦ hstageEnergy lam hlam (φ n) f)
      hlimitEnergy
      (fun lam hlam n f z ↦ hstageMin lam hlam (φ n) f z)
      hdet x xlim C hC hx hxBound
      (hqCobounded φ hφ x xlim hx)
  recovery := by
    apply recovery_of_strongResolvent_of_resolventCore J
      q qlim lam0 (Tn lam0) (T lam0) hdense
      (hT id tendsto_id lam0 hlam0)
      (hstageEnergy lam0 hlam0) (hlimitEnergy lam0 hlam0)
    exact hcore

end NCG.VaryingHilbert.System
