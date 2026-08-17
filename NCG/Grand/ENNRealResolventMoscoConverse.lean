/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ENNRealResolventCoreMoscoRecovery
import NCG.Grand.VaryingHilbertWeakBoundedness

/-!
# Converse from strong resolvents to extended-valued Mosco convergence

This file assembles the coboundedness-free ENNReal envelope lower bound and the ENNReal
resolvent-core recovery theorem.  It produces the genuine extended-valued `MoscoConverges`
record used by the manuscript's closed forms.
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

/-- Strong resolvent convergence, canonical extended envelope determination, and an ENNReal
energy-dense resolvent core imply genuine extended-valued Mosco convergence.

Weak-sequence norm bounds are automatic by Banach--Steinhaus, and ENNReal liminf requires no
separate coboundedness hypothesis. -/
theorem ennrealMoscoConverges_of_strongResolvents
    (q : (n : ℕ) → Hn n → ENNReal) (qlim : H → ENNReal)
    (Tn : ℝ → ∀ n, Hn n →L[K] Hn n) (T : ℝ → H →L[K] H)
    (hdense : J.IsAsymptoticallyDense)
    (hT : ∀ lam, 0 < lam → J.StrongOperatorConverges J (Tn lam) (T lam))
    (hstageFinite : ∀ lam, 0 < lam → ∀ n (f : Hn n),
      q n (Tn lam n f) ≠ (⊤ : ENNReal))
    (hlimitFinite : ∀ lam, 0 < lam → ∀ f : H,
      qlim (T lam f) ≠ (⊤ : ENNReal))
    (hstageEnergy : ∀ lam, 0 < lam → ∀ n (f : Hn n),
      (q n (Tn lam n f)).toReal + lam * ‖Tn lam n f‖ ^ 2 =
        RCLike.re (inner K (Tn lam n f) f))
    (hlimitEnergy : ∀ lam, 0 < lam → ∀ f : H,
      (qlim (T lam f)).toReal + lam * ‖T lam f‖ ^ 2 =
        RCLike.re (inner K (T lam f) f))
    (hstageMin : ∀ lam, 0 < lam → ∀ n (f z : Hn n),
      q n z ≠ (⊤ : ENNReal) →
        resolventObjective (K := K) (fun x ↦ (q n x).toReal)
            lam f (Tn lam n f) ≤
          resolventObjective (K := K) (fun x ↦ (q n x).toReal) lam f z)
    (hdet : IsDeterminedByENNRealResolventEnvelopes (K := K) qlim
      (fun lam f ↦ resolventPairingEnvelope (K := K) (T lam) f))
    (lam0 : ℝ) (hlam0 : 0 < lam0)
    (hcore : ∀ xlim : H, ∃ source : ℕ → H,
      Tendsto (fun m ↦ T lam0 (source m)) atTop (𝓝 xlim) ∧
        Tendsto (fun m ↦ qlim (T lam0 (source m))) atTop (𝓝 (qlim xlim))) :
    J.MoscoConverges q qlim where
  liminf_le := by
    intro x xlim hx
    obtain ⟨C, hC, hxBound⟩ := hx.exists_uniform_norm_bound J
    exact ennrealFormValue_le_liminf_of_strongResolvents J q qlim Tn T
      hdense hT hstageEnergy hstageMin hdet
        x xlim C hC hx hxBound
  recovery := by
    intro xlim
    obtain ⟨x, hx, henergy⟩ :=
      ennrealRecovery_of_strongResolvent_of_resolventCore J
        q qlim lam0 (Tn lam0) (T lam0) hdense (hT lam0 hlam0)
        (hstageFinite lam0 hlam0) (hlimitFinite lam0 hlam0)
        (hstageEnergy lam0 hlam0) (hlimitEnergy lam0 hlam0) hcore xlim
    exact ⟨x, hx, henergy.limsup_eq.le⟩

end NCG.VaryingHilbert.System
