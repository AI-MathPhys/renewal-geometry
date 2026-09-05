/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ENNRealClosedFormMoscoConverseFromOneShift
import NCG.Grand.ENNRealResolventEnvelopeDetermination

/-!
# Closed-form ENNReal Mosco converse from one shift and duality

This manuscript-facing wrapper combines one-shift propagation with shifted ENNReal envelope
duality and automatic Yosida recovery.
-/

open Set

noncomputable section

namespace NCG.VaryingHilbert.System

universe u v w

variable {K : Type u} [RCLike K]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H] [CompleteSpace H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace K (Hn n)]
variable (J : System (K := K) (H := H) (Hn := Hn))

/-- One strongly convergent resolvent shift, the second resolvent identities, and shifted
ENNReal envelope duality imply genuine ENNReal Mosco convergence for closed densely defined
forms. -/
theorem ennrealMoscoConverges_of_oneStrongResolvent_of_closedForm_of_duality
    (q : (n : ℕ) → Hn n → ENNReal) (qlim : H → ENNReal)
    (Tn : ℝ → ∀ n, Hn n →L[K] Hn n) (T : ℝ → H →L[K] H)
    (hdense : J.IsAsymptoticallyDense)
    (lam0 : ℝ)
    (hT0 : J.StrongOperatorConverges J (Tn lam0) (T lam0))
    (hbound : ∀ lam, ∃ C : ℝ, ∀ n, ‖Tn lam n‖ ≤ C)
    (hstageResolvent : ∀ a b n,
      Tn b n - Tn a n =
        (((a - b : ℝ) : K)) • ((Tn b n).comp (Tn a n)))
    (hlimitResolvent : ∀ a b,
      T a - T b = (((b - a : ℝ) : K)) • ((T a).comp (T b)))
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
    (hlimitMin : ∀ lam, 0 < lam → ∀ (f z : H),
      qlim z ≠ (⊤ : ENNReal) →
        resolventObjective (K := K) (fun x ↦ (qlim x).toReal)
            lam f (T lam f) ≤
          resolventObjective (K := K) (fun x ↦ (qlim x).toReal) lam f z)
    (hdual : HasENNRealResolventEnvelopeDuality (K := K) qlim
      (fun lam f ↦ resolventPairingEnvelope (K := K) (T lam) f))
    (hls : LowerSemicontinuous qlim)
    (hdom : Dense {z : H | qlim z ≠ (⊤ : ENNReal)}) :
    J.MoscoConverges q qlim := by
  exact ennrealMoscoConverges_of_oneStrongResolvent_of_closedForm J
    q qlim Tn T hdense lam0 hT0 hbound hstageResolvent hlimitResolvent
    hstageFinite hlimitFinite hstageEnergy hlimitEnergy hstageMin hlimitMin
    hdual.isDeterminedByENNRealResolventEnvelopes hls hdom

end NCG.VaryingHilbert.System
