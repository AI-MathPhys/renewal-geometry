/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ENNRealClosedFormResolventMoscoConverse
import NCG.Grand.ENNRealResolventEnvelopeDetermination

/-!
# Closed-form strong-resolvent Mosco converse from envelope duality

This packages the two reusable analytic reductions: shifted Fenchel duality determines the form,
while lower semicontinuity and dense effective domain generate the recovery core automatically.
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

/-- The manuscript-facing converse under the standard closed-form and shifted-duality
hypotheses. -/
theorem ennrealMoscoConverges_of_strongResolvents_of_closedForm_of_duality
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
  apply ennrealMoscoConverges_of_strongResolvents_of_closedForm J
    q qlim Tn T hdense hT hstageFinite hlimitFinite
      hstageEnergy hlimitEnergy hstageMin hlimitMin
  · exact hdual.isDeterminedByENNRealResolventEnvelopes
  · exact hls
  · exact hdom

end NCG.VaryingHilbert.System
