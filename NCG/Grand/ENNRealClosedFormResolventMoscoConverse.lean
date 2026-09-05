/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ENNRealYosidaApproximation
import NCG.Grand.ENNRealVaryingCoreMoscoRecovery
import NCG.Grand.ENNRealResolventMoscoConverse

/-!
# Strong-resolvent Mosco converse for closed densely defined forms

Lower semicontinuity and density of the finite-energy domain automatically generate the recovery
core by large-shift Yosida approximation, removing the explicit model-specific core hypothesis.
-/

open Filter Topology Set

noncomputable section

namespace NCG.VaryingHilbert.System

universe u v w

variable {K : Type u} [RCLike K]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H] [CompleteSpace H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace K (Hn n)]
variable (J : System (K := K) (H := H) (Hn := Hn))

/-- Strong resolvent convergence implies genuine ENNReal Mosco convergence for a
lower-semicontinuous limit form with dense effective domain. -/
theorem ennrealMoscoConverges_of_strongResolvents_of_closedForm
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
    (hdet : IsDeterminedByENNRealResolventEnvelopes (K := K) qlim
      (fun lam f ↦ resolventPairingEnvelope (K := K) (T lam) f))
    (hls : LowerSemicontinuous qlim)
    (hdom : Dense {z : H | qlim z ≠ (⊤ : ENNReal)}) :
    J.MoscoConverges q qlim where
  liminf_le := by
    intro x xlim hx
    obtain ⟨C, hC, hxBound⟩ := hx.exists_uniform_norm_bound J
    exact ennrealFormValue_le_liminf_of_strongResolvents J q qlim Tn T
      hdense hT hstageEnergy hstageMin hdet x xlim C hC hx hxBound
  recovery := by
    intro xlim
    have hcore := largeShift_resolventEnergyCore qlim T hls hdom
      hlimitFinite hlimitMin
    obtain ⟨x, hx, henergy⟩ :=
      ennrealRecovery_of_strongResolvents_of_varyingCore J
        q qlim Tn T hdense hT hstageFinite hlimitFinite
          hstageEnergy hlimitEnergy hcore xlim
    exact ⟨x, hx, henergy.limsup_eq.le⟩

end NCG.VaryingHilbert.System
