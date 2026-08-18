/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ENNRealResolventCoreMoscoRecovery

/-!
# ENNReal Mosco recovery from a varying-shift resolvent core

This variant consumes the automatic large-shift Yosida core of a closed densely defined form.
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

/-- A varying-shift ENNReal resolvent energy core supplies the full recovery clause. -/
theorem ennrealRecovery_of_strongResolvents_of_varyingCore
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
    (hcore : ∀ xlim : H, ∃ source : ℕ → H,
      Tendsto (fun m : ℕ ↦ T ((m : ℝ) + 1) (source m)) atTop (𝓝 xlim) ∧
        Tendsto (fun m : ℕ ↦ qlim (T ((m : ℝ) + 1) (source m)))
          atTop (𝓝 (qlim xlim))) :
    ∀ xlim : H, ∃ x : ∀ n, Hn n,
      J.StronglyConverges x xlim ∧
        Tendsto (fun n ↦ q n (x n)) atTop (𝓝 (qlim xlim)) := by
  intro xlim
  obtain ⟨source, hsource, hsourceEnergy⟩ := hcore xlim
  apply exists_recovery_of_topologicalValued_tendsto_approximants J q qlim
    (fun m : ℕ ↦ T ((m : ℝ) + 1) (source m)) xlim hsource hsourceEnergy
  intro m
  have hlam : 0 < (m : ℝ) + 1 := by positivity
  exact exists_ennreal_resolventImage_recovery J q qlim ((m : ℝ) + 1)
    (Tn ((m : ℝ) + 1)) (T ((m : ℝ) + 1)) hdense
    (hT ((m : ℝ) + 1) hlam)
    (hstageFinite ((m : ℝ) + 1) hlam)
    (hlimitFinite ((m : ℝ) + 1) hlam)
    (hstageEnergy ((m : ℝ) + 1) hlam)
    (hlimitEnergy ((m : ℝ) + 1) hlam) (source m)

end NCG.VaryingHilbert.System
