/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ENNRealResolventEnvelopeLiminf
import NCG.Grand.EMetricValuedDiagonalRecovery

/-!
# Extended-valued Mosco recovery from a resolvent energy core

Strong resolvent convergence gives exact ENNReal energy recovery on every limit resolvent image.
An energy-dense sequence of such images and metric-valued diagonal selection then give recovery
at an arbitrary limit vector.
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

/-- One limit resolvent image has a strongly convergent stage recovery with exact extended energy
convergence. -/
theorem exists_ennreal_resolventImage_recovery
    (q : (n : ℕ) → Hn n → ENNReal) (qlim : H → ENNReal) (lam : ℝ)
    (Tn : ∀ n, Hn n →L[K] Hn n) (T : H →L[K] H)
    (hdense : J.IsAsymptoticallyDense)
    (hT : J.StrongOperatorConverges J Tn T)
    (hstageFinite : ∀ n (f : Hn n), q n (Tn n f) ≠ (⊤ : ENNReal))
    (hlimitFinite : ∀ f : H, qlim (T f) ≠ (⊤ : ENNReal))
    (hstageEnergy : ∀ n (f : Hn n),
      (q n (Tn n f)).toReal + lam * ‖Tn n f‖ ^ 2 =
        RCLike.re (inner K (Tn n f) f))
    (hlimitEnergy : ∀ f : H,
      (qlim (T f)).toReal + lam * ‖T f‖ ^ 2 =
        RCLike.re (inner K (T f) f))
    (source : H) :
    ∃ x : ∀ n, Hn n,
      J.StronglyConverges x (T source) ∧
        Tendsto (fun n ↦ q n (x n)) atTop (𝓝 (qlim (T source))) := by
  obtain ⟨f, hf⟩ := hdense source
  refine ⟨fun n ↦ Tn n (f n), hT f source hf, ?_⟩
  exact ennrealResolventFormValue_tendsto_of_strongOperatorConverges J
    q qlim lam Tn T hT hstageFinite hlimitFinite hstageEnergy hlimitEnergy
      f source hf

/-- One ENNReal energy-core approximation by limit resolvent images yields a full recovery
sequence after simultaneous diagonal selection. -/
theorem exists_ennreal_recovery_of_resolventCore_approximation
    (q : (n : ℕ) → Hn n → ENNReal) (qlim : H → ENNReal) (lam : ℝ)
    (Tn : ∀ n, Hn n →L[K] Hn n) (T : H →L[K] H)
    (hdense : J.IsAsymptoticallyDense)
    (hT : J.StrongOperatorConverges J Tn T)
    (hstageFinite : ∀ n (f : Hn n), q n (Tn n f) ≠ (⊤ : ENNReal))
    (hlimitFinite : ∀ f : H, qlim (T f) ≠ (⊤ : ENNReal))
    (hstageEnergy : ∀ n (f : Hn n),
      (q n (Tn n f)).toReal + lam * ‖Tn n f‖ ^ 2 =
        RCLike.re (inner K (Tn n f) f))
    (hlimitEnergy : ∀ f : H,
      (qlim (T f)).toReal + lam * ‖T f‖ ^ 2 =
        RCLike.re (inner K (T f) f))
    (xlim : H) (source : ℕ → H)
    (hcore : Tendsto (fun m ↦ T (source m)) atTop (𝓝 xlim))
    (hcoreEnergy : Tendsto (fun m ↦ qlim (T (source m))) atTop
      (𝓝 (qlim xlim))) :
    ∃ x : ∀ n, Hn n,
      J.StronglyConverges x xlim ∧
        Tendsto (fun n ↦ q n (x n)) atTop (𝓝 (qlim xlim)) := by
  apply exists_recovery_of_emetricValued_tendsto_approximants J q qlim
    (fun m ↦ T (source m)) xlim hcore hcoreEnergy
  intro m
  exact exists_ennreal_resolventImage_recovery J q qlim lam Tn T
    hdense hT hstageFinite hlimitFinite hstageEnergy hlimitEnergy (source m)

/-- An ENNReal energy-dense limit resolvent range supplies the full recovery clause. -/
theorem ennrealRecovery_of_strongResolvent_of_resolventCore
    (q : (n : ℕ) → Hn n → ENNReal) (qlim : H → ENNReal) (lam : ℝ)
    (Tn : ∀ n, Hn n →L[K] Hn n) (T : H →L[K] H)
    (hdense : J.IsAsymptoticallyDense)
    (hT : J.StrongOperatorConverges J Tn T)
    (hstageFinite : ∀ n (f : Hn n), q n (Tn n f) ≠ (⊤ : ENNReal))
    (hlimitFinite : ∀ f : H, qlim (T f) ≠ (⊤ : ENNReal))
    (hstageEnergy : ∀ n (f : Hn n),
      (q n (Tn n f)).toReal + lam * ‖Tn n f‖ ^ 2 =
        RCLike.re (inner K (Tn n f) f))
    (hlimitEnergy : ∀ f : H,
      (qlim (T f)).toReal + lam * ‖T f‖ ^ 2 =
        RCLike.re (inner K (T f) f))
    (hcore : ∀ xlim : H, ∃ source : ℕ → H,
      Tendsto (fun m ↦ T (source m)) atTop (𝓝 xlim) ∧
        Tendsto (fun m ↦ qlim (T (source m))) atTop (𝓝 (qlim xlim))) :
    ∀ xlim : H, ∃ x : ∀ n, Hn n,
      J.StronglyConverges x xlim ∧
        Tendsto (fun n ↦ q n (x n)) atTop (𝓝 (qlim xlim)) := by
  intro xlim
  obtain ⟨source, hsource, hsourceEnergy⟩ := hcore xlim
  exact exists_ennreal_recovery_of_resolventCore_approximation J
    q qlim lam Tn T hdense hT hstageFinite hlimitFinite
      hstageEnergy hlimitEnergy xlim source hsource hsourceEnergy

end NCG.VaryingHilbert.System
