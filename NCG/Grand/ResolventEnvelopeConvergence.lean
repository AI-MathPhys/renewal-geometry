/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.VaryingHilbertResolventObjective

/-!
# Moreau-type resolvent envelope convergence

For a quadratic form, the Euler identity at its resolvent minimizer rewrites the minimized
objective as minus the source--resolvent pairing.  Consequently strong resolvent convergence
implies convergence of these envelopes and of the form energies along resolvent images.  These
are the basic ingredients for the converse resolvent-to-Mosco implication.
-/

open Filter Topology

noncomputable section

namespace NCG.VaryingHilbert

universe u v

variable {K : Type u} [RCLike K]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace K E]

/-- The resolvent objective evaluated at a specified resolvent operator.  When that operator is
the minimizer, this is the Moreau-type envelope of the quadratic form. -/
def resolventEnvelope
    (q : E → ℝ) (lam : ℝ) (T : E →L[K] E) (f : E) : ℝ :=
  resolventObjective (K := K) q lam f (T f)

/-- The quadratic Euler identity rewrites the minimized resolvent objective as a pairing. -/
theorem resolventEnvelope_eq_neg_re_inner
    (q : E → ℝ) (lam : ℝ) (T : E →L[K] E) (f : E)
    (henergy : q (T f) + lam * ‖T f‖ ^ 2 =
      RCLike.re (inner K (T f) f)) :
    resolventEnvelope (K := K) q lam T f =
      -RCLike.re (inner K (T f) f) := by
  simp only [resolventEnvelope, resolventObjective]
  linarith

namespace System

universe w

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace K (Hn n)]
variable (J : System (K := K) (H := H) (Hn := Hn))

/-- Strong resolvent convergence implies convergence of the minimized quadratic objectives once
the stage and limit resolvents satisfy their Euler energy identities. -/
theorem resolventEnvelope_tendsto_of_strongOperatorConverges
    (q : (n : ℕ) → Hn n → ℝ) (qlim : H → ℝ) (lam : ℝ)
    (Tn : ∀ n, Hn n →L[K] Hn n) (T : H →L[K] H)
    (hT : J.StrongOperatorConverges J Tn T)
    (hstageEnergy : ∀ n (f : Hn n),
      q n (Tn n f) + lam * ‖Tn n f‖ ^ 2 =
        RCLike.re (inner K (Tn n f) f))
    (hlimitEnergy : ∀ f : H,
      qlim (T f) + lam * ‖T f‖ ^ 2 =
        RCLike.re (inner K (T f) f))
    (f : ∀ n, Hn n) (flim : H) (hf : J.StronglyConverges f flim) :
    Tendsto
      (fun n ↦ resolventEnvelope (K := K) (q n) lam (Tn n) (f n)) atTop
      (𝓝 (resolventEnvelope (K := K) qlim lam T flim)) := by
  have hTf := hT f flim hf
  have hinner : Tendsto
      (fun n ↦ inner K (J.embedding n (Tn n (f n))) (J.embedding n (f n))) atTop
      (𝓝 (inner K (T flim) flim)) := hTf.inner hf
  have hinnerRe : Tendsto
      (fun n ↦ RCLike.re (inner K (Tn n (f n)) (f n))) atTop
      (𝓝 (RCLike.re (inner K (T flim) flim))) := by
    have hre := RCLike.reCLM.continuous.continuousAt.tendsto.comp hinner
    simpa only [Function.comp_def, LinearIsometry.inner_map_map,
      RCLike.reCLM_apply] using hre
  have hstageRewrite :
      (fun n ↦ resolventEnvelope (K := K) (q n) lam (Tn n) (f n)) =
        (fun n ↦ -RCLike.re (inner K (Tn n (f n)) (f n))) := by
    funext n
    exact resolventEnvelope_eq_neg_re_inner
      (q n) lam (Tn n) (f n) (hstageEnergy n (f n))
  rw [hstageRewrite, resolventEnvelope_eq_neg_re_inner
    qlim lam T flim (hlimitEnergy flim)]
  exact hinnerRe.neg

/-- Strong resolvent convergence also forces convergence of form energies along the moving
resolvent images.  This is the graph-energy component used in Moreau-envelope proofs of the
converse Mosco implication. -/
theorem resolventFormValue_tendsto_of_strongOperatorConverges
    (q : (n : ℕ) → Hn n → ℝ) (qlim : H → ℝ) (lam : ℝ)
    (Tn : ∀ n, Hn n →L[K] Hn n) (T : H →L[K] H)
    (hT : J.StrongOperatorConverges J Tn T)
    (hstageEnergy : ∀ n (f : Hn n),
      q n (Tn n f) + lam * ‖Tn n f‖ ^ 2 =
        RCLike.re (inner K (Tn n f) f))
    (hlimitEnergy : ∀ f : H,
      qlim (T f) + lam * ‖T f‖ ^ 2 =
        RCLike.re (inner K (T f) f))
    (f : ∀ n, Hn n) (flim : H) (hf : J.StronglyConverges f flim) :
    Tendsto (fun n ↦ q n (Tn n (f n))) atTop (𝓝 (qlim (T flim))) := by
  have hTf := hT f flim hf
  have hinner : Tendsto
      (fun n ↦ inner K (J.embedding n (Tn n (f n))) (J.embedding n (f n))) atTop
      (𝓝 (inner K (T flim) flim)) := hTf.inner hf
  have hinnerRe : Tendsto
      (fun n ↦ RCLike.re (inner K (Tn n (f n)) (f n))) atTop
      (𝓝 (RCLike.re (inner K (T flim) flim))) := by
    have hre := RCLike.reCLM.continuous.continuousAt.tendsto.comp hinner
    simpa only [Function.comp_def, LinearIsometry.inner_map_map,
      RCLike.reCLM_apply] using hre
  have hnorm : Tendsto (fun n ↦ ‖Tn n (f n)‖) atTop (𝓝 ‖T flim‖) := by
    simpa [StronglyConverges] using hTf.norm
  have hscaled : Tendsto
      (fun n ↦ lam * ‖Tn n (f n)‖ ^ 2) atTop
      (𝓝 (lam * ‖T flim‖ ^ 2)) :=
    tendsto_const_nhds.mul (hnorm.pow 2)
  have hraw : Tendsto
      (fun n ↦ RCLike.re (inner K (Tn n (f n)) (f n)) -
        lam * ‖Tn n (f n)‖ ^ 2) atTop
      (𝓝 (RCLike.re (inner K (T flim) flim) - lam * ‖T flim‖ ^ 2)) :=
    hinnerRe.sub hscaled
  have hstageRewrite :
      (fun n ↦ q n (Tn n (f n))) =
        (fun n ↦ RCLike.re (inner K (Tn n (f n)) (f n)) -
          lam * ‖Tn n (f n)‖ ^ 2) := by
    funext n
    linarith [hstageEnergy n (f n)]
  have hlimitRewrite : qlim (T flim) =
      RCLike.re (inner K (T flim) flim) - lam * ‖T flim‖ ^ 2 := by
    linarith [hlimitEnergy flim]
  rw [hstageRewrite, hlimitRewrite]
  exact hraw

/-- Asymptotic density of the stage spaces turns resolvent convergence into an exact recovery
sequence, with convergent form energy, for every vector in the range of the limit resolvent. -/
theorem exists_resolventImage_recovery
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
    (flim : H) :
    ∃ x : ∀ n, Hn n,
      J.StronglyConverges x (T flim) ∧
        Tendsto (fun n ↦ q n (x n)) atTop (𝓝 (qlim (T flim))) := by
  obtain ⟨f, hf⟩ := hdense flim
  exact ⟨fun n ↦ Tn n (f n), hT f flim hf,
    resolventFormValue_tendsto_of_strongOperatorConverges J
      q qlim lam Tn T hT hstageEnergy hlimitEnergy f flim hf⟩

end System

end NCG.VaryingHilbert
