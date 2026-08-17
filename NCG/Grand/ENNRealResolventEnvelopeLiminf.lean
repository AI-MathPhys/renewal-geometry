/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.VaryingHilbertWeakStrongPairing
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Analysis.InnerProductSpace.LinearMap
import NCG.Grand.VaryingHilbertResolventObjective

/-!
# Extended-valued form liminf from resolvent envelopes

Using `ℝ≥0∞` removes the conditional-coboundedness defect of real-valued `liminf`.  This file
proves the order-theoretic bridge and an abstract varying-Hilbert envelope theorem: convergent
finite dual lower bounds imply the Mosco lower inequality even when the limiting form value is
infinite.
-/

open Filter Topology

noncomputable section

namespace NCG

/-- A convergent real lower comparison passes through `ENNReal.ofReal` to an unconditional
extended-valued liminf inequality. -/
theorem ENNReal.ofReal_le_liminf_of_tendsto_of_eventually_le
    {u : ℕ → ENNReal} {v : ℕ → ℝ} {a : ℝ}
    (hv : Tendsto v atTop (𝓝 a))
    (hle : ∀ᶠ n in atTop, ENNReal.ofReal (v n) ≤ u n) :
    ENNReal.ofReal a ≤ liminf u atTop := by
  calc
    ENNReal.ofReal a = liminf (fun n ↦ ENNReal.ofReal (v n)) atTop :=
      (ENNReal.tendsto_ofReal hv).liminf_eq.symm
    _ ≤ liminf u atTop := liminf_le_liminf hle

namespace VaryingHilbert

universe u v w

variable {K : Type u} [RCLike K]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H]

/-- Finite envelope values recover an extended nonnegative form from below.  The formulation by
all strict lower approximations handles both finite values and `∞`. -/
def IsDeterminedByENNRealResolventEnvelopes
    (q : H → ENNReal) (E : ℝ → H → ℝ) : Prop :=
  ∀ (x : H) (C : ℝ), 0 ≤ C → ∀ a : ENNReal, a < q x →
    ∃ lam : ℝ, 0 < lam ∧ ∃ f : H,
      a ≤ ENNReal.ofReal
        (E lam f + 2 * RCLike.re (inner K x f) - lam * C ^ 2)


/-- The finite envelope value canonically determined by a resolvent through its source pairing. -/
def resolventPairingEnvelope (T : H →L[K] H) (f : H) : ℝ :=
  -RCLike.re (inner K (T f) f)

/-- The variational minimizer property and Euler energy identity give the canonical extended-form
envelope lower bound.  Points outside the form domain are handled automatically by `∞`. -/
theorem ennrealResolventEnvelopeLowerBound_of_minimizer
    (q : H → ENNReal) (lam : ℝ) (T : H →L[K] H)
    (henergy : ∀ f : H,
      (q (T f)).toReal + lam * ‖T f‖ ^ 2 = RCLike.re (inner K (T f) f))
    (hmin : ∀ (f z : H), q z ≠ (⊤ : ENNReal) →
      resolventObjective (K := K) (fun x ↦ (q x).toReal) lam f (T f) ≤
        resolventObjective (K := K) (fun x ↦ (q x).toReal) lam f z)
    (f z : H) :
    ENNReal.ofReal
        (resolventPairingEnvelope (K := K) T f +
          2 * RCLike.re (inner K z f) - lam * ‖z‖ ^ 2) ≤ q z := by
  by_cases hz : q z = (⊤ : ENNReal)
  · simp [hz]
  have hreal := hmin f z hz
  have hle :
      resolventPairingEnvelope (K := K) T f +
          2 * RCLike.re (inner K z f) - lam * ‖z‖ ^ 2 ≤ (q z).toReal := by
    simp only [resolventPairingEnvelope, resolventObjective] at hreal ⊢
    linarith [henergy f]
  calc
    ENNReal.ofReal
        (resolventPairingEnvelope (K := K) T f +
          2 * RCLike.re (inner K z f) - lam * ‖z‖ ^ 2)
      ≤ ENNReal.ofReal (q z).toReal := ENNReal.ofReal_le_ofReal hle
    _ = q z := ENNReal.ofReal_toReal hz
namespace System

variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace K (Hn n)]
variable (J : System (K := K) (H := H) (Hn := Hn))

/-- Strong convergence of resolvents gives convergence of their canonical finite pairing
envelopes along every strongly convergent moving source. -/
theorem resolventPairingEnvelope_tendsto_of_strongOperatorConverges
    (Tn : ∀ n, Hn n →L[K] Hn n) (T : H →L[K] H)
    (hT : J.StrongOperatorConverges J Tn T)
    (f : ∀ n, Hn n) (flim : H) (hf : J.StronglyConverges f flim) :
    Tendsto
      (fun n ↦ resolventPairingEnvelope (K := K) (Tn n) (f n)) atTop
      (𝓝 (resolventPairingEnvelope (K := K) T flim)) := by
  have hTf := hT f flim hf
  have hinner : Tendsto
      (fun n ↦ inner K (J.embedding n (Tn n (f n))) (J.embedding n (f n))) atTop
      (𝓝 (inner K (T flim) flim)) :=
    hTf.inner hf
  have hinnerRe := RCLike.reCLM.continuous.continuousAt.tendsto.comp hinner
  simpa only [resolventPairingEnvelope, Function.comp_def,
    LinearIsometry.inner_map_map, RCLike.reCLM_apply] using hinnerRe.neg

/-- Euler energy identities turn strong resolvent convergence into exact convergence of the
extended form energies on moving resolvent images, provided those image energies are finite. -/
theorem ennrealResolventFormValue_tendsto_of_strongOperatorConverges
    (q : (n : ℕ) → Hn n → ENNReal) (qlim : H → ENNReal) (lam : ℝ)
    (Tn : ∀ n, Hn n →L[K] Hn n) (T : H →L[K] H)
    (hT : J.StrongOperatorConverges J Tn T)
    (hstageFinite : ∀ n (f : Hn n), q n (Tn n f) ≠ (⊤ : ENNReal))
    (hlimitFinite : ∀ f : H, qlim (T f) ≠ (⊤ : ENNReal))
    (hstageEnergy : ∀ n (f : Hn n),
      (q n (Tn n f)).toReal + lam * ‖Tn n f‖ ^ 2 =
        RCLike.re (inner K (Tn n f) f))
    (hlimitEnergy : ∀ f : H,
      (qlim (T f)).toReal + lam * ‖T f‖ ^ 2 =
        RCLike.re (inner K (T f) f))
    (f : ∀ n, Hn n) (flim : H) (hf : J.StronglyConverges f flim) :
    Tendsto (fun n ↦ q n (Tn n (f n))) atTop (𝓝 (qlim (T flim))) := by
  have hTf := hT f flim hf
  have hnorm : Tendsto (fun n ↦ ‖Tn n (f n)‖) atTop (𝓝 ‖T flim‖) := by
    simpa [StronglyConverges] using hTf.norm
  have hinner : Tendsto
      (fun n ↦ inner K (J.embedding n (Tn n (f n))) (J.embedding n (f n))) atTop
      (𝓝 (inner K (T flim) flim)) :=
    hTf.inner hf
  have hinnerRe :
      Tendsto (fun n ↦ RCLike.re (inner K (Tn n (f n)) (f n))) atTop
        (𝓝 (RCLike.re (inner K (T flim) flim))) := by
    have hre := RCLike.reCLM.continuous.continuousAt.tendsto.comp hinner
    simpa only [Function.comp_def, LinearIsometry.inner_map_map,
      RCLike.reCLM_apply] using hre
  have hreal : Tendsto (fun n ↦ (q n (Tn n (f n))).toReal) atTop
      (𝓝 (qlim (T flim)).toReal) := by
    have hscaled : Tendsto (fun n ↦ lam * ‖Tn n (f n)‖ ^ 2) atTop
        (𝓝 (lam * ‖T flim‖ ^ 2)) :=
      tendsto_const_nhds.mul (hnorm.pow 2)
    have hraw := hinnerRe.sub hscaled
    convert hraw using 1
    · funext n
      rw [← hstageEnergy n (f n)]
      ring_nf
    · rw [← hlimitEnergy flim]
      ring_nf
  exact (ENNReal.tendsto_toReal_iff
    (fun n ↦ hstageFinite n (f n)) (hlimitFinite flim)).mp hreal

/-- Convergent finite resolvent envelopes imply the extended-valued weak Mosco lower bound.

Unlike the real-valued version, no coboundedness assumption on the stage energies is needed.
The norm penalty is controlled by the automatic bound carried as an explicit input here. -/
theorem ennrealFormValue_le_liminf_of_resolventEnvelopes
    (q : (n : ℕ) → Hn n → ENNReal) (qlim : H → ENNReal)
    (En : ℝ → ∀ n, Hn n → ℝ) (E : ℝ → H → ℝ)
    (hdense : J.IsAsymptoticallyDense)
    (hEnvelope : ∀ lam, 0 < lam →
      ∀ (f : ∀ n, Hn n) (flim : H), J.StronglyConverges f flim →
        Tendsto (fun n ↦ En lam n (f n)) atTop (𝓝 (E lam flim)))
    (hstageLower : ∀ lam, 0 < lam → ∀ n (f z : Hn n),
      ENNReal.ofReal
          (En lam n f + 2 * RCLike.re (inner K z f) - lam * ‖z‖ ^ 2) ≤
        q n z)
    (hdet : IsDeterminedByENNRealResolventEnvelopes (K := K) qlim E)
    (x : ∀ n, Hn n) (xlim : H) (C : ℝ) (hC : 0 ≤ C)
    (hx : J.WeaklyConverges x xlim) (hxBound : ∀ n, ‖x n‖ ≤ C) :
    qlim xlim ≤ liminf (fun n ↦ q n (x n)) atTop := by
  refine le_of_forall_lt_imp_le_of_dense fun a ha ↦ ?_
  obtain ⟨lam, hlam, f, hdual⟩ := hdet xlim C hC a ha
  obtain ⟨fn, hfn⟩ := hdense f
  have hpair := hx.inner_strong J hfn C hxBound
  have hpairRe :
      Tendsto (fun n ↦ RCLike.re (inner K (x n) (fn n))) atTop
        (𝓝 (RCLike.re (inner K xlim f))) := by
    have hre := RCLike.reCLM.continuous.continuousAt.tendsto.comp hpair
    simpa only [Function.comp_def, LinearIsometry.inner_map_map,
      RCLike.reCLM_apply] using hre
  have hscalar : Tendsto
      (fun n ↦ En lam n (fn n) +
        2 * RCLike.re (inner K (x n) (fn n)) - lam * C ^ 2) atTop
      (𝓝 (E lam f + 2 * RCLike.re (inner K xlim f) - lam * C ^ 2)) :=
    ((hEnvelope lam hlam fn f hfn).add (hpairRe.const_mul 2)).sub
      tendsto_const_nhds
  have hlower : ∀ n,
      ENNReal.ofReal
          (En lam n (fn n) + 2 * RCLike.re (inner K (x n) (fn n)) -
            lam * C ^ 2) ≤ q n (x n) := by
    intro n
    have hsq : ‖x n‖ ^ 2 ≤ C ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) hC).2 (hxBound n)
    apply (ENNReal.ofReal_le_ofReal ?_).trans
      (hstageLower lam hlam n (fn n) (x n))
    nlinarith
  exact hdual.trans
    (ENNReal.ofReal_le_liminf_of_tendsto_of_eventually_le
      hscalar (Eventually.of_forall hlower))

/-- Strong resolvent convergence at every positive shift implies the extended-valued form-liminf
inequality once the canonical pairing envelopes determine the limit form.  This specialization
has no real-liminf coboundedness hypothesis. -/
theorem ennrealFormValue_le_liminf_of_strongResolvents
    (q : (n : ℕ) → Hn n → ENNReal) (qlim : H → ENNReal)
    (Tn : ℝ → ∀ n, Hn n →L[K] Hn n) (T : ℝ → H →L[K] H)
    (hdense : J.IsAsymptoticallyDense)
    (hT : ∀ lam, 0 < lam → J.StrongOperatorConverges J (Tn lam) (T lam))
    (hstageEnergy : ∀ lam, 0 < lam → ∀ n (f : Hn n),
      (q n (Tn lam n f)).toReal + lam * ‖Tn lam n f‖ ^ 2 =
        RCLike.re (inner K (Tn lam n f) f))
    (hstageMin : ∀ lam, 0 < lam → ∀ n (f z : Hn n),
      q n z ≠ (⊤ : ENNReal) →
        resolventObjective (K := K) (fun x ↦ (q n x).toReal)
            lam f (Tn lam n f) ≤
          resolventObjective (K := K) (fun x ↦ (q n x).toReal) lam f z)
    (hdet : IsDeterminedByENNRealResolventEnvelopes (K := K) qlim
      (fun lam f ↦ resolventPairingEnvelope (K := K) (T lam) f))
    (x : ∀ n, Hn n) (xlim : H) (C : ℝ) (hC : 0 ≤ C)
    (hx : J.WeaklyConverges x xlim) (hxBound : ∀ n, ‖x n‖ ≤ C) :
    qlim xlim ≤ liminf (fun n ↦ q n (x n)) atTop := by
  apply ennrealFormValue_le_liminf_of_resolventEnvelopes J q qlim
    (fun lam n f ↦ resolventPairingEnvelope (K := K) (Tn lam n) f)
    (fun lam f ↦ resolventPairingEnvelope (K := K) (T lam) f)
    hdense
  · intro lam hlam f flim hf
    exact resolventPairingEnvelope_tendsto_of_strongOperatorConverges
      J (Tn lam) (T lam) (hT lam hlam) f flim hf
  · intro lam hlam n f z
    exact ennrealResolventEnvelopeLowerBound_of_minimizer
      (K := K) (q n) lam (Tn lam n) (hstageEnergy lam hlam n)
        (hstageMin lam hlam n) f z
  · exact hdet
  · exact hC
  · exact hx
  · exact hxBound

end System

end VaryingHilbert

end NCG
