/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ResolventEnvelopeConvergence
import NCG.Grand.VaryingHilbertWeakStrongPairing
import Mathlib.Topology.Order.LiminfLimsup

/-!
# Form liminf bounds from resolvent envelopes

The minimizing property of a resolvent gives a lower bound on the form at every test vector in
terms of the minimized objective, the source pairing, and a quadratic norm penalty.  Along a
bounded weakly convergent family, strong source convergence and envelope convergence pass this
bound to `liminf`.  Optimizing this estimate is the weak-liminf half of the Moreau-envelope
converse to Mosco convergence.
-/

open Filter Topology

noncomputable section

namespace NCG.VaryingHilbert

universe u v

variable {K : Type u} [RCLike K]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace K E]

/-- The elementary Moreau-envelope lower bound for a form value. -/
theorem resolventEnvelope_add_pairing_sub_le_form
    (q : E → ℝ) (lam C : ℝ) (T : E →L[K] E) (f x : E)
    (hlam : 0 ≤ lam) (hC : 0 ≤ C) (hx : ‖x‖ ≤ C)
    (hmin : resolventEnvelope (K := K) q lam T f ≤
      resolventObjective (K := K) q lam f x) :
    resolventEnvelope (K := K) q lam T f +
        2 * RCLike.re (inner K x f) - lam * C ^ 2 ≤ q x := by
  have hsquare : ‖x‖ ^ 2 ≤ C ^ 2 := (sq_le_sq₀ (norm_nonneg x) hC).2 hx
  have hscaled : lam * ‖x‖ ^ 2 ≤ lam * C ^ 2 :=
    mul_le_mul_of_nonneg_left hsquare hlam
  simp only [resolventObjective] at hmin
  linarith

namespace System

universe w

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace K (Hn n)]
variable (J : System (K := K) (H := H) (Hn := Hn))

/-- Envelope convergence yields a form-liminf lower bound along a uniformly bounded weakly
convergent sequence.  The explicit coboundedness hypothesis is the order-theoretic condition
needed for real-valued `liminf`; nonnegative finite-energy applications usually discharge it
from their energy bounds. -/
theorem resolventEnvelope_pairing_le_liminf
    (q : (n : ℕ) → Hn n → ℝ) (qlim : H → ℝ) (lam C : ℝ)
    (Tn : ∀ n, Hn n →L[K] Hn n) (T : H →L[K] H)
    (f x : ∀ n, Hn n) (flim xlim : H)
    (hlam : 0 ≤ lam) (hC : 0 ≤ C)
    (hx : J.WeaklyConverges x xlim) (hf : J.StronglyConverges f flim)
    (hxBound : ∀ n, ‖x n‖ ≤ C)
    (henv : Tendsto
      (fun n ↦ resolventEnvelope (K := K) (q n) lam (Tn n) (f n)) atTop
      (𝓝 (resolventEnvelope (K := K) qlim lam T flim)))
    (hmin : ∀ n,
      resolventEnvelope (K := K) (q n) lam (Tn n) (f n) ≤
        resolventObjective (K := K) (q n) lam (f n) (x n))
    (hqCobounded : IsCoboundedUnder (· ≥ ·) atTop (fun n ↦ q n (x n))) :
    resolventEnvelope (K := K) qlim lam T flim +
        2 * RCLike.re (inner K xlim flim) - lam * C ^ 2 ≤
      liminf (fun n ↦ q n (x n)) atTop := by
  have hpair := hx.inner_strong J hf C hxBound
  have hpairRe : Tendsto
      (fun n ↦ RCLike.re (inner K (x n) (f n))) atTop
      (𝓝 (RCLike.re (inner K xlim flim))) := by
    have hre := RCLike.reCLM.continuous.continuousAt.tendsto.comp hpair
    simpa only [Function.comp_def, LinearIsometry.inner_map_map,
      RCLike.reCLM_apply] using hre
  let lower : ℕ → ℝ := fun n ↦
    resolventEnvelope (K := K) (q n) lam (Tn n) (f n) +
      2 * RCLike.re (inner K (x n) (f n)) - lam * C ^ 2
  have hlower : Tendsto lower atTop
      (𝓝 (resolventEnvelope (K := K) qlim lam T flim +
        2 * RCLike.re (inner K xlim flim) - lam * C ^ 2)) := by
    simpa [lower] using (henv.add (hpairRe.const_mul 2)).sub tendsto_const_nhds
  have hlowerLe : ∀ n, lower n ≤ q n (x n) := by
    intro n
    exact resolventEnvelope_add_pairing_sub_le_form
      (q n) lam C (Tn n) (f n) (x n) hlam hC (hxBound n) (hmin n)
  calc
    resolventEnvelope (K := K) qlim lam T flim +
          2 * RCLike.re (inner K xlim flim) - lam * C ^ 2 =
        liminf lower atTop := hlower.liminf_eq.symm
    _ ≤ liminf (fun n ↦ q n (x n)) atTop :=
      liminf_le_liminf (Eventually.of_forall hlowerLe)
        hlower.isBoundedUnder_ge hqCobounded

/-- The same liminf lower bound follows directly from strong resolvent convergence and the
quadratic Euler identities, which automatically supply convergence of the envelopes. -/
theorem resolventEnvelope_pairing_le_liminf_of_strongOperatorConverges
    (q : (n : ℕ) → Hn n → ℝ) (qlim : H → ℝ) (lam C : ℝ)
    (Tn : ∀ n, Hn n →L[K] Hn n) (T : H →L[K] H)
    (hT : J.StrongOperatorConverges J Tn T)
    (hstageEnergy : ∀ n (f : Hn n),
      q n (Tn n f) + lam * ‖Tn n f‖ ^ 2 =
        RCLike.re (inner K (Tn n f) f))
    (hlimitEnergy : ∀ f : H,
      qlim (T f) + lam * ‖T f‖ ^ 2 =
        RCLike.re (inner K (T f) f))
    (f x : ∀ n, Hn n) (flim xlim : H)
    (hlam : 0 ≤ lam) (hC : 0 ≤ C)
    (hx : J.WeaklyConverges x xlim) (hf : J.StronglyConverges f flim)
    (hxBound : ∀ n, ‖x n‖ ≤ C)
    (hmin : ∀ n,
      resolventEnvelope (K := K) (q n) lam (Tn n) (f n) ≤
        resolventObjective (K := K) (q n) lam (f n) (x n))
    (hqCobounded : IsCoboundedUnder (· ≥ ·) atTop (fun n ↦ q n (x n))) :
    resolventEnvelope (K := K) qlim lam T flim +
        2 * RCLike.re (inner K xlim flim) - lam * C ^ 2 ≤
      liminf (fun n ↦ q n (x n)) atTop := by
  apply resolventEnvelope_pairing_le_liminf J q qlim lam C Tn T
    f x flim xlim hlam hC hx hf hxBound
  · exact resolventEnvelope_tendsto_of_strongOperatorConverges J
      q qlim lam Tn T hT hstageEnergy hlimitEnergy f flim hf
  · exact hmin
  · exact hqCobounded

end System

end NCG.VaryingHilbert
