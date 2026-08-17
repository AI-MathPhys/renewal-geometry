/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ResolventEnvelopeLiminf

/-!
# Recovering form liminf from resolvent envelopes

If the positive-shift resolvent envelopes determine the limit form through their dual lower
bounds, then strong resolvent convergence at every positive shift implies the weak form-liminf
inequality for bounded moving sequences.  This packages the optimization step in the converse
Mosco theorem.
-/

open Filter Topology

noncomputable section

namespace NCG.VaryingHilbert

universe u v

variable {K : Type u} [RCLike K]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace K E]

/-- The positive-shift resolvent envelopes recover a form through arbitrarily sharp dual lower
bounds, uniformly allowing any prescribed ambient norm bound `C`. -/
def IsDeterminedByResolventEnvelopes
    (q : E → ℝ) (T : ℝ → E →L[K] E) : Prop :=
  ∀ (x : E) (C : ℝ), 0 ≤ C → ∀ ε > 0,
    ∃ lam : ℝ, 0 < lam ∧ ∃ f : E,
      q x - ε ≤ resolventEnvelope (K := K) q lam (T lam) f +
        2 * RCLike.re (inner K x f) - lam * C ^ 2

namespace System

universe w

variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace K (Hn n)]
variable (J : System (K := K) (H := H) (Hn := Hn))

/-- Strong resolvent convergence at every positive shift implies the form-liminf inequality on
every uniformly bounded weakly convergent sequence, provided the limit envelopes determine the
form. -/
theorem formValue_le_liminf_of_strongResolvents
    (q : (n : ℕ) → Hn n → ℝ) (qlim : H → ℝ)
    (Tn : ℝ → ∀ n, Hn n →L[K] Hn n) (T : ℝ → H →L[K] H)
    (hdense : J.IsAsymptoticallyDense)
    (hT : ∀ lam, 0 < lam → J.StrongOperatorConverges J (Tn lam) (T lam))
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
    (x : ∀ n, Hn n) (xlim : H) (C : ℝ) (hC : 0 ≤ C)
    (hx : J.WeaklyConverges x xlim) (hxBound : ∀ n, ‖x n‖ ≤ C)
    (hqCobounded : IsCoboundedUnder (· ≥ ·) atTop (fun n ↦ q n (x n))) :
    qlim xlim ≤ liminf (fun n ↦ q n (x n)) atTop := by
  by_contra hnot
  have hgap : 0 < qlim xlim - liminf (fun n ↦ q n (x n)) atTop :=
    sub_pos.mpr (lt_of_not_ge hnot)
  let ε : ℝ := (qlim xlim - liminf (fun n ↦ q n (x n)) atTop) / 2
  have hε : 0 < ε := by
    dsimp [ε]
    linarith
  obtain ⟨lam, hlam, f, hdual⟩ := hdet xlim C hC ε hε
  obtain ⟨fn, hfn⟩ := hdense f
  have hlower :=
    resolventEnvelope_pairing_le_liminf_of_strongOperatorConverges J
      q qlim lam C (Tn lam) (T lam) (hT lam hlam)
      (hstageEnergy lam hlam) (hlimitEnergy lam hlam)
      fn x f xlim hlam.le hC
      hx hfn hxBound
      (fun n ↦ by
        simpa [resolventEnvelope] using hstageMin lam hlam n (fn n) (x n))
      hqCobounded
  dsimp [ε] at hdual
  linarith

end System

end NCG.VaryingHilbert
