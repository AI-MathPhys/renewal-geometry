/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.VaryingHilbertMosco
import Mathlib.Topology.Order.LiminfLimsup

/-!
# Cofinal finite-valued Mosco convergence

This is the real-valued interface used by quadratic-form resolvent arguments.  The liminf clause
is explicitly stable under every cofinal reindexing, matching the subsequences produced by weak
compactness, while recovery energies converge as finite real numbers.
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

/-- Cofinal Mosco convergence for everywhere-finite real-valued forms. -/
structure RealMoscoConverges
    (q : (n : ℕ) → Hn n → ℝ) (qlim : H → ℝ) : Prop where
  /-- Every cofinal reindexing satisfies the weak form-liminf inequality. -/
  liminf_le : ∀ (φ : ℕ → ℕ), Tendsto φ atTop atTop →
    ∀ (x : ∀ n, Hn (φ n)) (xlim : H),
      (J.reindex φ).WeaklyConverges x xlim →
        qlim xlim ≤ liminf (fun n ↦ q (φ n) (x n)) atTop
  /-- Every limit vector has a strongly convergent recovery sequence with convergent energy. -/
  recovery : ∀ xlim : H, ∃ x : ∀ n, Hn n,
    J.StronglyConverges x xlim ∧
      Tendsto (fun n ↦ q n (x n)) atTop (𝓝 (qlim xlim))

namespace RealMoscoConverges

variable {J}
variable {q : (n : ℕ) → Hn n → ℝ} {qlim : H → ℝ}

/-- Real Mosco convergence supplies asymptotic density of the comparison system. -/
theorem asymptoticallyDense (hq : J.RealMoscoConverges q qlim) :
    J.IsAsymptoticallyDense := by
  intro xlim
  obtain ⟨x, hx, -⟩ := hq.recovery xlim
  exact ⟨x, hx⟩

/-- The form liminf clause applies directly to a cofinal subsequence followed by a strictly
increasing extraction. -/
theorem liminf_le_subsequence
    (hq : J.RealMoscoConverges q qlim)
    (ns : ℕ → ℕ) (hns : Tendsto ns atTop atTop)
    (ψ : ℕ → ℕ) (hψ : StrictMono ψ)
    (x : ∀ n, Hn n) (xlim : H)
    (hweak : (J.reindex (ns ∘ ψ)).WeaklyConverges
      (fun k ↦ x (ns (ψ k))) xlim) :
    qlim xlim ≤ liminf (fun k ↦ q (ns (ψ k)) (x (ns (ψ k)))) atTop :=
  hq.liminf_le (ns ∘ ψ) (hns.comp hψ.tendsto_atTop)
    (fun k ↦ x (ns (ψ k))) xlim hweak

end RealMoscoConverges

end NCG.VaryingHilbert.System
