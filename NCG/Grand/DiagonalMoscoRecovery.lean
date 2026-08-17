/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.DiagonalTendsto
import NCG.Grand.VaryingHilbertRealMosco

/-!
# Diagonal recovery sequences on varying Hilbert spaces

Recovery sequences for a convergent family of limit-space approximants can be diagonalized into
one recovery sequence for their limit.  Both common-carrier norm convergence and real form-energy
convergence are preserved.
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

/-- A family of recovery sequences for convergent limit-space approximants admits one cofinal
diagonal recovery sequence for the limiting vector and energy. -/
theorem exists_diagonal_recovery
    (q : (n : ℕ) → Hn n → ℝ) (qlim : H → ℝ)
    (a : ℕ → H) (alim : H)
    (ha : Tendsto a atTop (𝓝 alim))
    (hqa : Tendsto (fun m ↦ qlim (a m)) atTop (𝓝 (qlim alim)))
    (x : ℕ → ∀ n, Hn n)
    (hx : ∀ m, J.StronglyConverges (x m) (a m))
    (hqx : ∀ m,
      Tendsto (fun n ↦ q n (x m n)) atTop (𝓝 (qlim (a m)))) :
    ∃ φ : ℕ → ℕ, Tendsto φ atTop atTop ∧
      J.StronglyConverges (fun n ↦ x (φ n) n) alim ∧
        Tendsto (fun n ↦ q n (x (φ n) n)) atTop (𝓝 (qlim alim)) := by
  obtain ⟨φ, hφ, hvec, henergy⟩ := exists_diagonal_tendsto_pair
    (fun m n ↦ J.embedding n (x m n)) a alim
    (fun m n ↦ q n (x m n)) (fun m ↦ qlim (a m)) (qlim alim)
    hx ha hqx hqa
  exact ⟨φ, hφ, hvec, henergy⟩

/-- It is enough to provide a recovery sequence separately for each approximating limit vector;
choice and the simultaneous diagonal theorem produce a single recovery sequence at the limit. -/
theorem exists_recovery_of_tendsto_approximants
    (q : (n : ℕ) → Hn n → ℝ) (qlim : H → ℝ)
    (a : ℕ → H) (alim : H)
    (ha : Tendsto a atTop (𝓝 alim))
    (hqa : Tendsto (fun m ↦ qlim (a m)) atTop (𝓝 (qlim alim)))
    (hrecovery : ∀ m, ∃ x : ∀ n, Hn n,
      J.StronglyConverges x (a m) ∧
        Tendsto (fun n ↦ q n (x n)) atTop (𝓝 (qlim (a m)))) :
    ∃ x : ∀ n, Hn n,
      J.StronglyConverges x alim ∧
        Tendsto (fun n ↦ q n (x n)) atTop (𝓝 (qlim alim)) := by
  choose x hx hqx using hrecovery
  obtain ⟨φ, -, hvec, henergy⟩ :=
    exists_diagonal_recovery J q qlim a alim ha hqa x hx hqx
  exact ⟨fun n ↦ x (φ n) n, hvec, henergy⟩

end NCG.VaryingHilbert.System
