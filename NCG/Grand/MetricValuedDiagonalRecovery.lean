/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.DiagonalTendsto
import NCG.Grand.VaryingHilbertMosco

/-!
# Metric-valued diagonal recovery on varying Hilbert spaces

The diagonal recovery argument is independent of the scalar type of the energy.  This generic
version applies to real, ENNReal, or any other pseudometric-valued functional.
-/

open Filter Topology

noncomputable section

namespace NCG.VaryingHilbert.System

universe u v w z

variable {K : Type u} [RCLike K]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace K (Hn n)]
variable {Y : Type z} [PseudoMetricSpace Y]
variable (J : System (K := K) (H := H) (Hn := Hn))

/-- Rowwise recovery sequences for convergent limit-space approximants admit a simultaneous
diagonal preserving vector convergence and convergence of a metric-valued energy. -/
theorem exists_metricValued_diagonal_recovery
    (q : (n : ℕ) → Hn n → Y) (qlim : H → Y)
    (a : ℕ → H) (alim : H)
    (ha : Tendsto a atTop (𝓝 alim))
    (hqa : Tendsto (fun m ↦ qlim (a m)) atTop (𝓝 (qlim alim)))
    (x : ℕ → ∀ n, Hn n)
    (hx : ∀ m, J.StronglyConverges (x m) (a m))
    (hqx : ∀ m, Tendsto (fun n ↦ q n (x m n)) atTop (𝓝 (qlim (a m)))) :
    ∃ φ : ℕ → ℕ, Tendsto φ atTop atTop ∧
      J.StronglyConverges (fun n ↦ x (φ n) n) alim ∧
        Tendsto (fun n ↦ q n (x (φ n) n)) atTop (𝓝 (qlim alim)) := by
  obtain ⟨φ, hφ, hvec, henergy⟩ := exists_diagonal_tendsto_pair
    (fun m n ↦ J.embedding n (x m n)) a alim
    (fun m n ↦ q n (x m n)) (fun m ↦ qlim (a m)) (qlim alim)
    hx ha hqx hqa
  exact ⟨φ, hφ, hvec, henergy⟩

/-- Separately supplied row recoveries for metric-valued energies combine into one recovery at
the limit of the approximating vectors. -/
theorem exists_recovery_of_metricValued_tendsto_approximants
    (q : (n : ℕ) → Hn n → Y) (qlim : H → Y)
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
    exists_metricValued_diagonal_recovery J q qlim a alim ha hqa x hx hqx
  exact ⟨fun n ↦ x (φ n) n, hvec, henergy⟩

end NCG.VaryingHilbert.System
