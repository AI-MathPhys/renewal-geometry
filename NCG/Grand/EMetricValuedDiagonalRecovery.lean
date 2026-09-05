/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.EDiagonalTendsto
import NCG.Grand.VaryingHilbertMosco

/-!
# Extended-metric-valued diagonal recovery on varying Hilbert spaces

This is the recovery wrapper for energies such as ENNReal that carry their natural topology via
an extended metric.
-/

open Filter Topology

noncomputable section

namespace NCG.VaryingHilbert.System

universe u v w z

variable {K : Type u} [RCLike K]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace K (Hn n)]
variable {Y : Type z} [PseudoEMetricSpace Y]
variable (J : System (K := K) (H := H) (Hn := Hn))

/-- Rowwise recoveries with extended-metric energy values admit a simultaneous diagonal. -/
theorem exists_emetricValued_diagonal_recovery
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
  obtain ⟨φ, hφ, hvec, henergy⟩ := exists_diagonal_tendsto_pair_emetric
    (fun m n ↦ J.embedding n (x m n)) a alim
    (fun m n ↦ q n (x m n)) (fun m ↦ qlim (a m)) (qlim alim)
    hx ha hqx hqa
  exact ⟨φ, hφ, hvec, henergy⟩

/-- Separately supplied extended-metric row recoveries combine into one recovery at the limit. -/
theorem exists_recovery_of_emetricValued_tendsto_approximants
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
    exists_emetricValued_diagonal_recovery J q qlim a alim ha hqa x hx hqx
  exact ⟨fun n ↦ x (φ n) n, hvec, henergy⟩

end NCG.VaryingHilbert.System
