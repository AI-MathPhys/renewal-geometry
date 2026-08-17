/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.MoscoRecoveryEnergyConvergence

/-!
# Finite-energy Mosco recovery sequences

Recovery toward a point of finite extended energy is eventually finite.  Replacing the finitely
many exceptional terms by a fixed finite-energy base point produces a recovery sequence that is
finite at every index, without changing either its strong limit or its energy limit.
-/

open scoped ENNReal

open Filter Topology

noncomputable section

namespace NCG.VaryingHilbert.System.MoscoConverges

universe u v w

variable {K : Type u} [RCLike K]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace K (Hn n)]
variable {J : System (K := K) (H := H) (Hn := Hn)}
variable {q : (n : ℕ) → Hn n → ℝ≥0∞} {qlim : H → ℝ≥0∞}

/-- A recovery sequence approaching a finite-energy limit is eventually finite. -/
theorem eventually_recovery_energy_ne_top
    (hq : J.MoscoConverges q qlim)
    {x : ∀ n, Hn n} {xlim : H}
    (hx : J.StronglyConverges x xlim)
    (hsup : limsup (fun n ↦ q n (x n)) atTop ≤ qlim xlim)
    (hfinite : qlim xlim ≠ ∞) :
    ∀ᶠ n in atTop, q n (x n) ≠ ∞ := by
  have htendsto := hq.recovery_energy_tendsto hx hsup
  have hlt : qlim xlim < ∞ := lt_top_iff_ne_top.mpr hfinite
  filter_upwards [htendsto.eventually (Iio_mem_nhds hlt)] with n hn
  exact ne_of_lt hn

/-- At a finite-energy limit, Mosco recovery may be chosen finite at every stage. -/
theorem exists_finite_recovery_energy_tendsto
    (hq : J.MoscoConverges q qlim)
    (hq0 : ∀ n, q n 0 = 0)
    (xlim : H) (hfinite : qlim xlim ≠ ∞) :
    ∃ x : ∀ n, Hn n,
      J.StronglyConverges x xlim ∧
        Tendsto (fun n ↦ q n (x n)) atTop (𝓝 (qlim xlim)) ∧
          ∀ n, q n (x n) ≠ ∞ := by
  obtain ⟨x, hx, henergy⟩ := hq.exists_recovery_energy_tendsto xlim
  have hevent : ∀ᶠ n in atTop, q n (x n) ≠ ∞ := by
    have hlt : qlim xlim < ∞ := lt_top_iff_ne_top.mpr hfinite
    filter_upwards [henergy.eventually (Iio_mem_nhds hlt)] with n hn
    exact ne_of_lt hn
  let x' : ∀ n, Hn n := fun n ↦ if q n (x n) = ∞ then 0 else x n
  have hxEq : ∀ᶠ n in atTop, x' n = x n := by
    filter_upwards [hevent] with n hn
    simp [x', hn]
  refine ⟨x', ?_, ?_, ?_⟩
  · rw [StronglyConverges]
    exact hx.congr' (hxEq.mono fun n hn ↦ congrArg (J.embedding n) hn.symm)
  · exact henergy.congr' (hxEq.mono fun n hn ↦ congrArg (q n) hn.symm)
  · intro n
    by_cases hn : q n (x n) = ∞
    · simp [x', hn, hq0 n]
    · simpa [x', hn] using hn

end NCG.VaryingHilbert.System.MoscoConverges
