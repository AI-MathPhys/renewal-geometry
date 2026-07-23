/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Full rank of the cycle covariance

**Proposition `prop:cycle-covariance-rank`**: if every nonzero scalar
projection of the displacement cocycle has a nonzero period on some
closed cycle, the winding covariance `Q` has full rank `b_eff`.  The
linear-algebra core proved here: for a positive-semidefinite symmetric
bilinear form, a zero diagonal value forces the whole row to vanish
(`NCG.psd_zero_diag_null`), so if no nonzero vector has zero variance
the form has trivial kernel and full rank
(`NCG.covariance_full_rank`).  The Markov-additive CLT identifying the
asymptotic variance with the cycle periods is the noted external
input.
-/

namespace NCG

/-- **PSD null-vector lemma**: for a symmetric positive-semidefinite
bilinear form, `B(a,a) = 0` forces `B(a,v) = 0` for every `v` — a
direction of zero variance is in the kernel of the whole form. -/
theorem psd_zero_diag_null {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hsym : ∀ u v, B u v = B v u) (hpsd : ∀ v, 0 ≤ B v v)
    {a : V} (ha : B a a = 0) : ∀ v, B a v = 0 := by
  intro v
  have hexp : ∀ t : ℝ, 0 ≤ 2 * t * B a v + t ^ 2 * B v v := by
    intro t
    have h1 := hpsd (a + t • v)
    have e : B (a + t • v) (a + t • v)
        = B a a + t * B a v + t * B v a + t ^ 2 * B v v := by
      simp only [map_add, map_smul, LinearMap.add_apply,
        LinearMap.smul_apply, smul_eq_mul]
      ring
    rw [e, ha, hsym v a] at h1
    linarith
  rcases eq_or_ne (B v v) 0 with hv | hv
  · have hp := hexp 1
    have hm := hexp (-1)
    rw [hv] at hp hm
    linarith
  · have hvpos : 0 < B v v := (hpsd v).lt_of_ne (Ne.symm hv)
    have hp := hexp (-(B a v) / B v v)
    have hkey : (2 * (-(B a v) / B v v) * B a v
        + (-(B a v) / B v v) ^ 2 * B v v) * B v v = -(B a v ^ 2) := by
      field_simp
      ring
    have hnn : 0 ≤ -(B a v ^ 2) := by
      rw [← hkey]
      exact mul_nonneg hp hvpos.le
    have hz : B a v ^ 2 = 0 :=
      le_antisymm (by linarith) (sq_nonneg _)
    exact pow_eq_zero_iff (n := 2) (by omega) |>.mp hz

/-- The covariance form has trivial kernel when no nonzero direction
has zero variance. -/
theorem covariance_ker_eq_bot {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hnull : ∀ a : V, a ≠ 0 → B a a ≠ 0) :
    LinearMap.ker B = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro a ha
  by_contra hne
  exact hnull a hne (by rw [ha]; rfl)

/-- **Proposition `prop:cycle-covariance-rank` (rank core)**: if every
nonzero projection has nonzero variance, the covariance form has full
rank — `rank Q = b_eff`. -/
theorem covariance_full_rank {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hnull : ∀ a : V, a ≠ 0 → B a a ≠ 0) :
    Module.finrank ℝ (LinearMap.range B) = Module.finrank ℝ V :=
  LinearMap.finrank_range_of_inj
    (LinearMap.ker_eq_bot.mp (covariance_ker_eq_bot B hnull))

end NCG
