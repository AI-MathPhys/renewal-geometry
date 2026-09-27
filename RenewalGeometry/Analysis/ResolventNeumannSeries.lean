/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Neumann series of the resolvent in a complete normed algebra

Reusable infrastructure for the rational realization theory of
`predictive_spectral_geometry` (`thm:supp-complete-rational-Krein`,
`thm:supp-pole-Hankel`, `cor:supp-all-rational`).

For an element `A` of a complete normed `ℂ`-algebra `R` and a scalar `z` with
`‖A‖ < ‖z‖`, the element `A - z` is a unit and its inverse is the Laurent
series at infinity
`(A - z)⁻¹ = -∑_{n ≥ 0} z^{-n-1} A^n`
(`hasSum_resolvent_neumann`, `inverse_sub_algebraMap_eq_neg_tsum`).

Consequences:

* `norm_inverse_sub_algebraMap_le`: `‖(A - z)⁻¹‖ ≤ (‖z‖ - ‖A‖)⁻¹` when
  `‖1‖ ≤ 1` (true in every operator algebra `E →L[ℂ] E`).
* `tendsto_neg_smul_inverse_sub_algebraMap`: `-w (A - w)⁻¹ → 1` along any
  sequence `w_k` with `‖w_k‖ → ∞` (the source vector lies in the closed span of
  the resolvent-source vectors).
* `resolvent_sub_resolvent`: the resolvent identity
  `(A - z)⁻¹ - (A - w)⁻¹ = (z - w) (A - z)⁻¹ (A - w)⁻¹`.
-/

open Filter Topology

namespace RenewalGeometry

section NormedAlgebra

variable {R : Type*} [NormedRing R] [NormedAlgebra ℂ R] [CompleteSpace R]

/-- `A - z = (-z) • (1 - z⁻¹ • A)` for `z ≠ 0`. -/
theorem sub_algebraMap_eq_neg_smul_one_sub (A : R) {z : ℂ} (hz : z ≠ 0) :
    A - algebraMap ℂ R z = (-z) • (1 - z⁻¹ • A) := by
  rw [Algebra.algebraMap_eq_smul_one, smul_sub, smul_smul, neg_mul, mul_inv_cancel₀ hz,
    neg_one_smul, sub_neg_eq_add, neg_smul, neg_add_eq_sub]

/-- `‖A‖ < ‖z‖` forces `z ≠ 0`. -/
theorem ne_zero_of_norm_lt_norm (A : R) {z : ℂ} (hz : ‖A‖ < ‖z‖) : z ≠ 0 := by
  rintro rfl
  rw [norm_zero] at hz
  exact not_lt.mpr (norm_nonneg A) hz

/-- The scaled element `z⁻¹ • A` has norm `< 1` when `‖A‖ < ‖z‖`. -/
theorem norm_inv_smul_lt_one (A : R) {z : ℂ} (hz : ‖A‖ < ‖z‖) : ‖z⁻¹ • A‖ < 1 := by
  have hz0 : z ≠ 0 := ne_zero_of_norm_lt_norm A hz
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  calc ‖z⁻¹ • A‖ ≤ ‖z⁻¹‖ * ‖A‖ := norm_smul_le _ _
    _ = ‖A‖ / ‖z‖ := by rw [norm_inv]; ring
    _ < 1 := (div_lt_one hzpos).mpr hz

/-- The Neumann (Laurent) series of the resolvent: for `‖A‖ < ‖z‖`,
`∑_{n ≥ 0} z^{-n-1} A^n = -(A - z)⁻¹`, and `A - z` is a unit
(`isUnit_sub_algebraMap_of_norm_lt`). -/
theorem hasSum_resolvent_neumann (A : R) {z : ℂ} (hz : ‖A‖ < ‖z‖) :
    HasSum (fun n : ℕ => (z⁻¹ ^ (n + 1)) • A ^ n)
      (-(Ring.inverse (A - algebraMap ℂ R z))) := by
  have hz0 : z ≠ 0 := ne_zero_of_norm_lt_norm A hz
  set t : R := z⁻¹ • A with ht
  have htn : ‖t‖ < 1 := norm_inv_smul_lt_one A hz
  have hsum : Summable fun n : ℕ => t ^ n := summable_geometric_of_norm_lt_one htn
  set G : R := ∑' n : ℕ, t ^ n with hG
  have hG1 : G * (1 - t) = 1 := geom_series_mul_neg t htn
  have hG2 : (1 - t) * G = 1 := mul_neg_geom_series t htn
  set S : R := (-z⁻¹) • G with hS
  have hfac : A - algebraMap ℂ R z = (-z) • (1 - t) := sub_algebraMap_eq_neg_smul_one_sub A hz0
  have hzz : (-z⁻¹) * (-z) = 1 := by rw [neg_mul_neg, inv_mul_cancel₀ hz0]
  have hzz' : (-z) * (-z⁻¹) = 1 := by rw [neg_mul_neg, mul_inv_cancel₀ hz0]
  have h1 : S * (A - algebraMap ℂ R z) = 1 := by
    rw [hfac, hS, smul_mul_smul_comm, hzz, hG1, one_smul]
  have h2 : (A - algebraMap ℂ R z) * S = 1 := by
    rw [hfac, hS, smul_mul_smul_comm, hzz', hG2, one_smul]
  let u : Rˣ := ⟨A - algebraMap ℂ R z, S, h2, h1⟩
  have hinv : Ring.inverse (A - algebraMap ℂ R z) = S := by
    have : Ring.inverse (u : R) = ((u⁻¹ : Rˣ) : R) := Ring.inverse_unit u
    exact this
  rw [hinv, hS, neg_smul, neg_neg]
  have hterm : ∀ n : ℕ, (z⁻¹ ^ (n + 1)) • A ^ n = z⁻¹ • t ^ n := by
    intro n
    rw [ht, smul_pow, smul_smul, pow_succ']
  simp_rw [hterm]
  exact hsum.hasSum.const_smul z⁻¹

/-- For `‖A‖ < ‖z‖` the element `A - z` is a unit. -/
theorem isUnit_sub_algebraMap_of_norm_lt (A : R) {z : ℂ} (hz : ‖A‖ < ‖z‖) :
    IsUnit (A - algebraMap ℂ R z) := by
  have hz0 : z ≠ 0 := ne_zero_of_norm_lt_norm A hz
  rw [sub_algebraMap_eq_neg_smul_one_sub A hz0]
  have htn : ‖z⁻¹ • A‖ < 1 := norm_inv_smul_lt_one A hz
  have hu : IsUnit (1 - z⁻¹ • A) := (Units.oneSub _ htn).isUnit
  have hzu : IsUnit (algebraMap ℂ R (-z)) := by
    exact (IsUnit.map (algebraMap ℂ R) (isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr hz0)))
  rw [Algebra.smul_def]
  exact hzu.mul hu

/-- The resolvent is the Laurent series at infinity:
`(A - z)⁻¹ = -∑_{n ≥ 0} z^{-n-1} A^n` for `‖A‖ < ‖z‖`. -/
theorem inverse_sub_algebraMap_eq_neg_tsum (A : R) {z : ℂ} (hz : ‖A‖ < ‖z‖) :
    Ring.inverse (A - algebraMap ℂ R z) = -∑' n : ℕ, (z⁻¹ ^ (n + 1)) • A ^ n := by
  rw [(hasSum_resolvent_neumann A hz).tsum_eq, neg_neg]

/-- Summability of the Laurent series of the resolvent. -/
theorem summable_resolvent_neumann (A : R) {z : ℂ} (hz : ‖A‖ < ‖z‖) :
    Summable fun n : ℕ => (z⁻¹ ^ (n + 1)) • A ^ n :=
  (hasSum_resolvent_neumann A hz).summable

/-- Norm bound on the resolvent: `‖(A - z)⁻¹‖ ≤ (‖z‖ - ‖A‖)⁻¹` for `‖A‖ < ‖z‖`,
assuming `‖1‖ ≤ 1` (true in every operator algebra). -/
theorem norm_inverse_sub_algebraMap_le (A : R) (h1 : ‖(1 : R)‖ ≤ 1) {z : ℂ}
    (hz : ‖A‖ < ‖z‖) :
    ‖Ring.inverse (A - algebraMap ℂ R z)‖ ≤ (‖z‖ - ‖A‖)⁻¹ := by
  have hz0 : z ≠ 0 := ne_zero_of_norm_lt_norm A hz
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hApow : ∀ n : ℕ, ‖A ^ n‖ ≤ ‖A‖ ^ n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simpa using h1
    · exact norm_pow_le' A hn
  have hbound : ∀ n : ℕ, ‖(z⁻¹ ^ (n + 1)) • A ^ n‖ ≤ ‖z‖⁻¹ * (‖A‖ / ‖z‖) ^ n := by
    intro n
    calc ‖(z⁻¹ ^ (n + 1)) • A ^ n‖ ≤ ‖z⁻¹ ^ (n + 1)‖ * ‖A ^ n‖ := norm_smul_le _ _
      _ ≤ ‖z‖⁻¹ ^ (n + 1) * ‖A‖ ^ n := by
          rw [norm_pow, norm_inv]
          exact mul_le_mul_of_nonneg_left (hApow n) (by positivity)
      _ = ‖z‖⁻¹ * (‖A‖ / ‖z‖) ^ n := by
          rw [pow_succ', div_pow, mul_assoc, inv_pow, div_eq_mul_inv, mul_comm (‖A‖ ^ n)]
  have hratio : ‖A‖ / ‖z‖ < 1 := (div_lt_one hzpos).mpr hz
  have hratio0 : 0 ≤ ‖A‖ / ‖z‖ := by positivity
  have hgeom : Summable fun n : ℕ => ‖z‖⁻¹ * (‖A‖ / ‖z‖) ^ n :=
    (summable_geometric_of_lt_one hratio0 hratio).mul_left _
  rw [inverse_sub_algebraMap_eq_neg_tsum A hz, norm_neg]
  calc ‖∑' n : ℕ, (z⁻¹ ^ (n + 1)) • A ^ n‖
      ≤ ∑' n : ℕ, ‖z‖⁻¹ * (‖A‖ / ‖z‖) ^ n := tsum_of_norm_bounded hgeom.hasSum hbound
    _ = ‖z‖⁻¹ * (1 - ‖A‖ / ‖z‖)⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hratio0 hratio]
    _ = (‖z‖ - ‖A‖)⁻¹ := by
        rw [one_sub_div hzpos.ne', inv_div, ← div_eq_inv_mul, div_div, mul_comm, ← div_div,
          div_self hzpos.ne', one_div]

/-- `-w (A - w)⁻¹ - 1 = -(A (A - w)⁻¹)` whenever `A - w` is a unit. -/
theorem neg_smul_inverse_sub_one (A : R) {w : ℂ} (hw : IsUnit (A - algebraMap ℂ R w)) :
    (-w) • Ring.inverse (A - algebraMap ℂ R w) - 1 =
      -(A * Ring.inverse (A - algebraMap ℂ R w)) := by
  have h := Ring.mul_inverse_cancel _ hw
  set Rw := Ring.inverse (A - algebraMap ℂ R w) with hRw
  have h' : A * Rw - w • Rw = 1 := by
    rw [← h, sub_mul, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  calc (-w) • Rw - 1 = (-w) • Rw - (A * Rw - w • Rw) := by rw [h']
    _ = -(A * Rw) := by rw [neg_smul]; abel

/-- Along any scalar sequence `w_k` with `‖w_k‖ → ∞`, `-w_k (A - w_k)⁻¹ → 1`. -/
theorem tendsto_neg_smul_inverse_sub_algebraMap (A : R) (h1 : ‖(1 : R)‖ ≤ 1)
    (w : ℕ → ℂ) (hw : Tendsto (fun k => ‖w k‖) atTop atTop) :
    Tendsto (fun k => (-(w k)) • Ring.inverse (A - algebraMap ℂ R (w k))) atTop (𝓝 1) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hev : ∀ᶠ k in atTop, ‖A‖ + 1 ≤ ‖w k‖ := hw.eventually_ge_atTop _
  have hbound : ∀ᶠ k in atTop,
      ‖(-(w k)) • Ring.inverse (A - algebraMap ℂ R (w k)) - 1‖ ≤ ‖A‖ * (‖w k‖ - ‖A‖)⁻¹ := by
    filter_upwards [hev] with k hk
    have hlt : ‖A‖ < ‖w k‖ := by linarith
    rw [neg_smul_inverse_sub_one A (isUnit_sub_algebraMap_of_norm_lt A hlt), norm_neg]
    calc ‖A * Ring.inverse (A - algebraMap ℂ R (w k))‖
        ≤ ‖A‖ * ‖Ring.inverse (A - algebraMap ℂ R (w k))‖ := norm_mul_le _ _
      _ ≤ ‖A‖ * (‖w k‖ - ‖A‖)⁻¹ :=
          mul_le_mul_of_nonneg_left (norm_inverse_sub_algebraMap_le A h1 hlt) (norm_nonneg _)
  have hlim : Tendsto (fun k => ‖A‖ * (‖w k‖ - ‖A‖)⁻¹) atTop (𝓝 0) := by
    have : Tendsto (fun k => ‖w k‖ - ‖A‖) atTop atTop := hw.atTop_add tendsto_const_nhds
    simpa using (tendsto_inv_atTop_zero.comp this).const_mul ‖A‖
  exact squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hbound hlim

/-- The resolvent identity
`(A - z)⁻¹ - (A - w)⁻¹ = (z - w) • (A - z)⁻¹ (A - w)⁻¹` when both are units. -/
theorem resolvent_sub_resolvent (A : R) {z w : ℂ} (hz : IsUnit (A - algebraMap ℂ R z))
    (hw : IsUnit (A - algebraMap ℂ R w)) :
    Ring.inverse (A - algebraMap ℂ R z) - Ring.inverse (A - algebraMap ℂ R w) =
      (z - w) • (Ring.inverse (A - algebraMap ℂ R z) * Ring.inverse (A - algebraMap ℂ R w)) := by
  set Rz := Ring.inverse (A - algebraMap ℂ R z)
  set Rw := Ring.inverse (A - algebraMap ℂ R w)
  have hz1 : Rz * (A - algebraMap ℂ R z) = 1 := Ring.inverse_mul_cancel _ hz
  have hw1 : (A - algebraMap ℂ R w) * Rw = 1 := Ring.mul_inverse_cancel _ hw
  have key : (A - algebraMap ℂ R w) - (A - algebraMap ℂ R z) = (z - w) • (1 : R) := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, sub_smul]
    abel
  calc Rz - Rw = Rz * ((A - algebraMap ℂ R w) * Rw) - (Rz * (A - algebraMap ℂ R z)) * Rw := by
        rw [hw1, hz1, mul_one, one_mul]
    _ = Rz * (((A - algebraMap ℂ R w) - (A - algebraMap ℂ R z)) * Rw) := by
        noncomm_ring
    _ = (z - w) • (Rz * Rw) := by
        rw [key, smul_mul_assoc, one_mul, mul_smul_comm]

end NormedAlgebra

end RenewalGeometry
