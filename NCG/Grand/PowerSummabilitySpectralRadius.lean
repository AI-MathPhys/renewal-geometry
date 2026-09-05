/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.Analysis.Normed.Algebra.GelfandFormula

/-!
# Power summability and spectral radius

For an element of a complex Banach algebra, absolute summability of its powers
is equivalent to having spectral radius strictly smaller than one.  The proof
uses Gelfand's formula to find one strictly contractive power, then decomposes
the full series into its finitely many residue classes modulo that power.
-/

open Filter
open scoped NNReal ENNReal Topology

namespace NCG

set_option maxHeartbeats 800000 in
-- Gelfand-formula reindexing normalizes a dependent `Fin N` residue type.
/-- Absolute summability of all powers in a complex Banach algebra is
equivalent to strict spectral stability. -/
theorem summable_norm_powers_iff_spectralRadius_lt_one
    {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]
    [Nontrivial A] [NormOneClass A] (a : A) :
    Summable (fun n : ℕ => ‖a ^ n‖) ↔ spectralRadius ℂ a < 1 := by
  constructor
  · intro hsum
    have hzero : Tendsto (fun n : ℕ => ‖a ^ n‖) atTop (𝓝 0) :=
      hsum.tendsto_atTop_zero
    have hevent : ∀ᶠ n : ℕ in atTop, ‖a ^ n‖ < 1 :=
      (tendsto_order.1 hzero).2 1 zero_lt_one
    obtain ⟨N, hN⟩ := eventually_atTop.1 hevent
    have hp : ‖a ^ (N + 1)‖ < 1 := hN (N + 1) (Nat.le_succ N)
    have hp' : (‖a ^ (N + 1)‖₊ : ℝ≥0∞) < 1 := by
      exact_mod_cast hp
    calc
      spectralRadius ℂ a
          ≤ (‖a ^ (N + 1)‖₊ : ℝ≥0∞) ^ (1 / (N + 1) : ℝ) *
              (‖(1 : A)‖₊ : ℝ≥0∞) ^ (1 / (N + 1) : ℝ) :=
        spectrum.spectralRadius_le_pow_nnnorm_pow_one_div ℂ a N
      _ = (‖a ^ (N + 1)‖₊ : ℝ≥0∞) ^ (1 / (N + 1) : ℝ) := by simp
      _ < 1 := ENNReal.rpow_lt_one hp' (by positivity)
  · intro hradius
    have hg := spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius a
    have hevent : ∀ᶠ n : ℕ in atTop,
        (‖a ^ n‖₊ : ℝ≥0∞) ^ (1 / n : ℝ) < 1 :=
      (tendsto_order.1 hg).2 1 hradius
    obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hevent
    let N := N₀ + 1
    have hNpos : 0 < N := by simp [N]
    have hroot : (‖a ^ N‖₊ : ℝ≥0∞) ^ (1 / N : ℝ) < 1 :=
      hN₀ N (by simp [N])
    have hpowENN : (‖a ^ N‖₊ : ℝ≥0∞) < 1 := by
      rw [← ENNReal.rpow_lt_rpow_iff (by positivity : (0 : ℝ) < 1 / N)]
      simpa using hroot
    have hpow : ‖a ^ N‖ < 1 := by exact_mod_cast hpowENN
    have hfiber : ∀ r : Fin N,
        Summable (fun q : ℕ => ‖a ^ (N * q + (r : ℕ))‖) := by
      intro r
      have hgeom : Summable (fun q : ℕ => ‖a ^ N‖ ^ q * ‖a ^ (r : ℕ)‖) :=
        (summable_geometric_of_lt_one (norm_nonneg _) hpow).mul_right _
      apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hgeom
      intro q
      rw [pow_add]
      calc
        ‖a ^ (N * q) * a ^ (r : ℕ)‖
            ≤ ‖a ^ (N * q)‖ * ‖a ^ (r : ℕ)‖ := norm_mul_le _ _
        _ ≤ ‖a ^ N‖ ^ q * ‖a ^ (r : ℕ)‖ :=
          mul_le_mul_of_nonneg_right (by simpa [pow_mul] using norm_pow_le (a ^ N) q)
            (norm_nonneg _)
    have hprod : Summable (fun rq : Fin N × ℕ =>
        ‖a ^ (N * rq.2 + (rq.1 : ℕ))‖) := by
      apply (summable_prod_of_nonneg (fun _ => norm_nonneg _)).2
      exact ⟨hfiber, (hasSum_fintype (fun r : Fin N =>
        ∑' q : ℕ, ‖a ^ (N * q + (r : ℕ))‖)).summable⟩
    have hswap : Summable (fun qr : ℕ × Fin N =>
        ‖a ^ (N * qr.1 + (qr.2 : ℕ))‖) := by
      simpa [Function.comp_def] using
        (Equiv.prodComm ℕ (Fin N)).summable_iff.mpr hprod
    have hreindexed := (Nat.divModEquiv N).summable_iff.mpr hswap
    simpa [Function.comp_def, Nat.div_add_mod] using hreindexed

end NCG
