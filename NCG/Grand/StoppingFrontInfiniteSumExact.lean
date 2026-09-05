/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.AssemblyRectangularStoppingFrontExact
import NCG.Grand.ExactMarkedCycleAnalysis

/-!
# Infinite stopping-front tightness

This upgrades the finite truncation in
`AssemblyRectangularStoppingFrontExact` to the actual convergent grade sums
of `thm:GT-stopping-front-tightness`.  Positivity of every summand lets the
global weighted bound control every finite partial sum; closedness of the
finite-dimensional positive cone then passes the uniform tail estimate to
the infinite tail.
-/

open Finset Matrix
open scoped ComplexOrder

namespace NCG
namespace StoppingFrontInfiniteSum

open AssemblyRectangularStoppingFront

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq m]

/-- A summable series of positive-semidefinite matrices has a
positive-semidefinite sum. -/
theorem tsum_posSemidef (F : ℕ → Matrix m m ℂ) (hF : Summable F)
    (hpos : ∀ k, (F k).PosSemidef) : (∑' k, F k).PosSemidef := by
  apply isClosed_posSemidef_finite.mem_of_tendsto hF.hasSum.tendsto_sum_nat
  filter_upwards [] with N
  exact Matrix.posSemidef_sum (Finset.range N) (fun k _ => hpos k)

/-- Reindex the grades strictly beyond `R` by a fresh natural number. -/
theorem sum_range_shift_eq_tail_filter (F : ℕ → Matrix m m ℂ) (R K : ℕ) :
    (∑ j ∈ Finset.range K, F (j + R + 1)) =
      ∑ k ∈ (Finset.range (R + 1 + K)).filter (fun k => R < k), F k := by
  refine Finset.sum_bij (fun j _ => j + R + 1) ?_ ?_ ?_ ?_
  · intro j hj
    rw [Finset.mem_filter]
    constructor
    · rw [Finset.mem_range] at hj ⊢
      omega
    · omega
  · intro j₁ _ j₂ _ h
    omega
  · intro k hk
    rw [Finset.mem_filter, Finset.mem_range] at hk
    refine ⟨k - R - 1, ?_, ?_⟩
    · rw [Finset.mem_range]
      omega
    · omega
  · intro j _
    rfl

/-- Infinite-tail version of (PA.15), assuming the weighted estimate for
every finite partial sum. -/
theorem stopping_front_tail_of_partial_bounds
    (S : Matrix n m ℂ) (E : ℕ → Matrix n n ℂ)
    (hE : ∀ k, (E k).PosSemidef)
    (w : ℕ → ℝ) (R : ℕ) (C : ℝ)
    (hwNonneg : ∀ k, 0 ≤ w k)
    (hwTail : ∀ k, R < k → w (R + 1) ≤ w k)
    (hwPos : 0 < w (R + 1))
    (hMsum : Summable fun k => Sᴴ * E k * S)
    (hbound : ∀ N, ((C : ℂ) • (1 : Matrix m m ℂ) -
      ∑ k ∈ Finset.range N, (w k : ℂ) • (Sᴴ * E k * S)).PosSemidef) :
    (((C / w (R + 1) : ℝ) : ℂ) • (1 : Matrix m m ℂ) -
      ∑' j, Sᴴ * E (j + R + 1) * S).PosSemidef := by
  have hshift : Summable fun j => Sᴴ * E (j + R + 1) * S := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      ((summable_nat_add_iff (R + 1)).mpr hMsum)
  apply isClosed_posSemidef_finite.mem_of_tendsto
    (tendsto_const_nhds.sub hshift.hasSum.tendsto_sum_nat)
  filter_upwards [] with K
  have hfinite := stopping_front_tail_operator S E hE w
    (R + 1 + K) R C hwNonneg
    (fun k hk _ => hwTail k hk) hwPos (hbound (R + 1 + K))
  have hreindex := sum_range_shift_eq_tail_filter
    (fun k => Sᴴ * E k * S) R K
  rw [hreindex]
  exact hfinite

/-- Exact infinite-grade form of (PA.14 ⇒ PA.15).  The two summability
hypotheses state that the displayed unweighted and weighted operator series
exist. -/
theorem stopping_front_tail_operator_infinite
    (S : Matrix n m ℂ) (E : ℕ → Matrix n n ℂ)
    (hE : ∀ k, (E k).PosSemidef)
    (w : ℕ → ℝ) (R : ℕ) (C : ℝ)
    (hwNonneg : ∀ k, 0 ≤ w k)
    (hwTail : ∀ k, R < k → w (R + 1) ≤ w k)
    (hwPos : 0 < w (R + 1))
    (hMsum : Summable fun k => Sᴴ * E k * S)
    (hWeightedSum : Summable fun k =>
      (w k : ℂ) • (Sᴴ * E k * S))
    (hWeightedBound : ((C : ℂ) • (1 : Matrix m m ℂ) -
      ∑' k, (w k : ℂ) • (Sᴴ * E k * S)).PosSemidef) :
    (((C / w (R + 1) : ℝ) : ℂ) • (1 : Matrix m m ℂ) -
      ∑' j, Sᴴ * E (j + R + 1) * S).PosSemidef := by
  let M : ℕ → Matrix m m ℂ := fun k => Sᴴ * E k * S
  have hMpos : ∀ k, (M k).PosSemidef :=
    fun k => (hE k).conjTranspose_mul_mul_same S
  have hWpos : ∀ k, ((w k : ℂ) • M k).PosSemidef := by
    intro k
    have hw : (0 : ℂ) ≤ (w k : ℂ) := by
      rw [Complex.zero_le_real]
      exact hwNonneg k
    exact (hMpos k).smul hw
  have hpartial : ∀ N, ((C : ℂ) • (1 : Matrix m m ℂ) -
      ∑ k ∈ Finset.range N, (w k : ℂ) • M k).PosSemidef := by
    intro N
    have htailSummable : Summable fun j => (w (j + N) : ℂ) • M (j + N) :=
      (summable_nat_add_iff N).mpr hWeightedSum
    have htail : (∑' j, (w (j + N) : ℂ) • M (j + N)).PosSemidef :=
      tsum_posSemidef _ htailSummable (fun j => hWpos (j + N))
    have hsplit := hWeightedSum.sum_add_tsum_nat_add N
    have hid : (C : ℂ) • (1 : Matrix m m ℂ) -
          ∑ k ∈ Finset.range N, (w k : ℂ) • M k =
        ((C : ℂ) • (1 : Matrix m m ℂ) -
          ∑' k, (w k : ℂ) • M k) +
          ∑' j, (w (j + N) : ℂ) • M (j + N) := by
      rw [← hsplit]
      abel
    rw [hid]
    exact hWeightedBound.add htail
  exact stopping_front_tail_of_partial_bounds S E hE w R C hwNonneg
    hwTail hwPos hMsum hpartial

end StoppingFrontInfiniteSum
end NCG
