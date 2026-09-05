/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GTSectorResolution
import NCG.Grand.GTSourceVariance
import NCG.Grand.GTRankTraceIndefiniteDirectExact

/-!
# Parallel population and causal-signed certificates

Exact finite realization of `thm:GRH-parallel-signed-certificate`.  The
functional-equation pair histories carry a four-sector orthogonal resolution:
conditional record innovation, covariant demand, open current, and cycle
current.  Independently, the same typed pair label carries the finite Weil
positive-plus-hyperbolic compression and its rank--trace population bound.
-/

open Matrix Finset
open scoped ComplexOrder MatrixOrder

namespace NCG
namespace GRHParallelSignedCertificateExact

abbrev PairSector := Fin 4

def innovation : PairSector := 0
def demand : PairSector := 1
def openCurrent : PairSector := 2
def cycle : PairSector := 3

/-- The four physical pair-history sectors at the actual first-return record. -/
structure PairResolution (n : Type) [Fintype n] [DecidableEq n] where
  projection : PairSector → Matrix n n ℂ
  sum_eq_one : ∑ s, projection s = 1
  selfAdjoint : ∀ s, (projection s)ᴴ = projection s
  idempotent : ∀ s, projection s * projection s = projection s

variable {n m Ω Y : Type} [Fintype n] [DecidableEq n]
  [Fintype m] [DecidableEq m] [Fintype Ω] [Fintype Y]

def pairSectorGram (R : PairResolution n) (N : Matrix n m ℂ)
    (s : PairSector) : Matrix m m ℂ :=
  Nᴴ * R.projection s * N

/-- GRH.3 with the four sectors named literally. -/
theorem pair_source_four_sector_decomposition
    (R : PairResolution n) (N : Matrix n m ℂ) :
    Nᴴ * N =
      pairSectorGram R N innovation + pairSectorGram R N demand +
        pairSectorGram R N openCurrent + pairSectorGram R N cycle := by
  have h := (gt_sector_resolution R.projection N R.sum_eq_one
    R.selfAdjoint R.idempotent).1
  rw [Fin.sum_univ_four] at h
  simpa [pairSectorGram, innovation, demand, openCurrent, cycle] using h

theorem pair_sectors_positive_and_zero_iff
    (R : PairResolution n) (N : Matrix n m ℂ) :
    (∀ s, (pairSectorGram R N s).PosSemidef) ∧
      ∀ s, pairSectorGram R N s = 0 ↔ R.projection s * N = 0 := by
  have h := gt_sector_resolution R.projection N R.sum_eq_one
    R.selfAdjoint R.idempotent
  exact ⟨h.2.2.1, h.2.2.2⟩

/-- The first pair sector is the conditional variance innovation from SK.3.
The identification hypothesis is precisely the statement that the actual
first-return projection is the independently constructed first sector. -/
theorem pair_innovation_conditional_variance
    (R : PairResolution n) (N : Matrix n m ℂ)
    (ν : Ω → ℂ) (S Sbar : Ω → Matrix Y m ℂ)
    (hcross1 : ∑ ω, ν ω • ((S ω - Sbar ω)ᴴ * Sbar ω) = 0)
    (hcross2 : ∑ ω, ν ω • ((Sbar ω)ᴴ * (S ω - Sbar ω)) = 0)
    (hidentify : pairSectorGram R N innovation =
      ∑ ω, ν ω • ((S ω - Sbar ω)ᴴ * (S ω - Sbar ω))) :
    (∑ ω, ν ω • ((S ω)ᴴ * S ω) =
        (∑ ω, ν ω • ((Sbar ω)ᴴ * Sbar ω)) +
          pairSectorGram R N innovation) := by
  rw [hidentify]
  exact gt_source_record_variance ν S Sbar hcross1 hcross2

/-- Complete parallel certificate.  The pair-source Hodge identity and the
finite Weil population inequality share the typed pair label but make no
spectral-complement identification, exactly as required by the manuscript. -/
theorem parallel_population_and_causal_signed_certificates
    (R : PairResolution n) (N : Matrix n m ℂ)
    (ν : Ω → ℂ) (S Sbar : Ω → Matrix Y m ℂ)
    (hcross1 : ∑ ω, ν ω • ((S ω - Sbar ω)ᴴ * Sbar ω) = 0)
    (hcross2 : ∑ ω, ν ω • ((Sbar ω)ᴴ * (S ω - Sbar ω)) = 0)
    (hidentify : pairSectorGram R N innovation =
      ∑ ω, ν ω • ((S ω - Sbar ω)ᴴ * (S ω - Sbar ω)))
    {d : ℕ} (P Q : Matrix (Fin d) (Fin d) ℂ)
    (hP : P.PosSemidef) (hQ : Q.IsHermitian)
    (s p : ℕ) (hs : P.rank ≤ s)
    (hp : (Upstream.PrimitiveWeight.posPart hQ).rank ≤ p) :
    (Nᴴ * N =
      pairSectorGram R N innovation + pairSectorGram R N demand +
        pairSectorGram R N openCurrent + pairSectorGram R N cycle)
    ∧ (∀ j, (pairSectorGram R N j).PosSemidef)
    ∧ (∑ ω, ν ω • ((S ω)ᴴ * S ω) =
        (∑ ω, ν ω • ((Sbar ω)ᴴ * Sbar ω)) +
          pairSectorGram R N innovation)
    ∧ ((s : ℝ) ≥ 2 * P.trace.re + 4 * Q.trace.re - 4 * p -
        GTRankTraceIndefiniteDirectExact.frobeniusSq (P + Q)) := by
  refine ⟨pair_source_four_sector_decomposition R N,
    (pair_sectors_positive_and_zero_iff R N).1,
    pair_innovation_conditional_variance R N ν S Sbar hcross1 hcross2 hidentify,
    ?_⟩
  exact (GTRankTraceIndefiniteDirectExact.gt_rank_trace_indefinite_direct
    P Q hP hQ s p hs hp).2

end GRHParallelSignedCertificateExact
end NCG
