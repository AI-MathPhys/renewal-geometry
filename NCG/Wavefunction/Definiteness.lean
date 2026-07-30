/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Definiteness from central record sectors (wavefunction, Phase 1)

`prop:definiteness`: let `{Z_i}` be orthogonal central projections
with `Σ Z_i = 1`, and suppose all retained observables commute with
the record centre.  Then:

* `central_expectation_decomposes` — every retained expectation
  decomposes over the sectors,
  `Tr(Xρ) = Σ_i Tr(X · Z_iρZ_i)`: an observer conditioned on sector
  `i` sees exactly the conditional (Lüders) state
  `ρ_i = Z_iρZ_i / Tr(Z_iρ)`;
* `central_offdiag_invisible` — no retained observable detects
  coherence between distinct sectors:
  `Tr(X · Z_iρZ_j) = 0` for `i ≠ j`;
* `sector_weight_eq` — the conditional state is correctly
  normalized: `Tr(Z_iρZ_i) = Tr(Z_iρ)`.

Together with the pointer-instrument machinery
(`NCG.Upstream.pointer_instrument_sum`, `pointer_offdiag_vanish`)
and the Lüders Kraus decomposition (`NCG.lueders_kraus_sum`), this
closes the mechanism clause of the renewal collapse principle.
-/

namespace NCG

open Matrix

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]

omit [DecidableEq n] in
/-- Sector weights: `Tr(Z_iρZ_i) = Tr(Z_iρ)`, so the conditional
state `Z_iρZ_i / Tr(Z_iρ)` is trace one on its sector. -/
theorem sector_weight_eq {α : Type*} [CommRing α]
    (Z rho : Matrix n n α) (hidem : Z * Z = Z) :
    (Z * rho * Z).trace = (Z * rho).trace := by
  rw [Matrix.trace_mul_cycle, hidem]

omit [DecidableEq ι] in
/-- `prop:definiteness` (sector decomposition): if every retained
observable `X` commutes with the central projections
(`X Z_i = Z_i X`), then its expectation decomposes exactly over the
conditional sector states, `Tr(Xρ) = Σ_i Tr(X · Z_iρZ_i)`. -/
theorem central_expectation_decomposes {α : Type*} [CommRing α]
    (Z : ι → Matrix n n α) (rho X : Matrix n n α)
    (hidem : ∀ i, Z i * Z i = Z i)
    (hsum : ∑ i, Z i = 1)
    (hcomm : ∀ i, X * Z i = Z i * X) :
    (X * rho).trace = ∑ i, (X * (Z i * rho * Z i)).trace := by
  have hterm : ∀ i, (X * (Z i * rho * Z i)).trace
      = (X * (Z i * rho)).trace := by
    intro i
    calc (X * (Z i * rho * Z i)).trace
        = (X * (Z i * rho) * Z i).trace := by
          congr 1
          noncomm_ring
      _ = (Z i * X * (Z i * rho)).trace := by
          rw [Matrix.trace_mul_cycle]
      _ = (X * Z i * (Z i * rho)).trace := by
          rw [← hcomm i]
      _ = (X * (Z i * rho)).trace := by
          congr 1
          calc X * Z i * (Z i * rho) = X * (Z i * Z i * rho) := by
                noncomm_ring
            _ = X * (Z i * rho) := by rw [hidem i]
  rw [Finset.sum_congr rfl fun i _ => hterm i]
  have hdist : ∑ i, (X * (Z i * rho)).trace
      = (X * ((∑ i, Z i) * rho)).trace := by
    rw [Finset.sum_mul, Matrix.mul_sum, Matrix.trace_sum]
  rw [hdist, hsum, one_mul]

omit [DecidableEq n] [Fintype ι] [DecidableEq ι] in
/-- `prop:definiteness` (no inter-sector coherence): for retained
observables commuting with the centre, the off-diagonal sector
blocks are invisible, `Tr(X · Z_iρZ_j) = 0` for `i ≠ j` — coherence
between distinct record sectors is undetectable in the predictive
quotient. -/
theorem central_offdiag_invisible {α : Type*} [CommRing α]
    (Z : ι → Matrix n n α) (rho X : Matrix n n α)
    (horth : ∀ i j, i ≠ j → Z i * Z j = 0)
    (hcomm : ∀ i, X * Z i = Z i * X)
    {i j : ι} (hij : i ≠ j) :
    (X * (Z i * rho * Z j)).trace = 0 := by
  calc (X * (Z i * rho * Z j)).trace
      = (X * (Z i * rho) * Z j).trace := by
        congr 1
        noncomm_ring
    _ = (Z j * X * (Z i * rho)).trace := by
        rw [Matrix.trace_mul_cycle]
    _ = (X * Z j * (Z i * rho)).trace := by
        rw [← hcomm j]
    _ = (X * (Z j * Z i * rho)).trace := by
        congr 1
        noncomm_ring
    _ = 0 := by
        rw [horth j i (Ne.symm hij), zero_mul, mul_zero,
          Matrix.trace_zero]

end NCG
