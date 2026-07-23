/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The covariant discrete renewal Hamiltonian

**Definition `def:curved-discrete`** (encoding): the covariant discrete
renewal Hamiltonian is assembled from a spatially varying direction
system — weights, directions, and the midpoint-sampled second-moment
field — acting through the Dirac matrices.  We encode the datum
(`NCG.CurvedDiscreteDatum`); its matrix layer (Hermiticity of the
frozen multiplier, `NCG.KreinCliffordDatum.multiplier_star`, and the
scalar symbol square, `…multiplier_square`) is the proved content of
Lemma `lem:curved-selfadjoint` at each frozen point.  The Sobolev-core
self-adjointness and the strong-resolvent curved limit are the noted
analytic steps. -/

namespace NCG

/-- **Definition `def:curved-discrete`** (encoding): the covariant
discrete Hamiltonian datum — mesh, clock normalisation, and the
pointwise direction system with its weights. -/
structure CurvedDiscreteDatum (X : Type*) (m d : ℕ) where
  /-- the mesh scale -/
  h : ℝ
  /-- the clock normalisation -/
  κ : ℝ
  /-- pointwise reset directions -/
  θ : X → Fin m → Fin d → ℝ
  /-- pointwise weights -/
  p : X → Fin m → ℝ
  h_pos : 0 < h
  κ_pos : 0 < κ
  p_nonneg : ∀ x a, 0 ≤ p x a
  p_sum : ∀ x, ∑ a, p x a = 1

end NCG
