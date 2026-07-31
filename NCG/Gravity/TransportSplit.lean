/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The projected transport decomposition
  (`thm:transport-decomp`, GR_emergence)

The trace mechanism of the band-transport decomposition
`∇^band = ∇^LC + ∇^mom + 𝒜_ren`:

* `skewAdjoint_trace_re_zero` — an anti-Hermitian matrix has purely
  imaginary trace, so the geometric terms (spacetime-frame plus
  momentum-space Berry transport, anti-Hermitian by
  `lem:berry-antiherm` = `NCG.berry_antihermitian`) drop from every
  real-trace response;
* `transport_decomp_trace` — for any decomposition
  `A = A_geo + A_grad + A_irr` with `A_geo` anti-Hermitian,
  `Re Tr A = Re Tr A_grad + Re Tr A_irr`: only the non-geometric
  parts can change a scalar modulus response, which is the
  boxed `κ_ren = r⁻¹Re Tr 𝒜_ren` selection.

The pseudodifferential construction of the three terms (the
`Π₊dΠ₊` symbol split) is the disclosed semiclassical layer.
-/

namespace NCG

open Matrix

variable {n : ℕ}

/-- An anti-Hermitian matrix has purely imaginary trace. -/
theorem skewAdjoint_trace_re_zero {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.conjTranspose = -A) :
    (Matrix.trace A).re = 0 := by
  have h1 : Matrix.trace A.conjTranspose = -Matrix.trace A := by
    rw [hA, Matrix.trace_neg]
  rw [Matrix.trace_conjTranspose] at h1
  have h2 : (starRingEnd ℂ) (Matrix.trace A) = -Matrix.trace A := h1
  have h3 := congrArg Complex.re h2
  simp only [Complex.conj_re, Complex.neg_re] at h3
  linarith

/-- `thm:transport-decomp` (trace selection): in the decomposition
`A = A_geo + A_grad + A_irr` with anti-Hermitian geometric part, the
real trace sees only the gradient and irreversible parts. -/
theorem transport_decomp_trace
    {A Ageo Agrad Airr : Matrix (Fin n) (Fin n) ℂ}
    (hsplit : A = Ageo + Agrad + Airr)
    (hgeo : Ageo.conjTranspose = -Ageo) :
    (Matrix.trace A).re
      = (Matrix.trace Agrad).re + (Matrix.trace Airr).re := by
  rw [hsplit, Matrix.trace_add, Matrix.trace_add, Complex.add_re,
    Complex.add_re, skewAdjoint_trace_re_zero hgeo]
  ring

end NCG
