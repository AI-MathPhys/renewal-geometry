/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Cross-chirality adjoint incidence
  (`thm:cross-chirality-adjoint-incidence`,
   `corollary:basis-independent-adjoint-lower-bound`, SM_emergence)

* `declared_spectra_distinct` — the declared up-quark and neutrino
  singular-value triples are distinct (exact decimal comparison);
* `cross_chirality_adjoint_incidence` — if the adjoint block `B_u`
  vanished, the up and neutrino Yukawas would coincide and so would
  their singular spectra; the declared spectra differ, so
  `B_u ≠ 0` (and likewise `B_d ≠ 0` from the down/charged-lepton
  spectra, `declared_down_spectra_distinct`);
* `adjoint_lower_bound_certificate` — with the sharp two-sided
  unitary-orbit distance
  `min ‖A - UBV†‖²_F = Σ(σᵢ(A) - σᵢ(B))²` (Mirsky, the disclosed
  interface), the up-sector spectral gap alone certifies the
  frame-independent bound `(‖B_u‖² + ‖B_d‖²)/g₂² ≥ 0.143237380173`
  — the adjoint incidence cannot be removed by any basis choice.

The Lie-theoretic closing step (the span of `uT₄u†` is the full
adjoint of `𝔰𝔩₄`) is the disclosed representation-theory layer.
-/

namespace NCG

/-- The declared up-quark singular values (units of `g₂`). -/
noncomputable def sigmaU : Fin 3 → ℝ :=
  ![1.08065388550, 0.00469299688, 5.81452e-6]

/-- The declared neutrino singular values (units of `g₂`). -/
noncomputable def sigmaNu : Fin 3 → ℝ :=
  ![0.68013559244, 0.17885949107, 0]

/-- The declared spectra are distinct. -/
theorem declared_spectra_distinct : sigmaU ≠ sigmaNu := by
  intro h
  have h0 := congrFun h 0
  simp only [sigmaU, sigmaNu, Matrix.cons_val_zero] at h0
  norm_num at h0

/-- `thm:cross-chirality-adjoint-incidence`: if `B_u = 0` forced
`Y_u = Ỹ_ν` (common Pati–Salam block), the singular spectra would
coincide; the declared spectra differ, so `B_u ≠ 0`. -/
theorem cross_chirality_adjoint_incidence {M : Type*} [Zero M]
    {Yu Ynu Bu : M} (spec : M → (Fin 3 → ℝ))
    (hcouple : Bu = 0 → Yu = Ynu)
    (hσu : spec Yu = sigmaU) (hσν : spec Ynu = sigmaNu) :
    Bu ≠ 0 := by
  intro h0
  have h := hcouple h0
  apply declared_spectra_distinct
  rw [← hσu, ← hσν, h]

/-- `corollary:basis-independent-adjoint-lower-bound`: with the
Mirsky unitary-orbit distance as interface, the up-sector spectral
gap alone certifies the frame-independent bound. -/
theorem adjoint_lower_bound_certificate {bu bd : ℝ} (hbd : 0 ≤ bd)
    (hmirsky : ∑ i, (sigmaU i - sigmaNu i) ^ 2 ≤ bu) :
    0.143237380173 ≤ bu + bd := by
  have hval : (0.190748 : ℝ) ≤ ∑ i, (sigmaU i - sigmaNu i) ^ 2 := by
    norm_num [sigmaU, sigmaNu, Fin.sum_univ_succ]
  linarith

end NCG
