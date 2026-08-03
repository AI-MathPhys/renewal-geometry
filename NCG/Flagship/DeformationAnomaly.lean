/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Exact five-term deformation anomaly
  (`thm:deformation-anomaly-master`, flagship manuscript)

* `interface_term_identity`: the boxed interface term — for an
  idempotent physical projection `P` with complement `Q = 1 - P`,
  expanding `P[A,B]P` with `I = P + Q` gives exactly
  `P[A,B]P = [PAP, PBP] + (PAQBP - PBQAP)`,
  so the shortened commutator differs from the full one by the
  interface term `PAQBP - PBQAP` and nothing else;
* `five_term_telescope`: the telescoping identity — the five
  consecutive differences (source, normal, connection, interface,
  scaling) sum exactly to the total defect
  `X₀ - X₅`, with no hidden cancellation, so the target
  hypersurface-deformation bracket follows iff all five vanish.

Rendering disclosed: the identification of the five intermediate
objects `X₁, …, X₄` (the separately shortened commutator, its
tangential-source projection, the metric-predicted structure map,
and the Levi–Civita realization) with the manuscript's concrete
constraint operators is the model layer; the identity content —
the interface expansion and the exact telescope — is proved here.
-/

namespace NCG

/-- Boxed interface term: for idempotent `P` and `Q = 1 - P`,
`P[A,B]P = [PAP, PBP] + (PAQBP - PBQAP)`. -/
theorem interface_term_identity {R : Type*} [Ring R]
    (P A B : R) (hP : P * P = P) :
    P * (A * B - B * A) * P
    = ((P * A * P) * (P * B * P) - (P * B * P) * (P * A * P))
      + (P * A * (1 - P) * B * P - P * B * (1 - P) * A * P) := by
  have h3 : (P * A * P) * (P * B * P) = P * A * P * B * P := by
    calc (P * A * P) * (P * B * P)
        = P * A * (P * P) * B * P := by noncomm_ring
      _ = P * A * P * B * P := by rw [hP]
  have h4 : (P * B * P) * (P * A * P) = P * B * P * A * P := by
    calc (P * B * P) * (P * A * P)
        = P * B * (P * P) * A * P := by noncomm_ring
      _ = P * B * P * A * P := by rw [hP]
  rw [h3, h4]
  noncomm_ring

/-- The five-term telescope: consecutive differences sum exactly
to the total defect. -/
theorem five_term_telescope {M : Type*} [AddCommGroup M]
    (X0 X1 X2 X3 X4 X5 : M) :
    X0 - X5 = (X0 - X1) + (X1 - X2) + (X2 - X3) + (X3 - X4)
      + (X4 - X5) := by
  abel

end NCG
