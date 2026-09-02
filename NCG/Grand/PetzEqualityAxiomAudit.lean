/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.PetzEqualityExact

/-!
# Axiom audit for finite Petz equality

The reports below ensure that both the imported partial-trace equality theorem
and the local arbitrary-Kraus bridge use only Lean's standard foundational
axioms.
-/

#print axioms Matrix.partialTraceRightPetzMap_eq_of_relativeEntropy_eq_general_support
#print axioms NCG.Petz.deltaDPI_eq_zero_implies_petz_recovery
#print axioms NCG.Petz.deltaDPI_eq_zero_iff_petz_recovery
