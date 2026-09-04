/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteCTMCHomogeneousRestartLawExact

/-! Standard-axiom audit for the concrete homogeneous CTMC restart law. -/

#print axioms
  NCG.FiniteCTMCHomogeneousRestartLaw.resetShift_one_eq_canonicalRestart
#print axioms
  NCG.FiniteCTMCHomogeneousRestartLaw.jumpSequenceLaw_pointMass_eq_continuation
#print axioms
  NCG.FiniteCTMCHomogeneousRestartLaw.map_continuation_resetShift
#print axioms
  NCG.FiniteCTMCHomogeneousRestartLaw.map_continuation_resetShift_eq_jumpSequenceLaw

