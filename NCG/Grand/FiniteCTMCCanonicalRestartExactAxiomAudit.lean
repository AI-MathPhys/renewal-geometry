/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteCTMCCanonicalRestartExact

/-! Standard-axiom audit for concrete CTMC restart machinery. -/

#print axioms
  NCG.FiniteCTMCCanonicalRestart.measurable_canonicalRestart
#print axioms
  NCG.FiniteCTMCCanonicalRestart.canonicalRestart_initial
#print axioms
  NCG.FiniteCTMCCanonicalRestart.admissibleJumpIndex_resetAdmissible
#print axioms
  NCG.FiniteCTMCCanonicalRestart.finiteHorizonAdditiveReward_resetAdmissible
#print axioms
  NCG.FiniteCTMCCanonicalRestart.feynmanKacIntegrand_resetAdmissible
#print axioms
  NCG.FiniteCTMCCanonicalRestart.feynmanKacIntegrand_eq_firstJump_mul_canonicalRestart

