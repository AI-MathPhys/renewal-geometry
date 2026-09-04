/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteCTMCAdmissiblePathRestartExact

/-! Axiom audit for admissible first-jump restart. -/

#print axioms NCG.FiniteCTMCAdmissiblePathRestart.cumulativeHold_tail_add_first
#print axioms NCG.FiniteCTMCAdmissiblePathRestart.measurable_tailJumpSequence
#print axioms NCG.FiniteCTMCAdmissiblePathRestart.cumulativeJumpTime_tail_add_first
#print axioms NCG.FiniteCTMCAdmissiblePathRestart.tailJumpSequence_mem
#print axioms NCG.FiniteCTMCAdmissiblePathRestart.measurable_tailAdmissibleJumpSequence
#print axioms NCG.FiniteCTMCAdmissiblePathRestart.admissibleJumpIndex_eq_zero_iff
#print axioms NCG.FiniteCTMCAdmissiblePathRestart.admissibleJumpIndex_eq_tail_add_one
#print axioms NCG.FiniteCTMCAdmissiblePathRestart.admissibleStateAt_eq_tail
#print axioms NCG.FiniteCTMCAdmissiblePathRestart.finiteHorizonAdditiveReward_eq_firstJump_add_tail
#print axioms NCG.FiniteCTMCAdmissiblePathRestart.feynmanKacIntegrand_eq_noJump
#print axioms NCG.FiniteCTMCAdmissiblePathRestart.feynmanKacIntegrand_eq_firstJump_mul_tail
