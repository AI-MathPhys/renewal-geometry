/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteCTMCRestartPrefixLawExact

/-! Standard-axiom audit for the concrete homogeneous CTMC restart law. -/

#print axioms
  NCG.FiniteCTMCRestartPrefixLaw.resetShiftPrefix_appendHistory
#print axioms
  NCG.FiniteCTMCRestartPrefixLaw.partialTraj_step_apply
#print axioms
  NCG.FiniteCTMCRestartPrefixLaw.map_step_resetShiftPrefix
#print axioms
  NCG.FiniteCTMCRestartPrefixLaw.map_partialTraj_resetShiftPrefix

