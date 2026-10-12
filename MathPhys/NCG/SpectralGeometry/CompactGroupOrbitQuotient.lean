/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Orbit spaces of compact group actions

Split out of `MathPhys.Spectralization.CompactFiniteStageSystem`: a compact topological
group acting continuously on a compact Hausdorff space acts properly
(`properSMul_of_compactSpace`), so the orbit space is compact Hausdorff
(`compactSpace_orbitQuotient`, `t2Space_orbitQuotient`).
-/

set_option linter.unusedSectionVars false

open Filter Topology Set MulAction

noncomputable section

namespace MathPhys.CompactFiniteStage

/-! ### Compact group quotients -/

section CompactGroupQuotient

variable {G X : Type*} [Group G] [TopologicalSpace G] [CompactSpace G]
  [MulAction G X] [TopologicalSpace X] [CompactSpace X] [T2Space X] [ContinuousSMul G X]

/-- A compact group acting continuously on a compact Hausdorff space acts properly. -/
theorem properSMul_of_compactSpace : ProperSMul G X :=
  ⟨(continuous_smul.prodMk continuous_snd).isProperMap⟩

/-- The orbit space of a compact group acting continuously on a compact Hausdorff space is
Hausdorff. -/
theorem t2Space_orbitQuotient : T2Space (orbitRel.Quotient G X) := by
  have := properSMul_of_compactSpace (G := G) (X := X)
  exact t2Space_quotient_mulAction_of_properSMul

/-- The orbit space of a compact space is compact. -/
theorem compactSpace_orbitQuotient : CompactSpace (orbitRel.Quotient G X) :=
  Quotient.compactSpace

end CompactGroupQuotient

end MathPhys.CompactFiniteStage
