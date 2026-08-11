/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.Analysis.CStarAlgebra.Unitary.Connected

/-!
# Principal-log reconstruction for a calibrated Store link
-/

namespace NCG

/-- The principal logarithm of a unitary, represented by the canonical
self-adjoint argument on the principal branch. -/
noncomputable def principalUnitaryLog
    {A : Type*} [CStarAlgebra A] (u : unitary A) : A :=
  Complex.I • (Unitary.argSelfAdjoint u : A)

/-- (R1) Exact reconstruction of a self-adjoint generator from its calibrated
unitary link in the principal-logarithm domain. -/
theorem principalUnitaryLog_reconstructs_generator
    {A : Type*} [CStarAlgebra A]
    (G : selfAdjoint A) (t : ℝ) (ht0 : t ≠ 0)
    (hbranch : ‖(-t) • G‖ < Real.pi) :
    ((Complex.I / t : ℂ) •
        principalUnitaryLog (selfAdjoint.expUnitary ((-t) • G))) = (G : A) := by
  rw [principalUnitaryLog,
    argSelfAdjoint_expUnitary hbranch]
  have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht0
  have hc : (Complex.I / (t : ℂ)) * Complex.I * ((-t : ℝ) : ℂ) = 1 := by
    field_simp [htc]
    rw [Complex.I_sq]
    push_cast
    ring
  change (Complex.I / (t : ℂ)) •
      (Complex.I • (((-t : ℝ) : ℂ) • (G : A))) = (G : A)
  rw [smul_smul, smul_smul, hc, one_smul]

end NCG
