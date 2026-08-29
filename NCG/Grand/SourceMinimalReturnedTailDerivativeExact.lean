/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GTReturnedTail
import NCG.Grand.ReturnedFeedbackHankelMatrixRankExact
import NCG.Grand.HankelMinimality

/-!
# Source-minimal retained-tail derivative

This closes all clauses of `cor:GT-returned-tail-derivative`: the Neumann
series identity, descent to the canonical reachable/observable returned
quotient, stabilized literal block-Hankel rank, and minimality of that quotient
among every finite realization of the same returned kernels.
-/

open Matrix
open scoped Matrix.Norms.L2Operator

namespace NCG
namespace SourceMinimalReturnedTailDerivative

variable {l e : Type*} [Fintype l] [Fintype e]
  [DecidableEq l] [DecidableEq e]

/-- The canonical source indexed by a delay and a visible input. -/
noncomputable def canonicalReturnedSource
    (B : Matrix l e ℂ) (C : Matrix e l ℂ) (D : Matrix e e ℂ)
    (q : ℕ × (l → ℂ)) : ReturnedFeedbackSpace B C D :=
  ((returnedFeedbackTransition B C D) ^ q.1)
    (returnedFeedbackSource B C D q.2)

/-- The scalar table of all delayed returned kernels. -/
noncomputable def returnedKernelTable
    (B : Matrix l e ℂ) (C : Matrix e l ℂ) (D : Matrix e e ℂ)
    (f : ℕ × l) (q : ℕ × (l → ℂ)) : ℂ :=
  returnedFeedbackRead B C D f (canonicalReturnedSource B C D q)

theorem canonicalReturnedSource_reachable
    (B : Matrix l e ℂ) (C : Matrix e l ℂ) (D : Matrix e e ℂ) :
    Submodule.span ℂ (Set.range (canonicalReturnedSource B C D)) = ⊤ := by
  exact returnedFeedback_reachable B C D

theorem returnedFeedbackRead_separating
    (B : Matrix l e ℂ) (C : Matrix e l ℂ) (D : Matrix e e ℂ)
    (z : ReturnedFeedbackSpace B C D)
    (hz : ∀ f, returnedFeedbackRead B C D f z = 0) : z = 0 := by
  have hzmem : z ∈ ⨅ f, LinearMap.ker (returnedFeedbackRead B C D f) := by
    rw [Submodule.mem_iInf]
    intro f
    exact LinearMap.mem_ker.mpr (hz f)
  rw [returnedFeedback_reads_separate B C D] at hzmem
  exact hzmem

/-- Any finite linear realization of the complete returned-kernel table has
dimension at least the canonical reachable/observable quotient. -/
theorem returnedFeedback_minimum_dimension
    (B : Matrix l e ℂ) (C : Matrix e l ℂ) (D : Matrix e e ℂ)
    {N : Type*} [AddCommGroup N] [Module ℂ N] [FiniteDimensional ℂ N]
    (nst : (ℕ × (l → ℂ)) → N)
    (read : (ℕ × l) → N →ₗ[ℂ] ℂ)
    (hmatch : ∀ f q, read f (nst q) = returnedKernelTable B C D f q) :
    Module.finrank ℂ (ReturnedFeedbackSpace B C D) ≤ Module.finrank ℂ N := by
  let Ecan := hankelCoreEquiv
    (returnedKernelTable B C D)
    (canonicalReturnedSource B C D)
    (returnedFeedbackRead B C D)
    (fun _ _ => rfl)
    (canonicalReturnedSource_reachable B C D)
    (returnedFeedbackRead_separating B C D)
  have hmin := (hankel_minimality
    (returnedKernelTable B C D) nst read hmatch).2
  calc
    Module.finrank ℂ (ReturnedFeedbackSpace B C D) =
        Module.finrank ℂ (HankelCore (ℕ × (l → ℂ)) (ℕ × l)
          (returnedKernelTable B C D)) := LinearEquiv.finrank_eq Ecan
    _ ≤ Module.finrank ℂ N := hmin

/-- Every sufficiently deep literal panel `[B D^(i+j) C]` has the canonical
quotient dimension, so the stabilized Hankel rank equals the exact minimum
tail dimension. -/
theorem stabilized_returned_hankel_rank
    (B : Matrix l e ℂ) (C : Matrix e l ℂ) (D : Matrix e e ℂ)
    (p q : ℕ)
    (hp : Module.finrank ℂ (ReturnedFeedbackSpace B C D) ≤ p)
    (hq : Module.finrank ℂ (ReturnedFeedbackSpace B C D) ≤ q) :
    (returnedFeedbackHankelPanel B C D p q).rank =
      Module.finrank ℂ (ReturnedFeedbackSpace B C D) :=
  returnedFeedbackHankelPanel_rank B C D p q hp hq

end SourceMinimalReturnedTailDerivative
end NCG
