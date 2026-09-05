/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.UniversalFeedbackMemory

/-!
# Feedback Hankel rank as a reachable--observable Krylov quotient

For the returned kernel `K_k = B D^k C`, this module realizes the infinite
block Hankel table on the external carrier.  The canonical Hankel quotient is
therefore exactly the span of the reachable vectors `D^k C u`, modulo those
reachable vectors annihilated by every future row `B D^i`.  Its dimension is
the minimal number of recurrent feedback coordinates.
-/

open Matrix

namespace NCG

/-- A Krylov-reachable external state, indexed by a delay and an old-carrier
input coordinate. -/
def feedbackReachState {d e : Type*} [Fintype e] [DecidableEq e]
    (C : Matrix e d ℂ) (D : Matrix e e ℂ) (p : ℕ × d) : e → ℂ :=
  fun x => (D ^ p.1 * C) x p.2

/-- A future observation row, indexed by a delay and an old-carrier output
coordinate. -/
def feedbackFutureFunctional {d e : Type*} [Fintype e] [DecidableEq e]
    (B : Matrix d e ℂ) (D : Matrix e e ℂ) (f : ℕ × d) :
    (e → ℂ) →ₗ[ℂ] ℂ where
  toFun v := ∑ x, (B * D ^ f.1) f.2 x * v x
  map_add' u v := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' a v := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    change (B * D ^ f.1) f.2 x * (a * v x) =
      a * ((B * D ^ f.1) f.2 x * v x)
    ring

/-- The scalarized infinite block-Hankel table of the feedback kernel. -/
def feedbackHankelTable {d e : Type*} [Fintype e] [DecidableEq e]
    (B : Matrix d e ℂ) (C : Matrix e d ℂ) (D : Matrix e e ℂ)
    (f p : ℕ × d) : ℂ :=
  (B * D ^ (f.1 + p.1) * C) f.2 p.2

/-- Evaluation of a future row on a reachable state is exactly the
corresponding feedback Hankel entry. -/
theorem feedbackFutureFunctional_reachState {d e : Type*} [Fintype e]
    [DecidableEq e] (B : Matrix d e ℂ) (C : Matrix e d ℂ)
    (D : Matrix e e ℂ) (f p : ℕ × d) :
    feedbackFutureFunctional B D f (feedbackReachState C D p) =
      feedbackHankelTable B C D f p := by
  change (∑ x, (B * D ^ f.1) f.2 x * (D ^ p.1 * C) x p.2) =
    (B * D ^ (f.1 + p.1) * C) f.2 p.2
  rw [← Matrix.mul_apply]
  congr 1
  rw [pow_add]
  simp only [Matrix.mul_assoc]

/-- The manuscript's feedback-rank formula.  The reachable external Krylov
space modulo its future-unobservable part is canonically equivalent to the
Hankel column space, whose dimension is consequently bounded by the external
carrier dimension. -/
theorem feedbackHankel_reachableObservableQuotient
    {d e : Type*} [Fintype e] [DecidableEq e]
    (B : Matrix d e ℂ) (C : Matrix e d ℂ) (D : Matrix e e ℂ) :
    Nonempty
      ((↥(Submodule.span ℂ (Set.range (feedbackReachState C D)))
          ⧸ (Submodule.comap
            (Submodule.span ℂ (Set.range (feedbackReachState C D))).subtype
            (⨅ f, LinearMap.ker (feedbackFutureFunctional B D f))))
        ≃ₗ[ℂ]
          ↥(Submodule.span ℂ
            (Set.range fun p f => feedbackHankelTable B C D f p)))
    ∧ Module.finrank ℂ
        (Submodule.span ℂ
          (Set.range fun p f => feedbackHankelTable B C D f p))
      ≤ Fintype.card e := by
  have hminimal := hankel_minimality
    (feedbackHankelTable B C D)
    (feedbackReachState C D)
    (feedbackFutureFunctional B D)
    (feedbackFutureFunctional_reachState B C D)
  refine ⟨hminimal.1, hminimal.2.trans_eq ?_⟩
  exact Module.finrank_pi ℂ

end NCG
