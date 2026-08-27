/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.VolterraMemory

/-!
# Exact Volterra/local-block equivalence

This supplies the explicit iff in `thm:continuum-memory-completion`.  The
causal memory register satisfies its local ODE and converts the convolution
term into `B y`; conversely the same identity turns the local first equation
back into the Volterra equation.  The existing uniqueness theorem shows this
is the only zero-initialized memory register.
-/

open MeasureTheory

namespace NCG

/-- A finite semigroup memory kernel is exactly Markovianized by its causal
auxiliary register. -/
theorem volterra_equation_iff_local_block_system
    {V W : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    (H : V →L[ℝ] V) (B : V →L[ℝ] W)
    (C : W →L[ℝ] V) (G : W →L[ℝ] W)
    (x : ℝ → W) (hx : Continuous x) :
    let y : ℝ → V := fun u =>
      ∫ s in (0 : ℝ)..u,
        (NormedSpace.exp ((u - s) • H)) (C (x s))
    ((∀ t, HasDerivAt x
        (G (x t) + ∫ s in (0 : ℝ)..t,
          B ((NormedSpace.exp ((t - s) • H)) (C (x s)))) t)
      ↔ ((∀ t, HasDerivAt x (G (x t) + B (y t)) t)
        ∧ ∀ t, HasDerivAt y (H (y t) + C (x t)) t))
      ∧ y 0 = 0 := by
  dsimp only
  constructor
  · constructor
    · intro hvolterra
      constructor
      · intro t
        have hloc := continuum_memory_localization H B C x hx t
        exact (hvolterra t).congr_deriv (by rw [hloc.2])
      · intro t
        exact (continuum_memory_localization H B C x hx t).1
    · rintro ⟨hxlocal, _hylocal⟩ t
      have hloc := continuum_memory_localization H B C x hx t
      exact (hxlocal t).congr_deriv (by rw [hloc.2])
  · simp

/-- The rank clause of the continuum completion, packaged with the literal
observability/controllability factorization. -/
theorem continuum_memory_hankel_rank_exact
    {d e : Type*} [Fintype d] [Fintype e]
    [DecidableEq d] [DecidableEq e]
    (B : Matrix d e ℂ) (H : Matrix e e ℂ) (C : Matrix e d ℂ)
    (p q : ℕ)
    (hObs : Function.Injective (memoryObservability B H p).mulVec)
    (hCtrl : Function.Surjective (memoryControllability H C q).mulVec) :
    memoryHankel B H C p q =
        memoryObservability B H p * memoryControllability H C q
      ∧ (memoryHankel B H C p q).rank = Fintype.card e := by
  exact ⟨memoryHankel_eq_observability_mul_controllability B H C p q,
    memoryHankel_rank_eq_carrier_dimension B H C p q hObs hCtrl⟩

end NCG
