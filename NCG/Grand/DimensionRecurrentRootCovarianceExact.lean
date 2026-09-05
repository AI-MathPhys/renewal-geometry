/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.DimensionRecurrentRoot

/-!
# The `S₄`-covariant recurrent-root bridge

The diagonal action of `S₄` has precisely two orbits on ordered endpoint
pairs: the diagonal and its complement.  Consequently every covariant
row-stochastic bridge has the manuscript's unique one-parameter form.  A
positive off-diagonal parameter joins every distinct pair and forces every
target-only sharp factor to be constant.
-/

open Finset

namespace NCG

/-- The recurrent tetrahedral bridge with off-diagonal weight `b`. -/
def recurrentK4Bridge (b : ℝ) (i j : Fin 4) : ℝ :=
  (1 - 3 * b) * (if i = j then 1 else 0)
    + b * (1 - if i = j then 1 else 0)

/-- Diagonal `S₄` covariance forces a matrix on endpoint pairs to be constant
on the diagonal and constant off the diagonal. -/
theorem s4CovariantBridge_twoOrbits
    (B : Fin 4 → Fin 4 → ℝ)
    (hcov : ∀ (σ : Equiv.Perm (Fin 4)) i j,
      B (σ i) (σ j) = B i j) :
    ∀ i j, B i j = if i = j then B 0 0 else B 0 1 := by
  intro i j
  by_cases hij : i = j
  · subst j
    let f : Fin 1 → Fin 4 := fun _ => i
    let g : Fin 1 → Fin 4 := fun _ => 0
    have hf : Function.Injective f := by
      intro a b _
      exact Subsingleton.elim _ _
    have hg : Function.Injective g := by
      intro a b _
      exact Subsingleton.elim _ _
    obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair f g hf hg
    have hi : σ i = 0 := by simpa [f, g] using hσ (0 : Fin 1)
    have h := hcov σ i i
    rw [hi] at h
    simpa using h.symm
  · let f : Fin 2 → Fin 4 := fun k => if k = 0 then i else j
    let g : Fin 2 → Fin 4 := fun k => if k = 0 then 0 else 1
    have hf : Function.Injective f := by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp [f] at hab ⊢
      · exact (hij hab).elim
      · exact (hij hab.symm).elim
    have hg : Function.Injective g := by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp [g] at hab ⊢
    obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair f g hf hg
    have hi : σ i = 0 := by simpa [f, g] using hσ (0 : Fin 2)
    have hj : σ j = 1 := by simpa [f, g] using hσ (1 : Fin 2)
    have h := hcov σ i j
    rw [hi, hj] at h
    simpa [hij] using h.symm

/-- A row-stochastic `S₄`-covariant bridge has uniquely the form
`(1-3b)I + b(11ᵀ-I)`, with `b` equal to any off-diagonal entry. -/
theorem s4CovariantStochasticBridge_unique
    (B : Fin 4 → Fin 4 → ℝ)
    (hcov : ∀ (σ : Equiv.Perm (Fin 4)) i j,
      B (σ i) (σ j) = B i j)
    (hstoch : ∀ i, ∑ j, B i j = 1) :
    ∃! b : ℝ, ∀ i j, B i j = recurrentK4Bridge b i j := by
  let b := B 0 1
  have horbit := s4CovariantBridge_twoOrbits B hcov
  have hrow := hstoch 0
  rw [Fin.sum_univ_four] at hrow
  have hdiag : B 0 0 = 1 - 3 * b := by
    have h02 : B 0 2 = B 0 1 := by simpa using horbit 0 2
    have h03 : B 0 3 = B 0 1 := by simpa using horbit 0 3
    rw [h02, h03] at hrow
    dsimp [b]
    linarith
  refine ⟨b, ?_, ?_⟩
  · intro i j
    rw [horbit]
    by_cases hij : i = j <;> simp [recurrentK4Bridge, hij, b, hdiag]
  · intro c hc
    have h := hc 0 1
    simp [recurrentK4Bridge, b] at h
    exact h.symm

/-- At positive slip every distinct endpoint pair is a positive-support edge;
this is the manuscript's connected overlap graph. -/
theorem recurrentK4Bridge_positiveSupport_connected
    {b : ℝ} (hb : 0 < b) :
    ∀ i j : Fin 4, i = j ∨ 0 < recurrentK4Bridge b i j := by
  intro i j
  by_cases hij : i = j
  · exact Or.inl hij
  · right
    simp [recurrentK4Bridge, hij, hb]

/-- Hence no nonconstant target-only sharp factor survives at positive slip:
any factor constant across positive-support overlaps is globally constant. -/
theorem recurrentK4Bridge_no_nonconstant_sharpFactor
    {b : ℝ} (hb : 0 < b) {Z : Type*} (f : Fin 4 → Z)
    (hf : ∀ i j, 0 < recurrentK4Bridge b i j → f i = f j) :
    ∀ i j, f i = f j := by
  intro i j
  rcases recurrentK4Bridge_positiveSupport_connected hb i j with hij | hij
  · exact congrArg f hij
  · exact hf i j hij

end NCG
