/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.JointCommutatorContinuousOperator

/-!
# The finite joint-commutator resolvent

At every positive shift, the commutant Laplacian plus the scalar shift is
injective by its graph-energy identity, hence bijective in finite dimension.
Its continuous inverse is the canonical finite joint-commutator resolvent and
automatically satisfies the weak graph-resolvent equation.
-/

open scoped InnerProductSpace

noncomputable section

namespace NCG

/-- The shifted finite commutant Laplacian. -/
noncomputable def shiftedCommutantLaplacianCLM
    {n : Type*} [Fintype n] {s : ℕ}
    (c : Fin s → Matrix n n ℂ) (lam : ℝ) :
    EuclideanSpace ℂ (n × n) →L[ℂ] EuclideanSpace ℂ (n × n) :=
  commutantLaplacianCLM c + (lam : ℂ) • 1

@[simp] theorem shiftedCommutantLaplacianCLM_apply
    {n : Type*} [Fintype n] {s : ℕ}
    (c : Fin s → Matrix n n ℂ) (lam : ℝ)
    (x : EuclideanSpace ℂ (n × n)) :
    shiftedCommutantLaplacianCLM c lam x =
      commutantLaplacianCLM c x + (lam : ℂ) • x := by
  simp [shiftedCommutantLaplacianCLM]

/-- A positive scalar shift makes the finite commutant Laplacian injective. -/
theorem shiftedCommutantLaplacianCLM_injective
    {n : Type*} [Fintype n] {s : ℕ}
    (c : Fin s → Matrix n n ℂ) (lam : ℝ) (hlam : 0 < lam) :
    Function.Injective (shiftedCommutantLaplacianCLM c lam) := by
  intro x y hxy
  let z : EuclideanSpace ℂ (n × n) := x - y
  have hz : shiftedCommutantLaplacianCLM c lam z = 0 := by
    dsimp only [z]
    rw [map_sub, hxy, sub_self]
  have heq := jointCommutator_resolventEquation_of_laplacianEquation
    c lam 0 z (by
      simpa only [shiftedCommutantLaplacianCLM_apply] using hz)
  have heuler := heq.weakEuler ⟨z, Submodule.mem_top⟩
  change Complex.re (inner ℂ (jointCommutatorCLM c z) (jointCommutatorCLM c z)) +
      lam * Complex.re (inner ℂ z z) =
    Complex.re (inner ℂ z 0) at heuler
  have hAnorm := norm_sq_eq_re_inner (𝕜 := ℂ) (jointCommutatorCLM c z)
  have hznormInner := norm_sq_eq_re_inner (𝕜 := ℂ) z
  simp only [inner_zero_right, Complex.zero_re] at heuler
  have heulerNorm :
      ‖jointCommutatorCLM c z‖ ^ 2 + lam * ‖z‖ ^ 2 = 0 := by
    rw [hAnorm, hznormInner]
    exact heuler
  have hmul : lam * ‖z‖ ^ 2 ≤ 0 := by
    nlinarith [heulerNorm, sq_nonneg ‖jointCommutatorCLM c z‖]
  have hzsqNonpos : ‖z‖ ^ 2 ≤ 0 :=
    nonpos_of_mul_nonpos_right hmul hlam
  have hzsq : ‖z‖ ^ 2 = 0 :=
    le_antisymm hzsqNonpos (sq_nonneg ‖z‖)
  have hznorm : ‖z‖ = 0 := by
    nlinarith [hzsq, norm_nonneg z]
  have hzzero : z = 0 := norm_eq_zero.mp hznorm
  change x - y = 0 at hzzero
  exact sub_eq_zero.mp hzzero

/-- The positive shifted commutant Laplacian as a continuous linear
equivalence. -/
noncomputable def shiftedCommutantLaplacianEquiv
    {n : Type*} [Fintype n] {s : ℕ}
    (c : Fin s → Matrix n n ℂ) (lam : ℝ) (hlam : 0 < lam) :
    EuclideanSpace ℂ (n × n) ≃L[ℂ] EuclideanSpace ℂ (n × n) :=
  ContinuousLinearEquiv.ofBijective (shiftedCommutantLaplacianCLM c lam)
    (LinearMap.ker_eq_bot.mpr
      (shiftedCommutantLaplacianCLM_injective c lam hlam))
    (LinearMap.range_eq_top.mpr
      (LinearMap.injective_iff_surjective.mp
        (shiftedCommutantLaplacianCLM_injective c lam hlam)))

@[simp] theorem shiftedCommutantLaplacianEquiv_apply
    {n : Type*} [Fintype n] {s : ℕ}
    (c : Fin s → Matrix n n ℂ) (lam : ℝ) (hlam : 0 < lam)
    (x : EuclideanSpace ℂ (n × n)) :
    shiftedCommutantLaplacianEquiv c lam hlam x =
      shiftedCommutantLaplacianCLM c lam x := by
  rfl


/-- The canonical finite resolvent of the commutant Laplacian. -/
noncomputable def jointCommutatorResolvent
    {n : Type*} [Fintype n] {s : ℕ}
    (c : Fin s → Matrix n n ℂ) (lam : ℝ) (hlam : 0 < lam) :
    EuclideanSpace ℂ (n × n) →L[ℂ] EuclideanSpace ℂ (n × n) :=
  (shiftedCommutantLaplacianEquiv c lam hlam).symm.toContinuousLinearMap

@[simp] theorem jointCommutatorResolvent_apply
    {n : Type*} [Fintype n] {s : ℕ}
    (c : Fin s → Matrix n n ℂ) (lam : ℝ) (hlam : 0 < lam)
    (f : EuclideanSpace ℂ (n × n)) :
    jointCommutatorResolvent c lam hlam f =
      (shiftedCommutantLaplacianEquiv c lam hlam).symm f := rfl


/-- The canonical finite resolvent solves the strong shifted normal equation. -/
theorem jointCommutatorResolvent_laplacianEquation
    {n : Type*} [Fintype n] {s : ℕ}
    (c : Fin s → Matrix n n ℂ) (lam : ℝ) (hlam : 0 < lam)
    (f : EuclideanSpace ℂ (n × n)) :
    commutantLaplacianCLM c (jointCommutatorResolvent c lam hlam f) +
        (lam : ℂ) • jointCommutatorResolvent c lam hlam f = f := by
  rw [← shiftedCommutantLaplacianCLM_apply,
    jointCommutatorResolvent_apply,
    ← shiftedCommutantLaplacianEquiv_apply]
  exact (shiftedCommutantLaplacianEquiv c lam hlam).apply_symm_apply f

/-- The canonical finite joint-commutator resolvent satisfies the exact weak
graph-resolvent equation required by the graph-Mosco compilers. -/
theorem jointCommutatorResolvent_resolventEquation
    {n : Type*} [Fintype n] {s : ℕ}
    (c : Fin s → Matrix n n ℂ) (lam : ℝ) (hlam : 0 < lam)
    (f : EuclideanSpace ℂ (n × n)) :
    NCG.VaryingHilbert.OperatorGraphResolventEquation
      (⊤ : Submodule ℂ (EuclideanSpace ℂ (n × n)))
      (NCG.VaryingHilbert.boundedOperatorGraphMap (jointCommutatorCLM c))
      lam f (jointCommutatorResolvent c lam hlam f) := by
  exact jointCommutator_resolventEquation_of_laplacianEquation
    c lam f (jointCommutatorResolvent c lam hlam f)
      (jointCommutatorResolvent_laplacianEquation c lam hlam f)

end NCG
