/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.ReferenceOriginMarginalBlockExact

/-!
# Exact shell inheritance

RG.3 machinery for `thm:SM-common-action-integrability`: the exact shell action
`e^{-S_eff(x)} = E_{ρ_Y}[e^{-S_Y} ∣ π(Y) = x]` on a finite fine space

* satisfies the defining conditional-expectation identity exactly
  (`exp_neg_shellAction`);
* **composes exactly through nested cutoffs** (`shellAction_comp` — the tower property:
  marginalizing in two stages equals marginalizing once);
* is **equivariant**: a symmetry of the fine packet covering a coarse symmetry leaves the
  shell action invariant (`shellAction_equivariant`), so gauge invariance passes through
  the conditional expectation.
-/

open NCG.ReferenceOrigin

namespace NCG
namespace ShellInheritance

variable {ΩY ΩX ΩZ : Type*} [Fintype ΩY] [Fintype ΩX] [DecidableEq ΩX] [DecidableEq ΩZ]

/-- The Gibbs numerator of the shell action. -/
noncomputable def gibbsSum (π : ΩY → ΩX) (ρ : ΩY → ℝ) (S : ΩY → ℝ) (x : ΩX) : ℝ :=
  ∑ y ∈ {y | π y = x}, ρ y * Real.exp (-S y)

omit [Fintype ΩX] in
theorem gibbsSum_def (π : ΩY → ΩX) (ρ : ΩY → ℝ) (S : ΩY → ℝ) (x : ΩX) :
    gibbsSum π ρ S x = ∑ y ∈ {y | π y = x}, ρ y * Real.exp (-S y) := rfl

omit [Fintype ΩX] in
theorem pushRef_def (π : ΩY → ΩX) (ρ : ΩY → ℝ) (x : ΩX) :
    pushRef π ρ x = ∑ y ∈ {y | π y = x}, ρ y := rfl

omit [Fintype ΩX] in
theorem shellAction_eq (π : ΩY → ΩX) (ρ : ΩY → ℝ) (S : ΩY → ℝ) (x : ΩX) :
    shellAction π ρ S x = -Real.log (gibbsSum π ρ S x / pushRef π ρ x) := rfl

omit [Fintype ΩX] in
theorem gibbsSum_pos (π : ΩY → ΩX) {ρ : ΩY → ℝ} (hρ : ∀ y, 0 < ρ y)
    (hπ : Function.Surjective π) (S : ΩY → ℝ) (x : ΩX) : 0 < gibbsSum π ρ S x := by
  classical
  obtain ⟨y0, hy0⟩ := hπ x
  refine Finset.sum_pos' (fun y _ => ?_) ⟨y0, by simp [hy0], ?_⟩
  · exact mul_nonneg (hρ y).le (Real.exp_pos _).le
  · exact mul_pos (hρ y0) (Real.exp_pos _)

omit [Fintype ΩX] in
/-- **The defining identity of RG.3**: `e^{-S_eff(x)} = E_{ρ_Y}[e^{-S_Y} ∣ π(Y) = x]`
holds exactly. -/
theorem exp_neg_shellAction (π : ΩY → ΩX) {ρ : ΩY → ℝ} (hρ : ∀ y, 0 < ρ y)
    (hπ : Function.Surjective π) (S : ΩY → ℝ) (x : ΩX) :
    Real.exp (-shellAction π ρ S x) = gibbsSum π ρ S x / pushRef π ρ x := by
  rw [shellAction_eq, neg_neg, Real.exp_log]
  exact div_pos (gibbsSum_pos π hρ hπ S x) (pushRef_pos π hρ hπ x)

/-- The pushed-forward reference composes through nested cutoffs. -/
theorem pushRef_comp (π₁ : ΩY → ΩX) (π₂ : ΩX → ΩZ) (ρ : ΩY → ℝ) (z : ΩZ) :
    pushRef (fun y => π₂ (π₁ y)) ρ z = pushRef π₂ (pushRef π₁ ρ) z := by
  classical
  refine Eq.symm ?_
  rw [pushRef_def, Finset.sum_congr rfl fun x _ => pushRef_def π₁ ρ x,
    Finset.sum_sigma', pushRef_def]
  refine Finset.sum_nbij' (fun p => p.2) (fun y => ⟨π₁ y, y⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨x, y⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hp.2, hp.1]
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hy, trivial⟩
  · rintro ⟨x, y⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simp [hp.2]
  · intro y _
    rfl
  · rintro ⟨x, y⟩ _
    rfl

/-- **Exact nested composition (the tower property)**: marginalizing through two nested
cutoffs equals marginalizing once — the shell action composes exactly. -/
theorem shellAction_comp (π₁ : ΩY → ΩX) (π₂ : ΩX → ΩZ) {ρ : ΩY → ℝ}
    (hρ : ∀ y, 0 < ρ y) (hπ₁ : Function.Surjective π₁) (S : ΩY → ℝ) (z : ΩZ) :
    shellAction (fun y => π₂ (π₁ y)) ρ S z
      = shellAction π₂ (pushRef π₁ ρ) (shellAction π₁ ρ S) z := by
  classical
  have hpush : ∀ x, 0 < pushRef π₁ ρ x := pushRef_pos π₁ hρ hπ₁
  have hterm : ∀ x : ΩX, pushRef π₁ ρ x * Real.exp (-shellAction π₁ ρ S x)
      = gibbsSum π₁ ρ S x := by
    intro x
    rw [exp_neg_shellAction π₁ hρ hπ₁ S x, mul_comm, div_mul_cancel₀ _ (hpush x).ne']
  have hnum : gibbsSum π₂ (pushRef π₁ ρ) (shellAction π₁ ρ S) z
      = gibbsSum (fun y => π₂ (π₁ y)) ρ S z := by
    rw [gibbsSum_def, Finset.sum_congr rfl fun x _ => hterm x,
      Finset.sum_congr rfl fun x _ => gibbsSum_def π₁ ρ S x,
      Finset.sum_sigma', gibbsSum_def]
    refine Finset.sum_nbij' (fun p => p.2) (fun y => ⟨π₁ y, y⟩) ?_ ?_ ?_ ?_ ?_
    · rintro ⟨x, y⟩ hp
      simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hp.2, hp.1]
    · intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
      simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hy, trivial⟩
    · rintro ⟨x, y⟩ hp
      simp only [Finset.mem_sigma, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      simp [hp.2]
    · intro y _
      rfl
    · rintro ⟨x, y⟩ _
      rfl
  rw [shellAction_eq, shellAction_eq, hnum, pushRef_comp]

omit [Fintype ΩX] in
/-- **Gauge equivariance passes through the conditional expectation**: a fine symmetry
preserving the reference law and the action, covering a coarse symmetry, leaves the shell
action invariant. -/
theorem shellAction_equivariant (π : ΩY → ΩX) (ρ : ΩY → ℝ) (S : ΩY → ℝ)
    (gY : Equiv.Perm ΩY) (gX : Equiv.Perm ΩX)
    (hcomm : ∀ y, π (gY y) = gX (π y)) (hρ : ∀ y, ρ (gY y) = ρ y)
    (hS : ∀ y, S (gY y) = S y) (x : ΩX) :
    shellAction π ρ S (gX x) = shellAction π ρ S x := by
  classical
  have hfiber : ∀ (f : ΩY → ℝ), (∀ y, f (gY y) = f y) →
      (∑ y ∈ {y | π y = gX x}, f y) = ∑ y ∈ {y | π y = x}, f y := by
    intro f hf
    refine Finset.sum_nbij' (fun y => gY.symm y) (fun y => gY y) ?_ ?_ ?_ ?_ ?_
    · intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      have h2 := hcomm (gY.symm y)
      rw [Equiv.apply_symm_apply] at h2
      rw [hy] at h2
      exact gX.injective h2.symm
    · intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      rw [hcomm, hy]
    · intro y _
      exact Equiv.apply_symm_apply gY y
    · intro y _
      exact Equiv.symm_apply_apply gY y
    · intro y _
      have h2 := hf (gY.symm y)
      rw [Equiv.apply_symm_apply] at h2
      exact h2
  rw [shellAction_eq, shellAction_eq, gibbsSum_def, gibbsSum_def,
    hfiber (fun y => ρ y * Real.exp (-S y)) fun y => by rw [hρ, hS],
    pushRef_def, pushRef_def, hfiber ρ hρ]

/-- **RG.3 bundle**: the exact conditional-expectation identity, exact nested composition,
and gauge equivariance of the shell action. -/
theorem shell_inheritance (π₁ : ΩY → ΩX) (π₂ : ΩX → ΩZ) {ρ : ΩY → ℝ}
    (hρ : ∀ y, 0 < ρ y) (hπ₁ : Function.Surjective π₁) (S : ΩY → ℝ)
    (gY : Equiv.Perm ΩY) (gX : Equiv.Perm ΩX)
    (hcomm : ∀ y, π₁ (gY y) = gX (π₁ y)) (hgρ : ∀ y, ρ (gY y) = ρ y)
    (hgS : ∀ y, S (gY y) = S y) :
    (∀ x, Real.exp (-shellAction π₁ ρ S x) = gibbsSum π₁ ρ S x / pushRef π₁ ρ x) ∧
    (∀ z, shellAction (fun y => π₂ (π₁ y)) ρ S z
      = shellAction π₂ (pushRef π₁ ρ) (shellAction π₁ ρ S) z) ∧
    ∀ x, shellAction π₁ ρ S (gX x) = shellAction π₁ ρ S x :=
  ⟨exp_neg_shellAction π₁ hρ hπ₁ S, shellAction_comp π₁ π₂ hρ hπ₁ S,
   shellAction_equivariant π₁ ρ S gY gX hcomm hgρ hgS⟩

end ShellInheritance
end NCG
