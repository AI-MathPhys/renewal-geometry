/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ReturnedFeedbackQuotientRealization
import NCG.Grand.FiniteLinearSystemKrylovSaturation

/-!
# Exact finite Hankel rank of the returned-feedback quotient

The finite column and row panels of the canonical quotient are respectively
surjective and injective once their depths reach the quotient dimension.
Consequently every sufficiently large block Hankel panel
`[B D^(i+j) C]` has exactly that rank.
-/

open Matrix Finset

namespace NCG

variable {l e : Type*} [Fintype l] [Fintype e]
  [DecidableEq l] [DecidableEq e]

/-- Synthesis from the first `q` delayed visible inputs. -/
noncomputable def returnedFeedbackColumnPanel
    (B : Matrix l e ℂ) (C : Matrix e l ℂ) (D : Matrix e e ℂ) (q : ℕ) :
    ((Fin q × l) → ℂ) →ₗ[ℂ] ReturnedFeedbackSpace B C D where
  toFun x := ∑ j : Fin q,
    ((returnedFeedbackTransition B C D) ^ (j : ℕ))
      (returnedFeedbackSource B C D (fun a => x (j, a)))
  map_add' x y := by
    change (∑ j : Fin q,
      ((returnedFeedbackTransition B C D) ^ (j : ℕ))
        (returnedFeedbackSource B C D
          ((fun a => x (j, a)) + (fun a => y (j, a))))) = _
    simp only [map_add, Finset.sum_add_distrib]
  map_smul' a x := by
    change (∑ j : Fin q,
      ((returnedFeedbackTransition B C D) ^ (j : ℕ))
        (returnedFeedbackSource B C D
          (a • (fun b => x (j, b))))) = _
    simp only [map_smul, Finset.smul_sum, RingHom.id_apply]

/-- Analysis by the first `p` delayed visible outputs. -/
noncomputable def returnedFeedbackRowPanel
    (B : Matrix l e ℂ) (C : Matrix e l ℂ) (D : Matrix e e ℂ) (p : ℕ) :
    ReturnedFeedbackSpace B C D →ₗ[ℂ] ((Fin p × l) → ℂ) where
  toFun z ia := returnedFeedbackOutput B C D
    (((returnedFeedbackTransition B C D) ^ (ia.1 : ℕ)) z) ia.2
  map_add' x y := by
    funext ia
    simp
  map_smul' a x := by
    funext ia
    simp

/-- A recursive reachable filtration is contained in any subspace containing
all source powers below its depth. -/
private theorem finiteReachableFiltration_le_of_pow_le
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (A : V →ₗ[ℂ] V) (S M : Submodule ℂ V) :
    ∀ q, (∀ n, n < q → S.map (A ^ n) ≤ M) →
      finiteReachableFiltration A S q ≤ M := by
  intro q hall
  induction q with
  | zero => simp
  | succ q ih =>
      rw [finiteReachableFiltration_succ]
      exact sup_le
        (ih (fun n hn => hall n (Nat.lt_succ_of_lt hn)))
        (hall q (Nat.lt_succ_self q))

/-- Reachability of the canonical quotient is exhausted by its finite
Krylov filtration. -/
theorem returnedFeedback_reachableFiltration_exhaustive
    (B : Matrix l e ℂ) (C : Matrix e l ℂ) (D : Matrix e e ℂ) :
    (⨆ q, finiteReachableFiltration
      (returnedFeedbackTransition B C D)
      (LinearMap.range (returnedFeedbackSource B C D)) q) = ⊤ := by
  apply top_unique
  rw [← returnedFeedback_reachable B C D]
  apply Submodule.span_le.mpr
  rintro z ⟨⟨n, x⟩, rfl⟩
  refine (le_iSup (fun q => finiteReachableFiltration
    (returnedFeedbackTransition B C D)
    (LinearMap.range (returnedFeedbackSource B C D)) q) (n + 1)) ?_
  exact source_pow_le_finiteReachableFiltration
    (returnedFeedbackTransition B C D)
    (LinearMap.range (returnedFeedbackSource B C D)) (Nat.lt_succ_self n)
    ⟨returnedFeedbackSource B C D x, ⟨x, rfl⟩, rfl⟩

/-- The finite column panel is onto once its depth reaches the canonical
returned-feedback dimension. -/
theorem returnedFeedbackColumnPanel_surjective
    (B : Matrix l e ℂ) (C : Matrix e l ℂ) (D : Matrix e e ℂ) (q : ℕ)
    (hq : Module.finrank ℂ (ReturnedFeedbackSpace B C D) ≤ q) :
    Function.Surjective (returnedFeedbackColumnPanel B C D q) := by
  rw [← LinearMap.range_eq_top]
  have htop := finiteReachableFiltration_eq_top_of_exhaustive
    (returnedFeedbackTransition B C D)
    (LinearMap.range (returnedFeedbackSource B C D))
    (returnedFeedback_reachableFiltration_exhaustive B C D) q hq
  apply top_unique
  rw [← htop]
  apply finiteReachableFiltration_le_of_pow_le
  intro n hn
  rintro z ⟨y, ⟨x, rfl⟩, rfl⟩
  classical
  let j : Fin q := ⟨n, hn⟩
  let input : Fin q × l → ℂ := fun ja =>
    if ja.1 = j then x ja.2 else 0
  refine ⟨input, ?_⟩
  change (∑ k : Fin q,
      ((returnedFeedbackTransition B C D) ^ (k : ℕ))
        (returnedFeedbackSource B C D (fun a => input (k, a)))) = _
  rw [Finset.sum_eq_single j]
  · congr 2
    funext a
    simp [input]
  · intro k _ hkj
    have hne : k ≠ j := hkj
    have hzero : (fun a => input (k, a)) = 0 := by
      funext a
      simp [input, hne]
    rw [hzero, map_zero, map_zero]
  · simp

/-- The intersection of all finite output kernels is zero. -/
theorem returnedFeedback_observableKernel_exhaustive
    (B : Matrix l e ℂ) (C : Matrix e l ℂ) (D : Matrix e e ℂ) :
    (⨅ p, finiteObservableKernel
      (returnedFeedbackTransition B C D)
      (returnedFeedbackOutput B C D) p) = ⊥ := by
  apply le_antisymm
  · intro z hz
    rw [Submodule.mem_bot]
    apply returnedFeedback_observable B C D z
    intro n
    rw [Submodule.mem_iInf] at hz
    have hn := hz (n + 1)
    rw [finiteObservableKernel_succ] at hn
    have hker := hn.2
    change returnedFeedbackOutput B C D
      (((returnedFeedbackTransition B C D) ^ n) z) = 0 at hker
    exact hker
  · exact bot_le

/-- Vanishing of the first p outputs places a state in the
finite observable kernel at depth p. -/
private theorem mem_finiteObservableKernel_of_vanishes
    {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (A : V →ₗ[ℂ] V) (O : V →ₗ[ℂ] W) (z : V) :
    ∀ p, (∀ n, n < p → O ((A ^ n) z) = 0) →
      z ∈ finiteObservableKernel A O p := by
  intro p hzero
  induction p with
  | zero => simp
  | succ p ih =>
      rw [finiteObservableKernel_succ]
      refine ⟨ih (fun n hn => hzero n (Nat.lt_succ_of_lt hn)), ?_⟩
      change O ((A ^ p) z) = 0
      exact hzero p (Nat.lt_succ_self p)

/-- The finite row panel is one-to-one once its depth reaches the canonical
returned-feedback dimension. -/
theorem returnedFeedbackRowPanel_injective
    (B : Matrix l e ℂ) (C : Matrix e l ℂ) (D : Matrix e e ℂ) (p : ℕ)
    (hp : Module.finrank ℂ (ReturnedFeedbackSpace B C D) ≤ p) :
    Function.Injective (returnedFeedbackRowPanel B C D p) := by
  rw [← LinearMap.ker_eq_bot]
  apply le_antisymm
  · intro z hz
    have hzero : ∀ n, n < p →
        returnedFeedbackOutput B C D
          (((returnedFeedbackTransition B C D) ^ n) z) = 0 := by
      intro n hn
      funext a
      have hcoord := congrFun (show returnedFeedbackRowPanel B C D p z = 0 by
        rwa [LinearMap.mem_ker] at hz) (⟨n, hn⟩, a)
      exact hcoord
    have hmem : z ∈ finiteObservableKernel
        (returnedFeedbackTransition B C D)
        (returnedFeedbackOutput B C D) p :=
      mem_finiteObservableKernel_of_vanishes
        (returnedFeedbackTransition B C D)
        (returnedFeedbackOutput B C D) z p hzero
    have hbot := finiteObservableKernel_eq_bot_of_exhaustive
      (returnedFeedbackTransition B C D)
      (returnedFeedbackOutput B C D)
      (returnedFeedback_observableKernel_exhaustive B C D) p hp
    rw [hbot] at hmem
    exact hmem
  · exact bot_le

/-- Exact finite block-Hankel rank in factorized linear-map form. -/
theorem returnedFeedback_finiteHankelPanel_rank
    (B : Matrix l e ℂ) (C : Matrix e l ℂ) (D : Matrix e e ℂ)
    (p q : ℕ)
    (hp : Module.finrank ℂ (ReturnedFeedbackSpace B C D) ≤ p)
    (hq : Module.finrank ℂ (ReturnedFeedbackSpace B C D) ≤ q) :
    Module.finrank ℂ (LinearMap.range
      ((returnedFeedbackRowPanel B C D p).comp
        (returnedFeedbackColumnPanel B C D q))) =
      Module.finrank ℂ (ReturnedFeedbackSpace B C D) := by
  exact full_panel_rank
    (returnedFeedbackColumnPanel B C D q)
    (returnedFeedbackRowPanel B C D p)
    (returnedFeedbackColumnPanel_surjective B C D q hq)
    (returnedFeedbackRowPanel_injective B C D p hp)

/-- The literal returned-kernel block Hankel matrix. -/
def returnedFeedbackHankelPanel
    (B : Matrix l e ℂ) (C : Matrix e l ℂ) (D : Matrix e e ℂ)
    (p q : ℕ) : Matrix (Fin p × l) (Fin q × l) ℂ :=
  fun ia jb => (B * D ^ ((ia.1 : ℕ) + (jb.1 : ℕ)) * C) ia.2 jb.2

end NCG
