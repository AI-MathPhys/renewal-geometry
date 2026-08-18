/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.HilbertWeakSpaceSequentialCompactness
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

/-!
# Product convergence in weak topologies

Strong convergence in one factor and weak convergence in the other combine to weak convergence
of pairs.  This is the mixed convergence needed for closed unbounded-operator graphs.
-/

open Filter Topology

noncomputable section

namespace NCG

universe u v w

variable {K : Type u} [RCLike K]
variable {E : Type v} [NormedAddCommGroup E] [NormedSpace K E]
variable {F : Type w} [NormedAddCommGroup F] [NormedSpace K F]

private theorem weakPairing_injective (X : Type*)
    [NormedAddCommGroup X] [NormedSpace K X] :
    Function.Injective (topDualPairing K X).flip := by
  intro a b hab
  by_contra hne
  obtain ⟨f, hf⟩ := SeparatingDual.exists_separating_of_ne (R := K) hne
  exact hf (DFunLike.congr_fun hab f)

/-- WeakSpace convergence implies convergence under every continuous linear functional. -/
theorem tendsto_apply_of_tendsto_toWeakSpace
    {ι : Type*} {l : Filter ι} {x : ι → E} {xlim : E}
    (hx : Tendsto (fun i ↦ toWeakSpace K E (x i)) l (𝓝 (toWeakSpace K E xlim)))
    (f : E →L[K] K) :
    Tendsto (fun i ↦ f (x i)) l (𝓝 (f xlim)) := by
  have heval := ((WeakBilin.tendsto_iff_forall_eval_tendsto
    (B := (topDualPairing K E).flip) (weakPairing_injective (K := K) E)).1 hx) f
  change Tendsto (fun i ↦ f (x i)) l (𝓝 (f xlim)) at heval
  exact heval

/-- Strong convergence in the first factor and weak convergence in the second imply weak
convergence of the paired sequence. -/
theorem tendsto_toWeakSpace_prod_of_strong_of_weak
    {ι : Type*} {l : Filter ι}
    {x : ι → E} {xlim : E} {y : ι → F} {ylim : F}
    (hx : Tendsto x l (𝓝 xlim))
    (hy : Tendsto (fun i ↦ toWeakSpace K F (y i)) l (𝓝 (toWeakSpace K F ylim))) :
    Tendsto (fun i ↦ toWeakSpace K (E × F) (x i, y i)) l
      (𝓝 (toWeakSpace K (E × F) (xlim, ylim))) := by
  apply (WeakBilin.tendsto_iff_forall_eval_tendsto
    (B := (topDualPairing K (E × F)).flip)
      (weakPairing_injective (K := K) (E × F))).2
  intro f
  change Tendsto (fun i ↦ f (x i, y i)) l (𝓝 (f (xlim, ylim)))
  have hxEval : Tendsto
      (fun i ↦ (f.comp (ContinuousLinearMap.inl K E F)) (x i)) l
      (𝓝 ((f.comp (ContinuousLinearMap.inl K E F)) xlim)) :=
    (f.comp (ContinuousLinearMap.inl K E F)).continuous.continuousAt.tendsto.comp hx
  have hyEval : Tendsto
      (fun i ↦ (f.comp (ContinuousLinearMap.inr K E F)) (y i)) l
      (𝓝 ((f.comp (ContinuousLinearMap.inr K E F)) ylim)) :=
    tendsto_apply_of_tendsto_toWeakSpace hy
      (f.comp (ContinuousLinearMap.inr K E F))
  have hpair (a : E) (b : F) :
      (f.comp (ContinuousLinearMap.inl K E F)) a +
          (f.comp (ContinuousLinearMap.inr K E F)) b = f (a, b) :=
    ContinuousLinearMap.comp_inl_add_comp_inr f (a, b)
  have hsum := hxEval.add hyEval
  have hfun :
      (fun i ↦ (f.comp (ContinuousLinearMap.inl K E F)) (x i) +
        (f.comp (ContinuousLinearMap.inr K E F)) (y i)) =
      (fun i ↦ f (x i, y i)) := by
    funext i
    exact hpair (x i) (y i)
  rw [hfun, hpair xlim ylim] at hsum
  exact hsum

end NCG
