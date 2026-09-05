/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.PreRenewalDecomposition
import NCG.Grand.PassiveRealizationSimilarity
import NCG.Grand.ProvenancePanelSaturation

/-!
# Returned-feedback quotient realization

This module equips the canonical pre-renewal quotient with its descended
source, transition, and output maps and proves that the resulting realization
is reachable and observable.
-/

open Matrix

namespace NCG

variable {l e : Type*} [Fintype l] [Fintype e] [DecidableEq e]

/-- The sealed part inside the hidden source-reachable carrier. -/
abbrev returnedFeedbackNull
    (B : Matrix l e ℂ) (C : Matrix e l ℂ) (D : Matrix e e ℂ) :=
  Submodule.comap (reachHid C D).subtype (sealedSub B D)

/-- The canonical returned-feedback state space. -/
abbrev ReturnedFeedbackSpace
    (B : Matrix l e ℂ) (C : Matrix e l ℂ) (D : Matrix e e ℂ) :=
  (reachHid C D) ⧸ returnedFeedbackNull B C D

/-- Each hidden Krylov source column belongs to the reachable carrier. -/
theorem reachHid_krylov_mem
    (C : Matrix e l ℂ) (D : Matrix e e ℂ)
    (n : ℕ) (x : l → ℂ) :
    (D ^ n * C) *ᵥ x ∈ reachHid C D := by
  apply Submodule.subset_span
  exact Set.mem_iUnion.mpr ⟨n, ⟨x, rfl⟩⟩

/-- The visible-to-hidden source map descended to returned feedback. -/
noncomputable def returnedFeedbackSource
    (B : Matrix l e ℂ) (C : Matrix e l ℂ) (D : Matrix e e ℂ) :
    (l → ℂ) →ₗ[ℂ] ReturnedFeedbackSpace B C D :=
  (returnedFeedbackNull B C D).mkQ.comp
    (C.mulVecLin.codRestrict (reachHid C D)
      (fun x => by simpa using reachHid_krylov_mem C D 0 x))

/-- The hidden transition restricted to the reachable carrier. -/
noncomputable def reachableHiddenTransition
    (C : Matrix e l ℂ) (D : Matrix e e ℂ) :
    reachHid C D →ₗ[ℂ] reachHid C D :=
  (D.mulVecLin.domRestrict (reachHid C D)).codRestrict
    (reachHid C D) (fun v =>
      (canonical_pre_renewal_decomposition (0 : Matrix l e ℂ) C D).1 v v.2)

/-- The hidden transition descended through the invariant sealed subspace. -/
noncomputable def returnedFeedbackTransition
    (B : Matrix l e ℂ) (C : Matrix e l ℂ) (D : Matrix e e ℂ) :
    ReturnedFeedbackSpace B C D →ₗ[ℂ] ReturnedFeedbackSpace B C D :=
  Submodule.mapQ (returnedFeedbackNull B C D)
    (returnedFeedbackNull B C D) (reachableHiddenTransition C D) (by
      intro v hv
      change D *ᵥ (v : e → ℂ) ∈ sealedSub B D
      exact (canonical_pre_renewal_decomposition B C D).2.1 v hv)

/-- The hidden-to-visible output descended through the sealed subspace. -/
noncomputable def returnedFeedbackOutput
    (B : Matrix l e ℂ) (C : Matrix e l ℂ) (D : Matrix e e ℂ) :
    ReturnedFeedbackSpace B C D →ₗ[ℂ] (l → ℂ) :=
  Submodule.liftQ (returnedFeedbackNull B C D)
    (B.mulVecLin.comp (reachHid C D).subtype) (by
      intro v hv
      rw [LinearMap.mem_ker]
      exact (canonical_pre_renewal_decomposition B C D).2.2.2.1 v hv)

@[simp] theorem returnedFeedbackSource_apply
    (B : Matrix l e ℂ) (C : Matrix e l ℂ) (D : Matrix e e ℂ)
    (x : l → ℂ) :
    returnedFeedbackSource B C D x =
      (returnedFeedbackNull B C D).mkQ
        ⟨C *ᵥ x, by simpa using reachHid_krylov_mem C D 0 x⟩ := rfl

@[simp] theorem returnedFeedbackTransition_mk
    (B : Matrix l e ℂ) (C : Matrix e l ℂ) (D : Matrix e e ℂ)
    (v : reachHid C D) :
    returnedFeedbackTransition B C D
        ((returnedFeedbackNull B C D).mkQ v) =
      (returnedFeedbackNull B C D).mkQ
        (reachableHiddenTransition C D v) := by
  rw [returnedFeedbackTransition, Submodule.mkQ_apply,
    Submodule.mkQ_apply, Submodule.mapQ_apply]

@[simp] theorem returnedFeedbackOutput_mk
    (B : Matrix l e ℂ) (C : Matrix e l ℂ) (D : Matrix e e ℂ)
    (v : reachHid C D) :
    returnedFeedbackOutput B C D
        ((returnedFeedbackNull B C D).mkQ v) = B *ᵥ (v : e → ℂ) := rfl

/-- The descended transition iterates are represented by the original hidden
matrix powers. -/
theorem returnedFeedbackTransition_pow_mk
    (B : Matrix l e ℂ) (C : Matrix e l ℂ) (D : Matrix e e ℂ)
    (n : ℕ) (v : reachHid C D) :
    ((returnedFeedbackTransition B C D) ^ n)
        ((returnedFeedbackNull B C D).mkQ v) =
      (returnedFeedbackNull B C D).mkQ
        ⟨D ^ n *ᵥ (v : e → ℂ), by
          induction n with
          | zero => simpa using v.2
          | succ n ih =>
              rw [pow_succ', ← Matrix.mulVec_mulVec]
              exact (canonical_pre_renewal_decomposition
                (0 : Matrix l e ℂ) C D).1 _ ih⟩ := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, ih,
        returnedFeedbackTransition_mk]
      apply congrArg (returnedFeedbackNull B C D).mkQ
      apply Subtype.ext
      change D *ᵥ (D ^ n *ᵥ (v : e → ℂ)) =
        D ^ (n + 1) *ᵥ (v : e → ℂ)
      rw [Matrix.mulVec_mulVec, pow_succ']

/-- Literal realization of every returned kernel `B D^n C`. -/
theorem returnedFeedback_realizes_kernel
    (B : Matrix l e ℂ) (C : Matrix e l ℂ) (D : Matrix e e ℂ)
    (n : ℕ) (x : l → ℂ) :
    returnedFeedbackOutput B C D
      (((returnedFeedbackTransition B C D) ^ n)
        (returnedFeedbackSource B C D x)) =
      (B * D ^ n * C) *ᵥ x := by
  rw [returnedFeedbackSource_apply,
    returnedFeedbackTransition_pow_mk, returnedFeedbackOutput_mk]
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]

/-- The descended Krylov source family spans the returned-feedback quotient. -/
theorem returnedFeedback_reachable
    (B : Matrix l e ℂ) (C : Matrix e l ℂ) (D : Matrix e e ℂ) :
    Submodule.span ℂ (Set.range fun q : ℕ × (l → ℂ) =>
      ((returnedFeedbackTransition B C D) ^ q.1)
        (returnedFeedbackSource B C D q.2)) = ⊤ := by
  apply top_unique
  intro z _
  obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective
    (returnedFeedbackNull B C D) z
  let S := Submodule.span ℂ (Set.range fun q : ℕ × (l → ℂ) =>
    ((returnedFeedbackTransition B C D) ^ q.1)
      (returnedFeedbackSource B C D q.2))
  have hspan : ∀ (y : e → ℂ) (hy : y ∈ reachHid C D),
      (returnedFeedbackNull B C D).mkQ ⟨y, hy⟩ ∈ S := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨s, ⟨n, rfl⟩, x, rfl⟩ := hy
        apply Submodule.subset_span
        refine ⟨(n, x), ?_⟩
        change ((returnedFeedbackTransition B C D) ^ n)
            (returnedFeedbackSource B C D x) = _
        rw [returnedFeedbackSource_apply,
          returnedFeedbackTransition_pow_mk]
        apply congrArg (returnedFeedbackNull B C D).mkQ
        apply Subtype.ext
        simp [Matrix.mulVec_mulVec]
    | zero =>
        change (returnedFeedbackNull B C D).mkQ
          (0 : reachHid C D) ∈ S
        simpa using S.zero_mem
    | add y z hy hz ihy ihz =>
        change (returnedFeedbackNull B C D).mkQ
          (⟨y, hy⟩ + ⟨z, hz⟩) ∈ S
        rw [map_add]
        exact Submodule.add_mem S ihy ihz
    | smul a y hy ihy =>
        change (returnedFeedbackNull B C D).mkQ
          (a • ⟨y, hy⟩) ∈ S
        rw [map_smul]
        exact Submodule.smul_mem S a ihy
  exact hspan v v.2

/-- The descended output iterates separate the returned-feedback quotient. -/
theorem returnedFeedback_observable
    (B : Matrix l e ℂ) (C : Matrix e l ℂ) (D : Matrix e e ℂ)
    (z : ReturnedFeedbackSpace B C D)
    (hz : ∀ n, returnedFeedbackOutput B C D
      (((returnedFeedbackTransition B C D) ^ n) z) = 0) :
    z = 0 := by
  obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective
    (returnedFeedbackNull B C D) z
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  change (v : e → ℂ) ∈ sealedSub B D
  rw [sealedSub, Submodule.mem_iInf]
  intro n
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
  have hn := hz n
  rw [returnedFeedbackTransition_pow_mk,
    returnedFeedbackOutput_mk] at hn
  simpa only [Matrix.mulVec_mulVec, Matrix.mul_assoc] using hn

/-- Coordinate evaluation on the visible carrier. -/
def visibleCoordinate (r : l) : (l → ℂ) →ₗ[ℂ] ℂ where
  toFun x := x r
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Complete returned-kernel Reads, indexed by delay and visible output
coordinate. -/
noncomputable def returnedFeedbackRead
    (B : Matrix l e ℂ) (C : Matrix e l ℂ) (D : Matrix e e ℂ)
    (f : ℕ × l) : ReturnedFeedbackSpace B C D →ₗ[ℂ] ℂ :=
  (visibleCoordinate f.2).comp
    ((returnedFeedbackOutput B C D).comp
      ((returnedFeedbackTransition B C D) ^ f.1))

/-- The complete family of returned-kernel Reads has trivial common kernel. -/
theorem returnedFeedback_reads_separate
    (B : Matrix l e ℂ) (C : Matrix e l ℂ) (D : Matrix e e ℂ) :
    (⨅ f, LinearMap.ker (returnedFeedbackRead B C D f)) = ⊥ := by
  apply le_antisymm
  · intro z hz
    rw [Submodule.mem_bot]
    apply returnedFeedback_observable B C D z
    intro n
    funext r
    rw [Submodule.mem_iInf] at hz
    have hzr := hz (n, r)
    rw [LinearMap.mem_ker] at hzr
    exact hzr
  · exact bot_le

/-- Any other source-reachable, Read-observable realization of the same
returned kernels is uniquely similar to the canonical quotient.  The
similarity fixes every Krylov source, preserves every output Read, and its
generic intertwining clause applies to the one-step transition. -/
theorem returnedFeedback_uniqueMinimalSimilarity
    (B : Matrix l e ℂ) (C : Matrix e l ℂ) (D : Matrix e e ℂ)
    {N : Type*} [AddCommGroup N] [Module ℂ N]
    (src : ℕ × (l → ℂ) → N)
    (read : ℕ × l → N →ₗ[ℂ] ℂ)
    (hmatch : ∀ f q,
      returnedFeedbackRead B C D f
        (((returnedFeedbackTransition B C D) ^ q.1)
          (returnedFeedbackSource B C D q.2)) =
        read f (src q))
    (hreach : Submodule.span ℂ (Set.range src) = ⊤)
    (hobs : (⨅ f, LinearMap.ker (read f)) = ⊥) :
    ∃ E : ReturnedFeedbackSpace B C D ≃ₗ[ℂ] N,
      (∀ q, E (((returnedFeedbackTransition B C D) ^ q.1)
          (returnedFeedbackSource B C D q.2)) = src q)
      ∧ (∀ f z, read f (E z) = returnedFeedbackRead B C D f z)
      ∧ (∀ G : ReturnedFeedbackSpace B C D ≃ₗ[ℂ] N,
          (∀ q, G (((returnedFeedbackTransition B C D) ^ q.1)
            (returnedFeedbackSource B C D q.2)) = src q) → G = E)
      ∧ (∀ (next : (ℕ × (l → ℂ)) → (ℕ × (l → ℂ)))
            (A₂ : N →ₗ[ℂ] N),
          (∀ q, returnedFeedbackTransition B C D
              (((returnedFeedbackTransition B C D) ^ q.1)
                (returnedFeedbackSource B C D q.2)) =
            ((returnedFeedbackTransition B C D) ^ (next q).1)
              (returnedFeedbackSource B C D (next q).2)) →
          (∀ q, A₂ (src q) = src (next q)) →
          ∀ z, E (returnedFeedbackTransition B C D z) = A₂ (E z)) := by
  rcases reachable_observable_unique_similarity
    (fun q : ℕ × (l → ℂ) =>
      ((returnedFeedbackTransition B C D) ^ q.1)
        (returnedFeedbackSource B C D q.2))
    src (returnedFeedbackRead B C D) read hmatch
    (returnedFeedback_reachable B C D) hreach
    (returnedFeedback_reads_separate B C D) hobs with
      ⟨E, hEsrc, hEread, hEunique, hEintertwine⟩
  refine ⟨E, hEsrc, hEread, hEunique, ?_⟩
  intro next A₂ hnext hA₂
  exact hEintertwine next (returnedFeedbackTransition B C D) A₂
    hnext hA₂

end NCG
