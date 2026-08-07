/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Canonical pre-renewal decomposition
  (`thm:canonical-pre-renewal-decomposition`,
  Gran-Tensor manuscript)

* `canonical_pre_renewal_decomposition`: for a finite lift
  `[[A,B],[C,D]]` with hidden source-reachable space
  `ℛ_hid = span{DⁿC·x}` and future-sealed subspace
  `𝒩_seal = {e ∈ ℛ_hid : B·Dⁿ·e = 0 ∀n}`:
  (i) both spaces are `D`-invariant;
  (ii) the writers land in the carrier (`C·x ∈ ℛ_hid`) and
      `B` kills the sealed part — so `C, D, B` descend to
      the returned-feedback quotient;
  (iii) the descended realization is observable by
      construction: a reachable vector unseen by every
      `B·Dⁿ` is sealed;
  (iv) the boxed exact sequence
      `0 → 𝒩_seal → ℛ_hid → ℱ_fb → 0` as the exact rank
      count `dim 𝒩_seal + dim ℱ_fb = dim ℛ_hid`.

The block-Hankel rank clause is the proved
`hankel_minimality`/`provenance_hankel_minimality` layer
applied to the returned kernels.
-/

open Matrix

namespace NCG

variable {l e : Type*} [Fintype l] [Fintype e]
variable [DecidableEq e]

/-- The hidden source-reachable space `span{DⁿC·x}`. -/
def reachHid (C : Matrix e l ℂ) (D : Matrix e e ℂ) :
    Submodule ℂ (e → ℂ) :=
  Submodule.span ℂ
    (⋃ n : ℕ, Set.range fun x : l → ℂ => (D ^ n * C) *ᵥ x)

/-- The future-sealed subspace `{v : B·Dⁿ·v = 0 ∀n}`. -/
def sealedSub (B : Matrix l e ℂ) (D : Matrix e e ℂ) :
    Submodule ℂ (e → ℂ) :=
  ⨅ n : ℕ, LinearMap.ker (B * D ^ n).mulVecLin

/-- `thm:canonical-pre-renewal-decomposition`. -/
theorem canonical_pre_renewal_decomposition
    (B : Matrix l e ℂ) (C : Matrix e l ℂ)
    (D : Matrix e e ℂ) :
    -- (i) D-invariance of the carrier and the sealed part
    (∀ v ∈ reachHid C D, D *ᵥ v ∈ reachHid C D)
    ∧ (∀ v ∈ sealedSub B D, D *ᵥ v ∈ sealedSub B D)
    -- (ii) the writers land in the carrier, B kills the seal
    ∧ (∀ x : l → ℂ, C *ᵥ x ∈ reachHid C D)
    ∧ (∀ v ∈ sealedSub B D, B *ᵥ v = 0)
    -- (iii) observability of the quotient by construction
    ∧ (∀ v : e → ℂ, (∀ n : ℕ, (B * D ^ n) *ᵥ v = 0) →
        v ∈ sealedSub B D)
    -- (iv) the exact sequence as an exact rank count
    ∧ Module.finrank ℂ
        ((reachHid C D) ⧸ (Submodule.comap
          (reachHid C D).subtype (sealedSub B D)))
      + Module.finrank ℂ
          (Submodule.comap (reachHid C D).subtype
            (sealedSub B D))
      = Module.finrank ℂ (reachHid C D) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    induction hv using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨s, ⟨n, rfl⟩, x, rfl⟩ := hy
        apply Submodule.subset_span
        refine Set.mem_iUnion.mpr ⟨n + 1, ⟨x, ?_⟩⟩
        rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc,
          ← pow_succ']
    | zero =>
        rw [Matrix.mulVec_zero]
        exact Submodule.zero_mem _
    | add y z _ _ hy hz =>
        rw [Matrix.mulVec_add]
        exact Submodule.add_mem _ hy hz
    | smul t y _ hy =>
        rw [Matrix.mulVec_smul]
        exact Submodule.smul_mem _ _ hy
  · intro v hv
    rw [sealedSub, Submodule.mem_iInf] at hv ⊢
    intro n
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply,
      Matrix.mulVec_mulVec, Matrix.mul_assoc, ← pow_succ]
    have h := hv (n + 1)
    rwa [LinearMap.mem_ker, Matrix.mulVecLin_apply] at h
  · intro x
    apply Submodule.subset_span
    refine Set.mem_iUnion.mpr ⟨0, ⟨x, ?_⟩⟩
    rw [pow_zero, Matrix.one_mul]
  · intro v hv
    rw [sealedSub, Submodule.mem_iInf] at hv
    have h := hv 0
    rwa [LinearMap.mem_ker, Matrix.mulVecLin_apply,
      pow_zero, Matrix.mul_one] at h
  · intro v hv
    rw [sealedSub, Submodule.mem_iInf]
    intro n
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
    exact hv n
  · exact Submodule.finrank_quotient_add_finrank _

end NCG
