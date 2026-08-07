/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.MinimalRecord

/-!
# Minimal Read-algebra characterization
  (`thm:minimal-read-algebra`, Gran-Tensor manuscript)

* `separating_subalgebra_eq_top`: a unital subalgebra of
  functions on a finite set which separates points is the whole
  function algebra (finite Lagrange interpolation).
* `minimal_read_algebra`: a function belongs to the pullback
  algebra of the minimal record exactly when it is constant on
  future-equivalence classes; and pulling back a generator along
  a primitive update produces the concatenated-word generator
  (update invariance).

Rendering disclosed: the Gelfand-spectrum clause is the finite
statement that the pullback algebra is canonically the function
algebra of the quotient (the proved factorization); the
`C*`/self-adjointness bookkeeping is automatic for finite
classical algebras.
-/

namespace NCG

/-- A separating unital subalgebra of functions on a finite set
is everything (finite Lagrange interpolation). -/
theorem separating_subalgebra_eq_top {R : Type*} [Finite R]
    (S : Subalgebra ℂ (R → ℂ))
    (hsep : ∀ r r' : R, r ≠ r' → ∃ f ∈ S, f r ≠ f r') :
    S = ⊤ := by
  classical
  cases nonempty_fintype R
  choose F hFmem hFne using hsep
  have hproof : ∀ (r : R) (s : (Finset.univ.erase r : Finset R)),
      r ≠ s.1 := fun r s =>
    (Finset.ne_of_mem_erase s.2).symm
  have hindic : ∀ r : R, (Pi.single r 1 : R → ℂ) ∈ S := by
    intro r
    set e : R → ℂ := ∏ s ∈ (Finset.univ.erase r).attach,
      (F r s.1 (hproof r s)
        - algebraMap ℂ (R → ℂ) (F r s.1 (hproof r s) s.1))
      with he
    have hmem : e ∈ S := by
      refine Subalgebra.prod_mem S fun s _ => ?_
      exact S.sub_mem (hFmem r s.1 (hproof r s))
        (S.algebraMap_mem _)
    have hval : ∀ t : R, e t
        = ∏ s ∈ (Finset.univ.erase r).attach,
            (F r s.1 (hproof r s) t
              - F r s.1 (hproof r s) s.1) := by
      intro t
      rw [he, Finset.prod_apply]
      refine Finset.prod_congr rfl fun s _ => ?_
      rfl
    have her : e r ≠ 0 := by
      rw [hval, Finset.prod_ne_zero_iff]
      intro s _
      exact sub_ne_zero.mpr (hFne r s.1 (hproof r s))
    have het : ∀ t : R, t ≠ r → e t = 0 := by
      intro t hne
      rw [hval]
      refine Finset.prod_eq_zero
        (Finset.mem_attach _ ⟨t, Finset.mem_erase.mpr
          ⟨hne, Finset.mem_univ t⟩⟩) ?_
      rw [sub_self]
    have hsingle : (Pi.single r 1 : R → ℂ) = (e r)⁻¹ • e := by
      funext t
      by_cases ht : t = r
      · subst ht
        simp [inv_mul_cancel₀ her]
      · simp [ht, het t ht]
    rw [hsingle]
    exact S.smul_mem hmem _
  rw [eq_top_iff]
  intro g _
  have hg : g = ∑ r : R, g r • (Pi.single r 1 : R → ℂ) := by
    funext t
    rw [Finset.sum_apply]
    rw [show (∑ r : R, (g r • (Pi.single r 1 : R → ℂ)) t)
        = ∑ r : R, g r * (Pi.single r 1 : R → ℂ) t from
      Finset.sum_congr rfl fun r _ => rfl]
    simp [Pi.single_apply]
  rw [hg]
  exact Subalgebra.sum_mem S fun r _ =>
    S.smul_mem (hindic r) _

/-- `thm:minimal-read-algebra`: pullback factorization and
update invariance. -/
theorem minimal_read_algebra {R Sig : Type*} (sig : R → Sig) :
    -- (1) a coordinate factors through the minimal record iff
    --     it is constant on future-equivalence classes
    (∀ f : R → ℂ,
      (∀ r r', sig r = sig r' → f r = f r') ↔
      ∃ g : MinRec sig → ℂ,
        ∀ r, g (Quotient.mk (minRecSetoid sig) r) = f r)
    -- (2) update invariance: pulling back a word generator
    --     along a primitive update gives the concatenated
    --     generator
    ∧ (∀ (d : R → ℂ) (uw ua : R → R),
        (d ∘ uw) ∘ ua = d ∘ (uw ∘ ua)) := by
  constructor
  · intro f
    constructor
    · intro hconst
      exact ⟨Quotient.lift f (fun a b h => hconst a b h),
        fun r => rfl⟩
    · rintro ⟨g, hg⟩ r r' hrr
      rw [← hg r, ← hg r']
      congr 1
      exact Quotient.sound hrr
  · intro d uw ua
    rfl

end NCG
