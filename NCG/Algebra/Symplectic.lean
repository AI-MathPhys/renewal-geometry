/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The standard symplectic form: primitive data in every odd spatial rank

The existence converse to the even-rank theorem
(`NCG.Dimension.EvenRank`): **every even dimension carries a nondegenerate
alternating form**, realised by the standard symplectic form on
`K^m × K^m`.  Consequently primitive modular revision data exist in *every*
odd spatial rank (Proposition `prop:primitive-all-odd`): the axioms of the
primitive class cannot select `d_Cl = 3` over `d_Cl = 5, 7, …` — which is
exactly why the manuscript's `3+1` result is a *minimality* theorem
unconditionally, and a *uniqueness* theorem only under the stated closure
or access principles (Remark `rem:minimal-not-unique`).

The graph side of `prop:primitive-all-odd` — a recurrent component with
`b₁ = d` for every `d` — is the bouquet of loops
(`NCG.Multigraph.finrank_H1_bouquet`).

## Main results

* `NCG.stdSymplectic` — the standard symplectic form
  `B((a,b),(c,d)) = Σ aᵢdᵢ − Σ bᵢcᵢ` on `(Fin m → K) × (Fin m → K)`;
* `NCG.stdSymplectic_isAlt`, `NCG.stdSymplectic_nondegenerate` — it is
  alternating and nondegenerate (over any field, in particular `𝔽₂`);
* `NCG.primitive_all_odd` — **Proposition `prop:primitive-all-odd`**: for
  every odd `d` there is a `𝔽₂`-space of dimension `1 + d` carrying a
  nondegenerate alternating form.
-/

namespace NCG

variable {K : Type*} [Field K] {m : ℕ}

/-- The **standard symplectic form** on `K^m × K^m`:
`B((a,b),(c,d)) = Σᵢ aᵢ dᵢ − Σᵢ bᵢ cᵢ`. -/
def stdSymplectic (K : Type*) [Field K] (m : ℕ) :
    LinearMap.BilinForm K ((Fin m → K) × (Fin m → K)) :=
  LinearMap.mk₂ K
    (fun p q => (∑ i, p.1 i * q.2 i) - ∑ i, p.2 i * q.1 i)
    (by
      intro p p' q
      simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_mul,
        Finset.sum_add_distrib]
      ring)
    (by
      intro c p q
      simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
        mul_sub, Finset.mul_sum]
      congr 1 <;> exact Finset.sum_congr rfl fun i _ => by ring)
    (by
      intro p q q'
      simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, mul_add,
        Finset.sum_add_distrib]
      ring)
    (by
      intro c p q
      simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
        mul_sub, Finset.mul_sum]
      congr 1 <;> exact Finset.sum_congr rfl fun i _ => by ring)

@[simp]
theorem stdSymplectic_apply (p q : (Fin m → K) × (Fin m → K)) :
    stdSymplectic K m p q
      = (∑ i, p.1 i * q.2 i) - ∑ i, p.2 i * q.1 i := rfl

/-- The standard symplectic form is alternating. -/
theorem stdSymplectic_isAlt : LinearMap.IsAlt (stdSymplectic K m) := by
  intro p
  rw [stdSymplectic_apply, sub_eq_zero]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- The standard symplectic form is nondegenerate: pairing against the
hyperbolic basis vectors `(eⱼ, 0)` and `(0, eⱼ)` recovers both components. -/
theorem stdSymplectic_nondegenerate :
    LinearMap.Nondegenerate (stdSymplectic K m) := by
  refine (LinearMap.IsRefl.nondegenerate_iff_separatingLeft
    (LinearMap.IsAlt.isRefl stdSymplectic_isAlt)).mpr ?_
  intro p hp
  have h1 : ∀ j, p.1 j = 0 := by
    intro j
    have h := hp (0, Pi.single j 1)
    simpa [Pi.single_apply, mul_ite, Finset.sum_ite_eq'] using h
  have h2 : ∀ j, p.2 j = 0 := by
    intro j
    have h := hp (Pi.single j 1, 0)
    have h' : -(p.2 j) = 0 := by
      simpa [Pi.single_apply, mul_ite, Finset.sum_ite_eq'] using h
    exact neg_eq_zero.mp h'
  exact Prod.ext (funext h1) (funext h2)

/-- The symplectic space `K^m × K^m` has dimension `2m`. -/
theorem finrank_symplectic_space :
    Module.finrank K ((Fin m → K) × (Fin m → K)) = 2 * m := by
  simp [Module.finrank_prod]
  ring

/-- **Proposition `prop:primitive-all-odd`** (primitive revision data exist
in every odd spatial rank): for every odd `d` there is a finite-dimensional
`𝔽₂`-space of dimension `1 + d` — the label module `H¹ ⊕ ⟨t⟩` of the
bouquet with `b₁ = d` — carrying a nondegenerate alternating form.
Together with the even-rank theorem this shows the primitive axioms select
the *parity* of the spatial rank but no particular odd value: `3+1` is
minimal, not unconditionally unique. -/
theorem primitive_all_odd (d : ℕ) (hd : Odd d) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 2) V)
      (_ : FiniteDimensional (ZMod 2) V)
      (B : LinearMap.BilinForm (ZMod 2) V),
      Module.finrank (ZMod 2) V = d + 1 ∧ LinearMap.IsAlt B ∧
        LinearMap.Nondegenerate B := by
  obtain ⟨k, hk⟩ := hd
  refine ⟨(Fin (k + 1) → ZMod 2) × (Fin (k + 1) → ZMod 2), inferInstance,
    inferInstance, inferInstance, stdSymplectic (ZMod 2) (k + 1),
    ?_, stdSymplectic_isAlt, stdSymplectic_nondegenerate⟩
  rw [finrank_symplectic_space]
  omega

end NCG
