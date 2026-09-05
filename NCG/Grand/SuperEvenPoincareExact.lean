/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.SuperCommutationExact
import NCG.Grand.PolynomialPoincareExact

/-!
# The super-algebra-valued even Poincaré lemma

Mixed-sector machinery for `thm:SM-common-action-integrability` (RG.1/RG.2).

Over the polynomial coefficient ring `R₀ = R[x^σ]`, the coordinate connections
(`coordConn`) differentiate the odd generator module coefficientwise; the resulting even
derivations `∂ᵢ` on the super-algebra kill the standard exterior basis vectors
(`evenDeriv_fullBasis`) and hence act coefficientwise
(`repr_evenDeriv`).  Consequently the **even Poincaré lemma holds with values in the
super-algebra** (`exists_even_potential`, `even_curl_iff_exists_potential`): a curl-free
family of even super-forces is the gradient of one super-action, componentwise by the
scalar polynomial Poincaré lemma.
-/

open CliffordAlgebra MvPolynomial

namespace NCG
namespace SuperPoincare

open NCG.SuperDeriv

variable {σ : Type*} [Fintype σ] {R : Type*} [CommRing R] [Algebra ℚ R]
variable {ιo : Type*} [LinearOrder ιo]
variable {M : Type*} [AddCommGroup M] [Module (MvPolynomial σ R) M]
variable (bM : Module.Basis ιo (MvPolynomial σ R) M)

/-- The coordinatewise connection over `pderiv i`: differentiate the basis coefficients. -/
noncomputable def coordConn (i : σ) :
    Connection (R := R) (pderiv i : Derivation R (MvPolynomial σ R) (MvPolynomial σ R))
      M where
  toFun m := bM.repr.symm
    (Finsupp.mapRange (pderiv i) (map_zero _) (bM.repr m))
  map_add' m n := by
    rw [map_add, Finsupp.mapRange_add (map_add _), map_add]
  map_smul' r m := by
    rw [map_smul]
    have hcoeff : Finsupp.mapRange (pderiv i) (map_zero _) (r • bM.repr m)
        = pderiv i r • bM.repr m + r • Finsupp.mapRange (pderiv i) (map_zero _)
          (bM.repr m) := by
      ext a
      simp only [Finsupp.mapRange_apply, Finsupp.add_apply, Finsupp.smul_apply,
        smul_eq_mul]
      rw [pderiv_mul]
    rw [hcoeff, map_add, map_smul, map_smul, LinearEquiv.symm_apply_apply]

omit [Fintype σ] [Algebra ℚ R] [LinearOrder ιo] in
theorem coordConn_apply (i : σ) (m : M) :
    (coordConn bM i).toFun m = bM.repr.symm
      (Finsupp.mapRange (pderiv i) (map_zero _) (bM.repr m)) := rfl

omit [Fintype σ] [Algebra ℚ R] [LinearOrder ιo] in
/-- The coordinate connections kill the basis vectors. -/
theorem coordConn_basis (i : σ) (a : ιo) : (coordConn bM i).toFun (bM a) = 0 := by
  rw [coordConn_apply, Module.Basis.repr_self]
  rw [show Finsupp.mapRange (pderiv i) (map_zero _) (Finsupp.single a 1)
      = (0 : ιo →₀ MvPolynomial σ R) from ?_]
  · exact map_zero _
  · rw [Finsupp.mapRange_single, pderiv_one, Finsupp.single_zero]

omit [Fintype σ] [Algebra ℚ R] [LinearOrder ιo] in
/-- The coordinate connections are compatible with the coordinate duals. -/
theorem coord_coordConn (i : σ) (a : ιo) (m : M) :
    bM.coord a ((coordConn bM i).toFun m) = pderiv i (bM.coord a m) := by
  rw [coordConn_apply, Module.Basis.coord_apply, Module.Basis.coord_apply,
    LinearEquiv.apply_symm_apply, Finsupp.mapRange_apply]

omit [Fintype σ] [Algebra ℚ R] in
/-- The even derivation kills any product of generators with flat coefficients. -/
theorem evenDeriv_list_prod_iota {d : Derivation R (MvPolynomial σ R) (MvPolynomial σ R)}
    (co : Connection d M) (l : List M) (hl : ∀ m ∈ l, co.toFun m = 0) :
    evenDeriv d co (l.map (ExteriorAlgebra.ι (MvPolynomial σ R))).prod = 0 := by
  induction l with
  | nil =>
    rw [List.map_nil, List.prod_nil]
    exact evenDeriv_one d co
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, evenDeriv_mul,
      ih fun m hm => hl m (List.mem_cons_of_mem a hm),
      evenDeriv_iota]
    rw [show co a = co.toFun a from rfl, hl a List.mem_cons_self, map_zero, mul_zero,
      zero_mul, add_zero]

/-- The full standard basis of the super-algebra: graded collection of the per-grade
exterior-power bases. -/
noncomputable def fullBasis :
    Module.Basis (Σ p : ℕ, Set.powersetCard ιo p) (MvPolynomial σ R)
      (ExteriorAlgebra (MvPolynomial σ R) M) :=
  (DirectSum.Decomposition.isInternal
    (fun p : ℕ => ⋀[MvPolynomial σ R]^p M)).collectedBasis
    fun p => bM.exteriorPower (n := p)

omit [Fintype σ] [Algebra ℚ R] in
/-- The even derivations kill the standard basis vectors. -/
theorem evenDeriv_fullBasis (i : σ) (st : Σ p : ℕ, Set.powersetCard ιo p) :
    evenDeriv (pderiv i) (coordConn bM i) (fullBasis bM st) = 0 := by
  have hcoe : fullBasis bM st
      = (bM.exteriorPower (n := st.1) st.2 : ExteriorAlgebra (MvPolynomial σ R) M) := by
    rw [fullBasis]
    rw [DirectSum.IsInternal.collectedBasis_coe]
  rw [hcoe, exteriorPower.basis_apply]
  rw [show ((exteriorPower.ιMulti_family (MvPolynomial σ R) st.1 (⇑bM) st.2 :
        (⋀[MvPolynomial σ R]^st.1 M : Submodule (MvPolynomial σ R) _))
        : ExteriorAlgebra (MvPolynomial σ R) M)
      = ExteriorAlgebra.ιMulti (MvPolynomial σ R) st.1
        ((⇑bM) ∘ (Set.powersetCard.ofFinEmbEquiv.symm st.2)) from rfl]
  rw [ExteriorAlgebra.ιMulti_apply]
  have h := evenDeriv_list_prod_iota (coordConn bM i)
    (List.ofFn fun k => bM (Set.powersetCard.ofFinEmbEquiv.symm st.2 k))
    (by
      intro m hm
      obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hm
      exact coordConn_basis bM i _)
  rw [List.map_ofFn] at h
  exact h

omit [Fintype σ] [Algebra ℚ R] [LinearOrder ιo] in
/-- The even derivation distributes over finite sums. -/
theorem evenDeriv_finset_sum {d : Derivation R (MvPolynomial σ R) (MvPolynomial σ R)}
    (co : Connection d M) {α : Type*} (s : Finset α)
    (f : α → ExteriorAlgebra (MvPolynomial σ R) M) :
    evenDeriv d co (∑ a ∈ s, f a) = ∑ a ∈ s, evenDeriv d co (f a) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    exact evenDeriv_zero d co
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, evenDeriv_add, ih]

omit [Fintype σ] [Algebra ℚ R] in
/-- The even derivations act coefficientwise on the standard basis expansion. -/
theorem evenDeriv_linearCombination (i : σ)
    (x : ExteriorAlgebra (MvPolynomial σ R) M) :
    evenDeriv (pderiv i) (coordConn bM i) x
      = Finsupp.sum ((fullBasis bM).repr x) fun st c =>
          pderiv i c • fullBasis bM st := by
  conv_lhs => rw [← Module.Basis.linearCombination_repr (fullBasis bM) x]
  rw [Finsupp.linearCombination_apply, Finsupp.sum, evenDeriv_finset_sum, Finsupp.sum]
  refine Finset.sum_congr rfl fun st _ => ?_
  rw [evenDeriv_smul, evenDeriv_fullBasis, smul_zero, add_zero]

omit [Fintype σ] [Algebra ℚ R] in
/-- The even derivations are coefficientwise `pderiv` in the standard basis. -/
theorem repr_evenDeriv (i : σ) (x : ExteriorAlgebra (MvPolynomial σ R) M) :
    (fullBasis bM).repr (evenDeriv (pderiv i) (coordConn bM i) x)
      = Finsupp.mapRange (pderiv i) (map_zero _) ((fullBasis bM).repr x) := by
  classical
  rw [evenDeriv_linearCombination]
  ext su
  rw [Finsupp.mapRange_apply, Finsupp.sum, map_sum, Finsupp.finsetSum_apply]
  rw [Finset.sum_congr rfl fun st _ => by
    rw [map_smul, Module.Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one,
      Finsupp.single_apply]]
  rw [Finset.sum_ite_eq' ((fullBasis bM).repr x).support su
    (fun st => pderiv i (((fullBasis bM).repr x) st))]
  by_cases hsu : su ∈ ((fullBasis bM).repr x).support
  · rw [if_pos hsu]
  · rw [if_neg hsu, Finsupp.notMem_support_iff.mp hsu, map_zero]

omit [Fintype σ] [Algebra ℚ R] in
/-- Mixed even partials commute on the super-algebra. -/
theorem evenDeriv_comm (i j : σ) (x : ExteriorAlgebra (MvPolynomial σ R) M) :
    evenDeriv (pderiv i) (coordConn bM i) (evenDeriv (pderiv j) (coordConn bM j) x)
      = evenDeriv (pderiv j) (coordConn bM j)
          (evenDeriv (pderiv i) (coordConn bM i) x) := by
  apply (fullBasis bM).repr.injective
  rw [repr_evenDeriv, repr_evenDeriv, repr_evenDeriv, repr_evenDeriv]
  ext st
  simp only [Finsupp.mapRange_apply]
  exact congrArg (coeff _) (PolyPoincare.pderiv_pderiv (R := R) i j _)

/-- **The super-algebra-valued even Poincaré lemma (existence)**: an even curl-free family
of super-forces is the even gradient of one super-action. -/
theorem exists_even_potential (F : σ → ExteriorAlgebra (MvPolynomial σ R) M)
    (hcurl : ∀ i j, evenDeriv (pderiv i) (coordConn bM i) (F j)
      = evenDeriv (pderiv j) (coordConn bM j) (F i)) :
    ∃ S : ExteriorAlgebra (MvPolynomial σ R) M,
      ∀ i, evenDeriv (pderiv i) (coordConn bM i) S = F i := by
  classical
  have hscal : ∀ st, ∀ i j : σ, pderiv i ((fullBasis bM).repr (F j) st)
      = pderiv j ((fullBasis bM).repr (F i) st) := by
    intro st i j
    have h := congrArg (fun z => ((fullBasis bM).repr z) st) (hcurl i j)
    simpa only [repr_evenDeriv, Finsupp.mapRange_apply] using h
  choose Spot hSpot using fun st =>
    PolyPoincare.exists_potential (fun i => (fullBasis bM).repr (F i) st)
      (fun i j => hscal st i j)
  set T : Finset (Σ p : ℕ, Set.powersetCard ιo p) :=
    Finset.univ.biUnion (fun i : σ => ((fullBasis bM).repr (F i)).support) with hT
  refine ⟨∑ st ∈ T, Spot st • fullBasis bM st, fun j => ?_⟩
  rw [evenDeriv_finset_sum, Finset.sum_congr rfl fun st _ => by
    rw [evenDeriv_smul, evenDeriv_fullBasis, smul_zero, add_zero, hSpot st j]]
  conv_rhs => rw [← Module.Basis.linearCombination_repr (fullBasis bM) (F j)]
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  refine (Finset.sum_subset
    (fun st hst => Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hst⟩)
    (fun st _ hst => ?_)).symm
  rw [Finsupp.notMem_support_iff.mp hst, zero_smul]

/-- **RG.1/RG.2, even sector with super-algebra values**: the even curl vanishes exactly
when the even super-force family is an even gradient. -/
theorem even_curl_iff_exists_potential (F : σ → ExteriorAlgebra (MvPolynomial σ R) M) :
    (∀ i j, evenDeriv (pderiv i) (coordConn bM i) (F j)
      = evenDeriv (pderiv j) (coordConn bM j) (F i)) ↔
    ∃ S : ExteriorAlgebra (MvPolynomial σ R) M,
      ∀ i, evenDeriv (pderiv i) (coordConn bM i) S = F i := by
  constructor
  · exact exists_even_potential bM F
  · rintro ⟨S, hS⟩ i j
    rw [← hS i, ← hS j]
    exact evenDeriv_comm bM i j S

end SuperPoincare
end NCG
