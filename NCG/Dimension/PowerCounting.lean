/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Engineering power counting, grade forcing, and the complexity gap

Covers three manuscript-1 records:

* `thm:rg-no-dimension-selection` — the engineering-dimension
  calculus: from the kinetic normalisation (a fermion bilinear with
  one derivative is marginal, `2F + 1 = d + 1`) the fermion dimension
  is `F = d/2`, a fermion bilinear has dimension `d` **independently
  of the inserted Clifford grade**, and the coefficient of a
  first-order gauge-potential-type coupling has dimension `1` in
  every spatial dimension `d` — canonical power counting is
  grade-blind and produces no `b^{3−d}` eigenvalue;
* `thm:minimal-field` — grade forcing: a nonzero element of a graded
  algebra cannot lie in two distinct graded components, so a nonzero
  volume-dual response of exterior degree `d−2` is a degree-one
  (one-reset) observable **iff** `d − 2 = 1`, i.e. `d = 3`;
* `lem:complexity-gap` — the primitive complexity gap: the revision
  algebra `M_{2^{(m+1)/2}}(ℂ)` of an odd-rank primitive datum (per
  the Wedderburn identification of `thm:primitivity-canonical`) has
  complex dimension `2^{m+1}`, and each odd step `m ↦ m+2` multiplies
  it by four.
-/

namespace NCG

/-! ## `thm:rg-no-dimension-selection`: the engineering calculus -/

/-- The fermion field engineering dimension in `(1+d)`-dimensional
spacetime, derived below from the kinetic normalisation. -/
def fermionDim (d : ℕ) : ℚ := d / 2

/-- The engineering dimension of an inserted Clifford-grade matrix:
dimensionless, for every grade — the physical convention that the
spinor-space insertion carries no length scale. -/
def gradeInsertionDim (_k : ℕ) : ℚ := 0

/-- The engineering dimension of a fermion bilinear with a grade-`k`
Clifford insertion: two fermion fields plus the dimensionless
insertion. -/
def bilinearDim (d k : ℕ) : ℚ :=
  fermionDim d + gradeInsertionDim k + fermionDim d

/-- The engineering dimension of the coefficient of a first-order
coupling: the action density has dimension `d+1`, the bilinear
carries `bilinearDim`. -/
def couplingDim (d k : ℕ) : ℚ := (d + 1) - bilinearDim d k

/-- **`thm:rg-no-dimension-selection` (kinetic normalisation)**: the
fermion dimension is the *unique* solution of the kinetic marginality
constraint `2F + 1 = d + 1` (a bilinear with one derivative fills the
action density). -/
theorem fermionDim_unique (d : ℕ) :
    2 * fermionDim d + 1 = d + 1
      ∧ ∀ F : ℚ, 2 * F + 1 = d + 1 → F = fermionDim d := by
  constructor
  · unfold fermionDim
    ring
  · intro F hF
    unfold fermionDim
    linarith

/-- **`thm:rg-no-dimension-selection` (grade blindness)**: the
bilinear dimension does not depend on the inserted Clifford grade. -/
theorem bilinearDim_grade_blind (d k k' : ℕ) :
    bilinearDim d k = bilinearDim d k' := rfl

/-- **`thm:rg-no-dimension-selection` (bilinear dimension)**: a
fermion bilinear has engineering dimension `d`, for every grade. -/
theorem bilinearDim_eq (d k : ℕ) : bilinearDim d k = d := by
  unfold bilinearDim fermionDim gradeInsertionDim
  ring

/-- **`thm:rg-no-dimension-selection` (marginality in every
dimension)**: the coefficient of the first-order coupling has
engineering dimension exactly `1` for every spatial dimension `d` and
every inserted grade `k` — a gauge-potential-type, marginal coupling.
Hence canonical power counting yields no universal `b^{3−d}`
eigenvalue and does not suppress higher-grade currents. -/
theorem couplingDim_eq_one (d k : ℕ) : couplingDim d k = 1 := by
  unfold couplingDim
  rw [bilinearDim_eq]
  ring

/-- **`thm:rg-no-dimension-selection` (no dimension selection)**: the
coupling dimension is the same in every spatial dimension and for
every grade — power counting cannot distinguish `d = 3`. -/
theorem no_rg_dimension_selection (d d' k k' : ℕ) :
    couplingDim d k = couplingDim d' k' := by
  rw [couplingDim_eq_one, couplingDim_eq_one]

/-! ## `thm:minimal-field`: grade forcing -/

/-- **Grade forcing**: in a decomposed graded structure a *nonzero*
element cannot lie in two distinct graded components. -/
theorem grade_eq_of_mem_mem {ιG : Type*} [DecidableEq ιG]
    {A σ : Type*} [AddCommMonoid A] [SetLike σ A]
    [AddSubmonoidClass σ A] (𝒜 : ιG → σ)
    [DirectSum.Decomposition 𝒜]
    {x : A} {i j : ιG} (hi : x ∈ 𝒜 i) (hj : x ∈ 𝒜 j)
    (hx : x ≠ 0) : i = j := by
  by_contra hne
  have h1 : (DirectSum.decompose 𝒜 x i : A) = x :=
    DirectSum.decompose_of_mem_same 𝒜 hi
  have h2 : (DirectSum.decompose 𝒜 x i : A) = 0 :=
    DirectSum.decompose_of_mem_ne 𝒜 hj (Ne.symm hne)
  exact hx (h1.symm.trans h2)

/-- **Theorem `thm:minimal-field`**: if the oriented volume-dual
response is a nonzero element of exterior degree `d − 2` (the degree
computation of the preceding construction) and the minimal-field
hypothesis places it in the degree-one (one-reset observable) sector,
then grade forcing gives `d − 2 = 1`, i.e. `d = 3`.  The deduction —
distinct exterior grades intersect only in `0` — is carried by the
graded decomposition of the exterior algebra, not assumed. -/
theorem minimal_field_degree_forcing {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] {d : ℕ} (hd : 3 ≤ d)
    {x : ExteriorAlgebra R M}
    (hdeg : x ∈ ⋀[R]^(d - 2) M) (hobs : x ∈ ⋀[R]^1 M)
    (hx : x ≠ 0) : d = 3 := by
  have h := grade_eq_of_mem_mem
    (fun i : ℕ => ⋀[R]^i M) hdeg hobs hx
  omega

/-! ## `lem:complexity-gap`: the primitive complexity gap -/

/-- **Lemma `lem:complexity-gap` (operator dimension)**: for odd
spatial Clifford rank `m`, the primitive revision algebra
`M_{2^{(m+1)/2}}(ℂ)` (per the `thm:primitivity-canonical`
identification) has complex dimension `2^{m+1}`. -/
theorem revisionAlgebra_finrank (m : ℕ) (hm : Odd m) :
    Module.finrank ℂ
        (Matrix (Fin (2 ^ ((m + 1) / 2))) (Fin (2 ^ ((m + 1) / 2))) ℂ)
      = 2 ^ (m + 1) := by
  rw [Module.finrank_matrix, Module.finrank_self, mul_one]
  simp only [Fintype.card_fin]
  rw [← pow_add]
  congr 1
  obtain ⟨t, rfl⟩ := hm
  omega

/-- **Lemma `lem:complexity-gap` (the gap)**: each odd step
`m ↦ m + 2` multiplies the primitive revision-algebra dimension by
exactly four. -/
theorem complexity_gap (m : ℕ) (hm : Odd m) :
    Module.finrank ℂ
        (Matrix (Fin (2 ^ ((m + 2 + 1) / 2)))
          (Fin (2 ^ ((m + 2 + 1) / 2))) ℂ)
      = 4 * Module.finrank ℂ
        (Matrix (Fin (2 ^ ((m + 1) / 2))) (Fin (2 ^ ((m + 1) / 2))) ℂ)
      := by
  rw [revisionAlgebra_finrank m hm,
    revisionAlgebra_finrank (m + 2) (by
      obtain ⟨t, rfl⟩ := hm
      exact ⟨t + 1, by omega⟩)]
  rw [show m + 2 + 1 = m + 3 from rfl]
  ring

end NCG
