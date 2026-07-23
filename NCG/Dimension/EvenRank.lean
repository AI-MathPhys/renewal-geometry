/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Even rank of nondegenerate alternating forms: no 2+1 spacetime

The parity backbone of the manuscript's dimension selection
(Theorem `thm:minimal-nondegenerate-3plus1` (i)–(ii)): a **nondegenerate
alternating bilinear form exists only in even dimension**.  Applied to the
modular commutator form `ω` on `H_full = H¹(G,ℤ/2) ⊕ ⟨t⟩`, primitivity
(nondegeneracy of `ω`) forces `1 + d_Cl` to be even, so:

* the spatial Clifford rank `d_Cl` is **odd** — Theorem
  `thm:minimal-nondegenerate-3plus1` (i);
* `2+1` is **impossible**: a three-dimensional space carries no
  nondegenerate alternating form — Theorem
  `thm:minimal-nondegenerate-3plus1` (ii).

Together with spatial nondegeneracy (which excludes `1+1`,
`NCG.Dimension.AccessSelection`) this makes `3+1` the minimal nondegenerate
primitive endpoint.

The proof is the classical hyperbolic-pair induction, carried out over an
arbitrary field — so in particular over `𝔽₂ = ZMod 2`, where alternation is
strictly stronger than skew-symmetry and the determinant parity argument
fails: a nonzero vector `x` has a partner `y` with `B x y = 1`; the plane
`P = span{x, y}` is `B`-nondegenerate, so `V = P ⊕ P^⊥` with the
restriction to `P^⊥` again alternating and nondegenerate; induct.

## Main results

* `NCG.even_finrank_of_isAlt_nondegenerate'` — the induction;
* `NCG.even_finrank_of_isAlt_nondegenerate` — `Even (finrank K V)`;
* `NCG.not_nondegenerate_of_isAlt_of_odd_finrank` — odd-dimensional spaces
  carry no nondegenerate alternating form;
* `NCG.no_two_plus_one` — the `2+1` exclusion over `𝔽₂`
  (`thm:minimal-nondegenerate-3plus1` (ii));
* `NCG.odd_spatial_rank_of_isAlt_nondegenerate` — the spatial rank
  `d_Cl = finrank − 1` is odd (`thm:minimal-nondegenerate-3plus1` (i)).
-/

namespace NCG

open Module LinearMap.BilinForm

universe u

variable {K : Type*} [Field K]

/-- **Nondegenerate alternating forms exist only in even dimension** —
the hyperbolic-pair induction, parametrised by the dimension. -/
theorem even_finrank_of_isAlt_nondegenerate' :
    ∀ (n : ℕ) {V : Type u} [AddCommGroup V] [Module K V]
      [FiniteDimensional K V] (B : LinearMap.BilinForm K V),
      LinearMap.IsAlt B → LinearMap.Nondegenerate B →
      Module.finrank K V = n → Even n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro V _ _ _ B halt hnd hrank
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      exact ⟨0, rfl⟩
    -- antisymmetry from alternation
    have hanti : ∀ u v : V, B u v = -B v u := by
      intro u v
      have h0 := halt (u + v)
      simp only [map_add, LinearMap.add_apply, halt u, halt v, zero_add,
        add_zero] at h0
      linear_combination h0
    have hrefl : LinearMap.IsRefl B := LinearMap.IsAlt.isRefl halt
    -- pick a nonzero vector and a hyperbolic partner
    have hnontriv : Nontrivial V := by
      rw [← Module.finrank_pos_iff (R := K)]
      omega
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    have hy : ∃ y₀, B x y₀ ≠ 0 := by
      by_contra h
      push Not at h
      exact hx (hnd.1 x h)
    obtain ⟨y₀, hy₀⟩ := hy
    obtain ⟨y, hxy⟩ : ∃ y : V, B x y = 1 :=
      ⟨(B x y₀)⁻¹ • y₀, by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hy₀]⟩
    have hyx : B y x = -1 := by
      rw [hanti y x, hxy]
    -- the hyperbolic plane
    set P := Submodule.span K {x, y} with hPdef
    have hxP : x ∈ P := Submodule.subset_span (by simp)
    have hyP : y ∈ P := Submodule.subset_span (by simp)
    have hli : LinearIndependent K ![x, y] := by
      rw [LinearIndependent.pair_iff]
      intro s t hst
      have h1 : B x (s • x + t • y) = 0 := by rw [hst, map_zero]
      have h2 : B y (s • x + t • y) = 0 := by rw [hst, map_zero]
      simp only [map_add, map_smul, smul_eq_mul, halt x, halt y, hxy, hyx,
        mul_zero, mul_one, mul_neg, zero_add, add_zero] at h1 h2
      exact ⟨neg_eq_zero.mp h2, h1⟩
    have hP2 : Module.finrank K P = 2 := by
      have hcard := finrank_span_eq_card hli
      rw [Matrix.range_cons_cons_empty] at hcard
      rw [hPdef, hcard]
      simp
    -- the restriction to the plane is alternating and nondegenerate
    have haltP : LinearMap.IsAlt (B.restrict P) := fun w => halt (w : V)
    have hreflP : LinearMap.IsRefl (B.restrict P) :=
      LinearMap.IsAlt.isRefl haltP
    have hrestP : (B.restrict P).Nondegenerate := by
      refine (LinearMap.IsRefl.nondegenerate_iff_separatingLeft hreflP).mpr ?_
      intro w hall
      have hw : (w : V) ∈ Submodule.span K {x, y} := w.2
      rw [Submodule.mem_span_pair] at hw
      obtain ⟨a, b, hab⟩ := hw
      have h1 : B (w : V) x = 0 := hall ⟨x, hxP⟩
      have h2 : B (w : V) y = 0 := hall ⟨y, hyP⟩
      rw [← hab] at h1 h2
      simp only [map_add, map_smul, LinearMap.add_apply,
        LinearMap.smul_apply, smul_eq_mul, halt x, halt y, hxy, hyx,
        mul_zero, mul_one, mul_neg, zero_add, add_zero] at h1 h2
      have hcoe : (w : V) = 0 := by
        rw [← hab, h2, neg_eq_zero.mp h1]
        simp
      exact Subtype.ext hcoe
    -- split off the plane and induct on its orthogonal complement
    have hcompl : IsCompl P (B.orthogonal P) :=
      isCompl_orthogonal_of_restrict_nondegenerate hrefl hrestP
    have hdisjW : Disjoint (B.orthogonal P)
        (B.orthogonal (B.orthogonal P)) := by
      rw [orthogonal_orthogonal hnd hrefl]
      exact hcompl.disjoint.symm
    have hrestW : (B.restrict (B.orthogonal P)).Nondegenerate :=
      nondegenerate_restrict_of_disjoint_orthogonal B hrefl hdisjW
    have haltW : LinearMap.IsAlt (B.restrict (B.orthogonal P)) := fun w =>
      halt (w : V)
    have hsum := Submodule.finrank_add_eq_of_isCompl hcompl
    rw [hP2, hrank] at hsum
    have hn2 : 2 ≤ n := by
      have hle := Submodule.finrank_le P
      rw [hP2, hrank] at hle
      exact hle
    have hrankW : Module.finrank K (B.orthogonal P) = n - 2 := by omega
    have heven := ih (n - 2) (by omega) (B.restrict (B.orthogonal P))
      haltW hrestW hrankW
    obtain ⟨k, hk⟩ := heven
    exact ⟨k + 1, by omega⟩

variable {V : Type u} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- **Even-rank theorem**: a finite-dimensional space carrying a
nondegenerate alternating bilinear form has even dimension.  This is the
parity mechanism behind primitivity in the modular revision sector: the
commutator form `ω` is alternating, so primitivity forces the full rank
`1 + d_Cl` to be even. -/
theorem even_finrank_of_isAlt_nondegenerate (B : LinearMap.BilinForm K V)
    (halt : LinearMap.IsAlt B) (hnd : LinearMap.Nondegenerate B) :
    Even (Module.finrank K V) :=
  even_finrank_of_isAlt_nondegenerate' (Module.finrank K V) B halt hnd rfl

/-- Odd-dimensional spaces carry no nondegenerate alternating form. -/
theorem not_nondegenerate_of_isAlt_of_odd_finrank
    (B : LinearMap.BilinForm K V) (halt : LinearMap.IsAlt B)
    (hodd : Odd (Module.finrank K V)) : ¬LinearMap.Nondegenerate B := by
  intro hnd
  obtain ⟨k, hk⟩ := even_finrank_of_isAlt_nondegenerate B halt hnd
  obtain ⟨m, hm⟩ := hodd
  omega

/-- **`2+1` is impossible** (Theorem `thm:minimal-nondegenerate-3plus1`
(ii)): a three-dimensional `𝔽₂`-space — the label module
`H_full = H¹ ⊕ ⟨t⟩` of a would-be `2+1` endpoint — carries no nondegenerate
alternating form, so no primitive modular revision datum exists there. -/
theorem no_two_plus_one {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (h3 : Module.finrank (ZMod 2) W = 3)
    (B : LinearMap.BilinForm (ZMod 2) W) (halt : LinearMap.IsAlt B) :
    ¬LinearMap.Nondegenerate B :=
  not_nondegenerate_of_isAlt_of_odd_finrank B halt (by rw [h3]; decide)

/-- **The spatial rank is odd** (Theorem `thm:minimal-nondegenerate-3plus1`
(i)): for a primitive (nondegenerate alternating) modular form on a space
of positive dimension `1 + d_Cl`, the spatial Clifford rank
`d_Cl = finrank − 1` is odd.  With `2+1` excluded and `1+1` spatially
degenerate, `3+1` is the minimal nondegenerate primitive endpoint. -/
theorem odd_spatial_rank_of_isAlt_nondegenerate
    (B : LinearMap.BilinForm K V) (halt : LinearMap.IsAlt B)
    (hnd : LinearMap.Nondegenerate B) (hpos : 0 < Module.finrank K V) :
    Odd (Module.finrank K V - 1) :=
  Nat.Even.sub_odd hpos (even_finrank_of_isAlt_nondegenerate B halt hnd)
    odd_one

end NCG
