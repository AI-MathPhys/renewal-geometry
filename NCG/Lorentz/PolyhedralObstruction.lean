/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The polyhedral obstruction to smooth higher-dimensional emergence

**Theorem `thm:obstruction`**: for `c ≥ 3` the deterministic product-order
cone `[0,∞)^c` is *not* linearly isomorphic to a round Lorentz cone
`L_c = {x₀ ≥ |(x₁,…,x_{c−1})|}`.  The invariant separating them is the set
of **extreme directions**: the orthant has exactly `c` extreme rays (the
coordinate axes), while the round Lorentz cone over a strictly convex
spatial space of dimension `≥ 2` has a *continuum* of extreme rays (its
null generators).  Linear isomorphisms preserve extreme directions, so no
linear isomorphism can carry one onto the other.

This is also the content of Corollary `cor:lorentz-violation`: the `c`
generator axes are intrinsically distinguished (they are the extreme rays
of the causal cone), so the deterministic commuting renewal continuum has
a preferred polyhedral structure and cannot possess full Lorentz symmetry.

## Main definitions

* `NCG.IsExtremeDir` — extreme directions of a convex cone;
* `NCG.orthant` — the deterministic product-order cone `[0,∞)^c`;
* `NCG.lorentzCone` — the round cone `{(t, v) : ‖v‖ ≤ t}`.

## Main results

* `NCG.IsExtremeDir.map` — linear isomorphisms transport extreme
  directions;
* `NCG.isExtremeDir_orthant_iff` — the orthant's extreme directions are
  exactly the positive multiples of the coordinate vectors
  (Corollary `cor:lorentz-violation`: the generator axes are canonical);
* `NCG.isExtremeDir_lorentzCone` — every null direction of the round cone
  is extreme (uses strict convexity via `sameRay_iff_norm_add`);
* `NCG.polyhedral_obstruction` — **Theorem `thm:obstruction`**: no linear
  equivalence maps the round Lorentz cone onto the orthant when the
  spatial space contains two independent directions;
* `NCG.polyhedral_obstruction_complex` — the concrete `1+2`-dimensional
  witness with spatial space `ℂ ≅ ℝ²` (hence all `c ≥ 3` by slicing).
-/

namespace NCG

/-! ### Extreme directions -/

section ExtremeDir

variable {V W : Type*} [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W]

/-- A nonzero `x` in a cone `C` is an **extreme direction** if every
decomposition `x = a + b` inside `C` is trivial: each summand is a scalar
multiple of `x`.  (For salient convex cones this recovers the classical
notion of extreme ray.) -/
def IsExtremeDir (C : Set V) (x : V) : Prop :=
  x ∈ C ∧ x ≠ 0 ∧ ∀ a ∈ C, ∀ b ∈ C, a + b = x → ∃ t : ℝ, a = t • x

/-- Linear equivalences transport extreme directions: the set of extreme
rays is a linear invariant of the cone. -/
theorem IsExtremeDir.map (T : V ≃ₗ[ℝ] W) {C : Set V} {x : V}
    (h : IsExtremeDir C x) : IsExtremeDir (T '' C) (T x) := by
  refine ⟨⟨x, h.1, rfl⟩, fun h0 => h.2.1 (T.map_eq_zero_iff.mp h0), ?_⟩
  rintro a ⟨a', ha', rfl⟩ b ⟨b', hb', rfl⟩ hab
  have hsum : a' + b' = x := T.injective (by rw [map_add]; exact hab)
  obtain ⟨t, ht⟩ := h.2.2 a' ha' b' hb' hsum
  exact ⟨t, by rw [ht, map_smul]⟩

end ExtremeDir

/-! ### The orthant and its extreme rays -/

/-- The deterministic product-order cone `[0,∞)^c` of the commuting
renewal model (Theorem `thm:obstruction`). -/
def orthant (c : ℕ) : Set (Fin c → ℝ) := {x | ∀ i, 0 ≤ x i}

/-- **The orthant has exactly the coordinate axes as extreme rays**
(Corollary `cor:lorentz-violation`): a direction is extreme iff it is a
positive multiple of some `eᵢ`.  In particular the `c` generator
directions are intrinsically distinguished by the causal cone. -/
theorem isExtremeDir_orthant_iff {c : ℕ} {x : Fin c → ℝ} :
    IsExtremeDir (orthant c) x ↔
      ∃ i : Fin c, ∃ t : ℝ, 0 < t ∧ x = t • Pi.single i 1 := by
  constructor
  · rintro ⟨hxC, hx0, hext⟩
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := Function.ne_iff.mp hx0
    have hipos : 0 < x i := (hxC i).lt_of_ne (Ne.symm hi)
    have hmem1 : (Pi.single i (x i) : Fin c → ℝ) ∈ orthant c := by
      intro j
      rcases eq_or_ne j i with rfl | hj
      · rw [Pi.single_eq_same]; exact hipos.le
      · rw [Pi.single_eq_of_ne hj]
    have hmem2 : x - Pi.single i (x i) ∈ orthant c := by
      intro j
      rcases eq_or_ne j i with rfl | hj
      · simp [Pi.single_eq_same]
      · simpa [Pi.single_eq_of_ne hj] using hxC j
    obtain ⟨t, ht⟩ := hext _ hmem1 _ hmem2 (add_sub_cancel _ _)
    have hti : x i = t * x i := by
      have := congrFun ht i
      rwa [Pi.single_eq_same, Pi.smul_apply, smul_eq_mul] at this
    have ht1 : t = 1 := by
      have h1 : (1 : ℝ) * x i = t * x i := by rw [one_mul]; exact hti
      exact (mul_right_cancel₀ hi h1).symm
    refine ⟨i, x i, hipos, funext fun j => ?_⟩
    rcases eq_or_ne j i with rfl | hj
    · rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
    · have := congrFun ht j
      rw [Pi.single_eq_of_ne hj, Pi.smul_apply, smul_eq_mul, ht1,
        one_mul] at this
      rw [Pi.smul_apply, Pi.single_eq_of_ne hj, smul_eq_mul, mul_zero,
        ← this]
  · rintro ⟨i, t, htpos, rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · intro j
      rcases eq_or_ne j i with rfl | hj
      · rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
        exact htpos.le
      · rw [Pi.smul_apply, Pi.single_eq_of_ne hj, smul_eq_mul, mul_zero]
    · intro h0
      have := congrFun h0 i
      rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one,
        Pi.zero_apply] at this
      exact htpos.ne' this
    · intro a ha b hb hab
      have hzero : ∀ j, j ≠ i → a j = 0 := by
        intro j hj
        have hsum : a j + b j = 0 := by
          have := congrFun hab j
          rwa [Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne hj,
            smul_eq_mul, mul_zero] at this
        have := ha j; have := hb j
        linarith
      have ht0 : t ≠ 0 := htpos.ne'
      refine ⟨a i / t, funext fun j => ?_⟩
      rcases eq_or_ne j i with rfl | hj
      · rw [Pi.smul_apply, Pi.smul_apply, Pi.single_eq_same,
          smul_eq_mul, smul_eq_mul, mul_one]
        field_simp
      · rw [hzero j hj, Pi.smul_apply, Pi.smul_apply,
          Pi.single_eq_of_ne hj, smul_eq_mul, smul_eq_mul, mul_zero,
          mul_zero]

/-! ### The round Lorentz cone and its null extreme rays -/

/-- The **round Lorentz cone** `{(t, v) : ‖v‖ ≤ t}` over a normed spatial
space `E` (Theorem `thm:obstruction`). -/
def lorentzCone (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Set (ℝ × E) := {p | ‖p.2‖ ≤ p.1}

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Null directions of the round cone are extreme** (Theorem
`thm:obstruction`, second half): over a strictly convex spatial space,
every null vector `(‖v‖, v)` generates an extreme ray of the Lorentz
cone.  The proof is the equality case of the triangle inequality
(`sameRay_iff_norm_add`). -/
theorem isExtremeDir_lorentzCone [StrictConvexSpace ℝ E] {v : E}
    (hv : v ≠ 0) : IsExtremeDir (lorentzCone E) ((‖v‖ : ℝ), v) := by
  have hmem : ((‖v‖ : ℝ), v) ∈ lorentzCone E := by
    simp only [lorentzCone, Set.mem_setOf_eq]
    exact le_rfl
  refine ⟨hmem, fun h0 => hv (congrArg Prod.snd h0), ?_⟩
  rintro ⟨a₁, a₂⟩ ha ⟨b₁, b₂⟩ hb hab
  simp only [lorentzCone, Set.mem_setOf_eq] at ha hb
  have ha' : ‖a₂‖ ≤ a₁ := ha
  have hb' : ‖b₂‖ ≤ b₁ := hb
  have h1 : a₁ + b₁ = ‖v‖ := congrArg Prod.fst hab
  have h2 : a₂ + b₂ = v := congrArg Prod.snd hab
  have htri : ‖v‖ ≤ ‖a₂‖ + ‖b₂‖ := by rw [← h2]; exact norm_add_le _ _
  have hea : ‖a₂‖ = a₁ := by linarith
  have heb : ‖b₂‖ = b₁ := by linarith
  have hadd : ‖a₂ + b₂‖ = ‖a₂‖ + ‖b₂‖ := by
    rw [h2, hea, heb]; exact h1.symm
  obtain ⟨s, t, hs, ht, hst, ha2, hb2⟩ :=
    (sameRay_iff_norm_add.mpr hadd).exists_eq_smul_add
  rw [h2] at ha2
  refine ⟨s, Prod.ext_iff.mpr ⟨?_, ?_⟩⟩
  · show a₁ = (s • ((‖v‖ : ℝ), v)).1
    rw [Prod.smul_fst, smul_eq_mul, ← hea, ha2, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg hs]
  · show a₂ = (s • ((‖v‖ : ℝ), v)).2
    rw [Prod.smul_snd]
    exact ha2

/-! ### The obstruction theorem -/

/-- **Theorem `thm:obstruction`** (polyhedral obstruction to smooth
higher-dimensional emergence): if the spatial space `E` is strictly
convex and contains two linearly independent directions, then *no* linear
equivalence carries the round Lorentz cone over `E` onto the orthant
`[0,∞)^c`.  The orthant has at most `c` pairwise non-proportional extreme
directions, while the null family `u + r·w` (`r ∈ ℝ`) provides a
continuum of them in the round cone; linear equivalences preserve extreme
directions. -/
theorem polyhedral_obstruction [StrictConvexSpace ℝ E] {u w : E}
    (huw : LinearIndependent ℝ ![u, w]) {c : ℕ}
    (T : (ℝ × E) ≃ₗ[ℝ] (Fin c → ℝ)) :
    T '' lorentzCone E ≠ orthant c := by
  intro hT
  have hpair := LinearIndependent.pair_iff.mp huw
  have hprofile_ne : ∀ r : ℝ, u + r • w ≠ 0 := fun r h =>
    one_ne_zero (hpair 1 r (by rwa [one_smul])).1
  have hex : ∀ r : ℝ, ∃ i : Fin c, ∃ t : ℝ, 0 < t ∧
      T ((‖u + r • w‖ : ℝ), u + r • w) = t • Pi.single i 1 := by
    intro r
    have h1 := (isExtremeDir_lorentzCone (hprofile_ne r)).map T
    rw [hT] at h1
    exact isExtremeDir_orthant_iff.mp h1
  choose f t ht hf using hex
  have hinj : Function.Injective f := by
    intro r r' hrr
    have hT1 : T ((‖u + r • w‖ : ℝ), u + r • w)
        = (t r / t r') • T ((‖u + r' • w‖ : ℝ), u + r' • w) := by
      rw [hf r, hf r', hrr, smul_smul, div_mul_cancel₀ _ (ht r').ne']
    have hEq : ((‖u + r • w‖ : ℝ), u + r • w)
        = (t r / t r') • ((‖u + r' • w‖ : ℝ), u + r' • w) :=
      T.injective (by rw [map_smul]; exact hT1)
    have hsnd : u + r • w = (t r / t r') • (u + r' • w) :=
      congrArg Prod.snd hEq
    set lam := t r / t r' with hlam
    have h' : u + r • w = lam • u + (lam * r') • w := by
      rw [hsnd, smul_add, smul_smul]
    have hexp : (1 - lam) • u + (r - lam * r') • w
        = (u + r • w) - (lam • u + (lam * r') • w) := by module
    have hzero : (1 - lam) • u + (r - lam * r') • w = 0 := by
      rw [hexp, ← h', sub_self]
    obtain ⟨hc1, hc2⟩ := hpair _ _ hzero
    have hlam1 : lam = 1 := by linarith
    rw [hlam1, one_mul] at hc2
    linarith
  exact (not_finite_iff_infinite.mpr inferInstance : ¬Finite ℝ)
    (Finite.of_injective f hinj)

/-- **Theorem `thm:obstruction`, concrete witness**: the round Lorentz
cone over the plane `ℂ ≅ ℝ²` — the tangent cone of `2+1`-dimensional
Minkowski space — is not linearly isomorphic to any orthant.  Together
with `Fin`-slicing this covers every `c ≥ 3`; for `c = 2` the cone *is*
polyhedral, which is why the 2d Minkowski identification of Theorem
`thm:minkowski-2d` (`NCG.minkowski_causal_order`) is consistent. -/
theorem polyhedral_obstruction_complex {c : ℕ}
    (T : (ℝ × ℂ) ≃ₗ[ℝ] (Fin c → ℝ)) :
    T '' lorentzCone ℂ ≠ orthant c := by
  have h : LinearIndependent ℝ ![(1 : ℂ), Complex.I] := by
    rw [← Complex.coe_basisOneI]
    exact Complex.basisOneI.linearIndependent
  exact polyhedral_obstruction h T

end NCG
