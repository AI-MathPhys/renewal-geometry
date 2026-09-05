/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The canonical temporal partner and the marked external split

`lem:app-temporal-partner` of the flagship manuscript: let `(V, B)`
be a finite-dimensional nondegenerate alternating space, `W ⊂ V` a
marked hyperplane (the revision label space `K`), and `t ∉ W` the
marked temporal label.  Then:

* `orthogonal_le_self_of_hyperplane` — the `B`-orthogonal of the
  hyperplane lies inside it, so it **is** the radical of the
  restricted form `B|_W`;
* `finrank_hyperplane_orthogonal` / `exists_radical_generator` — the
  radical is one-dimensional, spanned by some `r ≠ 0`;
* `temporal_pairing_ne_zero` — `B t r ≠ 0`; over `𝔽₂` the value is
  `1` (`temporal_pairing_eq_one`), and the generator is the unique
  nonzero radical element (`zmod2_span_nonzero_eq`);
* `spatialCore` — `K₀ = W ⊓ t^⊥`, of codimension two
  (`finrank_spatialCore`), with nondegenerate restriction
  (`spatialCore_restrict_nondegenerate`) and
  `W = span{r} ⊔ K₀` (`hyperplane_eq_radical_sup_core`);
* `isCompl_pair_spatialCore` / `spatialCore_le_orthogonal_pair` /
  `pair_restrict_nondegenerate` — the orthogonal hyperbolic split
  `V = span{t, r} ⟂ K₀` with nondegenerate rank-two temporal block.

Together with the even-rank and minimality records
(`NCG.even_finrank_of_isAlt_nondegenerate`, `NCG.no_two_plus_one`,
`NCG.three_le_of_odd_nondegenerate`) this supplies the symplectic
decomposition step of `thm:external-core`: choosing a hyperbolic pair
`b, c` inside the nondegenerate `K₀` yields the four-dimensional
marked external block `W_ext = span{t, r, b, c}` orthogonal to its
complement.  The corresponding matrix factorization
`M_{2^m}(ℂ) ≅ M₄(ℂ) ⊗ M_{2^{m-2}}(ℂ)` is
`NCG.externalFactorSplit` in `NCG/Algebra/ExternalFactor.lean`.
-/

namespace NCG

open Module Submodule

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V]
  [Module K V] [FiniteDimensional K V]
variable {B : LinearMap.BilinForm K V} {W : Submodule K V} {t : V}

/-! ## The radical of a marked hyperplane -/

/-- Any vector `B`-orthogonal to a hyperplane and outside it would be
orthogonal to the whole space: the hyperplane orthogonal of a
nondegenerate reflexive form lies **inside** the hyperplane, hence is
the radical of the restricted form. -/
theorem orthogonal_le_self_of_hyperplane
    (halt : B.IsAlt) (hnd : B.Nondegenerate)
    (hW : finrank K W + 1 = finrank K V) :
    B.orthogonal W ≤ W := by
  intro x hx
  by_contra hxW
  -- `W ⊔ span{x} = ⊤` because `W` is a hyperplane and `x ∉ W`
  have hlt : W < W ⊔ span K {x} := by
    refine lt_of_le_of_ne le_sup_left fun h => hxW ?_
    have hxmem : x ∈ W ⊔ span K {x} :=
      Submodule.mem_sup_right (mem_span_singleton_self x)
    rwa [← h] at hxmem
  have htop : W ⊔ span K {x} = ⊤ := by
    refine Submodule.eq_top_of_finrank_eq ?_
    have h1 : finrank K W < finrank K (W ⊔ span K {x} : Submodule K V) :=
      Submodule.finrank_lt_finrank_of_lt hlt
    have h2 : finrank K (W ⊔ span K {x} : Submodule K V)
        ≤ finrank K V := Submodule.finrank_le _
    omega
  -- `x` pairs trivially with everything
  have hzero : ∀ n : V, B x n = 0 := by
    intro n
    have hn : n ∈ W ⊔ span K {x} := htop ▸ Submodule.mem_top
    obtain ⟨w, hw, z, hz, rfl⟩ := Submodule.mem_sup.mp hn
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hz
    have hxw : B x w = 0 :=
      halt.isRefl _ _
        ((LinearMap.BilinForm.mem_orthogonal_iff.mp hx) w hw)
    rw [map_add, hxw, map_smul, halt x, smul_zero, add_zero]
  have hx0 : x = 0 := hnd.1 x hzero
  rw [hx0] at hxW
  exact hxW (Submodule.zero_mem W)

/-- The radical of the marked hyperplane is one-dimensional. -/
theorem finrank_hyperplane_orthogonal
    (hnd : B.Nondegenerate)
    (hW : finrank K W + 1 = finrank K V) :
    finrank K (B.orthogonal W) = 1 := by
  rw [LinearMap.BilinForm.finrank_orthogonal hnd]
  omega

/-- The radical of the marked hyperplane is spanned by a single
nonzero vector `r ∈ W`. -/
theorem exists_radical_generator
    (halt : B.IsAlt) (hnd : B.Nondegenerate)
    (hW : finrank K W + 1 = finrank K V) :
    ∃ r : V, r ≠ 0 ∧ r ∈ W ∧ B.orthogonal W = span K {r} := by
  have h1 : finrank K (B.orthogonal W) = 1 :=
    finrank_hyperplane_orthogonal hnd hW
  have hne : B.orthogonal W ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at h1
    omega
  obtain ⟨r, hrmem, hr0⟩ := (Submodule.ne_bot_iff _).mp hne
  refine ⟨r, hr0, orthogonal_le_self_of_hyperplane halt hnd hW hrmem, ?_⟩
  refine (Submodule.eq_of_le_of_finrank_le
    ((Submodule.span_singleton_le_iff_mem r _).mpr hrmem) ?_).symm
  rw [h1, finrank_span_singleton hr0]

/-! ## The temporal pairing -/

/-- **`lem:app-temporal-partner` (pairing)**: the marked temporal
label pairs nontrivially with the radical generator.  If `B t r`
vanished, `r` would be orthogonal to `W ⊔ span{t} = ⊤`. -/
theorem temporal_pairing_ne_zero
    (halt : B.IsAlt) (hnd : B.Nondegenerate)
    (hW : finrank K W + 1 = finrank K V) (ht : t ∉ W)
    {r : V} (hr0 : r ≠ 0) (hrad : B.orthogonal W = span K {r}) :
    B t r ≠ 0 := by
  intro htr
  have hrmem : r ∈ B.orthogonal W :=
    hrad ▸ mem_span_singleton_self r
  -- `W ⊔ span{t} = ⊤`
  have hlt : W < W ⊔ span K {t} := by
    refine lt_of_le_of_ne le_sup_left fun h => ht ?_
    have htmem : t ∈ W ⊔ span K {t} :=
      Submodule.mem_sup_right (mem_span_singleton_self t)
    rwa [← h] at htmem
  have htop : W ⊔ span K {t} = ⊤ := by
    refine Submodule.eq_top_of_finrank_eq ?_
    have h1 : finrank K W < finrank K (W ⊔ span K {t} : Submodule K V) :=
      Submodule.finrank_lt_finrank_of_lt hlt
    have h2 : finrank K (W ⊔ span K {t} : Submodule K V)
        ≤ finrank K V := Submodule.finrank_le _
    omega
  have hzero : ∀ n : V, B r n = 0 := by
    intro n
    have hn : n ∈ W ⊔ span K {t} := htop ▸ Submodule.mem_top
    obtain ⟨w, hw, z, hz, rfl⟩ := Submodule.mem_sup.mp hn
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hz
    have hrw : B r w = 0 :=
      halt.isRefl _ _
        ((LinearMap.BilinForm.mem_orthogonal_iff.mp hrmem) w hw)
    have hrt : B r t = 0 := halt.isRefl _ _ htr
    rw [map_add, hrw, map_smul, hrt, smul_zero, add_zero]
  exact hr0 (hnd.1 r hzero)

/-- Over `𝔽₂` the temporal pairing value is exactly `1`. -/
theorem temporal_pairing_eq_one
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    {B : LinearMap.BilinForm (ZMod 2) V} {W : Submodule (ZMod 2) V}
    {t : V} (halt : B.IsAlt) (hnd : B.Nondegenerate)
    (hW : finrank (ZMod 2) W + 1 = finrank (ZMod 2) V) (ht : t ∉ W)
    {r : V} (hr0 : r ≠ 0)
    (hrad : B.orthogonal W = span (ZMod 2) {r}) :
    B t r = 1 := by
  have h := temporal_pairing_ne_zero halt hnd hW ht hr0 hrad
  have hcases : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases hcases (B t r) with h0 | h1
  · exact absurd h0 h
  · exact h1

/-- Over `𝔽₂` a one-dimensional space has a **unique** nonzero
element: any nonzero vector of `span {r}` equals `r`. -/
theorem zmod2_span_nonzero_eq
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {r x : V}
    (hx : x ∈ span (ZMod 2) {r}) (hx0 : x ≠ 0) : x = r := by
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
  have hcases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  rcases hcases a with h0 | h1
  · exact absurd (by rw [h0, zero_smul]) hx0
  · rw [h1, one_smul]

/-! ## The spatial core `K₀ = W ⊓ t^⊥` -/

variable (B W t) in
/-- The spatial core `K₀ = K ∩ t^⊥` of the marked hyperplane: the
revision labels orthogonal to the temporal label. -/
def spatialCore : Submodule K V :=
  W ⊓ B.orthogonal (span K {t})

omit [FiniteDimensional K V] in
theorem mem_spatialCore_iff {x : V} :
    x ∈ spatialCore B W t ↔ x ∈ W ∧ B t x = 0 := by
  unfold spatialCore
  rw [Submodule.mem_inf, LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · rintro ⟨hxW, hperp⟩
    exact ⟨hxW, hperp t (mem_span_singleton_self t)⟩
  · rintro ⟨hxW, hperp⟩
    refine ⟨hxW, fun n hn => ?_⟩
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hn
    rw [map_smul, LinearMap.smul_apply, hperp, smul_zero]

/-- The radical generator lies outside the spatial core. -/
theorem radical_notMem_spatialCore
    (halt : B.IsAlt) (hnd : B.Nondegenerate)
    (hW : finrank K W + 1 = finrank K V) (ht : t ∉ W)
    {r : V} (hr0 : r ≠ 0) (hrad : B.orthogonal W = span K {r}) :
    r ∉ spatialCore B W t := by
  intro hmem
  exact temporal_pairing_ne_zero halt hnd hW ht hr0 hrad
    (mem_spatialCore_iff.mp hmem).2

/-- **`lem:app-temporal-partner` (dimension)**: the spatial core has
codimension two. -/
theorem finrank_spatialCore
    (halt : B.IsAlt) (hnd : B.Nondegenerate)
    (hW : finrank K W + 1 = finrank K V) (ht : t ∉ W) :
    finrank K (spatialCore B W t) + 2 = finrank K V := by
  obtain ⟨r, hr0, hrW, hrad⟩ := exists_radical_generator halt hnd hW
  have ht0 : t ≠ 0 := fun h => ht (h ▸ Submodule.zero_mem W)
  -- `t^⊥` is a hyperplane
  have hperp : finrank K (B.orthogonal (span K {t}))
      = finrank K V - 1 := by
    rw [LinearMap.BilinForm.finrank_orthogonal hnd,
      finrank_span_singleton ht0]
  -- `W ⊔ t^⊥ = ⊤` since `r ∈ W` pairs nontrivially with `t`
  have hrnotperp : r ∉ B.orthogonal (span K {t}) := by
    intro hmem
    have h := (LinearMap.BilinForm.mem_orthogonal_iff.mp hmem) t
      (mem_span_singleton_self t)
    exact temporal_pairing_ne_zero halt hnd hW ht hr0 hrad h
  have hlt : B.orthogonal (span K {t})
      < W ⊔ B.orthogonal (span K {t}) := by
    refine lt_of_le_of_ne le_sup_right fun h => hrnotperp ?_
    have hrmem : r ∈ W ⊔ B.orthogonal (span K {t}) :=
      Submodule.mem_sup_left hrW
    rwa [← h] at hrmem
  have htop : W ⊔ B.orthogonal (span K {t}) = ⊤ := by
    refine Submodule.eq_top_of_finrank_eq ?_
    have h1 := Submodule.finrank_lt_finrank_of_lt hlt
    have h2 : finrank K
        (W ⊔ B.orthogonal (span K {t}) : Submodule K V)
        ≤ finrank K V := Submodule.finrank_le _
    have h3 : 1 ≤ finrank K V := by omega
    omega
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq W
    (B.orthogonal (span K {t}))
  rw [htop, finrank_top] at hsum
  unfold spatialCore
  omega

/-- **`lem:app-temporal-partner` (splitting of `K`)**: the marked
hyperplane splits as `W = span{r} ⊔ K₀`. -/
theorem hyperplane_eq_radical_sup_core
    (halt : B.IsAlt) (hnd : B.Nondegenerate)
    (hW : finrank K W + 1 = finrank K V) (ht : t ∉ W)
    {r : V} (hr0 : r ≠ 0) (hrad : B.orthogonal W = span K {r}) :
    span K {r} ⊔ spatialCore B W t = W := by
  have hrW : r ∈ W :=
    orthogonal_le_self_of_hyperplane halt hnd hW
      (hrad ▸ mem_span_singleton_self r)
  have hle : span K {r} ⊔ spatialCore B W t ≤ W :=
    sup_le ((Submodule.span_singleton_le_iff_mem r W).mpr hrW)
      inf_le_left
  refine Submodule.eq_of_le_of_finrank_le hle ?_
  -- the sup is strictly larger than the core, whose codim in `W` is 1
  have hrnot : r ∉ spatialCore B W t :=
    radical_notMem_spatialCore halt hnd hW ht hr0 hrad
  have hlt : spatialCore B W t
      < span K {r} ⊔ spatialCore B W t := by
    refine lt_of_le_of_ne le_sup_right fun h => hrnot ?_
    have hrmem : r ∈ span K {r} ⊔ spatialCore B W t :=
      Submodule.mem_sup_left (mem_span_singleton_self r)
    rwa [← h] at hrmem
  have h1 := Submodule.finrank_lt_finrank_of_lt hlt
  have h2 := finrank_spatialCore halt hnd hW ht
  omega

/-- **`lem:app-temporal-partner` (nondegeneracy)**: the restriction
of the form to the spatial core is nondegenerate.  A core vector
orthogonal to the core is also orthogonal to `r` (radical) and to `t`
(definition), hence to all of `V`. -/
theorem spatialCore_restrict_nondegenerate
    (halt : B.IsAlt) (hnd : B.Nondegenerate)
    (hW : finrank K W + 1 = finrank K V) (ht : t ∉ W) :
    (B.restrict (spatialCore B W t)).Nondegenerate := by
  obtain ⟨r, hr0, hrW, hrad⟩ := exists_radical_generator halt hnd hW
  have haltR : (B.restrict (spatialCore B W t)).IsAlt := fun x => halt x
  refine (LinearMap.IsRefl.nondegenerate_iff_separatingLeft
    haltR.isRefl).mpr fun x hx => ?_
  have hxW : (x : V) ∈ W := (mem_spatialCore_iff.mp x.2).1
  have hxt : B t (x : V) = 0 := (mem_spatialCore_iff.mp x.2).2
  -- orthogonal to the radical generator
  have hxr : B (x : V) r = 0 := by
    have hrmem : r ∈ B.orthogonal W :=
      hrad ▸ mem_span_singleton_self r
    exact (LinearMap.BilinForm.mem_orthogonal_iff.mp hrmem) x hxW
  -- orthogonal to all of `W = span{r} ⊔ K₀`
  have hxWperp : ∀ w ∈ W, B (x : V) w = 0 := by
    intro w hw
    rw [← hyperplane_eq_radical_sup_core halt hnd hW ht hr0 hrad]
      at hw
    obtain ⟨z, hz, k, hk, rfl⟩ := Submodule.mem_sup.mp hw
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hz
    have hxk : B (x : V) k = 0 := hx ⟨k, hk⟩
    rw [map_add, map_smul, hxr, hxk, smul_zero, add_zero]
  -- `W ⊔ span{t} = ⊤`, so `x` is in the radical of `B`
  have hlt : W < W ⊔ span K {t} := by
    refine lt_of_le_of_ne le_sup_left fun h => ht ?_
    have htmem : t ∈ W ⊔ span K {t} :=
      Submodule.mem_sup_right (mem_span_singleton_self t)
    rwa [← h] at htmem
  have htop : W ⊔ span K {t} = ⊤ := by
    refine Submodule.eq_top_of_finrank_eq ?_
    have h1 : finrank K W < finrank K (W ⊔ span K {t} : Submodule K V) :=
      Submodule.finrank_lt_finrank_of_lt hlt
    have h2 : finrank K (W ⊔ span K {t} : Submodule K V)
        ≤ finrank K V := Submodule.finrank_le _
    omega
  have hzero : ∀ n : V, B (x : V) n = 0 := by
    intro n
    have hn : n ∈ W ⊔ span K {t} := htop ▸ Submodule.mem_top
    obtain ⟨w, hw, z, hz, rfl⟩ := Submodule.mem_sup.mp hn
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hz
    have hxt' : B (x : V) t = 0 := halt.isRefl _ _ hxt
    rw [map_add, hxWperp w hw, map_smul, hxt', smul_zero, add_zero]
  exact Subtype.ext (hnd.1 x hzero)

/-! ## The orthogonal hyperbolic split `V = span{t, r} ⟂ K₀` -/

omit [FiniteDimensional K V] in
/-- The marked temporal plane is two-dimensional. -/
theorem finrank_span_pair_two (ht : t ∉ W)
    {r : V} (hr0 : r ≠ 0) (hrW : r ∈ W) :
    finrank K (span K ({t, r} : Set V)) = 2 := by
  have hsplit : span K ({t, r} : Set V)
      = span K {t} ⊔ span K {r} := by
    rw [show ({t, r} : Set V) = insert t {r} from rfl,
      Submodule.span_insert]
  have hinf : span K {t} ⊓ span K {r} = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro x ⟨hxt, hxr⟩
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hxt
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp hxr
    by_cases ha : a = 0
    · rw [ha, zero_smul]
    · exfalso
      refine ht ?_
      have : t = a⁻¹ • (b • r) := by
        rw [hb, smul_smul, inv_mul_cancel₀ ha, one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hrW)
  have ht0 : t ≠ 0 := fun h => ht (h ▸ Submodule.zero_mem W)
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq
    (span K {t}) (span K {r})
  rw [hinf, finrank_bot, finrank_span_singleton ht0,
    finrank_span_singleton hr0] at hsum
  rw [hsplit]
  omega

omit [FiniteDimensional K V] in
/-- The spatial core is orthogonal to the marked temporal plane. -/
theorem spatialCore_le_orthogonal_pair
    (halt : B.IsAlt)
    {r : V} (hrad : B.orthogonal W = span K {r}) :
    spatialCore B W t
      ≤ B.orthogonal (span K ({t, r} : Set V)) := by
  intro x hx
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro n hn
  have hxW : x ∈ W := (mem_spatialCore_iff.mp hx).1
  have hxt : B t x = 0 := (mem_spatialCore_iff.mp hx).2
  have hxr : B r x = 0 := by
    have hrmem : r ∈ B.orthogonal W :=
      hrad ▸ mem_span_singleton_self r
    exact halt.isRefl _ _
      ((LinearMap.BilinForm.mem_orthogonal_iff.mp hrmem) x hxW)
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hn
  rw [map_add, LinearMap.add_apply, map_smul, map_smul,
    LinearMap.smul_apply, LinearMap.smul_apply, hxt, hxr,
    smul_zero, smul_zero, add_zero]

/-- **`lem:app-temporal-partner` (orthogonal split)**: the marked
temporal plane and the spatial core are complementary:
`V = span{t, r} ⊕ K₀`, and by `spatialCore_le_orthogonal_pair` the
sum is `B`-orthogonal. -/
theorem isCompl_pair_spatialCore
    (halt : B.IsAlt) (hnd : B.Nondegenerate)
    (hW : finrank K W + 1 = finrank K V) (ht : t ∉ W)
    {r : V} (hr0 : r ≠ 0) (hrad : B.orthogonal W = span K {r}) :
    IsCompl (span K ({t, r} : Set V)) (spatialCore B W t) := by
  have hrW : r ∈ W :=
    orthogonal_le_self_of_hyperplane halt hnd hW
      (hrad ▸ mem_span_singleton_self r)
  have hdim2 : finrank K (span K ({t, r} : Set V)) = 2 :=
    finrank_span_pair_two ht hr0 hrW
  have hdimcore := finrank_spatialCore halt hnd hW ht
  -- disjointness
  have hdisj : Disjoint (span K ({t, r} : Set V))
      (spatialCore B W t) := by
    rw [Submodule.disjoint_def]
    intro x hxpair hxcore
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hxpair
    have hxW : a • t + b • r ∈ W := (mem_spatialCore_iff.mp hxcore).1
    have hxt : B t (a • t + b • r) = 0 :=
      (mem_spatialCore_iff.mp hxcore).2
    -- first `a = 0` because `t ∉ W`
    have ha : a = 0 := by
      by_contra ha
      refine ht ?_
      have : t = a⁻¹ • ((a • t + b • r) - b • r) := by
        rw [add_sub_cancel_right, smul_smul, inv_mul_cancel₀ ha,
          one_smul]
      rw [this]
      exact Submodule.smul_mem _ _
        (Submodule.sub_mem _ hxW (Submodule.smul_mem _ _ hrW))
    -- then `b = 0` because `B t r ≠ 0`
    have hb : b = 0 := by
      rw [ha, zero_smul, zero_add, map_smul, smul_eq_mul] at hxt
      rcases mul_eq_zero.mp hxt with h | h
      · exact h
      · exact absurd h
          (temporal_pairing_ne_zero halt hnd hW ht hr0 hrad)
    rw [ha, hb, zero_smul, zero_smul, add_zero]
  -- codisjointness by dimension count
  refine ⟨hdisj, ?_⟩
  rw [codisjoint_iff]
  refine Submodule.eq_top_of_finrank_eq ?_
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq
    (span K ({t, r} : Set V)) (spatialCore B W t)
  rw [disjoint_iff.mp hdisj, finrank_bot] at hsum
  have hle : finrank K
      ((span K ({t, r} : Set V)) ⊔ spatialCore B W t : Submodule K V)
      ≤ finrank K V := Submodule.finrank_le _
  omega

/-- The restriction of the form to the marked temporal plane
`span{t, r}` is nondegenerate — the hyperbolic temporal block. -/
theorem pair_restrict_nondegenerate
    (halt : B.IsAlt) (hnd : B.Nondegenerate)
    (hW : finrank K W + 1 = finrank K V) (ht : t ∉ W)
    {r : V} (hr0 : r ≠ 0) (hrad : B.orthogonal W = span K {r}) :
    (B.restrict (span K ({t, r} : Set V))).Nondegenerate := by
  have hBtr := temporal_pairing_ne_zero halt hnd hW ht hr0 hrad
  have haltR : (B.restrict (span K ({t, r} : Set V))).IsAlt :=
    fun x => halt x
  refine (LinearMap.IsRefl.nondegenerate_iff_separatingLeft
    haltR.isRefl).mpr fun x hx => ?_
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp x.2
  -- pair `x` against `r` and against `t`
  have hxr : B (x : V) r = 0 := hx ⟨r, Submodule.subset_span (by simp)⟩
  have hxt : B (x : V) t = 0 := hx ⟨t, Submodule.subset_span (by simp)⟩
  have hBrt : B r t = -B t r := (LinearMap.IsAlt.neg halt t r).symm
  -- expand `x = a t + b r` in each pairing
  have hxr' : a * B t r = 0 := by
    rw [← hab, map_add, LinearMap.add_apply, map_smul, map_smul,
      LinearMap.smul_apply, LinearMap.smul_apply, halt r,
      smul_eq_mul, smul_eq_mul, mul_zero, add_zero] at hxr
    exact hxr
  have hxt' : b * B r t = 0 := by
    rw [← hab, map_add, LinearMap.add_apply, map_smul, map_smul,
      LinearMap.smul_apply, LinearMap.smul_apply, halt t,
      smul_eq_mul, smul_eq_mul, mul_zero, zero_add] at hxt
    exact hxt
  have ha : a = 0 := by
    rcases mul_eq_zero.mp hxr' with h | h
    · exact h
    · exact absurd h hBtr
  have hb : b = 0 := by
    rcases mul_eq_zero.mp hxt' with h | h
    · exact h
    · rw [hBrt] at h
      exact absurd (neg_eq_zero.mp h) hBtr
  refine Subtype.ext ?_
  rw [← hab, ha, hb, zero_smul, zero_smul, add_zero]
  simp

end NCG
