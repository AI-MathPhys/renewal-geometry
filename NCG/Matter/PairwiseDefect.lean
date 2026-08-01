/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Exact pairwise-source defect (`thm:v5-pairwise-defect`, SM manuscript)

On the set `𝒯` of the `24` oriented nonbacktracking tetrahedral
turns `(i,j,k)` (pairwise distinct vertices of `K₄`), let
`μ(i,j,k) = sgn(i,j,k,ℓ)` (`ℓ` the omitted vertex, sign computed
as the inversion parity of the four-term sequence), and let
`R_{≤2} ⊂ L²(𝒯)` be the span of all functions depending on at
most two of the three displayed turn coordinates.  Then

* `E[μ | t_S] = 0` for every proper coordinate subset: all
  conditional fiber sums of `μ` over the three coordinate pairs
  vanish (`muZ_fiber12/13/23`);
* `R_{≤2}ᗮ = ℂμ` (`orthogonal_pairwiseSpan`), whence the boxed
  orthogonal decomposition `L²(𝒯) = R_{≤2} ⊕ ℂμ` with
  `dim R_{≤2} = 23` (`pairwise_defect`);
* `inf_{f ∈ R_{≤2}} ‖μ - f‖² = ‖μ‖² = 24`, i.e. in the
  expectation-normalized metric of the manuscript
  (`⟪f,g⟫ = E[conj f · g]`, a `1/24` weight, disclosed)
  `inf ‖μ - f‖₂ = 1`; stated as an `IsLeast` fact.

The ambient `L²(𝒯)` is `EuclideanSpace ℂ Turn` with the counting
inner product; the normalization `1/24` appears explicitly in the
distance statement.
-/

open Finset

namespace NCG

/-- An oriented nonbacktracking tetrahedral turn: an ordered triple
of pairwise distinct vertices of `K₄`. -/
abbrev Turn : Type :=
  {t : Fin 4 × Fin 4 × Fin 4 //
    t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2}

/-- The omitted vertex `ℓ` of a turn. -/
def omitV (i j k : Fin 4) : Fin 4 :=
  if 0 ≠ i ∧ 0 ≠ j ∧ 0 ≠ k then 0
  else if 1 ≠ i ∧ 1 ≠ j ∧ 1 ≠ k then 1
  else if 2 ≠ i ∧ 2 ≠ j ∧ 2 ≠ k then 2
  else 3

/-- The sign of a four-term sequence of vertices: the parity of
its inversion count. -/
def signFour (i j k l : Fin 4) : ℤ :=
  (-1) ^ ((if j < i then 1 else 0) + (if k < i then 1 else 0)
    + (if l < i then 1 else 0) + (if k < j then 1 else 0)
    + (if l < j then 1 else 0) + (if l < k then 1 else 0) : ℕ)

/-- The Maslov turn sign `μ(i,j,k) = sgn(i,j,k,ℓ)`. -/
def muZ (t : Turn) : ℤ :=
  signFour t.1.1 t.1.2.1 t.1.2.2 (omitV t.1.1 t.1.2.1 t.1.2.2)

/-- The three coordinate-pair projections of a turn. -/
def pi12 (t : Turn) : Fin 4 × Fin 4 := (t.1.1, t.1.2.1)

/-- Projection onto the first and third turn coordinates. -/
def pi13 (t : Turn) : Fin 4 × Fin 4 := (t.1.1, t.1.2.2)

/-- Projection onto the second and third turn coordinates. -/
def pi23 (t : Turn) : Fin 4 × Fin 4 := (t.1.2.1, t.1.2.2)

/-- There are exactly `24` turns. -/
lemma card_turn : Fintype.card Turn = 24 := by decide

/-- `E[μ | t₁,t₂] = 0`: the fiber sums of the turn sign over the
first coordinate pair vanish. -/
lemma muZ_fiber12 (p : Fin 4 × Fin 4) :
    ∑ t ∈ univ.filter (fun t : Turn => pi12 t = p), muZ t = 0 := by
  revert p; decide

/-- `E[μ | t₁,t₃] = 0`. -/
lemma muZ_fiber13 (p : Fin 4 × Fin 4) :
    ∑ t ∈ univ.filter (fun t : Turn => pi13 t = p), muZ t = 0 := by
  revert p; decide

/-- `E[μ | t₂,t₃] = 0`. -/
lemma muZ_fiber23 (p : Fin 4 × Fin 4) :
    ∑ t ∈ univ.filter (fun t : Turn => pi23 t = p), muZ t = 0 := by
  revert p; decide

/-- The sign vector `μ` as an element of `L²(𝒯)`. -/
noncomputable def muVec : EuclideanSpace ℂ Turn :=
  WithLp.toLp 2 (fun t => (muZ t : ℂ))

/-- The composition maps realizing functions of a coordinate pair
as functions on turns. -/
noncomputable def coordMap (π : Turn → Fin 4 × Fin 4) :
    (Fin 4 × Fin 4 → ℂ) →ₗ[ℂ] EuclideanSpace ℂ Turn where
  toFun g := WithLp.toLp 2 (fun t => g (π t))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] lemma coordMap_apply (π : Turn → Fin 4 × Fin 4)
    (g : Fin 4 × Fin 4 → ℂ) (t : Turn) :
    coordMap π g t = g (π t) := rfl

/-- `R_{≤2}`: the span of all functions of at most two turn
coordinates. -/
noncomputable def pairwiseSpan : Submodule ℂ (EuclideanSpace ℂ Turn) :=
  LinearMap.range (coordMap pi12) ⊔ LinearMap.range (coordMap pi13)
    ⊔ LinearMap.range (coordMap pi23)

/-- Extract a two-term relation from a vanishing fiber sum. -/
lemma pair_rel (f : Turn → ℂ) (π : Turn → Fin 4 × Fin 4)
    (p : Fin 4 × Fin 4) (x y : Turn) (hxy : x ≠ y)
    (hfil : univ.filter (fun t : Turn => π t = p) = {x, y})
    (h : ∑ t ∈ univ.filter (fun t : Turn => π t = p), f t = 0) :
    f x + f y = 0 := by
  rw [hfil, Finset.sum_pair hxy] at h
  exact h

/-- Any function whose fiber sums over all three coordinate pairs
vanish is a multiple of the turn sign: the kernel of the pairwise
conditional expectations is exactly `ℂμ`. -/
lemma kernel_eq_sign (f : Turn → ℂ)
    (h12 : ∀ p : Fin 4 × Fin 4,
      ∑ t ∈ univ.filter (fun t : Turn => pi12 t = p), f t = 0)
    (h13 : ∀ p : Fin 4 × Fin 4,
      ∑ t ∈ univ.filter (fun t : Turn => pi13 t = p), f t = 0)
    (h23 : ∀ p : Fin 4 × Fin 4,
      ∑ t ∈ univ.filter (fun t : Turn => pi23 t = p), f t = 0) :
    ∀ t : Turn, f t = f ⟨(0, 1, 2), by decide⟩ * (muZ t : ℂ) := by
  -- the 23 two-term relations of the propagation chain
  have r1 : f ⟨(0,1,2), by decide⟩ + f ⟨(0,1,3), by decide⟩ = 0 :=
    pair_rel f pi12 (0,1) _ _ (by decide) (by decide) (h12 (0,1))
  have r2 : f ⟨(0,1,2), by decide⟩ + f ⟨(0,3,2), by decide⟩ = 0 :=
    pair_rel f pi13 (0,2) _ _ (by decide) (by decide) (h13 (0,2))
  have r3 : f ⟨(0,1,2), by decide⟩ + f ⟨(3,1,2), by decide⟩ = 0 :=
    pair_rel f pi23 (1,2) _ _ (by decide) (by decide) (h23 (1,2))
  have r4 : f ⟨(0,1,3), by decide⟩ + f ⟨(0,2,3), by decide⟩ = 0 :=
    pair_rel f pi13 (0,3) _ _ (by decide) (by decide) (h13 (0,3))
  have r5 : f ⟨(0,1,3), by decide⟩ + f ⟨(2,1,3), by decide⟩ = 0 :=
    pair_rel f pi23 (1,3) _ _ (by decide) (by decide) (h23 (1,3))
  have r6 : f ⟨(0,3,2), by decide⟩ + f ⟨(0,3,1), by decide⟩ = 0 :=
    pair_rel f pi12 (0,3) _ _ (by decide) (by decide) (h12 (0,3))
  have r7 : f ⟨(0,3,2), by decide⟩ + f ⟨(1,3,2), by decide⟩ = 0 :=
    pair_rel f pi23 (3,2) _ _ (by decide) (by decide) (h23 (3,2))
  have r8 : f ⟨(3,1,2), by decide⟩ + f ⟨(3,1,0), by decide⟩ = 0 :=
    pair_rel f pi12 (3,1) _ _ (by decide) (by decide) (h12 (3,1))
  have r9 : f ⟨(3,1,2), by decide⟩ + f ⟨(3,0,2), by decide⟩ = 0 :=
    pair_rel f pi13 (3,2) _ _ (by decide) (by decide) (h13 (3,2))
  have r10 : f ⟨(0,2,3), by decide⟩ + f ⟨(0,2,1), by decide⟩ = 0 :=
    pair_rel f pi12 (0,2) _ _ (by decide) (by decide) (h12 (0,2))
  have r11 : f ⟨(0,2,3), by decide⟩ + f ⟨(1,2,3), by decide⟩ = 0 :=
    pair_rel f pi23 (2,3) _ _ (by decide) (by decide) (h23 (2,3))
  have r12 : f ⟨(2,1,3), by decide⟩ + f ⟨(2,1,0), by decide⟩ = 0 :=
    pair_rel f pi12 (2,1) _ _ (by decide) (by decide) (h12 (2,1))
  have r13 : f ⟨(2,1,3), by decide⟩ + f ⟨(2,0,3), by decide⟩ = 0 :=
    pair_rel f pi13 (2,3) _ _ (by decide) (by decide) (h13 (2,3))
  have r14 : f ⟨(0,3,1), by decide⟩ + f ⟨(2,3,1), by decide⟩ = 0 :=
    pair_rel f pi23 (3,1) _ _ (by decide) (by decide) (h23 (3,1))
  have r15 : f ⟨(1,3,2), by decide⟩ + f ⟨(1,3,0), by decide⟩ = 0 :=
    pair_rel f pi12 (1,3) _ _ (by decide) (by decide) (h12 (1,3))
  have r16 : f ⟨(1,3,2), by decide⟩ + f ⟨(1,0,2), by decide⟩ = 0 :=
    pair_rel f pi13 (1,2) _ _ (by decide) (by decide) (h13 (1,2))
  have r17 : f ⟨(3,1,0), by decide⟩ + f ⟨(3,2,0), by decide⟩ = 0 :=
    pair_rel f pi13 (3,0) _ _ (by decide) (by decide) (h13 (3,0))
  have r18 : f ⟨(3,0,2), by decide⟩ + f ⟨(3,0,1), by decide⟩ = 0 :=
    pair_rel f pi12 (3,0) _ _ (by decide) (by decide) (h12 (3,0))
  have r19 : f ⟨(1,0,2), by decide⟩ + f ⟨(1,0,3), by decide⟩ = 0 :=
    pair_rel f pi12 (1,0) _ _ (by decide) (by decide) (h12 (1,0))
  have r20 : f ⟨(1,2,3), by decide⟩ + f ⟨(1,2,0), by decide⟩ = 0 :=
    pair_rel f pi12 (1,2) _ _ (by decide) (by decide) (h12 (1,2))
  have r21 : f ⟨(2,0,3), by decide⟩ + f ⟨(2,0,1), by decide⟩ = 0 :=
    pair_rel f pi12 (2,0) _ _ (by decide) (by decide) (h12 (2,0))
  have r22 : f ⟨(2,3,1), by decide⟩ + f ⟨(2,3,0), by decide⟩ = 0 :=
    pair_rel f pi12 (2,3) _ _ (by decide) (by decide) (h12 (2,3))
  have r23 : f ⟨(3,2,0), by decide⟩ + f ⟨(3,2,1), by decide⟩ = 0 :=
    pair_rel f pi12 (3,2) _ _ (by decide) (by decide) (h12 (3,2))
  -- the propagated values
  have v013 : f ⟨(0,1,3), by decide⟩ = -f ⟨(0,1,2), by decide⟩ := by
    linear_combination r1
  have v032 : f ⟨(0,3,2), by decide⟩ = -f ⟨(0,1,2), by decide⟩ := by
    linear_combination r2
  have v312 : f ⟨(3,1,2), by decide⟩ = -f ⟨(0,1,2), by decide⟩ := by
    linear_combination r3
  have v023 : f ⟨(0,2,3), by decide⟩ = f ⟨(0,1,2), by decide⟩ := by
    linear_combination r4 - v013
  have v213 : f ⟨(2,1,3), by decide⟩ = f ⟨(0,1,2), by decide⟩ := by
    linear_combination r5 - v013
  have v031 : f ⟨(0,3,1), by decide⟩ = f ⟨(0,1,2), by decide⟩ := by
    linear_combination r6 - v032
  have v132 : f ⟨(1,3,2), by decide⟩ = f ⟨(0,1,2), by decide⟩ := by
    linear_combination r7 - v032
  have v310 : f ⟨(3,1,0), by decide⟩ = f ⟨(0,1,2), by decide⟩ := by
    linear_combination r8 - v312
  have v302 : f ⟨(3,0,2), by decide⟩ = f ⟨(0,1,2), by decide⟩ := by
    linear_combination r9 - v312
  have v021 : f ⟨(0,2,1), by decide⟩ = -f ⟨(0,1,2), by decide⟩ := by
    linear_combination r10 - v023
  have v123 : f ⟨(1,2,3), by decide⟩ = -f ⟨(0,1,2), by decide⟩ := by
    linear_combination r11 - v023
  have v210 : f ⟨(2,1,0), by decide⟩ = -f ⟨(0,1,2), by decide⟩ := by
    linear_combination r12 - v213
  have v203 : f ⟨(2,0,3), by decide⟩ = -f ⟨(0,1,2), by decide⟩ := by
    linear_combination r13 - v213
  have v231 : f ⟨(2,3,1), by decide⟩ = -f ⟨(0,1,2), by decide⟩ := by
    linear_combination r14 - v031
  have v130 : f ⟨(1,3,0), by decide⟩ = -f ⟨(0,1,2), by decide⟩ := by
    linear_combination r15 - v132
  have v102 : f ⟨(1,0,2), by decide⟩ = -f ⟨(0,1,2), by decide⟩ := by
    linear_combination r16 - v132
  have v320 : f ⟨(3,2,0), by decide⟩ = -f ⟨(0,1,2), by decide⟩ := by
    linear_combination r17 - v310
  have v301 : f ⟨(3,0,1), by decide⟩ = -f ⟨(0,1,2), by decide⟩ := by
    linear_combination r18 - v302
  have v103 : f ⟨(1,0,3), by decide⟩ = f ⟨(0,1,2), by decide⟩ := by
    linear_combination r19 - v102
  have v120 : f ⟨(1,2,0), by decide⟩ = f ⟨(0,1,2), by decide⟩ := by
    linear_combination r20 - v123
  have v201 : f ⟨(2,0,1), by decide⟩ = f ⟨(0,1,2), by decide⟩ := by
    linear_combination r21 - v203
  have v230 : f ⟨(2,3,0), by decide⟩ = f ⟨(0,1,2), by decide⟩ := by
    linear_combination r22 - v231
  have v321 : f ⟨(3,2,1), by decide⟩ = f ⟨(0,1,2), by decide⟩ := by
    linear_combination r23 - v320
  intro t
  fin_cases t <;>
    norm_num [muZ, signFour, omitV, Fin.ext_iff, Fin.lt_def] <;>
    first
      | rfl
      | exact v013 | exact v021 | exact v023 | exact v031 | exact v032
      | exact v102 | exact v103 | exact v120 | exact v123 | exact v130
      | exact v132 | exact v201 | exact v203 | exact v210 | exact v213
      | exact v230 | exact v231 | exact v301 | exact v302 | exact v310
      | exact v312 | exact v320 | exact v321

@[simp] lemma muVec_apply (t : Turn) : muVec t = (muZ t : ℂ) := rfl

open scoped InnerProductSpace in
/-- Functions of a coordinate pair are orthogonal to the sign
vector as soon as its fiber sums over that pair vanish. -/
lemma coord_inner_muVec (π : Turn → Fin 4 × Fin 4)
    (hπ : ∀ p, ∑ t ∈ univ.filter (fun t : Turn => π t = p), muZ t = 0)
    (g : Fin 4 × Fin 4 → ℂ) :
    ⟪coordMap π g, muVec⟫_ℂ = 0 := by
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, coordMap_apply, muVec_apply]
  rw [← Finset.sum_fiberwise_of_maps_to
    (fun t _ => Finset.mem_univ (π t))
    (fun t => (muZ t : ℂ) * (starRingEnd ℂ) (g (π t)))]
  refine Finset.sum_eq_zero fun p _ => ?_
  have hcongr : ∀ t ∈ univ.filter (fun t : Turn => π t = p),
      (muZ t : ℂ) * (starRingEnd ℂ) (g (π t))
        = (muZ t : ℂ) * (starRingEnd ℂ) (g p) := by
    intro t ht
    rw [(Finset.mem_filter.mp ht).2]
  rw [Finset.sum_congr rfl hcongr, ← Finset.sum_mul, ← Int.cast_sum,
    hπ p, Int.cast_zero, zero_mul]

/-- The sign vector is orthogonal to `R_{≤2}`. -/
lemma muVec_mem_orthogonal : muVec ∈ pairwiseSpanᗮ := by
  rw [Submodule.mem_orthogonal]
  intro u hu
  rw [pairwiseSpan] at hu
  obtain ⟨a, ha, c, hc, rfl⟩ := Submodule.mem_sup.mp hu
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp ha
  obtain ⟨gx, rfl⟩ := hx
  obtain ⟨gy, rfl⟩ := hy
  obtain ⟨gc, rfl⟩ := hc
  rw [inner_add_left, inner_add_left,
    coord_inner_muVec pi12 muZ_fiber12,
    coord_inner_muVec pi13 muZ_fiber13,
    coord_inner_muVec pi23 muZ_fiber23]
  ring

open scoped InnerProductSpace in
/-- Everything orthogonal to `R_{≤2}` is a multiple of the sign
vector. -/
lemma orthogonal_le_span :
    pairwiseSpanᗮ ≤ Submodule.span ℂ {muVec} := by
  intro f hf
  have hker : ∀ (π : Turn → Fin 4 × Fin 4),
      LinearMap.range (coordMap π) ≤ pairwiseSpan →
      ∀ p, ∑ t ∈ univ.filter (fun t : Turn => π t = p), f t = 0 := by
    intro π hle p
    have hmem : coordMap π (Pi.single p 1) ∈ pairwiseSpan :=
      hle ⟨Pi.single p 1, rfl⟩
    have h0 := (Submodule.mem_orthogonal _ _).mp hf _ hmem
    rw [PiLp.inner_apply] at h0
    simp only [RCLike.inner_apply, coordMap_apply, Pi.single_apply,
      apply_ite (starRingEnd ℂ), map_one, map_zero, mul_ite, mul_one,
      mul_zero] at h0
    rw [Finset.sum_filter]
    exact h0
  have hval := kernel_eq_sign f
    (hker pi12 (le_sup_of_le_left le_sup_left))
    (hker pi13 (le_sup_of_le_left le_sup_right))
    (hker pi23 le_sup_right)
  refine Submodule.mem_span_singleton.mpr
    ⟨f ⟨(0, 1, 2), by decide⟩, ?_⟩
  ext t
  rw [PiLp.smul_apply, muVec_apply, smul_eq_mul, ← hval t]

/-- `R_{≤2}ᗮ = ℂμ`. -/
theorem orthogonal_pairwiseSpan :
    pairwiseSpanᗮ = Submodule.span ℂ {muVec} :=
  le_antisymm orthogonal_le_span
    ((Submodule.span_singleton_le_iff_mem _ _).mpr muVec_mem_orthogonal)

/-- The sign vector is nonzero. -/
lemma muVec_ne_zero : muVec ≠ 0 := by
  intro h
  have h1 := congrArg
    (fun x : EuclideanSpace ℂ Turn => x ⟨(0, 1, 2), by decide⟩) h
  simp only [muVec_apply, PiLp.zero_apply] at h1
  rw [show muZ ⟨(0, 1, 2), by decide⟩ = 1 from by decide] at h1
  norm_num at h1

open scoped InnerProductSpace in
/-- `‖μ‖² = 24`. -/
lemma norm_muVec_sq : ‖muVec‖ ^ 2 = 24 := by
  have h : ⟪muVec, muVec⟫_ℂ = 24 := by
    rw [PiLp.inner_apply]
    simp only [RCLike.inner_apply, muVec_apply, map_intCast]
    simp only [← Int.cast_mul, ← Int.cast_sum]
    rw [show ∑ t : Turn, muZ t * muZ t = 24 from by decide]
    norm_num
  rw [inner_self_eq_norm_sq_to_K] at h
  have h2 : ((‖muVec‖ ^ 2 : ℝ) : ℂ) = ((24 : ℝ) : ℂ) := by
    rw [← RCLike.ofReal_eq_complex_ofReal]
    push_cast [← h]
    norm_num
  exact_mod_cast h2

/-- `thm:v5-pairwise-defect`, boxed decomposition:
`L²(𝒯) = R_{≤2} ⊕ ℂμ` with `dim R_{≤2} = 23` on the `24` turns. -/
theorem pairwise_defect :
    Fintype.card Turn = 24
    ∧ Module.finrank ℂ pairwiseSpan = 23
    ∧ pairwiseSpanᗮ = Submodule.span ℂ {muVec}
    ∧ IsCompl pairwiseSpan (Submodule.span ℂ {muVec}) := by
  have hdim : Module.finrank ℂ (EuclideanSpace ℂ Turn) = 24 := by
    rw [finrank_euclideanSpace, card_turn]
  have hspan : Module.finrank ℂ
      (Submodule.span ℂ ({muVec} : Set (EuclideanSpace ℂ Turn))) = 1 :=
    finrank_span_singleton muVec_ne_zero
  have hsum := Submodule.finrank_add_finrank_orthogonal
    (K := pairwiseSpan)
  rw [orthogonal_pairwiseSpan, hspan, hdim] at hsum
  refine ⟨card_turn, by omega, orthogonal_pairwiseSpan, ?_⟩
  rw [← orthogonal_pairwiseSpan]
  exact pairwiseSpan.isCompl_orthogonal

open scoped InnerProductSpace in
/-- The expectation-normalized defect distance:
`inf_{f ∈ R_{≤2}} E‖μ - f‖² = 1`, attained at `f = 0`. -/
theorem defect_distance :
    IsLeast {r : ℝ | ∃ f ∈ pairwiseSpan,
      r = (1 / 24) * ‖muVec - f‖ ^ 2} 1 := by
  constructor
  · exact ⟨0, pairwiseSpan.zero_mem, by
      rw [sub_zero, norm_muVec_sq]; norm_num⟩
  · rintro r ⟨f, hf, rfl⟩
    have horth : ⟪muVec, f⟫_ℂ = 0 := by
      have h1 := (Submodule.mem_orthogonal _ _).mp muVec_mem_orthogonal
        f hf
      rw [← inner_conj_symm, h1, map_zero]
    have hexp : ‖muVec - f‖ ^ 2
        = ‖muVec‖ ^ 2 - 2 * RCLike.re ⟪muVec, f⟫_ℂ + ‖f‖ ^ 2 :=
      norm_sub_sq muVec f
    rw [hexp, horth, norm_muVec_sq]
    have h2 : (0 : ℝ) ≤ ‖f‖ ^ 2 := by positivity
    simp only [map_zero]
    nlinarith

end NCG
