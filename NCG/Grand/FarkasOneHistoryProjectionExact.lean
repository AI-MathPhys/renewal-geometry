/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Farkas' alternative and the one-history projection

Exact encoding of `thm:GT-one-history-projection` and the Bell–Farkas part of
`thm:arithmetic-common-history-projection`.

## Finitely generated cones are closed

`conicHull v` is the set of nonnegative combinations of a finite family `v : ι → E`.
`exists_linearIndependent_support` is the conic Carathéodory reduction: every
nonnegative combination can be rewritten with a linearly independent support.
Hence the cone is a finite union of images of closed orthants under injective
linear maps (`isClosed_conicHull`), so it is a proper cone and Mathlib's
hyperplane separation applies.

## Main statements

* `farkas_alternative`: for a query synthesis `M : Matrix R C ℝ` and reported values
  `d`, exactly one of (i) `∃ λ ≥ 0, M λ = d` (a positive joint cylinder) and
  (ii) `∃ y, Mᵀ y ≥ 0 ∧ ⟨y, d⟩ < 0` (an explicit no-common-history dual writer) holds;
* `pushforward_expectation`: branch writers that are pullbacks of one common writer
  on the support of the common cylinder give the same expectation;
* `parity_laws_counterexample`: the uniform even- and odd-parity laws on three binary
  coordinates have identical one- and two-coordinate marginals but opposite triple
  parity expectations (pairwise marginals do not identify a mixed writer).
-/

open Finset Matrix
open scoped RealInnerProductSpace

namespace NCG
namespace FarkasOneHistory

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-! ### Conic hulls of finite families -/

section cone

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The conic hull (nonnegative combinations) of a finite family. -/
def conicHull (v : ι → E) : Set E :=
  {x | ∃ c : ι → ℝ, (∀ i, 0 ≤ c i) ∧ ∑ i, c i • v i = x}

/-- The support of a coefficient vector. -/
noncomputable def coeffSupport (c : ι → ℝ) : Finset ι := univ.filter fun i => c i ≠ 0

theorem sum_eq_sum_support (v : ι → E) (c : ι → ℝ) :
    ∑ i, c i • v i = ∑ i ∈ coeffSupport c, c i • v i := by
  unfold coeffSupport
  rw [sum_filter]
  refine sum_congr rfl fun i _ => ?_
  split_ifs with h
  · rfl
  · push Not at h
    simp [h]

/-- **Conic Carathéodory**: every nonnegative combination has a representation whose
support is linearly independent. -/
theorem exists_linearIndependent_support (v : ι → E) (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i) :
    ∃ c' : ι → ℝ, (∀ i, 0 ≤ c' i) ∧ ∑ i, c' i • v i = ∑ i, c i • v i ∧
      LinearIndependent ℝ (fun i : coeffSupport c' => v i) := by
  -- strong induction on the size of the support
  suffices H : ∀ n, ∀ c : ι → ℝ, (coeffSupport c).card = n → (∀ i, 0 ≤ c i) →
      ∃ c' : ι → ℝ, (∀ i, 0 ≤ c' i) ∧ ∑ i, c' i • v i = ∑ i, c i • v i ∧
        LinearIndependent ℝ (fun i : coeffSupport c' => v i) from H _ c rfl hc
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro c hcard hc
  by_cases hli : LinearIndependent ℝ (fun i : coeffSupport c => v i)
  · exact ⟨c, hc, rfl, hli⟩
  -- a nontrivial relation on the support
  rw [Fintype.linearIndependent_iff] at hli
  push Not at hli
  obtain ⟨g, hg0, j₀, hj₀⟩ := hli
  -- extend the relation to `ι`, with a positive coefficient somewhere
  let g' : ι → ℝ := fun i => if h : i ∈ coeffSupport c then g ⟨i, h⟩ else 0
  have hg'supp : ∀ i, i ∉ coeffSupport c → g' i = 0 := fun i hi => by simp [g', hi]
  have hg'sum : ∑ i, g' i • v i = 0 := by
    rw [← sum_subset (subset_univ (coeffSupport c)) (fun i _ hi => by simp [hg'supp i hi]),
      ← sum_coe_sort (coeffSupport c)]
    convert hg0 using 2 with i
    simp [g', i.2]
  have hg'ne : ∃ i, g' i ≠ 0 := ⟨j₀, by simpa [g', j₀.2] using hj₀⟩
  -- choose the sign so that some coefficient is positive
  obtain ⟨e, he_sum, he_supp, i₁, hi₁⟩ : ∃ e : ι → ℝ, ∑ i, e i • v i = 0 ∧
      (∀ i, i ∉ coeffSupport c → e i = 0) ∧ ∃ i, 0 < e i := by
    obtain ⟨i, hi⟩ := hg'ne
    rcases lt_or_gt_of_ne hi with hneg | hpos
    · refine ⟨-g', ?_, fun i hi => by simp [hg'supp i hi], i, by simpa using hneg⟩
      simp [neg_smul, sum_neg_distrib, hg'sum]
    · exact ⟨g', hg'sum, hg'supp, i, hpos⟩
  -- the positive part of `e` meets the support, where `c > 0`
  have hpos_set : (univ.filter fun i => 0 < e i).Nonempty := ⟨i₁, by simp [hi₁]⟩
  obtain ⟨i₀, hi₀mem, hi₀min⟩ := exists_min_image (univ.filter fun i => 0 < e i)
    (fun i => c i / e i) hpos_set
  have hi₀pos : 0 < e i₀ := by simpa using hi₀mem
  set t := c i₀ / e i₀ with ht
  have hi₀supp : i₀ ∈ coeffSupport c := by
    by_contra h
    exact hi₀pos.ne' (he_supp i₀ h)
  have hc₀ne : c i₀ ≠ 0 := by simpa [coeffSupport] using hi₀supp
  have hc₀ : 0 < c i₀ := lt_of_le_of_ne (hc i₀) hc₀ne.symm
  have ht_pos : 0 < t := div_pos hc₀ hi₀pos
  let c' : ι → ℝ := fun i => c i - t * e i
  have hc'nonneg : ∀ i, 0 ≤ c' i := by
    intro i
    simp only [c']
    by_cases hei : 0 < e i
    · have := hi₀min i (by simpa using hei)
      have : t * e i ≤ c i := by
        rw [le_div_iff₀ hei] at this
        exact this
      linarith
    · push Not at hei
      nlinarith [hc i, ht_pos]
  have hc'sum : ∑ i, c' i • v i = ∑ i, c i • v i := by
    simp only [c', sub_smul, sum_sub_distrib, mul_smul, ← smul_sum, he_sum, smul_zero, sub_zero]
  have hc'i₀ : c' i₀ = 0 := by
    simp only [c']
    rw [ht, div_mul_cancel₀ _ hi₀pos.ne', sub_self]
  have hc'subset : coeffSupport c' ⊆ coeffSupport c := by
    intro i hi
    by_contra h
    have h1 := he_supp i h
    have h2 : c i = 0 := by simpa [coeffSupport] using h
    have : c' i = 0 := by simp [c', h1, h2]
    have hne : c' i ≠ 0 := by simpa [coeffSupport] using hi
    exact hne this
  have hcard' : (coeffSupport c').card < n := by
    rw [← hcard]
    refine card_lt_card ⟨hc'subset, fun hsub => ?_⟩
    have := hsub hi₀supp
    simp [coeffSupport, hc'i₀] at this
  obtain ⟨c'', h1, h2, h3⟩ := ih _ hcard' c' rfl hc'nonneg
  exact ⟨c'', h1, h2.trans hc'sum, h3⟩

/-- The image of the closed orthant under the linear combination map of a linearly
independent finite family is closed. -/
theorem isClosed_orthant_image (s : Finset ι) (v : ι → E)
    (hs : LinearIndependent ℝ (fun i : s => v i)) :
    IsClosed ((Fintype.linearCombination ℝ (fun i : s => v i)) ''
      {c : s → ℝ | ∀ i, 0 ≤ c i}) := by
  have hinj : LinearMap.ker (Fintype.linearCombination ℝ (fun i : s => v i)) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro c hc
    rw [Fintype.linearIndependent_iff] at hs
    funext i
    exact hs c (by simpa [Fintype.linearCombination_apply] using hc) i
  have hemb := LinearMap.isClosedEmbedding_of_injective hinj
  refine hemb.isClosedMap _ ?_
  have : {c : s → ℝ | ∀ i, 0 ≤ c i} = ⋂ i, {c : s → ℝ | 0 ≤ c i} := by
    ext c; simp
  rw [this]
  exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)

/-- **Finitely generated cones are closed.** -/
theorem isClosed_conicHull (v : ι → E) : IsClosed (conicHull v) := by
  have hunion : conicHull v = ⋃ s ∈ {s : Finset ι | LinearIndependent ℝ (fun i : s => v i.1)},
      (Fintype.linearCombination ℝ (fun i : s => v i.1)) '' {c : s → ℝ | ∀ i, 0 ≤ c i} := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_image, Set.mem_setOf_eq, exists_prop]
    constructor
    · rintro ⟨c, hc, rfl⟩
      obtain ⟨c', hc', hsum, hli⟩ := exists_linearIndependent_support v c hc
      refine ⟨coeffSupport c', hli, fun i => c' i, fun i => hc' i, ?_⟩
      rw [Fintype.linearCombination_apply, sum_coe_sort (coeffSupport c') (fun i => c' i • v i),
        ← sum_eq_sum_support, hsum]
    · rintro ⟨s, -, c, hc, rfl⟩
      refine ⟨fun i => if h : i ∈ s then c ⟨i, h⟩ else 0, fun i => ?_, ?_⟩
      · dsimp only
        split_ifs with h
        · exact hc ⟨i, h⟩
        · exact le_rfl
      · dsimp only
        rw [Fintype.linearCombination_apply,
          ← sum_subset (f := fun i => (if h : i ∈ s then c ⟨i, h⟩ else 0) • v i) (subset_univ s)
            (fun i _ hi => by simp [hi]), ← sum_coe_sort s]
        refine sum_congr rfl fun i _ => ?_
        simp [i.2]
  rw [hunion]
  exact (Set.toFinite _).isClosed_biUnion fun s hs => isClosed_orthant_image s v hs

/-- The conic hull as a proper (closed, convex, pointed) cone. -/
noncomputable def conicCone (v : ι → E) : ProperCone ℝ E where
  carrier := conicHull v
  add_mem' := by
    rintro x y ⟨c, hc, rfl⟩ ⟨c', hc', rfl⟩
    exact ⟨fun i => c i + c' i, fun i => add_nonneg (hc i) (hc' i), by
      simp [add_smul, sum_add_distrib]⟩
  zero_mem' := ⟨fun _ => 0, fun _ => le_rfl, by simp⟩
  smul_mem' := by
    rintro ⟨r, hr⟩ x ⟨c, hc, rfl⟩
    refine ⟨fun i => r * c i, fun i => mul_nonneg hr (hc i), ?_⟩
    simp only [mul_smul, ← smul_sum]
    rfl
  isClosed' := isClosed_conicHull v

theorem mem_conicCone (v : ι → E) (x : E) : x ∈ conicCone v ↔ x ∈ conicHull v := Iff.rfl

theorem generator_mem_conicCone (v : ι → E) (j : ι) : v j ∈ conicCone v := by
  refine ⟨fun i => if i = j then 1 else 0, fun i => by dsimp only; split_ifs <;> norm_num, ?_⟩
  simp [ite_smul]

end cone

/-! ### Farkas' alternative for a finite query synthesis -/

section farkas

variable {R C : Type*} [Fintype R] [Fintype C] [DecidableEq R] [DecidableEq C]

/-- The columns of `M` as vectors of the Euclidean space on the rows. -/
noncomputable def column (M : Matrix R C ℝ) (j : C) : EuclideanSpace ℝ R :=
  WithLp.toLp 2 (fun i => M i j)

theorem mulVec_eq_sum_column (M : Matrix R C ℝ) (c : C → ℝ) :
    WithLp.toLp 2 (M *ᵥ c) = ∑ j, c j • column M j := by
  ext i
  simp [column, Matrix.mulVec, dotProduct, mul_comm]

/-- **Farkas' alternative** (exactly one branch): either a positive joint cylinder
`λ ≥ 0` with `M λ = d` exists, or an explicit dual writer `y` with `Mᵀ y ≥ 0` and
`⟨y, d⟩ < 0` exists. -/
theorem farkas_alternative (M : Matrix R C ℝ) (d : R → ℝ) :
    ((∃ l : C → ℝ, (∀ j, 0 ≤ l j) ∧ M *ᵥ l = d) ∨
      (∃ y : R → ℝ, (∀ j, 0 ≤ (Mᵀ *ᵥ y) j) ∧ y ⬝ᵥ d < 0)) ∧
    ¬ ((∃ l : C → ℝ, (∀ j, 0 ≤ l j) ∧ M *ᵥ l = d) ∧
      (∃ y : R → ℝ, (∀ j, 0 ≤ (Mᵀ *ᵥ y) j) ∧ y ⬝ᵥ d < 0)) := by
  constructor
  · by_cases hd : WithLp.toLp 2 d ∈ conicCone (column M)
    · left
      obtain ⟨c, hc, hsum⟩ := hd
      refine ⟨c, hc, ?_⟩
      have := hsum
      rw [← mulVec_eq_sum_column] at this
      exact congrArg (WithLp.ofLp) this
    · right
      obtain ⟨y, hy, hyd⟩ := (conicCone (column M)).hyperplane_separation' hd
      refine ⟨WithLp.ofLp y, fun j => ?_, ?_⟩
      · have := hy _ (generator_mem_conicCone (column M) j)
        rw [EuclideanSpace.inner_eq_star_dotProduct] at this
        simpa [column, Matrix.mulVec, dotProduct, mul_comm] using this
      · rw [EuclideanSpace.inner_eq_star_dotProduct] at hyd
        simpa [dotProduct, mul_comm] using hyd
  · rintro ⟨⟨l, hl, hMl⟩, ⟨y, hy, hyd⟩⟩
    have : y ⬝ᵥ d = (Mᵀ *ᵥ y) ⬝ᵥ l := by
      rw [← hMl, dotProduct_mulVec, Matrix.mulVec_transpose]
    have hnonneg : 0 ≤ (Mᵀ *ᵥ y) ⬝ᵥ l :=
      Finset.sum_nonneg fun j _ => mul_nonneg (hy j) (hl j)
    linarith

end farkas

/-! ### The pushforward identity and the parity counterexample -/

section pushforward

variable {Ω B : Type*} [Fintype Ω] [Fintype B] [DecidableEq B]

/-- **Pushforward identity**: if the branch writer `w` satisfies `w ∘ π = w_H` on the
support of the joint cylinder `Λ`, then the branch expectation under the pushforward
`π_# Λ` equals the common-history expectation of `w_H`. -/
theorem pushforward_expectation (Λ : Ω → ℝ) (π : Ω → B) (w : B → ℝ) (wH : Ω → ℝ)
    (h : ∀ ω, Λ ω ≠ 0 → w (π ω) = wH ω) :
    ∑ b, (∑ ω ∈ univ.filter (fun ω => π ω = b), Λ ω) * w b = ∑ ω, Λ ω * wH ω := by
  calc ∑ b, (∑ ω ∈ univ.filter (fun ω => π ω = b), Λ ω) * w b
      = ∑ b, ∑ ω ∈ univ.filter (fun ω => π ω = b), Λ ω * w (π ω) := by
        refine sum_congr rfl fun b _ => ?_
        rw [sum_mul]
        refine sum_congr rfl fun ω hω => ?_
        rw [(mem_filter.mp hω).2]
    _ = ∑ ω, Λ ω * w (π ω) := sum_fiberwise univ π fun ω => Λ ω * w (π ω)
    _ = ∑ ω, Λ ω * wH ω := by
        refine sum_congr rfl fun ω _ => ?_
        by_cases hΛ : Λ ω = 0
        · simp [hΛ]
        · rw [h ω hΛ]

/-- Two branches with writers that are pullbacks of one common writer give the same
expectation. -/
theorem branches_agree (Λ : Ω → ℝ) (π₁ π₂ : Ω → B) (w₁ w₂ : B → ℝ) (wH : Ω → ℝ)
    (h₁ : ∀ ω, Λ ω ≠ 0 → w₁ (π₁ ω) = wH ω) (h₂ : ∀ ω, Λ ω ≠ 0 → w₂ (π₂ ω) = wH ω) :
    ∑ b, (∑ ω ∈ univ.filter (fun ω => π₁ ω = b), Λ ω) * w₁ b
      = ∑ b, (∑ ω ∈ univ.filter (fun ω => π₂ ω = b), Λ ω) * w₂ b := by
  rw [pushforward_expectation Λ π₁ w₁ wH h₁, pushforward_expectation Λ π₂ w₂ wH h₂]

end pushforward

section parity

/-- The triple parity `(-1)^{ω₁ + ω₂ + ω₃}` of three binary coordinates. -/
def parity (ω : Bool × Bool × Bool) : ℚ :=
  (if ω.1 then -1 else 1) * (if ω.2.1 then -1 else 1) * (if ω.2.2 then -1 else 1)

/-- The uniform even-parity law. -/
def evenLaw (ω : Bool × Bool × Bool) : ℚ := if parity ω = 1 then 1 / 4 else 0

/-- The uniform odd-parity law. -/
def oddLaw (ω : Bool × Bool × Bool) : ℚ := if parity ω = -1 then 1 / 4 else 0

/-- **Pairwise marginals do not identify the writer**: the even and odd parity laws
have identical two-coordinate (hence one-coordinate) marginals. -/
theorem parity_laws_pairwise_marginals (a b : Bool) :
    (∑ ω, if ω.1 = a ∧ ω.2.1 = b then evenLaw ω else 0)
        = (∑ ω, if ω.1 = a ∧ ω.2.1 = b then oddLaw ω else 0) ∧
      (∑ ω, if ω.1 = a ∧ ω.2.2 = b then evenLaw ω else 0)
        = (∑ ω, if ω.1 = a ∧ ω.2.2 = b then oddLaw ω else 0) ∧
      (∑ ω, if ω.2.1 = a ∧ ω.2.2 = b then evenLaw ω else 0)
        = (∑ ω, if ω.2.1 = a ∧ ω.2.2 = b then oddLaw ω else 0) := by
  cases a <;> cases b <;>
    simp [Fintype.sum_prod_type, evenLaw, oddLaw, parity] <;> norm_num

/-- ... but opposite triple-parity expectations. -/
theorem parity_laws_triple_expectation :
    ∑ ω, evenLaw ω * parity ω = 1 ∧ ∑ ω, oddLaw ω * parity ω = -1 := by
  simp [Fintype.sum_prod_type, evenLaw, oddLaw, parity]
  norm_num

end parity

end FarkasOneHistory
end NCG
