/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.DeSitterCauchySlices
import RenewalGeometry.Gravity.RelationalFlatVacuum

/-!
# Compact Cauchy slices of de Sitter on `ℝ × T³_{A₃}` (`thm:supp-desitter-einstein`)

`Gravity/DeSitterCauchySlices.lean` proves the Cauchy property of the slices `t = const` for
the cubic torus `(ℝ/ℤ)³`.  The manuscript's spatial quotient is the `A₃` torus
`T³_{A₃} = W₀/Λ_{A₃}`, `W₀ = {x ∈ ℝ⁴ : Σ xᵢ = 0}`, `Λ_{A₃} = W₀ ∩ ℤ⁴`
(`eq:supp-a3-lattice`), which is not isometric to the cubic torus.  This file

* generalises the Cauchy argument to an *arbitrary* continuous covering projection
  `π : ℝ³ → Q` (`IsInextendibleVia`, `time_surjective_of_inextendibleVia`,
  `slice_cauchy_via`): only convergence in the covering `ℝ × ℝ³` and continuity of `π`
  are used (`tendsto_lift_of_time_bdd`);
* constructs `W₀` (`W0`), `Λ_{A₃}` (`lambdaA3`) and `T³_{A₃} = W₀ ⧸ Λ_{A₃}` (`TorusA3`),
  with orthonormal coordinates `x ∈ ℝ³ ↦ a3Embed x ∈ W₀` (`a3Embed_normSq`: the coordinates
  are Euclidean-orthonormal on `W₀`; `a3Embed_surjective`), and the covering projection
  `a3TorusProj : ℝ³ → T³_{A₃}`; the kernel of the projection is the `D₃` lattice
  spanned by the twelve roots (`a3Embed_mem_lambdaA3_iff`, `a3Embed_a3Roots_mem`);
* proves `T³_{A₃}` compact (`compactSpace_torusA3`);
* **`desitter_cartan_einstein_cauchy_A3`**: `thm:supp-desitter-einstein` in full for
  `ℝ × T³_{A₃}`, the Cartan/Einstein part from `DeSitterCartan.desitter_cartan_einstein`.

Scoped rendering (as in the cubic file, disclosed): causal curves are everywhere
differentiable curves parametrized by `ℝ`, presented by a lift to `ℝ × ℝ³` (orthonormal
coordinates of `W₀`); inextendible means that the projected curve has no endpoint in
`ℝ × T³_{A₃}` at either end; global hyperbolicity is certified by the Cauchy time function.
-/

open Filter Topology Set
open scoped BigOperators

namespace RenewalGeometry.DeSitterCauchyA3

open RelationalDeSitterBranch DeSitterCauchy

/-! ### Convergence in the covering on a bounded time range -/

section covering

variable {H : ℝ} {τ τ' : ℝ → ℝ} {x x' : ℝ → Fin 3 → ℝ}

/-- Future-type end in the covering: if `τ' > 0` and `τ` is bounded above, then `τ` and the
lift `x` converge as `s → +∞`. -/
theorem tendsto_lift_atTop_of_pos_of_bddAbove (hc : IsCausalCurve H τ τ' x x')
    (hpos : ∀ s, 0 < τ' s) {B : ℝ} (hB : ∀ s, τ s ≤ B) :
    ∃ T L, Tendsto τ atTop (𝓝 T) ∧ Tendsto x atTop (𝓝 L) := by
  have hmono : Monotone τ :=
    (strictMono_of_deriv_pos fun s => by
      rw [(hc.hasDerivAt_time s).deriv]; exact hpos s).monotone
  have hτt := tendsto_atTop_ciSup hmono ⟨B, by rintro _ ⟨s, rfl⟩; exact hB s⟩
  set K : ℝ := |τ 0| + |B|
  have hK : ∀ s, 0 ≤ s → |τ s| ≤ K := by
    intro s hs
    have h1 : τ 0 ≤ τ s := hmono hs
    have h2 := hB s
    rw [abs_le]
    constructor <;> cases abs_cases (τ 0) <;> cases abs_cases B <;> linarith
  have hspace : ∀ i : Fin 3, ∃ L, Tendsto (fun s => x s i) atTop (𝓝 L) := by
    intro i
    refine tendsto_of_dominated_by_monotone (C := Real.exp (|H| * K)) (B := B) (τ := τ)
      (τ' := τ') (y' := fun s => x' s i) (Real.exp_pos _).le hc.hasDerivAt_time
      (fun s => hc.hasDerivAt_space s i) (fun s hs => ?_) hB
    have h1 := hc.abs_spatial_deriv_le s i
    have h2 : Real.exp (-H * τ s) ≤ Real.exp (|H| * K) := by
      apply Real.exp_le_exp.mpr
      have := hK s hs
      calc -H * τ s ≤ |-H * τ s| := le_abs_self _
        _ = |H| * |τ s| := by rw [abs_mul, abs_neg]
        _ ≤ |H| * K := mul_le_mul_of_nonneg_left this (abs_nonneg _)
    rw [abs_of_pos (hpos s)] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right h2 (hpos s).le)
  choose L hL using hspace
  exact ⟨_, L, hτt, tendsto_pi_nhds.2 hL⟩

/-- Every causal curve whose time is bounded at one end of the parameter line converges in
the covering `ℝ × ℝ³` at that end (four cases: direction of time × end). -/
theorem tendsto_lift_of_time_bdd (hc : IsCausalCurve H τ τ' x x') :
    ((∃ B, ∀ s, τ s ≤ B) → (∀ s, 0 < τ' s) →
      ∃ T L, Tendsto τ atTop (𝓝 T) ∧ Tendsto x atTop (𝓝 L)) ∧
    ((∃ B, ∀ s, B ≤ τ s) → (∀ s, 0 < τ' s) →
      ∃ T L, Tendsto τ atBot (𝓝 T) ∧ Tendsto x atBot (𝓝 L)) ∧
    ((∃ B, ∀ s, B ≤ τ s) → (∀ s, τ' s < 0) →
      ∃ T L, Tendsto τ atTop (𝓝 T) ∧ Tendsto x atTop (𝓝 L)) ∧
    ((∃ B, ∀ s, τ s ≤ B) → (∀ s, τ' s < 0) →
      ∃ T L, Tendsto τ atBot (𝓝 T) ∧ Tendsto x atBot (𝓝 L)) := by
  refine ⟨fun ⟨B, hB⟩ hpos => tendsto_lift_atTop_of_pos_of_bddAbove hc hpos hB, ?_, ?_, ?_⟩
  · rintro ⟨B, hB⟩ hpos
    obtain ⟨T, L, hT, hL⟩ := tendsto_lift_atTop_of_pos_of_bddAbove hc.reflect
      (fun s => hpos (-s)) (B := -B) (fun s => by have := hB (-s); linarith)
    refine ⟨-T, L, ?_, ?_⟩
    · have h2 := (hT.comp tendsto_neg_atBot_atTop).neg
      exact h2.congr fun s => by simp [Function.comp]
    · have h2 := hL.comp tendsto_neg_atBot_atTop
      exact h2.congr fun s => by simp [Function.comp]
  · rintro ⟨B, hB⟩ hneg'
    obtain ⟨T, L, hT, hL⟩ := tendsto_lift_atTop_of_pos_of_bddAbove hc.timeReflect
      (fun s => neg_pos.mpr (hneg' s)) (B := -B) (fun s => by have := hB s; linarith)
    exact ⟨-T, L, by simpa using hT.neg, hL⟩
  · rintro ⟨B, hB⟩ hneg'
    obtain ⟨T, L, hT, hL⟩ := tendsto_lift_atTop_of_pos_of_bddAbove hc.timeReflect.reflect
      (fun s => by simpa using hneg' (-s)) (B := B) (fun s => by simpa using hB (-s))
    refine ⟨T, L, ?_, ?_⟩
    · have h2 := hT.comp tendsto_neg_atBot_atTop
      exact h2.congr fun s => by simp [Function.comp]
    · have h2 := hL.comp tendsto_neg_atBot_atTop
      exact h2.congr fun s => by simp [Function.comp]

end covering

/-! ### Inextendibility through an arbitrary covering projection -/

/-- Inextendibility in `ℝ × Q` for a spatial projection `π : ℝ³ → Q`: the projected curve
`s ↦ (τ(s), π(x(s)))` has no endpoint at either end of its parameter line. -/
def IsInextendibleVia {Q : Type*} [TopologicalSpace Q] (π : (Fin 3 → ℝ) → Q)
    (τ : ℝ → ℝ) (x : ℝ → Fin 3 → ℝ) : Prop :=
  (¬ ∃ p : ℝ × Q, Tendsto (fun s => (τ s, π (x s))) atTop (𝓝 p)) ∧
    (¬ ∃ p : ℝ × Q, Tendsto (fun s => (τ s, π (x s))) atBot (𝓝 p))

/-- Sanity check: for the cubic projection this is the inextendibility of the cubic file. -/
theorem isInextendibleVia_torusProj_iff (τ : ℝ → ℝ) (x : ℝ → Fin 3 → ℝ) :
    IsInextendibleVia torusProj τ x ↔ IsInextendible τ x := Iff.rfl

section via

variable {Q : Type*} [TopologicalSpace Q] {π : (Fin 3 → ℝ) → Q}
variable {H : ℝ} {τ τ' : ℝ → ℝ} {x x' : ℝ → Fin 3 → ℝ}

/-- **The time function of an inextendible causal curve is onto `ℝ`**, for any continuous
spatial projection. -/
theorem time_surjective_of_inextendibleVia (hπ : Continuous π)
    (hc : IsCausalCurve H τ τ' x x') (hinext : IsInextendibleVia π τ x) :
    Function.Surjective τ := by
  obtain ⟨e1, e2, e3, e4⟩ := tendsto_lift_of_time_bdd hc
  have hproj : ∀ {l : Filter ℝ} {T : ℝ} {L : Fin 3 → ℝ}, Tendsto τ l (𝓝 T) →
      Tendsto x l (𝓝 L) → ∃ p : ℝ × Q, Tendsto (fun s => (τ s, π (x s))) l (𝓝 p) :=
    fun hT hL => ⟨_, hT.prodMk_nhds ((hπ.tendsto _).comp hL)⟩
  have hcont : Continuous τ :=
    continuous_iff_continuousAt.2 fun s => (hc.hasDerivAt_time s).continuousAt
  have hup : ∀ c, ∃ s, c ≤ τ s := by
    intro c
    by_contra h
    push Not at h
    rcases hc.time_deriv_pos_or_neg with hp | hn
    · obtain ⟨T, L, hT, hL⟩ := e1 ⟨c, fun s => (h s).le⟩ hp
      exact hinext.1 (hproj hT hL)
    · obtain ⟨T, L, hT, hL⟩ := e4 ⟨c, fun s => (h s).le⟩ hn
      exact hinext.2 (hproj hT hL)
  have hdown : ∀ c, ∃ s, τ s ≤ c := by
    intro c
    by_contra h
    push Not at h
    rcases hc.time_deriv_pos_or_neg with hp | hn
    · obtain ⟨T, L, hT, hL⟩ := e2 ⟨c, fun s => (h s).le⟩ hp
      exact hinext.2 (hproj hT hL)
    · obtain ⟨T, L, hT, hL⟩ := e3 ⟨c, fun s => (h s).le⟩ hn
      exact hinext.1 (hproj hT hL)
  intro c
  obtain ⟨a, ha⟩ := hdown c
  obtain ⟨b, hb⟩ := hup c
  exact intermediate_value_univ a b hcont ⟨ha, hb⟩

/-- **Cauchy property** for any continuous spatial projection: every inextendible causal
curve meets each slice exactly once. -/
theorem slice_cauchy_via (hπ : Continuous π) (hc : IsCausalCurve H τ τ' x x')
    (hinext : IsInextendibleVia π τ x) (t : ℝ) : ∃! s, τ s = t := by
  obtain ⟨s, hs⟩ := time_surjective_of_inextendibleVia hπ hc hinext t
  exact ⟨s, hs, fun r hr => hc.time_injective (hr.trans hs.symm)⟩

end via

/-! ### The `A₃` torus `T³_{A₃} = W₀ / Λ_{A₃}` -/

/-- `W₀ = {x ∈ ℝ⁴ : Σ xᵢ = 0}` (`eq:supp-a3-lattice`). -/
def W0 : Submodule ℝ (Fin 4 → ℝ) where
  carrier := {x | ∑ i, x i = 0}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, Pi.add_apply, Finset.sum_add_distrib] at *
    rw [ha, hb, add_zero]
  zero_mem' := by simp
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_ofPred_eq, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum] at *
    rw [ha, mul_zero]

/-- `Λ_{A₃} = W₀ ∩ ℤ⁴` (`eq:supp-a3-lattice`), as an additive subgroup of `W₀`. -/
def lambdaA3 : AddSubgroup W0 where
  carrier := {w | ∀ i, ∃ z : ℤ, (w : Fin 4 → ℝ) i = z}
  add_mem' := by
    intro a b ha hb i
    obtain ⟨z, hz⟩ := ha i
    obtain ⟨z', hz'⟩ := hb i
    exact ⟨z + z', by simp [hz, hz']⟩
  zero_mem' := fun i => ⟨0, by simp⟩
  neg_mem' := by
    intro a ha i
    obtain ⟨z, hz⟩ := ha i
    exact ⟨-z, by simp [hz]⟩

/-- The flat `A₃` torus `T³_{A₃} = W₀ / Λ_{A₃}`. -/
abbrev TorusA3 : Type := W0 ⧸ lambdaA3

/-- The vector `(x₀+x₁+x₂, x₀−x₁−x₂, −x₀+x₁−x₂, −x₀−x₁+x₂)/2 ∈ ℝ⁴`. -/
noncomputable def a3EmbedFun (x : Fin 3 → ℝ) : Fin 4 → ℝ :=
  ![(x 0 + x 1 + x 2) / 2, (x 0 - x 1 - x 2) / 2, (-x 0 + x 1 - x 2) / 2,
    (-x 0 - x 1 + x 2) / 2]

theorem a3EmbedFun_mem (x : Fin 3 → ℝ) : a3EmbedFun x ∈ W0 := by
  show ∑ i, a3EmbedFun x i = 0
  simp [a3EmbedFun, Fin.sum_univ_succ]
  ring

/-- Orthonormal coordinates on `W₀`: `x ∈ ℝ³ ↦ a3Embed x ∈ W₀`. -/
noncomputable def a3Embed (x : Fin 3 → ℝ) : W0 := ⟨a3EmbedFun x, a3EmbedFun_mem x⟩

theorem continuous_a3Embed : Continuous a3Embed := by
  refine Continuous.subtype_mk ?_ _
  refine continuous_pi fun i => ?_
  fin_cases i <;> simp [a3EmbedFun] <;> fun_prop

/-- The coordinates are Euclidean-orthonormal: `‖a3Embed x‖² = ‖x‖²` (the scalar product on
`W₀` is the restriction of the standard one on `ℝ⁴`). -/
theorem a3Embed_normSq (x : Fin 3 → ℝ) :
    ∑ i, ((a3Embed x : W0) : Fin 4 → ℝ) i ^ 2 = ∑ a, x a ^ 2 := by
  simp [a3Embed, a3EmbedFun, Fin.sum_univ_succ]
  ring

theorem a3Embed_sub (x y : Fin 3 → ℝ) : a3Embed (x - y) = a3Embed x - a3Embed y := by
  apply Subtype.ext
  funext i
  fin_cases i <;> simp [a3Embed, a3EmbedFun] <;> ring

/-- The coordinates cover all of `W₀`. -/
theorem a3Embed_surjective : Function.Surjective a3Embed := by
  rintro ⟨w, hw⟩
  have hs : w 0 + w 1 + w 2 + w 3 = 0 := by
    have : ∑ i, w i = 0 := hw
    simpa [Fin.sum_univ_succ, add_assoc] using this
  refine ⟨![w 0 + w 1, w 0 + w 2, w 0 + w 3], ?_⟩
  apply Subtype.ext
  funext i
  fin_cases i <;> simp [a3Embed, a3EmbedFun] <;> linarith

/-- The covering projection `ℝ³ → T³_{A₃}`. -/
noncomputable def a3TorusProj (x : Fin 3 → ℝ) : TorusA3 :=
  QuotientAddGroup.mk (a3Embed x)

theorem continuous_a3TorusProj : Continuous a3TorusProj :=
  QuotientAddGroup.continuous_mk.comp continuous_a3Embed

/-- The kernel of the projection is the `D₃` lattice `{x ∈ ℤ³ : x₀ + x₁ + x₂ even}`. -/
theorem a3Embed_mem_lambdaA3_iff (x : Fin 3 → ℝ) :
    a3Embed x ∈ lambdaA3 ↔ (∀ a, ∃ z : ℤ, x a = z) ∧ ∃ m : ℤ, x 0 + x 1 + x 2 = 2 * m := by
  constructor
  · intro h
    obtain ⟨z0, h0⟩ := h 0
    obtain ⟨z1, h1⟩ := h 1
    obtain ⟨z2, h2⟩ := h 2
    obtain ⟨z3, h3⟩ := h 3
    simp only [a3Embed, a3EmbedFun] at h0 h1 h2 h3
    simp at h0 h1 h2 h3
    refine ⟨fun a => ?_, ⟨z0, by push_cast; linarith⟩⟩
    fin_cases a
    · refine ⟨z0 + z1, ?_⟩
      show x 0 = ((z0 + z1 : ℤ) : ℝ)
      push_cast; linarith
    · refine ⟨z0 + z2, ?_⟩
      show x 1 = ((z0 + z2 : ℤ) : ℝ)
      push_cast; linarith
    · refine ⟨z0 + z3, ?_⟩
      show x 2 = ((z0 + z3 : ℤ) : ℝ)
      push_cast; linarith
  · rintro ⟨hz, m, hm⟩ i
    obtain ⟨z0, h0⟩ := hz 0
    obtain ⟨z1, h1⟩ := hz 1
    obtain ⟨z2, h2⟩ := hz 2
    fin_cases i
    · exact ⟨m, by simp [a3Embed, a3EmbedFun]; linarith⟩
    · exact ⟨z0 - m, by simp [a3Embed, a3EmbedFun]; push_cast; linarith⟩
    · exact ⟨z1 - m, by simp [a3Embed, a3EmbedFun]; push_cast; linarith⟩
    · exact ⟨z2 - m, by simp [a3Embed, a3EmbedFun]; push_cast; linarith⟩

/-- The twelve `A₃` roots `±eᵢ ± eⱼ` of the `D₃` realization (`a3Roots`) map into `Λ_{A₃}`;
in fact `a3Embed (a3Roots r)` are exactly the oriented roots `eᵢ − eⱼ` of
`eq:supp-a3-oriented-roots`. -/
theorem a3Embed_a3Roots_mem (r : Fin 12) :
    a3Embed (RenewalGeometry.a3Roots r) ∈ lambdaA3 := by
  rw [a3Embed_mem_lambdaA3_iff]
  refine ⟨fun a => ?_, ?_⟩
  · fin_cases r <;> fin_cases a <;> simp [RenewalGeometry.a3Roots] <;>
      first
      | (refine ⟨1, ?_⟩; norm_num; done)
      | (refine ⟨-1, ?_⟩; norm_num; done)
      | (refine ⟨0, ?_⟩; norm_num; done)
  · fin_cases r <;> simp [RenewalGeometry.a3Roots] <;>
      first
      | (refine ⟨1, ?_⟩; norm_num; done)
      | (refine ⟨-1, ?_⟩; norm_num; done)

/-- `2ℤ³` lies in the kernel of the projection. -/
theorem a3Embed_two_int_mem (k : Fin 3 → ℤ) :
    a3Embed (fun a => 2 * (k a : ℝ)) ∈ lambdaA3 := by
  rw [a3Embed_mem_lambdaA3_iff]
  exact ⟨fun a => ⟨2 * k a, by push_cast; ring⟩, ⟨k 0 + k 1 + k 2, by push_cast; ring⟩⟩

/-- Every point of `T³_{A₃}` is the image of a point of the cube `[0, 2]³`. -/
theorem a3TorusProj_image_cube :
    a3TorusProj '' (Set.pi univ fun _ => Icc (0 : ℝ) 2) = univ := by
  refine eq_univ_of_forall fun q => ?_
  obtain ⟨w, rfl⟩ := QuotientAddGroup.mk_surjective q
  obtain ⟨x, rfl⟩ := a3Embed_surjective w
  let k : Fin 3 → ℤ := fun a => ⌊x a / 2⌋
  refine ⟨fun a => x a - 2 * (k a : ℝ), ?_, ?_⟩
  · intro a _
    have h1 := Int.floor_le (x a / 2)
    have h2 := Int.lt_floor_add_one (x a / 2)
    constructor <;> simp only [k] <;> linarith
  · apply (QuotientAddGroup.eq_iff_sub_mem).mpr
    have : a3Embed (fun a => x a - 2 * (k a : ℝ)) - a3Embed x =
        -a3Embed (fun a => 2 * (k a : ℝ)) := by
      apply Subtype.ext
      funext i
      fin_cases i <;> simp [a3Embed, a3EmbedFun] <;> ring
    show a3Embed (fun a => x a - 2 * (k a : ℝ)) - a3Embed x ∈ lambdaA3
    rw [this]
    exact neg_mem (a3Embed_two_int_mem k)

/-- **`T³_{A₃}` is compact.** -/
instance compactSpace_torusA3 : CompactSpace TorusA3 := by
  refine ⟨?_⟩
  rw [← a3TorusProj_image_cube]
  exact (isCompact_univ_pi fun _ => isCompact_Icc).image continuous_a3TorusProj

/-! ### de Sitter on `ℝ × T³_{A₃}` -/

/-- **Global hyperbolicity of de Sitter on `ℝ × T³_{A₃}`**: `t` has timelike gradient
(`g^{tt} = -1`), every slice `{t} × T³_{A₃}` is compact and spacelike, every causal curve meets
it at most once, and every inextendible causal curve meets it exactly once. -/
theorem desitter_globally_hyperbolic_slicing_A3 (H : ℝ) :
    (∀ t, (lorentzMetric H t)⁻¹ 0 0 = -1) ∧
    (∀ t : ℝ, IsCompact ({t} ×ˢ (univ : Set TorusA3))) ∧
    (∀ t dx, lorentzQuadratic H t 0 dx ≤ 0 ↔ dx = 0) ∧
    (∀ (τ τ' : ℝ → ℝ) (x x' : ℝ → Fin 3 → ℝ), IsCausalCurve H τ τ' x x' →
      Function.Injective τ) ∧
    (∀ (τ τ' : ℝ → ℝ) (x x' : ℝ → Fin 3 → ℝ), IsCausalCurve H τ τ' x x' →
      IsInextendibleVia a3TorusProj τ x → ∀ t, ∃! s, τ s = t) :=
  ⟨lorentzMetric_inv_time H, fun _ => isCompact_singleton.prod isCompact_univ,
    causal_zero_time_iff H, fun _ _ _ _ hc => hc.time_injective,
    fun _ _ _ _ hc hi t => slice_cauchy_via continuous_a3TorusProj hc hi t⟩

/-- **`thm:supp-desitter-einstein`** in full, on the manuscript's spatial quotient
`ℝ × T³_{A₃}`: the displayed connection is the metric, torsion-free (unique such) spin
connection of the coframe, `Ω = H² ϑ ∧ ϑ`, `Ric = 3H² g`, `R = 12H²`, `G + 3H² g = 0`
(frame and coordinates), the coframe pulls back to `g_H`, and the slices `t = const` are
compact Cauchy hypersurfaces of `ℝ × T³_{A₃}`. -/
theorem desitter_cartan_einstein_cauchy_A3 (H : ℝ) :
    ((∀ A B C, DeSitterCartan.eta A * DeSitterCartan.spinConnection H A B C =
        -(DeSitterCartan.eta B * DeSitterCartan.spinConnection H B A C)) ∧
      DeSitterCartan.torsionComponents (DeSitterCartan.coframeStructure H)
        (DeSitterCartan.spinConnection H) = 0 ∧
      (∀ ω : Fin 4 → Fin 4 → Fin 4 → ℝ,
        (∀ A B C, DeSitterCartan.eta A * ω A B C = -(DeSitterCartan.eta B * ω B A C)) →
        DeSitterCartan.torsionComponents (DeSitterCartan.coframeStructure H) ω = 0 →
        ω = DeSitterCartan.spinConnection H) ∧
      DeSitterCartan.curvatureComponents (DeSitterCartan.coframeStructure H)
          (DeSitterCartan.spinConnection H) = DeSitterCartan.constantCurvature H ∧
      (∀ t, DeSitterCartan.coordinateRicci H t = (3 * H ^ 2) • lorentzMetric H t) ∧
      DeSitterCartan.frameScalar H = 12 * H ^ 2 ∧
      (∀ t, DeSitterCartan.coordinateRicci H t -
        (DeSitterCartan.frameScalar H / 2) • lorentzMetric H t +
        (3 * H ^ 2) • lorentzMetric H t = 0) ∧
      (∀ t, (DeSitterCartan.coframeMatrix H t).transpose * DeSitterCartan.etaMatrix *
        DeSitterCartan.coframeMatrix H t = lorentzMetric H t)) ∧
    (∀ t, (lorentzMetric H t)⁻¹ 0 0 = -1) ∧
    (∀ t : ℝ, IsCompact ({t} ×ˢ (univ : Set TorusA3))) ∧
    (∀ t dx, lorentzQuadratic H t 0 dx ≤ 0 ↔ dx = 0) ∧
    (∀ (τ τ' : ℝ → ℝ) (x x' : ℝ → Fin 3 → ℝ), IsCausalCurve H τ τ' x x' →
      Function.Injective τ) ∧
    (∀ (τ τ' : ℝ → ℝ) (x x' : ℝ → Fin 3 → ℝ), IsCausalCurve H τ τ' x x' →
      IsInextendibleVia a3TorusProj τ x → ∀ t, ∃! s, τ s = t) :=
  ⟨(desitter_cartan_einstein_cauchy H).1, desitter_globally_hyperbolic_slicing_A3 H⟩

/-! ### Non-vacuity -/

/-- The comoving observer is inextendible in `ℝ × T³_{A₃}`. -/
theorem comoving_isInextendibleVia_A3 : IsInextendibleVia a3TorusProj id (fun _ => 0) := by
  constructor
  · rintro ⟨p, hp⟩
    have h1 : Tendsto (fun s : ℝ => s) atTop (𝓝 p.1) := (continuous_fst.tendsto p).comp hp
    exact not_tendsto_nhds_of_tendsto_atTop tendsto_id _ h1
  · rintro ⟨p, hp⟩
    have h1 : Tendsto (fun s : ℝ => s) atBot (𝓝 p.1) := (continuous_fst.tendsto p).comp hp
    exact not_tendsto_nhds_of_tendsto_atBot tendsto_id _ h1

example (H t : ℝ) : ∃! s, id s = t :=
  slice_cauchy_via continuous_a3TorusProj (comoving_isCausalCurve H)
    comoving_isInextendibleVia_A3 t

/-- `T³_{A₃}` is not a point (the projection of `(1/2, 0, 0)` is not that of `0`). -/
example : a3TorusProj ![1 / 2, 0, 0] ≠ a3TorusProj 0 := by
  intro h
  have h' := (QuotientAddGroup.eq_iff_sub_mem).mp h.symm
  rw [← a3Embed_sub, zero_sub, a3Embed_mem_lambdaA3_iff] at h'
  obtain ⟨-, m, hm⟩ := h'
  simp at hm
  have : (m : ℝ) = -1 / 4 := by linarith
  have h4 : (4 * m : ℝ) = -1 := by rw [this]; ring
  have : (4 * m : ℤ) = -1 := by exact_mod_cast h4
  omega

end RenewalGeometry.DeSitterCauchyA3
