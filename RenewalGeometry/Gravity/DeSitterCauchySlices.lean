/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.DeSitterCartanComponentsExact

/-!
# Compact Cauchy slices of the flat de Sitter quotient
  (`thm:supp-desitter-einstein`, last sentence: "the slices `t = const` are compact Cauchy
  hypersurfaces, so the spatial quotient is globally hyperbolic"; emergent-spacetime supplement)

For the explicit metric `g_H = -dt² + e^{2Ht} Σ (dxᵃ)²` on `ℝ × T³`
(`T³ = RelationalDeSitterBranch.CompactSpatialQuotient`, three unit circles) we prove, by hand
for this metric and without a general Lorentzian causality library:

* `IsCausalCurve` — a differentiable curve `s ↦ (τ(s), x(s))`, written in the coordinates of
  the covering `ℝ × ℝ³` (the curve in the quotient is its image under `spacetimeProj`), whose
  velocity is nonzero and causal: `-τ'² + e^{2Hτ}|x'|² ≤ 0`;
* `IsInextendible` — the projected curve has no limit point in `ℝ × T³` at either end of its
  parameter line;
* `IsCausalCurve.time_deriv_ne_zero`, `IsCausalCurve.strictMono_or_strictAnti` — the time
  function is strictly monotone along every causal curve (`causal_zero_time_iff` plus Darboux's
  theorem), hence `IsCausalCurve.time_injective`: every causal curve meets each slice
  `{t} × T³` at most once;
* `IsCausalCurve.abs_spatial_deriv_le` — the light-cone speed bound `|xᵢ'| ≤ e^{-Hτ}|τ'|`;
* `tendsto_of_dominated_by_monotone` — a real function whose derivative is dominated by `C τ'`
  for a nondecreasing bounded `τ` converges (monotone convergence applied to `Cτ ∓ y`);
* `IsCausalCurve.tendsto_of_time_bddAbove` & co. — a causal curve whose time stays bounded at
  one end converges in `ℝ × T³` at that end (bounded spatial speed on a bounded time range);
* `IsCausalCurve.time_surjective_of_inextendible`, **`desitter_slice_cauchy`** — the time
  function of an inextendible causal curve is onto `ℝ`, so it meets every slice `{t} × T³`
  exactly once;
* `desitter_globally_hyperbolic_slicing` — `t` has timelike gradient (`g^{tt} = -1`), every
  slice is compact and spacelike, and it is a Cauchy hypersurface in the above sense;
* **`desitter_cartan_einstein_cauchy`** — `thm:supp-desitter-einstein` in full:
  `DeSitterCartan.desitter_cartan_einstein` together with the Cauchy slicing.

Scoped rendering (disclosed): causal curves are everywhere-differentiable curves parametrized by
the whole real line (any open parameter interval is reparametrized to `ℝ`), presented by a lift
to the covering `ℝ × ℝ³`; inextendibility means that the projected curve has no endpoint in
`ℝ × T³`.  Global hyperbolicity is certified by the existence of this Cauchy time function, the
standard criterion quoted in the manuscript.
-/

open Filter Topology Set
open scoped BigOperators

namespace RenewalGeometry.DeSitterCauchy

open RelationalDeSitterBranch

/-! ### The quotient `ℝ × T³` and causal curves -/

/-- The covering projection `ℝ³ → T³`. -/
noncomputable def torusProj (x : Fin 3 → ℝ) : CompactSpatialQuotient :=
  fun i => (x i : AddCircle (1 : ℝ))

theorem continuous_torusProj : Continuous torusProj :=
  continuous_pi fun i => (AddCircle.continuous_mk' (1 : ℝ)).comp (continuous_apply i)

/-- The projection of a covering point to the spacetime quotient `ℝ × T³`. -/
noncomputable def spacetimeProj (p : ℝ × (Fin 3 → ℝ)) : ℝ × CompactSpatialQuotient :=
  (p.1, torusProj p.2)

theorem continuous_spacetimeProj : Continuous spacetimeProj :=
  continuous_fst.prodMk (continuous_torusProj.comp continuous_snd)

/-- A causal curve of `g_H = -dt² + e^{2Ht} dx²`, presented by its lift `(τ, x)` to `ℝ × ℝ³`
with velocity `(τ', x')`: differentiable, nonzero velocity, `g_H(γ', γ') ≤ 0`. -/
structure IsCausalCurve (H : ℝ) (τ τ' : ℝ → ℝ) (x x' : ℝ → Fin 3 → ℝ) : Prop where
  hasDerivAt_time : ∀ s, HasDerivAt τ (τ' s) s
  hasDerivAt_space : ∀ s i, HasDerivAt (fun r => x r i) (x' s i) s
  causal : ∀ s, lorentzQuadratic H (τ s) (τ' s) (x' s) ≤ 0
  nonzero : ∀ s, τ' s ≠ 0 ∨ x' s ≠ 0

/-- The projected curve `s ↦ [(τ(s), x(s))] ∈ ℝ × T³`. -/
noncomputable def projCurve (τ : ℝ → ℝ) (x : ℝ → Fin 3 → ℝ) (s : ℝ) :
    ℝ × CompactSpatialQuotient :=
  spacetimeProj (τ s, x s)

/-- Inextendibility: the projected curve has no endpoint in `ℝ × T³` at either end. -/
def IsInextendible (τ : ℝ → ℝ) (x : ℝ → Fin 3 → ℝ) : Prop :=
  (¬ ∃ p, Tendsto (projCurve τ x) atTop (𝓝 p)) ∧ (¬ ∃ p, Tendsto (projCurve τ x) atBot (𝓝 p))

namespace IsCausalCurve

variable {H : ℝ} {τ τ' : ℝ → ℝ} {x x' : ℝ → Fin 3 → ℝ}

/-- The time component of a causal velocity never vanishes. -/
theorem time_deriv_ne_zero (hc : IsCausalCurve H τ τ' x x') (s : ℝ) : τ' s ≠ 0 := by
  intro h0
  have hq := hc.causal s
  rw [h0] at hq
  have hx := (causal_zero_time_iff H (τ s) (x' s)).1 hq
  rcases hc.nonzero s with h | h
  · exact h h0
  · exact h hx

/-- The time derivative has a constant sign (Darboux). -/
theorem time_deriv_pos_or_neg (hc : IsCausalCurve H τ τ' x x') :
    (∀ s, 0 < τ' s) ∨ (∀ s, τ' s < 0) := by
  have := hasDerivWithinAt_forall_lt_or_forall_gt_of_forall_ne (f := τ) (f' := τ') convex_univ
    (fun s _ => (hc.hasDerivAt_time s).hasDerivWithinAt) (m := 0)
    (fun s _ => hc.time_deriv_ne_zero s)
  rcases this with h | h
  · exact Or.inr fun s => h s (mem_univ s)
  · exact Or.inl fun s => h s (mem_univ s)

/-- **The time function is strictly monotone along every causal curve.** -/
theorem strictMono_or_strictAnti (hc : IsCausalCurve H τ τ' x x') :
    StrictMono τ ∨ StrictAnti τ := by
  rcases hc.time_deriv_pos_or_neg with h | h
  · exact Or.inl (strictMono_of_deriv_pos fun s => by rw [(hc.hasDerivAt_time s).deriv]; exact h s)
  · exact Or.inr (strictAnti_of_deriv_neg fun s => by rw [(hc.hasDerivAt_time s).deriv]; exact h s)

/-- Every causal curve meets each constant-time slice at most once. -/
theorem time_injective (hc : IsCausalCurve H τ τ' x x') : Function.Injective τ := by
  rcases hc.strictMono_or_strictAnti with h | h
  · exact h.injective
  · exact h.injective

/-- Light-cone speed bound: `|xᵢ'| ≤ e^{-Hτ} |τ'|`. -/
theorem abs_spatial_deriv_le (hc : IsCausalCurve H τ τ' x x') (s : ℝ) (i : Fin 3) :
    |x' s i| ≤ Real.exp (-H * τ s) * |τ' s| := by
  have hq := hc.causal s
  unfold lorentzQuadratic at hq
  have hi : x' s i ^ 2 ≤ ∑ j, x' s j ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (x' s j)) (Finset.mem_univ i)
  have he : Real.exp (2 * H * τ s) * Real.exp (-H * τ s) ^ 2 = 1 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_zero]; congr 1; push_cast; ring
  have hpos : 0 < Real.exp (2 * H * τ s) := Real.exp_pos _
  have hsq : x' s i ^ 2 ≤ (Real.exp (-H * τ s) * |τ' s|) ^ 2 := by
    have h1 : Real.exp (2 * H * τ s) * x' s i ^ 2 ≤ τ' s ^ 2 := by
      have := mul_le_mul_of_nonneg_left hi hpos.le
      linarith
    have h2 : (Real.exp (-H * τ s) * |τ' s|) ^ 2 =
        Real.exp (-H * τ s) ^ 2 * τ' s ^ 2 := by rw [mul_pow, sq_abs]
    rw [h2]
    have h3 : x' s i ^ 2 = Real.exp (-H * τ s) ^ 2 * (Real.exp (2 * H * τ s) * x' s i ^ 2) := by
      rw [← mul_assoc, mul_comm (Real.exp (-H * τ s) ^ 2), he, one_mul]
    rw [h3]
    exact mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
  exact abs_le_of_sq_le_sq hsq (by positivity)

end IsCausalCurve

/-! ### Convergence on a bounded time range -/

/-- A function whose derivative is dominated on `[0, ∞)` by `C τ'`, for a nondecreasing time
function `τ` bounded above, converges at `+∞`. -/
theorem tendsto_of_dominated_by_monotone {τ y τ' y' : ℝ → ℝ} {C B : ℝ} (hC : 0 ≤ C)
    (hτ : ∀ s, HasDerivAt τ (τ' s) s) (hy : ∀ s, HasDerivAt y (y' s) s)
    (hdom : ∀ s, 0 ≤ s → |y' s| ≤ C * τ' s) (hB : ∀ s, τ s ≤ B) :
    ∃ L, Tendsto y atTop (𝓝 L) := by
  set f : ℝ → ℝ := fun s => C * τ s - y s with hfdef
  set g : ℝ → ℝ := fun s => C * τ s + y s with hgdef
  have hf : ∀ s, HasDerivAt f (C * τ' s - y' s) s := fun s => ((hτ s).const_mul C).sub (hy s)
  have hg : ∀ s, HasDerivAt g (C * τ' s + y' s) s := fun s => ((hτ s).const_mul C).add (hy s)
  have hfmono : MonotoneOn f (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun s _ => (hf s).continuousAt.continuousWithinAt)
      (fun s _ => (hf s).differentiableAt.differentiableWithinAt) fun s hs => ?_
    rw [interior_Ici] at hs
    rw [(hf s).deriv]
    have := hdom s (le_of_lt hs)
    linarith [le_abs_self (y' s)]
  have hgmono : MonotoneOn g (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun s _ => (hg s).continuousAt.continuousWithinAt)
      (fun s _ => (hg s).differentiableAt.differentiableWithinAt) fun s hs => ?_
    rw [interior_Ici] at hs
    rw [(hg s).deriv]
    have := hdom s (le_of_lt hs)
    linarith [neg_abs_le (y' s)]
  have hmax : ∀ s : ℝ, max s 0 ∈ Ici (0 : ℝ) := fun s => le_max_right s 0
  have hmaxmono : Monotone fun s : ℝ => max s 0 := fun a b hab => max_le_max hab le_rfl
  set F : ℝ → ℝ := fun s => f (max s 0)
  set G : ℝ → ℝ := fun s => g (max s 0)
  have hFm : Monotone F := fun a b hab => hfmono (hmax a) (hmax b) (hmaxmono hab)
  have hGm : Monotone G := fun a b hab => hgmono (hmax a) (hmax b) (hmaxmono hab)
  have hFb : BddAbove (range F) := by
    refine ⟨2 * C * B - g 0, ?_⟩
    rintro _ ⟨s, rfl⟩
    have h1 : g 0 ≤ g (max s 0) := hgmono (mem_Ici.2 le_rfl) (hmax s) (hmax s)
    have h2 : C * τ (max s 0) ≤ C * B := mul_le_mul_of_nonneg_left (hB _) hC
    simp only [F, hfdef, hgdef] at h1 ⊢
    linarith
  have hGb : BddAbove (range G) := by
    refine ⟨2 * C * B - f 0, ?_⟩
    rintro _ ⟨s, rfl⟩
    have h1 : f 0 ≤ f (max s 0) := hfmono (mem_Ici.2 le_rfl) (hmax s) (hmax s)
    have h2 : C * τ (max s 0) ≤ C * B := mul_le_mul_of_nonneg_left (hB _) hC
    simp only [G, hfdef, hgdef] at h1 ⊢
    linarith
  have hFt := tendsto_atTop_ciSup hFm hFb
  have hGt := tendsto_atTop_ciSup hGm hGb
  refine ⟨((⨆ s, G s) - ⨆ s, F s) / 2, ?_⟩
  have hlim := (hGt.sub hFt).div_const 2
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
  simp only [F, G, hfdef, hgdef, max_eq_left hs]
  ring

namespace IsCausalCurve

variable {H : ℝ} {τ τ' : ℝ → ℝ} {x x' : ℝ → Fin 3 → ℝ}

/-- Future-type end: if `τ' > 0` and `τ` is bounded above, the curve converges in `ℝ × T³`
as `s → +∞`. -/
theorem tendsto_atTop_of_pos_of_bddAbove (hc : IsCausalCurve H τ τ' x x')
    (hpos : ∀ s, 0 < τ' s) {B : ℝ} (hB : ∀ s, τ s ≤ B) :
    ∃ p, Tendsto (projCurve τ x) atTop (𝓝 p) := by
  have hmono : Monotone τ :=
    (strictMono_of_deriv_pos fun s => by rw [(hc.hasDerivAt_time s).deriv]; exact hpos s).monotone
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
  refine ⟨spacetimeProj (⨆ s, τ s, L), ?_⟩
  have hx : Tendsto x atTop (𝓝 L) := tendsto_pi_nhds.2 hL
  exact (continuous_spacetimeProj.tendsto _).comp (hτt.prodMk_nhds hx)

/-- Reversal of the parameter of a causal curve (`s ↦ -s`), with time reflected
(`τ ↦ -τ`, `H ↦ -H`): again a causal curve. -/
theorem reflect (hc : IsCausalCurve H τ τ' x x') :
    IsCausalCurve (-H) (fun s => -τ (-s)) (fun s => τ' (-s)) (fun s => x (-s))
      (fun s => -x' (-s)) where
  hasDerivAt_time s := by
    have h := ((hc.hasDerivAt_time (-s)).comp s (hasDerivAt_neg s)).neg
    have e : (fun s => -τ (-s)) = -(τ ∘ Neg.neg) := by funext r; rfl
    rw [e]
    exact h.congr_deriv (by ring)
  hasDerivAt_space s i := by
    have h := (hc.hasDerivAt_space (-s) i).comp s (hasDerivAt_neg s)
    have e : (fun r => x (-r) i) = (fun r => x r i) ∘ Neg.neg := by funext r; rfl
    rw [e]
    exact h.congr_deriv (by simp)
  causal s := by
    have := hc.causal (-s)
    unfold lorentzQuadratic at this ⊢
    simpa [neg_mul_neg, mul_neg, neg_neg] using this
  nonzero s := by
    rcases hc.nonzero (-s) with h | h
    · exact Or.inl h
    · exact Or.inr (by simpa using h)

/-- Time reflection `τ ↦ -τ`, `H ↦ -H` with the same parameter: again a causal curve. -/
theorem timeReflect (hc : IsCausalCurve H τ τ' x x') :
    IsCausalCurve (-H) (fun s => -τ s) (fun s => -τ' s) x x' where
  hasDerivAt_time s := (hc.hasDerivAt_time s).neg
  hasDerivAt_space := hc.hasDerivAt_space
  causal s := by
    have := hc.causal s
    unfold lorentzQuadratic at this ⊢
    simpa [neg_mul_neg] using this
  nonzero s := by
    rcases hc.nonzero s with h | h
    · exact Or.inl (neg_ne_zero.mpr h)
    · exact Or.inr h

/-- Every causal curve whose time is bounded above (resp. below) has an endpoint in `ℝ × T³`
at the corresponding end of its parameter line. -/
theorem endpoint_of_time_bdd (hc : IsCausalCurve H τ τ' x x') :
    ((∃ B, ∀ s, τ s ≤ B) → (∀ s, 0 < τ' s) → ∃ p, Tendsto (projCurve τ x) atTop (𝓝 p)) ∧
    ((∃ B, ∀ s, B ≤ τ s) → (∀ s, 0 < τ' s) → ∃ p, Tendsto (projCurve τ x) atBot (𝓝 p)) ∧
    ((∃ B, ∀ s, B ≤ τ s) → (∀ s, τ' s < 0) → ∃ p, Tendsto (projCurve τ x) atTop (𝓝 p)) ∧
    ((∃ B, ∀ s, τ s ≤ B) → (∀ s, τ' s < 0) → ∃ p, Tendsto (projCurve τ x) atBot (𝓝 p)) := by
  -- the map undoing a time reflection on `ℝ × T³` is continuous
  have hneg : Continuous fun p : ℝ × CompactSpatialQuotient => (-p.1, p.2) :=
    continuous_fst.neg.prodMk continuous_snd
  refine ⟨fun ⟨B, hB⟩ hpos => hc.tendsto_atTop_of_pos_of_bddAbove hpos hB, ?_, ?_, ?_⟩
  · -- past end of a future-directed curve: reverse the parameter and reflect time
    rintro ⟨B, hB⟩ hpos
    obtain ⟨p, hp⟩ := hc.reflect.tendsto_atTop_of_pos_of_bddAbove (fun s => hpos (-s))
      (B := -B) (fun s => by have := hB (-s); linarith)
    refine ⟨(-p.1, p.2), ?_⟩
    have h2 := ((hneg.tendsto p).comp hp).comp tendsto_neg_atBot_atTop
    refine h2.congr fun s => ?_
    simp [projCurve, spacetimeProj, Function.comp]
  · rintro ⟨B, hB⟩ hneg'
    obtain ⟨p, hp⟩ := hc.timeReflect.tendsto_atTop_of_pos_of_bddAbove
      (fun s => neg_pos.mpr (hneg' s)) (B := -B) (fun s => by have := hB s; linarith)
    refine ⟨(-p.1, p.2), ?_⟩
    have h2 := (hneg.tendsto p).comp hp
    refine h2.congr fun s => ?_
    simp [projCurve, spacetimeProj, Function.comp]
  · rintro ⟨B, hB⟩ hneg'
    have hc2 := hc.timeReflect.reflect
    obtain ⟨p, hp⟩ := hc2.tendsto_atTop_of_pos_of_bddAbove
      (fun s => by simpa using hneg' (-s)) (B := B) (fun s => by simpa using hB (-s))
    refine ⟨p, ?_⟩
    have h2 := hp.comp tendsto_neg_atBot_atTop
    refine h2.congr fun s => ?_
    simp [projCurve, spacetimeProj, Function.comp]

/-- **The time function of an inextendible causal curve is onto `ℝ`.** -/
theorem time_surjective_of_inextendible (hc : IsCausalCurve H τ τ' x x')
    (hinext : IsInextendible τ x) : Function.Surjective τ := by
  obtain ⟨e1, e2, e3, e4⟩ := hc.endpoint_of_time_bdd
  have hcont : Continuous τ :=
    continuous_iff_continuousAt.2 fun s => (hc.hasDerivAt_time s).continuousAt
  -- unbounded above and below
  have hup : ∀ c, ∃ s, c ≤ τ s := by
    intro c
    by_contra h
    push Not at h
    rcases hc.time_deriv_pos_or_neg with hp | hn
    · exact hinext.1 (e1 ⟨c, fun s => (h s).le⟩ hp)
    · exact hinext.2 (e4 ⟨c, fun s => (h s).le⟩ hn)
  have hdown : ∀ c, ∃ s, τ s ≤ c := by
    intro c
    by_contra h
    push Not at h
    rcases hc.time_deriv_pos_or_neg with hp | hn
    · exact hinext.2 (e2 ⟨c, fun s => (h s).le⟩ hp)
    · exact hinext.1 (e3 ⟨c, fun s => (h s).le⟩ hn)
  intro c
  obtain ⟨a, ha⟩ := hdown c
  obtain ⟨b, hb⟩ := hup c
  exact intermediate_value_univ a b hcont ⟨ha, hb⟩

end IsCausalCurve

/-- **Cauchy property of the constant-time slices**: every inextendible causal curve of
`g_H` in `ℝ × T³` meets every slice `{t} × T³` exactly once. -/
theorem desitter_slice_cauchy {H : ℝ} {τ τ' : ℝ → ℝ} {x x' : ℝ → Fin 3 → ℝ}
    (hc : IsCausalCurve H τ τ' x x') (hinext : IsInextendible τ x) (t : ℝ) :
    ∃! s, τ s = t := by
  obtain ⟨s, hs⟩ := hc.time_surjective_of_inextendible hinext t
  exact ⟨s, hs, fun r hr => hc.time_injective (hr.trans hs.symm)⟩

/-- The inverse metric has `g^{tt} = -1`: the time function has timelike gradient. -/
theorem lorentzMetric_inv_time (H t : ℝ) : (lorentzMetric H t)⁻¹ 0 0 = -1 := by
  have h : (lorentzMetric H t)⁻¹ =
      Matrix.diagonal fun i => if i = 0 then -1 else Real.exp (-(2 * H * t)) := by
    apply Matrix.inv_eq_left_inv
    unfold lorentzMetric
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext k
    split_ifs
    · norm_num
    · rw [← Real.exp_add]; simp
  rw [h, Matrix.diagonal_apply_eq]
  simp

/-- **Global hyperbolicity of the flat de Sitter quotient**: the time function has timelike
gradient, every slice `{t} × T³` is compact and spacelike, every causal curve meets it at most
once, and every inextendible causal curve meets it exactly once (Cauchy hypersurface). -/
theorem desitter_globally_hyperbolic_slicing (H : ℝ) :
    (∀ t, (lorentzMetric H t)⁻¹ 0 0 = -1) ∧
    (∀ t : ℝ, IsCompact ({t} ×ˢ (univ : Set CompactSpatialQuotient))) ∧
    (∀ t dx, lorentzQuadratic H t 0 dx ≤ 0 ↔ dx = 0) ∧
    (∀ (τ τ' : ℝ → ℝ) (x x' : ℝ → Fin 3 → ℝ), IsCausalCurve H τ τ' x x' →
      Function.Injective τ) ∧
    (∀ (τ τ' : ℝ → ℝ) (x x' : ℝ → Fin 3 → ℝ), IsCausalCurve H τ τ' x x' →
      IsInextendible τ x → ∀ t, ∃! s, τ s = t) :=
  ⟨lorentzMetric_inv_time H, fun t => isCompact_singleton.prod isCompact_univ,
    causal_zero_time_iff H, fun _ _ _ _ hc => hc.time_injective,
    fun _ _ _ _ hc hi t => desitter_slice_cauchy hc hi t⟩

/-- **`thm:supp-desitter-einstein`** in full: the displayed connection is the metric,
torsion-free (unique such) spin connection of the coframe, `Ω = H² ϑ ∧ ϑ`, `Ric = 3H² g`,
`R = 12H²`, `G + 3H² g = 0` (frame and coordinates), and the slices `t = const` are compact
Cauchy hypersurfaces of `ℝ × T³` (`desitter_globally_hyperbolic_slicing`). -/
theorem desitter_cartan_einstein_cauchy (H : ℝ) :
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
    (∀ t : ℝ, IsCompact ({t} ×ˢ (univ : Set CompactSpatialQuotient))) ∧
    (∀ t dx, lorentzQuadratic H t 0 dx ≤ 0 ↔ dx = 0) ∧
    (∀ (τ τ' : ℝ → ℝ) (x x' : ℝ → Fin 3 → ℝ), IsCausalCurve H τ τ' x x' →
      Function.Injective τ) ∧
    (∀ (τ τ' : ℝ → ℝ) (x x' : ℝ → Fin 3 → ℝ), IsCausalCurve H τ τ' x x' →
      IsInextendible τ x → ∀ t, ∃! s, τ s = t) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, -⟩ := DeSitterCartan.desitter_cartan_einstein H
  exact ⟨⟨h1, h2, h3, h4, h5, h6, h7, DeSitterCartan.coframe_pullback_metric H⟩,
    desitter_globally_hyperbolic_slicing H⟩

/-! ### Non-vacuity -/

/-- The comoving observer `s ↦ (s, 0)` is an inextendible causal (timelike) curve. -/
theorem comoving_isCausalCurve (H : ℝ) :
    IsCausalCurve H id (fun _ => 1) (fun _ => 0) (fun _ => 0) where
  hasDerivAt_time s := hasDerivAt_id s
  hasDerivAt_space s i := hasDerivAt_const s 0
  causal s := by unfold lorentzQuadratic; simp
  nonzero _ := Or.inl one_ne_zero

theorem comoving_isInextendible : IsInextendible id (fun _ => 0) := by
  constructor
  · rintro ⟨p, hp⟩
    have h1 : Tendsto (fun s : ℝ => s) atTop (𝓝 p.1) := by
      have := (continuous_fst.tendsto p).comp hp
      have e : (Prod.fst ∘ projCurve id fun _ => (0 : Fin 3 → ℝ)) = fun s => s := by
        funext s; rfl
      rwa [e] at this
    exact not_tendsto_nhds_of_tendsto_atTop tendsto_id _ h1
  · rintro ⟨p, hp⟩
    have h1 : Tendsto (fun s : ℝ => s) atBot (𝓝 p.1) := by
      have := (continuous_fst.tendsto p).comp hp
      have e : (Prod.fst ∘ projCurve id fun _ => (0 : Fin 3 → ℝ)) = fun s => s := by
        funext s; rfl
      rwa [e] at this
    exact not_tendsto_nhds_of_tendsto_atBot tendsto_id _ h1

example (H t : ℝ) : ∃! s, id s = t :=
  desitter_slice_cauchy (comoving_isCausalCurve H) comoving_isInextendible t

end RenewalGeometry.DeSitterCauchy
