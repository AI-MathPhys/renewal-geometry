/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.AffineInformationProjectionExact
import NCG.Grand.EntropicProjectionKKTExact

/-!
# Exact finite gradient bijection for affine information projection

This closes CY.13c.  The relative interior of the finite response polytope is
represented intrinsically by its faithful barycentric selectors.  Minimizing
relative entropy on such a moment fibre gives a strictly positive minimizer;
the finite-dimensional KKT equation then puts its logarithmic gradient in the
range of the adjoint moment map, hence in the exponential family.  Direction
separation gives uniqueness of the natural parameter.
-/

open Finset Filter Topology
open scoped RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 400000

namespace NCG
namespace AffineProjection

variable {ι E : Type*} [Fintype ι] [Nonempty ι]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

/-- Euclidean selector coordinates on the finite response alphabet. -/
abbrev SelectorSpace (ι : Type*) [Fintype ι] := EuclideanSpace ℝ ι

/-- The affine mean of a selector. -/
noncomputable def selectorMean (X : ι → E) (q : SelectorSpace ι) : E :=
  ∑ i, q i • X i

/-- The probability fibre over the affine mean `θ`. -/
def momentFiber (X : ι → E) (θ : E) : Set (SelectorSpace ι) :=
  {q | (∀ i, 0 ≤ q i) ∧ (∑ i, q i = 1) ∧ selectorMean X q = θ}

/-- Intrinsic relative interior of the finite response polytope: precisely the
means admitting a faithful barycentric selector. -/
def RelativeMomentInterior (X : ι → E) : Set E :=
  {θ | ∃ q ∈ momentFiber X θ, ∀ i, 0 < q i}

/-- The mean map of the reference-relative exponential family. -/
noncomputable def expMean (g : ι → ℝ) (X : ι → E) (l : E) : E :=
  ∑ i, expQ g X l i • X i

/-- No nonzero natural-parameter direction is constant on all response atoms.
This is the intrinsic `V_Γ` condition used in CY.13b--CY.13c. -/
def SeparatesNaturalDirections (X : ι → E) : Prop :=
  ∀ u : E, u ≠ 0 → ∃ a b : ι, ⟪u, X a⟫ ≠ ⟪u, X b⟫

/-- Relative entropy on Euclidean selector coordinates. -/
noncomputable def selectorKL (q : SelectorSpace ι) (g : ι → ℝ) : ℝ :=
  ∑ i, EntropicProjection.klTerm (q i) (g i)

theorem isClosed_momentFiber (X : ι → E) (θ : E) :
    IsClosed (momentFiber X θ) := by
  have hrepr : momentFiber X θ =
      (⋂ i, {q : SelectorSpace ι | 0 ≤ q i}) ∩
      {q : SelectorSpace ι | ∑ i, q i = 1} ∩
      {q : SelectorSpace ι | selectorMean X q = θ} := by
    ext q
    simp only [momentFiber, Set.mem_setOf_eq, Set.mem_inter_iff,
      Set.mem_iInter]
    tauto
  rw [hrepr]
  refine ((isClosed_iInter fun i =>
      isClosed_le continuous_const (EuclideanSpace.proj (𝕜 := ℝ) i).continuous).inter
    (isClosed_eq (continuous_finsetSum _ fun i _ =>
      (EuclideanSpace.proj (𝕜 := ℝ) i).continuous) continuous_const)).inter ?_
  exact isClosed_eq
    (continuous_finsetSum _ fun i _ =>
      (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.smul continuous_const)
    continuous_const

theorem isBounded_momentFiber (X : ι → E) (θ : E) :
    Bornology.IsBounded (momentFiber X θ) := by
  rw [isBounded_iff_forall_norm_le]
  refine ⟨Fintype.card ι, fun q hq => ?_⟩
  have hcard : (1 : ℝ) ≤ Fintype.card ι := by
    exact_mod_cast Fintype.card_pos_iff.mpr (inferInstance : Nonempty ι)
  have hcoord : ∀ i, q i ≤ 1 := by
    intro i
    calc
      q i ≤ ∑ j, q j :=
        Finset.single_le_sum (fun j _ => hq.1 j) (Finset.mem_univ i)
      _ = 1 := hq.2.1
  have hsq : ‖q‖ ^ 2 ≤ Fintype.card ι := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      ∑ i, q i ^ 2 ≤ ∑ _i : ι, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        nlinarith [hq.1 i, hcoord i]
      _ = Fintype.card ι := by simp
  nlinarith [norm_nonneg q]

theorem isCompact_momentFiber (X : ι → E) (θ : E) :
    IsCompact (momentFiber X θ) :=
  Metric.isCompact_of_isClosed_isBounded
    (isClosed_momentFiber X θ) (isBounded_momentFiber X θ)

theorem continuous_selectorKL (g : ι → ℝ) :
    Continuous (fun q : SelectorSpace ι => selectorKL q g) := by
  refine continuous_finsetSum _ fun i _ => ?_
  unfold EntropicProjection.klTerm
  exact ((Real.continuous_mul_log.comp
      (EuclideanSpace.proj (𝕜 := ℝ) i).continuous).sub
    ((EuclideanSpace.proj (𝕜 := ℝ) i).continuous.mul continuous_const))

/-- Relative entropy attains a minimum on every nonempty affine moment
fibre. -/
theorem exists_momentFiber_min (g : ι → ℝ) (X : ι → E) (θ : E)
    (hne : (momentFiber X θ).Nonempty) :
    ∃ q₀ ∈ momentFiber X θ,
      ∀ q ∈ momentFiber X θ, selectorKL q₀ g ≤ selectorKL q g := by
  obtain ⟨q₀, hq₀, hmin⟩ :=
    (isCompact_momentFiber X θ).exists_isMinOn hne
      (continuous_selectorKL g).continuousOn
  exact ⟨q₀, hq₀, fun q hq => hmin hq⟩

theorem convex_momentFiber (X : ι → E) (θ : E) :
    Convex ℝ (momentFiber X θ) := by
  intro q hq r hr a b ha hb hab
  refine ⟨fun i => ?_, ?_, ?_⟩
  · exact add_nonneg (mul_nonneg ha (hq.1 i)) (mul_nonneg hb (hr.1 i))
  · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      Finset.sum_add_distrib, ← Finset.mul_sum, hq.2.1, hr.2.1,
      ← add_mul, hab, one_mul]
  · calc
      selectorMean X (a • q + b • r) =
          a • selectorMean X q + b • selectorMean X r := by
        simp [selectorMean, add_smul, Finset.sum_add_distrib,
          Finset.smul_sum, smul_smul]
      _ = a • θ + b • θ := by rw [hq.2.2, hr.2.2]
      _ = (a + b) • θ := (add_smul a b θ).symm
      _ = θ := by rw [hab, one_smul]

/-- A minimizer in a moment fibre containing a faithful selector is itself
faithful.  This is the finite entropy-barrier argument at every boundary
coordinate. -/
theorem momentFiber_minimizer_positive
    (g : ι → ℝ) (X : ι → E) (θ : E)
    (q₀ : SelectorSpace ι) (hq₀ : q₀ ∈ momentFiber X θ)
    (q : SelectorSpace ι) (hq : q ∈ momentFiber X θ)
    (hqpos : ∀ i, 0 < q i)
    (hmin : ∀ r ∈ momentFiber X θ, selectorKL q₀ g ≤ selectorKL r g) :
    ∀ i, 0 < q₀ i := by
  classical
  intro i
  by_contra hnpos
  have hi0 : q₀ i = 0 := le_antisymm (not_lt.mp hnpos) (hq₀.1 i)
  let C : ℝ := (selectorKL q₀ g - selectorKL q g) / q i
  let s : ℝ := min (-1) (C - 1)
  let t : ℝ := Real.exp s
  have hsneg : s < 0 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have ht0 : 0 < t := Real.exp_pos s
  have ht1 : t < 1 := (Real.exp_lt_one_iff).2 hsneg
  have hsC : s < C := by
    have hsle : s ≤ C - 1 := min_le_right _ _
    linarith
  have hlogt : Real.log t = s := Real.log_exp s
  let qt : SelectorSpace ι := (1 - t) • q₀ + t • q
  have hqt : qt ∈ momentFiber X θ := by
    exact convex_momentFiber X θ hq₀ hq (sub_nonneg.mpr ht1.le) ht0.le (by ring)
  have hiExact : EntropicProjection.klTerm (qt i) (g i) =
      (1 - t) * EntropicProjection.klTerm (q₀ i) (g i) +
        t * EntropicProjection.klTerm (q i) (g i) +
        t * q i * Real.log t := by
    rw [show qt i = t * q i by simp [qt, hi0]]
    rw [hi0]
    simp only [EntropicProjection.klTerm, zero_mul, sub_zero]
    rw [Real.log_mul ht0.ne' (hqpos i).ne']
    ring
  have hbound : selectorKL qt g ≤
      (1 - t) * selectorKL q₀ g + t * selectorKL q g +
        t * q i * Real.log t := by
    unfold selectorKL
    calc
      ∑ j, EntropicProjection.klTerm (qt j) (g j) ≤
          ∑ j, ((1 - t) * EntropicProjection.klTerm (q₀ j) (g j) +
            t * EntropicProjection.klTerm (q j) (g j) +
            if j = i then t * q i * Real.log t else 0) := by
        apply Finset.sum_le_sum
        intro j hj
        by_cases hji : j = i
        · subst j
          rw [if_pos rfl, hiExact]
        · rw [if_neg hji, add_zero]
          exact EntropicProjection.klTerm_convex_combo
            (hq₀.1 j) (hq.1 j) ht0.le ht1.le
      _ = (1 - t) * (∑ j, EntropicProjection.klTerm (q₀ j) (g j)) +
          t * (∑ j, EntropicProjection.klTerm (q j) (g j)) +
            t * q i * Real.log t := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum]
        simp
  have hstrict :
      (1 - t) * selectorKL q₀ g + t * selectorKL q g +
          t * q i * Real.log t < selectorKL q₀ g := by
    rw [hlogt]
    have hCeq : q i * C = selectorKL q₀ g - selectorKL q g := by
      dsimp [C]
      field_simp [(hqpos i).ne']
    have hqs : q i * s < q i * C := mul_lt_mul_of_pos_left hsC (hqpos i)
    have htq : 0 < t * q i := mul_pos ht0 (hqpos i)
    nlinarith
  have : selectorKL qt g < selectorKL q₀ g := lt_of_le_of_lt hbound hstrict
  exact (not_lt_of_ge (hmin qt hqt)) this

/-- The affine moment map whose kernel is the tangent space of a moment
fibre. -/
abbrev MomentTarget (E : Type*) := WithLp 2 (ℝ × E)

noncomputable def affineMomentMap (X : ι → E) :
    SelectorSpace ι →ₗ[ℝ] MomentTarget E where
  toFun q := WithLp.toLp 2 (∑ i, q i, selectorMean X q)
  map_add' q r := by
    apply WithLp.ofLp_injective
    ext
    · simp [Finset.sum_add_distrib]
    · simp [selectorMean, add_smul, Finset.sum_add_distrib]
  map_smul' c q := by
    apply WithLp.ofLp_injective
    ext
    · simp [Finset.mul_sum]
    · simp [selectorMean, Finset.smul_sum, smul_smul]

@[simp] theorem affineMomentMap_apply_fst (X : ι → E) (q : SelectorSpace ι) :
    (affineMomentMap X q).fst = ∑ i, q i := rfl

@[simp] theorem affineMomentMap_apply_snd (X : ι → E) (q : SelectorSpace ι) :
    (affineMomentMap X q).snd = selectorMean X q := rfl

theorem affineMomentMap_single [DecidableEq ι] (X : ι → E) (i : ι) :
    affineMomentMap X (EuclideanSpace.single i 1) =
      WithLp.toLp 2 ((1 : ℝ), X i) := by
  apply WithLp.ofLp_injective
  ext
  · simp [affineMomentMap]
  · simp [affineMomentMap, selectorMean]

private theorem hasDerivAt_selectorKL_affine
    (g : ι → ℝ) (q h : SelectorSpace ι) (hq : ∀ i, 0 < q i) :
    HasDerivAt (fun t : ℝ => selectorKL (q + t • h) g)
      (∑ i, h i * (Real.log (q i) + 1 - Real.log (g i))) 0 := by
  unfold selectorKL
  have hpoint : ∀ i : ι, HasDerivAt
      (fun t : ℝ => EntropicProjection.klTerm ((q + t • h) i) (g i))
      (h i * (Real.log (q i) + 1 - Real.log (g i))) 0 := by
    intro i
    have hinner : HasDerivAt (fun t : ℝ => t * h i + q i) (h i) 0 := by
      simpa using ((hasDerivAt_id (x := 0)).mul_const (h i)).const_add (q i)
    unfold EntropicProjection.klTerm
    have hout := (Real.hasDerivAt_mul_log (hq i).ne').sub
      ((hasDerivAt_id (x := q i)).mul_const (Real.log (g i)))
    have hout' : HasDerivAt
        ((fun x => x * Real.log x) - fun y => y * Real.log (g i))
        (Real.log (q i) + 1 - Real.log (g i)) (0 * h i + q i) := by
      simpa using hout
    have hc := hout'.comp 0 hinner
    have hf : (fun t : ℝ =>
        ((q + t • h) i) * Real.log ((q + t • h) i) -
          ((q + t • h) i) * Real.log (g i)) =
        (((fun x => x * Real.log x) - fun y => y * Real.log (g i)) ∘
          fun t => t * h i + q i) := by
      funext t
      simp only [Function.comp_apply, Pi.sub_apply,
        PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      rw [show q i + t * h i = t * h i + q i by ring]
    rw [hf]
    simpa [mul_comm] using hc
  have hsum := HasDerivAt.sum (u := Finset.univ)
    (A := fun i t => EntropicProjection.klTerm ((q + t • h) i) (g i))
    (A' := fun i => h i * (Real.log (q i) + 1 - Real.log (g i)))
    (fun i _ => hpoint i)
  have hfun : (∑ i : ι,
      fun t : ℝ => EntropicProjection.klTerm ((q + t • h) i) (g i)) =
      fun t : ℝ => ∑ i : ι,
        EntropicProjection.klTerm ((q + t • h) i) (g i) := by
    funext t
    simp
  rw [← hfun]
  exact hsum

/-- Finite KKT for a faithful affine-fibre minimizer: it belongs to the
reference-relative exponential family, with the scalar multiplier eliminated
by normalization. -/
theorem exponential_parameter_of_positive_minimizer
    (g : ι → ℝ) (hg : ∀ i, 0 < g i) (X : ι → E) (θ : E)
    (q₀ : SelectorSpace ι) (hq₀ : q₀ ∈ momentFiber X θ)
    (hqpos : ∀ i, 0 < q₀ i)
    (hmin : ∀ q ∈ momentFiber X θ, selectorKL q₀ g ≤ selectorKL q g) :
    ∃ l : E, ∀ i, q₀ i = expQ g X l i := by
  classical
  let v : SelectorSpace ι := WithLp.toLp 2 fun i =>
    Real.log (q₀ i) + 1 - Real.log (g i)
  have hvorth : v ∈ (LinearMap.ker (affineMomentMap X))ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro h hh
    have hAh : affineMomentMap X h = 0 := hh
    have hsum : ∑ i, h i = 0 := by
      have := congrArg (fun z : MomentTarget E => z.fst) hAh
      simpa using this
    have hmean : selectorMean X h = 0 := by
      have := congrArg (fun z : MomentTarget E => z.snd) hAh
      simpa using this
    have hfeas : ∀ᶠ t : ℝ in 𝓝 0, q₀ + t • h ∈ momentFiber X θ := by
      have hnonneg : ∀ᶠ t : ℝ in 𝓝 0, ∀ i, 0 ≤ (q₀ + t • h) i := by
        rw [Filter.eventually_all]
        intro i
        exact (continuous_const.continuousAt.eventually_lt
          (continuous_const.add
            (continuous_id.mul continuous_const)).continuousAt
              (by simpa using hqpos i)).mono (fun _ ht => ht.le)
      filter_upwards [hnonneg] with t ht
      have hqmap : affineMomentMap X q₀ =
          WithLp.toLp 2 ((1 : ℝ), θ) := by
        apply WithLp.ofLp_injective
        ext
        · exact hq₀.2.1
        · exact hq₀.2.2
      have hmap : affineMomentMap X (q₀ + t • h) =
          WithLp.toLp 2 ((1 : ℝ), θ) := by
        rw [map_add, map_smul, hqmap, hAh]
        simp
      exact ⟨ht,
        congrArg (fun z : MomentTarget E => z.fst) hmap,
        congrArg (fun z : MomentTarget E => z.snd) hmap⟩
    have hlocal : IsLocalMin (fun t : ℝ => selectorKL (q₀ + t • h) g) 0 := by
      filter_upwards [hfeas] with t ht
      simpa using hmin _ ht
    have hderiv := hasDerivAt_selectorKL_affine g q₀ h hqpos
    have hzero := hlocal.hasDerivAt_eq_zero hderiv
    calc
      inner ℝ h v = ∑ i, h i *
          (Real.log (q₀ i) + 1 - Real.log (g i)) := by
        rw [PiLp.inner_apply]
        apply Finset.sum_congr rfl
        intro i hi
        simp only [v, WithLp.ofLp_toLp, RCLike.inner_apply, conj_trivial]
        ring
      _ = 0 := hzero
  have hvRange : v ∈ (LinearMap.adjoint (affineMomentMap X)).range := by
    rw [← LinearMap.orthogonal_ker (affineMomentMap X)]
    exact hvorth
  obtain ⟨u, hu⟩ := hvRange
  let l : E := u.snd
  let c : ℝ := u.fst - 1
  have hlog : ∀ i, Real.log (q₀ i / g i) = c + ⟪l, X i⟫ := by
    intro i
    have hadj := LinearMap.adjoint_inner_right (affineMomentMap X)
      (EuclideanSpace.single i 1) u
    rw [hu, affineMomentMap_single] at hadj
    have hcoord : v i = u.fst + ⟪u.snd, X i⟫ := by
      rw [EuclideanSpace.inner_single_left] at hadj
      simpa [WithLp.prod_inner_apply, real_inner_comm] using hadj
    have hvdef : v i = Real.log (q₀ i) + 1 - Real.log (g i) := rfl
    rw [hvdef] at hcoord
    rw [Real.log_div (hqpos i).ne' (hg i).ne']
    simp only [c, l]
    linarith
  have hraw : ∀ i, q₀ i = g i * Real.exp (c + ⟪l, X i⟫) := by
    intro i
    calc
      q₀ i = g i * (q₀ i / g i) := by field_simp [(hg i).ne']
      _ = g i * Real.exp (Real.log (q₀ i / g i)) := by
        rw [Real.exp_log (div_pos (hqpos i) (hg i))]
      _ = g i * Real.exp (c + ⟪l, X i⟫) := by rw [hlog i]
  have hnorm : Real.exp c * expZ g X l = 1 := by
    calc
      Real.exp c * expZ g X l =
          ∑ i, g i * Real.exp (c + ⟪l, X i⟫) := by
        rw [expZ, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Real.exp_add]
        ring
      _ = ∑ i, q₀ i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hraw i]
      _ = 1 := hq₀.2.1
  refine ⟨l, fun i => ?_⟩
  rw [hraw i, expQ, Real.exp_add]
  have hZ := expZ_pos g X hg l
  have hc : Real.exp c = 1 / expZ g X l := by
    apply (eq_div_iff hZ.ne').2
    simpa [mul_comm] using hnorm
  rw [hc]
  field_simp

/-- Every exponential-family mean has a faithful barycentric selector, hence
lies in the intrinsic relative interior. -/
theorem expMean_mem_relativeMomentInterior
    (g : ι → ℝ) (hg : ∀ i, 0 < g i) (X : ι → E) (l : E) :
    expMean g X l ∈ RelativeMomentInterior X := by
  let q : SelectorSpace ι := WithLp.toLp 2 (expQ g X l)
  refine ⟨q, ?_, ?_⟩
  · refine ⟨fun i => (expQ_pos g X hg l i).le, ?_, ?_⟩
    · simpa [q] using expQ_sum g X hg l
    · rfl
  · intro i
    exact expQ_pos g X hg l i

/-- CY.13c, surjectivity: every faithful barycentric mean is the mean of a
unique entropy-minimizing exponential comparator. -/
theorem expMean_surjective_relativeMomentInterior
    (g : ι → ℝ) (hg : ∀ i, 0 < g i) (X : ι → E) :
    ∀ θ ∈ RelativeMomentInterior X, ∃ l : E, expMean g X l = θ := by
  intro θ hθ
  obtain ⟨p, hp, hppos⟩ := hθ
  obtain ⟨q₀, hq₀, hmin⟩ :=
    exists_momentFiber_min g X θ ⟨p, hp⟩
  have hqpos := momentFiber_minimizer_positive
    g X θ q₀ hq₀ p hp hppos hmin
  obtain ⟨l, hl⟩ := exponential_parameter_of_positive_minimizer
    g hg X θ q₀ hq₀ hqpos hmin
  refine ⟨l, ?_⟩
  calc
    expMean g X l = selectorMean X q₀ := by
      unfold expMean selectorMean
      apply Finset.sum_congr rfl
      intro i hi
      rw [hl i]
    _ = θ := hq₀.2.2

/-- Equality of exponential means forces equality of the two tilted
selectors. -/
theorem expQ_eq_of_expMean_eq
    (g : ι → ℝ) (hg : ∀ i, 0 < g i) (X : ι → E) {l l' : E}
    (hmean : expMean g X l = expMean g X l') :
    expQ g X l = expQ g X l' := by
  have hforward := unique_min g X hg l (expQ g X l')
    (expQ_pos g X hg l') (expQ_sum g X hg l') (by simpa [expMean] using hmean.symm)
  have hbackward := unique_min g X hg l' (expQ g X l)
    (expQ_pos g X hg l) (expQ_sum g X hg l) (by simpa [expMean] using hmean)
  exact (hforward.2.mp (le_antisymm hbackward.1 hforward.1)).symm

/-- CY.13c, injectivity on the natural parameter space `V_Γ`. -/
theorem expMean_injective
    (g : ι → ℝ) (hg : ∀ i, 0 < g i) (X : ι → E)
    (hsep : SeparatesNaturalDirections X) :
    Function.Injective (expMean g X) := by
  intro l l' hmean
  have hq := expQ_eq_of_expMean_eq g hg X hmean
  by_contra hne
  have hsub : l - l' ≠ 0 := sub_ne_zero.mpr hne
  obtain ⟨a, b, hab⟩ := hsep (l - l') hsub
  have hlogeq : ∀ i,
      ⟪l, X i⟫ - expPsi g X l = ⟪l', X i⟫ - expPsi g X l' := by
    intro i
    calc
      ⟪l, X i⟫ - expPsi g X l =
          Real.log (expQ g X l i / g i) :=
        (log_expQ_div g X hg l i).symm
      _ = Real.log (expQ g X l' i / g i) := by rw [congrFun hq i]
      _ = ⟪l', X i⟫ - expPsi g X l' := log_expQ_div g X hg l' i
  have ha := hlogeq a
  have hb := hlogeq b
  apply hab
  simp only [inner_sub_left]
  linarith

/-- The exponential mean with its canonical relative-interior codomain. -/
noncomputable def expMeanToInterior
    (g : ι → ℝ) (hg : ∀ i, 0 < g i) (X : ι → E) :
    E → {θ : E // θ ∈ RelativeMomentInterior X} :=
  fun l => ⟨expMean g X l, expMean_mem_relativeMomentInterior g hg X l⟩

/-- **CY.13c (exact finite convex duality).**  Under the intrinsic direction
separation condition, the gradient/mean map of the finite log-partition is a
bijection from `V_Γ` onto the relative interior of the response polytope. -/
theorem expMeanToInterior_bijective
    (g : ι → ℝ) (hg : ∀ i, 0 < g i) (X : ι → E)
    (hsep : SeparatesNaturalDirections X) :
    Function.Bijective (expMeanToInterior g hg X) := by
  constructor
  · intro l l' h
    apply expMean_injective g hg X hsep
    exact congrArg Subtype.val h
  · intro θ
    obtain ⟨l, hl⟩ := expMean_surjective_relativeMomentInterior
      g hg X θ.1 θ.2
    refine ⟨l, ?_⟩
    apply Subtype.ext
    exact hl

end AffineProjection
end NCG
