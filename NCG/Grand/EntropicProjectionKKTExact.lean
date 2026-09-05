/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.EntropicProjectionExact

/-!
# Finite KKT theorem for the entropic occurrence projection

This file supplies the finite-dimensional multiplier step in AO.6.  The
variables live on the actual admitted edge subtype.  Vanishing of the first
variation on the kernel of the two-marginal map puts the logarithmic gradient
in the range of its adjoint, which is exactly the source-plus-target potential
space.
-/

open Finset Filter Topology

noncomputable section

set_option maxHeartbeats 200000

namespace NCG
namespace EntropicProjection

variable {X Y : Type*} [Fintype X] [Fintype Y]
variable {E : Set (X × Y)} {α : X → ℝ} {β : Y → ℝ}
variable [DecidableEq X] [DecidableEq Y] [DecidablePred fun p => p ∈ E]

/-- The finite Euclidean space of admitted-edge perturbations. -/
abbrev EdgeSpace (E : Set (X × Y)) :=
  EuclideanSpace ℝ {p : X × Y // p ∈ E}

/-- Row and column sums of an admitted-edge perturbation. -/
noncomputable abbrev marginalTangentMap (E : Set (X × Y))
    [DecidablePred fun p => p ∈ E] :
    EdgeSpace E →ₗ[ℝ] EuclideanSpace ℝ (X ⊕ Y) := by
  exact {
  toFun := fun h => WithLp.toLp 2 fun z => match z with
    | Sum.inl x => ∑ e, if e.1.1 = x then h e else 0
    | Sum.inr y => ∑ e, if e.1.2 = y then h e else 0
  map_add' := by
    intro h k
    apply WithLp.ofLp_injective
    funext z
    cases z <;> simp only [PiLp.add_apply]
    all_goals
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro e he
      split_ifs <;> simp
  map_smul' := by
    intro c h
    apply WithLp.ofLp_injective
    funext z
    cases z <;> simp only [PiLp.smul_apply, RingHom.id_apply, smul_eq_mul]
    all_goals
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      split_ifs <;> simp }

@[simp] theorem marginalTangentMap_apply_inl (h : EdgeSpace E) (x : X) :
    (marginalTangentMap E h) (Sum.inl x) =
      ∑ e : {p : X × Y // p ∈ E}, if e.1.1 = x then h e else 0 := rfl

@[simp] theorem marginalTangentMap_apply_inr (h : EdgeSpace E) (y : Y) :
    (marginalTangentMap E h) (Sum.inr y) =
      ∑ e : {p : X × Y // p ∈ E}, if e.1.2 = y then h e else 0 := rfl

/-- Extend an admitted-edge perturbation by zero to all pairs. -/
noncomputable def extendEdge (h : EdgeSpace E) (p : X × Y) : ℝ := by
  exact ∑ e : {q : X × Y // q ∈ E}, if e.1 = p then h e else 0

@[simp] theorem extendEdge_coe (h : EdgeSpace E)
    (e : {p : X × Y // p ∈ E}) : extendEdge h e.1 = h e := by
  rw [extendEdge, Finset.sum_eq_single e]
  · simp
  · intro b hb hbe
    have hval : b.1 ≠ e.1 := by
      intro h
      exact hbe (Subtype.ext h)
    simp [hval]
  · exact fun h => absurd (Finset.mem_univ e) h

theorem extendEdge_eq_zero_of_not_mem (h : EdgeSpace E) {p : X × Y}
    (hp : p ∉ E) : extendEdge h p = 0 := by
  rw [extendEdge]
  apply Finset.sum_eq_zero
  intro e he
  rw [if_neg]
  intro hEq
  exact hp (hEq ▸ e.property)

theorem sum_extendEdge_mul (h : EdgeSpace E) (q : X × Y → ℝ) :
    ∑ p, extendEdge h p * q p =
      ∑ e : {p : X × Y // p ∈ E}, h e * q e.1 := by
  calc
    ∑ p, extendEdge h p * q p =
        ∑ p ∈ Finset.univ.filter (fun p => p ∈ E), extendEdge h p * q p := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro p hpU hpF
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hpF
      rw [extendEdge_eq_zero_of_not_mem h hpF, zero_mul]
    _ = ∑ e : {p : X × Y // p ∈ E}, extendEdge h e.1 * q e.1 := by
      exact Finset.sum_subtype _ (by simp) _
    _ = ∑ e : {p : X × Y // p ∈ E}, h e * q e.1 := by
      apply Finset.sum_congr rfl
      intro e he
      rw [extendEdge_coe]

theorem sum_extendEdge_fst (h : EdgeSpace E) (x : X) :
    ∑ y, extendEdge h (x, y) =
      ∑ e : {p : X × Y // p ∈ E}, if e.1.1 = x then h e else 0 := by
  simp only [extendEdge]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  by_cases hx : e.1.1 = x
  · subst x
    rw [Finset.sum_eq_single e.1.2]
    · simp
    · intro y hy hne
      rw [if_neg]
      intro hEq
      exact hne (congrArg Prod.snd hEq).symm
    · exact fun hmem => absurd (Finset.mem_univ e.1.2) hmem
  · have hne : ∀ y, e.1 ≠ (x, y) := by
      intro y hEq
      exact hx (congrArg Prod.fst hEq)
    simp [hx, hne]

theorem sum_extendEdge_snd (h : EdgeSpace E) (y : Y) :
    ∑ x, extendEdge h (x, y) =
      ∑ e : {p : X × Y // p ∈ E}, if e.1.2 = y then h e else 0 := by
  simp only [extendEdge]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  by_cases hy : e.1.2 = y
  · subst y
    rw [Finset.sum_eq_single e.1.1]
    · simp
    · intro x hx hne
      rw [if_neg]
      intro hEq
      exact hne (congrArg Prod.fst hEq).symm
    · exact fun hmem => absurd (Finset.mem_univ e.1.1) hmem
  · have hne : ∀ x, e.1 ≠ (x, y) := by
      intro x hEq
      exact hy (congrArg Prod.snd hEq)
    simp [hy, hne]

theorem marginalTangentMap_eq_zero_iff (h : EdgeSpace E) :
    marginalTangentMap E h = 0 ↔
      (∀ x, ∑ y, extendEdge h (x, y) = 0) ∧
      (∀ y, ∑ x, extendEdge h (x, y) = 0) := by
  constructor
  · intro hz
    constructor
    · intro x
      have hx := congrArg (fun v : EuclideanSpace ℝ (X ⊕ Y) => v (Sum.inl x)) hz
      simp only [marginalTangentMap, LinearMap.coe_mk, AddHom.coe_mk,
        WithLp.ofLp_toLp, Pi.zero_apply] at hx
      rw [sum_extendEdge_fst]
      simpa using hx
    · intro y
      have hy := congrArg (fun v : EuclideanSpace ℝ (X ⊕ Y) => v (Sum.inr y)) hz
      simp only [marginalTangentMap, LinearMap.coe_mk, AddHom.coe_mk,
        WithLp.ofLp_toLp, Pi.zero_apply] at hy
      rw [sum_extendEdge_snd]
      simpa using hy
  · rintro ⟨hrow, hcol⟩
    apply WithLp.ofLp_injective
    funext z
    cases z with
    | inl x =>
        have hx := hrow x
        simp only [marginalTangentMap, LinearMap.coe_mk, AddHom.coe_mk,
          WithLp.ofLp_toLp, Pi.zero_apply]
        change (∑ e : {p : X × Y // p ∈ E},
          if e.1.1 = x then h e else 0) = 0
        rw [← sum_extendEdge_fst]
        exact hx
    | inr y =>
        have hy := hcol y
        simp only [marginalTangentMap, LinearMap.coe_mk, AddHom.coe_mk,
          WithLp.ofLp_toLp, Pi.zero_apply]
        change (∑ e : {p : X × Y // p ∈ E},
          if e.1.2 = y then h e else 0) = 0
        rw [← sum_extendEdge_snd]
        exact hy

/-- The two-marginal image of one admitted edge is the sum of its endpoint
coordinate vectors. -/
theorem marginalTangentMap_single (e : {p : X × Y // p ∈ E}) :
    marginalTangentMap E (EuclideanSpace.single e 1) =
      EuclideanSpace.single (Sum.inl e.1.1) 1 +
        EuclideanSpace.single (Sum.inr e.1.2) 1 := by
  apply WithLp.ofLp_injective
  funext z
  cases z with
  | inl x =>
      rw [marginalTangentMap_apply_inl]
      simp only [PiLp.single_apply, PiLp.add_apply]
      rw [Fintype.sum_eq_single e (fun b hbe => by simp [hbe])]
      simp [eq_comm]
  | inr y =>
      rw [marginalTangentMap_apply_inr]
      simp only [PiLp.single_apply, PiLp.add_apply]
      rw [Fintype.sum_eq_single e (fun b hbe => by simp [hbe])]
      simp [eq_comm]

private theorem hasDerivAt_klTerm_affine {p r d : ℝ} (hp : 0 < p) :
    HasDerivAt (fun t => klTerm (p + t * d) r)
      (d * (Real.log p + 1 - Real.log r)) 0 := by
  have hinner : HasDerivAt (fun t : ℝ => t * d + p) d 0 := by
    simpa using ((hasDerivAt_id (x := 0)).mul_const d).const_add p
  unfold klTerm
  have hout := (Real.hasDerivAt_mul_log hp.ne').sub
      ((hasDerivAt_id (x := p)).mul_const (Real.log r))
  have hout' : HasDerivAt
      ((fun x => x * Real.log x) - fun y => y * Real.log r)
      (Real.log p + 1 - Real.log r) (0 * d + p) := by
    simpa using hout
  have hc := hout'.comp 0 hinner
  have hf : (fun t : ℝ =>
      (p + t * d) * Real.log (p + t * d) -
        (p + t * d) * Real.log r) =
      (((fun x => x * Real.log x) - fun y => y * Real.log r) ∘
        fun t => t * d + p) := by
    funext t
    simp only [Function.comp_apply, Pi.sub_apply, id_eq]
    rw [show p + t * d = t * d + p by ring]
  rw [hf]
  simpa [mul_comm] using hc

theorem klTerm_convex_combo {a q r t : ℝ}
    (ha : 0 ≤ a) (hq : 0 ≤ q) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    klTerm ((1 - t) * a + t * q) r ≤
      (1 - t) * klTerm a r + t * klTerm q r := by
  have hc := Real.convexOn_mul_log.2 ha hq
    (sub_nonneg.mpr ht1) ht0 (by ring)
  simp only [smul_eq_mul] at hc
  unfold klTerm
  nlinarith

/-- On the canonical feasible face (every admitted edge occurs in some
feasible coupling), an entropy minimizer cannot vanish on an admitted edge.
The proof perturbs toward a witness coupling and uses the strictly negative
`t q log t` boundary term. -/
theorem minimizer_positive_on_canonicalFace
    (R : X × Y → ℝ)
    (π₀ : X × Y → ℝ) (h₀ : π₀ ∈ feasible E α β)
    (hface : ∀ p, p ∈ E → ∃ q ∈ feasible E α β, 0 < q p)
    (hmin : ∀ π ∈ feasible E α β, kl π₀ R ≤ kl π R) :
    ∀ p, p ∈ E → 0 < π₀ p := by
  intro p hpE
  by_contra hnpos
  have hp0 : π₀ p = 0 := le_antisymm (not_lt.mp hnpos) (h₀.1 p)
  obtain ⟨q, hq, hqp⟩ := hface p hpE
  let C : ℝ := (kl π₀ R - kl q R) / q p
  let s : ℝ := min (-1) (C - 1)
  let t : ℝ := Real.exp s
  have hsneg : s < 0 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have ht0 : 0 < t := Real.exp_pos s
  have ht1 : t < 1 := (Real.exp_lt_one_iff).2 hsneg
  have hsC : s < C := by
    have hsle : s ≤ C - 1 := min_le_right _ _
    linarith
  have hlogt : Real.log t = s := Real.log_exp s
  let πt : X × Y → ℝ := fun z => (1 - t) * π₀ z + t * q z
  have hπt : πt ∈ feasible E α β := by
    have hc := convex_feasible (E := E) (α := α) (β := β) h₀ hq
      (sub_nonneg.mpr ht1.le) ht0.le (by ring)
    have heq : (1 - t) • π₀ + t • q = πt := by
      funext z
      simp [πt, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [← heq]
    exact hc
  have hpExact : klTerm (πt p) (R p) =
      (1 - t) * klTerm (π₀ p) (R p) + t * klTerm (q p) (R p) +
        t * q p * Real.log t := by
    rw [show πt p = t * q p by simp [πt, hp0]]
    rw [hp0]
    simp only [klTerm, zero_mul, sub_zero]
    rw [Real.log_mul ht0.ne' hqp.ne']
    ring
  have hbound : kl πt R ≤
      (1 - t) * kl π₀ R + t * kl q R + t * q p * Real.log t := by
    unfold kl
    calc
      ∑ z, klTerm (πt z) (R z) ≤
          ∑ z, ((1 - t) * klTerm (π₀ z) (R z) +
            t * klTerm (q z) (R z) +
            if z = p then t * q p * Real.log t else 0) := by
        apply Finset.sum_le_sum
        intro z hz
        by_cases hzp : z = p
        · subst z
          rw [if_pos rfl, hpExact]
        · rw [if_neg hzp, add_zero]
          exact klTerm_convex_combo (h₀.1 z) (hq.1 z) ht0.le ht1.le
      _ = (1 - t) * (∑ z, klTerm (π₀ z) (R z)) +
          t * (∑ z, klTerm (q z) (R z)) + t * q p * Real.log t := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum]
        simp
  have hstrict :
      (1 - t) * kl π₀ R + t * kl q R + t * q p * Real.log t < kl π₀ R := by
    rw [hlogt]
    have hCeq : q p * C = kl π₀ R - kl q R := by
      dsimp [C]
      field_simp [hqp.ne']
    have hqs : q p * s < q p * C := mul_lt_mul_of_pos_left hsC hqp
    have := mul_pos ht0 hqp
    nlinarith
  have : kl πt R < kl π₀ R := lt_of_le_of_lt hbound hstrict
  exact (not_lt_of_ge (hmin πt hπt)) this

/-- A strictly positive minimizer on the canonical feasible face has source
and target Gibbs potentials.  This is the exact finite KKT multiplier step. -/
theorem gibbsPotentials_of_positive_minimizer
    (R : X × Y → ℝ) (hR : ∀ p, 0 < R p)
    (π₀ : X × Y → ℝ) (h₀ : π₀ ∈ feasible E α β)
    (hpos : ∀ p, p ∈ E → 0 < π₀ p)
    (hmin : ∀ π ∈ feasible E α β, kl π₀ R ≤ kl π R) :
    ∃ a : X → ℝ, ∃ b : Y → ℝ, IsGibbsOn R a b (E := E) π₀ := by
  classical
  let g : EdgeSpace E := WithLp.toLp 2 fun e =>
    Real.log (π₀ e.1) + 1 - Real.log (R e.1)
  have hgorth : g ∈ (LinearMap.ker (marginalTangentMap E))ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro h hh
    have hAh : marginalTangentMap E h = 0 := hh
    have hmarg := (marginalTangentMap_eq_zero_iff h).mp hAh
    let d : X × Y → ℝ := extendEdge h
    have hdSupport : ∀ p, p ∉ E → d p = 0 := by
      intro p hp
      exact extendEdge_eq_zero_of_not_mem h hp
    have hrow : ∀ x, ∑ y, d (x, y) = 0 := hmarg.1
    have hcol : ∀ y, ∑ x, d (x, y) = 0 := hmarg.2
    have hfeas : ∀ᶠ t : ℝ in 𝓝 0,
        (fun p => π₀ p + t * d p) ∈ feasible E α β := by
      have hnonneg : ∀ᶠ t : ℝ in 𝓝 0, ∀ p, 0 ≤ π₀ p + t * d p := by
        rw [Filter.eventually_all]
        intro p
        by_cases hpE : p ∈ E
        · exact (continuous_const.continuousAt.eventually_lt
            (continuous_const.add (continuous_id.mul continuous_const)).continuousAt
              (by simpa using hpos p hpE)).mono (fun _ ht => ht.le)
        · have hp0 := h₀.2.1 p hpE
          simp [hp0, hdSupport p hpE]
      filter_upwards [hnonneg] with t ht
      refine ⟨ht, ?_, ?_, ?_⟩
      · intro p hpE
        simp [h₀.2.1 p hpE, hdSupport p hpE]
      · intro x
        rw [Finset.sum_congr rfl fun y _ => by
          show π₀ (x, y) + t * d (x, y) = _; rfl,
          Finset.sum_add_distrib, ← Finset.mul_sum, hrow x, mul_zero,
          add_zero, h₀.2.2.1 x]
      · intro y
        rw [Finset.sum_congr rfl fun x _ => by
          show π₀ (x, y) + t * d (x, y) = _; rfl,
          Finset.sum_add_distrib, ← Finset.mul_sum, hcol y, mul_zero,
          add_zero, h₀.2.2.2 y]
    have hlocal : IsLocalMin
        (fun t : ℝ => kl (fun p => π₀ p + t * d p) R) 0 := by
      filter_upwards [hfeas] with t ht
      simpa using hmin _ ht
    have hderiv : HasDerivAt
        (fun t : ℝ => kl (fun p => π₀ p + t * d p) R)
        (∑ e : {p : X × Y // p ∈ E},
          h e * (Real.log (π₀ e.1) + 1 - Real.log (R e.1))) 0 := by
      unfold kl
      have hall : HasDerivAt
          (fun t : ℝ => ∑ p : X × Y, klTerm (π₀ p + t * d p) (R p))
          (∑ p : X × Y,
            d p * (Real.log (π₀ p) + 1 - Real.log (R p))) 0 := by
        have hpoint : ∀ p : X × Y, HasDerivAt
            (fun t : ℝ => klTerm (π₀ p + t * d p) (R p))
            (d p * (Real.log (π₀ p) + 1 - Real.log (R p))) 0 := by
          intro p
          by_cases hpE : p ∈ E
          · exact hasDerivAt_klTerm_affine (r := R p) (d := d p) (hpos p hpE)
          · have hp0 := h₀.2.1 p hpE
            have hd0 := hdSupport p hpE
            have hc : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 0 :=
              hasDerivAt_const (x := 0) 0
            simpa [hp0, hd0, klTerm] using hc
        have hsum := HasDerivAt.sum (u := Finset.univ)
          (A := fun p t => klTerm (π₀ p + t * d p) (R p))
          (A' := fun p => d p * (Real.log (π₀ p) + 1 - Real.log (R p)))
          (fun p _ => hpoint p)
        have hfun : (∑ p : X × Y,
            fun t : ℝ => klTerm (π₀ p + t * d p) (R p)) =
            fun t : ℝ => ∑ p : X × Y,
              klTerm (π₀ p + t * d p) (R p) := by
          funext t
          simp
        rw [← hfun]
        exact hsum
      convert hall using 1
      rw [sum_extendEdge_mul]
    have hzero := hlocal.hasDerivAt_eq_zero hderiv
    calc
      inner ℝ h g = ∑ e : {p : X × Y // p ∈ E},
          h e * (Real.log (π₀ e.1) + 1 - Real.log (R e.1)) := by
        rw [PiLp.inner_apply]
        apply Finset.sum_congr rfl
        intro e he
        simp only [g, WithLp.ofLp_toLp, RCLike.inner_apply, conj_trivial]
        ring
      _ = 0 := hzero
  rw [LinearMap.orthogonal_ker] at hgorth
  obtain ⟨u, hu⟩ := hgorth
  let a : X → ℝ := fun x => u (Sum.inl x)
  let b : Y → ℝ := fun y => u (Sum.inr y) - 1
  refine ⟨a, b, ?_⟩
  intro p hp
  let e : {p : X × Y // p ∈ E} := ⟨p, hp⟩
  have hadj := LinearMap.adjoint_inner_right (marginalTangentMap E)
    (EuclideanSpace.single e 1) u
  rw [hu] at hadj
  have hcoord : g e = a p.1 + b p.2 + 1 := by
    rw [EuclideanSpace.inner_single_left] at hadj
    simp only [map_one, one_mul] at hadj
    rw [marginalTangentMap_single, inner_add_left,
      EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_left] at hadj
    calc
      g e = u (Sum.inl p.1) + u (Sum.inr p.2) := by
        simpa [e] using hadj
      _ = a p.1 + b p.2 + 1 := by simp only [a, b]; ring
  have hlog : Real.log (π₀ p / R p) = a p.1 + b p.2 := by
    have hgdef : g e = Real.log (π₀ p) + 1 - Real.log (R p) := rfl
    rw [hgdef] at hcoord
    rw [Real.log_div (hpos p hp).ne' (hR p).ne']
    linarith
  calc
    π₀ p = π₀ p * 1 := (mul_one _).symm
    _ = π₀ p * (R p / R p) := by
      exact congrArg (fun z : ℝ => π₀ p * z) (div_self (hR p).ne').symm
    _ = R p * (π₀ p / R p) := by ring
    _ = R p * Real.exp (Real.log (π₀ p / R p)) := by
      rw [Real.exp_log (div_pos (hpos p hp) (hR p))]
    _ = R p * Real.exp (a p.1 + b p.2) := by rw [hlog]

/-- **`thm:accepted-entropic-projection`, canonical-face form.**  Nonemptiness
and the manuscript's canonical-face condition now produce the minimizer and
its Gibbs potentials simultaneously; the potentials are no longer an input.
The information Pythagoras, both zero tests, and componentwise gauge
uniqueness are then derived from that constructed pair. -/
theorem accepted_entropic_projection_canonicalFace
    (R : X × Y → ℝ) (hR : ∀ p, 0 < R p)
    (hne : (feasible E α β).Nonempty)
    (hface : ∀ p, p ∈ E → ∃ q ∈ feasible E α β, 0 < q p) :
    ∃ π₀ : X × Y → ℝ, ∃ a : X → ℝ, ∃ b : Y → ℝ,
      π₀ ∈ feasible E α β ∧
      (∀ π ∈ feasible E α β, kl π₀ R ≤ kl π R) ∧
      (∀ π : X × Y → ℝ, π ∈ feasible E α β →
        (∀ ρ ∈ feasible E α β, kl π R ≤ kl ρ R) → π = π₀) ∧
      IsGibbsOn R a b (E := E) π₀ ∧
      (∀ π ∈ feasible E α β,
        kl π R = kl π π₀ + kl π₀ R) ∧
      (∀ π ∈ feasible E α β, kl π π₀ = 0 ↔ π = π₀) ∧
      ((∑ p, R p = ∑ x, α x) →
        (kl π₀ R = 0 ↔ R ∈ feasible E α β)) ∧
      (∀ [Nonempty X], ∀ (a' : X → ℝ) (b' : Y → ℝ),
        IsGibbsOn R a' b' (E := E) π₀ →
        (∀ u v : X ⊕ Y, Relation.ReflTransGen (Step E) u v) →
        ∃ c : ℝ, (∀ x, a' x = a x + c) ∧
          ∀ y, b' y = b y - c) := by
  obtain ⟨π₀, h₀, hmin⟩ := exists_min R hne
  have hpos := minimizer_positive_on_canonicalFace R π₀ h₀ hface hmin
  obtain ⟨a, b, hg⟩ :=
    gibbsPotentials_of_positive_minimizer R hR π₀ h₀ hpos hmin
  refine ⟨π₀, a, b, h₀, hmin, ?_, hg, ?_, ?_, ?_, ?_⟩
  · intro π hπ hπmin
    exact min_unique R hπ h₀ hπmin hmin
  · intro π hπ
    exact kl_pythagoras R a b hR h₀ hg hπ
  · intro π hπ
    exact selection_residual_eq_zero_iff R a b hR h₀ hg hπ
  · intro hsum
    exact occurrence_zero_iff R a b hR h₀ hg hsum
  · intro _ a' b' hg' hconn
    exact gibbs_gauge R a b hR hg hg' hconn

end EntropicProjection
end NCG
