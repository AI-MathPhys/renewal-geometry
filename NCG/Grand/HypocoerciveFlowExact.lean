/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ObservabilityGramianExact
import NCG.Grand.PositiveOperatorNormBridgeExact
import NCG.Grand.AcceptedKrylovOrbitSpan

/-!
# The hypocoercive flow, the sampled loss Gram, and (FC.10)

Machinery for `thm:GT-hypocoercive-memory`, flow part.  For `K = A - S` on a complex Hilbert
space (`A` skew-adjoint, `S ≥ 0`):

* `flow K t = e^{tK}` with its derivative, semigroup law and adjoint;
* `sampledGram K S T = ∫₀ᵀ e^{tK*} S e^{tK} dt` (the sampled loss Gram `W_K(T)`) with
  `re ⟪W_K(T) x, x⟫ = ∫₀ᵀ re ⟪S e^{tK} x, e^{tK} x⟫ dt`;
* **(FC.10)**: `e^{TK*} e^{TK} = I - 2 W_K(T)` (`gramFlow_eq`);
* **(H2) ⟺ (H4)**: no nonzero `A`-invariant subspace lies in `ker S` iff `W_K(T) ≻ 0` for
  every `T > 0` (`posDefSampled_of_noInvariant`, `noInvariant_of_posDefSampled`); the forward
  direction differentiates `S e^{tK} x ≡ 0` on `[0, T]`, the converse expands the exponential
  series.
-/

open ContinuousLinearMap Finset Module NormedSpace Set Filter
open scoped InnerProductSpace Topology

namespace NCG
namespace HypocoerciveMemory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-! ### The flow `e^{tK}` -/

/-- The flow `e^{tK}` at real time `t`. -/
noncomputable def flow (K : E →L[ℂ] E) (t : ℝ) : E →L[ℂ] E := exp ((t : ℂ) • K)

variable (K : E →L[ℂ] E)

@[simp] theorem flow_zero : flow K 0 = 1 := by simp [flow]

theorem hasDerivAt_flow (t : ℝ) : HasDerivAt (flow K) (flow K t * K) t := by
  have h1 : HasDerivAt (fun u : ℂ => exp (u • K)) (exp ((t : ℂ) • K) * K) (t : ℂ) :=
    hasDerivAt_exp_smul_const (𝕂 := ℂ) K (t : ℂ)
  have h2 := h1.scomp t Complex.ofRealCLM.hasDerivAt
  simp only [Complex.ofRealCLM_apply, Complex.ofReal_one, one_smul, Function.comp_def] at h2
  exact h2

theorem hasDerivAt_flow' (t : ℝ) : HasDerivAt (flow K) (K * flow K t) t := by
  have h1 : HasDerivAt (fun u : ℂ => exp (u • K)) (K * exp ((t : ℂ) • K)) (t : ℂ) :=
    hasDerivAt_exp_smul_const' (𝕂 := ℂ) K (t : ℂ)
  have h2 := h1.scomp t Complex.ofRealCLM.hasDerivAt
  simp only [Complex.ofRealCLM_apply, Complex.ofReal_one, one_smul, Function.comp_def] at h2
  exact h2

theorem continuous_flow : Continuous (flow K) :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_flow K t).continuousAt

theorem hasDerivAt_flow_apply (x : E) (t : ℝ) :
    HasDerivAt (fun s => flow K s x) (K (flow K t x)) t := by
  have h := ((ContinuousLinearMap.apply ℂ E x).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_flow' K t)
  simp only [Function.comp_def, ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.apply_apply] at h
  exact h

theorem continuous_flow_apply (x : E) : Continuous fun s => flow K s x :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_flow_apply K x t).continuousAt

theorem star_flow (t : ℝ) : star (flow K t) = flow (star K) t := by
  unfold flow
  rw [star_exp, star_smul, Complex.star_def, Complex.conj_ofReal]

theorem flow_add (s t : ℝ) : flow K (s + t) = flow K s * flow K t := by
  unfold flow
  rw [Complex.ofReal_add, add_smul]
  exact exp_add_of_commute_of_mem_ball (𝕂 := ℂ)
    (((Commute.refl K).smul_left (s : ℂ)).smul_right (t : ℂ))
    ((expSeries_radius_eq_top ℂ (E →L[ℂ] E)).symm ▸ edist_lt_top _ _)
    ((expSeries_radius_eq_top ℂ (E →L[ℂ] E)).symm ▸ edist_lt_top _ _)

theorem flow_mul_comm (t : ℝ) : flow K t * K = K * flow K t :=
  ((Commute.refl K).smul_left (t : ℂ)).exp_left

theorem flow_neg_mul_flow (t : ℝ) : flow K (-t) * flow K t = 1 := by
  rw [← flow_add, neg_add_cancel, flow_zero]

theorem flow_apply_ne_zero (t : ℝ) {x : E} (hx : x ≠ 0) : flow K t x ≠ 0 := by
  intro h
  apply hx
  have := congrArg (flow K (-t)) h
  rw [map_zero] at this
  have h1 : x = (flow K (-t) * flow K t) x := by rw [flow_neg_mul_flow]; rfl
  rw [h1]
  exact this

/-! ### The sampled loss Gram `W_K(T)` -/

/-- `W_K(T) = ∫₀ᵀ e^{tK*} S e^{tK} dt`. -/
noncomputable def sampledGram (S : E →L[ℂ] E) (T : ℝ) : E →L[ℂ] E :=
  ∫ t in (0 : ℝ)..T, star (flow K t) * S * flow K t

variable (S : E →L[ℂ] E)

theorem continuous_integrand : Continuous fun t => star (flow K t) * S * flow K t :=
  (((continuous_flow K).star).mul continuous_const).mul (continuous_flow K)

theorem hasDerivAt_star_flow (t : ℝ) :
    HasDerivAt (fun s => star (flow K s)) (star K * star (flow K t)) t := by
  have h : (fun s => star (flow K s)) = flow (star K) := funext (star_flow K)
  rw [h, star_flow]
  exact hasDerivAt_flow' (star K) t

theorem hasDerivAt_gramFlow (t : ℝ) :
    HasDerivAt (fun s => star (flow K s) * flow K s)
      (star K * (star (flow K t) * flow K t) + star (flow K t) * flow K t * K) t := by
  have h : HasDerivAt (fun s => star (flow K s) * flow K s)
      (star K * star (flow K t) * flow K t + star (flow K t) * (flow K t * K)) t :=
    (hasDerivAt_star_flow K t).mul (hasDerivAt_flow K t)
  convert h using 1
  simp only [mul_assoc]

theorem star_flow_mul_star (t : ℝ) : star K * star (flow K t) = star (flow K t) * star K := by
  rw [star_flow, flow_mul_comm]

/-- **(FC.10)**: `e^{TK*} e^{TK} = I - 2 W_K(T)` for `K = A - S`, `A` skew, `S` self-adjoint. -/
theorem gramFlow_eq {A : E →L[ℂ] E} (hK : K = A - S) (hA : star A = -A) (hS : star S = S)
    (T : ℝ) : star (flow K T) * flow K T = 1 - (2 : ℂ) • sampledGram K S T := by
  have hKK : star K + K = -((2 : ℂ) • S) := by
    rw [hK, star_sub, hA, hS, two_smul]
    abel
  have hderiv : ∀ s ∈ uIcc (0 : ℝ) T,
      HasDerivAt (fun s => star (flow K s) * flow K s)
        ((-2 : ℂ) • (star (flow K s) * S * flow K s)) s := by
    intro s _
    refine (hasDerivAt_gramFlow K s).congr_deriv ?_
    rw [← mul_assoc, star_flow_mul_star, mul_assoc (star (flow K s)) (flow K s) K,
      flow_mul_comm, ← mul_assoc, ← add_mul, ← mul_add, hKK, mul_neg, neg_mul, mul_smul_comm,
      smul_mul_assoc, ← neg_smul]
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (((continuous_integrand K S).const_smul (-2 : ℂ)).intervalIntegrable 0 T)
  rw [intervalIntegral.integral_smul, flow_zero, star_one, mul_one] at hint
  have h2 : star (flow K T) * flow K T = 1 + (-2 : ℂ) • sampledGram K S T := by
    unfold sampledGram
    rw [hint]
    abel
  rw [h2, neg_smul, ← sub_eq_add_neg]

omit [CompleteSpace E] in
theorem re_inner_comm (v w : E) : RCLike.re ⟪v, w⟫_ℂ = RCLike.re ⟪w, v⟫_ℂ := by
  rw [← inner_conj_symm w v, RCLike.conj_re]

/-- The quadratic form of the sampled loss Gram is the sampled loss. -/
theorem re_inner_sampledGram (T : ℝ) (x : E) :
    RCLike.re ⟪sampledGram K S T x, x⟫_ℂ
      = ∫ t in (0 : ℝ)..T, RCLike.re ⟪S (flow K t x), flow K t x⟫_ℂ := by
  have hint : IntervalIntegrable (fun t => star (flow K t) * S * flow K t) MeasureTheory.volume
    0 T := (continuous_integrand K S).intervalIntegrable 0 T
  have hint' : IntervalIntegrable (fun t => (star (flow K t) * S * flow K t) x)
      MeasureTheory.volume 0 T :=
    ((continuous_integrand K S).clm_apply continuous_const).intervalIntegrable 0 T
  have hint'' : IntervalIntegrable (fun t => ⟪x, (star (flow K t) * S * flow K t) x⟫_ℂ)
      MeasureTheory.volume 0 T :=
    (continuous_const.inner
      ((continuous_integrand K S).clm_apply continuous_const)).intervalIntegrable 0 T
  rw [sampledGram, ContinuousLinearMap.intervalIntegral_apply hint x, re_inner_comm]
  have e1 : ⟪x, ∫ t in (0 : ℝ)..T, (star (flow K t) * S * flow K t) x⟫_ℂ
      = ∫ t in (0 : ℝ)..T, ⟪x, (star (flow K t) * S * flow K t) x⟫_ℂ := by
    rw [← innerSL_apply_apply (𝕜 := ℂ) x,
      ← ContinuousLinearMap.intervalIntegral_comp_comm (innerSL ℂ x) hint']
    rfl
  have e2 : RCLike.re (∫ t in (0 : ℝ)..T, ⟪x, (star (flow K t) * S * flow K t) x⟫_ℂ)
      = ∫ t in (0 : ℝ)..T, RCLike.re ⟪x, (star (flow K t) * S * flow K t) x⟫_ℂ := by
    rw [← RCLike.reCLM_apply (K := ℂ),
      ← ContinuousLinearMap.intervalIntegral_comp_comm RCLike.reCLM hint'']
  rw [e1, e2]
  refine intervalIntegral.integral_congr fun t _ => ?_
  change RCLike.re ⟪x, star (flow K t) (S (flow K t x))⟫_ℂ = _
  rw [star_eq_adjoint, adjoint_inner_right, re_inner_comm]

/-! ### (H2) ⟺ (H4) -/

/-- (H4): the sampled loss Gram is positive definite for every `T > 0`. -/
def PosDefSampled (K S : E →L[ℂ] E) : Prop :=
  ∀ T : ℝ, 0 < T → ∀ x : E, x ≠ 0 → 0 < RCLike.re ⟪sampledGram K S T x, x⟫_ℂ

omit [CompleteSpace E] in
theorem pow_apply_eq_of_A_kernel {A : E →L[ℂ] E} (hK : K = A - S) {x : E}
    (h : ∀ j, S ((A ^ j) x) = 0) (j : ℕ) : (K ^ j) x = (A ^ j) x := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', pow_succ']
    change K ((K ^ j) x) = A ((A ^ j) x)
    rw [ih, hK, sub_apply, h j, sub_zero]

omit [CompleteSpace E] in
theorem pow_apply_eq_of_K_kernel {A : E →L[ℂ] E} (hK : K = A - S) {x : E}
    (h : ∀ j, S ((K ^ j) x) = 0) (j : ℕ) : (K ^ j) x = (A ^ j) x := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', pow_succ']
    change K ((K ^ j) x) = A ((A ^ j) x)
    have e : K ((K ^ j) x) = A ((K ^ j) x) - S ((K ^ j) x) := by rw [hK, sub_apply]
    rw [e, h j, sub_zero, ih]

/-- The exponential orbit of `x` stays in the Krylov span of `x`, so `S` kills it whenever
`S K^j x = 0` for all `j`. -/
theorem apply_flow_eq_zero_of_pow [FiniteDimensional ℂ E] {x : E} (h : ∀ j, S ((K ^ j) x) = 0)
    (t : ℝ) : S (flow K t x) = 0 := by
  have hmem : flow K t x ∈ AcceptedKrylovOrbitSpan.powerSpan K x :=
    AcceptedKrylovOrbitSpan.exp_smul_apply_mem_powerSpan K x (t : ℂ)
  have hle : AcceptedKrylovOrbitSpan.powerSpan K x ≤ LinearMap.ker (S : E →ₗ[ℂ] E) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨n, rfl⟩
    exact h n
  exact hle hmem

/-- **(H4) ⟹ (H2)**. -/
theorem noInvariant_of_posDefSampled [FiniteDimensional ℂ E] {A : E →L[ℂ] E} (hK : K = A - S)
    (h : PosDefSampled K S) : NoInvariant A S := by
  intro W hW
  rw [Submodule.eq_bot_iff]
  intro x hx
  by_contra hne
  have hx' := (mem_unobservable_iff A S x).mp (le_unobservable_of_isInvariantIn A S hW hx)
  have hSK : ∀ j, S ((K ^ j) x) = 0 := fun j => by
    rw [pow_apply_eq_of_A_kernel K S hK hx' j]
    exact hx' j
  have hzero : RCLike.re ⟪sampledGram K S 1 x, x⟫_ℂ = 0 := by
    rw [re_inner_sampledGram]
    have hterm : ∀ t : ℝ, RCLike.re ⟪S (flow K t x), flow K t x⟫_ℂ = 0 := fun t => by
      rw [apply_flow_eq_zero_of_pow K S hSK t, inner_zero_left, map_zero]
    simp only [hterm, intervalIntegral.integral_zero]
  exact (h 1 one_pos x hne).ne' hzero

/-- **(H2) ⟹ (H4)**. -/
theorem posDefSampled_of_noInvariant [FiniteDimensional ℂ E] {A : E →L[ℂ] E} (hK : K = A - S)
    (hS : S.IsPositive) (h : NoInvariant A S) : PosDefSampled K S := by
  intro T hT x hx
  set g : ℝ → ℝ := fun t => RCLike.re ⟪S (flow K t x), flow K t x⟫_ℂ with hg
  have hgc : Continuous g :=
    RCLike.continuous_re.comp
      ((S.continuous.comp (continuous_flow_apply K x)).inner (continuous_flow_apply K x))
  have hgnn : ∀ t, 0 ≤ g t := fun t => hS.re_inner_nonneg_left _
  rw [re_inner_sampledGram]
  rcases (intervalIntegral.integral_nonneg hT.le fun t _ => hgnn t).lt_or_eq with hlt | heq
  · exact hlt
  exfalso
  -- the sampled loss integrand vanishes on `[0, T]`
  have hg0 : ∀ t ∈ Icc (0 : ℝ) T, g t = 0 := by
    intro c hc
    by_contra hc0
    have hpos : 0 < ∫ t in (0 : ℝ)..T, g t :=
      intervalIntegral.integral_pos hT hgc.continuousOn (fun t _ => hgnn t)
        ⟨c, hc, lt_of_le_of_ne (hgnn c) (Ne.symm hc0)⟩
    linarith
  have hS0 : ∀ t ∈ Icc (0 : ℝ) T, S (flow K t x) = 0 := fun t ht =>
    apply_eq_zero_of_re_inner_eq_zero hS (hg0 t ht)
  -- differentiate repeatedly: `S K^j e^{tK} x = 0` on `[0, T]`
  have hder : ∀ j : ℕ, ∀ t ∈ Icc (0 : ℝ) T, S ((K ^ j) (flow K t x)) = 0 := by
    intro j
    induction j with
    | zero => intro t ht; simpa using hS0 t ht
    | succ j ih =>
      have hopen : ∀ t ∈ Ioo (0 : ℝ) T, S ((K ^ (j + 1)) (flow K t x)) = 0 := by
        intro t ht
        have hd : HasDerivAt (fun s => S ((K ^ j) (flow K s x)))
            (S ((K ^ j) (K (flow K t x)))) t := by
          have := ((S.comp (K ^ j)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
            (hasDerivAt_flow_apply K x t)
          simpa [Function.comp_def] using this
        have hev : (fun s => S ((K ^ j) (flow K s x))) =ᶠ[𝓝 t] fun _ => 0 := by
          filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
          exact ih s (Ioo_subset_Icc_self hs)
        have h0 : HasDerivAt (fun s => S ((K ^ j) (flow K s x))) 0 t :=
          (hasDerivAt_const t (0 : E)).congr_of_eventuallyEq hev
        have := hd.unique h0
        rw [pow_succ]
        exact this
      have hcont : Continuous fun s => S ((K ^ (j + 1)) (flow K s x)) :=
        (S.comp (K ^ (j + 1))).continuous.comp (continuous_flow_apply K x)
      intro t ht
      have hclos : EqOn (fun s => S ((K ^ (j + 1)) (flow K s x))) (fun _ => 0)
          (closure (Ioo (0 : ℝ) T)) :=
        Set.EqOn.closure (fun s hs => hopen s hs) hcont continuous_const
      rw [closure_Ioo hT.ne] at hclos
      exact hclos ht
  have hSK : ∀ j, S ((K ^ j) x) = 0 := fun j => by
    simpa [flow_zero] using hder j 0 ⟨le_rfl, hT.le⟩
  have hSA : ∀ j, S ((A ^ j) x) = 0 := fun j => by
    rw [← pow_apply_eq_of_K_kernel K S hK hSK j]
    exact hSK j
  have hmem : x ∈ unobservable A S := (mem_unobservable_iff A S x).mpr hSA
  have := h _ (unobservable_isInvariantIn A S)
  rw [this, Submodule.mem_bot] at hmem
  exact hx hmem

end HypocoerciveMemory
end NCG
