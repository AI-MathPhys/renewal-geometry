/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.MultivariateCLT

/-!
# Finite-dimensional Donsker limits for i.i.d. vector increments

Machinery for the stochastic continuum records: the partial-sum process
`S_n(t) = n^{-1/2} ∑_{k < ⌊n t⌋} X k` of i.i.d. centred square-integrable random vectors
converges, in the sense of finite-dimensional distributions, to the Brownian motion with
covariance `covMatrix X P`.

This file contains the analytic core:

* `tendsto_one_add_pow_exp_of_tendsto_mul`: `(1 + g n)^{N n} → exp t` when `g n → 0` and
  `N n * g n → t` (variable integer exponent);
* `charFun_map_smul_eq`: Cramér–Wold scaling `φ_X(s • t) = φ_{⟪t, X⟫}(s)`;
* `taylor_charFun_inner`: `φ_{⟪t, X⟫}(s) = 1 - (tᵀ S t) s² / 2 + o(s²)`;
* `charFun_block_sum`: the characteristic function of a scaled block sum is a power;
* `tendsto_charFun_block_sum`: a block of `N n ~ c n` terms scaled by `n^{-1/2}` has
  characteristic functions converging to those of `N(0, c S)`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Complex Finset Matrix Asymptotics
open scoped InnerProductSpace

namespace NCG
namespace DonskerFiniteDimensional

open MultivariateCLT

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

/-! ### Variable-exponent powers -/

/-- If `g n → 0` and `N n * g n → t`, then `(1 + g n) ^ (N n) → exp t`. -/
theorem tendsto_one_add_pow_exp_of_tendsto_mul (g : ℕ → ℂ) (N : ℕ → ℕ) (t : ℂ)
    (hg : Tendsto g atTop (𝓝 0)) (hN : Tendsto (fun n => (N n : ℂ) * g n) atTop (𝓝 t)) :
    Tendsto (fun n => (1 + g n) ^ (N n)) atTop (𝓝 (exp t)) := by
  -- eventually `‖g n‖ < 1/2`
  have hsmall : ∀ᶠ n in atTop, ‖g n‖ < 1 / 2 := by
    have := (continuous_norm.tendsto (0 : ℂ)).comp hg
    simp only [Function.comp_def, norm_zero] at this
    exact this.eventually (gt_mem_nhds (by norm_num))
  -- `(1 + g n) ^ N n = exp (N n * log (1 + g n))`
  have hrepr : ∀ᶠ n in atTop, (1 + g n) ^ (N n) = exp ((N n : ℂ) * log (1 + g n)) := by
    filter_upwards [hsmall] with n hn
    have hne : 1 + g n ≠ 0 := by
      intro h
      have : ‖g n‖ = 1 := by
        have h' : g n = -1 := by linear_combination h
        rw [h', norm_neg, norm_one]
      linarith
    rw [Complex.exp_nat_mul, Complex.exp_log hne]
  -- the exponent converges to `t`
  have hbound : ∀ᶠ n in atTop,
      ‖(N n : ℂ) * (log (1 + g n) - g n)‖ ≤ ‖(N n : ℂ) * g n‖ * ‖g n‖ := by
    filter_upwards [hsmall] with n hn
    have h1 := Complex.norm_log_one_add_sub_self_le (lt_trans hn (by norm_num))
    have h2 : (1 - ‖g n‖)⁻¹ / 2 ≤ 1 := by
      have hpos : (1 : ℝ) / 2 < 1 - ‖g n‖ := by linarith
      have hinv : (1 - ‖g n‖)⁻¹ ≤ 2 := by
        rw [inv_le_comm₀ (by linarith) (by norm_num)]
        linarith
      linarith
    calc ‖(N n : ℂ) * (log (1 + g n) - g n)‖
        = ‖(N n : ℂ)‖ * ‖log (1 + g n) - g n‖ := norm_mul _ _
      _ ≤ ‖(N n : ℂ)‖ * (‖g n‖ ^ 2 * (1 - ‖g n‖)⁻¹ / 2) :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = ‖(N n : ℂ)‖ * ‖g n‖ * ‖g n‖ * ((1 - ‖g n‖)⁻¹ / 2) := by ring
      _ ≤ ‖(N n : ℂ)‖ * ‖g n‖ * ‖g n‖ * 1 :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = ‖(N n : ℂ) * g n‖ * ‖g n‖ := by rw [norm_mul]; ring
  have hdiff : Tendsto (fun n => (N n : ℂ) * (log (1 + g n) - g n)) atTop (𝓝 0) := by
    refine squeeze_zero_norm' hbound ?_
    have := hN.norm.mul hg.norm
    simpa using this
  have hlog : Tendsto (fun n => (N n : ℂ) * log (1 + g n)) atTop (𝓝 t) := by
    have : (fun n => (N n : ℂ) * log (1 + g n))
        = fun n => (N n : ℂ) * g n + (N n : ℂ) * (log (1 + g n) - g n) := by
      funext n; ring
    rw [this]
    simpa using hN.add hdiff
  exact (Complex.continuous_exp.tendsto t |>.comp hlog).congr' (hrepr.mono fun n hn => hn.symm)

/-! ### Cramér–Wold scaling and the Taylor expansion -/

variable {ι : Type*} [Fintype ι]
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

/-- Cramér–Wold scaling: `φ_X(s • t) = φ_{⟪t, X⟫}(s)`. -/
theorem charFun_map_smul_eq {X : Ω → EuclideanSpace ℝ ι} (hX : AEMeasurable X P)
    (s : ℝ) (t : EuclideanSpace ℝ ι) :
    charFun (P.map X) (s • t) = charFun (P.map fun ω => ⟪t, X ω⟫_ℝ) s := by
  rw [charFun_map_eq_charFun_inner hX (s • t)]
  have hXt : AEMeasurable (fun ω => ⟪t, X ω⟫_ℝ) P := hX.const_inner
  have : (fun ω => ⟪s • t, X ω⟫_ℝ) = fun ω => s * ⟪t, X ω⟫_ℝ := by
    funext ω
    rw [real_inner_smul_left]
  rw [this, charFun_map_mul_comp hXt s 1, mul_one]

/-- The characteristic function of an a.e.-zero variable is `1`. -/
theorem charFun_map_eq_one_of_ae_zero {ξ : Ω → ℝ} (hξ : AEMeasurable ξ P) (h : ξ =ᵐ[P] 0)
    (s : ℝ) : charFun (P.map ξ) s = 1 := by
  rw [charFun_apply_real, integral_map hξ (by fun_prop)]
  have : (fun ω => exp ((s : ℂ) * (ξ ω : ℂ) * I)) =ᵐ[P] fun _ => (1 : ℂ) := by
    filter_upwards [h] with ω hω
    simp [hω]
  rw [integral_congr_ae this]
  simp

/-- **Second-order Taylor expansion** of the projected characteristic function:
`φ_{⟪t, X⟫}(s) = 1 - (tᵀ S t) s² / 2 + o(s²)` at `s = 0`. -/
theorem taylor_charFun_inner {X : Ω → EuclideanSpace ℝ ι} (hX : MemLp X 2 P) (h0 : P[X] = 0)
    (t : EuclideanSpace ℝ ι) :
    (fun s : ℝ => charFun (P.map fun ω => ⟪t, X ω⟫_ℝ) s
        - (1 - ((t ⬝ᵥ covMatrix X P *ᵥ t : ℝ) : ℂ) * (s : ℂ) ^ 2 / 2))
      =o[𝓝 0] fun s : ℝ => s ^ 2 := by
  set ξ : Ω → ℝ := fun ω => ⟪t, X ω⟫_ℝ with hξ
  set v : ℝ := t ⬝ᵥ covMatrix X P *ᵥ t with hv
  have hξL2 : MemLp ξ 2 P := hX.const_inner (𝕜 := ℝ) t
  have hξmeas : AEMeasurable ξ P := hξL2.aemeasurable
  have hξ0 : P[ξ] = 0 := integral_inner_eq_zero (hX.integrable (by norm_num)) h0 t
  have hξvar : Var[ξ; P] = v := variance_inner hX h0 t
  by_cases hv0 : v = 0
  · -- degenerate direction: the projection vanishes a.e.
    have hae : ξ =ᵐ[P] 0 := by
      have := ae_eq_integral_of_variance_eq_zero hξL2 (hξvar.trans hv0)
      filter_upwards [this] with ω hω
      rw [hω, hξ0]
      rfl
    refine (isLittleO_zero _ _).congr' (Eventually.of_forall fun s => ?_)
      (Eventually.of_forall fun s => rfl)
    beta_reduce
    rw [charFun_map_eq_one_of_ae_zero hξmeas hae, hv0]
    simp
  · have hvpos : 0 < v := lt_of_le_of_ne (hξvar ▸ variance_nonneg _ _) (Ne.symm hv0)
    have hsv : 0 < Real.sqrt v := Real.sqrt_pos.mpr hvpos
    -- normalise to unit variance
    set ξ' : Ω → ℝ := fun ω => (Real.sqrt v)⁻¹ * ξ ω with hξ'
    have hξ'L2 : MemLp ξ' 2 P := MemLp.const_mul hξL2 _
    have hξ'meas : AEMeasurable ξ' P := hξ'L2.aemeasurable
    have hξ'0 : P[ξ'] = 0 := by
      simp only [hξ', integral_const_mul, hξ0, mul_zero]
    have hξ'1 : P[ξ' ^ 2] = 1 := by
      have : (ξ' ^ 2) = fun ω => v⁻¹ * ξ ω ^ 2 := by
        funext ω
        simp only [hξ', Pi.pow_apply, mul_pow, inv_pow, Real.sq_sqrt hvpos.le]
      rw [this, integral_const_mul, ← variance_of_integral_eq_zero hξmeas hξ0, hξvar,
        inv_mul_cancel₀ hv0]
    have hT := taylor_charFun_two hξ'meas hξ'0 hξ'1
    -- `ξ = √v * ξ'`
    have hξeq : ξ = fun ω => Real.sqrt v * ξ' ω := by
      funext ω
      simp only [hξ']
      rw [mul_inv_cancel_left₀ hsv.ne']
    have hscale : ∀ s : ℝ, charFun (P.map ξ) s = charFun (P.map ξ') (Real.sqrt v * s) := by
      intro s
      conv_lhs => rw [hξeq]
      exact charFun_map_mul_comp hξ'meas _ s
    have hu : Tendsto (fun s : ℝ => Real.sqrt v * s) (𝓝 0) (𝓝 0) := by
      have hc : Continuous fun s : ℝ => Real.sqrt v * s := continuous_const.mul continuous_id
      have := hc.tendsto 0
      simpa using this
    have hcomp := hT.comp_tendsto hu
    -- rewrite the composed expansion
    have hleft : (fun s : ℝ => charFun (P.map ξ') (Real.sqrt v * s)
        - (1 - ((Real.sqrt v * s : ℝ) : ℂ) ^ 2 / 2))
        = fun s : ℝ => charFun (P.map ξ) s - (1 - (v : ℂ) * (s : ℂ) ^ 2 / 2) := by
      funext s
      rw [hscale s]
      congr 2
      push_cast
      rw [mul_pow, ← Complex.ofReal_pow, Real.sq_sqrt hvpos.le]
    have hright : (fun s : ℝ => (Real.sqrt v * s) ^ 2) = fun s : ℝ => v * s ^ 2 := by
      funext s
      rw [mul_pow, Real.sq_sqrt hvpos.le]
    simp only [Function.comp_def] at hcomp
    rw [hleft, hright] at hcomp
    exact hcomp.of_const_mul_right

/-! ### Block sums -/

/-- The characteristic function of a scaled block sum of i.i.d. vectors is a power of the
single-term characteristic function. -/
theorem charFun_block_sum {X : ℕ → Ω → EuclideanSpace ℝ ι} (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) (a b : ℕ) (r : ℝ) (t : EuclideanSpace ℝ ι) :
    charFun (P.map fun ω => r • ∑ k ∈ Finset.Ico a b, X k ω) t
      = charFun (P.map (X 0)) (r • t) ^ (b - a) := by
  have hmeas : ∀ k, AEMeasurable (X k) P := fun k => (hident k).aemeasurable_fst
  rw [charFun_map_smul_comp (Finset.aemeasurable_fun_sum _ fun k _ => hmeas k) r t,
    (hindep.restrict _).charFun_map_fun_finsetSum_eq_prod (fun k _ => hmeas k)]
  simp [fun i => (hident i).map_eq]

/-- `((√n)⁻¹)² = 1 / n` (also at `n = 0` by Lean's conventions). -/
theorem inv_sqrt_sq (n : ℕ) : ((√(n : ℝ))⁻¹) ^ 2 = 1 / (n : ℝ) := by
  rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg n), one_div]

theorem tendsto_inv_sqrt : Tendsto (fun n : ℕ => (√(n : ℝ))⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)

/-- **Block limit**: a block of `N n = b n - a n ~ c n` i.i.d. centred terms scaled by `n^{-1/2}`
has characteristic functions converging to those of `N(0, c S)`. -/
theorem tendsto_charFun_block_sum {X : ℕ → Ω → EuclideanSpace ℝ ι} (hX : MemLp (X 0) 2 P)
    (h0 : P[X 0] = 0) (hindep : iIndepFun X P) (hident : ∀ i, IdentDistrib (X i) (X 0) P P)
    (a b : ℕ → ℕ) (c : ℝ) (hc : Tendsto (fun n => ((b n - a n : ℕ) : ℝ) / n) atTop (𝓝 c))
    (t : EuclideanSpace ℝ ι) :
    Tendsto (fun n : ℕ =>
        charFun (P.map fun ω => (√(n : ℝ))⁻¹ • ∑ k ∈ Finset.Ico (a n) (b n), X k ω) t)
      atTop (𝓝 (exp (-((c * (t ⬝ᵥ covMatrix (X 0) P *ᵥ t) : ℝ) : ℂ) / 2))) := by
  set v : ℝ := t ⬝ᵥ covMatrix (X 0) P *ᵥ t with hv
  have hmeas0 : AEMeasurable (X 0) P := hX.aemeasurable
  set φ : ℝ → ℂ := charFun (P.map fun ω => ⟪t, X 0 ω⟫_ℝ) with hφ
  set g : ℕ → ℂ := fun n => φ ((√(n : ℝ))⁻¹) - 1 with hg
  -- the block characteristic function is a power
  have hpow : ∀ n : ℕ,
      charFun (P.map fun ω => (√(n : ℝ))⁻¹ • ∑ k ∈ Finset.Ico (a n) (b n), X k ω) t
        = (1 + g n) ^ (b n - a n) := by
    intro n
    rw [charFun_block_sum hindep hident, charFun_map_smul_eq hmeas0]
    simp [hg, hφ]
  simp_rw [hpow]
  -- `g n → 0`
  have hg0 : Tendsto g atTop (𝓝 0) := by
    have hcont : Continuous φ := continuous_charFun
    have := (hcont.tendsto 0).comp tendsto_inv_sqrt
    have h1 : φ 0 = 1 := by
      haveI : IsProbabilityMeasure (P.map fun ω => ⟪t, X 0 ω⟫_ℝ) :=
        Measure.isProbabilityMeasure_map hmeas0.const_inner
      simp [hφ]
    rw [h1] at this
    have := this.sub_const 1
    simpa [hg, Function.comp_def] using this
  -- `n * g n → -v/2`
  have hT := (taylor_charFun_inner hX h0 t).comp_tendsto tendsto_inv_sqrt
  have hTn : Tendsto (fun n : ℕ => (n : ℂ) * g n) atTop (𝓝 (-(v : ℂ) / 2)) := by
    have h1 := hT.tendsto_inv_smul_nhds_zero
    have hfun : ∀ n : ℕ, 1 ≤ n →
        (((√(n : ℝ))⁻¹) ^ 2)⁻¹ • (φ ((√(n : ℝ))⁻¹)
          - (1 - (v : ℂ) * (((√(n : ℝ))⁻¹ : ℝ) : ℂ) ^ 2 / 2))
          = (n : ℂ) * g n + (v : ℂ) / 2 := by
      intro n hn
      have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hn)
      rw [← Complex.ofReal_pow, inv_sqrt_sq, one_div, inv_inv, Complex.real_smul]
      simp only [hg]
      push_cast
      field_simp
      ring
    have h2 : Tendsto (fun n : ℕ => (n : ℂ) * g n + (v : ℂ) / 2) atTop (𝓝 0) := by
      refine h1.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      simpa [Function.comp_def] using hfun n hn
    have := h2.sub_const ((v : ℂ) / 2)
    simp only [add_sub_cancel_right, zero_sub] at this
    simpa [neg_div] using this
  -- `N n * g n → c * (-v/2)`
  have hN : Tendsto (fun n : ℕ => ((b n - a n : ℕ) : ℂ) * g n) atTop
      (𝓝 ((c : ℂ) * (-(v : ℂ) / 2))) := by
    have hcC : Tendsto (fun n : ℕ => ((((b n - a n : ℕ) : ℝ) / (n : ℝ) : ℝ) : ℂ)) atTop
        (𝓝 (c : ℂ)) :=
      (Complex.continuous_ofReal.tendsto c).comp hc
    have := hcC.mul hTn
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.one_le_iff_ne_zero.mp hn)
    change (((((b n - a n : ℕ) : ℝ) / (n : ℝ) : ℝ) : ℂ)) * ((n : ℂ) * g n)
      = ((b n - a n : ℕ) : ℂ) * g n
    push_cast
    rw [div_mul_eq_mul_div, mul_div_assoc, mul_div_cancel_left₀ _ hn']
  have := tendsto_one_add_pow_exp_of_tendsto_mul g (fun n => b n - a n) _ hg0 hN
  convert this using 3
  push_cast
  ring

/-! ### Joint block sums and finite-dimensional distributions -/

variable {J : Type*} [Fintype J]

/-- The disjoint union of the blocks `Ico (a j) (b j)`, as a finset of the sigma type. -/
def blockUnion (a b : J → ℕ) : Finset (Σ _ : J, ℕ) :=
  Finset.univ.sigma fun j => Finset.Ico (a j) (b j)

theorem mem_blockUnion {a b : J → ℕ} {u : Σ _ : J, ℕ} :
    u ∈ blockUnion a b ↔ u.2 ∈ Finset.Ico (a u.1) (b u.1) := by
  simp [blockUnion]

/-- The index projection of the block union is injective for pairwise disjoint blocks. -/
theorem blockUnion_snd_injective {a b : J → ℕ}
    (hdisj : Pairwise fun j j' => Disjoint (Finset.Ico (a j) (b j)) (Finset.Ico (a j') (b j'))) :
    Function.Injective fun u : blockUnion a b => u.1.2 := by
  rintro ⟨⟨j, k⟩, hu⟩ ⟨⟨j', k'⟩, hv⟩ h
  simp only at h
  subst h
  have hk : k ∈ Finset.Ico (a j) (b j) := mem_blockUnion.mp hu
  have hk' : k ∈ Finset.Ico (a j') (b j') := mem_blockUnion.mp hv
  have hjj : j = j' := by
    by_contra hne
    exact Finset.disjoint_left.mp (hdisj hne) hk hk'
  subst hjj
  rfl

/-- **Joint factorization**: for pairwise disjoint blocks the characteristic function of the
vector of scaled block sums is the product of the single-term characteristic functions. -/
theorem charFun_jointBlocks {X : ℕ → Ω → EuclideanSpace ℝ ι} (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) (a b : J → ℕ)
    (hdisj : Pairwise fun j j' => Disjoint (Finset.Ico (a j) (b j)) (Finset.Ico (a j') (b j')))
    (r : ℝ) (s : PiLp 2 (fun _ : J => EuclideanSpace ℝ ι)) :
    charFun (P.map fun ω => (WithLp.toLp 2 fun j => r • ∑ k ∈ Finset.Ico (a j) (b j), X k ω :
        PiLp 2 (fun _ : J => EuclideanSpace ℝ ι))) s
      = ∏ j, charFun (P.map (X 0)) (r • s j) ^ (b j - a j) := by
  have hmeas : ∀ k, AEMeasurable (X k) P := fun k => (hident k).aemeasurable_fst
  -- the independent scalar family indexed by the block union
  set U := blockUnion a b with hU
  set W : (Σ _ : J, ℕ) → Ω → ℝ := fun u ω => r * ⟪s u.1, X u.2 ω⟫_ℝ with hW
  have hWindep : iIndepFun (fun u : U => W u.1) P := by
    have h1 := hindep.precomp (blockUnion_snd_injective hdisj)
    exact h1.comp (fun u x => r * ⟪s u.1.1, x⟫_ℝ) (fun u => by fun_prop)
  have hWmeas : ∀ u : U, AEMeasurable (W u.1) P :=
    fun u => ((hmeas _).const_inner).const_mul r
  -- the joint characteristic function is the characteristic function of `∑ W`
  have hZmeas : AEMeasurable (fun ω => (WithLp.toLp 2 fun j => r • ∑ k ∈ Finset.Ico (a j) (b j),
      X k ω : PiLp 2 (fun _ : J => EuclideanSpace ℝ ι))) P := by fun_prop
  have hsum : ∀ ω, ⟪(WithLp.toLp 2 fun j => r • ∑ k ∈ Finset.Ico (a j) (b j), X k ω :
      PiLp 2 (fun _ : J => EuclideanSpace ℝ ι)), s⟫_ℝ = ∑ u : U, W u.1 ω := by
    intro ω
    rw [PiLp.inner_apply, Finset.sum_coe_sort U (fun u => W u ω)]
    simp only [hU, blockUnion, Finset.sum_sigma]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hW, real_inner_smul_left, sum_inner, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [real_inner_comm]
  have hjoint : charFun (P.map fun ω => (WithLp.toLp 2 fun j => r • ∑ k ∈ Finset.Ico (a j) (b j),
      X k ω : PiLp 2 (fun _ : J => EuclideanSpace ℝ ι))) s
      = charFun (P.map fun ω => ∑ u : U, W u.1 ω) 1 := by
    rw [charFun_apply, charFun_apply_real,
      integral_map (f := fun x : PiLp 2 (fun _ : J => EuclideanSpace ℝ ι) => exp (⟪x, s⟫_ℝ * I))
        hZmeas (by fun_prop),
      integral_map (f := fun x : ℝ => exp (((1 : ℝ) : ℂ) * (x : ℂ) * I))
        (Finset.aemeasurable_fun_sum _ fun u _ => hWmeas u) (by fun_prop)]
    congr 1
    funext ω
    rw [hsum ω]
    simp
  rw [hjoint, congrFun (hWindep.charFun_map_fun_sum_eq_prod hWmeas) 1, Finset.prod_apply]
  -- each factor
  have hfactor : ∀ u : U, charFun (P.map (W u.1)) 1 = charFun (P.map (X 0)) (r • s u.1.1) := by
    intro u
    simp only [hW]
    rw [charFun_map_mul_comp (hmeas _).const_inner r 1, mul_one, ← charFun_map_smul_eq (hmeas _),
      (hident _).map_eq]
  simp_rw [hfactor]
  rw [Finset.prod_coe_sort U (fun u => charFun (P.map (X 0)) (r • s u.1))]
  simp only [hU, blockUnion, Finset.prod_sigma]
  refine Finset.prod_congr rfl fun j _ => ?_
  simp

/-- **Finite-dimensional Donsker limit for block increments.** For i.i.d. centred
square-integrable vectors, pairwise disjoint blocks of sizes `~ Δ_j n`, and a random vector `Y`
with independent centred Gaussian coordinates of covariances `Δ_j • S`, the joint vector of
scaled block sums converges in distribution to `Y`. -/
theorem tendstoInDistribution_jointBlocks [DecidableEq ι] {Ω' : Type*} {mΩ' : MeasurableSpace Ω'}
    {P' : Measure Ω'} [IsProbabilityMeasure P'] {X : ℕ → Ω → EuclideanSpace ℝ ι}
    (hX : MemLp (X 0) 2 P) (h0 : P[X 0] = 0) (hindep : iIndepFun X P)
    (hident : ∀ i, IdentDistrib (X i) (X 0) P P) (a b : ℕ → J → ℕ)
    (hdisj : ∀ n, Pairwise fun j j' =>
      Disjoint (Finset.Ico (a n j) (b n j)) (Finset.Ico (a n j') (b n j')))
    (Δ : J → ℝ) (hΔ : ∀ j, Tendsto (fun n => ((b n j - a n j : ℕ) : ℝ) / n) atTop (𝓝 (Δ j)))
    {Y : Ω' → PiLp 2 (fun _ : J => EuclideanSpace ℝ ι)} (hYmeas : AEMeasurable Y P')
    (hYindep : iIndepFun (fun j ω => Y ω j) P')
    (hYlaw : ∀ j, HasLaw (fun ω => Y ω j) (multivariateGaussian 0 (Δ j • covMatrix (X 0) P)) P') :
    TendstoInDistribution
      (fun (n : ℕ) ω => (WithLp.toLp 2 fun j => (√(n : ℝ))⁻¹ • ∑ k ∈ Finset.Ico (a n j) (b n j),
        X k ω : PiLp 2 (fun _ : J => EuclideanSpace ℝ ι))) atTop Y (fun _ => P) P' := by
  have hmeas : ∀ k, AEMeasurable (X k) P := fun k => (hident k).aemeasurable_fst
  have hΔ0 : ∀ j, 0 ≤ Δ j := fun j => ge_of_tendsto' (hΔ j) fun n => by positivity
  have hS := covMatrix_posSemidef hX
  refine ⟨fun n => by fun_prop, hYmeas, ?_⟩
  refine ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 fun s => ?_
  -- prelimit: product of block characteristic functions
  have hL : ∀ n : ℕ, charFun (P.map fun ω => (WithLp.toLp 2 fun j =>
      (√(n : ℝ))⁻¹ • ∑ k ∈ Finset.Ico (a n j) (b n j), X k ω :
        PiLp 2 (fun _ : J => EuclideanSpace ℝ ι))) s
      = ∏ j, charFun (P.map fun ω => (√(n : ℝ))⁻¹ • ∑ k ∈ Finset.Ico (a n j) (b n j), X k ω)
          (s j) := by
    intro n
    rw [charFun_jointBlocks hindep hident (a n) (b n) (hdisj n)]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [charFun_block_sum hindep hident]
  -- limit: product of Gaussian characteristic functions
  have hR : charFun (P'.map Y) s
      = ∏ j, exp (-((Δ j * (s j ⬝ᵥ covMatrix (X 0) P *ᵥ s j) : ℝ) : ℂ) / 2) := by
    have hY' : Y = fun ω => WithLp.toLp 2 fun j => Y ω j := by
      funext ω
      simp
    have hcoord : ∀ j, AEMeasurable (fun ω => Y ω j) P' := fun j => (hYlaw j).aemeasurable
    rw [hY', (iIndepFun_iff_charFun_pi hcoord).mp hYindep s]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [(hYlaw j).map_eq, charFun_multivariateGaussian (hS.smul (hΔ0 j))]
    congr 1
    have hsc : s j ⬝ᵥ (Δ j • covMatrix (X 0) P) *ᵥ s j
        = Δ j * (s j ⬝ᵥ covMatrix (X 0) P *ᵥ s j) := by
      rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    rw [hsc]
    simp only [inner_zero_right, Complex.ofReal_zero, zero_mul, zero_sub]
    push_cast
    ring
  simp only [ProbabilityMeasure.coe_mk]
  rw [hR]
  simp_rw [hL]
  exact tendsto_finsetProd _ fun j _ =>
    tendsto_charFun_block_sum hX h0 hindep hident (fun n => a n j) (fun n => b n j) (Δ j) (hΔ j)
      (s j)

end DonskerFiniteDimensional
end NCG
