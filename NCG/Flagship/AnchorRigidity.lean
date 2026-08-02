/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Flagship.StoreAutocorrelation

/-!
# Anchor-return rigidity
  (`thm:anchor-return-rigidity-master`, flagship manuscript)

For a centered self-adjoint generator `H` with unit anchor `Ω`
(`⟨Ω, HΩ⟩ = 0`) and moments `μ_n = ⟨Ω, HⁿΩ⟩`:

* the boxed gap identity `μ₄ - μ₂² = ‖(H² - μ₂)Ω‖² ≥ 0`
  (`anchor_moment_gap`; `μ₂ = ‖HΩ‖²`, `μ₄ = ‖H²Ω‖²` by
  self-adjointness);
* the binary return identity `μ₄ = μ₂²` holds iff `H²Ω = μ₂Ω`
  (`anchor_return_flat_iff`);
* under `H²Ω = ν²Ω`, `ν > 0`, the pair `e₀ = Ω`,
  `e₁ = ν⁻¹HΩ` is orthonormal with `He₀ = νe₁`, `He₁ = νe₀`
  (the σₓ-matrix on the minimal carrier `W ≅ ℂ²`), and the boxed
  return law `⟨Ω, e^{-itH}Ω⟩ = cos(νt)`, `p(t) = cos²(νt)` holds
  (`anchor_return_amplitude`, `anchor_return_probability`) via the
  even/odd split of the exponential series;
* the derivative normalizations `p''(0) = -2ν² = -2μ₂` and
  `p⁗(0) = 8ν⁴ = 2μ₄ + 6μ₂² = 2p''(0)²` are verified on the
  certified profile (`anchor_jet_second`, `anchor_jet_fourth`).

The manuscript's hypotheses `p''(0) < 0`, `p⁗(0) = 2p''(0)²` enter
in exact moment form (`‖HΩ‖ = ν > 0`, `‖H²Ω‖² = ‖HΩ‖⁴`), which the
jet lemmas identify with the derivative form on the certified
profile (disclosed).  Uniqueness up to the source-fixing unitary
and a scalar phase is prose.
-/

open NormedSpace

namespace NCG

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

omit [CompleteSpace E] in
/-- Even powers on the anchor line. -/
lemma pow_even_applyC (H : E →L[ℂ] E) (v : E) (c : ℂ)
    (hv : H (H v) = c • v) (k : ℕ) :
    (H ^ (2 * k)) v = c ^ k • v := by
  induction k with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 2 by ring, pow_add]
    have happ : (H ^ (2 * m) * H ^ 2) v = (H ^ (2 * m)) ((H ^ 2) v) :=
      rfl
    have h2 : (H ^ 2) v = c • v := by
      rw [pow_two]
      exact hv
    rw [happ, h2, map_smul, ih, smul_smul, ← pow_succ']

omit [CompleteSpace E] in
/-- Odd powers on the anchor line. -/
lemma pow_odd_applyC (H : E →L[ℂ] E) (v : E) (c : ℂ)
    (hv : H (H v) = c • v) (k : ℕ) :
    (H ^ (2 * k + 1)) v = c ^ k • H v := by
  have hHv : H (H (H v)) = c • H v := by
    rw [hv, map_smul]
  have happ : (H ^ (2 * k + 1)) v = (H ^ (2 * k)) (H v) := by
    rw [pow_succ]
    rfl
  rw [happ, pow_even_applyC H (H v) c hHv k]

omit [CompleteSpace E] in
/-- `thm:anchor-return-rigidity-master`, boxed gap identity:
`μ₄ - μ₂² = ‖(H² - μ₂)Ω‖²` for the centered moments
`μ₂ = ‖HΩ‖²`, `μ₄ = ‖H²Ω‖²`. -/
lemma anchor_moment_gap (H : E →L[ℂ] E) (Ω : E) (hΩ : ‖Ω‖ = 1)
    (hsa : ∀ x y, inner ℂ (H x) y = inner ℂ x (H y)) :
    ‖H (H Ω) - ((‖H Ω‖ : ℂ) ^ 2) • Ω‖ ^ 2
      = ‖H (H Ω)‖ ^ 2 - ‖H Ω‖ ^ 4 := by
  have hx : inner ℂ (H (H Ω)) Ω = ((‖H Ω‖ : ℂ)) ^ 2 := by
    rw [hsa (H Ω) Ω, inner_self_eq_norm_sq_to_K,
      RCLike.ofReal_eq_complex_ofReal]
  have hsub := norm_sub_sq (𝕜 := ℂ) (H (H Ω))
    (((‖H Ω‖ : ℂ) ^ 2) • Ω)
  rw [inner_smul_right, hx] at hsub
  have hre : RCLike.re (K := ℂ)
      (((‖H Ω‖ : ℂ) ^ 2) * ((‖H Ω‖ : ℂ)) ^ 2) = ‖H Ω‖ ^ 4 := by
    rw [show ((‖H Ω‖ : ℂ) ^ 2) * ((‖H Ω‖ : ℂ)) ^ 2
      = ((‖H Ω‖ ^ 4 : ℝ) : ℂ) by push_cast; ring]
    simp only [RCLike.re_to_complex, Complex.ofReal_re]
  rw [hre, norm_smul, hΩ, mul_one, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (H Ω))] at hsub
  have hp : (‖H Ω‖ ^ 2) ^ 2 = ‖H Ω‖ ^ 4 := by ring
  rw [hp] at hsub
  linarith

omit [CompleteSpace E] in
/-- `thm:anchor-return-rigidity-master`, binary return
equivalence: `μ₄ = μ₂²` iff `H²Ω = μ₂Ω`. -/
theorem anchor_return_flat_iff (H : E →L[ℂ] E) (Ω : E)
    (hΩ : ‖Ω‖ = 1)
    (hsa : ∀ x y, inner ℂ (H x) y = inner ℂ x (H y)) :
    ‖H (H Ω)‖ ^ 2 = ‖H Ω‖ ^ 4
      ↔ H (H Ω) = ((‖H Ω‖ : ℂ) ^ 2) • Ω := by
  constructor
  · intro hflat
    have h := anchor_moment_gap H Ω hΩ hsa
    rw [hflat, sub_self] at h
    have h0 : ‖H (H Ω) - ((‖H Ω‖ : ℂ) ^ 2) • Ω‖ = 0 :=
      pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
    rw [norm_eq_zero, sub_eq_zero] at h0
    exact h0
  · intro heq
    rw [heq, norm_smul, hΩ, mul_one, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (norm_nonneg (H Ω))]
    ring

omit [CompleteSpace E] in
/-- The transverse unit `e₁ = ν⁻¹HΩ`: normalization. -/
lemma anchor_transverse_norm (H : E →L[ℂ] E) (Ω : E) (ν : ℝ)
    (hν : 0 < ν) (hsa : ∀ x y, inner ℂ (H x) y = inner ℂ x (H y))
    (hΩ : ‖Ω‖ = 1) (heig : H (H Ω) = ((ν : ℂ) ^ 2) • Ω) :
    ‖((ν : ℂ))⁻¹ • H Ω‖ = 1 := by
  have hnrm : ‖H Ω‖ = ν := by
    have h1 : inner ℂ (H Ω) (H Ω) = ((ν ^ 2 : ℝ) : ℂ) := by
      rw [hsa Ω (H Ω), heig, inner_smul_right,
        inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal,
        hΩ]
      push_cast
      ring
    rw [inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal]
      at h1
    have h2 : ‖H Ω‖ ^ 2 = ν ^ 2 := by exact_mod_cast h1
    rw [← Real.sqrt_sq (norm_nonneg (H Ω)), h2, Real.sqrt_sq hν.le]
  rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hν, hnrm]
  field_simp

omit [CompleteSpace E] in
/-- The transverse unit is orthogonal to the anchor. -/
lemma anchor_transverse_orth (H : E →L[ℂ] E) (Ω : E) (ν : ℝ)
    (hμ1 : inner ℂ Ω (H Ω) = 0) :
    inner ℂ Ω (((ν : ℂ))⁻¹ • H Ω) = 0 := by
  rw [inner_smul_right, hμ1, mul_zero]

omit [CompleteSpace E] in
/-- The σₓ action on the minimal carrier: `He₁ = νΩ`. -/
lemma anchor_sigma_action (H : E →L[ℂ] E) (Ω : E) (ν : ℝ)
    (hν : 0 < ν) (heig : H (H Ω) = ((ν : ℂ) ^ 2) • Ω) :
    H (((ν : ℂ))⁻¹ • H Ω) = (ν : ℂ) • Ω := by
  have hν0 : ((ν : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr hν.ne'
  rw [map_smul, heig, smul_smul]
  congr 1
  field_simp

/-- `thm:anchor-return-rigidity-master`, boxed return amplitude:
`⟨Ω, e^{-itH}Ω⟩ = cos(νt)` on the binary carrier, via the even/odd
split of the exponential series. -/
theorem anchor_return_amplitude (H : E →L[ℂ] E) (Ω : E) (ν : ℝ)
    (hΩ : ‖Ω‖ = 1) (hμ1 : inner ℂ Ω (H Ω) = 0)
    (heig : H (H Ω) = ((ν : ℂ) ^ 2) • Ω) (t : ℝ) :
    inner ℂ Ω ((exp ((-(Complex.I * (t : ℂ))) • H)) Ω)
      = ((Real.cos (ν * t) : ℝ) : ℂ) := by
  set c : ℂ := -(Complex.I * (t : ℂ)) with hc
  have hΩΩ : inner ℂ Ω Ω = (1 : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal,
      hΩ]
    norm_num
  have hc2 : c ^ 2 = ((-(t ^ 2) : ℝ) : ℂ) := by
    rw [hc]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  have hs := exp_series_hasSum_exp' (𝕂 := ℂ) (c • H)
  have hsz := (ContinuousLinearMap.apply ℂ E Ω).hasSum hs
  have hsy := (innerSL ℂ Ω).hasSum hsz
  simp only [ContinuousLinearMap.apply_apply, innerSL_apply_apply]
    at hsy
  have hterm : ∀ n : ℕ,
      inner ℂ Ω ((((n.factorial : ℂ))⁻¹ • (c • H) ^ n) Ω)
        = ((n.factorial : ℂ))⁻¹ * c ^ n
          * inner ℂ Ω ((H ^ n) Ω) := by
    intro n
    rw [smul_pow, smul_smul,
      show (((((n.factorial : ℂ)))⁻¹ * c ^ n) • H ^ n) Ω
        = ((((n.factorial : ℂ)))⁻¹ * c ^ n) • (H ^ n) Ω from rfl,
      inner_smul_right]
  have heven : HasSum
      (fun k : ℕ =>
        inner ℂ Ω (((((2 * k).factorial : ℂ))⁻¹
          • (c • H) ^ (2 * k)) Ω))
      ((Real.cos (ν * t) : ℝ) : ℂ) := by
    have hfe : (fun k : ℕ =>
        inner ℂ Ω (((((2 * k).factorial : ℂ))⁻¹
          • (c • H) ^ (2 * k)) Ω))
        = fun k => (((-1) ^ k * (ν * t) ^ (2 * k)
            / ((2 * k).factorial : ℝ) : ℝ) : ℂ) := by
      funext k
      rw [hterm (2 * k), pow_even_applyC H Ω ((ν : ℂ) ^ 2) heig k,
        inner_smul_right, hΩΩ, pow_mul c 2 k, hc2]
      push_cast
      ring
    rw [hfe]
    exact Complex.ofRealCLM.hasSum (Real.hasSum_cos (ν * t))
  have hodd : HasSum
      (fun k : ℕ =>
        inner ℂ Ω (((((2 * k + 1).factorial : ℂ))⁻¹
          • (c • H) ^ (2 * k + 1)) Ω)) 0 := by
    have hfe : (fun k : ℕ =>
        inner ℂ Ω (((((2 * k + 1).factorial : ℂ))⁻¹
          • (c • H) ^ (2 * k + 1)) Ω))
        = fun _ => (0 : ℂ) := by
      funext k
      rw [hterm (2 * k + 1), pow_odd_applyC H Ω ((ν : ℂ) ^ 2) heig k,
        inner_smul_right, hμ1]
      ring
    rw [hfe]
    exact hasSum_zero
  have hcombined := HasSum.even_add_odd
    (f := fun n : ℕ =>
      inner ℂ Ω ((((n.factorial : ℂ))⁻¹ • (c • H) ^ n) Ω))
    heven hodd
  rw [add_zero] at hcombined
  exact hsy.unique hcombined

/-- `thm:anchor-return-rigidity-master`, boxed return law:
`p(t) = cos²(νt)`. -/
theorem anchor_return_probability (H : E →L[ℂ] E) (Ω : E) (ν : ℝ)
    (hΩ : ‖Ω‖ = 1) (hμ1 : inner ℂ Ω (H Ω) = 0)
    (heig : H (H Ω) = ((ν : ℂ) ^ 2) • Ω) (t : ℝ) :
    ‖inner ℂ Ω ((exp ((-(Complex.I * (t : ℂ))) • H)) Ω)‖ ^ 2
      = Real.cos (ν * t) ^ 2 := by
  rw [anchor_return_amplitude H Ω ν hΩ hμ1 heig t,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-! ### Jet normalization of the certified return profile -/

/-- The certified profile as a two-term cosine family. -/
lemma cos_sq_as_family (ν : ℝ) :
    (fun t => Real.cos (ν * t) ^ 2)
      = fun t => ∑ j : Fin 2,
          (![(1 : ℝ) / 2, 1 / 2] j)
            * Real.cos ((![0, 2 * ν] j) * t) := by
  funext t
  rw [Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [Real.cos_sq, zero_mul, Real.cos_zero,
    show 2 * ν * t = 2 * (ν * t) by ring]
  ring

/-- `p''(0) = -2ν² = -2μ₂` on the certified profile. -/
theorem anchor_jet_second (ν : ℝ) :
    iteratedDeriv 2 (fun t => Real.cos (ν * t) ^ 2) 0
      = -2 * ν ^ 2 := by
  have h := iteratedDeriv_even_cos_family (s := 2) 1
    ![(1 : ℝ) / 2, 1 / 2] ![0, 2 * ν]
  rw [show 2 * 1 = 2 by norm_num] at h
  rw [cos_sq_as_family, h]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, mul_zero, Real.cos_zero]
  ring

/-- `p⁗(0) = 8ν⁴ = 2μ₄ + 6μ₂² = 2p''(0)²` on the certified
profile: the binary return identity. -/
theorem anchor_jet_fourth (ν : ℝ) :
    iteratedDeriv 4 (fun t => Real.cos (ν * t) ^ 2) 0
      = 8 * ν ^ 4 := by
  have h := iteratedDeriv_even_cos_family (s := 2) 2
    ![(1 : ℝ) / 2, 1 / 2] ![0, 2 * ν]
  rw [show 2 * 2 = 4 by norm_num] at h
  rw [cos_sq_as_family, h]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, mul_zero, Real.cos_zero]
  ring

/-- `thm:anchor-return-rigidity-master`, master bundle: under the
binary return identity in moment form (`‖H²Ω‖² = ‖HΩ‖⁴`,
`‖HΩ‖ = ν > 0`), the anchor line is `H²`-eigen, the pair
`(Ω, ν⁻¹HΩ)` is an orthonormal σₓ-carrier, and the return
amplitude and probability are exactly `cos(νt)`, `cos²(νt)`. -/
theorem anchor_return_rigidity (H : E →L[ℂ] E) (Ω : E) (ν : ℝ)
    (hΩ : ‖Ω‖ = 1)
    (hsa : ∀ x y, inner ℂ (H x) y = inner ℂ x (H y))
    (hμ1 : inner ℂ Ω (H Ω) = 0) (hν : 0 < ν)
    (hmom : ‖H Ω‖ = ν) (hflat : ‖H (H Ω)‖ ^ 2 = ‖H Ω‖ ^ 4) :
    H (H Ω) = ((ν : ℂ) ^ 2) • Ω
    ∧ ‖((ν : ℂ))⁻¹ • H Ω‖ = 1
    ∧ inner ℂ Ω (((ν : ℂ))⁻¹ • H Ω) = 0
    ∧ H (((ν : ℂ))⁻¹ • H Ω) = (ν : ℂ) • Ω
    ∧ (∀ t : ℝ,
        inner ℂ Ω ((exp ((-(Complex.I * (t : ℂ))) • H)) Ω)
          = ((Real.cos (ν * t) : ℝ) : ℂ))
    ∧ (∀ t : ℝ,
        ‖inner ℂ Ω ((exp ((-(Complex.I * (t : ℂ))) • H)) Ω)‖ ^ 2
          = Real.cos (ν * t) ^ 2) := by
  have heig : H (H Ω) = ((ν : ℂ) ^ 2) • Ω := by
    have h := (anchor_return_flat_iff H Ω hΩ hsa).mp hflat
    rw [hmom] at h
    exact h
  exact ⟨heig,
    anchor_transverse_norm H Ω ν hν hsa hΩ heig,
    anchor_transverse_orth H Ω ν hμ1,
    anchor_sigma_action H Ω ν hν heig,
    fun t => anchor_return_amplitude H Ω ν hΩ hμ1 heig t,
    fun t => anchor_return_probability H Ω ν hΩ hμ1 heig t⟩

end NCG
