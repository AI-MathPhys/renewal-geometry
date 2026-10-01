/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.VectorLineTaylorRemainderBound

/-!
# Two-endpoint Hermite interpolation of arbitrary odd degree in a normed space
(infrastructure for `lem:supp-open-hermite-residual`, `lem:supp-open-hermite-precision`,
`thm:supp-open-finite-words`; emergent-spacetime manuscript)

Let `E` be a real normed space and `k : ℕ`.  A polynomial map `ℝ → E` of degree at most
`2k+1` is `polyCurve c t = ∑_{i < 2k+2} tⁱ • cᵢ` with coefficients `c : Fin (2k+2) → E`.
Its *endpoint jet* is the family `(P⁽ʲ⁾(e))_{e ∈ {0,1}, j ≤ k}` (`jets`).

* `iteratedDeriv_polyCurve`: `P⁽ʲ⁾ = polyCurveDeriv j c`, the formal derivative
  `∑ᵢ i(i−1)⋯(i−j+1) t^{i−j} • cᵢ`.
* `jetMatrix_mulVec_injective`: (scalar uniqueness) a real polynomial of degree `≤ 2k+1` whose
  jets through order `k` vanish at `0` and `1` is zero (it is divisible by
  `X^{k+1}(X−1)^{k+1}`).
* `hermiteMatrix`, `jetMatrix_mul_hermiteMatrix`, `hermiteMatrix_mul_jetMatrix`: the inverse
  `(2k+2)×(2k+2)` real matrix of the jet map (the Hermite cardinal basis).
* `jets_hermiteCoeffs`, `hermiteCoeffs_jets`, `existsUnique_jets_eq`: **existence and
  uniqueness** of the `E`-valued interpolant: for every jet family `J` there is exactly one
  coefficient vector with `jets c = J`, namely `hermiteCoeffs J = N J` (componentwise).
* `norm_coeff_le`, `norm_polyCurveDeriv_le_unit`: **norm equivalence** with uniform explicit
  constants `hermiteConst k j` depending only on `k, j`:
  `sup_{[0,1]} ‖P⁽ʲ⁾‖ ≤ hermiteConst k j · max_{e,i≤k} ‖P⁽ⁱ⁾(e)‖`.
* `polyCurveDeriv_scaleCoeffs`, `norm_iteratedDeriv_polyCurve_le_scaled`: **τ-scaling**: on
  `[0,τ]`, `‖P⁽ʲ⁾(t)‖ ≤ hermiteConst k j · τ^{−j} · b` whenever
  `τⁱ ‖P⁽ⁱ⁾(eτ)‖ ≤ b` for `e ∈ {0,1}`, `i ≤ k`.  For `k = 3` (degree seven) this is the first
  clause of `lem:supp-open-hermite-precision` (`hermite_precision_degree_seven`).
* `hermiteCorrection` and `hermiteCorrection_jets`: the explicit degree-seven corrections
  `H₂(z) = −½ z⁴(z−1)²(4z−5)`, `H₃(z) = ⅙ z⁴(z−1)³` of `eq:supp-open-hermite-correction`:
  the curve `τ²δ₂H₂(t/τ) + τ³δ₃H₃(t/τ)` has zero jets through order three at `0` and the jet
  `(0, 0, δ₂, δ₃)` at `τ`.
* `hermiteInterpCoeffs`, `iteratedDeriv_hermiteInterp`, `norm_iteratedDeriv_sub_hermiteInterp_le`:
  the Hermite interpolant of a `C^{2k+2}` map `f : ℝ → E` on `[0,τ]` matches the jets of `f`
  through order `k` at `0` and `τ`, and (**Taylor–Hermite remainder**)
  `‖f⁽ʲ⁾(t) − P⁽ʲ⁾(t)‖ ≤ (1 + hermiteConst k j) · M · τ^{2k+2−j}` on `[0,τ]` for `j ≤ 2k+1`,
  where `M ≥ sup_{[0,τ]} ‖f^{(2k+2)}‖`.
-/

namespace RenewalGeometry.TwoPointHermite

open Polynomial Finset

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### Polynomial curves and their derivatives -/

/-- The polynomial curve `t ↦ ∑ᵢ tⁱ • cᵢ` (degree `< N`). -/
noncomputable def polyCurve {N : ℕ} (c : Fin N → E) (t : ℝ) : E :=
  ∑ i : Fin N, (t ^ (i : ℕ)) • c i

/-- The formal `j`-th derivative `∑ᵢ i(i−1)⋯(i−j+1) t^{i−j} • cᵢ`. -/
noncomputable def polyCurveDeriv {N : ℕ} (j : ℕ) (c : Fin N → E) (t : ℝ) : E :=
  ∑ i : Fin N, (((i : ℕ).descFactorial j : ℝ) * t ^ ((i : ℕ) - j)) • c i

theorem polyCurveDeriv_zero {N : ℕ} (c : Fin N → E) : polyCurveDeriv 0 c = polyCurve c := by
  funext t; simp [polyCurveDeriv, polyCurve]

theorem hasDerivAt_polyCurveDeriv {N : ℕ} (j : ℕ) (c : Fin N → E) (t : ℝ) :
    HasDerivAt (polyCurveDeriv j c) (polyCurveDeriv (j + 1) c t) t := by
  unfold polyCurveDeriv
  apply HasDerivAt.fun_sum
  intro i _
  have h := ((hasDerivAt_pow ((i : ℕ) - j) t).const_mul
    (((i : ℕ).descFactorial j : ℝ))).smul_const (c i)
  convert h using 2
  rw [Nat.descFactorial_succ, Nat.sub_sub]
  push_cast
  ring

theorem iteratedDeriv_polyCurve {N : ℕ} (c : Fin N → E) (j : ℕ) :
    iteratedDeriv j (polyCurve c) = polyCurveDeriv j c := by
  induction j with
  | zero => rw [iteratedDeriv_zero, polyCurveDeriv_zero]
  | succ j ih =>
      rw [iteratedDeriv_succ, ih]
      funext t
      exact (hasDerivAt_polyCurveDeriv j c t).deriv

theorem contDiff_polyCurve {N : ℕ} (c : Fin N → E) : ContDiff ℝ ⊤ (polyCurve c) := by
  unfold polyCurve
  fun_prop

/-! ### The scalar jet matrix and its inverse -/

/-- The jet matrix: row `(e, j)` evaluates the `j`-th derivative at the endpoint `e ∈ {0,1}`
on the monomial basis of degree `≤ 2k+1`. -/
noncomputable def jetMatrix (k : ℕ) : Matrix (Fin 2 × Fin (k + 1)) (Fin (2 * k + 2)) ℝ :=
  fun r i => ((i : ℕ).descFactorial (r.2 : ℕ) : ℝ) * (((r.1 : ℕ) : ℝ)) ^ ((i : ℕ) - r.2)

/-- The real polynomial with coefficient vector `a`. -/
noncomputable def coeffPoly {N : ℕ} (a : Fin N → ℝ) : ℝ[X] := ∑ i : Fin N, C (a i) * X ^ (i : ℕ)

theorem eval_iterate_derivative_coeffPoly {N : ℕ} (a : Fin N → ℝ) (j : ℕ) (x : ℝ) :
    (derivative^[j] (coeffPoly a)).eval x
      = ∑ i : Fin N, ((i : ℕ).descFactorial j : ℝ) * x ^ ((i : ℕ) - j) * a i := by
  unfold coeffPoly
  rw [iterate_derivative_sum, eval_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iterate_derivative_C_mul, iterate_derivative_X_pow_eq_C_mul]
  simp only [eval_mul, eval_C, eval_pow, eval_X]
  ring

theorem coeff_coeffPoly {N : ℕ} (a : Fin N → ℝ) (i : Fin N) : (coeffPoly a).coeff i = a i := by
  unfold coeffPoly
  rw [finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    rw [if_neg]
    intro h
    exact hb (Fin.ext h.symm)
  · intro h; exact absurd (Finset.mem_univ i) h

theorem natDegree_coeffPoly_le {N : ℕ} (a : Fin N → ℝ) : (coeffPoly a).natDegree ≤ N - 1 := by
  unfold coeffPoly
  refine natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
  refine (natDegree_C_mul_X_pow_le _ _).trans ?_
  have := i.2
  omega

/-- **Scalar uniqueness**: a real polynomial of degree `≤ 2k+1` whose jets through order `k`
vanish at both endpoints `0` and `1` is zero. -/
theorem jetMatrix_mulVec_eq_zero {k : ℕ} {a : Fin (2 * k + 2) → ℝ}
    (h : (jetMatrix k).mulVec a = 0) : a = 0 := by
  have hroot : ∀ e : Fin 2, ∀ m ≤ k, (derivative^[m] (coeffPoly a)).IsRoot ((e : ℕ) : ℝ) := by
    intro e m hm
    have := congrFun h (e, ⟨m, Nat.lt_succ_of_le hm⟩)
    simp only [Matrix.mulVec, dotProduct, jetMatrix, Pi.zero_apply] at this
    rw [IsRoot, eval_iterate_derivative_coeffPoly]
    exact this
  have hp : coeffPoly a = 0 := by
    by_contra hne
    have h0 := lt_rootMultiplicity_of_isRoot_iterate_derivative hne (hroot 0)
    have h1 := lt_rootMultiplicity_of_isRoot_iterate_derivative hne (hroot 1)
    simp only [Fin.val_zero, Nat.cast_zero, Fin.val_one, Nat.cast_one] at h0 h1
    have d0 : (X - C (0 : ℝ)) ^ (k + 1) ∣ coeffPoly a :=
      (pow_dvd_pow _ h0).trans (pow_rootMultiplicity_dvd _ _)
    have d1 : (X - C (1 : ℝ)) ^ (k + 1) ∣ coeffPoly a :=
      (pow_dvd_pow _ h1).trans (pow_rootMultiplicity_dvd _ _)
    have hcop : IsCoprime ((X - C (0 : ℝ)) ^ (k + 1)) ((X - C (1 : ℝ)) ^ (k + 1)) :=
      (isCoprime_X_sub_C_of_isUnit_sub (by norm_num)).pow
    have hd := natDegree_le_of_dvd (hcop.mul_dvd d0 d1) hne
    rw [natDegree_mul (pow_ne_zero _ (X_sub_C_ne_zero _)) (pow_ne_zero _ (X_sub_C_ne_zero _)),
      natDegree_pow, natDegree_pow, natDegree_X_sub_C, natDegree_X_sub_C] at hd
    have := natDegree_coeffPoly_le a
    omega
  funext i
  rw [← coeff_coeffPoly a i, hp, coeff_zero, Pi.zero_apply]

theorem jetMatrix_mulVec_injective (k : ℕ) : Function.Injective (jetMatrix k).mulVec := by
  intro a b h
  have : (jetMatrix k).mulVec (a - b) = 0 := by rw [Matrix.mulVec_sub, h, sub_self]
  exact sub_eq_zero.1 (jetMatrix_mulVec_eq_zero this)

/-- The jet map as a linear equivalence `ℝ^{2k+2} ≃ ℝ^{{0,1} × {0..k}}`. -/
noncomputable def jetEquiv (k : ℕ) : (Fin (2 * k + 2) → ℝ) ≃ₗ[ℝ] (Fin 2 × Fin (k + 1) → ℝ) :=
  LinearMap.linearEquivOfInjective (Matrix.toLin' (jetMatrix k))
    (by rw [Matrix.toLin'_apply']; exact jetMatrix_mulVec_injective k)
    (by simp; ring)

/-- The Hermite matrix, inverse of the jet matrix (its columns are the coefficient vectors of
the Hermite cardinal basis). -/
noncomputable def hermiteMatrix (k : ℕ) : Matrix (Fin (2 * k + 2)) (Fin 2 × Fin (k + 1)) ℝ :=
  LinearMap.toMatrix' (jetEquiv k).symm.toLinearMap

theorem jetMatrix_mul_hermiteMatrix (k : ℕ) : jetMatrix k * hermiteMatrix k = 1 := by
  have : Matrix.toLin' (jetMatrix k) ∘ₗ (jetEquiv k).symm.toLinearMap = LinearMap.id := by
    refine LinearMap.ext fun v => ?_
    exact (jetEquiv k).apply_symm_apply v
  have h2 := congrArg LinearMap.toMatrix' this
  rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at h2

theorem hermiteMatrix_mul_jetMatrix (k : ℕ) : hermiteMatrix k * jetMatrix k = 1 := by
  have : (jetEquiv k).symm.toLinearMap ∘ₗ Matrix.toLin' (jetMatrix k) = LinearMap.id := by
    refine LinearMap.ext fun v => ?_
    exact (jetEquiv k).symm_apply_apply v
  have h2 := congrArg LinearMap.toMatrix' this
  rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at h2

/-! ### Vector-valued interpolation: existence and uniqueness -/

/-- The endpoint jet `(P⁽ʲ⁾(e))_{e ∈ {0,1}, j ≤ k}` of a polynomial curve. -/
noncomputable def jets {k : ℕ} (c : Fin (2 * k + 2) → E) : Fin 2 × Fin (k + 1) → E :=
  fun r => polyCurveDeriv (r.2 : ℕ) c (((r.1 : ℕ) : ℝ))

theorem jets_apply {k : ℕ} (c : Fin (2 * k + 2) → E) (r : Fin 2 × Fin (k + 1)) :
    jets c r = ∑ i, jetMatrix k r i • c i := rfl

/-- The Hermite coefficients of a prescribed jet family. -/
noncomputable def hermiteCoeffs {k : ℕ} (J : Fin 2 × Fin (k + 1) → E) : Fin (2 * k + 2) → E :=
  fun i => ∑ r, hermiteMatrix k i r • J r

/-- **Existence**: the Hermite polynomial has the prescribed endpoint jets. -/
theorem jets_hermiteCoeffs {k : ℕ} (J : Fin 2 × Fin (k + 1) → E) : jets (hermiteCoeffs J) = J := by
  funext r
  rw [jets_apply]
  simp only [hermiteCoeffs, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  have : ∀ s, ∑ i, (jetMatrix k r i * hermiteMatrix k i s) • J s
      = ((jetMatrix k * hermiteMatrix k) r s) • J s := by
    intro s; rw [Matrix.mul_apply, Finset.sum_smul]
  simp only [this, jetMatrix_mul_hermiteMatrix, Matrix.one_apply, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- **Reproduction**: every polynomial curve of degree `≤ 2k+1` is the Hermite interpolant of
its own endpoint jets. -/
theorem hermiteCoeffs_jets {k : ℕ} (c : Fin (2 * k + 2) → E) : hermiteCoeffs (jets c) = c := by
  funext i
  simp only [hermiteCoeffs, jets_apply, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  have : ∀ i', ∑ r, (hermiteMatrix k i r * jetMatrix k r i') • c i'
      = ((hermiteMatrix k * jetMatrix k) i i') • c i' := by
    intro i'; rw [Matrix.mul_apply, Finset.sum_smul]
  simp only [this, hermiteMatrix_mul_jetMatrix, Matrix.one_apply, ite_smul, one_smul, zero_smul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- **Uniqueness**: two polynomial curves of degree `≤ 2k+1` with the same endpoint jets
through order `k` coincide. -/
theorem eq_of_jets_eq {k : ℕ} {c c' : Fin (2 * k + 2) → E} (h : jets c = jets c') : c = c' := by
  rw [← hermiteCoeffs_jets c, h, hermiteCoeffs_jets]

/-- **Existence and uniqueness of two-endpoint Hermite interpolation** in a normed space. -/
theorem existsUnique_jets_eq {k : ℕ} (J : Fin 2 × Fin (k + 1) → E) :
    ∃! c : Fin (2 * k + 2) → E, jets c = J :=
  ⟨hermiteCoeffs J, jets_hermiteCoeffs J, fun c hc => by rw [← hc, hermiteCoeffs_jets]⟩

/-! ### Norm equivalence with uniform constants -/

/-- The uniform constant `∑ᵢ i(i−1)⋯(i−j+1) · ∑_r |Nᵢᵣ|`. -/
noncomputable def hermiteConst (k j : ℕ) : ℝ :=
  ∑ i : Fin (2 * k + 2), ((i : ℕ).descFactorial j : ℝ) * ∑ r, |hermiteMatrix k i r|

theorem hermiteConst_nonneg (k j : ℕ) : 0 ≤ hermiteConst k j :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _)
    (Finset.sum_nonneg fun _ _ => abs_nonneg _)

/-- Coefficients are controlled by the endpoint jets. -/
theorem norm_coeff_le {k : ℕ} (c : Fin (2 * k + 2) → E) {b : ℝ} (hb : ∀ r, ‖jets c r‖ ≤ b)
    (i : Fin (2 * k + 2)) : ‖c i‖ ≤ (∑ r, |hermiteMatrix k i r|) * b := by
  conv_lhs => rw [← hermiteCoeffs_jets c]
  unfold hermiteCoeffs
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun r _ => ?_
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hb r) (abs_nonneg _)

/-- **Norm equivalence on `[0,1]`**: `‖P⁽ʲ⁾(z)‖ ≤ hermiteConst k j · b` for `z ∈ [0,1]`
whenever all endpoint jets through order `k` have norm `≤ b`. -/
theorem norm_polyCurveDeriv_le_unit {k : ℕ} (c : Fin (2 * k + 2) → E) {b : ℝ}
    (hb : ∀ r, ‖jets c r‖ ≤ b) (j : ℕ) {z : ℝ} (hz : z ∈ Set.Icc (0 : ℝ) 1) :
    ‖polyCurveDeriv j c z‖ ≤ hermiteConst k j * b := by
  unfold polyCurveDeriv hermiteConst
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [norm_smul, Real.norm_eq_abs, abs_mul, Nat.abs_cast, abs_of_nonneg (pow_nonneg hz.1 _),
    mul_assoc]
  rw [mul_assoc (((i : ℕ).descFactorial j : ℕ) : ℝ)]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg (α := ℝ) _)
  calc z ^ ((i : ℕ) - j) * ‖c i‖ ≤ 1 * ‖c i‖ :=
        mul_le_mul_of_nonneg_right (pow_le_one₀ hz.1 hz.2) (norm_nonneg _)
    _ ≤ (∑ r, |hermiteMatrix k i r|) * b := by rw [one_mul]; exact norm_coeff_le c hb i

/-! ### τ-scaling -/

/-- Rescaled coefficients `cᵢ ↦ τⁱ cᵢ`, i.e. the curve `z ↦ P(τ z)`. -/
noncomputable def scaleCoeffs {N : ℕ} (τ : ℝ) (c : Fin N → E) : Fin N → E :=
  fun i => τ ^ (i : ℕ) • c i

theorem polyCurveDeriv_scaleCoeffs {N : ℕ} (τ : ℝ) (c : Fin N → E) (j : ℕ) (z : ℝ) :
    polyCurveDeriv j (scaleCoeffs τ c) z = τ ^ j • polyCurveDeriv j c (τ * z) := by
  unfold polyCurveDeriv scaleCoeffs
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul, smul_smul]
  by_cases hij : j ≤ (i : ℕ)
  · congr 1
    obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hij
    rw [hm, Nat.add_sub_cancel_left, pow_add, mul_pow]
    ring
  · have : ((i : ℕ).descFactorial j) = 0 := Nat.descFactorial_eq_zero_iff_lt.2 (by omega)
    simp [this]

/-- **Scaled norm equivalence on `[0,τ]`**: if `τⁱ ‖P⁽ⁱ⁾(eτ)‖ ≤ b` for both endpoints
`e ∈ {0,1}` and `i ≤ k`, then `‖P⁽ʲ⁾(t)‖ ≤ hermiteConst k j · b / τʲ` on `[0,τ]`. -/
theorem norm_polyCurveDeriv_le_scaled {k : ℕ} (c : Fin (2 * k + 2) → E) {τ b : ℝ} (hτ : 0 < τ)
    (hb : ∀ e : Fin 2, ∀ i : Fin (k + 1),
      τ ^ (i : ℕ) * ‖polyCurveDeriv (i : ℕ) c (((e : ℕ) : ℝ) * τ)‖ ≤ b)
    (j : ℕ) {t : ℝ} (ht : t ∈ Set.Icc 0 τ) :
    ‖polyCurveDeriv j c t‖ ≤ hermiteConst k j * b / τ ^ j := by
  have hjets : ∀ r, ‖jets (scaleCoeffs τ c) r‖ ≤ b := by
    intro r
    simp only [jets, polyCurveDeriv_scaleCoeffs, norm_smul, Real.norm_eq_abs,
      abs_of_pos (pow_pos hτ _)]
    rw [mul_comm τ]
    exact hb r.1 r.2
  have hz : t / τ ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨div_nonneg ht.1 hτ.le, (div_le_one hτ).2 ht.2⟩
  have h := norm_polyCurveDeriv_le_unit (scaleCoeffs τ c) hjets j hz
  rw [polyCurveDeriv_scaleCoeffs, mul_div_cancel₀ _ hτ.ne', norm_smul, Real.norm_eq_abs,
    abs_of_pos (pow_pos hτ _)] at h
  rw [le_div_iff₀ (pow_pos hτ _), mul_comm]
  exact h

/-- The scaled norm equivalence in terms of the actual iterated derivatives of the polynomial
map `P = polyCurve c`. -/
theorem norm_iteratedDeriv_polyCurve_le_scaled {k : ℕ} (c : Fin (2 * k + 2) → E) {τ b : ℝ}
    (hτ : 0 < τ)
    (hb : ∀ e : Fin 2, ∀ i : Fin (k + 1),
      τ ^ (i : ℕ) * ‖iteratedDeriv (i : ℕ) (polyCurve c) (((e : ℕ) : ℝ) * τ)‖ ≤ b)
    (j : ℕ) {t : ℝ} (ht : t ∈ Set.Icc 0 τ) :
    ‖iteratedDeriv j (polyCurve c) t‖ ≤ hermiteConst k j * b / τ ^ j := by
  simp only [iteratedDeriv_polyCurve] at hb ⊢
  exact norm_polyCurveDeriv_le_scaled c hτ hb j ht

/-- **First clause of `lem:supp-open-hermite-precision`** (degree seven, jets through order
three): for a degree-seven polynomial map `δQ : ℝ → E` (coefficients `c : Fin 8 → E`), a step
`τ > 0` and `b ≥ max_{e ∈ {0,1}, j ≤ 3} τʲ ‖δQ⁽ʲ⁾(eτ)‖`, one has
`‖δQ⁽ʲ⁾(t)‖ ≤ C_j τ^{−j} b` on `[0,τ]` for every `j` (in particular `0 ≤ j ≤ 3`), with
`C_j = hermiteConst 3 j` independent of `τ`, `E` and `δQ`. -/
theorem hermite_precision_degree_seven (c : Fin (2 * 3 + 2) → E) {τ b : ℝ} (hτ : 0 < τ)
    (hb : ∀ e : Fin 2, ∀ i : Fin 4,
      τ ^ (i : ℕ) * ‖iteratedDeriv (i : ℕ) (polyCurve c) (((e : ℕ) : ℝ) * τ)‖ ≤ b)
    (j : ℕ) {t : ℝ} (ht : t ∈ Set.Icc 0 τ) :
    ‖iteratedDeriv j (polyCurve c) t‖ ≤ hermiteConst 3 j * b / τ ^ j :=
  norm_iteratedDeriv_polyCurve_le_scaled c hτ hb j ht

/-! ### The explicit degree-seven endpoint corrections `eq:supp-open-hermite-correction` -/

/-- `H₂(z) = −½ z⁴ (z−1)² (4z−5)` (`eq:supp-open-hermite-correction`). -/
noncomputable def hermiteH2 (z : ℝ) : ℝ := -(1 / 2) * z ^ 4 * (z - 1) ^ 2 * (4 * z - 5)

/-- `H₃(z) = ⅙ z⁴ (z−1)³` (`eq:supp-open-hermite-correction`). -/
noncomputable def hermiteH3 (z : ℝ) : ℝ := (1 / 6) * z ^ 4 * (z - 1) ^ 3

/-- Monomial coefficients of `H₂(z) δ₂ + H₃(z) δ₃`. -/
noncomputable def hermiteCorrUnit (δ₂ δ₃ : E) : Fin (2 * 3 + 2) → E :=
  ![0, 0, 0, 0, (5 / 2 : ℝ) • δ₂ - (1 / 6 : ℝ) • δ₃, (-7 : ℝ) • δ₂ + (1 / 2 : ℝ) • δ₃,
    (13 / 2 : ℝ) • δ₂ - (1 / 2 : ℝ) • δ₃, (-2 : ℝ) • δ₂ + (1 / 6 : ℝ) • δ₃]

theorem polyCurve_hermiteCorrUnit (δ₂ δ₃ : E) (z : ℝ) :
    polyCurve (hermiteCorrUnit δ₂ δ₃) z = hermiteH2 z • δ₂ + hermiteH3 z • δ₃ := by
  simp only [polyCurve, hermiteCorrUnit, hermiteH2, hermiteH3, Fin.sum_univ_succ,
    Fin.sum_univ_zero]
  simp
  module

/-- Unit-interval jets of the correction: zero through order three at `0`; at `1` the value
and velocity vanish, the acceleration is `δ₂` and the jerk is `δ₃`. -/
theorem polyCurveDeriv_hermiteCorrUnit (δ₂ δ₃ : E) :
    (∀ j : Fin 4, polyCurveDeriv (j : ℕ) (hermiteCorrUnit δ₂ δ₃) 0 = 0) ∧
      polyCurveDeriv 0 (hermiteCorrUnit δ₂ δ₃) 1 = 0 ∧
      polyCurveDeriv 1 (hermiteCorrUnit δ₂ δ₃) 1 = 0 ∧
      polyCurveDeriv 2 (hermiteCorrUnit δ₂ δ₃) 1 = δ₂ ∧
      polyCurveDeriv 3 (hermiteCorrUnit δ₂ δ₃) 1 = δ₃ := by
  refine ⟨fun j => ?_, ?_, ?_, ?_, ?_⟩
  · fin_cases j <;>
    · simp [polyCurveDeriv, hermiteCorrUnit, Fin.sum_univ_succ, Nat.descFactorial]
  all_goals
    simp [polyCurveDeriv, hermiteCorrUnit, Fin.sum_univ_succ, Nat.descFactorial]
    module

/-- The scaled correction `t ↦ τ² δ₂ H₂(t/τ) + τ³ δ₃ H₃(t/τ)` as a degree-seven polynomial
curve. -/
noncomputable def hermiteCorrection (τ : ℝ) (δ₂ δ₃ : E) : Fin (2 * 3 + 2) → E :=
  scaleCoeffs τ⁻¹ (hermiteCorrUnit (τ ^ 2 • δ₂) (τ ^ 3 • δ₃))

theorem polyCurve_scaleCoeffs {N : ℕ} (s : ℝ) (c : Fin N → E) (t : ℝ) :
    polyCurve (scaleCoeffs s c) t = polyCurve c (s * t) := by
  rw [← polyCurveDeriv_zero, polyCurveDeriv_scaleCoeffs, polyCurveDeriv_zero, pow_zero, one_smul]

theorem polyCurve_hermiteCorrection (τ : ℝ) (δ₂ δ₃ : E) (t : ℝ) :
    polyCurve (hermiteCorrection τ δ₂ δ₃) t
      = (τ ^ 2 * hermiteH2 (t / τ)) • δ₂ + (τ ^ 3 * hermiteH3 (t / τ)) • δ₃ := by
  rw [hermiteCorrection, polyCurve_scaleCoeffs, polyCurve_hermiteCorrUnit, smul_smul, smul_smul,
    inv_mul_eq_div]
  ring_nf

/-- **`eq:supp-open-hermite-correction`**: for `τ ≠ 0` the correction
`τ²δ₂H₂(t/τ) + τ³δ₃H₃(t/τ)` has vanishing derivatives of orders `0..3` at `t = 0`, and at
`t = τ` its value and velocity vanish while its acceleration is `δ₂` and its jerk is `δ₃`. -/
theorem hermiteCorrection_jets {τ : ℝ} (hτ : τ ≠ 0) (δ₂ δ₃ : E) :
    (∀ j : Fin 4, iteratedDeriv (j : ℕ) (polyCurve (hermiteCorrection τ δ₂ δ₃)) 0 = 0) ∧
      polyCurve (hermiteCorrection τ δ₂ δ₃) τ = 0 ∧
      iteratedDeriv 1 (polyCurve (hermiteCorrection τ δ₂ δ₃)) τ = 0 ∧
      iteratedDeriv 2 (polyCurve (hermiteCorrection τ δ₂ δ₃)) τ = δ₂ ∧
      iteratedDeriv 3 (polyCurve (hermiteCorrection τ δ₂ δ₃)) τ = δ₃ := by
  obtain ⟨h0, h10, h11, h12, h13⟩ := polyCurveDeriv_hermiteCorrUnit (τ ^ 2 • δ₂) (τ ^ 3 • δ₃)
  have hτ1 : τ⁻¹ * τ = 1 := inv_mul_cancel₀ hτ
  simp only [iteratedDeriv_polyCurve, hermiteCorrection, polyCurveDeriv_scaleCoeffs, mul_zero,
    hτ1]
  refine ⟨fun j => by rw [h0 j, smul_zero], ?_, ?_, ?_, ?_⟩
  · rw [← polyCurveDeriv_zero, polyCurveDeriv_scaleCoeffs, hτ1, h10, smul_zero]
  · rw [h11, smul_zero]
  · rw [h12, smul_smul, ← mul_pow, inv_mul_cancel₀ hτ, one_pow, one_smul]
  · rw [h13, smul_smul, ← mul_pow, inv_mul_cancel₀ hτ, one_pow, one_smul]

/-! ### Taylor–Hermite remainder with uniform constants -/

theorem polyCurveDeriv_sub {N : ℕ} (j : ℕ) (c c' : Fin N → E) (t : ℝ) :
    polyCurveDeriv j (c - c') t = polyCurveDeriv j c t - polyCurveDeriv j c' t := by
  simp only [polyCurveDeriv, Pi.sub_apply, smul_sub, Finset.sum_sub_distrib]

/-- Taylor bound at `0` on `[0,τ]` with a derivative bound only on `[0,τ]`. -/
theorem norm_sub_taylorSum_le_Icc (φ : ℝ → E) (n : ℕ) (M : ℝ) (hφ : ContDiff ℝ (n + 1) φ)
    {τ : ℝ} (hM : ∀ t ∈ Set.Icc 0 τ, ‖iteratedDeriv (n + 1) φ t‖ ≤ M) {h : ℝ} (hh : 0 ≤ h)
    (hhτ : h ≤ τ) :
    ‖φ h - VectorLineTaylor.taylorSum φ n h‖ ≤ M * h ^ (n + 1) / n.factorial := by
  rcases eq_or_lt_of_le hh with rfl | hpos
  · rw [VectorLineTaylor.taylorSum_zero, sub_self, norm_zero]
    simp
  · have hunique : UniqueDiffOn ℝ (Set.Icc 0 h) := uniqueDiffOn_Icc hpos
    have heq : VectorLineTaylor.taylorSum φ n h = taylorWithinEval φ n (Set.Icc 0 h) 0 h := by
      rw [taylor_within_apply, VectorLineTaylor.taylorSum]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [sub_zero, iteratedDerivWithin_eq_iteratedDeriv hunique _ (Set.left_mem_Icc.2 hh)]
      apply ContDiff.contDiffAt
      apply hφ.of_le
      have := Finset.mem_range.mp hk
      exact_mod_cast this.le
    rw [heq]
    have := taylor_mean_remainder_bound (f := φ) (n := n) (C := M) hh hφ.contDiffOn
      (Set.right_mem_Icc.2 hh) (fun y hy => by
        rw [iteratedDerivWithin_eq_iteratedDeriv hunique hφ.contDiffAt hy]
        exact hM y ⟨hy.1, hy.2.trans hhτ⟩)
    simpa using this

/-- Taylor coefficients `f⁽ⁱ⁾(0)/i!`, `i < N`, of `f` at `0`. -/
noncomputable def taylorCoeffs (f : ℝ → E) (N : ℕ) : Fin N → E :=
  fun i => (((i : ℕ).factorial : ℝ))⁻¹ • iteratedDeriv i f 0

theorem iteratedDeriv_iteratedDeriv_eq (f : ℝ → E) (m j : ℕ) :
    iteratedDeriv m (iteratedDeriv j f) = iteratedDeriv (m + j) f := by
  rw [iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate,
    Function.iterate_add]
  rfl

/-- The `j`-th derivative of the Taylor polynomial of `f` is the Taylor polynomial of `f⁽ʲ⁾`. -/
theorem polyCurveDeriv_taylorCoeffs (f : ℝ → E) {N j : ℕ} (hj : j < N) (t : ℝ) :
    polyCurveDeriv j (taylorCoeffs f N) t
      = VectorLineTaylor.taylorSum (iteratedDeriv j f) (N - 1 - j) t := by
  unfold polyCurveDeriv taylorCoeffs VectorLineTaylor.taylorSum
  rw [Fin.sum_univ_eq_sum_range (fun i => (((i.descFactorial j : ℕ) : ℝ) * t ^ (i - j)) •
    (((i.factorial : ℕ) : ℝ))⁻¹ • iteratedDeriv i f 0) N]
  obtain ⟨m, rfl⟩ : ∃ m, N = j + (m + 1) := ⟨N - j - 1, by omega⟩
  rw [Finset.sum_range_add, show j + (m + 1) - 1 - j = m by omega]
  rw [Finset.sum_eq_zero (fun i hi => by
    have : i.descFactorial j = 0 := Nat.descFactorial_eq_zero_iff_lt.2 (Finset.mem_range.1 hi)
    simp [this]), zero_add]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul, iteratedDeriv_iteratedDeriv_eq, Nat.add_sub_cancel_left, add_comm i j]
  congr 1
  have h := Nat.factorial_mul_descFactorial (show j ≤ j + i by omega)
  rw [Nat.add_sub_cancel_left] at h
  have hf : ((j + i).factorial : ℝ) ≠ 0 := by positivity
  have hi : (i.factorial : ℝ) ≠ 0 := by positivity
  have h' : (i.factorial : ℝ) * ((j + i).descFactorial j : ℝ) = (j + i).factorial := by
    exact_mod_cast h
  field_simp
  linear_combination t ^ i * h'

/-- The Hermite interpolant of `f` on `[0,τ]`: coefficients of the unique polynomial curve of
degree `≤ 2k+1` with the jets of `f` through order `k` at `0` and `τ`. -/
noncomputable def hermiteInterpCoeffs (k : ℕ) (f : ℝ → E) (τ : ℝ) : Fin (2 * k + 2) → E :=
  scaleCoeffs τ⁻¹ (hermiteCoeffs (fun r : Fin 2 × Fin (k + 1) =>
    τ ^ (r.2 : ℕ) • iteratedDeriv r.2 f (((r.1 : ℕ) : ℝ) * τ)))

/-- **Interpolation property**: the Hermite interpolant matches the jets of `f` through order `k`
at both endpoints `0` and `τ`. -/
theorem iteratedDeriv_hermiteInterp {k : ℕ} (f : ℝ → E) {τ : ℝ} (hτ : τ ≠ 0) (e : Fin 2)
    (i : Fin (k + 1)) :
    iteratedDeriv i (polyCurve (hermiteInterpCoeffs k f τ)) (((e : ℕ) : ℝ) * τ)
      = iteratedDeriv i f (((e : ℕ) : ℝ) * τ) := by
  rw [iteratedDeriv_polyCurve, hermiteInterpCoeffs, polyCurveDeriv_scaleCoeffs,
    show τ⁻¹ * (((e : ℕ) : ℝ) * τ) = ((e : ℕ) : ℝ) by field_simp]
  have := congrFun (jets_hermiteCoeffs (fun r : Fin 2 × Fin (k + 1) =>
    τ ^ (r.2 : ℕ) • iteratedDeriv r.2 f (((r.1 : ℕ) : ℝ) * τ))) (e, i)
  simp only [jets] at this
  rw [this, smul_smul, ← mul_pow, inv_mul_cancel₀ hτ, one_pow, one_smul]

/-- **Taylor–Hermite remainder bound with uniform constants and τ-scaling.**  If
`f : ℝ → E` is `C^{2k+2}` and `‖f^{(2k+2)}‖ ≤ M` on `[0,τ]`, then the two-endpoint Hermite
interpolant `P` of degree `2k+1` satisfies, for every `j ≤ 2k+1` and `t ∈ [0,τ]`,
`‖f⁽ʲ⁾(t) − P⁽ʲ⁾(t)‖ ≤ (1 + hermiteConst k j) · M · τ^{2k+2−j}`. -/
theorem norm_iteratedDeriv_sub_hermiteInterp_le {k : ℕ} (f : ℝ → E)
    (hf : ContDiff ℝ (2 * k + 2) f) {τ M : ℝ} (hτ : 0 < τ)
    (hM : ∀ t ∈ Set.Icc 0 τ, ‖iteratedDeriv (2 * k + 2) f t‖ ≤ M) {j : ℕ}
    (hj : j ≤ 2 * k + 1) {t : ℝ} (ht : t ∈ Set.Icc 0 τ) :
    ‖iteratedDeriv j f t - iteratedDeriv j (polyCurve (hermiteInterpCoeffs k f τ)) t‖
      ≤ (1 + hermiteConst k j) * M * τ ^ (2 * k + 2 - j) := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 ⟨le_rfl, hτ.le⟩)
  set T := taylorCoeffs f (2 * k + 2)
  set cP := hermiteInterpCoeffs k f τ
  -- Taylor bound for every derivative order `i ≤ 2k+1` on `[0,τ]`
  have htaylor : ∀ i, i ≤ 2 * k + 1 → ∀ s ∈ Set.Icc 0 τ,
      ‖iteratedDeriv i f s - polyCurveDeriv i T s‖ ≤ M * τ ^ (2 * k + 2 - i) := by
    intro i hi s hs
    rw [polyCurveDeriv_taylorCoeffs f (by omega)]
    have hn : 2 * k + 2 - 1 - i + 1 = 2 * k + 2 - i := by omega
    have hφ : ContDiff ℝ ((2 * k + 2 - 1 - i + 1 : ℕ)) (iteratedDeriv i f) := by
      rw [iteratedDeriv_eq_iterate]
      apply ContDiff.iterate_deriv'
      have h2 : (2 * k + 2 - 1 - i + 1 + i : ℕ) = 2 * k + 2 := by omega
      rw [h2]
      exact_mod_cast hf
    have hMφ : ∀ s ∈ Set.Icc 0 τ,
        ‖iteratedDeriv (2 * k + 2 - 1 - i + 1) (iteratedDeriv i f) s‖ ≤ M := by
      intro s hs
      rw [iteratedDeriv_iteratedDeriv_eq, show 2 * k + 2 - 1 - i + 1 + i = 2 * k + 2 by omega]
      exact hM s hs
    have := norm_sub_taylorSum_le_Icc (iteratedDeriv i f) (2 * k + 2 - 1 - i) M
      (by exact_mod_cast hφ) hMφ hs.1 hs.2
    rw [hn] at this
    refine this.trans ?_
    have hfac : (1 : ℝ) ≤ ((2 * k + 2 - 1 - i).factorial : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero _)
    have hs0 := hs.1
    calc M * s ^ (2 * k + 2 - i) / ((2 * k + 2 - 1 - i).factorial : ℝ)
        ≤ M * s ^ (2 * k + 2 - i) := div_le_self (by positivity) hfac
      _ ≤ M * τ ^ (2 * k + 2 - i) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hs.1 hs.2 _) hM0
  -- the Hermite part: `P − T` has jets bounded by `M τ^{2k+2−i}`
  have hjetsPT : ∀ e : Fin 2, ∀ i : Fin (k + 1),
      τ ^ (i : ℕ) * ‖polyCurveDeriv (i : ℕ) (cP - T) (((e : ℕ) : ℝ) * τ)‖
        ≤ M * τ ^ (2 * k + 2) := by
    intro e i
    have hi := i.2
    have he : ((e : ℕ) : ℝ) * τ ∈ Set.Icc 0 τ := by
      have : ((e : ℕ) : ℝ) ≤ 1 := by
        have := e.2; exact_mod_cast (by omega : (e : ℕ) ≤ 1)
      exact ⟨by positivity, by nlinarith⟩
    rw [polyCurveDeriv_sub, ← iteratedDeriv_polyCurve, iteratedDeriv_hermiteInterp f hτ.ne' e i]
    have := htaylor i (by omega) _ he
    calc τ ^ (i : ℕ) * ‖iteratedDeriv (i : ℕ) f (((e : ℕ) : ℝ) * τ)
          - polyCurveDeriv (i : ℕ) T (((e : ℕ) : ℝ) * τ)‖
        ≤ τ ^ (i : ℕ) * (M * τ ^ (2 * k + 2 - i)) :=
          mul_le_mul_of_nonneg_left this (pow_nonneg hτ.le _)
      _ = M * τ ^ (2 * k + 2) := by
          rw [mul_left_comm, ← pow_add, show (i : ℕ) + (2 * k + 2 - i) = 2 * k + 2 by omega]
  have hPT := norm_polyCurveDeriv_le_scaled (cP - T) hτ hjetsPT j ht
  have hfT := htaylor j hj t ht
  rw [iteratedDeriv_polyCurve]
  have hsplit : iteratedDeriv j f t - polyCurveDeriv j cP t
      = (iteratedDeriv j f t - polyCurveDeriv j T t) - polyCurveDeriv j (cP - T) t := by
    rw [polyCurveDeriv_sub]; abel
  rw [hsplit]
  refine (norm_sub_le _ _).trans ?_
  have hpow : M * τ ^ (2 * k + 2) / τ ^ j = M * τ ^ (2 * k + 2 - j) := by
    rw [show 2 * k + 2 = (2 * k + 2 - j) + j by omega, pow_add, Nat.add_sub_cancel]
    field_simp
  rw [mul_div_assoc, hpow] at hPT
  nlinarith [hermiteConst_nonneg k j]

end RenewalGeometry.TwoPointHermite
