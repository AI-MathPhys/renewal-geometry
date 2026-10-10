/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The abstract Cauchy–Kovalevskaya theorem in an analytic scale (Nirenberg–Nishida)

Generic infrastructure (no renewal notions) for `lem:generated-physical-identification` of the
Einstein–SM action-closure manuscript (the analytic germs of `ass:constrained-initial-solver`).

**The scale.**  Coefficient sequences `c : ι → V` (any index type `ι`, values in a real Banach space
`V`, weights `w : ι → ℝ`, `w ≥ 0`) with the exponentially weighted `ℓ¹` norms
`ν_s(c) = Σ_ι ‖c_ι‖ e^{s w_ι} ∈ [0, ∞]`.  For Fourier coefficients on `𝕋^d` (`ι = ℤ^d`,
`w_k = |k|₁`) `ν_s(c) < ∞` means analyticity in the complex strip `|Im z| < s` (up to an arbitrarily
small loss of width), and `ν_{s'}(∂_j c) ≤ ν_s(c)/(e(s - s'))` is the Cauchy estimate
(`nu_mul_weight_le`).  The scale is decreasing: `ν_{s'} ≤ ν_s` for `s' ≤ s`.

**The theorem** (`cauchy_kovalevskaya`, Nishida's form with Nirenberg–Nishida shrinking cones).  Let
`L` satisfy, for `0 ≤ s' < s < s₀` and `ν_s(u), ν_s(v) < R`,
`ν_{s'}(L u - L v) ≤ C/(s - s') ν_s(u - v)` and `ν_s(L 0) ≤ K/(s₀ - s)`.  Then with
`a = min(1/(32 C), R/(16 K))/2` there is `u` with `u(0) = 0`, `ν_s(u(t)) ≤ R/2` and
`u(t) = ∫₀ᵗ L(u(τ)) dτ` (coefficientwise) for `0 ≤ t < a(s₀ - s)`.  The existence time `a s₀`
depends only on the strip width `s₀` and the constants `C, K, R`.

Proof: Picard iterates `u_{k+1}(t) = ∫₀ᵗ L(u_k)`; on the cones `t < a_k(s₀ - s)`,
`a_k = a₀(k+2)/(2(k+1)) ↓ a₀/2`, the differences obey the Nishida weighted bound
`ν_s(u_{k+1} - u_k)(t) ≤ μ_{k+1} t/(a_k(s₀ - s) - t)`, `μ_{k+1} ≤ 4C a₀ μ_k`, by applying the
Lipschitz bound at the moving level `σ(τ) = (s + s₀ - τ/a_k)/2`; the shrinking of the cones keeps
the iterates in the ball `ν_s < R` (the weights are bounded by `(j+1)²` on the next cone).
-/

open MeasureTheory Filter Topology Set intervalIntegral
open scoped ENNReal NNReal

noncomputable section

namespace RenewalGeometry.CKScale

set_option linter.unusedSectionVars false

variable {ι : Type*} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-! ### The weighted `ℓ¹` scale -/

section Scale

variable (w : ι → ℝ)

/-- The exponentially weighted `ℓ¹` norm `ν_s(c) = Σ_ι ‖c_ι‖ e^{s w_ι}` (extended). -/
def nu (s : ℝ) (c : ι → V) : ℝ≥0∞ := ∑' i, ‖c i‖ₑ * ENNReal.ofReal (Real.exp (s * w i))

variable {w}

theorem nu_zero (s : ℝ) : nu w s (0 : ι → V) = 0 := by simp [nu]

theorem nu_add_le (s : ℝ) (c d : ι → V) : nu w s (c + d) ≤ nu w s c + nu w s d := by
  unfold nu
  rw [← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun i => ?_
  rw [← add_mul]
  exact mul_le_mul_left (enorm_add_le _ _) _

theorem nu_neg (s : ℝ) (c : ι → V) : nu w s (-c) = nu w s c := by simp [nu]

theorem nu_sub_comm (s : ℝ) (c d : ι → V) : nu w s (c - d) = nu w s (d - c) := by
  rw [← neg_sub, nu_neg]

theorem nu_sub_le (s : ℝ) (c d : ι → V) : nu w s (c - d) ≤ nu w s c + nu w s d := by
  rw [sub_eq_add_neg]; exact (nu_add_le s c (-d)).trans (by rw [nu_neg])

theorem nu_smul (s : ℝ) (r : ℝ) (c : ι → V) : nu w s (r • c) = ‖r‖ₑ * nu w s c := by
  unfold nu
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun i => ?_
  rw [Pi.smul_apply, enorm_smul, mul_assoc]

theorem nu_mono (hw : ∀ i, 0 ≤ w i) {s' s : ℝ} (hs : s' ≤ s) (c : ι → V) :
    nu w s' c ≤ nu w s c := by
  refine ENNReal.tsum_le_tsum fun i => mul_le_mul_right (ENNReal.ofReal_le_ofReal ?_) _
  exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hs (hw i))

theorem enorm_le_nu (hw : ∀ i, 0 ≤ w i) {s : ℝ} (hs : 0 ≤ s) (c : ι → V) (i : ι) :
    ‖c i‖ₑ ≤ nu w s c := by
  refine le_trans ?_ (ENNReal.le_tsum i)
  have : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (Real.exp (s * w i)) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (Real.one_le_exp (mul_nonneg hs (hw i)))
  calc ‖c i‖ₑ = ‖c i‖ₑ * 1 := (mul_one _).symm
    _ ≤ _ := mul_le_mul_right this _

theorem nu_finset_sum_le (s : ℝ) {α : Type*} (S : Finset α) (f : α → ι → V) :
    nu w s (∑ a ∈ S, f a) ≤ ∑ a ∈ S, nu w s (f a) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [nu_zero]
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (nu_add_le s _ _).trans (add_le_add_right ih _)

/-- **Lower semicontinuity** of `ν_s` under coefficientwise convergence. -/
theorem nu_le_of_tendsto {c : ℕ → ι → V} {d : ι → V} (hc : ∀ i, Tendsto (fun m => c m i) atTop (𝓝 (d i)))
    {s : ℝ} {B : ℝ≥0∞} (hB : ∀ᶠ m in atTop, nu w s (c m) ≤ B) : nu w s d ≤ B := by
  unfold nu
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun S => ?_
  have hlim : Tendsto (fun m => ∑ i ∈ S, ‖c m i‖ₑ * ENNReal.ofReal (Real.exp (s * w i))) atTop
      (𝓝 (∑ i ∈ S, ‖d i‖ₑ * ENNReal.ofReal (Real.exp (s * w i)))) := by
    refine tendsto_finsetSum _ fun i _ => ?_
    exact ENNReal.Tendsto.mul_const ((continuous_enorm.tendsto _).comp (hc i)) (Or.inr ENNReal.ofReal_ne_top)
  refine le_of_tendsto hlim ?_
  filter_upwards [hB] with m hm
  exact (ENNReal.sum_le_tsum S).trans hm

/-- The Cauchy estimate of the scale: `|w_i| e^{s' w_i} ≤ e^{s w_i}/(e(s - s'))`, so multiplying
the coefficients by the weights (a first-order derivative on the torus) loses `1/(e(s - s'))`. -/
theorem nu_mul_weight_le (hw : ∀ i, 0 ≤ w i) {s' s : ℝ} (hs : s' < s) (c : ι → V) :
    nu w s' (fun i => w i • c i) ≤ ENNReal.ofReal (1 / (Real.exp 1 * (s - s'))) * nu w s c := by
  unfold nu
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun i => ?_
  have hd : 0 < s - s' := sub_pos.2 hs
  -- `x e^{-δ x} ≤ 1/(e δ)`
  have key : w i * Real.exp (-(s - s') * w i) ≤ 1 / (Real.exp 1 * (s - s')) := by
    have h1 := Real.add_one_le_exp ((s - s') * w i - 1)
    rw [sub_add_cancel, Real.exp_sub] at h1
    have he := Real.exp_pos ((s - s') * w i)
    have he1 := Real.exp_pos 1
    rw [le_div_iff₀ (by positivity), neg_mul, Real.exp_neg]
    rw [le_div_iff₀ he1] at h1
    calc w i * (Real.exp ((s - s') * w i))⁻¹ * (Real.exp 1 * (s - s'))
        = ((s - s') * w i * Real.exp 1) * (Real.exp ((s - s') * w i))⁻¹ := by ring
      _ ≤ Real.exp ((s - s') * w i) * (Real.exp ((s - s') * w i))⁻¹ :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = 1 := mul_inv_cancel₀ he.ne'
  have hreal : w i * Real.exp (s' * w i) ≤ 1 / (Real.exp 1 * (s - s')) * Real.exp (s * w i) := by
    have e1 : w i * Real.exp (s' * w i) = Real.exp (s * w i) * (w i * Real.exp (-(s - s') * w i)) := by
      rw [show s' * w i = s * w i + (-(s - s') * w i) by ring, Real.exp_add]; ring
    rw [e1, mul_comm (1 / _)]
    exact mul_le_mul_of_nonneg_left key (Real.exp_pos _).le
  calc ‖w i • c i‖ₑ * ENNReal.ofReal (Real.exp (s' * w i))
      = ‖c i‖ₑ * ENNReal.ofReal (w i * Real.exp (s' * w i)) := by
        rw [enorm_smul, Real.enorm_eq_ofReal (hw i), ENNReal.ofReal_mul (hw i)]; ring
    _ ≤ ‖c i‖ₑ * ENNReal.ofReal (1 / (Real.exp 1 * (s - s')) * Real.exp (s * w i)) := by
        gcongr
    _ = _ := by rw [ENNReal.ofReal_mul (by positivity)]; ring

end Scale

/-! ### Time integrals in the scale -/

section Integral

variable {w : ι → ℝ}

/-- The coefficientwise time integral `(∫_a^b g)_ι = ∫_a^b g(τ)_ι dτ`. -/
def tint (g : ℝ → ι → V) (a b : ℝ) : ι → V := fun i => ∫ τ in a..b, g τ i

theorem lintegral_tsum_ge {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : ι → α → ℝ≥0∞) :
    ∑' i, ∫⁻ x, f i x ∂μ ≤ ∫⁻ x, ∑' i, f i x ∂μ := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun S => ?_
  have h1 : ∑ i ∈ S, ∫⁻ x, f i x ∂μ ≤ ∫⁻ x, ∑ i ∈ S, f i x ∂μ := by
    induction S using Finset.induction_on with
    | empty => simp
    | insert a S ha ih =>
      rw [Finset.sum_insert ha]
      refine (add_le_add_right ih _).trans ?_
      refine (le_lintegral_add _ _).trans (le_of_eq ?_)
      congr 1; funext x; rw [Finset.sum_insert ha]
  exact h1.trans (lintegral_mono fun x => ENNReal.sum_le_tsum S)

/-- `ν_s(∫_a^b g) ≤ ∫⁻_{(a,b]} ν_s(g)` (no measurability needed). -/
theorem nu_tint_le {a b : ℝ} (hab : a ≤ b) (s : ℝ) (g : ℝ → ι → V) :
    nu w s (tint g a b) ≤ ∫⁻ τ in Ioc a b, nu w s (g τ) := by
  unfold nu tint
  calc ∑' i, ‖∫ τ in a..b, g τ i‖ₑ * ENNReal.ofReal (Real.exp (s * w i))
      ≤ ∑' i, (∫⁻ τ in Ioc a b, ‖g τ i‖ₑ) * ENNReal.ofReal (Real.exp (s * w i)) := by
        refine ENNReal.tsum_le_tsum fun i => mul_le_mul_left ?_ _
        rw [intervalIntegral.integral_of_le hab]
        exact enorm_integral_le_lintegral_enorm _
    _ = ∑' i, ∫⁻ τ in Ioc a b, ‖g τ i‖ₑ * ENNReal.ofReal (Real.exp (s * w i)) := by
        refine tsum_congr fun i => ?_
        rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
    _ ≤ _ := lintegral_tsum_ge _ _

/-- `ν_s(∫_a^b g) ≤ ∫_a^b φ` whenever `ν_s(g(τ)) ≤ φ(τ)` on `(a, b]` (`φ ≥ 0` integrable). -/
theorem nu_tint_le_integral {a b : ℝ} (hab : a ≤ b) {s : ℝ} {g : ℝ → ι → V} {φ : ℝ → ℝ}
    (hφi : IntervalIntegrable φ volume a b) (hφ0 : ∀ τ ∈ Ioc a b, 0 ≤ φ τ)
    (hg : ∀ τ ∈ Ioc a b, nu w s (g τ) ≤ ENNReal.ofReal (φ τ)) :
    nu w s (tint g a b) ≤ ENNReal.ofReal (∫ τ in a..b, φ τ) := by
  refine (nu_tint_le hab s g).trans ?_
  rw [intervalIntegral.integral_of_le hab, ofReal_integral_eq_lintegral_ofReal
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).1 hφi)
    ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall hφ0))]
  exact setLIntegral_mono' measurableSet_Ioc hg

/-- The constant-bound version: `ν_s(∫_a^b g) ≤ B (b - a)`. -/
theorem nu_tint_le_const {a b : ℝ} (hab : a ≤ b) {s : ℝ} {g : ℝ → ι → V} {B : ℝ} (hB : 0 ≤ B)
    (hg : ∀ τ ∈ Ioc a b, nu w s (g τ) ≤ ENNReal.ofReal B) :
    nu w s (tint g a b) ≤ ENNReal.ofReal (B * (b - a)) := by
  have := nu_tint_le_integral hab (φ := fun _ => B) intervalIntegrable_const (fun _ _ => hB) hg
  simpa [mul_comm] using this

/-- `∫₀^A·A/(A - τ)² = t/(A - t)`. -/
theorem integral_inv_sq {A t : ℝ} (ht : 0 ≤ t) (htA : t < A) :
    ∫ τ in (0 : ℝ)..t, A / (A - τ) ^ 2 = t / (A - t) := by
  have hA : 0 < A := lt_of_le_of_lt ht htA
  have hderiv : ∀ τ ∈ uIcc 0 t, HasDerivAt (fun τ => A / (A - τ)) (A / (A - τ) ^ 2) τ := by
    intro τ hτ
    rw [uIcc_of_le ht] at hτ
    have hne : A - τ ≠ 0 := by linarith [hτ.2]
    have h2 : HasDerivAt (fun y => A / (A - y)) ((0 * (A - τ) - A * -1) / (A - τ) ^ 2) τ :=
      (hasDerivAt_const τ A).div ((hasDerivAt_id' τ).const_sub A) hne
    exact h2.congr_deriv (by ring)
  rw [integral_eq_sub_of_hasDerivAt hderiv]
  · have : A - t ≠ 0 := by linarith
    rw [sub_zero, div_self hA.ne']
    field_simp
    ring
  · refine ContinuousOn.intervalIntegrable ?_
    intro τ hτ
    rw [uIcc_of_le ht] at hτ
    have hne : A - τ ≠ 0 := by linarith [hτ.2]
    exact (continuousAt_const.div ((continuousAt_const.sub continuousAt_id).pow 2)
      (pow_ne_zero 2 hne)).continuousWithinAt

end Integral


/-! ### The shrinking cones -/

section Cones

/-- The Nirenberg–Nishida shrinking cone parameters `a_k = a₀ (k+2)/(2(k+1))`, decreasing from
`a₀` to `a₀/2`. -/
def coneA (a₀ : ℝ) (k : ℕ) : ℝ := a₀ * (k + 2) / (2 * (k + 1))

theorem coneA_zero (a₀ : ℝ) : coneA a₀ 0 = a₀ := by simp [coneA]

theorem coneA_le {a₀ : ℝ} (ha : 0 ≤ a₀) (k : ℕ) : coneA a₀ k ≤ a₀ := by
  unfold coneA
  rw [div_le_iff₀ (by positivity)]
  nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

theorem half_le_coneA {a₀ : ℝ} (ha : 0 ≤ a₀) (k : ℕ) : a₀ / 2 ≤ coneA a₀ k := by
  unfold coneA
  rw [le_div_iff₀ (by positivity)]
  nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

theorem coneA_pos {a₀ : ℝ} (ha : 0 < a₀) (k : ℕ) : 0 < coneA a₀ k :=
  lt_of_lt_of_le (by linarith) (half_le_coneA ha.le k)

theorem coneA_succ_le {a₀ : ℝ} (ha : 0 ≤ a₀) (k : ℕ) : coneA a₀ (k + 1) ≤ coneA a₀ k := by
  unfold coneA
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  push_cast
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  nlinarith [mul_nonneg ha hk]

theorem coneA_anti {a₀ : ℝ} (ha : 0 ≤ a₀) {k m : ℕ} (hkm : k ≤ m) : coneA a₀ m ≤ coneA a₀ k := by
  induction m, hkm using Nat.le_induction with
  | base => exact le_rfl
  | succ m _ ih => exact (coneA_succ_le ha m).trans ih

/-- The weight bound on the next cone: `t/(a_k D - t) ≤ (k+1)(k+3)` for `t ≤ a_{k+1} D`. -/
theorem ratio_le {a₀ D t : ℝ} (ha : 0 < a₀) (hD : 0 < D) (ht : 0 ≤ t) (k : ℕ)
    (htk : t ≤ coneA a₀ (k + 1) * D) :
    t / (coneA a₀ k * D - t) ≤ ((k : ℝ) + 1) * (k + 3) := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hlt : t < coneA a₀ k * D := by
    have h1 : coneA a₀ (k + 1) < coneA a₀ k := by
      unfold coneA
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      push_cast; nlinarith [mul_nonneg ha.le hk]
    nlinarith
  rw [div_le_iff₀ (by linarith)]
  unfold coneA at htk ⊢
  push_cast at htk
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)] at htk
  have e : coneA a₀ k * D = a₀ * (k + 2) * D / (2 * (k + 1)) := by unfold coneA; ring
  rw [show a₀ * (↑k + 2) / (2 * (↑k + 1)) * D = a₀ * (k + 2) * D / (2 * (k + 1)) by ring]
  rw [mul_sub, mul_div_assoc', le_sub_iff_add_le, le_div_iff₀ (by positivity)]
  have h2 := mul_le_mul_of_nonneg_right htk (show (0 : ℝ) ≤ ((k : ℝ) + 2) * (k + 1) by positivity)
  have e1 : (t + ((k : ℝ) + 1) * (k + 3) * t) * (2 * (k + 1)) =
      t * (2 * (k + 1 + 1)) * ((k + 2) * (k + 1)) := by ring
  have e2 : ((k : ℝ) + 1) * (k + 3) * (a₀ * (k + 2) * D) =
      a₀ * (k + 1 + 2) * D * ((k + 2) * (k + 1)) := by ring
  rw [e1, e2]; exact h2

theorem ratio_le_pow (k : ℕ) : ((k : ℝ) + 1) * (k + 3) ≤ 4 ^ (k + 1) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    push_cast
    rw [pow_succ]
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith

theorem frac_mono {x y B : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hyB : y < B) : x / (B - x) ≤ y / (B - y) := by
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

end Cones

/-! ### The Picard iteration -/

section CK

variable {w : ι → ℝ}

/-- **Nishida's hypotheses** on the operator `L` in the analytic scale `ν_s`, `0 ≤ s < s₀`:
`ν_{s'}(L u - L v) ≤ C/(s - s') ν_s(u - v)` on the ball `ν_s < R`, and `ν_s(L 0) ≤ K/(s₀ - s)`. -/
structure CKHyp (w : ι → ℝ) (L : (ι → V) → ι → V) (s₀ R C K : ℝ) : Prop where
  s₀_pos : 0 < s₀
  R_pos : 0 < R
  C_pos : 0 < C
  K_pos : 0 < K
  lip : ∀ s' s : ℝ, 0 ≤ s' → s' < s → s < s₀ → ∀ u v : ι → V,
    nu w s u < ENNReal.ofReal R → nu w s v < ENNReal.ofReal R →
    nu w s' (L u - L v) ≤ ENNReal.ofReal (C / (s - s')) * nu w s (u - v)
  zero : ∀ s : ℝ, 0 ≤ s → s < s₀ → nu w s (L 0) ≤ ENNReal.ofReal (K / (s₀ - s))

/-- The Picard iterates `u_0 = 0`, `u_{k+1}(t) = ∫₀ᵗ L(u_k(τ)) dτ`. -/
def picard (L : (ι → V) → ι → V) : ℕ → ℝ → ι → V
  | 0 => fun _ => 0
  | k + 1 => fun t => tint (fun τ => L (picard L k τ)) 0 t

/-- The initial cone parameter `a₀ = min(1/(32C), R/(16K))`. -/
def ckA (C K R : ℝ) : ℝ := min (1 / (32 * C)) (R / (16 * K))

/-- The Nishida weights `μ_k = K a₀ (4 C a₀)^k`. -/
def ckMu (C K a₀ : ℝ) (k : ℕ) : ℝ := K * a₀ * (4 * C * a₀) ^ k

/-- The time-Lipschitz constant of the iterates on `[0, T]` at level `s`. -/
def ckLam (s₀ C K R s T a : ℝ) : ℝ := K / (s₀ - s) + C * R / (s₀ - s - T / a)

variable {L : (ι → V) → ι → V} {s₀ R C K : ℝ}

theorem CKHyp.a_pos (hyp : CKHyp w L s₀ R C K) : 0 < ckA C K R := by
  have := hyp.C_pos; have := hyp.K_pos; have := hyp.R_pos
  unfold ckA; positivity

theorem CKHyp.a_C (hyp : CKHyp w L s₀ R C K) : 32 * C * ckA C K R ≤ 1 := by
  have := hyp.C_pos
  have h := min_le_left (1 / (32 * C)) (R / (16 * K))
  unfold ckA
  calc 32 * C * min (1 / (32 * C)) (R / (16 * K)) ≤ 32 * C * (1 / (32 * C)) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = 1 := by field_simp

theorem CKHyp.a_K (hyp : CKHyp w L s₀ R C K) : 16 * K * ckA C K R ≤ R := by
  have := hyp.K_pos
  have h := min_le_right (1 / (32 * C)) (R / (16 * K))
  unfold ckA
  calc 16 * K * min (1 / (32 * C)) (R / (16 * K)) ≤ 16 * K * (R / (16 * K)) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = R := by field_simp

theorem picard_zero_time (L : (ι → V) → ι → V) : ∀ k, picard L k 0 = 0
  | 0 => rfl
  | _ + 1 => by funext i; simp [picard, tint]

/-- Lipschitz continuity in time (in `ν_s`) of an iterate on the cone gives continuity of the
coefficients of `L` along it. -/
theorem continuousOn_coeff_of_lip (hw : ∀ i, 0 ≤ w i) {f : ℝ → ι → V} {T M : ℝ} (hM : 0 ≤ M)
    (h : ∀ τ ∈ Icc 0 T, ∀ τ' ∈ Icc 0 T, nu w 0 (f τ - f τ') ≤ ENNReal.ofReal (M * |τ - τ'|))
    (i : ι) : ContinuousOn (fun τ => f τ i) (Icc 0 T) := by
  have hL : LipschitzOnWith (Real.toNNReal M) (fun τ => f τ i) (Icc 0 T) := by
    intro τ hτ τ' hτ'
    rw [edist_eq_enorm_sub]
    refine (enorm_le_nu hw le_rfl (f τ - f τ') i).trans ((h τ hτ τ' hτ').trans (le_of_eq ?_))
    rw [edist_dist, Real.dist_eq, ENNReal.ofReal_mul hM, ENNReal.ofReal_coe_nnreal.symm]
    simp [Real.toNNReal, hM]
  exact hL.continuousOn

end CK

/-! ### The induction on the shrinking cones -/

section Induction

variable {w : ι → ℝ} (w) (L : (ι → V) → ι → V) (s₀ R C K : ℝ)

/-- Ball bound of the `m`-th iterate on its cone. -/
def QA (m : ℕ) : Prop :=
  ∀ s t : ℝ, 0 ≤ s → s < s₀ → 0 ≤ t → t < coneA (ckA C K R) m * (s₀ - s) →
    nu w s (picard L m t) ≤ ENNReal.ofReal (8 * K * ckA C K R)

/-- Time-Lipschitz bound of the `m`-th iterate on its cone. -/
def QL (m : ℕ) : Prop :=
  ∀ s T : ℝ, 0 ≤ s → s < s₀ → 0 ≤ T → T < coneA (ckA C K R) m * (s₀ - s) →
    ∀ t ∈ Icc 0 T, ∀ t' ∈ Icc 0 T, nu w s (picard L m t - picard L m t') ≤
      ENNReal.ofReal (ckLam s₀ C K R s T (coneA (ckA C K R) m) * |t - t'|)

/-- Nishida's weighted bound of the `(m+1)`-st difference on the `m`-th cone. -/
def QD (m : ℕ) : Prop :=
  ∀ s t : ℝ, 0 ≤ s → s < s₀ → 0 ≤ t → t < coneA (ckA C K R) m * (s₀ - s) →
    nu w s (picard L (m + 1) t - picard L m t) ≤
      ENNReal.ofReal (ckMu C K (ckA C K R) m * t / (coneA (ckA C K R) m * (s₀ - s) - t))

variable {w L s₀ R C K}

theorem ball_of_QA (hyp : CKHyp w L s₀ R C K) {m : ℕ} (hA : QA w L s₀ R C K m) {s t : ℝ}
    (hs : 0 ≤ s) (hs₀ : s < s₀) (ht : 0 ≤ t) (htc : t < coneA (ckA C K R) m * (s₀ - s)) :
    nu w s (picard L m t) < ENNReal.ofReal R := by
  refine (hA s t hs hs₀ ht htc).trans_lt ((ENNReal.ofReal_lt_ofReal_iff hyp.R_pos).2 ?_)
  have := hyp.a_K; have := hyp.a_pos; have := hyp.K_pos; nlinarith

theorem ckLam_nonneg (hyp : CKHyp w L s₀ R C K) {s T a : ℝ} (hs₀ : s < s₀) (ha : 0 < a)
    (hT : T < a * (s₀ - s)) : 0 ≤ ckLam s₀ C K R s T a := by
  have := hyp.K_pos; have := hyp.C_pos; have := hyp.R_pos
  have h1 : 0 < s₀ - s - T / a := by
    rw [sub_pos, div_lt_iff₀ ha]; linarith
  unfold ckLam
  have := sub_pos.2 hs₀
  positivity

/-- **Coefficient continuity along an iterate** (hence interval integrability). -/
theorem continuousOn_L_coeff (hw : ∀ i, 0 ≤ w i) (hyp : CKHyp w L s₀ R C K) {m : ℕ}
    (hA : QA w L s₀ R C K m) (hL : QL w L s₀ R C K m) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t < coneA (ckA C K R) m * s₀) (i : ι) :
    ContinuousOn (fun τ => L (picard L m τ) i) (Icc 0 t) := by
  set a := coneA (ckA C K R) m with ha_def
  have ha : 0 < a := coneA_pos hyp.a_pos m
  set σ := (s₀ - t / a) / 2 with hσ
  have htas : t / a < s₀ := by rw [div_lt_iff₀ ha]; linarith
  have hσ0 : 0 < σ := by rw [hσ]; linarith
  have hσs : σ < s₀ := by rw [hσ]; have : 0 ≤ t / a := by positivity
                          linarith
  have htσ : t < a * (s₀ - σ) := by
    have : a * (s₀ - σ) = (a * s₀ + t) / 2 := by
      rw [hσ]; field_simp; ring
    rw [this]; linarith
  have hΛ := ckLam_nonneg hyp hσs ha htσ
  refine continuousOn_coeff_of_lip hw (M := C / σ * ckLam s₀ C K R σ t a) (by
    have := hyp.C_pos; positivity) (fun τ hτ τ' hτ' => ?_) i
  have hb1 := ball_of_QA hyp hA hσ0.le hσs hτ.1 (lt_of_le_of_lt hτ.2 htσ)
  have hb2 := ball_of_QA hyp hA hσ0.le hσs hτ'.1 (lt_of_le_of_lt hτ'.2 htσ)
  refine (hyp.lip 0 σ le_rfl hσ0 hσs _ _ hb1 hb2).trans ?_
  rw [sub_zero, mul_assoc, ENNReal.ofReal_mul (by have := hyp.C_pos; positivity)]
  exact mul_le_mul_right (hL σ t hσ0.le hσs ht0 htσ τ hτ τ' hτ') _

theorem intervalIntegrable_L_coeff (hw : ∀ i, 0 ≤ w i) (hyp : CKHyp w L s₀ R C K) {m : ℕ}
    (hA : QA w L s₀ R C K m) (hL : QL w L s₀ R C K m) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t < coneA (ckA C K R) m * s₀) (i : ι) :
    IntervalIntegrable (fun τ => L (picard L m τ) i) volume 0 t :=
  (continuousOn_L_coeff hw hyp hA hL ht0 ht i).intervalIntegrable_of_Icc ht0

theorem QA_zero : QA w L s₀ R C K 0 := fun s t _ _ _ _ => by
  simp [picard, nu_zero]

theorem QL_zero : QL w L s₀ R C K 0 := fun s T _ _ _ _ t _ t' _ => by
  simp [picard, nu_zero]

theorem QD_zero (hyp : CKHyp w L s₀ R C K) : QD w L s₀ R C K 0 := by
  intro s t hs hs₀ ht htc
  have ha := hyp.a_pos
  rw [coneA_zero] at htc ⊢
  have hD : 0 < s₀ - s := sub_pos.2 hs₀
  have e : picard L 1 t - picard L 0 t = tint (fun _ => L 0) 0 t := by
    funext i; simp [picard, tint]
  rw [e]
  refine (nu_tint_le_const ht (B := K / (s₀ - s)) (by have := hyp.K_pos; positivity)
    (fun τ _ => hyp.zero s hs hs₀)).trans (ENNReal.ofReal_le_ofReal ?_)
  unfold ckMu
  rw [pow_zero, mul_one, sub_zero]
  have hpos : 0 < ckA C K R * (s₀ - s) - t := by linarith
  rw [div_mul_eq_mul_div, div_le_div_iff₀ hD hpos]
  have := hyp.K_pos
  nlinarith [mul_nonneg (mul_nonneg this.le ha.le) ht]

end Induction

/-! ### The induction steps -/

section Steps

variable {w : ι → ℝ} {L : (ι → V) → ι → V} {s₀ R C K : ℝ}

theorem coneA_mul_le_s₀ (hyp : CKHyp w L s₀ R C K) {m : ℕ} {s : ℝ} (hs : 0 ≤ s) :
    coneA (ckA C K R) m * (s₀ - s) ≤ coneA (ckA C K R) m * s₀ :=
  mul_le_mul_of_nonneg_left (by linarith) (coneA_pos hyp.a_pos m).le

/-- The difference of two values of the next iterate is the integral between them. -/
theorem picard_succ_sub (hw : ∀ i, 0 ≤ w i) (hyp : CKHyp w L s₀ R C K) {m : ℕ}
    (hA : QA w L s₀ R C K m) (hL : QL w L s₀ R C K m) {t t' : ℝ} (ht0 : 0 ≤ t) (ht'0 : 0 ≤ t')
    (ht : t < coneA (ckA C K R) m * s₀) (ht' : t' < coneA (ckA C K R) m * s₀) :
    picard L (m + 1) t - picard L (m + 1) t' = tint (fun τ => L (picard L m τ)) t' t := by
  funext i
  simp only [picard, tint, Pi.sub_apply]
  exact integral_interval_sub_left (intervalIntegrable_L_coeff hw hyp hA hL ht0 ht i)
    (intervalIntegrable_L_coeff hw hyp hA hL ht'0 ht' i)

theorem QL_succ (hw : ∀ i, 0 ≤ w i) (hyp : CKHyp w L s₀ R C K) {m : ℕ}
    (hA : QA w L s₀ R C K m) (hL : QL w L s₀ R C K m) : QL w L s₀ R C K (m + 1) := by
  intro s T hs hs₀ hT hTc
  set a' := coneA (ckA C K R) (m + 1) with ha'
  have ha'0 : 0 < a' := coneA_pos hyp.a_pos _
  have ham : a' ≤ coneA (ckA C K R) m := coneA_succ_le hyp.a_pos.le m
  have hD : 0 < s₀ - s := sub_pos.2 hs₀
  have hTa : T / a' < s₀ - s := by rw [div_lt_iff₀ ha'0]; linarith
  set σ := s + (s₀ - s - T / a') / 2 with hσ
  have hσs : s < σ := by rw [hσ]; linarith
  have hσ₀ : σ < s₀ := by rw [hσ]; have : 0 ≤ T / a' := by positivity
                          linarith
  have hTσ : T < coneA (ckA C K R) m * (s₀ - σ) := by
    have h1 : a' * (s₀ - σ) = (a' * (s₀ - s) + T) / 2 := by rw [hσ]; field_simp; ring
    have h2 : a' * (s₀ - σ) ≤ coneA (ckA C K R) m * (s₀ - σ) :=
      mul_le_mul_of_nonneg_right ham (by linarith)
    linarith
  have hΛ := ckLam_nonneg hyp hs₀ ha'0 hTc
  -- the pointwise bound of the integrand
  have hB : ∀ τ ∈ Icc 0 T, nu w s (L (picard L m τ)) ≤ ENNReal.ofReal (ckLam s₀ C K R s T a') := by
    intro τ hτ
    have hb := ball_of_QA hyp hA (hs.trans hσs.le) hσ₀ hτ.1 (lt_of_le_of_lt hτ.2 hTσ)
    have h0 : nu w σ (0 : ι → V) < ENNReal.ofReal R := by
      rw [nu_zero]; exact ENNReal.ofReal_pos.2 hyp.R_pos
    have hlip := hyp.lip s σ hs hσs hσ₀ _ _ hb h0
    rw [sub_zero] at hlip
    have hu := hA σ τ (hs.trans hσs.le) hσ₀ hτ.1 (lt_of_le_of_lt hτ.2 hTσ)
    calc nu w s (L (picard L m τ)) ≤ nu w s (L (picard L m τ) - L 0) + nu w s (L 0) := by
          have := nu_add_le (w := w) s (L (picard L m τ) - L 0) (L 0)
          rwa [sub_add_cancel] at this
      _ ≤ ENNReal.ofReal (C / (σ - s)) * ENNReal.ofReal (8 * K * ckA C K R) +
          ENNReal.ofReal (K / (s₀ - s)) :=
          add_le_add (hlip.trans (mul_le_mul_right hu _)) (hyp.zero s hs hs₀)
      _ ≤ ENNReal.ofReal (ckLam s₀ C K R s T a') := by
          rw [← ENNReal.ofReal_mul (by have := hyp.C_pos; have := sub_pos.2 hσs; positivity),
            ← ENNReal.ofReal_add (by have := hyp.C_pos; have := sub_pos.2 hσs
                                     have := hyp.K_pos; have := hyp.a_pos; positivity)
              (by have := hyp.K_pos; positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          unfold ckLam
          have hK8 : 8 * K * ckA C K R ≤ R / 2 := by have := hyp.a_K; linarith
          have hσs' : σ - s = (s₀ - s - T / a') / 2 := by rw [hσ]; ring
          have hpos : 0 < s₀ - s - T / a' := by linarith
          have : C / (σ - s) * (8 * K * ckA C K R) ≤ C * R / (s₀ - s - T / a') := by
            have hC := hyp.C_pos
            have hKa := hyp.a_K
            rw [hσs']
            calc C / ((s₀ - s - T / a') / 2) * (8 * K * ckA C K R)
                = C * (16 * K * ckA C K R) / (s₀ - s - T / a') := by field_simp; ring
              _ ≤ C * R / (s₀ - s - T / a') := by gcongr
          linarith
  intro t ht t' ht'
  have hTs₀ : T < coneA (ckA C K R) m * s₀ :=
    lt_of_lt_of_le (lt_of_lt_of_le hTc (mul_le_mul_of_nonneg_right ham hD.le))
      (coneA_mul_le_s₀ hyp hs)
  have hts := lt_of_le_of_lt ht.2 hTs₀
  have ht's := lt_of_le_of_lt ht'.2 hTs₀
  rcases le_total t' t with h | h
  · rw [picard_succ_sub hw hyp hA hL ht.1 ht'.1 hts ht's, abs_of_nonneg (by linarith)]
    exact nu_tint_le_const h hΛ fun τ hτ => hB τ ⟨by linarith [hτ.1, ht'.1], hτ.2.trans ht.2⟩
  · rw [nu_sub_comm, picard_succ_sub hw hyp hA hL ht'.1 ht.1 ht's hts, abs_of_nonpos (by linarith),
      neg_sub]
    exact nu_tint_le_const h hΛ fun τ hτ => hB τ ⟨by linarith [hτ.1, ht.1], hτ.2.trans ht'.2⟩

theorem ckMu_succ (C K a₀ : ℝ) (m : ℕ) : ckMu C K a₀ (m + 1) = 4 * C * a₀ * ckMu C K a₀ m := by
  unfold ckMu; ring

theorem ckMu_nonneg (hyp : CKHyp w L s₀ R C K) (m : ℕ) : 0 ≤ ckMu C K (ckA C K R) m := by
  have := hyp.K_pos; have := hyp.C_pos; have := hyp.a_pos
  unfold ckMu; positivity

theorem QD_succ (hw : ∀ i, 0 ≤ w i) (hyp : CKHyp w L s₀ R C K) {m : ℕ}
    (hA1 : QA w L s₀ R C K (m + 1)) (hA : QA w L s₀ R C K m) (hL1 : QL w L s₀ R C K (m + 1))
    (hL : QL w L s₀ R C K m) (hD : QD w L s₀ R C K m) : QD w L s₀ R C K (m + 1) := by
  intro s t hs hs₀ ht htc
  set a := coneA (ckA C K R) (m + 1) with ha_def
  set am := coneA (ckA C K R) m with ham_def
  have ha : 0 < a := coneA_pos hyp.a_pos _
  have haam : a ≤ am := coneA_succ_le hyp.a_pos.le m
  have hDs : 0 < s₀ - s := sub_pos.2 hs₀
  set A := a * (s₀ - s) with hA_def
  have htA : t < A := htc
  set μ := ckMu C K (ckA C K R) m with hμ
  have hμ0 : 0 ≤ μ := ckMu_nonneg hyp m
  have hC := hyp.C_pos
  -- the difference as one integral
  have hts1 : t < a * s₀ := lt_of_lt_of_le htc (coneA_mul_le_s₀ hyp hs)
  have hts0 : t < am * s₀ := lt_of_lt_of_le hts1 (mul_le_mul_of_nonneg_right haam hyp.s₀_pos.le)
  have e : picard L (m + 2) t - picard L (m + 1) t =
      tint (fun τ => L (picard L (m + 1) τ) - L (picard L m τ)) 0 t := by
    funext i
    simp only [picard, tint, Pi.sub_apply]
    exact (intervalIntegral.integral_sub (intervalIntegrable_L_coeff hw hyp hA1 hL1 ht hts1 i)
      (intervalIntegrable_L_coeff hw hyp hA hL ht hts0 i)).symm
  rw [e]
  set c := 4 * C * a * μ with hc
  have hc0 : 0 ≤ c := by positivity
  have hbound : ∀ τ ∈ Ioc 0 t, nu w s (L (picard L (m + 1) τ) - L (picard L m τ)) ≤
      ENNReal.ofReal (c * (A / (A - τ) ^ 2)) := by
    intro τ hτ
    have hτA : τ < A := lt_of_le_of_lt hτ.2 htA
    have hX : 0 < A - τ := by linarith
    set σ := (s + s₀ - τ / a) / 2 with hσ
    have hτa : τ / a < s₀ - s := by rw [div_lt_iff₀ ha]; linarith
    have hσs : s < σ := by rw [hσ]; linarith
    have hσ₀ : σ < s₀ := by rw [hσ]; have : 0 ≤ τ / a := div_nonneg hτ.1.le ha.le
                            linarith
    have hσs' : σ - s = (A - τ) / (2 * a) := by rw [hσ, hA_def]; field_simp; ring
    have haσ : a * (s₀ - σ) = (A + τ) / 2 := by rw [hσ, hA_def]; field_simp; ring
    have hτ1 : τ < a * (s₀ - σ) := by rw [haσ]; linarith
    have hτ0 : τ < am * (s₀ - σ) :=
      lt_of_lt_of_le hτ1 (mul_le_mul_of_nonneg_right haam (by linarith))
    have hb1 := ball_of_QA hyp hA1 (hs.trans hσs.le) hσ₀ hτ.1.le hτ1
    have hb0 := ball_of_QA hyp hA (hs.trans hσs.le) hσ₀ hτ.1.le hτ0
    have hd := hD σ τ (hs.trans hσs.le) hσ₀ hτ.1.le hτ0
    refine (hyp.lip s σ hs hσs hσ₀ _ _ hb1 hb0).trans ((mul_le_mul_right hd _).trans ?_)
    have hY : (A - τ) / 2 ≤ am * (s₀ - σ) - τ := by
      have : a * (s₀ - σ) ≤ am * (s₀ - σ) := mul_le_mul_of_nonneg_right haam (by linarith)
      linarith
    have hYpos : 0 < am * (s₀ - σ) - τ := lt_of_lt_of_le (by linarith) hY
    rw [← ENNReal.ofReal_mul (by rw [hσs']; positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hσs']
    calc C / ((A - τ) / (2 * a)) * (μ * τ / (am * (s₀ - σ) - τ))
        = 2 * a * C * μ * τ / ((A - τ) * (am * (s₀ - σ) - τ)) := by
          field_simp
      _ ≤ 2 * a * C * μ * τ / ((A - τ) * ((A - τ) / 2)) := by
          apply div_le_div_of_nonneg_left (by have := hτ.1.le; positivity) (by positivity)
          exact mul_le_mul_of_nonneg_left hY hX.le
      _ = c * (τ / (A - τ) ^ 2) := by rw [hc]; field_simp; ring
      _ ≤ c * (A / (A - τ) ^ 2) := by
          refine mul_le_mul_of_nonneg_left ?_ hc0
          exact div_le_div_of_nonneg_right (le_trans hτ.2 htA.le) (by positivity)
  have hint : IntervalIntegrable (fun τ => c * (A / (A - τ) ^ 2)) volume 0 t := by
    refine ContinuousOn.intervalIntegrable ?_
    intro τ hτ
    rw [uIcc_of_le ht] at hτ
    have hne : A - τ ≠ 0 := by linarith [hτ.2]
    exact (continuousAt_const.mul (continuousAt_const.div
      ((continuousAt_const.sub continuousAt_id).pow 2) (pow_ne_zero 2 hne))).continuousWithinAt
  refine (nu_tint_le_integral ht hint (fun τ hτ => by
      have : 0 < A - τ := by linarith [hτ.2]
      positivity) hbound).trans (ENNReal.ofReal_le_ofReal ?_)
  rw [intervalIntegral.integral_const_mul, integral_inv_sq ht htA]
  have hpos : 0 < A - t := by linarith
  rw [ckMu_succ, ← hμ, mul_div_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (div_nonneg ht hpos.le)
  rw [hc]
  have : a ≤ ckA C K R := coneA_le hyp.a_pos.le _
  have : 0 ≤ 4 * C * μ := by positivity
  nlinarith

theorem QA_succ (hyp : CKHyp w L s₀ R C K) {m : ℕ} (hD : ∀ k ≤ m, QD w L s₀ R C K k) :
    QA w L s₀ R C K (m + 1) := by
  intro s t hs hs₀ ht htc
  have ha := hyp.a_pos
  have hDs : 0 < s₀ - s := sub_pos.2 hs₀
  have htel : picard L (m + 1) t = ∑ k ∈ Finset.range (m + 1), (picard L (k + 1) t - picard L k t) := by
    rw [Finset.sum_range_sub (fun k => picard L k t)]
    simp [picard]
  rw [htel]
  refine (nu_finset_sum_le s _ _).trans ?_
  have hterm : ∀ k ∈ Finset.range (m + 1), nu w s (picard L (k + 1) t - picard L k t) ≤
      ENNReal.ofReal (4 * K * ckA C K R * (16 * C * ckA C K R) ^ k) := by
    intro k hk
    have hkm : k ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    have hk1 : t ≤ coneA (ckA C K R) (k + 1) * (s₀ - s) :=
      htc.le.trans (mul_le_mul_of_nonneg_right (coneA_anti ha.le (by omega)) hDs.le)
    have htk : t < coneA (ckA C K R) k * (s₀ - s) :=
      lt_of_lt_of_le htc (mul_le_mul_of_nonneg_right (coneA_anti ha.le (by omega)) hDs.le)
    refine (hD k hkm s t hs hs₀ ht htk).trans (ENNReal.ofReal_le_ofReal ?_)
    have hr := (ratio_le ha hDs ht k hk1).trans (ratio_le_pow k)
    rw [mul_div_assoc]
    calc ckMu C K (ckA C K R) k * (t / (coneA (ckA C K R) k * (s₀ - s) - t))
        ≤ ckMu C K (ckA C K R) k * 4 ^ (k + 1) :=
          mul_le_mul_of_nonneg_left hr (ckMu_nonneg hyp k)
      _ = 4 * K * ckA C K R * (16 * C * ckA C K R) ^ k := by
          unfold ckMu
          have h16 : (16 * C * ckA C K R) ^ k = 4 ^ k * (4 * C * ckA C K R) ^ k := by
            rw [← mul_pow]; ring_nf
          rw [h16, pow_succ]; ring
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => by
    have := hyp.K_pos; have := hyp.C_pos; positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← Finset.mul_sum]
  have hq0 : 0 ≤ 16 * C * ckA C K R := by have := hyp.C_pos; positivity
  have hq1 : 16 * C * ckA C K R < 1 := by have := hyp.a_C; linarith
  have hgeom := geom_sum_Ico_le_of_lt_one (m := 0) (n := m + 1) hq0 hq1
  rw [Finset.range_eq_Ico]
  have h2 : 1 / (1 - 16 * C * ckA C K R) ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]; have := hyp.a_C; linarith
  have h4 : 0 ≤ 4 * K * ckA C K R := by have := hyp.K_pos; positivity
  calc 4 * K * ckA C K R * ∑ i ∈ Finset.Ico 0 (m + 1), (16 * C * ckA C K R) ^ i
      ≤ 4 * K * ckA C K R * 2 := by
        refine mul_le_mul_of_nonneg_left ?_ h4
        refine hgeom.trans ?_
        simpa using h2
    _ = 8 * K * ckA C K R := by ring

/-- **The iterates stay in the ball, are time-Lipschitz on their cones, and their differences obey
Nishida's weighted bounds.** -/
theorem picard_bounds (hw : ∀ i, 0 ≤ w i) (hyp : CKHyp w L s₀ R C K) :
    ∀ m, (∀ k ≤ m, QA w L s₀ R C K k ∧ QL w L s₀ R C K k) ∧ ∀ k < m, QD w L s₀ R C K k := by
  intro m
  induction m with
  | zero =>
    refine ⟨fun k hk => ?_, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
    rw [Nat.le_zero.1 hk]; exact ⟨QA_zero, QL_zero⟩
  | succ m ih =>
    obtain ⟨hAL, hD⟩ := ih
    have hDm : QD w L s₀ R C K m := by
      rcases m with _ | m
      · exact QD_zero hyp
      · exact QD_succ hw hyp (hAL (m + 1) le_rfl).1 (hAL m (by omega)).1 (hAL (m + 1) le_rfl).2
          (hAL m (by omega)).2 (hD m (by omega))
    have hD' : ∀ k < m + 1, QD w L s₀ R C K k := fun k hk => by
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with h | h
      · exact hD k h
      · rw [h]; exact hDm
    refine ⟨fun k hk => ?_, hD'⟩
    rcases Nat.le_succ_iff.1 hk with h | h
    · exact hAL k h
    · rw [h]
      exact ⟨QA_succ hyp fun k hk => hD' k (by omega),
        QL_succ hw hyp (hAL m le_rfl).1 (hAL m le_rfl).2⟩

end Steps

/-! ### The limit: the analytic solution -/

section Limit

variable {w : ι → ℝ} {L : (ι → V) → ι → V} {s₀ R C K : ℝ}

/-- The ratio of the Nishida weights. -/
theorem ck_ratio (hyp : CKHyp w L s₀ R C K) : 0 ≤ 4 * C * ckA C K R ∧ 4 * C * ckA C K R ≤ 1 / 8 := by
  have := hyp.C_pos; have := hyp.a_pos; have := hyp.a_C
  constructor <;> [positivity; linarith]

theorem sum_ckMu_Ico_le (hyp : CKHyp w L s₀ R C K) (k m : ℕ) :
    ∑ j ∈ Finset.Ico k m, ckMu C K (ckA C K R) j ≤ 2 * ckMu C K (ckA C K R) k := by
  obtain ⟨h0, h1⟩ := ck_ratio hyp
  have hg := geom_sum_Ico_le_of_lt_one (m := k) (n := m) h0 (by linarith)
  have hKa : 0 ≤ K * ckA C K R := by have := hyp.K_pos; have := hyp.a_pos; positivity
  unfold ckMu
  rw [← Finset.mul_sum]
  calc K * ckA C K R * ∑ i ∈ Finset.Ico k m, (4 * C * ckA C K R) ^ i
      ≤ K * ckA C K R * ((4 * C * ckA C K R) ^ k / (1 - 4 * C * ckA C K R)) :=
        mul_le_mul_of_nonneg_left hg hKa
    _ ≤ K * ckA C K R * ((4 * C * ckA C K R) ^ k * 2) := by
        refine mul_le_mul_of_nonneg_left ?_ hKa
        rw [div_le_iff₀ (by linarith)]
        have := pow_nonneg h0 k
        nlinarith
    _ = _ := by ring

theorem tendsto_ckMu (hyp : CKHyp w L s₀ R C K) :
    Tendsto (fun k => ckMu C K (ckA C K R) k) atTop (𝓝 0) := by
  obtain ⟨h0, h1⟩ := ck_ratio hyp
  have := (tendsto_pow_atTop_nhds_zero_of_lt_one h0 (by linarith)).const_mul (K * ckA C K R)
  simpa [ckMu] using this

variable (hw : ∀ i, 0 ≤ w i) (hyp : CKHyp w L s₀ R C K)
include hw hyp

/-- The difference bound on the limiting cone `t < (a₀/2)(s₀ - s)`. -/
theorem delta_le_on_half (k : ℕ) {s t : ℝ} (hs : 0 ≤ s) (hs₀ : s < s₀) (ht : 0 ≤ t)
    (htc : t < ckA C K R / 2 * (s₀ - s)) :
    nu w s (picard L (k + 1) t - picard L k t) ≤
      ENNReal.ofReal (ckMu C K (ckA C K R) k * (t / (ckA C K R / 2 * (s₀ - s) - t))) := by
  have hD := ((picard_bounds hw hyp (k + 1)).2 k (by omega))
  have hDs : 0 < s₀ - s := sub_pos.2 hs₀
  have hhalf : ckA C K R / 2 * (s₀ - s) ≤ coneA (ckA C K R) k * (s₀ - s) :=
    mul_le_mul_of_nonneg_right (half_le_coneA hyp.a_pos.le k) hDs.le
  refine (hD s t hs hs₀ ht (lt_of_lt_of_le htc hhalf)).trans (ENNReal.ofReal_le_ofReal ?_)
  rw [mul_div_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (ckMu_nonneg hyp k)
  exact div_le_div_of_nonneg_left ht (by linarith) (by linarith)

theorem QA_all (k : ℕ) : QA w L s₀ R C K k := ((picard_bounds hw hyp k).1 k le_rfl).1

theorem QL_all (k : ℕ) : QL w L s₀ R C K k := ((picard_bounds hw hyp k).1 k le_rfl).2

theorem coneA_half_le (k : ℕ) {s : ℝ} (hs₀ : s < s₀) :
    ckA C K R / 2 * (s₀ - s) ≤ coneA (ckA C K R) k * (s₀ - s) :=
  mul_le_mul_of_nonneg_right (half_le_coneA hyp.a_pos.le k) (sub_pos.2 hs₀).le

variable [CompleteSpace V]

theorem cauchySeq_picard {t : ℝ} (ht : 0 ≤ t) (hta : t < ckA C K R / 2 * s₀) (i : ι) :
    CauchySeq fun k => picard L k t i := by
  have hpos : 0 < ckA C K R / 2 * (s₀ - 0) - t := by rw [sub_zero]; linarith
  refine cauchySeq_of_dist_le_of_summable
    (fun k => ckMu C K (ckA C K R) k * (t / (ckA C K R / 2 * (s₀ - 0) - t))) (fun k => ?_) ?_
  · rw [dist_comm, dist_eq_norm, ← ENNReal.ofReal_le_ofReal_iff (by
      have := ckMu_nonneg hyp k; positivity), ofReal_norm_eq_enorm]
    have := (enorm_le_nu hw le_rfl (picard L (k + 1) t - picard L k t) i).trans
      (delta_le_on_half hw hyp k le_rfl hyp.s₀_pos ht (by rwa [sub_zero]))
    simpa only [Pi.sub_apply] using this
  · obtain ⟨h0, h1⟩ := ck_ratio hyp
    have hs : Summable fun k => ckMu C K (ckA C K R) k :=
      (summable_geometric_of_lt_one h0 (by linarith)).mul_left _
    exact hs.mul_right _

/-- The limit of the Picard iterates (coefficientwise). -/
def ckSol (L : (ι → V) → ι → V) (t : ℝ) : ι → V := fun i => limUnder atTop fun k => picard L k t i

theorem tendsto_ckSol {t : ℝ} (ht : 0 ≤ t) (hta : t < ckA C K R / 2 * s₀) (i : ι) :
    Tendsto (fun k => picard L k t i) atTop (𝓝 (ckSol L t i)) :=
  tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete (cauchySeq_picard hw hyp ht hta i))

theorem ckSol_ball {s t : ℝ} (hs : 0 ≤ s) (hs₀ : s < s₀) (ht : 0 ≤ t)
    (htc : t < ckA C K R / 2 * (s₀ - s)) :
    nu w s (ckSol L t) ≤ ENNReal.ofReal (8 * K * ckA C K R) := by
  have hta : t < ckA C K R / 2 * s₀ := lt_of_lt_of_le htc
    (mul_le_mul_of_nonneg_left (by linarith) (by have := hyp.a_pos; positivity))
  refine nu_le_of_tendsto (fun i => tendsto_ckSol hw hyp ht hta i) (Eventually.of_forall fun k => ?_)
  exact QA_all hw hyp k s t hs hs₀ ht (lt_of_lt_of_le htc (coneA_half_le hw hyp k hs₀))

/-- The tail bound `ν_s(u(t) - u_k(t)) ≤ 2 μ_k t/((a₀/2)(s₀ - s) - t)`. -/
theorem ckSol_tail (k : ℕ) {s t : ℝ} (hs : 0 ≤ s) (hs₀ : s < s₀) (ht : 0 ≤ t)
    (htc : t < ckA C K R / 2 * (s₀ - s)) :
    nu w s (ckSol L t - picard L k t) ≤
      ENNReal.ofReal (2 * ckMu C K (ckA C K R) k * (t / (ckA C K R / 2 * (s₀ - s) - t))) := by
  have hta : t < ckA C K R / 2 * s₀ := lt_of_lt_of_le htc
    (mul_le_mul_of_nonneg_left (by linarith) (by have := hyp.a_pos; positivity))
  set W := t / (ckA C K R / 2 * (s₀ - s) - t) with hW
  have hW0 : 0 ≤ W := div_nonneg ht (by linarith)
  have hpart : ∀ m, k ≤ m → nu w s (picard L m t - picard L k t) ≤
      ENNReal.ofReal (W * ∑ j ∈ Finset.Ico k m, ckMu C K (ckA C K R) j) := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => simp [nu_zero]
    | succ m hkm ih =>
      have e : picard L (m + 1) t - picard L k t =
          (picard L m t - picard L k t) + (picard L (m + 1) t - picard L m t) := by abel
      rw [e, Finset.sum_Ico_succ_top hkm, mul_add, ENNReal.ofReal_add
        (mul_nonneg hW0 (Finset.sum_nonneg fun j _ => ckMu_nonneg hyp j))
        (mul_nonneg hW0 (ckMu_nonneg hyp m))]
      refine (nu_add_le s _ _).trans (add_le_add ih ?_)
      rw [mul_comm W]
      exact delta_le_on_half hw hyp m hs hs₀ ht htc
  refine nu_le_of_tendsto (c := fun m => picard L m t - picard L k t)
    (fun i => (tendsto_ckSol hw hyp ht hta i).sub_const _) ?_
  filter_upwards [eventually_ge_atTop k] with m hm
  refine (hpart m hm).trans (ENNReal.ofReal_le_ofReal ?_)
  rw [mul_comm W]
  exact mul_le_mul_of_nonneg_right (sum_ckMu_Ico_le hyp k m) hW0

/-- **Uniform convergence of the coefficients of `L` along the iterates** on `[0, t]`. -/
theorem L_coeff_uniform {t : ℝ} (ht : 0 ≤ t) (hta : t < ckA C K R / 2 * s₀) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ k, ∀ τ ∈ Icc 0 t, ∀ i,
      ‖L (picard L k τ) i - L (ckSol L τ) i‖ ≤ B * ckMu C K (ckA C K R) k := by
  set a := ckA C K R / 2 with ha_def
  have ha : 0 < a := by have := hyp.a_pos; positivity
  set σ := (s₀ - t / a) / 2 with hσ
  have htas : t / a < s₀ := by rw [div_lt_iff₀ ha]; linarith
  have hσ0 : 0 < σ := by rw [hσ]; linarith
  have hσs : σ < s₀ := by rw [hσ]; have : 0 ≤ t / a := by positivity
                          linarith
  have haσ : a * (s₀ - σ) = (a * s₀ + t) / 2 := by rw [hσ]; field_simp; ring
  have htσ : t < a * (s₀ - σ) := by rw [haσ]; linarith
  have hC := hyp.C_pos
  set Wst := t / (a * (s₀ - σ) - t) with hWst
  have hWst0 : 0 ≤ Wst := div_nonneg ht (by linarith)
  refine ⟨C / σ * (2 * Wst), by positivity, fun k τ hτ i => ?_⟩
  have hτσ : τ < a * (s₀ - σ) := lt_of_le_of_lt hτ.2 htσ
  have hb1 := ball_of_QA hyp (QA_all hw hyp k) hσ0.le hσs hτ.1
    (lt_of_lt_of_le hτσ (coneA_half_le hw hyp k hσs))
  have hb2 : nu w σ (ckSol L τ) < ENNReal.ofReal R := by
    refine (ckSol_ball hw hyp hσ0.le hσs hτ.1 hτσ).trans_lt
      ((ENNReal.ofReal_lt_ofReal_iff hyp.R_pos).2 ?_)
    have := hyp.a_K; have := hyp.a_pos; have := hyp.K_pos; nlinarith
  have h1 := hyp.lip 0 σ le_rfl hσ0 hσs _ _ hb1 hb2
  have h2 := ckSol_tail hw hyp k hσ0.le hσs hτ.1 hτσ
  rw [nu_sub_comm] at h2
  have hWτ : τ / (a * (s₀ - σ) - τ) ≤ Wst := frac_mono hτ.1 hτ.2 htσ
  have hfin : ‖L (picard L k τ) i - L (ckSol L τ) i‖ₑ ≤
      ENNReal.ofReal (C / σ * (2 * Wst) * ckMu C K (ckA C K R) k) := by
    refine (enorm_le_nu hw le_rfl _ i).trans (h1.trans ?_)
    rw [sub_zero]
    refine (mul_le_mul_right h2 _).trans ?_
    rw [← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hμ := ckMu_nonneg hyp k
    have : 2 * ckMu C K (ckA C K R) k * (τ / (a * (s₀ - σ) - τ)) ≤
        2 * ckMu C K (ckA C K R) k * Wst := mul_le_mul_of_nonneg_left hWτ (by positivity)
    calc C / σ * (2 * ckMu C K (ckA C K R) k * (τ / (a * (s₀ - σ) - τ)))
        ≤ C / σ * (2 * ckMu C K (ckA C K R) k * Wst) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by ring
  rwa [← ofReal_norm_eq_enorm, ENNReal.ofReal_le_ofReal_iff (by
    have := ckMu_nonneg hyp k; positivity)] at hfin

theorem continuousOn_L_ckSol {t : ℝ} (ht : 0 ≤ t) (hta : t < ckA C K R / 2 * s₀) (i : ι) :
    ContinuousOn (fun τ => L (ckSol L τ) i) (Icc 0 t) := by
  obtain ⟨B, hB0, hB⟩ := L_coeff_uniform hw hyp ht hta
  have hU : TendstoUniformlyOn (fun k τ => L (picard L k τ) i) (fun τ => L (ckSol L τ) i) atTop
      (Icc 0 t) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hlim := (tendsto_ckMu hyp).const_mul B
    rw [mul_zero] at hlim
    filter_upwards [hlim.eventually (gt_mem_nhds hε)] with k hk τ hτ
    rw [dist_comm, dist_eq_norm]
    exact lt_of_le_of_lt (hB k τ hτ i) hk
  refine hU.continuousOn (Frequently.of_forall fun k => ?_)
  have hk := coneA_half_le hw hyp k (s := 0) hyp.s₀_pos
  rw [sub_zero] at hk
  exact continuousOn_L_coeff hw hyp (QA_all hw hyp k) (QL_all hw hyp k) ht (lt_of_lt_of_le hta hk) i

/-- **The integral equation** `u(t) = ∫₀ᵗ L(u(τ)) dτ`. -/
theorem ckSol_integral {t : ℝ} (ht : 0 ≤ t) (hta : t < ckA C K R / 2 * s₀) (i : ι) :
    ckSol L t i = ∫ τ in (0 : ℝ)..t, L (ckSol L τ) i := by
  obtain ⟨B, hB0, hB⟩ := L_coeff_uniform hw hyp ht hta
  have h1 : Tendsto (fun k => picard L (k + 1) t i) atTop (𝓝 (ckSol L t i)) :=
    (tendsto_ckSol hw hyp ht hta i).comp (tendsto_add_atTop_nat 1)
  have hint : IntervalIntegrable (fun τ => L (ckSol L τ) i) volume 0 t :=
    (continuousOn_L_ckSol hw hyp ht hta i).intervalIntegrable_of_Icc ht
  have h2 : Tendsto (fun k => picard L (k + 1) t i) atTop
      (𝓝 (∫ τ in (0 : ℝ)..t, L (ckSol L τ) i)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hlim := ((tendsto_ckMu hyp).const_mul B).const_mul t
    rw [mul_zero, mul_zero] at hlim
    refine squeeze_zero (fun _ => norm_nonneg _) (fun k => ?_) hlim
    have hk := coneA_half_le hw hyp k (s := 0) hyp.s₀_pos
    rw [sub_zero] at hk
    have hintk := intervalIntegrable_L_coeff hw hyp (QA_all hw hyp k) (QL_all hw hyp k) ht
      (lt_of_lt_of_le hta hk) i
    show ‖(∫ τ in (0 : ℝ)..t, L (picard L k τ) i) - ∫ τ in (0 : ℝ)..t, L (ckSol L τ) i‖ ≤ _
    rw [← intervalIntegral.integral_sub hintk hint]
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := B * ckMu C K (ckA C K R) k)
      fun τ hτ => ?_).trans (le_of_eq ?_)
    · rw [uIoc_of_le ht] at hτ
      exact hB k τ ⟨hτ.1.le, hτ.2⟩ i
    · rw [sub_zero, abs_of_nonneg ht]; ring
  exact tendsto_nhds_unique h1 h2

theorem ckSol_zero : ckSol L 0 = 0 := by
  funext i
  have h := tendsto_ckSol hw hyp le_rfl (by have := hyp.a_pos; have := hyp.s₀_pos; positivity) i
  simp only [picard_zero_time, Pi.zero_apply] at h
  exact (tendsto_nhds_unique h tendsto_const_nhds)

/-- **The differential equation** `∂_t u = L(u)` on `0 < t < (a₀/2) s₀` (coefficientwise). -/
theorem ckSol_hasDerivAt {t : ℝ} (ht : 0 < t) (hta : t < ckA C K R / 2 * s₀) (i : ι) :
    HasDerivAt (fun τ => ckSol L τ i) (L (ckSol L t) i) t := by
  set T' := (t + ckA C K R / 2 * s₀) / 2 with hT'
  have htT : t < T' := by rw [hT']; linarith
  have hT'a : T' < ckA C K R / 2 * s₀ := by rw [hT']; linarith
  have hc := continuousOn_L_ckSol hw hyp (ht.le.trans htT.le) hT'a i
  have hco : ContinuousOn (fun τ => L (ckSol L τ) i) (Ioo 0 T') := hc.mono Ioo_subset_Icc_self
  have hint : IntervalIntegrable (fun τ => L (ckSol L τ) i) volume 0 t :=
    (hc.mono (Icc_subset_Icc le_rfl htT.le)).intervalIntegrable_of_Icc ht.le
  have hd := intervalIntegral.integral_hasDerivAt_right hint
    (hco.stronglyMeasurableAtFilter isOpen_Ioo t ⟨ht, htT⟩)
    (hco.continuousAt (Ioo_mem_nhds ht htT))
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds ht hta] with τ hτ
  exact ckSol_integral hw hyp hτ.1.le hτ.2 i

/-- **The abstract Cauchy–Kovalevskaya theorem** (Nirenberg–Nishida, in the analytic scale
`ν_s`).  Under Nishida's hypotheses `CKHyp` (Lipschitz `C/(s - s')` on the ball `ν_s < R` for
`0 ≤ s' < s < s₀`, `ν_s(L 0) ≤ K/(s₀ - s)`) and with `a = min(1/(32C), R/(16K))/2`, there is
`u : ℝ → ι → V` with
* `u(0) = 0`;
* `ν_s(u(t)) ≤ R/2` for `0 ≤ s < s₀`, `0 ≤ t < a(s₀ - s)` (analytic in a strip of width
  `s₀ - t/a`, shrinking linearly in time);
* `u(t) = ∫₀ᵗ L(u(τ)) dτ` coefficientwise for `0 ≤ t < a s₀`, and `∂_t u = L(u)` on `(0, a s₀)`.
The existence time `a s₀` depends only on the strip width `s₀` and on `C, K, R`. -/
theorem cauchy_kovalevskaya :
    ∃ u : ℝ → ι → V, u 0 = 0 ∧
      (∀ s t : ℝ, 0 ≤ s → s < s₀ → 0 ≤ t → t < ckA C K R / 2 * (s₀ - s) →
        nu w s (u t) ≤ ENNReal.ofReal (R / 2)) ∧
      (∀ t : ℝ, 0 ≤ t → t < ckA C K R / 2 * s₀ → ∀ i, u t i = ∫ τ in (0 : ℝ)..t, L (u τ) i) ∧
      (∀ t : ℝ, 0 < t → t < ckA C K R / 2 * s₀ → ∀ i,
        HasDerivAt (fun τ => u τ i) (L (u t) i) t) := by
  refine ⟨ckSol L, ckSol_zero hw hyp, fun s t hs hs₀ ht htc => ?_,
    fun t ht hta i => ckSol_integral hw hyp ht hta i,
    fun t ht hta i => ckSol_hasDerivAt hw hyp ht hta i⟩
  refine (ckSol_ball hw hyp hs hs₀ ht htc).trans (ENNReal.ofReal_le_ofReal ?_)
  have := hyp.a_K; linarith

end Limit
end RenewalGeometry.CKScale
