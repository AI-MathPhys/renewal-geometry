/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Graded Taylor expansion of analytic maps along rays, with uniform remainders

General machinery (used for `lem:supp-exact-slow-expansion` of the emergent-spacetime
manuscript).  For a map `f : E → F` with a power series `p` at `0`:

* `AnalyticRay.partialSum_smul`: `p.partialSum k (a • η) = ∑_{m<k} a^m • p_m(η, …, η)`.
* `AnalyticRay.ray_taylor_uniform`: **uniform graded Taylor bound along rays.**  For every
  `ρ` there are `a₀ > 0`, `C` with
  `‖f (a • η) - ∑_{m<k} a^m • p_m(η^m)‖ ≤ C |a|^k` for all `|a| < a₀`, `‖η‖ ≤ ρ`.
* `AnalyticRay.poly_coeff_eq_zero`: a polynomial `∑_{m<k} a^m • c_m` which is `O(a^k)` as
  `a → 0⁺` has `c_m = 0` for all `m < k`.
* `AnalyticRay.coeff_eq_zero_of_norm_le`: if `‖f (a • η)‖ ≤ C a^k` for small `a > 0`, then
  `p_m(η^m) = 0` for `m < k`.
* `AnalyticRay.ray_remainder_bound`: if moreover the coefficients below order `k` vanish on
  a set of directions, then `f(a • η) = a^k • p_k(η^k) + a^{k+1} • Rem(a, η)` with `Rem`
  uniformly bounded on bounded direction sets for small `a`.
* Expansions of symmetric bi- and trilinear maps on a sum `e + u`
  (`sym2_add_add`, `sym3_add_add_add`) and their instances for iterated derivatives of
  analytic maps (`iteratedFDeriv_two_add`, `iteratedFDeriv_three_add`), with
  `iteratedFDeriv_eq_factorial_coeff` relating `D^n f(0)[η^n]` to `n! • p_n(η^n)`.
-/

open Filter Set Finset
open scoped Topology NNReal ENNReal BigOperators

namespace RenewalGeometry
namespace AnalyticRay

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ### Partial sums along rays -/

/-- The `m`-th term of a formal multilinear series on the diagonal is homogeneous of degree
`m` along rays. -/
theorem coeff_smul (p : FormalMultilinearSeries ℝ E F) (m : ℕ) (a : ℝ) (η : E) :
    p m (fun _ => a • η) = a ^ m • p m (fun _ => η) := by
  rw [show (fun _ : Fin m => a • η) = fun i => (fun _ : Fin m => a) i • (fun _ : Fin m => η) i
    from rfl, ContinuousMultilinearMap.map_smul_univ]
  simp [Finset.prod_const, Finset.card_univ]

/-- `p.partialSum k (a • η) = ∑_{m<k} a^m • p_m(η, …, η)`. -/
theorem partialSum_smul (p : FormalMultilinearSeries ℝ E F) (k : ℕ) (a : ℝ) (η : E) :
    p.partialSum k (a • η) = ∑ m ∈ range k, a ^ m • p m (fun _ => η) := by
  simp only [FormalMultilinearSeries.partialSum, coeff_smul]

/-! ### Polynomials which are `O(a^k)` at `0⁺` -/

/-- A polynomial `∑_{m<k} a^m • c_m` with `‖·‖ ≤ C a^k` for `0 < a < δ` has all its
coefficients zero. -/
theorem poly_coeff_eq_zero (k : ℕ) :
    ∀ (c : ℕ → F) (δ C : ℝ), 0 < δ →
      (∀ a : ℝ, 0 < a → a < δ → ‖∑ m ∈ range k, a ^ m • c m‖ ≤ C * a ^ k) →
      ∀ m < k, c m = 0 := by
  induction k with
  | zero => intro c δ C _ _ m hm; exact absurd hm (Nat.not_lt_zero _)
  | succ k ih =>
    intro c δ C hδ h
    -- the polynomial and its limit at `0⁺`
    set S : ℝ → F := fun a => ∑ m ∈ range (k + 1), a ^ m • c m with hS
    have hScont : Continuous S := by
      refine continuous_finsetSum _ fun m _ => ?_
      exact (continuous_pow m).smul continuous_const
    have hS0 : S 0 = c 0 := by
      simp only [hS]
      rw [Finset.sum_range_succ']
      simp
    have hlim1 : Tendsto S (𝓝[>] (0 : ℝ)) (𝓝 (c 0)) := by
      rw [← hS0]; exact hScont.continuousAt.continuousWithinAt.tendsto
    have hlim2 : Tendsto S (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hg : Tendsto (fun a : ℝ => C * a ^ (k + 1)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        have : Tendsto (fun a : ℝ => C * a ^ (k + 1)) (𝓝 (0 : ℝ)) (𝓝 (C * 0 ^ (k + 1))) :=
          (continuous_const.mul (continuous_pow _)).tendsto 0
        simpa using this.mono_left nhdsWithin_le_nhds
      refine squeeze_zero_norm' ?_ hg
      filter_upwards [Ioo_mem_nhdsGT hδ] with a ha
      exact h a ha.1 ha.2
    have hc0 : c 0 = 0 := tendsto_nhds_unique hlim1 hlim2
    -- divide by `a`
    have h' : ∀ a : ℝ, 0 < a → a < δ →
        ‖∑ m ∈ range k, a ^ m • c (m + 1)‖ ≤ C * a ^ k := by
      intro a ha haδ
      have hsplit : ∑ m ∈ range (k + 1), a ^ m • c m
          = a • ∑ m ∈ range k, a ^ m • c (m + 1) := by
        rw [Finset.sum_range_succ', hc0, smul_zero, add_zero, Finset.smul_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [smul_smul, pow_succ, mul_comm]
      have := h a ha haδ
      rw [hsplit, norm_smul, Real.norm_eq_abs, abs_of_pos ha, pow_succ] at this
      have : a * ‖∑ m ∈ range k, a ^ m • c (m + 1)‖ ≤ a * (C * a ^ k) := by linarith
      exact le_of_mul_le_mul_left this ha
    intro m hm
    rcases m with _ | m
    · exact hc0
    · exact ih (fun m => c (m + 1)) δ C hδ h' m (by omega)

/-! ### Uniform graded Taylor bound along rays -/

/-- **Uniform graded Taylor bound along rays.**  If `f` has the power series `p` on a ball
around `0`, then for every radius `ρ` of directions there are `a₀ > 0` and `C` such that
`‖f (a • η) - ∑_{m<k} a^m • p_m(η^m)‖ ≤ C |a|^k` for all `|a| < a₀` and `‖η‖ ≤ ρ`. -/
theorem ray_taylor_uniform {f : E → F} {p : FormalMultilinearSeries ℝ E F} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f p 0 r) (k : ℕ) (ρ : ℝ) :
    ∃ a₀ > 0, ∃ C, ∀ a : ℝ, |a| < a₀ → ∀ η : E, ‖η‖ ≤ ρ →
      ‖f (a • η) - ∑ m ∈ range k, a ^ m • p m (fun _ => η)‖ ≤ C * |a| ^ k := by
  obtain ⟨r', hr'0, hr'r⟩ : ∃ r' : ℝ≥0, (0 : ℝ≥0∞) < r' ∧ (r' : ℝ≥0∞) < r :=
    ENNReal.lt_iff_exists_nnreal_btwn.mp hf.r_pos
  have hr'pos : (0 : ℝ) < r' := by exact_mod_cast ENNReal.coe_pos.mp hr'0
  obtain ⟨α, hα, C, hC, hbound⟩ := hf.uniform_geometric_approx' hr'r
  set ρ' := max ρ 0 + 1 with hρ'
  have hρ'pos : 0 < ρ' := by positivity
  refine ⟨r' / ρ', div_pos hr'pos hρ'pos, C * (ρ' / r') ^ k, ?_⟩
  intro a ha η hη
  have hnorm : ‖a • η‖ ≤ |a| * ρ' := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (by rw [hρ']; linarith [le_max_left ρ 0]) (abs_nonneg a)
  have hlt : ‖a • η‖ < r' := by
    calc ‖a • η‖ ≤ |a| * ρ' := hnorm
      _ < r' / ρ' * ρ' := mul_lt_mul_of_pos_right ha hρ'pos
      _ = r' := div_mul_cancel₀ _ hρ'pos.ne'
  have hmem : a • η ∈ Metric.ball (0 : E) r' := by simpa using hlt
  have h1 := hbound (a • η) hmem k
  rw [zero_add, partialSum_smul] at h1
  refine h1.trans ?_
  have hαle : α * (‖a • η‖ / r') ≤ |a| * ρ' / r' := by
    have h2 : ‖a • η‖ / r' ≤ |a| * ρ' / r' := div_le_div_of_nonneg_right hnorm hr'pos.le
    have h3 : 0 ≤ ‖a • η‖ / r' := by positivity
    calc α * (‖a • η‖ / r') ≤ 1 * (‖a • η‖ / r') :=
          mul_le_mul_of_nonneg_right hα.2.le h3
      _ ≤ |a| * ρ' / r' := by rw [one_mul]; exact h2
  have h0 : 0 ≤ α * (‖a • η‖ / r') := mul_nonneg hα.1.le (by positivity)
  calc C * (α * (‖a • η‖ / r')) ^ k ≤ C * (|a| * ρ' / r') ^ k :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 hαle k) hC.le
    _ = C * (ρ' / r') ^ k * |a| ^ k := by rw [mul_div_assoc, mul_pow]; ring

/-- If `‖f (a • η)‖ ≤ C a^k` for `0 < a < δ`, then the ray coefficients `p_m(η^m)` vanish for
all `m < k`. -/
theorem coeff_eq_zero_of_norm_le {f : E → F} {p : FormalMultilinearSeries ℝ E F} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f p 0 r) (η : E) (k : ℕ) {δ C : ℝ} (hδ : 0 < δ)
    (h : ∀ a : ℝ, 0 < a → a < δ → ‖f (a • η)‖ ≤ C * a ^ k) :
    ∀ m < k, p m (fun _ => η) = 0 := by
  obtain ⟨a₀, ha₀, C', hC'⟩ := ray_taylor_uniform hf k ‖η‖
  refine poly_coeff_eq_zero k (fun m => p m (fun _ => η)) (min δ a₀) (C + C')
    (lt_min hδ ha₀) ?_
  intro a ha haδ
  have h1 := hC' a (by rw [abs_of_pos ha]; exact haδ.trans_le (min_le_right _ _)) η le_rfl
  have h2 := h a ha (haδ.trans_le (min_le_left _ _))
  rw [abs_of_pos ha] at h1
  calc ‖∑ m ∈ range k, a ^ m • p m (fun _ => η)‖
      = ‖f (a • η) - (f (a • η) - ∑ m ∈ range k, a ^ m • p m (fun _ => η))‖ := by
        rw [sub_sub_cancel]
    _ ≤ ‖f (a • η)‖ + ‖f (a • η) - ∑ m ∈ range k, a ^ m • p m (fun _ => η)‖ :=
        norm_sub_le _ _
    _ ≤ C * a ^ k + C' * a ^ k := add_le_add h2 h1
    _ = (C + C') * a ^ k := by ring

/-- **Graded remainder along rays.**  If the ray coefficients of order `< k` vanish for all
directions in `S`, then on every bounded part of `S` the map along rays is
`f (a • η) = a^k • p_k(η^k) + a^(k+1) • Rem(a, η)` with
`Rem(a, η) = (a^(k+1))⁻¹ • (f (a • η) - a^k • p_k(η^k))` uniformly bounded for small `a ≠ 0`. -/
theorem ray_remainder_bound {f : E → F} {p : FormalMultilinearSeries ℝ E F} {r : ℝ≥0∞}
    (hf : HasFPowerSeriesOnBall f p 0 r) (k : ℕ) (S : Set E)
    (hS : ∀ η ∈ S, ∀ m < k, p m (fun _ => η) = 0) (ρ : ℝ) :
    ∃ a₀ > 0, ∃ C, ∀ a : ℝ, a ≠ 0 → |a| < a₀ → ∀ η ∈ S, ‖η‖ ≤ ρ →
      ‖(a ^ (k + 1))⁻¹ • (f (a • η) - a ^ k • p k (fun _ => η))‖ ≤ C := by
  obtain ⟨a₀, ha₀, C, hC⟩ := ray_taylor_uniform hf (k + 1) ρ
  refine ⟨a₀, ha₀, C, fun a ha0 ha η hη hηρ => ?_⟩
  have h1 := hC a ha η hηρ
  have hsum : ∑ m ∈ range (k + 1), a ^ m • p m (fun _ => η) = a ^ k • p k (fun _ => η) := by
    rw [Finset.sum_range_succ, Finset.sum_eq_zero (fun m hm => by
      rw [hS η hη m (Finset.mem_range.mp hm), smul_zero]), zero_add]
  rw [hsum] at h1
  rw [norm_smul, norm_inv, norm_pow, Real.norm_eq_abs]
  have hpos : 0 < |a| ^ (k + 1) := pow_pos (abs_pos.mpr ha0) _
  rw [inv_mul_le_iff₀ hpos, mul_comm]
  exact h1

/-! ### Symmetric multilinear expansions -/

section Symmetric

variable (q2 : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) F)
  (q3 : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) F)

theorem diag_two (v : E) : q2 (fun _ => v) = q2 ![v, v] := by
  congr 1; funext i; fin_cases i <;> rfl

theorem diag_three (v : E) : q3 (fun _ => v) = q3 ![v, v, v] := by
  congr 1; funext i; fin_cases i <;> rfl

theorem two_add_left (x x' y : E) : q2 ![x + x', y] = q2 ![x, y] + q2 ![x', y] :=
  q2.cons_add _ x x'

theorem two_add_right (x y y' : E) : q2 ![x, y + y'] = q2 ![x, y] + q2 ![x, y'] := by
  have h := q2.map_update_add ![x, y] 1 y y'
  have e1 : Function.update ![x, y] 1 (y + y') = ![x, y + y'] := by
    funext i; fin_cases i <;> simp
  have e2 : Function.update ![x, y] 1 y = ![x, y] := by funext i; fin_cases i <;> simp
  have e3 : Function.update ![x, y] 1 y' = ![x, y'] := by funext i; fin_cases i <;> simp
  rw [e1, e2, e3] at h; exact h

theorem three_add_0 (x x' y z : E) : q3 ![x + x', y, z] = q3 ![x, y, z] + q3 ![x', y, z] :=
  q3.cons_add _ x x'

theorem three_add_1 (x y y' z : E) : q3 ![x, y + y', z] = q3 ![x, y, z] + q3 ![x, y', z] := by
  have h := q3.map_update_add ![x, y, z] 1 y y'
  have e1 : Function.update ![x, y, z] 1 (y + y') = ![x, y + y', z] := by
    funext i; fin_cases i <;> simp
  have e2 : Function.update ![x, y, z] 1 y = ![x, y, z] := by funext i; fin_cases i <;> simp
  have e3 : Function.update ![x, y, z] 1 y' = ![x, y', z] := by funext i; fin_cases i <;> simp
  rw [e1, e2, e3] at h; exact h

theorem three_add_2 (x y z z' : E) : q3 ![x, y, z + z'] = q3 ![x, y, z] + q3 ![x, y, z'] := by
  have h := q3.map_update_add ![x, y, z] 2 z z'
  have e1 : Function.update ![x, y, z] 2 (z + z') = ![x, y, z + z'] := by
    funext i; fin_cases i <;> simp
  have e2 : Function.update ![x, y, z] 2 z = ![x, y, z] := by funext i; fin_cases i <;> simp
  have e3 : Function.update ![x, y, z] 2 z' = ![x, y, z'] := by funext i; fin_cases i <;> simp
  rw [e1, e2, e3] at h; exact h

theorem two_smul_right (x y : E) (c : ℝ) : q2 ![x, c • y] = c • q2 ![x, y] := by
  have h := q2.map_update_smul ![x, y] 1 c y
  have e1 : Function.update ![x, y] 1 (c • y) = ![x, c • y] := by
    funext i; fin_cases i <;> simp
  have e2 : Function.update ![x, y] 1 y = ![x, y] := by funext i; fin_cases i <;> simp
  rw [e1, e2] at h; exact h

theorem two_smul_left (x y : E) (c : ℝ) : q2 ![c • x, y] = c • q2 ![x, y] := by
  have h := q2.map_update_smul ![x, y] 0 c x
  have e1 : Function.update ![x, y] 0 (c • x) = ![c • x, y] := by
    funext i; fin_cases i <;> simp
  have e2 : Function.update ![x, y] 0 x = ![x, y] := by funext i; fin_cases i <;> simp
  rw [e1, e2] at h; exact h

theorem three_smul_1 (x y z : E) (c : ℝ) : q3 ![x, c • y, z] = c • q3 ![x, y, z] := by
  have h := q3.map_update_smul ![x, y, z] 1 c y
  have e1 : Function.update ![x, y, z] 1 (c • y) = ![x, c • y, z] := by
    funext i; fin_cases i <;> simp
  have e2 : Function.update ![x, y, z] 1 y = ![x, y, z] := by funext i; fin_cases i <;> simp
  rw [e1, e2] at h; exact h

theorem three_smul_2 (x y z : E) (c : ℝ) : q3 ![x, y, c • z] = c • q3 ![x, y, z] := by
  have h := q3.map_update_smul ![x, y, z] 2 c z
  have e1 : Function.update ![x, y, z] 2 (c • z) = ![x, y, c • z] := by
    funext i; fin_cases i <;> simp
  have e2 : Function.update ![x, y, z] 2 z = ![x, y, z] := by funext i; fin_cases i <;> simp
  rw [e1, e2] at h; exact h

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The linear map `ξ ↦ q₂(x, ι ξ)`. -/
def linOfTwo (x : E) (ι : V →ₗ[ℝ] E) : V →ₗ[ℝ] F where
  toFun ξ := q2 ![x, ι ξ]
  map_add' ξ ζ := by simp only [map_add, two_add_right]
  map_smul' c ξ := by simp only [map_smul, two_smul_right, RingHom.id_apply]

/-- The bilinear map `(ξ, ζ) ↦ q₂(ι ξ, ι ζ)`. -/
def bilOfTwo (ι : V →ₗ[ℝ] E) : V →ₗ[ℝ] V →ₗ[ℝ] F :=
  LinearMap.mk₂ ℝ (fun ξ ζ => q2 ![ι ξ, ι ζ])
    (fun ξ ξ' ζ => by simp only [map_add, two_add_left])
    (fun c ξ ζ => by simp only [map_smul, two_smul_left])
    (fun ξ ζ ζ' => by simp only [map_add, two_add_right])
    (fun c ξ ζ => by simp only [map_smul, two_smul_right])

/-- The linear map `ξ ↦ q₃(x, y, ι ξ)`. -/
def linOfThree (x y : E) (ι : V →ₗ[ℝ] E) : V →ₗ[ℝ] F where
  toFun ξ := q3 ![x, y, ι ξ]
  map_add' ξ ζ := by simp only [map_add, three_add_2]
  map_smul' c ξ := by simp only [map_smul, three_smul_2, RingHom.id_apply]

/-- The bilinear map `(ξ, ζ) ↦ q₃(x, ι ξ, ι ζ)`. -/
def bilOfThree (x : E) (ι : V →ₗ[ℝ] E) : V →ₗ[ℝ] V →ₗ[ℝ] F :=
  LinearMap.mk₂ ℝ (fun ξ ζ => q3 ![x, ι ξ, ι ζ])
    (fun ξ ξ' ζ => by simp only [map_add, three_add_1])
    (fun c ξ ζ => by simp only [map_smul, three_smul_1])
    (fun ξ ζ ζ' => by simp only [map_add, three_add_2])
    (fun c ξ ζ => by simp only [map_smul, three_smul_2])

@[simp] theorem linOfTwo_apply (x : E) (ι : V →ₗ[ℝ] E) (ξ : V) :
    linOfTwo q2 x ι ξ = q2 ![x, ι ξ] := rfl

@[simp] theorem bilOfTwo_apply (ι : V →ₗ[ℝ] E) (ξ ζ : V) :
    bilOfTwo q2 ι ξ ζ = q2 ![ι ξ, ι ζ] := rfl

@[simp] theorem linOfThree_apply (x y : E) (ι : V →ₗ[ℝ] E) (ξ : V) :
    linOfThree q3 x y ι ξ = q3 ![x, y, ι ξ] := rfl

@[simp] theorem bilOfThree_apply (x : E) (ι : V →ₗ[ℝ] E) (ξ ζ : V) :
    bilOfThree q3 x ι ξ ζ = q3 ![x, ι ξ, ι ζ] := rfl

/-- Expansion of a symmetric bilinear map on `e + u`. -/
theorem sym2_add_add (hsymm : ∀ x y, q2 ![x, y] = q2 ![y, x]) (e u : E) :
    q2 ![e + u, e + u] = q2 ![e, e] + (2 : ℝ) • q2 ![e, u] + q2 ![u, u] := by
  rw [two_add_left, two_add_right, two_add_right, hsymm u e, two_smul]
  abel

/-- Expansion of a symmetric trilinear map on `e + u`. -/
theorem sym3_add_add_add (h01 : ∀ x y z, q3 ![x, y, z] = q3 ![y, x, z])
    (h12 : ∀ x y z, q3 ![x, y, z] = q3 ![x, z, y]) (e u : E) :
    q3 ![e + u, e + u, e + u]
      = q3 ![e, e, e] + (3 : ℝ) • q3 ![e, e, u] + (3 : ℝ) • q3 ![e, u, u] + q3 ![u, u, u] := by
  simp only [three_add_0, three_add_1, three_add_2]
  -- normalise every term to the forms `eee, eeu, euu, uuu`
  have a1 : q3 ![e, u, e] = q3 ![e, e, u] := h12 _ _ _
  have a2 : q3 ![u, e, e] = q3 ![e, e, u] := by rw [h01, h12]
  have a3 : q3 ![u, e, u] = q3 ![e, u, u] := h01 _ _ _
  have a4 : q3 ![u, u, e] = q3 ![e, u, u] := by rw [h12, h01]
  rw [a1, a2, a3, a4]
  have h3 : ∀ w : F, (3 : ℝ) • w = w + w + w := fun w => by
    rw [show (3 : ℝ) = 1 + 1 + 1 by norm_num, add_smul, add_smul, one_smul]
  rw [h3, h3]
  abel

end Symmetric

/-! ### Iterated derivatives of analytic maps -/

section Iterated

variable [CompleteSpace F]

/-- `D^n f(0)[η, …, η] = n! • p_n(η^n)` for a map with power series `p` at `0`. -/
theorem iteratedFDeriv_eq_factorial_coeff {f : E → F} {p : FormalMultilinearSeries ℝ E F}
    {r : ℝ≥0∞} (hf : HasFPowerSeriesOnBall f p 0 r) (n : ℕ) (η : E) :
    iteratedFDeriv ℝ n f 0 (fun _ => η) = (n.factorial : ℝ) • p n (fun _ => η) := by
  rw [← hf.factorial_smul η n, Nat.cast_smul_eq_nsmul]

/-- Symmetry of the second derivative of a map analytic at `0`, in `![x, y]` form. -/
theorem iteratedFDeriv_two_symm {f : E → F} (hf : AnalyticAt ℝ f 0) (x y : E) :
    iteratedFDeriv ℝ 2 f 0 ![x, y] = iteratedFDeriv ℝ 2 f 0 ![y, x] := by
  have h := hf.contDiffAt.iteratedFDeriv_comp_perm (n := 2) ![x, y] (Equiv.swap 0 1)
  rw [← h]; congr 1; funext i; fin_cases i <;> simp

theorem iteratedFDeriv_three_symm01 {f : E → F} (hf : AnalyticAt ℝ f 0) (x y z : E) :
    iteratedFDeriv ℝ 3 f 0 ![x, y, z] = iteratedFDeriv ℝ 3 f 0 ![y, x, z] := by
  have h := hf.contDiffAt.iteratedFDeriv_comp_perm (n := 3) ![x, y, z] (Equiv.swap 0 1)
  rw [← h]; congr 1; funext i; fin_cases i <;> simp [Equiv.swap_apply_of_ne_of_ne]

theorem iteratedFDeriv_three_symm12 {f : E → F} (hf : AnalyticAt ℝ f 0) (x y z : E) :
    iteratedFDeriv ℝ 3 f 0 ![x, y, z] = iteratedFDeriv ℝ 3 f 0 ![x, z, y] := by
  have h := hf.contDiffAt.iteratedFDeriv_comp_perm (n := 3) ![x, y, z] (Equiv.swap 1 2)
  rw [← h]; congr 1; funext i; fin_cases i <;> simp [Equiv.swap_apply_of_ne_of_ne]

/-- `D²f(0)[e+u, e+u] = D²f(0)[e,e] + 2 D²f(0)[e,u] + D²f(0)[u,u]` for analytic `f`. -/
theorem iteratedFDeriv_two_add {f : E → F} (hf : AnalyticAt ℝ f 0) (e u : E) :
    iteratedFDeriv ℝ 2 f 0 ![e + u, e + u]
      = iteratedFDeriv ℝ 2 f 0 ![e, e] + (2 : ℝ) • iteratedFDeriv ℝ 2 f 0 ![e, u]
        + iteratedFDeriv ℝ 2 f 0 ![u, u] :=
  sym2_add_add _ (iteratedFDeriv_two_symm hf) e u

/-- The trilinear expansion of `D³f(0)` on `e + u` for analytic `f`. -/
theorem iteratedFDeriv_three_add {f : E → F} (hf : AnalyticAt ℝ f 0) (e u : E) :
    iteratedFDeriv ℝ 3 f 0 ![e + u, e + u, e + u]
      = iteratedFDeriv ℝ 3 f 0 ![e, e, e] + (3 : ℝ) • iteratedFDeriv ℝ 3 f 0 ![e, e, u]
        + (3 : ℝ) • iteratedFDeriv ℝ 3 f 0 ![e, u, u] + iteratedFDeriv ℝ 3 f 0 ![u, u, u] :=
  sym3_add_add_add _ (iteratedFDeriv_three_symm01 hf) (iteratedFDeriv_three_symm12 hf) e u

end Iterated

end AnalyticRay
end RenewalGeometry
