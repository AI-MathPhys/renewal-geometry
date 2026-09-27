/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.Analysis.LineTaylorRemainderBound

/-!
# The reversible coframe Renewal packet on a chart

Paper `predictive_spectral_geometry`, label `thm:supp-general-renewal-process`
(and the finite surrogate of `cth:supp-metric-no-coframe`).

A `CoframePacket` consists of a finite bank of lattice directions `r`
(`R_d^+` in the paper), coefficients `a_r(x) = ρ(x) w_r(x)` and the density
`ρ = sqrt(det g)`.  Following `eq:supp-general-conductance` the vertex mass is
`m_h(x) = h^d ρ(x)` and the conductance of the edge `x → x + h r` is
`c_h(x,r) = h^{d-2}/4 (a_r(x) + a_r(x + h r))`; the two directed rates are the
conductance divided by the endpoint mass.

* `detailed_balance`: the packet is reversible with stationary mass `m_h`.
* `bracket_eq` (`eq:supp-general-bracket`): the predictable coordinate bracket is
  `(4ρ)⁻¹ Σ_r [a_r(x+hr) + 2a_r(x) + a_r(x-hr)] r rᵀ`.
* `abs_bracket_sub_inverseMetric_le` (`eq:supp-general-bracket-error`): entrywise
  `|B_h - g⁻¹| ≤ C h²` with `g⁻¹ = ρ⁻¹ Σ_r a_r r rᵀ` (`inverseMetric`; this is
  `eq:supp-positive-decomposition`, see `inverseMetric_eq_of_decomposition`).
* `abs_generator_sub_laplaceBeltrami_le` (`eq:supp-general-generator`): for
  `f ∈ C⁴` with bounded differentials, `|L_h f - ½ Δ_g f| ≤ C h²` uniformly in `x`,
  with `Δ_g f = ρ⁻¹ Σ_r ∂_r(a_r ∂_r f)` written in directional form
  (`laplaceBeltrami`), and `C` linear in the `C⁴` bounds of `f`.

The Dirichlet-form limit `eq:supp-general-form-limit` (Riemann sums on the
torus) is not treated here.  The packet lives on the chart `ℝ^d` (the paper's
periodic torus `hℤ^d/ℤ^d` only affects the global summation).
-/

open Matrix Finset
open RenewalGeometry.LineTaylorRemainderBound

namespace RenewalGeometry.CoframeRenewalPacket

variable {d : ℕ} {ι : Type*} [Fintype ι]

/-- A lattice direction bank with coefficients `a_r` and density `ρ`. -/
structure CoframePacket (d : ℕ) (ι : Type*) where
  /-- lattice directions `r ∈ R_d^+` -/
  dir : ι → (Fin d → ℝ)
  /-- the coefficients `a_r(x) = ρ(x) w_r(x)` -/
  coeff : ι → (Fin d → ℝ) → ℝ
  /-- the density `ρ = sqrt(det g)` -/
  density : (Fin d → ℝ) → ℝ

namespace CoframePacket

variable (P : CoframePacket d ι)

noncomputable section

/-- Vertex mass `m_h(x) = h^d ρ(x)`. -/
def mass (h : ℝ) (x : Fin d → ℝ) : ℝ := h ^ d * P.density x

/-- Conductance `c_h(x, r) = h^{d-2}/4 (a_r(x) + a_r(x + h r))`. -/
def conductance (h : ℝ) (x : Fin d → ℝ) (r : ι) : ℝ :=
  h ^ (d - 2) / 4 * (P.coeff r x + P.coeff r (x + h • P.dir r))

/-- Rate of the jump `x → x + h r`. -/
def forwardRate (h : ℝ) (x : Fin d → ℝ) (r : ι) : ℝ := P.conductance h x r / P.mass h x

/-- Rate of the jump `x → x - h r`. -/
def backwardRate (h : ℝ) (x : Fin d → ℝ) (r : ι) : ℝ :=
  P.conductance h (x - h • P.dir r) r / P.mass h x

/-- The generator `L_h f (x) = Σ_r [k⁺(x,r) (f(x+hr) - f(x)) + k⁻(x,r) (f(x-hr) - f(x))]`. -/
def generator (h : ℝ) (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ :=
  ∑ r, (P.forwardRate h x r * (f (x + h • P.dir r) - f x) +
    P.backwardRate h x r * (f (x - h • P.dir r) - f x))

/-- The predictable coordinate bracket `B_h(x) = Σ_r [k⁺ + k⁻] h² r rᵀ`. -/
def bracket (h : ℝ) (x : Fin d → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  ∑ r, ((P.forwardRate h x r + P.backwardRate h x r) * h ^ 2) • vecMulVec (P.dir r) (P.dir r)

/-- The inverse metric reconstructed from the coefficients, `g⁻¹ = ρ⁻¹ Σ_r a_r r rᵀ`. -/
def inverseMetric (x : Fin d → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  (P.density x)⁻¹ • ∑ r, P.coeff r x • vecMulVec (P.dir r) (P.dir r)

/-- The Laplace–Beltrami operator in directional divergence form,
`Δ_g f = ρ⁻¹ Σ_r ∂_r (a_r ∂_r f) = ρ⁻¹ Σ_r [(∂_r a_r)(∂_r f) + a_r ∂_r² f]`. -/
def laplaceBeltrami (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ :=
  (P.density x)⁻¹ * ∑ r, (fderiv ℝ (P.coeff r) x (P.dir r) * fderiv ℝ f x (P.dir r) +
    P.coeff r x * fderiv ℝ (fderiv ℝ f) x (P.dir r) (P.dir r))

/-- The coefficients decompose `ρ g⁻¹` (`eq:supp-positive-decomposition` with
`a_r = ρ w_r`). -/
def IsDecomposition (ginv : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ) : Prop :=
  ∀ x, P.density x • ginv x = ∑ r, P.coeff r x • vecMulVec (P.dir r) (P.dir r)

theorem inverseMetric_eq_of_decomposition {ginv : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ}
    (hg : P.IsDecomposition ginv) {x : Fin d → ℝ} (hρ : P.density x ≠ 0) :
    P.inverseMetric x = ginv x := by
  rw [inverseMetric, ← hg x, smul_smul, inv_mul_cancel₀ hρ, one_smul]

/-! ### Reversibility -/

omit [Fintype ι] in
/-- **Detailed balance.** `m_h(x) k(x → x + hr) = m_h(x + hr) k(x + hr → x)`: the
packet is reversible with stationary mass `m_h`. -/
theorem detailed_balance (h : ℝ) (x : Fin d → ℝ) (r : ι) (hm : P.mass h x ≠ 0)
    (hm' : P.mass h (x + h • P.dir r) ≠ 0) :
    P.mass h x * P.forwardRate h x r =
      P.mass h (x + h • P.dir r) * P.backwardRate h (x + h • P.dir r) r := by
  unfold forwardRate backwardRate
  rw [add_sub_cancel_right, mul_div_cancel₀ _ hm, mul_div_cancel₀ _ hm']

/-! ### The exact bracket formula -/

theorem pow_eq_pow_sub_two_mul (h : ℝ) (hd : 2 ≤ d) : h ^ d = h ^ (d - 2) * h ^ 2 := by
  rw [← pow_add, Nat.sub_add_cancel hd]

omit [Fintype ι] in
/-- The bracket coefficient of one direction. -/
theorem rate_sum_mul_sq (h : ℝ) (hh : h ≠ 0) (hd : 2 ≤ d) (x : Fin d → ℝ)
    (hρ : P.density x ≠ 0) (r : ι) :
    (P.forwardRate h x r + P.backwardRate h x r) * h ^ 2 =
      (4 * P.density x)⁻¹ *
        (P.coeff r (x + h • P.dir r) + 2 * P.coeff r x + P.coeff r (x - h • P.dir r)) := by
  unfold forwardRate backwardRate conductance mass
  rw [sub_add_cancel, pow_eq_pow_sub_two_mul h hd]
  have hpow : h ^ (d - 2) ≠ 0 := pow_ne_zero _ hh
  field_simp
  ring

/-- **`eq:supp-general-bracket`.** -/
theorem bracket_eq (h : ℝ) (hh : h ≠ 0) (hd : 2 ≤ d) (x : Fin d → ℝ) (hρ : P.density x ≠ 0) :
    P.bracket h x = (4 * P.density x)⁻¹ • ∑ r,
      (P.coeff r (x + h • P.dir r) + 2 * P.coeff r x + P.coeff r (x - h • P.dir r)) •
        vecMulVec (P.dir r) (P.dir r) := by
  unfold bracket
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [smul_smul, P.rate_sum_mul_sq h hh hd x hρ r]

/-! ### The bracket error -/

omit [Fintype ι] in
/-- Second symmetric difference of a coefficient along its direction. -/
theorem abs_second_difference_le (r : ι) (hC : ContDiff ℝ 2 (P.coeff r)) {A2 : ℝ}
    (hA2 : ∀ y, ‖iteratedFDeriv ℝ 2 (P.coeff r) y‖ ≤ A2) (x : Fin d → ℝ) (h : ℝ) :
    |P.coeff r (x + h • P.dir r) - 2 * P.coeff r x + P.coeff r (x - h • P.dir r)| ≤
      A2 * ‖P.dir r‖ ^ 2 * h ^ 2 := by
  set α := lineMap (P.coeff r) x (P.dir r)
  have hα : ContDiff ℝ 2 α := contDiff_lineMap hC x (P.dir r)
  have hb : ∀ t, |iteratedDeriv 2 α t| ≤ A2 * ‖P.dir r‖ ^ 2 :=
    abs_iteratedDeriv_lineMap_le_of_bound hC le_rfl hA2 x (P.dir r)
  have hp := abs_sub_taylor_one_le α _ hα hb 0 h
  have hm := abs_sub_taylor_one_le α _ hα hb 0 (-h)
  simp only [sub_zero, abs_neg] at hp hm
  have e1 : P.coeff r (x + h • P.dir r) = α h := by simp [α, lineMap]
  have e2 : P.coeff r (x - h • P.dir r) = α (-h) := by simp [α, lineMap, sub_eq_add_neg]
  have e3 : P.coeff r x = α 0 := by simp [α, lineMap]
  rw [e1, e2, e3]
  have hsq : |h| ^ 2 = h ^ 2 := sq_abs h
  rw [hsq] at hp hm
  calc |α h - 2 * α 0 + α (-h)|
      = |(α h - (α 0 + h * iteratedDeriv 1 α 0)) + (α (-h) - (α 0 + -h * iteratedDeriv 1 α 0))| := by
        ring_nf
    _ ≤ |α h - (α 0 + h * iteratedDeriv 1 α 0)| + |α (-h) - (α 0 + -h * iteratedDeriv 1 α 0)| :=
        abs_add_le _ _
    _ ≤ A2 * ‖P.dir r‖ ^ 2 * h ^ 2 / 2 + A2 * ‖P.dir r‖ ^ 2 * h ^ 2 / 2 := add_le_add hp hm
    _ = A2 * ‖P.dir r‖ ^ 2 * h ^ 2 := by ring

/-- **`eq:supp-general-bracket-error`** (entrywise). -/
theorem abs_bracket_sub_inverseMetric_le (h : ℝ) (hh : h ≠ 0) (hd : 2 ≤ d) (x : Fin d → ℝ)
    (hρ : P.density x ≠ 0) (hC : ∀ r, ContDiff ℝ 2 (P.coeff r)) (A2 : ι → ℝ)
    (hA2 : ∀ r y, ‖iteratedFDeriv ℝ 2 (P.coeff r) y‖ ≤ A2 r) (i j : Fin d) :
    |P.bracket h x i j - P.inverseMetric x i j| ≤
      h ^ 2 * ((4 * |P.density x|)⁻¹ * ∑ r, A2 r * ‖P.dir r‖ ^ 2 * |P.dir r i * P.dir r j|) := by
  rw [P.bracket_eq h hh hd x hρ, inverseMetric]
  simp only [Matrix.smul_apply, Matrix.sum_apply, vecMulVec_apply, smul_eq_mul]
  have hid : (4 * P.density x)⁻¹ * ∑ r,
      (P.coeff r (x + h • P.dir r) + 2 * P.coeff r x + P.coeff r (x - h • P.dir r)) *
        (P.dir r i * P.dir r j) -
      (P.density x)⁻¹ * ∑ r, P.coeff r x * (P.dir r i * P.dir r j) =
      (4 * P.density x)⁻¹ * ∑ r,
        (P.coeff r (x + h • P.dir r) - 2 * P.coeff r x + P.coeff r (x - h • P.dir r)) *
          (P.dir r i * P.dir r j) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    field_simp
    ring
  rw [hid, abs_mul, abs_inv, abs_mul (4 : ℝ) (P.density x), abs_of_pos (by norm_num : (0:ℝ) < 4)]
  calc (4 * |P.density x|)⁻¹ * |∑ r,
        (P.coeff r (x + h • P.dir r) - 2 * P.coeff r x + P.coeff r (x - h • P.dir r)) *
          (P.dir r i * P.dir r j)|
      ≤ (4 * |P.density x|)⁻¹ * ∑ r, A2 r * ‖P.dir r‖ ^ 2 * h ^ 2 * |P.dir r i * P.dir r j| := by
        refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (by positivity))
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun r _ => ?_)
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (P.abs_second_difference_le r (hC r) (hA2 r) x h)
          (abs_nonneg _)
    _ = h ^ 2 * ((4 * |P.density x|)⁻¹ * ∑ r, A2 r * ‖P.dir r‖ ^ 2 * |P.dir r i * P.dir r j|) := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun r _ => ?_
        ring

/-! ### Generator consistency -/

/-- The per-direction consistency constant: the product-expansion constant with the
line bounds `F_k ‖r‖^k` and `A_k ‖r‖^k`. -/
def directionConstant (F : ℕ → ℝ) (A : ℕ → ℝ) (r : Fin d → ℝ) : ℝ :=
  productExpansionConstant (F 1 * ‖r‖ ^ 1) (F 2 * ‖r‖ ^ 2) (F 3 * ‖r‖ ^ 3) (F 4 * ‖r‖ ^ 4)
    (A 0 * ‖r‖ ^ 0) (A 1 * ‖r‖ ^ 1) (A 2 * ‖r‖ ^ 2) (A 3 * ‖r‖ ^ 3)

omit [Fintype ι] in
/-- One direction of the generator, in line coordinates. -/
theorem generator_term_eq (h : ℝ) (hh : h ≠ 0) (hd : 2 ≤ d) (x : Fin d → ℝ)
    (hρ : P.density x ≠ 0) (f : (Fin d → ℝ) → ℝ) (hf : ContDiff ℝ 4 f) (r : ι)
    (hC : ContDiff ℝ 3 (P.coeff r)) :
    P.forwardRate h x r * (f (x + h • P.dir r) - f x) +
        P.backwardRate h x r * (f (x - h • P.dir r) - f x) -
      (1 / 2) * ((P.density x)⁻¹ *
        (fderiv ℝ (P.coeff r) x (P.dir r) * fderiv ℝ f x (P.dir r) +
          P.coeff r x * fderiv ℝ (fderiv ℝ f) x (P.dir r) (P.dir r))) =
      (4 * h ^ 2 * P.density x)⁻¹ *
        ((lineMap (P.coeff r) x (P.dir r) 0 + lineMap (P.coeff r) x (P.dir r) h) *
            (lineMap f x (P.dir r) h - lineMap f x (P.dir r) 0) +
          (lineMap (P.coeff r) x (P.dir r) (-h) + lineMap (P.coeff r) x (P.dir r) 0) *
            (lineMap f x (P.dir r) (-h) - lineMap f x (P.dir r) 0) -
          2 * h ^ 2 * (lineMap (P.coeff r) x (P.dir r) 0 *
              iteratedDeriv 2 (lineMap f x (P.dir r)) 0 +
            iteratedDeriv 1 (lineMap (P.coeff r) x (P.dir r)) 0 *
              iteratedDeriv 1 (lineMap f x (P.dir r)) 0)) := by
  rw [iteratedDeriv_one_lineMap_zero hf (by norm_num), iteratedDeriv_two_lineMap_zero hf (by norm_num),
    iteratedDeriv_one_lineMap_zero hC (by norm_num)]
  unfold forwardRate backwardRate conductance mass
  rw [sub_add_cancel, pow_eq_pow_sub_two_mul h hd]
  simp only [lineMap_apply, zero_smul, add_zero, neg_smul, ← sub_eq_add_neg]
  have hpow : h ^ (d - 2) ≠ 0 := pow_ne_zero _ hh
  field_simp
  ring

/-- **`eq:supp-general-generator`.** For `f ∈ C⁴` with global differential bounds
`‖D^k f‖ ≤ F k` (`1 ≤ k ≤ 4`) and coefficients in `C³` with `‖D^k a_r‖ ≤ A r k`
(`k ≤ 3`), for `0 < h ≤ 1`, uniformly in `x`:
`|L_h f(x) - ½ Δ_g f(x)| ≤ h² (4|ρ(x)|)⁻¹ Σ_r directionConstant F (A r) r`.
The constant is linear in the `C⁴` bounds of `f`. -/
theorem abs_generator_sub_laplaceBeltrami_le (h : ℝ) (hh : 0 < h) (hh1 : h ≤ 1) (hd : 2 ≤ d)
    (x : Fin d → ℝ) (hρ : P.density x ≠ 0) (f : (Fin d → ℝ) → ℝ) (hf : ContDiff ℝ 4 f)
    (F : ℕ → ℝ) (hF : ∀ k, 1 ≤ k → k ≤ 4 → ∀ y, ‖iteratedFDeriv ℝ k f y‖ ≤ F k)
    (hC : ∀ r, ContDiff ℝ 3 (P.coeff r)) (A : ι → ℕ → ℝ)
    (hA : ∀ r k, k ≤ 3 → ∀ y, ‖iteratedFDeriv ℝ k (P.coeff r) y‖ ≤ A r k) :
    |P.generator h f x - (1 / 2) * P.laplaceBeltrami f x| ≤
      h ^ 2 * ((4 * |P.density x|)⁻¹ * ∑ r, directionConstant F (A r) (P.dir r)) := by
  have hsplit : P.generator h f x - (1 / 2) * P.laplaceBeltrami f x =
      ∑ r, (P.forwardRate h x r * (f (x + h • P.dir r) - f x) +
          P.backwardRate h x r * (f (x - h • P.dir r) - f x) -
        (1 / 2) * ((P.density x)⁻¹ *
          (fderiv ℝ (P.coeff r) x (P.dir r) * fderiv ℝ f x (P.dir r) +
            P.coeff r x * fderiv ℝ (fderiv ℝ f) x (P.dir r) (P.dir r)))) := by
    unfold generator laplaceBeltrami
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [hsplit]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun r _ => ?_
  rw [P.generator_term_eq h hh.ne' hd x hρ f hf r (hC r), abs_mul]
  set φ := lineMap f x (P.dir r)
  set α := lineMap (P.coeff r) x (P.dir r)
  have hφ : ContDiff ℝ 4 φ := contDiff_lineMap hf x (P.dir r)
  have hα : ContDiff ℝ 3 α := contDiff_lineMap (hC r) x (P.dir r)
  have hF' : ∀ k, 1 ≤ k → k ≤ 4 → ∀ t, |iteratedDeriv k φ t| ≤ F k * ‖P.dir r‖ ^ k :=
    fun k hk1 hk4 => abs_iteratedDeriv_lineMap_le_of_bound hf hk4 (hF k hk1 hk4) x (P.dir r)
  have hA' : ∀ k, k ≤ 3 → ∀ t, |iteratedDeriv k α t| ≤ A r k * ‖P.dir r‖ ^ k :=
    fun k hk => abs_iteratedDeriv_lineMap_le_of_bound (hC r) hk (hA r k hk) x (P.dir r)
  have hA0 : ∀ t, |α t| ≤ A r 0 * ‖P.dir r‖ ^ 0 := by
    intro t
    have := hA' 0 (by norm_num) t
    simpa using this
  have hbound := symmetric_product_expansion_bound φ α hφ hα _ _ _ _ _ _ _ _
    (hF' 1 (by norm_num) (by norm_num)) (hF' 2 (by norm_num) (by norm_num))
    (hF' 3 (by norm_num) (by norm_num)) (hF' 4 (by norm_num) (by norm_num))
    hA0 (hA' 1 (by norm_num)) (hA' 2 (by norm_num)) (hA' 3 (by norm_num)) h hh hh1
  have hpos : 0 < 4 * h ^ 2 * |P.density x| := by positivity
  calc |(4 * h ^ 2 * P.density x)⁻¹| *
        |(α 0 + α h) * (φ h - φ 0) + (α (-h) + α 0) * (φ (-h) - φ 0) -
          2 * h ^ 2 * (α 0 * iteratedDeriv 2 φ 0 + iteratedDeriv 1 α 0 * iteratedDeriv 1 φ 0)|
      ≤ (4 * h ^ 2 * |P.density x|)⁻¹ * (directionConstant F (A r) (P.dir r) * h ^ 4) := by
        rw [abs_inv, abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 4),
          abs_of_pos (by positivity : (0:ℝ) < h ^ 2)]
        exact mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hpos.le)
    _ = h ^ 2 * ((4 * |P.density x|)⁻¹ * directionConstant F (A r) (P.dir r)) := by
        field_simp

/-! ### The divergence form of the Laplace–Beltrami operator -/

/-- The paper's coordinate Laplace–Beltrami operator `Δ_g f = ρ⁻¹ ∂_i (ρ g^{ij} ∂_j f)`. -/
def divergenceLaplacian (ρ : (Fin d → ℝ) → ℝ) (ginv : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ)
    (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ :=
  (ρ x)⁻¹ * ∑ i, fderiv ℝ (fun y => ∑ j, ρ y * ginv y i j * fderiv ℝ f y (Pi.single j 1)) x
    (Pi.single i 1)

omit [Fintype ι] in
theorem fderiv_apply_eq_sum_single (f : (Fin d → ℝ) → ℝ) (y r : Fin d → ℝ) :
    fderiv ℝ f y r = ∑ j, r j * fderiv ℝ f y (Pi.single j 1) := by
  have hr : r = ∑ j, r j • (Pi.single j (1 : ℝ) : Fin d → ℝ) := by
    funext i
    simp [Pi.single_apply]
  conv_lhs => rw [hr]
  rw [map_sum]
  simp [map_smul]

/-- `Δ_g f = ρ⁻¹ Σ_r ∂_r (a_r ∂_r f)`: under the decomposition `ρ g⁻¹ = Σ_r a_r r rᵀ`,
the coordinate divergence form equals the directional form `laplaceBeltrami`
(for `f ∈ C²` and `a_r ∈ C¹`). -/
theorem divergenceLaplacian_eq_laplaceBeltrami
    {ginv : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ} (hg : P.IsDecomposition ginv)
    (f : (Fin d → ℝ) → ℝ) (hf : ContDiff ℝ 2 f) (hC : ∀ r, ContDiff ℝ 1 (P.coeff r))
    (x : Fin d → ℝ) :
    divergenceLaplacian P.density ginv f x = P.laplaceBeltrami f x := by
  unfold divergenceLaplacian laplaceBeltrami
  congr 1
  -- differentiability of `y ↦ (fderiv f y) r` and of the coefficients
  have hdf : ∀ r : ι, Differentiable ℝ fun y => fderiv ℝ f y (P.dir r) := fun r =>
    ((hf.fderiv_right (m := 1) le_rfl).differentiable one_ne_zero).clm_apply
      (differentiable_const _)
  have hda : ∀ r, Differentiable ℝ (P.coeff r) := fun r => (hC r).differentiable one_ne_zero
  -- the inner function in directional form
  have hinner : ∀ i : Fin d, (fun y => ∑ j, P.density y * ginv y i j * fderiv ℝ f y (Pi.single j 1))
      = fun y => ∑ r, P.dir r i * (P.coeff r y * fderiv ℝ f y (P.dir r)) := by
    intro i
    funext y
    have hentry : ∀ j, P.density y * ginv y i j = ∑ r, P.coeff r y * (P.dir r i * P.dir r j) := by
      intro j
      have := congrFun (congrFun (hg y) i) j
      simpa [Matrix.sum_apply, vecMulVec_apply] using this
    simp only [hentry, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [fderiv_apply_eq_sum_single f y (P.dir r), Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  simp only [hinner]
  have hG : ∀ r, DifferentiableAt ℝ (fun y => P.coeff r y * fderiv ℝ f y (P.dir r)) x :=
    fun r => ((hda r).differentiableAt).mul ((hdf r).differentiableAt)
  have hsum : ∀ i : Fin d,
      fderiv ℝ (fun y => ∑ r, P.dir r i * (P.coeff r y * fderiv ℝ f y (P.dir r))) x
        (Pi.single i 1) =
      ∑ r, P.dir r i * fderiv ℝ (fun y => P.coeff r y * fderiv ℝ f y (P.dir r)) x
        (Pi.single i 1) := by
    intro i
    rw [fderiv_fun_sum fun r _ => (hG r).const_mul _]
    simp only [FunLike.coe_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [fderiv_const_mul (hG r)]
    simp
  simp only [hsum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hline : ∑ i, P.dir r i * fderiv ℝ (fun y => P.coeff r y * fderiv ℝ f y (P.dir r)) x
      (Pi.single i 1) = fderiv ℝ (fun y => P.coeff r y * fderiv ℝ f y (P.dir r)) x (P.dir r) :=
    (fderiv_apply_eq_sum_single _ x (P.dir r)).symm
  rw [hline, fderiv_fun_mul ((hda r).differentiableAt) ((hdf r).differentiableAt)]
  have hsecond : fderiv ℝ (fun y => fderiv ℝ f y (P.dir r)) x (P.dir r) =
      fderiv ℝ (fderiv ℝ f) x (P.dir r) (P.dir r) := by
    rw [fderiv_clm_apply ((hf.fderiv_right (m := 1) le_rfl).differentiable one_ne_zero
      |>.differentiableAt) (differentiableAt_const _)]
    simp
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul, hsecond]
  ring

end

end CoframePacket

/-! ### The metric bracket does not select the coframe (finite surrogate of
`cth:supp-metric-no-coframe`) -/

section coframe

variable {d : ℕ}

/-- The inverse metric `g⁻¹ = Eᵀ E` of an inverse coframe `E = (E_a{}^j)`. -/
def coframeInverseMetric (E : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin d) (Fin d) ℝ := Eᵀ * E

/-- **Rotation invariance.** A frame rotation `E ↦ R E` with `R` orthogonal leaves
`g⁻¹ = Eᵀ E` unchanged; hence every quantity built from `g⁻¹` (the positive
stencil decomposition, the coefficients `a_r`, the density, the bracket and the
scalar Renewal generator of `CoframePacket`) is unchanged. -/
theorem coframeInverseMetric_rotate (E R : Matrix (Fin d) (Fin d) ℝ)
    (hR : R ∈ Matrix.orthogonalGroup (Fin d) ℝ) :
    coframeInverseMetric (R * E) = coframeInverseMetric E := by
  unfold coframeInverseMetric
  have hRR : Rᵀ * R = 1 := (Matrix.mem_orthogonalGroup_iff' (Fin d) ℝ).mp hR
  rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Rᵀ, hRR, Matrix.one_mul]

/-- Any function of the inverse metric, e.g. the packet built from
`(g⁻¹, ρ)`, cannot distinguish `E` from `R E`. -/
theorem packet_of_metric_rotate {X : Type*} (Φ : Matrix (Fin d) (Fin d) ℝ → X)
    (E R : Matrix (Fin d) (Fin d) ℝ) (hR : R ∈ Matrix.orthogonalGroup (Fin d) ℝ) :
    Φ (coframeInverseMetric (R * E)) = Φ (coframeInverseMetric E) := by
  rw [coframeInverseMetric_rotate E R hR]

/-- The rotation by `π` in the `(0,1)`-plane: a special orthogonal matrix
different from the identity. -/
def planeFlip (_hd : 2 ≤ d) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.diagonal fun i => if i.val < 2 then -1 else 1

theorem planeFlip_mem_specialOrthogonalGroup (hd : 2 ≤ d) :
    planeFlip hd ∈ Matrix.specialOrthogonalGroup (Fin d) ℝ := by
  rw [Matrix.mem_specialOrthogonalGroup_iff]
  constructor
  · rw [Matrix.mem_orthogonalGroup_iff]
    unfold planeFlip
    rw [Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
    ext i j
    simp only [Matrix.diagonal_apply, Matrix.one_apply]
    split_ifs <;> simp
  · unfold planeFlip
    rw [Matrix.det_diagonal]
    have h0 : (⟨0, by omega⟩ : Fin d) ≠ ⟨1, by omega⟩ := by simp
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ (⟨0, by omega⟩ : Fin d)),
      ← Finset.prod_erase_mul _ _ (Finset.mem_erase.mpr ⟨h0.symm, Finset.mem_univ _⟩)]
    rw [Finset.prod_eq_one]
    · simp
    · intro i hi
      simp only [Finset.mem_erase, Finset.mem_univ, and_true, ne_eq, Fin.ext_iff] at hi
      have : ¬ i.val < 2 := by omega
      simp [this]

theorem planeFlip_ne_one (hd : 2 ≤ d) : planeFlip hd ≠ 1 := by
  intro h
  have := congrFun (congrFun h ⟨0, by omega⟩) ⟨0, by omega⟩
  simp [planeFlip] at this
  norm_num at this

/-- **Non-injectivity.** The map `E ↦ g⁻¹ = Eᵀ E` does not determine the coframe:
the identity coframe and its image under the special orthogonal rotation
`planeFlip` have the same inverse metric. -/
theorem exists_distinct_coframes_same_metric (hd : 2 ≤ d) :
    ∃ E E' : Matrix (Fin d) (Fin d) ℝ, E ≠ E' ∧
      (∃ R ∈ Matrix.specialOrthogonalGroup (Fin d) ℝ, E' = R * E) ∧
      coframeInverseMetric E' = coframeInverseMetric E :=
  ⟨1, planeFlip hd, (planeFlip_ne_one hd).symm,
    ⟨planeFlip hd, planeFlip_mem_specialOrthogonalGroup hd, (Matrix.mul_one _).symm⟩,
    by
      rw [show planeFlip hd = planeFlip hd * 1 from (Matrix.mul_one _).symm]
      exact coframeInverseMetric_rotate 1 (planeFlip hd)
        (Matrix.mem_specialOrthogonalGroup_iff.mp (planeFlip_mem_specialOrthogonalGroup hd)).1⟩

end coframe

end RenewalGeometry.CoframeRenewalPacket
