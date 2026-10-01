/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Cubic Hermite basis and the tensor-product Hermite stability estimate

Infrastructure for the shared cubic Hermite readout of the emergent-spacetime manuscript
(`eq:supp-gowdy-hermite-second-jet`, used in `thm:supp-gowdy-full-curvature`).

* The cubic Hermite basis on `[0, 1]`
  `H₀ = 2q³ - 3q² + 1`, `H₁ = -2q³ + 3q²`, `G₀ = q³ - 2q² + q`, `G₁ = q³ - q²`
  (`basisH`, `basisG`), their first and second derivatives (`hasDerivAt_basisH`, …), the
  identities `H₀ + H₁ = 1`, `H₀' + H₁' = 0`, `H₀'' + H₁'' = 0` and the nodal interpolation
  properties.
* The tensor-product Hermite interpolant on a cell of size `h`, in cell coordinates
  `p = (x - x₀)/h`, `q = (y - y₀)/h`, from corner value records `f`, scaled first-derivative
  records `u` (in `x`), `v` (in `y`) and mixed records `w`:
  `F(p,q) = Σ_{a,b} [f_ab H_a(p)H_b(q) + h u_ab G_a(p)H_b(q) + h v_ab H_a(p)G_b(q)
            + h² w_ab G_a(p)G_b(q)]`  (`interp`),
  with its first and second partial derivatives in cell coordinates (`tensor` with the
  differentiated basis; `hasDerivAt_interp_p`, …).
* **Stability** (`interp_stability`): if all jet records are bounded by `η` and the first
  nodal differences of the value records by `η h` (`0 < h ≤ 1`), then on the cell
  `|F| ≤ 16 η`, every first partial (cell coordinates) is `≤ 24 η h` and every second partial
  is `≤ 72 η h`; in physical coordinates (`∂_x = h⁻¹ ∂_p`) this is
  `‖F‖ + ‖DF‖ = O(η)`, `‖D²F‖ = O(η/h)`, the estimate `eq:supp-gowdy-hermite-second-jet`.
  The proof uses exactly the identities `H₀' + H₁' = 0` and `H₀'' + H₁'' = 0`.
-/

open scoped BigOperators

namespace RenewalGeometry.CubicHermite

noncomputable section

/-! ### Cubics -/

/-- The cubic `c₀ + c₁ q + c₂ q² + c₃ q³`. -/
def cubic (c : Fin 4 → ℝ) (q : ℝ) : ℝ := c 0 + c 1 * q + c 2 * q ^ 2 + c 3 * q ^ 3

/-- Its derivative. -/
def cubicD (c : Fin 4 → ℝ) (q : ℝ) : ℝ := c 1 + 2 * c 2 * q + 3 * c 3 * q ^ 2

/-- Its second derivative. -/
def cubicDD (c : Fin 4 → ℝ) (q : ℝ) : ℝ := 2 * c 2 + 6 * c 3 * q

theorem hasDerivAt_cubic (c : Fin 4 → ℝ) (q : ℝ) : HasDerivAt (cubic c) (cubicD c q) q := by
  have h1 := ((hasDerivAt_id q).const_mul (c 1))
  have h2 := ((hasDerivAt_pow 2 q).const_mul (c 2))
  have h3 := ((hasDerivAt_pow 3 q).const_mul (c 3))
  have := (((hasDerivAt_const q (c 0)).add h1).add h2).add h3
  have e1 : cubic c = (((fun _ => c 0) + fun y => c 1 * id y) + fun y => c 2 * y ^ 2) +
      fun y => c 3 * y ^ 3 := by
    funext x; simp [cubic]
  rw [e1]
  refine this.congr_deriv ?_
  norm_num [cubicD] <;> ring

theorem hasDerivAt_cubicD (c : Fin 4 → ℝ) (q : ℝ) : HasDerivAt (cubicD c) (cubicDD c q) q := by
  have h1 := ((hasDerivAt_id q).const_mul (2 * c 2))
  have h2 := ((hasDerivAt_pow 2 q).const_mul (3 * c 3))
  have := ((hasDerivAt_const q (c 1)).add h1).add h2
  have e1 : cubicD c = ((fun _ => c 1) + fun y => 2 * c 2 * id y) + fun y => 3 * c 3 * y ^ 2 := by
    funext x; simp [cubicD]
  rw [e1]
  refine this.congr_deriv ?_
  norm_num [cubicDD] <;> ring

/-! ### The Hermite basis -/

/-- Coefficients of `H₀ = 1 - 3q² + 2q³` and `H₁ = 3q² - 2q³`. -/
def hCoef : Fin 2 → Fin 4 → ℝ := ![![1, 0, -3, 2], ![0, 0, 3, -2]]

/-- Coefficients of `G₀ = q - 2q² + q³` and `G₁ = -q² + q³`. -/
def gCoef : Fin 2 → Fin 4 → ℝ := ![![0, 1, -2, 1], ![0, 0, -1, 1]]

/-- Value basis `H_a`. -/
def basisH (a : Fin 2) (q : ℝ) : ℝ := cubic (hCoef a) q
/-- Slope basis `G_a`. -/
def basisG (a : Fin 2) (q : ℝ) : ℝ := cubic (gCoef a) q
/-- `H_a'`. -/
def basisHD (a : Fin 2) (q : ℝ) : ℝ := cubicD (hCoef a) q
/-- `G_a'`. -/
def basisGD (a : Fin 2) (q : ℝ) : ℝ := cubicD (gCoef a) q
/-- `H_a''`. -/
def basisHDD (a : Fin 2) (q : ℝ) : ℝ := cubicDD (hCoef a) q
/-- `G_a''`. -/
def basisGDD (a : Fin 2) (q : ℝ) : ℝ := cubicDD (gCoef a) q

theorem basisH_zero (q : ℝ) : basisH 0 q = 2 * q ^ 3 - 3 * q ^ 2 + 1 := by
  simp [basisH, cubic, hCoef]; ring
theorem basisH_one (q : ℝ) : basisH 1 q = -2 * q ^ 3 + 3 * q ^ 2 := by
  simp [basisH, cubic, hCoef]; ring
theorem basisG_zero (q : ℝ) : basisG 0 q = q ^ 3 - 2 * q ^ 2 + q := by
  simp [basisG, cubic, gCoef]; ring
theorem basisG_one (q : ℝ) : basisG 1 q = q ^ 3 - q ^ 2 := by
  simp [basisG, cubic, gCoef]; ring

theorem basisHD_zero (q : ℝ) : basisHD 0 q = 6 * q ^ 2 - 6 * q := by
  simp [basisHD, cubicD, hCoef]; ring
theorem basisHD_one (q : ℝ) : basisHD 1 q = -6 * q ^ 2 + 6 * q := by
  simp [basisHD, cubicD, hCoef]; ring
theorem basisGD_zero (q : ℝ) : basisGD 0 q = 3 * q ^ 2 - 4 * q + 1 := by
  simp [basisGD, cubicD, gCoef]; ring
theorem basisGD_one (q : ℝ) : basisGD 1 q = 3 * q ^ 2 - 2 * q := by
  simp [basisGD, cubicD, gCoef]; ring
theorem basisHDD_zero (q : ℝ) : basisHDD 0 q = 12 * q - 6 := by
  simp [basisHDD, cubicDD, hCoef]; ring
theorem basisHDD_one (q : ℝ) : basisHDD 1 q = -12 * q + 6 := by
  simp [basisHDD, cubicDD, hCoef]; ring
theorem basisGDD_zero (q : ℝ) : basisGDD 0 q = 6 * q - 4 := by
  simp [basisGDD, cubicDD, gCoef]; ring
theorem basisGDD_one (q : ℝ) : basisGDD 1 q = 6 * q - 2 := by
  simp [basisGDD, cubicDD, gCoef]; ring

/-- `H₀ + H₁ = 1`. -/
theorem basisH_sum (q : ℝ) : basisH 0 q + basisH 1 q = 1 := by
  rw [basisH_zero, basisH_one]; ring

/-- `H₀' + H₁' = 0`. -/
theorem basisHD_sum (q : ℝ) : basisHD 0 q + basisHD 1 q = 0 := by
  rw [basisHD_zero, basisHD_one]; ring

/-- `H₀'' + H₁'' = 0`. -/
theorem basisHDD_sum (q : ℝ) : basisHDD 0 q + basisHDD 1 q = 0 := by
  rw [basisHDD_zero, basisHDD_one]; ring

/-- Nodal interpolation: `H_a(b) = δ_ab`, `G_a(b) = 0`, `H_a'(b) = 0`, `G_a'(b) = δ_ab`. -/
theorem basis_nodal :
    basisH 0 0 = 1 ∧ basisH 0 1 = 0 ∧ basisH 1 0 = 0 ∧ basisH 1 1 = 1 ∧
    basisG 0 0 = 0 ∧ basisG 0 1 = 0 ∧ basisG 1 0 = 0 ∧ basisG 1 1 = 0 ∧
    basisHD 0 0 = 0 ∧ basisHD 0 1 = 0 ∧ basisHD 1 0 = 0 ∧ basisHD 1 1 = 0 ∧
    basisGD 0 0 = 1 ∧ basisGD 0 1 = 0 ∧ basisGD 1 0 = 0 ∧ basisGD 1 1 = 1 := by
  simp only [basisH_zero, basisH_one, basisG_zero, basisG_one, basisHD_zero, basisHD_one,
    basisGD_zero, basisGD_one]
  norm_num

/-! ### Basis bounds on `[0, 1]` -/

section Bounds

variable {q : ℝ}

theorem abs_basisH_le (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    ∀ a : Fin 2, |basisH a q| ≤ 1 := by
  obtain ⟨h0, h1⟩ := hq
  rw [Fin.forall_fin_two]
  refine ⟨?_, ?_⟩
  · rw [basisH_zero, abs_le]; constructor <;> nlinarith [mul_nonneg h0 h0, mul_nonneg h0 (sub_nonneg.2 h1)]
  · rw [basisH_one, abs_le]; constructor <;> nlinarith [mul_nonneg h0 h0, mul_nonneg h0 (sub_nonneg.2 h1)]

theorem abs_basisG_le (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    ∀ a : Fin 2, |basisG a q| ≤ 1 := by
  obtain ⟨h0, h1⟩ := hq
  rw [Fin.forall_fin_two]
  refine ⟨?_, ?_⟩
  · rw [basisG_zero, abs_le]; constructor <;> nlinarith [mul_nonneg h0 h0, mul_nonneg h0 (sub_nonneg.2 h1)]
  · rw [basisG_one, abs_le]; constructor <;> nlinarith [mul_nonneg h0 h0, mul_nonneg h0 (sub_nonneg.2 h1)]

theorem abs_basisHD_le (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    ∀ a : Fin 2, |basisHD a q| ≤ 3 / 2 := by
  obtain ⟨h0, h1⟩ := hq
  rw [Fin.forall_fin_two]
  refine ⟨?_, ?_⟩
  · rw [basisHD_zero, abs_le]; constructor <;> nlinarith [mul_nonneg h0 (sub_nonneg.2 h1), sq_nonneg (q - 1 / 2)]
  · rw [basisHD_one, abs_le]; constructor <;> nlinarith [mul_nonneg h0 (sub_nonneg.2 h1), sq_nonneg (q - 1 / 2)]

theorem abs_basisGD_le (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    ∀ a : Fin 2, |basisGD a q| ≤ 1 := by
  obtain ⟨h0, h1⟩ := hq
  rw [Fin.forall_fin_two]
  refine ⟨?_, ?_⟩
  · rw [basisGD_zero, abs_le]; constructor <;> nlinarith [mul_nonneg h0 (sub_nonneg.2 h1), sq_nonneg (q - 2 / 3)]
  · rw [basisGD_one, abs_le]; constructor <;> nlinarith [mul_nonneg h0 (sub_nonneg.2 h1), sq_nonneg (q - 1 / 3)]

theorem abs_basisHDD_le (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    ∀ a : Fin 2, |basisHDD a q| ≤ 6 := by
  obtain ⟨h0, h1⟩ := hq
  rw [Fin.forall_fin_two]
  refine ⟨?_, ?_⟩
  · rw [basisHDD_zero, abs_le]; constructor <;> linarith
  · rw [basisHDD_one, abs_le]; constructor <;> linarith

theorem abs_basisGDD_le (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    ∀ a : Fin 2, |basisGDD a q| ≤ 4 := by
  obtain ⟨h0, h1⟩ := hq
  rw [Fin.forall_fin_two]
  refine ⟨?_, ?_⟩
  · rw [basisGDD_zero, abs_le]; constructor <;> linarith
  · rw [basisGDD_one, abs_le]; constructor <;> linarith

end Bounds

/-! ### The tensor-product interpolant -/

/-- The tensor-product combination of the jet records `f, u, v, w` (indexed by the corners
`(a, b) ∈ {0,1}²`) with basis values `Hp, Gp` in the first and `Hq, Gq` in the second
variable. -/
def tensor (h : ℝ) (f u v w : Fin 2 → Fin 2 → ℝ) (Hp Gp Hq Gq : Fin 2 → ℝ) : ℝ :=
  (∑ a, ∑ b, f a b * Hp a * Hq b) + h * (∑ a, ∑ b, u a b * Gp a * Hq b) +
    h * (∑ a, ∑ b, v a b * Hp a * Gq b) + h ^ 2 * (∑ a, ∑ b, w a b * Gp a * Gq b)

/-- The tensor-product cubic Hermite interpolant in cell coordinates `(p, q) ∈ [0,1]²`. -/
def interp (h : ℝ) (f u v w : Fin 2 → Fin 2 → ℝ) (p q : ℝ) : ℝ :=
  tensor h f u v w (fun a => basisH a p) (fun a => basisG a p) (fun b => basisH b q)
    (fun b => basisG b q)

/-- Corner values: `F(a, b) = f_ab`. -/
theorem interp_corners (h : ℝ) (f u v w : Fin 2 → Fin 2 → ℝ) :
    interp h f u v w 0 0 = f 0 0 ∧ interp h f u v w 1 0 = f 1 0 ∧
      interp h f u v w 0 1 = f 0 1 ∧ interp h f u v w 1 1 = f 1 1 := by
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8, -⟩ := basis_nodal
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [interp, tensor, Fin.sum_univ_two, n1, n2, n3, n4, n5, n6, n7, n8]

theorem hasDerivAt_tensor_p (h : ℝ) (f u v w : Fin 2 → Fin 2 → ℝ) {Hp Gp : ℝ → Fin 2 → ℝ}
    {Hp' Gp' : Fin 2 → ℝ} (Hq Gq : Fin 2 → ℝ) {p : ℝ}
    (hH : ∀ a, HasDerivAt (fun p => Hp p a) (Hp' a) p)
    (hG : ∀ a, HasDerivAt (fun p => Gp p a) (Gp' a) p) :
    HasDerivAt (fun p => tensor h f u v w (Hp p) (Gp p) Hq Gq)
      (tensor h f u v w Hp' Gp' Hq Gq) p := by
  unfold tensor
  simp only [Fin.sum_univ_two]
  have e := fun a b => ((hH a).const_mul (f a b)).mul_const (Hq b)
  have e2 := fun a b => ((hG a).const_mul (u a b)).mul_const (Hq b)
  have e3 := fun a b => ((hH a).const_mul (v a b)).mul_const (Gq b)
  have e4 := fun a b => ((hG a).const_mul (w a b)).mul_const (Gq b)
  exact ((((e 0 0).add (e 0 1)).add ((e 1 0).add (e 1 1))).add
    ((((e2 0 0).add (e2 0 1)).add ((e2 1 0).add (e2 1 1))).const_mul h)).add
    ((((e3 0 0).add (e3 0 1)).add ((e3 1 0).add (e3 1 1))).const_mul h) |>.add
    ((((e4 0 0).add (e4 0 1)).add ((e4 1 0).add (e4 1 1))).const_mul (h ^ 2))

theorem hasDerivAt_tensor_q (h : ℝ) (f u v w : Fin 2 → Fin 2 → ℝ) (Hp Gp : Fin 2 → ℝ)
    {Hq Gq : ℝ → Fin 2 → ℝ} {Hq' Gq' : Fin 2 → ℝ} {q : ℝ}
    (hH : ∀ b, HasDerivAt (fun q => Hq q b) (Hq' b) q)
    (hG : ∀ b, HasDerivAt (fun q => Gq q b) (Gq' b) q) :
    HasDerivAt (fun q => tensor h f u v w Hp Gp (Hq q) (Gq q))
      (tensor h f u v w Hp Gp Hq' Gq') q := by
  unfold tensor
  simp only [Fin.sum_univ_two]
  have e := fun a b => (hH b).const_mul (f a b * Hp a)
  have e2 := fun a b => (hH b).const_mul (u a b * Gp a)
  have e3 := fun a b => (hG b).const_mul (v a b * Hp a)
  have e4 := fun a b => (hG b).const_mul (w a b * Gp a)
  exact ((((e 0 0).add (e 0 1)).add ((e 1 0).add (e 1 1))).add
    ((((e2 0 0).add (e2 0 1)).add ((e2 1 0).add (e2 1 1))).const_mul h)).add
    ((((e3 0 0).add (e3 0 1)).add ((e3 1 0).add (e3 1 1))).const_mul h) |>.add
    ((((e4 0 0).add (e4 0 1)).add ((e4 1 0).add (e4 1 1))).const_mul (h ^ 2))

/-- `∂_p F` (cell coordinates). -/
theorem hasDerivAt_interp_p (h : ℝ) (f u v w : Fin 2 → Fin 2 → ℝ) (p q : ℝ) :
    HasDerivAt (fun p => interp h f u v w p q)
      (tensor h f u v w (fun a => basisHD a p) (fun a => basisGD a p) (fun b => basisH b q)
        (fun b => basisG b q)) p :=
  hasDerivAt_tensor_p h f u v w _ _ (fun a => hasDerivAt_cubic _ p)
    (fun a => hasDerivAt_cubic _ p)

/-- `∂_q F` (cell coordinates). -/
theorem hasDerivAt_interp_q (h : ℝ) (f u v w : Fin 2 → Fin 2 → ℝ) (p q : ℝ) :
    HasDerivAt (fun q => interp h f u v w p q)
      (tensor h f u v w (fun a => basisH a p) (fun a => basisG a p) (fun b => basisHD b q)
        (fun b => basisGD b q)) q :=
  hasDerivAt_tensor_q h f u v w _ _ (fun b => hasDerivAt_cubic _ q)
    (fun b => hasDerivAt_cubic _ q)

/-- `∂_p² F`. -/
theorem hasDerivAt_interp_pp (h : ℝ) (f u v w : Fin 2 → Fin 2 → ℝ) (p q : ℝ) :
    HasDerivAt (fun p => tensor h f u v w (fun a => basisHD a p) (fun a => basisGD a p)
        (fun b => basisH b q) (fun b => basisG b q))
      (tensor h f u v w (fun a => basisHDD a p) (fun a => basisGDD a p) (fun b => basisH b q)
        (fun b => basisG b q)) p :=
  hasDerivAt_tensor_p h f u v w _ _ (fun a => hasDerivAt_cubicD _ p)
    (fun a => hasDerivAt_cubicD _ p)

/-- `∂_q ∂_p F`. -/
theorem hasDerivAt_interp_pq (h : ℝ) (f u v w : Fin 2 → Fin 2 → ℝ) (p q : ℝ) :
    HasDerivAt (fun q => tensor h f u v w (fun a => basisHD a p) (fun a => basisGD a p)
        (fun b => basisH b q) (fun b => basisG b q))
      (tensor h f u v w (fun a => basisHD a p) (fun a => basisGD a p) (fun b => basisHD b q)
        (fun b => basisGD b q)) q :=
  hasDerivAt_tensor_q h f u v w _ _ (fun b => hasDerivAt_cubic _ q)
    (fun b => hasDerivAt_cubic _ q)

/-- `∂_q² F`. -/
theorem hasDerivAt_interp_qq (h : ℝ) (f u v w : Fin 2 → Fin 2 → ℝ) (p q : ℝ) :
    HasDerivAt (fun q => tensor h f u v w (fun a => basisH a p) (fun a => basisG a p)
        (fun b => basisHD b q) (fun b => basisGD b q))
      (tensor h f u v w (fun a => basisH a p) (fun a => basisG a p) (fun b => basisHDD b q)
        (fun b => basisGDD b q)) q :=
  hasDerivAt_tensor_q h f u v w _ _ (fun b => hasDerivAt_cubicD _ q)
    (fun b => hasDerivAt_cubicD _ q)

/-! ### Double-sum estimates -/

theorem abs_double_sum_le (c : Fin 2 → Fin 2 → ℝ) (α β : Fin 2 → ℝ) {η A B : ℝ}
    (hc : ∀ a b, |c a b| ≤ η) (hα : ∀ a, |α a| ≤ A) (hβ : ∀ b, |β b| ≤ B) :
    |∑ a, ∑ b, c a b * α a * β b| ≤ 4 * (η * A * B) := by
  have h0 : 0 ≤ η := (abs_nonneg _).trans (hc 0 0)
  have hA : 0 ≤ A := (abs_nonneg _).trans (hα 0)
  have hB : 0 ≤ B := (abs_nonneg _).trans (hβ 0)
  have t : ∀ a b, |c a b * α a * β b| ≤ η * A * B := by
    intro a b
    rw [abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul (hc a b) (hα a) (abs_nonneg _) h0) (hβ b) (abs_nonneg _)
      (by positivity)
  simp only [Fin.sum_univ_two]
  have := abs_add_le (c 0 0 * α 0 * β 0 + c 0 1 * α 0 * β 1) (c 1 0 * α 1 * β 0 + c 1 1 * α 1 * β 1)
  have := abs_add_le (c 0 0 * α 0 * β 0) (c 0 1 * α 0 * β 1)
  have := abs_add_le (c 1 0 * α 1 * β 0) (c 1 1 * α 1 * β 1)
  linarith [t 0 0, t 0 1, t 1 0, t 1 1]

/-- If `α₀ = -α₁`, the double sum only sees the first differences in the first index. -/
theorem abs_double_sum_le_of_diff_p (c : Fin 2 → Fin 2 → ℝ) (α β : Fin 2 → ℝ) {δ A B : ℝ}
    (hsum : α 0 + α 1 = 0) (hc : ∀ b, |c 1 b - c 0 b| ≤ δ) (hα : |α 1| ≤ A)
    (hβ : ∀ b, |β b| ≤ B) :
    |∑ a, ∑ b, c a b * α a * β b| ≤ 2 * (δ * A * B) := by
  have hα0 : α 0 = -α 1 := by linarith
  have e : ∑ a, ∑ b, c a b * α a * β b =
      (c 1 0 - c 0 0) * α 1 * β 0 + (c 1 1 - c 0 1) * α 1 * β 1 := by
    simp only [Fin.sum_univ_two, hα0]; ring
  rw [e]
  have h0 : 0 ≤ δ := (abs_nonneg _).trans (hc 0)
  have hA : 0 ≤ A := (abs_nonneg _).trans hα
  have t : ∀ b, |(c 1 b - c 0 b) * α 1 * β b| ≤ δ * A * B := by
    intro b
    rw [abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul (hc b) hα (abs_nonneg _) h0) (hβ b) (abs_nonneg _)
      (by positivity)
  have := abs_add_le ((c 1 0 - c 0 0) * α 1 * β 0) ((c 1 1 - c 0 1) * α 1 * β 1)
  linarith [t 0, t 1]

/-- If `β₀ = -β₁`, the double sum only sees the first differences in the second index. -/
theorem abs_double_sum_le_of_diff_q (c : Fin 2 → Fin 2 → ℝ) (α β : Fin 2 → ℝ) {δ A B : ℝ}
    (hsum : β 0 + β 1 = 0) (hc : ∀ a, |c a 1 - c a 0| ≤ δ) (hα : ∀ a, |α a| ≤ A)
    (hβ : |β 1| ≤ B) :
    |∑ a, ∑ b, c a b * α a * β b| ≤ 2 * (δ * A * B) := by
  have hβ0 : β 0 = -β 1 := by linarith
  have e : ∑ a, ∑ b, c a b * α a * β b =
      (c 0 1 - c 0 0) * α 0 * β 1 + (c 1 1 - c 1 0) * α 1 * β 1 := by
    simp only [Fin.sum_univ_two, hβ0]; ring
  rw [e]
  have h0 : 0 ≤ δ := (abs_nonneg _).trans (hc 0)
  have hA : 0 ≤ A := (abs_nonneg _).trans (hα 0)
  have t : ∀ a, |(c a 1 - c a 0) * α a * β 1| ≤ δ * A * B := by
    intro a
    rw [abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul (hc a) (hα a) (abs_nonneg _) h0) hβ (abs_nonneg _)
      (by positivity)
  have := abs_add_le ((c 0 1 - c 0 0) * α 0 * β 1) ((c 1 1 - c 1 0) * α 1 * β 1)
  linarith [t 0, t 1]

/-- If `α₀ = -α₁` and `β₀ = -β₁`, the double sum is the double difference. -/
theorem abs_double_sum_le_of_diff_pq (c : Fin 2 → Fin 2 → ℝ) (α β : Fin 2 → ℝ) {δ A B : ℝ}
    (hα0 : α 0 + α 1 = 0) (hβ0 : β 0 + β 1 = 0) (hc : ∀ a, |c a 1 - c a 0| ≤ δ)
    (hα : |α 1| ≤ A) (hβ : |β 1| ≤ B) :
    |∑ a, ∑ b, c a b * α a * β b| ≤ 2 * (δ * A * B) := by
  have ha : α 0 = -α 1 := by linarith
  have hb : β 0 = -β 1 := by linarith
  have e : ∑ a, ∑ b, c a b * α a * β b =
      ((c 1 1 - c 1 0) - (c 0 1 - c 0 0)) * α 1 * β 1 := by
    simp only [Fin.sum_univ_two, ha, hb]; ring
  rw [e, abs_mul, abs_mul]
  have h0 : 0 ≤ δ := (abs_nonneg _).trans (hc 0)
  have hA : 0 ≤ A := (abs_nonneg _).trans hα
  have hd : |(c 1 1 - c 1 0) - (c 0 1 - c 0 0)| ≤ 2 * δ :=
    (abs_sub _ _).trans (by linarith [hc 0, hc 1])
  calc |(c 1 1 - c 1 0) - (c 0 1 - c 0 0)| * |α 1| * |β 1| ≤ 2 * δ * A * B :=
        mul_le_mul (mul_le_mul hd hα (abs_nonneg _) (by positivity)) hβ (abs_nonneg _)
          (by positivity)
    _ = 2 * (δ * A * B) := by ring

/-! ### Stability -/

/-- Hypotheses of the stability estimate: jet records bounded by `η`, first nodal
differences of the value records bounded by `η h`. -/
structure JetBound (h η : ℝ) (f u v w : Fin 2 → Fin 2 → ℝ) : Prop where
  f_le : ∀ a b, |f a b| ≤ η
  u_le : ∀ a b, |u a b| ≤ η
  v_le : ∀ a b, |v a b| ≤ η
  w_le : ∀ a b, |w a b| ≤ η
  diff_p : ∀ b, |f 1 b - f 0 b| ≤ η * h
  diff_q : ∀ a, |f a 1 - f a 0| ≤ η * h

theorem abs_tensor_le {h : ℝ} (hh : 0 ≤ h) (f u v w : Fin 2 → Fin 2 → ℝ)
    (Hp Gp Hq Gq : Fin 2 → ℝ) (F₁ F₂ F₃ F₄ : ℝ)
    (h1 : |∑ a, ∑ b, f a b * Hp a * Hq b| ≤ F₁) (h2 : |∑ a, ∑ b, u a b * Gp a * Hq b| ≤ F₂)
    (h3 : |∑ a, ∑ b, v a b * Hp a * Gq b| ≤ F₃) (h4 : |∑ a, ∑ b, w a b * Gp a * Gq b| ≤ F₄) :
    |tensor h f u v w Hp Gp Hq Gq| ≤ F₁ + h * F₂ + h * F₃ + h ^ 2 * F₄ := by
  unfold tensor
  have a2 : |h * ∑ a, ∑ b, u a b * Gp a * Hq b| ≤ h * F₂ := by
    rw [abs_mul, abs_of_nonneg hh]; exact mul_le_mul_of_nonneg_left h2 hh
  have a3 : |h * ∑ a, ∑ b, v a b * Hp a * Gq b| ≤ h * F₃ := by
    rw [abs_mul, abs_of_nonneg hh]; exact mul_le_mul_of_nonneg_left h3 hh
  have a4 : |h ^ 2 * ∑ a, ∑ b, w a b * Gp a * Gq b| ≤ h ^ 2 * F₄ := by
    rw [abs_mul, abs_of_nonneg (by positivity)]; exact mul_le_mul_of_nonneg_left h4 (by positivity)
  have := abs_add_le ((∑ a, ∑ b, f a b * Hp a * Hq b) + h * (∑ a, ∑ b, u a b * Gp a * Hq b) +
    h * (∑ a, ∑ b, v a b * Hp a * Gq b)) (h ^ 2 * (∑ a, ∑ b, w a b * Gp a * Gq b))
  have := abs_add_le ((∑ a, ∑ b, f a b * Hp a * Hq b) + h * (∑ a, ∑ b, u a b * Gp a * Hq b))
    (h * (∑ a, ∑ b, v a b * Hp a * Gq b))
  have := abs_add_le (∑ a, ∑ b, f a b * Hp a * Hq b) (h * (∑ a, ∑ b, u a b * Gp a * Hq b))
  linarith

/-- **Stability of the tensor-product cubic Hermite interpolant**
(`eq:supp-gowdy-hermite-second-jet`).  For `0 < h ≤ 1`, jet records bounded by `η` and first
nodal differences of the value records bounded by `η h`, on the cell `(p, q) ∈ [0,1]²`:
`|F| ≤ 16 η`; the first partials in cell coordinates are `≤ 24 η h`; the second partials in cell
coordinates are `≤ 72 η h`.  Since `∂_x = h⁻¹ ∂_p`, `∂_y = h⁻¹ ∂_q` on a cell of size `h`, this
is `‖F‖ + ‖DF‖ ≤ C η` and `‖D²F‖ ≤ C η / h` in physical coordinates. -/
theorem interp_stability {h η : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) {f u v w : Fin 2 → Fin 2 → ℝ}
    (hJ : JetBound h η f u v w) {p q : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    |interp h f u v w p q| ≤ 16 * η ∧
    |tensor h f u v w (fun a => basisHD a p) (fun a => basisGD a p) (fun b => basisH b q)
      (fun b => basisG b q)| ≤ 24 * η * h ∧
    |tensor h f u v w (fun a => basisH a p) (fun a => basisG a p) (fun b => basisHD b q)
      (fun b => basisGD b q)| ≤ 24 * η * h ∧
    |tensor h f u v w (fun a => basisHDD a p) (fun a => basisGDD a p) (fun b => basisH b q)
      (fun b => basisG b q)| ≤ 72 * η * h ∧
    |tensor h f u v w (fun a => basisHD a p) (fun a => basisGD a p) (fun b => basisHD b q)
      (fun b => basisGD b q)| ≤ 72 * η * h ∧
    |tensor h f u v w (fun a => basisH a p) (fun a => basisG a p) (fun b => basisHDD b q)
      (fun b => basisGDD b q)| ≤ 72 * η * h := by
  have hη : 0 ≤ η := (abs_nonneg _).trans (hJ.f_le 0 0)
  have hh0 := hh.le
  have hHp := abs_basisH_le hp
  have hGp := abs_basisG_le hp
  have hHq := abs_basisH_le hq
  have hGq := abs_basisG_le hq
  have hHDp := abs_basisHD_le hp
  have hGDp := abs_basisGD_le hp
  have hHDq := abs_basisHD_le hq
  have hGDq := abs_basisGD_le hq
  have hHDDp := abs_basisHDD_le hp
  have hGDDp := abs_basisGDD_le hp
  have hHDDq := abs_basisHDD_le hq
  have hGDDq := abs_basisGDD_le hq
  have hηh : 0 ≤ η * h := mul_nonneg hη hh0
  have hh2 : h ^ 2 ≤ h := by nlinarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := abs_tensor_le hh0 f u v w _ _ _ _ _ _ _ _
      (abs_double_sum_le f _ _ hJ.f_le hHp hHq) (abs_double_sum_le u _ _ hJ.u_le hGp hHq)
      (abs_double_sum_le v _ _ hJ.v_le hHp hGq) (abs_double_sum_le w _ _ hJ.w_le hGp hGq)
    unfold interp
    refine this.trans ?_
    nlinarith
  · have := abs_tensor_le hh0 f u v w _ _ _ _ _ _ _ _
      (abs_double_sum_le_of_diff_p f _ _ (basisHD_sum p) hJ.diff_p (hHDp 1) hHq)
      (abs_double_sum_le u _ _ hJ.u_le hGDp hHq)
      (abs_double_sum_le v _ _ hJ.v_le hHDp hGq) (abs_double_sum_le w _ _ hJ.w_le hGDp hGq)
    refine this.trans ?_
    nlinarith
  · have := abs_tensor_le hh0 f u v w _ _ _ _ _ _ _ _
      (abs_double_sum_le_of_diff_q f _ _ (basisHD_sum q) hJ.diff_q hHp (hHDq 1))
      (abs_double_sum_le u _ _ hJ.u_le hGp hHDq)
      (abs_double_sum_le v _ _ hJ.v_le hHp hGDq) (abs_double_sum_le w _ _ hJ.w_le hGp hGDq)
    refine this.trans ?_
    nlinarith
  · have := abs_tensor_le hh0 f u v w _ _ _ _ _ _ _ _
      (abs_double_sum_le_of_diff_p f _ _ (basisHDD_sum p) hJ.diff_p (hHDDp 1) hHq)
      (abs_double_sum_le u _ _ hJ.u_le hGDDp hHq)
      (abs_double_sum_le v _ _ hJ.v_le hHDDp hGq) (abs_double_sum_le w _ _ hJ.w_le hGDDp hGq)
    refine this.trans ?_
    nlinarith
  · have := abs_tensor_le hh0 f u v w _ _ _ _ _ _ _ _
      (abs_double_sum_le_of_diff_pq f _ _ (basisHD_sum p) (basisHD_sum q) hJ.diff_q (hHDp 1)
        (hHDq 1))
      (abs_double_sum_le u _ _ hJ.u_le hGDp hHDq)
      (abs_double_sum_le v _ _ hJ.v_le hHDp hGDq) (abs_double_sum_le w _ _ hJ.w_le hGDp hGDq)
    refine this.trans ?_
    nlinarith
  · have := abs_tensor_le hh0 f u v w _ _ _ _ _ _ _ _
      (abs_double_sum_le_of_diff_q f _ _ (basisHDD_sum q) hJ.diff_q hHp (hHDDq 1))
      (abs_double_sum_le u _ _ hJ.u_le hGp hHDDq)
      (abs_double_sum_le v _ _ hJ.v_le hHp hGDDq) (abs_double_sum_le w _ _ hJ.w_le hGp hGDDq)
    refine this.trans ?_
    nlinarith

/-- Non-vacuity of the stability hypotheses: the interpolant of `x ↦ x` (value records
`f_ab = a h`, slope records `u = 1`, `v = w = 0`) satisfies them with `η = 1` on a cell of
size `h ≤ 1`. -/
example {h : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) :
    JetBound h 1 (fun a _ => (a : ℝ) * h) (fun _ _ => 1) (fun _ _ => 0) (fun _ _ => 0) where
  f_le a b := by
    fin_cases a <;> simp [abs_of_pos hh, hh1]
  u_le _ _ := by simp
  v_le _ _ := by simp
  w_le _ _ := by simp
  diff_p _ := by simp [abs_of_pos hh, hh.le]
  diff_q _ := by simp [hh.le]

end

end RenewalGeometry.CubicHermite
