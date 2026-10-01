/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.TensorCubicHermiteRemainder

/-!
# The physical tensor cubic Hermite readout: derivatives, jet errors and `C¹` gluing
  (infrastructure for `thm:supp-gowdy-full-curvature`, `eq:supp-gowdy-second-jet`;
  emergent-spacetime supplement)

For a cell `[x₀, x₀+h] × [y₀, y₀+h]` and corner jet records `f, u, v, w` (value, `x`-, `y`- and
mixed derivative), the **physical readout** is
`readout x₀ y₀ h f u v w (x, y) = interp h f u v w ((x-x₀)/h) ((y-y₀)/h)`
(`CubicHermite.interp`, the tensor-product cubic Hermite interpolant).

* `cellDeriv h f u v w i j (p, q)` is the tensor of the `i`-th / `j`-th differentiated basis in the
  cell coordinates; `iterate_dP_dQ_cellDeriv`: `∂_p^i ∂_q^j` of the cell-coordinate interpolant is
  `cellDeriv … i j` for `i + j ≤ 2`.
* `iterate_dP_dQ_readout` (**chain rule of the readout**): for `h ≠ 0`,
  `∂ₓ^i ∂_y^j readout (x₀ + hp, y₀ + hq) = cellDeriv … i j (p, q) / h^{i+j}`; this identifies the
  scaled tensors of `CubicHermite.interp_stability` and
  `CubicHermiteRemainder.cell_remainder_scaled` with the actual physical derivatives.
* `abs_cellDeriv_le`: the stability estimate in this notation,
  `|cellDeriv i j| ≤ 72 η h^{min 1 (i+j)}` under `CubicHermite.JetBound h η`.
* `readout_jet_error` (**jet error of the readout**): if `φ` is smooth with `|∂^a_x ∂^b_y φ| ≤ M`
  for `4 ≤ a+b ≤ 6` on the cell and the corner records differ from the exact records of `φ` within
  `CubicHermite.JetBound h η`, then for `i + j ≤ 2` on the cell
  `|∂ₓ^i∂_y^j (readout - φ)| ≤ 72 η h^{min 1 (i+j)} / h^{i+j} + hermRemConst · M · h^{4-(i+j)}`;
  `readout_jet_error_le_one`, `readout_jet_error_two`: with `η ≤ c h²` this is `O(h²)` for
  `i + j ≤ 1` and `O(h)` for `i + j = 2` (`eq:supp-gowdy-second-jet`, cellwise).
* `readout_glue_x`, `readout_glue_y` (**`C¹` gluing**): two cells sharing an edge and the jet
  records at its two nodes have readouts with equal values and equal first derivatives (indeed
  equal tangential derivatives of all orders `≤ 2`) along the shared edge, so the cellwise
  readout is `C¹` and its weak second derivative is the cellwise one.
-/

open Set
open scoped BigOperators ContDiff

namespace RenewalGeometry.TensorHermiteReadout

open CubicHermite CubicHermiteRemainder

noncomputable section

/-! ### Cell-coordinate derivative tensors -/

/-- `∂_p^i ∂_q^j` of the cell-coordinate interpolant: the tensor of the differentiated basis. -/
def cellDeriv (h : ℝ) (f u v w : Fin 2 → Fin 2 → ℝ) (i j : ℕ) (z : ℝ × ℝ) : ℝ :=
  tensor h f u v w (fun a => BH i a z.1) (fun a => BG i a z.1) (fun b => BH j b z.2)
    (fun b => BG j b z.2)

theorem hasDerivAt_BH {i : ℕ} (hi : i ≤ 1) (a : Fin 2) (q : ℝ) :
    HasDerivAt (BH i a) (BH (i + 1) a q) q := by
  interval_cases i
  · exact hasDerivAt_cubic _ q
  · exact hasDerivAt_cubicD _ q

theorem hasDerivAt_BG {i : ℕ} (hi : i ≤ 1) (a : Fin 2) (q : ℝ) :
    HasDerivAt (BG i a) (BG (i + 1) a q) q := by
  interval_cases i
  · exact hasDerivAt_cubic _ q
  · exact hasDerivAt_cubicD _ q

theorem contDiff_cubic (c : Fin 4 → ℝ) : ContDiff ℝ ∞ (cubic c) := by
  unfold cubic; fun_prop

theorem contDiff_cubicD (c : Fin 4 → ℝ) : ContDiff ℝ ∞ (cubicD c) := by
  unfold cubicD; fun_prop

theorem contDiff_cubicDD (c : Fin 4 → ℝ) : ContDiff ℝ ∞ (cubicDD c) := by
  unfold cubicDD; fun_prop

theorem contDiff_BH (i : ℕ) (a : Fin 2) : ContDiff ℝ ∞ (BH i a) := by
  rcases i with _ | _ | _ | i
  · exact contDiff_cubic _
  · exact contDiff_cubicD _
  · exact contDiff_cubicDD _
  · exact contDiff_const

theorem contDiff_BG (i : ℕ) (a : Fin 2) : ContDiff ℝ ∞ (BG i a) := by
  rcases i with _ | _ | _ | i
  · exact contDiff_cubic _
  · exact contDiff_cubicD _
  · exact contDiff_cubicDD _
  · exact contDiff_const

theorem contDiff_cellDeriv (h : ℝ) (f u v w : Fin 2 → Fin 2 → ℝ) (i j : ℕ) :
    ContDiff ℝ ∞ (cellDeriv h f u v w i j) := by
  have hH := contDiff_BH i
  have hG := contDiff_BG i
  have hH' := contDiff_BH j
  have hG' := contDiff_BG j
  have p1 : ∀ a, ContDiff ℝ ∞ (fun z : ℝ × ℝ => BH i a z.1) := fun a => (hH a).comp contDiff_fst
  have p2 : ∀ a, ContDiff ℝ ∞ (fun z : ℝ × ℝ => BG i a z.1) := fun a => (hG a).comp contDiff_fst
  have p3 : ∀ a, ContDiff ℝ ∞ (fun z : ℝ × ℝ => BH j a z.2) := fun a => (hH' a).comp contDiff_snd
  have p4 : ∀ a, ContDiff ℝ ∞ (fun z : ℝ × ℝ => BG j a z.2) := fun a => (hG' a).comp contDiff_snd
  unfold cellDeriv tensor
  simp only [Fin.sum_univ_two]
  have q1 := p1 0; have q2 := p1 1; have q3 := p2 0; have q4 := p2 1
  have q5 := p3 0; have q6 := p3 1; have q7 := p4 0; have q8 := p4 1
  fun_prop

theorem dP_cellDeriv (h : ℝ) (f u v w : Fin 2 → Fin 2 → ℝ) {i : ℕ} (hi : i ≤ 1) (j : ℕ) :
    dP (cellDeriv h f u v w i j) = cellDeriv h f u v w (i + 1) j := by
  funext z
  have h1 := hasDerivAt_section_p ((contDiff_cellDeriv h f u v w i j).differentiable (by simp))
    z.1 z.2
  have h2 := hasDerivAt_tensor_p h f u v w (fun b => BH j b z.2) (fun b => BG j b z.2)
    (Hp := fun p a => BH i a p) (Gp := fun p a => BG i a p) (p := z.1)
    (fun a => hasDerivAt_BH hi a z.1) (fun a => hasDerivAt_BG hi a z.1)
  exact h1.unique h2

theorem dQ_cellDeriv (h : ℝ) (f u v w : Fin 2 → Fin 2 → ℝ) (i : ℕ) {j : ℕ} (hj : j ≤ 1) :
    dQ (cellDeriv h f u v w i j) = cellDeriv h f u v w i (j + 1) := by
  funext z
  have h1 := hasDerivAt_section_q ((contDiff_cellDeriv h f u v w i j).differentiable (by simp))
    z.1 z.2
  have h2 := hasDerivAt_tensor_q h f u v w (fun a => BH i a z.1) (fun a => BG i a z.1)
    (Hq := fun q b => BH j b q) (Gq := fun q b => BG j b q) (q := z.2)
    (fun b => hasDerivAt_BH hj b z.2) (fun b => hasDerivAt_BG hj b z.2)
  exact h1.unique h2

theorem iterate_dQ_cellDeriv (h : ℝ) (f u v w : Fin 2 → Fin 2 → ℝ) (i : ℕ) {j : ℕ}
    (hj : j ≤ 2) : dQ^[j] (cellDeriv h f u v w i 0) = cellDeriv h f u v w i j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih (by omega), dQ_cellDeriv h f u v w i (by omega)]

theorem iterate_dP_cellDeriv (h : ℝ) (f u v w : Fin 2 → Fin 2 → ℝ) {i : ℕ} (hi : i ≤ 2)
    (j : ℕ) : dP^[i] (cellDeriv h f u v w 0 j) = cellDeriv h f u v w i j := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih (by omega), dP_cellDeriv h f u v w (by omega) j]

/-- `∂_p^i ∂_q^j` of the cell-coordinate interpolant is `cellDeriv … i j`. -/
theorem iterate_dP_dQ_cellDeriv (h : ℝ) (f u v w : Fin 2 → Fin 2 → ℝ) {i j : ℕ} (hi : i ≤ 2)
    (hj : j ≤ 2) :
    dP^[i] (dQ^[j] (cellDeriv h f u v w 0 0)) = cellDeriv h f u v w i j := by
  rw [iterate_dQ_cellDeriv h f u v w 0 hj, iterate_dP_cellDeriv h f u v w hi j]

theorem cellDeriv_zero_zero (h : ℝ) (f u v w : Fin 2 → Fin 2 → ℝ) (p q : ℝ) :
    cellDeriv h f u v w 0 0 (p, q) = interp h f u v w p q := rfl

/-- Linearity of the derivative tensors in the jet records. -/
theorem cellDeriv_sub (h : ℝ) (f u v w f' u' v' w' : Fin 2 → Fin 2 → ℝ) (i j : ℕ) (z : ℝ × ℝ) :
    cellDeriv h (f - f') (u - u') (v - v') (w - w') i j z =
      cellDeriv h f u v w i j z - cellDeriv h f' u' v' w' i j z := by
  simp only [cellDeriv, tensor, Fin.sum_univ_two, Pi.sub_apply]
  ring

/-! ### The physical readout -/

/-- The physical readout `(x, y) ↦ interp h f u v w ((x-x₀)/h) ((y-y₀)/h)` on the cell
`[x₀, x₀+h] × [y₀, y₀+h]` (a polynomial on all of `ℝ²`). -/
def readout (x₀ y₀ h : ℝ) (f u v w : Fin 2 → Fin 2 → ℝ) (z : ℝ × ℝ) : ℝ :=
  cellDeriv h f u v w 0 0 ((z.1 - x₀) / h, (z.2 - y₀) / h)

theorem contDiff_readout (x₀ y₀ h : ℝ) (f u v w : Fin 2 → Fin 2 → ℝ) :
    ContDiff ℝ ∞ (readout x₀ y₀ h f u v w) := by
  unfold readout
  refine (contDiff_cellDeriv h f u v w 0 0).comp ?_
  exact ((contDiff_fst.sub contDiff_const).div_const h).prodMk
    ((contDiff_snd.sub contDiff_const).div_const h)

theorem readout_comp_cellMap {x₀ y₀ h : ℝ} (hh : h ≠ 0) (f u v w : Fin 2 → Fin 2 → ℝ) :
    (fun z => readout x₀ y₀ h f u v w (cellMap x₀ y₀ h z)) = cellDeriv h f u v w 0 0 := by
  funext z
  simp only [readout, cellMap]
  congr 1
  ext <;> simp <;> field_simp

/-- **Chain rule of the readout**: the physical derivatives of the readout are the scaled
cell-coordinate tensors, `∂ₓ^i∂_y^j readout (x₀+hp, y₀+hq) = cellDeriv … i j (p, q) / h^{i+j}`
for `i, j ≤ 2`. -/
theorem iterate_dP_dQ_readout {x₀ y₀ h : ℝ} (hh : h ≠ 0) (f u v w : Fin 2 → Fin 2 → ℝ)
    {i j : ℕ} (hi : i ≤ 2) (hj : j ≤ 2) (p q : ℝ) :
    (dP^[i] (dQ^[j] (readout x₀ y₀ h f u v w))) (x₀ + h * p, y₀ + h * q) =
      cellDeriv h f u v w i j (p, q) / h ^ (i + j) := by
  have e := iterate_dP_dQ_comp_cellMap (contDiff_readout x₀ y₀ h f u v w) x₀ y₀ h i j (p, q)
  rw [readout_comp_cellMap hh, iterate_dP_dQ_cellDeriv h f u v w hi hj] at e
  have hpos : h ^ (i + j) ≠ 0 := pow_ne_zero _ hh
  rw [eq_div_iff hpos, e]
  simp only [cellMap]
  ring

/-! ### Stability and jet error -/

/-- The stability estimate `CubicHermite.interp_stability` for the derivative tensors:
`|cellDeriv i j (p, q)| ≤ 72 η h^{min 1 (i+j)}` on the unit cell, `i + j ≤ 2`. -/
theorem abs_cellDeriv_le {h η : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) {f u v w : Fin 2 → Fin 2 → ℝ}
    (hJ : JetBound h η f u v w) {i j : ℕ} (hij : i + j ≤ 2) {p q : ℝ}
    (hp : p ∈ Icc (0 : ℝ) 1) (hq : q ∈ Icc (0 : ℝ) 1) :
    |cellDeriv h f u v w i j (p, q)| ≤ 72 * η * h ^ min 1 (i + j) := by
  have hη : 0 ≤ η := (abs_nonneg _).trans (hJ.f_le 0 0)
  obtain ⟨s0, s1, s2, s3, s4, s5⟩ := interp_stability hh hh1 hJ hp hq
  have hi : i ≤ 2 := by omega
  have hj : j ≤ 2 := by omega
  interval_cases i <;> interval_cases j <;> simp only [Nat.reduceAdd] at hij ⊢
  · norm_num; exact s0.trans (by linarith)
  · norm_num; exact s2.trans (by nlinarith)
  · norm_num; exact s5
  · norm_num; exact s1.trans (by nlinarith)
  · norm_num; exact s4
  · omega
  · norm_num; exact s3
  · omega
  · omega

/-- **Jet error of the readout** on a cell: if `φ` is smooth with `|∂ₓ^a∂_y^b φ| ≤ M`
(`4 ≤ a + b ≤ 6`) on the cell and the corner records `f, u, v, w` differ from the exact records
`(φ, ∂ₓφ, ∂_yφ, ∂ₓ∂_yφ)` within `JetBound h η`, then for `i + j ≤ 2` and `(x, y)` in the cell
`|∂ₓ^i∂_y^j readout - ∂ₓ^i∂_y^j φ| ≤ 72 η h^{min 1 (i+j)} / h^{i+j} + hermRemConst · M · h^{4-(i+j)}`. -/
theorem readout_jet_error {φ : ℝ × ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) {x₀ y₀ h M η : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1)
    (hM : ∀ x ∈ Icc x₀ (x₀ + h), ∀ y ∈ Icc y₀ (y₀ + h), ∀ a b : ℕ, 4 ≤ a + b → a + b ≤ 6 →
      |(dP^[a] (dQ^[b] φ)) (x, y)| ≤ M)
    {f u v w : Fin 2 → Fin 2 → ℝ}
    (hJ : JetBound h η (f - cellF φ x₀ y₀ h) (u - cellU φ x₀ y₀ h) (v - cellV φ x₀ y₀ h)
      (w - cellW φ x₀ y₀ h))
    {i j : ℕ} (hij : i + j ≤ 2) {x y : ℝ} (hx : x ∈ Icc x₀ (x₀ + h)) (hy : y ∈ Icc y₀ (y₀ + h)) :
    |(dP^[i] (dQ^[j] (readout x₀ y₀ h f u v w))) (x, y) - (dP^[i] (dQ^[j] φ)) (x, y)| ≤
      72 * η * h ^ min 1 (i + j) / h ^ (i + j) + hermRemConst * M * h ^ (4 - (i + j)) := by
  set p := (x - x₀) / h
  set q := (y - y₀) / h
  have hp : p ∈ Icc (0 : ℝ) 1 := ⟨div_nonneg (by linarith [hx.1]) hh.le,
    (div_le_one hh).2 (by linarith [hx.2])⟩
  have hq : q ∈ Icc (0 : ℝ) 1 := ⟨div_nonneg (by linarith [hy.1]) hh.le,
    (div_le_one hh).2 (by linarith [hy.2])⟩
  have ex : x = x₀ + h * p := by simp only [p]; field_simp; ring
  have ey : y = y₀ + h * q := by simp only [q]; field_simp; ring
  have hi : i ≤ 2 := by omega
  have hj : j ≤ 2 := by omega
  rw [ex, ey, iterate_dP_dQ_readout hh.ne' f u v w hi hj p q]
  have hR := cell_remainder_scaled hφ hh hh1 hM hij hp hq
  have hS := abs_cellDeriv_le hh hh1 hJ hij hp hq
  rw [cellDeriv_sub] at hS
  have hpos : 0 < h ^ (i + j) := pow_pos hh _
  set A := cellDeriv h f u v w i j (p, q)
  set B := cellDeriv h (cellF φ x₀ y₀ h) (cellU φ x₀ y₀ h) (cellV φ x₀ y₀ h) (cellW φ x₀ y₀ h)
    i j (p, q)
  have hR' : |(dP^[i] (dQ^[j] φ)) (x₀ + h * p, y₀ + h * q) - B / h ^ (i + j)| ≤
      hermRemConst * M * h ^ (4 - (i + j)) := hR
  have hS' : |A / h ^ (i + j) - B / h ^ (i + j)| ≤ 72 * η * h ^ min 1 (i + j) / h ^ (i + j) := by
    rw [← sub_div, abs_div, abs_of_pos hpos]
    exact div_le_div_of_nonneg_right hS hpos.le
  calc |A / h ^ (i + j) - (dP^[i] (dQ^[j] φ)) (x₀ + h * p, y₀ + h * q)|
      ≤ |A / h ^ (i + j) - B / h ^ (i + j)| +
          |(dP^[i] (dQ^[j] φ)) (x₀ + h * p, y₀ + h * q) - B / h ^ (i + j)| := by
        rw [abs_sub_comm ((dP^[i] (dQ^[j] φ)) _) _]
        exact abs_sub_le _ _ _
    _ ≤ _ := add_le_add hS' hR'

theorem hermRemConst_nonneg : 0 ≤ hermRemConst := by
  unfold hermRemConst
  have h0 := TwoPointHermite.hermiteConst_nonneg 1 0
  have h1 := TwoPointHermite.hermiteConst_nonneg 1 1
  have h2 := TwoPointHermite.hermiteConst_nonneg 1 2
  positivity

/-- **`W^{1,∞}` part of `eq:supp-gowdy-second-jet`, cellwise**: with record errors `η ≤ c h²`,
the readout error and its first derivatives are `≤ (72 c + hermRemConst M) h²`. -/
theorem readout_jet_error_le_one {φ : ℝ × ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) {x₀ y₀ h M η c : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1)
    (hM : ∀ x ∈ Icc x₀ (x₀ + h), ∀ y ∈ Icc y₀ (y₀ + h), ∀ a b : ℕ, 4 ≤ a + b → a + b ≤ 6 →
      |(dP^[a] (dQ^[b] φ)) (x, y)| ≤ M)
    {f u v w : Fin 2 → Fin 2 → ℝ}
    (hJ : JetBound h η (f - cellF φ x₀ y₀ h) (u - cellU φ x₀ y₀ h) (v - cellV φ x₀ y₀ h)
      (w - cellW φ x₀ y₀ h)) (hη : η ≤ c * h ^ 2)
    {i j : ℕ} (hij : i + j ≤ 1) {x y : ℝ} (hx : x ∈ Icc x₀ (x₀ + h)) (hy : y ∈ Icc y₀ (y₀ + h)) :
    |(dP^[i] (dQ^[j] (readout x₀ y₀ h f u v w))) (x, y) - (dP^[i] (dQ^[j] φ)) (x, y)| ≤
      (72 * c + hermRemConst * M) * h ^ 2 := by
  have hE := readout_jet_error hφ hh hh1 hM hJ (by omega : i + j ≤ 2) hx hy
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM x₀ ⟨le_refl _, by linarith⟩ y₀
    ⟨le_refl _, by linarith⟩ 4 0 (by norm_num) (by norm_num))
  have hR0 := hermRemConst_nonneg
  have hη0 : 0 ≤ η := (abs_nonneg _).trans (hJ.f_le 0 0)
  have hk : i + j = 0 ∨ i + j = 1 := by omega
  have hRM : 0 ≤ hermRemConst * M := mul_nonneg hR0 hM0
  rcases hk with hk | hk
  · rw [hk] at hE
    norm_num at hE
    have : h ^ 4 ≤ h ^ 2 := pow_le_pow_of_le_one hh.le hh1 (by norm_num)
    nlinarith [mul_le_mul_of_nonneg_left this hRM]
  · rw [hk] at hE
    norm_num at hE
    have e : 72 * η * h / h = 72 * η := by field_simp
    rw [e] at hE
    have : h ^ 3 ≤ h ^ 2 := pow_le_pow_of_le_one hh.le hh1 (by norm_num)
    nlinarith [mul_le_mul_of_nonneg_left this hRM]

/-- **Second-derivative part of `eq:supp-gowdy-second-jet`, cellwise**: with record errors
`η ≤ c h²`, the second derivatives of the readout error are `≤ (72 c + hermRemConst M) h`. -/
theorem readout_jet_error_two {φ : ℝ × ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) {x₀ y₀ h M η c : ℝ}
    (hh : 0 < h) (hh1 : h ≤ 1)
    (hM : ∀ x ∈ Icc x₀ (x₀ + h), ∀ y ∈ Icc y₀ (y₀ + h), ∀ a b : ℕ, 4 ≤ a + b → a + b ≤ 6 →
      |(dP^[a] (dQ^[b] φ)) (x, y)| ≤ M)
    {f u v w : Fin 2 → Fin 2 → ℝ}
    (hJ : JetBound h η (f - cellF φ x₀ y₀ h) (u - cellU φ x₀ y₀ h) (v - cellV φ x₀ y₀ h)
      (w - cellW φ x₀ y₀ h)) (hη : η ≤ c * h ^ 2)
    {i j : ℕ} (hij : i + j = 2) {x y : ℝ} (hx : x ∈ Icc x₀ (x₀ + h)) (hy : y ∈ Icc y₀ (y₀ + h)) :
    |(dP^[i] (dQ^[j] (readout x₀ y₀ h f u v w))) (x, y) - (dP^[i] (dQ^[j] φ)) (x, y)| ≤
      (72 * c + hermRemConst * M) * h := by
  have hE := readout_jet_error hφ hh hh1 hM hJ (by omega : i + j ≤ 2) hx hy
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM x₀ ⟨le_refl _, by linarith⟩ y₀
    ⟨le_refl _, by linarith⟩ 4 0 (by norm_num) (by norm_num))
  have hR0 := hermRemConst_nonneg
  have hRM : 0 ≤ hermRemConst * M := mul_nonneg hR0 hM0
  rw [hij] at hE
  norm_num at hE
  have e : 72 * η * h / h ^ 2 ≤ 72 * c * h := by
    rw [div_le_iff₀ (by positivity)]
    have : 72 * η * h ≤ 72 * (c * h ^ 2) * h := by
      have := mul_le_mul_of_nonneg_right hη hh.le; nlinarith
    nlinarith
  have : h ^ 2 ≤ h := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left this hRM]

/-! ### `C¹` gluing across cell interfaces -/

/-- The derivative tensors at the right edge `p = 1` of one cell coincide with those at the left
edge `p = 0` of the next cell when the jet records at the shared nodes coincide (`i ≤ 1`). -/
theorem cellDeriv_glue_p (h : ℝ) {f u v w f' u' v' w' : Fin 2 → Fin 2 → ℝ}
    (hf : ∀ b, f' 0 b = f 1 b) (hu : ∀ b, u' 0 b = u 1 b) (hv : ∀ b, v' 0 b = v 1 b)
    (hw : ∀ b, w' 0 b = w 1 b) {i : ℕ} (hi : i ≤ 1) (j : ℕ) (q : ℝ) :
    cellDeriv h f u v w i j (1, q) = cellDeriv h f' u' v' w' i j (0, q) := by
  interval_cases i
  · simp only [cellDeriv, tensor, Fin.sum_univ_two, BH, BG, basisH_zero, basisH_one,
      basisG_zero, basisG_one, hf, hu, hv, hw]
    ring
  · simp only [cellDeriv, tensor, Fin.sum_univ_two, BH, BG, basisHD_zero, basisHD_one,
      basisGD_zero, basisGD_one, hf, hu, hv, hw]
    ring

/-- The derivative tensors at the top edge `q = 1` of one cell coincide with those at the bottom
edge `q = 0` of the next cell when the jet records at the shared nodes coincide (`j ≤ 1`). -/
theorem cellDeriv_glue_q (h : ℝ) {f u v w f' u' v' w' : Fin 2 → Fin 2 → ℝ}
    (hf : ∀ a, f' a 0 = f a 1) (hu : ∀ a, u' a 0 = u a 1) (hv : ∀ a, v' a 0 = v a 1)
    (hw : ∀ a, w' a 0 = w a 1) (i : ℕ) {j : ℕ} (hj : j ≤ 1) (p : ℝ) :
    cellDeriv h f u v w i j (p, 1) = cellDeriv h f' u' v' w' i j (p, 0) := by
  interval_cases j
  · simp only [cellDeriv, tensor, Fin.sum_univ_two, BH, BG, basisH_zero, basisH_one,
      basisG_zero, basisG_one, hf, hu, hv, hw]
    ring
  · simp only [cellDeriv, tensor, Fin.sum_univ_two, BH, BG, basisHD_zero, basisHD_one,
      basisGD_zero, basisGD_one, hf, hu, hv, hw]
    ring

/-- **`C¹` gluing in `x`**: if the cell `[x₀+h, x₀+2h] × [y₀, y₀+h]` shares with
`[x₀, x₀+h] × [y₀, y₀+h]` the jet records at the two nodes of the common edge `x = x₀ + h`, the two
readouts have equal values, equal `x`-derivatives and equal `y`-derivatives (up to order 2) on
that edge: the cellwise readout is `C¹` across the interface. -/
theorem readout_glue_x {x₀ y₀ h : ℝ} (hh : h ≠ 0) {f u v w f' u' v' w' : Fin 2 → Fin 2 → ℝ}
    (hf : ∀ b, f' 0 b = f 1 b) (hu : ∀ b, u' 0 b = u 1 b) (hv : ∀ b, v' 0 b = v 1 b)
    (hw : ∀ b, w' 0 b = w 1 b) {i j : ℕ} (hi : i ≤ 1) (hj : j ≤ 2) (y : ℝ) :
    (dP^[i] (dQ^[j] (readout x₀ y₀ h f u v w))) (x₀ + h, y) =
      (dP^[i] (dQ^[j] (readout (x₀ + h) y₀ h f' u' v' w'))) (x₀ + h, y) := by
  have ey : y = y₀ + h * ((y - y₀) / h) := by field_simp; ring
  have e1 := iterate_dP_dQ_readout (x₀ := x₀) (y₀ := y₀) hh f u v w (by omega : i ≤ 2) hj 1
    ((y - y₀) / h)
  have e2 := iterate_dP_dQ_readout (x₀ := x₀ + h) (y₀ := y₀) hh f' u' v' w' (by omega : i ≤ 2) hj 0
    ((y - y₀) / h)
  rw [mul_one, ← ey] at e1
  rw [mul_zero, add_zero, ← ey] at e2
  rw [e1, e2, cellDeriv_glue_p h hf hu hv hw hi j]

/-- **`C¹` gluing in `y`** (the analogue of `readout_glue_x` across `y = y₀ + h`). -/
theorem readout_glue_y {x₀ y₀ h : ℝ} (hh : h ≠ 0) {f u v w f' u' v' w' : Fin 2 → Fin 2 → ℝ}
    (hf : ∀ a, f' a 0 = f a 1) (hu : ∀ a, u' a 0 = u a 1) (hv : ∀ a, v' a 0 = v a 1)
    (hw : ∀ a, w' a 0 = w a 1) {i j : ℕ} (hi : i ≤ 2) (hj : j ≤ 1) (x : ℝ) :
    (dP^[i] (dQ^[j] (readout x₀ y₀ h f u v w))) (x, y₀ + h) =
      (dP^[i] (dQ^[j] (readout x₀ (y₀ + h) h f' u' v' w'))) (x, y₀ + h) := by
  have ex : x = x₀ + h * ((x - x₀) / h) := by field_simp; ring
  have e1 := iterate_dP_dQ_readout (x₀ := x₀) (y₀ := y₀) hh f u v w hi (by omega : j ≤ 2)
    ((x - x₀) / h) 1
  have e2 := iterate_dP_dQ_readout (x₀ := x₀) (y₀ := y₀ + h) hh f' u' v' w' hi
    (by omega : j ≤ 2) ((x - x₀) / h) 0
  rw [mul_one, ← ex] at e1
  rw [mul_zero, add_zero, ← ex] at e2
  rw [e1, e2, cellDeriv_glue_q h hf hu hv hw i hj]

end

end RenewalGeometry.TensorHermiteReadout
