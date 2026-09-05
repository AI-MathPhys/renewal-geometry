/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.MatFunShiftExact
import NCG.Grand.PetzRecoveryExact

/-!
# The resolvent s-form of a faithful state

Step (B1) of the BKM programme for `cor:accepted-BKM-loss` (QS.5): the
Bogoliubov–Kubo–Mori quadratic form has the resolvent representation
`g_σ(v,v) = ∫₀^∞ Tr(v (σ+s)⁻¹ v (σ+s)⁻¹) ds`, so its finite theory rests
on the **s-form** `sForm σ v s = Re Tr(v (σ+s)⁻¹ v (σ+s)⁻¹)`.

* `resolvent`: `(σ + s·1)⁻¹` through the spectral calculus, with the
  two-sided inverse laws for faithful `σ`;
* `trace_herm_diag_sq_re`: the doubly indexed trace formula;
* `sForm_eq_sum`: the boxed spectral formula
  `sForm σ v s = Σᵢⱼ |v̂ᵢⱼ|² (qᵢ+s)⁻¹(qⱼ+s)⁻¹`;
* `sForm_nonneg`: positivity.
-/

open Matrix Unitary Finset
open scoped ComplexOrder

namespace NCG
namespace QRE

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {σ v : Matrix n n ℂ}

/-! ### The resolvent -/

/-- The resolvent `(σ + s·1)⁻¹` through the spectral calculus. -/
noncomputable def resolvent (hσ : σ.IsHermitian) (s : ℝ) :
    Matrix n n ℂ :=
  matFun hσ fun x => (x + s)⁻¹

theorem resolvent_isHermitian (hσ : σ.IsHermitian) (s : ℝ) :
    (resolvent hσ s).IsHermitian :=
  Petz.matFun_isHermitian hσ _

/-- `(σ + s·1) · R_s = 1` for faithful `σ` and `s > 0`. -/
theorem shift_mul_resolvent (hσp : σ.PosDef) {s : ℝ} (hs : 0 < s) :
    (σ + s • 1) * resolvent hσp.1 s = 1 := by
  rw [shift_eq_matFun hσp.1 s]
  unfold resolvent
  rw [matFun_mul]
  have h1 : matFun hσp.1 (fun x => (x + s) * (x + s)⁻¹) =
      matFun hσp.1 (fun _ => 1) := by
    refine Petz.matFun_congr hσp.1 _ _ fun i => ?_
    have hpos : 0 < hσp.1.eigenvalues i + s :=
      add_pos_of_nonneg_of_pos (hσp.posSemidef.eigenvalues_nonneg i) hs
    exact mul_inv_cancel₀ hpos.ne'
  rw [h1, Petz.matFun_one]

/-- `R_s · (σ + s·1) = 1` for faithful `σ` and `s > 0`. -/
theorem resolvent_mul_shift (hσp : σ.PosDef) {s : ℝ} (hs : 0 < s) :
    resolvent hσp.1 s * (σ + s • 1) = 1 :=
  mul_eq_one_comm.mp (shift_mul_resolvent hσp hs)

/-! ### The tangent in the eigenbasis -/

/-- The tangent conjugated into the eigenbasis of `σ`: `v̂ = U^* v U`. -/
noncomputable def tangentIn (hσ : σ.IsHermitian) (v : Matrix n n ℂ) :
    Matrix n n ℂ :=
  star (hσ.eigenvectorUnitary : Matrix n n ℂ) * v *
    (hσ.eigenvectorUnitary : Matrix n n ℂ)

theorem tangentIn_isHermitian (hσ : σ.IsHermitian) (hv : v.IsHermitian) :
    (tangentIn hσ v).IsHermitian := by
  unfold tangentIn Matrix.IsHermitian
  rw [← Matrix.star_eq_conjTranspose, star_mul, star_mul, star_star]
  rw [Matrix.star_eq_conjTranspose v, hv.eq, Matrix.mul_assoc]

/-- Reconstruction `v = U v̂ U^*`. -/
theorem tangentIn_reconstruct (hσ : σ.IsHermitian) (v : Matrix n n ℂ) :
    (hσ.eigenvectorUnitary : Matrix n n ℂ) * tangentIn hσ v *
      star (hσ.eigenvectorUnitary : Matrix n n ℂ) = v := by
  unfold tangentIn
  calc (hσ.eigenvectorUnitary : Matrix n n ℂ) *
        (star (hσ.eigenvectorUnitary : Matrix n n ℂ) * v *
          (hσ.eigenvectorUnitary : Matrix n n ℂ)) *
        star (hσ.eigenvectorUnitary : Matrix n n ℂ)
      = ((hσ.eigenvectorUnitary : Matrix n n ℂ) *
          star (hσ.eigenvectorUnitary : Matrix n n ℂ)) * v *
          ((hσ.eigenvectorUnitary : Matrix n n ℂ) *
          star (hσ.eigenvectorUnitary : Matrix n n ℂ)) := by
        simp only [Matrix.mul_assoc]
    _ = v := by
        rw [coe_mul_star hσ.eigenvectorUnitary, Matrix.one_mul,
          Matrix.mul_one]

/-! ### The doubly indexed trace formula -/

/-- `Re Tr(W D W D) = Σᵢⱼ |Wᵢⱼ|² dⱼ dᵢ` for Hermitian `W`. -/
theorem trace_herm_diag_sq_re (d : n → ℝ) {W : Matrix n n ℂ}
    (hW : W.IsHermitian) :
    ((W * diagonal (RCLike.ofReal ∘ d) * W *
        diagonal (RCLike.ofReal ∘ d)).trace).re =
      ∑ i, ∑ j, Complex.normSq (W i j) * (d j * d i) := by
  have hsym : ∀ i j, W j i = star (W i j) := by
    intro i j
    have h := congrFun (congrFun hW.eq i) j
    rw [Matrix.conjTranspose_apply] at h
    rw [← h, star_star]
  have htrace : (W * diagonal (RCLike.ofReal ∘ d) * W *
      diagonal (RCLike.ofReal ∘ d)).trace =
      ∑ i, ∑ j, W i j * (d j : ℂ) * (W j i * (d i : ℂ)) := by
    rw [Matrix.trace]
    simp only [Matrix.diag]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show W * diagonal (RCLike.ofReal ∘ d) * W *
        diagonal (RCLike.ofReal ∘ d) =
        (W * diagonal (RCLike.ofReal ∘ d)) *
        (W * diagonal (RCLike.ofReal ∘ d)) from by
      simp only [Matrix.mul_assoc]]
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mul_diagonal, Matrix.mul_diagonal]
    rfl
  rw [htrace, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hsym i j]
  have hterm : W i j * (d j : ℂ) * (star (W i j) * (d i : ℂ)) =
      ((Complex.normSq (W i j) * (d j * d i) : ℝ) : ℂ) := by
    rw [Complex.star_def]
    push_cast
    rw [show W i j * (d j : ℂ) * ((starRingEnd ℂ) (W i j) * (d i : ℂ)) =
        W i j * (starRingEnd ℂ) (W i j) * ((d j : ℂ) * (d i : ℂ)) from by
      ring]
    rw [Complex.mul_conj]
  rw [hterm]
  exact Complex.ofReal_re _

/-! ### The s-form -/

/-- **The s-form** `Re Tr(v R_s v R_s)` — the integrand of the BKM
resolvent representation. -/
noncomputable def sForm (hσ : σ.IsHermitian) (v : Matrix n n ℂ)
    (s : ℝ) : ℝ :=
  ((v * resolvent hσ s * v * resolvent hσ s).trace).re

set_option maxHeartbeats 1600000 in -- eigenbasis collapse
/-- **The spectral formula**:
`sForm σ v s = Σᵢⱼ |v̂ᵢⱼ|² (qᵢ+s)⁻¹ (qⱼ+s)⁻¹` for Hermitian `v`. -/
theorem sForm_eq_sum (hσ : σ.IsHermitian) (hv : v.IsHermitian) (s : ℝ) :
    sForm hσ v s =
      ∑ i, ∑ j, Complex.normSq (tangentIn hσ v i j) *
        ((hσ.eigenvalues j + s)⁻¹ * (hσ.eigenvalues i + s)⁻¹) := by
  unfold sForm
  have hRdec : resolvent hσ s =
      (hσ.eigenvectorUnitary : Matrix n n ℂ) *
        diagonal (RCLike.ofReal ∘ fun i => (hσ.eigenvalues i + s)⁻¹) *
        star (hσ.eigenvectorUnitary : Matrix n n ℂ) := by
    unfold resolvent matFun
    rw [conjStarAlgAut_apply]
  have hvdec := (tangentIn_reconstruct hσ v).symm
  set U : Matrix n n ℂ := (hσ.eigenvectorUnitary : Matrix n n ℂ)
    with hU
  set What : Matrix n n ℂ := tangentIn hσ v
  set D : Matrix n n ℂ :=
    diagonal (RCLike.ofReal ∘ fun i => (hσ.eigenvalues i + s)⁻¹)
  have hcollapse : v * resolvent hσ s * v * resolvent hσ s =
      U * (What * D * What * D) * star U := by
    rw [hRdec, hvdec]
    have hUU : star U * U = 1 := star_mul_coe hσ.eigenvectorUnitary
    calc (U * What * star U) * (U * D * star U) *
          (U * What * star U) * (U * D * star U)
        = U * (What * (star U * U) * D * (star U * U) * What *
            (star U * U) * D) * star U := by
          simp only [Matrix.mul_assoc]
      _ = U * (What * D * What * D) * star U := by
          rw [hUU]
          simp only [Matrix.mul_one]
  rw [hcollapse]
  have htr : (U * (What * D * What * D) * star U).trace =
      (What * D * What * D).trace := by
    rw [Matrix.trace_mul_cycle, hU, star_mul_coe hσ.eigenvectorUnitary,
      Matrix.one_mul]
  rw [htr]
  exact trace_herm_diag_sq_re _ (tangentIn_isHermitian hσ hv)

/-- Positivity of the s-form at a positive semidefinite base, `s > 0`. -/
theorem sForm_nonneg (hσ : σ.PosSemidef) (hv : v.IsHermitian) {s : ℝ}
    (hs : 0 < s) : 0 ≤ sForm hσ.1 v s := by
  rw [sForm_eq_sum hσ.1 hv s]
  refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
  have hi : 0 < hσ.1.eigenvalues i + s :=
    add_pos_of_nonneg_of_pos (hσ.eigenvalues_nonneg i) hs
  have hj : 0 < hσ.1.eigenvalues j + s :=
    add_pos_of_nonneg_of_pos (hσ.eigenvalues_nonneg j) hs
  exact mul_nonneg (Complex.normSq_nonneg _)
    (mul_nonneg (inv_nonneg.mpr hj.le) (inv_nonneg.mpr hi.le))

end QRE
end NCG
