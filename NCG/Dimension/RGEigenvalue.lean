/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The engineering eigenvalue of the block-renewal map

**Theorem `thm:rg-eigenvalue`** (continuum part): the block-renewal map
`(R_b σ)(ξ) = b·σ(ξ/b)` acts diagonally on homogeneous symbols of joint
degree `k`, with exact eigenvalue `b^{1−k}`
(`NCG.blockRG_eigenvalue`).  For the volume-dual response of degree
`k = d − 2` the eigenvalue is `λ_d = b^{3−d}`.

**Corollary `cor:relevance`** (relevance trichotomy): with `b ≥ 2`,

* `d = 3` — marginal/principal: `λ = 1` (`NCG.relevance_marginal`);
* `d ≥ 5` — irrelevant: `λ < 1` (`NCG.relevance_irrelevant`);
* `d = 1` — no bivector domain: every alternating bilinear form on a
  one-dimensional space vanishes (`NCG.alternating_rank_one_eq_zero`).

The lattice band-error estimate of `thm:rg-eigenvalue` (an `O((bh)²Λ²)`
Taylor bound) is not formalised; the exact continuum eigenvalue above is
the part used by the dimensional-selection corollary. -/

namespace NCG

variable {E V : Type*} [AddCommGroup E] [Module ℝ E]
  [AddCommGroup V] [Module ℝ V]

/-- The **block-renewal map** on symbols:
`(R_b σ)(ξ) = b · σ(ξ/b)` (Construction `constr:block-rg`). -/
noncomputable def blockRG (b : ℝ) (σ : E → V) : E → V :=
  fun ξ => b • σ (b⁻¹ • ξ)

/-- A symbol of **joint degree `k`**: homogeneous of degree `k` under
positive scaling of the momentum. -/
def IsHomogeneous (k : ℕ) (σ : E → V) : Prop :=
  ∀ (c : ℝ) (ξ : E), 0 < c → σ (c • ξ) = c ^ k • σ ξ

/-- **Theorem `thm:rg-eigenvalue`** (continuum eigenvalue): on symbols of
joint degree `k` the block-renewal map acts with exact eigenvalue
`b^{1−k}`.  In particular the volume-dual response of degree `k = d − 2`
has eigenvalue `λ_d = b^{3−d}`. -/
theorem blockRG_eigenvalue {b : ℝ} (hb : 0 < b) {k : ℕ} {σ : E → V}
    (hσ : IsHomogeneous k σ) (ξ : E) :
    blockRG b σ ξ = (b ^ ((1:ℤ) - k)) • σ ξ := by
  unfold blockRG
  rw [hσ b⁻¹ ξ (inv_pos.mpr hb), smul_smul]
  congr 1
  rw [inv_pow, ← zpow_natCast b k, ← zpow_neg, sub_eq_add_neg,
    zpow_add₀ hb.ne', zpow_one]

/-- **Corollary `cor:relevance`, marginal case**: for `b > 1` the
eigenvalue `b^{3−d}` equals `1` exactly at `d = 3` — the volume-dual
response is a principal (marginal) observable only in three spatial
dimensions. -/
theorem relevance_marginal {b : ℝ} (hb : 1 < b) {d : ℕ} :
    b ^ ((3:ℤ) - d) = 1 ↔ d = 3 := by
  rw [show (1:ℝ) = b ^ (0:ℤ) by simp,
    (zpow_right_injective₀ (by linarith) (by linarith)).eq_iff]
  omega

/-- **Corollary `cor:relevance`, irrelevant case**: for `b > 1` and every
rank `d ≥ 5` (in particular every higher odd primitive rank) the
eigenvalue is strictly contracting, `b^{3−d} < 1`: the response is
RG-irrelevant. -/
theorem relevance_irrelevant {b : ℝ} (hb : 1 < b) {d : ℕ} (hd : 5 ≤ d) :
    b ^ ((3:ℤ) - d) < 1 :=
  zpow_lt_one_of_neg₀ hb (by omega)

/-- **Corollary `cor:relevance`, `d = 1` case** (no bivector domain):
on a one-dimensional spatial space every alternating bilinear form
vanishes — `⋀²V_sp = 0`, so the two-reset response has empty domain. -/
theorem alternating_rank_one_eq_zero (B : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ)
    (halt : ∀ v, B v v = 0) : B = 0 := by
  refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
  change B x y = 0
  have hxy : B x y = (x * y) * B 1 1 := by
    have hx1 : x • (1:ℝ) = x := by rw [smul_eq_mul, mul_one]
    have hy1 : y • (1:ℝ) = y := by rw [smul_eq_mul, mul_one]
    have hBx : B x = x • B 1 := by
      calc B x = B (x • (1:ℝ)) := by rw [hx1]
        _ = x • B 1 := map_smul B x 1
    have hB1y : B 1 y = y * B 1 1 := by
      calc B 1 y = B 1 (y • (1:ℝ)) := by rw [hy1]
        _ = y • B 1 1 := map_smul (B 1) y 1
        _ = y * B 1 1 := smul_eq_mul y _
    rw [hBx, LinearMap.smul_apply, smul_eq_mul, hB1y]
    ring
  rw [hxy, halt 1, mul_zero]

end NCG
