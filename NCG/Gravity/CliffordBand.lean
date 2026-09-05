/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The massive renewal band: exact Perron origin and Clifford
projectors (GR_emergence, Phase 1)

* `frame_square_nonneg`, `frame_square_elliptic` —
  `lem:cp-elliptic`: the positive-endpoint cometric
  `g⁺(θ) = Σₐ ⟨eₐ, θ⟩²` is nonnegative, and when the frame spans it
  has empty real characteristic variety away from `θ = 0` — the
  positive endpoint is elliptic and carries no nonzero real null
  directions (`thm:positive-obstruction`(a); part (b) is the
  polyhedral-cone obstruction `NCG.polyhedral_obstruction`);
* `velocityJump`, `velocityJump_mulVec_top/bot`,
  `velocityJump_top_eigenvector_pos`, `band_eigenvalue_max`,
  `band_identity`, `band_le_causal` — `thm:exact-renewal-band`: the
  Perron eigenvalue of the tilted two-state velocity-jump generator
  is exactly `h(θ) = √(λ² + c²θ²) - λ`, with positive eigenvector
  (so it is genuinely the Perron root), the exact identity
  `h(θ)(s + λ) = c²θ²` interpolating the diffusive and causal
  limits, and the causal bound `h(θ) ≤ c|θ|`;
* `cliffordProj`, `cliffordProj_idem`, `cliffordProj_orth`,
  `cliffordProj_sum`, `cliffordProj_eigen`, `massive_band_gap` —
  `prop:model-W2`: for a Clifford symbol with `N² = r·1`
  (`r = λ² + c²g(θ,θ)`), the Riesz projectors
  `Π± = ½(1 ± N/√r)` are idempotent, orthogonal, complete, satisfy
  `(N - λ)Π± = (±√r - λ)Π±`, and the two branches are separated by
  the uniform gap `2√r ≥ 2λ_min`.
-/

namespace NCG

open Real

/-! ## `lem:cp-elliptic` / `thm:positive-obstruction`(a) -/

section Elliptic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The frame-square cometric of the positive endpoint is
nonnegative. -/
theorem frame_square_nonneg {m : ℕ} (e : Fin m → E) (theta : E) :
    0 ≤ ∑ a, (inner ℝ (e a) theta) ^ 2 :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- `lem:cp-elliptic`: if the local frame spans, the real
characteristic variety of the frame-square cometric is empty away
from the zero covector — the positive endpoint is elliptic and has
no nonzero real null directions. -/
theorem frame_square_elliptic {m : ℕ} (e : Fin m → E)
    (hspan : Submodule.span ℝ (Set.range e) = ⊤) (theta : E)
    (hnull : ∑ a, (inner ℝ (e a) theta) ^ 2 = 0) :
    theta = 0 := by
  have hz : ∀ a, inner ℝ (e a) theta = 0 := by
    intro a
    have h := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => sq_nonneg (inner ℝ (e i) theta))).mp hnull a (Finset.mem_univ a)
    exact pow_eq_zero_iff (two_ne_zero) |>.mp h
  have hmem : theta ∈ (Submodule.span ℝ (Set.range e))ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro u hu
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      exact hz a
    | zero => simp
    | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
    | smul c x _ hx => rw [inner_smul_left, hx, mul_zero]
  rw [hspan, Submodule.top_orthogonal_eq_bot, Submodule.mem_bot] at hmem
  exact hmem

end Elliptic

/-! ## `thm:exact-renewal-band` -/

section VelocityJump

variable (c lam theta : ℝ)

/-- The tilted generator of the two-state velocity-jump renewal
process. -/
def velocityJump : Matrix (Fin 2) (Fin 2) ℝ :=
  !![c * theta - lam, lam; lam, -(c * theta) - lam]

/-- The band value `h(θ) = √(λ² + c²θ²) - λ` is an eigenvalue of the
tilted generator, with eigenvector `(λ, s - cθ)`. -/
theorem velocityJump_mulVec_top :
    (velocityJump c lam theta).mulVec
        ![lam, Real.sqrt (lam ^ 2 + c ^ 2 * theta ^ 2) - c * theta]
      = (Real.sqrt (lam ^ 2 + c ^ 2 * theta ^ 2) - lam)
        • ![lam, Real.sqrt (lam ^ 2 + c ^ 2 * theta ^ 2) - c * theta] := by
  set s := Real.sqrt (lam ^ 2 + c ^ 2 * theta ^ 2) with hs
  have hsq : s ^ 2 = lam ^ 2 + c ^ 2 * theta ^ 2 :=
    Real.sq_sqrt (by positivity)
  funext i
  fin_cases i <;>
    simp [velocityJump, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
    nlinarith [hsq]

/-- The complementary branch `-(s + λ)` is an eigenvalue with
eigenvector `(λ, -(s + cθ))`. -/
theorem velocityJump_mulVec_bot :
    (velocityJump c lam theta).mulVec
        ![lam, -(Real.sqrt (lam ^ 2 + c ^ 2 * theta ^ 2) + c * theta)]
      = (-(Real.sqrt (lam ^ 2 + c ^ 2 * theta ^ 2) + lam))
        • ![lam, -(Real.sqrt (lam ^ 2 + c ^ 2 * theta ^ 2) + c * theta)] := by
  set s := Real.sqrt (lam ^ 2 + c ^ 2 * theta ^ 2) with hs
  have hsq : s ^ 2 = lam ^ 2 + c ^ 2 * theta ^ 2 :=
    Real.sq_sqrt (by positivity)
  funext i
  fin_cases i <;>
    simp [velocityJump, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
    nlinarith [hsq]

/-- For `λ > 0` the band eigenvector is strictly positive, so
`h(θ) = s - λ` is genuinely the Perron eigenvalue. -/
theorem velocityJump_top_eigenvector_pos (hlam : 0 < lam) :
    0 < lam ∧
    0 < Real.sqrt (lam ^ 2 + c ^ 2 * theta ^ 2) - c * theta := by
  refine ⟨hlam, ?_⟩
  have h1 : c * theta < Real.sqrt (lam ^ 2 + c ^ 2 * theta ^ 2) := by
    rcases le_or_gt (c * theta) 0 with h | h
    · exact lt_of_le_of_lt h (Real.sqrt_pos.mpr (by positivity))
    · have h2 : (c * theta) ^ 2 < lam ^ 2 + c ^ 2 * theta ^ 2 := by
        nlinarith
      calc c * theta = Real.sqrt ((c * theta) ^ 2) := by
            rw [Real.sqrt_sq h.le]
        _ < Real.sqrt (lam ^ 2 + c ^ 2 * theta ^ 2) := by
            exact Real.sqrt_lt_sqrt (by positivity) h2
  linarith

/-- The band branch dominates the complementary branch:
`s - λ ≥ -(s + λ)`, with strict inequality whenever `s > 0`. -/
theorem band_eigenvalue_max :
    -(Real.sqrt (lam ^ 2 + c ^ 2 * theta ^ 2) + lam)
      ≤ Real.sqrt (lam ^ 2 + c ^ 2 * theta ^ 2) - lam := by
  have := Real.sqrt_nonneg (lam ^ 2 + c ^ 2 * theta ^ 2)
  linarith

/-- **Exact band identity**: `h(θ)·(s + λ) = c²θ²`.  This single
identity interpolates the manuscript's two asymptotic regimes: the
diffusive limit `h ≈ c²θ²/(2λ)` for small momentum and the causal
limit `h ≈ c|θ|` for large momentum. -/
theorem band_identity :
    (Real.sqrt (lam ^ 2 + c ^ 2 * theta ^ 2) - lam)
      * (Real.sqrt (lam ^ 2 + c ^ 2 * theta ^ 2) + lam)
    = c ^ 2 * theta ^ 2 := by
  have hsq : Real.sqrt (lam ^ 2 + c ^ 2 * theta ^ 2) ^ 2
      = lam ^ 2 + c ^ 2 * theta ^ 2 := Real.sq_sqrt (by positivity)
  nlinarith [hsq]

/-- Causal bound: `h(θ) ≤ c·|θ|` for `λ ≥ 0` — the band never
propagates faster than the signed-cone speed. -/
theorem band_le_causal (hlam : 0 ≤ lam) :
    Real.sqrt (lam ^ 2 + c ^ 2 * theta ^ 2) - lam ≤ |c| * |theta| := by
  have h1 : Real.sqrt (lam ^ 2 + c ^ 2 * theta ^ 2)
      ≤ lam + |c| * |theta| := by
    rw [show lam ^ 2 + c ^ 2 * theta ^ 2
        = lam ^ 2 + (|c| * |theta|) ^ 2 by
      rw [mul_pow, sq_abs, sq_abs]]
    have h2 : lam ^ 2 + (|c| * |theta|) ^ 2 ≤ (lam + |c| * |theta|) ^ 2 := by
      nlinarith [abs_nonneg c, abs_nonneg theta,
        mul_nonneg (abs_nonneg c) (abs_nonneg theta)]
    calc Real.sqrt (lam ^ 2 + (|c| * |theta|) ^ 2)
        ≤ Real.sqrt ((lam + |c| * |theta|) ^ 2) :=
          Real.sqrt_le_sqrt h2
      _ = lam + |c| * |theta| := by
          rw [Real.sqrt_sq (by positivity)]
  linarith

end VelocityJump

/-! ## `prop:model-W2` -/

section CliffordProjectors

variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- The Riesz projector `Π± = ½(1 ± N/√r)` of a Clifford symbol with
`N² = r·1`. -/
noncomputable def cliffordProj (N : A) (r : ℝ) (sign : ℝ) : A :=
  (2:ℝ)⁻¹ • (1 + (sign * (Real.sqrt r)⁻¹) • N)

/-- The coefficient identity `(σ/√r)² · r = σ²`. -/
theorem cliffordProj_coef (r : ℝ) (hr : 0 < r) (sign : ℝ) :
    sign * (Real.sqrt r)⁻¹ * (sign * (Real.sqrt r)⁻¹) * r = sign ^ 2 := by
  have hs : Real.sqrt r ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hr)
  have hsq : Real.sqrt r ^ 2 = r := Real.sq_sqrt hr.le
  field_simp
  nlinarith [hsq]

/-- The square of the shifted symbol: `(a•N)² = (σ²)·1` for
`a = σ/√r`. -/
theorem cliffordProj_smul_sq (N : A) (r : ℝ) (hr : 0 < r)
    (hN : N * N = algebraMap ℝ A r) (sign : ℝ) (hsgn : sign ^ 2 = 1) :
    ((sign * (Real.sqrt r)⁻¹) • N) * ((sign * (Real.sqrt r)⁻¹) • N)
      = (1 : A) := by
  rw [smul_mul_smul_comm, hN, Algebra.algebraMap_eq_smul_one, smul_smul,
    cliffordProj_coef r hr sign, hsgn, one_smul]

/-- `prop:model-W2` (idempotence): `Π±² = Π±`. -/
theorem cliffordProj_idem (N : A) (r : ℝ) (hr : 0 < r)
    (hN : N * N = algebraMap ℝ A r) (sign : ℝ) (hsgn : sign ^ 2 = 1) :
    cliffordProj N r sign * cliffordProj N r sign
      = cliffordProj N r sign := by
  set a : ℝ := sign * (Real.sqrt r)⁻¹ with ha
  have h1 : (a • N) * (a • N) = (1 : A) :=
    cliffordProj_smul_sq N r hr hN sign hsgn
  have key : (1 + a • N) * (1 + a • N) = (2:ℝ) • (1 + a • N) := by
    have hexp : (1 + a • N) * (1 + a • N)
        = 1 + a • N + a • N + (a • N) * (a • N) := by
      noncomm_ring
      module
    rw [hexp, h1, two_smul]
    abel
  unfold cliffordProj
  rw [smul_mul_smul_comm, ← ha, key, smul_smul]
  norm_num

/-- `prop:model-W2` (orthogonality): `Π₊ Π₋ = 0`. -/
theorem cliffordProj_orth (N : A) (r : ℝ) (hr : 0 < r)
    (hN : N * N = algebraMap ℝ A r) :
    cliffordProj N r 1 * cliffordProj N r (-1) = 0 := by
  set a : ℝ := (Real.sqrt r)⁻¹ with ha
  have h1 : (a • N) * (a • N) = (1 : A) := by
    have := cliffordProj_smul_sq N r hr hN 1 (by norm_num)
    simpa using this
  have key : (1 + a • N) * (1 + (-a) • N) = 0 := by
    have hexp : (1 + a • N) * (1 + (-a) • N)
        = 1 + (-a) • N + a • N + (a • N) * ((-a) • N) := by
      noncomm_ring
      module
    have h2 : (a • N) * ((-a) • N) = -(1 : A) := by
      rw [neg_smul, mul_neg, h1]
    rw [hexp, h2, neg_smul]
    abel
  unfold cliffordProj
  rw [smul_mul_smul_comm]
  have hc : (1:ℝ) * (Real.sqrt r)⁻¹ = a := by rw [ha, one_mul]
  have hc' : (-1:ℝ) * (Real.sqrt r)⁻¹ = -a := by rw [ha]; ring
  rw [hc, hc', key, smul_zero]

/-- `prop:model-W2` (completeness): `Π₊ + Π₋ = 1`. -/
theorem cliffordProj_sum (N : A) (r : ℝ) :
    cliffordProj N r 1 + cliffordProj N r (-1) = 1 := by
  unfold cliffordProj
  rw [← smul_add]
  have h1 : (1 + (1 * (Real.sqrt r)⁻¹) • N)
      + (1 + ((-1) * (Real.sqrt r)⁻¹) • N) = (2:ℝ) • (1:A) := by
    have hc : ((-1:ℝ) * (Real.sqrt r)⁻¹) = -(1 * (Real.sqrt r)⁻¹) := by ring
    rw [hc, neg_smul, two_smul]
    abel
  rw [h1, smul_smul]
  norm_num

/-- `prop:model-W2` (branch eigenvalues): the shifted massive symbol
`M = N - λ·1` acts on each projector by its branch value,
`M Π± = (±√r - λ)·Π±`. -/
theorem cliffordProj_eigen (N : A) (r : ℝ) (hr : 0 < r)
    (hN : N * N = algebraMap ℝ A r) (lam : ℝ)
    (sign : ℝ) (hsgn : sign ^ 2 = 1) :
    (N - lam • 1) * cliffordProj N r sign
      = (sign * Real.sqrt r - lam) • cliffordProj N r sign := by
  set a : ℝ := sign * (Real.sqrt r)⁻¹ with ha
  have hs : Real.sqrt r ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hr)
  have hsq : Real.sqrt r ^ 2 = r := Real.sq_sqrt hr.le
  have hNP : N * (1 + a • N) = (sign * Real.sqrt r) • (1 + a • N) := by
    have h1 : N * (a • N) = (a * r) • (1 : A) := by
      rw [mul_smul_comm, hN, Algebra.algebraMap_eq_smul_one, smul_smul]
    have h2 : a * r = sign * Real.sqrt r := by
      rw [ha, mul_assoc]
      congr 1
      rw [inv_mul_eq_div, div_eq_iff hs]
      exact (Real.mul_self_sqrt hr.le).symm
    have h3 : (sign * Real.sqrt r) • ((a : ℝ) • N) = N := by
      rw [smul_smul]
      have hone : sign * Real.sqrt r * a = 1 := by
        rw [ha]
        have hstep : sign * Real.sqrt r * (sign * (Real.sqrt r)⁻¹)
            = (sign * sign) * (Real.sqrt r * (Real.sqrt r)⁻¹) := by ring
        rw [hstep, mul_inv_cancel₀ hs, mul_one, ← sq, hsgn]
      rw [hone, one_smul]
    calc N * (1 + a • N) = N + N * (a • N) := by noncomm_ring
      _ = N + (a * r) • (1:A) := by rw [h1]
      _ = (sign * Real.sqrt r) • (1 + a • N) := by
          rw [smul_add, h3, h2]
          abel
  unfold cliffordProj
  rw [mul_smul_comm]
  rw [smul_comm (sign * Real.sqrt r - lam) ((2:ℝ)⁻¹)]
  congr 1
  rw [sub_mul, hNP, smul_mul_assoc, one_mul, sub_smul]

/-- `prop:model-W2` (uniform gap): the two branch values are
separated by `2√r ≥ 2λ_min` whenever `r ≥ λ_min²`. -/
theorem massive_band_gap (r lam lammin : ℝ) (hmin : 0 ≤ lammin)
    (hr : lammin ^ 2 ≤ r) :
    2 * lammin ≤ (1 * Real.sqrt r - lam) - ((-1) * Real.sqrt r - lam) := by
  have h1 : lammin ≤ Real.sqrt r := by
    calc lammin = Real.sqrt (lammin ^ 2) := (Real.sqrt_sq hmin).symm
      _ ≤ Real.sqrt r := Real.sqrt_le_sqrt hr
  nlinarith [h1]

end CliffordProjectors

end NCG
