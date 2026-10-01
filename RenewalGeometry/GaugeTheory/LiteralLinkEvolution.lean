/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.DiscreteAnalysis.PeriodicGridSobolevCalculus

/-!
# Exact literal-link evolution and the identity-chart bounds
  (`lem:supp-literal-link-evolution`; emergent-spacetime manuscript, supplement)

* **Exponential bounds in a real Banach algebra** (no commutativity, any algebra norm, with
  `κ = max ‖1‖ 1`): `‖eˣ‖ ≤ κ e^{‖x‖}` (`norm_exp_le`), the Lipschitz bound
  `‖e^B - e^A‖ ≤ κ² e^{max(‖A‖,‖B‖)} ‖B - A‖` (`norm_exp_sub_exp_le`, integration along the
  segment `s ↦ e^{sB} e^{(1-s)A}`), and `‖eˣ - 1 - x‖ ≤ κ² e^{‖x‖} ‖x‖²`.
* **The link coordinate** `Z = Q_h(A) = (e^{hA} - I)/h` (`linkCoord`) and the identity-chart
  bounds `‖Z‖ ≤ C‖A‖`, `‖Z - A‖ ≤ C h‖A‖²`, `‖D⁺Z‖ ≤ C‖D⁺A‖` with `C = κ² e^δ`
  (`chart_bounds`, `norm_fwdDiff_linkCoord_le`).
* **Exact link evolution** on any lattice (`link_Z_identity`, `hasDerivAt_link_Z`): with the
  literal electric record `E U = (∂_tU + A₀U - U S A₀)/h` (`electricRecord`),
  `∂_t Z = E U + D⁺A₀ + Z S A₀ - A₀ Z` (`eq:supp-literal-Z-equation`).  The typeset definition
  `E U = ∂_tU/h - A₀U + U S A₀` (`eq:supp-literal-electric-definition`) omits the factor `1/h`
  and the sign of the two `A₀` terms; the normalization used here is the unique one under which
  `eq:supp-literal-Z-equation` and the continuum limit `eq:supp-literal-electric-limit` hold.
* **Negative-norm time control** on the periodic grid `(ℤ/N)³` for complex matrix links with the
  Frobenius norm (`negSobNorm2_linkTime_le`): the dual `H_h^{-2}` norm of
  `E U + D⁺A₀ + Z S A₀ - A₀ Z` is at most `C'(‖E‖_h + (1 + ‖Z‖_h)‖A₀‖_h)` with the
  cutoff-independent constant `C' = max(κ, 1, 2√K)` (`K` from the uniform discrete `H² ⊂ L^∞`
  of `PeriodicGridSobolev`, `norm_sq_le_sobSq_two`), via summation by parts
  (`norm_matPair_matDp_le`).
* `literal_link_evolution`: the assembled lemma.
-/

open Filter Topology NormedSpace Set

noncomputable section

namespace RenewalGeometry.LiteralLink

set_option linter.unusedSectionVars false

/-! ### Exponential bounds in a Banach algebra -/

section ExpBounds

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

variable (𝔸) in
/-- The constant `κ = max ‖1‖ 1` (equal to `1` for unital norms, `√n` for the Frobenius norm on
`n × n` matrices). -/
def kappa : ℝ := max ‖(1 : 𝔸)‖ 1

theorem one_le_kappa : 1 ≤ kappa 𝔸 := le_max_right _ _

theorem kappa_pos : 0 < kappa 𝔸 := lt_of_lt_of_le one_pos one_le_kappa

/-- `‖exp x‖ ≤ κ e^{‖x‖}` in any real Banach algebra. -/
theorem norm_exp_le (x : 𝔸) : ‖exp x‖ ≤ kappa 𝔸 * Real.exp ‖x‖ := by
  have hs := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) x
  have hr0 := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (‖x‖)
  rw [← Real.exp_eq_exp_ℝ] at hr0
  have hr : HasSum (fun n : ℕ => kappa 𝔸 * ((n.factorial : ℝ)⁻¹ * ‖x‖ ^ n))
      (kappa 𝔸 * Real.exp ‖x‖) := by
    simpa [smul_eq_mul] using hr0.mul_left (kappa 𝔸)
  rw [← hs.tsum_eq]
  refine tsum_of_norm_bounded hr fun n => ?_
  rw [norm_smul, Real.norm_of_nonneg (by positivity)]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [kappa]
  · calc (n.factorial : ℝ)⁻¹ * ‖x ^ n‖ ≤ (n.factorial : ℝ)⁻¹ * ‖x‖ ^ n := by
          gcongr; exact norm_pow_le' x hn
      _ ≤ kappa 𝔸 * ((n.factorial : ℝ)⁻¹ * ‖x‖ ^ n) := by
          have : 0 ≤ (n.factorial : ℝ)⁻¹ * ‖x‖ ^ n := by positivity
          nlinarith [one_le_kappa (𝔸 := 𝔸)]

/-- **Lipschitz bound for the exponential**: `‖e^B - e^A‖ ≤ κ² e^{max(‖A‖,‖B‖)} ‖B - A‖`
(integration along the segment, no commutativity needed). -/
theorem norm_exp_sub_exp_le (A B : 𝔸) :
    ‖exp B - exp A‖ ≤ kappa 𝔸 ^ 2 * Real.exp (max ‖A‖ ‖B‖) * ‖B - A‖ := by
  let f : ℝ → 𝔸 := fun s => exp (s • B) * exp ((1 - s) • A)
  have hderiv : ∀ s, HasDerivAt f (exp (s • B) * (B - A) * exp ((1 - s) • A)) s := by
    intro s
    have h1 := hasDerivAt_exp_smul_const (𝕂 := ℝ) B s
    have h2 : HasDerivAt (fun s : ℝ => exp ((1 - s) • A)) (-(exp ((1 - s) • A) * A)) s := by
      have h := (hasDerivAt_exp_smul_const (𝕂 := ℝ) A (1 - s)).scomp s
        ((hasDerivAt_id s).const_sub 1)
      exact h.congr_deriv (by simp)
    have := h1.mul h2
    have hc : exp ((1 - s) • A) * A = A * exp ((1 - s) • A) :=
      (((Commute.refl A).smul_left (1 - s)).exp_left).eq
    exact this.congr_deriv (by rw [hc]; noncomm_ring)
  have hbound : ∀ s ∈ Ico (0 : ℝ) 1,
      ‖exp (s • B) * (B - A) * exp ((1 - s) • A)‖ ≤
        kappa 𝔸 ^ 2 * Real.exp (max ‖A‖ ‖B‖) * ‖B - A‖ := by
    rintro s ⟨hs0, hs1⟩
    have hk := kappa_pos (𝔸 := 𝔸)
    have e1 := norm_exp_le (s • B)
    have e2 := norm_exp_le ((1 - s) • A)
    rw [norm_smul, Real.norm_of_nonneg hs0] at e1
    rw [norm_smul, Real.norm_of_nonneg (by linarith)] at e2
    have hexp : Real.exp (s * ‖B‖) * Real.exp ((1 - s) * ‖A‖) ≤ Real.exp (max ‖A‖ ‖B‖) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      have := le_max_left ‖A‖ ‖B‖
      have := le_max_right ‖A‖ ‖B‖
      nlinarith
    calc ‖exp (s • B) * (B - A) * exp ((1 - s) • A)‖
        ≤ ‖exp (s • B)‖ * ‖B - A‖ * ‖exp ((1 - s) • A)‖ := by
          refine (norm_mul_le _ _).trans ?_
          gcongr
          exact norm_mul_le _ _
      _ ≤ (kappa 𝔸 * Real.exp (s * ‖B‖)) * ‖B - A‖ * (kappa 𝔸 * Real.exp ((1 - s) * ‖A‖)) := by
          gcongr
      _ = kappa 𝔸 ^ 2 * (Real.exp (s * ‖B‖) * Real.exp ((1 - s) * ‖A‖)) * ‖B - A‖ := by ring
      _ ≤ kappa 𝔸 ^ 2 * Real.exp (max ‖A‖ ‖B‖) * ‖B - A‖ := by gcongr
  have := norm_image_sub_le_of_norm_deriv_le_segment' (f := f)
    (fun s _ => (hderiv s).hasDerivWithinAt) hbound 1 (right_mem_Icc.2 zero_le_one)
  simpa [f] using this

/-- Second-order remainder: `‖e^x - 1 - x‖ ≤ κ² e^{‖x‖} ‖x‖²`. -/
theorem norm_exp_sub_one_sub_le (x : 𝔸) :
    ‖exp x - 1 - x‖ ≤ kappa 𝔸 ^ 2 * Real.exp ‖x‖ * ‖x‖ ^ 2 := by
  let g : ℝ → 𝔸 := fun s => exp (s • x) - s • x
  have hderiv : ∀ s, HasDerivAt g ((exp (s • x) - exp ((0 : ℝ) • x)) * x) s := by
    intro s
    have h1 := hasDerivAt_exp_smul_const (𝕂 := ℝ) x s
    have h2 := (hasDerivAt_id s).smul_const x
    have := h1.sub h2
    exact this.congr_deriv (by simp [sub_mul])
  have hbound : ∀ s ∈ Ico (0 : ℝ) 1,
      ‖(exp (s • x) - exp ((0 : ℝ) • x)) * x‖ ≤ kappa 𝔸 ^ 2 * Real.exp ‖x‖ * ‖x‖ ^ 2 := by
    rintro s ⟨hs0, hs1⟩
    have h := norm_exp_sub_exp_le ((0 : ℝ) • x) (s • x)
    simp only [zero_smul, norm_zero, norm_smul, Real.norm_of_nonneg hs0, sub_zero] at h
    have hmax : max 0 (s * ‖x‖) ≤ ‖x‖ := max_le (norm_nonneg _) (by nlinarith [norm_nonneg x])
    calc ‖(exp (s • x) - exp ((0 : ℝ) • x)) * x‖
        ≤ ‖exp (s • x) - exp ((0 : ℝ) • x)‖ * ‖x‖ := norm_mul_le _ _
      _ ≤ (kappa 𝔸 ^ 2 * Real.exp (max 0 (s * ‖x‖)) * (s * ‖x‖)) * ‖x‖ := by
          gcongr; simpa using h
      _ ≤ (kappa 𝔸 ^ 2 * Real.exp ‖x‖ * ‖x‖) * ‖x‖ := by
          gcongr
          all_goals first | exact Real.exp_le_exp.2 hmax | nlinarith [norm_nonneg x]
      _ = kappa 𝔸 ^ 2 * Real.exp ‖x‖ * ‖x‖ ^ 2 := by ring
  have := norm_image_sub_le_of_norm_deriv_le_segment' (f := g)
    (fun s _ => (hderiv s).hasDerivWithinAt) hbound 1 (right_mem_Icc.2 zero_le_one)
  have e : g 1 - g 0 = exp x - 1 - x := by simp [g]; abel
  rw [e] at this
  simpa using this

end ExpBounds


/-! ### The link coordinate `Z = (e^{hA} - I)/h` on the identity chart -/

section LinkCoordinate

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- The link coordinate `Q_h(A) = (e^{hA} - I)/h` (`eq:main-link-coordinate`). -/
def linkCoord (h : ℝ) (A : 𝔸) : 𝔸 := h⁻¹ • (exp (h • A) - 1)

theorem linkCoord_zero (h : ℝ) : linkCoord h (0 : 𝔸) = 0 := by simp [linkCoord]

/-- `U = I + hZ` for `U = e^{hA}`, `Z = Q_h(A)`. -/
theorem exp_eq_one_add_smul_linkCoord {h : ℝ} (hh : h ≠ 0) (A : 𝔸) :
    exp (h • A) = 1 + h • linkCoord h A := by
  simp [linkCoord, smul_smul, mul_inv_cancel₀ hh]

/-- The differential bound for `Q_h`: `‖Q_h(B) - Q_h(A)‖ ≤ κ² e^{h max(‖A‖,‖B‖)} ‖B - A‖`. -/
theorem norm_linkCoord_sub_linkCoord_le {h : ℝ} (hh : 0 < h) (A B : 𝔸) :
    ‖linkCoord h B - linkCoord h A‖ ≤
      kappa 𝔸 ^ 2 * Real.exp (h * max ‖A‖ ‖B‖) * ‖B - A‖ := by
  have e : linkCoord h B - linkCoord h A = h⁻¹ • (exp (h • B) - exp (h • A)) := by
    simp only [linkCoord, ← smul_sub]; congr 1; abel
  rw [e, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hh.le)]
  have := norm_exp_sub_exp_le (h • A) (h • B)
  rw [norm_smul, norm_smul, Real.norm_of_nonneg hh.le, ← smul_sub, norm_smul,
    Real.norm_of_nonneg hh.le, ← mul_max_of_nonneg _ _ hh.le] at this
  calc h⁻¹ * ‖exp (h • B) - exp (h • A)‖
      ≤ h⁻¹ * (kappa 𝔸 ^ 2 * Real.exp (h * max ‖A‖ ‖B‖) * (h * ‖B - A‖)) := by gcongr
    _ = kappa 𝔸 ^ 2 * Real.exp (h * max ‖A‖ ‖B‖) * ‖B - A‖ := by field_simp

/-- `‖Q_h(A)‖ ≤ κ² e^{h‖A‖} ‖A‖`. -/
theorem norm_linkCoord_le {h : ℝ} (hh : 0 < h) (A : 𝔸) :
    ‖linkCoord h A‖ ≤ kappa 𝔸 ^ 2 * Real.exp (h * ‖A‖) * ‖A‖ := by
  have := norm_linkCoord_sub_linkCoord_le hh 0 A
  simpa [linkCoord_zero] using this

/-- `‖Q_h(A) - A‖ ≤ κ² e^{h‖A‖} h ‖A‖²`. -/
theorem norm_linkCoord_sub_self_le {h : ℝ} (hh : 0 < h) (A : 𝔸) :
    ‖linkCoord h A - A‖ ≤ kappa 𝔸 ^ 2 * Real.exp (h * ‖A‖) * (h * ‖A‖ ^ 2) := by
  have e : linkCoord h A - A = h⁻¹ • (exp (h • A) - 1 - h • A) := by
    simp only [linkCoord, smul_sub, smul_smul, inv_mul_cancel₀ hh.ne', one_smul]
  rw [e, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hh.le)]
  have := norm_exp_sub_one_sub_le (h • A)
  rw [norm_smul, Real.norm_of_nonneg hh.le] at this
  calc h⁻¹ * ‖exp (h • A) - 1 - h • A‖
      ≤ h⁻¹ * (kappa 𝔸 ^ 2 * Real.exp (h * ‖A‖) * (h * ‖A‖) ^ 2) := by gcongr
    _ = kappa 𝔸 ^ 2 * Real.exp (h * ‖A‖) * (h * ‖A‖ ^ 2) := by field_simp

/-- **Identity-chart comparison bounds** (`eq:supp-literal-Z-comparison`, pointwise part): on the
chart `h‖A‖ ≤ δ`, with the cutoff-independent constant `C = κ² e^δ`,
`‖Z‖ ≤ C‖A‖`, `‖Z - A‖ ≤ C h ‖A‖²`, and `‖U‖ ≤ κ e^δ` for `U = e^{hA}`. -/
theorem chart_bounds {h δ : ℝ} (hh : 0 < h) {A : 𝔸} (hA : h * ‖A‖ ≤ δ) :
    ‖linkCoord h A‖ ≤ kappa 𝔸 ^ 2 * Real.exp δ * ‖A‖ ∧
      ‖linkCoord h A - A‖ ≤ kappa 𝔸 ^ 2 * Real.exp δ * (h * ‖A‖ ^ 2) ∧
      ‖exp (h • A)‖ ≤ kappa 𝔸 * Real.exp δ := by
  have hk := kappa_pos (𝔸 := 𝔸)
  have he : Real.exp (h * ‖A‖) ≤ Real.exp δ := Real.exp_le_exp.2 hA
  refine ⟨(norm_linkCoord_le hh A).trans (by gcongr), (norm_linkCoord_sub_self_le hh A).trans
    (by gcongr), (norm_exp_le _).trans ?_⟩
  rw [norm_smul, Real.norm_of_nonneg hh.le]
  gcongr

end LinkCoordinate

/-! ### Exact link evolution on a lattice -/

section LinkEvolution

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
variable {G : Type*} [Add G]

/-- The forward difference `(D⁺u)(x) = (u(x + e) - u(x))/h` along the lattice step `e`. -/
def fwdDiff (h : ℝ) (e : G) (u : G → 𝔸) (x : G) : 𝔸 := h⁻¹ • (u (x + e) - u x)

/-- The literal electric link record, defined by the exact link identity
`E U = (∂_t U + A₀ U - U S A₀)/h` (`eq:supp-literal-electric-definition`, normalization under which
`eq:supp-literal-Z-equation` holds), using the inverse of the link. -/
def electricRecord (h : ℝ) (e : G) (U U' A₀ : G → 𝔸) (x : G) : 𝔸 :=
  h⁻¹ • (U' x + A₀ x * U x - U x * A₀ (x + e)) * Ring.inverse (U x)

theorem electricRecord_mul {h : ℝ} {e : G} {U U' A₀ : G → 𝔸} {x : G} (hU : IsUnit (U x)) :
    electricRecord h e U U' A₀ x * U x = h⁻¹ • (U' x + A₀ x * U x - U x * A₀ (x + e)) := by
  rw [electricRecord, mul_assoc, Ring.inverse_mul_cancel _ hU, mul_one]

/-- **Exact algebraic link evolution** (`eq:supp-literal-Z-equation`): if
`E U = (U' + A₀ U - U S A₀)/h` and `Z = (U - I)/h`, then
`U'/h = E U + D⁺A₀ + Z S A₀ - A₀ Z`. -/
theorem link_Z_identity (h : ℝ) (e : G) (U U' E A₀ : G → 𝔸) (x : G)
    (hE : E x * U x = h⁻¹ • (U' x + A₀ x * U x - U x * A₀ (x + e))) :
    h⁻¹ • U' x = E x * U x + fwdDiff h e A₀ x + (h⁻¹ • (U x - 1)) * A₀ (x + e) -
      A₀ x * (h⁻¹ • (U x - 1)) := by
  rw [hE, fwdDiff]
  simp only [smul_sub, smul_add, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul,
    mul_one]
  abel

/-- **Exact link evolution in time** (`eq:supp-literal-Z-equation`): for a differentiable link
history `t ↦ U(t)` with time derivative `U'`, the coordinate `Z = (U - I)/h` satisfies
`∂_t Z = E U + D⁺A₀ + Z S A₀ - A₀ Z` with `E` the literal electric record. -/
theorem hasDerivAt_link_Z (h : ℝ) (e : G) (U : ℝ → G → 𝔸) (U' E A₀ : G → 𝔸)
    (t : ℝ) (x : G) (hU : HasDerivAt (fun s => U s x) (U' x) t)
    (hE : E x * U t x = h⁻¹ • (U' x + A₀ x * U t x - U t x * A₀ (x + e))) :
    HasDerivAt (fun s => h⁻¹ • (U s x - 1))
      (E x * U t x + fwdDiff h e A₀ x + (h⁻¹ • (U t x - 1)) * A₀ (x + e) -
        A₀ x * (h⁻¹ • (U t x - 1))) t := by
  rw [← link_Z_identity h e (U t) U' E A₀ x hE]
  exact (hU.sub_const 1).const_smul h⁻¹

/-- **Difference comparison on the chart** (`eq:supp-literal-Z-comparison`, third bound):
if `h‖A(x)‖ ≤ δ` and `h‖A(x+e)‖ ≤ δ` then `‖D⁺Z(x)‖ ≤ κ² e^δ ‖D⁺A(x)‖` for `Z = Q_h(A)`. -/
theorem norm_fwdDiff_linkCoord_le {h δ : ℝ} (hh : 0 < h) (e : G) (A : G → 𝔸) (x : G)
    (hx : h * ‖A x‖ ≤ δ) (hxe : h * ‖A (x + e)‖ ≤ δ) :
    ‖fwdDiff h e (fun y => linkCoord h (A y)) x‖ ≤
      kappa 𝔸 ^ 2 * Real.exp δ * ‖fwdDiff h e A x‖ := by
  unfold fwdDiff
  rw [norm_smul, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hh.le)]
  have := norm_linkCoord_sub_linkCoord_le hh (A x) (A (x + e))
  have hmax : h * max ‖A x‖ ‖A (x + e)‖ ≤ δ := by
    rw [mul_max_of_nonneg _ _ hh.le]; exact max_le hx hxe
  have he : Real.exp (h * max ‖A x‖ ‖A (x + e)‖) ≤ Real.exp δ := Real.exp_le_exp.2 hmax
  have hk := kappa_pos (𝔸 := 𝔸)
  calc h⁻¹ * ‖linkCoord h (A (x + e)) - linkCoord h (A x)‖
      ≤ h⁻¹ * (kappa 𝔸 ^ 2 * Real.exp (h * max ‖A x‖ ‖A (x + e)‖) * ‖A (x + e) - A x‖) := by
        gcongr
    _ ≤ h⁻¹ * (kappa 𝔸 ^ 2 * Real.exp δ * ‖A (x + e) - A x‖) := by gcongr
    _ = kappa 𝔸 ^ 2 * Real.exp δ * (h⁻¹ * ‖A (x + e) - A x‖) := by ring

end LinkEvolution


/-! ### Negative-norm time control on the periodic grid (`eq:supp-literal-Z-time`)

Matrix-valued arrays on the periodic grid `(ℤ/N)³` (`h = 1/N`), with the Frobenius (Euclidean)
coefficient norm.  The grid Sobolev norms are those of `PeriodicGridSobolev`, applied entrywise;
`H_h^{-2}` is the dual norm of `H_h²` for the Frobenius grid pairing. -/

section NegativeNorm

open PeriodicGridSobolev
open scoped Matrix.Norms.Frobenius ComplexConjugate

variable {N : ℕ} [NeZero N] {n : ℕ}

/-- Matrix-valued arrays on the periodic grid. -/
abbrev MatArr (N n : ℕ) := PeriodicGridSobolev.Grid N → Matrix (Fin n) (Fin n) ℂ

/-- The `(a, b)` entry of a matrix array, as a scalar grid array. -/
def entry (u : MatArr N n) (a b : Fin n) : PeriodicGridSobolev.Grid N → ℂ := fun x => u x a b

/-- The squared grid `L²` norm `h³ Σ_x ‖u(x)‖²_F`, computed entrywise. -/
def matNormSq (u : MatArr N n) : ℝ := ∑ a, ∑ b, gridNormSq (entry u a b)

/-- The grid `L²` norm with Frobenius coefficient norm. -/
def matNorm (u : MatArr N n) : ℝ := Real.sqrt (matNormSq u)

/-- The squared grid Sobolev norm `‖u‖²_{r,h}`, entrywise. -/
def matSobSq (r : ℕ) (u : MatArr N n) : ℝ := ∑ a, ∑ b, sobSq r (entry u a b)

/-- The grid Sobolev norm `‖u‖_{r,h}`. -/
def matSobNorm (r : ℕ) (u : MatArr N n) : ℝ := Real.sqrt (matSobSq r u)

/-- The Frobenius grid pairing `⟨φ, u⟩_h = h³ Σ_x tr(φ(x)* u(x))`. -/
def matPair (φ u : MatArr N n) : ℂ :=
  ((N : ℂ) ^ 3)⁻¹ * ∑ x, ∑ a, ∑ b, conj (φ x a b) * u x a b

/-- The dual norm `‖u‖_{H_h^{-2}} = sup {|⟨φ, u⟩_h| : ‖φ‖_{2,h} ≤ 1}`. -/
def negSobNorm2 (u : MatArr N n) : ℝ :=
  sSup ((fun φ => ‖matPair φ u‖) '' {φ | matSobNorm 2 φ ≤ 1})

/-- The matrix forward difference `D_i⁺ = (S_i - I)/h` with `h = 1/N`. -/
def matDp (i : Fin 3) (u : MatArr N n) : MatArr N n :=
  fwdDiff ((N : ℝ)⁻¹) (unit i) u

theorem matNormSq_nonneg (u : MatArr N n) : 0 ≤ matNormSq u :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => gridNormSq_nonneg _

theorem matSobSq_nonneg (r : ℕ) (u : MatArr N n) : 0 ≤ matSobSq r u :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sobSq_nonneg _ _

theorem frob_sq (M : Matrix (Fin n) (Fin n) ℂ) : ‖M‖ ^ 2 = ∑ a, ∑ b, ‖M a b‖ ^ 2 := by
  rw [Matrix.frobenius_norm_def, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  norm_num

theorem matNormSq_eq (u : MatArr N n) :
    matNormSq u = ((N : ℝ) ^ 3)⁻¹ * ∑ x, ‖u x‖ ^ 2 := by
  simp only [matNormSq, gridNormSq, entry, frob_sq, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]

/-- **Uniform discrete `H² ⊂ L^∞`** (pointwise form of `gridNormSq_mul_le_two_zero`):
`|f(x)|² ≤ K ‖f‖²_{2,h}` with the `N`-independent constant `K = Kprod`. -/
theorem norm_sq_le_sobSq_two (f : PeriodicGridSobolev.Grid N → ℂ) (x : PeriodicGridSobolev.Grid N) :
    ‖f x‖ ^ 2 ≤ Kprod * sobSq 2 f := by
  classical
  let δ : PeriodicGridSobolev.Grid N → ℂ := fun y => if y = x then 1 else 0
  have h := gridNormSq_mul_le_two_zero f δ
  rw [sobSq_zero] at h
  have hN : (0 : ℝ) < ((N : ℝ) ^ 3)⁻¹ := by
    have : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N))
    positivity
  have e1 : gridNormSq (f * δ) = ((N : ℝ) ^ 3)⁻¹ * ‖f x‖ ^ 2 := by
    unfold gridNormSq
    congr 1
    rw [Finset.sum_eq_single x]
    · simp [δ]
    · intro y _ hy; simp [δ, hy]
    · simp
  have e2 : gridNormSq δ = ((N : ℝ) ^ 3)⁻¹ := by
    unfold gridNormSq
    rw [Finset.sum_eq_single x]
    · simp [δ]
    · intro y _ hy; simp [δ, hy]
    · simp
  rw [e1, e2] at h
  nlinarith [Kprod_nonneg, sobSq_nonneg 2 f]

/-- Matrix form of the uniform embedding: `‖φ(x)‖²_F ≤ K ‖φ‖²_{2,h}`. -/
theorem norm_sq_le_matSobSq_two (φ : MatArr N n) (x : PeriodicGridSobolev.Grid N) :
    ‖φ x‖ ^ 2 ≤ Kprod * matSobSq 2 φ := by
  rw [frob_sq, matSobSq, Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun b _ => norm_sq_le_sobSq_two (entry φ a b) x

theorem gridNormSq_Dp_le_sobSq_two (i : Fin 3) (f : PeriodicGridSobolev.Grid N → ℂ) :
    gridNormSq (Dp i f) ≤ sobSq 2 f := by
  have : Dp i f = Dα (0 + Pi.single i 1) f := by
    rw [← Dp_Dα, Dα_zero, Module.End.one_apply]
  rw [this]
  apply gridNormSq_Dα_le_sobSq
  rw [deg_add_single]; simp [deg]

theorem matNormSq_le_matSobSq_two (φ : MatArr N n) : matNormSq φ ≤ matSobSq 2 φ := by
  refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
  rw [← sobSq_zero]; exact sobSq_mono (by norm_num) _

/-- Pointwise Cauchy–Schwarz for the Frobenius pairing. -/
theorem norm_sum_conj_mul_le (P M : Matrix (Fin n) (Fin n) ℂ) :
    ‖∑ a, ∑ b, conj (P a b) * M a b‖ ≤ ‖P‖ * ‖M‖ := by
  have h1 : ‖∑ a, ∑ b, conj (P a b) * M a b‖ ≤ ∑ a, ∑ b, ‖P a b‖ * ‖M a b‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => (norm_sum_le _ _).trans ?_)
    refine Finset.sum_le_sum fun b _ => ?_
    rw [norm_mul, Complex.norm_conj]
  refine h1.trans ?_
  have hP : ‖P‖ = Real.sqrt (∑ a, ∑ b, ‖P a b‖ ^ 2) := by
    rw [← frob_sq, Real.sqrt_sq (norm_nonneg _)]
  have hM : ‖M‖ = Real.sqrt (∑ a, ∑ b, ‖M a b‖ ^ 2) := by
    rw [← frob_sq, Real.sqrt_sq (norm_nonneg _)]
  rw [hP, hM]
  simp only [← Fintype.sum_prod_type']
  exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _

/-- Discrete Cauchy–Schwarz over the grid with the `h³` weight. -/
theorem grid_cs (f g : PeriodicGridSobolev.Grid N → ℝ) :
    ((N : ℝ) ^ 3)⁻¹ * ∑ x, f x * g x ≤
      Real.sqrt (((N : ℝ) ^ 3)⁻¹ * ∑ x, f x ^ 2) * Real.sqrt (((N : ℝ) ^ 3)⁻¹ * ∑ x, g x ^ 2) := by
  have hN : (0 : ℝ) ≤ ((N : ℝ) ^ 3)⁻¹ := by positivity
  rw [Real.sqrt_mul hN, Real.sqrt_mul hN]
  calc ((N : ℝ) ^ 3)⁻¹ * ∑ x, f x * g x
      ≤ ((N : ℝ) ^ 3)⁻¹ * (Real.sqrt (∑ x, f x ^ 2) * Real.sqrt (∑ x, g x ^ 2)) := by
        gcongr; exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = Real.sqrt ((N : ℝ) ^ 3)⁻¹ * Real.sqrt (∑ x, f x ^ 2) *
          (Real.sqrt ((N : ℝ) ^ 3)⁻¹ * Real.sqrt (∑ x, g x ^ 2)) := by
        rw [show ((N : ℝ) ^ 3)⁻¹ = Real.sqrt ((N : ℝ) ^ 3)⁻¹ * Real.sqrt ((N : ℝ) ^ 3)⁻¹ from
          (Real.mul_self_sqrt hN).symm]
        rw [Real.sqrt_mul_self (Real.sqrt_nonneg _)]
        ring

theorem matNorm_eq (u : MatArr N n) :
    matNorm u = Real.sqrt (((N : ℝ) ^ 3)⁻¹ * ∑ x, ‖u x‖ ^ 2) := by
  rw [matNorm, matNormSq_eq]

/-- `|⟨φ, u⟩_h| ≤ h³ Σ_x ‖φ(x)‖ ‖u(x)‖`. -/
theorem norm_matPair_le (φ u : MatArr N n) :
    ‖matPair φ u‖ ≤ ((N : ℝ) ^ 3)⁻¹ * ∑ x, ‖φ x‖ * ‖u x‖ := by
  unfold matPair
  rw [norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
  gcongr
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => norm_sum_conj_mul_le _ _)

theorem matPair_add (φ u v : MatArr N n) :
    matPair φ (u + v) = matPair φ u + matPair φ v := by
  simp only [matPair, Pi.add_apply, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

theorem matPair_sub (φ u v : MatArr N n) :
    matPair φ (u - v) = matPair φ u - matPair φ v := by
  simp only [matPair, Pi.sub_apply, Matrix.sub_apply, mul_sub, Finset.sum_sub_distrib]

/-- Bound for a pointwise product with a bounded factor: `|⟨φ, E U⟩| ≤ κ ‖φ‖ ‖E‖`. -/
theorem norm_matPair_mul_bounded_le (φ E U : MatArr N n) {κ : ℝ} (hU : ∀ x, ‖U x‖ ≤ κ) :
    ‖matPair φ (fun x => E x * U x)‖ ≤ κ * matNorm E * matNorm φ := by
  have hκ : 0 ≤ κ := by
    rcases isEmpty_or_nonempty (PeriodicGridSobolev.Grid N) with h | ⟨⟨x⟩⟩
    · exact absurd (inferInstance : Nonempty (PeriodicGridSobolev.Grid N)) (not_nonempty_iff.2 h)
    · exact (norm_nonneg _).trans (hU x)
  refine (norm_matPair_le _ _).trans ?_
  calc ((N : ℝ) ^ 3)⁻¹ * ∑ x, ‖φ x‖ * ‖E x * U x‖
      ≤ ((N : ℝ) ^ 3)⁻¹ * ∑ x, ‖φ x‖ * (κ * ‖E x‖) := by
        gcongr with x
        have h1 := Matrix.frobenius_norm_mul (E x) (U x)
        have h2 := hU x
        nlinarith [norm_nonneg (E x), norm_nonneg (U x)]
    _ = κ * (((N : ℝ) ^ 3)⁻¹ * ∑ x, ‖E x‖ * ‖φ x‖) := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => by ring
    _ ≤ κ * (matNorm E * matNorm φ) := by
        rw [matNorm_eq, matNorm_eq]
        exact mul_le_mul_of_nonneg_left (grid_cs (fun x => ‖E x‖) (fun x => ‖φ x‖)) hκ
    _ = κ * matNorm E * matNorm φ := by ring

/-- Bound for a product with the `L^∞`-controlled test: `|⟨φ, F G⟩| ≤ √K ‖φ‖_{2,h} ‖F‖ ‖G‖`. -/
theorem norm_matPair_mul_le (φ F G : MatArr N n) :
    ‖matPair φ (fun x => F x * G x)‖ ≤
      Real.sqrt Kprod * matSobNorm 2 φ * (matNorm F * matNorm G) := by
  have hsup : ∀ x, ‖φ x‖ ≤ Real.sqrt Kprod * matSobNorm 2 φ := by
    intro x
    rw [matSobNorm, ← Real.sqrt_mul Kprod_nonneg]
    exact Real.le_sqrt_of_sq_le (norm_sq_le_matSobSq_two φ x)
  refine (norm_matPair_le _ _).trans ?_
  calc ((N : ℝ) ^ 3)⁻¹ * ∑ x, ‖φ x‖ * ‖F x * G x‖
      ≤ ((N : ℝ) ^ 3)⁻¹ * ∑ x, (Real.sqrt Kprod * matSobNorm 2 φ) * (‖F x‖ * ‖G x‖) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => ?_) (by positivity)
        exact mul_le_mul (hsup x) (Matrix.frobenius_norm_mul (F x) (G x))
          (norm_nonneg (F x * G x)) (by unfold matSobNorm; positivity)
    _ = Real.sqrt Kprod * matSobNorm 2 φ * (((N : ℝ) ^ 3)⁻¹ * ∑ x, ‖F x‖ * ‖G x‖) := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => by ring
    _ ≤ Real.sqrt Kprod * matSobNorm 2 φ * (matNorm F * matNorm G) := by
        have : 0 ≤ Real.sqrt Kprod * matSobNorm 2 φ := by
          unfold matSobNorm; positivity
        rw [matNorm_eq, matNorm_eq]
        exact mul_le_mul_of_nonneg_left (grid_cs (fun x => ‖F x‖) (fun x => ‖G x‖)) this

theorem matNorm_shift (u : MatArr N n) (e : PeriodicGridSobolev.Grid N) :
    matNorm (fun x => u (x + e)) = matNorm u := by
  rw [matNorm_eq, matNorm_eq]
  congr 2
  exact Fintype.sum_equiv (Equiv.addRight e) _ _ (fun _ => rfl)

end NegativeNorm


section NegativeNormBound

open PeriodicGridSobolev
open scoped Matrix.Norms.Frobenius ComplexConjugate

variable {N : ℕ} [NeZero N] {n : ℕ}

theorem entry_matDp (i : Fin 3) (u : MatArr N n) (a b : Fin n) :
    entry (matDp i u) a b = Dp i (entry u a b) := by
  funext x
  rw [Dp_apply]
  simp [entry, matDp, fwdDiff, Matrix.smul_apply, Complex.real_smul]

theorem matPair_eq_sum_gridInner (φ u : MatArr N n) :
    matPair φ u = ∑ a, ∑ b, gridInner (entry φ a b) (entry u a b) := by
  simp only [matPair, gridInner, entry, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]

theorem norm_gridInner_le (f g : PeriodicGridSobolev.Grid N → ℂ) :
    ‖gridInner f g‖ ≤ gridNorm f * gridNorm g := by
  unfold gridInner gridNorm gridNormSq
  rw [norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
  calc ((N : ℝ) ^ 3)⁻¹ * ‖∑ x, conj (f x) * g x‖
      ≤ ((N : ℝ) ^ 3)⁻¹ * ∑ x, ‖f x‖ * ‖g x‖ := by
        gcongr
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
        rw [norm_mul, Complex.norm_conj]
    _ ≤ _ := grid_cs (fun x => ‖f x‖) (fun x => ‖g x‖)

/-- **Summation by parts for the temporal gradient term**:
`|⟨φ, D_i⁺A₀⟩_h| ≤ ‖φ‖_{2,h} ‖A₀‖_h`. -/
theorem norm_matPair_matDp_le (i : Fin 3) (φ A₀ : MatArr N n) :
    ‖matPair φ (matDp i A₀)‖ ≤ matSobNorm 2 φ * matNorm A₀ := by
  rw [matPair_eq_sum_gridInner]
  simp only [entry_matDp]
  have hsbp : ∀ a b, gridInner (entry φ a b) (Dp i (entry A₀ a b)) =
      -gridInner (Dm i (entry φ a b)) (entry A₀ a b) := fun a b => by
    rw [gridInner_Dm_left, neg_neg]
  simp only [hsbp]
  calc ‖∑ a, ∑ b, -gridInner (Dm i (entry φ a b)) (entry A₀ a b)‖
      ≤ ∑ a, ∑ b, gridNorm (Dp i (entry φ a b)) * gridNorm (entry A₀ a b) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ =>
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_))
        rw [norm_neg, ← gridNorm_Dm_eq]
        exact norm_gridInner_le _ _
    _ ≤ Real.sqrt (∑ a, ∑ b, gridNorm (Dp i (entry φ a b)) ^ 2) *
          Real.sqrt (∑ a, ∑ b, gridNorm (entry A₀ a b) ^ 2) := by
        simp only [← Fintype.sum_prod_type']
        exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ ≤ matSobNorm 2 φ * matNorm A₀ := by
        unfold matSobNorm matNorm matNormSq matSobSq
        simp only [gridNorm_sq]
        gcongr with a _ b _
        exact gridNormSq_Dp_le_sobSq_two i _

theorem matNorm_le_matSobNorm_two (φ : MatArr N n) : matNorm φ ≤ matSobNorm 2 φ :=
  Real.sqrt_le_sqrt (matNormSq_le_matSobSq_two φ)

theorem matNorm_nonneg (u : MatArr N n) : 0 ≤ matNorm u := Real.sqrt_nonneg _

/-- **Tested negative-norm bound for the link evolution** (`eq:supp-literal-Z-time`, tested
form): for every matrix test `φ`,
`|⟨φ, E U + D_i⁺A₀ + Z S_iA₀ - A₀ Z⟩_h| ≤ (κ‖E‖ + ‖A₀‖ + 2√K ‖Z‖‖A₀‖) ‖φ‖_{2,h}`,
where `κ` bounds `‖U(x)‖_F` and `K = Kprod` is the `N`-independent embedding constant. -/
theorem norm_matPair_linkTime_le (i : Fin 3) (E U Z A₀ φ : MatArr N n) {κ : ℝ}
    (hU : ∀ x, ‖U x‖ ≤ κ) :
    ‖matPair φ (fun x => E x * U x + matDp i A₀ x + Z x * A₀ (x + unit i) - A₀ x * Z x)‖ ≤
      (κ * matNorm E + matNorm A₀ + 2 * Real.sqrt Kprod * matNorm Z * matNorm A₀) *
        matSobNorm 2 φ := by
  have hκ : 0 ≤ κ := (norm_nonneg _).trans (hU 0)
  have e : (fun x => E x * U x + matDp i A₀ x + Z x * A₀ (x + unit i) - A₀ x * Z x) =
      (fun x => E x * U x) + matDp i A₀ + (fun x => Z x * A₀ (x + unit i)) -
        (fun x => A₀ x * Z x) := rfl
  rw [e, matPair_sub, matPair_add, matPair_add]
  have t1 := norm_matPair_mul_bounded_le φ E U hU
  have t2 := norm_matPair_matDp_le i φ A₀
  have t3 := norm_matPair_mul_le φ Z (fun x => A₀ (x + unit i))
  have t4 := norm_matPair_mul_le φ A₀ Z
  rw [matNorm_shift] at t3
  have hφ := matNorm_le_matSobNorm_two φ
  have hE := matNorm_nonneg E
  have hS : 0 ≤ matSobNorm 2 φ := Real.sqrt_nonneg _
  have hK := Real.sqrt_nonneg Kprod
  have hZ := matNorm_nonneg Z
  have hA := matNorm_nonneg A₀
  calc ‖matPair φ (fun x => E x * U x) + matPair φ (matDp i A₀) +
        matPair φ (fun x => Z x * A₀ (x + unit i)) - matPair φ (fun x => A₀ x * Z x)‖
      ≤ ‖matPair φ (fun x => E x * U x)‖ + ‖matPair φ (matDp i A₀)‖ +
          ‖matPair φ (fun x => Z x * A₀ (x + unit i))‖ + ‖matPair φ (fun x => A₀ x * Z x)‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        exact (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
    _ ≤ κ * matNorm E * matSobNorm 2 φ + matSobNorm 2 φ * matNorm A₀ +
          Real.sqrt Kprod * matSobNorm 2 φ * (matNorm Z * matNorm A₀) +
          Real.sqrt Kprod * matSobNorm 2 φ * (matNorm A₀ * matNorm Z) := by
        gcongr
        exact t1.trans (by gcongr)
    _ = (κ * matNorm E + matNorm A₀ + 2 * Real.sqrt Kprod * matNorm Z * matNorm A₀) *
          matSobNorm 2 φ := by ring

/-- The dual norm is bounded by any constant in a tested bound. -/
theorem negSobNorm2_le_of_forall {u : MatArr N n} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ φ, ‖matPair φ u‖ ≤ C * matSobNorm 2 φ) : negSobNorm2 u ≤ C := by
  apply csSup_le
  · refine ⟨_, 0, ?_, rfl⟩
    show matSobNorm 2 0 ≤ 1
    have he : ∀ a b, entry (0 : MatArr N n) a b = 0 := fun a b => rfl
    have : matSobSq 2 (0 : MatArr N n) = 0 := by
      simp [matSobSq, he, sobSq, gridNormSq]
    rw [matSobNorm, this, Real.sqrt_zero]; norm_num
  · rintro _ ⟨φ, hφ, rfl⟩
    exact (h φ).trans (by simpa using mul_le_mul_of_nonneg_left hφ hC)

/-- The `N`-independent constant of `eq:supp-literal-Z-time`. -/
def timeConst (κ : ℝ) : ℝ := max κ (max 1 (2 * Real.sqrt Kprod))

/-- **Negative-norm time control** (`eq:supp-literal-Z-time`): if `‖U(x)‖_F ≤ κ` then
`‖E U + D_i⁺A₀ + Z S_iA₀ - A₀ Z‖_{H_h^{-2}} ≤ C (‖E‖_h + (1 + ‖Z‖_h)‖A₀‖_h)` with
`C = max(κ, 1, 2√K)` independent of the cutoff `N`. -/
theorem negSobNorm2_linkTime_le (i : Fin 3) (E U Z A₀ : MatArr N n) {κ : ℝ}
    (hU : ∀ x, ‖U x‖ ≤ κ) :
    negSobNorm2 (fun x => E x * U x + matDp i A₀ x + Z x * A₀ (x + unit i) - A₀ x * Z x) ≤
      timeConst κ * (matNorm E + (1 + matNorm Z) * matNorm A₀) := by
  have hκ : 0 ≤ κ := (norm_nonneg _).trans (hU 0)
  have hE := matNorm_nonneg E
  have hZ := matNorm_nonneg Z
  have hA := matNorm_nonneg A₀
  have hK := Real.sqrt_nonneg Kprod
  have h1 : κ ≤ timeConst κ := le_max_left _ _
  have h2 : 1 ≤ timeConst κ := (le_max_left _ _).trans (le_max_right _ _)
  have h3 : 2 * Real.sqrt Kprod ≤ timeConst κ := (le_max_right _ _).trans (le_max_right _ _)
  have hcoef : κ * matNorm E + matNorm A₀ + 2 * Real.sqrt Kprod * matNorm Z * matNorm A₀ ≤
      timeConst κ * (matNorm E + (1 + matNorm Z) * matNorm A₀) := by
    have := mul_le_mul_of_nonneg_right h1 hE
    have := mul_le_mul_of_nonneg_right h2 hA
    have := mul_le_mul_of_nonneg_right h3 (mul_nonneg hZ hA)
    nlinarith
  refine negSobNorm2_le_of_forall (by positivity) fun φ => ?_
  exact (norm_matPair_linkTime_le i E U Z A₀ φ hU).trans
    (mul_le_mul_of_nonneg_right hcoef (Real.sqrt_nonneg _))

end NegativeNormBound

/-! ### The assembled lemma (`lem:supp-literal-link-evolution`) -/

section Assembled

open PeriodicGridSobolev
open scoped Matrix.Norms.Frobenius

variable {N : ℕ} [NeZero N] {n : ℕ}

/-- **Exact link evolution and negative-norm time control** (`lem:supp-literal-link-evolution`),
on the odd/any periodic grid `(ℤ/N)³`, `h = 1/N`, for `n × n` complex matrix links with the
Frobenius coefficient norm.  Let `U(s)` be a link history in direction `i`, differentiable at
time `t` with derivative `U'`, with `U(t) = exp(hA)` on the identity chart `h‖A(x)‖ ≤ δ`; let
`Z = (U - I)/h` and let `E` be the literal electric record (`E U = (∂_tU + A₀U - U S_iA₀)/h`).
Then, with the cutoff-independent constants `C = κ² e^δ` (`κ = max ‖I‖ 1`) and
`C' = max(κ e^δ, 1, 2√K)`:
1. `∂_t Z = E U + D_i⁺A₀ + Z S_iA₀ - A₀ Z` (`eq:supp-literal-Z-equation`);
2. `‖Z‖ ≤ C‖A‖`, `‖Z - A‖ ≤ C h ‖A‖²` pointwise, and `‖D_j⁺Z‖ ≤ C ‖D_j⁺A‖` pointwise for every
   `j` (`eq:supp-literal-Z-comparison`);
3. `‖∂_t Z‖_{H_h^{-2}} ≤ C' (‖E‖_h + (1 + ‖Z‖_h)‖A₀‖_h)` (`eq:supp-literal-Z-time`). -/
theorem literal_link_evolution (i : Fin 3) {δ : ℝ} (U : ℝ → MatArr N n) (U' A₀ A : MatArr N n)
    (t : ℝ) (hUA : ∀ x, U t x = exp ((N : ℝ)⁻¹ • A x))
    (hchart : ∀ x, (N : ℝ)⁻¹ * ‖A x‖ ≤ δ)
    (hU : ∀ x, HasDerivAt (fun s => U s x) (U' x) t) :
    (∀ x, HasDerivAt (fun s => ((N : ℝ)⁻¹)⁻¹ • (U s x - 1))
      (electricRecord (N : ℝ)⁻¹ (unit i) (U t) U' A₀ x * U t x + matDp i A₀ x +
        (((N : ℝ)⁻¹)⁻¹ • (U t x - 1)) * A₀ (x + unit i) -
          A₀ x * (((N : ℝ)⁻¹)⁻¹ • (U t x - 1))) t) ∧
    (∀ x, ‖((N : ℝ)⁻¹)⁻¹ • (U t x - 1)‖ ≤
        kappa (Matrix (Fin n) (Fin n) ℂ) ^ 2 * Real.exp δ * ‖A x‖ ∧
      ‖((N : ℝ)⁻¹)⁻¹ • (U t x - 1) - A x‖ ≤
        kappa (Matrix (Fin n) (Fin n) ℂ) ^ 2 * Real.exp δ * ((N : ℝ)⁻¹ * ‖A x‖ ^ 2)) ∧
    (∀ (j : Fin 3) x, ‖matDp j (fun y => ((N : ℝ)⁻¹)⁻¹ • (U t y - 1)) x‖ ≤
        kappa (Matrix (Fin n) (Fin n) ℂ) ^ 2 * Real.exp δ * ‖matDp j A x‖) ∧
    negSobNorm2 (fun x => electricRecord (N : ℝ)⁻¹ (unit i) (U t) U' A₀ x * U t x +
        matDp i A₀ x + (((N : ℝ)⁻¹)⁻¹ • (U t x - 1)) * A₀ (x + unit i) -
          A₀ x * (((N : ℝ)⁻¹)⁻¹ • (U t x - 1))) ≤
      timeConst (kappa (Matrix (Fin n) (Fin n) ℂ) * Real.exp δ) *
        (matNorm (electricRecord (N : ℝ)⁻¹ (unit i) (U t) U' A₀) +
          (1 + matNorm (fun x => ((N : ℝ)⁻¹)⁻¹ • (U t x - 1))) * matNorm A₀) := by
  have hN : (0 : ℝ) < (N : ℝ)⁻¹ :=
    inv_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N)))
  have hunit : ∀ x, IsUnit (U t x) := fun x => by rw [hUA x]; exact isUnit_exp _
  have hZ : ∀ x, ((N : ℝ)⁻¹)⁻¹ • (U t x - 1) = linkCoord (N : ℝ)⁻¹ (A x) := fun x => by
    rw [hUA x, linkCoord]
    rfl
  refine ⟨fun x => ?_, fun x => ?_, fun j x => ?_, ?_⟩
  · exact hasDerivAt_link_Z _ (unit i) U U' _ A₀ t x (hU x) (electricRecord_mul (hunit x))
  · rw [hZ x]
    exact ⟨(chart_bounds hN (hchart x)).1, (chart_bounds hN (hchart x)).2.1⟩
  · have e : (fun y => ((N : ℝ)⁻¹)⁻¹ • (U t y - 1)) = fun y => linkCoord (N : ℝ)⁻¹ (A y) :=
      funext hZ
    rw [e]
    exact norm_fwdDiff_linkCoord_le hN (unit j) A x (hchart x) (hchart (x + unit j))
  · refine negSobNorm2_linkTime_le i _ (U t) _ A₀ fun x => ?_
    rw [hUA x]
    exact (chart_bounds hN (hchart x)).2.2

/-- Non-vacuity of `literal_link_evolution`: the trivial link history `U ≡ I` with `A = 0`,
`A₀ = 0` satisfies all hypotheses (with `δ = 0`). -/
example (i : Fin 3) : True := by
  have := literal_link_evolution (N := 3) (n := 2) i (δ := 0) (fun _ _ => 1) 0 0 0 0
    (fun x => by simp) (fun x => by simp) (fun x => hasDerivAt_const _ _)
  trivial

end Assembled

end RenewalGeometry.LiteralLink
