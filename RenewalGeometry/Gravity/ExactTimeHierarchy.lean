/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Derivative hierarchy in scalar--trace coordinates
(`thm:supp-exact-time-hierarchy`, `eq:supp-exact-time-sources`,
`eq:supp-exact-first-time-source`; emergent-spacetime manuscript)

The scalar--trace data of the exact-action response are a time-dependent
compression `C(t)`, the operator `H(t) = 2I − 3C(t)` (`traceOperator`), the
source `ζ(t)` and the response `χ(t) = H(t)⁻¹ ζ(t)` (`traceResponse`).  Everything
lives in a complete normed algebra `𝔸` over `ℝ` (e.g. square real matrices with an
operator norm); `ζ`, `χ` are elements of the same algebra, and the vector-valued
statement of the paper is the column-wise special case (the recursion is linear
in `ζ`, `χ` and acts by left multiplication).

* `hierarchy`: the recursively defined sources `χ_0 = χ`,
  `χ_j = H⁻¹[ζ^{(j)} + 3 Σ_{ℓ=1}^{j} binom(j,ℓ) C^{(ℓ)} χ_{j−ℓ}]`
  (**`eq:supp-exact-time-sources`**; the sum is indexed by `ℓ = l + 1`, `l < j`).
* `traceOperator_mul_iteratedDeriv_traceResponse`: for `C`, `ζ` of class `C^r`
  and `H(t)` invertible, `H χ^{(j)} = ζ^{(j)} + 3 Σ_{ℓ=1}^{j} binom(j,ℓ) C^{(ℓ)} χ^{(j−ℓ)}`
  for `j ≤ r` (Leibniz rule with `H^{(ℓ)} = −3 C^{(ℓ)}`).
* `hierarchy_eq_iteratedDeriv` (**`thm:supp-exact-time-hierarchy`**): `χ_j = χ^{(j)}`
  for `j ≤ r`, and `hierarchy_eq_neg_mul_iteratedDeriv`: if `E^* v = −χ` at every
  time then `χ_j = −E^* v^{(j)}`.
* `deriv_traceResponse_eq` and `hasDerivAt_response`
  (**`eq:supp-exact-first-time-source`**): `χ' = H⁻¹(ζ' + 3C'χ)` and, for
  `v = w − 3(I − Π)Eχ`, `v' = w' + 3Π'Eχ − 3(I − Π)Eχ'`.

Scoped conventions: `H⁻¹` is `Ring.inverse` (equal to the matrix inverse when `H`
is invertible); `C^r` regularity of the derived objects is *derived* from that of
`C`, `ζ` and invertibility of `H` (`contDiffAt_traceResponse`), not assumed.
-/

open scoped BigOperators

namespace RenewalGeometry.ExactTimeHierarchy

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- The trace operator `H(t) = 2I − 3C(t)`. -/
def traceOperator (C : ℝ → 𝔸) (t : ℝ) : 𝔸 := (2 : 𝔸) - 3 * C t

/-- The trace response `χ(t) = H(t)⁻¹ ζ(t)`. -/
noncomputable def traceResponse (C ζ : ℝ → 𝔸) (t : ℝ) : 𝔸 :=
  Ring.inverse (traceOperator C t) * ζ t

/-- The derivative hierarchy `χ_j` of `eq:supp-exact-time-sources`:
`χ_0 = χ`, `χ_{j+1} = H⁻¹[ζ^{(j+1)} + 3 Σ_{l<j+1} binom(j+1,l+1) C^{(l+1)} χ_{j−l}]`. -/
noncomputable def hierarchy (C ζ : ℝ → 𝔸) (t : ℝ) : ℕ → 𝔸
  | 0 => traceResponse C ζ t
  | j + 1 => Ring.inverse (traceOperator C t) *
      (iteratedDeriv (j + 1) ζ t + 3 * ∑ l ∈ Finset.range (j + 1),
        (((j + 1).choose (l + 1) : ℕ) : 𝔸) *
          (iteratedDeriv (l + 1) C t * hierarchy C ζ t (j - l)))
termination_by j => j
decreasing_by omega

theorem hierarchy_zero (C ζ : ℝ → 𝔸) (t : ℝ) : hierarchy C ζ t 0 = traceResponse C ζ t := by
  rw [hierarchy]

theorem hierarchy_succ (C ζ : ℝ → 𝔸) (t : ℝ) (j : ℕ) :
    hierarchy C ζ t (j + 1) = Ring.inverse (traceOperator C t) *
      (iteratedDeriv (j + 1) ζ t + 3 * ∑ l ∈ Finset.range (j + 1),
        (((j + 1).choose (l + 1) : ℕ) : 𝔸) *
          (iteratedDeriv (l + 1) C t * hierarchy C ζ t (j - l))) := by
  rw [hierarchy]

/-- `H χ = ζ` when `H` is invertible. -/
theorem traceOperator_mul_traceResponse (C ζ : ℝ → 𝔸) (t : ℝ)
    (hH : IsUnit (traceOperator C t)) :
    traceOperator C t * traceResponse C ζ t = ζ t := by
  unfold traceResponse
  rw [← mul_assoc, Ring.mul_inverse_cancel _ hH, one_mul]

/-- `ζ = H χ` as functions when `H(t)` is invertible for every `t`. -/
theorem source_eq_traceOperator_mul (C ζ : ℝ → 𝔸) (hH : ∀ t, IsUnit (traceOperator C t)) :
    ζ = traceOperator C * traceResponse C ζ := by
  funext t
  exact (traceOperator_mul_traceResponse C ζ t (hH t)).symm

theorem contDiffAt_traceOperator {r : ℕ} (C : ℝ → 𝔸) (t : ℝ) (hC : ContDiffAt ℝ r C t) :
    ContDiffAt ℝ r (traceOperator C) t :=
  contDiffAt_const.sub (contDiffAt_const.mul hC)

/-- `C^r` regularity of the response `χ = H⁻¹ ζ` follows from that of `C`, `ζ` and
invertibility of `H(t)`. -/
theorem contDiffAt_traceResponse {r : ℕ} (C ζ : ℝ → 𝔸) (t : ℝ) (hC : ContDiffAt ℝ r C t)
    (hζ : ContDiffAt ℝ r ζ t) (hH : IsUnit (traceOperator C t)) :
    ContDiffAt ℝ r (traceResponse C ζ) t := by
  have h1 : ContDiffAt ℝ r Ring.inverse (traceOperator C t) := by
    have := contDiffAt_ringInverse (𝕜 := ℝ) (n := r) hH.unit
    rwa [hH.unit_spec] at this
  exact (h1.comp t (contDiffAt_traceOperator C t hC)).mul hζ

/-- `H^{(l+1)} = −3 C^{(l+1)}`. -/
theorem iteratedDeriv_succ_traceOperator {r : ℕ} (C : ℝ → 𝔸) (t : ℝ) (hC : ContDiffAt ℝ r C t)
    (l : ℕ) (hl : l + 1 ≤ r) :
    iteratedDeriv (l + 1) (traceOperator C) t = -(3 * iteratedDeriv (l + 1) C t) := by
  have hC' : ContDiffAt ℝ (l + 1) C t := hC.of_le (by exact_mod_cast hl)
  have hfun : traceOperator C = (fun _ => (2 : 𝔸)) - (fun t => 3 * C t) := rfl
  rw [hfun, iteratedDeriv_sub contDiffAt_const (contDiffAt_const.mul hC'),
    iteratedDeriv_const, iteratedDeriv_const_mul _ hC']
  simp

/-- Auxiliary noncommutative rearrangement. -/
theorem cast_mul_neg_three_mul (n : ℕ) (a b : 𝔸) :
    (n : 𝔸) * (-(3 * a)) * b = -(3 * ((n : 𝔸) * (a * b))) := by
  rw [mul_assoc, neg_mul, mul_neg, mul_assoc, (Nat.cast_commute n (3 : 𝔸)).left_comm]

/-- The derivative recursion: for `C`, `ζ` of class `C^r` with `H` invertible,
`H χ^{(j)} = ζ^{(j)} + 3 Σ_{l<j} binom(j,l+1) C^{(l+1)} χ^{(j−(l+1))}` for `j ≤ r`. -/
theorem traceOperator_mul_iteratedDeriv_traceResponse {r : ℕ} (C ζ : ℝ → 𝔸)
    (hC : ContDiff ℝ r C) (hζ : ContDiff ℝ r ζ) (hH : ∀ t, IsUnit (traceOperator C t))
    (t : ℝ) (j : ℕ) (hj : j ≤ r) :
    traceOperator C t * iteratedDeriv j (traceResponse C ζ) t
      = iteratedDeriv j ζ t + 3 * ∑ l ∈ Finset.range j,
          ((j.choose (l + 1) : ℕ) : 𝔸) *
            (iteratedDeriv (l + 1) C t * iteratedDeriv (j - (l + 1)) (traceResponse C ζ) t) := by
  have hjr : (j : WithTop ℕ∞) ≤ r := by exact_mod_cast hj
  have hCj : ContDiffAt ℝ j (traceOperator C) t :=
    contDiffAt_traceOperator C t (hC.contDiffAt.of_le hjr)
  have hχj : ContDiffAt ℝ j (traceResponse C ζ) t :=
    contDiffAt_traceResponse C ζ t (hC.contDiffAt.of_le hjr) (hζ.contDiffAt.of_le hjr) (hH t)
  have hleib := iteratedDeriv_mul hCj hχj
  rw [← source_eq_traceOperator_mul C ζ hH] at hleib
  rw [Finset.sum_range_succ', Nat.choose_zero_right, Nat.sub_zero, iteratedDeriv_zero] at hleib
  have hterm : ∀ l ∈ Finset.range j,
      ((j.choose (l + 1) : ℕ) : 𝔸) * iteratedDeriv (l + 1) (traceOperator C) t
          * iteratedDeriv (j - (l + 1)) (traceResponse C ζ) t
        = -(3 * (((j.choose (l + 1) : ℕ) : 𝔸) *
            (iteratedDeriv (l + 1) C t * iteratedDeriv (j - (l + 1)) (traceResponse C ζ) t))) := by
    intro l hl
    have hl' : l + 1 ≤ r := by
      have := Finset.mem_range.mp hl
      omega
    rw [iteratedDeriv_succ_traceOperator C t hC.contDiffAt l hl', cast_mul_neg_three_mul]
  rw [Finset.sum_congr rfl hterm, Finset.sum_neg_distrib, ← Finset.mul_sum] at hleib
  simp only [Nat.cast_one, one_mul] at hleib
  rw [hleib]
  abel

/-- **`thm:supp-exact-time-hierarchy`**: the recursively defined sources coincide with
the derivatives of the response, `χ_j = χ^{(j)}`, for `j ≤ r`. -/
theorem hierarchy_eq_iteratedDeriv {r : ℕ} (C ζ : ℝ → 𝔸) (hC : ContDiff ℝ r C)
    (hζ : ContDiff ℝ r ζ) (hH : ∀ t, IsUnit (traceOperator C t)) (t : ℝ) (j : ℕ) (hj : j ≤ r) :
    hierarchy C ζ t j = iteratedDeriv j (traceResponse C ζ) t := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    cases j with
    | zero => rw [hierarchy_zero, iteratedDeriv_zero]
    | succ j =>
      rw [hierarchy_succ]
      have hrec := traceOperator_mul_iteratedDeriv_traceResponse C ζ hC hζ hH t (j + 1) hj
      have hsum : ∀ l ∈ Finset.range (j + 1),
          (((j + 1).choose (l + 1) : ℕ) : 𝔸) * (iteratedDeriv (l + 1) C t * hierarchy C ζ t (j - l))
            = (((j + 1).choose (l + 1) : ℕ) : 𝔸) *
              (iteratedDeriv (l + 1) C t * iteratedDeriv (j + 1 - (l + 1)) (traceResponse C ζ) t) := by
        intro l hl
        rw [ih (j - l) (by omega) (by omega), Nat.add_sub_add_right]
      rw [Finset.sum_congr rfl hsum, ← hrec, Ring.inverse_mul_cancel_left _ _ (hH t)]

/-- If `E^* v = −χ` at every time (the reconstruction identity `eq:supp-exact-scalar-v`),
then `χ_j = −E^* v^{(j)}` for `j ≤ r`. -/
theorem hierarchy_eq_neg_mul_iteratedDeriv {r : ℕ} (C ζ v : ℝ → 𝔸) (Est : 𝔸)
    (hC : ContDiff ℝ r C) (hζ : ContDiff ℝ r ζ) (hH : ∀ t, IsUnit (traceOperator C t))
    (hv : ContDiff ℝ r v) (hEv : ∀ t, Est * v t = -traceResponse C ζ t) (t : ℝ) (j : ℕ)
    (hj : j ≤ r) :
    hierarchy C ζ t j = -(Est * iteratedDeriv j v t) := by
  have hjr : (j : WithTop ℕ∞) ≤ r := by exact_mod_cast hj
  rw [hierarchy_eq_iteratedDeriv C ζ hC hζ hH t j hj,
    ← iteratedDeriv_const_mul Est (hv.contDiffAt.of_le hjr)]
  have hfun : (fun t => Est * v t) = fun t => -traceResponse C ζ t := funext hEv
  rw [hfun, iteratedDeriv_fun_neg, neg_neg]

/-- **`eq:supp-exact-first-time-source`**, first formula: `χ' = H⁻¹(ζ' + 3C'χ)`
(`r ≥ 1`). -/
theorem deriv_traceResponse_eq {r : ℕ} (C ζ : ℝ → 𝔸) (hC : ContDiff ℝ r C)
    (hζ : ContDiff ℝ r ζ) (hH : ∀ t, IsUnit (traceOperator C t)) (t : ℝ) (hr : 1 ≤ r) :
    deriv (traceResponse C ζ) t
      = Ring.inverse (traceOperator C t) *
          (deriv ζ t + 3 * (deriv C t * traceResponse C ζ t)) := by
  have h := hierarchy_eq_iteratedDeriv C ζ hC hζ hH t 1 hr
  rw [hierarchy_succ] at h
  simp only [iteratedDeriv_one] at h
  rw [← h]
  simp [hierarchy_zero]

/-- **`eq:supp-exact-first-time-source`**, second formula: for
`v = w − 3(I − Π)Eχ` with `Π`, `w`, `χ` differentiable at `t` and `E` constant,
`v' = w' + 3Π'Eχ − 3(I − Π)Eχ'`. -/
theorem hasDerivAt_response (Pr w χ : ℝ → 𝔸) (E : 𝔸) (Pr' w' χ' : 𝔸) (t : ℝ)
    (hPr : HasDerivAt Pr Pr' t) (hw : HasDerivAt w w' t) (hχ : HasDerivAt χ χ' t) :
    HasDerivAt (fun t => w t - 3 * ((1 - Pr t) * (E * χ t)))
      (w' + 3 * (Pr' * (E * χ t)) - 3 * ((1 - Pr t) * (E * χ' ))) t := by
  have h1 : HasDerivAt (fun t => (1 : 𝔸) - Pr t) (-Pr') t := by
    have := (hasDerivAt_const t (1 : 𝔸)).sub hPr
    rw [zero_sub] at this
    exact this
  have h2 : HasDerivAt (fun t => E * χ t) (E * χ') t := hχ.const_mul E
  have h3 := (h1.mul h2).const_mul (3 : 𝔸)
  refine (hw.sub h3).congr_deriv ?_
  simp only [neg_mul, mul_add, mul_neg]
  abel

end RenewalGeometry.ExactTimeHierarchy
