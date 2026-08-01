/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Store-jet/autocorrelation identity and frequency moments
  (`thm:store-autocorrelation-master`,
   `def:store-frequency-moments-master`, flagship manuscript)

On the retained carrier (a real inner product space) let `δ = D`
be the Store derivation and `z_j` the loaded spectral components of
the pointer `Z = Σ_j z_j`, with `δ²z_j = -4λ_j z_j`, `λ_j > 0`,
`⟨z_j, δz_j⟩ = 0` (skew-adjointness on the diagonal), and
orthogonal `δ`-invariant spectral planes.  Then:

* the boxed autocorrelation formula
  `c_Z(t) = ⟨Z, e^{tδ}Z⟩ = Σ_j w_j cos(2μ_j t)` with `w_j = ‖z_j‖²`
  and `μ_j = √λ_j` (`store_autocorrelation`), obtained from the
  exponential series on each invariant plane — the even part sums
  to the cosine series, the odd part is annihilated by
  `⟨z_j, δz_j⟩ = 0`;
* the boxed moment packet
  `m_n = ⟨Z, 𝒦ⁿZ⟩ = Σ_j w_j λ_jⁿ` for `𝒦 = -¼δ²`
  (`store_frequency_moments`);
* the boxed jet identity: every odd derivative of the closed-form
  autocorrelation vanishes at the origin and
  `c_Z^{(2n)}(0) = (-4)ⁿ m_n`, i.e. `m_n = (-1)ⁿ4⁻ⁿ c_Z^{(2n)}(0)`
  (`store_jet_even`, `store_jet_odd`, stated in multiplied form).

The spectral decomposition of the manuscript enters through the
hypotheses on the components `z_j` (disclosed interface); `Z` is
its loaded part.
-/

open NormedSpace Finset
open scoped RealInnerProductSpace

namespace NCG

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

omit [CompleteSpace E] in
/-- Even powers on an oscillation plane. -/
lemma pow_even_apply (D : E →L[ℝ] E) (v : E) (c : ℝ)
    (hv : D (D v) = c • v) (k : ℕ) :
    (D ^ (2 * k)) v = c ^ k • v := by
  induction k with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 2 by ring, pow_add]
    have happ : (D ^ (2 * m) * D ^ 2) v = (D ^ (2 * m)) ((D ^ 2) v) :=
      rfl
    have h2 : (D ^ 2) v = c • v := by
      rw [pow_two]
      exact hv
    rw [happ, h2, map_smul, ih, smul_smul, ← pow_succ']

omit [CompleteSpace E] in
/-- Odd powers on an oscillation plane. -/
lemma pow_odd_apply (D : E →L[ℝ] E) (v : E) (c : ℝ)
    (hv : D (D v) = c • v) (k : ℕ) :
    (D ^ (2 * k + 1)) v = c ^ k • D v := by
  have hDv : D (D (D v)) = c • D v := by
    rw [hv, map_smul]
  have happ : (D ^ (2 * k + 1)) v = (D ^ (2 * k)) (D v) := by
    rw [pow_succ]
    rfl
  rw [happ, pow_even_apply D (D v) c hDv k]

/-- Exponential-series inner product on an oscillation plane: if
`D²z = -ω²z` and `y` pairs trivially with `Dz`, then
`⟨y, e^{tD}z⟩ = ⟨y,z⟩·cos(ωt)`. -/
lemma exp_inner_cos (D : E →L[ℝ] E) (y z : E) (ω a : ℝ)
    (hD2 : D (D z) = -(ω ^ 2) • z)
    (hyz : ⟪y, z⟫ = a) (hyDz : ⟪y, D z⟫ = 0) (t : ℝ) :
    ⟪y, (exp (t • D)) z⟫ = a * Real.cos (ω * t) := by
  have hs := exp_series_hasSum_exp' (𝕂 := ℝ) (t • D)
  have hsz := (ContinuousLinearMap.apply ℝ E z).hasSum hs
  have hsy := (innerSL ℝ y).hasSum hsz
  simp only [ContinuousLinearMap.apply_apply, innerSL_apply_apply]
    at hsy
  have hterm : ∀ n : ℕ,
      ⟪y, (((n.factorial : ℝ))⁻¹ • (t • D) ^ n) z⟫
        = ((n.factorial : ℝ))⁻¹ * t ^ n * ⟪y, (D ^ n) z⟫ := by
    intro n
    rw [smul_pow, smul_smul,
      show ((((n.factorial : ℝ))⁻¹ * t ^ n) • D ^ n) z
        = (((n.factorial : ℝ))⁻¹ * t ^ n) • (D ^ n) z from rfl,
      real_inner_smul_right]
  have heven : HasSum
      (fun k : ℕ =>
        ⟪y, ((((2 * k).factorial : ℝ))⁻¹ • (t • D) ^ (2 * k)) z⟫)
      (a * Real.cos (ω * t)) := by
    have hfe : (fun k : ℕ =>
        ⟪y, ((((2 * k).factorial : ℝ))⁻¹ • (t • D) ^ (2 * k)) z⟫)
        = fun k => a * ((-1) ^ k * (ω * t) ^ (2 * k)
          / ((2 * k).factorial : ℝ)) := by
      funext k
      rw [hterm (2 * k), pow_even_apply D z (-(ω ^ 2)) hD2 k,
        real_inner_smul_right, hyz,
        show (-(ω ^ 2)) ^ k = (-1) ^ k * ω ^ (2 * k) by
          rw [neg_pow, pow_mul],
        mul_pow]
      field_simp
    rw [hfe]
    exact (Real.hasSum_cos (ω * t)).mul_left a
  have hodd : HasSum
      (fun k : ℕ =>
        ⟪y, ((((2 * k + 1).factorial : ℝ))⁻¹
          • (t • D) ^ (2 * k + 1)) z⟫) 0 := by
    have hfe : (fun k : ℕ =>
        ⟪y, ((((2 * k + 1).factorial : ℝ))⁻¹
          • (t • D) ^ (2 * k + 1)) z⟫)
        = fun _ => (0 : ℝ) := by
      funext k
      rw [hterm (2 * k + 1), pow_odd_apply D z (-(ω ^ 2)) hD2 k,
        real_inner_smul_right, hyDz]
      ring
    rw [hfe]
    exact hasSum_zero
  have hcombined := HasSum.even_add_odd
    (f := fun n : ℕ =>
      ⟪y, (((n.factorial : ℝ))⁻¹ • (t • D) ^ n) z⟫)
    heven hodd
  rw [add_zero] at hcombined
  exact hsy.unique hcombined

section Main

variable {s : ℕ} (D : E →L[ℝ] E) (z : Fin s → E) (lam : Fin s → ℝ)

omit [CompleteSpace E] in
/-- The pointer pairs with each component through its own weight. -/
lemma pointer_inner
    (horth : ∀ i j, i ≠ j → ⟪z i, z j⟫ = 0) (j : Fin s) :
    ⟪∑ i, z i, z j⟫ = ‖z j‖ ^ 2 := by
  rw [sum_inner]
  rw [Finset.sum_eq_single j (fun i _ hij => horth i j hij)
    (fun h => absurd (mem_univ j) h)]
  exact real_inner_self_eq_norm_sq (z j)

omit [CompleteSpace E] in
/-- The pointer pairs trivially with each rotated component. -/
lemma pointer_inner_rot
    (hskew : ∀ j, ⟪z j, D (z j)⟫ = 0)
    (horthD : ∀ i j, i ≠ j → ⟪z i, D (z j)⟫ = 0) (j : Fin s) :
    ⟪∑ i, z i, D (z j)⟫ = 0 := by
  rw [sum_inner]
  rw [Finset.sum_eq_single j (fun i _ hij => horthD i j hij)
    (fun h => absurd (mem_univ j) h)]
  exact hskew j

/-- `thm:store-autocorrelation-master`, boxed formula:
`c_Z(t) = Σ_j w_j cos(2μ_j t)`. -/
theorem store_autocorrelation (hlam : ∀ j, 0 ≤ lam j)
    (hD2 : ∀ j, D (D (z j)) = -(4 * lam j) • z j)
    (hskew : ∀ j, ⟪z j, D (z j)⟫ = 0)
    (horth : ∀ i j, i ≠ j → ⟪z i, z j⟫ = 0)
    (horthD : ∀ i j, i ≠ j → ⟪z i, D (z j)⟫ = 0) (t : ℝ) :
    ⟪∑ i, z i, (exp (t • D)) (∑ j, z j)⟫
      = ∑ j, ‖z j‖ ^ 2 * Real.cos (2 * Real.sqrt (lam j) * t) := by
  rw [map_sum, inner_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine exp_inner_cos D (∑ i, z i) (z j) (2 * Real.sqrt (lam j))
    (‖z j‖ ^ 2) ?_ (pointer_inner z horth j)
    (pointer_inner_rot D z hskew horthD j) t
  rw [show (2 * Real.sqrt (lam j)) ^ 2 = 4 * lam j by
    rw [mul_pow, Real.sq_sqrt (hlam j)]; ring]
  exact hD2 j

omit [CompleteSpace E] in
/-- `def:store-frequency-moments-master`, boxed identity: the
moment packet `m_n = ⟨Z, 𝒦ⁿZ⟩ = Σ_j w_j λ_jⁿ` for `𝒦 = -¼δ²`. -/
theorem store_frequency_moments
    (hD2 : ∀ j, D (D (z j)) = -(4 * lam j) • z j)
    (horth : ∀ i j, i ≠ j → ⟪z i, z j⟫ = 0) (n : ℕ) :
    ⟪∑ i, z i, (((-(4 : ℝ)⁻¹) • (D * D)) ^ n) (∑ j, z j)⟫
      = ∑ j, ‖z j‖ ^ 2 * lam j ^ n := by
  have heig : ∀ j, ((-(4 : ℝ)⁻¹) • (D * D)) (z j) = lam j • z j := by
    intro j
    have happ : ((-(4 : ℝ)⁻¹) • (D * D)) (z j)
        = (-(4 : ℝ)⁻¹) • D (D (z j)) := rfl
    rw [happ, hD2 j, smul_smul]
    congr 1
    ring
  have hpow : ∀ j, (((-(4 : ℝ)⁻¹) • (D * D)) ^ n) (z j)
      = lam j ^ n • z j := by
    intro j
    induction n with
    | zero => simp
    | succ m ih =>
      rw [pow_succ']
      have happ : ((((-(4 : ℝ)⁻¹) • (D * D))
            * (((-(4 : ℝ)⁻¹) • (D * D)) ^ m)) (z j))
          = ((-(4 : ℝ)⁻¹) • (D * D)) ((((-(4 : ℝ)⁻¹) • (D * D)) ^ m) (z j)) :=
        rfl
      rw [happ, ih, map_smul, heig j, smul_smul, ← pow_succ]
  rw [map_sum, inner_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hpow j, real_inner_smul_right, pointer_inner z horth j]
  ring

end Main

/-! ### Jet identities for the closed-form autocorrelation -/

section Jets

variable {s : ℕ}

/-- Derivative of a cosine family. -/
lemma deriv_cos_family (v a : Fin s → ℝ) :
    deriv (fun t => ∑ j, v j * Real.cos (a j * t))
      = fun t => ∑ j, (-(v j * a j)) * Real.sin (a j * t) := by
  funext t
  have h : HasDerivAt (fun t => ∑ j, v j * Real.cos (a j * t))
      (∑ j, (-(v j * a j)) * Real.sin (a j * t)) t := by
    refine HasDerivAt.fun_sum fun j _ => ?_
    have h1 : HasDerivAt (fun t : ℝ => a j * t) (a j) t := by
      simpa using (hasDerivAt_id t).const_mul (a j)
    have h2 := (Real.hasDerivAt_cos (a j * t)).comp t h1
    have h3 := h2.const_mul (v j)
    refine h3.congr_deriv ?_
    ring
  exact h.deriv

/-- Derivative of a sine family. -/
lemma deriv_sin_family (v a : Fin s → ℝ) :
    deriv (fun t => ∑ j, v j * Real.sin (a j * t))
      = fun t => ∑ j, (v j * a j) * Real.cos (a j * t) := by
  funext t
  have h : HasDerivAt (fun t => ∑ j, v j * Real.sin (a j * t))
      (∑ j, (v j * a j) * Real.cos (a j * t)) t := by
    refine HasDerivAt.fun_sum fun j _ => ?_
    have h1 : HasDerivAt (fun t : ℝ => a j * t) (a j) t := by
      simpa using (hasDerivAt_id t).const_mul (a j)
    have h2 := (Real.hasDerivAt_sin (a j * t)).comp t h1
    have h3 := h2.const_mul (v j)
    refine h3.congr_deriv ?_
    ring
  exact h.deriv

/-- Even iterated derivatives of a cosine family. -/
lemma iteratedDeriv_even_cos_family (n : ℕ) (v a : Fin s → ℝ) :
    iteratedDeriv (2 * n) (fun t => ∑ j, v j * Real.cos (a j * t))
      = fun t => ∑ j, ((-(a j ^ 2)) ^ n * v j) * Real.cos (a j * t) := by
  induction n generalizing v with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring,
      iteratedDeriv_succ', deriv_cos_family, iteratedDeriv_succ',
      deriv_sin_family, ih]
    funext t
    refine Finset.sum_congr rfl fun j _ => ?_
    ring

/-- Odd iterated derivatives of a cosine family vanish at the
origin. -/
lemma iteratedDeriv_odd_cos_family (n : ℕ) (v a : Fin s → ℝ) :
    iteratedDeriv (2 * n + 1)
      (fun t => ∑ j, v j * Real.cos (a j * t)) 0 = 0 := by
  have hsin : ∀ (w : Fin s → ℝ), iteratedDeriv (2 * n)
      (fun t => ∑ j, w j * Real.sin (a j * t))
      = fun t => ∑ j, ((-(a j ^ 2)) ^ n * w j) * Real.sin (a j * t) := by
    intro w
    induction n generalizing w with
    | zero => simp
    | succ m ih =>
      rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring,
        iteratedDeriv_succ', deriv_sin_family, iteratedDeriv_succ',
        deriv_cos_family, ih]
      funext t
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
  rw [iteratedDeriv_succ', deriv_cos_family, hsin]
  simp

/-- `thm:store-autocorrelation-master`, boxed jet identity in
multiplied form: `c_Z^{(2n)}(0) = (-4)ⁿ m_n`, so
`m_n = (-1)ⁿ4⁻ⁿ c_Z^{(2n)}(0)`. -/
theorem store_jet_even (w lam : Fin s → ℝ) (hlam : ∀ j, 0 ≤ lam j)
    (n : ℕ) :
    iteratedDeriv (2 * n)
      (fun t => ∑ j, w j * Real.cos (2 * Real.sqrt (lam j) * t)) 0
      = (-4) ^ n * ∑ j, w j * lam j ^ n := by
  rw [iteratedDeriv_even_cos_family n w
    (fun j => 2 * Real.sqrt (lam j))]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_zero, Real.cos_zero,
    show (2 * Real.sqrt (lam j)) ^ 2 = 4 * lam j by
      rw [mul_pow, Real.sq_sqrt (hlam j)]; ring,
    show (-(4 * lam j)) ^ n = (-4) ^ n * lam j ^ n by
      rw [show -(4 * lam j) = (-4) * lam j by ring, mul_pow]]
  ring

/-- Every odd derivative of the autocorrelation vanishes at the
origin. -/
theorem store_jet_odd (w lam : Fin s → ℝ) (n : ℕ) :
    iteratedDeriv (2 * n + 1)
      (fun t => ∑ j, w j * Real.cos (2 * Real.sqrt (lam j) * t)) 0
      = 0 :=
  iteratedDeriv_odd_cos_family n w (fun j => 2 * Real.sqrt (lam j))

end Jets

end NCG
