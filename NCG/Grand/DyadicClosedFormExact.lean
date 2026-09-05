/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.DyadicMeanExact

/-!
# The commuting closed form of the dyadic iterate

Step (D4g) of the finite Uhlmann-monotonicity programme for
`thm:accepted-Petz-sufficiency`: on commuting legs the dyadic iterate is
the interpolation power family,

`Λ #_{2⁻ᵏ} Ρ = Λ^{1−2⁻ᵏ} Ρ^{2⁻ᵏ}`.

* `rpow_half_mul_self`: the junk-compatible halving identity;
* `iterMean_commute_closed`: the closed form, by induction through
  `geoMean_commute` and square-root uniqueness.
-/

open Matrix Unitary Finset
open scoped ComplexOrder

namespace NCG
namespace QRE

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {Λ Ρ : Matrix n n ℂ}

/-! ### Scalar power helpers -/

theorem rpow_half_mul_self {x : ℝ} (hx : 0 ≤ x) {a : ℝ} (ha : 0 ≤ a) :
    x ^ (a / 2) * x ^ (a / 2) = x ^ a := by
  rcases eq_or_lt_of_le ha with h0 | hapos
  · rw [← h0]
    norm_num
  · rcases eq_or_lt_of_le hx with hx0 | hxpos
    · rw [← hx0, Real.zero_rpow (by positivity : a / 2 ≠ 0),
        Real.zero_rpow hapos.ne', mul_zero]
    · rw [← Real.rpow_add hxpos]
      congr 1
      ring

/-! ### The closed form -/

set_option maxHeartbeats 3200000 in -- commuting collapse chain
/-- **The commuting closed form**:
`Λ #_{2⁻ᵏ} Ρ = Λ^{1−2⁻ᵏ} Ρ^{2⁻ᵏ}` for commuting legs. -/
theorem iterMean_commute_closed (hΛ : Λ.PosDef) (hΡ : Ρ.PosSemidef)
    (hcomm : Commute Λ Ρ) (k : ℕ) :
    iterMean hΛ hΡ.1 k =
      matFun hΛ.1 (fun x => x ^ (1 - (2 : ℝ)⁻¹ ^ k)) *
        matFun hΡ.1 (fun x => x ^ ((2 : ℝ)⁻¹ ^ k)) := by
  induction k with
  | zero =>
      rw [iterMean_zero]
      have h1 : matFun hΛ.1 (fun x => x ^ (1 - (2 : ℝ)⁻¹ ^ 0)) = 1 := by
        rw [Petz.matFun_congr hΛ.1 _ (fun _ => 1) fun i => by norm_num]
        exact Petz.matFun_one hΛ.1
      have h2 : matFun hΡ.1 (fun x => x ^ ((2 : ℝ)⁻¹ ^ 0)) = Ρ := by
        rw [Petz.matFun_congr hΡ.1 _ id fun i => by
          simp [Real.rpow_one]]
        exact Petz.matFun_id hΡ.1
      rw [h1, h2, Matrix.one_mul]
  | succ k ih =>
      rw [iterMean_succ]
      have hb2 : ((2 : ℝ)⁻¹ ^ k) ≤ 1 :=
        pow_le_one₀ (by norm_num) (by norm_num)
      have ha_nonneg : (0 : ℝ) ≤ 1 - (2 : ℝ)⁻¹ ^ k := by linarith
      have hb_pos : (0 : ℝ) < (2 : ℝ)⁻¹ ^ k := by positivity
      -- the two commuting spectral factors
      have hMM : Commute (matFun hΛ.1 fun x => x ^ ((1 - (2:ℝ)⁻¹ ^ k) / 2))
          (matFun hΡ.1 fun x => x ^ (((2:ℝ)⁻¹ ^ k) / 2)) := by
        have h1 : Commute
            (matFun hΛ.1 fun x => x ^ ((1 - (2:ℝ)⁻¹ ^ k) / 2)) Ρ :=
          (commute_matFun_right hΛ.1 _ hcomm.symm).symm
        exact commute_matFun_right hΡ.1 _ h1
      -- Λ commutes with the k-th iterate
      have hcommT : Commute Λ (iterMean hΛ hΡ.1 k) := by
        rw [ih]
        exact Commute.mul_right
          (commute_matFun_right hΛ.1 _ (Commute.refl Λ))
          (commute_matFun_right hΡ.1 _ hcomm)
      have hTk_psd : (iterMean hΛ hΡ.1 k).PosSemidef :=
        iterMean_posSemidef hΛ hΡ k
      rw [geoMean_commute hΛ hTk_psd hcommT]
      -- the square roots
      have hsqrtΛ : Petz.sqrtMat hΛ.1 =
          matFun hΛ.1 fun x => x ^ ((2 : ℝ)⁻¹) := by
        unfold Petz.sqrtMat
        refine Petz.matFun_congr hΛ.1 _ _ fun i => ?_
        rw [show ((2 : ℝ)⁻¹) = (1 / 2 : ℝ) by norm_num]
        exact Real.sqrt_eq_rpow _
      have hsqrtT : Petz.sqrtMat hTk_psd.1 =
          matFun hΛ.1 (fun x => x ^ ((1 - (2:ℝ)⁻¹ ^ k) / 2)) *
            matFun hΡ.1 (fun x => x ^ (((2:ℝ)⁻¹ ^ k) / 2)) := by
        refine (posSemidef_sqrt_unique hTk_psd
          (commute_psd_mul_psd
            (matFun_posSemidef hΛ.1 _ fun i =>
              Real.rpow_nonneg (hΛ.posSemidef.eigenvalues_nonneg i) _)
            (matFun_posSemidef hΡ.1 _ fun i =>
              Real.rpow_nonneg (hΡ.eigenvalues_nonneg i) _) hMM) ?_).symm
        calc (matFun hΛ.1 (fun x => x ^ ((1 - (2:ℝ)⁻¹ ^ k) / 2)) *
              matFun hΡ.1 (fun x => x ^ (((2:ℝ)⁻¹ ^ k) / 2))) *
              (matFun hΛ.1 (fun x => x ^ ((1 - (2:ℝ)⁻¹ ^ k) / 2)) *
              matFun hΡ.1 (fun x => x ^ (((2:ℝ)⁻¹ ^ k) / 2)))
            = matFun hΛ.1 (fun x => x ^ ((1 - (2:ℝ)⁻¹ ^ k) / 2)) *
                (matFun hΡ.1 (fun x => x ^ (((2:ℝ)⁻¹ ^ k) / 2)) *
                matFun hΛ.1 (fun x => x ^ ((1 - (2:ℝ)⁻¹ ^ k) / 2))) *
                matFun hΡ.1 (fun x => x ^ (((2:ℝ)⁻¹ ^ k) / 2)) := by
              simp only [Matrix.mul_assoc]
          _ = matFun hΛ.1 (fun x => x ^ ((1 - (2:ℝ)⁻¹ ^ k) / 2)) *
                (matFun hΛ.1 (fun x => x ^ ((1 - (2:ℝ)⁻¹ ^ k) / 2)) *
                matFun hΡ.1 (fun x => x ^ (((2:ℝ)⁻¹ ^ k) / 2))) *
                matFun hΡ.1 (fun x => x ^ (((2:ℝ)⁻¹ ^ k) / 2)) := by
              rw [hMM.symm.eq]
          _ = (matFun hΛ.1 (fun x => x ^ ((1 - (2:ℝ)⁻¹ ^ k) / 2)) *
                matFun hΛ.1 (fun x => x ^ ((1 - (2:ℝ)⁻¹ ^ k) / 2))) *
                (matFun hΡ.1 (fun x => x ^ (((2:ℝ)⁻¹ ^ k) / 2)) *
                matFun hΡ.1 (fun x => x ^ (((2:ℝ)⁻¹ ^ k) / 2))) := by
              simp only [Matrix.mul_assoc]
          _ = iterMean hΛ hΡ.1 k := by
              rw [matFun_mul, matFun_mul, ih]
              congr 1
              · refine Petz.matFun_congr hΛ.1 _ _ fun i => ?_
                exact rpow_half_mul_self
                  (hΛ.posSemidef.eigenvalues_nonneg i) ha_nonneg
              · refine Petz.matFun_congr hΡ.1 _ _ fun i => ?_
                exact rpow_half_mul_self
                  (hΡ.eigenvalues_nonneg i) hb_pos.le
      rw [hsqrtΛ, hsqrtT]
      -- collapse the Λ-powers
      calc matFun hΛ.1 (fun x => x ^ ((2 : ℝ)⁻¹)) *
            (matFun hΛ.1 (fun x => x ^ ((1 - (2:ℝ)⁻¹ ^ k) / 2)) *
            matFun hΡ.1 (fun x => x ^ (((2:ℝ)⁻¹ ^ k) / 2)))
          = (matFun hΛ.1 (fun x => x ^ ((2 : ℝ)⁻¹)) *
              matFun hΛ.1 (fun x => x ^ ((1 - (2:ℝ)⁻¹ ^ k) / 2))) *
              matFun hΡ.1 (fun x => x ^ (((2:ℝ)⁻¹ ^ k) / 2)) := by
            rw [Matrix.mul_assoc]
        _ = matFun hΛ.1 (fun x => x ^ (1 - (2 : ℝ)⁻¹ ^ (k + 1))) *
              matFun hΡ.1 (fun x => x ^ ((2 : ℝ)⁻¹ ^ (k + 1))) := by
            rw [matFun_mul]
            have h1 : matFun hΛ.1 (fun x =>
                x ^ ((2 : ℝ)⁻¹) * x ^ ((1 - (2 : ℝ)⁻¹ ^ k) / 2)) =
                matFun hΛ.1 (fun x => x ^ (1 - (2 : ℝ)⁻¹ ^ (k + 1))) := by
              refine Petz.matFun_congr hΛ.1 _ _ fun i => ?_
              rw [← Real.rpow_add (hΛ.eigenvalues_pos i)]
              have hexp : (2 : ℝ)⁻¹ + (1 - (2 : ℝ)⁻¹ ^ k) / 2 =
                  1 - (2 : ℝ)⁻¹ ^ (k + 1) := by
                rw [pow_succ]
                ring
              rw [hexp]
            have h2 : matFun hΡ.1 (fun x => x ^ (((2 : ℝ)⁻¹ ^ k) / 2)) =
                matFun hΡ.1 (fun x => x ^ ((2 : ℝ)⁻¹ ^ (k + 1))) := by
              refine Petz.matFun_congr hΡ.1 _ _ fun i => ?_
              have hexp : ((2 : ℝ)⁻¹ ^ k) / 2 = (2 : ℝ)⁻¹ ^ (k + 1) := by
                rw [pow_succ]
                ring
              rw [hexp]
            rw [h1, h2]

end QRE
end NCG
