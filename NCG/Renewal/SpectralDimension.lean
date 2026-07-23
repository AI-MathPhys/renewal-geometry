/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Return-probability spectral dimension

**Corollary `cor:return-spectral-dimension`**: under two-sided
polynomial return-probability bounds `c·n^{−γ} ≤ p(n) ≤ C·n^{−γ}` the
log–log return exponent converges: `−log p(n)/log n → γ`
(`NCG.return_exponent_limit`) — with `γ = d_s/2` this is the
spectral-dimension identification.  The Delmotte two-sided Gaussian
heat-kernel bounds supplying the hypotheses are the noted external
input.
-/

namespace NCG

open Filter

/-- **Corollary `cor:return-spectral-dimension` (limit core)**:
two-sided polynomial bounds on the return probability pin the log–log
exponent: `−log p(n)/log n → γ`. -/
theorem return_exponent_limit (γ c C : ℝ) (hc : 0 < c) (hC : 0 < C)
    (p : ℕ → ℝ)
    (hlow : ∀ n : ℕ, 2 ≤ n → c * (n:ℝ) ^ (-γ) ≤ p n)
    (hupp : ∀ n : ℕ, 2 ≤ n → p n ≤ C * (n:ℝ) ^ (-γ)) :
    Tendsto (fun n : ℕ => -Real.log (p n) / Real.log n)
      atTop (nhds γ) := by
  have hlogtop : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hCz : Tendsto (fun n : ℕ => Real.log C / Real.log n)
      atTop (nhds 0) := Tendsto.div_atTop tendsto_const_nhds hlogtop
  have hcz : Tendsto (fun n : ℕ => Real.log c / Real.log n)
      atTop (nhds 0) := Tendsto.div_atTop tendsto_const_nhds hlogtop
  have hlo : Tendsto (fun n : ℕ => γ - Real.log C / Real.log n)
      atTop (nhds γ) := by
    simpa using tendsto_const_nhds.sub hCz
  have hhi : Tendsto (fun n : ℕ => γ - Real.log c / Real.log n)
      atTop (nhds γ) := by
    simpa using tendsto_const_nhds.sub hcz
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hn1 : (1:ℝ) < n := by exact_mod_cast (by omega : 1 < n)
    have hnpos : (0:ℝ) < n := by linarith
    have hL : 0 < Real.log n := Real.log_pos hn1
    have hr : (0:ℝ) < (n:ℝ) ^ (-γ) := Real.rpow_pos_of_pos hnpos _
    have hppos : 0 < p n := lt_of_lt_of_le (mul_pos hc hr) (hlow n hn)
    have hlogp : Real.log (p n) ≤ Real.log C + -γ * Real.log n := by
      calc Real.log (p n) ≤ Real.log (C * (n:ℝ) ^ (-γ)) :=
            (Real.log_le_log_iff hppos (mul_pos hC hr)).mpr (hupp n hn)
        _ = Real.log C + -γ * Real.log n := by
            rw [Real.log_mul hC.ne' hr.ne', Real.log_rpow hnpos]
    have heq : γ - Real.log C / Real.log n
        = (γ * Real.log n - Real.log C) / Real.log n := by
      field_simp
    rw [heq]
    have hdiv : 0 ≤ (-Real.log (p n)
        - (γ * Real.log n - Real.log C)) / Real.log n :=
      div_nonneg (by linarith) hL.le
    rw [sub_div] at hdiv
    linarith
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hn1 : (1:ℝ) < n := by exact_mod_cast (by omega : 1 < n)
    have hnpos : (0:ℝ) < n := by linarith
    have hL : 0 < Real.log n := Real.log_pos hn1
    have hr : (0:ℝ) < (n:ℝ) ^ (-γ) := Real.rpow_pos_of_pos hnpos _
    have hppos : 0 < p n := lt_of_lt_of_le (mul_pos hc hr) (hlow n hn)
    have hlogp : Real.log c + -γ * Real.log n ≤ Real.log (p n) := by
      calc Real.log c + -γ * Real.log n
          = Real.log (c * (n:ℝ) ^ (-γ)) := by
            rw [Real.log_mul hc.ne' hr.ne', Real.log_rpow hnpos]
        _ ≤ Real.log (p n) :=
            (Real.log_le_log_iff (mul_pos hc hr) hppos).mpr (hlow n hn)
    have heq : γ - Real.log c / Real.log n
        = (γ * Real.log n - Real.log c) / Real.log n := by
      field_simp
    rw [heq]
    have hdiv : 0 ≤ ((γ * Real.log n - Real.log c)
        - -Real.log (p n)) / Real.log n :=
      div_nonneg (by linarith) hL.le
    rw [sub_div] at hdiv
    linarith

end NCG
