/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Renewal.SpectralDimension
import NCG.Renewal.WeylDichotomy
import NCG.Renewal.Dimensions

/-!
# The limsup bookkeeping, proved

**Theorems `thm:dimension-coincidence` / `thm:commuting`
(limsup layer)**: the repeatedly-deferred "log/log limsup bookkeeping"
— converting two-sided polynomial counting bounds into actual
dimension *equalities* — is proved here:

* `NCG.log_ratio_tendsto_of_poly_bounds` — two-sided polynomial bounds
  `c·n^q ≤ N(n) ≤ C·n^q` force `log N(n)/log n → q` (by reflecting the
  spectral-dimension squeeze `NCG.return_exponent_limit`);
* `NCG.limsup_log_ratio_of_poly_bounds` — hence the defining `limsup`
  *equals* `q`;
* `NCG.algebraicDimension_eq_of_poly_bounds` — applied to the actual
  `NCG.RenewalMemory.algebraicDimension`: any renewal memory whose
  channel counting function is two-sidedly polynomially bounded has
  `q_alg = q` **as an equality of the defined limsup**, not merely
  two-sided bounds;
* `NCG.latticeShell_log_dimension` — the free lattice model
  instantiated: `log N_c(R)/log R → c` from the exact Ehrhart/Weyl
  bounds, with the uniform constants `1/c!` and `(1 + c/2)^c/c!`.

The remaining open piece of `thm:dimension-coincidence` is the
return-completion identity `q_alg = 1 + b_eff` and the heat-kernel
link `d_s` (Delmotte), tracked in that record's note.
-/

namespace NCG

open Filter

/-- **The limsup bookkeeping (counting side)**: two-sided polynomial
bounds `c·n^q ≤ N(n) ≤ C·n^q` (from the second index on) force the
log–log ratio to converge to the exponent: `log N(n)/log n → q`. -/
theorem log_ratio_tendsto_of_poly_bounds (q c C : ℝ) (hc : 0 < c)
    (hC : 0 < C) (Nf : ℕ → ℝ)
    (hlow : ∀ n : ℕ, 2 ≤ n → c * (n:ℝ) ^ q ≤ Nf n)
    (hupp : ∀ n : ℕ, 2 ≤ n → Nf n ≤ C * (n:ℝ) ^ q) :
    Tendsto (fun n : ℕ => Real.log (Nf n) / Real.log n)
      atTop (nhds q) := by
  have h := return_exponent_limit (-q) c C hc hC Nf
    (fun n hn => by simpa [neg_neg] using hlow n hn)
    (fun n hn => by simpa [neg_neg] using hupp n hn)
  have hneg := h.neg
  simp only [neg_neg] at hneg
  refine hneg.congr fun n => ?_
  rw [neg_div, neg_neg]

/-- The defining `limsup` equals the exponent under two-sided
polynomial bounds. -/
theorem limsup_log_ratio_of_poly_bounds (q c C : ℝ) (hc : 0 < c)
    (hC : 0 < C) (Nf : ℕ → ℝ)
    (hlow : ∀ n : ℕ, 2 ≤ n → c * (n:ℝ) ^ q ≤ Nf n)
    (hupp : ∀ n : ℕ, 2 ≤ n → Nf n ≤ C * (n:ℝ) ^ q) :
    limsup (fun n : ℕ => Real.log (Nf n) / Real.log n) atTop = q :=
  (log_ratio_tendsto_of_poly_bounds q c C hc hC Nf hlow hupp).limsup_eq

/-- **`q_alg` as an actual equality**: a renewal memory whose channel
counting function satisfies two-sided polynomial bounds of exponent
`q` has algebraic predictive dimension *equal* to `q` — the defined
limsup, not merely a pair of growth bounds. -/
theorem RenewalMemory.algebraicDimension_eq_of_poly_bounds
    {E M : Type*} [Monoid M] (R : RenewalMemory E M) [Finite E]
    (q c C : ℝ) (hc : 0 < c) (hC : 0 < C)
    (hlow : ∀ n : ℕ, 2 ≤ n → c * (n:ℝ) ^ q ≤ (R.channelCount n : ℝ))
    (hupp : ∀ n : ℕ, 2 ≤ n → (R.channelCount n : ℝ) ≤ C * (n:ℝ) ^ q) :
    R.algebraicDimension = q :=
  limsup_log_ratio_of_poly_bounds q c C hc hC _ hlow hupp

/-- **Theorem `thm:commuting` (dimension link, free model)**: the free
lattice counting function has log–log dimension *exactly* `c` — from
the proved Ehrhart/Weyl bounds `(R+1)^c ≤ c!·N_c(R) ≤ (R+c)^c`, with
the uniform two-sided constants `1/c!` and `(1 + c/2)^c/c!` valid for
all `R ≥ 2`. -/
theorem latticeShell_log_dimension (c : ℕ) (hc : 0 < c) :
    Tendsto (fun R : ℕ =>
        Real.log (latticeShellCard c R : ℝ) / Real.log R)
      atTop (nhds c) := by
  have hfact : (0:ℝ) < c.factorial := by
    exact_mod_cast c.factorial_pos
  apply log_ratio_tendsto_of_poly_bounds (c:ℝ)
    (1 / c.factorial) ((1 + c / 2) ^ c / c.factorial)
    (by positivity) (by positivity)
  · -- lower bound: c!·N ≥ (R+1)^c ≥ R^c
    intro R hR
    have hw := (weyl_free_bounds c R).1
    have hcast : ((R:ℝ) + 1) ^ c
        ≤ (latticeShellCard c R : ℝ) * c.factorial := by
      exact_mod_cast hw
    have hpow : (R:ℝ) ^ c ≤ ((R:ℝ) + 1) ^ c := by
      apply pow_le_pow_left₀ (by positivity)
      linarith
    rw [show (R:ℝ) ^ (c:ℝ) = (R:ℝ) ^ c from
      Real.rpow_natCast _ c]
    rw [div_mul_eq_mul_div, div_le_iff₀ hfact, one_mul]
    calc (R:ℝ) ^ c ≤ ((R:ℝ) + 1) ^ c := hpow
      _ ≤ (latticeShellCard c R : ℝ) * c.factorial := hcast
  · -- upper bound: c!·N ≤ (R+c)^c ≤ ((1+c/2)·R)^c for R ≥ 2
    intro R hR
    have hw := (weyl_free_bounds c R).2
    have hcast : (latticeShellCard c R : ℝ) * c.factorial
        ≤ ((R:ℝ) + c) ^ c := by
      exact_mod_cast hw
    have hR2 : (2:ℝ) ≤ (R:ℝ) := by exact_mod_cast hR
    have hbound : (R:ℝ) + c ≤ (1 + c / 2) * R := by
      have : (c:ℝ) ≤ (c / 2) * R := by nlinarith [hR2]
      nlinarith
    have hpow : ((R:ℝ) + c) ^ c ≤ ((1 + c / 2) * (R:ℝ)) ^ c := by
      apply pow_le_pow_left₀ (by positivity) hbound
    rw [show (R:ℝ) ^ (c:ℝ) = (R:ℝ) ^ c from
      Real.rpow_natCast _ c]
    rw [div_mul_eq_mul_div, le_div_iff₀ hfact]
    calc (latticeShellCard c R : ℝ) * c.factorial
        ≤ ((R:ℝ) + c) ^ c := hcast
      _ ≤ ((1 + c / 2) * (R:ℝ)) ^ c := hpow
      _ = (1 + c / 2) ^ c * (R:ℝ) ^ c := mul_pow _ _ _

/-- **The limsup bookkeeping (metric side)**: two-sided polynomial
covering bounds `c·δ^{−q} ≤ N(δ) ≤ C·δ^{−q}` at small scales force the
metric log–log ratio to converge to the exponent along `δ → 0⁺`. -/
theorem metric_log_ratio_tendsto (q c C δ₀ : ℝ) (hc : 0 < c)
    (hC : 0 < C) (hδ₀ : 0 < δ₀) (N : ℝ → ℕ)
    (hlow : ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → c * δ ^ (-q) ≤ (N δ : ℝ))
    (hupp : ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → (N δ : ℝ) ≤ C * δ ^ (-q)) :
    Tendsto (fun δ : ℝ => Real.log (N δ) / Real.log (1 / δ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds q) := by
  have hlogtop : Tendsto (fun δ : ℝ => Real.log (1 / δ))
      (nhdsWithin 0 (Set.Ioi 0)) atTop := by
    have h1 : Tendsto (fun δ : ℝ => δ⁻¹)
        (nhdsWithin 0 (Set.Ioi 0)) atTop := tendsto_inv_nhdsGT_zero
    exact (Real.tendsto_log_atTop.comp h1).congr fun δ => by
      rw [Function.comp_apply, one_div]
  have hCz : Tendsto (fun δ : ℝ => Real.log C / Real.log (1 / δ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    Tendsto.div_atTop tendsto_const_nhds hlogtop
  have hcz : Tendsto (fun δ : ℝ => Real.log c / Real.log (1 / δ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    Tendsto.div_atTop tendsto_const_nhds hlogtop
  have hlo : Tendsto (fun δ : ℝ => q + Real.log c / Real.log (1 / δ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds q) := by
    simpa using tendsto_const_nhds.add hcz
  have hhi : Tendsto (fun δ : ℝ => q + Real.log C / Real.log (1 / δ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds q) := by
    simpa using tendsto_const_nhds.add hCz
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · filter_upwards [Ioo_mem_nhdsGT
      (lt_min hδ₀ one_pos : (0:ℝ) < min δ₀ 1)] with δ hδ
    obtain ⟨hδpos, hδlt⟩ := hδ
    have hδδ₀ : δ ≤ δ₀ := le_of_lt (lt_of_lt_of_le hδlt (min_le_left _ _))
    have hδ1 : δ < 1 := lt_of_lt_of_le hδlt (min_le_right _ _)
    have hinv1 : (1:ℝ) < 1 / δ := by
      rw [lt_div_iff₀ hδpos, one_mul]
      exact hδ1
    have hL : 0 < Real.log (1 / δ) := Real.log_pos hinv1
    have hr : (0:ℝ) < δ ^ (-q) := Real.rpow_pos_of_pos hδpos _
    have hNpos : (0:ℝ) < N δ :=
      lt_of_lt_of_le (mul_pos hc hr) (hlow δ hδpos hδδ₀)
    have hlogδ : Real.log (1 / δ) = -Real.log δ := by
      rw [one_div, Real.log_inv]
    have hlogp : Real.log c + q * Real.log (1 / δ) ≤ Real.log (N δ) := by
      calc Real.log c + q * Real.log (1 / δ)
          = Real.log (c * δ ^ (-q)) := by
            rw [Real.log_mul hc.ne' hr.ne', Real.log_rpow hδpos,
              hlogδ]
            ring
        _ ≤ Real.log (N δ) :=
            (Real.log_le_log_iff (mul_pos hc hr) hNpos).mpr
              (hlow δ hδpos hδδ₀)
    have heq : q + Real.log c / Real.log (1 / δ)
        = (q * Real.log (1 / δ) + Real.log c) / Real.log (1 / δ) := by
      field_simp
    rw [heq]
    have hdiv : 0 ≤ (Real.log (N δ)
        - (q * Real.log (1 / δ) + Real.log c)) / Real.log (1 / δ) :=
      div_nonneg (by linarith) hL.le
    rw [sub_div] at hdiv
    linarith
  · filter_upwards [Ioo_mem_nhdsGT
      (lt_min hδ₀ one_pos : (0:ℝ) < min δ₀ 1)] with δ hδ
    obtain ⟨hδpos, hδlt⟩ := hδ
    have hδδ₀ : δ ≤ δ₀ := le_of_lt (lt_of_lt_of_le hδlt (min_le_left _ _))
    have hδ1 : δ < 1 := lt_of_lt_of_le hδlt (min_le_right _ _)
    have hinv1 : (1:ℝ) < 1 / δ := by
      rw [lt_div_iff₀ hδpos, one_mul]
      exact hδ1
    have hL : 0 < Real.log (1 / δ) := Real.log_pos hinv1
    have hr : (0:ℝ) < δ ^ (-q) := Real.rpow_pos_of_pos hδpos _
    have hNpos : (0:ℝ) < N δ :=
      lt_of_lt_of_le (mul_pos hc hr) (hlow δ hδpos hδδ₀)
    have hlogδ : Real.log (1 / δ) = -Real.log δ := by
      rw [one_div, Real.log_inv]
    have hlogp : Real.log (N δ) ≤ Real.log C + q * Real.log (1 / δ) := by
      calc Real.log (N δ) ≤ Real.log (C * δ ^ (-q)) :=
            (Real.log_le_log_iff hNpos (mul_pos hC hr)).mpr
              (hupp δ hδpos hδδ₀)
        _ = Real.log C + q * Real.log (1 / δ) := by
            rw [Real.log_mul hC.ne' hr.ne', Real.log_rpow hδpos,
              hlogδ]
            ring
    have heq : q + Real.log C / Real.log (1 / δ)
        = (q * Real.log (1 / δ) + Real.log C) / Real.log (1 / δ) := by
      field_simp
    rw [heq]
    have hdiv : 0 ≤ ((q * Real.log (1 / δ) + Real.log C)
        - Real.log (N δ)) / Real.log (1 / δ) :=
      div_nonneg (by linarith) hL.le
    rw [sub_div] at hdiv
    linarith

/-- **`q_met` as an actual equality**: a set whose covering numbers
satisfy two-sided polynomial bounds of exponent `q` at small scales
has upper box dimension *equal* to `q` — the defined limsup, not
merely growth bounds. -/
theorem upperBoxDimension_eq_of_poly_bounds {X : Type*}
    [PseudoMetricSpace X] (s : Set X) (q c C δ₀ : ℝ) (hc : 0 < c)
    (hC : 0 < C) (hδ₀ : 0 < δ₀)
    (hlow : ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      c * δ ^ (-q) ≤ (coveringNumber s δ : ℝ))
    (hupp : ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      (coveringNumber s δ : ℝ) ≤ C * δ ^ (-q)) :
    upperBoxDimension s = q :=
  (metric_log_ratio_tendsto q c C δ₀ hc hC hδ₀ _ hlow hupp).limsup_eq

/-- **`q_met = q_alg` (Theorem `thm:dimension-coincidence`,
channel-coding link)**: when the two-sided channel coding transfers
polynomial bounds of the *same* exponent to both the covering numbers
and the channel counting function, the defined metric and algebraic
dimensions are *equal* — the limsup bookkeeping of the coincidence
chain, proved. -/
theorem qmet_eq_qalg_of_poly_bounds {X E M : Type*}
    [PseudoMetricSpace X] (s : Set X) [Monoid M]
    (R : RenewalMemory E M) [Finite E] (q cm Cm δ₀ ca Ca : ℝ)
    (hcm : 0 < cm) (hCm : 0 < Cm) (hδ₀ : 0 < δ₀) (hca : 0 < ca)
    (hCa : 0 < Ca)
    (hmlow : ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      cm * δ ^ (-q) ≤ (coveringNumber s δ : ℝ))
    (hmupp : ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ →
      (coveringNumber s δ : ℝ) ≤ Cm * δ ^ (-q))
    (halow : ∀ n : ℕ, 2 ≤ n → ca * (n:ℝ) ^ q ≤ (R.channelCount n : ℝ))
    (haupp : ∀ n : ℕ, 2 ≤ n → (R.channelCount n : ℝ) ≤ Ca * (n:ℝ) ^ q) :
    upperBoxDimension s = R.algebraicDimension := by
  rw [upperBoxDimension_eq_of_poly_bounds s q cm Cm δ₀ hcm hCm hδ₀
      hmlow hmupp,
    R.algebraicDimension_eq_of_poly_bounds q ca Ca hca hCa halow haupp]

end NCG
