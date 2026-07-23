/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Upstream.CWPatterns
import NCG.Upstream.CWPressure

/-!
# Mass facts for the Curie–Weiss phase limits

Supporting layer for `thm:cw-spontaneous-orientation`: total mass
one, fibre-mass decomposition, the zero-field reflection symmetry of
fibre masses, boundedness of the hypergeometric weight, and the
field-tilt factorization of fibre weights.
-/

namespace NCG.Upstream

open Finset Real

section MassFacts

variable {N : ℕ} (hN : 0 < N) (lam h : ℝ)

/-- The fibre mass `μ_N(count = k)`. -/
noncomputable def fibreMass (N : ℕ) (lam h : ℝ) (k : ℕ) : ℝ :=
  ∑ η ∈ Finset.univ.filter
    (fun η : Fin N → Bool => countTrue N η = k),
    cwMeasure N lam h η

theorem fibreMass_nonneg (k : ℕ) : 0 ≤ fibreMass N lam h k :=
  Finset.sum_nonneg fun η _ => (cwMeasure_pos N lam h η).le

theorem fibreMass_total :
    ∑ k ∈ Finset.range (N + 1), fibreMass N lam h k = 1 := by
  unfold fibreMass
  rw [Finset.sum_fiberwise_of_maps_to
    (fun η _ => Finset.mem_range.mpr
      (Nat.lt_succ_of_le (countTrue_le N η)))
    (fun η => cwMeasure N lam h η)]
  unfold cwMeasure
  rw [← Finset.sum_div]
  rw [div_eq_one_iff_eq (cwPartition_pos N lam h).ne']
  rfl

/-- The unnormalized fibre weight `C(N,k) e^{λM²/(2N)+hM}`. -/
noncomputable def fibreWeight (N : ℕ) (lam h : ℝ) (k : ℕ) : ℝ :=
  (N.choose k : ℝ) * Real.exp (lam / (2 * (N : ℝ))
    * (2 * (k : ℝ) - N) ^ 2 + h * (2 * (k : ℝ) - N))

theorem fibreWeight_pos (k : ℕ) (hk : k ≤ N) :
    0 < fibreWeight N lam h k := by
  unfold fibreWeight
  have h1 : 0 < N.choose k := Nat.choose_pos hk
  have h2 : (0 : ℝ) < (N.choose k : ℝ) := Nat.cast_pos.mpr h1
  positivity

include hN in
theorem fibreMass_eq_weight_div (k : ℕ) :
    fibreMass N lam h k
      = fibreWeight N lam h k / cwPartition N lam h := by
  unfold fibreMass fibreWeight cwMeasure
  rw [← Finset.sum_div]
  congr 1
  have hw : ∀ η : Fin N → Bool, cwWeight N lam h η
      = Real.exp (lam / (2 * (N : ℝ))
        * (2 * ((countTrue N η : ℕ) : ℝ) - N) ^ 2
        + h * (2 * ((countTrue N η : ℕ) : ℝ) - N)) := by
    intro η
    unfold cwWeight
    rw [magSum_eq_countTrue]
  rw [Finset.sum_congr rfl fun η _ => hw η]
  rw [Finset.sum_congr rfl (fun η hη => by
    rw [(Finset.mem_filter.mp hη).2])]
  rw [Finset.sum_const, card_countTrue_fiber, nsmul_eq_mul]

/-- The field-tilt factorization of the fibre weight. -/
theorem fibreWeight_tilt (k : ℕ) :
    fibreWeight N lam h k
      = fibreWeight N lam 0 k
        * Real.exp (h * (2 * (k : ℝ) - N)) := by
  unfold fibreWeight
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- Zero-field reflection symmetry of fibre weights. -/
theorem fibreWeight_reflect (k : ℕ) (hk : k ≤ N) :
    fibreWeight N lam 0 (N - k) = fibreWeight N lam 0 k := by
  unfold fibreWeight
  rw [Nat.choose_symm hk]
  congr 2
  rw [Nat.cast_sub hk]
  ring

include hN in
/-- The partition function is the total fibre weight. -/
theorem cwPartition_eq_sum_fibreWeight :
    cwPartition N lam h
      = ∑ k ∈ Finset.range (N + 1), fibreWeight N lam h k := by
  have h1 : ∀ k ∈ Finset.range (N + 1),
      fibreMass N lam h k
        = fibreWeight N lam h k / cwPartition N lam h :=
    fun k _ => fibreMass_eq_weight_div hN lam h k
  have h2 := fibreMass_total (N := N) (lam := lam) (h := h)
  rw [Finset.sum_congr rfl h1, ← Finset.sum_div] at h2
  have hZ := cwPartition_pos N lam h
  field_simp at h2
  linarith [h2]

/-- The hypergeometric weight never exceeds one. -/
theorem hypWeight_le_one {N r j k : ℕ} (hjr : j ≤ r) (hrN : r ≤ N)
    (hkN : k ≤ N) : hypWeight N r j k ≤ 1 := by
  rcases lt_or_ge k j with hlt | hjk
  · rw [hypWeight_eq_zero_of_lt hlt]
    norm_num
  · by_cases hwin : r - j ≤ N - k
    · rw [hypWeight_eq_prod hjr hrN hjk hkN]
      have hwinR : (r : ℝ) - j ≤ (N : ℝ) - k := by
        have h1 : ((r - j : ℕ) : ℝ) ≤ ((N - k : ℕ) : ℝ) := by
          exact_mod_cast hwin
        rw [Nat.cast_sub hjr, Nat.cast_sub hkN] at h1
        exact h1
      have hjrR : (j : ℝ) ≤ r := by exact_mod_cast hjr
      have hrNR : (r : ℝ) ≤ N := by exact_mod_cast hrN
      have hjkR : (j : ℝ) ≤ k := by exact_mod_cast hjk
      have hkNR : (k : ℝ) ≤ N := by exact_mod_cast hkN
      have hA : (∏ i ∈ Finset.range j,
          ((k : ℝ) - i) / ((N : ℝ) - i)) ≤ 1 := by
        refine Finset.prod_le_one (fun i hi => ?_) (fun i hi => ?_)
        · have hi' : i < j := Finset.mem_range.mp hi
          have hik : (i : ℝ) < k := by
            exact_mod_cast lt_of_lt_of_le hi' hjk
          have hiN : (i : ℝ) < N := by linarith
          have h2 : (0 : ℝ) < (N : ℝ) - i := by linarith
          have h3 : (0 : ℝ) ≤ (k : ℝ) - i := by linarith
          positivity
        · have hi' : i < j := Finset.mem_range.mp hi
          have hik : (i : ℝ) < k := by
            exact_mod_cast lt_of_lt_of_le hi' hjk
          have hiN : (i : ℝ) < N := by linarith
          rw [div_le_one (by linarith)]
          linarith
      have hB : (∏ i ∈ Finset.range (r - j),
          (((N : ℝ) - k) - i) / (((N : ℝ) - j) - i)) ≤ 1 := by
        refine Finset.prod_le_one (fun i hi => ?_) (fun i hi => ?_)
        · have hi' : i < r - j := Finset.mem_range.mp hi
          have hiR : (i : ℝ) < (r : ℝ) - j := by
            have h4 : ((i : ℕ) : ℝ) < ((r - j : ℕ) : ℝ) := by
              exact_mod_cast hi'
            rwa [Nat.cast_sub hjr] at h4
          have hnum : (0 : ℝ) < ((N : ℝ) - k) - i := by linarith
          have hden : (0 : ℝ) < ((N : ℝ) - j) - i := by linarith
          positivity
        · have hi' : i < r - j := Finset.mem_range.mp hi
          have hiR : (i : ℝ) < (r : ℝ) - j := by
            have h4 : ((i : ℕ) : ℝ) < ((r - j : ℕ) : ℝ) := by
              exact_mod_cast hi'
            rwa [Nat.cast_sub hjr] at h4
          have hden : (0 : ℝ) < ((N : ℝ) - j) - i := by linarith
          rw [div_le_one hden]
          linarith
      have hA0 : (0 : ℝ) ≤ ∏ i ∈ Finset.range j,
          ((k : ℝ) - i) / ((N : ℝ) - i) := by
        refine Finset.prod_nonneg fun i hi => ?_
        have hi' : i < j := Finset.mem_range.mp hi
        have hik : (i : ℝ) < k := by
          exact_mod_cast lt_of_lt_of_le hi' hjk
        have hiN : (i : ℝ) < N := by
          have hkNR : (k : ℝ) ≤ N := by exact_mod_cast hkN
          linarith
        have h2 : (0 : ℝ) < (N : ℝ) - i := by linarith
        have h3 : (0 : ℝ) ≤ (k : ℝ) - i := by linarith
        positivity
      calc (∏ i ∈ Finset.range j, ((k : ℝ) - i) / ((N : ℝ) - i))
            * ∏ i ∈ Finset.range (r - j),
              (((N : ℝ) - k) - i) / (((N : ℝ) - j) - i)
          ≤ 1 * 1 := by
            refine mul_le_mul hA hB ?_ (by norm_num)
            refine Finset.prod_nonneg fun i hi => ?_
            have hi' : i < r - j := Finset.mem_range.mp hi
            have hiR : (i : ℝ) < (r : ℝ) - j := by
              have h4 : ((i : ℕ) : ℝ) < ((r - j : ℕ) : ℝ) := by
                exact_mod_cast hi'
              rwa [Nat.cast_sub hjr] at h4
            have hwinR : (r : ℝ) - j ≤ (N : ℝ) - k := by
              have h5 : ((r - j : ℕ) : ℝ) ≤ ((N - k : ℕ) : ℝ) := by
                exact_mod_cast hwin
              rw [Nat.cast_sub hjr, Nat.cast_sub hkN] at h5
              exact h5
            have hjrR : (j : ℝ) ≤ r := by exact_mod_cast hjr
            have hrNR : (r : ℝ) ≤ N := by exact_mod_cast hrN
            have hnum : (0 : ℝ) < ((N : ℝ) - k) - i := by linarith
            have hden : (0 : ℝ) < ((N : ℝ) - j) - i := by linarith
            positivity
        _ = 1 := one_mul _
    · push_neg at hwin
      rw [show hypWeight N r j k = 0 from by
        unfold hypWeight
        rw [Nat.descFactorial_eq_zero_iff_lt.mpr hwin]
        simp]
      norm_num

end MassFacts

/-! ## The zero-field spectral gap outside the two wells -/

section Gap

open Filter

variable {lam mstar : ℝ}

/-- Outside the two `ε`-wells the zero-field pressure sits a
positive gap below its maximum. -/
theorem cw_gap (hlam : 1 < lam) (hmstar : mstar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : Real.tanh (lam * mstar) = mstar) {ε : ℝ} (hε0 : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ m ∈ Set.Icc (-1 : ℝ) 1,
      ε ≤ |m - mstar| → ε ≤ |m + mstar| →
      cwPressure lam 0 m ≤ cwPressure lam 0 mstar - δ := by
  set K : Set ℝ := Set.Icc (-1 : ℝ) 1 \
    (Set.Ioo (mstar - ε) (mstar + ε)
      ∪ Set.Ioo (-mstar - ε) (-mstar + ε)) with hK_def
  have hKcomp : IsCompact K :=
    isCompact_Icc.diff (IsOpen.union isOpen_Ioo isOpen_Ioo)
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · refine ⟨1, one_pos, fun m hm h1 h2 => ?_⟩
    exfalso
    have hmem : m ∈ K := by
      rw [hK_def]
      refine ⟨hm, ?_⟩
      rintro (hw | hw)
      · have habs : |m - mstar| < ε :=
          abs_lt.mpr ⟨by linarith [hw.1], by linarith [hw.2]⟩
        linarith [habs, h1]
      · have habs : |m + mstar| < ε := by
          rw [abs_lt]
          constructor
          · linarith [hw.1]
          · linarith [hw.2]
        linarith [habs, h2]
    rw [hKe] at hmem
    exact Set.notMem_empty m hmem
  · obtain ⟨xK, hxK, hxKmax⟩ := hKcomp.exists_isMaxOn hKne
      (continuous_cwPressure lam 0).continuousOn
    have hxK_ne : xK ≠ mstar ∧ xK ≠ -mstar := by
      constructor
      · intro hcon
        have := hxK.2
        rw [hcon] at this
        exact this (Or.inl ⟨by linarith, by linarith⟩)
      · intro hcon
        have := hxK.2
        rw [hcon] at this
        exact this (Or.inr ⟨by linarith, by linarith⟩)
    have hgap : cwPressure lam 0 xK < cwPressure lam 0 mstar := by
      rcases lt_or_eq_of_le (cw_phase_supercritical_le hlam hmstar
        hfix hxK.1) with hlt | heq
      · exact hlt
      · exfalso
        rcases (cw_phase_supercritical_eq_iff hlam hmstar hfix
          hxK.1).mp heq with hcon | hcon
        · exact hxK_ne.1 hcon
        · exact hxK_ne.2 hcon
    refine ⟨cwPressure lam 0 mstar - cwPressure lam 0 xK,
      by linarith, fun m hm h1 h2 => ?_⟩
    have hmemK : m ∈ K := by
      rw [hK_def]
      refine ⟨hm, ?_⟩
      rintro (hw | hw)
      · have := abs_lt.mpr
          (⟨by linarith [hw.1], by linarith [hw.2]⟩ :
            -ε < m - mstar ∧ m - mstar < ε)
        linarith [this, h1]
      · have habs : |m + mstar| < ε := by
          rw [abs_lt]
          exact ⟨by linarith [hw.1], by linarith [hw.2]⟩
        linarith [habs, h2]
    have := hxKmax hmemK
    simp only [Set.mem_setOf_eq] at this
    linarith

/-- The field shifts the pressure by at most the field strength. -/
theorem cwPressure_field_close (lam h m : ℝ)
    (hm : m ∈ Set.Icc (-1 : ℝ) 1) :
    |cwPressure lam h m - cwPressure lam 0 m| ≤ |h| := by
  have h1 : cwPressure lam h m - cwPressure lam 0 m = h * m := by
    unfold cwPressure
    ring
  rw [h1, abs_mul]
  have h2 : |m| ≤ 1 := by
    rw [abs_le]
    exact ⟨hm.1, hm.2⟩
  nlinarith [abs_nonneg h, abs_nonneg m]

/-- Polynomially corrected exponential decay. -/
theorem sq_mul_exp_decay {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun N : ℕ => ((N : ℝ) + 1) ^ 2
      * Real.exp (-((N : ℝ) * δ))) atTop (nhds 0) := by
  have hlog := tendsto_log_succ_div
  have hev : ∀ᶠ N : ℕ in atTop,
      ((N : ℝ) + 1) ^ 2 * Real.exp (-((N : ℝ) * δ))
        ≤ Real.exp (-((N : ℝ) * (δ / 2))) := by
    obtain ⟨N₀, hN₀⟩ := (Metric.tendsto_atTop.mp hlog) (δ / 4)
      (by linarith)
    filter_upwards [eventually_ge_atTop (max N₀ 1)] with N hN
    have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
    have hN0' : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
    have h1 := hN₀ N (le_trans (le_max_left _ _) hN)
    rw [Real.dist_eq, sub_zero] at h1
    have hlogN : Real.log ((N : ℝ) + 1) ≤ (N : ℝ) * (δ / 4) := by
      have h2 := le_of_lt (lt_of_abs_lt h1)
      rw [div_le_iff₀ hN0'] at h2
      linarith
    have hsq : ((N : ℝ) + 1) ^ 2
        = Real.exp (2 * Real.log ((N : ℝ) + 1)) := by
      rw [show (2 : ℝ) * Real.log ((N : ℝ) + 1)
          = Real.log (((N : ℝ) + 1) ^ 2) from by
        rw [Real.log_pow]
        push_cast
        ring]
      rw [Real.exp_log (by positivity)]
    rw [hsq, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    linarith
  have hexp : Tendsto (fun N : ℕ =>
      Real.exp (-((N : ℝ) * (δ / 2)))) atTop (nhds 0) := by
    have h3 : ∀ N : ℕ, Real.exp (-((N : ℝ) * (δ / 2)))
        = Real.exp (-(δ / 2)) ^ N := by
      intro N
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [show (fun N : ℕ => Real.exp (-((N : ℝ) * (δ / 2))))
        = fun N : ℕ => Real.exp (-(δ / 2)) ^ N from
      funext h3]
    refine tendsto_pow_atTop_nhds_zero_of_lt_one
      (Real.exp_pos _).le ?_
    rw [Real.exp_lt_one_iff]
    linarith
  refine squeeze_zero' ?_ hev hexp
  filter_upwards with N
  positivity

end Gap

/-! ## Decay of the off-well mass -/

section RestDecay

open Filter

/-- Fibre-mass sums over a predicate agree with the configuration
sums bounded by the large-deviation estimates. -/
theorem sum_fibreMass_filter {N : ℕ} (lam h : ℝ)
    (P : ℕ → Prop) [DecidablePred P] :
    ∑ k ∈ (Finset.range (N + 1)).filter P, fibreMass N lam h k
      = ∑ η ∈ Finset.univ.filter
          (fun η : Fin N → Bool => P (countTrue N η)),
        cwMeasure N lam h η := by
  unfold fibreMass
  conv_lhs => rw [Finset.sum_filter]
  conv_rhs => rw [Finset.sum_filter]
  rw [← Finset.sum_fiberwise_of_maps_to
    (g := countTrue N) (t := Finset.range (N + 1))
    (fun η _ => Finset.mem_range.mpr
      (Nat.lt_succ_of_le (countTrue_le N η)))
    (fun η => if P (countTrue N η) then cwMeasure N lam h η
      else 0)]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hP : P k
  · rw [if_pos hP]
    refine Finset.sum_congr rfl fun η hη => ?_
    rw [if_pos]
    rw [(Finset.mem_filter.mp hη).2]
    exact hP
  · rw [if_neg hP]
    symm
    refine Finset.sum_eq_zero
      (f := fun η => if P (countTrue N η)
        then cwMeasure N lam h η else 0)
      fun η hη => ?_
    rw [if_neg]
    rw [(Finset.mem_filter.mp hη).2]
    exact hP

variable {lam mstar : ℝ}

/-- **Off-well mass decay**: along any field sequence with `N h_N`
bounded, the mass outside the two `ε`-wells vanishes. -/
theorem cw_rest_decay (hlam : 1 < lam)
    (hmstar : mstar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : Real.tanh (lam * mstar) = mstar)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < mstar)
    (hseq : ℕ → ℝ) (c : ℝ)
    (hc : Tendsto (fun N : ℕ => (N : ℝ) * hseq N) atTop (nhds c)) :
    Tendsto (fun N : ℕ =>
      ∑ k ∈ (Finset.range (N + 1)).filter (fun k =>
        ¬(|mGrid N k - mstar| < ε ∨ |mGrid N k + mstar| < ε)),
        fibreMass N lam (hseq N) k) atTop (nhds 0) := by
  obtain ⟨δ, hδ0, hδ⟩ := cw_gap hlam hmstar hfix (ε := ε) hε0
  -- the zero-field maximizer at `mstar`
  have hmemStar : mstar ∈ Set.Icc (-1 : ℝ) 1 :=
    ⟨by linarith [hmstar.1], hmstar.2.le⟩
  -- uniform continuity modulus for the zero-field pressure
  have hucont : UniformContinuousOn (cwPressure lam 0)
      (Set.Icc (-1 : ℝ) 1) :=
    isCompact_Icc.uniformContinuousOn_of_continuous
      (continuous_cwPressure lam 0).continuousOn
  obtain ⟨γ, hγ0, hγ⟩ := Metric.uniformContinuousOn_iff.mp hucont
    (δ / 4) (by linarith)
  -- eventual bound
  have hev : ∀ᶠ N : ℕ in atTop,
      ∑ k ∈ (Finset.range (N + 1)).filter (fun k =>
        ¬(|mGrid N k - mstar| < ε ∨ |mGrid N k + mstar| < ε)),
        fibreMass N lam (hseq N) k
      ≤ ((N : ℝ) + 1) ^ 2 * Real.exp (-((N : ℝ) * (δ / 2))) := by
    obtain ⟨Nc, hNc⟩ := (Metric.tendsto_atTop.mp hc) 1 one_pos
    obtain ⟨Nm, hNm⟩ := exists_nat_gt (2 / γ)
    obtain ⟨Nd, hNd⟩ := exists_nat_gt (8 * (|c| + 1) / δ)
    filter_upwards [eventually_ge_atTop
      (max (max Nc Nm) (max Nd 1))] with N hNge
    have hNc' : Nc ≤ N := le_trans (le_max_left _ _)
      (le_trans (le_max_left _ _) hNge)
    have hNm' : Nm ≤ N := le_trans (le_max_right _ _)
      (le_trans (le_max_left _ _) hNge)
    have hNd' : Nd ≤ N := le_trans (le_max_left _ _)
      (le_trans (le_max_right _ _) hNge)
    have hNpos : 0 < N := Nat.lt_of_lt_of_le Nat.zero_lt_one
      (le_trans (le_max_right _ _)
        (le_trans (le_max_right _ _) hNge))
    have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hNpos
    -- field control
    have hcN := hNc N hNc'
    rw [Real.dist_eq] at hcN
    have hcbound : |(N : ℝ) * hseq N| ≤ |c| + 1 := by
      have := abs_sub_abs_le_abs_sub ((N : ℝ) * hseq N) c
      linarith [le_of_lt hcN]
    have hhabs : |hseq N| ≤ (|c| + 1) / N := by
      rw [le_div_iff₀ hN']
      calc |hseq N| * N = |(N : ℝ) * hseq N| := by
            rw [abs_mul, Nat.abs_cast]
            ring
        _ ≤ |c| + 1 := hcbound
    -- reference grid point near mstar
    set k₀ : ℕ := ⌊(1 + mstar) / 2 * N⌋₊ with hk₀_def
    have hhalf0 : (0 : ℝ) ≤ (1 + mstar) / 2 := by
      have := hmemStar.1
      linarith
    have hk₀N : k₀ ≤ N := by
      rw [hk₀_def]
      refine Nat.floor_le_of_le ?_
      have h6 : (1 + mstar) / 2 ≤ 1 := by
        have := hmemStar.2
        linarith
      calc (1 + mstar) / 2 * (N : ℝ) ≤ 1 * N := by nlinarith
        _ = (N : ℝ) := one_mul _
    have hgrid_close : |mGrid N k₀ - mstar| ≤ 2 / N := by
      have hkfloor : (1 + mstar) / 2 * (N : ℝ) - 1 < (k₀ : ℝ) := by
        rw [hk₀_def]
        exact Nat.sub_one_lt_floor _
      have hkfloor2 : (k₀ : ℝ) ≤ (1 + mstar) / 2 * N := by
        rw [hk₀_def]
        exact Nat.floor_le (by positivity)
      unfold mGrid
      have heq : (2 * (k₀ : ℝ) - N) / N - mstar
          = (2 * (k₀ : ℝ) - N - mstar * N) / N := by
        field_simp
      rw [abs_le, heq]
      constructor
      · rw [neg_le, ← neg_div]
        refine (div_le_div_iff_of_pos_right hN').mpr ?_
        nlinarith [hkfloor2]
      · refine (div_le_div_iff_of_pos_right hN').mpr ?_
        nlinarith [hkfloor]
    have hmesh : (2 : ℝ) / N < γ := by
      rw [div_lt_iff₀ hN']
      have h6 : (2 : ℝ) / γ < Nm := hNm
      have h7 : (Nm : ℝ) ≤ N := Nat.cast_le.mpr hNm'
      rw [div_lt_iff₀ hγ0] at h6
      nlinarith
    have hΨk₀ : cwPressure lam 0 mstar - δ / 4
        ≤ cwPressure lam 0 (mGrid N k₀) := by
      have h8 := hγ (mGrid N k₀) (mGrid_mem hNpos hk₀N) mstar hmemStar
        (by
          rw [Real.dist_eq]
          exact lt_of_le_of_lt hgrid_close hmesh)
      rw [Real.dist_eq] at h8
      have := abs_lt.mp h8
      linarith [this.1]
    -- large-deviation bound with the gap level
    have hldp := cw_ldp_upper hNpos lam (hseq N)
      (fun k => ¬(|mGrid N k - mstar| < ε
        ∨ |mGrid N k + mstar| < ε))
      (cwPressure lam 0 mstar - δ + |hseq N|)
      (fun k hk hP => by
        rw [not_or] at hP
        have h9 := hδ (mGrid N k) (mGrid_mem hNpos hk)
          (not_lt.mp hP.1) (not_lt.mp hP.2)
        have h10 := cwPressure_field_close lam (hseq N)
          (mGrid N k) (mGrid_mem hNpos hk)
        have h11 := abs_le.mp h10
        linarith [h11.2])
      k₀ hk₀N
    rw [sum_fibreMass_filter lam (hseq N) _]
    refine le_trans hldp ?_
    have hΨh : cwPressure lam 0 (mGrid N k₀) - |hseq N|
        ≤ cwPressure lam (hseq N) (mGrid N k₀) := by
      have h10 := cwPressure_field_close lam (hseq N)
        (mGrid N k₀) (mGrid_mem hNpos hk₀N)
      have h11 := abs_le.mp h10
      linarith [h11.1]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine Real.exp_le_exp.mpr ?_
    have hNh : (N : ℝ) * |hseq N| ≤ |c| + 1 := by
      have h12 := hhabs
      rw [le_div_iff₀ hN'] at h12
      linarith [h12]
    have hNd'' : 8 * (|c| + 1) / δ < (N : ℝ) := by
      have h11 : ((Nd : ℕ) : ℝ) ≤ N := Nat.cast_le.mpr hNd'
      linarith [hNd]
    have hNδ : 2 * (|c| + 1) ≤ (N : ℝ) * (δ / 4) := by
      rw [div_lt_iff₀ hδ0] at hNd''
      nlinarith [abs_nonneg c]
    have h12 : (cwPressure lam 0 mstar - δ + |hseq N|)
        - cwPressure lam (hseq N) (mGrid N k₀)
        ≤ -(3 * δ / 4) + 2 * |hseq N| := by
      linarith [hΨh, hΨk₀]
    have h13 : (N : ℝ) * ((cwPressure lam 0 mstar - δ + |hseq N|)
        - cwPressure lam (hseq N) (mGrid N k₀))
        ≤ (N : ℝ) * (-(3 * δ / 4) + 2 * |hseq N|) :=
      mul_le_mul_of_nonneg_left h12 hN'.le
    have h14 : (N : ℝ) * (-(3 * δ / 4) + 2 * |hseq N|)
        = -(3 * ((N : ℝ) * δ) / 4)
          + 2 * ((N : ℝ) * |hseq N|) := by
      ring
    rw [h14] at h13
    have h15 : 2 * ((N : ℝ) * |hseq N|) ≤ 2 * (|c| + 1) := by
      linarith [hNh]
    have h16 : -(3 * ((N : ℝ) * δ) / 4) + 2 * (|c| + 1)
        ≤ -((N : ℝ) * (δ / 2)) := by
      have h17 : 2 * (|c| + 1) ≤ (N : ℝ) * δ / 4 := by
        linarith [hNδ]
      linarith
    linarith [h13, h15, h16]
  refine squeeze_zero' ?_ hev
    (sq_mul_exp_decay (by linarith : (0 : ℝ) < δ / 2))
  filter_upwards with N
  exact Finset.sum_nonneg fun k _ =>
    fibreMass_nonneg lam (hseq N) k

end RestDecay

/-! ## The two-well fraction sandwich -/

section Sandwich2

set_option maxHeartbeats 800000 in
-- heavy fraction algebra
/-- If the two well masses are `e^{±u}`-tilted copies of `S·a` and
`S·b` and the remainder is a `ρ`-fraction of the total, the
first-well fraction is within `(e^{2u}−1) + ρ` of `a/(a+b)`. -/
theorem well_fraction_bound {Tp Tm R S a b u ρ : ℝ}
    (hS : 0 < S) (ha : 0 < a) (hb : 0 < b) (hu : 0 ≤ u)
    (hρ0 : 0 ≤ ρ)
    (hTp1 : S * (a * Real.exp (-u)) ≤ Tp)
    (hTp2 : Tp ≤ S * (a * Real.exp u))
    (hTm1 : S * (b * Real.exp (-u)) ≤ Tm)
    (hTm2 : Tm ≤ S * (b * Real.exp u))
    (hR0 : 0 ≤ R)
    (hRρ : R ≤ ρ * (Tp + Tm + R)) :
    |Tp / (Tp + Tm + R) - a / (a + b)|
      ≤ (Real.exp (2 * u) - 1) + ρ := by
  have hTp0 : 0 < Tp := lt_of_lt_of_le (by positivity) hTp1
  have hTm0 : 0 < Tm := lt_of_lt_of_le (by positivity) hTm1
  have hZ0 : 0 < Tp + Tm + R := by linarith
  have hab : 0 < a + b := by linarith
  have hu2 : (1 : ℝ) ≤ Real.exp (2 * u) := by
    rw [show (1 : ℝ) = Real.exp 0 from Real.exp_zero.symm]
    exact Real.exp_le_exp.mpr (by linarith)
  have huu : Real.exp u * Real.exp (-u) = 1 := by
    rw [← Real.exp_add]
    norm_num
  have hprod : Real.exp (2 * u) * Real.exp (-(2 * u)) = 1 := by
    rw [← Real.exp_add]
    norm_num
  have he2u : (0 : ℝ) < Real.exp (-(2 * u)) := Real.exp_pos _
  have he2u' : (0 : ℝ) < Real.exp (2 * u) := Real.exp_pos _
  have hE1 : 1 - Real.exp (-(2 * u)) ≤ Real.exp (2 * u) - 1 := by
    nlinarith [hu2, hprod, he2u]
  rcases le_or_gt 1 ρ with hρ1 | hρ1
  · have hx0 : (0 : ℝ) ≤ Tp / (Tp + Tm + R) := by positivity
    have hx1 : Tp / (Tp + Tm + R) ≤ 1 := by
      rw [div_le_one hZ0]
      linarith
    have hw0 : (0 : ℝ) ≤ a / (a + b) := by positivity
    have hw1 : a / (a + b) ≤ 1 := by
      rw [div_le_one hab]
      linarith
    rw [abs_le]
    constructor <;> nlinarith [hu2]
  · have hsplit : Real.exp (-(2 * u))
        = Real.exp (-u) * Real.exp (-u) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hsplit2 : Real.exp (2 * u) = Real.exp u * Real.exp u := by
      rw [← Real.exp_add]
      congr 1
      ring
    -- upper bound
    have hup : Tp / (Tp + Tm + R)
        ≤ a / (a + b) + (Real.exp (2 * u) - 1) := by
      have h1 : Tp / (Tp + Tm + R) ≤ Tp / (Tp + Tm) := by
        rw [div_le_div_iff₀ hZ0 (by linarith)]
        nlinarith
      have h2 : Tp / (Tp + Tm)
          ≤ a / (a + b * Real.exp (-(2 * u))) := by
        rw [div_le_div_iff₀ (by linarith) (by positivity)]
        have hkey : Tp * (b * Real.exp (-(2 * u))) ≤ a * Tm := by
          calc Tp * (b * Real.exp (-(2 * u)))
              ≤ (S * (a * Real.exp u))
                * (b * Real.exp (-(2 * u))) :=
                mul_le_mul_of_nonneg_right hTp2 (by positivity)
            _ = a * (S * (b * Real.exp (-u))) := by
                rw [hsplit]
                linear_combination
                  (S * a * b * Real.exp (-u)) * huu
            _ ≤ a * Tm := mul_le_mul_of_nonneg_left hTm1 ha.le
        nlinarith [hkey]
      have h3 : a / (a + b * Real.exp (-(2 * u))) - a / (a + b)
          ≤ Real.exp (2 * u) - 1 := by
        rw [div_sub_div _ _ (by positivity) hab.ne']
        rw [div_le_iff₀ (by positivity)]
        have h4 : a * (a + b) - (a + b * Real.exp (-(2 * u))) * a
            = a * b * (1 - Real.exp (-(2 * u))) := by
          ring
        rw [h4]
        have hD : a * b
            ≤ (a + b * Real.exp (-(2 * u))) * (a + b) := by
          nlinarith [he2u, mul_pos ha hb, sq_nonneg a,
            mul_pos (mul_pos ha hb) he2u,
            mul_pos (mul_pos hb hb) he2u]
        have hEnn : (0 : ℝ) ≤ Real.exp (2 * u) - 1 := by
          linarith [hu2]
        have hstage1 : a * b * (1 - Real.exp (-(2 * u)))
            ≤ a * b * (Real.exp (2 * u) - 1) :=
          mul_le_mul_of_nonneg_left hE1 (by positivity)
        have hstage2 : a * b * (Real.exp (2 * u) - 1)
            ≤ ((a + b * Real.exp (-(2 * u))) * (a + b))
              * (Real.exp (2 * u) - 1) :=
          mul_le_mul_of_nonneg_right hD hEnn
        nlinarith [hstage1, hstage2]
      linarith [h1, h2, h3]
    -- lower bound
    have hlo : a / (a + b) - (Real.exp (2 * u) - 1) - ρ
        ≤ Tp / (Tp + Tm + R) := by
      have hZle : (1 - ρ) * (Tp + Tm + R) ≤ Tp + Tm := by
        linarith [hRρ]
      have h1 : ((1 - ρ) * Tp) / (Tp + Tm)
          ≤ Tp / (Tp + Tm + R) := by
        rw [div_le_div_iff₀ (by linarith) hZ0]
        nlinarith [hZle, hTp0.le]
      have h2 : a / (a + b * Real.exp (2 * u))
          ≤ Tp / (Tp + Tm) := by
        rw [div_le_div_iff₀ (by positivity) (by linarith)]
        have hkey : a * Tm ≤ Tp * (b * Real.exp (2 * u)) := by
          calc a * Tm ≤ a * (S * (b * Real.exp u)) :=
                mul_le_mul_of_nonneg_left hTm2 ha.le
            _ = (S * (a * Real.exp (-u)))
                * (b * Real.exp (2 * u)) := by
                rw [hsplit2]
                linear_combination
                  (-(S * a * b * Real.exp u)) * huu
            _ ≤ Tp * (b * Real.exp (2 * u)) :=
                mul_le_mul_of_nonneg_right hTp1 (by positivity)
        nlinarith [hkey]
      have h3 : a / (a + b) - (Real.exp (2 * u) - 1)
          ≤ a / (a + b * Real.exp (2 * u)) := by
        rw [sub_le_iff_le_add]
        rw [show a / (a + b * Real.exp (2 * u))
            + (Real.exp (2 * u) - 1)
            = a / (a + b * Real.exp (2 * u))
              + (Real.exp (2 * u) - 1) from rfl]
        have h5 : a / (a + b) - a / (a + b * Real.exp (2 * u))
            ≤ Real.exp (2 * u) - 1 := by
          rw [div_sub_div _ _ hab.ne' (by positivity)]
          rw [div_le_iff₀ (by positivity)]
          have h6 : a * (a + b * Real.exp (2 * u)) - (a + b) * a
              = a * b * (Real.exp (2 * u) - 1) := by
            ring
          rw [h6]
          have hD : a * b
              ≤ (a + b) * (a + b * Real.exp (2 * u)) := by
            nlinarith [he2u', mul_pos ha hb, sq_nonneg a,
              mul_pos (mul_pos ha hb) he2u',
              mul_pos (mul_pos hb hb) he2u']
          have hEnn : (0 : ℝ) ≤ Real.exp (2 * u) - 1 := by
            linarith [hu2]
          have hstage1 : a * b * (Real.exp (2 * u) - 1)
              ≤ ((a + b) * (a + b * Real.exp (2 * u)))
                * (Real.exp (2 * u) - 1) :=
            mul_le_mul_of_nonneg_right hD hEnn
          nlinarith [hstage1]
        linarith
      have hwE : a / (a + b) - (Real.exp (2 * u) - 1) ≤ 1 := by
        have h7 : a / (a + b) ≤ 1 := by
          rw [div_le_one hab]
          linarith
        linarith [hu2]
      have h4 : a / (a + b) - (Real.exp (2 * u) - 1) - ρ
          ≤ (1 - ρ) * (a / (a + b) - (Real.exp (2 * u) - 1)) := by
        have hprod4 : 0 ≤ ρ
            * (1 - (a / (a + b) - (Real.exp (2 * u) - 1))) :=
          mul_nonneg hρ0 (by linarith [hwE])
        nlinarith [hprod4]
      have h8 : (1 - ρ) * (a / (a + b) - (Real.exp (2 * u) - 1))
          ≤ (1 - ρ) * (Tp / (Tp + Tm)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by linarith)
        linarith [h2, h3]
      calc a / (a + b) - (Real.exp (2 * u) - 1) - ρ
          ≤ (1 - ρ) * (a / (a + b) - (Real.exp (2 * u) - 1)) := h4
        _ ≤ (1 - ρ) * (Tp / (Tp + Tm)) := h8
        _ = ((1 - ρ) * Tp) / (Tp + Tm) := by ring
        _ ≤ Tp / (Tp + Tm + R) := h1
    rw [abs_le]
    constructor
    · linarith [hlo]
    · linarith [hup, hρ0]

end Sandwich2

/-! ## The well masses -/

section WellMass

variable {lam mstar : ℝ}

/-- The reflection `k ↦ N − k` negates the magnetization grid. -/
theorem mGrid_reflect {N k : ℕ} (hk : k ≤ N) :
    mGrid N (N - k) = -(mGrid N k) := by
  unfold mGrid
  rw [Nat.cast_sub hk]
  by_cases hN : (N : ℝ) = 0
  · rw [hN]
    norm_num
  · field_simp
    ring

/-- `(2k − N) = N · m_k`. -/
theorem mag_eq_mGrid {N k : ℕ} (hN : 0 < N) :
    2 * (k : ℝ) - N = (N : ℝ) * mGrid N k := by
  unfold mGrid
  have hN' : ((N : ℝ)) ≠ 0 := (Nat.cast_pos.mpr hN).ne'
  field_simp

/-- **Well-mass estimate**: at field `h`, if the tilt exponent is
within `u` of `±c·m⋆` on the respective wells, the `+`-well mass is
within `(e^{2u}−1) + ρ` of `e^{cm⋆}/(2cosh(cm⋆))`, where `ρ` is the
off-well mass. -/
theorem cw_well_mass_bound
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < mstar)
    (hmstar : mstar ∈ Set.Ioo (0 : ℝ) 1)
    {N : ℕ} (hN : 0 < N) (h c u : ℝ) (hu0 : 0 ≤ u)
    (hmesh : 2 / (N : ℝ) < ε)
    (htp : ∀ k ≤ N, |mGrid N k - mstar| < ε →
      |h * (2 * (k : ℝ) - N) - c * mstar| ≤ u)
    (htm : ∀ k ≤ N, |mGrid N k + mstar| < ε →
      |h * (2 * (k : ℝ) - N) + c * mstar| ≤ u) :
    |(∑ k ∈ (Finset.range (N + 1)).filter
        (fun k => |mGrid N k - mstar| < ε),
        fibreMass N lam h k)
      - Real.exp (c * mstar) / (Real.exp (c * mstar)
        + Real.exp (-(c * mstar)))|
    ≤ (Real.exp (2 * u) - 1)
      + ∑ k ∈ (Finset.range (N + 1)).filter (fun k =>
          ¬(|mGrid N k - mstar| < ε ∨ |mGrid N k + mstar| < ε)),
        fibreMass N lam h k := by
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hZ := cwPartition_pos N lam h
  set Pp : ℕ → Prop := fun k => |mGrid N k - mstar| < ε with hPp
  set Pm : ℕ → Prop := fun k => |mGrid N k + mstar| < ε with hPm
  set Wp := (Finset.range (N + 1)).filter Pp with hWp
  set Wm := (Finset.range (N + 1)).filter Pm with hWm
  set Wr := (Finset.range (N + 1)).filter
    (fun k => ¬(Pp k ∨ Pm k)) with hWr
  set Tp := ∑ k ∈ Wp, fibreWeight N lam h k with hTp
  set Tm := ∑ k ∈ Wm, fibreWeight N lam h k with hTm
  set R := ∑ k ∈ Wr, fibreWeight N lam h k with hR
  set S := ∑ k ∈ Wp, fibreWeight N lam 0 k with hS
  -- the wells are disjoint and partition with the rest
  have hdisj : ∀ k, ¬(Pp k ∧ Pm k) := by
    intro k ⟨h1, h2⟩
    rw [hPp] at h1
    rw [hPm] at h2
    have h3 := abs_lt.mp h1
    have h4 := abs_lt.mp h2
    linarith [h3.1, h4.2, hmstar.1]
  have hWm_eq : ((Finset.range (N + 1)).filter
      (fun k => ¬Pp k)).filter Pm = Wm := by
    rw [hWm, Finset.filter_filter]
    refine Finset.filter_congr fun k hk => ?_
    constructor
    · intro h5
      exact h5.2
    · intro h5
      exact ⟨fun h6 => hdisj k ⟨h6, h5⟩, h5⟩
  have hWr_eq : ((Finset.range (N + 1)).filter
      (fun k => ¬Pp k)).filter (fun k => ¬Pm k) = Wr := by
    rw [hWr, Finset.filter_filter]
    refine Finset.filter_congr fun k hk => ?_
    constructor
    · intro h5
      rw [not_or]
      exact ⟨h5.1, h5.2⟩
    · intro h5
      rw [not_or] at h5
      exact ⟨h5.1, h5.2⟩
  have hZsum : cwPartition N lam h = Tp + Tm + R := by
    rw [cwPartition_eq_sum_fibreWeight hN lam h]
    have hsplit1 := Finset.sum_filter_add_sum_filter_not
      (Finset.range (N + 1)) Pp (fibreWeight N lam h)
    have hsplit2 := Finset.sum_filter_add_sum_filter_not
      ((Finset.range (N + 1)).filter (fun k => ¬Pp k)) Pm
      (fibreWeight N lam h)
    rw [hWm_eq, hWr_eq] at hsplit2
    rw [hTp, hTm, hR, hWp]
    linarith [hsplit1, hsplit2]
  -- reflection: the zero-field well weights agree
  have hreflect : ∑ k ∈ Wm, fibreWeight N lam 0 k = S := by
    rw [hS, hWm, hWp]
    refine Finset.sum_nbij' (fun k => N - k) (fun k => N - k)
      ?_ ?_ ?_ ?_ ?_
    · intro k hk
      have hk1 := Finset.mem_filter.mp hk
      have hkN : k ≤ N := Nat.lt_succ_iff.mp
        (Finset.mem_range.mp hk1.1)
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
        (by omega), ?_⟩
      simp only [hPp]
      rw [mGrid_reflect hkN]
      have h5 := hk1.2
      simp only [hPm] at h5
      rw [show -(mGrid N k) - mstar = -(mGrid N k + mstar) from by
        ring, abs_neg]
      exact h5
    · intro k hk
      have hk1 := Finset.mem_filter.mp hk
      have hkN : k ≤ N := Nat.lt_succ_iff.mp
        (Finset.mem_range.mp hk1.1)
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
        (by omega), ?_⟩
      simp only [hPm]
      rw [mGrid_reflect hkN]
      have h5 := hk1.2
      simp only [hPp] at h5
      rw [show -(mGrid N k) + mstar = -(mGrid N k - mstar) from by
        ring, abs_neg]
      exact h5
    · intro k hk
      have hkN : k ≤ N := Nat.lt_succ_iff.mp
        (Finset.mem_range.mp (Finset.mem_filter.mp hk).1)
      omega
    · intro k hk
      have hkN : k ≤ N := Nat.lt_succ_iff.mp
        (Finset.mem_range.mp (Finset.mem_filter.mp hk).1)
      omega
    · intro k hk
      have hkN : k ≤ N := Nat.lt_succ_iff.mp
        (Finset.mem_range.mp (Finset.mem_filter.mp hk).1)
      exact (fibreWeight_reflect lam k hkN).symm
  -- the positive well contains the reference grid point
  have hSpos : 0 < S := by
    set k₀ : ℕ := ⌊(1 + mstar) / 2 * N⌋₊ with hk₀_def
    have hhalf0 : (0 : ℝ) ≤ (1 + mstar) / 2 := by
      have := hmstar.1
      linarith
    have hk₀N : k₀ ≤ N := by
      rw [hk₀_def]
      refine Nat.floor_le_of_le ?_
      have h6 : (1 + mstar) / 2 ≤ 1 := by
        have := hmstar.2
        linarith
      calc (1 + mstar) / 2 * (N : ℝ) ≤ 1 * N := by nlinarith
        _ = (N : ℝ) := one_mul _
    have hgrid_close : |mGrid N k₀ - mstar| ≤ 2 / N := by
      have hkfloor : (1 + mstar) / 2 * (N : ℝ) - 1 < (k₀ : ℝ) := by
        rw [hk₀_def]
        exact Nat.sub_one_lt_floor _
      have hkfloor2 : (k₀ : ℝ) ≤ (1 + mstar) / 2 * N := by
        rw [hk₀_def]
        exact Nat.floor_le (by positivity)
      unfold mGrid
      have heq : (2 * (k₀ : ℝ) - N) / N - mstar
          = (2 * (k₀ : ℝ) - N - mstar * N) / N := by
        field_simp
      rw [abs_le, heq]
      constructor
      · rw [neg_le, ← neg_div]
        refine (div_le_div_iff_of_pos_right hN').mpr ?_
        nlinarith [hkfloor2]
      · refine (div_le_div_iff_of_pos_right hN').mpr ?_
        nlinarith [hkfloor]
    have hk₀mem : k₀ ∈ Wp := by
      rw [hWp]
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
        (by omega), ?_⟩
      simp only [hPp]
      exact lt_of_le_of_lt hgrid_close hmesh
    rw [hS]
    refine Finset.sum_pos' (fun k hk => ?_) ⟨k₀, hk₀mem, ?_⟩
    · exact (fibreWeight_pos lam 0 k (Nat.lt_succ_iff.mp
        (Finset.mem_range.mp (Finset.mem_filter.mp hk).1))).le
    · exact fibreWeight_pos lam 0 k₀ hk₀N
  -- tilt sandwiches
  have hexp_a : ∀ y x : ℝ, |x - y| ≤ u →
      Real.exp y * Real.exp (-u) ≤ Real.exp x
        ∧ Real.exp x ≤ Real.exp y * Real.exp u := by
    intro y x hx
    have h7 := abs_le.mp hx
    constructor
    · rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith [h7.1])
    · rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith [h7.2])
  have hTp_bounds : S * (Real.exp (c * mstar) * Real.exp (-u)) ≤ Tp
      ∧ Tp ≤ S * (Real.exp (c * mstar) * Real.exp u) := by
    constructor
    · rw [hS, hTp, Finset.sum_mul]
      refine Finset.sum_le_sum fun k hk => ?_
      have hk1 := Finset.mem_filter.mp hk
      have hkN : k ≤ N := Nat.lt_succ_iff.mp
        (Finset.mem_range.mp hk1.1)
      have h8 := htp k hkN (by simp only [hPp] at hk1; exact hk1.2)
      have h9 := (hexp_a (c * mstar) _ h8).1
      conv_rhs => rw [fibreWeight_tilt]
      have h10 := (fibreWeight_pos lam 0 k hkN).le
      exact mul_le_mul_of_nonneg_left h9 h10
    · rw [hS, hTp, Finset.sum_mul]
      refine Finset.sum_le_sum fun k hk => ?_
      have hk1 := Finset.mem_filter.mp hk
      have hkN : k ≤ N := Nat.lt_succ_iff.mp
        (Finset.mem_range.mp hk1.1)
      have h8 := htp k hkN (by simp only [hPp] at hk1; exact hk1.2)
      have h9 := (hexp_a (c * mstar) _ h8).2
      conv_lhs => rw [fibreWeight_tilt]
      have h10 := (fibreWeight_pos lam 0 k hkN).le
      exact mul_le_mul_of_nonneg_left h9 h10
  have hTm_bounds : S * (Real.exp (-(c * mstar)) * Real.exp (-u))
      ≤ Tm ∧ Tm ≤ S * (Real.exp (-(c * mstar)) * Real.exp u) := by
    constructor
    · rw [← hreflect, hTm, Finset.sum_mul]
      refine Finset.sum_le_sum fun k hk => ?_
      have hk1 := Finset.mem_filter.mp hk
      have hkN : k ≤ N := Nat.lt_succ_iff.mp
        (Finset.mem_range.mp hk1.1)
      have h8 := htm k hkN (by simp only [hPm] at hk1; exact hk1.2)
      have h8' : |h * (2 * (k : ℝ) - N) - (-(c * mstar))| ≤ u := by
        rw [show h * (2 * (k : ℝ) - N) - (-(c * mstar))
            = h * (2 * (k : ℝ) - N) + c * mstar from by ring]
        exact h8
      have h9 := (hexp_a (-(c * mstar)) _ h8').1
      conv_rhs => rw [fibreWeight_tilt]
      have h10 := (fibreWeight_pos lam 0 k hkN).le
      exact mul_le_mul_of_nonneg_left h9 h10
    · rw [← hreflect, hTm, Finset.sum_mul]
      refine Finset.sum_le_sum fun k hk => ?_
      have hk1 := Finset.mem_filter.mp hk
      have hkN : k ≤ N := Nat.lt_succ_iff.mp
        (Finset.mem_range.mp hk1.1)
      have h8 := htm k hkN (by simp only [hPm] at hk1; exact hk1.2)
      have h8' : |h * (2 * (k : ℝ) - N) - (-(c * mstar))| ≤ u := by
        rw [show h * (2 * (k : ℝ) - N) - (-(c * mstar))
            = h * (2 * (k : ℝ) - N) + c * mstar from by ring]
        exact h8
      have h9 := (hexp_a (-(c * mstar)) _ h8').2
      conv_lhs => rw [fibreWeight_tilt]
      have h10 := (fibreWeight_pos lam 0 k hkN).le
      exact mul_le_mul_of_nonneg_left h9 h10
  have hR0 : 0 ≤ R := by
    rw [hR]
    refine Finset.sum_nonneg fun k hk => ?_
    exact (fibreWeight_pos lam h k (Nat.lt_succ_iff.mp
      (Finset.mem_range.mp (Finset.mem_filter.mp hk).1))).le
  -- the rest mass ratio
  set ρ := ∑ k ∈ Wr, fibreMass N lam h k with hρ
  have hρ_eq : R = ρ * (Tp + Tm + R) := by
    rw [hρ, hR]
    rw [Finset.sum_congr rfl fun k hk =>
      fibreMass_eq_weight_div hN lam h k]
    rw [← Finset.sum_div, ← hZsum]
    field_simp [hZ.ne']
  -- assemble via the fraction sandwich
  have hmass : ∑ k ∈ Wp, fibreMass N lam h k
      = Tp / (Tp + Tm + R) := by
    rw [Finset.sum_congr rfl fun k hk =>
      fibreMass_eq_weight_div hN lam h k]
    rw [← Finset.sum_div, ← hZsum, hTp]
  rw [hmass]
  have hρ0 : 0 ≤ ρ := by
    rw [hρ]
    exact Finset.sum_nonneg fun k _ => fibreMass_nonneg lam h k
  exact well_fraction_bound hSpos (Real.exp_pos _)
    (Real.exp_pos _) hu0 hρ0
    hTp_bounds.1 hTp_bounds.2 hTm_bounds.1 hTm_bounds.2
    hR0 hρ_eq.le

end WellMass

/-! ## Weak convergence of the magnetization -/

section WeakConv

open Filter

/-- Splitting a fibre sum into the two wells and the rest. -/
theorem sum_split_wells {N : ℕ} {mstar ε : ℝ}
    (hdisj : ∀ k, ¬(|mGrid N k - mstar| < ε
      ∧ |mGrid N k + mstar| < ε)) (f : ℕ → ℝ) :
    ∑ k ∈ Finset.range (N + 1), f k
      = (∑ k ∈ (Finset.range (N + 1)).filter
          (fun k => |mGrid N k - mstar| < ε), f k)
        + (∑ k ∈ (Finset.range (N + 1)).filter
            (fun k => |mGrid N k + mstar| < ε), f k)
        + ∑ k ∈ (Finset.range (N + 1)).filter (fun k =>
            ¬(|mGrid N k - mstar| < ε ∨ |mGrid N k + mstar| < ε)),
          f k := by
  have hsplit1 := Finset.sum_filter_add_sum_filter_not
    (Finset.range (N + 1)) (fun k => |mGrid N k - mstar| < ε) f
  have hsplit2 := Finset.sum_filter_add_sum_filter_not
    ((Finset.range (N + 1)).filter
      (fun k => ¬|mGrid N k - mstar| < ε))
    (fun k => |mGrid N k + mstar| < ε) f
  have hWm_eq : ((Finset.range (N + 1)).filter
      (fun k => ¬|mGrid N k - mstar| < ε)).filter
        (fun k => |mGrid N k + mstar| < ε)
      = (Finset.range (N + 1)).filter
          (fun k => |mGrid N k + mstar| < ε) := by
    rw [Finset.filter_filter]
    refine Finset.filter_congr fun k hk => ?_
    constructor
    · intro h5
      exact h5.2
    · intro h5
      exact ⟨fun h6 => hdisj k ⟨h6, h5⟩, h5⟩
  have hWr_eq : ((Finset.range (N + 1)).filter
      (fun k => ¬|mGrid N k - mstar| < ε)).filter
        (fun k => ¬|mGrid N k + mstar| < ε)
      = (Finset.range (N + 1)).filter (fun k =>
          ¬(|mGrid N k - mstar| < ε
            ∨ |mGrid N k + mstar| < ε)) := by
    rw [Finset.filter_filter]
    refine Finset.filter_congr fun k hk => ?_
    constructor
    · intro h5
      rw [not_or]
      exact ⟨h5.1, h5.2⟩
    · intro h5
      rw [not_or] at h5
      exact ⟨h5.1, h5.2⟩
  rw [hWm_eq, hWr_eq] at hsplit2
  linarith [hsplit1, hsplit2]

variable {lam mstar : ℝ}

set_option maxHeartbeats 1600000 in
-- the three-well split and the mass sandwich make this proof large
/-- **Weak convergence of the magnetization to the two-point
mixture**: for every continuous observable `G` and field sequence
with `N h_N → c`, the fibre expectation of `G(m_N)` converges to
the `w±(c)`-mixture of `G(±m⋆)`. -/
theorem cw_weak_conv (hlam : 1 < lam)
    (hmstar : mstar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : Real.tanh (lam * mstar) = mstar)
    (hseq : ℕ → ℝ) (c : ℝ)
    (hc : Tendsto (fun N : ℕ => (N : ℝ) * hseq N) atTop (nhds c))
    (G : ℝ → ℝ) (hG : Continuous G) :
    Tendsto (fun N : ℕ => ∑ k ∈ Finset.range (N + 1),
        G (mGrid N k) * fibreMass N lam (hseq N) k) atTop
      (nhds (Real.exp (c * mstar)
          / (Real.exp (c * mstar) + Real.exp (-(c * mstar)))
          * G mstar
        + Real.exp (-(c * mstar))
          / (Real.exp (c * mstar) + Real.exp (-(c * mstar)))
          * G (-mstar))) := by
  set wP : ℝ := Real.exp (c * mstar)
    / (Real.exp (c * mstar) + Real.exp (-(c * mstar))) with hwP
  set wM : ℝ := Real.exp (-(c * mstar))
    / (Real.exp (c * mstar) + Real.exp (-(c * mstar))) with hwM
  have hwsum : wP + wM = 1 := by
    rw [hwP, hwM, ← add_div, div_self (by positivity)]
  rw [Metric.tendsto_atTop]
  intro ε' hε'
  obtain ⟨M₀, hM₀⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hG.continuousOn (s := Set.Icc (-1 : ℝ) 1))
  set M : ℝ := max M₀ 1 with hM_def
  have hM1 : (1 : ℝ) ≤ M := le_max_right _ _
  have hM0 : (0 : ℝ) < M := by linarith
  have hMb : ∀ m ∈ Set.Icc (-1 : ℝ) 1, |G m| ≤ M := fun m hm =>
    le_trans (hM₀ m hm) (le_max_left _ _)
  obtain ⟨γ, hγ0, hγ⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous
      hG.continuousOn) (ε' / 8) (by linarith)
  set u₀ : ℝ := Real.log (1 + ε' / (8 * M)) / 2 with hu₀_def
  have hfrac0 : (0 : ℝ) < ε' / (8 * M) := by positivity
  have hu₀0 : 0 < u₀ := by
    rw [hu₀_def]
    have hlog := Real.log_pos
      (by linarith : (1 : ℝ) < 1 + ε' / (8 * M))
    linarith
  have hu₀exp : Real.exp (2 * u₀) - 1 = ε' / (8 * M) := by
    rw [hu₀_def, show 2 * (Real.log (1 + ε' / (8 * M)) / 2)
        = Real.log (1 + ε' / (8 * M)) from by ring,
      Real.exp_log (by linarith)]
    ring
  set ε : ℝ := min (min (γ / 2) (mstar / 2))
    (u₀ / (2 * (|c| + 1))) with hε_def
  have habs1 : (0 : ℝ) < |c| + 1 := by positivity
  have hε0 : 0 < ε := by
    rw [hε_def]
    refine lt_min (lt_min (by linarith) (by linarith [hmstar.1])) ?_
    positivity
  have hε_γ : ε ≤ γ / 2 :=
    le_trans (min_le_left _ _) (min_le_left _ _)
  have hε_m : ε ≤ mstar / 2 :=
    le_trans (min_le_left _ _) (min_le_right _ _)
  have hε_u : ε ≤ u₀ / (2 * (|c| + 1)) := min_le_right _ _
  have hε1 : ε < mstar :=
    lt_of_le_of_lt hε_m (by linarith [hmstar.1])
  have hmstarIcc : mstar ∈ Set.Icc (-1 : ℝ) 1 :=
    ⟨by linarith [hmstar.1], hmstar.2.le⟩
  have hmstarIcc' : -mstar ∈ Set.Icc (-1 : ℝ) 1 :=
    ⟨by linarith [hmstar.2], by linarith [hmstar.1]⟩
  have hrest := cw_rest_decay hlam hmstar hfix hε0 hε1 hseq c hc
  obtain ⟨N₁, hN₁⟩ := (Metric.tendsto_atTop.mp hrest)
    (ε' / (16 * (M + 1))) (by positivity)
  obtain ⟨N₂, hN₂⟩ := (Metric.tendsto_atTop.mp hc) (u₀ / 2)
    (by linarith)
  obtain ⟨N₃, hN₃⟩ := exists_nat_gt (2 / ε)
  refine ⟨max (max N₁ N₂) (max N₃ 1), fun N hNge => ?_⟩
  have hN₁' : N₁ ≤ N := le_trans (le_max_left _ _)
    (le_trans (le_max_left _ _) hNge)
  have hN₂' : N₂ ≤ N := le_trans (le_max_right _ _)
    (le_trans (le_max_left _ _) hNge)
  have hN₃' : N₃ ≤ N := le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) hNge)
  have hNpos : 0 < N := Nat.lt_of_lt_of_le Nat.zero_lt_one
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hNge))
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hNpos
  have hmesh : 2 / (N : ℝ) < ε := by
    rw [div_lt_iff₀ hN']
    have h6 : (2 : ℝ) / ε < N₃ := hN₃
    have h7 : (N₃ : ℝ) ≤ N := Nat.cast_le.mpr hN₃'
    rw [div_lt_iff₀ hε0] at h6
    nlinarith
  set massWp : ℝ := ∑ k ∈ (Finset.range (N + 1)).filter
    (fun k => |mGrid N k - mstar| < ε),
    fibreMass N lam (hseq N) k with hmWp
  set massWm : ℝ := ∑ k ∈ (Finset.range (N + 1)).filter
    (fun k => |mGrid N k + mstar| < ε),
    fibreMass N lam (hseq N) k with hmWm
  set ρN : ℝ := ∑ k ∈ (Finset.range (N + 1)).filter (fun k =>
    ¬(|mGrid N k - mstar| < ε ∨ |mGrid N k + mstar| < ε)),
    fibreMass N lam (hseq N) k with hρN
  have hρ0 : 0 ≤ ρN := by
    rw [hρN]
    exact Finset.sum_nonneg fun k _ =>
      fibreMass_nonneg lam (hseq N) k
  have hmWp0 : 0 ≤ massWp := by
    rw [hmWp]
    exact Finset.sum_nonneg fun k _ =>
      fibreMass_nonneg lam (hseq N) k
  have hmWm0 : 0 ≤ massWm := by
    rw [hmWm]
    exact Finset.sum_nonneg fun k _ =>
      fibreMass_nonneg lam (hseq N) k
  have hρsmall : ρN ≤ ε' / (16 * (M + 1)) := by
    have h8 := hN₁ N hN₁'
    rw [Real.dist_eq, sub_zero] at h8
    exact le_of_lt (lt_of_abs_lt h8)
  have hcN := hN₂ N hN₂'
  rw [Real.dist_eq] at hcN
  -- tilt control on both wells
  have htilt_core : ∀ k ≤ N, ∀ y : ℝ, |y| ≤ 1 →
      |((N : ℝ) * hseq N) * y - c * y| ≤ u₀ / 2 := by
    intro k hk y hy
    rw [show ((N : ℝ) * hseq N) * y - c * y
        = ((N : ℝ) * hseq N - c) * y from by ring, abs_mul]
    calc |(N : ℝ) * hseq N - c| * |y|
        ≤ |(N : ℝ) * hseq N - c| * 1 :=
          mul_le_mul_of_nonneg_left hy (abs_nonneg _)
      _ ≤ u₀ / 2 := by
          rw [mul_one]
          linarith [hcN]
  have hcε : |c| * ε ≤ u₀ / 2 := by
    calc |c| * ε ≤ |c| * (u₀ / (2 * (|c| + 1))) :=
          mul_le_mul_of_nonneg_left hε_u (abs_nonneg _)
      _ ≤ u₀ / 2 := by
          rw [← mul_div_assoc]
          rw [div_le_div_iff₀ (by positivity)
            (by norm_num : (0 : ℝ) < 2)]
          nlinarith [abs_nonneg c, hu₀0.le]
  have htp : ∀ k ≤ N, |mGrid N k - mstar| < ε →
      |hseq N * (2 * (k : ℝ) - N) - c * mstar| ≤ u₀ := by
    intro k hk hkw
    have hmk := mGrid_mem hNpos hk
    have hmk1 : |mGrid N k| ≤ 1 := by
      rw [abs_le]
      exact ⟨hmk.1, hmk.2⟩
    have hident : hseq N * (2 * (k : ℝ) - N)
        = ((N : ℝ) * hseq N) * mGrid N k := by
      rw [mag_eq_mGrid hNpos]
      ring
    rw [hident]
    have hsplit9 : ((N : ℝ) * hseq N) * mGrid N k - c * mstar
        = (((N : ℝ) * hseq N) * mGrid N k - c * mGrid N k)
          + c * (mGrid N k - mstar) := by
      ring
    rw [hsplit9]
    refine le_trans (abs_add_le _ _) ?_
    have h9 := htilt_core k hk (mGrid N k) hmk1
    have h10 : |c * (mGrid N k - mstar)| ≤ u₀ / 2 := by
      rw [abs_mul]
      calc |c| * |mGrid N k - mstar| ≤ |c| * ε :=
            mul_le_mul_of_nonneg_left hkw.le (abs_nonneg _)
        _ ≤ u₀ / 2 := hcε
    linarith
  have htm : ∀ k ≤ N, |mGrid N k + mstar| < ε →
      |hseq N * (2 * (k : ℝ) - N) + c * mstar| ≤ u₀ := by
    intro k hk hkw
    have hmk := mGrid_mem hNpos hk
    have hmk1 : |mGrid N k| ≤ 1 := by
      rw [abs_le]
      exact ⟨hmk.1, hmk.2⟩
    have hident : hseq N * (2 * (k : ℝ) - N)
        = ((N : ℝ) * hseq N) * mGrid N k := by
      rw [mag_eq_mGrid hNpos]
      ring
    rw [hident]
    have hsplit9 : ((N : ℝ) * hseq N) * mGrid N k + c * mstar
        = (((N : ℝ) * hseq N) * mGrid N k - c * mGrid N k)
          + c * (mGrid N k + mstar) := by
      ring
    rw [hsplit9]
    refine le_trans (abs_add_le _ _) ?_
    have h9 := htilt_core k hk (mGrid N k) hmk1
    have h10 : |c * (mGrid N k + mstar)| ≤ u₀ / 2 := by
      rw [abs_mul]
      calc |c| * |mGrid N k + mstar| ≤ |c| * ε :=
            mul_le_mul_of_nonneg_left hkw.le (abs_nonneg _)
        _ ≤ u₀ / 2 := hcε
    linarith
  -- the +well mass bound
  have hWpb : |massWp - wP| ≤ ε' / (8 * M) + ρN := by
    have h11 := cw_well_mass_bound (lam := lam) hε0 hε1 hmstar
      hNpos (hseq N) c u₀ hu₀0.le hmesh htp htm
    rw [hu₀exp] at h11
    exact h11
  -- disjoint wells, mass partition
  have hdisj : ∀ k, ¬(|mGrid N k - mstar| < ε
      ∧ |mGrid N k + mstar| < ε) := by
    intro k ⟨h1, h2⟩
    have h3 := abs_lt.mp h1
    have h4 := abs_lt.mp h2
    linarith [h3.1, h4.2, hmstar.1]
  have hmass_total : massWp + massWm + ρN = 1 := by
    have h12 := sum_split_wells hdisj (fibreMass N lam (hseq N))
    have h13 := fibreMass_total (N := N) (lam := lam)
      (h := hseq N)
    rw [h12] at h13
    linarith [h13]
  have hWmb : |massWm - wM| ≤ ε' / (8 * M) + 2 * ρN := by
    have h15 : massWm = 1 - massWp - ρN := by
      linarith [hmass_total]
    have h16 : wM = 1 - wP := by linarith [hwsum]
    have h14 : massWm - wM = (wP - massWp) + -ρN := by
      rw [h15, h16]
      ring
    rw [h14]
    refine le_trans (abs_add_le _ _) ?_
    rw [abs_neg, abs_of_nonneg hρ0, abs_sub_comm]
    linarith [hWpb]
  have hmWp1 : massWp ≤ 1 := by linarith [hmass_total, hρ0, hmWm0]
  have hmWm1 : massWm ≤ 1 := by linarith [hmass_total, hρ0, hmWp0]
  -- split the observable sum
  have hEsplit := sum_split_wells hdisj
    (fun k => G (mGrid N k) * fibreMass N lam (hseq N) k)
  -- window sums close to G(±m⋆)·mass
  have hA : |(∑ k ∈ (Finset.range (N + 1)).filter
      (fun k => |mGrid N k - mstar| < ε),
        G (mGrid N k) * fibreMass N lam (hseq N) k)
      - G mstar * massWp| ≤ ε' / 8 * massWp := by
    rw [hmWp, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hterm : ∀ k ∈ (Finset.range (N + 1)).filter
        (fun k => |mGrid N k - mstar| < ε),
        |G (mGrid N k) * fibreMass N lam (hseq N) k
          - G mstar * fibreMass N lam (hseq N) k|
        ≤ ε' / 8 * fibreMass N lam (hseq N) k := by
      intro k hk
      have hk1 := Finset.mem_filter.mp hk
      have hkN : k ≤ N := Nat.lt_succ_iff.mp
        (Finset.mem_range.mp hk1.1)
      rw [← sub_mul, abs_mul,
        abs_of_nonneg (fibreMass_nonneg lam (hseq N) k)]
      refine mul_le_mul_of_nonneg_right ?_
        (fibreMass_nonneg lam (hseq N) k)
      have h17 := hγ (mGrid N k) (mGrid_mem hNpos hkN)
        mstar hmstarIcc (by
          rw [Real.dist_eq]
          exact lt_of_lt_of_le hk1.2 (by linarith [hε_γ]))
      rw [Real.dist_eq] at h17
      exact h17.le
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum]
  have hB : |(∑ k ∈ (Finset.range (N + 1)).filter
      (fun k => |mGrid N k + mstar| < ε),
        G (mGrid N k) * fibreMass N lam (hseq N) k)
      - G (-mstar) * massWm| ≤ ε' / 8 * massWm := by
    rw [hmWm, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hterm : ∀ k ∈ (Finset.range (N + 1)).filter
        (fun k => |mGrid N k + mstar| < ε),
        |G (mGrid N k) * fibreMass N lam (hseq N) k
          - G (-mstar) * fibreMass N lam (hseq N) k|
        ≤ ε' / 8 * fibreMass N lam (hseq N) k := by
      intro k hk
      have hk1 := Finset.mem_filter.mp hk
      have hkN : k ≤ N := Nat.lt_succ_iff.mp
        (Finset.mem_range.mp hk1.1)
      rw [← sub_mul, abs_mul,
        abs_of_nonneg (fibreMass_nonneg lam (hseq N) k)]
      refine mul_le_mul_of_nonneg_right ?_
        (fibreMass_nonneg lam (hseq N) k)
      have h17 := hγ (mGrid N k) (mGrid_mem hNpos hkN)
        (-mstar) hmstarIcc' (by
          rw [Real.dist_eq, sub_neg_eq_add]
          exact lt_of_lt_of_le hk1.2 (by linarith [hε_γ]))
      rw [Real.dist_eq] at h17
      exact h17.le
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum]
  have hC : |∑ k ∈ (Finset.range (N + 1)).filter (fun k =>
      ¬(|mGrid N k - mstar| < ε ∨ |mGrid N k + mstar| < ε)),
        G (mGrid N k) * fibreMass N lam (hseq N) k| ≤ M * ρN := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hterm : ∀ k ∈ (Finset.range (N + 1)).filter (fun k =>
        ¬(|mGrid N k - mstar| < ε ∨ |mGrid N k + mstar| < ε)),
        |G (mGrid N k) * fibreMass N lam (hseq N) k|
        ≤ M * fibreMass N lam (hseq N) k := by
      intro k hk
      have hkN : k ≤ N := Nat.lt_succ_iff.mp
        (Finset.mem_range.mp (Finset.mem_filter.mp hk).1)
      rw [abs_mul,
        abs_of_nonneg (fibreMass_nonneg lam (hseq N) k)]
      exact mul_le_mul_of_nonneg_right
        (hMb _ (mGrid_mem hNpos hkN))
        (fibreMass_nonneg lam (hseq N) k)
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum, hρN]
  -- assemble
  rw [Real.dist_eq]
  have hGm : |G mstar| ≤ M := hMb mstar hmstarIcc
  have hGm' : |G (-mstar)| ≤ M := hMb (-mstar) hmstarIcc'
  set A : ℝ := (∑ k ∈ (Finset.range (N + 1)).filter
    (fun k => |mGrid N k - mstar| < ε),
      G (mGrid N k) * fibreMass N lam (hseq N) k)
    - G mstar * massWp with hA_def
  set B : ℝ := (∑ k ∈ (Finset.range (N + 1)).filter
    (fun k => |mGrid N k + mstar| < ε),
      G (mGrid N k) * fibreMass N lam (hseq N) k)
    - G (-mstar) * massWm with hB_def
  set C : ℝ := ∑ k ∈ (Finset.range (N + 1)).filter (fun k =>
    ¬(|mGrid N k - mstar| < ε ∨ |mGrid N k + mstar| < ε)),
      G (mGrid N k) * fibreMass N lam (hseq N) k with hC_def
  have hexpand : (∑ k ∈ Finset.range (N + 1),
      G (mGrid N k) * fibreMass N lam (hseq N) k)
      - (wP * G mstar + wM * G (-mstar))
      = A + B + C + G mstar * (massWp - wP)
        + G (-mstar) * (massWm - wM) := by
    rw [hA_def, hB_def, hC_def, hEsplit]
    ring
  rw [hexpand]
  have htri : |A + B + C + G mstar * (massWp - wP)
      + G (-mstar) * (massWm - wM)|
      ≤ |A| + |B| + |C| + |G mstar| * |massWp - wP|
        + |G (-mstar)| * |massWm - wM| := by
    calc |A + B + C + G mstar * (massWp - wP)
        + G (-mstar) * (massWm - wM)|
        ≤ |A + B + C + G mstar * (massWp - wP)|
          + |G (-mstar) * (massWm - wM)| := abs_add_le _ _
      _ ≤ (|A + B + C| + |G mstar * (massWp - wP)|)
          + |G (-mstar) * (massWm - wM)| := by
          linarith [abs_add_le (A + B + C)
            (G mstar * (massWp - wP))]
      _ ≤ ((|A + B| + |C|) + |G mstar * (massWp - wP)|)
          + |G (-mstar) * (massWm - wM)| := by
          linarith [abs_add_le (A + B) C]
      _ ≤ (((|A| + |B|) + |C|) + |G mstar * (massWp - wP)|)
          + |G (-mstar) * (massWm - wM)| := by
          linarith [abs_add_le A B]
      _ = |A| + |B| + |C| + |G mstar| * |massWp - wP|
          + |G (-mstar)| * |massWm - wM| := by
          rw [abs_mul, abs_mul]
  refine lt_of_le_of_lt htri ?_
  have hD : |G mstar| * |massWp - wP|
      ≤ M * (ε' / (8 * M) + ρN) := by
    refine mul_le_mul hGm hWpb (abs_nonneg _) (by linarith)
  have hE : |G (-mstar)| * |massWm - wM|
      ≤ M * (ε' / (8 * M) + 2 * ρN) := by
    refine mul_le_mul hGm' hWmb (abs_nonneg _) (by linarith)
  have hMdiv : M * (ε' / (8 * M)) = ε' / 8 := by
    field_simp
  have hρfinal : 4 * M * ρN < ε' / 2 := by
    have h18 : 4 * M * ρN ≤ 4 * M * (ε' / (16 * (M + 1))) := by
      refine mul_le_mul_of_nonneg_left hρsmall (by linarith)
    have h19 : 4 * M * (ε' / (16 * (M + 1))) < ε' / 2 := by
      rw [← mul_div_assoc]
      rw [div_lt_div_iff₀ (by positivity)
        (by norm_num : (0 : ℝ) < 2)]
      nlinarith [hM0, hε']
    linarith
  have hApart : |A| ≤ ε' / 8 := by
    refine le_trans hA ?_
    nlinarith [hmWp1, hε', hmWp0]
  have hBpart : |B| ≤ ε' / 8 := by
    refine le_trans hB ?_
    nlinarith [hmWm1, hε', hmWm0]
  calc |A| + |B| + |C| + |G mstar| * |massWp - wP|
      + |G (-mstar)| * |massWm - wM|
      ≤ ε' / 8 + ε' / 8 + M * ρN + (ε' / 8 + M * ρN)
        + (ε' / 8 + 2 * M * ρN) := by
        have h20 : M * (ε' / (8 * M) + ρN)
            = ε' / 8 + M * ρN := by
          rw [mul_add, hMdiv]
        have h21 : M * (ε' / (8 * M) + 2 * ρN)
            = ε' / 8 + 2 * M * ρN := by
          rw [mul_add, hMdiv]
          ring
        have hD2 : |G mstar| * |massWp - wP|
            ≤ ε' / 8 + M * ρN := by
          rw [← h20]
          exact hD
        have hE2 : |G (-mstar)| * |massWm - wM|
            ≤ ε' / 8 + 2 * M * ρN := by
          rw [← h21]
          exact hE
        linarith [hApart, hBpart, hC, hD2, hE2]
    _ = ε' / 2 + 4 * M * ρN := by ring
    _ < ε' := by linarith [hρfinal]

end WeakConv

/-! ## The spontaneous orientation limit -/

section Spontaneous

open Filter

/-- The hypergeometric approximation without the `j ≤ k`
hypothesis. -/
theorem hypWeight_approx' {N r j k : ℕ} (hjr : j ≤ r) (hkN : k ≤ N)
    (hrN : 2 * r < N) :
    |hypWeight N r j k
      - ((k : ℝ) / N) ^ j * (((N : ℝ) - k) / N) ^ (r - j)|
    ≤ 2 * (r : ℝ) ^ 2 / ((N : ℝ) - r) := by
  rcases le_or_gt j k with hjk | hkj
  · exact hypWeight_approx hjr hjk hkN hrN
  · have hN0 : (0 : ℝ) < N := by
      have h0 : 0 < N := by omega
      exact_mod_cast h0
    have hrRN : (r : ℝ) < N := by
      have h0 : r < N := by omega
      exact_mod_cast h0
    have hNr0 : (0 : ℝ) < (N : ℝ) - r := by linarith
    have hkR : (k : ℝ) ≤ N := by exact_mod_cast hkN
    have hr1 : 1 ≤ r := by omega
    have hr1R : (1 : ℝ) ≤ r := by exact_mod_cast hr1
    have hj1 : 1 ≤ j := by omega
    rw [hypWeight_eq_zero_of_lt hkj, zero_sub, abs_neg]
    have hp0 : (0 : ℝ) ≤ (k : ℝ) / N := by positivity
    have hp1 : (k : ℝ) / N ≤ 1 := by
      rw [div_le_one hN0]
      exact hkR
    have hq0 : (0 : ℝ) ≤ ((N : ℝ) - k) / N := by
      have h1 : (0 : ℝ) ≤ (N : ℝ) - k := by linarith
      positivity
    have hq1 : ((N : ℝ) - k) / N ≤ 1 := by
      rw [div_le_one hN0]
      have h2 : (0 : ℝ) ≤ (k : ℝ) := by positivity
      linarith
    have hppow : ((k : ℝ) / N) ^ j ≤ (k : ℝ) / N :=
      pow_le_of_le_one hp0 hp1 (by omega)
    have hqpow : (((N : ℝ) - k) / N) ^ (r - j) ≤ 1 :=
      pow_le_one₀ hq0 hq1
    have hkr : (k : ℝ) < r := by
      have h3 : k < r := by omega
      exact_mod_cast h3
    have habs : |((k : ℝ) / N) ^ j
        * (((N : ℝ) - k) / N) ^ (r - j)| ≤ (k : ℝ) / N := by
      rw [abs_of_nonneg (mul_nonneg (pow_nonneg hp0 _)
        (pow_nonneg hq0 _))]
      calc ((k : ℝ) / N) ^ j * (((N : ℝ) - k) / N) ^ (r - j)
          ≤ ((k : ℝ) / N) ^ j * 1 :=
            mul_le_mul_of_nonneg_left hqpow (pow_nonneg hp0 _)
        _ = ((k : ℝ) / N) ^ j := mul_one _
        _ ≤ (k : ℝ) / N := hppow
    refine le_trans habs ?_
    rw [div_le_div_iff₀ hN0 hNr0]
    have hs1 : (k : ℝ) * ((N : ℝ) - r)
        ≤ (r : ℝ) * ((N : ℝ) - r) :=
      mul_le_mul_of_nonneg_right hkr.le hNr0.le
    have hs2 : (r : ℝ) * ((N : ℝ) - r) ≤ (r : ℝ) * N :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have hs3 : (r : ℝ) * N ≤ 2 * (r : ℝ) ^ 2 * N :=
      mul_le_mul_of_nonneg_right (by nlinarith [hr1R]) hN0.le
    linarith

/-- The Bernoulli cylinder value `g_b(m)` for a pattern with `j`
oriented cells among `r`. -/
noncomputable def cylProb (r j : ℕ) (m : ℝ) : ℝ :=
  ((1 + m) / 2) ^ j * ((1 - m) / 2) ^ (r - j)

theorem continuous_cylProb (r j : ℕ) : Continuous (cylProb r j) := by
  unfold cylProb
  fun_prop

theorem cylProb_mGrid {N k : ℕ} (hN : 0 < N) (r j : ℕ) :
    cylProb r j (mGrid N k)
      = ((k : ℝ) / N) ^ j * (((N : ℝ) - k) / N) ^ (r - j) := by
  unfold cylProb mGrid
  have hN' : ((N : ℝ)) ≠ 0 := (Nat.cast_pos.mpr hN).ne'
  have h1 : (1 + (2 * (k : ℝ) - N) / N) / 2 = (k : ℝ) / N := by
    rw [div_eq_div_iff (by norm_num : (2:ℝ) ≠ 0)
      (Nat.cast_pos.mpr hN).ne']
    field_simp
    ring
  have h2 : (1 - (2 * (k : ℝ) - N) / N) / 2
      = ((N : ℝ) - k) / N := by
    rw [div_eq_div_iff (by norm_num : (2:ℝ) ≠ 0)
      (Nat.cast_pos.mpr hN).ne']
    field_simp
    ring
  rw [h1, h2]

variable {lam mstar : ℝ}

/-- **Theorem `thm:cw-spontaneous-orientation` (i)–(ii)**: along any
field sequence with `N h_N → c`, every cylinder-pattern probability
converges to the `w±(c)`-mixture of the two Bernoulli product
values; `c = 0` (in particular zero field) gives the symmetric
mixture. -/
theorem cw_spontaneous_orientation (hlam : 1 < lam)
    (hmstar : mstar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : Real.tanh (lam * mstar) = mstar)
    (r : ℕ) (b : Fin r → Bool) (hseq : ℕ → ℝ) (c : ℝ)
    (hc : Tendsto (fun N : ℕ => (N : ℝ) * hseq N) atTop (nhds c)) :
    Tendsto (fun t : ℕ =>
      ∑ η ∈ Finset.univ.filter (fun η : Fin (r + t) → Bool =>
        ∀ i : Fin r, η (Fin.castAdd t i) = b i),
        cwMeasure (r + t) lam (hseq (r + t)) η)
      atTop
      (nhds (Real.exp (c * mstar) / (2 * Real.cosh (c * mstar))
          * cylProb r (countTrue r b) mstar
        + Real.exp (-(c * mstar)) / (2 * Real.cosh (c * mstar))
          * cylProb r (countTrue r b) (-mstar))) := by
  set j : ℕ := countTrue r b with hj
  have hjr : j ≤ r := countTrue_le r b
  have hcosh : 2 * Real.cosh (c * mstar)
      = Real.exp (c * mstar) + Real.exp (-(c * mstar)) := by
    rw [Real.cosh_eq]
    ring
  rw [hcosh]
  -- weak convergence composed with t ↦ r + t
  have hweak := cw_weak_conv hlam hmstar hfix hseq c hc
    (cylProb r j) (continuous_cylProb r j)
  have haux : Tendsto (fun t : ℕ => r + t) atTop atTop :=
    (tendsto_add_atTop_nat r).congr fun t => Nat.add_comm t r
  have hcomp := hweak.comp haux
  -- the difference with the exact pattern probability vanishes
  have hbound : ∀ᶠ t : ℕ in atTop,
      ‖(∑ η ∈ Finset.univ.filter
          (fun η : Fin (r + t) → Bool =>
            ∀ i : Fin r, η (Fin.castAdd t i) = b i),
          cwMeasure (r + t) lam (hseq (r + t)) η)
        - ∑ k ∈ Finset.range (r + t + 1),
            cylProb r j (mGrid (r + t) k)
              * fibreMass (r + t) lam (hseq (r + t)) k‖
      ≤ 2 * (r : ℝ) ^ 2 / (t : ℝ) := by
    filter_upwards [eventually_gt_atTop r] with t htr
    have hNpos : 0 < r + t := by omega
    have h2r : 2 * r < r + t := by omega
    have hdecomp := cw_pattern_decomposition lam (hseq (r + t))
      r t hNpos b
    rw [Real.norm_eq_abs, hdecomp, ← hj]
    have hfold : (∑ k ∈ Finset.range (r + t + 1),
        hypWeight (r + t) r j k
        * ∑ η ∈ Finset.univ.filter
            (fun η : Fin (r + t) → Bool =>
              countTrue (r + t) η = k),
          cwMeasure (r + t) lam (hseq (r + t)) η)
        = ∑ k ∈ Finset.range (r + t + 1),
          hypWeight (r + t) r j k
            * fibreMass (r + t) lam (hseq (r + t)) k := rfl
    rw [hfold, ← Finset.sum_sub_distrib]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hterm : ∀ k ∈ Finset.range (r + t + 1),
        |hypWeight (r + t) r j k
            * fibreMass (r + t) lam (hseq (r + t)) k
          - cylProb r j (mGrid (r + t) k)
            * fibreMass (r + t) lam (hseq (r + t)) k|
        ≤ 2 * (r : ℝ) ^ 2 / (t : ℝ)
            * fibreMass (r + t) lam (hseq (r + t)) k := by
      intro k hk
      have hkN : k ≤ r + t := Nat.lt_succ_iff.mp
        (Finset.mem_range.mp hk)
      rw [← sub_mul, abs_mul, abs_of_nonneg
        (fibreMass_nonneg lam (hseq (r + t)) k)]
      refine mul_le_mul_of_nonneg_right ?_
        (fibreMass_nonneg lam (hseq (r + t)) k)
      rw [cylProb_mGrid hNpos r j]
      have happrox := hypWeight_approx' hjr hkN h2r
      have hcast : ((r + t : ℕ) : ℝ) - r = (t : ℝ) := by
        push_cast
        ring
      rw [hcast] at happrox
      exact happrox
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum]
    rw [fibreMass_total (N := r + t) (lam := lam)
      (h := hseq (r + t)), mul_one]
  have hto0 : Tendsto (fun t : ℕ => 2 * (r : ℝ) ^ 2 / (t : ℝ))
      atTop (nhds 0) :=
    Tendsto.div_atTop tendsto_const_nhds
      tendsto_natCast_atTop_atTop
  have hdiff := squeeze_zero_norm' hbound hto0
  have hfinal := hdiff.add hcomp
  rw [zero_add] at hfinal
  refine hfinal.congr fun t => ?_
  simp only [Function.comp_apply]
  ring

end Spontaneous

/-! ## The pure-phase limits at strong tilt -/

section PurePhase

open Filter

variable {lam mstar : ℝ}

/-- The zero-field well weights are reflection symmetric. -/
theorem well_weight_reflect (lam : ℝ) {N : ℕ} {mstar ε : ℝ} :
    ∑ k ∈ (Finset.range (N + 1)).filter
      (fun k => |mGrid N k + mstar| < ε), fibreWeight N lam 0 k
    = ∑ k ∈ (Finset.range (N + 1)).filter
        (fun k => |mGrid N k - mstar| < ε),
        fibreWeight N lam 0 k := by
  refine Finset.sum_nbij' (fun k => N - k) (fun k => N - k)
    ?_ ?_ ?_ ?_ ?_
  · intro k hk
    have hk1 := Finset.mem_filter.mp hk
    have hkN : k ≤ N := Nat.lt_succ_iff.mp
      (Finset.mem_range.mp hk1.1)
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
      (by omega), ?_⟩
    rw [mGrid_reflect hkN]
    have h5 := hk1.2
    rw [show -(mGrid N k) - mstar = -(mGrid N k + mstar) from by
      ring, abs_neg]
    exact h5
  · intro k hk
    have hk1 := Finset.mem_filter.mp hk
    have hkN : k ≤ N := Nat.lt_succ_iff.mp
      (Finset.mem_range.mp hk1.1)
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
      (by omega), ?_⟩
    rw [mGrid_reflect hkN]
    have h5 := hk1.2
    rw [show -(mGrid N k) + mstar = -(mGrid N k - mstar) from by
      ring, abs_neg]
    exact h5
  · intro k hk
    have hkN : k ≤ N := Nat.lt_succ_iff.mp
      (Finset.mem_range.mp (Finset.mem_filter.mp hk).1)
    omega
  · intro k hk
    have hkN : k ≤ N := Nat.lt_succ_iff.mp
      (Finset.mem_range.mp (Finset.mem_filter.mp hk).1)
    omega
  · intro k hk
    have hkN : k ≤ N := Nat.lt_succ_iff.mp
      (Finset.mem_range.mp (Finset.mem_filter.mp hk).1)
    exact (fibreWeight_reflect lam k hkN).symm

/-- **Off-well mass decay, vanishing-field version**: only
`h_N → 0` is needed. -/
theorem cw_rest_decay0 (hlam : 1 < lam)
    (hmstar : mstar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : Real.tanh (lam * mstar) = mstar)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < mstar)
    (hseq : ℕ → ℝ) (hh0 : Tendsto hseq atTop (nhds 0)) :
    Tendsto (fun N : ℕ =>
      ∑ k ∈ (Finset.range (N + 1)).filter (fun k =>
        ¬(|mGrid N k - mstar| < ε ∨ |mGrid N k + mstar| < ε)),
        fibreMass N lam (hseq N) k) atTop (nhds 0) := by
  obtain ⟨δ, hδ0, hδ⟩ := cw_gap hlam hmstar hfix (ε := ε) hε0
  have hmemStar : mstar ∈ Set.Icc (-1 : ℝ) 1 :=
    ⟨by linarith [hmstar.1], hmstar.2.le⟩
  have hucont : UniformContinuousOn (cwPressure lam 0)
      (Set.Icc (-1 : ℝ) 1) :=
    isCompact_Icc.uniformContinuousOn_of_continuous
      (continuous_cwPressure lam 0).continuousOn
  obtain ⟨γ, hγ0, hγ⟩ := Metric.uniformContinuousOn_iff.mp hucont
    (δ / 4) (by linarith)
  have hev : ∀ᶠ N : ℕ in atTop,
      ∑ k ∈ (Finset.range (N + 1)).filter (fun k =>
        ¬(|mGrid N k - mstar| < ε ∨ |mGrid N k + mstar| < ε)),
        fibreMass N lam (hseq N) k
      ≤ ((N : ℝ) + 1) ^ 2 * Real.exp (-((N : ℝ) * (δ / 2))) := by
    obtain ⟨Nc, hNc⟩ := (Metric.tendsto_atTop.mp hh0) (δ / 8)
      (by linarith)
    obtain ⟨Nm, hNm⟩ := exists_nat_gt (2 / γ)
    filter_upwards [eventually_ge_atTop
      (max (max Nc Nm) 1)] with N hNge
    have hNc' : Nc ≤ N := le_trans (le_max_left _ _)
      (le_trans (le_max_left _ _) hNge)
    have hNm' : Nm ≤ N := le_trans (le_max_right _ _)
      (le_trans (le_max_left _ _) hNge)
    have hNpos : 0 < N := Nat.lt_of_lt_of_le Nat.zero_lt_one
      (le_trans (le_max_right _ _) hNge)
    have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hNpos
    have hcN := hNc N hNc'
    rw [Real.dist_eq, sub_zero] at hcN
    have hhabs : |hseq N| ≤ δ / 8 := hcN.le
    -- reference grid point near mstar
    set k₀ : ℕ := ⌊(1 + mstar) / 2 * N⌋₊ with hk₀_def
    have hhalf0 : (0 : ℝ) ≤ (1 + mstar) / 2 := by
      have := hmemStar.1
      linarith
    have hk₀N : k₀ ≤ N := by
      rw [hk₀_def]
      refine Nat.floor_le_of_le ?_
      have h6 : (1 + mstar) / 2 ≤ 1 := by
        have := hmemStar.2
        linarith
      calc (1 + mstar) / 2 * (N : ℝ) ≤ 1 * N := by nlinarith
        _ = (N : ℝ) := one_mul _
    have hgrid_close : |mGrid N k₀ - mstar| ≤ 2 / N := by
      have hkfloor : (1 + mstar) / 2 * (N : ℝ) - 1 < (k₀ : ℝ) := by
        rw [hk₀_def]
        exact Nat.sub_one_lt_floor _
      have hkfloor2 : (k₀ : ℝ) ≤ (1 + mstar) / 2 * N := by
        rw [hk₀_def]
        exact Nat.floor_le (by positivity)
      unfold mGrid
      have heq : (2 * (k₀ : ℝ) - N) / N - mstar
          = (2 * (k₀ : ℝ) - N - mstar * N) / N := by
        field_simp
      rw [abs_le, heq]
      constructor
      · rw [neg_le, ← neg_div]
        refine (div_le_div_iff_of_pos_right hN').mpr ?_
        nlinarith [hkfloor2]
      · refine (div_le_div_iff_of_pos_right hN').mpr ?_
        nlinarith [hkfloor]
    have hmesh : (2 : ℝ) / N < γ := by
      rw [div_lt_iff₀ hN']
      have h6 : (2 : ℝ) / γ < Nm := hNm
      have h7 : (Nm : ℝ) ≤ N := Nat.cast_le.mpr hNm'
      rw [div_lt_iff₀ hγ0] at h6
      nlinarith
    have hΨk₀ : cwPressure lam 0 mstar - δ / 4
        ≤ cwPressure lam 0 (mGrid N k₀) := by
      have h8 := hγ (mGrid N k₀) (mGrid_mem hNpos hk₀N) mstar
        hmemStar (by
          rw [Real.dist_eq]
          exact lt_of_le_of_lt hgrid_close hmesh)
      rw [Real.dist_eq] at h8
      have := abs_lt.mp h8
      linarith [this.1]
    have hldp := cw_ldp_upper hNpos lam (hseq N)
      (fun k => ¬(|mGrid N k - mstar| < ε
        ∨ |mGrid N k + mstar| < ε))
      (cwPressure lam 0 mstar - δ + |hseq N|)
      (fun k hk hP => by
        rw [not_or] at hP
        have h9 := hδ (mGrid N k) (mGrid_mem hNpos hk)
          (not_lt.mp hP.1) (not_lt.mp hP.2)
        have h10 := cwPressure_field_close lam (hseq N)
          (mGrid N k) (mGrid_mem hNpos hk)
        have h11 := abs_le.mp h10
        linarith [h11.2])
      k₀ hk₀N
    rw [sum_fibreMass_filter lam (hseq N) _]
    refine le_trans hldp ?_
    have hΨh : cwPressure lam 0 (mGrid N k₀) - |hseq N|
        ≤ cwPressure lam (hseq N) (mGrid N k₀) := by
      have h10 := cwPressure_field_close lam (hseq N)
        (mGrid N k₀) (mGrid_mem hNpos hk₀N)
      have h11 := abs_le.mp h10
      linarith [h11.1]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine Real.exp_le_exp.mpr ?_
    have hNh : (N : ℝ) * |hseq N| ≤ (N : ℝ) * (δ / 8) :=
      mul_le_mul_of_nonneg_left hhabs hN'.le
    have h12 : (cwPressure lam 0 mstar - δ + |hseq N|)
        - cwPressure lam (hseq N) (mGrid N k₀)
        ≤ -(3 * δ / 4) + 2 * |hseq N| := by
      linarith [hΨh, hΨk₀]
    have h13 : (N : ℝ) * ((cwPressure lam 0 mstar - δ + |hseq N|)
        - cwPressure lam (hseq N) (mGrid N k₀))
        ≤ (N : ℝ) * (-(3 * δ / 4) + 2 * |hseq N|) :=
      mul_le_mul_of_nonneg_left h12 hN'.le
    have h14 : (N : ℝ) * (-(3 * δ / 4) + 2 * |hseq N|)
        = -(3 * ((N : ℝ) * δ) / 4)
          + 2 * ((N : ℝ) * |hseq N|) := by
      ring
    rw [h14] at h13
    linarith [h13, hNh]
  refine squeeze_zero' ?_ hev
    (sq_mul_exp_decay (by linarith : (0 : ℝ) < δ / 2))
  filter_upwards with N
  exact Finset.sum_nonneg fun k _ =>
    fibreMass_nonneg lam (hseq N) k

set_option maxHeartbeats 1600000 in
-- single-well concentration with unbounded tilt
/-- **Weak convergence to the pure oriented phase**: for `h_N → 0`
with `N h_N → ∞`, the fibre expectation of any continuous
observable converges to its value at `m⋆`. -/
theorem cw_weak_conv_pure (hlam : 1 < lam)
    (hmstar : mstar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : Real.tanh (lam * mstar) = mstar)
    (hseq : ℕ → ℝ) (hh0 : Tendsto hseq atTop (nhds 0))
    (hcinf : Tendsto (fun N : ℕ => (N : ℝ) * hseq N) atTop atTop)
    (G : ℝ → ℝ) (hG : Continuous G) :
    Tendsto (fun N : ℕ => ∑ k ∈ Finset.range (N + 1),
        G (mGrid N k) * fibreMass N lam (hseq N) k) atTop
      (nhds (G mstar)) := by
  rw [Metric.tendsto_atTop]
  intro ε' hε'
  obtain ⟨M₀, hM₀⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hG.continuousOn (s := Set.Icc (-1 : ℝ) 1))
  set M : ℝ := max M₀ 1 with hM_def
  have hM1 : (1 : ℝ) ≤ M := le_max_right _ _
  have hM0 : (0 : ℝ) < M := by linarith
  have hMb : ∀ m ∈ Set.Icc (-1 : ℝ) 1, |G m| ≤ M := fun m hm =>
    le_trans (hM₀ m hm) (le_max_left _ _)
  obtain ⟨γ, hγ0, hγ⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous
      hG.continuousOn) (ε' / 4) (by linarith)
  set ε : ℝ := min (γ / 2) (mstar / 2) with hε_def
  have hε0 : 0 < ε := by
    rw [hε_def]
    exact lt_min (by linarith) (by linarith [hmstar.1])
  have hε_γ : ε ≤ γ / 2 := min_le_left _ _
  have hε_m : ε ≤ mstar / 2 := min_le_right _ _
  have hε1 : ε < mstar :=
    lt_of_le_of_lt hε_m (by linarith [hmstar.1])
  have hmstarIcc : mstar ∈ Set.Icc (-1 : ℝ) 1 :=
    ⟨by linarith [hmstar.1], hmstar.2.le⟩
  have hrest := cw_rest_decay0 hlam hmstar hfix hε0 hε1 hseq hh0
  obtain ⟨N₁, hN₁⟩ := (Metric.tendsto_atTop.mp hrest)
    (ε' / (16 * (M + 1))) (by positivity)
  -- required tilt strength
  set Creq : ℝ := max 1 (-Real.log (ε' / (16 * (M + 1)))
    / (2 * (mstar - ε))) with hCreq_def
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp
    ((Filter.tendsto_atTop.mp hcinf) Creq)
  obtain ⟨N₃, hN₃⟩ := exists_nat_gt (2 / ε)
  refine ⟨max (max N₁ N₂) (max N₃ 1), fun N hNge => ?_⟩
  have hN₁' : N₁ ≤ N := le_trans (le_max_left _ _)
    (le_trans (le_max_left _ _) hNge)
  have hN₂' : N₂ ≤ N := le_trans (le_max_right _ _)
    (le_trans (le_max_left _ _) hNge)
  have hN₃' : N₃ ≤ N := le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) hNge)
  have hNpos : 0 < N := Nat.lt_of_lt_of_le Nat.zero_lt_one
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hNge))
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hNpos
  have hmesh : 2 / (N : ℝ) < ε := by
    rw [div_lt_iff₀ hN']
    have h6 : (2 : ℝ) / ε < N₃ := hN₃
    have h7 : (N₃ : ℝ) ≤ N := Nat.cast_le.mpr hN₃'
    rw [div_lt_iff₀ hε0] at h6
    nlinarith
  set cN : ℝ := (N : ℝ) * hseq N with hcN_def
  have hcN1 : Creq ≤ cN := hN₂ N hN₂'
  have hCreq1 : (1 : ℝ) ≤ Creq := le_max_left _ _
  have hcN0 : 0 ≤ cN := by linarith
  have hh0N : 0 ≤ hseq N := by
    have h8 : cN = (N : ℝ) * hseq N := hcN_def
    nlinarith [hcN0, hN']
  -- masses
  set massWp : ℝ := ∑ k ∈ (Finset.range (N + 1)).filter
    (fun k => |mGrid N k - mstar| < ε),
    fibreMass N lam (hseq N) k with hmWp
  set massWm : ℝ := ∑ k ∈ (Finset.range (N + 1)).filter
    (fun k => |mGrid N k + mstar| < ε),
    fibreMass N lam (hseq N) k with hmWm
  set ρN : ℝ := ∑ k ∈ (Finset.range (N + 1)).filter (fun k =>
    ¬(|mGrid N k - mstar| < ε ∨ |mGrid N k + mstar| < ε)),
    fibreMass N lam (hseq N) k with hρN
  have hρ0 : 0 ≤ ρN := by
    rw [hρN]
    exact Finset.sum_nonneg fun k _ =>
      fibreMass_nonneg lam (hseq N) k
  have hρsmall : ρN ≤ ε' / (16 * (M + 1)) := by
    have h8 := hN₁ N hN₁'
    rw [Real.dist_eq, sub_zero] at h8
    exact le_of_lt (lt_of_abs_lt h8)
  -- the minus-well mass is exponentially tilted away
  set S : ℝ := ∑ k ∈ (Finset.range (N + 1)).filter
    (fun k => |mGrid N k - mstar| < ε),
    fibreWeight N lam 0 k with hS
  set Tp : ℝ := ∑ k ∈ (Finset.range (N + 1)).filter
    (fun k => |mGrid N k - mstar| < ε),
    fibreWeight N lam (hseq N) k with hTp
  set Tm : ℝ := ∑ k ∈ (Finset.range (N + 1)).filter
    (fun k => |mGrid N k + mstar| < ε),
    fibreWeight N lam (hseq N) k with hTm
  have hSpos : 0 < S := by
    set k₀ : ℕ := ⌊(1 + mstar) / 2 * N⌋₊ with hk₀_def
    have hhalf0 : (0 : ℝ) ≤ (1 + mstar) / 2 := by
      have := hmstarIcc.1
      linarith
    have hk₀N : k₀ ≤ N := by
      rw [hk₀_def]
      refine Nat.floor_le_of_le ?_
      have h6 : (1 + mstar) / 2 ≤ 1 := by
        have := hmstarIcc.2
        linarith
      calc (1 + mstar) / 2 * (N : ℝ) ≤ 1 * N := by nlinarith
        _ = (N : ℝ) := one_mul _
    have hgrid_close : |mGrid N k₀ - mstar| ≤ 2 / N := by
      have hkfloor : (1 + mstar) / 2 * (N : ℝ) - 1 < (k₀ : ℝ) := by
        rw [hk₀_def]
        exact Nat.sub_one_lt_floor _
      have hkfloor2 : (k₀ : ℝ) ≤ (1 + mstar) / 2 * N := by
        rw [hk₀_def]
        exact Nat.floor_le (by positivity)
      unfold mGrid
      have heq : (2 * (k₀ : ℝ) - N) / N - mstar
          = (2 * (k₀ : ℝ) - N - mstar * N) / N := by
        field_simp
      rw [abs_le, heq]
      constructor
      · rw [neg_le, ← neg_div]
        refine (div_le_div_iff_of_pos_right hN').mpr ?_
        nlinarith [hkfloor2]
      · refine (div_le_div_iff_of_pos_right hN').mpr ?_
        nlinarith [hkfloor]
    have hk₀mem : k₀ ∈ (Finset.range (N + 1)).filter
        (fun k => |mGrid N k - mstar| < ε) := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr
        (by omega), ?_⟩
      exact lt_of_le_of_lt hgrid_close hmesh
    rw [hS]
    refine Finset.sum_pos' (fun k hk => ?_) ⟨k₀, hk₀mem, ?_⟩
    · exact (fibreWeight_pos lam 0 k (Nat.lt_succ_iff.mp
        (Finset.mem_range.mp (Finset.mem_filter.mp hk).1))).le
    · exact fibreWeight_pos lam 0 k₀ hk₀N
  have hTp_lb : S * Real.exp (cN * (mstar - ε)) ≤ Tp := by
    rw [hS, hTp, Finset.sum_mul]
    refine Finset.sum_le_sum fun k hk => ?_
    have hk1 := Finset.mem_filter.mp hk
    have hkN : k ≤ N := Nat.lt_succ_iff.mp
      (Finset.mem_range.mp hk1.1)
    have hmk := abs_lt.mp hk1.2
    conv_rhs => rw [fibreWeight_tilt]
    refine mul_le_mul_of_nonneg_left ?_
      (fibreWeight_pos lam 0 k hkN).le
    refine Real.exp_le_exp.mpr ?_
    have hident : hseq N * (2 * (k : ℝ) - N) = cN * mGrid N k := by
      rw [hcN_def, mag_eq_mGrid hNpos]
      ring
    rw [hident]
    have h9 : mstar - ε ≤ mGrid N k := by linarith [hmk.1]
    nlinarith [hcN0, h9]
  have hTm_ub : Tm ≤ S * Real.exp (cN * (-mstar + ε)) := by
    rw [hTm, hS, ← well_weight_reflect lam (N := N)
      (mstar := mstar) (ε := ε), Finset.sum_mul]
    refine Finset.sum_le_sum fun k hk => ?_
    have hk1 := Finset.mem_filter.mp hk
    have hkN : k ≤ N := Nat.lt_succ_iff.mp
      (Finset.mem_range.mp hk1.1)
    have hmk := abs_lt.mp hk1.2
    conv_lhs => rw [fibreWeight_tilt]
    refine mul_le_mul_of_nonneg_left ?_
      (fibreWeight_pos lam 0 k hkN).le
    refine Real.exp_le_exp.mpr ?_
    have hident : hseq N * (2 * (k : ℝ) - N) = cN * mGrid N k := by
      rw [hcN_def, mag_eq_mGrid hNpos]
      ring
    rw [hident]
    have h9 : mGrid N k ≤ -mstar + ε := by linarith [hmk.2]
    nlinarith [hcN0, h9]
  have hZ := cwPartition_pos N lam (hseq N)
  have hmassWm_eq : massWm = Tm / cwPartition N lam (hseq N) := by
    rw [hmWm, hTm]
    rw [Finset.sum_congr rfl fun k hk =>
      fibreMass_eq_weight_div hNpos lam (hseq N) k]
    rw [← Finset.sum_div]
  have hTp_le_Z : Tp ≤ cwPartition N lam (hseq N) := by
    rw [cwPartition_eq_sum_fibreWeight hNpos lam (hseq N), hTp]
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset _ _) fun k hk _ => ?_
    exact (fibreWeight_pos lam (hseq N) k (Nat.lt_succ_iff.mp
      (Finset.mem_range.mp hk))).le
  have hTppos : 0 < Tp :=
    lt_of_lt_of_le (by positivity) hTp_lb
  have hTm0 : 0 ≤ Tm := by
    rw [hTm]
    exact Finset.sum_nonneg fun k hk =>
      (fibreWeight_pos lam (hseq N) k (Nat.lt_succ_iff.mp
        (Finset.mem_range.mp (Finset.mem_filter.mp hk).1))).le
  have hmassWm_bound : massWm
      ≤ Real.exp (-(2 * cN * (mstar - ε))) := by
    rw [hmassWm_eq]
    have h10 : Tm / cwPartition N lam (hseq N) ≤ Tm / Tp := by
      rw [div_le_div_iff₀ hZ hTppos]
      nlinarith [hTp_le_Z, hTm0]
    refine le_trans h10 ?_
    rw [div_le_iff₀ hTppos]
    have h11 : Real.exp (-(2 * cN * (mstar - ε)))
        * (S * Real.exp (cN * (mstar - ε)))
        = S * Real.exp (cN * (-mstar + ε)) := by
      rw [mul_comm (Real.exp (-(2 * cN * (mstar - ε)))) _,
        mul_assoc, ← Real.exp_add]
      congr 2
      ring
    calc Tm ≤ S * Real.exp (cN * (-mstar + ε)) := hTm_ub
      _ = Real.exp (-(2 * cN * (mstar - ε)))
          * (S * Real.exp (cN * (mstar - ε))) := h11.symm
      _ ≤ Real.exp (-(2 * cN * (mstar - ε))) * Tp :=
          mul_le_mul_of_nonneg_left hTp_lb (Real.exp_pos _).le
  have hmε : (0 : ℝ) < mstar - ε := by linarith
  have htarget : (0 : ℝ) < ε' / (16 * (M + 1)) := by positivity
  have hCbound : Real.exp (-(2 * cN * (mstar - ε)))
      ≤ ε' / (16 * (M + 1)) := by
    rw [show ε' / (16 * (M + 1))
        = Real.exp (Real.log (ε' / (16 * (M + 1)))) from
      (Real.exp_log htarget).symm]
    refine Real.exp_le_exp.mpr ?_
    have h12 : -Real.log (ε' / (16 * (M + 1)))
        / (2 * (mstar - ε)) ≤ Creq := le_max_right _ _
    have h13 : -Real.log (ε' / (16 * (M + 1)))
        / (2 * (mstar - ε)) ≤ cN := le_trans h12 hcN1
    rw [div_le_iff₀ (by linarith : (0 : ℝ) < 2 * (mstar - ε))]
      at h13
    nlinarith [h13]
  have hmassWm_small : massWm ≤ ε' / (16 * (M + 1)) :=
    le_trans hmassWm_bound hCbound
  have hmassWm0 : 0 ≤ massWm := by
    rw [hmWm]
    exact Finset.sum_nonneg fun k _ =>
      fibreMass_nonneg lam (hseq N) k
  have hmassWp0 : 0 ≤ massWp := by
    rw [hmWp]
    exact Finset.sum_nonneg fun k _ =>
      fibreMass_nonneg lam (hseq N) k
  have hdisj : ∀ k, ¬(|mGrid N k - mstar| < ε
      ∧ |mGrid N k + mstar| < ε) := by
    intro k ⟨h1, h2⟩
    have h3 := abs_lt.mp h1
    have h4 := abs_lt.mp h2
    linarith [h3.1, h4.2, hmstar.1]
  have htotal : massWp + massWm + ρN = 1 := by
    have h12 := sum_split_wells hdisj (fibreMass N lam (hseq N))
    have h13 := fibreMass_total (N := N) (lam := lam)
      (h := hseq N)
    rw [h12] at h13
    linarith [h13]
  have hmassWp1 : massWp ≤ 1 := by linarith [htotal, hρ0, hmassWm0]
  -- final assembly
  rw [Real.dist_eq]
  have h14 : G mstar = ∑ k ∈ Finset.range (N + 1),
      G mstar * fibreMass N lam (hseq N) k := by
    rw [← Finset.mul_sum, fibreMass_total (N := N) (lam := lam)
      (h := hseq N), mul_one]
  have hEdiff : (∑ k ∈ Finset.range (N + 1),
      G (mGrid N k) * fibreMass N lam (hseq N) k) - G mstar
      = ∑ k ∈ Finset.range (N + 1),
        (G (mGrid N k) - G mstar)
          * fibreMass N lam (hseq N) k := by
    conv_lhs => rw [h14]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hEdiff]
  refine lt_of_le_of_lt (Finset.abs_sum_le_sum_abs _ _) ?_
  have hsplitabs := sum_split_wells hdisj
    (fun k => |(G (mGrid N k) - G mstar)
      * fibreMass N lam (hseq N) k|)
  rw [hsplitabs]
  have hpart1 : ∑ k ∈ (Finset.range (N + 1)).filter
      (fun k => |mGrid N k - mstar| < ε),
      |(G (mGrid N k) - G mstar)
        * fibreMass N lam (hseq N) k|
      ≤ ε' / 4 * massWp := by
    rw [hmWp, Finset.mul_sum]
    refine Finset.sum_le_sum fun k hk => ?_
    have hk1 := Finset.mem_filter.mp hk
    have hkN : k ≤ N := Nat.lt_succ_iff.mp
      (Finset.mem_range.mp hk1.1)
    rw [abs_mul, abs_of_nonneg (fibreMass_nonneg lam (hseq N) k)]
    refine mul_le_mul_of_nonneg_right ?_
      (fibreMass_nonneg lam (hseq N) k)
    have h17 := hγ (mGrid N k) (mGrid_mem hNpos hkN)
      mstar hmstarIcc (by
        rw [Real.dist_eq]
        exact lt_of_lt_of_le hk1.2 (by linarith [hε_γ]))
    rw [Real.dist_eq] at h17
    exact h17.le
  have hbound2M : ∀ k, k ≤ N →
      |G (mGrid N k) - G mstar| ≤ 2 * M := by
    intro k hkN
    have h18 : |G (mGrid N k)| ≤ M := hMb _ (mGrid_mem hNpos hkN)
    have h19 : |G mstar| ≤ M := hMb mstar hmstarIcc
    calc |G (mGrid N k) - G mstar|
        ≤ |G (mGrid N k)| + |G mstar| := by
          rw [sub_eq_add_neg]
          refine le_trans (abs_add_le _ _) ?_
          rw [abs_neg]
      _ ≤ 2 * M := by linarith
  have hpart2 : ∑ k ∈ (Finset.range (N + 1)).filter
      (fun k => |mGrid N k + mstar| < ε),
      |(G (mGrid N k) - G mstar)
        * fibreMass N lam (hseq N) k|
      ≤ 2 * M * massWm := by
    rw [hmWm, Finset.mul_sum]
    refine Finset.sum_le_sum fun k hk => ?_
    have hkN : k ≤ N := Nat.lt_succ_iff.mp
      (Finset.mem_range.mp (Finset.mem_filter.mp hk).1)
    rw [abs_mul, abs_of_nonneg (fibreMass_nonneg lam (hseq N) k)]
    exact mul_le_mul_of_nonneg_right (hbound2M k hkN)
      (fibreMass_nonneg lam (hseq N) k)
  have hpart3 : ∑ k ∈ (Finset.range (N + 1)).filter (fun k =>
      ¬(|mGrid N k - mstar| < ε ∨ |mGrid N k + mstar| < ε)),
      |(G (mGrid N k) - G mstar)
        * fibreMass N lam (hseq N) k|
      ≤ 2 * M * ρN := by
    rw [hρN, Finset.mul_sum]
    refine Finset.sum_le_sum fun k hk => ?_
    have hkN : k ≤ N := Nat.lt_succ_iff.mp
      (Finset.mem_range.mp (Finset.mem_filter.mp hk).1)
    rw [abs_mul, abs_of_nonneg (fibreMass_nonneg lam (hseq N) k)]
    exact mul_le_mul_of_nonneg_right (hbound2M k hkN)
      (fibreMass_nonneg lam (hseq N) k)
  have h20 : 2 * M * (ε' / (16 * (M + 1))) < ε' / 4 := by
    rw [← mul_div_assoc, div_lt_div_iff₀ (by positivity)
      (by norm_num : (0 : ℝ) < 4)]
    nlinarith [hM0, hε']
  calc (∑ k ∈ (Finset.range (N + 1)).filter
        (fun k => |mGrid N k - mstar| < ε),
        |(G (mGrid N k) - G mstar)
          * fibreMass N lam (hseq N) k|)
      + (∑ k ∈ (Finset.range (N + 1)).filter
          (fun k => |mGrid N k + mstar| < ε),
          |(G (mGrid N k) - G mstar)
            * fibreMass N lam (hseq N) k|)
      + ∑ k ∈ (Finset.range (N + 1)).filter (fun k =>
          ¬(|mGrid N k - mstar| < ε ∨ |mGrid N k + mstar| < ε)),
          |(G (mGrid N k) - G mstar)
            * fibreMass N lam (hseq N) k|
      ≤ ε' / 4 * massWp + 2 * M * massWm + 2 * M * ρN := by
        linarith [hpart1, hpart2, hpart3]
    _ ≤ ε' / 4 * 1 + 2 * M * (ε' / (16 * (M + 1)))
        + 2 * M * (ε' / (16 * (M + 1))) := by
        refine add_le_add (add_le_add ?_ ?_) ?_
        · exact mul_le_mul_of_nonneg_left hmassWp1 (by linarith)
        · exact mul_le_mul_of_nonneg_left hmassWm_small
            (by linarith)
        · exact mul_le_mul_of_nonneg_left hρsmall (by linarith)
    _ < ε' := by linarith [h20]

/-- **Theorem `thm:cw-spontaneous-orientation` (iii), positive
side**: for `h_N → 0` with `N h_N → ∞`, every pattern probability
converges to the pure oriented Bernoulli value. -/
theorem cw_spontaneous_orientation_pure (hlam : 1 < lam)
    (hmstar : mstar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : Real.tanh (lam * mstar) = mstar)
    (r : ℕ) (b : Fin r → Bool) (hseq : ℕ → ℝ)
    (hh0 : Tendsto hseq atTop (nhds 0))
    (hcinf : Tendsto (fun N : ℕ => (N : ℝ) * hseq N) atTop atTop) :
    Tendsto (fun t : ℕ =>
      ∑ η ∈ Finset.univ.filter (fun η : Fin (r + t) → Bool =>
        ∀ i : Fin r, η (Fin.castAdd t i) = b i),
        cwMeasure (r + t) lam (hseq (r + t)) η)
      atTop (nhds (cylProb r (countTrue r b) mstar)) := by
  set j : ℕ := countTrue r b with hj
  have hjr : j ≤ r := countTrue_le r b
  have hweak := cw_weak_conv_pure hlam hmstar hfix hseq hh0 hcinf
    (cylProb r j) (continuous_cylProb r j)
  have haux : Tendsto (fun t : ℕ => r + t) atTop atTop :=
    (tendsto_add_atTop_nat r).congr fun t => Nat.add_comm t r
  have hcomp := hweak.comp haux
  have hbound : ∀ᶠ t : ℕ in atTop,
      ‖(∑ η ∈ Finset.univ.filter
          (fun η : Fin (r + t) → Bool =>
            ∀ i : Fin r, η (Fin.castAdd t i) = b i),
          cwMeasure (r + t) lam (hseq (r + t)) η)
        - ∑ k ∈ Finset.range (r + t + 1),
            cylProb r j (mGrid (r + t) k)
              * fibreMass (r + t) lam (hseq (r + t)) k‖
      ≤ 2 * (r : ℝ) ^ 2 / (t : ℝ) := by
    filter_upwards [eventually_gt_atTop r] with t htr
    have hNpos : 0 < r + t := by omega
    have h2r : 2 * r < r + t := by omega
    have hdecomp := cw_pattern_decomposition lam (hseq (r + t))
      r t hNpos b
    rw [Real.norm_eq_abs, hdecomp, ← hj]
    have hfold : (∑ k ∈ Finset.range (r + t + 1),
        hypWeight (r + t) r j k
        * ∑ η ∈ Finset.univ.filter
            (fun η : Fin (r + t) → Bool =>
              countTrue (r + t) η = k),
          cwMeasure (r + t) lam (hseq (r + t)) η)
        = ∑ k ∈ Finset.range (r + t + 1),
          hypWeight (r + t) r j k
            * fibreMass (r + t) lam (hseq (r + t)) k := rfl
    rw [hfold, ← Finset.sum_sub_distrib]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hterm : ∀ k ∈ Finset.range (r + t + 1),
        |hypWeight (r + t) r j k
            * fibreMass (r + t) lam (hseq (r + t)) k
          - cylProb r j (mGrid (r + t) k)
            * fibreMass (r + t) lam (hseq (r + t)) k|
        ≤ 2 * (r : ℝ) ^ 2 / (t : ℝ)
            * fibreMass (r + t) lam (hseq (r + t)) k := by
      intro k hk
      have hkN : k ≤ r + t := Nat.lt_succ_iff.mp
        (Finset.mem_range.mp hk)
      rw [← sub_mul, abs_mul, abs_of_nonneg
        (fibreMass_nonneg lam (hseq (r + t)) k)]
      refine mul_le_mul_of_nonneg_right ?_
        (fibreMass_nonneg lam (hseq (r + t)) k)
      rw [cylProb_mGrid hNpos r j]
      have happrox := hypWeight_approx' hjr hkN h2r
      have hcast : ((r + t : ℕ) : ℝ) - r = (t : ℝ) := by
        push_cast
        ring
      rw [hcast] at happrox
      exact happrox
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum]
    rw [fibreMass_total (N := r + t) (lam := lam)
      (h := hseq (r + t)), mul_one]
  have hto0 : Tendsto (fun t : ℕ => 2 * (r : ℝ) ^ 2 / (t : ℝ))
      atTop (nhds 0) :=
    Tendsto.div_atTop tendsto_const_nhds
      tendsto_natCast_atTop_atTop
  have hdiff := squeeze_zero_norm' hbound hto0
  have hfinal := hdiff.add hcomp
  rw [zero_add] at hfinal
  refine hfinal.congr fun t => ?_
  simp only [Function.comp_apply]
  ring

/-! ### Deck reflection and the negative pure phase -/

theorem countTrue_not (r : ℕ) (b : Fin r → Bool) :
    countTrue r (fun i => !(b i)) = r - countTrue r b := by
  unfold countTrue
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin r))) (fun i => b i = true)
  rw [Finset.card_univ, Fintype.card_fin] at h
  have h2 : (Finset.univ.filter fun i => (!(b i)) = true)
      = Finset.univ.filter fun i => ¬(b i = true) := by
    refine Finset.filter_congr fun i _ => ?_
    cases b i <;> simp
  rw [h2]
  omega

theorem cylProb_flip {r j : ℕ} (hjr : j ≤ r) (m : ℝ) :
    cylProb r (r - j) m = cylProb r j (-m) := by
  unfold cylProb
  rw [show r - (r - j) = j from by omega]
  rw [show (1 : ℝ) + -m = 1 - m from by ring,
    show (1 : ℝ) - -m = 1 + m from by ring]
  ring

/-- Deck reflection of pattern probabilities: flipping the pattern
and the field leaves the probability unchanged. -/
theorem cw_pattern_flip (lam h : ℝ) (r t : ℕ) (b : Fin r → Bool) :
    ∑ η ∈ Finset.univ.filter (fun η : Fin (r + t) → Bool =>
      ∀ i : Fin r, η (Fin.castAdd t i) = b i),
      cwMeasure (r + t) lam h η
    = ∑ η ∈ Finset.univ.filter (fun η : Fin (r + t) → Bool =>
        ∀ i : Fin r, η (Fin.castAdd t i) = !(b i)),
        cwMeasure (r + t) lam (-h) η := by
  set N : ℕ := r + t with hN_def
  have hinv : Function.Involutive (deckFlip N) := by
    intro η
    funext i
    simp [deckFlip]
  have hweight : ∀ η : Fin N → Bool, cwWeight N lam h η
      = cwWeight N lam (-h) (deckFlip N η) := by
    intro η
    unfold cwWeight
    rw [magSum_deckFlip]
    congr 1
    ring
  have hZ : cwPartition N lam (-h) = cwPartition N lam h := by
    unfold cwPartition
    rw [← Function.Bijective.sum_comp hinv.bijective
      (cwWeight N lam (-h))]
    refine Finset.sum_congr rfl fun η _ => ?_
    exact (hweight η).symm
  unfold cwMeasure
  rw [hZ, ← Finset.sum_div, ← Finset.sum_div]
  congr 1
  refine Finset.sum_nbij' (fun η => deckFlip N η)
    (fun η => deckFlip N η) ?_ ?_ ?_ ?_ ?_
  · intro η hη
    have hη1 := (Finset.mem_filter.mp hη).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    intro i
    simp only [deckFlip]
    rw [hη1 i]
  · intro η hη
    have hη1 := (Finset.mem_filter.mp hη).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    intro i
    have h3 := hη1 i
    simp only [deckFlip]
    rw [h3, Bool.not_not]
  · intro η _
    exact hinv η
  · intro η _
    exact hinv η
  · intro η _
    exact hweight η

/-- **Theorem `thm:cw-spontaneous-orientation` (iii), negative
side**: for `h_N → 0` with `N h_N → −∞`, every pattern probability
converges to the reversed pure Bernoulli value. -/
theorem cw_spontaneous_orientation_pure_neg (hlam : 1 < lam)
    (hmstar : mstar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : Real.tanh (lam * mstar) = mstar)
    (r : ℕ) (b : Fin r → Bool) (hseq : ℕ → ℝ)
    (hh0 : Tendsto hseq atTop (nhds 0))
    (hcinf : Tendsto (fun N : ℕ => (N : ℝ) * hseq N) atTop atBot) :
    Tendsto (fun t : ℕ =>
      ∑ η ∈ Finset.univ.filter (fun η : Fin (r + t) → Bool =>
        ∀ i : Fin r, η (Fin.castAdd t i) = b i),
        cwMeasure (r + t) lam (hseq (r + t)) η)
      atTop (nhds (cylProb r (countTrue r b) (-mstar))) := by
  set j : ℕ := countTrue r b with hj
  have hjr : j ≤ r := countTrue_le r b
  have hh0' : Tendsto (fun N => -hseq N) atTop (nhds 0) := by
    have := hh0.neg
    simpa using this
  have hcinf' : Tendsto (fun N : ℕ => (N : ℝ) * -hseq N)
      atTop atTop := by
    have h1 : Tendsto (fun N : ℕ => -((N : ℝ) * hseq N))
        atTop atTop := tendsto_neg_atBot_atTop.comp hcinf
    refine h1.congr fun N => ?_
    ring
  have hpos := cw_spontaneous_orientation_pure hlam hmstar hfix r
    (fun i => !(b i)) (fun N => -hseq N) hh0' hcinf'
  rw [countTrue_not r b, ← hj, cylProb_flip hjr] at hpos
  refine hpos.congr fun t => ?_
  exact (cw_pattern_flip lam (hseq (r + t)) r t b).symm

end PurePhase

/-! ## Fixed-field single-phase concentration -/

section FixedField

open Filter

variable {lam h mhat : ℝ}

/-- Gap of the field pressure outside the unique maximizer well. -/
theorem cw_gap_field
    (hmem : mhat ∈ Set.Icc (-1 : ℝ) 1)
    (hmax : IsMaxOn (cwPressure lam h) (Set.Icc (-1 : ℝ) 1) mhat)
    (huniq : ∀ m₁ ∈ Set.Icc (-1 : ℝ) 1,
      IsMaxOn (cwPressure lam h) (Set.Icc (-1 : ℝ) 1) m₁
        → m₁ = mhat)
    {ε : ℝ} (hε0 : 0 < ε) :
    ∃ δ > (0 : ℝ), ∀ m ∈ Set.Icc (-1 : ℝ) 1,
      ε ≤ |m - mhat| →
      cwPressure lam h m ≤ cwPressure lam h mhat - δ := by
  set K : Set ℝ := Set.Icc (-1 : ℝ) 1 \
    Set.Ioo (mhat - ε) (mhat + ε) with hK_def
  have hKcomp : IsCompact K := isCompact_Icc.diff isOpen_Ioo
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · refine ⟨1, one_pos, fun m hm h1 => ?_⟩
    exfalso
    have hmem2 : m ∈ K := by
      rw [hK_def]
      refine ⟨hm, fun hw => ?_⟩
      have habs : |m - mhat| < ε :=
        abs_lt.mpr ⟨by linarith [hw.1], by linarith [hw.2]⟩
      linarith [habs, h1]
    rw [hKe] at hmem2
    exact Set.notMem_empty m hmem2
  · obtain ⟨xK, hxK, hxKmax⟩ := hKcomp.exists_isMaxOn hKne
      (continuous_cwPressure lam h).continuousOn
    have hxK_ne : xK ≠ mhat := by
      intro hcon
      have h2 := hxK.2
      rw [hcon] at h2
      exact h2 ⟨by linarith, by linarith⟩
    have hgap : cwPressure lam h xK < cwPressure lam h mhat := by
      have h1 := hmax hxK.1
      simp only [Set.mem_setOf_eq] at h1
      rcases lt_or_eq_of_le h1 with hlt | heq
      · exact hlt
      · exfalso
        refine hxK_ne (huniq xK hxK.1 ?_)
        intro m hm
        simp only [Set.mem_setOf_eq]
        calc cwPressure lam h m ≤ cwPressure lam h mhat := hmax hm
          _ = cwPressure lam h xK := heq.symm
    refine ⟨cwPressure lam h mhat - cwPressure lam h xK,
      by linarith, fun m hm h1 => ?_⟩
    have hmemK : m ∈ K := by
      rw [hK_def]
      refine ⟨hm, fun hw => ?_⟩
      have habs : |m - mhat| < ε :=
        abs_lt.mpr ⟨by linarith [hw.1], by linarith [hw.2]⟩
      linarith [habs, h1]
    have h3 := hxKmax hmemK
    simp only [Set.mem_setOf_eq] at h3
    linarith

/-- Fixed-field off-well mass decay. -/
theorem cw_rest_decay_fixed (lam h : ℝ)
    (hmem : mhat ∈ Set.Icc (-1 : ℝ) 1)
    (hint : mhat ∈ Set.Ioo (-1 : ℝ) 1)
    (hmax : IsMaxOn (cwPressure lam h) (Set.Icc (-1 : ℝ) 1) mhat)
    (huniq : ∀ m₁ ∈ Set.Icc (-1 : ℝ) 1,
      IsMaxOn (cwPressure lam h) (Set.Icc (-1 : ℝ) 1) m₁
        → m₁ = mhat)
    {ε : ℝ} (hε0 : 0 < ε) :
    Tendsto (fun N : ℕ =>
      ∑ k ∈ (Finset.range (N + 1)).filter (fun k =>
        ¬(|mGrid N k - mhat| < ε)),
        fibreMass N lam h k) atTop (nhds 0) := by
  obtain ⟨δ, hδ0, hδ⟩ := cw_gap_field hmem hmax huniq
    (ε := ε) hε0
  have hucont : UniformContinuousOn (cwPressure lam h)
      (Set.Icc (-1 : ℝ) 1) :=
    isCompact_Icc.uniformContinuousOn_of_continuous
      (continuous_cwPressure lam h).continuousOn
  obtain ⟨γ, hγ0, hγ⟩ := Metric.uniformContinuousOn_iff.mp hucont
    (δ / 4) (by linarith)
  have hev : ∀ᶠ N : ℕ in atTop,
      ∑ k ∈ (Finset.range (N + 1)).filter (fun k =>
        ¬(|mGrid N k - mhat| < ε)),
        fibreMass N lam h k
      ≤ ((N : ℝ) + 1) ^ 2 * Real.exp (-((N : ℝ) * (δ / 2))) := by
    obtain ⟨Nm, hNm⟩ := exists_nat_gt (2 / γ)
    filter_upwards [eventually_ge_atTop (max Nm 1)] with N hNge
    have hNm' : Nm ≤ N := le_trans (le_max_left _ _) hNge
    have hNpos : 0 < N := Nat.lt_of_lt_of_le Nat.zero_lt_one
      (le_trans (le_max_right _ _) hNge)
    have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hNpos
    set k₀ : ℕ := ⌊(1 + mhat) / 2 * N⌋₊ with hk₀_def
    have hhalf0 : (0 : ℝ) ≤ (1 + mhat) / 2 := by
      have := hmem.1
      linarith
    have hk₀N : k₀ ≤ N := by
      rw [hk₀_def]
      refine Nat.floor_le_of_le ?_
      have h6 : (1 + mhat) / 2 ≤ 1 := by
        have := hmem.2
        linarith
      calc (1 + mhat) / 2 * (N : ℝ) ≤ 1 * N := by nlinarith
        _ = (N : ℝ) := one_mul _
    have hgrid_close : |mGrid N k₀ - mhat| ≤ 2 / N := by
      have hkfloor : (1 + mhat) / 2 * (N : ℝ) - 1 < (k₀ : ℝ) := by
        rw [hk₀_def]
        exact Nat.sub_one_lt_floor _
      have hkfloor2 : (k₀ : ℝ) ≤ (1 + mhat) / 2 * N := by
        rw [hk₀_def]
        exact Nat.floor_le (by positivity)
      unfold mGrid
      have heq : (2 * (k₀ : ℝ) - N) / N - mhat
          = (2 * (k₀ : ℝ) - N - mhat * N) / N := by
        field_simp
      rw [abs_le, heq]
      constructor
      · rw [neg_le, ← neg_div]
        refine (div_le_div_iff_of_pos_right hN').mpr ?_
        nlinarith [hkfloor2]
      · refine (div_le_div_iff_of_pos_right hN').mpr ?_
        nlinarith [hkfloor]
    have hmesh : (2 : ℝ) / N < γ := by
      rw [div_lt_iff₀ hN']
      have h6 : (2 : ℝ) / γ < Nm := hNm
      have h7 : (Nm : ℝ) ≤ N := Nat.cast_le.mpr hNm'
      rw [div_lt_iff₀ hγ0] at h6
      nlinarith
    have hΨk₀ : cwPressure lam h mhat - δ / 4
        ≤ cwPressure lam h (mGrid N k₀) := by
      have h8 := hγ (mGrid N k₀) (mGrid_mem hNpos hk₀N) mhat
        hmem (by
          rw [Real.dist_eq]
          exact lt_of_le_of_lt hgrid_close hmesh)
      rw [Real.dist_eq] at h8
      have := abs_lt.mp h8
      linarith [this.1]
    have hldp := cw_ldp_upper hNpos lam h
      (fun k => ¬(|mGrid N k - mhat| < ε))
      (cwPressure lam h mhat - δ)
      (fun k hk hP =>
        hδ (mGrid N k) (mGrid_mem hNpos hk) (not_lt.mp hP))
      k₀ hk₀N
    rw [sum_fibreMass_filter lam h _]
    refine le_trans hldp ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine Real.exp_le_exp.mpr ?_
    have h13 : (N : ℝ) * ((cwPressure lam h mhat - δ)
        - cwPressure lam h (mGrid N k₀))
        ≤ (N : ℝ) * (-(3 * δ / 4)) :=
      mul_le_mul_of_nonneg_left (by linarith [hΨk₀]) hN'.le
    nlinarith [h13, hN', hδ0]
  refine squeeze_zero' ?_ hev
    (sq_mul_exp_decay (by linarith : (0 : ℝ) < δ / 2))
  filter_upwards with N
  exact Finset.sum_nonneg fun k _ =>
    fibreMass_nonneg lam h k

set_option maxHeartbeats 1600000 in
-- one-well concentration at a fixed field
/-- **Fixed-field concentration**: the fibre expectation of any
continuous observable converges to its value at the unique
maximizer. -/
theorem cw_weak_conv_fixed (lam h : ℝ)
    (hmem : mhat ∈ Set.Icc (-1 : ℝ) 1)
    (hint : mhat ∈ Set.Ioo (-1 : ℝ) 1)
    (hmax : IsMaxOn (cwPressure lam h) (Set.Icc (-1 : ℝ) 1) mhat)
    (huniq : ∀ m₁ ∈ Set.Icc (-1 : ℝ) 1,
      IsMaxOn (cwPressure lam h) (Set.Icc (-1 : ℝ) 1) m₁
        → m₁ = mhat)
    (G : ℝ → ℝ) (hG : Continuous G) :
    Tendsto (fun N : ℕ => ∑ k ∈ Finset.range (N + 1),
        G (mGrid N k) * fibreMass N lam h k) atTop
      (nhds (G mhat)) := by
  rw [Metric.tendsto_atTop]
  intro ε' hε'
  obtain ⟨M₀, hM₀⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hG.continuousOn (s := Set.Icc (-1 : ℝ) 1))
  set M : ℝ := max M₀ 1 with hM_def
  have hM1 : (1 : ℝ) ≤ M := le_max_right _ _
  have hM0 : (0 : ℝ) < M := by linarith
  have hMb : ∀ m ∈ Set.Icc (-1 : ℝ) 1, |G m| ≤ M := fun m hm =>
    le_trans (hM₀ m hm) (le_max_left _ _)
  obtain ⟨γ, hγ0, hγ⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous
      hG.continuousOn) (ε' / 4) (by linarith)
  set ε : ℝ := γ / 2 with hε_def
  have hε0 : 0 < ε := by
    rw [hε_def]
    linarith
  have hrest := cw_rest_decay_fixed lam h hmem hint hmax huniq
    (ε := ε) hε0
  obtain ⟨N₁, hN₁⟩ := (Metric.tendsto_atTop.mp hrest)
    (ε' / (16 * (M + 1))) (by positivity)
  refine ⟨max N₁ 1, fun N hNge => ?_⟩
  have hN₁' : N₁ ≤ N := le_trans (le_max_left _ _) hNge
  have hNpos : 0 < N := Nat.lt_of_lt_of_le Nat.zero_lt_one
    (le_trans (le_max_right _ _) hNge)
  have hN' : (0 : ℝ) < N := Nat.cast_pos.mpr hNpos
  set massW : ℝ := ∑ k ∈ (Finset.range (N + 1)).filter
    (fun k => |mGrid N k - mhat| < ε),
    fibreMass N lam h k with hmW
  set ρN : ℝ := ∑ k ∈ (Finset.range (N + 1)).filter (fun k =>
    ¬(|mGrid N k - mhat| < ε)),
    fibreMass N lam h k with hρN
  have hρ0 : 0 ≤ ρN := by
    rw [hρN]
    exact Finset.sum_nonneg fun k _ => fibreMass_nonneg lam h k
  have hmassW0 : 0 ≤ massW := by
    rw [hmW]
    exact Finset.sum_nonneg fun k _ => fibreMass_nonneg lam h k
  have hρsmall : ρN ≤ ε' / (16 * (M + 1)) := by
    have h8 := hN₁ N hN₁'
    rw [Real.dist_eq, sub_zero] at h8
    exact le_of_lt (lt_of_abs_lt h8)
  have htotal : massW + ρN = 1 := by
    have h12 := Finset.sum_filter_add_sum_filter_not
      (Finset.range (N + 1)) (fun k => |mGrid N k - mhat| < ε)
      (fibreMass N lam h)
    have h13 := fibreMass_total (N := N) (lam := lam) (h := h)
    rw [← h12] at h13
    rw [hmW, hρN]
    linarith [h13]
  have hmassW1 : massW ≤ 1 := by linarith [htotal, hρ0]
  rw [Real.dist_eq]
  have h14 : G mhat = ∑ k ∈ Finset.range (N + 1),
      G mhat * fibreMass N lam h k := by
    rw [← Finset.mul_sum, fibreMass_total (N := N) (lam := lam)
      (h := h), mul_one]
  have hEdiff : (∑ k ∈ Finset.range (N + 1),
      G (mGrid N k) * fibreMass N lam h k) - G mhat
      = ∑ k ∈ Finset.range (N + 1),
        (G (mGrid N k) - G mhat) * fibreMass N lam h k := by
    conv_lhs => rw [h14]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hEdiff]
  refine lt_of_le_of_lt (Finset.abs_sum_le_sum_abs _ _) ?_
  rw [← Finset.sum_filter_add_sum_filter_not
    (Finset.range (N + 1)) (fun k => |mGrid N k - mhat| < ε)
    (fun k => |(G (mGrid N k) - G mhat)
      * fibreMass N lam h k|)]
  have hpart1 : ∑ k ∈ (Finset.range (N + 1)).filter
      (fun k => |mGrid N k - mhat| < ε),
      |(G (mGrid N k) - G mhat) * fibreMass N lam h k|
      ≤ ε' / 4 * massW := by
    rw [hmW, Finset.mul_sum]
    refine Finset.sum_le_sum fun k hk => ?_
    have hk1 := Finset.mem_filter.mp hk
    have hkN : k ≤ N := Nat.lt_succ_iff.mp
      (Finset.mem_range.mp hk1.1)
    rw [abs_mul, abs_of_nonneg (fibreMass_nonneg lam h k)]
    refine mul_le_mul_of_nonneg_right ?_
      (fibreMass_nonneg lam h k)
    have h17 := hγ (mGrid N k) (mGrid_mem hNpos hkN)
      mhat hmem (by
        rw [Real.dist_eq]
        exact lt_of_lt_of_le hk1.2 (by rw [hε_def]; linarith))
    rw [Real.dist_eq] at h17
    exact h17.le
  have hpart2 : ∑ k ∈ (Finset.range (N + 1)).filter (fun k =>
      ¬(|mGrid N k - mhat| < ε)),
      |(G (mGrid N k) - G mhat) * fibreMass N lam h k|
      ≤ 2 * M * ρN := by
    rw [hρN, Finset.mul_sum]
    refine Finset.sum_le_sum fun k hk => ?_
    have hkN : k ≤ N := Nat.lt_succ_iff.mp
      (Finset.mem_range.mp (Finset.mem_filter.mp hk).1)
    rw [abs_mul, abs_of_nonneg (fibreMass_nonneg lam h k)]
    refine mul_le_mul_of_nonneg_right ?_
      (fibreMass_nonneg lam h k)
    have h18 : |G (mGrid N k)| ≤ M := hMb _ (mGrid_mem hNpos hkN)
    have h19 : |G mhat| ≤ M := hMb mhat hmem
    calc |G (mGrid N k) - G mhat|
        ≤ |G (mGrid N k)| + |G mhat| := by
          rw [sub_eq_add_neg]
          refine le_trans (abs_add_le _ _) ?_
          rw [abs_neg]
      _ ≤ 2 * M := by linarith
  have h20 : 2 * M * (ε' / (16 * (M + 1))) < ε' / 4 := by
    rw [← mul_div_assoc, div_lt_div_iff₀ (by positivity)
      (by norm_num : (0 : ℝ) < 4)]
    nlinarith [hM0, hε']
  calc (∑ k ∈ (Finset.range (N + 1)).filter
        (fun k => |mGrid N k - mhat| < ε),
        |(G (mGrid N k) - G mhat) * fibreMass N lam h k|)
      + ∑ k ∈ (Finset.range (N + 1)).filter (fun k =>
          ¬(|mGrid N k - mhat| < ε)),
          |(G (mGrid N k) - G mhat) * fibreMass N lam h k|
      ≤ ε' / 4 * massW + 2 * M * ρN := by
        linarith [hpart1, hpart2]
    _ ≤ ε' / 4 * 1 + 2 * M * (ε' / (16 * (M + 1))) := by
        refine add_le_add ?_ ?_
        · exact mul_le_mul_of_nonneg_left hmassW1 (by linarith)
        · exact mul_le_mul_of_nonneg_left hρsmall (by linarith)
    _ < ε' := by linarith [h20]

/-- **Fixed-field pattern limit**: at a fixed field with unique
pressure maximizer `m̂`, every pattern probability converges to the
`m̂`-Bernoulli value. -/
theorem cw_fixed_field_pattern (lam h : ℝ)
    (hmem : mhat ∈ Set.Icc (-1 : ℝ) 1)
    (hint : mhat ∈ Set.Ioo (-1 : ℝ) 1)
    (hmax : IsMaxOn (cwPressure lam h) (Set.Icc (-1 : ℝ) 1) mhat)
    (huniq : ∀ m₁ ∈ Set.Icc (-1 : ℝ) 1,
      IsMaxOn (cwPressure lam h) (Set.Icc (-1 : ℝ) 1) m₁
        → m₁ = mhat)
    (r : ℕ) (b : Fin r → Bool) :
    Tendsto (fun t : ℕ =>
      ∑ η ∈ Finset.univ.filter (fun η : Fin (r + t) → Bool =>
        ∀ i : Fin r, η (Fin.castAdd t i) = b i),
        cwMeasure (r + t) lam h η)
      atTop (nhds (cylProb r (countTrue r b) mhat)) := by
  set j : ℕ := countTrue r b with hj
  have hjr : j ≤ r := countTrue_le r b
  have hweak := cw_weak_conv_fixed lam h hmem hint hmax huniq
    (cylProb r j) (continuous_cylProb r j)
  have haux : Tendsto (fun t : ℕ => r + t) atTop atTop :=
    (tendsto_add_atTop_nat r).congr fun t => Nat.add_comm t r
  have hcomp := hweak.comp haux
  have hbound : ∀ᶠ t : ℕ in atTop,
      ‖(∑ η ∈ Finset.univ.filter
          (fun η : Fin (r + t) → Bool =>
            ∀ i : Fin r, η (Fin.castAdd t i) = b i),
          cwMeasure (r + t) lam h η)
        - ∑ k ∈ Finset.range (r + t + 1),
            cylProb r j (mGrid (r + t) k)
              * fibreMass (r + t) lam h k‖
      ≤ 2 * (r : ℝ) ^ 2 / (t : ℝ) := by
    filter_upwards [eventually_gt_atTop r] with t htr
    have hNpos : 0 < r + t := by omega
    have h2r : 2 * r < r + t := by omega
    have hdecomp := cw_pattern_decomposition lam h r t hNpos b
    rw [Real.norm_eq_abs, hdecomp, ← hj]
    have hfold : (∑ k ∈ Finset.range (r + t + 1),
        hypWeight (r + t) r j k
        * ∑ η ∈ Finset.univ.filter
            (fun η : Fin (r + t) → Bool =>
              countTrue (r + t) η = k),
          cwMeasure (r + t) lam h η)
        = ∑ k ∈ Finset.range (r + t + 1),
          hypWeight (r + t) r j k
            * fibreMass (r + t) lam h k := rfl
    rw [hfold, ← Finset.sum_sub_distrib]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hterm : ∀ k ∈ Finset.range (r + t + 1),
        |hypWeight (r + t) r j k * fibreMass (r + t) lam h k
          - cylProb r j (mGrid (r + t) k)
            * fibreMass (r + t) lam h k|
        ≤ 2 * (r : ℝ) ^ 2 / (t : ℝ)
            * fibreMass (r + t) lam h k := by
      intro k hk
      have hkN : k ≤ r + t := Nat.lt_succ_iff.mp
        (Finset.mem_range.mp hk)
      rw [← sub_mul, abs_mul, abs_of_nonneg
        (fibreMass_nonneg lam h k)]
      refine mul_le_mul_of_nonneg_right ?_
        (fibreMass_nonneg lam h k)
      rw [cylProb_mGrid hNpos r j]
      have happrox := hypWeight_approx' hjr hkN h2r
      have hcast : ((r + t : ℕ) : ℝ) - r = (t : ℝ) := by
        push_cast
        ring
      rw [hcast] at happrox
      exact happrox
    refine le_trans (Finset.sum_le_sum hterm) ?_
    rw [← Finset.mul_sum]
    rw [fibreMass_total (N := r + t) (lam := lam) (h := h),
      mul_one]
  have hto0 : Tendsto (fun t : ℕ => 2 * (r : ℝ) ^ 2 / (t : ℝ))
      atTop (nhds 0) :=
    Tendsto.div_atTop tendsto_const_nhds
      tendsto_natCast_atTop_atTop
  have hdiff := squeeze_zero_norm' hbound hto0
  have hfinal := hdiff.add hcomp
  rw [zero_add] at hfinal
  refine hfinal.congr fun t => ?_
  simp only [Function.comp_apply]
  ring

end FixedField

/-! ## The two corollaries -/

section Corollaries

open Filter

variable {lam mstar : ℝ}

/-- The zero-field thermodynamic limit is the symmetric two-phase
mixture. -/
theorem cw_zero_field_mixture (hlam : 1 < lam)
    (hmstar : mstar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : Real.tanh (lam * mstar) = mstar)
    (r : ℕ) (b : Fin r → Bool) :
    Tendsto (fun t : ℕ =>
      ∑ η ∈ Finset.univ.filter (fun η : Fin (r + t) → Bool =>
        ∀ i : Fin r, η (Fin.castAdd t i) = b i),
        cwMeasure (r + t) lam 0 η)
      atTop
      (nhds (2⁻¹ * cylProb r (countTrue r b) mstar
        + 2⁻¹ * cylProb r (countTrue r b) (-mstar))) := by
  have hc : Tendsto (fun N : ℕ => (N : ℝ) * (fun _ : ℕ => (0:ℝ)) N)
      atTop (nhds 0) := by
    refine (tendsto_const_nhds (x := (0 : ℝ))).congr fun N => ?_
    ring
  have h0 := cw_spontaneous_orientation hlam hmstar hfix r b
    (fun _ => 0) 0 hc
  have heq : Real.exp ((0 : ℝ) * mstar)
      / (2 * Real.cosh ((0 : ℝ) * mstar))
      * cylProb r (countTrue r b) mstar
      + Real.exp (-((0 : ℝ) * mstar))
        / (2 * Real.cosh ((0 : ℝ) * mstar))
        * cylProb r (countTrue r b) (-mstar)
      = 2⁻¹ * cylProb r (countTrue r b) mstar
        + 2⁻¹ * cylProb r (countTrue r b) (-mstar) := by
    rw [zero_mul, neg_zero, Real.exp_zero, Real.cosh_zero]
    norm_num
  rw [← heq]
  exact h0

/-- **Corollary `cor:cw-evades-finite-no-go`**: the order of limits
is load-bearing.  At `h = 0` the thermodynamic limit of every
pattern probability is the symmetric mixture; at every fixed
`h > 0` it is the pure Bernoulli value at the unique field
maximizer; and those maximizers converge to `m⋆` as `h ↓ 0`. -/
theorem cw_evades_finite_no_go (hlam : 1 < lam)
    (hmstar : mstar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : Real.tanh (lam * mstar) = mstar)
    (r : ℕ) (b : Fin r → Bool) :
    (Tendsto (fun t : ℕ =>
      ∑ η ∈ Finset.univ.filter (fun η : Fin (r + t) → Bool =>
        ∀ i : Fin r, η (Fin.castAdd t i) = b i),
        cwMeasure (r + t) lam 0 η)
      atTop
      (nhds (2⁻¹ * cylProb r (countTrue r b) mstar
        + 2⁻¹ * cylProb r (countTrue r b) (-mstar))))
    ∧ (∀ h : ℝ, 0 < h → ∃ mh : ℝ, 0 < mh ∧ mh < 1
        ∧ Real.tanh (lam * mh + h) = mh
        ∧ Tendsto (fun t : ℕ =>
            ∑ η ∈ Finset.univ.filter
              (fun η : Fin (r + t) → Bool =>
                ∀ i : Fin r, η (Fin.castAdd t i) = b i),
              cwMeasure (r + t) lam h η)
            atTop (nhds (cylProb r (countTrue r b) mh)))
    ∧ (∀ ε > (0 : ℝ), ∃ h₀ > (0 : ℝ), ∀ h : ℝ, 0 < h → h < h₀ →
        ∀ m₀ ∈ Set.Icc (-1 : ℝ) 1,
          IsMaxOn (cwPressure lam h) (Set.Icc (-1 : ℝ) 1) m₀ →
            |m₀ - mstar| < ε) := by
  refine ⟨cw_zero_field_mixture hlam hmstar hfix r b, ?_,
    cw_field_limit hlam hmstar hfix⟩
  intro h hh0
  have hlam0 : (0 : ℝ) ≤ lam := by linarith
  obtain ⟨m₀, ⟨hm₀mem, hm₀max⟩, huniq'⟩ :=
    cw_phase_field hlam0 hh0
  obtain ⟨hp₀, hl₀, htanh, -⟩ :=
    cw_field_max_properties hlam0 hh0 hm₀mem hm₀max
  refine ⟨m₀, hp₀, hl₀, htanh, ?_⟩
  exact cw_fixed_field_pattern lam h hm₀mem
    ⟨by linarith, hl₀⟩ hm₀max
    (fun m₁ hm₁ hmax₁ => huniq' m₁ ⟨hm₁, hmax₁⟩) r b

/-- **Corollary `cor:cw-zero-entropy-orientation`**: the two
oriented phases arise from a sequence of exactly detailed-balanced
renewal systems — spontaneous orientation with zero entropy
production. -/
theorem cw_zero_entropy_orientation (hlam : 1 < lam)
    (hmstar : mstar ∈ Set.Ioo (0 : ℝ) 1)
    (hfix : Real.tanh (lam * mstar) = mstar)
    (r : ℕ) (b : Fin r → Bool) :
    (∀ (N : ℕ) (η : Fin N → Bool) (i : Fin N) (s : Bool),
      cwMeasure N lam 0 η * cwCond N lam 0 η i s
        = cwMeasure N lam 0 (Function.update η i s)
          * cwCond N lam 0 (Function.update η i s) i (η i))
    ∧ Tendsto (fun t : ℕ =>
        ∑ η ∈ Finset.univ.filter (fun η : Fin (r + t) → Bool =>
          ∀ i : Fin r, η (Fin.castAdd t i) = b i),
          cwMeasure (r + t) lam 0 η)
        atTop
        (nhds (2⁻¹ * cylProb r (countTrue r b) mstar
          + 2⁻¹ * cylProb r (countTrue r b) (-mstar))) :=
  ⟨fun N η i s => cw_detailed_balance N lam 0 η i s,
    cw_zero_field_mixture hlam hmstar hfix r b⟩

end Corollaries




















end NCG.Upstream
