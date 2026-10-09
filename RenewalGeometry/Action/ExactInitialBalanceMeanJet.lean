/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Action.ExactLapseHomogeneity
import RenewalGeometry.Action.ExactShiftWardEnvelope

/-!
# The quadratic mean jet of the actual action on the balancing seed
  (`lem:supp-initial-balance`, `eq:supp-initial-quadratic-mean`; emergent-spacetime manuscript)

* `fderiv_fderiv_diag_of_isBigO` (generic): if `f` is analytic at `0` and `f - Q = O(‖X‖³)` for a
  function `Q` with `Q(tX) = t² Q(X)`, then `D²f(0)(v, v) = 2 Q(v)` (power-series uniqueness along
  rays).
* `meanShift_eq`, `eventually_meanShift_eq_Prow`: the spatial mean of the `a`-th shift row of the
  original initial constraint map `Cmap` is the constant-shift row `P_{e_a} = ∂_λ𝓗_h[(0, e_a)]`
  of `ExactShiftWardEnvelope.lean` at `λ = (1, 0)`; by `ShiftWard.Prow_eq` and
  `ShiftWard.Qrow_isBigO` it is `⟨p, δ_a u⟩_h + O(‖X‖³)`, so (`meanShift_second_jet`)
  `D²(P₀ 𝒞_h^{shift,a})(0)(X, X) = 2⟨p, δ_a u⟩_h`.
* `qShift_seed`: `⟨p(ϑ), δ_a u_*⟩_h = -½ω_h b_a` on the seed.
* **`quadratic_mean_jet_seed`** (`eq:supp-initial-quadratic-mean`): for the actual action (`χ = 1`,
  `Λ = 0`, symmetric-square-root triad, odd `N ≥ 3`, `N`-independent threshold on `hR`) all four
  spatial means of the original lapse–shift rows vanish at flat data and their quadratic Taylor
  coefficients on the seed `Z(ϑ) = (u_*, p(ϑ))` are exactly the four components of
  `Q_h(ϑ) = (⅔κ² - ½Σb_i² - ⅜ω_h², -½ω_h b_1, -½ω_h b_2, -½ω_h b_3)`
  (the lapse component is `LapseHomogeneity.lapse_mean_jet_seed`).
-/

open Filter Finset Metric Asymptotics
open scoped Topology

noncomputable section

set_option linter.unusedSectionVars false

namespace RenewalGeometry.ExactPhaseAction.InitialMeanJet

/-! ### A generic second-order uniqueness lemma -/

section Generic

/-- If `a + b t + c t² = O(t³)` at `0`, then `a = b = c = 0`. -/
theorem poly_coeffs_eq_zero {a b c : ℝ}
    (h : (fun t : ℝ => a + b * t + c * t ^ 2) =O[𝓝 0] fun t => ‖t‖ ^ 3) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  obtain ⟨K, hK⟩ := h.bound
  have hK' : ∀ᶠ t in 𝓝[>] (0 : ℝ), |a + b * t + c * t ^ 2| ≤ K * t ^ 3 ∧ 0 < t := by
    filter_upwards [nhdsWithin_le_nhds hK, self_mem_nhdsWithin] with t ht htpos
    have htp : (0 : ℝ) < t := htpos
    refine ⟨?_, htp⟩
    simpa [Real.norm_eq_abs, abs_of_pos htp] using ht
  have ha : a = 0 := by
    have := hK.self_of_nhds
    simp only [mul_zero, zero_pow (by norm_num : (3 : ℕ) ≠ 0), norm_zero, add_zero,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at this
    exact norm_le_zero_iff.1 this
  have hb : b = 0 := by
    have hlim : Tendsto (fun t : ℝ => |c| * t + K * t ^ 2) (𝓝[>] 0) (𝓝 0) := by
      have : Continuous (fun t : ℝ => |c| * t + K * t ^ 2) := by fun_prop
      simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
    have hle : ∀ᶠ t in 𝓝[>] (0 : ℝ), |b| ≤ |c| * t + K * t ^ 2 := by
      filter_upwards [hK'] with t ⟨ht, htp⟩
      rw [ha, zero_add] at ht
      have h1 : |b * t + c * t ^ 2| = t * |b + c * t| := by
        rw [show b * t + c * t ^ 2 = t * (b + c * t) by ring, abs_mul, abs_of_pos htp]
      rw [h1] at ht
      have h2 : |b + c * t| ≤ K * t ^ 2 := by
        have : t * |b + c * t| ≤ t * (K * t ^ 2) := by nlinarith
        exact le_of_mul_le_mul_left this htp
      have h3 : |b| ≤ |b + c * t| + |c * t| := by
        calc |b| = |(b + c * t) + (-(c * t))| := by ring_nf
          _ ≤ |b + c * t| + |-(c * t)| := abs_add_le _ _
          _ = |b + c * t| + |c * t| := by rw [abs_neg]
      rw [abs_mul, abs_of_pos htp] at h3
      linarith
    have := ge_of_tendsto hlim hle
    exact abs_nonpos_iff.1 this
  have hc : c = 0 := by
    have hlim : Tendsto (fun t : ℝ => K * t) (𝓝[>] 0) (𝓝 0) := by
      have : Continuous (fun t : ℝ => K * t) := by fun_prop
      simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
    have hle : ∀ᶠ t in 𝓝[>] (0 : ℝ), |c| ≤ K * t := by
      filter_upwards [hK'] with t ⟨ht, htp⟩
      rw [ha, hb, zero_add, zero_mul, zero_add, abs_mul, abs_of_pos (pow_pos htp 2)] at ht
      have : t ^ 2 * |c| ≤ t ^ 2 * (K * t) := by nlinarith
      exact le_of_mul_le_mul_left this (pow_pos htp 2)
    have := ge_of_tendsto hlim hle
    exact abs_nonpos_iff.1 this
  exact ⟨ha, hb, hc⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Second-order uniqueness along rays.**  If `f` is analytic at `0` and `f - Q = O(‖X‖³)`,
where `Q(tX) = t² Q(X)`, then `D²f(0)(v, v) = 2 Q(v)`. -/
theorem fderiv_fderiv_diag_of_isBigO {f : E → ℝ} (hf : AnalyticAt ℝ f 0) {Q : E → ℝ}
    (hQ : ∀ (t : ℝ) (X : E), Q (t • X) = t ^ 2 * Q X)
    (h : (fun X => f X - Q X) =O[𝓝 0] fun X => ‖X‖ ^ 3) (v : E) :
    fderiv ℝ (fderiv ℝ f) 0 v v = 2 * Q v := by
  obtain ⟨p, r, hp⟩ := hf
  have hpa : HasFPowerSeriesAt f p 0 := ⟨r, hp⟩
  have hB := hpa.isBigO_sub_partialSum_pow 3
  simp only [zero_add] at hB
  -- `partialSum 3 - Q = O(‖·‖³)`
  have h1 : (fun y : E => p.partialSum 3 y - Q y) =O[𝓝 0] fun y => ‖y‖ ^ 3 := by
    have := h.sub hB
    refine this.congr_left fun y => ?_
    ring
  -- along the ray `t ↦ t • v`
  have hray : Tendsto (fun t : ℝ => t • v) (𝓝 0) (𝓝 0) := by
    have : Continuous (fun t : ℝ => t • v) := by fun_prop
    simpa using this.tendsto 0
  have h2 := h1.comp_tendsto hray
  have h3 : (fun t : ℝ => p.partialSum 3 (t • v) - Q (t • v)) =O[𝓝 0] fun t => ‖t‖ ^ 3 := by
    refine h2.trans (IsBigO.of_bound (‖v‖ ^ 3) (Eventually.of_forall fun t => ?_))
    simp only [Function.comp_apply, norm_smul, mul_pow, norm_pow, norm_norm]
    rw [mul_comm, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  -- the partial sum along the ray is a polynomial in `t`
  have hps : ∀ t : ℝ, p.partialSum 3 (t • v) - Q (t • v) =
      p 0 (fun _ => v) + p 1 (fun _ => v) * t + (p 2 (fun _ => v) - Q v) * t ^ 2 := by
    intro t
    simp only [FormalMultilinearSeries.partialSum, Finset.sum_range_succ, Finset.sum_range_zero,
      zero_add, hQ]
    have hs : ∀ n : ℕ, p n (fun _ => t • v) = t ^ n * p n (fun _ => v) := by
      intro n
      rw [show (fun _ : Fin n => t • v) = fun i => (fun _ : Fin n => t) i • (fun _ : Fin n => v) i
        from rfl, (p n).map_smul_univ]
      simp [Finset.prod_const, smul_eq_mul]
    rw [hs 0, hs 1, hs 2]
    ring
  have h4 : (fun t : ℝ => p 0 (fun _ => v) + p 1 (fun _ => v) * t +
      (p 2 (fun _ => v) - Q v) * t ^ 2) =O[𝓝 0] fun t => ‖t‖ ^ 3 :=
    h3.congr_left hps
  obtain ⟨-, -, hc⟩ := poly_coeffs_eq_zero h4
  have hfs := hp.factorial_smul v 2
  rw [iteratedFDeriv_two_apply] at hfs
  rw [← hfs]
  simp only [Nat.factorial_two, nsmul_eq_mul, Nat.cast_ofNat]
  linarith

end Generic

/-! ### The mean shift rows -/

section Shift

open QuadJet ShiftWard LapseHomogeneity OddPhaseDerivativeReal InitialBalancePhase

variable {N : ℕ} [NeZero N]

/-- The constant shift direction `δβ ≡ e_a`. -/
def dShift (a : Fin 3) : ParF N × MetF N := ((0, 0, fun _ => Pi.single a 1), 0)

theorem sum_shiftDir (a : Fin 3) : ∑ x : Site N, shiftDir x a = (dShift a : ParF N × MetF N) := by
  have h : ∑ x : Site N, (Pi.single x (Pi.single a (1 : ℝ)) : Site N → Fin 3 → ℝ) =
      fun _ => Pi.single a 1 := by
    funext y
    rw [Finset.sum_apply, Finset.sum_pi_single]
    simp
  have e : ∑ x : Site N, shiftDir x a =
      (((0, 0, ∑ x : Site N, (Pi.single x (Pi.single a (1 : ℝ)) : Site N → Fin 3 → ℝ)), 0) :
        ParF N × MetF N) := by
    simp only [shiftDir]
    refine Prod.ext ?_ ?_
    · rw [Prod.fst_sum]
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · rw [Prod.fst_sum]; simp
      · rw [Prod.snd_sum, Prod.fst_sum]; simp
      · rw [Prod.snd_sum, Prod.snd_sum]
    · rw [Prod.snd_sum]; simp
  rw [e, h]
  rfl

/-- The spatial mean `P₀ = h³Σ_x` of the `a`-th shift row of the original initial constraint
map. -/
def meanShift (χ R : ℝ) (a : Fin 3) (X : MetF N × MetF N) : ℝ :=
  hN N ^ 3 * ∑ x, (Cmap χ R X).2 x a

/-- The mean shift row is the derivative of `𝓗_h` along the constant shift `e_a`. -/
theorem meanShift_eq (χ R : ℝ) (a : Fin 3) (X : MetF N × MetF N) :
    meanShift χ R a X = fderiv ℝ (canonH χ R) (qFlat N + iotaX X) (dShift a) := by
  rw [meanShift, Cmap_eq]
  simp only
  have hh : hN N ^ 3 ≠ 0 := pow_ne_zero 3 hN_ne_zero
  rw [← sum_shiftDir, map_sum, ← Finset.mul_sum, ← mul_assoc, mul_inv_cancel₀ hh, one_mul]

theorem embX_lamE (X : MetF N × MetF N) : embX ((X, lamE N) : Xs N × Lam N) = qFlat N + iotaX X := by
  ext <;> simp [embX, lamE, qFlat, zFlat, refMult, iotaX_apply]

theorem embL_shift (a : Fin 3) :
    embL (((0 : Xs N), shiftLam (Pi.single a 1)) : Xs N × Lam N) = dShift a := by
  simp [embL, shiftLam, dShift]

/-- The mean shift row is the constant-shift row `P_{e_a} = ∂_λ𝓗_h[(0, e_a)]` at `λ = (1, 0)`. -/
theorem eventually_meanShift_eq_Prow {χ R : ℝ} {U : Set (CoP N)} (hU : FlatChart χ R U)
    (hχ : χ ≠ 0) (a : Fin 3) :
    ∀ᶠ X in 𝓝 (0 : MetF N × MetF N),
      meanShift χ R a X = Prow χ R (Pi.single a 1) ((X, lamE N) : Xs N × Lam N) := by
  have hH := analyticAt_canonH hU hχ
  have hq : Tendsto (fun X : MetF N × MetF N => qFlat N + iotaX X) (𝓝 0) (𝓝 (qFlat N)) := by
    have : Continuous (fun X : MetF N × MetF N => qFlat N + iotaX X) := by fun_prop
    have h := this.tendsto 0
    rwa [map_zero, add_zero] at h
  filter_upwards [hq.eventually hH.eventually_analyticAt] with X hX
  rw [meanShift_eq]
  have hemb : (fun z : Xs N × Lam N => embX z) =
      fun z => (((flatMet N, 0, 0), 0) : ParF N × MetF N) + embL z := funext embX_eq
  have hd : HasFDerivAt (Hlit χ R) (fderiv ℝ (canonH χ R) (qFlat N + iotaX X) ∘L embL)
      ((X, lamE N) : Xs N × Lam N) := by
    have h1 : HasFDerivAt (fun z : Xs N × Lam N =>
        (((flatMet N, 0, 0), 0) : ParF N × MetF N) + embL z) embL ((X, lamE N) : Xs N × Lam N) :=
      embL.hasFDerivAt.const_add _
    have h2 : HasFDerivAt (canonH χ R) (fderiv ℝ (canonH χ R) (qFlat N + iotaX X))
        ((((flatMet N, 0, 0), 0) : ParF N × MetF N) + embL ((X, lamE N) : Xs N × Lam N)) := by
      rw [← embX_eq, embX_lamE]; exact hX.differentiableAt.hasFDerivAt
    have h3 := h2.comp ((X, lamE N) : Xs N × Lam N) h1
    have e : Hlit χ R = fun z : Xs N × Lam N =>
        canonH χ R ((((flatMet N, 0, 0), 0) : ParF N × MetF N) + embL z) := by
      funext z; simp only [Hlit, ← embX_eq]
    rw [e]; exact h3
  rw [Prow, hd.fderiv, ContinuousLinearMap.comp_apply, embL_shift]

theorem pE_eq : (pE N : Xs N × Lam N) = ((0 : Xs N), lamE N) := rfl

/-- Near flat data the mean shift row is `⟨p, δ_a u⟩_h` plus the cubic remainder `Q_{e_a}`. -/
theorem eventually_meanShift {χ R : ℝ} {U : Set (CoP N)} (hU : FlatChart χ R U)
    (hχ : χ ≠ 0) (a : Fin 3) :
    ∀ᶠ X in 𝓝 (0 : MetF N × MetF N),
      meanShift χ R a X = qShift (Pi.single a 1) X +
        Qrow χ R (Pi.single a 1) ((X, lamE N) : Xs N × Lam N) := by
  have hT : Tendsto (fun X : MetF N × MetF N => ((X, lamE N) : Xs N × Lam N)) (𝓝 0)
      (𝓝 (pE N)) := by
    rw [pE_eq]
    exact (continuous_id.prodMk continuous_const).tendsto 0
  filter_upwards [eventually_meanShift_eq_Prow hU hχ a, hT.eventually (Prow_eq hU hχ _)]
    with X h1 h2
  rw [h1, h2]

/-- The mean shift row differs from `⟨p, δ_a u⟩_h` by `O(‖X‖³)`. -/
theorem meanShift_sub_isBigO {χ R : ℝ} {U : Set (CoP N)} (hU : FlatChart χ R U)
    (hχ : χ ≠ 0) (a : Fin 3) :
    (fun X : MetF N × MetF N => meanShift χ R a X - qShift (Pi.single a 1) X) =O[𝓝 0]
      fun X => ‖X‖ ^ 3 := by
  obtain ⟨C, hC⟩ := Qrow_isBigO hU hχ (Pi.single a 1)
  have hT : Tendsto (fun X : MetF N × MetF N => ((X, lamE N) : Xs N × Lam N)) (𝓝 0)
      (𝓝 (pE N)) := by
    rw [pE_eq]
    exact (continuous_id.prodMk continuous_const).tendsto 0
  refine IsBigO.of_bound C ?_
  filter_upwards [eventually_meanShift hU hχ a, hT.eventually hC] with X h1 h2
  rw [h1, add_sub_cancel_left, norm_pow, norm_norm]
  exact h2

theorem dcMet_smul (c : Fin 3 → ℝ) (t : ℝ) (u : MetF N) : dcMet c (t • u) = t • dcMet c u := by
  funext x
  simp only [dcMet, Pi.smul_apply, map_smul, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_comm]

theorem qShift_smul (c : Fin 3 → ℝ) (t : ℝ) (X : Xs N) :
    qShift c (t • X) = t ^ 2 * qShift c X := by
  simp only [qShift, Prod.smul_fst, Prod.smul_snd, dcMet_smul]
  rw [← pairCov_apply, ← pairCov_apply, map_smul, map_smul]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem analyticAt_meanShift {χ R : ℝ} {U : Set (CoP N)} (hU : FlatChart χ R U)
    (hχ : χ ≠ 0) (a : Fin 3) : AnalyticAt ℝ (meanShift χ R a) (0 : MetF N × MetF N) := by
  have hC := (fderiv_initialConstraint_flat hU hχ).2.1
  have hx : ∀ x : Site N, AnalyticAt ℝ (fun X : MetF N × MetF N => (Cmap χ R X).2 x a) 0 := by
    intro x
    have hL := ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) a).comp
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Site N => Fin 3 → ℝ) x).comp
        (ContinuousLinearMap.snd ℝ (Site N → ℝ) (Site N → Fin 3 → ℝ)))).analyticAt (Cmap χ R 0)
    exact hL.comp hC
  have hs := Finset.analyticAt_sum (𝕜 := ℝ) Finset.univ (fun x _ => hx x)
  rw [Finset.sum_fn] at hs
  exact analyticAt_const.mul hs

/-- **The quadratic jet of the mean shift rows**: `D²(P₀ 𝒞_h^{shift,a})(0)(X, X) = 2⟨p, δ_a u⟩_h`. -/
theorem meanShift_second_jet {χ R : ℝ} {U : Set (CoP N)} (hU : FlatChart χ R U)
    (hχ : χ ≠ 0) (a : Fin 3) (Z : MetF N × MetF N) :
    meanShift (N := N) χ R a 0 = 0 ∧
      fderiv ℝ (fderiv ℝ (meanShift χ R a)) 0 Z Z = 2 * qShift (Pi.single a 1) Z := by
  refine ⟨?_, fderiv_fderiv_diag_of_isBigO (analyticAt_meanShift hU hχ a)
    (fun t X => qShift_smul _ t X) (meanShift_sub_isBigO hU hχ a) Z⟩
  have h0 := (fderiv_initialConstraint_flat hU hχ).1
  simp [meanShift, h0]

/-- `δ_{e_a} u = δ_a u`. -/
theorem dcMet_single (a : Fin 3) (u : MetF N) : dcMet (Pi.single a 1) u = fun x => pd a u x := by
  funext x
  simp only [dcMet]
  rw [Finset.sum_eq_single a]
  · simp
  · intro k _ hk; simp [hk]
  · simp

/-- **The shift components of `Q_h` on the seed**: `⟨p(ϑ), δ_a u_*⟩_h = -½ω_h b_a`. -/
theorem qShift_seed (hNo : Odd N) (h3 : 3 ≤ N) (κ : ℝ) (b : Fin 3 → ℝ) (a : Fin 3) :
    qShift (Pi.single a 1) ((uSeed N, pSeedF N κ b) : Xs N) = -(omega N / 2) * b a := by
  have hh : hN N = ((N : ℝ))⁻¹ := rfl
  simp only [qShift, dcMet_single, pairH, pd_uSeed, phaseDerivFin_uStar hNo h3]
  have e : ∀ x : Site N, (∑ i, ∑ j, symMat (pSeedF N κ b x) i j *
      symMat (matToSymLin ((-(omega N * InitialBalance.sinMode N a (toF x))) •
        InitialBalance.T a)) i j) =
      InitialBalance.frob (InitialBalance.pSeed N κ b (toF x))
        ((-(omega N * InitialBalance.sinMode N a (toF x))) • InitialBalance.T a) := by
    intro x
    have := frob_matToSym (isSym3_pSeed κ b (toF x)) ((isSym3_T a).smul
      (-(omega N * InitialBalance.sinMode N a (toF x))))
    simpa [QuadJet.frob, pSeedF] using this
  simp only [e]
  rw [sum_toF (fun x => InitialBalance.frob (InitialBalance.pSeed N κ b x)
    ((-(omega N * InitialBalance.sinMode N a x)) • InitialBalance.T a)), hh]
  have := InitialBalance.gridInner_pSeed_delta N κ (omega N) b h3 a
  simpa [InitialBalance.gridInner] using this

end Shift

/-! ### Assembly: `eq:supp-initial-quadratic-mean` -/

section Assembly

open QuadJet ShiftWard LapseHomogeneity OddPhaseDerivativeReal

/-- **`lem:supp-initial-balance`, the quadratic mean jet of the full retained action on the seed**
(`eq:supp-initial-quadratic-mean`; `χ = 1`, `Λ = 0`, symmetric-square-root triad, odd `N ≥ 3`).
There is an `N`-independent threshold `ε` such that for `0 < R`, `hR ≤ ε`, the four spatial means
`P₀ = h³Σ_x` of the original lapse–shift rows of `𝒞_h = Cmap 1 R` vanish at flat data and their
quadratic Taylor coefficients on the seed `Z(ϑ) = (u_*, p(ϑ))` are the four components of
`Q_h(ϑ) = (⅔κ² - ½Σ_i b_i² - ⅜ω_h², -½ω_h b_1, -½ω_h b_2, -½ω_h b_3)`, `ω_h = 2h⁻¹ sin(πh)`. -/
theorem quadratic_mean_jet_seed :
    ∃ ε > 0, ∀ (N : ℕ) [NeZero N], Odd N → 3 ≤ N → ∀ R : ℝ, 0 < R → hN N * R ≤ ε →
      ∀ (κ : ℝ) (b : Fin 3 → ℝ),
        (meanLapse (N := N) 1 R 0 = 0 ∧
          1 / 2 * fderiv ℝ (fderiv ℝ (meanLapse (N := N) 1 R)) 0 (uSeed N, pSeedF N κ b)
            (uSeed N, pSeedF N κ b) = (InitialBalance.Qh (omega N) (κ, b)).1) ∧
        ∀ a : Fin 3, meanShift (N := N) 1 R a 0 = 0 ∧
          1 / 2 * fderiv ℝ (fderiv ℝ (meanShift (N := N) 1 R a)) 0 (uSeed N, pSeedF N κ b)
            (uSeed N, pSeedF N κ b) = (InitialBalance.Qh (omega N) (κ, b)).2 a := by
  obtain ⟨ε₀, hε₀, hlapse⟩ := lapse_mean_jet_seed
  obtain ⟨ε₁, hε₁, h₁⟩ := flat_chart 1 one_ne_zero
  refine ⟨min ε₀ ε₁, lt_min hε₀ hε₁, fun N _ hNo h3 R hR hhR κ b => ?_⟩
  refine ⟨hlapse N hNo h3 R hR (hhR.trans (min_le_left _ _)) κ b, fun a => ?_⟩
  obtain ⟨U, hU⟩ := h₁ N R hR (hhR.trans (min_le_right _ _))
  obtain ⟨h0, h2⟩ := meanShift_second_jet hU one_ne_zero a ((uSeed N, pSeedF N κ b))
  refine ⟨h0, ?_⟩
  rw [h2, qShift_seed hNo h3 κ b a]
  simp only [InitialBalance.Qh]
  ring

end Assembly

/-! ### `lem:supp-initial-balance` -/

section Record

open QuadJet LapseHomogeneity OddPhaseDerivativeReal InitialBalance

theorem four_le_omega {N : ℕ} (h3 : 3 ≤ N) : 4 ≤ omega N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hle : (1 / N : ℝ) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hN0 (by norm_num)]
    have : (3 : ℝ) ≤ N := by exact_mod_cast h3
    linarith
  have h := omega_ge_four (1 / N : ℝ) (by positivity) hle
  have e : 2 * (1 / (N : ℝ))⁻¹ * Real.sin (Real.pi * (1 / N)) = omega N := by
    simp only [omega, one_div, inv_inv]
    ring_nf
  linarith

/-- **`lem:supp-initial-balance` (exact four-mode mean calibration)** for the actual action
(`χ = 1`, `Λ = 0`, symmetric-square-root triad, stationary connection `statAst`, Legendre chart at
flat data; odd `N ≥ 3`, `h = 1/N`, `ω_h = 2h⁻¹ sin(πh) = omega N`; `N`-independent threshold on
`hR`):
* the quadratic mean jet of the original lapse–shift rows on the seed is `Q_h(ϑ)`
  (`eq:supp-initial-quadratic-mean`, `quadratic_mean_jet_seed`);
* `Q_h` has the exact root `ϑ_h^* = (3ω_h/4, 0, 0, 0)` with `DQ_h(ϑ_h^*) =
  diag(ω_h, -ω_h/2, -ω_h/2, -ω_h/2)` (`eq:supp-initial-balance-root`), whose inverse
  `jacobianInv` is uniformly bounded (entries `≤ 1/2`, since `ω_h ≥ 4`);
* the opposite sign of the first component is the second root (second branch). -/
theorem supp_initial_balance :
    ∃ ε > 0, ∀ (N : ℕ) [NeZero N], Odd N → 3 ≤ N → ∀ R : ℝ, 0 < R → hN N * R ≤ ε →
      (∀ (κ : ℝ) (b : Fin 3 → ℝ),
        (meanLapse (N := N) 1 R 0 = 0 ∧
          1 / 2 * fderiv ℝ (fderiv ℝ (meanLapse (N := N) 1 R)) 0 (uSeed N, pSeedF N κ b)
            (uSeed N, pSeedF N κ b) = (Qh (omega N) (κ, b)).1) ∧
        ∀ a : Fin 3, meanShift (N := N) 1 R a 0 = 0 ∧
          1 / 2 * fderiv ℝ (fderiv ℝ (meanShift (N := N) 1 R a)) 0 (uSeed N, pSeedF N κ b)
            (uSeed N, pSeedF N κ b) = (Qh (omega N) (κ, b)).2 a) ∧
      Qh (omega N) (3 * omega N / 4, 0) = 0 ∧
      HasFDerivAt (Qh (omega N)) (jacobian (omega N)) (3 * omega N / 4, 0) ∧
      (∀ y, jacobian (omega N) (jacobianInv (omega N) y) = y) ∧
      (∀ y, |(jacobianInv (omega N) y).1| ≤ 1 / 2 * |y.1| ∧
        ∀ i, |(jacobianInv (omega N) y).2 i| ≤ 1 / 2 * |y.2 i|) ∧
      Qh (omega N) (-(3 * omega N / 4), 0) = 0 := by
  obtain ⟨ε, hε, h⟩ := quadratic_mean_jet_seed
  refine ⟨ε, hε, fun N _ hNo h3 R hR hhR => ?_⟩
  have hω := four_le_omega h3
  exact ⟨fun κ b => h N hNo h3 R hR hhR κ b, Qh_root _, Qh_hasFDerivAt _,
    jacobian_jacobianInv _ (by linarith), jacobianInv_apply_bound _ hω, Qh_root_neg _⟩

end Record

end InitialMeanJet

end RenewalGeometry.ExactPhaseAction
