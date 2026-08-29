/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.RenewalFluctuationDissipation
import NCG.Grand.RelativeMetricSupportDensity
import NCG.Grand.SqrtPolar

/-!
# Infinite-horizon renewal fluctuation--dissipation

This file closes the infinite-series endpoint of the renewal
fluctuation--dissipation theorem.
-/

open Matrix Filter
open scoped ComplexOrder Matrix.Norms.L2Operator Topology

namespace NCG
namespace RenewalFluctuationDissipationLimit

open RelativeMetricSupportDensity

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- An order bound between positive matrices implies an ordinary operator
norm bound. -/
theorem norm_le_smul_of_posSemidef
    (A H : Matrix n n ℂ) (c : ℝ)
    (hA : A.PosSemidef)
    (hH : H.PosSemidef)
    (hc : 0 ≤ c)
    (hAH : (((c : ℂ) • H) - A).PosSemidef) :
    ‖A‖ ≤ c * ‖H‖ := by
  have hHnorm :
      ((((‖H‖ : ℝ) : ℂ) • (1 : Matrix n n ℂ)) - H).PosSemidef :=
    (posSemidef_norm_le_iff_scalar_deficit
      H hH ‖H‖ (norm_nonneg H)).mp le_rfl
  have hcC : (0 : ℂ) ≤ (c : ℂ) := by
    rw [Complex.nonneg_iff]
    exact ⟨hc, rfl⟩
  have hdef := hAH.add (hHnorm.smul hcC)
  have heq :
      ((c : ℂ) • H - A) +
          (c : ℂ) • ((((‖H‖ : ℝ) : ℂ) • 1) - H)
        = (((c * ‖H‖ : ℝ) : ℂ) • (1 : Matrix n n ℂ)) - A := by
    module
  rw [heq] at hdef
  exact (posSemidef_norm_le_iff_scalar_deficit
    A hA (c * ‖H‖) (mul_nonneg hc (norm_nonneg H))).mpr hdef

/-- The infinite stationary covariance series. -/
noncomputable def stationaryCovariance
    (K Q : Matrix n n ℂ) : Matrix n n ℂ :=
  ∑' k : ℕ, Kᴴ ^ k * Q * K ^ k

/-- Strict contraction in the positive metric gives geometric decay of its
transported metric endpoint in the ordinary operator norm. -/
theorem metricEndpoint_norm_le
    (H K : Matrix n n ℂ) (q : ℝ)
    (hH : H.PosSemidef) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hcontract : (((q ^ 2 : ℝ) : ℂ) • H - Kᴴ * H * K).PosSemidef) :
    ∀ k : ℕ, ‖Kᴴ ^ k * H * K ^ k‖ ≤ (q ^ 2) ^ k * ‖H‖ := by
  have hq2 : q ^ 2 ≤ 1 := by nlinarith
  have hmargin :
      ((H - Kᴴ * H * K) - ((1 - q ^ 2 : ℝ) : ℂ) • H).PosSemidef := by
    convert hcontract using 1 <;> module
  have hdecay := (renewal_complete_observability
    K H (0 : Matrix n n ℂ) (1 - q ^ 2)
    (by nlinarith) (by nlinarith) hH hmargin).2.1
  intro k
  have hkpsd : (Kᴴ ^ k * H * K ^ k).PosSemidef := by
    simpa [Matrix.conjTranspose_pow] using
      hH.conjTranspose_mul_mul_same (K ^ k)
  have hdecayPrime :
      ((((q ^ 2) ^ k : ℝ) : ℂ) • H -
        Kᴴ ^ k * H * K ^ k).PosSemidef := by
    convert hdecay k using 1 <;> push_cast <;> ring
  exact norm_le_smul_of_posSemidef
    (Kᴴ ^ k * H * K ^ k) H ((q ^ 2) ^ k)
    hkpsd hH (pow_nonneg (sq_nonneg q) k) hdecayPrime

/-- Every covariance term has a geometric norm majorant. -/
theorem covarianceTerm_norm_le
    (H K Q : Matrix n n ℂ) (q dplus : ℝ)
    (hH : H.PosSemidef) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hdplus : 0 ≤ dplus)
    (hcontract : (((q ^ 2 : ℝ) : ℂ) • H - Kᴴ * H * K).PosSemidef)
    (hQ : Q.PosSemidef)
    (hplus : (((dplus : ℂ) • (H - Kᴴ * H * K)) - Q).PosSemidef) :
    ∀ k : ℕ,
      ‖Kᴴ ^ k * Q * K ^ k‖ ≤
        dplus * ‖H‖ * (q ^ 2) ^ k := by
  intro k
  let T := Kᴴ ^ k * Q * K ^ k
  have hT : T.PosSemidef := by
    dsimp [T]
    simpa [Matrix.conjTranspose_pow] using
      hQ.conjTranspose_mul_mul_same (K ^ k)
  have hconj := hplus.conjTranspose_mul_mul_same (K ^ k)
  have hKH : (Kᴴ * H * K).PosSemidef :=
    hH.conjTranspose_mul_mul_same K
  have hdrop := hKH.conjTranspose_mul_mul_same (K ^ k)
  have hdplusC : (0 : ℂ) ≤ (dplus : ℂ) := by
    rw [Complex.nonneg_iff]
    exact ⟨hdplus, rfl⟩
  have hscaled := hdrop.smul hdplusC
  have hDle :
      ((dplus : ℂ) • (Kᴴ ^ k * H * K ^ k) - T).PosSemidef := by
    dsimp [T] at hconj ⊢
    have hadd := hconj.add hscaled
    convert hadd using 1 <;>
      simp only [Matrix.conjTranspose_pow, Matrix.mul_sub, Matrix.sub_mul,
        Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc] <;> module
  have hmargin :
      ((H - Kᴴ * H * K) - ((1 - q ^ 2 : ℝ) : ℂ) • H).PosSemidef := by
    convert hcontract using 1 <;> module
  have hdecay := (renewal_complete_observability
    K H (0 : Matrix n n ℂ) (1 - q ^ 2)
    (by nlinarith) (by nlinarith [sq_nonneg q]) hH hmargin).2.1 k
  have hdecayPrime :
      ((((q ^ 2) ^ k : ℝ) : ℂ) • H -
        Kᴴ ^ k * H * K ^ k).PosSemidef := by
    convert hdecay using 1 <;> push_cast <;> ring
  have hmetricOrder :
      ((((dplus * (q ^ 2) ^ k : ℝ) : ℂ) • H) - T).PosSemidef := by
    have hs := hdecayPrime.smul hdplusC
    have hadd := hDle.add hs
    convert hadd using 1 <;> module
  have hnorm := norm_le_smul_of_posSemidef T H
    (dplus * (q ^ 2) ^ k) hT hH
    (mul_nonneg hdplus (pow_nonneg (sq_nonneg q) k)) hmetricOrder
  calc
    ‖T‖ ≤ (dplus * (q ^ 2) ^ k) * ‖H‖ := hnorm
    _ = dplus * ‖H‖ * (q ^ 2) ^ k := by ring

/-- The covariance series is norm summable under the two-sided
fluctuation--dissipation window. -/
theorem summable_covarianceSeries
    (H K Q : Matrix n n ℂ) (q dminus dplus : ℝ)
    (hH : H.PosSemidef) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hdminus : 0 ≤ dminus) (hdplus : 0 ≤ dplus)
    (hcontract : (((q ^ 2 : ℝ) : ℂ) • H - Kᴴ * H * K).PosSemidef)
    (hminus : (Q - (dminus : ℂ) • (H - Kᴴ * H * K)).PosSemidef)
    (hplus : ((dplus : ℂ) • (H - Kᴴ * H * K) - Q).PosSemidef) :
    Summable fun k : ℕ => Kᴴ ^ k * Q * K ^ k := by
  have hq2lt : q ^ 2 < 1 := by nlinarith
  have hD : (H - Kᴴ * H * K).PosSemidef := by
    have hrest : (((1 - q ^ 2 : ℝ) : ℂ) • H).PosSemidef :=
      hH.smul (by
        exact_mod_cast (sub_nonneg.mpr hq2lt.le))
    have hadd := hcontract.add hrest
    convert hadd using 1 <;> module
  have hQ : Q.PosSemidef := by
    have hscaled : ((dminus : ℂ) • (H - Kᴴ * H * K)).PosSemidef :=
      hD.smul (by
        rw [Complex.nonneg_iff]
        exact ⟨hdminus, rfl⟩)
    have hadd := hminus.add hscaled
    convert hadd using 1 <;> module
  have hmajor : Summable fun k : ℕ =>
      dplus * ‖H‖ * (q ^ 2) ^ k :=
    (summable_geometric_of_lt_one (sq_nonneg q) hq2lt).mul_left
      (dplus * ‖H‖)
  exact Summable.of_norm_bounded hmajor
    (covarianceTerm_norm_le H K Q q dplus hH hq0 hq1
      hdplus hcontract hQ hplus)

/-- A norm-summable series of positive-semidefinite matrices has a
positive-semidefinite sum. -/
theorem posSemidef_tsum (f : ℕ → Matrix n n ℂ)
    (hsum : Summable f) (hf : ∀ k, (f k).PosSemidef) :
    (∑' k, f k).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · change (∑' k, f k)ᴴ = ∑' k, f k
    rw [Matrix.conjTranspose_tsum]
    exact tsum_congr fun k => (hf k).isHermitian.eq
  · intro x
    let evalQuadratic : Matrix n n ℂ →L[ℂ] ℂ :=
      LinearMap.toContinuousLinearMap
        { toFun := fun M => star x ⬝ᵥ (M *ᵥ x)
          map_add' := by
            intro A B
            simp [Matrix.add_mulVec, dotProduct_add]
          map_smul' := by
            intro c A
            simp [Matrix.smul_mulVec, dotProduct_smul] }
    have hq := hsum.hasSum.mapL evalQuadratic
    change HasSum (fun k => star x ⬝ᵥ (f k *ᵥ x))
      (star x ⬝ᵥ ((∑' k, f k) *ᵥ x)) at hq
    rw [← hq.tsum_eq]
    exact tsum_nonneg fun k => (hf k).dotProduct_mulVec_nonneg x

/-- The transported metric endpoint vanishes in operator norm. -/
theorem metricEndpoint_tendsto_zero
    (H K : Matrix n n ℂ) (q : ℝ)
    (hH : H.PosSemidef) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hcontract : (((q ^ 2 : ℝ) : ℂ) • H - Kᴴ * H * K).PosSemidef) :
    Tendsto (fun k : ℕ => Kᴴ ^ k * H * K ^ k) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hq2lt : q ^ 2 < 1 := by nlinarith
  have hmajor : Tendsto (fun k : ℕ => (q ^ 2) ^ k * ‖H‖)
      atTop (𝓝 0) := by
    simpa using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (sq_nonneg q) hq2lt).mul_const ‖H‖
  exact squeeze_zero
    (fun _ => norm_nonneg _)
    (metricEndpoint_norm_le H K q hH hq0 hq1 hcontract)
    hmajor

/-- The metric defect is a complete observability density: its infinite
transport series sums exactly to the metric. -/
theorem transportDefect_tsum_eq
    (H K : Matrix n n ℂ) (q : ℝ)
    (hH : H.PosSemidef) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hcontract : (((q ^ 2 : ℝ) : ℂ) • H - Kᴴ * H * K).PosSemidef) :
    Summable (fun k : ℕ =>
        Kᴴ ^ k * (H - Kᴴ * H * K) * K ^ k)
      ∧ (∑' k : ℕ, Kᴴ ^ k * (H - Kᴴ * H * K) * K ^ k) = H := by
  have hq2lt : q ^ 2 < 1 := by nlinarith
  have hD : (H - Kᴴ * H * K).PosSemidef := by
    have hrest : (((1 - q ^ 2 : ℝ) : ℂ) • H).PosSemidef :=
      hH.smul (by exact_mod_cast (sub_nonneg.mpr hq2lt.le))
    have hadd := hcontract.add hrest
    convert hadd using 1 <;> module
  have hsum : Summable (fun k : ℕ =>
      Kᴴ ^ k * (H - Kᴴ * H * K) * K ^ k) :=
    summable_covarianceSeries H K (H - Kᴴ * H * K) q 0 1
      hH hq0 hq1 (by positivity) (by positivity) hcontract
      (by simpa using hD) (by simpa using Matrix.PosSemidef.zero)
  refine ⟨hsum, ?_⟩
  have hpartial := hsum.hasSum.tendsto_sum_nat
  have htel : ∀ N : ℕ,
      (∑ k ∈ Finset.range N,
          Kᴴ ^ k * (H - Kᴴ * H * K) * K ^ k)
        = H - Kᴴ ^ N * H * K ^ N := by
    intro N
    exact (renewal_complete_observability K H
      (0 : Matrix n n ℂ) (1 - q ^ 2)
      (by nlinarith) (by nlinarith) hH
      (by convert hcontract using 1 <;> module)).2.2 N |>.1
  rw [show (fun N : ℕ => ∑ k ∈ Finset.range N,
      Kᴴ ^ k * (H - Kᴴ * H * K) * K ^ k)
      = fun N => H - Kᴴ ^ N * H * K ^ N from funext htel] at hpartial
  have hrhs : Tendsto (fun N : ℕ => H - Kᴴ ^ N * H * K ^ N)
      atTop (𝓝 H) := by
    simpa using tendsto_const_nhds.sub
      (metricEndpoint_tendsto_zero H K q hH hq0 hq1 hcontract)
  exact tendsto_nhds_unique hpartial hrhs

/-- Every covariance summand vanishes in operator norm. -/
theorem covarianceTerm_tendsto_zero
    (H K Q : Matrix n n ℂ) (q dplus : ℝ)
    (hH : H.PosSemidef) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hdplus : 0 ≤ dplus)
    (hcontract : (((q ^ 2 : ℝ) : ℂ) • H - Kᴴ * H * K).PosSemidef)
    (hQ : Q.PosSemidef)
    (hplus : (((dplus : ℂ) • (H - Kᴴ * H * K)) - Q).PosSemidef) :
    Tendsto (fun k : ℕ => Kᴴ ^ k * Q * K ^ k) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hq2lt : q ^ 2 < 1 := by nlinarith
  have hmajor : Tendsto
      (fun k : ℕ => dplus * ‖H‖ * (q ^ 2) ^ k) atTop (𝓝 0) := by
    simpa [mul_assoc] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (sq_nonneg q) hq2lt).const_mul
        (dplus * ‖H‖)
  exact squeeze_zero (fun _ => norm_nonneg _)
    (covarianceTerm_norm_le H K Q q dplus hH hq0 hq1
      hdplus hcontract hQ hplus) hmajor

/-- Infinite-horizon fluctuation--dissipation: the covariance series is
positive, solves the Lyapunov equation, and lies in the exact two-sided
metric window. -/
theorem renewalFluctuationDissipation_infinite
    (H K Q : Matrix n n ℂ) (q dminus dplus : ℝ)
    (hH : H.PosSemidef) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hdminus : 0 ≤ dminus) (hdle : dminus ≤ dplus)
    (hcontract : (((q ^ 2 : ℝ) : ℂ) • H - Kᴴ * H * K).PosSemidef)
    (hminus : (Q - (dminus : ℂ) • (H - Kᴴ * H * K)).PosSemidef)
    (hplus : ((dplus : ℂ) • (H - Kᴴ * H * K) - Q).PosSemidef) :
    let Sigma := stationaryCovariance K Q
    Summable (fun k : ℕ => Kᴴ ^ k * Q * K ^ k)
      ∧ Sigma.PosSemidef
      ∧ Sigma - Kᴴ * Sigma * K = Q
      ∧ (Sigma - (dminus : ℂ) • H).PosSemidef
      ∧ ((dplus : ℂ) • H - Sigma).PosSemidef := by
  dsimp only
  have hdplus : 0 ≤ dplus := le_trans hdminus hdle
  have hq2lt : q ^ 2 < 1 := by nlinarith
  let D := H - Kᴴ * H * K
  let fQ : ℕ → Matrix n n ℂ := fun k => Kᴴ ^ k * Q * K ^ k
  let fD : ℕ → Matrix n n ℂ := fun k => Kᴴ ^ k * D * K ^ k
  have hD : D.PosSemidef := by
    have hrest : (((1 - q ^ 2 : ℝ) : ℂ) • H).PosSemidef :=
      hH.smul (by exact_mod_cast (sub_nonneg.mpr hq2lt.le))
    have hadd := hcontract.add hrest
    dsimp [D]
    convert hadd using 1 <;> module
  have hQ : Q.PosSemidef := by
    have hscaled : ((dminus : ℂ) • D).PosSemidef :=
      hD.smul (by exact_mod_cast hdminus)
    have hadd := hminus.add hscaled
    dsimp [D] at hadd
    convert hadd using 1 <;> module
  have hQsum : Summable fQ := by
    dsimp [fQ]
    exact summable_covarianceSeries H K Q q dminus dplus
      hH hq0 hq1 hdminus hdplus hcontract hminus hplus
  have hDdata := transportDefect_tsum_eq H K q hH hq0 hq1 hcontract
  have hDsum : Summable fD := by simpa [fD, D] using hDdata.1
  have hDtotal : (∑' k, fD k) = H := by simpa [fD, D] using hDdata.2
  have hSigmaPsd : (∑' k, fQ k).PosSemidef :=
    posSemidef_tsum fQ hQsum fun k => by
      dsimp [fQ]
      simpa [Matrix.conjTranspose_pow] using
        hQ.conjTranspose_mul_mul_same (K ^ k)
  refine ⟨by simpa [fQ] using hQsum, hSigmaPsd, ?_, ?_, ?_⟩
  · have hpartial := hQsum.hasSum.tendsto_sum_nat
    have hlhs : Tendsto
        (fun N => (∑ k ∈ Finset.range N, fQ k) -
          Kᴴ * (∑ k ∈ Finset.range N, fQ k) * K)
        atTop (𝓝 ((∑' k, fQ k) - Kᴴ * (∑' k, fQ k) * K)) :=
      hpartial.sub ((tendsto_const_nhds.mul hpartial).mul tendsto_const_nhds)
    have hend : Tendsto (fun N : ℕ => Kᴴ ^ N * Q * K ^ N)
        atTop (𝓝 0) :=
      covarianceTerm_tendsto_zero H K Q q dplus hH hq0 hq1
        hdplus hcontract hQ hplus
    have hrhs : Tendsto (fun N : ℕ => Q - Kᴴ ^ N * Q * K ^ N)
        atTop (𝓝 Q) := by simpa using tendsto_const_nhds.sub hend
    have htel : (fun N : ℕ =>
        (∑ k ∈ Finset.range N, fQ k) -
          Kᴴ * (∑ k ∈ Finset.range N, fQ k) * K)
        = fun N => Q - Kᴴ ^ N * Q * K ^ N := by
      funext N
      simpa [fQ] using
        (renewal_fluctuation_dissipation H K Q dplus hplus).2.1 N
    rw [htel] at hlhs
    exact tendsto_nhds_unique hlhs hrhs
  · let fminus : ℕ → Matrix n n ℂ := fun k =>
      Kᴴ ^ k * (Q - (dminus : ℂ) • D) * K ^ k
    have hfminus : fminus = fun k => fQ k - (dminus : ℂ) • fD k := by
      funext k
      simp only [fminus, fQ, fD, Matrix.mul_sub, Matrix.sub_mul,
        Matrix.mul_smul, Matrix.smul_mul]
    have hminusSum : Summable fminus := by
      rw [hfminus]
      exact hQsum.sub (hDsum.smul (dminus : ℂ))
    have hminusPsd : ∀ k, (fminus k).PosSemidef := by
      intro k
      dsimp [fminus, D]
      simpa [Matrix.conjTranspose_pow] using
        hminus.conjTranspose_mul_mul_same (K ^ k)
    have hlimit : (∑' k, fminus k) =
        (∑' k, fQ k) - (dminus : ℂ) • H := by
      have hp := hminusSum.hasSum.tendsto_sum_nat
      have hQlim := hQsum.hasSum.tendsto_sum_nat
      have hDlim := hDsum.hasSum.tendsto_sum_nat
      have htarget : Tendsto
          (fun N => (∑ k ∈ Finset.range N, fQ k) -
            (dminus : ℂ) • (∑ k ∈ Finset.range N, fD k))
          atTop (𝓝 ((∑' k, fQ k) - (dminus : ℂ) • H)) := by
        simpa [hDtotal] using hQlim.sub (tendsto_const_nhds.smul hDlim)
      have hfinite : (fun N => ∑ k ∈ Finset.range N, fminus k)
          = fun N => (∑ k ∈ Finset.range N, fQ k) -
            (dminus : ℂ) • (∑ k ∈ Finset.range N, fD k) := by
        funext N
        simp only [hfminus, Finset.sum_sub_distrib, Finset.smul_sum]
      rw [hfinite] at hp
      exact tendsto_nhds_unique hp htarget
    rw [← hlimit]
    exact posSemidef_tsum fminus hminusSum hminusPsd
  · let fplus : ℕ → Matrix n n ℂ := fun k =>
      Kᴴ ^ k * ((dplus : ℂ) • D - Q) * K ^ k
    have hfplus : fplus = fun k => (dplus : ℂ) • fD k - fQ k := by
      funext k
      simp only [fplus, fQ, fD, Matrix.mul_sub, Matrix.sub_mul,
        Matrix.mul_smul, Matrix.smul_mul]
    have hplusSum : Summable fplus := by
      rw [hfplus]
      exact (hDsum.smul (dplus : ℂ)).sub hQsum
    have hplusPsd : ∀ k, (fplus k).PosSemidef := by
      intro k
      dsimp [fplus, D]
      simpa [Matrix.conjTranspose_pow] using
        hplus.conjTranspose_mul_mul_same (K ^ k)
    have hlimit : (∑' k, fplus k) =
        (dplus : ℂ) • H - (∑' k, fQ k) := by
      have hp := hplusSum.hasSum.tendsto_sum_nat
      have hQlim := hQsum.hasSum.tendsto_sum_nat
      have hDlim := hDsum.hasSum.tendsto_sum_nat
      have htarget : Tendsto
          (fun N => (dplus : ℂ) • (∑ k ∈ Finset.range N, fD k) -
            (∑ k ∈ Finset.range N, fQ k))
          atTop (𝓝 ((dplus : ℂ) • H - (∑' k, fQ k))) := by
        simpa [hDtotal] using
          (tendsto_const_nhds.smul hDlim).sub hQlim
      have hfinite : (fun N => ∑ k ∈ Finset.range N, fplus k)
          = fun N => (dplus : ℂ) • (∑ k ∈ Finset.range N, fD k) -
            (∑ k ∈ Finset.range N, fQ k) := by
        funext N
        simp only [hfplus, Finset.sum_sub_distrib, Finset.smul_sum]
      rw [hfinite] at hp
      exact tendsto_nhds_unique hp htarget
    rw [← hlimit]
    exact posSemidef_tsum fplus hplusSum hplusPsd

/-- Every positive-semidefinite matrix is bounded above by a scalar multiple
of a positive-definite metric.  The proof uses the inverse metric square root
and is valid for any finite index type. -/
theorem posSemidef_le_smul_posDef
    (H X : Matrix n n ℂ) (hH : H.PosDef) (hX : X.PosSemidef) :
    ∃ c : ℝ, 0 ≤ c ∧ (((c : ℂ) • H) - X).PosSemidef := by
  let S := CFC.sqrt H
  have hSu : IsUnit S := sqrt_isUnit hH
  letI : Invertible S := hSu.invertible
  let R := S⁻¹
  let A := R * X * R
  have hRH : Rᴴ = R := by
    dsimp [R, S]
    exact sqrt_inv_isHermitian H
  have hA : A.PosSemidef := by
    dsimp [A]
    rw [← hRH]
    exact hX.conjTranspose_mul_mul_same R
  let c : ℝ := ‖A‖
  have hc : 0 ≤ c := norm_nonneg A
  have hdef : ((((c : ℝ) : ℂ) • (1 : Matrix n n ℂ)) - A).PosSemidef :=
    (posSemidef_norm_le_iff_scalar_deficit A hA c hc).mp le_rfl
  have hconj := hdef.conjTranspose_mul_mul_same S
  refine ⟨c, hc, ?_⟩
  have hSH : Sᴴ = S := by
    dsimp [S]
    exact sqrt_isHermitian H
  have hS2 : S * S = H := by
    dsimp [S]
    exact sqrt_mul_self_eq H hH.posSemidef
  have heq :
      Sᴴ * ((((c : ℝ) : ℂ) • (1 : Matrix n n ℂ)) - A) * S
        = ((c : ℂ) • H) - X := by
    rw [hSH]
    dsimp [A, R]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_assoc, Matrix.mul_one, Matrix.one_mul]
    rw [Matrix.mul_inv_of_invertible, Matrix.inv_mul_of_invertible, hS2]
  rwa [heq] at hconj

/-- A positive-semidefinite endpoint transported by a strict metric
contraction vanishes, even when the endpoint is not itself bounded in the
ordinary norm by the metric a priori. -/
theorem posSemidefEndpoint_tendsto_zero
    (H K X : Matrix n n ℂ) (q : ℝ)
    (hH : H.PosDef) (hX : X.PosSemidef)
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hcontract : (((q ^ 2 : ℝ) : ℂ) • H - Kᴴ * H * K).PosSemidef) :
    Tendsto (fun k : ℕ => Kᴴ ^ k * X * K ^ k) atTop (𝓝 0) := by
  obtain ⟨c, hc, hdom⟩ := posSemidef_le_smul_posDef H X hH hX
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hq2lt : q ^ 2 < 1 := by nlinarith
  have hmajor : Tendsto
      (fun k : ℕ => c * ‖H‖ * (q ^ 2) ^ k) atTop (𝓝 0) := by
    simpa [mul_assoc] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (sq_nonneg q) hq2lt).const_mul
        (c * ‖H‖)
  apply squeeze_zero (fun _ => norm_nonneg _) _ hmajor
  intro k
  have hXk : (Kᴴ ^ k * X * K ^ k).PosSemidef := by
    simpa [Matrix.conjTranspose_pow] using
      hX.conjTranspose_mul_mul_same (K ^ k)
  have hHk : (Kᴴ ^ k * H * K ^ k).PosSemidef := by
    simpa [Matrix.conjTranspose_pow] using
      hH.posSemidef.conjTranspose_mul_mul_same (K ^ k)
  have hkdom :
      ((c : ℂ) • (Kᴴ ^ k * H * K ^ k) -
        Kᴴ ^ k * X * K ^ k).PosSemidef := by
    have hk := hdom.conjTranspose_mul_mul_same (K ^ k)
    convert hk using 1 <;>
      simp only [Matrix.conjTranspose_pow, Matrix.mul_sub, Matrix.sub_mul,
        Matrix.mul_smul, Matrix.smul_mul]
  calc
    ‖Kᴴ ^ k * X * K ^ k‖
        ≤ c * ‖Kᴴ ^ k * H * K ^ k‖ :=
      norm_le_smul_of_posSemidef _ _ c hXk hHk hc hkdom
    _ ≤ c * ((q ^ 2) ^ k * ‖H‖) :=
      mul_le_mul_of_nonneg_left
        (metricEndpoint_norm_le H K q hH.posSemidef hq0 hq1 hcontract k) hc
    _ = c * ‖H‖ * (q ^ 2) ^ k := by ring

/-- Iterating a discrete Lyapunov equation produces the exact finite
covariance sum plus the transported endpoint. -/
theorem lyapunov_iterate
    (K Q X : Matrix n n ℂ)
    (hlyap : X - Kᴴ * X * K = Q) :
    ∀ N : ℕ, X =
      (∑ k ∈ Finset.range N, Kᴴ ^ k * Q * K ^ k) +
        Kᴴ ^ N * X * K ^ N := by
  have hrec : X = Q + Kᴴ * X * K := by
    rw [← hlyap]
    module
  intro N
  induction N with
  | zero => simp
  | succ N ih =>
      have hstep :
          Kᴴ ^ N * X * K ^ N =
            Kᴴ ^ N * Q * K ^ N +
              Kᴴ ^ (N + 1) * X * K ^ (N + 1) := by
        calc
          Kᴴ ^ N * X * K ^ N
              = Kᴴ ^ N * (Q + Kᴴ * X * K) * K ^ N := by rw [← hrec]
          _ = Kᴴ ^ N * Q * K ^ N +
                Kᴴ ^ (N + 1) * X * K ^ (N + 1) := by
              rw [Matrix.mul_add, Matrix.add_mul]
              congr 1
              simp only [pow_succ, pow_succ', Matrix.mul_assoc]
      calc
        X = (∑ k ∈ Finset.range N, Kᴴ ^ k * Q * K ^ k) +
              Kᴴ ^ N * X * K ^ N := ih
        _ = (∑ k ∈ Finset.range N, Kᴴ ^ k * Q * K ^ k) +
              (Kᴴ ^ N * Q * K ^ N +
                Kᴴ ^ (N + 1) * X * K ^ (N + 1)) := by rw [hstep]
        _ = ((∑ k ∈ Finset.range N, Kᴴ ^ k * Q * K ^ k) +
              Kᴴ ^ N * Q * K ^ N) +
                Kᴴ ^ (N + 1) * X * K ^ (N + 1) := by abel
        _ = (∑ k ∈ Finset.range (N + 1),
              Kᴴ ^ k * Q * K ^ k) +
                Kᴴ ^ (N + 1) * X * K ^ (N + 1) := by
              rw [Finset.sum_range_succ]

/-- Under strict contraction in a positive-definite metric, the stationary
series is the unique positive-semidefinite solution of the Lyapunov
equation. -/
theorem lyapunov_unique_posSemidef
    (H K Q X : Matrix n n ℂ) (q : ℝ)
    (hH : H.PosDef) (hX : X.PosSemidef)
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hcontract : (((q ^ 2 : ℝ) : ℂ) • H - Kᴴ * H * K).PosSemidef)
    (hsum : Summable fun k : ℕ => Kᴴ ^ k * Q * K ^ k)
    (hlyap : X - Kᴴ * X * K = Q) :
    X = stationaryCovariance K Q := by
  have hpartial := hsum.hasSum.tendsto_sum_nat
  have hend := posSemidefEndpoint_tendsto_zero
    H K X q hH hX hq0 hq1 hcontract
  have hrhs : Tendsto
      (fun N : ℕ =>
        (∑ k ∈ Finset.range N, Kᴴ ^ k * Q * K ^ k) +
          Kᴴ ^ N * X * K ^ N)
      atTop (𝓝 (stationaryCovariance K Q)) := by
    dsimp [stationaryCovariance]
    simpa using hpartial.add hend
  have hconst : Tendsto (fun _ : ℕ => X) atTop (𝓝 X) :=
    tendsto_const_nhds
  have hfun : (fun _ : ℕ => X) = fun N =>
      (∑ k ∈ Finset.range N, Kᴴ ^ k * Q * K ^ k) +
        Kᴴ ^ N * X * K ^ N := by
    funext N
    exact lyapunov_iterate K Q X hlyap N
  rw [hfun] at hconst
  exact tendsto_nhds_unique hconst hrhs

/-- `thm:renewal-fluctuation-dissipation`, with the manuscript's full
infinite series, exact Lyapunov equation, two-sided noncollapse window, and
uniqueness among positive-semidefinite solutions. -/
theorem renewal_fluctuation_dissipation_limit
    (H K Q : Matrix n n ℂ) (q dminus dplus : ℝ)
    (hH : H.PosDef) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hdminus : 0 < dminus) (hdle : dminus ≤ dplus)
    (hcontract : (((q ^ 2 : ℝ) : ℂ) • H - Kᴴ * H * K).PosSemidef)
    (hminus : (Q - (dminus : ℂ) • (H - Kᴴ * H * K)).PosSemidef)
    (hplus : ((dplus : ℂ) • (H - Kᴴ * H * K) - Q).PosSemidef) :
    let Sigma := stationaryCovariance K Q
    (Sigma.PosSemidef
      ∧ Sigma - Kᴴ * Sigma * K = Q
      ∧ (Sigma - (dminus : ℂ) • H).PosSemidef
      ∧ ((dplus : ℂ) • H - Sigma).PosSemidef)
    ∧ (∀ X : Matrix n n ℂ, X.PosSemidef →
        X - Kᴴ * X * K = Q → X = Sigma) := by
  dsimp only
  have hmain := renewalFluctuationDissipation_infinite
    H K Q q dminus dplus hH.posSemidef hq0 hq1
      hdminus.le hdle hcontract hminus hplus
  refine ⟨⟨hmain.2.1, hmain.2.2.1, hmain.2.2.2.1,
    hmain.2.2.2.2⟩, ?_⟩
  intro X hX hlyap
  exact lyapunov_unique_posSemidef H K Q X q hH hX hq0 hq1
    hcontract hmain.1 hlyap

/-- The manuscript's scalar spectral window follows from the exact relative
metric window. -/
theorem renewal_fluctuation_dissipation_uniform_window
    (H K Q Sigma : Matrix n n ℂ) (dminus dplus m M : ℝ)
    (hdminus : 0 ≤ dminus) (hdle : dminus ≤ dplus)
    (hlower : (H - (m : ℂ) • (1 : Matrix n n ℂ)).PosSemidef)
    (hupper : ((M : ℂ) • (1 : Matrix n n ℂ) - H).PosSemidef)
    (hSigmaLower : (Sigma - (dminus : ℂ) • H).PosSemidef)
    (hSigmaUpper : ((dplus : ℂ) • H - Sigma).PosSemidef) :
    (Sigma - ((dminus * m : ℝ) : ℂ) • (1 : Matrix n n ℂ)).PosSemidef
      ∧ (((dplus * M : ℝ) : ℂ) • (1 : Matrix n n ℂ) - Sigma).PosSemidef := by
  have hdplus : 0 ≤ dplus := hdminus.trans hdle
  constructor
  · have hs := hlower.smul (by exact_mod_cast hdminus)
    have hadd := hSigmaLower.add hs
    convert hadd using 1 <;> module
  · have hs := hupper.smul (by exact_mod_cast hdplus)
    have hadd := hSigmaUpper.add hs
    convert hadd using 1 <;> module

/-- In the equal-marginal consecutive-boundary case, the innovation is the
metric defect and its stationary covariance is exactly `H`. -/
theorem stationary_consecutiveBoundary_covariance_eq_metric
    (H K : Matrix n n ℂ) (q : ℝ)
    (hH : H.PosDef) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hcontract : (((q ^ 2 : ℝ) : ℂ) • H - Kᴴ * H * K).PosSemidef) :
    stationaryCovariance K (H - Kᴴ * H * K) = H :=
  (transportDefect_tsum_eq H K q hH.posSemidef hq0 hq1 hcontract).2

end RenewalFluctuationDissipationLimit
end NCG
