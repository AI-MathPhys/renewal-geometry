/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.AnalyticRayExpansion
import RenewalGeometry.Analysis.PowerSeriesQuotientCoefficients

/-!
# From analytic identities to coefficient identities (Cauchy products)

General bridge from analytic functions of one real variable to formal coefficient identities
(machinery for `thm:supp-finite-acc-coefficients` of the emergent-spacetime manuscript, on top
of `Analysis/PowerSeriesQuotientCoefficients.lean`).

* `AnalyticCauchy.poly_coeff_eq_zero_of_eventually`: a polynomial `∑_{m<k} a^m • c_m` which is
  `O(a^k)` on a right neighbourhood of `0` has vanishing coefficients.
* `AnalyticCauchy.coeff_cauchy_of_apply_eq`: if an operator-valued `D(a)`, a vector `v(a)` and
  `χ(a)` have power series at `0` (coefficients `D_i`, `v_l`, `χ_m`) and `D(a) v(a) = χ(a)` near
  `0`, then `∑_{i ≤ j} D_i v_{j-i} = χ_j` for every `j` (the Cauchy product identity, without any
  product theorem for power series).
* `AnalyticCauchy.coeff_recursion_of_apply_eq`: the recursion
  `D₀ v_j = χ_j - ∑_{i=1}^{j} D_i v_{j-i}` (`eq:supp-finite-acc-recursion`), and with `D₀`
  invertible, `v_j = D₀⁻¹(χ_j - ∑_{i=1}^{j} D_i v_{j-i})`.
* `AnalyticCauchy.analyticAt_inverse_apply`: `a ↦ D(a)⁻¹ χ(a)` is analytic when `D, χ` are and
  `D(0)` is invertible (so `v = D⁻¹χ` has a power series).
-/

open Filter Finset Asymptotics
open scoped Topology

namespace RenewalGeometry
namespace AnalyticCauchy

/-! ### Polynomials that are `O(a^k)` -/

section Poly

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Filter form of `AnalyticRay.poly_coeff_eq_zero`. -/
theorem poly_coeff_eq_zero_of_eventually (k : ℕ) (c : ℕ → F) (C : ℝ)
    (h : ∀ᶠ a in 𝓝[>] (0 : ℝ), ‖∑ m ∈ range k, a ^ m • c m‖ ≤ C * a ^ k) :
    ∀ m < k, c m = 0 := by
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhdsWithin_iff.mp h
  refine AnalyticRay.poly_coeff_eq_zero k c δ C hδ fun a ha haδ => hball ⟨?_, ha⟩
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ha]; exact haδ

end Poly

/-! ### Cauchy products of analytic functions -/

section Cauchy

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem partialSum_eq_sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : FormalMultilinearSeries ℝ ℝ E) (n : ℕ) (a : ℝ) :
    p.partialSum n a = ∑ m ∈ range n, a ^ m • p.coeff m := by
  simp [FormalMultilinearSeries.partialSum, FormalMultilinearSeries.apply_eq_pow_smul_coeff]

theorem isBigO_sub_sum {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → E}
    {p : FormalMultilinearSeries ℝ ℝ E} (hf : HasFPowerSeriesAt f p 0) (n : ℕ) :
    (fun a : ℝ => f a - ∑ m ∈ range n, a ^ m • p.coeff m) =O[𝓝 0] fun a => ‖a‖ ^ n := by
  have := hf.isBigO_sub_partialSum_pow n
  simpa [partialSum_eq_sum] using this

/-- **Cauchy-product coefficients of an analytic identity.**  If `D : ℝ → (V →L[ℝ] W)`,
`v : ℝ → V`, `χ : ℝ → W` have power series at `0` and `D(a) v(a) = χ(a)` near `0`, then
`∑_{i ≤ j} D_i v_{j-i} = χ_j` for every `j`. -/
theorem coeff_cauchy_of_apply_eq (D : ℝ → V →L[ℝ] W) (v : ℝ → V) (χ : ℝ → W)
    {pD : FormalMultilinearSeries ℝ ℝ (V →L[ℝ] W)} {pv : FormalMultilinearSeries ℝ ℝ V}
    {pχ : FormalMultilinearSeries ℝ ℝ W} (hD : HasFPowerSeriesAt D pD 0)
    (hv : HasFPowerSeriesAt v pv 0) (hχ : HasFPowerSeriesAt χ pχ 0)
    (h : ∀ᶠ a in 𝓝 (0 : ℝ), D a (v a) = χ a) (j : ℕ) :
    ∑ i ∈ range (j + 1), pD.coeff i (pv.coeff (j - i)) = pχ.coeff j := by
  set N := j + 1
  set c : ℕ → W := fun m => ∑ i ∈ range (m + 1), pD.coeff i (pv.coeff (m - i)) -
    pχ.coeff m with hc
  set PD : ℝ → V →L[ℝ] W := fun a => ∑ i ∈ range N, a ^ i • pD.coeff i
  set PV : ℕ → ℝ → V := fun n a => ∑ l ∈ range n, a ^ l • pv.coeff l
  set PX : ℝ → W := fun a => ∑ m ∈ range N, a ^ m • pχ.coeff m
  -- the algebraic identity
  have hid : ∀ a : ℝ, ∑ m ∈ range N, a ^ m • c m
      = (D a (v a) - χ a) + (χ a - PX a) - (D a - PD a) (v a)
        - ∑ i ∈ range N, a ^ i • pD.coeff i (v a - PV (N - i) a) := by
    intro a
    have hflip := Finset.sum_range_diag_flip N
      (fun i l => a ^ (i + l) • pD.coeff i (pv.coeff l))
    have h1 : ∑ m ∈ range N, ∑ k ∈ range (m + 1), a ^ (k + (m - k)) • pD.coeff k (pv.coeff (m - k))
        = ∑ m ∈ range N, a ^ m • ∑ i ∈ range (m + 1), pD.coeff i (pv.coeff (m - i)) := by
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Nat.add_sub_cancel' (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))]
    have h2 : ∀ i, a ^ i • pD.coeff i (PV (N - i) a)
        = ∑ l ∈ range (N - i), a ^ (i + l) • pD.coeff i (pv.coeff l) := by
      intro i
      simp only [PV, map_sum, map_smul, Finset.smul_sum, smul_smul, pow_add]
    have h3 : (PD a) (v a) = ∑ i ∈ range N, a ^ i • pD.coeff i (v a) := by
      simp only [PD, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]
    have h4 : ∑ i ∈ range N, a ^ i • pD.coeff i (v a - PV (N - i) a)
        = (PD a) (v a) - ∑ i ∈ range N, ∑ l ∈ range (N - i),
            a ^ (i + l) • pD.coeff i (pv.coeff l) := by
      rw [h3, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_sub, smul_sub, h2]
    rw [h4, ← hflip, h1]
    simp only [hc, smul_sub, Finset.sum_sub_distrib, PX, ContinuousLinearMap.sub_apply]
    abel
  -- each error term is `O(|a|^N)`
  have hE1 : (fun a => χ a - PX a) =O[𝓝 0] fun a : ℝ => ‖a‖ ^ N := isBigO_sub_sum hχ N
  have hvb : v =O[𝓝 0] (fun _ => (1 : ℝ)) :=
    hv.continuousAt.norm.isBoundedUnder_le.isBigO_one ℝ
  have hE2 : (fun a => (D a - PD a) (v a)) =O[𝓝 0] fun a : ℝ => ‖a‖ ^ N := by
    have hDb : (fun a => D a - PD a) =O[𝓝 0] fun a : ℝ => ‖a‖ ^ N := isBigO_sub_sum hD N
    have := hDb.norm_left.mul hvb.norm_left
    simp only [mul_one] at this
    refine (isBigO_of_le _ fun a => ?_).trans this
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact (D a - PD a).le_opNorm (v a)
  have hE3 : (fun a => ∑ i ∈ range N, a ^ i • pD.coeff i (v a - PV (N - i) a))
      =O[𝓝 0] fun a : ℝ => ‖a‖ ^ N := by
    refine IsBigO.fun_sum fun i hi => ?_
    have hi' : i < N := Finset.mem_range.mp hi
    have hvi : (fun a => v a - PV (N - i) a) =O[𝓝 0] fun a : ℝ => ‖a‖ ^ (N - i) :=
      isBigO_sub_sum hv (N - i)
    have hDi := ((pD.coeff i).isBigO_comp (fun a => v a - PV (N - i) a) (𝓝 0)).trans hvi
    have hpow : (fun a : ℝ => a ^ i) =O[𝓝 0] fun a : ℝ => ‖a‖ ^ i :=
      isBigO_of_le _ fun a => by simp
    have := hpow.smul hDi
    have heq : (fun x : ℝ => ‖x‖ ^ i • ‖x‖ ^ (N - i)) = fun x : ℝ => ‖x‖ ^ N := by
      funext a
      rw [smul_eq_mul, ← pow_add, Nat.add_sub_cancel' hi'.le]
    rwa [heq] at this
  have hP : (fun a => ∑ m ∈ range N, a ^ m • c m) =O[𝓝 0] fun a : ℝ => ‖a‖ ^ N := by
    have hzero : (fun a => D a (v a) - χ a) =O[𝓝 0] fun a : ℝ => ‖a‖ ^ N :=
      (isBigO_zero _ _).congr' (by filter_upwards [h] with a ha; rw [ha, sub_self]) .rfl
    have := ((hzero.add hE1).sub hE2).sub hE3
    exact this.congr' (Eventually.of_forall fun a => (hid a).symm) .rfl
  obtain ⟨C, hC⟩ := hP.bound
  have hpos : ∀ᶠ a in 𝓝[>] (0 : ℝ), ‖∑ m ∈ range N, a ^ m • c m‖ ≤ C * a ^ N := by
    filter_upwards [nhdsWithin_le_nhds hC, self_mem_nhdsWithin] with a ha ha0
    rwa [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.norm_eq_abs,
      abs_of_pos ha0] at ha
  have := poly_coeff_eq_zero_of_eventually N c C hpos j (Nat.lt_succ_self j)
  exact sub_eq_zero.mp this

/-- **The coefficient recursion** `D₀ v_j = χ_j - ∑_{i=1}^{j} D_i v_{j-i}`
(`eq:supp-finite-acc-recursion`) for an analytic identity `D(a) v(a) = χ(a)`. -/
theorem coeff_recursion_of_apply_eq (D : ℝ → V →L[ℝ] W) (v : ℝ → V) (χ : ℝ → W)
    {pD : FormalMultilinearSeries ℝ ℝ (V →L[ℝ] W)} {pv : FormalMultilinearSeries ℝ ℝ V}
    {pχ : FormalMultilinearSeries ℝ ℝ W} (hD : HasFPowerSeriesAt D pD 0)
    (hv : HasFPowerSeriesAt v pv 0) (hχ : HasFPowerSeriesAt χ pχ 0)
    (h : ∀ᶠ a in 𝓝 (0 : ℝ), D a (v a) = χ a) (j : ℕ) :
    pD.coeff 0 (pv.coeff j) = pχ.coeff j - ∑ i ∈ Ioc 0 j, pD.coeff i (pv.coeff (j - i)) := by
  rw [← coeff_cauchy_of_apply_eq D v χ hD hv hχ h j, Finset.range_eq_Ico,
    Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos j)]
  have : Ico (0 + 1) (j + 1) = Ioc 0 j := by ext i; simp; omega
  rw [this, Nat.sub_zero]; abel

/-- With `D₀` invertible, every coefficient of `v` is computed from the single inverse `D₀⁻¹`:
`v_j = D₀⁻¹ (χ_j - ∑_{i=1}^{j} D_i v_{j-i})`. -/
theorem coeff_eq_of_apply_eq (D : ℝ → V →L[ℝ] W) (v : ℝ → V) (χ : ℝ → W)
    {pD : FormalMultilinearSeries ℝ ℝ (V →L[ℝ] W)} {pv : FormalMultilinearSeries ℝ ℝ V}
    {pχ : FormalMultilinearSeries ℝ ℝ W} (hD : HasFPowerSeriesAt D pD 0)
    (hv : HasFPowerSeriesAt v pv 0) (hχ : HasFPowerSeriesAt χ pχ 0)
    (h : ∀ᶠ a in 𝓝 (0 : ℝ), D a (v a) = χ a) (D₀inv : W →L[ℝ] V)
    (hinv : ∀ x, D₀inv (pD.coeff 0 x) = x) (j : ℕ) :
    pv.coeff j = D₀inv (pχ.coeff j - ∑ i ∈ Ioc 0 j, pD.coeff i (pv.coeff (j - i))) := by
  rw [← coeff_recursion_of_apply_eq D v χ hD hv hχ h j, hinv]

/-- If `χ₀ = χ₁ = χ₂ = 0`, then `v₀ = v₁ = v₂ = 0` and `v₃ = D₀⁻¹ χ₃`. -/
theorem coeff_low_of_apply_eq (D : ℝ → V →L[ℝ] W) (v : ℝ → V) (χ : ℝ → W)
    {pD : FormalMultilinearSeries ℝ ℝ (V →L[ℝ] W)} {pv : FormalMultilinearSeries ℝ ℝ V}
    {pχ : FormalMultilinearSeries ℝ ℝ W} (hD : HasFPowerSeriesAt D pD 0)
    (hv : HasFPowerSeriesAt v pv 0) (hχ : HasFPowerSeriesAt χ pχ 0)
    (h : ∀ᶠ a in 𝓝 (0 : ℝ), D a (v a) = χ a) (D₀inv : W →L[ℝ] V)
    (hinv : ∀ x, D₀inv (pD.coeff 0 x) = x) (hχ0 : ∀ j < 3, pχ.coeff j = 0) :
    (∀ j < 3, pv.coeff j = 0) ∧ pv.coeff 3 = D₀inv (pχ.coeff 3) := by
  have hlow : ∀ j < 3, pv.coeff j = 0 := by
    intro j hj
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      rw [coeff_eq_of_apply_eq D v χ hD hv hχ h D₀inv hinv j, hχ0 j hj, zero_sub]
      rw [Finset.sum_eq_zero fun i hi => by
        rw [ih (j - i) (by simp at hi; omega) (by omega), map_zero], neg_zero, map_zero]
  refine ⟨hlow, ?_⟩
  rw [coeff_eq_of_apply_eq D v χ hD hv hχ h D₀inv hinv 3]
  congr 1
  rw [Finset.sum_eq_zero fun i hi => by
    rw [hlow (3 - i) (by simp at hi; omega), map_zero], sub_zero]

end Cauchy

/-! ### Analyticity of `D⁻¹ χ` -/

section Inverse

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- If `D : ℝ → (V →L[ℝ] V)` and `χ` are analytic at `0` and `D(0)` is invertible, then
`a ↦ D(a)⁻¹ χ(a)` (with `Ring.inverse`) is analytic at `0`, and it solves `D(a) v(a) = χ(a)`
near `0`. -/
theorem analyticAt_inverse_apply {D : ℝ → V →L[ℝ] V} {χ : ℝ → V} (hD : AnalyticAt ℝ D 0)
    (hχ : AnalyticAt ℝ χ 0) (h0 : IsUnit (D 0)) :
    AnalyticAt ℝ (fun a => Ring.inverse (D a) (χ a)) 0 ∧
      ∀ᶠ a in 𝓝 (0 : ℝ), D a (Ring.inverse (D a) (χ a)) = χ a := by
  obtain ⟨u, hu⟩ := h0
  have hinv : AnalyticAt ℝ (fun a => Ring.inverse (D a)) 0 := by
    have := analyticAt_inverse (𝕜 := ℝ) u
    rw [hu] at this
    exact this.comp hD
  refine ⟨?_, ?_⟩
  · have hB : AnalyticAt ℝ (fun p : (V →L[ℝ] V) × V => p.1 p.2) (Ring.inverse (D 0), χ 0) := by
      simpa using ((ContinuousLinearMap.apply ℝ V).flip).analyticAt_bilinear
        (Ring.inverse (D 0), χ 0)
    exact hB.comp (f := fun a => (Ring.inverse (D a), χ a)) (hinv.prod hχ)
  · have hunits : ∀ᶠ a in 𝓝 (0 : ℝ), IsUnit (D a) := by
      have hopen : IsOpen {x : V →L[ℝ] V | IsUnit x} := Units.isOpen
      exact hD.continuousAt.preimage_mem_nhds (hopen.mem_nhds ⟨u, hu⟩)
    filter_upwards [hunits] with a ha
    rw [← ContinuousLinearMap.mul_apply, Ring.mul_inverse_cancel _ ha,
      ContinuousLinearMap.one_apply]

end Inverse

/-! ### The assembled coefficient certificate -/

section Certificate

variable {V U : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup U] [NormedSpace ℝ U]

/-- **Coefficient-complete acceleration certificate, analytic layer** (the parts of
`thm:supp-finite-acc-coefficients` that do not use `thm:supp-exact-initial-gate`).  Let
`D, χ` be analytic at `0` with `D(0)` invertible, `v = D⁻¹χ`, `p` linear and
`θ(a) = ∑_{k=-3}^{0} a^k θ_k + ρ(a)` with `ρ → 0`.  Then `v` has a power series `pv` at `0`
whose coefficients obey the recursion `D₀ v_j = χ_j - ∑_{i=1}^{j} D_i v_{j-i}` for every `j`,
and the defect `-a⁻³ p v(a) - θ(a)` has a finite limit iff `p v_j + θ_{j-3} = 0` (`j < 3`), with
value `-p v₃ - θ₀`; if moreover `χ₀ = χ₁ = χ₂ = 0`, then `v₀ = v₁ = v₂ = 0` and
`v₃ = D₀⁻¹ χ₃`. -/
theorem acc_coefficient_certificate {D : ℝ → V →L[ℝ] V} {χ : ℝ → V}
    {pD : FormalMultilinearSeries ℝ ℝ (V →L[ℝ] V)} {pχ : FormalMultilinearSeries ℝ ℝ V}
    (hD : HasFPowerSeriesAt D pD 0) (hχ : HasFPowerSeriesAt χ pχ 0) (h0 : IsUnit (D 0))
    (p : V →L[ℝ] U) (θm3 θm2 θm1 θ0 : U) (θ ρ : ℝ → U)
    (hθ : ∀ a, a ≠ 0 → θ a = (a⁻¹ ^ 3) • θm3 + (a⁻¹ ^ 2) • θm2 + a⁻¹ • θm1 + θ0 + ρ a)
    (hρ : Tendsto ρ (𝓝[≠] 0) (𝓝 0)) :
    ∃ pv : FormalMultilinearSeries ℝ ℝ V,
      HasFPowerSeriesAt (fun a => Ring.inverse (D a) (χ a)) pv 0 ∧
      (∀ j, pD.coeff 0 (pv.coeff j) = pχ.coeff j - ∑ i ∈ Ioc 0 j, pD.coeff i (pv.coeff (j - i))) ∧
      ((∃ L, Tendsto (fun a => -((a⁻¹ ^ 3) • p (Ring.inverse (D a) (χ a))) - θ a) (𝓝[≠] 0)
          (𝓝 L)) ↔
        p (pv.coeff 0) + θm3 = 0 ∧ p (pv.coeff 1) + θm2 = 0 ∧ p (pv.coeff 2) + θm1 = 0) ∧
      (p (pv.coeff 0) + θm3 = 0 ∧ p (pv.coeff 1) + θm2 = 0 ∧ p (pv.coeff 2) + θm1 = 0 →
        Tendsto (fun a => -((a⁻¹ ^ 3) • p (Ring.inverse (D a) (χ a))) - θ a) (𝓝[≠] 0)
          (𝓝 (-(p (pv.coeff 3)) - θ0))) ∧
      ((∀ j < 3, pχ.coeff j = 0) →
        (∀ j < 3, pv.coeff j = 0) ∧ pv.coeff 3 = Ring.inverse (D 0) (pχ.coeff 3)) := by
  obtain ⟨hvan, hsol⟩ := analyticAt_inverse_apply hD.analyticAt hχ.analyticAt h0
  obtain ⟨pv, hpv⟩ := hvan
  have hD0 : pD.coeff 0 = D 0 := by
    simpa using hD.coeff_zero (fun _ => (1 : ℝ))
  have hinv : ∀ x, Ring.inverse (D 0) (pD.coeff 0 x) = x := by
    intro x
    rw [hD0, ← ContinuousLinearMap.mul_apply, Ring.inverse_mul_cancel _ h0,
      ContinuousLinearMap.one_apply]
  have hdef := PowerSeriesQuotient.defect_tendsto_iff _ pv hpv p θm3 θm2 θm1 θ0 θ ρ hθ hρ
  refine ⟨pv, hpv, fun j => coeff_recursion_of_apply_eq D _ χ hD hpv hχ hsol j, hdef.1, hdef.2,
    fun hχ0 => coeff_low_of_apply_eq D _ χ hD hpv hχ hsol (Ring.inverse (D 0)) hinv hχ0⟩

end Certificate

end AnalyticCauchy
end RenewalGeometry
