/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.AnalyticCauchyProductCoefficients
import RenewalGeometry.Gravity.ExactInitialAccelerationGate
import RenewalGeometry.Gravity.FiniteAccInvarianceExact
import RenewalGeometry.Gravity.MultiplierAccelerationExact

/-!
# The coefficient-complete acceleration certificate and its initial-data verdict
  (`thm:supp-finite-acc-coefficients`, `prop:supp-finite-acc-invariance`,
  `eq:supp-finite-acc-recursion`, `eq:supp-finite-acc-poles`, `eq:supp-finite-acc-verdict`,
  `eq:supp-finite-acc-initial-verdict`, `eq:supp-finite-acc-total-response`;
  emergent-spacetime manuscript)

The amplitude `a` is positive (`a ↓ 0`, filter `𝓝[>] 0`), as for the exact initialized families of
`thm:supp-exact-initial-gate` (`Gravity/ExactInitialAccelerationGate.lean`).

* `tendsto_laurent_pos_iff`, `defect_tendsto_pos_iff`: one-sided (`a ↓ 0`) versions of the pole
  test of `PowerSeriesQuotient` (a one-sided finite limit already forces the poles to vanish).
* **`finite_acc_coefficients`** (`thm:supp-finite-acc-coefficients`, operator form): `D(a)`,
  `χ(a)` analytic at `0` with `D(0)` invertible, `v = D⁻¹χ`; the decoder identity
  `z_{a,ττ}(0) = λ_{tt,W} = -a⁻⁴v(a)` (`prop:supp-finite-acc-schur`,
  `MultiplierAcceleration.finite_acc_schur_eventually`, together with the balanced-chart decoder);
  `θ(a) = a p_g ḣ_a = Σ_{k=-3}^0 a^k θ_k + ρ(a)`, `ρ → 0`.  Then: the recursion
  `D₀v_j = χ_j - Σ_{i=1}^j D_i v_{j-i}` for every `j`; the two-row acceleration defect
  `a p_g{z_{a,ττ}(0) - ḣ_a}` equals `-a⁻³ p_g v(a) - θ(a)` and has a finite limit iff
  `p_g v_j + θ_{j-3} = 0` (`j < 3`), with value `Δ_g = -p_g v₃ - θ₀`; when `χ₀ = χ₁ = χ₂ = 0` and
  `θ = o(1)`, `Δ_g = -p_g D₀⁻¹χ₃`.
* `InitialGateFamily`: an exact initialized family satisfying the hypotheses of
  `thm:supp-exact-initial-gate` (bundled).  `InitialGateFamily.defect_tendsto`: its defect tends
  to the initial verdict `p_g{C_red Df(0)κ + C_red s₀ + Dg(0)b}`.
* **`finite_acc_initial_verdict`** (`eq:supp-finite-acc-initial-verdict`): for a family satisfying
  the gate and the coefficient hypotheses, the poles vanish and
  `-p_g v₃ - θ₀ = Δ_g = p_g{C_red Df(0)κ + C_red s₀ + Dg(0)b}`: the action-side coefficient
  calculation and the initialized slow-source calculation give the same two-vector.
* **`same_tuple_same_defect_of_gate`**, **`total_response_of_gate`**
  (`prop:supp-finite-acc-invariance`): the verdict hypothesis of
  `FiniteAccInvariance.same_tuple_same_defect` / `total_response` is discharged by the gate.
-/

open Filter Set Asymptotics Finset
open scoped Topology

noncomputable section

set_option linter.unusedSectionVars false

namespace RenewalGeometry
namespace FiniteAccVerdict

open ExactInitialGate

/-! ### One-sided pole test -/

section Poles

variable {U V : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup V]
  [NormedSpace ℝ V]

theorem eq_of_eventually_eq_of_tendsto_pos {f g : ℝ → U} {x y : U}
    (hf : Tendsto f (𝓝[>] 0) (𝓝 x)) (hg : Tendsto g (𝓝[>] 0) (𝓝 y))
    (h : ∀ a, 0 < a → f a = g a) : x = y := by
  refine tendsto_nhds_unique hf (hg.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with a ha
  exact (h a ha).symm

/-- **One-sided pole test.**  If `e(a) = a⁻³c₀ + a⁻²c₁ + a⁻¹c₂ + c₃ + r(a)` for `a > 0` with
`r(a) → 0` as `a ↓ 0`, then `e` has a finite limit as `a ↓ 0` iff `c₀ = c₁ = c₂ = 0`; the limit is
then `c₃`. -/
theorem tendsto_laurent_pos_iff (e r : ℝ → U) (c₀ c₁ c₂ c₃ : U)
    (he : ∀ a, 0 < a → e a = (a⁻¹ ^ 3) • c₀ + (a⁻¹ ^ 2) • c₁ + a⁻¹ • c₂ + c₃ + r a)
    (hr : Tendsto r (𝓝[>] 0) (𝓝 0)) :
    ((∃ L, Tendsto e (𝓝[>] 0) (𝓝 L)) ↔ c₀ = 0 ∧ c₁ = 0 ∧ c₂ = 0) ∧
      (c₀ = 0 ∧ c₁ = 0 ∧ c₂ = 0 → Tendsto e (𝓝[>] 0) (𝓝 c₃)) := by
  have hid : Tendsto (fun a : ℝ => a) (𝓝[>] 0) (𝓝 0) := tendsto_nhdsWithin_of_tendsto_nhds
    (continuous_id.tendsto 0)
  have hconv : c₀ = 0 ∧ c₁ = 0 ∧ c₂ = 0 → Tendsto e (𝓝[>] 0) (𝓝 c₃) := by
    rintro ⟨rfl, rfl, rfl⟩
    have h : Tendsto (fun a => c₃ + r a) (𝓝[>] 0) (𝓝 (c₃ + 0)) := tendsto_const_nhds.add hr
    rw [add_zero] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with a ha
    rw [he a ha]
    simp
  refine ⟨⟨?_, fun h => ⟨c₃, hconv h⟩⟩, hconv⟩
  rintro ⟨L, hL⟩
  set m : ℝ → U := fun a => e a - c₃ - r a with hmdef
  have hm : Tendsto m (𝓝[>] 0) (𝓝 (L - c₃ - 0)) := (hL.sub tendsto_const_nhds).sub hr
  have hmeq : ∀ a, 0 < a → m a = (a⁻¹ ^ 3) • c₀ + (a⁻¹ ^ 2) • c₁ + a⁻¹ • c₂ := by
    intro a ha
    simp only [hmdef, he a ha]
    abel
  have hpow : ∀ k : ℕ, 0 < k → Tendsto (fun a : ℝ => a ^ k • m a) (𝓝[>] 0) (𝓝 0) := by
    intro k hk
    have := (hid.pow k).smul hm
    simpa [zero_pow hk.ne'] using this
  have key : ∀ a, 0 < a → c₀ + a • c₁ + a ^ 2 • c₂ = a ^ 3 • m a := by
    intro a ha
    obtain ⟨e1, e2, e3, -, -, -⟩ := PowerSeriesQuotient.scalar_identities (ne_of_gt ha)
    rw [hmeq a ha, smul_add, smul_add, smul_smul, smul_smul, smul_smul, e1, e2, e3, one_smul]
  have hc₀ : c₀ = 0 := by
    have hpoly : Tendsto (fun a : ℝ => c₀ + a • c₁ + a ^ 2 • c₂) (𝓝[>] 0)
        (𝓝 (c₀ + (0 : ℝ) • c₁ + (0 : ℝ) ^ 2 • c₂)) :=
      (tendsto_const_nhds.add (hid.smul tendsto_const_nhds)).add
        ((hid.pow 2).smul tendsto_const_nhds)
    simp only [zero_smul, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow] at hpoly
    exact eq_of_eventually_eq_of_tendsto_pos hpoly (hpow 3 (by norm_num)) key
  have key2 : ∀ a, 0 < a → c₁ + a • c₂ = a ^ 2 • m a := by
    intro a ha
    obtain ⟨-, -, -, f1, f2, f3⟩ := PowerSeriesQuotient.scalar_identities (ne_of_gt ha)
    have := congrArg (fun x => a⁻¹ • x) (key a ha)
    simp only [hc₀, zero_add, smul_add, smul_smul, f1, f2, f3, one_smul] at this
    exact this
  have hc₁ : c₁ = 0 := by
    have hpoly : Tendsto (fun a : ℝ => c₁ + a • c₂) (𝓝[>] 0) (𝓝 (c₁ + (0 : ℝ) • c₂)) :=
      tendsto_const_nhds.add (hid.smul tendsto_const_nhds)
    rw [zero_smul, add_zero] at hpoly
    exact eq_of_eventually_eq_of_tendsto_pos hpoly (hpow 2 (by norm_num)) key2
  have key3 : ∀ a, 0 < a → c₂ = a • m a := by
    intro a ha
    obtain ⟨-, -, -, f1, f2, -⟩ := PowerSeriesQuotient.scalar_identities (ne_of_gt ha)
    have := congrArg (fun x => a⁻¹ • x) (key2 a ha)
    simp only [hc₁, zero_add, smul_smul, f1, f2, one_smul] at this
    exact this
  have hc₂ : c₂ = 0 := by
    have h1 := hpow 1 one_pos
    simp only [pow_one] at h1
    exact eq_of_eventually_eq_of_tendsto_pos tendsto_const_nhds h1 key3
  exact ⟨hc₀, hc₁, hc₂⟩

/-- One-sided **acceleration-defect pole test** (`eq:supp-finite-acc-poles`,
`eq:supp-finite-acc-verdict`) for `a ↓ 0`. -/
theorem defect_tendsto_pos_iff (v : ℝ → V) (pv : FormalMultilinearSeries ℝ ℝ V)
    (hv : HasFPowerSeriesAt v pv 0) (p : V →L[ℝ] U) (θm3 θm2 θm1 θ0 : U) (θ ρ : ℝ → U)
    (hθ : ∀ a, 0 < a → θ a = (a⁻¹ ^ 3) • θm3 + (a⁻¹ ^ 2) • θm2 + a⁻¹ • θm1 + θ0 + ρ a)
    (hρ : Tendsto ρ (𝓝[>] 0) (𝓝 0)) :
    ((∃ L, Tendsto (fun a => -((a⁻¹ ^ 3) • p (v a)) - θ a) (𝓝[>] 0) (𝓝 L)) ↔
        p (pv.coeff 0) + θm3 = 0 ∧ p (pv.coeff 1) + θm2 = 0 ∧ p (pv.coeff 2) + θm1 = 0) ∧
      (p (pv.coeff 0) + θm3 = 0 ∧ p (pv.coeff 1) + θm2 = 0 ∧ p (pv.coeff 2) + θm1 = 0 →
        Tendsto (fun a => -((a⁻¹ ^ 3) • p (v a)) - θ a) (𝓝[>] 0)
          (𝓝 (-(p (pv.coeff 3)) - θ0))) := by
  set R : ℝ → V := fun a => (a⁻¹ ^ 3) • (v a - ∑ k ∈ range 4, a ^ k • pv.coeff k) with hRdef
  have hR : Tendsto R (𝓝[>] 0) (𝓝 0) :=
    (PowerSeriesQuotient.tendsto_taylor_remainder v pv hv).mono_left
      (nhdsWithin_mono _ fun a (ha : 0 < a) => ne_of_gt ha)
  set r : ℝ → U := fun a => -(p (R a)) - ρ a with hrdef
  have hr : Tendsto r (𝓝[>] 0) (𝓝 0) := by
    have := ((p.continuous.tendsto 0).comp hR).neg.sub hρ
    simpa [r] using this
  have he : ∀ a, 0 < a → -((a⁻¹ ^ 3) • p (v a)) - θ a =
      (a⁻¹ ^ 3) • (-(p (pv.coeff 0) + θm3)) + (a⁻¹ ^ 2) • (-(p (pv.coeff 1) + θm2)) +
        a⁻¹ • (-(p (pv.coeff 2) + θm1)) + (-(p (pv.coeff 3)) - θ0) + r a := by
    intro a hpos
    have ha : a ≠ 0 := ne_of_gt hpos
    have hva : v a = ∑ k ∈ range 4, a ^ k • pv.coeff k + a ^ 3 • R a := by
      simp only [hRdef, smul_smul]
      rw [show a ^ 3 * a⁻¹ ^ 3 = 1 by field_simp, one_smul]
      abel
    rw [hθ a hpos, hva]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, map_add, map_smul, smul_add,
      smul_smul, hrdef]
    have e1 : a⁻¹ ^ 3 * a ^ 0 = a⁻¹ ^ 3 := by ring
    have e2 : a⁻¹ ^ 3 * a ^ 1 = a⁻¹ ^ 2 := by field_simp
    have e3 : a⁻¹ ^ 3 * a ^ 2 = a⁻¹ := by field_simp
    have e4 : a⁻¹ ^ 3 * a ^ 3 = 1 := by field_simp
    rw [e1, e2, e3, e4, one_smul, one_smul]
    simp only [zero_add, smul_neg, smul_add, map_zero, smul_zero]
    abel
  have := tendsto_laurent_pos_iff _ r _ _ _ _ he hr
  simp only [neg_eq_zero] at this
  exact this

end Poles

/-! ### The coefficient-complete certificate -/

section Certificate

variable {V Zg : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup Zg] [NormedSpace ℝ Zg]

/-- The decoded defect identity: with `z_{a,ττ}(0) = -a⁻⁴ v(a)` and `θ(a) = a p_g ḣ_a`, the
two-row acceleration defect is `a p_g{z_{a,ττ}(0) - ḣ_a} = -a⁻³ p_g v(a) - θ(a)`. -/
theorem defect_eq_decoded (pg : V →L[ℝ] Zg) {a : ℝ} (ha : a ≠ 0) (zdd hd v : V)
    (hdec : zdd = -(a ^ 4)⁻¹ • v) :
    a • pg (zdd - hd) = -((a⁻¹ ^ 3) • pg v) - a • pg hd := by
  rw [hdec, map_sub, smul_sub, map_smul, smul_smul]
  have : a * -(a ^ 4)⁻¹ = -(a⁻¹ ^ 3) := by field_simp
  rw [this, neg_smul]

/-- **`thm:supp-finite-acc-coefficients`** (operator form).  Let `D(a) = Σ a^j D_j` and
`χ(a) = Σ a^j χ_j` be analytic at `0` with `D₀ = D(0)` invertible, and `v(a) = D(a)⁻¹χ(a)`.
Let the decoded weak acceleration be `z_{a,ττ}(0) = -a⁻⁴ v(a)` for small `a > 0`
(`eq:supp-finite-acc-elimination` with the balanced-chart decoder `z_ττ = λ_{tt,W}`), and let
`θ(a) = a p_g ḣ_a = Σ_{k=-3}^0 a^k θ_k + ρ(a)` with `ρ → 0`.  Then the coefficients `v_j` of `v`
satisfy the recursion (`eq:supp-finite-acc-recursion`) with the single inverse `D₀⁻¹`; the
two-row acceleration defect `a p_g{z_{a,ττ}(0) - ḣ_a}` has a finite limit as `a ↓ 0` iff
`p_g v_j + θ_{j-3} = 0` for `j < 3` (`eq:supp-finite-acc-poles`), its value is then
`Δ_g = -p_g v₃ - θ₀` (`eq:supp-finite-acc-verdict`); and if `χ₀ = χ₁ = χ₂ = 0` and `θ = o(1)`
then `Δ_g = -p_g D₀⁻¹χ₃`. -/
theorem finite_acc_coefficients {D : ℝ → V →L[ℝ] V} {χ : ℝ → V}
    {pD : FormalMultilinearSeries ℝ ℝ (V →L[ℝ] V)} {pχ : FormalMultilinearSeries ℝ ℝ V}
    (hD : HasFPowerSeriesAt D pD 0) (hχ : HasFPowerSeriesAt χ pχ 0) (h0 : IsUnit (D 0))
    (pg : V →L[ℝ] Zg) (zdd hd : ℝ → V)
    (hdec : ∀ᶠ a in 𝓝[>] 0, zdd a = -(a ^ 4)⁻¹ • Ring.inverse (D a) (χ a))
    (θm3 θm2 θm1 θ0 : Zg) (ρ : ℝ → Zg)
    (hθ : ∀ a, 0 < a → a • pg (hd a) =
      (a⁻¹ ^ 3) • θm3 + (a⁻¹ ^ 2) • θm2 + a⁻¹ • θm1 + θ0 + ρ a)
    (hρ : Tendsto ρ (𝓝[>] 0) (𝓝 0)) :
    ∃ pv : FormalMultilinearSeries ℝ ℝ V,
      HasFPowerSeriesAt (fun a => Ring.inverse (D a) (χ a)) pv 0 ∧
      (∀ j, pD.coeff 0 (pv.coeff j) = pχ.coeff j - ∑ i ∈ Ioc 0 j, pD.coeff i (pv.coeff (j - i))) ∧
      ((∃ L, Tendsto (fun a => a • pg (zdd a - hd a)) (𝓝[>] 0) (𝓝 L)) ↔
        pg (pv.coeff 0) + θm3 = 0 ∧ pg (pv.coeff 1) + θm2 = 0 ∧ pg (pv.coeff 2) + θm1 = 0) ∧
      (pg (pv.coeff 0) + θm3 = 0 ∧ pg (pv.coeff 1) + θm2 = 0 ∧ pg (pv.coeff 2) + θm1 = 0 →
        Tendsto (fun a => a • pg (zdd a - hd a)) (𝓝[>] 0) (𝓝 (-(pg (pv.coeff 3)) - θ0))) ∧
      ((∀ j < 3, pχ.coeff j = 0) → θm3 = 0 → θm2 = 0 → θm1 = 0 → θ0 = 0 →
        Tendsto (fun a => a • pg (zdd a - hd a)) (𝓝[>] 0)
          (𝓝 (-(pg (Ring.inverse (D 0) (pχ.coeff 3)))))) := by
  obtain ⟨pv, hpv, hrec, -, -, hlow⟩ :=
    AnalyticCauchy.acc_coefficient_certificate hD hχ h0 pg 0 0 0 0 (fun _ => 0)
      (fun _ => 0) (fun a _ => by simp) tendsto_const_nhds
  set θ : ℝ → Zg := fun a => a • pg (hd a)
  have hpole := defect_tendsto_pos_iff _ pv hpv pg θm3 θm2 θm1 θ0 θ ρ hθ hρ
  -- the decoded defect identity
  have hdefeq : (fun a => -((a⁻¹ ^ 3) • pg (Ring.inverse (D a) (χ a))) - θ a) =ᶠ[𝓝[>] 0]
      fun a => a • pg (zdd a - hd a) := by
    filter_upwards [hdec, self_mem_nhdsWithin] with a hda hpos
    exact (defect_eq_decoded pg (ne_of_gt hpos) _ _ _ hda).symm
  have hiff : (∃ L, Tendsto (fun a => a • pg (zdd a - hd a)) (𝓝[>] 0) (𝓝 L)) ↔
      ∃ L, Tendsto (fun a => -((a⁻¹ ^ 3) • pg (Ring.inverse (D a) (χ a))) - θ a) (𝓝[>] 0)
        (𝓝 L) :=
    ⟨fun ⟨L, hL⟩ => ⟨L, hL.congr' hdefeq.symm⟩, fun ⟨L, hL⟩ => ⟨L, hL.congr' hdefeq⟩⟩
  refine ⟨pv, hpv, hrec, hiff.trans hpole.1, fun hp => (hpole.2 hp).congr' hdefeq, ?_⟩
  intro hχ0 h3 h2 h1 h0'
  obtain ⟨hv0, hv3⟩ := hlow hχ0
  have hp : pg (pv.coeff 0) + θm3 = 0 ∧ pg (pv.coeff 1) + θm2 = 0 ∧
      pg (pv.coeff 2) + θm1 = 0 := by
    rw [hv0 0 (by norm_num), hv0 1 (by norm_num), hv0 2 (by norm_num), h3, h2, h1]
    simp
  have := (hpole.2 hp).congr' hdefeq
  rwa [hv3, h0', sub_zero] at this

end Certificate

/-! ### The decoder from the exact Schur elimination -/

section SchurBridge

open Matrix

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- A square matrix as a continuous linear operator on `n → ℝ`. -/
def matCLM (M : Matrix n n ℝ) : (n → ℝ) →L[ℝ] (n → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.toLin' M)

theorem matCLM_apply (M : Matrix n n ℝ) (v : n → ℝ) : matCLM M v = M *ᵥ v := rfl

/-- For an invertible matrix, the ring inverse of its operator is the matrix inverse. -/
theorem ring_inverse_matCLM (M : Matrix n n ℝ) (hM : IsUnit M.det) (v : n → ℝ) :
    Ring.inverse (matCLM M) v = M⁻¹ *ᵥ v := by
  have h1 : matCLM M * matCLM M⁻¹ = 1 := by
    ext1 w
    simp [matCLM_apply, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hM]
  have h2 : matCLM M⁻¹ * matCLM M = 1 := by
    ext1 w
    simp [matCLM_apply, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hM]
  let u : ((n → ℝ) →L[ℝ] (n → ℝ))ˣ := ⟨matCLM M, matCLM M⁻¹, h1, h2⟩
  have : Ring.inverse (matCLM M) = matCLM M⁻¹ := by
    change Ring.inverse (u : (n → ℝ) →L[ℝ] (n → ℝ)) = _
    rw [Ring.inverse_unit]
    rfl
  rw [this, matCLM_apply]

/-- **Decoder from the exact Schur elimination.**  If along the analytic initial family the
physical accelerations solve `𝓜_a λ_tt = -𝓢_a` with the graded mass `eq:supp-finite-acc-mass`
(`A(0)`, `D(0)` invertible, blocks continuous at `0`), and the balanced-chart decoder gives
`z_{a,ττ}(0) = λ_{tt,W}`, then for all small `a > 0`,
`z_{a,ττ}(0) = -a⁻⁴ D(a)⁻¹χ(a)` with `D = C - LᵀA⁻¹L`, `χ = S_W - aLᵀA⁻¹S_A`
(`MultiplierAcceleration.finite_acc_schur_eventually`). -/
theorem decoded_of_schur (A : ℝ → Matrix m m ℝ) (L : ℝ → Matrix m n ℝ) (C : ℝ → Matrix n n ℝ)
    (hAc : ContinuousAt A 0) (hLc : ContinuousAt L 0) (hCc : ContinuousAt C 0)
    (hA0 : IsUnit (A 0).det) (hD0 : IsUnit (C 0 - (L 0)ᵀ * (A 0)⁻¹ * L 0).det)
    (SA lA : ℝ → m → ℝ) (SW lW zdd : ℝ → n → ℝ)
    (hacc : ∀ᶠ a in 𝓝[>] 0, Matrix.fromBlocks (a ^ 2 • A a) (a ^ 3 • L a) (a ^ 3 • (L a)ᵀ)
      (a ^ 4 • C a) *ᵥ Sum.elim (lA a) (lW a) = -Sum.elim (SA a) (SW a))
    (hdecoder : ∀ᶠ a in 𝓝[>] 0, zdd a = lW a) :
    ∀ᶠ a in 𝓝[>] 0, zdd a = -(a ^ 4)⁻¹ • Ring.inverse (matCLM (C a - (L a)ᵀ * (A a)⁻¹ * L a))
      (SW a - a • ((L a)ᵀ * (A a)⁻¹) *ᵥ SA a) := by
  have hs := MultiplierAcceleration.finite_acc_schur_eventually A L C hAc hLc hCc hA0 hD0
  have hs' : ∀ᶠ a in 𝓝[>] (0 : ℝ), _ := hs.filter_mono
    (nhdsWithin_mono _ fun a (ha : 0 < a) => ne_of_gt ha)
  have hinv := (MultiplierAcceleration.schur_blocks_eventually_invertible A L C hAc hLc hCc hA0
    hD0).filter_mono (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  filter_upwards [hs', hacc, hdecoder, hinv] with a h1 h2 h3 h4
  rw [h3, (h1 _ _ _ _ h2).1, ring_inverse_matCLM _ h4.2]

end SchurBridge

/-! ### Exact initialized families and the initial verdict -/

section Verdict

variable {Xs W U Zg Ho : Type*}
  [NormedAddCommGroup Xs] [NormedSpace ℝ Xs] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup Zg] [NormedSpace ℝ Zg]
  [NormedAddCommGroup Ho] [NormedSpace ℝ Ho]

/-- An exact initialized family in a fixed slow-source chart `(C_red, B, p_g, p_H)` satisfying the
hypotheses of `thm:supp-exact-initial-gate`: the source maps `f, g, s, h`, the histories
`x_a, z_a, u_a` and their initial derivatives, the jets `eq:supp-exact-initial-jets-corrected`, and
the differentiability of the histories and composed source at the initial cut. -/
structure InitialGateFamily (Cred : Xs →L[ℝ] W) (B : W →L[ℝ] W) (pg : W →L[ℝ] Zg)
    (pH : W →L[ℝ] Ho) where
  f : Xs × W → Xs
  g : Xs × W → W
  s : ℝ × (Xs × W) × U → Xs
  h : ℝ × (Xs × W) × U → W
  u0 : U
  x : ℝ → ℝ → Xs
  z : ℝ → ℝ → W
  u : ℝ → ℝ → U
  xd : ℝ → Xs
  zd : ℝ → W
  zdd : ℝ → W
  hd : ℝ → W
  κ : Xs × W
  bs : Xs
  bw : W
  hf : DifferentiableAt ℝ f 0
  hg1 : ContDiffAt ℝ 1 g 0
  hg0 : g 0 = 0
  hs : ContinuousAt s (0, 0, u0)
  hh : ContinuousAt h (0, 0, u0)
  hxd : ∀ᶠ a in 𝓝[>] 0, HasDerivWithinAt (x a) (xd a) (Ici 0) 0
  hzd : ∀ᶠ a in 𝓝[>] 0, HasDerivWithinAt (z a) (zd a) (Ici 0) 0
  hxeq : ∀ᶠ a in 𝓝[>] 0, xd a = xField f s a (x a 0, z a 0) (u a 0)
  hzsys : ∀ᶠ a in 𝓝[>] 0, ∀ᶠ τ in 𝓝[≥] 0,
    HasDerivWithinAt (z a) (zField Cred B g h a (x a τ, z a τ) (u a τ)) (Ici 0) τ
  hzdd : ∀ᶠ a in 𝓝[>] 0, HasDerivWithinAt (derivWithin (z a) (Ici 0)) (zdd a) (Ici 0) 0
  hhd : ∀ᶠ a in 𝓝[>] 0, HasDerivWithinAt (fun τ => h (a, (x a τ, z a τ), u a τ)) (hd a) (Ici 0) 0
  hκ : (fun a => (x a 0, z a 0) - a • κ) =O[𝓝[>] 0] fun a => a ^ 2
  hb : Tendsto (fun a => (xd a, zd a)) (𝓝[>] 0) (𝓝 (bs, bw))
  hu : Tendsto (fun a => u a 0) (𝓝[>] 0) (𝓝 u0)
  hgate : pg (Cred bs) = 0

variable {Cred : Xs →L[ℝ] W} {B : W →L[ℝ] W} {pg : W →L[ℝ] Zg} {pH : W →L[ℝ] Ho}

namespace InitialGateFamily

/-- The two-row acceleration defect `a p_g{z_{a,ττ}(0) - ḣ_a}` of the family. -/
def defect (F : InitialGateFamily (U := U) Cred B pg pH) (a : ℝ) : Zg :=
  a • pg (F.zdd a - F.hd a)

/-- The initial verdict `p_g{C_red Df(0)κ + C_red s₀ + Dg(0)b}` of the family. -/
def verdict (F : InitialGateFamily (U := U) Cred B pg pH) : Zg :=
  FiniteAccInvariance.initialVerdict pg Cred (fderiv ℝ F.f 0) (fderiv ℝ F.g 0) F.κ
    (F.s (0, 0, F.u0)) (F.bs, F.bw)

/-- The gate theorem for a bundled family: its defect tends to the initial verdict. -/
theorem defect_tendsto (hpHC : pH.comp Cred = 0) (hpHB : pH.comp B = 0) (hpgB : pg.comp B = 0)
    (F : InitialGateFamily (U := U) Cred B pg pH) :
    Tendsto F.defect (𝓝[>] 0) (𝓝 F.verdict) :=
  initial_gate_defect Cred B pg pH hpHC hpHB hpgB F.f F.g F.s F.h F.hf F.hg1 F.hg0 F.hs F.hh F.x
    F.z F.u F.xd F.zd F.zdd F.hd F.hxd F.hzd F.hxeq F.hzsys F.hzdd F.hhd F.hκ F.hb F.hu F.hgate

/-- Any limit of the defect of a gate family is the initial verdict. -/
theorem eq_verdict_of_tendsto (hpHC : pH.comp Cred = 0) (hpHB : pH.comp B = 0)
    (hpgB : pg.comp B = 0) (F : InitialGateFamily (U := U) Cred B pg pH) {Δ : Zg}
    (hΔ : Tendsto F.defect (𝓝[>] 0) (𝓝 Δ)) : Δ = F.verdict :=
  tendsto_nhds_unique hΔ (F.defect_tendsto hpHC hpHB hpgB)

end InitialGateFamily

/-- **`eq:supp-finite-acc-initial-verdict`** (last assertions of
`thm:supp-finite-acc-coefficients`).  For an exact initialized family satisfying
`thm:supp-exact-initial-gate` whose decoded acceleration obeys the coefficient hypotheses of
`finite_acc_coefficients`, the three pole conditions hold automatically and
`-p_g v₃ - θ₀ = Δ_g = p_g{C_red Df(0)κ + C_red s₀ + Dg(0)b}`: the action-side coefficient
calculation and the initialized slow-source calculation give the same two-vector. -/
theorem finite_acc_initial_verdict [CompleteSpace W] (hpHC : pH.comp Cred = 0)
    (hpHB : pH.comp B = 0) (hpgB : pg.comp B = 0)
    (F : InitialGateFamily (U := U) Cred B pg pH)
    {D : ℝ → W →L[ℝ] W} {χ : ℝ → W}
    {pD : FormalMultilinearSeries ℝ ℝ (W →L[ℝ] W)} {pχ : FormalMultilinearSeries ℝ ℝ W}
    (hD : HasFPowerSeriesAt D pD 0) (hχ : HasFPowerSeriesAt χ pχ 0) (h0 : IsUnit (D 0))
    (hdec : ∀ᶠ a in 𝓝[>] 0, F.zdd a = -(a ^ 4)⁻¹ • Ring.inverse (D a) (χ a))
    (θm3 θm2 θm1 θ0 : Zg) (ρ : ℝ → Zg)
    (hθ : ∀ a, 0 < a → a • pg (F.hd a) =
      (a⁻¹ ^ 3) • θm3 + (a⁻¹ ^ 2) • θm2 + a⁻¹ • θm1 + θ0 + ρ a)
    (hρ : Tendsto ρ (𝓝[>] 0) (𝓝 0)) :
    ∃ pv : FormalMultilinearSeries ℝ ℝ W,
      HasFPowerSeriesAt (fun a => Ring.inverse (D a) (χ a)) pv 0 ∧
      (pg (pv.coeff 0) + θm3 = 0 ∧ pg (pv.coeff 1) + θm2 = 0 ∧ pg (pv.coeff 2) + θm1 = 0) ∧
      -(pg (pv.coeff 3)) - θ0 = F.verdict := by
  obtain ⟨pv, hpv, -, hiff, hval, -⟩ := finite_acc_coefficients hD hχ h0 pg F.zdd F.hd hdec
    θm3 θm2 θm1 θ0 ρ hθ hρ
  have hlim := F.defect_tendsto hpHC hpHB hpgB
  have hp := hiff.mp ⟨_, hlim⟩
  exact ⟨pv, hpv, hp, tendsto_nhds_unique (hval hp) hlim⟩

/-- **`prop:supp-finite-acc-invariance`, first clause.**  Two exact initialized families in the
same slow-source chart with the same `κ, b, s₀, Df(0), Dg(0)` (and the same `C_red, p_g`) have the
same two-row acceleration defect `Δ_g`. -/
theorem same_tuple_same_defect_of_gate (hpHC : pH.comp Cred = 0) (hpHB : pH.comp B = 0)
    (hpgB : pg.comp B = 0) (F₁ F₂ : InitialGateFamily (U := U) Cred B pg pH)
    (hκ : F₁.κ = F₂.κ) (hb : (F₁.bs, F₁.bw) = (F₂.bs, F₂.bw))
    (hs : F₁.s (0, 0, F₁.u0) = F₂.s (0, 0, F₂.u0)) (hDf : fderiv ℝ F₁.f 0 = fderiv ℝ F₂.f 0)
    (hDg : fderiv ℝ F₁.g 0 = fderiv ℝ F₂.g 0) {Δ₁ Δ₂ : Zg}
    (h₁ : Tendsto F₁.defect (𝓝[>] 0) (𝓝 Δ₁)) (h₂ : Tendsto F₂.defect (𝓝[>] 0) (𝓝 Δ₂)) :
    Δ₁ = Δ₂ := by
  refine FiniteAccInvariance.same_tuple_same_defect pg Cred (fderiv ℝ F₁.f 0) (fderiv ℝ F₁.g 0)
    F₁.κ (F₁.s (0, 0, F₁.u0)) (F₁.bs, F₁.bw) Δ₁ Δ₂ (F₁.eq_verdict_of_tendsto hpHC hpHB hpgB h₁) ?_
  rw [F₂.eq_verdict_of_tendsto hpHC hpHB hpgB h₂]
  simp only [InitialGateFamily.verdict, hκ, hb, hs, hDf, hDg]

/-- **`eq:supp-finite-acc-total-response`** (`prop:supp-finite-acc-invariance`).  For a family of
exact initialized preparations `d ↦ F_d` (gate families) with `Df(0)`, `Dg(0)`, `C_red`, `p_g`
fixed and `d ↦ (κ_d, s₀_d, b_d)` differentiable at `d₀`, the defect `Δ_g(d)` (the limit of the
two-row acceleration defect of `F_d`) is differentiable at `d₀` with
`D_dΔ_g = p_g ∘ (C_red Df(0) D_dκ + C_red D_ds₀ + Dg(0) D_db)`. -/
theorem total_response_of_gate {Dsp : Type*} [NormedAddCommGroup Dsp] [NormedSpace ℝ Dsp]
    (hpHC : pH.comp Cred = 0) (hpHB : pH.comp B = 0) (hpgB : pg.comp B = 0)
    (F : Dsp → InitialGateFamily (U := U) Cred B pg pH) (Df0 : Xs × W →L[ℝ] Xs)
    (Dg0 : Xs × W →L[ℝ] W) (Δ : Dsp → Zg) (κ' : Dsp →L[ℝ] Xs × W) (s0' : Dsp →L[ℝ] Xs)
    (b' : Dsp →L[ℝ] Xs × W) {d₀ : Dsp}
    (hκ : HasFDerivAt (fun d => (F d).κ) κ' d₀)
    (hs : HasFDerivAt (fun d => (F d).s (0, 0, (F d).u0)) s0' d₀)
    (hb : HasFDerivAt (fun d => ((F d).bs, (F d).bw)) b' d₀)
    (hDf : ∀ᶠ d in 𝓝 d₀, fderiv ℝ (F d).f 0 = Df0) (hDg : ∀ᶠ d in 𝓝 d₀, fderiv ℝ (F d).g 0 = Dg0)
    (hΔ : ∀ᶠ d in 𝓝 d₀, Tendsto (F d).defect (𝓝[>] 0) (𝓝 (Δ d))) :
    HasFDerivAt Δ (pg.comp ((Cred.comp Df0).comp κ' + Cred.comp s0' + Dg0.comp b')) d₀ := by
  refine FiniteAccInvariance.total_response pg Cred Df0 Dg0 (fun d => (F d).κ)
    (fun d => (F d).s (0, 0, (F d).u0)) (fun d => ((F d).bs, (F d).bw)) Δ κ' s0' b' hκ hs hb ?_
  filter_upwards [hΔ, hDf, hDg] with d hd h1 h2
  rw [(F d).eq_verdict_of_tendsto hpHC hpHB hpgB hd]
  simp only [InitialGateFamily.verdict, h1, h2]

/-- Non-vacuity of `InitialGateFamily` (with a nonzero defect): in `ℝ × ℝ`, `C_red = p_g = id`,
`B = p_H = 0`, `f = g = h = 0`, `s ≡ 1`, `x_a(τ) = aτ`, `z_a(τ) = τ²/(2a)`; its defect is
`a p_g z_{a,ττ}(0) = 1` and its initial verdict is `p_g C_red s₀ = 1`. -/
def exampleFamily :
    InitialGateFamily (U := ℝ) (ContinuousLinearMap.id ℝ ℝ) (0 : ℝ →L[ℝ] ℝ)
      (ContinuousLinearMap.id ℝ ℝ) (0 : ℝ →L[ℝ] ℝ) where
  f := fun _ => 0
  g := fun _ => 0
  s := fun _ => 1
  h := fun _ => 0
  u0 := 0
  x := fun a τ => a * τ
  z := fun a τ => τ ^ 2 / (2 * a)
  u := fun _ _ => 0
  xd := fun a => a
  zd := fun _ => 0
  zdd := fun a => a⁻¹
  hd := fun _ => 0
  κ := 0
  bs := 0
  bw := 0
  hf := differentiableAt_const _
  hg1 := contDiffAt_const
  hg0 := rfl
  hs := continuousAt_const
  hh := continuousAt_const
  hxd := Eventually.of_forall fun a => by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul a).hasDerivWithinAt
  hzd := Eventually.of_forall fun a => by
    have := ((hasDerivAt_pow 2 (0 : ℝ)).div_const (2 * a)).hasDerivWithinAt (s := Ici 0)
    simpa using this
  hxeq := Eventually.of_forall fun a => by simp [xField]
  hzsys := Filter.Eventually.mono (show ∀ᶠ a in 𝓝[>] (0 : ℝ), 0 < a from self_mem_nhdsWithin) fun a ha =>
    Eventually.of_forall fun τ => by
      have h1 := ((hasDerivAt_pow 2 τ).div_const (2 * a)).hasDerivWithinAt (s := Ici 0)
      convert h1 using 1
      simp only [zField, phi0_apply, ContinuousLinearMap.id_apply, zero_apply, add_zero,
        smul_eq_mul]
      field_simp
      ring
  hzdd := Filter.Eventually.mono (show ∀ᶠ a in 𝓝[>] (0 : ℝ), 0 < a from self_mem_nhdsWithin) fun a ha => by
    have hd : ∀ τ ∈ Ici (0 : ℝ), derivWithin (fun τ => τ ^ 2 / (2 * a)) (Ici 0) τ = τ / a := by
      intro τ hτ
      rw [(((hasDerivAt_pow 2 τ).div_const (2 * a)).hasDerivWithinAt).derivWithin
        ((uniqueDiffOn_Ici 0) τ hτ)]
      field_simp
      ring
    have h1 : HasDerivWithinAt (fun τ : ℝ => τ / a) a⁻¹ (Ici 0) 0 := by
      simpa [div_eq_mul_inv] using ((hasDerivAt_id (0 : ℝ)).mul_const a⁻¹).hasDerivWithinAt
    exact h1.congr (fun τ hτ => hd τ hτ) (hd 0 self_mem_Ici)
  hhd := Eventually.of_forall fun a => hasDerivWithinAt_const _ _ _
  hκ := by simpa using isBigO_zero _ _
  hb := (tendsto_nhdsWithin_of_tendsto_nhds (continuous_id.tendsto' 0 0 rfl)).prodMk_nhds
    tendsto_const_nhds
  hu := tendsto_const_nhds
  hgate := by simp

theorem exampleFamily_verdict : exampleFamily.verdict = 1 := by
  simp [InitialGateFamily.verdict, exampleFamily, FiniteAccInvariance.initialVerdict]

theorem exampleFamily_defect_tendsto :
    Tendsto exampleFamily.defect (𝓝[>] 0) (𝓝 1) := by
  have := exampleFamily.defect_tendsto (by simp) (by simp) (by simp)
  rwa [exampleFamily_verdict] at this

end Verdict

end FiniteAccVerdict
end RenewalGeometry

end
