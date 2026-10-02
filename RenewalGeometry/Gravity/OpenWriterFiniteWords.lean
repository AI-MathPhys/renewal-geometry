/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.OpenWriterHermiteResidual
import RenewalGeometry.Gravity.OpenWriterLawCostControl
import RenewalGeometry.DiscreteAnalysis.PeriodicGridPointwisePrecision

/-!
# Finite local successor words of the open writer (`thm:supp-open-finite-words`,
  finite construction; emergent-spacetime manuscript)

The finite chronological Taylor–Hermite realization of the law-family writer
`𝓕_{B,h} = lawField s B` (the open writer is `B = 0`).

* `bankPoly τ β₀ β₁`: the degree-seven two-endpoint Hermite polynomial on `[0, τ]` with value,
  velocity, acceleration and jerk `β₀` at `0` and `β₁` at `τ` (`bankPoly_jets`).
* Banks and words: a *bank sequence* `β j : Fin 4 → (H^{s+1}_h)^{10}` (the finite registers:
  committed value and velocity of the `j`-th source, cached acceleration and jerk); the source
  `X̃_j = (β j 0, β j 1)` (`bankSource`); the letter of stage `j` interpolates the two endpoint
  banks `β j`, `β (j + 1)` (`bankLetter`); the chronological word `bankWord` on `[0, T]` has
  `J = ⌈T h⁻²⌉` cells of duration `τ = T / J ∈ [min(1/2, T) h², h²]`.
* `BankPrecise`: the precision convention of the manuscript, every scaled endpoint jet
  `τ^ℓ Q^{(ℓ)}` of the stage polynomial is within `η` pointwise of the local construction
  (the jets of `Q_{X̃_j}` from `lem:supp-open-hermite-residual`); `exactBank`: the exact
  construction (no rounding, `η = 0`).
* `stage_bounds`: one stage (`lem:supp-open-hermite-residual` +
  `lem:supp-open-hermite-precision` + `sobNorm_le_of_pointwise`).
* `word_energy_bound`: the forced-energy bound along a glued word in the chart.
* `finite_words_bounds` (**finite construction of `thm:supp-open-finite-words`**): for every
  horizon `T` and precision constant `c`, on fine grids and for small initial records, every bank
  word satisfying the precision convention `η = c ε h^{s+10}` is chronological with shared jets
  through order three, its sources stay in the chart, and
  `sup_t ‖(Q, Q')‖_{X^s_h} ≤ C ε`, `‖f‖_{C_t H^s_h} ≤ C ε h⁵`, `‖∂_t f‖_{C_t H^s_h} ≤ C ε h³`
  (`eq:supp-open-finite-defects`, with the derivative even in `H^s_h`), the stage costs obey
  `c_{h,j} ≤ C τ_j (h^{10} + h^6)` and the stopped cost `C_h ≤ C T (h^{10} + h^6)`.
-/

open Set Metric Filter Topology Finset MeasureTheory
open scoped NNReal BigOperators ContDiff

namespace RenewalGeometry.OpenWriterFiniteWords

open TwoPointHermite TaylorHermiteResidual

noncomputable section

/-! ### Two-endpoint Hermite polynomials on `[0, τ]` with prescribed jets -/

section Bank

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The scaled jet family `τ^ℓ β_e ℓ` of two endpoint banks. -/
def bankJets (τ : ℝ) (β₀ β₁ : Fin 4 → E) : Fin 2 × Fin (3 + 1) → E :=
  fun r => τ ^ (r.2 : ℕ) • (if r.1 = 0 then β₀ r.2 else β₁ r.2)

/-- **The Hermite polynomial of two endpoint banks**: the unique polynomial of degree `≤ 7` on
`[0, τ]` with jets (value, velocity, acceleration, jerk) `β₀` at `0` and `β₁` at `τ`. -/
def bankPoly (τ : ℝ) (β₀ β₁ : Fin 4 → E) : Fin 8 → E :=
  scaleCoeffs τ⁻¹ (hermiteCoeffs (k := 3) (bankJets τ β₀ β₁))

theorem bankPoly_jets {τ : ℝ} (hτ : τ ≠ 0) (β₀ β₁ : Fin 4 → E) (i : Fin 4) :
    polyCurveDeriv i (bankPoly τ β₀ β₁) 0 = β₀ i ∧
      polyCurveDeriv i (bankPoly τ β₀ β₁) τ = β₁ i := by
  have hj := jets_hermiteCoeffs (k := 3) (bankJets τ β₀ β₁)
  have h0 := congrFun hj (0, i)
  have h1 := congrFun hj (1, i)
  simp only [jets, bankJets, Fin.isValue, ite_true] at h0 h1
  simp only [Fin.isValue, Fin.val_zero, Nat.cast_zero, Fin.val_one, Nat.cast_one,
    one_ne_zero, ite_false] at h0 h1
  constructor
  · rw [bankPoly, polyCurveDeriv_scaleCoeffs, mul_zero, h0, smul_smul, ← mul_pow,
      inv_mul_cancel₀ hτ, one_pow, one_smul]
  · rw [bankPoly, polyCurveDeriv_scaleCoeffs, inv_mul_cancel₀ hτ, h1, smul_smul, ← mul_pow,
      inv_mul_cancel₀ hτ, one_pow, one_smul]

theorem polyCurveDeriv_sub' {n : ℕ} (j : ℕ) (c c' : Fin n → E) (t : ℝ) :
    polyCurveDeriv j (c - c') t = polyCurveDeriv j c t - polyCurveDeriv j c' t := by
  simp only [polyCurveDeriv, Pi.sub_apply, smul_sub, Finset.sum_sub_distrib]

end Bank

/-! ### Banks, sources and words on the grid -/

section Grid

open RootParityConnector OpenWriterGridBridge OpenWriterChart OpenWriterEnergy HarmonicWriter
  OpenWriterLocalJets OpenWriterLifespan OpenWriterEnergyEstimate PeriodicGridSobolev.GridH
open PeriodicGridSobolev (GridH)

variable {N : ℕ} [NeZero N]

/-- The source `X̃ = (β 0, β 1) ∈ 𝒳^s_h` of a bank (committed value and velocity registers). -/
def bankSource (s : ℕ) (β : Fin 4 → Upper → GridH N (s + 1)) : XS N s :=
  (β 0, iotaG s (β 1))

/-- **The precision convention** (`thm:supp-open-finite-words`): for every stage `j < J` and
`ℓ ≤ 3`, the scaled endpoint jets `τ^ℓ β_j ℓ` and `τ^ℓ β_{j+1} ℓ` of the stage polynomial are
within `η` pointwise (at every site and component) of the scaled jets of the local construction
`Q_{X̃_j}` of `lem:supp-open-hermite-residual`: `J_ℓ(X̃_j)` at `0` and `J_ℓ(X₁)` at `τ`. -/
def BankPrecise (s : ℕ) (B : Upper → Upper → ℝ) (τ η : ℝ) (β : ℕ → Fin 4 → Upper → GridH N (s + 1))
    (J : ℕ) : Prop :=
  ∀ j < J, ∀ (ℓ : Fin 4) (κ : Upper) (x : Grid N),
    τ ^ (ℓ : ℕ) * |val ((β j ℓ - (gridWriter s B).qj ℓ (bankSource s (β j))) κ) x| ≤ η ∧
    τ ^ (ℓ : ℕ) * |val ((β (j + 1) ℓ -
      (gridWriter s B).qj ℓ ((gridWriter s B).endpoint (bankSource s (β j)) τ)) κ) x| ≤ η

/-- The exact sources `X_0 = X₀`, `X_{j+1} = (T_{X_j}(τ), T_{X_j}'(τ))` (no rounding). -/
def exactSources (s : ℕ) (B : Upper → Upper → ℝ) (τ : ℝ) (X₀ : XS N s) : ℕ → XS N s
  | 0 => X₀
  | j + 1 => (gridWriter s B).endpoint (exactSources s B τ X₀ j) τ

/-- **The exact bank sequence**: the writer jets `J_ℓ(X_j)`, `ℓ ≤ 3`, of the exact sources. -/
def exactBank (s : ℕ) (B : Upper → Upper → ℝ) (τ : ℝ) (X₀ : XS N s) :
    ℕ → Fin 4 → Upper → GridH N (s + 1) :=
  fun j ℓ => (gridWriter s B).qj ℓ (exactSources s B τ X₀ j)

theorem bankSource_exactBank (s : ℕ) (B : Upper → Upper → ℝ) (τ : ℝ) (X₀ : XS N s) (j : ℕ) :
    bankSource s (exactBank s B τ X₀ j) = exactSources s B τ X₀ j := by
  refine Prod.ext rfl ?_
  show iotaG s ((gridWriter s B).qj 1 (exactSources s B τ X₀ j)) = _
  rw [Writer.qj_one]
  exact (gridWriter s B).ι_u _

/-- The exact construction satisfies the precision convention with `η = 0`. -/
theorem exactBank_precise (s : ℕ) (B : Upper → Upper → ℝ) (τ : ℝ) (X₀ : XS N s) (J : ℕ) :
    BankPrecise s B τ 0 (exactBank s B τ X₀) J := by
  intro j _ ℓ κ x
  rw [bankSource_exactBank]
  have e1 : exactBank s B τ X₀ j ℓ - (gridWriter s B).qj ℓ (exactSources s B τ X₀ j) = 0 :=
    sub_self _
  have e2 : exactBank s B τ X₀ (j + 1) ℓ -
      (gridWriter s B).qj ℓ ((gridWriter s B).endpoint (exactSources s B τ X₀ j) τ) = 0 :=
    sub_self _
  rw [e1, e2]
  simp

/-- The pointwise-to-Sobolev precision step for the velocity norm of a position-space record. -/
theorem norm_iotaG_le_of_pointwise (s : ℕ) (z : Upper → GridH N (s + 1)) {η : ℝ} (hη : 0 ≤ η)
    (h : ∀ κ x, |val (z κ) x| ≤ η) :
    ‖iotaG s z‖ ≤ PeriodicGridSobolev.precConst s * (N : ℝ) ^ s * η := by
  have hC : 0 ≤ PeriodicGridSobolev.precConst s * (N : ℝ) ^ s * η :=
    mul_nonneg (mul_nonneg (PeriodicGridSobolev.precConst_nonneg s) (by positivity)) hη
  refine (pi_norm_le_iff_of_nonneg hC).mpr fun κ => ?_
  show ‖incl (Nat.le_succ s) (z κ)‖ ≤ _
  rw [norm_def]
  refine PeriodicGridSobolev.sobNorm_le_of_pointwise s _ hη fun x => ?_
  simp only [cxv, incl_val, Complex.norm_real, Real.norm_eq_abs]
  exact h κ x

/-- `τ^i ‖ι y‖ ≤ C_s h^{-s} η` from scaled pointwise errors `τ^i |y(x)| ≤ η`. -/
theorem pow_mul_norm_iotaG_le (s : ℕ) (z : Upper → GridH N (s + 1)) {η τ : ℝ} (hη : 0 ≤ η)
    (hτ : 0 ≤ τ) (i : ℕ) (h : ∀ κ x, τ ^ i * |val (z κ) x| ≤ η) :
    τ ^ i * ‖iotaG s z‖ ≤ PeriodicGridSobolev.precConst s * (N : ℝ) ^ s * η := by
  have e : τ ^ i * ‖iotaG s z‖ = ‖iotaG s (τ ^ i • z)‖ := by
    rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hτ i)]
  rw [e]
  refine norm_iotaG_le_of_pointwise s _ hη fun κ x => ?_
  have : val ((τ ^ i • z) κ) x = τ ^ i * val (z κ) x := rfl
  rw [this, abs_mul, abs_of_nonneg (pow_nonneg hτ i)]
  exact h κ x

/-- `a h ≤ 1` from `h ≤ 1/(a + 1)`. -/
theorem mul_le_one_of_le_one_div {a h : ℝ} (ha : 0 ≤ a) (hh : 0 ≤ h) (H : h ≤ 1 / (a + 1)) :
    a * h ≤ 1 := by
  have hpos : 0 < a + 1 := by linarith
  rw [le_div_iff₀ hpos] at H
  nlinarith

/-- **One stage of the finite construction.**  Fix `s ≥ 2`, a mark bound `b`, `0 < c₋ ≤ c₊` and
a precision constant `c ≥ 0`.  There are `δ > 0`, `N₀` and `C`, independent of the mesh and of the
mark, such that for `N ≥ N₀`, every pair of endpoint banks `β₀, β₁` whose source
`X̃ = (β₀ 0, β₀ 1)` has `‖X̃‖ ≤ ε ≤ δ/4`, every step `c₋h² ≤ τ ≤ c₊h²`, and scaled endpoint jets
within `c ε h^{s+10}` pointwise of those of the local construction `Q_{X̃}`, the stage polynomial
`Q̃ = bankPoly τ β₀ β₁` satisfies on `[0, τ]`: `‖(Q̃, Q̃')‖ ≤ 4ε`, `‖f_{Q̃}‖ ≤ C ε h⁵`,
`f_{Q̃}` is differentiable with `‖∂_t f_{Q̃}‖ ≤ C ε h³`
(`lem:supp-open-hermite-residual`, `lem:supp-open-hermite-precision` and the pointwise precision
step `sobNorm_le_of_pointwise`). -/
theorem stage_bounds (s : ℕ) (hs : 2 ≤ s) (b cm cp cη : ℝ) (hcm : 0 < cm) (hcp : 0 < cp)
    (hcη : 0 ≤ cη) :
    ∃ δ > 0, ∃ N₀ : ℕ, ∃ C ≥ 0, ∀ (N : ℕ) [NeZero N], N₀ ≤ N →
      ∀ (B : Upper → Upper → ℝ), (∀ k l, |B k l| ≤ b) →
      ∀ (β₀ β₁ : Fin 4 → Upper → GridH N (s + 1)) (ε τ : ℝ), ‖bankSource s β₀‖ ≤ ε →
      4 * ε ≤ δ → cm * (1 / (N : ℝ)) ^ 2 ≤ τ → τ ≤ cp * (1 / (N : ℝ)) ^ 2 →
      (∀ (ℓ : Fin 4) (κ : Upper) (x : Grid N),
        τ ^ (ℓ : ℕ) * |val ((β₀ ℓ - (gridWriter s B).qj ℓ (bankSource s β₀)) κ) x| ≤
          cη * ε * (1 / (N : ℝ)) ^ (s + 10) ∧
        τ ^ (ℓ : ℕ) * |val ((β₁ ℓ -
          (gridWriter s B).qj ℓ ((gridWriter s B).endpoint (bankSource s β₀) τ)) κ) x| ≤
          cη * ε * (1 / (N : ℝ)) ^ (s + 10)) →
      ∀ t ∈ Icc 0 τ,
        ‖(gridWriter s B).phase (bankPoly τ β₀ β₁) t‖ ≤ 4 * ε ∧
        ‖(gridWriter s B).defect (bankPoly τ β₀ β₁) t‖ ≤ C * ε * (1 / (N : ℝ)) ^ 5 ∧
        HasDerivAt ((gridWriter s B).defect (bankPoly τ β₀ β₁))
          ((gridWriter s B).defectDeriv (bankPoly τ β₀ β₁) t) t ∧
        ‖(gridWriter s B).defectDeriv (bankPoly τ β₀ β₁) t‖ ≤ C * ε * (1 / (N : ℝ)) ^ 3 := by
  obtain ⟨δ, hδ, A, hA, hB⟩ := gridWriter_bounds s hs b
  obtain ⟨h₁, hh₁, C₁, hC₁, hfull⟩ := hermite_residual_full.{0, 0} A cm cp hA hcm hcp
  obtain ⟨h₂, hh₂, C₂, hC₂, hprec⟩ := hermite_precision.{0, 0} A cm cp 1 hA hcm hcp zero_le_one
  set P := PeriodicGridSobolev.precConst s
  have hP : 0 ≤ P := PeriodicGridSobolev.precConst_nonneg s
  set H0 := hermiteConst 3 0
  set H1 := hermiteConst 3 1
  have hH0 : 0 ≤ H0 := hermiteConst_nonneg 3 0
  have hH1 : 0 ≤ H1 := hermiteConst_nonneg 3 1
  have hA0 : (0 : ℝ) ≤ A := by linarith
  have hPc : 0 ≤ P * cη := mul_nonneg hP hcη
  have hAc : 0 ≤ A * H0 * cp ^ 2 := by positivity
  have hHc : 0 ≤ H1 * cp := mul_nonneg hH1 hcp.le
  set hs' : ℝ := min (min (min h₁ h₂) (cm ^ 2 / (P * cη + 1)))
    (min (min (1 / (2 * (A * H0 * cp ^ 2) + 1)) (1 / (2 * (H1 * cp) + 1))) 1)
  have hs'0 : 0 < hs' := by positivity
  obtain ⟨N₀, hN₀⟩ := exists_nat_ge (1 / hs')
  have e1 : hs' ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  have e2 : hs' ≤ h₁ := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have e3 : hs' ≤ h₂ := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have e4 : hs' ≤ cm ^ 2 / (P * cη + 1) := (min_le_left _ _).trans (min_le_right _ _)
  have e5 : hs' ≤ 1 / (2 * (A * H0 * cp ^ 2) + 1) :=
    (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have e6 : hs' ≤ 1 / (2 * (H1 * cp) + 1) :=
    (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  clear_value hs'
  refine ⟨δ, hδ, N₀ + 1, max C₁ C₂, le_max_of_le_left hC₁,
    fun N _ hN B hBb β₀ β₁ ε τ hX hεδ hτm hτp hpr t ht => ?_⟩
  set h : ℝ := 1 / (N : ℝ) with hhdef
  have hNpos : (0 : ℝ) < N := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
    linarith
  have hh0 : 0 < h := by positivity
  have hhs : h ≤ hs' := by
    have h1 : (1 / hs' : ℝ) ≤ N := hN₀.trans (by exact_mod_cast (Nat.le_succ N₀).trans hN)
    rw [hhdef, div_le_iff₀ hNpos]
    rw [div_le_iff₀ hs'0] at h1
    linarith
  have hh1 : h ≤ 1 := hhs.trans e1
  have hhh₁ : h ≤ h₁ := hhs.trans e2
  have hhh₂ : h ≤ h₂ := hhs.trans e3
  have hhP : h ≤ cm ^ 2 / (P * cη + 1) := hhs.trans e4
  have hhA : h ≤ 1 / (2 * (A * H0 * cp ^ 2) + 1) := hhs.trans e5
  have hhH : h ≤ 1 / (2 * (H1 * cp) + 1) := hhs.trans e6
  have hBN := hB N B hBb
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans hX
  have hτ0 : 0 < τ := lt_of_lt_of_le (by positivity) hτm
  set W := gridWriter (N := N) s B
  set X := bankSource s β₀
  set d : Fin 8 → Upper → GridH N (s + 1) := bankPoly τ β₀ β₁ - W.hermiteC X τ
  have hd : W.hermiteC X τ + d = bankPoly τ β₀ β₁ := by simp only [d]; abel
  set η : ℝ := cη * ε * h ^ (s + 10)
  have hη : 0 ≤ η := by positivity
  set bh : ℝ := P * (N : ℝ) ^ s * η
  have hbh0 : 0 ≤ bh := by positivity
  have hbh_eq : bh = P * cη * ε * h ^ 10 := by
    have hNh : (N : ℝ) * h = 1 := by rw [hhdef]; field_simp
    have : (N : ℝ) ^ s * h ^ (s + 10) = h ^ 10 := by
      rw [pow_add, ← mul_assoc, ← mul_pow, hNh, one_pow, one_mul]
    simp only [bh, η]
    rw [← this]; ring
  -- the endpoint jets of the perturbation
  have hjets : ∀ (e : Fin 2) (i : Fin 4),
      τ ^ (i : ℕ) * ‖W.ι (polyCurveDeriv i d (((e : ℕ) : ℝ) * τ))‖ ≤ bh := by
    intro e i
    have hbp := bankPoly_jets hτ0.ne' β₀ β₁ i
    have hhc := W.hermiteC_jets X hτ0.ne' i
    refine pow_mul_norm_iotaG_le s _ hη hτ0.le i fun κ x => ?_
    fin_cases e
    · simp only [Fin.zero_eta, Fin.isValue, Fin.val_zero, Nat.cast_zero, zero_mul]
      rw [polyCurveDeriv_sub', hbp.1, hhc.1]
      exact (hpr i κ x).1
    · simp only [Fin.mk_one, Fin.isValue, Fin.val_one, Nat.cast_one, one_mul]
      rw [polyCurveDeriv_sub', hbp.2, hhc.2]
      exact (hpr i κ x).2
  obtain ⟨hdj, hsmall⟩ := hprec W h δ hBN hhh₂ X ε τ hX hεδ hτm hτp d bh hjets t ht
  have hτ2 : cm ^ 2 * h ^ 4 ≤ τ ^ 2 := by
    have : cm * h ^ 2 ≤ τ := hτm
    have h0 : 0 ≤ cm * h ^ 2 := by positivity
    nlinarith
  have hbsmall : bh ≤ 1 * ε * τ ^ 2 * h ^ 5 := by
    rw [hbh_eq]
    have h1 : P * cη * h ≤ cm ^ 2 := by
      have hpos : 0 < P * cη + 1 := by positivity
      have h2 := (le_div_iff₀ hpos).mp hhP
      have h3 : 0 ≤ h := hh0.le
      linarith [mul_nonneg h3 hPc]
    have h9 : 0 ≤ ε * h ^ 9 := by positivity
    calc P * cη * ε * h ^ 10 = (P * cη * h) * (ε * h ^ 9) := by ring
      _ ≤ cm ^ 2 * (ε * h ^ 9) := mul_le_mul_of_nonneg_right h1 h9
      _ = ε * (cm ^ 2 * h ^ 4) * h ^ 5 := by ring
      _ ≤ ε * τ ^ 2 * h ^ 5 := by gcongr
      _ = 1 * ε * τ ^ 2 * h ^ 5 := by ring
  obtain ⟨-, -, -, hdef, hder, hdd⟩ := hsmall hbsmall
  obtain ⟨-, -, -, -, hph, -⟩ := hfull W h δ hBN hhh₁ X ε τ hX hεδ hτm hτp t ht
  rw [hd] at hdef hder hdd
  refine ⟨?_, hdef.trans (by gcongr; exact le_max_right _ _), hder,
    hdd.trans (by gcongr; exact le_max_right _ _)⟩
  -- the phase bound
  have hpert := W.phase_pert_le (W.hermiteC X τ) d t
  rw [hd] at hpert
  have hb2 : bh ≤ ε * (cp ^ 2 * h ^ 4) * h ^ 5 := by
    have hτp2 : τ ^ 2 ≤ (cp * h ^ 2) ^ 2 := pow_le_pow_left₀ hτ0.le hτp 2
    calc bh ≤ 1 * ε * τ ^ 2 * h ^ 5 := hbsmall
      _ ≤ 1 * ε * (cp * h ^ 2) ^ 2 * h ^ 5 := by gcongr
      _ = ε * (cp ^ 2 * h ^ 4) * h ^ 5 := by ring
  have hu : ‖W.u‖ ≤ A * h⁻¹ := hBN.norm_u
  have hd0 := hdj 0
  have hd1 := hdj 1
  simp only [pow_zero, div_one, pow_one] at hd0 hd1
  have hterm1 : ‖W.u‖ * ‖W.ι (polyCurveDeriv 0 d t)‖ ≤ ε / 2 := by
    have hprod : ‖W.u‖ * ‖W.ι (polyCurveDeriv 0 d t)‖ ≤ (A * h⁻¹) * (H0 * bh) :=
      mul_le_mul hu hd0 (norm_nonneg _) (by positivity)
    refine hprod.trans ?_
    have hk : 2 * (A * H0 * cp ^ 2) * h ≤ 1 := mul_le_one_of_le_one_div (by positivity) hh0.le hhA
    have hh8 : h ^ 8 ≤ h := by
      calc h ^ 8 ≤ h ^ 1 := pow_le_pow_of_le_one hh0.le hh1 (by norm_num)
        _ = h := pow_one h
    calc A * h⁻¹ * (H0 * bh) ≤ A * h⁻¹ * (H0 * (ε * (cp ^ 2 * h ^ 4) * h ^ 5)) := by gcongr
      _ = (A * H0 * cp ^ 2) * h ^ 8 * ε := by field_simp
      _ ≤ (A * H0 * cp ^ 2) * h * ε := by gcongr
      _ ≤ ε / 2 := by
          have := mul_le_mul_of_nonneg_right hk hε0
          linarith
  have hterm2 : ‖W.ι (polyCurveDeriv 1 d t)‖ ≤ ε / 2 := by
    refine hd1.trans ?_
    have hk : 2 * (H1 * cp) * h ≤ 1 := mul_le_one_of_le_one_div (by positivity) hh0.le hhH
    have hτb : bh / τ ≤ ε * cp * h ^ 7 := by
      rw [div_le_iff₀ hτ0]
      calc bh ≤ 1 * ε * τ ^ 2 * h ^ 5 := hbsmall
        _ = ε * τ * h ^ 5 * τ := by ring
        _ ≤ ε * (cp * h ^ 2) * h ^ 5 * τ := by gcongr
        _ = ε * cp * h ^ 7 * τ := by ring
    have hh7 : h ^ 7 ≤ h := by
      calc h ^ 7 ≤ h ^ 1 := pow_le_pow_of_le_one hh0.le hh1 (by norm_num)
        _ = h := pow_one h
    calc H1 * bh / τ = H1 * (bh / τ) := by ring
      _ ≤ H1 * (ε * cp * h ^ 7) := by gcongr
      _ ≤ H1 * (ε * cp * h) := by gcongr
      _ ≤ ε / 2 := by
          have := mul_le_mul_of_nonneg_right hk hε0
          linarith
  calc ‖W.phase (bankPoly τ β₀ β₁) t‖ ≤ ‖W.phase (W.hermiteC X τ) t‖ +
        ‖W.phase (bankPoly τ β₀ β₁) t - W.phase (W.hermiteC X τ) t‖ := norm_le_insert' _ _
    _ ≤ 3 * ε + (ε / 2 + ε / 2) := add_le_add hph (hpert.trans (add_le_add hterm1 hterm2))
    _ = 4 * ε := by ring

/-! ### The chronological bank word -/

/-- The number of cells `J = ⌈T h⁻²⌉` on `[0, T]` at mesh `h = 1/N`. -/
def numCells (N : ℕ) (T : ℝ) : ℕ := ⌈T * (N : ℝ) ^ 2⌉₊

/-- The cell duration `τ = T / J`. -/
def stepOf (N : ℕ) (T : ℝ) : ℝ := T / numCells N T

/-- The letter of stage `j`: the Hermite polynomial of the endpoint banks `β j`, `β (j + 1)`. -/
def bankLetter {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (τ : ℝ)
    (β : ℕ → Fin 4 → E) (j : ℕ) : Fin 8 → E :=
  bankPoly τ (β j) (β (j + 1))

/-- **The chronological bank word** on `[0, T]`: `J = ⌈T h⁻²⌉` cells of duration `τ = T/J`,
letter `j` the symmetric record polynomial of `bankLetter τ β j`, no failure. -/
def bankWord (s : ℕ) (T : ℝ) (β : ℕ → Fin 4 → Upper → GridH N (s + 1)) : LawWord N where
  J := numCells N T
  deg := 7
  node := fun j => (j : ℝ) * stepOf N T
  letter := fun j i => recOf (bankLetter (stepOf N T) β j i)
  fail := none

theorem numCells_pos {T : ℝ} (hT : 0 < T) : 0 < numCells N T := by
  unfold numCells
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
  exact Nat.ceil_pos.mpr (by positivity)

theorem stepOf_pos {T : ℝ} (hT : 0 < T) : 0 < stepOf N T := by
  unfold stepOf
  have := numCells_pos (N := N) hT
  positivity

/-- The cell duration is comparable to `h²`: `min(1/2, T) h² ≤ τ ≤ h²`. -/
theorem stepOf_bounds {T : ℝ} (hT : 0 < T) :
    min (1 / 2) T * (1 / (N : ℝ)) ^ 2 ≤ stepOf N T ∧ stepOf N T ≤ 1 * (1 / (N : ℝ)) ^ 2 := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hN : (0 : ℝ) < N := by linarith
  have hJ := numCells_pos (N := N) hT
  have hJr : (0 : ℝ) < numCells N T := by exact_mod_cast hJ
  have hceil : T * (N : ℝ) ^ 2 ≤ numCells N T := Nat.le_ceil _
  have hceil2 : (numCells N T : ℝ) < T * (N : ℝ) ^ 2 + 1 := Nat.ceil_lt_add_one (by positivity)
  unfold stepOf
  constructor
  · rw [le_div_iff₀ hJr]
    by_cases h1 : 1 ≤ T * (N : ℝ) ^ 2
    · have : (numCells N T : ℝ) ≤ 2 * (T * (N : ℝ) ^ 2) := by linarith
      calc min (1 / 2) T * (1 / (N : ℝ)) ^ 2 * (numCells N T)
          ≤ 1 / 2 * (1 / (N : ℝ)) ^ 2 * (2 * (T * (N : ℝ) ^ 2)) := by
            gcongr
            exact min_le_left _ _
        _ = T := by field_simp
    · push Not at h1
      have hJ1 : numCells N T = 1 := by
        unfold numCells
        rw [Nat.ceil_eq_iff (by norm_num)]
        constructor
        · norm_num; positivity
        · norm_num; exact h1.le
      rw [hJ1, Nat.cast_one, mul_one]
      calc min (1 / 2) T * (1 / (N : ℝ)) ^ 2 ≤ T * 1 := by
            gcongr
            · exact min_le_right _ _
            · rw [div_pow, one_pow]
              exact div_le_one_of_le₀ (by nlinarith) (by positivity)
        _ = T := mul_one T
  · rw [div_le_iff₀ hJr]
    calc T = 1 * (1 / (N : ℝ)) ^ 2 * (T * (N : ℝ) ^ 2) := by field_simp
      _ ≤ 1 * (1 / (N : ℝ)) ^ 2 * (numCells N T) := by gcongr

/-- Record arrays commute with polynomial evaluation. -/
theorem recOf_polyCurveDeriv {r n : ℕ} (k : ℕ) (c : Fin n → Upper → GridH N r) (σ : ℝ) :
    polyCurveDeriv k (fun i => recOf (c i)) σ = recOf (polyCurveDeriv k c σ) := by
  funext x μ ν
  simp only [polyCurveDeriv, recOf, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, val_sum,
    val_smul]

theorem recOf_iotaG {s : ℕ} (z : Upper → GridH N (s + 1)) : recOf (iotaG s z) = recOf z := rfl

theorem bankWord_path (s : ℕ) (T : ℝ) (β : ℕ → Fin 4 → Upper → GridH N (s + 1)) (k : ℕ)
    (t : ℝ) :
    (bankWord s T β).path k t = recOf (SplineGluing.splinePath (fun j => (j : ℝ) * stepOf N T)
      (numCells N T) (bankLetter (stepOf N T) β) k t) := by
  simp only [LawWord.path, SplineGluing.splinePath, bankWord]
  exact recOf_polyCurveDeriv k _ _

theorem bankWord_node_strictMono (s : ℕ) {T : ℝ} (hT : 0 < T)
    (β : ℕ → Fin 4 → Upper → GridH N (s + 1)) : StrictMono (bankWord s T β).node := by
  have hτ := stepOf_pos (N := N) hT
  refine strictMono_nat_of_lt_succ fun n => ?_
  simp only [bankWord]; push_cast; nlinarith

theorem bankWord_jetsMatch (s : ℕ) {T : ℝ} (hT : 0 < T)
    (β : ℕ → Fin 4 → Upper → GridH N (s + 1)) :
    SplineGluing.JetsMatch (bankWord s T β).node (bankWord s T β).J (bankWord s T β).letter 3 := by
  intro j _ k hk
  have hτ := stepOf_pos (N := N) hT
  have e : (bankWord s T β).node (j + 1) - (bankWord s T β).node j = stepOf N T := by
    simp only [bankWord]; push_cast; ring
  rw [e]
  have h1 := (bankPoly_jets hτ.ne' (β j) (β (j + 1)) ⟨k, by omega⟩).2
  have h2 := (bankPoly_jets hτ.ne' (β (j + 1)) (β (j + 1 + 1)) ⟨k, by omega⟩).1
  simp only [bankWord]
  rw [recOf_polyCurveDeriv, recOf_polyCurveDeriv]
  simp only [bankLetter]
  rw [h1, h2]

/-- **The bank word is chronological** on `[0, T]` at mesh `h = 1/N`, with
`min(1/2, T) h² ≤ τ ≤ h²`, shared endpoint jets through order three and symmetric letters. -/
theorem bankWord_isChronological (s : ℕ) {T : ℝ} (hT : 0 < T)
    (β : ℕ → Fin 4 → Upper → GridH N (s + 1)) :
    (bankWord s T β).IsChronological (N : ℝ)⁻¹ (min (1 / 2) T) 1 T := by
  have hJ := numCells_pos (N := N) hT
  have hJr : (numCells N T : ℝ) ≠ 0 := by exact_mod_cast hJ.ne'
  obtain ⟨hb1, hb2⟩ := stepOf_bounds (N := N) hT
  refine ⟨hJ, by simp [bankWord], ?_, bankWord_node_strictMono s hT β, ?_,
    bankWord_jetsMatch s hT β, fun j i => isSymRec_recOf (bankLetter (stepOf N T) β j i), fun j hj => by simp [bankWord] at hj⟩
  · simp only [bankWord, stepOf]; field_simp
  · intro j _
    have e : (bankWord s T β).node (j + 1) - (bankWord s T β).node j = stepOf N T := by
      simp only [bankWord]; push_cast; ring
    rw [e, inv_eq_one_div]
    exact ⟨hb1, hb2⟩

end Grid

end

end RenewalGeometry.OpenWriterFiniteWords
