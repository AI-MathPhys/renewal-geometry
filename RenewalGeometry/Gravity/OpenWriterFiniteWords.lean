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
* `finite_words_strict_margin`: on a fine tail, every stage cost is strictly below `M τ_j h⁴` for
  any fixed `M > 0` and the stopped cost is at most `h²` (the strict residual margin).
* `lattice_banks_exist`: finite registers.  For every tolerance there is a lattice `(M + 1)⁻¹ ℤ`
  carrying a bank sequence (`latBank`: rounded value/velocity registers, rounded acceleration and
  jerk caches reused at the next source) obeying the precision convention, with starting record
  as close as desired to the given one; at fixed `h` this is a finite alphabet.
* `stage_local`: fixed execution radius.  The stage polynomial and the successor caches on the box
  of radius `ρ` depend only on the source on the box of radius `ρ + 20`.
The Einstein-limit clause is `finite_words_einstein` (`OpenWriterFiniteWordsEinstein.lean`).
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

/-! ### Cells of the bank word -/

theorem bankWord_node (s : ℕ) (T : ℝ) (β : ℕ → Fin 4 → Upper → GridH N (s + 1)) (j : ℕ) :
    (bankWord s T β).node j = (j : ℝ) * stepOf N T := rfl

theorem bankWord_J (s : ℕ) (T : ℝ) (β : ℕ → Fin 4 → Upper → GridH N (s + 1)) :
    (bankWord s T β).J = numCells N T := rfl

/-- On the cell of a time `t ∈ [0, T]`, the word is the current letter at a local time in
`[0, τ]`, also on a right neighbourhood. -/
theorem bankWord_cell (s : ℕ) {T : ℝ} (hT : 0 < T) (β : ℕ → Fin 4 → Upper → GridH N (s + 1))
    {t : ℝ} (ht : t ∈ Icc 0 T) :
    SplineGluing.cellIdx (fun j => (j : ℝ) * stepOf N T) (numCells N T) t < numCells N T ∧
    t - SplineGluing.cellIdx (fun j => (j : ℝ) * stepOf N T) (numCells N T) t * stepOf N T ∈
      Icc 0 (stepOf N T) ∧
    (∀ k, (bankWord s T β).path k t = recOf (polyCurveDeriv k (bankLetter (stepOf N T) β
      (SplineGluing.cellIdx (fun j => (j : ℝ) * stepOf N T) (numCells N T) t))
      (t - SplineGluing.cellIdx (fun j => (j : ℝ) * stepOf N T) (numCells N T) t *
        stepOf N T))) ∧
    ∀ k, ∀ᶠ σ in 𝓝[≥] t, (bankWord s T β).path k σ = recOf (polyCurveDeriv k
      (bankLetter (stepOf N T) β
        (SplineGluing.cellIdx (fun j => (j : ℝ) * stepOf N T) (numCells N T) t))
      (σ - SplineGluing.cellIdx (fun j => (j : ℝ) * stepOf N T) (numCells N T) t *
        stepOf N T)) := by
  set node : ℕ → ℝ := fun j => (j : ℝ) * stepOf N T with hnode
  set J := numCells N T
  set i := SplineGluing.cellIdx node J t
  have hJ := numCells_pos (N := N) hT
  have hτ := stepOf_pos (N := N) hT
  have hmono : StrictMono node := bankWord_node_strictMono s hT β
  have hiJ : i ≤ J - 1 := SplineGluing.cellIdx_le node J t
  refine ⟨by omega, ⟨?_, ?_⟩, fun k => ?_, fun k => ?_⟩
  · by_cases hi : i = 0
    · rw [hi]; simp only [Nat.cast_zero, zero_mul, sub_zero]; exact ht.1
    · have := SplineGluing.cellIdx_spec (t := node) (J := J) (τ := t) hi
      simp only [node] at this; linarith
  · by_cases hi : i + 1 ≤ J - 1
    · have := SplineGluing.lt_of_cellIdx (t := node) (J := J) (τ := t) hi
      simp only [node] at this; push_cast at this; linarith
    · have hiJ' : i + 1 = J := by omega
      have hT' : T = (J : ℝ) * stepOf N T := by
        simp only [J, stepOf]; field_simp
      have : ((i : ℝ) + 1) = J := by exact_mod_cast hiJ'
      nlinarith [ht.2]
  · rw [bankWord_path]; rfl
  · have h := SplineGluing.eventually_right (J := J) (c := bankLetter (stepOf N T) β) hmono k t
    filter_upwards [h] with σ hσ
    rw [bankWord_path, hσ]

/-- The word at a node is the bank: `Q^{(k)}(t_j) = β_j k` for `j ≤ J`. -/
theorem bankWord_path_node (s : ℕ) {T : ℝ} (hT : 0 < T) (β : ℕ → Fin 4 → Upper → GridH N (s + 1))
    {j : ℕ} (hj : j ≤ numCells N T) (k : Fin 4) :
    (bankWord s T β).path k ((j : ℝ) * stepOf N T) = recOf (β j k) := by
  set node : ℕ → ℝ := fun j => (j : ℝ) * stepOf N T with hnode
  have hJ := numCells_pos (N := N) hT
  have hτ := stepOf_pos (N := N) hT
  have hmono : StrictMono node := bankWord_node_strictMono s hT β
  rw [bankWord_path]
  by_cases hjJ : j ≤ numCells N T - 1
  · have hc : SplineGluing.cellIdx node (numCells N T) (node j) = j :=
      SplineGluing.cellIdx_eq hmono hjJ (fun _ => le_rfl) fun _ => hmono (Nat.lt_succ_self j)
    simp only [SplineGluing.splinePath]
    rw [show (fun j : ℕ => (j : ℝ) * stepOf N T) = node from rfl, hc, sub_self]
    exact congrArg recOf (bankPoly_jets hτ.ne' (β j) (β (j + 1)) k).1
  · have hj' : j = numCells N T := by omega
    have hc : SplineGluing.cellIdx node (numCells N T) (node j) = numCells N T - 1 := by
      refine SplineGluing.cellIdx_eq hmono le_rfl (fun _ => hmono.monotone (by omega)) ?_
      intro h; omega
    simp only [SplineGluing.splinePath]
    rw [show (fun j : ℕ => (j : ℝ) * stepOf N T) = node from rfl, hc]
    have e : node j - node (numCells N T - 1) = stepOf N T := by
      simp only [node]; rw [hj', Nat.cast_sub (by omega)]; push_cast; ring
    rw [e]
    have := (bankPoly_jets hτ.ne' (β (numCells N T - 1)) (β (numCells N T - 1 + 1)) k).2
    simp only [bankLetter]
    rw [this, show numCells N T - 1 + 1 = j by omega]

/-- Before the node `t_j` (`1 ≤ j ≤ J`), the word is one of the letters `i < j` at a local time
in `[0, τ]`. -/
theorem bankWord_before (s : ℕ) {T : ℝ} (hT : 0 < T) (β : ℕ → Fin 4 → Upper → GridH N (s + 1))
    {j : ℕ} (hj1 : 1 ≤ j) (hjJ : j ≤ numCells N T) {t : ℝ}
    (ht : t ∈ Icc 0 ((j : ℝ) * stepOf N T)) :
    ∃ i < j, ∃ σ ∈ Icc 0 (stepOf N T), ∀ k : Fin 4,
      (bankWord s T β).path k t = recOf (polyCurveDeriv k (bankLetter (stepOf N T) β i) σ) := by
  set node : ℕ → ℝ := fun j => (j : ℝ) * stepOf N T with hnode
  have hτ := stepOf_pos (N := N) hT
  have hmono : StrictMono node := bankWord_node_strictMono s hT β
  have hT' : T = (numCells N T : ℝ) * stepOf N T := by
    have := numCells_pos (N := N) hT
    simp only [stepOf]; field_simp
  have htT : t ∈ Icc 0 T := by
    refine ⟨ht.1, ht.2.trans ?_⟩
    have : (j : ℝ) * stepOf N T ≤ (numCells N T : ℝ) * stepOf N T := by
      gcongr
    linarith
  obtain ⟨hiJ, hσ, hrep, -⟩ := bankWord_cell s hT β htT
  set i := SplineGluing.cellIdx node (numCells N T) t
  by_cases hij : i < j
  · exact ⟨i, hij, _, hσ, fun k => hrep k⟩
  · have hi0 : i ≠ 0 := by omega
    have h1 : node i ≤ t := SplineGluing.cellIdx_spec hi0
    have h2 : node i ≤ node j := h1.trans ht.2
    have hij' : i = j := le_antisymm (hmono.le_iff_le.mp h2) (not_lt.mp hij)
    have htj : t = node j := le_antisymm ht.2 (hij' ▸ h1)
    refine ⟨j - 1, by omega, stepOf N T, ⟨hτ.le, le_rfl⟩, fun k => ?_⟩
    rw [htj]
    show (bankWord s T β).path k ((j : ℝ) * stepOf N T) = _
    rw [bankWord_path_node s hT β hjJ k]
    have := (bankPoly_jets hτ.ne' (β (j - 1)) (β (j - 1 + 1)) k).2
    rw [show j - 1 + 1 = j by omega] at this
    simp only [bankLetter]
    rw [show j - 1 + 1 = j by omega, this]

/-! ### Bridges between the writer form and the record form -/

/-- The upper components of the word residual are the writer defect of the current letter. -/
theorem comp_residual_of_rep (s : ℕ) (B : Upper → Upper → ℝ) (W : LawWord N)
    (c : Fin 8 → Upper → GridH N (s + 1)) (σ t : ℝ)
    (h0 : W.path 0 t = recOf (polyCurveDeriv 0 c σ)) (h1 : W.path 1 t = recOf (polyCurveDeriv 1 c σ))
    (h2 : W.path 2 t = recOf (polyCurveDeriv 2 c σ)) (κ : Upper) :
    comp (W.residual B t) κ.1.1 κ.1.2 = val ((gridWriter s B).defect c σ κ) := by
  have e1 : comp (W.residual B t) κ.1.1 κ.1.2 =
      comp (W.path 2 t) κ.1.1 κ.1.2 - comp (lawAccel B (W.path 0 t) (W.path 1 t)) κ.1.1 κ.1.2 :=
    rfl
  rw [e1, h2, comp_recOf, h0, h1, polyCurveDeriv_zero]
  rfl

/-- The record `H^r_h` norm is controlled by the writer norm of ten upper components. -/
theorem Fnorm_le_of_comp {r : ℕ} (f : Grid N → MetricRec) (D : Upper → GridH N r)
    (h : ∀ κ : Upper, comp f κ.1.1 κ.1.2 = val (D κ)) :
    Fnorm r f ≤ Real.sqrt (Fintype.card Upper) * ‖D‖ := by
  rw [Fnorm, ← Real.sqrt_sq (norm_nonneg D), ← Real.sqrt_mul (by positivity)]
  refine Real.sqrt_le_sqrt ?_
  have hκ : ∀ κ : Upper, PeriodicGridSobolev.sobSq r (cx (comp f κ.1.1 κ.1.2)) ≤ ‖D‖ ^ 2 := by
    intro κ
    rw [h κ, ← PeriodicGridSobolev.sobNorm_sq]
    have : PeriodicGridSobolev.sobNorm r (cx (val (D κ))) = ‖D κ‖ := rfl
    rw [this]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm D κ) 2
  calc ∑ κ : Upper, PeriodicGridSobolev.sobSq r (cx (comp f κ.1.1 κ.1.2)) ≤
        ∑ _κ : Upper, ‖D‖ ^ 2 := Finset.sum_le_sum fun κ _ => hκ κ
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- The record norm of the word is controlled by the writer norm of the phase. -/
theorem recNorm_le_of_rep (s : ℕ) (B : Upper → Upper → ℝ) (W : LawWord N)
    (c : Fin 8 → Upper → GridH N (s + 1)) (σ t : ℝ)
    (h0 : W.path 0 t = recOf (polyCurveDeriv 0 c σ)) (h1 : W.path 1 t = recOf (polyCurveDeriv 1 c σ)) :
    W.recNorm s t ≤ Real.sqrt (2 * Fintype.card Upper) * ‖(gridWriter s B).phase c σ‖ := by
  have e : W.recNorm s t = Xnorm s (recOf ((gridWriter s B).phase c σ).1)
      (recOf ((gridWriter s B).phase c σ).2) := by
    rw [LawWord.recNorm, h0, h1, polyCurveDeriv_zero]; rfl
  rw [e]
  exact Xnorm_le_norm s _

/-! ### The forced energy along a glued word -/

/-- **Forced-energy bound along a chronological word** (`eq:supp-law-forced` integrated).  For
`s ≥ 3` there are a chart radius `ρ > 0` and `K ≥ 0`, independent of the mesh, the mark and the
word, such that for every word with shared jets through order three and symmetric letters, if on
`[0, t₁]` the record stays in `‖(Q, Q')‖_{X^s_h} ≤ ρ` and the actual defect obeys
`‖f‖_{s,h} ≤ G`, then
`‖(Q, Q')(t₁)‖_{X^s_h} ≤ 3 e^{K t₁} (3 ‖(Q, Q')(0)‖_{X^s_h} + K G t₁)`. -/
theorem word_energy_bound (s : ℕ) (hs : 3 ≤ s) :
    ∃ ρ > 0, ∃ K ≥ 0, ∀ (N : ℕ) [NeZero N] (B : Upper → Upper → ℝ), IsMark (1 / 48) B →
      ∀ (W : LawWord N), StrictMono W.node → SplineGluing.JetsMatch W.node W.J W.letter 3 →
      (∀ j i, IsSymRec (W.letter j i)) → ∀ (t₁ G : ℝ), 0 ≤ t₁ → 0 ≤ G →
      (∀ τ ∈ Icc 0 t₁, W.recNorm s τ ≤ ρ ∧ Fnorm s (W.residual B τ) ≤ G) →
      W.recNorm s t₁ ≤ 3 * Real.exp (K * t₁) * (3 * W.recNorm s 0 + K * (G * t₁)) := by
  obtain ⟨δF, hδF, CF, hCF, hF⟩ := law_forced_energy s hs
  obtain ⟨δ0, hδ0, K₁, hK₁, hpc⟩ := pointwise_chart s hs
  refine ⟨min δF (min δ0 1), by positivity, 8 * CF, by positivity,
    fun N _ B hB W ht hm hsym t₁ G ht₁ hG hle => ?_⟩
  set ρ := min δF (min δ0 1)
  have hρF : ρ ≤ δF := min_le_left _ _
  have hρ0 : ρ ≤ δ0 := (min_le_right _ _).trans (min_le_left _ _)
  have hρ1 : ρ ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  set K : ℝ := 8 * CF
  have hK : 0 ≤ K := by positivity
  set φ : ℝ → ℝ := W.recNorm s
  set f : ℝ → Grid N → MetricRec := W.residual B
  have hsym0 : ∀ τ, IsSymRec (W.path 0 τ) := LawWord.isSymRec_path W hsym 0
  have hsym1 : ∀ τ, IsSymRec (W.path 1 τ) := LawWord.isSymRec_path W hsym 1
  have hq : ∀ τ x, HasDerivAt (fun σ => W.path 0 σ x) (W.path 1 τ x) τ := fun τ x =>
    hasDerivAt_pi.1 (LawWord.hasDerivAt_path ht hm (k := 0) (by norm_num) τ) x
  have hv : ∀ τ x (κ : Upper), HasDerivAt (fun σ => W.path 1 σ x κ.1.1 κ.1.2)
      (lawAccel B (W.path 0 τ) (W.path 1 τ) x κ.1.1 κ.1.2 + f τ x κ.1.1 κ.1.2) τ := by
    intro τ x κ
    have h := hasDerivAt_pi.1 (hasDerivAt_pi.1 (hasDerivAt_pi.1
      (LawWord.hasDerivAt_path ht hm (k := 1) (by norm_num) τ) x) κ.1.1) κ.1.2
    refine h.congr_deriv ?_
    simp only [f, LawWord.residual, Pi.sub_apply]
    ring
  set E : ℝ → ℝ := fun τ => lawEnergy B s (W.path 0 τ) (W.path 1 τ)
  have hstep : ∀ τ ∈ Icc 0 t₁, ∃ e', HasDerivAt E e' τ ∧
      e' ≤ K * E τ + K * Real.sqrt (E τ) * G := by
    intro τ hτ
    have hφτ : φ τ ≤ ρ := (hle τ hτ).1
    obtain ⟨r, hr, hlow, hrb, -⟩ := hF N B (W.path 0) (W.path 1) f τ hB (hsym0 τ) (hsym1 τ)
      (hq τ) (hv τ) (hφτ.trans hρF)
    obtain ⟨ha, hc, -⟩ := hpc N (W.path 0 τ) (W.path 1 τ) (hsym0 τ) (hsym1 τ)
      (hφτ.trans hρ0)
    have hup := (lawEnergy_bounds s hB le_rfl (W.path 0 τ) (W.path 1 τ) ha hc).2
    have hXsq : Xsq s (W.path 0 τ) (W.path 1 τ) = φ τ ^ 2 := (Xnorm_sq _ _ _).symm
    have hφ0' : 0 ≤ φ τ := Xnorm_nonneg _ _ _
    have hE0 : 0 ≤ E τ := le_trans (by rw [hXsq]; positivity) hlow
    have hE9 : E τ ≤ 9 := by
      have : φ τ ^ 2 ≤ 1 := by nlinarith
      simp only [E]; rw [hXsq] at hup; linarith
    have hss : Real.sqrt (E τ) * Real.sqrt (E τ) = E τ := Real.mul_self_sqrt hE0
    have hsE0 := Real.sqrt_nonneg (E τ)
    have hg0 := Fnorm_nonneg s (f τ)
    have hfG : Fnorm s (f τ) ≤ G := (hle τ hτ).2
    refine ⟨r, hr, ?_⟩
    have h1 : E τ * Real.sqrt (E τ) ≤ 3 * E τ := by
      have hsE : Real.sqrt (E τ) ≤ 3 := by
        rw [show (3 : ℝ) = Real.sqrt 9 by
          rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_le_sqrt hE9
      nlinarith
    have hexp : 2 * Real.sqrt (E τ) * (CF * Real.sqrt (E τ) + CF * E τ + CF * Fnorm s (f τ)) =
        2 * CF * E τ + 2 * CF * (E τ * Real.sqrt (E τ)) +
          2 * CF * (Real.sqrt (E τ) * Fnorm s (f τ)) := by
      linear_combination (2 * CF) * hss
    have hrb' : r ≤ 2 * Real.sqrt (E τ) *
        (CF * Real.sqrt (E τ) + CF * E τ + CF * Fnorm s (f τ)) := hrb
    rw [hexp] at hrb'
    have h3 : 2 * CF * (E τ * Real.sqrt (E τ)) ≤ 2 * CF * (3 * E τ) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h4 : 2 * CF * (Real.sqrt (E τ) * Fnorm s (f τ)) ≤ 2 * CF * (Real.sqrt (E τ) * G) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hfG hsE0) (by positivity)
    have h5 : 0 ≤ CF * (Real.sqrt (E τ) * G) := by positivity
    have e6 : K * Real.sqrt (E τ) * G = 8 * (CF * (Real.sqrt (E τ) * G)) := by simp only [K]; ring
    have e7 : K * E τ = 8 * CF * E τ := rfl
    rw [e6, e7]
    linarith
  have hE0 : ∀ τ ∈ Icc 0 t₁, 0 ≤ E τ := by
    intro τ hτ
    obtain ⟨r, -, hlow, -⟩ := hF N B (W.path 0) (W.path 1) f τ hB (hsym0 τ) (hsym1 τ)
      (hq τ) (hv τ) ((hle τ hτ).1.trans hρF)
    exact le_trans (by have := Xsq_nonneg s (W.path 0 τ) (W.path 1 τ); linarith) hlow
  have hgr := ODECutoff.sqrt_le_of_forced_deriv hK hstep hE0 continuousOn_const
    (fun _ _ => hG) t₁ ⟨ht₁, le_rfl⟩
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hgr
  have h0mem : (0 : ℝ) ∈ Icc 0 t₁ := ⟨le_rfl, ht₁⟩
  have hE0b : Real.sqrt (E 0) ≤ 3 * φ 0 := by
    obtain ⟨ha, hc, -⟩ := hpc N (W.path 0 0) (W.path 1 0) (hsym0 0) (hsym1 0)
      ((hle 0 h0mem).1.trans hρ0)
    have hup := (lawEnergy_bounds s hB le_rfl (W.path 0 0) (W.path 1 0) ha hc).2
    have hXsq : Xsq s (W.path 0 0) (W.path 1 0) = φ 0 ^ 2 := (Xnorm_sq _ _ _).symm
    have hφ0' : 0 ≤ φ 0 := Xnorm_nonneg _ _ _
    rw [Real.sqrt_le_left (by positivity)]
    simp only [E]; rw [hXsq] at hup; nlinarith
  have hφt : φ t₁ ≤ 3 * Real.sqrt (E t₁) := by
    have htm : t₁ ∈ Icc 0 t₁ := ⟨ht₁, le_rfl⟩
    obtain ⟨r, -, hlow, -⟩ := hF N B (W.path 0) (W.path 1) f t₁ hB (hsym0 t₁) (hsym1 t₁)
      (hq t₁) (hv t₁) ((hle t₁ htm).1.trans hρF)
    have hXsq : Xsq s (W.path 0 t₁) (W.path 1 t₁) = φ t₁ ^ 2 := (Xnorm_sq _ _ _).symm
    rw [hXsq] at hlow
    have hEt := hE0 t₁ htm
    have hs3 : (3 * Real.sqrt (E t₁)) ^ 2 = 9 * E t₁ := by
      rw [mul_pow, Real.sq_sqrt hEt]; norm_num
    have hφ0' : 0 ≤ φ t₁ := Xnorm_nonneg _ _ _
    nlinarith [Real.sqrt_nonneg (E t₁)]
  have hexp0 : 0 ≤ Real.exp (K * t₁) := (Real.exp_pos _).le
  calc φ t₁ ≤ 3 * Real.sqrt (E t₁) := hφt
    _ ≤ 3 * (Real.exp (K * t₁) * (Real.sqrt (E 0) + K * (t₁ * G))) := by gcongr
    _ ≤ 3 * (Real.exp (K * t₁) * (3 * φ 0 + K * (t₁ * G))) := by gcongr
    _ = 3 * Real.exp (K * t₁) * (3 * W.recNorm s 0 + K * (G * t₁)) := by ring

/-- The time derivative of the word residual is the writer derivative of the defect of the
current letter, when the word coincides with that letter on a right neighbourhood. -/
theorem comp_deriv_residual_of_right (s : ℕ) (B : Upper → Upper → ℝ) (W : LawWord N)
    (c : Fin 8 → Upper → GridH N (s + 1)) (a t : ℝ)
    (h0 : ∀ᶠ σ in 𝓝[≥] t, W.path 0 σ = recOf (polyCurveDeriv 0 c (σ - a)))
    (h1 : ∀ᶠ σ in 𝓝[≥] t, W.path 1 σ = recOf (polyCurveDeriv 1 c (σ - a)))
    (h2 : ∀ᶠ σ in 𝓝[≥] t, W.path 2 σ = recOf (polyCurveDeriv 2 c (σ - a)))
    (hdiff : DifferentiableAt ℝ (W.residual B) t)
    (hD : HasDerivAt ((gridWriter s B).defect c) ((gridWriter s B).defectDeriv c (t - a)) (t - a))
    (κ : Upper) :
    comp (deriv (W.residual B) t) κ.1.1 κ.1.2 = val ((gridWriter s B).defectDeriv c (t - a) κ) := by
  funext x
  set L : (Upper → GridH N s) →L[ℝ] ℝ := (ContinuousLinearMap.proj x).comp
    ((toFunL (N := N) (r := s)).toContinuousLinearMap.comp (ContinuousLinearMap.proj κ))
  have hL : ∀ D : Upper → GridH N s, L D = val (D κ) x := fun D => rfl
  have hg : HasDerivAt (fun σ => L ((gridWriter s B).defect c (σ - a)))
      (L ((gridWriter s B).defectDeriv c (t - a))) t :=
    L.hasFDerivAt.comp_hasDerivAt t (hD.comp_sub_const t a)
  have hr : HasDerivAt (fun σ => W.residual B σ x κ.1.1 κ.1.2)
      (deriv (W.residual B) t x κ.1.1 κ.1.2) t :=
    hasDerivAt_pi.1 (hasDerivAt_pi.1 (hasDerivAt_pi.1 hdiff.hasDerivAt x) κ.1.1) κ.1.2
  have heq : (fun σ => W.residual B σ x κ.1.1 κ.1.2) =ᶠ[𝓝[≥] t]
      fun σ => L ((gridWriter s B).defect c (σ - a)) := by
    filter_upwards [h0, h1, h2] with σ e0 e1 e2
    rw [hL]
    exact congrFun (comp_residual_of_rep s B W c (σ - a) σ e0 e1 e2 κ) x
  have hgW : HasDerivWithinAt (fun σ => W.residual B σ x κ.1.1 κ.1.2)
      (L ((gridWriter s B).defectDeriv c (t - a))) (Ici t) t :=
    hg.hasDerivWithinAt.congr_of_eventuallyEq heq (heq.self_of_nhdsWithin (le_refl t : t ∈ Ici t))
  exact (uniqueDiffWithinAt_Ici t).eq_deriv _ hr.hasDerivWithinAt hgW

/-! ### The finite construction -/

theorem LawWord.guardTime_le (W : LawWord N) (s : ℕ) (ρ T : ℝ) : W.guardTime s ρ T ≤ T := by
  unfold LawWord.guardTime
  split_ifs with h
  · obtain ⟨t, ht, hρ⟩ := h
    refine (csInf_le ?_ ?_).trans ht.2
    · exact ⟨0, fun τ hτ => hτ.1.1⟩
    · exact ⟨ht, hρ⟩
  · exact le_rfl

set_option maxHeartbeats 1600000 in
-- the induction over the stages and the global bounds share all constants
/-- **The finite construction of `thm:supp-open-finite-words`.**  Fix `s ≥ 5` (the manuscript
takes `s ≥ 11`), a horizon `T > 0` and a precision constant `c ≥ 0`.  There are `ε₀ > 0`, `N₀`
and `C`, independent of the mesh `h = 1/N` and of the mark `B` (`B = Bᵀ`, `‖B‖_op ≤ 1/48`; the
open writer is `B = 0`), with the following property.  Let `β` be any bank sequence whose initial
record has `‖(β 0 0, β 0 1)‖_{X^s_h} ≤ ε ≤ ε₀` and whose scaled endpoint jets obey the precision
convention `η = c ε h^{s+10}` relative to the local construction (`BankPrecise`; the exact
construction `exactBank` has `η = 0`).  Then on the bank word `Q_h` (`bankWord`, chronological
with `τ ≍ h²` and shared endpoint jets through order three by `bankWord_isChronological`):

* every source stays in the chart, `‖X̃_j‖ ≤ C ε` for `j ≤ J`;
* `sup_{t ≤ T} ‖(Q_h, Q_h')‖_{X^s_h} ≤ C ε`, `‖f_h^{num}(t)‖_{H^s_h} ≤ C ε h⁵`, and `f_h^{num}`
  is differentiable on `[0, T]` with `‖∂_t f_h^{num}(t)‖_{H^s_h} ≤ C ε h³`
  (`eq:supp-open-finite-defects`, the derivative even at the top order `H^s_h`);
* the physical stage costs obey `c_{h,j} = ε⁻² ∫_{I_j} (‖f‖²_{s,h} + ‖∂_t f‖²_{s-3,h}) ≤
  C τ_j (h^{10} + h^6)`, and the stopped cost (any guard radius) `C_h ≤ C T (h^{10} + h^6)`. -/
theorem finite_words_bounds (s : ℕ) (hs : 5 ≤ s) (T : ℝ) (hT : 0 < T) (cη : ℝ) (hcη : 0 ≤ cη) :
    ∃ ε₀ > 0, ∃ N₀ : ℕ, ∃ C ≥ 0, ∀ (N : ℕ) [NeZero N], N₀ ≤ N →
      ∀ (B : Upper → Upper → ℝ), IsMark (1 / 48) B →
      ∀ (β : ℕ → Fin 4 → Upper → GridH N (s + 1)) (ε : ℝ), 0 ≤ ε → ε ≤ ε₀ →
      Xnorm s (recOf (β 0 0)) (recOf (β 0 1)) ≤ ε →
      BankPrecise s B (stepOf N T) (cη * ε * (1 / (N : ℝ)) ^ (s + 10)) β (numCells N T) →
      (∀ j ≤ numCells N T, ‖bankSource s (β j)‖ ≤ C * ε) ∧
      (∀ t ∈ Icc 0 T, (bankWord s T β).recNorm s t ≤ C * ε ∧
        Fnorm s ((bankWord s T β).residual B t) ≤ C * ε * (1 / (N : ℝ)) ^ 5 ∧
        DifferentiableAt ℝ ((bankWord s T β).residual B) t ∧
        Fnorm s (deriv ((bankWord s T β).residual B) t) ≤ C * ε * (1 / (N : ℝ)) ^ 3) ∧
      (∀ j < numCells N T, (ε ^ 2)⁻¹ * ∫ t in ((j : ℝ) * stepOf N T)..(((j + 1 : ℕ) : ℝ) *
          stepOf N T), (bankWord s T β).costDensity B s t ≤
        C * stepOf N T * ((1 / (N : ℝ)) ^ 10 + (1 / (N : ℝ)) ^ 6)) ∧
      (∀ ρ, (bankWord s T β).cost B s ρ ε T ≤ C * T * ((1 / (N : ℝ)) ^ 10 + (1 / (N : ℝ)) ^ 6)) := by
  have hcm : 0 < min (1 / 2 : ℝ) T := lt_min (by norm_num) hT
  obtain ⟨δH, hδH, N₁, CH, hCH, hst⟩ := stage_bounds s (by omega) (1 / 48) (min (1 / 2) T) 1 cη
    hcm one_pos hcη
  obtain ⟨ρE, hρE, K, hK, hen⟩ := word_energy_bound s (by omega)
  obtain ⟨ρc, hρc, hres⟩ := residual_contDiffAt s (by omega)
  set S20 : ℝ := Real.sqrt (2 * Fintype.card Upper)
  set S10 : ℝ := Real.sqrt (Fintype.card Upper)
  have hcard0 : 0 < Fintype.card Upper :=
    Fintype.card_pos_iff.mpr ⟨⟨((0 : Fin 4), (0 : Fin 4)), le_refl _⟩⟩
  have hcard : (0 : ℝ) < Fintype.card Upper := by exact_mod_cast hcard0
  have hS20 : 0 < S20 := Real.sqrt_pos.mpr (by positivity)
  have hS10 : 0 ≤ S10 := Real.sqrt_nonneg _
  set eK : ℝ := Real.exp (K * T)
  have heK : 1 ≤ eK := Real.one_le_exp (by positivity)
  set Λ : ℝ := 18 * eK
  have hΛ : 0 < Λ := by positivity
  set ρ' : ℝ := min ρE (ρc / 2)
  have hρ' : 0 < ρ' := by positivity
  set ε₀ : ℝ := min (δH / 4) (ρ' / (4 * S20)) / Λ
  have hε₀ : 0 < ε₀ := by positivity
  set a : ℝ := 6 * eK * K * S10 * CH * T
  have ha : 0 ≤ a := by positivity
  obtain ⟨N₂, hN₂⟩ := exists_nat_ge (a + 1)
  set C : ℝ := S20 * 4 * Λ + S10 * CH * Λ + Λ + (S10 * CH * Λ) ^ 2 * 2
  refine ⟨ε₀, hε₀, max N₁ N₂, C, by positivity, fun N _ hN B hB β ε hε0 hεε₀ hX0 hprec => ?_⟩
  -- the mesh
  set h : ℝ := 1 / (N : ℝ) with hhdef
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hNpos : (0 : ℝ) < N := by linarith
  have hh0 : 0 < h := by positivity
  have hh1 : h ≤ 1 := by rw [hhdef, div_le_one hNpos]; exact hN1
  have hNN₁ : N₁ ≤ N := (le_max_left _ _).trans hN
  have hah : a * h ≤ 1 := by
    have h2 : (a + 1 : ℝ) ≤ N := hN₂.trans (by exact_mod_cast (le_max_right _ _).trans hN)
    refine mul_le_one_of_le_one_div ha hh0.le ?_
    rw [hhdef]
    exact one_div_le_one_div_of_le (by positivity) h2
  set J := numCells N T
  set τ := stepOf N T
  have hJ : 0 < J := numCells_pos hT
  have hτ : 0 < τ := stepOf_pos hT
  obtain ⟨hτm, hτp⟩ := stepOf_bounds (N := N) hT
  have hJr : (numCells N T : ℝ) ≠ 0 := by exact_mod_cast hJ.ne'
  have hTJ : T = (J : ℝ) * τ := by simp only [J, τ, stepOf]; field_simp
  set W := bankWord s T β
  have hWmono : StrictMono W.node := bankWord_node_strictMono s hT β
  have hWjm := bankWord_jetsMatch s hT β
  have hWsym : ∀ j i, IsSymRec (W.letter j i) := fun j i =>
    isSymRec_recOf (bankLetter (stepOf N T) β j i)
  set ε1 : ℝ := Λ * ε
  have hε1 : 0 ≤ ε1 := by positivity
  have hεε1 : ε ≤ ε1 := by simp only [ε1, Λ]; nlinarith
  have hε1δ : 4 * ε1 ≤ δH := by
    have : ε * Λ ≤ δH / 4 := by
      have := (le_div_iff₀ hΛ).mp hεε₀
      exact this.trans (min_le_left _ _)
    simp only [ε1]; linarith
  have hε1ρ : S20 * (4 * ε1) ≤ ρ' := by
    have h1 : ε * Λ ≤ ρ' / (4 * S20) := ((le_div_iff₀ hΛ).mp hεε₀).trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h1
    simp only [ε1]; linarith
  have hBent : ∀ k l, |B k l| ≤ 1 / 48 := hB.entry_le
  -- one stage with a source in the chart
  have hstage : ∀ i < J, ‖bankSource s (β i)‖ ≤ ε1 → ∀ σ ∈ Icc 0 τ,
      ‖(gridWriter s B).phase (bankLetter τ β i) σ‖ ≤ 4 * ε1 ∧
      ‖(gridWriter s B).defect (bankLetter τ β i) σ‖ ≤ CH * ε1 * h ^ 5 ∧
      HasDerivAt ((gridWriter s B).defect (bankLetter τ β i))
        ((gridWriter s B).defectDeriv (bankLetter τ β i) σ) σ ∧
      ‖(gridWriter s B).defectDeriv (bankLetter τ β i) σ‖ ≤ CH * ε1 * h ^ 3 := by
    intro i hi hsrc σ hσ
    refine hst N hNN₁ B hBent (β i) (β (i + 1)) ε1 τ hsrc hε1δ hτm hτp (fun ℓ κ x => ?_) σ hσ
    obtain ⟨p1, p2⟩ := hprec i hi ℓ κ x
    have hmono : cη * ε * h ^ (s + 10) ≤ cη * ε1 * h ^ (s + 10) := by gcongr
    exact ⟨p1.trans hmono, p2.trans hmono⟩
  -- consequences of a representation by a good stage
  have hrep : ∀ (i : ℕ) (σ t : ℝ), i < J → ‖bankSource s (β i)‖ ≤ ε1 → σ ∈ Icc 0 τ →
      (∀ k : Fin 4, W.path k t = recOf (polyCurveDeriv k (bankLetter τ β i) σ)) →
      W.recNorm s t ≤ S20 * (4 * ε1) ∧ Fnorm s (W.residual B t) ≤ S10 * (CH * ε1 * h ^ 5) := by
    intro i σ t hi hsrc hσ hk
    obtain ⟨g1, g2, -, -⟩ := hstage i hi hsrc σ hσ
    refine ⟨(recNorm_le_of_rep s B W _ σ t (hk 0) (hk 1)).trans
      (mul_le_mul_of_nonneg_left g1 hS20.le), ?_⟩
    refine (Fnorm_le_of_comp _ _ (comp_residual_of_rep s B W _ σ t (hk 0) (hk 1) (hk 2))).trans ?_
    exact mul_le_mul_of_nonneg_left g2 hS10
  -- the initial record
  have hrec0 : W.recNorm s 0 = Xnorm s (recOf (β 0 0)) (recOf (β 0 1)) := by
    have e0 := bankWord_path_node s hT β (j := 0) (Nat.zero_le _) 0
    have e1 := bankWord_path_node s hT β (j := 0) (Nat.zero_le _) 1
    simp only [Nat.cast_zero, zero_mul, Fin.val_zero, Fin.val_one] at e0 e1
    simp only [LawWord.recNorm, W]
    rw [e0, e1]
  -- the stage induction: all sources stay in the chart
  have hsrc : ∀ j ≤ J, ‖bankSource s (β j)‖ ≤ ε1 := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hjJ
      rcases Nat.eq_zero_or_pos j with hj0 | hj0
      · subst hj0
        exact (norm_le_Xnorm s (bankSource s (β 0))).trans (hX0.trans hεε1)
      · have hgood : ∀ i < j, ‖bankSource s (β i)‖ ≤ ε1 := fun i hi => ih i hi (by omega)
        set t₁ : ℝ := (j : ℝ) * τ
        have ht₁ : 0 ≤ t₁ := by positivity
        have ht₁T : t₁ ≤ T := by
          have hjr : (j : ℝ) ≤ J := by exact_mod_cast hjJ
          calc t₁ = (j : ℝ) * τ := rfl
            _ ≤ (J : ℝ) * τ := mul_le_mul_of_nonneg_right hjr hτ.le
            _ = T := hTJ.symm
        set G : ℝ := S10 * (CH * ε1 * h ^ 5)
        have hG : 0 ≤ G := by positivity
        have hloc : ∀ τ' ∈ Icc 0 t₁, W.recNorm s τ' ≤ ρE ∧ Fnorm s (W.residual B τ') ≤ G := by
          intro τ' hτ'
          obtain ⟨i, hij, σ, hσ, hk⟩ := bankWord_before s hT β hj0 hjJ hτ'
          obtain ⟨r1, r2⟩ := hrep i σ τ' (by omega) (hgood i hij) hσ hk
          exact ⟨r1.trans (hε1ρ.trans (min_le_left _ _)), r2⟩
        have hE := hen N B hB W hWmono hWjm hWsym t₁ G ht₁ hG hloc
        have hnode : W.recNorm s t₁ = Xnorm s (recOf (β j 0)) (recOf (β j 1)) := by
          have e0 := bankWord_path_node s hT β hjJ 0
          have e1 := bankWord_path_node s hT β hjJ 1
          simp only [Fin.val_zero, Fin.val_one] at e0 e1
          simp only [LawWord.recNorm, W, t₁]
          rw [e0, e1]
        have hX : ‖bankSource s (β j)‖ ≤ W.recNorm s t₁ := by
          rw [hnode]; exact norm_le_Xnorm s (bankSource s (β j))
        have hexp : Real.exp (K * t₁) ≤ eK := Real.exp_le_exp.mpr (by gcongr)
        have hGT : K * (G * t₁) ≤ K * (G * T) := by gcongr
        have h5 : h ^ 5 ≤ h := by
          calc h ^ 5 ≤ h ^ 1 := pow_le_pow_of_le_one hh0.le hh1 (by norm_num)
            _ = h := pow_one h
        have hsmall : 3 * eK * (K * (G * T)) ≤ ε1 / 2 := by
          have e : 3 * eK * (K * (G * T)) = (a / 2) * h ^ 5 * ε1 := by
            simp only [G, a]; ring
          rw [e]
          have h6 : (a / 2) * h ^ 5 ≤ 1 / 2 := by nlinarith
          nlinarith
        have h9 : 3 * eK * (3 * ε) ≤ ε1 / 2 := by simp only [ε1, Λ]; nlinarith
        have hr0 : 0 ≤ W.recNorm s 0 := Xnorm_nonneg _ _ _
        calc ‖bankSource s (β j)‖ ≤ W.recNorm s t₁ := hX
          _ ≤ 3 * Real.exp (K * t₁) * (3 * W.recNorm s 0 + K * (G * t₁)) := hE
          _ ≤ 3 * eK * (3 * ε + K * (G * T)) := by
              have hx : 3 * W.recNorm s 0 + K * (G * t₁) ≤ 3 * ε + K * (G * T) := by
                have h0 : W.recNorm s 0 ≤ ε := hrec0 ▸ hX0
                linarith
              have hx0 : 0 ≤ 3 * W.recNorm s 0 + K * (G * t₁) :=
                add_nonneg (by linarith) (mul_nonneg hK (mul_nonneg hG ht₁))
              have he0 : (0 : ℝ) ≤ 3 * eK := by linarith
              exact mul_le_mul (mul_le_mul_of_nonneg_left hexp (by norm_num)) hx hx0 he0
          _ = 3 * eK * (3 * ε) + 3 * eK * (K * (G * T)) := by ring
          _ ≤ ε1 / 2 + ε1 / 2 := add_le_add h9 hsmall
          _ = ε1 := by ring
  -- the constants
  have hε1C : ε1 ≤ C * ε := by
    have : Λ ≤ C := by
      have h1 : 0 ≤ S20 * 4 * Λ := by positivity
      have h2 : 0 ≤ S10 * CH * Λ := by positivity
      have h3 : 0 ≤ (S10 * CH * Λ) ^ 2 * 2 := by positivity
      simp only [C]; linarith
    simp only [ε1]; exact mul_le_mul_of_nonneg_right this hε0
  have hC1 : S20 * (4 * ε1) ≤ C * ε := by
    have : S20 * 4 * Λ ≤ C := by
      have h2 : 0 ≤ S10 * CH * Λ := by positivity
      have h3 : 0 ≤ (S10 * CH * Λ) ^ 2 * 2 := by positivity
      simp only [C]; linarith
    calc S20 * (4 * ε1) = (S20 * 4 * Λ) * ε := by simp only [ε1]; ring
      _ ≤ C * ε := mul_le_mul_of_nonneg_right this hε0
  have hCk : S10 * CH * Λ ≤ C := by
    have h1 : 0 ≤ S20 * 4 * Λ := by positivity
    have h3 : 0 ≤ (S10 * CH * Λ) ^ 2 * 2 := by positivity
    simp only [C]; linarith
  have hC2 : ∀ m : ℕ, S10 * (CH * ε1 * h ^ m) ≤ C * ε * h ^ m := by
    intro m
    calc S10 * (CH * ε1 * h ^ m) = (S10 * CH * Λ) * ε * h ^ m := by simp only [ε1]; ring
      _ ≤ C * ε * h ^ m := by gcongr
  have hCD : (S10 * CH * Λ) ^ 2 ≤ C := by
    have h1 : 0 ≤ S20 * 4 * Λ := by positivity
    have h2 : 0 ≤ S10 * CH * Λ := by positivity
    have h3 : 0 ≤ (S10 * CH * Λ) ^ 2 := by positivity
    simp only [C]; linarith
  have hρc' : S20 * (4 * ε1) < ρc := by
    have : ρ' ≤ ρc / 2 := min_le_right _ _
    linarith
  -- the global pointwise bounds
  have hglob : ∀ t ∈ Icc 0 T, W.recNorm s t ≤ S20 * (4 * ε1) ∧
      Fnorm s (W.residual B t) ≤ S10 * (CH * ε1 * h ^ 5) ∧
      DifferentiableAt ℝ (W.residual B) t ∧
      Fnorm s (deriv (W.residual B) t) ≤ S10 * (CH * ε1 * h ^ 3) := by
    intro t ht
    obtain ⟨hiJ, hσ, hrp, hev⟩ := bankWord_cell s hT β ht
    set i := SplineGluing.cellIdx (fun j => (j : ℝ) * stepOf N T) (numCells N T) t
    have hsi := hsrc i hiJ.le
    obtain ⟨r1, r2⟩ := hrep i _ t hiJ hsi hσ (fun k => hrp k)
    obtain ⟨-, -, hD, hDb⟩ := hstage i hiJ hsi _ hσ
    have hdiff : DifferentiableAt ℝ (W.residual B) t :=
      (hres N B W hWmono hWjm hWsym t (lt_of_le_of_lt r1 hρc')).differentiableAt (by norm_num)
    have hcomp := comp_deriv_residual_of_right s B W (bankLetter τ β i) ((i : ℝ) * τ) t
      (hev 0) (hev 1) (hev 2) hdiff hD
    refine ⟨r1, r2, hdiff, ?_⟩
    exact (Fnorm_le_of_comp _ _ hcomp).trans (mul_le_mul_of_nonneg_left hDb hS10)
  -- the cost density
  set D : ℝ := (S10 * CH * Λ) ^ 2 * ε ^ 2 * (h ^ 10 + h ^ 6)
  have hD0 : 0 ≤ D := by positivity
  have hdens : ∀ t ∈ Icc 0 T, ‖W.costDensity B s t‖ ≤ D := by
    intro t ht
    obtain ⟨-, g2, -, g4⟩ := hglob t ht
    have g4' : Fnorm (s - 3) (deriv (W.residual B) t) ≤ S10 * (CH * ε1 * h ^ 3) :=
      (lawDiff_Fnorm_mono (by omega) _).trans g4
    rw [Real.norm_eq_abs, abs_of_nonneg (W.costDensity_nonneg B s t)]
    have a1 := pow_le_pow_left₀ (Fnorm_nonneg _ _) g2 2
    have a2 := pow_le_pow_left₀ (Fnorm_nonneg _ _) g4' 2
    calc W.costDensity B s t = Fnorm s (W.residual B t) ^ 2 +
          Fnorm (s - 3) (deriv (W.residual B) t) ^ 2 := rfl
      _ ≤ (S10 * (CH * ε1 * h ^ 5)) ^ 2 + (S10 * (CH * ε1 * h ^ 3)) ^ 2 := add_le_add a1 a2
      _ = D := by simp only [D, ε1]; ring
  -- `(ε²)⁻¹ ε² ≤ 1`
  have hεinv : (ε ^ 2)⁻¹ * ε ^ 2 ≤ 1 := by
    rcases eq_or_lt_of_le hε0 with h0 | h0
    · rw [← h0]; norm_num
    · rw [inv_mul_cancel₀ (by positivity)]
  have hint : ∀ a b : ℝ, a ≤ b → Icc a b ⊆ Icc 0 T →
      (ε ^ 2)⁻¹ * ∫ t in a..b, W.costDensity B s t ≤
        (S10 * CH * Λ) ^ 2 * (b - a) * (h ^ 10 + h ^ 6) := by
    intro a b hab hsub
    have hn := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b)
      (f := fun t => W.costDensity B s t) (C := D) fun x hx => by
        rw [uIoc_of_le hab] at hx
        exact hdens x (hsub ⟨hx.1.le, hx.2⟩)
    have hle : (∫ t in a..b, W.costDensity B s t) ≤ D * (b - a) := by
      rw [abs_of_nonneg (by linarith)] at hn
      exact (le_abs_self _).trans (by rw [← Real.norm_eq_abs]; exact hn)
    have hinv0 : 0 ≤ (ε ^ 2)⁻¹ := by positivity
    calc (ε ^ 2)⁻¹ * ∫ t in a..b, W.costDensity B s t ≤ (ε ^ 2)⁻¹ * (D * (b - a)) :=
          mul_le_mul_of_nonneg_left hle hinv0
      _ = ((ε ^ 2)⁻¹ * ε ^ 2) * ((S10 * CH * Λ) ^ 2 * (b - a) * (h ^ 10 + h ^ 6)) := by
          simp only [D]; ring
      _ ≤ 1 * ((S10 * CH * Λ) ^ 2 * (b - a) * (h ^ 10 + h ^ 6)) := by
          have : 0 ≤ b - a := by linarith
          gcongr
      _ = _ := one_mul _
  have hpow : 0 ≤ h ^ 10 + h ^ 6 := by positivity
  refine ⟨fun j hj => (hsrc j hj).trans hε1C, fun t ht => ?_, fun j hj => ?_, fun ρ => ?_⟩
  · obtain ⟨g1, g2, g3, g4⟩ := hglob t ht
    exact ⟨g1.trans hC1, g2.trans (hC2 5), g3, g4.trans (hC2 3)⟩
  · have hab : (j : ℝ) * τ ≤ ((j + 1 : ℕ) : ℝ) * τ := by
      gcongr; exact_mod_cast Nat.le_succ j
    have hsub : Icc ((j : ℝ) * τ) (((j + 1 : ℕ) : ℝ) * τ) ⊆ Icc 0 T := by
      intro x hx
      have hjr : ((j + 1 : ℕ) : ℝ) ≤ J := by exact_mod_cast hj
      refine ⟨le_trans (by positivity) hx.1, hx.2.trans ?_⟩
      rw [hTJ]; exact mul_le_mul_of_nonneg_right hjr hτ.le
    refine (hint _ _ hab hsub).trans ?_
    have e : ((j + 1 : ℕ) : ℝ) * τ - (j : ℝ) * τ = τ := by push_cast; ring
    rw [e]
    gcongr
  · have hstop : W.stopTime s ρ T = W.guardTime s ρ T := rfl
    have hg0 := W.guardTime_nonneg s ρ hT.le
    have hgT := LawWord.guardTime_le W s ρ T
    have hfail : (if W.fail.isSome then (1 : ℝ) else 0) = 0 := rfl
    have hc : W.cost B s ρ ε T = (ε ^ 2)⁻¹ * ∫ t in (0)..(W.guardTime s ρ T),
        W.costDensity B s t := by
      simp only [LawWord.cost, hstop, hfail, add_zero]
    rw [hc]
    refine (hint 0 _ hg0 (Icc_subset_Icc le_rfl hgT)).trans ?_
    rw [sub_zero]
    have : (S10 * CH * Λ) ^ 2 * W.guardTime s ρ T * (h ^ 10 + h ^ 6) ≤
        C * W.guardTime s ρ T * (h ^ 10 + h ^ 6) := by gcongr
    refine this.trans ?_
    gcongr

theorem BankPrecise.mono {s : ℕ} {B : Upper → Upper → ℝ} {τ η η' : ℝ}
    {β : ℕ → Fin 4 → Upper → GridH N (s + 1)} {J : ℕ} (h : BankPrecise s B τ η β J)
    (hη : η ≤ η') : BankPrecise s B τ η' β J := fun j hj ℓ κ x =>
  ⟨(h j hj ℓ κ x).1.trans hη, (h j hj ℓ κ x).2.trans hη⟩

/-! ### Registers on a rational lattice (finite alphabet) -/

/-- Rounding to the lattice `(M + 1)⁻¹ ℤ`. -/
def roundLat (M : ℕ) (y : ℝ) : ℝ := (round (y * ((M : ℝ) + 1)) : ℝ) / ((M : ℝ) + 1)

theorem abs_roundLat_sub_le (M : ℕ) (y : ℝ) : |roundLat M y - y| ≤ 1 / ((M : ℝ) + 1) := by
  have hM : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have h := abs_sub_round (y * ((M : ℝ) + 1))
  have e : roundLat M y - y = -(y * ((M : ℝ) + 1) - round (y * ((M : ℝ) + 1))) / ((M : ℝ) + 1) := by
    unfold roundLat; field_simp; ring
  rw [e, abs_div, abs_neg, abs_of_pos hM, div_le_div_iff_of_pos_right hM]
  linarith

/-- Entrywise rounding of a ten-component record to the lattice `(M + 1)⁻¹ ℤ`. -/
def roundRec {r : ℕ} (M : ℕ) (z : Upper → GridH N r) : Upper → GridH N r :=
  fun κ => PeriodicGridSobolev.GridH.mk (fun x => roundLat M (val (z κ) x))

theorem roundRec_mem_lattice {r : ℕ} (M : ℕ) (z : Upper → GridH N r) (κ : Upper) (x : Grid N) :
    ∃ m : ℤ, val (roundRec M z κ) x = (m : ℝ) / ((M : ℝ) + 1) :=
  ⟨round (val (z κ) x * ((M : ℝ) + 1)), rfl⟩

theorem norm_roundRec_sub_le {r : ℕ} (M : ℕ) (z : Upper → GridH N r) :
    ‖roundRec M z - z‖ ≤ PeriodicGridSobolev.precConst r * (N : ℝ) ^ r * (1 / ((M : ℝ) + 1)) := by
  have hC : 0 ≤ PeriodicGridSobolev.precConst r * (N : ℝ) ^ r * (1 / ((M : ℝ) + 1)) :=
    mul_nonneg (mul_nonneg (PeriodicGridSobolev.precConst_nonneg r) (by positivity)) (by positivity)
  refine (pi_norm_le_iff_of_nonneg hC).mpr fun κ => ?_
  rw [norm_def]
  refine PeriodicGridSobolev.sobNorm_le_of_pointwise r _ (by positivity) fun x => ?_
  simp only [cxv, Pi.sub_apply, val_sub, Complex.norm_real, Real.norm_eq_abs]
  exact abs_roundLat_sub_le M _

/-- Rounding along a convergent sequence converges to the same limit. -/
theorem tendsto_roundRec {r : ℕ} {z : ℕ → Upper → GridH N r} {z₀ : Upper → GridH N r}
    (hz : Tendsto z atTop (𝓝 z₀)) : Tendsto (fun M => roundRec M (z M)) atTop (𝓝 z₀) := by
  have h0 : Tendsto (fun M : ℕ => PeriodicGridSobolev.precConst r * (N : ℝ) ^ r *
      (1 / ((M : ℝ) + 1))) atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
      (PeriodicGridSobolev.precConst r * (N : ℝ) ^ r)
    simpa using this
  have hd : Tendsto (fun M => roundRec M (z M) - z M) atTop (𝓝 0) :=
    squeeze_zero_norm (fun M => norm_roundRec_sub_le M (z M)) h0
  have := hd.add hz
  simpa using this

variable (s : ℕ) (B : Upper → Upper → ℝ) (τ : ℝ) (X₀ : XS N s)

/-- **The lattice registers** (rounded value and velocity of the sources): the initial record
and every successor `(T_{X̃_j}(τ), T_{X̃_j}'(τ))` rounded to `(M + 1)⁻¹ ℤ`. -/
def latRegs (M : ℕ) : ℕ → (Upper → GridH N (s + 1)) × (Upper → GridH N (s + 1))
  | 0 => (roundRec M X₀.1, roundRec M (upG s X₀.2))
  | j + 1 =>
    ((roundRec M ((gridWriter s B).endpoint ((latRegs M j).1, iotaG s (latRegs M j).2) τ).1),
      roundRec M (upG s ((gridWriter s B).endpoint ((latRegs M j).1, iotaG s (latRegs M j).2) τ).2))

/-- The source `X̃_j` of the lattice registers. -/
def latSrc (M j : ℕ) : XS N s := ((latRegs s B τ X₀ M j).1, iotaG s (latRegs s B τ X₀ M j).2)

/-- **The lattice bank**: rounded value and velocity, and the rounded acceleration and jerk caches
`J_2(X̃_j)`, `J_3(X̃_j)`. -/
def latBank (M j : ℕ) : Fin 4 → Upper → GridH N (s + 1) :=
  ![(latRegs s B τ X₀ M j).1, (latRegs s B τ X₀ M j).2,
    roundRec M ((gridWriter s B).qj 2 (latSrc s B τ X₀ M j)),
    roundRec M ((gridWriter s B).qj 3 (latSrc s B τ X₀ M j))]

theorem bankSource_latBank (M j : ℕ) :
    bankSource s (latBank s B τ X₀ M j) = latSrc s B τ X₀ M j := rfl

theorem latBank_mem_lattice (M j : ℕ) (ℓ : Fin 4) (κ : Upper) (x : Grid N) :
    ∃ m : ℤ, val (latBank s B τ X₀ M j ℓ κ) x = (m : ℝ) / ((M : ℝ) + 1) := by
  have hR : ∀ i, (∃ m : ℤ, val ((latRegs s B τ X₀ M i).1 κ) x = (m : ℝ) / ((M : ℝ) + 1)) ∧
      ∃ m : ℤ, val ((latRegs s B τ X₀ M i).2 κ) x = (m : ℝ) / ((M : ℝ) + 1) := by
    intro i
    cases i with
    | zero => exact ⟨roundRec_mem_lattice M _ κ x, roundRec_mem_lattice M _ κ x⟩
    | succ i => exact ⟨roundRec_mem_lattice M _ κ x, roundRec_mem_lattice M _ κ x⟩
  fin_cases ℓ
  · exact (hR j).1
  · exact (hR j).2
  · exact roundRec_mem_lattice M _ κ x
  · exact roundRec_mem_lattice M _ κ x

theorem latSrc_succ (M j : ℕ) : latSrc s B τ X₀ M (j + 1) =
    (roundRec M ((gridWriter s B).endpoint (latSrc s B τ X₀ M j) τ).1,
      iotaG s (roundRec M (upG s ((gridWriter s B).endpoint (latSrc s B τ X₀ M j) τ).2))) := rfl

/-- The endpoint map `X ↦ (T_X(τ), T_X'(τ))` is continuous wherever the writer jets are. -/
theorem continuousAt_endpoint {Y : XS N s}
    (hq : ∀ i, ContinuousAt ((gridWriter s B).qj i) Y) :
    ContinuousAt (fun Z => (gridWriter s B).endpoint Z τ) Y := by
  set W := gridWriter (N := N) s B
  have ht : ContinuousAt (fun Z => W.taylorC Z) Y :=
    continuousAt_pi.2 fun i => by
      show ContinuousAt (fun Z => (((i : ℕ).factorial : ℝ))⁻¹ • W.qj i Z) Y
      exact (hq i).const_smul ((((i : ℕ).factorial : ℝ))⁻¹)
  have hg : Continuous fun c : Fin 8 → Upper → GridH N (s + 1) =>
      (polyCurve c τ, W.ι (polyCurveDeriv 1 c τ)) := by
    refine Continuous.prodMk ?_ (W.ι.continuous.comp ?_)
    · unfold polyCurve
      exact continuous_finsetSum _ fun i _ => by fun_prop
    · unfold polyCurveDeriv
      exact continuous_finsetSum _ fun i _ => by fun_prop
  exact hg.continuousAt.comp ht

/-- **Lattice (finite-alphabet) realization of the precision convention.**  Fix `s ≥ 5` and
`T > 0`.  There are `ε₁ > 0` and `N₀` such that for `N ≥ N₀`, every mark `B` of the closed ball,
every initial record `X₀` with `‖X₀‖_{X^s_h} ≤ ε ≤ ε₁` and all tolerances `η, ζ > 0`, some lattice
`(M + 1)⁻¹ ℤ` carries a bank sequence (`latBank`: every register of every stage is a lattice
point) obeying the precision convention with tolerance `η` and whose starting record is within
`ζ` of `X₀` in `X^s_h`.  At fixed `h` the registers of the `J` stages are finitely many lattice
points, so the realization uses a finite alphabet. -/
theorem lattice_banks_exist (hs : 5 ≤ s) {T : ℝ} (hT : 0 < T) :
    ∃ ε₁ > 0, ∃ N₀ : ℕ, ∀ (N : ℕ) [NeZero N], N₀ ≤ N →
      ∀ (B : Upper → Upper → ℝ), IsMark (1 / 48) B →
      ∀ (X₀ : XS N s) (ε : ℝ), Xnorm s (recOf X₀.1) (recOf X₀.2) ≤ ε → ε ≤ ε₁ →
      ∀ η > 0, ∀ ζ > 0, ∃ M : ℕ,
        (∀ j ℓ κ x, ∃ m : ℤ,
          val (latBank s B (stepOf N T) X₀ M j ℓ κ) x = (m : ℝ) / ((M : ℝ) + 1)) ∧
        BankPrecise s B (stepOf N T) η (latBank s B (stepOf N T) X₀ M) (numCells N T) ∧
        Xnorm s (recOf (latBank s B (stepOf N T) X₀ M 0 0) - recOf X₀.1)
          (recOf (latBank s B (stepOf N T) X₀ M 0 1) - recOf X₀.2) ≤ ζ := by
  obtain ⟨δG, hδG, A, hA, hBd⟩ := gridWriter_bounds s (by omega) (1 / 48)
  obtain ⟨ε₀, hε₀, N₀, C, hC, hFW⟩ := finite_words_bounds s hs T hT 0 le_rfl
  refine ⟨min ε₀ (δG / (2 * (C + 1))), by positivity, N₀,
    fun N _ hN B hB X₀ ε hX hεε η hη ζ hζ => ?_⟩
  set W := gridWriter (N := N) s B
  set τ := stepOf N T
  set J := numCells N T
  have hε0 : 0 ≤ ε := (Xnorm_nonneg _ _ _).trans hX
  -- the exact sources stay in the chart of the writer
  have hex : ∀ j ≤ J, ‖exactSources s B τ X₀ j‖ ≤ C * ε := by
    have hstart : Xnorm s (recOf (exactBank s B τ X₀ 0 0)) (recOf (exactBank s B τ X₀ 0 1)) ≤ ε := by
      show Xnorm s (recOf X₀.1) (recOf ((gridWriter s B).qj 1 X₀)) ≤ ε
      rw [Writer.qj_one]
      exact hX
    have hprec : BankPrecise s B τ (0 * ε * (1 / (N : ℝ)) ^ (s + 10)) (exactBank s B τ X₀) J :=
      (exactBank_precise s B τ X₀ J).mono (by simp)
    obtain ⟨h1, -⟩ := hFW N hN B hB (exactBank s B τ X₀) ε hε0 (hεε.trans (min_le_left _ _))
      hstart hprec
    intro j hj
    rw [← bankSource_exactBank]
    exact h1 j hj
  have hball : ∀ j ≤ J, exactSources s B τ X₀ j ∈ ball (0 : XS N s) δG := by
    intro j hj
    rw [mem_ball_zero_iff]
    have h1 : ε ≤ δG / (2 * (C + 1)) := hεε.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h1
    have : C * ε < δG := by nlinarith
    exact (hex j hj).trans_lt this
  have hBN := hBd N B hB.entry_le
  have hF : ContDiffOn ℝ ∞ W.field (ball 0 δG) := hBN.deriv.contDiffOn
  have hqc : ∀ i, ∀ Y ∈ ball (0 : XS N s) δG, ContinuousAt (W.qj i) Y := fun i Y hY =>
    continuous_fst.continuousAt.comp
      ((IteratedDerivBounds.vfJet_contDiffOn hF isOpen_ball i).continuousOn.continuousAt
        (isOpen_ball.mem_nhds hY))
  -- the lattice sources converge to the exact sources
  have hsrc : ∀ j ≤ J, Tendsto (fun M => latSrc s B τ X₀ M j) atTop
      (𝓝 (exactSources s B τ X₀ j)) := by
    intro j
    induction j with
    | zero =>
      intro _
      have h1 := tendsto_roundRec (z := fun _ => X₀.1) tendsto_const_nhds
      have h2 := ((iotaG s).continuous.tendsto _).comp
        (tendsto_roundRec (z := fun _ => upG s X₀.2) tendsto_const_nhds)
      have e : iotaG s (upG s X₀.2) = X₀.2 := (gridWriter (N := N) s B).ι_u X₀.2
      rw [e] at h2
      exact h1.prodMk_nhds h2
    | succ j ih =>
      intro hj
      have he : Tendsto (fun M => W.endpoint (latSrc s B τ X₀ M j) τ) atTop
          (𝓝 (exactSources s B τ X₀ (j + 1))) :=
        (continuousAt_endpoint s B τ fun i => hqc i _ (hball j (by omega))).tendsto.comp
          (ih (by omega))
      have h1 := tendsto_roundRec ((continuous_fst.tendsto _).comp he)
      have h2 := ((iotaG s).continuous.tendsto _).comp
        (tendsto_roundRec (((upG s).continuous.tendsto _).comp ((continuous_snd.tendsto _).comp he)))
      have e : iotaG s (upG s (exactSources s B τ X₀ (j + 1)).2) =
          (exactSources s B τ X₀ (j + 1)).2 := (gridWriter (N := N) s B).ι_u _
      rw [e] at h2
      have := h1.prodMk_nhds h2
      simp only [latSrc_succ]
      exact this
  -- the lattice banks converge to the exact banks
  have hbank : ∀ j ≤ J, ∀ ℓ : Fin 4, Tendsto (fun M => latBank s B τ X₀ M j ℓ) atTop
      (𝓝 (exactBank s B τ X₀ j ℓ)) := by
    intro j hj ℓ
    have hs' := hsrc j hj
    fin_cases ℓ
    · show Tendsto (fun M => (latSrc s B τ X₀ M j).1) atTop (𝓝 (exactSources s B τ X₀ j).1)
      exact (continuous_fst.tendsto _).comp hs'
    · show Tendsto (fun M => (latRegs s B τ X₀ M j).2) atTop
        (𝓝 ((gridWriter s B).qj 1 (exactSources s B τ X₀ j)))
      rw [Writer.qj_one]
      have h := ((upG s).continuous.tendsto _).comp ((continuous_snd.tendsto _).comp hs')
      have e1 : ∀ M, upG s (latSrc s B τ X₀ M j).2 = (latRegs s B τ X₀ M j).2 := fun M =>
        (gridWriter (N := N) s B).u_ι _
      simp only [Function.comp_def, e1] at h
      exact h
    · show Tendsto (fun M => roundRec M (W.qj 2 (latSrc s B τ X₀ M j))) atTop
        (𝓝 (W.qj 2 (exactSources s B τ X₀ j)))
      exact tendsto_roundRec ((hqc 2 _ (hball j hj)).tendsto.comp hs')
    · show Tendsto (fun M => roundRec M (W.qj 3 (latSrc s B τ X₀ M j))) atTop
        (𝓝 (W.qj 3 (exactSources s B τ X₀ j)))
      exact tendsto_roundRec ((hqc 3 _ (hball j hj)).tendsto.comp hs')
  -- the entry functional
  have hent : ∀ {z : ℕ → Upper → GridH N (s + 1)} {z₀ : Upper → GridH N (s + 1)},
      Tendsto z atTop (𝓝 z₀) → ∀ (κ : Upper) (x : Grid N),
        Tendsto (fun M => val (z M κ) x) atTop (𝓝 (val (z₀ κ) x)) := by
    intro z z₀ hz κ x
    set L : (Upper → GridH N (s + 1)) →L[ℝ] ℝ := (ContinuousLinearMap.proj x).comp
      ((PeriodicGridSobolev.GridH.toFunL (N := N) (r := s + 1)).toContinuousLinearMap.comp
        (ContinuousLinearMap.proj κ))
    exact (L.continuous.tendsto z₀).comp hz
  -- the precision errors tend to zero
  have hA : ∀ j < J, ∀ (ℓ : Fin 4) (κ : Upper) (x : Grid N), ∀ᶠ M in atTop,
      τ ^ (ℓ : ℕ) * |val ((latBank s B τ X₀ M j ℓ -
        W.qj ℓ (bankSource s (latBank s B τ X₀ M j))) κ) x| ≤ η := by
    intro j hj ℓ κ x
    have h1 : Tendsto (fun M => latBank s B τ X₀ M j ℓ -
        W.qj ℓ (bankSource s (latBank s B τ X₀ M j))) atTop
        (𝓝 (exactBank s B τ X₀ j ℓ - W.qj ℓ (exactSources s B τ X₀ j))) :=
      (hbank j hj.le ℓ).sub ((hqc ℓ _ (hball j hj.le)).tendsto.comp (hsrc j hj.le))
    have e : exactBank s B τ X₀ j ℓ - W.qj ℓ (exactSources s B τ X₀ j) = 0 := sub_self _
    rw [e] at h1
    have h2 := ((hent h1 κ x).abs.const_mul (τ ^ (ℓ : ℕ)))
    simp only [Pi.zero_apply, val_zero, abs_zero, mul_zero] at h2
    exact (h2.eventually (gt_mem_nhds hη)).mono fun M hM => hM.le
  have hB' : ∀ j < J, ∀ (ℓ : Fin 4) (κ : Upper) (x : Grid N), ∀ᶠ M in atTop,
      τ ^ (ℓ : ℕ) * |val ((latBank s B τ X₀ M (j + 1) ℓ -
        W.qj ℓ (W.endpoint (bankSource s (latBank s B τ X₀ M j)) τ)) κ) x| ≤ η := by
    intro j hj ℓ κ x
    have he : Tendsto (fun M => W.endpoint (latSrc s B τ X₀ M j) τ) atTop
        (𝓝 (exactSources s B τ X₀ (j + 1))) :=
      (continuousAt_endpoint s B τ fun i => hqc i _ (hball j hj.le)).tendsto.comp
        (hsrc j hj.le)
    have h1 : Tendsto (fun M => latBank s B τ X₀ M (j + 1) ℓ -
        W.qj ℓ (W.endpoint (bankSource s (latBank s B τ X₀ M j)) τ)) atTop
        (𝓝 (exactBank s B τ X₀ (j + 1) ℓ - W.qj ℓ (exactSources s B τ X₀ (j + 1)))) :=
      (hbank (j + 1) hj ℓ).sub ((hqc ℓ _ (hball (j + 1) hj)).tendsto.comp he)
    have e : exactBank s B τ X₀ (j + 1) ℓ - W.qj ℓ (exactSources s B τ X₀ (j + 1)) = 0 :=
      sub_self _
    rw [e] at h1
    have h2 := ((hent h1 κ x).abs.const_mul (τ ^ (ℓ : ℕ)))
    simp only [Pi.zero_apply, val_zero, abs_zero, mul_zero] at h2
    exact (h2.eventually (gt_mem_nhds hη)).mono fun M hM => hM.le
  -- the starting record
  have hstart : ∀ᶠ M in atTop, Xnorm s (recOf (latBank s B τ X₀ M 0 0) - recOf X₀.1)
      (recOf (latBank s B τ X₀ M 0 1) - recOf X₀.2) ≤ ζ := by
    have h0 : Tendsto (fun M => latSrc s B τ X₀ M 0 - X₀) atTop (𝓝 0) := by
      have := (hsrc 0 (Nat.zero_le _)).sub_const X₀
      rw [show exactSources s B τ X₀ 0 - X₀ = 0 from sub_self X₀] at this
      exact this
    have h1 : Tendsto (fun M => Real.sqrt (2 * Fintype.card Upper) *
        ‖latSrc s B τ X₀ M 0 - X₀‖) atTop (𝓝 0) := by
      have := (tendsto_norm_zero.comp h0).const_mul (Real.sqrt (2 * Fintype.card Upper))
      simpa using this
    refine (h1.eventually (gt_mem_nhds hζ)).mono fun M hM => ?_
    have h2 := Xnorm_le_norm s (latSrc s B τ X₀ M 0 - X₀)
    exact h2.trans hM.le
  -- all finitely many conditions at once
  have hall : ∀ᶠ M in atTop, (∀ j ∈ Finset.range J, ∀ (ℓ : Fin 4) (κ : Upper) (x : Grid N),
      τ ^ (ℓ : ℕ) * |val ((latBank s B τ X₀ M j ℓ -
        W.qj ℓ (bankSource s (latBank s B τ X₀ M j))) κ) x| ≤ η ∧
      τ ^ (ℓ : ℕ) * |val ((latBank s B τ X₀ M (j + 1) ℓ -
        W.qj ℓ (W.endpoint (bankSource s (latBank s B τ X₀ M j)) τ)) κ) x| ≤ η) ∧
      Xnorm s (recOf (latBank s B τ X₀ M 0 0) - recOf X₀.1)
        (recOf (latBank s B τ X₀ M 0 1) - recOf X₀.2) ≤ ζ := by
    refine Filter.Eventually.and ?_ hstart
    refine (Filter.eventually_all_finset _).2 fun j hj => ?_
    have hj' : j < J := Finset.mem_range.mp hj
    refine Filter.eventually_all.2 fun ℓ => Filter.eventually_all.2 fun κ =>
      Filter.eventually_all.2 fun x => ?_
    exact (hA j hj' ℓ κ x).and (hB' j hj' ℓ κ x)
  obtain ⟨M, hM1, hM2⟩ := hall.exists
  exact ⟨M, latBank_mem_lattice s B τ X₀ M, fun j hj ℓ κ x => hM1 j (Finset.mem_range.mpr hj) ℓ κ x,
    hM2⟩

/-! ### Fixed execution radius of a stage -/

/-- Restriction of a ten-component record to a set of sites (zero outside). -/
def restrQ {r : ℕ} (S : Set (Grid N)) : (Upper → GridH N r) →ₗ[ℝ] (Upper → GridH N r) where
  toFun a := fun κ => PeriodicGridSobolev.GridH.mk (S.indicator (val (a κ)))
  map_add' a b := funext fun κ => PeriodicGridSobolev.GridH.ext fun x => by
    show S.indicator (val (a κ) + val (b κ)) x = S.indicator (val (a κ)) x + S.indicator (val (b κ)) x
    by_cases hx : x ∈ S
    · simp only [Set.indicator_of_mem hx]; rfl
    · simp only [Set.indicator_of_notMem hx]; simp
  map_smul' c a := funext fun κ => PeriodicGridSobolev.GridH.ext fun x => by
    show S.indicator (c • val (a κ)) x = c * S.indicator (val (a κ)) x
    by_cases hx : x ∈ S
    · simp only [Set.indicator_of_mem hx]; rfl
    · simp only [Set.indicator_of_notMem hx]; simp

theorem restrQ_apply {r : ℕ} (S : Set (Grid N)) (a : Upper → GridH N r) (κ : Upper) (y : Grid N) :
    val (restrQ S a κ) y = S.indicator (val (a κ)) y := rfl

/-- Two records agree on `S` iff their restrictions to `S` coincide. -/
theorem restrQ_eq_iff {r : ℕ} {S : Set (Grid N)} {a b : Upper → GridH N r} :
    restrQ S a = restrQ S b ↔ ∀ y ∈ S, ∀ κ, val (a κ) y = val (b κ) y := by
  constructor
  · intro h y hy κ
    have := congrArg (fun z : Upper → GridH N r => val (z κ) y) h
    simpa only [restrQ_apply, Set.indicator_of_mem hy] using this
  · intro h
    refine funext fun κ => PeriodicGridSobolev.GridH.ext fun y => ?_
    rw [restrQ_apply, restrQ_apply]
    by_cases hy : y ∈ S
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]; exact h y hy κ
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]

theorem restrQ_mono {r : ℕ} {S S' : Set (Grid N)} (hS : S' ⊆ S) {a b : Upper → GridH N r}
    (h : restrQ S a = restrQ S b) : restrQ S' a = restrQ S' b :=
  restrQ_eq_iff.2 fun y hy κ => restrQ_eq_iff.1 h y (hS hy) κ

omit [NeZero N] in
theorem map_polyCurveDeriv' {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →ₗ[ℝ] F) {n : ℕ} (k : ℕ) (c : Fin n → E)
    (t : ℝ) : L (polyCurveDeriv k c t) = polyCurveDeriv k (fun i => L (c i)) t := by
  simp only [polyCurveDeriv, map_sum, map_smul]

omit [NeZero N] in
theorem map_hermiteCorrection {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →ₗ[ℝ] F) (τ : ℝ) (a b : E) (i : Fin 8) :
    L (hermiteCorrection τ a b i) = hermiteCorrection τ (L a) (L b) i := by
  fin_cases i <;>
    simp [hermiteCorrection, scaleCoeffs, hermiteCorrUnit, map_add, map_sub, map_smul]

/-- **Fixed execution radius of one stage** (`lem:supp-open-local-jets` locality, propagated
through the Taylor–Hermite construction).  On the common chart, the stage polynomial `Q_X` on the
box of radius `ρ` around a site, and the successor value, velocity, acceleration and jerk caches
`J_ℓ(X₁)`, `ℓ ≤ 3`, there, depend only on the source `X` on the box of radius `ρ + 20`: a radius
fixed by the number of local jet compositions and endpoint evaluations, independent of the mesh,
of the number of sites and of the number of stages. -/
theorem stage_local (s : ℕ) (hs : 2 ≤ s) (b : ℝ) :
    ∃ δ > 0, ∀ (N : ℕ) [NeZero N] (B : Upper → Upper → ℝ), (∀ k l, |B k l| ≤ b) →
      ∀ (τ : ℝ) (x : Grid N) (ρ : ℕ) (X X' : XS N s), X ∈ ball 0 δ → X' ∈ ball 0 δ →
      (gridWriter s B).endpoint X τ ∈ ball 0 δ → (gridWriter s B).endpoint X' τ ∈ ball 0 δ →
      AgreeOn s (box x (ρ + 20)) X X' →
      (∀ i, restrQ (box x ρ) ((gridWriter s B).hermiteC X τ i) =
        restrQ (box x ρ) ((gridWriter s B).hermiteC X' τ i)) ∧
      ∀ ℓ ≤ 3, restrQ (box x ρ) ((gridWriter s B).qj ℓ ((gridWriter s B).endpoint X τ)) =
        restrQ (box x ρ) ((gridWriter s B).qj ℓ ((gridWriter s B).endpoint X' τ)) := by
  obtain ⟨δ, hδ, A, hA, hBd⟩ := gridWriter_bounds s hs b
  refine ⟨δ, hδ, fun N _ B hB τ x ρ X X' hX hX' hE hE' h => ?_⟩
  set W := gridWriter (N := N) s B
  have hF : ContDiffOn ℝ ∞ (lawField (N := N) s B) (ball 0 δ) := (hBd N B hB).deriv.contDiffOn
  have agree_mono : ∀ {S S' : Set (Grid N)} {Y Y' : XS N s}, S' ⊆ S → AgreeOn s S Y Y' →
      AgreeOn s S' Y Y' := fun hS hY y hy => hY y (hS hy)
  -- the source jets on the box of radius `ρ + 6`
  have hJ : ∀ i ≤ 7, restrQ (box x (ρ + 6)) (W.qj i X) = restrQ (box x (ρ + 6)) (W.qj i X') := by
    intro i hi
    refine restrQ_eq_iff.2 fun y hy κ => ?_
    exact (jets_local s isOpen_ball hF x i (ρ + 6) hX hX'
      (agree_mono (box_mono (by omega)) h) y hy κ).1
  have hT : ∀ i : Fin 8, restrQ (box x (ρ + 6)) (W.taylorC X i) =
      restrQ (box x (ρ + 6)) (W.taylorC X' i) := by
    intro i
    simp only [Writer.taylorC, map_smul]
    rw [hJ i (by omega)]
  have hTc : (fun i => restrQ (box x (ρ + 6)) (W.taylorC X i)) =
      fun i => restrQ (box x (ρ + 6)) (W.taylorC X' i) := funext hT
  have hP : ∀ k, restrQ (box x (ρ + 6)) (polyCurveDeriv k (W.taylorC X) τ) =
      restrQ (box x (ρ + 6)) (polyCurveDeriv k (W.taylorC X') τ) := by
    intro k
    rw [map_polyCurveDeriv', map_polyCurveDeriv', hTc]
  -- the successor agrees on the box of radius `ρ + 6`
  have hEnd : AgreeOn s (box x (ρ + 6)) (W.endpoint X τ) (W.endpoint X' τ) := by
    intro y hy κ
    have h0 := restrQ_eq_iff.1 (hP 0) y hy κ
    have h1 := restrQ_eq_iff.1 (hP 1) y hy κ
    simp only [polyCurveDeriv_zero] at h0
    exact ⟨h0, h1⟩
  have hJ1 : ∀ ℓ ≤ 3, restrQ (box x ρ) (W.qj ℓ (W.endpoint X τ)) =
      restrQ (box x ρ) (W.qj ℓ (W.endpoint X' τ)) := by
    intro ℓ hℓ
    refine restrQ_eq_iff.2 fun y hy κ => ?_
    exact (jets_local s isOpen_ball hF x ℓ ρ hE hE'
      (agree_mono (box_mono (by omega)) hEnd) y hy κ).1
  refine ⟨fun i => ?_, hJ1⟩
  have hP' : ∀ k, restrQ (box x ρ) (polyCurveDeriv k (W.taylorC X) τ) =
      restrQ (box x ρ) (polyCurveDeriv k (W.taylorC X') τ) := fun k =>
    restrQ_mono (box_mono (by omega)) (hP k)
  have h2 : restrQ (box x ρ) (W.corr2 X τ) = restrQ (box x ρ) (W.corr2 X' τ) := by
    simp only [Writer.corr2, map_sub]
    rw [hJ1 2 (by norm_num), hP' 2]
  have h3 : restrQ (box x ρ) (W.corr3 X τ) = restrQ (box x ρ) (W.corr3 X' τ) := by
    simp only [Writer.corr3, map_sub]
    rw [hJ1 3 (by norm_num), hP' 3]
  simp only [Writer.hermiteC, Pi.add_apply, map_add]
  rw [map_hermiteCorrection, map_hermiteCorrection, h2, h3,
    restrQ_mono (box_mono (by omega)) (hT i)]

/-! ### The strict residual margin -/

/-- **The strict residual margin supplied by the finite construction** (proof of
`thm:supp-open-finite-words`, used in `thm:main-open-law-basin` (L3)): for every fixed `M > 0`,
on a sufficiently fine tail every stage cost of every bank word obeying the precision convention
is strictly below `M τ_j h⁴` (`eq:main-law-row-moment` for the letter), and the stopped cost is at
most `h²`. -/
theorem finite_words_strict_margin (s : ℕ) (hs : 5 ≤ s) (T : ℝ) (hT : 0 < T) (cη : ℝ)
    (hcη : 0 ≤ cη) (Mrow : ℝ) (hM : 0 < Mrow) :
    ∃ ε₀ > 0, ∃ N₀ : ℕ, ∀ (N : ℕ) [NeZero N], N₀ ≤ N →
      ∀ (B : Upper → Upper → ℝ), IsMark (1 / 48) B →
      ∀ (β : ℕ → Fin 4 → Upper → GridH N (s + 1)) (ε : ℝ), 0 ≤ ε → ε ≤ ε₀ →
      Xnorm s (recOf (β 0 0)) (recOf (β 0 1)) ≤ ε →
      BankPrecise s B (stepOf N T) (cη * ε * (1 / (N : ℝ)) ^ (s + 10)) β (numCells N T) →
      (∀ j < numCells N T, (ε ^ 2)⁻¹ * ∫ t in ((j : ℝ) * stepOf N T)..(((j + 1 : ℕ) : ℝ) *
          stepOf N T), (bankWord s T β).costDensity B s t <
        Mrow * stepOf N T * (1 / (N : ℝ)) ^ 4) ∧
      (∀ ρ, (bankWord s T β).cost B s ρ ε T ≤ (1 / (N : ℝ)) ^ 2) := by
  obtain ⟨ε₀, hε₀, N₀, C, hC, hFW⟩ := finite_words_bounds s hs T hT cη hcη
  set a : ℝ := 4 * C / Mrow + 2 * C * T
  have ha : 0 ≤ a := by positivity
  obtain ⟨N₁, hN₁⟩ := exists_nat_ge (a + 1)
  refine ⟨ε₀, hε₀, max N₀ N₁, fun N _ hN B hB β ε hε0 hεε hX hprec => ?_⟩
  obtain ⟨-, -, hstage, hcost⟩ := hFW N ((le_max_left _ _).trans hN) B hB β ε hε0 hεε hX hprec
  set h : ℝ := 1 / (N : ℝ) with hhdef
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hh0 : 0 < h := by positivity
  have hh1 : h ≤ 1 := by rw [hhdef, div_le_one (by linarith)]; exact hN1
  have hah : a * h ≤ 1 := by
    have h2 : (a + 1 : ℝ) ≤ N := hN₁.trans (by exact_mod_cast (le_max_right _ _).trans hN)
    refine mul_le_one_of_le_one_div ha hh0.le ?_
    rw [hhdef]
    exact one_div_le_one_div_of_le (by positivity) h2
  have hτ := stepOf_pos (N := N) hT
  have h10 : h ^ 10 ≤ h ^ 6 := pow_le_pow_of_le_one hh0.le hh1 (by norm_num)
  have hh2 : h ^ 2 ≤ h := by
    calc h ^ 2 ≤ h ^ 1 := pow_le_pow_of_le_one hh0.le hh1 (by norm_num)
      _ = h := pow_one h
  have hh4 : h ^ 4 ≤ h := by
    calc h ^ 4 ≤ h ^ 1 := pow_le_pow_of_le_one hh0.le hh1 (by norm_num)
      _ = h := pow_one h
  refine ⟨fun j hj => (hstage j hj).trans_lt ?_, fun ρ => (hcost ρ).trans ?_⟩
  · -- `C τ (h¹⁰ + h⁶) ≤ 2 C τ h² h⁴ < M τ h⁴`
    have h4 : 4 * C * h ≤ Mrow := by
      have h1 : 4 * C / Mrow * h ≤ 1 := by
        have : 4 * C / Mrow ≤ a := by have : 0 ≤ 2 * C * T := by positivity
                                      simp only [a]; linarith
        exact (mul_le_mul_of_nonneg_right this hh0.le).trans hah
      rw [div_mul_eq_mul_div, div_le_one hM] at h1
      linarith
    have h2 : 2 * C * h ^ 2 < Mrow := by
      have h5 : 2 * C * h ^ 2 ≤ 2 * C * h := by gcongr
      linarith
    have hpos : 0 < stepOf N T * h ^ 4 := by positivity
    calc C * stepOf N T * (h ^ 10 + h ^ 6) ≤ C * stepOf N T * (2 * h ^ 6) := by gcongr; linarith
      _ = (2 * C * h ^ 2) * (stepOf N T * h ^ 4) := by ring
      _ < Mrow * (stepOf N T * h ^ 4) := mul_lt_mul_of_pos_right h2 hpos
      _ = Mrow * stepOf N T * h ^ 4 := by ring
  · -- `C T (h¹⁰ + h⁶) ≤ 2 C T h⁴ h² ≤ h²`
    have h1 : 2 * C * T * h ≤ 1 := by
      have : 2 * C * T ≤ a := by have : 0 ≤ 4 * C / Mrow := by positivity
                                 simp only [a]; linarith
      exact (mul_le_mul_of_nonneg_right this hh0.le).trans hah
    calc C * T * (h ^ 10 + h ^ 6) ≤ C * T * (2 * h ^ 6) := by gcongr; linarith
      _ = (2 * C * T * h ^ 4) * h ^ 2 := by ring
      _ ≤ (2 * C * T * h) * h ^ 2 := by gcongr
      _ ≤ 1 * h ^ 2 := by gcongr
      _ = h ^ 2 := one_mul _

end Grid

end

end RenewalGeometry.OpenWriterFiniteWords
