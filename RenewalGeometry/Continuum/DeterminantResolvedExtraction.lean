/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.FiniteWilsonZeroDefect
import RenewalGeometry.GaugeTheory.DeterminantCombinedConnection

/-!
# The Wilson/Coulomb extraction with a convergent, non-small central background
  (`cor:determinant-resolved-closure`, extraction step; Einstein–SM action closure)

`FiniteWilsonZeroDefect.wilson_coulomb_extraction` needs `‖A_h‖_{4,h} ≤ ε_*` for the **whole**
logarithmic connection.  In `cor:determinant-resolved-closure` the normalized connection has the
form `A_h = b_h + a_h Z` (`eq:determinant-combined-connection`): `Z` is central, `a_h` is a real
potential whose raw reconstructions converge strongly in `L⁴` with strongly convergent first
differences (the determinant normalization), and only `b_h` is controlled ("only `b_h` needs to
lie in the small critical ball").  This file reruns the extraction in that situation; the
background `a_h Z` enters only as a bounded source:

* the adjoint links do not see the central part, `Ad e^{h(b + aZ)} = Ad e^{hb}`
  (`ad_combined`), and the Higgs links are displaced by at most `2h‖ρ_H‖(‖b‖ + ‖Z‖|a|)`
  (`norm_exp_apply_sub_le_of_iso`, no smallness needed for isometric links), so both literal
  packets are precompact by `thm:native-Wilson-compactness` under a bounded `L²_h` norm of the
  full connection;
* eventually `h ‖a_h‖_∞ → 0` (`NativeCriticalGrid.tendsto_meshSup`), so the curvature split
  `F_h(b + aZ) = F_h(b) + f_h Z` (`DeterminantCombined.fieldStrength_combined`) holds on the
  chart, and `R_h^0 F_h(b) → F - (G^a - (G^a)ᵀ) Z` strongly in `L²`;
* the semisimple part is then handled by an abstract compactness hypothesis on `b`
  (`BCompact`): it is supplied by `thm:native-discrete-Coulomb` when `b_h` is small and
  co-closed (`bCompact_of_coulomb`) and by `lem:flat-semisimple-normalization` when `b_h` is a
  bounded family of constant commuting links (`bCompact_of_const`);
* the limit connection is `A = B + a₀ Z`, `G = G^b + G^a Z`, and `F = F_A` exactly
  (`recCurv_combined`: no mixed commutator).

Main results: `combined_extraction_core`, `combined_criterion_core` (the complete conclusions of
`FiniteWilsonZeroDefect.finite_wilson_criterion` for the combined connection), and the two
instances `combined_criterion_coulomb`, `combined_criterion_const`.

Rendering as in `FiniteWilsonZeroDefect`: unit torus, mesh `h = 1/N`.
-/

open MeasureTheory Set Finset Filter Topology Metric NormedSpace
open scoped BigOperators ENNReal NNReal RealInnerProductSpace

namespace RenewalGeometry.DeterminantResolved

noncomputable section

set_option linter.unusedSectionVars false

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance : (volume : Measure UnitAddCircle).IsAddHaarMeasure :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

/-- The unit torus `𝕋⁴`. -/
local notation "𝕋" => UnitAddTorus (Fin 4)

open TorusPiecewiseConstantTranslation KolmogorovRieszTorus FiniteWilsonZeroDefect
open NativeGravityFirstJet (M4 asM4 coframeM liftL)

local instance fact_one_le_two_dr : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
local instance fact_one_le_four_dr : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩

/-! ### Isometric links without smallness -/

section Iso

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]

/-- `‖e^Z X e^{-Z} - X‖ ≤ 6 ‖Z‖ ‖X‖` for an isometric adjoint link, **without smallness**
(for `‖Z‖ > 1/2` the left side is at most `2‖X‖`). -/
theorem norm_ad_sub_le_of_iso {Z : 𝔄} (hZ : ∀ X : 𝔄, ‖exp Z * X * exp (-Z)‖ = ‖X‖) (X : 𝔄) :
    ‖exp Z * X * exp (-Z) - X‖ ≤ 6 * ‖Z‖ * ‖X‖ := by
  by_cases h : ‖Z‖ ≤ 1 / 2
  · exact norm_ad_sub_le h X
  · replace h := not_le.1 h
    calc ‖exp Z * X * exp (-Z) - X‖ ≤ ‖exp Z * X * exp (-Z)‖ + ‖X‖ := norm_sub_le _ _
      _ = 2 * ‖X‖ := by rw [hZ]; ring
      _ ≤ 6 * ‖Z‖ * ‖X‖ := by nlinarith [norm_nonneg X]

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [Nontrivial G] [CompleteSpace G]

/-- `‖e^Z v - v‖ ≤ 2 ‖Z‖ ‖v‖` for an isometric link `e^Z`, **without smallness**. -/
theorem norm_exp_apply_sub_le_of_iso {Z : G →L[ℝ] G} (hZ : ∀ v, ‖exp Z v‖ = ‖v‖) (v : G) :
    ‖expIso Z hZ v - v‖ ≤ 2 * ‖Z‖ * ‖v‖ := by
  by_cases h : ‖Z‖ ≤ 1
  · exact norm_expIso_sub_le hZ h v
  · replace h := not_le.1 h
    change ‖exp Z v - v‖ ≤ _
    calc ‖exp Z v - v‖ ≤ ‖exp Z v‖ + ‖v‖ := norm_sub_le _ _
      _ = 2 * ‖v‖ := by rw [hZ]; ring
      _ ≤ 2 * ‖Z‖ * ‖v‖ := by nlinarith [norm_nonneg v]

/-- **The adjoint links do not see a central background**: for `Z` central,
`Ad e^{s(b + aZ)} = Ad e^{sb}`. -/
theorem ad_combined (s a : ℝ) {b Z : 𝔄} (hZ : ∀ X : 𝔄, Commute X Z) (X : 𝔄) :
    exp (s • (b + a • Z)) * X * exp (-(s • (b + a • Z))) = exp (s • b) * X * exp (-(s • b)) := by
  rw [DeterminantCombined.exp_combined s a (hZ b), DeterminantCombined.exp_neg_combined s a (hZ b)]
  set E := exp (s • b)
  set F := exp (-(s • b))
  set C := exp ((s * a) • Z)
  set C' := exp (-((s * a) • Z))
  have hcY : ∀ Y, Commute C Y := fun Y => ((hZ Y).symm.smul_left (s * a)).exp_left
  have h1 : C * C' = 1 := FiniteWilsonZeroDefect.exp_mul_exp_neg' _
  calc E * C * X * (F * C') = E * X * (C * F) * C' := by
        rw [show E * C * X * (F * C') = E * (C * X) * F * C' by noncomm_ring, (hcY X).eq]
        noncomm_ring
    _ = E * X * (F * C) * C' := by rw [(hcY F).eq]
    _ = E * X * F * (C * C') := by noncomm_ring
    _ = E * X * F := by rw [h1, mul_one]

end Iso

/-! ### The curvature split on the chart -/

section Chart

open ShiftedJetAction (Grid unitVec fwdDiff)
open LogBCH (expProd normSum)
open NativeYMIdentification (slots)

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]

/-- On a list with `Σ ‖Xᵢ‖ ≤ 1/128`, `‖e^{X₁} ⋯ e^{X_m} - 1‖ ≤ 1/64`. -/
theorem norm_expProd_sub_one_le_small (L : List 𝔄) (hs : normSum L ≤ 1 / 128) :
    ‖expProd L - 1‖ ≤ 1 / 64 := by
  set s := normSum L
  have hs0 : 0 ≤ s := LogBCH.normSum_nonneg L
  have h1 := LogBCH.norm_expProd_sub_le L
  have h2 := LogBCH.norm_sum_le_normSum L
  have h3 := LogBCH.norm_secondOrder_le L
  have he : Real.exp s ≤ 3 := by
    have : Real.exp s ≤ Real.exp 1 := Real.exp_le_exp.2 (by linarith)
    linarith [Real.exp_one_lt_d9]
  have e : expProd L - 1 = (expProd L - (1 + L.sum + LogBCH.secondOrder L)) + L.sum +
      LogBCH.secondOrder L := by abel
  rw [e]
  calc ‖(expProd L - (1 + L.sum + LogBCH.secondOrder L)) + L.sum + LogBCH.secondOrder L‖
      ≤ ‖expProd L - (1 + L.sum + LogBCH.secondOrder L)‖ + ‖L.sum‖ +
          ‖LogBCH.secondOrder L‖ := norm_add₃_le
    _ ≤ s ^ 3 * Real.exp s + s + s ^ 2 / 2 := by gcongr
    _ ≤ s ^ 3 * 3 + s + s ^ 2 / 2 := by gcongr
    _ ≤ 1 / 64 := by nlinarith

variable {N : ℕ} [NeZero N]

/-- The plaquette of a mesh-small connection is close to `1`. -/
theorem norm_gaugePlaquette_sub_one_le (b : Fin 4 → Grid N → 𝔄)
    (hb : ∀ μ x, (N : ℝ)⁻¹ * ‖b μ x‖ ≤ 1 / 512) (x : Grid N) (μ ν : Fin 4) :
    ‖NativeScaling.gaugePlaquette (N : ℝ)⁻¹ b x μ ν - 1‖ ≤ 1 / 64 := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  rw [NativeYMBridge.gaugePlaquette_eq_expProd]
  refine norm_expProd_sub_one_le_small _ ?_
  rw [NativeYMIdentification.normSum_map_smul, abs_of_pos (inv_pos.2 hN),
    NativeYMIdentification.normSum_slots]
  simp only [NativeYMBridge.arr]
  have h1 := hb μ x
  have h2 := hb ν (x + Pi.single μ 1)
  have h3 := hb μ (x + Pi.single ν 1)
  have h4 := hb ν x
  nlinarith

/-- The Abelian plaquette angle `h² f = h (a_ν(x+μ) - a_ν(x) - a_μ(x+ν) + a_μ(x))`. -/
theorem sq_mul_abelCurv (a : Fin 4 → Grid N → ℝ) (x : Grid N) (μ ν : Fin 4) :
    ((N : ℝ)⁻¹) ^ 2 * DeterminantCombined.abelCurv (N : ℝ)⁻¹ a x μ ν =
      (N : ℝ)⁻¹ * (a ν (x + unitVec N μ) - a ν x - a μ (x + unitVec N ν) + a μ x) := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  simp only [DeterminantCombined.abelCurv, ShiftedJetAction.fwdDiff, smul_eq_mul, inv_inv]
  field_simp
  ring

theorem abs_sq_mul_abelCurv_le (a : Fin 4 → Grid N → ℝ) {δ : ℝ}
    (ha : ∀ μ x, (N : ℝ)⁻¹ * |a μ x| ≤ δ) (x : Grid N) (μ ν : Fin 4) :
    |((N : ℝ)⁻¹) ^ 2 * DeterminantCombined.abelCurv (N : ℝ)⁻¹ a x μ ν| ≤ 4 * δ := by
  rw [sq_mul_abelCurv]
  have hN : (0 : ℝ) < (N : ℝ)⁻¹ := inv_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N))
  rw [abs_mul, abs_of_pos hN]
  have h1 := ha ν (x + unitVec N μ)
  have h2 := ha ν x
  have h3 := ha μ (x + unitVec N ν)
  have h4 := ha μ x
  have t : |a ν (x + unitVec N μ) - a ν x - a μ (x + unitVec N ν) + a μ x| ≤
      |a ν (x + unitVec N μ)| + |a ν x| + |a μ (x + unitVec N ν)| + |a μ x| := by
    have := abs_add_le (a ν (x + unitVec N μ) - a ν x - a μ (x + unitVec N ν)) (a μ x)
    have := abs_sub (a ν (x + unitVec N μ) - a ν x) (a μ (x + unitVec N ν))
    have := abs_sub (a ν (x + unitVec N μ)) (a ν x)
    linarith
  calc (N : ℝ)⁻¹ * |a ν (x + unitVec N μ) - a ν x - a μ (x + unitVec N ν) + a μ x|
      ≤ (N : ℝ)⁻¹ * (|a ν (x + unitVec N μ)| + |a ν x| + |a μ (x + unitVec N ν)| + |a μ x|) :=
        mul_le_mul_of_nonneg_left t hN.le
    _ ≤ 4 * δ := by nlinarith

/-- **The curvature split on the chart**: if `h‖b‖ ≤ 1/512` and `h|a|‖Z‖ ≤ 1/512` pointwise,
`F_h(b + aZ) = F_h(b) + f Z` for central `Z`. -/
theorem fieldStrength_combined_of_small (b : Fin 4 → Grid N → 𝔄) {Z : 𝔄}
    (hZ : ∀ X : 𝔄, Commute X Z) (a : Fin 4 → Grid N → ℝ)
    (hb : ∀ μ x, (N : ℝ)⁻¹ * ‖b μ x‖ ≤ 1 / 512)
    (ha : ∀ μ x, (N : ℝ)⁻¹ * |a μ x| * ‖Z‖ ≤ 1 / 512) (x : Grid N) (μ ν : Fin 4) :
    NativeScaling.fieldStrength (N : ℝ)⁻¹ (DeterminantCombined.combined b Z a) x μ ν =
      NativeScaling.fieldStrength (N : ℝ)⁻¹ b x μ ν +
        DeterminantCombined.abelCurv (N : ℝ)⁻¹ a x μ ν • Z := by
  have hN : (N : ℝ)⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast NeZero.ne N)
  set P := NativeScaling.gaugePlaquette (N : ℝ)⁻¹ b x μ ν
  set t := ((N : ℝ)⁻¹) ^ 2 * DeterminantCombined.abelCurv (N : ℝ)⁻¹ a x μ ν
  have hP : ‖P - 1‖ ≤ 1 / 64 := norm_gaugePlaquette_sub_one_le b hb x μ ν
  have hW : ‖t • Z‖ ≤ 1 / 128 := by
    rw [norm_smul, Real.norm_eq_abs]
    rcases eq_or_ne ‖Z‖ 0 with hz | hz
    · rw [hz, mul_zero]; norm_num
    · have hz' : 0 < ‖Z‖ := lt_of_le_of_ne (norm_nonneg Z) (Ne.symm hz)
      have ha' : ∀ μ x, (N : ℝ)⁻¹ * |a μ x| ≤ 1 / 512 / ‖Z‖ := fun μ x => by
        rw [le_div_iff₀ hz']; exact ha μ x
      have := abs_sq_mul_abelCurv_le a ha' x μ ν
      calc |t| * ‖Z‖ ≤ 4 * (1 / 512 / ‖Z‖) * ‖Z‖ := mul_le_mul_of_nonneg_right this hz'.le
        _ = 1 / 128 := by field_simp; norm_num
  have hlog : ‖SeriesLogChart.logChart P‖ ≤ 1 / 32 :=
    (SeriesLogChart.norm_logChart_le (hP.trans (by norm_num))).trans (by linarith)
  have hW1 : ‖t • Z‖ ≤ 1 := hW.trans (by norm_num)
  have hE1 := SeriesLogChart.norm_exp_sub_one_le hW1
  have hE2 := SeriesLogChart.norm_exp_le_one_add hW1
  refine DeterminantCombined.fieldStrength_combined hN b (fun μ x => hZ (b μ x)) a x μ ν
    (hP.trans_lt (by norm_num)) ?_ ?_
  · calc ‖SeriesLogChart.logChart P + t • Z‖ ≤ ‖SeriesLogChart.logChart P‖ + ‖t • Z‖ :=
          norm_add_le _ _
      _ ≤ 1 / 8 := by linarith
  · rw [DeterminantCombined.gaugePlaquette_combined hN b (fun μ x => hZ (b μ x)) a x μ ν]
    have e : P * exp (t • Z) - 1 = (P - 1) * exp (t • Z) + (exp (t • Z) - 1) := by noncomm_ring
    rw [e]
    calc ‖(P - 1) * exp (t • Z) + (exp (t • Z) - 1)‖
        ≤ ‖P - 1‖ * ‖exp (t • Z)‖ + ‖exp (t • Z) - 1‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) le_rfl)
      _ ≤ 1 / 64 * (1 + 2 * ‖t • Z‖) + 2 * ‖t • Z‖ := by
          gcongr
      _ ≤ 1 / 16 := by nlinarith [norm_nonneg (t • Z)]

end Chart

/-! ### Generic lemmas for the extraction -/

section Lemmas

variable {X : Type*} [MeasurableSpace X] {ν : Measure X}
variable {E : Type*} [NormedAddCommGroup E]

/-- Strong convergence is insensitive to finitely many terms. -/
theorem lpTendsto_of_eventually_eq {p : ℝ≥0∞} {u v : ℕ → X → E} {u' : X → E}
    (hu : LpTendsto ν p u u') (hv : ∀ k, MemLp (v k) p ν) (h : ∀ᶠ k in atTop, u k = v k) :
    LpTendsto ν p v u' :=
  ⟨hv, hu.memLp_lim, hu.tendsto.congr' (h.mono fun k hk => by rw [hk])⟩

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄]

/-- **No mixed commutator in the limit**: for `Z` central,
`[X + sZ, Y + tZ] = [X, Y]`. -/
theorem commutator_add_central {Z : 𝔄} (hZ : ∀ X : 𝔄, Commute X Z) (X Y : 𝔄) (s t : ℝ) :
    (X + s • Z) * (Y + t • Z) - (Y + t • Z) * (X + s • Z) = X * Y - Y * X := by
  have h1 : Z * Y = Y * Z := (hZ Y).eq.symm
  have h2 : Z * X = X * Z := (hZ X).eq.symm
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, h1, h2, smul_add, smul_smul]
  rw [mul_comm s t]
  abel

/-- The complete curvature of `A = B + a₀ Z` is that of `B` plus `(G^a_{μν} - G^a_{νμ}) Z`. -/
theorem recCurv_combined {Z : 𝔄} (hZ : ∀ X : 𝔄, Commute X Z) (B : Fin 4 → 𝕋 → 𝔄)
    (Gb : Fin 4 → Fin 4 → 𝕋 → 𝔄) (a₀ : Fin 4 → 𝕋 → ℝ) (Ga : Fin 4 → Fin 4 → 𝕋 → ℝ)
    (μ ν : Fin 4) (z : 𝕋) :
    NativeReconstructed.recCurv (fun μ z => B μ z + a₀ μ z • Z)
        (fun μ ν z => Gb μ ν z + Ga μ ν z • Z) μ ν z =
      NativeReconstructed.recCurv B Gb μ ν z + (Ga μ ν z - Ga ν μ z) • Z := by
  simp only [NativeReconstructed.recCurv]
  rw [commutator_add_central hZ, sub_smul]
  abel

end Lemmas

/-! ### The extraction with a central background -/

section Core

open NativeDensity NativeBank
open ShiftedJetAction (Grid)
open NativeDiracConv (CoHyp qM ωM)
open NativeScaling (Mat)

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℂ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
  [FiniteDimensional ℝ 𝔄]
variable {rH : ℕ} [NeZero rH]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
  [FiniteDimensional ℝ 𝓢]
variable {J : ℕ}

/-- **The compactness property of the semisimple part** `b_h`: along every subsequence on which
the literal curvatures `R_h^0 F_h(b_h)` converge strongly in `L²` to `F^b`, a further subsequence
has `R_h^0 b_h → B` strongly in `L⁴`, `R_h^0 D⁺_μ b_{h,ν} → G^b_{μν}` strongly in `L²`, and
`F^b = F_B` (`F^b_{μν} = G^b_{μν} - G^b_{νμ} + [B_μ, B_ν]`).  Supplied by
`thm:native-discrete-Coulomb` for small co-closed `b_h` (`bCompact_of_coulomb`) and by bounded
constant commuting links (`bCompact_of_const`, `lem:flat-semisimple-normalization`). -/
def BCompact (n : ℕ → ℕ) [∀ k, NeZero (n k)] (b : ∀ k, Fin 4 → Grid (n k) → 𝔄) : Prop :=
  ∀ ψ : ℕ → ℕ, StrictMono ψ → ∀ Fb : Fin 4 → Fin 4 → 𝕋 → 𝔄,
    (∀ μ ν, LpTendsto volume 2 (fun k => pc (fun x =>
      NativeScaling.fieldStrength (n (ψ k) : ℝ)⁻¹ (b (ψ k)) x μ ν)) (Fb μ ν)) →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ (B : Fin 4 → 𝕋 → 𝔄) (Gb : Fin 4 → Fin 4 → 𝕋 → 𝔄),
      (∀ μ, LpTendsto volume 4 (fun k => pc (b (ψ (φ k)) μ)) (B μ)) ∧
      (∀ μ ν, LpTendsto volume 2 (fun k => pc (NativeHiggs.DpV μ (b (ψ (φ k)) ν))) (Gb μ ν)) ∧
      (∀ μ ν, Fb μ ν =ᵐ[MeasureTheory.volume] NativeReconstructed.recCurv B Gb μ ν)

/-- `BCompact` passes to subsequences. -/
theorem BCompact.comp {n : ℕ → ℕ} [∀ k, NeZero (n k)] {b : ∀ k, Fin 4 → Grid (n k) → 𝔄}
    (h : BCompact n b) {φ₀ : ℕ → ℕ} (hφ₀ : StrictMono φ₀) :
    BCompact (fun k => n (φ₀ k)) (fun k => b (φ₀ k)) :=
  fun ψ hψ Fb hFb => h (fun k => φ₀ (ψ k)) (hφ₀.comp hψ) Fb hFb

omit [NormOneClass 𝔄] [FiniteDimensional ℝ 𝔄] in
theorem DpV_combined {N : ℕ} [NeZero N] (b : Grid N → 𝔄) (a : Grid N → ℝ) (Z : 𝔄) (μ : Fin 4)
    (x : Grid N) :
    NativeHiggs.DpV μ (fun x => b x + a x • Z) x =
      NativeHiggs.DpV μ b x + NativeHiggs.DpV μ a x • Z := by
  simp only [NativeHiggs.DpV, smul_eq_mul]
  module

omit [FiniteDimensional ℝ 𝔄] in
theorem abelCurv_eq_DpV {N : ℕ} [NeZero N] (a : Fin 4 → Grid N → ℝ) (x : Grid N) (μ ν : Fin 4) :
    DeterminantCombined.abelCurv (N : ℝ)⁻¹ a x μ ν =
      NativeHiggs.DpV μ (a ν) x - NativeHiggs.DpV ν (a μ) x := by
  simp only [DeterminantCombined.abelCurv, ShiftedJetAction.fwdDiff, NativeHiggs.DpV, inv_inv,
    ShiftedJetAction.unitVec]

set_option maxHeartbeats 3200000 in
-- six successive extractions with the central background
/-- **The Wilson/Coulomb extraction with a central background** (`cor:determinant-resolved-closure`,
extraction step; unit-torus rendering).  Records whose gauge field is `A_h = b_h + a_h Z`
(`Z` central, `a_h` real), with
* `b_h` bounded in `L²_h`, eventually `h ‖b_h‖_∞ ≤ 1/512`, and the compactness property
  `BCompact` (small Coulomb gauge or bounded constant commuting links);
* `R_h^0 a_h → a₀` strongly in `L⁴` and `R_h^0 D⁺_μ a_{h,ν} → G^a_{μν}` strongly in `L²`
  (the determinant normalization; **no smallness of `a_h`**);
* `(F1)`, `(F3)` (isometric links, bounded packets, vanishing Wilson screens), `(F4)` (banks),

have, after extraction, the conclusions of `FiniteWilsonZeroDefect.wilson_coulomb_extraction`:
a `CoHyp` on the same chart (strong `L⁴` convergence of the **full** connection
`A = B + a₀ Z`), convergent physical banks, `R^0 𝔽_h → F` and `R^0 D⁺A_h → G` strongly in `L²`
with `F = F_A`, and `R^0 𝕂_h → K` strongly in `L²`. -/
theorem combined_extraction_core (D : Data 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢) {Z : 𝔄}
    (hZ : ∀ X : 𝔄, Commute X Z) (n : ℕ → ℕ) [∀ k, NeZero (n k)]
    (y : ∀ k, Grid (n k) → Field 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢)
    (θs : ℕ → Bank J (EuclideanSpace ℝ (Fin rH)) 𝓢) (hn : Tendsto n atTop atTop)
    (b : ∀ k, Fin 4 → Grid (n k) → 𝔄) (a : ∀ k, Fin 4 → Grid (n k) → ℝ)
    (hyab : ∀ k μ x, gauge (y k) μ x = b k μ x + a k μ x • Z)
    (hbB : ∃ MB, ∀ k μ, gridNorm (b k μ) ≤ MB)
    (hbs : ∀ᶠ k in atTop, ∀ μ x, (n k : ℝ)⁻¹ * ‖b k μ x‖ ≤ 1 / 512)
    (hbC : BCompact n b) (a₀ : Fin 4 → 𝕋 → ℝ) (Ga : Fin 4 → Fin 4 → 𝕋 → ℝ)
    (ha : ∀ μ, LpTendsto volume 4 (fun k => pc (a k μ)) (a₀ μ))
    (hGa : ∀ μ ν, LpTendsto volume 2 (fun k => pc (NativeHiggs.DpV μ (a k ν))) (Ga μ ν))
    -- `(F1)`
    (Ke : Set M4) (hKe : IsCompact Ke) (hpos : ∀ M ∈ Ke, 0 < Matrix.det (show Mat from M))
    (hval : ∀ k x, coframeM (y k) x ∈ Ke) (cm : ℝ) (hcm : cm ≤ 1 / 64)
    (hmar : ∀ k x μ, (n k : ℝ)⁻¹ * ‖ωM (y k) μ x‖ ≤ cm)
    (hTBe : TotallyBounded (range fun k => pcLp (coframeM (y k))))
    (hTBq : TotallyBounded (range fun k => pcLp (fun x lam => qM (y k) lam x)))
    -- `(F3)`
    (hAd : ∀ k x μ (X : 𝔄), ‖exp ((n k : ℝ)⁻¹ • gauge (y k) μ x) * X *
        exp (-((n k : ℝ)⁻¹ • gauge (y k) μ x))‖ = ‖X‖)
    (hUH : ∀ k x μ (v : EuclideanSpace ℝ (Fin rH)),
        ‖exp ((n k : ℝ)⁻¹ • D.ρHL (gauge (y k) μ x)) v‖ = ‖v‖)
    (hFb : ∃ M, ∀ k, gridNorm (curvPacket (n k) (y k)) ≤ M)
    (hKb : ∃ M, ∀ k, gridNorm (higgsPacket D (n k) (y k)) ≤ M)
    (hΩF : ∀ ε > 0, ∃ ρ > 0, ∀ᶠ k in atTop, ∀ (μ : Fin 4) (m : ℕ), 0 < m → (m : ℝ) / n k ≤ ρ →
      gridNorm (wilsonShiftR (adLinks (n k) (y k) (hAd k)) μ m (curvPacket (n k) (y k)) -
        curvPacket (n k) (y k)) ≤ ε)
    (hΩK : ∀ ε > 0, ∃ ρ > 0, ∀ᶠ k in atTop, ∀ (μ : Fin 4) (m : ℕ), 0 < m → (m : ℝ) / n k ≤ ρ →
      gridNorm (wilsonShiftR (higgsLinks D (n k) (y k) (hUH k)) μ m
        (higgsPacket D (n k) (y k)) - higgsPacket D (n k) (y k)) ≤ ε)
    -- `(F4)`, banks
    (Kθ : Set (ℝ × ℝ × ℝ × ℝ × (Fin J → ℝ) × (EuclideanSpace ℝ (Fin rH) →L[ℝ] Spin 𝓢)))
    (hKθ : IsCompact Kθ) (hθK : ∀ k, bankVec (θs k) ∈ Kθ)
    (hphys : ∀ v ∈ Kθ, v.1 ≠ 0 ∧ ∀ j, 0 ≤ v.2.2.2.2.1 j) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ H : CoHyp (fun k => n (φ k)) (fun k => y (φ k)),
      H.Ke = Ke ∧ H.c = cm ∧
      ∃ θ : Bank J (EuclideanSpace ℝ (Fin rH)) 𝓢, BankConv (fun k => θs (φ k)) θ ∧
        θ.κ ≠ 0 ∧ (∀ j, 0 ≤ θ.w j) ∧
      ∃ F : Fin 4 → Fin 4 → 𝕋 → 𝔄, (∀ μ ν, LpTendsto volume 2 (fun k => pc (fun x =>
          NativeScaling.fieldStrength (n (φ k) : ℝ)⁻¹ (gauge (y (φ k))) x μ ν)) (F μ ν)) ∧
      ∃ G : Fin 4 → Fin 4 → 𝕋 → 𝔄, (∀ μ ν, LpTendsto volume 2
          (fun k => pc (NativeHiggs.DpV μ (gauge (y (φ k)) ν))) (G μ ν)) ∧
        (∀ μ ν, F μ ν =ᵐ[MeasureTheory.volume] NativeReconstructed.recCurv H.A₀ G μ ν) ∧
      ∃ K₀ : Fin 4 → 𝕋 → EuclideanSpace ℝ (Fin rH), ∀ μ, LpTendsto volume 2
        (fun k => pc (fun x => higgsLink D (n (φ k) : ℝ)⁻¹ (y (φ k)) x μ)) (K₀ μ) := by
  have : FiniteDimensional ℂ 𝔄 := Module.Finite.of_restrictScalars_finite ℝ ℂ 𝔄
  have hNpos : ∀ k, (0 : ℝ) < (n k : ℝ)⁻¹ := fun k =>
    inv_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (n k)))
  have hgauge : ∀ k, gauge (y k) = DeterminantCombined.combined (b k) Z (a k) := fun k =>
    funext fun μ => funext fun x => hyab k μ x
  obtain ⟨MB, hMB⟩ := hbB
  -- the `L²_h` bound of the potential
  have hCa : ∀ μ, ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ k, eLpNorm (pc (a k μ)) 4 volume ≤ C := fun μ =>
    NativeGridLp.exists_bound_of_lpTendsto (ha μ)
  choose Ca hCa hCab using hCa
  set MA : ℝ := ∑ μ, (Ca μ).toReal with hMA
  have hMA0 : ∀ μ, (Ca μ).toReal ≤ MA := fun μ =>
    Finset.single_le_sum (f := fun μ => (Ca μ).toReal) (fun _ _ => ENNReal.toReal_nonneg)
      (Finset.mem_univ μ)
  have hgA : ∀ k μ, gridNorm (a k μ) ≤ MA := fun k μ => by
    refine (NativeCoulomb.gridNorm_le_g4 (a k μ)).trans ?_
    rw [NativeCoulomb.g4_eq_toReal]
    exact (ENNReal.toReal_mono (hCa μ) (hCab μ k)).trans (hMA0 μ)
  -- `h ‖a_h‖_∞ → 0`
  have hmesh : ∀ μ, Tendsto (fun k => NativeCriticalGrid.meshSup (a k μ)) atTop (𝓝 0) :=
    fun μ => NativeCriticalGrid.tendsto_meshSup hn (ha μ).memLp_lim (ha μ).tendsto
  have has : ∀ᶠ k in atTop, ∀ μ x, (n k : ℝ)⁻¹ * |a k μ x| * ‖Z‖ ≤ 1 / 512 := by
    have hδ : (0 : ℝ) < 1 / 512 / (‖Z‖ + 1) := by positivity
    have hev : ∀ μ, ∀ᶠ k in atTop, NativeCriticalGrid.meshSup (a k μ) < 1 / 512 / (‖Z‖ + 1) :=
      fun μ => (hmesh μ).eventually (gt_mem_nhds hδ)
    filter_upwards [eventually_all.2 hev] with k hk μ x
    have h1 : (n k : ℝ)⁻¹ * |a k μ x| ≤ 1 / 512 / (‖Z‖ + 1) := by
      have := NativeCriticalGrid.le_meshSup (a k μ) x
      rw [Real.norm_eq_abs] at this
      exact this.trans (hk μ).le
    calc (n k : ℝ)⁻¹ * |a k μ x| * ‖Z‖ ≤ 1 / 512 / (‖Z‖ + 1) * ‖Z‖ :=
          mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ ≤ 1 / 512 := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          nlinarith [norm_nonneg Z]
  -- the curvature split, eventually
  have hsplit : ∀ᶠ k in atTop, ∀ x μ ν,
      NativeScaling.fieldStrength (n k : ℝ)⁻¹ (b k) x μ ν =
        NativeScaling.fieldStrength (n k : ℝ)⁻¹ (gauge (y k)) x μ ν -
          (NativeHiggs.DpV μ (a k ν) x - NativeHiggs.DpV ν (a k μ) x) • Z := by
    filter_upwards [hbs, has] with k hk1 hk2 x μ ν
    rw [hgauge k, fieldStrength_combined_of_small (b k) hZ (a k) hk1 hk2 x μ ν,
      abelCurv_eq_DpV]
    abel
  -- the curvature packet is precompact (the adjoint links only see `b`)
  have hAdb : ∀ k x μ (X : 𝔄), ‖exp ((n k : ℝ)⁻¹ • b k μ x) * X *
      exp (-((n k : ℝ)⁻¹ • b k μ x))‖ = ‖X‖ := fun k x μ X => by
    rw [← ad_combined _ (a k μ x) hZ X, ← hyab]
    exact hAd k x μ X
  have hTBF : TotallyBounded (range fun k => pcLp (curvPacket (n k) (y k))) := by
    refine native_wilson_vector_totallyBounded_real n hn (fun k => adLinks (n k) (y k) (hAd k))
      (fun k => curvPacket (n k) (y k)) hFb hΩF (fun k μ x => 6 * ‖b k μ x‖)
      (fun k μ x => by positivity) (MA := 6 * MB)
      (fun k μ => by
        rw [gridNorm_const_mul (fun x => ‖b k μ x‖) (by norm_num),
          NativeWilsonCompactness.gridNorm_norm]
        exact mul_le_mul_of_nonneg_left (hMB k μ) (by norm_num)) (fun k μ x v => ?_)
    have h1 : ∀ X : 𝔄, ‖adIso ((n k : ℝ)⁻¹ • gauge (y k) μ x) (hAd k x μ) X - X‖ ≤
        6 * ‖b k μ x‖ / n k * ‖X‖ := fun X => by
      rw [adIso_apply, hyab, ad_combined _ (a k μ x) hZ X]
      refine (norm_ad_sub_le_of_iso (hAdb k x μ) X).trans (le_of_eq ?_)
      rw [norm_smul, Real.norm_of_nonneg (hNpos k).le]
      ring
    exact norm_piIso_sub_le _ (by positivity) (fun w => norm_piIso_sub_le _ (by positivity) h1 w) v
  -- the Higgs packet is precompact
  have hTBK : TotallyBounded (range fun k => pcLp (higgsPacket D (n k) (y k))) := by
    refine native_wilson_vector_totallyBounded_real n hn (fun k => higgsLinks D (n k) (y k) (hUH k))
      (fun k => higgsPacket D (n k) (y k)) hKb hΩK
      (fun k μ x => (2 * ‖D.ρHL‖) * (‖b k μ x‖ + ‖Z‖ * |a k μ x|)) (fun k μ x => by positivity)
      (MA := (2 * ‖D.ρHL‖) * (MB + ‖Z‖ * MA)) (fun k μ => ?_) (fun k μ x v => ?_)
    · rw [gridNorm_const_mul _ (by positivity)]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have e : (fun x => ‖b k μ x‖ + ‖Z‖ * |a k μ x|) =
          (fun x => ‖b k μ x‖) + fun x => ‖Z‖ * ‖a k μ x‖ := by
        funext x; simp [Real.norm_eq_abs]
      rw [e]
      refine (gridNorm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [NativeWilsonCompactness.gridNorm_norm]; exact hMB k μ
      · rw [gridNorm_const_mul (fun x => ‖a k μ x‖) (norm_nonneg Z),
          NativeWilsonCompactness.gridNorm_norm]
        exact mul_le_mul_of_nonneg_left (hgA k μ) (norm_nonneg Z)
    · have hZn : ‖(n k : ℝ)⁻¹ • D.ρHL (gauge (y k) μ x)‖ ≤
          ‖D.ρHL‖ * (‖b k μ x‖ + ‖Z‖ * |a k μ x|) / n k := by
        rw [norm_smul, Real.norm_of_nonneg (hNpos k).le, hyab]
        have h2 : ‖b k μ x + a k μ x • Z‖ ≤ ‖b k μ x‖ + ‖Z‖ * |a k μ x| := by
          refine (norm_add_le _ _).trans (le_of_eq ?_)
          rw [norm_smul, Real.norm_eq_abs, mul_comm]
        calc (n k : ℝ)⁻¹ * ‖D.ρHL (b k μ x + a k μ x • Z)‖
            ≤ (n k : ℝ)⁻¹ * (‖D.ρHL‖ * (‖b k μ x‖ + ‖Z‖ * |a k μ x|)) :=
              mul_le_mul_of_nonneg_left ((D.ρHL.le_opNorm _).trans
                (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))) (hNpos k).le
          _ = _ := by ring
      have h1 : ∀ w : EuclideanSpace ℝ (Fin rH),
          ‖expIso ((n k : ℝ)⁻¹ • D.ρHL (gauge (y k) μ x)) (hUH k x μ) w - w‖ ≤
            (2 * ‖D.ρHL‖) * (‖b k μ x‖ + ‖Z‖ * |a k μ x|) / n k * ‖w‖ := fun w => by
        refine (norm_exp_apply_sub_le_of_iso (hUH k x μ) w).trans ?_
        have := mul_le_mul_of_nonneg_left hZn (by norm_num : (0 : ℝ) ≤ 2)
        calc 2 * ‖(n k : ℝ)⁻¹ • D.ρHL (gauge (y k) μ x)‖ * ‖w‖ ≤
              2 * (‖D.ρHL‖ * (‖b k μ x‖ + ‖Z‖ * |a k μ x|) / n k) * ‖w‖ :=
              mul_le_mul_of_nonneg_right this (norm_nonneg _)
          _ = _ := by ring
      exact norm_piIso_sub_le _ (by positivity) h1 v
  -- successive extractions
  obtain ⟨φ₁, hφ₁, e₀, he⟩ := exists_subseq_lpTendsto (fun k => coframeM (y k)) hTBe
  obtain ⟨φ₂, hφ₂, q₀, hq⟩ := exists_subseq_lpTendsto
    (n := fun k => n (φ₁ k)) (fun k x lam => qM (y (φ₁ k)) lam x) (totallyBounded_comp hTBq φ₁)
  set ψ₂ : ℕ → ℕ := fun k => φ₁ (φ₂ k) with hψ₂
  obtain ⟨φ₃, hφ₃, Fp, hFp⟩ := exists_subseq_lpTendsto (n := fun k => n (ψ₂ k))
    (fun k => curvPacket (n (ψ₂ k)) (y (ψ₂ k))) (totallyBounded_comp hTBF ψ₂)
  set ψ₃ : ℕ → ℕ := fun k => ψ₂ (φ₃ k) with hψ₃
  obtain ⟨φ₄, hφ₄, Kp, hKp⟩ := exists_subseq_lpTendsto (n := fun k => n (ψ₃ k))
    (fun k => higgsPacket D (n (ψ₃ k)) (y (ψ₃ k))) (totallyBounded_comp hTBK ψ₃)
  set ψ₄ : ℕ → ℕ := fun k => ψ₃ (φ₄ k) with hψ₄
  have hψ₄m : StrictMono ψ₄ := ((hφ₁.comp hφ₂).comp hφ₃).comp hφ₄
  -- the literal curvature along `ψ₄`
  have hF4 : ∀ μ ν, LpTendsto volume 2 (fun k => pc (fun x =>
      NativeScaling.fieldStrength (n (ψ₄ k) : ℝ)⁻¹ (gauge (y (ψ₄ k))) x μ ν))
      (fun z => Fp z μ ν) := fun μ ν =>
    ((hFp.comp_strictMono hφ₄).clm ((ContinuousLinearMap.proj ν).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => Fin 4 → 𝔄) μ))).congr
      (fun k => Eventually.of_forall fun z => rfl) (Eventually.of_forall fun z => rfl)
  -- the semisimple curvature converges
  set LZ : ℝ →L[ℝ] 𝔄 := (ContinuousLinearMap.id ℝ ℝ).smulRight Z with hLZ
  have hFbconv : ∀ μ ν, LpTendsto volume 2 (fun k => pc (fun x =>
      NativeScaling.fieldStrength (n (ψ₄ k) : ℝ)⁻¹ (b (ψ₄ k)) x μ ν))
      (fun z => Fp z μ ν - (Ga μ ν z - Ga ν μ z) • Z) := by
    intro μ ν
    have h1 := (hF4 μ ν).sub ((((hGa μ ν).comp_strictMono hψ₄m).sub
      ((hGa ν μ).comp_strictMono hψ₄m)).clm LZ)
    refine lpTendsto_of_eventually_eq (h1.congr (fun k => Eventually.of_forall fun z => rfl)
      (Eventually.of_forall fun z => ?_)) (fun k => memLp_pc _) ?_
    · simp [hLZ]
    · filter_upwards [hψ₄m.tendsto_atTop.eventually hsplit] with k hk
      funext z
      simp only [pc, Pi.sub_apply, hLZ, ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.id_apply, hk]
  -- the compactness of the semisimple part
  obtain ⟨φ₅, hφ₅, B, Gb, hB, hGb, hFbG⟩ := hbC ψ₄ hψ₄m _ hFbconv
  set ψ₅ : ℕ → ℕ := fun k => ψ₄ (φ₅ k) with hψ₅
  -- the banks
  obtain ⟨φ₆, hφ₆, θ, hθ, hκ, hw⟩ := exists_bankConv (θs := fun k => θs (ψ₅ k)) hKθ
    (fun k => hθK (ψ₅ k)) hphys
  set φ : ℕ → ℕ := fun k => ψ₅ (φ₆ k) with hφ
  have hφm : StrictMono φ := (hψ₄m.comp hφ₅).comp hφ₆
  have r1 : StrictMono (fun k => φ₂ (φ₃ (φ₄ (φ₅ (φ₆ k))))) :=
    (((hφ₂.comp hφ₃).comp hφ₄).comp hφ₅).comp hφ₆
  have r2 : StrictMono (fun k => φ₃ (φ₄ (φ₅ (φ₆ k)))) := ((hφ₃.comp hφ₄).comp hφ₅).comp hφ₆
  have r4 : StrictMono (fun k => φ₅ (φ₆ k)) := hφ₅.comp hφ₆
  -- the full connection
  have hA : ∀ μ, LpTendsto volume 4 (fun k => pc (gauge (y (φ k)) μ))
      (fun z => B μ z + a₀ μ z • Z) := fun μ =>
    (((hB μ).comp_strictMono hφ₆).add (((ha μ).comp_strictMono hφm).clm LZ)).congr
      (fun k => Eventually.of_forall fun z => by
        simp only [pc, Pi.add_apply, hLZ, ContinuousLinearMap.smulRight_apply,
          ContinuousLinearMap.id_apply, hyab]
        rfl)
      (Eventually.of_forall fun z => by simp [hLZ])
  have hG : ∀ μ ν, LpTendsto volume 2 (fun k => pc (NativeHiggs.DpV μ (gauge (y (φ k)) ν)))
      (fun z => Gb μ ν z + Ga μ ν z • Z) := fun μ ν =>
    (((hGb μ ν).comp_strictMono hφ₆).add (((hGa μ ν).comp_strictMono hφm).clm LZ)).congr
      (fun k => Eventually.of_forall fun z => by
        simp only [pc, Pi.add_apply, hLZ, ContinuousLinearMap.smulRight_apply,
          ContinuousLinearMap.id_apply]
        rw [show gauge (y (φ k)) ν = fun x => b (φ k) ν x + a (φ k) ν x • Z from
          funext fun x => hyab _ ν x, DpV_combined])
      (Eventually.of_forall fun z => by simp [hLZ])
  let H : CoHyp (fun k => n (φ k)) (fun k => y (φ k)) :=
    { hn := hn.comp hφm.tendsto_atTop
      Ke := Ke
      hKe := hKe
      hKdet := fun M hM => (hpos M hM).ne'
      hval := fun k x => hval (φ k) x
      c := cm
      hmar := fun k x μ => hmar (φ k) x μ
      e₀ := e₀
      he := he.comp_strictMono r1
      p := fun lam z => q₀ z lam
      hp := fun lam => ((hq.comp_strictMono r2).clm (ContinuousLinearMap.proj lam)).congr
        (fun k => Eventually.of_forall fun z => rfl) (Eventually.of_forall fun z => rfl)
      A₀ := fun μ z => B μ z + a₀ μ z • Z
      hA := hA }
  refine ⟨φ, hφm, H, rfl, rfl, θ, hθ, hκ, hw, fun μ ν z => Fp z μ ν,
    fun μ ν => (hF4 μ ν).comp_strictMono r4, fun μ ν z => Gb μ ν z + Ga μ ν z • Z, hG,
    fun μ ν => ?_, fun μ z => Kp z μ, fun μ => ?_⟩
  · filter_upwards [hFbG μ ν] with z hz
    change Fp z μ ν = NativeReconstructed.recCurv (fun μ z => B μ z + a₀ μ z • Z)
      (fun μ ν z => Gb μ ν z + Ga μ ν z • Z) μ ν z
    rw [recCurv_combined hZ, ← hz]
    abel
  · exact ((hKp.comp_strictMono r4).clm (ContinuousLinearMap.proj μ)).congr
      (fun k => Eventually.of_forall fun z => rfl) (Eventually.of_forall fun z => rfl)

end Core



/-! ### The two sources of semisimple compactness -/

section Instances

open NativeDensity
open ShiftedJetAction (Grid)

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℂ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
  [FiniteDimensional ℝ 𝔄]
variable {E₀ : Type*} [NormedAddCommGroup E₀] [InnerProductSpace ℝ E₀]

/-- **Small co-closed semisimple parts are compact** (`thm:native-discrete-Coulomb`): there is
`ε > 0` such that, for `N_k → ∞` and `b_k` with `δ_h T₀ b_k = 0`, `‖T₀ b_{k,μ}‖_{4,h} ≤ ε`, the
family is bounded in `L²_h`, satisfies `h ‖b_k‖_∞ ≤ 1/512`, and has the compactness property
`BCompact`. -/
theorem bCompact_of_coulomb (T₀ : 𝔄 →L[ℝ] E₀) {c₀ : ℝ} (hc0 : 0 ≤ c₀)
    (hc : ∀ X, ‖X‖ ≤ c₀ * ‖T₀ X‖) :
    ∃ ε > 0, ∀ (n : ℕ → ℕ) [∀ k, NeZero (n k)], Tendsto n atTop atTop →
      ∀ b : ∀ k, Fin 4 → Grid (n k) → 𝔄,
      (∀ k, NativeCoulomb.codiffT T₀ (fun x μ => b k μ x) = 0) →
      (∀ k μ, NativeCoulomb.g4 (fun x => T₀ (b k μ x)) ≤ ε) →
      (∃ MB, ∀ k μ, gridNorm (b k μ) ≤ MB) ∧
      (∀ k μ x, (n k : ℝ)⁻¹ * ‖b k μ x‖ ≤ 1 / 512) ∧ BCompact n b := by
  have : FiniteDimensional ℂ 𝔄 := Module.Finite.of_restrictScalars_finite ℝ ℂ 𝔄
  obtain ⟨ε₀, hε₀, hC⟩ := NativeCoulomb.native_discrete_Coulomb T₀ hc0 hc
  set ε : ℝ := min ε₀ (1 / (512 * (c₀ + 1))) with hεdef
  have hε : 0 < ε := lt_min hε₀ (by positivity)
  have hεε : ε ≤ ε₀ := min_le_left _ _
  have hcε : c₀ * ε ≤ 1 / 512 := by
    have h1 : ε ≤ 1 / (512 * (c₀ + 1)) := min_le_right _ _
    calc c₀ * ε ≤ c₀ * (1 / (512 * (c₀ + 1))) := mul_le_mul_of_nonneg_left h1 hc0
      _ ≤ 1 / 512 := by
          rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
  refine ⟨ε, hε, fun n _ hn b hδ hs => ⟨⟨c₀ * ε, fun k μ => ?_⟩, fun k μ x => ?_, ?_⟩⟩
  · have h := gridNorm_norm_le T₀ hc0 hc (N := n k) (b k) (hs k) μ (K := 1) zero_le_one
    simp only [one_mul, NativeWilsonCompactness.gridNorm_norm] at h
    exact h
  · exact (mesh_small T₀ hc0 hc (N := n k) (b k) (hs k) x μ).trans hcε
  · intro ψ hψ Fb hFb
    have hlt : ∀ k x μ ν, ‖NativeScaling.gaugePlaquette (n (ψ k) : ℝ)⁻¹ (b (ψ k)) x μ ν - 1‖ < 1 :=
      fun k x μ ν => (norm_gaugePlaquette_sub_one_le (b (ψ k))
        (fun μ x => (mesh_small T₀ hc0 hc (N := n (ψ k)) (b (ψ k)) (hs (ψ k)) x μ).trans hcε)
        x μ ν).trans_lt (by norm_num)
    have hFcl : ∀ μ ν, LpTendsto volume 2 (fun k => pc (fun x =>
        NativeYMIdentification.curvLog (n (ψ k)) (fun x μ => b (ψ k) μ x) x μ ν)) (Fb μ ν) :=
      fun μ ν => (hFb μ ν).congr (fun k => Eventually.of_forall fun z => by
        simp only [pc]
        exact NativeYMBridge.fieldStrength_eq_curvLog (b (ψ k)) _ μ ν (hlt k _ μ ν))
        (Eventually.of_forall fun z => rfl)
    obtain ⟨φ, hφ, A₀, G, hA, hG, -, -, hFG, -⟩ := hC (fun k => n (ψ k))
      (hn.comp hψ.tendsto_atTop) (fun k x μ => b (ψ k) μ x) Fb (fun k => hδ (ψ k))
      (fun k μ => (hs (ψ k) μ).trans hεε) hFcl
    exact ⟨φ, hφ, A₀, G, hA, hG, fun μ ν => by
      filter_upwards [hFG μ ν] with z hz
      simp only [NativeReconstructed.recCurv]
      exact hz⟩

/-- `‖R_h^0 c‖`-type bound: the nodal norm of a constant is its norm. -/
theorem gridNorm_const {F : Type*} [NormedAddCommGroup F] {N : ℕ} [NeZero N] (c : F) :
    gridNorm (fun _ : Grid N => c) = ‖c‖ := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  unfold gridNorm
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : (Fintype.card (Grid N) : ℝ) = (N : ℝ) ^ 4 := by simp [ZMod.card]
  rw [hcard, Fintype.card_fin, ← mul_assoc, one_div, ← mul_pow, inv_mul_cancel₀ hN.ne', one_pow,
    one_mul, Real.sqrt_sq (norm_nonneg c)]

/-- **Bounded constant commuting semisimple parts are compact**
(`lem:flat-semisimple-normalization`): constant links `b_{k,μ}(x) = β_{k,μ}` with pairwise
commuting, uniformly bounded values are bounded in `L²_h`, eventually satisfy
`h ‖b_k‖_∞ ≤ 1/512`, and have the compactness property `BCompact` (zero curvature, zero first
differences, a convergent subsequence of commuting constants). -/
theorem bCompact_of_const (n : ℕ → ℕ) [∀ k, NeZero (n k)] (hn : Tendsto n atTop atTop)
    (β : ℕ → Fin 4 → 𝔄) (hcomm : ∀ k μ ν, Commute (β k μ) (β k ν)) {Mβ : ℝ}
    (hMβ : ∀ k μ, ‖β k μ‖ ≤ Mβ) :
    (∃ MB, ∀ k μ, gridNorm (fun _ : Grid (n k) => β k μ) ≤ MB) ∧
    (∀ᶠ k in atTop, ∀ μ (x : Grid (n k)), (n k : ℝ)⁻¹ * ‖β k μ‖ ≤ 1 / 512) ∧
    BCompact n (fun k μ (_ : Grid (n k)) => β k μ) := by
  refine ⟨⟨Mβ, fun k μ => by rw [gridNorm_const]; exact hMβ k μ⟩, ?_, ?_⟩
  · have hM0 : 0 ≤ Mβ := (norm_nonneg _).trans (hMβ 0 0)
    have hev : ∀ᶠ k in atTop, (512 * Mβ : ℝ) ≤ n k :=
      (tendsto_natCast_atTop_atTop.comp hn).eventually (eventually_ge_atTop _)
    filter_upwards [hev] with k hk μ x
    have hN : (0 : ℝ) < n k := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (n k))
    rw [inv_mul_le_iff₀ hN]
    nlinarith [hMβ k μ]
  · intro ψ hψ Fb hFb
    -- zero curvature
    have hF0 : ∀ k x μ ν, NativeScaling.fieldStrength (n (ψ k) : ℝ)⁻¹
        (fun μ (_ : Grid (n (ψ k))) => β (ψ k) μ) x μ ν = 0 := by
      intro k x μ ν
      have hc : Commute (exp ((n (ψ k) : ℝ)⁻¹ • β (ψ k) μ))
          (exp ((n (ψ k) : ℝ)⁻¹ • β (ψ k) ν)) :=
        (((hcomm (ψ k) μ ν).smul_left _).smul_right _).exp
      have hP : NativeScaling.gaugePlaquette (n (ψ k) : ℝ)⁻¹
          (fun μ (_ : Grid (n (ψ k))) => β (ψ k) μ) x μ ν = 1 := by
        simp only [NativeScaling.gaugePlaquette]
        set u := exp ((n (ψ k) : ℝ)⁻¹ • β (ψ k) μ)
        set v := exp ((n (ψ k) : ℝ)⁻¹ • β (ψ k) ν)
        have huu : u * exp (-((n (ψ k) : ℝ)⁻¹ • β (ψ k) μ)) = 1 :=
          FiniteWilsonZeroDefect.exp_mul_exp_neg' _
        have hvv : v * exp (-((n (ψ k) : ℝ)⁻¹ • β (ψ k) ν)) = 1 :=
          FiniteWilsonZeroDefect.exp_mul_exp_neg' _
        rw [hc.eq]
        calc v * u * exp (-((n (ψ k) : ℝ)⁻¹ • β (ψ k) μ)) * exp (-((n (ψ k) : ℝ)⁻¹ • β (ψ k) ν))
            = v * (u * exp (-((n (ψ k) : ℝ)⁻¹ • β (ψ k) μ))) *
                exp (-((n (ψ k) : ℝ)⁻¹ • β (ψ k) ν)) := by noncomm_ring
          _ = 1 := by rw [huu, mul_one, hvv]
      simp only [NativeScaling.fieldStrength, hP, sub_self, ShiftedPlaquette.logOneAdd, zero_mul,
        smul_zero]
    have hFb0 : ∀ μ ν, Fb μ ν =ᵐ[MeasureTheory.volume] 0 := by
      intro μ ν
      have e : ∀ k, (pc fun x => NativeScaling.fieldStrength (n (ψ k) : ℝ)⁻¹
          ((fun k μ (_ : Grid (n k)) => β k μ) (ψ k)) x μ ν) = 0 := fun k => by
        funext z; exact hF0 k _ μ ν
      have ht : Tendsto (fun _ : ℕ => eLpNorm (Fb μ ν) 2 volume) atTop (𝓝 0) :=
        (hFb μ ν).tendsto.congr fun k => by rw [e k, zero_sub, eLpNorm_neg]
      have h0 : eLpNorm (Fb μ ν) 2 volume = 0 := tendsto_nhds_unique tendsto_const_nhds ht
      exact (eLpNorm_eq_zero_iff (hFb μ ν).memLp_lim.1 two_ne_zero).1 h0
    -- a convergent subsequence of the constants
    have hbdd : Bornology.IsBounded (Metric.closedBall (0 : Fin 4 → 𝔄) Mβ) :=
      Metric.isBounded_closedBall
    have hM0 : 0 ≤ Mβ := (norm_nonneg _).trans (hMβ 0 0)
    obtain ⟨β₀, -, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded hbdd
      (x := fun k => β (ψ k)) fun k => by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact (pi_norm_le_iff_of_nonneg hM0).2 fun μ => hMβ _ μ
    have hlimμ : ∀ μ, Tendsto (fun k => β (ψ (φ k)) μ) atTop (𝓝 (β₀ μ)) := fun μ =>
      ((continuous_apply μ).tendsto β₀).comp hlim
    -- limits of commuting families commute
    have hc₀ : ∀ μ ν, β₀ μ * β₀ ν = β₀ ν * β₀ μ := by
      intro μ ν
      have h1 : Tendsto (fun k => β (ψ (φ k)) μ * β (ψ (φ k)) ν) atTop (𝓝 (β₀ μ * β₀ ν)) :=
        (hlimμ μ).mul (hlimμ ν)
      have h2 : Tendsto (fun k => β (ψ (φ k)) ν * β (ψ (φ k)) μ) atTop (𝓝 (β₀ ν * β₀ μ)) :=
        (hlimμ ν).mul (hlimμ μ)
      refine tendsto_nhds_unique h1 (h2.congr fun k => ?_)
      exact (hcomm (ψ (φ k)) μ ν).eq.symm
    refine ⟨φ, hφ, fun μ _ => β₀ μ, fun _ _ _ => 0, fun μ => ?_, fun μ ν => ?_, fun μ ν => ?_⟩
    · exact (FirstVariationCalculus.LpTendsto.const_seq (hlimμ μ)).congr (fun k => Eventually.of_forall fun z => rfl)
        (Eventually.of_forall fun z => rfl)
    · refine (LpTendsto.const (MemLp.zero : MemLp (fun _ : 𝕋 => (0 : 𝔄)) 2 volume)).congr
        (fun k => Eventually.of_forall fun z => ?_) (Eventually.of_forall fun z => rfl)
      simp [pc, NativeHiggs.DpV]
    · filter_upwards [hFb0 μ ν] with z hz
      simp only [hz, NativeReconstructed.recCurv, Pi.zero_apply, sub_self, zero_add, hc₀ μ ν]

end Instances

/-! ### The criterion with a central background -/

section Criterion

open NativeDensity NativeBank NativeHiggsVar NativeDiracLimit NativeDiracConvergence
open ShiftedJetAction (Grid)
open NativeDiracConv (CoHyp qM ωM)
open NativeScaling (Mat)
open NativeSpinorGraph (κid spinGraph dualGraph coHypSubseq)

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℂ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
  [FiniteDimensional ℝ 𝔄]
variable {rH : ℕ} [NeZero rH]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
  [FiniteDimensional ℝ 𝓢]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {r r' : ℕ} [NeZero r] [NeZero r']
variable {J : ℕ}

set_option maxHeartbeats 6400000 in
-- the composition of the extraction with the all-sector closure
/-- **`thm:finite-Wilson-zero-defect` after normalization, with a central background**
(`cor:determinant-resolved-closure`, all conclusions after the normalization; unit-torus
rendering).  For records with gauge field `A_h = b_h + a_h Z` (`Z` central) satisfying the
hypotheses of `combined_extraction_core` on `b_h` and `a_h` (**only `b_h` is controlled; `a_h`
need not be small**), under `(F1)`, `(F3)`, `(F4)` and the reconstruction chart condition, after
extraction: `eq:Wilson-strong-convergence`, `eq:native-all-sector-limit` with the cutoff banks,
the consistency relative to the reconstructed fields, the Euler equations under native
stationarity, and strong `L¹` convergence of the bosonic stress densities — exactly the
conclusions of `FiniteWilsonZeroDefect.finite_wilson_criterion`. -/
theorem combined_criterion_core (D₀ : Data 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢)
    (Tj : Fin J → 𝔄 →L[ℝ] E) (Θ : 𝓢 ≃L[ℝ] EuclideanSpace ℝ (Fin r))
    (Θ' : CoSpinor 𝓢 ≃L[ℝ] EuclideanSpace ℝ (Fin r')) {Z : 𝔄}
    (hZ : ∀ X : 𝔄, Commute X Z) (n : ℕ → ℕ) [∀ k, NeZero (n k)]
    (y : ∀ k, Grid (n k) → Field 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢)
    (θs : ℕ → Bank J (EuclideanSpace ℝ (Fin rH)) 𝓢) (hn : Tendsto n atTop atTop)
    (b : ∀ k, Fin 4 → Grid (n k) → 𝔄) (a : ∀ k, Fin 4 → Grid (n k) → ℝ)
    (hyab : ∀ k μ x, gauge (y k) μ x = b k μ x + a k μ x • Z)
    (hbB : ∃ MB, ∀ k μ, gridNorm (b k μ) ≤ MB)
    (hbs : ∀ᶠ k in atTop, ∀ μ x, (n k : ℝ)⁻¹ * ‖b k μ x‖ ≤ 1 / 512)
    (hbC : BCompact n b) (a₀ : Fin 4 → 𝕋 → ℝ) (Ga : Fin 4 → Fin 4 → 𝕋 → ℝ)
    (ha : ∀ μ, LpTendsto volume 4 (fun k => pc (a k μ)) (a₀ μ))
    (hGa : ∀ μ ν, LpTendsto volume 2 (fun k => pc (NativeHiggs.DpV μ (a k ν))) (Ga μ ν))
    -- `(F1)`
    (Ke : Set M4) (hKe : IsCompact Ke) (hpos : ∀ M ∈ Ke, 0 < Matrix.det (show Mat from M))
    (hval : ∀ k x, coframeM (y k) x ∈ Ke) (cm : ℝ) (hcm : cm ≤ 1 / 64)
    (hmar : ∀ k x μ, (n k : ℝ)⁻¹ * ‖ωM (y k) μ x‖ ≤ cm)
    (hTBe : TotallyBounded (range fun k => pcLp (coframeM (y k))))
    (hTBq : TotallyBounded (range fun k => pcLp (fun x lam => qM (y k) lam x)))
    -- `(F3)`
    (hAd : ∀ k x μ (X : 𝔄), ‖exp ((n k : ℝ)⁻¹ • gauge (y k) μ x) * X *
        exp (-((n k : ℝ)⁻¹ • gauge (y k) μ x))‖ = ‖X‖)
    (hUH : ∀ k x μ (v : EuclideanSpace ℝ (Fin rH)),
        ‖exp ((n k : ℝ)⁻¹ • D₀.ρHL (gauge (y k) μ x)) v‖ = ‖v‖)
    (hFb : ∃ M, ∀ k, gridNorm (curvPacket (n k) (y k)) ≤ M)
    (hKb : ∃ M, ∀ k, gridNorm (higgsPacket D₀ (n k) (y k)) ≤ M)
    (BH : ℝ) (hHb : ∀ k, gridNorm (higgs (y k)) ≤ BH)
    (hΩF : ∀ ε > 0, ∃ ρ > 0, ∀ᶠ k in atTop, ∀ (μ : Fin 4) (m : ℕ), 0 < m → (m : ℝ) / n k ≤ ρ →
      gridNorm (wilsonShiftR (adLinks (n k) (y k) (hAd k)) μ m (curvPacket (n k) (y k)) -
        curvPacket (n k) (y k)) ≤ ε)
    (hΩK : ∀ ε > 0, ∃ ρ > 0, ∀ᶠ k in atTop, ∀ (μ : Fin 4) (m : ℕ), 0 < m → (m : ℝ) / n k ≤ ρ →
      gridNorm (wilsonShiftR (higgsLinks D₀ (n k) (y k) (hUH k)) μ m
        (higgsPacket D₀ (n k) (y k)) - higgsPacket D₀ (n k) (y k)) ≤ ε)
    -- `(F4)`
    (hU : ∀ k x μ (v : 𝓢), ‖D₀.ρS (exp ((n k : ℝ)⁻¹ • gauge (y k) μ x)) v‖ = ‖v‖)
    (B : ℝ) (hΨ : ∀ k, gridNorm (psi (y k)) ≤ B)
    (hKs : ∀ k μ, gridNorm (fun x => spinGraph D₀ (n k : ℝ)⁻¹ (y k) x μ) ≤ B)
    (hΨb : ∀ k, gridNorm (psiBar (y k)) ≤ B)
    (hKbd : ∀ k μ, gridNorm (fun x => dualGraph D₀ (n k : ℝ)⁻¹ (y k) x μ) ≤ B)
    (Kθ : Set (ℝ × ℝ × ℝ × ℝ × (Fin J → ℝ) × (EuclideanSpace ℝ (Fin rH) →L[ℝ] Spin 𝓢)))
    (hKθ : IsCompact Kθ) (hθK : ∀ k, bankVec (θs k) ∈ Kθ)
    (hphys : ∀ v ∈ Kθ, v.1 ≠ 0 ∧ ∀ j, 0 ≤ v.2.2.2.2.1 j)
    -- the complete unfiltered reconstructed coframes stay in the chart
    (hfK : ∀ k z, NativeTrigRec.recon (coframeM (y k)) z ∈ Ke) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ H : CoHyp (fun k => n (φ k)) (fun k => y (φ k)),
      H.Ke = Ke ∧
      ∃ θ : Bank J (EuclideanSpace ℝ (Fin rH)) 𝓢, BankConv (fun k => θs (φ k)) θ ∧
      ∃ F : Fin 4 → Fin 4 → 𝕋 → 𝔄, ∃ G : Fin 4 → Fin 4 → 𝕋 → 𝔄,
      ∃ P : HiggsHyp (bankData D₀ Tj θ) (fun k => y (φ k)),
      ∃ S : SpinHyp (κid 𝓢) (fun k => y (φ k)), ∃ u₀ : 𝕋 → Dif 𝓢 (CoSpinor 𝓢),
      -- `eq:Wilson-strong-convergence`
      (∀ μ ν, LpTendsto volume 2 (fun k => pc (fun x =>
        NativeScaling.fieldStrength (n (φ k) : ℝ)⁻¹ (gauge (y (φ k))) x μ ν)) (F μ ν)) ∧
      (∀ μ ν, LpTendsto volume 2 (fun k => pc (NativeHiggs.DpV μ (gauge (y (φ k)) ν)))
        (G μ ν)) ∧
      (∀ μ ν, F μ ν =ᵐ[MeasureTheory.volume] NativeReconstructed.recCurv H.A₀ G μ ν) ∧
      (∀ μ, LpTendsto volume 2 (fun k => pc (NativeHiggs.DpV μ (higgs (y (φ k)))))
        (fun z => P.K₀ μ z - D₀.ρHL (H.A₀ μ z) (P.H₀ z))) ∧
      (∀ j, ∃ fj : Lp ℂ 2 (MeasureTheory.volume : Measure 𝕋),
        ((fj : 𝕋 → ℂ) =ᵐ[MeasureTheory.volume] fun z => ((Θ (S.Ψ₀ z) j : ℝ) : ℂ)) ∧
        TorusSobolev.MemH 1 fj ∧ ∀ μ, (TorusSobolev.weakDeriv μ fj : 𝕋 → ℂ)
          =ᵐ[MeasureTheory.volume] fun z => ((Θ ((u₀ z).1 μ) j : ℝ) : ℂ)) ∧
      -- `eq:native-all-sector-limit` with the cutoff banks
      (∀ M : NNReal, ∀ ε > 0, ∀ᶠ k in atTop,
        ∀ τ : DTest 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢 (CoSpinor 𝓢), τ.norm ≤ M →
        |NativeAllSector.nativeVar (bankData D₀ Tj (θs (φ k))) (n (φ k)) (y (φ k))
            (testRec (κid 𝓢) (n (φ k)) (y (φ k)) τ) -
          NativeAllSector.contAllVar (bankData D₀ Tj θ) (κid 𝓢) (bankT Tj θ.w) H F P S u₀ τ|
            ≤ ε) ∧
      -- consistency relative to the reconstructed fields
      (∀ M : NNReal, ∀ ε > 0, ∀ᶠ k in atTop,
        ∀ τ : DTest 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢 (CoSpinor 𝓢), τ.norm ≤ M →
        |NativeAllSector.nativeVar (bankData D₀ Tj (θs (φ k))) (n (φ k)) (y (φ k))
            (testRec (κid 𝓢) (n (φ k)) (y (φ k)) τ) -
          NativeReconstructed.recAllVar (bankData D₀ Tj θ) (κid 𝓢) (bankT Tj θ.w)
            (NativeTrigRec.recon (coframeM (y (φ k))))
            (fun lam => NativeTrigRec.drecon lam (coframeM (y (φ k))))
            (fun μ => NativeTrigRec.recon (gauge (y (φ k)) μ))
            (fun μ ν => NativeTrigRec.drecon μ (gauge (y (φ k)) ν))
            (NativeTrigRec.recon (higgs (y (φ k))))
            (fun μ => NativeTrigRec.drecon μ (higgs (y (φ k))))
            (NativeTrigRec.recon (psi (y (φ k)))) (NativeTrigRec.recon (psiBar (y (φ k))))
            (NativeTrigRec.recJets (y (φ k))) τ| ≤ ε) ∧
      -- the Euler equations under native stationarity
      ((∀ ε > 0, ∀ᶠ k in atTop,
          ∀ τ : DTest 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢 (CoSpinor 𝓢), τ.norm ≤ 1 →
          |NativeAllSector.nativeVar (bankData D₀ Tj (θs k)) (n k) (y k)
            (testRec (κid 𝓢) (n k) (y k) τ)| ≤ ε) →
        ∀ τ : DTest 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢 (CoSpinor 𝓢),
          NativeAllSector.contAllVar (bankData D₀ Tj θ) (κid 𝓢) (bankT Tj θ.w) H F P S u₀ τ
            = 0) ∧
      -- the bosonic stress densities
      (∀ (ΘF : M4 → (Fin 4 → Fin 4 → 𝔄) →L[ℝ] (Fin 4 → Fin 4 → 𝔄) →L[ℝ] ℝ)
        (ΘK : M4 → (Fin 4 → EuclideanSpace ℝ (Fin rH)) →L[ℝ]
          (Fin 4 → EuclideanSpace ℝ (Fin rH)) →L[ℝ] ℝ) (ΘV : M4 → ℝ),
        ContinuousOn ΘF Ke → ContinuousOn ΘK Ke → ContinuousOn ΘV Ke →
        LpTendsto volume 1
          (fun k z => ΘF (pc (coframeM (y (φ k))) z) (pc (curvPacket (n (φ k)) (y (φ k))) z)
              (pc (curvPacket (n (φ k)) (y (φ k))) z) +
            ΘK (pc (coframeM (y (φ k))) z) (pc (higgsPacket D₀ (n (φ k)) (y (φ k))) z)
              (pc (higgsPacket D₀ (n (φ k)) (y (φ k))) z) +
            ΘV (pc (coframeM (y (φ k))) z) *
              potential (bankData D₀ Tj (θs (φ k))) (pc (higgs (y (φ k))) z))
          (fun z => ΘF (H.e₀ z) (fun μ ν => F μ ν z) (fun μ ν => F μ ν z) +
            ΘK (H.e₀ z) (fun μ => P.K₀ μ z) (fun μ => P.K₀ μ z) +
            ΘV (H.e₀ z) * potential (bankData D₀ Tj θ) (P.H₀ z))) := by
  obtain ⟨φ, hφ, H, hHK, hHc', θ, hθ, hκ, hw, F, hF, G, hG, hFG, K₀, hK⟩ :=
    combined_extraction_core (J := J) D₀ hZ n y θs hn b a hyab hbB hbs hbC a₀ Ga ha hGa Ke hKe
      hpos hval cm hcm hmar hTBe hTBq hAd hUH hFb hKb hΩF hΩK Kθ hKθ hθK hphys
  have hposH : ∀ M ∈ H.Ke, 0 < Matrix.det (show Mat from M) := by rw [hHK]; exact hpos
  have hcH : H.c ≤ 1 / 64 := by rw [hHc']; exact hcm
  have hfKH : ∀ k z, NativeTrigRec.recon (coframeM (y (φ k))) z ∈ H.Ke := by
    rw [hHK]; exact fun k => hfK (φ k)
  obtain ⟨ψ, hψ, P, S, u₀, hlim, -, hPK, hDH, hid1, -, htot, -, -, -, -⟩ :=
    NativeTrigRec.native_reconstructed_closure_trig_bank D₀ Tj hθ hκ hw Θ Θ' H hposH hcH hF
      (fun k => hUH (φ k)) (BH := BH) (fun k => hHb (φ k)) hK (fun k => hU (φ k)) (B := B)
      (fun k => hΨ (φ k)) (fun k => hKs (φ k)) (fun k => hΨb (φ k)) (fun k => hKbd (φ k)) hG
      hfKH
  have hφψ : StrictMono (fun k => φ (ψ k)) := hφ.comp hψ
  set H' := coHypSubseq H hψ with hH'
  have hθ' : BankConv (fun k => θs (φ (ψ k))) θ :=
    ⟨hθ.κ.comp hψ.tendsto_atTop, hθ.Λ.comp hψ.tendsto_atTop, hθ.lamH.comp hψ.tendsto_atTop,
      hθ.vH.comp hψ.tendsto_atTop, fun j => (hθ.w j).comp hψ.tendsto_atTop,
      hθ.Y.comp hψ.tendsto_atTop⟩
  refine ⟨fun k => φ (ψ k), hφψ, H', hHK, θ, hθ', F, G, P, S, u₀,
    fun μ ν => (hF μ ν).comp_strictMono hψ, fun μ ν => (hG μ ν).comp_strictMono hψ, hFG,
    by rw [hPK]; exact hDH, hid1, hlim, htot, fun hstat τ => ?_, ?_⟩
  · refine euler_of_limit (fun k => bankData D₀ Tj (θs (φ (ψ k)))) (κid 𝓢) _ (hlim) ?_ τ
    intro ε hε
    exact (hstat ε hε).filter_mono hφψ.tendsto_atTop |>.mono fun k hk => hk
  · intro ΘF ΘK ΘV hΘF hΘK hΘV
    have he : LpTendsto volume 2 (fun k => pc (coframeM (y (φ (ψ k))))) H.e₀ := H'.he
    have hfK' : ∀ k z, pc (coframeM (y (φ (ψ k)))) z ∈ Ke := fun k z => hval _ _
    have hFp : LpTendsto volume 2 (fun k => pc (curvPacket (n (φ (ψ k))) (y (φ (ψ k)))))
        (fun z μ ν => F μ ν z) :=
      LpTendsto.pi fun μ => LpTendsto.pi fun ν => (hF μ ν).comp_strictMono hψ
    have hKp : LpTendsto volume 2 (fun k => pc (higgsPacket D₀ (n (φ (ψ k))) (y (φ (ψ k)))))
        (fun z μ => P.K₀ μ z) :=
      LpTendsto.pi fun μ => by rw [hPK]; exact (hK μ).comp_strictMono hψ
    have T1 := lpTendsto_chart_quadratic hKe he hfK' hΘF hFp
    have T2 := lpTendsto_chart_quadratic hKe he hfK' hΘK hKp
    have hpot := lpTendsto_potential_seq (D₀.hermH) (hθ'.lamH) (hθ'.vH) P.hH
    have T3 := NativeReconstructed.chart (p := 1) ENNReal.one_ne_top hKe he hfK' hΘV
      (ContinuousLinearMap.mul ℝ ℝ) hpot
    refine ((T1.add T2).add T3).congr (fun k => Eventually.of_forall fun z => ?_)
      (Eventually.of_forall fun z => ?_)
    · simp only [Pi.add_apply, ContinuousLinearMap.mul_apply', potential, bankData]
    · simp only [Pi.add_apply, ContinuousLinearMap.mul_apply', potential, bankData]
      rfl

end Criterion

/-! ### Non-vacuity -/

section NonVacuity

open ShiftedJetAction (Grid)

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

/-- **Non-vacuity of the background hypotheses, with a large background**: a constant real
potential `a ≡ c` (for any `c`, e.g. with `|c| ‖Z‖` far above the critical ball) satisfies the
strong `L⁴` / first-difference hypotheses of `combined_extraction_core` (limits `c` and `0`). -/
theorem const_background_hyps (n : ℕ → ℕ) [∀ k, NeZero (n k)] (c : ℝ) :
    (∀ _μ : Fin 4, LpTendsto volume 4 (fun k => pc (fun _ : Grid (n k) => c)) (fun _ : 𝕋 => c)) ∧
    (∀ μ ν : Fin 4, LpTendsto volume 2
      (fun k => pc (NativeHiggs.DpV μ (fun _ : Grid (n k) => c))) (fun _ : 𝕋 => (0 : ℝ))) := by
  refine ⟨fun _ => (LpTendsto.const (memLp_const c)).congr (fun k => Eventually.of_forall
    fun z => rfl) (Eventually.of_forall fun z => rfl), fun μ _ => ?_⟩
  refine (LpTendsto.const (memLp_const (0 : ℝ))).congr (fun k => Eventually.of_forall
    fun z => ?_) (Eventually.of_forall fun z => rfl)
  simp [pc, NativeHiggs.DpV]

/-- Non-vacuity of the semisimple hypotheses: the zero semisimple part (constant, commuting,
bounded) has the compactness property `BCompact` (`bCompact_of_const`). -/
example (n : ℕ → ℕ) [∀ k, NeZero (n k)] (hn : Tendsto n atTop atTop) :
    BCompact (𝔄 := ℂ) n (fun k μ (_ : Grid (n k)) => (fun (_ : ℕ) (_ : Fin 4) => (0 : ℂ)) k μ) :=
  (bCompact_of_const n hn (fun _ _ => (0 : ℂ)) (fun _ _ _ => Commute.zero_left _)
    (Mβ := 0) (fun _ _ => by simp)).2.2

end NonVacuity

end

end RenewalGeometry.DeterminantResolved
