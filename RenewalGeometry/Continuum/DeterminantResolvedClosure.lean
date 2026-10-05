/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.DeterminantResolvedExtraction
import RenewalGeometry.Continuum.FiniteWilsonZeroDefectClosure
import RenewalGeometry.Continuum.DeterminantNormalizationSequence
import RenewalGeometry.GaugeTheory.FlatSemisimpleNormalization

/-!
# Determinant-resolved finite Wilson closure (`cor:determinant-resolved-closure`)

Einstein–SM action-closure manuscript, subsection "Determinant-resolved closure".  The gauge
group is `G_SM = S(U(3) × U(2)) ⊂ M₃(ℂ) × M₂(ℂ)` (`NativeRecordNormSM.GSM`), with the central
direction `Z_c = (-i/3 I₃, i/2 I₂)` (`DeterminantSplit.Zc`).

* `cUg hZs s = e^{s Z}` for a central skew-adjoint `Z` (for `Z = Z_c` in `G_SM`,
  `cUg_Zc_mem_GSM`); `splitVg hZs h t a U`, the remainder
  `V_μ(x) = e^{-h a_μ(x) Z} e^{t(x) Z} U_μ(x) e^{-t(x+μ) Z}` of `eq:determinant-exact-split`
  (`DeterminantSplit.splitLinks` in matrix form);
* `gaugeLinks_splitVg`, `exp_combined_splitVg`: normalizing `V` by a site gauge `g` normalizes the
  actual links by the total gauge `g e^{tZ}` up to the central factor `e^{haZ}`: the normalized
  actual links are exactly `e^{h b} e^{h a Z} = e^{h(b + a Z)}`
  (`eq:determinant-combined-connection`);
* the bridge from the record encoding of `(F3)` to the screened sequence of
  `DeterminantScreenFlux.CurvatureScreen`, so that `DeterminantNormalizationSequence.
  precompact_sequence` gives the strong compactness of the determinant coordinates `a_h`;
* `determinant_resolved_closure_SM` (**`cor:determinant-resolved-closure`**, certificate form)
  and `determinant_resolved_closure_flat_SM` (exact-flatness alternative).
-/

open NormedSpace Finset Filter Topology Set MeasureTheory
open scoped BigOperators RealInnerProductSpace ENNReal

namespace RenewalGeometry.DeterminantResolvedSM

open scoped Matrix.Norms.L2Operator
open StandardModelCoulomb (SMAlg toESM detSM)

noncomputable section

set_option linter.unusedSectionVars false

/-! ### Central unitary phases in a C*-algebra -/

section Central

variable {𝔄 : Type*} [CStarAlgebra 𝔄] {Z : 𝔄}

theorem star_exp_smul_of_skew (hZs : star Z = -Z) (s : ℝ) :
    star (exp (s • Z)) = exp ((-s) • Z) := by
  rw [star_exp, star_smul, hZs, star_trivial, smul_neg, neg_smul]

theorem exp_smul_mem_unitary_of_skew (hZs : star Z = -Z) (s : ℝ) : exp (s • Z) ∈ unitary 𝔄 := by
  rw [Unitary.mem_iff, star_exp_smul_of_skew hZs, DeterminantCombined.exp_smul_mul_exp_smul,
    DeterminantCombined.exp_smul_mul_exp_smul, neg_add_cancel, add_neg_cancel, zero_smul,
    exp_zero]
  exact ⟨rfl, rfl⟩

/-- **The central unitary phase** `e^{sZ}` for a skew-adjoint `Z`. -/
def cUg (hZs : star Z = -Z) (s : ℝ) : unitary 𝔄 := ⟨exp (s • Z), exp_smul_mem_unitary_of_skew hZs s⟩

@[simp] theorem coe_cUg (hZs : star Z = -Z) (s : ℝ) :
    ((cUg hZs s : unitary 𝔄) : 𝔄) = exp (s • Z) := rfl

theorem cUg_central (hZs : star Z = -Z) (hZc : ∀ X : 𝔄, Commute X Z) (s : ℝ) (X : 𝔄) :
    Commute ((cUg hZs s : unitary 𝔄) : 𝔄) X :=
  ((hZc X).symm.smul_left s).exp_left

end Central

/-! ### The semisimple remainder and the combined normalization -/

section Split

open ShiftedJetAction (Grid unitVec)
open RootedCoulomb (latSrc latTgt)
open GridSobolev (gridStep)

variable {𝔄 : Type*} [CStarAlgebra 𝔄] [Nontrivial 𝔄] {Z : 𝔄}
variable {N : ℕ} [NeZero N]

/-- **The remainder of the central split** (matrix form of `DeterminantSplit.splitLinks`, for a
general central skew-adjoint direction `Z`): with site phases `t` and the potential `a`,
`V_μ(x) = e^{-h a_μ(x) Z} · e^{t(x) Z} U_μ(x) e^{-t(x+μ) Z}`. -/
def splitVg (hZs : star Z = -Z) (h : ℝ) (t : Grid N → ℝ) (a : Fin 4 → Grid N → ℝ)
    (U : Grid N × Fin 4 → unitary 𝔄) : Grid N × Fin 4 → unitary 𝔄 :=
  fun e => cUg hZs (-(h * a e.2 e.1)) *
    (cUg hZs (t e.1) * U e * star (cUg hZs (t (e.1 + gridStep e.2))))

theorem splitVg_mem (hZs : star Z = -Z) (K : Subgroup (unitary 𝔄)) (hZK : ∀ s, cUg hZs s ∈ K)
    (h : ℝ) (t : Grid N → ℝ) (a : Fin 4 → Grid N → ℝ) {U : Grid N × Fin 4 → unitary 𝔄}
    (hU : ∀ e, U e ∈ K) (e : Grid N × Fin 4) : splitVg hZs h t a U e ∈ K :=
  K.mul_mem (hZK _) (K.mul_mem (K.mul_mem (hZK _) (hU e)) (K.inv_mem (hZK _)))

/-- The total gauge `g_x e^{t(x) Z}`. -/
def totGauge (hZs : star Z = -Z) (g : Grid N → unitary 𝔄) (t : Grid N → ℝ) :
    Grid N → unitary 𝔄 :=
  fun x => g x * cUg hZs (t x)

theorem totGauge_mem (hZs : star Z = -Z) (K : Subgroup (unitary 𝔄)) (hZK : ∀ s, cUg hZs s ∈ K)
    {g : Grid N → unitary 𝔄} (hg : ∀ x, g x ∈ K) (t : Grid N → ℝ) (x : Grid N) :
    totGauge hZs g t x ∈ K :=
  K.mul_mem (hg x) (hZK _)

/-- **Normalizing the remainder normalizes the actual links up to the central factor**:
`g_x V_μ(x) g_{x+μ}^* = e^{-h a_μ(x) Z} · (g e^{tZ})_x U_μ(x) (g e^{tZ})_{x+μ}^*`. -/
theorem gaugeLinks_splitVg (hZs : star Z = -Z) (hZc : ∀ X : 𝔄, Commute X Z) (h : ℝ)
    (t : Grid N → ℝ) (a : Fin 4 → Grid N → ℝ) (U : Grid N × Fin 4 → unitary 𝔄)
    (g : Grid N → unitary 𝔄) (x : Grid N) (μ : Fin 4) :
    ((gaugeLinks latSrc latTgt g (splitVg hZs h t a U) (x, μ) : unitary 𝔄) : 𝔄) =
      exp ((-(h * a μ x)) • Z) *
        ((gaugeLinks latSrc latTgt (totGauge hZs g t) U (x, μ) : unitary 𝔄) : 𝔄) := by
  simp only [gaugeLinks_apply, latSrc, latTgt, splitVg, totGauge, Submonoid.coe_mul,
    RootedCoulomb.coe_inv_unitary, star_mul, coe_cUg, Unitary.coe_star]
  have hc : Commute ((g x : unitary 𝔄) : 𝔄) (exp ((-(h * a μ x)) • Z)) :=
    (cUg_central hZs hZc (-(h * a μ x)) _).symm
  rw [← mul_assoc ((g x : unitary 𝔄) : 𝔄), hc.eq]
  simp only [mul_assoc]

/-- **The normalized actual links are `e^{h(b + aZ)}`**, `b = h⁻¹ Log(g V g^*)`
(`eq:determinant-combined-connection`). -/
theorem exp_combined_splitVg (hZs : star Z = -Z) (hZc : ∀ X : 𝔄, Commute X Z) {h : ℝ}
    (hh : h ≠ 0) (t : Grid N → ℝ) (a : Fin 4 → Grid N → ℝ) (U : Grid N × Fin 4 → unitary 𝔄)
    (g : Grid N → unitary 𝔄) (x : Grid N) (μ : Fin 4)
    (hch : ‖((gaugeLinks latSrc latTgt g (splitVg hZs h t a U) (x, μ) : unitary 𝔄) : 𝔄) - 1‖
      < 1) :
    exp (h • (h⁻¹ • SeriesLogChart.logChart
        ((gaugeLinks latSrc latTgt g (splitVg hZs h t a U) (x, μ) : unitary 𝔄) : 𝔄) +
        a μ x • Z)) =
      ((gaugeLinks latSrc latTgt (totGauge hZs g t) U (x, μ) : unitary 𝔄) : 𝔄) := by
  set W := ((gaugeLinks latSrc latTgt g (splitVg hZs h t a U) (x, μ) : unitary 𝔄) : 𝔄)
  set T := ((gaugeLinks latSrc latTgt (totGauge hZs g t) U (x, μ) : unitary 𝔄) : 𝔄)
  have hW : W = exp ((-(h * a μ x)) • Z) * T := gaugeLinks_splitVg hZs hZc h t a U g x μ
  have hT : Commute T (exp ((h * a μ x) • Z)) := (cUg_central hZs hZc (h * a μ x) T).symm
  rw [DeterminantCombined.exp_combined h (a μ x) (hZc _), smul_smul,
    mul_inv_cancel₀ hh, one_smul, SeriesLogChart.exp_logChart hch, hW, mul_assoc, hT.eq,
    ← mul_assoc, DeterminantCombined.exp_smul_mul_exp_smul, neg_add_cancel, zero_smul, exp_zero,
    one_mul]

/-- Variant of `exp_combined_splitVg` for any `B` with `e^{hB} = g V g^*`. -/
theorem exp_combined_splitVg' (hZs : star Z = -Z) (hZc : ∀ X : 𝔄, Commute X Z) {h : ℝ}
    (t : Grid N → ℝ) (a : Fin 4 → Grid N → ℝ) (U : Grid N × Fin 4 → unitary 𝔄)
    (g : Grid N → unitary 𝔄) (x : Grid N) (μ : Fin 4) (B : 𝔄)
    (hB : exp (h • B) = ((gaugeLinks latSrc latTgt g (splitVg hZs h t a U) (x, μ) :
      unitary 𝔄) : 𝔄)) :
    exp (h • (B + a μ x • Z)) =
      ((gaugeLinks latSrc latTgt (totGauge hZs g t) U (x, μ) : unitary 𝔄) : 𝔄) := by
  set T := ((gaugeLinks latSrc latTgt (totGauge hZs g t) U (x, μ) : unitary 𝔄) : 𝔄)
  have hW := gaugeLinks_splitVg hZs hZc h t a U g x μ
  have hT : Commute T (exp ((h * a μ x) • Z)) := (cUg_central hZs hZc (h * a μ x) T).symm
  rw [DeterminantCombined.exp_combined h (a μ x) (hZc _), hB, hW, mul_assoc, hT.eq,
    ← mul_assoc, DeterminantCombined.exp_smul_mul_exp_smul, neg_add_cancel, zero_smul, exp_zero,
    one_mul]

end Split

/-! ### `Z_c` in `M₃(ℂ) × M₂(ℂ)` -/

section SMCentral

/-- `Z_c = (-i/3 I₃, i/2 I₂)` in the pair algebra. -/
abbrev Zc : SMAlg := DeterminantSplit.Zc

theorem Zc_central (X : SMAlg) : Commute X Zc := (DeterminantCombined.commute_Zc X).symm

theorem star_Zc : star Zc = -Zc := by
  refine Prod.ext ?_ ?_
  · change star (-(Complex.I / 3) • (1 : Matrix (Fin 3) (Fin 3) ℂ)) =
      -(-(Complex.I / 3) • (1 : Matrix (Fin 3) (Fin 3) ℂ))
    rw [star_smul, star_one, star_neg, star_div₀, Complex.star_def, Complex.conj_I, map_ofNat,
      neg_div, neg_smul]
  · change star ((Complex.I / 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) =
      -((Complex.I / 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ))
    rw [star_smul, star_one, star_div₀, Complex.star_def, Complex.conj_I, map_ofNat, neg_div,
      neg_smul]

theorem trace_smul_Zc (s : ℝ) : (s • Zc).1.trace + (s • Zc).2.trace = 0 := by
  have h := DeterminantCombined.trace_Zc
  simp only [Prod.smul_fst, Prod.smul_snd, Matrix.trace_smul]
  change s • Matrix.trace (DeterminantSplit.Zc.1) + s • Matrix.trace DeterminantSplit.Zc.2 = 0
  rw [← smul_add, h, smul_zero]

/-- `e^{s Z_c} ∈ G_SM`. -/
theorem cUg_Zc_mem_GSM (s : ℝ) : cUg star_Zc s ∈ NativeRecordNormSM.GSM :=
  NativeRecordNormSM.mem_GSM.2 (StandardModelCoulomb.detSM_exp (trace_smul_Zc s))

end SMCentral

/-! ### From the record encoding to the screened sequence of `lem:determinant-screen-flux` -/

section Bridge

open ShiftedJetAction (Grid unitVec)
open NativeDensity
open SMDescentYukawa (smU3 smU2 smChi)
open DeterminantScreenFlux (toOp ofOp PairIdx Packet)
open TorusPiecewiseConstantTranslation (gridNorm)

/-- An element of `G_SM ⊂ U(M₃(ℂ) × M₂(ℂ))` as an element of `SMGaugeGroup`. -/
def toSMG (u : unitary SMAlg) (hu : u ∈ NativeRecordNormSM.GSM) : SMGaugeGroup :=
  ⟨(⟨(u : SMAlg).1, StandardModelCoulomb.fst_mem_unitary u.2⟩,
    ⟨(u : SMAlg).2, StandardModelCoulomb.snd_mem_unitary u.2⟩), by
    refine MonoidHom.mem_ker.2 (Subtype.ext ?_)
    have := NativeRecordNormSM.mem_GSM.1 hu
    simpa [determinantProductHom, unitaryDetHom, detSM] using this⟩

@[simp] theorem smU3_toSMG (u : unitary SMAlg) (hu) : smU3 (toSMG u hu) = (u : SMAlg).1 := rfl
@[simp] theorem smU2_toSMG (u : unitary SMAlg) (hu) : smU2 (toSMG u hu) = (u : SMAlg).2 := rfl

theorem smU3_inv' (g : SMGaugeGroup) : smU3 g⁻¹ = star (smU3 g) := rfl
theorem smU2_inv' (g : SMGaugeGroup) : smU2 g⁻¹ = star (smU2 g) := rfl

/-- The restriction of a full packet `(Y_{μν})_{μ,ν}` to the oriented pairs `μ < ν`. -/
def restr (Y : Fin 4 → Fin 4 → SMAlg) : Packet := fun p => toOp (Y p.1.1 p.1.2)

theorem norm_restr_le (Y : Fin 4 → Fin 4 → SMAlg) : ‖restr Y‖ ≤ ‖Y‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun p => ?_
  exact (norm_le_pi_norm (Y p.1.1) p.1.2).trans (norm_le_pi_norm Y p.1.1)

variable {rH : ℕ} [NeZero rH]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
  [FiniteDimensional ℝ 𝓢]
variable {N : ℕ} [NeZero N]

/-- `e^{-hA} = (e^{hA})^*` for unitary links. -/
theorem exp_neg_eq_star_of_links {y : Grid N → Field SMAlg (EuclideanSpace ℝ (Fin rH)) 𝓢}
    {U : Grid N × Fin 4 → unitary SMAlg}
    (hUe : ∀ x μ, (U (x, μ) : SMAlg) = exp ((N : ℝ)⁻¹ • gauge y μ x)) (x : Grid N) (μ : Fin 4) :
    exp (-((N : ℝ)⁻¹ • gauge y μ x)) = star (U (x, μ) : SMAlg) := by
  rw [hUe]
  exact FiniteWilsonClosure.exp_neg_eq_star (by rw [← hUe]; exact (U (x, μ)).2)

/-- The adjoint links of the two encodings agree on restricted packets. -/
theorem adLinks_restr {y : Grid N → Field SMAlg (EuclideanSpace ℝ (Fin rH)) 𝓢}
    {U : Grid N × Fin 4 → unitary SMAlg} (hUK : ∀ e, U e ∈ NativeRecordNormSM.GSM)
    (hUe : ∀ x μ, (U (x, μ) : SMAlg) = exp ((N : ℝ)⁻¹ • gauge y μ x))
    (hAd : ∀ x μ (X : SMAlg), ‖exp ((N : ℝ)⁻¹ • gauge y μ x) * X *
      exp (-((N : ℝ)⁻¹ • gauge y μ x))‖ = ‖X‖) (μ : Fin 4) (x : Grid N)
    (w : Fin 4 → Fin 4 → SMAlg) :
    DeterminantScreenFlux.adLinks (fun x μ => toSMG (U (x, μ)) (hUK (x, μ))) μ x (restr w) =
      restr (FiniteWilsonZeroDefect.adLinks N y hAd μ x w) := by
  funext p
  change toOp ((U (x, μ) : SMAlg).1 * (w p.1.1 p.1.2).1 * star ((U (x, μ) : SMAlg).1),
    (U (x, μ) : SMAlg).2 * (w p.1.1 p.1.2).2 * star ((U (x, μ) : SMAlg).2)) =
    toOp (exp ((N : ℝ)⁻¹ • gauge y μ x) * w p.1.1 p.1.2 * exp (-((N : ℝ)⁻¹ • gauge y μ x)))
  rw [exp_neg_eq_star_of_links hUe, ← hUe]
  rfl

/-- The open links of the two encodings agree on restricted packets. -/
theorem openLink_restr {y : Grid N → Field SMAlg (EuclideanSpace ℝ (Fin rH)) 𝓢}
    {U : Grid N × Fin 4 → unitary SMAlg} (hUK : ∀ e, U e ∈ NativeRecordNormSM.GSM)
    (hUe : ∀ x μ, (U (x, μ) : SMAlg) = exp ((N : ℝ)⁻¹ • gauge y μ x))
    (hAd : ∀ x μ (X : SMAlg), ‖exp ((N : ℝ)⁻¹ • gauge y μ x) * X *
      exp (-((N : ℝ)⁻¹ • gauge y μ x))‖ = ‖X‖) (μ : Fin 4) (m : ℕ) :
    ∀ (x : Grid N) (w : Fin 4 → Fin 4 → SMAlg),
    NativeWilsonCompactness.openLink
        (DeterminantScreenFlux.adLinks (fun x μ => toSMG (U (x, μ)) (hUK (x, μ)))) μ m x
        (restr w) =
      restr (FiniteWilsonZeroDefect.openLinkR (FiniteWilsonZeroDefect.adLinks N y hAd) μ m x w) := by
  induction m with
  | zero => intro x w; rfl
  | succ m ih =>
      intro x w
      rw [NativeWilsonCompactness.openLink, FiniteWilsonZeroDefect.openLinkR,
        LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.trans_apply, ih,
        adLinks_restr hUK hUe hAd]

/-- The Wilson differences of the two encodings agree on restricted packets. -/
theorem wilsonShift_restr {y : Grid N → Field SMAlg (EuclideanSpace ℝ (Fin rH)) 𝓢}
    {U : Grid N × Fin 4 → unitary SMAlg} (hUK : ∀ e, U e ∈ NativeRecordNormSM.GSM)
    (hUe : ∀ x μ, (U (x, μ) : SMAlg) = exp ((N : ℝ)⁻¹ • gauge y μ x))
    (hAd : ∀ x μ (X : SMAlg), ‖exp ((N : ℝ)⁻¹ • gauge y μ x) * X *
      exp (-((N : ℝ)⁻¹ • gauge y μ x))‖ = ‖X‖) (μ : Fin 4) (m : ℕ)
    (Y : Grid N → Fin 4 → Fin 4 → SMAlg) (x : Grid N) :
    (NativeWilsonCompactness.wilsonShift
        (DeterminantScreenFlux.adLinks (fun x μ => toSMG (U (x, μ)) (hUK (x, μ)))) μ m
        (fun x => restr (Y x)) - fun x => restr (Y x)) x =
      restr ((FiniteWilsonZeroDefect.wilsonShiftR (FiniteWilsonZeroDefect.adLinks N y hAd) μ m
        Y - Y) x) := by
  simp only [Pi.sub_apply, NativeWilsonCompactness.wilsonShift,
    FiniteWilsonZeroDefect.wilsonShiftR]
  rw [openLink_restr hUK hUe hAd]
  rfl

/-- The chart logarithms of the full plaquettes. -/
def plaqLog (y : Grid N → Field SMAlg (EuclideanSpace ℝ (Fin rH)) 𝓢) (x : Grid N) (μ ν : Fin 4) :
    DeterminantSplit.LiePair :=
  SeriesLogChart.logChart (NativeScaling.gaugePlaquette (N : ℝ)⁻¹ (gauge y) x μ ν)

theorem curvPacket_restr (y : Grid N → Field SMAlg (EuclideanSpace ℝ (Fin rH)) 𝓢) (x : Grid N) :
    DeterminantScreenFlux.curvPacket (1 / (N : ℝ)) (plaqLog y) x =
      restr (FiniteWilsonZeroDefect.curvPacket N y x) := by
  funext p
  simp only [DeterminantScreenFlux.curvPacket, restr, FiniteWilsonZeroDefect.curvPacket,
    NativeScaling.fieldStrength, plaqLog, one_div]
  congr 1

end Bridge

/-! ### The screened sequence -/

section Screen

open ShiftedJetAction (Grid unitVec)
open NativeDensity
open SMDescentYukawa (smU3 smU2 smChi)
open DeterminantScreenFlux (toOp ofOp PairIdx Packet)
open TorusPiecewiseConstantTranslation (gridNorm)

variable {rH : ℕ} [NeZero rH]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
  [FiniteDimensional ℝ 𝓢]

theorem fst_exp_SM (Y : SMAlg) : (exp Y).1 = exp Y.1 := by
  letI : NormedAlgebra ℚ (Matrix (Fin 3) (Fin 3) ℂ) := NormedAlgebra.restrictScalars ℚ ℝ _
  letI : NormedAlgebra ℚ (Matrix (Fin 2) (Fin 2) ℂ) := NormedAlgebra.restrictScalars ℚ ℝ _
  convert Prod.fst_exp Y using 2

theorem snd_exp_SM (Y : SMAlg) : (exp Y).2 = exp Y.2 := by
  letI : NormedAlgebra ℚ (Matrix (Fin 3) (Fin 3) ℂ) := NormedAlgebra.restrictScalars ℚ ℝ _
  letI : NormedAlgebra ℚ (Matrix (Fin 2) (Fin 2) ℂ) := NormedAlgebra.restrictScalars ℚ ℝ _
  convert Prod.snd_exp Y using 2

variable {N : ℕ} [NeZero N]

/-- The full plaquette of the record is the literal plaquette of its unitary links, in the
`SMGaugeGroup` encoding. -/
theorem gaugePlaquette_eq_plaqSMG {y : Grid N → Field SMAlg (EuclideanSpace ℝ (Fin rH)) 𝓢}
    {U : Grid N × Fin 4 → unitary SMAlg} (hUK : ∀ e, U e ∈ NativeRecordNormSM.GSM)
    (hUe : ∀ x μ, (U (x, μ) : SMAlg) = exp ((N : ℝ)⁻¹ • gauge y μ x)) (x : Grid N) (μ ν : Fin 4) :
    (NativeScaling.gaugePlaquette (N : ℝ)⁻¹ (gauge y) x μ ν).1 =
        smU3 (DeterminantSplit.plaq DeterminantFlux.gridShift
          (fun x μ => toSMG (U (x, μ)) (hUK (x, μ))) x μ ν) ∧
      (NativeScaling.gaugePlaquette (N : ℝ)⁻¹ (gauge y) x μ ν).2 =
        smU2 (DeterminantSplit.plaq DeterminantFlux.gridShift
          (fun x μ => toSMG (U (x, μ)) (hUK (x, μ))) x μ ν) := by
  simp only [NativeScaling.gaugePlaquette, exp_neg_eq_star_of_links hUe, ← hUe,
    DeterminantSplit.plaq, map_mul, smU3_inv', smU2_inv', smU3_toSMG, smU2_toSMG, Prod.fst_mul,
    Prod.snd_mul, Prod.fst_star, Prod.snd_star]
  exact ⟨rfl, rfl⟩

set_option maxHeartbeats 1600000 in
-- the encoding bridge for the full screen
/-- **The record form of `(F3)` (curvature part) gives the screened sequence of
`lem:determinant-screen-flux`** (box side `L = 1`): unitary `G_SM` links `U_h = e^{hA_h}` with
plaquettes in the logarithm chart, a bounded literal curvature packet and a vanishing adjoint
Wilson screen define a `DeterminantScreenFlux.CurvatureScreen`, with the chart logarithms of the
full plaquettes. -/
theorem curvatureScreen_of_records (n : ℕ → ℕ) [∀ k, NeZero (n k)] (hn : Tendsto n atTop atTop)
    (y : ∀ k, Grid (n k) → Field SMAlg (EuclideanSpace ℝ (Fin rH)) 𝓢)
    (U : ∀ k, Grid (n k) × Fin 4 → unitary SMAlg) (hUK : ∀ k e, U k e ∈ NativeRecordNormSM.GSM)
    (hUe : ∀ k x μ, (U k (x, μ) : SMAlg) = exp ((n k : ℝ)⁻¹ • gauge (y k) μ x))
    (hP : ∀ k x μ ν, ‖NativeScaling.gaugePlaquette (n k : ℝ)⁻¹ (gauge (y k)) x μ ν - 1‖ < 1)
    (hAd : ∀ k x μ (X : SMAlg), ‖exp ((n k : ℝ)⁻¹ • gauge (y k) μ x) * X *
        exp (-((n k : ℝ)⁻¹ • gauge (y k) μ x))‖ = ‖X‖)
    (hFb : ∃ B, ∀ k, gridNorm (FiniteWilsonZeroDefect.curvPacket (n k) (y k)) ≤ B)
    (hΩF : ∀ ε > 0, ∃ ρ > 0, ∀ᶠ k in atTop, ∀ (μ : Fin 4) (m : ℕ), 0 < m → (m : ℝ) / n k ≤ ρ →
      gridNorm (FiniteWilsonZeroDefect.wilsonShiftR (FiniteWilsonZeroDefect.adLinks (n k) (y k)
        (hAd k)) μ m (FiniteWilsonZeroDefect.curvPacket (n k) (y k)) -
          FiniteWilsonZeroDefect.curvPacket (n k) (y k)) ≤ ε) :
    DeterminantScreenFlux.CurvatureScreen 1 n
      (fun k x μ => toSMG (U k (x, μ)) (hUK k (x, μ))) (fun k => plaqLog (y k)) where
  pos := one_pos
  tendsto := hn
  exp_fst k x μ ν _ := by
    rw [plaqLog, ← fst_exp_SM, SeriesLogChart.exp_logChart (hP k x μ ν)]
    exact (gaugePlaquette_eq_plaqSMG (hUK k) (hUe k) x μ ν).1
  exp_snd k x μ ν _ := by
    rw [plaqLog, ← snd_exp_SM, SeriesLogChart.exp_logChart (hP k x μ ν)]
    exact (gaugePlaquette_eq_plaqSMG (hUK k) (hUe k) x μ ν).2
  bdd := by
    obtain ⟨B, hB⟩ := hFb
    refine ⟨B, fun k => ?_⟩
    rw [DeterminantScreenFlux.gridL2Norm_eq_gridNorm one_pos, one_pow, one_mul]
    refine le_trans ?_ (hB k)
    refine TorusPiecewiseConstantTranslation.gridNorm_mono fun x => ?_
    rw [curvPacket_restr]
    exact norm_restr_le _
  screen := by
    intro ε hε
    obtain ⟨ρ, hρ, hev⟩ := hΩF ε hε
    refine ⟨ρ, hρ, hev.mono fun k hk μ m hm hmρ => ?_⟩
    rw [DeterminantScreenFlux.gridL2Norm_eq_gridNorm one_pos, one_pow, one_mul]
    have hmρ' : (m : ℝ) / n k ≤ ρ := by rw [div_eq_mul_one_div]; exact hmρ
    refine le_trans ?_ (hk μ m hm hmρ')
    refine TorusPiecewiseConstantTranslation.gridNorm_mono fun x => ?_
    have e : DeterminantScreenFlux.curvPacket (1 / (n k : ℝ)) (plaqLog (y k)) =
        fun x => restr (FiniteWilsonZeroDefect.curvPacket (n k) (y k) x) :=
      funext (curvPacket_restr (y k))
    rw [e, wilsonShift_restr (hUK k) (hUe k) (hAd k)]
    exact norm_restr_le _

end Screen

/-! ### The determinant coordinates -/

section Potential

open ShiftedJetAction (Grid unitVec)
open NativeDensity
open TorusPiecewiseConstantTranslation (gridNorm pc)

local notation "𝕋" => UnitAddTorus (Fin 4)

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- **The determinant coordinates** `a_h = a⁰_h + c_h` (`prop:periodic-determinant-normalization`,
unit side): the paper's potential `a⁰ = δ_h Δ_h^† f` of the determinant links `χ(U) = det U₂`,
plus the cycle constants `c_h`. -/
def detCoord (N : ℕ) [NeZero N] (U : Grid N × Fin 4 → unitary SMAlg) (c : Fin 4 → ℝ) :
    Fin 4 → Grid N → ℝ :=
  fun μ x => DeterminantFlux.detPotential (fun x μ => ((U (x, μ) : SMAlg).2).det) (1 / (N : ℝ)) x μ +
    c μ

theorem detCoord_eq (N : ℕ) [NeZero N] (U : Grid N × Fin 4 → unitary SMAlg)
    (hUK : ∀ e, U e ∈ NativeRecordNormSM.GSM) (c : Fin 4 → ℝ) :
    detCoord N U c = fun μ x => DeterminantFlux.detPotential
      (fun x μ => SMDescentYukawa.smChi (toSMG (U (x, μ)) (hUK (x, μ)))) (1 / (N : ℝ)) x μ + c μ :=
  rfl

/-- **The determinant coordinates are co-closed** (`δ_h a = 0`) once the determinant curvature
is closed with zero plane means. -/
theorem gridDiv_detCoord (N : ℕ) [NeZero N] (U : Grid N × Fin 4 → unitary SMAlg) (c : Fin 4 → ℝ)
    (hcl : ∀ x μ ν κ, GridHodge.cubeSum (DeterminantFlux.detCurvature
      (fun x μ => ((U (x, μ) : SMAlg).2).det) (1 / (N : ℝ))) x μ ν κ = 0)
    (hm : ∀ μ ν, ∑ x, DeterminantFlux.detCurvature
      (fun x μ => ((U (x, μ) : SMAlg).2).det) (1 / (N : ℝ)) x μ ν = 0)
    (x : Grid N) : DeterminantFlux.gridDiv (fun x μ => detCoord N U c μ x) x = 0 := by
  simp only [detCoord]
  rw [DeterminantFlux.gridDiv_add_const, DeterminantFlux.gridDiv_eq_div]
  have e : GridHodge.div (DeterminantFlux.detPotential (fun x μ => ((U (x, μ) : SMAlg).2).det)
      (1 / (N : ℝ))) x = (1 / (N : ℝ)) * GridHodge.div (GridHodge.hodgePrimitive
        (DeterminantFlux.detCurvature (fun x μ => ((U (x, μ) : SMAlg).2).det) (1 / (N : ℝ)))) x := by
    simp only [GridHodge.div, DeterminantFlux.detPotential, GridHodge.scaledPrimitive,
      Finset.mul_sum, mul_sub]
  rw [e, GridHodge.hodgePrimitive_div _ hcl hm, mul_zero]

/-- Under the screen and zero flux, the determinant coordinates are eventually co-closed. -/
theorem eventually_gridDiv_detCoord {n : ℕ → ℕ} [∀ k, NeZero (n k)]
    {U : ∀ k, Grid (n k) × Fin 4 → unitary SMAlg} (hUK : ∀ k e, U k e ∈ NativeRecordNormSM.GSM)
    {Lg : ∀ k, (Fin 4 → ZMod (n k)) → Fin 4 → Fin 4 → DeterminantSplit.LiePair}
    (S : DeterminantScreenFlux.CurvatureScreen 1 n
      (fun k x μ => toSMG (U k (x, μ)) (hUK k (x, μ))) Lg)
    (hflux : ∀ᶠ k in atTop, ∀ μ ν,
      DeterminantFlux.planeFlux (fun x μ => ((U k (x, μ) : SMAlg).2).det) 0 μ ν = 0)
    (c : ℕ → Fin 4 → ℝ) :
    ∀ᶠ k in atTop, ∀ x, DeterminantFlux.gridDiv (fun x μ => detCoord (n k) (U k) (c k) μ x) x = 0 := by
  filter_upwards [S.eventually_phase_small 1 one_pos, hflux] with k hk hf x
  obtain ⟨hcl, hm⟩ := DeterminantFlux.detCurvature_closed_meanZero
    (fun x μ => SMDescentYukawa.smChi (toSMG (U k (x, μ)) (hUK k (x, μ))))
    (fun x μ => DeterminantFlux.norm_smChi _)
    (fun x μ ν => (hk x μ ν).trans_lt (by linarith [Real.pi_gt_three])) hf (1 / (n k : ℝ))
  exact gridDiv_detCoord (n k) (U k) (c k) hcl hm x

/-- **Strong compactness of the determinant coordinates** (`prop:periodic-determinant-
normalization`, sequence clauses, record encoding): under the curvature screen and zero
determinant flux, for constants `|c_{h,μ}| ≤ π`, every subsequence has a further subsequence along
which `R_h^0 a_h → a₀` strongly in `L⁴` and `R_h^0 D⁺_μ a_{h,ν} → G^a_{μν}` strongly in `L²`. -/
theorem detCoord_precompact {n : ℕ → ℕ} [∀ k, NeZero (n k)]
    {U : ∀ k, Grid (n k) × Fin 4 → unitary SMAlg} (hUK : ∀ k e, U k e ∈ NativeRecordNormSM.GSM)
    {Lg : ∀ k, (Fin 4 → ZMod (n k)) → Fin 4 → Fin 4 → DeterminantSplit.LiePair}
    (S : DeterminantScreenFlux.CurvatureScreen 1 n
      (fun k x μ => toSMG (U k (x, μ)) (hUK k (x, μ))) Lg)
    (hflux : ∀ᶠ k in atTop, ∀ μ ν,
      DeterminantFlux.planeFlux (fun x μ => ((U k (x, μ) : SMAlg).2).det) 0 μ ν = 0)
    (c : ℕ → Fin 4 → ℝ) (hc : ∀ k μ, |c k μ| ≤ Real.pi) (ψ : ℕ → ℕ)
    (hψ : Tendsto ψ atTop atTop) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ (a₀ : Fin 4 → 𝕋 → ℝ) (Ga : Fin 4 → Fin 4 → 𝕋 → ℝ),
      (∀ μ, LpTendsto volume 4 (fun k => pc (detCoord (n (ψ (φ k))) (U (ψ (φ k))) (c (ψ (φ k))) μ))
        (a₀ μ)) ∧
      (∀ μ ν, LpTendsto volume 2 (fun k => pc (NativeHiggs.DpV μ
        (detCoord (n (ψ (φ k))) (U (ψ (φ k))) (c (ψ (φ k))) ν))) (Ga μ ν)) := by
  obtain ⟨φ, hφ, A, hA⟩ := DeterminantNormalizationSequence.precompact_sequence S hflux c
    (fun k μ => by rw [one_mul]; exact hc k μ) ψ hψ
  refine ⟨φ, hφ, fun μ z => (A μ z).re, fun μ ν z => (TorusSobolev.weakDeriv μ (A ν) z).re,
    fun μ => ?_, fun μ ν => ?_⟩
  · obtain ⟨hmem, hconv, -⟩ := hA μ
    have hL : LpTendsto volume 4 (fun k => pc (DeterminantNormalizationSequence.unitCoord 1
        (fun k x μ => toSMG (U k (x, μ)) (hUK k (x, μ))) c (ψ (φ k)) μ)) (A μ : 𝕋 → ℂ) :=
      ⟨fun k => NativeYMIdentification.memLp_pc_gen _ 4, hmem, hconv⟩
    refine (hL.clm Complex.reCLM).congr (fun k => Eventually.of_forall fun z => ?_)
      (Eventually.of_forall fun z => rfl)
    simp only [pc, DeterminantNormalizationSequence.unitCoord, Complex.reCLM_apply,
      Complex.ofReal_re, one_mul, detCoord, one_div]
    rfl
  · obtain ⟨-, -, -, hD, -⟩ := hA ν
    have hL := (NativeGridLp.lpTendsto_of_norm_pcLp (hD μ)).clm Complex.reCLM
    refine hL.congr (fun k => Eventually.of_forall fun z => ?_)
      (Eventually.of_forall fun z => rfl)
    simp only [pc, Complex.reCLM_apply, TorusTrigReconstruction.Dp_apply, NativeHiggs.DpV,
      DeterminantNormalizationSequence.unitCoord, detCoord, one_mul, one_div, smul_eq_mul]
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_sub, ← Complex.ofReal_mul, Complex.ofReal_re]
    rfl

end Potential

/-! ### Generic lemmas for the assembly -/

section AssemblyLemmas

open ShiftedJetAction (Grid unitVec)
open TorusPiecewiseConstantTranslation (pc)

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance : (volume : Measure UnitAddCircle).IsAddHaarMeasure :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

/-- The unit torus `𝕋⁴`. -/
local notation "𝕋" => UnitAddTorus (Fin 4)

/-- **`h ‖a_h‖_∞ → 0`** for a family of potentials that is strongly precompact in `L⁴` (along
every subsequence there is a further strongly convergent one). -/
theorem tendsto_meshSup_of_precompact {n : ℕ → ℕ} [∀ k, NeZero (n k)]
    (hn : Tendsto n atTop atTop) (a : ∀ k, Fin 4 → Grid (n k) → ℝ)
    (ha : ∀ ψ : ℕ → ℕ, Tendsto ψ atTop atTop → ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ (a₀ : Fin 4 → 𝕋 → ℝ) (Ga : Fin 4 → Fin 4 → 𝕋 → ℝ),
        (∀ μ, LpTendsto volume 4 (fun k => pc (a (ψ (φ k)) μ)) (a₀ μ)) ∧
        (∀ μ ν, LpTendsto volume 2 (fun k => pc (NativeHiggs.DpV μ (a (ψ (φ k)) ν))) (Ga μ ν)))
    (μ : Fin 4) : Tendsto (fun k => NativeCriticalGrid.meshSup (a k μ)) atTop (𝓝 0) := by
  refine tendsto_of_subseq_tendsto fun ψ hψ => ?_
  obtain ⟨φ, hφ, a₀, -, h4, -⟩ := ha ψ hψ
  exact ⟨φ, NativeCriticalGrid.tendsto_meshSup (n := fun k => n (ψ (φ k)))
    (hn.comp (hψ.comp hφ.tendsto_atTop)) (h4 μ).memLp_lim (h4 μ).tendsto⟩

theorem eventually_mesh_le_of_precompact {n : ℕ → ℕ} [∀ k, NeZero (n k)]
    (hn : Tendsto n atTop atTop) (a : ∀ k, Fin 4 → Grid (n k) → ℝ)
    (ha : ∀ ψ : ℕ → ℕ, Tendsto ψ atTop atTop → ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ (a₀ : Fin 4 → 𝕋 → ℝ) (Ga : Fin 4 → Fin 4 → 𝕋 → ℝ),
        (∀ μ, LpTendsto volume 4 (fun k => pc (a (ψ (φ k)) μ)) (a₀ μ)) ∧
        (∀ μ ν, LpTendsto volume 2 (fun k => pc (NativeHiggs.DpV μ (a (ψ (φ k)) ν))) (Ga μ ν)))
    {δ : ℝ} (hδ : 0 < δ) : ∀ᶠ k in atTop, ∀ μ x, (n k : ℝ)⁻¹ * |a k μ x| ≤ δ := by
  have hev : ∀ μ, ∀ᶠ k in atTop, NativeCriticalGrid.meshSup (a k μ) < δ := fun μ =>
    (tendsto_meshSup_of_precompact hn a ha μ).eventually (gt_mem_nhds hδ)
  filter_upwards [eventually_all.2 hev] with k hk μ x
  have := NativeCriticalGrid.le_meshSup (a k μ) x
  rw [Real.norm_eq_abs] at this
  exact this.trans (hk μ).le

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℂ 𝔄]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The codifferential of the combined connection**:
`δ_h T(b + aZ) = δ_h T b - (N · δ a) T Z` with the integer divergence `δ a = Σ_μ (a_μ - T_{-μ}a_μ)`
of `DeterminantFlux.gridDiv`. -/
theorem codiffT_combined (T : 𝔄 →L[ℝ] E) {N : ℕ} [NeZero N] (b : Fin 4 → Grid N → 𝔄)
    (a : Fin 4 → Grid N → ℝ) (Z : 𝔄) (x : Grid N) :
    NativeCoulomb.codiffT T (fun x μ => b μ x + a μ x • Z) x =
      NativeCoulomb.codiffT T (fun x μ => b μ x) x -
        ((N : ℝ) * DeterminantFlux.gridDiv (fun x μ => a μ x) x) • T Z := by
  simp only [NativeCoulomb.codiffT, periodicHodgeCodiff, periodicHodgeBwd, DeterminantFlux.gridDiv,
    map_add, map_smul, inv_inv, Finset.mul_sum, Finset.sum_smul]
  rw [← sub_eq_zero]
  simp only [smul_sub, smul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib, mul_sub,
    sub_smul, smul_smul, GridSobolev.gridStep, DeterminantFlux.unitStep]
  abel

end AssemblyLemmas

/-! ### The determinant-resolved closure, generic assembly -/

section Assembly

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance : (volume : Measure UnitAddCircle).IsAddHaarMeasure :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

/-- The unit torus `𝕋⁴`. -/
local notation "𝕋" => UnitAddTorus (Fin 4)

open ShiftedJetAction (Grid unitVec)
open NativeScaling (Mat)
open NativeDensity NativeGauge NativeLinkCov NativeBank
open NativeDiracLimit (DTest testRec samp Dif)
open NativeGravityFirstJet (M4 liftM coframeM)
open NativeSpinorGraph (κid spinGraph dualGraph)
open TorusPiecewiseConstantTranslation KolmogorovRieszTorus
open NativeHiggsVar NativeDiracConvergence FiniteWilsonZeroDefect FiniteWilsonClosure
open NativeDiracConv (CoHyp qM ωM)

variable {𝔄 : Type*} [CStarAlgebra 𝔄] [Nontrivial 𝔄] [FiniteDimensional ℝ 𝔄]
variable {rH : ℕ} [NeZero rH]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
  [FiniteDimensional ℝ 𝓢]
variable {E E₀ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [NormedAddCommGroup E₀]
  [InnerProductSpace ℝ E₀] [Nontrivial E₀] [FiniteDimensional ℝ E₀]
variable {r r' : ℕ} [NeZero r] [NeZero r'] {J : ℕ}

local instance fact_one_le_two_drc : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

set_option maxHeartbeats 12800000 in
-- the transfer of the hypotheses and the combined criterion
/-- **`cor:determinant-resolved-closure`, assembly after the normalization of the remainder**
(generic).  The normalization `g_h V_h g_h^* = e^{h b_h}` of the remainder, with `g_h ∈ K`, `b_h`
bounded in `L²_h`, eventually `h ‖b_h‖_∞ ≤ 1/1024`, and the compactness property
`DeterminantResolved.BCompact`, is a hypothesis here; it is supplied by the rooted certificate
(`determinant_resolved_of_rootedNorm`) or by exact flatness.  Conclusions as in
`determinant_resolved_of_rootedNorm`.  The rest of this docstring describes that theorem:
**`cor:determinant-resolved-closure`, generic assembly** (unit-torus rendering, mesh
`h = 1/N`; gauge group `K ⊆ U(𝔄)` with the rooted Coulomb normalization property `RootedNorm`,
invariant metric `toE`; a central skew-adjoint direction `Z` whose phases `e^{sZ}` lie in `K`).
There are cutoff-independent `ε_c, ε_* > 0` such that, for native records with unitary links
`U_h = e^{hA_h} ∈ K` whose plaquettes are in the logarithm chart, and **central-split data**
(site phases `t_h`, real potentials `a_h` that are strongly precompact in `L⁴` with strongly
precompact first differences — the determinant normalization — **with no smallness**), if the
remainder `V_h = e^{-h a_h Z} e^{t_h Z} U_h e^{-t_h Z}` (`splitVg`) has an admissible rooted seed,
plaquettes in the chart and rooted certificate `≤ ε_c` (`eq:semisimple-only-certificate`), then
under `(F1)`, `(F3)`, `(F4)`, `(F5)` of `thm:finite-Wilson-zero-defect` there are actual site
gauges `g_h ∈ K` (`g_h = q_h e^{t_h Z}`, `q_h` the rooted normalization of `V_h`) acting on the
same records, the normalized logarithmic connection is exactly `A'_h = b_h + a_h Z`
(`eq:determinant-combined-connection`) with `δ_h b_h = 0` and `‖b_h‖_{4,h} ≤ ε_*` — **only `b_h`
lies in the small critical ball** — and, after extraction, all the convergence and variational
conclusions of `thm:finite-Wilson-zero-defect` hold (`eq:Wilson-strong-convergence`,
`eq:native-all-sector-limit` with the cutoff banks, the reconstructed-field consistency, the
distributional Einstein–Standard-Model equations, strong `L¹` convergence of the bosonic stress
densities). -/
theorem determinant_resolved_post (C₀ : CovData 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢)
    (K : Subgroup (unitary 𝔄)) (hG : ∀ u ∈ K, Unitary.toUnits u ∈ C₀.G)
    (hρH : ∀ k ∈ C₀.G, ∀ v : EuclideanSpace ℝ (Fin rH), ‖C₀.ρH k v‖ = ‖v‖)
    (Tj : Fin J → 𝔄 →L[ℝ] E)
    (hT : ∀ g ∈ C₀.G, ∀ j (X Y : 𝔄),
      ⟪Tj j ((g : 𝔄) * X * ↑g⁻¹), Tj j ((g : 𝔄) * Y * ↑g⁻¹)⟫ = ⟪Tj j X, Tj j Y⟫)
    (M : MassMetric 𝔄 (EuclideanSpace ℝ (Fin rH))) (hM : M.Invariant C₀)
    (Θ : 𝓢 ≃L[ℝ] EuclideanSpace ℝ (Fin r)) (Θ' : CoSpinor 𝓢 ≃L[ℝ] EuclideanSpace ℝ (Fin r'))
    {Z : 𝔄} (hZs : star Z = -Z) (hZc : ∀ X : 𝔄, Commute X Z) (hZK : ∀ s, cUg hZs s ∈ K) :
    ∀ (n : ℕ → ℕ) [∀ k, NeZero (n k)]
      (y : ∀ k, Grid (n k) → Field 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢)
      (θs : ℕ → Bank J (EuclideanSpace ℝ (Fin rH)) 𝓢), Tendsto n atTop atTop →
      -- the unitary internal links of the records, in the logarithm chart
      ∀ (U : ∀ k, Grid (n k) × Fin 4 → unitary 𝔄)
        (hUe : ∀ k x μ, (U k (x, μ) : 𝔄) = exp ((n k : ℝ)⁻¹ • NativeDensity.gauge (y k) μ x))
        (hUK : ∀ k e, U k e ∈ K),
      (∀ k μ ν x, ‖RootedCoulomb.litPlaq (U k) μ ν x - 1‖ < 1) →
      -- the central-split data
      ∀ (t : ∀ k, Grid (n k) → ℝ) (a : ∀ k, Fin 4 → Grid (n k) → ℝ),
      (∀ ψ : ℕ → ℕ, Tendsto ψ atTop atTop → ∃ φ : ℕ → ℕ, StrictMono φ ∧
        ∃ (a₀ : Fin 4 → 𝕋 → ℝ) (Ga : Fin 4 → Fin 4 → 𝕋 → ℝ),
          (∀ μ, LpTendsto volume 4 (fun k => pc (a (ψ (φ k)) μ)) (a₀ μ)) ∧
          (∀ μ ν, LpTendsto volume 2 (fun k => pc (NativeHiggs.DpV μ (a (ψ (φ k)) ν)))
            (Ga μ ν))) →
      -- the normalization of the remainder: `g V g^* = e^{h b}`
      ∀ (gV : ∀ k, Grid (n k) → unitary 𝔄) (b : ∀ k, Fin 4 → Grid (n k) → 𝔄),
      (∀ k x, gV k x ∈ K) →
      (∀ k μ x, exp ((n k : ℝ)⁻¹ • b k μ x) = ((gaugeLinks RootedCoulomb.latSrc
        RootedCoulomb.latTgt (gV k) (splitVg hZs (n k : ℝ)⁻¹ (t k) (a k) (U k)) (x, μ) :
          unitary 𝔄) : 𝔄)) →
      (∃ MB, ∀ k μ, gridNorm (b k μ) ≤ MB) →
      (∀ᶠ k in atTop, ∀ μ x, (n k : ℝ)⁻¹ * ‖b k μ x‖ ≤ 1 / 1024) →
      DeterminantResolved.BCompact n b →
      -- `(F1)`
      ∀ (Ke : Set M4), IsCompact Ke → (∀ M ∈ Ke, 0 < Matrix.det (show Mat from M)) →
      (∀ k x, coframeM (y k) x ∈ Ke) → ∀ cm : ℝ, cm ≤ 1 / 64 →
      (∀ k x μ, (n k : ℝ)⁻¹ * ‖ωM (y k) μ x‖ ≤ cm) →
      TotallyBounded (range fun k => pcLp (coframeM (y k))) →
      TotallyBounded (range fun k => pcLp (fun x lam => qM (y k) lam x)) →
      (∀ k z, NativeTrigRec.recon (coframeM (y k)) z ∈ Ke) →
      -- `(F3)`
      (∃ B, ∀ k, gridNorm (curvPacket (n k) (y k)) ≤ B) →
      (∃ B, ∀ k, gridNorm (higgsPacket C₀.toData (n k) (y k)) ≤ B) →
      ∀ BH : ℝ, (∀ k, gridNorm (higgs (y k)) ≤ BH) →
      (∀ ε > 0, ∃ ρ > 0, ∀ᶠ k in atTop, ∀ (μ : Fin 4) (m : ℕ), 0 < m → (m : ℝ) / n k ≤ ρ →
        gridNorm (wilsonShiftR (adLinks (n k) (y k) (adUnit_of_links (hUe k))) μ m
          (curvPacket (n k) (y k)) - curvPacket (n k) (y k)) ≤ ε) →
      (∀ ε > 0, ∃ ρ > 0, ∀ᶠ k in atTop, ∀ (μ : Fin 4) (m : ℕ), 0 < m → (m : ℝ) / n k ≤ ρ →
        gridNorm (wilsonShiftR (higgsLinks C₀.toData (n k) (y k)
            (higgsUnit_of_links C₀ K hG hρH (hUe k) (hUK k))) μ m
          (higgsPacket C₀.toData (n k) (y k)) - higgsPacket C₀.toData (n k) (y k)) ≤ ε) →
      -- `(F4)`
      ∀ B : ℝ, (∀ k, gridNorm (psi (y k)) ≤ B) →
      (∀ k μ, gridNorm (fun x => spinGraph C₀.toData (n k : ℝ)⁻¹ (y k) x μ) ≤ B) →
      (∀ k, gridNorm (psiBar (y k)) ≤ B) →
      (∀ k μ, gridNorm (fun x => dualGraph C₀.toData (n k : ℝ)⁻¹ (y k) x μ) ≤ B) →
      ∀ (Kθ : Set (ℝ × ℝ × ℝ × ℝ × (Fin J → ℝ) ×
          (EuclideanSpace ℝ (Fin rH) →L[ℝ] Spin 𝓢))), IsCompact Kθ →
      (∀ k, bankVec (θs k) ∈ Kθ) → (∀ v ∈ Kθ, v.1 ≠ 0 ∧ ∀ j, 0 ≤ v.2.2.2.2.1 j) →
      ∀ (hY : ∀ k, ∀ g ∈ C₀.G, ∀ H : EuclideanSpace ℝ (Fin rH),
        (θs k).Y (C₀.ρH g H) = C₀.ρS g * (θs k).Y H * C₀.ρS ↑g⁻¹),
      -- `(F5)`
      Tendsto (fun k => covNormP (bankCov C₀ Tj (θs k) hT (hY k)) M (n k : ℝ)⁻¹
        (toLinks (n k : ℝ)⁻¹ (y k))) atTop (𝓝 0) →
      ∃ g : ∀ k, Grid (n k) → 𝔄ˣ, ∃ y' : ∀ k, Grid (n k) → Field 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢,
      (∀ k x, ∃ u ∈ K, g k x = Unitary.toUnits u) ∧
      (∀ k, IsGaugeTransform C₀ (n k : ℝ)⁻¹ (g k) (y k) (y' k)) ∧
      -- `eq:determinant-combined-connection`
      (∀ k μ x, NativeDensity.gauge (y' k) μ x = b k μ x + a k μ x • Z) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ H : CoHyp (fun k => n (φ k)) (fun k => y' (φ k)),
      H.Ke = Ke ∧
      ∃ θ : Bank J (EuclideanSpace ℝ (Fin rH)) 𝓢, BankConv (fun k => θs (φ k)) θ ∧
      ∃ F : Fin 4 → Fin 4 → 𝕋 → 𝔄, ∃ G : Fin 4 → Fin 4 → 𝕋 → 𝔄,
      ∃ P : HiggsHyp (bankData C₀.toData Tj θ) (fun k => y' (φ k)),
      ∃ S : SpinHyp (κid 𝓢) (fun k => y' (φ k)), ∃ u₀ : 𝕋 → Dif 𝓢 (CoSpinor 𝓢),
      -- `eq:Wilson-strong-convergence`
      (∀ μ ν, LpTendsto volume 2 (fun k => pc (fun x =>
        NativeScaling.fieldStrength (n (φ k) : ℝ)⁻¹ (NativeDensity.gauge (y' (φ k))) x μ ν))
        (F μ ν)) ∧
      (∀ μ ν, LpTendsto volume 2
        (fun k => pc (NativeHiggs.DpV μ (NativeDensity.gauge (y' (φ k)) ν))) (G μ ν)) ∧
      (∀ μ ν, F μ ν =ᵐ[MeasureTheory.volume] NativeReconstructed.recCurv H.A₀ G μ ν) ∧
      (∀ μ, LpTendsto volume 2 (fun k => pc (NativeHiggs.DpV μ (higgs (y' (φ k)))))
        (fun z => P.K₀ μ z - C₀.ρHL (H.A₀ μ z) (P.H₀ z))) ∧
      (∀ j, ∃ fj : Lp ℂ 2 (MeasureTheory.volume : Measure 𝕋),
        ((fj : 𝕋 → ℂ) =ᵐ[MeasureTheory.volume] fun z => ((Θ (S.Ψ₀ z) j : ℝ) : ℂ)) ∧
        TorusSobolev.MemH 1 fj ∧ ∀ μ, (TorusSobolev.weakDeriv μ fj : 𝕋 → ℂ)
          =ᵐ[MeasureTheory.volume] fun z => ((Θ ((u₀ z).1 μ) j : ℝ) : ℂ)) ∧
      -- `eq:native-all-sector-limit` with the cutoff banks
      (∀ M : NNReal, ∀ ε > 0, ∀ᶠ k in atTop,
        ∀ τ : DTest 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢 (CoSpinor 𝓢), τ.norm ≤ M →
        |NativeAllSector.nativeVar (bankData C₀.toData Tj (θs (φ k))) (n (φ k)) (y' (φ k))
            (testRec (κid 𝓢) (n (φ k)) (y' (φ k)) τ) -
          NativeAllSector.contAllVar (bankData C₀.toData Tj θ) (κid 𝓢) (bankT Tj θ.w) H F P S u₀
            τ| ≤ ε) ∧
      -- consistency relative to the reconstructed fields
      (∀ M : NNReal, ∀ ε > 0, ∀ᶠ k in atTop,
        ∀ τ : DTest 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢 (CoSpinor 𝓢), τ.norm ≤ M →
        |NativeAllSector.nativeVar (bankData C₀.toData Tj (θs (φ k))) (n (φ k)) (y' (φ k))
            (testRec (κid 𝓢) (n (φ k)) (y' (φ k)) τ) -
          NativeReconstructed.recAllVar (bankData C₀.toData Tj θ) (κid 𝓢) (bankT Tj θ.w)
            (NativeTrigRec.recon (coframeM (y' (φ k))))
            (fun lam => NativeTrigRec.drecon lam (coframeM (y' (φ k))))
            (fun μ => NativeTrigRec.recon (NativeDensity.gauge (y' (φ k)) μ))
            (fun μ ν => NativeTrigRec.drecon μ (NativeDensity.gauge (y' (φ k)) ν))
            (NativeTrigRec.recon (higgs (y' (φ k))))
            (fun μ => NativeTrigRec.drecon μ (higgs (y' (φ k))))
            (NativeTrigRec.recon (psi (y' (φ k)))) (NativeTrigRec.recon (psiBar (y' (φ k))))
            (NativeTrigRec.recJets (y' (φ k))) τ| ≤ ε) ∧
      -- the distributional Einstein–Standard-Model equations
      (∀ τ : DTest 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢 (CoSpinor 𝓢),
        NativeAllSector.contAllVar (bankData C₀.toData Tj θ) (κid 𝓢) (bankT Tj θ.w) H F P S u₀ τ
          = 0) ∧
      -- the bosonic stress densities
      (∀ (ΘF : M4 → (Fin 4 → Fin 4 → 𝔄) →L[ℝ] (Fin 4 → Fin 4 → 𝔄) →L[ℝ] ℝ)
        (ΘK : M4 → (Fin 4 → EuclideanSpace ℝ (Fin rH)) →L[ℝ]
          (Fin 4 → EuclideanSpace ℝ (Fin rH)) →L[ℝ] ℝ) (ΘV : M4 → ℝ),
        ContinuousOn ΘF Ke → ContinuousOn ΘK Ke → ContinuousOn ΘV Ke →
        LpTendsto volume 1
          (fun k z => ΘF (pc (coframeM (y' (φ k))) z) (pc (curvPacket (n (φ k)) (y' (φ k))) z)
              (pc (curvPacket (n (φ k)) (y' (φ k))) z) +
            ΘK (pc (coframeM (y' (φ k))) z)
              (pc (higgsPacket C₀.toData (n (φ k)) (y' (φ k))) z)
              (pc (higgsPacket C₀.toData (n (φ k)) (y' (φ k))) z) +
            ΘV (pc (coframeM (y' (φ k))) z) *
              potential (bankData C₀.toData Tj (θs (φ k))) (pc (higgs (y' (φ k))) z))
          (fun z => ΘF (H.e₀ z) (fun μ ν => F μ ν z) (fun μ ν => F μ ν z) +
            ΘK (H.e₀ z) (fun μ => P.K₀ μ z) (fun μ => P.K₀ μ z) +
            ΘV (H.e₀ z) * potential (bankData C₀.toData Tj θ) (P.H₀ z))) := by
  intro n _ y θs hn U hUe hUK hplaq t a ha gV b hgVK hWb hbB hbs hbC Ke hKe hpos hval cm hcm
    hmar hTBe hTBq hrec hFb hKb BH hHb hΩF hΩK B hΨ hKs hΨb hKbd Kθ hKθ hθK hphys hY hF5
  have hNpos : ∀ k, (0 : ℝ) < (n k : ℝ)⁻¹ := fun k =>
    inv_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (n k)))
  set gt : ∀ k, Grid (n k) → unitary 𝔄 := fun k => totGauge hZs (gV k) (t k) with hgtdef
  have hgtK : ∀ k x, gt k x ∈ K := fun k x =>
    totGauge_mem hZs K hZK (fun x => hgVK k x) (t k) x
  set g : ∀ k, Grid (n k) → 𝔄ˣ := fun k x => Unitary.toUnits (gt k x) with hgdef
  have hgG : ∀ k x, g k x ∈ C₀.G := fun k x => hG _ (hgtK k x)
  set y' : ∀ k, Grid (n k) → Field 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢 := fun k x =>
    (coframe (y k) x, fun μ => b k μ x + a k μ x • Z, C₀.ρH (g k x) (higgs (y k) x),
      C₀.ρS (g k x) (psi (y k) x), (psiBar (y k) x).comp (C₀.ρS ↑(g k x)⁻¹)) with hy'def
  have hgauge : ∀ k μ x, NativeDensity.gauge (y' k) μ x = b k μ x + a k μ x • Z :=
    fun k μ x => rfl
  have hexp : ∀ k μ x, exp ((n k : ℝ)⁻¹ • NativeDensity.gauge (y' k) μ x) =
      ((gaugeLinks RootedCoulomb.latSrc RootedCoulomb.latTgt (gt k) (U k) (x, μ) :
        unitary 𝔄) : 𝔄) := fun k μ x =>
    exp_combined_splitVg' hZs hZc (t k) (a k) (U k) (gV k) x μ (b k μ x) (hWb k μ x)
  have hIG : ∀ k, IsGaugeTransform C₀ (n k : ℝ)⁻¹ (g k) (y k) (y' k) := by
    intro k
    refine ⟨hgG k, ?_⟩
    refine LinkConfig.ext rfl ?_ rfl rfl rfl
    funext μ x
    change exp ((n k : ℝ)⁻¹ • NativeDensity.gauge (y' k) μ x) =
      ((gt k x : unitary 𝔄) : 𝔄) * exp ((n k : ℝ)⁻¹ • NativeDensity.gauge (y k) μ x) *
        star ((gt k (x + unitVec (n k) μ) : unitary 𝔄) : 𝔄)
    rw [hexp, gaugeLinks_apply, ← hUe]
    rfl
  -- transfer of `(F1)`
  have hcf : ∀ k, coframe (y' k) = coframe (y k) := fun k =>
    FiniteWilsonTransfer.coframe_eq C₀ (hIG k)
  have hcfM : ∀ k, coframeM (y' k) = coframeM (y k) := fun k => by
    unfold coframeM; rw [hcf k]
  have hωM : ∀ k μ x, ωM (y' k) μ x = ωM (y k) μ x := fun k μ x => by
    unfold ωM; rw [hcf k]
  have hqM : ∀ k lam x, qM (y' k) lam x = qM (y k) lam x := fun k lam x => by
    unfold qM; rw [hcf k]
  have hval' : ∀ k x, coframeM (y' k) x ∈ Ke := fun k x => by rw [hcfM]; exact hval k x
  -- the plaquette chart of the original links
  have hP : ∀ k x μ ν, ‖plaq (toLinks (n k : ℝ)⁻¹ (y k)) x μ ν - 1‖ < 1 := fun k x μ ν => by
    rw [plaq_eq_litPlaq (hUe k)]; exact hplaq k μ ν x
  -- unitarity of the normalized links
  have hAd' := fun k => FiniteWilsonTransfer.adUnit_gauge C₀ (hIG k) (adUnit_of_links (hUe k))
  have hUH' := fun k => FiniteWilsonTransfer.higgsUnit_gauge C₀ hρH (hIG k)
    (higgsUnit_of_links C₀ K hG hρH (hUe k) (hUK k))
  have hU' := fun k => FiniteWilsonTransfer.spinUnit_gauge C₀ (hIG k)
    (spinUnit_of_links C₀ K hG (hUe k) (hUK k))
  -- transfer of `(F3)`, `(F4)`
  obtain ⟨BF, hBF⟩ := hFb
  obtain ⟨BK, hBK⟩ := hKb
  have hFb' : ∃ B, ∀ k, gridNorm (curvPacket (n k) (y' k)) ≤ B := ⟨BF, fun k => by
    rw [FiniteWilsonTransfer.gridNorm_curvPacket_gauge C₀ (hIG k) (hP k)]; exact hBF k⟩
  have hKb' : ∃ B, ∀ k, gridNorm (higgsPacket C₀.toData (n k) (y' k)) ≤ B := ⟨BK, fun k => by
    rw [FiniteWilsonTransfer.gridNorm_higgsPacket_gauge C₀ hρH (hIG k)]; exact hBK k⟩
  have hHb' : ∀ k, gridNorm (higgs (y' k)) ≤ BH := fun k => by
    rw [FiniteWilsonTransfer.gridNorm_higgs_gauge C₀ hρH (hIG k)]; exact hHb k
  have hΩF' : ∀ ε > 0, ∃ ρ > 0, ∀ᶠ k in atTop, ∀ (μ : Fin 4) (m : ℕ), 0 < m →
      (m : ℝ) / n k ≤ ρ → gridNorm (wilsonShiftR (adLinks (n k) (y' k) (hAd' k)) μ m
        (curvPacket (n k) (y' k)) - curvPacket (n k) (y' k)) ≤ ε := by
    intro ε hε
    obtain ⟨ρ, hρ, hev⟩ := hΩF ε hε
    refine ⟨ρ, hρ, hev.mono fun k hk μ m hm hmρ => ?_⟩
    rw [FiniteWilsonTransfer.gridNorm_wilson_curv_gauge C₀ (hIG k) (hP k)
      (adUnit_of_links (hUe k)) (hAd' k)]
    exact hk μ m hm hmρ
  have hΩK' : ∀ ε > 0, ∃ ρ > 0, ∀ᶠ k in atTop, ∀ (μ : Fin 4) (m : ℕ), 0 < m →
      (m : ℝ) / n k ≤ ρ → gridNorm (wilsonShiftR (higgsLinks C₀.toData (n k) (y' k) (hUH' k))
        μ m (higgsPacket C₀.toData (n k) (y' k)) - higgsPacket C₀.toData (n k) (y' k)) ≤ ε := by
    intro ε hε
    obtain ⟨ρ, hρ, hev⟩ := hΩK ε hε
    refine ⟨ρ, hρ, hev.mono fun k hk μ m hm hmρ => ?_⟩
    rw [FiniteWilsonTransfer.gridNorm_wilson_higgs_gauge C₀ hρH (hIG k)
      (higgsUnit_of_links C₀ K hG hρH (hUe k) (hUK k)) (hUH' k)]
    exact hk μ m hm hmρ
  have hΨ' : ∀ k, gridNorm (psi (y' k)) ≤ B := fun k => by
    rw [FiniteWilsonTransfer.gridNorm_psi_gauge C₀ (hIG k)]; exact hΨ k
  have hKs' : ∀ k μ, gridNorm (fun x => spinGraph C₀.toData (n k : ℝ)⁻¹ (y' k) x μ) ≤ B :=
    fun k μ => by rw [FiniteWilsonTransfer.gridNorm_spinGraph_gauge C₀ (hIG k)]; exact hKs k μ
  have hΨb' : ∀ k, gridNorm (psiBar (y' k)) ≤ B := fun k => by
    rw [FiniteWilsonTransfer.gridNorm_psiBar_gauge C₀ (hIG k)]; exact hΨb k
  have hKbd' : ∀ k μ, gridNorm (fun x => dualGraph C₀.toData (n k : ℝ)⁻¹ (y' k) x μ) ≤ B :=
    fun k μ => by rw [FiniteWilsonTransfer.gridNorm_dualGraph_gauge C₀ (hIG k)]; exact hKbd k μ
  have hTBe' : TotallyBounded (range fun k => pcLp (coframeM (y' k))) := by
    simp only [hcfM]; exact hTBe
  have hTBq' : TotallyBounded (range fun k => pcLp (fun x lam => qM (y' k) lam x)) := by
    simp only [hqM]; exact hTBq
  have hrec' : ∀ k z, NativeTrigRec.recon (coframeM (y' k)) z ∈ Ke := fun k z => by
    rw [hcfM]; exact hrec k z
  -- the subsequence along which the potentials converge
  obtain ⟨φ₀, hφ₀, a₀, Ga, ha4, hGa⟩ := ha id tendsto_id
  have hn₀ : Tendsto (fun k => n (φ₀ k)) atTop atTop := hn.comp hφ₀.tendsto_atTop
  obtain ⟨MB, hMB⟩ := hbB
  have hev₀ : ∀ {P : ℕ → Prop}, (∀ᶠ k in atTop, P k) → ∀ᶠ k in atTop, P (φ₀ k) :=
    fun h => hφ₀.tendsto_atTop.eventually h
  obtain ⟨φ', hφ', H, hHK, θ, hθ, F, G, P, S, u₀, c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ :=
    DeterminantResolved.combined_criterion_core (J := J) C₀.toData Tj Θ Θ' hZc
      (fun k => n (φ₀ k)) (fun k => y' (φ₀ k)) (fun k => θs (φ₀ k)) hn₀
      (fun k => b (φ₀ k)) (fun k => a (φ₀ k)) (fun k μ x => hgauge (φ₀ k) μ x)
      ⟨MB, fun k μ => hMB (φ₀ k) μ⟩
      ((hφ₀.tendsto_atTop.eventually hbs).mono fun k hk μ x => (hk μ x).trans (by norm_num))
      (hbC.comp hφ₀) a₀ Ga
      ha4 hGa Ke hKe hpos (fun k => hval' (φ₀ k)) cm hcm
      (fun k x μ => by rw [hωM]; exact hmar (φ₀ k) x μ)
      (totallyBounded_comp hTBe' φ₀) (totallyBounded_comp hTBq' φ₀)
      (fun k => hAd' (φ₀ k)) (fun k => hUH' (φ₀ k))
      (let ⟨B', hB'⟩ := hFb'; ⟨B', fun k => hB' (φ₀ k)⟩)
      (let ⟨B', hB'⟩ := hKb'; ⟨B', fun k => hB' (φ₀ k)⟩) BH (fun k => hHb' (φ₀ k))
      (fun ε hε => let ⟨ρ, hρ, hev⟩ := hΩF' ε hε; ⟨ρ, hρ, hev₀ hev⟩)
      (fun ε hε => let ⟨ρ, hρ, hev⟩ := hΩK' ε hε; ⟨ρ, hρ, hev₀ hev⟩)
      (fun k => hU' (φ₀ k)) B (fun k => hΨ' (φ₀ k)) (fun k => hKs' (φ₀ k))
      (fun k => hΨb' (φ₀ k)) (fun k => hKbd' (φ₀ k)) Kθ hKθ (fun k => hθK (φ₀ k)) hphys
      (fun k => hrec' (φ₀ k))
  -- `(F5)` ⟹ native stationarity
  obtain ⟨Kl, hKl0, hKl⟩ := exists_liftM_bound hKe
  have has : ∀ᶠ k in atTop, ∀ μ x, (n k : ℝ)⁻¹ * |a k μ x| ≤ 1 / 1024 / (‖Z‖ + 1) :=
    eventually_mesh_le_of_precompact hn a ha (by positivity)
  have hA512 : ∀ᶠ k in atTop, ∀ μ x,
      (n k : ℝ)⁻¹ * ‖NativeDensity.gauge (y' k) μ x‖ ≤ 1 / 512 := by
    filter_upwards [has, hbs] with k hk hkb μ x
    rw [hgauge]
    have h1 := hkb μ x
    have h2 := hk μ x
    have h3 : (n k : ℝ)⁻¹ * |a k μ x| * ‖Z‖ ≤ 1 / 1024 := by
      calc (n k : ℝ)⁻¹ * |a k μ x| * ‖Z‖ ≤ 1 / 1024 / (‖Z‖ + 1) * ‖Z‖ :=
            mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
        _ ≤ 1 / 1024 := by
            rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
            nlinarith [norm_nonneg Z]
    calc (n k : ℝ)⁻¹ * ‖b k μ x + a k μ x • Z‖ ≤
          (n k : ℝ)⁻¹ * ‖b k μ x‖ + (n k : ℝ)⁻¹ * |a k μ x| * ‖Z‖ := by
          rw [mul_assoc, ← mul_add]
          refine mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (le_of_eq ?_))
            (hNpos k).le
          rw [norm_smul (a k μ x) Z, Real.norm_eq_abs]
      _ ≤ 1 / 512 := by linarith
  have hstat : ∀ ε > 0, ∀ᶠ k in atTop,
      ∀ τ : DTest 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢 (CoSpinor 𝓢), τ.norm ≤ 1 →
      |NativeAllSector.nativeVar (bankData C₀.toData Tj (θs k)) (n k) (y' k)
        (testRec (κid 𝓢) (n k) (y' k) τ)| ≤ ε := by
    intro ε hε
    set s := Real.sqrt (Kl ^ 2 + 16 * ‖M.gm‖ + ‖M.hm‖ + 2)
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have hev := hF5.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / (s + 1)))
    filter_upwards [hev, hA512] with k hk hk512 τ hτ
    have hs : ∀ μ x, ‖(n k : ℝ)⁻¹ • NativeDensity.gauge (y' k) μ x‖ < 1 / 32 := by
      intro μ x
      rw [norm_smul, Real.norm_of_nonneg (hNpos k).le]
      linarith [hk512 μ x]
    have hd : DifferentiableAt ℝ
        (localAction (bankCov C₀ Tj (θs k) hT (hY k)).toData (n k : ℝ)⁻¹) (y' k) := by
      refine NativeFrechet.differentiableAt_localAction _ (hNpos k).ne'
        (fun x => (hpos _ (hval' k x)).ne') (fun x μ ν _ => ?_) (fun x μ ν _ => ?_)
      · refine NativeGravityFirstJet.cartan_log_lt (hNpos k) hcm (coframe (y' k))
          (fun x μ => ?_) x μ ν
        have := hmar k x μ
        rw [← hωM] at this
        exact this
      · exact (DeterminantResolved.norm_gaugePlaquette_sub_one_le (NativeDensity.gauge (y' k))
          (fun μ x => hk512 μ x) x μ ν).trans_lt (by norm_num)
    have hb := abs_nativeVar_testRec_le (bankCov C₀ Tj (θs k) hT (hY k)) M hKl0 hKl (hval' k)
      hs hd τ
    rw [covNormP_record_gauge (bankCov C₀ Tj (θs k) hT (hY k)) M
      (massMetric_invariant_bankCov C₀ M hM Tj (θs k) hT (hY k))
      (isGaugeTransform_bankCov C₀ Tj (θs k) hT (hY k) (hIG k))
      (fun x μ ν _ => hP k x μ ν)] at hb
    have hc0' := covNormP_nonneg (bankCov C₀ Tj (θs k) hT (hY k)) M (N := n k) (n k : ℝ)⁻¹
      (toLinks (n k : ℝ)⁻¹ (y k))
    have hτ0 := τ.norm_nonneg
    calc _ ≤ _ := hb
      _ ≤ ε / (s + 1) * (s * 1) :=
          mul_le_mul hk.le (mul_le_mul_of_nonneg_left hτ hs0) (by positivity) (by positivity)
      _ ≤ ε := by
          rw [mul_one, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          nlinarith
  exact ⟨g, y', fun k x => ⟨gt k x, hgtK k x, rfl⟩, hIG, hgauge, fun k => φ₀ (φ' k), hφ₀.comp hφ', H, hHK, θ, hθ, F, G, P, S, u₀,
    c1, c2, c3, c4, c5, c6, c7, c8 (fun ε hε => hev₀ (hstat ε hε)), c9⟩

set_option maxHeartbeats 12800000 in
-- the normalization of the remainder, the transfer of the hypotheses and the combined criterion
/-- **`cor:determinant-resolved-closure`, generic assembly** (unit-torus rendering, mesh
`h = 1/N`; gauge group `K ⊆ U(𝔄)` with the rooted Coulomb normalization property `RootedNorm`,
invariant metric `toE`; a central skew-adjoint direction `Z` whose phases `e^{sZ}` lie in `K`).
There are cutoff-independent `ε_c, ε_* > 0` such that, for native records with unitary links
`U_h = e^{hA_h} ∈ K` whose plaquettes are in the logarithm chart, and **central-split data**
(site phases `t_h`, real potentials `a_h` that are strongly precompact in `L⁴` with strongly
precompact first differences — the determinant normalization — **with no smallness**), if the
remainder `V_h = e^{-h a_h Z} e^{t_h Z} U_h e^{-t_h Z}` (`splitVg`) has an admissible rooted seed,
plaquettes in the chart and rooted certificate `≤ ε_c` (`eq:semisimple-only-certificate`), then
under `(F1)`, `(F3)`, `(F4)`, `(F5)` of `thm:finite-Wilson-zero-defect` there are actual site
gauges `g_h ∈ K` (`g_h = q_h e^{t_h Z}`, `q_h` the rooted normalization of `V_h`) acting on the
same records, the normalized logarithmic connection is exactly `A'_h = b_h + a_h Z`
(`eq:determinant-combined-connection`) with `δ_h b_h = 0` and `‖b_h‖_{4,h} ≤ ε_*` — **only `b_h`
lies in the small critical ball** — and, after extraction, all the convergence and variational
conclusions of `thm:finite-Wilson-zero-defect` hold (`eq:Wilson-strong-convergence`,
`eq:native-all-sector-limit` with the cutoff banks, the reconstructed-field consistency, the
distributional Einstein–Standard-Model equations, strong `L¹` convergence of the bosonic stress
densities). -/
theorem determinant_resolved_of_rootedNorm (C₀ : CovData 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢)
    (K : Subgroup (unitary 𝔄)) (hG : ∀ u ∈ K, Unitary.toUnits u ∈ C₀.G)
    (hρH : ∀ k ∈ C₀.G, ∀ v : EuclideanSpace ℝ (Fin rH), ‖C₀.ρH k v‖ = ‖v‖)
    (Tj : Fin J → 𝔄 →L[ℝ] E)
    (hT : ∀ g ∈ C₀.G, ∀ j (X Y : 𝔄),
      ⟪Tj j ((g : 𝔄) * X * ↑g⁻¹), Tj j ((g : 𝔄) * Y * ↑g⁻¹)⟫ = ⟪Tj j X, Tj j Y⟫)
    (toE : 𝔄 ≃L[ℝ] E₀) (HN : RootedNorm K toE)
    (M : MassMetric 𝔄 (EuclideanSpace ℝ (Fin rH))) (hM : M.Invariant C₀)
    (Θ : 𝓢 ≃L[ℝ] EuclideanSpace ℝ (Fin r)) (Θ' : CoSpinor 𝓢 ≃L[ℝ] EuclideanSpace ℝ (Fin r'))
    {Z : 𝔄} (hZs : star Z = -Z) (hZc : ∀ X : 𝔄, Commute X Z) (hZK : ∀ s, cUg hZs s ∈ K) :
    ∃ εc > 0, ∃ εstar > 0, ∀ (n : ℕ → ℕ) [∀ k, NeZero (n k)]
      (y : ∀ k, Grid (n k) → Field 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢)
      (θs : ℕ → Bank J (EuclideanSpace ℝ (Fin rH)) 𝓢), Tendsto n atTop atTop →
      -- the unitary internal links of the records, in the logarithm chart
      ∀ (U : ∀ k, Grid (n k) × Fin 4 → unitary 𝔄)
        (hUe : ∀ k x μ, (U k (x, μ) : 𝔄) = exp ((n k : ℝ)⁻¹ • NativeDensity.gauge (y k) μ x))
        (hUK : ∀ k e, U k e ∈ K),
      (∀ k μ ν x, ‖RootedCoulomb.litPlaq (U k) μ ν x - 1‖ < 1) →
      -- the central-split data
      ∀ (t : ∀ k, Grid (n k) → ℝ) (a : ∀ k, Fin 4 → Grid (n k) → ℝ),
      (∀ ψ : ℕ → ℕ, Tendsto ψ atTop atTop → ∃ φ : ℕ → ℕ, StrictMono φ ∧
        ∃ (a₀ : Fin 4 → 𝕋 → ℝ) (Ga : Fin 4 → Fin 4 → 𝕋 → ℝ),
          (∀ μ, LpTendsto volume 4 (fun k => pc (a (ψ (φ k)) μ)) (a₀ μ)) ∧
          (∀ μ ν, LpTendsto volume 2 (fun k => pc (NativeHiggs.DpV μ (a (ψ (φ k)) ν)))
            (Ga μ ν))) →
      -- `eq:semisimple-only-certificate` for the remainder
      ∀ (o : ∀ k, Grid (n k))
        (w : ∀ k, ∀ v, LatticeWalk (RootedCoulomb.latSrc (ι := Fin 4) (n := n k))
          RootedCoulomb.latTgt v (o k)),
      (∀ k μ x, ‖((RootedWilson.rootedWord (w k)
        (splitVg hZs (n k : ℝ)⁻¹ (t k) (a k) (U k)) (x, μ) : unitary 𝔄) : 𝔄) - 1‖ ≤ 1 / 64) →
      (∀ k μ ν x, ‖RootedCoulomb.litPlaq (splitVg hZs (n k : ℝ)⁻¹ (t k) (a k) (U k)) μ ν x - 1‖
        < 1) →
      (∀ k, CoulombApriori.oneL4 (n k : ℝ)⁻¹ (toE : 𝔄 →L[ℝ] E₀)
          (RootedCoulomb.treeSeed (n k : ℝ)⁻¹ (w k) (splitVg hZs (n k : ℝ)⁻¹ (t k) (a k) (U k))) +
        RootedCoulomb.litCurvL2 toE (n k : ℝ)⁻¹ (splitVg hZs (n k : ℝ)⁻¹ (t k) (a k) (U k))
          ≤ εc) →
      -- `(F1)`
      ∀ (Ke : Set M4), IsCompact Ke → (∀ M ∈ Ke, 0 < Matrix.det (show Mat from M)) →
      (∀ k x, coframeM (y k) x ∈ Ke) → ∀ cm : ℝ, cm ≤ 1 / 64 →
      (∀ k x μ, (n k : ℝ)⁻¹ * ‖ωM (y k) μ x‖ ≤ cm) →
      TotallyBounded (range fun k => pcLp (coframeM (y k))) →
      TotallyBounded (range fun k => pcLp (fun x lam => qM (y k) lam x)) →
      (∀ k z, NativeTrigRec.recon (coframeM (y k)) z ∈ Ke) →
      -- `(F3)`
      (∃ B, ∀ k, gridNorm (curvPacket (n k) (y k)) ≤ B) →
      (∃ B, ∀ k, gridNorm (higgsPacket C₀.toData (n k) (y k)) ≤ B) →
      ∀ BH : ℝ, (∀ k, gridNorm (higgs (y k)) ≤ BH) →
      (∀ ε > 0, ∃ ρ > 0, ∀ᶠ k in atTop, ∀ (μ : Fin 4) (m : ℕ), 0 < m → (m : ℝ) / n k ≤ ρ →
        gridNorm (wilsonShiftR (adLinks (n k) (y k) (adUnit_of_links (hUe k))) μ m
          (curvPacket (n k) (y k)) - curvPacket (n k) (y k)) ≤ ε) →
      (∀ ε > 0, ∃ ρ > 0, ∀ᶠ k in atTop, ∀ (μ : Fin 4) (m : ℕ), 0 < m → (m : ℝ) / n k ≤ ρ →
        gridNorm (wilsonShiftR (higgsLinks C₀.toData (n k) (y k)
            (higgsUnit_of_links C₀ K hG hρH (hUe k) (hUK k))) μ m
          (higgsPacket C₀.toData (n k) (y k)) - higgsPacket C₀.toData (n k) (y k)) ≤ ε) →
      -- `(F4)`
      ∀ B : ℝ, (∀ k, gridNorm (psi (y k)) ≤ B) →
      (∀ k μ, gridNorm (fun x => spinGraph C₀.toData (n k : ℝ)⁻¹ (y k) x μ) ≤ B) →
      (∀ k, gridNorm (psiBar (y k)) ≤ B) →
      (∀ k μ, gridNorm (fun x => dualGraph C₀.toData (n k : ℝ)⁻¹ (y k) x μ) ≤ B) →
      ∀ (Kθ : Set (ℝ × ℝ × ℝ × ℝ × (Fin J → ℝ) ×
          (EuclideanSpace ℝ (Fin rH) →L[ℝ] Spin 𝓢))), IsCompact Kθ →
      (∀ k, bankVec (θs k) ∈ Kθ) → (∀ v ∈ Kθ, v.1 ≠ 0 ∧ ∀ j, 0 ≤ v.2.2.2.2.1 j) →
      ∀ (hY : ∀ k, ∀ g ∈ C₀.G, ∀ H : EuclideanSpace ℝ (Fin rH),
        (θs k).Y (C₀.ρH g H) = C₀.ρS g * (θs k).Y H * C₀.ρS ↑g⁻¹),
      -- `(F5)`
      Tendsto (fun k => covNormP (bankCov C₀ Tj (θs k) hT (hY k)) M (n k : ℝ)⁻¹
        (toLinks (n k : ℝ)⁻¹ (y k))) atTop (𝓝 0) →
      ∃ g : ∀ k, Grid (n k) → 𝔄ˣ, ∃ y' : ∀ k, Grid (n k) → Field 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢,
      (∀ k x, ∃ u ∈ K, g k x = Unitary.toUnits u) ∧
      (∀ k, IsGaugeTransform C₀ (n k : ℝ)⁻¹ (g k) (y k) (y' k)) ∧
      -- `eq:determinant-combined-connection`: only `b` is small
      ∃ b : ∀ k, Fin 4 → Grid (n k) → 𝔄,
      (∀ k μ x, NativeDensity.gauge (y' k) μ x = b k μ x + a k μ x • Z) ∧
      (∀ k, NativeCoulomb.codiffT (toE : 𝔄 →L[ℝ] E₀) (fun x μ => b k μ x) = 0) ∧
      (∀ k μ, NativeCoulomb.g4 (fun x => toE (b k μ x)) ≤ εstar) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ H : CoHyp (fun k => n (φ k)) (fun k => y' (φ k)),
      H.Ke = Ke ∧
      ∃ θ : Bank J (EuclideanSpace ℝ (Fin rH)) 𝓢, BankConv (fun k => θs (φ k)) θ ∧
      ∃ F : Fin 4 → Fin 4 → 𝕋 → 𝔄, ∃ G : Fin 4 → Fin 4 → 𝕋 → 𝔄,
      ∃ P : HiggsHyp (bankData C₀.toData Tj θ) (fun k => y' (φ k)),
      ∃ S : SpinHyp (κid 𝓢) (fun k => y' (φ k)), ∃ u₀ : 𝕋 → Dif 𝓢 (CoSpinor 𝓢),
      -- `eq:Wilson-strong-convergence`
      (∀ μ ν, LpTendsto volume 2 (fun k => pc (fun x =>
        NativeScaling.fieldStrength (n (φ k) : ℝ)⁻¹ (NativeDensity.gauge (y' (φ k))) x μ ν))
        (F μ ν)) ∧
      (∀ μ ν, LpTendsto volume 2
        (fun k => pc (NativeHiggs.DpV μ (NativeDensity.gauge (y' (φ k)) ν))) (G μ ν)) ∧
      (∀ μ ν, F μ ν =ᵐ[MeasureTheory.volume] NativeReconstructed.recCurv H.A₀ G μ ν) ∧
      (∀ μ, LpTendsto volume 2 (fun k => pc (NativeHiggs.DpV μ (higgs (y' (φ k)))))
        (fun z => P.K₀ μ z - C₀.ρHL (H.A₀ μ z) (P.H₀ z))) ∧
      (∀ j, ∃ fj : Lp ℂ 2 (MeasureTheory.volume : Measure 𝕋),
        ((fj : 𝕋 → ℂ) =ᵐ[MeasureTheory.volume] fun z => ((Θ (S.Ψ₀ z) j : ℝ) : ℂ)) ∧
        TorusSobolev.MemH 1 fj ∧ ∀ μ, (TorusSobolev.weakDeriv μ fj : 𝕋 → ℂ)
          =ᵐ[MeasureTheory.volume] fun z => ((Θ ((u₀ z).1 μ) j : ℝ) : ℂ)) ∧
      -- `eq:native-all-sector-limit` with the cutoff banks
      (∀ M : NNReal, ∀ ε > 0, ∀ᶠ k in atTop,
        ∀ τ : DTest 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢 (CoSpinor 𝓢), τ.norm ≤ M →
        |NativeAllSector.nativeVar (bankData C₀.toData Tj (θs (φ k))) (n (φ k)) (y' (φ k))
            (testRec (κid 𝓢) (n (φ k)) (y' (φ k)) τ) -
          NativeAllSector.contAllVar (bankData C₀.toData Tj θ) (κid 𝓢) (bankT Tj θ.w) H F P S u₀
            τ| ≤ ε) ∧
      -- consistency relative to the reconstructed fields
      (∀ M : NNReal, ∀ ε > 0, ∀ᶠ k in atTop,
        ∀ τ : DTest 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢 (CoSpinor 𝓢), τ.norm ≤ M →
        |NativeAllSector.nativeVar (bankData C₀.toData Tj (θs (φ k))) (n (φ k)) (y' (φ k))
            (testRec (κid 𝓢) (n (φ k)) (y' (φ k)) τ) -
          NativeReconstructed.recAllVar (bankData C₀.toData Tj θ) (κid 𝓢) (bankT Tj θ.w)
            (NativeTrigRec.recon (coframeM (y' (φ k))))
            (fun lam => NativeTrigRec.drecon lam (coframeM (y' (φ k))))
            (fun μ => NativeTrigRec.recon (NativeDensity.gauge (y' (φ k)) μ))
            (fun μ ν => NativeTrigRec.drecon μ (NativeDensity.gauge (y' (φ k)) ν))
            (NativeTrigRec.recon (higgs (y' (φ k))))
            (fun μ => NativeTrigRec.drecon μ (higgs (y' (φ k))))
            (NativeTrigRec.recon (psi (y' (φ k)))) (NativeTrigRec.recon (psiBar (y' (φ k))))
            (NativeTrigRec.recJets (y' (φ k))) τ| ≤ ε) ∧
      -- the distributional Einstein–Standard-Model equations
      (∀ τ : DTest 𝔄 (EuclideanSpace ℝ (Fin rH)) 𝓢 (CoSpinor 𝓢),
        NativeAllSector.contAllVar (bankData C₀.toData Tj θ) (κid 𝓢) (bankT Tj θ.w) H F P S u₀ τ
          = 0) ∧
      -- the bosonic stress densities
      (∀ (ΘF : M4 → (Fin 4 → Fin 4 → 𝔄) →L[ℝ] (Fin 4 → Fin 4 → 𝔄) →L[ℝ] ℝ)
        (ΘK : M4 → (Fin 4 → EuclideanSpace ℝ (Fin rH)) →L[ℝ]
          (Fin 4 → EuclideanSpace ℝ (Fin rH)) →L[ℝ] ℝ) (ΘV : M4 → ℝ),
        ContinuousOn ΘF Ke → ContinuousOn ΘK Ke → ContinuousOn ΘV Ke →
        LpTendsto volume 1
          (fun k z => ΘF (pc (coframeM (y' (φ k))) z) (pc (curvPacket (n (φ k)) (y' (φ k))) z)
              (pc (curvPacket (n (φ k)) (y' (φ k))) z) +
            ΘK (pc (coframeM (y' (φ k))) z)
              (pc (higgsPacket C₀.toData (n (φ k)) (y' (φ k))) z)
              (pc (higgsPacket C₀.toData (n (φ k)) (y' (φ k))) z) +
            ΘV (pc (coframeM (y' (φ k))) z) *
              potential (bankData C₀.toData Tj (θs (φ k))) (pc (higgs (y' (φ k))) z))
          (fun z => ΘF (H.e₀ z) (fun μ ν => F μ ν z) (fun μ ν => F μ ν z) +
            ΘK (H.e₀ z) (fun μ => P.K₀ μ z) (fun μ => P.K₀ μ z) +
            ΘV (H.e₀ z) * potential (bankData C₀.toData Tj θ) (P.H₀ z))) := by
  -- constants
  set c₀ : ℝ := ‖(toE.symm : E₀ →L[ℝ] 𝔄)‖ with hc₀def
  have hc0 : 0 ≤ c₀ := norm_nonneg _
  have hc : ∀ X : 𝔄, ‖X‖ ≤ c₀ * ‖(toE : 𝔄 →L[ℝ] E₀) X‖ := FiniteCoulomb.norm_le_symm toE
  obtain ⟨ε₀, hε₀, hBC⟩ := DeterminantResolved.bCompact_of_coulomb (toE : 𝔄 →L[ℝ] E₀) hc0 hc
  set ε₁ : ℝ := min ε₀ (1 / (1024 * (c₀ + 1))) with hε₁def
  have hε₁ : 0 < ε₁ := lt_min hε₀ (by positivity)
  have hε₁₀ : ε₁ ≤ ε₀ := min_le_left _ _
  have hcε : c₀ * ε₁ ≤ 1 / 1024 := by
    have h1 : ε₁ ≤ 1 / (1024 * (c₀ + 1)) := min_le_right _ _
    calc c₀ * ε₁ ≤ c₀ * (1 / (1024 * (c₀ + 1))) := mul_le_mul_of_nonneg_left h1 hc0
      _ ≤ 1 / 1024 := by
          rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
  obtain ⟨εc, hεc, hroot⟩ := HN ε₁ hε₁
  refine ⟨εc, hεc, ε₁, hε₁, fun n _ y θs hn U hUe hUK hplaq t a ha o w hadm hplaqV hcert Ke hKe
    hpos hval cm hcm hmar hTBe hTBq hrec hFb hKb BH hHb hΩF hΩK B hΨ hKs hΨb hKbd Kθ hKθ hθK
    hphys hY hF5 => ?_⟩
  have hNpos : ∀ k, (0 : ℝ) < (n k : ℝ)⁻¹ := fun k =>
    inv_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (n k)))
  -- the rooted normalization of the remainder
  have hVK : ∀ k e, splitVg hZs (n k : ℝ)⁻¹ (t k) (a k) (U k) e ∈ K := fun k e =>
    splitVg_mem hZs K hZK _ _ _ (hUK k) e
  choose gV hgV using fun k => hroot (n k) (o k) (w k)
    (splitVg hZs (n k : ℝ)⁻¹ (t k) (a k) (U k)) (hVK k) (hadm k) (hplaqV k) (hcert k)
  set b : ∀ k, Fin 4 → Grid (n k) → 𝔄 := fun k μ x => ((n k : ℝ)⁻¹)⁻¹ •
    SeriesLogChart.logChart ((gaugeLinks RootedCoulomb.latSrc RootedCoulomb.latTgt (gV k)
      (splitVg hZs (n k : ℝ)⁻¹ (t k) (a k) (U k)) (x, μ) : unitary 𝔄) : 𝔄) with hbdef
  have hWb : ∀ k μ x, exp ((n k : ℝ)⁻¹ • b k μ x) = ((gaugeLinks RootedCoulomb.latSrc
      RootedCoulomb.latTgt (gV k) (splitVg hZs (n k : ℝ)⁻¹ (t k) (a k) (U k)) (x, μ) :
        unitary 𝔄) : 𝔄) := fun k μ x => by
    simp only [hbdef]
    rw [smul_smul, mul_inv_cancel₀ (hNpos k).ne', one_smul,
      SeriesLogChart.exp_logChart ((hgV k).2.1 μ x)]
  -- exact Coulomb gauge and smallness of `b`
  have hcod : ∀ k, NativeCoulomb.codiffT (toE : 𝔄 →L[ℝ] E₀) (fun x μ => b k μ x) = 0 := by
    intro k
    have h := (hgV k).2.2.1
    unfold NativeCoulomb.codiffT
    convert h using 2
    rfl
  have hsm : ∀ k μ, NativeCoulomb.g4 (fun x => toE (b k μ x)) ≤ ε₁ := by
    intro k μ
    have h := (CoulombApriori.gridL4_le_oneL4 (hNpos k).le (toE : 𝔄 →L[ℝ] E₀) _ μ).trans
      (hgV k).2.2.2
    refine (le_of_eq ?_).trans h
    rfl
  have hbmesh : ∀ k μ x, (n k : ℝ)⁻¹ * ‖b k μ x‖ ≤ 1 / 1024 := fun k μ x =>
    (mesh_small (toE : 𝔄 →L[ℝ] E₀) hc0 hc (N := n k) (b k) (hsm k) x μ).trans hcε
  obtain ⟨hbB, -, hbC⟩ := hBC n hn b hcod (fun k μ => (hsm k μ).trans hε₁₀)
  obtain ⟨g, y', hgK, hIG, hgauge, rest⟩ := determinant_resolved_post C₀ K hG hρH Tj hT M hM Θ Θ'
    hZs hZc hZK n y θs hn U hUe hUK hplaq t a ha gV b (fun k x => (hgV k).1 x) hWb hbB
    (Eventually.of_forall hbmesh) hbC Ke hKe hpos hval cm hcm hmar hTBe hTBq hrec
    hFb hKb BH hHb hΩF hΩK B hΨ hKs hΨb hKbd Kθ hKθ hθK hphys hY hF5
  exact ⟨g, y', hgK, hIG, b, hgauge, hcod, hsm, rest⟩

end Assembly

/-! ### The exact-flatness alternative: bridge to `lem:flat-semisimple-normalization` -/

section FlatBridge

open ShiftedJetAction (Grid unitVec)
open FlatSemisimple (Gss)

/-- An element of `G_ss = SU(3) × SU(2)` given as a unitary of `M₃(ℂ) × M₂(ℂ)` with both block
determinants `1`. -/
def toGss (u : unitary SMAlg) (h1 : ((u : SMAlg).1).det = 1) (h2 : ((u : SMAlg).2).det = 1) :
    Gss :=
  (⟨(u : SMAlg).1, Matrix.mem_specialUnitaryGroup_iff.2
      ⟨StandardModelCoulomb.fst_mem_unitary u.2, h1⟩⟩,
    ⟨(u : SMAlg).2, Matrix.mem_specialUnitaryGroup_iff.2
      ⟨StandardModelCoulomb.snd_mem_unitary u.2, h2⟩⟩)

/-- `G_ss = SU(3) × SU(2)` inside the unitaries of `M₃(ℂ) × M₂(ℂ)`. -/
def fromGss (q : Gss) : unitary SMAlg :=
  ⟨((q.1 : Matrix (Fin 3) (Fin 3) ℂ), (q.2 : Matrix (Fin 2) (Fin 2) ℂ)), by
    have h1 := (Matrix.mem_specialUnitaryGroup_iff.1 q.1.2).1
    have h2 := (Matrix.mem_specialUnitaryGroup_iff.1 q.2.2).1
    rw [Unitary.mem_iff]
    exact ⟨Prod.ext (Unitary.star_mul_self_of_mem h1) (Unitary.star_mul_self_of_mem h2),
      Prod.ext (Unitary.mul_star_self_of_mem h1) (Unitary.mul_star_self_of_mem h2)⟩⟩

@[simp] theorem coe_fromGss (q : Gss) :
    ((fromGss q : unitary SMAlg) : SMAlg) =
      ((q.1 : Matrix (Fin 3) (Fin 3) ℂ), (q.2 : Matrix (Fin 2) (Fin 2) ℂ)) := rfl

theorem fromGss_mem_GSM (q : Gss) : fromGss q ∈ NativeRecordNormSM.GSM := by
  rw [NativeRecordNormSM.mem_GSM]
  simp only [StandardModelCoulomb.detSM, coe_fromGss]
  rw [(Matrix.mem_specialUnitaryGroup_iff.1 q.1.2).2, (Matrix.mem_specialUnitaryGroup_iff.1 q.2.2).2,
    one_mul]

variable {N : ℕ} [NeZero N]

/-- Exact flatness of unitary links in the `G_ss`-encoding. -/
theorem isFlat_toGss {V : Grid N × Fin 4 → unitary SMAlg}
    (h1 : ∀ e, ((V e : SMAlg).1).det = 1) (h2 : ∀ e, ((V e : SMAlg).2).det = 1)
    (hflat : ∀ μ ν x, RootedCoulomb.litPlaq V μ ν x = 1) :
    FlatSemisimple.IsFlat (fun x μ => toGss (V (x, μ)) (h1 (x, μ)) (h2 (x, μ))) := by
  intro x μ ν
  have hu : ∀ e, (V e : SMAlg) ∈ unitary SMAlg := fun e => (V e).2
  have key : (V (x, μ) : SMAlg) * (V (x + GridSobolev.gridStep μ, ν) : SMAlg) =
      (V (x, ν) : SMAlg) * (V (x + GridSobolev.gridStep ν, μ) : SMAlg) := by
    have h := hflat μ ν x
    simp only [RootedCoulomb.litPlaq] at h
    calc (V (x, μ) : SMAlg) * (V (x + GridSobolev.gridStep μ, ν) : SMAlg)
        = ((V (x, μ) : SMAlg) * (V (x + GridSobolev.gridStep μ, ν) : SMAlg) *
            star (V (x + GridSobolev.gridStep ν, μ) : SMAlg) * star (V (x, ν) : SMAlg)) *
          ((V (x, ν) : SMAlg) * (V (x + GridSobolev.gridStep ν, μ) : SMAlg)) := by
          rw [show ((V (x, μ) : SMAlg) * (V (x + GridSobolev.gridStep μ, ν) : SMAlg) *
            star (V (x + GridSobolev.gridStep ν, μ) : SMAlg) * star (V (x, ν) : SMAlg)) *
            ((V (x, ν) : SMAlg) * (V (x + GridSobolev.gridStep ν, μ) : SMAlg)) =
            (V (x, μ) : SMAlg) * (V (x + GridSobolev.gridStep μ, ν) : SMAlg) *
            (star (V (x + GridSobolev.gridStep ν, μ) : SMAlg) * (star (V (x, ν) : SMAlg) *
              (V (x, ν) : SMAlg)) * (V (x + GridSobolev.gridStep ν, μ) : SMAlg)) by noncomm_ring,
            Unitary.star_mul_self_of_mem (hu _), mul_one, Unitary.star_mul_self_of_mem (hu _),
            mul_one]
      _ = (V (x, ν) : SMAlg) * (V (x + GridSobolev.gridStep ν, μ) : SMAlg) := by rw [h, one_mul]
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
  · exact congrArg Prod.fst key
  · exact congrArg Prod.snd key

/-- The flat normalization in the `M₃(ℂ) × M₂(ℂ)` encoding. -/
theorem gaugeLinks_fromGss {V : Grid N × Fin 4 → unitary SMAlg}
    (h1 : ∀ e, ((V e : SMAlg).1).det = 1) (h2 : ∀ e, ((V e : SMAlg).2).det = 1)
    (g : Grid N → Gss) (x : Grid N) (μ : Fin 4) :
    ((gaugeLinks RootedCoulomb.latSrc RootedCoulomb.latTgt (fun x => fromGss (g x)) V (x, μ) :
        unitary SMAlg) : SMAlg) =
      (((FlatSemisimple.gaugeAct g (fun x μ => toGss (V (x, μ)) (h1 (x, μ)) (h2 (x, μ))) x μ).1 :
          Matrix (Fin 3) (Fin 3) ℂ),
        ((FlatSemisimple.gaugeAct g (fun x μ => toGss (V (x, μ)) (h1 (x, μ)) (h2 (x, μ))) x μ).2 :
          Matrix (Fin 2) (Fin 2) ℂ)) := rfl

end FlatBridge

/-! ### `cor:determinant-resolved-closure` for `G_SM` -/

section MainSM

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance : (volume : Measure UnitAddCircle).IsAddHaarMeasure :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

/-- The unit torus `𝕋⁴`. -/
local notation "𝕋" => UnitAddTorus (Fin 4)

open ShiftedJetAction (Grid unitVec)
open NativeScaling (Mat)
open NativeDensity NativeGauge NativeLinkCov NativeBank
open NativeDiracLimit (DTest testRec samp Dif)
open NativeGravityFirstJet (M4 liftM coframeM)
open NativeSpinorGraph (κid spinGraph dualGraph)
open TorusPiecewiseConstantTranslation KolmogorovRieszTorus
open NativeHiggsVar NativeDiracConvergence FiniteWilsonZeroDefect FiniteWilsonClosure
open NativeDiracConv (CoHyp qM ωM)

variable {rH : ℕ} [NeZero rH]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
  [FiniteDimensional ℝ 𝓢]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {r r' : ℕ} [NeZero r] [NeZero r'] {J : ℕ}

local instance fact_one_le_two_drsm : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩

/-- The full plaquette of the record is the literal plaquette of its unitary links. -/
theorem gaugePlaquette_eq_litPlaq_SM {N : ℕ} [NeZero N]
    {y : Grid N → Field SMAlg (EuclideanSpace ℝ (Fin rH)) 𝓢} {U : Grid N × Fin 4 → unitary SMAlg}
    (hUe : ∀ x μ, (U (x, μ) : SMAlg) = exp ((N : ℝ)⁻¹ • gauge y μ x)) (x : Grid N) (μ ν : Fin 4) :
    NativeScaling.gaugePlaquette (N : ℝ)⁻¹ (gauge y) x μ ν = RootedCoulomb.litPlaq U μ ν x := by
  simp only [NativeScaling.gaugePlaquette, exp_neg_eq_star_of_links hUe, ← hUe,
    RootedCoulomb.litPlaq]
  rfl

set_option maxHeartbeats 12800000 in
-- instantiation of the generic assembly
/-- **`cor:determinant-resolved-closure`** (certificate form; Standard-Model gauge group
`G_SM = S(U(3) × U(2)) ⊂ M₃(ℂ) × M₂(ℂ)`, `eq:gauge-group`; unit-torus rendering, mesh
`h = 1/N`).  There are cutoff-independent `ε_c, ε_* > 0` such that the following holds.  Native
records with internal links `U_h = e^{hA_h} ∈ G_SM` whose plaquettes are in the logarithm chart
satisfy `(F1)`, `(F3)`, `(F4)`, `(F5)` of `thm:finite-Wilson-zero-defect`; **in place of `(F2)`**:
the determinant flux is zero for all sufficiently small `h`, and the semisimple remainder
`V_h = e^{-h a_h Z_c} e^{t_h Z_c} U_h e^{-t_h Z_c}` of `eq:determinant-exact-split` — built from the
paper's determinant potential `a_h = δ_h Δ_h^† f_h + c_h` (`detCoord`, cycle constants
`|c_{h,μ}| ≤ π`) and any site phases `t_h` — has, for one predeclared rooted tree, an admissible
seed, plaquettes in the logarithm chart, and rooted certificate
`‖B^𝔗(V_h)‖_{4,h} + ‖F_h(V_h)‖_{2,h} ≤ ε_c` (`eq:semisimple-only-certificate`).

Conclusions: actual `G_SM` site gauges `g_h = q_h e^{t_h Z_c}` act on the same records; the
normalized logarithmic connection is exactly `A_h = b_h + Z_c a_h`
(`eq:determinant-combined-connection`) with `δ_h b_h = 0`, `‖b_h‖_{4,h} ≤ ε_*` (only `b_h` lies
in the small critical ball; no smallness of the determinant curvature, of `‖a_h‖_{4,h}` or of the
flat cycle holonomies is assumed), and eventually `δ_h a_h = 0` and `δ_h A_h = 0`; after
extraction, all the convergence and variational conclusions of `thm:finite-Wilson-zero-defect`
hold: `eq:Wilson-strong-convergence`, `eq:native-all-sector-limit` with the cutoff banks, the
reconstructed-field consistency, the distributional Einstein–Standard-Model equations, and strong
`L¹` convergence of the bosonic stress densities.  The compactness of `a_h` is
`prop:periodic-determinant-normalization` (`detCoord_precompact`), fed by the full curvature
Wilson screen of `(F3)` (`curvatureScreen_of_records`). -/
theorem determinant_resolved_closure_SM (C₀ : CovData SMAlg (EuclideanSpace ℝ (Fin rH)) 𝓢)
    (hG : ∀ u ∈ NativeRecordNormSM.GSM, Unitary.toUnits u ∈ C₀.G)
    (hρH : ∀ k ∈ C₀.G, ∀ v : EuclideanSpace ℝ (Fin rH), ‖C₀.ρH k v‖ = ‖v‖)
    (Tj : Fin J → SMAlg →L[ℝ] E)
    (hT : ∀ g ∈ C₀.G, ∀ j (X Y : SMAlg),
      ⟪Tj j ((g : SMAlg) * X * ↑g⁻¹), Tj j ((g : SMAlg) * Y * ↑g⁻¹)⟫ = ⟪Tj j X, Tj j Y⟫)
    (M : MassMetric SMAlg (EuclideanSpace ℝ (Fin rH))) (hM : M.Invariant C₀)
    (Θ : 𝓢 ≃L[ℝ] EuclideanSpace ℝ (Fin r)) (Θ' : CoSpinor 𝓢 ≃L[ℝ] EuclideanSpace ℝ (Fin r')) :
    ∃ εc > 0, ∃ εstar > 0, ∀ (n : ℕ → ℕ) [∀ k, NeZero (n k)]
      (y : ∀ k, Grid (n k) → Field SMAlg (EuclideanSpace ℝ (Fin rH)) 𝓢)
      (θs : ℕ → Bank J (EuclideanSpace ℝ (Fin rH)) 𝓢), Tendsto n atTop atTop →
      -- the unitary internal links of the records, in the logarithm chart
      ∀ (U : ∀ k, Grid (n k) × Fin 4 → unitary SMAlg)
        (hUe : ∀ k x μ, (U k (x, μ) : SMAlg) = exp ((n k : ℝ)⁻¹ • NativeDensity.gauge (y k) μ x))
        (hUK : ∀ k e, U k e ∈ NativeRecordNormSM.GSM),
      (∀ k μ ν x, ‖RootedCoulomb.litPlaq (U k) μ ν x - 1‖ < 1) →
      -- zero determinant flux for all sufficiently small `h`
      (∀ᶠ k in atTop, ∀ μ ν,
        DeterminantFlux.planeFlux (fun x μ => ((U k (x, μ) : SMAlg).2).det) 0 μ ν = 0) →
      -- the determinant normalization: cycle constants and site phases
      ∀ (c : ℕ → Fin 4 → ℝ), (∀ k μ, |c k μ| ≤ Real.pi) → ∀ (t : ∀ k, Grid (n k) → ℝ),
      -- `eq:semisimple-only-certificate` for the remainder
      ∀ (o : ∀ k, Grid (n k))
        (w : ∀ k, ∀ v, LatticeWalk (RootedCoulomb.latSrc (ι := Fin 4) (n := n k))
          RootedCoulomb.latTgt v (o k)),
      (∀ k μ x, ‖((RootedWilson.rootedWord (w k)
        (splitVg star_Zc (n k : ℝ)⁻¹ (t k) (detCoord (n k) (U k) (c k)) (U k)) (x, μ) : unitary SMAlg) : SMAlg) - 1‖ ≤ 1 / 64) →
      (∀ k μ ν x, ‖RootedCoulomb.litPlaq (splitVg star_Zc (n k : ℝ)⁻¹ (t k) (detCoord (n k) (U k) (c k)) (U k)) μ ν x - 1‖
        < 1) →
      (∀ k, CoulombApriori.oneL4 (n k : ℝ)⁻¹ (StandardModelCoulomb.toESM : SMAlg →L[ℝ] StandardModelCoulomb.SMEuc)
          (RootedCoulomb.treeSeed (n k : ℝ)⁻¹ (w k) (splitVg star_Zc (n k : ℝ)⁻¹ (t k) (detCoord (n k) (U k) (c k)) (U k))) +
        RootedCoulomb.litCurvL2 StandardModelCoulomb.toESM (n k : ℝ)⁻¹ (splitVg star_Zc (n k : ℝ)⁻¹ (t k) (detCoord (n k) (U k) (c k)) (U k))
          ≤ εc) →
      -- `(F1)`
      ∀ (Ke : Set M4), IsCompact Ke → (∀ M ∈ Ke, 0 < Matrix.det (show Mat from M)) →
      (∀ k x, coframeM (y k) x ∈ Ke) → ∀ cm : ℝ, cm ≤ 1 / 64 →
      (∀ k x μ, (n k : ℝ)⁻¹ * ‖ωM (y k) μ x‖ ≤ cm) →
      TotallyBounded (range fun k => pcLp (coframeM (y k))) →
      TotallyBounded (range fun k => pcLp (fun x lam => qM (y k) lam x)) →
      (∀ k z, NativeTrigRec.recon (coframeM (y k)) z ∈ Ke) →
      -- `(F3)`
      (∃ B, ∀ k, gridNorm (curvPacket (n k) (y k)) ≤ B) →
      (∃ B, ∀ k, gridNorm (higgsPacket C₀.toData (n k) (y k)) ≤ B) →
      ∀ BH : ℝ, (∀ k, gridNorm (higgs (y k)) ≤ BH) →
      (∀ ε > 0, ∃ ρ > 0, ∀ᶠ k in atTop, ∀ (μ : Fin 4) (m : ℕ), 0 < m → (m : ℝ) / n k ≤ ρ →
        gridNorm (wilsonShiftR (adLinks (n k) (y k) (adUnit_of_links (hUe k))) μ m
          (curvPacket (n k) (y k)) - curvPacket (n k) (y k)) ≤ ε) →
      (∀ ε > 0, ∃ ρ > 0, ∀ᶠ k in atTop, ∀ (μ : Fin 4) (m : ℕ), 0 < m → (m : ℝ) / n k ≤ ρ →
        gridNorm (wilsonShiftR (higgsLinks C₀.toData (n k) (y k)
            (higgsUnit_of_links C₀ NativeRecordNormSM.GSM hG hρH (hUe k) (hUK k))) μ m
          (higgsPacket C₀.toData (n k) (y k)) - higgsPacket C₀.toData (n k) (y k)) ≤ ε) →
      -- `(F4)`
      ∀ B : ℝ, (∀ k, gridNorm (psi (y k)) ≤ B) →
      (∀ k μ, gridNorm (fun x => spinGraph C₀.toData (n k : ℝ)⁻¹ (y k) x μ) ≤ B) →
      (∀ k, gridNorm (psiBar (y k)) ≤ B) →
      (∀ k μ, gridNorm (fun x => dualGraph C₀.toData (n k : ℝ)⁻¹ (y k) x μ) ≤ B) →
      ∀ (Kθ : Set (ℝ × ℝ × ℝ × ℝ × (Fin J → ℝ) ×
          (EuclideanSpace ℝ (Fin rH) →L[ℝ] Spin 𝓢))), IsCompact Kθ →
      (∀ k, bankVec (θs k) ∈ Kθ) → (∀ v ∈ Kθ, v.1 ≠ 0 ∧ ∀ j, 0 ≤ v.2.2.2.2.1 j) →
      ∀ (hY : ∀ k, ∀ g ∈ C₀.G, ∀ H : EuclideanSpace ℝ (Fin rH),
        (θs k).Y (C₀.ρH g H) = C₀.ρS g * (θs k).Y H * C₀.ρS ↑g⁻¹),
      -- `(F5)`
      Tendsto (fun k => covNormP (bankCov C₀ Tj (θs k) hT (hY k)) M (n k : ℝ)⁻¹
        (toLinks (n k : ℝ)⁻¹ (y k))) atTop (𝓝 0) →
      ∃ g : ∀ k, Grid (n k) → SMAlgˣ, ∃ y' : ∀ k, Grid (n k) → Field SMAlg (EuclideanSpace ℝ (Fin rH)) 𝓢,
      (∀ k x, ∃ u ∈ NativeRecordNormSM.GSM, g k x = Unitary.toUnits u) ∧
      (∀ k, IsGaugeTransform C₀ (n k : ℝ)⁻¹ (g k) (y k) (y' k)) ∧
      -- `eq:determinant-combined-connection`: only `b` is small
      ∃ b : ∀ k, Fin 4 → Grid (n k) → SMAlg,
      (∀ k μ x, NativeDensity.gauge (y' k) μ x = b k μ x + detCoord (n k) (U k) (c k) μ x • Zc) ∧
      (∀ k, NativeCoulomb.codiffT (StandardModelCoulomb.toESM : SMAlg →L[ℝ] StandardModelCoulomb.SMEuc) (fun x μ => b k μ x) = 0) ∧
      (∀ k μ, NativeCoulomb.g4 (fun x => StandardModelCoulomb.toESM (b k μ x)) ≤ εstar) ∧
      -- the determinant potential and the full logarithmic connection are co-closed
      (∀ᶠ k in atTop, ∀ x,
        DeterminantFlux.gridDiv (fun x μ => detCoord (n k) (U k) (c k) μ x) x = 0) ∧
      (∀ᶠ k in atTop, NativeCoulomb.codiffT
        (StandardModelCoulomb.toESM : SMAlg →L[ℝ] StandardModelCoulomb.SMEuc)
        (NativeYMBridge.gaugeArr (y' k)) = 0) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ H : CoHyp (fun k => n (φ k)) (fun k => y' (φ k)),
      H.Ke = Ke ∧
      ∃ θ : Bank J (EuclideanSpace ℝ (Fin rH)) 𝓢, BankConv (fun k => θs (φ k)) θ ∧
      ∃ F : Fin 4 → Fin 4 → 𝕋 → SMAlg, ∃ G : Fin 4 → Fin 4 → 𝕋 → SMAlg,
      ∃ P : HiggsHyp (bankData C₀.toData Tj θ) (fun k => y' (φ k)),
      ∃ S : SpinHyp (κid 𝓢) (fun k => y' (φ k)), ∃ u₀ : 𝕋 → Dif 𝓢 (CoSpinor 𝓢),
      -- `eq:Wilson-strong-convergence`
      (∀ μ ν, LpTendsto volume 2 (fun k => pc (fun x =>
        NativeScaling.fieldStrength (n (φ k) : ℝ)⁻¹ (NativeDensity.gauge (y' (φ k))) x μ ν))
        (F μ ν)) ∧
      (∀ μ ν, LpTendsto volume 2
        (fun k => pc (NativeHiggs.DpV μ (NativeDensity.gauge (y' (φ k)) ν))) (G μ ν)) ∧
      (∀ μ ν, F μ ν =ᵐ[MeasureTheory.volume] NativeReconstructed.recCurv H.A₀ G μ ν) ∧
      (∀ μ, LpTendsto volume 2 (fun k => pc (NativeHiggs.DpV μ (higgs (y' (φ k)))))
        (fun z => P.K₀ μ z - C₀.ρHL (H.A₀ μ z) (P.H₀ z))) ∧
      (∀ j, ∃ fj : Lp ℂ 2 (MeasureTheory.volume : Measure 𝕋),
        ((fj : 𝕋 → ℂ) =ᵐ[MeasureTheory.volume] fun z => ((Θ (S.Ψ₀ z) j : ℝ) : ℂ)) ∧
        TorusSobolev.MemH 1 fj ∧ ∀ μ, (TorusSobolev.weakDeriv μ fj : 𝕋 → ℂ)
          =ᵐ[MeasureTheory.volume] fun z => ((Θ ((u₀ z).1 μ) j : ℝ) : ℂ)) ∧
      -- `eq:native-all-sector-limit` with the cutoff banks
      (∀ M : NNReal, ∀ ε > 0, ∀ᶠ k in atTop,
        ∀ τ : DTest SMAlg (EuclideanSpace ℝ (Fin rH)) 𝓢 (CoSpinor 𝓢), τ.norm ≤ M →
        |NativeAllSector.nativeVar (bankData C₀.toData Tj (θs (φ k))) (n (φ k)) (y' (φ k))
            (testRec (κid 𝓢) (n (φ k)) (y' (φ k)) τ) -
          NativeAllSector.contAllVar (bankData C₀.toData Tj θ) (κid 𝓢) (bankT Tj θ.w) H F P S u₀
            τ| ≤ ε) ∧
      -- consistency relative to the reconstructed fields
      (∀ M : NNReal, ∀ ε > 0, ∀ᶠ k in atTop,
        ∀ τ : DTest SMAlg (EuclideanSpace ℝ (Fin rH)) 𝓢 (CoSpinor 𝓢), τ.norm ≤ M →
        |NativeAllSector.nativeVar (bankData C₀.toData Tj (θs (φ k))) (n (φ k)) (y' (φ k))
            (testRec (κid 𝓢) (n (φ k)) (y' (φ k)) τ) -
          NativeReconstructed.recAllVar (bankData C₀.toData Tj θ) (κid 𝓢) (bankT Tj θ.w)
            (NativeTrigRec.recon (coframeM (y' (φ k))))
            (fun lam => NativeTrigRec.drecon lam (coframeM (y' (φ k))))
            (fun μ => NativeTrigRec.recon (NativeDensity.gauge (y' (φ k)) μ))
            (fun μ ν => NativeTrigRec.drecon μ (NativeDensity.gauge (y' (φ k)) ν))
            (NativeTrigRec.recon (higgs (y' (φ k))))
            (fun μ => NativeTrigRec.drecon μ (higgs (y' (φ k))))
            (NativeTrigRec.recon (psi (y' (φ k)))) (NativeTrigRec.recon (psiBar (y' (φ k))))
            (NativeTrigRec.recJets (y' (φ k))) τ| ≤ ε) ∧
      -- the distributional Einstein–Standard-Model equations
      (∀ τ : DTest SMAlg (EuclideanSpace ℝ (Fin rH)) 𝓢 (CoSpinor 𝓢),
        NativeAllSector.contAllVar (bankData C₀.toData Tj θ) (κid 𝓢) (bankT Tj θ.w) H F P S u₀ τ
          = 0) ∧
      -- the bosonic stress densities
      (∀ (ΘF : M4 → (Fin 4 → Fin 4 → SMAlg) →L[ℝ] (Fin 4 → Fin 4 → SMAlg) →L[ℝ] ℝ)
        (ΘK : M4 → (Fin 4 → EuclideanSpace ℝ (Fin rH)) →L[ℝ]
          (Fin 4 → EuclideanSpace ℝ (Fin rH)) →L[ℝ] ℝ) (ΘV : M4 → ℝ),
        ContinuousOn ΘF Ke → ContinuousOn ΘK Ke → ContinuousOn ΘV Ke →
        LpTendsto volume 1
          (fun k z => ΘF (pc (coframeM (y' (φ k))) z) (pc (curvPacket (n (φ k)) (y' (φ k))) z)
              (pc (curvPacket (n (φ k)) (y' (φ k))) z) +
            ΘK (pc (coframeM (y' (φ k))) z)
              (pc (higgsPacket C₀.toData (n (φ k)) (y' (φ k))) z)
              (pc (higgsPacket C₀.toData (n (φ k)) (y' (φ k))) z) +
            ΘV (pc (coframeM (y' (φ k))) z) *
              potential (bankData C₀.toData Tj (θs (φ k))) (pc (higgs (y' (φ k))) z))
          (fun z => ΘF (H.e₀ z) (fun μ ν => F μ ν z) (fun μ ν => F μ ν z) +
            ΘK (H.e₀ z) (fun μ => P.K₀ μ z) (fun μ => P.K₀ μ z) +
            ΘV (H.e₀ z) * potential (bankData C₀.toData Tj θ) (P.H₀ z))) := by
  obtain ⟨εc, hεc, εstar, hεs, H⟩ := determinant_resolved_of_rootedNorm C₀
    NativeRecordNormSM.GSM hG hρH Tj hT StandardModelCoulomb.toESM FiniteWilsonClosure.rootedNorm_SM
    M hM Θ Θ' star_Zc Zc_central cUg_Zc_mem_GSM
  refine ⟨εc, hεc, εstar, hεs, fun n _ y θs hn U hUe hUK hplaq hflux c hc t o w hadm hplaqV hcert
    Ke hKe hpos hval cm hcm hmar hTBe hTBq hrec hFb hKb BH hHb hΩF hΩK B hΨ hKs hΨb hKbd Kθ hKθ
    hθK hphys hY hF5 => ?_⟩
  have hP' : ∀ k x μ ν,
      ‖NativeScaling.gaugePlaquette (n k : ℝ)⁻¹ (NativeDensity.gauge (y k)) x μ ν - 1‖ < 1 :=
    fun k x μ ν => by rw [gaugePlaquette_eq_litPlaq_SM (hUe k)]; exact hplaq k μ ν x
  have S := curvatureScreen_of_records n hn y U hUK hUe hP' (fun k => adUnit_of_links (hUe k))
    hFb hΩF
  obtain ⟨g, y', hgK, hIG, b, hgauge, hcod, hsm, rest⟩ := H n y θs hn U hUe hUK hplaq t
    (fun k => detCoord (n k) (U k) (c k)) (fun ψ hψ => detCoord_precompact hUK S hflux c hc ψ hψ)
    o w hadm hplaqV hcert Ke hKe hpos hval cm hcm hmar hTBe hTBq hrec hFb hKb BH hHb hΩF hΩK B
    hΨ hKs hΨb hKbd Kθ hKθ hθK hphys hY hF5
  have hdiv := eventually_gridDiv_detCoord hUK S hflux c
  refine ⟨g, y', hgK, hIG, b, hgauge, hcod, hsm, hdiv, ?_, rest⟩
  filter_upwards [hdiv] with k hk
  funext x
  have e : NativeYMBridge.gaugeArr (y' k) =
      fun x μ => b k μ x + detCoord (n k) (U k) (c k) μ x • Zc :=
    funext fun x => funext fun μ => hgauge k μ x
  rw [e, codiffT_combined, hcod k, hk x, mul_zero, zero_smul, sub_zero]

set_option maxHeartbeats 12800000 in
-- the flat normalization of the remainder and the generic assembly
/-- **`cor:determinant-resolved-closure`, exact-flatness alternative** ("`eq:semisimple-only-
certificate` may be replaced by exact flatness of `V_h`; in that case its semisimple cycle
holonomies also need not be small"; Standard-Model gauge group, unit-torus rendering).  Under
`(F1)`, `(F3)`, `(F4)`, `(F5)`, zero determinant flux for small `h`, and **exact flatness** of the
`G_ss`-valued remainder `V_h` (`χ(V_h) = 1`, all plaquettes trivial; no smallness of any
holonomy), actual `G_SM` site gauges `g_h = q_h e^{t_h Z_c}` (`q_h` the `G_ss` gauge of
`lem:flat-semisimple-normalization`) put the records in the form `A_h = β_h + Z_c a_h` with
**constant**, pairwise commuting, uniformly bounded (not small) `β_h`, eventually `δ_h A_h = 0`,
and, after extraction, all the convergence and variational conclusions of
`thm:finite-Wilson-zero-defect` hold. -/
theorem determinant_resolved_closure_flat_SM (C₀ : CovData SMAlg (EuclideanSpace ℝ (Fin rH)) 𝓢)
    (hG : ∀ u ∈ NativeRecordNormSM.GSM, Unitary.toUnits u ∈ C₀.G)
    (hρH : ∀ k ∈ C₀.G, ∀ v : EuclideanSpace ℝ (Fin rH), ‖C₀.ρH k v‖ = ‖v‖)
    (Tj : Fin J → SMAlg →L[ℝ] E)
    (hT : ∀ g ∈ C₀.G, ∀ j (X Y : SMAlg),
      ⟪Tj j ((g : SMAlg) * X * ↑g⁻¹), Tj j ((g : SMAlg) * Y * ↑g⁻¹)⟫ = ⟪Tj j X, Tj j Y⟫)
    (M : MassMetric SMAlg (EuclideanSpace ℝ (Fin rH))) (hM : M.Invariant C₀)
    (Θ : 𝓢 ≃L[ℝ] EuclideanSpace ℝ (Fin r)) (Θ' : CoSpinor 𝓢 ≃L[ℝ] EuclideanSpace ℝ (Fin r')) :
    ∀ (n : ℕ → ℕ) [∀ k, NeZero (n k)]
      (y : ∀ k, Grid (n k) → Field SMAlg (EuclideanSpace ℝ (Fin rH)) 𝓢)
      (θs : ℕ → Bank J (EuclideanSpace ℝ (Fin rH)) 𝓢), Tendsto n atTop atTop →
      -- the unitary internal links of the records, in the logarithm chart
      ∀ (U : ∀ k, Grid (n k) × Fin 4 → unitary SMAlg)
        (hUe : ∀ k x μ, (U k (x, μ) : SMAlg) = exp ((n k : ℝ)⁻¹ • NativeDensity.gauge (y k) μ x))
        (hUK : ∀ k e, U k e ∈ NativeRecordNormSM.GSM),
      (∀ k μ ν x, ‖RootedCoulomb.litPlaq (U k) μ ν x - 1‖ < 1) →
      -- zero determinant flux for all sufficiently small `h`
      (∀ᶠ k in atTop, ∀ μ ν,
        DeterminantFlux.planeFlux (fun x μ => ((U k (x, μ) : SMAlg).2).det) 0 μ ν = 0) →
      -- the determinant normalization: cycle constants and site phases
      ∀ (c : ℕ → Fin 4 → ℝ), (∀ k μ, |c k μ| ≤ Real.pi) → ∀ (t : ∀ k, Grid (n k) → ℝ),
      -- the remainder is `G_ss`-valued (`χ(V_h) = 1`, the determinant normalization) and flat
      (∀ k e, (((splitVg star_Zc (n k : ℝ)⁻¹ (t k) (detCoord (n k) (U k) (c k)) (U k) e :
        unitary SMAlg) : SMAlg).1).det = 1) →
      (∀ k e, (((splitVg star_Zc (n k : ℝ)⁻¹ (t k) (detCoord (n k) (U k) (c k)) (U k) e :
        unitary SMAlg) : SMAlg).2).det = 1) →
      (∀ k μ ν x, RootedCoulomb.litPlaq
        (splitVg star_Zc (n k : ℝ)⁻¹ (t k) (detCoord (n k) (U k) (c k)) (U k)) μ ν x = 1) →
      -- `(F1)`
      ∀ (Ke : Set M4), IsCompact Ke → (∀ M ∈ Ke, 0 < Matrix.det (show Mat from M)) →
      (∀ k x, coframeM (y k) x ∈ Ke) → ∀ cm : ℝ, cm ≤ 1 / 64 →
      (∀ k x μ, (n k : ℝ)⁻¹ * ‖ωM (y k) μ x‖ ≤ cm) →
      TotallyBounded (range fun k => pcLp (coframeM (y k))) →
      TotallyBounded (range fun k => pcLp (fun x lam => qM (y k) lam x)) →
      (∀ k z, NativeTrigRec.recon (coframeM (y k)) z ∈ Ke) →
      -- `(F3)`
      (∃ B, ∀ k, gridNorm (curvPacket (n k) (y k)) ≤ B) →
      (∃ B, ∀ k, gridNorm (higgsPacket C₀.toData (n k) (y k)) ≤ B) →
      ∀ BH : ℝ, (∀ k, gridNorm (higgs (y k)) ≤ BH) →
      (∀ ε > 0, ∃ ρ > 0, ∀ᶠ k in atTop, ∀ (μ : Fin 4) (m : ℕ), 0 < m → (m : ℝ) / n k ≤ ρ →
        gridNorm (wilsonShiftR (adLinks (n k) (y k) (adUnit_of_links (hUe k))) μ m
          (curvPacket (n k) (y k)) - curvPacket (n k) (y k)) ≤ ε) →
      (∀ ε > 0, ∃ ρ > 0, ∀ᶠ k in atTop, ∀ (μ : Fin 4) (m : ℕ), 0 < m → (m : ℝ) / n k ≤ ρ →
        gridNorm (wilsonShiftR (higgsLinks C₀.toData (n k) (y k)
            (higgsUnit_of_links C₀ NativeRecordNormSM.GSM hG hρH (hUe k) (hUK k))) μ m
          (higgsPacket C₀.toData (n k) (y k)) - higgsPacket C₀.toData (n k) (y k)) ≤ ε) →
      -- `(F4)`
      ∀ B : ℝ, (∀ k, gridNorm (psi (y k)) ≤ B) →
      (∀ k μ, gridNorm (fun x => spinGraph C₀.toData (n k : ℝ)⁻¹ (y k) x μ) ≤ B) →
      (∀ k, gridNorm (psiBar (y k)) ≤ B) →
      (∀ k μ, gridNorm (fun x => dualGraph C₀.toData (n k : ℝ)⁻¹ (y k) x μ) ≤ B) →
      ∀ (Kθ : Set (ℝ × ℝ × ℝ × ℝ × (Fin J → ℝ) ×
          (EuclideanSpace ℝ (Fin rH) →L[ℝ] Spin 𝓢))), IsCompact Kθ →
      (∀ k, bankVec (θs k) ∈ Kθ) → (∀ v ∈ Kθ, v.1 ≠ 0 ∧ ∀ j, 0 ≤ v.2.2.2.2.1 j) →
      ∀ (hY : ∀ k, ∀ g ∈ C₀.G, ∀ H : EuclideanSpace ℝ (Fin rH),
        (θs k).Y (C₀.ρH g H) = C₀.ρS g * (θs k).Y H * C₀.ρS ↑g⁻¹),
      -- `(F5)`
      Tendsto (fun k => covNormP (bankCov C₀ Tj (θs k) hT (hY k)) M (n k : ℝ)⁻¹
        (toLinks (n k : ℝ)⁻¹ (y k))) atTop (𝓝 0) →
      ∃ g : ∀ k, Grid (n k) → SMAlgˣ, ∃ y' : ∀ k, Grid (n k) → Field SMAlg (EuclideanSpace ℝ (Fin rH)) 𝓢,
      (∀ k x, ∃ u ∈ NativeRecordNormSM.GSM, g k x = Unitary.toUnits u) ∧
      (∀ k, IsGaugeTransform C₀ (n k : ℝ)⁻¹ (g k) (y k) (y' k)) ∧
      -- `eq:determinant-combined-connection`: only `b` is small
      ∃ β : ℕ → Fin 4 → SMAlg,
      (∀ k μ x, NativeDensity.gauge (y' k) μ x = β k μ + detCoord (n k) (U k) (c k) μ x • Zc) ∧
      (∀ k μ ν, Commute (β k μ) (β k ν)) ∧ (∃ Mβ, ∀ k μ, ‖β k μ‖ ≤ Mβ) ∧
      -- the determinant potential and the full logarithmic connection are co-closed
      (∀ᶠ k in atTop, ∀ x,
        DeterminantFlux.gridDiv (fun x μ => detCoord (n k) (U k) (c k) μ x) x = 0) ∧
      (∀ᶠ k in atTop, NativeCoulomb.codiffT
        (StandardModelCoulomb.toESM : SMAlg →L[ℝ] StandardModelCoulomb.SMEuc)
        (NativeYMBridge.gaugeArr (y' k)) = 0) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ H : CoHyp (fun k => n (φ k)) (fun k => y' (φ k)),
      H.Ke = Ke ∧
      ∃ θ : Bank J (EuclideanSpace ℝ (Fin rH)) 𝓢, BankConv (fun k => θs (φ k)) θ ∧
      ∃ F : Fin 4 → Fin 4 → 𝕋 → SMAlg, ∃ G : Fin 4 → Fin 4 → 𝕋 → SMAlg,
      ∃ P : HiggsHyp (bankData C₀.toData Tj θ) (fun k => y' (φ k)),
      ∃ S : SpinHyp (κid 𝓢) (fun k => y' (φ k)), ∃ u₀ : 𝕋 → Dif 𝓢 (CoSpinor 𝓢),
      -- `eq:Wilson-strong-convergence`
      (∀ μ ν, LpTendsto volume 2 (fun k => pc (fun x =>
        NativeScaling.fieldStrength (n (φ k) : ℝ)⁻¹ (NativeDensity.gauge (y' (φ k))) x μ ν))
        (F μ ν)) ∧
      (∀ μ ν, LpTendsto volume 2
        (fun k => pc (NativeHiggs.DpV μ (NativeDensity.gauge (y' (φ k)) ν))) (G μ ν)) ∧
      (∀ μ ν, F μ ν =ᵐ[MeasureTheory.volume] NativeReconstructed.recCurv H.A₀ G μ ν) ∧
      (∀ μ, LpTendsto volume 2 (fun k => pc (NativeHiggs.DpV μ (higgs (y' (φ k)))))
        (fun z => P.K₀ μ z - C₀.ρHL (H.A₀ μ z) (P.H₀ z))) ∧
      (∀ j, ∃ fj : Lp ℂ 2 (MeasureTheory.volume : Measure 𝕋),
        ((fj : 𝕋 → ℂ) =ᵐ[MeasureTheory.volume] fun z => ((Θ (S.Ψ₀ z) j : ℝ) : ℂ)) ∧
        TorusSobolev.MemH 1 fj ∧ ∀ μ, (TorusSobolev.weakDeriv μ fj : 𝕋 → ℂ)
          =ᵐ[MeasureTheory.volume] fun z => ((Θ ((u₀ z).1 μ) j : ℝ) : ℂ)) ∧
      -- `eq:native-all-sector-limit` with the cutoff banks
      (∀ M : NNReal, ∀ ε > 0, ∀ᶠ k in atTop,
        ∀ τ : DTest SMAlg (EuclideanSpace ℝ (Fin rH)) 𝓢 (CoSpinor 𝓢), τ.norm ≤ M →
        |NativeAllSector.nativeVar (bankData C₀.toData Tj (θs (φ k))) (n (φ k)) (y' (φ k))
            (testRec (κid 𝓢) (n (φ k)) (y' (φ k)) τ) -
          NativeAllSector.contAllVar (bankData C₀.toData Tj θ) (κid 𝓢) (bankT Tj θ.w) H F P S u₀
            τ| ≤ ε) ∧
      -- consistency relative to the reconstructed fields
      (∀ M : NNReal, ∀ ε > 0, ∀ᶠ k in atTop,
        ∀ τ : DTest SMAlg (EuclideanSpace ℝ (Fin rH)) 𝓢 (CoSpinor 𝓢), τ.norm ≤ M →
        |NativeAllSector.nativeVar (bankData C₀.toData Tj (θs (φ k))) (n (φ k)) (y' (φ k))
            (testRec (κid 𝓢) (n (φ k)) (y' (φ k)) τ) -
          NativeReconstructed.recAllVar (bankData C₀.toData Tj θ) (κid 𝓢) (bankT Tj θ.w)
            (NativeTrigRec.recon (coframeM (y' (φ k))))
            (fun lam => NativeTrigRec.drecon lam (coframeM (y' (φ k))))
            (fun μ => NativeTrigRec.recon (NativeDensity.gauge (y' (φ k)) μ))
            (fun μ ν => NativeTrigRec.drecon μ (NativeDensity.gauge (y' (φ k)) ν))
            (NativeTrigRec.recon (higgs (y' (φ k))))
            (fun μ => NativeTrigRec.drecon μ (higgs (y' (φ k))))
            (NativeTrigRec.recon (psi (y' (φ k)))) (NativeTrigRec.recon (psiBar (y' (φ k))))
            (NativeTrigRec.recJets (y' (φ k))) τ| ≤ ε) ∧
      -- the distributional Einstein–Standard-Model equations
      (∀ τ : DTest SMAlg (EuclideanSpace ℝ (Fin rH)) 𝓢 (CoSpinor 𝓢),
        NativeAllSector.contAllVar (bankData C₀.toData Tj θ) (κid 𝓢) (bankT Tj θ.w) H F P S u₀ τ
          = 0) ∧
      -- the bosonic stress densities
      (∀ (ΘF : M4 → (Fin 4 → Fin 4 → SMAlg) →L[ℝ] (Fin 4 → Fin 4 → SMAlg) →L[ℝ] ℝ)
        (ΘK : M4 → (Fin 4 → EuclideanSpace ℝ (Fin rH)) →L[ℝ]
          (Fin 4 → EuclideanSpace ℝ (Fin rH)) →L[ℝ] ℝ) (ΘV : M4 → ℝ),
        ContinuousOn ΘF Ke → ContinuousOn ΘK Ke → ContinuousOn ΘV Ke →
        LpTendsto volume 1
          (fun k z => ΘF (pc (coframeM (y' (φ k))) z) (pc (curvPacket (n (φ k)) (y' (φ k))) z)
              (pc (curvPacket (n (φ k)) (y' (φ k))) z) +
            ΘK (pc (coframeM (y' (φ k))) z)
              (pc (higgsPacket C₀.toData (n (φ k)) (y' (φ k))) z)
              (pc (higgsPacket C₀.toData (n (φ k)) (y' (φ k))) z) +
            ΘV (pc (coframeM (y' (φ k))) z) *
              potential (bankData C₀.toData Tj (θs (φ k))) (pc (higgs (y' (φ k))) z))
          (fun z => ΘF (H.e₀ z) (fun μ ν => F μ ν z) (fun μ ν => F μ ν z) +
            ΘK (H.e₀ z) (fun μ => P.K₀ μ z) (fun μ => P.K₀ μ z) +
            ΘV (H.e₀ z) * potential (bankData C₀.toData Tj θ) (P.H₀ z))) := by
  intro n _ y θs hn U hUe hUK hplaq hflux c hc t h1 h2 hflat Ke hKe hpos hval cm hcm hmar hTBe
    hTBq hrec hFb hKb BH hHb hΩF hΩK B hΨ hKs hΨb hKbd Kθ hKθ hθK hphys hY hF5
  have hP' : ∀ k x μ ν,
      ‖NativeScaling.gaugePlaquette (n k : ℝ)⁻¹ (NativeDensity.gauge (y k)) x μ ν - 1‖ < 1 :=
    fun k x μ ν => by rw [gaugePlaquette_eq_litPlaq_SM (hUe k)]; exact hplaq k μ ν x
  have S := curvatureScreen_of_records n hn y U hUK hUe hP' (fun k => adUnit_of_links (hUe k))
    hFb hΩF
  -- the flat normalization of the remainder
  obtain ⟨b₃, b₂, gq, -, hcomm, hbd, hgq, -⟩ := FlatSemisimple.flat_semisimple_normalization_seq n
    one_pos (fun k x μ => toGss _ (h1 k (x, μ)) (h2 k (x, μ)))
    (fun k => isFlat_toGss (h1 k) (h2 k) (hflat k))
  set β : ℕ → Fin 4 → SMAlg := fun k μ => (b₃ k μ, b₂ k μ) with hβ
  have hβc : ∀ k μ ν, Commute (β k μ) (β k ν) := fun k μ ν =>
    Prod.ext (hcomm k μ ν).1.eq (hcomm k μ ν).2.eq
  -- a uniform bound (all norms on `M₃(ℂ) × M₂(ℂ)` are equivalent)
  let Lq : SMAlg ≃ₗ[ℝ] (Fin 3 → Fin 3 → ℂ) × (Fin 2 → Fin 2 → ℂ) :=
    ((Matrix.ofLinearEquiv ℝ).symm).prodCongr ((Matrix.ofLinearEquiv ℝ).symm)
  let Lc := Lq.toContinuousLinearEquiv
  have hMβ : ∀ k μ, ‖β k μ‖ ≤ ‖Lc.symm.toContinuousLinearMap‖ * (4 * Real.pi / 1) := by
    intro k μ
    have e : β k μ = Lc.symm (Lc (β k μ)) := (Lc.symm_apply_apply _).symm
    rw [e]
    refine (Lc.symm.toContinuousLinearMap.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
    rw [Prod.norm_def]
    refine max_le ?_ ?_
    · refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i =>
        (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
      exact (hbd k μ).1 i j
    · refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i =>
        (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
      exact (hbd k μ).2 i j
  have hWb : ∀ k μ (x : Grid (n k)), exp ((n k : ℝ)⁻¹ • β k μ) =
      ((gaugeLinks RootedCoulomb.latSrc RootedCoulomb.latTgt (fun x => fromGss (gq k x))
        (splitVg star_Zc (n k : ℝ)⁻¹ (t k) (detCoord (n k) (U k) (c k)) (U k)) (x, μ) :
          unitary SMAlg) : SMAlg) := by
    intro k μ x
    rw [gaugeLinks_fromGss (h1 k) (h2 k)]
    refine Prod.ext ?_ ?_
    · rw [fst_exp_SM, (hgq k x μ).1, ← Complex.coe_smul, one_div]
      rfl
    · rw [snd_exp_SM, (hgq k x μ).2, ← Complex.coe_smul, one_div]
      rfl
  have hev : ∀ᶠ k in atTop, ∀ μ (x : Grid (n k)), (n k : ℝ)⁻¹ * ‖β k μ‖ ≤ 1 / 1024 := by
    set Mβ := ‖Lc.symm.toContinuousLinearMap‖ * (4 * Real.pi / 1)
    have hM0 : 0 ≤ Mβ := (norm_nonneg _).trans (hMβ 0 0)
    have hev' : ∀ᶠ k in atTop, (1024 * Mβ : ℝ) ≤ n k :=
      (tendsto_natCast_atTop_atTop.comp hn).eventually (eventually_ge_atTop _)
    filter_upwards [hev'] with k hk μ x
    have hN : (0 : ℝ) < n k := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (n k))
    rw [inv_mul_le_iff₀ hN]
    nlinarith [hMβ k μ]
  obtain ⟨hbB, -, hbC⟩ := DeterminantResolved.bCompact_of_const n hn β hβc hMβ
  obtain ⟨g, y', hgK, hIG, hgauge, rest⟩ := determinant_resolved_post C₀ NativeRecordNormSM.GSM hG
    hρH Tj hT M hM Θ Θ' star_Zc Zc_central cUg_Zc_mem_GSM n y θs hn U hUe hUK hplaq t
    (fun k => detCoord (n k) (U k) (c k)) (fun ψ hψ => detCoord_precompact hUK S hflux c hc ψ hψ)
    (fun k x => fromGss (gq k x)) (fun k μ _ => β k μ) (fun k x => fromGss_mem_GSM _) hWb hbB hev
    hbC Ke hKe hpos hval cm hcm hmar hTBe hTBq hrec hFb hKb BH hHb hΩF hΩK B hΨ hKs hΨb hKbd
    Kθ hKθ hθK hphys hY hF5
  have hdiv := eventually_gridDiv_detCoord hUK S hflux c
  refine ⟨g, y', hgK, hIG, β, hgauge, hβc, ⟨_, hMβ⟩, hdiv, ?_, rest⟩
  filter_upwards [hdiv] with k hk
  funext x
  have e : NativeYMBridge.gaugeArr (y' k) =
      fun x μ => (fun μ (_ : Grid (n k)) => β k μ) μ x + detCoord (n k) (U k) (c k) μ x • Zc :=
    funext fun x => funext fun μ => hgauge k μ x
  have hc0 : NativeCoulomb.codiffT
      (StandardModelCoulomb.toESM : SMAlg →L[ℝ] StandardModelCoulomb.SMEuc)
      (fun x μ => (fun μ (_ : Grid (n k)) => β k μ) μ x) = 0 := by
    funext z
    simp [NativeCoulomb.codiffT, periodicHodgeCodiff, periodicHodgeBwd]
  rw [e, codiffT_combined, hc0, hk x, mul_zero, zero_smul, sub_zero]

end MainSM


end

end RenewalGeometry.DeterminantResolvedSM
