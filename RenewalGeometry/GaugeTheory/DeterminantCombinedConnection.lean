/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Action.NativeScalingBlocksExact
import RenewalGeometry.Action.ShiftedFirstJetNormalFormExact
import RenewalGeometry.Algebra.SeriesLogChart
import RenewalGeometry.GaugeTheory.DeterminantSemisimpleSplitExact

/-!
# The determinant-combined connection `A_h = b_h + Z_c a_h` (`eq:determinant-combined-connection`)

The finite-algebra content of the combined-connection identity of `cor:determinant-resolved-closure`
(Einstein–SM action-closure manuscript, subsection "Determinant-resolved closure"): "Since `Z_c` is
central, adding `Z_c a_h` preserves the Coulomb condition and introduces no mixed curvature
commutator.  The normalized actual links are exactly `e^{h b_h} e^{h Z_c a_h} = e^{h A_h}` …  The
full literal curvature is the sum of the semisimple curvature and `Z_c f_h`."

Generic part (any complete normed real algebra `𝔸`, a element `Z` commuting with all values of the
semisimple connection `b`, a real potential `a`; the grid `(ℤ/n)⁴` with mesh `h`):

* `exp_combined`: `e^{h(b + aZ)} = e^{hb} e^{haZ}`;
* `gaugePlaquette_combined` (**no mixed commutator**): the literal plaquette of `A = b + aZ` is
  `P(A) = P(b) · e^{h² f Z}`, `f = D⁺_μ a_ν - D⁺_ν a_μ` the Abelian curvature of `a`;
* `codiff_combined`, `codiff_combined_eq_zero` (**Coulomb condition preserved**):
  `δ_h(b + aZ) = δ_h b + (δ_h a) Z`, so `δ_h b = δ_h a = 0` gives `δ_h A = 0`;
* `fieldStrength_combined` (**curvature split**): on the logarithm chart,
  `F^h(A) = F^h(b) + f Z` for the literal logarithmic curvature
  `F^h = h⁻² log(plaquette)` (`NativeScaling.fieldStrength`).

Concrete part: `G_SM = S(U(3) × U(2))`, `Z_c = (-i/3 I₃, i/2 I₂)` (`DeterminantSplit.Zc`) in the
pair algebra `M₃(ℂ) × M₂(ℂ)` with the `L²` operator norm: `Z_c` is central (`commute_Zc`), so the
generic identities hold for every semisimple connection `b`; `e^{s Z_c}` is the central
one-parameter subgroup `DeterminantSplit.centralElem s` (`exp_Zc_pair`), whose determinant
character is `e^{is}` (`DeterminantSplit.smChi_centralElem`).
-/

open NormedSpace Finset

namespace RenewalGeometry.DeterminantCombined

open ShiftedJetAction (Grid unitVec fwdDiff)

noncomputable section

/-! ### Generic central combinations -/

section Generic

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
variable {n : ℕ} [NeZero n]

/-- The combined connection `A = b + a Z`. -/
def combined (b : Fin 4 → Grid n → 𝔸) (Z : 𝔸) (a : Fin 4 → Grid n → ℝ) :
    Fin 4 → Grid n → 𝔸 := fun μ x => b μ x + a μ x • Z

/-- The Abelian curvature `f = D⁺_μ a_ν - D⁺_ν a_μ` of the potential. -/
def abelCurv (h : ℝ) (a : Fin 4 → Grid n → ℝ) (x : Grid n) (μ ν : Fin 4) : ℝ :=
  fwdDiff h μ (a ν) x - fwdDiff h ν (a μ) x

/-- The discrete co-differential `δ_h A = Σ_μ D⁻_μ A_μ`. -/
def codiff {V : Type*} [AddCommGroup V] [Module ℝ V] (h : ℝ) (A : Fin 4 → Grid n → V)
    (x : Grid n) : V :=
  ∑ μ, ShiftedFirstJet.bwdDiff h μ (A μ) x

/-- **Coulomb condition preserved**: `δ_h(b + aZ) = δ_h b + (δ_h a) Z`. -/
theorem codiff_combined (h : ℝ) (b : Fin 4 → Grid n → 𝔸) (Z : 𝔸) (a : Fin 4 → Grid n → ℝ)
    (x : Grid n) : codiff h (combined b Z a) x = codiff h b x + codiff h a x • Z := by
  simp only [codiff, combined, ShiftedFirstJet.bwdDiff, Finset.sum_smul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  simp only [smul_sub, sub_smul, smul_add, smul_smul]
  module

theorem codiff_combined_eq_zero (h : ℝ) (b : Fin 4 → Grid n → 𝔸) (Z : 𝔸)
    (a : Fin 4 → Grid n → ℝ) (hb : ∀ x, codiff h b x = 0) (ha : ∀ x, codiff h a x = 0) (x : Grid n) :
    codiff h (combined b Z a) x = 0 := by
  rw [codiff_combined, hb, ha, zero_smul, add_zero]

/-- `e^{h(b + aZ)} = e^{hb} e^{haZ}` for `Z` commuting with `b`. -/
theorem exp_combined (h a : ℝ) {b Z : 𝔸} (hc : Commute b Z) :
    exp (h • (b + a • Z)) = exp (h • b) * exp ((h * a) • Z) := by
  rw [smul_add, smul_smul]
  exact MatrixExpDerivative.exp_add_of_commute' ((hc.smul_left h).smul_right (h * a))

theorem exp_neg_combined (h a : ℝ) {b Z : 𝔸} (hc : Commute b Z) :
    exp (-(h • (b + a • Z))) = exp (-(h • b)) * exp (-((h * a) • Z)) := by
  rw [smul_add, smul_smul, neg_add]
  exact MatrixExpDerivative.exp_add_of_commute' (((hc.smul_left h).smul_right (h * a)).neg_left.neg_right)

theorem exp_smul_mul_exp_smul (s t : ℝ) (Z : 𝔸) : exp (s • Z) * exp (t • Z) = exp ((s + t) • Z) := by
  rw [add_smul, MatrixExpDerivative.exp_add_of_commute' ((Commute.refl Z).smul_left s |>.smul_right t)]

/-- **No mixed curvature commutator**: the literal plaquette of `A = b + aZ` is
`P(A) = P(b) · e^{h² f Z}`. -/
theorem gaugePlaquette_combined {h : ℝ} (hh : h ≠ 0) (b : Fin 4 → Grid n → 𝔸) {Z : 𝔸}
    (hc : ∀ μ x, Commute (b μ x) Z) (a : Fin 4 → Grid n → ℝ) (x : Grid n) (μ ν : Fin 4) :
    NativeScaling.gaugePlaquette h (combined b Z a) x μ ν =
      NativeScaling.gaugePlaquette h b x μ ν * exp ((h ^ 2 * abelCurv h a x μ ν) • Z) := by
  unfold NativeScaling.gaugePlaquette combined
  rw [exp_combined h _ (hc μ x), exp_combined h _ (hc ν _), exp_neg_combined h _ (hc μ _),
    exp_neg_combined h _ (hc ν x)]
  set E1 := exp (h • b μ x)
  set E2 := exp (h • b ν (x + unitVec n μ))
  set E3 := exp (-(h • b μ (x + unitVec n ν)))
  set E4 := exp (-(h • b ν x))
  set Z1 := exp ((h * a μ x) • Z)
  set Z2 := exp ((h * a ν (x + unitVec n μ)) • Z)
  set Z3 := exp (-((h * a μ (x + unitVec n ν)) • Z))
  set Z4 := exp (-((h * a ν x) • Z))
  have hZE : ∀ (s : ℝ) (w : 𝔸), Commute w Z → Commute (exp (s • Z)) (exp w) := fun s w hw =>
    ((hw.smul_right s).symm).exp
  have c12 : Z1 * E2 = E2 * Z1 := (hZE _ _ ((hc ν _).smul_left h)).eq
  have hZ3 : Z3 = exp ((-(h * a μ (x + unitVec n ν))) • Z) := by rw [neg_smul]
  have hZ4 : Z4 = exp ((-(h * a ν x)) • Z) := by rw [neg_smul]
  have hZ12 : Z1 * Z2 = exp ((h * a μ x + h * a ν (x + unitVec n μ)) • Z) :=
    exp_smul_mul_exp_smul _ _ Z
  have c3 : Commute (exp ((h * a μ x + h * a ν (x + unitVec n μ)) • Z)) E3 :=
    hZE _ _ ((hc μ _).smul_left h).neg_left
  have hZ123 : Z1 * Z2 * Z3 = exp ((h * a μ x + h * a ν (x + unitVec n μ) +
      -(h * a μ (x + unitVec n ν))) • Z) := by
    rw [hZ12, hZ3, exp_smul_mul_exp_smul]
  have c4 : Commute (exp ((h * a μ x + h * a ν (x + unitVec n μ) +
      -(h * a μ (x + unitVec n ν))) • Z)) E4 := hZE _ _ ((hc ν x).smul_left h).neg_left
  have hZ1234 : Z1 * Z2 * Z3 * Z4 = exp ((h ^ 2 * abelCurv h a x μ ν) • Z) := by
    rw [hZ123, hZ4, exp_smul_mul_exp_smul]
    congr 2
    unfold abelCurv ShiftedJetAction.fwdDiff
    simp only [smul_eq_mul]
    field_simp
    ring
  rw [← hZ1234]
  calc E1 * Z1 * (E2 * Z2) * (E3 * Z3) * (E4 * Z4)
      = E1 * E2 * (Z1 * Z2) * (E3 * Z3) * (E4 * Z4) := by
        rw [show E1 * Z1 * (E2 * Z2) = E1 * (Z1 * E2) * Z2 by noncomm_ring, c12]; noncomm_ring
    _ = E1 * E2 * E3 * (Z1 * Z2 * Z3) * (E4 * Z4) := by
        rw [hZ12]
        rw [show E1 * E2 * exp ((h * a μ x + h * a ν (x + unitVec n μ)) • Z) * (E3 * Z3) =
          E1 * E2 * (exp ((h * a μ x + h * a ν (x + unitVec n μ)) • Z) * E3) * Z3 by noncomm_ring,
          c3.eq, ← hZ12]
        noncomm_ring
    _ = E1 * E2 * E3 * E4 * (Z1 * Z2 * Z3 * Z4) := by
        rw [hZ123]
        rw [show E1 * E2 * E3 * exp ((h * a μ x + h * a ν (x + unitVec n μ) +
            -(h * a μ (x + unitVec n ν))) • Z) * (E4 * Z4) =
          E1 * E2 * E3 * (exp ((h * a μ x + h * a ν (x + unitVec n μ) +
            -(h * a μ (x + unitVec n ν))) • Z) * E4) * Z4 by noncomm_ring, c4.eq, ← hZ123]
        noncomm_ring

/-- A central element commutes with the chart logarithm of anything it commutes with. -/
theorem commute_logOneAdd [NormOneClass 𝔸] {z Z : 𝔸} (hz : ‖z‖ < 1) (hc : Commute z Z) :
    Commute (ShiftedPlaquette.logOneAdd z) Z := by
  rw [← (SeriesLogChart.hasSum_logOneAdd hz).tsum_eq]
  exact Commute.tsum_left Z fun n => (hc.pow_left (n + 1)).smul_left _

/-- **Curvature split** (`eq:determinant-combined-connection`): on the logarithm chart, the literal
logarithmic curvature of `A = b + aZ` is `F^h(A) = F^h(b) + f Z`. -/
theorem fieldStrength_combined [NormOneClass 𝔸] {h : ℝ} (hh : h ≠ 0)
    (b : Fin 4 → Grid n → 𝔸) {Z : 𝔸} (hc : ∀ μ x, Commute (b μ x) Z) (a : Fin 4 → Grid n → ℝ)
    (x : Grid n) (μ ν : Fin 4)
    (hP : ‖NativeScaling.gaugePlaquette h b x μ ν - 1‖ < 1)
    (hsum : ‖SeriesLogChart.logChart (NativeScaling.gaugePlaquette h b x μ ν) +
      (h ^ 2 * abelCurv h a x μ ν) • Z‖ ≤ 1 / 8)
    (hPA : ‖NativeScaling.gaugePlaquette h (combined b Z a) x μ ν - 1‖ ≤ 1 / 16) :
    NativeScaling.fieldStrength h (combined b Z a) x μ ν =
      NativeScaling.fieldStrength h b x μ ν + abelCurv h a x μ ν • Z := by
  set P := NativeScaling.gaugePlaquette h b x μ ν
  set W := (h ^ 2 * abelCurv h a x μ ν) • Z
  have hPZ : Commute P Z := by
    unfold P NativeScaling.gaugePlaquette
    have e : ∀ w : 𝔸, Commute w Z → Commute (exp w) Z := fun w hw => hw.exp_left
    exact (((e _ ((hc μ x).smul_left h)).mul_left (e _ ((hc ν _).smul_left h))).mul_left
      (e _ ((hc μ _).smul_left h).neg_left)).mul_left (e _ ((hc ν x).smul_left h).neg_left)
  have hlogP : Commute (SeriesLogChart.logChart P) W := by
    unfold SeriesLogChart.logChart
    exact (commute_logOneAdd hP ((hPZ.sub_left (Commute.one_left Z)))).smul_right _
  have hA : NativeScaling.gaugePlaquette h (combined b Z a) x μ ν = P * exp W :=
    gaugePlaquette_combined hh b hc a x μ ν
  -- the two logarithms have the same exponential
  have hexp1 : exp (SeriesLogChart.logChart (P * exp W)) = P * exp W :=
    SeriesLogChart.exp_logChart (by rw [← hA]; linarith)
  have hexp2 : exp (SeriesLogChart.logChart P + W) = P * exp W := by
    rw [MatrixExpDerivative.exp_add_of_commute' hlogP, SeriesLogChart.exp_logChart hP]
  have hsmall : ‖SeriesLogChart.logChart (P * exp W)‖ ≤ 1 / 8 := by
    refine (SeriesLogChart.norm_logChart_le (by rw [← hA]; linarith)).trans ?_
    rw [← hA]; linarith
  have hlog : SeriesLogChart.logChart (P * exp W) = SeriesLogChart.logChart P + W :=
    SeriesLogChart.exp_injective_of_norm_le hsmall hsum (hexp1.trans hexp2.symm)
  unfold NativeScaling.fieldStrength
  have e1 : ShiftedPlaquette.logOneAdd (NativeScaling.gaugePlaquette h (combined b Z a) x μ ν - 1) =
      SeriesLogChart.logChart (P * exp W) := by rw [hA]; rfl
  have e2 : ShiftedPlaquette.logOneAdd (P - 1) = SeriesLogChart.logChart P := rfl
  rw [e1, e2, hlog, smul_add, smul_smul, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 hh),
    one_mul]

end Generic

/-! ### `G_SM` and `Z_c = (-i/3 I₃, i/2 I₂)` -/

section StandardModel

open scoped Matrix.Norms.L2Operator

/-- The Lie-algebra pair space `M₃(ℂ) × M₂(ℂ)` with the `L²` operator norm (a complete normed
real algebra with `‖1‖ = 1`). -/
abbrev PairAlg := Matrix (Fin 3) (Fin 3) ℂ × Matrix (Fin 2) (Fin 2) ℂ

example : NormedRing PairAlg := inferInstance
example : NormedAlgebra ℝ PairAlg := inferInstance
example : NormOneClass PairAlg := inferInstance
example : CompleteSpace PairAlg := inferInstance

/-- **`Z_c` is central**: it commutes with every element of the pair algebra (in particular with
every semisimple connection value). -/
theorem commute_Zc (X : PairAlg) : Commute (DeterminantSplit.Zc : PairAlg) X := by
  refine Prod.ext ?_ ?_
  · show (-(Complex.I / 3) • (1 : Matrix (Fin 3) (Fin 3) ℂ)) * X.1 =
      X.1 * (-(Complex.I / 3) • (1 : Matrix (Fin 3) (Fin 3) ℂ))
    rw [smul_mul_assoc, one_mul, mul_smul_comm, mul_one]
  · show ((Complex.I / 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) * X.2 =
      X.2 * ((Complex.I / 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ))
    rw [smul_mul_assoc, one_mul, mul_smul_comm, mul_one]

/-- `Z_c` is traceless (it lies in `𝔰(𝔲(3) ⊕ 𝔲(2))`). -/
theorem trace_Zc : Matrix.trace (DeterminantSplit.Zc.1) + Matrix.trace DeterminantSplit.Zc.2 = 0 := by
  simp only [DeterminantSplit.Zc, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin,
    smul_eq_mul]
  push_cast
  ring

/-- **`eq:determinant-combined-connection` for `G_SM`**: for every semisimple connection `b` and real
co-closed determinant potential `a`, the combined connection `A = b + Z_c a` has links
`e^{hA} = e^{hb} e^{haZ_c}`, plaquettes `P(A) = P(b) e^{h² f Z_c}`, co-differential
`δ_h A = δ_h b + (δ_h a) Z_c` (co-closed when both are), and, on the logarithm chart, curvature
`F^h(A) = F^h(b) + f Z_c`. -/
theorem determinant_combined_connection {n : ℕ} [NeZero n] {h : ℝ} (hh : h ≠ 0)
    (b : Fin 4 → Grid n → PairAlg) (a : Fin 4 → Grid n → ℝ) :
    (∀ μ x, exp (h • combined b DeterminantSplit.Zc a μ x) =
      exp (h • b μ x) * exp ((h * a μ x) • (DeterminantSplit.Zc : PairAlg))) ∧
    (∀ x μ ν, NativeScaling.gaugePlaquette h (combined b DeterminantSplit.Zc a) x μ ν =
      NativeScaling.gaugePlaquette h b x μ ν *
        exp ((h ^ 2 * abelCurv h a x μ ν) • (DeterminantSplit.Zc : PairAlg))) ∧
    (∀ x, codiff h (combined b DeterminantSplit.Zc a) x =
      codiff h b x + codiff h a x • (DeterminantSplit.Zc : PairAlg)) := by
  have hc : ∀ μ x, Commute (b μ x) (DeterminantSplit.Zc : PairAlg) := fun μ x =>
    (commute_Zc (b μ x)).symm
  exact ⟨fun μ x => exp_combined h (a μ x) (hc μ x), fun x μ ν =>
    gaugePlaquette_combined hh b hc a x μ ν, fun x => codiff_combined h b _ a x⟩

end StandardModel

end

end RenewalGeometry.DeterminantCombined
