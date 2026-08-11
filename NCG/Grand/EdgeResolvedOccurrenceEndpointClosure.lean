/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ExactSourceSchurResidual

/-!
# Edge-resolved occurrence and endpoint-source closure

This file formalizes the exact endpoint-export half of
thm:SM-occurrence-endpoint-closure.  Scaling a three-column chronological
source with Gram 4 alpha I by sqrt(m/alpha) gives the canonical occurrence
source.  Both displayed Grams, the zero Moore--Penrose Schur residual, the
literal-source equality criterion, and the exact Hilbert--Schmidt distance are
proved.
-/

open Matrix
open scoped ComplexOrder

namespace NCG
namespace EdgeResolvedOccurrenceEndpointClosure

noncomputable section

/-- Real Choi mass of a finite positive branch. -/
def choiMass {n : Type*} [Fintype n] (J : Matrix n n ℂ) : ℝ :=
  (Matrix.trace J).re

theorem choiMass_nonneg_and_zero_iff
    {n : Type*} [Fintype n] [DecidableEq n]
    (J : Matrix n n ℂ) (hJ : J.PosSemidef) :
    0 ≤ choiMass J ∧ (choiMass J = 0 ↔ J = 0) := by
  have hself : star (Matrix.trace J) = Matrix.trace J := by
    rw [← Matrix.trace_conjTranspose, hJ.isHermitian]
  have him : (Matrix.trace J).im = 0 := by
    have hi := congrArg Complex.im hself
    change -(Matrix.trace J).im = (Matrix.trace J).im at hi
    linarith
  have hnonnegComplex := hJ.trace_nonneg
  have hnonneg : 0 ≤ choiMass J := by
    exact (Complex.nonneg_iff.mp hnonnegComplex).1
  refine ⟨hnonneg, ?_⟩
  constructor
  · intro hm
    apply hJ.trace_eq_zero_iff.mp
    apply Complex.ext
    · simpa [choiMass] using hm
    · simpa using him
  · rintro rfl
    simp [choiMass]

/-- Covariance under unitary conjugacy makes all twelve ordered-edge Choi
branches have the same mass; positivity gives the exact nonzero equivalences. -/
theorem covariantOrderedEdgeChoiMasses
    {Edge n : Type*} [Fintype Edge] [Nonempty Edge]
    [Fintype n] [DecidableEq n]
    (J : Edge → Matrix n n ℂ)
    (hcard : Fintype.card Edge = 12)
    (hpsd : ∀ e, (J e).PosSemidef)
    (hcov : ∀ e f : Edge, ∃ U : Matrix n n ℂ,
      Uᴴ * U = 1 ∧ J f = U * J e * Uᴴ) :
    (∀ e f, choiMass (J e) = choiMass (J f)) ∧
    (∀ e, choiMass (∑ f, J f) = 12 * choiMass (J e)) ∧
    (∀ e, choiMass (J e) > 0 ↔
      (∑ f, J f) ≠ 0) ∧
    (∀ e, choiMass (J e) > 0 ↔ ∀ f, J f ≠ 0) := by
  have htrace : ∀ e f, Matrix.trace (J e) = Matrix.trace (J f) := by
    intro e f
    obtain ⟨U, hU, hconj⟩ := hcov e f
    symm
    rw [hconj, Matrix.trace_mul_cycle, hU, Matrix.one_mul]
  have hmass : ∀ e f, choiMass (J e) = choiMass (J f) := by
    intro e f
    exact congrArg Complex.re (htrace e f)
  have hsumPsd : (∑ f, J f).PosSemidef :=
    Matrix.posSemidef_sum Finset.univ fun i _ => hpsd i
  have htotal : ∀ e, choiMass (∑ f, J f) = 12 * choiMass (J e) := by
    intro e
    unfold choiMass
    rw [Matrix.trace_sum]
    simp_rw [htrace _ e]
    simp [hcard]
  have hmassPos : ∀ e, choiMass (J e) > 0 ↔ J e ≠ 0 := by
    intro e
    obtain ⟨hne, hzero⟩ := choiMass_nonneg_and_zero_iff (J e) (hpsd e)
    constructor
    · intro hp hJ0
      rw [hJ0] at hp
      simp [choiMass] at hp
    · intro hJ0
      have hmne : choiMass (J e) ≠ 0 := mt hzero.mp hJ0
      exact lt_of_le_of_ne hne (Ne.symm hmne)
  have hsumPos :
      choiMass (∑ f, J f) > 0 ↔ (∑ f, J f) ≠ 0 := by
    obtain ⟨hne, hzero⟩ :=
      choiMass_nonneg_and_zero_iff (∑ f, J f) hsumPsd
    constructor
    · intro hp hJ0
      rw [hJ0] at hp
      simp [choiMass] at hp
    · intro hJ0
      have hmne : choiMass (∑ f, J f) ≠ 0 := mt hzero.mp hJ0
      exact lt_of_le_of_ne hne (Ne.symm hmne)
  refine ⟨hmass, htotal, ?_, ?_⟩
  · intro e
    rw [← hsumPos, htotal e]
    constructor <;> intro hp <;> nlinarith
  · intro e
    constructor
    · intro hp f
      exact (hmassPos f).mp (by rwa [hmass f e])
    · intro hall
      exact (hmassPos e).mpr (hall e)

/-- A nonzero rank-one Choi matrix determines its Kraus vector up to a unit
complex phase.  This is the coordinate-free content of the rank-one branch
clause in the occurrence-endpoint closure theorem. -/
theorem krausVector_unique_up_to_phase
    {n : Type*} [Fintype n] [DecidableEq n]
    (v w : n → ℂ) (hv : v ≠ 0)
    (hchoi : Matrix.vecMulVec v (star v) =
      Matrix.vecMulVec w (star w)) :
    ∃ phase : ℂ, ‖phase‖ = 1 ∧ w = phase • v := by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hv (funext hall)
  let phase : ℂ := w i / v i
  have hdiag := congrFun (congrFun hchoi i) i
  have hnormSq : Complex.normSq (v i) = Complex.normSq (w i) := by
    simpa [Matrix.vecMulVec_apply, Complex.mul_conj] using hdiag
  have hphaseNormSq : Complex.normSq phase = 1 := by
    dsimp only [phase]
    rw [Complex.normSq_div, ← hnormSq]
    exact div_self (mt Complex.normSq_eq_zero.mp hi)
  have hphaseNorm : ‖phase‖ = 1 := by
    have hsquare : ‖phase‖ ^ 2 = 1 := by
      simpa [Complex.normSq_eq_norm_sq] using hphaseNormSq
    nlinarith [norm_nonneg phase]
  have hphaseUnit : phase * star phase = 1 := by
    simpa [Complex.mul_conj] using hphaseNormSq
  refine ⟨phase, hphaseNorm, ?_⟩
  funext j
  have hcross := congrFun (congrFun hchoi j) i
  have hphase_i : w i = phase * v i := by
    dsimp only [phase]
    exact (div_mul_cancel₀ _ hi).symm
  have hconj_i : star (w i) = star phase * star (v i) := by
    rw [hphase_i, star_mul]
    ring
  have hcancel : v j = w j * star phase := by
    apply mul_right_cancel₀ (star_ne_zero.mpr hi)
    calc
      v j * star (v i) = w j * star (w i) := by
        simpa [Matrix.vecMulVec_apply] using hcross
      _ = (w j * star phase) * star (v i) := by
        rw [hconj_i]
        ring
  change w j = phase * v j
  calc
    w j = (phase * star phase) * w j := by rw [hphaseUnit, one_mul]
    _ = phase * (w j * star phase) := by ring
    _ = phase * v j := by rw [← hcancel]

/-- Changing a Kraus representative by a unit complex phase leaves its
rank-one Choi matrix unchanged.  Hence all statements expressed through that
Choi matrix, including its support and Gram data, are phase independent. -/
theorem unitPhase_preserves_rankOneChoi
    {n : Type*} [Fintype n]
    (phase : ℂ) (v : n → ℂ) (hphase : ‖phase‖ = 1) :
    Matrix.vecMulVec (phase • v) (star (phase • v)) =
      Matrix.vecMulVec v (star v) := by
  have hphaseNormSq : Complex.normSq phase = 1 := by
    rw [Complex.normSq_eq_norm_sq, hphase]
    norm_num
  have hphaseUnit : phase * star phase = 1 := by
    simpa [Complex.mul_conj] using hphaseNormSq
  ext i j
  simp only [Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul,
    Pi.star_apply]
  rw [star_mul]
  calc
    phase * v i * (star (v j) * star phase) =
        (phase * star phase) * (v i * star (v j)) := by ring
    _ = v i * star (v j) := by rw [hphaseUnit, one_mul]

/-- Squared Hilbert--Schmidt norm of a finite complex matrix. -/
def hilbertSchmidtSq {h e : Type*} [Fintype h] [Fintype e]
    (M : Matrix h e ℂ) : ℝ :=
  (Matrix.trace (Mᴴ * M)).re

/-- Canonical positive-modulus endpoint export. -/
def occurrenceEndpointSource {h : ℕ}
    (Tchr : Matrix (Fin h) (Fin 3) ℂ) (alpha mass : ℝ) :
    Matrix (Fin h) (Fin 3) ℂ :=
  ((Real.sqrt (mass / alpha) : ℝ) : ℂ) • Tchr

theorem occurrenceEndpointSource_exact
    {h : ℕ} (Tchr : Matrix (Fin h) (Fin 3) ℂ)
    (alpha mass : ℝ) (halpha : 0 < alpha) (hmass : 0 < mass)
    (hgram : Tchrᴴ * Tchr = (4 * alpha : ℂ) • 1) :
    let Tocc := occurrenceEndpointSource Tchr alpha mass
    Toccᴴ * Tocc = (4 * mass : ℂ) • 1 ∧
    Tchrᴴ * Tocc = (4 * Real.sqrt (alpha * mass) : ℂ) • 1 ∧
    sourceSchurResidual Tchr Tocc = 0 ∧
    (Tocc = Tchr ↔ mass = alpha) ∧
    hilbertSchmidtSq (Tocc - Tchr) =
      12 * (Real.sqrt mass - Real.sqrt alpha) ^ 2 := by
  let c : ℝ := Real.sqrt (mass / alpha)
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have hquot0 : 0 ≤ mass / alpha := div_nonneg hmass.le halpha.le
  have hc2 : c * c = mass / alpha := by
    dsimp only [c]
    nlinarith [Real.sq_sqrt hquot0]
  have hc2alpha : c * c * alpha = mass := by
    rw [hc2]
    field_simp [halpha.ne']
  have hsalpha : 0 < Real.sqrt alpha := Real.sqrt_pos.2 halpha
  have hsmass : 0 < Real.sqrt mass := Real.sqrt_pos.2 hmass
  have hc :
      c = Real.sqrt mass / Real.sqrt alpha := by
    dsimp only [c]
    rw [Real.sqrt_div hmass.le]
  have hscale :
      c * alpha = Real.sqrt (alpha * mass) := by
    rw [hc, Real.sqrt_mul halpha.le]
    field_simp [ne_of_gt hsalpha]
    nlinarith [Real.sq_sqrt halpha.le]
  have hdistance :
      alpha * (c - 1) ^ 2 =
        (Real.sqrt mass - Real.sqrt alpha) ^ 2 := by
    have hcminus :
        c - 1 = (Real.sqrt mass - Real.sqrt alpha) / Real.sqrt alpha := by
      rw [hc]
      field_simp [ne_of_gt hsalpha]
    rw [hcminus, div_pow]
    field_simp [ne_of_gt hsalpha]
    nlinarith [Real.sq_sqrt halpha.le]
  let Tocc := occurrenceEndpointSource Tchr alpha mass
  have hTocc : Tocc = (c : ℂ) • Tchr := rfl
  have hoccGram : Toccᴴ * Tocc = (4 * mass : ℂ) • 1 := by
    rw [hTocc, Matrix.conjTranspose_smul, Matrix.smul_mul,
      Matrix.mul_smul, hgram]
    ext i j
    simp only [Matrix.smul_apply, Matrix.one_apply]
    by_cases hij : i = j
    · subst j
      simp
      norm_cast
      nlinarith [hc2alpha]
    · simp [hij]
  have hcrossGram :
      Tchrᴴ * Tocc = (4 * Real.sqrt (alpha * mass) : ℂ) • 1 := by
    rw [hTocc, Matrix.mul_smul, hgram]
    ext i j
    simp only [Matrix.smul_apply, Matrix.one_apply]
    by_cases hij : i = j
    · subst j
      simp
      norm_cast
      nlinarith [hscale]
    · simp [hij]
  have hresidual : sourceSchurResidual Tchr Tocc = 0 := by
    apply (sourceSchurResidual_eq_zero_iff_rangeIncluded Tchr Tocc).2
    refine ⟨(c : ℂ) • (1 : Matrix (Fin 3) (Fin 3) ℂ), ?_⟩
    rw [hTocc, Matrix.mul_smul, Matrix.mul_one]
  have hequality : Tocc = Tchr ↔ mass = alpha := by
    constructor
    · intro hEq
      have hg := hoccGram
      rw [hEq, hgram] at hg
      have h00 := congrFun (congrFun hg (0 : Fin 3)) (0 : Fin 3)
      symm
      simpa using h00
    · intro hEq
      have hratio : mass / alpha = 1 := by
        rw [hEq, div_self halpha.ne']
      simp [Tocc, occurrenceEndpointSource, hratio]
  have hdistanceMatrix :
      (Tocc - Tchr)ᴴ * (Tocc - Tchr) =
        ((4 * alpha * (c - 1) ^ 2 : ℝ) : ℂ) •
          (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
    have hdiff : Tocc - Tchr = ((c - 1 : ℝ) : ℂ) • Tchr := by
      rw [hTocc]
      module
    rw [hdiff, Matrix.conjTranspose_smul, Matrix.smul_mul,
      Matrix.mul_smul, hgram]
    ext i j
    simp only [Matrix.smul_apply, Matrix.one_apply]
    by_cases hij : i = j
    · subst j
      simp
      ring
    · simp [hij]
  have hdistanceTrace :
      hilbertSchmidtSq (Tocc - Tchr) =
        12 * alpha * (c - 1) ^ 2 := by
    rw [hilbertSchmidtSq, hdistanceMatrix]
    rw [Matrix.trace]
    simp only [Matrix.diag_apply, Matrix.smul_apply,
      Matrix.one_apply, if_pos, smul_eq_mul, mul_one]
    let r : ℝ := 4 * alpha * (c - 1) ^ 2
    change (∑ _i : Fin 3, (r : ℂ)).re =
      12 * alpha * (c - 1) ^ 2
    have hsum : (∑ _i : Fin 3, (r : ℂ)) = ((3 * r : ℝ) : ℂ) := by
      simp
    rw [hsum]
    change 3 * r = 12 * alpha * (c - 1) ^ 2
    dsimp only [r]
    ring
  refine ⟨hoccGram, hcrossGram, hresidual, hequality, ?_⟩
  rw [hdistanceTrace]
  calc
    12 * alpha * (c - 1) ^ 2 =
        12 * (alpha * (c - 1) ^ 2) := by ring
    _ = 12 * (Real.sqrt mass - Real.sqrt alpha) ^ 2 := by rw [hdistance]

end
end EdgeResolvedOccurrenceEndpointClosure
end NCG
