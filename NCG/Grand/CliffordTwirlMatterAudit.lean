/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CliffordMarginalMatterNoGo
import NCG.Grand.GrandWedderburn
import NCG.Grand.NormalBranchPurityMargin

/-!
# One-scalar Clifford-twirl matter audit

Exact finite-dimensional trace identities for a protected Hermitian grading
and four Hermitian Clifford involutions, followed by the concrete
`M₄(ℂ) ⊗ I` commutant and intrinsic-chirality branches.
-/

open Matrix Kronecker
open scoped ComplexOrder

namespace NCG
namespace CliffordTwirlMatterAudit

open CommonOrigin

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

abbrev Block (n : Type*) := Matrix n n ℂ

def positiveProjection (J : Block n) : Block n := (2⁻¹ : ℂ) • (1 + J)
def negativeProjection (J : Block n) : Block n := (2⁻¹ : ℂ) • (1 - J)

def axisCrossBlock (J σ : Block n) : Block n :=
  negativeProjection J * σ * positiveProjection J

def axisOccurrence (J σ : Block n) : ℂ :=
  ((axisCrossBlock J σ)ᴴ * axisCrossBlock J σ).trace

def axisCorrelation (J σ : Block n) : ℂ :=
  (Fintype.card n : ℂ)⁻¹ * (J * σ * J * σ).trace

def axisProbability (J σ : Block n) : ℂ :=
  2 * (Fintype.card n : ℂ)⁻¹ * axisOccurrence J σ

def cliffordProbability (J : Block n) (σ : Fin 4 → Block n) : ℂ :=
  (4⁻¹ : ℂ) * ∑ μ, axisProbability J (σ μ)

def cliffordOccurrence (J : Block n) (σ : Fin 4 → Block n) : ℂ :=
  ∑ μ, axisOccurrence J (σ μ)

def cliffordTwirl (σ : Fin 4 → Block n) (X : Block n) : Block n :=
  (4⁻¹ : ℂ) • ∑ μ, σ μ * X * σ μ

def trivialResidual (J : Block n) (σ : Fin 4 → Block n) : ℂ :=
  ∑ μ, (((J * σ μ * J - σ μ)ᴴ) * (J * σ μ * J - σ μ)).trace

def chiralityResidual (J : Block n) (σ : Fin 4 → Block n) : ℂ :=
  ∑ μ, (((J * σ μ * J + σ μ)ᴴ) * (J * σ μ * J + σ μ)).trace

/-- Hilbert--Schmidt pairing, with the manuscript's convention. -/
def hilbertSchmidtPair (X Y : Block n) : ℂ := (Xᴴ * Y).trace

theorem signProjection_properties (J : Block n)
    (hJH : Jᴴ = J) (hJ2 : J * J = 1) :
    (positiveProjection J)ᴴ = positiveProjection J ∧
    (negativeProjection J)ᴴ = negativeProjection J ∧
    positiveProjection J * positiveProjection J = positiveProjection J ∧
    negativeProjection J * negativeProjection J = negativeProjection J := by
  constructor
  · simp [positiveProjection, Matrix.conjTranspose_add, hJH]
  constructor
  · simp [negativeProjection, Matrix.conjTranspose_sub, hJH]
  constructor
  · unfold positiveProjection
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_add,
      Matrix.mul_one, hJ2]
    module
  · unfold negativeProjection
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub,
      Matrix.mul_one, hJ2]
    module

/-- One-axis off-diagonal occurrence identity. -/
theorem axisOccurrence_eq_correlation
    (J σ : Block n) (hJH : Jᴴ = J) (hJ2 : J * J = 1)
    (hσH : σᴴ = σ) (hσ2 : σ * σ = 1) :
    axisOccurrence J σ =
      (4⁻¹ : ℂ) * ((Fintype.card n : ℂ) - (J * σ * J * σ).trace) := by
  obtain ⟨hPH, hMH, hP2, hM2⟩ := signProjection_properties J hJH hJ2
  let P := positiveProjection J
  let M := negativeProjection J
  have hcross : (axisCrossBlock J σ)ᴴ * axisCrossBlock J σ =
      P * σ * M * σ * P := by
    calc
      (axisCrossBlock J σ)ᴴ * axisCrossBlock J σ =
          (P * σ * M) * (M * σ * P) := by
        unfold axisCrossBlock
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
          hPH, hMH, hσH]
        change P * (σ * M) * (M * σ * P) = (P * σ * M) * (M * σ * P)
        simp only [Matrix.mul_assoc]
      _ = P * σ * (M * M) * σ * P := by
        simp only [Matrix.mul_assoc]
      _ = P * σ * M * σ * P := by rw [hM2]
  rw [axisOccurrence, hcross]
  have hcycle : (P * σ * M * σ * P).trace =
      (P * σ * M * σ).trace := by
    calc
      (P * σ * M * σ * P).trace =
          (P * (P * σ * M * σ)).trace := by
        rw [Matrix.trace_mul_cycle]
        simp only [Matrix.mul_assoc]
      _ = (P * σ * M * σ).trace := by
        rw [show P * (P * σ * M * σ) = (P * P) * σ * M * σ by
          simp only [Matrix.mul_assoc], hP2]
  rw [hcycle]
  unfold P M positiveProjection negativeProjection
  simp only [Matrix.smul_mul, Matrix.mul_smul,
    Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_add,
    Matrix.mul_sub, Matrix.mul_one]
  simp only [Matrix.trace_smul, Matrix.trace_add, Matrix.trace_sub]
  have htrσσ : (σ * σ).trace = Fintype.card n := by
    rw [hσ2, Matrix.trace_one]
  have htrσJσ : (σ * J * σ).trace = J.trace := by
    calc
      (σ * J * σ).trace = (σ * (σ * J)).trace := by
        rw [Matrix.trace_mul_cycle]
        simp only [Matrix.mul_assoc]
      _ = ((σ * σ) * J).trace :=
        congrArg Matrix.trace (Matrix.mul_assoc σ σ J).symm
      _ = J.trace := by rw [hσ2, Matrix.one_mul]
  have htrJσσ : (J * σ * σ).trace = J.trace := by
    rw [Matrix.mul_assoc, hσ2, Matrix.mul_one]
  rw [htrσσ, htrσJσ, htrJσσ]
  ring

theorem axisOccurrence_probability_formulas
    (J σ : Block n) (hJH : Jᴴ = J) (hJ2 : J * J = 1)
    (hσH : σᴴ = σ) (hσ2 : σ * σ = 1) :
    axisOccurrence J σ = (Fintype.card n : ℂ) / 4 *
        (1 - axisCorrelation J σ) ∧
      axisProbability J σ = (2⁻¹ : ℂ) * (1 - axisCorrelation J σ) := by
  have hcard : (Fintype.card n : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  constructor
  · rw [axisOccurrence_eq_correlation J σ hJH hJ2 hσH hσ2]
    unfold axisCorrelation
    field_simp
  · unfold axisProbability axisCorrelation
    rw [axisOccurrence_eq_correlation J σ hJH hJ2 hσH hσ2]
    field_simp
    ring

open scoped ComplexOrder in
theorem axisOccurrence_nonnegative (J σ : Block n) :
    (0 : ℂ) ≤ axisOccurrence J σ :=
  (Matrix.posSemidef_conjTranspose_mul_self (axisCrossBlock J σ)).trace_nonneg

open scoped ComplexOrder in
theorem axisOccurrence_eq_zero_iff (J σ : Block n) :
    axisOccurrence J σ = 0 ↔ axisCrossBlock J σ = 0 :=
  Matrix.trace_conjTranspose_mul_self_eq_zero_iff

/-- For Hermitian involutions, a Clifford axis has no grading-changing corner
exactly when it commutes with the grading. -/
theorem axisCrossBlock_eq_zero_iff_commute
    (J σ : Block n) (hJH : Jᴴ = J) (hJ2 : J * J = 1)
    (hσH : σᴴ = σ) :
    axisCrossBlock J σ = 0 ↔ J * σ = σ * J := by
  obtain ⟨hPH, hMH, -, -⟩ := signProjection_properties J hJH hJ2
  constructor
  · intro hMP
    have hPM : positiveProjection J * σ * negativeProjection J = 0 := by
      have h := congrArg Matrix.conjTranspose hMP
      simp only [axisCrossBlock, Matrix.conjTranspose_mul,
        hPH, hMH, hσH, Matrix.conjTranspose_zero] at h
      simpa only [Matrix.mul_assoc] using h
    have hid : J * σ - σ * J =
        2 • (positiveProjection J * σ * negativeProjection J -
          negativeProjection J * σ * positiveProjection J) := by
      unfold positiveProjection negativeProjection
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul,
        Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one]
      module
    have hMP' : negativeProjection J * σ * positiveProjection J = 0 := hMP
    rw [hPM, hMP', sub_zero, smul_zero] at hid
    exact sub_eq_zero.mp hid
  · intro hcomm
    have hcore : (1 - J) * σ * (1 + J) = 0 := by
      simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_add,
        Matrix.mul_one]
      rw [hcomm, Matrix.mul_assoc, hJ2, Matrix.mul_one]
      abel
    unfold axisCrossBlock positiveProjection negativeProjection
    simp only [Matrix.smul_mul, Matrix.mul_smul]
    rw [hcore, smul_zero]
    simp

theorem axisOccurrence_eq_zero_iff_commute
    (J σ : Block n) (hJH : Jᴴ = J) (hJ2 : J * J = 1)
    (hσH : σᴴ = σ) :
    axisOccurrence J σ = 0 ↔ J * σ = σ * J := by
  rw [axisOccurrence_eq_zero_iff,
    axisCrossBlock_eq_zero_iff_commute J σ hJH hJ2 hσH]

/-- Summing the four one-axis identities gives both manuscript formulas for
the complete occurrence mass. -/
theorem cliffordOccurrence_formulas
    (J : Block n) (σ : Fin 4 → Block n)
    (hJH : Jᴴ = J) (hJ2 : J * J = 1)
    (hσH : ∀ μ, (σ μ)ᴴ = σ μ) (hσ2 : ∀ μ, σ μ * σ μ = 1) :
    cliffordOccurrence J σ =
        (Fintype.card n : ℂ) - hilbertSchmidtPair J (cliffordTwirl σ J) ∧
      cliffordOccurrence J σ =
        2 * (Fintype.card n : ℂ) * cliffordProbability J σ := by
  have hcard : (Fintype.card n : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  constructor
  · simp only [cliffordOccurrence, Fin.sum_univ_four]
    rw [axisOccurrence_eq_correlation J (σ 0) hJH hJ2 (hσH 0) (hσ2 0),
      axisOccurrence_eq_correlation J (σ 1) hJH hJ2 (hσH 1) (hσ2 1),
      axisOccurrence_eq_correlation J (σ 2) hJH hJ2 (hσH 2) (hσ2 2),
      axisOccurrence_eq_correlation J (σ 3) hJH hJ2 (hσH 3) (hσ2 3)]
    unfold hilbertSchmidtPair cliffordTwirl
    rw [hJH]
    simp only [Matrix.mul_smul, Matrix.mul_add, Matrix.trace_smul,
      Matrix.trace_add, Fin.sum_univ_four, Matrix.mul_assoc]
    ring
  · unfold cliffordOccurrence cliffordProbability axisProbability
    simp only [Fin.sum_univ_four]
    field_simp [hcard]
    ring

/-- One-axis grading-automorphism residuals are respectively eight times the
off-diagonal occurrence and its complementary mass. -/
theorem axisResidual_formulas
    (J σ : Block n) (hJH : Jᴴ = J) (hJ2 : J * J = 1)
    (hσH : σᴴ = σ) (hσ2 : σ * σ = 1) :
    (((J * σ * J - σ)ᴴ) * (J * σ * J - σ)).trace =
        8 * axisOccurrence J σ ∧
      (((J * σ * J + σ)ᴴ) * (J * σ * J + σ)).trace =
        4 * (Fintype.card n : ℂ) - 8 * axisOccurrence J σ := by
  have hselfMinus : (J * σ * J - σ)ᴴ = J * σ * J - σ := by
    simp [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hJH, hσH]
    simp only [Matrix.mul_assoc]
  have hselfPlus : (J * σ * J + σ)ᴴ = J * σ * J + σ := by
    simp [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, hJH, hσH]
    simp only [Matrix.mul_assoc]
  have hcycle : (σ * (J * σ * J)).trace = (J * σ * J * σ).trace := by
    calc
      (σ * (J * σ * J)).trace = ((J * σ * J) * σ).trace :=
        Matrix.trace_mul_comm σ (J * σ * J)
      _ = (J * σ * J * σ).trace := rfl
  have hminus : ((J * σ * J - σ) * (J * σ * J - σ)).trace =
      2 * (Fintype.card n : ℂ) - 2 * (J * σ * J * σ).trace := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub,
      Matrix.trace_add]
    have hJJ : J * σ * J * (J * σ * J) = 1 := by
      calc
        J * σ * J * (J * σ * J) = J * σ * (J * J) * σ * J := by
          simp only [Matrix.mul_assoc]
        _ = J * σ * σ * J := by rw [hJ2]; simp
        _ = J * (σ * σ) * J := by simp only [Matrix.mul_assoc]
        _ = J * J := by rw [hσ2]; simp
        _ = 1 := hJ2
    rw [hJJ, hσ2, Matrix.trace_one, hcycle]
    ring
  have hplus : ((J * σ * J + σ) * (J * σ * J + σ)).trace =
      2 * (Fintype.card n : ℂ) + 2 * (J * σ * J * σ).trace := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.trace_add]
    have hJJ : J * σ * J * (J * σ * J) = 1 := by
      calc
        J * σ * J * (J * σ * J) = J * σ * (J * J) * σ * J := by
          simp only [Matrix.mul_assoc]
        _ = J * σ * σ * J := by rw [hJ2]; simp
        _ = J * (σ * σ) * J := by simp only [Matrix.mul_assoc]
        _ = J * J := by rw [hσ2]; simp
        _ = 1 := hJ2
    rw [hJJ, hσ2, Matrix.trace_one, hcycle]
    ring
  rw [hselfMinus, hselfPlus, hminus, hplus,
    axisOccurrence_eq_correlation J σ hJH hJ2 hσH hσ2]
  constructor <;> ring

/-- The two four-axis residual identities and their constant-sum law. -/
theorem cliffordResidual_formulas
    (J : Block n) (σ : Fin 4 → Block n)
    (hJH : Jᴴ = J) (hJ2 : J * J = 1)
    (hσH : ∀ μ, (σ μ)ᴴ = σ μ) (hσ2 : ∀ μ, σ μ * σ μ = 1) :
    trivialResidual J σ = 16 * (Fintype.card n : ℂ) * cliffordProbability J σ ∧
      chiralityResidual J σ =
        16 * (Fintype.card n : ℂ) * (1 - cliffordProbability J σ) ∧
      trivialResidual J σ + chiralityResidual J σ =
        16 * (Fintype.card n : ℂ) := by
  have h0 := axisResidual_formulas J (σ 0) hJH hJ2 (hσH 0) (hσ2 0)
  have h1 := axisResidual_formulas J (σ 1) hJH hJ2 (hσH 1) (hσ2 1)
  have h2 := axisResidual_formulas J (σ 2) hJH hJ2 (hσH 2) (hσ2 2)
  have h3 := axisResidual_formulas J (σ 3) hJH hJ2 (hσH 3) (hσ2 3)
  have hocc := (cliffordOccurrence_formulas J σ hJH hJ2 hσH hσ2).2
  have htriv : trivialResidual J σ = 8 * cliffordOccurrence J σ := by
    unfold trivialResidual cliffordOccurrence
    simp only [Fin.sum_univ_four]
    rw [h0.1, h1.1, h2.1, h3.1]
    ring
  have hchir : chiralityResidual J σ =
      16 * (Fintype.card n : ℂ) - 8 * cliffordOccurrence J σ := by
    unfold chiralityResidual cliffordOccurrence
    simp only [Fin.sum_univ_four]
    rw [h0.2, h1.2, h2.2, h3.2]
    ring
  constructor
  · rw [htriv, hocc]
    ring
  constructor
  · rw [hchir, hocc]
    ring
  · rw [htriv, hchir]
    ring

section ConcreteCarrier

variable {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]

abbrev CliffordCarrier (m : Type*) := SMST4 × m

/-- The canonical faithful Clifford packet on `ℂ⁴ ⊗ M`. -/
def representedAxis (μ : Fin 4) : Block (CliffordCarrier m) :=
  gamma μ ⊗ₖ (1 : Block m)

/-- Intrinsic chirality on the same multiplicity carrier. -/
def representedChirality : Block (CliffordCarrier m) :=
  smstChirality ⊗ₖ (1 : Block m)

theorem representedAxis_sq (μ : Fin 4) :
    representedAxis (m := m) μ * representedAxis μ = 1 := by
  rw [representedAxis, ← Matrix.mul_kronecker_mul, gamma_sq,
    Matrix.one_mul, Matrix.one_kronecker_one]

theorem representedAxis_hermitian (μ : Fin 4) :
    (representedAxis (m := m) μ)ᴴ = representedAxis μ := by
  simp [representedAxis, Matrix.conjTranspose_kronecker, gamma_herm]

theorem representedChirality_sq :
    representedChirality (m := m) * representedChirality = 1 := by
  rw [representedChirality, ← Matrix.mul_kronecker_mul,
    smstChirality_sq, Matrix.one_mul, Matrix.one_kronecker_one]

theorem representedChirality_hermitian :
    (representedChirality (m := m))ᴴ = representedChirality := by
  rw [representedChirality, Matrix.conjTranspose_kronecker]
  have hC : smstChiralityᴴ = smstChirality := by
    rw [smstChirality_eq]
    simp [Matrix.conjTranspose_kronecker, pauli3_herm]
  rw [hC, Matrix.conjTranspose_one]

theorem representedChirality_anticomm (μ : Fin 4) :
    representedChirality (m := m) * representedAxis μ =
      -(representedAxis μ * representedChirality) := by
  rw [representedChirality, representedAxis,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, smstChirality_anticomm]
  ext ⟨i, k⟩ ⟨j, l⟩
  simp [Matrix.kroneckerMap_apply]

/-- Direct slice proof of `N' = I₄ ⊗ B(M)` on an arbitrary finite
multiplicity carrier. -/
theorem representedAxis_commutant
    (X : Block (CliffordCarrier m))
    (hX : ∀ μ, X * representedAxis μ = representedAxis μ * X) :
    ∃ B : Block m, X = (1 : Block SMST4) ⊗ₖ B := by
  classical
  let slice (k l : m) : Block SMST4 :=
    Matrix.of fun i j => X (i, k) (j, l)
  have hslice : ∀ k l μ, slice k l * gamma μ = gamma μ * slice k l := by
    intro k l μ
    ext i j
    have h := congrFun (congrFun (hX μ) (i, k)) (j, l)
    simp only [representedAxis, Matrix.mul_apply,
      Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
      Matrix.one_apply, mul_ite, ite_mul, mul_one, mul_zero,
      zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, slice, Matrix.of_apply] at h ⊢
    exact h
  have hscalar (k l : m) : ∃ c : ℂ, slice k l = c • 1 :=
    gamma_commutant (slice k l) (hslice k l)
  let coefficient (k l : m) : ℂ := Classical.choose (hscalar k l)
  let B : Block m := Matrix.of fun k l => coefficient k l
  refine ⟨B, ?_⟩
  ext ⟨i, k⟩ ⟨j, l⟩
  have hs := congrFun (congrFun (Classical.choose_spec (hscalar k l)) i) j
  simp only [slice, Matrix.of_apply, Matrix.smul_apply, Matrix.one_apply] at hs
  simp only [Matrix.kroneckerMap_apply, B, Matrix.of_apply, coefficient]
  simpa [Matrix.one_apply, mul_comm] using hs

theorem multiplicityFactor_commutes (B : Block m) (μ : Fin 4) :
    ((1 : Block SMST4) ⊗ₖ B) * representedAxis μ =
      representedAxis μ * ((1 : Block SMST4) ⊗ₖ B) := by
  rw [representedAxis, ← Matrix.mul_kronecker_mul,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]
  simp

theorem representedAxis_commutant_iff (X : Block (CliffordCarrier m)) :
    (∀ μ, X * representedAxis μ = representedAxis μ * X) ↔
      ∃ B : Block m, X = (1 : Block SMST4) ⊗ₖ B := by
  constructor
  · exact representedAxis_commutant X
  · rintro ⟨B, rfl⟩ μ
    exact multiplicityFactor_commutes B μ

open scoped ComplexOrder in
theorem cliffordProbability_eq_zero_iff_commutes
    (J : Block (CliffordCarrier m))
    (hJH : Jᴴ = J) (hJ2 : J * J = 1) :
    cliffordProbability J representedAxis = 0 ↔
      ∀ μ, J * representedAxis μ = representedAxis μ * J := by
  have hmass := (cliffordOccurrence_formulas J representedAxis hJH hJ2
    representedAxis_hermitian representedAxis_sq).2
  have hnonneg : ∀ μ ∈ Finset.univ,
      (0 : ℂ) ≤ axisOccurrence J (representedAxis μ) :=
    fun μ _ => axisOccurrence_nonnegative J (representedAxis μ)
  constructor
  · intro hp
    have hsum : cliffordOccurrence J representedAxis = 0 := by
      rw [hmass, hp]
      ring
    unfold cliffordOccurrence at hsum
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum
    intro μ
    exact (axisOccurrence_eq_zero_iff_commute J (representedAxis μ)
      hJH hJ2 (representedAxis_hermitian μ)).mp
        (hz μ (Finset.mem_univ μ))
  · intro hcomm
    have hz : cliffordOccurrence J representedAxis = 0 := by
      unfold cliffordOccurrence
      apply Finset.sum_eq_zero
      intro μ _
      exact (axisOccurrence_eq_zero_iff_commute J (representedAxis μ)
        hJH hJ2 (representedAxis_hermitian μ)).mpr (hcomm μ)
    rw [hz] at hmass
    have hfactor : (2 * (Fintype.card (CliffordCarrier m) : ℂ)) ≠ 0 := by
      positivity
    exact (mul_eq_zero.mp hmass.symm).resolve_left hfactor

/-- A grading carried by the multiplicity factor induces a Hermitian
involution on that factor. -/
theorem multiplicityFactor_inherits_grading
    (J : Block (CliffordCarrier m)) (B : Block m)
    (hfactor : J = (1 : Block SMST4) ⊗ₖ B)
    (hJH : Jᴴ = J) (hJ2 : J * J = 1) :
    Bᴴ = B ∧ B * B = 1 := by
  subst J
  constructor
  · ext k l
    have h := congrFun (congrFun hJH ((0, 0), k)) ((0, 0), l)
    simpa [Matrix.conjTranspose_kronecker, Matrix.kroneckerMap_apply,
      Matrix.one_apply] using h
  · have hkron : (1 : Block SMST4) ⊗ₖ (B * B) =
        (1 : Block SMST4) ⊗ₖ (1 : Block m) := by
      calc
        (1 : Block SMST4) ⊗ₖ (B * B) =
            ((1 : Block SMST4) ⊗ₖ B) * ((1 : Block SMST4) ⊗ₖ B) := by
              rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]
        _ = 1 := hJ2
        _ = (1 : Block SMST4) ⊗ₖ (1 : Block m) :=
          Matrix.one_kronecker_one.symm
    ext k l
    have h := congrFun (congrFun hkron ((0, 0), k)) ((0, 0), l)
    simpa [Matrix.kroneckerMap_apply, Matrix.one_apply] using h

/-- Exact no-matter branch on the faithful carrier. -/
theorem noMatter_branch
    (J : Block (CliffordCarrier m))
    (hJH : Jᴴ = J) (hJ2 : J * J = 1) :
    cliffordProbability J representedAxis = 0 ↔
      ∃ B : Block m, J = (1 : Block SMST4) ⊗ₖ B ∧ Bᴴ = B ∧ B * B = 1 := by
  rw [cliffordProbability_eq_zero_iff_commutes J hJH hJ2,
    representedAxis_commutant_iff]
  constructor
  · rintro ⟨B, hB⟩
    exact ⟨B, hB, (multiplicityFactor_inherits_grading J B hB hJH hJ2).1,
      (multiplicityFactor_inherits_grading J B hB hJH hJ2).2⟩
  · rintro ⟨B, hB, -, -⟩
    exact ⟨B, hB⟩

open scoped ComplexOrder in
theorem cliffordProbability_eq_one_iff_anticommutes
    (J : Block (CliffordCarrier m))
    (hJH : Jᴴ = J) (hJ2 : J * J = 1) :
    cliffordProbability J representedAxis = 1 ↔
      ∀ μ, J * representedAxis μ = -(representedAxis μ * J) := by
  have hres := cliffordResidual_formulas J representedAxis hJH hJ2
    representedAxis_hermitian representedAxis_sq
  constructor
  · intro hp
    have hzero : chiralityResidual J representedAxis = 0 := by
      rw [hres.2.1, hp]
      ring
    unfold chiralityResidual at hzero
    have hnonneg : ∀ μ ∈ Finset.univ, (0 : ℂ) ≤
        (((J * representedAxis μ * J + representedAxis μ)ᴴ) *
          (J * representedAxis μ * J + representedAxis μ)).trace :=
      fun μ _ =>
        (Matrix.posSemidef_conjTranspose_mul_self
          (J * representedAxis μ * J + representedAxis μ)).trace_nonneg
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hzero
    intro μ
    have hmat := Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp
      (hz μ (Finset.mem_univ μ))
    have htransform : J * representedAxis μ * J = -representedAxis μ :=
      eq_neg_of_add_eq_zero_left hmat
    calc
      J * representedAxis μ = (J * representedAxis μ * J) * J := by
        rw [Matrix.mul_assoc, hJ2, Matrix.mul_one]
      _ = (-representedAxis μ) * J := by rw [htransform]
      _ = -(representedAxis μ * J) := by simp
  · intro hanti
    have hzero : chiralityResidual J representedAxis = 0 := by
      unfold chiralityResidual
      apply Finset.sum_eq_zero
      intro μ _
      have htransform : J * representedAxis μ * J = -representedAxis μ := by
        calc
          J * representedAxis μ * J = (-(representedAxis μ * J)) * J := by
            rw [hanti μ]
          _ = -representedAxis μ := by
            simp only [neg_mul, Matrix.mul_assoc, hJ2, Matrix.mul_one]
      rw [htransform]
      simp
    have heq : 16 * (Fintype.card (CliffordCarrier m) : ℂ) *
        (1 - cliffordProbability J representedAxis) = 0 := by
      rw [← hres.2.1, hzero]
    have hfactor : (16 * (Fintype.card (CliffordCarrier m) : ℂ)) ≠ 0 := by
      positivity
    have : 1 - cliffordProbability J representedAxis = 0 :=
      (mul_eq_zero.mp heq).resolve_left hfactor
    have hone : (1 : ℂ) = cliffordProbability J representedAxis :=
      sub_eq_zero.mp this
    exact hone.symm

/-- Two operators which both anticommute with every axis have a commuting
product. -/
theorem chiralityTimesAnticommutant_commutes
    (J : Block (CliffordCarrier m))
    (hanti : ∀ μ, J * representedAxis μ = -(representedAxis μ * J)) :
    ∀ μ, (representedChirality * J) * representedAxis μ =
      representedAxis μ * (representedChirality * J) := by
  intro μ
  calc
    (representedChirality * J) * representedAxis μ =
        representedChirality * (J * representedAxis μ) := by
          simp only [Matrix.mul_assoc]
    _ = representedChirality * (-(representedAxis μ * J)) := by rw [hanti μ]
    _ = -(representedChirality * representedAxis μ) * J := by
      simp only [Matrix.mul_neg, neg_mul, Matrix.mul_assoc]
    _ = -(-(representedAxis μ * representedChirality)) * J := by
      rw [representedChirality_anticomm μ]
    _ = representedAxis μ * (representedChirality * J) := by
      simp only [neg_neg, Matrix.mul_assoc]

theorem representedAxis_anticommutant
    (J : Block (CliffordCarrier m))
    (hanti : ∀ μ, J * representedAxis μ = -(representedAxis μ * J)) :
    ∃ B : Block m, J = smstChirality ⊗ₖ B := by
  obtain ⟨B, hB⟩ := representedAxis_commutant
    (representedChirality * J) (chiralityTimesAnticommutant_commutes J hanti)
  refine ⟨B, ?_⟩
  calc
    J = representedChirality * (representedChirality * J) := by
      rw [← Matrix.mul_assoc, representedChirality_sq, Matrix.one_mul]
    _ = representedChirality * ((1 : Block SMST4) ⊗ₖ B) := by rw [hB]
    _ = smstChirality ⊗ₖ B := by
      rw [representedChirality, ← Matrix.mul_kronecker_mul,
        Matrix.mul_one, Matrix.one_mul]

theorem chiralityFactor_inherits_grading
    (J : Block (CliffordCarrier m)) (B : Block m)
    (hfactor : J = smstChirality ⊗ₖ B)
    (hJH : Jᴴ = J) (hJ2 : J * J = 1) :
    Bᴴ = B ∧ B * B = 1 := by
  subst J
  constructor
  · ext k l
    have h := congrFun (congrFun hJH ((0, 0), k)) ((0, 0), l)
    simpa [Matrix.conjTranspose_kronecker, Matrix.kroneckerMap_apply,
      smstChirality_eq, pauli3, Matrix.one_apply] using h
  · have hkron : (1 : Block SMST4) ⊗ₖ (B * B) =
        (1 : Block SMST4) ⊗ₖ (1 : Block m) := by
      calc
        (1 : Block SMST4) ⊗ₖ (B * B) =
            (smstChirality ⊗ₖ B) * (smstChirality ⊗ₖ B) := by
              rw [← Matrix.mul_kronecker_mul, smstChirality_sq]
        _ = 1 := hJ2
        _ = (1 : Block SMST4) ⊗ₖ (1 : Block m) :=
          Matrix.one_kronecker_one.symm
    ext k l
    have h := congrFun (congrFun hkron ((0, 0), k)) ((0, 0), l)
    simpa [Matrix.kroneckerMap_apply, Matrix.one_apply] using h

/-- Exact intrinsic-chirality branch on the faithful carrier. -/
theorem intrinsicChirality_branch
    (J : Block (CliffordCarrier m))
    (hJH : Jᴴ = J) (hJ2 : J * J = 1) :
    cliffordProbability J representedAxis = 1 ↔
      ∃ B : Block m, J = smstChirality ⊗ₖ B ∧ Bᴴ = B ∧ B * B = 1 := by
  rw [cliffordProbability_eq_one_iff_anticommutes J hJH hJ2]
  constructor
  · intro hanti
    obtain ⟨B, hB⟩ := representedAxis_anticommutant J hanti
    exact ⟨B, hB, (chiralityFactor_inherits_grading J B hB hJH hJ2).1,
      (chiralityFactor_inherits_grading J B hB hJH hJ2).2⟩
  · rintro ⟨B, rfl, -, -⟩ μ
    rw [representedAxis, ← Matrix.mul_kronecker_mul,
      ← Matrix.mul_kronecker_mul, Matrix.mul_one,
      smstChirality_anticomm]
    ext ⟨i, k⟩ ⟨j, l⟩
    simp [Matrix.kroneckerMap_apply]

/-- A protected grading-changing matter route is literally a nonzero
off-diagonal Clifford corner on the common carrier. -/
def HasProtectedMatterRoute (J : Block (CliffordCarrier m)) : Prop :=
  ∃ μ, axisCrossBlock J (representedAxis μ) ≠ 0

open scoped ComplexOrder in
/-- The manuscript's five equivalent positive-matter tests.  The last clause
uses the formal route predicate above; the fourth is non-membership in the
explicitly classified commutant. -/
theorem positiveMatter_five_way
    (J : Block (CliffordCarrier m))
    (hJH : Jᴴ = J) (hJ2 : J * J = 1) :
    ((0 : ℂ) < cliffordProbability J representedAxis ↔
        (0 : ℂ) < cliffordOccurrence J representedAxis) ∧
      ((0 : ℂ) < cliffordOccurrence J representedAxis ↔
        ∃ μ, axisCrossBlock J (representedAxis μ) ≠ 0) ∧
      ((∃ μ, axisCrossBlock J (representedAxis μ) ≠ 0) ↔
        ¬ ∃ B : Block m, J = (1 : Block SMST4) ⊗ₖ B) ∧
      ((¬ ∃ B : Block m, J = (1 : Block SMST4) ⊗ₖ B) ↔
        HasProtectedMatterRoute J) := by
  have hmass := (cliffordOccurrence_formulas J representedAxis hJH hJ2
    representedAxis_hermitian representedAxis_sq).2
  have hocc_nonneg : (0 : ℂ) ≤ cliffordOccurrence J representedAxis := by
    unfold cliffordOccurrence
    exact Finset.sum_nonneg fun μ _ =>
      axisOccurrence_nonnegative J (representedAxis μ)
  have hprob_nonneg : (0 : ℂ) ≤ cliffordProbability J representedAxis := by
    unfold cliffordProbability
    apply mul_nonneg
    · norm_num [Complex.nonneg_iff]
    · apply Finset.sum_nonneg
      intro μ _
      unfold axisProbability
      positivity [axisOccurrence_nonnegative J (representedAxis μ)]
  have hfactor : (2 * (Fintype.card (CliffordCarrier m) : ℂ)) ≠ 0 := by
    positivity
  have hzero : cliffordOccurrence J representedAxis = 0 ↔
      cliffordProbability J representedAxis = 0 := by
    constructor
    · intro h
      rw [h] at hmass
      exact (mul_eq_zero.mp hmass.symm).resolve_left hfactor
    · intro h
      rw [h] at hmass
      simpa using hmass
  have hprob_pos : (0 : ℂ) < cliffordProbability J representedAxis ↔
      cliffordProbability J representedAxis ≠ 0 := by
    constructor
    · exact ne_of_gt
    · intro h
      exact lt_of_le_of_ne hprob_nonneg (Ne.symm h)
  have hocc_pos : (0 : ℂ) < cliffordOccurrence J representedAxis ↔
      cliffordOccurrence J representedAxis ≠ 0 := by
    constructor
    · exact ne_of_gt
    · intro h
      exact lt_of_le_of_ne hocc_nonneg (Ne.symm h)
  have hsum_zero : cliffordOccurrence J representedAxis = 0 ↔
      ∀ μ, axisCrossBlock J (representedAxis μ) = 0 := by
    unfold cliffordOccurrence
    rw [Finset.sum_eq_zero_iff_of_nonneg]
    · constructor
      · intro hz μ
        exact (axisOccurrence_eq_zero_iff J (representedAxis μ)).mp
          (hz μ (Finset.mem_univ μ))
      · intro hz μ _
        exact (axisOccurrence_eq_zero_iff J (representedAxis μ)).mpr (hz μ)
    · exact fun μ _ => axisOccurrence_nonnegative J (representedAxis μ)
  have hroute : cliffordOccurrence J representedAxis ≠ 0 ↔
      ∃ μ, axisCrossBlock J (representedAxis μ) ≠ 0 := by
    simpa only [not_forall] using (not_congr hsum_zero)
  have hcomm : (∀ μ, axisCrossBlock J (representedAxis μ) = 0) ↔
      ∃ B : Block m, J = (1 : Block SMST4) ⊗ₖ B := by
    calc
      (∀ μ, axisCrossBlock J (representedAxis μ) = 0) ↔
          ∀ μ, J * representedAxis μ = representedAxis μ * J := by
            constructor <;> intro h μ
            · exact (axisCrossBlock_eq_zero_iff_commute J (representedAxis μ)
                hJH hJ2 (representedAxis_hermitian μ)).mp (h μ)
            · exact (axisCrossBlock_eq_zero_iff_commute J (representedAxis μ)
                hJH hJ2 (representedAxis_hermitian μ)).mpr (h μ)
      _ ↔ ∃ B : Block m, J = (1 : Block SMST4) ⊗ₖ B :=
        representedAxis_commutant_iff J
  have hroute_comm : (∃ μ, axisCrossBlock J (representedAxis μ) ≠ 0) ↔
      ¬ ∃ B : Block m, J = (1 : Block SMST4) ⊗ₖ B := by
    simpa only [not_forall] using (not_congr hcomm)
  constructor
  · rw [hprob_pos, hocc_pos]
    exact not_congr hzero.symm
  constructor
  · exact hocc_pos.trans hroute
  constructor
  · exact hroute_comm
  · simpa [HasProtectedMatterRoute] using hroute_comm.symm

/-- Trace-preserving expectation onto `I₄ ⊗ B(M)`. -/
def commutantExpectation (X : Block (CliffordCarrier m)) :
    Block (CliffordCarrier m) :=
  NormalBranchPurityMargin.normalSeparatedOperator
    (NormalBranchPurityMargin.normalizedNormalPartialTrace X)

/-- Squared Hilbert--Schmidt distance from the multiplicity commutant. -/
def commutantExpectationResidual (X : Block (CliffordCarrier m)) : ℂ :=
  NormalBranchPurityMargin.productHilbertSchmidtInner
    (NormalBranchPurityMargin.normalSeparationResidual X)
    (NormalBranchPurityMargin.normalSeparationResidual X)

/-- Unnormalized multiplicity marginals `ρ± = Tr_{ℂ⁴} P±`. -/
def positiveBranchDensity (J : Block (CliffordCarrier m)) : Block m :=
  (4 : ℂ) • NormalBranchPurityMargin.normalizedNormalPartialTrace
    (positiveProjection J)

def negativeBranchDensity (J : Block (CliffordCarrier m)) : Block m :=
  (4 : ℂ) • NormalBranchPurityMargin.normalizedNormalPartialTrace
    (negativeProjection J)

theorem branchDensity_formulas (J : Block (CliffordCarrier m)) :
    let T := NormalBranchPurityMargin.normalizedNormalPartialTrace J
    positiveBranchDensity J = (2 : ℂ) • (1 + T) ∧
      negativeBranchDensity J = (2 : ℂ) • (1 - T) := by
  dsimp
  have hcenter :=
    NormalBranchPurityMargin.centeredMatterSign_eq_normalizedNormalPartialTrace J
  change (2 : ℂ) • NormalBranchPurityMargin.normalizedNormalPartialTrace
      (NormalBranchPurityMargin.positiveSignProjection J) - 1 =
        NormalBranchPurityMargin.normalizedNormalPartialTrace J at hcenter
  have hposdef : NormalBranchPurityMargin.positiveSignProjection J =
      positiveProjection J := rfl
  rw [hposdef] at hcenter
  have hsum : negativeProjection J = 1 - positiveProjection J := by
    unfold negativeProjection positiveProjection
    module
  have hE : (2 : ℂ) • NormalBranchPurityMargin.normalizedNormalPartialTrace
      (positiveProjection J) =
        1 + NormalBranchPurityMargin.normalizedNormalPartialTrace J := by
    rw [sub_eq_iff_eq_add] at hcenter
    calc
      (2 : ℂ) • NormalBranchPurityMargin.normalizedNormalPartialTrace
          (positiveProjection J) =
          NormalBranchPurityMargin.normalizedNormalPartialTrace J + 1 := hcenter
      _ = 1 + NormalBranchPurityMargin.normalizedNormalPartialTrace J := add_comm _ _
  constructor
  · unfold positiveBranchDensity
    rw [show (4 : ℂ) = 2 * 2 by norm_num, mul_smul, hE]
  · unfold negativeBranchDensity
    rw [hsum, NormalBranchPurityMargin.normalizedNormalPartialTrace_sub,
      NormalBranchPurityMargin.normalizedNormalPartialTrace_one]
    rw [show (4 : ℂ) = 2 * 2 by norm_num, mul_smul,
      smul_sub, hE]
    module

/-- Exact branch-overlap form of the conditional-expectation residual:
`ΩCl = Tr_M(ρ₊ρ₋)`. -/
theorem commutantExpectationResidual_eq_branchOverlap
    (J : Block (CliffordCarrier m))
    (hJH : Jᴴ = J) (hJ2 : J * J = 1) :
    commutantExpectationResidual J =
      (positiveBranchDensity J * negativeBranchDensity J).trace := by
  let T := NormalBranchPurityMargin.normalizedNormalPartialTrace J
  have hmargin :=
    NormalBranchPurityMargin.involution_branchMargin_eq_residual J hJH hJ2
  change NormalBranchPurityMargin.productHilbertSchmidtInner
      (NormalBranchPurityMargin.normalSeparationResidual J)
      (NormalBranchPurityMargin.normalSeparationResidual J) =
        (4 : ℂ) * Matrix.trace (1 - T * T) at hmargin
  have hρ := branchDensity_formulas J
  dsimp only at hρ
  change positiveBranchDensity J = (2 : ℂ) • (1 + T) ∧
    negativeBranchDensity J = (2 : ℂ) • (1 - T) at hρ
  unfold commutantExpectationResidual
  rw [hmargin, hρ.1, hρ.2]
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.add_mul, Matrix.one_mul, Matrix.mul_sub,
    Matrix.mul_one, Matrix.trace_smul]
  have hmat : 1 - T + (T - T * T) = 1 - T * T := by abel
  rw [hmat]
  ring

end ConcreteCarrier

end
end CliffordTwirlMatterAudit
end NCG
