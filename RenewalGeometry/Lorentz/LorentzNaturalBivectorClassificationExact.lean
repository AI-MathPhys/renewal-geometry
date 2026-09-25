/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Lorentz.BivectorRotationCommutantExact
import RenewalGeometry.Gravity.PalatiniInsertion

/-!
# Lorentz-natural classification of the generic gravitational score
  (`thm:main-gravitational-classification`, `eq:main-phv-classification`,
  `eq:main-phv-coefficients`, `eq:supp-lorentz-commutant`;
  emergent-spacetime manuscript)

Finite-dimensional model of the classification.  The coframe bivector and
the curvature both transform in `Λ²ℝ^{1,3}`, represented on the carrier
`BivectorIndex = Fin 2 × Fin 3` (electric/magnetic components) through the
*actual induced action* `inducedBivectorAction Λ` (the matrix of `Λ²Λ` in the
bivector basis, i.e. the `2 × 2` minors of `Λ`) of a `4 × 4` matrix `Λ`.
`IsProperLorentz Λ` is the proper orthochronous Lorentz condition
`Λᵀ η Λ = η`, `det Λ = 1`, `Λ₀₀ > 0`.

* `lorentz_natural_operator_classification` (`eq:supp-lorentz-commutant`):
  every real operator on the bivector carrier commuting with the induced
  action of every proper Lorentz matrix is `p·I + q·⋆`
  (`hodgeBivector`, `⋆(E,B) = (B,-E)`).  Only three explicit elements are
  used: two spatial rotations (`BivectorRotationCommutantExact.lean`) and one
  boost of rapidity `arcosh(5/4)`.
* `lorentz_natural_pairing_classification`: every real bilinear pairing on
  the bivector carrier invariant under the induced action of every proper
  Lorentz matrix is `a·(metric pairing) + b·(ε pairing)`, i.e. a combination
  of the Holst contraction `e^I ∧ e^J ∧ R_{IJ}` (internal indices contracted
  with `η`, `metricPairing`) and the Palatini contraction
  `½ ε_{IJKL} e^I ∧ e^J ∧ R^{KL}` (internal indices contracted with `ε`,
  `epsilonPairing = η ⋆`), with unique coefficients.
* `alternating_four_form_eq_smul_det`: every alternating four-form of the
  coframe is `λ · det` (the determinant volume `L_vol`).
* `gravitational_score_classification` (`eq:main-phv-coefficients`): a
  first-order bulk score modelled as (Lorentz-natural bivector/curvature
  pairing, alternating coframe four-form) is uniquely
  `α L_Holst + β L_Palatini + λ L_vol`.

Scoped modelling disclosed: the score's first-order bulk term is modelled as
a Lorentz-invariant real bilinear pairing of the coframe bivector with the
curvature (both valued in `Λ²ℝ^{1,3}`, the spacetime two-form part being
fixed by the wedge) plus an alternating coframe four-form; the manuscript's
hypotheses "scalar residual typed commutant" (no additional internal tensor)
and "represented determinant volume" are the assumptions of this model.  No
Palatini, Holst or Einstein action is assumed.
-/

open Matrix
open scoped BigOperators

namespace RenewalGeometry

open BivectorRotationCommutant

noncomputable section

/-! ### Proper Lorentz matrices and the induced bivector action -/

/-- Minkowski metric `η = diag(-1, 1, 1, 1)`. -/
def minkowski4 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![-1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

/-- Proper orthochronous Lorentz matrices `SO⁺(1,3)`. -/
structure IsProperLorentz (Λ : Matrix (Fin 4) (Fin 4) ℝ) : Prop where
  metric : Λᵀ * minkowski4 * Λ = minkowski4
  det : Λ.det = 1
  orthochronous : 0 < Λ 0 0

/-- Oriented index pair of each bivector basis element:
`E_i = e_0 ∧ e_{i+1}`, `B_0 = e_2 ∧ e_3`, `B_1 = e_3 ∧ e_1`, `B_2 = e_1 ∧ e_2`. -/
def bivectorPair (ab : BivectorIndex) : Fin 4 × Fin 4 :=
  ![![((0 : Fin 4), (1 : Fin 4)), (0, 2), (0, 3)], ![(2, 3), (3, 1), (1, 2)]] ab.1 ab.2

/-- The induced action `Λ²Λ` of a `4 × 4` matrix on the bivector carrier:
the coefficient of `e_c ∧ e_d` in `Λe_a ∧ Λe_b` is
`Λ_{ca} Λ_{db} - Λ_{da} Λ_{cb}`. -/
def inducedBivectorAction (Λ : Matrix (Fin 4) (Fin 4) ℝ) :
    Matrix BivectorIndex BivectorIndex ℝ :=
  fun α β =>
    Λ (bivectorPair α).1 (bivectorPair β).1 * Λ (bivectorPair α).2 (bivectorPair β).2 -
      Λ (bivectorPair α).2 (bivectorPair β).1 * Λ (bivectorPair α).1 (bivectorPair β).2

/-- Half-turn about the first spatial axis. -/
def halfTurn4 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1]

/-- Cyclic permutation of the three spatial axes. -/
def cycle4 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 0, 0, 0; 0, 0, 0, 1; 0, 1, 0, 0; 0, 0, 1, 0]

/-- Boost along the first spatial axis with `cosh φ = 5/4`, `sinh φ = 3/4`. -/
def boost4 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![5 / 4, 3 / 4, 0, 0; 3 / 4, 5 / 4, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

theorem halfTurn4_isProperLorentz : IsProperLorentz halfTurn4 where
  metric := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [halfTurn4, minkowski4, Matrix.mul_apply, Fin.sum_univ_four]
  det := by
    simp [halfTurn4, Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  orthochronous := by simp [halfTurn4]

theorem cycle4_isProperLorentz : IsProperLorentz cycle4 where
  metric := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [cycle4, minkowski4, Matrix.mul_apply, Fin.sum_univ_four]
  det := by
    simp [cycle4, Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  orthochronous := by simp [cycle4]

theorem boost4_isProperLorentz : IsProperLorentz boost4 where
  metric := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [boost4, minkowski4, Matrix.mul_apply, Fin.sum_univ_four] <;> norm_num
  det := by
    simp [boost4, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
    norm_num
  orthochronous := by simp [boost4]

/-- The induced action of the half-turn is the doubled spatial half-turn. -/
theorem inducedBivectorAction_halfTurn4 :
    inducedBivectorAction halfTurn4 = doubledRotation spatialHalfTurn := by
  ext ⟨a, i⟩ ⟨b, j⟩
  fin_cases a <;> fin_cases i <;> fin_cases b <;> fin_cases j <;>
    simp [inducedBivectorAction, bivectorPair, doubledRotation, halfTurn4, spatialHalfTurn]

/-- The induced action of the spatial cycle is the doubled spatial cycle. -/
theorem inducedBivectorAction_cycle4 :
    inducedBivectorAction cycle4 = doubledRotation spatialCycle := by
  ext ⟨a, i⟩ ⟨b, j⟩
  fin_cases a <;> fin_cases i <;> fin_cases b <;> fin_cases j <;>
    simp [inducedBivectorAction, bivectorPair, doubledRotation, cycle4, spatialCycle]

/-! ### The invariant pairings and the Hodge operator -/

/-- Metric pairing `E·E' - B·B'` on the bivector carrier (the internal
`η`-contraction of the Holst density `e^I ∧ e^J ∧ R_{IJ}`). -/
def metricPairing : Matrix BivectorIndex BivectorIndex ℝ :=
  scalarBlocks !![1, 0; 0, -1]

/-- `ε`-pairing `E·B' + B·E'` on the bivector carrier (the internal
`ε`-contraction of the Palatini density `½ ε_{IJKL} e^I ∧ e^J ∧ R^{KL}`). -/
def epsilonPairing : Matrix BivectorIndex BivectorIndex ℝ :=
  scalarBlocks !![0, 1; 1, 0]

/-- Hodge operator `⋆(E, B) = (B, -E)` on the bivector carrier. -/
def hodgeBivector : Matrix BivectorIndex BivectorIndex ℝ :=
  scalarBlocks !![0, 1; -1, 0]

theorem scalarBlocks_mul (C D : Matrix (Fin 2) (Fin 2) ℝ) :
    scalarBlocks C * scalarBlocks D = scalarBlocks (C * D) := by
  ext ⟨a, i⟩ ⟨b, j⟩
  simp [scalarBlocks, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]

theorem scalarBlocks_one : scalarBlocks (1 : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by
  ext ⟨a, i⟩ ⟨b, j⟩
  fin_cases a <;> fin_cases b <;> simp [scalarBlocks, Matrix.one_apply]

theorem metricPairing_mul_self : metricPairing * metricPairing = 1 := by
  rw [metricPairing, scalarBlocks_mul, ← scalarBlocks_one]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem metricPairing_mul_hodge : metricPairing * hodgeBivector = epsilonPairing := by
  rw [metricPairing, hodgeBivector, scalarBlocks_mul, epsilonPairing]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem doubledRotation_mul (R S : Matrix (Fin 3) (Fin 3) ℝ) :
    doubledRotation R * doubledRotation S = doubledRotation (R * S) := by
  ext ⟨a, i⟩ ⟨b, j⟩
  fin_cases a <;> fin_cases b <;>
    simp [doubledRotation, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]

theorem doubledRotation_transpose (R : Matrix (Fin 3) (Fin 3) ℝ) :
    (doubledRotation R)ᵀ = doubledRotation Rᵀ := by
  ext ⟨a, i⟩ ⟨b, j⟩
  fin_cases a <;> fin_cases b <;> simp [doubledRotation, Matrix.transpose_apply]

theorem doubledRotation_one : doubledRotation (1 : Matrix (Fin 3) (Fin 3) ℝ) = 1 := by
  ext ⟨a, i⟩ ⟨b, j⟩
  fin_cases a <;> fin_cases b <;> simp [doubledRotation, Matrix.one_apply]

theorem spatialHalfTurn_mul_transpose : spatialHalfTurn * spatialHalfTurnᵀ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [spatialHalfTurn, Matrix.mul_apply, Fin.sum_univ_three]

theorem spatialCycle_mul_transpose : spatialCycle * spatialCycleᵀ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [spatialCycle, Matrix.mul_apply, Fin.sum_univ_three]

/-- The bivector boost is symmetric. -/
theorem inducedBivectorAction_boost4_transpose :
    (inducedBivectorAction boost4)ᵀ = inducedBivectorAction boost4 := by
  ext ⟨a, i⟩ ⟨b, j⟩
  fin_cases a <;> fin_cases i <;> fin_cases b <;> fin_cases j <;>
    simp [inducedBivectorAction, bivectorPair, boost4, Matrix.transpose_apply] <;> norm_num

/-- The bivector boost preserves the metric pairing. -/
theorem boost_metricPairing_boost :
    inducedBivectorAction boost4 * metricPairing * inducedBivectorAction boost4 =
      metricPairing := by
  ext ⟨a, i⟩ ⟨b, j⟩
  fin_cases a <;> fin_cases i <;> fin_cases b <;> fin_cases j <;>
    simp [inducedBivectorAction, bivectorPair, boost4, metricPairing, scalarBlocks,
      Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three] <;>
    norm_num

/-! ### The commutant -/

/-- Commuting with the bivector boost cuts the scalar `2 × 2` block down to
`p I + q J`. -/
theorem boost_commutant_block (C : Matrix (Fin 2) (Fin 2) ℝ)
    (hboost : scalarBlocks C * inducedBivectorAction boost4 =
      inducedBivectorAction boost4 * scalarBlocks C) :
    C 1 1 = C 0 0 ∧ C 1 0 = -C 0 1 := by
  have h1 := congrFun (congrFun hboost (0, 1)) (1, 2)
  have h2 := congrFun (congrFun hboost (0, 1)) (0, 2)
  simp [scalarBlocks, inducedBivectorAction, bivectorPair, boost4, Matrix.mul_apply,
    Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_three] at h1 h2
  constructor <;> linarith

/-- `eq:supp-lorentz-commutant` on the three generators: an operator on the
bivector carrier commuting with the doubled half-turn, the doubled cycle and
the bivector boost is `p I + q ⋆`. -/
theorem commutant_generators_eq_scalar_add_hodge (T : Matrix BivectorIndex BivectorIndex ℝ)
    (hhalf : T * doubledRotation spatialHalfTurn = doubledRotation spatialHalfTurn * T)
    (hcycle : T * doubledRotation spatialCycle = doubledRotation spatialCycle * T)
    (hboost : T * inducedBivectorAction boost4 = inducedBivectorAction boost4 * T) :
    ∃ p q : ℝ, T = p • (1 : Matrix BivectorIndex BivectorIndex ℝ) + q • hodgeBivector := by
  have hT := rotation_commutant_scalar_blocks T hhalf hcycle
  set C : Matrix (Fin 2) (Fin 2) ℝ := fun a b => T (a, 0) (b, 0) with hC
  rw [hT] at hboost
  obtain ⟨h11, h10⟩ := boost_commutant_block C hboost
  refine ⟨C 0 0, C 0 1, ?_⟩
  rw [hT]
  ext ⟨a, i⟩ ⟨b, j⟩
  fin_cases a <;> fin_cases b <;>
    simp [scalarBlocks, hodgeBivector, Matrix.one_apply, h11, h10]

/-- `eq:supp-lorentz-commutant`, `End_{SO⁺(1,3)}(Λ²ℝ^{1,3}) = span{I, ⋆}`:
every real operator on the bivector carrier commuting with the induced action
of every proper Lorentz matrix is `p I + q ⋆`. -/
theorem lorentz_natural_operator_classification (T : Matrix BivectorIndex BivectorIndex ℝ)
    (hnat : ∀ Λ : Matrix (Fin 4) (Fin 4) ℝ, IsProperLorentz Λ →
      T * inducedBivectorAction Λ = inducedBivectorAction Λ * T) :
    ∃ p q : ℝ, T = p • (1 : Matrix BivectorIndex BivectorIndex ℝ) + q • hodgeBivector := by
  have h1 := hnat _ halfTurn4_isProperLorentz
  have h2 := hnat _ cycle4_isProperLorentz
  have h3 := hnat _ boost4_isProperLorentz
  rw [inducedBivectorAction_halfTurn4] at h1
  rw [inducedBivectorAction_cycle4] at h2
  exact commutant_generators_eq_scalar_add_hodge T h1 h2 h3

/-! ### Invariant pairings -/

/-- An invariant pairing under an orthogonal doubled rotation commutes with it. -/
theorem pairing_commutes_of_invariant_rotation (A : Matrix BivectorIndex BivectorIndex ℝ)
    (R : Matrix (Fin 3) (Fin 3) ℝ) (hR : R * Rᵀ = 1)
    (hinv : (doubledRotation R)ᵀ * A * doubledRotation R = A) :
    A * doubledRotation R = doubledRotation R * A := by
  have hRR : doubledRotation R * (doubledRotation R)ᵀ = 1 := by
    rw [doubledRotation_transpose, doubledRotation_mul, hR, doubledRotation_one]
  calc A * doubledRotation R
      = (doubledRotation R * (doubledRotation R)ᵀ) * A * doubledRotation R := by
        rw [hRR, Matrix.one_mul]
    _ = doubledRotation R * ((doubledRotation R)ᵀ * A * doubledRotation R) := by
        simp only [Matrix.mul_assoc]
    _ = doubledRotation R * A := by rw [hinv]

/-- The `η`-twist `η A` of a boost-invariant pairing commutes with the boost. -/
theorem metric_mul_pairing_commutes_boost (A : Matrix BivectorIndex BivectorIndex ℝ)
    (hinv : (inducedBivectorAction boost4)ᵀ * A * inducedBivectorAction boost4 = A) :
    (metricPairing * A) * inducedBivectorAction boost4 =
      inducedBivectorAction boost4 * (metricPairing * A) := by
  rw [inducedBivectorAction_boost4_transpose] at hinv
  have hBηB := boost_metricPairing_boost
  set B := inducedBivectorAction boost4 with hB
  calc metricPairing * A * B = (B * metricPairing * B) * A * B := by rw [hBηB]
    _ = B * metricPairing * (B * A * B) := by simp only [Matrix.mul_assoc]
    _ = B * (metricPairing * A) := by rw [hinv, Matrix.mul_assoc]

/-- Lorentz-natural pairing classification: every real bilinear pairing on
the bivector carrier invariant under the induced action of every proper
Lorentz matrix is `a·(metric pairing) + b·(ε pairing)`, i.e. a combination of
the Holst and Palatini internal contractions. -/
theorem lorentz_natural_pairing_classification (A : Matrix BivectorIndex BivectorIndex ℝ)
    (hnat : ∀ Λ : Matrix (Fin 4) (Fin 4) ℝ, IsProperLorentz Λ →
      (inducedBivectorAction Λ)ᵀ * A * inducedBivectorAction Λ = A) :
    ∃ a b : ℝ, A = a • metricPairing + b • epsilonPairing := by
  have h1 := hnat _ halfTurn4_isProperLorentz
  have h2 := hnat _ cycle4_isProperLorentz
  have h3 := hnat _ boost4_isProperLorentz
  rw [inducedBivectorAction_halfTurn4] at h1
  rw [inducedBivectorAction_cycle4] at h2
  have c1 := pairing_commutes_of_invariant_rotation A _ spatialHalfTurn_mul_transpose h1
  have c2 := pairing_commutes_of_invariant_rotation A _ spatialCycle_mul_transpose h2
  have c3 := metric_mul_pairing_commutes_boost A h3
  have m1 : (metricPairing * A) * doubledRotation spatialHalfTurn =
      doubledRotation spatialHalfTurn * (metricPairing * A) := by
    rw [Matrix.mul_assoc, c1, ← Matrix.mul_assoc, metricPairing,
      scalarBlocks_commutes_doubledRotation, Matrix.mul_assoc]
  have m2 : (metricPairing * A) * doubledRotation spatialCycle =
      doubledRotation spatialCycle * (metricPairing * A) := by
    rw [Matrix.mul_assoc, c2, ← Matrix.mul_assoc, metricPairing,
      scalarBlocks_commutes_doubledRotation, Matrix.mul_assoc]
  obtain ⟨p, q, hpq⟩ := commutant_generators_eq_scalar_add_hodge (metricPairing * A) m1 m2 c3
  refine ⟨p, q, ?_⟩
  have hA : A = metricPairing * (metricPairing * A) := by
    rw [← Matrix.mul_assoc, metricPairing_mul_self, Matrix.one_mul]
  rw [hA, hpq, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one,
    metricPairing_mul_hodge]

/-- The metric and `ε` pairings are linearly independent: the coefficients of
`a·metric + b·ε` are unique. -/
theorem pairing_coefficients_unique {a b a' b' : ℝ}
    (h : a • metricPairing + b • epsilonPairing = a' • metricPairing + b' • epsilonPairing) :
    a = a' ∧ b = b' := by
  have h1 := congrFun (congrFun h (0, 0)) (0, 0)
  have h2 := congrFun (congrFun h (0, 0)) (1, 0)
  simp [metricPairing, epsilonPairing, scalarBlocks] at h1 h2
  exact ⟨h1, h2⟩

/-! ### The volume term -/

/-- Every alternating four-form of the coframe is a multiple of the
determinant: the only alternating four-coframe scalar is `L_vol = λ det`. -/
theorem alternating_four_form_eq_smul_det (ω : (Fin 4 → ℝ) [⋀^Fin 4]→ₗ[ℝ] ℝ) :
    ∃ c : ℝ, ω = c • (Pi.basisFun ℝ (Fin 4)).det :=
  ⟨ω (Pi.basisFun ℝ (Fin 4)), AlternatingMap.eq_smul_basis_det (Pi.basisFun ℝ (Fin 4)) ω⟩

/-- The determinant four-form evaluates to the matrix determinant. -/
theorem basisFun_det_apply (v : Fin 4 → Fin 4 → ℝ) :
    (Pi.basisFun ℝ (Fin 4)).det v = Matrix.det (Matrix.of v) := by
  rw [Pi.basisFun_det]
  rfl

/-! ### The classification -/

/-- `thm:main-gravitational-classification`, `eq:main-phv-coefficients`:
a first-order Lorentz-natural bulk score, modelled as a real bilinear
bivector/curvature pairing `A` invariant under the induced action of every
proper Lorentz matrix together with an alternating coframe four-form `ω`, has
unique real coefficients `(α, β, λ)` with
`A = α·(Holst contraction) + β·(Palatini contraction)` and
`ω = λ·det` (the volume term); i.e. the score lies in
`span{L_Holst, L_Palatini, L_vol}` (`eq:main-phv-classification`). -/
theorem gravitational_score_classification (A : Matrix BivectorIndex BivectorIndex ℝ)
    (ω : (Fin 4 → ℝ) [⋀^Fin 4]→ₗ[ℝ] ℝ)
    (hnat : ∀ Λ : Matrix (Fin 4) (Fin 4) ℝ, IsProperLorentz Λ →
      (inducedBivectorAction Λ)ᵀ * A * inducedBivectorAction Λ = A) :
    ∃! c : ℝ × ℝ × ℝ,
      A = c.1 • metricPairing + c.2.1 • epsilonPairing ∧
        ω = c.2.2 • (Pi.basisFun ℝ (Fin 4)).det := by
  obtain ⟨a, b, hab⟩ := lorentz_natural_pairing_classification A hnat
  obtain ⟨c, hc⟩ := alternating_four_form_eq_smul_det ω
  refine ⟨(a, b, c), ⟨hab, hc⟩, ?_⟩
  rintro ⟨a', b', c'⟩ ⟨hab', hc'⟩
  obtain ⟨ha, hb⟩ := pairing_coefficients_unique (hab'.symm.trans hab)
  have hcc : c' = c := by
    have h := congrArg (fun f => f (Pi.basisFun ℝ (Fin 4))) (hc'.symm.trans hc)
    simp only [AlternatingMap.smul_apply, Module.Basis.det_self, smul_eq_mul, mul_one] at h
    exact h
  simp only [Prod.mk.injEq]
  exact ⟨ha, hb, hcc⟩

end

end RenewalGeometry
