/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.Dimension.K4TwistedExteriorSquareMultiplicity

/-!
# Isometric normalization of the `S₄` twisted Hodge identification
  (`prop:supp-source-equivalence`, last clause; emergent-spacetime manuscript)

`prop:supp-source-equivalence`: for `N ≥ 3` an `S_N`-equivariant isomorphism
`Λ²W_N → W_N ⊗ sgn` exists iff `N = 4` (`standardTwistedExteriorTensor_zero_of_ne_four`,
`k4TwistedHodgeMatrix_det`), at `N = 4` its space is one-dimensional
(`k4TwistedExteriorSquare_intertwiner_unique`), and *with the standard invariant
Euclidean forms an isometric choice is unique up to sign*.  This file proves the last
clause over `ℝ`.

Coordinates (as in `K4CutCycleIsotypicSchur.lean` / `K4TwistedExteriorSquareMultiplicity.lean`):
`W_4` carries the basis `f_i = e_i - e_3` (`i = 0, 1, 2`) of the centred standard
permutation module, on which the transposition `(01)` and the four-cycle `(0123)` act by
`k4StandardTranspositionReal`, `k4StandardFourCycleReal`; `Λ²W_4` carries the wedge basis
`f₀∧f₁, f₀∧f₂, f₁∧f₂` with the second compound matrices
`k4ExteriorSquareTranspositionReal`, `k4ExteriorSquareFourCycleReal`.

* `k4StandardGram` — the Gram matrix `⟨f_i, f_j⟩ = δ_ij + 1` of the standard Euclidean
  form restricted to `W_4` (`k4StandardGram_apply`); it is `S_4`-invariant
  (`k4StandardGram_invariant_transposition`, `k4StandardGram_invariant_fourCycle`).
* `k4ExteriorSquareGram` — the induced Euclidean form on `Λ²W_4`,
  `⟨u∧v, u'∧v'⟩ = ⟨u,u'⟩⟨v,v'⟩ - ⟨u,v'⟩⟨v,u'⟩` (`k4ExteriorSquareGram_eq_induced`);
  it is `S_4`-invariant (`k4ExteriorSquareGram_invariant_*`).
* `k4TwistedHodgeMatrixReal_gram` — the integral Hodge identification `H` satisfies
  `Hᵀ G_W H = 4 · G_{Λ²}`.
* `k4TwistedExteriorSquare_real_intertwiner_unique` — every real intertwiner is a
  unique real multiple of `H` (transported from the complex multiplicity-one statement).
* `k4TwistedExteriorSquare_isometric_iff` — a real intertwiner `B` is an isometry
  `Bᵀ G_W B = G_{Λ²}` iff `B = ±(1/2) H`.
* `k4TwistedExteriorSquare_isometric_intertwiner_unique_up_to_sign` — the last clause of
  `prop:supp-source-equivalence`: an isometric equivariant identification exists and is
  unique up to sign.
-/

open Matrix

namespace RenewalGeometry

/-! ### Real coordinates -/

/-- The transposition `(01)` on `W_4` in the basis `f_i = e_i - e_3`. -/
def k4StandardTranspositionReal : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, 1, 0; 1, 0, 0; 0, 0, 1]

/-- The four-cycle `(0123)` on `W_4` in the basis `f_i = e_i - e_3`. -/
def k4StandardFourCycleReal : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-1, -1, -1; 1, 0, 0; 0, 1, 0]

/-- The transposition on `Λ²W_4` in the wedge basis `(01, 02, 12)`. -/
def k4ExteriorSquareTranspositionReal : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-1, 0, 0; 0, 0, 1; 0, 1, 0]

/-- The four-cycle on `Λ²W_4` in the wedge basis `(01, 02, 12)`. -/
def k4ExteriorSquareFourCycleReal : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 1, 0; -1, 0, 1; 1, 0, 0]

/-- The integral Hodge identification `Λ²W_4 → W_4 ⊗ sgn`, real form. -/
def k4TwistedHodgeMatrixReal : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, -1, -3; 1, 3, 1; -3, -1, 1]

/-- The standard invariant Euclidean form on `W_4` in the basis `f_i = e_i - e_3`. -/
def k4StandardGram : Matrix (Fin 3) (Fin 3) ℝ :=
  !![2, 1, 1; 1, 2, 1; 1, 1, 2]

/-- The induced invariant Euclidean form on `Λ²W_4` in the wedge basis `(01, 02, 12)`. -/
def k4ExteriorSquareGram : Matrix (Fin 3) (Fin 3) ℝ :=
  !![3, 1, -1; 1, 3, 1; -1, 1, 3]

/-- The index pairs of the wedge basis `f₀∧f₁, f₀∧f₂, f₁∧f₂`. -/
def k4WedgePair : Fin 3 → Fin 3 × Fin 3 :=
  ![((0 : Fin 3), (1 : Fin 3)), (0, 2), (1, 2)]

/-- `⟨f_i, f_j⟩ = ⟨e_i - e_3, e_j - e_3⟩ = δ_ij + 1`. -/
theorem k4StandardGram_apply (i j : Fin 3) :
    k4StandardGram i j = (if i = j then 1 else 0) + 1 := by
  fin_cases i <;> fin_cases j <;> norm_num [k4StandardGram, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val]

/-- The exterior-square Gram matrix is the form induced by the standard form:
`⟨u∧v, u'∧v'⟩ = ⟨u,u'⟩⟨v,v'⟩ - ⟨u,v'⟩⟨v,u'⟩` on the wedge basis. -/
theorem k4ExteriorSquareGram_eq_induced (i j : Fin 3) :
    k4ExteriorSquareGram i j =
      k4StandardGram (k4WedgePair i).1 (k4WedgePair j).1 *
          k4StandardGram (k4WedgePair i).2 (k4WedgePair j).2 -
        k4StandardGram (k4WedgePair i).1 (k4WedgePair j).2 *
          k4StandardGram (k4WedgePair i).2 (k4WedgePair j).1 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [k4ExteriorSquareGram, k4StandardGram, k4WedgePair, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val]

/-! ### Invariance of the Euclidean forms under the generators -/

theorem k4StandardGram_invariant_transposition :
    k4StandardTranspositionRealᵀ * k4StandardGram * k4StandardTranspositionReal =
      k4StandardGram := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [k4StandardTranspositionReal, k4StandardGram, Matrix.mul_apply,
      Fin.sum_univ_three, Matrix.transpose_apply, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val]

theorem k4StandardGram_invariant_fourCycle :
    k4StandardFourCycleRealᵀ * k4StandardGram * k4StandardFourCycleReal =
      k4StandardGram := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [k4StandardFourCycleReal, k4StandardGram, Matrix.mul_apply,
      Fin.sum_univ_three, Matrix.transpose_apply, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val]

theorem k4ExteriorSquareGram_invariant_transposition :
    k4ExteriorSquareTranspositionRealᵀ * k4ExteriorSquareGram *
        k4ExteriorSquareTranspositionReal = k4ExteriorSquareGram := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [k4ExteriorSquareTranspositionReal, k4ExteriorSquareGram, Matrix.mul_apply,
      Fin.sum_univ_three, Matrix.transpose_apply, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val]

theorem k4ExteriorSquareGram_invariant_fourCycle :
    k4ExteriorSquareFourCycleRealᵀ * k4ExteriorSquareGram *
        k4ExteriorSquareFourCycleReal = k4ExteriorSquareGram := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [k4ExteriorSquareFourCycleReal, k4ExteriorSquareGram, Matrix.mul_apply,
      Fin.sum_univ_three, Matrix.transpose_apply, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val]

/-! ### The Hodge identification against the invariant forms -/

/-- The real Hodge identification intertwines the generator actions. -/
theorem k4TwistedHodgeMatrixReal_intertwines :
    k4TwistedHodgeMatrixReal * k4ExteriorSquareTranspositionReal =
        (-k4StandardTranspositionReal) * k4TwistedHodgeMatrixReal
    ∧ k4TwistedHodgeMatrixReal * k4ExteriorSquareFourCycleReal =
        (-k4StandardFourCycleReal) * k4TwistedHodgeMatrixReal := by
  constructor <;>
    ext i j <;>
    fin_cases i <;> fin_cases j <;>
    norm_num [k4TwistedHodgeMatrixReal, k4ExteriorSquareTranspositionReal,
      k4ExteriorSquareFourCycleReal, k4StandardTranspositionReal,
      k4StandardFourCycleReal, Matrix.mul_apply, Fin.sum_univ_three, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val]

/-- `Hᵀ G_W H = 4 · G_{Λ²}`: the integral Hodge identification is conformal with factor
`4` for the standard invariant Euclidean forms. -/
theorem k4TwistedHodgeMatrixReal_gram :
    k4TwistedHodgeMatrixRealᵀ * k4StandardGram * k4TwistedHodgeMatrixReal =
      (4 : ℝ) • k4ExteriorSquareGram := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [k4TwistedHodgeMatrixReal, k4StandardGram, k4ExteriorSquareGram,
      Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val]

/-- The real Hodge identification is nonsingular (`det = -16`). -/
theorem k4TwistedHodgeMatrixReal_det : k4TwistedHodgeMatrixReal.det = -16 := by
  rw [Matrix.det_fin_three]
  norm_num [k4TwistedHodgeMatrixReal, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val]

/-! ### Transport of multiplicity one to real coefficients -/

theorem k4StandardTranspositionReal_map :
    k4StandardTranspositionReal.map Complex.ofRealHom = k4StandardTransposition := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [k4StandardTranspositionReal, k4StandardTransposition]

theorem k4StandardFourCycleReal_map :
    k4StandardFourCycleReal.map Complex.ofRealHom = k4StandardFourCycle := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [k4StandardFourCycleReal, k4StandardFourCycle]

theorem k4ExteriorSquareTranspositionReal_map :
    k4ExteriorSquareTranspositionReal.map Complex.ofRealHom =
      k4ExteriorSquareTransposition := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [k4ExteriorSquareTranspositionReal, k4ExteriorSquareTransposition]

theorem k4ExteriorSquareFourCycleReal_map :
    k4ExteriorSquareFourCycleReal.map Complex.ofRealHom = k4ExteriorSquareFourCycle := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [k4ExteriorSquareFourCycleReal, k4ExteriorSquareFourCycle]

theorem k4TwistedHodgeMatrixReal_map :
    k4TwistedHodgeMatrixReal.map Complex.ofRealHom = k4TwistedHodgeMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [k4TwistedHodgeMatrixReal, k4TwistedHodgeMatrix]

/-- **Multiplicity one over `ℝ`**: every real intertwiner `Λ²W_4 → W_4 ⊗ sgn` (tested on
the generators) is a unique real multiple of the Hodge identification. -/
theorem k4TwistedExteriorSquare_real_intertwiner_unique
    (B : Matrix (Fin 3) (Fin 3) ℝ)
    (hs : B * k4ExteriorSquareTranspositionReal = (-k4StandardTranspositionReal) * B)
    (ht : B * k4ExteriorSquareFourCycleReal = (-k4StandardFourCycleReal) * B) :
    ∃! α : ℝ, B = α • k4TwistedHodgeMatrixReal := by
  have hs' : B.map Complex.ofRealHom * k4ExteriorSquareTransposition =
      (-k4StandardTransposition) * B.map Complex.ofRealHom := by
    rw [← k4ExteriorSquareTranspositionReal_map, ← k4StandardTranspositionReal_map,
      ← Matrix.map_mul, hs, Matrix.map_mul, Matrix.map_neg _ (fun a => map_neg Complex.ofRealHom a)]
  have ht' : B.map Complex.ofRealHom * k4ExteriorSquareFourCycle =
      (-k4StandardFourCycle) * B.map Complex.ofRealHom := by
    rw [← k4ExteriorSquareFourCycleReal_map, ← k4StandardFourCycleReal_map,
      ← Matrix.map_mul, ht, Matrix.map_mul, Matrix.map_neg _ (fun a => map_neg Complex.ofRealHom a)]
  obtain ⟨α, hα, -⟩ := k4TwistedExteriorSquare_intertwiner_unique _ hs' ht'
  have hentry : ∀ i j, (B i j : ℂ) = α * (k4TwistedHodgeMatrixReal i j : ℂ) := by
    intro i j
    have h := congrFun (congrFun hα i) j
    rw [← k4TwistedHodgeMatrixReal_map] at h
    simpa using h
  have hα22 : α = (B 2 2 : ℂ) := by
    have h := hentry 2 2
    simp [k4TwistedHodgeMatrixReal] at h
    exact h.symm
  refine ⟨B 2 2, ?_, ?_⟩
  · ext i j
    have h := hentry i j
    rw [hα22, ← Complex.ofReal_mul] at h
    have h' := Complex.ofReal_injective h
    simp only [Matrix.smul_apply, smul_eq_mul]
    exact h'
  · intro β hβ
    have h := congrFun (congrFun hβ 2) 2
    simp [k4TwistedHodgeMatrixReal] at h
    exact h.symm

/-! ### The isometric normalization -/

/-- A map `Λ²W_4 → W_4` is an isometry for the standard invariant Euclidean forms when
`Bᵀ G_W B = G_{Λ²}`. -/
def IsK4TwistedIsometry (B : Matrix (Fin 3) (Fin 3) ℝ) : Prop :=
  Bᵀ * k4StandardGram * B = k4ExteriorSquareGram

/-- A real multiple `α H` of the Hodge identification is isometric iff `4α² = 1`. -/
theorem isK4TwistedIsometry_smul_iff (α : ℝ) :
    IsK4TwistedIsometry (α • k4TwistedHodgeMatrixReal) ↔ α = 1 / 2 ∨ α = -(1 / 2) := by
  unfold IsK4TwistedIsometry
  have hgram : (α • k4TwistedHodgeMatrixReal)ᵀ * k4StandardGram *
      (α • k4TwistedHodgeMatrixReal) = (4 * α ^ 2) • k4ExteriorSquareGram := by
    rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul,
      k4TwistedHodgeMatrixReal_gram, smul_smul, smul_smul]
    congr 1
    ring
  rw [hgram]
  constructor
  · intro h
    have h00 := congrFun (congrFun h 0) 0
    simp [k4ExteriorSquareGram] at h00
    have hsq : (2 * α - 1) * (2 * α + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hsq with h1 | h1
    · left; linarith
    · right; linarith
  · rintro (rfl | rfl) <;> norm_num

/-- **`prop:supp-source-equivalence`, last clause (pointwise form)**: a real equivariant
map `Λ²W_4 → W_4 ⊗ sgn` is an isometry for the standard invariant Euclidean forms iff it
is `±(1/2) H`. -/
theorem k4TwistedExteriorSquare_isometric_iff
    (B : Matrix (Fin 3) (Fin 3) ℝ)
    (hs : B * k4ExteriorSquareTranspositionReal = (-k4StandardTranspositionReal) * B)
    (ht : B * k4ExteriorSquareFourCycleReal = (-k4StandardFourCycleReal) * B) :
    IsK4TwistedIsometry B ↔
      B = (1 / 2 : ℝ) • k4TwistedHodgeMatrixReal ∨
        B = -((1 / 2 : ℝ) • k4TwistedHodgeMatrixReal) := by
  obtain ⟨α, hα, -⟩ := k4TwistedExteriorSquare_real_intertwiner_unique B hs ht
  subst hα
  rw [isK4TwistedIsometry_smul_iff, ← neg_smul]
  constructor
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rintro (h | h)
    · left
      have := congrFun (congrFun h 2) 2
      simp [k4TwistedHodgeMatrixReal] at this
      linarith
    · right
      have := congrFun (congrFun h 2) 2
      simp [k4TwistedHodgeMatrixReal] at this
      linarith

/-- **`prop:supp-source-equivalence`, last clause**: with the standard invariant Euclidean
forms on `Λ²W_4` and `W_4 ⊗ sgn`, an isometric `S_4`-equivariant identification exists
(`B₀ = (1/2) H`, nonsingular) and every isometric equivariant map is `±B₀`. -/
theorem k4TwistedExteriorSquare_isometric_intertwiner_unique_up_to_sign :
    ∃ B₀ : Matrix (Fin 3) (Fin 3) ℝ,
      (B₀ * k4ExteriorSquareTranspositionReal = (-k4StandardTranspositionReal) * B₀ ∧
        B₀ * k4ExteriorSquareFourCycleReal = (-k4StandardFourCycleReal) * B₀ ∧
        IsK4TwistedIsometry B₀ ∧ B₀.det ≠ 0) ∧
      ∀ B : Matrix (Fin 3) (Fin 3) ℝ,
        B * k4ExteriorSquareTranspositionReal = (-k4StandardTranspositionReal) * B →
        B * k4ExteriorSquareFourCycleReal = (-k4StandardFourCycleReal) * B →
        (IsK4TwistedIsometry B ↔ B = B₀ ∨ B = -B₀) := by
  refine ⟨(1 / 2 : ℝ) • k4TwistedHodgeMatrixReal, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [Matrix.smul_mul, k4TwistedHodgeMatrixReal_intertwines.1, Matrix.mul_smul]
  · rw [Matrix.smul_mul, k4TwistedHodgeMatrixReal_intertwines.2, Matrix.mul_smul]
  · exact (isK4TwistedIsometry_smul_iff _).2 (Or.inl rfl)
  · rw [Matrix.det_smul, k4TwistedHodgeMatrixReal_det]
    norm_num
  · intro B hs ht
    exact k4TwistedExteriorSquare_isometric_iff B hs ht

end RenewalGeometry
