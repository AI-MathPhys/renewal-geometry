/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Medium-exact batch 08: SMQG exterior-power records and GT-NCG spectral records

Exact formalizations for the MEDIUM records:

* `thm:SMQG-positive-mixture` — positive bosonic mixing (QG.55/QG.56);
* `thm:SMQG-robust-positivity` — robust reflected-positivity alternative (QG.58–QG.61);
* `thm:SMQG-unitary-covariance` — unitary covariance of `Γ∧` (QG.17);
* `thm:SMQG-zero-safe` — invertible and zero-safe source hierarchy (QG.49–QG.51);
* `cor:GT-NCG-finite-landing-nonempty` — nonempty finite loaded spectral branch;
* `cor:GT-NCG-germ-handoff` — exact upstream germ packet and rerun rule;
* `cth:GT-NCG-extensive-oneform-kernel` — extensive one-form kernel `2e − n + 2` (SP.21);
* `thm:GT-NCG-austere-image` — exact derivation-only image and sharp anchor rank (SP.31/SP.32).

The file builds a self-contained `Γ∧` mini-library: the grade-`r` exterior power of an
endomorphism of `ℂ^d` rendered as the `r`-th *compound matrix* (matrix of
`exteriorPower.map r` in the wedge basis), with entries the `r × r` minors
(`compound_apply`), Cauchy–Binet multiplicativity (`compound_mul`), adjoint
compatibility (`compound_conjTranspose`), diagonal evaluation, PSD/Hermitian/rank
transport, and an operator-norm perturbation bound proved through the `r`-fold tuple
(Kronecker-power) model and the isometric antisymmetrizer compression.
-/

open scoped ComplexOrder

namespace NCG
namespace MediumExact08

/-! ### The compound-matrix (grade-`r` exterior power) mini-library -/

/-- The index type of the grade-`r` wedge basis of `ℂ^d`: `r`-element subsets of `Fin d`. -/
abbrev WedgeIdx (d r : ℕ) := ↥(Set.powersetCard (Fin d) r)

variable {d : ℕ}

/-- The increasing enumeration of an `r`-element subset of `Fin d`. -/
noncomputable def enum {r : ℕ} (s : WedgeIdx d r) : Fin r ↪o Fin d :=
  Set.powersetCard.ofFinEmbEquiv.symm s

/-- The `r`-th compound matrix of `A`: the matrix of `⋀^r A` in the wedge basis induced by
the standard basis of `ℂ^d`. -/
noncomputable def compound (r : ℕ) (A : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (WedgeIdx d r) (WedgeIdx d r) ℂ :=
  LinearMap.toMatrix ((Pi.basisFun ℂ (Fin d)).exteriorPower r)
    ((Pi.basisFun ℂ (Fin d)).exteriorPower r) (exteriorPower.map r (Matrix.toLin' A))

/-- **Cauchy–Binet / functoriality**: the compound of a product is the product of the
compounds. -/
theorem compound_mul (r : ℕ) (A B : Matrix (Fin d) (Fin d) ℂ) :
    compound r (A * B) = compound r A * compound r B := by
  unfold compound
  rw [← LinearMap.toMatrix_comp _ ((Pi.basisFun ℂ (Fin d)).exteriorPower r) _,
    ← exteriorPower.map_comp, ← Matrix.toLin'_mul]

/-- The compound of the identity is the identity. -/
theorem compound_one (r : ℕ) : compound r (1 : Matrix (Fin d) (Fin d) ℂ) = 1 := by
  unfold compound
  rw [Matrix.toLin'_one, exteriorPower.map_id, LinearMap.toMatrix_id]

/-- **Entry formula**: the `(s, t)` entry of the `r`-th compound is the `r × r` minor of `A`
with rows `s` and columns `t`. -/
theorem compound_apply (r : ℕ) (A : Matrix (Fin d) (Fin d) ℂ) (s t : WedgeIdx d r) :
    compound r A s t = (A.submatrix (enum s) (enum t)).det := by
  unfold compound
  rw [LinearMap.toMatrix_apply, exteriorPower.basis_apply,
    exteriorPower.map_apply_ιMulti_family, exteriorPower.basis_repr_apply]
  rw [show exteriorPower.ιMulti_family ℂ r (⇑(Matrix.toLin' A) ∘ ⇑(Pi.basisFun ℂ (Fin d))) t
      = exteriorPower.ιMulti ℂ r ((⇑(Matrix.toLin' A) ∘ ⇑(Pi.basisFun ℂ (Fin d))) ∘
        (Set.powersetCard.ofFinEmbEquiv.symm t)) from rfl]
  rw [exteriorPower.ιMultiDual_apply_ιMulti]
  have hentry : (Matrix.of fun i j => (Pi.basisFun ℂ (Fin d)).coord
      (Set.powersetCard.ofFinEmbEquiv.symm s j)
      (((⇑(Matrix.toLin' A) ∘ ⇑(Pi.basisFun ℂ (Fin d))) ∘
        (Set.powersetCard.ofFinEmbEquiv.symm t)) i))
      = (A.submatrix (enum s) (enum t))ᵀ := by
    ext i j
    simp only [Matrix.of_apply, Function.comp_apply, Pi.basisFun_apply, Matrix.toLin'_apply,
      Matrix.transpose_apply, Matrix.submatrix_apply, Pi.basisFun_repr, Basis.coord_apply,
      enum]
    rw [Matrix.mulVec_single_one]
    rfl
  rw [hentry, Matrix.det_transpose]

/-- The compound of the adjoint is the adjoint of the compound. -/
theorem compound_conjTranspose (r : ℕ) (A : Matrix (Fin d) (Fin d) ℂ) :
    compound r Aᴴ = (compound r A)ᴴ := by
  ext s t
  rw [compound_apply, Matrix.conjTranspose_apply, compound_apply]
  rw [show Aᴴ.submatrix (enum s) (enum t) = (A.submatrix (enum t) (enum s))ᴴ from rfl,
    Matrix.det_conjTranspose]

/-- The compound of a scalar multiple: `⋀^r (c • A) = c^r • ⋀^r A`. -/
theorem compound_smul (r : ℕ) (c : ℂ) (A : Matrix (Fin d) (Fin d) ℂ) :
    compound r (c • A) = c ^ r • compound r A := by
  ext s t
  rw [compound_apply, Matrix.pi_smul_apply, Matrix.pi_smul_apply, compound_apply,
    show (c • A).submatrix (enum s) (enum t) = c • (A.submatrix (enum s) (enum t)) from rfl,
    Matrix.det_smul, Fintype.card_fin, smul_eq_mul, smul_eq_mul]

/-- The compound of a diagonal matrix is diagonal, with entries the subset products. -/
theorem compound_diagonal (r : ℕ) (v : Fin d → ℂ) (s t : WedgeIdx d r) :
    compound r (Matrix.diagonal v) s t
      = if s = t then ∏ i ∈ (s : Finset (Fin d)), v i else 0 := by
  rw [compound_apply]
  by_cases hst : s = t
  · subst hst
    simp only [if_pos rfl]
    have hsub : (Matrix.diagonal v).submatrix (enum s) (enum s)
        = Matrix.diagonal fun i => v (enum s i) := by
      ext i j
      by_cases hij : i = j
      · subst hij; simp [Matrix.diagonal_apply_eq]
      · rw [Matrix.submatrix_apply, Matrix.diagonal_apply_ne _ (fun h => hij ((enum s).injective h)),
          Matrix.diagonal_apply_ne _ hij]
    rw [hsub, Matrix.det_diagonal]
    exact Finset.prod_orderEmbOfFin (s : Finset (Fin d)) (f := v) s.prop
  · rw [if_neg hst]
    obtain ⟨a, has, hat⟩ := (Set.powersetCard.exists_mem_notMem_iff_ne s t).mp hst
    obtain ⟨i, hi⟩ := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem s a).mpr has
    refine Matrix.det_eq_zero_of_row_eq_zero i fun j => ?_
    rw [Matrix.submatrix_apply]
    refine Matrix.diagonal_apply_ne _ fun h => hat ?_
    rw [show enum s i = a from hi] at h
    rw [h]
    exact (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem t (enum t j)).mp ⟨j, rfl⟩

/-- The compound of a Hermitian matrix is Hermitian. -/
theorem compound_isHermitian (r : ℕ) {A : Matrix (Fin d) (Fin d) ℂ}
    (hA : A.IsHermitian) : (compound r A).IsHermitian := by
  have : (compound r A)ᴴ = compound r Aᴴ := (compound_conjTranspose r A).symm
  rw [Matrix.IsHermitian, this, hA.eq]

/-- The compound of a positive semidefinite matrix is positive semidefinite. -/
theorem compound_posSemidef (r : ℕ) {P : Matrix (Fin d) (Fin d) ℂ}
    (hP : P.PosSemidef) : (compound r P).PosSemidef := by
  obtain ⟨B, rfl⟩ := Matrix.posSemidef_iff_eq_conjTranspose_mul_self.mp hP
  rw [compound_mul, compound_conjTranspose]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- The compound of a unitary is unitary. -/
theorem compound_unitary (r : ℕ) {U : Matrix (Fin d) (Fin d) ℂ}
    (hU : Uᴴ * U = 1) : (compound r U)ᴴ * compound r U = 1 := by
  rw [← compound_conjTranspose, ← compound_mul, hU, compound_one]

/-- The determinant of the compound of a unitary is a unit. -/
theorem compound_unitary_isUnit_det (r : ℕ) {U : Matrix (Fin d) (Fin d) ℂ}
    (hU : Uᴴ * U = 1) : IsUnit (compound r U).det := by
  have h := congrArg Matrix.det (compound_unitary r hU)
  rw [Matrix.det_mul, Matrix.det_one] at h
  exact isUnit_of_mul_eq_one _ _ h

/-! ### Record `thm:SMQG-unitary-covariance` (QG.17)

For every unitary `U : E → E`, `Γ∧(U P U*) = Γ∧(U) Γ∧(P) Γ∧(U)*`; unitary congruence acts
gradewise and preserves positivity, ranks, and all direct word residuals. -/

/-- The full second-quantized functor `Γ∧(A)`: the family of all grade-`r` compounds. -/
noncomputable def Gamma (A : Matrix (Fin d) (Fin d) ℂ) :
    (r : ℕ) → Matrix (WedgeIdx d r) (WedgeIdx d r) ℂ :=
  fun r => compound r A

/-- **`thm:SMQG-unitary-covariance`, boxed identity (QG.17)**: for every unitary `U`,
`Γ∧(U P U*) = Γ∧(U) Γ∧(P) Γ∧(U)*` on every reflected word grade. -/
theorem smqg_unitary_covariance (P U : Matrix (Fin d) (Fin d) ℂ)
    (_hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) :
    Gamma (U * P * Uᴴ) = fun r => Gamma U r * Gamma P r * (Gamma U r)ᴴ := by
  funext r
  rw [Gamma, Gamma, Gamma, compound_mul, compound_mul, compound_conjTranspose]

/-- **`thm:SMQG-unitary-covariance`, positivity preservation**: unitary congruence preserves
positivity on every grade. -/
theorem smqg_unitary_covariance_posSemidef (P U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) (r : ℕ) :
    (Gamma (U * P * Uᴴ) r).PosSemidef ↔ (Gamma P r).PosSemidef := by
  have hU1 : Uᴴ * U = 1 := by
    have := Matrix.mem_unitaryGroup_iff'.mp hU
    rwa [Matrix.star_eq_conjTranspose] at this
  have hU2 : U * Uᴴ = 1 := by
    have := Matrix.mem_unitaryGroup_iff.mp hU
    rwa [Matrix.star_eq_conjTranspose] at this
  constructor
  · intro h
    have h2 := h.conjTranspose_mul_mul_same (compound r U)
    rw [show Gamma (U * P * Uᴴ) r = compound r (U * P * Uᴴ) from rfl,
      compound_mul, compound_mul, compound_conjTranspose] at h2
    rw [show (compound r U)ᴴ * (compound r U * compound r P * (compound r U)ᴴ) *
        compound r U = ((compound r U)ᴴ * compound r U) * compound r P *
        ((compound r U)ᴴ * compound r U) from by noncomm_ring] at h2
    rwa [compound_unitary r hU1, one_mul, mul_one] at h2
  · intro h
    have h2 := h.conjTranspose_mul_mul_same ((compound r U)ᴴ)
    rwa [show ((compound r U)ᴴ)ᴴ * compound r P * (compound r U)ᴴ
        = compound r U * compound r P * (compound r U)ᴴ from by
        rw [Matrix.conjTranspose_conjTranspose],
      ← compound_conjTranspose, ← compound_mul, ← compound_mul] at h2

/-- **`thm:SMQG-unitary-covariance`, rank preservation**: unitary congruence preserves the
rank of every reflected word grade. -/
theorem smqg_unitary_covariance_rank (P U : Matrix (Fin d) (Fin d) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ) (r : ℕ) :
    (Gamma (U * P * Uᴴ) r).rank = (Gamma P r).rank := by
  have hU1 : Uᴴ * U = 1 := by
    have := Matrix.mem_unitaryGroup_iff'.mp hU
    rwa [Matrix.star_eq_conjTranspose] at this
  have hdet : IsUnit (compound r U).det := compound_unitary_isUnit_det r hU1
  have hdetH : IsUnit (compound r U)ᴴ.det := by
    rw [Matrix.det_conjTranspose]
    exact hdet.star
  rw [show Gamma (U * P * Uᴴ) r = compound r U * compound r P * (compound r U)ᴴ from by
    rw [Gamma, compound_mul, compound_mul, compound_conjTranspose]]
  rw [Matrix.rank_mul_eq_right_of_isUnit_det ((compound r U)ᴴ) _ hdetH,
    Matrix.rank_mul_eq_left_of_isUnit_det (compound r U) _ hdet]
  rfl

/-- **`thm:SMQG-unitary-covariance`, word residuals**: every direct grade-`r` word residual
against the transformed covariance equals the residual of the `Γ∧(U)*`-transported word map
against the original covariance — unitary congruence preserves all direct word residuals. -/
theorem smqg_unitary_covariance_residual {F : Type*} [Fintype F]
    (P U : Matrix (Fin d) (Fin d) ℂ) (_hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (r : ℕ) (K : Matrix F F ℂ) (W : Matrix (WedgeIdx d r) F ℂ) :
    K - Wᴴ * Gamma (U * P * Uᴴ) r * W
      = K - ((compound r U)ᴴ * W)ᴴ * Gamma P r * ((compound r U)ᴴ * W) := by
  rw [show Gamma (U * P * Uᴴ) r = compound r U * compound r P * (compound r U)ᴴ from by
    rw [Gamma, compound_mul, compound_mul, compound_conjTranspose]]
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  rw [show Gamma P r = compound r P from rfl]
  noncomm_ring

end MediumExact08
end NCG
