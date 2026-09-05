/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteChoiRadonNikodym

/-!
# Predictive completely positive Radon--Nikodym envelope

This file proves `thm:RN-envelope` in the finite Choi model.  The reshuffled
Stinespring matrix is the minimal Kraus factor.  Positive contractions on the
environment are identified, affinely and order-isomorphically, with the Choi
matrices of completely positive maps dominated by the Stinespring channel.
The inverse is the explicit finite Radon--Nikodym derivative constructed in
`FiniteChoiRadonNikodym`; finite POVMs are identified with finite dominated CP
decompositions whose sum is the channel.
-/

open Matrix Finset
open scoped ComplexOrder

namespace NCG

section ChoiCoordinates

variable {K E H : Type*} [Fintype K] [Fintype E] [Fintype H]
  [DecidableEq K] [DecidableEq E] [DecidableEq H]

/-- Reshuffle a Stinespring isometry into its minimal Kraus/Choi factor. -/
def stinespringKrausMatrix (V : Matrix (K × E) H ℂ) :
    Matrix E (K × H) ℂ :=
  fun e kh => V (kh.1, e) kh.2

/-- The Choi matrix of a finite matrix-valued linear operation, defined on
the matrix-unit basis. -/
def finiteMapChoi
    (Ψ : Matrix K K ℂ → Matrix H H ℂ) : Matrix (K × H) (K × H) ℂ :=
  fun kh lh => Ψ (Matrix.single kh.1 lh.1 1) kh.2 lh.2

/-- Reconstruct the finite matrix operation represented by a Choi matrix. -/
def choiMatrixAction (C : Matrix (K × H) (K × H) ℂ)
    (X : Matrix K K ℂ) : Matrix H H ℂ :=
  fun h h' => ∑ k, ∑ l, X k l * C (k, h) (l, h')

/-- Choi reconstruction is exact on every finite Choi matrix. -/
@[simp] theorem finiteMapChoi_choiMatrixAction
    (C : Matrix (K × H) (K × H) ℂ) :
    finiteMapChoi (choiMatrixAction C) = C := by
  classical
  ext ⟨k, h⟩ ⟨l, h'⟩
  simp only [finiteMapChoi, choiMatrixAction, Matrix.single_apply,
    ite_and, ite_mul, one_mul, zero_mul, Finset.sum_ite_irrel,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const_zero]

/-- The Choi matrix of `Θ_V(F)` is the Kraus Gram `Wᴴ F W`. -/
theorem finiteMapChoi_thetaV
    (V : Matrix (K × E) H ℂ) (F : Matrix E E ℂ) :
    finiteMapChoi (thetaV V F) =
      (stinespringKrausMatrix V)ᴴ * F * stinespringKrausMatrix V := by
  classical
  ext ⟨k, h⟩ ⟨l, h'⟩
  simp only [finiteMapChoi, thetaV, stinespringKrausMatrix,
    Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.kroneckerMap_apply, Matrix.single_apply]
  simp_rw [Fintype.sum_prod_type]
  simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_ite_eq,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_ite, ite_mul,
    mul_zero, zero_mul, one_mul, Finset.sum_const_zero]

/-- Minimality in finite Kraus coordinates: the reshuffled Kraus matrix has
full row rank.  This is the standard finite Kraus-coordinate rendering of
cyclic minimality for the Stinespring representation. -/
def FiniteStinespringMinimal (V : Matrix (K × E) H ℂ) : Prop :=
  Function.Surjective (stinespringKrausMatrix V).mulVec

/-- Positive contractions on the Stinespring environment. -/
def PositiveEnvironmentContraction :=
  {F : Matrix E E ℂ //
    F.PosSemidef ∧ ((1 : Matrix E E ℂ) - F).PosSemidef}

/-- Choi matrices in the completely positive order interval below the
Stinespring channel. -/
def StinespringCPOrderInterval (V : Matrix (K × E) H ℂ) :=
  {C : Matrix (K × H) (K × H) ℂ //
    C.PosSemidef ∧
      ((stinespringKrausMatrix V)ᴴ * stinespringKrausMatrix V - C).PosSemidef}

/-- The forward Radon--Nikodym coordinate map on Choi matrices. -/
def environmentContractionToChoi
    (V : Matrix (K × E) H ℂ) :
    PositiveEnvironmentContraction (E := E) →
      StinespringCPOrderInterval V :=
  fun F => ⟨(stinespringKrausMatrix V)ᴴ * F.1 * stinespringKrausMatrix V,
    F.2.1.conjTranspose_mul_mul_same _, by
      have h := F.2.2.conjTranspose_mul_mul_same
        (stinespringKrausMatrix V)
      simpa [Matrix.mul_sub, Matrix.sub_mul] using h⟩

/-- The unique derivative selected by the finite Choi Radon--Nikodym theorem. -/
noncomputable def dominatedChoiDerivative
    (V : Matrix (K × E) H ℂ) (hmin : FiniteStinespringMinimal V)
    (C : StinespringCPOrderInterval V) :
    PositiveEnvironmentContraction (E := E) := by
  let W := stinespringKrausMatrix V
  let hex := dominatedGram_radonNikodym W hmin C.1 C.2.1 C.2.2
  exact ⟨Classical.choose hex, (Classical.choose_spec hex).1.1,
    (Classical.choose_spec hex).1.2.1⟩

theorem dominatedChoiDerivative_representation
    (V : Matrix (K × E) H ℂ) (hmin : FiniteStinespringMinimal V)
    (C : StinespringCPOrderInterval V) :
    (stinespringKrausMatrix V)ᴴ *
        (dominatedChoiDerivative V hmin C).1 * stinespringKrausMatrix V = C.1 := by
  classical
  let W := stinespringKrausMatrix V
  let hex := dominatedGram_radonNikodym W hmin C.1 C.2.1 C.2.2
  change Wᴴ * (dominatedChoiDerivative V hmin C).1 * W = C.1
  change Wᴴ * Classical.choose hex * W = C.1
  exact (Classical.choose_spec hex).1.2.2

/-- The affine Radon--Nikodym bijection between environment effects and the
dominated completely positive Choi interval. -/
noncomputable def predictiveCPRadonNikodymEquiv
    (V : Matrix (K × E) H ℂ) (hmin : FiniteStinespringMinimal V) :
    PositiveEnvironmentContraction (E := E) ≃
      StinespringCPOrderInterval V where
  toFun := environmentContractionToChoi V
  invFun := dominatedChoiDerivative V hmin
  left_inv F := by
    apply Subtype.ext
    apply fullRowRank_gramCoordinate_injective
      (stinespringKrausMatrix V) hmin
    exact dominatedChoiDerivative_representation V hmin
      (environmentContractionToChoi V F)
  right_inv C := by
    apply Subtype.ext
    exact dominatedChoiDerivative_representation V hmin C

@[simp] theorem predictiveCPRadonNikodymEquiv_apply
    (V : Matrix (K × E) H ℂ) (hmin : FiniteStinespringMinimal V)
    (F : PositiveEnvironmentContraction (E := E)) :
    (predictiveCPRadonNikodymEquiv V hmin F).1 =
      (stinespringKrausMatrix V)ᴴ * F.1 * stinespringKrausMatrix V := rfl

/-- The bijection preserves and reflects the positive-semidefinite difference
order, hence is an order isomorphism. -/
theorem predictiveCPRadonNikodym_order_iff
    (V : Matrix (K × E) H ℂ) (hmin : FiniteStinespringMinimal V)
    (F G : PositiveEnvironmentContraction (E := E)) :
    (G.1 - F.1).PosSemidef ↔
      ((predictiveCPRadonNikodymEquiv V hmin G).1 -
        (predictiveCPRadonNikodymEquiv V hmin F).1).PosSemidef := by
  exact fullRowRank_gramCoordinate_order_iff
    (stinespringKrausMatrix V) hmin F.1 G.1

/-- Additivity of the ambient Choi coordinate map. -/
theorem stinespringChoiCoordinate_add
    (V : Matrix (K × E) H ℂ) (F G : Matrix E E ℂ) :
    (stinespringKrausMatrix V)ᴴ * (F + G) * stinespringKrausMatrix V =
      (stinespringKrausMatrix V)ᴴ * F * stinespringKrausMatrix V +
        (stinespringKrausMatrix V)ᴴ * G * stinespringKrausMatrix V := by
  rw [Matrix.mul_add, Matrix.add_mul]

/-- Homogeneity of the ambient Choi coordinate map. -/
theorem stinespringChoiCoordinate_smul
    (V : Matrix (K × E) H ℂ) (c : ℂ) (F : Matrix E E ℂ) :
    (stinespringKrausMatrix V)ᴴ * (c • F) * stinespringKrausMatrix V =
      c • ((stinespringKrausMatrix V)ᴴ * F * stinespringKrausMatrix V) := by
  rw [Matrix.mul_smul, Matrix.smul_mul]

/-- Finite POVMs correspond exactly to finite decompositions of the channel
inside the dominated CP interval. -/
theorem environmentPOVM_iff_dominatedChoiDecomposition
    (V : Matrix (K × E) H ℂ) (hmin : FiniteStinespringMinimal V)
    {ι : Type*} (s : Finset ι)
    (C : ι → StinespringCPOrderInterval V) :
    (∑ i ∈ s, (dominatedChoiDerivative V hmin (C i)).1) = 1 ↔
      (∑ i ∈ s, (C i).1) =
        (stinespringKrausMatrix V)ᴴ * stinespringKrausMatrix V := by
  classical
  let W := stinespringKrausMatrix V
  have hcoord : Wᴴ *
      (∑ i ∈ s, (dominatedChoiDerivative V hmin (C i)).1) * W =
      ∑ i ∈ s, (C i).1 := by
    simp only [Matrix.mul_sum, Matrix.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    exact dominatedChoiDerivative_representation V hmin (C i)
  constructor
  · intro hsum
    rw [hsum] at hcoord
    change (∑ i ∈ s, (C i).1) = Wᴴ * W
    calc
      (∑ i ∈ s, (C i).1) = Wᴴ * 1 * W := hcoord.symm
      _ = Wᴴ * W := by rw [Matrix.mul_one]
  · intro hsum
    apply fullRowRank_gramCoordinate_injective W hmin
    calc
      Wᴴ * (∑ i ∈ s,
          (dominatedChoiDerivative V hmin (C i)).1) * W =
          ∑ i ∈ s, (C i).1 := hcoord
      _ = Wᴴ * W := by
        change (∑ i ∈ s, (C i).1) =
          (stinespringKrausMatrix V)ᴴ * stinespringKrausMatrix V
        exact hsum
      _ = Wᴴ * (1 : Matrix E E ℂ) * W := by rw [Matrix.mul_one]

/-- Full finite statement of the predictive CP Radon--Nikodym envelope:
bijectivity, order equivalence, affinity, and the POVM/decomposition clause. -/
theorem predictiveCPRadonNikodymEnvelope
    (V : Matrix (K × E) H ℂ) (hmin : FiniteStinespringMinimal V) :
    Function.Bijective (environmentContractionToChoi V)
    ∧ (∀ F G : PositiveEnvironmentContraction (E := E),
        (G.1 - F.1).PosSemidef ↔
          ((environmentContractionToChoi V G).1 -
            (environmentContractionToChoi V F).1).PosSemidef)
    ∧ (∀ F G : Matrix E E ℂ,
        (stinespringKrausMatrix V)ᴴ * (F + G) * stinespringKrausMatrix V =
          (stinespringKrausMatrix V)ᴴ * F * stinespringKrausMatrix V +
          (stinespringKrausMatrix V)ᴴ * G * stinespringKrausMatrix V)
    ∧ (∀ (c : ℂ) (F : Matrix E E ℂ),
        (stinespringKrausMatrix V)ᴴ * (c • F) * stinespringKrausMatrix V =
          c • ((stinespringKrausMatrix V)ᴴ * F * stinespringKrausMatrix V)) := by
  refine ⟨(predictiveCPRadonNikodymEquiv V hmin).bijective, ?_,
    stinespringChoiCoordinate_add V, stinespringChoiCoordinate_smul V⟩
  intro F G
  exact predictiveCPRadonNikodym_order_iff V hmin F G

/-- An isometric Stinespring matrix makes the ambient channel unital. -/
theorem thetaV_unital_of_isometry
    (V : Matrix (K × E) H ℂ) (hiso : Vᴴ * V = 1) :
    thetaV V (1 : Matrix E E ℂ) (1 : Matrix K K ℂ) = 1 := by
  rw [thetaV, Matrix.one_kronecker_one, Matrix.mul_one, hiso]

/-- Manuscript form for a finite UCP map: isometric normalization together
with the affine order isomorphism and its explicit inverse. -/
theorem predictiveUCPRadonNikodymEnvelope
    (V : Matrix (K × E) H ℂ) (hiso : Vᴴ * V = 1)
    (hmin : FiniteStinespringMinimal V) :
    thetaV V (1 : Matrix E E ℂ) (1 : Matrix K K ℂ) = 1
      ∧ Function.Bijective (environmentContractionToChoi V)
      ∧ (∀ F G : PositiveEnvironmentContraction (E := E),
          (G.1 - F.1).PosSemidef ↔
            ((environmentContractionToChoi V G).1 -
              (environmentContractionToChoi V F).1).PosSemidef)
      ∧ (∀ F G : Matrix E E ℂ,
          (stinespringKrausMatrix V)ᴴ * (F + G) * stinespringKrausMatrix V =
            (stinespringKrausMatrix V)ᴴ * F * stinespringKrausMatrix V +
            (stinespringKrausMatrix V)ᴴ * G * stinespringKrausMatrix V)
      ∧ (∀ (c : ℂ) (F : Matrix E E ℂ),
          (stinespringKrausMatrix V)ᴴ * (c • F) * stinespringKrausMatrix V =
            c • ((stinespringKrausMatrix V)ᴴ * F *
              stinespringKrausMatrix V)) := by
  exact ⟨thetaV_unital_of_isometry V hiso,
    predictiveCPRadonNikodymEnvelope V hmin⟩

end ChoiCoordinates

end NCG
