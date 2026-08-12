/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CommonCPCompletion
import NCG.Grand.FiniteNaimarkDilation
import NCG.Grand.PredictiveCPRadonNikodymEnvelope
import NCG.Grand.CanonicalPrefixPurificationUniqueness

/-!
# Common finite CP completion

This file completes `thm:common-CP-completion`. It combines four exact finite
constructions: controlled direct sums of Julia completions, the Choi
Radon--Nikodym effects in one minimal Stinespring environment, their common
finite Naimark dilation, and path-labelled finite-word dilations. The final
source-cyclic compatibility clause is the unique range unitary for equal
Stinespring Grams.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace NCG

set_option linter.unusedDecidableInType false

/-- A matrix family placed on the diagonal blocks selected by a finite
classical control register. -/
def finiteControlledMatrix {ι r c : Type*} [DecidableEq ι]
    (U : ι → Matrix r c ℂ) : Matrix (ι × r) (ι × c) ℂ :=
  fun ir jc => if ir.1 = jc.1 then U ir.1 ir.2 jc.2 else 0

/-- A finite controlled family of two-sided unitaries is again a two-sided
unitary (rectangular coordinate types of equal finite dimension are allowed). -/
theorem finiteControlledMatrix_unitary {ι r c : Type*}
    [Fintype ι] [Fintype r] [Fintype c]
    [DecidableEq ι] [DecidableEq r] [DecidableEq c]
    (U : ι → Matrix r c ℂ)
    (hrow : ∀ i, U i * (U i)ᴴ = 1)
    (hcol : ∀ i, (U i)ᴴ * U i = 1) :
    finiteControlledMatrix U * (finiteControlledMatrix U)ᴴ = 1
      ∧ (finiteControlledMatrix U)ᴴ * finiteControlledMatrix U = 1 := by
  constructor
  · ext ⟨i, x⟩ ⟨j, y⟩
    by_cases hij : i = j
    · subst j
      simpa [finiteControlledMatrix, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Fintype.sum_prod_type,
        Matrix.one_apply] using congrArg (fun M : Matrix r r ℂ => M x y)
          (hrow i)
    · simp [finiteControlledMatrix, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Fintype.sum_prod_type,
        Matrix.one_apply, hij, Ne.symm hij]
  · ext ⟨i, x⟩ ⟨j, y⟩
    by_cases hij : i = j
    · subst j
      simpa [finiteControlledMatrix, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Fintype.sum_prod_type,
        Matrix.one_apply] using congrArg (fun M : Matrix c c ℂ => M x y)
          (hcol i)
    · simp [finiteControlledMatrix, Matrix.mul_apply,
        Matrix.conjTranspose_apply, Fintype.sum_prod_type,
        Matrix.one_apply, hij, Ne.symm hij]

/-- The Julia matrix attached to a Stinespring contraction. -/
noncomputable def juliaCompletion {h k : Type*} [Fintype h] [Fintype k]
    [DecidableEq h] [DecidableEq k] (V : Matrix k h ℂ) :
    Matrix (k ⊕ h) (h ⊕ k) ℂ :=
  Matrix.fromBlocks V (CFC.sqrt (1 - V * Vᴴ))
    (CFC.sqrt (1 - Vᴴ * V)) (-Vᴴ)

/-- Every finite family of contractions has one simultaneous, finitely
controlled Julia-unitary completion. -/
theorem finiteFamily_simultaneousJuliaCompletion
    {ι h k : Type*} [Fintype ι] [Fintype h] [Fintype k]
    [DecidableEq ι] [DecidableEq h] [DecidableEq k]
    (V : ι → Matrix k h ℂ)
    (hA : ∀ i, ((1 : Matrix h h ℂ) - (V i)ᴴ * V i).PosSemidef)
    (hB : ∀ i, ((1 : Matrix k k ℂ) - V i * (V i)ᴴ).PosSemidef) :
    finiteControlledMatrix (fun i => juliaCompletion (V i)) *
        (finiteControlledMatrix (fun i => juliaCompletion (V i)))ᴴ = 1
      ∧ (finiteControlledMatrix (fun i => juliaCompletion (V i)))ᴴ *
          finiteControlledMatrix (fun i => juliaCompletion (V i)) = 1 := by
  apply finiteControlledMatrix_unitary
  · intro i
    exact (common_cp_completion (V i) (hA i) (hB i)).2.1
  · intro i
    exact (common_cp_completion (V i) (hA i) (hB i)).2.2.1

/-- The canonical common Stinespring--Naimark dilation of a finite Choi
decomposition. All branches first become effects in the same minimal
environment, and then become orthogonal projections in `ι × E`. -/
theorem finiteChoiDecomposition_commonNaimark
    {ι K E H : Type*} [Fintype ι] [Fintype K] [Fintype E]
    [Fintype H] [DecidableEq ι] [DecidableEq K] [DecidableEq E]
    [DecidableEq H]
    (V : Matrix (K × E) H ℂ) (hmin : FiniteStinespringMinimal V)
    (C : ι → StinespringCPOrderInterval V)
    (hsum : ∑ i, (C i).1 =
      (stinespringKrausMatrix V)ᴴ * stinespringKrausMatrix V) :
    let F := fun i => (dominatedChoiDerivative V hmin (C i)).1
    let L := finiteNaimarkIsometry F
    (Lᴴ * L = 1)
      ∧ (∀ i : ι, (finiteNaimarkProjection (E := E) i).PosSemidef)
      ∧ (∀ i : ι, finiteNaimarkProjection (E := E) i *
          finiteNaimarkProjection (E := E) i =
            finiteNaimarkProjection (E := E) i)
      ∧ (∀ i j : ι, i ≠ j → finiteNaimarkProjection (E := E) i *
          finiteNaimarkProjection (E := E) j = 0)
      ∧ (∑ i : ι, finiteNaimarkProjection (E := E) i = 1)
      ∧ (∀ i : ι, Lᴴ * finiteNaimarkProjection (E := E) i * L = F i)
      ∧ (∀ i : ι, (stinespringKrausMatrix V)ᴴ *
          (Lᴴ * finiteNaimarkProjection (E := E) i * L) *
            stinespringKrausMatrix V = (C i).1) := by
  classical
  dsimp only
  have hF : ∀ i, ((dominatedChoiDerivative V hmin (C i)).1).PosSemidef :=
    fun i => (dominatedChoiDerivative V hmin (C i)).2.1
  have hFsum : ∑ i, (dominatedChoiDerivative V hmin (C i)).1 = 1 :=
    (environmentPOVM_iff_dominatedChoiDecomposition V hmin Finset.univ C).2
      (by simpa using hsum)
  obtain ⟨hL, hpos, hidem, hortho, hPsum, hcompress⟩ :=
    finiteNaimarkDilation
      (fun i => (dominatedChoiDerivative V hmin (C i)).1) hF hFsum
  refine ⟨hL, hpos, hidem, hortho, hPsum, hcompress, ?_⟩
  intro i
  rw [hcompress i]
  exact dominatedChoiDerivative_representation V hmin (C i)

/-- Unitary accumulated along a finite word of primitive labels. -/
def wordUnitary {α d : Type*} [Fintype d] [DecidableEq d]
    (U : α → Matrix d d ℂ) : List α → Matrix d d ℂ
  | [] => 1
  | a :: w => U a * wordUnitary U w

/-- Products along words preserve two-sided unitarity. -/
theorem wordUnitary_unitary {α d : Type*} [Fintype d] [DecidableEq d]
    (U : α → Matrix d d ℂ)
    (hU : ∀ a, U a * (U a)ᴴ = 1 ∧ (U a)ᴴ * U a = 1) :
    ∀ w, wordUnitary U w * (wordUnitary U w)ᴴ = 1
      ∧ (wordUnitary U w)ᴴ * wordUnitary U w = 1 := by
  intro w
  induction w with
  | nil => simp [wordUnitary]
  | cons a w ih =>
      constructor
      · rw [wordUnitary, Matrix.conjTranspose_mul]
        calc
          U a * wordUnitary U w * ((wordUnitary U w)ᴴ * (U a)ᴴ) =
              U a * (wordUnitary U w * (wordUnitary U w)ᴴ) *
                (U a)ᴴ := by simp only [Matrix.mul_assoc]
          _ = 1 := by rw [ih.1, Matrix.mul_one, (hU a).1]
      · rw [wordUnitary, Matrix.conjTranspose_mul]
        calc
          (wordUnitary U w)ᴴ * (U a)ᴴ * (U a * wordUnitary U w) =
              (wordUnitary U w)ᴴ * ((U a)ᴴ * U a) *
                wordUnitary U w := by simp only [Matrix.mul_assoc]
          _ = 1 := by rw [(hU a).2, Matrix.mul_one, ih.2]

/-- The path-labelled direct sum for a finite family of words. -/
def finiteWordDilation {α d : Type*} [Fintype d] [DecidableEq α]
    [DecidableEq d]
    (U : α → Matrix d d ℂ) (s : Finset (List α)) :
    Matrix (s × d) (s × d) ℂ :=
  finiteControlledMatrix fun w : s => wordUnitary U w.1

/-- Every finite word family has a path-labelled unitary dilation. -/
theorem finiteWordDilation_unitary
    {α d : Type*} [Fintype d] [DecidableEq α] [DecidableEq d]
    (U : α → Matrix d d ℂ)
    (hU : ∀ a, U a * (U a)ᴴ = 1 ∧ (U a)ᴴ * U a = 1)
    (s : Finset (List α)) :
    finiteWordDilation U s * (finiteWordDilation U s)ᴴ = 1
      ∧ (finiteWordDilation U s)ᴴ * finiteWordDilation U s = 1 := by
  apply finiteControlledMatrix_unitary
  · intro w
    exact (wordUnitary_unitary U hU w.1).1
  · intro w
    exact (wordUnitary_unitary U hU w.1).2

/-- Increasing a finite word family leaves every old path block unchanged;
this is the explicit compatibility of the path-labelled dilations. -/
theorem finiteWordDilation_compatible
    {α d : Type*} [Fintype d] [DecidableEq α] [DecidableEq d]
    (U : α → Matrix d d ℂ) {s t : Finset (List α)} (hst : s ⊆ t)
    (w v : List α) (hw : w ∈ s) (hv : v ∈ s) (x y : d) :
    finiteWordDilation U s (⟨w, hw⟩, x) (⟨v, hv⟩, y) =
      finiteWordDilation U t (⟨w, hst hw⟩, x) (⟨v, hst hv⟩, y) := by
  by_cases h : w = v
  · subst v
    simp [finiteWordDilation, finiteControlledMatrix]
  · simp [finiteWordDilation, finiteControlledMatrix, h]

/-- Full exact finite-word compatibility package, including the unique
source-cyclic compression supplied by minimal Stinespring uniqueness. -/
theorem finiteWordPathDilations_with_uniqueCompression
    {α d : Type*} [Fintype d] [DecidableEq α] [DecidableEq d]
    (U : α → Matrix d d ℂ)
    (hU : ∀ a, U a * (U a)ᴴ = 1 ∧ (U a)ᴴ * U a = 1) :
    (∀ s : Finset (List α),
      finiteWordDilation U s * (finiteWordDilation U s)ᴴ = 1
        ∧ (finiteWordDilation U s)ᴴ * finiteWordDilation U s = 1)
      ∧ (∀ {s t : Finset (List α)} (hst : s ⊆ t),
        ∀ (w v : List α) (hw : w ∈ s) (hv : v ∈ s) (x y : d),
          finiteWordDilation U s (⟨w, hw⟩, x) (⟨v, hv⟩, y) =
            finiteWordDilation U t (⟨w, hst hw⟩, x)
              (⟨v, hst hv⟩, y))
      ∧ (∀ {e h h' : Type*} [Fintype e] [Fintype h] [Fintype h']
          (S : Matrix h e ℂ) (T : Matrix h' e ℂ), Sᴴ * S = Tᴴ * T →
          ∃! Q : LinearMap.range S.mulVecLin ≃ₗ[ℂ]
              LinearMap.range T.mulVecLin,
            (∀ z : e → ℂ,
              Q (S.mulVecLin.rangeRestrict z) = T.mulVecLin.rangeRestrict z)
            ∧ (∀ x y : LinearMap.range S.mulVecLin,
              star (x : h → ℂ) ⬝ᵥ (y : h → ℂ) =
                star (Q x : h' → ℂ) ⬝ᵥ (Q y : h' → ℂ))) := by
  refine ⟨fun s => finiteWordDilation_unitary U hU s, ?_, ?_⟩
  · intro s t hst w v hw hv x y
    exact finiteWordDilation_compatible U hst w v hw hv x y
  · intro e h h' _ _ _ S T hGram
    exact supportMinimalPrefixMemories_unique S T hGram

end NCG
