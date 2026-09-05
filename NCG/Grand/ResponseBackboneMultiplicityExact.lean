/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GTResponseBackbone
import Mathlib.LinearAlgebra.Lagrange

/-!
# Exact spectral multiplicity formula for response backbones

This module completes `thm:GT-response-backbone`.  It defines the minimum
cyclic response-bank width, proves the eigenspace-projection lower bound for
that minimum, constructs a bank with exactly the largest multiplicity by
Lagrange interpolation across distinct eigenvalues, and transports the result
from grouped spectral normal form to every finite Hermitian matrix.
-/

open Matrix

namespace NCG.ResponseBackbone

variable {Λ k : Type} [Fintype Λ] [DecidableEq Λ]
  [Nonempty Λ] [Fintype k] [DecidableEq k]
  (M : Λ → Type) [∀ l, Fintype (M l)] [∀ l, DecidableEq (M l)]

abbrev Carrier := Σ l, M l

def spectralDiagonal (lam : Λ → ℂ) :
    Matrix (Carrier M) (Carrier M) ℂ :=
  Matrix.diagonal fun x => lam x.1

def spectralBank (e : ∀ l, M l ↪ k) :
    Matrix (Carrier M) k ℂ :=
  fun x a => if e x.1 x.2 = a then 1 else 0

theorem spectralBank_mulVec (e : ∀ l, M l ↪ k) (c : k → ℂ)
    (x : Carrier M) :
    spectralBank M e *ᵥ c x = c (e x.1 x.2) := by
  classical
  rw [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single (e x.1 x.2)]
  · simp [spectralBank]
  · intro a _ ha
    simp [spectralBank, Ne.symm ha]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem spectralDiagonal_pow_mulVec (lam : Λ → ℂ) (i : ℕ)
    (w : Carrier M → ℂ) (x : Carrier M) :
    (spectralDiagonal M lam ^ i) *ᵥ w x = lam x.1 ^ i * w x := by
  classical
  rw [spectralDiagonal, Matrix.diagonal_pow, Matrix.diagonal_mulVec]
  rfl

theorem spectralBank_responseComplete
    (lam : Λ → ℂ) (hlam : Function.Injective lam)
    (e : ∀ l, M l ↪ k) :
    ∀ v : Carrier M → ℂ, ∃ (N : ℕ) (c : ℕ → k → ℂ),
      v = ∑ i ∈ Finset.range N,
        (spectralDiagonal M lam ^ i) *ᵥ
          (spectralBank M e *ᵥ c i) := by
  classical
  intro v
  let value : k → Λ → ℂ := fun a l =>
    if h : ∃ m : M l, e l m = a then v ⟨l, Classical.choose h⟩ else 0
  let p : k → ℂ[X] := fun a =>
    Lagrange.interpolate Finset.univ lam (value a)
  refine ⟨Fintype.card Λ, fun i a => (p a).coeff i, ?_⟩
  funext x
  rw [Finset.sum_apply]
  simp_rw [spectralDiagonal_pow_mulVec, spectralBank_mulVec]
  have hvalue : value (e x.1 x.2) x.1 = v x := by
    simp only [value, dif_pos ⟨x.2, rfl⟩]
    congr 1
    apply Sigma.ext rfl
    exact (e x.1).injective (Classical.choose_spec
      (show ∃ m : M x.1, e x.1 m = e x.1 x.2 from ⟨x.2, rfl⟩))
  have heval : (p (e x.1 x.2)).eval (lam x.1) =
      value (e x.1 x.2) x.1 := by
    exact Lagrange.eval_interpolate_at_node _
      (hlam.injOn) (Finset.mem_univ x.1)
  have hdegree : (p (e x.1 x.2)).natDegree < Fintype.card Λ := by
    by_cases hp : p (e x.1 x.2) = 0
    · rw [hp, Polynomial.natDegree_zero]
      exact Fintype.card_pos
    · exact (Polynomial.natDegree_lt_iff_degree_lt hp).2
        (Lagrange.degree_interpolate_lt _ hlam.injOn)
  rw [← hvalue, ← heval,
    Polynomial.eval_eq_sum_range' hdegree]
  apply Finset.sum_congr rfl
  intro i hi
  ring

def maximumMultiplicity : ℕ :=
  Finset.univ.sup fun l : Λ => Fintype.card (M l)

theorem card_le_maximumMultiplicity (l : Λ) :
    Fintype.card (M l) ≤ maximumMultiplicity M := by
  exact Finset.le_sup (s := Finset.univ) (f := fun l : Λ => Fintype.card (M l))
    (Finset.mem_univ l)

noncomputable def maximumMultiplicityEmbedding (l : Λ) :
    M l ↪ Fin (maximumMultiplicity M) :=
  (Fintype.equivFin (M l)).toEmbedding.trans
    ⟨fun i => ⟨i, i.isLt.trans_le (card_le_maximumMultiplicity M l)⟩,
      fun _ _ h => Fin.ext_iff.mp h⟩

/-- A bank whose number of columns is the largest spectral multiplicity is
cyclic for the diagonal spectral normal form. -/
theorem maximumMultiplicityBank_responseComplete
    (lam : Λ → ℂ) (hlam : Function.Injective lam) :
    ∀ v : Carrier M → ℂ, ∃ (N : ℕ)
      (c : ℕ → Fin (maximumMultiplicity M) → ℂ),
      v = ∑ i ∈ Finset.range N,
        (spectralDiagonal M lam ^ i) *ᵥ
          (spectralBank M (maximumMultiplicityEmbedding M) *ᵥ c i) :=
  spectralBank_responseComplete M lam hlam (maximumMultiplicityEmbedding M)

def IsResponseComplete {n r : Type} [Fintype n] [Fintype r]
    (T : Matrix n n ℂ) (J : Matrix n r ℂ) : Prop :=
  ∀ v : n → ℂ, ∃ (N : ℕ) (c : ℕ → r → ℂ),
    v = ∑ i ∈ Finset.range N, (T ^ i) *ᵥ (J *ᵥ c i)

def ResponseBankExists {n : Type} [Fintype n] (T : Matrix n n ℂ)
    (r : ℕ) : Prop :=
  ∃ J : Matrix n (Fin r) ℂ, IsResponseComplete T J

noncomputable def coordinateBank (n : Type) [Fintype n] :
    Matrix n (Fin (Fintype.card n)) ℂ :=
  fun i k => if Fintype.equivFin n i = k then 1 else 0

theorem coordinateBank_mulVec {n : Type} [Fintype n]
    (c : Fin (Fintype.card n) → ℂ) (i : n) :
    coordinateBank n *ᵥ c i = c (Fintype.equivFin n i) := by
  classical
  rw [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single (Fintype.equivFin n i)]
  · simp [coordinateBank]
  · intro a _ ha
    simp [coordinateBank, Ne.symm ha]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem responseBankExists_card {n : Type} [Fintype n]
    (T : Matrix n n ℂ) : ResponseBankExists T (Fintype.card n) := by
  classical
  refine ⟨coordinateBank n, ?_⟩
  intro v
  refine ⟨1, fun _ k => v ((Fintype.equivFin n).symm k), ?_⟩
  funext i
  simp [coordinateBank_mulVec]

noncomputable def responseBackboneDimension {n : Type} [Fintype n]
    (T : Matrix n n ℂ) : ℕ :=
  Nat.find ⟨Fintype.card n, responseBankExists_card T⟩

theorem responseBankExists_responseBackboneDimension
    {n : Type} [Fintype n] (T : Matrix n n ℂ) :
    ResponseBankExists T (responseBackboneDimension T) :=
  Nat.find_spec ⟨Fintype.card n, responseBankExists_card T⟩

theorem responseBackboneDimension_minimal
    {n : Type} [Fintype n] (T : Matrix n n ℂ) {r : ℕ}
    (hr : ResponseBankExists T r) : responseBackboneDimension T ≤ r :=
  Nat.find_min' ⟨Fintype.card n, responseBankExists_card T⟩ hr

def spectralProjection (l : Λ) :
    Matrix (Carrier M) (Carrier M) ℂ :=
  Matrix.diagonal fun x => if x.1 = l then 1 else 0

theorem spectralProjection_mul_spectralDiagonal (lam : Λ → ℂ) (l : Λ) :
    spectralProjection M l * spectralDiagonal M lam =
      lam l • spectralProjection M l := by
  classical
  ext x y
  by_cases hxy : x = y
  · subst y
    by_cases hxl : x.1 = l
    · subst l
      simp [spectralProjection, spectralDiagonal, Matrix.diagonal_mul]
    · simp [spectralProjection, spectralDiagonal, Matrix.diagonal_mul, hxl]
  · simp [spectralProjection, spectralDiagonal, Matrix.diagonal_mul, hxy]

noncomputable def spectralProjectionSupportEquiv (l : Λ) :
    {x : Carrier M // (if x.1 = l then (1 : ℂ) else 0) ≠ 0} ≃ M l where
  toFun x := by
    have hx : x.1.1 = l := by
      by_contra h
      exact x.2 (if_neg h)
    exact hx ▸ x.1.2
  invFun m := ⟨⟨l, m⟩, by simp⟩
  left_inv x := by
    apply Subtype.ext
    apply Sigma.ext
    · have hx : x.1.1 = l := by
        by_contra h
        exact x.2 (if_neg h)
      exact hx.symm
    · simp
  right_inv m := by simp

theorem spectralProjection_rank (l : Λ) :
    (spectralProjection M l).rank = Fintype.card (M l) := by
  classical
  rw [spectralProjection, Matrix.rank_diagonal]
  exact Fintype.card_congr (spectralProjectionSupportEquiv M l)

theorem responseBank_width_ge_multiplicity
    (lam : Λ → ℂ) {r : ℕ}
    (hr : ResponseBankExists (spectralDiagonal M lam) r) (l : Λ) :
    Fintype.card (M l) ≤ r := by
  obtain ⟨J, hJ⟩ := hr
  have h := NCG.gt_response_backbone (spectralDiagonal M lam)
    (spectralProjection M l) (lam l) J
    (spectralProjection_mul_spectralDiagonal M lam l) hJ
  simpa [spectralProjection_rank] using h

theorem maximumMultiplicity_le_responseBackboneDimension (lam : Λ → ℂ) :
    maximumMultiplicity M ≤ responseBackboneDimension (spectralDiagonal M lam) := by
  apply Finset.sup_le
  intro l hl
  exact responseBank_width_ge_multiplicity M lam
    (responseBankExists_responseBackboneDimension _) l

theorem responseBackboneDimension_le_maximumMultiplicity
    (lam : Λ → ℂ) (hlam : Function.Injective lam) :
    responseBackboneDimension (spectralDiagonal M lam) ≤ maximumMultiplicity M := by
  apply responseBackboneDimension_minimal
  exact ⟨spectralBank M (maximumMultiplicityEmbedding M),
    maximumMultiplicityBank_responseComplete M lam hlam⟩

/-- Exact SA.8 equality on finite spectral normal form. -/
theorem responseBackboneDimension_spectralDiagonal
    (lam : Λ → ℂ) (hlam : Function.Injective lam) :
    responseBackboneDimension (spectralDiagonal M lam) = maximumMultiplicity M :=
  le_antisymm (responseBackboneDimension_le_maximumMultiplicity M lam hlam)
    (maximumMultiplicity_le_responseBackboneDimension M lam)

section UnitaryTransport

variable {n m : Type} [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

theorem isResponseComplete_unitary_transport
    (D : Matrix m m ℂ) (U : Matrix n m ℂ)
    (hleft : Uᴴ * U = 1) (hright : U * Uᴴ = 1)
    {r : Type} [Fintype r] (J : Matrix m r ℂ)
    (hJ : IsResponseComplete D J) :
    IsResponseComplete (U * D * Uᴴ) (U * J) := by
  intro v
  obtain ⟨N, c, hc⟩ := hJ (Uᴴ *ᵥ v)
  refine ⟨N, c, ?_⟩
  have hpow : ∀ i : ℕ, (U * D * Uᴴ) ^ i * U = U * D ^ i := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
        rw [pow_succ, Matrix.mul_assoc, ih]
        calc
          U * D ^ i * (U * D * Uᴴ) =
              U * D ^ i * U * D * Uᴴ := by noncomm_ring
          _ = U * D ^ i * D := by rw [Matrix.mul_assoc Uᴴ U, hleft]; simp
          _ = U * D ^ (i + 1) := by rw [pow_succ]; simp [Matrix.mul_assoc]
  calc
    v = U *ᵥ (Uᴴ *ᵥ v) := by
      rw [Matrix.mulVec_mulVec, hright, Matrix.one_mulVec]
    _ = U *ᵥ ∑ i ∈ Finset.range N,
        (D ^ i) *ᵥ (J *ᵥ c i) := by rw [hc]
    _ = ∑ i ∈ Finset.range N,
        U *ᵥ ((D ^ i) *ᵥ (J *ᵥ c i)) := by rw [Matrix.mulVec_sum]
    _ = ∑ i ∈ Finset.range N,
        ((U * D * Uᴴ) ^ i) *ᵥ ((U * J) *ᵥ c i) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Matrix.mulVec_mulVec]
      rw [← Matrix.mul_assoc, hpow i]
      simp [Matrix.mul_assoc]

theorem responseBankExists_unitary_conjugate_iff
    (D : Matrix m m ℂ) (U : Matrix n m ℂ)
    (hleft : Uᴴ * U = 1) (hright : U * Uᴴ = 1) (r : ℕ) :
    ResponseBankExists (U * D * Uᴴ) r ↔ ResponseBankExists D r := by
  constructor
  · rintro ⟨J, hJ⟩
    refine ⟨Uᴴ * J, ?_⟩
    have hconj : Uᴴ * (U * D * Uᴴ) * U = D := by
      rw [Matrix.mul_assoc Uᴴ U, hleft, Matrix.one_mul,
        Matrix.mul_assoc D Uᴴ U, hleft, Matrix.mul_one]
    have ht := isResponseComplete_unitary_transport
      (U * D * Uᴴ) Uᴴ hright (by simpa using hleft) J hJ
    simpa [hconj, Matrix.mul_assoc, hleft] using ht
  · rintro ⟨J, hJ⟩
    exact ⟨U * J, isResponseComplete_unitary_transport D U hleft hright J hJ⟩

theorem responseBackboneDimension_unitary_conjugate
    (D : Matrix m m ℂ) (U : Matrix n m ℂ)
    (hleft : Uᴴ * U = 1) (hright : U * Uᴴ = 1) :
    responseBackboneDimension (U * D * Uᴴ) = responseBackboneDimension D := by
  apply le_antisymm
  · apply responseBackboneDimension_minimal
    exact (responseBankExists_unitary_conjugate_iff D U hleft hright _).2
      (responseBankExists_responseBackboneDimension D)
  · apply responseBackboneDimension_minimal
    exact (responseBankExists_unitary_conjugate_iff D U hleft hright _).1
      (responseBankExists_responseBackboneDimension (U * D * Uᴴ))

end UnitaryTransport

section GroupedSpectrum

variable {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]

abbrev DistinctValue (e : n → ℂ) :=
  {z : ℂ // z ∈ Finset.image e Finset.univ}

abbrev ValueFiber (e : n → ℂ) (z : DistinctValue e) :=
  {i : n // e i = z.1}

noncomputable def groupingEquiv (e : n → ℂ) :
    (Σ z : DistinctValue e, ValueFiber e z) ≃ n where
  toFun x := x.2.1
  invFun i := ⟨⟨e i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩, ⟨i, rfl⟩⟩
  left_inv x := by
    apply Sigma.ext
    · apply Subtype.ext
      exact x.2.2.symm
    · simp
  right_inv i := rfl

noncomputable def groupingMatrix (e : n → ℂ) :
    Matrix n (Σ z : DistinctValue e, ValueFiber e z) ℂ :=
  (groupingEquiv e).symm.toPEquiv.toMatrix

theorem groupingMatrix_conjTranspose (e : n → ℂ) :
    (groupingMatrix e)ᴴ = (groupingEquiv e).toPEquiv.toMatrix := by
  classical
  ext x i
  simp [groupingMatrix, Matrix.conjTranspose_apply, PEquiv.toMatrix_apply,
    groupingEquiv]

theorem groupingMatrix_conjTranspose_mul (e : n → ℂ) :
    (groupingMatrix e)ᴴ * groupingMatrix e = 1 := by
  classical
  rw [groupingMatrix_conjTranspose]
  ext x y
  simp [groupingMatrix, Matrix.mul_apply, PEquiv.toMatrix_apply]

theorem groupingMatrix_mul_conjTranspose (e : n → ℂ) :
    groupingMatrix e * (groupingMatrix e)ᴴ = 1 := by
  classical
  rw [groupingMatrix_conjTranspose]
  ext i j
  simp [groupingMatrix, Matrix.mul_apply, PEquiv.toMatrix_apply]

theorem groupingMatrix_diagonal_grouping (e : n → ℂ) :
    groupingMatrix e *
        spectralDiagonal (fun z : DistinctValue e => ValueFiber e z)
          (fun z => z.1) *
        (groupingMatrix e)ᴴ = Matrix.diagonal e := by
  classical
  rw [groupingMatrix_conjTranspose]
  ext i j
  simp [groupingMatrix, spectralDiagonal, Matrix.mul_apply,
    PEquiv.toMatrix_apply, groupingEquiv]

end GroupedSpectrum

section HermitianEquality

variable {n : Type} [Fintype n] [DecidableEq n] [Nonempty n]

noncomputable def hermitianMaximumMultiplicity
    {T : Matrix n n ℂ} (hT : T.IsHermitian) : ℕ :=
  let e : n → ℂ := fun i => (hT.eigenvalues i : ℂ)
  maximumMultiplicity (fun z : DistinctValue e => ValueFiber e z)

/-- Exact SA.8 for an arbitrary finite Hermitian response: the minimum
cyclic source-bank width equals the largest eigenspace multiplicity. -/
theorem responseBackboneDimension_hermitian
    (T : Matrix n n ℂ) (hT : T.IsHermitian) :
    responseBackboneDimension T = hermitianMaximumMultiplicity hT := by
  classical
  let e : n → ℂ := fun i => (hT.eigenvalues i : ℂ)
  let M : DistinctValue e → Type := fun z => ValueFiber e z
  let Dg : Matrix (Σ z, M z) (Σ z, M z) ℂ :=
    spectralDiagonal M (fun z => z.1)
  let V : Matrix n (Σ z, M z) ℂ := groupingMatrix e
  let E : Matrix n n ℂ := hT.eigenvectorUnitary
  let U : Matrix n (Σ z, M z) ℂ := E * V
  have hEleft : Eᴴ * E = 1 := by
    simpa [E] using star_mul_coe hT.eigenvectorUnitary
  have hEright : E * Eᴴ = 1 := by
    simpa [E] using coe_mul_star hT.eigenvectorUnitary
  have hUleft : Uᴴ * U = 1 := by
    simp only [U, Matrix.conjTranspose_mul]
    rw [Matrix.mul_assoc Vᴴ Eᴴ E, hEleft, Matrix.mul_one]
    exact groupingMatrix_conjTranspose_mul e
  have hUright : U * Uᴴ = 1 := by
    simp only [U, Matrix.conjTranspose_mul]
    rw [← Matrix.mul_assoc E V Vᴴ, groupingMatrix_mul_conjTranspose e,
      Matrix.mul_one, hEright]
  have hdiag : V * Dg * Vᴴ = Matrix.diagonal e := by
    exact groupingMatrix_diagonal_grouping e
  have hrep : T = U * Dg * Uᴴ := by
    have hspec := hT.spectral_theorem
    change T = E * Matrix.diagonal e * Eᴴ at hspec
    rw [hdiag.symm] at hspec
    calc
      T = E * (V * Dg * Vᴴ) * Eᴴ := hspec
      _ = (E * V) * Dg * (E * V)ᴴ := by
        simp only [Matrix.conjTranspose_mul]
        noncomm_ring
      _ = U * Dg * Uᴴ := rfl
  calc
    responseBackboneDimension T =
        responseBackboneDimension (U * Dg * Uᴴ) := by rw [hrep]
    _ = responseBackboneDimension Dg :=
      responseBackboneDimension_unitary_conjugate Dg U hUleft hUright
    _ = maximumMultiplicity M :=
      responseBackboneDimension_spectralDiagonal M (fun z => z.1)
        Subtype.val_injective
    _ = hermitianMaximumMultiplicity hT := rfl

end HermitianEquality

end NCG.ResponseBackbone
