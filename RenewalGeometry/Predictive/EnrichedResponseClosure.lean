/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
/-!
# Enriched successor-state Gram certificates and forward-response closure

Paper label: `thm:ncg-enriched-closure` (predictive spectral geometry).

Setting (finite matrix algebra).  The ambient memory space is the finite Hilbert space
`m → ℂ` with its standard inner product; for memory operators on `B(H)` with the
Hilbert–Schmidt inner product take `m = H × H` (vectorisation is an HS isometry).

* `L : Matrix m r ℂ` has the reproducible conditional states `ρ_j` as columns
  (`L x = ∑ x_j ρ_j`), `G = Lᴴ L` (`EnrichedResponse.gram`);
* `Φ α : Matrix m m ℂ` are the branch superoperators, `R : Matrix s m ℂ` the retained
  boundary response map;
* `H_α = Lᴴ Φ_α L` (`overlap`), `K_α = (Φ_α L)ᴴ (Φ_α L)` (`successorGram`),
  `B = R L`, `C_α = R Φ_α L`, `B† = Bᴴ (B Bᴴ)⁻¹` (`responsePinv`, the Moore–Penrose inverse
  of a full-row-rank matrix), `A_α = C_α B†`.

Main results.
* `stateProjection` `P = L G⁻¹ Lᴴ` is a Hermitian idempotent fixing `L`
  (`stateProjection_conjTranspose`, `stateProjection_mul_self`, `stateProjection_mul_states`);
* `successorGram_sub_eq`: `K_α − H_αᴴ G⁻¹ H_α = ((1 − P) Φ_α L)ᴴ ((1 − P) Φ_α L)`;
* `successorGram_sub_eq_zero_iff_forwardInvariant`: the Gram defect vanishes iff
  `Ran L` is `Φ_α`-invariant, and then `Φ_α L = L G⁻¹ H_α`;
* `responsePinv_isMoorePenrose`: `B†` satisfies the four Penrose identities;
* `mul_one_sub_pinv_mul_eq_zero_iff`: `C (1 − B† B) = 0 ↔ C = (C B†) B`;
* `enrichedClosure`: **the theorem** — under the two certificates, `Ran L` is forward
  invariant, `R Φ_α X = A_α R X` on `Ran L`, `R Φ_w L = A_w B` for every finite word, and
  `A_α` is the unique factor of `C_α` through `B`.
-/

namespace RenewalGeometry
namespace EnrichedResponse

open Matrix
open scoped ComplexOrder

variable {m r s : Type*} [Fintype m] [Fintype r] [Fintype s]
  [DecidableEq m] [DecidableEq r] [DecidableEq s]

/-- The Gram matrix `G = Lᴴ L` of the reproducible states (`thm:ncg-enriched-closure`). -/
def gram (L : Matrix m r ℂ) : Matrix r r ℂ := Lᴴ * L

/-- The overlap matrix `H_α = Lᴴ Φ_α L` (`thm:ncg-enriched-closure`). -/
def overlap (L : Matrix m r ℂ) (Φ : Matrix m m ℂ) : Matrix r r ℂ := Lᴴ * Φ * L

/-- The successor-state Gram matrix `K_α = (Φ_α L)ᴴ (Φ_α L)` (`thm:ncg-enriched-closure`). -/
def successorGram (L : Matrix m r ℂ) (Φ : Matrix m m ℂ) : Matrix r r ℂ :=
  (Φ * L)ᴴ * (Φ * L)

/-- The orthogonal projection `P_V = L G⁻¹ Lᴴ` onto `V = Ran L`. -/
noncomputable def stateProjection (L : Matrix m r ℂ) : Matrix m m ℂ :=
  L * (gram L)⁻¹ * Lᴴ

/-- The Moore–Penrose inverse `B† = Bᴴ (B Bᴴ)⁻¹` of a full-row-rank response matrix. -/
noncomputable def responsePinv (B : Matrix s r ℂ) : Matrix r s ℂ := Bᴴ * (B * Bᴴ)⁻¹

/-- Linearly independent states have an invertible Gram matrix. -/
theorem isUnit_gram {L : Matrix m r ℂ} (hL : LinearIndependent ℂ L.col) :
    IsUnit (gram L) := by
  rw [← mulVec_injective_iff_isUnit]
  have hinj : Function.Injective L.mulVec := Matrix.mulVec_injective_iff.2 hL
  intro x y hxy
  have h0 : (Lᴴ * L) *ᵥ (x - y) = 0 := by
    rw [mulVec_sub]; exact sub_eq_zero.2 hxy
  rw [conjTranspose_mul_self_mulVec_eq_zero, mulVec_sub, sub_eq_zero] at h0
  exact hinj h0

/-- A matrix with linearly independent rows (full row rank) has invertible `B Bᴴ`. -/
theorem isUnit_mul_conjTranspose {B : Matrix s r ℂ} (hB : LinearIndependent ℂ B.row) :
    IsUnit (B * Bᴴ) := by
  rw [← vecMul_injective_iff_isUnit]
  have hinj : Function.Injective B.vecMul := Matrix.vecMul_injective_iff.2 hB
  intro x y hxy
  have h0 : (x - y) ᵥ* (B * Bᴴ) = 0 := by
    rw [sub_vecMul]; exact sub_eq_zero.2 hxy
  rw [vecMul_self_mul_conjTranspose_eq_zero, sub_vecMul, sub_eq_zero] at h0
  exact hinj h0

theorem gram_conjTranspose (L : Matrix m r ℂ) : (gram L)ᴴ = gram L := by
  simp [gram, conjTranspose_mul]

theorem gram_inv_conjTranspose (L : Matrix m r ℂ) : ((gram L)⁻¹)ᴴ = (gram L)⁻¹ := by
  rw [conjTranspose_nonsing_inv, gram_conjTranspose]

/-- `P_V` is Hermitian. -/
theorem stateProjection_conjTranspose (L : Matrix m r ℂ) :
    (stateProjection L)ᴴ = stateProjection L := by
  simp only [stateProjection, conjTranspose_mul, conjTranspose_conjTranspose,
    gram_inv_conjTranspose, Matrix.mul_assoc]

/-- `P_V L = L`. -/
theorem stateProjection_mul_states {L : Matrix m r ℂ} (hG : IsUnit (gram L)) :
    stateProjection L * L = L := by
  have h := nonsing_inv_mul (gram L) ((isUnit_iff_isUnit_det _).1 hG)
  rw [stateProjection, Matrix.mul_assoc, Matrix.mul_assoc, ← gram, h, Matrix.mul_one]

/-- `P_V` is idempotent. -/
theorem stateProjection_mul_self {L : Matrix m r ℂ} (hG : IsUnit (gram L)) :
    stateProjection L * stateProjection L = stateProjection L := by
  conv_lhs => rw [show stateProjection L * stateProjection L
    = (stateProjection L * L) * ((gram L)⁻¹ * Lᴴ) by
      simp only [stateProjection, Matrix.mul_assoc]]
  rw [stateProjection_mul_states hG, ← Matrix.mul_assoc]; rfl

/-- `(1 − P_V) L = 0`. -/
theorem one_sub_stateProjection_mul_states {L : Matrix m r ℂ} (hG : IsUnit (gram L)) :
    (1 - stateProjection L) * L = 0 := by
  rw [Matrix.sub_mul, Matrix.one_mul, stateProjection_mul_states hG, sub_self]

/-- **Gram-defect identity** (`thm:ncg-enriched-closure`, first display of the proof):
`K_α − H_αᴴ G⁻¹ H_α = ((1 − P_V) Φ_α L)ᴴ ((1 − P_V) Φ_α L)`. -/
theorem successorGram_sub_eq {L : Matrix m r ℂ} (hG : IsUnit (gram L)) (Φ : Matrix m m ℂ) :
    successorGram L Φ - (overlap L Φ)ᴴ * (gram L)⁻¹ * overlap L Φ
      = ((1 - stateProjection L) * Φ * L)ᴴ * ((1 - stateProjection L) * Φ * L) := by
  set P := stateProjection L with hP
  have hPh : Pᴴ = P := stateProjection_conjTranspose L
  have hPP : P * P = P := stateProjection_mul_self hG
  have hQ : (1 - P)ᴴ * (1 - P) = 1 - P := by
    rw [conjTranspose_sub, conjTranspose_one, hPh, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, hPP]
    abel
  have hR : ((1 - P) * Φ * L)ᴴ * ((1 - P) * Φ * L)
      = Lᴴ * Φᴴ * ((1 - P)ᴴ * (1 - P)) * Φ * L := by
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  rw [hR, hQ, successorGram, overlap, hP, stateProjection]
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_one, Matrix.mul_assoc]

/-- The Gram defect is positive semidefinite. -/
theorem successorGram_sub_posSemidef {L : Matrix m r ℂ} (hG : IsUnit (gram L))
    (Φ : Matrix m m ℂ) :
    (successorGram L Φ - (overlap L Φ)ᴴ * (gram L)⁻¹ * overlap L Φ).PosSemidef := by
  rw [successorGram_sub_eq hG]
  exact posSemidef_conjTranspose_mul_self _

/-- The Gram defect vanishes iff `Φ_α L = L G⁻¹ H_α`. -/
theorem successorGram_sub_eq_zero_iff {L : Matrix m r ℂ} (hG : IsUnit (gram L))
    (Φ : Matrix m m ℂ) :
    successorGram L Φ - (overlap L Φ)ᴴ * (gram L)⁻¹ * overlap L Φ = 0 ↔
      Φ * L = L * ((gram L)⁻¹ * overlap L Φ) := by
  rw [successorGram_sub_eq hG, conjTranspose_mul_self_eq_zero]
  have hPΦL : stateProjection L * Φ * L = L * ((gram L)⁻¹ * overlap L Φ) := by
    simp only [stateProjection, overlap, Matrix.mul_assoc]
  rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, hPΦL, sub_eq_zero]

/-- A matrix killing every vector is zero. -/
theorem eq_zero_of_mulVec_eq_zero {p q : Type*} [Fintype q] [DecidableEq q]
    {M : Matrix p q ℂ} (h : ∀ x, M *ᵥ x = 0) : M = 0 := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [mulVec_single_one] using this

/-- **Forward invariance** (`thm:ncg-enriched-closure`): the Gram defect vanishes iff
`V = Ran L` is invariant under `Φ_α`. -/
theorem successorGram_sub_eq_zero_iff_forwardInvariant {L : Matrix m r ℂ}
    (hG : IsUnit (gram L)) (Φ : Matrix m m ℂ) :
    successorGram L Φ - (overlap L Φ)ᴴ * (gram L)⁻¹ * overlap L Φ = 0 ↔
      ∀ x : r → ℂ, ∃ y : r → ℂ, Φ *ᵥ (L *ᵥ x) = L *ᵥ y := by
  rw [successorGram_sub_eq_zero_iff hG]
  constructor
  · intro h x
    refine ⟨((gram L)⁻¹ * overlap L Φ) *ᵥ x, ?_⟩
    rw [mulVec_mulVec, h, ← mulVec_mulVec]
  · intro h
    have h0 : (1 - stateProjection L) * Φ * L = 0 := by
      apply eq_zero_of_mulVec_eq_zero
      intro x
      obtain ⟨y, hy⟩ := h x
      rw [Matrix.mul_assoc, ← mulVec_mulVec, ← mulVec_mulVec, hy, mulVec_mulVec,
        one_sub_stateProjection_mul_states hG, zero_mulVec]
    have hPΦL : stateProjection L * Φ * L = L * ((gram L)⁻¹ * overlap L Φ) := by
      simp only [stateProjection, overlap, Matrix.mul_assoc]
    rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, hPΦL, sub_eq_zero] at h0
    exact h0

/-- `B B† = 1` for a full-row-rank `B`. -/
theorem mul_responsePinv {B : Matrix s r ℂ} (hB : IsUnit (B * Bᴴ)) :
    B * responsePinv B = 1 := by
  rw [responsePinv, ← Matrix.mul_assoc]
  exact mul_nonsing_inv _ ((isUnit_iff_isUnit_det _).1 hB)

/-- `B† = Bᴴ (B Bᴴ)⁻¹` is the Moore–Penrose inverse of a full-row-rank `B`: the four Penrose
identities `B B† B = B`, `B† B B† = B†`, `(B B†)ᴴ = B B†`, `(B† B)ᴴ = B† B` hold. -/
theorem responsePinv_isMoorePenrose {B : Matrix s r ℂ} (hB : IsUnit (B * Bᴴ)) :
    B * responsePinv B * B = B ∧ responsePinv B * B * responsePinv B = responsePinv B ∧
    (B * responsePinv B)ᴴ = B * responsePinv B ∧
    (responsePinv B * B)ᴴ = responsePinv B * B := by
  have h1 := mul_responsePinv hB
  refine ⟨by rw [h1, Matrix.one_mul], by rw [Matrix.mul_assoc, h1, Matrix.mul_one],
    by rw [h1, conjTranspose_one], ?_⟩
  have hh : ((B * Bᴴ)⁻¹)ᴴ = (B * Bᴴ)⁻¹ := by
    rw [conjTranspose_nonsing_inv, conjTranspose_mul, conjTranspose_conjTranspose]
  simp only [responsePinv, conjTranspose_mul, conjTranspose_conjTranspose, hh, Matrix.mul_assoc]

/-- **Response factorization** (`thm:ncg-enriched-closure`): `C (1 − B† B) = 0` iff
`C = (C B†) B`, i.e. iff `C` factors through the response coordinates. -/
theorem mul_one_sub_pinv_mul_eq_zero_iff {p : Type*} [Fintype p] (B : Matrix s r ℂ)
    (C : Matrix p r ℂ) :
    C * (1 - responsePinv B * B) = 0 ↔ C = C * responsePinv B * B := by
  rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero, Matrix.mul_assoc]

/-- The factorization `C = A B` is unique when `B` has full row rank. -/
theorem factor_unique {p : Type*} [Fintype p] {B : Matrix s r ℂ} (hB : IsUnit (B * Bᴴ))
    {A A' : Matrix p s ℂ} (h : A * B = A' * B) : A = A' := by
  have h' := congrArg (· * responsePinv B) h
  simp only [Matrix.mul_assoc, mul_responsePinv hB, Matrix.mul_one] at h'
  exact h'

/-- Intertwining along words: if `X a T = T Y a` for every letter, then the same holds for
the ordered products along every finite word. -/
theorem list_prod_map_mul_of_intertwine {α p q : Type*} [Fintype p] [Fintype q]
    [DecidableEq p] [DecidableEq q] {X : α → Matrix p p ℂ} {Y : α → Matrix q q ℂ}
    {T : Matrix p q ℂ} (h : ∀ a, X a * T = T * Y a) (w : List α) :
    (w.map X).prod * T = T * (w.map Y).prod := by
  induction w with
  | nil => simp
  | cons a w ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, Matrix.mul_assoc, ih,
      ← Matrix.mul_assoc, h, Matrix.mul_assoc]

/-- **Theorem `thm:ncg-enriched-closure`.**  Let the states (columns of `L`) be linearly
independent and let `B = R L` have full row rank.  If for every branch `α` the successor
Gram certificate `K_α − H_αᴴ G⁻¹ H_α = 0` and the response certificate
`C_α (1 − B† B) = 0` hold, then `V = Ran L` is forward invariant under every `Φ_α`, and with
`A_α = C_α B†` one has `R Φ_α X = A_α R X` for `X ∈ V` and `R Φ_w L = A_w B` for every
finite word `w` (ordered products `Φ_w = ∏ Φ_{w_i}`, `A_w = ∏ A_{w_i}` in the same order). -/
theorem enrichedClosure {α : Type*} (L : Matrix m r ℂ) (Φ : α → Matrix m m ℂ)
    (R : Matrix s m ℂ) (hL : LinearIndependent ℂ L.col)
    (hB : LinearIndependent ℂ (R * L).row)
    (hK : ∀ a, successorGram L (Φ a) - (overlap L (Φ a))ᴴ * (gram L)⁻¹ * overlap L (Φ a) = 0)
    (hC : ∀ a, R * Φ a * L * (1 - responsePinv (R * L) * (R * L)) = 0) :
    (∀ a, ∀ x : r → ℂ, ∃ y : r → ℂ, Φ a *ᵥ (L *ᵥ x) = L *ᵥ y) ∧
    (∀ a, ∀ x : r → ℂ, R *ᵥ (Φ a *ᵥ (L *ᵥ x))
        = (R * Φ a * L * responsePinv (R * L)) *ᵥ (R *ᵥ (L *ᵥ x))) ∧
    (∀ w : List α, R * (w.map Φ).prod * L
        = (w.map fun a => R * Φ a * L * responsePinv (R * L)).prod * (R * L)) ∧
    (∀ a, ∀ A' : Matrix s s ℂ, R * Φ a * L = A' * (R * L) →
        A' = R * Φ a * L * responsePinv (R * L)) := by
  have hG := isUnit_gram hL
  set A : α → Matrix s s ℂ := fun a => R * Φ a * L * responsePinv (R * L) with hAdef
  set M : α → Matrix r r ℂ := fun a => (gram L)⁻¹ * overlap L (Φ a) with hMdef
  have hΦL : ∀ a, Φ a * L = L * M a := fun a => (successorGram_sub_eq_zero_iff hG _).1 (hK a)
  have hCA : ∀ a, R * Φ a * L = A a * (R * L) := fun a =>
    (mul_one_sub_pinv_mul_eq_zero_iff _ _).1 (hC a)
  have hAB : ∀ a, A a * (R * L) = (R * L) * M a := by
    intro a
    rw [← hCA, Matrix.mul_assoc, hΦL, ← Matrix.mul_assoc]
  refine ⟨fun a => (successorGram_sub_eq_zero_iff_forwardInvariant hG _).1 (hK a), ?_, ?_,
    ?_⟩
  · intro a x
    simp only [mulVec_mulVec]
    congr 1
    have h := hCA a
    simp only [hAdef, Matrix.mul_assoc] at h ⊢
    exact h
  · intro w
    rw [Matrix.mul_assoc, list_prod_map_mul_of_intertwine hΦL, ← Matrix.mul_assoc,
      list_prod_map_mul_of_intertwine hAB]
  · intro a A' hA'
    exact factor_unique (isUnit_mul_conjTranspose hB) (hA'.symm.trans (hCA a))

/-- Non-vacuity witness for `enrichedClosure`: one state, the identity branch and the
identity response satisfy both certificates. -/
example : successorGram (1 : Matrix (Fin 1) (Fin 1) ℂ) 1
      - (overlap (1 : Matrix (Fin 1) (Fin 1) ℂ) 1)ᴴ * (gram (1 : Matrix (Fin 1) (Fin 1) ℂ))⁻¹
        * overlap (1 : Matrix (Fin 1) (Fin 1) ℂ) 1 = 0 ∧
    (1 : Matrix (Fin 1) (Fin 1) ℂ) * 1 * 1
      * (1 - responsePinv ((1 : Matrix (Fin 1) (Fin 1) ℂ) * 1) * (1 * 1)) = 0 ∧
    LinearIndependent ℂ (1 : Matrix (Fin 1) (Fin 1) ℂ).col ∧
    LinearIndependent ℂ ((1 : Matrix (Fin 1) (Fin 1) ℂ) * 1).row := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [successorGram, overlap, gram]
  · simp [responsePinv]
  · rw [linearIndependent_cols_iff_isUnit]; exact isUnit_one
  · rw [Matrix.mul_one, linearIndependent_rows_iff_isUnit]; exact isUnit_one

end EnrichedResponse
end RenewalGeometry
