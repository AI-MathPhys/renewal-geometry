/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Exact scalar--trace response reconstruction
(`thm:supp-exact-scalar-reconstruction`, `eq:supp-exact-Pi-w`,
`eq:supp-exact-trace-data`, `eq:supp-exact-scalar-v`, `eq:supp-exact-scalar-norm`,
`eq:supp-exact-response-equivalence`; emergent-spacetime manuscript)

Finite-dimensional setting: physical space `n → ℝ`, remaining full-rank source
`F : Matrix n m ℝ` (Gram `Fᵀ F` invertible) with actual target `b`, trace isometry
`E : Matrix n k ℝ` with `Eᵀ E = 1` (the paper's `E τ = τ I/√3`), trace projection
`P_tr = E Eᵀ`, and the DeWitt operator `K₀ = 2(I − 3 P_tr)` with inverse
`K₀⁻¹ = (2I − 3 P_tr)/4` (`dewittK`, `dewittKinv`, `dewittK_mul_dewittKinv`).

Objects of `eq:supp-exact-Pi-w`, `eq:supp-exact-trace-data`:
`Π = F (Fᵀ F)⁻¹ Fᵀ` (`sourceProj`), `w = F (Fᵀ F)⁻¹ b` (`sourceResponse`),
`C = Eᵀ Π E` (`traceCompression`), `H = 2I − 3C` (`traceOp`), `ζ = Eᵀ w`
(`traceSource`), `χ = H⁻¹ ζ` (`traceResponseVec`), signed Gram `Fᵀ K₀⁻¹ F`
(`signedGram`).

* `signedGram_isUnit_iff`: the signed Gram is invertible iff `H` is invertible
  (Sylvester's determinant identity `det(1 − AB) = det(1 − BA)`).
* `response_eq` (**`eq:supp-exact-scalar-v`**): the physical response, characterized
  by `Fᵀ v = b` and `K₀ v ∈ Ran F`, satisfies `E^* v = −χ` and
  `v = w − 3(I − Π) E χ`; `reconstructed_isResponse` shows conversely that this
  vector is a response (existence).
* `dotProduct_reconstructed` (**`eq:supp-exact-scalar-norm`**):
  `‖v‖² = ‖w‖² + 9 ⟨χ, (I − C) χ⟩`.
* `response_tendsto_zero_iff` (**`eq:supp-exact-response-equivalence`**): along any
  family (indexed by a filter, with dimension types depending on the index),
  `v_h → 0 ⟺ w_h → 0 ∧ H_h⁻¹ E^* w_h → 0` (squared Euclidean norms).

Scoped conventions: `H⁻¹` is Mathlib's `Matrix.inv` (nonsingular inverse); the trace
map is any isometry `E` with `Eᵀ E = 1`; invertibility of `H` (regular signed Gram,
by `signedGram_isUnit_iff`) is the hypothesis `hH`.
-/

open Matrix Filter Topology

noncomputable section

namespace RenewalGeometry.ExactScalarReconstruction

variable {n m k : Type*} [Fintype n] [Fintype m] [Fintype k]
  [DecidableEq n] [DecidableEq m] [DecidableEq k]

/-! ### Symmetric idempotents -/

theorem dotProduct_self_nonneg' (x : n → ℝ) : 0 ≤ x ⬝ᵥ x :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)

/-- For a symmetric idempotent `Q`, `‖Q x‖² = ⟨x, Q x⟩`. -/
theorem dotProduct_mulVec_self_of_symm_idem (Q : Matrix n n ℝ) (hQt : Qᵀ = Q)
    (hQQ : Q * Q = Q) (x : n → ℝ) : (Q *ᵥ x) ⬝ᵥ (Q *ᵥ x) = x ⬝ᵥ (Q *ᵥ x) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hQt, mulVec_mulVec, hQQ, dotProduct_comm]

/-- For a symmetric idempotent `Q`, `0 ≤ ⟨x, Q x⟩`. -/
theorem dotProduct_mulVec_nonneg_of_symm_idem (Q : Matrix n n ℝ) (hQt : Qᵀ = Q)
    (hQQ : Q * Q = Q) (x : n → ℝ) : 0 ≤ x ⬝ᵥ (Q *ᵥ x) := by
  rw [← dotProduct_mulVec_self_of_symm_idem Q hQt hQQ]
  exact dotProduct_self_nonneg' _

/-- For a symmetric idempotent `Q`, `⟨x, Q x⟩ ≤ ‖x‖²`. -/
theorem dotProduct_mulVec_le_of_symm_idem (Q : Matrix n n ℝ) (hQt : Qᵀ = Q)
    (hQQ : Q * Q = Q) (x : n → ℝ) : x ⬝ᵥ (Q *ᵥ x) ≤ x ⬝ᵥ x := by
  have h1t : (1 - Q)ᵀ = 1 - Q := by rw [transpose_sub, transpose_one, hQt]
  have h1Q : (1 - Q) * (1 - Q) = 1 - Q := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hQQ]
    abel
  have := dotProduct_mulVec_nonneg_of_symm_idem (1 - Q) h1t h1Q x
  rw [sub_mulVec, one_mulVec, dotProduct_sub] at this
  linarith

/-! ### The DeWitt operator and its inverse -/

/-- The trace projection `P_tr = E Eᵀ`. -/
def traceProj (E : Matrix n k ℝ) : Matrix n n ℝ := E * Eᵀ

/-- The DeWitt operator `K₀ = 2 (I − 3 P_tr)`. -/
def dewittK (E : Matrix n k ℝ) : Matrix n n ℝ := (2 : ℝ) • (1 - (3 : ℝ) • traceProj E)

/-- The inverse DeWitt operator `K₀⁻¹ = (2 I − 3 P_tr)/4`. -/
def dewittKinv (E : Matrix n k ℝ) : Matrix n n ℝ :=
  (1 / 4 : ℝ) • ((2 : ℝ) • 1 - (3 : ℝ) • traceProj E)

theorem traceProj_transpose (E : Matrix n k ℝ) : (traceProj E)ᵀ = traceProj E := by
  unfold traceProj
  rw [transpose_mul, transpose_transpose]

theorem traceProj_mul_traceProj (E : Matrix n k ℝ) (hE : Eᵀ * E = 1) :
    traceProj E * traceProj E = traceProj E := by
  unfold traceProj
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc Eᵀ, hE, Matrix.one_mul]

theorem dewittK_mul_dewittKinv (E : Matrix n k ℝ) (hE : Eᵀ * E = 1) :
    dewittK E * dewittKinv E = 1 := by
  have hPP := traceProj_mul_traceProj E hE
  have hexp : (1 - (3 : ℝ) • traceProj E) * ((2 : ℝ) • 1 - (3 : ℝ) • traceProj E)
      = (2 : ℝ) • (1 : Matrix n n ℝ) := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_sub, Matrix.mul_smul,
      Matrix.mul_smul, Matrix.mul_one, hPP]
    module
  unfold dewittK dewittKinv
  rw [Matrix.smul_mul, Matrix.mul_smul, hexp, smul_smul, smul_smul]
  norm_num

/-! ### Source projection and scalar--trace data -/

/-- The source projection `Π = F (Fᵀ F)⁻¹ Fᵀ`. -/
def sourceProj (F : Matrix n m ℝ) : Matrix n n ℝ := F * (Fᵀ * F)⁻¹ * Fᵀ

/-- The projected response `w = F (Fᵀ F)⁻¹ b`. -/
def sourceResponse (F : Matrix n m ℝ) (b : m → ℝ) : n → ℝ := F *ᵥ ((Fᵀ * F)⁻¹ *ᵥ b)

/-- The trace compression `C = Eᵀ Π E`. -/
def traceCompression (F : Matrix n m ℝ) (E : Matrix n k ℝ) : Matrix k k ℝ :=
  Eᵀ * sourceProj F * E

/-- The trace operator `H = 2I − 3C`. -/
def traceOp (F : Matrix n m ℝ) (E : Matrix n k ℝ) : Matrix k k ℝ :=
  (2 : ℝ) • 1 - (3 : ℝ) • traceCompression F E

/-- The trace source `ζ = Eᵀ w`. -/
def traceSource (F : Matrix n m ℝ) (E : Matrix n k ℝ) (b : m → ℝ) : k → ℝ :=
  Eᵀ *ᵥ sourceResponse F b

/-- The trace response `χ = H⁻¹ ζ`. -/
def traceResponseVec (F : Matrix n m ℝ) (E : Matrix n k ℝ) (b : m → ℝ) : k → ℝ :=
  (traceOp F E)⁻¹ *ᵥ traceSource F E b

/-- The signed Gram `Fᵀ K₀⁻¹ F`. -/
def signedGram (F : Matrix n m ℝ) (E : Matrix n k ℝ) : Matrix m m ℝ :=
  Fᵀ * dewittKinv E * F

/-- The reconstructed response `w − 3 (I − Π) E χ`. -/
def reconstructed (F : Matrix n m ℝ) (E : Matrix n k ℝ) (b : m → ℝ) : n → ℝ :=
  sourceResponse F b
    - (3 : ℝ) • ((1 - sourceProj F) *ᵥ (E *ᵥ traceResponseVec F E b))

/-- A vector `v` is the physical response when `Fᵀ v = b` and `K₀ v ∈ Ran F`. -/
def IsResponse (F : Matrix n m ℝ) (E : Matrix n k ℝ) (b : m → ℝ) (v : n → ℝ) : Prop :=
  Fᵀ *ᵥ v = b ∧ ∃ μ : m → ℝ, dewittK E *ᵥ v = F *ᵥ μ

section projections

variable (F : Matrix n m ℝ) (hG : IsUnit (Fᵀ * F).det)
include hG

theorem sourceProj_mul_self_right : sourceProj F * F = F := by
  unfold sourceProj
  rw [Matrix.mul_assoc, Matrix.mul_assoc, nonsing_inv_mul _ hG, Matrix.mul_one]

theorem transpose_mul_sourceProj : Fᵀ * sourceProj F = Fᵀ := by
  unfold sourceProj
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv _ hG, Matrix.one_mul]

theorem sourceProj_transpose : (sourceProj F)ᵀ = sourceProj F := by
  unfold sourceProj
  rw [transpose_mul, transpose_mul, transpose_transpose, transpose_nonsing_inv, transpose_mul,
    transpose_transpose, Matrix.mul_assoc]

theorem sourceProj_mul_sourceProj : sourceProj F * sourceProj F = sourceProj F := by
  have h := transpose_mul_sourceProj F hG
  calc sourceProj F * sourceProj F = F * (Fᵀ * F)⁻¹ * (Fᵀ * sourceProj F) := by
        unfold sourceProj
        simp only [Matrix.mul_assoc]
    _ = sourceProj F := by
        rw [h]
        rfl

theorem one_sub_sourceProj_mul : (1 - sourceProj F) * F = 0 := by
  rw [Matrix.sub_mul, Matrix.one_mul, sourceProj_mul_self_right F hG, sub_self]

theorem transpose_mul_one_sub_sourceProj : Fᵀ * (1 - sourceProj F) = 0 := by
  rw [Matrix.mul_sub, Matrix.mul_one, transpose_mul_sourceProj F hG, sub_self]

theorem one_sub_sourceProj_transpose : (1 - sourceProj F)ᵀ = 1 - sourceProj F := by
  rw [transpose_sub, transpose_one, sourceProj_transpose F hG]

theorem one_sub_sourceProj_mul_self : (1 - sourceProj F) * (1 - sourceProj F) = 1 - sourceProj F := by
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
    sourceProj_mul_sourceProj F hG]
  abel

theorem sourceProj_mulVec_of_transpose_mulVec (b : m → ℝ) (v : n → ℝ) (hv : Fᵀ *ᵥ v = b) :
    sourceProj F *ᵥ v = sourceResponse F b := by
  unfold sourceProj sourceResponse
  rw [← mulVec_mulVec, ← mulVec_mulVec, hv]

theorem transpose_mulVec_sourceResponse (b : m → ℝ) : Fᵀ *ᵥ sourceResponse F b = b := by
  unfold sourceResponse
  rw [mulVec_mulVec, mulVec_mulVec, mul_nonsing_inv _ hG, one_mulVec]

theorem sourceProj_mulVec_sourceResponse (b : m → ℝ) :
    sourceProj F *ᵥ sourceResponse F b = sourceResponse F b :=
  sourceProj_mulVec_of_transpose_mulVec F hG b _ (transpose_mulVec_sourceResponse F hG b)

theorem one_sub_sourceProj_mulVec_sourceResponse (b : m → ℝ) :
    (1 - sourceProj F) *ᵥ sourceResponse F b = 0 := by
  rw [sub_mulVec, one_mulVec, sourceProj_mulVec_sourceResponse F hG, sub_self]

end projections

theorem transpose_mul_one_sub_sourceProj_mul (F : Matrix n m ℝ) (E : Matrix n k ℝ)
    (hE : Eᵀ * E = 1) :
    Eᵀ * (1 - sourceProj F) * E = 1 - traceCompression F E := by
  unfold traceCompression
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, hE]

/-! ### Invertibility of the signed Gram -/

theorem signedGram_eq (F : Matrix n m ℝ) (E : Matrix n k ℝ) :
    signedGram F E
      = (1 / 4 : ℝ) • ((2 : ℝ) • (Fᵀ * F) - (3 : ℝ) • ((Fᵀ * E) * (Eᵀ * F))) := by
  unfold signedGram dewittKinv traceProj
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
    Matrix.mul_assoc]

/-- `2·1 − 3 A B = 2 • (1 − ((3/2) • A) B)`. -/
theorem two_sub_three_mul_eq {p q : Type*} [Fintype p] [Fintype q] [DecidableEq p]
    (A : Matrix p q ℝ) (B : Matrix q p ℝ) :
    (2 : ℝ) • (1 : Matrix p p ℝ) - (3 : ℝ) • (A * B)
      = (2 : ℝ) • (1 - ((3 / 2 : ℝ) • A) * B) := by
  rw [Matrix.smul_mul, smul_sub, smul_smul]
  norm_num

/-- Sylvester: `det(2·1_p − 3 A B)` and `det(2·1_q − 3 B A)` differ by a power of `2`. -/
theorem det_two_sub_three_mul_comm {p q : Type*} [Fintype p] [Fintype q] [DecidableEq p]
    [DecidableEq q] (A : Matrix p q ℝ) (B : Matrix q p ℝ) :
    ((2 : ℝ) • (1 : Matrix p p ℝ) - (3 : ℝ) • (A * B)).det
      = 2 ^ Fintype.card p * (1 / 2 : ℝ) ^ Fintype.card q
        * ((2 : ℝ) • (1 : Matrix q q ℝ) - (3 : ℝ) • (B * A)).det := by
  rw [two_sub_three_mul_eq, det_smul, det_one_sub_mul_comm, Matrix.mul_smul]
  have h : (1 : Matrix q q ℝ) - (3 / 2 : ℝ) • (B * A)
      = (1 / 2 : ℝ) • ((2 : ℝ) • (1 : Matrix q q ℝ) - (3 : ℝ) • (B * A)) := by
    rw [smul_sub, smul_smul, smul_smul]
    norm_num
  rw [h, det_smul]
  ring

/-- `det(Fᵀ K₀⁻¹ F) = (1/4)^m · det(Fᵀ F) · 2^m (1/2)^k · det H`. -/
theorem signedGram_det (F : Matrix n m ℝ) (E : Matrix n k ℝ) (hG : IsUnit (Fᵀ * F).det) :
    (signedGram F E).det
      = (1 / 4 : ℝ) ^ Fintype.card m * (Fᵀ * F).det
        * (2 ^ Fintype.card m * (1 / 2 : ℝ) ^ Fintype.card k) * (traceOp F E).det := by
  have hfac : (2 : ℝ) • (Fᵀ * F) - (3 : ℝ) • ((Fᵀ * E) * (Eᵀ * F))
      = (Fᵀ * F) * ((2 : ℝ) • 1 - (3 : ℝ) • (((Fᵀ * F)⁻¹ * (Fᵀ * E)) * (Eᵀ * F))) := by
    rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one,
      ← Matrix.mul_assoc (Fᵀ * F) ((Fᵀ * F)⁻¹ * (Fᵀ * E)) (Eᵀ * F),
      ← Matrix.mul_assoc (Fᵀ * F) (Fᵀ * F)⁻¹ (Fᵀ * E), mul_nonsing_inv _ hG, Matrix.one_mul]
  have hBA : (Eᵀ * F) * ((Fᵀ * F)⁻¹ * (Fᵀ * E)) = traceCompression F E := by
    unfold traceCompression sourceProj
    simp only [Matrix.mul_assoc]
  rw [signedGram_eq, det_smul, hfac, det_mul, det_two_sub_three_mul_comm, hBA]
  unfold traceOp
  ring

/-- The signed Gram `Fᵀ K₀⁻¹ F` is invertible iff `H = 2I − 3C` is invertible. -/
theorem signedGram_isUnit_iff (F : Matrix n m ℝ) (E : Matrix n k ℝ)
    (hG : IsUnit (Fᵀ * F).det) :
    IsUnit (signedGram F E).det ↔ IsUnit (traceOp F E).det := by
  rw [isUnit_iff_ne_zero, isUnit_iff_ne_zero, signedGram_det F E hG]
  have h1 : (1 / 4 : ℝ) ^ Fintype.card m ≠ 0 := pow_ne_zero _ (by norm_num)
  have h2 : (Fᵀ * F).det ≠ 0 := isUnit_iff_ne_zero.mp hG
  have h3 : (2 : ℝ) ^ Fintype.card m * (1 / 2 : ℝ) ^ Fintype.card k ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (by norm_num))
  constructor
  · intro h hH
    exact h (by rw [hH, mul_zero])
  · intro hH h
    exact hH ((mul_eq_zero.mp h).resolve_left (mul_ne_zero (mul_ne_zero h1 h2) h3))

/-! ### Identification of the physical response -/

/-- `K₀ v = 2 (v − 3 E (Eᵀ v))`. -/
theorem dewittK_mulVec (E : Matrix n k ℝ) (v : n → ℝ) :
    dewittK E *ᵥ v = (2 : ℝ) • (v - (3 : ℝ) • (E *ᵥ (Eᵀ *ᵥ v))) := by
  unfold dewittK traceProj
  rw [smul_mulVec, sub_mulVec, one_mulVec, smul_mulVec, ← mulVec_mulVec]

/-- The trace coordinate of any response is `−χ`: `E^* v = −χ`. -/
theorem transpose_mulVec_response (F : Matrix n m ℝ) (E : Matrix n k ℝ) (b : m → ℝ)
    (hG : IsUnit (Fᵀ * F).det) (hE : Eᵀ * E = 1) (hH : IsUnit (traceOp F E).det)
    (v : n → ℝ) (hv : IsResponse F E b v) :
    Eᵀ *ᵥ v = -traceResponseVec F E b := by
  obtain ⟨hFv, μ, hKv⟩ := hv
  -- `(1 − Π) K₀ v = 0`
  have h0 : (1 - sourceProj F) *ᵥ (dewittK E *ᵥ v) = 0 := by
    rw [hKv, mulVec_mulVec, one_sub_sourceProj_mul F hG, zero_mulVec]
  rw [dewittK_mulVec, mulVec_smul, mulVec_sub, mulVec_smul, smul_eq_zero] at h0
  have h1 : (1 - sourceProj F) *ᵥ v
      = (3 : ℝ) • ((1 - sourceProj F) *ᵥ (E *ᵥ (Eᵀ *ᵥ v))) := by
    have := h0.resolve_left (by norm_num)
    exact sub_eq_zero.mp this
  -- split `v = Π v + (1 − Π) v`
  have hsplit : v = sourceProj F *ᵥ v + (1 - sourceProj F) *ᵥ v := by
    rw [sub_mulVec, one_mulVec]; abel
  have hPv := sourceProj_mulVec_of_transpose_mulVec F hG b v hFv
  -- apply `Eᵀ`
  have hy : Eᵀ *ᵥ v = traceSource F E b
      + (3 : ℝ) • ((1 - traceCompression F E) *ᵥ (Eᵀ *ᵥ v)) := by
    calc Eᵀ *ᵥ v = Eᵀ *ᵥ (sourceProj F *ᵥ v + (1 - sourceProj F) *ᵥ v) := by rw [← hsplit]
      _ = traceSource F E b + (3 : ℝ) • ((1 - traceCompression F E) *ᵥ (Eᵀ *ᵥ v)) := by
        rw [mulVec_add, hPv, h1, mulVec_smul, mulVec_mulVec, mulVec_mulVec,
          transpose_mul_one_sub_sourceProj_mul F E hE]
        rfl
  have hHy : traceOp F E *ᵥ (Eᵀ *ᵥ v) = -traceSource F E b := by
    unfold traceOp
    rw [sub_mulVec, smul_mulVec, one_mulVec, smul_mulVec]
    rw [sub_mulVec, one_mulVec] at hy
    linear_combination (norm := module) (-1 : ℝ) • hy
  unfold traceResponseVec
  rw [← mulVec_neg, ← hHy, mulVec_mulVec, nonsing_inv_mul _ hH, one_mulVec]

/-- **`eq:supp-exact-scalar-v`**: the physical response is `v = w − 3(I − Π)Eχ` with
`E^* v = −χ`. -/
theorem response_eq (F : Matrix n m ℝ) (E : Matrix n k ℝ) (b : m → ℝ)
    (hG : IsUnit (Fᵀ * F).det) (hE : Eᵀ * E = 1) (hH : IsUnit (traceOp F E).det)
    (v : n → ℝ) (hv : IsResponse F E b v) :
    Eᵀ *ᵥ v = -traceResponseVec F E b ∧ v = reconstructed F E b := by
  have hEv := transpose_mulVec_response F E b hG hE hH v hv
  refine ⟨hEv, ?_⟩
  obtain ⟨hFv, μ, hKv⟩ := hv
  have h0 : (1 - sourceProj F) *ᵥ (dewittK E *ᵥ v) = 0 := by
    rw [hKv, mulVec_mulVec, one_sub_sourceProj_mul F hG, zero_mulVec]
  rw [dewittK_mulVec, mulVec_smul, mulVec_sub, mulVec_smul, smul_eq_zero] at h0
  have h1 : (1 - sourceProj F) *ᵥ v
      = (3 : ℝ) • ((1 - sourceProj F) *ᵥ (E *ᵥ (Eᵀ *ᵥ v))) := by
    have := h0.resolve_left (by norm_num)
    exact sub_eq_zero.mp this
  have hsplit : v = sourceProj F *ᵥ v + (1 - sourceProj F) *ᵥ v := by
    rw [sub_mulVec, one_mulVec]; abel
  have hPv := sourceProj_mulVec_of_transpose_mulVec F hG b v hFv
  unfold reconstructed
  calc v = sourceProj F *ᵥ v + (1 - sourceProj F) *ᵥ v := hsplit
    _ = sourceResponse F b
        - (3 : ℝ) • ((1 - sourceProj F) *ᵥ (E *ᵥ traceResponseVec F E b)) := by
      rw [hPv, h1, hEv, mulVec_neg, mulVec_neg]
      module

/-- Existence: the reconstructed vector is a response (`Fᵀ v = b`, `K₀ v ∈ Ran F`). -/
theorem reconstructed_isResponse (F : Matrix n m ℝ) (E : Matrix n k ℝ) (b : m → ℝ)
    (hG : IsUnit (Fᵀ * F).det) (hE : Eᵀ * E = 1) (hH : IsUnit (traceOp F E).det) :
    IsResponse F E b (reconstructed F E b) := by
  have hFt : Fᵀ *ᵥ reconstructed F E b = b := by
    unfold reconstructed
    rw [mulVec_sub, transpose_mulVec_sourceResponse F hG, mulVec_smul, mulVec_mulVec,
      transpose_mul_one_sub_sourceProj F hG, zero_mulVec, smul_zero, sub_zero]
  refine ⟨hFt, (Fᵀ * F)⁻¹ *ᵥ (Fᵀ *ᵥ (dewittK E *ᵥ reconstructed F E b)), ?_⟩
  -- it suffices that `(1 − Π) K₀ v = 0`
  have hEv : Eᵀ *ᵥ reconstructed F E b = -traceResponseVec F E b := by
    unfold reconstructed
    rw [mulVec_sub, mulVec_smul, mulVec_mulVec, mulVec_mulVec,
      transpose_mul_one_sub_sourceProj_mul F E hE]
    have hHχ : traceOp F E *ᵥ traceResponseVec F E b = traceSource F E b := by
      unfold traceResponseVec
      rw [mulVec_mulVec, mul_nonsing_inv _ hH, one_mulVec]
    unfold traceOp traceSource at hHχ
    rw [sub_mulVec, smul_mulVec, one_mulVec, smul_mulVec] at hHχ
    rw [sub_mulVec, one_mulVec]
    linear_combination (norm := module) (-1 : ℝ) • hHχ
  have h0 : (1 - sourceProj F) *ᵥ (dewittK E *ᵥ reconstructed F E b) = 0 := by
    rw [dewittK_mulVec, hEv, mulVec_smul, mulVec_sub, mulVec_smul, mulVec_neg, mulVec_neg]
    unfold reconstructed
    rw [mulVec_sub, one_sub_sourceProj_mulVec_sourceResponse F hG, mulVec_smul, mulVec_mulVec,
      one_sub_sourceProj_mul_self F hG]
    module
  rw [mulVec_mulVec, mulVec_mulVec]
  have : dewittK E *ᵥ reconstructed F E b
      = sourceProj F *ᵥ (dewittK E *ᵥ reconstructed F E b) := by
    rw [sub_mulVec, one_mulVec, sub_eq_zero] at h0
    exact h0
  exact this

/-! ### The norm identity -/

/-- **`eq:supp-exact-scalar-norm`**: `‖v‖² = ‖w‖² + 9 ⟨χ, (I − C) χ⟩` for
`v = w − 3(I − Π)Eχ`. -/
theorem dotProduct_reconstructed (F : Matrix n m ℝ) (E : Matrix n k ℝ) (b : m → ℝ)
    (hG : IsUnit (Fᵀ * F).det) (hE : Eᵀ * E = 1) :
    reconstructed F E b ⬝ᵥ reconstructed F E b
      = sourceResponse F b ⬝ᵥ sourceResponse F b
        + 9 * (traceResponseVec F E b ⬝ᵥ ((1 - traceCompression F E) *ᵥ traceResponseVec F E b)) := by
  obtain ⟨w, hw⟩ : ∃ w, w = sourceResponse F b := ⟨_, rfl⟩
  obtain ⟨χ, hχ⟩ : ∃ χ, χ = traceResponseVec F E b := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ : ∃ u, u = (1 - sourceProj F) *ᵥ (E *ᵥ χ) := ⟨_, rfl⟩
  have hrec : reconstructed F E b = w - (3 : ℝ) • u := by
    rw [hu, hχ, hw]
    rfl
  have hwu : w ⬝ᵥ u = 0 := by
    rw [hu, hw, dotProduct_mulVec, ← mulVec_transpose, one_sub_sourceProj_transpose F hG,
      one_sub_sourceProj_mulVec_sourceResponse F hG, zero_dotProduct]
  have huu : u ⬝ᵥ u = χ ⬝ᵥ ((1 - traceCompression F E) *ᵥ χ) := by
    rw [hu, dotProduct_mulVec_self_of_symm_idem _ (one_sub_sourceProj_transpose F hG)
      (one_sub_sourceProj_mul_self F hG), dotProduct_mulVec, ← mulVec_transpose,
      one_sub_sourceProj_transpose F hG, mulVec_mulVec, dotProduct_comm, dotProduct_mulVec,
      ← mulVec_transpose, mulVec_mulVec, transpose_mul, one_sub_sourceProj_transpose F hG,
      transpose_mul_one_sub_sourceProj_mul F E hE, dotProduct_comm]
  rw [hrec, ← hw, ← hχ, sub_dotProduct, dotProduct_sub, dotProduct_sub, smul_dotProduct,
    dotProduct_smul, smul_dotProduct, dotProduct_smul, dotProduct_comm u w, hwu, huu]
  simp only [smul_eq_mul]
  ring

/-! ### Response equivalence along a family -/

/-- Pointwise comparison: for any response `v`, `‖w‖² ≤ ‖v‖²`, `‖χ‖² ≤ ‖v‖²` and
`‖v‖² ≤ ‖w‖² + 9 ‖χ‖²`. -/
theorem response_norm_bounds (F : Matrix n m ℝ) (E : Matrix n k ℝ) (b : m → ℝ)
    (hG : IsUnit (Fᵀ * F).det) (hE : Eᵀ * E = 1) (hH : IsUnit (traceOp F E).det)
    (v : n → ℝ) (hv : IsResponse F E b v) :
    sourceResponse F b ⬝ᵥ sourceResponse F b ≤ v ⬝ᵥ v
      ∧ traceResponseVec F E b ⬝ᵥ traceResponseVec F E b ≤ v ⬝ᵥ v
      ∧ v ⬝ᵥ v ≤ sourceResponse F b ⬝ᵥ sourceResponse F b
          + 9 * (traceResponseVec F E b ⬝ᵥ traceResponseVec F E b) := by
  obtain ⟨hEv, hveq⟩ := response_eq F E b hG hE hH v hv
  have hPv := sourceProj_mulVec_of_transpose_mulVec F hG b v hv.1
  refine ⟨?_, ?_, ?_⟩
  · rw [← hPv, dotProduct_mulVec_self_of_symm_idem _ (sourceProj_transpose F hG)
      (sourceProj_mul_sourceProj F hG)]
    exact dotProduct_mulVec_le_of_symm_idem _ (sourceProj_transpose F hG)
      (sourceProj_mul_sourceProj F hG) v
  · have hχ : traceResponseVec F E b ⬝ᵥ traceResponseVec F E b = (Eᵀ *ᵥ v) ⬝ᵥ (Eᵀ *ᵥ v) := by
      rw [hEv, neg_dotProduct, dotProduct_neg, neg_neg]
    rw [hχ, dotProduct_mulVec, vecMul_transpose, mulVec_mulVec, dotProduct_comm]
    exact dotProduct_mulVec_le_of_symm_idem _ (traceProj_transpose E)
      (traceProj_mul_traceProj E hE) v
  · rw [hveq, dotProduct_reconstructed F E b hG hE]
    have hC : 0 ≤ traceResponseVec F E b ⬝ᵥ (traceCompression F E *ᵥ traceResponseVec F E b) := by
      unfold traceCompression
      rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose,
        transpose_transpose]
      exact dotProduct_mulVec_nonneg_of_symm_idem _ (sourceProj_transpose F hG)
        (sourceProj_mul_sourceProj F hG) _
    rw [sub_mulVec, one_mulVec, dotProduct_sub]
    linarith

/-- Real squeeze: if `0 ≤ b ≤ a`, `0 ≤ c ≤ a` and `a ≤ b + 9c`, then
`a → 0 ↔ b → 0 ∧ c → 0`. -/
theorem tendsto_zero_iff_of_bounds {ι : Type*} (l : Filter ι) (a b c : ι → ℝ)
    (hb0 : ∀ i, 0 ≤ b i) (hc0 : ∀ i, 0 ≤ c i) (ha0 : ∀ i, 0 ≤ a i)
    (hba : ∀ i, b i ≤ a i) (hca : ∀ i, c i ≤ a i) (habc : ∀ i, a i ≤ b i + 9 * c i) :
    Tendsto a l (𝓝 0) ↔ Tendsto b l (𝓝 0) ∧ Tendsto c l (𝓝 0) := by
  constructor
  · intro ha
    exact ⟨squeeze_zero hb0 hba ha, squeeze_zero hc0 hca ha⟩
  · rintro ⟨hb, hc⟩
    have : Tendsto (fun i => b i + 9 * c i) l (𝓝 0) := by
      simpa using hb.add (hc.const_mul 9)
    exact squeeze_zero ha0 habc this

/-- **`eq:supp-exact-response-equivalence`**: along any family (the dimension types may
depend on the index), `v_h → 0 ⟺ w_h → 0 ∧ H_h⁻¹ E^* w_h → 0`, in squared Euclidean
norm. -/
theorem response_tendsto_zero_iff {ι : Type*} (l : Filter ι)
    {n m k : ι → Type*} [∀ i, Fintype (n i)] [∀ i, Fintype (m i)] [∀ i, Fintype (k i)]
    [∀ i, DecidableEq (n i)] [∀ i, DecidableEq (m i)] [∀ i, DecidableEq (k i)]
    (F : ∀ i, Matrix (n i) (m i) ℝ) (E : ∀ i, Matrix (n i) (k i) ℝ) (b : ∀ i, m i → ℝ)
    (hG : ∀ i, IsUnit ((F i)ᵀ * F i).det) (hE : ∀ i, (E i)ᵀ * E i = 1)
    (hH : ∀ i, IsUnit (traceOp (F i) (E i)).det)
    (v : ∀ i, n i → ℝ) (hv : ∀ i, IsResponse (F i) (E i) (b i) (v i)) :
    Tendsto (fun i => v i ⬝ᵥ v i) l (𝓝 0)
      ↔ Tendsto (fun i => sourceResponse (F i) (b i) ⬝ᵥ sourceResponse (F i) (b i)) l (𝓝 0)
        ∧ Tendsto (fun i => traceResponseVec (F i) (E i) (b i)
            ⬝ᵥ traceResponseVec (F i) (E i) (b i)) l (𝓝 0) := by
  refine tendsto_zero_iff_of_bounds l _ _ _ (fun i => dotProduct_self_nonneg' _)
    (fun i => dotProduct_self_nonneg' _) (fun i => dotProduct_self_nonneg' _)
    (fun i => (response_norm_bounds (F i) (E i) (b i) (hG i) (hE i) (hH i) (v i) (hv i)).1)
    (fun i => (response_norm_bounds (F i) (E i) (b i) (hG i) (hE i) (hH i) (v i) (hv i)).2.1)
    (fun i => (response_norm_bounds (F i) (E i) (b i) (hG i) (hE i) (hH i) (v i) (hv i)).2.2)

end RenewalGeometry.ExactScalarReconstruction

end
