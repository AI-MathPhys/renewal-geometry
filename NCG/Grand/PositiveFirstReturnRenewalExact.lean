/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.PositiveOperatorNormBridgeExact

/-!
# Positive first-return renewal on the source-cyclic carrier

Machinery for `thm:GT-positive-first-return-renewal`.  The sampled return kernel
`K = [[A, B], [Bᴴ, D]]` is written relative to a physical source projection (head block `A`)
and its complement (tail block `D`).

* `firstReturn`: the first-return kernels `F₁ = A`, `Fₙ = B D^{n-2} Bᴴ` (ER.12);
* `renewal_recursion` / `renewal_recursion'`: the first-return decomposition
  `Gₙ = ∑_{j=1}^n F_j G_{n-j} = ∑_{j=1}^n G_{n-j} F_j` of the sampled return block `Gₙ = P Kⁿ P`;
* `one_sub_firstReturnSeries_mul` / `mul_one_sub_firstReturnSeries`: the renewal equation
  `𝒢(z) = [I - ℱ(z)]⁻¹` (ER.13) as a two-sided inverse identity of formal power series with
  matrix coefficients;
* `firstReturn_posSemidef`: every `Fₙ` is a positive kernel;
* `one_sub_tail_posDef`: on a source-cyclic carrier (`IsSourceObservable`: no nonzero tail vector
  is invisible to the source along the whole return chronology) the tail block satisfies
  `‖D‖ < 1`, in the form `I - D ≻ 0`;
* `posDef_one_sub_smul_kernel_iff`: (ER.14) for every `r > 0`,
  `I - rK ≻ 0 ⟺ I - rD ≻ 0 ∧ I - ℱ(r) ≻ 0`, the Schur-complement form of
  `‖K‖ < r⁻¹ ⟺ r‖D‖ < 1 ∧ ‖ℱ(r)‖ < 1`.
-/

open Matrix Finset
open scoped ComplexOrder

namespace NCG
namespace FirstReturnRenewal

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The sampled return kernel `K = [[A, B], [Bᴴ, D]]` (ER.11). -/
def kernel (A : Matrix m m ℂ) (B : Matrix m n ℂ) (D : Matrix n n ℂ) :
    Matrix (m ⊕ n) (m ⊕ n) ℂ :=
  fromBlocks A B Bᴴ D

/-- The sampled return block `Gₙ = P Kⁿ P|_{PH}`. -/
def headReturn (A : Matrix m m ℂ) (B : Matrix m n ℂ) (D : Matrix n n ℂ) (k : ℕ) :
    Matrix m m ℂ :=
  (kernel A B D ^ k).toBlocks₁₁

/-- The tail-to-head block of `Kⁿ`. -/
def tailEntry (A : Matrix m m ℂ) (B : Matrix m n ℂ) (D : Matrix n n ℂ) (k : ℕ) :
    Matrix n m ℂ :=
  (kernel A B D ^ k).toBlocks₂₁

/-- The head-to-tail block of `Kⁿ`. -/
def headExit (A : Matrix m m ℂ) (B : Matrix m n ℂ) (D : Matrix n n ℂ) (k : ℕ) :
    Matrix m n ℂ :=
  (kernel A B D ^ k).toBlocks₁₂

/-- The first-return kernels `F₁ = A`, `Fₙ = B D^{n-2} Bᴴ` for `n ≥ 2` (ER.12), with `F₀ = 0`. -/
def firstReturn (A : Matrix m m ℂ) (B : Matrix m n ℂ) (D : Matrix n n ℂ) : ℕ → Matrix m m ℂ
  | 0 => 0
  | 1 => A
  | k + 2 => B * D ^ k * Bᴴ

variable (A : Matrix m m ℂ) (B : Matrix m n ℂ) (D : Matrix n n ℂ)

omit [Fintype m] [DecidableEq m] in
theorem firstReturn_zero : firstReturn A B D 0 = 0 := rfl
omit [Fintype m] [DecidableEq m] in
theorem firstReturn_one : firstReturn A B D 1 = A := rfl
omit [Fintype m] [DecidableEq m] in
theorem firstReturn_add_two (k : ℕ) : firstReturn A B D (k + 2) = B * D ^ k * Bᴴ := rfl

theorem headReturn_zero : headReturn A B D 0 = 1 := by
  rw [headReturn, pow_zero, ← fromBlocks_one, toBlocks_fromBlocks₁₁]

theorem tailEntry_zero : tailEntry A B D 0 = 0 := by
  rw [tailEntry, pow_zero, ← fromBlocks_one, toBlocks_fromBlocks₂₁]

theorem headExit_zero : headExit A B D 0 = 0 := by
  rw [headExit, pow_zero, ← fromBlocks_one, toBlocks_fromBlocks₁₂]

/-- One step of the return chronology, entering from the left. -/
theorem kernel_mul_pow (k : ℕ) :
    kernel A B D * kernel A B D ^ k
      = fromBlocks (A * headReturn A B D k + B * tailEntry A B D k)
          (A * headExit A B D k + B * (kernel A B D ^ k).toBlocks₂₂)
          (Bᴴ * headReturn A B D k + D * tailEntry A B D k)
          (Bᴴ * headExit A B D k + D * (kernel A B D ^ k).toBlocks₂₂) := by
  conv_lhs => rw [← fromBlocks_toBlocks (kernel A B D ^ k)]
  rw [kernel, fromBlocks_multiply]
  rfl

/-- One step of the return chronology, exiting to the right. -/
theorem pow_mul_kernel (k : ℕ) :
    kernel A B D ^ k * kernel A B D
      = fromBlocks (headReturn A B D k * A + headExit A B D k * Bᴴ)
          (headReturn A B D k * B + headExit A B D k * D)
          (tailEntry A B D k * A + (kernel A B D ^ k).toBlocks₂₂ * Bᴴ)
          (tailEntry A B D k * B + (kernel A B D ^ k).toBlocks₂₂ * D) := by
  conv_lhs => rw [← fromBlocks_toBlocks (kernel A B D ^ k)]
  rw [kernel, fromBlocks_multiply]
  rfl

theorem headReturn_succ (k : ℕ) :
    headReturn A B D (k + 1) = A * headReturn A B D k + B * tailEntry A B D k := by
  rw [headReturn, pow_succ', kernel_mul_pow, toBlocks_fromBlocks₁₁]

theorem tailEntry_succ (k : ℕ) :
    tailEntry A B D (k + 1) = Bᴴ * headReturn A B D k + D * tailEntry A B D k := by
  rw [tailEntry, pow_succ', kernel_mul_pow, toBlocks_fromBlocks₂₁]

theorem headReturn_succ' (k : ℕ) :
    headReturn A B D (k + 1) = headReturn A B D k * A + headExit A B D k * Bᴴ := by
  rw [headReturn, pow_succ, pow_mul_kernel, toBlocks_fromBlocks₁₁]

theorem headExit_succ (k : ℕ) :
    headExit A B D (k + 1) = headReturn A B D k * B + headExit A B D k * D := by
  rw [headExit, pow_succ, pow_mul_kernel, toBlocks_fromBlocks₁₂]

/-- The tail entry is the sum of all tail excursions since the last head visit. -/
theorem tailEntry_eq_sum (k : ℕ) :
    tailEntry A B D k = ∑ i ∈ range k, D ^ (k - 1 - i) * Bᴴ * headReturn A B D i := by
  induction k with
  | zero => simp [tailEntry_zero]
  | succ k ih =>
    rw [tailEntry_succ, ih, Matrix.mul_sum, sum_range_succ, add_comm]
    congr 1
    · refine sum_congr rfl fun i hi => ?_
      have hi' : i < k := mem_range.mp hi
      have : k + 1 - 1 - i = (k - 1 - i) + 1 := by omega
      rw [this, pow_succ', ← Matrix.mul_assoc, ← Matrix.mul_assoc]
    · simp

/-- The head exit is the sum of all head-to-tail excursions. -/
theorem headExit_eq_sum (k : ℕ) :
    headExit A B D k = ∑ i ∈ range k, headReturn A B D i * B * D ^ (k - 1 - i) := by
  induction k with
  | zero => simp [headExit_zero]
  | succ k ih =>
    rw [headExit_succ, ih, Matrix.sum_mul, sum_range_succ, add_comm]
    congr 1
    · refine sum_congr rfl fun i hi => ?_
      have hi' : i < k := mem_range.mp hi
      have : k + 1 - 1 - i = (k - 1 - i) + 1 := by omega
      rw [this, pow_succ]
      simp only [Matrix.mul_assoc]
    · simp

/-- **First-return decomposition** (left form): `G_{k+1} = ∑_{j=0}^{k} F_{j+1} G_{k-j}`. -/
theorem renewal_recursion (k : ℕ) :
    headReturn A B D (k + 1)
      = ∑ j ∈ range (k + 1), firstReturn A B D (j + 1) * headReturn A B D (k - j) := by
  rw [headReturn_succ, tailEntry_eq_sum, Matrix.mul_sum, sum_range_succ', firstReturn_one,
    Nat.sub_zero, add_comm]
  congr 1
  rw [← sum_range_reflect]
  refine sum_congr rfl fun i hi => ?_
  have hi' : i < k := mem_range.mp hi
  have h1 : firstReturn A B D (i + 1 + 1) = B * D ^ i * Bᴴ := rfl
  have h2 : k - (i + 1) = k - 1 - i := by omega
  have h3 : k - 1 - (k - 1 - i) = i := by omega
  rw [h1, h2, h3]
  simp only [Matrix.mul_assoc]

/-- **First-return decomposition** (right form): `G_{k+1} = ∑_{j=0}^{k} G_{k-j} F_{j+1}`. -/
theorem renewal_recursion' (k : ℕ) :
    headReturn A B D (k + 1)
      = ∑ j ∈ range (k + 1), headReturn A B D (k - j) * firstReturn A B D (j + 1) := by
  rw [headReturn_succ', headExit_eq_sum, Matrix.sum_mul, sum_range_succ', firstReturn_one,
    Nat.sub_zero, add_comm]
  congr 1
  rw [← sum_range_reflect]
  refine sum_congr rfl fun i hi => ?_
  have hi' : i < k := mem_range.mp hi
  have h1 : firstReturn A B D (i + 1 + 1) = B * D ^ i * Bᴴ := rfl
  have h2 : k - (i + 1) = k - 1 - i := by omega
  have h3 : k - 1 - (k - 1 - i) = i := by omega
  rw [h1, h2, h3]
  simp only [Matrix.mul_assoc]

/-! ### The renewal equation as a formal power-series identity -/

/-- `𝒢(z) = ∑ zⁿ Gₙ`. -/
noncomputable def returnSeries : PowerSeries (Matrix m m ℂ) := PowerSeries.mk (headReturn A B D)

/-- `ℱ(z) = ∑_{n ≥ 1} zⁿ Fₙ`. -/
noncomputable def firstReturnSeries : PowerSeries (Matrix m m ℂ) :=
  PowerSeries.mk (firstReturn A B D)

theorem coeff_firstReturnSeries_mul_returnSeries (k : ℕ) :
    PowerSeries.coeff (k + 1) (firstReturnSeries A B D * returnSeries A B D)
      = headReturn A B D (k + 1) := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, sum_range_succ']
  simp only [firstReturnSeries, returnSeries, PowerSeries.coeff_mk, firstReturn_zero, zero_mul,
    add_zero]
  rw [renewal_recursion]
  refine sum_congr rfl fun j _ => ?_
  congr 2
  omega

theorem coeff_returnSeries_mul_firstReturnSeries (k : ℕ) :
    PowerSeries.coeff (k + 1) (returnSeries A B D * firstReturnSeries A B D)
      = headReturn A B D (k + 1) := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, sum_range_succ]
  simp only [firstReturnSeries, returnSeries, PowerSeries.coeff_mk, Nat.sub_self, firstReturn_zero,
    mul_zero, add_zero]
  rw [renewal_recursion', ← sum_range_reflect]
  refine sum_congr rfl fun j hj => ?_
  have hj' : j < k + 1 := mem_range.mp hj
  congr 2
  omega

/-- **The renewal equation** (ER.13), left inverse: `(I - ℱ(z)) 𝒢(z) = I`. -/
theorem one_sub_firstReturnSeries_mul :
    (1 - firstReturnSeries A B D) * returnSeries A B D = 1 := by
  ext k
  rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_one]
  cases k with
  | zero =>
    simp [returnSeries, firstReturnSeries, PowerSeries.coeff_mul, headReturn_zero, firstReturn_zero]
  | succ k =>
    rw [coeff_firstReturnSeries_mul_returnSeries]
    simp [returnSeries]

/-- **The renewal equation** (ER.13), right inverse: `𝒢(z) (I - ℱ(z)) = I`. -/
theorem mul_one_sub_firstReturnSeries :
    returnSeries A B D * (1 - firstReturnSeries A B D) = 1 := by
  ext k
  rw [mul_sub, mul_one, map_sub, PowerSeries.coeff_one]
  cases k with
  | zero =>
    simp [returnSeries, firstReturnSeries, PowerSeries.coeff_mul, headReturn_zero, firstReturn_zero]
  | succ k =>
    rw [coeff_returnSeries_mul_firstReturnSeries]
    simp [returnSeries]

/-! ### Positivity -/

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
theorem head_posSemidef (hK : (kernel A B D).PosSemidef) : A.PosSemidef := by
  have h := hK.submatrix Sum.inl
  have : (kernel A B D).submatrix Sum.inl Sum.inl = A := by
    ext i j; simp [kernel]
  rwa [this] at h

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
theorem tail_posSemidef (hK : (kernel A B D).PosSemidef) : D.PosSemidef := by
  have h := hK.submatrix Sum.inr
  have : (kernel A B D).submatrix Sum.inr Sum.inr = D := by
    ext i j; simp [kernel]
  rwa [this] at h

set_option linter.unusedFintypeInType false in
omit [DecidableEq m] in
/-- **Every first-return kernel is positive** (ER.12). -/
theorem firstReturn_posSemidef (hK : (kernel A B D).PosSemidef) (k : ℕ) :
    (firstReturn A B D k).PosSemidef := by
  match k with
  | 0 => exact PosSemidef.zero
  | 1 => exact head_posSemidef A B D hK
  | k + 2 => exact ((tail_posSemidef A B D hK).pow k).mul_mul_conjTranspose_same B

/-! ### Source cyclicity and the strict tail contraction -/

/-- **Source cyclicity**, in the observability form: no nonzero tail vector stays invisible to
the source interface along the whole return chronology. -/
def IsSourceObservable (B : Matrix m n ℂ) (D : Matrix n n ℂ) : Prop :=
  ∀ y : n → ℂ, (∀ j : ℕ, B *ᵥ (D ^ j *ᵥ y) = 0) → y = 0

omit [Fintype m] [Fintype n] in
theorem one_sub_kernel :
    1 - kernel A B D = fromBlocks (1 - A) (-B) (-B)ᴴ (1 - D) := by
  rw [kernel, ← fromBlocks_one, sub_eq_add_neg, fromBlocks_neg, fromBlocks_add, conjTranspose_neg]
  congr 1 <;> simp

omit [Fintype m] [Fintype n] in
theorem one_sub_tail_posSemidef (hK1 : (1 - kernel A B D).PosSemidef) : (1 - D).PosSemidef := by
  have h := hK1.submatrix Sum.inr
  have : (1 - kernel A B D).submatrix Sum.inr Sum.inr = 1 - D := by
    rw [one_sub_kernel]
    ext i j; simp
  rwa [this] at h

theorem pow_mulVec_eq_self {y : n → ℂ} (hy : D *ᵥ y = y) (j : ℕ) : D ^ j *ᵥ y = y := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ', ← mulVec_mulVec, ih, hy]

set_option linter.unusedFintypeInType false in
/-- **Strict tail contraction** `‖D‖ < 1` on a source-cyclic carrier, in the form `I - D ≻ 0`:
a unit tail vector with `⟨y, D y⟩ = 1` would be `K`-invariant and source-invisible. -/
theorem one_sub_tail_posDef (hK1 : (1 - kernel A B D).PosSemidef)
    (hobs : IsSourceObservable B D) : (1 - D).PosDef := by
  have h1D := one_sub_tail_posSemidef A B D hK1
  refine PosDef.of_dotProduct_mulVec_pos h1D.1 fun y hy => ?_
  rcases (h1D.dotProduct_mulVec_nonneg y).lt_or_eq with hlt | heq
  · exact hlt
  exfalso
  have hDy : (1 - D) *ᵥ y = 0 := (h1D.dotProduct_mulVec_zero_iff y).mp heq.symm
  have hDy' : D *ᵥ y = y := by
    rw [sub_mulVec, one_mulVec, sub_eq_zero] at hDy
    exact hDy.symm
  -- the lifted vector `0 ⊕ y` has zero form for `1 - K`, hence is fixed by `K`
  have hform : star (Sum.elim (0 : m → ℂ) y) ⬝ᵥ (1 - kernel A B D) *ᵥ Sum.elim 0 y = 0 := by
    rw [one_sub_kernel, fromBlocks_mulVec, Function.star_sumElim, sumElim_dotProduct_sumElim]
    simp [← heq]
  have hKu := (hK1.dotProduct_mulVec_zero_iff _).mp hform
  rw [one_sub_kernel, fromBlocks_mulVec] at hKu
  have hBy : B *ᵥ y = 0 := by
    funext i
    have := congrFun hKu (Sum.inl i)
    simpa [neg_mulVec] using this
  exact hy (hobs y fun j => by rw [pow_mulVec_eq_self D hDy' j, hBy])

/-! ### The Schur-complement form of (ER.14) -/

/-- `ℱ(r) = rA + r² B (I - rD)⁻¹ Bᴴ` for real `r`. -/
noncomputable def schurReturn (r : ℝ) : Matrix m m ℂ :=
  (r : ℂ) • A + ((r : ℂ) ^ 2) • (B * (1 - (r : ℂ) • D)⁻¹ * Bᴴ)

omit [Fintype m] [Fintype n] in
theorem one_sub_smul_kernel (r : ℝ) :
    1 - (r : ℂ) • kernel A B D
      = fromBlocks (1 - (r : ℂ) • A) (-((r : ℂ) • B)) (-((r : ℂ) • B))ᴴ (1 - (r : ℂ) • D) := by
  have hC : (-((r : ℂ) • B))ᴴ = -((r : ℂ) • Bᴴ) := by
    rw [conjTranspose_neg, conjTranspose_smul, Complex.star_def, Complex.conj_ofReal]
  rw [hC, kernel, fromBlocks_smul, ← fromBlocks_one, sub_eq_add_neg, fromBlocks_neg,
    fromBlocks_add]
  congr 1 <;> simp

theorem one_sub_smul_isHermitian {k : Type*} [DecidableEq k] {M : Matrix k k ℂ}
    (hM : M.IsHermitian) (r : ℝ) : (1 - (r : ℂ) • M).IsHermitian := by
  rw [IsHermitian, conjTranspose_sub, conjTranspose_one, conjTranspose_smul, hM.eq,
    Complex.star_def, Complex.conj_ofReal]

omit [Fintype m] in
/-- The Schur complement of the tail block of `I - rK` is `I - ℱ(r)`. -/
theorem schur_complement_eq (r : ℝ) :
    (1 - (r : ℂ) • A) - (-((r : ℂ) • B)) * (1 - (r : ℂ) • D)⁻¹ * (-((r : ℂ) • B))ᴴ
      = 1 - schurReturn A B D r := by
  rw [schurReturn, conjTranspose_neg, conjTranspose_smul, Complex.star_def, Complex.conj_ofReal]
  simp only [Matrix.neg_mul, Matrix.mul_neg, smul_neg, neg_neg, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, sub_add_eq_sub_sub, pow_two]

set_option linter.unusedFintypeInType false in
/-- **(ER.14) in Schur-complement form**: for every real `r`,
`I - rK ≻ 0 ⟺ I - rD ≻ 0 ∧ I - ℱ(r) ≻ 0`. -/
theorem posDef_one_sub_smul_kernel_iff (hK : (kernel A B D).PosSemidef) (r : ℝ) :
    (1 - (r : ℂ) • kernel A B D).PosDef
      ↔ (1 - (r : ℂ) • D).PosDef ∧ (1 - schurReturn A B D r).PosDef := by
  have hDh : (1 - (r : ℂ) • D).IsHermitian :=
    one_sub_smul_isHermitian (tail_posSemidef A B D hK).1 r
  have hKh : (1 - (r : ℂ) • kernel A B D).IsHermitian := one_sub_smul_isHermitian hK.1 r
  constructor
  · intro h
    have hD : (1 - (r : ℂ) • D).PosDef := by
      have := h.submatrix Sum.inr_injective
      have heq : (1 - (r : ℂ) • kernel A B D).submatrix Sum.inr Sum.inr = 1 - (r : ℂ) • D := by
        rw [one_sub_smul_kernel]
        ext i j
        simp
      rwa [heq] at this
    refine ⟨hD, ?_⟩
    haveI : Invertible (1 - (r : ℂ) • D) := hD.isUnit.invertible
    have hSh : (1 - schurReturn A B D r).IsHermitian := by
      rw [← schur_complement_eq]
      exact (IsHermitian.fromBlocks₂₂ _ _ hDh).mp (by rwa [← one_sub_smul_kernel])
    refine PosDef.of_dotProduct_mulVec_pos hSh fun x hx => ?_
    have hne : Sum.elim x (-(((1 - (r : ℂ) • D)⁻¹ * (-((r : ℂ) • B))ᴴ) *ᵥ x)) ≠ 0 := by
      intro h0
      apply hx
      funext i
      simpa using congrFun h0 (Sum.inl i)
    have hq := h.dotProduct_mulVec_pos hne
    rw [one_sub_smul_kernel, dotProduct_mulVec, schur_complement_eq₂₂ _ _ _ _ hDh,
      add_neg_cancel, schur_complement_eq] at hq
    simpa [dotProduct_mulVec] using hq
  · rintro ⟨hD, hS⟩
    haveI : Invertible (1 - (r : ℂ) • D) := hD.isUnit.invertible
    refine PosDef.of_dotProduct_mulVec_pos hKh fun v hv => ?_
    rw [← Sum.elim_comp_inl_inr v, one_sub_smul_kernel, dotProduct_mulVec,
      schur_complement_eq₂₂ _ _ _ _ hDh, schur_complement_eq]
    by_cases hx : v ∘ Sum.inl = 0
    · have hy : v ∘ Sum.inr ≠ 0 := by
        intro hy
        apply hv
        rw [← Sum.elim_comp_inl_inr v, hx, hy]
        funext i
        cases i <;> rfl
      rw [hx]
      simp only [mulVec_zero, zero_add, star_zero, zero_vecMul, dotProduct_zero, add_zero]
      have := hD.dotProduct_mulVec_pos hy
      rwa [dotProduct_mulVec] at this
    · have h1 := hD.posSemidef.dotProduct_mulVec_nonneg
        (((1 - (r : ℂ) • D)⁻¹ * (-((r : ℂ) • B))ᴴ) *ᵥ (v ∘ Sum.inl) + v ∘ Sum.inr)
      have h2 := hS.dotProduct_mulVec_pos hx
      rw [dotProduct_mulVec] at h1 h2
      exact add_pos_of_nonneg_of_pos h1 h2

/-! ### The boxed norm form of (ER.14) -/

open scoped Matrix.Norms.L2Operator

set_option linter.unusedFintypeInType false in
theorem smul_posSemidef {k : Type*} [Fintype k] {M : Matrix k k ℂ} (hM : M.PosSemidef) {r : ℝ}
    (hr : 0 ≤ r) : ((r : ℂ) • M).PosSemidef := by
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · rw [IsHermitian, conjTranspose_smul, hM.1.eq, Complex.star_def, Complex.conj_ofReal]
  · rw [smul_mulVec, dotProduct_smul]
    exact mul_nonneg (Complex.zero_le_real.mpr hr) (hM.dotProduct_mulVec_nonneg x)

set_option linter.unusedFintypeInType false in
omit [DecidableEq m] in
/-- `ℱ(r)` is a positive kernel whenever `I - rD ≻ 0`. -/
theorem schurReturn_posSemidef (hK : (kernel A B D).PosSemidef) {r : ℝ} (hr : 0 ≤ r)
    (hD : (1 - (r : ℂ) • D).PosDef) : (schurReturn A B D r).PosSemidef := by
  have h1 := smul_posSemidef (head_posSemidef A B D hK) hr
  have h2 : (((r : ℂ) ^ 2) • (B * (1 - (r : ℂ) • D)⁻¹ * Bᴴ)).PosSemidef := by
    have := smul_posSemidef (hD.inv.posSemidef.mul_mul_conjTranspose_same B) (sq_nonneg r)
    rwa [Complex.ofReal_pow] at this
  exact h1.add h2

/-- **(ER.14)**: for every `r > 0`, `‖K‖ < r⁻¹ ⟺ r‖D‖ < 1 ∧ ‖ℱ(r)‖ < 1` (`ℓ²` operator norms). -/
theorem norm_kernel_lt_inv_iff (hK : (kernel A B D).PosSemidef) {r : ℝ} (hr : 0 < r) :
    ‖kernel A B D‖ < r⁻¹ ↔ r * ‖D‖ < 1 ∧ ‖schurReturn A B D r‖ < 1 := by
  have hrK : ((r : ℂ) • kernel A B D).PosSemidef := smul_posSemidef hK hr.le
  have hrD : ((r : ℂ) • D).PosSemidef := smul_posSemidef (tail_posSemidef A B D hK) hr.le
  have h1 : ‖kernel A B D‖ < r⁻¹ ↔ ‖(r : ℂ) • kernel A B D‖ < 1 := by
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hr.le, inv_eq_one_div, lt_div_iff₀ hr,
      mul_comm]
  have h2 : ‖(r : ℂ) • D‖ = r * ‖D‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hr.le]
  rw [h1, PositiveNormBridge.norm_lt_one_iff_posDef_one_sub hrK,
    posDef_one_sub_smul_kernel_iff A B D hK r]
  constructor
  · rintro ⟨hD, hS⟩
    refine ⟨?_, ?_⟩
    · rw [← h2]
      exact (PositiveNormBridge.norm_lt_one_iff_posDef_one_sub hrD).mpr hD
    · exact (PositiveNormBridge.norm_lt_one_iff_posDef_one_sub
        (schurReturn_posSemidef A B D hK hr.le hD)).mpr hS
  · rintro ⟨hD, hS⟩
    have hD' : (1 - (r : ℂ) • D).PosDef :=
      (PositiveNormBridge.norm_lt_one_iff_posDef_one_sub hrD).mp (by rw [h2]; exact hD)
    exact ⟨hD', (PositiveNormBridge.norm_lt_one_iff_posDef_one_sub
      (schurReturn_posSemidef A B D hK hr.le hD')).mp hS⟩

/-- **`thm:GT-positive-first-return-renewal`**: on a source-cyclic carrier with `0 ≼ K ≼ I`,
the tail block is a strict contraction (`I - D ≻ 0`, equivalently `‖D‖ < 1`), every first-return
kernel `Fₙ` is positive, the return series is the two-sided inverse of `I - ℱ` (ER.13), and for
every `r > 0` the criterion (ER.14) `‖K‖ < r⁻¹ ⟺ r‖D‖ < 1 ∧ ‖ℱ(r)‖ < 1` holds. -/
theorem positive_first_return_renewal (hK : (kernel A B D).PosSemidef)
    (hK1 : (1 - kernel A B D).PosSemidef) (hobs : IsSourceObservable B D) :
    ((1 - D).PosDef ∧ ‖D‖ < 1) ∧
      (∀ k, (firstReturn A B D k).PosSemidef) ∧
      (1 - firstReturnSeries A B D) * returnSeries A B D = 1 ∧
      returnSeries A B D * (1 - firstReturnSeries A B D) = 1 ∧
      ∀ r : ℝ, 0 < r →
        (‖kernel A B D‖ < r⁻¹ ↔ r * ‖D‖ < 1 ∧ ‖schurReturn A B D r‖ < 1) := by
  have hD := one_sub_tail_posDef A B D hK1 hobs
  refine ⟨⟨hD, (PositiveNormBridge.norm_lt_one_iff_posDef_one_sub
    (tail_posSemidef A B D hK)).mpr hD⟩, firstReturn_posSemidef A B D hK,
    one_sub_firstReturnSeries_mul A B D, mul_one_sub_firstReturnSeries A B D,
    fun r hr => norm_kernel_lt_inv_iff A B D hK hr⟩

end FirstReturnRenewal
end NCG
