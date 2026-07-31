/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The coherent Kraus source of the twenty-four-outcome metric instrument
  (`thm:flagship-kraus-source-master`, flagship)

The 24 Kraus branches `K_{d,a,σ} = (1/√12)·(I + σ A(u_a))/2` over six
icosahedral line representatives `u_a ⊂ ℝ³` (tight frame
`Σ_a u_a u_aᵀ = 2 I₃`, unit norms), with `A(u) = Σᵢ uᵢ Aᵢ` a Clifford
triple on the external factor `ℂ⁴` and `τ₄ = ¼ Tr`.  With `Γ = R*R`
the coherent Gram source (`gram`):

* `gram_apply` — exact entries
  `⟨d,a,σ|Γ|d',b,τ⟩ = (1 + στ u_a·u_b)/48`;
* `gram_diag` — the completely dephased pointer state is `I₂₄/24`;
* `kraus_complete` — the 24 branches are complete: `Σ K*K = I`;
* `gram_decomposition` — `Γ = ½ P₀ + ⅙ P_V` with `P₀ = j₀ j₀*`,
  `P_V = J_V J_V*` orthogonal projections of ranks one and three
  (`P0_mul_P0`, `PV_mul_PV`, `P0_mul_PV`, `P0_herm`, `PV_herm`,
  `P0_rank`, `PV_rank`);
* `gram_rank` — `rank Γ = 4`, via the isometry `W = [j₀ | J_V]`
  (`Wmat_iso : WᴴW = I₄`);
* `sflip_mul_P0` / `sflip_mul_PV` — under the sign-contrast
  (antipodal) involution the scalar block is even and the vector
  block is odd, witnessing the parity split of `Ran Γ ≅ 1₊ ⊕ 3₋`;
* `ico_frame` / `ico_unit` / `ico_cross` — the explicit golden-ratio
  icosahedral frame realizes the hypotheses, with `|u_a·u_b|² = 1/5`;
* `icosahedral_*` — the conclusions instantiated on that frame.

The full icosahedral (`A₅ × Z₂`) representation classification of
`Ran Γ` beyond the sign parity is classical character theory and is
recorded in the ledger note.
-/

namespace NCG.Kraus24

open Matrix

open scoped Kronecker ComplexOrder

noncomputable section

/-- Index of the external Clifford factor `ℂ² ⊗ ℂ²`. -/
abbrev CIdx := Fin 2 × Fin 2

/-- Kraus branch labels `(d, a, σ)`: depth, line, sign. -/
abbrev KIdx := Fin 2 × Fin 6 × Fin 2

/-! ## The Clifford triple on `ℂ⁴` -/

/-- Pauli `σₓ`. -/
def pX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- Pauli `σ_y`. -/
def pY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]

/-- Pauli `σ_z`. -/
def pZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

private lemma pXX : pX * pX = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pX, Matrix.mul_apply, Fin.sum_univ_two]

private lemma pYY : pY * pY = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pY, Matrix.mul_apply, Fin.sum_univ_two]

private lemma pZZ : pZ * pZ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pZ, Matrix.mul_apply, Fin.sum_univ_two]

private lemma pXY_anti : pX * pY + pY * pX = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pX, pY]

private lemma pXZ_anti : pX * pZ + pZ * pX = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pX, pZ]

private lemma pYZ_anti : pY * pZ + pZ * pY = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pY, pZ]

private lemma pYX_anti : pY * pX + pX * pY = 0 := by
  rw [add_comm]; exact pXY_anti

private lemma pZX_anti : pZ * pX + pX * pZ = 0 := by
  rw [add_comm]; exact pXZ_anti

private lemma pZY_anti : pZ * pY + pY * pZ = 0 := by
  rw [add_comm]; exact pYZ_anti

private lemma trace_pX : trace pX = 0 := by
  simp [pX, Matrix.trace, Matrix.diag, Fin.sum_univ_two]

private lemma trace_pY : trace pY = 0 := by
  simp [pY, Matrix.trace, Matrix.diag, Fin.sum_univ_two]

private lemma trace_pZ : trace pZ = 0 := by
  simp [pZ, Matrix.trace, Matrix.diag, Fin.sum_univ_two]

private lemma trace_pXY : trace (pX * pY) = 0 := by
  simp [pX, pY, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Fin.sum_univ_two]

private lemma trace_pYX : trace (pY * pX) = 0 := by
  simp [pX, pY, Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Fin.sum_univ_two]

private lemma pX_herm : pXᴴ = pX := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pX, Matrix.conjTranspose_apply]

private lemma pY_herm : pYᴴ = pY := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pY, Matrix.conjTranspose_apply]

private lemma pZ_herm : pZᴴ = pZ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pZ, Matrix.conjTranspose_apply]

/-- The Clifford triple `Aᵢ = γ⁰γᵢ`, realized as
`σₓ⊗1, σ_y⊗1, σ_z⊗σₓ`. -/
def cliff : Fin 3 → Matrix CIdx CIdx ℂ
  | 0 => pX ⊗ₖ 1
  | 1 => pY ⊗ₖ 1
  | 2 => pZ ⊗ₖ pX

private lemma cliff_trace : ∀ i, trace (cliff i) = 0 := by
  intro i
  fin_cases i <;>
    simp [cliff, Matrix.trace_kronecker, trace_pX, trace_pY, trace_pZ]

private lemma cliff_pair_trace :
    ∀ i j, trace (cliff i * cliff j) = if i = j then 4 else 0 := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [cliff, ← Matrix.mul_kronecker_mul, Matrix.trace_kronecker, pXX, pYY,
      pZZ, trace_pX, trace_pXY, trace_pYX, Matrix.trace_one]

private lemma cliff_herm : ∀ i, (cliff i)ᴴ = cliff i := by
  intro i
  fin_cases i <;>
    simp [cliff, Matrix.conjTranspose_kronecker, pX_herm, pY_herm, pZ_herm]

private lemma cliff_anticomm :
    ∀ i j, cliff i * cliff j + cliff j * cliff i
      = if i = j then (2 : ℂ) • 1 else 0 := by
  intro i j
  fin_cases i <;> fin_cases j
  · rw [if_pos rfl]
    simp only [cliff, ← Matrix.mul_kronecker_mul, pXX, Matrix.mul_one,
      Matrix.one_kronecker_one]
    rw [two_smul]
  · rw [if_neg (by decide)]
    simp only [cliff, ← Matrix.mul_kronecker_mul, Matrix.mul_one]
    rw [← Matrix.add_kronecker, pXY_anti, Matrix.zero_kronecker]
  · rw [if_neg (by decide)]
    simp only [cliff, ← Matrix.mul_kronecker_mul, Matrix.mul_one,
      Matrix.one_mul]
    rw [← Matrix.add_kronecker, pXZ_anti, Matrix.zero_kronecker]
  · rw [if_neg (by decide)]
    simp only [cliff, ← Matrix.mul_kronecker_mul, Matrix.mul_one]
    rw [← Matrix.add_kronecker, pYX_anti, Matrix.zero_kronecker]
  · rw [if_pos rfl]
    simp only [cliff, ← Matrix.mul_kronecker_mul, pYY, Matrix.mul_one,
      Matrix.one_kronecker_one]
    rw [two_smul]
  · rw [if_neg (by decide)]
    simp only [cliff, ← Matrix.mul_kronecker_mul, Matrix.mul_one,
      Matrix.one_mul]
    rw [← Matrix.add_kronecker, pYZ_anti, Matrix.zero_kronecker]
  · rw [if_neg (by decide)]
    simp only [cliff, ← Matrix.mul_kronecker_mul, Matrix.mul_one,
      Matrix.one_mul]
    rw [← Matrix.add_kronecker, pZX_anti, Matrix.zero_kronecker]
  · rw [if_neg (by decide)]
    simp only [cliff, ← Matrix.mul_kronecker_mul, Matrix.mul_one,
      Matrix.one_mul]
    rw [← Matrix.add_kronecker, pZY_anti, Matrix.zero_kronecker]
  · rw [if_pos rfl]
    simp only [cliff, ← Matrix.mul_kronecker_mul, pZZ, pXX,
      Matrix.one_kronecker_one]
    rw [two_smul]

/-! ## The Clifford map `A(u)` and its trace calculus -/

/-- `A(x) = Σᵢ xᵢ Aᵢ`. -/
def Amap (x : Fin 3 → ℝ) : Matrix CIdx CIdx ℂ :=
  ∑ i, (x i : ℂ) • cliff i

theorem Amap_herm (x : Fin 3 → ℝ) : (Amap x)ᴴ = Amap x := by
  simp [Amap, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul,
    cliff_herm]

theorem trace_Amap (x : Fin 3 → ℝ) : trace (Amap x) = 0 := by
  simp [Amap, Matrix.trace_sum, Matrix.trace_smul, cliff_trace]

private lemma Amap_expand (x y : Fin 3 → ℝ) :
    Amap x * Amap y
      = ∑ i, ∑ j, ((x i : ℂ) * (y j : ℂ)) • (cliff i * cliff j) := by
  rw [Amap, Amap, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun i _ =>
    Finset.sum_congr rfl fun j _ => smul_mul_smul_comm _ _ _ _

/-- `Tr(A(x) A(y)) = 4 (x·y)`, i.e. `τ₄(A(x)A(y)) = x·y`. -/
theorem trace_Amap_mul (x y : Fin 3 → ℝ) :
    trace (Amap x * Amap y) = 4 * ((x ⬝ᵥ y : ℝ) : ℂ) := by
  rw [Amap_expand]
  simp only [Matrix.trace_sum, Matrix.trace_smul, cliff_pair_trace,
    smul_eq_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    if_true]
  push_cast [dotProduct]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The Clifford relation `{A(x), A(y)} = 2(x·y)·I`. -/
theorem Amap_anticomm (x y : Fin 3 → ℝ) :
    Amap x * Amap y + Amap y * Amap x
      = ((2 * (x ⬝ᵥ y) : ℝ) : ℂ) • 1 := by
  have expand2 : Amap y * Amap x
      = ∑ i, ∑ j, ((x i : ℂ) * (y j : ℂ)) • (cliff j * cliff i) := by
    rw [Amap, Amap, Finset.sum_mul_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [smul_mul_smul_comm, mul_comm ((y j : ℂ)) ((x i : ℂ))]
  rw [Amap_expand, expand2, ← Finset.sum_add_distrib]
  have hcombine : ∀ i : Fin 3,
      ((∑ j, ((x i : ℂ) * (y j : ℂ)) • (cliff i * cliff j))
        + ∑ j, ((x i : ℂ) * (y j : ℂ)) • (cliff j * cliff i))
      = ∑ j, ((x i : ℂ) * (y j : ℂ))
          • (cliff i * cliff j + cliff j * cliff i) := by
    intro i
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => (smul_add _ _ _).symm
  rw [Finset.sum_congr rfl fun i _ => hcombine i]
  simp only [cliff_anticomm, smul_ite, smul_zero]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp only [smul_smul]
  rw [← Finset.sum_smul]
  congr 1
  push_cast [dotProduct]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- `A(x)² = |x|²·I`. -/
theorem Amap_sq (x : Fin 3 → ℝ) :
    Amap x * Amap x = ((x ⬝ᵥ x : ℝ) : ℂ) • 1 := by
  have h := Amap_anticomm x x
  rw [← two_smul ℂ (Amap x * Amap x)] at h
  have h2 : ((2 * (x ⬝ᵥ x) : ℝ) : ℂ) • (1 : Matrix CIdx CIdx ℂ)
      = (2 : ℂ) • (((x ⬝ᵥ x : ℝ) : ℂ) • (1 : Matrix CIdx CIdx ℂ)) := by
    rw [smul_smul]
    push_cast
    ring_nf
  exact smul_right_injective (Matrix CIdx CIdx ℂ) two_ne_zero (h.trans h2)

/-! ## The 24 Kraus branches and the coherent Gram source -/

/-- Branch sign `σ ↦ ±1`. -/
def sgn : Fin 2 → ℝ
  | 0 => 1
  | 1 => -1

@[simp] private lemma sgn_zero : sgn 0 = 1 := rfl

@[simp] private lemma sgn_one : sgn 1 = -1 := rfl

private lemma sgn_mul_self (σ : Fin 2) : sgn σ * sgn σ = 1 := by
  fin_cases σ <;> norm_num

variable (u : Fin 6 → Fin 3 → ℝ)

/-- The Kraus branch `K_{d,a,σ} = (1/√12) (I + σ A(u_a))/2`. -/
def kraus (x : KIdx) : Matrix CIdx CIdx ℂ :=
  (((Real.sqrt 12)⁻¹ / 2 : ℝ) : ℂ)
    • (1 + ((sgn x.2.2 : ℝ) : ℂ) • Amap (u x.2.1))

/-- The coherent Gram source `Γ = R*R`: `Γ_{x,y} = τ₄(K_x* K_y)`. -/
def gram : Matrix KIdx KIdx ℂ :=
  Matrix.of fun x y => (4 : ℂ)⁻¹ * trace ((kraus u x)ᴴ * kraus u y)

private lemma kraus_pair (x y : KIdx) :
    (kraus u x)ᴴ * kraus u y
      = ((48 : ℝ)⁻¹ : ℂ)
          • ((1 : Matrix CIdx CIdx ℂ)
            + ((sgn x.2.2 : ℝ) : ℂ) • Amap (u x.2.1)
            + ((sgn y.2.2 : ℝ) : ℂ) • Amap (u y.2.1)
            + (((sgn x.2.2 : ℝ) : ℂ) * ((sgn y.2.2 : ℝ) : ℂ))
                • (Amap (u x.2.1) * Amap (u y.2.1))) := by
  rw [kraus, kraus, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
    Matrix.conjTranspose_one, Matrix.conjTranspose_smul, Amap_herm,
    smul_mul_smul_comm]
  have hsc : star ((((Real.sqrt 12)⁻¹ / 2 : ℝ)) : ℂ)
      * ((((Real.sqrt 12)⁻¹ / 2 : ℝ)) : ℂ) = ((48 : ℝ)⁻¹ : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul]
    have h12 : (Real.sqrt 12)⁻¹ * (Real.sqrt 12)⁻¹ = (12 : ℝ)⁻¹ := by
      rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]
    rw [show ((Real.sqrt 12)⁻¹ / 2) * ((Real.sqrt 12)⁻¹ / 2)
        = ((Real.sqrt 12)⁻¹ * (Real.sqrt 12)⁻¹) / 4 by ring, h12]
    norm_num
  have hstar : star (((sgn x.2.2 : ℝ)) : ℂ) = ((sgn x.2.2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal]
  rw [hsc, hstar]
  congr 1
  rw [mul_add, mul_one, add_mul, one_mul, smul_mul_assoc, mul_smul_comm,
    smul_smul, ← add_assoc]

/-- `thm:flagship-kraus-source-master`, exact entries:
`⟨d,a,σ|Γ|d',b,τ⟩ = (1 + στ u_a·u_b)/48`. -/
theorem gram_apply (x y : KIdx) :
    gram u x y
      = (((1 + sgn x.2.2 * sgn y.2.2 * (u x.2.1 ⬝ᵥ u y.2.1)) / 48 : ℝ)
          : ℂ) := by
  simp only [gram, Matrix.of_apply]
  rw [kraus_pair, Matrix.trace_smul, Matrix.trace_add, Matrix.trace_add,
    Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
    Matrix.trace_smul, Matrix.trace_one, trace_Amap, trace_Amap,
    trace_Amap_mul]
  simp only [smul_eq_mul, mul_zero, add_zero, Fintype.card_prod,
    Fintype.card_fin]
  push_cast
  ring

/-- `thm:flagship-kraus-source-master`, dephased pointer state:
`Diag(Γ) = I₂₄/24`. -/
theorem gram_diag (hunit : ∀ a, u a ⬝ᵥ u a = 1) (x : KIdx) :
    gram u x x = ((24 : ℝ)⁻¹ : ℂ) := by
  rw [gram_apply, hunit, mul_one, sgn_mul_self]
  norm_num

/-- Completeness of the 24 branches: `Σ K*K = I`. -/
theorem kraus_complete (hunit : ∀ a, u a ⬝ᵥ u a = 1) :
    ∑ x : KIdx, (kraus u x)ᴴ * kraus u x = 1 := by
  have hsum : (∑ x : KIdx, (kraus u x)ᴴ * kraus u x)
      = ∑ a : Fin 6, ∑ d : Fin 2, ∑ σ : Fin 2,
          (kraus u (d, a, σ))ᴴ * kraus u (d, a, σ) := by
    rw [Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type]
    exact Finset.sum_comm
  rw [hsum]
  have hpa : ∀ a : Fin 6,
      (∑ d : Fin 2, ∑ σ : Fin 2,
        (kraus u (d, a, σ))ᴴ * kraus u (d, a, σ))
      = ((6 : ℝ)⁻¹ : ℂ) • 1 := by
    intro a
    have hAA : Amap (u a) * Amap (u a) = 1 := by
      rw [Amap_sq, hunit]
      simp
    simp only [Fin.sum_univ_two, kraus_pair, hAA, sgn_zero, sgn_one]
    push_cast
    module
  rw [Finset.sum_congr rfl fun a _ => hpa a, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℂ,
    smul_smul]
  norm_num

/-! ## The rank-one and rank-three projections -/

/-- The normalized scalar column `j₀`. -/
def jcol : Matrix KIdx (Fin 1) ℂ :=
  Matrix.of fun _ _ => (((Real.sqrt 24)⁻¹ : ℝ) : ℂ)

/-- The sign-weighted frame columns `J_V`. -/
def Jcol : Matrix KIdx (Fin 3) ℂ :=
  Matrix.of fun x i => ((sgn x.2.2 * u x.2.1 i * (Real.sqrt 8)⁻¹ : ℝ) : ℂ)

/-- The rank-one scalar projection `P₀ = j₀ j₀*`. -/
def P0 : Matrix KIdx KIdx ℂ := jcol * jcolᴴ

/-- The rank-three vector projection `P_V = J_V J_V*`. -/
def PV : Matrix KIdx KIdx ℂ := Jcol u * (Jcol u)ᴴ

private lemma sum_KIdx {M : Type*} [AddCommMonoid M] (f : KIdx → M) :
    ∑ x : KIdx, f x
      = ∑ a : Fin 6, ∑ d : Fin 2, ∑ σ : Fin 2, f (d, a, σ) := by
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  exact Finset.sum_comm

private lemma hsum_jj :
    ∑ x : KIdx, star (jcol x 0) * jcol x 0 = 1 := by
  have h24 : ((Real.sqrt 24)⁻¹ * (Real.sqrt 24)⁻¹ : ℝ) = (24 : ℝ)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]
  simp only [jcol, Matrix.of_apply, Complex.star_def, Complex.conj_ofReal,
    ← Complex.ofReal_mul, h24, Finset.sum_const, Finset.card_univ,
    Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  norm_num

private lemma hsum_jJ (i : Fin 3) :
    ∑ x : KIdx, star (jcol x 0) * Jcol u x i = 0 := by
  rw [sum_KIdx]
  refine Finset.sum_eq_zero fun a _ => ?_
  simp only [jcol, Jcol, Matrix.of_apply, Complex.star_def,
    Complex.conj_ofReal, Fin.sum_univ_two, sgn_zero, sgn_one]
  push_cast
  ring

private lemma hsum_Jj (i : Fin 3) :
    ∑ x : KIdx, star (Jcol u x i) * jcol x 0 = 0 := by
  rw [sum_KIdx]
  refine Finset.sum_eq_zero fun a _ => ?_
  simp only [jcol, Jcol, Matrix.of_apply, Complex.star_def,
    Complex.conj_ofReal, Fin.sum_univ_two, sgn_zero, sgn_one]
  push_cast
  ring

private lemma hsum_JJ
    (hframe : ∀ i j, ∑ a, u a i * u a j = if i = j then 2 else 0)
    (i j : Fin 3) :
    ∑ x : KIdx, star (Jcol u x i) * Jcol u x j
      = if i = j then 1 else 0 := by
  have h8 : ((Real.sqrt 8)⁻¹ * (Real.sqrt 8)⁻¹ : ℝ) = (8 : ℝ)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]
  have hreal : ∑ a : Fin 6, ∑ d : Fin 2, ∑ σ : Fin 2,
      ((sgn σ * u a i * (Real.sqrt 8)⁻¹)
        * (sgn σ * u a j * (Real.sqrt 8)⁻¹))
      = if i = j then 1 else 0 := by
    have hpa : ∀ a : Fin 6, (∑ d : Fin 2, ∑ σ : Fin 2,
        ((sgn σ * u a i * (Real.sqrt 8)⁻¹)
          * (sgn σ * u a j * (Real.sqrt 8)⁻¹)))
        = u a i * u a j * 2⁻¹ := by
      intro a
      simp only [Fin.sum_univ_two, sgn_zero, sgn_one]
      linear_combination 4 * u a i * u a j * h8
    rw [Finset.sum_congr rfl fun a _ => hpa a, ← Finset.sum_mul, hframe]
    split <;> norm_num
  rw [sum_KIdx]
  have hcast : (∑ a : Fin 6, ∑ d : Fin 2, ∑ σ : Fin 2,
      star (Jcol u (d, a, σ) i) * Jcol u (d, a, σ) j)
      = ((∑ a : Fin 6, ∑ d : Fin 2, ∑ σ : Fin 2,
          ((sgn σ * u a i * (Real.sqrt 8)⁻¹)
            * (sgn σ * u a j * (Real.sqrt 8)⁻¹)) : ℝ) : ℂ) := by
    simp only [Jcol, Matrix.of_apply, Complex.star_def,
      Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_sum]
  rw [hcast, hreal]
  split <;> norm_num

private lemma jcol_iso : jcolᴴ * jcol = 1 := by
  ext k k'
  fin_cases k
  fin_cases k'
  simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
    using hsum_jj

private lemma Jcol_iso
    (hframe : ∀ i j, ∑ a, u a i * u a j = if i = j then 2 else 0) :
    (Jcol u)ᴴ * Jcol u = 1 := by
  ext i j
  simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply]
    using hsum_JJ u hframe i j

private lemma jJ_zero : jcolᴴ * Jcol u = 0 := by
  ext k i
  fin_cases k
  simpa [Matrix.mul_apply, Matrix.conjTranspose_apply]
    using hsum_jJ u i

private lemma Jj_zero : (Jcol u)ᴴ * jcol = 0 := by
  ext i k
  fin_cases k
  simpa [Matrix.mul_apply, Matrix.conjTranspose_apply]
    using hsum_Jj u i

theorem P0_mul_P0 : P0 * P0 = P0 := by
  rw [P0, Matrix.mul_assoc, ← Matrix.mul_assoc jcolᴴ, jcol_iso,
    Matrix.one_mul]

theorem PV_mul_PV
    (hframe : ∀ i j, ∑ a, u a i * u a j = if i = j then 2 else 0) :
    PV u * PV u = PV u := by
  rw [PV, Matrix.mul_assoc, ← Matrix.mul_assoc (Jcol u)ᴴ, Jcol_iso u hframe,
    Matrix.one_mul]

theorem P0_mul_PV : P0 * PV u = 0 := by
  rw [P0, PV, Matrix.mul_assoc, ← Matrix.mul_assoc jcolᴴ, jJ_zero u,
    Matrix.zero_mul, Matrix.mul_zero]

theorem PV_mul_P0 : PV u * P0 = 0 := by
  rw [P0, PV, Matrix.mul_assoc, ← Matrix.mul_assoc (Jcol u)ᴴ, Jj_zero u,
    Matrix.zero_mul, Matrix.mul_zero]

theorem P0_herm : P0ᴴ = P0 := by
  rw [P0, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

theorem PV_herm : (PV u)ᴴ = PV u := by
  rw [PV, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

/-- `P₀` has rank one. -/
theorem P0_rank : P0.rank = 1 := by
  rw [P0, Matrix.rank_self_mul_conjTranspose,
    ← Matrix.rank_conjTranspose_mul_self, jcol_iso, Matrix.rank_one]
  simp

/-- `P_V` has rank three. -/
theorem PV_rank
    (hframe : ∀ i j, ∑ a, u a i * u a j = if i = j then 2 else 0) :
    (PV u).rank = 3 := by
  rw [PV, Matrix.rank_self_mul_conjTranspose,
    ← Matrix.rank_conjTranspose_mul_self, Jcol_iso u hframe,
    Matrix.rank_one]
  simp

private lemma P0_apply (x y : KIdx) : P0 x y = ((24 : ℝ)⁻¹ : ℂ) := by
  have h24 : ((Real.sqrt 24)⁻¹ * (Real.sqrt 24)⁻¹ : ℝ) = (24 : ℝ)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]
  simp only [P0, Matrix.mul_apply, Matrix.conjTranspose_apply, jcol,
    Matrix.of_apply, Complex.star_def, Complex.conj_ofReal,
    Fin.sum_univ_one, ← Complex.ofReal_mul, h24]
  norm_num

private lemma PV_apply (x y : KIdx) :
    PV u x y
      = ((sgn x.2.2 * sgn y.2.2 * (u x.2.1 ⬝ᵥ u y.2.1) * 8⁻¹ : ℝ)
          : ℂ) := by
  have h8 : ((Real.sqrt 8)⁻¹ * (Real.sqrt 8)⁻¹ : ℝ) = (8 : ℝ)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]
  simp only [PV, Matrix.mul_apply, Matrix.conjTranspose_apply, Jcol,
    Matrix.of_apply, Complex.star_def, Complex.conj_ofReal,
    ← Complex.ofReal_mul, ← Complex.ofReal_sum]
  rw [Complex.ofReal_inj]
  simp only [dotProduct, Fin.sum_univ_three]
  linear_combination (sgn x.2.2 * sgn y.2.2
      * (u x.2.1 0 * u y.2.1 0 + u x.2.1 1 * u y.2.1 1
        + u x.2.1 2 * u y.2.1 2)) * h8

/-! ## The spectral decomposition `Γ = ½P₀ + ⅙P_V` -/

/-- `thm:flagship-kraus-source-master`, exact source compression:
`Γ = ½ P₀ + ⅙ P_V`. -/
theorem gram_decomposition :
    gram u = (2 : ℂ)⁻¹ • P0 + (6 : ℂ)⁻¹ • PV u := by
  ext x y
  rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, gram_apply,
    P0_apply, PV_apply]
  simp only [smul_eq_mul]
  push_cast
  ring

/-- The eigenvector relations: `Γ` acts by `½` on the scalar column
and by `⅙` on the frame columns. -/
theorem gram_eigen
    (hframe : ∀ i j, ∑ a, u a i * u a j = if i = j then 2 else 0) :
    gram u * jcol = (2 : ℂ)⁻¹ • jcol
      ∧ gram u * Jcol u = (6 : ℂ)⁻¹ • Jcol u := by
  constructor
  · rw [gram_decomposition, Matrix.add_mul, Matrix.smul_mul,
      Matrix.smul_mul, P0, PV, Matrix.mul_assoc, jcol_iso, Matrix.mul_one,
      Matrix.mul_assoc, Jj_zero u, Matrix.mul_zero, smul_zero, add_zero]
  · rw [gram_decomposition, Matrix.add_mul, Matrix.smul_mul,
      Matrix.smul_mul, P0, PV, Matrix.mul_assoc, jJ_zero u,
      Matrix.mul_zero, smul_zero, zero_add, Matrix.mul_assoc,
      Jcol_iso u hframe, Matrix.mul_one]

/-! ## Rank four -/

/-- The stacked isometry `W = [j₀ | J_V] : ℂ⁴ → ℂ²⁴`. -/
def Wmat : Matrix KIdx (Fin 4) ℂ :=
  Matrix.of fun x k =>
    (Fin.cons (jcol x 0) (fun i => Jcol u x i) : Fin 4 → ℂ) k

/-- `WᴴW = I₄`: the four coherent directions are orthonormal. -/
theorem Wmat_iso
    (hframe : ∀ i j, ∑ a, u a i * u a j = if i = j then 2 else 0) :
    (Wmat u)ᴴ * Wmat u = 1 := by
  ext k k'
  rw [Matrix.mul_apply]
  induction k using Fin.cases with
  | zero =>
    induction k' using Fin.cases with
    | zero =>
      simpa [Wmat, Matrix.conjTranspose_apply, Matrix.one_apply]
        using hsum_jj
    | succ i =>
      simpa [Wmat, Matrix.conjTranspose_apply, Matrix.one_apply,
        (Fin.succ_ne_zero i).symm] using hsum_jJ u i
  | succ i =>
    induction k' using Fin.cases with
    | zero =>
      simpa [Wmat, Matrix.conjTranspose_apply, Matrix.one_apply,
        Fin.succ_ne_zero i] using hsum_Jj u i
    | succ i' =>
      simpa [Wmat, Matrix.conjTranspose_apply, Matrix.one_apply,
        Fin.succ_inj] using hsum_JJ u hframe i i'

private lemma WWH : Wmat u * (Wmat u)ᴴ = P0 + PV u := by
  ext x y
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Wmat,
    Matrix.of_apply, Matrix.add_apply, P0, PV, Fin.sum_univ_succ,
    Fin.cons_zero, Fin.cons_succ, Fin.sum_univ_zero, add_zero]

/-- The weighted analysis factor `B = D Wᴴ` with `D = diag(½,⅙,⅙,⅙)`. -/
def Bmat : Matrix (Fin 4) KIdx ℂ :=
  Matrix.of fun k y =>
    (Fin.cons ((2 : ℂ)⁻¹ * star (jcol y 0))
      (fun i => (6 : ℂ)⁻¹ * star (Jcol u y i)) : Fin 4 → ℂ) k

private lemma gram_factor : gram u = Wmat u * Bmat u := by
  ext x y
  rw [show gram u x y = ((2 : ℂ)⁻¹ • P0 + (6 : ℂ)⁻¹ • PV u) x y by
    rw [gram_decomposition]]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Wmat, Bmat,
    Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, P0, PV,
    Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.sum_univ_zero,
    add_zero, smul_eq_mul]
  ring

/-- `thm:flagship-kraus-source-master`, `rank Γ = 4`. -/
theorem gram_rank
    (hframe : ∀ i j, ∑ a, u a i * u a j = if i = j then 2 else 0) :
    (gram u).rank = 4 := by
  have hW : (Wmat u).rank = 4 := by
    rw [← Matrix.rank_conjTranspose_mul_self, Wmat_iso u hframe,
      Matrix.rank_one]
    simp
  refine le_antisymm ?_ ?_
  · calc (gram u).rank = (Wmat u * Bmat u).rank := by rw [← gram_factor]
    _ ≤ (Wmat u).rank := Matrix.rank_mul_le_left _ _
    _ = 4 := hW
  · have hQ : gram u * ((2 : ℂ) • P0 + (6 : ℂ) • PV u)
        = Wmat u * (Wmat u)ᴴ := by
      rw [gram_decomposition, WWH, Matrix.add_mul, Matrix.mul_add,
        Matrix.mul_add]
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        P0_mul_P0, PV_mul_PV u hframe, P0_mul_PV u, PV_mul_P0 u,
        smul_zero, add_zero, zero_add]
      norm_num
    calc (4 : ℕ) = (Wmat u * (Wmat u)ᴴ).rank := by
          rw [Matrix.rank_self_mul_conjTranspose, hW]
    _ = (gram u * ((2 : ℂ) • P0 + (6 : ℂ) • PV u)).rank := by rw [hQ]
    _ ≤ (gram u).rank := Matrix.rank_mul_le_left _ _

/-! ## The sign-contrast (antipodal) parity -/

/-- The sign-flip involution on branch labels. -/
def sflip (x : KIdx) : KIdx := (x.1, x.2.1, x.2.2 + 1)

/-- Its permutation matrix. -/
def Sflip : Matrix KIdx KIdx ℂ :=
  Matrix.of fun x y => if y = sflip x then 1 else 0

private lemma sgn_flip (σ : Fin 2) : sgn (σ + 1) = -sgn σ := by
  fin_cases σ <;> norm_num [show ((0 : Fin 2) + 1) = 1 from rfl,
    show ((1 : Fin 2) + 1) = 0 from rfl]

private lemma Sflip_mul_apply (M : Matrix KIdx KIdx ℂ) (x y : KIdx) :
    (Sflip * M) x y = M (sflip x) y := by
  rw [Matrix.mul_apply]
  simp [Sflip, Finset.sum_ite_eq']

/-- The scalar block is sign-contrast even. -/
theorem sflip_mul_P0 : Sflip * P0 = P0 := by
  ext x y
  rw [Sflip_mul_apply, P0_apply, P0_apply]

/-- The vector block is sign-contrast odd: `Ran Γ ≅ 1₊ ⊕ 3₋`. -/
theorem sflip_mul_PV : Sflip * PV u = -PV u := by
  ext x y
  rw [Sflip_mul_apply, PV_apply, Matrix.neg_apply, PV_apply]
  have : sgn ((sflip x).2.2) = -sgn x.2.2 := sgn_flip x.2.2
  rw [show (sflip x).2.1 = x.2.1 from rfl, this]
  push_cast
  ring

/-! ## The golden-ratio icosahedral frame -/

open Real in
open scoped goldenRatio in
/-- The six unnormalized icosahedral vertex representatives. -/
def icoRaw : Fin 6 → Fin 3 → ℝ
  | 0 => ![1, φ, 0]
  | 1 => ![-1, φ, 0]
  | 2 => ![0, 1, φ]
  | 3 => ![0, -1, φ]
  | 4 => ![φ, 0, 1]
  | 5 => ![-φ, 0, 1]

open Real in
open scoped goldenRatio in
/-- The normalized icosahedral line representatives. -/
def ico : Fin 6 → Fin 3 → ℝ := fun a i => (Real.sqrt (φ + 2))⁻¹ * icoRaw a i

section Ico

open Real

open scoped goldenRatio

private lemma hgold : φ ^ 2 = φ + 1 := goldenRatio_sq

private lemma hkey : ((Real.sqrt (φ + 2))⁻¹) ^ 2 * (φ + 2) = 1 := by
  have hpos : (0 : ℝ) < φ + 2 := by positivity
  rw [sq, ← mul_inv, Real.mul_self_sqrt hpos.le]
  field_simp

/-- Unit normalization of the icosahedral representatives. -/
theorem ico_unit : ∀ a, ico a ⬝ᵥ ico a = 1 := by
  intro a
  fin_cases a <;>
    (simp only [ico, icoRaw, dotProduct, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons];
     linear_combination ((Real.sqrt (φ + 2))⁻¹) ^ 2 * hgold + hkey)

/-- The tight-frame identity `Σ_a u_a u_aᵀ = 2 I₃`. -/
theorem ico_frame :
    ∀ i j, ∑ a, ico a i * ico a j = if i = j then 2 else 0 := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    (simp only [ico, icoRaw, Fin.sum_univ_six,
      show (⟨0, by omega⟩ : Fin 3) = 0 from rfl,
      show (⟨1, by omega⟩ : Fin 3) = 1 from rfl,
      show (⟨2, by omega⟩ : Fin 3) = 2 from rfl,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons, Fin.reduceEq, reduceIte];
     first
      | (linear_combination
          (2 : ℝ) * ((Real.sqrt (φ + 2))⁻¹) ^ 2 * hgold + 2 * hkey)
      | ring1)

/-- Icosahedral cross coherence: `|u_a·u_b|² = 1/5` for `a ≠ b`. -/
theorem ico_cross :
    ∀ a b, a ≠ b → (ico a ⬝ᵥ ico b) ^ 2 = 1 / 5 := by
  have hquad : 5 * φ ^ 2 = (φ + 2) ^ 2 := by
    linear_combination 4 * hgold
  have hkey2 : ((Real.sqrt (φ + 2))⁻¹) ^ 4 * (φ + 2) ^ 2 = 1 := by
    have h := hkey
    nlinarith [h]
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  intro a b hab
  fin_cases a <;> fin_cases b <;>
    first
      | exact absurd rfl hab
      | (simp only [ico, icoRaw, dotProduct, Fin.sum_univ_three,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          Matrix.cons_val_two, Matrix.tail_cons];
         first
          | (linear_combination (1 / 5 : ℝ) * hkey2
              + (((Real.sqrt (φ + 2))⁻¹) ^ 4 / 5) * hquad)
          | (linear_combination (1 / 5 : ℝ) * hkey2
              + (((Real.sqrt (φ + 2))⁻¹) ^ 4 / 5) * hquad
              + ((Real.sqrt (φ + 2))⁻¹) ^ 4
                  * (Real.sqrt 5 ^ 2 / 16 + Real.sqrt 5 / 4 - 1 / 16)
                  * h5))

end Ico

/-! ## The icosahedral instantiation -/

/-- `thm:flagship-kraus-source-master` on the golden-ratio frame:
exact source compression `Γ = ½P₀ + ⅙P_V`, spectral projections,
rank four, entries, dephased diagonal, and completeness. -/
theorem icosahedral_source_compression :
    gram ico = (2 : ℂ)⁻¹ • P0 + (6 : ℂ)⁻¹ • PV ico
      ∧ (gram ico).rank = 4
      ∧ (∀ x : KIdx, gram ico x x = ((24 : ℝ)⁻¹ : ℂ))
      ∧ ∑ x : KIdx, (kraus ico x)ᴴ * kraus ico x = 1 := by
  exact ⟨gram_decomposition ico, gram_rank ico ico_frame,
    gram_diag ico ico_unit, kraus_complete ico ico_unit⟩

/-- The projections on the icosahedral frame are orthogonal of ranks
one and three, and split evenly/oddly under the sign contrast. -/
theorem icosahedral_projection_split :
    PV ico * PV ico = PV ico ∧ P0 * PV ico = 0
      ∧ P0.rank = 1 ∧ (PV ico).rank = 3
      ∧ Sflip * P0 = P0 ∧ Sflip * PV ico = -PV ico := by
  exact ⟨PV_mul_PV ico ico_frame, P0_mul_PV ico, P0_rank,
    PV_rank ico ico_frame, sflip_mul_P0, sflip_mul_PV ico⟩

end

end NCG.Kraus24
