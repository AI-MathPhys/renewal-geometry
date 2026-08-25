/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.DyadicClosedFormExact

/-!
# Lieb concavity at dyadic exponents

Step (D4h) of the finite Uhlmann-monotonicity programme for
`thm:accepted-Petz-sufficiency`: pairing the dyadic geometric-mean iterate
on the Kronecker legs `ρ ⊗ 1` and `1 ⊗ σᵀ` at the entangled vector yields
**Lieb concavity** of `(ρ, σ) ↦ Re Tr(ρ^{1−t} σ^t)` at every dyadic
`t = 2⁻ᵏ`.

* `kronR_posDef`: positive definiteness of the left leg;
* `kronR_kronL_commute`: the two legs commute;
* `pairing`, `pairing_nonneg`: the entangled quadratic functional;
* `iterMean_pairing`: `⟨vec 1, T_k(ρ⊗1, 1⊗σᵀ) vec 1⟩ = Tr(ρ^{1−2⁻ᵏ} σ^{2⁻ᵏ})`;
* `lieb_dyadic`: **Lieb concavity at dyadic exponents**.
-/

open Matrix Unitary Finset Kronecker
open scoped ComplexOrder

namespace NCG
namespace QRE

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {p : Type*} [Fintype p] [DecidableEq p]
variable {A ρ σ : Matrix n n ℂ}

/-! ### Positive definiteness of the left leg -/

omit [DecidableEq n] in
theorem kronR_quadratic (A : Matrix n n ℂ) (v : n × p → ℂ) :
    star v ⬝ᵥ ((A ⊗ₖ (1 : Matrix p p ℂ)) *ᵥ v) =
      ∑ b : p, star (fun i => v (i, b)) ⬝ᵥ (A *ᵥ fun i => v (i, b)) := by
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ => ?_
  congr 1
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i₁ _ => ?_
  rw [Finset.sum_eq_single b]
  · change A i i₁ * (1 : Matrix p p ℂ) b b * v (i₁, b) =
      A i i₁ * v (i₁, b)
    rw [Matrix.one_apply_eq, mul_one]
  · intro y _ hy
    change A i i₁ * (1 : Matrix p p ℂ) b y * v (i₁, y) = 0
    rw [Matrix.one_apply_ne (Ne.symm hy), mul_zero, zero_mul]
  · intro hb
    exact absurd (Finset.mem_univ _) hb

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
omit [DecidableEq n] in
theorem kronR_posDef (hA : A.PosDef) :
    (A ⊗ₖ (1 : Matrix p p ℂ)).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨kronR_isHermitian hA.1, fun v hv => ?_⟩
  rw [kronR_quadratic]
  obtain ⟨q, hq⟩ := Function.ne_iff.mp hv
  refine Finset.sum_pos' (fun b _ => hA.posSemidef.dotProduct_mulVec_nonneg _)
    ⟨q.2, Finset.mem_univ _, ?_⟩
  refine hA.dotProduct_mulVec_pos ?_
  intro h0
  exact hq (congrFun h0 q.1)

/-! ### The commuting legs -/

theorem kronR_kronL_commute (A : Matrix n n ℂ) (C : Matrix p p ℂ) :
    Commute (A ⊗ₖ (1 : Matrix p p ℂ)) ((1 : Matrix n n ℂ) ⊗ₖ C) := by
  unfold Commute SemiconjBy
  calc (A ⊗ₖ (1 : Matrix p p ℂ)) * ((1 : Matrix n n ℂ) ⊗ₖ C)
      = (A * 1) ⊗ₖ ((1 : Matrix p p ℂ) * C) := by
        rw [Matrix.mul_kronecker_mul]
    _ = A ⊗ₖ C := by rw [Matrix.mul_one, Matrix.one_mul]
    _ = (1 * A) ⊗ₖ (C * (1 : Matrix p p ℂ)) := by
        rw [Matrix.one_mul, Matrix.mul_one]
    _ = ((1 : Matrix n n ℂ) ⊗ₖ C) * (A ⊗ₖ (1 : Matrix p p ℂ)) := by
        rw [Matrix.mul_kronecker_mul]

/-! ### The entangled pairing -/

/-- The entangled quadratic functional. -/
noncomputable def pairing (M : Matrix (n × n) (n × n) ℂ) : ℝ :=
  (star vecOne ⬝ᵥ (M *ᵥ vecOne)).re

theorem pairing_nonneg {M : Matrix (n × n) (n × n) ℂ}
    (hM : M.PosSemidef) : 0 ≤ pairing M := by
  have h := hM.dotProduct_mulVec_nonneg (vecOne (n := n))
  rw [Complex.le_def] at h
  unfold pairing
  simpa using h.1

theorem pairing_sub (M N : Matrix (n × n) (n × n) ℂ) :
    pairing (M - N) = pairing M - pairing N := by
  unfold pairing
  rw [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re]

theorem pairing_smul (c : ℝ) (M : Matrix (n × n) (n × n) ℂ) :
    pairing (c • M) = c * pairing M := by
  unfold pairing
  have hmv : (c • M) *ᵥ vecOne = c • (M *ᵥ vecOne (n := n)) := by
    funext q
    simp only [Matrix.mulVec, Matrix.smul_apply, Pi.smul_apply,
      dotProduct, Complex.real_smul]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun r _ => by ring
  rw [hmv, dotProduct_smul, Complex.real_smul, Complex.mul_re]
  simp

theorem pairing_sum {ι : Type*} (s : Finset ι)
    (f : ι → Matrix (n × n) (n × n) ℂ) :
    pairing (∑ j ∈ s, f j) = ∑ j ∈ s, pairing (f j) := by
  classical
  induction s using Finset.cons_induction with
  | empty =>
      unfold pairing
      simp
  | cons a s ha ih =>
      rw [Finset.sum_cons, Finset.sum_cons, ← ih]
      unfold pairing
      rw [Matrix.add_mulVec, dotProduct_add, Complex.add_re]

theorem iterMean_congr {Λ Λ' Ρ Ρ' : Matrix n n ℂ}
    (hΛe : Λ = Λ') (hΡe : Ρ = Ρ') (hΛ : Λ.PosDef) (hΛ' : Λ'.PosDef)
    (hΡ : Ρ.IsHermitian) (hΡ' : Ρ'.IsHermitian) (k : ℕ) :
    iterMean hΛ hΡ k = iterMean hΛ' hΡ' k := by
  subst hΛe
  subst hΡe
  rfl

/-! ### The dyadic trace interpolation -/

/-- `Re Tr(ρ^{1−t} σ^t)` through the spectral calculus. -/
noncomputable def tracePow (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian)
    (t : ℝ) : ℝ :=
  ((matFun hρ (fun x => x ^ (1 - t)) *
    matFun hσ (fun x => x ^ t)).trace).re

set_option maxHeartbeats 3200000 in -- leg transport chain
/-- **The pairing identity**:
`⟨vec 1, T_k(ρ⊗1, 1⊗σᵀ) vec 1⟩ = Re Tr(ρ^{1−2⁻ᵏ} σ^{2⁻ᵏ})`. -/
theorem iterMean_pairing (hρ : ρ.PosDef) (hσ : σ.PosSemidef)
    (hL : (ρ ⊗ₖ (1 : Matrix n n ℂ)).PosDef)
    (hR : ((1 : Matrix n n ℂ) ⊗ₖ σᵀ).PosSemidef) (k : ℕ) :
    pairing (iterMean hL hR.1 k) =
      tracePow hρ.1 hσ.1 ((2 : ℝ)⁻¹ ^ k) := by
  have hcomm : Commute (ρ ⊗ₖ (1 : Matrix n n ℂ))
      ((1 : Matrix n n ℂ) ⊗ₖ σᵀ) := kronR_kronL_commute ρ σᵀ
  rw [iterMean_commute_closed hL hR hcomm k]
  -- transport the two matFun legs
  have hlegL : matFun hL.1 (fun x => x ^ (1 - (2 : ℝ)⁻¹ ^ k)) =
      matFun hρ.1 (fun x => x ^ (1 - (2 : ℝ)⁻¹ ^ k)) ⊗ₖ 1 :=
    matFun_kronR hρ.1 hL.1 _
  have hσt : (σᵀ).IsHermitian := transpose_isHermitian hσ.1
  have hlegR : matFun hR.1 (fun x => x ^ ((2 : ℝ)⁻¹ ^ k)) =
      (1 : Matrix n n ℂ) ⊗ₖ (matFun hσ.1 (fun x => x ^ ((2 : ℝ)⁻¹ ^ k)))ᵀ := by
    have h1 : matFun hR.1 (fun x => x ^ ((2 : ℝ)⁻¹ ^ k)) =
        (1 : Matrix n n ℂ) ⊗ₖ matFun hσt (fun x => x ^ ((2 : ℝ)⁻¹ ^ k)) :=
      matFun_kron_one hσt hR.1 _
    rw [h1, matFun_transpose hσ.1 hσt]
  rw [hlegL, hlegR]
  have hprod : (matFun hρ.1 (fun x => x ^ (1 - (2 : ℝ)⁻¹ ^ k)) ⊗ₖ
      (1 : Matrix n n ℂ)) *
      ((1 : Matrix n n ℂ) ⊗ₖ
        (matFun hσ.1 (fun x => x ^ ((2 : ℝ)⁻¹ ^ k)))ᵀ) =
      matFun hρ.1 (fun x => x ^ (1 - (2 : ℝ)⁻¹ ^ k)) ⊗ₖ
        (matFun hσ.1 (fun x => x ^ ((2 : ℝ)⁻¹ ^ k)))ᵀ := by
    rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  rw [hprod]
  unfold pairing tracePow
  rw [vecOne_pair, Matrix.transpose_transpose]

set_option maxHeartbeats 1600000 in -- leg mixture bookkeeping
/-- **Lieb concavity at dyadic exponents**: for weights `λ_j ≥ 0`,
`Σ λ_j Re Tr(ρ_j^{1−t} σ_j^t) ≤ Re Tr(ρ̄^{1−t} σ̄^t)` at `t = 2⁻ᵏ`. -/
theorem lieb_dyadic {ι : Type*} [Fintype ι] {lam : ι → ℝ}
    (hlam : ∀ j, 0 ≤ lam j)
    {ρmat σmat : ι → Matrix n n ℂ}
    (hρj : ∀ j, (ρmat j).PosDef) (hσj : ∀ j, (σmat j).PosSemidef)
    (hρbar : (∑ j, lam j • ρmat j).PosDef)
    (hσbar : (∑ j, lam j • σmat j).PosSemidef) (k : ℕ) :
    ∑ j, lam j * tracePow (hρj j).1 (hσj j).1 ((2 : ℝ)⁻¹ ^ k) ≤
      tracePow hρbar.1 hσbar.1 ((2 : ℝ)⁻¹ ^ k) := by
  -- the legs
  set Λmat : ι → Matrix (n × n) (n × n) ℂ :=
    fun j => ρmat j ⊗ₖ (1 : Matrix n n ℂ) with hΛdef
  set Ρmat : ι → Matrix (n × n) (n × n) ℂ :=
    fun j => (1 : Matrix n n ℂ) ⊗ₖ (σmat j)ᵀ with hΡdef
  have hΛj : ∀ j, (Λmat j).PosDef := fun j => kronR_posDef (hρj j)
  have hΡj : ∀ j, (Ρmat j).PosSemidef := fun j =>
    one_kron_posSemidef (transpose_posSemidef (hσj j))
  -- the mixture legs
  have hΛsum : ∑ j, lam j • Λmat j =
      (∑ j, lam j • ρmat j) ⊗ₖ (1 : Matrix n n ℂ) := by
    rw [kronR_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hΛdef, kronR_smul]
  have hΡsum : ∑ j, lam j • Ρmat j =
      (1 : Matrix n n ℂ) ⊗ₖ (∑ j, lam j • σmat j)ᵀ := by
    rw [Matrix.transpose_sum, kron_one_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hΡdef, Matrix.transpose_smul, kron_one_smul]
  have hΛbar : (∑ j, lam j • Λmat j).PosDef := by
    rw [hΛsum]
    exact kronR_posDef hρbar
  have hΡbar : (∑ j, lam j • Ρmat j).PosSemidef := by
    rw [hΡsum]
    exact one_kron_posSemidef (transpose_posSemidef hσbar)
  -- joint concavity of the iterate
  have hconc := iterMean_concave hlam hΛj hΡj hΛbar hΡbar k
  have hpair := pairing_nonneg hconc
  rw [pairing_sub, pairing_sum] at hpair
  have hterm : ∀ j, pairing (lam j • iterMean (hΛj j) (hΡj j).1 k) =
      lam j * tracePow (hρj j).1 (hσj j).1 ((2 : ℝ)⁻¹ ^ k) := by
    intro j
    rw [pairing_smul, iterMean_pairing (hρj j) (hσj j) (hΛj j) (hΡj j)]
  have hbar : pairing (iterMean hΛbar hΡbar.1 k) =
      tracePow hρbar.1 hσbar.1 ((2 : ℝ)⁻¹ ^ k) := by
    have hL' : ((∑ j, lam j • ρmat j) ⊗ₖ (1 : Matrix n n ℂ)).PosDef :=
      kronR_posDef hρbar
    have hR' : ((1 : Matrix n n ℂ) ⊗ₖ (∑ j, lam j • σmat j)ᵀ).PosSemidef :=
      one_kron_posSemidef (transpose_posSemidef hσbar)
    have hiter : iterMean hΛbar hΡbar.1 k = iterMean hL' hR'.1 k :=
      iterMean_congr hΛsum hΡsum hΛbar hL' hΡbar.1 hR'.1 k
    rw [hiter]
    exact iterMean_pairing hρbar hσbar hL' hR' k
  rw [hbar] at hpair
  have hsum : ∑ j, pairing (lam j • iterMean (hΛj j) (hΡj j).1 k) =
      ∑ j, lam j * tracePow (hρj j).1 (hσj j).1 ((2 : ℝ)⁻¹ ^ k) :=
    Finset.sum_congr rfl fun j _ => hterm j
  rw [hsum] at hpair
  linarith

end QRE
end NCG
