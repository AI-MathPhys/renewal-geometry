/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.QuadFormPsdExact

/-!
# Scaling and ancilla laws of the affine quadratic form

Step (B4c) of the BKM programme for `cor:accepted-BKM-loss` (QS.5): the
two exact transport laws of the twirl output,

`tQuad(c·σ, c·v, t) = c · tQuad(σ, v, t)` and
`tQuad(1⊗A, 1⊗w, t) = |K| · tQuad(A, w, t)`,

with **no logarithmic corrections** — the affine kernel scales cleanly.

* `affineOp_smul`, `invMat_smul_pos`, `tQuad_smul`: the scaling law;
* `blockEmb`: the ancilla block isometries, orthogonal and intertwining;
* `affineOp_intertwine''`: the hypothesis-based intertwining;
* `tQuad_kron_one`: **the ancilla law**.
-/

open Matrix Unitary Finset Kronecker
open scoped ComplexOrder

attribute [-instance] CStarMatrix.instHMulOfFintypeOfMulOfAddCommMonoid

namespace NCG
namespace QRE

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {K : Type*} [Fintype K] [DecidableEq K]
variable {σ v A : Matrix n n ℂ}

/-! ### The scaling law -/

theorem matFun_real_smul {N : Type*} [Fintype N] [DecidableEq N]
    {S : Matrix N N ℂ} (hS : S.IsHermitian) (a : ℝ) (f : ℝ → ℝ) :
    matFun hS (fun x => a * f x) = a • matFun hS f := by
  unfold matFun
  have hdiag : diagonal
      (RCLike.ofReal (K := ℂ) ∘ fun i => a * f (hS.eigenvalues i)) =
      (a : ℂ) • diagonal
        (RCLike.ofReal (K := ℂ) ∘ fun i => f (hS.eigenvalues i)) := by
    ext i j
    rcases eq_or_ne i j with rfl | hij
    · simp only [Matrix.diagonal_apply_eq, Matrix.smul_apply,
        Function.comp_apply, smul_eq_mul]
      simp only [show ∀ x : ℝ, RCLike.ofReal (K := ℂ) x =
        Complex.ofReal x from fun _ => rfl]
      push_cast
      ring
    · simp [Matrix.diagonal_apply_ne _ hij]
  rw [hdiag, map_smul]
  ext i j
  simp [Matrix.smul_apply, Complex.real_smul]

omit [Fintype n] in
theorem affineOp_smul (c : ℝ) (σ : Matrix n n ℂ) (t : ℝ) :
    affineOp (c • σ) t = c • affineOp σ t := by
  unfold affineOp
  rw [kronR_smul, Matrix.transpose_smul, kron_one_smul, smul_add]
  congr 1 <;> rw [smul_comm]

theorem invMat_smul_pos {N : Type*} [Fintype N] [DecidableEq N]
    {M : Matrix N N ℂ} (hM : M.IsHermitian) {c : ℝ} (_hc : 0 < c)
    (hcM : (c • M).IsHermitian) :
    invMat hcM = c⁻¹ • invMat hM := by
  unfold invMat
  rw [matFun_smul_pos hM c hcM]
  rw [show (fun x => (c * x)⁻¹) = fun x => c⁻¹ * x⁻¹ from
    funext fun x => by rw [mul_inv]]
  exact matFun_real_smul hM c⁻¹ _

set_option maxHeartbeats 1600000 in -- scaling assembly
/-- **The scaling law**: `tQuad(c·σ, c·v, t) = c · tQuad(σ, v, t)`. -/
theorem tQuad_smul (hσ : σ.IsHermitian) {c : ℝ} (hc : 0 < c)
    (hcσ : (c • σ).IsHermitian) (v : Matrix n n ℂ) (t : ℝ) :
    tQuad hcσ (c • v) t = c * tQuad hσ v t := by
  unfold tQuad
  have hinv : invMat (affineOp_isHermitian hcσ t) =
      c⁻¹ • invMat (affineOp_isHermitian hσ t) := by
    rw [invMat_congr (affineOp_smul c σ t) (affineOp_isHermitian hcσ t)
      (real_smul_isHermitian' c (affineOp_isHermitian hσ t))]
    exact invMat_smul_pos (affineOp_isHermitian hσ t) hc _
  have hvec : vecM (c • v) = (c : ℂ) • vecM v := by
    funext p
    simp [vecM, Matrix.smul_apply, Complex.real_smul]
  have hstar : star ((c : ℂ) • vecM v) = (c : ℂ) • star (vecM v) := by
    funext p
    simp only [Pi.smul_apply, Pi.star_apply, smul_eq_mul, star_mul',
      Complex.star_def, Complex.conj_ofReal]
  rw [hinv, hvec, hstar, real_smul_mulVec, Matrix.mulVec_smul]
  rw [smul_dotProduct, dotProduct_smul, dotProduct_smul]
  rw [smul_smul, smul_smul, smul_eq_mul]
  have hcne : (c : ℂ) ≠ 0 := by
    exact_mod_cast hc.ne'
  rw [show ((c : ℂ) * ((c⁻¹ : ℝ) : ℂ) * (c : ℂ)) = (c : ℂ) from by
    rw [Complex.ofReal_inv]
    field_simp]
  rw [Complex.mul_re]
  simp

/-! ### The ancilla block isometries -/

/-- The block embedding of the ancilla copy `k`. -/
def blockEmb (k : K) : Matrix (K × n) n ℂ :=
  Matrix.of fun p y => if p = (k, y) then 1 else 0

theorem blockEmb_orth (k l : K) :
    (blockEmb (n := n) l)ᴴ * blockEmb (n := n) k =
      if l = k then (1 : Matrix n n ℂ) else 0 := by
  ext x y
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply, blockEmb, Matrix.of_apply]
  rw [Finset.sum_eq_single ((l, x) : K × n)]
  · rw [if_pos rfl, star_one, one_mul]
    rcases eq_or_ne l k with rfl | hlk
    · rw [if_pos rfl, Matrix.one_apply]
      rcases eq_or_ne x y with rfl | hxy
      · rw [if_pos rfl, if_pos rfl]
      · rw [if_neg (fun h => hxy (congrArg Prod.snd h)), if_neg hxy]
    · rw [if_neg hlk, Matrix.zero_apply,
        if_neg (fun h => hlk (congrArg Prod.fst h))]
  · intro p _ hp
    rw [if_neg hp, star_zero, zero_mul]
  · intro habs
    exact absurd (Finset.mem_univ _) habs

theorem blockEmb_isometry (k : K) :
    (blockEmb (n := n) k)ᴴ * blockEmb (n := n) k = (1 : Matrix n n ℂ) := by
  rw [blockEmb_orth k k, if_pos rfl]

omit [Fintype K] in
/-- The block product `Vₖ · w` in closed form. -/
theorem blockEmb_mul (w : Matrix n n ℂ) (k : K) :
    blockEmb (n := n) k * w =
      Matrix.of fun p y => if p.1 = k then w p.2 y else 0 := by
  ext p y
  obtain ⟨p1, p2⟩ := p
  rw [Matrix.mul_apply]
  simp only [blockEmb, Matrix.of_apply]
  rcases eq_or_ne p1 k with rfl | hpk
  · rw [if_pos rfl]
    rw [Finset.sum_eq_single p2]
    · rw [if_pos rfl, one_mul]
    · intro z _ hz
      rw [if_neg (fun h => hz (congrArg Prod.snd h).symm), zero_mul]
    · intro habs
      exact absurd (Finset.mem_univ _) habs
  · rw [if_neg hpk]
    refine Finset.sum_eq_zero fun z _ => ?_
    rw [if_neg (fun h => hpk (congrArg Prod.fst h)), zero_mul]

/-- The block intertwining `(1⊗A)·Vₖ = Vₖ·A`. -/
theorem kron_one_mul_blockEmb (A : Matrix n n ℂ) (k : K) :
    ((1 : Matrix K K ℂ) ⊗ₖ A) * blockEmb (n := n) k = blockEmb (n := n) k * A := by
  rw [blockEmb_mul]
  ext p y
  obtain ⟨p1, p2⟩ := p
  rw [Matrix.mul_apply]
  simp only [Matrix.kroneckerMap_apply, blockEmb, Matrix.of_apply,
    Matrix.one_apply]
  rw [Finset.sum_eq_single ((k, y) : K × n)]
  · rw [if_pos rfl, mul_one]
    rcases eq_or_ne p1 k with rfl | hpk
    · rw [if_pos rfl, if_pos rfl, one_mul]
    · rw [if_neg hpk, if_neg hpk, zero_mul]
  · intro q _ hq
    rw [if_neg hq, mul_zero]
  · intro habs
    exact absurd (Finset.mem_univ _) habs

omit [Fintype n] [Fintype K] in
/-- The block embeddings have real entries. -/
theorem blockEmb_conj_self (k : K) :
    (((blockEmb (n := n) k)ᴴ)ᵀ) = blockEmb (n := n) k := by
  ext p y
  simp only [Matrix.transpose_apply, Matrix.conjTranspose_apply,
    blockEmb, Matrix.of_apply, apply_ite (star : ℂ → ℂ), star_one,
    star_zero]

omit [Fintype n] [DecidableEq n] [Fintype K] in
/-- Transpose of the ancilla kron. -/
theorem kron_one_transpose (A : Matrix n n ℂ) :
    (((1 : Matrix K K ℂ) ⊗ₖ A))ᵀ = (1 : Matrix K K ℂ) ⊗ₖ Aᵀ := by
  ext p q
  simp only [Matrix.transpose_apply, Matrix.kroneckerMap_apply,
    Matrix.one_apply]
  rcases eq_or_ne p.1 q.1 with hpq | hpq
  · rw [if_pos hpq.symm, if_pos hpq]
  · rw [if_neg (Ne.symm hpq), if_neg hpq]

/-! ### The hypothesis-based intertwining -/

set_option maxHeartbeats 1600000 in -- leg intertwining
/-- The affine intertwining from the two leg hypotheses. -/
theorem affineOp_intertwine'' {N' : Type*} [Fintype N'] [DecidableEq N']
    {X : Matrix N' N' ℂ} {V : Matrix N' n ℂ}
    (hXV : X * V = V * σ) (hXT : Xᵀ * (Vᴴ)ᵀ = (Vᴴ)ᵀ * σᵀ) (t : ℝ) :
    affineOp X t * doubledIso V = doubledIso V * affineOp σ t := by
  unfold affineOp doubledIso
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.mul_smul]
  congr 1
  · congr 1
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
    rw [hXV, Matrix.one_mul, Matrix.mul_one]
  · congr 1
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
    rw [hXT, Matrix.one_mul, Matrix.mul_one]

/-! ### The ancilla decomposition -/

set_option maxHeartbeats 1600000 in -- block sum collapse
/-- The ancilla kron as an orthogonal block sum. -/
theorem kron_one_eq_sum_blockEmb (w : Matrix n n ℂ) :
    (1 : Matrix K K ℂ) ⊗ₖ w =
      ∑ k, blockEmb (n := n) k * w * (blockEmb (n := n) k)ᴴ := by
  have hterm : ∀ k, blockEmb (n := n) k * w * (blockEmb (n := n) k)ᴴ =
      (Matrix.of fun p q =>
        if p.1 = k ∧ q.1 = k then w p.2 q.2 else 0 :
        Matrix (K × n) (K × n) ℂ) := by
    intro k
    rw [blockEmb_mul]
    ext p q
    obtain ⟨q1, q2⟩ := q
    rw [Matrix.mul_apply]
    simp only [Matrix.conjTranspose_apply, blockEmb, Matrix.of_apply]
    rw [Finset.sum_eq_single q2]
    · rcases eq_or_ne q1 k with rfl | hqk
      · rw [if_pos rfl, star_one, mul_one]
        rcases eq_or_ne p.1 q1 with hpk | hpk
        · rw [if_pos hpk, if_pos ⟨hpk, rfl⟩]
        · rw [if_neg hpk, if_neg (fun h => hpk h.1)]
      · rw [if_neg (fun h => hqk (congrArg Prod.fst h)), star_zero,
          mul_zero, if_neg (fun h => hqk h.2)]
    · intro z _ hz
      rw [if_neg (fun h => hz (congrArg Prod.snd h).symm), star_zero,
        mul_zero]
    · intro habs
      exact absurd (Finset.mem_univ _) habs
  ext p q
  rw [Matrix.sum_apply]
  simp only [hterm, Matrix.of_apply, Matrix.kroneckerMap_apply,
    Matrix.one_apply]
  rcases eq_or_ne p.1 q.1 with hpq | hpq
  · rw [if_pos hpq]
    rw [Finset.sum_eq_single p.1]
    · rw [if_pos ⟨rfl, hpq.symm⟩, one_mul]
    · intro k _ hk
      rw [if_neg (fun h => hk h.1.symm)]
    · intro habs
      exact absurd (Finset.mem_univ _) habs
  · rw [if_neg hpq, zero_mul]
    symm
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [if_neg (fun h => hpq (h.1.trans h.2.symm))]

/-! ### Orthogonality of the doubled blocks -/

theorem doubledIso_orth (k l : K) :
    (doubledIso (blockEmb (n := n) l))ᴴ *
      doubledIso (blockEmb (n := n) k) =
      if l = k then (1 : Matrix (n × n) (n × n) ℂ) else 0 := by
  unfold doubledIso
  rw [conjTranspose_kron, ← Matrix.mul_kronecker_mul]
  rw [blockEmb_orth k l]
  have hconjleg : ((blockEmb (n := n) l)ᴴ)ᵀᴴ *
      ((blockEmb (n := n) k)ᴴ)ᵀ =
      if l = k then (1 : Matrix n n ℂ) else 0 := by
    rw [conjTranspose_conj_transpose]
    rw [show (blockEmb (n := n) l)ᵀ * ((blockEmb (n := n) k)ᴴ)ᵀ =
        ((blockEmb (n := n) k)ᴴ * blockEmb (n := n) l)ᵀ from
      (Matrix.transpose_mul _ _).symm]
    rw [blockEmb_orth l k]
    rcases eq_or_ne l k with rfl | hlk
    · simp
    · rw [if_neg (fun h => hlk h.symm), if_neg hlk,
        Matrix.transpose_zero]
  rw [hconjleg]
  rcases eq_or_ne l k with rfl | hlk
  · rw [if_pos rfl, if_pos rfl]
    exact Matrix.one_kronecker_one
  · simp only [if_neg hlk]
    exact Matrix.zero_kronecker _

/-! ### The ancilla law -/

omit [Fintype n] [DecidableEq n] in
theorem vecM_sum {ι : Type*} [Fintype ι] (M : ι → Matrix n n ℂ) :
    vecM (∑ k, M k) = ∑ k, vecM (M k) := by
  funext p
  simp [vecM, Matrix.sum_apply, Finset.sum_apply]

omit [DecidableEq n] in
theorem mulVec_sum_vec {N' : Type*} [Fintype N'] {ι : Type*} [Fintype ι]
    (M : Matrix N' N' ℂ) (vs : ι → N' → ℂ) :
    M *ᵥ (∑ k, vs k) = ∑ k, M *ᵥ vs k := by
  funext p
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply,
    Finset.mul_sum]
  rw [Finset.sum_comm]

set_option maxHeartbeats 3200000 in -- orthogonal block assembly
/-- **The ancilla law**:
`tQuad(1⊗A, 1⊗w, t) = |K| · tQuad(A, w, t)`. -/
theorem tQuad_kron_one (hA : A.IsHermitian)
    (hKA : ((1 : Matrix K K ℂ) ⊗ₖ A).IsHermitian)
    (w : Matrix n n ℂ) (t : ℝ) :
    tQuad hKA ((1 : Matrix K K ℂ) ⊗ₖ w) t =
      (Fintype.card K : ℝ) * tQuad hA w t := by
  unfold tQuad
  set W : K → Matrix ((K × n) × (K × n)) (n × n) ℂ :=
    fun k => doubledIso (blockEmb (n := n) k) with hW
  have hXT : ∀ k : K, ((1 : Matrix K K ℂ) ⊗ₖ A)ᵀ *
      ((blockEmb (n := n) k)ᴴ)ᵀ = ((blockEmb (n := n) k)ᴴ)ᵀ * Aᵀ := by
    intro k
    rw [kron_one_transpose, blockEmb_conj_self,
      kron_one_mul_blockEmb (n := n) Aᵀ k]
  have hint : ∀ k : K,
      affineOp ((1 : Matrix K K ℂ) ⊗ₖ A) t * W k =
        W k * affineOp A t := by
    intro k
    simp only [hW]
    exact affineOp_intertwine'' (kron_one_mul_blockEmb (n := n) A k)
      (hXT k) t
  have hinv : ∀ k : K,
      invMat (affineOp_isHermitian hKA t) * W k =
        W k * invMat (affineOp_isHermitian hA t) := fun k =>
    invMat_intertwine _ _ (hint k)
  have horth : ∀ l k : K, (W l)ᴴ * W k =
      if l = k then (1 : Matrix (n × n) (n × n) ℂ) else 0 := by
    intro l k
    simp only [hW]
    exact doubledIso_orth k l
  have hdec : vecM ((1 : Matrix K K ℂ) ⊗ₖ w) =
      ∑ k, W k *ᵥ vecM w := by
    rw [kron_one_eq_sum_blockEmb (n := n) w, vecM_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hW]
    unfold doubledIso
    rw [vecM_kron_mulVec', Matrix.transpose_transpose]
  rw [hdec]
  have hmv : invMat (affineOp_isHermitian hKA t) *ᵥ
      (∑ k, W k *ᵥ vecM w) =
      ∑ k, W k *ᵥ (invMat (affineOp_isHermitian hA t) *ᵥ vecM w) := by
    rw [mulVec_sum_vec]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.mulVec_mulVec, hinv k, ← Matrix.mulVec_mulVec]
  rw [hmv]
  have hstar : star (∑ k, W k *ᵥ vecM w) =
      ∑ k, star (W k *ᵥ vecM w) := by
    funext p
    simp [Finset.sum_apply, Pi.star_apply, star_sum]
  rw [hstar, sum_dotProduct]
  have hpair : ∀ l k : K,
      star (W l *ᵥ vecM w) ⬝ᵥ
        (W k *ᵥ (invMat (affineOp_isHermitian hA t) *ᵥ vecM w)) =
      if l = k then star (vecM w) ⬝ᵥ
        (invMat (affineOp_isHermitian hA t) *ᵥ vecM w) else 0 := by
    intro l k
    rw [adjoint_dot_rect]
    rw [Matrix.mulVec_mulVec, horth k l]
    rcases eq_or_ne l k with rfl | hlk
    · rw [if_pos rfl, if_pos rfl, Matrix.one_mulVec]
    · rw [if_neg (fun h => hlk h.symm), if_neg hlk,
        Matrix.zero_mulVec]
      simp
  have hsum : ∀ l : K,
      star (W l *ᵥ vecM w) ⬝ᵥ
        (∑ k, W k *ᵥ (invMat (affineOp_isHermitian hA t) *ᵥ
          vecM w)) =
      star (vecM w) ⬝ᵥ
        (invMat (affineOp_isHermitian hA t) *ᵥ vecM w) := by
    intro l
    rw [dotProduct_sum]
    rw [Finset.sum_congr rfl fun k _ => hpair l k]
    simp
  rw [Finset.sum_congr rfl fun l _ => hsum l]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Complex.mul_re]
  simp

end QRE
end NCG
