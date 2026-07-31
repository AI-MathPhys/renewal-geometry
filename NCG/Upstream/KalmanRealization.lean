/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Upstream.HodgeBSD

/-!
# Finite Kalman realization theory and Hankel saturation
  (`thm:physical-source-completeness` (flagship),
   `thm:v5-hankel-descent`, `thm:v5-block-hankel-packet`,
   SM_emergence)

* `krylovMat` — the stacked Krylov/controllability block matrix
  `[S, MS, M²S, …]`;
* `block_hankel_gram` / `block_hankel_rank` — the block-Hankel
  moment matrix is the Gram matrix of the Krylov family, so its
  rank equals the dimension of the Krylov span
  (`thm:v5-block-hankel-packet`);
* `hankel_descent` — covariant relabellings preserve `ker H`,
  descend isometrically, and the quotient dimension is `rank H`
  (`thm:v5-hankel-descent`);
* `physical_source_uniqueness` — two source-minimal finite triples
  with identical all-order moments are related by a unitary `W`
  with `WB = B'` and `WG = G'W`
  (`thm:physical-source-completeness` (iv), by the explicit Gram
  factorization `W = K'K^H(KK^H)⁻¹`);
* `krylov_reduces` — the cyclic subspace is invariant under the
  self-adjoint transport (clause (i)).
-/

namespace NCG

open Matrix

open scoped ComplexOrder

noncomputable section

variable {u p : Type*} [Fintype u] [Fintype p] [DecidableEq u]

/-- The stacked Krylov (controllability) block matrix
`[S, MS, …, M^{d-1}S]`. -/
def krylovMat (M : Matrix u u ℂ) (S : Matrix u p ℂ) (d : ℕ) :
    Matrix u (Fin d × p) ℂ :=
  Matrix.of fun i nq => (M ^ (nq.1 : ℕ) * S) i nq.2

omit [Fintype p] in
/-- `thm:v5-block-hankel-packet` (Gram form): the block-Hankel
moment matrix is the Gram matrix of the Krylov family (two
horizons). -/
theorem block_hankel_gram (M : Matrix u u ℂ) (S : Matrix u p ℂ)
    (hM : Mᴴ = M) {d e : ℕ} (mq : Fin d × p) (nr : Fin e × p) :
    ((krylovMat M S d)ᴴ * krylovMat M S e) mq nr
      = (Sᴴ * M ^ ((mq.1 : ℕ) + (nr.1 : ℕ)) * S) mq.2 nr.2 := by
  have hpow : ∀ n : ℕ, (M ^ n)ᴴ = M ^ n := by
    intro n
    rw [Matrix.conjTranspose_pow, hM]
  rw [Matrix.mul_apply]
  have hrhs : (Sᴴ * M ^ ((mq.1 : ℕ) + (nr.1 : ℕ)) * S) mq.2 nr.2
      = ((M ^ (mq.1 : ℕ) * S)ᴴ * (M ^ (nr.1 : ℕ) * S))
          mq.2 nr.2 := by
    rw [Matrix.conjTranspose_mul, hpow, pow_add]
    simp only [Matrix.mul_assoc]
  rw [hrhs, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.conjTranspose_apply, Matrix.conjTranspose_apply]
  rfl

/-- `thm:v5-block-hankel-packet` (rank): the rank of the
block-Hankel matrix equals the dimension of the Krylov span. -/
theorem block_hankel_rank (M : Matrix u u ℂ) (S : Matrix u p ℂ)
    (d : ℕ) :
    ((krylovMat M S d)ᴴ * krylovMat M S d).rank
      = Module.finrank ℂ (Submodule.span ℂ
          (Set.range (krylovMat M S d).col)) := by
  rw [Matrix.rank_conjTranspose_mul_self,
    Matrix.rank_eq_finrank_span_cols]

/-- `thm:v5-hankel-descent`: covariant relabellings preserve the
Hankel kernel, act isometrically on the intrinsic source, and the
quotient dimension is `rank H`. -/
theorem hankel_descent {f : Type*} [Fintype f] [DecidableEq f]
    (H : Matrix f p ℂ) (Mg : Matrix f f ℂ) (Lg : Matrix p p ℂ)
    (hcov : Mg * H = H * Lg) (hMg : Mgᴴ * Mg = 1) :
    (∀ v : p → ℂ, H *ᵥ v = 0 → H *ᵥ (Lg *ᵥ v) = 0)
    ∧ (∀ v w : p → ℂ,
        star (H *ᵥ (Lg *ᵥ v)) ⬝ᵥ (H *ᵥ (Lg *ᵥ w))
          = star (H *ᵥ v) ⬝ᵥ (H *ᵥ w))
    ∧ Module.finrank ℂ
        ((p → ℂ) ⧸ LinearMap.ker H.mulVecLin) = H.rank := by
  refine ⟨?_, ?_, ?_⟩
  · intro v hv
    rw [Matrix.mulVec_mulVec, ← hcov, ← Matrix.mulVec_mulVec, hv,
      Matrix.mulVec_zero]
  · intro v w
    have hl : ∀ x : p → ℂ, H *ᵥ (Lg *ᵥ x) = Mg *ᵥ (H *ᵥ x) := by
      intro x
      rw [Matrix.mulVec_mulVec, ← hcov, ← Matrix.mulVec_mulVec]
    rw [hl v, hl w, Matrix.star_mulVec, Matrix.dotProduct_mulVec,
      Matrix.vecMul_vecMul, hMg, Matrix.vecMul_one]
  · have h1 := Submodule.finrank_quotient_add_finrank
      (LinearMap.ker H.mulVecLin)
    have h2 := LinearMap.finrank_range_add_finrank_ker
      H.mulVecLin
    have h3 : H.rank
        = Module.finrank ℂ (LinearMap.range H.mulVecLin) := by
      rw [Matrix.rank_eq_finrank_span_cols,
        Matrix.range_mulVecLin]
    omega


/-- Clause (i) of `thm:physical-source-completeness`: the Krylov
span is invariant under the transport. -/
theorem krylov_reduces (G : Matrix u u ℂ) (B : Matrix u p ℂ)
    (x : u → ℂ)
    (hx : x ∈ Submodule.span ℂ
      (⋃ n : ℕ, Set.range fun v : p → ℂ => (G ^ n * B) *ᵥ v)) :
    G *ᵥ x ∈ Submodule.span ℂ
      (⋃ n : ℕ, Set.range fun v : p → ℂ => (G ^ n * B) *ᵥ v) := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨s, ⟨n, rfl⟩, v, rfl⟩ := hy
    apply Submodule.subset_span
    refine Set.mem_iUnion.mpr ⟨n + 1, ⟨v, ?_⟩⟩
    rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← pow_succ']
  | zero =>
    rw [Matrix.mulVec_zero]
    exact Submodule.zero_mem _
  | add y z _ _ hy hz =>
    rw [Matrix.mulVec_add]
    exact Submodule.add_mem _ hy hz
  | smul t y _ hy =>
    rw [Matrix.mulVec_smul]
    exact Submodule.smul_mem _ _ hy

/-- The zero-block extraction `K·E₀ = B`. -/
lemma krylov_zero_block [DecidableEq p] (M : Matrix u u ℂ)
    (S : Matrix u p ℂ) (d : ℕ) (hd : 0 < d) :
    krylovMat M S d * (Matrix.of fun (nq : Fin d × p) (r : p) =>
      if nq.1 = ⟨0, hd⟩ ∧ nq.2 = r then (1 : ℂ) else 0) = S := by
  ext i r
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (⟨⟨0, hd⟩, r⟩ : Fin d × p)]
  · simp [krylovMat]
  · intro nq _ hnq
    rw [Matrix.of_apply, if_neg, mul_zero]
    intro ⟨h1, h2⟩
    exact hnq (Prod.ext h1 h2)
  · intro hmem
    exact absurd (Finset.mem_univ _) hmem

/-- The shift identity `M·K_d = K_{d+1}·Sh`. -/
lemma krylov_shift [DecidableEq p] (M : Matrix u u ℂ)
    (S : Matrix u p ℂ) (d : ℕ) :
    M * krylovMat M S d
      = krylovMat M S (d + 1)
        * (Matrix.of fun (mr : Fin (d + 1) × p)
            (nq : Fin d × p) =>
          if (mr.1 : ℕ) = (nq.1 : ℕ) + 1 ∧ mr.2 = nq.2
          then (1 : ℂ) else 0) := by
  ext i nq
  have hcollapse : (∑ mr : Fin (d + 1) × p,
      krylovMat M S (d + 1) i mr
        * (Matrix.of fun (mr : Fin (d + 1) × p)
            (nq : Fin d × p) =>
          if (mr.1 : ℕ) = (nq.1 : ℕ) + 1 ∧ mr.2 = nq.2
          then (1 : ℂ) else 0) mr nq)
      = krylovMat M S (d + 1)
          i ⟨⟨(nq.1 : ℕ) + 1, by omega⟩, nq.2⟩ := by
    rw [Finset.sum_eq_single
      (⟨⟨(nq.1 : ℕ) + 1, by omega⟩, nq.2⟩ : Fin (d + 1) × p)]
    · rw [Matrix.of_apply, if_pos ⟨rfl, rfl⟩, mul_one]
    · intro mr _ hmr
      rw [Matrix.of_apply, if_neg, mul_zero]
      intro hpair
      exact hmr (Prod.ext (Fin.ext hpair.1) hpair.2)
    · intro hmem
      exact absurd (Finset.mem_univ _) hmem
  rw [Matrix.mul_apply, Matrix.mul_apply, hcollapse]
  simp only [krylovMat, Matrix.of_apply]
  rw [show M ^ ((nq.1 : ℕ) + 1) * S
      = M * (M ^ (nq.1 : ℕ) * S) from by
    rw [← Matrix.mul_assoc, ← pow_succ']]
  rw [Matrix.mul_apply]

/-- `thm:physical-source-completeness` (iv): two source-minimal
finite triples with identical all-order moments are related by a
unique source-fixing unitary intertwining the transports —
constructed explicitly as `W = K'Kᴴ(KKᴴ)⁻¹`. -/
theorem physical_source_uniqueness
    (G G' : Matrix u u ℂ) (B B' : Matrix u p ℂ)
    (hG : Gᴴ = G) (hG' : G'ᴴ = G')
    (d : ℕ) (hd : 0 < d)
    (hmin : Function.Surjective (krylovMat G B d).mulVec)
    (hmom : ∀ n : ℕ, Bᴴ * G ^ n * B = B'ᴴ * G' ^ n * B') :
    ∃ W : Matrix u u ℂ, Wᴴ * W = 1 ∧ W * B = B'
      ∧ W * G = G' * W := by
  classical
  set K := krylovMat G B d with hK
  set K' := krylovMat G' B' d with hK'
  set Kb := krylovMat G B (d + 1) with hKb
  set Kb' := krylovMat G' B' (d + 1) with hKb'
  -- Gram equality at both horizons
  have hgram : ∀ (e : ℕ), (krylovMat G B e)ᴴ * krylovMat G B e
      = (krylovMat G' B' e)ᴴ * krylovMat G' B' e := by
    intro e
    ext mq nr
    rw [block_hankel_gram G B hG, block_hankel_gram G' B' hG',
      hmom]
  -- positive definiteness of KKᴴ from minimality
  have hPD : (K * Kᴴ).PosDef :=
    ((hodge_cycle_observability K).2.1).mp hmin
  have hdet : IsUnit (K * Kᴴ).det :=
    isUnit_iff_ne_zero.mpr hPD.det_pos.ne'
  have hHerm : (K * Kᴴ)⁻¹ᴴ = (K * Kᴴ)⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv,
      Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  set W : Matrix u u ℂ := K' * Kᴴ * (K * Kᴴ)⁻¹ with hW
  -- the projection onto the Krylov row space
  set P : Matrix (Fin d × p) (Fin d × p) ℂ
    := Kᴴ * (K * Kᴴ)⁻¹ * K with hP
  have hKP : K * P = K := by
    rw [hP, show K * (Kᴴ * (K * Kᴴ)⁻¹ * K)
        = (K * Kᴴ) * (K * Kᴴ)⁻¹ * K from by simp only [Matrix.mul_assoc],
      Matrix.mul_nonsing_inv _ hdet, Matrix.one_mul]
  have hPH : Pᴴ = P := by
    rw [hP, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      hHerm, Matrix.conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
  have hKP' : K' * P = K' := by
    have hzero : (K' * (1 - P))ᴴ * (K' * (1 - P)) = 0 := by
      rw [Matrix.conjTranspose_mul,
        show (1 - P)ᴴ * K'ᴴ * (K' * (1 - P))
          = (1 - P)ᴴ * (K'ᴴ * K') * (1 - P) from by simp only [Matrix.mul_assoc],
        ← hgram d]
      rw [show (1 - P)ᴴ * (Kᴴ * K) * (1 - P)
          = (K * (1 - P))ᴴ * (K * (1 - P)) from by
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]]
      rw [Matrix.mul_sub, Matrix.mul_one, hKP, sub_self,
        Matrix.conjTranspose_zero, Matrix.mul_zero]
    have h0 := Matrix.conjTranspose_mul_self_eq_zero.mp hzero
    rw [Matrix.mul_sub, Matrix.mul_one] at h0
    exact (sub_eq_zero.mp h0).symm
  -- cross-horizon Gram equality
  have hgram2 : Kᴴ * Kb = K'ᴴ * Kb' := by
    ext mq nr
    rw [hK, hKb, hK', hKb', block_hankel_gram G B hG,
      block_hankel_gram G' B' hG', hmom]
  -- unitarity
  have hWu : Wᴴ * W = 1 := by
    rw [hW, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      hHerm, Matrix.conjTranspose_conjTranspose]
    rw [show (K * Kᴴ)⁻¹ * (K * K'ᴴ) * (K' * Kᴴ * (K * Kᴴ)⁻¹)
        = (K * Kᴴ)⁻¹ * (K * (K'ᴴ * K') * Kᴴ) * (K * Kᴴ)⁻¹ from by
      simp only [Matrix.mul_assoc], ← hgram d]
    rw [show (K * Kᴴ)⁻¹ * (K * (Kᴴ * K) * Kᴴ) * (K * Kᴴ)⁻¹
        = ((K * Kᴴ)⁻¹ * (K * Kᴴ)) * ((K * Kᴴ) * (K * Kᴴ)⁻¹)
        from by simp only [Matrix.mul_assoc],
      Matrix.nonsing_inv_mul _ hdet,
      Matrix.mul_nonsing_inv _ hdet, Matrix.one_mul]
  -- W maps the Krylov data
  have hWK : W * K = K' := by
    rw [hW, show K' * Kᴴ * (K * Kᴴ)⁻¹ * K = K' * P from by
      rw [hP]
      simp only [Matrix.mul_assoc], hKP']
  have hWB : W * B = B' := by
    have hEB := krylov_zero_block G B d hd
    have hEB' := krylov_zero_block G' B' d hd
    rw [← hEB, ← hEB', ← Matrix.mul_assoc, hWK]
  -- W agrees on the extended Krylov data
  have hWHKb : Wᴴ * Kb' = Kb := by
    rw [hW, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      hHerm, Matrix.conjTranspose_conjTranspose]
    rw [show (K * Kᴴ)⁻¹ * (K * K'ᴴ) * Kb'
        = (K * Kᴴ)⁻¹ * (K * (K'ᴴ * Kb')) from by
      simp only [Matrix.mul_assoc], ← hgram2,
      show (K * Kᴴ)⁻¹ * (K * (Kᴴ * Kb))
        = ((K * Kᴴ)⁻¹ * (K * Kᴴ)) * Kb from by
      simp only [Matrix.mul_assoc],
      Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]
  have hWKb : W * Kb = Kb' := by
    have hzero : (W * Kb - Kb')ᴴ * (W * Kb - Kb') = 0 := by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul,
        Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
      rw [show Kbᴴ * Wᴴ * (W * Kb)
          = Kbᴴ * (Wᴴ * W) * Kb from by simp only [Matrix.mul_assoc], hWu]
      rw [show Kbᴴ * Wᴴ * Kb' = Kbᴴ * (Wᴴ * Kb') from
        Matrix.mul_assoc _ _ _, hWHKb]
      rw [show Kb'ᴴ * (W * Kb) = (Wᴴ * Kb')ᴴ * Kb from by
        rw [Matrix.conjTranspose_mul,
          Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc,
          hW]
        simp only [Matrix.mul_assoc], hWHKb]
      rw [← hgram (d + 1), ← hKb,
        show Kbᴴ * (1 : Matrix u u ℂ) * Kb = Kbᴴ * Kb from by
          rw [Matrix.mul_one]]
      abel
    have h0 := Matrix.conjTranspose_mul_self_eq_zero.mp hzero
    exact sub_eq_zero.mp h0
  -- intertwining
  have hshiftK := krylov_shift G B d
  have hshiftK' := krylov_shift G' B' d
  have hint : (W * G - G' * W) * K = 0 := by
    rw [Matrix.sub_mul]
    rw [show W * G * K = W * (G * K) from Matrix.mul_assoc _ _ _,
      hshiftK, ← Matrix.mul_assoc, hWKb]
    rw [show G' * W * K = G' * (W * K) from Matrix.mul_assoc _ _ _,
      hWK, hshiftK']
    rw [sub_self]
  have hfinal : W * G - G' * W = 0 := by
    have h1 : (W * G - G' * W) * K * Kᴴ * (K * Kᴴ)⁻¹ = 0 := by
      rw [hint, Matrix.zero_mul, Matrix.zero_mul]
    rw [show (W * G - G' * W) * K * Kᴴ * (K * Kᴴ)⁻¹
        = (W * G - G' * W) * ((K * Kᴴ) * (K * Kᴴ)⁻¹) from by
      simp only [Matrix.mul_assoc], Matrix.mul_nonsing_inv _ hdet,
      Matrix.mul_one] at h1
    exact h1
  exact ⟨W, hWu, hWB, sub_eq_zero.mp hfinal⟩

end

end NCG
