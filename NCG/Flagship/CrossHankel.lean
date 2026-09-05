/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Upstream.KalmanRealization

/-!
# Cross-Hankel chronology theorem
  (`thm:clock-geometry-cross-Hankel-master`, flagship manuscript)

With the depth-`d` history syntheses `𝒱^a = [S_a, TS_a, …]`
realized by `krylovMat`:

* the cross-Hankel window is the Gram of the two history families,
  `(𝗛^{ab})_{(i,q),(j,r)} = (S_a* T^{i+j} S_b)_{qr}`
  (`cross_hankel_gram`);
* with the clock-packet projection `Π = K(K*K)⁻¹K*` (Hermitian
  idempotent fixing the clock histories, `clock_proj_props`), the
  boxed Schur identity
  `𝔾 = 𝗛^{gg} - (𝗛^{cg})*(𝗛^{cc})⁻¹𝗛^{cg} = ((1-Π)𝒱^g)*((1-Π)𝒱^g)`
  holds (`cross_hankel_schur`), hence `𝔾 ⪰ 0`
  (`cross_hankel_psd`) and `rank 𝔾 = rank((1-Π)𝒱^g)` — the number
  of additional geometry-history directions
  (`cross_hankel_rank`);
* boxed reconstruction: if `𝔾 = 0` then
  `S_geo = Σ_{n<d} Tⁿ S_clk R_n` with the coefficients given by
  the inverse of `𝗛^{cc}` applied to `𝗛^{cg}`
  (`cross_hankel_reconstruction`).

The Moore–Penrose convention of the manuscript enters through the
nondegeneracy hypothesis `𝗛^{cc} ≻ 0` (independent clock
histories), under which `(𝗛^{cc})† = (𝗛^{cc})⁻¹` (disclosed);
minimality of the chronology degree `d` is its definition
(prose).
-/

open Matrix
open scoped ComplexOrder

namespace NCG

variable {u p q : Type*} [Fintype u] [Fintype p] [Fintype q]
  [DecidableEq u] [DecidableEq p] [DecidableEq q]

omit [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q] in
/-- Cross-Hankel Gram: the window `𝗛^{ab}` is the Gram matrix of
the two history families. -/
theorem cross_hankel_gram (T : Matrix u u ℂ) (hT : Tᴴ = T)
    (Sa : Matrix u p ℂ) (Sb : Matrix u q ℂ) {d e : ℕ}
    (mq : Fin d × p) (nr : Fin e × q) :
    ((krylovMat T Sa d)ᴴ * krylovMat T Sb e) mq nr
      = (Saᴴ * T ^ ((mq.1 : ℕ) + (nr.1 : ℕ)) * Sb) mq.2 nr.2 := by
  have hpow : ∀ n : ℕ, (T ^ n)ᴴ = T ^ n := by
    intro n
    rw [Matrix.conjTranspose_pow, hT]
  rw [Matrix.mul_apply]
  have hrhs : (Saᴴ * T ^ ((mq.1 : ℕ) + (nr.1 : ℕ)) * Sb) mq.2 nr.2
      = ((T ^ (mq.1 : ℕ) * Sa)ᴴ * (T ^ (nr.1 : ℕ) * Sb))
          mq.2 nr.2 := by
    rw [Matrix.conjTranspose_mul, hpow, pow_add]
    simp only [Matrix.mul_assoc]
  rw [hrhs, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.conjTranspose_apply, Matrix.conjTranspose_apply]
  rfl

section Schur

variable (T : Matrix u u ℂ) (Sc : Matrix u p ℂ) (Sg : Matrix u q ℂ)
  (d : ℕ)

/-- The clock-packet projection `Π = K(K*K)⁻¹K*`. -/
noncomputable def clockPacketProj : Matrix u u ℂ :=
  krylovMat T Sc d
    * ((krylovMat T Sc d)ᴴ * krylovMat T Sc d)⁻¹
    * (krylovMat T Sc d)ᴴ

/-- The clock-packet projection is a Hermitian idempotent fixing
the clock histories. -/
theorem clock_proj_props
    (hPD : ((krylovMat T Sc d)ᴴ * krylovMat T Sc d).PosDef) :
    (clockPacketProj T Sc d)ᴴ = clockPacketProj T Sc d
    ∧ clockPacketProj T Sc d * clockPacketProj T Sc d
        = clockPacketProj T Sc d
    ∧ clockPacketProj T Sc d * krylovMat T Sc d
        = krylovMat T Sc d := by
  set K := krylovMat T Sc d with hK
  have hdet : IsUnit ((Kᴴ * K).det) :=
    isUnit_iff_ne_zero.mpr hPD.det_pos.ne'
  have hHerm : ((Kᴴ * K)⁻¹)ᴴ = (Kᴴ * K)⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  have hQK : clockPacketProj T Sc d * K = K := by
    rw [clockPacketProj, ← hK,
      show K * (Kᴴ * K)⁻¹ * Kᴴ * K = K * ((Kᴴ * K)⁻¹ * (Kᴴ * K))
        from by simp only [Matrix.mul_assoc],
      Matrix.nonsing_inv_mul _ hdet, Matrix.mul_one]
  refine ⟨?_, ?_, hQK⟩
  · rw [clockPacketProj, ← hK, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_mul, hHerm,
      Matrix.conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
  · rw [show clockPacketProj T Sc d * clockPacketProj T Sc d
        = (clockPacketProj T Sc d * K) * ((Kᴴ * K)⁻¹ * Kᴴ)
        from by rw [clockPacketProj, ← hK]; simp only [Matrix.mul_assoc],
      hQK, clockPacketProj, ← hK]
    simp only [Matrix.mul_assoc]

omit [Fintype q] [DecidableEq q] in
/-- Boxed Schur identity: the geometry-outside-clock window is
the Gram of the projected-out geometry histories. -/
theorem cross_hankel_schur
    (hPD : ((krylovMat T Sc d)ᴴ * krylovMat T Sc d).PosDef) :
    (krylovMat T Sg d)ᴴ * krylovMat T Sg d
      - ((krylovMat T Sc d)ᴴ * krylovMat T Sg d)ᴴ
        * ((krylovMat T Sc d)ᴴ * krylovMat T Sc d)⁻¹
        * ((krylovMat T Sc d)ᴴ * krylovMat T Sg d)
      = ((1 - clockPacketProj T Sc d) * krylovMat T Sg d)ᴴ
        * ((1 - clockPacketProj T Sc d) * krylovMat T Sg d) := by
  obtain ⟨hQH, hQQ, _⟩ := clock_proj_props T Sc d hPD
  set K := krylovMat T Sc d with hK
  set V := krylovMat T Sg d with hV
  have hoQH : (1 - clockPacketProj T Sc d)ᴴ
      = 1 - clockPacketProj T Sc d := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hQH]
  have hoQQ : (1 - clockPacketProj T Sc d)
      * (1 - clockPacketProj T Sc d)
      = 1 - clockPacketProj T Sc d := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
      Matrix.mul_one, hQQ]
    abel
  calc Vᴴ * V - (Kᴴ * V)ᴴ * (Kᴴ * K)⁻¹ * (Kᴴ * V)
      = Vᴴ * ((1 - clockPacketProj T Sc d) * V) := by
        rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub,
          Matrix.conjTranspose_mul,
          Matrix.conjTranspose_conjTranspose, clockPacketProj,
          ← hK]
        simp only [Matrix.mul_assoc]
    _ = Vᴴ * (((1 - clockPacketProj T Sc d)
          * (1 - clockPacketProj T Sc d)) * V) := by
        rw [hoQQ]
    _ = ((1 - clockPacketProj T Sc d) * V)ᴴ
          * ((1 - clockPacketProj T Sc d) * V) := by
        rw [Matrix.conjTranspose_mul, hoQH]
        simp only [Matrix.mul_assoc]

omit [Fintype q] [DecidableEq q] in
/-- `𝔾 ⪰ 0`. -/
theorem cross_hankel_psd [Finite q]
    (hPD : ((krylovMat T Sc d)ᴴ * krylovMat T Sc d).PosDef) :
    ((krylovMat T Sg d)ᴴ * krylovMat T Sg d
      - ((krylovMat T Sc d)ᴴ * krylovMat T Sg d)ᴴ
        * ((krylovMat T Sc d)ᴴ * krylovMat T Sc d)⁻¹
        * ((krylovMat T Sc d)ᴴ * krylovMat T Sg d)).PosSemidef := by
  rw [cross_hankel_schur T Sc Sg d hPD]
  exact Matrix.posSemidef_conjTranspose_mul_self _

omit [DecidableEq q] in
/-- `rank 𝔾` counts the additional geometry-history
directions. -/
theorem cross_hankel_rank
    (hPD : ((krylovMat T Sc d)ᴴ * krylovMat T Sc d).PosDef) :
    ((krylovMat T Sg d)ᴴ * krylovMat T Sg d
      - ((krylovMat T Sc d)ᴴ * krylovMat T Sg d)ᴴ
        * ((krylovMat T Sc d)ᴴ * krylovMat T Sc d)⁻¹
        * ((krylovMat T Sc d)ᴴ * krylovMat T Sg d)).rank
      = ((1 - clockPacketProj T Sc d) * krylovMat T Sg d).rank := by
  rw [cross_hankel_schur T Sc Sg d hPD,
    Matrix.rank_conjTranspose_mul_self]

omit [Fintype q] [DecidableEq p] [DecidableEq q] in
/-- Block expansion of a Krylov product. -/
lemma krylov_block_expand (W : Matrix (Fin d × p) q ℂ) :
    krylovMat T Sc d * W
      = ∑ n : Fin d, T ^ (n : ℕ) * Sc
          * Matrix.of fun (a : p) (y : q) => W (n, a) y := by
  ext i y
  rw [Matrix.mul_apply, Matrix.sum_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.mul_apply, krylovMat]
  simp only [Matrix.of_apply]
  rw [Matrix.mul_apply]

omit [Fintype p] [DecidableEq p] in
/-- Extracting the zero block of a coefficient matrix. -/
lemma mul_zero_block (R : Matrix (Fin d × p) (Fin d × q) ℂ)
    (hd : 0 < d) (w : Fin d × p) (y : q) :
    (R * (Matrix.of fun (nq : Fin d × q) (r : q) =>
        if nq.1 = ⟨0, hd⟩ ∧ nq.2 = r then (1 : ℂ) else 0)) w y
      = R w (⟨0, hd⟩, y) := by
  rw [Matrix.mul_apply,
    Finset.sum_eq_single (⟨⟨0, hd⟩, y⟩ : Fin d × q)]
  · simp
  · intro nq _ hnq
    rw [Matrix.of_apply, if_neg, mul_zero]
    intro ⟨h1, h2⟩
    exact hnq (Prod.ext h1 h2)
  · intro hmem
    exact absurd (Finset.mem_univ _) hmem

omit [Fintype q] [DecidableEq q] in
/-- Boxed reconstruction: a vanishing cross-Hankel residual
recovers the geometry source as a clock-history polynomial with
coefficients from `(𝗛^{cc})⁻¹𝗛^{cg}`. -/
theorem cross_hankel_reconstruction [Finite q]
    (hPD : ((krylovMat T Sc d)ᴴ * krylovMat T Sc d).PosDef)
    (hd : 0 < d)
    (hvan : (krylovMat T Sg d)ᴴ * krylovMat T Sg d
      - ((krylovMat T Sc d)ᴴ * krylovMat T Sg d)ᴴ
        * ((krylovMat T Sc d)ᴴ * krylovMat T Sc d)⁻¹
        * ((krylovMat T Sc d)ᴴ * krylovMat T Sg d) = 0) :
    Sg = ∑ n : Fin d, T ^ (n : ℕ) * Sc
      * Matrix.of fun (a : p) (y : q) =>
          (((krylovMat T Sc d)ᴴ * krylovMat T Sc d)⁻¹
            * ((krylovMat T Sc d)ᴴ * krylovMat T Sg d))
          (n, a) (⟨0, hd⟩, y) := by
  haveI := Fintype.ofFinite q
  classical
  set K := krylovMat T Sc d with hK
  set V := krylovMat T Sg d with hV
  set R : Matrix (Fin d × p) (Fin d × q) ℂ
    := (Kᴴ * K)⁻¹ * (Kᴴ * V) with hR
  have hzero : (1 - clockPacketProj T Sc d) * V = 0 := by
    have h := hvan
    rw [cross_hankel_schur T Sc Sg d hPD] at h
    exact Matrix.conjTranspose_mul_self_eq_zero.mp h
  have hVQ : V = K * R := by
    have h1 : V - clockPacketProj T Sc d * V = 0 := by
      have h := hzero
      rwa [Matrix.sub_mul, Matrix.one_mul] at h
    have h2 : V = clockPacketProj T Sc d * V := sub_eq_zero.mp h1
    rw [h2, clockPacketProj, ← hK, hR]
    simp only [Matrix.mul_assoc]
  have hSg : Sg = V * (Matrix.of fun (nq : Fin d × q) (r : q) =>
      if nq.1 = ⟨0, hd⟩ ∧ nq.2 = r then (1 : ℂ) else 0) := by
    rw [hV, krylov_zero_block T Sg d hd]
  rw [hSg, hVQ, Matrix.mul_assoc, krylov_block_expand]
  refine Finset.sum_congr rfl fun n _ => ?_
  congr 1
  ext a y
  simp only [Matrix.of_apply]
  rw [mul_zero_block]

end Schur

end NCG
