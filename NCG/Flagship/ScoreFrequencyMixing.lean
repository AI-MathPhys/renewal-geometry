/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Exact score-frequency mixing identity
  (`thm:score-frequency-mixing-master`, flagship manuscript)

For the loaded Store operator `K = Σ_j λ_je_j` (orthogonal
Hermitian spectral projections `e_j`, real values `λ_j`) and any
`A` on the finite carrier:

* the boxed mixing identity
  `‖[K,A]‖²_HS = Σ_{j,k}(λ_j-λ_k)²‖e_jAe_k‖²_HS`
  (`score_mixing_hs`), via the block formula
  `e_j[K,A]e_k = (λ_j-λ_k)e_jAe_k` and Hilbert–Schmidt
  orthogonality of the spectral blocks;
* the boxed zero criterion: for distinct loaded values,
  `[K,A] = 0 ↔ A = Σ_je_jAe_j` (`score_mixing_zero`);
* the boxed cluster-leakage estimate: for a partition of the
  labels with spectral gap `Δ` between clusters,
  `Δ²‖A - Σ_CE_CAE_C‖²_HS ≤ ‖[K,A]‖²_HS`
  (`score_cluster_leakage`, stated in squared form to avoid
  square roots — equivalent to the boxed bound; disclosed).

Self-adjointness of `A` is not needed for these identities and is
not assumed (disclosed).
-/

open Matrix Finset

namespace NCG

variable {d : Type*} [Fintype d] [DecidableEq d] {s : ℕ}
  (e : Fin s → Matrix d d ℂ) (lam : Fin s → ℝ)
  (A : Matrix d d ℂ)

omit [DecidableEq d] in
/-- Expansion of the Hilbert–Schmidt square of a real-coefficient
combination of HS-orthogonal matrices. -/
lemma hs_expansion {ι : Type*} [Fintype ι] (M : ι → Matrix d d ℂ)
    (c : ι → ℝ)
    (horthHS : ∀ p q, p ≠ q → ((M p)ᴴ * M q).trace = 0) :
    ((∑ p, ((c p : ℂ)) • M p)ᴴ * (∑ q, ((c q : ℂ)) • M q)).trace
      = ∑ p, ((c p : ℂ)) ^ 2 * ((M p)ᴴ * M p).trace := by
  rw [Matrix.conjTranspose_sum]
  rw [Finset.sum_congr rfl fun p _ => by
    rw [Matrix.conjTranspose_smul, Complex.star_def,
      Complex.conj_ofReal]]
  rw [Finset.sum_mul, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl fun q _ => by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]]
  rw [Matrix.trace_sum]
  rw [Finset.sum_congr rfl fun q _ => Matrix.trace_smul _ _]
  rw [Finset.sum_eq_single p (fun q _ hqp => by
      rw [horthHS p q (Ne.symm hqp), smul_zero])
    (fun h => absurd (mem_univ p) h)]
  rw [smul_eq_mul]
  ring

section Mixing

/-- The loaded Store operator `K = Σ_j λ_je_j`. -/
noncomputable def loadedK : Matrix d d ℂ :=
  ∑ j, ((lam j : ℂ)) • e j

omit [DecidableEq d] in
/-- `e_jK = λ_je_j`. -/
lemma proj_mul_loadedK
    (horth : ∀ i j, e i * e j = if i = j then e i else 0)
    (j : Fin s) :
    e j * loadedK e lam = (lam j : ℂ) • e j := by
  rw [loadedK, Finset.mul_sum]
  rw [Finset.sum_congr rfl fun l _ => by
    rw [Matrix.mul_smul, horth j l]]
  rw [Finset.sum_eq_single j (fun l _ hlj => by
      rw [if_neg (Ne.symm hlj), smul_zero])
    (fun h => absurd (mem_univ j) h)]
  rw [if_pos rfl]

omit [DecidableEq d] in
/-- `Ke_k = λ_ke_k`. -/
lemma loadedK_mul_proj
    (horth : ∀ i j, e i * e j = if i = j then e i else 0)
    (k : Fin s) :
    loadedK e lam * e k = (lam k : ℂ) • e k := by
  rw [loadedK, Finset.sum_mul]
  rw [Finset.sum_congr rfl fun l _ => by
    rw [Matrix.smul_mul, horth l k]]
  rw [Finset.sum_eq_single k (fun l _ hlk => by
      rw [if_neg hlk, smul_zero])
    (fun h => absurd (mem_univ k) h)]
  rw [if_pos rfl]

omit [DecidableEq d] in
/-- Boxed block formula: `e_j[K,A]e_k = (λ_j-λ_k)e_jAe_k`. -/
lemma commutator_block
    (horth : ∀ i j, e i * e j = if i = j then e i else 0)
    (j k : Fin s) :
    e j * (loadedK e lam * A - A * loadedK e lam) * e k
      = (((lam j - lam k : ℝ) : ℂ)) • (e j * A * e k) := by
  rw [Matrix.mul_sub, Matrix.sub_mul]
  rw [show e j * (loadedK e lam * A) = (e j * loadedK e lam) * A from
    (Matrix.mul_assoc _ _ _).symm,
    proj_mul_loadedK e lam horth j]
  rw [show e j * (A * loadedK e lam) * e k
      = (e j * A) * (loadedK e lam * e k) from by
    simp only [Matrix.mul_assoc],
    loadedK_mul_proj e lam horth k]
  rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul]
  rw [show (((lam j - lam k : ℝ) : ℂ))
      = ((lam j : ℂ)) - ((lam k : ℂ)) from by push_cast; ring,
    sub_smul]

/-- Any `X` decomposes into its spectral blocks. -/
lemma block_decomposition (hsum : ∑ j, e j = 1)
    (X : Matrix d d ℂ) :
    X = ∑ j, ∑ k, e j * X * e k := by
  have h : X = (∑ j, e j) * X * (∑ k, e k) := by
    rw [hsum, Matrix.one_mul, Matrix.mul_one]
  conv_lhs => rw [h]
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]

omit [DecidableEq d] in
/-- Distinct spectral blocks are Hilbert–Schmidt orthogonal. -/
lemma block_hs_orthogonal
    (horth : ∀ i j, e i * e j = if i = j then e i else 0)
    (hherm : ∀ j, (e j)ᴴ = e j)
    (X Y : Matrix d d ℂ) (j k l m : Fin s)
    (hne : j ≠ l ∨ k ≠ m) :
    ((e j * X * e k)ᴴ * (e l * Y * e m)).trace = 0 := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    hherm j, hherm k]
  rcases hne with hjl | hkm
  · rw [show e k * (Xᴴ * e j) * (e l * Y * e m)
        = e k * Xᴴ * (e j * e l) * (Y * e m) from by
      simp only [Matrix.mul_assoc],
      horth j l, if_neg hjl, Matrix.mul_zero, Matrix.zero_mul,
      Matrix.trace_zero]
  · rw [Matrix.trace_mul_comm]
    rw [show e l * Y * e m * (e k * (Xᴴ * e j))
        = e l * Y * (e m * e k) * (Xᴴ * e j) from by
      simp only [Matrix.mul_assoc],
      horth m k, if_neg (Ne.symm hkm), Matrix.mul_zero,
      Matrix.zero_mul, Matrix.trace_zero]

/-- The commutator as a real-coefficient block combination over
the product index. -/
lemma commutator_decomposition
    (horth : ∀ i j, e i * e j = if i = j then e i else 0)
    (hsum : ∑ j, e j = 1) :
    loadedK e lam * A - A * loadedK e lam
      = ∑ p : Fin s × Fin s,
          (((lam p.1 - lam p.2 : ℝ) : ℂ))
            • (e p.1 * A * e p.2) := by
  rw [Fintype.sum_prod_type]
  calc loadedK e lam * A - A * loadedK e lam
      = ∑ j, ∑ k, e j * (loadedK e lam * A - A * loadedK e lam)
          * e k := block_decomposition e hsum _
    _ = _ := by
        refine Finset.sum_congr rfl fun j _ => ?_
        exact Finset.sum_congr rfl fun k _ =>
          commutator_block e lam A horth j k

/-- `thm:score-frequency-mixing-master`, boxed mixing identity:
`‖[K,A]‖²_HS = Σ_{j,k}(λ_j-λ_k)²‖e_jAe_k‖²_HS`. -/
theorem score_mixing_hs
    (horth : ∀ i j, e i * e j = if i = j then e i else 0)
    (hherm : ∀ j, (e j)ᴴ = e j)
    (hsum : ∑ j, e j = 1) :
    ((loadedK e lam * A - A * loadedK e lam)ᴴ
      * (loadedK e lam * A - A * loadedK e lam)).trace
      = ∑ j, ∑ k, (((lam j - lam k : ℝ) : ℂ)) ^ 2
        * ((e j * A * e k)ᴴ * (e j * A * e k)).trace := by
  rw [commutator_decomposition e lam A horth hsum]
  rw [hs_expansion (fun p : Fin s × Fin s => e p.1 * A * e p.2)
    (fun p => lam p.1 - lam p.2)
    (fun p q hpq => block_hs_orthogonal e horth hherm A A
      p.1 p.2 q.1 q.2 (by
        by_contra hcon
        rw [not_or, not_not, not_not] at hcon
        exact hpq (Prod.ext hcon.1 hcon.2)))]
  rw [Fintype.sum_prod_type]

/-- `thm:score-frequency-mixing-master`, boxed zero criterion:
for distinct loaded values, `[K,A] = 0 ↔ A = Σ_je_jAe_j`. -/
theorem score_mixing_zero
    (horth : ∀ i j, e i * e j = if i = j then e i else 0)
    (hsum : ∑ j, e j = 1)
    (hinj : Function.Injective lam) :
    loadedK e lam * A - A * loadedK e lam = 0
      ↔ A = ∑ j, e j * A * e j := by
  constructor
  · intro h0
    have hblocks : ∀ j k, j ≠ k → e j * A * e k = 0 := by
      intro j k hjk
      have hb := commutator_block e lam A horth j k
      rw [h0, Matrix.mul_zero, Matrix.zero_mul] at hb
      have hcoeff : (((lam j - lam k : ℝ) : ℂ)) ≠ 0 := by
        rw [Complex.ofReal_ne_zero, sub_ne_zero]
        exact fun h => hjk (hinj h)
      exact ((smul_eq_zero.mp hb.symm).resolve_left hcoeff)
    calc A = ∑ j, ∑ k, e j * A * e k := block_decomposition e hsum A
      _ = ∑ j, e j * A * e j := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_eq_single j
            (fun k _ hkj => hblocks j k (Ne.symm hkj))
            (fun h => absurd (mem_univ j) h)]
  · intro hA
    conv_lhs => rw [hA]
    rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [show loadedK e lam * (e j * A * e j)
        = (loadedK e lam * e j) * (A * e j) from by
      simp only [Matrix.mul_assoc],
      loadedK_mul_proj e lam horth j,
      show e j * A * e j * loadedK e lam
        = (e j * A) * (e j * loadedK e lam) from by
      simp only [Matrix.mul_assoc],
      proj_mul_loadedK e lam horth j,
      Matrix.smul_mul, Matrix.mul_smul]
    rw [sub_eq_zero]
    congr 1
    simp only [Matrix.mul_assoc]

/-! ### Cluster leakage -/

variable {γ : Type*} [Fintype γ] [DecidableEq γ]

/-- The cluster projections `E_C = Σ_{cl(j)=C} e_j`. -/
noncomputable def clusterProj (cl : Fin s → γ) (C : γ) :
    Matrix d d ℂ :=
  ∑ j, if cl j = C then e j else 0

/-- The cluster complement is the sum of the cross-cluster
blocks. -/
lemma cluster_complement (hsum : ∑ j, e j = 1)
    (cl : Fin s → γ) :
    A - ∑ C, clusterProj e cl C * A * clusterProj e cl C
      = ∑ p : Fin s × Fin s,
          ((((if cl p.1 = cl p.2 then 0 else 1 : ℝ)) : ℂ))
            • (e p.1 * A * e p.2) := by
  have hdiag : ∑ C, clusterProj e cl C * A * clusterProj e cl C
      = ∑ p : Fin s × Fin s,
          ((((if cl p.1 = cl p.2 then 1 else 0 : ℝ)) : ℂ))
            • (e p.1 * A * e p.2) := by
    have hCform : ∀ C, clusterProj e cl C * A * clusterProj e cl C
        = ∑ j, ∑ k, if cl j = C then
            (if cl k = C then e j * A * e k else 0) else 0 := by
      intro C
      rw [clusterProj, Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hj : cl j = C <;> by_cases hk : cl k = C <;>
        simp [hj, hk]
    rw [Finset.sum_congr rfl fun C _ => hCform C]
    rw [Finset.sum_comm, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_eq_single (cl j)
      (fun C _ hC => by rw [if_neg (fun h => hC h.symm)])
      (fun h => absurd (mem_univ (cl j)) h)]
    rw [if_pos rfl]
    by_cases hk : cl j = cl k
    · rw [if_pos hk.symm, if_pos hk]
      simp
    · rw [if_neg (fun h => hk h.symm), if_neg hk]
      simp
  rw [hdiag]
  nth_rewrite 1 [show A = ∑ p : Fin s × Fin s,
    e p.1 * A * e p.2 from by
      rw [Fintype.sum_prod_type]
      exact block_decomposition e hsum A]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hp : cl p.1 = cl p.2 <;> simp [hp]

/-- `thm:score-frequency-mixing-master`, boxed cluster-leakage
estimate in squared form:
`Δ²‖A - Σ_CE_CAE_C‖²_HS ≤ ‖[K,A]‖²_HS`. -/
theorem score_cluster_leakage
    (horth : ∀ i j, e i * e j = if i = j then e i else 0)
    (hherm : ∀ j, (e j)ᴴ = e j)
    (hsum : ∑ j, e j = 1)
    (cl : Fin s → γ) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hgap : ∀ j k, cl j ≠ cl k → Δ ≤ |lam j - lam k|) :
    Δ ^ 2 * (((A - ∑ C, clusterProj e cl C * A * clusterProj e cl C)ᴴ
        * (A - ∑ C, clusterProj e cl C * A * clusterProj e cl C)).trace).re
      ≤ (((loadedK e lam * A - A * loadedK e lam)ᴴ
        * (loadedK e lam * A - A * loadedK e lam)).trace).re := by
  rw [cluster_complement e A hsum cl,
    commutator_decomposition e lam A horth hsum]
  rw [hs_expansion (fun p : Fin s × Fin s => e p.1 * A * e p.2)
    (fun p => if cl p.1 = cl p.2 then (0 : ℝ) else 1)
    (fun p q hpq => block_hs_orthogonal e horth hherm A A
      p.1 p.2 q.1 q.2 (by
        by_contra hcon
        rw [not_or, not_not, not_not] at hcon
        exact hpq (Prod.ext hcon.1 hcon.2))),
    hs_expansion (fun p : Fin s × Fin s => e p.1 * A * e p.2)
    (fun p => lam p.1 - lam p.2)
    (fun p q hpq => block_hs_orthogonal e horth hherm A A
      p.1 p.2 q.1 q.2 (by
        by_contra hcon
        rw [not_or, not_not, not_not] at hcon
        exact hpq (Prod.ext hcon.1 hcon.2)))]
  rw [Complex.re_sum, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun p _ => ?_
  have hre : ∀ (r : ℝ) (τ : ℂ),
      (((r : ℂ)) ^ 2 * τ).re = r ^ 2 * τ.re := by
    intro r τ
    rw [show ((r : ℂ)) ^ 2 = ((r ^ 2 : ℝ) : ℂ) from by
      push_cast; ring, Complex.re_ofReal_mul]
  rw [hre, hre]
  have hτ : 0 ≤ (((e p.1 * A * e p.2)ᴴ
      * (e p.1 * A * e p.2)).trace).re := by
    open scoped ComplexOrder in
    have h0 := (Matrix.posSemidef_conjTranspose_mul_self
      (e p.1 * A * e p.2)).trace_nonneg
    exact (Complex.nonneg_iff.mp h0).1
  by_cases hp : cl p.1 = cl p.2
  · rw [if_pos hp]
    have h1 : Δ ^ 2 * ((0 : ℝ) ^ 2 * (((e p.1 * A * e p.2)ᴴ
        * (e p.1 * A * e p.2)).trace).re) = 0 := by ring
    rw [h1]
    exact mul_nonneg (sq_nonneg _) hτ
  · rw [if_neg hp]
    have hd2 : Δ ^ 2 ≤ (lam p.1 - lam p.2) ^ 2 := by
      have h1 := hgap p.1 p.2 hp
      calc Δ ^ 2 ≤ |lam p.1 - lam p.2| ^ 2 :=
            pow_le_pow_left₀ hΔ h1 2
        _ = (lam p.1 - lam p.2) ^ 2 := sq_abs _
    calc Δ ^ 2 * ((1 : ℝ) ^ 2 * (((e p.1 * A * e p.2)ᴴ
          * (e p.1 * A * e p.2)).trace).re)
        = Δ ^ 2 * (((e p.1 * A * e p.2)ᴴ
          * (e p.1 * A * e p.2)).trace).re := by ring
      _ ≤ (lam p.1 - lam p.2) ^ 2 * (((e p.1 * A * e p.2)ᴴ
          * (e p.1 * A * e p.2)).trace).re :=
          mul_le_mul_of_nonneg_right hd2 hτ

end Mixing

end NCG
