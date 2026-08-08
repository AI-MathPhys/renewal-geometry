/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FlowDuality
import NCG.Grand.BoundaryCorner

/-!
# Final conditional panels I: provenance, Möbius, hierarchy,
  endpoint, and Hodge records (Gran-Tensor manuscript;
  `thm:provenance-aware-connected-short`,
  `thm:conditional-Mobius-support`,
  `thm:conditional-score-panel-export`,
  `cor:S4-provenance-isotypic`,
  `prop:endpoint-capacity-reconstruction`,
  `thm:endpoint-refinement-coequalizer`,
  `thm:hierarchy-linear-router-distinction`,
  `thm:hierarchy-electrical-router`,
  `thm:collision-parity-Hodge`,
  `thm:global-spatial-compiler`)

Formal cores, each cited in its ledger record with the
manuscript's remaining bookkeeping disclosed there.
-/

open Matrix Finset

namespace NCG

/-- Provenance short: two Hermitian idempotents with orthogonal
ranges sum to the projector onto the direct sum. -/
theorem orthogonal_projection_sum {n : Type*} [Fintype n]
    (P Q : Matrix n n ℂ) (hP : P * P = P) (hQ : Q * Q = Q)
    (hPQ : P * Q = 0) (hQP : Q * P = 0) :
    (P + Q) * (P + Q) = P + Q := by
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, hP, hQ,
    hPQ, hQP]
  abel

/-- Möbius pair inversion: the exact-support block is the
alternating sum of the conditional blocks (pair level). -/
theorem mobius_pair_inversion {E : Type*} [AddCommGroup E]
    (mEmpty ma mb mab C0 Ca Cb Cab : E)
    (hab : mab = C0 + Ca + Cb + Cab) (haa : ma = C0 + Ca)
    (hbb : mb = C0 + Cb) (h0 : mEmpty = C0) :
    Cab = mab - ma - mb + mEmpty := by
  rw [hab, haa, hbb, h0]
  abel

/-- Coarse-score export: the coarse law's derivative is the
fiber sum of the record derivatives. -/
theorem coarse_score_derivative {Ω : Type*}
    (fiber : Finset Ω) (p : ℝ → Ω → ℝ) (d : Ω → ℝ)
    (hp : ∀ ω ∈ fiber, HasDerivAt (fun θ => p θ ω) (d ω) 0) :
    HasDerivAt (fun θ => ∑ ω ∈ fiber, p θ ω)
      (∑ ω ∈ fiber, d ω) 0 := by
  have h := HasDerivAt.sum (u := fiber)
    (fun ω hω => hp ω hω)
  have heq : (∑ ω ∈ fiber, fun θ => p θ ω)
      = fun θ => ∑ ω ∈ fiber, p θ ω := by
    funext θ
    simp [Finset.sum_apply]
  rw [heq] at h
  exact h

/-- Tetrahedral provenance projector: the normalized rank-one
synthesis is idempotent. -/
theorem rank_one_projector_idempotent {n : Type*} [Fintype n]
    (p : n → ℂ) (hp : star p ⬝ᵥ p ≠ 0) :
    ((star p ⬝ᵥ p)⁻¹ • Matrix.vecMulVec p (star p))
        * ((star p ⬝ᵥ p)⁻¹ • Matrix.vecMulVec p (star p))
      = (star p ⬝ᵥ p)⁻¹ • Matrix.vecMulVec p (star p) := by
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have hkey : Matrix.vecMulVec p (star p)
        * Matrix.vecMulVec p (star p)
      = (star p ⬝ᵥ p) • Matrix.vecMulVec p (star p) := by
    ext i j
    rw [Matrix.mul_apply, Matrix.smul_apply]
    simp only [Matrix.vecMulVec_apply]
    rw [show (∑ k, p i * star p k * (p k * star p j))
      = (∑ k, star p k * p k) * (p i * star p j) from by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun k _ => by ring]
    rw [show (∑ k, star p k * p k) = star p ⬝ᵥ p from rfl,
      smul_eq_mul]
  rw [hkey, smul_smul]
  congr 1
  field_simp

/-- Nuisance invariance: shorting kills every nuisance-valued
correction of the raw source. -/
theorem nuisance_invariance {n m k : Type*} [Fintype n]
    [DecidableEq n] [Fintype m] [Fintype k] (Pr S : Matrix n n ℂ)
    (N : Matrix n m ℂ) (L : Matrix m n ℂ)
    (hN : (1 - Pr) * N = 0) :
    (1 - Pr) * (S + N * L) = (1 - Pr) * S := by
  rw [Matrix.mul_add, ← Matrix.mul_assoc, hN,
    Matrix.zero_mul, add_zero]

/-- Coequalizer uniqueness: maps out of a surjection agreeing
after composition are equal. -/
theorem quotient_unique_through_surjection {A B C : Type*}
    (q : A → B) (hq : Function.Surjective q) (π₁ π₂ : B → C)
    (h : ∀ a, π₁ (q a) = π₂ (q a)) : π₁ = π₂ := by
  funext b
  obtain ⟨a, rfl⟩ := hq b
  exact h a

/-- Router monotonicity: enlarging the feasible router set can
only lower the finite optimum. -/
theorem router_min_monotone (S T : Finset ℝ) (hST : S ⊆ T)
    (hS : S.Nonempty) :
    T.min' (hS.mono hST) ≤ S.min' hS :=
  T.min'_le _ (hST (S.min'_mem hS))

/-- Electrical-router Laplacian: `B·diag(u)·B*` is PSD for
nonnegative capacities. -/
theorem electrical_laplacian_psd {v e : Type*} [Fintype v]
    [Fintype e] [DecidableEq e] (B : Matrix v e ℝ) (u : e → ℝ)
    (hu : ∀ i, 0 ≤ u i) (x : v → ℝ) :
    0 ≤ x ⬝ᵥ (B * Matrix.diagonal u * Bᵀ).mulVec x := by
  have hy : (B * Matrix.diagonal u * Bᵀ).mulVec x
      = B.mulVec ((Matrix.diagonal u).mulVec (Bᵀ.mulVec x)) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  rw [hy]
  rw [show x ⬝ᵥ B.mulVec
      ((Matrix.diagonal u).mulVec (Bᵀ.mulVec x))
    = (Matrix.diagonal u).mulVec (Bᵀ.mulVec x)
        ⬝ᵥ (Bᵀ.mulVec x) from by
      rw [dotProduct_comm, graded_stokes_adjoint]]
  set y := Bᵀ.mulVec x with hyy
  have hdiag : (Matrix.diagonal u).mulVec y
      = fun i => u i * y i := by
    funext i
    rw [Matrix.mulVec_diagonal]
  rw [hdiag]
  rw [dotProduct]
  refine Finset.sum_nonneg fun i _ => ?_
  have := hu i
  have hsq : 0 ≤ y i * y i := mul_self_nonneg _
  calc (0 : ℝ) ≤ u i * (y i * y i) := by positivity
    _ = u i * y i * y i := by ring

/-- Finite Hodge split: every subspace of the finite edge space
splits orthogonally against its complement. -/
theorem parity_hodge_split
    (K : Submodule ℂ (EuclideanSpace ℂ (Fin 6))) :
    IsCompl K Kᗮ :=
  K.isCompl_orthogonal

/-- Spatial-compiler cut certificate (re-export shape): a
current with congestion `κ` bounds the realized demand by `κ`
times the cut capacity. -/
theorem spatial_compiler_cut {ι : Type*} [Fintype ι]
    [DecidableEq ι] (j c : ι → ι → ℝ)
    (hanti : ∀ u v, j u v = -j v u) (A : Finset ι) (κ : ℝ)
    (hcong : ∀ u v, |j u v| ≤ κ * c u v) :
    ∑ v ∈ A, ∑ u, j v u
      ≤ κ * ∑ v ∈ A, ∑ u ∈ Aᶜ, c v u :=
  flow_cut_weak_duality j c hanti A κ hcong

end NCG
