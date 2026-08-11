/-
Copyright (c) 2026 Aurelien Pelissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurelien Pelissier
-/
import NCG.Grand.UniversalFeedback

/-!
# Propagation-invariant Einstein observability subspace

This module proves the finite observability theorem used by
`thm:SMST-invariant-Einstein-subspace`.  The residual operator is represented
as `LᵀL`, where `L` stacks the endpoint-writer, tail-innovation, and
action-range residual maps.  The manuscript's observability Gram is therefore
the Gram of the finite Krylov stack.

The kernel is proved to be exactly the all-time residual-null space and the
largest propagation-invariant subspace of the one-step residual kernel.
Cayley--Hamilton enters through `feedback_kernel_reduction`.  The final
section gives the exhaustive two-dimensional alternatives, the eigenline
property on the rank-one branch, and the matching-axis residual identity.
-/

open Matrix Finset

namespace NCG

variable {d m : Type*} [Fintype d] [DecidableEq d]
  [Fintype m] [DecidableEq m]

/-- The finite Krylov observability synthesis, with one row block for each
power below the carrier dimension. -/
def einsteinObservabilityStack (P : Matrix d d ℝ) (L : Matrix m d ℝ) :
    Matrix (Fin (Fintype.card d) × m) d ℝ :=
  fun q i => (L * P ^ q.1.1) q.2 i

/-- The finite observability Gram `O_d`. -/
def einsteinObservabilityGram (P : Matrix d d ℝ) (L : Matrix m d ℝ) :
    Matrix d d ℝ :=
  ∑ n : Fin (Fintype.card d),
    (L * P ^ n.1)ᵀ * (L * P ^ n.1)

/-- The physically reconstructed Einstein-eligible coefficient space. -/
def invariantEinsteinSubspace (P : Matrix d d ℝ) (L : Matrix m d ℝ) :
    Submodule ℝ (d → ℝ) :=
  LinearMap.ker (einsteinObservabilityGram P L).mulVecLin

/-- The stack Gram is the manuscript's sum
`Σ_n (P^n)ᵀ (LᵀL) P^n`. -/
theorem einsteinObservabilityGram_eq_sum
    (P : Matrix d d ℝ) (L : Matrix m d ℝ) :
    einsteinObservabilityGram P L =
      ∑ n : Fin (Fintype.card d),
        (P ^ n.1)ᵀ * (Lᵀ * L) * P ^ n.1 := by
  apply Finset.sum_congr rfl
  intro n hn
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose,
    Matrix.mul_assoc]

private theorem dotProduct_gram_mulVec
    (A : Matrix m d ℝ) (x : d → ℝ) :
    dotProduct x ((Aᵀ * A).mulVec x) =
      dotProduct (A.mulVec x) (A.mulVec x) := by
  rw [← Matrix.mulVec_mulVec, dotProduct_mulVec,
    Matrix.vecMul_transpose]

private theorem real_dotProduct_self_nonneg (x : d → ℝ) :
    0 ≤ dotProduct x x := by
  rw [dotProduct]
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)

/-- Membership in the Gram kernel is exactly vanishing of every row block of
the finite Krylov stack. -/
theorem mem_invariantEinsteinSubspace_iff_window
    (P : Matrix d d ℝ) (L : Matrix m d ℝ) (x : d → ℝ) :
    x ∈ invariantEinsteinSubspace P L ↔
      ∀ n : Fin (Fintype.card d),
        L.mulVec ((P ^ n.1).mulVec x) = 0 := by
  rw [invariantEinsteinSubspace]
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply]
  constructor
  · intro hx n
    have hquad := congrArg (dotProduct x) hx
    have hsum : ∑ k : Fin (Fintype.card d),
        dotProduct ((L * P ^ k.1).mulVec x)
          ((L * P ^ k.1).mulVec x) = 0 := by
      unfold einsteinObservabilityGram at hquad
      simp only [Matrix.sum_mulVec, dotProduct_sum,
        dotProduct_zero, dotProduct_gram_mulVec] at hquad
      exact hquad
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg
      (fun k _ => real_dotProduct_self_nonneg _)).mp hsum n (mem_univ _)
    have hz : (L * P ^ n.1).mulVec x = 0 :=
      dotProduct_self_eq_zero.mp hterm
    simpa [Matrix.mulVec_mulVec] using hz
  · intro hx
    unfold einsteinObservabilityGram
    rw [Matrix.sum_mulVec]
    apply Finset.sum_eq_zero
    intro n hn
    rw [← Matrix.mulVec_mulVec]
    have hz : (L * P ^ n.1).mulVec x = 0 := by
      simpa [Matrix.mulVec_mulVec] using hx n
    rw [hz, Matrix.mulVec_zero]

/-- Cayley--Hamilton upgrades the finite window to every propagated power. -/
theorem mem_invariantEinsteinSubspace_iff_all_powers
    (P : Matrix d d ℝ) (L : Matrix m d ℝ) (x : d → ℝ) :
    x ∈ invariantEinsteinSubspace P L ↔
      ∀ n : ℕ, L.mulVec ((P ^ n).mulVec x) = 0 := by
  constructor
  · intro hx
    have hwindow := (mem_invariantEinsteinSubspace_iff_window P L x).mp hx
    intro n
    funext i
    let B : Matrix (Fin 1) d ℝ := fun _ j => L i j
    let C : Matrix d (Fin 1) ℝ := fun j _ => x j
    have hlow : ∀ k < Fintype.card d, B * P ^ k * C = 0 := by
      intro k hk
      rw [Matrix.mul_assoc]
      ext a b
      fin_cases a
      fin_cases b
      have hvec := congrFun (hwindow (⟨k, hk⟩ : Fin (Fintype.card d))) i
      simp only [Pi.zero_apply] at hvec
      change ∑ j, L i j * (∑ a, (P ^ k) j a * x a) = 0
      simpa only [Matrix.mulVec, dotProduct] using hvec
    have hall := feedback_kernel_reduction B C P hlow n
    rw [Matrix.mul_assoc] at hall
    have hentry := congrFun (congrFun hall (0 : Fin 1)) (0 : Fin 1)
    simp only [B, C, Matrix.mul_apply, Matrix.zero_apply] at hentry
    change ∑ j, L i j * (∑ a, (P ^ n) j a * x a) = 0
    exact hentry
  · intro hall
    apply (mem_invariantEinsteinSubspace_iff_window P L x).2
    intro n
    exact hall n.1

/-- The Einstein space is invariant under the measured propagator. -/
theorem invariantEinsteinSubspace_isInvariant
    (P : Matrix d d ℝ) (L : Matrix m d ℝ) :
    invariantEinsteinSubspace P L ≤
      (invariantEinsteinSubspace P L).comap P.mulVecLin := by
  intro x hx
  apply (mem_invariantEinsteinSubspace_iff_all_powers P L (P.mulVec x)).2
  intro n
  have h := (mem_invariantEinsteinSubspace_iff_all_powers P L x).1 hx (n + 1)
  simpa [pow_succ, Matrix.mulVec_mulVec] using h

/-- The Einstein space lies in the kernel of the one-step residual map. -/
theorem invariantEinsteinSubspace_le_residualKernel
    (P : Matrix d d ℝ) (L : Matrix m d ℝ) :
    invariantEinsteinSubspace P L ≤ LinearMap.ker L.mulVecLin := by
  intro x hx
  have h := (mem_invariantEinsteinSubspace_iff_all_powers P L x).1 hx 0
  simpa using h

/-- Maximality: every `P`-invariant subspace in the residual kernel is
contained in the observability kernel. -/
theorem invariantEinsteinSubspace_isLargest
    (P : Matrix d d ℝ) (L : Matrix m d ℝ)
    (S : Submodule ℝ (d → ℝ))
    (hInv : S ≤ S.comap P.mulVecLin)
    (hRes : S ≤ LinearMap.ker L.mulVecLin) :
    S ≤ invariantEinsteinSubspace P L := by
  intro x hx
  apply (mem_invariantEinsteinSubspace_iff_all_powers P L x).2
  intro n
  have hpow : (P ^ n).mulVec x ∈ S := by
    induction n with
    | zero => simpa using hx
    | succ n ih =>
        have hstep := hInv ih
        simpa [pow_succ', Matrix.mulVec_mulVec] using hstep
  exact hRes hpow

/-- Positive definiteness of the observability Gram is equivalent to absence
of a nonzero eligible coefficient direction. -/
theorem einsteinObservabilityGram_posDef_iff_subspace_bot
    (P : Matrix d d ℝ) (L : Matrix m d ℝ) :
    (einsteinObservabilityGram P L).PosDef ↔
      invariantEinsteinSubspace P L = ⊥ := by
  constructor
  · intro hO
    apply le_antisymm ?_ bot_le
    intro x hx
    show x = 0
    by_contra hx0
    have hpos := hO.dotProduct_mulVec_pos hx0
    change 0 < dotProduct x ((einsteinObservabilityGram P L).mulVec x) at hpos
    have hxv : (einsteinObservabilityGram P L).mulVec x = 0 := hx
    rw [hxv, dotProduct_zero] at hpos
    exact (lt_irrefl 0 hpos)
  · intro hbot
    apply Matrix.PosDef.of_dotProduct_mulVec_pos
    · rw [Matrix.isHermitian_iff_isSymm, Matrix.IsSymm.ext_iff]
      intro i j
      unfold einsteinObservabilityGram
      simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.transpose_apply]
      apply Finset.sum_congr rfl
      intro n hn
      apply Finset.sum_congr rfl
      intro k hk
      ring
    · intro x hx0
      have hxnot : x ∉ invariantEinsteinSubspace P L := by
        rw [hbot]
        simpa using hx0
      have hnotall : ¬ ∀ n : Fin (Fintype.card d),
          L.mulVec ((P ^ n.1).mulVec x) = 0 := by
        intro hall
        exact hxnot ((mem_invariantEinsteinSubspace_iff_window P L x).2 hall)
      push_neg at hnotall
      obtain ⟨n, hn⟩ := hnotall
      have hn' : (L * P ^ n.1).mulVec x ≠ 0 := by
        simpa [Matrix.mulVec_mulVec] using hn
      have hterm : 0 < dotProduct ((L * P ^ n.1).mulVec x)
          ((L * P ^ n.1).mulVec x) := by
        simpa only [star_trivial] using
          (dotProduct_self_star_pos_iff.mpr hn')
      have hsum : 0 < ∑ k : Fin (Fintype.card d),
          dotProduct ((L * P ^ k.1).mulVec x)
            ((L * P ^ k.1).mulVec x) := by
        exact Finset.sum_pos'
          (fun k _ => real_dotProduct_self_nonneg _)
          ⟨n, mem_univ n, hterm⟩
      change 0 < dotProduct x ((einsteinObservabilityGram P L).mulVec x)
      unfold einsteinObservabilityGram
      simpa only [Matrix.sum_mulVec, dotProduct_sum,
        dotProduct_gram_mulVec] using hsum

/-- The metric matching-axis residual written in source coordinates. -/
noncomputable def matchingAxisResidual (G P : Matrix d d ℝ) (e : d → ℝ) : ℝ :=
  dotProduct (P.mulVec e) (G.mulVec (P.mulVec e))
    - (dotProduct e (G.mulVec (P.mulVec e))) ^ 2 /
      dotProduct e (G.mulVec e)

/-- An invariant coefficient line has identically zero matching-axis
residual for every positive source metric. -/
theorem matchingAxisResidual_eq_zero_of_eigenvector
    (G P : Matrix d d ℝ) (hG : G.PosDef)
    (e : d → ℝ) (he : e ≠ 0) (c : ℝ)
    (hPe : P.mulVec e = c • e) :
    matchingAxisResidual G P e = 0 := by
  have hq : 0 < dotProduct e (G.mulVec e) := hG.dotProduct_mulVec_pos he
  unfold matchingAxisResidual
  rw [hPe]
  simp only [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct,
    smul_eq_mul]
  field_simp
  ring

/-- The exhaustive `d=2` branch classification.  The middle branch includes
both the manuscript's rank-one statement and the canonical eigenline. -/
theorem invariantEinsteinSubspace_fin_two_trichotomy
    (P : Matrix (Fin 2) (Fin 2) ℝ) (L : Matrix m (Fin 2) ℝ) :
    ((einsteinObservabilityGram P L).PosDef ∧
        invariantEinsteinSubspace P L = ⊥)
      ∨ ((einsteinObservabilityGram P L).rank = 1 ∧
          Module.finrank ℝ (invariantEinsteinSubspace P L) = 1 ∧
          ∀ e ∈ invariantEinsteinSubspace P L, e ≠ 0 →
            ∃ c : ℝ, P.mulVec e = c • e)
      ∨ (invariantEinsteinSubspace P L = ⊤ ∧
          einsteinObservabilityGram P L = 0) := by
  let K := invariantEinsteinSubspace P L
  let O := einsteinObservabilityGram P L
  have hdim : Module.finrank ℝ K ≤ 2 := by
    simpa [K] using (Submodule.finrank_le K)
  have hranknull := LinearMap.finrank_range_add_finrank_ker O.mulVecLin
  have hker : LinearMap.ker O.mulVecLin = K := rfl
  have hrank : O.rank + Module.finrank ℝ K = 2 := by
    change Module.finrank ℝ (LinearMap.range O.mulVecLin)
        + Module.finrank ℝ K = 2
    rw [← hker]
    simpa using hranknull
  interval_cases hK : Module.finrank ℝ K
  · left
    have hbot : invariantEinsteinSubspace P L = ⊥ :=
      Submodule.finrank_eq_zero.mp hK
    exact ⟨(einsteinObservabilityGram_posDef_iff_subspace_bot P L).2 hbot,
      hbot⟩
  · right; left
    refine ⟨?_, rfl, ?_⟩
    · change O.rank = 1
      omega
    intro e heK he0
    have hspan := eq_span_singleton_of_mem_of_finrank_eq_one hK heK he0
    have hPeK : P.mulVec e ∈ K := by
      exact invariantEinsteinSubspace_isInvariant P L heK
    rw [hspan] at hPeK
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hPeK
    exact ⟨c, hc.symm⟩
  · right; right
    have htop : K = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      simpa [K] using hK
    refine ⟨htop, ?_⟩
    apply Matrix.mulVec_injective
    funext x
    have hxK : x ∈ K := by rw [htop]; exact Submodule.mem_top
    change (einsteinObservabilityGram P L).mulVec x =
      (0 : Matrix (Fin 2) (Fin 2) ℝ).mulVec x
    rw [Matrix.zero_mulVec]
    exact hxK

end NCG
