/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Renewal.RenewalMemoryCumulantExact
/-!
# Complete resolved-memory subtraction with blocks of different sizes
  (`thm:supp-memory-short`)

`Renewal/RenewalMemoryCumulantExact.lean` proves the memory-short identities when all the
faithful blocks `ρ_ω` act on one common matrix type.  The manuscript's resolved cut-memory
state `ρ_cq = ⊕_ω p_ω ρ_ω` lives on `⊕_ω ℂ^{d_ω}` with blocks of *different* dimensions.
Here the block types form a dependent family `n : Ω → Type`, and every statement is proved
in that generality:

* `directSumGenerator`, `exp_directSumGenerator`, `mixturePartition_eq_trace_exp`: with the
  Hermitian generator `log ρ_cq = ⊕_ω (log p_ω · 1 + H_ω)` (whose exponential is
  `ρ_cq = ⊕_ω p_ω e^{H_ω}`, `Matrix.blockDiagonal'`) and `K_cq(z) = ⊕_ω K_ω(z)`, the
  complete log-partition of `eq:supp-memory-logpartition`,
  `log Tr exp(log ρ_cq + K_cq(z))`, equals `log Σ_ω p_ω Tr exp(H_ω + K_ω(z))`
  (the block exponential and trace split over the classical label);
* `memoryLogPartition_zero` (`M_cq(0) = 0`), `memory_first_deriv_t/u` (`DM_cq(0) = 0`);
* `memory_hessian`: the mixed second derivative is the classical branch covariance plus the
  branch-averaged centered Kubo–Mori (Duhamel/BKM) form;
* `classical_summand_nonneg`, `quantum_summand_nonneg`: both summands are `≥ 0` on the
  diagonal (and `*_eq_zero_iff`, `quantum_branch_vanish_iff`: vanishing clauses);
* `shortedScore_def`: `A_sh = A_coarse − M_cq`;
* `memory_short_blocks`: everything packaged for the paper's hypotheses (faithful blocks
  `ρ_ω = e^{H_ω}` with `Tr ρ_ω = 1`, weights `p_ω > 0` summing to one, Hermitian linear
  perturbation evaluated on the plane `z = t x + u y`).

The perturbation is evaluated along a plane `z = t x + u y` (`Kx`, `Ky` the blocks of
`K_cq(x)`, `K_cq(y)`), as in the common-type file; the Hessian of `M_cq` at `0` is the
bilinear form `(x, y) ↦ ∂_u ∂_t M_cq(tx + uy)|₀`.  The single-block analytic lemmas
(Duhamel series, BKM centering and positivity) are reused from
`RenewalGeometry.RenewalMemory`, applied block by block.
-/

open Matrix RenewalGeometry.TraceExp
open scoped Matrix.Norms.Operator

namespace RenewalGeometry
namespace RenewalMemoryBlocks

open RenewalMemory

variable {Ω : Type} [Fintype Ω] {n : Ω → Type} [∀ ω, Fintype (n ω)] [∀ ω, DecidableEq (n ω)]

/-- A normalized block is nonzero-dimensional. -/
theorem nonempty_of_trace_eq_one {m : Type} [Fintype m] (A : Matrix m m ℂ)
    (h : A.trace = 1) : Nonempty m := by
  by_contra hm
  rw [not_nonempty_iff] at hm
  have : A.trace = 0 := by simp [Matrix.trace]
  rw [this] at h
  exact zero_ne_one h

variable (p : Ω → ℝ) (H Kx Ky : (ω : Ω) → Matrix (n ω) (n ω) ℂ)

/-! ### The complete memory log-partition -/

/-- `G(t,u) = ∑_ω p_ω Tr exp(H_ω + t Kx_ω + u Ky_ω)`. -/
noncomputable def mixturePartition (t u : ℝ) : ℝ :=
  ∑ ω : Ω, p ω * ((NormedSpace.exp (H ω + t • Kx ω + u • Ky ω)).trace).re

/-- The mixture mean slope `∑_ω p_ω Tr(ρ_ω K_ω)`. -/
noncomputable def meanBar (K : (ω : Ω) → Matrix (n ω) (n ω) ℂ) : ℝ :=
  ∑ ω : Ω, p ω * ((NormedSpace.exp (H ω) * K ω).trace).re

/-- **The complete memory log-partition** `M_cq(t,u) = log G(t,u) − (t x̄ + u ȳ)`. -/
noncomputable def memoryLogPartition (t u : ℝ) : ℝ :=
  Real.log (mixturePartition p H Kx Ky t u) - (t * meanBar p H Kx + u * meanBar p H Ky)

/-- The centered block perturbation `K̃_ω = K_ω − Tr(ρ_ω K_ω)·1`. -/
noncomputable def centered (K : (ω : Ω) → Matrix (n ω) (n ω) ℂ) (ω : Ω) :
    Matrix (n ω) (n ω) ℂ :=
  K ω - ((NormedSpace.exp (H ω) * K ω).trace) • (1 : Matrix (n ω) (n ω) ℂ)

/-! ### The direct-sum presentation -/

/-- The Hermitian generator `log ρ_cq = ⊕_ω (log p_ω · 1 + H_ω)`. -/
noncomputable def directSumGenerator [DecidableEq Ω] : Matrix (Σ ω, n ω) (Σ ω, n ω) ℂ :=
  Matrix.blockDiagonal' fun ω => ((Real.log (p ω) : ℝ) : ℂ) • (1 : Matrix (n ω) (n ω) ℂ) + H ω

/-- The resolved cut-memory state `ρ_cq = ⊕_ω p_ω ρ_ω`, `ρ_ω = e^{H_ω}`. -/
noncomputable def directSumState [DecidableEq Ω] : Matrix (Σ ω, n ω) (Σ ω, n ω) ℂ :=
  Matrix.blockDiagonal' fun ω => ((p ω : ℝ) : ℂ) • NormedSpace.exp (H ω)

/-- The linear perturbation `K_cq(t x + u y) = ⊕_ω (t Kx_ω + u Ky_ω)`. -/
noncomputable def directSumPerturbation [DecidableEq Ω] (t u : ℝ) : Matrix (Σ ω, n ω) (Σ ω, n ω) ℂ :=
  Matrix.blockDiagonal' fun ω => t • Kx ω + u • Ky ω

/-- `exp(c·1 + A) = e^c · exp A` for a complex scalar `c`. -/
theorem exp_scalar_add {m : Type} [Fintype m] [DecidableEq m] (c : ℂ) (A : Matrix m m ℂ) :
    NormedSpace.exp (c • (1 : Matrix m m ℂ) + A) = NormedSpace.exp c • NormedSpace.exp A := by
  have hcomm : Commute (c • (1 : Matrix m m ℂ)) A := (Commute.one_left A).smul_left c
  rw [Matrix.exp_add_of_commute _ _ hcomm]
  have h1 : c • (1 : Matrix m m ℂ) = Matrix.diagonal fun _ => c := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  rw [h1, Matrix.exp_diagonal, Pi.exp_def]
  ext i j
  simp [Matrix.diagonal_mul]


set_option backward.isDefEq.respectTransparency false in
/-- The exponential in the product algebra `Π ω, Matrix (n ω) (n ω) ℂ` is computed
blockwise. -/
theorem exp_pi_apply (v : ∀ ω, Matrix (n ω) (n ω) ℂ) (ω : Ω) :
    NormedSpace.exp v ω = NormedSpace.exp (v ω) := by
  open scoped Matrix.Norms.Operator in exact Pi.coe_exp v ω

/-- The generator exponentiates to the state: `exp(log ρ_cq) = ρ_cq`. -/
theorem exp_directSumGenerator [DecidableEq Ω] (hp : ∀ ω, 0 < p ω) :
    NormedSpace.exp (directSumGenerator p H) = directSumState p H := by
  unfold directSumGenerator directSumState
  rw [Matrix.exp_blockDiagonal']
  congr 1
  funext ω
  rw [exp_pi_apply, exp_scalar_add, ← Complex.exp_eq_exp_ℂ, ← Complex.ofReal_exp, Real.exp_log (hp ω)]

omit [Fintype Ω] [∀ ω, Fintype (n ω)] in
/-- The generator is Hermitian when the blocks are. -/
theorem directSumGenerator_isHermitian [DecidableEq Ω] (hH : ∀ ω, (H ω).IsHermitian) :
    (directSumGenerator p H).IsHermitian := by
  unfold directSumGenerator
  rw [Matrix.isHermitian_blockDiagonal'_iff]
  intro ω
  refine IsHermitian.add ?_ (hH ω)
  show ((((Real.log (p ω) : ℝ) : ℂ) • (1 : Matrix (n ω) (n ω) ℂ))ᴴ = _)
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Complex.star_def,
    Complex.conj_ofReal]

/-- The complete log-partition in direct-sum form:
`Tr exp(log ρ_cq + K_cq(t x + u y)) = ∑_ω p_ω Tr exp(H_ω + t Kx_ω + u Ky_ω)`. -/
theorem mixturePartition_eq_trace_exp [DecidableEq Ω] (hp : ∀ ω, 0 < p ω) (t u : ℝ) :
    mixturePartition p H Kx Ky t u =
      ((NormedSpace.exp (directSumGenerator p H + directSumPerturbation Kx Ky t u)).trace).re := by
  unfold directSumGenerator directSumPerturbation mixturePartition
  rw [← Matrix.blockDiagonal'_add, Matrix.exp_blockDiagonal',
    Matrix.trace_blockDiagonal', Complex.re_sum]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [exp_pi_apply, Pi.add_apply,
    add_assoc (((Real.log (p ω) : ℝ) : ℂ) • (1 : Matrix (n ω) (n ω) ℂ)), exp_scalar_add,
    ← Complex.exp_eq_exp_ℂ, ← Complex.ofReal_exp, Real.exp_log (hp ω), Matrix.trace_smul,
    smul_eq_mul, Complex.re_ofReal_mul, ← add_assoc]

/-! ### Normalization and first derivatives -/

theorem mixturePartition_zero (hsum : ∑ ω : Ω, p ω = 1)
    (htr : ∀ ω, (NormedSpace.exp (H ω)).trace = 1) :
    mixturePartition p H Kx Ky 0 0 = 1 := by
  unfold mixturePartition
  have hω : ∀ ω : Ω, H ω + (0:ℝ) • Kx ω + (0:ℝ) • Ky ω = H ω := by
    intro ω
    rw [zero_smul, zero_smul, add_zero, add_zero]
  rw [Finset.sum_congr rfl fun ω _ => by rw [hω ω, htr ω]]
  simp only [Complex.one_re, mul_one]
  exact hsum

theorem mixturePartition_pos [Nonempty Ω] [∀ ω, Nonempty (n ω)]
    (hp : ∀ ω, 0 < p ω) (hH : ∀ ω, (H ω).IsHermitian)
    (hKx : ∀ ω, (Kx ω).IsHermitian) (hKy : ∀ ω, (Ky ω).IsHermitian) (t u : ℝ) :
    0 < mixturePartition p H Kx Ky t u :=
  Finset.sum_pos (fun ω _ => mul_pos (hp ω)
    (traceExp_re_pos _ (hermitian_path (hH ω) (hKx ω) (hKy ω) t u)))
    Finset.univ_nonempty

/-- **Normalization**: `M_cq(0) = 0`. -/
theorem memoryLogPartition_zero (hsum : ∑ ω : Ω, p ω = 1)
    (htr : ∀ ω, (NormedSpace.exp (H ω)).trace = 1) :
    memoryLogPartition p H Kx Ky 0 0 = 0 := by
  unfold memoryLogPartition
  rw [mixturePartition_zero p H Kx Ky hsum htr, Real.log_one]
  ring

theorem hasDerivAt_mixture_t [∀ ω, Nonempty (n ω)] (u : ℝ) :
    HasDerivAt (fun t => mixturePartition p H Kx Ky t u)
      (∑ ω : Ω, p ω * ((NormedSpace.exp (H ω + u • Ky ω) * Kx ω).trace).re) 0 := by
  refine hasDerivAt_finset_sum fun ω _ => ?_
  have h1 := hasDerivAt_traceExp (H ω + u • Ky ω) (Kx ω)
  have h2 : (fun t : ℝ => (NormedSpace.exp (H ω + u • Ky ω + t • Kx ω)).trace)
      = fun t : ℝ => (NormedSpace.exp (H ω + t • Kx ω + u • Ky ω)).trace := by
    funext t
    rw [add_right_comm]
  rw [h2] at h1
  exact (hasDerivAt_re h1).const_mul (p ω)

theorem hasDerivAt_mixture_u [∀ ω, Nonempty (n ω)] :
    HasDerivAt (fun u => mixturePartition p H Kx Ky 0 u) (meanBar p H Ky) 0 := by
  refine hasDerivAt_finset_sum fun ω _ => ?_
  have h1 := hasDerivAt_traceExp (H ω) (Ky ω)
  have h2 : (fun u : ℝ => (NormedSpace.exp (H ω + u • Ky ω)).trace)
      = fun u : ℝ => (NormedSpace.exp (H ω + (0:ℝ) • Kx ω + u • Ky ω)).trace := by
    funext u
    rw [zero_smul, add_zero]
  rw [h2] at h1
  exact (hasDerivAt_re h1).const_mul (p ω)

/-- **First derivative vanishes** (`x`-direction). -/
theorem memory_first_deriv_t (hsum : ∑ ω : Ω, p ω = 1)
    (htr : ∀ ω, (NormedSpace.exp (H ω)).trace = 1) :
    HasDerivAt (fun t => memoryLogPartition p H Kx Ky t 0) 0 0 := by
  have : ∀ ω, Nonempty (n ω) := fun ω => nonempty_of_trace_eq_one _ (htr ω)
  have hG := hasDerivAt_mixture_t p H Kx Ky 0
  have hd : (∑ ω : Ω, p ω * ((NormedSpace.exp (H ω + (0:ℝ) • Ky ω) * Kx ω).trace).re)
      = meanBar p H Kx := by
    unfold meanBar
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [zero_smul, add_zero]
  rw [hd] at hG
  have hG0 : mixturePartition p H Kx Ky 0 0 = 1 := mixturePartition_zero p H Kx Ky hsum htr
  have hlog := hG.log (by rw [hG0]; exact one_ne_zero)
  rw [hG0, div_one] at hlog
  have hlin : HasDerivAt (fun t : ℝ => t * meanBar p H Kx + 0 * meanBar p H Ky)
      (meanBar p H Kx) 0 := by
    have h := ((hasDerivAt_id (0:ℝ)).mul_const (meanBar p H Kx)).add_const
      (0 * meanBar p H Ky)
    rw [one_mul] at h
    exact h
  have h := hlog.sub hlin
  rw [sub_self] at h
  exact h

/-- **First derivative vanishes** (`y`-direction). -/
theorem memory_first_deriv_u (hsum : ∑ ω : Ω, p ω = 1)
    (htr : ∀ ω, (NormedSpace.exp (H ω)).trace = 1) :
    HasDerivAt (fun u => memoryLogPartition p H Kx Ky 0 u) 0 0 := by
  have : ∀ ω, Nonempty (n ω) := fun ω => nonempty_of_trace_eq_one _ (htr ω)
  have hG := hasDerivAt_mixture_u p H Kx Ky
  have hG0 : mixturePartition p H Kx Ky 0 0 = 1 := mixturePartition_zero p H Kx Ky hsum htr
  have hlog := hG.log (by rw [hG0]; exact one_ne_zero)
  rw [hG0, div_one] at hlog
  have hlin : HasDerivAt (fun u : ℝ => 0 * meanBar p H Kx + u * meanBar p H Ky)
      (meanBar p H Ky) 0 := by
    have h := ((hasDerivAt_id (0:ℝ)).mul_const (meanBar p H Ky)).const_add
      (0 * meanBar p H Kx)
    rw [one_mul] at h
    exact h
  have h := hlog.sub hlin
  rw [sub_self] at h
  exact h

/-! ### The Hessian identity -/

/-- Single-block split of the BKM series into the centered Duhamel integral plus the
product of mean slopes. -/
theorem bkm_block_split {m : Type} [Fintype m] [DecidableEq m] [Nonempty m]
    (A P Q : Matrix m m ℂ) (hA : A.IsHermitian) (hP : P.IsHermitian) (hQ : Q.IsHermitian)
    (htr : (NormedSpace.exp A).trace = 1) :
    (bkmSeries A Q P).re
    = (bkmIntegral A (P - ((NormedSpace.exp A * P).trace) • (1 : Matrix m m ℂ))
        (Q - ((NormedSpace.exp A * Q).trace) • (1 : Matrix m m ℂ))).re
      + ((NormedSpace.exp A * P).trace).re * ((NormedSpace.exp A * Q).trace).re := by
  have h1 : bkmSeries A Q P = bkmIntegral A Q P := bkmSeries_eq_integral A Q P hA
  have h2' := bkm_centering A Q P htr
  have h3 := bkmIntegral_comm A (Q - ((NormedSpace.exp A * Q).trace) • (1 : Matrix m m ℂ))
    (P - ((NormedSpace.exp A * P).trace) • (1 : Matrix m m ℂ))
  rw [h3] at h2'
  have h4 : bkmSeries A Q P
      = bkmIntegral A (P - ((NormedSpace.exp A * P).trace) • (1 : Matrix m m ℂ))
          (Q - ((NormedSpace.exp A * Q).trace) • (1 : Matrix m m ℂ))
        + (NormedSpace.exp A * Q).trace * (NormedSpace.exp A * P).trace := by
    rw [h1, h2']
    ring
  have hix := trace_mul_hermitian_real (exp_hermitian A hA) hP
  have hiy := trace_mul_hermitian_real (exp_hermitian A hA) hQ
  have hmul : ((NormedSpace.exp A * Q).trace * (NormedSpace.exp A * P).trace).re
      = ((NormedSpace.exp A * P).trace).re * ((NormedSpace.exp A * Q).trace).re := by
    rw [Complex.mul_re, hiy, hix]
    ring
  rw [h4, Complex.add_re, hmul]

/-- The mixture covariance identity. -/
theorem covariance_split (hsum : ∑ ω : Ω, p ω = 1) :
    (∑ ω : Ω, p ω * ((((NormedSpace.exp (H ω) * Kx ω).trace).re - meanBar p H Kx)
        * (((NormedSpace.exp (H ω) * Ky ω).trace).re - meanBar p H Ky)))
    = (∑ ω : Ω, p ω * (((NormedSpace.exp (H ω) * Kx ω).trace).re
          * ((NormedSpace.exp (H ω) * Ky ω).trace).re))
      - meanBar p H Kx * meanBar p H Ky := by
  have hterm : ∀ ω ∈ Finset.univ (α := Ω),
      p ω * ((((NormedSpace.exp (H ω) * Kx ω).trace).re - meanBar p H Kx)
        * (((NormedSpace.exp (H ω) * Ky ω).trace).re - meanBar p H Ky))
      = p ω * (((NormedSpace.exp (H ω) * Kx ω).trace).re
            * ((NormedSpace.exp (H ω) * Ky ω).trace).re)
        - meanBar p H Ky * (p ω * ((NormedSpace.exp (H ω) * Kx ω).trace).re)
        - meanBar p H Kx * (p ω * ((NormedSpace.exp (H ω) * Ky ω).trace).re)
        + meanBar p H Kx * meanBar p H Ky * p ω :=
    fun ω _ => by ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hsum]
  have hmx : (∑ ω : Ω, p ω * ((NormedSpace.exp (H ω) * Kx ω).trace).re)
      = meanBar p H Kx := rfl
  have hmy : (∑ ω : Ω, p ω * ((NormedSpace.exp (H ω) * Ky ω).trace).re)
      = meanBar p H Ky := rfl
  rw [hmx, hmy]
  ring

/-- **The Hessian identity** for blocks of arbitrary (different) sizes:
`D²M_cq(0)[x,y] = ∑_ω p_ω (m_ω(x)−x̄)(m_ω(y)−ȳ)
  + ∑_ω p_ω ∫₀¹ Tr(ρ_ω^s K̃_ω(x) ρ_ω^{1−s} K̃_ω(y)) ds`. -/
theorem memory_hessian [Nonempty Ω]
    (hp : ∀ ω, 0 < p ω) (hsum : ∑ ω : Ω, p ω = 1)
    (hH : ∀ ω, (H ω).IsHermitian) (hKx : ∀ ω, (Kx ω).IsHermitian)
    (hKy : ∀ ω, (Ky ω).IsHermitian) (htr : ∀ ω, (NormedSpace.exp (H ω)).trace = 1) :
    deriv (fun u => deriv (fun t => memoryLogPartition p H Kx Ky t u) 0) 0
    = (∑ ω : Ω, p ω * ((((NormedSpace.exp (H ω) * Kx ω).trace).re - meanBar p H Kx)
          * (((NormedSpace.exp (H ω) * Ky ω).trace).re - meanBar p H Ky)))
      + ∑ ω : Ω, p ω * (bkmIntegral (H ω) (centered H Kx ω) (centered H Ky ω)).re := by
  have : ∀ ω, Nonempty (n ω) := fun ω => nonempty_of_trace_eq_one _ (htr ω)
  have hGpos : ∀ u : ℝ, 0 < mixturePartition p H Kx Ky 0 u := fun u =>
    mixturePartition_pos p H Kx Ky hp hH hKx hKy 0 u
  have hslice : ∀ u : ℝ,
      deriv (fun t => memoryLogPartition p H Kx Ky t u) 0
      = (∑ ω : Ω, p ω * ((NormedSpace.exp (H ω + u • Ky ω) * Kx ω).trace).re)
          / mixturePartition p H Kx Ky 0 u - meanBar p H Kx := by
    intro u
    have hG := hasDerivAt_mixture_t p H Kx Ky u
    have hlog := hG.log (ne_of_gt (hGpos u))
    have hlin : HasDerivAt (fun t : ℝ => t * meanBar p H Kx + u * meanBar p H Ky)
        (meanBar p H Kx) 0 := by
      have h := ((hasDerivAt_id (0:ℝ)).mul_const (meanBar p H Kx)).add_const
        (u * meanBar p H Ky)
      rw [one_mul] at h
      exact h
    exact (hlog.sub hlin).deriv
  have houter : (fun u => deriv (fun t => memoryLogPartition p H Kx Ky t u) 0)
      = fun u : ℝ => (∑ ω : Ω, p ω * ((NormedSpace.exp (H ω + u • Ky ω) * Kx ω).trace).re)
          / mixturePartition p H Kx Ky 0 u - meanBar p H Kx := funext hslice
  rw [houter]
  have hNx : HasDerivAt (fun u : ℝ => ∑ ω : Ω, p ω
      * ((NormedSpace.exp (H ω + u • Ky ω) * Kx ω).trace).re)
      (∑ ω : Ω, p ω * (bkmSeries (H ω) (Ky ω) (Kx ω)).re) (0 : ℝ) := by
    refine hasDerivAt_finset_sum fun ω _ => ?_
    exact (hasDerivAt_re (hasDerivAt_traceExpMul_zero (H ω) (Ky ω) (Kx ω))).const_mul (p ω)
  have hGu := hasDerivAt_mixture_u p H Kx Ky
  have hG00 : mixturePartition p H Kx Ky 0 0 = 1 := mixturePartition_zero p H Kx Ky hsum htr
  have hne : mixturePartition p H Kx Ky 0 0 ≠ 0 := by rw [hG00]; exact one_ne_zero
  have hNx0 : (∑ ω : Ω, p ω * ((NormedSpace.exp (H ω + (0:ℝ) • Ky ω) * Kx ω).trace).re)
      = meanBar p H Kx := by
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [zero_smul, add_zero]
  have hfull := (hNx.div hGu hne).sub_const (meanBar p H Kx)
  have hderiv2 : deriv (fun u : ℝ => (∑ ω : Ω, p ω
      * ((NormedSpace.exp (H ω + u • Ky ω) * Kx ω).trace).re)
      / mixturePartition p H Kx Ky 0 u - meanBar p H Kx) 0
      = ((∑ ω : Ω, p ω * (bkmSeries (H ω) (Ky ω) (Kx ω)).re)
            * mixturePartition p H Kx Ky 0 0
          - (∑ ω : Ω, p ω * ((NormedSpace.exp (H ω + (0:ℝ) • Ky ω) * Kx ω).trace).re)
            * meanBar p H Ky)
          / mixturePartition p H Kx Ky 0 0 ^ 2 :=
    hfull.deriv
  rw [hderiv2, hG00, hNx0, one_pow, div_one, mul_one]
  have hsplit : (∑ ω : Ω, p ω * (bkmSeries (H ω) (Ky ω) (Kx ω)).re)
      = (∑ ω : Ω, p ω * (bkmIntegral (H ω) (centered H Kx ω) (centered H Ky ω)).re)
        + ∑ ω : Ω, p ω * (((NormedSpace.exp (H ω) * Kx ω).trace).re
            * ((NormedSpace.exp (H ω) * Ky ω).trace).re) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [bkm_block_split (H ω) (Kx ω) (Ky ω) (hH ω) (hKx ω) (hKy ω) (htr ω)]
    unfold centered
    ring
  rw [hsplit, covariance_split p H Kx Ky hsum]
  ring

/-! ### Positivity and vanishing clauses -/

omit [Fintype Ω] in
/-- Centered perturbations of Hermitian data are Hermitian. -/
theorem centered_hermitian (K : (ω : Ω) → Matrix (n ω) (n ω) ℂ)
    (hH : ∀ ω, (H ω).IsHermitian) (hK : ∀ ω, (K ω).IsHermitian) (ω : Ω) :
    (centered H K ω).IsHermitian := by
  have him := trace_mul_hermitian_real (exp_hermitian (H ω) (hH ω)) (hK ω)
  have hstar : star ((NormedSpace.exp (H ω) * K ω).trace)
      = (NormedSpace.exp (H ω) * K ω).trace := Complex.conj_eq_iff_im.mpr him
  have h : (centered H K ω)ᴴ = centered H K ω := by
    unfold centered
    rw [Matrix.conjTranspose_sub, (hK ω).eq, Matrix.conjTranspose_smul,
      Matrix.conjTranspose_one, hstar]
  exact h

/-- **Positivity (classical summand)**: the branch mean-slope variance is `≥ 0`. -/
theorem classical_summand_nonneg (hp : ∀ ω, 0 < p ω) :
    0 ≤ ∑ ω : Ω, p ω * ((((NormedSpace.exp (H ω) * Kx ω).trace).re - meanBar p H Kx)
        * (((NormedSpace.exp (H ω) * Kx ω).trace).re - meanBar p H Kx)) :=
  Finset.sum_nonneg fun ω _ => mul_nonneg (hp ω).le (mul_self_nonneg _)

/-- **Vanishing clause (classical)**: iff all branch mean slopes agree. -/
theorem classical_summand_eq_zero_iff (hp : ∀ ω, 0 < p ω) :
    (∑ ω : Ω, p ω * ((((NormedSpace.exp (H ω) * Kx ω).trace).re - meanBar p H Kx)
        * (((NormedSpace.exp (H ω) * Kx ω).trace).re - meanBar p H Kx))) = 0
    ↔ ∀ ω : Ω, ((NormedSpace.exp (H ω) * Kx ω).trace).re = meanBar p H Kx := by
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun ω _ => mul_nonneg (hp ω).le (mul_self_nonneg _))]
  constructor
  · intro h ω
    have h1 := h ω (Finset.mem_univ ω)
    rcases mul_eq_zero.mp h1 with h3 | h3
    · exact absurd h3 (hp ω).ne'
    · exact sub_eq_zero.mp (mul_self_eq_zero.mp h3)
  · intro h ω _
    rw [h ω, sub_self, zero_mul, mul_zero]

omit [Fintype Ω] in
/-- **Positivity (quantum summand)**: each block's Kubo–Mori integral is `≥ 0`. -/
theorem quantum_summand_nonneg (hH : ∀ ω, (H ω).IsHermitian)
    (hKx : ∀ ω, (Kx ω).IsHermitian) (ω : Ω) :
    0 ≤ (bkmIntegral (H ω) (centered H Kx ω) (centered H Kx ω)).re :=
  bkmIntegral_self_nonneg (H ω) (centered H Kx ω) (hH ω) (centered_hermitian H Kx hH hKx ω)

omit [Fintype Ω] in
/-- **Vanishing clause (quantum)**: a block's Kubo–Mori summand vanishes iff that block's
perturbation is scalar. -/
theorem quantum_branch_vanish_iff (hH : ∀ ω, (H ω).IsHermitian)
    (hKx : ∀ ω, (Kx ω).IsHermitian) (ω : Ω) :
    (bkmIntegral (H ω) (centered H Kx ω) (centered H Kx ω)).re = 0
    ↔ Kx ω = ((NormedSpace.exp (H ω) * Kx ω).trace) • (1 : Matrix (n ω) (n ω) ℂ) := by
  rw [bkmIntegral_self_eq_zero_iff (H ω) (centered H Kx ω) (hH ω)
    (centered_hermitian H Kx hH hKx ω)]
  unfold centered
  exact sub_eq_zero

/-- The whole Hessian form is positive semidefinite on the diagonal. -/
theorem memory_hessian_diag_nonneg [Nonempty Ω]
    (hp : ∀ ω, 0 < p ω) (hsum : ∑ ω : Ω, p ω = 1)
    (hH : ∀ ω, (H ω).IsHermitian) (hKx : ∀ ω, (Kx ω).IsHermitian)
    (htr : ∀ ω, (NormedSpace.exp (H ω)).trace = 1) :
    0 ≤ deriv (fun u => deriv (fun t => memoryLogPartition p H Kx Kx t u) 0) 0 := by
  rw [memory_hessian p H Kx Kx hp hsum hH hKx hKx htr]
  exact add_nonneg (classical_summand_nonneg p H Kx hp)
    (Finset.sum_nonneg fun ω _ => mul_nonneg (hp ω).le (quantum_summand_nonneg H Kx hH hKx ω))

/-! ### The fully memory-shorted face score -/

/-- **The canonical fully memory-shorted face score** `A_sh = A_coarse − M_cq`. -/
noncomputable def shortedScore (Acoarse : ℝ → ℝ → ℝ) (t u : ℝ) : ℝ :=
  Acoarse t u - memoryLogPartition p H Kx Ky t u

theorem shortedScore_def (Acoarse : ℝ → ℝ → ℝ) (t u : ℝ) :
    shortedScore p H Kx Ky Acoarse t u = Acoarse t u - memoryLogPartition p H Kx Ky t u :=
  rfl

/-- **`thm:supp-memory-short`** for faithful blocks of arbitrary sizes `d_ω`: with
`ρ_cq = ⊕_ω p_ω e^{H_ω}` and `K_cq = ⊕_ω K_ω`, the complete log-partition
`log Tr exp(log ρ_cq + K_cq(t x + u y)) − m̄` is the block mixture `M_cq`, `M_cq(0) = 0`,
`DM_cq(0) = 0`, the Hessian is classical covariance plus Kubo–Mori, both summands are
nonnegative on the diagonal, and `A_sh = A_coarse − M_cq`. -/
theorem memory_short_blocks [DecidableEq Ω] [Nonempty Ω]
    (hp : ∀ ω, 0 < p ω) (hsum : ∑ ω : Ω, p ω = 1)
    (hH : ∀ ω, (H ω).IsHermitian) (hKx : ∀ ω, (Kx ω).IsHermitian)
    (hKy : ∀ ω, (Ky ω).IsHermitian) (htr : ∀ ω, (NormedSpace.exp (H ω)).trace = 1) :
    NormedSpace.exp (directSumGenerator p H) = directSumState p H ∧
    (directSumGenerator p H).IsHermitian ∧
    (∀ t u, memoryLogPartition p H Kx Ky t u =
      Real.log ((NormedSpace.exp (directSumGenerator p H
          + directSumPerturbation Kx Ky t u)).trace).re
        - (t * meanBar p H Kx + u * meanBar p H Ky)) ∧
    memoryLogPartition p H Kx Ky 0 0 = 0 ∧
    HasDerivAt (fun t => memoryLogPartition p H Kx Ky t 0) 0 0 ∧
    HasDerivAt (fun u => memoryLogPartition p H Kx Ky 0 u) 0 0 ∧
    deriv (fun u => deriv (fun t => memoryLogPartition p H Kx Ky t u) 0) 0
      = (∑ ω : Ω, p ω * ((((NormedSpace.exp (H ω) * Kx ω).trace).re - meanBar p H Kx)
          * (((NormedSpace.exp (H ω) * Ky ω).trace).re - meanBar p H Ky)))
        + ∑ ω : Ω, p ω * (bkmIntegral (H ω) (centered H Kx ω) (centered H Ky ω)).re ∧
    0 ≤ ∑ ω : Ω, p ω * ((((NormedSpace.exp (H ω) * Kx ω).trace).re - meanBar p H Kx)
        * (((NormedSpace.exp (H ω) * Kx ω).trace).re - meanBar p H Kx)) ∧
    (∀ ω, 0 ≤ (bkmIntegral (H ω) (centered H Kx ω) (centered H Kx ω)).re) ∧
    (∀ Acoarse : ℝ → ℝ → ℝ, ∀ t u,
      shortedScore p H Kx Ky Acoarse t u = Acoarse t u - memoryLogPartition p H Kx Ky t u) :=
  ⟨exp_directSumGenerator p H hp, directSumGenerator_isHermitian p H hH,
    fun t u => by rw [memoryLogPartition, mixturePartition_eq_trace_exp p H Kx Ky hp t u],
    memoryLogPartition_zero p H Kx Ky hsum htr, memory_first_deriv_t p H Kx Ky hsum htr,
    memory_first_deriv_u p H Kx Ky hsum htr, memory_hessian p H Kx Ky hp hsum hH hKx hKy htr,
    classical_summand_nonneg p H Kx hp, quantum_summand_nonneg H Kx hH hKx,
    shortedScore_def p H Kx Ky⟩

/-! ### Non-vacuity: blocks of different sizes -/

/-- Block sizes `d_0 = 1`, `d_1 = 2`. -/
abbrev exampleDims : Fin 2 → Type := fun ω => Fin (ω.val + 1)

/-- Maximally mixed blocks `ρ_ω = 1/d_ω`, i.e. `H_ω = −log(d_ω) · 1`. -/
noncomputable def exampleH (ω : Fin 2) : Matrix (exampleDims ω) (exampleDims ω) ℂ :=
  ((-Real.log ((ω.val : ℝ) + 1) : ℝ) : ℂ) • (1 : Matrix (exampleDims ω) (exampleDims ω) ℂ)

theorem exampleH_isHermitian (ω : Fin 2) : (exampleH ω).IsHermitian := by
  show (exampleH ω)ᴴ = exampleH ω
  rw [exampleH, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, Complex.star_def,
    Complex.conj_ofReal]

theorem exampleH_trace (ω : Fin 2) : (NormedSpace.exp (exampleH ω)).trace = 1 := by
  have h := exp_scalar_add (((-Real.log ((ω.val : ℝ) + 1) : ℝ) : ℂ))
    (0 : Matrix (exampleDims ω) (exampleDims ω) ℂ)
  rw [add_zero, NormedSpace.exp_zero] at h
  rw [exampleH, h, ← Complex.exp_eq_exp_ℂ, ← Complex.ofReal_exp, Real.exp_neg,
    Real.exp_log (by positivity), Matrix.trace_smul, Matrix.trace_one, smul_eq_mul]
  simp only [Fintype.card_fin]
  push_cast
  have : ((ω.val : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero ω.val
  field_simp

/-- The memory-short theorem applies to the two-branch state `½ (1) ⊕ ½ (½ I₂)` with
blocks of sizes `1` and `2`. -/
example (Kx Ky : (ω : Fin 2) → Matrix (exampleDims ω) (exampleDims ω) ℂ)
    (hKx : ∀ ω, (Kx ω).IsHermitian) (hKy : ∀ ω, (Ky ω).IsHermitian) :
    memoryLogPartition (fun _ => (1 / 2 : ℝ)) exampleH Kx Ky 0 0 = 0 ∧
    0 ≤ deriv (fun u => deriv (fun t =>
      memoryLogPartition (fun _ => (1 / 2 : ℝ)) exampleH Kx Kx t u) 0) 0 := by
  have hsum : ∑ _ω : Fin 2, (1 / 2 : ℝ) = 1 := by norm_num
  exact ⟨(memory_short_blocks (fun _ => (1 / 2 : ℝ)) exampleH Kx Ky (fun _ => by norm_num)
      hsum exampleH_isHermitian hKx hKy exampleH_trace).2.2.2.1,
    memory_hessian_diag_nonneg _ exampleH Kx (fun _ => by norm_num) hsum
      exampleH_isHermitian hKx exampleH_trace⟩

end RenewalMemoryBlocks
end RenewalGeometry
