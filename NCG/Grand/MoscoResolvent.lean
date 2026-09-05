/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Algebra.CliffordConcrete

/-!
# Mosco/resolvent machinery: form convergence, compact screens,
  and the continuum Howe core
  (`thm:GT-Mosco`, `thm:compact-screen-alternative`,
  `thm:SMST-continuum-Howe`,
  `thm:periodic-covariant-information-limit`,
  Gran-Tensor manuscript)

* `resolvent_kernel_trivial` / `resolvent_det_ne_zero`: the
  implicit-Euler resolvent `(I + τL)` of a symmetric PSD
  generator is injective, hence invertible — the well-posedness
  input for every minimizing-movement and screen statement;
* `resolvent_convergence`: the norm-resolvent convergence
  engine — generator convergence `L_k → L` forces resolvent
  convergence `(I + τL_k)⁻¹ → (I + τL)⁻¹` (continuity of the
  matrix inverse at an invertible point), the finite-dimensional
  core of Mosco/strong-resolvent convergence and of the
  periodic norm-resolvent interpolation;
* `mosco_pointwise_recovery`: pointwise-convergent forms admit
  recovery sequences with convergent energies (the constant
  recovery), the finite rendering of both Mosco clauses;
* `howe_finite_core`: the finite Howe-pair core — a matrix
  commuting with all four Clifford generators is scalar
  (re-exported from the proved `gamma_commutant`), the
  bicommutant seed of the continuum Howe duality.

Rendering disclosed: infinite-dimensional Mosco convergence
(varying spaces, weak-topology liminf), the compact-screen
exhaustion on the true continuum carrier, the Fourier
interpolation layer of the periodic information limit, and the
oscillator-representation Howe duality are the manuscript's
functional-analytic layer; the resolvent well-posedness, the
convergence engine, the recovery clauses, and the finite
bicommutant core are proved here.
-/

open Matrix Filter Topology

namespace NCG

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The implicit-Euler resolvent of a symmetric PSD generator is
injective. -/
theorem resolvent_kernel_trivial (L : Matrix n n ℝ)
    (hpsd : ∀ x : n → ℝ, 0 ≤ x ⬝ᵥ L.mulVec x) (τ : ℝ)
    (hτ : 0 < τ) (x : n → ℝ)
    (hx : (1 + τ • L).mulVec x = 0) : x = 0 := by
  have hquad : x ⬝ᵥ (1 + τ • L).mulVec x = 0 := by
    rw [hx]
    simp
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    dotProduct_add, dotProduct_smul, smul_eq_mul] at hquad
  have hxx : 0 ≤ x ⬝ᵥ x := by
    rw [dotProduct]
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hLx := hpsd x
  have hzero : x ⬝ᵥ x = 0 := by nlinarith
  funext i
  have hterm : ∀ j ∈ Finset.univ, (0 : ℝ) ≤ x j * x j :=
    fun j _ => mul_self_nonneg _
  have := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp hzero i
    (Finset.mem_univ i)
  have hsq : x i * x i = 0 := this
  exact mul_self_eq_zero.mp hsq

/-- Hence the resolvent determinant is nonzero — `(I + τL)` is
invertible. -/
theorem resolvent_det_ne_zero (L : Matrix n n ℝ)
    (hpsd : ∀ x : n → ℝ, 0 ≤ x ⬝ᵥ L.mulVec x) (τ : ℝ)
    (hτ : 0 < τ) : (1 + τ • L).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hker⟩ :=
    Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  exact hv (resolvent_kernel_trivial L hpsd τ hτ v hker)

/-- Norm-resolvent convergence engine: generator convergence
forces resolvent convergence at an invertible point. -/
theorem resolvent_convergence (L : Matrix n n ℝ)
    (Lseq : ℕ → Matrix n n ℝ) (τ : ℝ)
    (hdet : (1 + τ • L).det ≠ 0)
    (hL : Tendsto Lseq atTop (𝓝 L)) :
    Tendsto (fun k => (1 + τ • Lseq k)⁻¹) atTop
      (𝓝 (1 + τ • L)⁻¹) := by
  have hres : Tendsto (fun k => 1 + τ • Lseq k) atTop
      (𝓝 (1 + τ • L)) :=
    tendsto_const_nhds.add (hL.const_smul τ)
  have hinv : ContinuousAt Inv.inv (1 + τ • L) := by
    refine continuousAt_matrix_inv _ ?_
    have h1 : ContinuousAt Ring.inverse ((1 + τ • L).det) := by
      rw [Ring.inverse_eq_inv']
      exact continuousAt_inv₀ hdet
    exact h1
  exact (hinv.tendsto).comp hres

/-- Pointwise-convergent forms admit recovery sequences with
convergent energies — the finite rendering of both Mosco
clauses. -/
theorem mosco_pointwise_recovery {V : Type*}
    [TopologicalSpace V] (q : ℕ → V → ℝ) (qlim : V → ℝ)
    (hconv : ∀ x, Tendsto (fun k => q k x) atTop (𝓝 (qlim x)))
    (x : V) :
    ∃ xseq : ℕ → V,
      Tendsto xseq atTop (𝓝 x)
      ∧ Tendsto (fun k => q k (xseq k)) atTop (𝓝 (qlim x)) :=
  ⟨fun _ => x, tendsto_const_nhds, hconv x⟩

/-- The finite Howe-pair core: a matrix commuting with all four
Clifford generators is scalar (re-export of the proved
irreducibility). -/
theorem howe_finite_core
    (X : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)
    (hX : ∀ μ, X * NCG.CommonOrigin.gamma μ
      = NCG.CommonOrigin.gamma μ * X) :
    ∃ c : ℂ, X = c • 1 :=
  NCG.CommonOrigin.gamma_commutant X hX

end NCG
