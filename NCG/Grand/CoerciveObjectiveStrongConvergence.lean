/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.VariationalMinimizerValueConvergence
import Mathlib.Analysis.Convex.Strong

/-!
# Strong convergence from a coercive objective gap

If the gap between a recovery competitor and a stage minimizer controls their squared distance,
convergence of both objective values makes the minimizer asymptotic to the recovery sequence.
This is the quantitative strong-convexity bridge in the Mosco minimizer argument.
-/

open Filter Topology

noncomputable section

namespace NCG.VaryingHilbert.System

universe u v w

variable {K : Type u} [RCLike K]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace K (Hn n)]
variable (J : System (K := K) (H := H) (Hn := Hn))

/-- A coercive objective gap and a strongly convergent recovery sequence force strong convergence
of the compared sequence. -/
theorem stronglyConverges_of_recovery_of_coercive_objective_gap
    (Fn : (n : ℕ) → Hn n → ℝ) (x recovery : ∀ n, Hn n) (xlim : H)
    (L c : ℝ) (hc : 0 < c)
    (hrecoveryStrong : J.StronglyConverges recovery xlim)
    (hvalue : Tendsto (fun n ↦ Fn n (x n)) atTop (𝓝 L))
    (hrecoveryValue : Tendsto (fun n ↦ Fn n (recovery n)) atTop (𝓝 L))
    (hgap : ∀ n, c * ‖x n - recovery n‖ ^ 2 ≤
      Fn n (recovery n) - Fn n (x n)) :
    J.StronglyConverges x xlim := by
  have hgapTendsto : Tendsto
      (fun n ↦ Fn n (recovery n) - Fn n (x n)) atTop (𝓝 0) := by
    simpa using hrecoveryValue.sub hvalue
  have hsqUpper : ∀ n, ‖x n - recovery n‖ ^ 2 ≤
      c⁻¹ * (Fn n (recovery n) - Fn n (x n)) := by
    intro n
    calc
      ‖x n - recovery n‖ ^ 2 = c⁻¹ * (c * ‖x n - recovery n‖ ^ 2) := by
        field_simp
      _ ≤ c⁻¹ * (Fn n (recovery n) - Fn n (x n)) :=
        mul_le_mul_of_nonneg_left (hgap n) (le_of_lt (inv_pos.mpr hc))
  have hupperTendsto : Tendsto
      (fun n ↦ c⁻¹ * (Fn n (recovery n) - Fn n (x n))) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hgapTendsto
  have hsquare : Tendsto (fun n ↦ ‖x n - recovery n‖ ^ 2) atTop (𝓝 0) :=
    squeeze_zero (fun n ↦ sq_nonneg ‖x n - recovery n‖) hsqUpper hupperTendsto
  have hnormDiff : Tendsto (fun n ↦ ‖x n - recovery n‖) atTop (𝓝 0) := by
    have hsqrt := hsquare.sqrt
    simpa [Real.sqrt_sq (norm_nonneg _)] using hsqrt
  have hdiff : J.StronglyConverges (fun n ↦ x n - recovery n) 0 := by
    rw [StronglyConverges, tendsto_zero_iff_norm_tendsto_zero]
    convert hnormDiff using 1
    funext n
    exact (J.embedding n).norm_map (x n - recovery n)
  have hadd := hdiff.add J hrecoveryStrong
  simpa using hadd
/-- A global strongly convex functional has a quantitative gap above its minimizer. -/
theorem coercive_objective_gap_of_strongConvexOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → ℝ) (m : ℝ)
    (hstrong : StrongConvexOn Set.univ m F)
    (x y : E) (hmin : ∀ z, F x ≤ F z) :
    m / 4 * ‖x - y‖ ^ 2 ≤ F y - F x := by
  have hmid := hstrong.2 (Set.mem_univ x) (Set.mem_univ y)
    (show 0 ≤ (1 / 2 : ℝ) by norm_num)
    (show 0 ≤ (1 / 2 : ℝ) by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  have hxmin : F x ≤ F ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) :=
    hmin _
  simp only [smul_eq_mul] at hmid
  nlinarith [sq_nonneg ‖x - y‖]
/-- A positive strongly convex functional has at most one minimizer. -/
theorem eq_minimizer_of_strongConvexOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → ℝ) (m : ℝ) (hm : 0 < m)
    (hstrong : StrongConvexOn Set.univ m F)
    (x : E) (hmin : ∀ z, F x ≤ F z)
    (y : E) (hy : F y ≤ F x) :
    y = x := by
  have hgap := coercive_objective_gap_of_strongConvexOn
    F m hstrong x y hmin
  have hsquare : ‖x - y‖ ^ 2 = 0 := by
    nlinarith [sq_nonneg ‖x - y‖]
  have hnorm : ‖x - y‖ = 0 := (sq_eq_zero_iff).mp hsquare
  exact (sub_eq_zero.mp (norm_eq_zero.mp hnorm)).symm


/-- Stagewise strong convexity supplies the coercive recovery gap used by the convergence
theorem. -/
theorem stronglyConverges_of_recovery_of_strongConvex_objective
    [∀ n, NormedSpace ℝ (Hn n)]
    (Fn : (n : ℕ) → Hn n → ℝ) (x recovery : ∀ n, Hn n) (xlim : H)
    (L m : ℝ) (hm : 0 < m)
    (hstrong : ∀ n, StrongConvexOn Set.univ m (Fn n))
    (hmin : ∀ n z, Fn n (x n) ≤ Fn n z)
    (hrecoveryStrong : J.StronglyConverges recovery xlim)
    (hvalue : Tendsto (fun n ↦ Fn n (x n)) atTop (𝓝 L))
    (hrecoveryValue : Tendsto (fun n ↦ Fn n (recovery n)) atTop (𝓝 L)) :
    J.StronglyConverges x xlim := by
  apply stronglyConverges_of_recovery_of_coercive_objective_gap J Fn x recovery xlim
    L (m / 4) (div_pos hm (by norm_num)) hrecoveryStrong hvalue hrecoveryValue
  intro n
  exact coercive_objective_gap_of_strongConvexOn
    (Fn n) m (hstrong n) (x n) (recovery n) (hmin n)


/-- The full variational compactness package plus a coercive recovery gap directly yields strong
convergence of the stage minimizers. -/
theorem stronglyConverges_of_variational_minimizers_of_coercive_gap
    (Fn : (n : ℕ) → Hn n → ℝ) (Flim : H → ℝ)
    (x recovery : ∀ n, Hn n) (xlim : H)
    (hcompact : J.IsSequentiallyWeaklyPrecompact x)
    (hmin : ∀ n, Fn n (x n) ≤ Fn n (recovery n))
    (hrecoveryStrong : J.StronglyConverges recovery xlim)
    (hrecoveryValue : Tendsto (fun n ↦ Fn n (recovery n)) atTop (𝓝 (Flim xlim)))
    (B : ℝ) (hbelow : ∀ n, B ≤ Fn n (x n))
    (hclusterLower : ∀ (ns : ℕ → ℕ) (_hns : Tendsto ns atTop atTop)
      (ψ : ℕ → ℕ) (_hψ : StrictMono ψ) (y : H),
      (J.reindex (ns ∘ ψ)).WeaklyConverges (fun k ↦ x (ns (ψ k))) y →
        Flim y ≤ liminf (fun k ↦ Fn (ns (ψ k)) (x (ns (ψ k)))) atTop)
    (hunique : ∀ y : H, Flim y ≤ Flim xlim → y = xlim)
    (c : ℝ) (hc : 0 < c)
    (hgap : ∀ n, c * ‖x n - recovery n‖ ^ 2 ≤
      Fn n (recovery n) - Fn n (x n)) :
    J.StronglyConverges x xlim := by
  have hvalue := minimizerValue_tendsto_of_weakPrecompact J Fn Flim x recovery xlim
    hcompact hmin hrecoveryValue B hbelow hclusterLower hunique
  exact stronglyConverges_of_recovery_of_coercive_objective_gap J Fn x recovery xlim
    (Flim xlim) c hc hrecoveryStrong hvalue hrecoveryValue hgap

/-- Weak precompactness, variational liminf/recovery, uniqueness, and stagewise strong convexity
form a closed strong-convergence theorem for minimizing sequences. -/
theorem stronglyConverges_of_variational_minimizers_of_strongConvex
    [∀ n, NormedSpace ℝ (Hn n)]
    (Fn : (n : ℕ) → Hn n → ℝ) (Flim : H → ℝ)
    (x recovery : ∀ n, Hn n) (xlim : H)
    (hcompact : J.IsSequentiallyWeaklyPrecompact x)
    (hmin : ∀ n z, Fn n (x n) ≤ Fn n z)
    (hrecoveryStrong : J.StronglyConverges recovery xlim)
    (hrecoveryValue : Tendsto (fun n ↦ Fn n (recovery n)) atTop (𝓝 (Flim xlim)))
    (B : ℝ) (hbelow : ∀ n, B ≤ Fn n (x n))
    (hclusterLower : ∀ (ns : ℕ → ℕ) (_hns : Tendsto ns atTop atTop)
      (ψ : ℕ → ℕ) (_hψ : StrictMono ψ) (y : H),
      (J.reindex (ns ∘ ψ)).WeaklyConverges (fun k ↦ x (ns (ψ k))) y →
        Flim y ≤ liminf (fun k ↦ Fn (ns (ψ k)) (x (ns (ψ k)))) atTop)
    (hunique : ∀ y : H, Flim y ≤ Flim xlim → y = xlim)
    (m : ℝ) (hm : 0 < m)
    (hstrong : ∀ n, StrongConvexOn Set.univ m (Fn n)) :
    J.StronglyConverges x xlim := by
  have hvalue := minimizerValue_tendsto_of_weakPrecompact J Fn Flim x recovery xlim
    hcompact (fun n ↦ hmin n (recovery n)) hrecoveryValue B hbelow hclusterLower hunique
  exact stronglyConverges_of_recovery_of_strongConvex_objective J
    Fn x recovery xlim (Flim xlim) m hm hstrong hmin
      hrecoveryStrong hvalue hrecoveryValue

end NCG.VaryingHilbert.System
