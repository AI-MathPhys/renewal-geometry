/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.FiniteHermitianHeatSemigroup

/-!
# The entropic Hodge continuum: second variation and minimizing movements

Final machinery layer for `thm:entropic-Hodge-continuum`, on top of the proved
Fisher-window bound, kernel identification, `176/225` Poincaré floor
(`NCG.CoerciveHodgeOperator`), resolvent-step minimizing movement
(`NCG.resolvent_minimizer`), local Fisher Hessian
(`NCG.primitiveActionHessian_physical_eq_G0`), and the now-proved Grand-Tensor
Mosco equivalence (`thm:GT-Mosco`):

* `hessian_second_variation`: the second variation of the summed routed
  entropic functional at the primitive law is the sum of the local edge
  Fisher Hessians — the routed edge form `q_{U,G₀}`;
* `abs_exp_neg_sub_exp_neg_le` / `norm_finiteHermitianHeat_sub_le` /
  `heat_time_lipschitz`: the finite heat semigroup is Lipschitz in physical
  time with constant the spectral cap;
* `minimizing_movement_floor` (**the boxed clause**): on every fixed finite
  graph, the minimizing-movement iterates satisfy the quantitative bound
  `‖W_τ^{⌊t/τ⌋} − e^{−tL}‖ ≤ (√⌊t/τ⌋)⁻¹ + τ·B`, which tends to zero with
  `τ ↓ 0` uniformly for `t` in compact positive intervals.
-/

open Filter Topology Matrix
open scoped ComplexOrder Norms.L2Operator

noncomputable section

namespace NCG
namespace EntropicHodgeContinuum

/-! ### The second variation of the routed entropic functional -/

/-- **The Hessian assembly**: if every edge slice of the routed entropic
functional has derivative family `F' e` and local Fisher Hessian `q e` at the
primitive law, the summed functional has second variation `∑ e, q e` — the
routed edge form `q_{U,G₀}`. -/
theorem hessian_second_variation {ι : Type*} [Fintype ι]
    (F F' : ι → ℝ → ℝ) (q : ι → ℝ)
    (hF1 : ∀ e s, HasDerivAt (F e) (F' e s) s)
    (hF2 : ∀ e, HasDerivAt (F' e) (q e) 0) :
    (∀ s, HasDerivAt (fun s => ∑ e, F e s) (∑ e, F' e s) s) ∧
      HasDerivAt (fun s => ∑ e, F' e s) (∑ e, q e) 0 :=
  ⟨fun s => HasDerivAt.fun_sum fun e _ => hF1 e s,
    HasDerivAt.fun_sum fun e _ => hF2 e⟩

/-! ### The heat semigroup is Lipschitz in physical time -/

theorem abs_exp_neg_sub_exp_neg_le {ν B s t : ℝ} (hν : 0 ≤ ν) (hνB : ν ≤ B)
    (hs : 0 ≤ s) (hst : s ≤ t) :
    |Real.exp (-(t * ν)) - Real.exp (-(s * ν))| ≤ (t - s) * B := by
  have hmono : Real.exp (-(t * ν)) ≤ Real.exp (-(s * ν)) :=
    Real.exp_le_exp.mpr (by nlinarith)
  rw [abs_sub_comm, abs_of_nonneg (by linarith)]
  have hexp : (-(s * ν)) + (-((t - s) * ν)) = -(t * ν) := by ring
  have hsplit : Real.exp (-(s * ν)) - Real.exp (-(t * ν))
      = Real.exp (-(s * ν)) * (1 - Real.exp (-((t - s) * ν))) := by
    rw [mul_sub, mul_one, ← Real.exp_add, hexp]
  have hone : Real.exp (-(s * ν)) ≤ 1 := by
    have h := Real.exp_le_exp.mpr (show -(s * ν) ≤ 0 by nlinarith)
    simpa using h
  have hlin : 1 - Real.exp (-((t - s) * ν)) ≤ (t - s) * ν := by
    have h := Real.add_one_le_exp (-((t - s) * ν))
    linarith
  have hpos : 0 ≤ 1 - Real.exp (-((t - s) * ν)) := by
    have h := Real.exp_le_exp.mpr (show -((t - s) * ν) ≤ 0 by nlinarith)
    simpa using h
  calc Real.exp (-(s * ν)) - Real.exp (-(t * ν))
      = Real.exp (-(s * ν)) * (1 - Real.exp (-((t - s) * ν))) := hsplit
    _ ≤ 1 * ((t - s) * ν) :=
        mul_le_mul hone hlin hpos zero_le_one
    _ = (t - s) * ν := one_mul _
    _ ≤ (t - s) * B := by nlinarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Matrix-level time-Lipschitz bound for the canonical spectral heat
multiplier, with constant the spectral cap. -/
theorem norm_finiteHermitianHeat_sub_le {A : Matrix ι ι ℂ} (hA : A.PosSemidef)
    {B s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (hB0 : 0 ≤ B)
    (hB : ∀ i, hA.1.eigenvalues i ≤ B) :
    ‖NCG.ImplicitEuler.finiteHermitianHeat hA.1 t
        - NCG.ImplicitEuler.finiteHermitianHeat hA.1 s‖ ≤ (t - s) * B := by
  have hBnn : 0 ≤ (t - s) * B := mul_nonneg (by linarith) hB0
  unfold NCG.ImplicitEuler.finiteHermitianHeat
    NCG.ImplicitEuler.finiteUnitarySpectralHeat
  rw [← map_sub]
  change ‖(hA.1.eigenvectorUnitary : Matrix ι ι ℂ)
      * (NCG.ImplicitEuler.finiteSpectralHeat hA.1.eigenvalues t
          - NCG.ImplicitEuler.finiteSpectralHeat hA.1.eigenvalues s)
      * (star hA.1.eigenvectorUnitary : Matrix ι ι ℂ)‖ ≤ _
  rw [← Unitary.coe_star, CStarRing.norm_mul_coe_unitary,
    CStarRing.norm_coe_unitary_mul]
  have hdiag : NCG.ImplicitEuler.finiteSpectralHeat hA.1.eigenvalues t
      - NCG.ImplicitEuler.finiteSpectralHeat hA.1.eigenvalues s
      = Matrix.diagonal (fun i =>
          ((Real.exp (-(t * hA.1.eigenvalues i))
            - Real.exp (-(s * hA.1.eigenvalues i)) : ℝ) : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [NCG.ImplicitEuler.finiteSpectralHeat]
    · simp [NCG.ImplicitEuler.finiteSpectralHeat, hij]
  rw [hdiag, Matrix.l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg hBnn).2 fun i => ?_
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact abs_exp_neg_sub_exp_neg_le (hA.eigenvalues_nonneg i) (hB i) hs hst

/-- **The heat semigroup is Lipschitz in physical time** on every fixed
finite graph, with constant the spectral cap. -/
theorem heat_time_lipschitz {A : Matrix ι ι ℂ} (hA : A.PosSemidef)
    {B s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (hB0 : 0 ≤ B)
    (hB : ∀ i, hA.1.eigenvalues i ≤ B) :
    ‖NCG.ImplicitEuler.finiteHermitianHeatOperator hA.1 t
        - NCG.ImplicitEuler.finiteHermitianHeatOperator hA.1 s‖
      ≤ (t - s) * B := by
  unfold NCG.ImplicitEuler.finiteHermitianHeatOperator
  rw [← map_sub]
  change ‖NCG.ImplicitEuler.finiteHermitianHeat hA.1 t
      - NCG.ImplicitEuler.finiteHermitianHeat hA.1 s‖ ≤ _
  exact norm_finiteHermitianHeat_sub_le hA hs hst hB0 hB

/-! ### The boxed minimizing-movement convergence -/

/-- **The boxed clause `W_τ^{⌊t/τ⌋} → e^{−tL}`**: on every fixed finite
graph, the minimizing-movement iterates of the resolvent step
`W_τ = (I+τL)^{-1}` satisfy the quantitative operator-norm bound
`‖W_τ^{⌊t/τ⌋} − e^{−tL}‖ ≤ (√⌊t/τ⌋)⁻¹ + τ·B`, which tends to zero with
`τ ↓ 0`, uniformly for `t` in compact positive intervals. -/
theorem minimizing_movement_floor {A : Matrix ι ι ℂ} (hA : A.PosSemidef)
    {B τ t : ℝ} (hτ : 0 < τ) (hτt : τ ≤ t) (hB0 : 0 ≤ B)
    (hB : ∀ i, hA.1.eigenvalues i ≤ B) :
    ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)
        (((1 : Matrix ι ι ℂ) + ((τ : ℂ) • A))⁻¹ ^ ⌊t / τ⌋₊)
      - NormedSpace.exp ((-(t : ℂ)) •
          Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A)‖
      ≤ (Real.sqrt (⌊t / τ⌋₊ : ℝ))⁻¹ + τ * B := by
  set k : ℕ := ⌊t / τ⌋₊ with hkdef
  have ht0 : 0 < t := lt_of_lt_of_le hτ hτt
  have hk1 : 1 ≤ k := by
    rw [hkdef]
    exact Nat.le_floor (by
      rw [Nat.cast_one, le_div_iff₀ hτ, one_mul]
      exact hτt)
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
  have hfl : (k : ℝ) ≤ t / τ := by
    rw [hkdef]
    exact Nat.floor_le (by positivity)
  have hτk_le : τ * k ≤ t := by
    calc τ * k ≤ τ * (t / τ) := mul_le_mul_of_nonneg_left hfl hτ.le
      _ = t := by field_simp
  have ht_lt : t - τ * k ≤ τ := by
    have hlt : t / τ < (k : ℝ) + 1 := by
      rw [hkdef]
      exact_mod_cast Nat.lt_floor_add_one (t / τ)
    have hlt2 : t < ((k : ℝ) + 1) * τ := (div_lt_iff₀ hτ).mp hlt
    nlinarith
  have hW : Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ)
      (((1 : Matrix ι ι ℂ) + ((τ : ℂ) • A))⁻¹ ^ k)
      = NCG.ImplicitEuler.finiteHermitianEulerResolventOperator A (τ * k) k := by
    unfold NCG.ImplicitEuler.finiteHermitianEulerResolventOperator
    rw [show ((τ * (k : ℝ)) / (k : ℝ)) = τ from
      mul_div_cancel_right₀ τ (ne_of_gt hk0)]
  rw [hW]
  have h1 := NCG.ImplicitEuler.norm_finiteHermitianEulerResolventOperator_sub_exp_le_inv_sqrt
    hA (τ * k) k (by positivity) (by omega)
  have h2 : ‖NormedSpace.exp ((-((τ * (k : ℝ) : ℝ) : ℂ)) •
        Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A)
      - NormedSpace.exp ((-(t : ℂ)) •
        Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A)‖ ≤ τ * B := by
    rw [← NCG.ImplicitEuler.finiteHermitianHeatOperator_eq_exp_smul hA.1 (τ * k),
      ← NCG.ImplicitEuler.finiteHermitianHeatOperator_eq_exp_smul hA.1 t]
    calc ‖NCG.ImplicitEuler.finiteHermitianHeatOperator hA.1 (τ * k)
          - NCG.ImplicitEuler.finiteHermitianHeatOperator hA.1 t‖
        = ‖NCG.ImplicitEuler.finiteHermitianHeatOperator hA.1 t
          - NCG.ImplicitEuler.finiteHermitianHeatOperator hA.1 (τ * k)‖ :=
          norm_sub_rev _ _
      _ ≤ (t - τ * k) * B :=
          heat_time_lipschitz hA (by positivity) hτk_le hB0 hB
      _ ≤ τ * B := by nlinarith
  calc ‖NCG.ImplicitEuler.finiteHermitianEulerResolventOperator A (τ * k) k
        - NormedSpace.exp ((-(t : ℂ)) •
          Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A)‖
      = dist (NCG.ImplicitEuler.finiteHermitianEulerResolventOperator A (τ * k) k)
          (NormedSpace.exp ((-(t : ℂ)) •
            Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A)) :=
        (dist_eq_norm _ _).symm
    _ ≤ dist (NCG.ImplicitEuler.finiteHermitianEulerResolventOperator A (τ * k) k)
          (NormedSpace.exp ((-((τ * (k : ℝ) : ℝ) : ℂ)) •
            Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A))
        + dist (NormedSpace.exp ((-((τ * (k : ℝ) : ℝ) : ℂ)) •
            Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A))
          (NormedSpace.exp ((-(t : ℂ)) •
            Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) A)) :=
        dist_triangle _ _ _
    _ ≤ (Real.sqrt (k : ℝ))⁻¹ + τ * B := by
        rw [dist_eq_norm, dist_eq_norm]
        exact add_le_add h1 h2

end EntropicHodgeContinuum
end NCG
