/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Spectralization.ModularAffinityReversalPacketExact
import RenewalGeometry.Spectralization.StationaryRenewalGraphCurrentFibreExact
import RenewalGeometry.DiscreteAnalysis.CycleProjector
/-!
# Nonlinear Hodge theorem for stationary affinities

This file covers `thm:supp-nonlinear-Hodge` of `papers/predictive_spectral_geometry`.

Fix a real oriented incidence matrix `B : Matrix V E ℝ` of a connected graph
(`IsConnectedIncidence B`: `Bᵀ 1 = 0` and only constant potentials have zero
gradient) and positive conductances `c`.  For a representative `a₀ : E → ℝ` of a
class `α ∈ H¹(G;ℝ) = ℝ^E / Ran Bᵀ`, the convex affinity functional is

  `𝓕_α(φ) = Σ_e c_e log cosh(a₀_e + (Bᵀφ)_e)`

on mean-zero vertex potentials `φ`.  We prove

* coercivity, in the form `𝓕_α(φ) + (Σ_x φ_x)² → ∞` along the cocompact filter
  (`tendsto_regularizedFunctional_cocompact`);
* existence and uniqueness of the mean-zero minimiser `φ_α`
  (`exists_meanZeroMinimizer`, `meanZeroMinimizer_unique`);
* for the minimiser, `a_α = a₀ + Bᵀφ_α`, `j_α = c tanh a_α` is divergence free,
  lies in the current fibre `𝒥(G,c)`, and has modular class `[a_α] = α`
  (`currentOfPotential_mem_currentFibre`, `isExact_affinity_currentOfPotential_sub`);
* `j_α` is the unique current with modular class `α` (`existsUnique_current_of_class`);
* hence the affinity map `𝔄 : 𝒥(G,c) → H¹(G;ℝ)`, `j ↦ [artanh(j/c)]`, is a
  bijection (`affinityClass_bijOn`); the packaged statement is `nonlinear_hodge`.

The real hypotheses `IsConnectedIncidence B` follow from the complex connected-incidence
predicate of `DiscreteAnalysis/CycleProjector` (`isConnectedIncidence_of_complex`) and hence
from graph connectedness of a simple orientation (`isConnectedIncidence_incidenceReal`,
`existsUnique_current_of_connected`).

Uniqueness of the minimiser is obtained from the Euler equation and the strict
monotonicity of `tanh` (via `current_eq_of_affinity_class_eq`) rather than from
strict convexity of `log cosh`; the smoothness of `𝔄⁻¹` (the "diffeomorphism"
clause) is not formalised here.
-/

open Matrix Finset Filter Topology

namespace RenewalGeometry
namespace NonlinearAffinityHodge

open ModularAffinityReversalPacket

variable {V E : Type*} [Fintype V] [Fintype E]

/-! ## Connected incidence matrices and the affinity functional -/

/-- Real connected-incidence hypotheses for an oriented incidence matrix:
`Bᵀ 1 = 0` (every column has one `+1` and one `-1`) and only constant vertex
potentials have zero edge gradient (connectedness). -/
structure IsConnectedIncidence (B : Matrix V E ℝ) : Prop where
  transpose_mulVec_one : Bᵀ *ᵥ (fun _ : V => (1 : ℝ)) = 0
  eq_const_of_transpose_mulVec_eq_zero :
    ∀ φ : V → ℝ, Bᵀ *ᵥ φ = 0 → ∃ t : ℝ, φ = fun _ => t

/-- The convex affinity functional `𝓕_α(φ) = Σ_e c_e log cosh(a₀_e + (Bᵀφ)_e)`
(eq:supp-convex-affinity-functional). -/
noncomputable def affinityFunctional (B : Matrix V E ℝ) (c a₀ : E → ℝ) (φ : V → ℝ) : ℝ :=
  ∑ e, c e * Real.log (Real.cosh (a₀ e + (Bᵀ *ᵥ φ) e))

/-- The affinity functional penalised by the squared mean, `𝓕_α(φ) + (Σ_x φ_x)²`;
its global minimisers are exactly the mean-zero minimisers of `𝓕_α`. -/
noncomputable def regularizedFunctional (B : Matrix V E ℝ) (c a₀ : E → ℝ) (φ : V → ℝ) : ℝ :=
  affinityFunctional B c a₀ φ + (∑ x, φ x) ^ 2

/-- The current produced by a vertex potential, `j_e = c_e tanh(a₀_e + (Bᵀφ)_e)`
(eq:supp-affinity-inverse). -/
noncomputable def currentOfPotential (B : Matrix V E ℝ) (c a₀ : E → ℝ) (φ : V → ℝ) :
    E → ℝ :=
  fun e => c e * Real.tanh (a₀ e + (Bᵀ *ᵥ φ) e)

/-- A mean-zero potential minimising `𝓕_α` over all mean-zero potentials. -/
def IsMeanZeroMinimizer (B : Matrix V E ℝ) (c a₀ : E → ℝ) (φ : V → ℝ) : Prop :=
  ∑ x, φ x = 0 ∧
    ∀ ψ : V → ℝ, ∑ x, ψ x = 0 → affinityFunctional B c a₀ φ ≤ affinityFunctional B c a₀ ψ

/-! ## Elementary bounds -/

/-- `log cosh t ≥ |t| - log 2`. -/
theorem abs_sub_log_two_le_log_cosh (t : ℝ) : |t| - Real.log 2 ≤ Real.log (Real.cosh t) := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hexp : Real.exp |t| ≤ 2 * Real.cosh t := by
    rw [Real.cosh_eq]
    rcases le_total 0 t with h | h
    · rw [abs_of_nonneg h]; have := Real.exp_pos (-t); linarith
    · rw [abs_of_nonpos h]; have := Real.exp_pos t; linarith
  have hcosh := Real.cosh_pos t
  have : |t| ≤ Real.log 2 + Real.log (Real.cosh t) := by
    rw [← Real.log_mul h2.ne' hcosh.ne', ← Real.log_exp |t|]
    exact Real.log_le_log (Real.exp_pos _) hexp
  linarith

/-- The sup norm of a finite real vector is bounded by its `ℓ¹` norm. -/
theorem pi_norm_le_sum_abs (v : E → ℝ) : ‖v‖ ≤ ∑ e, |v e| := by
  rw [pi_norm_le_iff_of_nonneg (sum_nonneg fun e _ => abs_nonneg _)]
  intro e
  rw [Real.norm_eq_abs]
  exact single_le_sum (fun e _ => abs_nonneg (v e)) (mem_univ e)

/-- Positive conductances on a finite edge set are bounded below by a positive constant. -/
theorem exists_pos_le_conductance {c : E → ℝ} (hc : ∀ e, 0 < c e) :
    ∃ κ > 0, ∀ e, κ ≤ c e := by
  rcases isEmpty_or_nonempty E with h | h
  · exact ⟨1, one_pos, fun e => (h.false e).elim⟩
  · obtain ⟨e₀, -, he₀⟩ := exists_min_image univ c univ_nonempty
    exact ⟨c e₀, hc e₀, fun e => he₀ e (mem_univ e)⟩

variable {B : Matrix V E ℝ} {c a₀ : E → ℝ}

/-- The affinity functional is continuous. -/
theorem continuous_affinityFunctional (B : Matrix V E ℝ) (c a₀ : E → ℝ) :
    Continuous (affinityFunctional B c a₀) := by
  unfold affinityFunctional
  refine continuous_finsetSum _ fun e _ => ?_
  refine continuous_const.mul (Continuous.log ?_ fun φ => (Real.cosh_pos _).ne')
  refine Real.continuous_cosh.comp (continuous_const.add ?_)
  exact (continuous_apply e).comp (Matrix.mulVecLin Bᵀ).continuous_of_finiteDimensional

/-- The regularised functional is continuous. -/
theorem continuous_regularizedFunctional (B : Matrix V E ℝ) (c a₀ : E → ℝ) :
    Continuous (regularizedFunctional B c a₀) := by
  unfold regularizedFunctional
  exact (continuous_affinityFunctional B c a₀).add
    ((continuous_finsetSum _ fun x _ => continuous_apply x).pow 2)

/-- Lower bound `𝓕_α(φ) ≥ κ ‖Bᵀφ‖ - (κ Σ|a₀| + log 2 · Σ c)` for `0 < κ ≤ c`. -/
theorem le_affinityFunctional (hc : ∀ e, 0 < c e) {κ : ℝ} (hκ : 0 < κ)
    (hκc : ∀ e, κ ≤ c e) (φ : V → ℝ) :
    κ * ‖Bᵀ *ᵥ φ‖ - (κ * ∑ e, |a₀ e| + Real.log 2 * ∑ e, c e) ≤
      affinityFunctional B c a₀ φ := by
  set x : E → ℝ := fun e => a₀ e + (Bᵀ *ᵥ φ) e with hx
  have h1 : ∀ e, c e * (|x e| - Real.log 2) ≤ c e * Real.log (Real.cosh (x e)) :=
    fun e => mul_le_mul_of_nonneg_left (abs_sub_log_two_le_log_cosh _) (hc e).le
  have h2 : ∀ e, κ * (|(Bᵀ *ᵥ φ) e| - |a₀ e|) ≤ c e * |x e| := by
    intro e
    have hy : |(Bᵀ *ᵥ φ) e| - |a₀ e| ≤ |x e| := by
      have : (Bᵀ *ᵥ φ) e = x e - a₀ e := by simp [hx]
      rw [this]
      have := abs_sub (x e) (a₀ e)
      linarith
    calc κ * (|(Bᵀ *ᵥ φ) e| - |a₀ e|) ≤ κ * |x e| := mul_le_mul_of_nonneg_left hy hκ.le
      _ ≤ c e * |x e| := mul_le_mul_of_nonneg_right (hκc e) (abs_nonneg _)
  have hA : ∑ e, c e * (|x e| - Real.log 2) ≤ affinityFunctional B c a₀ φ :=
    sum_le_sum fun e _ => h1 e
  have hB : ∑ e, κ * (|(Bᵀ *ᵥ φ) e| - |a₀ e|) ≤ ∑ e, c e * |x e| :=
    sum_le_sum fun e _ => h2 e
  have hC : ‖Bᵀ *ᵥ φ‖ ≤ ∑ e, |(Bᵀ *ᵥ φ) e| := pi_norm_le_sum_abs _
  have eA : ∑ e, c e * (|x e| - Real.log 2) = ∑ e, c e * |x e| - Real.log 2 * ∑ e, c e := by
    rw [mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun e _ => by ring
  have eB : ∑ e, κ * (|(Bᵀ *ᵥ φ) e| - |a₀ e|) =
      κ * ∑ e, |(Bᵀ *ᵥ φ) e| - κ * ∑ e, |a₀ e| := by
    rw [mul_sum, mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun e _ => by ring
  have hD := mul_le_mul_of_nonneg_left hC hκ.le
  linarith

/-! ## Coercivity -/

/-- The vertex-sum functional as a linear map. -/
def sumLinear (V : Type*) [Fintype V] : (V → ℝ) →ₗ[ℝ] ℝ where
  toFun φ := ∑ x, φ x
  map_add' φ ψ := by simp [sum_add_distrib]
  map_smul' t φ := by simp [mul_sum]

/-- The gradient-and-mean map `φ ↦ (Bᵀφ, Σ_x φ_x)`. -/
def gradientMean (B : Matrix V E ℝ) : (V → ℝ) →ₗ[ℝ] (E → ℝ) × ℝ :=
  LinearMap.prod (Matrix.mulVecLin Bᵀ) (sumLinear V)

/-- For a connected incidence the gradient-and-mean map is injective. -/
theorem gradientMean_ker (hB : IsConnectedIncidence B) :
    LinearMap.ker (gradientMean B) = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro φ hφ
  have h1 : Bᵀ *ᵥ φ = 0 := congrArg Prod.fst hφ
  have h2 : ∑ x, φ x = 0 := congrArg Prod.snd hφ
  obtain ⟨t, rfl⟩ := hB.eq_const_of_transpose_mulVec_eq_zero φ h1
  rcases isEmpty_or_nonempty V with hV | hV
  · exact Subsingleton.elim _ _
  · simp only [sum_const, card_univ, nsmul_eq_mul] at h2
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
    · funext x; simp [h]

/-- Poincaré-type estimate: `‖φ‖ ≤ K (‖Bᵀφ‖ + |Σ_x φ_x|)` for a connected incidence. -/
theorem exists_norm_le_mul_gradient_add_mean (hB : IsConnectedIncidence B) :
    ∃ K > (0 : ℝ), ∀ φ : V → ℝ, ‖φ‖ ≤ K * (‖Bᵀ *ᵥ φ‖ + |∑ x, φ x|) := by
  obtain ⟨K, hK, hL⟩ := (gradientMean B).exists_antilipschitzWith (gradientMean_ker hB)
  refine ⟨K, NNReal.coe_pos.mpr hK, fun φ => ?_⟩
  have h := hL.le_mul_norm (map_zero _) φ
  have hprod : ‖gradientMean B φ‖ ≤ ‖Bᵀ *ᵥ φ‖ + |∑ x, φ x| := by
    rw [Prod.norm_def]
    refine max_le ?_ ?_
    · exact le_add_of_nonneg_right (abs_nonneg _)
    · rw [Real.norm_eq_abs]
      exact le_add_of_nonneg_left (norm_nonneg _)
  calc ‖φ‖ ≤ K * ‖gradientMean B φ‖ := h
    _ ≤ K * (‖Bᵀ *ᵥ φ‖ + |∑ x, φ x|) := mul_le_mul_of_nonneg_left hprod K.2

/-- Coercivity (thm:supp-nonlinear-Hodge): the regularised affinity functional tends
to `+∞` away from compact sets of potentials. -/
theorem tendsto_regularizedFunctional_cocompact (hB : IsConnectedIncidence B)
    (hc : ∀ e, 0 < c e) (a₀ : E → ℝ) :
    Tendsto (regularizedFunctional B c a₀) (cocompact (V → ℝ)) atTop := by
  obtain ⟨κ, hκ, hκc⟩ := exists_pos_le_conductance hc
  obtain ⟨K, hK, hKle⟩ := exists_norm_le_mul_gradient_add_mean hB
  set κ' := min κ 1 with hκ'def
  have hκ' : 0 < κ' := lt_min hκ one_pos
  set C : ℝ := κ * ∑ e, |a₀ e| + Real.log 2 * ∑ e, c e + 1 with hC
  have hlow : ∀ φ, κ' / K * ‖φ‖ + (-C) ≤ regularizedFunctional B c a₀ φ := by
    intro φ
    have h1 := le_affinityFunctional (B := B) (a₀ := a₀) hc hκ hκc φ
    have h2 : |∑ x, φ x| - 1 ≤ (∑ x, φ x) ^ 2 := by
      nlinarith [sq_nonneg (|∑ x, φ x| - 1 / 2), sq_abs (∑ x, φ x)]
    have h3 := hKle φ
    have h4 : κ' / K * ‖φ‖ ≤ κ' * (‖Bᵀ *ᵥ φ‖ + |∑ x, φ x|) := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hK]
      nlinarith [h3, hκ'.le]
    have h5 : κ' * ‖Bᵀ *ᵥ φ‖ ≤ κ * ‖Bᵀ *ᵥ φ‖ :=
      mul_le_mul_of_nonneg_right (min_le_left _ _) (norm_nonneg _)
    have h6 : κ' * |∑ x, φ x| ≤ |∑ x, φ x| := by
      have := min_le_right κ 1
      nlinarith [abs_nonneg (∑ x, φ x)]
    unfold regularizedFunctional
    linarith
  refine tendsto_atTop_mono hlow ?_
  have hnorm : Tendsto (fun φ : V → ℝ => ‖φ‖) (cocompact (V → ℝ)) atTop :=
    tendsto_norm_cocompact_atTop
  exact tendsto_atTop_add_const_right _ (-C) (hnorm.const_mul_atTop (div_pos hκ' hK))

/-- The regularised functional attains a global minimum. -/
theorem exists_regularizedFunctional_min (hB : IsConnectedIncidence B) (hc : ∀ e, 0 < c e)
    (a₀ : E → ℝ) :
    ∃ φ : V → ℝ, ∀ ψ, regularizedFunctional B c a₀ φ ≤ regularizedFunctional B c a₀ ψ :=
  (continuous_regularizedFunctional B c a₀).exists_forall_le
    (tendsto_regularizedFunctional_cocompact hB hc a₀)

/-! ## The Euler equation -/

/-- Directional derivative of `𝓕_α` at `φ` in direction `ψ`:
`Σ_e c_e tanh(a_e) (Bᵀψ)_e = ⟨j, Bᵀψ⟩`. -/
theorem hasDerivAt_affinityFunctional_line (B : Matrix V E ℝ) (c a₀ : E → ℝ) (φ ψ : V → ℝ) :
    HasDerivAt (fun t : ℝ => affinityFunctional B c a₀ (φ + t • ψ))
      (∑ e, currentOfPotential B c a₀ φ e * (Bᵀ *ᵥ ψ) e) 0 := by
  have hline : (fun t : ℝ => affinityFunctional B c a₀ (φ + t • ψ)) =
      fun t => ∑ e, c e * Real.log (Real.cosh (a₀ e + (Bᵀ *ᵥ φ) e + t * (Bᵀ *ᵥ ψ) e)) := by
    funext t
    unfold affinityFunctional
    refine sum_congr rfl fun e _ => ?_
    rw [mulVec_add, mulVec_smul]
    simp [add_assoc]
  rw [hline]
  refine HasDerivAt.fun_sum (u := univ)
    (A := fun e t => c e * Real.log (Real.cosh (a₀ e + (Bᵀ *ᵥ φ) e + t * (Bᵀ *ᵥ ψ) e)))
    (A' := fun e => currentOfPotential B c a₀ φ e * (Bᵀ *ᵥ ψ) e) fun e _ => ?_
  have h1 : HasDerivAt (fun t : ℝ => a₀ e + (Bᵀ *ᵥ φ) e + t * (Bᵀ *ᵥ ψ) e) ((Bᵀ *ᵥ ψ) e) 0 :=
    (hasDerivAt_mul_const _).const_add _
  have h2 := (Real.hasDerivAt_cosh _).comp (0 : ℝ) h1
  have h3 := h2.log (Real.cosh_pos _).ne'
  have h4 := h3.const_mul (c e)
  refine h4.congr_deriv ?_
  simp only [Function.comp_apply, zero_mul, add_zero, currentOfPotential,
    Real.tanh_eq_sinh_div_cosh]
  ring

/-- Directional derivative of the regularised functional. -/
theorem hasDerivAt_regularizedFunctional_line (B : Matrix V E ℝ) (c a₀ : E → ℝ)
    (φ ψ : V → ℝ) :
    HasDerivAt (fun t : ℝ => regularizedFunctional B c a₀ (φ + t • ψ))
      (∑ e, currentOfPotential B c a₀ φ e * (Bᵀ *ᵥ ψ) e +
        2 * (∑ x, φ x) * (∑ x, ψ x)) 0 := by
  have hsq : HasDerivAt (fun t : ℝ => (∑ x, (φ + t • ψ) x) ^ 2)
      (2 * (∑ x, φ x) * (∑ x, ψ x)) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => ∑ x, φ x + t * ∑ x, ψ x) (∑ x, ψ x) 0 :=
      (hasDerivAt_mul_const _).const_add _
    have hfun : (fun t : ℝ => (∑ x, (φ + t • ψ) x) ^ 2) =
        fun t => (∑ x, φ x + t * ∑ x, ψ x) * (∑ x, φ x + t * ∑ x, ψ x) := by
      funext t
      simp [sum_add_distrib, mul_sum, sq]
    rw [hfun]
    exact (h1.mul h1).congr_deriv (by simp; ring)
  exact (hasDerivAt_affinityFunctional_line B c a₀ φ ψ).add hsq

/-- The vertex gradient of any potential vanishes when there are no vertices. -/
theorem transpose_mulVec_eq_zero_of_isEmpty [IsEmpty V] (ψ : V → ℝ) : Bᵀ *ᵥ ψ = 0 := by
  funext e
  simp [mulVec, dotProduct]

/-- If `⟨j, Bᵀψ⟩ = 0` for every potential `ψ`, then `Bj = 0`. -/
theorem mulVec_eq_zero_of_forall_pairing {j : E → ℝ}
    (h : ∀ ψ : V → ℝ, ∑ e, j e * (Bᵀ *ᵥ ψ) e = 0) : B *ᵥ j = 0 := by
  have hdiv : ∀ ψ : V → ℝ, ψ ⬝ᵥ (B *ᵥ j) = 0 := by
    intro ψ
    rw [dotProduct_mulVec, ← mulVec_transpose]
    have := h ψ
    simp only [dotProduct]
    rw [← this]
    exact sum_congr rfl fun e _ => mul_comm _ _
  exact dotProduct_self_eq_zero.mp (hdiv _)

/-- A global minimiser of the regularised functional has zero mean and produces a
divergence-free current. -/
theorem sum_eq_zero_and_mulVec_eq_zero_of_regularized_min (hB : IsConnectedIncidence B)
    {φ : V → ℝ}
    (hmin : ∀ ψ, regularizedFunctional B c a₀ φ ≤ regularizedFunctional B c a₀ ψ) :
    ∑ x, φ x = 0 ∧ B *ᵥ currentOfPotential B c a₀ φ = 0 := by
  have hcrit : ∀ ψ : V → ℝ, ∑ e, currentOfPotential B c a₀ φ e * (Bᵀ *ᵥ ψ) e +
      2 * (∑ x, φ x) * (∑ x, ψ x) = 0 := by
    intro ψ
    have hloc : IsLocalMin (fun t : ℝ => regularizedFunctional B c a₀ (φ + t • ψ)) 0 :=
      Filter.Eventually.of_forall fun t => by simpa using hmin (φ + t • ψ)
    exact hloc.hasDerivAt_eq_zero (hasDerivAt_regularizedFunctional_line B c a₀ φ ψ)
  have hsum : ∑ x, φ x = 0 := by
    have h := hcrit (fun _ => 1)
    rw [hB.transpose_mulVec_one] at h
    simp only [Pi.zero_apply, mul_zero, sum_const_zero, zero_add, sum_const, card_univ,
      nsmul_eq_mul, mul_one] at h
    rcases isEmpty_or_nonempty V with hV | hV
    · simp
    · rcases mul_eq_zero.mp h with h | h
      · rcases mul_eq_zero.mp h with h | h
        · norm_num at h
        · exact h
      · exact absurd h (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  refine ⟨hsum, mulVec_eq_zero_of_forall_pairing fun ψ => ?_⟩
  have h := hcrit ψ
  rw [hsum] at h
  simpa using h

/-- A mean-zero minimiser of `𝓕_α` produces a divergence-free current
(the Euler equation `Σ_e c_e tanh(a_e)(Bᵀψ)_e = ⟨Bj, ψ⟩ = 0`). -/
theorem mulVec_currentOfPotential_eq_zero_of_isMeanZeroMinimizer (hB : IsConnectedIncidence B)
    {φ : V → ℝ} (hφ : IsMeanZeroMinimizer B c a₀ φ) :
    B *ᵥ currentOfPotential B c a₀ φ = 0 := by
  have hcrit0 : ∀ ψ : V → ℝ, ∑ x, ψ x = 0 →
      ∑ e, currentOfPotential B c a₀ φ e * (Bᵀ *ᵥ ψ) e = 0 := by
    intro ψ hψ
    have hloc : IsLocalMin (fun t : ℝ => affinityFunctional B c a₀ (φ + t • ψ)) 0 :=
      Filter.Eventually.of_forall fun t => by
        have hmean : ∑ x, (φ + t • ψ) x = 0 := by
          simp [sum_add_distrib, hφ.1, ← mul_sum, hψ]
        simpa using hφ.2 _ hmean
    exact hloc.hasDerivAt_eq_zero (hasDerivAt_affinityFunctional_line B c a₀ φ ψ)
  refine mulVec_eq_zero_of_forall_pairing fun ψ => ?_
  rcases isEmpty_or_nonempty V with hV | hV
  · simp [transpose_mulVec_eq_zero_of_isEmpty]
  · set s : ℝ := (∑ x, ψ x) / Fintype.card V with hs
    have hcard : (Fintype.card V : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    have hψ0 : ∑ x, (ψ - fun _ : V => s) x = 0 := by
      simp only [Pi.sub_apply, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, hs]
      field_simp
      ring
    have h := hcrit0 _ hψ0
    have hconst : (fun _ : V => s) = s • (fun _ : V => (1 : ℝ)) := by
      funext x; simp
    have hE : Bᵀ *ᵥ (ψ - fun _ => s) = Bᵀ *ᵥ ψ := by
      rw [mulVec_sub, hconst, mulVec_smul, hB.transpose_mulVec_one, smul_zero, sub_zero]
    rwa [hE] at h

/-! ## The current of a potential lies in the fibre and has the right class -/

/-- `|c_e tanh a_e| < c_e`. -/
theorem abs_currentOfPotential_lt (hc : ∀ e, 0 < c e) (φ : V → ℝ) (e : E) :
    |currentOfPotential B c a₀ φ e| < c e := by
  unfold currentOfPotential
  rw [abs_mul, abs_of_pos (hc e)]
  have : |Real.tanh (a₀ e + (Bᵀ *ᵥ φ) e)| < 1 :=
    abs_lt.mpr ⟨Real.neg_one_lt_tanh _, Real.tanh_lt_one _⟩
  calc c e * |Real.tanh (a₀ e + (Bᵀ *ᵥ φ) e)| < c e * 1 := mul_lt_mul_of_pos_left this (hc e)
    _ = c e := mul_one _

/-- The affinity of `c tanh(a₀ + Bᵀφ)` is `a₀ + Bᵀφ`. -/
theorem affinity_currentOfPotential (hc : ∀ e, 0 < c e) (φ : V → ℝ) :
    affinity c (currentOfPotential B c a₀ φ) = a₀ + Bᵀ *ᵥ φ := by
  funext e
  simp only [affinity, currentOfPotential, Pi.add_apply]
  rw [mul_div_cancel_left₀ _ (hc e).ne', Real.artanh_tanh]

/-- The current of a mean-zero minimiser lies in the fibre `𝒥(G,c)`. -/
theorem currentOfPotential_mem_currentFibre (hB : IsConnectedIncidence B) (hc : ∀ e, 0 < c e)
    {φ : V → ℝ} (hφ : IsMeanZeroMinimizer B c a₀ φ) :
    currentOfPotential B c a₀ φ ∈ CurrentFibre B c :=
  ⟨mulVec_currentOfPotential_eq_zero_of_isMeanZeroMinimizer hB hφ,
    fun e => abs_currentOfPotential_lt hc φ e⟩

/-- The current of a potential has modular class `[a₀]`: `artanh(j/c) - a₀ = Bᵀφ`. -/
theorem isExact_affinity_currentOfPotential_sub (hc : ∀ e, 0 < c e) (φ : V → ℝ) :
    IsExact B (affinity c (currentOfPotential B c a₀ φ) - a₀) :=
  ⟨φ, by rw [affinity_currentOfPotential hc, add_sub_cancel_left]⟩

/-! ## Existence and uniqueness -/

/-- Existence of a mean-zero minimiser of `𝓕_α` (thm:supp-nonlinear-Hodge). -/
theorem exists_meanZeroMinimizer (hB : IsConnectedIncidence B) (hc : ∀ e, 0 < c e)
    (a₀ : E → ℝ) : ∃ φ : V → ℝ, IsMeanZeroMinimizer B c a₀ φ := by
  obtain ⟨φ, hφ⟩ := exists_regularizedFunctional_min hB hc a₀
  obtain ⟨hsum, -⟩ := sum_eq_zero_and_mulVec_eq_zero_of_regularized_min hB hφ
  refine ⟨φ, hsum, fun ψ hψ => ?_⟩
  have := hφ ψ
  unfold regularizedFunctional at this
  rw [hsum, hψ] at this
  simpa using this

/-- Every class `α = [a₀]` is the modular class of exactly one fibre current
(thm:supp-nonlinear-Hodge, "this is the unique current with modular class `α`"). -/
theorem existsUnique_current_of_class (hB : IsConnectedIncidence B) (hc : ∀ e, 0 < c e)
    (a₀ : E → ℝ) :
    ∃! j : E → ℝ, j ∈ CurrentFibre B c ∧ IsExact B (affinity c j - a₀) := by
  obtain ⟨φ, hφ⟩ := exists_meanZeroMinimizer hB hc a₀
  have hmem := currentOfPotential_mem_currentFibre hB hc hφ
  have hex := isExact_affinity_currentOfPotential_sub (B := B) (a₀ := a₀) hc φ
  refine ⟨currentOfPotential B c a₀ φ, ⟨hmem, hex⟩, fun j' ⟨hj', hex'⟩ => ?_⟩
  apply current_eq_of_affinity_class_eq B c hj' hmem
  obtain ⟨φ₁, h₁⟩ := hex'
  obtain ⟨φ₂, h₂⟩ := hex
  refine ⟨φ₁ - φ₂, ?_⟩
  rw [mulVec_sub, ← h₁, ← h₂]
  abel

/-- The mean-zero minimiser of `𝓕_α` is unique (thm:supp-nonlinear-Hodge). -/
theorem meanZeroMinimizer_unique (hB : IsConnectedIncidence B) (hc : ∀ e, 0 < c e)
    {φ φ' : V → ℝ} (hφ : IsMeanZeroMinimizer B c a₀ φ) (hφ' : IsMeanZeroMinimizer B c a₀ φ') :
    φ = φ' := by
  have hj : currentOfPotential B c a₀ φ = currentOfPotential B c a₀ φ' := by
    apply current_eq_of_affinity_class_eq B c (currentOfPotential_mem_currentFibre hB hc hφ)
      (currentOfPotential_mem_currentFibre hB hc hφ')
    rw [affinity_currentOfPotential hc, affinity_currentOfPotential hc]
    exact ⟨φ - φ', by rw [mulVec_sub]; abel⟩
  have ha : Bᵀ *ᵥ φ = Bᵀ *ᵥ φ' := by
    have := congrArg (affinity c) hj
    rw [affinity_currentOfPotential hc, affinity_currentOfPotential hc] at this
    exact add_left_cancel this
  obtain ⟨t, ht⟩ := hB.eq_const_of_transpose_mulVec_eq_zero (φ - φ')
    (by rw [mulVec_sub, ha, sub_self])
  rcases isEmpty_or_nonempty V with hV | hV
  · exact Subsingleton.elim _ _
  · have hsum : ∑ x, (φ - φ') x = 0 := by
      simp [sum_sub_distrib, hφ.1, hφ'.1]
    rw [ht] at hsum
    simp only [sum_const, card_univ, nsmul_eq_mul] at hsum
    have ht0 : t = 0 := by
      rcases mul_eq_zero.mp hsum with h | h
      · exact absurd h (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
      · exact h
    have : φ - φ' = 0 := by rw [ht, ht0]; rfl
    exact sub_eq_zero.mp this

/-! ## The affinity map as a bijection onto `H¹(G;ℝ)` -/

/-- The first cohomology `H¹(G;ℝ) = ℝ^E / Ran Bᵀ`. -/
abbrev FirstCohomology (B : Matrix V E ℝ) : Type _ :=
  (E → ℝ) ⧸ LinearMap.range (Matrix.mulVecLin Bᵀ)

/-- The affinity map `𝔄 : j ↦ [artanh(j/c)] ∈ H¹(G;ℝ)` (eq:supp-affinity-map). -/
noncomputable def affinityClass (B : Matrix V E ℝ) (c : E → ℝ) (j : E → ℝ) :
    FirstCohomology B :=
  Submodule.Quotient.mk (affinity c j)

/-- `thm:supp-nonlinear-Hodge` (bijection clause): the affinity map is a bijection from
the current fibre `𝒥(G,c)` onto `H¹(G;ℝ)`. -/
theorem affinityClass_bijOn (hB : IsConnectedIncidence B) (hc : ∀ e, 0 < c e) :
    Set.BijOn (affinityClass B c) (CurrentFibre B c) Set.univ := by
  refine ⟨fun _ _ => trivial, fun j hj j' hj' h => ?_, fun α _ => ?_⟩
  · apply current_eq_of_affinity_class_eq B c hj hj'
    have hmem := (Submodule.Quotient.eq _).mp h
    obtain ⟨φ, hφ⟩ := LinearMap.mem_range.mp hmem
    exact ⟨φ, hφ.symm⟩
  · obtain ⟨a₀, rfl⟩ := Submodule.Quotient.mk_surjective _ α
    obtain ⟨j, ⟨hj, hex⟩, -⟩ := existsUnique_current_of_class hB hc a₀
    refine ⟨j, hj, ?_⟩
    unfold affinityClass
    rw [Submodule.Quotient.eq]
    obtain ⟨φ, hφ⟩ := hex
    exact LinearMap.mem_range.mpr ⟨φ, hφ.symm⟩

/-- **`thm:supp-nonlinear-Hodge` (Nonlinear Hodge theorem for stationary affinities),
packaged.**  For a connected incidence `B`, positive conductances `c` and a
representative `a₀` of a class `α ∈ H¹(G;ℝ)`:

1. the affinity functional `𝓕_α` has a unique mean-zero minimiser `φ_α`;
2. for that minimiser, `a_α = a₀ + Bᵀφ_α` and `j_α = c tanh a_α` satisfy
   `Bj_α = 0`, `|j_α| < c`, `artanh(j_α/c) = a_α`, `[a_α] = α`;
3. `j_α` is the unique fibre current of modular class `α`;
4. the affinity map `𝔄 : 𝒥(G,c) → H¹(G;ℝ)` is a bijection.

Coercivity is `tendsto_regularizedFunctional_cocompact`. -/
theorem nonlinear_hodge (hB : IsConnectedIncidence B) (hc : ∀ e, 0 < c e) (a₀ : E → ℝ) :
    (∃! φ : V → ℝ, IsMeanZeroMinimizer B c a₀ φ) ∧
    (∀ φ : V → ℝ, IsMeanZeroMinimizer B c a₀ φ →
      B *ᵥ currentOfPotential B c a₀ φ = 0 ∧
      currentOfPotential B c a₀ φ ∈ CurrentFibre B c ∧
      affinity c (currentOfPotential B c a₀ φ) = a₀ + Bᵀ *ᵥ φ ∧
      IsExact B (affinity c (currentOfPotential B c a₀ φ) - a₀) ∧
      ∀ j' ∈ CurrentFibre B c, IsExact B (affinity c j' - a₀) →
        j' = currentOfPotential B c a₀ φ) ∧
    (∃! j : E → ℝ, j ∈ CurrentFibre B c ∧ IsExact B (affinity c j - a₀)) ∧
    Set.BijOn (affinityClass B c) (CurrentFibre B c) Set.univ := by
  refine ⟨?_, fun φ hφ => ?_, existsUnique_current_of_class hB hc a₀, affinityClass_bijOn hB hc⟩
  · obtain ⟨φ, hφ⟩ := exists_meanZeroMinimizer hB hc a₀
    exact ⟨φ, hφ, fun φ' hφ' => meanZeroMinimizer_unique hB hc hφ' hφ⟩
  · have hmem := currentOfPotential_mem_currentFibre hB hc hφ
    have hex := isExact_affinity_currentOfPotential_sub (B := B) (a₀ := a₀) hc φ
    refine ⟨hmem.1, hmem, affinity_currentOfPotential hc φ, hex, fun j' hj' hex' => ?_⟩
    obtain ⟨j, -, huniq⟩ := existsUnique_current_of_class hB hc a₀
    rw [huniq j' ⟨hj', hex'⟩, huniq _ ⟨hmem, hex⟩]

/-! ## Bridge to the complex connected-incidence predicate and to graph connectedness -/

section Bridge

/-- The real connected-incidence hypotheses follow from the complex predicate
`RenewalGeometry.IsConnectedIncidence` of `DiscreteAnalysis/CycleProjector` applied to the
complexified matrix `B.map ofReal`. -/
theorem isConnectedIncidence_of_complex (B : Matrix V E ℝ)
    (h : _root_.RenewalGeometry.IsConnectedIncidence (B.map ((↑) : ℝ → ℂ))) :
    IsConnectedIncidence B := by
  have hconj : (B.map ((↑) : ℝ → ℂ))ᴴ = Bᵀ.map ((↑) : ℝ → ℂ) := by
    rw [← Matrix.conjTranspose_map ((↑) : ℝ → ℂ) (fun r => by simp),
      Matrix.conjTranspose_eq_transpose_of_trivial]
  have hcast : ∀ φ : V → ℝ,
      Bᵀ.map ((↑) : ℝ → ℂ) *ᵥ (((↑) : ℝ → ℂ) ∘ φ) = ((↑) : ℝ → ℂ) ∘ (Bᵀ *ᵥ φ) := by
    intro φ
    funext e
    exact (RingHom.map_mulVec Complex.ofRealHom Bᵀ φ e).symm
  refine ⟨?_, ?_⟩
  · have h1 := h.1
    rw [hconj] at h1
    have hone : ((↑) : ℝ → ℂ) ∘ (fun _ : V => (1 : ℝ)) = fun _ => (1 : ℂ) := by
      funext x; simp
    rw [← hone, hcast] at h1
    funext e
    have := congrFun h1 e
    simpa using this
  · intro φ hφ
    obtain ⟨c, hc⟩ := h.2 (((↑) : ℝ → ℂ) ∘ φ) (by
      rw [hconj, hcast, hφ]
      funext e
      simp)
    refine ⟨c.re, ?_⟩
    funext x
    have := congrFun hc x
    simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul, mul_one] at this
    rw [← this, Complex.ofReal_re]

open StationaryRenewalGraphFibre in
/-- Graph connectedness of a simple orientation gives the real connected-incidence hypotheses
for its real incidence matrix. -/
theorem isConnectedIncidence_incidenceReal [DecidableEq V] [DecidableEq E] [Nonempty V]
    (G : SimpleOrientation V E) (hG : G.Connected) :
    IsConnectedIncidence G.incidenceReal :=
  isConnectedIncidence_of_complex _ (by rw [← G.incidence_eq_map]; exact G.isConnectedIncidence hG)

open StationaryRenewalGraphFibre in
/-- `thm:supp-nonlinear-Hodge` on a connected graph: every class `[a₀] ∈ H¹(G;ℝ)` is the
modular class of exactly one current in the fibre `𝒥(G,c)`. -/
theorem existsUnique_current_of_connected [DecidableEq V] [DecidableEq E] [Nonempty V]
    (G : SimpleOrientation V E) (hG : G.Connected) {c : E → ℝ} (hc : ∀ e, 0 < c e)
    (a₀ : E → ℝ) :
    ∃! j : E → ℝ, j ∈ CurrentFibre G.incidenceReal c ∧
      IsExact G.incidenceReal (affinity c j - a₀) :=
  existsUnique_current_of_class (isConnectedIncidence_incidenceReal G hG) hc a₀

end Bridge

end NonlinearAffinityHodge
end RenewalGeometry
