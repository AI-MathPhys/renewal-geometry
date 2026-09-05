/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ENNRealResolventEnvelopeLiminf
import NCG.Grand.TopologicalDiagonalTendsto
import Mathlib.Topology.Semicontinuity.Basic

/-!
# Large-shift Yosida approximation for extended forms

For a lower-semicontinuous nonnegative extended form, resolvent minimizers with shift tending to
infinity recover every finite-energy vector strongly and in energy.
-/

open scoped ENNReal

open Filter Topology Set

noncomputable section

namespace NCG.VaryingHilbert

universe u v

variable {K : Type u} [RCLike K]
variable {E : Type v} [NormedAddCommGroup E] [InnerProductSpace K E]

/-- The resolvent variational inequality against a finite-energy point gives the basic proximal
distance estimate. -/
theorem ennrealResolvent_proximal_estimate
    (q : E → ENNReal) (lam : ℝ)
    (T : E →L[K] E)
    (hmin : ∀ (f z : E), q z ≠ ∞ →
      resolventObjective (K := K) (fun w ↦ (q w).toReal) lam f (T f) ≤
        resolventObjective (K := K) (fun w ↦ (q w).toReal) lam f z)
    (x : E) (hx : q x ≠ ∞) :
    (q (T ((lam : K) • x))).toReal +
        lam * ‖T ((lam : K) • x) - x‖ ^ 2 ≤ (q x).toReal := by
  have h := hmin ((lam : K) • x) x hx
  simp only [resolventObjective, inner_smul_real_right, RCLike.smul_re] at h
  rw [norm_sub_sq (𝕜 := K)]
  rw [← norm_sq_eq_re_inner (𝕜 := K) x] at h
  nlinarith

/-- Large-shift resolvents recover every finite-energy vector strongly and with exact ENNReal
energy convergence. -/
theorem largeShift_resolvent_approximation_of_finite
    (q : E → ENNReal) (T : ℝ → E →L[K] E)
    (hls : LowerSemicontinuous q)
    (hfinite : ∀ lam, 0 < lam → ∀ f : E, q (T lam f) ≠ ∞)
    (hmin : ∀ lam, 0 < lam → ∀ (f z : E), q z ≠ ∞ →
      resolventObjective (K := K) (fun w ↦ (q w).toReal) lam f (T lam f) ≤
        resolventObjective (K := K) (fun w ↦ (q w).toReal) lam f z)
    (x : E) (hx : q x ≠ ∞) :
    Tendsto (fun n : ℕ ↦ T ((n : ℝ) + 1) ((((n : ℝ) + 1 : ℝ) : K) • x))
        atTop (𝓝 x) ∧
      Tendsto (fun n : ℕ ↦ q (T ((n : ℝ) + 1)
        ((((n : ℝ) + 1 : ℝ) : K) • x))) atTop (𝓝 (q x)) := by
  let lam : ℕ → ℝ := fun n ↦ n + 1
  let source : ℕ → E := fun n ↦ ((lam n : ℝ) : K) • x
  let y : ℕ → E := fun n ↦ T (lam n) (source n)
  have hlamPos : ∀ n, 0 < lam n := by
    intro n
    dsimp [lam]
    positivity
  have hlam : Tendsto lam atTop atTop := by
    simpa [lam] using tendsto_atTop_add_const_right atTop (1 : ℝ)
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hprox : ∀ n,
      (q (y n)).toReal + lam n * ‖y n - x‖ ^ 2 ≤ (q x).toReal := by
    intro n
    exact ennrealResolvent_proximal_estimate q (lam n) (T (lam n))
      (hmin (lam n) (hlamPos n)) x hx
  have hsquareUpper : ∀ n, ‖y n - x‖ ^ 2 ≤ (q x).toReal / lam n := by
    intro n
    have hqnonneg : 0 ≤ (q (y n)).toReal := ENNReal.toReal_nonneg
    exact (le_div_iff₀ (hlamPos n)).2 (by nlinarith [hprox n])
  have hdiv : Tendsto (fun n ↦ (q x).toReal / lam n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlam
  have hsquare : Tendsto (fun n ↦ ‖y n - x‖ ^ 2) atTop (𝓝 0) := by
    apply squeeze_zero'
    · exact Eventually.of_forall fun n ↦ sq_nonneg ‖y n - x‖
    · exact Eventually.of_forall hsquareUpper
    · exact hdiv
  have hnorm : Tendsto (fun n ↦ ‖y n - x‖) atTop (𝓝 0) := by
    have hsqrt := hsquare.sqrt
    simpa [Real.sqrt_sq (norm_nonneg _)] using hsqrt
  have hy : Tendsto y atTop (𝓝 x) :=
    tendsto_iff_norm_sub_tendsto_zero.2 hnorm
  have hqUpper : ∀ n, q (y n) ≤ q x := by
    intro n
    rw [← ENNReal.ofReal_toReal (hfinite (lam n) (hlamPos n) (source n)),
      ← ENNReal.ofReal_toReal hx]
    apply ENNReal.ofReal_le_ofReal
    exact (by nlinarith [hprox n, mul_nonneg (hlamPos n).le (sq_nonneg ‖y n - x‖)])
  have henergy : Tendsto (fun n ↦ q (y n)) atTop (𝓝 (q x)) := by
    refine tendsto_order.2 ⟨?_, ?_⟩
    · intro a ha
      exact hy.eventually (hls.lowerSemicontinuousAt x a ha)
    · intro b hb
      exact Eventually.of_forall fun n ↦ (hqUpper n).trans_lt hb
  simpa [y, source, lam] using And.intro hy henergy

/-- If the finite-energy domain is dense, canonical large-shift resolvent images give an exact
energy core at every vector, including vectors whose form value is infinite. -/
theorem exists_largeShift_resolventCore_approximation
    (q : E → ENNReal) (T : ℝ → E →L[K] E)
    (hls : LowerSemicontinuous q)
    (hdom : Dense {z : E | q z ≠ ∞})
    (hfinite : ∀ lam, 0 < lam → ∀ f : E, q (T lam f) ≠ ∞)
    (hmin : ∀ lam, 0 < lam → ∀ (f z : E), q z ≠ ∞ →
      resolventObjective (K := K) (fun w ↦ (q w).toReal) lam f (T lam f) ≤
        resolventObjective (K := K) (fun w ↦ (q w).toReal) lam f z)
    (x : E) :
    ∃ source : ℕ → E,
      Tendsto (fun n : ℕ ↦ T ((n : ℝ) + 1) (source n)) atTop (𝓝 x) ∧
        Tendsto (fun n : ℕ ↦ q (T ((n : ℝ) + 1) (source n)))
          atTop (𝓝 (q x)) := by
  by_cases hx : q x = ∞
  · have hxClosure : x ∈ closure {z : E | q z ≠ ∞} := by
      rw [hdom.closure_eq]
      exact mem_univ x
    obtain ⟨z, hzDomain, hz⟩ := mem_closure_iff_seq_limit.mp hxClosure
    have hqz : Tendsto (fun m ↦ q (z m)) atTop (𝓝 (q x)) := by
      refine tendsto_order.2 ⟨?_, ?_⟩
      · intro a ha
        exact hz.eventually (hls.lowerSemicontinuousAt x a ha)
      · intro b hb
        simp [hx] at hb
    let g : ℕ → ℕ → E := fun m n ↦
      T ((n : ℝ) + 1) ((((n : ℝ) + 1 : ℝ) : K) • z m)
    have hrow : ∀ m,
        Tendsto (g m) atTop (𝓝 (z m)) ∧
          Tendsto (fun n ↦ q (g m n)) atTop (𝓝 (q (z m))) := by
      intro m
      exact largeShift_resolvent_approximation_of_finite
        q T hls hfinite hmin (z m) (hzDomain m)
    obtain ⟨φ, _hφ, hvec, henergy⟩ := exists_diagonal_tendsto_pair_topological
      g z x (fun m n ↦ q (g m n)) (fun m ↦ q (z m)) (q x)
      (fun m ↦ (hrow m).1) hz (fun m ↦ (hrow m).2) hqz
    refine ⟨fun n ↦ ((((n : ℝ) + 1 : ℝ) : K) • z (φ n)), ?_, ?_⟩
    · simpa [g] using hvec
    · simpa [g] using henergy
  · refine ⟨fun n ↦ ((((n : ℝ) + 1 : ℝ) : K) • x), ?_, ?_⟩
    · exact (largeShift_resolvent_approximation_of_finite
        q T hls hfinite hmin x hx).1
    · exact (largeShift_resolvent_approximation_of_finite
        q T hls hfinite hmin x hx).2

/-- Dense-domain lower-semicontinuous forms have an automatic varying-shift resolvent energy
core. -/
theorem largeShift_resolventEnergyCore
    (q : E → ENNReal) (T : ℝ → E →L[K] E)
    (hls : LowerSemicontinuous q) (hdom : Dense {z : E | q z ≠ ∞})
    (hfinite : ∀ lam, 0 < lam → ∀ f : E, q (T lam f) ≠ ∞)
    (hmin : ∀ lam, 0 < lam → ∀ (f z : E), q z ≠ ∞ →
      resolventObjective (K := K) (fun w ↦ (q w).toReal) lam f (T lam f) ≤
        resolventObjective (K := K) (fun w ↦ (q w).toReal) lam f z) :
    ∀ x : E, ∃ source : ℕ → E,
      Tendsto (fun n : ℕ ↦ T ((n : ℝ) + 1) (source n)) atTop (𝓝 x) ∧
        Tendsto (fun n : ℕ ↦ q (T ((n : ℝ) + 1) (source n)))
          atTop (𝓝 (q x)) :=
  exists_largeShift_resolventCore_approximation q T hls hdom hfinite hmin


end NCG.VaryingHilbert
