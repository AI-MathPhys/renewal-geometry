/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Smooth parametric integrals and the Hadamard quotient

Generic infrastructure (no renewal notions) for the Lipschitz (difference) form of the Moser
composition estimate used in `prop:coupled-bootstrap` of the Einstein–Standard-Model
action-closure manuscript ("the first term is locally Lipschitz in `H^k`").

* **`contDiff_intervalIntegral_param`** — if `F : E × ℝ → G` is `C^∞` (`E` finite dimensional,
  `G` complete), then `x ↦ ∫₀¹ F(x, s) ds` is `C^∞` (differentiation under the integral sign by
  dominated convergence, induction on the order).
* `hadQ Φ b` — the **Hadamard quotient** `(v, v') ↦ ∫₀¹ ∂_bΦ(v + s(v' - v)) ds` of a smooth
  `Φ : ℝ^n → ℝ`, as a function of the concatenation `(v, v') ∈ ℝ^{n+n}`;
  **`contDiff_hadQ`** — it is smooth; **`hadamard_eq`** — the **Hadamard identity**
  `Φ(v') - Φ(v) = Σ_b (v'_b - v_b) hadQ Φ b (v, v')`.
-/

open Set Filter Topology MeasureTheory Metric
open scoped ContDiff

noncomputable section

namespace RenewalGeometry.Hadamard

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- `C^N` smoothness of a parametric integral over `[0, 1]` with a `C^∞` integrand. -/
theorem contDiff_nat_intervalIntegral_param (N : ℕ) :
    ∀ {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G] {F : E × ℝ → G},
      ContDiff ℝ ∞ F → ContDiff ℝ N (fun x => ∫ s in (0 : ℝ)..1, F (x, s)) := by
  induction N with
  | zero =>
    intro G _ _ _ F hF
    refine contDiff_zero.2 ?_
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun x s => F (x, s)) (hF.continuous) 0 1
  | succ N ih =>
    intro G _ _ _ F hF
    set F' : E × ℝ → E →L[ℝ] G := fun p => (fderiv ℝ F p).comp (ContinuousLinearMap.inl ℝ E ℝ)
      with hF'def
    have hF' : ContDiff ℝ ∞ F' :=
      (hF.fderiv_right (m := ∞) le_rfl).clm_comp contDiff_const
    rw [show ((N + 1 : ℕ) : WithTop ℕ∞) = (N : WithTop ℕ∞) + 1 by norm_cast,
      contDiff_succ_iff_hasFDerivAt]
    refine ⟨fun x => ∫ s in (0 : ℝ)..1, F' (x, s), ih hF', fun x₀ => ?_⟩
    have hK : IsCompact (closedBall x₀ 1 ×ˢ Icc (0 : ℝ) 1) :=
      (isCompact_closedBall x₀ 1).prod isCompact_Icc
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hF'.continuous.continuousOn
    have hdiff : ∀ x t, HasFDerivAt (fun x => F (x, t)) (F' (x, t)) x := by
      intro x t
      have h1 : HasFDerivAt F (fderiv ℝ F (x, t)) (x, t) :=
        ((hF.differentiable (by simp)) (x, t)).hasFDerivAt
      exact h1.comp x (hasFDerivAt_prodMk_left x t)
    refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
      (F := fun x s => F (x, s)) (F' := fun x s => F' (x, s)) (bound := fun _ => C)
      (ball_mem_nhds x₀ one_pos) ?_ ?_ ?_ ?_ intervalIntegrable_const ?_
    · exact Eventually.of_forall fun x =>
        (hF.continuous.comp (Continuous.prodMk_right x)).aestronglyMeasurable
    · exact (hF.continuous.comp (Continuous.prodMk_right x₀)).intervalIntegrable 0 1
    · exact (hF'.continuous.comp (Continuous.prodMk_right x₀)).aestronglyMeasurable
    · refine Eventually.of_forall fun t ht x hx => hC _ ⟨ball_subset_closedBall hx, ?_⟩
      rw [uIoc_of_le zero_le_one] at ht
      exact ⟨ht.1.le, ht.2⟩
    · exact Eventually.of_forall fun t _ x _ => hdiff x t

/-- **Smooth parametric integrals**: if `F : E × ℝ → G` is `C^∞`, so is `x ↦ ∫₀¹ F(x, s) ds`. -/
theorem contDiff_intervalIntegral_param {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [CompleteSpace G] {F : E × ℝ → G} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun x => ∫ s in (0 : ℝ)..1, F (x, s)) :=
  contDiff_infty.2 fun N => contDiff_nat_intervalIntegral_param N hF

/-! ### The Hadamard quotient -/

variable {n : ℕ}

/-- The first half `v` of a concatenated vector `(v, v') ∈ ℝ^{n+n}`. -/
def lo (z : Fin (n + n) → ℝ) : Fin n → ℝ := fun i => z (Fin.castAdd n i)

/-- The second half `v'` of a concatenated vector `(v, v') ∈ ℝ^{n+n}`. -/
def hi (z : Fin (n + n) → ℝ) : Fin n → ℝ := fun i => z (Fin.natAdd n i)

/-- The continuous linear map `z ↦ (lo z, hi z)` pieces. -/
def loL : (Fin (n + n) → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (Fin.castAdd n i)

/-- The continuous linear map `z ↦ hi z`. -/
def hiL : (Fin (n + n) → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (Fin.natAdd n i)

theorem loL_apply (z : Fin (n + n) → ℝ) : loL z = lo z := rfl

theorem hiL_apply (z : Fin (n + n) → ℝ) : hiL z = hi z := rfl

@[simp] theorem lo_append (v v' : Fin n → ℝ) : lo (Fin.append v v') = v := by
  funext i; simp [lo]

@[simp] theorem hi_append (v v' : Fin n → ℝ) : hi (Fin.append v v') = v' := by
  funext i; exact Fin.append_right v v' i

/-- **The Hadamard quotient** `hadQ Φ b (v, v') = ∫₀¹ ∂_bΦ(v + s(v' - v)) ds`. -/
def hadQ (Φ : (Fin n → ℝ) → ℝ) (b : Fin n) (z : Fin (n + n) → ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..1, fderiv ℝ Φ (lo z + s • (hi z - lo z)) (Pi.single b 1)

/-- The Hadamard quotient of a smooth function is smooth. -/
theorem contDiff_hadQ {Φ : (Fin n → ℝ) → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (b : Fin n) :
    ContDiff ℝ ∞ (hadQ Φ b) := by
  have hseg : ContDiff ℝ ∞ (fun p : (Fin (n + n) → ℝ) × ℝ =>
      lo p.1 + p.2 • (hi p.1 - lo p.1)) := by
    have h1 : ContDiff ℝ ∞ (fun p : (Fin (n + n) → ℝ) × ℝ => lo p.1) :=
      loL.contDiff.comp contDiff_fst
    have h2 : ContDiff ℝ ∞ (fun p : (Fin (n + n) → ℝ) × ℝ => hi p.1) :=
      hiL.contDiff.comp contDiff_fst
    exact h1.add (contDiff_snd.smul (h2.sub h1))
  have hF : ContDiff ℝ ∞ (fun p : (Fin (n + n) → ℝ) × ℝ =>
      fderiv ℝ Φ (lo p.1 + p.2 • (hi p.1 - lo p.1)) (Pi.single b 1)) :=
    ((hΦ.fderiv_right (m := ∞) le_rfl).comp hseg).clm_apply contDiff_const
  exact contDiff_intervalIntegral_param hF

/-- **The Hadamard identity**: `Φ(v') - Φ(v) = Σ_b (v'_b - v_b) hadQ Φ b (v, v')`. -/
theorem hadamard_eq {Φ : (Fin n → ℝ) → ℝ} (hΦ : ContDiff ℝ ∞ Φ) (z : Fin (n + n) → ℝ) :
    Φ (hi z) - Φ (lo z) = ∑ b, (hi z b - lo z b) * hadQ Φ b z := by
  set v := lo z
  set w := hi z - lo z
  have hd : Differentiable ℝ Φ := hΦ.differentiable (by simp)
  have hpath : ∀ s : ℝ, HasDerivAt (fun s : ℝ => Φ (v + s • w))
      (fderiv ℝ Φ (v + s • w) w) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => v + s • w) w s := by
      simpa using ((hasDerivAt_id s).smul_const w).const_add v
    exact (hd _).hasFDerivAt.comp_hasDerivAt s h1
  have hcont : Continuous fun s : ℝ => fderiv ℝ Φ (v + s • w) w :=
    ((hΦ.continuous_fderiv (by simp)).comp (continuous_const.add
      (continuous_id.smul continuous_const))).clm_apply continuous_const
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hpath s)
    (hcont.intervalIntegrable 0 1)
  simp only [one_smul, zero_smul, add_zero] at hftc
  have hvw : v + w = hi z := by simp [v, w]
  rw [hvw] at hftc
  rw [← hftc]
  have hwsum : (∑ b, w b • (Pi.single b 1 : Fin n → ℝ)) = w := by
    funext i; simp [Finset.sum_apply, Pi.single_apply]
  have hL : ∀ L : (Fin n → ℝ) →L[ℝ] ℝ, L w = ∑ b, w b * L (Pi.single b 1) := by
    intro L
    conv_lhs => rw [← hwsum]
    rw [map_sum]
    simp [map_smul, smul_eq_mul]
  have hexp : ∀ s : ℝ, fderiv ℝ Φ (v + s • w) w =
      ∑ b, w b * fderiv ℝ Φ (v + s • w) (Pi.single b 1) := fun s => hL _
  simp_rw [hexp]
  rw [intervalIntegral.integral_finsetSum
    (f := fun b s => w b * fderiv ℝ Φ (v + s • w) (Pi.single b 1)) fun b _ =>
    (continuous_const.mul (((hΦ.continuous_fderiv (by simp)).comp (continuous_const.add
      (continuous_id.smul continuous_const))).clm_apply continuous_const)).intervalIntegrable 0 1]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [intervalIntegral.integral_const_mul]
  simp [hadQ, w, v]

end RenewalGeometry.Hadamard
