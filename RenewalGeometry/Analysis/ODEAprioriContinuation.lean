/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Global existence of ODE solutions confined by an a priori compact set

Mathlib's Picard–Lindelöf theorem (`IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt`)
is local.  This file proves the classical **continuation (first-exit) principle** used in the
proof of `thm:finite-Coulomb-normalization` (Einstein–SM action closure): a time-dependent
`C¹` vector field on an open set `O ⊆ ℝ × E` (`E` finite dimensional) whose solutions are
a priori confined to a compact set `K ⊆ O` has a solution on the whole interval `[0, T₁]`.

* `exists_solution_of_apriori` — if `(0, x₀) ∈ K` and every solution `γ` on any `[0, T]`,
  `T ≤ T₁`, with `γ 0 = x₀` and graph in `O` has its graph in `K`, then there is a solution on
  `[0, T₁]` with graph in `K`.

The proof: a uniform Picard–Lindelöf step (uniform bound and Lipschitz constant on the closed
`ε`-thickening of `K` inside `O`, from compactness and continuity of the derivative), a radial
clipping of the field outside the Picard–Lindelöf ball (so that each local solution stays in the
ball), gluing of one-sided derivatives, and finitely many steps.
-/

open Set Metric Filter Topology
open scoped NNReal

namespace RenewalGeometry.ODEContinuation

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A derivative within `s` at a point that is isolated from `s` holds for every value. -/
theorem hasDerivWithinAt_of_nhdsWithin_eq_bot {f : ℝ → E} {f' : E} {s : Set ℝ} {x : ℝ}
    (h : 𝓝[s \ {x}] x = ⊥) : HasDerivWithinAt f f' s x := by
  rw [hasDerivWithinAt_iff_tendsto_slope, h]
  exact tendsto_bot

theorem hasDerivWithinAt_singleton' (f : ℝ → E) (f' : E) (x : ℝ) :
    HasDerivWithinAt f f' {x} x :=
  hasDerivWithinAt_of_nhdsWithin_eq_bot (by simp)

theorem hasDerivWithinAt_of_notMem_closure {f : ℝ → E} {f' : E} {s : Set ℝ} {x : ℝ}
    (h : x ∉ closure s) : HasDerivWithinAt f f' s x := by
  refine hasDerivWithinAt_of_nhdsWithin_eq_bot ?_
  rw [← le_bot_iff, ← (notMem_closure_iff_nhdsWithin_eq_bot.1 h)]
  exact nhdsWithin_mono _ diff_subset

/-- Radial clipping onto the closed ball `closedBall y ρ`. -/
def clip (y : E) (ρ : ℝ) (x : E) : E :=
  if ‖x - y‖ ≤ ρ then x else y + (ρ / ‖x - y‖) • (x - y)

theorem clip_of_mem {y : E} {ρ : ℝ} {x : E} (hx : x ∈ closedBall y ρ) : clip y ρ x = x := by
  rw [mem_closedBall, dist_eq_norm] at hx
  simp [clip, hx]

theorem clip_mem (y : E) {ρ : ℝ} (hρ : 0 ≤ ρ) (x : E) : clip y ρ x ∈ closedBall y ρ := by
  rw [mem_closedBall, dist_eq_norm]
  unfold clip
  split_ifs with h
  · exact h
  · have hpos : 0 < ‖x - y‖ := lt_of_le_of_lt hρ (lt_of_not_ge h)
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      div_mul_cancel₀ _ hpos.ne']

/-- Gluing two solutions at `T`. -/
theorem hasDerivWithinAt_glue {f : ℝ → E → E} {γ β : ℝ → E} {T T' : ℝ} (h0T : 0 ≤ T)
    (hTT' : T ≤ T') (hγ : ∀ t ∈ Icc 0 T, HasDerivWithinAt γ (f t (γ t)) (Icc 0 T) t)
    (hβ : ∀ t ∈ Icc T T', HasDerivWithinAt β (f t (β t)) (Icc T T') t) (hβT : β T = γ T) :
    ∀ t ∈ Icc 0 T', HasDerivWithinAt (fun t => if t ≤ T then γ t else β t)
      (f t (if t ≤ T then γ t else β t)) (Icc 0 T') t := by
  set g : ℝ → E := fun t => if t ≤ T then γ t else β t with hg
  intro t ht
  rw [← Icc_union_Icc_eq_Icc h0T hTT']
  refine HasDerivWithinAt.union ?_ ?_
  · by_cases htT : t ≤ T
    · have hmem : t ∈ Icc 0 T := ⟨ht.1, htT⟩
      have := (hγ t hmem).congr_of_mem (f₁ := g) (fun u hu => by simp [hg, hu.2]) hmem
      simpa [hg, htT] using this
    · refine hasDerivWithinAt_of_notMem_closure ?_
      rw [closure_Icc]
      exact fun h => htT h.2
  · by_cases htT : T ≤ t
    · have hmem : t ∈ Icc T T' := ⟨htT, ht.2⟩
      have hgβ : ∀ u ∈ Icc T T', g u = β u := by
        intro u hu
        simp only [hg]
        split_ifs with h
        · rw [le_antisymm h hu.1, hβT]
        · rfl
      have := (hβ t hmem).congr_of_mem hgβ hmem
      rwa [← hgβ t hmem] at this
    · refine hasDerivWithinAt_of_notMem_closure ?_
      rw [closure_Icc]
      exact fun h => htT h.1

variable [FiniteDimensional ℝ E]

/-- Uniform Picard–Lindelöf data near a compact set `K ⊆ O` for a `C¹` field. -/
theorem exists_uniform_data {f : ℝ → E → E} {O K : Set (ℝ × E)} (hO : IsOpen O)
    (hf : ContDiffOn ℝ 1 (Function.uncurry f) O) (hK : IsCompact K) (hKO : K ⊆ O) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ M : ℝ, 0 ≤ M ∧ ∃ Λ : ℝ≥0,
      ∀ p ∈ K, ∀ t, |t - p.1| ≤ ρ →
        (∀ x ∈ closedBall p.2 ρ, (t, x) ∈ O ∧ ‖f t x‖ ≤ M) ∧
        LipschitzOnWith Λ (f t) (closedBall p.2 ρ) := by
  obtain ⟨ε, hε, hεO⟩ := hK.exists_cthickening_subset_open hO hKO
  have hC : IsCompact (cthickening ε K) := hK.cthickening
  have hcont : ContinuousOn (Function.uncurry f) O := hf.continuousOn
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn (hcont.mono hεO)
  have hD : ContinuousOn (fderiv ℝ (Function.uncurry f)) O :=
    hf.continuousOn_fderiv_of_isOpen hO le_rfl
  obtain ⟨D, hDb⟩ := hC.exists_bound_of_continuousOn (hD.mono hεO)
  have hmemC : ∀ p ∈ K, ∀ t, |t - p.1| ≤ ε → ∀ x ∈ closedBall p.2 ε,
      (t, x) ∈ cthickening ε K := by
    intro p hp t ht x hx
    refine mem_cthickening_of_dist_le (t, x) p ε K hp ?_
    rw [Prod.dist_eq, Real.dist_eq]
    exact max_le ht (mem_closedBall.1 hx)
  refine ⟨ε, hε, max M 0, le_max_right _ _, Real.toNNReal D, fun p hp t ht => ⟨fun x hx =>
    ⟨hεO (hmemC p hp t ht x hx), (hM _ (hmemC p hp t ht x hx)).trans (le_max_left _ _)⟩, ?_⟩⟩
  -- Lipschitz bound from the derivative bound on the convex ball
  have hder : ∀ x ∈ closedBall p.2 ε, HasFDerivWithinAt (f t)
      ((fderiv ℝ (Function.uncurry f) (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ E))
      (closedBall p.2 ε) x := by
    intro x hx
    have hx' := hεO (hmemC p hp t ht x hx)
    have h1 : HasFDerivAt (Function.uncurry f) (fderiv ℝ (Function.uncurry f) (t, x)) (t, x) :=
      ((hf.differentiableOn one_ne_zero) _ hx').differentiableAt (hO.mem_nhds hx')
        |>.hasFDerivAt
    have h2 : HasFDerivAt (fun y : E => ((t, y) : ℝ × E)) (ContinuousLinearMap.inr ℝ ℝ E) x :=
      (hasFDerivAt_const t x).prodMk (hasFDerivAt_id x)
    exact (h1.comp x h2).hasFDerivWithinAt
  have hbound : ∀ x ∈ closedBall p.2 ε,
      ‖(fderiv ℝ (Function.uncurry f) (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ E)‖ ≤ D := by
    intro x hx
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    have h1 := hDb _ (hmemC p hp t ht x hx)
    have h2 : ‖ContinuousLinearMap.inr ℝ ℝ E‖ ≤ 1 := ContinuousLinearMap.norm_inr_le_one _ _ _
    calc _ ≤ D * 1 := mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
      _ = D := mul_one D
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
  rw [dist_eq_norm, dist_eq_norm]
  have := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le hder hbound (convex_closedBall _ _)
    hy hx
  refine this.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  exact Real.le_coe_toNNReal D

/-- One continuation step: a solution on `[0, T]` with graph in `O`, ending in `K`, extends to
`[0, T']` (`T' - T ≤ δ`) with graph in `O`. -/
theorem extend_step {f : ℝ → E → E} {O : Set (ℝ × E)} (hO : IsOpen O)
    (hf : ContDiffOn ℝ 1 (Function.uncurry f) O) {ρ M : ℝ} (hρ : 0 < ρ) (hM : 0 ≤ M) {Λ : ℝ≥0}
    {T T' : ℝ} (h0T : 0 ≤ T) (hTT' : T ≤ T') (hT'ρ : T' - T ≤ ρ) (hT'M : M * (T' - T) ≤ ρ)
    {γ : ℝ → E} (hdata : ∀ t, |t - T| ≤ ρ →
        (∀ x ∈ closedBall (γ T) ρ, (t, x) ∈ O ∧ ‖f t x‖ ≤ M) ∧
        LipschitzOnWith Λ (f t) (closedBall (γ T) ρ))
    (hγO : ∀ t ∈ Icc 0 T, (t, γ t) ∈ O)
    (hγ : ∀ t ∈ Icc 0 T, HasDerivWithinAt γ (f t (γ t)) (Icc 0 T) t) :
    ∃ γ' : ℝ → E, γ' 0 = γ 0 ∧ (∀ t ∈ Icc 0 T', (t, γ' t) ∈ O) ∧
      ∀ t ∈ Icc 0 T', HasDerivWithinAt γ' (f t (γ' t)) (Icc 0 T') t := by
  set y := γ T
  set g : ℝ → E → E := fun t x => f t (clip y ρ x) with hg
  have hcont : ContinuousOn (Function.uncurry f) O := hf.continuousOn
  have htime : ∀ t ∈ Icc T T', |t - T| ≤ ρ := by
    intro t ht
    rw [abs_of_nonneg (by linarith [ht.1])]
    linarith [ht.2]
  have hPL : IsPicardLindelof g (tmin := T) (tmax := T') ⟨T, le_rfl, hTT'⟩ y
      ⟨ρ, hρ.le⟩ 0 ⟨M, hM⟩ Λ := by
    refine ⟨fun t ht => ?_, fun x hx => ?_, fun t ht x hx => ?_, ?_⟩
    · refine LipschitzOnWith.of_dist_le_mul fun x hx z hz => ?_
      have hx' : x ∈ closedBall y ρ := hx
      have hz' : z ∈ closedBall y ρ := hz
      simp only [hg, clip_of_mem hx', clip_of_mem hz']
      exact ((hdata t (htime t ht)).2).dist_le_mul x hx' z hz'
    · have hx' : x ∈ closedBall y ρ := hx
      have : ContinuousOn (fun t => Function.uncurry f (t, x)) (Icc T T') :=
        hcont.comp (continuousOn_id.prodMk continuousOn_const) fun t ht =>
          ((hdata t (htime t ht)).1 x hx').1
      refine this.congr fun t _ => ?_
      simp [hg, clip_of_mem hx']
    · have hx' : x ∈ closedBall y ρ := hx
      simp only [hg, clip_of_mem hx']
      exact ((hdata t (htime t ht)).1 x hx').2
    · simp only [sub_self, NNReal.coe_zero, sub_zero]
      rw [max_eq_left (by linarith)]
      exact hT'M
  obtain ⟨β, hβ0, hβ⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  -- `β` stays in the ball
  have hβball : ∀ t ∈ Icc T T', β t ∈ closedBall y ρ := by
    intro t ht
    have hb : ∀ u ∈ Ico T T', ‖g u (β u)‖ ≤ M := fun u hu =>
      ((hdata u (htime u (Ico_subset_Icc_self hu))).1 _ (clip_mem y hρ.le _)).2
    have := norm_image_sub_le_of_norm_deriv_le_segment' hβ hb t ht
    rw [mem_closedBall, dist_eq_norm]
    have hβ0' : β T = y := hβ0
    rw [hβ0'] at this
    calc ‖β t - y‖ ≤ M * (t - T) := this
      _ ≤ M * (T' - T) := mul_le_mul_of_nonneg_left (by linarith [ht.2]) hM
      _ ≤ ρ := hT'M
  have hβ' : ∀ t ∈ Icc T T', HasDerivWithinAt β (f t (β t)) (Icc T T') t := by
    intro t ht
    have := hβ t ht
    simp only [hg, clip_of_mem (hβball t ht)] at this
    exact this
  refine ⟨fun t => if t ≤ T then γ t else β t, by simp [h0T], fun t ht => ?_,
    hasDerivWithinAt_glue h0T hTT' hγ hβ' hβ0⟩
  by_cases htT : t ≤ T
  · simp only [htT, ite_true]; exact hγO t ⟨ht.1, htT⟩
  · have htT := lt_of_not_ge htT
    simp only [not_le.2 htT, ite_false]
    exact ((hdata t (htime t ⟨htT.le, ht.2⟩)).1 _ (hβball t ⟨htT.le, ht.2⟩)).1

/-- **Global existence under a priori confinement.**  Let `f` be a time-dependent `C¹` vector
field on an open set `O ⊆ ℝ × E` (`E` finite dimensional), `K ⊆ O` compact with `(0, x₀) ∈ K`.
If every solution `γ` of `γ' = f(t, γ)` on any `[0, T]`, `0 ≤ T ≤ T₁`, with `γ 0 = x₀` and graph
in `O` has its graph in `K`, then there is a solution on `[0, T₁]` with graph in `K`. -/
theorem exists_solution_of_apriori {f : ℝ → E → E} {O K : Set (ℝ × E)} (hO : IsOpen O)
    (hf : ContDiffOn ℝ 1 (Function.uncurry f) O) (hK : IsCompact K) (hKO : K ⊆ O) {x₀ : E}
    (hx₀ : ((0 : ℝ), x₀) ∈ K) {T₁ : ℝ} (hT₁ : 0 ≤ T₁)
    (hapriori : ∀ T ∈ Icc 0 T₁, ∀ γ : ℝ → E, γ 0 = x₀ →
      (∀ t ∈ Icc 0 T, (t, γ t) ∈ O) →
      (∀ t ∈ Icc 0 T, HasDerivWithinAt γ (f t (γ t)) (Icc 0 T) t) →
      ∀ t ∈ Icc 0 T, (t, γ t) ∈ K) :
    ∃ γ : ℝ → E, γ 0 = x₀ ∧
      ∀ t ∈ Icc 0 T₁, HasDerivWithinAt γ (f t (γ t)) (Icc 0 T₁) t ∧ (t, γ t) ∈ K := by
  obtain ⟨ρ, hρ, M, hM, Λ, hdata⟩ := exists_uniform_data hO hf hK hKO
  set δ : ℝ := min ρ (ρ / (M + 1)) with hδ
  have hδ0 : 0 < δ := lt_min hρ (div_pos hρ (by linarith))
  have hδρ : δ ≤ ρ := min_le_left _ _
  have hδM : M * δ ≤ ρ := by
    have h1 : δ ≤ ρ / (M + 1) := min_le_right _ _
    calc M * δ ≤ (M + 1) * (ρ / (M + 1)) := mul_le_mul (by linarith) h1 hδ0.le (by linarith)
      _ = ρ := mul_div_cancel₀ _ (by linarith)
  -- induction on the number of steps
  have key : ∀ k : ℕ, ∃ γ : ℝ → E, γ 0 = x₀ ∧
      (∀ t ∈ Icc 0 (min (k * δ) T₁), (t, γ t) ∈ O) ∧
      ∀ t ∈ Icc 0 (min (k * δ) T₁),
        HasDerivWithinAt γ (f t (γ t)) (Icc 0 (min (k * δ) T₁)) t := by
    intro k
    induction k with
    | zero =>
      refine ⟨fun _ => x₀, rfl, fun t ht => ?_, fun t ht => ?_⟩
      · have ht' : t ∈ Icc (0 : ℝ) 0 := by
          simpa only [Nat.cast_zero, zero_mul, min_eq_left hT₁] using ht
        have : t = 0 := le_antisymm ht'.2 ht'.1
        subst this; exact hKO hx₀
      · simp only [Nat.cast_zero, zero_mul, min_eq_left hT₁, Icc_self] at ht ⊢
        rw [ht]; exact hasDerivWithinAt_singleton' _ _ _
    | succ k ih =>
      obtain ⟨γ, hγ0, hγO, hγ⟩ := ih
      set T := min (k * δ) T₁ with hT
      have h0T : 0 ≤ T := le_min (by positivity) hT₁
      by_cases hk : T₁ ≤ k * δ
      · have e1 : T = T₁ := min_eq_right hk
        have e2 : min (((k + 1 : ℕ) : ℝ) * δ) T₁ = T₁ := min_eq_right (by push_cast; nlinarith)
        rw [e2]; rw [e1] at hγO hγ; exact ⟨γ, hγ0, hγO, hγ⟩
      · have hk := lt_of_not_ge hk
        have e1 : T = k * δ := min_eq_left hk.le
        set T' := min (((k + 1 : ℕ) : ℝ) * δ) T₁ with hT'
        have hTT' : T ≤ T' := by
          rw [e1]; refine le_min ?_ hk.le; push_cast; linarith
        have hT'T : T' - T ≤ δ := by
          rw [e1]; have : T' ≤ ((k + 1 : ℕ) : ℝ) * δ := min_le_left _ _
          push_cast at this; linarith
        have hTK : (T, γ T) ∈ K :=
          hapriori T ⟨h0T, min_le_right _ _⟩ γ hγ0 hγO hγ T ⟨h0T, le_rfl⟩
        obtain ⟨γ', hγ'0, hγ'O, hγ'⟩ := extend_step hO hf hρ hM h0T hTT' (hT'T.trans hδρ)
          ((mul_le_mul_of_nonneg_left hT'T hM).trans hδM)
          (fun t ht => hdata (T, γ T) hTK t ht) hγO hγ
        exact ⟨γ', hγ'0.trans hγ0, hγ'O, hγ'⟩
  obtain ⟨k, hk⟩ := exists_nat_ge (T₁ / δ)
  have hkT : min (k * δ) T₁ = T₁ := min_eq_right (by rwa [div_le_iff₀ hδ0] at hk)
  obtain ⟨γ, hγ0, hγO, hγ⟩ := key k
  rw [hkT] at hγO hγ
  exact ⟨γ, hγ0, fun t ht => ⟨hγ t ht,
    hapriori T₁ ⟨hT₁, le_rfl⟩ γ hγ0 hγO hγ t ht⟩⟩

end

end RenewalGeometry.ODEContinuation
