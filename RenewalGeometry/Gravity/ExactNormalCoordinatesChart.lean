/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.AnalyticImplicitFunction

/-!
# Exact nonlinear constraint coordinates (`lem:supp-exact-normal-coordinates`;
  emergent-spacetime manuscript)

The amplitude-graded exact-action chart `ass:supp-graded-exact-chart` enters as hypotheses (the
ledger convention for that assumption: its formal counterparts are the hypothesis arguments of
the theorems referencing it).  Notation (paper → Lean):

* free coordinates `w = (q, p)`, `p = (p_A, p_W)` → `w : Qs × (LA × LW)`; normal coordinate
  `n` → `Nn` (`ℝ¹⁰⁸`); the divided constraint rows → `Rows` (`ℝ¹⁰⁸`); canonical space → `Xc`
  (`ℝ³²⁴`); the parameter `y = (a, w)`;
* the analytic divided map `𝒫(a, n, w)` of (C2) → `P : (ℝ × W) × Nn → Rows`, `P ((a, w), n)`
  (argument order changed only);
* (C2) `𝒫(a, 0, 0) = 0`, `𝒫(0, n, w) = 𝒞₀J_c n` with `𝒞₀J_c` invertible → `hPzero`, `hPlin`
  with `C : Nn ≃L Rows`;
* (C2) `D_q𝒫 = O(a)`, `D_p𝒫 = O(a²)` "with these factors preserved by the fixed-order
  derivatives" (the paper: "analytic divisibilities") → `D_q𝒫 = a • 𝒫_q`, `D_p𝒫 = a² • 𝒫_p` near
  `0` with `𝒫_q`, `𝒫_p` analytic (`hdq`, `hdp`);
* the substitution `eq:supp-exact-normal-chart` → `normalChart`, with an analytic prepared
  record `a ↦ (X⁰_a, λ⁰_a)`;
* "substitution into `P_h` followed by division of the rows by `a²`, `a³`" → `hdiv`:
  for `a ≠ 0`, `P_h (Θ(a, n, w)) = 0 ↔ 𝒫(a, n, w) = 0`;
* (C1) `𝒞₀ : ℝ³²⁴ → ℝ¹⁰⁸`, `E : ℝ²¹⁶ → ker 𝒞₀` (onto `ker 𝒞₀`, as the dimension count
  `216 = 324 - 108` gives), `Λ E = I`, `Λ J_c = 0`, `𝒞₀ J_c = C`.

Results.

* `exact_normal_coordinates`: an analytic `n(a, w)` with `n(0) = 0`, `𝒫(a, n(a,w), w) = 0`,
  local uniqueness, `n(a, 0) = 0`, `‖n‖ ≤ K(|a|‖q‖ + a²‖p‖)` (which implies the paper's
  `O(a|q| + a|q|² + a²|p|)`), `D_q n = O(a)`, `D_p n = O(a²)`, and for the canonical
  component `𝒳_a(w) = X⁰_a + a²(E q + J_c n(a, w))`:
  `D_q𝒳 = O(a²)`, `D_p𝒳 = O(a⁴)`, `D_q²𝒳 = O(a³)`, `D_qD_p𝒳 = O(a⁴)`, `D_p²𝒳 = O(a⁴)`
  (all uniformly on a neighbourhood of `(a, w) = 0`).
* `exact_normal_chart`: for `a ≠ 0` the substitution `Θ(a, ·, ·)` is a bijection onto the full
  configuration space, with explicit inverse (free projection `q = Λ(X - X⁰)/a²`, the affine
  multiplier formulas for `p`), so `w ↦ Θ_a(w) := Θ(a, n(a, w), w)` satisfies all original
  constraints, is injective, and its image is exactly the set of original-constraint solutions
  `Θ(a, n, w)` with `(a, n, w)` in the implicit-function neighbourhood: a coordinate chart on the
  constraint leaf near the prepared record.  (The dimension `323 = 216 + 107` is the dimension of
  the free space `W`; it enters only through the concrete sizes.)
-/

open Filter Set
open scoped Topology

namespace RenewalGeometry

namespace ExactNormalCoordinates

/-! ### Helpers on partial derivatives with an amplitude factor -/

section Helpers

variable {Y V W' : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W'] [NormedSpace ℝ W']

theorem exists_eventually_norm_le {G : Y → W'} {y₀ : Y} (hG : ContinuousAt G y₀) :
    ∃ K, ∀ᶠ y in 𝓝 y₀, ‖G y‖ ≤ K := by
  refine ⟨‖G y₀‖ + 1, ?_⟩
  filter_upwards [hG.eventually (Metric.ball_mem_nhds (G y₀) one_pos)] with y hy
  rw [dist_eq_norm] at hy
  have := norm_sub_norm_le (G y) (G y₀)
  linarith

/-- The `ι`-partial derivative of `A(c y) + c(y)^k • Z(y)`, along a direction `ι` with
`c ∘ ι = 0`, is `c(y)^k • ∂_ι Z(y)`. -/
theorem fderiv_add_pow_smul_comp (c : Y →L[ℝ] ℝ) (ι : V →L[ℝ] Y) (hι : c ∘L ι = 0) (k : ℕ)
    (A : ℝ → W') (Z : Y → W') (y : Y) (hA : DifferentiableAt ℝ A (c y))
    (hZ : DifferentiableAt ℝ Z y) :
    fderiv ℝ (fun z => A (c z) + c z ^ k • Z z) y ∘L ι = c y ^ k • (fderiv ℝ Z y ∘L ι) := by
  have hcv : ∀ v, c (ι v) = 0 := fun v => by
    have := congrArg (fun L => L v) hι
    simpa using this
  have h1 : HasFDerivAt (fun z => A (c z)) ((fderiv ℝ A (c y)).comp c) y :=
    hA.hasFDerivAt.comp y c.hasFDerivAt
  have h2 : HasFDerivAt (fun z => c z ^ k • Z z)
      (c y ^ k • fderiv ℝ Z y + ((k • c y ^ (k - 1)) • c).smulRight (Z y)) y :=
    ((c.hasFDerivAt (x := y)).pow k).smul hZ.hasFDerivAt
  have h3 : HasFDerivAt (fun z => A (c z) + c z ^ k • Z z)
      ((fderiv ℝ A (c y)).comp c +
        (c y ^ k • fderiv ℝ Z y + ((k • c y ^ (k - 1)) • c).smulRight (Z y))) y := h1.add h2
  rw [h3.fderiv]
  ext v
  simp [hcv]

/-- Bound for the `ι`-partial derivative of `A(c y) + c(y)^k • G(y)` with `A`, `G` analytic. -/
theorem norm_fderiv_add_pow_smul_comp_le [CompleteSpace W'] (c : Y →L[ℝ] ℝ) (ι : V →L[ℝ] Y)
    (hι : c ∘L ι = 0) (k : ℕ) (A : ℝ → W') (hA : AnalyticAt ℝ A 0) (G : Y → W')
    (hG : AnalyticAt ℝ G 0) (F : Y → W')
    (hF : ∀ᶠ y in 𝓝 (0 : Y), F y = A (c y) + c y ^ k • G y) :
    ∃ K, ∀ᶠ y in 𝓝 (0 : Y), ‖fderiv ℝ F y ∘L ι‖ ≤ K * |c y| ^ k := by
  obtain ⟨K₀, hK₀⟩ := exists_eventually_norm_le hG.fderiv.continuousAt
  refine ⟨K₀ * ‖ι‖, ?_⟩
  have hGan : ∀ᶠ y in 𝓝 (0 : Y), AnalyticAt ℝ G y := hG.eventually_analyticAt
  have hAan : ∀ᶠ y in 𝓝 (0 : Y), AnalyticAt ℝ A (c y) := by
    have := hA.eventually_analyticAt
    rw [← map_zero c] at this
    exact c.continuous.continuousAt.eventually this
  filter_upwards [hF.eventually_nhds, hGan, hAan, hK₀] with y hy hGy hAy hKy
  rw [Filter.EventuallyEq.fderiv_eq
    (show F =ᶠ[𝓝 y] (fun z => A (c z) + c z ^ k • G z) from hy), fderiv_add_pow_smul_comp c ι hι k A G y hAy.differentiableAt
    hGy.differentiableAt, norm_smul, Real.norm_eq_abs, abs_pow]
  calc |c y| ^ k * ‖fderiv ℝ G y ∘L ι‖ ≤ |c y| ^ k * (‖fderiv ℝ G y‖ * ‖ι‖) := by
        gcongr; exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ |c y| ^ k * (K₀ * ‖ι‖) := by gcongr
    _ = K₀ * ‖ι‖ * |c y| ^ k := by ring

end Helpers

/-! ### The normal-coordinate solve -/

section Coordinates

variable {Nn Qs LA LW Rows Xc : Type*}
  [NormedAddCommGroup Nn] [NormedSpace ℝ Nn] [CompleteSpace Nn]
  [NormedAddCommGroup Qs] [NormedSpace ℝ Qs] [CompleteSpace Qs]
  [NormedAddCommGroup LA] [NormedSpace ℝ LA] [CompleteSpace LA]
  [NormedAddCommGroup LW] [NormedSpace ℝ LW] [CompleteSpace LW]
  [NormedAddCommGroup Rows] [NormedSpace ℝ Rows] [CompleteSpace Rows]
  [NormedAddCommGroup Xc] [NormedSpace ℝ Xc] [CompleteSpace Xc]

variable (Qs LA LW) in
/-- The `q`-direction `q ↦ (0, (q, 0))` in the parameter space `ℝ × W`. -/
def iotaQ : Qs →L[ℝ] ℝ × (Qs × (LA × LW)) :=
  (ContinuousLinearMap.inr ℝ ℝ (Qs × (LA × LW))).comp (ContinuousLinearMap.inl ℝ Qs (LA × LW))

variable (Qs LA LW) in
/-- The `p`-direction `p ↦ (0, (0, p))` in the parameter space `ℝ × W`. -/
def iotaP : (LA × LW) →L[ℝ] ℝ × (Qs × (LA × LW)) :=
  (ContinuousLinearMap.inr ℝ ℝ (Qs × (LA × LW))).comp (ContinuousLinearMap.inr ℝ Qs (LA × LW))

variable (Qs LA LW) in
/-- The amplitude coordinate `(a, w) ↦ a`. -/
def amp : ℝ × (Qs × (LA × LW)) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ (Qs × (LA × LW))

theorem amp_comp_iotaQ : amp Qs LA LW ∘L iotaQ Qs LA LW = 0 := by
  ext v; simp [amp, iotaQ]

theorem amp_comp_iotaP : amp Qs LA LW ∘L iotaP Qs LA LW = 0 := by
  ext v <;> simp [amp, iotaP]

/-- The canonical component `𝒳_a(w) = X⁰_a + a² (E q + J_c n)` of the substitution
`eq:supp-exact-normal-chart`, as a function of `y = (a, w)` for a given normal solve `nf`. -/
def canonicalComponent (X0 : ℝ → Xc) (E : Qs →L[ℝ] Xc) (Jc : Nn →L[ℝ] Xc)
    (nf : ℝ × (Qs × (LA × LW)) → Nn) (y : ℝ × (Qs × (LA × LW))) : Xc :=
  X0 y.1 + y.1 ^ 2 • (E y.2.1 + Jc (nf y))

/-- Mean-value bound for the normal solve: if on the `δ`-ball `ψ` is differentiable with
`‖D_q ψ‖ ≤ K_G |a|`, `‖D_p ψ‖ ≤ K_H a²` and `ψ(a, 0) = 0`, then
`‖ψ(a, q, p)‖ ≤ K_H a² ‖p‖ + K_G |a| ‖q‖` on the ball. -/
theorem normal_solve_norm_le (ψ : ℝ × (Qs × (LA × LW)) → Nn) {δ KG KH : ℝ}
    (hB : ∀ y ∈ Metric.ball (0 : ℝ × (Qs × (LA × LW))) δ,
      DifferentiableAt ℝ ψ y ∧ ‖fderiv ℝ ψ y ∘L iotaQ Qs LA LW‖ ≤ KG * |y.1| ∧
        ‖fderiv ℝ ψ y ∘L iotaP Qs LA LW‖ ≤ KH * y.1 ^ 2 ∧ ψ (y.1, 0) = 0)
    (a : ℝ) (q : Qs) (p : LA × LW)
    (hy : ((a, q, p) : ℝ × (Qs × (LA × LW))) ∈ Metric.ball 0 δ) :
    ‖ψ (a, q, p)‖ ≤ KH * a ^ 2 * ‖p‖ + KG * |a| * ‖q‖ := by
  have hδ : 0 < δ := by
    have := Metric.mem_ball.1 hy
    exact lt_of_le_of_lt dist_nonneg this
  have hyB' := hy
  rw [mem_ball_zero_iff] at hyB'
  have ha_lt : ‖a‖ < δ := (norm_fst_le _).trans_lt hyB'
  have hq_lt : ‖q‖ < δ :=
    ((norm_fst_le (q, p)).trans (norm_snd_le ((a, q, p) : ℝ × (Qs × (LA × LW))))).trans_lt hyB'
  have hp_lt : ‖p‖ < δ :=
    ((norm_snd_le (q, p)).trans (norm_snd_le ((a, q, p) : ℝ × (Qs × (LA × LW))))).trans_lt hyB'
  have hp_path : ‖ψ (a, q, p) - ψ (a, q, 0)‖ ≤ KH * a ^ 2 * ‖p - 0‖ := by
    have hs : Convex ℝ (Metric.ball (0 : LA × LW) δ) := convex_ball _ _
    have hmem : ∀ p' ∈ Metric.ball (0 : LA × LW) δ,
        ((a, q, p') : ℝ × (Qs × (LA × LW))) ∈ Metric.ball 0 δ := by
      intro p' hp'
      rw [mem_ball_zero_iff] at hp' ⊢
      simp only [Prod.norm_def]
      exact max_lt ha_lt (max_lt hq_lt hp')
    refine hs.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (f := fun p' => ψ (a, q, p')) (f' := fun p' => fderiv ℝ ψ (a, q, p') ∘L iotaP Qs LA LW)
      ?_ ?_ (Metric.mem_ball_self hδ) (by rw [mem_ball_zero_iff]; exact hp_lt)
    · intro p' hp'
      have hd := ((hB _ (hmem p' hp')).1).hasFDerivAt
      have hlin : HasFDerivAt (fun p'' : LA × LW => ((a, q, p'') : ℝ × (Qs × (LA × LW))))
          (iotaP Qs LA LW) p' := by
        have : (fun p'' : LA × LW => ((a, q, p'') : ℝ × (Qs × (LA × LW)))) =
            fun p'' => ((a, q, 0) : ℝ × (Qs × (LA × LW))) + iotaP Qs LA LW p'' := by
          funext p''; simp [iotaP]
        rw [this]
        exact ((iotaP Qs LA LW).hasFDerivAt).const_add _
      exact (hd.comp p' hlin).hasFDerivWithinAt
    · intro p' hp'
      exact (hB _ (hmem p' hp')).2.2.1
  have hq_path : ‖ψ (a, q, 0) - ψ (a, 0, 0)‖ ≤ KG * |a| * ‖q - 0‖ := by
    have hs : Convex ℝ (Metric.ball (0 : Qs) δ) := convex_ball _ _
    have hmem : ∀ q' ∈ Metric.ball (0 : Qs) δ,
        ((a, q', (0 : LA × LW)) : ℝ × (Qs × (LA × LW))) ∈ Metric.ball 0 δ := by
      intro q' hq'
      rw [mem_ball_zero_iff] at hq' ⊢
      simp only [Prod.norm_def, norm_zero]
      exact max_lt ha_lt (max_lt hq' (by simpa using hδ))
    refine hs.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (f := fun q' => ψ (a, q', 0)) (f' := fun q' => fderiv ℝ ψ (a, q', 0) ∘L iotaQ Qs LA LW)
      ?_ ?_ (Metric.mem_ball_self hδ) (by rw [mem_ball_zero_iff]; exact hq_lt)
    · intro q' hq'
      have hd := ((hB _ (hmem q' hq')).1).hasFDerivAt
      have hlin : HasFDerivAt
          (fun q'' : Qs => ((a, q'', (0 : LA × LW)) : ℝ × (Qs × (LA × LW))))
          (iotaQ Qs LA LW) q' := by
        have : (fun q'' : Qs => ((a, q'', (0 : LA × LW)) : ℝ × (Qs × (LA × LW)))) =
            fun q'' => ((a, 0, 0) : ℝ × (Qs × (LA × LW))) + iotaQ Qs LA LW q'' := by
          funext q''; simp [iotaQ]
        rw [this]
        exact ((iotaQ Qs LA LW).hasFDerivAt).const_add _
      exact (hd.comp q' hlin).hasFDerivWithinAt
    · intro q' hq'
      exact (hB _ (hmem q' hq')).2.1
  have hz : ψ (a, 0, 0) = 0 := (hB _ hy).2.2.2
  rw [sub_zero] at hp_path hq_path
  rw [hz, sub_zero] at hq_path
  calc ‖ψ (a, q, p)‖ = ‖(ψ (a, q, p) - ψ (a, q, 0)) + ψ (a, q, 0)‖ := by rw [sub_add_cancel]
    _ ≤ ‖ψ (a, q, p) - ψ (a, q, 0)‖ + ‖ψ (a, q, 0)‖ := norm_add_le _ _
    _ ≤ KH * a ^ 2 * ‖p‖ + KG * |a| * ‖q‖ := add_le_add hp_path hq_path

/-- `‖a² • E + a³ • T‖ ≤ a² (‖E‖ + ‖T‖)` for `|a| ≤ 1`. -/
theorem norm_sq_smul_add_cube_smul_le {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (a : ℝ) (ha : |a| ≤ 1) (E T : Z) : ‖a ^ 2 • E + a ^ 3 • T‖ ≤ a ^ 2 * (‖E‖ + ‖T‖) := by
  have h1 : ‖a ^ 2 • E‖ = a ^ 2 * ‖E‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg a)]
  have h2 : ‖a ^ 3 • T‖ ≤ a ^ 2 * ‖T‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_pow]
    have : |a| ^ 3 ≤ a ^ 2 := by
      rw [show |a| ^ 3 = |a| ^ 2 * |a| by ring, sq_abs]
      calc a ^ 2 * |a| ≤ a ^ 2 * 1 := by gcongr
        _ = a ^ 2 := mul_one _
    gcongr
  calc ‖a ^ 2 • E + a ^ 3 • T‖ ≤ ‖a ^ 2 • E‖ + ‖a ^ 3 • T‖ := norm_add_le _ _
    _ ≤ a ^ 2 * ‖E‖ + a ^ 2 * ‖T‖ := by rw [h1]; gcongr
    _ = a ^ 2 * (‖E‖ + ‖T‖) := by ring

set_option maxHeartbeats 1000000 in
/-- **Exact nonlinear constraint coordinates** (`lem:supp-exact-normal-coordinates`, analytic
part and derivative orders).  Under the (C2) hypotheses there is an analytic normal solve
`n = nf (a, w)` with `nf 0 = 0`, `𝒫(a, nf(a,w), w) = 0`, local uniqueness of the solution,
`nf (a, 0) = 0`, and constants `K` such that near `(a, w) = 0`:
`‖n‖ ≤ K(|a|‖q‖ + a²‖p‖)`, `‖D_q n‖ ≤ K|a|`, `‖D_p n‖ ≤ K a²`, and for the canonical component
`𝒳 = X⁰_a + a²(E q + J_c n)`: `‖D_q𝒳‖ ≤ K a²`, `‖D_p𝒳‖ ≤ K a⁴`, `‖D_q²𝒳‖ ≤ K|a|³`,
`‖D_qD_p𝒳‖ ≤ K a⁴`, `‖D_p²𝒳‖ ≤ K a⁴`. -/
theorem exact_normal_coordinates (P : (ℝ × (Qs × (LA × LW))) × Nn → Rows)
    (hP : AnalyticAt ℝ P 0) (hPzero : ∀ᶠ a in 𝓝 (0 : ℝ), P ((a, 0), 0) = 0)
    (C : Nn ≃L[ℝ] Rows) (hPlin : ∀ w n, P ((0, w), n) = C n)
    (Pq : (ℝ × (Qs × (LA × LW))) × Nn → (Qs →L[ℝ] Rows)) (hPq : AnalyticAt ℝ Pq 0)
    (hdq : ∀ᶠ x in 𝓝 (0 : (ℝ × (Qs × (LA × LW))) × Nn),
      fderiv ℝ P x ∘L (ContinuousLinearMap.inl ℝ _ Nn ∘L iotaQ Qs LA LW) = x.1.1 • Pq x)
    (Pp : (ℝ × (Qs × (LA × LW))) × Nn → ((LA × LW) →L[ℝ] Rows)) (hPp : AnalyticAt ℝ Pp 0)
    (hdp : ∀ᶠ x in 𝓝 (0 : (ℝ × (Qs × (LA × LW))) × Nn),
      fderiv ℝ P x ∘L (ContinuousLinearMap.inl ℝ _ Nn ∘L iotaP Qs LA LW) =
        x.1.1 ^ 2 • Pp x)
    (X0 : ℝ → Xc) (hX0 : AnalyticAt ℝ X0 0) (E : Qs →L[ℝ] Xc) (Jc : Nn →L[ℝ] Xc) :
    ∃ nf : ℝ × (Qs × (LA × LW)) → Nn, AnalyticAt ℝ nf 0 ∧ nf 0 = 0 ∧
      (∀ᶠ y in 𝓝 (0 : ℝ × (Qs × (LA × LW))), P (y, nf y) = 0) ∧
      (∀ᶠ x in 𝓝 (0 : (ℝ × (Qs × (LA × LW))) × Nn), P x = 0 ↔ nf x.1 = x.2) ∧
      (∀ᶠ a in 𝓝 (0 : ℝ), nf (a, 0) = 0) ∧
      ∃ K, ∀ᶠ y in 𝓝 (0 : ℝ × (Qs × (LA × LW))),
        ‖nf y‖ ≤ K * (|y.1| * ‖y.2.1‖ + y.1 ^ 2 * ‖y.2.2‖) ∧
        ‖fderiv ℝ nf y ∘L iotaQ Qs LA LW‖ ≤ K * |y.1| ∧
        ‖fderiv ℝ nf y ∘L iotaP Qs LA LW‖ ≤ K * y.1 ^ 2 ∧
        ‖fderiv ℝ (canonicalComponent X0 E Jc nf) y ∘L iotaQ Qs LA LW‖ ≤ K * y.1 ^ 2 ∧
        ‖fderiv ℝ (canonicalComponent X0 E Jc nf) y ∘L iotaP Qs LA LW‖ ≤ K * y.1 ^ 4 ∧
        ‖fderiv ℝ (fun z => fderiv ℝ (canonicalComponent X0 E Jc nf) z ∘L
          iotaQ Qs LA LW) y ∘L iotaQ Qs LA LW‖ ≤ K * |y.1| ^ 3 ∧
        ‖fderiv ℝ (fun z => fderiv ℝ (canonicalComponent X0 E Jc nf) z ∘L
          iotaP Qs LA LW) y ∘L iotaQ Qs LA LW‖ ≤ K * y.1 ^ 4 ∧
        ‖fderiv ℝ (fun z => fderiv ℝ (canonicalComponent X0 E Jc nf) z ∘L
          iotaP Qs LA LW) y ∘L iotaP Qs LA LW‖ ≤ K * y.1 ^ 4 := by
  set ιq := iotaQ Qs LA LW
  set ιp := iotaP Qs LA LW
  set c := amp Qs LA LW
  -- the normal partial derivative at `0`
  have hP00 : P 0 = 0 := by
    rw [show (0 : (ℝ × (Qs × (LA × LW))) × Nn) = ((0, 0), 0) from rfl, hPlin, map_zero]
  have hC : fderiv ℝ P 0 ∘L ContinuousLinearMap.inr ℝ (ℝ × (Qs × (LA × LW))) Nn =
      (C : Nn →L[ℝ] Rows) := by
    have h1 : HasFDerivAt (fun n : Nn => P ((0 : ℝ × (Qs × (LA × LW))), n))
        (fderiv ℝ P 0 ∘L ContinuousLinearMap.inr ℝ (ℝ × (Qs × (LA × LW))) Nn) 0 := by
      have h := hP.differentiableAt.hasFDerivAt
      have hin := hasFDerivAt_prodMk_right (𝕜 := ℝ) (0 : ℝ × (Qs × (LA × LW))) (0 : Nn)
      exact h.comp (0 : Nn) hin
    have h2 : HasFDerivAt (fun n : Nn => P ((0 : ℝ × (Qs × (LA × LW))), n))
        (C : Nn →L[ℝ] Rows) 0 := by
      have : (fun n : Nn => P ((0 : ℝ × (Qs × (LA × LW))), n)) = fun n => C n :=
        funext fun n => by
          rw [show ((0 : ℝ × (Qs × (LA × LW))), n) = ((0, 0), n) from rfl, hPlin]
      rw [this]
      exact C.hasFDerivAt
    exact h1.unique h2
  have hinv : (fderiv ℝ P 0 ∘L ContinuousLinearMap.inr ℝ (ℝ × (Qs × (LA × LW))) Nn).IsInvertible :=
    ⟨C, hC.symm⟩
  obtain ⟨ψ, hψ0, hψan, hsol, huniq, -⟩ :=
    AnalyticImplicit.analytic_implicit_function (u := (0 : (ℝ × (Qs × (LA × LW))) × Nn)) hP hinv
  simp only [Prod.fst_zero, Prod.snd_zero] at hψ0 hsol hψan
  rw [hP00] at hsol huniq
  have hsol0 : ∀ᶠ y in 𝓝 (0 : ℝ × (Qs × (LA × LW))), P (y, ψ y) = 0 := hsol
  refine ⟨ψ, hψan, hψ0, hsol0, ?_, ?_, ?_⟩
  · exact huniq
  · -- `n(a, 0) = 0`
    have hcont : Continuous fun a : ℝ => (((a, 0) : ℝ × (Qs × (LA × LW))), (0 : Nn)) := by
      fun_prop
    have h0 : (fun a : ℝ => (((a, 0) : ℝ × (Qs × (LA × LW))), (0 : Nn))) 0 = 0 := rfl
    have hu := hcont.continuousAt.eventually (h0 ▸ huniq)
    filter_upwards [hu, hPzero] with a ha hza
    exact (ha.1 hza)
  -- divisibility of the partial derivatives of the solve
  obtain ⟨G, hG, hGeq⟩ := AnalyticImplicit.implicit_fderiv_comp_eq_smul P hP ψ hψan hψ0 hsol0
    C hC ιq (fun y => y.1) Pq hPq hdq
  obtain ⟨H, hH, hHeq⟩ := AnalyticImplicit.implicit_fderiv_comp_eq_smul P hP ψ hψan hψ0 hsol0
    C hC ιp (fun y => y.1 ^ 2) Pp hPp hdp
  obtain ⟨KG, hKG⟩ := exists_eventually_norm_le hG.continuousAt
  obtain ⟨KH, hKH⟩ := exists_eventually_norm_le hH.continuousAt
  -- the canonical component
  set X := canonicalComponent X0 E Jc ψ with hXdef
  have hψev : ∀ᶠ y in 𝓝 (0 : ℝ × (Qs × (LA × LW))), AnalyticAt ℝ ψ y := hψan.eventually_analyticAt
  have hX0ev : ∀ᶠ y in 𝓝 (0 : ℝ × (Qs × (LA × LW))), AnalyticAt ℝ X0 (c y) := by
    have := hX0.eventually_analyticAt
    rw [← map_zero c] at this
    exact c.continuous.continuousAt.eventually this
  set Z : ℝ × (Qs × (LA × LW)) → Xc := fun z => E z.2.1 + Jc (ψ z) with hZdef
  have hXZ : X = fun z => X0 (c z) + c z ^ 2 • Z z := rfl
  have hZq : ∀ y, DifferentiableAt ℝ ψ y → fderiv ℝ Z y ∘L ιq = E + Jc ∘L (fderiv ℝ ψ y ∘L ιq) := by
    intro y hy
    have hlin : HasFDerivAt (fun z : ℝ × (Qs × (LA × LW)) => E z.2.1)
        (E ∘L ((ContinuousLinearMap.fst ℝ Qs (LA × LW)).comp
          (ContinuousLinearMap.snd ℝ ℝ (Qs × (LA × LW))))) y :=
      (E ∘L ((ContinuousLinearMap.fst ℝ Qs (LA × LW)).comp
          (ContinuousLinearMap.snd ℝ ℝ (Qs × (LA × LW))))).hasFDerivAt
    have hJ : HasFDerivAt (fun z => Jc (ψ z)) (Jc ∘L fderiv ℝ ψ y) y :=
      Jc.hasFDerivAt.comp y hy.hasFDerivAt
    have h3 : HasFDerivAt Z ((E ∘L ((ContinuousLinearMap.fst ℝ Qs (LA × LW)).comp
          (ContinuousLinearMap.snd ℝ ℝ (Qs × (LA × LW))))) + Jc ∘L fderiv ℝ ψ y) y :=
      hlin.add hJ
    rw [h3.fderiv]
    ext v
    simp [ιq, iotaQ]
  have hZp : ∀ y, DifferentiableAt ℝ ψ y → fderiv ℝ Z y ∘L ιp = Jc ∘L (fderiv ℝ ψ y ∘L ιp) := by
    intro y hy
    have hlin : HasFDerivAt (fun z : ℝ × (Qs × (LA × LW)) => E z.2.1)
        (E ∘L ((ContinuousLinearMap.fst ℝ Qs (LA × LW)).comp
          (ContinuousLinearMap.snd ℝ ℝ (Qs × (LA × LW))))) y :=
      (E ∘L ((ContinuousLinearMap.fst ℝ Qs (LA × LW)).comp
          (ContinuousLinearMap.snd ℝ ℝ (Qs × (LA × LW))))).hasFDerivAt
    have hJ : HasFDerivAt (fun z => Jc (ψ z)) (Jc ∘L fderiv ℝ ψ y) y :=
      Jc.hasFDerivAt.comp y hy.hasFDerivAt
    have h3 : HasFDerivAt Z ((E ∘L ((ContinuousLinearMap.fst ℝ Qs (LA × LW)).comp
          (ContinuousLinearMap.snd ℝ ℝ (Qs × (LA × LW))))) + Jc ∘L fderiv ℝ ψ y) y :=
      hlin.add hJ
    rw [h3.fderiv]
    ext v <;> simp [ιp, iotaP]
  -- first partial derivatives of the canonical component
  have hXq : ∀ᶠ y in 𝓝 (0 : ℝ × (Qs × (LA × LW))),
      fderiv ℝ X y ∘L ιq = (fun a : ℝ => a ^ 2 • E) (c y) + c y ^ 3 • (Jc ∘L G y) := by
    filter_upwards [hψev, hX0ev, hGeq] with y hy hXy hGy
    rw [hXZ, fderiv_add_pow_smul_comp c ιq amp_comp_iotaQ 2 X0 Z y hXy.differentiableAt
      (by fun_prop (disch := exact hy.differentiableAt)), hZq y hy.differentiableAt, hGy]
    ext v
    simp [c, amp, pow_succ, smul_smul, mul_comm]
  have hXp : ∀ᶠ y in 𝓝 (0 : ℝ × (Qs × (LA × LW))),
      fderiv ℝ X y ∘L ιp = (fun _ : ℝ => (0 : (LA × LW) →L[ℝ] Xc)) (c y) + c y ^ 4 • (Jc ∘L H y) := by
    filter_upwards [hψev, hX0ev, hHeq] with y hy hXy hHy
    rw [hXZ, fderiv_add_pow_smul_comp c ιp amp_comp_iotaP 2 X0 Z y hXy.differentiableAt
      (by fun_prop (disch := exact hy.differentiableAt)), hZp y hy.differentiableAt, hHy]
    ext v <;> simp [c, amp, smul_smul, ← pow_add]
  -- second partial derivatives
  have hJG : AnalyticAt ℝ (fun y => Jc ∘L G y) 0 :=
    ((ContinuousLinearMap.compL ℝ Qs Nn Xc Jc).analyticAt _).comp hG
  have hJH : AnalyticAt ℝ (fun y => Jc ∘L H y) 0 :=
    ((ContinuousLinearMap.compL ℝ (LA × LW) Nn Xc Jc).analyticAt _).comp hH
  obtain ⟨K1, hK1⟩ := norm_fderiv_add_pow_smul_comp_le c ιq amp_comp_iotaQ 3
    (fun a : ℝ => a ^ 2 • E) (by fun_prop) _ hJG _ hXq
  obtain ⟨K2, hK2⟩ := norm_fderiv_add_pow_smul_comp_le c ιq amp_comp_iotaQ 4
    (fun _ : ℝ => (0 : (LA × LW) →L[ℝ] Xc)) analyticAt_const _ hJH _ hXp
  obtain ⟨K3, hK3⟩ := norm_fderiv_add_pow_smul_comp_le c ιp amp_comp_iotaP 4
    (fun _ : ℝ => (0 : (LA × LW) →L[ℝ] Xc)) analyticAt_const _ hJH _ hXp
  -- the bound on `n` itself, by the mean value inequality in `q` and in `p`
  have hball : ∃ δ > 0, ∀ y ∈ Metric.ball (0 : ℝ × (Qs × (LA × LW))) δ,
      DifferentiableAt ℝ ψ y ∧ ‖fderiv ℝ ψ y ∘L ιq‖ ≤ KG * |y.1| ∧
        ‖fderiv ℝ ψ y ∘L ιp‖ ≤ KH * y.1 ^ 2 ∧ ψ (y.1, 0) = 0 := by
    have hn0 : ∀ᶠ y in 𝓝 (0 : ℝ × (Qs × (LA × LW))), ψ (y.1, 0) = 0 := by
      have hcont : Continuous fun y : ℝ × (Qs × (LA × LW)) => y.1 := continuous_fst
      have h' : ∀ᶠ a in 𝓝 (0 : ℝ), ψ (a, 0) = 0 := by
        have hc2 : Continuous fun a : ℝ => (((a, 0) : ℝ × (Qs × (LA × LW))), (0 : Nn)) := by
          fun_prop
        have hu := hc2.continuousAt.eventually ((show (fun a : ℝ =>
          (((a, 0) : ℝ × (Qs × (LA × LW))), (0 : Nn))) 0 = 0 from rfl) ▸ huniq)
        filter_upwards [hu, hPzero] with a ha hza
        exact ha.1 hza
      have ht : Tendsto (fun y : ℝ × (Qs × (LA × LW)) => y.1) (𝓝 0) (𝓝 0) := by
        simpa using hcont.tendsto (0 : ℝ × (Qs × (LA × LW)))
      exact ht.eventually h'
    have hall : ∀ᶠ y in 𝓝 (0 : ℝ × (Qs × (LA × LW))),
        DifferentiableAt ℝ ψ y ∧ ‖fderiv ℝ ψ y ∘L ιq‖ ≤ KG * |y.1| ∧
          ‖fderiv ℝ ψ y ∘L ιp‖ ≤ KH * y.1 ^ 2 ∧ ψ (y.1, 0) = 0 := by
      filter_upwards [hψev, hGeq, hHeq, hKG, hKH, hn0] with y h1 h2 h3 h4 h5 h6
      refine ⟨h1.differentiableAt, ?_, ?_, h6⟩
      · rw [h2, norm_smul, Real.norm_eq_abs, mul_comm]
        exact mul_le_mul_of_nonneg_right h4 (abs_nonneg _)
      · rw [h3, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), mul_comm]
        exact mul_le_mul_of_nonneg_right h5 (sq_nonneg _)
    exact Metric.eventually_nhds_iff_ball.1 hall
  obtain ⟨δ, hδ, hB⟩ := hball
  set K0 := max (max (max KG KH) 0) (max (max K1 K2) K3) with hK0def
  set K := K0 + (‖E‖ + ‖Jc‖ * max KG 0 + ‖Jc‖ * max KH 0) with hKdef
  refine ⟨K, ?_⟩
  have hK0nn : 0 ≤ K0 := le_max_of_le_left (le_max_right _ _)
  have hJG0 : 0 ≤ ‖Jc‖ * max KG 0 := by positivity
  have hJH0 : 0 ≤ ‖Jc‖ * max KH 0 := by positivity
  have hE0 : 0 ≤ ‖E‖ := norm_nonneg _
  have hKG' : KG ≤ K := by
    have : KG ≤ K0 := le_max_of_le_left (le_max_of_le_left (le_max_left _ _))
    linarith
  have hKH' : KH ≤ K := by
    have : KH ≤ K0 := le_max_of_le_left (le_max_of_le_left (le_max_right _ _))
    linarith
  have hK1' : K1 ≤ K := by
    have : K1 ≤ K0 := le_max_of_le_right (le_max_of_le_left (le_max_left _ _))
    linarith
  have hK2' : K2 ≤ K := by
    have : K2 ≤ K0 := le_max_of_le_right (le_max_of_le_left (le_max_right _ _))
    linarith
  have hK3' : K3 ≤ K := by
    have : K3 ≤ K0 := le_max_of_le_right (le_max_right _ _)
    linarith
  have hKE : ‖E‖ + ‖Jc‖ * max KG 0 ≤ K := by linarith
  have hKJ : ‖Jc‖ * max KH 0 ≤ K := by linarith
  have hsmall : ∀ᶠ y in 𝓝 (0 : ℝ × (Qs × (LA × LW))), |y.1| ≤ 1 := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ × (Qs × (LA × LW))) one_pos] with y hy
    rw [mem_ball_zero_iff] at hy
    exact (norm_fst_le y).trans hy.le
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ × (Qs × (LA × LW))) hδ, hsmall, hXq, hXp, hK1,
    hK2, hK3, hGeq, hHeq, hKG, hKH]
    with y hyB hy1 hXqy hXpy hK1y hK2y hK3y hGy hHy hKGy hKHy
  have hcy : c y = y.1 := rfl
  rw [hcy] at hXqy hXpy hK1y hK2y hK3y
  have ha4 : |y.1| ^ 4 = y.1 ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := normal_solve_norm_le ψ hB y.1 y.2.1 y.2.2 hyB
    calc ‖ψ y‖ ≤ KH * y.1 ^ 2 * ‖y.2.2‖ + KG * |y.1| * ‖y.2.1‖ := this
      _ ≤ K * y.1 ^ 2 * ‖y.2.2‖ + K * |y.1| * ‖y.2.1‖ := by gcongr
      _ = K * (|y.1| * ‖y.2.1‖ + y.1 ^ 2 * ‖y.2.2‖) := by ring
  · rw [hGy, norm_smul, Real.norm_eq_abs]
    calc |y.1| * ‖G y‖ ≤ |y.1| * K := by gcongr; linarith
      _ = K * |y.1| := by ring
  · rw [hHy, norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    calc y.1 ^ 2 * ‖H y‖ ≤ y.1 ^ 2 * K := by gcongr; linarith
      _ = K * y.1 ^ 2 := by ring
  · rw [hXqy]
    show ‖y.1 ^ 2 • E + y.1 ^ 3 • (Jc ∘L G y)‖ ≤ K * y.1 ^ 2
    have h1 : ‖Jc ∘L G y‖ ≤ ‖Jc‖ * max KG 0 :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (by gcongr; exact hKGy.trans (le_max_left _ _))
    calc ‖y.1 ^ 2 • E + y.1 ^ 3 • (Jc ∘L G y)‖ ≤ y.1 ^ 2 * (‖E‖ + ‖Jc ∘L G y‖) :=
          norm_sq_smul_add_cube_smul_le y.1 hy1 E _
      _ ≤ y.1 ^ 2 * K := by gcongr; linarith
      _ = K * y.1 ^ 2 := by ring
  · rw [hXpy]
    show ‖(0 : (LA × LW) →L[ℝ] Xc) + y.1 ^ 4 • (Jc ∘L H y)‖ ≤ K * y.1 ^ 4
    rw [zero_add, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h1 : ‖Jc ∘L H y‖ ≤ ‖Jc‖ * max KH 0 :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (by gcongr; exact hKHy.trans (le_max_left _ _))
    calc y.1 ^ 4 * ‖Jc ∘L H y‖ ≤ y.1 ^ 4 * K := by gcongr; linarith
      _ = K * y.1 ^ 4 := by ring
  · calc _ ≤ K1 * |y.1| ^ 3 := hK1y
      _ ≤ K * |y.1| ^ 3 := by gcongr
  · calc _ ≤ K2 * |y.1| ^ 4 := hK2y
      _ ≤ K * y.1 ^ 4 := by rw [ha4]; gcongr
  · calc _ ≤ K3 * |y.1| ^ 4 := hK3y
      _ ≤ K * y.1 ^ 4 := by rw [ha4]; gcongr

end Coordinates


/-! ### The coordinate chart on the constraint leaf -/

section Chart

variable {Nn Qs LA LW Rows Xc Cons : Type*}
  [NormedAddCommGroup Nn] [NormedSpace ℝ Nn]
  [NormedAddCommGroup Qs] [NormedSpace ℝ Qs]
  [NormedAddCommGroup LA] [NormedSpace ℝ LA]
  [NormedAddCommGroup LW] [NormedSpace ℝ LW]
  [NormedAddCommGroup Rows] [NormedSpace ℝ Rows]
  [NormedAddCommGroup Xc] [NormedSpace ℝ Xc] [Zero Cons]

/-- The substitution `Θ(a, n, w)` of `eq:supp-exact-normal-chart`:
`X = X⁰_a + a²(E q + J_c n)`, `λ_A = λ⁰_{a,A} + a²(p_A - H p_W)`, `λ_W = λ⁰_{a,W} + a p_W`. -/
def normalChart (X0 : ℝ → Xc) (lA0 : ℝ → LA) (lW0 : ℝ → LW) (E : Qs →L[ℝ] Xc)
    (Jc : Nn →L[ℝ] Xc) (Hsh : LW →L[ℝ] LA) (a : ℝ) (n : Nn) (w : Qs × (LA × LW)) :
    Xc × (LA × LW) :=
  (X0 a + a ^ 2 • (E w.1 + Jc n), lA0 a + a ^ 2 • (w.2.1 - Hsh w.2.2), lW0 a + a • w.2.2)

/-- **The substitution is an affine bijection for `a ≠ 0`** (from (C1)).  With the free
projection `Λ` (`Λ E = I`, `Λ J_c = 0`) and `𝒞₀` (`𝒞₀ E = 0`, `𝒞₀ J_c = C` invertible, `E` onto
`ker 𝒞₀`), every configuration `(X, λ)` is `Θ(a, n, w)` for exactly one `(n, w)`; explicitly
`q = Λ(X - X⁰_a)/a²`, `n = C⁻¹ 𝒞₀ (X - X⁰_a)/a²`, `p_W = (λ_W - λ⁰_W)/a`,
`p_A = (λ_A - λ⁰_A)/a² + H p_W`. -/
theorem normalChart_bijective (X0 : ℝ → Xc) (lA0 : ℝ → LA) (lW0 : ℝ → LW) (E : Qs →L[ℝ] Xc)
    (Jc : Nn →L[ℝ] Xc) (Hsh : LW →L[ℝ] LA) (Λ : Xc →L[ℝ] Qs) (hΛE : ∀ q, Λ (E q) = q)
    (hΛJ : ∀ n, Λ (Jc n) = 0) (C0 : Xc →L[ℝ] Rows) (C : Nn ≃L[ℝ] Rows)
    (hC0J : ∀ n, C0 (Jc n) = C n) (hC0E : ∀ q, C0 (E q) = 0)
    (hEonto : ∀ v, C0 v = 0 → ∃ q, E q = v) {a : ℝ} (ha : a ≠ 0) :
    Function.Bijective fun nw : Nn × (Qs × (LA × LW)) =>
      normalChart X0 lA0 lW0 E Jc Hsh a nw.1 nw.2 := by
  have ha2 : a ^ 2 ≠ 0 := pow_ne_zero 2 ha
  constructor
  · rintro ⟨n, q, pA, pW⟩ ⟨n', q', pA', pW'⟩ h
    simp only [normalChart, Prod.mk.injEq, add_right_inj] at h
    obtain ⟨h1, h2, h3⟩ := h
    have h1' : E q + Jc n = E q' + Jc n' := smul_right_injective _ ha2 h1
    have hW : pW = pW' := smul_right_injective _ ha h3
    have hq : q = q' := by
      have := congrArg Λ h1'
      simpa [hΛE, hΛJ] using this
    have hn : n = n' := by
      have := congrArg C0 h1'
      simp only [map_add, hC0E, hC0J, zero_add] at this
      exact C.injective this
    have hA : pA = pA' := by
      have := smul_right_injective _ ha2 h2
      rw [hW] at this
      exact sub_left_injective this
    subst hq hn hW hA
    rfl
  · rintro ⟨X, lA, lW⟩
    set v := (a ^ 2)⁻¹ • (X - X0 a)
    set n := C.symm (C0 v)
    have hker : C0 (v - Jc n) = 0 := by
      simp [n, hC0J]
    obtain ⟨q, hq⟩ := hEonto _ hker
    set pW := a⁻¹ • (lW - lW0 a)
    set pA := (a ^ 2)⁻¹ • (lA - lA0 a) + Hsh pW
    refine ⟨(n, q, pA, pW), ?_⟩
    simp only [normalChart, Prod.mk.injEq]
    refine ⟨?_, ?_, ?_⟩
    · rw [hq, sub_add_cancel]
      simp only [v, smul_smul, mul_inv_cancel₀ ha2, one_smul, add_sub_cancel]
    · simp only [pA, add_sub_cancel_right, smul_smul, mul_inv_cancel₀ ha2, one_smul,
        add_sub_cancel]
    · simp only [pW, smul_smul, mul_inv_cancel₀ ha, one_smul, add_sub_cancel]

/-- **Coordinate chart on the constraint leaf** (`lem:supp-exact-normal-coordinates`, chart
clause).  Let `nf` be the normal solve of the divided equations (`𝒫(a, nf(a,w), w) = 0` near `0`,
with local uniqueness), and suppose the divided map is the row-rescaling of the original
constraints, `P_h(Θ(a, n, w)) = 0 ↔ 𝒫(a, n, w) = 0` for `a ≠ 0` (`hdiv`).  Then, writing
`Θ_a(w) = Θ(a, nf(a,w), w)`:
1. near `(a, w) = 0` with `a ≠ 0`, `Θ_a(w)` satisfies all original constraints;
2. for `a ≠ 0`, `w ↦ Θ_a(w)` is injective (free projection and affine multiplier formulas);
3. near `(a, n, w) = 0` with `a ≠ 0`, every original-constraint solution `Θ(a, n, w)` equals
   `Θ_a(w)`;
4. for `a ≠ 0`, every configuration is `Θ(a, n, w)` for a unique `(n, w)`.
So for small `a > 0` the map `w ↦ Θ_a(w)` parametrizes exactly the constraint solutions in the
`a`-scaled neighbourhood of the prepared record. -/
theorem exact_normal_chart (X0 : ℝ → Xc) (lA0 : ℝ → LA) (lW0 : ℝ → LW) (E : Qs →L[ℝ] Xc)
    (Jc : Nn →L[ℝ] Xc) (Hsh : LW →L[ℝ] LA) (Λ : Xc →L[ℝ] Qs) (hΛE : ∀ q, Λ (E q) = q)
    (hΛJ : ∀ n, Λ (Jc n) = 0) (C0 : Xc →L[ℝ] Rows) (C : Nn ≃L[ℝ] Rows)
    (hC0J : ∀ n, C0 (Jc n) = C n) (hC0E : ∀ q, C0 (E q) = 0)
    (hEonto : ∀ v, C0 v = 0 → ∃ q, E q = v)
    (P : (ℝ × (Qs × (LA × LW))) × Nn → Rows) (Ph : Xc × (LA × LW) → Cons)
    (hdiv : ∀ a, a ≠ 0 → ∀ n w, Ph (normalChart X0 lA0 lW0 E Jc Hsh a n w) = 0 ↔
      P ((a, w), n) = 0)
    (nf : ℝ × (Qs × (LA × LW)) → Nn)
    (hsol : ∀ᶠ y in 𝓝 (0 : ℝ × (Qs × (LA × LW))), P (y, nf y) = 0)
    (huniq : ∀ᶠ x in 𝓝 (0 : (ℝ × (Qs × (LA × LW))) × Nn), P x = 0 ↔ nf x.1 = x.2) :
    (∀ᶠ y in 𝓝 (0 : ℝ × (Qs × (LA × LW))), y.1 ≠ 0 →
      Ph (normalChart X0 lA0 lW0 E Jc Hsh y.1 (nf y) y.2) = 0) ∧
    (∀ a, a ≠ 0 → ∀ w w', normalChart X0 lA0 lW0 E Jc Hsh a (nf (a, w)) w =
      normalChart X0 lA0 lW0 E Jc Hsh a (nf (a, w')) w' → w = w') ∧
    (∀ᶠ x in 𝓝 (0 : (ℝ × (Qs × (LA × LW))) × Nn), x.1.1 ≠ 0 →
      Ph (normalChart X0 lA0 lW0 E Jc Hsh x.1.1 x.2 x.1.2) = 0 →
      normalChart X0 lA0 lW0 E Jc Hsh x.1.1 x.2 x.1.2 =
        normalChart X0 lA0 lW0 E Jc Hsh x.1.1 (nf x.1) x.1.2) ∧
    (∀ a, a ≠ 0 → Function.Bijective fun nw : Nn × (Qs × (LA × LW)) =>
      normalChart X0 lA0 lW0 E Jc Hsh a nw.1 nw.2) := by
  have hbij := fun a (ha : a ≠ 0) =>
    normalChart_bijective X0 lA0 lW0 E Jc Hsh Λ hΛE hΛJ C0 C hC0J hC0E hEonto ha
  refine ⟨?_, ?_, ?_, hbij⟩
  · filter_upwards [hsol] with y hy hy0
    exact (hdiv y.1 hy0 (nf y) y.2).2 hy
  · intro a ha w w' h
    have := (hbij a ha).1 (a₁ := (nf (a, w), w)) (a₂ := (nf (a, w'), w')) h
    exact (Prod.mk.inj this).2
  · filter_upwards [huniq] with x hx hx0 hPh
    have hP : P x = 0 := (hdiv x.1.1 hx0 x.2 x.1.2).1 hPh
    rw [(hx.1 hP)]

end Chart


/-! ### The assembled lemma -/

section Assembled

variable {Nn Qs LA LW Rows Xc Cons : Type*}
  [NormedAddCommGroup Nn] [NormedSpace ℝ Nn] [CompleteSpace Nn]
  [NormedAddCommGroup Qs] [NormedSpace ℝ Qs] [CompleteSpace Qs]
  [NormedAddCommGroup LA] [NormedSpace ℝ LA] [CompleteSpace LA]
  [NormedAddCommGroup LW] [NormedSpace ℝ LW] [CompleteSpace LW]
  [NormedAddCommGroup Rows] [NormedSpace ℝ Rows] [CompleteSpace Rows]
  [NormedAddCommGroup Xc] [NormedSpace ℝ Xc] [CompleteSpace Xc] [Zero Cons]

/-- **`lem:supp-exact-normal-coordinates`** (assembled).  Under the amplitude-graded chart
hypotheses (C1)–(C2) there is an analytic normal solve `n(a, w)` such that `P_h(Θ_a(w)) = 0` for
`a ≠ 0` near `0`, with `n(a, 0) = 0`, `‖n‖ ≤ K(|a|‖q‖ + a²‖p‖)`, `D_q n = O(a)`,
`D_p n = O(a²)`, `D_q𝒳 = O(a²)`, `D_p𝒳 = O(a⁴)`, `D_q²𝒳 = O(a³)`, `D_qD_p𝒳 = O(a⁴)`,
`D_p²𝒳 = O(a⁴)`, and `w ↦ Θ_a(w)` is a coordinate chart on the constraint solutions near the
prepared record (injective; every nearby solution `Θ(a, n, w)` is `Θ_a(w)`; `Θ(a, ·, ·)` is a
bijection). -/
theorem supp_exact_normal_coordinates (P : (ℝ × (Qs × (LA × LW))) × Nn → Rows)
    (hP : AnalyticAt ℝ P 0) (hPzero : ∀ᶠ a in 𝓝 (0 : ℝ), P ((a, 0), 0) = 0)
    (C : Nn ≃L[ℝ] Rows) (hPlin : ∀ w n, P ((0, w), n) = C n)
    (Pq : (ℝ × (Qs × (LA × LW))) × Nn → (Qs →L[ℝ] Rows)) (hPq : AnalyticAt ℝ Pq 0)
    (hdq : ∀ᶠ x in 𝓝 (0 : (ℝ × (Qs × (LA × LW))) × Nn),
      fderiv ℝ P x ∘L (ContinuousLinearMap.inl ℝ _ Nn ∘L iotaQ Qs LA LW) = x.1.1 • Pq x)
    (Pp : (ℝ × (Qs × (LA × LW))) × Nn → ((LA × LW) →L[ℝ] Rows)) (hPp : AnalyticAt ℝ Pp 0)
    (hdp : ∀ᶠ x in 𝓝 (0 : (ℝ × (Qs × (LA × LW))) × Nn),
      fderiv ℝ P x ∘L (ContinuousLinearMap.inl ℝ _ Nn ∘L iotaP Qs LA LW) =
        x.1.1 ^ 2 • Pp x)
    (X0 : ℝ → Xc) (hX0 : AnalyticAt ℝ X0 0) (lA0 : ℝ → LA) (lW0 : ℝ → LW)
    (E : Qs →L[ℝ] Xc) (Jc : Nn →L[ℝ] Xc) (Hsh : LW →L[ℝ] LA) (Λ : Xc →L[ℝ] Qs)
    (hΛE : ∀ q, Λ (E q) = q) (hΛJ : ∀ n, Λ (Jc n) = 0) (C0 : Xc →L[ℝ] Rows)
    (hC0J : ∀ n, C0 (Jc n) = C n) (hC0E : ∀ q, C0 (E q) = 0)
    (hEonto : ∀ v, C0 v = 0 → ∃ q, E q = v) (Ph : Xc × (LA × LW) → Cons)
    (hdiv : ∀ a, a ≠ 0 → ∀ n w, Ph (normalChart X0 lA0 lW0 E Jc Hsh a n w) = 0 ↔
      P ((a, w), n) = 0) :
    ∃ nf : ℝ × (Qs × (LA × LW)) → Nn, AnalyticAt ℝ nf 0 ∧ nf 0 = 0 ∧
      (∀ᶠ y in 𝓝 (0 : ℝ × (Qs × (LA × LW))), y.1 ≠ 0 →
        Ph (normalChart X0 lA0 lW0 E Jc Hsh y.1 (nf y) y.2) = 0) ∧
      (∀ᶠ a in 𝓝 (0 : ℝ), nf (a, 0) = 0) ∧
      (∃ K, ∀ᶠ y in 𝓝 (0 : ℝ × (Qs × (LA × LW))),
        ‖nf y‖ ≤ K * (|y.1| * ‖y.2.1‖ + y.1 ^ 2 * ‖y.2.2‖) ∧
        ‖fderiv ℝ nf y ∘L iotaQ Qs LA LW‖ ≤ K * |y.1| ∧
        ‖fderiv ℝ nf y ∘L iotaP Qs LA LW‖ ≤ K * y.1 ^ 2 ∧
        ‖fderiv ℝ (canonicalComponent X0 E Jc nf) y ∘L iotaQ Qs LA LW‖ ≤ K * y.1 ^ 2 ∧
        ‖fderiv ℝ (canonicalComponent X0 E Jc nf) y ∘L iotaP Qs LA LW‖ ≤ K * y.1 ^ 4 ∧
        ‖fderiv ℝ (fun z => fderiv ℝ (canonicalComponent X0 E Jc nf) z ∘L
          iotaQ Qs LA LW) y ∘L iotaQ Qs LA LW‖ ≤ K * |y.1| ^ 3 ∧
        ‖fderiv ℝ (fun z => fderiv ℝ (canonicalComponent X0 E Jc nf) z ∘L
          iotaP Qs LA LW) y ∘L iotaQ Qs LA LW‖ ≤ K * y.1 ^ 4 ∧
        ‖fderiv ℝ (fun z => fderiv ℝ (canonicalComponent X0 E Jc nf) z ∘L
          iotaP Qs LA LW) y ∘L iotaP Qs LA LW‖ ≤ K * y.1 ^ 4) ∧
      (∀ a, a ≠ 0 → ∀ w w', normalChart X0 lA0 lW0 E Jc Hsh a (nf (a, w)) w =
        normalChart X0 lA0 lW0 E Jc Hsh a (nf (a, w')) w' → w = w') ∧
      (∀ᶠ x in 𝓝 (0 : (ℝ × (Qs × (LA × LW))) × Nn), x.1.1 ≠ 0 →
        Ph (normalChart X0 lA0 lW0 E Jc Hsh x.1.1 x.2 x.1.2) = 0 →
        normalChart X0 lA0 lW0 E Jc Hsh x.1.1 x.2 x.1.2 =
          normalChart X0 lA0 lW0 E Jc Hsh x.1.1 (nf x.1) x.1.2) ∧
      (∀ a, a ≠ 0 → Function.Bijective fun nw : Nn × (Qs × (LA × LW)) =>
        normalChart X0 lA0 lW0 E Jc Hsh a nw.1 nw.2) := by
  obtain ⟨nf, hnf, hnf0, hsol, huniq, hzero, hbounds⟩ :=
    exact_normal_coordinates P hP hPzero C hPlin Pq hPq hdq Pp hPp hdp X0 hX0 E Jc
  obtain ⟨h1, h2, h3, h4⟩ := exact_normal_chart X0 lA0 lW0 E Jc Hsh Λ hΛE hΛJ C0 C hC0J hC0E
    hEonto P Ph hdiv nf hsol huniq
  exact ⟨nf, hnf, hnf0, h1, hzero, hbounds, h2, h3, h4⟩

end Assembled

/-! ### Non-vacuity -/

/-- The (C2) hypothesis packet is satisfiable: the linear divided map
`𝒫((a, w), n) = n` (with `𝒫_q = 𝒫_p = 0`) meets every hypothesis of
`exact_normal_coordinates`. -/
example :
    let P : (ℝ × (ℝ × (ℝ × ℝ))) × ℝ → ℝ := fun x => x.2
    AnalyticAt ℝ P 0 ∧ (∀ᶠ a in 𝓝 (0 : ℝ), P ((a, 0), 0) = 0) ∧
      (∀ w n, P ((0, w), n) = (ContinuousLinearEquiv.refl ℝ ℝ) n) ∧
      (∀ᶠ x in 𝓝 (0 : (ℝ × (ℝ × (ℝ × ℝ))) × ℝ),
        fderiv ℝ P x ∘L (ContinuousLinearMap.inl ℝ _ ℝ ∘L iotaQ ℝ ℝ ℝ) =
          x.1.1 • (0 : ℝ →L[ℝ] ℝ)) ∧
      (∀ᶠ x in 𝓝 (0 : (ℝ × (ℝ × (ℝ × ℝ))) × ℝ),
        fderiv ℝ P x ∘L (ContinuousLinearMap.inl ℝ _ ℝ ∘L iotaP ℝ ℝ ℝ) =
          x.1.1 ^ 2 • (0 : (ℝ × ℝ) →L[ℝ] ℝ)) := by
  intro P
  have hd : ∀ x, fderiv ℝ P x = ContinuousLinearMap.snd ℝ _ ℝ := fun x =>
    (ContinuousLinearMap.snd ℝ (ℝ × (ℝ × (ℝ × ℝ))) ℝ).fderiv
  refine ⟨analyticAt_snd, Eventually.of_forall fun _ => rfl, fun _ _ => rfl,
    Eventually.of_forall fun x => ?_, Eventually.of_forall fun x => ?_⟩
  · rw [hd, smul_zero]; ext v; simp
  · rw [hd, smul_zero]; ext v <;> simp

end ExactNormalCoordinates

end RenewalGeometry
