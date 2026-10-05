/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.Renewal.LocalizedRenewalFaceLinearizationExact
/-!
# Face linearization with boundedness only near zero (`thm:supp-face-linearization`)

Emergent-spacetime manuscript, `thm:supp-face-linearization`.

* `renewal_face_linearization_boundedNear` (exact branch, as stated): `U` a
  neighbourhood of zero closed under halving (e.g. balanced), `A z = 2 A(z/2)` on `U`,
  `A` bounded on `U ∩ V` for some neighbourhood `V` of zero, and the quadratic
  additivity defect bound `|A(x+y) − A x − A y| ≤ H ‖x‖ ‖y‖` for `x, y, x + y` in
  `U ∩ W` with `W` a neighbourhood of zero.  Then `A` agrees on `U` with a unique
  continuous real-linear functional.  The proof applies the localized theorem
  `LocalizedRenewalFaceLinearizationExact.localized_renewal_face_linearization` on
  `U' = U ∩ B(0, δ)` and extends the agreement to all of `U` by the dyadic identity
  `A z = 2ⁿ A(2⁻ⁿ z)`.
* `renewal_face_linearization_balanced`: the manuscript's form (`U` balanced convex
  neighbourhood of zero, `A 0 = 0`), with uniqueness among *all* real-linear
  functionals (not only continuous ones).
* Stable branch: `stable_branch_needs_regularity` shows that the stable branch as
  printed (summable adjacent defects and vanishing additivity defect only) is FALSE:
  a ℚ-linear coordinate functional `c : ℝ → ℝ` of a Hamel basis gives renormalized
  scores `L_m(z) = 2^m c(2^{-m} z) = c(z)` with zero adjacent-cutoff and zero
  additivity defects, but no real-linear functional is their pointwise limit.  The
  corrected statement (one score `L_{m₀}` continuous at zero) is
  `RenewalGeometry.stable_renewal_face_linearization`.
-/

open Filter
open scoped Topology

namespace RenewalGeometry
namespace FaceLinearizationBoundedNear

/-- Dyadic identity `A z = 2ⁿ A(2⁻ⁿ z)` on a halving-closed set. -/
theorem dyadic_identity {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : Set E) (A : E → ℝ)
    (hhalf_mem : ∀ z ∈ U, (2 : ℝ)⁻¹ • z ∈ U)
    (hhalf : ∀ z ∈ U, A z = 2 * A ((2 : ℝ)⁻¹ • z)) :
    ∀ n : ℕ, ∀ z ∈ U, ((2 : ℝ)⁻¹ ^ n) • z ∈ U ∧
      A z = (2 : ℝ) ^ n * A (((2 : ℝ)⁻¹ ^ n) • z) := by
  intro n
  induction n with
  | zero => intro z hz; simp [hz]
  | succ n ih =>
    intro z hz
    obtain ⟨hmem, heq⟩ := ih z hz
    have hs : ((2 : ℝ)⁻¹ ^ (n + 1)) • z = (2 : ℝ)⁻¹ • (((2 : ℝ)⁻¹ ^ n) • z) := by
      rw [pow_succ, mul_comm, mul_smul]
    refine ⟨hs ▸ hhalf_mem _ hmem, ?_⟩
    rw [heq, hhalf _ hmem, ← hs, pow_succ]
    ring

/-- **`thm:supp-face-linearization`, exact branch, under the paper's hypotheses**:
boundedness of `A` is only required near zero (`A '' (U ∩ V)` bounded for a
neighbourhood `V` of `0`), and the quadratic additivity defect only near zero. -/
theorem renewal_face_linearization_boundedNear
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : Set E) (A : E → ℝ) (H : ℝ)
    (hU : U ∈ 𝓝 (0 : E))
    (hhalf_mem : ∀ z ∈ U, (2 : ℝ)⁻¹ • z ∈ U)
    (hhalf : ∀ z ∈ U, A z = 2 * A ((2 : ℝ)⁻¹ • z))
    (hbdd : ∃ V ∈ 𝓝 (0 : E), Bornology.IsBounded (A '' (U ∩ V)))
    (hquasi : ∃ W ∈ 𝓝 (0 : E), ∀ x y, x ∈ U ∩ W → y ∈ U ∩ W → x + y ∈ U ∩ W →
      |A (x + y) - A x - A y| ≤ H * ‖x‖ * ‖y‖) :
    ∃! ell : E →L[ℝ] ℝ, ∀ x ∈ U, ell x = A x := by
  obtain ⟨V, hV, hAV⟩ := hbdd
  obtain ⟨W, hW, hAW⟩ := hquasi
  obtain ⟨δ, hδ, hδV⟩ := Metric.mem_nhds_iff.mp hV
  obtain ⟨ρ, hρ, hρW⟩ := Metric.mem_nhds_iff.mp hW
  set U' : Set E := U ∩ Metric.ball 0 δ with hU'
  have hU'n : U' ∈ 𝓝 (0 : E) := Filter.inter_mem hU (Metric.ball_mem_nhds 0 hδ)
  have hq : ‖(2 : ℝ)⁻¹‖ ≤ 1 := by norm_num
  have hhalf_mem' : ∀ z ∈ U', (2 : ℝ)⁻¹ • z ∈ U' := by
    rintro z ⟨hzU, hzB⟩
    refine ⟨hhalf_mem z hzU, ?_⟩
    rw [Metric.mem_ball, dist_zero_right] at hzB ⊢
    rw [norm_smul]
    calc ‖(2 : ℝ)⁻¹‖ * ‖z‖ ≤ 1 * ‖z‖ := by gcongr
      _ < δ := by rw [one_mul]; exact hzB
  have hhalf' : ∀ z ∈ U', A z = 2 * A ((2 : ℝ)⁻¹ • z) := fun z hz => hhalf z hz.1
  have hρ2 : 0 < ρ / 2 := half_pos hρ
  have hinW : ∀ z : E, ‖z‖ ≤ ρ / 2 → z ∈ W := by
    intro z hz
    apply hρW
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  have hquasi' : ∀ x y, x ∈ U' → y ∈ U' → x + y ∈ U' →
      ‖x‖ ≤ ρ / 2 → ‖y‖ ≤ ρ / 2 → ‖x + y‖ ≤ ρ / 2 →
      |A (x + y) - A x - A y| ≤ H * ‖x‖ * ‖y‖ := by
    intro x y hx hy hxy hnx hny hnxy
    exact hAW x y ⟨hx.1, hinW x hnx⟩ ⟨hy.1, hinW y hny⟩ ⟨hxy.1, hinW _ hnxy⟩
  have hbounded' : Bornology.IsBounded (A '' U') := by
    refine hAV.subset (Set.image_mono ?_)
    rintro z ⟨hzU, hzB⟩
    exact ⟨hzU, hδV hzB⟩
  obtain ⟨ell, hell, huniq⟩ :=
    LocalizedRenewalFaceLinearizationExact.localized_renewal_face_linearization U' A (ρ / 2) H
      hU'n hhalf_mem' hhalf' hρ2 hquasi' hbounded'
  have hdy := dyadic_identity U A hhalf_mem hhalf
  refine ⟨ell, ?_, ?_⟩
  · intro x hx
    -- choose `n` with `2⁻ⁿ x ∈ B(0, δ)`
    have hs : Tendsto (fun n : ℕ => ((2 : ℝ)⁻¹ ^ n) • x) atTop (𝓝 0) := by
      have hpow : Tendsto (fun n : ℕ => (2 : ℝ)⁻¹ ^ n) atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
      simpa using hpow.smul_const x
    obtain ⟨n, hn⟩ := (hs.eventually (Metric.ball_mem_nhds (0 : E) hδ)).exists
    obtain ⟨hmem, heq⟩ := hdy n x hx
    have hx' : ((2 : ℝ)⁻¹ ^ n) • x ∈ U' := ⟨hmem, hn⟩
    have hrepr : x = (2 : ℝ) ^ n • (((2 : ℝ)⁻¹ ^ n) • x) := by
      rw [smul_smul, ← mul_pow, mul_inv_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_pow, one_smul]
    rw [heq, ← hell _ hx', hrepr, map_smul, smul_eq_mul, ← hrepr]
  · intro g hg
    exact huniq g (fun x hx => hg x hx.1)

/-- Two real-linear functionals agreeing on a neighbourhood of zero are equal. -/
theorem linearMap_eq_of_eqOn_nhds {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : Set E) (hU : U ∈ 𝓝 (0 : E)) (f g : E →ₗ[ℝ] ℝ) (hfg : ∀ x ∈ U, f x = g x) :
    f = g := by
  ext x
  have hs : Tendsto (fun n : ℕ => ((2 : ℝ)⁻¹ ^ n) • x) atTop (𝓝 0) := by
    have hpow : Tendsto (fun n : ℕ => (2 : ℝ)⁻¹ ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    simpa using hpow.smul_const x
  obtain ⟨n, hn⟩ := (hs.eventually hU).exists
  have h := hfg _ hn
  rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul] at h
  have hne : ((2 : ℝ)⁻¹ ^ n) ≠ 0 := pow_ne_zero _ (by norm_num)
  exact mul_left_cancel₀ hne h

/-- **`thm:supp-face-linearization`, exact branch, in the manuscript's form**: `U` a
balanced convex neighbourhood of zero, `A 0 = 0`, `A z = 2 A(z/2)` on `U`, `A` bounded
near zero and quasi-additive near zero.  Then `A` is the restriction to `U` of a unique
real-linear functional (unique among all linear functionals), which is moreover
continuous.  (Convexity and `A 0 = 0` are not needed for the argument.) -/
theorem renewal_face_linearization_balanced
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : Set E) (A : E → ℝ) (H : ℝ)
    (hU : U ∈ 𝓝 (0 : E)) (hbal : Balanced ℝ U) (_hconv : Convex ℝ U) (_hA0 : A 0 = 0)
    (hhalf : ∀ z ∈ U, A z = 2 * A ((2 : ℝ)⁻¹ • z))
    (hbdd : ∃ V ∈ 𝓝 (0 : E), Bornology.IsBounded (A '' (U ∩ V)))
    (hquasi : ∃ W ∈ 𝓝 (0 : E), ∀ x y, x ∈ U ∩ W → y ∈ U ∩ W → x + y ∈ U ∩ W →
      |A (x + y) - A x - A y| ≤ H * ‖x‖ * ‖y‖) :
    (∃! ell : E →ₗ[ℝ] ℝ, ∀ x ∈ U, ell x = A x) ∧
      ∃ ell : E →L[ℝ] ℝ, ∀ x ∈ U, ell x = A x := by
  have hhalf_mem : ∀ z ∈ U, (2 : ℝ)⁻¹ • z ∈ U :=
    fun z hz => hbal.smul_mem (by norm_num) hz
  obtain ⟨ell, hell, -⟩ :=
    renewal_face_linearization_boundedNear U A H hU hhalf_mem hhalf hbdd hquasi
  refine ⟨⟨ell.toLinearMap, hell, ?_⟩, ell, hell⟩
  intro g hg
  exact linearMap_eq_of_eqOn_nhds U hU g ell.toLinearMap
    (fun x hx => (hg x hx).trans (hell x hx).symm)

/-! ### The stable branch needs a regularity hypothesis -/

/-- A ℚ-linear, real-valued coordinate functional of a Hamel basis of `ℝ` over `ℚ`. -/
noncomputable def hamelCoord (i : Module.Basis.ofVectorSpaceIndex ℚ ℝ) (x : ℝ) : ℝ :=
  ((Module.Basis.ofVectorSpace ℚ ℝ).coord i x : ℝ)

theorem hamelCoord_add (i : Module.Basis.ofVectorSpaceIndex ℚ ℝ) (x y : ℝ) :
    hamelCoord i (x + y) = hamelCoord i x + hamelCoord i y := by
  simp [hamelCoord]

theorem hamelCoord_dyadic (i : Module.Basis.ofVectorSpaceIndex ℚ ℝ) (m : ℕ) (z : ℝ) :
    (2 : ℝ) ^ m * hamelCoord i ((2 : ℝ)⁻¹ ^ m * z) = hamelCoord i z := by
  have h : ((2 : ℝ)⁻¹ ^ m * z) = ((2 : ℚ)⁻¹ ^ m : ℚ) • z := by
    rw [Rat.smul_def]; push_cast; ring
  rw [hamelCoord, h, map_smul, smul_eq_mul, hamelCoord]
  push_cast
  rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ (by norm_num : (2 : ℝ) ≠ 0), one_pow, one_mul]

/-- No real-linear functional agrees with a Hamel coordinate functional. -/
theorem not_linear_hamelCoord (i : Module.Basis.ofVectorSpaceIndex ℚ ℝ) (ell : ℝ →ₗ[ℝ] ℝ)
    (h : ∀ z, ell z = hamelCoord i z) : False := by
  set b := Module.Basis.ofVectorSpace ℚ ℝ
  have hlin : ∀ z, ell z = z * ell 1 := by
    intro z
    rw [show z = z • (1 : ℝ) by simp, map_smul, smul_eq_mul, smul_eq_mul, mul_one]
  have hbi : ell (b i) = 1 := by
    rw [h, hamelCoord, Module.Basis.coord_apply, Module.Basis.repr_self]
    simp
  have h1 : ell 1 ≠ 0 := by
    intro h0
    rw [hlin, h0, mul_zero] at hbi
    exact zero_ne_one hbi
  have hv := h (Real.sqrt 2 / ell 1)
  rw [hlin, div_mul_cancel₀ _ h1, hamelCoord] at hv
  exact irrational_sqrt_two ⟨_, hv.symm⟩

/-- **The stable branch of `thm:supp-face-linearization` is false as printed.**  With
`A_m = c` a Hamel coordinate functional, the renormalized scores
`L_m(z) = 2^m A_m(2^{-m} z)` have zero adjacent-cutoff defect and zero additivity
defect (so every summability / vanishing hypothesis holds with `ε = η = 0`), yet no
real-linear functional, continuous or not, is their pointwise limit.  The regularity
hypothesis "one `L_{m₀}` continuous at zero" of
`RenewalGeometry.stable_renewal_face_linearization` is therefore necessary. -/
theorem stable_branch_needs_regularity :
    ∃ A : ℕ → ℝ → ℝ,
      let L : ℕ → ℝ → ℝ := fun m z => (2 : ℝ) ^ m * A m ((2 : ℝ)⁻¹ ^ m * z)
      (∀ m z, |L (m + 1) z - L m z| ≤ 0 * ‖z‖) ∧
      (∀ m x y, |L m (x + y) - L m x - L m y| ≤ 0 * ‖x‖ * ‖y‖) ∧
      (¬ ∃ ell : ℝ →ₗ[ℝ] ℝ, ∀ z, Tendsto (fun m => L m z) atTop (𝓝 (ell z))) ∧
      (¬ ∃ ell : ℝ →L[ℝ] ℝ, ∀ z, Tendsto (fun m => L m z) atTop (𝓝 (ell z))) := by
  obtain ⟨i⟩ := (Module.Basis.ofVectorSpace ℚ ℝ).index_nonempty
  refine ⟨fun _ => hamelCoord i, ?_⟩
  intro L
  have hL : ∀ m z, L m z = hamelCoord i z := fun m z => hamelCoord_dyadic i m z
  have hnolin : ¬ ∃ ell : ℝ →ₗ[ℝ] ℝ, ∀ z, Tendsto (fun m => L m z) atTop (𝓝 (ell z)) := by
    rintro ⟨ell, hell⟩
    refine not_linear_hamelCoord i ell (fun z => ?_)
    have h := hell z
    simp only [hL] at h
    exact tendsto_nhds_unique h tendsto_const_nhds
  refine ⟨fun m z => by simp [hL], fun m x y => by simp [hL, hamelCoord_add], hnolin, ?_⟩
  rintro ⟨ell, hell⟩
  exact hnolin ⟨ell.toLinearMap, hell⟩

/-- Non-vacuity of the exact branch: `A = 3·id` on the balanced convex neighbourhood
`U = [-1, 1]` (any bound near zero, `H = 0`). -/
example : (∃! ell : ℝ →ₗ[ℝ] ℝ, ∀ x ∈ Metric.closedBall (0 : ℝ) 1, ell x = 3 * x) ∧
    ∃ ell : ℝ →L[ℝ] ℝ, ∀ x ∈ Metric.closedBall (0 : ℝ) 1, ell x = 3 * x := by
  refine renewal_face_linearization_balanced (Metric.closedBall (0 : ℝ) 1) (fun x => 3 * x) 0
    (Metric.closedBall_mem_nhds 0 one_pos) (balanced_closedBall_zero)
    (convex_closedBall 0 1) (by simp) (fun z _ => by ring) ?_ ?_
  · refine ⟨Metric.closedBall 0 1, Metric.closedBall_mem_nhds 0 one_pos, ?_⟩
    refine (Metric.isBounded_closedBall (x := (0 : ℝ)) (r := 3)).subset ?_
    rintro _ ⟨x, ⟨hx, -⟩, rfl⟩
    simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at hx ⊢
    rw [abs_mul]; norm_num; linarith
  · exact ⟨Set.univ, Filter.univ_mem, fun x y _ _ _ => by simp; ring⟩

end FaceLinearizationBoundedNear
end RenewalGeometry
