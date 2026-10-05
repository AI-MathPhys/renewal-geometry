/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.AnalyticImplicitFunction

/-!
# Stationary-connection solve: contraction, analyticity and cubic remainders

This file collects the reusable analysis behind the stationary-connection solve of the
emergent-spacetime manuscript (`eq:supp-exact-stationary-connection`):
`γ(A) = f + C A + N(A) = 0`, with `C` invertible (least singular value `c_*`) and `N` Lipschitz
with a small constant on the `R`-ball.  This is "a contraction after multiplication by `C⁻¹`",
with "analytic dependence from the finite-dimensional implicit function theorem".

## Main results

* `exists_unique_zero_of_contraction`: if `‖C⁻¹‖ ≤ K`, `N` is `L`-Lipschitz on the closed
  `R`-ball, `K L ≤ 1/2` and `K (‖f‖ + ‖N 0‖) ≤ R / 2`, then `f + C A + N A = 0` has a unique
  solution in the closed `R`-ball; `norm_le_of_zero_of_contraction` bounds it by
  `2 K (‖f‖ + ‖N 0‖)`.
* `exists_unique_zero_of_lower_bound`, `norm_le_of_zero_of_lower_bound`: the same with the
  least-singular-value hypothesis `c ‖x‖ ≤ ‖C x‖` in finite dimension.
* `analyticAt_of_unique_zero`: a locally unique zero of an analytic equation with invertible
  partial derivative depends analytically on the parameter;
  `analyticOnNhd_of_unique_zero_closedBall` is the version over an open parameter set.
* `cubic_remainder_apply_zero`, `cubic_remainder_fderiv_zero`,
  `cubic_remainder_fderiv_fderiv_zero`, `cubic_remainder_fderiv_lipschitz`: a `C³` map with
  `‖ρ Y‖ ≤ K ‖Y‖³` has vanishing `2`-jet at `0`, hence a derivative which is
  `K' r`-Lipschitz on the `r`-ball and bounded by `K' ‖Y‖²`.
* `fderiv_scaled`, `norm_fderiv_scaled_sub_le`: the rescaled remainder
  `ρ_h A = h⁻² ρ (h A)` has `(K' h R)`-Lipschitz derivative on the `R`-ball.
* `norm_fderiv_bilinear_sub_le`: uniformity in a coefficient entering bilinearly.
-/

open Filter Metric Asymptotics
open scoped Topology

namespace RenewalGeometry

namespace StationaryContraction

/-! ### The contraction step -/

section Contraction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The zero equation `f + C A + N A = 0` is the fixed-point equation of
`A ↦ -C⁻¹ (f + N A)`. -/
theorem eq_zero_iff_fixed {C Cinv : E →L[ℝ] E} (hCinvC : ∀ x, Cinv (C x) = x)
    (hCCinv : ∀ y, C (Cinv y) = y) (f : E) (Nl : E → E) (A : E) :
    f + C A + Nl A = 0 ↔ -Cinv (f + Nl A) = A := by
  constructor
  · intro h
    have h' : f + Nl A = -C A := by
      rw [eq_neg_iff_add_eq_zero, ← h]
      abel
    rw [h', map_neg, neg_neg, hCinvC]
  · intro h
    have h' : C A = -(f + Nl A) := by
      conv_lhs => rw [← h]
      rw [map_neg, hCCinv]
    rw [h']
    abel

/-- **A priori bound for the stationary solve.**  Any solution `A` of `f + C A + N A = 0` in the
closed `R`-ball, with `‖C⁻¹‖ ≤ K`, `N` `L`-Lipschitz on the ball and `K L ≤ 1/2`, satisfies
`‖A‖ ≤ 2 K (‖f‖ + ‖N 0‖)`. -/
theorem norm_le_of_zero_of_contraction {C Cinv : E →L[ℝ] E} (hCinvC : ∀ x, Cinv (C x) = x)
    (hCCinv : ∀ y, C (Cinv y) = y) {f : E} {Nl : E → E} {R K L : ℝ} (hK : ‖Cinv‖ ≤ K)
    (hL : ∀ x ∈ closedBall (0 : E) R, ∀ y ∈ closedBall (0 : E) R,
      ‖Nl x - Nl y‖ ≤ L * ‖x - y‖)
    (hKL : K * L ≤ 1 / 2) {A : E} (hA : A ∈ closedBall (0 : E) R)
    (hzero : f + C A + Nl A = 0) :
    ‖A‖ ≤ 2 * K * (‖f‖ + ‖Nl 0‖) := by
  have hK0 : 0 ≤ K := (norm_nonneg _).trans hK
  have hfix := (eq_zero_iff_fixed hCinvC hCCinv f Nl A).1 hzero
  have hR : 0 ≤ R := (norm_nonneg A).trans (mem_closedBall_zero_iff.1 hA)
  have h0 : (0 : E) ∈ closedBall (0 : E) R := mem_closedBall_self hR
  have hNA : ‖Nl A‖ ≤ ‖Nl 0‖ + L * ‖A‖ := by
    have := hL A hA 0 h0
    rw [sub_zero] at this
    calc ‖Nl A‖ = ‖Nl 0 + (Nl A - Nl 0)‖ := by rw [add_sub_cancel]
      _ ≤ ‖Nl 0‖ + ‖Nl A - Nl 0‖ := norm_add_le _ _
      _ ≤ ‖Nl 0‖ + L * ‖A‖ := by linarith
  have h1 : ‖A‖ ≤ K * (‖f‖ + ‖Nl 0‖) + (K * L) * ‖A‖ := by
    calc ‖A‖ = ‖Cinv (f + Nl A)‖ := by conv_lhs => rw [← hfix, norm_neg]
      _ ≤ K * ‖f + Nl A‖ := Cinv.le_of_opNorm_le hK _
      _ ≤ K * (‖f‖ + (‖Nl 0‖ + L * ‖A‖)) :=
          mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (by linarith)) hK0
      _ = K * (‖f‖ + ‖Nl 0‖) + (K * L) * ‖A‖ := by ring
  have h2 : (K * L) * ‖A‖ ≤ 1 / 2 * ‖A‖ := mul_le_mul_of_nonneg_right hKL (norm_nonneg _)
  linarith

/-- **Existence and uniqueness for the stationary solve (contraction after `C⁻¹`).**  Let `E` be
complete, `C` invertible with inverse `Cinv`, `‖Cinv‖ ≤ K`, `N` `L`-Lipschitz on the closed
`R`-ball, `K L ≤ 1/2` and `K (‖f‖ + ‖N 0‖) ≤ R / 2`.  Then `f + C A + N A = 0` has a unique
solution `A` in the closed `R`-ball. -/
theorem exists_unique_zero_of_contraction [CompleteSpace E] {C Cinv : E →L[ℝ] E}
    (hCinvC : ∀ x, Cinv (C x) = x) (hCCinv : ∀ y, C (Cinv y) = y) (f : E) (Nl : E → E)
    {R K L : ℝ} (hK : ‖Cinv‖ ≤ K)
    (hL : ∀ x ∈ closedBall (0 : E) R, ∀ y ∈ closedBall (0 : E) R,
      ‖Nl x - Nl y‖ ≤ L * ‖x - y‖)
    (hKL : K * L ≤ 1 / 2) (hKR : K * (‖f‖ + ‖Nl 0‖) ≤ R / 2) :
    ∃! A, A ∈ closedBall (0 : E) R ∧ f + C A + Nl A = 0 := by
  have hK0 : 0 ≤ K := (norm_nonneg _).trans hK
  have hR : 0 ≤ R := by
    have : 0 ≤ K * (‖f‖ + ‖Nl 0‖) := mul_nonneg hK0 (by positivity)
    linarith
  set T : E → E := fun A => -Cinv (f + Nl A) with hT
  have h0 : (0 : E) ∈ closedBall (0 : E) R := mem_closedBall_self hR
  -- the contraction estimate
  have hcontr : ∀ x ∈ closedBall (0 : E) R, ∀ y ∈ closedBall (0 : E) R,
      ‖T x - T y‖ ≤ 1 / 2 * ‖x - y‖ := by
    intro x hx y hy
    have : T x - T y = Cinv (Nl y - Nl x) := by
      simp only [hT, map_sub, map_add]
      abel
    rw [this]
    calc ‖Cinv (Nl y - Nl x)‖ ≤ K * ‖Nl y - Nl x‖ := Cinv.le_of_opNorm_le hK _
      _ ≤ K * (L * ‖y - x‖) := mul_le_mul_of_nonneg_left (hL y hy x hx) hK0
      _ = (K * L) * ‖x - y‖ := by rw [norm_sub_rev]; ring
      _ ≤ 1 / 2 * ‖x - y‖ := mul_le_mul_of_nonneg_right hKL (norm_nonneg _)
  -- the ball is mapped into itself
  have hmaps : ∀ x ∈ closedBall (0 : E) R, T x ∈ closedBall (0 : E) R := by
    intro x hx
    rw [mem_closedBall_zero_iff] at hx ⊢
    have hT0 : ‖T 0‖ ≤ R / 2 := by
      calc ‖T 0‖ = ‖Cinv (f + Nl 0)‖ := by rw [hT, norm_neg]
        _ ≤ K * ‖f + Nl 0‖ := Cinv.le_of_opNorm_le hK _
        _ ≤ K * (‖f‖ + ‖Nl 0‖) := mul_le_mul_of_nonneg_left (norm_add_le _ _) hK0
        _ ≤ R / 2 := hKR
    have h1 := hcontr x (mem_closedBall_zero_iff.2 hx) 0 h0
    rw [sub_zero] at h1
    calc ‖T x‖ = ‖T 0 + (T x - T 0)‖ := by rw [add_sub_cancel]
      _ ≤ ‖T 0‖ + ‖T x - T 0‖ := norm_add_le _ _
      _ ≤ R / 2 + 1 / 2 * ‖x‖ := add_le_add hT0 h1
      _ ≤ R := by linarith
  -- Banach fixed point on the closed ball
  have : CompleteSpace (closedBall (0 : E) R) := isClosed_closedBall.completeSpace_coe
  have : Nonempty (closedBall (0 : E) R) := ⟨⟨0, h0⟩⟩
  let g : closedBall (0 : E) R → closedBall (0 : E) R := fun x => ⟨T x, hmaps x x.2⟩
  have hg : ContractingWith (1 / 2 : NNReal) g := by
    refine ⟨by norm_num, ?_⟩
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm, dist_eq_norm]
    simpa using hcontr x x.2 y y.2
  set A := ContractingWith.fixedPoint g hg
  have hA : T A = A := congrArg Subtype.val (ContractingWith.fixedPoint_isFixedPt (f := g) hg)
  refine ⟨A, ⟨A.2, (eq_zero_iff_fixed hCinvC hCCinv f Nl A).2 hA⟩, ?_⟩
  rintro B ⟨hB, hBzero⟩
  have hTB : T B = B := (eq_zero_iff_fixed hCinvC hCCinv f Nl B).1 hBzero
  have h := hcontr B hB A A.2
  rw [hTB, hA] at h
  have : ‖B - A‖ = 0 := le_antisymm (by linarith [norm_nonneg (B - A)]) (norm_nonneg _)
  exact sub_eq_zero.1 (norm_eq_zero.1 this)

/-- **Inverse from a least-singular-value bound.**  In finite dimension, a linear endomorphism
with `c ‖x‖ ≤ ‖C x‖` (`c > 0`) is invertible, with `‖C⁻¹‖ ≤ c⁻¹`. -/
theorem exists_inverse_of_lower_bound [FiniteDimensional ℝ E] {C : E →L[ℝ] E} {c : ℝ}
    (hc : 0 < c) (hC : ∀ x, c * ‖x‖ ≤ ‖C x‖) :
    ∃ Cinv : E →L[ℝ] E, (∀ x, Cinv (C x) = x) ∧ (∀ y, C (Cinv y) = y) ∧ ‖Cinv‖ ≤ c⁻¹ := by
  have hinj : Function.Injective (C : E →ₗ[ℝ] E) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h1 := hC x
    have hx' : C x = 0 := hx
    rw [hx', norm_zero] at h1
    have : ‖x‖ ≤ 0 := by nlinarith [norm_nonneg x]
    exact norm_le_zero_iff.1 this
  have hsurj : Function.Surjective (C : E →ₗ[ℝ] E) := LinearMap.injective_iff_surjective.1 hinj
  set e := LinearEquiv.ofBijective (C : E →ₗ[ℝ] E) ⟨hinj, hsurj⟩
  have he : ∀ x, e x = C x := fun x => rfl
  refine ⟨LinearMap.toContinuousLinearMap (e.symm : E →ₗ[ℝ] E), ?_, ?_, ?_⟩
  · intro x
    simp only [LinearMap.coe_toContinuousLinearMap', LinearEquiv.coe_coe]
    rw [← he, LinearEquiv.symm_apply_apply]
  · intro y
    simp only [LinearMap.coe_toContinuousLinearMap', LinearEquiv.coe_coe]
    rw [← he, LinearEquiv.apply_symm_apply]
  · refine ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.2 hc.le) fun y => ?_
    simp only [LinearMap.coe_toContinuousLinearMap', LinearEquiv.coe_coe]
    have h1 := hC (e.symm y)
    rw [← he, LinearEquiv.apply_symm_apply] at h1
    rw [le_inv_mul_iff₀ hc]
    exact h1

/-- **Stationary solve under a least-singular-value bound.**  In finite dimension, if
`c ‖x‖ ≤ ‖C x‖` with `c > 0`, `N` is `L`-Lipschitz on the closed `R`-ball, `c⁻¹ L ≤ 1/2` and
`c⁻¹ (‖f‖ + ‖N 0‖) ≤ R / 2`, then `f + C A + N A = 0` has a unique solution in the closed
`R`-ball. -/
theorem exists_unique_zero_of_lower_bound [FiniteDimensional ℝ E] {C : E →L[ℝ] E} {c : ℝ}
    (hc : 0 < c) (hC : ∀ x, c * ‖x‖ ≤ ‖C x‖) (f : E) (Nl : E → E) {R L : ℝ}
    (hL : ∀ x ∈ closedBall (0 : E) R, ∀ y ∈ closedBall (0 : E) R,
      ‖Nl x - Nl y‖ ≤ L * ‖x - y‖)
    (hKL : c⁻¹ * L ≤ 1 / 2) (hKR : c⁻¹ * (‖f‖ + ‖Nl 0‖) ≤ R / 2) :
    ∃! A, A ∈ closedBall (0 : E) R ∧ f + C A + Nl A = 0 := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨Cinv, h1, h2, h3⟩ := exists_inverse_of_lower_bound hc hC
  exact exists_unique_zero_of_contraction h1 h2 f Nl h3 hL hKL hKR

/-- **A priori bound under a least-singular-value bound.**  A solution in the closed `R`-ball
satisfies `‖A‖ ≤ 2 c⁻¹ (‖f‖ + ‖N 0‖)`. -/
theorem norm_le_of_zero_of_lower_bound [FiniteDimensional ℝ E] {C : E →L[ℝ] E} {c : ℝ}
    (hc : 0 < c) (hC : ∀ x, c * ‖x‖ ≤ ‖C x‖) {f : E} {Nl : E → E} {R L : ℝ}
    (hL : ∀ x ∈ closedBall (0 : E) R, ∀ y ∈ closedBall (0 : E) R,
      ‖Nl x - Nl y‖ ≤ L * ‖x - y‖)
    (hKL : c⁻¹ * L ≤ 1 / 2) {A : E} (hA : A ∈ closedBall (0 : E) R)
    (hzero : f + C A + Nl A = 0) :
    ‖A‖ ≤ 2 * c⁻¹ * (‖f‖ + ‖Nl 0‖) := by
  obtain ⟨Cinv, h1, h2, h3⟩ := exists_inverse_of_lower_bound hc hC
  exact norm_le_of_zero_of_contraction h1 h2 h3 hL hKL hA hzero

end Contraction

/-! ### Analytic dependence on parameters -/

section Analytic

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- **Analyticity of a locally unique zero.**  Let `F : P × E → G` be analytic at `(p₀, a₀)`
with `F (p₀, a₀) = 0` and invertible partial derivative in `E`.  If `s : P → E` is such that,
for `p` near `p₀`, every zero `a ∈ S` of `F (p, ·)` (with `S` a neighbourhood of `a₀`) equals
`s p`, then `s` is analytic at `p₀`.  (No continuity of `s` is assumed; `s p₀ = a₀` and
`F (p, s p) = 0` near `p₀` follow.) -/
theorem analyticAt_of_unique_zero {F : P × E → G} {p₀ : P} {a₀ : E}
    (hF : AnalyticAt ℝ F (p₀, a₀)) (hF0 : F (p₀, a₀) = 0)
    (hinv : (fderiv ℝ F (p₀, a₀) ∘L .inr ℝ P E).IsInvertible) {s : P → E} {S : Set E}
    (hS : S ∈ 𝓝 a₀) (huniq : ∀ᶠ p in 𝓝 p₀, ∀ a ∈ S, F (p, a) = 0 → a = s p) :
    AnalyticAt ℝ s p₀ := by
  obtain ⟨ψ, hψ0, hψan, hψeq, -, -⟩ := AnalyticImplicit.analytic_implicit_function hF hinv
  have hS' : S ∈ 𝓝 (ψ p₀) := by simpa [hψ0] using hS
  have hcont : ∀ᶠ p in 𝓝 p₀, ψ p ∈ S := hψan.continuousAt.preimage_mem_nhds hS'
  have hψs : ψ =ᶠ[𝓝 p₀] s := by
    filter_upwards [hcont, hψeq, huniq] with p h1 h2 h3
    exact h3 _ h1 (by simpa [hF0] using h2)
  exact hψan.congr hψs

/-- **Analytic dependence of the stationary solution on an open parameter set.**  Let `U ⊆ P`
be open and, for `p ∈ U`, let `s p` be a zero of `F (p, ·)` lying in the open `R`-ball which is
the unique zero in the closed `R`-ball; assume `F` analytic and `∂_E F` invertible at each
`(p, s p)`.  Then `s` is analytic on a neighbourhood of every point of `U`. -/
theorem analyticOnNhd_of_unique_zero_closedBall {F : P × E → G} {s : P → E} {U : Set P}
    (hU : IsOpen U) {R : ℝ} (hF : ∀ p ∈ U, AnalyticAt ℝ F (p, s p))
    (hs : ∀ p ∈ U, s p ∈ ball (0 : E) R) (hzero : ∀ p ∈ U, F (p, s p) = 0)
    (huniq : ∀ p ∈ U, ∀ a ∈ closedBall (0 : E) R, F (p, a) = 0 → a = s p)
    (hinv : ∀ p ∈ U, (fderiv ℝ F (p, s p) ∘L .inr ℝ P E).IsInvertible) :
    AnalyticOnNhd ℝ s U := by
  intro p₀ hp₀
  refine analyticAt_of_unique_zero (hF p₀ hp₀) (hzero p₀ hp₀) (hinv p₀ hp₀)
    (isOpen_ball.mem_nhds (hs p₀ hp₀)) ?_
  filter_upwards [hU.mem_nhds hp₀] with p hp a ha hFa
  exact huniq p hp a (ball_subset_closedBall ha) hFa

end Analytic

/-! ### Cubic remainders -/

section Cubic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- A cubic bound forces `ρ 0 = 0`. -/
theorem cubic_remainder_apply_zero {ρ : E → F} {r₁ K : ℝ} (hr₁ : 0 < r₁)
    (hK : ∀ Y ∈ ball (0 : E) r₁, ‖ρ Y‖ ≤ K * ‖Y‖ ^ 3) : ρ 0 = 0 := by
  have := hK 0 (mem_ball_self hr₁)
  simpa using this

omit [NormedSpace ℝ F] in
/-- A cubic bound forces `ρ (t • y) = o(t ^ 2)` along every ray. -/
theorem cubic_remainder_isLittleO_sq {ρ : E → F} {r₁ K : ℝ} (hr₁ : 0 < r₁)
    (hK : ∀ Y ∈ ball (0 : E) r₁, ‖ρ Y‖ ≤ K * ‖Y‖ ^ 3) (y : E) :
    (fun t : ℝ => ρ (t • y)) =o[𝓝 0] fun t => t ^ 2 := by
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), t • y ∈ ball (0 : E) r₁ := by
    have ht : Tendsto (fun t : ℝ => t • y) (𝓝 0) (𝓝 0) := by
      simpa using (tendsto_id (x := 𝓝 (0 : ℝ))).smul_const y
    exact ht.eventually (isOpen_ball.mem_nhds (mem_ball_self hr₁))
  have hO : (fun t : ℝ => ρ (t • y)) =O[𝓝 0] fun t => t ^ 3 := by
    refine IsBigO.of_bound (K * ‖y‖ ^ 3) ?_
    filter_upwards [hev] with t ht
    calc ‖ρ (t • y)‖ ≤ K * ‖t • y‖ ^ 3 := hK _ ht
      _ = K * ‖y‖ ^ 3 * ‖t ^ 3‖ := by rw [norm_smul, norm_pow]; ring
  exact hO.trans_isLittleO (isLittleO_pow_pow (by norm_num))

/-- A cubic bound forces `fderiv ℝ ρ 0 = 0` (indeed `ρ` has derivative `0` at `0`). -/
theorem cubic_remainder_hasFDerivAt_zero {ρ : E → F} {r₁ K : ℝ} (hr₁ : 0 < r₁)
    (hK : ∀ Y ∈ ball (0 : E) r₁, ‖ρ Y‖ ≤ K * ‖Y‖ ^ 3) :
    HasFDerivAt ρ (0 : E →L[ℝ] F) 0 := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  have h0 := cubic_remainder_apply_zero hr₁ hK
  simp only [zero_add, h0, sub_zero, zero_apply]
  have hO : (fun Y : E => ρ Y) =O[𝓝 0] fun Y => ‖Y‖ ^ 3 := by
    refine IsBigO.of_bound K ?_
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr₁)] with Y hY
    calc ‖ρ Y‖ ≤ K * ‖Y‖ ^ 3 := hK Y hY
      _ = K * ‖‖Y‖ ^ 3‖ := by rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact hO.trans_isLittleO (isLittleO_norm_pow_id (by norm_num))

/-- A cubic bound forces `fderiv ℝ ρ 0 = 0`. -/
theorem cubic_remainder_fderiv_zero {ρ : E → F} {r₁ K : ℝ} (hr₁ : 0 < r₁)
    (hK : ∀ Y ∈ ball (0 : E) r₁, ‖ρ Y‖ ≤ K * ‖Y‖ ^ 3) : fderiv ℝ ρ 0 = 0 :=
  (cubic_remainder_hasFDerivAt_zero hr₁ hK).fderiv

/-- A vector `u` with `t ^ 2 • u = o(t ^ 2)` as `t → 0⁺` vanishes. -/
theorem eq_zero_of_sq_smul_isLittleO {u : F}
    (h : (fun t : ℝ => t ^ 2 • u) =o[𝓝[>] 0] fun t => t ^ 2) : u = 0 := by
  by_contra hu
  have hpos : 0 < ‖u‖ := norm_pos_iff.2 hu
  have h1 := (isLittleO_iff.1 h) (half_pos hpos)
  have h2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  obtain ⟨t, ht, htpos⟩ := (h1.and h2).exists
  rw [norm_smul, norm_pow, Real.norm_eq_abs, abs_of_pos htpos] at ht
  have : 0 < t ^ 2 := by positivity
  nlinarith

/-- A `C²` map with cubic bound has vanishing second derivative at `0`. -/
theorem cubic_remainder_fderiv_fderiv_zero {ρ : E → F} {r₁ K : ℝ} (hr₁ : 0 < r₁)
    (hρ : ContDiffOn ℝ 2 ρ (ball (0 : E) r₁))
    (hK : ∀ Y ∈ ball (0 : E) r₁, ‖ρ Y‖ ≤ K * ‖Y‖ ^ 3) :
    fderiv ℝ (fderiv ℝ ρ) 0 = 0 := by
  set s := ball (0 : E) r₁
  set B := fderiv ℝ (fderiv ℝ ρ) 0
  have hint : interior s = s := isOpen_ball.interior_eq
  have hat : ∀ Y ∈ s, ContDiffAt ℝ 2 ρ Y := fun Y hY =>
    hρ.contDiffAt (isOpen_ball.mem_nhds hY)
  have hf : ∀ x ∈ interior s, HasFDerivAt ρ (fderiv ℝ ρ x) x := by
    intro x hx
    rw [hint] at hx
    exact ((hat x hx).differentiableAt (by norm_num)).hasFDerivAt
  have hx : HasFDerivWithinAt (fderiv ℝ ρ) B (interior s) 0 := by
    have h1 : ContDiffAt ℝ 1 (fderiv ℝ ρ) 0 :=
      (hat 0 (mem_ball_self hr₁)).fderiv_right (by norm_num)
    exact (h1.differentiableAt one_ne_zero).hasFDerivAt.hasFDerivWithinAt
  have hD1 := cubic_remainder_fderiv_zero hr₁ hK
  -- the Taylor identity: `B v w + ½ B w w = 0` for small `v`, `v + w`
  have key : ∀ v w : E, ‖v‖ < r₁ → ‖v + w‖ < r₁ → B v w + (1 / 2 : ℝ) • B w w = 0 := by
    intro v w hv hw
    have hv' : (0 : E) + v ∈ interior s := by
      rw [hint, zero_add]; exact mem_ball_zero_iff.2 hv
    have hw' : (0 : E) + v + w ∈ interior s := by
      rw [hint, zero_add]; exact mem_ball_zero_iff.2 hw
    have hT := (convex_ball (0 : E) r₁).taylor_approx_two_segment hf (mem_ball_self hr₁) hx
      hv' hw'
    have hA := (cubic_remainder_isLittleO_sq hr₁ hK (v + w)).mono
      (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    have hB := (cubic_remainder_isLittleO_sq hr₁ hK v).mono
      (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    apply eq_zero_of_sq_smul_isLittleO
    have hsum := (hA.sub hB).sub hT
    refine hsum.congr' (Eventually.of_forall fun t => ?_) EventuallyEq.rfl
    simp only [zero_add, hD1, zero_apply, smul_zero, sub_zero, smul_add]
    rw [smul_smul]
    module
  have hdiag : ∀ w : E, ‖w‖ < r₁ → B w w = 0 := by
    intro w hw
    have := key 0 w (by simpa using hr₁) (by simpa using hw)
    simpa using this
  have hsmall : ∀ v w : E, ‖v‖ < r₁ / 2 → ‖w‖ < r₁ / 2 → B v w = 0 := by
    intro v w hv hw
    have h1 := key v w (by linarith) ((norm_add_le _ _).trans_lt (by linarith))
    rw [hdiag w (by linarith), smul_zero, add_zero] at h1
    exact h1
  ext v w
  -- rescale `v` and `w` into the small ball
  set c : ℝ := r₁ / (4 * (‖v‖ + ‖w‖ + 1)) with hc
  have hden : 0 < 4 * (‖v‖ + ‖w‖ + 1) := by positivity
  have hcpos : 0 < c := div_pos hr₁ hden
  have hcn : ∀ z : E, ‖z‖ ≤ ‖v‖ + ‖w‖ → ‖c • z‖ < r₁ / 2 := by
    intro z hz
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hcpos, hc, div_mul_eq_mul_div,
      div_lt_iff₀ hden]
    nlinarith [norm_nonneg z, norm_nonneg v, norm_nonneg w]
  have h := hsmall (c • v) (c • w) (hcn v (by linarith [norm_nonneg w]))
    (hcn w (by linarith [norm_nonneg v]))
  simp only [map_smul, smul_apply, smul_smul] at h
  simpa [hcpos.ne'] using h

/-- **Lipschitz bound from `C¹` regularity on a compact ball.**  If `E` is finite-dimensional
and `g : E → V` is `C¹` at every point of the closed ball of radius `r₀`, then `g` is Lipschitz on
that ball. -/
theorem exists_lipschitz_closedBall_of_contDiffAt [FiniteDimensional ℝ E] {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {g : E → V} {r₀ : ℝ}
    (hg : ∀ Y ∈ closedBall (0 : E) r₀, ContDiffAt ℝ 1 g Y) :
    ∃ M, 0 ≤ M ∧ ∀ Y ∈ closedBall (0 : E) r₀, ∀ Y' ∈ closedBall (0 : E) r₀,
      ‖g Y - g Y'‖ ≤ M * ‖Y - Y'‖ := by
  have hcont : ∀ Y ∈ closedBall (0 : E) r₀, ContinuousAt (fderiv ℝ g) Y :=
    fun Y hY => ((hg Y hY).fderiv_right (m := 0) (by norm_num)).continuousAt
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : E) r₀).exists_bound_of_continuousOn
    (continuousOn_of_forall_continuousAt hcont)
  refine ⟨max M 0, le_max_right _ _, fun Y hY Y' hY' => ?_⟩
  exact (convex_closedBall (0 : E) r₀).norm_image_sub_le_of_norm_fderiv_le
    (fun Z hZ => (hg Z hZ).differentiableAt one_ne_zero)
    (fun Z hZ => (hM Z hZ).trans (le_max_left _ _)) hY' hY

/-- **Cubic remainder ⇒ Lipschitz derivative.**  Let `E` be finite-dimensional, `ρ : E → F`
of class `C³` on the ball of radius `r₁ > 0` with `‖ρ Y‖ ≤ K ‖Y‖³` there.  Then there are
`0 < r₀ < r₁` and `K' ≥ 0` such that on every ball of radius `r ≤ r₀` the derivative of `ρ` is
`K' r`-Lipschitz, and `‖Dρ(Y)‖ ≤ K' ‖Y‖²` for `‖Y‖ ≤ r₀`. -/
theorem cubic_remainder_fderiv_lipschitz [FiniteDimensional ℝ E] {ρ : E → F} {r₁ K : ℝ}
    (hr₁ : 0 < r₁) (hρ : ContDiffOn ℝ 3 ρ (ball (0 : E) r₁))
    (hK : ∀ Y ∈ ball (0 : E) r₁, ‖ρ Y‖ ≤ K * ‖Y‖ ^ 3) :
    ∃ r₀, 0 < r₀ ∧ r₀ < r₁ ∧ ∃ K', 0 ≤ K' ∧
      (∀ r, 0 ≤ r → r ≤ r₀ → ∀ Y Y' : E, ‖Y‖ ≤ r → ‖Y'‖ ≤ r →
        ‖fderiv ℝ ρ Y - fderiv ℝ ρ Y'‖ ≤ K' * r * ‖Y - Y'‖) ∧
      (∀ Y : E, ‖Y‖ ≤ r₀ → ‖fderiv ℝ ρ Y‖ ≤ K' * ‖Y‖ ^ 2) := by
  set r₀ := r₁ / 2 with hr₀
  have hr₀pos : 0 < r₀ := half_pos hr₁
  have hr₀lt : r₀ < r₁ := half_lt_self hr₁
  have hsub : closedBall (0 : E) r₀ ⊆ ball (0 : E) r₁ := closedBall_subset_ball hr₀lt
  have hat : ∀ Y ∈ closedBall (0 : E) r₀, ContDiffAt ℝ 3 ρ Y := fun Y hY =>
    hρ.contDiffAt (isOpen_ball.mem_nhds (hsub hY))
  have hat1 : ∀ Y ∈ closedBall (0 : E) r₀, ContDiffAt ℝ 2 (fderiv ℝ ρ) Y := fun Y hY =>
    (hat Y hY).fderiv_right (by norm_num)
  have hat2 : ∀ Y ∈ closedBall (0 : E) r₀, ContDiffAt ℝ 1 (fderiv ℝ (fderiv ℝ ρ)) Y :=
    fun Y hY => (hat1 Y hY).fderiv_right (by norm_num)
  obtain ⟨M, hM0, hM⟩ := exists_lipschitz_closedBall_of_contDiffAt hat2
  set K' := M
  have hD1 := cubic_remainder_fderiv_zero hr₁ hK
  have hD2 := cubic_remainder_fderiv_fderiv_zero hr₁ (hρ.of_le (by norm_num)) hK
  -- step 1: `‖D²ρ(Y)‖ ≤ K' ‖Y‖`
  have hstep1 : ∀ Y ∈ closedBall (0 : E) r₀, ‖fderiv ℝ (fderiv ℝ ρ) Y‖ ≤ K' * ‖Y‖ := by
    intro Y hY
    have := hM Y hY 0 (mem_closedBall_self hr₀pos.le)
    simpa [hD2] using this
  -- step 2: the Lipschitz bound
  have hstep2 : ∀ r, 0 ≤ r → r ≤ r₀ → ∀ Y Y' : E, ‖Y‖ ≤ r → ‖Y'‖ ≤ r →
      ‖fderiv ℝ ρ Y - fderiv ℝ ρ Y'‖ ≤ K' * r * ‖Y - Y'‖ := by
    intro r _ hr Y Y' hY hY'
    have hss : closedBall (0 : E) r ⊆ closedBall (0 : E) r₀ := closedBall_subset_closedBall hr
    exact (convex_closedBall (0 : E) r).norm_image_sub_le_of_norm_fderiv_le
      (fun Z hZ => (hat1 Z (hss hZ)).differentiableAt (by norm_num))
      (fun Z hZ => (hstep1 Z (hss hZ)).trans
        (mul_le_mul_of_nonneg_left (mem_closedBall_zero_iff.1 hZ) hM0))
      (mem_closedBall_zero_iff.2 hY') (mem_closedBall_zero_iff.2 hY)
  refine ⟨r₀, hr₀pos, hr₀lt, K', hM0, hstep2, fun Y hY => ?_⟩
  have := hstep2 ‖Y‖ (norm_nonneg _) hY Y 0 le_rfl (by simp)
  rw [hD1, sub_zero, sub_zero] at this
  calc ‖fderiv ℝ ρ Y‖ ≤ K' * ‖Y‖ * ‖Y‖ := this
    _ = K' * ‖Y‖ ^ 2 := by ring

/-- **Cubic remainder ⇒ Lipschitz derivative, analytic version.** -/
theorem cubic_remainder_fderiv_lipschitz_of_analyticOnNhd [FiniteDimensional ℝ E]
    [CompleteSpace F] {ρ : E → F} {r₁ K : ℝ} (hr₁ : 0 < r₁)
    (hρ : AnalyticOnNhd ℝ ρ (ball (0 : E) r₁))
    (hK : ∀ Y ∈ ball (0 : E) r₁, ‖ρ Y‖ ≤ K * ‖Y‖ ^ 3) :
    ∃ r₀, 0 < r₀ ∧ r₀ < r₁ ∧ ∃ K', 0 ≤ K' ∧
      (∀ r, 0 ≤ r → r ≤ r₀ → ∀ Y Y' : E, ‖Y‖ ≤ r → ‖Y'‖ ≤ r →
        ‖fderiv ℝ ρ Y - fderiv ℝ ρ Y'‖ ≤ K' * r * ‖Y - Y'‖) ∧
      (∀ Y : E, ‖Y‖ ≤ r₀ → ‖fderiv ℝ ρ Y‖ ≤ K' * ‖Y‖ ^ 2) :=
  cubic_remainder_fderiv_lipschitz hr₁ ((hρ.contDiffOn isOpen_ball.uniqueDiffOn).of_le le_top) hK

/-! ### Rescaling and bilinear coefficients -/

/-- **Derivative of the rescaled remainder.**  For `h ≠ 0`, the map
`ρ_h A = (h ^ 2)⁻¹ • ρ (h • A)` has derivative `h⁻¹ • Dρ(h A)` at `A`. -/
theorem fderiv_scaled {ρ : E → F} {h : ℝ} (hh : h ≠ 0) {A : E}
    (hd : DifferentiableAt ℝ ρ (h • A)) :
    fderiv ℝ (fun B : E => (h ^ 2)⁻¹ • ρ (h • B)) A = h⁻¹ • fderiv ℝ ρ (h • A) := by
  have hlin : HasFDerivAt (fun B : E => h • B) (h • ContinuousLinearMap.id ℝ E) A :=
    (hasFDerivAt_id A).const_smul h
  have hcomp : HasFDerivAt (fun B : E => (h ^ 2)⁻¹ • ρ (h • B))
      ((h ^ 2)⁻¹ • (fderiv ℝ ρ (h • A)).comp (h • ContinuousLinearMap.id ℝ E)) A :=
    (hd.hasFDerivAt.comp A hlin).const_smul (h ^ 2)⁻¹
  rw [hcomp.fderiv]
  ext v
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_smul]
  congr 1
  field_simp

/-- **Lipschitz bound for the rescaled remainder.**  If `ρ` is differentiable on the ball of
radius `r₁ > r₀` and its derivative is `K' r`-Lipschitz on balls of radius `r ≤ r₀`, then for
`h > 0`, `R ≥ 0`, `h R ≤ r₀`, the rescaled `ρ_h A = h⁻² ρ (h A)` has
`‖Dρ_h(A) - Dρ_h(A')‖ ≤ K' (h R) ‖A - A'‖` on the closed `R`-ball. -/
theorem norm_fderiv_scaled_sub_le {ρ : E → F} {r₀ r₁ K' : ℝ}
    (hρ : DifferentiableOn ℝ ρ (ball (0 : E) r₁)) (hr₀ : r₀ < r₁)
    (hLip : ∀ r, 0 ≤ r → r ≤ r₀ → ∀ Y Y' : E, ‖Y‖ ≤ r → ‖Y'‖ ≤ r →
      ‖fderiv ℝ ρ Y - fderiv ℝ ρ Y'‖ ≤ K' * r * ‖Y - Y'‖)
    {h R : ℝ} (hh : 0 < h) (hR : 0 ≤ R) (hhR : h * R ≤ r₀) {A A' : E} (hA : ‖A‖ ≤ R)
    (hA' : ‖A'‖ ≤ R) :
    ‖fderiv ℝ (fun B : E => (h ^ 2)⁻¹ • ρ (h • B)) A -
        fderiv ℝ (fun B : E => (h ^ 2)⁻¹ • ρ (h • B)) A'‖ ≤ K' * (h * R) * ‖A - A'‖ := by
  have hn : ∀ Z : E, ‖Z‖ ≤ R → ‖h • Z‖ ≤ h * R := by
    intro Z hZ
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hh]
    exact mul_le_mul_of_nonneg_left hZ hh.le
  have hd : ∀ Z : E, ‖Z‖ ≤ R → DifferentiableAt ℝ ρ (h • Z) := by
    intro Z hZ
    refine hρ.differentiableAt (isOpen_ball.mem_nhds ?_)
    exact mem_ball_zero_iff.2 ((hn Z hZ).trans_lt (hhR.trans_lt hr₀))
  rw [fderiv_scaled hh.ne' (hd A hA), fderiv_scaled hh.ne' (hd A' hA'), ← smul_sub,
    norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hh]
  have h1 := hLip (h * R) (mul_nonneg hh.le hR) hhR (h • A) (h • A') (hn A hA) (hn A' hA')
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hh] at h1
  rw [inv_mul_le_iff₀ hh]
  calc ‖fderiv ℝ ρ (h • A) - fderiv ℝ ρ (h • A')‖ ≤ K' * (h * R) * (h * ‖A - A'‖) := h1
    _ = h * (K' * (h * R) * ‖A - A'‖) := by ring

/-- **Bilinear coefficients.**  If `ρ_c(Y) = Φ c (ρ Y)` with `Φ` a continuous bilinear map, the
derivative differences of `ρ_c` are controlled by `‖Φ‖ ‖c‖` times those of `ρ`. -/
theorem norm_fderiv_bilinear_sub_le {G H : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H] (Φ : G →L[ℝ] F →L[ℝ] H) (c : G) {ρ : E → F}
    {Y Y' : E} (hY : DifferentiableAt ℝ ρ Y) (hY' : DifferentiableAt ℝ ρ Y') :
    ‖fderiv ℝ (fun Z => Φ c (ρ Z)) Y - fderiv ℝ (fun Z => Φ c (ρ Z)) Y'‖ ≤
      ‖Φ‖ * ‖c‖ * ‖fderiv ℝ ρ Y - fderiv ℝ ρ Y'‖ := by
  have h1 : fderiv ℝ (fun Z => Φ c (ρ Z)) Y = (Φ c).comp (fderiv ℝ ρ Y) :=
    ((Φ c).hasFDerivAt.comp Y hY.hasFDerivAt).fderiv
  have h2 : fderiv ℝ (fun Z => Φ c (ρ Z)) Y' = (Φ c).comp (fderiv ℝ ρ Y') :=
    ((Φ c).hasFDerivAt.comp Y' hY'.hasFDerivAt).fderiv
  rw [h1, h2, ← ContinuousLinearMap.comp_sub]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_right (Φ.le_opNorm c) (norm_nonneg _))

/-- **Uniform-in-coefficient Lipschitz bound.**  Under the conclusions of
`cubic_remainder_fderiv_lipschitz`, the coefficient family `ρ_c(Y) = Φ c (ρ Y)` has
`‖Dρ_c(Y) - Dρ_c(Y')‖ ≤ ‖Φ‖ ‖c‖ K' r ‖Y - Y'‖` on balls of radius `r ≤ r₀`. -/
theorem norm_fderiv_bilinear_sub_le_of_lipschitz {G H : Type*} [NormedAddCommGroup G]
    [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H] (Φ : G →L[ℝ] F →L[ℝ] H)
    (c : G) {ρ : E → F} {r₀ r₁ K' : ℝ} (hρ : DifferentiableOn ℝ ρ (ball (0 : E) r₁))
    (hr₀ : r₀ < r₁)
    (hLip : ∀ r, 0 ≤ r → r ≤ r₀ → ∀ Y Y' : E, ‖Y‖ ≤ r → ‖Y'‖ ≤ r →
      ‖fderiv ℝ ρ Y - fderiv ℝ ρ Y'‖ ≤ K' * r * ‖Y - Y'‖)
    {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ r₀) {Y Y' : E} (hY : ‖Y‖ ≤ r) (hY' : ‖Y'‖ ≤ r) :
    ‖fderiv ℝ (fun Z => Φ c (ρ Z)) Y - fderiv ℝ (fun Z => Φ c (ρ Z)) Y'‖ ≤
      ‖Φ‖ * ‖c‖ * K' * r * ‖Y - Y'‖ := by
  have hd : ∀ Z : E, ‖Z‖ ≤ r → DifferentiableAt ℝ ρ Z := fun Z hZ =>
    hρ.differentiableAt (isOpen_ball.mem_nhds
      (mem_ball_zero_iff.2 ((hZ.trans hr).trans_lt hr₀)))
  calc _ ≤ ‖Φ‖ * ‖c‖ * ‖fderiv ℝ ρ Y - fderiv ℝ ρ Y'‖ :=
        norm_fderiv_bilinear_sub_le Φ c (hd Y hY) (hd Y' hY')
    _ ≤ ‖Φ‖ * ‖c‖ * (K' * r * ‖Y - Y'‖) :=
        mul_le_mul_of_nonneg_left (hLip r hr0 hr Y Y' hY hY') (by positivity)
    _ = ‖Φ‖ * ‖c‖ * K' * r * ‖Y - Y'‖ := by ring

end Cubic

end StationaryContraction

end RenewalGeometry
