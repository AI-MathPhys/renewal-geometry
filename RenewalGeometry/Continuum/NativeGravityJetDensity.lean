/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Action.NativeFirstJetNormalFormExact
import RenewalGeometry.Analysis.PlaquetteBCHExpansion

/-!
# The literal gravitational density on coframe first jets: scaling, regularity, continuum limit
  (jet-level part of `prop:native-gravity-firstjet`, Einstein–SM action-closure manuscript)

The finite gravitational row of `eq:native-densities` is
`𝓛_{g,h} = v(e)/(2κ) e_a^μ e^{bν} (R^h_{μν})^a_b - (Λ/κ) v(e)` with the literal Cartan plaquette
`R^h_{μν} = h⁻² log(L_μ(x) L_ν(x+he_μ) L_μ(x+he_ν)⁻¹ L_ν(x)⁻¹)`, `L_μ = exp(h ω_{μ,h})`,
`ω_{μ,h} = Ω_μ(e, δ⁺_h e)` (`NativeDensity.gravityDensity`).  The first-jet normal form
(`lem:native-firstjet-normal-form`, `NativeDensity.localAction_eq_action_firstJetDensity`) writes
its sum over the periodic grid as `h⁴ Σ_x F^{(1)}_h(Ξ_h y(x))`: the curl `δ⁺_μω_ν - δ⁺_νω_μ` of the
plaquette logarithm is moved onto the Palatini coefficient by summation by parts, and only the
exact quadratic remainder `Rem = Q_h(W)` of the logarithm remains.  This file works with the
**coframe part** of that density on coframe jets `w = (v, q) ∈ JetM` (shifted values `v` over the
nine shifts `0, ±e_μ` and normalised first differences `q`), and proves:

* `gravFirstJet_stencil` / `sum_gravityDensity_eq`: on the oriented logarithm chart the grid sum of
  the literal gravitational density is `Σ_x (gravCurv κ (h, Ξ_h e(x)) - (Λ/κ) v(e(x)))`.
* `gravCurv_scale` (**exact degree-two scaling**, `lem:native-scaling` on jets):
  `gravCurv κ (ρ, v, q) = K² gravCurv κ (ρK, v, K⁻¹q)` for `K ≠ 0`
  (`remPlaquette_scale`: the plaquette remainder is homogeneous of degree `-2` under
  `(h, slots) ↦ (hK, slots/K)`; `dqPal_scale`: the divided Palatini difference is homogeneous of
  degree `-1`).
* `contDiffAt_gravCurv` (regularity off `ρ = 0`): `gravCurv κ` is smooth at every point where the
  shifted coframes are invertible, the segment coframes `e(x - e_μ) + ρ δ⁺_μ e(x - e_μ)` are
  invertible and the four-exponential plaquettes satisfy `‖P - 1‖ < 1`;
  `norm_plaquette_sub_one_lt` / `logChart_of_margin`: the **common logarithm-chart condition**
  `eq:native-gravity-log-margin` `ρ |ω| ≤ c_* ≤ 1/64` (matrix sup norm) implies `‖P - 1‖ < 1`.
* `gravChart` / `isCompact_gravChart` / `contDiffAt_of_mem_gravChart`: the compact set of
  normalised jets (mesh `≤ R`, values and segment values in a compact chart `K_e ⊂ {det > 0}`,
  normalised differences of norm `≤ 1`, margin `c_*`) on which `gravCurv` is smooth.
* The continuum first-order Palatini density `palatiniFirstOrder κ Λ e p = gravCurv κ (0, ē, p̄) -
  (Λ/κ) v(e)` at the constant jet, identified explicitly (`palatiniFirstOrder_eq`) as
  `Σ pal(e)^{μν}_{ab} [ω_μ, ω_ν]^a_b - Σ (D_e C^{μν}(e)[p_μ])_{ab} ω_ν^{ab} - (Λ/κ) v(e)`,
  `ω = Ω(e, p)` (`remPlaquette_zero_comm`: `Rem(0; X, Y, 0, 0) = [X, Y]`; `hasDerivAt_palA`:
  `dqPal(0; e, p) = D_e C(e)[p]`).  This is the representative `-dB ∧ ω + B ∧ ω ∧ ω` of
  `eq:palatini-first-order` in the chart's coordinates (`app:palatini`).
-/

open NormedSpace Finset Filter Topology
open scoped ContDiff

namespace RenewalGeometry.NativeGravityJet

open ShiftedJetAction (Grid unitVec fwdDiff stencil)
open NativeScaling (Mat eta metric readerOmega omegaLink)
open ShiftedPlaquette NativeDensity

noncomputable section

/-! ### Generic algebra of the plaquette remainder -/

section Scaling

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄]

theorem linkExp_smul (ρ L : ℝ) (v : 𝔄) : linkExp ρ (L • v) = L • linkExp (ρ * L) v := by
  unfold linkExp
  rw [smul_smul, smul_pow, smul_mul_assoc, smul_smul, smul_add, smul_smul]
  congr 2
  ring

theorem sqE_smul (ρ L : ℝ) (u : 𝔄) :
    (L • u) ^ 2 * expRemainder (ρ • (L • u)) = L ^ 2 • (u ^ 2 * expRemainder ((ρ * L) • u)) := by
  rw [smul_smul, smul_pow, smul_mul_assoc]

/-- The remainder `G` of the explicit quotient is homogeneous of degree two in the slots under
`(ρ, slots) ↦ (ρ, L · slots)`, `ρ L` fixed. -/
theorem remQuotient_smul (ρ L : ℝ) (X Y A B : 𝔄) :
    remQuotient ρ (L • X) (L • Y) (L • A) (L • B) = L ^ 2 • remQuotient (ρ * L) X Y A B := by
  unfold remQuotient
  have e1 : L • Y + L • A = L • (Y + A) := (smul_add L Y A).symm
  have e2 : -(L • X + L • B) = L • -(X + B) := by rw [smul_neg, smul_add]
  have e3 : -(L • Y) = L • -Y := (smul_neg L Y).symm
  rw [e1, e2, e3, sqE_smul, sqE_smul, sqE_smul, sqE_smul, linkExp_smul, linkExp_smul,
    linkExp_smul, linkExp_smul]
  simp only [smul_mul_smul_comm, smul_smul]
  module

/-- The plaquette remainder `Rem` is homogeneous of degree two in the slots under
`(ρ, slots) ↦ (ρ, L · slots)`, `ρ L` fixed. -/
theorem remPlaquette_smul (ρ L : ℝ) (X Y A B : 𝔄) :
    remPlaquette (ρ, L • X, L • Y, L • A, L • B) = L ^ 2 • remPlaquette (ρ * L, X, Y, A, B) := by
  unfold remPlaquette
  simp only []
  rw [remQuotient_smul]
  set G := remQuotient (ρ * L) X Y A B
  have hW : (L • A - L • B) + ρ • (L ^ 2 • G) = L • ((A - B) + (ρ * L) • G) := by module
  rw [hW, smul_pow, smul_smul ρ L, smul_mul_assoc, ← smul_add]

end Scaling

section Chart

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]

/-- The chart quantity `ρ((A - B) + ρ G(ρ; X, Y, A, B))` of the curl decomposition, as a function
of the joint variable. -/
def plaqDevGen (p : ℝ × 𝔄 × 𝔄 × 𝔄 × 𝔄) : 𝔄 :=
  p.1 • ((p.2.2.2.1 - p.2.2.2.2) + p.1 • remQuotient p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)

/-- The four-exponential plaquette is within the logarithm chart when the exponents are small:
`‖e^a e^b e^c e^d - 1‖ < 1` for `‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ ≤ 1/4`. -/
theorem norm_exp4_sub_one_lt {a b c d : 𝔄} (h : ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ ≤ 1 / 4) :
    ‖exp a * exp b * exp c * exp d - 1‖ < 1 := by
  have e : exp a * exp b * exp c * exp d = LogBCH.expProd [a, b, c, d] := by
    simp [LogBCH.expProd_cons, mul_assoc]
  rw [e]
  refine LogBCH.PlaquetteBCH.norm_expProd_sub_one_lt _ ?_
  simp only [LogBCH.normSum_cons, LogBCH.normSum_nil]
  linarith

/-- The plaquette deviation in the curl variables: for `ρ ≠ 0`,
`ρ((A - B) + ρ G(ρ; X, Y, A, B)) = e^{ρX} e^{ρ(Y+A)} e^{-ρ(X+B)} e^{-ρY} - 1`. -/
theorem plaqDev_eq_exp {ρ : ℝ} (hρ : ρ ≠ 0) (X Y A B : 𝔄) :
    ρ • ((A - B) + ρ • remQuotient ρ X Y A B) =
      exp (ρ • X) * exp (ρ • (Y + A)) * exp (ρ • -(X + B)) * exp (ρ • -Y) - 1 := by
  have h1 := product_sub_one_eq ρ X Y (ρ⁻¹ • A) (ρ⁻¹ • B)
  rw [quotientPoly_eq_remQuotient, smul_smul ρ ρ⁻¹, smul_smul ρ ρ⁻¹, mul_inv_cancel₀ hρ, one_smul,
    one_smul, product_eq_exp_smul, smul_smul ρ ρ⁻¹, smul_smul ρ ρ⁻¹, mul_inv_cancel₀ hρ, one_smul,
    one_smul] at h1
  rw [h1, smul_add, smul_add, smul_sub, smul_sub, smul_smul, smul_smul, smul_smul, sq,
    mul_assoc, mul_inv_cancel₀ hρ, mul_one]

/-- **The logarithm chart from the margin**: if the four exponents have norms `≤ ρ‖·‖ ≤ c`,
`c ≤ 1/16`, the curl variables satisfy `‖ρ((A - B) + ρG)‖ < 1`. -/
theorem norm_plaqDev_lt {ρ c : ℝ} (hρ : 0 ≤ ρ) (hc : c ≤ 1 / 16) (X Y A B : 𝔄)
    (hX : ρ * ‖X‖ ≤ c) (hY : ρ * ‖Y‖ ≤ c) (hYA : ρ * ‖Y + A‖ ≤ c) (hXB : ρ * ‖X + B‖ ≤ c) :
    ‖plaqDevGen (ρ, X, Y, A, B)‖ < 1 := by
  unfold plaqDevGen
  simp only []
  rcases eq_or_lt_of_le hρ with h0 | hpos
  · subst h0; simp
  rw [plaqDev_eq_exp hpos.ne']
  refine norm_exp4_sub_one_lt ?_
  simp only [norm_smul, Real.norm_of_nonneg hρ, norm_neg]
  linarith

/-- `Rem ∘ g` is smooth wherever `g` is smooth and the curl variables lie in the logarithm
chart (generic in the algebra, so that it applies to `Op` without unfolding its instances). -/
theorem contDiffAt_remPlaquette_comp' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → ℝ × 𝔄 × 𝔄 × 𝔄 × 𝔄} {z : E} (hg : ContDiffAt ℝ ∞ g z)
    (hp : ‖plaqDevGen (g z)‖ < 1) : ContDiffAt ℝ ∞ (fun z => remPlaquette (g z)) z :=
  ContDiffAt.comp z (analyticAt_remPlaquette hp).contDiffAt hg

/-- `Rem(0; X, Y, 0, 0) = [X, Y]`: at the mesh origin and vanishing translation slots, the
quadratic remainder of the plaquette logarithm is the commutator. -/
theorem remPlaquette_zero_comm (X Y : 𝔄) :
    remPlaquette ((0 : ℝ), X, Y, (0 : 𝔄), (0 : 𝔄)) = X * Y - Y * X := by
  have h := logPlaquette_eq_curl_add_rem X Y (0 : 𝔄) (0 : 𝔄) (h := (0 : ℝ)) (by simp)
  rw [logPlaquette_zero, curvature, smul_zero, sub_self, zero_add, zero_add] at h
  exact h.symm

end Chart

end

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

/-! ### Coframe jets -/

/-- Shifted coframe values over the nine shifts `0, ±e_μ`. -/
abbrev Vals := Shift → Mat

/-- Normalised first differences of the coframe at the shifted nodes. -/
abbrev Diffs := Shift × Fin 4 → Mat

/-- Coframe first jets. -/
abbrev JetM := Vals × Diffs

/-- `ω_μ = Ω_μ(e, δ⁺e)` at the base node. -/
def omegaM (μ : Fin 4) (w : JetM) : Mat := readerOmega (w.1 none) (fun lam => w.2 (none, lam)) μ

/-- `ω_ν` at the node shifted by `+e_μ`. -/
def omegaShiftM (ν μ : Fin 4) (w : JetM) : Mat :=
  readerOmega (w.1 (some (true, μ))) (fun lam => w.2 (some (true, μ), lam)) ν

/-- The coframe at the node shifted by `-e_μ`. -/
def emM (μ : Fin 4) (w : JetM) : Mat := w.1 (some (false, μ))

/-- `δ⁺_μ e` at the node shifted by `-e_μ`. -/
def pmM (μ : Fin 4) (w : JetM) : Mat := w.2 (some (false, μ), μ)

/-- The Cartan remainder `Rem(ρ; X, Y, A, B)` of the curl decomposition on coframe jets. -/
def remM (μ ν : Fin 4) (z : ℝ × JetM) : Op :=
  remPlaquette (z.1, matToOp (omegaM μ z.2), matToOp (omegaM ν z.2),
    matToOp (omegaShiftM ν μ z.2 - omegaM ν z.2), matToOp (omegaShiftM μ ν z.2 - omegaM μ z.2))

/-- **The curvature part of the gravitational first-jet density** on coframe jets: the remainder
of the Cartan plaquette contracted with the Palatini coefficient, and the summation-by-parts form
`-⟨δ⁻_μ C^{μν}, ω_ν⟩` of the curl. -/
def gravCurv (κ : ℝ) (z : ℝ × JetM) : ℝ :=
  (∑ μ, ∑ ν, ∑ a, ∑ b, pal κ (z.2.1 none) μ ν a b *
      opEntry (antisym (fun μ ν => remM μ ν z) μ ν) a b) -
    ∑ μ, ∑ ν, ∑ a, ∑ b, dqPal κ z.1 (emM μ z.2) (pmM μ z.2) μ ν a b * omegaM ν z.2 a b

/-! ### Relation to the native first-jet density -/

section Relation

variable {𝔄 : Type*} [NormedRing 𝔄] [NormedAlgebra ℝ 𝔄] [CompleteSpace 𝔄] [NormOneClass 𝔄]
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [CompleteSpace 𝓗] [Nontrivial 𝓗]
variable {𝓢 : Type*} [NormedAddCommGroup 𝓢] [NormedSpace ℝ 𝓢] [CompleteSpace 𝓢] [Nontrivial 𝓢]
variable (D : Data 𝔄 𝓗 𝓢)
variable {n : ℕ} [NeZero n]

/-- The gravitational part `F^{(1)}_g` of the native first-jet density at the stencil of a record
is the coframe density at the stencil of its coframe. -/
theorem gravFirstJet_stencil (h : ℝ) (y : Grid n → Field 𝔄 𝓗 𝓢) (x : Grid n) :
    gravFirstJet D (h, stencil h (shiftVec n) x y) =
      gravCurv D.κ (h, stencil h (shiftVec n) x (coframe y)) -
        D.Λ / D.κ * volume (coframe y x) := by
  unfold gravFirstJet gravCurv remCartan remM jetOmega jetOmegaShift jetEm jetPm omegaM
    omegaShiftM emM pmM
  simp only [stencil_fst, stencil_snd, fwdDiff_coframe, coframe, shiftVec_none, add_zero]
  ring

/-- **The literal gravitational action as a coframe first-jet sum**: on the oriented logarithm
chart, `Σ_x 𝓛_{g,h}(y)(x) = Σ_x (gravCurv κ (h, Ξ_h e(x)) - (Λ/κ) v(e(x)))`, `e = coframe y`. -/
theorem sum_gravityDensity_eq {h : ℝ} (hh : h ≠ 0) (y : Grid n → Field 𝔄 𝓗 𝓢)
    (hdet : ∀ x, 0 < (coframe y x).det)
    (hlog : ∀ x μ ν, ‖cartanPlaquette h (coframe y) x μ ν - 1‖ < 1) :
    ∑ x, gravityDensity D h y x =
      ∑ x, (gravCurv D.κ (h, stencil h (shiftVec n) x (coframe y)) -
        D.Λ / D.κ * volume (coframe y x)) := by
  simp only [gravityDensity_eq_curl D hh y _ (hlog _), sum_add_distrib]
  have hcurl := sum_curl_eq D hh y hdet univ
  have hcollar : ∀ (g : Grid n → ℝ) (μ : Fin 4),
      ∑ x ∈ (univ : Finset (Grid n)).map (Equiv.subRight (unitVec n μ)).toEmbedding, g x =
        ∑ x, g x := by
    intro g μ
    rw [sum_map]
    exact Equiv.sum_comp (Equiv.subRight (unitVec n μ)) g
  simp only [hcollar, sub_self, mul_zero, sum_const_zero, add_zero] at hcurl
  rw [hcurl]
  simp_rw [← gravFirstJet_stencil D h y]
  unfold gravFirstJet
  simp only [sum_add_distrib, sum_sub_distrib, sum_neg_distrib, stencil_fst, shiftVec_none,
    add_zero, coframe]
  ring

end Relation

/-! ### Exact scaling -/


section ScalingJet

theorem dqDet_smul (e₀ e₁ p : Mat) (L : ℝ) : dqDet e₀ e₁ (L • p) = L * dqDet e₀ e₁ p := by
  unfold dqDet rowsMix
  rw [mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [show (L • p) i = L • p i from rfl, Matrix.det_updateRow_smul]

theorem palBil_smul_left (X Y : Mat) (L : ℝ) (μ ν a b : Fin 4) :
    palBil (L • X) Y μ ν a b = L * palBil X Y μ ν a b := by
  simp only [palBil, Matrix.smul_apply, smul_eq_mul]
  ring

theorem palBil_smul_right (X Y : Mat) (L : ℝ) (μ ν a b : Fin 4) :
    palBil X (L • Y) μ ν a b = L * palBil X Y μ ν a b := by
  simp only [palBil, Matrix.smul_apply, smul_eq_mul, mul_assoc, ← mul_sum]
  ring

/-- The divided Palatini difference is homogeneous of degree one in the difference slot. -/
theorem dqPal_smul (κ ρ L : ℝ) (e₀ p : Mat) (μ ν a b : Fin 4) :
    dqPal κ ρ e₀ (L • p) μ ν a b = L * dqPal κ (ρ * L) e₀ p μ ν a b := by
  unfold dqPal
  have e1 : e₀ + ρ • (L • p) = e₀ + (ρ * L) • p := by rw [smul_smul]
  have e2 : -((e₀ + (ρ * L) • p)⁻¹ * (L • p) * e₀⁻¹) =
      L • -((e₀ + (ρ * L) • p)⁻¹ * p * e₀⁻¹) := by
    rw [Matrix.mul_smul, Matrix.smul_mul, smul_neg]
  rw [e1, dqDet_smul, e2, palBil_smul_left, palBil_smul_right]
  ring

theorem omegaM_smul (μ : Fin 4) (v : Vals) (q : Diffs) (L : ℝ) :
    omegaM μ (v, L • q) = L • omegaM μ (v, q) := by
  unfold omegaM
  exact NativeScaling.readerOmega_smul (v none) L (fun lam => q (none, lam)) μ

theorem omegaShiftM_smul (ν μ : Fin 4) (v : Vals) (q : Diffs) (L : ℝ) :
    omegaShiftM ν μ (v, L • q) = L • omegaShiftM ν μ (v, q) := by
  unfold omegaShiftM
  exact NativeScaling.readerOmega_smul (v (some (true, μ))) L (fun lam => q (some (true, μ), lam)) ν

theorem matToOp_smul (c : ℝ) (M : Mat) : matToOp (c • M) = c • matToOp M := by
  ext v i
  simp [matToOp_apply, Matrix.smul_mulVec]

theorem remM_smul (μ ν : Fin 4) (ρ L : ℝ) (v : Vals) (q : Diffs) :
    remM μ ν (ρ, (v, L • q)) = L ^ 2 • remM μ ν (ρ * L, (v, q)) := by
  unfold remM
  simp only [omegaM_smul, omegaShiftM_smul, ← smul_sub, matToOp_smul]
  -- the slots are generalised before applying the algebra lemma (instance paths of the scalar
  -- action on `Op` otherwise force a costly unfolding of the concrete slots)
  generalize matToOp (omegaM μ (v, q)) = X
  generalize matToOp (omegaM ν (v, q)) = Y
  generalize matToOp (omegaShiftM ν μ (v, q) - omegaM ν (v, q)) = A
  generalize matToOp (omegaShiftM μ ν (v, q) - omegaM μ (v, q)) = B
  exact remPlaquette_smul ρ L X Y A B

/-- **Exact degree-two homogeneity** of the gravitational curvature density on coframe jets. -/
theorem gravCurv_smul (κ ρ L : ℝ) (v : Vals) (q : Diffs) :
    gravCurv κ (ρ, (v, L • q)) = L ^ 2 * gravCurv κ (ρ * L, (v, q)) := by
  unfold gravCurv
  have h1 : ∀ μ ν a b, opEntry (antisym (fun μ ν => remM μ ν (ρ, (v, L • q))) μ ν) a b =
      L ^ 2 * opEntry (antisym (fun μ ν => remM μ ν (ρ * L, (v, q))) μ ν) a b := by
    intro μ ν a b
    simp only [remM_smul]
    rw [antisym_smul (L ^ 2) (fun μ ν => remM μ ν (ρ * L, (v, q))), opEntry_smul]
  have h2 : ∀ μ, pmM μ (v, L • q) = L • pmM μ (v, q) := fun μ => rfl
  have h3 : ∀ μ, emM μ (v, L • q) = emM μ (v, q) := fun μ => rfl
  simp only [h1, h2, h3, dqPal_smul, omegaM_smul, Matrix.smul_apply, smul_eq_mul]
  rw [mul_sub]
  simp only [mul_sum]
  congr 1
  · refine sum_congr rfl fun μ _ => sum_congr rfl fun ν _ => sum_congr rfl fun a _ =>
      sum_congr rfl fun b _ => ?_
    ring
  · refine sum_congr rfl fun μ _ => sum_congr rfl fun ν _ => sum_congr rfl fun a _ =>
      sum_congr rfl fun b _ => ?_
    ring

/-- **`lem:native-scaling` on coframe jets**: `gravCurv κ (ρ, v, q) = K² gravCurv κ (ρK, v, K⁻¹q)`. -/
theorem gravCurv_scale (κ ρ K : ℝ) (hK : K ≠ 0) (v : Vals) (q : Diffs) :
    gravCurv κ (ρ, (v, q)) = K ^ 2 * gravCurv κ (ρ * K, (v, K⁻¹ • q)) := by
  have e : ρ * K * K⁻¹ = ρ := by field_simp
  rw [gravCurv_smul, e, ← mul_assoc, inv_pow, mul_inv_cancel₀ (pow_ne_zero 2 hK), one_mul]

end ScalingJet

/-! ### The logarithm chart -/


theorem norm_matToOp_le (M : Mat) : ‖matToOp M‖ ≤ 4 * ‖M‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  rw [matToOp_apply]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  simp only [Matrix.mulVec, dotProduct, Real.norm_eq_abs]
  calc |∑ j, M i j * v j| ≤ ∑ j, |M i j * v j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin 4, ‖M‖ * ‖v‖ := by
        refine sum_le_sum fun j _ => ?_
        rw [abs_mul]
        exact mul_le_mul (by simpa using Matrix.norm_entry_le_entrywise_sup_norm M (i := i) (j := j))
          (by simpa using norm_le_pi_norm v j) (abs_nonneg _) (norm_nonneg _)
    _ = 4 * ‖M‖ * ‖v‖ := by simp; ring

/-- The four curl slots `(ρ, X, Y, A, B)` of the Cartan plaquette `μν` of a coframe jet. -/
def slots (μ ν : Fin 4) (z : ℝ × JetM) : ℝ × Op × Op × Op × Op :=
  (z.1, matToOp (omegaM μ z.2), matToOp (omegaM ν z.2),
    matToOp (omegaShiftM ν μ z.2 - omegaM ν z.2), matToOp (omegaShiftM μ ν z.2 - omegaM μ z.2))

theorem remM_eq (μ ν : Fin 4) (z : ℝ × JetM) : remM μ ν z = remPlaquette (slots μ ν z) := rfl

/-- The plaquette chart quantity `ρ((A - B) + ρ G)` of the Cartan remainder of a coframe jet. -/
def plaqDev (μ ν : Fin 4) (z : ℝ × JetM) : Op := plaqDevGen (slots μ ν z)

/-- The margin condition `eq:native-gravity-log-margin` on a coframe jet:
`ρ |ω_μ| ≤ c` at the base node and `ρ |ω_ν| ≤ c` at the shifted nodes `x + e_μ`. -/
def Margin (c : ℝ) (z : ℝ × JetM) : Prop :=
  ∀ μ ν, z.1 * ‖omegaM μ z.2‖ ≤ c ∧ z.1 * ‖omegaShiftM ν μ z.2‖ ≤ c

/-- **`eq:native-gravity-log-margin` implies the logarithm chart** (`c ≤ 1/64`, matrix sup norm). -/
theorem norm_plaqDev_lt_of_margin {c : ℝ} (hc : c ≤ 1 / 64) {z : ℝ × JetM} (hρ : 0 ≤ z.1)
    (hm : Margin c z) (μ ν : Fin 4) : ‖plaqDev μ ν z‖ < 1 := by
  unfold plaqDev slots
  have hb : ∀ M : Mat, z.1 * ‖M‖ ≤ c → z.1 * ‖matToOp M‖ ≤ 4 * c := by
    intro M hM
    calc z.1 * ‖matToOp M‖ ≤ z.1 * (4 * ‖M‖) := mul_le_mul_of_nonneg_left (norm_matToOp_le M) hρ
      _ = 4 * (z.1 * ‖M‖) := by ring
      _ ≤ 4 * c := by linarith
  have hYA : matToOp (omegaM ν z.2) + matToOp (omegaShiftM ν μ z.2 - omegaM ν z.2) =
      matToOp (omegaShiftM ν μ z.2) := by rw [← map_add, add_sub_cancel]
  have hXB : matToOp (omegaM μ z.2) + matToOp (omegaShiftM μ ν z.2 - omegaM μ z.2) =
      matToOp (omegaShiftM μ ν z.2) := by rw [← map_add, add_sub_cancel]
  have h1 := hb _ (hm μ ν).1
  have h2 := hb _ (hm ν μ).1
  have h3 := hb _ (hm μ ν).2
  have h4 := hb _ (hm ν μ).2
  rw [← hYA] at h3
  rw [← hXB] at h4
  generalize matToOp (omegaM μ z.2) = X at h1 h3 h4 ⊢
  generalize matToOp (omegaM ν z.2) = Y at h2 h3 h4 ⊢
  generalize matToOp (omegaShiftM ν μ z.2 - omegaM ν z.2) = A at h3 ⊢
  generalize matToOp (omegaShiftM μ ν z.2 - omegaM μ z.2) = B at h4 ⊢
  exact norm_plaqDev_lt hρ (by linarith) X Y A B h1 h2 h3 h4

/-- Regularity conditions for `gravCurv` at a point: invertible shifted coframes, invertible
segment coframes `e(x-e_μ) + ρ δ⁺_μ e(x-e_μ)`, and all four Cartan plaquettes in the logarithm
chart. -/
def GravRegular (z : ℝ × JetM) : Prop :=
  (∀ s, (z.2.1 s).det ≠ 0) ∧ (∀ μ, (emM μ z.2 + z.1 • pmM μ z.2).det ≠ 0) ∧
    ∀ μ ν, ‖plaqDev μ ν z‖ < 1

theorem contDiffAt_omegaM (μ : Fin 4) {z : ℝ × JetM} (hz : (z.2.1 none).det ≠ 0) :
    ContDiffAt ℝ ∞ (fun z : ℝ × JetM => omegaM μ z.2) z := by
  unfold omegaM
  have h1 : ContDiffAt ℝ ∞ (fun z : ℝ × JetM => (z.2.1 none, fun lam => z.2.2 (none, lam))) z := by
    fun_prop
  refine contDiffAt_pi.mpr fun a => contDiffAt_pi.mpr fun b => ?_
  exact (contDiffAt_readerOmega_entry μ a b (q := (z.2.1 none, fun lam => z.2.2 (none, lam)))
    hz).comp z h1

theorem contDiffAt_omegaShiftM (ν μ : Fin 4) {z : ℝ × JetM}
    (hz : (z.2.1 (some (true, μ))).det ≠ 0) :
    ContDiffAt ℝ ∞ (fun z : ℝ × JetM => omegaShiftM ν μ z.2) z := by
  unfold omegaShiftM
  have h1 : ContDiffAt ℝ ∞ (fun z : ℝ × JetM =>
      (z.2.1 (some (true, μ)), fun lam => z.2.2 (some (true, μ), lam))) z := by
    fun_prop
  refine contDiffAt_pi.mpr fun a => contDiffAt_pi.mpr fun b => ?_
  exact (contDiffAt_readerOmega_entry ν a b
    (q := (z.2.1 (some (true, μ)), fun lam => z.2.2 (some (true, μ), lam))) hz).comp z h1

theorem contDiffAt_remM (μ ν : Fin 4) {z : ℝ × JetM} (hz : GravRegular z) :
    ContDiffAt ℝ ∞ (remM μ ν) z := by
  have hΩ : ∀ μ, ContDiffAt ℝ ∞ (fun z : ℝ × JetM => omegaM μ z.2) z := fun μ =>
    contDiffAt_omegaM μ (hz.1 none)
  have hΩs : ∀ ν μ, ContDiffAt ℝ ∞ (fun z : ℝ × JetM => omegaShiftM ν μ z.2) z := fun ν μ =>
    contDiffAt_omegaShiftM ν μ (hz.1 _)
  have hg : ContDiffAt ℝ ∞ (slots μ ν) z := by
    unfold slots
    simp only [← matToOpL_apply]
    fun_prop
  have hfun : remM μ ν = fun z => remPlaquette (slots μ ν z) := funext fun z => remM_eq μ ν z
  rw [hfun]
  exact contDiffAt_remPlaquette_comp' hg (hz.2.2 μ ν)

/-- **Regularity of the gravitational curvature density off the mesh origin.** -/
theorem contDiffAt_gravCurv (κ : ℝ) {z : ℝ × JetM} (hz : GravRegular z) :
    ContDiffAt ℝ ∞ (gravCurv κ) z := by
  have hR : ∀ μ ν, ContDiffAt ℝ ∞ (remM μ ν) z := fun μ ν => contDiffAt_remM μ ν hz
  have hΩ : ∀ ν, ContDiffAt ℝ ∞ (fun z : ℝ × JetM => omegaM ν z.2) z := fun ν =>
    contDiffAt_omegaM ν (hz.1 none)
  have he0 : (z.2.1 none).det ≠ 0 := hz.1 none
  have hEm : ∀ μ, (emM μ z.2).det ≠ 0 := fun μ => hz.1 _
  have hseg : ∀ μ, (emM μ z.2 + z.1 • pmM μ z.2).det ≠ 0 := hz.2.1
  have hEmc : ∀ μ, ContDiffAt ℝ ∞ (fun z : ℝ × JetM => emM μ z.2) z := fun μ => by
    unfold emM; fun_prop
  have hPmc : ∀ μ, ContDiffAt ℝ ∞ (fun z : ℝ × JetM => pmM μ z.2) z := fun μ => by
    unfold pmM; fun_prop
  have hpal : ∀ μ ν a b, ContDiffAt ℝ ∞ (fun z : ℝ × JetM => pal κ (z.2.1 none) μ ν a b) z :=
    fun μ ν a b => (contDiffAt_pal κ μ ν a b he0).comp z
      (f := fun z : ℝ × JetM => z.2.1 none) (by fun_prop)
  have hdq : ∀ μ ν a b, ContDiffAt ℝ ∞
      (fun z : ℝ × JetM => dqPal κ z.1 (emM μ z.2) (pmM μ z.2) μ ν a b) z :=
    fun μ ν a b => ContDiffAt.dqPal κ μ ν a b (by fun_prop) (hEmc μ) (hPmc μ) (hEm μ) (hseg μ)
  have hant : ∀ μ ν a b, ContDiffAt ℝ ∞
      (fun z : ℝ × JetM => opEntry (antisym (fun μ ν => remM μ ν z) μ ν) a b) z :=
    fun μ ν a b => (ContDiffAt.antisym (P := fun z μ ν => remM μ ν z) (fun μ ν => hR μ ν) μ ν).opEntry
      a b
  have hΩe : ∀ ν a b, ContDiffAt ℝ ∞ (fun z : ℝ × JetM => omegaM ν z.2 a b) z := fun ν a b =>
    contDiffAt_pi.mp (contDiffAt_pi.mp (hΩ ν) a) b
  unfold gravCurv
  refine ContDiffAt.sub ?_ ?_
  · exact ContDiffAt.sum fun μ _ => ContDiffAt.sum fun ν _ => ContDiffAt.sum fun a _ =>
      ContDiffAt.sum fun b _ => (hpal μ ν a b).mul (hant μ ν a b)
  · exact ContDiffAt.sum fun μ _ => ContDiffAt.sum fun ν _ => ContDiffAt.sum fun a _ =>
      ContDiffAt.sum fun b _ => (hdq μ ν a b).mul (hΩe ν a b)


/-! ### The compact set of normalised jets -/

/-- The compact set of normalised coframe jets: mesh in `[0, R]`, shifted coframes and segment
coframes `e(x+s) + ρ δ⁺_λ e(x+s) = e(x+s+e_λ)` in the chart `K_e`, normalised differences of norm
`≤ 1`, and the logarithm margin `c`. -/
def gravChart (Ke : Set Mat) (R c : ℝ) : Set (ℝ × JetM) :=
  {z | 0 ≤ z.1 ∧ z.1 ≤ R ∧ (∀ s, z.2.1 s ∈ Ke) ∧ ‖z.2.2‖ ≤ 1 ∧
    (∀ s lam, z.2.1 s + z.1 • z.2.2 (s, lam) ∈ Ke) ∧ Margin c z}

theorem continuousOn_omegaM (μ : Fin 4) {Ke : Set Mat} (hKe : ∀ e ∈ Ke, 0 < e.det) :
    ContinuousOn (fun z : ℝ × JetM => omegaM μ z.2) {z | ∀ s, z.2.1 s ∈ Ke} := fun z hz =>
  (contDiffAt_omegaM μ (hKe _ (hz none)).ne').continuousAt.continuousWithinAt

theorem continuousOn_omegaShiftM (ν μ : Fin 4) {Ke : Set Mat} (hKe : ∀ e ∈ Ke, 0 < e.det) :
    ContinuousOn (fun z : ℝ × JetM => omegaShiftM ν μ z.2) {z | ∀ s, z.2.1 s ∈ Ke} := fun z hz =>
  (contDiffAt_omegaShiftM ν μ (hKe _ (hz _)).ne').continuousAt.continuousWithinAt

theorem isClosed_valsIn {Ke : Set Mat} (hKe : IsClosed Ke) :
    IsClosed {z : ℝ × JetM | ∀ s, z.2.1 s ∈ Ke} := by
  simp only [Set.setOf_forall]
  exact isClosed_iInter fun s => hKe.preimage (by fun_prop)

/-- **The normalised jet chart is compact.** -/
theorem isCompact_gravChart {Ke : Set Mat} (hKe : IsCompact Ke) (hdet : ∀ e ∈ Ke, 0 < e.det)
    (R c : ℝ) : IsCompact (gravChart Ke R c) := by
  set S3 := {z : ℝ × JetM | ∀ s, z.2.1 s ∈ Ke}
  have h3 : IsClosed S3 := isClosed_valsIn hKe.isClosed
  have hbig : IsCompact (Set.Icc 0 R ×ˢ ((Set.univ.pi fun _ : Shift => Ke) ×ˢ
      Metric.closedBall (0 : Diffs) 1)) :=
    isCompact_Icc.prod ((isCompact_univ_pi fun _ => hKe).prod (isCompact_closedBall _ _))
  refine hbig.of_isClosed_subset ?_ ?_
  · have hM : IsClosed (S3 ∩ {z : ℝ × JetM | Margin c z}) := by
      have e : S3 ∩ {z : ℝ × JetM | Margin c z} = ⋂ μ, ⋂ ν,
          ((S3 ∩ (fun z : ℝ × JetM => z.1 * ‖omegaM μ z.2‖) ⁻¹' Set.Iic c) ∩
            (S3 ∩ (fun z : ℝ × JetM => z.1 * ‖omegaShiftM ν μ z.2‖) ⁻¹' Set.Iic c)) := by
        ext z
        simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Margin, Set.mem_iInter,
          Set.mem_preimage, Set.mem_Iic]
        constructor
        · rintro ⟨hz, hm⟩ μ ν; exact ⟨⟨hz, (hm μ ν).1⟩, ⟨hz, (hm μ ν).2⟩⟩
        · intro h
          exact ⟨(h 0 0).1.1, fun μ ν => ⟨(h μ ν).1.2, (h μ ν).2.2⟩⟩
      rw [e]
      refine isClosed_iInter fun μ => isClosed_iInter fun ν => IsClosed.inter ?_ ?_
      · exact (continuous_fst.continuousOn.mul
          (continuousOn_omegaM μ hdet).norm).preimage_isClosed_of_isClosed h3 isClosed_Iic
      · exact (continuous_fst.continuousOn.mul
          (continuousOn_omegaShiftM ν μ hdet).norm).preimage_isClosed_of_isClosed h3 isClosed_Iic
    have hrest : IsClosed {z : ℝ × JetM | 0 ≤ z.1 ∧ z.1 ≤ R ∧ ‖z.2.2‖ ≤ 1 ∧
        ∀ s lam, z.2.1 s + z.1 • z.2.2 (s, lam) ∈ Ke} := by
      have c1 : IsClosed {z : ℝ × JetM | 0 ≤ z.1} := isClosed_le continuous_const continuous_fst
      have c2 : IsClosed {z : ℝ × JetM | z.1 ≤ R} := isClosed_le continuous_fst continuous_const
      have c3 : IsClosed {z : ℝ × JetM | ‖z.2.2‖ ≤ 1} :=
        isClosed_le (f := fun z : ℝ × JetM => ‖z.2.2‖) (by fun_prop) continuous_const
      have c4 : IsClosed {z : ℝ × JetM | ∀ s lam, z.2.1 s + z.1 • z.2.2 (s, lam) ∈ Ke} := by
        simp only [Set.setOf_forall]
        exact isClosed_iInter fun s => isClosed_iInter fun lam => hKe.isClosed.preimage
          (f := fun z : ℝ × JetM => z.2.1 s + z.1 • z.2.2 (s, lam)) (by fun_prop)
      have e : {z : ℝ × JetM | 0 ≤ z.1 ∧ z.1 ≤ R ∧ ‖z.2.2‖ ≤ 1 ∧
          ∀ s lam, z.2.1 s + z.1 • z.2.2 (s, lam) ∈ Ke} =
          {z : ℝ × JetM | 0 ≤ z.1} ∩ ({z | z.1 ≤ R} ∩ ({z | ‖z.2.2‖ ≤ 1} ∩
            {z | ∀ s lam, z.2.1 s + z.1 • z.2.2 (s, lam) ∈ Ke})) := by
        ext z; simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
      rw [e]
      exact c1.inter (c2.inter (c3.inter c4))
    have e : gravChart Ke R c = (S3 ∩ {z : ℝ × JetM | Margin c z}) ∩
        {z : ℝ × JetM | 0 ≤ z.1 ∧ z.1 ≤ R ∧ ‖z.2.2‖ ≤ 1 ∧
          ∀ s lam, z.2.1 s + z.1 • z.2.2 (s, lam) ∈ Ke} := by
      ext z
      simp only [gravChart, Set.mem_inter_iff, Set.mem_setOf_eq, S3]
      tauto
    rw [e]
    exact hM.inter hrest
  · rintro z ⟨h0, hR, hv, hq, -, -⟩
    exact ⟨⟨h0, hR⟩, fun s _ => hv s, mem_closedBall_zero_iff.2 hq⟩

/-- Points of the normalised jet chart are regular points of `gravCurv`. -/
theorem gravRegular_of_mem {Ke : Set Mat} (hdet : ∀ e ∈ Ke, 0 < e.det) {R c : ℝ}
    (hc : c ≤ 1 / 64) {z : ℝ × JetM} (hz : z ∈ gravChart Ke R c) : GravRegular z :=
  ⟨fun s => (hdet _ (hz.2.2.1 s)).ne', fun μ => (hdet _ (hz.2.2.2.2.1 _ μ)).ne',
    fun μ ν => norm_plaqDev_lt_of_margin hc hz.1 hz.2.2.2.2.2 μ ν⟩

theorem contDiffAt_of_mem_gravChart (κ : ℝ) {Ke : Set Mat} (hdet : ∀ e ∈ Ke, 0 < e.det)
    {R c : ℝ} (hc : c ≤ 1 / 64) {z : ℝ × JetM} (hz : z ∈ gravChart Ke R c) :
    ContDiffAt ℝ 1 (gravCurv κ) z :=
  (contDiffAt_gravCurv κ (gravRegular_of_mem hdet hc hz)).of_le (by exact_mod_cast le_top)

/-! ### The continuum first-order Palatini density -/

/-- The constant jet `(e at every shift, p_λ at every shift)` of a continuum first jet. -/
def constJet (e : Mat) (p : Fin 4 → Mat) : JetM := (fun _ => e, fun sl => p sl.2)

/-- **The continuum first-order gravitational density** `L^{(1)}(e, ∂e)` (`eq:palatini-first-order`):
the `h → 0` value of the shifted first-jet density at the constant jet. -/
def palatiniFirstOrder (κ Λ : ℝ) (e : Mat) (p : Fin 4 → Mat) : ℝ :=
  gravCurv κ (0, constJet e p) - Λ / κ * volume e

theorem omegaShiftM_constJet (ν μ : Fin 4) (e : Mat) (p : Fin 4 → Mat) :
    omegaShiftM ν μ (constJet e p) = omegaM ν (constJet e p) := rfl

/-- The Cartan remainder at the mesh origin and the constant jet is the commutator. -/
theorem remM_constJet (μ ν : Fin 4) (e : Mat) (p : Fin 4 → Mat) :
    remM μ ν (0, constJet e p) =
      matToOp (readerOmega e p μ * readerOmega e p ν - readerOmega e p ν * readerOmega e p μ) := by
  rw [remM_eq]
  unfold slots
  simp only [omegaShiftM_constJet, sub_self, map_zero, map_sub, map_mul]
  have h : ∀ X Y : Op, remPlaquette ((0 : ℝ), X, Y, (0 : Op), (0 : Op)) = X * Y - Y * X :=
    fun X Y => remPlaquette_zero_comm X Y
  exact h _ _

/-- `dqPal(0; e, p) = D_e C(e)[p]`: the divided Palatini difference at `h = 0` is the derivative
of the antisymmetrised Palatini coefficient. -/
theorem hasDerivAt_palA (κ : ℝ) {e : Mat} (he : 0 < e.det) (p : Mat) (μ ν a b : Fin 4) :
    HasDerivAt (fun t : ℝ => palA κ (e + t • p) μ ν a b) (dqPal κ 0 e p μ ν a b) 0 := by
  have hc : ContinuousAt (fun t : ℝ => (e + t • p).det) 0 := by fun_prop
  have hpos : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < (e + t • p).det := by
    have := hc.eventually (lt_mem_nhds (show (0 : ℝ) < (e + (0 : ℝ) • p).det by simpa using he))
    exact this
  have hdq : ContinuousAt (fun t : ℝ => dqPal κ t e p μ ν a b) 0 := by
    have h := contDiffAt_dqPal κ μ ν a b (q := ((0 : ℝ), e, p)) he.ne' (by simpa using he.ne')
    exact (h.continuousAt.comp (f := fun t : ℝ => (t, e, p)) (by fun_prop))
  rw [hasDerivAt_iff_tendsto_slope]
  refine (hdq.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds hpos] with t ht htp
  rw [slope_def_field, sub_zero, zero_smul, add_zero]
  have := smul_dqPal_eq κ t e p he htp μ ν a b
  rw [← this]
  field_simp [show t ≠ 0 from ht]

/-- **Identification of the continuum first-order density** with the Palatini representative
`-dB ∧ ω + B ∧ ω ∧ ω - (Λ/κ) v` in coordinates: with `ω_μ = Ω_μ(e, p)`,
`L^{(1)}(e, p) = Σ pal(e)^{μν}_{ab} [ω_μ, ω_ν]^a_b - Σ (∂_t C^{μν}(e + t p_μ)|₀)_{ab} ω_ν^{ab}
 - (Λ/κ) v(e)`. -/
theorem palatiniFirstOrder_eq (κ Λ : ℝ) {e : Mat} (he : 0 < e.det) (p : Fin 4 → Mat) :
    palatiniFirstOrder κ Λ e p =
      (∑ μ, ∑ ν, ∑ a, ∑ b, pal κ e μ ν a b *
        (readerOmega e p μ * readerOmega e p ν - readerOmega e p ν * readerOmega e p μ) a b) -
      (∑ μ, ∑ ν, ∑ a, ∑ b, deriv (fun t : ℝ => palA κ (e + t • p μ) μ ν a b) 0 *
        readerOmega e p ν a b) - Λ / κ * volume e := by
  unfold palatiniFirstOrder gravCurv
  have h1 : ∀ μ ν a b, opEntry (antisym (fun μ ν => remM μ ν (0, constJet e p)) μ ν) a b =
      (readerOmega e p μ * readerOmega e p ν - readerOmega e p ν * readerOmega e p μ) a b := by
    intro μ ν a b
    simp only [remM_constJet]
    rw [antisym_eq_self (fun μ ν => matToOp (readerOmega e p μ * readerOmega e p ν -
      readerOmega e p ν * readerOmega e p μ)) (fun μ ν => by rw [← map_neg, neg_sub]),
      opEntry_matToOp]
  have h2 : ∀ μ ν a b, dqPal κ 0 (emM μ (constJet e p)) (pmM μ (constJet e p)) μ ν a b =
      deriv (fun t : ℝ => palA κ (e + t • p μ) μ ν a b) 0 :=
    fun μ ν a b => (hasDerivAt_palA κ he (p μ) μ ν a b).deriv.symm
  simp only [h1, h2]
  rfl

end

end RenewalGeometry.NativeGravityJet
