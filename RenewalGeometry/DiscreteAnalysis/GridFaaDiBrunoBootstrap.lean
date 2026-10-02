/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.DiscreteAnalysis.GridFaaDiBrunoHigherOrder

/-!
# The smallness bootstrap for the `C^r_ℓ` global error of characteristic Strang splitting
  (infrastructure for `prop:supp-gowdy-residual-control`, bootstrap branch of
  `eq:supp-gowdy-state-error`; emergent-spacetime supplement)

`SmoothSetup.global_error_crNorm` bounds the `C^r_ℓ` error of numerical histories whose split
steps lie in the `C^r_ℓ` envelope `EnvK r`.  This file removes the envelope hypothesis under
smallness:

* `SmoothSetup.env0_of_near`: if the state is `η`-close (sup norm) to the sampled reference and the
  implicit stages are `ρ`-near-identity, the stages lie in the chart (`3η + 4ρ + 3Dℓ ≤ δ`).
* `CharData.fwdDiff_srcStep_le`: for an implicit-midpoint source step with an `L`-Lipschitz field,
  `‖D₊A‖ ≤ 3‖D₊X‖` and `‖D₊(A - X)‖ ≤ 2σL‖D₊X‖` (`σL ≤ 1`).
* `SmoothSetup.stageCtl` (**stage control**, by induction through the difference-quotient
  prolongation): `C^k_ℓ`-closeness `η` of the state to the reference and `ρ`-near-identity stages
  imply the `C^k_ℓ` envelope `EnvK k` with radius `envR k p`, whenever `SmallK k p η ρ ℓ`; and
  `exists_smallK`: `SmallK` holds for all small `η, ρ, ℓ`.
* `SmoothSetup.global_error_bootstrap` (**continuation argument**): there are a near-identity
  branch radius `ρ_*`, a smallness threshold `ε_*`, `ℓ₀ > 0` and `C` such that every history of
  near-identity split steps with `‖X₀ - 𝖲X_*(τ₀)‖_{r,∞,ℓ} + Σ_k ‖r_k‖_{r,∞,ℓ} ≤ ε_*` stays in the
  envelope on the whole interval (the proved bound keeps the error below the stage-control
  threshold at every step) and obeys
  `‖X_n - 𝖲X_*(τ₀ + nℓ)‖_{r,∞,ℓ} ≤ C (‖X₀ - 𝖲X_*(τ₀)‖_{r,∞,ℓ} + Σ_{k<n} ‖r_k‖_{r,∞,ℓ} + ℓ²)`.
-/

open Set Finset
open scoped BigOperators ContDiff

set_option linter.unusedSectionVars false

namespace RenewalGeometry.GridFaaDiBruno

noncomputable section

open IteratedDerivBounds CharacteristicSplitting

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-! ### Level-one difference bounds of the stages -/

namespace CharData

variable {c : CharData V} {N : ℕ} [NeZero N]

theorem fwdDiff_apply' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (ℓ : ℝ)
    (v : ZMod N → E) (j : ZMod N) :
    PeriodicGridResidual.fwdDiff ℓ v j = ℓ⁻¹ • (v (j + 1) - v j) := rfl

/-- **Level-one difference bounds of an implicit-midpoint source step**: with an `L`-Lipschitz
field on a set containing the midpoints and `σL ≤ 1`, `‖D₊A‖ ≤ 3‖D₊X‖` and
`‖D₊(A - X)‖ ≤ 2σL‖D₊X‖`. -/
theorem fwdDiff_srcStep_le {G : Set V} {L σ ℓ : ℝ} (hℓ : 0 < ℓ)
    (hL : ∀ x ∈ G, ∀ y ∈ G, ‖c.F x - c.F y‖ ≤ L * ‖x - y‖) (hL0 : 0 ≤ L) (hσ : 0 ≤ σ)
    (hσL : σ * L ≤ 1) {X A : CGrid V N} (h : c.IsSrc σ X A) (hm : ∀ j, midA X A j ∈ G) :
    ‖PeriodicGridResidual.fwdDiff ℓ A.site‖ ≤ 3 * ‖PeriodicGridResidual.fwdDiff ℓ X.site‖ ∧
      ‖PeriodicGridResidual.fwdDiff ℓ (A.site - X.site)‖ ≤
        2 * σ * L * ‖PeriodicGridResidual.fwdDiff ℓ X.site‖ := by
  set a := ‖PeriodicGridResidual.fwdDiff ℓ X.site‖
  set b := ‖PeriodicGridResidual.fwdDiff ℓ A.site‖
  have ha : 0 ≤ a := norm_nonneg _
  have hb : 0 ≤ b := norm_nonneg _
  have hinc : ∀ j, A.site j - X.site j = σ • c.F (midA X A j) := by
    intro j; conv_lhs => rw [h.1 j]
    simp [midA]
  have key : ∀ j, ‖PeriodicGridResidual.fwdDiff ℓ (A.site - X.site) j‖ ≤ σ * L * (a + b) / 2 := by
    intro j
    have hX := norm_le_pi_norm (PeriodicGridResidual.fwdDiff ℓ X.site) j
    have hA := norm_le_pi_norm (PeriodicGridResidual.fwdDiff ℓ A.site) j
    rw [fwdDiff_apply'] at hX hA ⊢
    simp only [Pi.sub_apply]
    rw [hinc, hinc, ← smul_sub, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_inv, abs_of_pos hℓ, abs_of_nonneg hσ]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hℓ] at hX hA
    have hmd : midA X A (j + 1) - midA X A j =
        (1 / 2 : ℝ) • ((X.site (j + 1) - X.site j) + (A.site (j + 1) - A.site j)) := by
      simp only [midA]; module
    have hF := hL _ (hm (j + 1)) _ (hm j)
    rw [hmd, norm_smul] at hF
    have h1 : ‖X.site (j + 1) - X.site j‖ ≤ ℓ * a := by
      rw [← mul_le_mul_iff_of_pos_left (inv_pos.2 hℓ)]
      calc ℓ⁻¹ * ‖X.site (j + 1) - X.site j‖ ≤ a := hX
        _ = ℓ⁻¹ * (ℓ * a) := by field_simp
    have h2 : ‖A.site (j + 1) - A.site j‖ ≤ ℓ * b := by
      rw [← mul_le_mul_iff_of_pos_left (inv_pos.2 hℓ)]
      calc ℓ⁻¹ * ‖A.site (j + 1) - A.site j‖ ≤ b := hA
        _ = ℓ⁻¹ * (ℓ * b) := by field_simp
    have h3 := norm_add_le (X.site (j + 1) - X.site j) (A.site (j + 1) - A.site j)
    norm_num at hF
    have hF' : ‖c.F (midA X A (j + 1)) - c.F (midA X A j)‖ ≤ L * (2⁻¹ * (ℓ * a + ℓ * b)) :=
      hF.trans (mul_le_mul_of_nonneg_left (by nlinarith) hL0)
    calc ℓ⁻¹ * (σ * ‖c.F (midA X A (j + 1)) - c.F (midA X A j)‖)
        ≤ ℓ⁻¹ * (σ * (L * (2⁻¹ * (ℓ * a + ℓ * b)))) := by gcongr
      _ = σ * L * (a + b) / 2 := by field_simp
  have hD : ‖PeriodicGridResidual.fwdDiff ℓ (A.site - X.site)‖ ≤ σ * L * (a + b) / 2 :=
    (pi_norm_le_iff_of_nonneg (by positivity)).2 key
  have hsplit : PeriodicGridResidual.fwdDiff ℓ A.site = PeriodicGridResidual.fwdDiff ℓ X.site +
      PeriodicGridResidual.fwdDiff ℓ (A.site - X.site) := by
    rw [← fwdDiff_sub']; abel
  have hb' : b ≤ a + σ * L * (a + b) / 2 := by
    calc b = ‖PeriodicGridResidual.fwdDiff ℓ X.site +
        PeriodicGridResidual.fwdDiff ℓ (A.site - X.site)‖ := by rw [← hsplit]
      _ ≤ a + _ := norm_add_le _ _
      _ ≤ a + σ * L * (a + b) / 2 := by linarith
  have hσL0 : 0 ≤ σ * L := mul_nonneg hσ hL0
  have hb3 : b ≤ 3 * a := by nlinarith
  refine ⟨hb3, hD.trans ?_⟩
  nlinarith

/-- The forward difference of transported sites is the transport of the forward differences;
in particular `‖D₊(TA)‖ ≤ 3 ‖D₊A‖`. -/
theorem norm_fwdDiff_transport_le (hc : c.Proj) {ℓ : ℝ} (hℓ : ℓ ≠ 0) (A : CGrid V N) :
    ‖PeriodicGridResidual.fwdDiff ℓ (c.transport ℓ A).site‖ ≤
      3 * ‖PeriodicGridResidual.fwdDiff ℓ A.site‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  have e := congrArg (fun G : CGrid (V × V) N => (G.site j).2) (prol_transport (c := c) hℓ A)
  simp only [CGrid.prol, prolArr, transport, prol, LinearMap.prodMap_apply, Prod.snd_add] at e
  show ‖PeriodicGridResidual.fwdDiff ℓ
    (fun j => c.Pp (A.site (j + 1)) + c.Pm (A.site (j - 1)) + c.P0 (A.site j)) j‖ ≤ _
  rw [e]
  set w := PeriodicGridResidual.fwdDiff ℓ A.site
  calc ‖c.Pp (w (j + 1)) + c.Pm (w (j - 1)) + c.P0 (w j)‖
      ≤ ‖c.Pp (w (j + 1))‖ + ‖c.Pm (w (j - 1))‖ + ‖c.P0 (w j)‖ := norm_add₃_le
    _ ≤ ‖w‖ + ‖w‖ + ‖w‖ := add_le_add (add_le_add ((hc.norm_Pp _).trans (norm_le_pi_norm w _))
        ((hc.norm_Pm _).trans (norm_le_pi_norm w _))) ((hc.norm_P0 _).trans (norm_le_pi_norm w _))
    _ = 3 * ‖w‖ := by ring

/-- `crNorm k` of a prolonged array is at most `crNorm (k+1)` of the array. -/
theorem crNorm_prolArr_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (ℓ : ℝ) (k : ℕ)
    (v : ZMod N → E) :
    PeriodicGridResidual.crNorm k ℓ (prolArr ℓ v) ≤ PeriodicGridResidual.crNorm (k + 1) ℓ v := by
  refine Finset.sup'_le _ _ fun i hi => ?_
  have hi' : i < k + 1 := mem_range.1 hi
  rw [iterate_fwdDiff_prolArr]
  refine norm_pair_le (Finset.le_sup' (fun i => ‖(PeriodicGridResidual.fwdDiff ℓ)^[i] v‖)
    (mem_range.2 (by omega))) ?_
  rw [← Function.iterate_succ_apply' (PeriodicGridResidual.fwdDiff ℓ)]
  exact Finset.le_sup' (fun i => ‖(PeriodicGridResidual.fwdDiff ℓ)^[i] v‖)
    (mem_range.2 (by omega))

theorem norm_iterate_le_crNorm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ℓ : ℝ}
    {i k : ℕ} (hi : i ≤ k) (v : ZMod N → E) :
    ‖(PeriodicGridResidual.fwdDiff ℓ)^[i] v‖ ≤ PeriodicGridResidual.crNorm k ℓ v :=
  Finset.le_sup' (fun i => ‖(PeriodicGridResidual.fwdDiff ℓ)^[i] v‖)
    (mem_range.2 (Nat.lt_succ_of_le hi))

theorem EnvK.mono_R {k : ℕ} {K : Set V} {R R' ℓ : ℝ} (hR : R ≤ R') {X A B : CGrid V N}
    (h : c.EnvK k K R ℓ X A B) : c.EnvK k K R' ℓ X A B :=
  ⟨h.1, fun i h1 h2 => ⟨(h.2 i h1 h2).1.trans hR, (h.2 i h1 h2).2.1.trans hR,
    (h.2 i h1 h2).2.2.trans hR⟩⟩

/-- **Converse of `envK_prol`**: the envelope of the prolonged step in the prolonged chart gives
the envelope of one more order. -/
theorem envK_of_prol {k : ℕ} {K : Set V} {R R'' ℓ : ℝ} (hℓ : ℓ ≠ 0) {X A B : CGrid V N}
    (h : (c.prol ℓ).EnvK k (SmoothSetup.prolK K R ℓ) R'' ℓ (X.prol ℓ) (A.prol ℓ) (B.prol ℓ)) :
    c.EnvK (k + 1) K (max R R'') ℓ X A B := by
  obtain ⟨h0, hd⟩ := h
  have htr : (c.prol ℓ).transport ℓ (A.prol ℓ) = (c.transport ℓ A).prol ℓ :=
    (prol_transport hℓ A).symm
  -- memberships of the prolonged arrays
  have m1 : ∀ j, prolArr ℓ (midA X A) j ∈ SmoothSetup.prolK K R ℓ := fun j => by
    have := (h0 j).1; rwa [show (1 / 2 : ℝ) • ((X.prol ℓ).site j + (A.prol ℓ).site j) =
      midA (X.prol ℓ) (A.prol ℓ) j from rfl, midA_prol] at this
  have m2 : ∀ j, prolArr ℓ A.site j ∈ SmoothSetup.prolK K R ℓ := fun j => (h0 j).2.1
  have m3 : ∀ j, prolArr ℓ (midA (c.transport ℓ A) B) j ∈ SmoothSetup.prolK K R ℓ := fun j => by
    have := (h0 j).2.2
    rwa [htr, show (1 / 2 : ℝ) • (((c.transport ℓ A).prol ℓ).site j + (B.prol ℓ).site j) =
      midA ((c.transport ℓ A).prol ℓ) (B.prol ℓ) j from rfl, midA_prol] at this
  have d1 : ∀ v : ZMod N → V, (∀ j, prolArr ℓ v j ∈ SmoothSetup.prolK K R ℓ) →
      ‖PeriodicGridResidual.fwdDiff ℓ v‖ ≤ R := fun v hv =>
    (pi_norm_le_iff_of_nonneg ((norm_nonneg _).trans (hv 0).2.2)).2 fun j => (hv j).2.2
  have dk : ∀ v : ZMod N → V, ∀ i, ‖(PeriodicGridResidual.fwdDiff ℓ)^[i] (prolArr ℓ v)‖ ≤ R'' →
      ‖(PeriodicGridResidual.fwdDiff ℓ)^[i + 1] v‖ ≤ R'' := fun v i hv => by
    rw [iterate_fwdDiff_prolArr] at hv
    rw [Function.iterate_succ_apply']
    exact (norm_snd_le_pair _ _).trans hv
  refine ⟨fun j => ⟨(m1 j).1, (m2 j).1, (m3 j).1⟩, fun i hi1 hik => ?_⟩
  rcases Nat.eq_or_lt_of_le hi1 with rfl | hlt
  · exact ⟨(d1 _ m1).trans (le_max_left _ _), (d1 _ m2).trans (le_max_left _ _),
      (d1 _ m3).trans (le_max_left _ _)⟩
  · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    obtain ⟨e1, e2, e3⟩ := hd i' (by omega) (by omega)
    refine ⟨(dk _ i' ?_).trans (le_max_right _ _), (dk _ i' e2).trans (le_max_right _ _),
      (dk _ i' ?_).trans (le_max_right _ _)⟩
    · rwa [midA_prol] at e1
    · rwa [htr, midA_prol] at e3

end CharData

open CharData

/-! ### Thresholds -/

namespace Params

/-- The smallness conditions of stage control at level `k`. -/
def SmallK : ℕ → Params → ℝ → ℝ → ℝ → Prop
  | 0, p, η, ρ, ℓ => 3 * η + 4 * ρ + 3 * p.D * ℓ ≤ p.δ
  | k + 1, p, η, ρ, ℓ => 3 * η + 4 * ρ + 3 * p.D * ℓ ≤ p.δ ∧
      SmallK k p.prol η (ρ + 9 * ℓ * p.M * (p.D + η)) ℓ

/-- The envelope radius produced by stage control at level `k`. -/
def envR : ℕ → Params → ℝ
  | 0, _ => 0
  | k + 1, p => max p.R (envR k p.prol)

theorem SmallK.base {k : ℕ} {p : Params} {η ρ ℓ : ℝ} (h : SmallK k p η ρ ℓ) :
    3 * η + 4 * ρ + 3 * p.D * ℓ ≤ p.δ := by
  cases k with
  | zero => exact h
  | succ k => exact h.1

/-- **The smallness conditions hold for all small `η, ρ, ℓ`.** -/
theorem exists_smallK (k : ℕ) : ∀ {p : Params}, p.Good → ∃ η₀ ρ₀ ℓ₀ : ℝ, 0 < η₀ ∧ 0 < ρ₀ ∧
    0 < ℓ₀ ∧ ∀ η ρ ℓ, 0 ≤ η → η ≤ η₀ → 0 ≤ ρ → ρ ≤ ρ₀ → 0 ≤ ℓ → ℓ ≤ ℓ₀ → SmallK k p η ρ ℓ := by
  have base : ∀ {p : Params}, p.Good → ∀ η ρ ℓ, 0 ≤ η → η ≤ p.δ / 10 → 0 ≤ ρ → ρ ≤ p.δ / 10 →
      0 ≤ ℓ → ℓ ≤ p.δ / (10 * (p.D + 1)) → 3 * η + 4 * ρ + 3 * p.D * ℓ ≤ p.δ := by
    intro p hp η ρ ℓ _ hη _ hρ hℓ0 hℓ
    have hD := hp.D_nonneg
    have hδ := hp.δ_pos
    rw [le_div_iff₀ (by positivity)] at hℓ
    nlinarith
  induction k with
  | zero =>
    intro p hp
    have hD := hp.D_nonneg
    have hδ := hp.δ_pos
    exact ⟨p.δ / 10, p.δ / 10, p.δ / (10 * (p.D + 1)), by positivity, by positivity,
      by positivity, fun η ρ ℓ h1 h2 h3 h4 h5 h6 => base hp η ρ ℓ h1 h2 h3 h4 h5 h6⟩
  | succ k ih =>
    intro p hp
    obtain ⟨η₁, ρ₁, ℓ₁, hη₁, hρ₁, hℓ₁, h1⟩ := ih hp.prol
    have hD := hp.D_nonneg
    have hδ := hp.δ_pos
    have hM := hp.M_nonneg
    set c := 18 * (p.M + 1) * (p.D + 1 + 1)
    have hc : 0 < c := by positivity
    refine ⟨min (p.δ / 10) (min η₁ 1), min (p.δ / 10) (ρ₁ / 2),
      min (p.δ / (10 * (p.D + 1))) (min ℓ₁ (ρ₁ / c)), by positivity, by positivity,
      by positivity, fun η ρ ℓ h0η hη h0ρ hρ h0ℓ hℓ => ⟨?_, ?_⟩⟩
    · exact base hp η ρ ℓ h0η (hη.trans (min_le_left _ _)) h0ρ (hρ.trans (min_le_left _ _)) h0ℓ
        (hℓ.trans (min_le_left _ _))
    · have hη1 : η ≤ η₁ := hη.trans ((min_le_right _ _).trans (min_le_left _ _))
      have hη2 : η ≤ 1 := hη.trans ((min_le_right _ _).trans (min_le_right _ _))
      have hρ1 : ρ ≤ ρ₁ / 2 := hρ.trans (min_le_right _ _)
      have hℓ1 : ℓ ≤ ℓ₁ := hℓ.trans ((min_le_right _ _).trans (min_le_left _ _))
      have hℓc : ℓ ≤ ρ₁ / c := hℓ.trans ((min_le_right _ _).trans (min_le_right _ _))
      refine h1 η _ ℓ h0η hη1 (by positivity) ?_ h0ℓ hℓ1
      rw [le_div_iff₀ hc] at hℓc
      have : 9 * ℓ * p.M * (p.D + η) ≤ ℓ * c / 2 := by
        have : p.M * (p.D + η) ≤ (p.M + 1) * (p.D + 1 + 1) := by nlinarith
        simp only [c]; nlinarith
      linarith

end Params

/-! ### Stage control -/

namespace SmoothSetup

variable {p : Params} (S : SmoothSetup V p) {N : ℕ} [NeZero N]

/-- **Stages of a near-identity split step from a near-reference state lie in the chart.** -/
theorem env0_of_near (hm : 3 ≤ p.m) (τ : ℝ) (hτ : p.t₀ ≤ τ)
    (hτh : τ + 2 * Real.pi / N ≤ p.t₁) (X A B : CGrid V N) {η ρ : ℝ}
    (hX : ∀ j, ‖X.site j - S.Z (τ, GowdyStaggered.sampleAngle N j)‖ ≤ η)
    (hA : ∀ j, ‖A.site j - X.site j‖ ≤ ρ)
    (hB : ∀ j, ‖B.site j - (S.c.transport (2 * Real.pi / N) A).site j‖ ≤ ρ)
    (hsmall : 3 * η + 4 * ρ + 3 * p.D * (2 * Real.pi / N) ≤ p.δ) :
    S.c.Env0 S.K (2 * Real.pi / N) X A B := by
  set ℓ := 2 * Real.pi / N with hℓdef
  have hℓpos : 0 < ℓ := by
    have : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N))
    positivity
  have hρ : 0 ≤ ρ := (norm_nonneg _).trans (hA 0)
  have hη : 0 ≤ η := (norm_nonneg _).trans (hX 0)
  have hD := S.good.D_nonneg
  set T := S.toStrang hm
  have hslab : ∀ θ : ℝ, ((τ, θ) : ℝ × ℝ).1 ∈ Icc p.t₀ p.t₁ := fun θ => ⟨hτ, by
    show τ ≤ p.t₁; linarith⟩
  have hline : ∀ (q v : ℝ × ℝ), q.1 = τ → v.1 = 1 → ‖v‖ ≤ 1 →
      ‖S.Z (q + ℓ • v) - S.Z q‖ ≤ p.D * ℓ := by
    intro q v hq hv hvn
    have hseg : T.SegInSlab q v ℓ :=
      T.segInSlab_of hℓpos.le (by rw [hv]; norm_num) (by rw [hv]) (by rw [hq]; exact hτ)
        (by rw [hq]; exact hτh)
    exact norm_line_sub_le T.Z_smooth hvn hℓpos.le (fun s hs => T.Z_bound1 _ (hseg s hs))
  have hDl : 0 ≤ p.D * ℓ := by positivity
  intro j
  set θ := GowdyStaggered.sampleAngle N j
  set W := S.Z (τ + ℓ, θ)
  have hXj : ‖X.site j - S.Z (τ, θ)‖ ≤ η := hX j
  refine ⟨?_, ?_, ?_⟩
  · apply S.tube _ (hslab θ)
    have e : (1 / 2 : ℝ) • (X.site j + A.site j) - S.Z (τ, θ) =
        (X.site j - S.Z (τ, θ)) + (1 / 2 : ℝ) • (A.site j - X.site j) := by module
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul]
    have := hA j
    norm_num
    linarith
  · apply S.tube _ (hslab θ)
    have e : A.site j - S.Z (τ, θ) = (A.site j - X.site j) + (X.site j - S.Z (τ, θ)) := by abel
    rw [e]
    exact (norm_add_le _ _).trans (by linarith [hA j])
  · have hZp : S.Z (τ, GowdyStaggered.sampleAngle N (j + 1)) = S.Z (τ, θ + ℓ) :=
      GowdyStaggered.sample_succ S.Z S.Z_per N τ j
    have hZm : S.Z (τ, GowdyStaggered.sampleAngle N (j - 1)) = S.Z (τ, θ - ℓ) :=
      GowdyStaggered.sample_pred S.Z S.Z_per N τ j
    have lp := hline (τ, θ + ℓ) (1, -1) rfl rfl (by simp [Prod.norm_def])
    have lm := hline (τ, θ - ℓ) (1, 1) rfl rfl (by simp [Prod.norm_def])
    have l0 := hline (τ, θ) (1, 0) rfl rfl (by simp [Prod.norm_def])
    have e1 : ((τ, θ + ℓ) : ℝ × ℝ) + ℓ • ((1 : ℝ), (-1 : ℝ)) = (τ + ℓ, θ) := by
      refine Prod.ext ?_ ?_ <;> simp
    have e2 : ((τ, θ - ℓ) : ℝ × ℝ) + ℓ • ((1 : ℝ), (1 : ℝ)) = (τ + ℓ, θ) := by
      refine Prod.ext ?_ ?_ <;> simp
    have e3 : ((τ, θ) : ℝ × ℝ) + ℓ • ((1 : ℝ), (0 : ℝ)) = (τ + ℓ, θ) := by
      refine Prod.ext ?_ ?_ <;> simp
    rw [e1] at lp; rw [e2] at lm; rw [e3] at l0
    have near : ∀ k : ZMod N, ∀ q : ℝ × ℝ, S.Z (τ, GowdyStaggered.sampleAngle N k) = S.Z q →
        ‖W - S.Z q‖ ≤ p.D * ℓ → ‖A.site k - W‖ ≤ ρ + η + p.D * ℓ := by
      intro k q hq hW
      have h1 := hA k
      have h2 := hX k
      rw [hq] at h2
      have e : A.site k - W = (A.site k - X.site k) + (X.site k - S.Z q) - (W - S.Z q) := by abel
      rw [e]
      have h3 := norm_add_le (A.site k - X.site k) (X.site k - S.Z q)
      have h4 := norm_sub_le ((A.site k - X.site k) + (X.site k - S.Z q)) (W - S.Z q)
      linarith
    have np := near (j + 1) _ hZp lp
    have nm := near (j - 1) _ hZm lm
    have n0 := near j _ rfl l0
    have hT : ‖(S.c.transport ℓ A).site j - W‖ ≤ 3 * (ρ + η + p.D * ℓ) := by
      have e : (S.c.transport ℓ A).site j - W =
          S.c.Pp (A.site (j + 1) - W) + S.c.Pm (A.site (j - 1) - W) + S.c.P0 (A.site j - W) := by
        have hs := S.proj.sum W
        simp only [CharData.transport, map_sub]
        conv_lhs => rw [← hs]
        abel
      rw [e]
      calc _ ≤ ‖S.c.Pp (A.site (j + 1) - W)‖ + ‖S.c.Pm (A.site (j - 1) - W)‖ +
            ‖S.c.P0 (A.site j - W)‖ := norm_add₃_le
        _ ≤ _ := by linarith [S.proj.norm_Pp (A.site (j + 1) - W),
            S.proj.norm_Pm (A.site (j - 1) - W), S.proj.norm_P0 (A.site j - W)]
    apply S.tube (τ + ℓ, θ) ⟨by show p.t₀ ≤ τ + ℓ; linarith, by show τ + ℓ ≤ p.t₁; linarith⟩
    set TA := (S.c.transport ℓ A).site j
    have e : (1 / 2 : ℝ) • (TA + B.site j) - W = (TA - W) + (1 / 2 : ℝ) • (B.site j - TA) := by
      module
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul]
    have := hB j
    norm_num
    linarith

theorem fwdDiff_sample_le (hm : 1 ≤ p.m) {τ : ℝ} (hτ : τ ∈ Icc p.t₀ p.t₁) (hℓ : 0 < 2 * Real.pi / N) :
    ‖PeriodicGridResidual.fwdDiff (2 * Real.pi / N) (sampleGrid S.Z S.lam N τ).site‖ ≤ p.D := by
  refine (pi_norm_le_iff_of_nonneg S.good.D_nonneg).2 fun j => ?_
  have e : PeriodicGridResidual.fwdDiff (2 * Real.pi / N) (sampleGrid S.Z S.lam N τ).site j =
      thetaQuot (2 * Real.pi / N) S.Z (τ, GowdyStaggered.sampleAngle N j) := by
    simp only [CharData.fwdDiff_apply', sampleGrid, thetaQuot]
    rw [GowdyStaggered.sample_succ S.Z S.Z_per N τ j]
    simp
  rw [e]
  have := norm_iteratedFDeriv_thetaQuot_le S.Z_smooth hℓ 0
    (q := (τ, GowdyStaggered.sampleAngle N j)) fun z hz =>
      S.Z_bd z (by rw [hz]; exact hτ) 1 le_rfl hm
  rwa [norm_iteratedFDeriv_zero] at this

/-- **Stage control.**  If the state is `C^k_ℓ`-close (`η`) to the sampled reference, the
implicit stages are `ρ`-near-identity and `SmallK k p η ρ ℓ` holds, then the split step lies in
the `C^k_ℓ` envelope of radius `envR k p`. -/
theorem stageCtl (k : ℕ) : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {p : Params}
    (S : SmoothSetup V p), 3 + k ≤ p.m → ∀ {N : ℕ} [NeZero N],
    2 * Real.pi / N ≤ Params.step k p → ∀ τ : ℝ, p.t₀ ≤ τ → τ + 2 * Real.pi / N ≤ p.t₁ →
    ∀ X A B : CGrid V N, S.c.IsSplit (2 * Real.pi / N) X A B → ∀ η ρ : ℝ, 0 ≤ η → 0 ≤ ρ →
    Params.SmallK k p η ρ (2 * Real.pi / N) →
    PeriodicGridResidual.crNorm k (2 * Real.pi / N)
      (X.site - (sampleGrid S.Z S.lam N τ).site) ≤ η →
    (∀ j, ‖A.site j - X.site j‖ ≤ ρ) →
    (∀ j, ‖B.site j - (S.c.transport (2 * Real.pi / N) A).site j‖ ≤ ρ) →
    S.c.EnvK k S.K (Params.envR k p) (2 * Real.pi / N) X A B := by
  induction k with
  | zero =>
    intro V _ _ p S hm N _ hN τ hτ hτh X A B _ η ρ _ _ hs hX hA hB
    refine ⟨S.env0_of_near (by omega) τ hτ hτh X A B (fun j => ?_) hA hB hs.base,
      fun i h1 h2 => absurd (h1.trans h2) (by omega)⟩
    exact (norm_le_pi_norm (X.site - (sampleGrid S.Z S.lam N τ).site) j).trans
      ((norm_iterate_le_crNorm (i := 0) le_rfl _).trans hX)
  | succ k ih =>
    intro V _ _ p S hm N _ hN τ hτ hτh X A B hsp η ρ hη hρ hs hX hA hB
    set ℓ := 2 * Real.pi / N with hℓdef
    have hℓ : 0 < ℓ := by
      have : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N))
      positivity
    have hN0 : ℓ ≤ p.step0 := hN.trans (Params.step_le_step0 _ p)
    have hℓ1 : ℓ ≤ 1 := hN0.trans (Params.step0_le_one S.good)
    have hM := S.good.M_nonneg
    have hD := S.good.D_nonneg
    have h3M : 3 * ℓ * p.M ≤ 1 := by
      have h2 : ℓ ≤ 1 / (3 * p.M + 1) := hN0.trans (min_le_right _ _)
      rw [le_div_iff₀ (by positivity)] at h2
      nlinarith
    have hm1 : 1 ≤ p.m := by omega
    -- level zero
    have hX0 : ∀ j, ‖X.site j - S.Z (τ, GowdyStaggered.sampleAngle N j)‖ ≤ η := fun j =>
      (norm_le_pi_norm (X.site - (sampleGrid S.Z S.lam N τ).site) j).trans
        ((norm_iterate_le_crNorm (i := 0) (Nat.zero_le _) _).trans hX)
    have henv0 := S.env0_of_near (by omega) τ hτ hτh X A B hX0 hA hB hs.base
    have hLip : ∀ x ∈ S.K, ∀ y ∈ S.K, ‖S.c.F x - S.c.F y‖ ≤ p.M * ‖x - y‖ :=
      fun x hx y hy => lipschitz_of_derivBound S.UF_open S.UF_convex S.F_bd hm1 (S.K_UF hx)
        (S.K_UF hy)
    have hσ : 0 ≤ ℓ / 2 := by positivity
    have hσL : ℓ / 2 * p.M ≤ 1 := by nlinarith
    obtain ⟨hA3, hAX⟩ := fwdDiff_srcStep_le hℓ hLip hM hσ hσL hsp.1 fun j => (henv0 j).1
    obtain ⟨-, hBT⟩ := fwdDiff_srcStep_le hℓ hLip hM hσ hσL hsp.2 fun j => (henv0 j).2.2
    have hTA := norm_fwdDiff_transport_le S.proj hℓ.ne' A
    -- `‖D₊X‖ ≤ D + η`
    have hDY := S.fwdDiff_sample_le hm1 ⟨hτ, by linarith⟩ hℓ
    have hDXY : ‖PeriodicGridResidual.fwdDiff ℓ (X.site - (sampleGrid S.Z S.lam N τ).site)‖ ≤ η := by
      have h1 := norm_iterate_le_crNorm (ℓ := ℓ) (i := 1) (k := k + 1) (by omega)
        (X.site - (sampleGrid S.Z S.lam N τ).site)
      simp only [Function.iterate_one] at h1
      exact h1.trans hX
    have hDX : ‖PeriodicGridResidual.fwdDiff ℓ X.site‖ ≤ p.D + η := by
      have e : PeriodicGridResidual.fwdDiff ℓ X.site =
          PeriodicGridResidual.fwdDiff ℓ (sampleGrid S.Z S.lam N τ).site +
            PeriodicGridResidual.fwdDiff ℓ (X.site - (sampleGrid S.Z S.lam N τ).site) := by
        rw [← fwdDiff_sub']; abel
      rw [e]; exact (norm_add_le _ _).trans (by linarith)
    set ρ' := ρ + 9 * ℓ * p.M * (p.D + η)
    have hDXn := norm_nonneg (PeriodicGridResidual.fwdDiff ℓ X.site)
    have hA' : ∀ j, ‖(A.prol ℓ).site j - (X.prol ℓ).site j‖ ≤ ρ' := by
      intro j
      have hj : ‖PeriodicGridResidual.fwdDiff ℓ A.site j - PeriodicGridResidual.fwdDiff ℓ X.site j‖
          ≤ ‖PeriodicGridResidual.fwdDiff ℓ (A.site - X.site)‖ := by
        rw [← fwdDiff_sub']
        exact norm_le_pi_norm (PeriodicGridResidual.fwdDiff ℓ A.site -
          PeriodicGridResidual.fwdDiff ℓ X.site) j
      simp only [CGrid.prol, prolArr, Prod.mk_sub_mk, Prod.norm_def]
      refine max_le ((hA j).trans (by
        have : 0 ≤ 9 * ℓ * p.M * (p.D + η) := by positivity
        linarith)) (hj.trans (hAX.trans ?_))
      have : 2 * (ℓ / 2) * p.M * ‖PeriodicGridResidual.fwdDiff ℓ X.site‖ ≤
          ℓ * p.M * (p.D + η) := by
        have := mul_le_mul_of_nonneg_left hDX (by positivity : 0 ≤ ℓ * p.M)
        nlinarith
      have : 0 ≤ ℓ * p.M * (p.D + η) := by positivity
      nlinarith
    have hB' : ∀ j, ‖(B.prol ℓ).site j - ((S.c.prol ℓ).transport ℓ (A.prol ℓ)).site j‖ ≤ ρ' := by
      intro j
      rw [← prol_transport hℓ.ne']
      have hj : ‖PeriodicGridResidual.fwdDiff ℓ B.site j -
          PeriodicGridResidual.fwdDiff ℓ (S.c.transport ℓ A).site j‖
          ≤ ‖PeriodicGridResidual.fwdDiff ℓ (B.site - (S.c.transport ℓ A).site)‖ := by
        rw [← fwdDiff_sub']
        exact norm_le_pi_norm (PeriodicGridResidual.fwdDiff ℓ B.site -
          PeriodicGridResidual.fwdDiff ℓ (S.c.transport ℓ A).site) j
      simp only [CGrid.prol, prolArr, Prod.mk_sub_mk, Prod.norm_def]
      refine max_le ((hB j).trans (by
        have : 0 ≤ 9 * ℓ * p.M * (p.D + η) := by positivity
        linarith)) (hj.trans (hBT.trans ?_))
      have h1 : ‖PeriodicGridResidual.fwdDiff ℓ (S.c.transport ℓ A).site‖ ≤ 9 * (p.D + η) := by
        linarith
      have := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 2 * (ℓ / 2) * p.M)
      nlinarith
    -- the prolonged state is close to the prolonged reference
    have hXp : PeriodicGridResidual.crNorm k ℓ ((X.prol ℓ).site -
        (sampleGrid (S.prol ℓ hℓ hℓ1 hm1).Z (S.prol ℓ hℓ hℓ1 hm1).lam N τ).site) ≤ η := by
      rw [S.sample_prol hℓ hℓ1 hm1]
      show PeriodicGridResidual.crNorm k ℓ (prolArr ℓ X.site -
        prolArr ℓ (sampleGrid S.Z S.lam N τ).site) ≤ η
      rw [prolArr_sub]
      exact (crNorm_prolArr_le ℓ k _).trans hX
    have hm' : 3 + k ≤ p.prol.m := by simp only [Params.prol]; omega
    have h := ih (S.prol ℓ hℓ hℓ1 hm1) hm' (hN.trans (min_le_right _ _)) τ hτ hτh (X.prol ℓ)
      (A.prol ℓ) (B.prol ℓ) (prol_isSplit hℓ.ne' hsp) η ρ' hη (by positivity) hs.2 hXp hA' hB'
    exact envK_of_prol hℓ.ne' h

/-- Enlarging the envelope radius of a smooth setup. -/
def withR (R' : ℝ) (hR : p.R ≤ R') : SmoothSetup V { p with R := R' } where
  c := S.c
  K := S.K
  UF := S.UF
  Ug := S.Ug
  Z := S.Z
  lam := S.lam
  proj := S.proj
  gp_proj := S.gp_proj
  gm_proj := S.gm_proj
  UF_open := S.UF_open
  UF_convex := S.UF_convex
  Ug_open := S.Ug_open
  Ug_convex := S.Ug_convex
  K_convex := S.K_convex
  K_UF := S.K_UF
  K_Ug := S.K_Ug
  Pp_K := S.Pp_K
  Pm_K := S.Pm_K
  F_bd := S.F_bd
  gp_bd := S.gp_bd
  gm_bd := S.gm_bd
  Z_smooth := S.Z_smooth
  lam_smooth := S.lam_smooth
  Z_per := S.Z_per
  lam_per := S.lam_per
  Z_bd := S.Z_bd
  lam_bd := S.lam_bd
  char_plus := S.char_plus
  char_minus := S.char_minus
  char_zero := S.char_zero
  char_lam := S.char_lam
  tube := S.tube
  good := ⟨S.good.δ_pos, S.good.δ_le, S.good.M_nonneg, S.good.D_nonneg, S.good.R_ge.trans hR⟩

end SmoothSetup

/-! ### The continuation argument -/

namespace SmoothSetup

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] {p : Params}
  (S : SmoothSetup V p) {N : ℕ} [NeZero N]

/-- **The `C^r_ℓ` global error under the smallness bootstrap** (no envelope hypothesis): there are
a near-identity branch radius `ρ_* > 0`, a smallness threshold `ε_* > 0`, `ℓ₀ > 0` and `C ≥ 0` such
that for `ℓ = 2π/N ≤ ℓ₀`, `[τ₀, τ₀ + n₀ℓ] ⊆ [t₀, t₁]` and every history of split steps
`X_n → A_n → B_n` whose implicit stages are `ρ_*`-near-identity, if
`‖X₀ - 𝖲X_*(τ₀)‖_{r,∞,ℓ} + Σ_{k<n₀} ‖X_{k+1} - B_k‖_{r,∞,ℓ} ≤ ε_*`, then every step lies in the
`C^r_ℓ` envelope and
`‖X_n - 𝖲X_*(τ₀+nℓ)‖_{r,∞,ℓ} ≤ C (‖X₀ - 𝖲X_*(τ₀)‖_{r,∞,ℓ} + Σ_{k<n} ‖X_{k+1} - B_k‖_{r,∞,ℓ} + ℓ²)`
for all `n ≤ n₀`. -/
theorem global_error_bootstrap (r : ℕ) (hm : 3 + r ≤ p.m) :
    ∃ ρs εs ℓ₀ C : ℝ, 0 < ρs ∧ 0 < εs ∧ 0 < ℓ₀ ∧ 0 ≤ C ∧
      ∀ (N : ℕ) [NeZero N], 2 * Real.pi / N ≤ ℓ₀ →
      ∀ (τ₀ : ℝ) (n₀ : ℕ), p.t₀ ≤ τ₀ → τ₀ + n₀ * (2 * Real.pi / N) ≤ p.t₁ →
      ∀ X A B : ℕ → CGrid V N,
        (∀ n < n₀, S.c.IsSplit (2 * Real.pi / N) (X n) (A n) (B n) ∧
          (∀ j, ‖(A n).site j - (X n).site j‖ ≤ ρs) ∧
          (∀ j, ‖(B n).site j - (S.c.transport (2 * Real.pi / N) (A n)).site j‖ ≤ ρs)) →
        PeriodicGridResidual.crNorm r (2 * Real.pi / N)
            (errA (X 0) (sampleGrid S.Z S.lam N τ₀)) +
          ∑ i ∈ range n₀, PeriodicGridResidual.crNorm r (2 * Real.pi / N)
            (errA (X (i + 1)) (B i)) ≤ εs →
        (∀ n < n₀, S.c.EnvK r S.K (max p.R (Params.envR r p)) (2 * Real.pi / N)
          (X n) (A n) (B n)) ∧
        ∀ n ≤ n₀, PeriodicGridResidual.crNorm r (2 * Real.pi / N)
            (errA (X n) (sampleGrid S.Z S.lam N (τ₀ + n * (2 * Real.pi / N)))) ≤
          C * (PeriodicGridResidual.crNorm r (2 * Real.pi / N)
              (errA (X 0) (sampleGrid S.Z S.lam N τ₀)) +
            ∑ i ∈ range n, PeriodicGridResidual.crNorm r (2 * Real.pi / N)
              (errA (X (i + 1)) (B i)) + (2 * Real.pi / N) ^ 2) := by
  set R₁ := max p.R (Params.envR r p)
  set p₁ : Params := { p with R := R₁ }
  obtain ⟨S₁, hS₁c, hS₁K, hS₁Z, hS₁l⟩ : ∃ S₁ : SmoothSetup V p₁, S₁.c = S.c ∧ S₁.K = S.K ∧
      S₁.Z = S.Z ∧ S₁.lam = S.lam := ⟨S.withR R₁ (le_max_left _ _), rfl, rfl, rfl, rfl⟩
  have hgood₁ : p₁.Good := S₁.good
  obtain ⟨η₀, ρ₀, ℓs, hη₀, hρ₀, hℓs, hsmall⟩ := Params.exists_smallK r S.good
  set T := max (p.t₁ - p.t₀) 0
  have hT0 : 0 ≤ T := le_max_right _ _
  set K := rateR r p₁
  set Cc := consR r p₁
  have hK : 0 ≤ K := Finset.sum_nonneg fun k _ => Params.rate_nonneg hgood₁ k
  have hCc : 0 ≤ Cc := Finset.sum_nonneg fun k _ => Params.cons_nonneg hgood₁ k
  set E := Real.exp (K * T)
  have hE : 0 < E := Real.exp_pos _
  set εs := η₀ / (6 * E)
  have hεs : 0 < εs := by positivity
  set ℓ₀ := min (min (Params.step r p₁) (Params.step r p)) (min ℓs (min 1 (η₀ / (6 * (Cc * T + 1) * E))))
  have hℓ₀ : 0 < ℓ₀ := lt_min (lt_min (Params.step_pos hgood₁ r) (Params.step_pos S.good r))
    (lt_min hℓs (lt_min one_pos (by positivity)))
  refine ⟨ρ₀, εs, ℓ₀, 3 * (1 + Cc * T) * E, hρ₀, hεs, hℓ₀, by positivity, ?_⟩
  intro N _ hN τ₀ n₀ hτ₀ hn₀ X A B hst hsm
  set ℓ := 2 * Real.pi / N with hℓdef
  have hℓpos : 0 < ℓ := by
    have : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N))
    positivity
  have hN1 : ℓ ≤ Params.step r p₁ := hN.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hN2 : ℓ ≤ Params.step r p := hN.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hNs : ℓ ≤ ℓs := hN.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hNl1 : ℓ ≤ 1 := hN.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    (min_le_left _ _)))
  have hNl2 : ℓ ≤ η₀ / (6 * (Cc * T + 1) * E) := hN.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  have hT : p.t₁ - p.t₀ ≤ T := le_max_left _ _
  have hTn : 0 ≤ p.t₁ - p.t₀ := by
    have : 0 ≤ (n₀ : ℝ) * ℓ := by positivity
    linarith
  -- the global bound for histories in the envelope up to step `n`
  have hglob : ∀ n ≤ n₀, (∀ m < n, S.c.EnvK r S.K R₁ ℓ (X m) (A m) (B m)) →
      PeriodicGridResidual.crNorm r ℓ (errA (X n) (sampleGrid S.Z S.lam N (τ₀ + n * ℓ))) ≤
        3 * ((PeriodicGridResidual.crNorm r ℓ (errA (X 0) (sampleGrid S.Z S.lam N τ₀)) +
          ∑ i ∈ range n, PeriodicGridResidual.crNorm r ℓ (errA (X (i + 1)) (B i)) +
          Cc * (p.t₁ - p.t₀) * ℓ ^ 2) * Real.exp (K * (p.t₁ - p.t₀))) := by
    intro n hn henv
    have hn₀' : τ₀ + n * ℓ ≤ p.t₁ := by
      have : (n : ℝ) * ℓ ≤ n₀ * ℓ :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hn) hℓpos.le
      linarith
    have h := S₁.global_error_crNorm r hm hN1 τ₀ n hτ₀ hn₀' X A B
      (fun m hm' => by
        rw [hS₁c, hS₁K]
        exact ⟨(hst m (lt_of_lt_of_le hm' hn)).1, henv m hm'⟩) n le_rfl
    rw [hS₁Z, hS₁l] at h
    exact h
  -- the bound stays below the stage-control threshold
  have hsmallbd : ∀ n ≤ n₀, 3 * ((PeriodicGridResidual.crNorm r ℓ
      (errA (X 0) (sampleGrid S.Z S.lam N τ₀)) +
      ∑ i ∈ range n, PeriodicGridResidual.crNorm r ℓ (errA (X (i + 1)) (B i)) +
      Cc * (p.t₁ - p.t₀) * ℓ ^ 2) * Real.exp (K * (p.t₁ - p.t₀))) ≤ η₀ := by
    intro n hn
    have hsum : ∑ i ∈ range n, PeriodicGridResidual.crNorm r ℓ (errA (X (i + 1)) (B i)) ≤
        ∑ i ∈ range n₀, PeriodicGridResidual.crNorm r ℓ (errA (X (i + 1)) (B i)) :=
      Finset.sum_le_sum_of_subset_of_nonneg (range_subset_range.2 hn)
        fun i _ _ => PeriodicGridResidual.crNorm_nonneg _ _ _
    have hexp : Real.exp (K * (p.t₁ - p.t₀)) ≤ E :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hT hK)
    have hℓ2 : Cc * (p.t₁ - p.t₀) * ℓ ^ 2 ≤ η₀ / (6 * E) := by
      have h1 : Cc * (p.t₁ - p.t₀) * ℓ ^ 2 ≤ (Cc * T + 1) * ℓ := by
        have : ℓ ^ 2 ≤ ℓ := by nlinarith
        have : Cc * (p.t₁ - p.t₀) ≤ Cc * T := mul_le_mul_of_nonneg_left hT hCc
        nlinarith [mul_nonneg hCc hTn]
      have h2 : (Cc * T + 1) * ℓ ≤ η₀ / (6 * E) := by
        rw [le_div_iff₀ (by positivity)] at hNl2
        rw [le_div_iff₀ (by positivity)]
        nlinarith
      linarith
    have he0 := PeriodicGridResidual.crNorm_nonneg r ℓ (errA (X 0) (sampleGrid S.Z S.lam N τ₀))
    have hs0 : 0 ≤ ∑ i ∈ range n, PeriodicGridResidual.crNorm r ℓ (errA (X (i + 1)) (B i)) :=
      Finset.sum_nonneg fun i _ => PeriodicGridResidual.crNorm_nonneg _ _ _
    have hin : PeriodicGridResidual.crNorm r ℓ (errA (X 0) (sampleGrid S.Z S.lam N τ₀)) +
        ∑ i ∈ range n, PeriodicGridResidual.crNorm r ℓ (errA (X (i + 1)) (B i)) +
        Cc * (p.t₁ - p.t₀) * ℓ ^ 2 ≤ 2 * (η₀ / (6 * E)) := by linarith
    have hpos : 0 ≤ PeriodicGridResidual.crNorm r ℓ (errA (X 0) (sampleGrid S.Z S.lam N τ₀)) +
        ∑ i ∈ range n, PeriodicGridResidual.crNorm r ℓ (errA (X (i + 1)) (B i)) +
        Cc * (p.t₁ - p.t₀) * ℓ ^ 2 := by
      have : 0 ≤ Cc * (p.t₁ - p.t₀) * ℓ ^ 2 := by positivity
      linarith
    calc _ ≤ 3 * ((2 * (η₀ / (6 * E))) * E) := by gcongr
      _ = η₀ := by field_simp; ring
  -- continuation: every step lies in the envelope
  have hcont : ∀ n ≤ n₀, ∀ m < n, S.c.EnvK r S.K R₁ ℓ (X m) (A m) (B m) := by
    intro n
    induction n with
    | zero => intro _ m hm'; exact absurd hm' (Nat.not_lt_zero _)
    | succ n ih =>
      intro hn m hm'
      have ih' := ih (by omega)
      rcases Nat.lt_succ_iff_lt_or_eq.1 hm' with h | rfl
      · exact ih' m h
      · have hb := (hglob m (by omega) ih').trans (hsmallbd m (by omega))
        have hτm : p.t₀ ≤ τ₀ + m * ℓ := by
          have : 0 ≤ (m : ℝ) * ℓ := by positivity
          linarith
        have hτh : τ₀ + m * ℓ + ℓ ≤ p.t₁ := by
          have : ((m + 1 : ℕ) : ℝ) * ℓ ≤ n₀ * ℓ :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast hn) hℓpos.le
          push_cast at this
          linarith
        have hηsite : PeriodicGridResidual.crNorm r ℓ
            ((X m).site - (sampleGrid S.Z S.lam N (τ₀ + m * ℓ)).site) ≤ η₀ := by
          refine le_trans (Finset.sup'_le _ _ fun i hi => ?_) hb
          have := iterate_fwdDiff_errA ℓ i (X m) (sampleGrid S.Z S.lam N (τ₀ + m * ℓ))
          refine le_trans ?_ (Finset.le_sup' (fun i =>
            ‖(PeriodicGridResidual.fwdDiff ℓ)^[i] (errA (X m)
              (sampleGrid S.Z S.lam N (τ₀ + m * ℓ)))‖) hi)
          rw [this]
          exact norm_fst_le_pair _ _
        have hc := S.stageCtl r hm hN2 (τ₀ + m * ℓ) hτm hτh (X m) (A m) (B m)
          (hst m (by omega)).1 η₀ ρ₀ hη₀.le hρ₀.le
          (hsmall η₀ ρ₀ ℓ hη₀.le le_rfl hρ₀.le le_rfl hℓpos.le hNs) hηsite
          (fun j => (hst m (by omega)).2.1 j) (fun j => (hst m (by omega)).2.2 j)
        exact hc.mono_R (le_max_right _ _)
  have henvall := hcont n₀ le_rfl
  refine ⟨henvall, fun n hn => ?_⟩
  have h := hglob n hn fun m hm' => henvall m (lt_of_lt_of_le hm' hn)
  refine h.trans ?_
  set e0 := PeriodicGridResidual.crNorm r ℓ (errA (X 0) (sampleGrid S.Z S.lam N τ₀))
  set sr := ∑ i ∈ range n, PeriodicGridResidual.crNorm r ℓ (errA (X (i + 1)) (B i))
  have he0 : 0 ≤ e0 := PeriodicGridResidual.crNorm_nonneg _ _ _
  have hsr : 0 ≤ sr := Finset.sum_nonneg fun i _ => PeriodicGridResidual.crNorm_nonneg _ _ _
  have hexp : Real.exp (K * (p.t₁ - p.t₀)) ≤ E :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hT hK)
  have hin : e0 + sr + Cc * (p.t₁ - p.t₀) * ℓ ^ 2 ≤ (1 + Cc * T) * (e0 + sr + ℓ ^ 2) := by
    have h1 : Cc * (p.t₁ - p.t₀) * ℓ ^ 2 ≤ Cc * T * ℓ ^ 2 := by gcongr
    have h2 : 0 ≤ Cc * T := mul_nonneg hCc hT0
    nlinarith [sq_nonneg ℓ, mul_nonneg h2 he0, mul_nonneg h2 hsr]
  have hb0 : 0 ≤ (1 + Cc * T) * (e0 + sr + ℓ ^ 2) :=
    mul_nonneg (add_nonneg zero_le_one (mul_nonneg hCc hT0))
      (add_nonneg (add_nonneg he0 hsr) (sq_nonneg _))
  calc 3 * ((e0 + sr + Cc * (p.t₁ - p.t₀) * ℓ ^ 2) * Real.exp (K * (p.t₁ - p.t₀)))
      ≤ 3 * (((1 + Cc * T) * (e0 + sr + ℓ ^ 2)) * E) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hin hexp (Real.exp_pos _).le hb0) (by norm_num)
    _ = 3 * (1 + Cc * T) * E * (e0 + sr + ℓ ^ 2) := by ring

end SmoothSetup

end

end RenewalGeometry.GridFaaDiBruno
