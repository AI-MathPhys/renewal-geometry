/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.MatrixSpectralDecay

/-!
# Rapid Lyapunov growth, slow scalar growth and the two residence precision scales
  (`prop:supp-exact-normal-growth`, `thm:main-exact-residence`; emergent-spacetime manuscript)

The normal-factor certificate `ass:supp-exact-normal` enters as hypotheses (the ledger
convention for that assumption: its formal counterparts are the hypothesis arguments of the
theorems referencing it):

* **(N1)** in rapid time `s = t/a³` the eleven-component normal `v` solves `v' = N(s) v` with
  `‖N(s) - J_u‖ ≤ ε` along the history (here `N(s) = N_a(u(s), n(s))`), where the real matrix
  `J_u` has complex spectrum in the open right half-plane, and the smallness `ε` is the one
  produced below ("sufficiently small");
* **(N2)** in slow time `τ = t/a` the scalar normal solves `ω_τ = (λ₊(a) + r(τ)) ω` with
  `λ₊(a) = γ + O(a)` (`|λ₊(a) - γ| ≤ K a` for `0 < a ≤ a₀`), `|r| ≤ γ/4`, `γ > 0`;
* the physical normal displacements are comparable to `a|v|` and `a|ω|` (only the upper
  comparison at the initial cut is used), and residence keeps the terminal normal inside the
  certified chart radius `R`.

Results.

* `exact_normal_rapid_growth`: `c e^{μ_r t/a³} |v(0)| ≤ |v(t)| ≤ C e^{C t/a³} |v(0)|` with
  constants depending only on `J_u` (proved by the Lyapunov form of
  `RenewalGeometry/Analysis/LyapunovExponentialGrowth.lean` and Gelfand decay,
  `RenewalGeometry/Analysis/MatrixSpectralDecay.lean`);
* `exact_normal_slow_growth`: after reducing `a₀`,
  `e^{γ t/(2a)} |ω(0)| ≤ |ω(t)| ≤ e^{2γ t/a} |ω(0)|` (so `μ_s = γ/2`);
* `exact_normal_growth`: the two together (`prop:supp-exact-normal-growth`);
* `exact_rapid_residence_width`, `exact_slow_residence_width`: residence through physical
  time `T` forces `δ_r(0) ≤ C a e^{-μ_r T/a³}` and `δ_s(0) ≤ C a e^{-μ_s T/a}`
  (`eq:main-exact-rapid-width`, `eq:main-exact-slow-width`);
* `residence_width_eventually_lt_pow`: `C a e^{-μ T/a^k} < C₀ a^m` for all small `a > 0`, for
  every algebraic power `a^m` (`k ≥ 1`), so no resident tube has algebraic thickness;
* `main_exact_residence`: the assembled theorem.

The nesting `𝒟_a ⊂ 𝒮_a ⊂ 𝒫_a` and the dimension counts `311, 312, 323` of
`thm:main-exact-residence` are the content of `ass:supp-exact-normal` (the certified graphs) and
of the constraint-leaf chart; they are carried as part of the certificate, not re-derived.
-/

open Set Filter Matrix
open scoped Topology Matrix.Norms.L2Operator

namespace RenewalGeometry

namespace ExactNormalResidence

/-! ### Rapid normal growth -/

/-- **Rapid Lyapunov growth** (first half of `eq:supp-exact-normal-growth`).  For a real matrix
`J` with complex spectrum in the open right half-plane there are `ε, c, C, μ > 0` such that, for
every amplitude `a > 0`, every rapid-time history `v` on `[0, S]` with `v' = N(s) v` and
`‖N(s) - J‖ ≤ ε`, and every physical time `t ∈ [0, a³ S]` (so `s = t/a³`),
`c e^{μ t/a³} ‖v 0‖ ≤ ‖v(t/a³)‖ ≤ C e^{C t/a³} ‖v 0‖`. -/
theorem exact_normal_rapid_growth {k : Type*} [Fintype k] [DecidableEq k] (J : Matrix k k ℝ)
    (hJ : ∀ c ∈ spectrum ℂ (J.map (algebraMap ℝ ℂ)), 0 < c.re) :
    ∃ ε > 0, ∃ c > 0, ∃ C > 0, ∃ μ > 0, ∀ (a S : ℝ) (v : ℝ → EuclideanSpace ℝ k)
      (N : ℝ → Matrix k k ℝ), 0 < a →
      (∀ s ∈ Icc 0 S, HasDerivWithinAt v (toEuclideanCLM (𝕜 := ℝ) (N s) (v s)) (Icc 0 S) s) →
      (∀ s ∈ Icc 0 S, ‖N s - J‖ ≤ ε) →
      ∀ t ∈ Icc 0 (a ^ 3 * S), c * Real.exp (μ * t / a ^ 3) * ‖v 0‖ ≤ ‖v (t / a ^ 3)‖ ∧
        ‖v (t / a ^ 3)‖ ≤ C * Real.exp (C * t / a ^ 3) * ‖v 0‖ := by
  obtain ⟨ε, hε, c, hc, μ, hμ, H⟩ := MatrixSpectralDecay.matrix_lyapunov_exponential_growth J hJ
  refine ⟨ε, hε, c, hc, ‖J‖ + ε + 1, by positivity, μ, hμ, ?_⟩
  intro a S v N ha hv hN t ht
  have ha3 : 0 < a ^ 3 := by positivity
  have hs : t / a ^ 3 ∈ Icc 0 S := by
    refine ⟨div_nonneg ht.1 ha3.le, ?_⟩
    rw [div_le_iff₀ ha3]
    linarith [ht.2]
  obtain ⟨h1, h2⟩ := H S v N hv hN (t / a ^ 3) hs
  refine ⟨by rwa [mul_div_assoc], ?_⟩
  calc ‖v (t / a ^ 3)‖ ≤ Real.exp ((‖J‖ + ε) * (t / a ^ 3)) * ‖v 0‖ := h2
    _ ≤ (‖J‖ + ε + 1) * Real.exp ((‖J‖ + ε + 1) * t / a ^ 3) * ‖v 0‖ := by
      have hs0 : 0 ≤ t / a ^ 3 := hs.1
      have he : Real.exp ((‖J‖ + ε) * (t / a ^ 3)) ≤ Real.exp ((‖J‖ + ε + 1) * t / a ^ 3) := by
        apply Real.exp_le_exp.2
        rw [mul_div_assoc]
        nlinarith
      have hone : 1 ≤ ‖J‖ + ε + 1 := by linarith [norm_nonneg J]
      have hpos : 0 ≤ Real.exp ((‖J‖ + ε + 1) * t / a ^ 3) := (Real.exp_pos _).le
      have hv0 := norm_nonneg (v 0)
      calc Real.exp ((‖J‖ + ε) * (t / a ^ 3)) * ‖v 0‖
          ≤ Real.exp ((‖J‖ + ε + 1) * t / a ^ 3) * ‖v 0‖ := by gcongr
        _ ≤ (‖J‖ + ε + 1) * Real.exp ((‖J‖ + ε + 1) * t / a ^ 3) * ‖v 0‖ := by
          rw [mul_assoc]
          exact le_mul_of_one_le_left (by positivity) hone

/-! ### Slow scalar growth -/

/-- Scalar two-sided exponential bounds for `ω' = ℓ(τ) ω` with `γ/2 ≤ ℓ ≤ 2γ`. -/
theorem scalar_growth_of_rate_bounds {γ S : ℝ} {ω ℓ : ℝ → ℝ}
    (hω : ∀ τ ∈ Icc 0 S, HasDerivWithinAt ω (ℓ τ * ω τ) (Icc 0 S) τ)
    (hℓ : ∀ τ ∈ Icc 0 S, γ / 2 ≤ ℓ τ ∧ ℓ τ ≤ 2 * γ) :
    ∀ τ ∈ Icc 0 S, Real.exp (γ / 2 * τ) * |ω 0| ≤ |ω τ| ∧
      |ω τ| ≤ Real.exp (2 * γ * τ) * |ω 0| := by
  have hf : ∀ τ ∈ Icc 0 S, HasDerivWithinAt (fun τ => ω τ ^ 2) (2 * ℓ τ * ω τ ^ 2)
      (Icc 0 S) τ := by
    intro τ hτ
    have h2 : HasDerivWithinAt (fun x => ω x * ω x)
        (ℓ τ * ω τ * ω τ + ω τ * (ℓ τ * ω τ)) (Icc 0 S) τ := (hω τ hτ).mul (hω τ hτ)
    have h3 : (fun x => ω x ^ 2) = fun x => ω x * ω x := by funext x; ring
    rw [h3]
    convert h2 using 1
    ring
  intro τ hτ
  have hlow := LyapunovGrowth.le_exp_mul_of_hasDerivWithinAt (κ := γ) hf
    (fun τ hτ => by have := (hℓ τ hτ).1; nlinarith [sq_nonneg (ω τ)]) τ hτ
  have hup := LyapunovGrowth.exp_mul_le_of_hasDerivWithinAt (κ := 4 * γ) hf
    (fun τ hτ => by have := (hℓ τ hτ).2; nlinarith [sq_nonneg (ω τ)]) τ hτ
  constructor
  · have hsq : (Real.exp (γ / 2 * τ) * |ω 0|) ^ 2 ≤ |ω τ| ^ 2 := by
      have e : Real.exp (γ / 2 * τ) ^ 2 = Real.exp (γ * τ) := by
        rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
      rw [mul_pow, sq_abs, sq_abs, e]
      exact hlow
    exact le_of_pow_le_pow_left₀ two_ne_zero (abs_nonneg _) hsq
  · have hsq : |ω τ| ^ 2 ≤ (Real.exp (2 * γ * τ) * |ω 0|) ^ 2 := by
      have e : Real.exp (2 * γ * τ) ^ 2 = Real.exp (4 * γ * τ) := by
        rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
      rw [mul_pow, sq_abs, sq_abs, e]
      exact hup
    exact le_of_pow_le_pow_left₀ two_ne_zero (by positivity) hsq

/-- **Slow scalar growth** (second half of `eq:supp-exact-normal-growth`, with `μ_s = γ/2`).
If `λ₊(a) = γ + O(a)` (`|λ₊(a) - γ| ≤ K a` for `0 < a ≤ a₀`), then after reducing `a₀`: for
every slow-time history `ω` with `ω_τ = (λ₊(a) + r(τ)) ω` and `|r| ≤ γ/4` on `[0, S]`, and every
physical time `t ∈ [0, a S]` (so `τ = t/a`),
`e^{(γ/2) t/a} |ω 0| ≤ |ω(t/a)| ≤ e^{2γ t/a} |ω 0|`. -/
theorem exact_normal_slow_growth {γ K a₀ : ℝ} (hγ : 0 < γ) (ha₀ : 0 < a₀) (lam : ℝ → ℝ)
    (hlam : ∀ a, 0 < a → a ≤ a₀ → |lam a - γ| ≤ K * a) :
    ∃ a₁ > 0, ∀ a, 0 < a → a ≤ a₁ → ∀ (S : ℝ) (ω r : ℝ → ℝ),
      (∀ τ ∈ Icc 0 S, HasDerivWithinAt ω ((lam a + r τ) * ω τ) (Icc 0 S) τ) →
      (∀ τ ∈ Icc 0 S, |r τ| ≤ γ / 4) →
      ∀ t ∈ Icc 0 (a * S), Real.exp (γ / 2 * t / a) * |ω 0| ≤ |ω (t / a)| ∧
        |ω (t / a)| ≤ Real.exp (2 * γ * t / a) * |ω 0| := by
  refine ⟨min a₀ (γ / (4 * (|K| + 1))), lt_min ha₀ (by positivity), ?_⟩
  intro a ha ha₁ S ω r hω hr t ht
  have haa₀ : a ≤ a₀ := ha₁.trans (min_le_left _ _)
  have hKa : |lam a - γ| ≤ γ / 4 := by
    have h1 := hlam a ha haa₀
    have h2 : a ≤ γ / (4 * (|K| + 1)) := ha₁.trans (min_le_right _ _)
    have h3 : K * a ≤ |K| * a := mul_le_mul_of_nonneg_right (le_abs_self K) ha.le
    have h4 : |K| * a ≤ γ / 4 := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 4 * (|K| + 1))] at h2
      nlinarith [abs_nonneg K]
    linarith
  have hτ : t / a ∈ Icc 0 S := by
    refine ⟨div_nonneg ht.1 ha.le, ?_⟩
    rw [div_le_iff₀ ha]
    linarith [ht.2]
  have hrate : ∀ τ ∈ Icc 0 S, γ / 2 ≤ lam a + r τ ∧ lam a + r τ ≤ 2 * γ := by
    intro τ hτ
    have := abs_le.1 (hr τ hτ)
    have := abs_le.1 hKa
    constructor <;> linarith
  have := scalar_growth_of_rate_bounds hω hrate (t / a) hτ
  simpa only [mul_div_assoc] using this

/-- **Rapid Lyapunov growth and slow scalar growth** (`prop:supp-exact-normal-growth`).
Under the normal-factor certificate (N1)–(N2) there are constants `ε, c, C, μ_r > 0` (depending
only on `J_u`) and, after reducing `a₀`, the slow rate `μ_s = γ/2`, such that the two-sided
estimates `eq:supp-exact-normal-growth` hold until exit from the chart. -/
theorem exact_normal_growth {k : Type*} [Fintype k] [DecidableEq k] (J : Matrix k k ℝ)
    (hJ : ∀ c ∈ spectrum ℂ (J.map (algebraMap ℝ ℂ)), 0 < c.re)
    {γ K a₀ : ℝ} (hγ : 0 < γ) (ha₀ : 0 < a₀) (lam : ℝ → ℝ)
    (hlam : ∀ a, 0 < a → a ≤ a₀ → |lam a - γ| ≤ K * a) :
    (∃ ε > 0, ∃ c > 0, ∃ C > 0, ∃ μ > 0, ∀ (a S : ℝ) (v : ℝ → EuclideanSpace ℝ k)
      (N : ℝ → Matrix k k ℝ), 0 < a →
      (∀ s ∈ Icc 0 S, HasDerivWithinAt v (toEuclideanCLM (𝕜 := ℝ) (N s) (v s)) (Icc 0 S) s) →
      (∀ s ∈ Icc 0 S, ‖N s - J‖ ≤ ε) →
      ∀ t ∈ Icc 0 (a ^ 3 * S), c * Real.exp (μ * t / a ^ 3) * ‖v 0‖ ≤ ‖v (t / a ^ 3)‖ ∧
        ‖v (t / a ^ 3)‖ ≤ C * Real.exp (C * t / a ^ 3) * ‖v 0‖) ∧
    (∃ a₁ > 0, ∀ a, 0 < a → a ≤ a₁ → ∀ (S : ℝ) (ω r : ℝ → ℝ),
      (∀ τ ∈ Icc 0 S, HasDerivWithinAt ω ((lam a + r τ) * ω τ) (Icc 0 S) τ) →
      (∀ τ ∈ Icc 0 S, |r τ| ≤ γ / 4) →
      ∀ t ∈ Icc 0 (a * S), Real.exp (γ / 2 * t / a) * |ω 0| ≤ |ω (t / a)| ∧
        |ω (t / a)| ≤ Real.exp (2 * γ * t / a) * |ω 0|) :=
  ⟨exact_normal_rapid_growth J hJ, exact_normal_slow_growth hγ ha₀ lam hlam⟩

/-! ### Residence widths -/

/-- **Rapid residence width** (`eq:main-exact-rapid-width`).  There are `ε, μ_r > 0` (from
`J_u`) such that for every comparability constant `K ≥ 0` and chart radius `R ≥ 0` there is
`C ≥ 0` with: if a rapid-time history on `[0, T/a³]` satisfies (N1), its initial physical normal
displacement obeys `δ_r(0) ≤ K a |v(0)|`, and it resides in the chart through physical time
`T` (`|v(T/a³)| ≤ R`), then `δ_r(0) ≤ C a e^{-μ_r T/a³}`. -/
theorem exact_rapid_residence_width {k : Type*} [Fintype k] [DecidableEq k] (J : Matrix k k ℝ)
    (hJ : ∀ c ∈ spectrum ℂ (J.map (algebraMap ℝ ℂ)), 0 < c.re) :
    ∃ ε > 0, ∃ μ > 0, ∀ K R : ℝ, 0 ≤ K → 0 ≤ R → ∃ C ≥ 0, ∀ (a T δ₀ : ℝ)
      (v : ℝ → EuclideanSpace ℝ k) (N : ℝ → Matrix k k ℝ), 0 < a → 0 ≤ T →
      (∀ s ∈ Icc 0 (T / a ^ 3),
        HasDerivWithinAt v (toEuclideanCLM (𝕜 := ℝ) (N s) (v s)) (Icc 0 (T / a ^ 3)) s) →
      (∀ s ∈ Icc 0 (T / a ^ 3), ‖N s - J‖ ≤ ε) →
      δ₀ ≤ K * a * ‖v 0‖ → ‖v (T / a ^ 3)‖ ≤ R →
      δ₀ ≤ C * a * Real.exp (-(μ * T / a ^ 3)) := by
  obtain ⟨ε, hε, c, hc, C', hC', μ, hμ, H⟩ := exact_normal_rapid_growth J hJ
  refine ⟨ε, hε, μ, hμ, fun K R hK hR => ⟨K * R / c, by positivity, ?_⟩⟩
  intro a T δ₀ v N ha hT hv hN hδ hres
  have ha3 : 0 < a ^ 3 := by positivity
  have hTmem : T ∈ Icc 0 (a ^ 3 * (T / a ^ 3)) := by
    rw [mul_div_cancel₀ _ ha3.ne']
    exact ⟨hT, le_rfl⟩
  have hgrow := (H a (T / a ^ 3) v N ha hv hN T hTmem).1
  -- `|v 0| ≤ R e^{-μT/a³} / c`
  have hv0 : ‖v 0‖ ≤ R * Real.exp (-(μ * T / a ^ 3)) / c := by
    rw [le_div_iff₀ hc]
    have he : Real.exp (μ * T / a ^ 3) * Real.exp (-(μ * T / a ^ 3)) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have hpos := Real.exp_pos (-(μ * T / a ^ 3))
    have h1 : c * Real.exp (μ * T / a ^ 3) * ‖v 0‖ ≤ R := hgrow.trans hres
    calc ‖v 0‖ * c = (c * Real.exp (μ * T / a ^ 3) * ‖v 0‖) * Real.exp (-(μ * T / a ^ 3)) := by
          rw [show (c * Real.exp (μ * T / a ^ 3) * ‖v 0‖) * Real.exp (-(μ * T / a ^ 3)) =
            ‖v 0‖ * c * (Real.exp (μ * T / a ^ 3) * Real.exp (-(μ * T / a ^ 3))) by ring, he,
            mul_one]
      _ ≤ R * Real.exp (-(μ * T / a ^ 3)) := by gcongr
  calc δ₀ ≤ K * a * ‖v 0‖ := hδ
    _ ≤ K * a * (R * Real.exp (-(μ * T / a ^ 3)) / c) := by gcongr
    _ = K * R / c * a * Real.exp (-(μ * T / a ^ 3)) := by ring

/-- **Slow residence width** (`eq:main-exact-slow-width`, with `μ_s = γ/2`).  After reducing
`a₀`: if a slow-time history on `[0, T/a]` inside `𝒮_a` satisfies (N2), its initial physical
slow normal obeys `δ_s(0) ≤ K a |ω(0)|`, and it resides in the slow chart through `T`
(`|ω(T/a)| ≤ R`), then `δ_s(0) ≤ K R a e^{-(γ/2) T/a}`.  A smaller available slow radius `R`
only decreases the bound. -/
theorem exact_slow_residence_width {γ K₀ a₀ : ℝ} (hγ : 0 < γ) (ha₀ : 0 < a₀) (lam : ℝ → ℝ)
    (hlam : ∀ a, 0 < a → a ≤ a₀ → |lam a - γ| ≤ K₀ * a) :
    ∃ a₁ > 0, ∀ K R : ℝ, 0 ≤ K → 0 ≤ R → ∀ (a T δ₀ : ℝ) (ω r : ℝ → ℝ), 0 < a → a ≤ a₁ →
      0 ≤ T →
      (∀ τ ∈ Icc 0 (T / a), HasDerivWithinAt ω ((lam a + r τ) * ω τ) (Icc 0 (T / a)) τ) →
      (∀ τ ∈ Icc 0 (T / a), |r τ| ≤ γ / 4) →
      δ₀ ≤ K * a * |ω 0| → |ω (T / a)| ≤ R →
      δ₀ ≤ K * R * a * Real.exp (-(γ / 2 * T / a)) := by
  obtain ⟨a₁, ha₁, H⟩ := exact_normal_slow_growth hγ ha₀ lam hlam
  refine ⟨a₁, ha₁, fun K R hK hR => ?_⟩
  intro a T δ₀ ω r ha haa₁ hT hω hr hδ hres
  have hTmem : T ∈ Icc 0 (a * (T / a)) := by
    rw [mul_div_cancel₀ _ ha.ne']
    exact ⟨hT, le_rfl⟩
  have hgrow := (H a ha haa₁ (T / a) ω r hω hr T hTmem).1
  have hω0 : |ω 0| ≤ R * Real.exp (-(γ / 2 * T / a)) := by
    have he : Real.exp (γ / 2 * T / a) * Real.exp (-(γ / 2 * T / a)) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have h1 : Real.exp (γ / 2 * T / a) * |ω 0| ≤ R := hgrow.trans hres
    calc |ω 0| = (Real.exp (γ / 2 * T / a) * |ω 0|) * Real.exp (-(γ / 2 * T / a)) := by
          rw [mul_comm (Real.exp _), mul_assoc, he, mul_one]
      _ ≤ R * Real.exp (-(γ / 2 * T / a)) := by gcongr
  calc δ₀ ≤ K * a * |ω 0| := hδ
    _ ≤ K * a * (R * Real.exp (-(γ / 2 * T / a))) := by gcongr
    _ = K * R * a * Real.exp (-(γ / 2 * T / a)) := by ring

/-! ### No algebraic thickness -/

theorem tendsto_exp_neg_div_div_pow (b : ℝ) (hb : 0 < b) (m : ℕ) :
    Tendsto (fun a : ℝ => Real.exp (-(b / a)) / a ^ m) (𝓝[>] 0) (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ => x ^ m * Real.exp (-(b * x))) atTop (𝓝 0) := by
    have := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero m).comp
      (tendsto_id.const_mul_atTop hb)
    have h2 := this.const_mul ((b ^ m)⁻¹)
    rw [mul_zero] at h2
    refine h2.congr fun x => ?_
    simp only [Function.comp_apply, id]
    rw [mul_pow, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
  have h3 := h1.comp tendsto_inv_nhdsGT_zero
  refine h3.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with a ha
  simp only [Function.comp_apply, inv_pow]
  rw [div_eq_mul_inv, mul_comm, div_eq_mul_inv]

/-- **No algebraic thickness.**  For `C ≥ 0`, `b > 0`, `k ≥ 1`, every power `m` and every
`C₀ > 0`, the residence width `C a e^{-b/a^k}` is eventually (as `a → 0⁺`) strictly below the
algebraic width `C₀ a^m`. -/
theorem residence_width_eventually_lt_pow {C b C₀ : ℝ} (hb : 0 < b) (hC₀ : 0 < C₀)
    {k : ℕ} (hk : 1 ≤ k) (m : ℕ) :
    ∀ᶠ a in 𝓝[>] (0 : ℝ), C * a * Real.exp (-(b / a ^ k)) < C₀ * a ^ m := by
  have hlim := (tendsto_exp_neg_div_div_pow b hb m).const_mul (|C| + 1)
  rw [mul_zero] at hlim
  have hev := hlim.eventually (gt_mem_nhds hC₀)
  have hsmall : ∀ᶠ a in 𝓝[>] (0 : ℝ), a < 1 :=
    nhdsWithin_le_nhds (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hev, hsmall, self_mem_nhdsWithin] with a h1 h2 h3
  have ha : 0 < a := h3
  have ham : 0 < a ^ m := by positivity
  -- `a^k ≤ a`, hence `e^{-b/a^k} ≤ e^{-b/a}`
  have hak : a ^ k ≤ a := by
    calc a ^ k ≤ a ^ 1 := pow_le_pow_of_le_one ha.le h2.le hk
      _ = a := pow_one a
  have hexp : Real.exp (-(b / a ^ k)) ≤ Real.exp (-(b / a)) := by
    apply Real.exp_le_exp.2
    have : b / a ≤ b / a ^ k := div_le_div_of_nonneg_left hb.le (by positivity) hak
    linarith
  have h1' : (|C| + 1) * Real.exp (-(b / a)) < C₀ * a ^ m := by
    rw [mul_div_assoc'] at h1
    rwa [div_lt_iff₀ ham] at h1
  calc C * a * Real.exp (-(b / a ^ k)) ≤ (|C| + 1) * Real.exp (-(b / a)) := by
        have hCa : C * a ≤ |C| + 1 := by
          calc C * a ≤ |C| * a := mul_le_mul_of_nonneg_right (le_abs_self C) ha.le
            _ ≤ |C| * 1 := by gcongr
            _ ≤ |C| + 1 := by linarith
        have hep := Real.exp_pos (-(b / a ^ k))
        calc C * a * Real.exp (-(b / a ^ k)) ≤ (|C| + 1) * Real.exp (-(b / a ^ k)) := by
              gcongr
          _ ≤ (|C| + 1) * Real.exp (-(b / a)) := by gcongr
    _ < C₀ * a ^ m := h1'

/-- **Two necessary normal precision scales for local residence** (`thm:main-exact-residence`).
Under the normal-factor certificate (N1)–(N2), with initial comparability constant `K` and
chart radii `R_r`, `R_s`:

1. (rapid width) every history resident in the rapid chart through physical time `T` has
   `δ_r(0) ≤ C_r a e^{-μ_r T/a³}`;
2. (slow width) every history in `𝒮_a` resident in the slow chart through `T` has
   `δ_s(0) ≤ C_s a e^{-μ_s T/a}` with `μ_s = γ/2`, for `a ≤ a₁`;
3. (no algebraic thickness) for `T > 0`, every power `m` and `C₀ > 0`, both widths are
   eventually (`a → 0⁺`) strictly below `C₀ a^m`, so no tube of resident histories has
   algebraic thickness in either normal sector.

The constants are fixed-cutoff constants (independent of `a`, `T` and the history). -/
theorem main_exact_residence {k : Type*} [Fintype k] [DecidableEq k] (J : Matrix k k ℝ)
    (hJ : ∀ c ∈ spectrum ℂ (J.map (algebraMap ℝ ℂ)), 0 < c.re)
    {γ K₀ a₀ : ℝ} (hγ : 0 < γ) (ha₀ : 0 < a₀) (lam : ℝ → ℝ)
    (hlam : ∀ a, 0 < a → a ≤ a₀ → |lam a - γ| ≤ K₀ * a) (K R_r R_s : ℝ) (hK : 0 ≤ K)
    (hR_r : 0 ≤ R_r) (hR_s : 0 ≤ R_s) :
    ∃ ε > 0, ∃ μ_r > 0, ∃ C_r ≥ 0, ∃ a₁ > 0, ∃ C_s ≥ 0,
      (∀ (a T δ₀ : ℝ) (v : ℝ → EuclideanSpace ℝ k) (N : ℝ → Matrix k k ℝ), 0 < a → 0 ≤ T →
        (∀ s ∈ Icc 0 (T / a ^ 3),
          HasDerivWithinAt v (toEuclideanCLM (𝕜 := ℝ) (N s) (v s)) (Icc 0 (T / a ^ 3)) s) →
        (∀ s ∈ Icc 0 (T / a ^ 3), ‖N s - J‖ ≤ ε) →
        δ₀ ≤ K * a * ‖v 0‖ → ‖v (T / a ^ 3)‖ ≤ R_r →
        δ₀ ≤ C_r * a * Real.exp (-(μ_r * T / a ^ 3))) ∧
      (∀ (a T δ₀ : ℝ) (ω r : ℝ → ℝ), 0 < a → a ≤ a₁ → 0 ≤ T →
        (∀ τ ∈ Icc 0 (T / a), HasDerivWithinAt ω ((lam a + r τ) * ω τ) (Icc 0 (T / a)) τ) →
        (∀ τ ∈ Icc 0 (T / a), |r τ| ≤ γ / 4) →
        δ₀ ≤ K * a * |ω 0| → |ω (T / a)| ≤ R_s →
        δ₀ ≤ C_s * a * Real.exp (-(γ / 2 * T / a))) ∧
      (∀ T > 0, ∀ (m : ℕ) (C₀ : ℝ), 0 < C₀ →
        (∀ᶠ a in 𝓝[>] (0 : ℝ), C_r * a * Real.exp (-(μ_r * T / a ^ 3)) < C₀ * a ^ m) ∧
        (∀ᶠ a in 𝓝[>] (0 : ℝ), C_s * a * Real.exp (-(γ / 2 * T / a)) < C₀ * a ^ m)) := by
  obtain ⟨ε, hε, μ, hμ, Hr⟩ := exact_rapid_residence_width J hJ
  obtain ⟨C_r, hC_r, Hr'⟩ := Hr K R_r hK hR_r
  obtain ⟨a₁, ha₁, Hs⟩ := exact_slow_residence_width hγ ha₀ lam hlam
  refine ⟨ε, hε, μ, hμ, C_r, hC_r, a₁, ha₁, K * R_s, by positivity, Hr', Hs K R_s hK hR_s,
    fun T hT m C₀ hC₀ => ⟨?_, ?_⟩⟩
  · have := residence_width_eventually_lt_pow (C := C_r) (b := μ * T) (by positivity) hC₀
      (k := 3) (by norm_num) m
    simpa only [mul_div_assoc] using this
  · have h2 := residence_width_eventually_lt_pow (C := K * R_s) (b := γ / 2 * T)
      (by positivity) hC₀ (k := 1) le_rfl m
    simpa only [pow_one, mul_div_assoc] using h2

/-! ### Non-vacuity -/

/-- The identity matrix has spectrum `{1}` in the open right half-plane, so the spectral
hypothesis of (N1) is satisfiable. -/
example : ∀ c ∈ spectrum ℂ ((1 : Matrix (Fin 2) (Fin 2) ℝ).map (algebraMap ℝ ℂ)), 0 < c.re := by
  intro c hc
  rw [Matrix.map_one _ (map_zero _) (map_one _), spectrum.one_eq] at hc
  rw [Set.mem_singleton_iff.1 hc]
  norm_num

/-- The slow factor hypotheses are satisfiable: `ω(τ) = e^{γτ}` with `λ₊ ≡ γ`, `r ≡ 0`. -/
example (γ S : ℝ) : ∀ τ ∈ Icc 0 S, HasDerivWithinAt (fun τ => Real.exp (γ * τ))
    (((fun _ : ℝ => γ) 1 + (fun _ : ℝ => (0 : ℝ)) τ) * Real.exp (γ * τ)) (Icc 0 S) τ := by
  intro τ _
  have := ((hasDerivAt_id τ).const_mul γ).exp
  simp only [mul_one, id, add_zero] at this ⊢
  rw [mul_comm]
  exact this.hasDerivWithinAt

end ExactNormalResidence

end RenewalGeometry
