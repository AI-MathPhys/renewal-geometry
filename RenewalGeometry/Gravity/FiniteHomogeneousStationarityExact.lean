/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Finite stationary classification and de Sitter convergence
(`thm:main-finite-homogeneous-stationarity`, `eq:main-discrete-homogeneous-action`,
`eq:main-discrete-lapse-constraint`, `eq:main-discrete-scale-euler`,
`eq:main-finite-stationary-recurrence`, `eq:main-finite-profile-convergence`;
emergent-spacetime manuscript)

The finite lapse-varied homogeneous action is
`S_d(q,s) = −Σ_{j<M} [A₀ (q_{j+1} − q_j)²/s_j + B₀ s_j q̄_j²]`, `q̄_j = (q_j+q_{j+1})/2`
(`discreteAction`), with `A₀ = 8/3`, `B₀ = 2Λ`.

* `hasDerivAt_discreteAction_lapse`: the partial derivative of `S_d` in the
  lapse-weighted interval `s_j` (`j < M`) is `A₀ v_j² − B₀ q̄_j²`
  (**`eq:main-discrete-lapse-constraint`**, `v_j = (q_{j+1} − q_j)/s_j`);
* `hasDerivAt_discreteAction_scale`: the partial derivative in the interior node
  `q_j` (`1 ≤ j < M`) is `2A₀(v_j − v_{j−1}) − B₀(s_{j−1} q̄_{j−1} + s_j q̄_j)`
  (**`eq:main-discrete-scale-euler`**); endpoints `q_0, q_M` are held fixed;
* `stationary_recurrence_of_pos`: for `A₀, B₀ > 0`, `ω = √(B₀/A₀)`, every positive
  stationary path has one common sign `σ ∈ {±1}` with
  `q_{j+1} = q_j (1 + σωs_j/2)/(1 − σωs_j/2)` and `0 < ωs_j/2 < 1`
  (**`eq:main-finite-stationary-recurrence`**);
* `stationary_of_recurrence`: conversely every common-sign recurrence is a positive
  stationary path;
* `stationary_const_of_B_zero`, `no_positive_stationary_of_B_neg`: `Λ = 0` forces a
  constant path, `Λ < 0` admits no positive stationary path;
* `log_profile_error_le`: **`eq:main-finite-profile-convergence`**: with
  `τ_j = Σ_{i<j} s_i`, `T = Σ_{j<M} s_j`, `s_j ≤ h_t` and `ωh_t/2 ≤ b < 1`,
  `|log(q_j/q_0) − σωτ_j| ≤ ω³ T h_t²/(12(1 − b²))` for all `j ≤ M`, from the
  remainder bound `0 ≤ log((1+x)/(1−x)) − 2x ≤ 2x³/(3(1−b²))` on `0 ≤ x ≤ b`
  (`log_ratio_sub_two_mul_le`; `log((1+x)/(1−x)) = 2 artanh x`);
* `scale_factor_log_error_le`, `density_log_error_le`, `conductance_log_error_le`:
  the induced second-order logarithmic errors for `a_j = q_j^{2/3}` against
  `σ H₀ τ_j` (`H₀ = 2ω/3 = √(Λ/3)`), `ϱ_j = q_j²` and `κ_j = q_j^{−4/3}`.

Scoped conventions: paths and lapse intervals are `ℕ → ℝ` sequences, only the
indices `j ≤ M` (resp. `j < M`) enter; the maximal step `h_t` is any common upper
bound of the `s_j`.
-/

namespace RenewalGeometry.FiniteHomogeneousStationarity

open Real Finset

/-! ### The finite action and its Euler expressions -/

/-- The midpoint amplitude `q̄_j = (q_j + q_{j+1})/2`. -/
noncomputable def midAmp (q : ℕ → ℝ) (j : ℕ) : ℝ := (q j + q (j + 1)) / 2

/-- The discrete velocity `v_j = (q_{j+1} − q_j)/s_j`. -/
noncomputable def velocity (q s : ℕ → ℝ) (j : ℕ) : ℝ := (q (j + 1) - q j) / s j

/-- One edge term `A₀ (q_{j+1} − q_j)²/s_j + B₀ s_j q̄_j²`. -/
noncomputable def edgeTerm (A₀ B₀ : ℝ) (q s : ℕ → ℝ) (j : ℕ) : ℝ :=
  A₀ * (q (j + 1) - q j) ^ 2 / s j + B₀ * s j * midAmp q j ^ 2

/-- The finite lapse-varied homogeneous action `S_d(q,s)`
(`eq:main-discrete-homogeneous-action`). -/
noncomputable def discreteAction (A₀ B₀ : ℝ) (M : ℕ) (q s : ℕ → ℝ) : ℝ :=
  -∑ j ∈ range M, edgeTerm A₀ B₀ q s j

/-- The lapse Euler expression `A₀ v_j² − B₀ q̄_j²` (`eq:main-discrete-lapse-constraint`). -/
noncomputable def lapseEuler (A₀ B₀ : ℝ) (q s : ℕ → ℝ) (j : ℕ) : ℝ :=
  A₀ * velocity q s j ^ 2 - B₀ * midAmp q j ^ 2

/-- The scale Euler expression `2A₀(v_j − v_{j−1}) − B₀(s_{j−1} q̄_{j−1} + s_j q̄_j)`
(`eq:main-discrete-scale-euler`). -/
noncomputable def scaleEuler (A₀ B₀ : ℝ) (q s : ℕ → ℝ) (j : ℕ) : ℝ :=
  2 * A₀ * (velocity q s j - velocity q s (j - 1))
    - B₀ * (s (j - 1) * midAmp q (j - 1) + s j * midAmp q j)

/-- Derivative of a real quadratic polynomial. -/
theorem hasDerivAt_quadratic (α β γ t : ℝ) :
    HasDerivAt (fun t => α * t ^ 2 + β * t + γ) (2 * α * t + β) t := by
  have h := (((hasDerivAt_pow 2 t).const_mul α).add ((hasDerivAt_id t).const_mul β)).add_const γ
  refine h.congr_deriv ?_
  simp
  ring

/-- **`eq:main-discrete-lapse-constraint`**: the partial derivative of `S_d` with respect
to the lapse-weighted interval `s_j` (`j < M`, `s_j ≠ 0`) is `A₀ v_j² − B₀ q̄_j²`. -/
theorem hasDerivAt_discreteAction_lapse (A₀ B₀ : ℝ) (M : ℕ) (q s : ℕ → ℝ) {j : ℕ}
    (hj : j < M) (hs : s j ≠ 0) :
    HasDerivAt (fun t => discreteAction A₀ B₀ M q (Function.update s j t))
      (lapseEuler A₀ B₀ q s j) (s j) := by
  have key : ∀ i ∈ range M,
      HasDerivAt (fun t => edgeTerm A₀ B₀ q (Function.update s j t) i)
        (if i = j then -(A₀ * (q (j + 1) - q j) ^ 2) / s j ^ 2 + B₀ * midAmp q j ^ 2 else 0)
        (s j) := by
    intro i _
    by_cases hij : i = j
    · subst hij
      simp only [if_true]
      have hfun : (fun t => edgeTerm A₀ B₀ q (Function.update s i t) i)
          = fun t => A₀ * (q (i + 1) - q i) ^ 2 / t + B₀ * t * midAmp q i ^ 2 := by
        funext t; simp [edgeTerm, Function.update_self]
      rw [hfun]
      have h1 : HasDerivAt (fun t : ℝ => A₀ * (q (i + 1) - q i) ^ 2 / t)
          (-(A₀ * (q (i + 1) - q i) ^ 2) / s i ^ 2) (s i) := by
        have := (hasDerivAt_const (s i) (A₀ * (q (i + 1) - q i) ^ 2)).div (hasDerivAt_id (s i)) hs
        refine this.congr_deriv ?_
        simp only [id]
        ring
      have h2 : HasDerivAt (fun t : ℝ => B₀ * t * midAmp q i ^ 2) (B₀ * midAmp q i ^ 2) (s i) := by
        have := ((hasDerivAt_id (s i)).const_mul B₀).mul_const (midAmp q i ^ 2)
        refine this.congr_deriv ?_
        simp
      exact h1.add h2
    · simp only [hij, if_false]
      have hfun : (fun t => edgeTerm A₀ B₀ q (Function.update s j t) i)
          = fun _ => edgeTerm A₀ B₀ q s i := by
        funext t; simp [edgeTerm, Function.update_of_ne hij]
      rw [hfun]
      exact hasDerivAt_const _ _
  have hsum := HasDerivAt.fun_sum key
  rw [sum_ite_eq' (range M) j, if_pos (mem_range.mpr hj)] at hsum
  have hneg := hsum.neg
  unfold discreteAction
  refine hneg.congr_deriv ?_
  unfold lapseEuler velocity
  field_simp
  ring

/-- **`eq:main-discrete-scale-euler`**: the partial derivative of `S_d` with respect to
the interior node `q_j` (`1 ≤ j < M`, `s_{j−1}, s_j ≠ 0`) is
`2A₀(v_j − v_{j−1}) − B₀(s_{j−1} q̄_{j−1} + s_j q̄_j)`; the endpoints `q_0, q_M` are
never varied. -/
theorem hasDerivAt_discreteAction_scale (A₀ B₀ : ℝ) (M : ℕ) (q s : ℕ → ℝ) {j : ℕ}
    (hj1 : 1 ≤ j) (hjM : j < M) (hs : s j ≠ 0) (hs' : s (j - 1) ≠ 0) :
    HasDerivAt (fun t => discreteAction A₀ B₀ M (Function.update q j t) s)
      (scaleEuler A₀ B₀ q s j) (q j) := by
  have hjeq : j - 1 + 1 = j := by omega
  -- derivative contributions of the two edges touching node `j`
  set d₁ : ℝ := -2 * A₀ * (q (j + 1) - q j) / s j + B₀ * s j * midAmp q j with hd₁
  set d₂ : ℝ := 2 * A₀ * (q j - q (j - 1)) / s (j - 1) + B₀ * s (j - 1) * midAmp q (j - 1)
    with hd₂
  have key : ∀ i ∈ range M,
      HasDerivAt (fun t => edgeTerm A₀ B₀ (Function.update q j t) s i)
        ((if i = j then d₁ else 0) + (if i = j - 1 then d₂ else 0)) (q j) := by
    intro i _
    by_cases hij : i = j
    · subst hij
      have hne : ¬ (i = i - 1) := by omega
      rw [if_pos rfl, if_neg hne, add_zero]
      have hfun : (fun t => edgeTerm A₀ B₀ (Function.update q i t) s i)
          = fun t => (A₀ / s i + B₀ * s i / 4) * t ^ 2
              + (-2 * A₀ * q (i + 1) / s i + B₀ * s i * q (i + 1) / 2) * t
              + (A₀ * q (i + 1) ^ 2 / s i + B₀ * s i * q (i + 1) ^ 2 / 4) := by
        funext t
        have h1 : i + 1 ≠ i := by omega
        simp only [edgeTerm, midAmp, Function.update_self, Function.update_of_ne h1]
        field_simp
        ring
      rw [hfun]
      refine (hasDerivAt_quadratic _ _ _ _).congr_deriv ?_
      rw [hd₁]
      unfold midAmp
      field_simp
      ring
    · by_cases hij' : i = j - 1
      · subst hij'
        rw [if_neg hij, if_pos rfl, zero_add]
        have hfun : (fun t => edgeTerm A₀ B₀ (Function.update q j t) s (j - 1))
            = fun t => (A₀ / s (j - 1) + B₀ * s (j - 1) / 4) * t ^ 2
                + (-2 * A₀ * q (j - 1) / s (j - 1) + B₀ * s (j - 1) * q (j - 1) / 2) * t
                + (A₀ * q (j - 1) ^ 2 / s (j - 1) + B₀ * s (j - 1) * q (j - 1) ^ 2 / 4) := by
          funext t
          unfold edgeTerm midAmp
          rw [hjeq, Function.update_self, Function.update_of_ne hij]
          field_simp
          ring
        rw [hfun]
        refine (hasDerivAt_quadratic _ _ _ _).congr_deriv ?_
        rw [hd₂]
        unfold midAmp
        rw [hjeq]
        field_simp
        ring
      · rw [if_neg hij, if_neg hij', add_zero]
        have hfun : (fun t => edgeTerm A₀ B₀ (Function.update q j t) s i)
            = fun _ => edgeTerm A₀ B₀ q s i := by
          funext t
          have h1 : i + 1 ≠ j := by omega
          simp [edgeTerm, midAmp, Function.update_of_ne hij, Function.update_of_ne h1]
        rw [hfun]
        exact hasDerivAt_const _ _
  have hsum := HasDerivAt.fun_sum key
  rw [sum_add_distrib, sum_ite_eq' (range M) j, if_pos (mem_range.mpr hjM),
    sum_ite_eq' (range M) (j - 1), if_pos (mem_range.mpr (by omega))] at hsum
  have hneg := hsum.neg
  unfold discreteAction
  refine hneg.congr_deriv ?_
  rw [hd₁, hd₂]
  unfold scaleEuler velocity midAmp
  rw [hjeq]
  field_simp
  ring

/-! ### Stationary paths and the common-sign recurrence -/

/-- A pair `(q, s)` is a finite stationary point of `S_d` when both Euler expressions
vanish: the lapse constraint at every edge `j < M` and the scale equation at every
interior node `1 ≤ j < M` (`thm:main-finite-homogeneous-stationarity`). -/
structure IsFiniteStationary (A₀ B₀ : ℝ) (M : ℕ) (q s : ℕ → ℝ) : Prop where
  lapse : ∀ j < M, lapseEuler A₀ B₀ q s j = 0
  scale : ∀ j, 1 ≤ j → j < M → scaleEuler A₀ B₀ q s j = 0

/-- A positive path: `q_j > 0` for `j ≤ M` and `s_j > 0` for `j < M`. -/
structure IsPositivePath (M : ℕ) (q s : ℕ → ℝ) : Prop where
  q_pos : ∀ j ≤ M, 0 < q j
  s_pos : ∀ j < M, 0 < s j

/-- The common-sign rational recurrence `eq:main-finite-stationary-recurrence`:
`q_{j+1} = q_j (1 + σωs_j/2)/(1 − σωs_j/2)` with `ωs_j/2 < 1` for all `j < M`. -/
def SatisfiesRecurrence (ω σ : ℝ) (M : ℕ) (q s : ℕ → ℝ) : Prop :=
  ∀ j < M, ω * s j / 2 < 1 ∧
    q (j + 1) = q j * ((1 + σ * ω * s j / 2) / (1 - σ * ω * s j / 2))

/-- The signed step relation `q_{j+1} − q_j = σ ω s_j q̄_j`. -/
def SignedStep (ω σ : ℝ) (q s : ℕ → ℝ) (j : ℕ) : Prop :=
  q (j + 1) - q j = σ * ω * s j * midAmp q j

/-- The lapse constraint with `A₀, B₀ > 0` forces a signed step `v_j = ±ω q̄_j`,
`ω = √(B₀/A₀)`. -/
theorem signedStep_of_lapse (A₀ B₀ : ℝ) (hA : 0 < A₀) (hB : 0 < B₀) (q s : ℕ → ℝ) (j : ℕ)
    (hs : s j ≠ 0) (h : lapseEuler A₀ B₀ q s j = 0) :
    SignedStep (Real.sqrt (B₀ / A₀)) 1 q s j ∨ SignedStep (Real.sqrt (B₀ / A₀)) (-1) q s j := by
  set ω := Real.sqrt (B₀ / A₀) with hω
  have hω2 : ω ^ 2 = B₀ / A₀ := Real.sq_sqrt (div_pos hB hA).le
  have hv : velocity q s j ^ 2 = (ω * midAmp q j) ^ 2 := by
    unfold lapseEuler at h
    rw [mul_pow, hω2]
    field_simp
    linarith
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hv with h1 | h1
  · left
    unfold SignedStep
    unfold velocity at h1
    field_simp at h1
    linear_combination h1
  · right
    unfold SignedStep
    unfold velocity at h1
    field_simp at h1
    linear_combination h1

/-- A signed step with positive amplitudes and `ω, s_j > 0` forces `ωs_j/2 < 1` and the
rational recurrence at edge `j`. -/
theorem recurrence_of_signedStep (ω σ : ℝ) (hω : 0 < ω) (hσ : σ = 1 ∨ σ = -1) (q s : ℕ → ℝ)
    (j : ℕ) (hq : 0 < q j) (hq' : 0 < q (j + 1)) (hs : 0 < s j)
    (h : SignedStep ω σ q s j) :
    ω * s j / 2 < 1 ∧ q (j + 1) = q j * ((1 + σ * ω * s j / 2) / (1 - σ * ω * s j / 2)) := by
  unfold SignedStep midAmp at h
  have hx : 0 < ω * s j / 2 := by positivity
  have hlt : ω * s j / 2 < 1 := by
    rcases hσ with rfl | rfl
    · -- q_{j+1}(1 − x) = q_j (1 + x) > 0
      have : q (j + 1) * (1 - ω * s j / 2) = q j * (1 + ω * s j / 2) := by linarith
      have hpos : 0 < q j * (1 + ω * s j / 2) := by positivity
      rw [← this] at hpos
      have := (pos_iff_pos_of_mul_pos hpos).mp hq'
      linarith
    · have : q j * (1 - ω * s j / 2) = q (j + 1) * (1 + ω * s j / 2) := by linarith
      have hpos : 0 < q (j + 1) * (1 + ω * s j / 2) := by positivity
      rw [← this] at hpos
      have := (pos_iff_pos_of_mul_pos hpos).mp hq
      linarith
  refine ⟨hlt, ?_⟩
  have hden : 1 - σ * ω * s j / 2 ≠ 0 := by
    apply ne_of_gt
    rcases hσ with rfl | rfl <;> nlinarith
  rw [← mul_div_assoc, eq_div_iff hden]
  linear_combination h

/-- Two consecutive signed steps with signs `σ, σ'` at edges `j, j+1` and the scale
equation at node `j+1` force `σ' = σ` (positive `q_{j+1}`, `A₀ ω ≠ 0`). -/
theorem sign_eq_of_scale (A₀ B₀ ω σ σ' : ℝ) (hA : 0 < A₀) (hω : 0 < ω) (hB : B₀ = A₀ * ω ^ 2)
    (hσ : σ = 1 ∨ σ = -1) (hσ' : σ' = 1 ∨ σ' = -1) (q s : ℕ → ℝ) (j : ℕ)
    (hq : 0 < q (j + 1)) (hs : s j ≠ 0) (hs' : s (j + 1) ≠ 0)
    (h₁ : SignedStep ω σ q s j) (h₂ : SignedStep ω σ' q s (j + 1))
    (hsc : scaleEuler A₀ B₀ q s (j + 1) = 0) : σ' = σ := by
  have hσsq : σ ^ 2 = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hσ'sq : σ' ^ 2 = 1 := by rcases hσ' with rfl | rfl <;> norm_num
  unfold SignedStep at h₁ h₂
  have hv₁ : velocity q s j = σ * ω * midAmp q j := by
    unfold velocity; rw [h₁]; field_simp
  have hv₂ : velocity q s (j + 1) = σ' * ω * midAmp q (j + 1) := by
    unfold velocity; rw [h₂]; field_simp
  unfold scaleEuler at hsc
  rw [Nat.add_sub_cancel, hv₁, hv₂, hB] at hsc
  simp only [midAmp] at hsc h₁ h₂
  have key : 2 * A₀ * ω * q (j + 1) * (σ' - σ) = 0 := by
    linear_combination hsc + (-A₀ * ω * σ) * h₁ + (-A₀ * ω ^ 2 * s j * ((q j + q (j + 1)) / 2)) * hσsq
      + (-A₀ * ω * σ') * h₂
      + (-A₀ * ω ^ 2 * s (j + 1) * ((q (j + 1) + q (j + 1 + 1)) / 2)) * hσ'sq
  have hne : 2 * A₀ * ω * q (j + 1) ≠ 0 := by positivity
  have := (mul_eq_zero.mp key).resolve_left hne
  linarith

/-- **`eq:main-finite-stationary-recurrence`** (`thm:main-finite-homogeneous-stationarity`,
classification): for `A₀, B₀ > 0` (`Λ > 0`) and `ω = √(B₀/A₀)`, every positive
stationary path has one common sign `σ ∈ {−1, 1}` with
`q_{j+1} = q_j (1 + σωs_j/2)/(1 − σωs_j/2)` and `0 < ωs_j/2 < 1` for all `j < M`. -/
theorem stationary_recurrence_of_pos (A₀ B₀ : ℝ) (hA : 0 < A₀) (hB : 0 < B₀) (M : ℕ)
    (q s : ℕ → ℝ) (hpos : IsPositivePath M q s) (hst : IsFiniteStationary A₀ B₀ M q s) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ SatisfiesRecurrence (Real.sqrt (B₀ / A₀)) σ M q s ∧
      ∀ j < M, 0 < Real.sqrt (B₀ / A₀) * s j / 2 := by
  set ω := Real.sqrt (B₀ / A₀) with hω
  have hωpos : 0 < ω := Real.sqrt_pos.mpr (div_pos hB hA)
  have hBω : B₀ = A₀ * ω ^ 2 := by
    rw [hω, Real.sq_sqrt (div_pos hB hA).le]; field_simp
  have hstep : ∀ j < M, SignedStep ω 1 q s j ∨ SignedStep ω (-1) q s j := fun j hj =>
    signedStep_of_lapse A₀ B₀ hA hB q s j (hpos.s_pos j hj).ne' (hst.lapse j hj)
  -- common sign by induction
  have hcommon : ∀ σ : ℝ, (σ = 1 ∨ σ = -1) → SignedStep ω σ q s 0 →
      ∀ j < M, SignedStep ω σ q s j := by
    intro σ hσ h0 j
    induction j with
    | zero => intro _; exact h0
    | succ n ih =>
        intro hn
        have hprev := ih (by omega)
        rcases hstep (n + 1) hn with hnext | hnext
        · have := sign_eq_of_scale A₀ B₀ ω σ 1 hA hωpos hBω hσ (Or.inl rfl) q s n
            (hpos.q_pos (n + 1) (by omega)) (hpos.s_pos n (by omega)).ne'
            (hpos.s_pos (n + 1) hn).ne' hprev hnext (hst.scale (n + 1) (by omega) hn)
          rw [← this]; exact hnext
        · have := sign_eq_of_scale A₀ B₀ ω σ (-1) hA hωpos hBω hσ (Or.inr rfl) q s n
            (hpos.q_pos (n + 1) (by omega)) (hpos.s_pos n (by omega)).ne'
            (hpos.s_pos (n + 1) hn).ne' hprev hnext (hst.scale (n + 1) (by omega) hn)
          rw [← this]; exact hnext
  have hrec : ∀ σ : ℝ, (σ = 1 ∨ σ = -1) → (∀ j < M, SignedStep ω σ q s j) →
      SatisfiesRecurrence ω σ M q s := by
    intro σ hσ hall j hj
    exact recurrence_of_signedStep ω σ hωpos hσ q s j (hpos.q_pos j (by omega))
      (hpos.q_pos (j + 1) (by omega)) (hpos.s_pos j hj) (hall j hj)
  have hx : ∀ j < M, 0 < ω * s j / 2 := fun j hj => by
    have := hpos.s_pos j hj; positivity
  by_cases hM : M = 0
  · subst hM
    exact ⟨1, Or.inl rfl, fun j hj => absurd hj (Nat.not_lt_zero _), fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  · have h0M : 0 < M := Nat.pos_of_ne_zero hM
    rcases hstep 0 h0M with h0 | h0
    · exact ⟨1, Or.inl rfl, hrec 1 (Or.inl rfl) (hcommon 1 (Or.inl rfl) h0), hx⟩
    · exact ⟨-1, Or.inr rfl, hrec (-1) (Or.inr rfl) (hcommon (-1) (Or.inr rfl) h0), hx⟩

/-- A common-sign recurrence gives the signed step at every edge. -/
theorem signedStep_of_recurrence (ω σ : ℝ) (hω : 0 < ω) (hσ : σ = 1 ∨ σ = -1) (M : ℕ)
    (q s : ℕ → ℝ) (hs : ∀ j < M, 0 < s j) (h : SatisfiesRecurrence ω σ M q s) :
    ∀ j < M, SignedStep ω σ q s j := by
  intro j hj
  obtain ⟨hlt, heq⟩ := h j hj
  have hx0 : 0 < ω * s j / 2 := by have := hs j hj; positivity
  have hden : 1 - σ * ω * s j / 2 ≠ 0 := by
    apply ne_of_gt
    rcases hσ with rfl | rfl <;> nlinarith
  have h' : q (j + 1) * (1 - σ * ω * s j / 2) = q j * (1 + σ * ω * s j / 2) := by
    rw [heq, mul_div_assoc', div_mul_cancel₀ _ hden]
  unfold SignedStep midAmp
  linear_combination h'

/-- Positivity propagates along a common-sign recurrence. -/
theorem recurrence_pos (ω σ : ℝ) (hω : 0 < ω) (hσ : σ = 1 ∨ σ = -1) (M : ℕ) (q s : ℕ → ℝ) (hq0 : 0 < q 0)
    (hs : ∀ j < M, 0 < s j) (h : SatisfiesRecurrence ω σ M q s) : ∀ j ≤ M, 0 < q j := by
  intro j
  induction j with
  | zero => intro _; exact hq0
  | succ n ih =>
      intro hn
      obtain ⟨hlt, heq⟩ := h n (by omega)
      have hsn := hs n (by omega)
      have hx0 : 0 < ω * s n / 2 := by positivity
      have h1 : 0 < 1 + σ * ω * s n / 2 := by rcases hσ with rfl | rfl <;> nlinarith
      have h2 : 0 < 1 - σ * ω * s n / 2 := by rcases hσ with rfl | rfl <;> nlinarith
      rw [heq]
      exact mul_pos (ih (by omega)) (div_pos h1 h2)

/-- Converse (`thm:main-finite-homogeneous-stationarity`): every common-sign recurrence
with positive lapse intervals and `q_0 > 0` is a positive stationary path
(`A₀ > 0`, `B₀ = A₀ ω²`). -/
theorem stationary_of_recurrence (A₀ B₀ ω σ : ℝ) (hA : 0 < A₀) (hω : 0 < ω) (hB : B₀ = A₀ * ω ^ 2)
    (hσ : σ = 1 ∨ σ = -1) (M : ℕ) (q s : ℕ → ℝ) (hq0 : 0 < q 0) (hs : ∀ j < M, 0 < s j)
    (h : SatisfiesRecurrence ω σ M q s) :
    IsPositivePath M q s ∧ IsFiniteStationary A₀ B₀ M q s := by
  have hstep := signedStep_of_recurrence ω σ hω hσ M q s hs h
  have hσsq : σ ^ 2 = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hv : ∀ j < M, velocity q s j = σ * ω * midAmp q j := by
    intro j hj
    have := hstep j hj
    unfold SignedStep at this
    unfold velocity; rw [this]; field_simp [(hs j hj).ne']
  refine ⟨⟨recurrence_pos ω σ hω hσ M q s hq0 hs h, hs⟩, ⟨?_, ?_⟩⟩
  · intro j hj
    unfold lapseEuler
    rw [hv j hj, hB]
    linear_combination A₀ * ω ^ 2 * midAmp q j ^ 2 * hσsq
  · intro j hj1 hjM
    obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
    unfold scaleEuler
    rw [Nat.add_sub_cancel, hv (n + 1) hjM, hv n (by omega), hB]
    have h₁ := hstep n (by omega)
    have h₂ := hstep (n + 1) hjM
    unfold SignedStep at h₁ h₂
    unfold midAmp at h₁ h₂ ⊢
    linear_combination (A₀ * ω * σ) * h₁ + (A₀ * ω * σ) * h₂
      + (A₀ * ω ^ 2 * (s n * ((q n + q (n + 1)) / 2)
          + s (n + 1) * ((q (n + 1) + q (n + 1 + 1)) / 2))) * hσsq

/-- `Λ = 0` (`B₀ = 0`): the lapse constraint forces a constant amplitude. -/
theorem stationary_const_of_B_zero (A₀ : ℝ) (hA : A₀ ≠ 0) (M : ℕ) (q s : ℕ → ℝ)
    (hs : ∀ j < M, s j ≠ 0) (hst : IsFiniteStationary A₀ 0 M q s) :
    ∀ j ≤ M, q j = q 0 := by
  intro j
  induction j with
  | zero => intro _; rfl
  | succ n ih =>
      intro hn
      have h := hst.lapse n (by omega)
      unfold lapseEuler velocity at h
      simp only [zero_mul, sub_zero, mul_eq_zero, hA, false_or] at h
      have h' : (q (n + 1) - q n) / s n = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
      rw [div_eq_zero_iff] at h'
      rcases h' with h' | h'
      · rw [← ih (by omega)]; linarith
      · exact absurd h' (hs n (by omega))

/-- `Λ < 0` (`B₀ < 0`): there is no positive stationary path with at least one edge. -/
theorem no_positive_stationary_of_B_neg (A₀ B₀ : ℝ) (hA : 0 < A₀) (hB : B₀ < 0) (M : ℕ)
    (hM : 0 < M) (q s : ℕ → ℝ) (hpos : IsPositivePath M q s) :
    ¬ IsFiniteStationary A₀ B₀ M q s := by
  intro hst
  have h := hst.lapse 0 hM
  unfold lapseEuler at h
  have hm : 0 < midAmp q 0 := by
    unfold midAmp
    have := hpos.q_pos 0 (by omega)
    have := hpos.q_pos 1 (by omega)
    positivity
  have h1 : 0 ≤ A₀ * velocity q s 0 ^ 2 := by positivity
  have h2 : B₀ * midAmp q 0 ^ 2 < 0 := mul_neg_of_neg_of_pos hB (by positivity)
  linarith

/-! ### The second-order logarithmic profile error -/

/-- The remainder `log((1+x)/(1−x)) − 2x` is nonnegative and at most `2x³/(3(1−b²))` for
`0 ≤ x ≤ b < 1` (the artanh remainder used in `eq:main-finite-profile-convergence`;
`log((1+x)/(1−x)) = 2 artanh x`). -/
theorem log_ratio_sub_two_mul_le {b : ℝ} (hb : b < 1) {x : ℝ} (hx0 : 0 ≤ x) (hxb : x ≤ b) :
    0 ≤ Real.log ((1 + x) / (1 - x)) - 2 * x ∧
      Real.log ((1 + x) / (1 - x)) - 2 * x ≤ 2 * x ^ 3 / (3 * (1 - b ^ 2)) := by
  have hb2 : 0 < 1 - b ^ 2 := by nlinarith
  -- f(y) = log(1+y) − log(1−y) − 2y
  set f : ℝ → ℝ := fun y => Real.log (1 + y) - Real.log (1 - y) - 2 * y with hf
  have hderiv : ∀ y ∈ Set.Ioo (-1 : ℝ) 1, HasDerivAt f (2 * y ^ 2 / (1 - y ^ 2)) y := by
    intro y hy
    have h1 : (1 : ℝ) + y ≠ 0 := by linarith [hy.1]
    have h2 : (1 : ℝ) - y ≠ 0 := by linarith [hy.2]
    have d1 : HasDerivAt (fun y : ℝ => Real.log (1 + y)) (1 / (1 + y)) y := by
      have := ((hasDerivAt_id y).const_add 1).log h1
      simpa using this
    have d2 : HasDerivAt (fun y : ℝ => Real.log (1 - y)) ((-1) / (1 - y)) y := by
      have := ((hasDerivAt_id y).const_sub 1).log h2
      simpa using this
    have d3 : HasDerivAt (fun y : ℝ => 2 * y) 2 y := by
      simpa using (hasDerivAt_id y).const_mul 2
    have := (d1.sub d2).sub d3
    refine this.congr_deriv ?_
    have h3 : (1 : ℝ) - y ^ 2 ≠ 0 := by
      have : (1 : ℝ) - y ^ 2 = (1 + y) * (1 - y) := by ring
      rw [this]; exact mul_ne_zero h1 h2
    field_simp
    ring
  have hcont : ∀ y ∈ Set.Ioo (-1 : ℝ) 1, ContinuousAt f y :=
    fun y hy => (hderiv y hy).continuousAt
  have hIcc : Set.Icc (0 : ℝ) b ⊆ Set.Ioo (-1) 1 := fun y hy =>
    ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hf0 : f 0 = 0 := by simp [hf]
  -- monotonicity of f on [0, b]
  have hmono : MonotoneOn f (Set.Icc 0 b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 b)
    · exact fun y hy => (hcont y (hIcc hy)).continuousWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      exact (hderiv y (hIcc (Set.Ioo_subset_Icc_self hy))).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      rw [(hderiv y (hIcc (Set.Ioo_subset_Icc_self hy))).deriv]
      have : 0 < 1 - y ^ 2 := by nlinarith [hy.1, hy.2, hb]
      positivity
  -- monotonicity of g(y) = 2y³/(3(1−b²)) − f(y) on [0, b]
  set g : ℝ → ℝ := fun y => 2 * y ^ 3 / (3 * (1 - b ^ 2)) - f y with hg
  have hgderiv : ∀ y ∈ Set.Ioo (-1 : ℝ) 1,
      HasDerivAt g (2 * y ^ 2 / (1 - b ^ 2) - 2 * y ^ 2 / (1 - y ^ 2)) y := by
    intro y hy
    have d1 : HasDerivAt (fun y : ℝ => 2 * y ^ 3 / (3 * (1 - b ^ 2)))
        (2 * (↑(3:ℕ) * y ^ (3 - 1)) / (3 * (1 - b ^ 2))) y :=
      ((hasDerivAt_pow 3 y).const_mul 2).div_const _
    have := d1.sub (hderiv y hy)
    refine this.congr_deriv ?_
    field_simp
    ring
  have hgmono : MonotoneOn g (Set.Icc 0 b) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 b)
    · exact fun y hy => (hgderiv y (hIcc hy)).continuousAt.continuousWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      exact (hgderiv y (hIcc (Set.Ioo_subset_Icc_self hy))).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [interior_Icc] at hy
      rw [(hgderiv y (hIcc (Set.Ioo_subset_Icc_self hy))).deriv]
      have hy2 : 0 < 1 - y ^ 2 := by nlinarith [hy.1, hy.2, hb]
      have hle : 1 - b ^ 2 ≤ 1 - y ^ 2 := by nlinarith [hy.1, hy.2]
      rw [sub_nonneg]
      apply div_le_div_of_nonneg_left (by positivity) hb2 hle
  have hg0 : g 0 = 0 := by simp [hg, hf0]
  have hxmem : x ∈ Set.Icc (0 : ℝ) b := ⟨hx0, hxb⟩
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) b := ⟨le_refl _, by linarith⟩
  have hfx : f 0 ≤ f x := hmono h0mem hxmem hx0
  have hgx : g 0 ≤ g x := hgmono h0mem hxmem hx0
  rw [hf0] at hfx
  rw [hg0] at hgx
  have hlog : Real.log ((1 + x) / (1 - x)) = Real.log (1 + x) - Real.log (1 - x) :=
    Real.log_div (by linarith) (by linarith)
  rw [hlog]
  simp only [hg, hf] at hfx hgx
  constructor <;> linarith

/-- `log((1+x)/(1−x)) = 2 artanh x` for `|x| < 1`: the remainder lemma is the artanh
remainder of the manuscript. -/
theorem log_ratio_eq_two_artanh {x : ℝ} (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    Real.log ((1 + x) / (1 - x)) = 2 * Real.artanh x := by
  rw [Real.artanh_eq_half_log (Set.Ioo_subset_Icc_self hx)]; ring

/-- The one-step logarithm along the common-sign recurrence:
`log(q_{j+1}/q_j) = σ log((1+x_j)/(1−x_j))` with `x_j = ωs_j/2`. -/
theorem log_step_eq (ω σ : ℝ) (hσ : σ = 1 ∨ σ = -1) (q s : ℕ → ℝ) (j : ℕ) (hq : 0 < q j)
    (hx : 0 < ω * s j / 2) (hlt : ω * s j / 2 < 1)
    (heq : q (j + 1) = q j * ((1 + σ * ω * s j / 2) / (1 - σ * ω * s j / 2))) :
    Real.log (q (j + 1)) - Real.log (q j)
      = σ * Real.log ((1 + ω * s j / 2) / (1 - ω * s j / 2)) := by
  have h1 : (0:ℝ) < 1 - ω * s j / 2 := by linarith
  have h2 : (0:ℝ) < 1 + ω * s j / 2 := by linarith
  rcases hσ with rfl | rfl
  · have heq' : q (j + 1) = q j * ((1 + ω * s j / 2) / (1 - ω * s j / 2)) := by rw [heq]; ring
    rw [heq', Real.log_mul hq.ne' (div_pos h2 h1).ne']
    ring
  · have heq' : q (j + 1) = q j * ((1 - ω * s j / 2) / (1 + ω * s j / 2)) := by rw [heq]; ring
    rw [heq', Real.log_mul hq.ne' (div_pos h1 h2).ne', Real.log_div h1.ne' h2.ne',
      Real.log_div h2.ne' h1.ne']
    ring

/-- The renewal time `τ_j = Σ_{i<j} s_i`. -/
noncomputable def renewalTime (s : ℕ → ℝ) (j : ℕ) : ℝ := ∑ i ∈ range j, s i

/-- **`eq:main-finite-profile-convergence`** (`thm:main-finite-homogeneous-stationarity`):
along a common-sign recurrence with `q_0 > 0`, `s_j > 0`, `s_j ≤ h_t` and
`ωh_t/2 ≤ b < 1`, for every `j ≤ M`,
`|log(q_j/q_0) − σωτ_j| ≤ ω³ T h_t²/(12(1 − b²))` with `T = Σ_{j<M} s_j`. -/
theorem log_profile_error_le (ω σ b h : ℝ) (hω : 0 < ω) (hσ : σ = 1 ∨ σ = -1) (hb0 : 0 ≤ b) (hb : b < 1)
    (hωb : ω * h / 2 ≤ b) (M : ℕ) (q s : ℕ → ℝ) (hq0 : 0 < q 0) (hs : ∀ j < M, 0 < s j)
    (hsh : ∀ j < M, s j ≤ h) (hrec : SatisfiesRecurrence ω σ M q s) :
    ∀ j ≤ M, |Real.log (q j / q 0) - σ * ω * renewalTime s j|
      ≤ ω ^ 3 * renewalTime s M * h ^ 2 / (12 * (1 - b ^ 2)) := by
  have hqpos := recurrence_pos ω σ hω hσ M q s hq0 hs hrec
  have hb2 : 0 < 1 - b ^ 2 := by nlinarith
  intro j hjM
  -- the per-step remainder
  set K : ℝ := ω ^ 3 * h ^ 2 / (12 * (1 - b ^ 2)) with hK
  have hstep : ∀ i < M, 0 ≤ σ * (Real.log (q (i + 1)) - Real.log (q i)) - ω * s i ∧
      σ * (Real.log (q (i + 1)) - Real.log (q i)) - ω * s i ≤ K * s i := by
    intro i hi
    obtain ⟨hlt, heq⟩ := hrec i hi
    have hx : 0 < ω * s i / 2 := by have := hs i hi; positivity
    have hlog := log_step_eq ω σ hσ q s i (hqpos i (by omega)) hx hlt heq
    have hσsq : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
    have hxb : ω * s i / 2 ≤ b := by
      have := hsh i hi
      calc ω * s i / 2 ≤ ω * h / 2 := by gcongr
        _ ≤ b := hωb
    obtain ⟨hr0, hr1⟩ := log_ratio_sub_two_mul_le hb hx.le hxb
    have hσlog : σ * (Real.log (q (i + 1)) - Real.log (q i))
        = Real.log ((1 + ω * s i / 2) / (1 - ω * s i / 2)) := by
      rw [hlog, ← mul_assoc, hσsq, one_mul]
    rw [hσlog]
    constructor
    · linarith
    · have hbound : Real.log ((1 + ω * s i / 2) / (1 - ω * s i / 2)) - 2 * (ω * s i / 2)
          ≤ ω ^ 3 * s i ^ 3 / (12 * (1 - b ^ 2)) := by
        refine le_trans hr1 (le_of_eq ?_)
        rw [div_eq_div_iff (by positivity) (by positivity)]
        ring
      have h3 : ω ^ 3 * s i ^ 3 / (12 * (1 - b ^ 2)) ≤ K * s i := by
        rw [hK]
        have : ω ^ 3 * s i ^ 3 / (12 * (1 - b ^ 2))
            = (ω ^ 3 * s i / (12 * (1 - b ^ 2))) * s i ^ 2 := by field_simp
        rw [this]
        have hc : 0 ≤ ω ^ 3 * s i / (12 * (1 - b ^ 2)) := by have := hs i hi; positivity
        have hsi := hs i hi
        have hsih := hsh i hi
        calc (ω ^ 3 * s i / (12 * (1 - b ^ 2))) * s i ^ 2
            ≤ (ω ^ 3 * s i / (12 * (1 - b ^ 2))) * h ^ 2 := by gcongr
          _ = ω ^ 3 * h ^ 2 / (12 * (1 - b ^ 2)) * s i := by ring
      linarith
  -- telescoping
  have htel : Real.log (q j / q 0) = ∑ i ∈ range j, (Real.log (q (i + 1)) - Real.log (q i)) := by
    rw [sum_range_sub (fun i => Real.log (q i)) j, Real.log_div (hqpos j hjM).ne' hq0.ne']
  have hσsq : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hσabs : |σ| = 1 := by rcases hσ with rfl | rfl <;> simp
  have hdiff : Real.log (q j / q 0) - σ * ω * renewalTime s j
      = σ * ∑ i ∈ range j, (σ * (Real.log (q (i + 1)) - Real.log (q i)) - ω * s i) := by
    rw [htel]
    unfold renewalTime
    simp only [mul_sum]
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro i _
    linear_combination (-(Real.log (q (i + 1)) - Real.log (q i))) * hσsq
  rw [hdiff, abs_mul, hσabs, one_mul]
  have hnn : 0 ≤ ∑ i ∈ range j, (σ * (Real.log (q (i + 1)) - Real.log (q i)) - ω * s i) :=
    sum_nonneg (fun i hi => (hstep i (by have := mem_range.mp hi; omega)).1)
  rw [abs_of_nonneg hnn]
  calc ∑ i ∈ range j, (σ * (Real.log (q (i + 1)) - Real.log (q i)) - ω * s i)
      ≤ ∑ i ∈ range j, K * s i :=
        sum_le_sum (fun i hi => (hstep i (by have := mem_range.mp hi; omega)).2)
    _ = K * renewalTime s j := by rw [renewalTime, mul_sum]
    _ ≤ K * renewalTime s M := by
        have hK0 : 0 ≤ K := by rw [hK]; positivity
        apply mul_le_mul_of_nonneg_left _ hK0
        unfold renewalTime
        apply sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr hjM)
        intro i hi _; exact (hs i (mem_range.mp hi)).le
    _ = ω ^ 3 * renewalTime s M * h ^ 2 / (12 * (1 - b ^ 2)) := by rw [hK]; ring

/-- The induced scale-factor error: `a_j = q_j^{2/3}` satisfies
`|log(a_j/a_0) − σH₀τ_j| ≤ (2/3) ω³ T h_t²/(12(1−b²))` with `H₀ = 2ω/3`
(`thm:main-finite-homogeneous-stationarity`, convergence of `a_j`). -/
theorem scale_factor_log_error_le (ω σ b h : ℝ) (hω : 0 < ω) (hσ : σ = 1 ∨ σ = -1) (hb0 : 0 ≤ b) (hb : b < 1)
    (hωb : ω * h / 2 ≤ b) (M : ℕ) (q s : ℕ → ℝ) (hq0 : 0 < q 0) (hs : ∀ j < M, 0 < s j)
    (hsh : ∀ j < M, s j ≤ h) (hrec : SatisfiesRecurrence ω σ M q s) :
    ∀ j ≤ M, |Real.log (q j ^ (2 / 3 : ℝ) / q 0 ^ (2 / 3 : ℝ)) - σ * (2 * ω / 3) * renewalTime s j|
      ≤ (2 / 3) * (ω ^ 3 * renewalTime s M * h ^ 2 / (12 * (1 - b ^ 2))) := by
  intro j hj
  have hqpos := recurrence_pos ω σ hω hσ M q s hq0 hs hrec
  have h := log_profile_error_le ω σ b h hω hσ hb0 hb hωb M q s hq0 hs hsh hrec j hj
  have hlog : Real.log (q j ^ (2 / 3 : ℝ) / q 0 ^ (2 / 3 : ℝ))
      = (2 / 3) * Real.log (q j / q 0) := by
    rw [← Real.div_rpow (hqpos j hj).le hq0.le, Real.log_rpow (div_pos (hqpos j hj) hq0)]
  rw [hlog, show (2 / 3 : ℝ) * Real.log (q j / q 0) - σ * (2 * ω / 3) * renewalTime s j
      = (2 / 3) * (Real.log (q j / q 0) - σ * ω * renewalTime s j) by ring, abs_mul,
    abs_of_pos (by norm_num : (0:ℝ) < 2 / 3)]
  gcongr

/-- The induced density error: `ϱ_j = q_j²` has twice the logarithmic error. -/
theorem density_log_error_le (ω σ b h : ℝ) (hω : 0 < ω) (hσ : σ = 1 ∨ σ = -1) (hb0 : 0 ≤ b) (hb : b < 1)
    (hωb : ω * h / 2 ≤ b) (M : ℕ) (q s : ℕ → ℝ) (hq0 : 0 < q 0) (hs : ∀ j < M, 0 < s j)
    (hsh : ∀ j < M, s j ≤ h) (hrec : SatisfiesRecurrence ω σ M q s) :
    ∀ j ≤ M, |Real.log (q j ^ 2 / q 0 ^ 2) - σ * (2 * ω) * renewalTime s j|
      ≤ 2 * (ω ^ 3 * renewalTime s M * h ^ 2 / (12 * (1 - b ^ 2))) := by
  intro j hj
  have hqpos := recurrence_pos ω σ hω hσ M q s hq0 hs hrec
  have h := log_profile_error_le ω σ b h hω hσ hb0 hb hωb M q s hq0 hs hsh hrec j hj
  have hlog : Real.log (q j ^ 2 / q 0 ^ 2) = 2 * Real.log (q j / q 0) := by
    rw [← div_pow, Real.log_pow]; push_cast; ring
  rw [hlog, show (2 : ℝ) * Real.log (q j / q 0) - σ * (2 * ω) * renewalTime s j
      = 2 * (Real.log (q j / q 0) - σ * ω * renewalTime s j) by ring, abs_mul,
    abs_of_pos (by norm_num : (0:ℝ) < 2)]
  gcongr

/-- The induced proper-time conductance error: `κ_j = q_j^{−4/3}` has `4/3` times the
logarithmic error (with the opposite sign of drift). -/
theorem conductance_log_error_le (ω σ b h : ℝ) (hω : 0 < ω) (hσ : σ = 1 ∨ σ = -1) (hb0 : 0 ≤ b) (hb : b < 1)
    (hωb : ω * h / 2 ≤ b) (M : ℕ) (q s : ℕ → ℝ) (hq0 : 0 < q 0) (hs : ∀ j < M, 0 < s j)
    (hsh : ∀ j < M, s j ≤ h) (hrec : SatisfiesRecurrence ω σ M q s) :
    ∀ j ≤ M, |Real.log (q j ^ (-(4 / 3) : ℝ) / q 0 ^ (-(4 / 3) : ℝ))
        + σ * (4 * ω / 3) * renewalTime s j|
      ≤ (4 / 3) * (ω ^ 3 * renewalTime s M * h ^ 2 / (12 * (1 - b ^ 2))) := by
  intro j hj
  have hqpos := recurrence_pos ω σ hω hσ M q s hq0 hs hrec
  have h := log_profile_error_le ω σ b h hω hσ hb0 hb hωb M q s hq0 hs hsh hrec j hj
  have hlog : Real.log (q j ^ (-(4 / 3) : ℝ) / q 0 ^ (-(4 / 3) : ℝ))
      = (-(4 / 3)) * Real.log (q j / q 0) := by
    rw [← Real.div_rpow (hqpos j hj).le hq0.le, Real.log_rpow (div_pos (hqpos j hj) hq0)]
  rw [hlog, show (-(4 / 3) : ℝ) * Real.log (q j / q 0) + σ * (4 * ω / 3) * renewalTime s j
      = (-(4 / 3)) * (Real.log (q j / q 0) - σ * ω * renewalTime s j) by ring, abs_mul,
    abs_neg, abs_of_pos (by norm_num : (0:ℝ) < 4 / 3)]
  gcongr

end RenewalGeometry.FiniteHomogeneousStationarity
