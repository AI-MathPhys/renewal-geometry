/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Same-record selection from the actual signed action drift
  (`thm:source-selection`, Einstein–Standard-Model action-closure manuscript)

A finite accepted process over a finite horizon `J` on a finite state
space has finitely many outcomes, so the whole argument of
`app:native-source-selection` is finite-sum bookkeeping on a finite
weighted outcome space `Ω` (no Markov assumption: the outcome `ω` may
carry the entire finite past).

* `FiniteAcceptedProcess`: weights `P`, records `X_j`, and the
  decreasing surviving sets `S_j` of the predeclared legal-edge mask
  (`S_0 = univ`, `S_{j+1} ⊆ S_j`);
* `survivingMass μ_j(x)`, `legalKernel K^{leg}_j(x,y)` (the legal
  transition probabilities `P(S_{j+1}, X_j = x, X_{j+1} = y)/μ_j(x)`),
  `actionDrift 𝔡_j(x)` of `eq:source-action-drift`, the diagnostic
  stopped action `stoppedAction Z_j` (retaining its last legal value),
  and `exitProbability p^{exit} = 1 - Σ_x μ_J(x)`;
* `mass_drift_eq`: `Σ_x μ_j(x) 𝔡_j(x) = E[Z_{j+1} - Z_j]`
  (`eq:app-stopped-drift`), and `sum_mass_drift_ge`: the stopped-action
  telescope `Σ_{j<J} Σ_x μ_j 𝔡_j ≥ -D^A`;
* `slope_occupation`: `eq:source-slope-occupation`
  (`eq:app-slope-telescope`) from the drift inequality
  `eq:source-drift-ineq` on active legal rows;
* `selection_failure_le`: the boxed selection-failure bound
  `eq:source-selection-failure` for any observed index minimising the
  score `eq:source-score` on surviving prefixes.

Rendering disclosed: `W_h = (i_{h,k} + γ_{h,k})²` is carried as one
nonnegative readout `W`, so the alignment threshold reads `W ≤ α²`;
`g_h ≥ 0`, `V_h ≥ 0`, and the action bounds `A⁻ ≤ a ≤ A⁺` are assumed
on the whole (legal) state space.
-/

namespace RenewalGeometry
namespace SourceSelection

/-- A finite accepted process with a legal-edge mask: probability weights
`P`, records `X_j`, and decreasing surviving sets `S_j` (the outcomes
with no attempted illegal transition up to step `j`). -/
structure FiniteAcceptedProcess (Ω 𝒳 : Type*) [Fintype Ω] where
  /-- probability weights of the outcomes -/
  P : Ω → ℝ
  P_nonneg : ∀ ω, 0 ≤ P ω
  P_sum : ∑ ω, P ω = 1
  /-- the record at step `j` -/
  X : ℕ → Ω → 𝒳
  /-- the surviving (still legal) outcomes at step `j` -/
  S : ℕ → Finset Ω
  S_zero : S 0 = Finset.univ
  S_antitone : ∀ j, S (j + 1) ⊆ S j

variable {Ω 𝒳 : Type*} [Fintype Ω] [Fintype 𝒳] [DecidableEq 𝒳] [DecidableEq Ω]

namespace FiniteAcceptedProcess

variable (proc : FiniteAcceptedProcess Ω 𝒳)

/-- The unconditioned surviving mass `μ_j(x) = P(S_j, X_j = x)`. -/
def survivingMass (j : ℕ) (x : 𝒳) : ℝ :=
  ∑ ω ∈ (proc.S j).filter (fun ω => proc.X j ω = x), proc.P ω

/-- The legal joint mass `P(S_{j+1}, X_j = x, X_{j+1} = y)`. -/
def legalJoint (j : ℕ) (x y : 𝒳) : ℝ :=
  ∑ ω ∈ (proc.S (j + 1)).filter
    (fun ω => proc.X j ω = x ∧ proc.X (j + 1) ω = y), proc.P ω

/-- The legal transition probabilities `K^{leg}_j(x,y)`. -/
noncomputable def legalKernel (j : ℕ) (x y : 𝒳) : ℝ :=
  proc.legalJoint j x y / proc.survivingMass j x

/-- The stopped conditional action increment `eq:source-action-drift`:
`𝔡_j(x) = Σ_y K^{leg}_j(x,y) [a(y) - a(x)]`. -/
noncomputable def actionDrift (a : 𝒳 → ℝ) (j : ℕ) (x : 𝒳) : ℝ :=
  ∑ y, proc.legalKernel j x y * (a y - a x)

/-- The diagnostic stopped action value `Z_j`: on a legal transition it
equals `a(X_j)`, after the first attempted illegal transition it retains
the last legal value. -/
def stoppedAction (a : 𝒳 → ℝ) : ℕ → Ω → ℝ
  | 0, ω => a (proc.X 0 ω)
  | j + 1, ω => if ω ∈ proc.S (j + 1) then a (proc.X (j + 1) ω)
      else stoppedAction a j ω

/-- The exit probability `p^{exit} = 1 - Σ_x μ_J(x)`. -/
noncomputable def exitProbability (J : ℕ) : ℝ := 1 - ∑ x, proc.survivingMass J x

/-- The occupation average `(1/J) Σ_{j<J,x} μ_j(x) f(x)` (used for
`M_{h,J}`, `A_{h,J}`, `ℛ_{h,J}` of `eq:source-occupations`,
`eq:source-work-occupation`). -/
noncomputable def occupation (J : ℕ) (f : ℕ → 𝒳 → ℝ) : ℝ :=
  (1 / (J:ℝ)) * ∑ j ∈ Finset.range J, ∑ x, proc.survivingMass j x * f j x

/-! ### Elementary mass identities -/

theorem survivingMass_nonneg (j : ℕ) (x : 𝒳) : 0 ≤ proc.survivingMass j x :=
  Finset.sum_nonneg fun ω _ => proc.P_nonneg ω

theorem legalJoint_nonneg (j : ℕ) (x y : 𝒳) : 0 ≤ proc.legalJoint j x y :=
  Finset.sum_nonneg fun ω _ => proc.P_nonneg ω

theorem legalJoint_le_survivingMass (j : ℕ) (x y : 𝒳) :
    proc.legalJoint j x y ≤ proc.survivingMass j x := by
  unfold legalJoint survivingMass
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro ω hω
    rw [Finset.mem_filter] at hω ⊢
    exact ⟨proc.S_antitone j hω.1, hω.2.1⟩
  · intro ω _ _
    exact proc.P_nonneg ω

theorem survivingMass_mul_legalKernel (j : ℕ) (x y : 𝒳) :
    proc.survivingMass j x * proc.legalKernel j x y = proc.legalJoint j x y := by
  unfold legalKernel
  by_cases hμ : proc.survivingMass j x = 0
  · have h1 := proc.legalJoint_le_survivingMass j x y
    have h2 := proc.legalJoint_nonneg j x y
    rw [hμ] at h1 ⊢
    have : proc.legalJoint j x y = 0 := le_antisymm h1 h2
    rw [this]
    simp
  · rw [mul_div_cancel₀ _ hμ]

/-- `S_J ⊆ S_j` for `j ≤ J`. -/
theorem S_subset_of_le {j J : ℕ} (h : j ≤ J) : proc.S J ⊆ proc.S j := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact (proc.S_antitone _).trans ih

/-- The total surviving mass is the probability of survival. -/
theorem sum_survivingMass (j : ℕ) :
    ∑ x, proc.survivingMass j x = ∑ ω ∈ proc.S j, proc.P ω := by
  unfold survivingMass
  exact Finset.sum_fiberwise (proc.S j) (proc.X j) proc.P

/-- Occupation of a state function through the outcome sum. -/
theorem sum_survivingMass_mul (j : ℕ) (f : 𝒳 → ℝ) :
    ∑ x, proc.survivingMass j x * f x
      = ∑ ω ∈ proc.S j, proc.P ω * f (proc.X j ω) := by
  unfold survivingMass
  rw [← Finset.sum_fiberwise (proc.S j) (proc.X j)
    (fun ω => proc.P ω * f (proc.X j ω))]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ω hω
  rw [Finset.mem_filter] at hω
  rw [hω.2]

/-! ### The stopped action -/

theorem stoppedAction_of_mem (a : 𝒳 → ℝ) :
    ∀ j ω, ω ∈ proc.S j → proc.stoppedAction a j ω = a (proc.X j ω)
  | 0, ω, _ => rfl
  | j + 1, ω, hω => by
      simp [stoppedAction, hω]

theorem stoppedAction_succ_sub (a : 𝒳 → ℝ) (j : ℕ) (ω : Ω) :
    proc.stoppedAction a (j + 1) ω - proc.stoppedAction a j ω
      = if ω ∈ proc.S (j + 1) then a (proc.X (j + 1) ω) - a (proc.X j ω) else 0 := by
  by_cases hω : ω ∈ proc.S (j + 1)
  · rw [if_pos hω]
    have h1 : proc.stoppedAction a (j + 1) ω = a (proc.X (j + 1) ω) :=
      proc.stoppedAction_of_mem a (j + 1) ω hω
    have h2 : proc.stoppedAction a j ω = a (proc.X j ω) :=
      proc.stoppedAction_of_mem a j ω (proc.S_antitone j hω)
    rw [h1, h2]
  · rw [if_neg hω]
    simp [stoppedAction, hω]

theorem stoppedAction_bounds (a : 𝒳 → ℝ) (Am Ap : ℝ)
    (ha : ∀ x, Am ≤ a x ∧ a x ≤ Ap) :
    ∀ j ω, Am ≤ proc.stoppedAction a j ω ∧ proc.stoppedAction a j ω ≤ Ap
  | 0, ω => ha _
  | j + 1, ω => by
      by_cases hω : ω ∈ proc.S (j + 1)
      · simp only [stoppedAction, if_pos hω]
        exact ha _
      · simp only [stoppedAction, if_neg hω]
        exact stoppedAction_bounds a Am Ap ha j ω

/-- **`eq:app-stopped-drift`**: the mass-weighted drift is the expected
stopped-action increment, `Σ_x μ_j(x) 𝔡_j(x) = E[Z_{j+1} - Z_j]`. -/
theorem mass_drift_eq (a : 𝒳 → ℝ) (j : ℕ) :
    ∑ x, proc.survivingMass j x * proc.actionDrift a j x
      = ∑ ω, proc.P ω * (proc.stoppedAction a (j + 1) ω - proc.stoppedAction a j ω) := by
  -- left side as a sum over legal joint masses
  have hL : ∑ x, proc.survivingMass j x * proc.actionDrift a j x
      = ∑ ω ∈ proc.S (j + 1), proc.P ω * (a (proc.X (j + 1) ω) - a (proc.X j ω)) := by
    unfold actionDrift
    simp_rw [Finset.mul_sum, ← mul_assoc, proc.survivingMass_mul_legalKernel]
    unfold legalJoint
    rw [← Finset.sum_fiberwise (proc.S (j + 1)) (proc.X j)
      (fun ω => proc.P ω * (a (proc.X (j + 1) ω) - a (proc.X j ω)))]
    apply Finset.sum_congr rfl
    intro x _
    rw [← Finset.sum_fiberwise ((proc.S (j + 1)).filter (fun ω => proc.X j ω = x))
      (proc.X (j + 1)) (fun ω => proc.P ω * (a (proc.X (j + 1) ω) - a (proc.X j ω)))]
    apply Finset.sum_congr rfl
    intro y _
    rw [Finset.filter_filter, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro ω hω
    rw [Finset.mem_filter] at hω
    rw [hω.2.1, hω.2.2]
  rw [hL]
  simp_rw [proc.stoppedAction_succ_sub a j, mul_ite, mul_zero]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

/-- **The stopped-action telescope**: `Σ_{j<J} Σ_x μ_j(x) 𝔡_j(x) ≥ -D^A`
with `D^A = A⁺ - A⁻`; killing is recorded as failure, never as a
decrease of the signed action. -/
theorem sum_mass_drift_ge (a : 𝒳 → ℝ) (Am Ap : ℝ)
    (ha : ∀ x, Am ≤ a x ∧ a x ≤ Ap) (J : ℕ) :
    -(Ap - Am) ≤ ∑ j ∈ Finset.range J, ∑ x, proc.survivingMass j x * proc.actionDrift a j x := by
  simp_rw [proc.mass_drift_eq a]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  rw [show (∑ ω, proc.P ω * ∑ j ∈ Finset.range J,
      (proc.stoppedAction a (j + 1) ω - proc.stoppedAction a j ω))
      = ∑ ω, proc.P ω * (proc.stoppedAction a J ω - proc.stoppedAction a 0 ω) by
    apply Finset.sum_congr rfl
    intro ω _
    rw [Finset.sum_range_sub (fun j => proc.stoppedAction a j ω)]]
  have h1 : ∑ ω, proc.P ω * (Am - Ap) ≤
      ∑ ω, proc.P ω * (proc.stoppedAction a J ω - proc.stoppedAction a 0 ω) := by
    apply Finset.sum_le_sum
    intro ω _
    apply mul_le_mul_of_nonneg_left _ (proc.P_nonneg ω)
    have hJ := proc.stoppedAction_bounds a Am Ap ha J ω
    have h0 := proc.stoppedAction_bounds a Am Ap ha 0 ω
    linarith
  rw [← Finset.sum_mul, proc.P_sum, one_mul] at h1
  linarith

/-! ### The occupation slope bound -/

/-- **`eq:source-slope-occupation`** (`eq:app-slope-telescope`): if every
active legal row (`μ_j(x) > 0`, `j < J`) satisfies the signed drift
inequality `𝔡_j(x) ≤ -κ_A δ g(x)² + δ r_j(x)`, then
`(1/J) Σ_{j<J,x} μ_j(x) g(x)² ≤ D^A/(κ_A δ J) + ℛ_{h,J}/κ_A`. -/
theorem slope_occupation (a g : 𝒳 → ℝ) (r : ℕ → 𝒳 → ℝ) (Am Ap κ δ : ℝ)
    (ha : ∀ x, Am ≤ a x ∧ a x ≤ Ap) (hκ : 0 < κ) (hδ : 0 < δ)
    (J : ℕ) (hJ : 0 < J)
    (hdrift : ∀ j < J, ∀ x, 0 < proc.survivingMass j x →
      proc.actionDrift a j x ≤ -(κ * δ) * g x ^ 2 + δ * r j x) :
    proc.occupation J (fun _ x => g x ^ 2)
      ≤ (Ap - Am) / (κ * δ * J) + proc.occupation J r / κ := by
  have htel := proc.sum_mass_drift_ge a Am Ap ha J
  have hrow : ∀ j ∈ Finset.range J, ∀ x,
      proc.survivingMass j x * proc.actionDrift a j x
        ≤ proc.survivingMass j x * (-(κ * δ) * g x ^ 2 + δ * r j x) := by
    intro j hj x
    rcases (proc.survivingMass_nonneg j x).lt_or_eq with hpos | hzero
    · exact mul_le_mul_of_nonneg_left (hdrift j (Finset.mem_range.mp hj) x hpos) hpos.le
    · rw [← hzero]
      simp
  have hsum : ∑ j ∈ Finset.range J, ∑ x, proc.survivingMass j x * proc.actionDrift a j x
      ≤ ∑ j ∈ Finset.range J, ∑ x,
          proc.survivingMass j x * (-(κ * δ) * g x ^ 2 + δ * r j x) := by
    apply Finset.sum_le_sum
    intro j hj
    apply Finset.sum_le_sum
    intro x _
    exact hrow j hj x
  have hsplit : ∑ j ∈ Finset.range J, ∑ x,
      proc.survivingMass j x * (-(κ * δ) * g x ^ 2 + δ * r j x)
      = -(κ * δ) * (∑ j ∈ Finset.range J, ∑ x, proc.survivingMass j x * g x ^ 2)
        + δ * (∑ j ∈ Finset.range J, ∑ x, proc.survivingMass j x * r j x) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hsplit] at hsum
  set G := ∑ j ∈ Finset.range J, ∑ x, proc.survivingMass j x * g x ^ 2 with hG
  set R := ∑ j ∈ Finset.range J, ∑ x, proc.survivingMass j x * r j x with hR
  have hkey : κ * δ * G ≤ (Ap - Am) + δ * R := by linarith
  have hJpos : (0:ℝ) < J := by exact_mod_cast hJ
  unfold occupation
  rw [← hG, ← hR]
  rw [show (1 / (J:ℝ)) * G = G / J by ring,
    show (Ap - Am) / (κ * δ * J) + (1 / (J:ℝ)) * R / κ
      = ((Ap - Am) + δ * R) / (κ * δ * J) by field_simp]
  rw [div_le_div_iff₀ hJpos (by positivity)]
  nlinarith

/-! ### The same-record selection bound -/

/-- The selection score `eq:source-score`. -/
noncomputable def score (g V W : 𝒳 → ℝ) (s R α : ℝ) (x : 𝒳) : ℝ :=
  g x ^ 2 / s ^ 2 + V x / R ^ 2 + W x / α ^ 2

/-- A score `≤ 1` forces all three thresholds `eq:source-selected`. -/
theorem thresholds_of_score_le_one (g V W : 𝒳 → ℝ) (s R α : ℝ)
    (hs : 0 < s) (hR : 0 < R) (hα : 0 < α)
    (hg : ∀ x, 0 ≤ g x) (hV : ∀ x, 0 ≤ V x) (hW : ∀ x, 0 ≤ W x)
    (x : 𝒳) (hx : score g V W s R α x ≤ 1) :
    g x ≤ s ∧ V x ≤ R ^ 2 ∧ W x ≤ α ^ 2 := by
  unfold score at hx
  have h1 : 0 ≤ g x ^ 2 / s ^ 2 := by positivity
  have h2 : 0 ≤ V x / R ^ 2 := div_nonneg (hV x) (by positivity)
  have h3 : 0 ≤ W x / α ^ 2 := div_nonneg (hW x) (by positivity)
  refine ⟨?_, ?_, ?_⟩
  · have : g x ^ 2 / s ^ 2 ≤ 1 := by linarith
    rw [div_le_one (by positivity)] at this
    exact pow_le_pow_iff_left₀ (hg x) hs.le (by norm_num) |>.mp this
  · have : V x / R ^ 2 ≤ 1 := by linarith
    exact (div_le_one (by positivity : (0:ℝ) < R ^ 2)).mp this
  · have : W x / α ^ 2 ≤ 1 := by linarith
    exact (div_le_one (by positivity : (0:ℝ) < α ^ 2)).mp this

/-- The occupation of the score splits into the three occupations
`eq:source-occupations`. -/
theorem occupation_score_eq (g V W : 𝒳 → ℝ) (s R α : ℝ) (J : ℕ) :
    proc.occupation J (fun _ x => score g V W s R α x)
      = proc.occupation J (fun _ x => g x ^ 2) / s ^ 2
        + proc.occupation J (fun _ x => V x) / R ^ 2
        + proc.occupation J (fun _ x => W x) / α ^ 2 := by
  unfold occupation
  simp only [score]
  have h : ∀ j, ∑ x, proc.survivingMass j x * (g x ^ 2 / s ^ 2 + V x / R ^ 2 + W x / α ^ 2)
      = (∑ x, proc.survivingMass j x * g x ^ 2) / s ^ 2
        + (∑ x, proc.survivingMass j x * V x) / R ^ 2
        + (∑ x, proc.survivingMass j x * W x) / α ^ 2 := by
    intro j
    rw [Finset.sum_div, Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    ring
  simp_rw [h]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div,
    ← Finset.sum_div]
  ring

/-- **`thm:source-selection`, `eq:source-selection-failure`.**  Under the
drift inequality on active legal rows, for thresholds `s, R, α > 0` and
any selection rule `sel` that on every surviving prefix returns an
observed index `< J` minimising the score `eq:source-score`, the
probability of failing to output one observed record with
`g ≤ s`, `V ≤ R²`, `W ≤ α²` is at most
`p^{exit} + D^A/(κ_A δ J s²) + ℛ_{h,J}/(κ_A s²) + M_{h,J}/R² + A_{h,J}/α²`. -/
theorem selection_failure_le (a g V W : 𝒳 → ℝ) (r : ℕ → 𝒳 → ℝ)
    (Am Ap κ δ s R α : ℝ)
    (ha : ∀ x, Am ≤ a x ∧ a x ≤ Ap) (hκ : 0 < κ) (hδ : 0 < δ)
    (hs : 0 < s) (hR : 0 < R) (hα : 0 < α)
    (hg : ∀ x, 0 ≤ g x) (hV : ∀ x, 0 ≤ V x) (hW : ∀ x, 0 ≤ W x)
    (J : ℕ) (hJ : 0 < J)
    (hdrift : ∀ j < J, ∀ x, 0 < proc.survivingMass j x →
      proc.actionDrift a j x ≤ -(κ * δ) * g x ^ 2 + δ * r j x)
    (sel : Ω → ℕ)
    (hsel : ∀ ω ∈ proc.S J, sel ω < J ∧
      ∀ j < J, score g V W s R α (proc.X (sel ω) ω) ≤ score g V W s R α (proc.X j ω)) :
    ∑ ω ∈ Finset.univ.filter (fun ω => ω ∉ proc.S J ∨
        ¬ (g (proc.X (sel ω) ω) ≤ s ∧ V (proc.X (sel ω) ω) ≤ R ^ 2
            ∧ W (proc.X (sel ω) ω) ≤ α ^ 2)), proc.P ω
      ≤ proc.exitProbability J
        + (Ap - Am) / (κ * δ * J * s ^ 2)
        + proc.occupation J r / (κ * s ^ 2)
        + proc.occupation J (fun _ x => V x) / R ^ 2
        + proc.occupation J (fun _ x => W x) / α ^ 2 := by
  have hJpos : (0:ℝ) < J := by exact_mod_cast hJ
  set Fail : Finset Ω := Finset.univ.filter (fun ω => ω ∉ proc.S J ∨
    ¬ (g (proc.X (sel ω) ω) ≤ s ∧ V (proc.X (sel ω) ω) ≤ R ^ 2
        ∧ W (proc.X (sel ω) ω) ≤ α ^ 2)) with hFail
  -- split the failure set into exit and surviving failure
  have hsplit : ∑ ω ∈ Fail, proc.P ω
      ≤ ∑ ω ∈ Finset.univ.filter (fun ω => ω ∉ proc.S J), proc.P ω
        + ∑ ω ∈ Fail.filter (fun ω => ω ∈ proc.S J), proc.P ω := by
    rw [← Finset.sum_filter_add_sum_filter_not Fail (fun ω => ω ∈ proc.S J)]
    have hsub : ∑ ω ∈ Fail.filter (fun ω => ¬ ω ∈ proc.S J), proc.P ω
        ≤ ∑ ω ∈ Finset.univ.filter (fun ω => ω ∉ proc.S J), proc.P ω := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro ω hω
        rw [Finset.mem_filter] at hω ⊢
        exact ⟨Finset.mem_univ _, hω.2⟩
      · intro ω _ _
        exact proc.P_nonneg ω
    linarith
  -- the exit term
  have hexit : ∑ ω ∈ Finset.univ.filter (fun ω => ω ∉ proc.S J), proc.P ω
      = proc.exitProbability J := by
    unfold exitProbability
    rw [proc.sum_survivingMass J]
    have := Finset.sum_filter_add_sum_filter_not Finset.univ (fun ω => ω ∈ proc.S J) proc.P
    rw [proc.P_sum] at this
    have h2 : ∑ ω ∈ Finset.univ.filter (fun ω => ω ∈ proc.S J), proc.P ω
        = ∑ ω ∈ proc.S J, proc.P ω := by
      apply Finset.sum_congr
      · ext ω
        simp
      · intros; rfl
    linarith
  -- surviving failure forces mean score > 1
  have hmean : ∀ ω ∈ Fail.filter (fun ω => ω ∈ proc.S J),
      (1:ℝ) ≤ (1 / (J:ℝ)) * ∑ j ∈ Finset.range J, score g V W s R α (proc.X j ω) := by
    intro ω hω
    rw [Finset.mem_filter, hFail, Finset.mem_filter] at hω
    obtain ⟨⟨_, hfail⟩, hS⟩ := hω
    obtain ⟨hselJ, hmin⟩ := hsel ω hS
    have hbig : 1 < score g V W s R α (proc.X (sel ω) ω) := by
      by_contra hle
      push Not at hle
      rcases hfail with hfail | hfail
      · exact hfail hS
      · exact hfail (thresholds_of_score_le_one g V W s R α hs hR hα hg hV hW _ hle)
    have hterm : ∀ j ∈ Finset.range J,
        score g V W s R α (proc.X (sel ω) ω) ≤ score g V W s R α (proc.X j ω) :=
      fun j hj => hmin j (Finset.mem_range.mp hj)
    have hs' := Finset.sum_le_sum hterm
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hs'
    rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hJpos]
    nlinarith
  have hscore_nn : ∀ x, 0 ≤ score g V W s R α x := by
    intro x
    unfold score
    have := hg x; have := hV x; have := hW x
    positivity
  -- Markov step on the finite space
  have hmarkov : ∑ ω ∈ Fail.filter (fun ω => ω ∈ proc.S J), proc.P ω
      ≤ (1 / (J:ℝ)) * ∑ j ∈ Finset.range J, ∑ ω ∈ proc.S j,
          proc.P ω * score g V W s R α (proc.X j ω) := by
    calc ∑ ω ∈ Fail.filter (fun ω => ω ∈ proc.S J), proc.P ω
        ≤ ∑ ω ∈ Fail.filter (fun ω => ω ∈ proc.S J),
            proc.P ω * ((1 / (J:ℝ)) * ∑ j ∈ Finset.range J,
              score g V W s R α (proc.X j ω)) := by
          apply Finset.sum_le_sum
          intro ω hω
          have := hmean ω hω
          have hp := proc.P_nonneg ω
          nlinarith
      _ ≤ ∑ ω ∈ proc.S J,
            proc.P ω * ((1 / (J:ℝ)) * ∑ j ∈ Finset.range J,
              score g V W s R α (proc.X j ω)) := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro ω hω
            exact (Finset.mem_filter.mp hω).2
          · intro ω _ _
            have := proc.P_nonneg ω
            have : 0 ≤ ∑ j ∈ Finset.range J, score g V W s R α (proc.X j ω) :=
              Finset.sum_nonneg fun j _ => hscore_nn _
            positivity
      _ = ∑ ω ∈ proc.S J, ∑ j ∈ Finset.range J,
            (1 / (J:ℝ)) * (proc.P ω * score g V W s R α (proc.X j ω)) := by
          apply Finset.sum_congr rfl
          intro ω _
          rw [Finset.mul_sum, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
      _ = ∑ j ∈ Finset.range J, ∑ ω ∈ proc.S J,
            (1 / (J:ℝ)) * (proc.P ω * score g V W s R α (proc.X j ω)) :=
          Finset.sum_comm
      _ = (1 / (J:ℝ)) * ∑ j ∈ Finset.range J, ∑ ω ∈ proc.S J,
            proc.P ω * score g V W s R α (proc.X j ω) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.mul_sum]
      _ ≤ (1 / (J:ℝ)) * ∑ j ∈ Finset.range J, ∑ ω ∈ proc.S j,
            proc.P ω * score g V W s R α (proc.X j ω) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply Finset.sum_le_sum
          intro j hj
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact proc.S_subset_of_le (Finset.mem_range.mp hj).le
          · intro ω _ _
            have := proc.P_nonneg ω
            have := hscore_nn (proc.X j ω)
            positivity
  -- identify the mean score with the occupations
  have hocc : (1 / (J:ℝ)) * ∑ j ∈ Finset.range J, ∑ ω ∈ proc.S j,
      proc.P ω * score g V W s R α (proc.X j ω)
      = proc.occupation J (fun _ x => g x ^ 2) / s ^ 2
        + proc.occupation J (fun _ x => V x) / R ^ 2
        + proc.occupation J (fun _ x => W x) / α ^ 2 := by
    have h1 : (1 / (J:ℝ)) * ∑ j ∈ Finset.range J, ∑ ω ∈ proc.S j,
        proc.P ω * score g V W s R α (proc.X j ω)
        = proc.occupation J (fun _ x => score g V W s R α x) := by
      unfold occupation
      simp_rw [← proc.sum_survivingMass_mul]
    rw [h1]
    exact proc.occupation_score_eq g V W s R α J
  have hslope := proc.slope_occupation a g r Am Ap κ δ ha hκ hδ J hJ hdrift
  have hs2 : 0 < s ^ 2 := by positivity
  have hslope' : proc.occupation J (fun _ x => g x ^ 2) / s ^ 2
      ≤ (Ap - Am) / (κ * δ * J * s ^ 2) + proc.occupation J r / (κ * s ^ 2) := by
    rw [show (Ap - Am) / (κ * δ * J * s ^ 2) + proc.occupation J r / (κ * s ^ 2)
        = ((Ap - Am) / (κ * δ * J) + proc.occupation J r / κ) / s ^ 2 by
      field_simp]
    exact div_le_div_of_nonneg_right hslope hs2.le
  calc ∑ ω ∈ Fail, proc.P ω
      ≤ _ := hsplit
    _ ≤ proc.exitProbability J + (proc.occupation J (fun _ x => g x ^ 2) / s ^ 2
        + proc.occupation J (fun _ x => V x) / R ^ 2
        + proc.occupation J (fun _ x => W x) / α ^ 2) := by
        rw [hexit, ← hocc]
        gcongr
    _ ≤ _ := by linarith

end FiniteAcceptedProcess
end SourceSelection
end RenewalGeometry
