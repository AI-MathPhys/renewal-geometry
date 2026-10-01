/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.GowdySplittingSecondOrderConsistency
import RenewalGeometry.Analysis.PeriodicGridResidualInverseEstimate

/-!
# Characteristic-norm stability of the Gowdy split map and the sup-norm global error
  (`prop:supp-gowdy-residual-control`, case `r = 0` of `eq:supp-gowdy-state-error`;
  nodal time differences used in `thm:supp-gowdy-full-curvature`; emergent-spacetime
  supplement)

In the plain sup norm of the local state `(U, P, Q, t)` the transport shift
`Π₊ X_{j+1} + Π₋ X_{j-1} + Π₀ X_j` of the Gowdy scheme has Lipschitz constant up to `2`, so it
cannot feed a discrete Grönwall argument.  This file introduces the **characteristic norm**

`charNorm v = max (‖Π₊ v‖, ‖Π₋ v‖, ‖Π₀ v‖)`

(`Π₊, Π₋, Π₀` the projections onto the right-moving `w⁺`, left-moving `w⁻` and non-moving
`(P, Q, t)` parts), which is equivalent to the sup norm (`charNorm_le_norm`,
`norm_le_three_mul_charNorm`), and in which the transport shift is nonexpansive.  On the
periodic grid `ZMod N` the grid distance is
`charDist X Y = max_j max (charNorm (X_j - Y_j), |λ_j - λ'_j|)`.

* `charNorm_midpointStep`: an implicit-midpoint source step of duration `σ` with an
  `L`-Lipschitz field on a chart containing the midpoints is `(1 + 6σL)`-Lipschitz in
  `charNorm` (for `3σL ≤ 1`), and its increment is `6σL`-Lipschitz.
* `charDist_sourceStep`, `charDist_transport`: grid source steps are `(1 + 6σL)`-Lipschitz and
  the transport `eq:supp-gowdy-transport` is `(1 + 16Rℓ)`-Lipschitz in `charDist` on states with
  `‖X_j‖ ≤ R` (the background increment is `ℓ/2` times differences of `g± = |w±|²`).
* `charDist_splitStep` (**`(1 + Kℓ)`-Lipschitz bound of the split map**): the
  source-half / transport / source-half step with `h = ℓ` is `(1 + (9L + 64R)ℓ)`-Lipschitz in
  `charDist` on the envelope `SplitEnvelope` (stage midpoints in the Gowdy chart
  `{t ≥ t₀', |u_i| ≤ R, |P| ≤ R}` with `L = gowdyLipschitz t₀' R`, transported inputs of norm
  `≤ R`).
* `projZero_increment_splitStep`, `lam_increment_splitStep`: `Φ_h - id` is `O(h)`-Lipschitz in the
  `(P, Q, t)` and `λ` components.
* `GowdyFrameSolution.state_error_charDist` (**`eq:supp-gowdy-state-error` for `r = 0`**): for a
  `C³` solution of the frame system on `[t₀, t₁] × 𝕋¹` and every envelope radius
  `R ≥ chartRadius`, there are `C, K, ℓ₀` such that every numerical history
  `X_{n+1} = Φ_h(X_n) + r_n` (realised by split steps `X_n → A_n → B_n` in the envelope) obeys
  `charDist(X_n, 𝖲_ℓ X_*(τ₀ + nℓ)) ≤ (ε₀ + Σ_{k<n} charDist(X_{k+1}, B_k) + C T ℓ²) e^{K T}`,
  `T = t₁ - t₀`; `state_error_sup` is the same estimate for the sup norm `‖·‖_{0,∞,ℓ}` of the
  error arrays in `(U,P,Q,t,λ)`, with the residual sum replaced by `√(2nh) √𝓕_h`
  (`eq:supp-gowdy-residual-energy`, `r = 0`).
* `GowdyFrameSolution.nodal_time_difference`: the nodal time differences of the errors in
  `P, Q, λ` (and `t`) obey `|Δ_t e| ≤ Kℓ · charDist(e_n) + charDist(X_{n+1}, B_n) + C ℓ³`, the
  bound "subtraction of the reference step and division by `h`" of the manuscript.

The enforced envelope is a hypothesis on the numerical history (the manuscript's "smallness
bootstrap or enforced offset envelope"); the reference history is shown to lie in it.
-/

open Set Finset
open scoped BigOperators

set_option linter.unusedSectionVars false

namespace RenewalGeometry.GowdyStaggered

namespace CharStability

noncomputable section

/-! ### The characteristic norm of a local state -/

/-- The characteristic norm `max (‖Π₊ v‖, ‖Π₋ v‖, ‖Π₀ v‖)` of a local state vector. -/
def charNorm (v : StateVec) : ℝ := max ‖projPlus v‖ (max ‖projMinus v‖ ‖projZero v‖)

theorem charNorm_nonneg (v : StateVec) : 0 ≤ charNorm v :=
  (norm_nonneg _).trans (le_max_left _ _)

theorem norm_projPlus_le_charNorm (v : StateVec) : ‖projPlus v‖ ≤ charNorm v := le_max_left _ _

theorem norm_projMinus_le_charNorm (v : StateVec) : ‖projMinus v‖ ≤ charNorm v :=
  (le_max_left _ _).trans (le_max_right _ _)

theorem norm_projZero_le_charNorm (v : StateVec) : ‖projZero v‖ ≤ charNorm v :=
  (le_max_right _ _).trans (le_max_right _ _)

/-- The characteristic norm is dominated by the sup norm. -/
theorem charNorm_le_norm (v : StateVec) : charNorm v ≤ ‖v‖ :=
  max_le (norm_projPlus_le v) (max_le (norm_projMinus_le v) (norm_projZero_le v))

/-- The sup norm is at most three times the characteristic norm. -/
theorem norm_le_three_mul_charNorm (v : StateVec) : ‖v‖ ≤ 3 * charNorm v := by
  have hs := proj_sum v
  calc ‖v‖ = ‖projPlus v + projMinus v + projZero v‖ := by rw [hs]
    _ ≤ ‖projPlus v‖ + ‖projMinus v‖ + ‖projZero v‖ := norm_add₃_le
    _ ≤ 3 * charNorm v := by
        linarith [norm_projPlus_le_charNorm v, norm_projMinus_le_charNorm v,
          norm_projZero_le_charNorm v]

theorem charNorm_add_le (v w : StateVec) : charNorm (v + w) ≤ charNorm v + charNorm w := by
  unfold charNorm
  simp only [map_add]
  refine max_le ?_ (max_le ?_ ?_)
  · exact (norm_add_le _ _).trans (add_le_add (le_max_left _ _) (le_max_left _ _))
  · exact (norm_add_le _ _).trans (add_le_add ((le_max_left _ _).trans (le_max_right _ _))
      ((le_max_left _ _).trans (le_max_right _ _)))
  · exact (norm_add_le _ _).trans (add_le_add ((le_max_right _ _).trans (le_max_right _ _))
      ((le_max_right _ _).trans (le_max_right _ _)))

theorem charNorm_neg (v : StateVec) : charNorm (-v) = charNorm v := by
  simp [charNorm, map_neg, norm_neg]

theorem charNorm_sub_le (v w : StateVec) : charNorm (v - w) ≤ charNorm v + charNorm w := by
  rw [sub_eq_add_neg]
  exact (charNorm_add_le _ _).trans (by rw [charNorm_neg])

theorem charNorm_sub_comm (v w : StateVec) : charNorm (v - w) = charNorm (w - v) := by
  rw [← neg_sub, charNorm_neg]

theorem charNorm_smul (c : ℝ) (v : StateVec) : charNorm (c • v) = |c| * charNorm v := by
  unfold charNorm
  simp only [map_smul, norm_smul, Real.norm_eq_abs]
  rw [mul_max_of_nonneg _ _ (abs_nonneg c), mul_max_of_nonneg _ _ (abs_nonneg c)]

/-! ### Projection identities -/

theorem projPlus_projPlus (v : StateVec) : projPlus (projPlus v) = projPlus v := by
  rw [projPlus_apply, projPlus_apply]
  refine Prod.ext ?_ (by simp)
  funext i; fin_cases i <;> simp

theorem projPlus_projMinus (v : StateVec) : projPlus (projMinus v) = 0 := by
  rw [projPlus_apply, projMinus_apply]
  refine Prod.ext ?_ (by simp)
  funext i; fin_cases i <;> simp

theorem projPlus_projZero (v : StateVec) : projPlus (projZero v) = 0 := by
  rw [projPlus_apply, projZero_apply]
  refine Prod.ext ?_ (by simp)
  funext i; fin_cases i <;> simp

theorem projMinus_projPlus (v : StateVec) : projMinus (projPlus v) = 0 := by
  rw [projMinus_apply, projPlus_apply]
  refine Prod.ext ?_ (by simp)
  funext i; fin_cases i <;> simp

theorem projMinus_projMinus (v : StateVec) : projMinus (projMinus v) = projMinus v := by
  rw [projMinus_apply, projMinus_apply]
  refine Prod.ext ?_ (by simp)
  funext i; fin_cases i <;> simp

theorem projMinus_projZero (v : StateVec) : projMinus (projZero v) = 0 := by
  rw [projMinus_apply, projZero_apply]
  refine Prod.ext ?_ (by simp)
  funext i; fin_cases i <;> simp

theorem projZero_projPlus (v : StateVec) : projZero (projPlus v) = 0 := by
  rw [projZero_apply, projPlus_apply]; rfl

theorem projZero_projMinus (v : StateVec) : projZero (projMinus v) = 0 := by
  rw [projZero_apply, projMinus_apply]; rfl

theorem projZero_projZero (v : StateVec) : projZero (projZero v) = projZero v := by
  rw [projZero_apply, projZero_apply]

/-- **The characteristic shift is nonexpansive** in the characteristic norm:
`charNorm (Π₊a + Π₋b + Π₀c) ≤ max (charNorm a, charNorm b, charNorm c)`. -/
theorem charNorm_shift_le (a b c : StateVec) {D : ℝ} (ha : charNorm a ≤ D)
    (hb : charNorm b ≤ D) (hc : charNorm c ≤ D) :
    charNorm (projPlus a + projMinus b + projZero c) ≤ D := by
  unfold charNorm
  simp only [map_add, projPlus_projPlus, projPlus_projMinus, projPlus_projZero,
    projMinus_projPlus, projMinus_projMinus, projMinus_projZero, projZero_projPlus,
    projZero_projMinus, projZero_projZero, add_zero, zero_add]
  exact max_le ((norm_projPlus_le_charNorm a).trans ha)
    (max_le ((norm_projMinus_le_charNorm b).trans hb) ((norm_projZero_le_charNorm c).trans hc))

/-! ### One implicit-midpoint source step -/

/-- **Characteristic-norm stability of one implicit-midpoint step.**  If `F` is `L`-Lipschitz
on a set `G` containing the midpoints of two implicit-midpoint steps
`Y = X + σ F((X+Y)/2)`, `Y' = X' + σ F((X'+Y')/2)` and `3σL ≤ 1`, then
`charNorm (Y - Y') ≤ (1 + 6σL) charNorm (X - X')` and the increments satisfy
`‖(Y - X) - (Y' - X')‖ ≤ 6σL charNorm (X - X')`. -/
theorem charNorm_midpointStep {F : StateVec → StateVec} {G : Set StateVec} {L σ : ℝ}
    (hL : ∀ x ∈ G, ∀ y ∈ G, ‖F x - F y‖ ≤ L * ‖x - y‖) (hL0 : 0 ≤ L) (hσ : 0 ≤ σ)
    (hσL : 3 * σ * L ≤ 1) {X Y X' Y' : StateVec}
    (hY : Y = X + σ • F ((1 / 2 : ℝ) • (X + Y))) (hY' : Y' = X' + σ • F ((1 / 2 : ℝ) • (X' + Y')))
    (hm : (1 / 2 : ℝ) • (X + Y) ∈ G) (hm' : (1 / 2 : ℝ) • (X' + Y') ∈ G) :
    charNorm (Y - Y') ≤ (1 + 6 * σ * L) * charNorm (X - X') ∧
      ‖(Y - X) - (Y' - X')‖ ≤ 6 * σ * L * charNorm (X - X') := by
  set m := (1 / 2 : ℝ) • (X + Y)
  set m' := (1 / 2 : ℝ) • (X' + Y')
  set a := charNorm (X - X')
  set b := charNorm (Y - Y')
  have ha := charNorm_nonneg (X - X')
  have hb := charNorm_nonneg (Y - Y')
  have hmm : m - m' = (1 / 2 : ℝ) • ((X - X') + (Y - Y')) := by
    simp only [m, m']; module
  have hcm : charNorm (m - m') ≤ (a + b) / 2 := by
    rw [hmm, charNorm_smul]
    have := charNorm_add_le (X - X') (Y - Y')
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    linarith
  have hd : ‖F m - F m'‖ ≤ 3 * L * ((a + b) / 2) := by
    calc ‖F m - F m'‖ ≤ L * ‖m - m'‖ := hL _ hm _ hm'
      _ ≤ L * (3 * charNorm (m - m')) :=
          mul_le_mul_of_nonneg_left (norm_le_three_mul_charNorm _) hL0
      _ ≤ L * (3 * ((a + b) / 2)) := by gcongr
      _ = 3 * L * ((a + b) / 2) := by ring
  have hinc : (Y - X) - (Y' - X') = σ • (F m - F m') := by
    have e1 : Y - X = σ • F m := by rw [hY]; abel
    have e2 : Y' - X' = σ • F m' := by rw [hY']; abel
    rw [e1, e2, smul_sub]
  have hincn : ‖(Y - X) - (Y' - X')‖ ≤ σ * (3 * L * ((a + b) / 2)) := by
    rw [hinc, norm_smul, Real.norm_eq_abs, abs_of_nonneg hσ]
    exact mul_le_mul_of_nonneg_left hd hσ
  have hYY : Y - Y' = (X - X') + ((Y - X) - (Y' - X')) := by abel
  have hb' : b ≤ a + σ * (3 * L * ((a + b) / 2)) := by
    calc b = charNorm ((X - X') + ((Y - X) - (Y' - X'))) := by rw [← hYY]
      _ ≤ a + charNorm ((Y - X) - (Y' - X')) := charNorm_add_le _ _
      _ ≤ a + ‖(Y - X) - (Y' - X')‖ := by gcongr; exact charNorm_le_norm _
      _ ≤ a + σ * (3 * L * ((a + b) / 2)) := by gcongr
  -- solve the linear inequality `b (1 - c) ≤ a (1 + c)`, `c = 3σL/2 ≤ 1/2`
  have hc0 : 0 ≤ σ * L := mul_nonneg hσ hL0
  have hkey : b * (1 - 3 * (σ * L) / 2) ≤ a * (1 + 3 * (σ * L) / 2) := by nlinarith
  have hb2 : b ≤ (1 + 6 * σ * L) * a := by
    have h1 : 0 < 1 - 3 * (σ * L) / 2 := by nlinarith
    have h2 : a * (1 + 3 * (σ * L) / 2) ≤ (1 + 6 * σ * L) * a * (1 - 3 * (σ * L) / 2) := by
      have : 0 ≤ a * (σ * L) * (3 - 9 * (σ * L)) := by
        apply mul_nonneg (mul_nonneg ha hc0); nlinarith
      nlinarith
    exact le_of_mul_le_mul_right (hkey.trans h2) h1
  refine ⟨hb2, hincn.trans ?_⟩
  have : σ * (3 * L * ((a + b) / 2)) ≤ σ * (3 * L * ((a + (1 + 6 * σ * L) * a) / 2)) := by
    gcongr
  refine this.trans ?_
  have : 0 ≤ a * (σ * L) * (1 - 3 * (σ * L)) := mul_nonneg (mul_nonneg ha hc0) (by nlinarith)
  nlinarith

/-! ### The grid characteristic distance -/

variable {N : ℕ} [NeZero N]

/-- The grid characteristic distance
`charDist X Y = max_j max (charNorm (X_j - Y_j), |λ_j - λ'_j|)` of two Gowdy grid states. -/
def charDist (X Y : GridState N) : ℝ :=
  univ.sup' univ_nonempty fun j =>
    max (charNorm ((X.site j).toVec - (Y.site j).toVec)) |X.lam j - Y.lam j|

theorem charNorm_le_charDist (X Y : GridState N) (j : ZMod N) :
    charNorm ((X.site j).toVec - (Y.site j).toVec) ≤ charDist X Y :=
  (le_max_left _ _).trans (Finset.le_sup' (fun j => max (charNorm ((X.site j).toVec -
    (Y.site j).toVec)) |X.lam j - Y.lam j|) (mem_univ j))

theorem abs_lam_le_charDist (X Y : GridState N) (j : ZMod N) :
    |X.lam j - Y.lam j| ≤ charDist X Y :=
  (le_max_right _ _).trans (Finset.le_sup' (fun j => max (charNorm ((X.site j).toVec -
    (Y.site j).toVec)) |X.lam j - Y.lam j|) (mem_univ j))

theorem charDist_nonneg (X Y : GridState N) : 0 ≤ charDist X Y :=
  (abs_nonneg _).trans (abs_lam_le_charDist X Y 0)

theorem charDist_le {X Y : GridState N} {c : ℝ}
    (hs : ∀ j, charNorm ((X.site j).toVec - (Y.site j).toVec) ≤ c)
    (hl : ∀ j, |X.lam j - Y.lam j| ≤ c) : charDist X Y ≤ c :=
  Finset.sup'_le _ _ fun j _ => max_le (hs j) (hl j)

theorem charDist_comm (X Y : GridState N) : charDist X Y = charDist Y X := by
  unfold charDist
  congr 1; funext j
  rw [charNorm_sub_comm, abs_sub_comm]

theorem charDist_triangle (X Y Z : GridState N) :
    charDist X Z ≤ charDist X Y + charDist Y Z := by
  refine charDist_le (fun j => ?_) (fun j => ?_)
  · have e : (X.site j).toVec - (Z.site j).toVec =
        ((X.site j).toVec - (Y.site j).toVec) + ((Y.site j).toVec - (Z.site j).toVec) := by abel
    rw [e]
    exact (charNorm_add_le _ _).trans (add_le_add (charNorm_le_charDist X Y j)
      (charNorm_le_charDist Y Z j))
  · have e : X.lam j - Z.lam j = (X.lam j - Y.lam j) + (Y.lam j - Z.lam j) := by ring
    rw [e]
    exact (abs_add_le _ _).trans (add_le_add (abs_lam_le_charDist X Y j)
      (abs_lam_le_charDist Y Z j))

/-- Sup-norm sites are controlled by the characteristic distance:
`‖X_j - Y_j‖ ≤ 3 charDist X Y`. -/
theorem norm_site_sub_le_charDist (X Y : GridState N) (j : ZMod N) :
    ‖(X.site j).toVec - (Y.site j).toVec‖ ≤ 3 * charDist X Y :=
  (norm_le_three_mul_charNorm _).trans (by linarith [charNorm_le_charDist X Y j])

/-! ### Grid source steps -/

theorem toVec_of_sourceStep {σ : ℝ} {X A : GridState N} (h : IsSourceStep σ X A) (j : ZMod N) :
    (A.site j).toVec = (X.site j).toVec +
      σ • localFieldVec ((1 / 2 : ℝ) • ((X.site j).toVec + (A.site j).toVec)) :=
  (isMidpointStep_iff_toVec _ _ _).1 (h.1 j)

/-- **Grid source steps are `(1 + 6σL)`-Lipschitz in `charDist`**, and their site increments are
`6σL`-Lipschitz, when the source field is `L`-Lipschitz on a set containing all midpoints. -/
theorem charDist_sourceStep {G : Set StateVec} {L σ : ℝ}
    (hL : ∀ x ∈ G, ∀ y ∈ G, ‖localFieldVec x - localFieldVec y‖ ≤ L * ‖x - y‖) (hL0 : 0 ≤ L)
    (hσ : 0 ≤ σ) (hσL : 3 * σ * L ≤ 1) {X A X' A' : GridState N} (h : IsSourceStep σ X A)
    (h' : IsSourceStep σ X' A')
    (hm : ∀ j, (1 / 2 : ℝ) • ((X.site j).toVec + (A.site j).toVec) ∈ G)
    (hm' : ∀ j, (1 / 2 : ℝ) • ((X'.site j).toVec + (A'.site j).toVec) ∈ G) :
    charDist A A' ≤ (1 + 6 * σ * L) * charDist X X' ∧
      ∀ j, ‖((A.site j).toVec - (X.site j).toVec) - ((A'.site j).toVec - (X'.site j).toVec)‖ ≤
        6 * σ * L * charDist X X' := by
  have hc : 0 ≤ 6 * σ * L := by positivity
  have hD := charDist_nonneg X X'
  have key := fun j => charNorm_midpointStep hL hL0 hσ hσL (toVec_of_sourceStep h j)
    (toVec_of_sourceStep h' j) (hm j) (hm' j)
  refine ⟨charDist_le (fun j => ?_) (fun j => ?_), fun j => ?_⟩
  · exact (key j).1.trans (mul_le_mul_of_nonneg_left (charNorm_le_charDist X X' j) (by linarith))
  · rw [h.2, h'.2]
    have := abs_lam_le_charDist X X' j
    nlinarith
  · exact (key j).2.trans (mul_le_mul_of_nonneg_left (charNorm_le_charDist X X' j) hc)

/-! ### The transport map -/

theorem transport_lam_apply (ℓ : ℝ) (X : GridState N) (j : ZMod N) :
    (transport ℓ X).lam j = X.lam j + ℓ / 2 *
      ((densPlus (X.site j).toVec + densPlus (X.site (j + 1)).toVec) +
        (densMinus (X.site j).toVec + densMinus (X.site (j - 1)).toVec)) := rfl

theorem transport_site_sub (ℓ : ℝ) (X X' : GridState N) (j : ZMod N) :
    ((transport ℓ X).site j).toVec - ((transport ℓ X').site j).toVec =
      projPlus ((X.site (j + 1)).toVec - (X'.site (j + 1)).toVec) +
        projMinus ((X.site (j - 1)).toVec - (X'.site (j - 1)).toVec) +
          projZero ((X.site j).toVec - (X'.site j).toVec) := by
  rw [transport_site_toVec, transport_site_toVec]
  simp only [map_sub]
  abel

/-- The background increments of two transported states differ by at most `16Rℓ charDist`. -/
theorem transport_lam_increment_le {R ℓ : ℝ} (hℓ : 0 ≤ ℓ) {X X' : GridState N}
    (hX : ∀ j, ‖(X.site j).toVec‖ ≤ R) (hX' : ∀ j, ‖(X'.site j).toVec‖ ≤ R) (j : ZMod N) :
    |((transport ℓ X).lam j - X.lam j) - ((transport ℓ X').lam j - X'.lam j)| ≤
      16 * R * ℓ * charDist X X' := by
  have hR : 0 ≤ R := (norm_nonneg _).trans (hX 0)
  have hp : ∀ k, |densPlus (X.site k).toVec - densPlus (X'.site k).toVec| ≤
      8 * R * charDist X X' := fun k =>
    (densPlus_lip (hX k) (hX' k)).trans (mul_le_mul_of_nonneg_left
      ((norm_projPlus_le_charNorm _).trans (charNorm_le_charDist X X' k)) (by positivity))
  have hm : ∀ k, |densMinus (X.site k).toVec - densMinus (X'.site k).toVec| ≤
      8 * R * charDist X X' := fun k =>
    (densMinus_lip (hX k) (hX' k)).trans (mul_le_mul_of_nonneg_left
      ((norm_projMinus_le_charNorm _).trans (charNorm_le_charDist X X' k)) (by positivity))
  rw [transport_lam_apply, transport_lam_apply]
  set a1 := densPlus (X.site j).toVec - densPlus (X'.site j).toVec
  set a2 := densPlus (X.site (j + 1)).toVec - densPlus (X'.site (j + 1)).toVec
  set a3 := densMinus (X.site j).toVec - densMinus (X'.site j).toVec
  set a4 := densMinus (X.site (j - 1)).toVec - densMinus (X'.site (j - 1)).toVec
  have e : X.lam j + ℓ / 2 * ((densPlus (X.site j).toVec + densPlus (X.site (j + 1)).toVec) +
        (densMinus (X.site j).toVec + densMinus (X.site (j - 1)).toVec)) - X.lam j -
      (X'.lam j + ℓ / 2 * ((densPlus (X'.site j).toVec + densPlus (X'.site (j + 1)).toVec) +
        (densMinus (X'.site j).toVec + densMinus (X'.site (j - 1)).toVec)) - X'.lam j) =
      ℓ / 2 * ((a1 + a2) + (a3 + a4)) := by simp only [a1, a2, a3, a4]; ring
  rw [e, abs_mul, abs_of_nonneg (by linarith : 0 ≤ ℓ / 2)]
  have h4 := abs_add_le (a1 + a2) (a3 + a4)
  have h5 := abs_add_le a1 a2
  have h6 := abs_add_le a3 a4
  have hsum : |(a1 + a2) + (a3 + a4)| ≤ 32 * R * charDist X X' := by
    linarith [hp j, hp (j + 1), hm j, hm (j - 1)]
  calc ℓ / 2 * |(a1 + a2) + (a3 + a4)| ≤ ℓ / 2 * (32 * R * charDist X X') :=
        mul_le_mul_of_nonneg_left hsum (by linarith)
    _ = 16 * R * ℓ * charDist X X' := by ring

/-- **The transport `eq:supp-gowdy-transport` is `(1 + 16Rℓ)`-Lipschitz in `charDist`** on grid
states whose sites have sup norm at most `R`: the characteristic shift is nonexpansive and the
background increment is `ℓ/2` times differences of `g± = |w±|²`. -/
theorem charDist_transport {R ℓ : ℝ} (hℓ : 0 ≤ ℓ) {X X' : GridState N}
    (hX : ∀ j, ‖(X.site j).toVec‖ ≤ R) (hX' : ∀ j, ‖(X'.site j).toVec‖ ≤ R) :
    charDist (transport ℓ X) (transport ℓ X') ≤ (1 + 16 * R * ℓ) * charDist X X' := by
  have hR : 0 ≤ R := (norm_nonneg _).trans (hX 0)
  have hD := charDist_nonneg X X'
  have hc : 0 ≤ 16 * R * ℓ := by positivity
  refine charDist_le (fun j => ?_) (fun j => ?_)
  · rw [transport_site_sub]
    refine (charNorm_shift_le _ _ _ (charNorm_le_charDist X X' (j + 1))
      (charNorm_le_charDist X X' (j - 1)) (charNorm_le_charDist X X' j)).trans ?_
    nlinarith
  · have hinc := transport_lam_increment_le hℓ hX hX' j
    have hl := abs_lam_le_charDist X X' j
    have e : (transport ℓ X).lam j - (transport ℓ X').lam j =
        (X.lam j - X'.lam j) + (((transport ℓ X).lam j - X.lam j) -
          ((transport ℓ X').lam j - X'.lam j)) := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    nlinarith

/-! ### The split step -/

/-- The synchronized split step `X → A → B` with `h = ℓ`: an implicit-midpoint source half-step
of duration `ℓ/2`, the transport, and a second source half-step (`thm:supp-gowdy-momentum`). -/
def IsSplitStep (ℓ : ℝ) (X A B : GridState N) : Prop :=
  IsSourceStep (ℓ / 2) X A ∧ IsSourceStep (ℓ / 2) (transport ℓ A) B

/-- The (enforced or bootstrapped) envelope of a split step: all stage midpoints lie in the Gowdy
chart `{t ≥ t₀, |u_i| ≤ R, |P| ≤ R}` and the transported inputs have sup norm at most `R`. -/
def SplitEnvelope (t₀ R ℓ : ℝ) (X A B : GridState N) : Prop :=
  ∀ j, (1 / 2 : ℝ) • ((X.site j).toVec + (A.site j).toVec) ∈ gowdyChart t₀ R ∧
    ‖(A.site j).toVec‖ ≤ R ∧
    (1 / 2 : ℝ) • (((transport ℓ A).site j).toVec + (B.site j).toVec) ∈ gowdyChart t₀ R

/-- The Lipschitz rate `K = 9 L + 64 R` of the split map, `L = gowdyLipschitz t₀ R`. -/
def splitConst (t₀ R : ℝ) : ℝ := 9 * gowdyLipschitz t₀ R + 64 * R

theorem splitConst_nonneg {t₀ R : ℝ} (h0 : 0 < t₀) (hR : 0 ≤ R) : 0 ≤ splitConst t₀ R := by
  unfold splitConst; have := gowdyLipschitz_nonneg h0 hR; positivity

theorem projZero_transport_sub (ℓ : ℝ) (Y : GridState N) (k : ZMod N) :
    projZero (((transport ℓ Y).site k).toVec - (Y.site k).toVec) = 0 := by
  rw [transport_site_toVec, map_sub, map_add, map_add, projZero_projPlus, projZero_projMinus,
    projZero_projZero, zero_add, zero_add, sub_self]

/-- **The Gowdy split map is `(1 + Kℓ)`-Lipschitz in the characteristic distance** on the
envelope, `K = splitConst t₀ R`, for `3ℓL ≤ 1` and `16Rℓ ≤ 1`.  Moreover `Φ_h - id` is
`O(ℓ)`-Lipschitz in the non-moving components `(P, Q, t)` (constant `15Lℓ`) and in `λ`
(constant `32Rℓ`). -/
theorem charDist_splitStep {t₀ R ℓ : ℝ} (h0 : 0 < t₀) (hR : 0 ≤ R) (hℓ : 0 ≤ ℓ)
    (hℓL : 3 * ℓ * gowdyLipschitz t₀ R ≤ 1) (hℓR : 16 * R * ℓ ≤ 1)
    {X A B X' A' B' : GridState N} (hs : IsSplitStep ℓ X A B) (hs' : IsSplitStep ℓ X' A' B')
    (he : SplitEnvelope t₀ R ℓ X A B) (he' : SplitEnvelope t₀ R ℓ X' A' B') :
    charDist B B' ≤ (1 + splitConst t₀ R * ℓ) * charDist X X' ∧
      (∀ j, ‖projZero (((B.site j).toVec - (X.site j).toVec) -
          ((B'.site j).toVec - (X'.site j).toVec))‖ ≤
        15 * gowdyLipschitz t₀ R * ℓ * charDist X X') ∧
      (∀ j, |(B.lam j - X.lam j) - (B'.lam j - X'.lam j)| ≤ 32 * R * ℓ * charDist X X') := by
  set L := gowdyLipschitz t₀ R with hLdef
  have hL0 : 0 ≤ L := gowdyLipschitz_nonneg h0 hR
  have hσ : 0 ≤ ℓ / 2 := by linarith
  have hσL : 3 * (ℓ / 2) * L ≤ 1 := by nlinarith
  have hLip := localFieldVec_lipschitz_on_chart h0 hR
  have hD := charDist_nonneg X X'
  -- stage one
  obtain ⟨h1, hinc1⟩ := charDist_sourceStep hLip hL0 hσ hσL hs.1 hs'.1
    (fun j => (he j).1) (fun j => (he' j).1)
  -- transport
  have h2 := charDist_transport hℓ (fun j => (he j).2.1) (fun j => (he' j).2.1)
  -- stage three
  obtain ⟨h3, hinc3⟩ := charDist_sourceStep hLip hL0 hσ hσL hs.2 hs'.2
    (fun j => (he j).2.2) (fun j => (he' j).2.2)
  have e6 : 6 * (ℓ / 2) * L = 3 * ℓ * L := by ring
  rw [e6] at h1 h3 hinc1 hinc3
  have hD1 := charDist_nonneg A A'
  have hD2 := charDist_nonneg (transport ℓ A) (transport ℓ A')
  have ha0 : 0 ≤ 3 * ℓ * L := by positivity
  have hb0 : 0 ≤ 16 * R * ℓ := by positivity
  -- chained bounds
  have hA : charDist A A' ≤ 2 * charDist X X' := h1.trans (by nlinarith)
  have hT : charDist (transport ℓ A) (transport ℓ A') ≤ 4 * charDist X X' :=
    h2.trans (by nlinarith)
  refine ⟨?_, fun j => ?_, fun j => ?_⟩
  · calc charDist B B' ≤ (1 + 3 * ℓ * L) * ((1 + 16 * R * ℓ) * ((1 + 3 * ℓ * L) *
          charDist X X')) := by
          refine h3.trans (mul_le_mul_of_nonneg_left (h2.trans ?_) (by linarith))
          exact mul_le_mul_of_nonneg_left h1 (by linarith)
      _ ≤ (1 + splitConst t₀ R * ℓ) * charDist X X' := by
          rw [← mul_assoc, ← mul_assoc]
          refine mul_le_mul_of_nonneg_right ?_ hD
          unfold splitConst
          rw [← hLdef]
          have : (3 * ℓ * L) * (3 * ℓ * L) ≤ 3 * ℓ * L := by nlinarith
          have : (3 * ℓ * L) * (16 * R * ℓ) ≤ 16 * R * ℓ := by nlinarith
          nlinarith
  · -- the `(P, Q, t)` increment: the transport does not move `Π₀`
    have e : ((B.site j).toVec - (X.site j).toVec) - ((B'.site j).toVec - (X'.site j).toVec) =
        (((B.site j).toVec - ((transport ℓ A).site j).toVec) -
          ((B'.site j).toVec - ((transport ℓ A').site j).toVec)) +
        ((((transport ℓ A).site j).toVec - (A.site j).toVec) -
          (((transport ℓ A').site j).toVec - (A'.site j).toVec)) +
        (((A.site j).toVec - (X.site j).toVec) - ((A'.site j).toVec - (X'.site j).toVec)) := by
      abel
    have hz : projZero ((((transport ℓ A).site j).toVec - (A.site j).toVec) -
          (((transport ℓ A').site j).toVec - (A'.site j).toVec)) = 0 := by
      rw [map_sub, projZero_transport_sub, projZero_transport_sub, sub_self]
    rw [e, map_add, map_add, hz, add_zero]
    refine (norm_add_le _ _).trans ?_
    have i3 := (norm_projZero_le _).trans (hinc3 j)
    have i1 := (norm_projZero_le _).trans (hinc1 j)
    have : 3 * ℓ * L * charDist (transport ℓ A) (transport ℓ A') ≤
        3 * ℓ * L * (4 * charDist X X') := mul_le_mul_of_nonneg_left hT ha0
    nlinarith
  · -- the `λ` increment: only the transport moves `λ`
    have eB : B.lam = (transport ℓ A).lam := hs.2.2
    have eB' : B'.lam = (transport ℓ A').lam := hs'.2.2
    have eA : A.lam = X.lam := hs.1.2
    have eA' : A'.lam = X'.lam := hs'.1.2
    rw [eB, eB', ← eA, ← eA']
    refine (transport_lam_increment_le hℓ (fun k => (he k).2.1) (fun k => (he' k).2.1) j).trans ?_
    have : 16 * R * ℓ * charDist A A' ≤ 16 * R * ℓ * (2 * charDist X X') :=
      mul_le_mul_of_nonneg_left hA hb0
    linarith

/-! ### A finite discrete Grönwall inequality -/

/-- Discrete Grönwall on a finite horizon: if `u (m+1) ≤ (1 + c) u m + b m` for `m < n₀`,
`c ≥ 0`, `b ≥ 0`, then `u n ≤ (u 0 + Σ_{k<n} b k) e^{n c}` for `n ≤ n₀`. -/
theorem gronwall_finite {u b : ℕ → ℝ} {c : ℝ} {n₀ : ℕ} (hc : 0 ≤ c) (hb : ∀ m, 0 ≤ b m)
    (hstep : ∀ m < n₀, u (m + 1) ≤ (1 + c) * u m + b m) (hu : ∀ m, 0 ≤ u m) :
    ∀ n ≤ n₀, u n ≤ (u 0 + ∑ k ∈ range n, b k) * Real.exp (n * c) := by
  intro n hn
  induction n with
  | zero => simp
  | succ n ih =>
    have ih := ih (by omega)
    have h1 : 1 + c ≤ Real.exp c := by linarith [Real.add_one_le_exp c]
    have hS : 0 ≤ u 0 + ∑ k ∈ range n, b k :=
      add_nonneg (hu 0) (Finset.sum_nonneg fun k _ => hb k)
    have hE : Real.exp ((n + 1 : ℕ) * c) = Real.exp c * Real.exp (n * c) := by
      rw [← Real.exp_add]; push_cast; ring_nf
    have hE1 : 1 ≤ Real.exp ((n + 1 : ℕ) * c) := Real.one_le_exp (by positivity)
    calc u (n + 1) ≤ (1 + c) * u n + b n := hstep n (by omega)
      _ ≤ Real.exp c * ((u 0 + ∑ k ∈ range n, b k) * Real.exp (n * c)) +
            b n * Real.exp ((n + 1 : ℕ) * c) := by
          refine add_le_add ?_ (le_mul_of_one_le_right (hb n) hE1)
          exact mul_le_mul h1 ih (hu n) (Real.exp_pos c).le
      _ = (u 0 + ∑ k ∈ range (n + 1), b k) * Real.exp ((n + 1 : ℕ) * c) := by
          rw [Finset.sum_range_succ, hE]; ring

/-! ### Error arrays and the sup norm `‖·‖_{0,∞,ℓ}` -/

/-- The error array `j ↦ (X_j - Y_j, λ_j - λ'_j) ∈ (U,P,Q,t) × λ` of two grid states. -/
def errArr (X Y : GridState N) : ZMod N → StateVec × ℝ :=
  fun j => ((X.site j).toVec - (Y.site j).toVec, X.lam j - Y.lam j)

theorem charDist_le_norm_errArr (X Y : GridState N) : charDist X Y ≤ ‖errArr X Y‖ := by
  refine charDist_le (fun j => ?_) (fun j => ?_)
  · refine (charNorm_le_norm _).trans ((norm_fst_le (errArr X Y j)).trans ?_)
    exact norm_le_pi_norm (errArr X Y) j
  · have := (norm_snd_le (errArr X Y j)).trans (norm_le_pi_norm (errArr X Y) j)
    rwa [Real.norm_eq_abs] at this

theorem norm_errArr_le_charDist (X Y : GridState N) : ‖errArr X Y‖ ≤ 3 * charDist X Y := by
  have hD := charDist_nonneg X Y
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  refine norm_prod_le_iff.2 ⟨norm_site_sub_le_charDist X Y j, ?_⟩
  rw [Real.norm_eq_abs]
  show |X.lam j - Y.lam j| ≤ _
  linarith [abs_lam_le_charDist X Y j]

theorem crNorm_zero_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (ℓ : ℝ)
    (v : ZMod N → E) : PeriodicGridResidual.crNorm 0 ℓ v = ‖v‖ := by
  simp [PeriodicGridResidual.crNorm]

/-! ### The reference history lies in the envelope -/

theorem gowdyChart_mono {t R R' : ℝ} (h : R ≤ R') {v : StateVec} (hv : v ∈ gowdyChart t R) :
    v ∈ gowdyChart t R' :=
  ⟨hv.1, fun i => (hv.2.1 i).trans h, hv.2.2.trans h⟩


end

end CharStability

noncomputable section

open CharStability

variable {N : ℕ} [NeZero N]

namespace GowdyFrameSolution

variable {t₀ t₁ : ℝ} (sol : GowdyFrameSolution t₀ t₁)

/-- **The near-identity reference step lies in the envelope** `SplitEnvelope (t₀/2) R` for every
`R ≥ chartRadius`: the sampled state, its source half-step, the transported state and the last
stage all stay in the tube around the reference solution. -/
theorem charStab_reference_envelope (h0 : 0 < t₀) (N : ℕ) [NeZero N]
    (hN : 2 * Real.pi / N ≤ (sol.strangSetup h0).stepBound) (τ : ℝ) (hτ : t₀ ≤ τ)
    (hτh : τ + 2 * Real.pi / N ≤ t₁) (X₁ X₃ : GridState N)
    (h₁ : IsSourceStep (2 * Real.pi / N / 2) (sol.sample N τ) X₁)
    (hd₁ : ∀ j, ‖(X₁.site j).toVec - ((sol.sample N τ).site j).toVec‖ ≤ (sol.strangSetup h0).δ)
    (hd₃ : ∀ j, ‖(X₃.site j).toVec - ((transport (2 * Real.pi / N) X₁).site j).toVec‖ ≤
      (sol.strangSetup h0).δ) {R : ℝ} (hR : sol.chartRadius h0 ≤ R) :
    SplitEnvelope (t₀ / 2) R (2 * Real.pi / N) (sol.sample N τ) X₁ X₃ := by
  set S := sol.strangSetup h0 with hS
  set ℓ := 2 * Real.pi / N with hℓ
  have hℓpos : 0 < ℓ := by
    have : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N))
    positivity
  have hsamp : ∀ k, ((sol.sample N τ).site k).toVec = sol.Z (τ, sampleAngle N k) := by
    intro k; simp [sample]
  have hslab : ∀ k : ZMod N, ((τ, sampleAngle N k) : ℝ × ℝ).1 ∈ Icc S.t₀ S.t₁ :=
    fun k => ⟨hτ, by show τ ≤ t₁; linarith⟩
  have hK : ∀ v, v ∈ S.K → v ∈ gowdyChart (t₀ / 2) R ∧ ‖v‖ ≤ R := fun v hv =>
    ⟨gowdyChart_mono hR (chartK_subset_gowdyChart hv), hv.1.trans hR⟩
  have hYd : ∀ k, ‖(X₁.site k).toVec - S.Z (τ, sampleAngle N k)‖ ≤ S.δ := by
    intro k; have := hd₁ k; rwa [hsamp k] at this
  have hX1K : ∀ k, (X₁.site k).toVec ∈ S.K := fun k => S.tube _ (hslab k) _ (hYd k)
  have hZK : ∀ k, S.Z (τ, sampleAngle N k) ∈ S.K := fun k => S.mem_K_of_slab (hslab k)
  have hY : ∀ k, (X₁.site k).toVec = S.Z (τ, sampleAngle N k) + (ℓ / 2) •
      S.F ((1 / 2 : ℝ) • (S.Z (τ, sampleAngle N k) + (X₁.site k).toVec)) := by
    intro k
    have := (isMidpointStep_iff_toVec _ _ _).1 (h₁.1 k)
    rw [hsamp k] at this
    exact this
  intro j
  refine ⟨?_, (hK _ (hX1K j)).2, ?_⟩
  · rw [hsamp j]; exact (hK _ (S.mem_K_midpoint (hZK j) (hX1K j))).1
  · have hnear : ‖((transport ℓ X₁).site j).toVec - S.Z (τ + ℓ, sampleAngle N j)‖ ≤
        S.δ / 2 := by
      have hZp : S.Z (τ, sampleAngle N (j + 1)) = S.Z (τ, sampleAngle N j + ℓ) :=
        sample_succ sol.Z sol.periodic_Z N τ j
      have hZm : S.Z (τ, sampleAngle N (j - 1)) = S.Z (τ, sampleAngle N j - ℓ) :=
        sample_pred sol.Z sol.periodic_Z N τ j
      have h1p := hY (j + 1)
      have h1m := hY (j - 1)
      have hd1p := hYd (j + 1)
      have hd1m := hYd (j - 1)
      rw [hZp] at h1p hd1p
      rw [hZm] at h1m hd1m
      rw [transport_site_toVec]
      exact S.transportCombine_near hℓpos hN hτ hτh h1m hd1m (hY j) (hYd j) h1p hd1p
    set T := ((transport ℓ X₁).site j).toVec
    set W := S.Z (τ + ℓ, sampleAngle N j)
    have hmid : ‖(1 / 2 : ℝ) • (T + (X₃.site j).toVec) - W‖ ≤ S.δ := by
      have e : (1 / 2 : ℝ) • (T + (X₃.site j).toVec) - W =
          (T - W) + (1 / 2 : ℝ) • ((X₃.site j).toVec - T) := by module
      rw [e]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul]
      have := hd₃ j
      norm_num
      linarith
    exact (hK _ (S.tube (τ + ℓ, sampleAngle N j) ⟨by show t₀ ≤ τ + ℓ; linarith,
      by show τ + ℓ ≤ t₁; linarith⟩ _ hmid)).1

/-! ### The global error -/

/-- The step-size threshold of the stability analysis on the envelope of radius `R`. -/
def charStabStep (h0 : 0 < t₀) (R : ℝ) : ℝ :=
  min (sol.strangSetup h0).stepBound
    (min (1 / (3 * gowdyLipschitz (t₀ / 2) R + 1)) (1 / (16 * R + 1)))

/-- The consistency constant (coefficient of `ℓ³`). -/
def charConsConst (h0 : 0 < t₀) : ℝ :=
  max (max (sol.strangSetup h0).stateConst (sol.strangSetup h0).lamConst) 0

theorem charStabStep_pos (h0 : 0 < t₀) {R : ℝ} (hR : 0 ≤ R) : 0 < sol.charStabStep h0 R := by
  have hL := gowdyLipschitz_nonneg (by linarith : 0 < t₀ / 2) hR
  exact lt_min (sol.strangSetup h0).stepBound_pos (lt_min (by positivity) (by positivity))

theorem charStabStep_spec (h0 : 0 < t₀) {R : ℝ} (hR : 0 ≤ R) {ℓ : ℝ} (hℓ : 0 ≤ ℓ)
    (h : ℓ ≤ sol.charStabStep h0 R) :
    ℓ ≤ (sol.strangSetup h0).stepBound ∧ 3 * ℓ * gowdyLipschitz (t₀ / 2) R ≤ 1 ∧
      16 * R * ℓ ≤ 1 := by
  have hL := gowdyLipschitz_nonneg (by linarith : 0 < t₀ / 2) hR
  have h1 := h.trans (min_le_left _ _)
  have h2 := (h.trans (min_le_right _ _)).trans (min_le_left _ _)
  have h3 := (h.trans (min_le_right _ _)).trans (min_le_right _ _)
  refine ⟨h1, ?_, ?_⟩
  · rw [le_div_iff₀ (by positivity)] at h2; nlinarith
  · rw [le_div_iff₀ (by positivity)] at h3; nlinarith

theorem charConsConst_nonneg (h0 : 0 < t₀) : 0 ≤ sol.charConsConst h0 := le_max_right _ _

/-- **One step of the error recursion.**  For a numerical split step `X → A → B` in the envelope,
started at the grid time `τ`, and any next state `X⁺`:
`charDist(X⁺, 𝖲X_*(τ+ℓ)) ≤ charDist(X⁺, B) + (1 + Kℓ) charDist(X, 𝖲X_*(τ)) + C ℓ³`, and the
time increments of the `(P, Q, t)` and `λ` errors are bounded by
`(15L + 32R)ℓ charDist(X, 𝖲X_*(τ)) + charDist(X⁺, B) + C ℓ³`. -/
theorem charStab_error_step (h0 : 0 < t₀) {R : ℝ} (hR : sol.chartRadius h0 ≤ R) (N : ℕ) [NeZero N]
    (hN : 2 * Real.pi / N ≤ sol.charStabStep h0 R) (τ : ℝ) (hτ : t₀ ≤ τ)
    (hτh : τ + 2 * Real.pi / N ≤ t₁) (X A B X' : GridState N)
    (hs : IsSplitStep (2 * Real.pi / N) X A B)
    (he : SplitEnvelope (t₀ / 2) R (2 * Real.pi / N) X A B) :
    charDist X' (sol.sample N (τ + 2 * Real.pi / N)) ≤ charDist X' B +
        (1 + splitConst (t₀ / 2) R * (2 * Real.pi / N)) * charDist X (sol.sample N τ) +
        sol.charConsConst h0 * (2 * Real.pi / N) ^ 3 ∧
      ∀ j, ‖projZero (((X'.site j).toVec - ((sol.sample N (τ + 2 * Real.pi / N)).site j).toVec) -
          ((X.site j).toVec - ((sol.sample N τ).site j).toVec))‖ ≤
        (15 * gowdyLipschitz (t₀ / 2) R + 32 * R) * (2 * Real.pi / N) *
          charDist X (sol.sample N τ) + charDist X' B + sol.charConsConst h0 * (2 * Real.pi / N) ^ 3 ∧
      |(X'.lam j - (sol.sample N (τ + 2 * Real.pi / N)).lam j) -
          (X.lam j - (sol.sample N τ).lam j)| ≤
        (15 * gowdyLipschitz (t₀ / 2) R + 32 * R) * (2 * Real.pi / N) *
          charDist X (sol.sample N τ) + charDist X' B + sol.charConsConst h0 * (2 * Real.pi / N) ^ 3 := by
  set S := sol.strangSetup h0 with hS
  set ℓ := 2 * Real.pi / N with hℓ
  have hℓpos : 0 < ℓ := by
    have : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N))
    positivity
  have hR0 : 0 ≤ R := by linarith [(sol.chartRadius_spec h0).1]
  obtain ⟨hNb, hℓL, hℓR⟩ := sol.charStabStep_spec h0 hR0 hℓpos.le hN
  -- the reference step
  obtain ⟨X₁, X₃, h₁, h₃, hd₁, hd₃⟩ := sol.step_exists h0 N hNb τ hτ hτh
  have hloc := sol.local_error_grid h0 N hNb τ hτ hτh X₁ X₃ h₁ h₃ hd₁ hd₃
  have henv := sol.charStab_reference_envelope h0 N hNb τ hτ hτh X₁ X₃ h₁ hd₁ hd₃ hR
  have hC : max S.stateConst S.lamConst ≤ sol.charConsConst h0 := le_max_left _ _
  have hℓ3 : 0 ≤ ℓ ^ 3 := by positivity
  set Y' := sol.sample N (τ + ℓ)
  have hcons : charDist X₃ Y' ≤ sol.charConsConst h0 * ℓ ^ 3 := by
    refine charDist_le (fun j => ?_) (fun j => ?_)
    · exact (charNorm_le_norm _).trans ((hloc j).1.trans
        (mul_le_mul_of_nonneg_right hC hℓ3))
    · exact (hloc j).2.trans (mul_le_mul_of_nonneg_right hC hℓ3)
  obtain ⟨hlip, hP0, hlam⟩ := charDist_splitStep (by linarith : 0 < t₀ / 2) hR0 hℓpos.le hℓL hℓR
    hs ⟨h₁, h₃⟩ he henv
  have hD := charDist_nonneg X (sol.sample N τ)
  refine ⟨?_, fun j => ⟨?_, ?_⟩⟩
  · calc charDist X' Y' ≤ charDist X' B + charDist B Y' := charDist_triangle _ _ _
      _ ≤ charDist X' B + (charDist B X₃ + charDist X₃ Y') := by
          gcongr; exact charDist_triangle _ _ _
      _ ≤ _ := by linarith
  · have e : ((X'.site j).toVec - (Y'.site j).toVec) - ((X.site j).toVec -
        ((sol.sample N τ).site j).toVec) =
        ((X'.site j).toVec - (B.site j).toVec) +
        (((B.site j).toVec - (X.site j).toVec) - ((X₃.site j).toVec -
          ((sol.sample N τ).site j).toVec)) + ((X₃.site j).toVec - (Y'.site j).toVec) := by
      abel
    rw [e, map_add, map_add]
    refine (norm_add₃_le).trans ?_
    have a1 : ‖projZero ((X'.site j).toVec - (B.site j).toVec)‖ ≤ charDist X' B :=
      (norm_projZero_le_charNorm _).trans (charNorm_le_charDist _ _ j)
    have a3 : ‖projZero ((X₃.site j).toVec - (Y'.site j).toVec)‖ ≤ sol.charConsConst h0 * ℓ ^ 3 :=
      (norm_projZero_le _).trans ((hloc j).1.trans (mul_le_mul_of_nonneg_right hC hℓ3))
    have a2 := hP0 j
    have : 15 * gowdyLipschitz (t₀ / 2) R * ℓ * charDist X (sol.sample N τ) ≤
        (15 * gowdyLipschitz (t₀ / 2) R + 32 * R) * ℓ * charDist X (sol.sample N τ) := by
      have : 0 ≤ 32 * R * ℓ * charDist X (sol.sample N τ) := by positivity
      nlinarith
    linarith
  · have e : (X'.lam j - Y'.lam j) - (X.lam j - (sol.sample N τ).lam j) =
        (X'.lam j - B.lam j) + ((B.lam j - X.lam j) - (X₃.lam j - (sol.sample N τ).lam j)) +
        (X₃.lam j - Y'.lam j) := by ring
    rw [e]
    have a1 : |X'.lam j - B.lam j| ≤ charDist X' B := abs_lam_le_charDist _ _ j
    have a3 : |X₃.lam j - Y'.lam j| ≤ sol.charConsConst h0 * ℓ ^ 3 :=
      (hloc j).2.trans (mul_le_mul_of_nonneg_right hC hℓ3)
    have a2 := hlam j
    have hL0 := gowdyLipschitz_nonneg (by linarith : 0 < t₀ / 2) hR0
    have : 32 * R * ℓ * charDist X (sol.sample N τ) ≤
        (15 * gowdyLipschitz (t₀ / 2) R + 32 * R) * ℓ * charDist X (sol.sample N τ) := by
      have : 0 ≤ 15 * gowdyLipschitz (t₀ / 2) R * ℓ * charDist X (sol.sample N τ) := by
        positivity
      nlinarith
    have h3 := abs_add_le ((X'.lam j - B.lam j) + ((B.lam j - X.lam j) -
      (X₃.lam j - (sol.sample N τ).lam j))) (X₃.lam j - Y'.lam j)
    have h2 := abs_add_le (X'.lam j - B.lam j) ((B.lam j - X.lam j) -
      (X₃.lam j - (sol.sample N τ).lam j))
    linarith

/-- **The global sup-type error of the Gowdy scheme in the characteristic distance**
(`eq:supp-gowdy-state-error`, `r = 0`, enforced envelope).  Let `ℓ = 2π/N ≤ charStabStep`,
`[τ₀, τ₀ + n₀ℓ] ⊆ [t₀, t₁]`, and let `X_n` be a numerical history realised by split steps
`X_n → A_n → B_n` in the envelope of radius `R ≥ chartRadius`, with arbitrary next states
`X_{n+1}` (the residual is `X_{n+1} - B_n`).  Then for `n ≤ n₀`
`charDist(X_n, 𝖲X_*(τ₀+nℓ)) ≤ (charDist(X₀, 𝖲X_*(τ₀)) + Σ_{k<n} charDist(X_{k+1}, B_k)
  + C (t₁ - t₀) ℓ²) e^{K (t₁ - t₀)}`. -/
theorem state_error_charDist (h0 : 0 < t₀) {R : ℝ} (hR : sol.chartRadius h0 ≤ R) (N : ℕ)
    [NeZero N] (hN : 2 * Real.pi / N ≤ sol.charStabStep h0 R) (τ₀ : ℝ) (n₀ : ℕ)
    (hτ₀ : t₀ ≤ τ₀) (hn₀ : τ₀ + n₀ * (2 * Real.pi / N) ≤ t₁) (X A B : ℕ → GridState N)
    (hstep : ∀ n < n₀, IsSplitStep (2 * Real.pi / N) (X n) (A n) (B n) ∧
      SplitEnvelope (t₀ / 2) R (2 * Real.pi / N) (X n) (A n) (B n)) :
    ∀ n ≤ n₀, charDist (X n) (sol.sample N (τ₀ + n * (2 * Real.pi / N))) ≤
      (charDist (X 0) (sol.sample N τ₀) + ∑ k ∈ range n, charDist (X (k + 1)) (B k) +
        sol.charConsConst h0 * (t₁ - t₀) * (2 * Real.pi / N) ^ 2) *
        Real.exp (splitConst (t₀ / 2) R * (t₁ - t₀)) := by
  set ℓ := 2 * Real.pi / N with hℓ
  have hℓpos : 0 < ℓ := by
    have : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N))
    positivity
  have hR0 : 0 ≤ R := by linarith [(sol.chartRadius_spec h0).1]
  set K := splitConst (t₀ / 2) R
  have hK : 0 ≤ K := splitConst_nonneg (by linarith) hR0
  set C := sol.charConsConst h0
  have hC : 0 ≤ C := sol.charConsConst_nonneg h0
  set u : ℕ → ℝ := fun m => charDist (X m) (sol.sample N (τ₀ + m * ℓ))
  set b : ℕ → ℝ := fun m => charDist (X (m + 1)) (B m) + C * ℓ ^ 3
  have hrec : ∀ m < n₀, u (m + 1) ≤ (1 + K * ℓ) * u m + b m := by
    intro m hm
    have hτm : t₀ ≤ τ₀ + m * ℓ := by
      have : 0 ≤ (m : ℝ) * ℓ := by positivity
      linarith
    have hm' : ((m + 1 : ℕ) : ℝ) ≤ n₀ := by exact_mod_cast hm
    have hτh : τ₀ + m * ℓ + ℓ ≤ t₁ := by
      have : ((m + 1 : ℕ) : ℝ) * ℓ ≤ n₀ * ℓ := mul_le_mul_of_nonneg_right hm' hℓpos.le
      push_cast at this
      linarith
    obtain ⟨h1, -⟩ := sol.charStab_error_step h0 hR N hN (τ₀ + m * ℓ) hτm hτh (X m) (A m) (B m)
      (X (m + 1)) (hstep m hm).1 (hstep m hm).2
    have e : τ₀ + ((m + 1 : ℕ) : ℝ) * ℓ = τ₀ + m * ℓ + ℓ := by push_cast; ring
    show charDist (X (m + 1)) (sol.sample N (τ₀ + ((m + 1 : ℕ) : ℝ) * ℓ)) ≤ _
    rw [e]
    simp only [u, b]
    linarith
  have hb0 : ∀ m, 0 ≤ b m := fun m => add_nonneg (charDist_nonneg _ _) (by positivity)
  have hg := gronwall_finite (u := u) (b := b) (c := K * ℓ) (n₀ := n₀) (by positivity)
    hb0 hrec (fun m => charDist_nonneg _ _)
  intro n hn
  have hgn := hg n hn
  have hu0 : u 0 = charDist (X 0) (sol.sample N τ₀) := by simp [u]
  have hnl : (n : ℝ) * ℓ ≤ t₁ - t₀ := by
    have : (n : ℝ) ≤ n₀ := by exact_mod_cast hn
    have : (n : ℝ) * ℓ ≤ n₀ * ℓ := mul_le_mul_of_nonneg_right this hℓpos.le
    linarith
  have hsum : ∑ k ∈ range n, b k ≤ ∑ k ∈ range n, charDist (X (k + 1)) (B k) +
      C * (t₁ - t₀) * ℓ ^ 2 := by
    simp only [b, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have : (n : ℝ) * (C * ℓ ^ 3) ≤ C * (t₁ - t₀) * ℓ ^ 2 := by
      have : (n : ℝ) * (C * ℓ ^ 3) = C * ℓ ^ 2 * ((n : ℝ) * ℓ) := by ring
      rw [this]
      have := mul_le_mul_of_nonneg_left hnl (by positivity : 0 ≤ C * ℓ ^ 2)
      linarith
    linarith
  have hexp : Real.exp (n * (K * ℓ)) ≤ Real.exp (K * (t₁ - t₀)) := by
    apply Real.exp_le_exp.2
    have := mul_le_mul_of_nonneg_left hnl hK
    linarith
  have hS0 : 0 ≤ u 0 + ∑ k ∈ range n, b k :=
    add_nonneg (charDist_nonneg _ _) (Finset.sum_nonneg fun k _ => hb0 k)
  calc u n ≤ (u 0 + ∑ k ∈ range n, b k) * Real.exp (n * (K * ℓ)) := hgn
    _ ≤ (u 0 + ∑ k ∈ range n, b k) * Real.exp (K * (t₁ - t₀)) :=
        mul_le_mul_of_nonneg_left hexp hS0
    _ ≤ _ := by
        rw [hu0] at hS0 ⊢
        refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
        linarith

/-- **`eq:supp-gowdy-state-error` for `r = 0`** in the manuscript's norms: with
`‖·‖_{0,∞,ℓ}` the sup norm of the error array in `(U, P, Q, t, λ)`, residual arrays
`r_k = X_{k+1} - B_k` and `𝓕_h = ℓ^{-1} Σ_{k<n} ‖r_k‖²_{2,ℓ}/(2h)` (`h = ℓ ≤ 2`),
`‖X_n - 𝖲X_*(t_n)‖_{0,∞,ℓ} ≤ 3 (‖X₀ - 𝖲X_*(t₀)‖_{0,∞,ℓ} + √(2nh) √𝓕_h + C (t₁-t₀) h²)
  e^{K(t₁-t₀)}`. -/
theorem state_error_sup (h0 : 0 < t₀) {R : ℝ} (hR : sol.chartRadius h0 ≤ R) (N : ℕ)
    [NeZero N] (hN : 2 * Real.pi / N ≤ sol.charStabStep h0 R) (hN2 : 2 * Real.pi / N ≤ 2)
    (τ₀ : ℝ) (n₀ : ℕ) (hτ₀ : t₀ ≤ τ₀) (hn₀ : τ₀ + n₀ * (2 * Real.pi / N) ≤ t₁)
    (X A B : ℕ → GridState N)
    (hstep : ∀ n < n₀, IsSplitStep (2 * Real.pi / N) (X n) (A n) (B n) ∧
      SplitEnvelope (t₀ / 2) R (2 * Real.pi / N) (X n) (A n) (B n)) :
    ∀ n ≤ n₀, PeriodicGridResidual.crNorm 0 (2 * Real.pi / N)
        (errArr (X n) (sol.sample N (τ₀ + n * (2 * Real.pi / N)))) ≤
      3 * (PeriodicGridResidual.crNorm 0 (2 * Real.pi / N) (errArr (X 0) (sol.sample N τ₀)) +
        2 ^ 0 * Real.sqrt (2 * n * (2 * Real.pi / N)) *
          Real.sqrt (PeriodicGridResidual.residualFlux 0 (2 * Real.pi / N) (2 * Real.pi / N)
            (fun k => errArr (X (k + 1)) (B k)) n) +
        sol.charConsConst h0 * (t₁ - t₀) * (2 * Real.pi / N) ^ 2) *
        Real.exp (splitConst (t₀ / 2) R * (t₁ - t₀)) := by
  set ℓ := 2 * Real.pi / N with hℓ
  have hℓpos : 0 < ℓ := by
    have : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N))
    positivity
  intro n hn
  have h := sol.state_error_charDist h0 hR N hN τ₀ n₀ hτ₀ hn₀ X A B hstep n hn
  have hbud := PeriodicGridResidual.sum_crNorm_le_sqrt_residualFlux hℓpos hN2 0
    (fun k => errArr (X (k + 1)) (B k)) n
  have hsum : ∑ k ∈ range n, charDist (X (k + 1)) (B k) ≤
      ∑ k ∈ range n, PeriodicGridResidual.crNorm 0 ℓ (errArr (X (k + 1)) (B k)) :=
    Finset.sum_le_sum fun k _ => by rw [crNorm_zero_eq]; exact charDist_le_norm_errArr _ _
  rw [crNorm_zero_eq, crNorm_zero_eq]
  have h0' := charDist_le_norm_errArr (X 0) (sol.sample N τ₀)
  refine (norm_errArr_le_charDist _ _).trans ?_
  have hin : charDist (X 0) (sol.sample N τ₀) + ∑ k ∈ range n, charDist (X (k + 1)) (B k) +
        sol.charConsConst h0 * (t₁ - t₀) * ℓ ^ 2 ≤
      ‖errArr (X 0) (sol.sample N τ₀)‖ + 2 ^ 0 * Real.sqrt (2 * n * ℓ) *
        Real.sqrt (PeriodicGridResidual.residualFlux 0 ℓ ℓ (fun k => errArr (X (k + 1)) (B k)) n)
        + sol.charConsConst h0 * (t₁ - t₀) * ℓ ^ 2 := by linarith
  have h2 := h.trans (mul_le_mul_of_nonneg_right hin (Real.exp_pos _).le)
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left h2 (by norm_num)

/-- **`eq:supp-gowdy-state-error` for `r = 0`, constant form**: on the envelope of radius
`R ≥ chartRadius` there are `C` and `ℓ₀ > 0` (independent of the grid, the history and the
residuals) such that `max_{n ≤ n₀} ‖X_n - 𝖲_ℓ X_*(t_n)‖_{0,∞,ℓ} ≤ C (ε₀ + h² + √𝓕_h)` for every
`h = ℓ = 2π/N ≤ ℓ₀`. -/
theorem state_error_bigO (h0 : 0 < t₀) {R : ℝ} (hR : sol.chartRadius h0 ≤ R) :
    ∃ C ℓ₀ : ℝ, 0 < ℓ₀ ∧ 0 ≤ C ∧ ∀ (N : ℕ) [NeZero N], 2 * Real.pi / N ≤ ℓ₀ →
      ∀ (τ₀ : ℝ) (n₀ : ℕ), t₀ ≤ τ₀ → τ₀ + n₀ * (2 * Real.pi / N) ≤ t₁ →
      ∀ X A B : ℕ → GridState N,
        (∀ n < n₀, IsSplitStep (2 * Real.pi / N) (X n) (A n) (B n) ∧
          SplitEnvelope (t₀ / 2) R (2 * Real.pi / N) (X n) (A n) (B n)) →
        ∀ n ≤ n₀, PeriodicGridResidual.crNorm 0 (2 * Real.pi / N)
            (errArr (X n) (sol.sample N (τ₀ + n * (2 * Real.pi / N)))) ≤
          C * (PeriodicGridResidual.crNorm 0 (2 * Real.pi / N) (errArr (X 0) (sol.sample N τ₀)) +
            (2 * Real.pi / N) ^ 2 +
            Real.sqrt (PeriodicGridResidual.residualFlux 0 (2 * Real.pi / N) (2 * Real.pi / N)
              (fun k => errArr (X (k + 1)) (B k)) n)) := by
  have hR0 : 0 ≤ R := by linarith [(sol.chartRadius_spec h0).1]
  set T := max (t₁ - t₀) 0
  set K := splitConst (t₀ / 2) R
  have hK : 0 ≤ K := splitConst_nonneg (by linarith) hR0
  set C0 := sol.charConsConst h0
  have hC0 : 0 ≤ C0 := sol.charConsConst_nonneg h0
  refine ⟨3 * (1 + Real.sqrt (2 * T) + C0 * T) * Real.exp (K * T),
    min (sol.charStabStep h0 R) 2, lt_min (sol.charStabStep_pos h0 hR0) two_pos,
    by positivity, ?_⟩
  intro N _ hN τ₀ n₀ hτ₀ hn₀ X A B hstep n hn
  set ℓ := 2 * Real.pi / N with hℓ
  have hℓpos : 0 < ℓ := by
    have : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N))
    positivity
  have h := sol.state_error_sup h0 hR N (hN.trans (min_le_left _ _)) (hN.trans (min_le_right _ _))
    τ₀ n₀ hτ₀ hn₀ X A B hstep n hn
  have hT : t₁ - t₀ ≤ T := le_max_left _ _
  have hT0 : 0 ≤ T := le_max_right _ _
  have hnl : (n : ℝ) * ℓ ≤ T := by
    have : (n : ℝ) ≤ n₀ := by exact_mod_cast hn
    have : (n : ℝ) * ℓ ≤ n₀ * ℓ := mul_le_mul_of_nonneg_right this hℓpos.le
    linarith
  set e0 := PeriodicGridResidual.crNorm 0 ℓ (errArr (X 0) (sol.sample N τ₀))
  set F := PeriodicGridResidual.residualFlux 0 ℓ ℓ (fun k => errArr (X (k + 1)) (B k)) n
  have he0 : 0 ≤ e0 := PeriodicGridResidual.crNorm_nonneg _ _ _
  have hsF : 0 ≤ Real.sqrt F := Real.sqrt_nonneg _
  have hs : Real.sqrt (2 * n * ℓ) ≤ Real.sqrt (2 * T) :=
    Real.sqrt_le_sqrt (by nlinarith)
  have hexp : Real.exp (K * (t₁ - t₀)) ≤ Real.exp (K * T) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hT hK)
  have hinner : e0 + 2 ^ 0 * Real.sqrt (2 * n * ℓ) * Real.sqrt F + C0 * (t₁ - t₀) * ℓ ^ 2 ≤
      (1 + Real.sqrt (2 * T) + C0 * T) * (e0 + ℓ ^ 2 + Real.sqrt F) := by
    have h1 : Real.sqrt (2 * n * ℓ) * Real.sqrt F ≤ Real.sqrt (2 * T) * Real.sqrt F :=
      mul_le_mul_of_nonneg_right hs hsF
    have h2 : C0 * (t₁ - t₀) * ℓ ^ 2 ≤ C0 * T * ℓ ^ 2 := by
      have := mul_le_mul_of_nonneg_left hT hC0
      nlinarith [sq_nonneg ℓ]
    have h3 : 0 ≤ Real.sqrt (2 * T) := Real.sqrt_nonneg _
    have h4 : 0 ≤ C0 * T := by positivity
    simp only [pow_zero, one_mul]
    nlinarith [sq_nonneg ℓ, mul_nonneg h3 he0, mul_nonneg h3 (sq_nonneg ℓ), mul_nonneg h4 he0,
      mul_nonneg h4 hsF]
  have hinner0 : 0 ≤ e0 + 2 ^ 0 * Real.sqrt (2 * n * ℓ) * Real.sqrt F + C0 * (t₁ - t₀) * ℓ ^ 2 := by
    have := PeriodicGridResidual.crNorm_nonneg 0 ℓ
      (errArr (X n) (sol.sample N (τ₀ + n * ℓ)))
    have h3 : 0 ≤ Real.exp (K * (t₁ - t₀)) := (Real.exp_pos _).le
    by_contra hneg
    push Not at hneg
    have : 3 * (e0 + 2 ^ 0 * Real.sqrt (2 * n * ℓ) * Real.sqrt F + C0 * (t₁ - t₀) * ℓ ^ 2) *
        Real.exp (K * (t₁ - t₀)) < 0 :=
      mul_neg_of_neg_of_pos (by linarith) (Real.exp_pos _)
    linarith
  calc _ ≤ 3 * (e0 + 2 ^ 0 * Real.sqrt (2 * n * ℓ) * Real.sqrt F + C0 * (t₁ - t₀) * ℓ ^ 2) *
        Real.exp (K * (t₁ - t₀)) := h
    _ ≤ 3 * ((1 + Real.sqrt (2 * T) + C0 * T) * (e0 + ℓ ^ 2 + Real.sqrt F)) *
        Real.exp (K * T) := by
        gcongr
    _ = _ := by ring

/-- **Nodal time differences of the errors** (the step "subtraction of the reference step and
division by `h`" preceding `eq:supp-gowdy-hermite-jets`).  If along the history the
characteristic error is at most `E` and the residuals at most `ρ`, then for the non-moving
components `(P, Q, t)` and for `λ` the nodal time differences of the errors obey
`‖Δ_t e‖ / ℓ ≤ (15L + 32R) E + ρ/ℓ + C ℓ²`; with the pathwise `E = O(h²)` of
`eq:supp-gowdy-pathwise-c1` and the offset cap `ρ = O(h⁴)` of `eq:supp-gowdy-offset-cap` this is
`O(h²)`. -/
theorem nodal_time_difference (h0 : 0 < t₀) {R : ℝ} (hR : sol.chartRadius h0 ≤ R) (N : ℕ)
    [NeZero N] (hN : 2 * Real.pi / N ≤ sol.charStabStep h0 R) (τ₀ : ℝ) (n₀ : ℕ)
    (hτ₀ : t₀ ≤ τ₀) (hn₀ : τ₀ + n₀ * (2 * Real.pi / N) ≤ t₁) (X A B : ℕ → GridState N)
    (hstep : ∀ n < n₀, IsSplitStep (2 * Real.pi / N) (X n) (A n) (B n) ∧
      SplitEnvelope (t₀ / 2) R (2 * Real.pi / N) (X n) (A n) (B n)) {E ρ : ℝ}
    (hE : ∀ n ≤ n₀, charDist (X n) (sol.sample N (τ₀ + n * (2 * Real.pi / N))) ≤ E)
    (hρ : ∀ n < n₀, charDist (X (n + 1)) (B n) ≤ ρ) :
    ∀ n < n₀, ∀ j,
      ‖projZero (((X (n + 1)).site j).toVec -
          ((sol.sample N (τ₀ + (n + 1 : ℕ) * (2 * Real.pi / N))).site j).toVec -
          (((X n).site j).toVec - ((sol.sample N (τ₀ + n * (2 * Real.pi / N))).site j).toVec))‖ /
          (2 * Real.pi / N) ≤
        (15 * gowdyLipschitz (t₀ / 2) R + 32 * R) * E + ρ / (2 * Real.pi / N) +
          sol.charConsConst h0 * (2 * Real.pi / N) ^ 2 ∧
      |((X (n + 1)).lam j - (sol.sample N (τ₀ + (n + 1 : ℕ) * (2 * Real.pi / N))).lam j -
          ((X n).lam j - (sol.sample N (τ₀ + n * (2 * Real.pi / N))).lam j))| /
          (2 * Real.pi / N) ≤
        (15 * gowdyLipschitz (t₀ / 2) R + 32 * R) * E + ρ / (2 * Real.pi / N) +
          sol.charConsConst h0 * (2 * Real.pi / N) ^ 2 := by
  set ℓ := 2 * Real.pi / N with hℓ
  have hℓpos : 0 < ℓ := by
    have : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N))
    positivity
  have hR0 : 0 ≤ R := by linarith [(sol.chartRadius_spec h0).1]
  have hL0 := gowdyLipschitz_nonneg (by linarith : 0 < t₀ / 2) hR0
  intro n hn j
  have hτm : t₀ ≤ τ₀ + n * ℓ := by
    have : 0 ≤ (n : ℝ) * ℓ := by positivity
    linarith
  have hm' : ((n + 1 : ℕ) : ℝ) ≤ n₀ := by exact_mod_cast hn
  have hτh : τ₀ + n * ℓ + ℓ ≤ t₁ := by
    have : ((n + 1 : ℕ) : ℝ) * ℓ ≤ n₀ * ℓ := mul_le_mul_of_nonneg_right hm' hℓpos.le
    push_cast at this
    linarith
  obtain ⟨-, h2⟩ := sol.charStab_error_step h0 hR N hN (τ₀ + n * ℓ) hτm hτh (X n) (A n) (B n)
    (X (n + 1)) (hstep n hn).1 (hstep n hn).2
  have e : τ₀ + ((n + 1 : ℕ) : ℝ) * ℓ = τ₀ + n * ℓ + ℓ := by push_cast; ring
  rw [e]
  obtain ⟨a, b⟩ := h2 j
  have hEn := hE n hn.le
  have hρn := hρ n hn
  have hk : 0 ≤ 15 * gowdyLipschitz (t₀ / 2) R + 32 * R := by positivity
  have hbound : (15 * gowdyLipschitz (t₀ / 2) R + 32 * R) * ℓ *
        charDist (X n) (sol.sample N (τ₀ + n * ℓ)) + charDist (X (n + 1)) (B n) +
        sol.charConsConst h0 * ℓ ^ 3 ≤
      ((15 * gowdyLipschitz (t₀ / 2) R + 32 * R) * E + ρ / ℓ +
        sol.charConsConst h0 * ℓ ^ 2) * ℓ := by
    have : (15 * gowdyLipschitz (t₀ / 2) R + 32 * R) * ℓ *
        charDist (X n) (sol.sample N (τ₀ + n * ℓ)) ≤
        (15 * gowdyLipschitz (t₀ / 2) R + 32 * R) * ℓ * E :=
      mul_le_mul_of_nonneg_left hEn (by positivity)
    have e2 : ((15 * gowdyLipschitz (t₀ / 2) R + 32 * R) * E + ρ / ℓ +
        sol.charConsConst h0 * ℓ ^ 2) * ℓ = (15 * gowdyLipschitz (t₀ / 2) R + 32 * R) * ℓ * E +
        ρ + sol.charConsConst h0 * ℓ ^ 3 := by
      rw [add_mul, add_mul, div_mul_cancel₀ _ hℓpos.ne']; ring
    rw [e2]; linarith
  constructor
  · rw [div_le_iff₀ hℓpos]; exact a.trans hbound
  · rw [div_le_iff₀ hℓpos]; exact b.trans hbound

/-- **Non-vacuity of the envelope hypothesis**: the sampled reference history itself, with its
near-identity split-step realisations, satisfies the hypotheses of `state_error_charDist` (so
the theorem applies at least to `X_n = 𝖲_ℓ X_*(τ₀ + nℓ)`, every exact numerical solution being
compared with it). -/
theorem exists_envelope_history (h0 : 0 < t₀) {R : ℝ} (hR : sol.chartRadius h0 ≤ R) (N : ℕ)
    [NeZero N] (hN : 2 * Real.pi / N ≤ sol.charStabStep h0 R) (τ₀ : ℝ) (n₀ : ℕ)
    (hτ₀ : t₀ ≤ τ₀) (hn₀ : τ₀ + n₀ * (2 * Real.pi / N) ≤ t₁) :
    ∃ A B : ℕ → GridState N, ∀ n < n₀,
      IsSplitStep (2 * Real.pi / N) (sol.sample N (τ₀ + n * (2 * Real.pi / N))) (A n) (B n) ∧
      SplitEnvelope (t₀ / 2) R (2 * Real.pi / N) (sol.sample N (τ₀ + n * (2 * Real.pi / N)))
        (A n) (B n) := by
  set ℓ := 2 * Real.pi / N with hℓ
  have hℓpos : 0 < ℓ := by
    have : (0 : ℝ) < N := Nat.cast_pos.2 (Nat.pos_of_ne_zero (NeZero.ne N))
    positivity
  have hR0 : 0 ≤ R := by linarith [(sol.chartRadius_spec h0).1]
  have hNb := (sol.charStabStep_spec h0 hR0 hℓpos.le hN).1
  have hex : ∀ n : ℕ, ∃ A B : GridState N, n < n₀ →
      IsSplitStep ℓ (sol.sample N (τ₀ + n * ℓ)) A B ∧
      SplitEnvelope (t₀ / 2) R ℓ (sol.sample N (τ₀ + n * ℓ)) A B := by
    intro n
    by_cases hn : n < n₀
    · have hτm : t₀ ≤ τ₀ + n * ℓ := by
        have : 0 ≤ (n : ℝ) * ℓ := by positivity
        linarith
      have hm' : ((n + 1 : ℕ) : ℝ) ≤ n₀ := by exact_mod_cast hn
      have hτh : τ₀ + n * ℓ + ℓ ≤ t₁ := by
        have : ((n + 1 : ℕ) : ℝ) * ℓ ≤ n₀ * ℓ := mul_le_mul_of_nonneg_right hm' hℓpos.le
        push_cast at this
        linarith
      obtain ⟨X₁, X₃, h₁, h₃, hd₁, hd₃⟩ := sol.step_exists h0 N hNb (τ₀ + n * ℓ) hτm hτh
      exact ⟨X₁, X₃, fun _ => ⟨⟨h₁, h₃⟩,
        sol.charStab_reference_envelope h0 N hNb _ hτm hτh X₁ X₃ h₁ hd₁ hd₃ hR⟩⟩
    · exact ⟨sol.sample N 0, sol.sample N 0, fun h => absurd h hn⟩
  choose A B hAB using hex
  exact ⟨A, B, fun n hn => hAB n hn⟩

end GowdyFrameSolution

end

end RenewalGeometry.GowdyStaggered
