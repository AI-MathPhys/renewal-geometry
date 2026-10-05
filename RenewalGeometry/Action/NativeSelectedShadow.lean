/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Action.SameRecordSourceSelectionExact
import RenewalGeometry.Continuum.AposterioriShadowRate

/-!
# Same-source selected exact physical shadow (`thm:native-selected-shadow`)

Einstein–Standard-Model action-closure manuscript, `thm:native-selected-shadow`
(`eq:selected-shadow-forcing`, `eq:selected-shadow-budget`, `eq:selected-exact-shadow`): one
actually
observed record, selected by the same-record score of `cor:source-selected-shadow-budgets`, supplies
the finite Euler row, the regularity reserve and the near-compatible initial datum from which its
exact physical comparison future is constructed.

The proof is the manuscript's composition:

* `thm:source-selection` / `cor:source-selected-shadow-budgets` (proved:
  `SourceSelection.FiniteAcceptedProcess.selection_failure_le` with the third readout
  `W = c_h² = |Φ_h(·,0)|²` and threshold `β_h`) — the failure probability
  `eq:source-shadow-selection-failure`;
* `cor:native-reader-sobolev` and `prop:shadow-residual-upgrade` (proved) — on the success event,
  `V_h ≤ R²` and `σ_h ≤ s_h` give `ε_h ≤ C_R(s_h + h)` and forcing `≤ η(ε_h)`; monotonicity of
  `η` (`AposterioriShadowRate.shadowEta_mono`) gives the forcing budget `η̄_{h,k}` of
  `eq:selected-shadow-forcing` with `ε̄_h = C_R(s_h + h)`;
* `prop:initial-constraint-retraction` (proved) with the uniform margins, `ass:physical-Cauchy-tube`
  and `thm:aposteriori-physical-shadow` (`AposterioriShadow.aposteriori_physical_shadow`, which is
  conditional on the conclusion of the open `prop:coupled-bootstrap`).

Renderings disclosed: the selection process is the finite weighted outcome space of
`SameRecordSourceSelectionExact`; legal records `x` carry an abstract slab-model record `zrec x`
(`AposterioriShadow.SlabModel`, `Σ = 𝕋³` only through the model), the composite charge is
`c_h(x) = |Φ_h(x,0)|` of the exact reduction at the record's initial state; the chart, normalization
and tube-membership requirements of every legal record are hypotheses on the legal state space
(violations are illegal states, counted in `p_h^exit`); the combined output of
`cor:native-reader-sobolev` and `prop:shadow-residual-upgrade` on the selected thresholds is the
hypothesis `hupgrade` (both are proved records; the abstract model does not re-derive them from the
concrete trigonometric record).
-/

open Metric Finset

namespace RenewalGeometry.SelectedShadow

open AposterioriShadow AposterioriShadowRate SourceSelection

noncomputable section

variable {Ω 𝒳 : Type*} [Fintype Ω] [Fintype 𝒳] [DecidableEq 𝒳] [DecidableEq Ω]
variable {Z X O : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [PseudoMetricSpace O]
variable {Y : Type*} [AddCommGroup Y] [Module ℝ Y]

/-- The selected-shadow forcing budget `η̄_{h,k} = C_R(ε̄^{1-k/s} + ε̄^{1-(k+1)/s})` with
`ε̄_h = C_R(s_h + h)` (`eq:selected-shadow-forcing`). -/
def selectedEta (CR k s sh h : ℝ) : ℝ := shadowEta CR k s (CR * (sh + h))

/-- The budget `d̄_h = 2B_*γ_*⁻¹β_h + C_R√T η̄_{h,k}` (`eq:selected-shadow-budget`). -/
def selectedBudget (B γ β c τ CR k s sh h : ℝ) : ℝ :=
  shadowBudget B γ β c τ (selectedEta CR k s sh h)

/-- **`thm:native-selected-shadow`** (conditional on the conclusion of the open
`prop:coupled-bootstrap`, carried as `hboot`).

Hypotheses: the signed action-drift hypotheses of `thm:source-selection` on the finite accepted
process (`ha`, `hκ`, `hδ`, `hdrift`), a selection rule minimising the score
`g²/s_h² + V/R² + c_h²/β_h²` on surviving prefixes (`hsel`); the Cauchy tube `T`; for every legal
record `x` an admissible normalized record `zrec x` in harmonic/temporal gauge, an exact reduction
`R x` at its initial state with the uniform margins `γ_*`, `r_*`, `B_*`, corrected data in
`𝒞_k^reg ∩ 𝒪_k`; the reader/upgrade output `hupgrade`; and the budget `d̄_h` below the stability
radius.

Conclusions: (1) the probability of failing to output a surviving record with `g_h ≤ s_h`,
`V_h ≤ R²`, `c_h ≤ β_h` is at most the boxed bound `eq:source-shadow-selection-failure`; (2) on that
success event the selected actually observed record has a unique exact zero `λ_h` of its retained
constraint map, the corrected datum generates the unique exact solution `z_{*,h}` of the tube, and
`dist(obs ẑ_{h,j_*}, obs z_{*,h}) ≤ C d̄_h` (`eq:selected-exact-shadow`). -/
theorem native_selected_shadow (proc : FiniteAcceptedProcess Ω 𝒳)
    (a g V : 𝒳 → ℝ) (rr : ℕ → 𝒳 → ℝ) {Am Ap κ δ sh Rr β : ℝ}
    (ha : ∀ x, Am ≤ a x ∧ a x ≤ Ap) (hκ : 0 < κ) (hδ : 0 < δ) (hsh : 0 < sh) (hRr : 0 < Rr)
    (hβ : 0 < β) (hg : ∀ x, 0 ≤ g x) (hV : ∀ x, 0 ≤ V x) (J : ℕ) (hJ : 0 < J)
    (hdrift : ∀ j < J, ∀ x, 0 < proc.survivingMass j x →
      proc.actionDrift a j x ≤ -(κ * δ) * g x ^ 2 + δ * rr j x)
    (M : SlabModel Z X O) {Ck : X → Y} (T : CauchyTube M Ck)
    (hboot : CoupledBootstrapConclusion M T.family T.dstar T.Cstar)
    (zrec : 𝒳 → Z) (hadm : ∀ x, M.Admissible (zrec x)) (hharm : ∀ x, M.harm (zrec x) = 0)
    {m : 𝒳 → ℕ} {r B γ : ℝ}
    (R : ∀ x, ExactInitialConstraintReduction Ck (M.init (zrec x)) (m x) r B) (hγ : 0 < γ)
    (hA : ∀ x, ∀ v, γ * ‖v‖ ≤ ‖fderivWithin ℝ (R x).retained (closedBall 0 r) 0 v‖)
    (hmargin : ∀ x, ∀ l ∈ closedBall (0 : EuclideanSpace ℝ (Fin (m x))) r,
      ‖fderivWithin ℝ (R x).retained (closedBall 0 r) l -
        fderivWithin ℝ (R x).retained (closedBall 0 r) 0‖ ≤ γ / 2)
    (hrad : 2 * γ⁻¹ * β ≤ r) (hB : 0 ≤ B)
    (htube : ∀ x, ∀ l ∈ closedBall (0 : EuclideanSpace ℝ (Fin (m x))) (2 * γ⁻¹ * β),
      (R x).retained l = 0 → (R x).corr l ∈ T.Creg ∩ T.nbhd)
    (sel : Ω → ℕ)
    (hsel : ∀ ω ∈ proc.S J, sel ω < J ∧ ∀ j < J,
      FiniteAcceptedProcess.score g V (fun x => ‖(R x).retained 0‖ ^ 2) sh Rr β
          (proc.X (sel ω) ω) ≤
        FiniteAcceptedProcess.score g V (fun x => ‖(R x).retained 0‖ ^ 2) sh Rr β (proc.X j ω))
    {h CR k s c τ : ℝ} (εr : 𝒳 → ℝ) (hk : 0 ≤ k) (hks : k + 1 ≤ s) (hCR : 0 ≤ CR)
    (hupgrade : ∀ x, V x ≤ Rr ^ 2 → g x ≤ sh →
      0 ≤ εr x ∧ εr x ≤ CR * (sh + h) ∧
        M.resB (zrec x) + M.resD (zrec x) ≤ shadowEta CR k s (εr x))
    (hc : 0 < c) (hτ : 0 < τ)
    (hsmall : selectedBudget B γ β c τ CR k s sh h ≤ T.stabilityRadius c τ) :
    (∑ ω ∈ Finset.univ.filter (fun ω => ω ∉ proc.S J ∨
        ¬ (g (proc.X (sel ω) ω) ≤ sh ∧ V (proc.X (sel ω) ω) ≤ Rr ^ 2 ∧
          ‖(R (proc.X (sel ω) ω)).retained 0‖ ^ 2 ≤ β ^ 2)), proc.P ω
      ≤ proc.exitProbability J + (Ap - Am) / (κ * δ * J * sh ^ 2)
        + proc.occupation J rr / (κ * sh ^ 2)
        + proc.occupation J (fun _ x => V x) / Rr ^ 2
        + proc.occupation J (fun _ x => ‖(R x).retained 0‖ ^ 2) / β ^ 2) ∧
    ∀ ω ∈ proc.S J, g (proc.X (sel ω) ω) ≤ sh → V (proc.X (sel ω) ω) ≤ Rr ^ 2 →
      ‖(R (proc.X (sel ω) ω)).retained 0‖ ≤ β →
      ∃ l : EuclideanSpace ℝ (Fin (m (proc.X (sel ω) ω))),
        (l ∈ closedBall 0 (2 * γ⁻¹ * β) ∧ (R (proc.X (sel ω) ω)).retained l = 0) ∧
        Ck ((R (proc.X (sel ω) ω)).corr l) = 0 ∧
        ‖(R (proc.X (sel ω) ω)).corr l - M.init (zrec (proc.X (sel ω) ω))‖ ≤ 2 * B * γ⁻¹ * β ∧
        M.IsExact (T.evolve ((R (proc.X (sel ω) ω)).corr l)) ∧
        (∀ z, M.IsExact z → M.init z = (R (proc.X (sel ω) ω)).corr l →
          z = T.evolve ((R (proc.X (sel ω) ω)).corr l)) ∧
        dist (M.obs (zrec (proc.X (sel ω) ω)))
            (M.obs (T.evolve ((R (proc.X (sel ω) ω)).corr l))) ≤
          T.shadowConst c τ * selectedBudget B γ β c τ CR k s sh h := by
  refine ⟨proc.selection_failure_le a g V (fun x => ‖(R x).retained 0‖ ^ 2) rr Am Ap κ δ sh Rr β
    ha hκ hδ hsh hRr hβ hg hV (fun x => sq_nonneg _) J hJ hdrift sel hsel, ?_⟩
  intro ω _ hgx hVx hcx
  set x := proc.X (sel ω) ω
  obtain ⟨hε0, hε, hforce⟩ := hupgrade x hVx hgx
  have hη : M.resB (zrec x) + M.resD (zrec x) ≤ selectedEta CR k s sh h :=
    hforce.trans (shadowEta_mono hCR hk hks hε0 hε)
  obtain ⟨l, hl, -, hC, hd, hex, -, hun, hdist⟩ :=
    aposteriori_physical_shadow M T hboot (hadm x) (hharm x) (R x) hγ (hA x) (hmargin x) hcx hrad
      hB (htube x) hc hτ hη hsmall
  exact ⟨l, hl, hC, hd, hex, hun, hdist⟩

/-- The success thresholds of the selector in squared form are the paper's thresholds:
`c_h² ≤ β_h² ↔ c_h ≤ β_h` for the nonnegative charge `c_h = |Φ_h(·,0)|`. -/
theorem charge_sq_le_iff {cx β : ℝ} (hc : 0 ≤ cx) (hβ : 0 ≤ β) : cx ^ 2 ≤ β ^ 2 ↔ cx ≤ β :=
  pow_le_pow_iff_left₀ hc hβ (by norm_num)

end

end RenewalGeometry.SelectedShadow
