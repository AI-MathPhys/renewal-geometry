/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Action.ExactInitialCalculusConstraint
import RenewalGeometry.Analysis.LyapunovSchmidtRangeReduction

/-!
# The original-action constraint map on one mesh-independent ball
  (`lem:supp-initial-calculus`; emergent-spacetime manuscript)

`CHmap`: the four original lapse–shift rows evaluated at the joint stationary/Legendre solution
`z_h(X)` of the uniform solve (`ExactInitialCalculusSolve.lean`):
`C_h(X) = CrowH(X, z_h(X))`, a map `P^r_h = (H^{r+2}_h)^6 × (H^{r+1}_h)^6 → (H^r_h)^4`.

* **`exists_derivBound_CH`**: for `χ ≠ 0`, `r ≥ 2` and every `K` there are `N`-independent
  constants such that, for every odd `N` with `h < h₀`, `C_h` has `DerivBound` of order `K + 2` on
  the fixed ball `B(0, del)`.
* **`exists_CH_taylor`** (`eq:supp-initial-nonlinear-bounds`): writing `C_h = DC_h(0) + N_h`,
  `‖N_h(X)‖ ≤ C ‖X‖²`, `‖DN_h(X)‖ ≤ C ‖X‖` on the fixed ball, `C` independent of `N`.
-/

open Filter Finset Metric Set
open scoped Topology

noncomputable section

namespace RenewalGeometry.ExactPhaseAction.InitialCalculus

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

set_option linter.unusedSectionVars false

open QuadJet PeriodicGridSobolev GridLocalOps IteratedDerivBounds UniformDerivBounds
open UniformImplicit

variable {N : ℕ} [NeZero N]

theorem hyp_mono_rho {E Z Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y] {F : E × Z → Y} {T : Z ≃L[ℝ] Y}
    {K : ℕ} {M a ρ ρ' : ℝ} (h : Hyp F T K M a ρ) (hρ' : 0 < ρ') (hle : ρ' ≤ ρ) :
    Hyp F T K M a ρ' :=
  ⟨hρ', h.ha, h.hT, h.hF.subset (ball_subset_ball hle), h.hF0, h.hDF⟩

/-- **The original-action constraint map on the common ball**: the four lapse–shift rows at the
joint stationary/Legendre solution. -/
def CHmap (hNo : Odd N) (χ : ℝ) (r : ℕ) (M a ρ : ℝ) (X : XH N r) : Fin 4 → GridH N r :=
  CrowH hNo χ r (X, imp (FH hNo χ r) M a ρ X)

/-- **Mesh-uniform derivative bounds for the constraint map on one ball.** -/
theorem exists_derivBound_CH {χ : ℝ} (hχ : χ ≠ 0) (r : ℕ) (hr : 2 ≤ r) (K : ℕ) :
    ∃ M ρ h₀ Mc : ℝ, 0 < h₀ ∧ 0 ≤ Mc ∧ ∀ (N : ℕ) [NeZero N] (hNo : Odd N), hN N < h₀ →
      Hyp (FH hNo χ r) (TH (N := N) hχ r) K M (aBlock hχ) ρ ∧
      DerivBound (CHmap hNo χ r M (aBlock hχ) ρ) (ball 0 (del M (aBlock hχ) ρ)) (K + 2) Mc := by
  obtain ⟨M, ρF, h₁, hh₁, hyp⟩ := exists_uniform_solve hχ r hr K
  obtain ⟨ρC, hρC, MC, hMC, h₂, hh₂, hC⟩ := exists_derivBound_CrowH χ r hr (K + 2)
  -- the radius of the solve, below the radius of the rows
  have hρF : ∀ (N : ℕ) [NeZero N] (hNo : Odd N), hN N < h₁ → 0 < ρF := fun N _ hNo hh =>
    (hyp N hNo hh).hρ
  set ρ := min ρF ρC
  set a := aBlock hχ
  set Mf := max 1 (del M a ρ) + impC K M a ρ
  refine ⟨M, ρ, min h₁ h₂, (Nat.factorial (K + 2) : ℝ) * MC * max 1 Mf ^ (K + 2),
    lt_min hh₁ hh₂, by positivity, fun N _ hNo hh => ?_⟩
  have hh1 : hN N < h₁ := hh.trans_le (min_le_left _ _)
  have hh2 : hN N < h₂ := hh.trans_le (min_le_right _ _)
  have hρ : 0 < ρ := lt_min (hρF N hNo hh1) hρC
  have h := hyp_mono_rho (hyp N hNo hh1) hρ (min_le_left _ _)
  refine ⟨h, ?_⟩
  have hdel : 0 ≤ del M a ρ := h.del_pos.le
  have himp := h.derivBound_imp
  have hgraph := derivBound_graph himp isOpen_ball hdel ball_subset_closedBall
    (himp.nonneg (mem_ball_self h.del_pos))
  have hmaps : MapsTo (fun X : XH N r => (X, imp (FH hNo χ r) M a ρ X))
      (ball (0 : XH N r) (del M a ρ)) (ball (0 : XH N r × ZH N r) ρC) := by
    intro X hX
    have hX' : ‖X‖ < del M a ρ := by simpa using hX
    have hs := (h.imp_spec hX').1
    rw [mem_ball_zero_iff, Prod.norm_def]
    have h1 : ‖X‖ ≤ sig M a ρ := hX'.le.trans h.del_le_sig
    exact lt_of_le_of_lt (max_le h1 hs) (h.sig_lt.trans_le (min_le_right _ _))
  have hc := derivBound_comp (g := CrowH hNo χ r) (hC N hNo hh2) isOpen_ball hgraph isOpen_ball hmaps
  exact hc.congr fun X => rfl

/-- **The nonlinear bounds `eq:supp-initial-nonlinear-bounds`** with cutoff-independent constants:
`‖C_h(X) - C_h(0) - DC_h(0)X‖ ≤ C‖X‖²` and `‖DC_h(X) - DC_h(0)‖ ≤ C‖X‖` on the fixed ball. -/
theorem exists_CH_taylor {χ : ℝ} (hχ : χ ≠ 0) (r : ℕ) (hr : 2 ≤ r) :
    ∃ M ρ h₀ C : ℝ, 0 < h₀ ∧ 0 ≤ C ∧ ∀ (N : ℕ) [NeZero N] (hNo : Odd N), hN N < h₀ →
      0 < del M (aBlock hχ) ρ ∧
      ∀ X ∈ ball (0 : XH N r) (del M (aBlock hχ) ρ),
        ‖fderiv ℝ (CHmap hNo χ r M (aBlock hχ) ρ) X - fderiv ℝ (CHmap hNo χ r M (aBlock hχ) ρ) 0‖ ≤
            C * ‖X‖ ∧
        ‖CHmap hNo χ r M (aBlock hχ) ρ X - CHmap hNo χ r M (aBlock hχ) ρ 0 -
            fderiv ℝ (CHmap hNo χ r M (aBlock hχ) ρ) 0 X‖ ≤ C * ‖X‖ ^ 2 := by
  obtain ⟨M, ρ, h₀, Mc, hh₀, hMc, hall⟩ := exists_derivBound_CH hχ r hr 0
  refine ⟨M, ρ, h₀, Mc, hh₀, hMc, fun N _ hNo hh => ?_⟩
  obtain ⟨h, hD⟩ := hall N hNo hh
  refine ⟨h.del_pos, ?_⟩
  set CH := CHmap hNo χ r M (aBlock hχ) ρ
  have hd : ∀ X ∈ ball (0 : XH N r) (del M (aBlock hχ) ρ), HasFDerivAt CH (fderiv ℝ CH X) X :=
    fun X hX => ((hD.contDiffAt isOpen_ball hX).differentiableAt (by simp)).hasFDerivAt
  have hL : ∀ X ∈ ball (0 : XH N r) (del M (aBlock hχ) ρ),
      ‖fderiv ℝ CH X - fderiv ℝ CH 0‖ ≤ Mc * ‖X‖ := by
    intro X hX
    have := norm_fderiv_sub_le_of_derivBound hD isOpen_ball (convex_ball 0 _) hX
      (mem_ball_self h.del_pos)
    simpa using this
  have hT := LyapunovSchmidt.taylor_remainder_bounds (Φ := fun X => CH X - CH 0)
    (DΦ := fun X => fderiv ℝ CH X) (ρ := del M (aBlock hχ) ρ)
    (fun X hX => (hd X hX).sub_const (CH 0)) hL hMc (by simp)
  intro X hX
  refine ⟨hL X hX, ?_⟩
  have := hT.2 X hX
  simpa using this

end RenewalGeometry.ExactPhaseAction.InitialCalculus
