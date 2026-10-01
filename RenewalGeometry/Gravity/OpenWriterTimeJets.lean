/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.OpenWriterLawFamily

/-!
# Uniform physical time jets of the open writer and of the law family
  (`lem:supp-open-time-jets`)

Along a solution of the law-family writer `eq:supp-law-family` (the open writer is the mark
`B = 0`) staying in the common top ball `‖X‖_{X^s_h} ≤ ε` on `[0, T]`, the time jets satisfy
`‖q‖_{s+1,h} + ‖q_t‖_{s,h} + ‖q_tt‖_{s-1,h} + ‖q_ttt‖_{s-2,h} ≤ C_s ε`, uniformly in the mesh and in
the mark (`s ≥ 4`; the manuscript takes `s ≥ 11`).

* `moser_rate_coefficients`, `moser_rate_compensator`: Moser bounds for the coefficient time
  derivatives `ȧ = Da(g)[v]`, `ċ`, `ḃ` and for the compensator differential `D𝖦(w)[w']`
  (analytic functions of the pair, vanishing at the origin);
* `hasDerivWithinAt_divArr`, `hasDerivWithinAt_skewArr`: product rules for the flux and the skew
  transport along a history;
* `jetDeriv`, `hasDerivWithinAt_lawAccel`: the third time derivative `q_ttt` obtained by
  differentiating the mass row once (`a q_ttt = (row)' - ȧ q_tt`);
* `law_time_jets` (**`lem:supp-open-time-jets`**).
-/

open Set Metric Filter Topology Finset MeasureTheory
open scoped NNReal BigOperators

namespace RenewalGeometry.OpenWriterLifespan

open RootParityConnector OpenWriterGridBridge OpenWriterChart OpenWriterEnergy HarmonicWriter
  OpenWriterEnergyEstimate

noncomputable section

set_option linter.unusedSectionVars false

variable {N : ℕ} [NeZero N]

/-! ### Moser bounds for the coefficient rates -/

/-- `ḃ^i = Db^i(g)[v]` along a record. -/
def bdot (q v : Grid N → MetricRec) (i : Fin 3) : Grid N → ℝ :=
  fun x => fderiv ℝ (harmB i) (minkowski + q x) (v x)

/-- The basis of record pairs. -/
def bP : Module.Basis ((Σ _ : Fin 4, Fin 4) ⊕ (Σ _ : Fin 4, Fin 4)) ℝ (MetricRec × MetricRec) :=
  bM.prod bM

theorem coordSum_bP (r : ℕ) (q v : Grid N → MetricRec) :
    PeriodicGridSobolev.Moser.coordSum r bP (fun x => (q x, v x)) =
      PeriodicGridSobolev.Moser.coordSum r bM q + PeriodicGridSobolev.Moser.coordSum r bM v := by
  unfold PeriodicGridSobolev.Moser.coordSum
  rw [Fintype.sum_sum_type]
  congr 1

/-- The rate map `(w, z) ↦ DA(η + w)[z]` of an analytic coefficient is analytic at the origin. -/
theorem analyticAt_rate {A : MetricRec → ℝ} (hA : AnalyticAt ℝ A minkowski) :
    AnalyticAt ℝ (fun p : MetricRec × MetricRec => fderiv ℝ A (minkowski + p.1) p.2) 0 := by
  have hg : AnalyticAt ℝ (fun p : MetricRec × MetricRec => minkowski + p.1) 0 := by fun_prop
  have hD : AnalyticAt ℝ (fun p : MetricRec × MetricRec => fderiv ℝ A (minkowski + p.1)) 0 :=
    hA.fderiv.comp_of_eq hg (by simp)
  exact ((ContinuousLinearMap.id ℝ (MetricRec →L[ℝ] ℝ)).analyticAt_bilinear _).comp
    (hD.prod (by fun_prop))

/-- **Moser bounds for the coefficient rates**: `‖ȧ‖_{r,h}, ‖ċ^{ij}‖_{r,h}, ‖ḃ^i‖_{r,h} ≤
C (S_r(q) + S_r(v))` on a mesh-independent ball. -/
theorem moser_rate_coefficients (r : ℕ) (hr : 2 ≤ r) :
    ∃ δ > 0, ∃ C ≥ 0, ∀ (N : ℕ) [NeZero N] (q v : Grid N → MetricRec),
      PeriodicGridSobolev.Moser.coordSum r bM q + PeriodicGridSobolev.Moser.coordSum r bM v ≤ δ →
      PeriodicGridSobolev.sobNorm r (cx (adot q v)) ≤
          C * (PeriodicGridSobolev.Moser.coordSum r bM q +
            PeriodicGridSobolev.Moser.coordSum r bM v) ∧
      (∀ i j, PeriodicGridSobolev.sobNorm r (cx (cdot q v i j)) ≤
          C * (PeriodicGridSobolev.Moser.coordSum r bM q +
            PeriodicGridSobolev.Moser.coordSum r bM v)) ∧
      ∀ i, PeriodicGridSobolev.sobNorm r (cx (bdot q v i)) ≤
          C * (PeriodicGridSobolev.Moser.coordSum r bM q +
            PeriodicGridSobolev.Moser.coordSum r bM v) := by
  let F : Fin 1 ⊕ (Fin 3 × Fin 3 ⊕ Fin 3) → MetricRec → ℝ
    | Sum.inl _ => harmA
    | Sum.inr (Sum.inl ij) => harmC ij.1 ij.2
    | Sum.inr (Sum.inr i) => harmB i
  have hF : ∀ k, AnalyticAt ℝ (F k) minkowski := by
    rintro (k | ij | i)
    · exact analyticAt_harmA
    · exact analyticAt_harmC ij.1 ij.2
    · exact analyticAt_harmB i
  obtain ⟨δ, hδ, C, hC, h⟩ := uniformize (fun k δ C => ∀ (N : ℕ) [NeZero N]
      (u : Grid N → MetricRec × MetricRec), PeriodicGridSobolev.Moser.coordSum r bP u ≤ δ →
      PeriodicGridSobolev.sobNorm r (fun x => ((fderiv ℝ (F k) (minkowski + (0 + u x).1) (0 + u x).2 -
        fderiv ℝ (F k) (minkowski + (0 : MetricRec × MetricRec).1)
          (0 : MetricRec × MetricRec).2 : ℝ) : ℂ))
        ≤ C * PeriodicGridSobolev.Moser.coordSum r bP u ^ 1)
    (fun k δ δ' C C' _ hδ' hC' hP N _ u hu => (hP N u (hu.trans hδ')).trans (by
      gcongr; exact pow_nonneg (PeriodicGridSobolev.Moser.coordSum_nonneg _ _ _) _))
    (fun k => by
      obtain ⟨pp, R, hp⟩ := analyticAt_rate (hF k)
      exact PeriodicGridSobolev.Moser.moser_composition_order r hr bP hp 1 le_rfl
        (fun n h1 h2 => absurd h2 (by omega)))
  refine ⟨δ, hδ, C, hC, fun N _ q v hqv => ?_⟩
  have hu := (coordSum_bP r q v).symm ▸ hqv
  have key : ∀ k, PeriodicGridSobolev.sobNorm r
      (fun x => ((fderiv ℝ (F k) (minkowski + q x) (v x) : ℝ) : ℂ)) ≤
      C * (PeriodicGridSobolev.Moser.coordSum r bM q + PeriodicGridSobolev.Moser.coordSum r bM v) := by
    intro k
    have := h k N (fun x => (q x, v x)) hu
    rw [coordSum_bP, pow_one] at this
    convert this using 2
    funext x
    simp
  refine ⟨key (Sum.inl 0), fun i j => key (Sum.inr (Sum.inl (i, j))), fun i => key (Sum.inr (Sum.inr i))⟩

/-- The compensator differential `(w, w') ↦ D𝖦(w)[w']` is analytic at the origin. -/
theorem analyticAt_compensator_rate (μ ν : Fin 4) :
    AnalyticAt ℝ (fun p : JetSpace × JetSpace =>
      fderiv ℝ (fun w : JetSpace => compensatorMap w μ ν) p.1 p.2) 0 := by
  have hD : AnalyticAt ℝ (fun p : JetSpace × JetSpace =>
      fderiv ℝ (fun w : JetSpace => compensatorMap w μ ν) p.1) 0 :=
    (analyticAt_compensatorMap μ ν 0).fderiv.comp_of_eq (by fun_prop) rfl
  exact ((ContinuousLinearMap.id ℝ (JetSpace →L[ℝ] ℝ)).analyticAt_bilinear _).comp
    (hD.prod (by fun_prop))

/-- The basis of jet pairs. -/
def bJP := bJ.prod bJ

theorem coordSum_bJP (r : ℕ) (w w' : Grid N → JetSpace) :
    PeriodicGridSobolev.Moser.coordSum r bJP (fun x => (w x, w' x)) =
      PeriodicGridSobolev.Moser.coordSum r bJ w + PeriodicGridSobolev.Moser.coordSum r bJ w' := by
  unfold PeriodicGridSobolev.Moser.coordSum
  rw [Fintype.sum_sum_type]
  congr 1

/-- **Moser bound for the compensator differential**: `‖D𝖦(w)[w']‖_{r,h} ≤ C (S_r(w) + S_r(w'))`. -/
theorem moser_rate_compensator (r : ℕ) (hr : 2 ≤ r) :
    ∃ δ > 0, ∃ C ≥ 0, ∀ (N : ℕ) [NeZero N] (w w' : Grid N → JetSpace),
      PeriodicGridSobolev.Moser.coordSum r bJ w + PeriodicGridSobolev.Moser.coordSum r bJ w' ≤ δ →
      ∀ μ ν : Fin 4, PeriodicGridSobolev.sobNorm r (fun x =>
        ((fderiv ℝ (fun u : JetSpace => compensatorMap u μ ν) (w x) (w' x) : ℝ) : ℂ)) ≤
        C * (PeriodicGridSobolev.Moser.coordSum r bJ w + PeriodicGridSobolev.Moser.coordSum r bJ w') := by
  obtain ⟨δ, hδ, C, hC, h⟩ := uniformize (ι := Fin 4 × Fin 4) (fun k δ C => ∀ (N : ℕ) [NeZero N]
      (u : Grid N → JetSpace × JetSpace), PeriodicGridSobolev.Moser.coordSum r bJP u ≤ δ →
      PeriodicGridSobolev.sobNorm r (fun x =>
        ((fderiv ℝ (fun w : JetSpace => compensatorMap w k.1 k.2) (0 + u x).1 (0 + u x).2 -
          fderiv ℝ (fun w : JetSpace => compensatorMap w k.1 k.2) (0 : JetSpace × JetSpace).1
            (0 : JetSpace × JetSpace).2 : ℝ) : ℂ))
        ≤ C * PeriodicGridSobolev.Moser.coordSum r bJP u ^ 1)
    (fun k δ δ' C C' _ hδ' hC' hP N _ u hu => (hP N u (hu.trans hδ')).trans (by
      gcongr; exact pow_nonneg (PeriodicGridSobolev.Moser.coordSum_nonneg _ _ _) _))
    (fun k => by
      obtain ⟨pp, R, hp⟩ := analyticAt_compensator_rate k.1 k.2
      exact PeriodicGridSobolev.Moser.moser_composition_order r hr bJP hp 1 le_rfl
        (fun n h1 h2 => absurd h2 (by omega)))
  refine ⟨δ, hδ, C, hC, fun N _ w w' hww μ ν => ?_⟩
  have hu := (coordSum_bJP r w w').symm ▸ hww
  have := h (μ, ν) N (fun x => (w x, w' x)) hu
  rw [coordSum_bJP, pow_one] at this
  convert this using 2
  funext x
  simp

end

end RenewalGeometry.OpenWriterLifespan
