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


/-! ### Product rules along a history -/

theorem divArr_expand (c : Fin 3 → Fin 3 → Grid N → ℝ) (Q : Grid N → ℝ) (x : Grid N) :
    divArr c Q x = ∑ i, ∑ j, (N : ℝ) * (c i j x * ((N : ℝ) * (Q (x + e N j) - Q x)) -
      c i j (x - e N i) * ((N : ℝ) * (Q (x - e N i + e N j) - Q (x - e N i)))) := by
  simp only [divArr, OpenWriterEnergy.Dm_apply, OpenWriterEnergy.Dp_apply]

theorem hasDerivWithinAt_divArr {S : Set ℝ} {t : ℝ} (c : ℝ → Fin 3 → Fin 3 → Grid N → ℝ)
    (c' : Fin 3 → Fin 3 → Grid N → ℝ) (Q : ℝ → Grid N → ℝ) (Q' : Grid N → ℝ)
    (hc : ∀ i j y, HasDerivWithinAt (fun τ => c τ i j y) (c' i j y) S t)
    (hQ : ∀ y, HasDerivWithinAt (fun τ => Q τ y) (Q' y) S t) (x : Grid N) :
    HasDerivWithinAt (fun τ => divArr (c τ) (Q τ) x)
      (divArr c' (Q t) x + divArr (c t) Q' x) S t := by
  simp only [divArr_expand]
  refine (HasDerivWithinAt.fun_sum fun i _ => HasDerivWithinAt.fun_sum fun j _ =>
    ((((hc i j x).mul (((hQ _).sub (hQ _)).const_mul _)).sub
      ((hc i j _).mul (((hQ _).sub (hQ _)).const_mul _))).const_mul _)).congr_deriv ?_
  rw [← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [← sum_add_distrib]
  refine sum_congr rfl fun j _ => ?_
  simp only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply]
  ring

theorem skewArr_expand (b : Fin 3 → Grid N → ℝ) (V : Grid N → ℝ) (x : Grid N) :
    skewArr b V x = ∑ i, (b i x * (((N : ℝ) * (V (x + e N i) - V x) +
      (N : ℝ) * (V x - V (x - e N i))) / 2) +
      ((N : ℝ) * (b i (x + e N i) * V (x + e N i) - b i x * V x) +
        (N : ℝ) * (b i x * V x - b i (x - e N i) * V (x - e N i))) / 2) := by
  simp only [skewArr, OpenWriterEnergy.D0_apply, OpenWriterEnergy.Dp_apply,
    OpenWriterEnergy.Dm_apply]

theorem hasDerivWithinAt_skewArr {S : Set ℝ} {t : ℝ} (b : ℝ → Fin 3 → Grid N → ℝ)
    (b' : Fin 3 → Grid N → ℝ) (V : ℝ → Grid N → ℝ) (V' : Grid N → ℝ)
    (hb : ∀ i y, HasDerivWithinAt (fun τ => b τ i y) (b' i y) S t)
    (hV : ∀ y, HasDerivWithinAt (fun τ => V τ y) (V' y) S t) (x : Grid N) :
    HasDerivWithinAt (fun τ => skewArr (b τ) (V τ) x)
      (skewArr b' (V t) x + skewArr (b t) V' x) S t := by
  simp only [skewArr_expand]
  have hi : ∀ i : Fin 3, HasDerivWithinAt (fun τ => b τ i x * (((N : ℝ) * (V τ (x + e N i) - V τ x) +
      (N : ℝ) * (V τ x - V τ (x - e N i))) / 2) +
      ((N : ℝ) * (b τ i (x + e N i) * V τ (x + e N i) - b τ i x * V τ x) +
        (N : ℝ) * (b τ i x * V τ x - b τ i (x - e N i) * V τ (x - e N i))) / 2)
      (b' i x * (((N : ℝ) * (V t (x + e N i) - V t x) +
        (N : ℝ) * (V t x - V t (x - e N i))) / 2) +
        b t i x * (((N : ℝ) * (V' (x + e N i) - V' x) + (N : ℝ) * (V' x - V' (x - e N i))) / 2) +
        ((N : ℝ) * ((b' i (x + e N i) * V t (x + e N i) + b t i (x + e N i) * V' (x + e N i)) -
          (b' i x * V t x + b t i x * V' x)) +
          (N : ℝ) * ((b' i x * V t x + b t i x * V' x) -
            (b' i (x - e N i) * V t (x - e N i) + b t i (x - e N i) * V' (x - e N i)))) / 2) S t := by
    intro i
    have h1 := (hb i x).mul (((((hV (x + e N i)).sub (hV x)).const_mul (N : ℝ)).add
      (((hV x).sub (hV (x - e N i))).const_mul (N : ℝ))).div_const 2)
    have h2 := (((((hb i (x + e N i)).mul (hV (x + e N i))).sub ((hb i x).mul (hV x))).const_mul
      (N : ℝ)).add ((((hb i x).mul (hV x)).sub ((hb i (x - e N i)).mul
        (hV (x - e N i)))).const_mul (N : ℝ))).div_const 2
    exact (h1.add h2).congr_deriv (by simp only [Pi.sub_apply, Pi.add_apply] <;> ring)
  refine (HasDerivWithinAt.fun_sum fun i _ => hi i).congr_deriv ?_
  rw [← sum_add_distrib]
  refine sum_congr rfl fun i _ => ?_
  ring

/-- A coefficient of the chart along a history `q` with velocity `Q'`. -/
theorem hasDerivWithinAt_coef {S : Set ℝ} {t : ℝ} {F : MetricRec → ℝ}
    {q : ℝ → Grid N → MetricRec} {Q' : Grid N → MetricRec}
    (hq : ∀ y μ ν, HasDerivWithinAt (fun τ => q τ y μ ν) (Q' y μ ν) S t) (y : Grid N)
    (hF : DifferentiableAt ℝ F (minkowski + q t y)) :
    HasDerivWithinAt (fun τ => F (minkowski + q τ y)) (fderiv ℝ F (minkowski + q t y) (Q' y)) S t := by
  have h : HasDerivWithinAt (fun τ => minkowski + q τ y) (Q' y) S t :=
    (hasDerivWithinAt_pi.2 fun μ => hasDerivWithinAt_pi.2 fun ν => hq y μ ν).const_add _
  exact hF.hasFDerivAt.comp_hasDerivWithinAt t h

/-- The site jet along a history. -/
theorem hasDerivWithinAt_jetArr {S : Set ℝ} {t : ℝ} {q v : ℝ → Grid N → MetricRec}
    {Q' V' : Grid N → MetricRec}
    (hq : ∀ y μ ν, HasDerivWithinAt (fun τ => q τ y μ ν) (Q' y μ ν) S t)
    (hv : ∀ y μ ν, HasDerivWithinAt (fun τ => v τ y μ ν) (V' y μ ν) S t) (x : Grid N) :
    HasDerivWithinAt (fun τ => jetArr (q τ) (v τ) x) (jetArr Q' V' x) S t := by
  have hq' : ∀ y, HasDerivWithinAt (fun τ => q τ y) (Q' y) S t := fun y =>
    hasDerivWithinAt_pi.2 fun μ => hasDerivWithinAt_pi.2 fun ν => hq y μ ν
  have hv' : ∀ y, HasDerivWithinAt (fun τ => v τ y) (V' y) S t := fun y =>
    hasDerivWithinAt_pi.2 fun μ => hasDerivWithinAt_pi.2 fun ν => hv y μ ν
  refine HasDerivWithinAt.prodMk (hq' x) (HasDerivWithinAt.prodMk (hv' x) ?_)
  refine hasDerivWithinAt_pi.2 fun i => ?_
  simp only [fwd]
  exact ((hq' _).sub (hq' x)).const_smul ((N : ℝ)⁻¹)⁻¹

/-- `τ ↦ (h² B Λ_h² q(τ))(x)` along a history. -/
theorem hasDerivWithinAt_bTerm {S : Set ℝ} {t : ℝ} (B : Upper → Upper → ℝ)
    {q : ℝ → Grid N → MetricRec} {Q' : Grid N → MetricRec}
    (hq : ∀ y μ ν, HasDerivWithinAt (fun τ => q τ y μ ν) (Q' y μ ν) S t) (x : Grid N)
    (μ ν : Fin 4) :
    HasDerivWithinAt (fun τ => bTerm B (q τ) x μ ν) (bTerm B Q' x μ ν) S t := by
  unfold bTerm
  refine HasDerivWithinAt.const_mul _ (HasDerivWithinAt.fun_sum fun l _ =>
    HasDerivWithinAt.const_mul _ ?_)
  have hc : HasDerivWithinAt (fun τ => comp (q τ) l.1.1 l.1.2) (comp Q' l.1.1 l.1.2) S t :=
    hasDerivWithinAt_pi.2 fun y => hq y l.1.1 l.1.2
  have := (LinearMap.toContinuousLinearMap ((lapRLin (N := N)).comp lapRLin)).hasFDerivAt
    |>.comp_hasDerivWithinAt t hc
  exact hasDerivWithinAt_pi.1 this x

theorem lawAccel_apply (B : Upper → Upper → ℝ) (q v : Grid N → MetricRec) (x : Grid N)
    (μ ν : Fin 4) :
    lawAccel B q v x μ ν = (aArr q x)⁻¹ * (divArr (cArr q) (comp q μ ν) x -
      skewArr (bArr q) (comp v μ ν) x + compensatorMap (jetArr q v x) μ ν - bTerm B q x μ ν) := by
  have h := accel_apply q v x μ ν
  simp only [lawAccel, lawForce, Pi.add_apply]
  rw [h]
  simp only [Garr, comp]
  ring

/-- **The third time derivative** `q_ttt` of a law-family history (the once-differentiated mass
row): `a q_ttt = Σ D_i⁻(ċ^{ij} D_j⁺ q + c^{ij} D_j⁺ v) - 𝖪_ḃ v - 𝖪_b q_tt + D𝖦[(v, q_tt, D⁺v)]
 - h² B Λ_h² v - ȧ q_tt`. -/
def jetDeriv (B : Upper → Upper → ℝ) (q v W : Grid N → MetricRec) (x : Grid N) (μ ν : Fin 4) : ℝ :=
  (aArr q x)⁻¹ * (divArr (cdot q v) (comp q μ ν) x + divArr (cArr q) (comp v μ ν) x -
    (skewArr (bdot q v) (comp v μ ν) x + skewArr (bArr q) (comp W μ ν) x) +
    fderiv ℝ (fun w : JetSpace => compensatorMap w μ ν) (jetArr q v x) (jetArr v W x) -
    bTerm B v x μ ν - adot q v x * lawAccel B q v x μ ν)

/-- The third derivative of a law-family history: if `q` has velocity `v` and `v` has velocity
`W` (all components, within `S`) at `t` and the chart is non-degenerate at the stencil, then
`τ ↦ V_{B,h}(q(τ), v(τ))` has derivative `jetDeriv` within `S`. -/
theorem hasDerivWithinAt_lawAccel {S : Set ℝ} {t : ℝ} (B : Upper → Upper → ℝ)
    {q v : ℝ → Grid N → MetricRec} {W : Grid N → MetricRec}
    (hq : ∀ y μ ν, HasDerivWithinAt (fun τ => q τ y μ ν) (v t y μ ν) S t)
    (hv : ∀ y μ ν, HasDerivWithinAt (fun τ => v τ y μ ν) (W y μ ν) S t)
    (hdet : ∀ y, (Matrix.of (minkowski + q t y)).det ≠ 0)
    (ha : ∀ y, aArr (q t) y ≠ 0) (x : Grid N) (μ ν : Fin 4) :
    HasDerivWithinAt (fun τ => lawAccel B (q τ) (v τ) x μ ν)
      (jetDeriv B (q t) (v t) W x μ ν) S t := by
  have hdA : ∀ y, DifferentiableAt ℝ harmA (minkowski + q t y) := fun y =>
    ((analyticAt_inv_entry _ (hdet y) 0 0).neg).differentiableAt
  have hdC : ∀ y i j, DifferentiableAt ℝ (harmC i j) (minkowski + q t y) := fun y i j =>
    (analyticAt_inv_entry _ (hdet y) i.succ j.succ).differentiableAt
  have hdB : ∀ y i, DifferentiableAt ℝ (harmB i) (minkowski + q t y) := fun y i =>
    ((analyticAt_inv_entry _ (hdet y) 0 i.succ).neg).differentiableAt
  have hA : ∀ y, HasDerivWithinAt (fun τ => aArr (q τ) y) (adot (q t) (v t) y) S t := fun y =>
    hasDerivWithinAt_coef hq y (hdA y)
  have hC : ∀ i j y, HasDerivWithinAt (fun τ => cArr (q τ) i j y) (cdot (q t) (v t) i j y) S t :=
    fun i j y => hasDerivWithinAt_coef hq y (hdC y i j)
  have hB : ∀ i y, HasDerivWithinAt (fun τ => bArr (q τ) i y) (bdot (q t) (v t) i y) S t :=
    fun i y => hasDerivWithinAt_coef hq y (hdB y i)
  have hD := hasDerivWithinAt_divArr (fun τ => cArr (q τ)) (cdot (q t) (v t))
    (fun τ => comp (q τ) μ ν) (comp (v t) μ ν) hC (fun y => hq y μ ν) x
  have hS := hasDerivWithinAt_skewArr (fun τ => bArr (q τ)) (bdot (q t) (v t))
    (fun τ => comp (v τ) μ ν) (comp W μ ν) hB (fun y => hv y μ ν) x
  have hJ := hasDerivWithinAt_jetArr hq hv x
  have hG : HasDerivWithinAt (fun τ => compensatorMap (jetArr (q τ) (v τ) x) μ ν)
      (fderiv ℝ (fun w : JetSpace => compensatorMap w μ ν) (jetArr (q t) (v t) x)
        (jetArr (v t) W x)) S t := by
    have hdiff : DifferentiableAt ℝ (fun w : JetSpace => compensatorMap w μ ν)
        (jetArr (q t) (v t) x) :=
      (analyticAt_compensatorMap_of_det μ ν _ (by simpa [jetArr] using hdet x)).differentiableAt
    exact hdiff.hasFDerivAt.comp_hasDerivWithinAt t hJ
  have hbT := hasDerivWithinAt_bTerm B hq x μ ν
  have hR := ((hD.sub hS).add hG).sub hbT
  have hinv := (hA x).inv (ha x)
  have hprod := hinv.mul hR
  have e : (fun τ => lawAccel B (q τ) (v τ) x μ ν) = fun τ => (aArr (q τ) x)⁻¹ *
      (divArr (cArr (q τ)) (comp (q τ) μ ν) x - skewArr (bArr (q τ)) (comp (v τ) μ ν) x +
        compensatorMap (jetArr (q τ) (v τ) x) μ ν - bTerm B (q τ) x μ ν) := by
    funext τ; exact lawAccel_apply B (q τ) (v τ) x μ ν
  rw [e]
  refine hprod.congr_deriv ?_
  unfold jetDeriv
  rw [lawAccel_apply]
  simp only [Pi.sub_apply, Pi.add_apply, Pi.inv_apply, Pi.mul_apply]
  have hax := ha x
  field_simp
  ring

/-! ### Bounds of the jets -/

theorem lawAccel_zero (q v : Grid N → MetricRec) :
    lawAccel (fun _ _ => 0) q v = harmonicWriterAcceleration q v := by
  funext x μ ν
  simp [lawAccel, lawForce, bTerm]

theorem isMark_zero : IsMark (1 / 48) (fun _ _ : Upper => (0 : ℝ)) :=
  ⟨fun _ _ => rfl, fun ξ η => by simp only [mul_zero, zero_mul, sum_const_zero, abs_zero]; positivity⟩

theorem Xnorm_le_sum (r : ℕ) (Q V : Grid N → MetricRec) :
    Xnorm r Q V ≤ ∑ κ : Upper, (PeriodicGridSobolev.sobNorm (r + 1) (cx (comp Q κ.1.1 κ.1.2)) +
      PeriodicGridSobolev.sobNorm r (cx (comp V κ.1.1 κ.1.2))) := by
  have h0 : 0 ≤ ∑ κ : Upper, (PeriodicGridSobolev.sobNorm (r + 1) (cx (comp Q κ.1.1 κ.1.2)) +
      PeriodicGridSobolev.sobNorm r (cx (comp V κ.1.1 κ.1.2))) :=
    sum_nonneg fun _ _ => add_nonneg (PeriodicGridSobolev.Moser.sobNorm_nonneg _ _)
      (PeriodicGridSobolev.Moser.sobNorm_nonneg _ _)
  unfold Xnorm
  rw [Real.sqrt_le_left h0]
  unfold Xsq
  calc ∑ κ : Upper, (PeriodicGridSobolev.sobSq (r + 1) (cx (comp Q κ.1.1 κ.1.2)) +
        PeriodicGridSobolev.sobSq r (cx (comp V κ.1.1 κ.1.2))) ≤
        ∑ κ : Upper, (PeriodicGridSobolev.sobNorm (r + 1) (cx (comp Q κ.1.1 κ.1.2)) +
          PeriodicGridSobolev.sobNorm r (cx (comp V κ.1.1 κ.1.2))) ^ 2 := by
        refine sum_le_sum fun κ _ => ?_
        rw [← PeriodicGridSobolev.sobNorm_sq, ← PeriodicGridSobolev.sobNorm_sq]
        have := PeriodicGridSobolev.Moser.sobNorm_nonneg (r + 1) (cx (comp Q κ.1.1 κ.1.2))
        have := PeriodicGridSobolev.Moser.sobNorm_nonneg r (cx (comp V κ.1.1 κ.1.2))
        nlinarith
    _ ≤ _ := Finset.sum_sq_le_sq_sum_of_nonneg fun κ _ =>
        add_nonneg (PeriodicGridSobolev.Moser.sobNorm_nonneg _ _)
          (PeriodicGridSobolev.Moser.sobNorm_nonneg _ _)

theorem Xnorm_vel_le (s : ℕ) (q v : Grid N → MetricRec) :
    Xnorm (s - 1) v 0 ≤ Xnorm s q v ∨ s = 0 := by
  rcases Nat.eq_zero_or_pos s with h | h
  · exact Or.inr h
  left
  refine Real.sqrt_le_sqrt ?_
  unfold Xsq
  refine sum_le_sum fun κ _ => ?_
  have e : cx (comp (0 : Grid N → MetricRec) κ.1.1 κ.1.2) = 0 := by funext x; simp [comp, cx]
  rw [e, show s - 1 + 1 = s by omega]
  have : PeriodicGridSobolev.sobSq (s - 1) (0 : PeriodicGridSobolev.Grid N → ℂ) = 0 := by
    simp [PeriodicGridSobolev.sobSq, PeriodicGridSobolev.gridNormSq]
  rw [this]
  have := PeriodicGridSobolev.sobSq_nonneg (s + 1) (cx (comp q κ.1.1 κ.1.2))
  linarith

/-- The law-family acceleration is bounded in `H^{s-1}_h` by `K ‖X‖_{X^s_h}` on the chart. -/
theorem lawAccel_bound (s : ℕ) (hs : 3 ≤ s) :
    ∃ δ > 0, ∃ K ≥ 0, ∀ (N : ℕ) [NeZero N] (B : Upper → Upper → ℝ) (q v : Grid N → MetricRec),
      IsMark (1 / 48) B → IsSymRec q → IsSymRec v → Xnorm s q v ≤ δ → ∀ κ : Upper,
      PeriodicGridSobolev.sobNorm (s - 1) (cx (comp (lawAccel B q v) κ.1.1 κ.1.2)) ≤
        K * Xnorm s q v := by
  obtain ⟨δA, hδA, KA, hKA, hacc⟩ := accel_bound s hs
  obtain ⟨δ1, hδ1, C1, hC1, hm1⟩ := moser_coefficients (s - 1) (by omega)
  set A1 := PeriodicGridSobolev.Moser.algConst (s - 1)
  have hA1 := PeriodicGridSobolev.Moser.algConst_pos (s - 1)
  refine ⟨min δA (min (δ1 / 16) (1 / (16 * (C1 + 1)))), by positivity, KA + (A1 + 1) * 12,
    by positivity, fun N _ B q v hB hq hv hX κ => ?_⟩
  set X := Xnorm s q v
  have hX0 : 0 ≤ X := Xnorm_nonneg _ _ _
  have hXs : 16 * (C1 + 1) * X ≤ 1 := by
    have := hX.trans ((min_le_right _ _).trans (min_le_right _ _))
    rw [le_div_iff₀ (by positivity)] at this; linarith
  have hcs : PeriodicGridSobolev.Moser.coordSum (s - 1) bM q ≤ 16 * X :=
    coordSum_bM_q_le s hq v (by omega)
  have hM1 := hm1 N q (hcs.trans (by linarith [hX.trans ((min_le_right _ _).trans
    (min_le_left _ _))]))
  have hainv : PeriodicGridSobolev.sobNorm (s - 1)
      (cx (fun x => (aArr q x)⁻¹) - fun _ => (1 : ℂ)) ≤ 1 := by
    refine hM1.2.1.trans ?_
    calc C1 * PeriodicGridSobolev.Moser.coordSum (s - 1) bM q ≤ C1 * (16 * X) :=
          mul_le_mul_of_nonneg_left hcs hC1
      _ ≤ 1 := by nlinarith
  have e : cx (comp (lawAccel B q v) κ.1.1 κ.1.2) =
      cx (comp (harmonicWriterAcceleration q v) κ.1.1 κ.1.2) -
        cx (fun x => (aArr q x)⁻¹) * cx (comp (bTerm B q) κ.1.1 κ.1.2) := by
    funext x; simp [comp, cx, lawAccel, lawForce, sub_eq_add_neg]
  rw [e]
  refine (PeriodicGridSobolev.Moser.sobNorm_sub_le _ _ _).trans ?_
  have h1 := hacc N q v hq hv (hX.trans (min_le_left _ _)) κ.1.1 κ.1.2
  have h2 := (sobNorm_coef_mul_le (s - 1) (by omega) _ (cx (comp (bTerm B q) κ.1.1 κ.1.2)) 1
    (by simp) hainv)
  have h3 := sobNorm_bTerm_le s (by omega) hB hq v κ
  have h4 : (A1 + 1) * PeriodicGridSobolev.sobNorm (s - 1) (cx (comp (bTerm B q) κ.1.1 κ.1.2)) ≤
      (A1 + 1) * (12 * X) :=
    mul_le_mul_of_nonneg_left (h3.trans (by nlinarith)) (by positivity)
  nlinarith

set_option maxHeartbeats 4000000 in
/-- **The third time derivative is bounded**: `‖q_ttt‖_{s-2,h} ≤ K ‖X‖_{X^s_h}` on the chart,
uniformly in the mesh and the mark (`s ≥ 4`). -/
theorem jetDeriv_bound (s : ℕ) (hs : 4 ≤ s) :
    ∃ δ > 0, ∃ K ≥ 0, ∀ (N : ℕ) [NeZero N] (B : Upper → Upper → ℝ) (q v : Grid N → MetricRec),
      IsMark (1 / 48) B → IsSymRec q → IsSymRec v → Xnorm s q v ≤ δ → ∀ κ : Upper,
      PeriodicGridSobolev.sobNorm (s - 2) (cx (fun x =>
        jetDeriv B q v (symRec (lawAccel B q v)) x κ.1.1 κ.1.2)) ≤ K * Xnorm s q v := by
  open PeriodicGridSobolev PeriodicGridSobolev.Moser PeriodicGridSobolev.CommutedRow in
  obtain ⟨δL, hδL, KL, hKL, hLa⟩ := lawAccel_bound s (by omega)
  obtain ⟨δr, hδr, Cr, hCr, hmr⟩ := moser_rate_coefficients (s - 1) (by omega)
  obtain ⟨δr2, hδr2, Cr2, hCr2, hmr2⟩ := moser_rate_coefficients (s - 2) (by omega)
  obtain ⟨δG, hδG, CG, hCG, hmG⟩ := moser_rate_compensator (s - 2) (by omega)
  obtain ⟨δ1, hδ1, C1, hC1, hm1⟩ := moser_coefficients (s - 1) (by omega)
  obtain ⟨δ2, hδ2, C2, hC2, hm2⟩ := moser_coefficients (s - 2) (by omega)
  set A1 := algConst (s - 1)
  set A2 := algConst (s - 2)
  have hA1 := algConst_pos (s - 1)
  have hA2 := algConst_pos (s - 2)
  set CC : ℝ := C1 + C2 + 1
  set Dj : ℝ := 80 + 1280 * (1 + KL)
  set δ : ℝ := min (min δL (min (δr / 32) (δr2 / 32))) (min (min (δG / Dj) (δ1 / 16))
    (min (δ2 / 16) (min 1 (1 / (16 * CC)))))
  have hδ : 0 < δ := by positivity
  set Kb : ℝ := 9 * A1 * (Cr * 32) + 9 * (A1 + 1) + 3 * (A2 + A1) * (Cr * 32) +
    3 * (A2 + A1) * KL + CG * Dj + 12 + A2 * (Cr2 * 32) * KL
  have hKb : 0 ≤ Kb := by positivity
  refine ⟨δ, hδ, (A2 + 1) * Kb, by positivity, fun N _ B q v hB hq hv hX κ => ?_⟩
  set X := Xnorm s q v
  have hX0 : 0 ≤ X := Xnorm_nonneg _ _ _
  have hδL' : δ ≤ δL := (min_le_left _ _).trans (min_le_left _ _)
  have hδr' : δ ≤ δr / 32 := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδr2' : δ ≤ δr2 / 32 :=
    (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hδG' : δ ≤ δG / Dj := (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hδ1' : δ ≤ δ1 / 16 := (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hδ2' : δ ≤ δ2 / 16 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδ1'' : δ ≤ 1 := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hδCC : δ ≤ 1 / (16 * CC) := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  have hX1 : X ≤ 1 := hX.trans hδ1''
  have hsmall : 16 * CC * X ≤ 1 := by
    have := hX.trans hδCC
    rw [le_div_iff₀ (by positivity)] at this; linarith
  have hC1X : C1 * (16 * X) ≤ 1 := by
    have : C1 ≤ CC := by simp only [CC]; linarith
    nlinarith
  have hC2X : C2 * (16 * X) ≤ 1 := by
    have : C2 ≤ CC := by simp only [CC]; linarith
    nlinarith
  -- coefficient bounds
  have hcs1 : coordSum (s - 1) bM q ≤ 16 * X := coordSum_bM_q_le s hq v (by omega)
  have hcs2 : coordSum (s - 2) bM q ≤ 16 * X := coordSum_bM_q_le s hq v (by omega)
  have hcv1 : coordSum (s - 1) bM v ≤ 16 * X := coordSum_bM_v_le s q hv (by omega)
  have hcv2 : coordSum (s - 2) bM v ≤ 16 * X := coordSum_bM_v_le s q hv (by omega)
  have hM1 := hm1 N q (hcs1.trans (by linarith [hX.trans hδ1']))
  have hM2 := hm2 N q (hcs2.trans (by linarith [hX.trans hδ2']))
  have hc1 : ∀ i j, sobNorm (s - 1) (cx (cArr q i j) -
      fun _ => ((if i = j then 1 else 0 : ℝ) : ℂ)) ≤ 1 := fun i j =>
    (hM1.2.2.1 i j).trans ((mul_le_mul_of_nonneg_left hcs1 hC1).trans hC1X)
  have hb1 : ∀ i, sobNorm (s - 1) (cx (bArr q i) - fun _ => (0 : ℂ)) ≤ 1 := fun i =>
    (hM1.2.2.2 i).trans ((mul_le_mul_of_nonneg_left hcs1 hC1).trans hC1X)
  have hb1' : ∀ i, sobNorm (s - 1) (cx (bArr q i)) ≤ 1 := fun i => by
    have e : (cx (bArr q i) - fun _ => (0 : ℂ)) = cx (bArr q i) := by funext x; simp
    have := hb1 i; rwa [e] at this
  have hb2' : ∀ i, sobNorm (s - 2) (cx (bArr q i)) ≤ 1 := fun i =>
    (sobNorm_mono (by omega) _).trans (hb1' i)
  have hainv : sobNorm (s - 2) (cx (fun x => (aArr q x)⁻¹) - fun _ => (1 : ℂ)) ≤ 1 :=
    hM2.2.1.trans ((mul_le_mul_of_nonneg_left hcs2 hC2).trans hC2X)
  -- rate bounds
  have hR1 := hmr N q v (by linarith [hX.trans hδr'])
  have hR2 := hmr2 N q v (by linarith [hX.trans hδr2'])
  have hcdot : ∀ i j, sobNorm (s - 1) (cx (cdot q v i j)) ≤ Cr * 32 * X := fun i j =>
    (hR1.2.1 i j).trans (by nlinarith)
  have hbdot1 : ∀ i, sobNorm (s - 1) (cx (bdot q v i)) ≤ Cr * 32 * X := fun i =>
    (hR1.2.2 i).trans (by nlinarith)
  have hbdot2 : ∀ i, sobNorm (s - 2) (cx (bdot q v i)) ≤ Cr * 32 * X := fun i =>
    (sobNorm_mono (by omega) _).trans (hbdot1 i)
  have hadot2 : sobNorm (s - 2) (cx (adot q v)) ≤ Cr2 * 32 * X :=
    hR2.1.trans (by nlinarith)
  -- the acceleration
  have hW1 : sobNorm (s - 1) (cx (comp (lawAccel B q v) κ.1.1 κ.1.2)) ≤ KL * X :=
    hLa N B q v hB hq hv (hX.trans hδL') κ
  have hW2 : sobNorm (s - 2) (cx (comp (lawAccel B q v) κ.1.1 κ.1.2)) ≤ KL * X :=
    (sobNorm_mono (by omega) _).trans hW1
  have hWsym := isSymRec_symRec (lawAccel B q v)
  have hcompW : comp (symRec (lawAccel B q v)) κ.1.1 κ.1.2 = comp (lawAccel B q v) κ.1.1 κ.1.2 :=
    comp_symRec _ κ
  -- the compensator differential
  have hjet : coordSum (s - 2) bJ (jetArr q v) ≤ 80 * X :=
    (coordSum_mono (by omega) bJ _).trans (coordSum_bJ_le s hq hv)
  have hjet' : coordSum (s - 2) bJ (jetArr v (symRec (lawAccel B q v))) ≤ 1280 * (1 + KL) * X := by
    refine (coordSum_bJ_le (s - 2) hv hWsym).trans ?_
    have h1 := Xnorm_le_sum (s - 2) v (symRec (lawAccel B q v))
    have h2 : ∀ κ' : Upper, sobNorm (s - 2 + 1) (cx (comp v κ'.1.1 κ'.1.2)) +
        sobNorm (s - 2) (cx (comp (symRec (lawAccel B q v)) κ'.1.1 κ'.1.2)) ≤ X + KL * X := by
      intro κ'
      rw [comp_symRec]
      refine add_le_add (sobNorm_v_le s q hv _ _ (by omega)) ?_
      exact (sobNorm_mono (by omega) _).trans (hLa N B q v hB hq hv (hX.trans hδL') κ')
    have h3 : ∑ κ' : Upper, (sobNorm (s - 2 + 1) (cx (comp v κ'.1.1 κ'.1.2)) +
        sobNorm (s - 2) (cx (comp (symRec (lawAccel B q v)) κ'.1.1 κ'.1.2))) ≤ 16 * (X + KL * X) := by
      calc _ ≤ ∑ _κ' : Upper, (X + KL * X) := sum_le_sum fun κ' _ => h2 κ'
        _ = (Fintype.card Upper : ℝ) * (X + KL * X) := by rw [sum_const, card_univ, nsmul_eq_mul]
        _ ≤ 16 * (X + KL * X) := by
            have hc : (Fintype.card Upper : ℝ) ≤ 16 := by
              have h1 : Fintype.card Upper ≤ Fintype.card (Fin 4 × Fin 4) :=
                Fintype.card_subtype_le _
              have h2 : Fintype.card (Fin 4 × Fin 4) = 16 := by simp
              exact_mod_cast h1.trans h2.le
            exact mul_le_mul_of_nonneg_right hc (by positivity)
    have h4 := Xnorm_nonneg (s - 2) v (symRec (lawAccel B q v))
    linarith
  have hGd := hmG N (jetArr q v) (jetArr v (symRec (lawAccel B q v)))
    (by
      have := hX.trans hδG'
      rw [le_div_iff₀ (by positivity)] at this
      nlinarith) κ.1.1 κ.1.2
  have hGd' : sobNorm (s - 2) (cx (fun x => fderiv ℝ (fun u : JetSpace => compensatorMap u κ.1.1 κ.1.2)
      (jetArr q v x) (jetArr v (symRec (lawAccel B q v)) x))) ≤ CG * Dj * X := by
    refine hGd.trans ?_
    calc CG * (coordSum (s - 2) bJ (jetArr q v) +
          coordSum (s - 2) bJ (jetArr v (symRec (lawAccel B q v)))) ≤
          CG * (80 * X + 1280 * (1 + KL) * X) := by gcongr
      _ = CG * Dj * X := by simp only [Dj]; ring
  -- the pieces
  have P1 : sobNorm (s - 2) (∑ i, ∑ j, Dm i (cx (cdot q v i j) * Dp j (cx (comp q κ.1.1 κ.1.2)))) ≤
      9 * A1 * (Cr * 32) * X := by
    have hij : ∀ i j, sobNorm (s - 2) (Dm i (cx (cdot q v i j) * Dp j (cx (comp q κ.1.1 κ.1.2)))) ≤
        A1 * (Cr * 32) * X := by
      intro i j
      have h0 := sobNorm_Dm_le (s - 2) i (cx (cdot q v i j) * Dp j (cx (comp q κ.1.1 κ.1.2)))
      rw [show s - 2 + 1 = s - 1 by omega] at h0
      refine h0.trans ((sobNorm_mul_le (s - 1) (by omega) _ _).trans ?_)
      have hq1 : sobNorm (s - 1) (Dp j (cx (comp q κ.1.1 κ.1.2))) ≤ 1 := by
        have := sobNorm_Dp_le (s - 1) j (cx (comp q κ.1.1 κ.1.2))
        rw [show s - 1 + 1 = s by omega] at this
        exact this.trans ((sobNorm_q_le s hq v _ _ (by omega)).trans hX1)
      calc A1 * sobNorm (s - 1) (cx (cdot q v i j)) * sobNorm (s - 1) (Dp j (cx (comp q κ.1.1 κ.1.2)))
          ≤ A1 * (Cr * 32 * X) * 1 := by
            gcongr
            · exact sobNorm_nonneg _ _
            · exact hcdot i j
        _ = A1 * (Cr * 32) * X := by ring
    calc _ ≤ ∑ i, sobNorm (s - 2) (∑ j, Dm i (cx (cdot q v i j) * Dp j (cx (comp q κ.1.1 κ.1.2)))) :=
          sobNorm_sum_le _ _ _
      _ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, A1 * (Cr * 32) * X :=
          sum_le_sum fun i _ => (sobNorm_sum_le _ _ _).trans (sum_le_sum fun j _ => hij i j)
      _ = 9 * A1 * (Cr * 32) * X := by simp; ring
  have P2 : sobNorm (s - 2) (∑ i, ∑ j, Dm i (cx (cArr q i j) * Dp j (cx (comp v κ.1.1 κ.1.2)))) ≤
      9 * (A1 + 1) * X := by
    have hij : ∀ i j, sobNorm (s - 2) (Dm i (cx (cArr q i j) * Dp j (cx (comp v κ.1.1 κ.1.2)))) ≤
        (A1 + 1) * X := by
      intro i j
      have h0 := sobNorm_Dm_le (s - 2) i (cx (cArr q i j) * Dp j (cx (comp v κ.1.1 κ.1.2)))
      rw [show s - 2 + 1 = s - 1 by omega] at h0
      refine h0.trans ((sobNorm_coef_mul_le (s - 1) (by omega) _ _ _
        (by split_ifs <;> simp) (hc1 i j)).trans ?_)
      have hv1 : sobNorm (s - 1) (Dp j (cx (comp v κ.1.1 κ.1.2))) ≤ X := by
        have := sobNorm_Dp_le (s - 1) j (cx (comp v κ.1.1 κ.1.2))
        rw [show s - 1 + 1 = s by omega] at this
        exact this.trans (sobNorm_v_le s q hv _ _ le_rfl)
      exact mul_le_mul_of_nonneg_left hv1 (by positivity)
    calc _ ≤ ∑ i, sobNorm (s - 2) (∑ j, Dm i (cx (cArr q i j) * Dp j (cx (comp v κ.1.1 κ.1.2)))) :=
          sobNorm_sum_le _ _ _
      _ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, (A1 + 1) * X :=
          sum_le_sum fun i _ => (sobNorm_sum_le _ _ _).trans (sum_le_sum fun j _ => hij i j)
      _ = 9 * (A1 + 1) * X := by simp; ring
  have hskew : ∀ (bb : Fin 3 → PeriodicGridSobolev.Grid N → ℂ) (V : PeriodicGridSobolev.Grid N → ℂ)
      (Mb Mv : ℝ), (∀ i, sobNorm (s - 1) (bb i) ≤ Mb) → sobNorm (s - 1) V ≤ Mv →
      sobNorm (s - 2) (∑ i, (bb i * D0 i V + D0 i (bb i * V))) ≤ 3 * (A2 + A1) * (Mb * Mv) := by
    intro bb V Mb Mv hbb hV
    have hi : ∀ i, sobNorm (s - 2) (bb i * D0 i V + D0 i (bb i * V)) ≤ (A2 + A1) * (Mb * Mv) := by
      intro i
      refine (sobNorm_add_le _ _ _).trans ?_
      have hMb : 0 ≤ Mb := (sobNorm_nonneg _ _).trans (hbb i)
      have h1 : sobNorm (s - 2) (bb i * D0 i V) ≤ A2 * (Mb * Mv) := by
        refine (sobNorm_mul_le (s - 2) (by omega) _ _).trans ?_
        have hb2 : sobNorm (s - 2) (bb i) ≤ Mb := (sobNorm_mono (by omega) _).trans (hbb i)
        have hd : sobNorm (s - 2) (D0 i V) ≤ Mv := by
          have := sobNorm_D0_le (s - 2) i V
          rw [show s - 2 + 1 = s - 1 by omega] at this
          exact this.trans hV
        calc A2 * sobNorm (s - 2) (bb i) * sobNorm (s - 2) (D0 i V) ≤ A2 * Mb * Mv :=
              mul_le_mul (mul_le_mul_of_nonneg_left hb2 hA2.le) hd (sobNorm_nonneg _ _)
                (mul_nonneg hA2.le hMb)
          _ = A2 * (Mb * Mv) := by ring
      have h2 : sobNorm (s - 2) (D0 i (bb i * V)) ≤ A1 * (Mb * Mv) := by
        have := sobNorm_D0_le (s - 2) i (bb i * V)
        rw [show s - 2 + 1 = s - 1 by omega] at this
        refine this.trans ((sobNorm_mul_le (s - 1) (by omega) _ _).trans ?_)
        calc A1 * sobNorm (s - 1) (bb i) * sobNorm (s - 1) V ≤ A1 * Mb * Mv :=
              mul_le_mul (mul_le_mul_of_nonneg_left (hbb i) hA1.le) hV (sobNorm_nonneg _ _)
                (mul_nonneg hA1.le hMb)
          _ = A1 * (Mb * Mv) := by ring
      linarith
    calc _ ≤ ∑ i, sobNorm (s - 2) (bb i * D0 i V + D0 i (bb i * V)) := sobNorm_sum_le _ _ _
      _ ≤ ∑ _i : Fin 3, (A2 + A1) * (Mb * Mv) := sum_le_sum fun i _ => hi i
      _ = 3 * (A2 + A1) * (Mb * Mv) := by simp; ring
  have P3 := hskew (fun i => cx (bdot q v i)) (cx (comp v κ.1.1 κ.1.2)) (Cr * 32 * X) X hbdot1
    (sobNorm_v_le s q hv _ _ (by omega))
  have P4 := hskew (fun i => cx (bArr q i)) (cx (comp (lawAccel B q v) κ.1.1 κ.1.2)) 1 (KL * X)
    hb1' hW1
  have P6 : sobNorm (s - 2) (cx (comp (bTerm B v) κ.1.1 κ.1.2)) ≤ 12 * X := by
    have h := sobNorm_bTerm_le (s - 1) (by omega) hB hv 0 κ
    rw [show s - 1 - 1 = s - 2 by omega] at h
    have hXv := Xnorm_vel_le s q v
    rcases hXv with hXv | hXv
    · refine h.trans ?_
      have := Xnorm_nonneg (s - 1) v 0
      nlinarith
    · omega
  have hXX : X * X ≤ X := by nlinarith
  have P7 : sobNorm (s - 2) (cx (adot q v) * cx (comp (lawAccel B q v) κ.1.1 κ.1.2)) ≤
      A2 * (Cr2 * 32) * KL * X := by
    refine (sobNorm_mul_le (s - 2) (by omega) _ _).trans ?_
    have h0 : 0 ≤ A2 * (Cr2 * 32) * KL := by positivity
    calc A2 * sobNorm (s - 2) (cx (adot q v)) *
          sobNorm (s - 2) (cx (comp (lawAccel B q v) κ.1.1 κ.1.2)) ≤
          A2 * (Cr2 * 32 * X) * (KL * X) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hadot2 hA2.le) hW2 (sobNorm_nonneg _ _)
            (by positivity)
      _ = A2 * (Cr2 * 32) * KL * (X * X) := by ring
      _ ≤ A2 * (Cr2 * 32) * KL * X := mul_le_mul_of_nonneg_left hXX h0
  -- assemble
  have e1 : (fun x => jetDeriv B q v (symRec (lawAccel B q v)) x κ.1.1 κ.1.2) = fun x =>
      (aArr q x)⁻¹ * ((divArr (cdot q v) (comp q κ.1.1 κ.1.2) +
        divArr (cArr q) (comp v κ.1.1 κ.1.2) -
        (skewArr (bdot q v) (comp v κ.1.1 κ.1.2) +
          skewArr (bArr q) (comp (lawAccel B q v) κ.1.1 κ.1.2)) +
        (fun x => fderiv ℝ (fun u : JetSpace => compensatorMap u κ.1.1 κ.1.2) (jetArr q v x)
          (jetArr v (symRec (lawAccel B q v)) x)) -
        comp (bTerm B v) κ.1.1 κ.1.2 -
        fun x => adot q v x * comp (lawAccel B q v) κ.1.1 κ.1.2 x) x) := by
    funext x
    simp only [jetDeriv]
    rw [hcompW]
    simp only [Pi.add_apply, Pi.sub_apply, comp]
  rw [e1]
  simp only [cx_fun_mul, cx_add, cx_sub, cx_divArr, cx_skewArr]
  have tri : ∀ A1' A2' A3' A4' A5' A6' A7' : PeriodicGridSobolev.Grid N → ℂ,
      sobNorm (s - 2) (A1' + A2' - (A3' + A4') + A5' - A6' - A7') ≤
        sobNorm (s - 2) A1' + sobNorm (s - 2) A2' + sobNorm (s - 2) A3' + sobNorm (s - 2) A4' +
          sobNorm (s - 2) A5' + sobNorm (s - 2) A6' + sobNorm (s - 2) A7' := by
    intro A1' A2' A3' A4' A5' A6' A7'
    have h1 := sobNorm_sub_le (s - 2) (A1' + A2' - (A3' + A4') + A5' - A6') A7'
    have h2 := sobNorm_sub_le (s - 2) (A1' + A2' - (A3' + A4') + A5') A6'
    have h3 := sobNorm_add_le (s - 2) (A1' + A2' - (A3' + A4')) A5'
    have h4 := sobNorm_sub_le (s - 2) (A1' + A2') (A3' + A4')
    have h5 := sobNorm_add_le (s - 2) A1' A2'
    have h6 := sobNorm_add_le (s - 2) A3' A4'
    linarith
  refine (sobNorm_coef_mul_le (s - 2) (by omega) _ _ 1 (by simp) hainv).trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ((tri _ _ _ _ _ _ _).trans ?_) (by positivity)
  have h3 : 3 * (A2 + A1) * (Cr * 32 * X * X) ≤ 3 * (A2 + A1) * (Cr * 32) * X := by
    have : 3 * (A2 + A1) * (Cr * 32 * X * X) = 3 * (A2 + A1) * (Cr * 32) * (X * X) := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hXX (by positivity)
  have e2 : Kb * X = 9 * A1 * (Cr * 32) * X + 9 * (A1 + 1) * X + 3 * (A2 + A1) * (Cr * 32) * X +
      3 * (A2 + A1) * (1 * (KL * X)) + CG * Dj * X + 12 * X + A2 * (Cr2 * 32) * KL * X := by
    simp only [Kb]; ring
  linarith [P1, P2, P3, P4, hGd', P6, P7]

/-! ### The time-jet lemma -/

/-- **`lem:supp-open-time-jets`** (uniform physical time jets).  For `s ≥ 4` (the manuscript
takes `s ≥ 11`) there are a top-ball radius `δ > 0` and `C ≥ 0`, independent of the mesh and
uniform over all marks `B = Bᵀ`, `‖B‖_op ≤ 1/48` (the open writer is `B = 0`, `lawAccel_zero`),
such that every solution of the law-family writer on `[0, T]` staying in the top ball
`‖X‖_{X^s_h} ≤ ε ≤ δ` satisfies, at every `t ∈ [0, T]` and for each of the ten components:
* `q_ttt` exists: `τ ↦ q_tt(τ) = V_{B,h}(q(τ), v(τ))` is differentiable within `[0, T]` at `t`
  with derivative `jetDeriv` (the once-differentiated mass row; `B` is constant in time);
* `‖q‖_{s+1,h} + ‖q_t‖_{s,h} + ‖q_tt‖_{s-1,h} + ‖q_ttt‖_{s-2,h} ≤ C ε`
  (`eq:supp-open-time-jet-bound`). -/
theorem law_time_jets (s : ℕ) (hs : 4 ≤ s) :
    ∃ δ > 0, ∃ C ≥ 0, ∀ (N : ℕ) [NeZero N] (B : Upper → Upper → ℝ) (T ε : ℝ)
      (q v : ℝ → Grid N → MetricRec), IsMark (1 / 48) B → ε ≤ δ →
      IsAccSolution (lawAccel B) T q v → (∀ t ∈ Icc 0 T, Xnorm s (q t) (v t) ≤ ε) →
      ∀ t ∈ Icc 0 T, ∀ κ : Upper,
        (∀ x, HasDerivWithinAt (fun τ => lawAccel B (q τ) (v τ) x κ.1.1 κ.1.2)
          (jetDeriv B (q t) (v t) (symRec (lawAccel B (q t) (v t))) x κ.1.1 κ.1.2) (Icc 0 T) t) ∧
        PeriodicGridSobolev.sobNorm (s + 1) (cx (comp (q t) κ.1.1 κ.1.2)) +
          PeriodicGridSobolev.sobNorm s (cx (comp (v t) κ.1.1 κ.1.2)) +
          PeriodicGridSobolev.sobNorm (s - 1) (cx (comp (lawAccel B (q t) (v t)) κ.1.1 κ.1.2)) +
          PeriodicGridSobolev.sobNorm (s - 2) (cx (fun x =>
            jetDeriv B (q t) (v t) (symRec (lawAccel B (q t) (v t))) x κ.1.1 κ.1.2)) ≤ C * ε := by
  obtain ⟨δL, hδL, KL, hKL, hLa⟩ := lawAccel_bound s (by omega)
  obtain ⟨δJ, hδJ, KJ, hKJ, hJ⟩ := jetDeriv_bound s hs
  obtain ⟨r₀, hr₀, hchart⟩ := exists_det_chart
  have hS := supConst_nonneg
  set δ : ℝ := min (min δL δJ) (r₀ / (2 * (supConst + 1)))
  refine ⟨δ, by positivity, 2 + KL + KJ, by positivity,
    fun N _ B T ε q v hB hε hsol hX t ht κ => ?_⟩
  obtain ⟨hqs, hvs, hq, hv⟩ := hsol t ht
  have hXt := hX t ht
  have hXδ : Xnorm s (q t) (v t) ≤ δ := hXt.trans hε
  have hX0 := Xnorm_nonneg s (q t) (v t)
  refine ⟨fun x => ?_, ?_⟩
  · -- the chart at time `t`
    have hqy : ∀ y, ‖(minkowski + q t y) - minkowski‖ < r₀ := by
      intro y
      rw [add_sub_cancel_left]
      have h1 := norm_q_le s (by omega) hqs (v t) y
      have h2 : supConst * Xnorm s (q t) (v t) ≤ supConst * (r₀ / (2 * (supConst + 1))) :=
        mul_le_mul_of_nonneg_left (hXδ.trans (min_le_right _ _)) hS
      have h3 : supConst * (r₀ / (2 * (supConst + 1))) < r₀ := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith
      linarith
    have hqd : ∀ y μ ν, HasDerivWithinAt (fun τ => q τ y μ ν) (v t y μ ν) (Icc 0 T) t :=
      fun y μ ν => (hasDerivAt_pi.1 (hasDerivAt_pi.1 (hq y) μ) ν).hasDerivWithinAt
    have hvd : ∀ y μ ν, HasDerivWithinAt (fun τ => v τ y μ ν)
        (symRec (lawAccel B (q t) (v t)) y μ ν) (Icc 0 T) t := by
      intro y μ ν
      refine (hv y (upperOf μ ν)).hasDerivWithinAt.congr (fun σ hσ => ?_) ?_
      · exact (congrFun (comp_upperOf (hsol σ hσ).2.1 μ ν) y).symm
      · exact (congrFun (comp_upperOf hvs μ ν) y).symm
    exact hasDerivWithinAt_lawAccel B hqd hvd (fun y => (hchart _ (hqy y)).1)
      (fun y => (hchart _ (hqy y)).2) x κ.1.1 κ.1.2
  · have h1 := sobNorm_q_le s hqs (v t) κ.1.1 κ.1.2 le_rfl
    have h2 := sobNorm_v_le s (q t) hvs κ.1.1 κ.1.2 le_rfl
    have h3 := hLa N B (q t) (v t) hB hqs hvs (hXδ.trans ((min_le_left _ _).trans
      (min_le_left _ _))) κ
    have h4 := hJ N B (q t) (v t) hB hqs hvs (hXδ.trans ((min_le_left _ _).trans
      (min_le_right _ _))) κ
    have : (2 + KL + KJ) * Xnorm s (q t) (v t) ≤ (2 + KL + KJ) * ε :=
      mul_le_mul_of_nonneg_left hXt (by positivity)
    nlinarith

theorem lawAccel_zero_state (B : Upper → Upper → ℝ) :
    lawAccel B (0 : Grid N → MetricRec) 0 = 0 := by
  have hb : bTerm B (0 : Grid N → MetricRec) = 0 := by
    have hl : lapR (lapR (0 : Grid N → ℝ)) = 0 := by
      rw [show (0 : Grid N → ℝ) = (0 : ℝ) • (0 : Grid N → ℝ) by simp, lapR_smul, lapR_smul]
      simp
    funext x μ ν
    have e : ∀ l : Upper, comp (0 : Grid N → MetricRec) l.1.1 l.1.2 = 0 := fun l => by
      funext y; rfl
    simp [bTerm, e, hl]
  funext x μ ν
  simp only [lawAccel, lawForce, hb, Pi.add_apply, Pi.zero_apply, mul_zero, neg_zero, add_zero]
  rw [harmonicWriterAcceleration_zero]
  rfl

/-- Non-vacuity of `law_time_jets`: the flat history is a solution of every member of the law
family on every interval and stays in every top ball. -/
example (s : ℕ) (hs : 4 ≤ s) : True := by
  obtain ⟨δ, hδ, C, hC, h⟩ := law_time_jets s hs
  have hsol : IsAccSolution (lawAccel (fun _ _ => 0)) 1 (fun _ => (0 : Grid 5 → MetricRec))
      (fun _ => 0) := by
    intro t _
    refine ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun x => hasDerivAt_const _ _, fun x κ => ?_⟩
    rw [lawAccel_zero_state]
    exact hasDerivAt_const _ _
  have hX : ∀ t ∈ Icc (0 : ℝ) 1, Xnorm s ((fun _ => (0 : Grid 5 → MetricRec)) t)
      ((fun _ => (0 : Grid 5 → MetricRec)) t) ≤ 0 := by
    intro t _
    have : Xsq s (0 : Grid 5 → MetricRec) 0 = 0 := by
      unfold Xsq
      refine sum_eq_zero fun κ _ => ?_
      have e : cx (comp (0 : Grid 5 → MetricRec) κ.1.1 κ.1.2) = 0 := by funext x; simp [comp, cx]
      rw [e]
      simp [PeriodicGridSobolev.sobSq, PeriodicGridSobolev.gridNormSq]
    simp only [Xnorm, this, Real.sqrt_zero, le_refl]
  have := h 5 _ 1 0 _ _ isMark_zero hδ.le hsol hX 0 ⟨le_rfl, zero_le_one⟩
  trivial
end

end RenewalGeometry.OpenWriterLifespan
