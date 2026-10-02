/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.OpenWriterReducedResidual
import RenewalGeometry.Gravity.OpenWriterTimeJets
import RenewalGeometry.DiscreteAnalysis.PeriodicGridTimeDifferentiatedConsistency

/-!
# Time-differentiated consistency of the complete reduced residual
  (`lem:supp-open-reduced-consistency`, both halves of `eq:supp-open-reduced-rate`, central and
  `B`-writer; emergent-spacetime manuscript)

The manuscript proves `‖∂ₜr_h‖_{H^{s-3}} ≤ C h ε` by "differentiating the flux, transport and
composition decompositions once in physical time".  This file carries that out.

Infrastructure:

* `coef_mul_family_gen`, `rate_family_gen`, `rate_mul_family`: continuum multiplier bounds for
  analytic coefficients `A(c + Q)` and for their rates `DA(c + Q)[Q']` (Moser on a small `H^r`
  ball; the rates are linear in `Q'`, so no smallness of `Q'` is needed);
* `hasDerivWithinAt_coef_mul`, `hasDerivWithinAt_rate_mul`, `prodT`, `prodDT`,
  `hasDerivWithinAt_prodD`, `isLineDeriv_prodT`: the chain rule for a coefficient product
  `A(η + Q) G` and for its spatial derivative along a path, and the commutation of the time and
  space derivatives (symmetry of the second derivative of the analytic coefficient);
* `rowDeriv`, `hasDerivWithinAt_normalRow`, `rowDeriv_sn_le`: the linearized harmonic normal row,
  the chain rule for the normal row along a path of jets, and its `H^r` bound;
* `hasDerivWithinAt_reField`, `hasDerivWithinAt_interpRec'`, `hasDerivWithinAt_interpD'`,
  `hasDerivWithinAt_interpDD'`: interpolation commutes with one-sided time derivatives;
* `errRow`, `row_identity_interp`, `errDeriv`, `hasDerivWithinAt_errRow`: the consistency error of
  the interpolant jet (`sampled_row_identity`) and its derivative along a path of records;
* `errDeriv_bound`: the differentiated consistency error is `O(h)` in `H^{s-3}_h` (flux,
  interpolation, transport and compensator terms; `prodT_fields`, `moser_lipschitz_compRate`);
* `sn_le_of_sample` (aliasing) and `interp_rowDeriv_small`: the linearized row of the interpolant
  jet in the direction of the writer flow is `O(h)` in `H^{s-3}` (static, uniformly in marks
  `‖B‖_op ≤ 1/48`; the sampled identity is differentiated along the straight path
  `(q + τ v, v + τ q_tt)`);
* `interp_row_small_law`: the undifferentiated rows of the `B`-writer interpolant.

Main results:

* `interp_reduced_residual_deriv_law`: along a `B`-writer solution in the top ball, the reduced
  residual `r_h = G(g_h) - 𝓗(g_h, c(g_h))` of the interpolant jet has a time derivative within
  `[0, T]` at every point and `‖∂ₜr_{h,ab}‖_{H^{s-3}} ≤ C h ε` (trace reversal and its time
  derivative are uniformly bounded multipliers);
* `supp_open_reduced_consistency_law`, `supp_open_reduced_consistency`
  (**`lem:supp-open-reduced-consistency`**): `‖r_h‖_{H^{s-2}} + ‖∂ₜr_h‖_{H^{s-3}} ≤ C h ε` at every
  time, for the B-writer uniformly on the closed mark ball `IsMark (1/48) B` and for the central
  writer (`B = 0`); `s ≥ 5` (the manuscript takes `s ≥ 11`).
-/

open Finset Filter Topology UnitAddTorus
open scoped BigOperators Real

namespace RenewalGeometry.OpenWriterReducedResidualDeriv

open TorusSobolevTransfer OpenWriterLifespan OpenWriterEnergyEstimate OpenWriterChart
  OpenWriterEnergy OpenWriterContinuum HarmonicGaugePropagation HarmonicDefect
  PeriodicGridSobolev.Composition OpenWriterGridBridge RootParityConnector HarmonicWriter
  OpenWriterLimitRegularity OpenWriterReducedResidual

noncomputable section

set_option linter.unusedSectionVars false

/-! ### Multiplier bounds for analytic coefficients and their rates -/

section Multipliers

variable {E ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι] [DecidableEq ι]
  [Fintype κ]

/-- **Continuum coefficient products, general chart** (uniform over a finite family of
coefficients analytic at `c`): on a small `H^r` ball of `Q`, `A_k(c + Q) G ∈ H^r` with
`‖A_k(c + Q) G‖_{H^r} ≤ K ‖G‖_{H^r}`. -/
theorem coef_mul_family_gen (r : ℕ) (hr : 2 ≤ r) (b : Module.Basis ι ℝ E) (c : E)
    (A : κ → E → ℝ) (hA : ∀ k, AnalyticAt ℝ (A k) c) :
    ∃ δ > 0, ∃ K ≥ 0, ∀ (k : κ) (Q : C(T3, E)), (∀ j, MemH r ⇑(ccoord b Q j)) →
      ccoordSum r b Q ≤ δ → ∀ G : CT, MemH r ⇑G →
      ∃ P : CT, (∀ y, P y = ((A k (c + Q y) : ℝ) : ℂ) * G y) ∧ MemH r ⇑P ∧
        sn r ⇑P ≤ K * sn r ⇑G := by
  set P : κ → ℝ → ℝ → Prop := fun k δ K => ∀ (Q : C(T3, E)),
      (∀ j, MemH r ⇑(ccoord b Q j)) → ccoordSum r b Q ≤ δ → ∀ G : CT, MemH r ⇑G →
      ∃ P : CT, (∀ y, P y = ((A k (c + Q y) : ℝ) : ℂ) * G y) ∧ MemH r ⇑P ∧
        sn r ⇑P ≤ K * sn r ⇑G with hPdef
  have hmono : ∀ k δ δ' K K', 0 < δ' → δ' ≤ δ → K ≤ K' → P k δ K → P k δ' K' := by
    intro k δ δ' K K' _ hδ' hK' hP Q hQ hQδ G hG
    obtain ⟨P, h1, h2, h3⟩ := hP Q hQ (hQδ.trans hδ') G hG
    exact ⟨P, h1, h2, h3.trans (mul_le_mul_of_nonneg_right hK' (sn_nonneg _ _))⟩
  have hex : ∀ k, ∃ δ > 0, ∃ K ≥ 0, P k δ K := by
    intro k
    obtain ⟨p, R, hp⟩ := hA k
    obtain ⟨δ, hδ, C, hC, hm⟩ := cont_moser r hr b hp
    obtain ⟨Km, hKm, hmul⟩ := memH_mul r hr
    refine ⟨δ, hδ, ‖A k c‖ + Km * (C * δ), by positivity, fun Q hQ hQδ G hG => ?_⟩
    obtain ⟨-, F, hF, hFm, hFs⟩ := hm Q hQ hQδ
    obtain ⟨hFG, hFGs⟩ := hmul F G hFm hG
    refine ⟨((A k c : ℝ) : ℂ) • G + F * G, fun y => ?_, memH_add (memH_smul _ hG) hFG, ?_⟩
    · simp only [ContinuousMap.add_apply, ContinuousMap.smul_apply, ContinuousMap.mul_apply,
        hF y, smul_eq_mul]
      push_cast; ring
    · refine (sn_add_le' (memH_smul _ hG) hFG).trans ?_
      rw [sn_smul, Complex.norm_real]
      have hSn := sn_nonneg r ⇑G
      have h1 : sn r ⇑F ≤ C * δ :=
        hFs.trans (mul_le_mul_of_nonneg_left hQδ hC)
      have h2 : Km * sn r ⇑F * sn r ⇑G ≤ Km * (C * δ) * sn r ⇑G := by gcongr
      nlinarith
  obtain ⟨δ, hδ, K, hK, h⟩ := uniformize P hmono hex
  exact ⟨δ, hδ, K, hK, h⟩

/-- A continuous linear functional in the coordinates of a basis. -/
theorem clm_apply_eq_sum_repr (b : Module.Basis ι ℝ E) (L : E →L[ℝ] ℝ) (z : E) :
    L z = ∑ j, b.repr z j * L (b j) := by
  conv_lhs => rw [← b.sum_repr z]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]

/-- **Continuum rate bounds, general chart**: for a finite family of coefficients analytic at
`c`, on a small `H^r` ball of `Q` the rate `DA_k(c + Q)[Q']` lies in `H^r` with
`‖DA_k(c + Q)[Q']‖_{H^r} ≤ K Σ_j ‖Q'_j‖_{H^r}` (linear in `Q'`, no smallness of `Q'`). -/
theorem rate_family_gen [CompleteSpace E] (r : ℕ) (hr : 2 ≤ r) (b : Module.Basis ι ℝ E) (c : E)
    (A : κ → E → ℝ) (hA : ∀ k, AnalyticAt ℝ (A k) c) :
    ∃ δ > 0, ∃ K ≥ 0, ∀ (k : κ) (Q : C(T3, E)), (∀ j, MemH r ⇑(ccoord b Q j)) →
      ccoordSum r b Q ≤ δ → ∀ Q' : C(T3, E), (∀ j, MemH r ⇑(ccoord b Q' j)) →
      ∃ P : CT, (∀ y, P y = ((fderiv ℝ (A k) (c + Q y) (Q' y) : ℝ) : ℂ)) ∧ MemH r ⇑P ∧
        sn r ⇑P ≤ K * ccoordSum r b Q' := by
  have hA2 : ∀ km : κ × ι, AnalyticAt ℝ (fun g => fderiv ℝ (A km.1) g (b km.2)) c := fun km =>
    ((ContinuousLinearMap.apply ℝ ℝ (b km.2)).analyticAt _).comp (hA km.1).fderiv
  obtain ⟨δ, hδ, K, hK, hmul⟩ := coef_mul_family_gen r hr b c
    (fun km : κ × ι => fun g => fderiv ℝ (A km.1) g (b km.2)) hA2
  refine ⟨δ, hδ, K, hK, fun k Q hQ hQδ Q' hQ' => ?_⟩
  have hP := fun j => hmul (k, j) Q hQ hQδ (ccoord b Q' j) (hQ' j)
  choose P hPy hPm hPs using hP
  have hS := sn_sum_le' univ hPm
  refine ⟨∑ j, P j, fun y => ?_, hS.1, hS.2.trans ?_⟩
  · simp only [ContinuousMap.coe_sum, Finset.sum_apply, hPy, ccoord_apply]
    rw [clm_apply_eq_sum_repr b (fderiv ℝ (A k) (c + Q y)) (Q' y)]
    push_cast
    exact sum_congr rfl fun j _ => by ring
  · unfold ccoordSum
    rw [mul_sum]
    exact sum_le_sum fun j _ => hPs j

/-- **Rate products**: `‖DA_k(c + Q)[Q'] G‖_{H^r} ≤ K (Σ_j ‖Q'_j‖_{H^r}) ‖G‖_{H^r}`. -/
theorem rate_mul_family [CompleteSpace E] (r : ℕ) (hr : 2 ≤ r) (b : Module.Basis ι ℝ E) (c : E)
    (A : κ → E → ℝ) (hA : ∀ k, AnalyticAt ℝ (A k) c) :
    ∃ δ > 0, ∃ K ≥ 0, ∀ (k : κ) (Q : C(T3, E)), (∀ j, MemH r ⇑(ccoord b Q j)) →
      ccoordSum r b Q ≤ δ → ∀ Q' : C(T3, E), (∀ j, MemH r ⇑(ccoord b Q' j)) →
      ∀ G : CT, MemH r ⇑G →
      ∃ P : CT, (∀ y, P y = ((fderiv ℝ (A k) (c + Q y) (Q' y) : ℝ) : ℂ) * G y) ∧ MemH r ⇑P ∧
        sn r ⇑P ≤ K * ccoordSum r b Q' * sn r ⇑G := by
  obtain ⟨δ, hδ, K, hK, hrate⟩ := rate_family_gen r hr b c A hA
  obtain ⟨Km, hKm, hmul⟩ := memH_mul r hr
  refine ⟨δ, hδ, Km * K, by positivity, fun k Q hQ hQδ Q' hQ' G hG => ?_⟩
  obtain ⟨R, hRy, hRm, hRs⟩ := hrate k Q hQ hQδ Q' hQ'
  obtain ⟨hRG, hRGs⟩ := hmul R G hRm hG
  refine ⟨R * G, fun y => by simp [hRy], hRG, hRGs.trans ?_⟩
  have := sn_nonneg r ⇑G
  calc Km * sn r ⇑R * sn r ⇑G ≤ Km * (K * ccoordSum r b Q') * sn r ⇑G := by gcongr
    _ = Km * K * ccoordSum r b Q' * sn r ⇑G := by ring

end Multipliers

/-! ### Chain rules for coefficient products along paths -/

section Chain

/-- `σ ↦ A(η + Q σ) G σ` along a path. -/
theorem hasDerivWithinAt_coef_mul {S : Set ℝ} {t : ℝ} {A : MetricRec → ℝ} {Q : ℝ → MetricRec}
    {Q' : MetricRec} {G : ℝ → ℝ} {G' : ℝ} (hA : DifferentiableAt ℝ A (minkowski + Q t))
    (hQ : HasDerivWithinAt Q Q' S t) (hG : HasDerivWithinAt G G' S t) :
    HasDerivWithinAt (fun σ => A (minkowski + Q σ) * G σ)
      (fderiv ℝ A (minkowski + Q t) Q' * G t + A (minkowski + Q t) * G') S t := by
  have h1 : HasDerivWithinAt (fun σ => A (minkowski + Q σ)) (fderiv ℝ A (minkowski + Q t) Q') S t :=
    hA.hasFDerivAt.comp_hasDerivWithinAt t (hQ.const_add minkowski)
  exact h1.mul hG

/-- `σ ↦ DA(η + Q σ)[P σ] G σ` along a path. -/
theorem hasDerivWithinAt_rate_mul {S : Set ℝ} {t : ℝ} {A : MetricRec → ℝ} {Q P : ℝ → MetricRec}
    {Q' P' : MetricRec} {G : ℝ → ℝ} {G' : ℝ} (hA : AnalyticAt ℝ A (minkowski + Q t))
    (hQ : HasDerivWithinAt Q Q' S t) (hP : HasDerivWithinAt P P' S t)
    (hG : HasDerivWithinAt G G' S t) :
    HasDerivWithinAt (fun σ => fderiv ℝ A (minkowski + Q σ) (P σ) * G σ)
      ((fderiv ℝ (fderiv ℝ A) (minkowski + Q t) Q' (P t) + fderiv ℝ A (minkowski + Q t) P') * G t +
        fderiv ℝ A (minkowski + Q t) (P t) * G') S t := by
  have hD : HasDerivWithinAt (fun σ => fderiv ℝ A (minkowski + Q σ))
      (fderiv ℝ (fderiv ℝ A) (minkowski + Q t) Q') S t :=
    hA.fderiv.differentiableAt.hasFDerivAt.comp_hasDerivWithinAt t (hQ.const_add minkowski)
  exact (hD.clm_apply hP).mul hG

/-- The time derivative of the coefficient product `A(η + Q) G`: `DA[Q'] G + A G'`. -/
def prodT (A : MetricRec → ℝ) (Q Q' : MetricRec) (G G' : ℝ) : ℝ :=
  fderiv ℝ A (minkowski + Q) Q' * G + A (minkowski + Q) * G'

/-- The time derivative of the spatial derivative `DA[Qᵢ] G + A Gᵢ` of the coefficient product:
`(D²A[Q', Qᵢ] + DA[Qᵢ']) G + DA[Qᵢ] G' + DA[Q'] Gᵢ + A Gᵢ'`. -/
def prodDT (A : MetricRec → ℝ) (Q Q' Qi Qi' : MetricRec) (G G' Gi Gi' : ℝ) : ℝ :=
  (fderiv ℝ (fderiv ℝ A) (minkowski + Q) Q' Qi + fderiv ℝ A (minkowski + Q) Qi') * G +
    fderiv ℝ A (minkowski + Q) Qi * G' + prodT A Q Q' Gi Gi'

/-- **Time derivative of the spatial derivative of a coefficient product.** -/
theorem hasDerivWithinAt_prodD {S : Set ℝ} {t : ℝ} {A : MetricRec → ℝ} {Q Qi : ℝ → MetricRec}
    {Q' Qi' : MetricRec} {G Gi : ℝ → ℝ} {G' Gi' : ℝ} (hA : AnalyticAt ℝ A (minkowski + Q t))
    (hQ : HasDerivWithinAt Q Q' S t) (hQi : HasDerivWithinAt Qi Qi' S t)
    (hG : HasDerivWithinAt G G' S t) (hGi : HasDerivWithinAt Gi Gi' S t) :
    HasDerivWithinAt (fun σ => fderiv ℝ A (minkowski + Q σ) (Qi σ) * G σ +
        A (minkowski + Q σ) * Gi σ)
      (prodDT A (Q t) Q' (Qi t) Qi' (G t) G' (Gi t) Gi') S t := by
  have h1 := hasDerivWithinAt_rate_mul hA hQ hQi hG
  have h2 := hasDerivWithinAt_coef_mul hA.differentiableAt hQ hGi
  exact (h1.add h2).congr_deriv (by unfold prodDT prodT; ring)

/-- **Time derivative of a coefficient product.** -/
theorem hasDerivWithinAt_prod {S : Set ℝ} {t : ℝ} {A : MetricRec → ℝ} {Q : ℝ → MetricRec}
    {Q' : MetricRec} {G : ℝ → ℝ} {G' : ℝ} (hA : DifferentiableAt ℝ A (minkowski + Q t))
    (hQ : HasDerivWithinAt Q Q' S t) (hG : HasDerivWithinAt G G' S t) :
    HasDerivWithinAt (fun σ => A (minkowski + Q σ) * G σ) (prodT A (Q t) Q' (G t) G') S t :=
  hasDerivWithinAt_coef_mul hA hQ hG

/-- **Time and space derivatives of a coefficient product commute**: if `Q, Q', G, G'` have line
derivatives `Qᵢ, Qᵢ', Gᵢ, Gᵢ'`, the time-derivative field `prodT A Q Q' G G'` has line derivative
`prodDT A Q Q' Qᵢ Qᵢ' G G' Gᵢ Gᵢ'` (symmetry of `D²A` for the analytic coefficient). -/
theorem isLineDeriv_prodT {i : Fin 3} {A : MetricRec → ℝ} {Q Q' Qi Qi' : T3 → MetricRec}
    {G G' Gi Gi' : T3 → ℝ} (hA : ∀ y, AnalyticAt ℝ A (minkowski + Q y))
    (hQ : IsLineDeriv i Q Qi) (hQ' : IsLineDeriv i Q' Qi') (hG : IsLineDeriv i G Gi)
    (hG' : IsLineDeriv i G' Gi') :
    IsLineDeriv i (fun y => prodT A (Q y) (Q' y) (G y) (G' y))
      (fun y => prodDT A (Q y) (Q' y) (Qi y) (Qi' y) (G y) (G' y) (Gi y) (Gi' y)) := by
  intro x
  have hx0 : x + lineShift i 0 = x := by
    have : lineShift i (0 : ℝ) = 0 := by
      funext j; simp [lineShift]
    rw [this, add_zero]
  have hQx := hQ x
  have hQ'x := hQ' x
  have hGx := hG x
  have hG'x := hG' x
  have hAx : AnalyticAt ℝ A (minkowski + Q (x + lineShift i 0)) := by rw [hx0]; exact hA x
  have h1 := hasDerivWithinAt_rate_mul (S := Set.univ) (Q := fun σ => Q (x + lineShift i σ))
    (P := fun σ => Q' (x + lineShift i σ)) (G := fun σ => G (x + lineShift i σ)) hAx
    hQx.hasDerivWithinAt hQ'x.hasDerivWithinAt hGx.hasDerivWithinAt
  have h2 := hasDerivWithinAt_coef_mul (S := Set.univ) (Q := fun σ => Q (x + lineShift i σ))
    (G := fun σ => G' (x + lineShift i σ)) hAx.differentiableAt hQx.hasDerivWithinAt
    hG'x.hasDerivWithinAt
  have h3 := (h1.add h2).hasDerivAt Filter.univ_mem
  simp only [hx0] at h3
  have hsym := (hA x).contDiffAt.isSymmSndFDerivAt_of_omega (Qi x) (Q' x)
  rw [hsym] at h3
  unfold prodDT prodT
  convert h3 using 1
  all_goals first | (funext σ; rfl) | ring

end Chain


/-! ### The linearized normal row -/

section RowDeriv

/-- The harmonic first-jet source component `F_{μν}(η + w.1, w.2)` as a function of the site jet. -/
def srcF (μ ν : Fin 4) (w : JetSpace) : ℝ := harmonicSource (minkowski + w.1) w.2 μ ν

/-- **The linearized harmonic normal row**: the derivative of `normalRow` at the jet
`(q, v, w, qd, vd, qdd)` in the direction `(q', v', w', qd', vd', qdd')`:
`DA[q'] w + A w' + 2 Σᵢ (Dbⁱ[q'] vdᵢ + bⁱ vdᵢ') - Σᵢⱼ (Dc^{ij}[q'] qddᵢⱼ + c^{ij} qddᵢⱼ')
 - DF(q, v, qd)[q', v', qd']`. -/
def rowDeriv (q v w : MetricRec) (qd vd : Fin 3 → MetricRec) (qdd : Fin 3 → Fin 3 → MetricRec)
    (q' v' w' : MetricRec) (qd' vd' : Fin 3 → MetricRec) (qdd' : Fin 3 → Fin 3 → MetricRec)
    (μ ν : Fin 4) : ℝ :=
  prodT harmA q q' (w μ ν) (w' μ ν) + 2 * ∑ i, prodT (harmB i) q q' (vd i μ ν) (vd' i μ ν) -
    ∑ i, ∑ j, prodT (harmC i j) q q' (qdd i j μ ν) (qdd' i j μ ν) -
    fderiv ℝ (srcF μ ν) ((q, v, qd) : JetSpace) ((q', v', qd') : JetSpace)

theorem analyticAt_harmA_of_det {g : MetricRec} (hg : (Matrix.of g).det ≠ 0) :
    AnalyticAt ℝ harmA g := by
  unfold harmA; exact (analyticAt_inv_entry g hg 0 0).neg

theorem analyticAt_harmB_of_det {g : MetricRec} (hg : (Matrix.of g).det ≠ 0) (i : Fin 3) :
    AnalyticAt ℝ (harmB i) g := analyticOnNhd_harmB i g hg

theorem analyticAt_harmC_of_det {g : MetricRec} (hg : (Matrix.of g).det ≠ 0) (i j : Fin 3) :
    AnalyticAt ℝ (harmC i j) g := analyticOnNhd_harmC i j g hg

theorem hasDerivWithinAt_entry {S : Set ℝ} {t : ℝ} {f : ℝ → MetricRec} {f' : MetricRec}
    (h : HasDerivWithinAt f f' S t) (μ ν : Fin 4) :
    HasDerivWithinAt (fun σ => f σ μ ν) (f' μ ν) S t :=
  hasDerivWithinAt_pi.1 (hasDerivWithinAt_pi.1 h μ) ν

theorem normalRow_apply (q v w : MetricRec) (qd vd : Fin 3 → MetricRec)
    (qdd : Fin 3 → Fin 3 → MetricRec) (μ ν : Fin 4) :
    normalRow q v w qd vd qdd μ ν = harmA (minkowski + q) * w μ ν +
      2 * ∑ i, harmB i (minkowski + q) * vd i μ ν -
      ∑ i, ∑ j, harmC i j (minkowski + q) * qdd i j μ ν - srcF μ ν ((q, v, qd) : JetSpace) := by
  simp only [normalRow, srcF, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_apply]

/-- **Chain rule for the normal row along a path of jets** (one-sided within `S`). -/
theorem hasDerivWithinAt_normalRow {S : Set ℝ} {t : ℝ} {q v w : ℝ → MetricRec}
    {qd vd : ℝ → Fin 3 → MetricRec} {qdd : ℝ → Fin 3 → Fin 3 → MetricRec} {q' v' w' : MetricRec}
    {qd' vd' : Fin 3 → MetricRec} {qdd' : Fin 3 → Fin 3 → MetricRec}
    (hdet : (Matrix.of (minkowski + q t)).det ≠ 0) (hq : HasDerivWithinAt q q' S t)
    (hv : HasDerivWithinAt v v' S t) (hw : HasDerivWithinAt w w' S t)
    (hqd : ∀ i, HasDerivWithinAt (fun σ => qd σ i) (qd' i) S t)
    (hvd : ∀ i, HasDerivWithinAt (fun σ => vd σ i) (vd' i) S t)
    (hqdd : ∀ i j, HasDerivWithinAt (fun σ => qdd σ i j) (qdd' i j) S t) (μ ν : Fin 4) :
    HasDerivWithinAt (fun σ => normalRow (q σ) (v σ) (w σ) (qd σ) (vd σ) (qdd σ) μ ν)
      (rowDeriv (q t) (v t) (w t) (qd t) (vd t) (qdd t) q' v' w' qd' vd' qdd' μ ν) S t := by
  simp only [normalRow_apply]
  have hA := hasDerivWithinAt_prod (analyticAt_harmA_of_det hdet).differentiableAt hq
    (hasDerivWithinAt_entry hw μ ν)
  have hB := fun i => hasDerivWithinAt_prod (analyticAt_harmB_of_det hdet i).differentiableAt hq
    (hasDerivWithinAt_entry (hvd i) μ ν)
  have hC := fun i j => hasDerivWithinAt_prod (analyticAt_harmC_of_det hdet i j).differentiableAt
    hq (hasDerivWithinAt_entry (hqdd i j) μ ν)
  have hJ : HasDerivWithinAt (fun σ => ((q σ, v σ, qd σ) : JetSpace)) ((q', v', qd') : JetSpace)
      S t := hq.prodMk (hv.prodMk (hasDerivWithinAt_pi.2 hqd))
  have hS : HasDerivWithinAt (fun σ => srcF μ ν ((q σ, v σ, qd σ) : JetSpace))
      (fderiv ℝ (srcF μ ν) ((q t, v t, qd t) : JetSpace) ((q', v', qd') : JetSpace)) S t := by
    have hd : DifferentiableAt ℝ (srcF μ ν) ((q t, v t, qd t) : JetSpace) :=
      (analyticAt_source_jet_of_det μ ν ((q t, v t, qd t) : JetSpace) hdet).differentiableAt
    exact hd.hasFDerivAt.comp_hasDerivWithinAt t hJ
  have hB' := (HasDerivWithinAt.fun_sum (u := univ) fun i _ => hB i).const_mul (2 : ℝ)
  have hC' := HasDerivWithinAt.fun_sum (u := univ) fun i _ =>
    HasDerivWithinAt.fun_sum (u := univ) fun j _ => hC i j
  have h := ((hA.add hB').sub hC').sub hS
  exact h

/-- The coefficients of the normal row: `a`, `bⁱ`, `c^{ij}`. -/
def rowCoef : Unit ⊕ (Fin 3 ⊕ (Fin 3 × Fin 3)) → MetricRec → ℝ
  | Sum.inl _ => harmA
  | Sum.inr (Sum.inl i) => harmB i
  | Sum.inr (Sum.inr ij) => harmC ij.1 ij.2

theorem analyticAt_rowCoef (k : Unit ⊕ (Fin 3 ⊕ (Fin 3 × Fin 3))) :
    AnalyticAt ℝ (rowCoef k) minkowski := by
  rcases k with _ | i | ij
  · exact analyticAt_harmA
  · exact analyticAt_harmB i
  · exact analyticAt_harmC ij.1 ij.2

set_option maxHeartbeats 1000000 in
/-- **The linearized normal row in `H^r`** (`r ≥ 2`): on a small `H^r` ball of the site jet
`(Q, V, ∂Q)`, every component of the linearized row lies in `H^r` with
`‖ρ'_{μν}‖_{H^r} ≤ C Y' (1 + Y)`, where `Y = ‖W‖ + Σ‖∂V‖ + Σ‖∂²Q‖` and
`Y' = ‖Q'‖ + ‖W'‖ + Σ‖∂V'‖ + Σ‖∂²Q'‖ + ‖(Q', V', ∂Q')‖` (all in `H^r`). -/
theorem rowDeriv_sn_le (r : ℕ) (hr : 2 ≤ r) :
    ∃ δ > 0, ∃ C ≥ 0, ∀ (Q V W Q' V' W' : C(T3, MetricRec))
      (Qd Vd Qd' Vd' : Fin 3 → C(T3, MetricRec)) (Qdd Qdd' : Fin 3 → Fin 3 → C(T3, MetricRec)),
      (∀ k, MemH r ⇑(ccoord bM Q k)) → (∀ k, MemH r ⇑(ccoord bM V k)) →
      (∀ k, MemH r ⇑(ccoord bM W k)) → (∀ i k, MemH r ⇑(ccoord bM (Qd i) k)) →
      (∀ i k, MemH r ⇑(ccoord bM (Vd i) k)) → (∀ i j k, MemH r ⇑(ccoord bM (Qdd i j) k)) →
      (∀ k, MemH r ⇑(ccoord bM Q' k)) → (∀ k, MemH r ⇑(ccoord bM V' k)) →
      (∀ k, MemH r ⇑(ccoord bM W' k)) → (∀ i k, MemH r ⇑(ccoord bM (Qd' i) k)) →
      (∀ i k, MemH r ⇑(ccoord bM (Vd' i) k)) → (∀ i j k, MemH r ⇑(ccoord bM (Qdd' i j) k)) →
      ccoordSum r bJ (jetField Q V Qd) ≤ δ → ∀ μ ν : Fin 4,
      ∃ R : CT, (∀ y, R y = ((rowDeriv (Q y) (V y) (W y) (fun i => Qd i y) (fun i => Vd i y)
          (fun i j => Qdd i j y) (Q' y) (V' y) (W' y) (fun i => Qd' i y) (fun i => Vd' i y)
          (fun i j => Qdd' i j y) μ ν : ℝ) : ℂ)) ∧ MemH r ⇑R ∧
        sn r ⇑R ≤ C * ((ccoordSum r bM Q' + ccoordSum r bM W' + ∑ i, ccoordSum r bM (Vd' i) +
          ∑ i, ∑ j, ccoordSum r bM (Qdd' i j) + ccoordSum r bJ (jetField Q' V' Qd')) *
          (1 + (ccoordSum r bM W + ∑ i, ccoordSum r bM (Vd i) +
            ∑ i, ∑ j, ccoordSum r bM (Qdd i j)))) := by
  obtain ⟨δ1, hδ1, K0, hK0, hcoef⟩ := coef_mul_family r hr rowCoef analyticAt_rowCoef
  obtain ⟨δ2, hδ2, K1, hK1, hrate⟩ := rate_mul_family r hr bM minkowski rowCoef
    analyticAt_rowCoef
  obtain ⟨δ3, hδ3, K2, hK2, hsrc⟩ := rate_family_gen r hr bJ (0 : JetSpace)
    (fun p : Fin 4 × Fin 4 => srcF p.1 p.2) (fun p => analyticAt_source_jet p.1 p.2)
  refine ⟨min (min δ1 δ2) δ3, by positivity, 12 * (K0 + K1) + K2, by positivity,
    fun Q V W Q' V' W' Qd Vd Qd' Vd' Qdd Qdd' hQ hV hW hQd hVd hQdd hQ' hV' hW' hQd' hVd' hQdd'
      hsm μ ν => ?_⟩
  set Y : ℝ := ccoordSum r bM W + ∑ i, ccoordSum r bM (Vd i) + ∑ i, ∑ j, ccoordSum r bM (Qdd i j)
  set Y' : ℝ := ccoordSum r bM Q' + ccoordSum r bM W' + ∑ i, ccoordSum r bM (Vd' i) +
    ∑ i, ∑ j, ccoordSum r bM (Qdd' i j) + ccoordSum r bJ (jetField Q' V' Qd')
  have hn : ∀ (F : C(T3, MetricRec)), 0 ≤ ccoordSum r bM F := fun F => ccoordSum_nonneg _ _ _
  have hVd0 := sum_nonneg fun i (_ : i ∈ univ) => hn (Vd i)
  have hQdd0 := sum_nonneg fun i (_ : i ∈ univ) => sum_nonneg fun j (_ : j ∈ univ) => hn (Qdd i j)
  have hJ0 := ccoordSum_nonneg r bJ (jetField Q' V' Qd')
  have hVd'0 := sum_nonneg fun i (_ : i ∈ univ) => hn (Vd' i)
  have hQdd'0 := sum_nonneg fun i (_ : i ∈ univ) => sum_nonneg fun j (_ : j ∈ univ) => hn (Qdd' i j)
  have hW0 := hn W
  have hW'0 := hn W'
  have hQ'0 := hn Q'
  have hY0 : 0 ≤ Y := by simp only [Y]; linarith
  have hQ'Y : ccoordSum r bM Q' ≤ Y' := by simp only [Y']; linarith
  have hJY : ccoordSum r bJ (jetField Q' V' Qd') ≤ Y' := by simp only [Y']; linarith
  have hY'0 : 0 ≤ Y' := hQ'0.trans hQ'Y
  have hQsm : ccoordSum r bM Q ≤ min δ1 δ2 := by
    have h1 : ccoordSum r bM Q ≤ ccoordSum r bJ (jetField Q V Qd) := by
      rw [ccoordSum_jetField]
      have := sum_nonneg fun i (_ : i ∈ univ) => hn (Qd i)
      have := hn V
      linarith
    exact h1.trans (hsm.trans (min_le_left _ _))
  have hQ1 := hQsm.trans (min_le_left _ _)
  have hQ2 := hQsm.trans (min_le_right _ _)
  -- the terms
  obtain ⟨A1, hA1y, hA1m, hA1s⟩ := hrate (Sum.inl ()) Q hQ hQ2 Q' hQ' (cmp W μ ν) (memH_cmp hW μ ν)
  obtain ⟨A2, hA2y, hA2m, hA2s⟩ := hcoef (Sum.inl ()) Q hQ hQ1 (cmp W' μ ν) (memH_cmp hW' μ ν)
  have hB1 := fun i => hrate (Sum.inr (Sum.inl i)) Q hQ hQ2 Q' hQ' (cmp (Vd i) μ ν)
    (memH_cmp (hVd i) μ ν)
  have hB2 := fun i => hcoef (Sum.inr (Sum.inl i)) Q hQ hQ1 (cmp (Vd' i) μ ν)
    (memH_cmp (hVd' i) μ ν)
  have hC1 := fun i j => hrate (Sum.inr (Sum.inr (i, j))) Q hQ hQ2 Q' hQ' (cmp (Qdd i j) μ ν)
    (memH_cmp (hQdd i j) μ ν)
  have hC2 := fun i j => hcoef (Sum.inr (Sum.inr (i, j))) Q hQ hQ1 (cmp (Qdd' i j) μ ν)
    (memH_cmp (hQdd' i j) μ ν)
  choose B1 hB1y hB1m hB1s using hB1
  choose B2 hB2y hB2m hB2s using hB2
  choose C1 hC1y hC1m hC1s using hC1
  choose C2 hC2y hC2m hC2s using hC2
  obtain ⟨S0, hS0y, hS0m, hS0s⟩ := hsrc (μ, ν) (jetField Q V Qd) (memH_jetField hQ hV hQd)
    (hsm.trans (min_le_right _ _)) (jetField Q' V' Qd') (memH_jetField hQ' hV' hQd')
  set TB : CT := ∑ i, (B1 i + B2 i)
  set TC : CT := ∑ i, ∑ j, (C1 i j + C2 i j)
  have hTBi : ∀ i, MemH r ⇑(B1 i + B2 i) := fun i => memH_add (hB1m i) (hB2m i)
  have hTCij : ∀ i j, MemH r ⇑(C1 i j + C2 i j) := fun i j => memH_add (hC1m i j) (hC2m i j)
  have hTB := sn_sum_le' univ hTBi
  have hTCi := fun i => sn_sum_le' univ (hTCij i)
  have hTC := sn_sum_le' univ fun i => (hTCi i).1
  refine ⟨A1 + A2 + (2 : ℂ) • TB - TC - S0, fun y => ?_, ?_, ?_⟩
  · simp only [ContinuousMap.sub_apply, ContinuousMap.add_apply, ContinuousMap.smul_apply, TB, TC,
      ContinuousMap.coe_sum, Finset.sum_apply, hA1y, hA2y, hB1y, hB2y, hC1y, hC2y, hS0y,
      smul_eq_mul, cmp_apply]
    simp only [rowDeriv, prodT, rowCoef, zero_add, jetField, ContinuousMap.coe_mk]
    push_cast
    simp only [mul_sum]
  · exact memH_sub (memH_sub (memH_add (memH_add hA1m hA2m) (memH_smul _ hTB.1)) hTC.1) hS0m
  · -- the bounds
    have hcmp := fun (F : C(T3, MetricRec)) => sn_cmp_le_ccoordSum r F μ ν
    have hWY : sn r ⇑(cmp W μ ν) ≤ Y := (hcmp W).trans (by simp only [Y]; linarith)
    have hW'Y : sn r ⇑(cmp W' μ ν) ≤ Y' := (hcmp W').trans (by simp only [Y']; linarith)
    have eA1 : sn r ⇑A1 ≤ K1 * Y' * Y := hA1s.trans
      (mul_le_mul (mul_le_mul_of_nonneg_left hQ'Y hK1) hWY (sn_nonneg _ _) (mul_nonneg hK1 hY'0))
    have eA2 : sn r ⇑A2 ≤ K0 * Y' := hA2s.trans (mul_le_mul_of_nonneg_left hW'Y hK0)
    have eB : sn r ⇑TB ≤ K1 * Y' * Y + K0 * Y' := by
      refine hTB.2.trans ?_
      have h1 : ∀ i ∈ univ, sn r ⇑(B1 i + B2 i) ≤ K1 * Y' * ccoordSum r bM (Vd i) +
          K0 * ccoordSum r bM (Vd' i) := by
        intro i _
        refine (sn_add_le' (hB1m i) (hB2m i)).trans (add_le_add ((hB1s i).trans ?_)
          ((hB2s i).trans ?_))
        · exact mul_le_mul (mul_le_mul_of_nonneg_left hQ'Y hK1) (hcmp (Vd i)) (sn_nonneg _ _)
            (mul_nonneg hK1 hY'0)
        · exact mul_le_mul_of_nonneg_left (hcmp (Vd' i)) hK0
      refine (sum_le_sum h1).trans ?_
      rw [sum_add_distrib, ← mul_sum, ← mul_sum]
      have e1 : ∑ i, ccoordSum r bM (Vd i) ≤ Y := by simp only [Y]; linarith
      have e2 : ∑ i, ccoordSum r bM (Vd' i) ≤ Y' := by simp only [Y']; linarith
      exact add_le_add (mul_le_mul_of_nonneg_left e1 (mul_nonneg hK1 hY'0))
        (mul_le_mul_of_nonneg_left e2 hK0)
    have eC : sn r ⇑TC ≤ K1 * Y' * Y + K0 * Y' := by
      refine hTC.2.trans ?_
      have h1 : ∀ i ∈ univ, sn r ⇑(∑ j, (C1 i j + C2 i j)) ≤
          K1 * Y' * ∑ j, ccoordSum r bM (Qdd i j) + K0 * ∑ j, ccoordSum r bM (Qdd' i j) := by
        intro i _
        refine (hTCi i).2.trans ?_
        rw [mul_sum, mul_sum, ← sum_add_distrib]
        refine sum_le_sum fun j _ => ?_
        refine (sn_add_le' (hC1m i j) (hC2m i j)).trans (add_le_add ((hC1s i j).trans ?_)
          ((hC2s i j).trans ?_))
        · exact mul_le_mul (mul_le_mul_of_nonneg_left hQ'Y hK1) (hcmp (Qdd i j)) (sn_nonneg _ _)
            (mul_nonneg hK1 hY'0)
        · exact mul_le_mul_of_nonneg_left (hcmp (Qdd' i j)) hK0
      refine (sum_le_sum h1).trans ?_
      rw [sum_add_distrib, ← mul_sum, ← mul_sum]
      have e1 : ∑ i, ∑ j, ccoordSum r bM (Qdd i j) ≤ Y := by simp only [Y]; linarith
      have e2 : ∑ i, ∑ j, ccoordSum r bM (Qdd' i j) ≤ Y' := by simp only [Y']; linarith
      exact add_le_add (mul_le_mul_of_nonneg_left e1 (mul_nonneg hK1 hY'0))
        (mul_le_mul_of_nonneg_left e2 hK0)
    have eS : sn r ⇑S0 ≤ K2 * Y' := hS0s.trans (mul_le_mul_of_nonneg_left hJY hK2)
    have t1 := sn_sub_le' (memH_sub (memH_add (memH_add hA1m hA2m) (memH_smul (2 : ℂ) hTB.1))
      hTC.1) hS0m
    have t2 := sn_sub_le' (memH_add (memH_add hA1m hA2m) (memH_smul (2 : ℂ) hTB.1)) hTC.1
    have t3 := sn_add_le' (memH_add hA1m hA2m) (memH_smul (2 : ℂ) hTB.1)
    have t4 := sn_add_le' hA1m hA2m
    have t5 := sn_smul r (2 : ℂ) TB
    have hn2 : ‖(2 : ℂ)‖ = 2 := by simp
    rw [hn2] at t5
    have p1 := mul_nonneg (mul_nonneg hK1 hY'0) hY0
    have p2 := mul_nonneg hK0 hY'0
    have p3 := mul_nonneg hK2 hY'0
    calc sn r ⇑(A1 + A2 + (2 : ℂ) • TB - TC - S0)
        ≤ sn r ⇑A1 + sn r ⇑A2 + 2 * sn r ⇑TB + sn r ⇑TC + sn r ⇑S0 := by linarith
      _ ≤ K1 * Y' * Y + K0 * Y' + 2 * (K1 * Y' * Y + K0 * Y') + (K1 * Y' * Y + K0 * Y') +
          K2 * Y' := by linarith
      _ ≤ (12 * (K0 + K1) + K2) * (Y' * (1 + Y)) := by nlinarith

end RowDeriv


/-! ### Interpolated grid paths and the differentiated consistency error -/

section GridPaths

variable {N : ℕ} [NeZero N]

local notation "Smp" => PeriodicGridSobolev.Sampling.sample N

/-- Real interpolation commutes with one-sided time derivatives. -/
theorem hasDerivWithinAt_reField {S : Set ℝ} {t : ℝ} {w : ℝ → Fin 4 → Fin 4 → Grid N → ℂ}
    {w' : Fin 4 → Fin 4 → Grid N → ℂ}
    (hw : ∀ μ ν x, HasDerivWithinAt (fun τ => w τ μ ν x) (w' μ ν x) S t) (y : T3) :
    HasDerivWithinAt (fun τ => reField (w τ) y) (reField w' y) S t := by
  refine hasDerivWithinAt_pi.2 fun μ => hasDerivWithinAt_pi.2 fun ν => ?_
  have e1 : (fun τ => reField (w τ) y μ ν) = fun τ => (∑ x, w τ μ ν x *
      PeriodicGridSobolev.interp (fun z => if z = x then (1 : ℂ) else 0) y).re :=
    funext fun τ => congrArg Complex.re (interp_apply_eq_sum _ y)
  have e2 : reField w' y μ ν = (∑ x, w' μ ν x *
      PeriodicGridSobolev.interp (fun z => if z = x then (1 : ℂ) else 0) y).re :=
    congrArg Complex.re (interp_apply_eq_sum _ y)
  show HasDerivWithinAt (fun τ => reField (w τ) y μ ν) (reField w' y μ ν) S t
  rw [e1, e2]
  have h : HasDerivWithinAt (fun τ => ∑ x, w τ μ ν x *
      PeriodicGridSobolev.interp (fun z => if z = x then (1 : ℂ) else 0) y)
      (∑ x, w' μ ν x * PeriodicGridSobolev.interp (fun z => if z = x then (1 : ℂ) else 0) y) S t :=
    HasDerivWithinAt.fun_sum fun x _ => (hw μ ν x).mul_const _
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt t h

/-- A grid linear map commutes with one-sided time derivatives. -/
theorem hasDerivWithinAt_end {S : Set ℝ} {t : ℝ} (L : Module.End ℂ (Grid N → ℂ))
    {f : ℝ → Grid N → ℂ} {f' : Grid N → ℂ}
    (hf : ∀ z, HasDerivWithinAt (fun τ => f τ z) (f' z) S t) (x : Grid N) :
    HasDerivWithinAt (fun τ => L (f τ) x) (L f' x) S t := by
  have h : HasDerivWithinAt f f' S t := hasDerivWithinAt_pi.2 hf
  have := ((LinearMap.toContinuousLinearMap L).restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt
    t h
  exact hasDerivWithinAt_pi.1 this x

theorem hasDerivWithinAt_cxcomp {S : Set ℝ} {t : ℝ} {u : ℝ → Grid N → MetricRec}
    {u' : Grid N → MetricRec} (hu : ∀ x μ ν, HasDerivWithinAt (fun τ => u τ x μ ν) (u' x μ ν) S t)
    (μ ν : Fin 4) (x : Grid N) :
    HasDerivWithinAt (fun τ => cx (comp (u τ) μ ν) x) (cx (comp u' μ ν) x) S t :=
  (hu x μ ν).ofReal_comp

theorem hasDerivWithinAt_interpRec' {S : Set ℝ} {t : ℝ} {u : ℝ → Grid N → MetricRec}
    {u' : Grid N → MetricRec} (hu : ∀ x μ ν, HasDerivWithinAt (fun τ => u τ x μ ν) (u' x μ ν) S t)
    (y : T3) : HasDerivWithinAt (fun τ => interpRec (u τ) y) (interpRec u' y) S t :=
  hasDerivWithinAt_reField (fun μ ν x => hasDerivWithinAt_cxcomp hu μ ν x) y

theorem hasDerivWithinAt_interpD' {S : Set ℝ} {t : ℝ} {u : ℝ → Grid N → MetricRec}
    {u' : Grid N → MetricRec} (hu : ∀ x μ ν, HasDerivWithinAt (fun τ => u τ x μ ν) (u' x μ ν) S t)
    (i : Fin 3) (y : T3) : HasDerivWithinAt (fun τ => interpD (u τ) i y) (interpD u' i y) S t :=
  hasDerivWithinAt_reField (fun μ ν x => hasDerivWithinAt_end
    (PeriodicGridSobolev.TimeConsistency.specDL i) (fun z => hasDerivWithinAt_cxcomp hu μ ν z) x) y

theorem hasDerivWithinAt_interpDD' {S : Set ℝ} {t : ℝ} {u : ℝ → Grid N → MetricRec}
    {u' : Grid N → MetricRec} (hu : ∀ x μ ν, HasDerivWithinAt (fun τ => u τ x μ ν) (u' x μ ν) S t)
    (i j : Fin 3) (y : T3) :
    HasDerivWithinAt (fun τ => interpDD (u τ) i j y) (interpDD u' i j y) S t :=
  hasDerivWithinAt_reField (fun μ ν x => hasDerivWithinAt_end
    (PeriodicGridSobolev.TimeConsistency.specDL i) (fun z => hasDerivWithinAt_end
      (PeriodicGridSobolev.TimeConsistency.specDL j)
        (fun z' => hasDerivWithinAt_cxcomp hu μ ν z') z) x) y

/-- **The consistency error of the interpolant jet** (the right-hand side of
`sampled_row_identity` for `Q = 𝓘_h q`, `V = 𝓘_h v`): flux, interpolation, transport and
compensator errors. -/
def errRow (q v : Grid N → MetricRec) (μ ν : Fin 4) : Grid N → ℂ :=
  ∑ i, ∑ j, ((Smp (pdF (interpRec q) (interpD q) (interpDD q) i j μ ν) -
      PeriodicGridSobolev.Dm i (Smp (pfF (interpRec q) (interpD q) i j μ ν))) +
      PeriodicGridSobolev.Dm i (cx (cArr q i j) *
        (Smp ⇑(cmp (interpD q j) μ ν) - PeriodicGridSobolev.Dp j (cx (comp q μ ν))))) -
    ∑ i, cx (bArr q i) * (Smp ⇑(cmp (interpD v i) μ ν) -
      PeriodicGridSobolev.D0 i (cx (comp v μ ν))) -
    ∑ i, (Smp (bdF (interpRec q) (interpRec v) (interpD q) (interpD v) i μ ν) -
      PeriodicGridSobolev.D0 i (Smp (bfF (interpRec q) (interpRec v) i μ ν))) +
    (cx (fun x => compensatorMap (q x, v x,
        fun i => interpD q i (PeriodicGridSobolev.samplePt x)) μ ν) -
      cx (comp (Garr q v) μ ν))

/-- **The sampled row identity for an interpolant jet**: for every acceleration record `W`,
`a(q)(W - V_{0,h}(q, v)) - 𝒮_h ρ = errRow q v`, `ρ` the continuum normal row of the interpolant
jet `(𝓘_h q, 𝓘_h v, 𝓘_h W, ∂𝓘_h q, ∂𝓘_h v, ∂²𝓘_h q)`. -/
theorem row_identity_interp (q v W : Grid N → MetricRec) (ha : ∀ x, aArr q x ≠ 0)
    (μ ν : Fin 4) :
    cx (aArr q) * cx (comp (W - harmonicWriterAcceleration q v) μ ν) -
      Smp (rowF (interpRec q) (interpRec v) (interpRec W) (interpD q) (interpD v) (interpDD q) μ ν)
      = errRow q v μ ν := by
  have h := sampled_row_identity (N := N) (interpRec q) (interpRec v) (interpRec W) (interpD q)
    (interpD v) (interpDD q) (by rw [sampleRec_interpRec]; exact ha) μ ν
  rw [sampleRec_interpRec, sampleRec_interpRec, sampleRec_interpRec] at h
  exact h

/-- **The time derivative of the consistency error** along a path `(q, v) → (q', v')`. -/
def errDeriv (q v q' v' : Grid N → MetricRec) (μ ν : Fin 4) : Grid N → ℂ :=
  ∑ i, ∑ j, ((Smp (fun y => ((prodDT (harmC i j) (interpRec q y) (interpRec q' y)
        (interpD q i y) (interpD q' i y) (interpD q j y μ ν) (interpD q' j y μ ν)
        (interpDD q i j y μ ν) (interpDD q' i j y μ ν) : ℝ) : ℂ)) -
      PeriodicGridSobolev.Dm i (Smp (fun y => ((prodT (harmC i j) (interpRec q y)
        (interpRec q' y) (interpD q j y μ ν) (interpD q' j y μ ν) : ℝ) : ℂ)))) +
      PeriodicGridSobolev.Dm i (cx (fun x => fderiv ℝ (harmC i j) (minkowski + q x) (q' x)) *
          (Smp ⇑(cmp (interpD q j) μ ν) - PeriodicGridSobolev.Dp j (cx (comp q μ ν))) +
        cx (cArr q i j) *
          (Smp ⇑(cmp (interpD q' j) μ ν) - PeriodicGridSobolev.Dp j (cx (comp q' μ ν))))) -
    ∑ i, (cx (fun x => fderiv ℝ (harmB i) (minkowski + q x) (q' x)) *
        (Smp ⇑(cmp (interpD v i) μ ν) - PeriodicGridSobolev.D0 i (cx (comp v μ ν))) +
      cx (bArr q i) *
        (Smp ⇑(cmp (interpD v' i) μ ν) - PeriodicGridSobolev.D0 i (cx (comp v' μ ν)))) -
    ∑ i, (Smp (fun y => ((prodDT (harmB i) (interpRec q y) (interpRec q' y)
        (interpD q i y) (interpD q' i y) (interpRec v y μ ν) (interpRec v' y μ ν)
        (interpD v i y μ ν) (interpD v' i y μ ν) : ℝ) : ℂ)) -
      PeriodicGridSobolev.D0 i (Smp (fun y => ((prodT (harmB i) (interpRec q y)
        (interpRec q' y) (interpRec v y μ ν) (interpRec v' y μ ν) : ℝ) : ℂ)))) +
    (cx (fun x => fderiv ℝ (fun w : JetSpace => compensatorMap w μ ν)
        (q x, v x, fun i => interpD q i (PeriodicGridSobolev.samplePt x))
        (q' x, v' x, fun i => interpD q' i (PeriodicGridSobolev.samplePt x))) -
      cx (fun x => fderiv ℝ (fun w : JetSpace => compensatorMap w μ ν) (jetArr q v x)
        (jetArr q' v' x)))

theorem interpRec_sample_eq (u : Grid N → MetricRec) (x : Grid N) :
    interpRec u (PeriodicGridSobolev.samplePt x) = u x :=
  congrFun (sampleRec_interpRec u) x

set_option maxHeartbeats 2000000 in
/-- **The consistency error is differentiable along a path of records**, with derivative
`errDeriv` (one-sided within `S`; the chart is nondegenerate at time `t`). -/
theorem hasDerivWithinAt_errRow {S : Set ℝ} {t : ℝ} {q v : ℝ → Grid N → MetricRec}
    {q' v' : Grid N → MetricRec}
    (hq : ∀ x μ ν, HasDerivWithinAt (fun τ => q τ x μ ν) (q' x μ ν) S t)
    (hv : ∀ x μ ν, HasDerivWithinAt (fun τ => v τ x μ ν) (v' x μ ν) S t)
    (hdet : ∀ y, (Matrix.of (minkowski + interpRec (q t) y)).det ≠ 0) (μ ν : Fin 4) :
    HasDerivWithinAt (fun τ => errRow (q τ) (v τ) μ ν) (errDeriv (q t) (v t) q' v' μ ν) S t := by
  have dQ := hasDerivWithinAt_interpRec' hq
  have dV := hasDerivWithinAt_interpRec' hv
  have dQd := hasDerivWithinAt_interpD' hq
  have dVd := hasDerivWithinAt_interpD' hv
  have dQdd := hasDerivWithinAt_interpDD' hq
  have hdetx : ∀ x, (Matrix.of (minkowski + q t x)).det ≠ 0 := fun x => by
    have := hdet (PeriodicGridSobolev.samplePt x); rwa [interpRec_sample_eq] at this
  have pi := fun {F : ℝ → Grid N → ℂ} {F' : Grid N → ℂ}
    (h : ∀ x, HasDerivWithinAt (fun τ => F τ x) (F' x) S t) => (hasDerivWithinAt_pi.2 h :
      HasDerivWithinAt F F' S t)
  have lin := fun (L : Module.End ℂ (Grid N → ℂ)) {F : ℝ → Grid N → ℂ} {F' : Grid N → ℂ}
    (h : ∀ x, HasDerivWithinAt (fun τ => F τ x) (F' x) S t) =>
    (hasDerivWithinAt_pi.2 fun x => hasDerivWithinAt_end L h x :
      HasDerivWithinAt (fun τ => L (F τ)) (L F') S t)
  -- (1) flux derivative terms
  have hPd : ∀ i j, ∀ x, HasDerivWithinAt
      (fun τ => Smp (pdF (interpRec (q τ)) (interpD (q τ)) (interpDD (q τ)) i j μ ν) x)
      (Smp (fun y => ((prodDT (harmC i j) (interpRec (q t) y) (interpRec q' y)
        (interpD (q t) i y) (interpD q' i y) (interpD (q t) j y μ ν) (interpD q' j y μ ν)
        (interpDD (q t) i j y μ ν) (interpDD q' i j y μ ν) : ℝ) : ℂ)) x) S t := by
    intro i j x
    set y := PeriodicGridSobolev.samplePt x
    exact (hasDerivWithinAt_prodD (A := harmC i j) (analyticAt_harmC_of_det (hdet y) i j) (dQ y)
      (dQd i y) (hasDerivWithinAt_entry (dQd j y) μ ν)
      (hasDerivWithinAt_entry (dQdd i j y) μ ν)).ofReal_comp
  have hPf : ∀ i j, ∀ x, HasDerivWithinAt
      (fun τ => Smp (pfF (interpRec (q τ)) (interpD (q τ)) i j μ ν) x)
      (Smp (fun y => ((prodT (harmC i j) (interpRec (q t) y) (interpRec q' y)
        (interpD (q t) j y μ ν) (interpD q' j y μ ν) : ℝ) : ℂ)) x) S t := by
    intro i j x
    set y := PeriodicGridSobolev.samplePt x
    exact (hasDerivWithinAt_prod (A := harmC i j)
      (analyticAt_harmC_of_det (hdet y) i j).differentiableAt (dQ y)
      (hasDerivWithinAt_entry (dQd j y) μ ν)).ofReal_comp
  -- (2) the flux interpolation error
  have hcoefC : ∀ i j x, HasDerivWithinAt (fun τ => cx (cArr (q τ) i j) x)
      (cx (fun x => fderiv ℝ (harmC i j) (minkowski + q t x) (q' x)) x) S t := fun i j x =>
    (hasDerivWithinAt_coef hq x (analyticAt_harmC_of_det (hdetx x) i j).differentiableAt).ofReal_comp
  have hYq : ∀ j x, HasDerivWithinAt (fun τ => (Smp ⇑(cmp (interpD (q τ) j) μ ν) -
      PeriodicGridSobolev.Dp j (cx (comp (q τ) μ ν))) x)
      ((Smp ⇑(cmp (interpD q' j) μ ν) - PeriodicGridSobolev.Dp j (cx (comp q' μ ν))) x) S t := by
    intro j x
    exact ((hasDerivWithinAt_entry (dQd j (PeriodicGridSobolev.samplePt x)) μ ν).ofReal_comp).sub
      (hasDerivWithinAt_end (PeriodicGridSobolev.Dp j) (hasDerivWithinAt_cxcomp hq μ ν) x)
  have hT1b : ∀ i j, ∀ x, HasDerivWithinAt (fun τ => (cx (cArr (q τ) i j) *
      (Smp ⇑(cmp (interpD (q τ) j) μ ν) - PeriodicGridSobolev.Dp j (cx (comp (q τ) μ ν)))) x)
      ((cx (fun x => fderiv ℝ (harmC i j) (minkowski + q t x) (q' x)) *
          (Smp ⇑(cmp (interpD (q t) j) μ ν) - PeriodicGridSobolev.Dp j (cx (comp (q t) μ ν))) +
        cx (cArr (q t) i j) *
          (Smp ⇑(cmp (interpD q' j) μ ν) - PeriodicGridSobolev.Dp j (cx (comp q' μ ν)))) x)
      S t := fun i j x => (hcoefC i j x).mul (hYq j x)
  -- (3) the transport interpolation error
  have hcoefB : ∀ i x, HasDerivWithinAt (fun τ => cx (bArr (q τ) i) x)
      (cx (fun x => fderiv ℝ (harmB i) (minkowski + q t x) (q' x)) x) S t := fun i x =>
    (hasDerivWithinAt_coef hq x (analyticAt_harmB_of_det (hdetx x) i).differentiableAt).ofReal_comp
  have hZ : ∀ i x, HasDerivWithinAt (fun τ => (Smp ⇑(cmp (interpD (v τ) i) μ ν) -
      PeriodicGridSobolev.D0 i (cx (comp (v τ) μ ν))) x)
      ((Smp ⇑(cmp (interpD v' i) μ ν) - PeriodicGridSobolev.D0 i (cx (comp v' μ ν))) x) S t := by
    intro i x
    exact ((hasDerivWithinAt_entry (dVd i (PeriodicGridSobolev.samplePt x)) μ ν).ofReal_comp).sub
      (hasDerivWithinAt_end (PeriodicGridSobolev.D0 i) (hasDerivWithinAt_cxcomp hv μ ν) x)
  have hT2 : ∀ i x, HasDerivWithinAt (fun τ => (cx (bArr (q τ) i) *
      (Smp ⇑(cmp (interpD (v τ) i) μ ν) - PeriodicGridSobolev.D0 i (cx (comp (v τ) μ ν)))) x)
      ((cx (fun x => fderiv ℝ (harmB i) (minkowski + q t x) (q' x)) *
          (Smp ⇑(cmp (interpD (v t) i) μ ν) - PeriodicGridSobolev.D0 i (cx (comp (v t) μ ν))) +
        cx (bArr (q t) i) *
          (Smp ⇑(cmp (interpD v' i) μ ν) - PeriodicGridSobolev.D0 i (cx (comp v' μ ν)))) x)
      S t := fun i x => (hcoefB i x).mul (hZ i x)
  -- (4) transport derivative terms
  have hBd : ∀ i, ∀ x, HasDerivWithinAt
      (fun τ => Smp (bdF (interpRec (q τ)) (interpRec (v τ)) (interpD (q τ)) (interpD (v τ)) i μ ν) x)
      (Smp (fun y => ((prodDT (harmB i) (interpRec (q t) y) (interpRec q' y)
        (interpD (q t) i y) (interpD q' i y) (interpRec (v t) y μ ν) (interpRec v' y μ ν)
        (interpD (v t) i y μ ν) (interpD v' i y μ ν) : ℝ) : ℂ)) x) S t := by
    intro i x
    set y := PeriodicGridSobolev.samplePt x
    exact (hasDerivWithinAt_prodD (A := harmB i) (analyticAt_harmB_of_det (hdet y) i) (dQ y)
      (dQd i y) (hasDerivWithinAt_entry (dV y) μ ν)
      (hasDerivWithinAt_entry (dVd i y) μ ν)).ofReal_comp
  have hBf : ∀ i, ∀ x, HasDerivWithinAt
      (fun τ => Smp (bfF (interpRec (q τ)) (interpRec (v τ)) i μ ν) x)
      (Smp (fun y => ((prodT (harmB i) (interpRec (q t) y) (interpRec q' y)
        (interpRec (v t) y μ ν) (interpRec v' y μ ν) : ℝ) : ℂ)) x) S t := by
    intro i x
    set y := PeriodicGridSobolev.samplePt x
    exact (hasDerivWithinAt_prod (A := harmB i)
      (analyticAt_harmB_of_det (hdet y) i).differentiableAt (dQ y)
      (hasDerivWithinAt_entry (dV y) μ ν)).ofReal_comp
  -- (5) the compensator
  have hG1 : ∀ x, HasDerivWithinAt (fun τ => cx (fun x => compensatorMap (q τ x, v τ x,
        fun i => interpD (q τ) i (PeriodicGridSobolev.samplePt x)) μ ν) x)
      (cx (fun x => fderiv ℝ (fun w : JetSpace => compensatorMap w μ ν)
        (q t x, v t x, fun i => interpD (q t) i (PeriodicGridSobolev.samplePt x))
        (q' x, v' x, fun i => interpD q' i (PeriodicGridSobolev.samplePt x))) x) S t := by
    intro x
    have hpath : HasDerivWithinAt (fun τ => ((q τ x, v τ x,
        fun i => interpD (q τ) i (PeriodicGridSobolev.samplePt x)) : JetSpace))
        ((q' x, v' x, fun i => interpD q' i (PeriodicGridSobolev.samplePt x)) : JetSpace) S t :=
      (hasDerivWithinAt_pi.2 fun μ => hasDerivWithinAt_pi.2 fun ν => hq x μ ν).prodMk
        ((hasDerivWithinAt_pi.2 fun μ => hasDerivWithinAt_pi.2 fun ν => hv x μ ν).prodMk
          (hasDerivWithinAt_pi.2 fun i => dQd i _))
    have hd : DifferentiableAt ℝ (fun w : JetSpace => compensatorMap w μ ν)
        ((q t x, v t x, fun i => interpD (q t) i (PeriodicGridSobolev.samplePt x)) : JetSpace) :=
      (analyticAt_compensatorMap_of_det μ ν _ (hdetx x)).differentiableAt
    exact (hd.hasFDerivAt.comp_hasDerivWithinAt t hpath).ofReal_comp
  have hG2 : ∀ x, HasDerivWithinAt (fun τ => cx (comp (Garr (q τ) (v τ)) μ ν) x)
      (cx (fun x => fderiv ℝ (fun w : JetSpace => compensatorMap w μ ν) (jetArr (q t) (v t) x)
        (jetArr q' v' x)) x) S t := by
    intro x
    have hd : DifferentiableAt ℝ (fun w : JetSpace => compensatorMap w μ ν)
        (jetArr (q t) (v t) x) :=
      (analyticAt_compensatorMap_of_det μ ν _ (by simpa [jetArr] using hdetx x)).differentiableAt
    exact (hd.hasFDerivAt.comp_hasDerivWithinAt t
      (hasDerivWithinAt_jetArr (fun y μ ν => hq y μ ν) (fun y μ ν => hv y μ ν) x)).ofReal_comp
  -- assembly
  have g1 := HasDerivWithinAt.fun_sum (u := univ) fun i _ => HasDerivWithinAt.fun_sum (u := univ)
    fun j _ => ((pi (hPd i j)).sub (lin (PeriodicGridSobolev.Dm i) (hPf i j))).add
      (lin (PeriodicGridSobolev.Dm i) (hT1b i j))
  have g2 := HasDerivWithinAt.fun_sum (u := univ) fun i _ => pi (hT2 i)
  have g3 := HasDerivWithinAt.fun_sum (u := univ) fun i _ =>
    (pi (hBd i)).sub (lin (PeriodicGridSobolev.D0 i) (hBf i))
  have g4 := (pi hG1).sub (pi hG2)
  exact ((g1.sub g2).sub g3).add g4

end GridPaths


/-! ### Estimates for the differentiated consistency error -/

section ErrBounds

theorem analyticOnNhd_rowCoef (k : Unit ⊕ (Fin 3 ⊕ (Fin 3 × Fin 3))) :
    AnalyticOnNhd ℝ (rowCoef k) detSet := by
  rcases k with _ | i | ij
  · exact fun g hg => analyticAt_harmA_of_det hg
  · exact analyticOnNhd_harmB i
  · exact analyticOnNhd_harmC ij.1 ij.2

/-- Continuity of the field `prodDT A Q Q' Qᵢ Qᵢ' F F' Fᵢ Fᵢ'` on the chart. -/
theorem continuous_prodDT {A : MetricRec → ℝ} (hA : AnalyticOnNhd ℝ A detSet)
    {Q Q' Qi Qi' F F' Fi Fi' : C(T3, MetricRec)} (hU : ∀ y, minkowski + Q y ∈ detSet)
    (μ ν : Fin 4) :
    Continuous fun y => prodDT A (Q y) (Q' y) (Qi y) (Qi' y) (F y μ ν) (F' y μ ν) (Fi y μ ν)
      (Fi' y μ ν) := by
  have hQc : Continuous fun y => minkowski + Q y := continuous_const.add Q.continuous
  have c0 : Continuous fun y => A (minkowski + Q y) := hA.continuousOn.comp_continuous hQc hU
  have c1 : Continuous fun y => fderiv ℝ A (minkowski + Q y) :=
    hA.fderiv.continuousOn.comp_continuous hQc hU
  have c2 : Continuous fun y => fderiv ℝ (fderiv ℝ A) (minkowski + Q y) :=
    hA.fderiv.fderiv.continuousOn.comp_continuous hQc hU
  have cF := continuous_comp_apply F μ ν
  have cF' := continuous_comp_apply F' μ ν
  have cFi := continuous_comp_apply Fi μ ν
  have cFi' := continuous_comp_apply Fi' μ ν
  unfold prodDT prodT
  exact (((((c2.clm_apply Q'.continuous).clm_apply Qi.continuous).add
    (c1.clm_apply Qi'.continuous)).mul cF).add ((c1.clm_apply Qi.continuous).mul cF')).add
    (((c1.clm_apply Q'.continuous).mul cFi).add (c0.mul cFi'))

/-- **The differentiated flux and transport products as continuum fields**: on a small `H^r`
ball of `Q`, for `A = a, bⁱ, c^{ij}`, the time derivative `P = DA[Q'] F + A F'` of the product
`A(η + Q) F_{μν}` is a continuous `H^r` field with `‖P‖_{H^r} ≤ C(‖Q'‖ ‖F‖ + ‖F'‖)`, and its line
derivative is the continuous field `prodDT` (the time derivative of `∂ᵢ(A F)`). -/
theorem prodT_fields (r : ℕ) (hr : 2 ≤ r) :
    ∃ δ > 0, ∃ C ≥ 0, ∀ (k : Unit ⊕ (Fin 3 ⊕ (Fin 3 × Fin 3))) (i : Fin 3)
      (Q Q' Qi Qi' F F' Fi Fi' : C(T3, MetricRec)) (μ ν : Fin 4),
      (∀ y, (Matrix.of (minkowski + Q y)).det ≠ 0) → IsLineDeriv i ⇑Q ⇑Qi →
      IsLineDeriv i ⇑Q' ⇑Qi' → IsLineDeriv i ⇑F ⇑Fi → IsLineDeriv i ⇑F' ⇑Fi' →
      (∀ m, MemH r ⇑(ccoord bM Q m)) → (∀ m, MemH r ⇑(ccoord bM Q' m)) →
      (∀ m, MemH r ⇑(ccoord bM F m)) → (∀ m, MemH r ⇑(ccoord bM F' m)) →
      ccoordSum r bM Q ≤ δ →
      ∃ P D : CT, (∀ y, P y = ((prodT (rowCoef k) (Q y) (Q' y) (F y μ ν) (F' y μ ν) : ℝ) : ℂ)) ∧
        (∀ y, D y = ((prodDT (rowCoef k) (Q y) (Q' y) (Qi y) (Qi' y) (F y μ ν) (F' y μ ν)
          (Fi y μ ν) (Fi' y μ ν) : ℝ) : ℂ)) ∧ IsLineDeriv i ⇑P ⇑D ∧ MemH r ⇑P ∧
        sn r ⇑P ≤ C * (ccoordSum r bM Q' * ccoordSum r bM F + ccoordSum r bM F') := by
  obtain ⟨δ1, hδ1, K0, hK0, hcoef⟩ := coef_mul_family r hr rowCoef analyticAt_rowCoef
  obtain ⟨δ2, hδ2, K1, hK1, hrate⟩ := rate_mul_family r hr bM minkowski rowCoef
    analyticAt_rowCoef
  refine ⟨min δ1 δ2, by positivity, K0 + K1, by positivity,
    fun k i Q Q' Qi Qi' F F' Fi Fi' μ ν hdet hQ hQ' hF hF' hQm hQ'm hFm hF'm hsm => ?_⟩
  obtain ⟨P1, hP1y, hP1m, hP1s⟩ := hrate k Q hQm (hsm.trans (min_le_right _ _)) Q' hQ'm
    (cmp F μ ν) (memH_cmp hFm μ ν)
  obtain ⟨P2, hP2y, hP2m, hP2s⟩ := hcoef k Q hQm (hsm.trans (min_le_left _ _)) (cmp F' μ ν)
    (memH_cmp hF'm μ ν)
  have hU : ∀ y, minkowski + Q y ∈ detSet := hdet
  have hP : ∀ y, (P1 + P2) y = ((prodT (rowCoef k) (Q y) (Q' y) (F y μ ν) (F' y μ ν) : ℝ) : ℂ) := by
    intro y
    simp only [ContinuousMap.add_apply, hP1y, hP2y, cmp_apply, prodT]
    push_cast; ring
  set D : CT := ⟨fun y => ((prodDT (rowCoef k) (Q y) (Q' y) (Qi y) (Qi' y) (F y μ ν) (F' y μ ν)
      (Fi y μ ν) (Fi' y μ ν) : ℝ) : ℂ),
    Complex.continuous_ofReal.comp (continuous_prodDT (analyticOnNhd_rowCoef k) hU μ ν)⟩
  refine ⟨P1 + P2, D, hP, fun y => rfl, ?_, memH_add hP1m hP2m, ?_⟩
  · have hl := (isLineDeriv_prodT (A := rowCoef k) (fun y => analyticOnNhd_rowCoef k _ (hU y)) hQ
      hQ' (isLineDeriv_comp_apply hF μ ν) (isLineDeriv_comp_apply hF' μ ν)).ofReal
    have e : ⇑(P1 + P2) = fun y => ((prodT (rowCoef k) (Q y) (Q' y) (F y μ ν) (F' y μ ν) : ℝ) : ℂ) :=
      funext hP
    rw [e]
    exact hl
  · refine (sn_add_le' hP1m hP2m).trans ?_
    have h1 := sn_cmp_le_ccoordSum r F μ ν
    have h2 := sn_cmp_le_ccoordSum r F' μ ν
    have hQ'0 := ccoordSum_nonneg r bM Q'
    have hF0 := ccoordSum_nonneg r bM F
    have hF'0 := ccoordSum_nonneg r bM F'
    have e1 : K1 * ccoordSum r bM Q' * sn r ⇑(cmp F μ ν) ≤
        K1 * (ccoordSum r bM Q' * ccoordSum r bM F) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left h1 hQ'0) hK1
    have e2 : K0 * sn r ⇑(cmp F' μ ν) ≤ K0 * ccoordSum r bM F' :=
      mul_le_mul_of_nonneg_left h2 hK0
    have p1 := mul_nonneg hQ'0 hF0
    nlinarith

set_option maxHeartbeats 1000000 in
/-- **Lipschitz Moser bound for the compensator differential** `(w, w') ↦ D𝖦(w)[w']` on the grid. -/
theorem moser_lipschitz_compRate (r : ℕ) (hr : 2 ≤ r) :
    ∃ δ > 0, ∃ C ≥ 0, ∀ (N : ℕ) [NeZero N] (u w : Grid N → JetSpace × JetSpace),
      PeriodicGridSobolev.Moser.coordSum r bJP u ≤ δ →
      PeriodicGridSobolev.Moser.coordSum r bJP w ≤ δ → ∀ μ ν : Fin 4,
      PeriodicGridSobolev.sobNorm r
        (cx (fun x => fderiv ℝ (fun z : JetSpace => compensatorMap z μ ν) (u x).1 (u x).2) -
          cx (fun x => fderiv ℝ (fun z : JetSpace => compensatorMap z μ ν) (w x).1 (w x).2)) ≤
        C * PeriodicGridSobolev.Moser.coordSum r bJP (u - w) := by
  obtain ⟨δ, hδ, C, hC, h⟩ := uniformize (ι := Fin 4 × Fin 4) (fun k δ C => ∀ (N : ℕ) [NeZero N]
      (u w : Grid N → JetSpace × JetSpace), PeriodicGridSobolev.Moser.coordSum r bJP u ≤ δ →
      PeriodicGridSobolev.Moser.coordSum r bJP w ≤ δ →
      PeriodicGridSobolev.sobNorm r (fun x =>
        ((fderiv ℝ (fun z : JetSpace => compensatorMap z k.1 k.2) (0 + u x).1 (0 + u x).2 -
          fderiv ℝ (fun z : JetSpace => compensatorMap z k.1 k.2) (0 + w x).1 (0 + w x).2 : ℝ) : ℂ))
        ≤ C * PeriodicGridSobolev.Moser.coordSum r bJP (u - w))
    (fun k δ δ' C C' _ hδ' hC' hP N _ u w hu hw => (hP N u w (hu.trans hδ') (hw.trans hδ')).trans
      (mul_le_mul_of_nonneg_right hC' (PeriodicGridSobolev.Moser.coordSum_nonneg _ _ _)))
    (fun k => by
      obtain ⟨pp, R, hp⟩ := analyticAt_compensator_rate k.1 k.2
      obtain ⟨δ, hδ, C, hC, h⟩ := PeriodicGridSobolev.Moser.moser_lipschitz r hr bJP hp
      refine ⟨δ, hδ, C, hC, fun N _ u w hu hw => ?_⟩
      have := h N u w hu hw
      beta_reduce at this
      exact this)
  refine ⟨δ, hδ, C, hC, fun N _ u w hu hw μ ν => ?_⟩
  have h1 := h (μ, ν) N u w hu hw
  have e : (cx (fun x => fderiv ℝ (fun z : JetSpace => compensatorMap z μ ν) (u x).1 (u x).2) -
      cx (fun x => fderiv ℝ (fun z : JetSpace => compensatorMap z μ ν) (w x).1 (w x).2)) =
      fun x => ((fderiv ℝ (fun z : JetSpace => compensatorMap z μ ν) (0 + u x).1 (0 + u x).2 -
        fderiv ℝ (fun z : JetSpace => compensatorMap z μ ν) (0 + w x).1 (0 + w x).2 : ℝ) : ℂ) := by
    funext x
    simp only [cx, Pi.sub_apply, zero_add, Complex.ofReal_sub]
  rw [e]
  exact h1

end ErrBounds

section ErrBound

variable {N : ℕ} [NeZero N]

theorem memH_interpRec_all (k : ℕ) (u : Grid N → MetricRec) :
    ∀ m, MemH k ⇑(ccoord bM (interpRec u) m) := fun m => (memH_interpRec k u m).1

theorem memH_interpD_all (k : ℕ) (u : Grid N → MetricRec) (i : Fin 3) :
    ∀ m, MemH k ⇑(ccoord bM (interpD u i) m) := by
  intro m; rw [ccoord_bM]; exact (memH_cmp_reField k _ m.1 m.2).1

theorem memH_interpDD_all (k : ℕ) (u : Grid N → MetricRec) (i j : Fin 3) :
    ∀ m, MemH k ⇑(ccoord bM (interpDD u i j) m) := by
  intro m; rw [ccoord_bM]; exact (memH_cmp_reField k _ m.1 m.2).1

theorem ccoordSum_interpD_le (k : ℕ) (u : Grid N → MetricRec) (i : Fin 3) :
    ccoordSum k bM (interpD u i) ≤ ccoordSum (k + 1) bM (interpRec u) :=
  (ccoordSum_deriv_le ((isContJet_interp u u).dQ i) (memH_interpRec_all (k + 1) u)).2

/-- The continuum size of an interpolant from componentwise grid bounds. -/
theorem ccoordSum_interpRec_of (k : ℕ) (u : Grid N → MetricRec) {M : ℝ}
    (h : ∀ μ ν, PeriodicGridSobolev.sobNorm k (cx (comp u μ ν)) ≤ M) :
    ccoordSum k bM (interpRec u) ≤ 16 * Real.sqrt (pc k) * M := by
  unfold ccoordSum
  calc ∑ m, sn k ⇑(ccoord bM (interpRec u) m)
      ≤ ∑ _m : Σ _ : Fin 4, Fin 4, Real.sqrt (pc k) * M :=
        sum_le_sum fun m _ => (memH_interpRec k u m).2.trans
          (mul_le_mul_of_nonneg_left (h _ _) (Real.sqrt_nonneg _))
    _ = 16 * Real.sqrt (pc k) * M := by simp; ring

/-- The grid coordinate size from componentwise bounds. -/
theorem coordSum_of (k : ℕ) (u : Grid N → MetricRec) {M : ℝ}
    (h : ∀ μ ν, PeriodicGridSobolev.sobNorm k (cx (comp u μ ν)) ≤ M) :
    PeriodicGridSobolev.Moser.coordSum k bM u ≤ 16 * M := by
  have := coordSum_le_card k bM u M fun m => by rw [coordArr_bM]; exact h _ _
  simpa using this

theorem smp_cmp_interpRec (u : Grid N → MetricRec) (μ ν : Fin 4) :
    PeriodicGridSobolev.Sampling.sample N ⇑(cmp (interpRec u) μ ν) = cx (comp u μ ν) := by
  rw [← cx_comp_sampleRec, sampleRec_interpRec]

/-- `Σ_k ‖𝒮_h ∂ᵢF_k - D_i⁺ 𝒮_h F_k‖_{r,h} ≤ C h ‖F‖_{H^{r+2}}` for interpolants
(the site-jet difference of the compensator). -/
theorem coordSum_interpD_fwd_le (r : ℕ) (hr : 2 ≤ r) :
    ∃ C ≥ 0, ∀ (N : ℕ) [NeZero N] (u : Grid N → MetricRec) (i : Fin 3),
      PeriodicGridSobolev.Moser.coordSum r bM
        (fun x => interpD u i (PeriodicGridSobolev.samplePt x) - fwd (N : ℝ)⁻¹ (e N) i u x) ≤
        C * (N : ℝ)⁻¹ * ccoordSum (r + 2) bM (interpRec u) := by
  obtain ⟨Cp, hCp, hDp⟩ := sample_Dp_sub_le r hr
  refine ⟨Cp, hCp, fun N _ u i => ?_⟩
  unfold PeriodicGridSobolev.Moser.coordSum
  have hk : ∀ k : Σ _ : Fin 4, Fin 4, PeriodicGridSobolev.sobNorm r
      (PeriodicGridSobolev.Moser.coordArr bM
        (fun x => interpD u i (PeriodicGridSobolev.samplePt x) - fwd (N : ℝ)⁻¹ (e N) i u x) k) ≤
      Cp * (N : ℝ)⁻¹ * sn (r + 2) ⇑(cmp (interpRec u) k.1 k.2) := by
    intro k
    have e1 : PeriodicGridSobolev.Moser.coordArr bM
        (fun x => interpD u i (PeriodicGridSobolev.samplePt x) - fwd (N : ℝ)⁻¹ (e N) i u x) k =
        PeriodicGridSobolev.Sampling.sample N ⇑(cmp (interpD u i) k.1 k.2) -
          PeriodicGridSobolev.Dp i (PeriodicGridSobolev.Sampling.sample N
            ⇑(cmp (interpRec u) k.1 k.2)) := by
      rw [smp_cmp_interpRec]
      have := PeriodicGridSobolev.Moser.coordArr_sub bM
        (fun x : Grid N => interpD u i (PeriodicGridSobolev.samplePt x))
        (fun x => fwd (N : ℝ)⁻¹ (e N) i u x) k
      rw [show (fun x => interpD u i (PeriodicGridSobolev.samplePt x) - fwd (N : ℝ)⁻¹ (e N) i u x) =
        (fun x : Grid N => interpD u i (PeriodicGridSobolev.samplePt x)) -
          (fun x => fwd (N : ℝ)⁻¹ (e N) i u x) from rfl, this, coordArr_bM, coordArr_bM, comp_fwd,
        cx_Dp]
      rfl
    rw [e1, sobNorm_sub_comm]
    exact hDp N i (cmp (interpRec u) k.1 k.2) (cmp (interpD u i) k.1 k.2)
      (isLineDeriv_cmp ((isContJet_interp u u).dQ i) k.1 k.2)
      (memH_cmp (memH_interpRec_all (r + 2) u) k.1 k.2)
  calc ∑ k, PeriodicGridSobolev.sobNorm r (PeriodicGridSobolev.Moser.coordArr bM
        (fun x => interpD u i (PeriodicGridSobolev.samplePt x) - fwd (N : ℝ)⁻¹ (e N) i u x) k)
      ≤ ∑ k : Σ _ : Fin 4, Fin 4, Cp * (N : ℝ)⁻¹ * sn (r + 2) ⇑(cmp (interpRec u) k.1 k.2) :=
        sum_le_sum fun k _ => hk k
    _ = Cp * (N : ℝ)⁻¹ * ccoordSum (r + 2) bM (interpRec u) := by
        rw [← mul_sum]; unfold ccoordSum; simp [ccoord_bM]

end ErrBound

set_option maxHeartbeats 8000000 in
/-- **The differentiated consistency error is `O(h)` in `H^{s-3}_h`** (`s ≥ 5`).  For every
`K ≥ 0` there are `δ, C`, independent of the mesh, such that for every symmetric record
`X = (q, v)` with `‖X‖_{X^s_h} ≤ δ` and every record `A` with `‖A_{μν}‖_{s-1,h} ≤ K ‖X‖`
(the writer acceleration), the derivative of the consistency error in the direction
`(q, v) ↦ (v, A)` (`errDeriv q v v A`) satisfies `‖·‖_{s-3,h} ≤ C h ‖X‖_{X^s_h}`. -/
theorem errDeriv_bound (s : ℕ) (hs : 5 ≤ s) (K : ℝ) (hK : 0 ≤ K) :
    ∃ δ > 0, ∃ C ≥ 0, ∀ (N : ℕ) [NeZero N] (q v A : Grid N → MetricRec), IsSymRec q →
      IsSymRec v → Xnorm s q v ≤ δ →
      (∀ μ ν, PeriodicGridSobolev.sobNorm (s - 1) (cx (comp A μ ν)) ≤ K * Xnorm s q v) →
      ∀ μ ν, PeriodicGridSobolev.sobNorm (s - 3) (errDeriv q v v A μ ν) ≤
        C * (N : ℝ)⁻¹ * Xnorm s q v := by
  obtain ⟨r, rfl⟩ : ∃ r, s = r + 3 := ⟨s - 3, by omega⟩
  have hr : 2 ≤ r := by omega
  have e1 : r + 3 - 1 = r + 2 := by omega
  have e3 : r + 3 - 3 = r := by omega
  rw [e1, e3]
  obtain ⟨δ0, hδ0, K00, hK00, hcore⟩ := reduced_residual_of_rows (r + 3) (by omega)
  obtain ⟨δF, hδF, CF, hCF, hfields⟩ := prodT_fields (r + 2) (by omega)
  obtain ⟨Cm, hCm, hDm⟩ := sample_Dm_sub_le r hr
  obtain ⟨C0, hC0, hD0⟩ := sample_D0_sub_le r hr
  obtain ⟨Cp1, hCp1, hDp1⟩ := sample_Dp_sub_le (r + 1) (by omega)
  obtain ⟨Cf, hCf, hfwd⟩ := coordSum_interpD_fwd_le r hr
  obtain ⟨δr1, hδr1, Cr1, hCr1, hmr1⟩ := moser_rate_coefficients (r + 1) (by omega)
  obtain ⟨δr0, hδr0, Cr0, hCr0, hmr0⟩ := moser_rate_coefficients r hr
  obtain ⟨δc1, hδc1, Cc1, hCc1, hmc1⟩ := moser_coefficients (r + 1) (by omega)
  obtain ⟨δc0, hδc0, Cc0, hCc0, hmc0⟩ := moser_coefficients r hr
  obtain ⟨δL, hδL, CL, hCL, hLip⟩ := moser_lipschitz_compRate r hr
  obtain ⟨Cs, hCs, hsamp⟩ := coordSum_sample_le (E := MetricRec) (ι := Σ _ : Fin 4, Fin 4) r hr
  set A0 := PeriodicGridSobolev.Moser.algConst r
  set A1 := PeriodicGridSobolev.Moser.algConst (r + 1)
  have hA0 := PeriodicGridSobolev.Moser.algConst_pos r
  have hA1 := PeriodicGridSobolev.Moser.algConst_pos (r + 1)
  set σ : ℝ := 16 * (Real.sqrt (pc r) + Real.sqrt (pc (r + 1)) + Real.sqrt (pc (r + 2)) +
    Real.sqrt (pc (r + 3)) + Real.sqrt (pc (r + 4))) + 16 with hσdef
  have hσ0 : 0 ≤ σ := by positivity
  set Mb : ℝ := 200 + 64 * K + 6 * Cs * σ
  have hMb : 0 ≤ Mb := by positivity
  set δ : ℝ := min (min (min δ0 1) (δF / (σ + 1)))
    (min (min (δr1 / 33) (δr0 / 33)) (min (min (δc1 / 17) (1 / (17 * (Cc1 + 1))))
      (min (min (δc0 / 17) (1 / (17 * (Cc0 + 1)))) (δL / (Mb + 1)))))
  have hδ : 0 < δ := by positivity
  set Ctot : ℝ := 9 * (Cm * CF * (σ ^ 2 + σ) + (32 * A1 * Cr1 * Cp1 * σ + (A1 + 1) * Cp1 * σ)) +
    3 * (32 * A0 * Cr0 * C0 * σ + (A0 + 1) * C0 * σ * K) + 3 * (C0 * CF * (σ ^ 2 + σ * K)) +
    CL * (6 * Cf * σ)
  refine ⟨δ, hδ, Ctot, by positivity, fun N _ q v A hq hv hX hAb μ ν => ?_⟩
  set X := Xnorm (r + 3) q v
  set h : ℝ := (N : ℝ)⁻¹
  have hh : 0 ≤ h := by positivity
  have hX0 : 0 ≤ X := Xnorm_nonneg _ _ _
  have hX1 : X ≤ 1 := hX.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hXδ0 : X ≤ δ0 := hX.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hXF : X ≤ δF / (σ + 1) := hX.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hXr1 : X ≤ δr1 / 33 :=
    hX.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hXr0 : X ≤ δr0 / 33 :=
    hX.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hXc1 : X ≤ δc1 / 17 := hX.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_left _ _).trans (min_le_left _ _))))
  have hXc1' : X ≤ 1 / (17 * (Cc1 + 1)) := hX.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))))
  have hXc0 : X ≤ δc0 / 17 := hX.trans ((min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))))
  have hXc0' : X ≤ 1 / (17 * (Cc0 + 1)) := hX.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_left _ _).trans
      (min_le_right _ _)))))
  have hXL : X ≤ δL / (Mb + 1) := hX.trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hdet := (hcore N q v 0 hq hv (fun _ _ _ => rfl) hXδ0).1
  -- sizes of the interpolants
  have hsq : ∀ k, r ≤ k → k ≤ r + 4 → Real.sqrt (pc k) * 16 ≤ σ := by
    intro k hk1 hk
    have h0 := Real.sqrt_nonneg (pc r)
    have h1 := Real.sqrt_nonneg (pc (r + 1))
    have h2 := Real.sqrt_nonneg (pc (r + 2))
    have h3 := Real.sqrt_nonneg (pc (r + 3))
    have h4 := Real.sqrt_nonneg (pc (r + 4))
    have hk' : k = r ∨ k = r + 1 ∨ k = r + 2 ∨ k = r + 3 ∨ k = r + 4 := by omega
    rcases hk' with rfl | rfl | rfl | rfl | rfl <;> (simp only [hσdef]; linarith)
  have cq : ∀ k, r ≤ k → k ≤ r + 4 → ccoordSum k bM (interpRec q) ≤ σ * X := by
    intro k hk1 hk
    refine (ccoordSum_interpRec_le k (r + 3) hq v hk).trans ?_
    have := hsq k hk1 (by omega)
    nlinarith
  have cv : ∀ k, r ≤ k → k ≤ r + 3 → ccoordSum k bM (interpRec v) ≤ σ * X := by
    intro k hk1 hk
    refine (ccoordSum_interpRec_v_le k (r + 3) q hv hk).trans ?_
    have := hsq k hk1 (by omega)
    nlinarith
  have cA : ∀ k, r ≤ k → k ≤ r + 2 → ccoordSum k bM (interpRec A) ≤ σ * (K * X) := by
    intro k hk1 hk
    refine (ccoordSum_interpRec_of k A fun μ ν =>
      (PeriodicGridSobolev.Moser.sobNorm_mono hk _).trans (hAb μ ν)).trans ?_
    have := hsq k hk1 (by omega)
    have : 0 ≤ K * X := mul_nonneg hK hX0
    nlinarith
  have cqd : ∀ k j, r ≤ k → k ≤ r + 3 → ccoordSum k bM (interpD q j) ≤ σ * X :=
    fun k j hk1 hk => (ccoordSum_interpD_le k q j).trans (cq (k + 1) (by omega) (by omega))
  have cvd : ∀ k j, r ≤ k → k ≤ r + 2 → ccoordSum k bM (interpD v j) ≤ σ * X :=
    fun k j hk1 hk => (ccoordSum_interpD_le k v j).trans (cv (k + 1) (by omega) (by omega))
  have gq : ∀ k, k ≤ r + 4 → PeriodicGridSobolev.Moser.coordSum k bM q ≤ 16 * X := fun k hk =>
    coordSum_bM_q_le (r + 3) hq v hk
  have gv : ∀ k, k ≤ r + 3 → PeriodicGridSobolev.Moser.coordSum k bM v ≤ 16 * X := fun k hk =>
    coordSum_bM_v_le (r + 3) q hv hk
  have gA : PeriodicGridSobolev.Moser.coordSum r bM A ≤ 16 * (K * X) :=
    coordSum_of r A fun μ ν => (PeriodicGridSobolev.Moser.sobNorm_mono (by omega) _).trans (hAb μ ν)
  have hsmF : ccoordSum (r + 2) bM (interpRec q) ≤ δF := by
    refine (cq (r + 2) (by omega) (by omega)).trans ?_
    rw [le_div_iff₀ (by positivity)] at hXF
    nlinarith
  have hσX : σ * X * (σ * X) ≤ σ ^ 2 * X := by
    have := mul_le_mul_of_nonneg_left hX1 (sq_nonneg σ)
    nlinarith
  -- (1) the flux products
  have hE1 : ∀ i j, PeriodicGridSobolev.sobNorm r
      (PeriodicGridSobolev.Sampling.sample N (fun y => ((prodDT (harmC i j) (interpRec q y)
          (interpRec v y) (interpD q i y) (interpD v i y) (interpD q j y μ ν) (interpD v j y μ ν)
          (interpDD q i j y μ ν) (interpDD v i j y μ ν) : ℝ) : ℂ)) -
        PeriodicGridSobolev.Dm i (PeriodicGridSobolev.Sampling.sample N (fun y => ((prodT
          (harmC i j) (interpRec q y) (interpRec v y) (interpD q j y μ ν) (interpD v j y μ ν) :
            ℝ) : ℂ)))) ≤ Cm * CF * (σ ^ 2 + σ) * h * X := by
    intro i j
    obtain ⟨P, D, hPy, hDy, hPD, hPm, hPs⟩ := hfields (Sum.inr (Sum.inr (i, j))) i (interpRec q)
      (interpRec v) (interpD q i) (interpD v i) (interpD q j) (interpD v j) (interpDD q i j)
      (interpDD v i j) μ ν hdet ((isContJet_interp q v).dQ i) ((isContJet_interp v v).dQ i)
      ((isContJet_interp q v).dQd i j) ((isContJet_interp v v).dQd i j)
      (memH_interpRec_all _ q) (memH_interpRec_all _ v) (memH_interpD_all _ q j)
      (memH_interpD_all _ v j) hsmF
    have eP : (fun y => ((prodT (harmC i j) (interpRec q y) (interpRec v y) (interpD q j y μ ν)
        (interpD v j y μ ν) : ℝ) : ℂ)) = ⇑P := funext fun y => (hPy y).symm
    have eD : (fun y => ((prodDT (harmC i j) (interpRec q y) (interpRec v y) (interpD q i y)
        (interpD v i y) (interpD q j y μ ν) (interpD v j y μ ν) (interpDD q i j y μ ν)
        (interpDD v i j y μ ν) : ℝ) : ℂ)) = ⇑D := funext fun y => (hDy y).symm
    rw [eP, eD, sobNorm_sub_comm]
    refine (hDm N i P D hPD hPm).trans ?_
    have hb : sn (r + 2) ⇑P ≤ CF * ((σ ^ 2 + σ) * X) := by
      refine hPs.trans (mul_le_mul_of_nonneg_left ?_ hCF)
      have a1 := cv (r + 2) (by omega) (by omega)
      have a2 := cqd (r + 2) j (by omega) (by omega)
      have a3 := cvd (r + 2) j (by omega) (by omega)
      have a4 := ccoordSum_nonneg (r + 2) bM (interpRec v)
      have a5 := ccoordSum_nonneg (r + 2) bM (interpD q j)
      have : ccoordSum (r + 2) bM (interpRec v) * ccoordSum (r + 2) bM (interpD q j) ≤
          σ * X * (σ * X) := mul_le_mul a1 a2 a5 (by positivity)
      nlinarith
    calc Cm * (N : ℝ)⁻¹ * sn (r + 2) ⇑P ≤ Cm * (N : ℝ)⁻¹ * (CF * ((σ ^ 2 + σ) * X)) := by gcongr
      _ = Cm * CF * (σ ^ 2 + σ) * h * X := by ring
  -- (4) the transport products
  have hE4 : ∀ i, PeriodicGridSobolev.sobNorm r
      (PeriodicGridSobolev.Sampling.sample N (fun y => ((prodDT (harmB i) (interpRec q y)
          (interpRec v y) (interpD q i y) (interpD v i y) (interpRec v y μ ν) (interpRec A y μ ν)
          (interpD v i y μ ν) (interpD A i y μ ν) : ℝ) : ℂ)) -
        PeriodicGridSobolev.D0 i (PeriodicGridSobolev.Sampling.sample N (fun y => ((prodT
          (harmB i) (interpRec q y) (interpRec v y) (interpRec v y μ ν) (interpRec A y μ ν) :
            ℝ) : ℂ)))) ≤ C0 * CF * (σ ^ 2 + σ * K) * h * X := by
    intro i
    obtain ⟨P, D, hPy, hDy, hPD, hPm, hPs⟩ := hfields (Sum.inr (Sum.inl i)) i (interpRec q)
      (interpRec v) (interpD q i) (interpD v i) (interpRec v) (interpRec A) (interpD v i)
      (interpD A i) μ ν hdet ((isContJet_interp q v).dQ i) ((isContJet_interp v v).dQ i)
      ((isContJet_interp v v).dQ i) ((isContJet_interp A A).dQ i)
      (memH_interpRec_all _ q) (memH_interpRec_all _ v) (memH_interpRec_all _ v)
      (memH_interpRec_all _ A) hsmF
    have eP : (fun y => ((prodT (harmB i) (interpRec q y) (interpRec v y) (interpRec v y μ ν)
        (interpRec A y μ ν) : ℝ) : ℂ)) = ⇑P := funext fun y => (hPy y).symm
    have eD : (fun y => ((prodDT (harmB i) (interpRec q y) (interpRec v y) (interpD q i y)
        (interpD v i y) (interpRec v y μ ν) (interpRec A y μ ν) (interpD v i y μ ν)
        (interpD A i y μ ν) : ℝ) : ℂ)) = ⇑D := funext fun y => (hDy y).symm
    rw [eP, eD, sobNorm_sub_comm]
    refine (hD0 N i P D hPD hPm).trans ?_
    have hb : sn (r + 2) ⇑P ≤ CF * ((σ ^ 2 + σ * K) * X) := by
      refine hPs.trans (mul_le_mul_of_nonneg_left ?_ hCF)
      have a1 := cv (r + 2) (by omega) (by omega)
      have a3 := cA (r + 2) (by omega) le_rfl
      have a4 := ccoordSum_nonneg (r + 2) bM (interpRec v)
      have : ccoordSum (r + 2) bM (interpRec v) * ccoordSum (r + 2) bM (interpRec v) ≤
          σ * X * (σ * X) := mul_le_mul a1 a1 a4 (by positivity)
      nlinarith
    calc C0 * (N : ℝ)⁻¹ * sn (r + 2) ⇑P ≤ C0 * (N : ℝ)⁻¹ * (CF * ((σ ^ 2 + σ * K) * X)) := by
          gcongr
      _ = C0 * CF * (σ ^ 2 + σ * K) * h * X := by ring
  -- grid coefficient bounds
  have hqv1 : PeriodicGridSobolev.Moser.coordSum (r + 1) bM q +
      PeriodicGridSobolev.Moser.coordSum (r + 1) bM v ≤ 32 * X := by
    have := gq (r + 1) (by omega); have := gv (r + 1) (by omega); linarith
  have hqv0 : PeriodicGridSobolev.Moser.coordSum r bM q +
      PeriodicGridSobolev.Moser.coordSum r bM v ≤ 32 * X := by
    have := gq r (by omega); have := gv r (by omega); linarith
  obtain ⟨-, hcdot1, -⟩ := hmr1 N q v (hqv1.trans (by linarith))
  obtain ⟨-, -, hbdot0⟩ := hmr0 N q v (hqv0.trans (by linarith))
  obtain ⟨-, -, hcC1, -⟩ := hmc1 N q ((gq (r + 1) (by omega)).trans (by linarith))
  obtain ⟨-, -, -, hcB0⟩ := hmc0 N q ((gq r (by omega)).trans (by linarith))
  have hcoefC : ∀ i j, PeriodicGridSobolev.sobNorm (r + 1)
      (cx (cArr q i j) - fun _ => ((if i = j then 1 else 0 : ℝ) : ℂ)) ≤ 1 := by
    intro i j
    refine (hcC1 i j).trans ?_
    have := gq (r + 1) (by omega)
    rw [le_div_iff₀ (by positivity)] at hXc1'
    have : Cc1 * PeriodicGridSobolev.Moser.coordSum (r + 1) bM q ≤ Cc1 * (16 * X) :=
      mul_le_mul_of_nonneg_left this hCc1
    nlinarith
  have hcoefB : ∀ i, PeriodicGridSobolev.sobNorm r (cx (bArr q i) - fun _ => (0 : ℂ)) ≤ 1 := by
    intro i
    refine (hcB0 i).trans ?_
    have := gq r (by omega)
    rw [le_div_iff₀ (by positivity)] at hXc0'
    have : Cc0 * PeriodicGridSobolev.Moser.coordSum r bM q ≤ Cc0 * (16 * X) :=
      mul_le_mul_of_nonneg_left this hCc0
    nlinarith
  have hdij : ∀ i j : Fin 3, ‖((if i = j then 1 else 0 : ℝ) : ℂ)‖ ≤ 1 := by
    intro i j; split_ifs <;> simp
  -- (2) the flux interpolation errors
  have hYu : ∀ (u : Grid N → MetricRec) j, PeriodicGridSobolev.sobNorm (r + 1)
      (PeriodicGridSobolev.Sampling.sample N ⇑(cmp (interpD u j) μ ν) -
        PeriodicGridSobolev.Dp j (cx (comp u μ ν))) ≤
      Cp1 * h * ccoordSum (r + 3) bM (interpRec u) := by
    intro u j
    rw [← smp_cmp_interpRec, sobNorm_sub_comm]
    refine (hDp1 N j (cmp (interpRec u) μ ν) (cmp (interpD u j) μ ν)
      (isLineDeriv_cmp ((isContJet_interp u u).dQ j) μ ν)
      (memH_cmp (memH_interpRec_all _ u) μ ν)).trans ?_
    exact mul_le_mul_of_nonneg_left (sn_cmp_le_ccoordSum _ _ _ _) (by positivity)
  have hE2 : ∀ i j, PeriodicGridSobolev.sobNorm r (PeriodicGridSobolev.Dm i
      (cx (fun x => fderiv ℝ (harmC i j) (minkowski + q x) (v x)) *
          (PeriodicGridSobolev.Sampling.sample N ⇑(cmp (interpD q j) μ ν) -
            PeriodicGridSobolev.Dp j (cx (comp q μ ν))) +
        cx (cArr q i j) * (PeriodicGridSobolev.Sampling.sample N ⇑(cmp (interpD v j) μ ν) -
          PeriodicGridSobolev.Dp j (cx (comp v μ ν))))) ≤
      (32 * A1 * Cr1 * Cp1 * σ + (A1 + 1) * Cp1 * σ) * h * X := by
    intro i j
    refine (PeriodicGridSobolev.CommutedRow.sobNorm_Dm_le r i _).trans ?_
    refine (PeriodicGridSobolev.Moser.sobNorm_add_le _ _ _).trans ?_
    have t1 := PeriodicGridSobolev.Moser.sobNorm_mul_le (r + 1) (by omega)
      (cx (fun x => fderiv ℝ (harmC i j) (minkowski + q x) (v x)))
      (PeriodicGridSobolev.Sampling.sample N ⇑(cmp (interpD q j) μ ν) -
        PeriodicGridSobolev.Dp j (cx (comp q μ ν)))
    have t2 := sobNorm_coef_mul_le (r + 1) (by omega) (cx (cArr q i j))
      (PeriodicGridSobolev.Sampling.sample N ⇑(cmp (interpD v j) μ ν) -
        PeriodicGridSobolev.Dp j (cx (comp v μ ν))) _ (hdij i j) (hcoefC i j)
    have b1 : PeriodicGridSobolev.sobNorm (r + 1)
        (cx (fun x => fderiv ℝ (harmC i j) (minkowski + q x) (v x))) ≤ Cr1 * (32 * X) :=
      (hcdot1 i j).trans (mul_le_mul_of_nonneg_left hqv1 hCr1)
    have b2 := (hYu q j).trans (mul_le_mul_of_nonneg_left (cq (r + 3) (by omega) (by omega))
      (by positivity : (0 : ℝ) ≤ Cp1 * h))
    have b3 := (hYu v j).trans (mul_le_mul_of_nonneg_left (cv (r + 3) (by omega) le_rfl)
      (by positivity : (0 : ℝ) ≤ Cp1 * h))
    have n1 := PeriodicGridSobolev.Moser.sobNorm_nonneg (r + 1)
      (cx (fun x => fderiv ℝ (harmC i j) (minkowski + q x) (v x)))
    have n2 := PeriodicGridSobolev.Moser.sobNorm_nonneg (r + 1)
      (PeriodicGridSobolev.Sampling.sample N ⇑(cmp (interpD q j) μ ν) -
        PeriodicGridSobolev.Dp j (cx (comp q μ ν)))
    have p1 : A1 * PeriodicGridSobolev.sobNorm (r + 1)
        (cx (fun x => fderiv ℝ (harmC i j) (minkowski + q x) (v x))) *
        PeriodicGridSobolev.sobNorm (r + 1)
          (PeriodicGridSobolev.Sampling.sample N ⇑(cmp (interpD q j) μ ν) -
            PeriodicGridSobolev.Dp j (cx (comp q μ ν))) ≤
        A1 * (Cr1 * (32 * X)) * (Cp1 * h * (σ * X)) := by
      gcongr
    have p2 : (A1 + 1) * PeriodicGridSobolev.sobNorm (r + 1)
        (PeriodicGridSobolev.Sampling.sample N ⇑(cmp (interpD v j) μ ν) -
          PeriodicGridSobolev.Dp j (cx (comp v μ ν))) ≤ (A1 + 1) * (Cp1 * h * (σ * X)) := by
      gcongr
    have hXX : X * X ≤ X := by nlinarith
    have p3 : A1 * (Cr1 * (32 * X)) * (Cp1 * h * (σ * X)) ≤ 32 * A1 * Cr1 * Cp1 * σ * h * X := by
      have : 0 ≤ 32 * A1 * Cr1 * Cp1 * σ * h := by positivity
      have e : A1 * (Cr1 * (32 * X)) * (Cp1 * h * (σ * X)) =
          32 * A1 * Cr1 * Cp1 * σ * h * (X * X) := by ring
      rw [e]
      exact mul_le_mul_of_nonneg_left hXX this
    calc _ ≤ A1 * PeriodicGridSobolev.sobNorm (r + 1)
          (cx (fun x => fderiv ℝ (harmC i j) (minkowski + q x) (v x))) *
          PeriodicGridSobolev.sobNorm (r + 1)
            (PeriodicGridSobolev.Sampling.sample N ⇑(cmp (interpD q j) μ ν) -
              PeriodicGridSobolev.Dp j (cx (comp q μ ν))) +
          (A1 + 1) * PeriodicGridSobolev.sobNorm (r + 1)
            (PeriodicGridSobolev.Sampling.sample N ⇑(cmp (interpD v j) μ ν) -
              PeriodicGridSobolev.Dp j (cx (comp v μ ν))) := add_le_add t1 t2
      _ ≤ 32 * A1 * Cr1 * Cp1 * σ * h * X + (A1 + 1) * (Cp1 * h * (σ * X)) := by linarith
      _ = (32 * A1 * Cr1 * Cp1 * σ + (A1 + 1) * Cp1 * σ) * h * X := by ring
  -- (3) the transport interpolation errors
  have hZu : ∀ (u : Grid N → MetricRec) i, PeriodicGridSobolev.sobNorm r
      (PeriodicGridSobolev.Sampling.sample N ⇑(cmp (interpD u i) μ ν) -
        PeriodicGridSobolev.D0 i (cx (comp u μ ν))) ≤
      C0 * h * ccoordSum (r + 2) bM (interpRec u) := by
    intro u i
    rw [← smp_cmp_interpRec, sobNorm_sub_comm]
    refine (hD0 N i (cmp (interpRec u) μ ν) (cmp (interpD u i) μ ν)
      (isLineDeriv_cmp ((isContJet_interp u u).dQ i) μ ν)
      (memH_cmp (memH_interpRec_all _ u) μ ν)).trans ?_
    exact mul_le_mul_of_nonneg_left (sn_cmp_le_ccoordSum _ _ _ _) (by positivity)
  have hE3 : ∀ i, PeriodicGridSobolev.sobNorm r
      (cx (fun x => fderiv ℝ (harmB i) (minkowski + q x) (v x)) *
          (PeriodicGridSobolev.Sampling.sample N ⇑(cmp (interpD v i) μ ν) -
            PeriodicGridSobolev.D0 i (cx (comp v μ ν))) +
        cx (bArr q i) * (PeriodicGridSobolev.Sampling.sample N ⇑(cmp (interpD A i) μ ν) -
          PeriodicGridSobolev.D0 i (cx (comp A μ ν)))) ≤
      (32 * A0 * Cr0 * C0 * σ + (A0 + 1) * C0 * σ * K) * h * X := by
    intro i
    refine (PeriodicGridSobolev.Moser.sobNorm_add_le _ _ _).trans ?_
    have t1 := PeriodicGridSobolev.Moser.sobNorm_mul_le r hr
      (cx (fun x => fderiv ℝ (harmB i) (minkowski + q x) (v x)))
      (PeriodicGridSobolev.Sampling.sample N ⇑(cmp (interpD v i) μ ν) -
        PeriodicGridSobolev.D0 i (cx (comp v μ ν)))
    have t2 := sobNorm_coef_mul_le r hr (cx (bArr q i))
      (PeriodicGridSobolev.Sampling.sample N ⇑(cmp (interpD A i) μ ν) -
        PeriodicGridSobolev.D0 i (cx (comp A μ ν))) 0 (by simp) (hcoefB i)
    have b1 : PeriodicGridSobolev.sobNorm r
        (cx (fun x => fderiv ℝ (harmB i) (minkowski + q x) (v x))) ≤ Cr0 * (32 * X) :=
      (hbdot0 i).trans (mul_le_mul_of_nonneg_left hqv0 hCr0)
    have b2 := (hZu v i).trans (mul_le_mul_of_nonneg_left (cv (r + 2) (by omega) (by omega))
      (by positivity : (0 : ℝ) ≤ C0 * h))
    have b3 := (hZu A i).trans (mul_le_mul_of_nonneg_left (cA (r + 2) (by omega) le_rfl)
      (by positivity : (0 : ℝ) ≤ C0 * h))
    have n2 := PeriodicGridSobolev.Moser.sobNorm_nonneg r
      (PeriodicGridSobolev.Sampling.sample N ⇑(cmp (interpD v i) μ ν) -
        PeriodicGridSobolev.D0 i (cx (comp v μ ν)))
    have p1 : A0 * PeriodicGridSobolev.sobNorm r
        (cx (fun x => fderiv ℝ (harmB i) (minkowski + q x) (v x))) *
        PeriodicGridSobolev.sobNorm r
          (PeriodicGridSobolev.Sampling.sample N ⇑(cmp (interpD v i) μ ν) -
            PeriodicGridSobolev.D0 i (cx (comp v μ ν))) ≤
        A0 * (Cr0 * (32 * X)) * (C0 * h * (σ * X)) := by
      gcongr
    have hXX : X * X ≤ X := by nlinarith
    have p3 : A0 * (Cr0 * (32 * X)) * (C0 * h * (σ * X)) ≤ 32 * A0 * Cr0 * C0 * σ * h * X := by
      have : 0 ≤ 32 * A0 * Cr0 * C0 * σ * h := by positivity
      have e : A0 * (Cr0 * (32 * X)) * (C0 * h * (σ * X)) =
          32 * A0 * Cr0 * C0 * σ * h * (X * X) := by ring
      rw [e]
      exact mul_le_mul_of_nonneg_left hXX this
    have p2 : (A0 + 1) * PeriodicGridSobolev.sobNorm r
        (PeriodicGridSobolev.Sampling.sample N ⇑(cmp (interpD A i) μ ν) -
          PeriodicGridSobolev.D0 i (cx (comp A μ ν))) ≤ (A0 + 1) * (C0 * h * (σ * (K * X))) := by
      gcongr
    calc _ ≤ A0 * PeriodicGridSobolev.sobNorm r
          (cx (fun x => fderiv ℝ (harmB i) (minkowski + q x) (v x))) *
          PeriodicGridSobolev.sobNorm r
            (PeriodicGridSobolev.Sampling.sample N ⇑(cmp (interpD v i) μ ν) -
              PeriodicGridSobolev.D0 i (cx (comp v μ ν))) +
          (A0 + 1) * PeriodicGridSobolev.sobNorm r
            (PeriodicGridSobolev.Sampling.sample N ⇑(cmp (interpD A i) μ ν) -
              PeriodicGridSobolev.D0 i (cx (comp A μ ν))) := add_le_add t1 t2
      _ ≤ 32 * A0 * Cr0 * C0 * σ * h * X + (A0 + 1) * (C0 * h * (σ * (K * X))) := by linarith
      _ = (32 * A0 * Cr0 * C0 * σ + (A0 + 1) * C0 * σ * K) * h * X := by ring
  -- (5) the compensator
  have hE5 : PeriodicGridSobolev.sobNorm r
      (cx (fun x => fderiv ℝ (fun w : JetSpace => compensatorMap w μ ν)
          (q x, v x, fun i => interpD q i (PeriodicGridSobolev.samplePt x))
          (v x, A x, fun i => interpD v i (PeriodicGridSobolev.samplePt x))) -
        cx (fun x => fderiv ℝ (fun w : JetSpace => compensatorMap w μ ν) (jetArr q v x)
          (jetArr v A x))) ≤ CL * (6 * Cf * σ) * h * X := by
    set u1 : Grid N → JetSpace × JetSpace := fun x =>
      (((q x, v x, fun i => interpD q i (PeriodicGridSobolev.samplePt x)) : JetSpace),
        ((v x, A x, fun i => interpD v i (PeriodicGridSobolev.samplePt x)) : JetSpace))
    set u2 : Grid N → JetSpace × JetSpace := fun x => (jetArr q v x, jetArr v A x)
    have hsd : ∀ (u : Grid N → MetricRec) i, PeriodicGridSobolev.Moser.coordSum r bM
        (fun x : Grid N => interpD u i (PeriodicGridSobolev.samplePt x)) ≤
        Cs * ccoordSum r bM (interpD u i) := fun u i =>
      hsamp N bM (interpD u i) (memH_interpD_all r u i)
    have hfw : ∀ (u : Grid N → MetricRec) i, PeriodicGridSobolev.Moser.coordSum r bM
        (fun x => fwd (N : ℝ)⁻¹ (e N) i u x) ≤ PeriodicGridSobolev.Moser.coordSum (r + 1) bM u := by
      intro u i
      unfold PeriodicGridSobolev.Moser.coordSum
      refine sum_le_sum fun k _ => ?_
      rw [coordArr_bM, coordArr_bM, comp_fwd, cx_Dp]
      exact PeriodicGridSobolev.CommutedRow.sobNorm_Dp_le r i _
    have h3sum : ∀ (f : Fin 3 → ℝ) (c : ℝ), (∀ i, f i ≤ c) → ∑ i, f i ≤ 3 * c := by
      intro f c hf
      calc ∑ i, f i ≤ ∑ _i : Fin 3, c := sum_le_sum fun i _ => hf i
        _ = 3 * c := by simp
    have hu1 : PeriodicGridSobolev.Moser.coordSum r bJP u1 ≤ δL := by
      rw [coordSum_bJP, coordSum_bJ_eq, coordSum_bJ_eq]
      have a1 := gq r (by omega)
      have a2 := gv r (by omega)
      have a3 := h3sum _ _ fun i => (hsd q i).trans
        (mul_le_mul_of_nonneg_left (cqd r i le_rfl (by omega)) hCs)
      have a4 := h3sum _ _ fun i => (hsd v i).trans
        (mul_le_mul_of_nonneg_left (cvd r i le_rfl (by omega)) hCs)
      rw [le_div_iff₀ (by positivity)] at hXL
      have hKX := mul_nonneg hK hX0
      have : 0 ≤ Cs * σ * X := by positivity
      nlinarith
    have hu2 : PeriodicGridSobolev.Moser.coordSum r bJP u2 ≤ δL := by
      rw [coordSum_bJP]
      show PeriodicGridSobolev.Moser.coordSum r bJ (fun x => ((q x, v x,
          fun i => fwd (N : ℝ)⁻¹ (e N) i q x) : JetSpace)) +
        PeriodicGridSobolev.Moser.coordSum r bJ (fun x => ((v x, A x,
          fun i => fwd (N : ℝ)⁻¹ (e N) i v x) : JetSpace)) ≤ δL
      rw [coordSum_bJ_eq, coordSum_bJ_eq]
      have a1 := gq r (by omega)
      have a2 := gv r (by omega)
      have a3 := h3sum _ _ fun i => (hfw q i).trans (gq (r + 1) (by omega))
      have a4 := h3sum _ _ fun i => (hfw v i).trans (gv (r + 1) (by omega))
      rw [le_div_iff₀ (by positivity)] at hXL
      have hKX := mul_nonneg hK hX0
      have : 0 ≤ Cs * σ * X := by positivity
      nlinarith
    have hL := hLip N u1 u2 hu1 hu2 μ ν
    have ediff : u1 - u2 = fun x =>
        ((((0 : MetricRec), (0 : MetricRec), fun i => interpD q i (PeriodicGridSobolev.samplePt x) -
            fwd (N : ℝ)⁻¹ (e N) i q x) : JetSpace),
          (((0 : MetricRec), (0 : MetricRec), fun i => interpD v i (PeriodicGridSobolev.samplePt x) -
            fwd (N : ℝ)⁻¹ (e N) i v x) : JetSpace)) := by
      funext x
      simp only [u1, u2, jetArr, Pi.sub_apply, Prod.mk_sub_mk, sub_self]
      rfl
    rw [ediff, coordSum_bJP, coordSum_bJ_eq, coordSum_bJ_eq] at hL
    have hz : PeriodicGridSobolev.Moser.coordSum r bM (fun _ : Grid N => (0 : MetricRec)) = 0 := by
      unfold PeriodicGridSobolev.Moser.coordSum
      refine sum_eq_zero fun k _ => ?_
      have : PeriodicGridSobolev.Moser.coordArr bM (fun _ : Grid N => (0 : MetricRec)) k = 0 := by
        funext x; simp [PeriodicGridSobolev.Moser.coordArr]
      rw [this, PeriodicGridSobolev.Moser.sobNorm_zero]
    rw [hz] at hL
    have a3 := h3sum _ _ fun i => (hfwd N q i).trans (mul_le_mul_of_nonneg_left
      (cq (r + 2) (by omega) (by omega)) (by positivity : (0 : ℝ) ≤ Cf * (N : ℝ)⁻¹))
    have a4 := h3sum _ _ fun i => (hfwd N v i).trans (mul_le_mul_of_nonneg_left
      (cv (r + 2) (by omega) (by omega)) (by positivity : (0 : ℝ) ≤ Cf * (N : ℝ)⁻¹))
    refine hL.trans ?_
    have : 0 + 0 + ∑ i, PeriodicGridSobolev.Moser.coordSum r bM (fun x =>
        interpD q i (PeriodicGridSobolev.samplePt x) - fwd (N : ℝ)⁻¹ (e N) i q x) +
        (0 + 0 + ∑ i, PeriodicGridSobolev.Moser.coordSum r bM (fun x =>
        interpD v i (PeriodicGridSobolev.samplePt x) - fwd (N : ℝ)⁻¹ (e N) i v x)) ≤
        6 * Cf * σ * h * X := by
      simp only [h] at *
      nlinarith
    calc CL * _ ≤ CL * (6 * Cf * σ * h * X) := mul_le_mul_of_nonneg_left this hCL
      _ = CL * (6 * Cf * σ) * h * X := by ring
  -- assembly
  unfold errDeriv
  have hS1 : PeriodicGridSobolev.sobNorm r (∑ i, ∑ j, (
      (PeriodicGridSobolev.Sampling.sample N (fun y => ((prodDT (harmC i j) (interpRec q y)
          (interpRec v y) (interpD q i y) (interpD v i y) (interpD q j y μ ν) (interpD v j y μ ν)
          (interpDD q i j y μ ν) (interpDD v i j y μ ν) : ℝ) : ℂ)) -
        PeriodicGridSobolev.Dm i (PeriodicGridSobolev.Sampling.sample N (fun y => ((prodT
          (harmC i j) (interpRec q y) (interpRec v y) (interpD q j y μ ν) (interpD v j y μ ν) :
            ℝ) : ℂ)))) +
      PeriodicGridSobolev.Dm i (cx (fun x => fderiv ℝ (harmC i j) (minkowski + q x) (v x)) *
          (PeriodicGridSobolev.Sampling.sample N ⇑(cmp (interpD q j) μ ν) -
            PeriodicGridSobolev.Dp j (cx (comp q μ ν))) +
        cx (cArr q i j) * (PeriodicGridSobolev.Sampling.sample N ⇑(cmp (interpD v j) μ ν) -
          PeriodicGridSobolev.Dp j (cx (comp v μ ν)))))) ≤
      9 * ((Cm * CF * (σ ^ 2 + σ) + (32 * A1 * Cr1 * Cp1 * σ + (A1 + 1) * Cp1 * σ)) * h * X) := by
    refine (PeriodicGridSobolev.Moser.sobNorm_sum_le r _ _).trans ?_
    calc _ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3,
          (Cm * CF * (σ ^ 2 + σ) + (32 * A1 * Cr1 * Cp1 * σ + (A1 + 1) * Cp1 * σ)) * h * X := by
          refine sum_le_sum fun i _ => (PeriodicGridSobolev.Moser.sobNorm_sum_le r _ _).trans ?_
          refine sum_le_sum fun j _ => (PeriodicGridSobolev.Moser.sobNorm_add_le r _ _).trans ?_
          have := add_le_add (hE1 i j) (hE2 i j)
          linarith
      _ = _ := by simp; ring
  have hS2 : PeriodicGridSobolev.sobNorm r (∑ i,
      (cx (fun x => fderiv ℝ (harmB i) (minkowski + q x) (v x)) *
          (PeriodicGridSobolev.Sampling.sample N ⇑(cmp (interpD v i) μ ν) -
            PeriodicGridSobolev.D0 i (cx (comp v μ ν))) +
        cx (bArr q i) * (PeriodicGridSobolev.Sampling.sample N ⇑(cmp (interpD A i) μ ν) -
          PeriodicGridSobolev.D0 i (cx (comp A μ ν))))) ≤
      3 * ((32 * A0 * Cr0 * C0 * σ + (A0 + 1) * C0 * σ * K) * h * X) := by
    refine (PeriodicGridSobolev.Moser.sobNorm_sum_le r _ _).trans ?_
    calc _ ≤ ∑ _i : Fin 3, (32 * A0 * Cr0 * C0 * σ + (A0 + 1) * C0 * σ * K) * h * X :=
          sum_le_sum fun i _ => hE3 i
      _ = _ := by simp
  have hS3 : PeriodicGridSobolev.sobNorm r (∑ i,
      (PeriodicGridSobolev.Sampling.sample N (fun y => ((prodDT (harmB i) (interpRec q y)
          (interpRec v y) (interpD q i y) (interpD v i y) (interpRec v y μ ν) (interpRec A y μ ν)
          (interpD v i y μ ν) (interpD A i y μ ν) : ℝ) : ℂ)) -
        PeriodicGridSobolev.D0 i (PeriodicGridSobolev.Sampling.sample N (fun y => ((prodT
          (harmB i) (interpRec q y) (interpRec v y) (interpRec v y μ ν) (interpRec A y μ ν) :
            ℝ) : ℂ))))) ≤ 3 * (C0 * CF * (σ ^ 2 + σ * K) * h * X) := by
    refine (PeriodicGridSobolev.Moser.sobNorm_sum_le r _ _).trans ?_
    calc _ ≤ ∑ _i : Fin 3, C0 * CF * (σ ^ 2 + σ * K) * h * X := sum_le_sum fun i _ => hE4 i
      _ = _ := by simp
  refine ((PeriodicGridSobolev.Moser.sobNorm_add_le r _ _).trans (add_le_add
    ((PeriodicGridSobolev.Moser.sobNorm_sub_le r _ _).trans (add_le_add
      ((PeriodicGridSobolev.Moser.sobNorm_sub_le r _ _).trans (add_le_add hS1 hS2)) hS3)) hE5)).trans
    (le_of_eq ?_)
  simp only [Ctot, h]
  ring

/-! ### The undifferentiated rows of the `B`-writer interpolant -/

section LawRows

/-- **The continuum normal row of the interpolated `B`-writer state is `O(h)` in `H^{s-2}`**
(upper components; uniformly in marks `‖B‖_op ≤ b ≤ 1`): the central rows `interp_row_small` plus
the extra row `a(g_h) 𝓘_h(-a⁻¹ h² B Λ_h² q)` (`normalRow_add_w`, `Fnorm_lawForce_mesh`). -/
theorem interp_row_small_law (s : ℕ) (hs : 5 ≤ s) :
    ∃ δ > 0, ∃ C ≥ 0, ∀ (N : ℕ) [NeZero N] (β : ℝ) (B : Upper → Upper → ℝ), IsMark β B → β ≤ 1 →
      ∀ (q v : Grid N → MetricRec), IsSymRec q → IsSymRec v → Xnorm s q v ≤ δ → ∀ κ : Upper,
      ∃ R : CT, ⇑R = rowF (interpRec q) (interpRec v) (interpRec (symRec (lawAccel B q v)))
          (interpD q) (interpD v) (interpDD q) κ.1.1 κ.1.2 ∧ MemH (s - 2) ⇑R ∧
        sn (s - 2) ⇑R ≤ C * (N : ℝ)⁻¹ * Xnorm s q v := by
  obtain ⟨δr, hδr, Cr, hCr, hrow⟩ := interp_row_small s hs
  obtain ⟨δa, hδa, Ka, hKa, hmulA⟩ := coef_mul_family (s - 2) (by omega)
    (fun _ : Unit => harmA) (fun _ => analyticAt_harmA)
  obtain ⟨δF, hδF, CF, hCF, hF⟩ := Fnorm_lawForce_mesh (s - 2) (by omega)
  set Ct : ℝ := 16 * Real.sqrt (pc (s - 2))
  have hCt : 0 ≤ Ct := by positivity
  set δ : ℝ := min δr (min (δa / (Ct + 1)) δF)
  have hδ : 0 < δ := lt_min hδr (lt_min (by positivity) hδF)
  set Cx : ℝ := Cr + Ka * (Real.sqrt (pc (s - 2)) * CF)
  refine ⟨δ, hδ, Cx, by positivity, fun N _ b' B hB hb1 q v hq hv hX κ => ?_⟩
  have hb0 := hB.nonneg
  set X := Xnorm s q v
  have hX0 : 0 ≤ X := Xnorm_nonneg _ _ _
  set V0 := harmonicWriterAcceleration q v
  set Fc := lawForce B q
  have hsplit : interpRec (symRec (lawAccel B q v)) =
      interpRec (symRec V0) + interpRec (symRec Fc) := by
    rw [show lawAccel B q v = V0 + Fc from rfl, symRec_add, interpRec_add]
  have hQm : ∀ k, MemH (s - 2) ⇑(ccoord bM (interpRec q) k) := fun k => (memH_interpRec _ _ k).1
  have hQs : ccoordSum (s - 2) bM (interpRec q) ≤ δa := by
    have h1 := ccoordSum_interpRec_le (s - 2) s hq v (by omega)
    have h2 : X ≤ δa / (Ct + 1) := hX.trans ((min_le_right _ _).trans (min_le_left _ _))
    rw [le_div_iff₀ (by positivity)] at h2
    have : ccoordSum (s - 2) bM (interpRec q) ≤ Ct * X := h1
    nlinarith
  have hFb : Fnorm (s - 2) Fc ≤ CF * (N : ℝ)⁻¹ * b' * X := by
    have h := hF N b' B q v hB hq (by
      rw [show s - 2 + 2 = s by omega]; exact hX.trans ((min_le_right _ _).trans (min_le_right _ _)))
    rwa [show s - 2 + 2 = s by omega] at h
  obtain ⟨R0, hR0, hR0m, hR0s⟩ := hrow N q v hq hv (hX.trans (min_le_left _ _)) κ
  obtain ⟨hGm, hGs⟩ := memH_interpRec (s - 2) (symRec Fc) ⟨κ.1.1, κ.1.2⟩
  rw [ccoord_bM] at hGm hGs
  obtain ⟨P, hPy, hPm, hPs⟩ := hmulA () (interpRec q) hQm hQs _ hGm
  refine ⟨R0 + P, ?_, memH_add hR0m hPm, ?_⟩
  · funext y
    rw [ContinuousMap.add_apply, hPy y, hR0, hsplit]
    simp only [rowF, ContinuousMap.add_apply, normalRow_add_w, cmp_apply]
    push_cast
    ring
  · have hc : PeriodicGridSobolev.sobNorm (s - 2) (cx (comp (symRec Fc) κ.1.1 κ.1.2)) ≤
        CF * (N : ℝ)⁻¹ * b' * X := by
      have e : comp (symRec Fc) κ.1.1 κ.1.2 = comp Fc κ.1.1 κ.1.2 := by
        funext x; exact symRec_upper Fc x κ
      rw [e]
      exact (sobNorm_le_Fnorm (s - 2) Fc κ).trans hFb
    have hPs' : sn (s - 2) ⇑P ≤ Ka * (Real.sqrt (pc (s - 2)) * (CF * (N : ℝ)⁻¹ * X)) := by
      refine hPs.trans (mul_le_mul_of_nonneg_left (hGs.trans ?_) hKa)
      refine mul_le_mul_of_nonneg_left (hc.trans ?_) (Real.sqrt_nonneg _)
      have : CF * (N : ℝ)⁻¹ * b' * X ≤ CF * (N : ℝ)⁻¹ * 1 * X := by gcongr
      linarith
    refine (sn_add_le' hR0m hPm).trans ?_
    have : sn (s - 2) ⇑R0 + sn (s - 2) ⇑P ≤
        Cr * (N : ℝ)⁻¹ * X + Ka * (Real.sqrt (pc (s - 2)) * (CF * (N : ℝ)⁻¹ * X)) :=
      add_le_add hR0s hPs'
    refine this.trans (le_of_eq ?_)
    simp only [Cx]; ring

end LawRows


/-! ### The linearized row of the interpolated writer is `O(h)` in `H^{s-3}` -/

section Core

/-- **Aliasing**: a continuum field in `H^{r+1}` is controlled in `H^r` by its grid samples and
one mesh power: `‖R‖_{H^r} ≤ √(pc r) ‖𝒮_h R‖_{r,h} + C h ‖R‖_{H^{r+1}}`. -/
theorem sn_le_of_sample (r : ℕ) (hr : 1 ≤ r) :
    ∃ C ≥ 0, ∀ (N : ℕ) [NeZero N] (R : CT), MemH (r + 1) ⇑R →
      sn r ⇑R ≤ Real.sqrt (pc r) * PeriodicGridSobolev.sobNorm r
        (PeriodicGridSobolev.Sampling.sample N ⇑R) + C * (N : ℝ)⁻¹ * sn (r + 1) ⇑R := by
  obtain ⟨Ce, hCe, herr⟩ := PeriodicGridSobolev.Sampling.sampling_error r 1 (by omega)
  refine ⟨Real.sqrt Ce, Real.sqrt_nonneg _, fun N _ R hRm => ?_⟩
  obtain ⟨hEm, hEb⟩ := herr N R hRm
  have hPm : MemH r ⇑(PeriodicGridSobolev.Sampling.proj N ⇑R) := (isTP_interp _).summable _
  have eR : R = PeriodicGridSobolev.Sampling.proj N ⇑R -
      (PeriodicGridSobolev.Sampling.proj N ⇑R - R) := by abel
  have h1 : sn r ⇑(PeriodicGridSobolev.Sampling.proj N ⇑R) ≤
      Real.sqrt (pc r) * PeriodicGridSobolev.sobNorm r (PeriodicGridSobolev.Sampling.sample N ⇑R) := by
    have hp := trigSobSq_proj_le_sobSq (N := N) r ⇑R
    unfold sn
    calc Real.sqrt (PeriodicGridSobolev.trigSobSq r ⇑(PeriodicGridSobolev.Sampling.proj N ⇑R))
        ≤ Real.sqrt (pc r * PeriodicGridSobolev.sobNorm r
            (PeriodicGridSobolev.Sampling.sample N ⇑R) ^ 2) := by
          refine Real.sqrt_le_sqrt (hp.trans (le_of_eq ?_))
          rw [PeriodicGridSobolev.sobNorm_sq]
      _ = Real.sqrt (pc r) * PeriodicGridSobolev.sobNorm r
            (PeriodicGridSobolev.Sampling.sample N ⇑R) := by
          rw [Real.sqrt_mul (pc_pos _).le,
            Real.sqrt_sq (PeriodicGridSobolev.Moser.sobNorm_nonneg _ _)]
  have h2 : sn r ⇑(PeriodicGridSobolev.Sampling.proj N ⇑R - R) ≤
      Real.sqrt Ce * (N : ℝ)⁻¹ * sn (r + 1) ⇑R := by
    unfold sn
    have e2 : Ce * (((N : ℝ) ^ 2) ^ 1)⁻¹ * PeriodicGridSobolev.trigSobSq (r + 1) ⇑R =
        (Real.sqrt Ce * (N : ℝ)⁻¹ * Real.sqrt (PeriodicGridSobolev.trigSobSq (r + 1) ⇑R)) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hCe, Real.sq_sqrt (trigSobSq_nonneg _ _)]
      field_simp
    rw [e2] at hEb
    calc Real.sqrt (PeriodicGridSobolev.trigSobSq r ⇑(PeriodicGridSobolev.Sampling.proj N ⇑R - R))
        ≤ Real.sqrt ((Real.sqrt Ce * (N : ℝ)⁻¹ *
            Real.sqrt (PeriodicGridSobolev.trigSobSq (r + 1) ⇑R)) ^ 2) := Real.sqrt_le_sqrt hEb
      _ = _ := Real.sqrt_sq (by positivity)
  have h3 := sn_sub_le' hPm hEm
  rw [← eR] at h3
  linarith

variable {N : ℕ} [NeZero N]

/-- The (symmetrized) law-family acceleration record `q_tt = V_{B,h}(q, v)`. -/
def accRec (B : Upper → Upper → ℝ) (q v : Grid N → MetricRec) : Grid N → MetricRec :=
  symRec (lawAccel B q v)

/-- The (symmetrized) third time derivative `q_ttt` (`jetDeriv`, the once-differentiated mass
row). -/
def accDRec (B : Upper → Upper → ℝ) (q v : Grid N → MetricRec) : Grid N → MetricRec :=
  symRec (fun x μ ν => jetDeriv B q v (accRec B q v) x μ ν)

/-- **The linearized normal row of the interpolant jet in the direction of the writer flow**:
the jet `(𝓘q, 𝓘v, 𝓘q_tt, ∂𝓘q, ∂𝓘v, ∂²𝓘q)` with the direction
`(𝓘v, 𝓘q_tt, 𝓘q_ttt, ∂𝓘v, ∂𝓘q_tt, ∂²𝓘v)` (`q_tt = V_{B,h}(q, v)`, `q_ttt = jetDeriv`). -/
def interpRowDeriv (B : Upper → Upper → ℝ) (q v : Grid N → MetricRec) (y : T3) (μ ν : Fin 4) : ℝ :=
  rowDeriv (interpRec q y) (interpRec v y) (interpRec (accRec B q v) y) (fun i => interpD q i y)
    (fun i => interpD v i y) (fun i j => interpDD q i j y) (interpRec v y)
    (interpRec (accRec B q v) y) (interpRec (accDRec B q v) y) (fun i => interpD v i y)
    (fun i => interpD (accRec B q v) i y) (fun i j => interpDD v i j y) μ ν

theorem ccoordSum_interpDD_le (k : ℕ) (u : Grid N → MetricRec) (i j : Fin 3) :
    ccoordSum k bM (interpDD u i j) ≤ ccoordSum (k + 1) bM (interpD u j) :=
  (ccoordSum_deriv_le ((isContJet_interp u u).dQd i j) (memH_interpD_all (k + 1) u j)).2

theorem Xnorm_shift_le (s : ℕ) (hs : 1 ≤ s) (q v : Grid N → MetricRec) :
    Xnorm (s - 1) v 0 ≤ Xnorm s q v := by
  unfold Xnorm
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

set_option maxHeartbeats 8000000 in
/-- **The linearized row of the interpolated writer state is `O(h)` in `H^{s-3}`** (the core of
the time-differentiated half of `eq:supp-open-reduced-rate`), uniformly in the mesh and in the
marks `‖B‖_op ≤ 1/48`.  For `s ≥ 5` there are `δ, C` such that for every symmetric record
`X = (q, v)` with `‖X‖_{X^s_h} ≤ δ`, every component of the linearized normal row of the
interpolant jet in the direction of the writer flow (`interpRowDeriv`) lies in `H^{s-3}` with
norm `≤ C h ‖X‖_{X^s_h}`.  Proof: the sampled row identity holds along the straight path
`(q + τ v, v + τ q_tt)`; differentiating it at `τ = 0` gives
`𝒮_h ρ' = -h² B Λ_h² v - errDeriv` (the differentiated consistency error, `errDeriv_bound`);
`ρ' ∈ H^{s-2}` (`rowDeriv_sn_le`, `law_time_jets`-type bounds) and aliasing finish. -/
theorem interp_rowDeriv_small (s : ℕ) (hs : 5 ≤ s) :
    ∃ δ > 0, ∃ C ≥ 0, ∀ (N : ℕ) [NeZero N] (B : Upper → Upper → ℝ) (q v : Grid N → MetricRec),
      IsMark (1 / 48) B → IsSymRec q → IsSymRec v → Xnorm s q v ≤ δ → ∀ μ ν : Fin 4,
      ∃ R : CT, (∀ y, R y = ((interpRowDeriv B q v y μ ν : ℝ) : ℂ)) ∧ MemH (s - 3) ⇑R ∧
        sn (s - 3) ⇑R ≤ C * (N : ℝ)⁻¹ * Xnorm s q v := by
  obtain ⟨δ0, hδ0, K0, hK0, hcore⟩ := reduced_residual_of_rows s hs
  obtain ⟨r₀, hr₀, hchart⟩ := exists_det_chart
  obtain ⟨δL, hδL, KL, hKL, hLa⟩ := lawAccel_bound s (by omega)
  obtain ⟨δJ, hδJ, KJ, hKJ, hJ⟩ := jetDeriv_bound s (by omega)
  obtain ⟨δE, hδE, CE, hCE, hE⟩ := errDeriv_bound s hs KL hKL
  obtain ⟨δR, hδR, CR, hCR, hR⟩ := rowDeriv_sn_le (s - 2) (by omega)
  obtain ⟨Ca, hCa, halias⟩ := sn_le_of_sample (s - 3) (by omega)
  have hS := supConst_nonneg
  set σ : ℝ := 16 * (Real.sqrt (pc (s - 2)) + Real.sqrt (pc (s - 1)) + Real.sqrt (pc s)) + 16
    with hσdef
  have hσ0 : 0 ≤ σ := by positivity
  have hsq2 : 16 * Real.sqrt (pc (s - 2)) ≤ σ := by
    have := Real.sqrt_nonneg (pc (s - 1)); have := Real.sqrt_nonneg (pc s); simp only [hσdef]; linarith
  have hsq1 : 16 * Real.sqrt (pc (s - 1)) ≤ σ := by
    have := Real.sqrt_nonneg (pc (s - 2)); have := Real.sqrt_nonneg (pc s); simp only [hσdef]; linarith
  have hsq0 : 16 * Real.sqrt (pc s) ≤ σ := by
    have := Real.sqrt_nonneg (pc (s - 1)); have := Real.sqrt_nonneg (pc (s - 2))
    simp only [hσdef]; linarith
  set cY : ℝ := 12 * σ + σ * KL
  set cY' : ℝ := 14 * σ + 4 * σ * KL + σ * KJ
  set δ : ℝ := min (min (min δ0 δL) (min δJ δE)) (min (min (δR / (5 * σ + 1))
    (r₀ / (2 * (supConst + 1)))) 1)
  have hδ : 0 < δ := by positivity
  set CRR : ℝ := CR * cY' * (1 + cY)
  refine ⟨δ, hδ, Real.sqrt (pc (s - 3)) * (6 + CE) + Ca * CRR, by positivity,
    fun N _ B q v hB hq hv hX μ ν => ?_⟩
  set X := Xnorm s q v
  set h : ℝ := (N : ℝ)⁻¹
  have hh : 0 ≤ h := by positivity
  have hX0 : 0 ≤ X := Xnorm_nonneg _ _ _
  have hXδ0 : X ≤ δ0 := hX.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hXL : X ≤ δL := hX.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hXJ : X ≤ δJ := hX.trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hXE : X ≤ δE := hX.trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hXR : X ≤ δR / (5 * σ + 1) :=
    hX.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hXc : X ≤ r₀ / (2 * (supConst + 1)) :=
    hX.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hX1 : X ≤ 1 := hX.trans ((min_le_right _ _).trans (min_le_right _ _))
  set A := accRec B q v with hAdef
  set A' := accDRec B q v with hA'def
  have hAsym : IsSymRec A := isSymRec_symRec _
  have hAb : ∀ μ ν, PeriodicGridSobolev.sobNorm (s - 1) (cx (comp A μ ν)) ≤ KL * X := by
    intro μ ν
    rw [hAdef, accRec, comp_symRec_eq]
    exact hLa N B q v hB hq hv hXL (upperOf μ ν)
  have hA'b : ∀ μ ν, PeriodicGridSobolev.sobNorm (s - 2) (cx (comp A' μ ν)) ≤ KJ * X := by
    intro μ ν
    rw [hA'def, accDRec, comp_symRec_eq]
    exact hJ N B q v hB hq hv hXJ (upperOf μ ν)
  have hdet : ∀ y, (Matrix.of (minkowski + interpRec q y)).det ≠ 0 :=
    (hcore N q v 0 hq hv (fun _ _ _ => rfl) hXδ0).1
  have hqx : ∀ x, ‖(minkowski + q x) - minkowski‖ < r₀ := by
    intro x
    rw [add_sub_cancel_left]
    have h1 := norm_q_le s (by omega) hq v x
    have h2 : supConst * X ≤ supConst * (r₀ / (2 * (supConst + 1))) :=
      mul_le_mul_of_nonneg_left hXc hS
    have h3 : supConst * (r₀ / (2 * (supConst + 1))) < r₀ := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  have hdetx : ∀ x, (Matrix.of (minkowski + q x)).det ≠ 0 := fun x => (hchart _ (hqx x)).1
  have ha : ∀ x, aArr q x ≠ 0 := fun x => (hchart _ (hqx x)).2
  -- the straight path in the direction of the writer flow
  set qL : ℝ → Grid N → MetricRec := fun τ => q + τ • v with hqLdef
  set vL : ℝ → Grid N → MetricRec := fun τ => v + τ • A with hvLdef
  have hq0 : qL 0 = q := by simp [qL]
  have hv0 : vL 0 = v := by simp [vL]
  have hqL : ∀ x μ ν, HasDerivWithinAt (fun τ => qL τ x μ ν) (v x μ ν) Set.univ 0 := by
    intro x μ ν
    have := (((hasDerivAt_id (0 : ℝ)).mul_const (v x μ ν)).const_add (q x μ ν)).hasDerivWithinAt
      (s := Set.univ)
    simpa [qL] using this
  have hvL : ∀ x μ ν, HasDerivWithinAt (fun τ => vL τ x μ ν) (A x μ ν) Set.univ 0 := by
    intro x μ ν
    have := (((hasDerivAt_id (0 : ℝ)).mul_const (A x μ ν)).const_add (v x μ ν)).hasDerivWithinAt
      (s := Set.univ)
    simpa [vL] using this
  have hAL : ∀ x μ ν, HasDerivWithinAt (fun τ => accRec B (qL τ) (vL τ) x μ ν) (A' x μ ν)
      Set.univ 0 := by
    intro x μ ν
    have hq' : ∀ y μ ν, HasDerivWithinAt (fun τ => qL τ y μ ν) (vL 0 y μ ν) Set.univ 0 := by
      rw [hv0]; exact hqL
    have h1 := hasDerivWithinAt_lawAccel B hq' hvL (by rw [hq0]; exact hdetx) (by rw [hq0]; exact ha)
      x (upperOf μ ν).1.1 (upperOf μ ν).1.2
    rw [hq0, hv0] at h1
    exact h1
  have dQ := hasDerivWithinAt_interpRec' hqL
  have dV := hasDerivWithinAt_interpRec' hvL
  have dW := hasDerivWithinAt_interpRec' hAL
  have dQd := hasDerivWithinAt_interpD' hqL
  have dVd := hasDerivWithinAt_interpD' hvL
  have dQdd := hasDerivWithinAt_interpDD' hqL
  have hrow : ∀ y μ ν, HasDerivAt (fun τ => normalRow (interpRec (qL τ) y) (interpRec (vL τ) y)
      (interpRec (accRec B (qL τ) (vL τ)) y) (fun i => interpD (qL τ) i y)
      (fun i => interpD (vL τ) i y) (fun i j => interpDD (qL τ) i j y) μ ν)
      (interpRowDeriv B q v y μ ν) 0 := by
    intro y μ ν
    have h1 := hasDerivWithinAt_normalRow (q := fun τ => interpRec (qL τ) y)
      (v := fun τ => interpRec (vL τ) y) (w := fun τ => interpRec (accRec B (qL τ) (vL τ)) y)
      (qd := fun τ i => interpD (qL τ) i y) (vd := fun τ i => interpD (vL τ) i y)
      (qdd := fun τ i j => interpDD (qL τ) i j y) (by simp only [hq0]; exact hdet y) (dQ y) (dV y)
      (dW y) (fun i => dQd i y) (fun i => dVd i y) (fun i j => dQdd i j y) μ ν
    simp only [hq0, hv0] at h1
    exact h1.hasDerivAt Filter.univ_mem
  -- symmetry of the linearized row
  have hsymD : ∀ y μ ν, interpRowDeriv B q v y μ ν = interpRowDeriv B q v y ν μ := by
    intro y μ ν
    have hc : ContinuousAt (fun τ => (Matrix.of (minkowski + interpRec (qL τ) y)).det) 0 := by
      have h1 : ContinuousAt (fun τ => interpRec (qL τ) y) 0 :=
        ((dQ y).hasDerivAt Filter.univ_mem).continuousAt
      have hcd : Continuous (fun g : MetricRec => (Matrix.of g).det) :=
        Continuous.matrix_det (by fun_prop)
      exact hcd.continuousAt.comp (continuousAt_const.add h1)
    have hev := hc.eventually_ne (by simp only [hq0]; exact hdet y)
    have hsqL : ∀ τ, IsSymRec (qL τ) := fun τ x μ ν => by
      simp only [qL, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hq x μ ν, hv x μ ν]
    have hsvL : ∀ τ, IsSymRec (vL τ) := fun τ x μ ν => by
      simp only [vL, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hv x μ ν, hAsym x μ ν]
    have heq : (fun τ => normalRow (interpRec (qL τ) y) (interpRec (vL τ) y)
        (interpRec (accRec B (qL τ) (vL τ)) y) (fun i => interpD (qL τ) i y)
        (fun i => interpD (vL τ) i y) (fun i j => interpDD (qL τ) i j y) ν μ) =ᶠ[𝓝 0]
        (fun τ => normalRow (interpRec (qL τ) y) (interpRec (vL τ) y)
        (interpRec (accRec B (qL τ) (vL τ)) y) (fun i => interpD (qL τ) i y)
        (fun i => interpD (vL τ) i y) (fun i j => interpDD (qL τ) i j y) μ ν) := by
      filter_upwards [hev] with τ hτ
      exact (normalRow_symm _ _ _ _ _ _ (interpRec_symm (hsqL τ) y) hτ (interpRec_symm (hsvL τ) y)
        (fun i => interpD_symm (hsqL τ) i y) (interpRec_symm (isSymRec_symRec _) y)
        (fun i => interpD_symm (hsvL τ) i y) (fun i j => interpDD_symm (hsqL τ) i j y)
        (fun i j => by rw [interpDD_comm]) μ ν).symm
    exact ((hrow y μ ν).congr_of_eventuallyEq heq).unique (hrow y ν μ)
  have hupper : ∀ y μ ν, interpRowDeriv B q v y μ ν =
      interpRowDeriv B q v y (upperOf μ ν).1.1 (upperOf μ ν).1.2 := by
    intro y μ ν
    unfold upperOf
    split_ifs
    · rfl
    · exact hsymD y μ ν
  -- the differentiated sampled identity (upper components)
  have heva : ∀ᶠ τ in 𝓝 (0 : ℝ), ∀ x, aArr (qL τ) x ≠ 0 := by
    refine Filter.eventually_all.2 fun x => ?_
    have hc : ContinuousAt (fun τ => aArr (qL τ) x) 0 :=
      ((hasDerivWithinAt_coef (F := harmA) hqL x (by rw [hq0]; exact
        (analyticAt_harmA_of_det (hdetx x)).differentiableAt)).hasDerivAt
          Filter.univ_mem).continuousAt
    exact hc.eventually_ne (by simp only [hq0]; exact ha x)
  have hSmp : ∀ κ : Upper, ∀ x, ((interpRowDeriv B q v (PeriodicGridSobolev.samplePt x)
      κ.1.1 κ.1.2 : ℝ) : ℂ) = -cx (comp (bTerm B v) κ.1.1 κ.1.2) x -
        errDeriv q v v A κ.1.1 κ.1.2 x := by
    intro κ x
    have hid : ∀ τ, (∀ x, aArr (qL τ) x ≠ 0) →
        PeriodicGridSobolev.Sampling.sample N (rowF (interpRec (qL τ)) (interpRec (vL τ))
          (interpRec (accRec B (qL τ) (vL τ))) (interpD (qL τ)) (interpD (vL τ)) (interpDD (qL τ))
          κ.1.1 κ.1.2) = -cx (comp (bTerm B (qL τ)) κ.1.1 κ.1.2) -
          errRow (qL τ) (vL τ) κ.1.1 κ.1.2 := by
      intro τ haτ
      have h1 := row_identity_interp (qL τ) (vL τ) (accRec B (qL τ) (vL τ)) haτ κ.1.1 κ.1.2
      have e : cx (aArr (qL τ)) * cx (comp (accRec B (qL τ) (vL τ) -
          harmonicWriterAcceleration (qL τ) (vL τ)) κ.1.1 κ.1.2) =
          -cx (comp (bTerm B (qL τ)) κ.1.1 κ.1.2) := by
        funext z
        have hz := haτ z
        have hz' : ((aArr (qL τ) z : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hz
        simp only [cx, comp, Pi.mul_apply, Pi.neg_apply, Pi.sub_apply, accRec, symRec_upper,
          lawAccel, lawForce, Pi.add_apply]
        push_cast
        field_simp
        ring
      rw [e] at h1
      linear_combination -h1
    have hL : HasDerivAt (fun τ => PeriodicGridSobolev.Sampling.sample N (rowF (interpRec (qL τ))
        (interpRec (vL τ)) (interpRec (accRec B (qL τ) (vL τ))) (interpD (qL τ)) (interpD (vL τ))
        (interpDD (qL τ)) κ.1.1 κ.1.2) x)
        ((interpRowDeriv B q v (PeriodicGridSobolev.samplePt x) κ.1.1 κ.1.2 : ℝ) : ℂ) 0 :=
      (hrow (PeriodicGridSobolev.samplePt x) κ.1.1 κ.1.2).ofReal_comp
    have hb := (hasDerivWithinAt_bTerm B hqL x κ.1.1 κ.1.2).ofReal_comp
    have he := hasDerivWithinAt_pi.1 (hasDerivWithinAt_errRow hqL hvL
      (by simp only [hq0]; exact hdet) κ.1.1 κ.1.2) x
    simp only [hq0, hv0] at he
    have hRHS : HasDerivAt (fun τ => (-cx (comp (bTerm B (qL τ)) κ.1.1 κ.1.2) -
        errRow (qL τ) (vL τ) κ.1.1 κ.1.2) x)
        (-cx (comp (bTerm B v) κ.1.1 κ.1.2) x - errDeriv q v v A κ.1.1 κ.1.2 x) 0 :=
      ((hb.neg).sub he).hasDerivAt Filter.univ_mem
    have heq : (fun τ => (-cx (comp (bTerm B (qL τ)) κ.1.1 κ.1.2) -
        errRow (qL τ) (vL τ) κ.1.1 κ.1.2) x) =ᶠ[𝓝 0]
        (fun τ => PeriodicGridSobolev.Sampling.sample N (rowF (interpRec (qL τ))
          (interpRec (vL τ)) (interpRec (accRec B (qL τ) (vL τ))) (interpD (qL τ))
          (interpD (vL τ)) (interpDD (qL τ)) κ.1.1 κ.1.2) x) := by
      filter_upwards [heva] with τ hτ
      rw [hid τ hτ]
    exact (hL.congr_of_eventuallyEq heq).unique hRHS
  -- the linearized row in `H^{s-2}`
  have cq : ∀ k, k ≤ s → s - 2 ≤ k → ccoordSum k bM (interpRec q) ≤ σ * X := by
    intro k hk hk2
    refine (ccoordSum_interpRec_le k s hq v (by omega)).trans ?_
    have : 16 * Real.sqrt (pc k) ≤ σ := by
      rcases (show k = s - 2 ∨ k = s - 1 ∨ k = s by omega) with rfl | rfl | rfl <;> assumption
    nlinarith
  have cv : ∀ k, k ≤ s → s - 2 ≤ k → ccoordSum k bM (interpRec v) ≤ σ * X := by
    intro k hk hk2
    refine (ccoordSum_interpRec_v_le k s q hv hk).trans ?_
    have : 16 * Real.sqrt (pc k) ≤ σ := by
      rcases (show k = s - 2 ∨ k = s - 1 ∨ k = s by omega) with rfl | rfl | rfl <;> assumption
    nlinarith
  have cA : ∀ k, k ≤ s - 1 → s - 2 ≤ k → ccoordSum k bM (interpRec A) ≤ σ * KL * X := by
    intro k hk hk2
    refine (ccoordSum_interpRec_of k A fun μ ν =>
      (PeriodicGridSobolev.Moser.sobNorm_mono hk _).trans (hAb μ ν)).trans ?_
    have : 16 * Real.sqrt (pc k) ≤ σ := by
      rcases (show k = s - 2 ∨ k = s - 1 by omega) with rfl | rfl <;> assumption
    have := mul_nonneg hKL hX0
    nlinarith
  have cA' : ccoordSum (s - 2) bM (interpRec A') ≤ σ * KJ * X := by
    refine (ccoordSum_interpRec_of (s - 2) A' hA'b).trans ?_
    have := mul_nonneg hKJ hX0
    nlinarith
  have hsum3 : ∀ (f : Fin 3 → ℝ) (c : ℝ), (∀ i, f i ≤ c) → ∑ i, f i ≤ 3 * c := by
    intro f c hf
    calc ∑ i, f i ≤ ∑ _i : Fin 3, c := sum_le_sum fun i _ => hf i
      _ = 3 * c := by simp
  have hsum9 : ∀ (f : Fin 3 → Fin 3 → ℝ) (c : ℝ), (∀ i j, f i j ≤ c) → ∑ i, ∑ j, f i j ≤ 9 * c := by
    intro f c hf
    calc ∑ i, ∑ j, f i j ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, c :=
          sum_le_sum fun i _ => sum_le_sum fun j _ => hf i j
      _ = 9 * c := by simp; ring
  have hjet : ccoordSum (s - 2) bJ (jetField (interpRec q) (interpRec v) (interpD q)) ≤ δR := by
    rw [ccoordSum_jetField]
    have a1 := cq (s - 2) (by omega) le_rfl
    have a2 := cv (s - 2) (by omega) le_rfl
    have a3 := hsum3 _ _ fun i => (ccoordSum_interpD_le (s - 2) q i).trans
      (cq (s - 2 + 1) (by omega) (by omega))
    rw [le_div_iff₀ (by positivity)] at hXR
    nlinarith
  obtain ⟨R, hRy, hRm, hRs⟩ := hR (interpRec q) (interpRec v) (interpRec A) (interpRec v)
    (interpRec A) (interpRec A') (interpD q) (interpD v) (interpD v) (interpD A) (interpDD q)
    (interpDD v) (memH_interpRec_all _ q) (memH_interpRec_all _ v) (memH_interpRec_all _ A)
    (fun i => memH_interpD_all _ q i) (fun i => memH_interpD_all _ v i)
    (fun i j => memH_interpDD_all _ q i j) (memH_interpRec_all _ v) (memH_interpRec_all _ A)
    (memH_interpRec_all _ A') (fun i => memH_interpD_all _ v i) (fun i => memH_interpD_all _ A i)
    (fun i j => memH_interpDD_all _ v i j) hjet μ ν
  have hRs' : sn (s - 2) ⇑R ≤ CRR * X := by
    refine hRs.trans ?_
    have y1 := cv (s - 2) (by omega) le_rfl
    have y2 := cA'
    have y3 := hsum3 _ _ fun i => (ccoordSum_interpD_le (s - 2) A i).trans
      (cA (s - 2 + 1) (by omega) (by omega))
    have y4 := hsum9 _ _ fun i j => (ccoordSum_interpDD_le (s - 2) v i j).trans
      ((ccoordSum_interpD_le (s - 2 + 1) v j).trans (cv (s - 2 + 1 + 1) (by omega) (by omega)))
    have y5 : ccoordSum (s - 2) bJ (jetField (interpRec v) (interpRec A) (interpD v)) ≤
        σ * X + σ * KL * X + 3 * (σ * X) := by
      rw [ccoordSum_jetField]
      have a1 := cA (s - 2) (by omega) le_rfl
      have a3 := hsum3 _ _ fun i => (ccoordSum_interpD_le (s - 2) v i).trans
        (cv (s - 2 + 1) (by omega) (by omega))
      linarith
    have z1 := cA (s - 2) (by omega) le_rfl
    have z2 := hsum3 _ _ fun i => (ccoordSum_interpD_le (s - 2) v i).trans
      (cv (s - 2 + 1) (by omega) (by omega))
    have z3 := hsum9 _ _ fun i j => (ccoordSum_interpDD_le (s - 2) q i j).trans
      ((ccoordSum_interpD_le (s - 2 + 1) q j).trans (cq (s - 2 + 1 + 1) (by omega) (by omega)))
    have hY' : ccoordSum (s - 2) bM (interpRec v) + ccoordSum (s - 2) bM (interpRec A') +
        ∑ i, ccoordSum (s - 2) bM (interpD A i) + ∑ i, ∑ j, ccoordSum (s - 2) bM (interpDD v i j) +
        ccoordSum (s - 2) bJ (jetField (interpRec v) (interpRec A) (interpD v)) ≤ cY' * X := by
      simp only [cY']; nlinarith
    have hY : ccoordSum (s - 2) bM (interpRec A) + ∑ i, ccoordSum (s - 2) bM (interpD v i) +
        ∑ i, ∑ j, ccoordSum (s - 2) bM (interpDD q i j) ≤ cY := by
      have : σ * KL * X ≤ σ * KL := by
        have := mul_nonneg hσ0 hKL; nlinarith
      have : 3 * (σ * X) ≤ 3 * σ := by nlinarith
      have : 9 * (σ * X) ≤ 9 * σ := by nlinarith
      simp only [cY]; nlinarith
    have hY0 : 0 ≤ ccoordSum (s - 2) bM (interpRec A) + ∑ i, ccoordSum (s - 2) bM (interpD v i) +
        ∑ i, ∑ j, ccoordSum (s - 2) bM (interpDD q i j) := by
      have := ccoordSum_nonneg (s - 2) bM (interpRec A)
      have := sum_nonneg fun i (_ : i ∈ univ) => ccoordSum_nonneg (s - 2) bM (interpD v i)
      have := sum_nonneg fun i (_ : i ∈ univ) => sum_nonneg fun j (_ : j ∈ univ) =>
        ccoordSum_nonneg (s - 2) bM (interpDD q i j)
      linarith
    have hY'0 : 0 ≤ ccoordSum (s - 2) bM (interpRec v) + ccoordSum (s - 2) bM (interpRec A') +
        ∑ i, ccoordSum (s - 2) bM (interpD A i) + ∑ i, ∑ j, ccoordSum (s - 2) bM (interpDD v i j) +
        ccoordSum (s - 2) bJ (jetField (interpRec v) (interpRec A) (interpD v)) := by
      have := ccoordSum_nonneg (s - 2) bM (interpRec v)
      have := ccoordSum_nonneg (s - 2) bM (interpRec A')
      have := sum_nonneg fun i (_ : i ∈ univ) => ccoordSum_nonneg (s - 2) bM (interpD A i)
      have := sum_nonneg fun i (_ : i ∈ univ) => sum_nonneg fun j (_ : j ∈ univ) =>
        ccoordSum_nonneg (s - 2) bM (interpDD v i j)
      have := ccoordSum_nonneg (s - 2) bJ (jetField (interpRec v) (interpRec A) (interpD v))
      linarith
    calc CR * ((ccoordSum (s - 2) bM (interpRec v) + ccoordSum (s - 2) bM (interpRec A') +
          ∑ i, ccoordSum (s - 2) bM (interpD A i) + ∑ i, ∑ j, ccoordSum (s - 2) bM (interpDD v i j) +
          ccoordSum (s - 2) bJ (jetField (interpRec v) (interpRec A) (interpD v))) *
          (1 + (ccoordSum (s - 2) bM (interpRec A) + ∑ i, ccoordSum (s - 2) bM (interpD v i) +
            ∑ i, ∑ j, ccoordSum (s - 2) bM (interpDD q i j))))
        ≤ CR * ((cY' * X) * (1 + cY)) := by gcongr
      _ = CRR * X := by simp only [CRR]; ring
  -- the samples of the linearized row
  have hRy' : ∀ y, R y = ((interpRowDeriv B q v y μ ν : ℝ) : ℂ) := fun y => hRy y
  refine ⟨R, hRy', memH_mono (by omega) hRm, ?_⟩
  have hsm : PeriodicGridSobolev.Sampling.sample N ⇑R =
      -cx (comp (bTerm B v) (upperOf μ ν).1.1 (upperOf μ ν).1.2) -
        errDeriv q v v A (upperOf μ ν).1.1 (upperOf μ ν).1.2 := by
    funext x
    change R (PeriodicGridSobolev.samplePt x) = _
    rw [hRy', hupper, hSmp (upperOf μ ν) x]
    all_goals rfl
  have hsmb : PeriodicGridSobolev.sobNorm (s - 3) (PeriodicGridSobolev.Sampling.sample N ⇑R) ≤
      (6 + CE) * h * X := by
    rw [hsm]
    refine (PeriodicGridSobolev.Moser.sobNorm_sub_le _ _ _).trans ?_
    rw [PeriodicGridSobolev.Moser.sobNorm_neg]
    have b1 := sobNorm_bTerm_mesh (s - 3) hB hv 0 (upperOf μ ν)
    rw [show s - 3 + 2 = s - 1 by omega] at b1
    have b2 := Xnorm_shift_le s (by omega) q v
    have b3 := hE N q v A hq hv hXE hAb (upperOf μ ν).1.1 (upperOf μ ν).1.2
    have b4 : 288 * (1 / 48) * (N : ℝ)⁻¹ * Xnorm (s - 1) v 0 ≤ 6 * h * X := by
      have : (N : ℝ)⁻¹ * Xnorm (s - 1) v 0 ≤ h * X := mul_le_mul_of_nonneg_left b2 hh
      nlinarith
    linarith
  have hRm1 : MemH (s - 3 + 1) ⇑R := by rw [show s - 3 + 1 = s - 2 by omega]; exact hRm
  have hal := halias N R hRm1
  rw [show s - 3 + 1 = s - 2 by omega] at hal
  have := mul_le_mul_of_nonneg_left hsmb (Real.sqrt_nonneg (pc (s - 3)))
  have := mul_le_mul_of_nonneg_left hRs' (by positivity : (0 : ℝ) ≤ Ca * (N : ℝ)⁻¹)
  calc sn (s - 3) ⇑R ≤ Real.sqrt (pc (s - 3)) * ((6 + CE) * h * X) + Ca * (N : ℝ)⁻¹ * (CRR * X) := by
        linarith
    _ = (Real.sqrt (pc (s - 3)) * (6 + CE) + Ca * CRR) * (N : ℝ)⁻¹ * X := by simp only [h]; ring

end Core

/-! ### The time derivative of the reduced residual -/

section ResidualDeriv

theorem analyticAt_trCoef_of_det {g : MetricRec} (hg : (Matrix.of g).det ≠ 0)
    (k : Fin 4 × Fin 4 × Fin 4 × Fin 4) : AnalyticAt ℝ (trCoef k) g := by
  have h1 : AnalyticAt ℝ (fun g : MetricRec => g k.1 k.2.1) g := by fun_prop
  have h2 : AnalyticAt ℝ (fun g : MetricRec => recInv g k.2.2.1 k.2.2.2) g :=
    analyticAt_inv_entry g hg _ _
  exact h1.mul h2

/-- The trace-reversed form of the reduced residual: `ρ_{ab}/2 - ½ Σ_{cd} g_{ab} g^{cd} ρ_{cd}/2`. -/
theorem reducedEinstein_eq_trForm (q v w : MetricRec) (qd vd : Fin 3 → MetricRec)
    (qdd : Fin 3 → Fin 3 → MetricRec) (hq : ∀ μ ν, q μ ν = q ν μ)
    (hdet : (Matrix.of (minkowski + q)).det ≠ 0)
    (hw : ∀ μ ν, w μ ν = w ν μ) (hvd : ∀ i μ ν, vd i μ ν = vd i ν μ)
    (hqdd : ∀ i j μ ν, qdd i j μ ν = qdd i j ν μ) (hqdd' : ∀ i j, qdd i j = qdd j i) (a b : Fin 4) :
    reducedEinstein (minkowski + q) (recInv (minkowski + q)) (metricJet (v, qd)) (ddArr w vd qdd)
      a b = normalRow q v w qd vd qdd a b / 2 -
        (1 / 2) * ∑ c, ∑ d, trCoef (a, b, c, d) (minkowski + q) *
          (normalRow q v w qd vd qdd c d / 2) := by
  rw [reducedEinstein_eq_traceRev_normalRow q v w qd vd qdd hq hdet hw hvd hqdd hqdd' a b,
    traceRev_apply']
  all_goals rfl

variable {N : ℕ} [NeZero N]

set_option maxHeartbeats 8000000 in
/-- **The time-differentiated half of `eq:supp-open-reduced-rate` for the law family**
(`lem:supp-open-reduced-consistency`, `B`-writer clause; the central writer is the mark `B = 0`).
For `s ≥ 5` there are `δ, C`, independent of the mesh `h = 1/N`, of the history and of the mark
`‖B‖_op ≤ 1/48` (`IsMark (1/48) B`, the closed ball `ℬ̄` of the library), such that for every
solution `(q, v)` of the `B`-writer on `[0, T]` staying in the top ball `‖X(t)‖_{X^s_h} ≤ ε ≤ δ`,
at every `t ∈ [0, T]` and for every component `(a, b)`, the reduced residual
`r_h = G(g_h) - 𝓗(g_h, c(g_h))` of the interpolant jet (acceleration slot the actual finite
acceleration `𝓘_h V_{B,h}(q, v)`) has a time derivative within `[0, T]` at `t` at every point of
`𝕋³`, and `‖∂ₜ r_{h,ab}(t)‖_{H^{s-3}} ≤ C h ε`. -/
theorem interp_reduced_residual_deriv_law (s : ℕ) (hs : 5 ≤ s) :
    ∃ δ > 0, ∃ C ≥ 0, ∀ (N : ℕ) [NeZero N] (B : Upper → Upper → ℝ) (T ε : ℝ)
      (q v : ℝ → Grid N → MetricRec), IsMark (1 / 48) B → ε ≤ δ →
      IsAccSolution (lawAccel B) T q v → (∀ t ∈ Set.Icc 0 T, Xnorm s (q t) (v t) ≤ ε) →
      ∀ t ∈ Set.Icc 0 T, ∀ a b : Fin 4, ∃ R : CT,
        (∀ y, HasDerivWithinAt (fun τ => ((reducedEinstein (minkowski + interpRec (q τ) y)
            (recInv (minkowski + interpRec (q τ) y))
            (metricJet (interpRec (v τ) y, fun i => interpD (q τ) i y))
            (ddArr (interpRec (symRec (lawAccel B (q τ) (v τ))) y)
              (fun i => interpD (v τ) i y) (fun i j => interpDD (q τ) i j y)) a b : ℝ) : ℂ))
            (R y) (Set.Icc 0 T) t) ∧
        MemH (s - 3) ⇑R ∧ sn (s - 3) ⇑R ≤ C * (N : ℝ)⁻¹ * ε := by
  obtain ⟨δ0, hδ0, K0, hK0, hcore⟩ := reduced_residual_of_rows s hs
  obtain ⟨r₀, hr₀, hchart⟩ := exists_det_chart
  obtain ⟨δD, hδD, CD, hCD, hDer⟩ := interp_rowDeriv_small s hs
  obtain ⟨δW, hδW, CW, hCW, hrows⟩ := interp_row_small_law s hs
  obtain ⟨δm, hδm, Km, hKm, hmul⟩ := coef_mul_family (s - 3) (by omega) trCoef analyticAt_trCoef
  obtain ⟨δt, hδt, Kt, hKt, hrate⟩ := rate_mul_family (s - 3) (by omega) bM minkowski trCoef
    analyticAt_trCoef
  have hS := supConst_nonneg
  set Ct : ℝ := 16 * Real.sqrt (pc (s - 3)) + 16 * Real.sqrt (pc (s - 2)) + 1
  have hCt : 0 ≤ Ct := by positivity
  set δ : ℝ := min (min (min δ0 δD) (min δW (r₀ / (2 * (supConst + 1)))))
    (min (min (δm / (Ct + 1)) (δt / (Ct + 1))) 1)
  have hδ : 0 < δ := by positivity
  refine ⟨δ, hδ, 1 / 2 * CD + 8 * (Kt * Ct * CW + Km * CD), by positivity,
    fun N _ B T ε q v hB hε hsol hXall t ht a b => ?_⟩
  -- the state at time `t`
  obtain ⟨hqs, hvs, hqd, hvd⟩ := hsol t ht
  set X := Xnorm s (q t) (v t)
  have hX0 : 0 ≤ X := Xnorm_nonneg _ _ _
  have hXε : X ≤ ε := hXall t ht
  have hXδ : X ≤ δ := hXε.trans hε
  have hε0 : 0 ≤ ε := hX0.trans hXε
  have hX0δ : X ≤ δ0 := hXδ.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hXD : X ≤ δD := hXδ.trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hXW : X ≤ δW := hXδ.trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hXc : X ≤ r₀ / (2 * (supConst + 1)) :=
    hXδ.trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hXm : X ≤ δm / (Ct + 1) :=
    hXδ.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hXt : X ≤ δt / (Ct + 1) :=
    hXδ.trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hX1 : X ≤ 1 := hXδ.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hdetτ : ∀ τ ∈ Set.Icc 0 T, ∀ y, (Matrix.of (minkowski + interpRec (q τ) y)).det ≠ 0 :=
    fun τ hτ => (hcore N (q τ) (v τ) 0 (hsol τ hτ).1 (hsol τ hτ).2.1 (fun _ _ _ => rfl)
      (((hXall τ hτ).trans hε).trans ((min_le_left _ _).trans ((min_le_left _ _).trans
        (min_le_left _ _))))).1
  have hdet := hdetτ t ht
  have hqx : ∀ x, ‖(minkowski + q t x) - minkowski‖ < r₀ := by
    intro x
    rw [add_sub_cancel_left]
    have h1 := norm_q_le s (by omega) hqs (v t) x
    have h2 : supConst * X ≤ supConst * (r₀ / (2 * (supConst + 1))) :=
      mul_le_mul_of_nonneg_left hXc hS
    have h3 : supConst * (r₀ / (2 * (supConst + 1))) < r₀ := by
      rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  -- the derivatives of the history (all components, within `[0, T]`)
  have hQ : ∀ x μ ν, HasDerivWithinAt (fun τ => q τ x μ ν) (v t x μ ν) (Set.Icc 0 T) t :=
    fun x μ ν => (hasDerivAt_pi.1 (hasDerivAt_pi.1 (hqd x) μ) ν).hasDerivWithinAt
  have hV : ∀ x μ ν, HasDerivWithinAt (fun τ => v τ x μ ν) (accRec B (q t) (v t) x μ ν)
      (Set.Icc 0 T) t := by
    intro x μ ν
    refine (hvd x (upperOf μ ν)).hasDerivWithinAt.congr (fun σ hσ => ?_) ?_
    · exact (congrFun (comp_upperOf (hsol σ hσ).2.1 μ ν) x).symm
    · exact (congrFun (comp_upperOf hvs μ ν) x).symm
  have hA : ∀ x μ ν, HasDerivWithinAt (fun τ => accRec B (q τ) (v τ) x μ ν)
      (accDRec B (q t) (v t) x μ ν) (Set.Icc 0 T) t := fun x μ ν =>
    hasDerivWithinAt_lawAccel B hQ hV (fun y => (hchart _ (hqx y)).1) (fun y => (hchart _ (hqx y)).2)
      x (upperOf μ ν).1.1 (upperOf μ ν).1.2
  have dQ := hasDerivWithinAt_interpRec' hQ
  have dV := hasDerivWithinAt_interpRec' hV
  have dW := hasDerivWithinAt_interpRec' hA
  have dQd := hasDerivWithinAt_interpD' hQ
  have dVd := hasDerivWithinAt_interpD' hV
  have dQdd := hasDerivWithinAt_interpDD' hQ
  have hrow : ∀ y c d, HasDerivWithinAt (fun τ => normalRow (interpRec (q τ) y)
      (interpRec (v τ) y) (interpRec (accRec B (q τ) (v τ)) y) (fun i => interpD (q τ) i y)
      (fun i => interpD (v τ) i y) (fun i j => interpDD (q τ) i j y) c d)
      (interpRowDeriv B (q t) (v t) y c d) (Set.Icc 0 T) t := fun y c d =>
    hasDerivWithinAt_normalRow (q := fun τ => interpRec (q τ) y)
      (v := fun τ => interpRec (v τ) y) (w := fun τ => interpRec (accRec B (q τ) (v τ)) y)
      (qd := fun τ i => interpD (q τ) i y) (vd := fun τ i => interpD (v τ) i y)
      (qdd := fun τ i j => interpDD (q τ) i j y) (hdet y) (dQ y) (dV y) (dW y)
      (fun i => dQd i y) (fun i => dVd i y) (fun i j => dQdd i j y) c d
  -- the trace-reversed form along the history
  set ρ : ℝ → T3 → Fin 4 → Fin 4 → ℝ := fun τ y c d => normalRow (interpRec (q τ) y)
    (interpRec (v τ) y) (interpRec (accRec B (q τ) (v τ)) y) (fun i => interpD (q τ) i y)
    (fun i => interpD (v τ) i y) (fun i j => interpDD (q τ) i j y) c d with hρdef
  have hform : ∀ y, ∀ τ ∈ Set.Icc 0 T, ((reducedEinstein (minkowski + interpRec (q τ) y)
      (recInv (minkowski + interpRec (q τ) y))
      (metricJet (interpRec (v τ) y, fun i => interpD (q τ) i y))
      (ddArr (interpRec (symRec (lawAccel B (q τ) (v τ))) y)
        (fun i => interpD (v τ) i y) (fun i j => interpDD (q τ) i j y)) a b : ℝ) : ℂ) =
      ((ρ τ y a b / 2 - (1 / 2) * ∑ c, ∑ d, trCoef (a, b, c, d)
        (minkowski + interpRec (q τ) y) * (ρ τ y c d / 2) : ℝ) : ℂ) := by
    intro y τ hτ
    obtain ⟨hqτ, hvτ, -, -⟩ := hsol τ hτ
    exact congrArg (fun r : ℝ => (r : ℂ)) (reducedEinstein_eq_trForm (interpRec (q τ) y)
      (interpRec (v τ) y) (interpRec (symRec (lawAccel B (q τ) (v τ))) y)
      (fun i => interpD (q τ) i y) (fun i => interpD (v τ) i y) (fun i j => interpDD (q τ) i j y)
      (interpRec_symm hqτ y) (hdetτ τ hτ y)
      (interpRec_symm (isSymRec_symRec _) y) (fun i => interpD_symm hvτ i y)
      (fun i j => interpDD_symm hqτ i j y) (fun i j => by rw [interpDD_comm]) a b)
  have hformD : ∀ y, HasDerivWithinAt (fun τ => ((ρ τ y a b / 2 - (1 / 2) * ∑ c, ∑ d,
      trCoef (a, b, c, d) (minkowski + interpRec (q τ) y) * (ρ τ y c d / 2) : ℝ) : ℂ))
      (((interpRowDeriv B (q t) (v t) y a b / 2 - (1 / 2) * ∑ c, ∑ d,
        prodT (trCoef (a, b, c, d)) (interpRec (q t) y) (interpRec (v t) y) (ρ t y c d / 2)
          (interpRowDeriv B (q t) (v t) y c d / 2) : ℝ) : ℂ)) (Set.Icc 0 T) t := by
    intro y
    have h1 := (hrow y a b).div_const 2
    have h2 := HasDerivWithinAt.fun_sum (u := univ) fun c _ =>
      HasDerivWithinAt.fun_sum (u := univ) fun d _ =>
        hasDerivWithinAt_prod (A := trCoef (a, b, c, d))
          (analyticAt_trCoef_of_det (hdet y) _).differentiableAt (dQ y) ((hrow y c d).div_const 2)
    exact (h1.sub (h2.const_mul (1 / 2))).ofReal_comp
  -- the rows and the linearized rows as `H^r` fields
  have hsym : ∀ y c d, ρ t y c d = ρ t y d c := fun y c d =>
    normalRow_symm _ _ _ _ _ _ (interpRec_symm hqs y) (hdet y) (interpRec_symm hvs y)
      (fun i => interpD_symm hqs i y) (interpRec_symm (isSymRec_symRec _) y)
      (fun i => interpD_symm hvs i y) (fun i j => interpDD_symm hqs i j y)
      (fun i j => by rw [interpDD_comm]) c d
  have hrowsU := fun κ : Upper => hrows N (1 / 48) B hB (by norm_num) (q t) (v t) hqs hvs hXW κ
  choose Rκ hRκ hRκm hRκs using hrowsU
  set P : Fin 4 → Fin 4 → CT := fun c d => Rκ (upperOfPair c d)
  have hP : ∀ c d y, P c d y = ((ρ t y c d : ℝ) : ℂ) := by
    intro c d y
    have e := congrFun (hRκ (upperOfPair c d)) y
    simp only [P, e, rowF]
    simp only [upperOfPair]
    rcases le_total c d with hcd | hcd
    · rw [min_eq_left hcd, max_eq_right hcd]; rfl
    · rw [min_eq_right hcd, max_eq_left hcd]
      exact congrArg _ (hsym y d c)
  have hPm : ∀ c d, MemH (s - 2) ⇑(P c d) := fun c d => hRκm _
  have hPs : ∀ c d, sn (s - 2) ⇑(P c d) ≤ CW * (N : ℝ)⁻¹ * X := fun c d => hRκs _
  have hD := fun c d => hDer N B (q t) (v t) hB hqs hvs hXD c d
  choose D hDy hDm hDs using hD
  -- the trace-reversal products
  have hQm : ∀ k, MemH (s - 3) ⇑(ccoord bM (interpRec (q t)) k) := memH_interpRec_all _ _
  have hQs : ccoordSum (s - 3) bM (interpRec (q t)) ≤ Ct * X := by
    refine (ccoordSum_interpRec_le (s - 3) s hqs (v t) (by omega)).trans ?_
    have : 16 * Real.sqrt (pc (s - 3)) ≤ Ct := by
      have := Real.sqrt_nonneg (pc (s - 2)); simp only [Ct]; linarith
    nlinarith
  have hVs : ccoordSum (s - 3) bM (interpRec (v t)) ≤ Ct * X := by
    refine (ccoordSum_interpRec_v_le (s - 3) s (q t) hvs (by omega)).trans ?_
    have : 16 * Real.sqrt (pc (s - 3)) ≤ Ct := by
      have := Real.sqrt_nonneg (pc (s - 2)); simp only [Ct]; linarith
    nlinarith
  have hQm' : ccoordSum (s - 3) bM (interpRec (q t)) ≤ δm := by
    refine hQs.trans ?_; rw [le_div_iff₀ (by positivity)] at hXm; nlinarith
  have hQt' : ccoordSum (s - 3) bM (interpRec (q t)) ≤ δt := by
    refine hQs.trans ?_; rw [le_div_iff₀ (by positivity)] at hXt; nlinarith
  have hT1 := fun c d => hrate (a, b, c, d) (interpRec (q t)) hQm hQt' (interpRec (v t))
    (memH_interpRec_all _ _) ((2⁻¹ : ℂ) • P c d) (memH_smul _ (memH_mono (by omega) (hPm c d)))
  have hT2 := fun c d => hmul (a, b, c, d) (interpRec (q t)) hQm hQm' ((2⁻¹ : ℂ) • D c d)
    (memH_smul _ (hDm c d))
  choose T1 hT1y hT1m hT1s using hT1
  choose T2 hT2y hT2m hT2s using hT2
  set Rf : CT := (2⁻¹ : ℂ) • D a b - (2⁻¹ : ℂ) • ∑ c, ∑ d, (T1 c d + T2 c d)
  have hS1 : ∀ c, MemH (s - 3) ⇑(∑ d, (T1 c d + T2 c d)) ∧
      sn (s - 3) ⇑(∑ d, (T1 c d + T2 c d)) ≤ ∑ d, sn (s - 3) ⇑(T1 c d + T2 c d) :=
    fun c => sn_sum_le' univ fun d => memH_add (hT1m c d) (hT2m c d)
  have hS2 := sn_sum_le' univ fun c => (hS1 c).1
  refine ⟨Rf, fun y => ?_, ?_, ?_⟩
  · refine ((hformD y).congr (fun τ hτ => hform y τ hτ) (hform y t ht)).congr_deriv ?_
    simp only [Rf, ContinuousMap.sub_apply, ContinuousMap.smul_apply, ContinuousMap.coe_sum,
      Finset.sum_apply, ContinuousMap.add_apply, hT1y, hT2y, hDy, smul_eq_mul, hP, prodT]
    push_cast
    simp only [mul_sum, div_eq_inv_mul, mul_one]
  · exact memH_sub (memH_smul _ (hDm a b)) (memH_smul _ hS2.1)
  · have hn2 : ‖(2⁻¹ : ℂ)‖ = 1 / 2 := by rw [norm_inv]; norm_num
    have h1 := sn_sub_le' (memH_smul (2⁻¹ : ℂ) (hDm a b)) (memH_smul (2⁻¹ : ℂ) hS2.1)
    rw [sn_smul, sn_smul, hn2] at h1
    have hterm : ∀ c d, sn (s - 3) ⇑(T1 c d + T2 c d) ≤
        (Kt * Ct * CW + Km * CD) * (N : ℝ)⁻¹ * X := by
      intro c d
      refine (sn_add_le' (hT1m c d) (hT2m c d)).trans ?_
      have e1 : sn (s - 3) ⇑((2⁻¹ : ℂ) • P c d) ≤ CW * (N : ℝ)⁻¹ * X := by
        rw [sn_smul, hn2]
        have := (sn_mono' (show s - 3 ≤ s - 2 by omega) (hPm c d)).trans (hPs c d)
        have := sn_nonneg (s - 3) ⇑(P c d)
        linarith
      have e2 : sn (s - 3) ⇑((2⁻¹ : ℂ) • D c d) ≤ CD * (N : ℝ)⁻¹ * X := by
        rw [sn_smul, hn2]
        have := hDs c d
        have := sn_nonneg (s - 3) ⇑(D c d)
        linarith
      have f1 : sn (s - 3) ⇑(T1 c d) ≤ Kt * (Ct * X) * (CW * (N : ℝ)⁻¹ * X) :=
        (hT1s c d).trans (by
          have := sn_nonneg (s - 3) ⇑((2⁻¹ : ℂ) • P c d)
          gcongr)
      have f2 : sn (s - 3) ⇑(T2 c d) ≤ Km * (CD * (N : ℝ)⁻¹ * X) :=
        (hT2s c d).trans (mul_le_mul_of_nonneg_left e2 hKm)
      have hXX : Kt * (Ct * X) * (CW * (N : ℝ)⁻¹ * X) ≤ Kt * Ct * CW * (N : ℝ)⁻¹ * X := by
        have : 0 ≤ Kt * Ct * CW * (N : ℝ)⁻¹ := by positivity
        have e : Kt * (Ct * X) * (CW * (N : ℝ)⁻¹ * X) = Kt * Ct * CW * (N : ℝ)⁻¹ * (X * X) := by ring
        rw [e]
        exact mul_le_mul_of_nonneg_left (by nlinarith) this
      nlinarith
    have hsum : sn (s - 3) ⇑(∑ c, ∑ d, (T1 c d + T2 c d)) ≤
        16 * ((Kt * Ct * CW + Km * CD) * (N : ℝ)⁻¹ * X) := by
      refine hS2.2.trans ?_
      calc ∑ c, sn (s - 3) ⇑(∑ d, (T1 c d + T2 c d)) ≤
            ∑ _c : Fin 4, ∑ _d : Fin 4, (Kt * Ct * CW + Km * CD) * (N : ℝ)⁻¹ * X :=
            sum_le_sum fun c _ => (hS1 c).2.trans (sum_le_sum fun d _ => hterm c d)
        _ = _ := by simp; ring
    have hab := hDs a b
    have hN : 0 ≤ (N : ℝ)⁻¹ := by positivity
    have hmono : (1 / 2 * CD + 8 * (Kt * Ct * CW + Km * CD)) * (N : ℝ)⁻¹ * X ≤
        (1 / 2 * CD + 8 * (Kt * Ct * CW + Km * CD)) * (N : ℝ)⁻¹ * ε := by
      have : 0 ≤ (1 / 2 * CD + 8 * (Kt * Ct * CW + Km * CD)) * (N : ℝ)⁻¹ := by positivity
      exact mul_le_mul_of_nonneg_left hXε this
    calc sn (s - 3) ⇑Rf ≤ 1 / 2 * sn (s - 3) ⇑(D a b) +
          1 / 2 * sn (s - 3) ⇑(∑ c, ∑ d, (T1 c d + T2 c d)) := h1
      _ ≤ 1 / 2 * (CD * (N : ℝ)⁻¹ * X) + 1 / 2 * (16 * ((Kt * Ct * CW + Km * CD) * (N : ℝ)⁻¹ * X)) := by
          gcongr
      _ = (1 / 2 * CD + 8 * (Kt * Ct * CW + Km * CD)) * (N : ℝ)⁻¹ * X := by ring
      _ ≤ _ := hmono

end ResidualDeriv

/-! ### `lem:supp-open-reduced-consistency` -/

section Consistency

/-- **`lem:supp-open-reduced-consistency`, `B`-writer clause** (`eq:supp-open-reduced-rate`
uniformly on the closed mark ball `‖B‖_op ≤ 1/48`): for `s ≥ 5` there are `δ, C`, independent of
the mesh `h = 1/N`, of the history, of `T` and of the mark, such that every solution of the
`B`-writer on `[0, T]` in the top ball `‖X(t)‖_{X^s_h} ≤ ε ≤ δ` has, at every `t ∈ [0, T]` and for
every component, `‖r_{h,ab}(t)‖_{H^{s-2}} ≤ C h ε` and `‖∂ₜ r_{h,ab}(t)‖_{H^{s-3}} ≤ C h ε`, where
`r_h` is the complete reduced residual `G(g_h) - 𝓗(g_h, c(g_h))` of the interpolant jet
(`g_h = η + 𝓘_h q`, acceleration slot the actual finite acceleration `𝓘_h V_{B,h}(q, v)`) and
`∂ₜ r_h` its time derivative within `[0, T]`. -/
theorem supp_open_reduced_consistency_law (s : ℕ) (hs : 5 ≤ s) :
    ∃ δ > 0, ∃ C ≥ 0, ∀ (N : ℕ) [NeZero N] (B : Upper → Upper → ℝ) (T ε : ℝ)
      (q v : ℝ → Grid N → MetricRec), IsMark (1 / 48) B → ε ≤ δ →
      IsAccSolution (lawAccel B) T q v → (∀ t ∈ Set.Icc 0 T, Xnorm s (q t) (v t) ≤ ε) →
      ∀ t ∈ Set.Icc 0 T, ∀ a b : Fin 4,
        (∃ R : CT, (∀ y, R y = ((reducedEinstein (minkowski + interpRec (q t) y)
            (recInv (minkowski + interpRec (q t) y))
            (metricJet (interpRec (v t) y, fun i => interpD (q t) i y))
            (ddArr (interpRec (symRec (lawAccel B (q t) (v t))) y)
              (fun i => interpD (v t) i y) (fun i j => interpDD (q t) i j y)) a b : ℝ) : ℂ)) ∧
          MemH (s - 2) ⇑R ∧ sn (s - 2) ⇑R ≤ C * (N : ℝ)⁻¹ * ε) ∧
        ∃ R : CT,
          (∀ y, HasDerivWithinAt (fun τ => ((reducedEinstein (minkowski + interpRec (q τ) y)
              (recInv (minkowski + interpRec (q τ) y))
              (metricJet (interpRec (v τ) y, fun i => interpD (q τ) i y))
              (ddArr (interpRec (symRec (lawAccel B (q τ) (v τ))) y)
                (fun i => interpD (v τ) i y) (fun i j => interpDD (q τ) i j y)) a b : ℝ) : ℂ))
              (R y) (Set.Icc 0 T) t) ∧
          MemH (s - 3) ⇑R ∧ sn (s - 3) ⇑R ≤ C * (N : ℝ)⁻¹ * ε := by
  obtain ⟨δ1, hδ1, C1, hC1, h1⟩ := interp_reduced_residual_small_law s hs
  obtain ⟨δ2, hδ2, C2, hC2, h2⟩ := interp_reduced_residual_deriv_law s hs
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, C1 + C2, by positivity,
    fun N _ B T ε q v hB hε hsol hX t ht a b => ⟨?_, ?_⟩⟩
  · obtain ⟨hqs, hvs, -, -⟩ := hsol t ht
    have hXt := hX t ht
    obtain ⟨-, h1'⟩ := h1 N (1 / 48) B hB (by norm_num) (q t) (v t) hqs hvs
      (hXt.trans (hε.trans (min_le_left _ _)))
    obtain ⟨R, hR, hRm, hRs⟩ := h1' a b
    refine ⟨R, hR, hRm, hRs.trans ?_⟩
    have hN : 0 ≤ (N : ℝ)⁻¹ := by positivity
    have hε0 : 0 ≤ ε := (Xnorm_nonneg _ _ _).trans hXt
    calc C1 * (N : ℝ)⁻¹ * Xnorm s (q t) (v t) ≤ C1 * (N : ℝ)⁻¹ * ε := by gcongr
      _ ≤ (C1 + C2) * (N : ℝ)⁻¹ * ε := by gcongr; linarith
  · obtain ⟨R, hR, hRm, hRs⟩ := h2 N B T ε q v hB (hε.trans (min_le_right _ _)) hsol hX t ht a b
    refine ⟨R, hR, hRm, hRs.trans ?_⟩
    have hε0 : 0 ≤ ε := (Xnorm_nonneg _ _ _).trans (hX t ht)
    have hN : 0 ≤ (N : ℝ)⁻¹ := by positivity
    gcongr
    linarith

theorem isAccSolution_lawAccel_zero {N : ℕ} [NeZero N] {T : ℝ} {q v : ℝ → Grid N → MetricRec}
    (h : IsWriterSolution T q v) : IsAccSolution (lawAccel (fun _ _ => 0)) T q v := by
  have e : lawAccel (N := N) (fun _ _ => 0) = harmonicWriterAcceleration := by
    funext q v; exact lawAccel_zero q v
  rw [e]
  exact h

/-- **`lem:supp-open-reduced-consistency`** (`eq:supp-open-reduced-rate`, unforced central
writer): for `s ≥ 5` there are `δ, C`, independent of the mesh `h = 1/N`, of the history and of
`T`, such that every solution of the open writer on `[0, T]` in the top ball
`‖X(t)‖_{X^s_h} ≤ ε ≤ δ` satisfies, at every `t ∈ [0, T]` and for every component,
`‖r_{h,ab}(t)‖_{H^{s-2}} ≤ C h ε` and `‖∂ₜ r_{h,ab}(t)‖_{H^{s-3}} ≤ C h ε`, where
`r_h = G(g_h) - 𝓗(g_h, c(g_h))` is the complete reduced residual of the interpolant jet of
`g_h = η + 𝓘_h q` (acceleration slot `𝓘_h V_{0,h}(q, v)`, the actual finite acceleration) and
`∂ₜ r_h` its time derivative within `[0, T]` (the mark `B = 0` of
`supp_open_reduced_consistency_law`). -/
theorem supp_open_reduced_consistency (s : ℕ) (hs : 5 ≤ s) :
    ∃ δ > 0, ∃ C ≥ 0, ∀ (N : ℕ) [NeZero N] (T ε : ℝ) (q v : ℝ → Grid N → MetricRec), ε ≤ δ →
      IsWriterSolution T q v → (∀ t ∈ Set.Icc 0 T, Xnorm s (q t) (v t) ≤ ε) →
      ∀ t ∈ Set.Icc 0 T, ∀ a b : Fin 4,
        (∃ R : CT, (∀ y, R y = ((reducedEinstein (minkowski + interpRec (q t) y)
            (recInv (minkowski + interpRec (q t) y))
            (metricJet (interpRec (v t) y, fun i => interpD (q t) i y))
            (ddArr (interpRec (symRec (harmonicWriterAcceleration (q t) (v t))) y)
              (fun i => interpD (v t) i y) (fun i j => interpDD (q t) i j y)) a b : ℝ) : ℂ)) ∧
          MemH (s - 2) ⇑R ∧ sn (s - 2) ⇑R ≤ C * (N : ℝ)⁻¹ * ε) ∧
        ∃ R : CT,
          (∀ y, HasDerivWithinAt (fun τ => ((reducedEinstein (minkowski + interpRec (q τ) y)
              (recInv (minkowski + interpRec (q τ) y))
              (metricJet (interpRec (v τ) y, fun i => interpD (q τ) i y))
              (ddArr (interpRec (symRec (harmonicWriterAcceleration (q τ) (v τ))) y)
                (fun i => interpD (v τ) i y) (fun i j => interpDD (q τ) i j y)) a b : ℝ) : ℂ))
              (R y) (Set.Icc 0 T) t) ∧
          MemH (s - 3) ⇑R ∧ sn (s - 3) ⇑R ≤ C * (N : ℝ)⁻¹ * ε := by
  obtain ⟨δ, hδ, C, hC, h⟩ := supp_open_reduced_consistency_law s hs
  refine ⟨δ, hδ, C, hC, fun N _ T ε q v hε hsol hX t ht a b => ?_⟩
  have := h N (fun _ _ => 0) T ε q v isMark_zero hε (isAccSolution_lawAccel_zero hsol) hX t ht a b
  simp only [lawAccel_zero] at this
  exact this

/-- Non-vacuity of `supp_open_reduced_consistency` and `supp_open_reduced_consistency_law`: the
flat history solves every member of the law family (in particular the open writer) on every
interval and lies in every top ball (`ε = 0`). -/
example (N : ℕ) [NeZero N] (s : ℕ) (T : ℝ) :
    IsWriterSolution T (fun _ => (0 : Grid N → MetricRec)) (fun _ => 0) ∧
      IsAccSolution (lawAccel (fun _ _ => 0)) T (fun _ => (0 : Grid N → MetricRec)) (fun _ => 0) ∧
      ∀ t ∈ Set.Icc 0 T, Xnorm s ((fun _ => (0 : Grid N → MetricRec)) t)
        ((fun _ => (0 : Grid N → MetricRec)) t) ≤ 0 :=
  ⟨isWriterSolution_zero N T, isAccSolution_lawAccel_zero (isWriterSolution_zero N T),
    fun _ _ => (Xnorm_zero' N s).le⟩

end Consistency

end

end RenewalGeometry.OpenWriterReducedResidualDeriv
