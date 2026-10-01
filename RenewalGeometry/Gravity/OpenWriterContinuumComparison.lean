/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.TorusSobolevTransfer
import RenewalGeometry.Gravity.OpenWriterLawDifference
import RenewalGeometry.Gravity.OpenWriterTimeJets

/-!
# The continuum harmonic normal row and the sampled comparison with the open writer
  (`eq:main-harmonic-normal-row`, `lem:supp-open-continuum-comparison`;
  emergent-spacetime manuscript)

Continuum fields on `𝕋³ = UnitAddTorus (Fin 3)` are continuous `4 × 4` record fields; spatial
derivatives are classical coordinate-line derivatives (`TorusSobolevTransfer.IsLineDeriv`), and
Sobolev norms are the trigonometric `H^r` norms of the components.

* `normalRow` — the harmonic normal row `a(g) q_tt + 2bⁱ(g) ∂ᵢq_t - c^{ij}(g) ∂ᵢ∂ⱼq - F(g, ∂g)`
  of `eq:main-harmonic-normal-row` at a point, with the explicit harmonic first-jet source
  `F = harmonicSource`; `IsContJet` — the line-derivative relations of a continuum jet
  `(Q, V, ∂Q, ∂V, ∂²Q)`; `contTop` — the continuum top size
  `Σ_k ‖Q_k‖_{H^{s+1}} + Σ_k ‖V_k‖_{H^s}`.
* `normalRow_identity` — the continuum chain-rule decomposition of the normal row that matches
  the divergence, skew-transport and compensator placements of the writer.
* `sampled_row_consistency` (**sampled consistency of the writer**): for a continuum jet in the
  small top ball, the sampled record `𝒮_h(Q, V)` with sampled acceleration `𝒮_h W` satisfies the
  mass row of the open writer up to the sampled continuum residual and an error
  `‖a(q)(𝒮_h W - V_{0,h}) - 𝒮_h ρ‖_{s-2,h} ≤ C h ‖(Q, V)‖_top`; `sampled_force_bound`.
* `IsContSolution` (continuum solutions of the harmonic normal row on `[0, T]`) and
  `continuum_comparison` (**`lem:supp-open-continuum-comparison`**): the sampled continuum solution
  and the writer solution differ by `C e^{Kt}(e_{0,h} + (1 + t) h ε)` in `X^{s-2}_h`, and their
  accelerations by the same bound in `H^{s-3}_h`; non-vacuity via `isContSolution_flat`.
-/

open Finset Filter Topology UnitAddTorus
open scoped BigOperators Real

namespace RenewalGeometry.OpenWriterContinuum

open TorusSobolevTransfer OpenWriterLifespan OpenWriterEnergyEstimate OpenWriterChart
  OpenWriterEnergy OpenWriterGridBridge RootParityConnector PeriodicGridSobolev.Composition
  HarmonicWriter

noncomputable section

set_option linter.unusedSectionVars false

attribute [local irreducible] harmA harmB harmC compensatorMap

/-- The unit torus `𝕋³`. -/
abbrev T3 := UnitAddTorus (Fin 3)

/-! ### Continuum record fields -/

/-- The complexified `(μ, ν)` component of a continuous record field. -/
def cmp (F : C(T3, MetricRec)) (μ ν : Fin 4) : CT :=
  ⟨fun x => ((F x μ ν : ℝ) : ℂ), Complex.continuous_ofReal.comp
    ((continuous_apply ν).comp ((continuous_apply μ).comp F.continuous))⟩

@[simp] theorem cmp_apply (F : C(T3, MetricRec)) (μ ν : Fin 4) (x : T3) :
    cmp F μ ν x = ((F x μ ν : ℝ) : ℂ) := rfl

theorem ccoord_bM (F : C(T3, MetricRec)) (k : Σ _ : Fin 4, Fin 4) :
    ccoord bM F k = cmp F k.1 k.2 := by
  ext x; simp [bM_repr]

/-- Grid samples of a record field. -/
def sampleRec (N : ℕ) [NeZero N] (F : T3 → MetricRec) : Grid N → MetricRec :=
  fun x => F (PeriodicGridSobolev.samplePt x)

theorem cx_comp_sampleRec (N : ℕ) [NeZero N] (F : C(T3, MetricRec)) (μ ν : Fin 4) :
    cx (comp (sampleRec N ⇑F) μ ν) = PeriodicGridSobolev.Sampling.sample N ⇑(cmp F μ ν) := rfl

/-- The continuum top size `Σ_k ‖Q_k‖_{H^{s+1}} + Σ_k ‖V_k‖_{H^s}` (over the sixteen components). -/
def contTop (s : ℕ) (Q V : C(T3, MetricRec)) : ℝ := ccoordSum (s + 1) bM Q + ccoordSum s bM V

theorem contTop_nonneg (s : ℕ) (Q V : C(T3, MetricRec)) : 0 ≤ contTop s Q V :=
  add_nonneg (ccoordSum_nonneg _ _ _) (ccoordSum_nonneg _ _ _)

/-- **The harmonic normal row** `eq:main-harmonic-normal-row` at a point:
`a(g) q_tt + 2bⁱ(g) ∂ᵢq_t - c^{ij}(g) ∂ᵢ∂ⱼq - F(g, ∂g)`, `g = η + q`, with `a = -g^{00}`,
`bⁱ = -g^{0i}`, `c^{ij} = g^{ij}` and the explicit first-jet source `F = harmonicSource`
(`∂₀g = q_t`, `∂ᵢg = ∂ᵢq`).  The arguments are `q`, `v = q_t`, `w = q_tt`, `qd i = ∂ᵢq`,
`vd i = ∂ᵢq_t`, `qdd i j = ∂ᵢ∂ⱼq`. -/
def normalRow (q v w : MetricRec) (qd vd : Fin 3 → MetricRec) (qdd : Fin 3 → Fin 3 → MetricRec) :
    MetricRec :=
  harmA (minkowski + q) • w + (2 : ℝ) • ∑ i, harmB i (minkowski + q) • vd i -
    ∑ i, ∑ j, harmC i j (minkowski + q) • qdd i j - harmonicSource (minkowski + q) (v, qd)

/-- The line-derivative relations of a continuum jet: `Qd i = ∂ᵢQ`, `Qdd i j = ∂ᵢ(Qd j)`,
`Vd i = ∂ᵢV` (classical coordinate derivatives on `𝕋³`). -/
structure IsContJet (Q V : C(T3, MetricRec)) (Qd Vd : Fin 3 → C(T3, MetricRec))
    (Qdd : Fin 3 → Fin 3 → C(T3, MetricRec)) : Prop where
  dQ : ∀ i, IsLineDeriv i ⇑Q ⇑(Qd i)
  dQd : ∀ i j, IsLineDeriv i ⇑(Qd j) ⇑(Qdd i j)
  dV : ∀ i, IsLineDeriv i ⇑V ⇑(Vd i)

theorem isLineDeriv_cmp {i : Fin 3} {F F' : C(T3, MetricRec)} (h : IsLineDeriv i ⇑F ⇑F')
    (μ ν : Fin 4) : IsLineDeriv i ⇑(cmp F μ ν) ⇑(cmp F' μ ν) := by
  intro x
  have h1 := hasDerivAt_pi.mp (h x) μ
  have h2 := hasDerivAt_pi.mp h1 ν
  exact h2.ofReal_comp

/-- **Continuum chain-rule decomposition of the normal row**:
`a w - ρ = Σ_{ij} ∂ᵢ(c^{ij} ∂ⱼq) - Σᵢ bⁱ ∂ᵢv - Σᵢ ∂ᵢ(bⁱ v) + 𝖦(q, v, ∂q)` with the
derivatives of the products written out by the chain rule. -/
theorem normalRow_identity (q v w : MetricRec) (qd vd : Fin 3 → MetricRec)
    (qdd : Fin 3 → Fin 3 → MetricRec) (μ ν : Fin 4) :
    harmA (minkowski + q) * w μ ν - normalRow q v w qd vd qdd μ ν =
      ∑ i, ∑ j, (fderiv ℝ (harmC i j) (minkowski + q) (qd i) * qd j μ ν +
          harmC i j (minkowski + q) * qdd i j μ ν) -
        ∑ i, harmB i (minkowski + q) * vd i μ ν -
        ∑ i, (fderiv ℝ (harmB i) (minkowski + q) (qd i) * v μ ν +
          harmB i (minkowski + q) * vd i μ ν) +
        compensatorMap (q, v, qd) μ ν := by
  rw [compensatorMap_apply]
  simp only [normalRow, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_apply, sum_add_distrib]
  ring

/-! ### Helper estimates -/

theorem sn_cmp_le_ccoordSum (r : ℕ) (F : C(T3, MetricRec)) (μ ν : Fin 4) :
    sn r ⇑(cmp F μ ν) ≤ ccoordSum r bM F := by
  rw [show cmp F μ ν = ccoord bM F ⟨μ, ν⟩ from (ccoord_bM F ⟨μ, ν⟩).symm]
  exact single_le_sum (f := fun k : Σ _ : Fin 4, Fin 4 => sn r ⇑(ccoord bM F k))
    (fun _ _ => sn_nonneg _ _) (mem_univ _)

theorem memH_cmp {r : ℕ} {F : C(T3, MetricRec)} (h : ∀ k, MemH r ⇑(ccoord bM F k)) (μ ν : Fin 4) :
    MemH r ⇑(cmp F μ ν) := by
  have := h ⟨μ, ν⟩
  rwa [ccoord_bM] at this

theorem ccoordSum_mono {r r' : ℕ} (h : r ≤ r') {F : C(T3, MetricRec)}
    (hF : ∀ k, MemH r' ⇑(ccoord bM F k)) : ccoordSum r bM F ≤ ccoordSum r' bM F :=
  sum_le_sum fun k _ => sn_mono' h (hF k)

/-- Derivative fields of `H^{r+1}` record fields are in `H^r`, with
`Σ_k ‖∂ᵢF_k‖_{H^r} ≤ Σ_k ‖F_k‖_{H^{r+1}}`. -/
theorem ccoordSum_deriv_le {r : ℕ} {i : Fin 3} {F F' : C(T3, MetricRec)}
    (hd : IsLineDeriv i ⇑F ⇑F') (hF : ∀ k, MemH (r + 1) ⇑(ccoord bM F k)) :
    (∀ k, MemH r ⇑(ccoord bM F' k)) ∧ ccoordSum r bM F' ≤ ccoordSum (r + 1) bM F := by
  have h : ∀ k : Σ _ : Fin 4, Fin 4, MemH r ⇑(ccoord bM F' k) ∧
      sn r ⇑(ccoord bM F' k) ≤ sn (r + 1) ⇑(ccoord bM F k) := by
    intro k
    rw [ccoord_bM, ccoord_bM]
    exact memH_of_isLineDeriv (isLineDeriv_cmp hd k.1 k.2) (memH_cmp hF k.1 k.2)
  exact ⟨fun k => (h k).1, sum_le_sum fun k _ => (h k).2⟩

/-- The coordinate size of a site-jet array splits over its three slots. -/
theorem coordSum_bJ_eq {N : ℕ} [NeZero N] (r : ℕ) (a b : Grid N → MetricRec)
    (c : Grid N → Fin 3 → MetricRec) :
    PeriodicGridSobolev.Moser.coordSum r bJ (fun x => ((a x, b x, c x) : JetSpace)) =
      PeriodicGridSobolev.Moser.coordSum r bM a + PeriodicGridSobolev.Moser.coordSum r bM b +
        ∑ i, PeriodicGridSobolev.Moser.coordSum r bM (fun x => c x i) := by
  unfold PeriodicGridSobolev.Moser.coordSum
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  have e1 : ∀ k, PeriodicGridSobolev.Moser.coordArr bJ (fun x => ((a x, b x, c x) : JetSpace))
      (Sum.inl k) = PeriodicGridSobolev.Moser.coordArr bM a k := by
    intro k; funext x
    simp [PeriodicGridSobolev.Moser.coordArr, bJ, Module.Basis.prod_repr_inl]
  have e2 : ∀ k, PeriodicGridSobolev.Moser.coordArr bJ (fun x => ((a x, b x, c x) : JetSpace))
      (Sum.inr (Sum.inl k)) = PeriodicGridSobolev.Moser.coordArr bM b k := by
    intro k; funext x
    simp [PeriodicGridSobolev.Moser.coordArr, bJ, Module.Basis.prod_repr_inr,
      Module.Basis.prod_repr_inl]
  have e3 : ∀ i k, PeriodicGridSobolev.Moser.coordArr bJ (fun x => ((a x, b x, c x) : JetSpace))
      (Sum.inr (Sum.inr ⟨i, k⟩)) = PeriodicGridSobolev.Moser.coordArr bM (fun x => c x i) k := by
    intro i k; funext x
    simp [PeriodicGridSobolev.Moser.coordArr, bJ, Module.Basis.prod_repr_inr, Pi.basis_repr]
  have e4 : ∀ g : Fin 3 → (Σ _ : Fin 4, Fin 4) → ℝ,
      ∑ x : (Σ _ : Fin 3, Σ _ : Fin 4, Fin 4), g x.1 x.2 = ∑ i, ∑ k, g i k :=
    fun g => Fintype.sum_sigma (fun x : (Σ _ : Fin 3, Σ _ : Fin 4, Fin 4) => g x.1 x.2)
  have e5 : ∑ x : (Σ _ : Fin 3, Σ _ : Fin 4, Fin 4), PeriodicGridSobolev.sobNorm r
      (PeriodicGridSobolev.Moser.coordArr bJ (fun x => ((a x, b x, c x) : JetSpace))
        (Sum.inr (Sum.inr x))) = ∑ i, ∑ k, PeriodicGridSobolev.sobNorm r
          (PeriodicGridSobolev.Moser.coordArr bM (fun x => c x i) k) := by
    rw [← e4 (fun i k => PeriodicGridSobolev.sobNorm r
      (PeriodicGridSobolev.Moser.coordArr bM (fun x => c x i) k))]
    exact sum_congr rfl fun x _ => by rw [← e3]
  rw [e5]
  simp only [e1, e2]
  ring

/-- **Continuum coefficient products** (uniform over a finite family of coefficients analytic at
Minkowski): on a small `H^s` ball of `Q`, `A_k(η + Q) G ∈ H^s` with
`‖A_k(η + Q) G‖_{H^s} ≤ K ‖G‖_{H^s}`. -/
theorem coef_mul_family (s : ℕ) (hs : 2 ≤ s) {ι : Type*} [Fintype ι] (A : ι → MetricRec → ℝ)
    (hA : ∀ k, AnalyticAt ℝ (A k) minkowski) :
    ∃ δ > 0, ∃ K ≥ 0, ∀ (k : ι) (Q : C(T3, MetricRec)), (∀ j, MemH s ⇑(ccoord bM Q j)) →
      ccoordSum s bM Q ≤ δ → ∀ G : CT, MemH s ⇑G →
      ∃ P : CT, (∀ y, P y = ((A k (minkowski + Q y) : ℝ) : ℂ) * G y) ∧ MemH s ⇑P ∧
        sn s ⇑P ≤ K * sn s ⇑G := by
  set P : ι → ℝ → ℝ → Prop := fun k δ K => ∀ (Q : C(T3, MetricRec)),
      (∀ j, MemH s ⇑(ccoord bM Q j)) → ccoordSum s bM Q ≤ δ → ∀ G : CT, MemH s ⇑G →
      ∃ P : CT, (∀ y, P y = ((A k (minkowski + Q y) : ℝ) : ℂ) * G y) ∧ MemH s ⇑P ∧
        sn s ⇑P ≤ K * sn s ⇑G with hPdef
  have hmono : ∀ k δ δ' K K', 0 < δ' → δ' ≤ δ → K ≤ K' → P k δ K → P k δ' K' := by
    intro k δ δ' K K' _ hδ' hK' hP Q hQ hQδ G hG
    obtain ⟨P, h1, h2, h3⟩ := hP Q hQ (hQδ.trans hδ') G hG
    exact ⟨P, h1, h2, h3.trans (mul_le_mul_of_nonneg_right hK' (sn_nonneg _ _))⟩
  have hex : ∀ k, ∃ δ > 0, ∃ K ≥ 0, P k δ K := by
    intro k
    obtain ⟨p, R, hp⟩ := hA k
    obtain ⟨δ, hδ, C, hC, hm⟩ := cont_moser s hs bM hp
    obtain ⟨Km, hKm, hmul⟩ := memH_mul s hs
    refine ⟨δ, hδ, ‖A k minkowski‖ + Km * (C * δ), by positivity, fun Q hQ hQδ G hG => ?_⟩
    obtain ⟨-, F, hF, hFm, hFs⟩ := hm Q hQ hQδ
    obtain ⟨hFG, hFGs⟩ := hmul F G hFm hG
    refine ⟨((A k minkowski : ℝ) : ℂ) • G + F * G, fun y => ?_, memH_add (memH_smul _ hG) hFG, ?_⟩
    · simp only [ContinuousMap.add_apply, ContinuousMap.smul_apply, ContinuousMap.mul_apply,
        hF y, smul_eq_mul]
      push_cast; ring
    · refine (sn_add_le' (memH_smul _ hG) hFG).trans ?_
      rw [sn_smul, Complex.norm_real]
      have hSn := sn_nonneg s ⇑G
      have h1 : sn s ⇑F ≤ C * δ :=
        hFs.trans (mul_le_mul_of_nonneg_left hQδ hC)
      have h2 : Km * sn s ⇑F * sn s ⇑G ≤ Km * (C * δ) * sn s ⇑G := by gcongr
      nlinarith
  obtain ⟨δ, hδ, K, hK, h⟩ := uniformize P hmono hex
  exact ⟨δ, hδ, K, hK, h⟩

/-- The open set of invertible records, on which the chart coefficients are analytic. -/
def detSet : Set MetricRec := {g | (Matrix.of g).det ≠ 0}

theorem isOpen_detSet : IsOpen detSet :=
  isOpen_ne_fun (Continuous.matrix_det (by fun_prop)) continuous_const

theorem analyticOnNhd_harmC (i j : Fin 3) : AnalyticOnNhd ℝ (harmC i j) detSet :=
  fun g hg => by unfold harmC; exact analyticAt_inv_entry g hg i.succ j.succ

theorem analyticOnNhd_harmB (i : Fin 3) : AnalyticOnNhd ℝ (harmB i) detSet :=
  fun g hg => by unfold harmB; exact (analyticAt_inv_entry g hg 0 i.succ).neg

/-- The continuum derivative of a coefficient product `A(η + Q) G`, as a continuous function. -/
theorem coef_product_lineDeriv {A : MetricRec → ℝ} (hA : AnalyticOnNhd ℝ A detSet) {i : Fin 3}
    {Q Qi : C(T3, MetricRec)} (hQ : IsLineDeriv i ⇑Q ⇑Qi) (hU : ∀ y, minkowski + Q y ∈ detSet)
    {G G' : T3 → ℝ} (hGc : Continuous G) (hG'c : Continuous G') (hG : IsLineDeriv i G G') :
    ∃ D : CT, (∀ y, D y = ((fderiv ℝ A (minkowski + Q y) (Qi y) * G y +
        A (minkowski + Q y) * G' y : ℝ) : ℂ)) ∧
      IsLineDeriv i (fun y => ((A (minkowski + Q y) * G y : ℝ) : ℂ)) ⇑D := by
  have hQc : Continuous fun y => minkowski + Q y := continuous_const.add Q.continuous
  obtain ⟨hc1, hc2⟩ := continuous_comp_analyticOnNhd hA hQc hU
  have hcont : Continuous fun y => ((fderiv ℝ A (minkowski + Q y) (Qi y) * G y +
      A (minkowski + Q y) * G' y : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (((hc2.clm_apply Qi.continuous).mul hGc).add (hc1.mul hG'c))
  refine ⟨⟨_, hcont⟩, fun y => rfl, ?_⟩
  have h1 : IsLineDeriv i (fun y => A (minkowski + Q y))
      (fun y => fderiv ℝ A (minkowski + Q y) (Qi y)) :=
    IsLineDeriv.comp (hQ.const_add minkowski) (fun y => (hA _ (hU y)).differentiableAt)
  exact (h1.mul hG).ofReal

/-! ### The sampled row identity -/

section Identity

variable {N : ℕ} [NeZero N]

local notation "Smp" => PeriodicGridSobolev.Sampling.sample N

/-- `c^{ij}(η + Q) ∂ⱼQ_{μν}` (complexified). -/
def pfF (Q : C(T3, MetricRec)) (Qd : Fin 3 → C(T3, MetricRec)) (i j : Fin 3) (μ ν : Fin 4) :
    T3 → ℂ := fun y => ((harmC i j (minkowski + Q y) * Qd j y μ ν : ℝ) : ℂ)

/-- Its derivative along `i` by the chain rule. -/
def pdF (Q : C(T3, MetricRec)) (Qd : Fin 3 → C(T3, MetricRec))
    (Qdd : Fin 3 → Fin 3 → C(T3, MetricRec)) (i j : Fin 3) (μ ν : Fin 4) : T3 → ℂ :=
  fun y => ((fderiv ℝ (harmC i j) (minkowski + Q y) (Qd i y) * Qd j y μ ν +
    harmC i j (minkowski + Q y) * Qdd i j y μ ν : ℝ) : ℂ)

/-- `bⁱ(η + Q) V_{μν}` (complexified). -/
def bfF (Q V : C(T3, MetricRec)) (i : Fin 3) (μ ν : Fin 4) : T3 → ℂ :=
  fun y => ((harmB i (minkowski + Q y) * V y μ ν : ℝ) : ℂ)

/-- Its derivative along `i` by the chain rule. -/
def bdF (Q V : C(T3, MetricRec)) (Qd Vd : Fin 3 → C(T3, MetricRec)) (i : Fin 3) (μ ν : Fin 4) :
    T3 → ℂ :=
  fun y => ((fderiv ℝ (harmB i) (minkowski + Q y) (Qd i y) * V y μ ν +
    harmB i (minkowski + Q y) * Vd i y μ ν : ℝ) : ℂ)

/-- The complexified `(μ, ν)` component of the continuum normal row. -/
def rowF (Q V W : C(T3, MetricRec)) (Qd Vd : Fin 3 → C(T3, MetricRec))
    (Qdd : Fin 3 → Fin 3 → C(T3, MetricRec)) (μ ν : Fin 4) : T3 → ℂ :=
  fun y => ((normalRow (Q y) (V y) (W y) (fun i => Qd i y) (fun i => Vd i y)
    (fun i j => Qdd i j y) μ ν : ℝ) : ℂ)

/-- **The sampled row identity.**  For the sampled record `q = 𝒮_h Q`, `v = 𝒮_h V`, `w = 𝒮_h W`,
the mass row of the open writer differs from the sampled continuum normal row by the flux,
transport and compensator consistency errors. -/
theorem sampled_row_identity (Q V W : C(T3, MetricRec)) (Qd Vd : Fin 3 → C(T3, MetricRec))
    (Qdd : Fin 3 → Fin 3 → C(T3, MetricRec)) (ha : ∀ x, aArr (sampleRec N ⇑Q) x ≠ 0)
    (μ ν : Fin 4) :
    cx (aArr (sampleRec N ⇑Q)) * cx (comp (sampleRec N ⇑W -
        harmonicWriterAcceleration (sampleRec N ⇑Q) (sampleRec N ⇑V)) μ ν) -
      Smp (rowF Q V W Qd Vd Qdd μ ν) =
    ∑ i, ∑ j, ((Smp (pdF Q Qd Qdd i j μ ν) - PeriodicGridSobolev.Dm i (Smp (pfF Q Qd i j μ ν))) +
        PeriodicGridSobolev.Dm i (cx (cArr (sampleRec N ⇑Q) i j) *
          (Smp ⇑(cmp (Qd j) μ ν) - PeriodicGridSobolev.Dp j (cx (comp (sampleRec N ⇑Q) μ ν))))) -
      ∑ i, cx (bArr (sampleRec N ⇑Q) i) * (Smp ⇑(cmp (Vd i) μ ν) -
        PeriodicGridSobolev.D0 i (cx (comp (sampleRec N ⇑V) μ ν))) -
      ∑ i, (Smp (bdF Q V Qd Vd i μ ν) - PeriodicGridSobolev.D0 i (Smp (bfF Q V i μ ν))) +
      (cx (fun x => compensatorMap (sampleRec N ⇑Q x, sampleRec N ⇑V x,
          fun i => Qd i (PeriodicGridSobolev.samplePt x)) μ ν) -
        cx (comp (Garr (sampleRec N ⇑Q) (sampleRec N ⇑V)) μ ν)) := by
  set q := sampleRec N ⇑Q
  set v := sampleRec N ⇑V
  have hrow := writer_row_cx q v μ ν ha
  have e1 : cx (comp (sampleRec N ⇑W - harmonicWriterAcceleration q v) μ ν) =
      cx (comp (sampleRec N ⇑W) μ ν) - cx (comp (harmonicWriterAcceleration q v) μ ν) := by
    funext x; simp [cx, comp]
  have hPf : ∀ i j, Smp (pfF Q Qd i j μ ν) = cx (cArr q i j) * Smp ⇑(cmp (Qd j) μ ν) := by
    intro i j; funext x
    simp [pfF, cx, cArr, PeriodicGridSobolev.Sampling.sample, q, sampleRec]
  have hBf : ∀ i, Smp (bfF Q V i μ ν) = cx (bArr q i) * cx (comp v μ ν) := by
    intro i; funext x
    simp [bfF, cx, bArr, PeriodicGridSobolev.Sampling.sample, q, v, sampleRec, comp]
  have hDm : ∀ i j, PeriodicGridSobolev.Dm i (cx (cArr q i j) *
      PeriodicGridSobolev.Dp j (cx (comp q μ ν))) =
      PeriodicGridSobolev.Dm i (Smp (pfF Q Qd i j μ ν)) -
        PeriodicGridSobolev.Dm i (cx (cArr q i j) *
          (Smp ⇑(cmp (Qd j) μ ν) - PeriodicGridSobolev.Dp j (cx (comp q μ ν)))) := by
    intro i j
    rw [hPf, ← map_sub]
    congr 1
    ring
  have hD0 : ∀ i, PeriodicGridSobolev.D0 i (cx (bArr q i) * cx (comp v μ ν)) =
      PeriodicGridSobolev.D0 i (Smp (bfF Q V i μ ν)) := by
    intro i; rw [hBf]
  have hcont : cx (aArr q) * cx (comp (sampleRec N ⇑W) μ ν) - Smp (rowF Q V W Qd Vd Qdd μ ν) =
      ∑ i, ∑ j, Smp (pdF Q Qd Qdd i j μ ν) - ∑ i, cx (bArr q i) * Smp ⇑(cmp (Vd i) μ ν) -
        ∑ i, Smp (bdF Q V Qd Vd i μ ν) +
        cx (fun x => compensatorMap (q x, v x, fun i => Qd i (PeriodicGridSobolev.samplePt x)) μ ν) := by
    funext x
    have h := normalRow_identity (Q (PeriodicGridSobolev.samplePt x))
      (V (PeriodicGridSobolev.samplePt x)) (W (PeriodicGridSobolev.samplePt x))
      (fun i => Qd i (PeriodicGridSobolev.samplePt x)) (fun i => Vd i (PeriodicGridSobolev.samplePt x))
      (fun i j => Qdd i j (PeriodicGridSobolev.samplePt x)) μ ν
    simp only [Pi.sub_apply, Pi.mul_apply, Pi.add_apply, Finset.sum_apply, cx, aArr, comp,
      PeriodicGridSobolev.Sampling.sample, rowF, pdF, bdF, cmp_apply, bArr, q, v, sampleRec]
    exact_mod_cast h
  rw [e1, mul_sub, hrow]
  simp only [hDm, hD0, sum_sub_distrib, sum_add_distrib, mul_sub]
  linear_combination hcont

end Identity

/-! ### Sampled consistency of the writer -/

theorem sobNorm_sub_comm {N : ℕ} [NeZero N] (r : ℕ) (u w : Grid N → ℂ) :
    PeriodicGridSobolev.sobNorm r (u - w) = PeriodicGridSobolev.sobNorm r (w - u) := by
  rw [← PeriodicGridSobolev.Moser.sobNorm_neg, neg_sub]

theorem isLineDeriv_comp_apply {i : Fin 3} {F F' : C(T3, MetricRec)} (h : IsLineDeriv i ⇑F ⇑F')
    (μ ν : Fin 4) : IsLineDeriv i (fun y => F y μ ν) (fun y => F' y μ ν) := by
  intro x
  exact hasDerivAt_pi.mp (hasDerivAt_pi.mp (h x) μ) ν

theorem continuous_comp_apply (F : C(T3, MetricRec)) (μ ν : Fin 4) :
    Continuous fun y => F y μ ν :=
  (continuous_apply ν).comp ((continuous_apply μ).comp F.continuous)

/-- The chart coefficient family `c^{ij}`, `bⁱ`. -/
def coefFam : (Fin 3 × Fin 3) ⊕ Fin 3 → MetricRec → ℝ
  | Sum.inl ij => harmC ij.1 ij.2
  | Sum.inr i => harmB i

theorem analyticAt_coefFam (k : (Fin 3 × Fin 3) ⊕ Fin 3) : AnalyticAt ℝ (coefFam k) minkowski := by
  rcases k with ij | i
  · exact analyticAt_harmC ij.1 ij.2
  · exact analyticAt_harmB i

/-- **Sampled consistency of the open writer** (the flux, transport and compensator estimates
behind `lem:supp-open-continuum-comparison` and `lem:supp-open-reduced-consistency`).  For
`s ≥ 4` there are `δ, C`, independent of the mesh `h = 1/N`, such that for every continuum jet
`(Q, V, W, ∂Q, ∂V, ∂²Q)` with `Q ∈ H^{s+1}`, `V ∈ H^s` componentwise and
`‖(Q, V)‖_top ≤ δ`, the sampled record `q = 𝒮_h Q`, `v = 𝒮_h V` with sampled acceleration
`𝒮_h W` satisfies `a(q) ≠ 0` and, componentwise,
`‖a(q)(𝒮_h W - V_{0,h}(q, v)) - 𝒮_h ρ‖_{s-2,h} ≤ C h ‖(Q, V)‖_top`,
where `ρ` is the continuum harmonic normal row of the jet. -/
theorem sampled_row_consistency (s : ℕ) (hs : 4 ≤ s) :
    ∃ δ > 0, ∃ C ≥ 0, ∀ (N : ℕ) [NeZero N] (Q V W : C(T3, MetricRec))
      (Qd Vd : Fin 3 → C(T3, MetricRec)) (Qdd : Fin 3 → Fin 3 → C(T3, MetricRec)),
      IsContJet Q V Qd Vd Qdd → (∀ k, MemH (s + 1) ⇑(ccoord bM Q k)) →
      (∀ k, MemH s ⇑(ccoord bM V k)) → contTop s Q V ≤ δ →
      (∀ x, aArr (sampleRec N ⇑Q) x ≠ 0) ∧ ∀ μ ν : Fin 4,
      PeriodicGridSobolev.sobNorm (s - 2) (cx (aArr (sampleRec N ⇑Q)) *
        cx (comp (sampleRec N ⇑W - harmonicWriterAcceleration (sampleRec N ⇑Q)
          (sampleRec N ⇑V)) μ ν) - PeriodicGridSobolev.Sampling.sample N (rowF Q V W Qd Vd Qdd μ ν))
        ≤ C * (N : ℝ)⁻¹ * contTop s Q V := by
  obtain ⟨r, rfl⟩ : ∃ r, s = r + 2 := ⟨s - 2, by omega⟩
  have hr : 2 ≤ r := by omega
  obtain ⟨Cp1, hCp1, hDp1⟩ := sample_Dp_sub_le (r + 1) (by omega)
  obtain ⟨Cp0, hCp0, hDp0⟩ := sample_Dp_sub_le r hr
  obtain ⟨Cm, hCm, hDm⟩ := sample_Dm_sub_le r hr
  obtain ⟨C0, hC0, hD0⟩ := sample_D0_sub_le r hr
  obtain ⟨Cs1, hCs1, hsamp1⟩ := coordSum_sample_le (E := MetricRec) (ι := Σ _ : Fin 4, Fin 4)
    (r + 1) (by omega)
  obtain ⟨Cs0, hCs0, hsamp0⟩ := coordSum_sample_le (E := MetricRec) (ι := Σ _ : Fin 4, Fin 4)
    r hr
  obtain ⟨δmc, hδmc, Cmc, hCmc, hmc⟩ := moser_coefficients (r + 1) (by omega)
  obtain ⟨δG, hδG, CG, hCG, hG⟩ := moser_lipschitz_compensator r hr
  obtain ⟨δL, hδL, KL, hKL, hL⟩ := coef_mul_family (r + 2) (by omega) coefFam analyticAt_coefFam
  obtain ⟨r₀, hr₀, hdet⟩ := exists_det_chart
  set B : ℝ := 1 + ∑ j, ‖bM j‖ with hBdef
  have hB : ∀ j, ‖bM j‖ ≤ B := fun j => by
    have := single_le_sum (f := fun j => ‖bM j‖) (fun _ _ => norm_nonneg _) (mem_univ j)
    linarith
  have hB0 : 0 ≤ B := by
    have : 0 ≤ ∑ j, ‖bM j‖ := sum_nonneg fun _ _ => norm_nonneg _
    linarith
  have he := cEmb_nonneg
  set A0 := PeriodicGridSobolev.Moser.algConst r
  set A1 := PeriodicGridSobolev.Moser.algConst (r + 1)
  have hA0 := PeriodicGridSobolev.Moser.algConst_pos r
  have hA1 := PeriodicGridSobolev.Moser.algConst_pos (r + 1)
  set δ : ℝ := min (min δL (r₀ / (2 * (B * Real.sqrt cEmb + 1))))
    (min (δmc / (Cs1 + 1)) (min (1 / ((Cmc + 1) * (Cs1 + 1))) (δG / (5 * (Cs0 + Cs1 + 1)))))
  have hδ : 0 < δ := by positivity
  set Ctot : ℝ := 9 * (Cm * KL + (A1 + 1) * Cp1) + 3 * ((A0 + 1) * C0) + 3 * (C0 * KL) +
    CG * (3 * Cp0)
  refine ⟨δ, hδ, Ctot, by positivity, fun N _ Q V W Qd Vd Qdd hJ hQ hV hX => ?_⟩
  set X := contTop (r + 2) Q V with hXdef
  set h : ℝ := (N : ℝ)⁻¹
  have hh : 0 ≤ h := by positivity
  have hX0 : 0 ≤ X := contTop_nonneg _ _ _
  set q := sampleRec N ⇑Q
  set v := sampleRec N ⇑V
  -- sizes of the continuum fields
  have hQX : ccoordSum (r + 3) bM Q ≤ X :=
    le_add_of_nonneg_right (ccoordSum_nonneg _ _ _)
  have hVX : ccoordSum (r + 2) bM V ≤ X :=
    le_add_of_nonneg_left (ccoordSum_nonneg _ _ _)
  have hQm2 : ∀ k, MemH (r + 2) ⇑(ccoord bM Q k) := fun k => memH_mono (by omega) (hQ k)
  have hQ2X : ccoordSum (r + 2) bM Q ≤ X := (ccoordSum_mono (by omega) hQ).trans hQX
  have hQ1X : ccoordSum (r + 1) bM Q ≤ X := (ccoordSum_mono (by omega) hQ).trans hQX
  have hQ0X : ccoordSum r bM Q ≤ X := (ccoordSum_mono (by omega) hQ).trans hQX
  have hV0X : ccoordSum r bM V ≤ X := (ccoordSum_mono (by omega) hV).trans hVX
  have hQd : ∀ i, (∀ k, MemH (r + 2) ⇑(ccoord bM (Qd i) k)) ∧
      ccoordSum (r + 2) bM (Qd i) ≤ ccoordSum (r + 3) bM Q := fun i =>
    ccoordSum_deriv_le (hJ.dQ i) hQ
  have hQd0X : ∀ i, ccoordSum r bM (Qd i) ≤ X := fun i =>
    ((ccoordSum_mono (by omega) (hQd i).1).trans (hQd i).2).trans hQX
  have hXδ1 : X ≤ δL := hX.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hXδ2 : X ≤ r₀ / (2 * (B * Real.sqrt cEmb + 1)) :=
    hX.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hXδ3 : X ≤ δmc / (Cs1 + 1) := hX.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hXδ4 : X ≤ 1 / ((Cmc + 1) * (Cs1 + 1)) :=
    hX.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hXδ5 : X ≤ δG / (5 * (Cs0 + Cs1 + 1)) :=
    hX.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  -- the pointwise chart
  have hsup : ∀ y, ‖Q y‖ < r₀ := by
    intro y
    have h1 := norm_le_ccoordSum (r + 3) (by omega) bM hB Q hQ y
    have h2 : B * (Real.sqrt cEmb * ccoordSum (r + 3) bM Q) ≤ B * (Real.sqrt cEmb * X) := by
      gcongr
    have hpos : 0 < 2 * (B * Real.sqrt cEmb + 1) := by positivity
    have h3 : X * (2 * (B * Real.sqrt cEmb + 1)) ≤ r₀ := by rwa [le_div_iff₀ hpos] at hXδ2
    nlinarith [Real.sqrt_nonneg cEmb]
  have hU : ∀ y, minkowski + Q y ∈ detSet := fun y =>
    (hdet _ (by rw [add_sub_cancel_left]; exact hsup y)).1
  have ha : ∀ x, aArr q x ≠ 0 := fun x =>
    (hdet _ (by rw [add_sub_cancel_left]; exact hsup _)).2
  refine ⟨ha, fun μ ν => ?_⟩
  rw [show r + 2 - 2 = r from rfl, sampled_row_identity Q V W Qd Vd Qdd ha μ ν]
  -- grid coefficient bounds
  have hq1 : PeriodicGridSobolev.Moser.coordSum (r + 1) bM q ≤ Cs1 * X :=
    (hsamp1 N bM Q (fun k => memH_mono (by omega) (hQ k))).trans
      (mul_le_mul_of_nonneg_left hQ1X hCs1)
  have hq1δ : PeriodicGridSobolev.Moser.coordSum (r + 1) bM q ≤ δmc := by
    refine hq1.trans ?_
    rw [le_div_iff₀ (by positivity)] at hXδ3
    nlinarith
  have hq1one : Cmc * PeriodicGridSobolev.Moser.coordSum (r + 1) bM q ≤ 1 := by
    have h1 : Cmc * PeriodicGridSobolev.Moser.coordSum (r + 1) bM q ≤ Cmc * (Cs1 * X) :=
      mul_le_mul_of_nonneg_left hq1 hCmc
    rw [le_div_iff₀ (by positivity)] at hXδ4
    nlinarith
  obtain ⟨-, -, hmcC, hmcB⟩ := hmc N q hq1δ
  have hcoefC : ∀ i j, PeriodicGridSobolev.sobNorm (r + 1)
      (cx (cArr q i j) - fun _ => ((if i = j then 1 else 0 : ℝ) : ℂ)) ≤ 1 :=
    fun i j => (hmcC i j).trans hq1one
  have hcoefB : ∀ i, PeriodicGridSobolev.sobNorm (r + 1)
      (cx (bArr q i) - fun _ => (0 : ℂ)) ≤ 1 := fun i => (hmcB i).trans hq1one
  have hdij : ∀ i j : Fin 3, ‖((if i = j then 1 else 0 : ℝ) : ℂ)‖ ≤ 1 := by
    intro i j; split_ifs <;> simp
  -- (T1a) the flux derivative
  have hT1a : ∀ i j, PeriodicGridSobolev.sobNorm r
      (PeriodicGridSobolev.Sampling.sample N (pdF Q Qd Qdd i j μ ν) -
        PeriodicGridSobolev.Dm i (PeriodicGridSobolev.Sampling.sample N (pfF Q Qd i j μ ν))) ≤
      Cm * KL * h * X := by
    intro i j
    have hG := memH_cmp (hQd j).1 μ ν
    obtain ⟨P, hP, hPm, hPs⟩ := hL (Sum.inl (i, j)) Q hQm2 (hQ2X.trans hXδ1) (cmp (Qd j) μ ν) hG
    obtain ⟨D, hD, hDd⟩ := coef_product_lineDeriv (analyticOnNhd_harmC i j) (hJ.dQ i) hU
      (continuous_comp_apply (Qd j) μ ν) (continuous_comp_apply (Qdd i j) μ ν)
      (isLineDeriv_comp_apply (hJ.dQd i j) μ ν)
    have ePf : ⇑P = pfF Q Qd i j μ ν := by
      funext y; rw [hP y]; simp [pfF, coefFam]
    have ePd : ⇑D = pdF Q Qd Qdd i j μ ν := by
      funext y; rw [hD y]; rfl
    have hdd : IsLineDeriv i ⇑P ⇑D := by
      rw [ePf]
      convert hDd using 1
      funext y; simp [pfF]
    have h1 := hDm N i P D hdd hPm
    rw [ePf, ePd] at h1
    rw [sobNorm_sub_comm]
    refine h1.trans ?_
    have h2 : sn (r + 2) (pfF Q Qd i j μ ν) ≤ KL * X := by
      rw [← ePf]
      exact hPs.trans (mul_le_mul_of_nonneg_left ((sn_cmp_le_ccoordSum _ _ _ _).trans
        ((hQd j).2.trans hQX)) hKL)
    calc Cm * (N : ℝ)⁻¹ * sn (r + 2) (pfF Q Qd i j μ ν) ≤ Cm * (N : ℝ)⁻¹ * (KL * X) := by
          gcongr
      _ = Cm * KL * h * X := by ring
  -- (T1b) the flux interpolation error
  have hT1b : ∀ i j, PeriodicGridSobolev.sobNorm r (PeriodicGridSobolev.Dm i
      (cx (cArr q i j) * (PeriodicGridSobolev.Sampling.sample N ⇑(cmp (Qd j) μ ν) -
        PeriodicGridSobolev.Dp j (cx (comp q μ ν))))) ≤ (A1 + 1) * Cp1 * h * X := by
    intro i j
    refine (PeriodicGridSobolev.CommutedRow.sobNorm_Dm_le r i _).trans ?_
    refine (sobNorm_coef_mul_le (r + 1) (by omega) _ _ _ (hdij i j) (hcoefC i j)).trans ?_
    have h1 := hDp1 N j (cmp Q μ ν) (cmp (Qd j) μ ν) (isLineDeriv_cmp (hJ.dQ j) μ ν)
      (memH_cmp hQ μ ν)
    rw [← cx_comp_sampleRec] at h1
    rw [sobNorm_sub_comm]
    have h2 : sn (r + 1 + 2) ⇑(cmp Q μ ν) ≤ X := (sn_cmp_le_ccoordSum _ _ _ _).trans hQX
    calc (A1 + 1) * PeriodicGridSobolev.sobNorm (r + 1)
          (PeriodicGridSobolev.Dp j (cx (comp q μ ν)) -
            PeriodicGridSobolev.Sampling.sample N ⇑(cmp (Qd j) μ ν))
        ≤ (A1 + 1) * (Cp1 * (N : ℝ)⁻¹ * sn (r + 1 + 2) ⇑(cmp Q μ ν)) := by gcongr
      _ ≤ (A1 + 1) * (Cp1 * (N : ℝ)⁻¹ * X) := by gcongr
      _ = (A1 + 1) * Cp1 * h * X := by ring
  -- (T2) the transport interpolation error
  have hT2 : ∀ i, PeriodicGridSobolev.sobNorm r (cx (bArr q i) *
      (PeriodicGridSobolev.Sampling.sample N ⇑(cmp (Vd i) μ ν) -
        PeriodicGridSobolev.D0 i (cx (comp v μ ν)))) ≤ (A0 + 1) * C0 * h * X := by
    intro i
    have hb : PeriodicGridSobolev.sobNorm r (cx (bArr q i) - fun _ => (0 : ℂ)) ≤ 1 :=
      (PeriodicGridSobolev.Moser.sobNorm_mono (by omega) _).trans (hcoefB i)
    refine (sobNorm_coef_mul_le r hr _ _ 0 (by simp) hb).trans ?_
    have h1 := hD0 N i (cmp V μ ν) (cmp (Vd i) μ ν) (isLineDeriv_cmp (hJ.dV i) μ ν)
      (memH_cmp hV μ ν)
    rw [← cx_comp_sampleRec] at h1
    rw [sobNorm_sub_comm]
    have h2 : sn (r + 2) ⇑(cmp V μ ν) ≤ X := (sn_cmp_le_ccoordSum _ _ _ _).trans hVX
    calc (A0 + 1) * PeriodicGridSobolev.sobNorm r
          (PeriodicGridSobolev.D0 i (cx (comp v μ ν)) -
            PeriodicGridSobolev.Sampling.sample N ⇑(cmp (Vd i) μ ν))
        ≤ (A0 + 1) * (C0 * (N : ℝ)⁻¹ * sn (r + 2) ⇑(cmp V μ ν)) := by gcongr
      _ ≤ (A0 + 1) * (C0 * (N : ℝ)⁻¹ * X) := by gcongr
      _ = (A0 + 1) * C0 * h * X := by ring
  -- (T3) the transport derivative
  have hT3 : ∀ i, PeriodicGridSobolev.sobNorm r
      (PeriodicGridSobolev.Sampling.sample N (bdF Q V Qd Vd i μ ν) -
        PeriodicGridSobolev.D0 i (PeriodicGridSobolev.Sampling.sample N (bfF Q V i μ ν))) ≤
      C0 * KL * h * X := by
    intro i
    have hG := memH_cmp hV μ ν
    obtain ⟨P, hP, hPm, hPs⟩ := hL (Sum.inr i) Q hQm2 (hQ2X.trans hXδ1) (cmp V μ ν) hG
    obtain ⟨D, hD, hDd⟩ := coef_product_lineDeriv (analyticOnNhd_harmB i) (hJ.dQ i) hU
      (continuous_comp_apply V μ ν) (continuous_comp_apply (Vd i) μ ν)
      (isLineDeriv_comp_apply (hJ.dV i) μ ν)
    have ePf : ⇑P = bfF Q V i μ ν := by
      funext y; rw [hP y]; simp [bfF, coefFam]
    have ePd : ⇑D = bdF Q V Qd Vd i μ ν := by
      funext y; rw [hD y]; rfl
    have hdd : IsLineDeriv i ⇑P ⇑D := by
      rw [ePf]
      convert hDd using 1
      funext y; simp [bfF]
    have h1 := hD0 N i P D hdd hPm
    rw [ePf, ePd] at h1
    rw [sobNorm_sub_comm]
    refine h1.trans ?_
    have h2 : sn (r + 2) (bfF Q V i μ ν) ≤ KL * X := by
      rw [← ePf]
      exact hPs.trans (mul_le_mul_of_nonneg_left ((sn_cmp_le_ccoordSum _ _ _ _).trans hVX) hKL)
    calc C0 * (N : ℝ)⁻¹ * sn (r + 2) (bfF Q V i μ ν) ≤ C0 * (N : ℝ)⁻¹ * (KL * X) := by
          gcongr
      _ = C0 * KL * h * X := by ring
  -- (T4) the compensator
  have hT4 : PeriodicGridSobolev.sobNorm r
      (cx (fun x => compensatorMap (q x, v x, fun i => Qd i (PeriodicGridSobolev.samplePt x)) μ ν) -
        cx (comp (Garr q v) μ ν)) ≤ CG * (3 * Cp0) * h * X := by
    have hcomp : ∀ i (k : Σ _ : Fin 4, Fin 4), PeriodicGridSobolev.Moser.coordArr bM
        (fun x => fwd (N : ℝ)⁻¹ (e N) i q x) k =
        PeriodicGridSobolev.Dp i (cx (comp q k.1 k.2)) := by
      intro i k
      rw [coordArr_bM, comp_fwd, cx_Dp]
    have hfwd : ∀ i, PeriodicGridSobolev.Moser.coordSum r bM (fun x => fwd (N : ℝ)⁻¹ (e N) i q x)
        ≤ Cs1 * X := by
      intro i
      refine le_trans ?_ hq1
      unfold PeriodicGridSobolev.Moser.coordSum
      refine sum_le_sum fun k _ => ?_
      rw [hcomp, coordArr_bM]
      exact PeriodicGridSobolev.CommutedRow.sobNorm_Dp_le r i _
    have hjc : PeriodicGridSobolev.Moser.coordSum r bJ
        (fun x => ((q x, v x, fun i => Qd i (PeriodicGridSobolev.samplePt x)) : JetSpace)) ≤ δG := by
      rw [coordSum_bJ_eq]
      have h1 : PeriodicGridSobolev.Moser.coordSum r bM q ≤ Cs0 * ccoordSum r bM Q :=
        hsamp0 N bM Q (fun k => memH_mono (by omega) (hQ k))
      have h2 : PeriodicGridSobolev.Moser.coordSum r bM v ≤ Cs0 * ccoordSum r bM V :=
        hsamp0 N bM V (fun k => memH_mono (by omega) (hV k))
      have h3 : ∀ i, PeriodicGridSobolev.Moser.coordSum r bM
          (fun x : Grid N => Qd i (PeriodicGridSobolev.samplePt x)) ≤ Cs0 * X := fun i =>
        (hsamp0 N bM (Qd i) (fun k => memH_mono (by omega) ((hQd i).1 k))).trans
          (mul_le_mul_of_nonneg_left (hQd0X i) hCs0)
      have h4 : ∑ i, PeriodicGridSobolev.Moser.coordSum r bM
          (fun x : Grid N => Qd i (PeriodicGridSobolev.samplePt x)) ≤ 3 * (Cs0 * X) := by
        calc _ ≤ ∑ _i : Fin 3, Cs0 * X := sum_le_sum fun i _ => h3 i
          _ = 3 * (Cs0 * X) := by simp
      have h5 : Cs0 * ccoordSum r bM Q ≤ Cs0 * X := mul_le_mul_of_nonneg_left hQ0X hCs0
      have h6 : Cs0 * ccoordSum r bM V ≤ Cs0 * X := mul_le_mul_of_nonneg_left hV0X hCs0
      rw [le_div_iff₀ (by positivity)] at hXδ5
      have : PeriodicGridSobolev.Moser.coordSum r bM q +
          PeriodicGridSobolev.Moser.coordSum r bM v ≤ 2 * (Cs0 * X) := by
        have := h1.trans h5; have := h2.trans h6; linarith
      have hpos := mul_nonneg (by positivity : (0 : ℝ) ≤ 5 * Cs1 + 5) hX0
      have e5 : X * (5 * (Cs0 + Cs1 + 1)) = 2 * (Cs0 * X) + 3 * (Cs0 * X) + (5 * Cs1 + 5) * X := by
        ring
      linarith
    have hjg : PeriodicGridSobolev.Moser.coordSum r bJ (jetArr q v) ≤ δG := by
      have ej : jetArr q v = fun x => ((q x, v x, fun i => fwd (N : ℝ)⁻¹ (e N) i q x) : JetSpace) :=
        rfl
      rw [ej, coordSum_bJ_eq]
      have h1 : PeriodicGridSobolev.Moser.coordSum r bM q ≤ Cs0 * ccoordSum r bM Q :=
        hsamp0 N bM Q (fun k => memH_mono (by omega) (hQ k))
      have h2 : PeriodicGridSobolev.Moser.coordSum r bM v ≤ Cs0 * ccoordSum r bM V :=
        hsamp0 N bM V (fun k => memH_mono (by omega) (hV k))
      have h4 : ∑ i, PeriodicGridSobolev.Moser.coordSum r bM
          (fun x => fwd (N : ℝ)⁻¹ (e N) i q x) ≤ 3 * (Cs1 * X) := by
        calc _ ≤ ∑ _i : Fin 3, Cs1 * X := sum_le_sum fun i _ => hfwd i
          _ = 3 * (Cs1 * X) := by simp
      have h5 : Cs0 * ccoordSum r bM Q ≤ Cs0 * X := mul_le_mul_of_nonneg_left hQ0X hCs0
      have h6 : Cs0 * ccoordSum r bM V ≤ Cs0 * X := mul_le_mul_of_nonneg_left hV0X hCs0
      rw [le_div_iff₀ (by positivity)] at hXδ5
      have : PeriodicGridSobolev.Moser.coordSum r bM q +
          PeriodicGridSobolev.Moser.coordSum r bM v ≤ 2 * (Cs0 * X) := by
        have := h1.trans h5; have := h2.trans h6; linarith
      have hpos := mul_nonneg (by positivity : (0 : ℝ) ≤ 3 * Cs0 + 2 * Cs1 + 5) hX0
      have e5 : X * (5 * (Cs0 + Cs1 + 1)) = 2 * (Cs0 * X) + 3 * (Cs1 * X) +
          (3 * Cs0 + 2 * Cs1 + 5) * X := by ring
      linarith
    have hG' := hG N
      (fun x => ((q x, v x, fun i => Qd i (PeriodicGridSobolev.samplePt x)) : JetSpace))
      (jetArr q v) hjc hjg μ ν
    have eG : cx (comp (Garr q v) μ ν) = cx (fun x => compensatorMap (jetArr q v x) μ ν) := rfl
    rw [eG]
    refine hG'.trans ?_
    have ediff : (fun x => ((q x, v x, fun i => Qd i (PeriodicGridSobolev.samplePt x)) : JetSpace))
        - jetArr q v = fun x => (((0 : MetricRec), (0 : MetricRec),
          fun i => Qd i (PeriodicGridSobolev.samplePt x) - fwd (N : ℝ)⁻¹ (e N) i q x) : JetSpace) := by
      funext x
      simp only [jetArr, Pi.sub_apply, Prod.mk_sub_mk, sub_self]
      rfl
    rw [ediff, coordSum_bJ_eq]
    have hz : PeriodicGridSobolev.Moser.coordSum r bM (fun _ : Grid N => (0 : MetricRec)) = 0 := by
      unfold PeriodicGridSobolev.Moser.coordSum
      refine sum_eq_zero fun k _ => ?_
      have : PeriodicGridSobolev.Moser.coordArr bM (fun _ : Grid N => (0 : MetricRec)) k = 0 := by
        funext x; simp [PeriodicGridSobolev.Moser.coordArr]
      rw [this, PeriodicGridSobolev.Moser.sobNorm_zero]
    rw [hz]
    have hterm : ∀ i, PeriodicGridSobolev.Moser.coordSum r bM
        (fun x => Qd i (PeriodicGridSobolev.samplePt x) - fwd (N : ℝ)⁻¹ (e N) i q x) ≤
        Cp0 * h * X := by
      intro i
      unfold PeriodicGridSobolev.Moser.coordSum
      have hk : ∀ k : Σ _ : Fin 4, Fin 4, PeriodicGridSobolev.sobNorm r
          (PeriodicGridSobolev.Moser.coordArr bM
            (fun x => Qd i (PeriodicGridSobolev.samplePt x) - fwd (N : ℝ)⁻¹ (e N) i q x) k) ≤
          Cp0 * h * sn (r + 2) ⇑(cmp Q k.1 k.2) := by
        intro k
        have e1 : PeriodicGridSobolev.Moser.coordArr bM
            (fun x => Qd i (PeriodicGridSobolev.samplePt x) - fwd (N : ℝ)⁻¹ (e N) i q x) k =
            PeriodicGridSobolev.Sampling.sample N ⇑(cmp (Qd i) k.1 k.2) -
              PeriodicGridSobolev.Dp i (PeriodicGridSobolev.Sampling.sample N ⇑(cmp Q k.1 k.2)) := by
          have := PeriodicGridSobolev.Moser.coordArr_sub bM
            (fun x : Grid N => Qd i (PeriodicGridSobolev.samplePt x))
            (fun x => fwd (N : ℝ)⁻¹ (e N) i q x) k
          rw [show (fun x => Qd i (PeriodicGridSobolev.samplePt x) - fwd (N : ℝ)⁻¹ (e N) i q x) =
            (fun x : Grid N => Qd i (PeriodicGridSobolev.samplePt x)) -
              (fun x => fwd (N : ℝ)⁻¹ (e N) i q x) from rfl, this, hcomp, coordArr_bM,
            ← cx_comp_sampleRec]
          rfl
        rw [e1, sobNorm_sub_comm]
        exact hDp0 N i (cmp Q k.1 k.2) (cmp (Qd i) k.1 k.2) (isLineDeriv_cmp (hJ.dQ i) k.1 k.2)
          (memH_cmp hQm2 k.1 k.2)
      calc ∑ k, PeriodicGridSobolev.sobNorm r (PeriodicGridSobolev.Moser.coordArr bM
            (fun x => Qd i (PeriodicGridSobolev.samplePt x) - fwd (N : ℝ)⁻¹ (e N) i q x) k)
          ≤ ∑ k : Σ _ : Fin 4, Fin 4, Cp0 * h * sn (r + 2) ⇑(cmp Q k.1 k.2) :=
            sum_le_sum fun k _ => hk k
        _ = Cp0 * h * ccoordSum (r + 2) bM Q := by
            rw [← mul_sum]; unfold ccoordSum; simp [ccoord_bM]
        _ ≤ Cp0 * h * X := by gcongr
    have hsum3 : ∑ i, PeriodicGridSobolev.Moser.coordSum r bM
        (fun x => Qd i (PeriodicGridSobolev.samplePt x) - fwd (N : ℝ)⁻¹ (e N) i q x) ≤
        3 * (Cp0 * h * X) := by
      calc _ ≤ ∑ _i : Fin 3, Cp0 * h * X := sum_le_sum fun i _ => hterm i
        _ = 3 * (Cp0 * h * X) := by simp
    calc CG * (0 + 0 + ∑ i, PeriodicGridSobolev.Moser.coordSum r bM
          (fun x => Qd i (PeriodicGridSobolev.samplePt x) - fwd (N : ℝ)⁻¹ (e N) i q x))
        ≤ CG * (3 * (Cp0 * h * X)) := by rw [zero_add, zero_add]; gcongr
      _ = CG * (3 * Cp0) * h * X := by ring
  -- assembly
  have hS1 : PeriodicGridSobolev.sobNorm r (∑ i, ∑ j,
      ((PeriodicGridSobolev.Sampling.sample N (pdF Q Qd Qdd i j μ ν) -
        PeriodicGridSobolev.Dm i (PeriodicGridSobolev.Sampling.sample N (pfF Q Qd i j μ ν))) +
      PeriodicGridSobolev.Dm i (cx (cArr q i j) *
        (PeriodicGridSobolev.Sampling.sample N ⇑(cmp (Qd j) μ ν) -
          PeriodicGridSobolev.Dp j (cx (comp q μ ν)))))) ≤
      9 * ((Cm * KL + (A1 + 1) * Cp1) * h * X) := by
    refine (PeriodicGridSobolev.Moser.sobNorm_sum_le r _ _).trans ?_
    calc _ ≤ ∑ _i : Fin 3, ∑ _j : Fin 3, (Cm * KL + (A1 + 1) * Cp1) * h * X := by
          refine sum_le_sum fun i _ => (PeriodicGridSobolev.Moser.sobNorm_sum_le r _ _).trans ?_
          refine sum_le_sum fun j _ => (PeriodicGridSobolev.Moser.sobNorm_add_le r _ _).trans ?_
          have h1 := hT1a i j
          have h2 := hT1b i j
          have e : (Cm * KL + (A1 + 1) * Cp1) * h * X = Cm * KL * h * X + (A1 + 1) * Cp1 * h * X := by
            ring
          rw [e]
          exact add_le_add h1 h2
      _ = 9 * ((Cm * KL + (A1 + 1) * Cp1) * h * X) := by simp; ring
  have hS2 : PeriodicGridSobolev.sobNorm r (∑ i, cx (bArr q i) *
      (PeriodicGridSobolev.Sampling.sample N ⇑(cmp (Vd i) μ ν) -
        PeriodicGridSobolev.D0 i (cx (comp v μ ν)))) ≤ 3 * ((A0 + 1) * C0 * h * X) := by
    refine (PeriodicGridSobolev.Moser.sobNorm_sum_le r _ _).trans ?_
    calc _ ≤ ∑ _i : Fin 3, (A0 + 1) * C0 * h * X := sum_le_sum fun i _ => hT2 i
      _ = 3 * ((A0 + 1) * C0 * h * X) := by simp
  have hS3 : PeriodicGridSobolev.sobNorm r (∑ i,
      (PeriodicGridSobolev.Sampling.sample N (bdF Q V Qd Vd i μ ν) -
        PeriodicGridSobolev.D0 i (PeriodicGridSobolev.Sampling.sample N (bfF Q V i μ ν)))) ≤
      3 * (C0 * KL * h * X) := by
    refine (PeriodicGridSobolev.Moser.sobNorm_sum_le r _ _).trans ?_
    calc _ ≤ ∑ _i : Fin 3, C0 * KL * h * X := sum_le_sum fun i _ => hT3 i
      _ = 3 * (C0 * KL * h * X) := by simp
  refine ((PeriodicGridSobolev.Moser.sobNorm_add_le r _ _).trans (add_le_add
    ((PeriodicGridSobolev.Moser.sobNorm_sub_le r _ _).trans (add_le_add
      ((PeriodicGridSobolev.Moser.sobNorm_sub_le r _ _).trans (add_le_add hS1 hS2)) hS3)) hT4)).trans
    (le_of_eq ?_)
  simp only [Ctot, h]
  ring

/-! ### Continuum solutions and the sampled force -/

/-- **A continuum solution of the harmonic normal row on `[0, T]`** with spatial regularity
`Q ∈ H^{s+1}`, `V = ∂ₜQ ∈ H^s` (componentwise, every time): at every `t ∈ [0, T]`
`Q_t = V`, `V_t = W` pointwise (two-sided time derivatives), `W` is continuous in time, the
spatial derivative fields are the classical coordinate derivatives (`IsContJet`), the records are
symmetric, and the normal row `eq:main-harmonic-normal-row` vanishes at every point. -/
structure IsContSolution (s : ℕ) (T : ℝ) (Q V W : ℝ → C(T3, MetricRec))
    (Qd Vd : ℝ → Fin 3 → C(T3, MetricRec)) (Qdd : ℝ → Fin 3 → Fin 3 → C(T3, MetricRec)) :
    Prop where
  jet : ∀ t ∈ Set.Icc 0 T, IsContJet (Q t) (V t) (Qd t) (Vd t) (Qdd t)
  dQ : ∀ t ∈ Set.Icc 0 T, ∀ y, HasDerivAt (fun τ => Q τ y) (V t y) t
  dV : ∀ t ∈ Set.Icc 0 T, ∀ y, HasDerivAt (fun τ => V τ y) (W t y) t
  contW : ∀ y, ContinuousOn (fun τ => W τ y) (Set.Icc 0 T)
  row : ∀ t ∈ Set.Icc 0 T, ∀ y, normalRow (Q t y) (V t y) (W t y) (fun i => Qd t i y)
    (fun i => Vd t i y) (fun i j => Qdd t i j y) = 0
  symQ : ∀ t ∈ Set.Icc 0 T, ∀ y μ ν, Q t y μ ν = Q t y ν μ
  symV : ∀ t ∈ Set.Icc 0 T, ∀ y μ ν, V t y μ ν = V t y ν μ
  regQ : ∀ t ∈ Set.Icc 0 T, ∀ k, MemH (s + 1) ⇑(ccoord bM (Q t) k)
  regV : ∀ t ∈ Set.Icc 0 T, ∀ k, MemH s ⇑(ccoord bM (V t) k)

theorem isSymRec_sampleRec {N : ℕ} [NeZero N] {F : T3 → MetricRec}
    (h : ∀ y μ ν, F y μ ν = F y ν μ) : IsSymRec (sampleRec N F) := fun x μ ν => h _ μ ν

theorem card_upper_le : (Fintype.card Upper : ℝ) ≤ 16 := by
  have h1 : Fintype.card Upper ≤ Fintype.card (Fin 4 × Fin 4) := Fintype.card_subtype_le _
  have h2 : Fintype.card (Fin 4 × Fin 4) = 16 := by simp
  exact_mod_cast h1.trans h2.le

/-- The sampled continuum record is in the grid top ball:
`‖𝒮_h(Q, V)‖_{X^s_h} ≤ C ‖(Q, V)‖_top`. -/
theorem Xnorm_sample_le (s : ℕ) (hs : 2 ≤ s) :
    ∃ C ≥ 0, ∀ (N : ℕ) [NeZero N] (Q V : C(T3, MetricRec)), (∀ k, MemH (s + 1) ⇑(ccoord bM Q k)) →
      (∀ k, MemH s ⇑(ccoord bM V k)) →
      Xnorm s (sampleRec N ⇑Q) (sampleRec N ⇑V) ≤ C * contTop s Q V := by
  obtain ⟨C1, hC1, h1⟩ := sobNorm_sample_le (s + 1) (by omega)
  obtain ⟨C2, hC2, h2⟩ := sobNorm_sample_le s hs
  refine ⟨16 * (C1 + C2), by positivity, fun N _ Q V hQ hV => ?_⟩
  refine (Xnorm_le_sum s _ _).trans ?_
  have hX0 := contTop_nonneg s Q V
  have hterm : ∀ κ : Upper, PeriodicGridSobolev.sobNorm (s + 1)
      (cx (comp (sampleRec N ⇑Q) κ.1.1 κ.1.2)) +
      PeriodicGridSobolev.sobNorm s (cx (comp (sampleRec N ⇑V) κ.1.1 κ.1.2)) ≤
      (C1 + C2) * contTop s Q V := by
    intro κ
    rw [cx_comp_sampleRec, cx_comp_sampleRec]
    have a1 := h1 N _ (memH_cmp hQ κ.1.1 κ.1.2)
    have a2 := h2 N _ (memH_cmp hV κ.1.1 κ.1.2)
    have b1 : sn (s + 1) ⇑(cmp Q κ.1.1 κ.1.2) ≤ contTop s Q V :=
      (sn_cmp_le_ccoordSum _ _ _ _).trans (le_add_of_nonneg_right (ccoordSum_nonneg _ _ _))
    have b2 : sn s ⇑(cmp V κ.1.1 κ.1.2) ≤ contTop s Q V :=
      (sn_cmp_le_ccoordSum _ _ _ _).trans (le_add_of_nonneg_left (ccoordSum_nonneg _ _ _))
    have c1 : C1 * sn (s + 1) ⇑(cmp Q κ.1.1 κ.1.2) ≤ C1 * contTop s Q V :=
      mul_le_mul_of_nonneg_left b1 hC1
    have c2 : C2 * sn s ⇑(cmp V κ.1.1 κ.1.2) ≤ C2 * contTop s Q V :=
      mul_le_mul_of_nonneg_left b2 hC2
    nlinarith
  calc ∑ κ : Upper, (PeriodicGridSobolev.sobNorm (s + 1)
        (cx (comp (sampleRec N ⇑Q) κ.1.1 κ.1.2)) +
        PeriodicGridSobolev.sobNorm s (cx (comp (sampleRec N ⇑V) κ.1.1 κ.1.2)))
      ≤ ∑ _κ : Upper, (C1 + C2) * contTop s Q V := sum_le_sum fun κ _ => hterm κ
    _ = (Fintype.card Upper : ℝ) * ((C1 + C2) * contTop s Q V) := by simp
    _ ≤ 16 * ((C1 + C2) * contTop s Q V) :=
        mul_le_mul_of_nonneg_right card_upper_le (by positivity)
    _ = 16 * (C1 + C2) * contTop s Q V := by ring

/-- **The sampled force of a continuum solution**: for `s ≥ 4` there are `δ, C`, independent of
the mesh, such that if `(Q, V, W, ...)` is a continuum jet whose normal row vanishes, then the
sampled record `𝒮_h(Q, V)` solves the open writer with the acceleration force
`f = 𝒮_h W - V_{0,h}(𝒮_h Q, 𝒮_h V)`, and `‖f‖_{s-2,h} ≤ C h ‖(Q, V)‖_top`. -/
theorem sampled_force_bound (s : ℕ) (hs : 4 ≤ s) :
    ∃ δ > 0, ∃ C ≥ 0, ∀ (N : ℕ) [NeZero N] (Q V W : C(T3, MetricRec))
      (Qd Vd : Fin 3 → C(T3, MetricRec)) (Qdd : Fin 3 → Fin 3 → C(T3, MetricRec)),
      IsContJet Q V Qd Vd Qdd → (∀ k, MemH (s + 1) ⇑(ccoord bM Q k)) →
      (∀ k, MemH s ⇑(ccoord bM V k)) → contTop s Q V ≤ δ →
      (∀ y, normalRow (Q y) (V y) (W y) (fun i => Qd i y) (fun i => Vd i y)
        (fun i j => Qdd i j y) = 0) →
      Fnorm (s - 2) (sampleRec N ⇑W - harmonicWriterAcceleration (sampleRec N ⇑Q)
        (sampleRec N ⇑V)) ≤ C * (N : ℝ)⁻¹ * contTop s Q V := by
  obtain ⟨δc, hδc, Cc, hCc, hcons⟩ := sampled_row_consistency s hs
  obtain ⟨δmc, hδmc, Cmc, hCmc, hmc⟩ := moser_coefficients (s - 2) (by omega)
  obtain ⟨Cs, hCs, hsamp⟩ := coordSum_sample_le (E := MetricRec) (ι := Σ _ : Fin 4, Fin 4)
    (s - 2) (by omega)
  set A := PeriodicGridSobolev.Moser.algConst (s - 2)
  have hA := PeriodicGridSobolev.Moser.algConst_pos (s - 2)
  set δ : ℝ := min δc (min (δmc / (Cs + 1)) (1 / ((Cmc + 1) * (Cs + 1))))
  have hδ : 0 < δ := by positivity
  refine ⟨δ, hδ, 16 * ((A + 1) * Cc), by positivity,
    fun N _ Q V W Qd Vd Qdd hJ hQ hV hX hrow => ?_⟩
  set X := contTop s Q V
  have hX0 : 0 ≤ X := contTop_nonneg _ _ _
  obtain ⟨ha, hc⟩ := hcons N Q V W Qd Vd Qdd hJ hQ hV (hX.trans (min_le_left _ _))
  set q := sampleRec N ⇑Q
  have hcQ : ccoordSum (s - 2) bM Q ≤ X :=
    (ccoordSum_mono (by omega) hQ).trans (le_add_of_nonneg_right (ccoordSum_nonneg _ _ _))
  have hq : PeriodicGridSobolev.Moser.coordSum (s - 2) bM q ≤ Cs * X :=
    (hsamp N bM Q (fun k => memH_mono (by omega) (hQ k))).trans
      (mul_le_mul_of_nonneg_left hcQ hCs)
  have hXδ2 : X ≤ δmc / (Cs + 1) := hX.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hXδ3 : X ≤ 1 / ((Cmc + 1) * (Cs + 1)) :=
    hX.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hqδ : PeriodicGridSobolev.Moser.coordSum (s - 2) bM q ≤ δmc := by
    refine hq.trans ?_
    rw [le_div_iff₀ (by positivity)] at hXδ2
    nlinarith
  have hqone : Cmc * PeriodicGridSobolev.Moser.coordSum (s - 2) bM q ≤ 1 := by
    have h1 := mul_le_mul_of_nonneg_left hq hCmc
    rw [le_div_iff₀ (by positivity)] at hXδ3
    nlinarith
  obtain ⟨-, hinv, -, -⟩ := hmc N q hqδ
  have hinv1 : PeriodicGridSobolev.sobNorm (s - 2)
      (cx (fun x => (harmA (minkowski + q x))⁻¹) - fun _ => (1 : ℂ)) ≤ 1 := hinv.trans hqone
  refine (lawDiff_Fnorm_le_of_comp_le (s - 2) _ (M := (A + 1) * Cc * (N : ℝ)⁻¹ * X)
    (by positivity) fun κ => ?_).trans (le_of_eq (by ring))
  have e : cx (comp (sampleRec N ⇑W - harmonicWriterAcceleration q (sampleRec N ⇑V))
      κ.1.1 κ.1.2) = cx (fun x => (harmA (minkowski + q x))⁻¹) *
      (cx (aArr q) * cx (comp (sampleRec N ⇑W - harmonicWriterAcceleration q
        (sampleRec N ⇑V)) κ.1.1 κ.1.2) -
        PeriodicGridSobolev.Sampling.sample N (rowF Q V W Qd Vd Qdd κ.1.1 κ.1.2)) := by
    have hz : PeriodicGridSobolev.Sampling.sample N (rowF Q V W Qd Vd Qdd κ.1.1 κ.1.2) = 0 := by
      funext x
      simp [PeriodicGridSobolev.Sampling.sample, rowF, hrow]
    rw [hz, sub_zero]
    funext x
    simp only [Pi.mul_apply, cx_apply, aArr]
    have hax := ha x
    simp only [aArr] at hax
    have hax' : ((harmA (minkowski + q x) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hax
    push_cast
    field_simp
  rw [e]
  refine (sobNorm_coef_mul_le (s - 2) (by omega) _ _ 1 (by simp) hinv1).trans ?_
  have := hc κ.1.1 κ.1.2
  calc (A + 1) * PeriodicGridSobolev.sobNorm (s - 2) _ ≤ (A + 1) * (Cc * (N : ℝ)⁻¹ * X) := by
        gcongr
    _ = (A + 1) * Cc * (N : ℝ)⁻¹ * X := by ring

/-! ### The lower-order Cauchy comparison -/

/-- Continuity of the writer acceleration along a continuous history in the analytic chart. -/
theorem continuousOn_accel_history (s : ℕ) (hs : 1 ≤ s) :
    ∃ ρ > 0, ∀ (N : ℕ) [NeZero N] (T : ℝ) (q v : ℝ → Grid N → MetricRec),
      (∀ t ∈ Set.Icc 0 T, ContinuousAt q t) → (∀ t ∈ Set.Icc 0 T, ContinuousAt v t) →
      (∀ t ∈ Set.Icc 0 T, IsSymRec (q t)) → (∀ t ∈ Set.Icc 0 T, Xnorm s (q t) (v t) ≤ ρ) →
      ContinuousOn (fun t => harmonicWriterAcceleration (q t) (v t)) (Set.Icc 0 T) := by
  obtain ⟨r₀, hr₀, hchart⟩ := exists_det_chart
  have hS := supConst_nonneg
  refine ⟨r₀ / (2 * (supConst + 1)), div_pos hr₀ (by linarith),
    fun N _ T q v hqc hvc hqs hX => ?_⟩
  intro t ht
  have hz : ∀ z, ‖(minkowski + q t z) - minkowski‖ < r₀ := by
    intro z
    rw [add_sub_cancel_left]
    have h1 := norm_q_le s hs (hqs t ht) (v t) z
    have h2 : supConst * Xnorm s (q t) (v t) ≤ supConst * (r₀ / (2 * (supConst + 1))) :=
      mul_le_mul_of_nonneg_left (hX t ht) hS
    have h3 : supConst * (r₀ / (2 * (supConst + 1))) < r₀ := by
      rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
      nlinarith
    exact lt_of_le_of_lt h1 (h2.trans_lt h3)
  have hcomp : ∀ x μ ν, ContinuousAt (fun τ => harmonicWriterAcceleration (q τ) (v τ) x μ ν) t := by
    intro x μ ν
    have hA := analyticAt_accel ((q t, v t) : State N) (fun z => (hchart _ (hz z)).1)
      (fun z => (hchart _ (hz z)).2) x μ ν
    have hpath : ContinuousAt (fun τ => ((q τ, v τ) : State N)) t :=
      (hqc t ht).prodMk (hvc t ht)
    exact hA.continuousAt.comp_of_eq hpath rfl
  exact (continuousAt_pi.2 fun x => continuousAt_pi.2 fun μ => continuousAt_pi.2 fun ν =>
    hcomp x μ ν).continuousWithinAt

theorem Fnorm_neg {N : ℕ} [NeZero N] (r : ℕ) (F : Grid N → MetricRec) : Fnorm r (-F) = Fnorm r F := by
  unfold Fnorm
  congr 1
  refine sum_congr rfl fun κ _ => ?_
  have e : cx (comp (-F) κ.1.1 κ.1.2) = -cx (comp F κ.1.1 κ.1.2) := by
    funext x; simp [cx, comp]
  rw [e, ← PeriodicGridSobolev.sobNorm_sq, ← PeriodicGridSobolev.sobNorm_sq,
    PeriodicGridSobolev.Moser.sobNorm_neg]

/-- **`lem:supp-open-continuum-comparison` (lower-order Cauchy comparison and acceleration
recovery).**  For `s ≥ 5` there are `δ > 0` and `K, C ≥ 0`, independent of the mesh `h = 1/N`,
such that: if `X_h = (q, v)` solves the central (open) writer on `[0, T]` in the grid top ball
`‖X_h‖_{X^s_h} ≤ δ`, and `g = η + Q` is a continuum solution of the harmonic normal row on
`[0, T]` (`IsContSolution`, `Q ∈ H^{s+1}`, `∂ₜQ = V ∈ H^s`, `∂ₜ²Q = W`) in the continuum top ball
`‖(Q, V)‖_top ≤ ε ≤ δ`, then with `Y_h = 𝒮_h(g - η, ∂ₜg)` and
`e_{0,h} = ‖X_h(0) - Y_h(0)‖_{X^{s-2}_h}`, for every `t ∈ [0, T]`
`‖q_h - 𝒮_h(g - η)‖_{s-1,h}`, `‖v_h - 𝒮_h ∂ₜg‖_{s-2,h}` (jointly, the `X^{s-2}_h` norm) and,
componentwise, `‖q_{h,tt} - 𝒮_h ∂ₜ²g‖_{s-3,h}` (`q_{h,tt} = V_{0,h}(q, v)`) are bounded by
`C e^{K t} (e_{0,h} + (1 + t) h ε)`; on the common interval `[0, T_s]` this is
`eq:supp-open-sampled-comparison` with constant `C e^{K T_s}(1 + T_s)`. -/
theorem continuum_comparison (s : ℕ) (hs : 5 ≤ s) :
    ∃ δ > 0, ∃ K ≥ 0, ∃ C ≥ 0, ∀ (N : ℕ) [NeZero N] (T : ℝ) (q v : ℝ → Grid N → MetricRec)
      (Q V W : ℝ → C(T3, MetricRec)) (Qd Vd : ℝ → Fin 3 → C(T3, MetricRec))
      (Qdd : ℝ → Fin 3 → Fin 3 → C(T3, MetricRec)) (ε : ℝ),
      IsWriterSolution T q v → (∀ t ∈ Set.Icc 0 T, Xnorm s (q t) (v t) ≤ δ) →
      IsContSolution s T Q V W Qd Vd Qdd → (∀ t ∈ Set.Icc 0 T, contTop s (Q t) (V t) ≤ ε) →
      ε ≤ δ → ∀ t ∈ Set.Icc 0 T,
        Xnorm (s - 2) (q t - sampleRec N ⇑(Q t)) (v t - sampleRec N ⇑(V t)) ≤
          C * Real.exp (K * t) * (Xnorm (s - 2) (q 0 - sampleRec N ⇑(Q 0))
            (v 0 - sampleRec N ⇑(V 0)) + (1 + t) * ((N : ℝ)⁻¹ * ε)) ∧
        ∀ κ : Upper, PeriodicGridSobolev.sobNorm (s - 3)
          (cx (comp (harmonicWriterAcceleration (q t) (v t) - sampleRec N ⇑(W t)) κ.1.1 κ.1.2)) ≤
          C * Real.exp (K * t) * (Xnorm (s - 2) (q 0 - sampleRec N ⇑(Q 0))
            (v 0 - sampleRec N ⇑(V 0)) + (1 + t) * ((N : ℝ)⁻¹ * ε)) := by
  obtain ⟨δd, hδd, Kd, hKd, hdiff⟩ := open_writer_difference s (s - 2) (by omega) (by omega)
  obtain ⟨δa, hδa, Ka, hKa, hacc⟩ := dAcc_bound s (s - 2) (by omega) (by omega)
  obtain ⟨δf, hδf, Cf, hCf, hforce⟩ := sampled_force_bound s (by omega)
  obtain ⟨Cx, hCx, hXs⟩ := Xnorm_sample_le s (by omega)
  obtain ⟨ρc, hρc, hcont⟩ := continuousOn_accel_history s (by omega)
  set δ : ℝ := min (min δd δa) (min δf (min (δd / (Cx + 1)) (min (δa / (Cx + 1))
    (ρc / (Cx + 1)))))
  have hδ : 0 < δ := by positivity
  set Cfin : ℝ := (Ka + 1) * (6 + 2 * Kd * Cf + Cf)
  refine ⟨δ, hδ, Kd, hKd, Cfin, by positivity,
    fun N _ T q v Q V W Qd Vd Qdd ε hsol hXq hsolc hXQ hεδ t ht => ?_⟩
  have hT : 0 ≤ T := ht.1.trans ht.2
  set h : ℝ := (N : ℝ)⁻¹
  have hh : 0 ≤ h := by positivity
  set p : ℝ → Grid N → MetricRec := fun τ => sampleRec N ⇑(Q τ)
  set w : ℝ → Grid N → MetricRec := fun τ => sampleRec N ⇑(V τ)
  set f : ℝ → Grid N → MetricRec := fun τ =>
    sampleRec N ⇑(W τ) - harmonicWriterAcceleration (p τ) (w τ)
  have hε0 : 0 ≤ ε := (contTop_nonneg s _ _).trans (hXQ 0 ⟨le_rfl, hT⟩)
  -- the sampled record is in the grid top ball
  have hYX : ∀ τ ∈ Set.Icc 0 T, Xnorm s (p τ) (w τ) ≤ Cx * ε := fun τ hτ =>
    (hXs N (Q τ) (V τ) (hsolc.regQ τ hτ) (hsolc.regV τ hτ)).trans
      (mul_le_mul_of_nonneg_left (hXQ τ hτ) hCx)
  have hCxδ : ∀ a : ℝ, 0 < a → δ ≤ a / (Cx + 1) → Cx * ε ≤ a := by
    intro a ha hδa'
    have h1 : ε ≤ a / (Cx + 1) := hεδ.trans hδa'
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith
  have hYd : ∀ τ ∈ Set.Icc 0 T, Xnorm s (p τ) (w τ) ≤ δd := fun τ hτ =>
    (hYX τ hτ).trans (hCxδ δd hδd ((min_le_right _ _).trans ((min_le_right _ _).trans
      (min_le_left _ _))))
  have hYa : ∀ τ ∈ Set.Icc 0 T, Xnorm s (p τ) (w τ) ≤ δa := fun τ hτ =>
    (hYX τ hτ).trans (hCxδ δa hδa ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))))
  have hYc : ∀ τ ∈ Set.Icc 0 T, Xnorm s (p τ) (w τ) ≤ ρc := fun τ hτ =>
    (hYX τ hτ).trans (hCxδ ρc hρc ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))))
  -- the sampled force
  have hfb : ∀ τ ∈ Set.Icc 0 T, Fnorm (s - 2) (f τ) ≤ Cf * h * ε := by
    intro τ hτ
    have hδf' : contTop s (Q τ) (V τ) ≤ δf :=
      (hXQ τ hτ).trans (hεδ.trans ((min_le_right _ _).trans (min_le_left _ _)))
    refine (hforce N (Q τ) (V τ) (W τ) (Qd τ) (Vd τ) (Qdd τ) (hsolc.jet τ hτ) (hsolc.regQ τ hτ)
      (hsolc.regV τ hτ) hδf' (hsolc.row τ hτ)).trans ?_
    exact mul_le_mul_of_nonneg_left (hXQ τ hτ) (by positivity)
  -- time derivatives of the sampled record
  have hpd : ∀ τ ∈ Set.Icc 0 T, ∀ x, HasDerivAt (fun σ => p σ x) (w τ x) τ := fun τ hτ x =>
    hsolc.dQ τ hτ _
  have hwd : ∀ τ ∈ Set.Icc 0 T, ∀ x (κ : Upper), HasDerivAt (fun σ => w σ x κ.1.1 κ.1.2)
      (harmonicWriterAcceleration (p τ) (w τ) x κ.1.1 κ.1.2 + f τ x κ.1.1 κ.1.2) τ := by
    intro τ hτ x κ
    have h1 := hasDerivAt_pi.mp (hasDerivAt_pi.mp (hsolc.dV τ hτ
      (PeriodicGridSobolev.samplePt x)) κ.1.1) κ.1.2
    have ef : f τ x κ.1.1 κ.1.2 = W τ (PeriodicGridSobolev.samplePt x) κ.1.1 κ.1.2 -
        harmonicWriterAcceleration (p τ) (w τ) x κ.1.1 κ.1.2 := rfl
    have h2 : HasDerivAt (fun σ => w σ x κ.1.1 κ.1.2)
        (W τ (PeriodicGridSobolev.samplePt x) κ.1.1 κ.1.2) τ := h1
    exact h2.congr_deriv (by rw [ef]; ring)
  have hpc : ∀ τ ∈ Set.Icc 0 T, ContinuousAt p τ := fun τ hτ =>
    (hasDerivAt_pi.2 fun x => hpd τ hτ x).continuousAt
  have hwc : ∀ τ ∈ Set.Icc 0 T, ContinuousAt w τ := fun τ hτ =>
    (hasDerivAt_pi.2 fun x => hasDerivAt_pi.2 fun μ => hasDerivAt_pi.2 fun ν =>
      hasDerivAt_pi.mp (hasDerivAt_pi.mp (hsolc.dV τ hτ (PeriodicGridSobolev.samplePt x)) μ) ν).continuousAt
  have hsymp : ∀ τ ∈ Set.Icc 0 T, IsSymRec (p τ) := fun τ hτ =>
    isSymRec_sampleRec (hsolc.symQ τ hτ)
  have hsymw : ∀ τ ∈ Set.Icc 0 T, IsSymRec (w τ) := fun τ hτ =>
    isSymRec_sampleRec (hsolc.symV τ hτ)
  have hfc : ContinuousOn f (Set.Icc 0 T) := by
    have h1 : ContinuousOn (fun τ => sampleRec N ⇑(W τ)) (Set.Icc 0 T) :=
      continuousOn_pi.2 fun x => hsolc.contW (PeriodicGridSobolev.samplePt x)
    exact h1.sub (hcont N T p w hpc hwc hsymp hYc)
  -- the forced pair
  have hpair : IsForcedPair s δd T q p v w (fun _ => 0) f := by
    intro τ hτ
    obtain ⟨hqs, hvs, hq, hv⟩ := hsol τ hτ
    refine ⟨hqs, hvs, hsymp τ hτ, hsymw τ hτ, hq, hpd τ hτ, fun x κ => ?_, hwd τ hτ,
      (hXq τ hτ).trans (min_le_left _ _ |>.trans (min_le_left _ _)), hYd τ hτ⟩
    simpa using hv x κ
  have hD := hdiff N T q p v w (fun _ => 0) f hpair continuousOn_const hfc t ht
  -- the integral of the force
  have hint : ∫ τ in (0)..t, Fnorm (s - 2) ((fun _ => (0 : Grid N → MetricRec)) τ - f τ) ≤
      t * (Cf * h * ε) := by
    have hic : ContinuousOn (fun τ => Fnorm (s - 2) ((fun _ => (0 : Grid N → MetricRec)) τ - f τ))
        (Set.Icc 0 t) :=
      (continuous_Fnorm (s - 2)).comp_continuousOn
        (continuousOn_const.sub (hfc.mono (Set.Icc_subset_Icc le_rfl ht.2)))
    have h1 : ∫ τ in (0)..t, Fnorm (s - 2) ((fun _ => (0 : Grid N → MetricRec)) τ - f τ) ≤
        ∫ _τ in (0)..t, Cf * h * ε := intervalIntegral.integral_mono_on ht.1
      (hic.intervalIntegrable_of_Icc ht.1) intervalIntegrable_const
      (fun τ hτ => by
        simp only [zero_sub, Fnorm_neg]
        exact hfb τ ⟨hτ.1, hτ.2.trans ht.2⟩)
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at h1
    exact h1
  set e0 := Xnorm (s - 2) (q 0 - p 0) (v 0 - w 0)
  have he0 : 0 ≤ e0 := Xnorm_nonneg _ _ _
  set E := e0 + (1 + t) * (h * ε)
  have hhe : 0 ≤ h * ε := mul_nonneg hh hε0
  have hE : e0 + t * (h * ε) ≤ E := by
    simp only [E]; nlinarith
  have hexp1 : 1 ≤ Real.exp (Kd * t) := Real.one_le_exp (mul_nonneg hKd ht.1)
  have hDiff : Xnorm (s - 2) (q t - p t) (v t - w t) ≤
      Real.exp (Kd * t) * ((6 + 2 * Kd * Cf) * E) := by
    refine hD.trans ?_
    have h1 : Kd * ∫ τ in (0)..t, Fnorm (s - 2) ((fun _ => (0 : Grid N → MetricRec)) τ - f τ) ≤
        Kd * (t * (Cf * h * ε)) := mul_le_mul_of_nonneg_left hint hKd
    have hpos : 0 ≤ Real.exp (Kd * t) := (Real.exp_pos _).le
    have h2 : 3 * e0 + Kd * (t * (Cf * h * ε)) ≤ (6 + 2 * Kd * Cf) * E / 2 := by
      have h3 : t * (h * ε) ≤ (1 + t) * (h * ε) := by nlinarith
      have hKC : 0 ≤ Kd * Cf := mul_nonneg hKd hCf
      have h4 := mul_le_mul_of_nonneg_left h3 hKC
      have h5 := mul_nonneg hKC he0
      have h6 : 0 ≤ (1 + t) * (h * ε) := mul_nonneg (by linarith [ht.1]) hhe
      have e1 : Kd * (t * (Cf * h * ε)) = Kd * Cf * (t * (h * ε)) := by ring
      rw [e1]
      simp only [E]
      nlinarith
    calc 2 * Real.exp (Kd * t) * (3 * e0 + Kd * ∫ τ in (0)..t,
          Fnorm (s - 2) ((fun _ => (0 : Grid N → MetricRec)) τ - f τ))
        ≤ 2 * Real.exp (Kd * t) * (3 * e0 + Kd * (t * (Cf * h * ε))) := by gcongr
      _ ≤ 2 * Real.exp (Kd * t) * ((6 + 2 * Kd * Cf) * E / 2) := by gcongr
      _ = Real.exp (Kd * t) * ((6 + 2 * Kd * Cf) * E) := by ring
  have hE0 : 0 ≤ E := le_trans (add_nonneg he0 (mul_nonneg ht.1 hhe)) hE
  refine ⟨?_, fun κ => ?_⟩
  · refine hDiff.trans ?_
    have : (6 + 2 * Kd * Cf) ≤ Cfin := by
      simp only [Cfin]
      have h1 : 0 ≤ Ka * (6 + 2 * Kd * Cf + Cf) := by positivity
      nlinarith
    calc Real.exp (Kd * t) * ((6 + 2 * Kd * Cf) * E) ≤ Real.exp (Kd * t) * (Cfin * E) := by
          gcongr
      _ = Cfin * Real.exp (Kd * t) * E := by ring
  · obtain ⟨hqs, hvs, -, -⟩ := hsol t ht
    have hA := hacc N (q t) (p t) (v t) (w t) 0 (f t) hqs (hsymp t ht) hvs (hsymw t ht)
      ((hXq t ht).trans (min_le_left _ _ |>.trans (min_le_right _ _))) (hYa t ht) κ
    have edA : dAcc (q t) (p t) (v t) (w t) 0 (f t) =
        harmonicWriterAcceleration (q t) (v t) - sampleRec N ⇑(W t) := by
      simp only [dAcc, f]
      abel
    have es : s - 2 - 1 = s - 3 := by omega
    rw [edA, es, zero_sub, Fnorm_neg] at hA
    refine hA.trans ?_
    have hfbt := hfb t ht
    have hhε : Cf * h * ε ≤ Cf * E := by
      have : h * ε ≤ E := by
        have : 0 ≤ t * (h * ε) := mul_nonneg ht.1 (mul_nonneg hh hε0)
        simp only [E]; nlinarith
      calc Cf * h * ε = Cf * (h * ε) := by ring
        _ ≤ Cf * E := mul_le_mul_of_nonneg_left this hCf
    have hexpE : Cf * E ≤ Real.exp (Kd * t) * (Cf * E) := by
      have : 0 ≤ Cf * E := mul_nonneg hCf hE0
      nlinarith
    calc Ka * (Xnorm (s - 2) (q t - p t) (v t - w t) + Fnorm (s - 2) (f t))
        ≤ Ka * (Real.exp (Kd * t) * ((6 + 2 * Kd * Cf) * E) + Real.exp (Kd * t) * (Cf * E)) := by
          gcongr
          exact hfbt.trans (hhε.trans hexpE)
      _ = Ka * ((6 + 2 * Kd * Cf + Cf) * (Real.exp (Kd * t) * E)) := by ring
      _ ≤ (Ka + 1) * ((6 + 2 * Kd * Cf + Cf) * (Real.exp (Kd * t) * E)) := by
          have : 0 ≤ (6 + 2 * Kd * Cf + Cf) * (Real.exp (Kd * t) * E) := by positivity
          nlinarith
      _ = Cfin * Real.exp (Kd * t) * E := by simp only [Cfin]; ring

/-! ### Non-vacuity: the flat solution -/

theorem harmonicSource_zero_jet (g : MetricRec) : harmonicSource g 0 = 0 := by
  have := harmonicSource_smul g 0 0
  simpa using this

theorem normalRow_zero : normalRow 0 0 0 (fun _ => 0) (fun _ => 0) (fun _ _ => 0) = 0 := by
  have h := harmonicSource_zero_jet minkowski
  simp only [normalRow, smul_zero, sum_const_zero, sub_zero, add_zero]
  rw [show ((0 : MetricRec), (fun _ => (0 : MetricRec))) = (0 : MetricRec × (Fin 3 → MetricRec))
    from rfl, h, sub_zero]

theorem isLineDeriv_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (i : Fin 3) :
    IsLineDeriv i (fun _ : T3 => (0 : E)) (fun _ => 0) := fun _ => hasDerivAt_const _ _

theorem ccoord_zero (k : Σ _ : Fin 4, Fin 4) : ccoord bM (0 : C(T3, MetricRec)) k = 0 := by
  ext x; simp

/-- The flat continuum history `g = η` is a continuum solution of the harmonic normal row. -/
theorem isContSolution_flat (s : ℕ) (T : ℝ) :
    IsContSolution s T (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ _ => 0) (fun _ _ => 0)
      (fun _ _ _ => 0) where
  jet := fun _ _ => ⟨fun i => isLineDeriv_zero i, fun i _ => isLineDeriv_zero i,
    fun i => isLineDeriv_zero i⟩
  dQ := fun _ _ _ => hasDerivAt_const _ _
  dV := fun _ _ _ => hasDerivAt_const _ _
  contW := fun _ => continuousOn_const
  row := fun _ _ _ => normalRow_zero
  symQ := fun _ _ _ _ _ => rfl
  symV := fun _ _ _ _ _ => rfl
  regQ := fun _ _ k => by rw [ccoord_zero]; exact memH_zero _
  regV := fun _ _ k => by rw [ccoord_zero]; exact memH_zero _

/-- Non-vacuity of `continuum_comparison`: the flat grid history and the flat continuum solution
satisfy every hypothesis. -/
example (s : ℕ) (hs : 5 ≤ s) : True := by
  obtain ⟨δ, hδ, K, hK, C, hC, h⟩ := continuum_comparison s hs
  have hX : Xnorm s (0 : Grid 5 → MetricRec) 0 ≤ δ := by
    have : Xsq s (0 : Grid 5 → MetricRec) 0 = 0 := by
      unfold Xsq
      refine sum_eq_zero fun κ _ => ?_
      have e : cx (comp (0 : Grid 5 → MetricRec) κ.1.1 κ.1.2) = 0 := by funext x; simp [comp, cx]
      rw [e]
      simp [PeriodicGridSobolev.sobSq, PeriodicGridSobolev.gridNormSq]
    rw [Xnorm, this, Real.sqrt_zero]; exact hδ.le
  have hsol : IsWriterSolution 1 (fun _ => (0 : Grid 5 → MetricRec)) (fun _ => 0) := by
    intro t _
    refine ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun x => hasDerivAt_const _ _, fun x κ => ?_⟩
    rw [harmonicWriterAcceleration_zero]
    simpa using hasDerivAt_const t (0 : ℝ)
  have hc0 : contTop s (0 : C(T3, MetricRec)) 0 = 0 := by
    simp [contTop, ccoordSum, ccoord_zero, sn, PeriodicGridSobolev.trigSobSq,
      mFourierCoeff_zero']
  have := h 5 1 (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ _ => 0)
    (fun _ _ => 0) (fun _ _ _ => 0) 0 hsol (fun _ _ => hX) (isContSolution_flat s 1)
    (fun _ _ => by rw [hc0]) hδ.le 0 ⟨le_rfl, zero_le_one⟩
  trivial

end

end RenewalGeometry.OpenWriterContinuum
