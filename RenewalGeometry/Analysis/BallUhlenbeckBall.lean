/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.BallAssemblyTools

/-!
# Uhlenbeck's small-energy Coulomb gauge on a fixed ball, from uniform higher bounds
  (stage D4 of the ball rendering of Uhlenbeck's small-energy gauge theorem)

Generic infrastructure (no renewal notions) for `prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript.

* `CoulombHigherBounds c r L G` — the **uniform `H⁶` bounds of the closedness step** of the
  continuity method: for every jointly smooth family `B_f(t)` of connections and every
  sufficiently small `κ` (below a threshold `κ₀` independent of the family), the Coulomb gauge
  states along `t ∈ [0,1]` with coefficient `L⁴` norm `≤ κ` lift to `H⁶` with a uniform bound.
* `UhlenbeckBallIn c r m G 𝔤` — the clauses of `UhlenbeckGauge.UhlenbeckSmallEnergyGaugeIn` on the
  single ball `B_r(c)`.
* `uhlenbeckBallIn_of_bounds` (**main result**): for a Lie basis `L` of a Lie algebra of
  skew-Hermitian matrices and a closed `G` with `exp 𝔤 ⊆ G`, `G·G ⊆ G`, `Ad_G 𝔤 ⊆ 𝔤`,
  `CoulombHigherBounds c r L G → UhlenbeckBallIn c r m G L.lieAlg`.  The proof runs the continuity
  method (`coulomb_continuity_method`) along the pre-gauged dilation path
  `pathConn c r A t`, with the a-priori improvement of `coulomb_state_apriori`; the state at
  `t = 1` is lifted to every `H^k` (`coulomb_gauge_lift`), has a smooth representative `U`
  (`exists_smooth_rep_matrix`), and `R = U · pregauge c r A` is the Uhlenbeck gauge, with the
  `W^{1,2}` and `L⁴` bounds of the weak Coulomb a-priori estimate (`coulomb_apriori_weak`).
-/

open MeasureTheory Set Metric Filter Topology NormedSpace
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator

noncomputable section

namespace RenewalGeometry.BallAnalysis.UhlenbeckBall

open SobolevOpen BallReg BallAlg SobAlg FinalTools UhlenbeckCore WeakCoulomb CriticalGauge
  UhlenbeckGauge UhlenbeckPregauge UhlenbeckPath AssemblyTools

set_option linter.unusedSectionVars false

variable {m d : ℕ}

/-- **Uniform higher bounds for Coulomb gauge states** (the closedness input of the continuity
method): there is `κ₀ > 0` such that for every jointly smooth family `B_f(t)` and every
`κ ≤ κ₀` the Coulomb gauge states of `B_f(t)`, `t ∈ [0,1]`, with coefficient `L⁴` norm `≤ κ`
lift to `H⁶(B, M_m(ℂ))` with a uniform bound. -/
def CoulombHigherBounds (c : Fin 4 → ℝ) (r : ℝ) [Fact (0 < r)] (L : LieBasis m d)
    (G : Set (Matrix (Fin m) (Fin m) ℂ)) : Prop :=
  ∃ κ₀ : ℝ≥0∞, 0 < κ₀ ∧ ∀ (Bf : ℝ → MConn m)
    (_hBf : ∀ μ i j, ContDiff ℝ ∞ (fun p : ℝ × (Fin 4 → ℝ) => Bf p.1 μ p.2 i j))
    (hBt : ∀ t μ i j, ContDiff ℝ ∞ (fun x => Bf t μ x i j)),
    ∀ κ : ℝ≥0∞, κ ≤ κ₀ → ∃ K : ℝ, ∀ t ∈ Icc (0 : ℝ) 1, ∀ u a,
      IsCoulombState L G κ (fun μ => matOfSmooth (c := c) (r := r) 4 (Bf t μ) (hBt t μ)) u a →
      ∃ u6 : MatSob c r 6 m, rhoM u6 = u ∧ ‖u6‖ ≤ K

/-- **Uhlenbeck's small-energy Coulomb gauge theorem on the single ball `B_r(c)`** (the clauses
of `UhlenbeckGauge.UhlenbeckSmallEnergyGaugeIn` for one ball). -/
def UhlenbeckBallIn (c : Fin 4 → ℝ) (r : ℝ) (m : ℕ) (G 𝔤 : Set (Matrix (Fin m) (Fin m) ℂ)) :
    Prop :=
  ∃ εU : ℝ≥0, 0 < εU ∧ ∃ CU Cr : ℝ≥0,
    ∀ A : MConn m, IsSmoothUnitaryConn A → (∀ μ y, A μ y ∈ 𝔤) → curvEnergy A (eBall c r) ≤ εU →
      ∃ R : (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ,
        (∀ y ∈ eBall c r, R y ∈ G) ∧
        (∀ c' e', ContDiffOn ℝ ∞ (fun y => R y c' e') (eBall c r)) ∧
        (∀ x ∈ eBall c r, ∀ c' e', ∑ μ, entryGrad (gaugeConn R A) μ c' e' μ x = 0) ∧
        (∀ ν c' e', MemW12 (eBall c r) (entries (gaugeConn R A) ν c' e')
          (entryGrad (gaugeConn R A) ν c' e')) ∧
        (∀ ν c' e', w12Norm (eBall c r) (entries (gaugeConn R A) ν c' e')
          (entryGrad (gaugeConn R A) ν c' e') ≤ Cr * curvEnergy A (eBall c r) ^ (1 / 2 : ℝ)) ∧
        (∀ ν c' e', eLpNorm (entries (gaugeConn R A) ν c' e') 4 (volume.restrict (eBall c r)) ≤
          CU * curvEnergy A (eBall c r) ^ (1 / 2 : ℝ))

theorem eBall_eq_euclBall (c : Fin 4 → ℝ) (r : ℝ) : eBall c r = euclBall c r := rfl

theorem one_mem_of_gaugeGroupData (L : LieBasis m d) {G : Set (Matrix (Fin m) (Fin m) ℂ)}
    (hGD : GaugeGroupData L G) : (1 : Matrix (Fin m) (Fin m) ℂ) ∈ G := by
  simpa using hGD.exp_mem 0 L.lieAlg.zero_mem

/-- The hypothesis shape of `coulomb_apriori_weak`. -/
def WeakAprioriData (m : ℕ) (δw Cw : ℝ≥0) : Prop :=
  ∀ (o : Fin 4 → ℝ) (r : ℝ), 0 < r → ∀ (a : Fin 4 → Fin m → Fin m → (Fin 4 → ℝ) → ℂ)
      (ga : Fin 4 → Fin m → Fin m → Fin 4 → (Fin 4 → ℝ) → ℂ),
      IsWeakBallCoulomb o r a ga → bL4 o r a ≤ δw →
      bL4 o r a ≤ Cw * wCurvNorm o r a ga ∧
      wGradNorm o r ga ≤ 32 * (m : ℝ≥0∞) ^ 2 * wCurvNorm o r a ga ∧
      (∀ ν c e, eLpNorm (a ν c e) 2 (volume.restrict (euclBall o r)) ≤
        2 * ENNReal.ofReal r * wCurvNorm o r a ga)

theorem single_le_sum3 {ι κ τ : Type*} [Fintype ι] [Fintype κ] [Fintype τ]
    (f : ι → κ → τ → ℝ≥0∞) (i : ι) (k : κ) (l : τ) : f i k l ≤ ∑ i, ∑ k, ∑ l, f i k l :=
  (Finset.single_le_sum (f := fun l => f i k l) (fun _ _ => zero_le) (Finset.mem_univ l)).trans
    ((Finset.single_le_sum (f := fun k => ∑ l, f i k l) (fun _ _ => zero_le)
      (Finset.mem_univ k)).trans
      (Finset.single_le_sum (f := fun i => ∑ k, ∑ l, f i k l) (fun _ _ => zero_le)
        (Finset.mem_univ i)))

section State

variable {c : Fin 4 → ℝ} {r : ℝ} [hr : Fact (0 < r)]

/-- **The Uhlenbeck gauge from a Coulomb state of the pre-gauged connection.**  A Coulomb gauge
state `(u, a)` of `B_f = pathConn c r A 1 = (pregauge c r A)·A` with small coefficient `L⁴` norm
gives the gauge `R = U · pregauge c r A` (`U` the smooth representative of `u`) with all clauses
of `UhlenbeckBallIn`, and with the constants of the weak a-priori estimate. -/
theorem gauge_of_state (L : LieBasis m d) {G : Set (Matrix (Fin m) (Fin m) ℂ)}
    (hGD : GaugeGroupData L G) {δw Cw : ℝ≥0} (hW : WeakAprioriData m δw Cw)
    {A : MConn m} (hA : IsSmoothUnitaryConn A) (h𝔤 : ∀ μ y, A μ y ∈ L.lieAlg)
    (hBt : ∀ μ i j, ContDiff ℝ ∞ (fun x => pathConn c r A 1 μ x i j))
    {κ : ℝ≥0∞} (hκ : L.Ke * κ ≤ δw) {u : MatSob c r 5 m} {a : Fin 4 → Fin d → SobAlg c r 4}
    (hst : IsCoulombState L G κ
      (fun μ => matOfSmooth (c := c) (r := r) 4 (pathConn c r A 1 μ) (hBt μ)) u a) :
    ∃ R : (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ,
      (∀ y ∈ eBall c r, R y ∈ G) ∧
      (∀ c' e', ContDiffOn ℝ ∞ (fun y => R y c' e') (eBall c r)) ∧
      (∀ x ∈ eBall c r, ∀ c' e', ∑ μ, entryGrad (gaugeConn R A) μ c' e' μ x = 0) ∧
      (∀ ν c' e', MemW12 (eBall c r) (entries (gaugeConn R A) ν c' e')
        (entryGrad (gaugeConn R A) ν c' e')) ∧
      (∀ ν c' e', w12Norm (eBall c r) (entries (gaugeConn R A) ν c' e')
        (entryGrad (gaugeConn R A) ν c' e') ≤
          ((2 * r.toNNReal + 32 * (m : ℝ≥0) ^ 2) * (16 * (m : ℝ≥0) ^ 2) : ℝ≥0) *
            curvEnergy A (eBall c r) ^ (1 / 2 : ℝ)) ∧
      (∀ ν c' e', eLpNorm (entries (gaugeConn R A) ν c' e') 4 (volume.restrict (eBall c r)) ≤
        (Cw * (16 * (m : ℝ≥0) ^ 2) : ℝ≥0) * curvEnergy A (eBall c r) ^ (1 / 2 : ℝ)) := by
  obtain ⟨hu, hG, hN, ha, hact, hcoul, hS⟩ := hst
  rw [eBall_eq_euclBall]
  set Bf := pathConn c r A 1 with hBfdef
  have hΩ : IsOpen (euclBall c r) := isOpen_euclBall c r
  have hΩm : MeasurableSet (euclBall c r) := measurableSet_euclBall c r
  -- lifts and the smooth representative
  have hcoulM : ∑ μ, derM μ (actM u (star u)
      (fun κ => matOfSmooth (c := c) (r := r) 4 (Bf κ) (hBt κ)) μ) = 0 := by
    rw [Finset.sum_congr rfl fun μ _ => congrArg (derM μ) (hact μ)]
    exact sum_derM_embX_eq_zero L hcoul
  obtain ⟨U, hUs, hUae, hdU⟩ := exists_smooth_rep_matrix (coulomb_gauge_lift hBt hu hN hcoulM)
  set P := pregauge c r A with hPdef
  have hPs : ∀ Ω, EntCDO P Ω := EntCDO.of_contDiff (contDiff_pregauge_entry hA)
  have hUs' : EntCDO U (euclBall c r) := hUs
  have hRs : EntCDO (fun y => U y * P y) (euclBall c r) := hUs'.mul (hPs _)
  have hPu : ∀ y, P y * star (P y) = 1 := fun y =>
    Matrix.mem_unitaryGroup_iff.mp (pregauge_unitary hA y)
  have hpt : ∀ x ∈ euclBall c r, ∀ μ,
      gaugeConn (fun y => U y * P y) A μ x = gaugeConn U Bf μ x := by
    intro x hx μ
    rw [gaugeConn_mul_apply A (hUs'.mDiffAt hΩ hx) ((hPs univ).mDiffAt isOpen_univ (mem_univ x))
      (hPu x) μ, hBfdef, pathConn_one]
  -- the a.e. identification with the Coulomb state
  have hae : ∀ μ, ∀ᵐ x ∂(volume.restrict (euclBall c r)),
      gaugeConn (fun y => U y * P y) A μ x = evM (embX L (a μ)) x := by
    intro μ
    set Bμ := matOfSmooth (c := c) (r := r) 4 (Bf μ) (hBt μ)
    filter_upwards [ae_restrict_mem hΩm, hUae, hdU μ,
      evM_sub (rhoM u * Bμ * rhoM (star u)) (derM μ u * rhoM (star u)),
      evM_mul (rhoM u * Bμ) (rhoM (star u)), evM_mul (rhoM u) Bμ,
      evM_mul (derM μ u) (rhoM (star u)), evM_star u,
      evM_matOfSmooth (c := c) (r := r) (s := 4) (hBt μ)] with x hx h1 h2 h3 h4 h5 h6 h7 h8
    rw [hpt x hx μ, ← hact μ]
    show _ = evM (rhoM u * Bμ * rhoM (star u) - derM μ u * rhoM (star u)) x
    rw [h3, h4, h5, h6, evM_rhoM, evM_rhoM, h7, h8, ← h1, ← h2]
    rfl
  -- the weak Coulomb data and the a-priori bounds
  set ρ := volume.restrict (euclBall c r) with hρ
  set X : Fin 4 → Fin m → Fin m → (Fin 4 → ℝ) → ℂ := fun ν i j x => evM (embX L (a ν)) x i j
    with hXdef
  set ga : Fin 4 → Fin m → Fin m → Fin 4 → (Fin 4 → ℝ) → ℂ :=
    fun ν i j μ x => evM (derM μ (embX L (a ν))) x i j with hgadef
  have hweak : IsWeakBallCoulomb c r X ga := isWeakBallCoulomb_embX L ha hcoul
  have hsmall : bL4 c r X ≤ δw :=
    (bL4_le_coords L a).trans ((by gcongr : L.Ke * coordL4 a ≤ L.Ke * κ).trans hκ)
  obtain ⟨hX4, hgrad, hL2⟩ := hW c r hr.out X ga hweak hsmall
  have hcurv : wCurvNorm c r X ga ≤
      16 * (m : ℝ≥0∞) ^ 2 * (∫⁻ x in euclBall c r, ‖curvVec Bf x‖ₑ ^ 2) ^ (1 / 2 : ℝ) :=
    wCurvNorm_state_le L hu hBt hact
  have hE1 : (∫⁻ x in euclBall c r, ‖curvVec Bf x‖ₑ ^ 2) ^ (1 / 2 : ℝ) ≤
      curvEnergy A (euclBall c r) ^ (1 / 2 : ℝ) :=
    ENNReal.rpow_le_rpow (curvEnergy_pathConn_le hr.out hA zero_le_one le_rfl) (by norm_num)
  have hWE : wCurvNorm c r X ga ≤ 16 * (m : ℝ≥0∞) ^ 2 * curvEnergy A (euclBall c r) ^ (1 / 2 : ℝ) :=
    hcurv.trans (by gcongr)
  set Ã := gaugeConn (fun y => U y * P y) A with hÃdef
  have hÃs : ∀ ν, EntCDO (Ã ν) (euclBall c r) := fun ν =>
    EntCDO.gaugeConn hΩ hRs (fun μ => EntCDO.of_contDiff (hA.smooth μ) _) ν
  have hent : ∀ ν i j, X ν i j =ᵐ[ρ] fun x => Ã ν x i j := fun ν i j => by
    filter_upwards [hae ν] with x hx
    rw [hx]
  have hgr : ∀ ν i j μ, pd (fun x => Ã ν x i j) μ =ᵐ[ρ] ga ν i j μ := fun ν i j μ =>
    pd_ae_eq_of_weak hΩ (hÃs ν i j) (hent ν i j) (hasWeakPartial_evM (embX L (a ν)) μ i j)
      (locallyIntegrableOn_of_memLp (memLp_evC _))
  have hUc : ContinuousOn U (euclBall c r) :=
    continuousOn_pi.mpr fun a => continuousOn_pi.mpr fun b => (hUs a b).continuousOn
  have hUG : ∀ y ∈ euclBall c r, U y ∈ G := mem_of_ae_mem_of_continuousOn hΩ hUc hGD.closed (by
    filter_upwards [hUae, hG] with x h1 h2
    rw [h1]; exact h2)
  refine ⟨fun y => U y * P y, fun y hy => hGD.mul_mem _ (hUG y hy) _
      (pregauge_mem L.lieAlg h𝔤 hGD.exp_mem y), fun c' e' => hRs c' e', ?_, ?_, ?_, ?_⟩
  · -- the Coulomb condition, pointwise on the open ball
    intro x hx c' e'
    have hc := eqOn_of_ae_eq_of_continuousOn hΩ
      (f := fun x => ∑ μ, pd (fun y => Ã μ y c' e') μ x) (g := fun _ => (0 : ℂ))
      (continuousOn_finsetSum _ fun μ _ => (hÃs μ).continuousOn_pd hΩ c' e' μ)
      continuousOn_const (by
        filter_upwards [hweak.coulomb c' e', ae_all_iff.mpr fun μ => hgr μ c' e' μ] with x h1 h2
        rw [Finset.sum_congr rfl fun μ _ => h2 μ]
        exact h1) hx
    exact hc
  · intro ν c' e'
    exact ⟨(memLp_evC _).ae_eq (hent ν c' e'), fun μ => (memLp_evC _).ae_eq (hgr ν c' e' μ).symm,
      fun μ => hasWeakPartial_of_contDiffOn hΩ ((hÃs ν c' e').of_le (by simp)) μ⟩
  · intro ν c' e'
    have e1 : eLpNorm (entries Ã ν c' e') 2 ρ = eLpNorm (X ν c' e') 2 ρ :=
      eLpNorm_congr_ae (hent ν c' e').symm
    have e2 : ∀ μ, eLpNorm (entryGrad Ã ν c' e' μ) 2 ρ = eLpNorm (ga ν c' e' μ) 2 ρ := fun μ =>
      eLpNorm_congr_ae (hgr ν c' e' μ)
    have hsum : ∑ μ, eLpNorm (ga ν c' e' μ) 2 ρ ≤ wGradNorm c r ga :=
      single_le_sum3 (fun ν c e => ∑ μ, eLpNorm (ga ν c e μ) 2 ρ) ν c' e'
    unfold w12Norm
    rw [e1, Finset.sum_congr rfl fun μ _ => e2 μ]
    calc eLpNorm (X ν c' e') 2 ρ + ∑ μ, eLpNorm (ga ν c' e' μ) 2 ρ
        ≤ 2 * ENNReal.ofReal r * wCurvNorm c r X ga + 32 * (m : ℝ≥0∞) ^ 2 * wCurvNorm c r X ga :=
          add_le_add (hL2 ν c' e') (hsum.trans hgrad)
      _ = (2 * ENNReal.ofReal r + 32 * (m : ℝ≥0∞) ^ 2) * wCurvNorm c r X ga := by ring
      _ ≤ (2 * ENNReal.ofReal r + 32 * (m : ℝ≥0∞) ^ 2) *
          (16 * (m : ℝ≥0∞) ^ 2 * curvEnergy A (euclBall c r) ^ (1 / 2 : ℝ)) := by gcongr
      _ = _ := by
          rw [ENNReal.ofReal]
          push_cast; ring
  · intro ν c' e'
    have e1 : eLpNorm (entries Ã ν c' e') 4 ρ = eLpNorm (X ν c' e') 4 ρ :=
      eLpNorm_congr_ae (hent ν c' e').symm
    rw [e1]
    calc eLpNorm (X ν c' e') 4 ρ ≤ bL4 c r X :=
          single_le_sum3 (fun ν c e => eLpNorm (X ν c e) 4 ρ) ν c' e'
      _ ≤ Cw * wCurvNorm c r X ga := hX4
      _ ≤ Cw * (16 * (m : ℝ≥0∞) ^ 2 * curvEnergy A (euclBall c r) ^ (1 / 2 : ℝ)) := by gcongr
      _ = _ := by push_cast; ring

/-- **Uhlenbeck's small-energy Coulomb gauge on a ball, from the uniform higher bounds.**
For a Lie basis `L` (a Lie algebra `𝔤 = L.lieAlg` of skew-Hermitian matrices) and a closed set `G`
with `G·G ⊆ G`, `exp 𝔤 ⊆ G`, `Ad_G 𝔤 ⊆ 𝔤` (`GaugeGroupData`), the uniform `H⁶` bounds of the
closedness step imply all clauses of Uhlenbeck's theorem on `B_r(c)`. -/
theorem uhlenbeckBallIn_of_bounds (L : LieBasis m d) {G : Set (Matrix (Fin m) (Fin m) ℂ)}
    (hGD : GaugeGroupData L G) (hHB : CoulombHigherBounds c r L G) :
    UhlenbeckBallIn c r m G L.lieAlg := by
  obtain ⟨δ₁, hδ₁, hcm⟩ := coulomb_continuity_method (c := c) (r := r) L hGD
    (one_mem_of_gaugeGroupData L hGD)
  obtain ⟨δa, hδa, Ca, hCa, hapr⟩ := coulomb_state_apriori (c := c) (r := r) L
  obtain ⟨κ₀, hκ₀, hHB'⟩ := hHB
  obtain ⟨δw, hδw, Cw, hW⟩ := coulomb_apriori_weak m
  set κ : ℝ≥0∞ := min (min (ENNReal.ofReal δ₁) (δa / 2)) (min κ₀ ((δw : ℝ≥0∞) / (L.Ke + 1)))
    with hκdef
  have hKe1 : L.Ke + 1 ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨L.Ke_ne_top, ENNReal.one_ne_top⟩
  have hκ0 : 0 < κ := lt_min (lt_min (ENNReal.ofReal_pos.mpr hδ₁) (ENNReal.half_pos hδa.ne'))
    (lt_min hκ₀ (ENNReal.div_pos (by exact_mod_cast hδw.ne') hKe1))
  have hκt : κ ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top ((min_le_left _ _).trans (min_le_left _ _))
  have hκδ : κ.toReal ≤ δ₁ :=
    ENNReal.toReal_le_of_le_ofReal hδ₁.le ((min_le_left _ _).trans (min_le_left _ _))
  have h2κ : 2 * κ ≤ δa :=
    calc 2 * κ ≤ 2 * (δa / 2) := by gcongr; exact (min_le_left _ _).trans (min_le_right _ _)
      _ = δa := ENNReal.mul_div_cancel two_ne_zero ENNReal.ofNat_ne_top
  have hκK : L.Ke * κ ≤ δw :=
    calc L.Ke * κ ≤ (L.Ke + 1) * ((δw : ℝ≥0∞) / (L.Ke + 1)) := by
          gcongr
          · exact le_self_add
          · exact (min_le_right _ _).trans (min_le_right _ _)
      _ = δw := ENNReal.mul_div_cancel (by simp) hKe1
  have hκκ₀ : κ ≤ κ₀ := (min_le_right _ _).trans (min_le_left _ _)
  set η : ℝ≥0 := κ.toNNReal with hηdef
  set CA : ℝ≥0 := Ca.toNNReal with hCAdef
  have hη : 0 < η := ENNReal.toNNReal_pos hκ0.ne' hκt
  refine ⟨(η / (CA + 1)) ^ 2, pow_pos (div_pos hη (by positivity)) 2, Cw * (16 * (m : ℝ≥0) ^ 2),
    (2 * r.toNNReal + 32 * (m : ℝ≥0) ^ 2) * (16 * (m : ℝ≥0) ^ 2), fun A hA h𝔤 hE => ?_⟩
  -- the continuity path
  set Bf : ℝ → MConn m := fun t => pathConn c r A t with hBfdef
  have hBf : ∀ μ i j, ContDiff ℝ ∞ (fun p : ℝ × (Fin 4 → ℝ) => Bf p.1 μ p.2 i j) :=
    fun μ i j => contDiff_pathConn_entry hA μ i j
  have hBt : ∀ t μ i j, ContDiff ℝ ∞ (fun x => Bf t μ x i j) :=
    fun t μ i j => contDiff_pathConn_slice hA t μ i j
  set B : ℝ → Fin 4 → MatSob c r 4 m := fun t μ => matOfSmooth 4 (Bf t μ) (hBt t μ) with hBdef
  have hBc : Continuous B := continuous_pi fun μ =>
    continuous_matOfSmooth_param (F := fun t => Bf t μ) (fun i j => hBf μ i j) (fun t => hBt t μ)
  have hBtan : ∀ t, B t ∈ tanM (c := c) (r := r) m := fun t =>
    matOfSmooth_mem_tanM c r (hBt t) (fun y hy => pathConn_tangential hr.out hA t hy)
  have hB𝔤 : ∀ t μ, ∀ᵐ x ∂(volume.restrict (euclBall c r)), evM (B t μ) x ∈ L.lieAlg := by
    intro t μ
    filter_upwards [evM_matOfSmooth (c := c) (r := r) (s := 4) (hBt t μ)] with x hx
    rw [hx]
    exact pathConn_mem L hA h𝔤 t μ x
  have hB0 : B 0 = fun _ => 0 := funext fun μ =>
    matOfSmooth_eq_zero _ fun x => by simp [hBfdef, pathConn_zero]
  have himp : ∀ t ∈ Icc (0 : ℝ) 1, ∀ u a, IsCoulombState L G (2 * κ) (B t) u a →
      coordL4 a ≤ κ := by
    rintro t ⟨ht0, ht1⟩ u a ⟨hu, -, -, ha, hact, hcoul, hS⟩
    have h1 := hapr u hu (Bf t) (hBt t) a ha hcoul hact (hS.trans h2κ)
    refine h1.trans ?_
    have hEt : (∫⁻ x in euclBall c r, ‖curvVec (Bf t) x‖ₑ ^ 2) ≤
        (((η / (CA + 1)) ^ 2 : ℝ≥0) : ℝ≥0∞) :=
      (curvEnergy_pathConn_le hr.out hA ht0 ht1).trans hE
    have := mul_rpow_half_le (CU := CA) (η := η) le_rfl hEt
    rwa [hCAdef, hηdef, ENNReal.coe_toNNReal hCa, ENNReal.coe_toNNReal hκt] at this
  obtain ⟨K, hK⟩ := hHB' Bf hBf hBt κ hκκ₀
  obtain ⟨u, a, hst⟩ := hcm κ hκ0 hκt hκδ B hBc hBtan hB𝔤 hB0 himp ⟨K, hK⟩
  exact gauge_of_state L hGD hW hA h𝔤 (hBt 1) hκK hst

end State

end RenewalGeometry.BallAnalysis.UhlenbeckBall
