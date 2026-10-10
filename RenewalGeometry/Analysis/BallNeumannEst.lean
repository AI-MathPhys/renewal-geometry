/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.BallMatNorms

/-!
# The quantitative `H^{k+2}` estimate for the Neumann problem on a ball (all `k`)
  (stage D2 of the ball rendering of Uhlenbeck's small-energy gauge theorem)

Generic infrastructure (no renewal notions) for `prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript.

* `E0 k` — mean-zero jets of `H^k(B)` (closed subspace);
* `solJetCLM k : E0 k →L H^{k+2}(B)` — **the Neumann solution operator** `F ↦ jet of Sol F`,
  well defined by `neumann_Hk_weak`, linear by uniqueness of jets (`HsB_ext`), and continuous by
  the closed graph theorem (the function component depends continuously on `F` through the
  Lax–Milgram solution `solCLM`);
* `fn_eq_solFn` — a weakly Neumann mean-zero `X ∈ H⁵(B)` is the Neumann solution of `ΔX`;
* `neumann_est` (**main result**): there is `C_k` with
  `‖X‖_{H^{k+2}(B)} ≤ C_k (‖ΔX‖_{H^k(B)} + ‖X‖_{L²(B)})` for weakly Neumann `X ∈ H^{t+2}(B)`,
  `k ≤ t`.
-/

open MeasureTheory Set Metric Filter Topology NormedSpace
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator RealInnerProductSpace

noncomputable section

namespace RenewalGeometry.BallAnalysis.BallAlg

open SobolevOpen BallReg SobAlg

set_option linter.unusedSectionVars false

variable {c : Fin 4 → ℝ} {r : ℝ} [hr : Fact (0 < r)]

/-! ### The Neumann solution as a function of the data -/

/-- The function component of the Neumann solution, as a continuous linear map on `L²(B)`. -/
def solL2 : L2B c r →L[ℝ] L2B c r :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Option (Fin 4) => L2B c r) none).comp
    ((H1B0 c r).subtypeL.comp (solCLM c r))

theorem coe_solL2 (F : L2B c r) : ((solL2 F : L2B c r) : (Fin 4 → ℝ) → ℝ) = solFn c r F := rfl

/-- **A weakly Neumann mean-zero `X ∈ H⁵(B)` is the Neumann solution of its Laplacian.** -/
theorem fn_eq_solFn {X : SobAlg c r 5} (hN : IsNeumannS X) (hm : meanS X = 0) :
    fn X =ᵐ[volume.restrict (euclBall c r)]
      solFn c r ((memLp_fn (lapS X)).toLp (fn (lapS X))) := by
  set A : Fin 4 → Fin 1 → Fin 1 → SobAlg c r 4 := fun _ _ _ => 0
  have htan : ∀ k l, IsTangentialS (fun ν => A ν k l) := fun _ _ => isTangentialS_zero
  set η : Fin 1 → SobAlg c r 5 := fun _ => X
  have hm' : ∀ k, meanS (η k) = 0 := fun _ => hm
  have hlin : linOpS A η = fun _ => lapS X := by
    funext k
    simp only [linOpS, A, η, zero_mul]
    have : divS (fun _ : Fin 4 => (0 : SobAlg c r 4)) = 0 := by simp [divS]
    simp [this]
  have hw := weak_toXi htan (fun _ => hN) hm'
  have hξ : ∀ ζ, dirFormN c r 1 (toXi η hm') ζ + couplingN c r 1 (memLp_coefFn A) (toXi η hm') ζ =
      loadN (linOpS A η) ζ := by
    intro ζ
    rw [hw ζ, loadN_apply]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_fn_mul _ (Lp.memLp _), Lp.toLp_coeFn]
    congr 1
    exact (Lp.toLp_coeFn (fnL _) (memLp_fn _)).symm
  have hc := component_eq_sol htan hξ 0
  have hcd : compData A (linOpS A η) (toXi η hm') 0 =
      (memLp_fn (lapS X)).toLp (fn (lapS X)) := by
    apply Lp.ext
    have h0 : ∀ l, divData A 0 l (((toXi η hm' l : H1B0 c r) : H1Amb c r))
        =ᵐ[volume.restrict (euclBall c r)] fun _ => 0 := by
      intro l
      have hd : divS (fun ν => A ν 0 l) = 0 := by simp [divS, A]
      filter_upwards [fn_zero (c := c) (r := r) (s := 3), fn_zero (c := c) (r := r) (s := 4)]
        with z h1 h2
      simp only [divData, A, hd, h1, h2, zero_mul, Finset.sum_const_zero, add_zero]
    filter_upwards [compData_ae A (linOpS A η) (toXi η hm') 0, ae_all_iff.mpr h0,
      (memLp_fn (lapS X)).coeFn_toLp] with z hz hz0 hz1
    rw [hz, hlin, hz1]
    simp [hz0]
  have e1 : solFn c r (compData A (linOpS A η) (toXi η hm') 0) =
      (((toXi η hm' 0 : H1B0 c r) : H1Amb c r) none : (Fin 4 → ℝ) → ℝ) := by
    unfold solFn; rw [← hc]
  rw [← hcd, e1, toXi_apply]
  exact (toH1_none_ae X).symm

/-! ### The solution operator on jets -/

/-- The function component of a jet, as a continuous linear map. -/
def nilL (k : ℕ) : HsB c r k →L[ℝ] L2B c r :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : ↥(wordsUpTo 4 k) => L2B c r) (nilW k)).comp (HsB c r k).subtypeL

theorem nilL_apply (k : ℕ) (F : HsB c r k) : nilL k F = (F : JetAmb c r k) (nilW k) := rfl

/-- Mean-zero jets. -/
def E0 (k : ℕ) : Submodule ℝ (HsB c r k) :=
  LinearMap.ker ((innerSL ℝ (oneB c r)).comp (nilL k)).toLinearMap

theorem isClosed_E0 (k : ℕ) : IsClosed (E0 (c := c) (r := r) k : Set (HsB c r k)) :=
  ContinuousLinearMap.isClosed_ker ((innerSL ℝ (oneB c r)).comp (nilL k))

instance (k : ℕ) : CompleteSpace (E0 (c := c) (r := r) k) := (isClosed_E0 k).completeSpace_coe

instance instNormedSpaceE0 (k : ℕ) : NormedSpace ℝ (E0 (c := c) (r := r) k) :=
  Submodule.normedSpace (E0 (c := c) (r := r) k)

theorem exists_solJet (k : ℕ) (F : HsB c r k) :
    ∃ J : HsB c r (k + 2), (nilL (k + 2) J : (Fin 4 → ℝ) → ℝ)
      =ᵐ[volume.restrict (euclBall c r)] solFn c r (nilL k F) := by
  have hF : MemHk (euclBall c r) k ((nilL k F : L2B c r) : (Fin 4 → ℝ) → ℝ) :=
    memHk_of_mem_HsB c r F.2 k (nilW k) (by simp [nilW])
  obtain ⟨J, hJ, hJae⟩ := exists_mem_HsB_of_memHk c r (neumann_Hk_weak c r k hF)
  exact ⟨⟨J, hJ⟩, hJae⟩

/-- The Neumann solution jet. -/
def solJet (k : ℕ) (F : HsB c r k) : HsB c r (k + 2) := (exists_solJet k F).choose

theorem solJet_spec (k : ℕ) (F : HsB c r k) :
    (nilL (k + 2) (solJet k F) : (Fin 4 → ℝ) → ℝ) =ᵐ[volume.restrict (euclBall c r)]
      solFn c r (nilL k F) := (exists_solJet k F).choose_spec

theorem nilL_solJet (k : ℕ) (F : HsB c r k) : nilL (k + 2) (solJet k F) = solL2 (nilL k F) :=
  Lp.ext (solJet_spec k F)

theorem solJet_ext (k : ℕ) {F : HsB c r k} {J : HsB c r (k + 2)}
    (h : nilL (k + 2) J = solL2 (nilL k F)) : J = solJet k F := by
  apply HsB_ext
  show ((nilL (k + 2) J : L2B c r) : (Fin 4 → ℝ) → ℝ) =ᵐ[volume.restrict (euclBall c r)]
    ((nilL (k + 2) (solJet k F) : L2B c r) : (Fin 4 → ℝ) → ℝ)
  rw [h, nilL_solJet]

/-- The Neumann solution operator on mean-zero jets, as a linear map. -/
def solJetLin (k : ℕ) : HsB c r k →ₗ[ℝ] HsB c r (k + 2) where
  toFun F := solJet k F
  map_add' F G := by
    symm
    apply solJet_ext
    rw [map_add, nilL_solJet, nilL_solJet]
    simp [map_add]
  map_smul' t F := by
    symm
    apply solJet_ext
    rw [map_smul, nilL_solJet]
    simp [map_smul]

set_option synthInstance.maxHeartbeats 200000 in
/-- **The Neumann solution operator is continuous** (closed graph theorem). -/
theorem continuous_solJetLin (k : ℕ) : Continuous (solJetLin (c := c) (r := r) k) := by
  apply LinearMap.continuous_of_isClosed_graph
  refine IsSeqClosed.isClosed fun {p} {q} hp hlim => ?_
  -- `p n = (F_n, T F_n) → q = (F, G)`
  have hp' : ∀ n, (p n).2 = solJetLin k (p n).1 := fun n => (hp n).symm.symm
  set F := q.1
  set G := q.2
  have h1 : Tendsto (fun n => (p n).1) atTop (𝓝 F) := (continuous_fst.tendsto q).comp hlim
  have h2 : Tendsto (fun n => (p n).2) atTop (𝓝 G) := (continuous_snd.tendsto q).comp hlim
  have h3 : Tendsto (fun n => nilL (k + 2) (p n).2) atTop (𝓝 (nilL (k + 2) G)) :=
    ((nilL (k + 2)).continuous.tendsto G).comp h2
  have h4 : Tendsto (fun n => solL2 (nilL k (p n).1)) atTop (𝓝 (solL2 (nilL k F))) :=
    ((solL2.comp (nilL k)).continuous.tendsto F).comp h1
  have h5 : ∀ n, nilL (k + 2) (p n).2 = solL2 (nilL k (p n).1) := fun n => by
    rw [hp' n]; exact nilL_solJet k _
  simp_rw [h5] at h3
  have h6 := tendsto_nhds_unique h3 h4
  show G = solJetLin k F
  exact solJet_ext k h6

set_option synthInstance.maxHeartbeats 200000 in
/-- The Neumann solution operator as a continuous linear map. -/
def solJetCLM (k : ℕ) : HsB c r k →L[ℝ] HsB c r (k + 2) :=
  ⟨solJetLin k, continuous_solJetLin k⟩

set_option synthInstance.maxHeartbeats 200000 in
theorem solJetCLM_apply (k : ℕ) (F : HsB c r k) : solJetCLM k F = solJet k F := rfl

end RenewalGeometry.BallAnalysis.BallAlg

namespace RenewalGeometry.BallAnalysis.BallAlg

open SobolevOpen BallReg SobAlg

variable {c : Fin 4 → ℝ} {r : ℝ} [hr : Fact (0 < r)]

/-! ### The quantitative Neumann estimate -/

theorem derS_restrS_any {s s' : ℕ} [Fact (3 ≤ s)] [Fact (3 ≤ s')] (i : Fin 4) (h : s' + 1 ≤ s + 1)
    (F : SobAlg c r (s + 1)) :
    derS i (restrS h F) = restrS (Nat.le_of_succ_le_succ h) (derS i F) :=
  derS_restrS_gen i (Nat.le_of_succ_le_succ h) F

/-- The Laplacian `H^{t+2}(B) → H^t(B)`. -/
def lap2 {t : ℕ} [Fact (3 ≤ t)] (X : SobAlg c r (t + 2)) : SobAlg c r t :=
  ∑ ν, derS ν (derS ν X)

theorem lapS_restrS {t : ℕ} [Fact (3 ≤ t)] (h5 : 5 ≤ t + 2) (X : SobAlg c r (t + 2)) :
    lapS (restrS h5 X) = restrS (by omega) (lap2 X) := by
  unfold lapS lap2
  rw [map_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [show restrS h5 X = restrS (Nat.succ_le_succ (by omega : 4 ≤ t + 1)) X from rfl,
    derS_restrS_any ν (Nat.succ_le_succ (by omega : 4 ≤ t + 1)) X,
    show restrS (Nat.le_of_succ_le_succ (Nat.succ_le_succ (by omega : 4 ≤ t + 1)))
      (derS ν X) = restrS (Nat.succ_le_succ (by omega : 3 ≤ t)) (derS ν X) from rfl,
    derS_restrS_any ν (Nat.succ_le_succ (by omega : 3 ≤ t)) (derS ν X)]

theorem exists_abs_meanS_le {s : ℕ} [Fact (3 ≤ s)] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ F : SobAlg c r s, |meanS F| ≤ C * sN 2 F := by
  have hfin := isFiniteMeasure_restrict_euclBall c hr.out.le
  set V := (volume.restrict (euclBall c r)) Set.univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal)
  have hV : V ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top _ _)
  refine ⟨V.toReal, ENNReal.toReal_nonneg, fun F => ?_⟩
  have h1 : |meanS F| ≤ (eLpNorm (fn F) 1 (volume.restrict (euclBall c r))).toReal := by
    unfold meanS
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_lintegral_norm _).trans (le_of_eq ?_)
    rw [eLpNorm_one_eq_lintegral_enorm]
    congr 1
    refine lintegral_congr fun x => ?_
    simp [Real.enorm_eq_ofReal_abs]
  have h2 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2) (by norm_num)
    (μ := volume.restrict (euclBall c r)) (memLp_fn F).aestronglyMeasurable
  refine h1.trans ?_
  rw [mul_comm]
  unfold sN
  rw [← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top (eLpNorm_fn_ne_top 2 F) hV) h2

theorem volB_pos : 0 < volB c r := by
  have hvol : volume (euclBall c r) ≠ ⊤ := ((measure_mono (euclBall_subset_closedBall c
    hr.out.le)).trans_lt (isCompact_closedBall c r).measure_lt_top).ne
  have hpos : 0 < volume (euclBall c r) := (isOpen_euclBall c r).measure_pos volume
    ⟨c, by show sqDist c c < r ^ 2; simp [sqDist]; exact pow_pos hr.out 2⟩
  exact ENNReal.toReal_pos hpos.ne' hvol

theorem lap2_sub_smul_one {t : ℕ} [Fact (3 ≤ t)] (X : SobAlg c r (t + 2)) (τ : ℝ) :
    lap2 (X - τ • (1 : SobAlg c r (t + 2))) = lap2 X := by
  have h1 : ∀ ν, derS ν (1 : SobAlg c r (t + 2)) = 0 := fun ν => derS_one ν
  simp [lap2, map_sub, map_smul, h1]

/-- **The quantitative Neumann estimate**: for weakly Neumann `X ∈ H^{t+2}(B)` and `k ≤ t`,
`‖X‖_{H^{k+2}(B)} ≤ C (‖ΔX‖_{H^k(B)} + ‖X‖_{L²(B)})`. -/
theorem neumann_est (k t : ℕ) [Fact (3 ≤ t)] (ht : 3 ≤ t) (hkt : k ≤ t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : SobAlg c r (t + 2), IsNeumannS (restrS (by omega : 5 ≤ t + 2) X) →
      ‖restrL c r (by omega : k + 2 ≤ t + 2) (jet X)‖ ≤
        C * (‖restrL c r hkt (jet (lap2 X))‖ + sN 2 X) := by
  obtain ⟨Cm, hCm0, hCm⟩ := exists_abs_meanS_le (c := c) (r := r) (s := t + 2)
  set K1 := ‖restrL c r (by omega : k + 2 ≤ t + 2) (jet (1 : SobAlg c r (t + 2)))‖
  have hvB := volB_pos (c := c) (r := r)
  refine ⟨‖solJetCLM (c := c) (r := r) k‖ + Cm * K1 / volB c r, by positivity, fun X hN => ?_⟩
  set τ := meanS X / volB c r
  set X₀ := X - τ • (1 : SobAlg c r (t + 2))
  have hN₀ : IsNeumannS (restrS (by omega : 5 ≤ t + 2) X₀) := by
    rw [isNeumannS_iff] at hN ⊢
    intro φ hφ
    have h1 := (isNeumannS_iff (c := c) (r := r) (1 : SobAlg c r 5)).mp isNeumannS_one φ hφ
    have e : restrS (by omega : 5 ≤ t + 2) X₀ =
        restrS (by omega : 5 ≤ t + 2) X - τ • (1 : SobAlg c r 5) := by
      simp only [X₀, map_sub, map_smul, restrS_one]
    rw [e, map_sub, map_smul, hN φ hφ, h1, smul_zero, sub_zero]
  have hm₀ : meanS (restrS (by omega : 5 ≤ t + 2) X₀) = 0 := by
    rw [meanS_eq_inner, show restrS (by omega : 5 ≤ t + 2) X₀ =
        restrS (by omega : 5 ≤ t + 2) X - τ • (1 : SobAlg c r 5) by
      simp only [X₀, map_sub, map_smul, restrS_one], map_sub, map_smul,
      inner_sub_right, inner_smul_right, ← meanS_eq_inner, ← meanS_eq_inner, meanS_one]
    have : meanS (restrS (by omega : 5 ≤ t + 2) X) = meanS X := rfl
    rw [this]
    simp only [τ]
    field_simp
    ring
  -- the jet of `X₀` is the Neumann solution of `ΔX`
  have hsol : restrL c r (by omega : k + 2 ≤ t + 2) (jet X₀) =
      solJet k (restrL c r hkt (jet (lap2 X))) := by
    apply solJet_ext
    apply Lp.ext
    have h1 := fn_eq_solFn hN₀ hm₀
    rw [lapS_restrS, lap2_sub_smul_one] at h1
    have e2 : (memLp_fn (restrS (by omega : 3 ≤ t) (lap2 X))).toLp
        (fn (restrS (by omega : 3 ≤ t) (lap2 X))) = nilL k (restrL c r hkt (jet (lap2 X))) :=
      Lp.toLp_coeFn _ _
    rw [e2] at h1
    exact h1
  -- the estimate
  have hX : jet X = jet X₀ + τ • jet (1 : SobAlg c r (t + 2)) := by
    have e : jet X₀ = jet X - τ • jet (1 : SobAlg c r (t + 2)) := by
      simp only [X₀, jet_sub]
      rfl
    rw [e]; abel
  have h1 : ‖restrL c r (by omega : k + 2 ≤ t + 2) (jet X)‖ ≤
      ‖solJetCLM (c := c) (r := r) k‖ * ‖restrL c r hkt (jet (lap2 X))‖ + |τ| * K1 := by
    rw [hX, map_add, map_smul]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [hsol, ← solJetCLM_apply]
      exact (solJetCLM k).le_opNorm _
    · rw [norm_smul, Real.norm_eq_abs]
  have h2 : |τ| ≤ Cm * sN 2 X / volB c r := by
    simp only [τ, abs_div, abs_of_pos hvB]
    gcongr
    exact hCm X
  calc ‖restrL c r (by omega : k + 2 ≤ t + 2) (jet X)‖
      ≤ ‖solJetCLM (c := c) (r := r) k‖ * ‖restrL c r hkt (jet (lap2 X))‖ + |τ| * K1 := h1
    _ ≤ ‖solJetCLM (c := c) (r := r) k‖ * ‖restrL c r hkt (jet (lap2 X))‖ +
          Cm * sN 2 X / volB c r * K1 := by gcongr
    _ ≤ (‖solJetCLM (c := c) (r := r) k‖ + Cm * K1 / volB c r) *
          (‖restrL c r hkt (jet (lap2 X))‖ + sN 2 X) := by
        have h3 : 0 ≤ ‖restrL c r hkt (jet (lap2 X))‖ := norm_nonneg _
        have h4 : 0 ≤ sN 2 X := sN_nonneg 2 X
        have h5 : 0 ≤ Cm * K1 / volB c r := by positivity
        have e : Cm * sN 2 X / volB c r * K1 = Cm * K1 / volB c r * sN 2 X := by ring
        rw [e]
        nlinarith [norm_nonneg (solJetCLM (c := c) (r := r) k)]

end RenewalGeometry.BallAnalysis.BallAlg
