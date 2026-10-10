/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.GeneratedCellVariation
import RenewalGeometry.Continuum.GeneratedResidualMaps

/-!
# The bulk rows of `D S^{(1)}` are the bosonic residual

Einstein–Standard-Model action-closure manuscript, `app:generated-dynamics` ("integration by
parts expresses `D S^{cmp}_{N,τ}` through the physical rows"):

* `traceRev_invol` — trace reversal is an involution (dimension four);
* **`bulkT_eq`** — for variational theory data with `κ ≠ 0`, the bulk rows of the cell variation
  (`GenCellVar.bulkT`) are the bilinear expression `bulkJ` in the bosonic residual
  `R_B = (𝓔^{tr}, r^A, r_H)` of the tuple and the variation `(k, X, η)`:
  `-(1/2κ)√(-det g)⟨(𝓔^{tr})^{tr♯}, k⟩ + ⟨√(-det g) g^{δβ}r^A_β, X_δ⟩ + 2√(-det g)⟨r_H, η⟩`;
* **`exists_hom_bound`** — a function continuous on `K × B × W` (`K` compact, `B`, `W`
  finite-dimensional) and homogeneous in each of the last two arguments is bounded by
  `M‖b‖‖w‖`.
-/

namespace RenewalGeometry

namespace GenCellBulk

open HarmonicDefect EHJetVariation EHFieldVariation ActualJetSystem ActualJetRecon
  ActualJetSmooth ActualJetGauge SlabWaveHk ActualJetWriter ActualJetBridge ActualJetState
  GenMatVar GenNoether PeriodicCube GenFOGrav GenMatEuler GenFOAction GenCell KatoGalerkin
  SymHypEnergy GenCellVar GenResMaps ActualJetCompleteForcing
open SobolevOpen (pd)
open MeasureTheory Set
open scoped ContDiff

noncomputable section

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024

/-! ### Trace reversal -/

section TraceRev

theorem inv_contract {g : Met} (hdet : (Matrix.of g).det ≠ 0) (a c : Fin 4) :
    ∑ b, g a b * ginvOf g b c = if a = c then 1 else 0 := by
  have h := Matrix.mul_nonsing_inv (Matrix.of g) (isUnit_iff_ne_zero.mpr hdet)
  have := congrFun (congrFun h a) c
  rw [Matrix.mul_apply, Matrix.one_apply] at this
  simpa [ginvOf] using this

theorem trG_metric_four {g : Met} (hdet : (Matrix.of g).det ≠ 0)
    (hsym : ∀ μ ν, g μ ν = g ν μ) : ∑ μ, ∑ ν, ginvOf g μ ν * g μ ν = 4 := by
  have e : ∀ μ, ∑ ν, ginvOf g μ ν * g μ ν = if μ = μ then 1 else 0 := fun μ => by
    rw [← inv_contract hdet μ μ]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [ginvOf_symm' hsym μ ν]; ring
  simp only [e, if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  norm_num

/-- **Trace reversal is an involution in dimension four.** -/
theorem traceRev_invol {g : Met} (hdet : (Matrix.of g).det ≠ 0) (hsym : ∀ μ ν, g μ ν = g ν μ)
    (X : Met) (a b : Fin 4) :
    traceRev g (ginvOf g) (traceRev g (ginvOf g) X) a b = X a b := by
  set T := trG (ginvOf g) X with hT
  have htr : trG (ginvOf g) (traceRev g (ginvOf g) X) = -T := by
    show ∑ μ, ∑ ν, ginvOf g μ ν * (X μ ν - 1 / 2 * g μ ν * T) = -T
    have e : ∀ μ ν, ginvOf g μ ν * (X μ ν - 1 / 2 * g μ ν * T) =
        ginvOf g μ ν * X μ ν - (1 / 2 * T) * (ginvOf g μ ν * g μ ν) := fun μ ν => by ring
    simp only [e, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [trG_metric_four hdet hsym]
    have : ∑ μ, ∑ ν, ginvOf g μ ν * X μ ν = T := rfl
    rw [this]; ring
  show traceRev g (ginvOf g) X a b - 1 / 2 * g a b * trG (ginvOf g) (traceRev g (ginvOf g) X) =
    X a b
  rw [htr]
  show X a b - 1 / 2 * g a b * T - 1 / 2 * g a b * -T = X a b
  ring

theorem sum_up_comb (gi X Y Z W k : Met) (c₁ c₂ : ℝ) :
    ∑ μ, ∑ ν, up gi (fun a b => X a b + c₁ * Y a b - c₂ * (Z a b + W a b)) μ ν * k μ ν =
      ∑ μ, ∑ ν, up gi X μ ν * k μ ν + c₁ * ∑ μ, ∑ ν, up gi Y μ ν * k μ ν -
        c₂ * (∑ μ, ∑ ν, up gi Z μ ν * k μ ν + ∑ μ, ∑ ν, up gi W μ ν * k μ ν) := by
  have hup : ∀ μ ν, up gi (fun a b => X a b + c₁ * Y a b - c₂ * (Z a b + W a b)) μ ν =
      up gi X μ ν + c₁ * up gi Y μ ν - c₂ * (up gi Z μ ν + up gi W μ ν) := fun μ ν => by
    have e : ∀ a b, gi μ a * gi ν b * (X a b + c₁ * Y a b - c₂ * (Z a b + W a b)) =
        gi μ a * gi ν b * X a b + c₁ * (gi μ a * gi ν b * Y a b) -
          c₂ * (gi μ a * gi ν b * Z a b + gi μ a * gi ν b * W a b) := fun a b => by ring
    simp only [up, e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have e2 : ∀ μ ν, (up gi X μ ν + c₁ * up gi Y μ ν - c₂ * (up gi Z μ ν + up gi W μ ν)) * k μ ν =
      up gi X μ ν * k μ ν + c₁ * (up gi Y μ ν * k μ ν) -
        c₂ * (up gi Z μ ν * k μ ν + up gi W μ ν * k μ ν) := fun μ ν => by ring
  simp only [hup, e2, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]

end TraceRev

/-! ### The bulk rows -/

section Bulk

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']

/-- **The bulk rows as a bilinear expression in the bosonic residual** `b = (𝓔^{tr}, r^A, r_H)`
and the variation `(k, X, η)`. -/
def bulkJ (SM : SMData (MatLie m) V S S') (g : Met) (b : BosP m V) (k : Met)
    (X : Fin 4 → MatLie m) (η : V) : ℝ :=
  -(1 / (2 * SM.κ)) * (volM g * ∑ μ, ∑ ν, up (ginvOf g) (traceRev g (ginvOf g) b.1) μ ν * k μ ν) +
    ∑ δ, SM.ipG (volM g • ∑ β, ginvOf g δ β • b.2.1 β) (X δ) + 2 * volM g * SM.ipV b.2.2 η

theorem coord_zero (SM : SMData (MatLie m) V S S') (hV : GenStress.VariationalStress SM)
    (g : Met) (ε : Fin 4 → ℝ) (e : Met) (H : V) (ψ : S) (X : Fin 4 → S) (ψb : S')
    (Xb : Fin 4 → S') (μ ν : Fin 4) : SM.TD.coord g ε e H ψ X ψb Xb μ ν = 0 := by
  unfold DiracStressForm.coord DiracStressForm.frame
  simp [hV.P_zero, hV.P'_zero, hV.P''_zero]

set_option maxHeartbeats 1000000 in
/-- **The bulk rows are the bosonic residual paired with the variation** (variational data,
`κ ≠ 0`). -/
theorem bulkT_eq (SM : SMData (MatLie m) V S S') (hV : GenStress.VariationalStress SM)
    (hκ : SM.κ ≠ 0) (z : Tuple m V S S') (k : ST 3 → Met) (X : ST 3 → Fin 4 → MatLie m)
    (η : ST 3 → V) (x : ST 3) :
    bulkT SM z k X η x = bulkJ SM (z.g x) (bosF SM z x) (k x) (X x) (η x) := by
  have hdet : (Matrix.of (z.g x)).det ≠ 0 := (GenCell.Tuple_det_neg z x).ne
  have hsym : ∀ μ ν, z.g x μ ν = z.g x ν μ := z.g_symm x
  set Tym : Met := ymStressB SM.ipG (z.g x) (ginvOf (z.g x)) (Fm (z.A x) (fun γ μ => pd z.A γ x μ))
    with hTym
  set TH : Met := higgsStressB SM.ipV SM.lamH SM.vH (z.g x) (ginvOf (z.g x)) (z.H x)
    (ActualJetGauge.DH (z.A x) (z.H x) (fun γ => pd z.H γ x)) with hTH
  set Ein : Met := einstein (z.g x) (ginvOf (z.g x)) (dF z.g x) (ddF z.g x) with hEin
  have hE : traceRev (z.g x) (ginvOf (z.g x)) (bosF SM z x).1 =
      fun a b => Ein a b + SM.Λ * z.g x a b - SM.κ * (Tym a b + TH a b) := by
    funext a b
    rw [← bosR_hj2 z x SM]
    show traceRev (z.g x) (ginvOf (z.g x)) (traceRev (z.g x) (ginvOf (z.g x))
      (fun a b => einstein (z.g x) (ginvOf (z.g x)) (dF z.g x) (ddF z.g x) a b +
        SM.Λ * z.g x a b - SM.κ * TactR SM (z.g x) (fun α => pd z.g α x) (z.A x)
          (fun γ => pd z.A γ x) (z.H x) (fun γ => pd z.H γ x) (z.ψ x) (fun γ => pd z.ψ γ x)
          (z.ψb x) (fun γ => pd z.ψb γ x) a b)) a b = _
    rw [traceRev_invol hdet hsym]
    simp only [TactR, coord_zero SM hV, add_zero]
    rfl
  have hsum := sum_up_comb (ginvOf (z.g x)) Ein (z.g x) Tym TH (k x) SM.Λ SM.κ
  have hmet := up_metric_contract hdet hsym (k x)
  have hEU : ∑ μ, ∑ ν, up (ginvOf (z.g x)) Ein μ ν * k x μ ν =
      ∑ μ, ∑ ν, einsteinUp (z.g x) (ginvOf (z.g x)) (dF z.g x) (ddF z.g x) μ ν * k x μ ν := rfl
  have hrho : rho z x = volM (z.g x) := (volM_eq_rho z x).symm
  unfold bulkT bulkJ einRow
  rw [hE, hsum, hmet, ← hEU]
  simp only [densR, hrho]
  have hgi : z.gi x = ginvOf (z.g x) := rfl
  rw [hgi]
  field_simp
  ring

end Bulk

/-! ### Homogeneous bounds on compact sets -/

section HomBound

/-- **A jointly continuous function, homogeneous in its last two arguments, is bounded by
`M‖b‖‖w‖` over a compact set of base points.** -/
theorem exists_hom_bound {G B W : Type*} [TopologicalSpace G] [NormedAddCommGroup B]
    [NormedSpace ℝ B] [FiniteDimensional ℝ B] [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W] (Φ : G → B → W → ℝ) {K : Set G} (hK : IsCompact K)
    (hc : ContinuousOn (fun p : G × B × W => Φ p.1 p.2.1 p.2.2) (K ×ˢ univ))
    (h1 : ∀ g ∈ K, ∀ (c : ℝ) b w, Φ g (c • b) w = c * Φ g b w)
    (h2 : ∀ g ∈ K, ∀ (c : ℝ) b w, Φ g b (c • w) = c * Φ g b w) :
    ∃ M ≥ 0, ∀ g ∈ K, ∀ b w, |Φ g b w| ≤ M * ‖b‖ * ‖w‖ := by
  set C : Set (G × B × W) := K ×ˢ (Metric.closedBall (0 : B) 1 ×ˢ Metric.closedBall (0 : W) 1)
    with hC
  have hCc : IsCompact C := hK.prod ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))
  have hCsub : C ⊆ K ×ˢ univ := fun p hp => ⟨hp.1, trivial⟩
  obtain ⟨M, hM⟩ := hCc.exists_bound_of_continuousOn (hc.mono hCsub)
  refine ⟨max M 0, le_max_right _ _, fun g hg b w => ?_⟩
  by_cases hb : b = 0
  · have : Φ g b w = 0 := by
      have := h1 g hg 0 b w
      rw [zero_smul, zero_mul] at this
      rw [hb]; exact this
    rw [this, abs_zero]; positivity
  by_cases hw : w = 0
  · have : Φ g b w = 0 := by
      have := h2 g hg 0 b w
      rw [zero_smul, zero_mul] at this
      rw [hw]; exact this
    rw [this, abs_zero]; positivity
  have hnb : 0 < ‖b‖ := norm_pos_iff.2 hb
  have hnw : 0 < ‖w‖ := norm_pos_iff.2 hw
  set b' := ‖b‖⁻¹ • b with hb'def
  set w' := ‖w‖⁻¹ • w with hw'def
  have hb' : b = ‖b‖ • b' := by rw [hb'def, smul_smul, mul_inv_cancel₀ hnb.ne', one_smul]
  have hw' : w = ‖w‖ • w' := by rw [hw'def, smul_smul, mul_inv_cancel₀ hnw.ne', one_smul]
  have hmem : (g, b', w') ∈ C := by
    refine ⟨hg, ?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right, hb'def, norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ hnb.ne']
    · rw [Metric.mem_closedBall, dist_zero_right, hw'def, norm_smul, norm_inv, norm_norm,
        inv_mul_cancel₀ hnw.ne']
  have hbd := hM _ hmem
  rw [Real.norm_eq_abs] at hbd
  have e : Φ g b w = ‖b‖ * ‖w‖ * Φ g b' w' := by
    conv_lhs => rw [hb', hw']
    rw [h1 g hg, h2 g hg]
    ring
  rw [e, abs_mul, abs_mul, abs_of_pos hnb, abs_of_pos hnw]
  have := le_max_left M 0
  calc ‖b‖ * ‖w‖ * |Φ g b' w'| ≤ ‖b‖ * ‖w‖ * max M 0 :=
        mul_le_mul_of_nonneg_left (hbd.trans this) (by positivity)
    _ = max M 0 * ‖b‖ * ‖w‖ := by ring

end HomBound

/-! ### Homogeneity and continuity of the bulk expression -/

section BulkReg

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']

theorem trG_smul (gi X : Met) (t : ℝ) : trG gi (t • X) = t * trG gi X := by
  unfold trG
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => by ring

theorem traceRev_smul (g gi X : Met) (t : ℝ) :
    traceRev g gi (t • X) = t • traceRev g gi X := by
  funext μ ν
  simp only [traceRev, trG_smul, Pi.smul_apply, smul_eq_mul]
  ring

theorem sum_up_smul (gi X k : Met) (t : ℝ) :
    ∑ μ, ∑ ν, up gi (t • X) μ ν * k μ ν = t * ∑ μ, ∑ ν, up gi X μ ν * k μ ν := by
  simp only [up, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ =>
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem sum_up_smul_right (gi X k : Met) (t : ℝ) :
    ∑ μ, ∑ ν, up gi X μ ν * (t • k) μ ν = t * ∑ μ, ∑ ν, up gi X μ ν * k μ ν := by
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => by ring

theorem bulkJ_smul_left (SM : SMData (MatLie m) V S S') (g : Met) (t : ℝ) (b : BosP m V)
    (k : Met) (X : Fin 4 → MatLie m) (η : V) :
    bulkJ SM g (t • b) k X η = t * bulkJ SM g b k X η := by
  unfold bulkJ
  have e1 : (t • b).1 = t • b.1 := rfl
  have e2 : ∀ β, (t • b).2.1 β = t • b.2.1 β := fun β => rfl
  have e3 : (t • b).2.2 = t • b.2.2 := rfl
  have e4 : ∀ δ, volM g • ∑ β, ginvOf g δ β • (t • b.2.1 β) =
      t • (volM g • ∑ β, ginvOf g δ β • b.2.1 β) := fun δ => by
    simp only [Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun β _ => ?_
    congr 1; ring
  simp only [e1, e2, e3, e4, traceRev_smul, sum_up_smul, map_smul, LinearMap.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  ring_nf
  simp only [Finset.mul_sum, Finset.sum_mul]
  ring_nf

theorem bulkJ_smul_right (SM : SMData (MatLie m) V S S') (g : Met) (b : BosP m V) (t : ℝ)
    (k : Met) (X : Fin 4 → MatLie m) (η : V) :
    bulkJ SM g b (t • k) (t • X) (t • η) = t * bulkJ SM g b k X η := by
  unfold bulkJ
  simp only [sum_up_smul_right, Pi.smul_apply, map_smul, smul_eq_mul, Finset.mul_sum]
  ring_nf
  simp only [Finset.mul_sum, Finset.sum_mul]
  ring_nf

section CA

variable {E : Type*} [TopologicalSpace E] {x : E}

theorem ca_metricTerm {g gi B k : E → Met} (hg : ∀ a b, ContinuousAt (fun y => g y a b) x)
    (hgi : ∀ a b, ContinuousAt (fun y => gi y a b) x)
    (hB : ∀ a b, ContinuousAt (fun y => B y a b) x)
    (hk : ∀ a b, ContinuousAt (fun y => k y a b) x) :
    ContinuousAt (fun y => ∑ μ, ∑ ν, up (gi y) (traceRev (g y) (gi y) (B y)) μ ν * k y μ ν) x := by
  have htr : ContinuousAt (fun y => trG (gi y) (B y)) x := by unfold trG; fun_prop
  have hT : ∀ a b, ContinuousAt (fun y => traceRev (g y) (gi y) (B y) a b) x := fun a b => by
    unfold traceRev; fun_prop
  unfold up
  fun_prop

end CA

theorem continuous_volM : Continuous (fun g : Met => volM g) := by
  unfold volM
  exact Real.continuous_sqrt.comp
    (Continuous.matrix_det (A := fun g : Met => Matrix.of g) continuous_id).neg

/-- **Joint continuity of the bulk expression** where `det g ≠ 0`. -/
theorem continuousAt_bulkJ (SM : SMData (MatLie m) V S S')
    {p : Met × BosP m V × (Met × (Fin 4 → MatLie m) × V)} (hp : (Matrix.of p.1).det ≠ 0) :
    ContinuousAt (fun q : Met × BosP m V × (Met × (Fin 4 → MatLie m) × V) =>
      bulkJ SM q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2) p := by
  have hg : ContinuousAt (fun q : Met × BosP m V × (Met × (Fin 4 → MatLie m) × V) => q.1) p :=
    continuousAt_fst
  have hv : ContinuousAt (fun q : Met × BosP m V × (Met × (Fin 4 → MatLie m) × V) =>
      volM q.1) p := (continuous_volM.comp continuous_fst).continuousAt
  have hgi0 : ContinuousAt (fun q : Met × BosP m V × (Met × (Fin 4 → MatLie m) × V) =>
      ginvOf q.1) p := (ContDiffAt.ginvOf_fun (n := ∞) contDiffAt_fst hp).continuousAt
  have hgi : ∀ a b, ContinuousAt (fun q : Met × BosP m V × (Met × (Fin 4 → MatLie m) × V) =>
      ginvOf q.1 a b) p := fun a b =>
    (continuous_apply b).continuousAt.comp ((continuous_apply a).continuousAt.comp hgi0)
  have hgab : ∀ a b, ContinuousAt (fun q : Met × BosP m V × (Met × (Fin 4 → MatLie m) × V) =>
      q.1 a b) p := fun a b => by fun_prop
  have hB : ∀ a b, ContinuousAt (fun q : Met × BosP m V × (Met × (Fin 4 → MatLie m) × V) =>
      q.2.1.1 a b) p := fun a b => by fun_prop
  have hk : ∀ a b, ContinuousAt (fun q : Met × BosP m V × (Met × (Fin 4 → MatLie m) × V) =>
      q.2.2.1 a b) p := fun a b => by fun_prop
  have h1 := ca_metricTerm hgab hgi hB hk
  have hu : ∀ δ, ContinuousAt (fun q : Met × BosP m V × (Met × (Fin 4 → MatLie m) × V) =>
      volM q.1 • ∑ β, ginvOf q.1 δ β • q.2.1.2.1 β) p := fun δ => by
    have hr : ∀ β, ContinuousAt (fun q : Met × BosP m V × (Met × (Fin 4 → MatLie m) × V) =>
        q.2.1.2.1 β) p := fun β => by fun_prop
    have hs : ∀ β, ContinuousAt (fun q : Met × BosP m V × (Met × (Fin 4 → MatLie m) × V) =>
        ginvOf q.1 δ β • q.2.1.2.1 β) p := fun β => (hgi δ β).smul (hr β)
    exact hv.smul (by fun_prop)
  have hX : ∀ δ, ContinuousAt (fun q : Met × BosP m V × (Met × (Fin 4 → MatLie m) × V) =>
      q.2.2.2.1 δ) p := fun δ => by fun_prop
  have h2 : ∀ δ, ContinuousAt (fun q : Met × BosP m V × (Met × (Fin 4 → MatLie m) × V) =>
      SM.ipG (volM q.1 • ∑ β, ginvOf q.1 δ β • q.2.1.2.1 β) (q.2.2.2.1 δ)) p := fun δ =>
    ((bilinCLM SM.ipG).continuous.continuousAt.comp (hu δ)).clm_apply (hX δ)
  have h3 : ContinuousAt (fun q : Met × BosP m V × (Met × (Fin 4 → MatLie m) × V) =>
      SM.ipV q.2.1.2.2 q.2.2.2.2) p := by
    have ha : ContinuousAt (fun q : Met × BosP m V × (Met × (Fin 4 → MatLie m) × V) =>
        q.2.1.2.2) p := by fun_prop
    have hb : ContinuousAt (fun q : Met × BosP m V × (Met × (Fin 4 → MatLie m) × V) =>
        q.2.2.2.2) p := by fun_prop
    exact ((bilinCLM SM.ipV).continuous.continuousAt.comp ha).clm_apply hb
  unfold bulkJ
  have h2' : ContinuousAt (fun q : Met × BosP m V × (Met × (Fin 4 → MatLie m) × V) =>
      ∑ δ, SM.ipG (volM q.1 • ∑ β, ginvOf q.1 δ β • q.2.1.2.1 β) (q.2.2.2.1 δ)) p := by
    fun_prop
  exact ((continuousAt_const.mul (hv.mul h1)).add h2').add ((continuousAt_const.mul hv).mul h3)

end BulkReg

end

end GenCellBulk

end RenewalGeometry
