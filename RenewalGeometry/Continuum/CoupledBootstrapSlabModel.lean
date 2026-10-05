/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.CoupledBootstrapRecovery
import RenewalGeometry.Continuum.SlabSobolevSeminorms
import RenewalGeometry.Continuum.AposterioriPhysicalShadow

/-!
# `prop:coupled-bootstrap` in norm form, discharging `CoupledBootstrapConclusion`

Einstein–Standard-Model action-closure manuscript, `prop:coupled-bootstrap`
(`eq:bootstrap-state`, `eq:bootstrap-curvature`).

The concrete slab model `slabModel` (an `AposterioriShadow.SlabModel`) of smooth actual field
tuples `z = (g, A, H, ψ, ψ̄)` on `ℝ × 𝕋³` (unit period; temporal internal gauge; Lorentzian chart
everywhere):
* `init z = 𝒰(z)(0)` in the initial `H^k` space, a real normed space (separation quotient of the
  smooth periodic families with the `H^k` seminorm, in the coordinates `eX` of the state space);
* `obs z = (𝒰(z), Riem(g), T^{SM}(z))` in `C_tH^k_x × L²_tH^{k-1}_x × L²_tH^k_x` on `[0, T]`;
* `resB = ‖R_B‖_{L²_tH^k_x}`, `resD = ‖R_D‖_{L²_tH^{k+1}_x}`,
  `harm = ‖C(g)‖_{L²_tH^{k+1}_x} + ‖∂_tC(g)‖_{L²_tH^k_x}`;
* `IsExact = ExactOn` (all physical, Dirac and harmonic-gauge rows vanish on the slab).

`coupled_bootstrap` proves `AposterioriShadow.CoupledBootstrapConclusion` for this model with
`d_* = √δ_*`, `C_* = 3√C_*'` from the squared-form `coupled_bootstrap_sq`, for the reference class
of exact smooth solutions with values in a compact chart margin `K` and `C_tH^{k+1}` bound `R₁`.
`coupled_bootstrap_orth` replaces the symmetry hypothesis by orthonormality of `eX` for the block
inner product and the Clifford (anti)self-adjointness conditions (`Aco_symm`).
-/

open MeasureTheory Filter Topology Set Metric
open scoped BigOperators ContDiff

noncomputable section

namespace RenewalGeometry.CoupledBootstrap

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk SlabSobAlg QLEnergy QLDiff QLRecovery FrameCurvature
  HarmonicDefect ActualJetWriter ActualJetFrame ActualJetSystem ActualJetSmooth ActualJetGauge
  ActualJetBridge ActualJetCompleteForcing ActualJetState ActualJetRecon SpinorProlongation
  TwistedHalfRicci SlabSemi AposterioriShadow

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024

section Model

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable (SM : SMData (MatLie m) V S S')
variable {n : ℕ} (eX : (Fin n → ℝ) ≃L[ℝ] StateP m V S S')
variable {na nb : ℕ} (eY : (Fin na → ℝ) ≃L[ℝ] BosP m V) (eYD : (Fin nb → ℝ) ≃L[ℝ] S × S')

/-- The state field `𝒰(z) = eX⁻¹(state)` as a smooth periodic family. -/
def stateGrp (z : Tuple m V S S') : SmoothPer 3 (Fin n) :=
  ⟨uC SM eX z, fun a => ⟨contDiff_uC SM eX z a, isSPeriodic_uC SM eX z a⟩⟩

/-- The Riemann tensor field as a smooth periodic family. -/
def riemGrp (z : Tuple m V S S') : SmoothPer 3 RIdx :=
  ⟨fun c x => RiemF z x c, fun c => ⟨contDiff_RiemF z c, isSPeriodic_RiemF z c⟩⟩

/-- The complete off-shell stress `T^{SM}` as a smooth periodic family. -/
def stressGrp (hS : SMSmooth SM) (z : Tuple m V S S') : SmoothPer 3 (Fin 4 × Fin 4) :=
  ⟨fun p x => TactF SM z x p.1 p.2,
    fun p => ⟨contDiff_TactF SM eX eYD z hS p.1 p.2, isSPeriodic_TactF SM z p.1 p.2⟩⟩

/-- The observable seminorm `‖·‖_{C_tH^k} + ‖·‖_{L²_tH^{k-1}} + ‖·‖_{L²_tH^k}`. -/
def obsSemi (k : ℕ) (T : ℝ) (hT : 0 ≤ T) :
    AddGroupSeminorm (SmoothPer 3 (Fin n) × SmoothPer 3 RIdx × SmoothPer 3 (Fin 4 × Fin 4)) :=
  (supSemi k T hT).comp (AddMonoidHom.fst _ _) +
    (l2Semi (k - 1) T hT).comp ((AddMonoidHom.fst _ _).comp (AddMonoidHom.snd _ _)) +
    (l2Semi k T hT).comp ((AddMonoidHom.snd _ _).comp (AddMonoidHom.snd _ _))

/-- The squared `L²_tH^j_x` norm of a family of fields. -/
def l2Sq {ι : Type*} [Fintype ι] (j : ℕ) (T : ℝ) (F : ι → ST 3 → ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..T, ∑ i, Q j (F i) t

theorem intervalIntegrable_sumQ {ι : Type*} [Fintype ι] (j : ℕ) (T : ℝ) {F : ι → ST 3 → ℝ}
    (hF : ∀ i, ContDiff ℝ ∞ (F i)) :
    IntervalIntegrable (fun t => ∑ i, Q j (F i) t) volume 0 T :=
  (continuous_finsetSum _ fun i _ => continuous_Q j (hF i)).intervalIntegrable _ _

/-- A family of smooth fields vanishing on the slab `[0, T] × ℝ³` has vanishing `L²_tH^j_x`
norm. -/
theorem l2Sq_eq_zero_of_slab {ι : Type*} [Fintype ι] (j : ℕ) {T : ℝ} (hT : 0 ≤ T)
    {F : ι → ST 3 → ℝ} (hF : ∀ i, ContDiff ℝ ∞ (F i))
    (h0 : ∀ i (x : ST 3), x 0 ∈ Icc 0 T → F i x = 0) : l2Sq j T F = 0 := by
  unfold l2Sq
  rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)), intervalIntegral.integral_zero]
  intro t ht
  rw [uIcc_of_le hT] at ht
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [SliceForcing.Q_congr_slice (hF i) (contDiff_const (c := (0 : ℝ))) t
    (fun y => h0 i _ (by simpa using ht)) j]
  simpa using Q_const (d := 3) j 0 t

theorem l2Sq_nonneg {ι : Type*} [Fintype ι] (j : ℕ) {T : ℝ} (hT : 0 ≤ T) (F : ι → ST 3 → ℝ) :
    0 ≤ l2Sq j T F :=
  intervalIntegral.integral_nonneg hT fun t _ => Finset.sum_nonneg fun i _ => Q_nonneg _ _ _

/-- **The concrete slab model of `prop:coupled-bootstrap`** (see the module docstring). -/
def slabModel (hS : SMSmooth SM) (k : ℕ) (T : ℝ) (hT : 0 < T) :
    SlabModel (Tuple m V S S')
      (SeparationQuotient (NSpace (hkSeminorm (d := 3) (ι := Fin n) k 0)))
      (SemiSpace (obsSemi (n := n) k T hT.le)) where
  init z := SeparationQuotient.mk (NSpace.of _ (stateGrp SM eX z))
  obs z := SemiSpace.of _ (stateGrp SM eX z, riemGrp z, stressGrp SM eX eYD hS z)
  resB z := Real.sqrt (l2Sq k T (RBc SM eY z))
  resD z := Real.sqrt (l2Sq (k + 1) T (RDc SM eYD z))
  harm z := Real.sqrt (l2Sq (k + 1) T (Cc z)) + Real.sqrt (l2Sq k T (dtCc z))
  Admissible _ := True
  IsExact z := ExactOn SM T z
  resB_nonneg _ := Real.sqrt_nonneg _
  resD_nonneg _ := Real.sqrt_nonneg _
  harm_nonneg _ := add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  exact_resB z hz := by
    rw [l2Sq_eq_zero_of_slab k hT.le (contDiff_RBc SM eY z hS) fun i x hx => by
      simp [RBc, (hz x hx).1], Real.sqrt_zero]
  exact_resD z hz := by
    rw [l2Sq_eq_zero_of_slab (k + 1) hT.le (contDiff_RDc SM eYD z) fun i x hx => by
      simp [RDc, (hz x hx).2.1], Real.sqrt_zero]
  exact_harm z hz := by
    rw [l2Sq_eq_zero_of_slab (k + 1) hT.le (contDiff_Cc z) fun l x hx => by
      simp [Cc, (hz x hx).2.2], l2Sq_eq_zero_of_slab k hT.le (contDiff_dtCc z) fun l x hx => by
      simp [dtCc, pd_eq_zero_of_slab (contDiff_CF z) (fun y hy => (hz y hy).2.2) hx 0
        (Or.inr hT)], Real.sqrt_zero, add_zero]

/-- The initial `H^k` distance of the model is the `H^k` norm of the state difference at `t = 0`. -/
theorem norm_init_sub (hS : SMSmooth SM) (k : ℕ) {T : ℝ} (hT : 0 < T) (zh zs : Tuple m V S S') :
    ‖(slabModel SM eX eY eYD hS k T hT).init zh - (slabModel SM eX eY eYD hS k T hT).init zs‖ =
      Real.sqrt (energyQ k (subF (uC SM eX zh) (uC SM eX zs)) 0) := by
  show ‖SeparationQuotient.mk _ - SeparationQuotient.mk _‖ = _
  rw [← SeparationQuotient.mk_sub, SeparationQuotient.norm_mk, ← NSpace.of_sub,
    NSpace.norm_of]
  rfl

/-- `∫₀ᵀ forcingSq` splits into the four squared residual norms. -/
theorem integral_forcingSq (hS : SMSmooth SM) (k : ℕ) (T : ℝ) (z : Tuple m V S S') :
    ∫ t in (0 : ℝ)..T, forcingSq SM eY eYD k z t =
      l2Sq k T (RBc SM eY z) + l2Sq (k + 1) T (RDc SM eYD z) + l2Sq (k + 1) T (Cc z) +
        l2Sq k T (dtCc z) := by
  unfold forcingSq l2Sq
  rw [intervalIntegral.integral_add, intervalIntegral.integral_add, intervalIntegral.integral_add]
  · exact intervalIntegrable_sumQ _ _ (contDiff_RBc SM eY z hS)
  · exact intervalIntegrable_sumQ _ _ (contDiff_RDc SM eYD z)
  · exact (intervalIntegrable_sumQ _ _ (contDiff_RBc SM eY z hS)).add
      (intervalIntegrable_sumQ _ _ (contDiff_RDc SM eYD z))
  · exact intervalIntegrable_sumQ _ _ (contDiff_Cc z)
  · exact ((intervalIntegrable_sumQ _ _ (contDiff_RBc SM eY z hS)).add
      (intervalIntegrable_sumQ _ _ (contDiff_RDc SM eYD z))).add
        (intervalIntegrable_sumQ _ _ (contDiff_Cc z))
  · exact intervalIntegrable_sumQ _ _ (contDiff_dtCc z)

/-- **The squared mismatch is dominated by the square of the paper's mismatch `d`**. -/
theorem misSq_le_sq (hS : SMSmooth SM) (k : ℕ) {T : ℝ} (hT : 0 < T) (zh zs : Tuple m V S S') :
    misSq SM eX eY eYD k T zh zs ≤ ((slabModel SM eX eY eYD hS k T hT).mismatch zh zs) ^ 2 := by
  unfold SlabModel.mismatch
  rw [norm_init_sub SM eX eY eYD hS k hT]
  unfold misSq
  rw [integral_forcingSq SM eY eYD hS k T zh]
  show _ ≤ (Real.sqrt _ + Real.sqrt (l2Sq k T (RBc SM eY zh)) +
    Real.sqrt (l2Sq (k + 1) T (RDc SM eYD zh)) +
    (Real.sqrt (l2Sq (k + 1) T (Cc zh)) + Real.sqrt (l2Sq k T (dtCc zh)))) ^ 2
  have e0 := Real.sq_sqrt (energyQ_nonneg k (subF (uC SM eX zh) (uC SM eX zs)) 0)
  have e1 := Real.sq_sqrt (l2Sq_nonneg k hT.le (RBc SM eY zh))
  have e2 := Real.sq_sqrt (l2Sq_nonneg (k + 1) hT.le (RDc SM eYD zh))
  have e3 := Real.sq_sqrt (l2Sq_nonneg (k + 1) hT.le (Cc zh))
  have e4 := Real.sq_sqrt (l2Sq_nonneg k hT.le (dtCc zh))
  set a0 := Real.sqrt (energyQ k (subF (uC SM eX zh) (uC SM eX zs)) 0)
  set a1 := Real.sqrt (l2Sq k T (RBc SM eY zh))
  set a2 := Real.sqrt (l2Sq (k + 1) T (RDc SM eYD zh))
  set a3 := Real.sqrt (l2Sq (k + 1) T (Cc zh))
  set a4 := Real.sqrt (l2Sq k T (dtCc zh))
  have h0 : 0 ≤ a0 := Real.sqrt_nonneg _
  have h1 : 0 ≤ a1 := Real.sqrt_nonneg _
  have h2 : 0 ≤ a2 := Real.sqrt_nonneg _
  have h3 : 0 ≤ a3 := Real.sqrt_nonneg _
  have h4 : 0 ≤ a4 := Real.sqrt_nonneg _
  rw [← e0, ← e1, ← e2, ← e3, ← e4]
  nlinarith [mul_nonneg h0 h1, mul_nonneg h0 h2, mul_nonneg h0 h3, mul_nonneg h0 h4,
    mul_nonneg h1 h2, mul_nonneg h1 h3, mul_nonneg h1 h4, mul_nonneg h2 h3, mul_nonneg h2 h4,
    mul_nonneg h3 h4]

/-- The reference class of `prop:coupled-bootstrap`: exact smooth solutions on the slab whose state
stays in the compact chart margin `K` and whose `C_tH^{k+1}` norm is at most `R₁`. -/
def refSet (k : ℕ) (T : ℝ) (K : Set (Fin n → ℝ)) (R₁ : ℝ) : Set (Tuple m V S S') :=
  {zs | ExactOn SM T zs ∧ (∀ x : ST 3, x 0 ∈ Icc 0 T → (fun b => uC SM eX zs b x) ∈ K) ∧
    ∀ t ∈ Icc 0 T, energyQ (k + 1) (uC SM eX zs) t ≤ R₁ ^ 2}

/-- **`prop:coupled-bootstrap`** (`eq:bootstrap-state`, `eq:bootstrap-curvature`), discharging
`AposterioriShadow.CoupledBootstrapConclusion` for the concrete slab model: if the principal
matrices are symmetric in the coordinates `eX`, `k ≥ 4`, `T > 0`, `K` is a compact subset of the
chart and `R₁ ≥ 0`, there are `d_* > 0`, `C_* ≥ 0` such that for every exact reference
`z_* ∈ refSet` and every smooth actual tuple `ẑ` with `d ≤ d_*`,
`‖𝒰̂ - 𝒰_*‖_{C_tH^k} + ‖Riem(ĝ) - Riem(g_*)‖_{L²H^{k-1}} + ‖T^{SM}(ẑ) - T^{SM}(z_*)‖_{L²H^k}
≤ C_* d`. -/
theorem coupled_bootstrap (hS : SMSmooth SM)
    (hAsym : ∀ j a b v, Aco SM eX j a b v = Aco SM eX j b a v)
    {k : ℕ} (hk : 4 ≤ k) {T : ℝ} (hT : 0 < T) {K : Set (Fin n → ℝ)} (hK : IsCompact K)
    (hKO : K ⊆ chartC eX) {R₁ : ℝ} (hR₁ : 0 ≤ R₁) :
    ∃ dstar Cstar : ℝ, 0 < dstar ∧ 0 ≤ Cstar ∧
      CoupledBootstrapConclusion (slabModel SM eX eY eYD hS k T hT)
        (refSet SM eX k T K R₁) dstar Cstar := by
  obtain ⟨δs, Cs, hδ, hCs, H⟩ := coupled_bootstrap_sq SM eX eY eYD hS hAsym hk hT hK hKO hR₁
  refine ⟨Real.sqrt δs, 3 * Real.sqrt Cs, Real.sqrt_pos.2 hδ, by positivity, ?_⟩
  rintro zs ⟨hex, hKs, hRs⟩ zh - hmis
  set M := slabModel SM eX eY eYD hS k T hT
  have hD := misSq_le_sq SM eX eY eYD hS k hT zh zs
  have hm0 : 0 ≤ M.mismatch zh zs :=
    add_nonneg (add_nonneg (add_nonneg (norm_nonneg _) (M.resB_nonneg _)) (M.resD_nonneg _))
      (M.harm_nonneg _)
  have hDδ : misSq SM eX eY eYD k T zh zs ≤ δs := by
    refine hD.trans ?_
    calc M.mismatch zh zs ^ 2 ≤ Real.sqrt δs ^ 2 := pow_le_pow_left₀ hm0 hmis 2
      _ = δs := Real.sq_sqrt hδ.le
  obtain ⟨h1, h2, h3⟩ := H zs zh hex hKs hRs hDδ
  have hsq : Real.sqrt (Cs * misSq SM eX eY eYD k T zh zs) ≤
      Real.sqrt Cs * M.mismatch zh zs := by
    rw [Real.sqrt_mul hCs]
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    calc Real.sqrt (misSq SM eX eY eYD k T zh zs) ≤ Real.sqrt (M.mismatch zh zs ^ 2) :=
          Real.sqrt_le_sqrt hD
      _ = M.mismatch zh zs := Real.sqrt_sq hm0
  have t1 : supSemi k T hT.le (stateGrp SM eX zh - stateGrp SM eX zs) ≤
      Real.sqrt (Cs * misSq SM eX eY eYD k T zh zs) :=
    supSemi_le k hT.le _ fun t ht => Real.sqrt_le_sqrt (h1 t ht)
  have t2 : l2Semi (k - 1) T hT.le (riemGrp zh - riemGrp zs) ≤
      Real.sqrt (Cs * misSq SM eX eY eYD k T zh zs) :=
    Real.sqrt_le_sqrt h2
  have t3 : l2Semi k T hT.le (stressGrp SM eX eYD hS zh - stressGrp SM eX eYD hS zs) ≤
      Real.sqrt (Cs * misSq SM eX eY eYD k T zh zs) :=
    Real.sqrt_le_sqrt h3
  have hdist : dist (M.obs zh) (M.obs zs) = obsSemi (n := n) k T hT.le
      ((stateGrp SM eX zh, riemGrp zh, stressGrp SM eX eYD hS zh) -
        (stateGrp SM eX zs, riemGrp zs, stressGrp SM eX eYD hS zs)) :=
    SemiSpace.dist_of _ _ _
  rw [hdist]
  show supSemi k T hT.le (stateGrp SM eX zh - stateGrp SM eX zs) +
    l2Semi (k - 1) T hT.le (riemGrp zh - riemGrp zs) +
    l2Semi k T hT.le (stressGrp SM eX eYD hS zh - stressGrp SM eX eYD hS zs) ≤ _
  linarith

/-- **`prop:coupled-bootstrap`** with the symmetry hypothesis discharged (`Aco_symm`): `eX` is
orthonormal for the positive block inner product `ipState bG bV bS bS'`, and the Clifford
generators are self-adjoint (`c₀`) and skew-adjoint (`cᵢ`) for the spinor forms. -/
theorem coupled_bootstrap_orth (hS : SMSmooth SM) (bG : MatLie m →ₗ[ℝ] MatLie m →ₗ[ℝ] ℝ)
    (bV : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (bS : S →ₗ[ℝ] S →ₗ[ℝ] ℝ) (bS' : S' →ₗ[ℝ] S' →ₗ[ℝ] ℝ)
    (hc0 : ∀ x y, bS (SM.D.Fr.c 0 • x) y = bS x (SM.D.Fr.c 0 • y))
    (hci : ∀ (i : Fin 3) x y, bS (SM.D.Fr.c i.succ • x) y = -bS x (SM.D.Fr.c i.succ • y))
    (hc0b : ∀ x y, bS' (SM.Db.Fr.c 0 • x) y = bS' x (SM.Db.Fr.c 0 • y))
    (hcib : ∀ (i : Fin 3) x y, bS' (SM.Db.Fr.c i.succ • x) y = -bS' x (SM.Db.Fr.c i.succ • y))
    (hX : ∀ v w, ipState bG bV bS bS' (ofP (eX v)) (ofP (eX w)) = ∑ i, v i * w i)
    {k : ℕ} (hk : 4 ≤ k) {T : ℝ} (hT : 0 < T) {K : Set (Fin n → ℝ)} (hK : IsCompact K)
    (hKO : K ⊆ chartC eX) {R₁ : ℝ} (hR₁ : 0 ≤ R₁) :
    ∃ dstar Cstar : ℝ, 0 < dstar ∧ 0 ≤ Cstar ∧
      CoupledBootstrapConclusion (slabModel SM eX eY eYD hS k T hT)
        (refSet SM eX k T K R₁) dstar Cstar :=
  coupled_bootstrap SM eX eY eYD hS
    (fun j a b v => Aco_symm SM eX bG bV bS bS' hc0 hci hc0b hcib hX j a b v) hk hT hK hKO hR₁

end Model

end RenewalGeometry.CoupledBootstrap
