/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.OpenWriterRateLiftCutMargin
import RenewalGeometry.Gravity.OpenWriterSubsidiaryRate
import RenewalGeometry.Gravity.OpenWriterLawEinsteinLimit

/-!
# Rate positivity, cut margin, noncollapse, curvature and subsidiary bounds along the writer
  histories, uniformly over the law family
  (clause (O3) of `thm:main-open-3plus1`; last sentence of `thm:supp-law-einstein`;
  the uniformity sentence of (L2) in `thm:main-open-law-basin`; emergent-spacetime manuscript)

**General jet tools** (for an arbitrary acceleration record `f`):
* `accJet q v f` — the space-time 2-jet field of `g_h = η + 𝓘_h q` with acceleration slot
  `𝓘_h f` (`interpJet q v = accJet q v (V_{0,h}(q, v))`); `accJet1` its 1-jet;
* `accJet_size`, `accJet1_size` — `‖accJet q v f‖_{H^{s-3}} ≤ S (2 + K) X` from
  `‖(q, v)‖_{X^s_h} ≤ X` and `‖f‖_{s-3,h} ≤ K X`;
* `accJet_diff`, `accJet1_diff` — the jet difference of two states is bounded by
  `‖(q - q', v - v')‖_{X^{s-2}_h} + ‖f - f'‖_{s-3,h}`;
* `accJet_det_ne` — small jets have nondegenerate interpolated metrics;
* `gauge_hasDerivWithinAt_acc` — along any solution of `q_t = v`, `v_t = Acc(q, v)`, the jet
  slots are actual derivatives and `dtGaugeOf (accJet …)` is the time derivative of `c(g_h)`;
* `riem_moser` — the Riemann tensor of a small jet field is bounded in `H^{r}` by its size
  (`riemOf 0 = 0`).

**Writer histories.**
* `writer_eq_of_small` — uniqueness on any interval `[0, T]` for writer solutions one of which
  stays in a fixed small `X^s_h` ball;
* `RateLiftAt g h` — the pointwise rate-lift package of `rateLift_chart` (inversion identities,
  interior cone `1/16 ≤ h² k_a^± ≤ 3/16`, `|c_a - 1/4| ≤ 5/56`, noncollapse `N², det γ, ϱ ∈ [1/2, 2]`,
  `ξᵀγξ ≥ |ξ|²/2`);
* `RateLiftMargin q` — `RateLiftAt (η + q(x)) h` at every grid point, the interior-cone
  `ConeData` of the rate-lift graph (`liftMass`, `liftRate`), and for odd `N` the spatial cut
  margin `I^sp ≥ 1/4096` and the full `RenewalSpatialPositiveScreen` package;
* `rateLift_grid` — small symmetric records satisfy `RateLiftMargin`.
-/

open Finset Filter Topology UnitAddTorus
open scoped BigOperators Real NNReal

namespace RenewalGeometry.OpenWriterRateLift

open TorusSobolevTransfer OpenWriterLifespan OpenWriterEnergyEstimate OpenWriterChart
  OpenWriterEnergy OpenWriterContinuum PeriodicGridSobolev.Composition OpenWriterGridBridge
  RootParityConnector HarmonicWriter OpenWriterLimitRegularity OpenWriterSubsidiary
  HarmonicGaugePropagation ContractedBianchiJet HarmonicDefect

noncomputable section

set_option linter.unusedSectionVars false

/-! ### Jets with an arbitrary acceleration slot -/

section Jets

variable {N : ℕ} [NeZero N]

/-- The space-time 2-jet field `(𝓘_h q, 𝓘_h v, 𝓘_h f, ∂ᵢ𝓘_h q, ∂ᵢ𝓘_h v, ∂ᵢ∂ⱼ𝓘_h q)` of
`g_h = η + 𝓘_h q` with the acceleration record `f` (symmetrised). -/
def accJet (q v f : Grid N → MetricRec) : C(T3, PJet) :=
  pjetField (interpRec q) (interpRec v) (interpRec (symRec f)) (interpD q) (interpD v) (interpDD q)

theorem interpJet_eq_accJet (q v : Grid N → MetricRec) :
    interpJet q v = accJet q v (harmonicWriterAcceleration q v) := rfl

/-- The 1-jet field `(𝓘_h q, 𝓘_h v, 0, ∂ᵢ𝓘_h q, 0, 0)`. -/
theorem accJet1_apply (q v f : Grid N → MetricRec) (y : T3) :
    interpJet1 q v y = trunc (accJet q v f y) := rfl

theorem sum16_le (f : (Σ _ : Fin 4, Fin 4) → ℝ) (B : ℝ) (h : ∀ k, f k ≤ B) :
    ∑ k, f k ≤ 16 * B := (sum_le_sum fun k _ => h k).trans (by simp)

theorem derQ (u : Grid N → MetricRec) (i : Fin 3) (k : Σ _ : Fin 4, Fin 4) (r' : ℕ) :
    MemH r' ⇑(ccoord bM (interpD u i) k) ∧
      sn r' ⇑(ccoord bM (interpD u i) k) ≤ sn (r' + 1) ⇑(ccoord bM (interpRec u) k) := by
  rw [ccoord_bM, ccoord_bM]
  exact memH_of_isLineDeriv (isLineDeriv_cmp (isLineDeriv_reField i _) k.1 k.2)
    (memH_cmp_reField _ _ _ _).1

theorem derQQ (u : Grid N → MetricRec) (i j : Fin 3) (k : Σ _ : Fin 4, Fin 4) (r' : ℕ) :
    MemH r' ⇑(ccoord bM (interpDD u i j) k) ∧
      sn r' ⇑(ccoord bM (interpDD u i j) k) ≤ sn (r' + 1) ⇑(ccoord bM (interpD u j) k) := by
  rw [ccoord_bM, ccoord_bM]
  exact memH_of_isLineDeriv (isLineDeriv_cmp (isLineDeriv_reField i _) k.1 k.2)
    (memH_cmp_reField _ _ _ _).1

/-- Membership of the jet field in `H^r`. -/
theorem accJet_memH (r : ℕ) (q v f : Grid N → MetricRec) :
    ∀ j, MemH r ⇑(ccoord bPJ (accJet q v f) j) :=
  memH_pjetField (fun k => (memH_interpRec r _ k).1) (fun k => (memH_interpRec r _ k).1)
    (fun k => (memH_interpRec r _ k).1) (fun i k => (derQ q i k r).1)
    (fun i k => (derQ v i k r).1) (fun i j k => (derQQ q i j k r).1)

theorem accJet1_memH (r : ℕ) (q v : Grid N → MetricRec) :
    ∀ j, MemH r ⇑(ccoord bPJ (interpJet1 q v) j) :=
  memH_pjetField (fun k => (memH_interpRec r _ k).1) (fun k => (memH_interpRec r _ k).1)
    (memH_ccoord_zero_rec r) (fun i k => (derQ q i k r).1)
    (fun i => memH_ccoord_zero_rec r) (fun i j => memH_ccoord_zero_rec r)

/-- The size constant `S_{s,K} = 16(√pc(r)(2 + K) + 6√pc(r+1) + 9√pc(r+2))`, `r = s - 3`. -/
def sizeConst (s : ℕ) (K : ℝ) : ℝ :=
  16 * (Real.sqrt (pc (s - 3)) * (2 + K) + 6 * Real.sqrt (pc (s - 3 + 1)) +
    9 * Real.sqrt (pc (s - 3 + 2)))

/-- The 1-jet size constant `16(2√pc(r) + 3√pc(r+1))`, `r = s - 2`. -/
def sizeConst1 (s : ℕ) : ℝ := 16 * (2 * Real.sqrt (pc (s - 2)) + 3 * Real.sqrt (pc (s - 2 + 1)))

/-- **Size of the jet field**: `‖accJet q v f‖_{H^{s-3}} ≤ S_{s,K} X` when
`‖(q, v)‖_{X^s_h} ≤ X` and every upper component of `f` has `‖f_κ‖_{s-3,h} ≤ K X`. -/
theorem accJet_size (s : ℕ) (hs : 5 ≤ s) {q v : Grid N → MetricRec} (hq : IsSymRec q)
    (hv : IsSymRec v) (f : Grid N → MetricRec) {X K : ℝ} (hK : 0 ≤ K) (hX : Xnorm s q v ≤ X)
    (hf : ∀ κ : Upper, PeriodicGridSobolev.sobNorm (s - 3) (cx (comp f κ.1.1 κ.1.2)) ≤ K * X) :
    ccoordSum (s - 3) bPJ (accJet q v f) ≤ sizeConst s K * X := by
  set r := s - 3 with hrdef
  have hX0 : 0 ≤ X := (Xnorm_nonneg _ _ _).trans hX
  unfold accJet
  rw [ccoordSum_pjetField]
  have b1 := ccoordSum_interpRec_le r s hq v (by omega)
  have b2 := ccoordSum_interpRec_v_le r s q hv (by omega)
  have b3 : ccoordSum r bM (interpRec (symRec f)) ≤ 16 * (Real.sqrt (pc r) * (K * X)) := by
    unfold ccoordSum
    refine sum16_le _ _ fun k => (memH_interpRec r _ k).2.trans
      (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _))
    rw [comp_symRec_eq]
    exact hf (upperOf k.1 k.2)
  have b4 : ∀ i, ccoordSum r bM (interpD q i) ≤ 16 * Real.sqrt (pc (r + 1)) * Xnorm s q v := fun i =>
    (sum_le_sum fun k _ => (derQ q i k r).2).trans (ccoordSum_interpRec_le (r + 1) s hq v (by omega))
  have b5 : ∀ i, ccoordSum r bM (interpD v i) ≤ 16 * Real.sqrt (pc (r + 1)) * Xnorm s q v := fun i =>
    (sum_le_sum fun k _ => (derQ v i k r).2).trans
      (ccoordSum_interpRec_v_le (r + 1) s q hv (by omega))
  have b6 : ∀ i j, ccoordSum r bM (interpDD q i j) ≤ 16 * Real.sqrt (pc (r + 2)) * Xnorm s q v :=
    fun i j => (sum_le_sum fun k _ => (derQQ q i j k r).2).trans
      ((sum_le_sum fun k _ => (derQ q j k (r + 1)).2).trans
        (ccoordSum_interpRec_le (r + 2) s hq v (by omega)))
  have s4 : ∑ i, ccoordSum r bM (interpD q i) ≤ 3 * (16 * Real.sqrt (pc (r + 1)) * Xnorm s q v) :=
    (sum_le_sum fun i _ => b4 i).trans (by simp)
  have s5 : ∑ i, ccoordSum r bM (interpD v i) ≤ 3 * (16 * Real.sqrt (pc (r + 1)) * Xnorm s q v) :=
    (sum_le_sum fun i _ => b5 i).trans (by simp)
  have s6 : ∑ i, ∑ j, ccoordSum r bM (interpDD q i j) ≤
      9 * (16 * Real.sqrt (pc (r + 2)) * Xnorm s q v) :=
    (sum_le_sum fun i _ => sum_le_sum fun j _ => b6 i j).trans (by simp; ring_nf; rfl)
  have p0 := Real.sqrt_nonneg (pc r)
  have p1 := Real.sqrt_nonneg (pc (r + 1))
  have p2 := Real.sqrt_nonneg (pc (r + 2))
  have hXX := hX
  unfold sizeConst
  rw [← hrdef]
  have m1 : 16 * Real.sqrt (pc r) * Xnorm s q v ≤ 16 * Real.sqrt (pc r) * X :=
    mul_le_mul_of_nonneg_left hX (by positivity)
  have m4 : 16 * Real.sqrt (pc (r + 1)) * Xnorm s q v ≤ 16 * Real.sqrt (pc (r + 1)) * X :=
    mul_le_mul_of_nonneg_left hX (by positivity)
  have m6 : 16 * Real.sqrt (pc (r + 2)) * Xnorm s q v ≤ 16 * Real.sqrt (pc (r + 2)) * X :=
    mul_le_mul_of_nonneg_left hX (by positivity)
  nlinarith

/-- **Size of the 1-jet field** at order `s - 2`. -/
theorem accJet1_size (s : ℕ) (hs : 5 ≤ s) {q v : Grid N → MetricRec} (hq : IsSymRec q)
    (hv : IsSymRec v) {X : ℝ} (hX : Xnorm s q v ≤ X) :
    ccoordSum (s - 2) bPJ (interpJet1 q v) ≤ sizeConst1 s * X := by
  set r2 := s - 2 with hr2def
  unfold interpJet1
  rw [ccoordSum_pjetField]
  have b1 := ccoordSum_interpRec_le r2 s hq v (by omega)
  have b2 := ccoordSum_interpRec_v_le r2 s q hv (by omega)
  have b4 : ∀ i, ccoordSum r2 bM (interpD q i) ≤ 16 * Real.sqrt (pc (r2 + 1)) * Xnorm s q v :=
    fun i => (sum_le_sum fun k _ => (derQ q i k r2).2).trans
      (ccoordSum_interpRec_le (r2 + 1) s hq v (by omega))
  have s4 : ∑ i, ccoordSum r2 bM (interpD q i) ≤ 3 * (16 * Real.sqrt (pc (r2 + 1)) * Xnorm s q v) :=
    (sum_le_sum fun i _ => b4 i).trans (by simp)
  have z2 : ∑ _i : Fin 3, ∑ _j : Fin 3,
      ccoordSum r2 bM ((0 : Fin 3 → Fin 3 → C(T3, MetricRec)) _i _j) = 0 := by
    simp [ccoordSum_zero_rec]
  have z1 : ∑ i : Fin 3, ccoordSum r2 bM ((0 : Fin 3 → C(T3, MetricRec)) i) = 0 := by
    simp [ccoordSum_zero_rec]
  rw [ccoordSum_zero_rec, z1, z2]
  unfold sizeConst1
  rw [← hr2def]
  have m1 : 16 * Real.sqrt (pc r2) * Xnorm s q v ≤ 16 * Real.sqrt (pc r2) * X :=
    mul_le_mul_of_nonneg_left hX (by positivity)
  have m4 : 16 * Real.sqrt (pc (r2 + 1)) * Xnorm s q v ≤ 16 * Real.sqrt (pc (r2 + 1)) * X :=
    mul_le_mul_of_nonneg_left hX (by positivity)
  nlinarith

/-- The difference constant `P_s = √pc(s-3) + √pc(s-2) + √pc(s-1)`. -/
def diffConst (s : ℕ) : ℝ :=
  Real.sqrt (pc (s - 3)) + Real.sqrt (pc (s - 3 + 1)) + Real.sqrt (pc (s - 3 + 2))

theorem diffConst_nonneg (s : ℕ) : 0 ≤ diffConst s := by unfold diffConst; positivity

/-- **Jet difference of two states**: with `D ≥ ‖(q - q', v - v')‖_{X^{s-2}_h} + ‖f - f'‖_{s-3,h}`,
`‖accJet q v f - accJet q' v' f'‖_{H^{s-3}} ≤ 288 P_s D`. -/
theorem accJet_diff (s : ℕ) (hs : 5 ≤ s) {q v q' v' : Grid N → MetricRec} (hq : IsSymRec q)
    (hv : IsSymRec v) (hq' : IsSymRec q') (hv' : IsSymRec v') (f f' : Grid N → MetricRec) {D : ℝ}
    (hD : Xnorm (s - 2) (q - q') (v - v') + Fnorm (s - 3) (f - f') ≤ D) :
    (∀ j, MemH (s - 3) ⇑(ccoord bPJ (accJet q v f - accJet q' v' f') j)) ∧
      ccoordSum (s - 3) bPJ (accJet q v f - accJet q' v' f') ≤ 288 * diffConst s * D := by
  set r := s - 3 with hrdef
  have hX0 := Xnorm_nonneg (s - 2) (q - q') (v - v')
  have hF0 := Fnorm_nonneg (s - 3) (f - f')
  have hXD : Xnorm (s - 2) (q - q') (v - v') ≤ D := by linarith
  have hFD : Fnorm (s - 3) (f - f') ≤ D := by linarith
  have hD0 : 0 ≤ D := hX0.trans hXD
  have hsq := isSymRec_sub hq hq'
  have hsv := isSymRec_sub hv hv'
  set P := diffConst s
  have p0 := Real.sqrt_nonneg (pc r)
  have p1 := Real.sqrt_nonneg (pc (r + 1))
  have p2 := Real.sqrt_nonneg (pc (r + 2))
  have hP0 : Real.sqrt (pc r) ≤ P := by simp only [P, diffConst, ← hrdef]; linarith
  have hP1 : Real.sqrt (pc (r + 1)) ≤ P := by simp only [P, diffConst, ← hrdef]; linarith
  have hP2 : Real.sqrt (pc (r + 2)) ≤ P := by simp only [P, diffConst, ← hrdef]; linarith
  have bound : ∀ (c x : ℝ), 0 ≤ c → c ≤ P → x ≤ D → c * x ≤ P * D := fun c x hc hcP hx =>
    (mul_le_mul_of_nonneg_left hx hc).trans (mul_le_mul_of_nonneg_right hcP hD0)
  have eJ : accJet q v f - accJet q' v' f' =
      pjetField (interpRec q - interpRec q') (interpRec v - interpRec v')
        (interpRec (symRec f) - interpRec (symRec f')) (interpD q - interpD q')
        (interpD v - interpD v') (interpDD q - interpDD q') :=
    pjetField_sub _ _ _ _ _ _ _ _ _ _ _ _
  obtain ⟨m1, c1⟩ := ccoordSum_sub_le_of_upper r _ _ (fun y μ ν => interpRec_symm hq y μ ν)
    (fun y μ ν => interpRec_symm hq' y μ ν) (B := P * D) fun κ =>
      ⟨(lawLimit_interp_diff r q q' κ.1.1 κ.1.2).1, (lawLimit_interp_diff r q q' κ.1.1 κ.1.2).2.trans
        (bound _ _ p0 hP0 ((sobNorm_q_le (s - 2) hsq (v - v') _ _ (by omega)).trans hXD))⟩
  obtain ⟨m2, c2⟩ := ccoordSum_sub_le_of_upper r _ _ (fun y μ ν => interpRec_symm hv y μ ν)
    (fun y μ ν => interpRec_symm hv' y μ ν) (B := P * D) fun κ =>
      ⟨(lawLimit_interp_diff r v v' κ.1.1 κ.1.2).1, (lawLimit_interp_diff r v v' κ.1.1 κ.1.2).2.trans
        (bound _ _ p0 hP0 ((sobNorm_v_le (s - 2) (q - q') hsv _ _ (by omega)).trans hXD))⟩
  obtain ⟨m3, c3⟩ := ccoordSum_sub_le_of_upper r _ _ (fun y μ ν => interpRec_symRec_symm f y μ ν)
    (fun y μ ν => interpRec_symRec_symm f' y μ ν) (B := P * D) fun κ => by
      rw [cmp_interpRec_symRec (N := N), cmp_interpRec_symRec (N := N)]
      exact ⟨(lawLimit_interp_diff r f f' κ.1.1 κ.1.2).1,
        (lawLimit_interp_diff r f f' κ.1.1 κ.1.2).2.trans
          (bound _ _ p0 hP0 ((sobNorm_le_Fnorm r (f - f') κ).trans hFD))⟩
  have m4 := fun i => ccoordSum_sub_le_of_upper r _ _ (fun y μ ν => interpD_symm hq i y μ ν)
    (fun y μ ν => interpD_symm hq' i y μ ν) (B := P * D) fun κ =>
      ⟨(lawLimit_interpD_diff r q q' i κ).1, (lawLimit_interpD_diff r q q' i κ).2.trans
        (bound _ _ p1 hP1 ((sobNorm_q_le (s - 2) hsq (v - v') _ _ (by omega)).trans hXD))⟩
  have m5 := fun i => ccoordSum_sub_le_of_upper r _ _ (fun y μ ν => interpD_symm hv i y μ ν)
    (fun y μ ν => interpD_symm hv' i y μ ν) (B := P * D) fun κ =>
      ⟨(lawLimit_interpD_diff r v v' i κ).1, (lawLimit_interpD_diff r v v' i κ).2.trans
        (bound _ _ p1 hP1 ((sobNorm_v_le (s - 2) (q - q') hsv _ _ (by omega)).trans hXD))⟩
  have m6 := fun i j => ccoordSum_sub_le_of_upper r _ _ (fun y μ ν => interpDD_symm hq i j y μ ν)
    (fun y μ ν => interpDD_symm hq' i j y μ ν) (B := P * D) fun κ =>
      ⟨(lawLimit_interpDD_diff r q q' i j κ).1, (lawLimit_interpDD_diff r q q' i j κ).2.trans
        (bound _ _ p2 hP2 ((sobNorm_q_le (s - 2) hsq (v - v') _ _ (by omega)).trans hXD))⟩
  rw [eJ]
  refine ⟨memH_pjetField m1 m2 m3 (fun i => (m4 i).1) (fun i => (m5 i).1) (fun i j => (m6 i j).1), ?_⟩
  rw [ccoordSum_pjetField]
  have s4 : ∑ i, ccoordSum r bM ((interpD q - interpD q') i) ≤ 3 * (16 * (P * D)) :=
    (sum_le_sum fun i _ => (m4 i).2).trans (by simp)
  have s5 : ∑ i, ccoordSum r bM ((interpD v - interpD v') i) ≤ 3 * (16 * (P * D)) :=
    (sum_le_sum fun i _ => (m5 i).2).trans (by simp)
  have s6 : ∑ i, ∑ j, ccoordSum r bM ((interpDD q - interpDD q') i j) ≤ 9 * (16 * (P * D)) :=
    (sum_le_sum fun i _ => sum_le_sum fun j _ => (m6 i j).2).trans (by simp; ring_nf; rfl)
  linarith

/-- **1-jet difference of two states** at order `s - 2`:
`‖interpJet1 q v - interpJet1 q' v'‖_{H^{s-2}} ≤ 288 P'_s ‖(q - q', v - v')‖_{X^{s-2}_h}`,
`P'_s = √pc(s-2) + √pc(s-1)`. -/
theorem accJet1_diff (s : ℕ) (hs : 5 ≤ s) {q v q' v' : Grid N → MetricRec} (hq : IsSymRec q)
    (hv : IsSymRec v) (hq' : IsSymRec q') (hv' : IsSymRec v') {D : ℝ}
    (hD : Xnorm (s - 2) (q - q') (v - v') ≤ D) :
    (∀ j, MemH (s - 2) ⇑(ccoord bPJ (interpJet1 q v - interpJet1 q' v') j)) ∧
      ccoordSum (s - 2) bPJ (interpJet1 q v - interpJet1 q' v') ≤
        288 * (Real.sqrt (pc (s - 2)) + Real.sqrt (pc (s - 2 + 1))) * D := by
  set r := s - 2 with hrdef
  have hD0 : 0 ≤ D := (Xnorm_nonneg _ _ _).trans hD
  have hsq := isSymRec_sub hq hq'
  have hsv := isSymRec_sub hv hv'
  set P := Real.sqrt (pc r) + Real.sqrt (pc (r + 1))
  have p0 := Real.sqrt_nonneg (pc r)
  have p1 := Real.sqrt_nonneg (pc (r + 1))
  have hP0 : Real.sqrt (pc r) ≤ P := by simp only [P]; linarith
  have hP1 : Real.sqrt (pc (r + 1)) ≤ P := by simp only [P]; linarith
  have bound : ∀ (c x : ℝ), 0 ≤ c → c ≤ P → x ≤ D → c * x ≤ P * D := fun c x hc hcP hx =>
    (mul_le_mul_of_nonneg_left hx hc).trans (mul_le_mul_of_nonneg_right hcP hD0)
  have eJ : interpJet1 q v - interpJet1 q' v' =
      pjetField (interpRec q - interpRec q') (interpRec v - interpRec v') (0 - 0)
        (interpD q - interpD q') (0 - 0) (0 - 0) :=
    pjetField_sub _ _ _ _ _ _ _ _ _ _ _ _
  obtain ⟨m1, c1⟩ := ccoordSum_sub_le_of_upper r _ _ (fun y μ ν => interpRec_symm hq y μ ν)
    (fun y μ ν => interpRec_symm hq' y μ ν) (B := P * D) fun κ =>
      ⟨(lawLimit_interp_diff r q q' κ.1.1 κ.1.2).1, (lawLimit_interp_diff r q q' κ.1.1 κ.1.2).2.trans
        (bound _ _ p0 hP0 ((sobNorm_q_le (s - 2) hsq (v - v') _ _ (by omega)).trans hD))⟩
  obtain ⟨m2, c2⟩ := ccoordSum_sub_le_of_upper r _ _ (fun y μ ν => interpRec_symm hv y μ ν)
    (fun y μ ν => interpRec_symm hv' y μ ν) (B := P * D) fun κ =>
      ⟨(lawLimit_interp_diff r v v' κ.1.1 κ.1.2).1, (lawLimit_interp_diff r v v' κ.1.1 κ.1.2).2.trans
        (bound _ _ p0 hP0 ((sobNorm_v_le (s - 2) (q - q') hsv _ _ (by omega)).trans hD))⟩
  have m4 := fun i => ccoordSum_sub_le_of_upper r _ _ (fun y μ ν => interpD_symm hq i y μ ν)
    (fun y μ ν => interpD_symm hq' i y μ ν) (B := P * D) fun κ =>
      ⟨(lawLimit_interpD_diff r q q' i κ).1, (lawLimit_interpD_diff r q q' i κ).2.trans
        (bound _ _ p1 hP1 ((sobNorm_q_le (s - 2) hsq (v - v') _ _ (by omega)).trans hD))⟩
  rw [eJ]
  simp only [sub_zero]
  refine ⟨memH_pjetField m1 m2 (memH_ccoord_zero_rec r) (fun i => (m4 i).1)
    (fun i => memH_ccoord_zero_rec r) (fun i j => memH_ccoord_zero_rec r), ?_⟩
  rw [ccoordSum_pjetField]
  have s4 : ∑ i, ccoordSum r bM ((interpD q - interpD q') i) ≤ 3 * (16 * (P * D)) :=
    (sum_le_sum fun i _ => (m4 i).2).trans (by simp)
  have z1 : ∑ i : Fin 3, ccoordSum r bM ((0 : Fin 3 → C(T3, MetricRec)) i) = 0 := by
    simp [ccoordSum_zero_rec]
  have z2 : ∑ i : Fin 3, ∑ j : Fin 3,
      ccoordSum r bM ((0 : Fin 3 → Fin 3 → C(T3, MetricRec)) i j) = 0 := by
    simp [ccoordSum_zero_rec]
  rw [ccoordSum_zero_rec, z1, z2]
  have hPD : 0 ≤ P * D := mul_nonneg (by positivity) hD0
  linarith

/-- **Small jets have nondegenerate interpolated metrics** (any acceleration slot), and the
interpolated metric is within `r` of Minkowski: for every `r > 0` there is `δ > 0` with
`‖accJet q v f‖_{H^{s-3}} ≤ δ ⇒ ‖𝓘_h q(y)‖ < r` at every point. -/
theorem accJet_pointwise_small (s : ℕ) (hs : 5 ≤ s) {r : ℝ} (hr : 0 < r) :
    ∃ δ > 0, ∀ (N : ℕ) [NeZero N] (q v f : Grid N → MetricRec),
      ccoordSum (s - 3) bPJ (accJet q v f) ≤ δ → ∀ y, ‖interpRec q y‖ < r := by
  set B : ℝ := 1 + ∑ j, ‖bPJ j‖
  have hB : ∀ j, ‖bPJ j‖ ≤ B := fun j => by
    have := single_le_sum (f := fun j => ‖bPJ j‖) (fun _ _ => norm_nonneg _) (mem_univ j)
    linarith
  have hB0 : 0 ≤ B := by
    have : 0 ≤ ∑ j, ‖bPJ j‖ := sum_nonneg fun _ _ => norm_nonneg _
    linarith
  have hpos : 0 < 2 * (B * Real.sqrt cEmb + 1) := by positivity
  refine ⟨r / (2 * (B * Real.sqrt cEmb + 1)), div_pos hr hpos, fun N _ q v f hδ y => ?_⟩
  have h1 : ‖interpRec q y‖ ≤ ‖accJet q v f y‖ := norm_fst_le (accJet q v f y)
  have h2 := norm_le_ccoordSum (s - 3) (by omega) bPJ hB (accJet q v f) (accJet_memH _ q v f) y
  have h3 : B * (Real.sqrt cEmb * ccoordSum (s - 3) bPJ (accJet q v f)) ≤
      B * (Real.sqrt cEmb * (r / (2 * (B * Real.sqrt cEmb + 1)))) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hδ (Real.sqrt_nonneg _)) hB0
  have h4 : B * (Real.sqrt cEmb * (r / (2 * (B * Real.sqrt cEmb + 1)))) < r := by
    have e : B * (Real.sqrt cEmb * (r / (2 * (B * Real.sqrt cEmb + 1)))) =
        r * (B * Real.sqrt cEmb / (2 * (B * Real.sqrt cEmb + 1))) := by ring
    rw [e]
    have : B * Real.sqrt cEmb / (2 * (B * Real.sqrt cEmb + 1)) < 1 := by
      rw [div_lt_one hpos]; nlinarith [Real.sqrt_nonneg cEmb]
    nlinarith
  linarith

/-- **`∂ₜ c(g_h)` along a solution of an arbitrary acceleration law**: along a solution of
`q_t = v`, `v_t = Acc(q, v)` on `[0, T]`, where `g_h = η + 𝓘_h q` is nondegenerate,
`τ ↦ c_b(g_h)(τ, y)` has derivative `dtGaugeOf (accJet q v (Acc q v))` within `[0, T]`. -/
theorem gauge_hasDerivWithinAt_acc
    {Acc : (Grid N → MetricRec) → (Grid N → MetricRec) → Grid N → MetricRec}
    {T : ℝ} {q v : ℝ → Grid N → MetricRec} (hsol : OpenWriterLifespan.IsAccSolution Acc T q v)
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) (y : T3)
    (hdet : (Matrix.of (minkowski + interpRec (q t) y)).det ≠ 0) (b : Fin 4) :
    HasDerivWithinAt (fun τ => gaugeOf (accJet (q τ) (v τ) (Acc (q τ) (v τ)) y) b)
      (dtGaugeOf (accJet (q t) (v t) (Acc (q t) (v t)) y) b) (Set.Icc 0 T) t := by
  set Z : ℝ → PJet := fun τ => (interpRec (q τ) y, interpRec (symRec (v τ)) y,
    interpRec (symRec (Acc (q t) (v t))) y, fun i => interpD (q τ) i y,
    fun i => interpD (v t) i y, fun i j => interpDD (q t) i j y) with hZ
  have hsv : symRec (v t) = v t := symRec_of_isSymRec (hsol t ht).2.1
  have hZt : Z t = accJet (q t) (v t) (Acc (q t) (v t)) y := by
    simp only [Z, hsv]; rfl
  have hq : HasDerivAt (fun τ => interpRec (q τ) y) (interpRec (symRec (v t)) y) t := by
    rw [hsv]; exact hasDerivAt_interpRec (hsol t ht).2.2.1 y
  have hg : MHasDeriv (fun τ => (pjJet (Z τ)).g) ((pjJet (Z t)).dg 0) t :=
    C3Field.mhasDeriv_of_rec_add minkowski hq
  have hP : Jet3.PathDeriv (fun τ => pjJet (Z τ)) 0 t := by
    refine ⟨hg, ?_, fun a => ?_, fun a b' i j => ?_⟩
    · exact mhasDeriv_inv (A := fun τ => Matrix.of (minkowski + interpRec (q τ) y)) hg hdet
    · refine Fin.cases ?_ (fun i => ?_) a
      · exact C3Field.mhasDeriv_of_rec
          (hasDerivAt_interpRec_symRec (u := v) (t := t) (hsol t ht).2.2.2 y)
      · exact C3Field.mhasDeriv_of_rec (hasDerivAt_interpD (hsol t ht).2.2.1 i y)
    · exact (hasDerivAt_const t ((pjJet (Z t)).ddg a b' i j)).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun τ => rfl)
  have h1 := hP.gc b
  have h2 : (pjJet (Z t)).dgc 0 b = dtGaugeOf (accJet (q t) (v t) (Acc (q t) (v t)) y) b := by
    rw [← hZt]; rfl
  rw [h2] at h1
  refine h1.hasDerivWithinAt.congr (fun τ hτ => ?_) ?_
  · show gaugeOf (accJet (q τ) (v τ) (Acc (q τ) (v τ)) y) b = gaugeOf (Z τ) b
    rw [← gaugeOf_trunc (accJet (q τ) (v τ) (Acc (q τ) (v τ)) y), ← gaugeOf_trunc (Z τ)]
    simp only [Z, trunc, symRec_of_isSymRec (hsol τ hτ).2.1]
    rfl
  · show gaugeOf (accJet (q t) (v t) (Acc (q t) (v t)) y) b = gaugeOf (Z t) b
    rw [hZt]

end Jets

/-! ### Curvature of small jets -/

theorem ccoordSum_zero_pjet (r : ℕ) : ccoordSum r bPJ (0 : C(T3, PJet)) = 0 := by
  unfold ccoordSum
  refine sum_eq_zero fun j _ => ?_
  have : ccoord bPJ (0 : C(T3, PJet)) j = 0 := by ext y; simp
  rw [this, sn_zero_CT]

theorem memH_ccoord_zero_pjet (r : ℕ) (j) : MemH r ⇑(ccoord bPJ (0 : C(T3, PJet)) j) := by
  have : ccoord bPJ (0 : C(T3, PJet)) j = 0 := by ext y; simp
  rw [this]; exact memH_zero r

theorem dgOf_zero : dgOf (0 : PJet) = 0 := by
  funext d
  refine Fin.cases ?_ (fun i => ?_) d <;> simp [dgOf] <;> rfl

theorem ddgOf_zero : ddgOf (0 : PJet) = 0 := by
  funext d e
  refine Fin.cases ?_ (fun i => ?_) d <;> refine Fin.cases ?_ (fun j => ?_) e <;>
    simp [ddgOf] <;> rfl

theorem riemOf_zero : riemOf (0 : PJet) = 0 := by
  funext a b c d
  simp [riemOf, dgOf_zero, ddgOf_zero, christoffel, riemann, dChrOf, dInvOf]

/-- **Curvature of small jet fields** (Moser): there are `δ > 0`, `C ≥ 0` such that every jet
field `P` with `‖P‖_{H^r} ≤ δ` (`r ≥ 2`) has `‖Riem(P)‖_{H^r} ≤ C ‖P‖_{H^r}` componentwise. -/
theorem riem_moser (r : ℕ) (hr : 2 ≤ r) :
    ∃ δ > 0, ∃ C ≥ 0, ∀ (P : C(T3, PJet)), (∀ j, MemH r ⇑(ccoord bPJ P j)) →
      ccoordSum r bPJ P ≤ δ → ∀ a b c d : Fin 4, ∃ F : CT,
        (∀ y, F y = ((riemOf (P y) a b c d : ℝ) : ℂ)) ∧ MemH r ⇑F ∧ sn r ⇑F ≤ C * ccoordSum r bPJ P := by
  obtain ⟨δ, hδ, C, hC, hm⟩ := pjet_moser_fin r hr
    (fun p : Fin 4 × Fin 4 × Fin 4 × Fin 4 => fun z => riemOf z p.1 p.2.1 p.2.2.1 p.2.2.2)
    (fun p => analyticAt_riemOf _ _ _ _ 0 det_minkowski_add_zero)
  refine ⟨δ, hδ, C, hC, fun P hP hPδ a b c d => ?_⟩
  obtain ⟨F, hF, hFm, hFs⟩ := hm (a, b, c, d) P 0 hP (memH_ccoord_zero_pjet r) hPδ
    (by rw [ccoordSum_zero_pjet]; exact hδ.le)
  refine ⟨F, fun y => ?_, hFm, by simpa using hFs⟩
  rw [hF y]
  simp [riemOf_zero]

/-! ### Uniqueness next to a small writer solution -/

/-- **Uniqueness of writer solutions next to a small one**, on any interval: there is `b > 0`
(independent of the mesh) such that if `(q, v)` solves the open writer on `[0, T]` and stays in
the ball `‖·‖_{X^s_h} ≤ b`, every writer solution `(q', v')` on `[0, T]` with the same initial
record coincides with it on `[0, T]`. -/
theorem writer_eq_of_small (s : ℕ) (hs : 2 ≤ s) :
    ∃ b > 0, ∀ (N : ℕ) [NeZero N] (T : ℝ) (q v q' v' : ℝ → Grid N → MetricRec),
      IsWriterSolution T q v → IsWriterSolution T q' v' → q' 0 = q 0 → v' 0 = v 0 →
      (∀ t ∈ Set.Icc 0 T, Xnorm s (q t) (v t) ≤ b) →
      ∀ t ∈ Set.Icc 0 T, q' t = q t ∧ v' t = v t := by
  obtain ⟨r₀, hr₀, hchart⟩ := exists_det_chart
  set ρ : ℝ := r₀ / 4 with hρdef
  have hρ : 0 < ρ := by positivity
  have hρr : 2 * ρ < r₀ := by simp only [ρ]; linarith
  have hS := supConst_nonneg
  set b : ℝ := ρ / (supConst + 1) with hbdef
  have hb : 0 < b := by positivity
  have hregion : ∀ (N : ℕ) [NeZero N] (y : State N), Xnorm s y.1 y.2 ≤ 2 * b →
      ‖symL y‖ ≤ 2 * ρ := by
    intro N _ y hy
    refine (norm_symL_le s hs y).trans ?_
    have e : supConst * (2 * b) = 2 * ρ * (supConst / (supConst + 1)) := by
      simp only [b]; ring
    have h1 : supConst / (supConst + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    calc supConst * Xnorm s y.1 y.2 ≤ supConst * (2 * b) := mul_le_mul_of_nonneg_left hy hS
      _ = 2 * ρ * (supConst / (supConst + 1)) := e
      _ ≤ 2 * ρ * 1 := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 2 * ρ := mul_one _
  refine ⟨b, hb, fun N _ T q v q' v' hsol hsol' hq0 hv0 hsmall => ?_⟩
  obtain ⟨L, M, hL, -⟩ := exists_lipschitz_writerField hchart hρr N
  -- uniqueness on `[0, t]` while both stay in the region
  have hunique : ∀ t ∈ Set.Icc 0 T, (∀ τ ∈ Set.Icc 0 t, Xnorm s (q' τ) (v' τ) ≤ 2 * b) →
      ∀ τ ∈ Set.Icc 0 t, q' τ = q τ ∧ v' τ = v τ := by
    intro t ht hreg'
    have hsolt : IsWriterSolution t q v := fun τ hτ => hsol τ ⟨hτ.1, hτ.2.trans ht.2⟩
    have hsolt' : IsWriterSolution t q' v' := fun τ hτ => hsol' τ ⟨hτ.1, hτ.2.trans ht.2⟩
    have heq := ODE_solution_unique_of_mem_Icc_right (v := fun _ => writerField (N := N))
      (s := fun _ => {y | ‖symL y‖ ≤ 2 * ρ}) (K := L) (a := 0) (b := t)
      (f := fun τ => ((q' τ, v' τ) : State N)) (g := fun τ => ((q τ, v τ) : State N))
      (fun _ _ => hL) (continuousOn_of_writer hsolt')
      (fun τ hτ => hasDerivWithinAt_field_of_writer hsolt' hτ)
      (fun τ hτ => hregion N ((q' τ, v' τ) : State N) (hreg' τ (Set.Ico_subset_Icc_self hτ)))
      (continuousOn_of_writer hsolt)
      (fun τ hτ => hasDerivWithinAt_field_of_writer hsolt hτ)
      (fun τ hτ => hregion N ((q τ, v τ) : State N)
        ((hsmall τ ⟨(Set.Ico_subset_Icc_self hτ).1,
          (Set.Ico_subset_Icc_self hτ).2.trans ht.2⟩).trans (by linarith)))
      (by simp only [hq0, hv0])
    intro τ hτ
    have := heq hτ
    simp only [Prod.mk.injEq] at this
    exact this
  -- the second solution stays in the small ball
  have hcont : ContinuousOn (fun τ => Xnorm s (q' τ) (v' τ)) (Set.Icc 0 T) := by
    intro t ht
    obtain ⟨-, -, hq, hv⟩ := hsol' t ht
    exact continuousWithinAt_Xnorm s
      (fun x κ => (hasDerivAt_pi.1 (hasDerivAt_pi.1 (hq x) κ.1.1) κ.1.2).continuousAt
        |>.continuousWithinAt)
      (fun x κ => (hv x κ).continuousAt.continuousWithinAt)
  have hT0 : ∀ t ∈ Set.Icc 0 T, (0 : ℝ) ∈ Set.Icc 0 T := fun t ht => ⟨le_rfl, ht.1.trans ht.2⟩
  have hstay : ∀ t ∈ Set.Icc 0 T, Xnorm s (q' t) (v' t) ≤ b := by
    by_cases hT : 0 ≤ T
    · refine ODECutoff.firstExit_le (a := b) (b := 2 * b) hcont (by linarith) ?_ fun t ht hbt => ?_
      · rw [hq0, hv0]; exact hsmall 0 ⟨le_rfl, hT⟩
      · obtain ⟨e1, e2⟩ := hunique t ht hbt t ⟨ht.1, le_rfl⟩
        rw [e1, e2]; exact hsmall t ht
    · intro t ht; exact absurd (ht.1.trans ht.2) hT
  intro t ht
  by_cases hT : 0 ≤ T
  · exact hunique T ⟨hT, le_rfl⟩ (fun τ hτ => (hstay τ hτ).trans (by linarith)) t ht
  · exact absurd (ht.1.trans ht.2) hT

/-! ### The rate lift along grid records -/

/-- The pointwise rate-lift package of `rateLift_chart` for the metric `g` at mesh `h`. -/
def RateLiftAt (g : MetricRec) (h : ℝ) : Prop :=
  (∀ i j, h ^ 2 * ∑ a : D3Root, (liftK h (rateMatrix g) (shiftUp g) a true +
      liftK h (rateMatrix g) (shiftUp g) a false) * rootVec a i * rootVec a j = rateMatrix g i j) ∧
  (∀ i, h * ∑ a : D3Root, (liftK h (rateMatrix g) (shiftUp g) a true -
      liftK h (rateMatrix g) (shiftUp g) a false) * rootVec a i = shiftUp g i) ∧
  (∀ a, |liftC (rateMatrix g) a - 1 / 4| ≤ 5 / 56) ∧
  (∀ a s, 1 / 16 ≤ h ^ 2 * liftK h (rateMatrix g) (shiftUp g) a s ∧
    h ^ 2 * liftK h (rateMatrix g) (shiftUp g) a s ≤ 3 / 16) ∧
  (1 / 2 ≤ lapseSq g ∧ lapseSq g ≤ 2) ∧
  (1 / 2 ≤ (spatialMetric g).det ∧ (spatialMetric g).det ≤ 2) ∧
  (1 / 2 ≤ volumeDensity g ∧ volumeDensity g ≤ 2) ∧
  ∀ ξ : Fin 3 → ℝ, (∑ i, ξ i ^ 2) / 2 ≤ ∑ i, ∑ j, ξ i * spatialMetric g i j * ξ j

section Grid

variable {N : ℕ} [NeZero N]

/-- The vertex masses `m_x = ϱ(η + q(x)) h³` of the rate-lift graph. -/
def liftMass (q : Grid N → MetricRec) (x : Fin 3 → ZMod N) : ℝ :=
  volumeDensity (minkowski + q x) * meshN N ^ 3

/-- The directed rates `k_a^±(x)` of the rate lift of `η + q(x)` at mesh `h = 1/N`. -/
def liftRate (q : Grid N → MetricRec) (x : Fin 3 → ZMod N) (a : D3Root) (s : Bool) : ℝ :=
  liftK (meshN N) (rateMatrix (minkowski + q x)) (shiftUp (minkowski + q x)) a s

/-- **The rate-lift margin of a grid record**: the pointwise package at every grid point, the
interior-cone data of the rate-lift graph, and for odd `N` the spatial cut margin
`I^sp ≥ 1/4096` and the full `RenewalSpatialPositiveScreen` package
(`I = 1/4096`, `D = 6`, `V_* = 2`). -/
def RateLiftMargin (q : Grid N → MetricRec) : Prop :=
  ∃ hc : ConeData (liftMass q) (liftRate q),
    (∀ x, RateLiftAt (minkowski + q x) (meshN N)) ∧
    ∀ m₀ : ℕ, N = 2 * m₀ + 1 →
      (∀ A, (d3Graph _ _ hc.mass_pos hc.rate_nonneg).IsHalfVolumeCut A →
        1 / 4096 ≤ (d3Graph _ _ hc.mass_pos hc.rate_nonneg).cutRatio
          (fun x y => meshN N * (d3Graph _ _ hc.mass_pos hc.rate_nonneg).conductance x y) A) ∧
      Nonempty ((d3Graph _ _ hc.mass_pos hc.rate_nonneg).RenewalSpatialPositiveScreen
        (1 / 4096) 6 (meshN N) 2)

theorem meshN_le_one : meshN N ≤ 1 := by
  unfold meshN
  have : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  rw [div_le_one (by linarith)]; exact this

theorem coneData_of_rateLiftAt {q : Grid N → MetricRec}
    (h : ∀ x, RateLiftAt (minkowski + q x) (meshN N)) : ConeData (liftMass q) (liftRate q) := by
  have hh := meshN_pos (N := N)
  refine ⟨fun x => ?_, fun x => ?_, fun x a s => ?_, fun x a s => ?_⟩
  · have := (h x).2.2.2.2.2.2.1.1
    unfold liftMass
    have h3 : 0 < meshN N ^ 3 := by positivity
    nlinarith
  · have := (h x).2.2.2.2.2.2.1.2
    unfold liftMass
    have h3 : 0 < meshN N ^ 3 := by positivity
    nlinarith
  · have := ((h x).2.2.2.1 a s).1
    unfold liftRate
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  · have := ((h x).2.2.2.1 a s).2
    unfold liftRate
    rw [le_div_iff₀ (by positivity)]
    nlinarith

/-- `RateLiftMargin` from the pointwise package. -/
theorem rateLiftMargin_of_at {q : Grid N → MetricRec}
    (h : ∀ x, RateLiftAt (minkowski + q x) (meshN N)) : RateLiftMargin q := by
  refine ⟨coneData_of_rateLiftAt h, h, fun m₀ hN => ⟨fun A hA => d3_cutRatio_ge hN (coneData_of_rateLiftAt h) A hA, ?_⟩⟩
  obtain ⟨S, -⟩ := d3_screen hN (coneData_of_rateLiftAt h)
  exact ⟨S⟩

end Grid

/-- The pointwise rate lift of every small symmetric metric record (`rateLift_chart`). -/
theorem rateLiftAt_chart : ∃ r > 0, ∀ g : MetricRec, (∀ μ ν, g μ ν = g ν μ) →
    ‖g - minkowski‖ < r → ∀ h : ℝ, 0 < h → h ≤ 1 → RateLiftAt g h :=
  rateLift_chart

/-- **Small symmetric records carry the rate-lift margin**: there is `ρ > 0` such that every
symmetric grid record with `‖q(x)‖ < ρ` at every grid point satisfies `RateLiftMargin q`. -/
theorem rateLift_grid : ∃ ρ > 0, ∀ (N : ℕ) [NeZero N] (q : Grid N → MetricRec), IsSymRec q →
    (∀ x, ‖q x‖ < ρ) → RateLiftMargin q := by
  obtain ⟨r, hr, hc⟩ := rateLiftAt_chart
  refine ⟨r, hr, fun N _ q hq hsmall => rateLiftMargin_of_at fun x => ?_⟩
  refine hc _ (fun μ ν => ?_) (by rw [add_sub_cancel_left]; exact hsmall x) _ meshN_pos
    meshN_le_one
  simp only [Pi.add_apply, hq x μ ν, OpenWriterEnergyEstimate.minkowski_symm μ ν]

/-- **The rate-lift margin on the `X^s_h` ball**: there is `δ > 0` (independent of the mesh)
such that every symmetric record with `‖(q, v)‖_{X^s_h} ≤ δ` satisfies `RateLiftMargin q`. -/
theorem rateLift_of_Xnorm (s : ℕ) (hs : 1 ≤ s) : ∃ δ > 0, ∀ (N : ℕ) [NeZero N]
    (q v : Grid N → MetricRec), IsSymRec q → Xnorm s q v ≤ δ → RateLiftMargin q := by
  obtain ⟨ρ, hρ, hg⟩ := rateLift_grid
  have hS := supConst_nonneg
  refine ⟨ρ / (2 * (supConst + 1)), by positivity, fun N _ q v hq hX => hg N q hq fun x => ?_⟩
  have h1 := norm_q_le s hs hq v x
  have h2 : supConst * Xnorm s q v ≤ supConst * (ρ / (2 * (supConst + 1))) :=
    mul_le_mul_of_nonneg_left hX hS
  have h3 : supConst * (ρ / (2 * (supConst + 1))) < ρ := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith
  linarith

/-- **The rate lift of the interpolated metric** at every point of the torus: there is `δ > 0`
such that a symmetric record whose jet field (any acceleration slot) has `H^{s-3}` size `≤ δ`
has `RateLiftAt (η + 𝓘_h q(y)) h` for every `y ∈ 𝕋³` (in particular the interpolated metric is
uniformly noncollapsed: `N², det γ, ϱ ∈ [1/2, 2]`, `ξᵀγξ ≥ |ξ|²/2`). -/
theorem rateLift_interp (s : ℕ) (hs : 5 ≤ s) : ∃ δ > 0, ∀ (N : ℕ) [NeZero N]
    (q v f : Grid N → MetricRec), IsSymRec q → ccoordSum (s - 3) bPJ (accJet q v f) ≤ δ →
      ∀ y, RateLiftAt (minkowski + interpRec q y) (meshN N) := by
  obtain ⟨r, hr, hc⟩ := rateLiftAt_chart
  obtain ⟨δ, hδ, hsm⟩ := accJet_pointwise_small s hs hr
  refine ⟨δ, hδ, fun N _ q v f hq hJ y => ?_⟩
  refine hc _ (fun μ ν => ?_) (by rw [add_sub_cancel_left]; exact hsm N q v f hJ y) _ meshN_pos
    meshN_le_one
  simp only [Pi.add_apply, interpRec_symm hq y μ ν, OpenWriterEnergyEstimate.minkowski_symm μ ν]

/-! ### The uniform (O3) package along central and law-family histories -/

/-- **The per-time (O3) conclusions** for a writer state `(q, v)` with acceleration record `f`
at mesh `h = 1/(n + 1)`:
* the harmonic subsidiary field and Einstein residual of `g_h = η + 𝓘_h q` (with the jet
  `accJet q v f`): `‖c(g_h)‖_{H^{s-2}}, ‖∂ₜc(g_h)‖_{H^{s-3}}, ‖G(g_h)‖_{H^{s-3}} ≤ C ε h`
  (componentwise, `eq:main-open-subsidiary`);
* the uniform curvature bound `‖Riem(g_h)‖_{H^{s-3}} ≤ C ε` (componentwise);
* `RateLiftMargin q`: positive `A₃` rate lift in the interior cone at every grid point, ADM
  inversion, noncollapse, and for odd `N` the cut margin `I^sp ≥ 1/4096` with the spatial screen;
* noncollapse of the interpolated metric: `RateLiftAt (η + 𝓘_h q(y)) h` at every `y ∈ 𝕋³`. -/
def UniformO3 (s : ℕ) (C ε : ℝ) (n : ℕ) (q v f : Grid (n + 1) → MetricRec) : Prop :=
  (∀ b, ∃ F : CT, (∀ y, F y = ((gaugeOf (accJet q v f y) b : ℝ) : ℂ)) ∧
    MemH (s - 2) ⇑F ∧ sn (s - 2) ⇑F ≤ C * ε * ((n : ℝ) + 1)⁻¹) ∧
  (∀ b, ∃ F : CT, (∀ y, F y = ((dtGaugeOf (accJet q v f y) b : ℝ) : ℂ)) ∧
    MemH (s - 3) ⇑F ∧ sn (s - 3) ⇑F ≤ C * ε * ((n : ℝ) + 1)⁻¹) ∧
  (∀ μ ν, ∃ F : CT, (∀ y, F y = ((einOf (accJet q v f y) μ ν : ℝ) : ℂ)) ∧
    MemH (s - 3) ⇑F ∧ sn (s - 3) ⇑F ≤ C * ε * ((n : ℝ) + 1)⁻¹) ∧
  (∀ a b c d, ∃ F : CT, (∀ y, F y = ((riemOf (accJet q v f y) a b c d : ℝ) : ℂ)) ∧
    MemH (s - 3) ⇑F ∧ sn (s - 3) ⇑F ≤ C * ε) ∧
  RateLiftMargin q ∧
  ∀ y, RateLiftAt (minkowski + interpRec q y) (meshN (n + 1))

theorem isMark_zero : IsMark 0 (fun _ _ => 0) := ⟨fun _ _ => rfl, fun ξ η => by simp⟩

theorem restrict_acc {N : ℕ} {Acc : (Grid N → MetricRec) → (Grid N → MetricRec) → Grid N → MetricRec}
    {T T' : ℝ} {q v : ℝ → Grid N → MetricRec} (h : IsAccSolution Acc T q v) (hT : T' ≤ T) :
    IsAccSolution Acc T' q v := fun t ht => h t ⟨ht.1, ht.2.trans hT⟩

theorem restrict_writer {N : ℕ} {T T' : ℝ} {q v : ℝ → Grid N → MetricRec}
    (h : IsWriterSolution T q v) (hT : T' ≤ T) : IsWriterSolution T' q v :=
  fun t ht => h t ⟨ht.1, ht.2.trans hT⟩

set_option maxHeartbeats 16000000 in
/-- **Clause (O3) of `thm:main-open-3plus1` and the last sentence of `thm:supp-law-einstein`**
(uniformity over the law family), for `s ≥ 6`.  There are `ε_s, T > 0`, `T_B ≥ T` and `C ≥ 0`
such that for every `(γ, K) ∈ D_s(ε)` (`DsData`, `dataSize ≤ ε ≤ ε_s`) with the harmonic
preparation `V₀ = prepFun`:
* the central writer has, for every mesh `h = 1/(n + 1)`, a unique solution on `[0, T]` from the
  samples of `(Q₀, V₀)` (the solution of `thm:supp-open-einstein` / `supp_law_einstein`), and at
  every `t ∈ [0, T]` it satisfies `UniformO3`: the subsidiary bound `eq:main-open-subsidiary`
  `≤ C h ε`, the uniform curvature bound `≤ C ε`, the positive `A₃` rate lift in the interior
  cone with ADM inversion and noncollapse at every grid point, the cutoff-uniform cut margin
  `I^sp ≥ 1/4096` and spatial screen for odd `N`, and noncollapse of the interpolated metric;
  `∂ₜ c(g_h)` is the actual time derivative;
* for **every** sequence of marks `B_n` (`‖B_n‖_op ≤ b_n ≤ 1/48`, no convergence), the law-family
  solutions (unique on `[0, T_B]`, those of `supp_law_einstein`) satisfy the same `UniformO3`
  package with the **same** constant `C` (the subsidiary field, rate positivity, cut margin,
  noncollapse and curvature estimates are uniform on the coefficient ball), `∂ₜ c(g_{B,h})` is the
  actual time derivative, and the interpolant 2-jets of the law and central histories differ by
  `≤ C b_n h ε` in `H^{s-3}`. -/
theorem supp_law_einstein_uniform (s : ℕ) (hs : 6 ≤ s) :
    ∃ εs > 0, ∃ T > 0, ∃ TB ≥ T, ∃ C ≥ 0, ∀ (Q₀ Kr : C(T3, MetricRec))
      (Qd Kd : Fin 3 → C(T3, MetricRec)) (Qdd : Fin 3 → Fin 3 → C(T3, MetricRec)) (ε : ℝ),
      DsData s Q₀ Kr Qd Kd Qdd → dataSize s Q₀ Kr ≤ ε → ε ≤ εs →
      ∃ V₀ : C(T3, MetricRec), ⇑V₀ = prepFun ⇑Q₀ ⇑Kr (fun i => ⇑(Qd i)) ∧
      ∃ q v : ∀ n : ℕ, ℝ → Grid (n + 1) → MetricRec,
        (∀ n, IsWriterSolution T (q n) (v n) ∧ q n 0 = sampleRec (n + 1) ⇑Q₀ ∧
          v n 0 = sampleRec (n + 1) ⇑V₀) ∧
        (∀ n (q' v' : ℝ → Grid (n + 1) → MetricRec), q' 0 = sampleRec (n + 1) ⇑Q₀ →
          v' 0 = sampleRec (n + 1) ⇑V₀ → IsWriterSolution T q' v' →
          ∀ t ∈ Set.Icc 0 T, q' t = q n t ∧ v' t = v n t) ∧
        (∀ n, ∀ t ∈ Set.Icc 0 T,
          UniformO3 s C ε n (q n t) (v n t) (harmonicWriterAcceleration (q n t) (v n t)) ∧
          ∀ y b, HasDerivWithinAt (fun τ => gaugeOf (interpJet (q n τ) (v n τ) y) b)
            (dtGaugeOf (interpJet (q n t) (v n t) y) b) (Set.Icc 0 T) t) ∧
        ∀ (b : ℕ → ℝ) (B : ℕ → Upper → Upper → ℝ), (∀ n, IsMark (b n) (B n)) →
          (∀ n, b n ≤ 1 / 48) →
        ∃ qB vB : ∀ n : ℕ, ℝ → Grid (n + 1) → MetricRec,
          (∀ n, IsAccSolution (lawAccel (B n)) TB (qB n) (vB n) ∧
            qB n 0 = sampleRec (n + 1) ⇑Q₀ ∧ vB n 0 = sampleRec (n + 1) ⇑V₀) ∧
          (∀ n (q' v' : ℝ → Grid (n + 1) → MetricRec), q' 0 = sampleRec (n + 1) ⇑Q₀ →
            v' 0 = sampleRec (n + 1) ⇑V₀ → IsAccSolution (lawAccel (B n)) TB q' v' →
            ∀ t ∈ Set.Icc 0 TB, q' t = qB n t ∧ v' t = vB n t) ∧
          ∀ n, ∀ t ∈ Set.Icc 0 T,
            UniformO3 s C ε n (qB n t) (vB n t) (lawAccel (B n) (qB n t) (vB n t)) ∧
            (∀ y b', HasDerivWithinAt
              (fun τ => gaugeOf (accJet (qB n τ) (vB n τ) (lawAccel (B n) (qB n τ) (vB n τ)) y) b')
              (dtGaugeOf (accJet (qB n t) (vB n t) (lawAccel (B n) (qB n t) (vB n t)) y) b')
              (Set.Icc 0 T) t) ∧
            ccoordSum (s - 3) bPJ (accJet (qB n t) (vB n t) (lawAccel (B n) (qB n t) (vB n t)) -
              interpJet (q n t) (v n t)) ≤ C * b n * ε * ((n : ℝ) + 1)⁻¹ := by
  obtain ⟨εL, hεL, TL, hTL, TB, hTB, K₀, hK₀, C₀, hC₀, Cε₀, hCε₀, CB, hCB, hLaw⟩ :=
    supp_law_einstein s hs
  obtain ⟨εS, hεS, TS, hTS, CS, hCS, hSub⟩ := supp_open_subsidiary s hs
  obtain ⟨bU, hbU, hUniq⟩ := writer_eq_of_small s (by omega)
  obtain ⟨δR, hδR, hRate⟩ := rateLift_of_Xnorm s (by omega)
  obtain ⟨δA, hδA, KA, hKA, hacc⟩ := accel_bound s (by omega)
  obtain ⟨δL, hδL, KL, hKL, hlacc⟩ := lawAccel_bound s (by omega)
  obtain ⟨δI, hδI, hInterp⟩ := rateLift_interp s (by omega)
  obtain ⟨r₁, hr₁, hinv⟩ := exists_inv_chart
  obtain ⟨δP, hδP, hPS⟩ := accJet_pointwise_small s (by omega) hr₁
  obtain ⟨δG, hδG, CG, hCG, hGm⟩ := pjet_moser_fin (s - 2) (by omega)
    (fun b : Fin 4 => fun z => gaugeOf z b) analyticAt_gaugeOf
  obtain ⟨δD, hδD, CD, hCD, hDm⟩ := pjet_moser_fin (s - 3) (by omega)
    (fun b : Fin 4 => fun z => dtGaugeOf z b) analyticAt_dtGaugeOf
  obtain ⟨δE, hδE, CE, hCE, hEm⟩ := pjet_moser_fin (s - 3) (by omega)
    (fun p : Fin 4 × Fin 4 => fun z => einOf z p.1 p.2) (fun p => analyticAt_einOf p.1 p.2)
  obtain ⟨δM, hδM, CR, hCR, hRm⟩ := riem_moser (s - 3) (by omega)
  -- constants
  set Kx : ℝ := KA + KL with hKx
  have hKx0 : 0 ≤ Kx := by positivity
  set S3 : ℝ := sizeConst s Kx
  have hS3 : 0 ≤ S3 := by simp only [S3, sizeConst]; positivity
  set S2 : ℝ := sizeConst1 s
  have hS2 : 0 ≤ S2 := by simp only [S2, sizeConst1]; positivity
  set P : ℝ := diffConst s
  have hP : 0 ≤ P := diffConst_nonneg s
  set P' : ℝ := Real.sqrt (pc (s - 2)) + Real.sqrt (pc (s - 2 + 1))
  have hP' : 0 ≤ P' := by positivity
  set Δ : ℝ := min (min (min bU δR) (min δA δL)) (min (min δD δE) (min (min δM δI) (min δP δG)))
  have hΔ : 0 < Δ := by positivity
  set C : ℝ := CS + (CG + CD + CE + 1) * (288 * (P + P') * CB) + CR * S3 * CB
  have hC : 0 ≤ C := by positivity
  set T : ℝ := min TL TS
  have hT : 0 < T := lt_min hTL hTS
  have hTTL : T ≤ TL := min_le_left _ _
  have hTTS : T ≤ TS := min_le_right _ _
  refine ⟨min (min εL εS) (Δ / ((CB + 1) * (S3 + S2 + 1))), by positivity, T, hT, TB,
    hTTL.trans hTB, C, hC, fun Q₀ Kr Qd Kd Qdd ε hD hsz hε => ?_⟩
  have hεL' : ε ≤ εL := hε.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hεS' : ε ≤ εS := hε.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hεΔ : ε ≤ Δ / ((CB + 1) * (S3 + S2 + 1)) := hε.trans (min_le_right _ _)
  have hε0 : 0 ≤ ε := (add_nonneg (ccoordSum_nonneg _ _ _) (ccoordSum_nonneg _ _ _)).trans hsz
  -- the top-ball radius `X = C_B ε` is below all thresholds
  set X : ℝ := CB * ε with hXdef
  have hX0 : 0 ≤ X := by positivity
  have hXΔ : X ≤ Δ / (S3 + S2 + 1) := by
    rw [le_div_iff₀ (by positivity)] at hεΔ
    rw [le_div_iff₀ (by positivity)]
    have : CB * ε * (S3 + S2 + 1) ≤ ε * ((CB + 1) * (S3 + S2 + 1)) := by nlinarith
    linarith
  have hXΔ' : X ≤ Δ := hXΔ.trans (div_le_self hΔ.le (by linarith))
  have hS3X : S3 * X ≤ Δ := by
    have := mul_le_mul_of_nonneg_left hXΔ hS3
    have e : S3 * (Δ / (S3 + S2 + 1)) ≤ Δ := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
    linarith
  have hS2X : S2 * X ≤ Δ := by
    have := mul_le_mul_of_nonneg_left hXΔ hS2
    have e : S2 * (Δ / (S3 + S2 + 1)) ≤ Δ := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
    linarith
  have hΔbU : Δ ≤ bU := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hΔR : Δ ≤ δR := (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hΔA : Δ ≤ δA := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hΔL : Δ ≤ δL := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hΔD : Δ ≤ δD := (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have hΔE : Δ ≤ δE := (min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hΔM : Δ ≤ δM :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hΔI : Δ ≤ δI :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hΔP : Δ ≤ δP :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hΔG : Δ ≤ δG :=
    (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  -- the law-family theorem and the subsidiary theorem for these data
  obtain ⟨V₀, hV₀, q, v, hsol, Q, V, A, Qd', Vd', Qdd', -, -, -, hmarks⟩ :=
    hLaw Q₀ Kr Qd Kd Qdd ε hD hsz hεL'
  obtain ⟨V₀', hV₀', qS, vS, hsolS, -, hboundS⟩ := hSub Q₀ Kr Qd Kd Qdd ε hD hsz hεS'
  have hVV : V₀ = V₀' := DFunLike.coe_injective (hV₀.trans hV₀'.symm)
  subst hVV
  -- central top-ball bound (zero marks)
  obtain ⟨qZ, vZ, hsZ, huZ, hX0s, hcZ, hlZ⟩ := hmarks (fun _ => 0) (fun _ _ _ => 0) (fun _ => isMark_zero)
    (fun _ => by norm_num)
  have hXq : ∀ n, ∀ t ∈ Set.Icc 0 T, Xnorm s (q n t) (v n t) ≤ X := fun n t ht =>
    (hX0s n t ⟨ht.1, ht.2.trans hTTL⟩).2
  -- identification of the subsidiary-theorem solution on `[0, T]`
  have hident : ∀ n, ∀ t ∈ Set.Icc 0 T, qS n t = q n t ∧ vS n t = v n t := by
    intro n
    exact hUniq (n + 1) T (q n) (v n) (qS n) (vS n) (restrict_writer (hsol n).1 hTTL)
      (restrict_writer (hsolS n).1 hTTS) ((hsolS n).2.1.trans (hsol n).2.1.symm)
      ((hsolS n).2.2.trans (hsol n).2.2.symm) (fun t ht => (hXq n t ht).trans (hXΔ'.trans hΔbU))
  -- generic per-state facts
  have hw0 : ∀ n : ℕ, 0 ≤ ε * ((n : ℝ) + 1)⁻¹ := fun n => mul_nonneg hε0 (by positivity)
  have hcurv : ∀ (n : ℕ) (qq vv f : Grid (n + 1) → MetricRec),
      ccoordSum (s - 3) bPJ (accJet qq vv f) ≤ S3 * X → ∀ a b c d, ∃ F : CT,
        (∀ y, F y = ((riemOf (accJet qq vv f y) a b c d : ℝ) : ℂ)) ∧ MemH (s - 3) ⇑F ∧
          sn (s - 3) ⇑F ≤ C * ε := by
    intro n qq vv f hJ a b c d
    obtain ⟨F, hF, hFm, hFs⟩ := hRm (accJet qq vv f) (accJet_memH _ qq vv f)
      (hJ.trans (hS3X.trans hΔM)) a b c d
    refine ⟨F, hF, hFm, hFs.trans ?_⟩
    calc CR * ccoordSum (s - 3) bPJ (accJet qq vv f) ≤ CR * (S3 * X) :=
          mul_le_mul_of_nonneg_left hJ hCR
      _ = (CR * S3 * CB) * ε := by simp only [X]; ring
      _ ≤ C * ε := by
          apply mul_le_mul_of_nonneg_right _ hε0
          simp only [C]
          have : 0 ≤ (CG + CD + CE + 1) * (288 * (P + P') * CB) := by positivity
          linarith
  have hdetJ : ∀ (n : ℕ) (qq vv f : Grid (n + 1) → MetricRec),
      ccoordSum (s - 3) bPJ (accJet qq vv f) ≤ S3 * X → ∀ y,
        (Matrix.of (minkowski + interpRec qq y)).det ≠ 0 := by
    intro n qq vv f hJ y
    have h1 := hPS (n + 1) qq vv f (hJ.trans (hS3X.trans hΔP)) y
    exact (hinv _ (by rw [add_sub_cancel_left]; exact h1)).1
  -- the central size bounds
  have hJ0 : ∀ n, ∀ t ∈ Set.Icc 0 T,
      ccoordSum (s - 3) bPJ (interpJet (q n t) (v n t)) ≤ S3 * X ∧
      ccoordSum (s - 2) bPJ (interpJet1 (q n t) (v n t)) ≤ S2 * X := by
    intro n t ht
    have hst := (hsol n).1 t ⟨ht.1, ht.2.trans hTTL⟩
    have hXt := hXq n t ht
    refine ⟨accJet_size s (by omega) hst.1 hst.2.1 _ hKx0 hXt fun κ => ?_,
      accJet1_size s (by omega) hst.1 hst.2.1 hXt⟩
    have h1 := hacc (n + 1) (q n t) (v n t) hst.1 hst.2.1 (hXt.trans (hXΔ'.trans hΔA))
      κ.1.1 κ.1.2
    calc PeriodicGridSobolev.sobNorm (s - 3)
          (cx (comp (harmonicWriterAcceleration (q n t) (v n t)) κ.1.1 κ.1.2))
        ≤ PeriodicGridSobolev.sobNorm (s - 1)
          (cx (comp (harmonicWriterAcceleration (q n t) (v n t)) κ.1.1 κ.1.2)) :=
          PeriodicGridSobolev.Moser.sobNorm_mono (by omega) _
      _ ≤ KA * Xnorm s (q n t) (v n t) := h1
      _ ≤ Kx * X := mul_le_mul (by simp only [Kx]; linarith) hXt (Xnorm_nonneg _ _ _)
          hKx0
  -- the central package
  have hcentral : ∀ n, ∀ t ∈ Set.Icc 0 T,
      UniformO3 s C ε n (q n t) (v n t) (harmonicWriterAcceleration (q n t) (v n t)) := by
    intro n t ht
    have hst := (hsol n).1 t ⟨ht.1, ht.2.trans hTTL⟩
    obtain ⟨hJ3, -⟩ := hJ0 n t ht
    obtain ⟨b1, b2, b3, -⟩ := hboundS n t ⟨ht.1, ht.2.trans hTTS⟩
    rw [(hident n t ht).1, (hident n t ht).2] at b1 b2 b3
    have hCSC : CS * ε * ((n : ℝ) + 1)⁻¹ ≤ C * ε * ((n : ℝ) + 1)⁻¹ := by
      have : CS ≤ C := by
        simp only [C]
        have : 0 ≤ (CG + CD + CE + 1) * (288 * (P + P') * CB) := by positivity
        have : 0 ≤ CR * S3 * CB := by positivity
        linarith
      have := mul_le_mul_of_nonneg_right this (hw0 n)
      linarith [mul_assoc CS ε ((n : ℝ) + 1)⁻¹, mul_assoc C ε ((n : ℝ) + 1)⁻¹]
    refine ⟨fun b => ?_, fun b => ?_, fun μ ν => ?_, hcurv n _ _ _ hJ3,
      hRate (n + 1) (q n t) (v n t) hst.1 ((hXq n t ht).trans (hXΔ'.trans hΔR)),
      hInterp (n + 1) (q n t) (v n t) _ hst.1 (hJ3.trans (hS3X.trans hΔI))⟩
    · obtain ⟨F, hF, hFm, hFs⟩ := b1 b; exact ⟨F, hF, hFm, hFs.trans hCSC⟩
    · obtain ⟨F, hF, hFm, hFs⟩ := b2 b; exact ⟨F, hF, hFm, hFs.trans hCSC⟩
    · obtain ⟨F, hF, hFm, hFs⟩ := b3 μ ν; exact ⟨F, hF, hFm, hFs.trans hCSC⟩
  refine ⟨V₀, hV₀, q, v, fun n => ⟨restrict_writer (hsol n).1 hTTL, (hsol n).2.1, (hsol n).2.2⟩,
    fun n q' v' h1 h2 h3 t ht => hUniq (n + 1) T (q n) (v n) q' v'
      (restrict_writer (hsol n).1 hTTL) h3 (h1.trans (hsol n).2.1.symm)
      (h2.trans (hsol n).2.2.symm) (fun t ht => (hXq n t ht).trans (hXΔ'.trans hΔbU)) t ht,
    fun n t ht => ⟨hcentral n t ht, fun y b => ?_⟩, fun bb BB hBB hbb => ?_⟩
  · -- central time derivative
    exact gauge_hasDerivWithinAt (restrict_writer (hsol n).1 hTTL) ht y
      (hdetJ n _ _ _ (hJ0 n t ht).1 y) b
  -- the law family
  obtain ⟨qB, vB, hsolB, huniqB, hXB, hcmpB, hlimB⟩ := hmarks bb BB hBB hbb
  refine ⟨qB, vB, hsolB, huniqB, fun n t ht => ?_⟩
  have htL : t ∈ Set.Icc 0 TL := ⟨ht.1, ht.2.trans hTTL⟩
  have hst := (hsol n).1 t htL
  have hstB := (hsolB n).1 t ⟨ht.1, ht.2.trans (hTTL.trans hTB)⟩
  have hXBt : Xnorm s (qB n t) (vB n t) ≤ X := (hXB n t htL).1
  have hbn0 : 0 ≤ bb n := (hBB n).nonneg
  -- sizes of the law jets
  set fB := lawAccel (BB n) (qB n t) (vB n t)
  have hJB : ccoordSum (s - 3) bPJ (accJet (qB n t) (vB n t) fB) ≤ S3 * X := by
    refine accJet_size s (by omega) hstB.1 hstB.2.1 _ hKx0 hXBt fun κ => ?_
    have h1 := hlacc (n + 1) (BB n) (qB n t) (vB n t) ((hBB n).mono (hbb n)) hstB.1 hstB.2.1
      (hXBt.trans (hXΔ'.trans hΔL)) κ
    calc PeriodicGridSobolev.sobNorm (s - 3) (cx (comp fB κ.1.1 κ.1.2))
        ≤ PeriodicGridSobolev.sobNorm (s - 1) (cx (comp fB κ.1.1 κ.1.2)) :=
          PeriodicGridSobolev.Moser.sobNorm_mono (by omega) _
      _ ≤ KL * Xnorm s (qB n t) (vB n t) := h1
      _ ≤ Kx * X := mul_le_mul (by simp only [Kx]; linarith) hXBt (Xnorm_nonneg _ _ _) hKx0
  have hJB1 : ccoordSum (s - 2) bPJ (interpJet1 (qB n t) (vB n t)) ≤ S2 * X :=
    accJet1_size s (by omega) hstB.1 hstB.2.1 hXBt
  obtain ⟨hJ3, hJ2⟩ := hJ0 n t ht
  -- the difference size `D = C_B h b ε`
  set D : ℝ := CB * ((n : ℝ) + 1)⁻¹ * bb n * ε with hDdef
  have hDiff : Xnorm (s - 2) (qB n t - q n t) (vB n t - v n t) +
      Fnorm (s - 3) (fB - harmonicWriterAcceleration (q n t) (v n t)) ≤ D := by
    have h := ((hcmpB n t htL) (upperOf 0 0)).2.2
    have h0 := PeriodicGridSobolev.Moser.sobNorm_nonneg (s - 4)
      (cx (fun x => jetDeriv (BB n) (qB n t) (vB n t)
        (symRec (lawAccel (BB n) (qB n t) (vB n t))) x (upperOf 0 0).1.1 (upperOf 0 0).1.2) -
      cx (fun x => jetDeriv (fun _ _ => 0) (q n t) (v n t)
        (symRec (harmonicWriterAcceleration (q n t) (v n t))) x (upperOf 0 0).1.1
          (upperOf 0 0).1.2))
    linarith
  have hDw : D ≤ CB * (ε * ((n : ℝ) + 1)⁻¹) := by
    have hb1 : bb n ≤ 1 := (hbb n).trans (by norm_num)
    have : D = CB * (ε * ((n : ℝ) + 1)⁻¹) * bb n := by simp only [D]; ring
    rw [this]
    have h0 : 0 ≤ CB * (ε * ((n : ℝ) + 1)⁻¹) := mul_nonneg hCB (hw0 n)
    nlinarith
  obtain ⟨hdm, hdS⟩ := accJet_diff s (by omega) hstB.1 hstB.2.1 hst.1 hst.2.1 fB
    (harmonicWriterAcceleration (q n t) (v n t)) hDiff
  obtain ⟨hdm1, hdS1⟩ := accJet1_diff s (by omega) hstB.1 hstB.2.1 hst.1 hst.2.1
    (le_trans (le_add_of_nonneg_right (Fnorm_nonneg _ _)) hDiff)
  -- the central subsidiary bounds at this time
  obtain ⟨b1, b2, b3, -⟩ := hboundS n t ⟨ht.1, ht.2.trans hTTS⟩
  rw [(hident n t ht).1, (hident n t ht).2] at b1 b2 b3
  -- the final constant
  have hfin : ∀ (Cm Pq X1 X2 : ℝ), 0 ≤ Cm → Cm ≤ CG + CD + CE + 1 → 0 ≤ Pq → Pq ≤ P + P' →
      X1 ≤ Cm * (288 * Pq * D) → X2 ≤ CS * ε * ((n : ℝ) + 1)⁻¹ →
      X1 + X2 ≤ C * ε * ((n : ℝ) + 1)⁻¹ := by
    intro Cm Pq X1 X2 hCm hCm' hPq hPq' h1 h2
    have hD0 : 0 ≤ D := by simp only [D]; have := hw0 n; positivity
    have k1 : Cm * (288 * Pq * D) ≤ (CG + CD + CE + 1) * (288 * (P + P') * (CB * (ε * ((n : ℝ) + 1)⁻¹))) := by
      apply mul_le_mul hCm' _ (by positivity) (by positivity)
      apply mul_le_mul (by linarith) hDw hD0 (by positivity)
    have e : C * ε * ((n : ℝ) + 1)⁻¹ = CS * ε * ((n : ℝ) + 1)⁻¹ +
        (CG + CD + CE + 1) * (288 * (P + P') * (CB * (ε * ((n : ℝ) + 1)⁻¹))) +
        CR * S3 * CB * (ε * ((n : ℝ) + 1)⁻¹) := by simp only [C]; ring
    have k3 : 0 ≤ CR * S3 * CB * (ε * ((n : ℝ) + 1)⁻¹) := by have := hw0 n; positivity
    linarith
  have hnorm1 : ∀ y, gaugeOf (interpJet (q n t) (v n t) y) = gaugeOf (interpJet1 (q n t) (v n t) y) :=
    fun y => funext fun b => (gaugeOf_trunc _ b).symm
  refine ⟨⟨fun b => ?_, fun b => ?_, fun μ ν => ?_, hcurv n _ _ _ hJB,
    hRate (n + 1) (qB n t) (vB n t) hstB.1 (hXBt.trans (hXΔ'.trans hΔR)),
    hInterp (n + 1) (qB n t) (vB n t) _ hstB.1 (hJB.trans (hS3X.trans hΔI))⟩, fun y b' => ?_, ?_⟩
  · -- gauge covector
    obtain ⟨F1, hF1, hF1m, hF1s⟩ := hGm b (interpJet1 (qB n t) (vB n t)) (interpJet1 (q n t) (v n t))
      (accJet1_memH _ _ _) (accJet1_memH _ _ _) (hJB1.trans (hS2X.trans hΔG))
      (hJ2.trans (hS2X.trans hΔG))
    obtain ⟨F0, hF0, hF0m, hF0s⟩ := b1 b
    refine ⟨F1 + F0, fun y => ?_, memH_add hF1m hF0m,
      (lawLimit_sn_add_le F1 F0 hF0m).trans (hfin CG P' _ _ hCG (by linarith) hP' (by linarith)
        (hF1s.trans (mul_le_mul_of_nonneg_left hdS1 hCG)) hF0s)⟩
    rw [ContinuousMap.add_apply, hF1 y, hF0 y, congrFun (hnorm1 y) b, ← gaugeOf_trunc]
    push_cast; ring_nf; rfl
  · -- its time derivative
    obtain ⟨F1, hF1, hF1m, hF1s⟩ := hDm b (accJet (qB n t) (vB n t) fB) (interpJet (q n t) (v n t))
      (accJet_memH _ _ _ _) (accJet_memH _ _ _ _) (hJB.trans (hS3X.trans hΔD))
      (hJ3.trans (hS3X.trans hΔD))
    obtain ⟨F0, hF0, hF0m, hF0s⟩ := b2 b
    refine ⟨F1 + F0, fun y => ?_, memH_add hF1m hF0m,
      (lawLimit_sn_add_le F1 F0 hF0m).trans (hfin CD P _ _ hCD (by linarith) hP (by linarith)
        (hF1s.trans (mul_le_mul_of_nonneg_left hdS hCD)) hF0s)⟩
    rw [ContinuousMap.add_apply, hF1 y, hF0 y]
    push_cast; ring
  · -- the Einstein tensor
    obtain ⟨F1, hF1, hF1m, hF1s⟩ := hEm (μ, ν) (accJet (qB n t) (vB n t) fB)
      (interpJet (q n t) (v n t)) (accJet_memH _ _ _ _) (accJet_memH _ _ _ _)
      (hJB.trans (hS3X.trans hΔE)) (hJ3.trans (hS3X.trans hΔE))
    obtain ⟨F0, hF0, hF0m, hF0s⟩ := b3 μ ν
    refine ⟨F1 + F0, fun y => ?_, memH_add hF1m hF0m,
      (lawLimit_sn_add_le F1 F0 hF0m).trans (hfin CE P _ _ hCE (by linarith) hP (by linarith)
        (hF1s.trans (mul_le_mul_of_nonneg_left hdS hCE)) hF0s)⟩
    rw [ContinuousMap.add_apply, hF1 y, hF0 y]
    push_cast; ring
  · -- the time derivative of the law-family gauge covector
    exact gauge_hasDerivWithinAt_acc (Acc := lawAccel (BB n))
      (restrict_acc (hsolB n).1 (hTTL.trans hTB)) ht y (hdetJ n _ _ _ hJB y) b'
  · -- the jet comparison
    refine hdS.trans ?_
    have e : C * bb n * ε * ((n : ℝ) + 1)⁻¹ = C * (bb n * ε * ((n : ℝ) + 1)⁻¹) := by ring
    have e2 : 288 * P * D = (288 * P * CB) * (bb n * ε * ((n : ℝ) + 1)⁻¹) := by
      simp only [D]; ring
    rw [e, e2]
    apply mul_le_mul_of_nonneg_right _ (by have := hw0 n; positivity)
    simp only [C]
    have : 288 * P * CB ≤ (CG + CD + CE + 1) * (288 * (P + P') * CB) := by
      have h1 : 288 * P * CB ≤ 288 * (P + P') * CB := by nlinarith
      have h2 : 288 * (P + P') * CB ≤ (CG + CD + CE + 1) * (288 * (P + P') * CB) := by
        have : 0 ≤ 288 * (P + P') * CB := by positivity
        nlinarith
      linarith
    have : 0 ≤ CR * S3 * CB := by positivity
    linarith

/-- Non-vacuity of the hypothesis packet of `supp_law_einstein_uniform`: the flat data
`γ = I`, `K = 0` lie in `D_s(0)`, and the zero mark lies in the coefficient ball. -/
theorem uniform_data_nonvacuous (s : ℕ) :
    DsData s 0 0 (fun _ => 0) (fun _ => 0) (fun _ _ => 0) ∧ dataSize s 0 0 ≤ 0 ∧
      IsMark 0 (fun _ _ => 0) ∧ (0 : ℝ) ≤ 1 / 48 :=
  ⟨dsData_zero s, by simp [dataSize, ccoordSum_zero_rec], isMark_zero, by norm_num⟩

end

end RenewalGeometry.OpenWriterRateLift
