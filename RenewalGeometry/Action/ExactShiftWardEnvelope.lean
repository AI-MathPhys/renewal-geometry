/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Action.ExactShiftWardFlat
import RenewalGeometry.Gravity.HarmonicQuarticAnnihilation

/-!
# The literal constant-shift rows `P_c = ∂_λ𝓗_h[(0, c)]`
  (`eq:supp-exact-ward-objects`, `eq:supp-exact-harmonic-mass-column`: `P_{c,1} = 0`,
  `P_{c,2}(U, p) = ⟨p, δ_c U⟩`; emergent-spacetime manuscript)

All objects are the literal ones: `𝓗_h` is the canonical Hamiltonian of the actual action
(`canonicalHamiltonian` with `Λ = 0`, the symmetric-square-root triad `sqrtTriad` and the selected
stationary connection `statAst χ R`, Legendre chart based at flat data), written in the chart
`X = (u, p)`, `γ = I + u`, `π = p`, `λ = (N, β)` (`Hlit`, base point `pE = (0, (1, 0))`).

* `Prow c z = ∂_λ𝓗_h(z)[(0, c)]`: the constant-shift row (shift `β ↦ β + c`, `c ∈ ℝ³`).
* **`Prow_eq`** (envelope + `ExactShiftCovariance.shiftDen_eq`): near `pE`,
  `P_c(X, λ) = ⟨p, δ_c u⟩_h + Q_c(X, λ)` with
  `Q_c = -⟨δ_cΠ(γ) - DΠ(γ)[δ_cγ], A_sp⟩ - ⟨ρ-terms⟩` (`Qrow`): the Leibniz defect of the phase
  derivative against the spatial stationary connection, plus the link-remainder terms.
* **`Qrow_isBigO`**: `Q_c(X, λ) = O(‖X‖³)` uniformly for `λ` near `(1, 0)`: the Leibniz defect is
  `O(‖u‖²)`, the spatial stationary connection is `O(‖X‖)` because it vanishes on the whole flat
  slice (`ExactShiftWardFlat.flat_slice`), and the link remainders are cubic.

Hence `P_{c,1} = 0`, `P_{c,2}(U, p) = ⟨p, δ_c U⟩_h` and, uniformly in `λ`, all `λ`-derivatives of
`P_c - P_{c,2}` vanish to second order in `X`; this is the input of the Ward packet in
`Gravity/ExactWardPacketLiteral.lean`.
-/

open Filter Finset Metric Asymptotics
open scoped Topology

noncomputable section

set_option linter.unusedSectionVars false

namespace RenewalGeometry.ExactPhaseAction.ShiftWard

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

open PalatiniEinsteinAlgebra OddPhaseDerivativeReal QuadJet

variable {N : ℕ} [NeZero N]

/-! ### Chart, rows and the quadratic form -/

/-- Canonical variables `X = (u, p)` (`γ = I + u`, `π = p`). -/
abbrev Xs (N : ℕ) := MetF N × MetF N

/-- The chart `(X, λ) ↦ ((I + u, N, β), p)`. -/
def embX (z : Xs N × Lam N) : ParF N × MetF N := ((flatMet N + z.1.1, z.2.1, z.2.2), z.1.2)

/-- The linear part of the chart. -/
def embL : (Xs N × Lam N) →L[ℝ] (ParF N × MetF N) :=
  ((((ContinuousLinearMap.fst ℝ (MetF N) (MetF N)).comp
      (ContinuousLinearMap.fst ℝ (Xs N) (Lam N))).prod
    (ContinuousLinearMap.snd ℝ (Xs N) (Lam N))).prod
    ((ContinuousLinearMap.snd ℝ (MetF N) (MetF N)).comp
      (ContinuousLinearMap.fst ℝ (Xs N) (Lam N))))

theorem embX_eq (z : Xs N × Lam N) : embX z = (((flatMet N, 0, 0), 0) : ParF N × MetF N) + embL z := by
  simp [embX, embL]

/-- **The literal canonical Hamiltonian in the chart** `𝓗_h(X, λ)`. -/
def Hlit (χ R : ℝ) (z : Xs N × Lam N) : ℝ := canonH χ R (embX z)

/-- The base point `(X, λ) = (0, (1, 0))`. -/
def pE (N : ℕ) [NeZero N] : Xs N × Lam N := (0, lamE N)

theorem embX_pE : embX (pE N) = qFlat N := by
  simp [embX, pE, lamE, qFlat, zFlat, refMult]

/-- The constant shift `β ↦ β + c`. -/
def shiftLam (c : Fin 3 → ℝ) : Lam N := (0, fun _ => c)

/-- **The constant-shift row** `P_c = ∂_λ𝓗_h[(0, c)]` (`eq:supp-exact-ward-objects`). -/
def Prow (χ R : ℝ) (c : Fin 3 → ℝ) (z : Xs N × Lam N) : ℝ :=
  fderiv ℝ (Hlit χ R) z ((0 : Xs N), shiftLam c)

/-- `δ_c u = Σ_k c_k δ_k u`. -/
def dcMet (c : Fin 3 → ℝ) (u : MetF N) : MetF N := fun x => ∑ k, c k • pd k u x

/-- **The quadratic constant-shift form** `P_{c,2}(u, p) = ⟨p, δ_c u⟩_h`. -/
def qShift (c : Fin 3 → ℝ) (X : Xs N) : ℝ := pairH X.2 (dcMet c X.1)

/-- The Legendre velocity along the chart. -/
def Vh (χ R : ℝ) (z : Xs N × Lam N) : MetF N :=
  legendreVel χ 0 sqrtTriad (statAst χ R) (zFlat N) (embX z).1 (embX z).2

/-- The stationary connection along the chart. -/
def Astar (χ R : ℝ) (z : Xs N × Lam N) : Conn N := Sfun χ R ((embX z).1, Vh χ R z)

/-- **The Leibniz defect** `δ_cΠ_i(γ) - DΠ_i(γ)[δ_cγ]` (it vanishes for the commuting linear
part and is quadratic in `γ - I`). -/
def leib (χ : ℝ) (c : Fin 3 → ℝ) (γ : MetF N) (i : Fin 3) (x : Site N) : M4 :=
  dcPi χ (coframeField sqrtTriad ((γ, fun _ => 1, fun _ => 0) : ParF N)) c i x -
    piDot χ sqrtTriad γ (dcMet c γ) i x

/-- **The cubic remainder** `Q_c = P_c - P_{c,2}`. -/
def Qrow (χ R : ℝ) (c : Fin 3 → ℝ) (z : Xs N × Lam N) : ℝ :=
  -gridPair (hN N) (fun x => ∑ i, pairing (leib χ c (flatMet N + z.1.1) i x)
      (toA (Astar χ R z) i x)) -
    gridPair (hN N) (vDen χ (hN N) (coframeField sqrtTriad (embX z).1) c (toA (Astar χ R z)))

/-! ### Affine dependence of the phase Lagrangian on `∂_tΠ` and of `∂_tΠ` on `V` -/

theorem phaseLagr_P_affine (χ Λ t : ℝ) (e : Site N → M4) (P Q : Fin 3 → Site N → M4)
    (A : Conn N) :
    phaseLagr χ Λ e (P + t • Q) A = phaseLagr χ Λ e P A -
      t * gridPair (hN N) (fun x => ∑ i, pairing (Q i x) (toA A i x)) := by
  unfold phaseLagr nfDensityPh gridPair
  simp only [Pi.add_apply, Pi.smul_apply, neg_add, pairing_add_left, pairing_neg_left,
    pairing_smul_left, Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.mul_sum]
  simp only [← Finset.mul_sum]
  ring

theorem piDot_add_smul (χ : ℝ) (triad : (Fin 3 → Fin 3 → ℝ) → Fin 3 → Fin 3 → ℝ) (γ V W : MetF N)
    (t : ℝ) : piDot χ triad γ (V + t • W) = piDot χ triad γ V + t • piDot χ triad γ W := by
  funext i x
  ext K L
  simp [piDot, map_add, map_smul]

/-- A derivative along a direction in which the function is affine. -/
theorem fderiv_dir_of_affine {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {f' : E →L[ℝ] ℝ} {x v : E} (hf : HasFDerivAt f f' x) (K : ℝ)
    (hc : ∀ t : ℝ, f (x + t • v) = f x + t * K) : f' v = K := by
  have hl : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hf' : HasFDerivAt f f' (x + (0 : ℝ) • v) := by simpa using hf
  have h1 := hf'.comp_hasDerivAt (0 : ℝ) hl
  have h2 : HasDerivAt (fun t : ℝ => f (x + t • v)) K 0 := by
    simp only [hc]
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const K).const_add (f x)
  simpa using h1.unique h2

theorem hasFDerivAt_embX (z : Xs N × Lam N) : HasFDerivAt (embX (N := N)) embL z := by
  have h : (embX (N := N)) = fun z => (((flatMet N, 0, 0), 0) : ParF N × MetF N) + embL z :=
    funext embX_eq
  rw [h]
  exact embL.hasFDerivAt.const_add _

theorem continuous_embX : Continuous (embX (N := N)) := by
  have h : (embX (N := N)) = fun z => (((flatMet N, 0, 0), 0) : ParF N × MetF N) + embL z :=
    funext embX_eq
  rw [h]; exact continuous_const.add embL.continuous

theorem dcMet_flatMet_add (c : Fin 3 → ℝ) (u : MetF N) : dcMet c (flatMet N + u) = dcMet c u := by
  funext x
  simp only [dcMet, map_add, Pi.add_apply]
  have h0 : ∀ k, pd k (flatMet N) x = 0 := fun k => by
    rw [show flatMet N = fun _ => flatSym from rfl, pd_const]; rfl
  simp [h0]

theorem piArr_coframeField_indep (χ : ℝ) (γ : MetF N) (n : Site N → ℝ) (β : Site N → Fin 3 → ℝ)
    (y : Site N) (i : Fin 3) :
    piArr χ (coframeField sqrtTriad ((γ, n, β) : ParF N) y) i =
      piArr χ (coframeField sqrtTriad ((γ, fun _ => 1, fun _ => 0) : ParF N) y) i := by
  simp only [coframeField]
  rw [piArr_admCoframe]

theorem dcPi_indep (χ : ℝ) (γ : MetF N) (n : Site N → ℝ) (β : Site N → Fin 3 → ℝ)
    (c : Fin 3 → ℝ) :
    dcPi χ (coframeField sqrtTriad ((γ, n, β) : ParF N)) c =
      dcPi χ (coframeField sqrtTriad ((γ, fun _ => 1, fun _ => 0) : ParF N)) c := by
  funext i x
  simp only [dcPi, piArr_coframeField_indep]

/-- Shifting the shift multiplier by a constant is the substitution `e ↦ e S_c`. -/
theorem coframeField_shift (p : ParF N) (c : Fin 3 → ℝ) (t : ℝ) :
    coframeField sqrtTriad ((p.1, p.2.1, p.2.2 + t • fun _ => c) : ParF N) =
      fun x => shiftCo (coframeField sqrtTriad p x) (t • c) := by
  funext x
  simp only [coframeField, Pi.add_apply, Pi.smul_apply]
  rw [admCoframe_add_shift]

theorem gridPair_pair_sub (h : ℝ) (a b B : Fin 3 → Site N → M4) :
    gridPair h (fun x => ∑ i, pairing (a i x - b i x) (B i x)) =
      gridPair h (fun x => ∑ i, pairing (a i x) (B i x)) -
        gridPair h (fun x => ∑ i, pairing (b i x) (B i x)) := by
  simp only [gridPair, pairing_sub_left, Finset.sum_sub_distrib, mul_sub]

section Chart

variable {χ R : ℝ} {U : Set (CoP N)} (hU : FlatChart χ R U) (hχ : χ ≠ 0)
include hU hχ

set_option maxHeartbeats 1000000 in
/-- **The literal constant-shift row**: near the base point
`P_c(X, λ) = ⟨p, δ_c u⟩_h + Q_c(X, λ)`. -/
theorem Prow_eq (c : Fin 3 → ℝ) :
    ∀ᶠ z in 𝓝 (pE N), Prow χ R c z = qShift c z.1 + Qrow χ R c z := by
  have hc := legendreChart_flat hU hχ
  have hπ₀ : pairCov (0 : MetF N) = velMom (redLagr χ 0 sqrtTriad (statAst χ R)) (zFlat N) := by
    rw [velMom_flat hU hχ, map_zero]
  obtain ⟨hV0, hVan, hVmom, -, -⟩ := canonical_legendre χ 0 hc hπ₀
  have hH := hasFDerivAt_canonicalHamiltonian χ 0 hc hπ₀
  have hemb : Tendsto (embX (N := N)) (𝓝 (pE N)) (𝓝 ((zFlat N).1, 0)) := by
    have := (continuous_embX (N := N)).continuousAt.tendsto (x := pE N)
    rw [embX_pE] at this
    exact this
  have hy : Tendsto (fun z : Xs N × Lam N => ((embX z).1, Vh χ R z)) (𝓝 (pE N)) (𝓝 (zFlat N)) := by
    have hc1 : ContinuousAt (fun q : ParF N × MetF N =>
        (q.1, legendreVel χ 0 sqrtTriad (statAst χ R) (zFlat N) q.1 q.2)) ((zFlat N).1, 0) :=
      continuousAt_fst.prodMk hVan.continuousAt
    have h := hc1.tendsto.comp hemb
    have h0 : ((((zFlat N).1, (0 : MetF N)) : ParF N × MetF N).1,
        legendreVel χ 0 sqrtTriad (statAst χ R) (zFlat N)
          (((zFlat N).1, (0 : MetF N)) : ParF N × MetF N).1
          (((zFlat N).1, (0 : MetF N)) : ParF N × MetF N).2) = zFlat N := by
      simp only; rw [hV0]
    rw [h0] at h
    exact h
  have hS := analyticAt_Sfun hU
  have hpair : ContinuousAt (fun y : ParF N × MetF N => (y, Sfun χ R y)) (zFlat N) :=
    continuousAt_id.prodMk hS.continuousAt
  have hPev := (analyticAt_PhiL (N := N) χ).eventually_analyticAt
  rw [← pair_Sfun_flat hU] at hPev
  filter_upwards [hemb.eventually hH, hemb.eventually hVmom, hy.eventually (eventually_fderiv_redLagr hU),
    hy.eventually (eventually_stationary hU), hy.eventually (hpair.eventually hPev)]
    with z h1 h2 h3 h4 h5
  set y : ParF N × MetF N := ((embX z).1, Vh χ R z) with hydef
  set A : Conn N := Sfun χ R y with hAdef
  have hA : Astar χ R z = A := rfl
  -- the data at `y`
  set e := (dataMap χ y).1 with hedef
  set P := (dataMap χ y).2 with hPdef
  have hd : DifferentiableAt ℝ (phaseLagr χ 0 e P) A := by
    have hc' : HasFDerivAt (fun A' : Conn N => ((y, A') : (ParF N × MetF N) × Conn N))
        (ContinuousLinearMap.inr ℝ (ParF N × MetF N) (Conn N)) A :=
      (hasFDerivAt_const y A).prodMk (hasFDerivAt_id A)
    exact (h5.differentiableAt.hasFDerivAt.comp A hc').differentiableAt
  have ha0 : gridPair (hN N) (a0Den χ (hN N) e c (toA A)) = 0 :=
    gridPair_a0Den_eq_zero c hd h4.1
  -- the shift derivative of `Φ`
  have hshift : fderiv ℝ (PhiL χ) (y, A) ((((0 : MetF N), (0 : Site N → ℝ), fun _ => c), 0), 0) =
      gridPair (hN N) (shiftDen χ (hN N) e c (toA A)) := by
    refine fderiv_dir_of_affine h5.differentiableAt.hasFDerivAt _ fun t => ?_
    have hy' : ((y, A) + t • ((((0 : MetF N), (0 : Site N → ℝ), fun _ => c), (0 : MetF N)),
        (0 : Conn N)) : (ParF N × MetF N) × Conn N) =
        ((((y.1.1, y.1.2.1, y.1.2.2 + t • fun _ => c) : ParF N), y.2), A) := by
      ext <;> simp
    rw [hy']
    simp only [PhiL, dataMap]
    rw [coframeField_shift y.1 c t, phaseLagr_shift]
    rfl
  -- the momentum derivative of `Φ`
  have hmom : ∀ W : MetF N, fderiv ℝ (PhiL χ) (y, A) ((0, W), 0) =
      -gridPair (hN N) (fun x => ∑ i, pairing (piDot χ sqrtTriad y.1.1 W i x) (toA A i x)) := by
    intro W
    refine fderiv_dir_of_affine h5.differentiableAt.hasFDerivAt _ fun t => ?_
    have hy' : ((y, A) + t • ((((0 : ParF N)), W), (0 : Conn N)) : (ParF N × MetF N) × Conn N) =
        ((y.1, y.2 + t • W), A) := by
      ext <;> simp
    rw [hy']
    simp only [PhiL, dataMap]
    rw [piDot_add_smul, phaseLagr_P_affine]
    ring
  -- the row
  have hrow : Prow χ R c z = -gridPair (hN N) (fun x => ∑ i, pairing (dcPi χ e c i x) (toA A i x)) -
      gridPair (hN N) (vDen χ (hN N) e c (toA A)) := by
    have hd1 : HasFDerivAt (Hlit χ R) ((fderiv ℝ (canonH χ R) (embX z)).comp embL) z := by
      have := h1.differentiableAt.hasFDerivAt
      exact this.comp z (hasFDerivAt_embX z)
    unfold Prow
    rw [hd1.fderiv, ContinuousLinearMap.comp_apply]
    have hcan : canonH χ R = fun q : ParF N × MetF N =>
        canonicalHamiltonian χ 0 sqrtTriad (statAst χ R) (zFlat N) q.1 q.2 := rfl
    rw [hcan, h1.fderiv]
    simp only [embL, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      ContinuousLinearMap.apply_apply, ContinuousLinearMap.inl_apply, map_zero,
      ContinuousLinearMap.zero_apply, zero_sub]
    rw [show legendreVel χ 0 sqrtTriad (statAst χ R) (zFlat N) (embX z).1 (embX z).2 = Vh χ R z
      from rfl]
    rw [h3, show (((0 : MetF N), shiftLam c) : ParF N) = ((0 : MetF N), (0 : Site N → ℝ),
      fun _ => c) from rfl, hshift, gridPair_shiftDen, ha0]
    ring
  -- the quadratic form from the momentum
  have hq : qShift c z.1 = -gridPair (hN N) (fun x => ∑ i, pairing
      (piDot χ sqrtTriad y.1.1 (dcMet c y.1.1) i x) (toA A i x)) := by
    have hV := h2 (dcMet c y.1.1)
    rw [show legendreVel χ 0 sqrtTriad (statAst χ R) (zFlat N) (embX z).1 (embX z).2 = Vh χ R z
      from rfl] at hV
    change fderiv ℝ (redLagr χ 0 sqrtTriad (statAst χ R)) y (0, dcMet c y.1.1) = _ at hV
    rw [h3, hmom] at hV
    unfold qShift
    rw [show z.1.2 = (embX z).2 from rfl, ← dcMet_flatMet_add c z.1.1]
    exact hV.symm
  have hfinal : Qrow χ R c z = -(gridPair (hN N) (fun x => ∑ i, pairing (dcPi χ e c i x)
      (toA A i x)) - gridPair (hN N) (fun x => ∑ i, pairing
      (piDot χ sqrtTriad y.1.1 (dcMet c y.1.1) i x) (toA A i x))) -
      gridPair (hN N) (vDen χ (hN N) e c (toA A)) := by
    have he' : e = coframeField sqrtTriad ((flatMet N + z.1.1, z.2.1, z.2.2) : ParF N) := rfl
    have hl : leib χ c (flatMet N + z.1.1) = fun i x =>
        dcPi χ e c i x - piDot χ sqrtTriad y.1.1 (dcMet c y.1.1) i x := by
      rw [he', dcPi_indep]; rfl
    unfold Qrow
    rw [hA, hl, gridPair_pair_sub]
    rfl
  rw [hrow, hq, hfinal]
  ring

end Chart

/-! ### The Leibniz defect is quadratic -/

section Leibniz

open WardOrders

/-- Second-order Taylor remainder at the flat metric. -/
def T2 (f : (Fin 6 → ℝ) → ℝ) (v : Fin 6 → ℝ) : ℝ :=
  f (flatSym + v) - f flatSym - fderiv ℝ f flatSym v

/-- First-order remainder of the derivative at the flat metric. -/
def T1 (f : (Fin 6 → ℝ) → ℝ) (v : Fin 6 → ℝ) : (Fin 6 → ℝ) →L[ℝ] ℝ :=
  fderiv ℝ f (flatSym + v) - fderiv ℝ f flatSym

theorem vanishes_T2 {f : (Fin 6 → ℝ) → ℝ} (hf : AnalyticAt ℝ f flatSym) :
    VanishesToOrder (T2 f) 0 2 := by
  have hsh : AnalyticAt ℝ (fun v : Fin 6 → ℝ => f (flatSym + v)) 0 :=
    hf.comp_of_eq (analyticAt_const.add analyticAt_id) (by simp)
  have hT : AnalyticAt ℝ (T2 f) 0 :=
    (hsh.sub analyticAt_const).sub ((fderiv ℝ f flatSym).analyticAt 0)
  refine vanishesToOrder_two (hT.eventually_analyticAt.mono fun v hv => hv.differentiableAt)
    hT.fderiv.differentiableAt (by simp [T2]) ?_
  have h1 : HasFDerivAt (fun v : Fin 6 → ℝ => f (flatSym + v)) (fderiv ℝ f flatSym) 0 := by
    have hf' : HasFDerivAt f (fderiv ℝ f flatSym) (flatSym + (0 : Fin 6 → ℝ)) := by
      simpa using hf.differentiableAt.hasFDerivAt
    exact hf'.comp (0 : Fin 6 → ℝ) ((hasFDerivAt_id (0 : Fin 6 → ℝ)).const_add flatSym)
  have h2 : HasFDerivAt (T2 f) (fderiv ℝ f flatSym - fderiv ℝ f flatSym) 0 :=
    (h1.sub_const (f flatSym)).sub (fderiv ℝ f flatSym).hasFDerivAt
  rw [h2.fderiv]; simp

theorem vanishes_T1 {f : (Fin 6 → ℝ) → ℝ} (hf : AnalyticAt ℝ f flatSym) :
    VanishesToOrder (T1 f) 0 1 := by
  have hsh : AnalyticAt ℝ (fun v : Fin 6 → ℝ => fderiv ℝ f (flatSym + v)) 0 :=
    hf.fderiv.comp_of_eq (analyticAt_const.add analyticAt_id) (by simp)
  exact vanishesToOrder_one_of_differentiableAt (hsh.sub analyticAt_const).differentiableAt
    (by simp [T1])

/-- Composition with a continuous linear map at `0` keeps the vanishing order. -/
theorem vanishes_comp_clm {E E' G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup G] [NormedSpace ℝ G]
    {g : E' → G} {k : ℕ} (hg : VanishesToOrder g 0 k) (L : E →L[ℝ] E') :
    VanishesToOrder (fun u => g (L u)) 0 k := by
  unfold VanishesToOrder at *
  have ht : Tendsto L (𝓝 0) (𝓝 0) := by simpa using L.continuous.tendsto 0
  have h1 := hg.comp_tendsto ht
  simp only [sub_zero] at h1 ⊢
  refine h1.trans ?_
  have : (fun u => ‖L u‖) =O[𝓝 (0 : E)] fun u => ‖u‖ := (L.isBigO_comp _ _).norm_norm
  exact this.pow k

theorem isBigO_finsum' {α ι : Type*} [Fintype ι] {l : Filter α} {f : ι → α → ℝ} {g : α → ℝ}
    (h : ∀ i, f i =O[l] g) : (fun a => ∑ i, f i a) =O[l] g :=
  (IsBigO.sum (s := Finset.univ) fun i _ => h i).congr_left fun a => by simp [Finset.sum_apply]

/-- The scalar Leibniz defect of `f` at a site. -/
def leibS (f : (Fin 6 → ℝ) → ℝ) (c : Fin 3 → ℝ) (u : MetF N) (x : Site N) : ℝ :=
  (∑ k, c k * pd k (fun y => f (flatSym + u y)) x) - fderiv ℝ f (flatSym + u x) (dcMet c u x)

/-- The evaluation `u ↦ u y` as a continuous linear map. -/
def evalAt (y : Site N) : MetF N →L[ℝ] (Fin 6 → ℝ) := ContinuousLinearMap.proj y

/-- `u ↦ δ_c u (x)` as a continuous linear map. -/
def dcAt (c : Fin 3 → ℝ) (x : Site N) : MetF N →L[ℝ] (Fin 6 → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun u => dcMet c u x
      map_add' := fun u v => by simp [dcMet, map_add, Finset.sum_add_distrib, smul_add]
      map_smul' := fun a u => by
        simp [dcMet, map_smul, Finset.smul_sum, smul_comm a] }

theorem leibS_eq (f : (Fin 6 → ℝ) → ℝ) (c : Fin 3 → ℝ) (u : MetF N) (x : Site N) :
    leibS f c u x = (∑ k, c k * pd k (fun y => T2 f (u y)) x) - T1 f (u x) (dcMet c u x) := by
  have hsplit : ∀ k, pd k (fun y => f (flatSym + u y)) x =
      fderiv ℝ f flatSym (pd k u x) + pd k (fun y => T2 f (u y)) x := by
    intro k
    have hfun : (fun y => f (flatSym + u y)) = (fun _ => f flatSym) +
        (fun y => fderiv ℝ f flatSym (u y)) + fun y => T2 f (u y) := by
      funext y; simp [T2]
    rw [hfun, map_add, map_add, pd_const, pd_map_clm]
    simp
  simp only [leibS, hsplit, mul_add, Finset.sum_add_distrib, T1, ContinuousLinearMap.sub_apply]
  have hlin : ∑ k, c k * fderiv ℝ f flatSym (pd k u x) = fderiv ℝ f flatSym (dcMet c u x) := by
    simp [dcMet, map_sum, map_smul]
  rw [hlin]
  ring

/-- **The scalar Leibniz defect vanishes to second order** in the metric perturbation. -/
theorem vanishes_leibS {f : (Fin 6 → ℝ) → ℝ} (hf : AnalyticAt ℝ f flatSym) (c : Fin 3 → ℝ)
    (x : Site N) : VanishesToOrder (fun u : MetF N => leibS f c u x) 0 2 := by
  have h2 := vanishes_T2 hf
  have h1 := vanishes_T1 hf
  have hpd : ∀ k, VanishesToOrder (fun u : MetF N => pd k (fun y => T2 f (u y)) x) 0 2 := by
    intro k
    have : (fun u : MetF N => pd k (fun y => T2 f (u y)) x) =
        fun u => ∑ s : ZMod N, kernel N s • T2 f (evalAt (x + Pi.single k s) u) := by
      funext u; rfl
    rw [this]
    exact isBigO_finsum' fun s => by
      have := (vanishes_comp_clm h2 (evalAt (x + Pi.single k s))).map
        ((kernel N s) • ContinuousLinearMap.id ℝ ℝ)
      simpa [VanishesToOrder] using this
  have hA : VanishesToOrder (fun u : MetF N => ∑ k, c k * pd k (fun y => T2 f (u y)) x) 0 2 :=
    isBigO_finsum' fun k => by
      have := (hpd k).map ((c k) • ContinuousLinearMap.id ℝ ℝ)
      simpa [VanishesToOrder] using this
  have hB : VanishesToOrder (fun u : MetF N => T1 f (u x) (dcMet c u x)) 0 (1 + 1) :=
    (vanishes_comp_clm h1 (evalAt x)).clm_apply
      (vanishesToOrder_one_of_differentiableAt (dcAt c x).differentiableAt (map_zero (dcAt c x)))
  have hfun : (fun u : MetF N => leibS f c u x) = (fun u => ∑ k, c k * pd k (fun y => T2 f (u y)) x) +
      fun u => -(T1 f (u x) (dcMet c u x)) := by
    funext u; rw [leibS_eq]; simp only [Pi.add_apply]; ring
  rw [hfun]
  exact hA.add (by unfold VanishesToOrder at hB ⊢; exact hB.neg_left)

theorem leib_entry (χ : ℝ) (c : Fin 3 → ℝ) (u : MetF N) (i : Fin 3) (x : Site N) (K L : Fin 4) :
    leib χ c (flatMet N + u) i x K L = leibS (piEntry χ sqrtTriad i K L) c u x := by
  unfold leib dcPi leibS
  rw [dcMet_flatMet_add]
  simp only [Matrix.sub_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, pd_matrix_apply]
  rfl

theorem analyticAt_piEntry_flat (χ : ℝ) (i : Fin 3) (K L : Fin 4) :
    AnalyticAt ℝ (piEntry χ sqrtTriad i K L) flatSym := by
  have htr : AnalyticAt ℝ sqrtTriad (symMat flatSym) := by
    rw [symMat_flatSym]; exact analyticAt_sqrtTriad
  exact analyticAt_piEntry χ htr i K L

/-- **The Leibniz defect vanishes to second order** in `u = γ - I`. -/
theorem vanishes_leib (χ : ℝ) (c : Fin 3 → ℝ) (i : Fin 3) (x : Site N) :
    VanishesToOrder (fun u : MetF N => leib χ c (flatMet N + u) i x) 0 2 := by
  have he : ∀ K L, VanishesToOrder (fun u : MetF N => leib χ c (flatMet N + u) i x K L) 0 2 := by
    intro K L
    simp only [leib_entry]
    exact vanishes_leibS (analyticAt_piEntry_flat χ i K L) c x
  have hsum : (fun u : MetF N => ∑ K, ∑ L, |leib χ c (flatMet N + u) i x K L|) =O[𝓝 0]
      fun u : MetF N => ‖u - 0‖ ^ 2 :=
    isBigO_finsum' fun K => isBigO_finsum' fun L => by
      have := (he K L).norm_left
      simpa [Real.norm_eq_abs] using this
  refine IsBigO.trans ?_ hsum
  refine IsBigO.of_bound 1 (Eventually.of_forall fun u => ?_)
  rw [one_mul]
  refine (norm_le_sum_abs _).trans (le_of_eq ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]

end Leibniz

/-! ### The link-remainder part is cubic in the spatial connection -/

theorem norm_piArr_le' (χ : ℝ) (e : M4) (he : ‖e‖ ≤ 2) (i : Fin 3) :
    ‖piArr χ e i‖ ≤ 32768 * |χ| := by
  have := norm_piArr_le χ e i
  have h4 : ‖e‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg e]
  calc ‖piArr χ e i‖ ≤ 8192 * |χ| * ‖e‖ ^ 2 := this
    _ ≤ 8192 * |χ| * 4 := by gcongr
    _ = 32768 * |χ| := by ring

theorem norm_entry_le_pi (B : Fin 3 → Site N → M4) (i : Fin 3) (y : Site N) : ‖B i y‖ ≤ ‖B‖ :=
  (norm_le_pi_norm (B i) y).trans (norm_le_pi_norm B i)

theorem norm_cA_le (c : Fin 3 → ℝ) (B : Fin 3 → Site N → M4) (y : Site N) :
    ‖cA c B y‖ ≤ (∑ j, |c j|) * ‖B‖ := by
  unfold cA
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (norm_entry_le_pi B j y) (abs_nonneg _)

/-- **Cubic bound for the remainder part of the shift slope.** -/
theorem abs_vDen_le (χ : ℝ) {h : ℝ} (hh : 0 < h) (e : Site N → M4) (c : Fin 3 → ℝ)
    (B : Fin 3 → Site N → M4) (x : Site N) (he : ‖e x‖ ≤ 2) (hB : h * ‖B‖ ≤ 1 / 16) :
    |vDen χ h e c B x| ≤
      (3 * (4 * (2 * (∑ j, |c j|) * (32768 * |χ|)) * (384 * h)) +
        3 * (4 * (32768 * |χ|) * (16 * h * (∑ j, |c j|)))) * ‖B‖ ^ 3 := by
  set Cc := ∑ j, |c j|
  set Pm := 32768 * |χ|
  have hPi : ∀ i, ‖piArr χ (e x) i‖ ≤ Pm := fun i => norm_piArr_le' χ (e x) he i
  have hCc : 0 ≤ Cc := Finset.sum_nonneg fun j _ => abs_nonneg _
  have hPm : 0 ≤ Pm := by positivity
  have hBn := norm_nonneg B
  -- plaquette terms
  have hcoef : ∀ i j, ‖c j • piArr χ (e x) i - c i • piArr χ (e x) j‖ ≤ 2 * Cc * Pm := by
    intro i j
    have hci : |c i| ≤ Cc := Finset.single_le_sum (fun k _ => abs_nonneg (c k)) (Finset.mem_univ i)
    have hcj : |c j| ≤ Cc := Finset.single_le_sum (fun k _ => abs_nonneg (c k)) (Finset.mem_univ j)
    calc ‖c j • piArr χ (e x) i - c i • piArr χ (e x) j‖
        ≤ ‖c j • piArr χ (e x) i‖ + ‖c i • piArr χ (e x) j‖ := norm_sub_le _ _
      _ = |c j| * ‖piArr χ (e x) i‖ + |c i| * ‖piArr χ (e x) j‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ Cc * Pm + Cc * Pm := by gcongr <;> first | exact hPi _ | assumption
      _ = 2 * Cc * Pm := by ring
  have hplaq : ∀ i j, |pairing (c j • piArr χ (e x) i - c i • piArr χ (e x) j)
      (remB h (B i x) (B j (x + unitVec i)) (B i (x + unitVec j)) (B j x))| ≤
        4 * (2 * Cc * Pm) * (384 * h) * ‖B‖ ^ 3 := by
    intro i j
    set Y : Fin 4 → M4 := ![B i x, B j (x + unitVec i), -B i (x + unitVec j), -B j x]
    have hY : ‖Y‖ ≤ ‖B‖ := by
      refine (pi_norm_le_iff_of_nonneg hBn).2 fun ℓ => ?_
      fin_cases ℓ <;> simp [Y, norm_neg, norm_entry_le_pi]
    have hrem : ‖remB h (B i x) (B j (x + unitVec i)) (B i (x + unitVec j)) (B j x)‖ ≤
        384 * h * ‖B‖ ^ 3 := by
      rw [remB_eq_rhoB hh.ne']
      have h1 := norm_rhoB_le hh Y (le_trans (by gcongr) hB)
      exact h1.trans (by gcongr)
    calc _ ≤ 4 * (‖c j • piArr χ (e x) i - c i • piArr χ (e x) j‖ *
          ‖remB h (B i x) (B j (x + unitVec i)) (B i (x + unitVec j)) (B j x)‖) :=
          abs_pairing_le _ _
      _ ≤ 4 * ((2 * Cc * Pm) * (384 * h * ‖B‖ ^ 3)) := by gcongr; exact hcoef i j
      _ = 4 * (2 * Cc * Pm) * (384 * h) * ‖B‖ ^ 3 := by ring
  have hlink : ∀ i, |pairing (piArr χ (e x) i) (remE h (B i x) (cA c B (x + unitVec i)))| ≤
      4 * Pm * (16 * h * Cc) * ‖B‖ ^ 3 := by
    intro i
    have hBi := norm_entry_le_pi B i x
    have hrem := norm_remE_le hh (B i x) (cA c B (x + unitVec i))
      (by nlinarith [norm_nonneg (B i x)])
    have hcA := norm_cA_le c B (x + unitVec i)
    calc _ ≤ 4 * (‖piArr χ (e x) i‖ * ‖remE h (B i x) (cA c B (x + unitVec i))‖) :=
          abs_pairing_le _ _
      _ ≤ 4 * (Pm * (16 * h * ‖B‖ ^ 2 * (Cc * ‖B‖))) := by
          gcongr
          · exact hPi i
          · exact hrem.trans (by gcongr)
      _ = 4 * Pm * (16 * h * Cc) * ‖B‖ ^ 3 := by ring
  unfold vDen
  rw [sumLt_eq]
  have hsum := Finset.abs_sum_le_sum_abs (fun i => pairing (piArr χ (e x) i)
    (remE h (B i x) (cA c B (x + unitVec i)))) Finset.univ
  simp only [Fin.sum_univ_three] at hsum ⊢
  have := hplaq 0 1; have := hplaq 0 2; have := hplaq 1 2
  have := hlink 0; have := hlink 1; have := hlink 2
  have hB3 : 0 ≤ ‖B‖ ^ 3 := by positivity
  rw [abs_le]
  constructor <;> nlinarith [abs_le.1 (hplaq 0 1), abs_le.1 (hplaq 0 2), abs_le.1 (hplaq 1 2),
    abs_le.1 (hlink 0), abs_le.1 (hlink 1), abs_le.1 (hlink 2)]

/-! ### The cubic order of `Q_c` -/

/-- The spatial part `(0, A_i)` of a connection, as a continuous linear map on `Conn N`. -/
def spatialCLM : Conn N →L[ℝ] Conn N :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A x μ => Fin.cases (motive := fun _ => Fin 6 → ℝ) 0 (fun i => A x i.succ) μ
      map_add' := fun A B => by
        funext x μ; cases μ using Fin.cases <;> simp
      map_smul' := fun c A => by
        funext x μ; cases μ using Fin.cases <;> simp }

theorem spatialCLM_succ (A : Conn N) (x : Site N) (i : Fin 3) :
    spatialCLM A x i.succ = A x i.succ := rfl

theorem spatialCLM_eq_zero_of_toA {A : Conn N} (h : toA A = 0) : spatialCLM A = 0 := by
  funext x μ
  cases μ using Fin.cases with
  | zero => rfl
  | succ i =>
    rw [spatialCLM_succ]
    have h1 : iota (A x i.succ) = 0 := congrFun (congrFun h i) x
    have := congrArg coord h1
    rwa [coord_iota, show (0 : M4) = iota 0 from iota_zero.symm, coord_iota] at this

theorem norm_toA_le (A : Conn N) (i : Fin 3) (x : Site N) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ c, ‖iota c‖ ≤ C * ‖c‖) : ‖toA A i x‖ ≤ C * ‖spatialCLM A‖ := by
  have h1 : ‖A x i.succ‖ ≤ ‖spatialCLM A‖ := by
    show ‖spatialCLM A x i.succ‖ ≤ _
    exact (norm_le_pi_norm (spatialCLM A x) i.succ).trans (norm_le_pi_norm (spatialCLM A) x)
  exact (hC _).trans (mul_le_mul_of_nonneg_left h1 hC0)

theorem norm_toA_pi_le (A : Conn N) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ c, ‖iota c‖ ≤ C * ‖c‖) :
    ‖toA A‖ ≤ C * ‖spatialCLM A‖ :=
  (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i =>
    (pi_norm_le_iff_of_nonneg (by positivity)).2 fun x => norm_toA_le A i x hC0 hC

theorem embX_zero (lam : Lam N) : embX ((0 : Xs N), lam) = ((flatCfg lam).1, 0) := by
  simp [embX, flatCfg]

section Chart

variable {χ R : ℝ} {U : Set (CoP N)} (hU : FlatChart χ R U) (hχ : χ ≠ 0)
include hU hχ

/-- The chart of the stationary data `z ↦ ((γ, N, β), V_h)` is analytic at the base point and
takes the value `zFlat`. -/
theorem analyticAt_Ychart :
    AnalyticAt ℝ (fun z : Xs N × Lam N => ((embX z).1, Vh χ R z)) (pE N) ∧
      ((embX (pE N)).1, Vh χ R (pE N)) = zFlat N := by
  have hc := legendreChart_flat hU hχ
  have hπ₀ : pairCov (0 : MetF N) = velMom (redLagr χ 0 sqrtTriad (statAst χ R)) (zFlat N) := by
    rw [velMom_flat hU hχ, map_zero]
  obtain ⟨hV0, hVan, -, -, -⟩ := canonical_legendre χ 0 hc hπ₀
  have hemb : AnalyticAt ℝ (embX (N := N)) (pE N) := by
    have h : (embX (N := N)) = fun z => (((flatMet N, 0, 0), 0) : ParF N × MetF N) + embL z :=
      funext embX_eq
    rw [h]; exact analyticAt_const.add ((embL (N := N)).analyticAt (pE N))
  have hVan' : AnalyticAt ℝ (fun q : ParF N × MetF N =>
      legendreVel χ 0 sqrtTriad (statAst χ R) (zFlat N) q.1 q.2) (embX (pE N)) := by
    rw [embX_pE]; exact hVan
  refine ⟨(analyticAt_fst.comp hemb).prod (hVan'.comp hemb), ?_⟩
  simp only [Vh, embX_pE]
  exact Prod.ext rfl hV0

theorem analyticAt_Astar : AnalyticAt ℝ (Astar χ R) (pE N) := by
  obtain ⟨hY, hY0⟩ := analyticAt_Ychart hU hχ
  have hS := analyticAt_Sfun hU
  rw [← hY0] at hS
  exact AnalyticAt.comp (g := Sfun χ R) (f := fun z : Xs N × Lam N => ((embX z).1, Vh χ R z))
    hS hY

/-- **The spatial stationary connection is `O(‖X‖)`** uniformly in the multipliers: it vanishes
on the whole flat slice (`flat_slice`). -/
theorem spatial_Astar_bound :
    ∃ C, 0 ≤ C ∧ ∀ᶠ z in 𝓝 (pE N), ‖spatialCLM (Astar χ R z)‖ ≤ C * ‖z.1‖ := by
  set G : Xs N × Lam N → Conn N := fun z => spatialCLM (Astar χ R z) with hG
  have hGa : AnalyticAt ℝ G (pE N) :=
    AnalyticAt.comp (g := ⇑(spatialCLM (N := N))) (f := Astar χ R)
      ((spatialCLM (N := N)).analyticAt (𝕜 := ℝ) (Astar χ R (pE N))) (analyticAt_Astar hU hχ)
  set C := ‖fderiv ℝ G (pE N)‖ + 1 with hC
  have hC0 : 0 ≤ C := by positivity
  have hd : ∀ᶠ z in 𝓝 ((0 : Xs N), lamE N), DifferentiableAt ℝ G z :=
    hGa.eventually_analyticAt.mono fun z hz => hz.differentiableAt
  have hbound : ∀ᶠ z in 𝓝 ((0 : Xs N), lamE N),
      ‖(fderiv ℝ G z).comp (ContinuousLinearMap.inl ℝ (Xs N) (Lam N))‖ ≤ C * ‖z.1‖ ^ 0 := by
    have hcont : ContinuousAt (fun z => ‖fderiv ℝ G z‖) (pE N) :=
      continuous_norm.continuousAt.comp hGa.fderiv.continuousAt
    filter_upwards [hcont.eventually (gt_mem_nhds (lt_add_one ‖fderiv ℝ G (pE N)‖))] with z hz
    rw [pow_zero, mul_one]
    calc ‖(fderiv ℝ G z).comp (ContinuousLinearMap.inl ℝ (Xs N) (Lam N))‖
        ≤ ‖fderiv ℝ G z‖ * ‖ContinuousLinearMap.inl ℝ (Xs N) (Lam N)‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖fderiv ℝ G z‖ * 1 := by gcongr; exact ContinuousLinearMap.norm_inl_le_one ℝ _ _
      _ ≤ C := by rw [mul_one]; exact hz.le
  have hslice : ∀ᶠ lam in 𝓝 (lamE N), G (0, lam) = 0 := by
    filter_upwards [flat_slice hU hχ] with lam h
    show spatialCLM (Sfun χ R ((embX ((0 : Xs N), lam)).1, Vh χ R ((0 : Xs N), lam))) = 0
    unfold Vh
    rw [embX_zero]
    exact spatialCLM_eq_zero_of_toA h.2.2
  have := HarmonicQuartic.norm_le_of_slice hC0 hd hbound hslice
  refine ⟨C, hC0, ?_⟩
  simp only [zero_add, pow_one] at this
  exact this

/-- **`Q_c = O(‖X‖³)` uniformly in the multipliers.** -/
theorem Qrow_isBigO (c : Fin 3 → ℝ) :
    ∃ C, ∀ᶠ z in 𝓝 (pE N), ‖Qrow χ R c z‖ ≤ C * ‖z.1‖ ^ 3 := by
  obtain ⟨CA, hCA0, hCA⟩ := spatial_Astar_bound hU hχ
  obtain ⟨Cι, hCι1, hCι⟩ := exists_iota_bound
  have hCι0 : 0 ≤ Cι := by linarith
  have hh := hN_pos (N := N)
  have hz11 : Tendsto (fun z : Xs N × Lam N => z.1.1) (𝓝 (pE N)) (𝓝 0) := by
    have hc : Continuous fun z : Xs N × Lam N => z.1.1 := continuous_fst.comp continuous_fst
    have := hc.continuousAt (x := pE N)
    simpa [pE] using this.tendsto
  have hn11 : (fun z : Xs N × Lam N => ‖z.1.1‖) =O[𝓝 (pE N)] fun z => ‖z.1‖ :=
    IsBigO.of_bound 1 (Eventually.of_forall fun z => by
      simp only [norm_norm, one_mul]; exact norm_fst_le z.1)
  have hAO : (fun z : Xs N × Lam N => toA (Astar χ R z)) =O[𝓝 (pE N)] fun z => ‖z.1‖ :=
    IsBigO.of_bound (Cι * CA) (hCA.mono fun z hz => by
      rw [norm_norm]
      calc ‖toA (Astar χ R z)‖ ≤ Cι * ‖spatialCLM (Astar χ R z)‖ :=
            norm_toA_pi_le _ hCι0 hCι
        _ ≤ Cι * (CA * ‖z.1‖) := by gcongr
        _ = Cι * CA * ‖z.1‖ := by ring)
  -- the Leibniz term
  have hLeib : ∀ i x, (fun z : Xs N × Lam N => leib χ c (flatMet N + z.1.1) i x) =O[𝓝 (pE N)]
      fun z => ‖z.1‖ ^ 2 := by
    intro i x
    have h1 := (vanishes_leib χ c i x).comp_tendsto hz11
    simp only [sub_zero] at h1
    exact h1.trans (hn11.pow 2)
  have hT1 : (fun z => gridPair (hN N) (fun x => ∑ i, pairing (leib χ c (flatMet N + z.1.1) i x)
      (toA (Astar χ R z) i x))) =O[𝓝 (pE N)] fun z : Xs N × Lam N => ‖z.1‖ ^ 3 := by
    unfold gridPair
    refine IsBigO.const_mul_left ?_ _
    refine isBigO_finsum' fun x => isBigO_finsum' fun i => ?_
    have hAi : (fun z : Xs N × Lam N => toA (Astar χ R z) i x) =O[𝓝 (pE N)] fun z => ‖z.1‖ :=
      (IsBigO.of_bound 1 (Eventually.of_forall fun z => by
        rw [one_mul]; exact norm_entry_le_pi _ i x)).trans hAO
    have hprod : (fun z : Xs N × Lam N => pairing (leib χ c (flatMet N + z.1.1) i x)
        (toA (Astar χ R z) i x)) =O[𝓝 (pE N)] fun z =>
          ‖leib χ c (flatMet N + z.1.1) i x‖ * ‖toA (Astar χ R z) i x‖ :=
      IsBigO.of_bound 4 (Eventually.of_forall fun z => by
        have hn : ‖‖leib χ c (flatMet N + z.1.1) i x‖ * ‖toA (Astar χ R z) i x‖‖ =
            ‖leib χ c (flatMet N + z.1.1) i x‖ * ‖toA (Astar χ R z) i x‖ :=
          Real.norm_of_nonneg (by positivity)
        rw [hn, Real.norm_eq_abs]
        have := abs_pairing_le (leib χ c (flatMet N + z.1.1) i x) (toA (Astar χ R z) i x)
        linarith)
    refine hprod.trans ?_
    have := (hLeib i x).norm_left.mul hAi.norm_left
    refine this.trans (IsBigO.of_bound 1 (Eventually.of_forall fun z => ?_))
    rw [one_mul, Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
    ring_nf; rfl
  -- the remainder term
  have hY := analyticAt_Ychart hU hχ
  have he2 : ∀ᶠ z in 𝓝 (pE N), ∀ x, ‖coframeField sqrtTriad (embX z).1 x‖ ≤ 2 := by
    rw [Filter.eventually_all]
    intro x
    have hcont : ContinuousAt (fun z : Xs N × Lam N =>
        ‖(dataMap χ ((embX z).1, Vh χ R z)).1 x‖) (pE N) := by
      have h1 : ContinuousAt (fun y : ParF N × MetF N => ‖(dataMap χ y).1 x‖) (zFlat N) :=
        continuous_norm.continuousAt.comp
          (analyticAt_pi_apply (analyticAt_fst.comp (analyticAt_dataMap (N := N) χ)) x).continuousAt
      rw [← hY.2] at h1
      exact ContinuousAt.comp (g := fun y : ParF N × MetF N => ‖(dataMap χ y).1 x‖)
        (f := fun z : Xs N × Lam N => ((embX z).1, Vh χ R z)) h1 hY.1.continuousAt
    have h0 : (fun z : Xs N × Lam N => ‖(dataMap χ ((embX z).1, Vh χ R z)).1 x‖) (pE N) < 2 := by
      simp only
      rw [hY.2, dataMap_flat]; simp
    filter_upwards [hcont.eventually (gt_mem_nhds h0)] with z hz
    exact hz.le
  have hBsmall : ∀ᶠ z in 𝓝 (pE N), hN N * ‖toA (Astar χ R z)‖ ≤ 1 / 16 := by
    have hlin : ∀ᶠ z in 𝓝 (pE N), hN N * ‖toA (Astar χ R z)‖ ≤ hN N * (Cι * (CA * ‖z.1‖)) := by
      filter_upwards [hCA] with z hz
      gcongr
      exact (norm_toA_pi_le _ hCι0 hCι).trans (by gcongr)
    have hcont : ContinuousAt (fun z : Xs N × Lam N => hN N * (Cι * (CA * ‖z.1‖))) (pE N) := by
      fun_prop
    have h0 : (fun z : Xs N × Lam N => hN N * (Cι * (CA * ‖z.1‖))) (pE N) < 1 / 16 := by
      simp [pE]
    filter_upwards [hlin, hcont.eventually (gt_mem_nhds h0)] with z h1 h2
    exact h1.trans h2.le
  have hT2 : (fun z => gridPair (hN N) (vDen χ (hN N) (coframeField sqrtTriad (embX z).1) c
      (toA (Astar χ R z)))) =O[𝓝 (pE N)] fun z : Xs N × Lam N => ‖z.1‖ ^ 3 := by
    unfold gridPair
    refine IsBigO.const_mul_left ?_ _
    refine isBigO_finsum' fun x => ?_
    set K := (3 * (4 * (2 * (∑ j, |c j|) * (32768 * |χ|)) * (384 * hN N)) +
        3 * (4 * (32768 * |χ|) * (16 * hN N * (∑ j, |c j|))))
    have h1 : (fun z => vDen χ (hN N) (coframeField sqrtTriad (embX z).1) c (toA (Astar χ R z)) x)
        =O[𝓝 (pE N)] fun z : Xs N × Lam N => ‖toA (Astar χ R z)‖ ^ 3 :=
      IsBigO.of_bound K (by
        filter_upwards [he2, hBsmall] with z hz hb
        rw [Real.norm_eq_abs, Real.norm_of_nonneg (by positivity)]
        exact abs_vDen_le χ hh _ c _ x (hz x) hb)
    refine h1.trans ?_
    have := hAO.norm_left.pow 3
    simpa using this
  obtain ⟨C, hC⟩ := (hT1.neg_left.sub hT2).bound
  refine ⟨C, ?_⟩
  filter_upwards [hC] with z hz
  have h3 : ‖‖z.1‖ ^ 3‖ = ‖z.1‖ ^ 3 := Real.norm_of_nonneg (by positivity)
  rw [h3] at hz
  exact hz

end Chart

end RenewalGeometry.ExactPhaseAction.ShiftWard
