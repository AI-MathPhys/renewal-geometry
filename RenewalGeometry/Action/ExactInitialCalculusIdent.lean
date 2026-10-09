/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Action.ExactInitialCalculusMain

/-!
# The uniform constraint map is the original-action constraint map `Cmap`
  (`lem:supp-initial-calculus`, `eq:main-action-initial-constraints`; emergent-spacetime manuscript)

For each fixed odd `N` with `h` below the threshold, near `X = 0` the map `CHmap` of
`ExactInitialCalculusMain.lean` (the four rows at the uniform joint solution) coincides with the
initial constraint map `Cmap` of the actual canonical Hamiltonian
(`QuadJet.Cmap = initialConstraint` of `ExactLegendreHamiltonian.lean`, built from the analytic
Legendre inverse of the reduced Lagrangian at flat data):

* `encZ`, `decX`, `encY`: the encodings between the Lean field types and the grid Sobolev arrays.
* `eventually_legLoc_zero`: the analytic Legendre velocity `V_h` solves the site-wise Legendre row
  (envelope identity + `fderiv_PhiL_velocity`).
* `eventually_Cmap_eq`: `𝒞_h(X)(x) = (conLoc(Σ(e(x)), 𝒜_h)(x), -conLoc(e_a,j Π_i - e_a,i Π_j, 𝒜_h)(x))`
  near `X = 0` (`initialConstraint_eq`, envelope identity, `fderiv_PhiL_lapse/shift`).
* **`eventually_CHmap_eq_Cmap`**: `CHmap = encY ∘ Cmap ∘ decX` near `X = 0`.
-/

open Filter Finset Metric Set
open scoped Topology

noncomputable section

namespace RenewalGeometry.ExactPhaseAction.InitialCalculus

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

set_option linter.unusedSectionVars false

open QuadJet PeriodicGridSobolev GridLocalOps IteratedDerivBounds UniformDerivBounds
open UniformImplicit LocalSumGradient

variable {N : ℕ} [NeZero N]

/-! ### Encodings -/

/-- Encoding of a connection and a velocity as unknowns. -/
def encZ (r : ℕ) (A : Conn N) (V : MetF N) : ZH N r :=
  fun m => Sum.elim (fun mk : Fin 4 × Fin 6 => GridH.mk (fun x => A x mk.1 mk.2))
    (fun c => GridH.mk (fun x => V x c)) m

theorem connOfZ_encZ (r : ℕ) (A : Conn N) (V : MetF N) : connOfZ (encZ r A V) = A := rfl

theorem velOfZ_encZ (r : ℕ) (A : Conn N) (V : MetF N) : velOfZ (encZ r A V) = V := rfl

/-- The encoding of unknowns as a continuous linear map. -/
def encZL (r : ℕ) : Conn N × MetF N →L[ℝ] ZH N r :=
  LinearMap.toContinuousLinearMap
    { toFun := fun p => encZ r p.1 p.2
      map_add' := fun p p' => by
        funext m; rcases m with ⟨μ, k⟩ | c <;> exact GridH.ext fun x => rfl
      map_smul' := fun t p => by
        funext m; rcases m with ⟨μ, k⟩ | c <;> exact GridH.ext fun x => rfl }

@[simp] theorem encZL_apply (r : ℕ) (p : Conn N × MetF N) : encZL r p = encZ r p.1 p.2 := rfl

/-- Decoding of the data `X = (u, π)` as metric fields. -/
def decX {r : ℕ} (X : XH N r) : MetF N × MetF N := (metOf X.1, metOf X.2)

/-- The data decoding as a continuous linear map. -/
def decXL (r : ℕ) : XH N r →L[ℝ] MetF N × MetF N :=
  LinearMap.toContinuousLinearMap
    { toFun := decX
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

@[simp] theorem decXL_apply (r : ℕ) (X : XH N r) : decXL r X = decX X := rfl

/-- Encoding of the four rows. -/
def encY (r : ℕ) (C : (Site N → ℝ) × (Site N → Fin 3 → ℝ)) : Fin 4 → GridH N r :=
  fun row => Fin.cases (GridH.mk C.1) (fun a => GridH.mk (fun x => C.2 x a)) row

/-- The encoding of the four rows as a continuous linear map. -/
def encYL (r : ℕ) : (Site N → ℝ) × (Site N → Fin 3 → ℝ) →L[ℝ] (Fin 4 → GridH N r) :=
  LinearMap.toContinuousLinearMap
    { toFun := encY r
      map_add' := fun C C' => by
        funext row; cases row using Fin.cases <;> exact GridH.ext fun x => rfl
      map_smul' := fun t C => by
        funext row; cases row using Fin.cases <;> exact GridH.ext fun x => rfl }

@[simp] theorem encYL_apply (r : ℕ) (C : (Site N → ℝ) × (Site N → Fin 3 → ℝ)) :
    encYL r C = encY r C := rfl

/-! ### The data along the analytic Legendre velocity -/

theorem continuousAt_momData (r : ℕ) :
    ContinuousAt (fun X : XH N r => ((refMult (flatMet N + metOf X.1), metOf X.2) :
      ParF N × MetF N)) 0 := by
  have h : (fun X : XH N r => ((refMult (flatMet N + metOf X.1), metOf X.2) : ParF N × MetF N)) =
      fun X => ((zFlat N).1, (0 : MetF N)) + ((((decXL r X).1, 0, 0), (decXL r X).2) :
        ParF N × MetF N) := by
    funext X; ext <;> simp [refMult, zFlat, decX]
  rw [h]
  refine continuousAt_const.add ?_
  have hc : Continuous (decXL (N := N) r) := (decXL r).continuous
  exact ((continuous_fst.comp hc).prodMk (continuous_const.prodMk continuous_const)).prodMk
    (continuous_snd.comp hc) |>.continuousAt

theorem momData_zero (r : ℕ) :
    ((refMult (flatMet N + metOf (0 : XH N r).1), metOf (0 : XH N r).2) : ParF N × MetF N) =
      ((zFlat N).1, 0) := by
  ext <;> simp [refMult, zFlat, metOf_zero]

section Chart

variable {χ R : ℝ} {U : Set (CoP N)} (hU : FlatChart χ R U) (hχ : χ ≠ 0)
include hU hχ

/-- The analytic Legendre velocity of the data `X`. -/
def psiV (χ R : ℝ) {r : ℕ} (X : XH N r) : MetF N :=
  legendreVel χ 0 sqrtTriad (statAst χ R) (zFlat N) (refMult (flatMet N + metOf X.1)) (metOf X.2)

/-- The configuration `(γ, V_h, 1, 0)` of the data `X`. -/
def zOf (χ R : ℝ) {r : ℕ} (X : XH N r) : ParF N × MetF N :=
  (refMult (flatMet N + metOf X.1), psiV χ R X)

theorem hπflat : pairCov (0 : MetF N) = velMom (redLagr χ 0 sqrtTriad (statAst χ R)) (zFlat N) := by
  rw [velMom_flat hU hχ, map_zero]

theorem continuousAt_psiV (r : ℕ) : ContinuousAt (fun X : XH N r => psiV χ R X) 0 := by
  have hL := canonical_legendre χ 0 (legendreChart_flat hU hχ) (hπflat hU hχ)
  have h1 := hL.2.1.continuousAt
  have h2 := continuousAt_momData (N := N) r
  exact ContinuousAt.comp_of_eq (g := fun q : ParF N × MetF N =>
    legendreVel χ 0 sqrtTriad (statAst χ R) (zFlat N) q.1 q.2) h1 h2 (momData_zero r)

theorem psiV_zero (r : ℕ) : psiV χ R (0 : XH N r) = 0 := by
  have hL := canonical_legendre χ 0 (legendreChart_flat hU hχ) (hπflat hU hχ)
  have h := hL.1
  simp only [psiV, Prod.fst_zero, Prod.snd_zero, metOf_zero, add_zero]
  exact h

theorem continuousAt_zOf (r : ℕ) : ContinuousAt (fun X : XH N r => zOf χ R X) 0 := by
  have h1 : ContinuousAt (fun X : XH N r => refMult (flatMet N + metOf X.1)) 0 :=
    continuous_fst.continuousAt.comp (continuousAt_momData (N := N) r)
  exact h1.prodMk (continuousAt_psiV hU hχ r)

theorem zOf_zero (r : ℕ) : zOf χ R (0 : XH N r) = zFlat N := by
  simp only [zOf, psiV_zero hU hχ r]
  ext <;> simp [refMult, zFlat, metOf_zero]

theorem tendsto_zOf (r : ℕ) : Tendsto (fun X : XH N r => zOf χ R X) (𝓝 0) (𝓝 (zFlat N)) := by
  have := (continuousAt_zOf hU hχ r).tendsto
  rwa [zOf_zero hU hχ r] at this

/-- The stationary connection along the data. -/
theorem tendsto_Sfun_zOf (r : ℕ) :
    Tendsto (fun X : XH N r => Sfun χ R (zOf χ R X)) (𝓝 0) (𝓝 0) := by
  have h := (analyticAt_Sfun hU).continuousAt.tendsto.comp (tendsto_zOf hU hχ r)
  rwa [Sfun_flat hU] at h

end Chart

/-! ### The constraint rows of `Cmap` along the data -/

section Chart2

variable {χ R : ℝ} {U : Set (CoP N)} (hU : FlatChart χ R U) (hχ : χ ≠ 0)
include hU hχ

theorem tendsto_pair_zOf (r : ℕ) : Tendsto (fun X : XH N r => (zOf χ R X, Sfun χ R (zOf χ R X)))
    (𝓝 0) (𝓝 (zFlat N, (0 : Conn N))) :=
  (tendsto_zOf hU hχ r).prodMk_nhds (tendsto_Sfun_zOf hU hχ r)

theorem eventually_differentiableAt_PhiL (r : ℕ) : ∀ᶠ X in 𝓝 (0 : XH N r),
    DifferentiableAt ℝ (PhiL χ) (zOf χ R X, Sfun χ R (zOf χ R X)) :=
  (tendsto_pair_zOf hU hχ r).eventually ((analyticAt_PhiL χ).eventually_analyticAt.mono
    fun _ h => h.differentiableAt)

theorem eventually_fderiv_redLagr_zOf (r : ℕ) : ∀ᶠ X in 𝓝 (0 : XH N r), ∀ w,
    fderiv ℝ (redLagr χ 0 sqrtTriad (statAst χ R)) (zOf χ R X) w =
      fderiv ℝ (PhiL χ) (zOf χ R X, Sfun χ R (zOf χ R X)) (w, 0) :=
  (tendsto_zOf hU hχ r).eventually (eventually_fderiv_redLagr hU)

/-- **`𝒞_h` along the data** (`initialConstraint_eq` + envelope identity + lapse/shift
partials): `𝒞_h(X)(x) = (conLoc(Σ(e(x)), 𝒜_h)(x), -conLoc(e_a,j Π_i - e_a,i Π_j, 𝒜_h)(x))`. -/
theorem eventually_Cmap_eq (r : ℕ) : ∀ᶠ X in 𝓝 (0 : XH N r),
    Cmap χ R (decX X) =
      (fun x => conLoc (hN N) (sigmaArr χ (e0 (flatMet N + metOf X.1) x)) (Sfun χ R (zOf χ R X)) x,
       fun x a => -conLoc (hN N) (sigS χ (e0 (flatMet N + metOf X.1) x) a)
         (Sfun χ R (zOf χ R X)) x) := by
  have hc := legendreChart_flat hU hχ
  have hIC := initialConstraint_eq χ 0 hc ((flatMet N, 0) : MetF N × MetF N) rfl (hπflat hU hχ)
  have hT : Tendsto (fun X : XH N r => ((flatMet N + metOf X.1, metOf X.2) : MetF N × MetF N))
      (𝓝 0) (𝓝 (flatMet N, 0)) := by
    have hcont : Continuous (fun X : XH N r => ((flatMet N + metOf X.1, metOf X.2) :
        MetF N × MetF N)) := by
      have : (fun X : XH N r => ((flatMet N + metOf X.1, metOf X.2) : MetF N × MetF N)) =
          fun X => ((flatMet N, 0) : MetF N × MetF N) + decXL r X := by
        funext X; ext <;> simp [decX]
      rw [this]; exact continuous_const.add (decXL r).continuous
    have := hcont.tendsto 0
    simpa [metOf_zero] using this
  filter_upwards [hT.eventually hIC, eventually_fderiv_redLagr_zOf hU hχ r,
    eventually_differentiableAt_PhiL hU hχ r] with X hX hF hd
  have hh3 : hN N ^ 3 ≠ 0 := pow_ne_zero 3 hN_ne_zero
  have hCm : Cmap χ R (decX X) = initialConstraint χ 0 sqrtTriad (statAst χ R) (zFlat N)
      (flatMet N + metOf X.1, metOf X.2) := rfl
  rw [hCm, hX]
  have hz : ((refMult (flatMet N + metOf X.1), legendreVel χ 0 sqrtTriad (statAst χ R) (zFlat N)
      (refMult (flatMet N + metOf X.1)) (metOf X.2)) : ParF N × MetF N) = zOf χ R X := rfl
  have hz' : zOf χ R X = (refMult (flatMet N + metOf X.1), psiV χ R X) := rfl
  have hd' : DifferentiableAt ℝ (PhiL χ) ((refMult (flatMet N + metOf X.1), psiV χ R X),
      Sfun χ R (zOf χ R X)) := hd
  refine Prod.ext (funext fun x => ?_) (funext fun x => funext fun a => ?_)
  · simp only []
    rw [hz, hF]
    have := fderiv_PhiL_lapse χ hd' x
    rw [← hz'] at this
    rw [this, ← mul_assoc, inv_mul_cancel₀ hh3, one_mul]
  · simp only []
    rw [hz, hF]
    have := fderiv_PhiL_shift χ hd' x a
    rw [← hz'] at this
    rw [this, ← mul_assoc, inv_mul_cancel₀ hh3, one_mul]
    rfl

/-- **The analytic Legendre velocity solves the site-wise Legendre row** near `X = 0`. -/
theorem eventually_legLoc_zero (r : ℕ) : ∀ᶠ X in 𝓝 (0 : XH N r), ∀ (x : Site N) (c : Fin 6),
    legLoc χ (metOf X.1 x) (metOf X.2 x) (Sfun χ R (zOf χ R X) x) c = 0 := by
  have hL := canonical_legendre χ 0 (legendreChart_flat hU hχ) (hπflat hU hχ)
  have hT : Tendsto (fun X : XH N r => ((refMult (flatMet N + metOf X.1), metOf X.2) :
      ParF N × MetF N)) (𝓝 0) (𝓝 ((zFlat N).1, 0)) := by
    have := (continuousAt_momData (N := N) r).tendsto
    rwa [momData_zero] at this
  filter_upwards [hT.eventually hL.2.2.1, eventually_fderiv_redLagr_zOf hU hχ r,
    eventually_differentiableAt_PhiL hU hχ r] with X hX hF hd x c
  set V : MetF N := Pi.single x (Pi.single c (1 : ℝ))
  have h1 := hX V
  -- the momentum side
  have hpair : pairH (metOf X.2) V = hN N ^ 3 * frob (metOf X.2 x) (Pi.single c 1) := by
    unfold pairH
    congr 1
    rw [Finset.sum_eq_single x]
    · simp [V, frob]
    · intro y _ hy
      simp [V, hy, symMat]
    · simp
  -- the velocity side
  have hvel : velMom (redLagr χ 0 sqrtTriad (statAst χ R))
      ((refMult (flatMet N + metOf X.1)), legendreVel χ 0 sqrtTriad (statAst χ R) (zFlat N)
        (refMult (flatMet N + metOf X.1)) (metOf X.2)) V =
      -(hN N ^ 3 * ∑ i, pairing (PdLoc χ (metOf X.1 x) (Pi.single c 1) i)
        (toA (Sfun χ R (zOf χ R X)) i x)) := by
    have e1 : velMom (redLagr χ 0 sqrtTriad (statAst χ R)) (zOf χ R X) V =
        fderiv ℝ (redLagr χ 0 sqrtTriad (statAst χ R)) (zOf χ R X) ((0 : ParF N), V) := rfl
    change velMom (redLagr χ 0 sqrtTriad (statAst χ R)) (zOf χ R X) V = _
    rw [e1, hF, fderiv_PhiL_velocity χ hd V]
    congr 2
    rw [Finset.sum_eq_single x]
    · refine Finset.sum_congr rfl fun i _ => ?_
      have hVx : V x = Pi.single c 1 := by simp [V]
      show pairing (PdLoc χ (metOf X.1 x) (V x) i) _ = _
      rw [hVx]
    · intro y _ hy
      have hVy : V y = 0 := by simp [V, hy]
      refine Finset.sum_eq_zero fun i _ => ?_
      have : piDot χ sqrtTriad (zOf χ R X).1.1 V i y = 0 := by
        show PdLoc χ (metOf X.1 y) (V y) i = 0
        rw [hVy, PdLoc_zero_right]
      rw [this, pairing_zero_left]
    · simp
  rw [hvel, hpair] at h1
  have hh3 : 0 < hN N ^ 3 := pow_pos hN_pos 3
  unfold legLoc
  have h2 : hN N ^ 3 * (frob (metOf X.2 x) (Pi.single c 1) + ∑ i, pairing
      (PdLoc χ (metOf X.1 x) (Pi.single c 1) i) (toA (Sfun χ R (zOf χ R X)) i x)) = 0 := by
    linarith
  have h3 := (mul_eq_zero.mp h2).resolve_left hh3.ne'
  exact h3

end Chart2

/-! ### Identification of the uniform solution and of the constraint map -/

/-- **The uniform joint solution is the stationary connection and the analytic Legendre
velocity** near `X = 0`. -/
theorem exists_eventually_imp_eq : ∃ δ > 0, ∀ (N : ℕ) [NeZero N] (hNo : Odd N) {χ R : ℝ}
    {U : Set (CoP N)} (hU : FlatChart χ R U) (hχ : χ ≠ 0) (r K : ℕ) {M a ρ : ℝ}
    (h : Hyp (FH hNo χ r) (TH hχ r) K M a ρ), hN N < δ →
      ∀ᶠ X in 𝓝 (0 : XH N r),
        imp (FH hNo χ r) M a ρ X = encZ r (Sfun χ R (zOf χ R X)) (psiV χ R X) := by
  obtain ⟨δ₁, hδ₁, hval⟩ := exists_FH_inl_val
  obtain ⟨ε₀, hε₀, hrow⟩ := exists_statRow_eq
  refine ⟨δ₁, hδ₁, fun N _ hNo χ R U hU hχ r K M a ρ h hh => ?_⟩
  have hA := tendsto_Sfun_zOf hU hχ r
  have hψ : Tendsto (fun X : XH N r => psiV χ R X) (𝓝 0) (𝓝 0) := by
    have := (continuousAt_psiV hU hχ r).tendsto
    rwa [psiV_zero hU hχ r] at this
  have hZ : Tendsto (fun X : XH N r => encZ r (Sfun χ R (zOf χ R X)) (psiV χ R X)) (𝓝 0) (𝓝 0) := by
    have := ((encZL (N := N) r).continuous.tendsto (0, 0)).comp (hA.prodMk_nhds hψ)
    have h00 : encZL (N := N) r ((0 : Conn N), (0 : MetF N)) = 0 := by
      funext m; rcases m with ⟨μ, k⟩ | c <;> rfl
    rw [h00] at this
    exact this
  have E1 : ∀ᶠ X in 𝓝 (0 : XH N r), ‖X‖ < del M a ρ := by
    filter_upwards [Metric.ball_mem_nhds (0 : XH N r) h.del_pos] with X hX
    simpa using hX
  have E2 : ∀ᶠ X in 𝓝 (0 : XH N r), ‖encZ r (Sfun χ R (zOf χ R X)) (psiV χ R X)‖ < sig M a ρ :=
    hZ.eventually (by
      filter_upwards [Metric.ball_mem_nhds (0 : ZH N r) h.sig_pos] with z hz
      simpa using hz)
  have E3 : ∀ᶠ X in 𝓝 (0 : XH N r), ‖Sfun χ R (zOf χ R X)‖ < δ₁ :=
    hA.eventually (by
      filter_upwards [Metric.ball_mem_nhds (0 : Conn N) hδ₁] with A hA'
      simpa using hA')
  have E4 : ∀ᶠ X in 𝓝 (0 : XH N r), hN N * ‖Sfun χ R (zOf χ R X)‖ ≤ ε₀ := by
    have hpos := hN_pos (N := N)
    have hb : 0 < ε₀ / hN N := div_pos hε₀ hpos
    filter_upwards [hA.eventually (Metric.ball_mem_nhds (0 : Conn N) hb)] with X hX
    rw [dist_zero_right, lt_div_iff₀ hpos] at hX
    linarith
  have E5 := (tendsto_zOf hU hχ r).eventually (eventually_stationary hU)
  have E6 := eventually_legLoc_zero hU hχ r
  filter_upwards [E1, E2, E3, E4, E5, E6] with X h1 h2 h3 h4 h5 h6
  refine (h.imp_unique h1 h2.le ?_).symm
  funext m
  refine GridH.ext fun x => ?_
  rcases m with ⟨μ, k⟩ | c
  · rw [hval N hNo χ r (X, encZ r (Sfun χ R (zOf χ R X)) (psiV χ R X)) hh
      (by rw [connOfZ_encZ]; exact h3)]
    simp only [connOfZ_encZ, velOfZ_encZ]
    have hr := hrow N χ 0 (dataMap χ (zOf χ R X)).1 (dataMap χ (zOf χ R X)).2
      (Sfun χ R (zOf χ R X)) h4
    rw [h5.1] at hr
    have e : statRowExplicit χ (fun y => eU (metOf X.1 y))
        (fun i y => PdLoc χ (metOf X.1 y) (psiV χ R X y) i) (Sfun χ R (zOf χ R X)) =
        statRowExplicit χ (dataMap χ (zOf χ R X)).1 (dataMap χ (zOf χ R X)).2
          (Sfun χ R (zOf χ R X)) := rfl
    rw [e, ← hr]
    rfl
  · rw [FH_inr_val]
    simp only [connOfZ_encZ]
    exact h6 x c

/-- **The uniform constraint map is the original-action constraint map `Cmap`** near `X = 0`. -/
theorem exists_eventually_CHmap_eq_Cmap : ∃ δ > 0, ∀ (N : ℕ) [NeZero N] (hNo : Odd N) {χ R : ℝ}
    {U : Set (CoP N)} (hU : FlatChart χ R U) (hχ : χ ≠ 0) (r K : ℕ) {M a ρ : ℝ}
    (h : Hyp (FH hNo χ r) (TH hχ r) K M a ρ), hN N < δ →
      ∀ᶠ X in 𝓝 (0 : XH N r), CHmap hNo χ r M a ρ X = encY r (Cmap χ R (decX X)) := by
  obtain ⟨δ₁, hδ₁, himp⟩ := exists_eventually_imp_eq
  obtain ⟨δ₂, hδ₂, hcrow⟩ := exists_CrowH_val
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun N _ hNo χ R U hU hχ r K M a ρ h hh => ?_⟩
  have hh1 : hN N < δ₁ := hh.trans_le (min_le_left _ _)
  have hh2 : hN N < δ₂ := hh.trans_le (min_le_right _ _)
  have hA := tendsto_Sfun_zOf hU hχ r
  have E3 : ∀ᶠ X in 𝓝 (0 : XH N r), ‖Sfun χ R (zOf χ R X)‖ < δ₂ :=
    hA.eventually (by
      filter_upwards [Metric.ball_mem_nhds (0 : Conn N) hδ₂] with A hA'
      simpa using hA')
  filter_upwards [himp N hNo hU hχ r K h hh1, eventually_Cmap_eq hU hχ r, E3] with X hD hC h3
  unfold CHmap
  rw [hD, hC]
  have hcr := hcrow N hNo χ r (X, encZ r (Sfun χ R (zOf χ R X)) (psiV χ R X)) hh2
    (by rw [connOfZ_encZ]; exact h3)
  funext row
  refine GridH.ext fun x => ?_
  obtain ⟨h0, hs⟩ := hcr x
  cases row using Fin.cases with
  | zero =>
    rw [h0]
    rfl
  | succ a =>
    rw [hs a]
    rfl

end RenewalGeometry.ExactPhaseAction.InitialCalculus
