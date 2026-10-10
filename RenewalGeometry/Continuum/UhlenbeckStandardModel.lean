/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.BallUhlenbeckProved
import RenewalGeometry.Analysis.StandardModelGaugeStructure

/-!
# Uhlenbeck's theorem and the critical quotient closure for `G_SM = S(U(3) × U(2))`

Standard-Model instance of `prop:critical-uhlenbeck` and of the composed compactness/Vitali
clauses of `thm:critical-quotient-defect` (Einstein–Standard-Model action-closure manuscript):
the Coulomb gauges take values in the structure group `G_SM = S(U(3) × U(2))` of
`eq:gauge-group` (not merely in `U(5)`), which is what the pull-back of the `G_SM`-equivariant
budgets through the Coulomb charts requires.

* `uhlenbeckSmallEnergyGaugeIn_SM` — `UhlenbeckSmallEnergyGaugeIn 5 G_SM 𝔰(𝔲(3) ⊕ 𝔲(2))`;
* `critical_uhlenbeck_SM` — `prop:critical-uhlenbeck` for `smLie`-valued smooth connections with
  `G_SM`-valued Coulomb gauges;
* `critical_quotient_closure_SM` — the composed clauses of `thm:critical-quotient-defect` with
  `G_SM`-valued (hence unitary) Coulomb gauges.

The Lie-algebra hypothesis is stated in the ledger encoding `EinsteinSM.smLie` of the field
spaces (`def:tests`), via the identification `SMGaugeStructure.mem_gSM_iff`.
-/

open MeasureTheory Filter Topology Set Matrix
open scoped ENNReal NNReal ContDiff

noncomputable section

namespace RenewalGeometry.BallAnalysis.UhlenbeckStandardModel

open SobolevOpen CriticalGauge CriticalQuotient CriticalQuotientClosure UhlenbeckGauge
  UhlenbeckGaugeClosed UhlenbeckPackage UhlenbeckProved SMGaugeStructure EinsteinSM

set_option linter.unusedSectionVars false

/-- **Uhlenbeck's small-energy Coulomb gauge theorem for `G_SM = S(U(3) × U(2))`**:
`𝔰(𝔲(3) ⊕ 𝔲(2))`-valued smooth connections of small energy admit smooth `G_SM`-valued Coulomb
gauges with the `W^{1,2}` and scale-invariant `L⁴` bounds. -/
theorem uhlenbeckSmallEnergyGaugeIn_SM :
    UhlenbeckSmallEnergyGaugeIn 5 GSM (gSM : Set (Matrix (Fin 5) (Fin 5) ℂ)) :=
  uhlenbeckSmallEnergyGaugeIn_of_isGaugeStructure isGaugeStructure_SM

/-- An `smLie`-valued matrix is in `gSM`. -/
theorem mem_gSM_of_smLie {X : Matrix (Fin 5) (Fin 5) ℂ} (hX : Matrix.of.symm X ∈ smLie) :
    X ∈ gSM := by
  have := (mem_gSM_iff (Matrix.of.symm X)).2 hX
  rwa [Equiv.apply_symm_apply] at this

/-- **`prop:critical-uhlenbeck` for the Standard-Model structure group** (box rendering):
for smooth unitary connections with values in `smLie = 𝔰(𝔲(3) ⊕ 𝔲(2))` and uniformly integrable
critical curvature energy, the local Coulomb gauges take values in `G_SM = S(U(3) × U(2))`. -/
theorem critical_uhlenbeck_SM
    {a b : Fin 4 → ℝ} (A : ℕ → MConn 5) (hA : ∀ h, IsSmoothUnitaryConn (A h))
    (hsm : ∀ h μ y, Matrix.of.symm (A h μ y) ∈ smLie)
    (hUI : CriticalCurvatureUI volume (box a b) (fun h x => curvVec (A h) x))
    {K' : Set (Fin 4 → ℝ)} (hK' : IsCompact K') (hK'Q : K' ⊆ box a b) {η : ℝ≥0} (hη : 0 < η) :
    ∃ (N : ℕ) (lo hi : Fin N → Fin 4 → ℝ), (∀ j i, lo j i < hi j i) ∧
      (∀ j, box (lo j) (hi j) ⊆ box a b) ∧ K' ⊆ ⋃ j, box (lo j) (hi j) ∧
      ∃ R : ℕ → Fin N → (Fin 4 → ℝ) → Matrix (Fin 5) (Fin 5) ℂ,
        (∀ h j, ∀ y ∈ box (lo j) (hi j), R h j y ∈ GSM) ∧
        (∀ h j, ∀ x ∈ box (lo j) (hi j), ∀ c e,
          ∑ μ, entryGrad (gaugeConn (R h j) (A h)) μ c e μ x = 0) ∧
        (∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ h j ν c e,
          MemW12 (box (lo j) (hi j)) (entries (gaugeConn (R h j) (A h)) ν c e)
            (entryGrad (gaugeConn (R h j) (A h)) ν c e) ∧
          w12Norm (box (lo j) (hi j)) (entries (gaugeConn (R h j) (A h)) ν c e)
            (entryGrad (gaugeConn (R h j) (A h)) ν c e) ≤ B) ∧
        (∀ h j ν c e, eLpNorm (entries (gaugeConn (R h j) (A h)) ν c e) 4
          (volume.restrict (box (lo j) (hi j))) ≤ η) ∧
        ∃ φ : ℕ → ℕ, StrictMono φ ∧
          ∀ j, CoulombLimit (box (lo j) (hi j)) (fun h => gaugeConn (R h j) (A h)) φ :=
  critical_uhlenbeck_in isGaugeStructure_SM A hA (fun h μ y => mem_gSM_of_smLie (hsm h μ y)) hUI
    hK' hK'Q hη

/-- **`thm:critical-quotient-defect`, compactness, coframe/bank and Vitali clauses, for the
Standard-Model structure group**: the composition of `critical_quotient_closure_in` with
`(G_SM, 𝔰(𝔲(3) ⊕ 𝔲(2)))`; the Coulomb gauges are `G_SM`-valued (and unitary). -/
theorem critical_quotient_closure_SM
    {a b : Fin 4 → ℝ} (A : ℕ → MConn 5) (hA : ∀ h, IsSmoothUnitaryConn (A h))
    (hsm : ∀ h μ y, Matrix.of.symm (A h μ y) ∈ smLie)
    (hbd : ∃ M : ℝ≥0, ∀ h, curvEnergy (A h) (box a b) ≤ M)
    (hUI : CriticalCurvatureUI volume (box a b) (fun h x => curvVec (A h) x))
    {S : Type} [Fintype S] (u : ℕ → S → (Fin 4 → ℝ) → Fin 5 → ℂ)
    (hu : ∀ h s, ContDiff ℝ ∞ (u h s))
    (hQ3 : ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ h s,
      ∑ e, eLpNorm (fun y => u h s y e) 2 (volume.restrict (box a b)) +
        ∑ e, ∑ μ, eLpNorm (fun y => covDerV (A h) (u h s) μ y e) 2 (volume.restrict (box a b))
          ≤ B)
    (e : ℕ → (Fin 4 → ℝ) → Fin 4 → Fin 4 → ℝ)
    (hQ1 : ∀ φ : ℕ → ℕ, StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      CoframeLimit (box a b) e (φ ∘ ψ))
    {P : Type*} [MetricSpace P] {Pset : Set P} (hPset : IsCompact Pset) (θ : ℕ → P)
    (hθ : ∀ h, θ h ∈ Pset)
    (SH : Set S)
    (hUI4 : ∀ s ∈ SH, UnifIntegrable (fun p : ℕ × Fin 5 => fun y => u p.1 s y p.2) 4
      (volume.restrict (box a b)))
    {K' : Set (Fin 4 → ℝ)} (hK' : IsCompact K') (hK'Q : K' ⊆ box a b) {η : ℝ≥0} (hη : 0 < η) :
    ∃ (N : ℕ) (ctr : Fin N → Fin 4 → ℝ) (r : ℝ), 0 < r ∧
      (∀ j, innerCube (ctr j) r ⊆ box a b) ∧ K' ⊆ ⋃ j, innerCube (ctr j) r ∧
      ∃ R : ℕ → Fin N → (Fin 4 → ℝ) → Matrix (Fin 5) (Fin 5) ℂ,
        (∀ h j, ∀ y ∈ innerCube (ctr j) r, R h j y ∈ GSM) ∧
        (∀ h j, ∀ y ∈ innerCube (ctr j) r, R h j y ∈ unitaryGroup (Fin 5) ℂ) ∧
        (∀ h j, ∀ x ∈ innerCube (ctr j) r, ∀ c e,
          ∑ μ, entryGrad (gaugeConn (R h j) (A h)) μ c e μ x = 0) ∧
        (∀ h j ν c e, eLpNorm (entries (gaugeConn (R h j) (A h)) ν c e) 4
          (volume.restrict (innerCube (ctr j) r)) ≤ η) ∧
        ∃ φ : ℕ → ℕ, StrictMono φ ∧ CoframeLimit (box a b) e φ ∧
          (∃ θ₀ ∈ Pset, Tendsto (θ ∘ φ) atTop (𝓝 θ₀)) ∧ ∀ j,
          QuotientLimitL4 (innerCube (ctr j) r) (fun h => gaugeConn (R h j) (A h))
            (fun h s => transp (R h j) (u h s)) (fun h s => tgrad (R h j) (u h s)) φ SH :=
  critical_quotient_closure_in isGaugeStructure_SM GSM_subset_unitary A hA
    (fun h μ y => mem_gSM_of_smLie (hsm h μ y)) hbd hUI u hu hQ3 e hQ1 hPset θ hθ SH hUI4 hK'
    hK'Q hη

/-- Non-vacuity: `(G_SM, 𝔰(𝔲(3) ⊕ 𝔲(2)))` is a gauge structure with a nonzero Lie-algebra
element whose one-parameter group lies in `G_SM`, and `G_SM` has a non-identity element. -/
example : IsGaugeStructure GSM gSM ∧ (∃ X ∈ gSM, X ≠ 0 ∧ ∀ t : ℝ, NormedSpace.exp (t • X) ∈ GSM) ∧
    ∃ g ∈ GSM, g ≠ 1 :=
  ⟨isGaugeStructure_SM,
    ⟨hyperY, hyperY_mem, hyperY_ne_zero, fun t => exp_mem_GSM (gSM.smul_mem t hyperY_mem)⟩,
    flipTwo, flipTwo_mem, flipTwo_ne_one⟩

/-- Non-vacuity of the Lie-algebra hypothesis: the trivial connection is `smLie`-valued. -/
example : ∀ μ y, Matrix.of.symm ((fun _ _ => 0 : MConn 5) μ y) ∈ smLie :=
  fun _ _ => smLie.zero_mem

end RenewalGeometry.BallAnalysis.UhlenbeckStandardModel
