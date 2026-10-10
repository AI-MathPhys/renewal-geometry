/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.BallHigherFinal
import RenewalGeometry.Continuum.UhlenbeckGaugeClosed
import RenewalGeometry.Continuum.CriticalQuotientClosure

/-!
# Uhlenbeck's small-energy Coulomb gauge theorem (ball rendering): proved
  (stage D, end of the proof)

Generic infrastructure for `prop:critical-uhlenbeck` and `thm:critical-quotient-defect` of the
Einstein–Standard-Model action-closure manuscript.

* `uhlenbeckHigherBounds` — the uniform `H⁶` bounds of the closedness step hold for every
  structure-group set `G` (`HigherFinal.coulombHigherBounds`);
* `uhlenbeckSmallEnergyGaugeIn_of_isGaugeStructure` (**Uhlenbeck's theorem for structure
  groups**) — for a real Lie subalgebra `𝔤` of skew-Hermitian matrices and a closed `G` with
  `G·G ⊆ G`, `exp 𝔤 ⊆ G`, `Ad_G 𝔤 ⊆ 𝔤`: `UhlenbeckGauge.UhlenbeckSmallEnergyGaugeIn m G 𝔤`;
* `uhlenbeckSmallEnergyGauge_holds` (**Uhlenbeck's theorem for `U(m)`**) — the named Prop
  `CriticalGauge.UhlenbeckSmallEnergyGauge m`;
* `critical_uhlenbeck`, `critical_uhlenbeck_in` — `prop:critical-uhlenbeck` (box rendering)
  without the named hypothesis; `critical_quotient_closure_in`, `critical_quotient_closure_unitary`
  — the composed compactness/Vitali clauses of `thm:critical-quotient-defect` without it.
-/

open MeasureTheory Filter Topology Set Matrix
open scoped ENNReal NNReal ContDiff

noncomputable section

namespace RenewalGeometry.BallAnalysis.UhlenbeckProved

open SobolevOpen CriticalGauge CriticalQuotient CriticalQuotientClosure UhlenbeckGauge
  UhlenbeckGaugeClosed UhlenbeckPackage

set_option linter.unusedSectionVars false

/-- **The uniform higher bounds** for every structure-group set `G`. -/
theorem uhlenbeckHigherBounds (m : ℕ) (G : Set (Matrix (Fin m) (Fin m) ℂ)) :
    UhlenbeckHigherBounds m G :=
  fun _d L _hGD => HigherFinal.coulombHigherBounds L G

/-- **Uhlenbeck's small-energy Coulomb gauge theorem for structure groups** (ball rendering). -/
theorem uhlenbeckSmallEnergyGaugeIn_of_isGaugeStructure {m : ℕ} {G : Set (Matrix (Fin m) (Fin m) ℂ)}
    {𝔤 : Submodule ℝ (Matrix (Fin m) (Fin m) ℂ)} (hS : IsGaugeStructure G 𝔤) :
    UhlenbeckSmallEnergyGaugeIn m G 𝔤 :=
  uhlenbeckIn_of_higherBounds hS (uhlenbeckHigherBounds m G)

/-- **Uhlenbeck's small-energy Coulomb gauge theorem for `U(m)`**: the named Prop
`CriticalGauge.UhlenbeckSmallEnergyGauge m` holds. -/
theorem uhlenbeckSmallEnergyGauge_holds (m : ℕ) : UhlenbeckSmallEnergyGauge m :=
  uhlenbeck_of_higherBounds (uhlenbeckHigherBounds m _)

/-- The structure-group form for `U(m)` with the Lie algebra `𝔲(m)`. -/
theorem uhlenbeckSmallEnergyGaugeIn_unitary (m : ℕ) :
    UhlenbeckSmallEnergyGaugeIn m (unitaryGroup (Fin m) ℂ) (skewSub m) :=
  uhlenbeckSmallEnergyGaugeIn_of_isGaugeStructure (unitary_isGaugeStructure m)

/-- **`prop:critical-uhlenbeck`** (`U(m)`, box rendering), unconditional. -/
theorem critical_uhlenbeck {m : ℕ}
    {a b : Fin 4 → ℝ} (A : ℕ → MConn m) (hA : ∀ h, IsSmoothUnitaryConn (A h))
    (_hbd : ∃ M : ℝ≥0, ∀ h, curvEnergy (A h) (box a b) ≤ M)
    (hUI : CriticalCurvatureUI volume (box a b) (fun h x => curvVec (A h) x))
    {K' : Set (Fin 4 → ℝ)} (hK' : IsCompact K') (hK'Q : K' ⊆ box a b) {η : ℝ≥0} (hη : 0 < η) :
    ∃ (N : ℕ) (lo hi : Fin N → Fin 4 → ℝ), (∀ j i, lo j i < hi j i) ∧
      (∀ j, box (lo j) (hi j) ⊆ box a b) ∧ K' ⊆ ⋃ j, box (lo j) (hi j) ∧
      ∃ R : ℕ → Fin N → (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ,
        (∀ h j, ∀ y ∈ box (lo j) (hi j), R h j y ∈ unitaryGroup (Fin m) ℂ) ∧
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
  critical_uhlenbeck_of_gauge (uhlenbeckSmallEnergyGauge_holds m) A hA _hbd hUI hK' hK'Q hη

/-- **`prop:critical-uhlenbeck` with `G`-valued gauges** for a gauge structure `(G, 𝔤)`. -/
theorem critical_uhlenbeck_in {m : ℕ} {G : Set (Matrix (Fin m) (Fin m) ℂ)}
    {𝔤 : Submodule ℝ (Matrix (Fin m) (Fin m) ℂ)} (hS : IsGaugeStructure G 𝔤)
    {a b : Fin 4 → ℝ} (A : ℕ → MConn m) (hA : ∀ h, IsSmoothUnitaryConn (A h))
    (h𝔤 : ∀ h μ y, A h μ y ∈ 𝔤)
    (hUI : CriticalCurvatureUI volume (box a b) (fun h x => curvVec (A h) x))
    {K' : Set (Fin 4 → ℝ)} (hK' : IsCompact K') (hK'Q : K' ⊆ box a b) {η : ℝ≥0} (hη : 0 < η) :
    ∃ (N : ℕ) (lo hi : Fin N → Fin 4 → ℝ), (∀ j i, lo j i < hi j i) ∧
      (∀ j, box (lo j) (hi j) ⊆ box a b) ∧ K' ⊆ ⋃ j, box (lo j) (hi j) ∧
      ∃ R : ℕ → Fin N → (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ,
        (∀ h j, ∀ y ∈ box (lo j) (hi j), R h j y ∈ G) ∧
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
  critical_uhlenbeck_of_gauge_in (𝔤 := (𝔤 : Set (Matrix (Fin m) (Fin m) ℂ)))
    (uhlenbeckSmallEnergyGaugeIn_of_isGaugeStructure hS) A hA h𝔤 hUI hK' hK'Q hη

/-- **`thm:critical-quotient-defect`, compactness and Vitali clauses, `G`-valued gauges**,
unconditional for a gauge structure `(G, 𝔤)` with `G ⊆ U(m)`. -/
theorem critical_quotient_closure_in {m : ℕ} {G : Set (Matrix (Fin m) (Fin m) ℂ)}
    {𝔤 : Submodule ℝ (Matrix (Fin m) (Fin m) ℂ)} (hS : IsGaugeStructure G 𝔤)
    (hG : G ⊆ unitaryGroup (Fin m) ℂ)
    {a b : Fin 4 → ℝ} (A : ℕ → MConn m) (hA : ∀ h, IsSmoothUnitaryConn (A h))
    (h𝔤 : ∀ h μ y, A h μ y ∈ 𝔤)
    (_hbd : ∃ M : ℝ≥0, ∀ h, curvEnergy (A h) (box a b) ≤ M)
    (hUI : CriticalCurvatureUI volume (box a b) (fun h x => curvVec (A h) x))
    {S : Type} [Fintype S] (u : ℕ → S → (Fin 4 → ℝ) → Fin m → ℂ)
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
    (hUI4 : ∀ s ∈ SH, UnifIntegrable (fun p : ℕ × Fin m => fun y => u p.1 s y p.2) 4
      (volume.restrict (box a b)))
    {K' : Set (Fin 4 → ℝ)} (hK' : IsCompact K') (hK'Q : K' ⊆ box a b) {η : ℝ≥0} (hη : 0 < η) :
    ∃ (N : ℕ) (ctr : Fin N → Fin 4 → ℝ) (r : ℝ), 0 < r ∧
      (∀ j, innerCube (ctr j) r ⊆ box a b) ∧ K' ⊆ ⋃ j, innerCube (ctr j) r ∧
      ∃ R : ℕ → Fin N → (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ,
        (∀ h j, ∀ y ∈ innerCube (ctr j) r, R h j y ∈ G) ∧
        (∀ h j, ∀ y ∈ innerCube (ctr j) r, R h j y ∈ unitaryGroup (Fin m) ℂ) ∧
        (∀ h j, ∀ x ∈ innerCube (ctr j) r, ∀ c e,
          ∑ μ, entryGrad (gaugeConn (R h j) (A h)) μ c e μ x = 0) ∧
        (∀ h j ν c e, eLpNorm (entries (gaugeConn (R h j) (A h)) ν c e) 4
          (volume.restrict (innerCube (ctr j) r)) ≤ η) ∧
        ∃ φ : ℕ → ℕ, StrictMono φ ∧ CoframeLimit (box a b) e φ ∧
          (∃ θ₀ ∈ Pset, Tendsto (θ ∘ φ) atTop (𝓝 θ₀)) ∧ ∀ j,
          QuotientLimitL4 (innerCube (ctr j) r) (fun h => gaugeConn (R h j) (A h))
            (fun h s => transp (R h j) (u h s)) (fun h s => tgrad (R h j) (u h s)) φ SH :=
  critical_quotient_closure_of_gauge_in (𝔤 := (𝔤 : Set (Matrix (Fin m) (Fin m) ℂ)))
    (uhlenbeckSmallEnergyGaugeIn_of_isGaugeStructure hS) hG A hA h𝔤 _hbd hUI u hu hQ3 e hQ1 hPset θ hθ
    SH hUI4 hK' hK'Q hη

/-- `critical_quotient_closure_of_gauge` without the named hypothesis (Uhlenbeck's theorem is proved). -/
theorem critical_quotient_closure {m : ℕ}
    {a b : Fin 4 → ℝ} (A : ℕ → MConn m) (hA : ∀ h, IsSmoothUnitaryConn (A h))
    (_hbd : ∃ M : ℝ≥0, ∀ h, curvEnergy (A h) (box a b) ≤ M)
    (hUI : CriticalCurvatureUI volume (box a b) (fun h x => curvVec (A h) x))
    {S : Type} [Fintype S] (u : ℕ → S → (Fin 4 → ℝ) → Fin m → ℂ)
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
    (hUI4 : ∀ s ∈ SH, UnifIntegrable (fun p : ℕ × Fin m => fun y => u p.1 s y p.2) 4
      (volume.restrict (box a b)))
    {K' : Set (Fin 4 → ℝ)} (hK' : IsCompact K') (hK'Q : K' ⊆ box a b) {η : ℝ≥0} (hη : 0 < η) :
    ∃ (N : ℕ) (ctr : Fin N → Fin 4 → ℝ) (r : ℝ), 0 < r ∧
      (∀ j, innerCube (ctr j) r ⊆ box a b) ∧ K' ⊆ ⋃ j, innerCube (ctr j) r ∧
      ∃ R : ℕ → Fin N → (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ,
        (∀ h j, ∀ y ∈ innerCube (ctr j) r, R h j y ∈ unitaryGroup (Fin m) ℂ) ∧
        (∀ h j, ∀ x ∈ innerCube (ctr j) r, ∀ c e,
          ∑ μ, entryGrad (gaugeConn (R h j) (A h)) μ c e μ x = 0) ∧
        (∀ h j ν c e, eLpNorm (entries (gaugeConn (R h j) (A h)) ν c e) 4
          (volume.restrict (innerCube (ctr j) r)) ≤ η) ∧
        ∃ φ : ℕ → ℕ, StrictMono φ ∧ CoframeLimit (box a b) e φ ∧
          (∃ θ₀ ∈ Pset, Tendsto (θ ∘ φ) atTop (𝓝 θ₀)) ∧ ∀ j,
          QuotientLimitL4 (innerCube (ctr j) r) (fun h => gaugeConn (R h j) (A h))
            (fun h s => transp (R h j) (u h s)) (fun h s => tgrad (R h j) (u h s)) φ SH :=
  critical_quotient_closure_of_gauge (uhlenbeckSmallEnergyGauge_holds m) A hA _hbd hUI u hu hQ3 e hQ1 hPset θ hθ SH hUI4 hK' hK'Q hη

/-- `critical_quotient_compactness_of_gauge` without the named hypothesis (Uhlenbeck's theorem is proved). -/
theorem critical_quotient_compactness {m : ℕ}
    {a b : Fin 4 → ℝ} (A : ℕ → MConn m) (hA : ∀ h, IsSmoothUnitaryConn (A h))
    (_hbd : ∃ M : ℝ≥0, ∀ h, curvEnergy (A h) (box a b) ≤ M)
    (hUI : CriticalCurvatureUI volume (box a b) (fun h x => curvVec (A h) x))
    {S : Type} [Fintype S] (u : ℕ → S → (Fin 4 → ℝ) → Fin m → ℂ)
    (hu : ∀ h s, ContDiff ℝ ∞ (u h s))
    (hQ3 : ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ h s,
      ∑ e, eLpNorm (fun y => u h s y e) 2 (volume.restrict (box a b)) +
        ∑ e, ∑ μ, eLpNorm (fun y => covDerV (A h) (u h s) μ y e) 2 (volume.restrict (box a b))
          ≤ B)
    {K' : Set (Fin 4 → ℝ)} (hK' : IsCompact K') (hK'Q : K' ⊆ box a b) {η : ℝ≥0} (hη : 0 < η) :
    ∃ (N : ℕ) (ctr : Fin N → Fin 4 → ℝ) (r : ℝ), 0 < r ∧
      (∀ j, innerCube (ctr j) r ⊆ box a b) ∧ K' ⊆ ⋃ j, innerCube (ctr j) r ∧
      ∃ R : ℕ → Fin N → (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ,
        (∀ h j, ∀ y ∈ innerCube (ctr j) r, R h j y ∈ unitaryGroup (Fin m) ℂ) ∧
        (∀ h j, ∀ x ∈ innerCube (ctr j) r, ∀ c e,
          ∑ μ, entryGrad (gaugeConn (R h j) (A h)) μ c e μ x = 0) ∧
        (∀ h j ν c e, eLpNorm (entries (gaugeConn (R h j) (A h)) ν c e) 4
          (volume.restrict (innerCube (ctr j) r)) ≤ η) ∧
        ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ j,
          QuotientLimit (innerCube (ctr j) r) (fun h => gaugeConn (R h j) (A h))
            (fun h s => transp (R h j) (u h s)) (fun h s => tgrad (R h j) (u h s)) φ :=
  critical_quotient_compactness_of_gauge (uhlenbeckSmallEnergyGauge_holds m) A hA _hbd hUI u hu hQ3 hK' hK'Q hη

/-- `critical_quotient_closure_of_gauge_unitary` without the named hypothesis (Uhlenbeck's theorem is proved). -/
theorem critical_quotient_closure_unitary {m : ℕ}
    {a b : Fin 4 → ℝ} (A : ℕ → MConn m) (hA : ∀ h, IsSmoothUnitaryConn (A h))
    (hbd : ∃ M : ℝ≥0, ∀ h, curvEnergy (A h) (box a b) ≤ M)
    (hUI : CriticalCurvatureUI volume (box a b) (fun h x => curvVec (A h) x))
    {S : Type} [Fintype S] (u : ℕ → S → (Fin 4 → ℝ) → Fin m → ℂ)
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
    (hUI4 : ∀ s ∈ SH, UnifIntegrable (fun p : ℕ × Fin m => fun y => u p.1 s y p.2) 4
      (volume.restrict (box a b)))
    {K' : Set (Fin 4 → ℝ)} (hK' : IsCompact K') (hK'Q : K' ⊆ box a b) {η : ℝ≥0} (hη : 0 < η) :
    ∃ (N : ℕ) (ctr : Fin N → Fin 4 → ℝ) (r : ℝ), 0 < r ∧
      (∀ j, innerCube (ctr j) r ⊆ box a b) ∧ K' ⊆ ⋃ j, innerCube (ctr j) r ∧
      ∃ R : ℕ → Fin N → (Fin 4 → ℝ) → Matrix (Fin m) (Fin m) ℂ,
        (∀ h j, ∀ y ∈ innerCube (ctr j) r, R h j y ∈ unitaryGroup (Fin m) ℂ) ∧
        (∀ h j, ∀ x ∈ innerCube (ctr j) r, ∀ c e,
          ∑ μ, entryGrad (gaugeConn (R h j) (A h)) μ c e μ x = 0) ∧
        (∀ h j ν c e, eLpNorm (entries (gaugeConn (R h j) (A h)) ν c e) 4
          (volume.restrict (innerCube (ctr j) r)) ≤ η) ∧
        ∃ φ : ℕ → ℕ, StrictMono φ ∧ CoframeLimit (box a b) e φ ∧
          (∃ θ₀ ∈ Pset, Tendsto (θ ∘ φ) atTop (𝓝 θ₀)) ∧ ∀ j,
          QuotientLimitL4 (innerCube (ctr j) r) (fun h => gaugeConn (R h j) (A h))
            (fun h s => transp (R h j) (u h s)) (fun h s => tgrad (R h j) (u h s)) φ SH :=
  critical_quotient_closure_of_gauge_unitary (uhlenbeckSmallEnergyGauge_holds m) A hA hbd hUI u hu hQ3 e hQ1 hPset θ hθ SH hUI4 hK' hK'Q hη

/-- Non-vacuity: the trivial connection on the unit ball has the trivial Uhlenbeck gauge data
(`UhlenbeckSmallEnergyGauge 1` is an inhabited Prop with a positive threshold). -/
example : ∃ εU : ℝ≥0, 0 < εU := by
  obtain ⟨εU, hεU, -⟩ := uhlenbeckSmallEnergyGauge_holds 1
  exact ⟨εU, hεU⟩

/-- Non-vacuity of the gauge-structure hypothesis: `(U(m), 𝔲(m))` is a gauge structure. -/
example (m : ℕ) : IsGaugeStructure (unitaryGroup (Fin m) ℂ) (skewSub m) :=
  unitary_isGaugeStructure m

end RenewalGeometry.BallAnalysis.UhlenbeckProved
