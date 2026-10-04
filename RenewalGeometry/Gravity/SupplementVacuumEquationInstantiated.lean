/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.RenewalPalatiniHandoffExact
import RenewalGeometry.Gravity.SupplementVacuumEquationCore
import RenewalGeometry.Action.PhysicalTestStationarityExact

/-!
# Vacuum equation from certified accepted-action variations, instantiated
  (`cor:supp-renewal-einstein`; emergent-spacetime manuscript, supplement)

This file closes `cor:supp-renewal-einstein` by instantiating the proved localized
renewal–Palatini handoff `thm:supp-renewal-palatini`
(`RenewalPalatiniHandoff.renewal_palatini_handoff`, full-connection route, and
`renewal_palatini_handoff_literalLink`, literal-link route) and running the corollary's own
argument (`SupplementVacuumEquationCore`): the limit of each certified first variation is
`χ ∫_K √(-g) (G + Λ g) k` with `χ = β ≠ 0` (`eq:supp-einstein-insertion`); it vanishes on the
determining core because the realized variations vanish there along the selected cofinal
subsequence (uniqueness of limits); `χ ≠ 0` permits division; continuity in the declared test
topology extends the identity to the closure of the core (`Set.EqOn.closure`).

## Hypotheses ("the preceding hypotheses")

* the hypothesis packet of `thm:supp-renewal-palatini`, `RenewalPalatiniHypotheses` (or
  `RenewalPalatiniLiteralLinkHypotheses`), **including the disclosed amendment
  `spatialConnectionL3Bound`** (a uniform `L³_loc` bound on the spatial connection coefficients,
  accepted as a manuscript correction: the first Bianchi identity of the limit at the available
  regularity needs it; it is supplied by the Hodge–temporal budget
  `eq:main-connection-hodge-budget` and, on the literal-link route, by
  `eq:supp-literal-integrability`);
* `CertifiedMetricTests`: for each test `τ` of the determining metric-test core (an arbitrary
  set `core` in a test type `Test`, the test field being `kOf τ`), the bounded convergent physical
  lifts of `(E1)` (`δe_X = e_X H_X`, `H_X → -½ k g` a.e. on `K`) and the physical
  first-variation remainder condition `eq:main-first-variation-reduction` for the realized
  complete first variations `δA τ X`;
* the vanishing of the realized common-action variations on the core along a selected cofinal
  subsequence `sel` (`Tendsto sel atTop atTop`).

## Conclusion

`G + Λ g = 0` distributionally on the compact cylinder `K`: with
`einsteinCosmologicalPairing K Λ e R k = ∫_K √(-g) k^{γb} (G_{bγ} + Λ g_{bγ})`,
`Λ = cosmologicalConstant β λ = -λ/(2β)`, `G` the Einstein tensor of the identified limiting
curvature `RL` (the curvature of the torsion-free limit connection `ωL`, which is the unique
torsion-free metric-compatible one, by the handoff):

* the certified first variations converge to `β · ⟨G + Λ g, k⟩_K` for every core test;
* `⟨G + Λ g, k⟩_K = 0` for every core test;
* if the pairing is continuous in the declared test topology, it vanishes on the closure of
  the core.

`renewal_vacuum_equation_almost_surely` is the stochastic clause: on a common coupling of the
cutoffs, the scaled test gap `eq:supp-scaled-test-gap` (mean-square bounds `𝔼|δ𝒜_X|² ≤ b_X → 0`
on a countable core) gives, by `prop:supp-physical-test-stationarity`
(`physical_test_stationarity_core`, proved: Tonelli + diagonal selection), a deterministic
subsequence of cutoffs on which every core variation vanishes almost surely; provided the
compactness and identification budgets (the handoff packet and the test lifts) hold almost
surely on that same realized sequence, `G + Λ g = 0` holds almost surely.

Integrability: the conclusions also export that the Einstein insertion density (and the
Einstein-plus-cosmological density) of every core test is integrable on `K`
(`integrable_einsteinInsertionDensity`: the limit coframe is `L⁶`, the identified curvature `L²`,
the limit lift bounded; the classified variation is integrable by `tendsto_liftVariations` on
constant sequences and equals the insertion density a.e. by `ae_classifiedMetricVariation_eq_einstein`),
so the vanishing pairing is a genuine integral.  `ae_einsteinCosmologicalDensity_symmUnit_eq_zero`
gives the pointwise form (symmetrized `√(-g)(G + Λ g)` vanishes a.e. on `int K`) when the core
contains the constant symmetric unit tests and their smooth localizations.

Disclosed renderings: the test pairing is the Bochner integral over `K` (as in the handoff);
`G + Λ g` is tested against the inverse-metric test fields `k^{γb}`, i.e. its part detected by
the test class; the budget hypothesis of the stochastic clause is required for every
deterministic strictly increasing sequence of cutoffs (in particular for the one selected by
`prop:supp-physical-test-stationarity`), which is implied by the budgets holding along the whole
realized path sequence since all budget items are stable under subsequences.
-/

open MeasureTheory Filter Topology ENNReal TopologicalSpace Set
open scoped NNReal Distributions Matrix

noncomputable section

namespace RenewalGeometry.RenewalEinstein

open DistributionalTorsion DistributionalCurvature LimitEinsteinInsertion PalatiniEinsteinAlgebra
  RenewalPalatiniHandoff

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-! ### The tested Einstein-plus-cosmological tensor -/

/-- The density `√(-g) k^{γb} (G_{bγ} + Λ g_{bγ})` of the coframe `e`, the inverse-metric test
`k` and the raised internal curvature `R` (`G` the Einstein tensor of the coordinate curvature,
`g = eᵀ η e`). -/
def einsteinCosmologicalDensity (Λ : ℝ) (e k : Matrix (Fin 4) (Fin 4) ℝ)
    (R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) : ℝ :=
  Real.sqrt (-(coframeMetric minkowski e).det) *
    ∑ γ, ∑ b, k γ b * (PalatiniEinsteinAlgebra.einsteinOf (coframeMetric minkowski e)
      (coordCurvature e R) b γ + Λ * coframeMetric minkowski e b γ)

/-- The cosmological constant `Λ = -λ/(2β)` of the classified limit `α L_H + β L_P + λ L_vol`
(`eq:supp-einstein-insertion`, density conventions of `eq:main-phv-densities`). -/
def cosmologicalConstant (β lam : ℝ) : ℝ := -lam / (2 * β)

/-- The Einstein insertion density is `χ = β` times the Einstein-plus-cosmological density. -/
theorem einsteinInsertionDensity_eq (β lam : ℝ) (e k : Matrix (Fin 4) (Fin 4) ℝ)
    (R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    einsteinInsertionDensity β lam e k R =
      β * einsteinCosmologicalDensity (cosmologicalConstant β lam) e k R := by
  unfold einsteinInsertionDensity einsteinCosmologicalDensity cosmologicalConstant
  ring

/-- The distributional pairing `⟨G + Λ g, k⟩_K = ∫_K √(-g) k^{γb} (G_{bγ} + Λ g_{bγ})` of a
limiting coframe field `eL` and identified curvature field `RL`. -/
def einsteinCosmologicalPairing (K : Set (Fin 4 → ℝ)) (Λ : ℝ)
    (eL : Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ))
    (RL : Fin 4 → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)
    (k : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ) : ℝ :=
  ∫ x in K, einsteinCosmologicalDensity Λ (cfm eL x) (k x) (rcf RL x)

/-- `eq:supp-einstein-insertion` in the form `χ ⟨G + Λ g, k⟩_K`, `χ = β`. -/
theorem integral_einsteinInsertionDensity_eq (K : Set (Fin 4 → ℝ)) (β lam : ℝ)
    (eL : Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ))
    (RL : Fin 4 → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)
    (k : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ) :
    ∫ x in K, einsteinInsertionDensity β lam (cfm eL x) (k x) (rcf RL x) =
      β * einsteinCosmologicalPairing K (cosmologicalConstant β lam) eL RL k := by
  simp only [einsteinInsertionDensity_eq]
  exact integral_const_mul _ _

/-! ### The corollary's own argument -/

/-- Core vanishing and division by `χ ≠ 0`: if the certified first variations converge to
`χ Φ(τ)` on the core and vanish there along a cofinal subsequence, then `Φ = 0` on the core. -/
theorem insertion_vanishes_on_core {Test : Type*} (core : Set Test) (δA : Test → ℕ → ℝ)
    (Φ : Test → ℝ) {χ : ℝ} (hχ : χ ≠ 0)
    (hlim : ∀ τ ∈ core, Tendsto (δA τ) atTop (𝓝 (χ * Φ τ))) {sel : ℕ → ℕ}
    (hsel : Tendsto sel atTop atTop)
    (hvanish : ∀ τ ∈ core, Tendsto (fun n => δA τ (sel n)) atTop (𝓝 0)) :
    ∀ τ ∈ core, Φ τ = 0 := by
  intro τ hτ
  have h := tendsto_nhds_unique ((hlim τ hτ).comp hsel) (hvanish τ hτ)
  exact (mul_eq_zero.mp h).resolve_left hχ

/-- Extension to the closure of the core: continuity in the declared test topology. -/
theorem insertion_vanishes_on_closure {Test : Type*} [TopologicalSpace Test] (core : Set Test)
    (Φ : Test → ℝ) (hcont : Continuous Φ) (h0 : ∀ τ ∈ core, Φ τ = 0) :
    ∀ τ ∈ closure core, Φ τ = 0 := fun _ hτ =>
  (Set.EqOn.closure (f := Φ) (g := fun _ => (0 : ℝ)) h0 hcont continuous_const) hτ

/-! ### Integrability of the Einstein insertion density -/

open MollifiedBianchi DistributionalBianchi in
/-- **Pointwise Einstein form of the classified variation at limit regularity**: for a
torsion-free, metric-compatible limit pair with identified `L²_loc` curvature and the anisotropic
integrability packet on `Ω`, almost every point of `Ω` satisfies, for every test value `k` and
coefficients with `β ≠ 0`, `δ(α L_H + β L_P + λ L_vol)[k] = β √(-g) k (G + Λ g)` (the pointwise
statement behind `MollifiedBianchi.integral_classifiedMetricVariation_of_metricCompatible`). -/
theorem ae_classifiedMetricVariation_eq_einstein {Ω : Opens (Fin 4 → ℝ)}
    {e : Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ)} {ω : Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
    {R : Fin 4 → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ} {t : Fin 4}
    (hT : IsTorsionFree matAct Ω e ω) (hC : IsDistributionalCurvature Ω ω R)
    (hI : AnisotropicIntegrability Ω t e ω R)
    (hc : ∀ᵐ x, x ∈ Ω → ∀ a, (minkowski * ω a x)ᵀ = -(minkowski * ω a x))
    (hdet : ∀ᵐ x, x ∈ Ω → 0 < (coframeMatrix fun μ => e μ x).det) :
    ∀ᵐ x, x ∈ Ω → ∀ (k : Matrix (Fin 4) (Fin 4) ℝ) (α β lam : ℝ), β ≠ 0 →
      classifiedMetricVariation α β lam minkowski (coframeMatrix fun μ => e μ x) k
          (raisedCurvature fun ρ σ => R ρ σ x) =
        einsteinInsertionDensity β lam (coframeMatrix fun μ => e μ x) k
          (raisedCurvature fun ρ σ => R ρ σ x) := by
  have hsingle : ∀ I J a b, ∀ᵐ x, x ∈ Ω → so13Entry I J (R a b x) = 0 := by
    intro I J a b
    refine ae_map_curvature_eq_zero hC hI.curvature hI.connection (so13Entry I J) ?_ ?_ a b
    · filter_upwards [hc] with x hx hxΩ a
      show so13Defect (ω a x) I J = 0
      rw [so13Defect_eq_zero_of_compat (hx hxΩ a)]; rfl
    · filter_upwards [hc] with x hx hxΩ a b
      show so13Defect (ω a x * ω b x - ω b x * ω a x) I J = 0
      rw [so13Defect_commutator (so13Defect_eq_zero_of_compat (hx hxΩ a))
        (so13Defect_eq_zero_of_compat (hx hxΩ b))]; rfl
  have hall0 : ∀ᵐ x, x ∈ Ω → ∀ I J a b, so13Entry I J (R a b x) = 0 := by
    have : ∀ᵐ x, ∀ I J a b : Fin 4, x ∈ Ω → so13Entry I J (R a b x) = 0 := by
      simp only [ae_all_iff]; exact hsingle
    filter_upwards [this] with x hx hxΩ I J a b using hx I J a b hxΩ
  have hB := isDistributionalBianchi_of_isTorsionFree matAct matAct_mul hT hC hI
  have he2 : ∀ c (C : Set (Fin 4 → ℝ)), IsCompact C → C ⊆ Ω →
      MemLp (e c) 2 (volume.restrict C) := fun c C hC' hCΩ => by
    have : IsFiniteMeasure (volume.restrict C) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hC'.measure_lt_top⟩
    exact (hI.coframe c C hC' hCΩ).mono_exponent (by norm_num)
  have hae : ∀ a b c, ∀ᵐ x, x ∈ Ω → bianchiForm matAct R e a b c x = 0 := fun a b c =>
    ae_bianchi_of_isDistributionalBianchi matAct hI.curvature he2 hB a b c
  have hall : ∀ᵐ x, x ∈ Ω → ∀ a b c, bianchiForm matAct R e a b c x = 0 := by
    have : ∀ᵐ x, ∀ a b c : Fin 4, x ∈ Ω → bianchiForm matAct R e a b c x = 0 := by
      simp only [ae_all_iff]; exact hae
    filter_upwards [this] with x hx hxΩ a b c using hx a b c hxΩ
  have hswap : ∀ᵐ x, x ∈ Ω → ∀ a b, R a b x + R b a x = 0 := by
    have : ∀ᵐ x, ∀ a b : Fin 4, x ∈ Ω → R a b x + R b a x = 0 := by
      simp only [ae_all_iff]; exact fun a b => ae_curvature_add_swap_eq_zero hC hI.curvature a b
    filter_upwards [this] with x hx hxΩ a b using hx a b hxΩ
  filter_upwards [hall, hdet, hall0, hswap] with x h1 h2 h3 h4 hxΩ k α β lam hβ
  have hanti : ∀ K L ρ σ, raisedCurvature (fun ρ σ => R ρ σ x) L K ρ σ =
      -raisedCurvature (fun ρ σ => R ρ σ x) K L ρ σ := fun K' L ρ σ => by
    have h : so13Defect (R ρ σ x) K' L = 0 := h3 hxΩ K' L ρ σ
    simp only [so13Defect, Matrix.add_apply, Matrix.transpose_apply, Matrix.mul_apply] at h
    simp only [raisedCurvature]
    linarith
  refine classifiedMetricVariation_eq_einstein _ _ (h2 hxΩ) _ hanti (fun K L ρ σ => ?_)
    (satisfiesFirstBianchi_of_bianchiForm_eq_zero _ _ fun a b c => h1 hxΩ a b c) α β lam hβ
  have hR : R σ ρ x = -R ρ σ x := eq_neg_of_add_eq_zero_left (by rw [add_comm]; exact h4 hxΩ ρ σ)
  simp only [raisedCurvature, hR, Matrix.neg_apply, neg_mul, Finset.sum_neg_distrib]

open MollifiedBianchi in
/-- **The Einstein insertion density of a certified test is integrable** on `K`: at the limit,
the coframe is in `L⁶(K)`, the identified curvature in `L²(K)` and the test lift `-½ k g` is
bounded (as the a.e. limit of the uniformly bounded physical lifts of `(E1)`), so the three
limiting classified variation densities are integrable (`tendsto_liftVariations` applied to
constant sequences), and the classified variation equals the Einstein insertion density almost
everywhere on `K` (`ae_classifiedMetricVariation_eq_einstein`). -/
theorem integrable_einsteinInsertionDensity {K K' : Set (Fin 4 → ℝ)} (hK : IsCompact K)
    (hK' : IsCompact K') (hKK' : K ⊆ interior K')
    {e : ℕ → Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ)} {eL : Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ)}
    {ω : ℕ → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
    {ωL : Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
    {RL : Fin 4 → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ} {t : Fin 4}
    (he : ∀ μ, LpTendsto (volume.restrict K') 2 (fun n => e n μ) (eL μ))
    (he6 : ∀ μ, ∃ M : ℝ≥0∞, M ≠ ∞ ∧ ∀ n, eLpNorm (e n μ) 6 (volume.restrict K') ≤ M)
    (hωL : ∀ a, MemLp (ωL a) 2 (volume.restrict K'))
    (hωs : ∀ a, a ≠ t → LpTendsto (volume.restrict K') 2 (fun n => ω n a) (ωL a))
    (hω3 : ∀ a, a ≠ t → ∃ M : ℝ≥0∞, M ≠ ∞ ∧ ∀ n, eLpNorm (ω n a) 3 (volume.restrict K') ≤ M)
    (hT : IsTorsionFree matAct (interiorOpens K') eL ωL)
    (hcompat : ∀ᵐ x ∂(volume.restrict K'), ∀ a, (minkowski * ωL a x)ᵀ = -(minkowski * ωL a x))
    (hdet : ∀ᵐ x ∂(volume.restrict K'), 0 < (cfm eL x).det)
    (hCurv : IsDistributionalCurvature (interiorOpens K') ωL RL)
    (hR' : ∀ a b, MemLp (RL a b) 2 (volume.restrict K'))
    {k : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ} {H : ℕ → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
    {M : ℝ} (hHm : ∀ n, AEStronglyMeasurable (H n) (volume.restrict K))
    (hHb : ∀ n, ∀ᵐ x ∂(volume.restrict K), ‖H n x‖ ≤ M)
    (hHae : ∀ᵐ x ∂(volume.restrict K),
      Tendsto (fun n => H n x) atTop (𝓝 (metricTestGenerator minkowski (cfm eL x) (k x))))
    {β lam : ℝ} (hβ : β ≠ 0) :
    Integrable (fun x => einsteinInsertionDensity β lam (cfm eL x) (k x) (rcf RL x))
      (volume.restrict K) := by
  have hKK'' : K ⊆ K' := hKK'.trans interior_subset
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hK'm : MeasurableSet K' := hK'.isClosed.measurableSet
  have : IsFiniteMeasure (volume.restrict K) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
  have : IsFiniteMeasure (volume.restrict K') :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hK'.measure_lt_top⟩
  have hle : volume.restrict K ≤ volume.restrict K' := Measure.restrict_mono hKK'' le_rfl
  set H' : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ :=
    fun x => metricTestGenerator minkowski (cfm eL x) (k x)
  -- the limit lift is measurable and bounded
  have : PseudoMetrizableSpace (Matrix (Fin 4) (Fin 4) ℝ) :=
    inferInstanceAs (PseudoMetrizableSpace (Fin 4 → Fin 4 → ℝ))
  have hH'm : AEStronglyMeasurable H' (volume.restrict K) :=
    aestronglyMeasurable_of_tendsto_ae atTop hHm hHae
  have hH'b : ∀ᵐ x ∂(volume.restrict K), ‖H' x‖ ≤ M := by
    filter_upwards [hHae, ae_all_iff.2 hHb] with x hx hb
    exact le_of_tendsto' hx.norm hb
  -- the limit coframe is in `L⁶(K')`
  have he6' : ∀ μ, MemLp (eL μ) 6 (volume.restrict K') := fun μ => by
    obtain ⟨M6, hM6, hb⟩ := he6 μ
    exact (lpTendsto_four_of_two_six (he μ) hM6 hb).2
  -- constant sequences
  have hcE : ∀ μ, LpTendsto (volume.restrict K) 2 (fun _ : ℕ => eL μ) (eL μ) := fun μ =>
    ⟨fun _ => ((he μ).memLp_lim).mono_measure hle, ((he μ).memLp_lim).mono_measure hle,
      by simp⟩
  set M6 : ℝ≥0∞ := ∑ μ, eLpNorm (eL μ) 6 (volume.restrict K)
  have hM6 : M6 ≠ ∞ := ENNReal.sum_ne_top.2 fun μ _ =>
    ((he6' μ).mono_measure hle).eLpNorm_ne_top
  have hb6 : ∀ (_ : ℕ) μ, eLpNorm (eL μ) 6 (volume.restrict K) ≤ M6 := fun _ μ =>
    Finset.single_le_sum (f := fun μ => eLpNorm (eL μ) 6 (volume.restrict K))
      (fun _ _ => zero_le) (Finset.mem_univ μ)
  have hRK : ∀ a b, MemLp (RL a b) 2 (volume.restrict K) := fun a b =>
    memLp_mono_measure' hle (hR' a b)
  have hRb' : ∀ a b, eLpNorm (RL a b) 2 (volume.restrict K) ≤
      ∑ a', ∑ b', eLpNorm (RL a' b') 2 (volume.restrict K) := fun a b =>
    (Finset.single_le_sum (f := fun b' => eLpNorm (RL a b') 2 (volume.restrict K))
      (fun _ _ => zero_le) (Finset.mem_univ b)).trans
      (Finset.single_le_sum (f := fun a' => ∑ b', eLpNorm (RL a' b') 2 (volume.restrict K))
        (fun _ _ => zero_le) (Finset.mem_univ a))
  have hB : ∑ a', ∑ b', eLpNorm (RL a' b') 2 (volume.restrict K) ≠ ∞ :=
    ENNReal.sum_ne_top.2 fun a _ => ENNReal.sum_ne_top.2 fun b _ => (hRK a b).eLpNorm_ne_top
  obtain ⟨-, -, -, iH, iP, iV⟩ := tendsto_liftVariations (ν := volume.restrict K) minkowski
    (e := fun _ => eL) (H := fun _ => H') (R := fun _ => RL) hcE hM6 hb6 (fun _ => hH'm)
    (fun _ => hH'b) (Eventually.of_forall fun _ => tendsto_const_nhds) (fun _ => hRK) hRK hB
    (fun _ => hRb')
    (fun _ _ _ _ => tendsto_const_nhds)
  -- the classified variation density is integrable
  have hdetK : ∀ᵐ x ∂(volume.restrict K), 0 < (cfm eL x).det := ae_mono hle hdet
  have hcl : Integrable (fun x => classifiedMetricVariation 0 β lam minkowski (cfm eL x) (k x)
      (rcf RL x)) (volume.restrict K) := by
    refine (((iH.const_mul 0).add (iP.const_mul β)).add (iV.const_mul lam)).congr ?_
    filter_upwards [hdetK] with x hx
    simp only [classifiedMetricVariation, Pi.add_apply]
    rw [Matrix.nonsing_inv_mul_cancel_left _ _ (isUnit_iff_ne_zero.2 hx.ne')]
  -- the anisotropic integrability packet on `int K'`
  have hsub : ∀ C : Set (Fin 4 → ℝ), C ⊆ interiorOpens K' →
      volume.restrict C ≤ volume.restrict K' := fun C hC =>
    Measure.restrict_mono (hC.trans interior_subset) le_rfl
  have hI : AnisotropicIntegrability (interiorOpens K') t eL ωL RL :=
    ⟨fun a b C _ hC => memLp_mono_measure' (hsub C hC) (hR' a b),
      fun c C _ hC => (he6' c).mono_measure (hsub C hC),
      fun a C _ hC => memLp_mono_measure' (hsub C hC) (hωL a),
      fun a ha C _ hC => by
        obtain ⟨M3, hM3, hb3⟩ := hω3 a ha
        exact memLp_mono_measure' (hsub C hC) ((hωs a ha).memLp_of_bound two_ne_zero hM3 hb3)⟩
  have hc : ∀ᵐ x, x ∈ interiorOpens K' → ∀ a,
      (minkowski * ωL a x)ᵀ = -(minkowski * ωL a x) := by
    filter_upwards [(ae_restrict_iff' hK'm).1 hcompat] with x hx hxU
    exact hx (interior_subset hxU)
  have hd : ∀ᵐ x, x ∈ interiorOpens K' → 0 < (coframeMatrix fun μ => eL μ x).det := by
    filter_upwards [(ae_restrict_iff' hK'm).1 hdet] with x hx hxU
    exact hx (interior_subset hxU)
  have hpt := ae_classifiedMetricVariation_eq_einstein hT hCurv hI hc hd
  refine hcl.congr ?_
  refine (ae_restrict_iff' hKm).2 ?_
  filter_upwards [hpt] with x hx hxK
  exact hx (hKK' hxK) (k x) 0 β lam hβ

/-- The Einstein-plus-cosmological density of a certified test is integrable as well
(`χ = β ≠ 0`). -/
theorem integrable_einsteinCosmologicalDensity_of_insertion {K : Set (Fin 4 → ℝ)}
    {eL : Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ)}
    {RL : Fin 4 → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
    {k : (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ} {β lam : ℝ} (hβ : β ≠ 0)
    (h : Integrable (fun x => einsteinInsertionDensity β lam (cfm eL x) (k x) (rcf RL x))
      (volume.restrict K)) :
    Integrable (fun x => einsteinCosmologicalDensity (cosmologicalConstant β lam) (cfm eL x) (k x)
      (rcf RL x)) (volume.restrict K) := by
  refine (h.const_mul β⁻¹).congr (Eventually.of_forall fun x => ?_)
  simp only [einsteinInsertionDensity_eq, ← mul_assoc, inv_mul_cancel₀ hβ, one_mul]

/-! ### The certified metric tests -/

/-- The test-level hypotheses on a compact cylinder `K`: for every test `τ` of the determining
metric-test core, the bounded convergent physical lifts of `(E1)` (coefficient tensors `H τ X`,
`δe_X = e_X H_X`, uniformly bounded and converging a.e. on `K` to the limit lift
`-½ k g` of the test field `kOf τ`), and the physical first-variation remainder condition
`eq:main-first-variation-reduction` for the realized complete first variations `δA τ X`. -/
structure CertifiedMetricTests (K : Set (Fin 4 → ℝ)) (score : ℕ → GravitationalClassDensity)
    (e : ℕ → Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ))
    (R : ℕ → Fin 4 → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)
    (eL : Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ)) {Test : Type*}
    (kOf : Test → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ) (core : Set Test)
    (H : Test → ℕ → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ) (M : Test → ℝ)
    (δA : Test → ℕ → ℝ) : Prop where
  /-- `(E1)`: the lift coefficient tensors are measurable. -/
  lift_measurable : ∀ τ ∈ core, ∀ n, AEStronglyMeasurable (H τ n) (volume.restrict K)
  /-- `(E1)`: uniformly bounded coefficient tensors. -/
  lift_bounded : ∀ τ ∈ core, ∀ n, ∀ᵐ x ∂(volume.restrict K), ‖H τ n x‖ ≤ M τ
  /-- `(E1)`: convergent coefficient tensors, with limit the inverse-metric test lift. -/
  lift_tendsto : ∀ τ ∈ core, ∀ᵐ x ∂(volume.restrict K),
    Tendsto (fun n => H τ n x) atTop (𝓝 (metricTestGenerator minkowski (cfm eL x) (kOf τ x)))
  /-- `eq:main-first-variation-reduction` on the same metric tests. -/
  firstVariationRemainder : ∀ τ ∈ core, Tendsto (classifiedVariationRemainder (δA τ)
    (fun n => realizedHolst K (e n) (H τ n) (R n))
    (fun n => realizedPalatini K (e n) (H τ n) (R n))
    (fun n => realizedVolume K (e n) (H τ n))
    (fun n => holstCoeff (score n)) (fun n => palatiniCoeff (score n))
    (fun n => volumeCoeff (score n))) atTop (𝓝 0)


/-! ### `cor:supp-renewal-einstein`, deterministic route -/

/-- **`cor:supp-renewal-einstein` (full-connection route of `thm:supp-renewal-palatini`, with the
amendment `spatialConnectionL3Bound` inherited from `RenewalPalatiniHypotheses`).**  Under the
handoff hypotheses, the certified metric tests on a compact cylinder `K ⊆ Ω`, and vanishing of
the realized common-action first variations on the determining core along a selected cofinal
subsequence: the limit connection is torsion-free, `χ = β ≠ 0`, and there is an identified
limiting curvature `RL = dω + ω ∧ ω` (on a compact neighbourhood `K'` of `K`) such that the
certified first variations converge to `χ ⟨G + Λ g, k⟩_K`, `Λ = -λ/(2β)`, and `G + Λ g = 0`
distributionally on `K`: the pairing vanishes on the core and, when continuous in the declared
test topology, on its closure. -/
theorem renewal_vacuum_equation {Ω : Opens (Fin 4 → ℝ)}
    {score : ℕ → GravitationalClassDensity} {e : ℕ → Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ)}
    {ω : ℕ → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
    {R : ℕ → Fin 4 → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
    {T : ℕ → Fin 4 → Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ)}
    {eL : Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ)}
    {ωL : Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ} {α β lam : ℝ} {t : Fin 4}
    (h : RenewalPalatiniHypotheses Ω score e ω R T eL ωL α β lam t)
    {K : Set (Fin 4 → ℝ)} (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    {Test : Type*} [TopologicalSpace Test] {kOf : Test → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
    {core : Set Test} {H : Test → ℕ → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ} {M : Test → ℝ}
    {δA : Test → ℕ → ℝ} (htests : CertifiedMetricTests K score e R eL kOf core H M δA)
    {sel : ℕ → ℕ} (hsel : Tendsto sel atTop atTop)
    (hvanish : ∀ τ ∈ core, Tendsto (fun n => δA τ (sel n)) atTop (𝓝 0)) :
    IsTorsionFree matAct Ω eL ωL ∧ β ≠ 0 ∧
    ∃ K' : Set (Fin 4 → ℝ), IsCompact K' ∧ K ⊆ interior K' ∧ K' ⊆ Ω ∧
    ∃ RL : Fin 4 → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ,
      (∀ a b, MemLp (RL a b) 2 (volume.restrict K')) ∧
      IsDistributionalCurvature (interiorOpens K') ωL RL ∧
      (∀ τ ∈ core, Integrable (fun x => einsteinInsertionDensity β lam (cfm eL x) (kOf τ x)
          (rcf RL x)) (volume.restrict K) ∧
        Integrable (fun x => einsteinCosmologicalDensity (cosmologicalConstant β lam) (cfm eL x)
          (kOf τ x) (rcf RL x)) (volume.restrict K)) ∧
      (∀ τ ∈ core, Tendsto (δA τ) atTop
        (𝓝 (β * einsteinCosmologicalPairing K (cosmologicalConstant β lam) eL RL (kOf τ)))) ∧
      (∀ τ ∈ core, einsteinCosmologicalPairing K (cosmologicalConstant β lam) eL RL (kOf τ) = 0) ∧
      (Continuous (fun τ => einsteinCosmologicalPairing K (cosmologicalConstant β lam) eL RL
          (kOf τ)) →
        ∀ τ ∈ closure core,
          einsteinCosmologicalPairing K (cosmologicalConstant β lam) eL RL (kOf τ) = 0) := by
  obtain ⟨-, hTF, hloc⟩ := renewal_palatini_handoff h
  obtain ⟨K', hK', hKK', hK'Ω, RL, hRL, hid, hcompat, hdet, -, hvar⟩ := hloc K hK hKΩ
  have hUK' : ((interiorOpens K' : Opens (Fin 4 → ℝ)) : Set (Fin 4 → ℝ)) ⊆ Ω :=
    interior_subset.trans hK'Ω
  have hint : ∀ τ ∈ core, Integrable (fun x => einsteinInsertionDensity β lam (cfm eL x) (kOf τ x)
      (rcf RL x)) (volume.restrict K) ∧
      Integrable (fun x => einsteinCosmologicalDensity (cosmologicalConstant β lam) (cfm eL x)
        (kOf τ x) (rcf RL x)) (volume.restrict K) := fun τ hτ => by
    have hI := integrable_einsteinInsertionDensity hK hK' hKK'
      (fun μ => h.coframe_L2.lpTendsto μ hK' hK'Ω) (fun μ => h.coframe_L6 μ K' hK' hK'Ω)
      (fun a => h.connection_L2.memLp_lim a K' hK' hK'Ω)
      (fun a _ => h.connection_L2.lpTendsto a hK' hK'Ω)
      (fun a ha => h.spatialConnectionL3Bound a ha K' hK' hK'Ω) (isTorsionFree_mono hUK' hTF)
      hcompat hdet hid hRL (htests.lift_measurable τ hτ) (htests.lift_bounded τ hτ)
      (htests.lift_tendsto τ hτ) (lam := lam) h.palatini_ne_zero
    exact ⟨hI, integrable_einsteinCosmologicalDensity_of_insertion h.palatini_ne_zero hI⟩
  have hlim : ∀ τ ∈ core, Tendsto (δA τ) atTop
      (𝓝 (β * einsteinCosmologicalPairing K (cosmologicalConstant β lam) eL RL (kOf τ))) :=
    fun τ hτ => by
      rw [← integral_einsteinInsertionDensity_eq]
      exact hvar (kOf τ) (H τ) (M τ) (δA τ) (htests.lift_measurable τ hτ)
        (htests.lift_bounded τ hτ) (htests.lift_tendsto τ hτ) (htests.firstVariationRemainder τ hτ)
  have h0 := insertion_vanishes_on_core core δA _ h.palatini_ne_zero hlim hsel hvanish
  exact ⟨hTF, h.palatini_ne_zero, K', hK', hKK', hK'Ω, RL, hRL, hid, hint, hlim, h0,
    fun hc => insertion_vanishes_on_closure core _ hc h0⟩

/-- **`cor:supp-renewal-einstein` (literal-link route of `thm:supp-renewal-palatini`, with the
common-packet field `spatialConnectionL3Bound`, on this route `eq:supp-literal-integrability`).**
The same conclusion with the identified limiting curvature `RL` of the literal-link records. -/
theorem renewal_vacuum_equation_literalLink {Ω : Opens (Fin 4 → ℝ)}
    {score : ℕ → GravitationalClassDensity} {e : ℕ → Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ)}
    {ω : ℕ → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
    {R : ℕ → Fin 4 → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
    {T : ℕ → Fin 4 → Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ)}
    {eL : Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ)}
    {ωL : Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
    {RL : Fin 4 → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ} {α β lam : ℝ} {t : Fin 4}
    (h : RenewalPalatiniLiteralLinkHypotheses Ω score e ω R T eL ωL RL α β lam t)
    {K : Set (Fin 4 → ℝ)} (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    {Test : Type*} [TopologicalSpace Test] {kOf : Test → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
    {core : Set Test} {H : Test → ℕ → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ} {M : Test → ℝ}
    {δA : Test → ℕ → ℝ} (htests : CertifiedMetricTests K score e R eL kOf core H M δA)
    {sel : ℕ → ℕ} (hsel : Tendsto sel atTop atTop)
    (hvanish : ∀ τ ∈ core, Tendsto (fun n => δA τ (sel n)) atTop (𝓝 0)) :
    IsTorsionFree matAct Ω eL ωL ∧ β ≠ 0 ∧ IsDistributionalCurvature Ω ωL RL ∧
      (∀ τ ∈ core, Integrable (fun x => einsteinInsertionDensity β lam (cfm eL x) (kOf τ x)
          (rcf RL x)) (volume.restrict K) ∧
        Integrable (fun x => einsteinCosmologicalDensity (cosmologicalConstant β lam) (cfm eL x)
          (kOf τ x) (rcf RL x)) (volume.restrict K)) ∧
      (∀ τ ∈ core, Tendsto (δA τ) atTop
        (𝓝 (β * einsteinCosmologicalPairing K (cosmologicalConstant β lam) eL RL (kOf τ)))) ∧
      (∀ τ ∈ core, einsteinCosmologicalPairing K (cosmologicalConstant β lam) eL RL (kOf τ) = 0) ∧
      (Continuous (fun τ => einsteinCosmologicalPairing K (cosmologicalConstant β lam) eL RL
          (kOf τ)) →
        ∀ τ ∈ closure core,
          einsteinCosmologicalPairing K (cosmologicalConstant β lam) eL RL (kOf τ) = 0) := by
  obtain ⟨-, hTF, hloc⟩ := renewal_palatini_handoff_literalLink h
  obtain ⟨K', hK', hKK', hK'Ω, hcompat, hdet, -, hvar⟩ := hloc K hK hKΩ
  have hUK' : ((interiorOpens K' : Opens (Fin 4 → ℝ)) : Set (Fin 4 → ℝ)) ⊆ Ω :=
    interior_subset.trans hK'Ω
  have hint : ∀ τ ∈ core, Integrable (fun x => einsteinInsertionDensity β lam (cfm eL x) (kOf τ x)
      (rcf RL x)) (volume.restrict K) ∧
      Integrable (fun x => einsteinCosmologicalDensity (cosmologicalConstant β lam) (cfm eL x)
        (kOf τ x) (rcf RL x)) (volume.restrict K) := fun τ hτ => by
    have hI := integrable_einsteinInsertionDensity hK hK' hKK'
      (fun μ => h.coframe_L2.lpTendsto μ hK' hK'Ω) (fun μ => h.coframe_L6 μ K' hK' hK'Ω)
      (fun a => h.connection_limit_L2 a K' hK' hK'Ω)
      (fun a ha => h.spatial_strong a ha K' hK' hK'Ω)
      (fun a ha => h.spatialConnectionL3Bound a ha K' hK' hK'Ω) (isTorsionFree_mono hUK' hTF)
      hcompat hdet (fun ψ a b => h.curvature_identified (liftTest hUK' ψ) a b)
      (fun a b => h.curvature_limit_L2 a b K' hK' hK'Ω) (htests.lift_measurable τ hτ)
      (htests.lift_bounded τ hτ) (htests.lift_tendsto τ hτ) (lam := lam) h.palatini_ne_zero
    exact ⟨hI, integrable_einsteinCosmologicalDensity_of_insertion h.palatini_ne_zero hI⟩
  have hlim : ∀ τ ∈ core, Tendsto (δA τ) atTop
      (𝓝 (β * einsteinCosmologicalPairing K (cosmologicalConstant β lam) eL RL (kOf τ))) :=
    fun τ hτ => by
      rw [← integral_einsteinInsertionDensity_eq]
      exact hvar (kOf τ) (H τ) (M τ) (δA τ) (htests.lift_measurable τ hτ)
        (htests.lift_bounded τ hτ) (htests.lift_tendsto τ hτ) (htests.firstVariationRemainder τ hτ)
  have h0 := insertion_vanishes_on_core core δA _ h.palatini_ne_zero hlim hsel hvanish
  exact ⟨hTF, h.palatini_ne_zero, h.curvature_identified, hint, hlim, h0,
    fun hc => insertion_vanishes_on_closure core _ hc h0⟩

/-! ### `cor:supp-renewal-einstein`, stochastic route -/

/-- **`cor:supp-renewal-einstein`, stochastic clause** (full-connection route, amendment
`spatialConnectionL3Bound` inherited).  On a common coupling `(Path, P)` of the cutoffs, let the
determining core be countable, enumerated by `enum : ℕ → Test`, and let the realized first
variations `δA p τ X` satisfy the mean-square bounds `𝔼 |δA_X(k_m)|² ≤ b X m` of
`eq:main-physical-stationarity` with the scaled test gap `b X m → 0`
(`eq:supp-scaled-test-gap`).  Suppose the remaining compactness and identification budgets — the
handoff packet and the certified tests — hold almost surely on the realized sequence along every
deterministic strictly increasing choice of cutoffs (in particular along the one selected by
`prop:supp-physical-test-stationarity`).  Then the core first variations converge to zero in mean
square, and there is a deterministic subsequence of cutoffs along which, almost surely, the
limit connection is torsion-free and `G + Λ g = 0` distributionally on `K` (on the core and, under
continuity in the declared test topology, on its closure). -/
theorem renewal_vacuum_equation_almost_surely {Path : Type*} [MeasurableSpace Path]
    (P : Measure Path) {Ω : Opens (Fin 4 → ℝ)}
    {score : Path → ℕ → GravitationalClassDensity}
    {e : Path → ℕ → Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ)}
    {ω : Path → ℕ → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
    {R : Path → ℕ → Fin 4 → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
    {T : Path → ℕ → Fin 4 → Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ)}
    {eL : Path → Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ)}
    {ωL : Path → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ} {α β lam : Path → ℝ}
    {t : Fin 4} {K : Set (Fin 4 → ℝ)} (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    {Test : Type*} [TopologicalSpace Test] (kOf : Test → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)
    (enum : ℕ → Test) (H : Path → Test → ℕ → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ)
    (M : Path → Test → ℝ) (δA : Path → Test → ℕ → ℝ)
    (hint : ∀ X m, Integrable (fun p => δA p (enum m) X ^ 2) P)
    (hmeas : ∀ X m, AEMeasurable (fun p => δA p (enum m) X) P)
    (b : ℕ → ℕ → ℝ) (hb : ∀ X m, ∫ p, δA p (enum m) X ^ 2 ∂P ≤ b X m)
    (hgap : ∀ m, Tendsto (fun X => b X m) atTop (𝓝 0))
    (hbudget : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ᵐ p ∂P,
      RenewalPalatiniHypotheses Ω (fun n => score p (φ n)) (fun n => e p (φ n))
        (fun n => ω p (φ n)) (fun n => R p (φ n)) (fun n => T p (φ n)) (eL p) (ωL p) (α p) (β p)
        (lam p) t ∧
      CertifiedMetricTests K (fun n => score p (φ n)) (fun n => e p (φ n)) (fun n => R p (φ n))
        (eL p) kOf (Set.range enum) (fun τ n => H p τ (φ n)) (M p) (fun τ n => δA p τ (φ n))) :
    (∀ m, Tendsto (fun X => ∫ p, δA p (enum m) X ^ 2 ∂P) atTop (𝓝 0)) ∧
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ p ∂P,
      IsTorsionFree matAct Ω (eL p) (ωL p) ∧ β p ≠ 0 ∧
      ∃ K' : Set (Fin 4 → ℝ), IsCompact K' ∧ K ⊆ interior K' ∧ K' ⊆ Ω ∧
      ∃ RL : Fin 4 → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ,
        (∀ a b, MemLp (RL a b) 2 (volume.restrict K')) ∧
        IsDistributionalCurvature (interiorOpens K') (ωL p) RL ∧
        (∀ m, Integrable (fun x => einsteinInsertionDensity (β p) (lam p) (cfm (eL p) x)
            (kOf (enum m) x) (rcf RL x)) (volume.restrict K) ∧
          Integrable (fun x => einsteinCosmologicalDensity (cosmologicalConstant (β p) (lam p))
            (cfm (eL p) x) (kOf (enum m) x) (rcf RL x)) (volume.restrict K)) ∧
        (∀ m, Tendsto (fun j => δA p (enum m) (φ j)) atTop (𝓝 0)) ∧
        (∀ m, einsteinCosmologicalPairing K (cosmologicalConstant (β p) (lam p)) (eL p) RL
          (kOf (enum m)) = 0) ∧
        (Continuous (fun τ => einsteinCosmologicalPairing K (cosmologicalConstant (β p) (lam p))
            (eL p) RL (kOf τ)) →
          ∀ τ ∈ closure (Set.range enum), einsteinCosmologicalPairing K
            (cosmologicalConstant (β p) (lam p)) (eL p) RL (kOf τ) = 0) := by
  obtain ⟨hms, φ, hφ, hae⟩ := physical_test_stationarity_core P
    (fun X m p => δA p (enum m) X) hint hmeas b hb hgap
  refine ⟨hms, φ, hφ, ?_⟩
  filter_upwards [hae, hbudget φ hφ] with p hp hpk
  obtain ⟨hpal, htests⟩ := hpk
  have hvan : ∀ τ ∈ Set.range enum, Tendsto (fun n => δA p τ (φ (id n))) atTop (𝓝 0) := by
    rintro τ ⟨m, rfl⟩
    exact hp m
  obtain ⟨hTF, hβ, K', hK', hKK', hK'Ω, RL, hRL, hid, hint, -, h0, hcl⟩ :=
    renewal_vacuum_equation hpal hK hKΩ htests tendsto_id hvan
  exact ⟨hTF, hβ, K', hK', hKK', hK'Ω, RL, hRL, hid, fun m => hint _ ⟨m, rfl⟩, hp,
    fun m => h0 _ ⟨m, rfl⟩, hcl⟩

/-! ### Non-vacuity -/

theorem rcf_zero (x : Fin 4 → ℝ) :
    rcf (fun _ _ _ => (0 : Matrix (Fin 4) (Fin 4) ℝ)) x = 0 := by
  funext K L ρ σ
  simp [rcf, raisedCurvature]

/-- **Non-vacuity of `CertifiedMetricTests`** at the flat solution of
`renewalPalatiniHypotheses_flat`: every constant inverse-metric test `k` (test type `Matrix`, the
whole space as core) has the constant lift `H = -½ k η` (bounded, trivially convergent), and the
zero realized first variation satisfies the remainder condition (the Palatini variation vanishes
at zero curvature, and `α = λ = 0`). -/
theorem certifiedMetricTests_flat (K : Set (Fin 4 → ℝ)) :
    CertifiedMetricTests K (fun _ => RenewalGeometry.palatiniDensity)
      (fun _ μ _ => (Pi.single μ 1 : Fin 4 → ℝ)) (fun _ _ _ _ => 0)
      (fun μ _ => (Pi.single μ 1 : Fin 4 → ℝ)) (Test := Matrix (Fin 4) (Fin 4) ℝ)
      (fun k _ => k) Set.univ
      (fun k _ _ => metricTestGenerator minkowski 1 k)
      (fun k => ‖metricTestGenerator minkowski 1 k‖) (fun _ _ => 0) := by
  have hcfm : ∀ x : Fin 4 → ℝ, cfm (fun μ (_ : Fin 4 → ℝ) => (Pi.single μ 1 : Fin 4 → ℝ)) x = 1 :=
    fun x => coframeMatrix_basis
  refine ⟨fun _ _ _ => aestronglyMeasurable_const, fun _ _ _ => Eventually.of_forall fun _ => le_rfl,
    fun _ _ => Eventually.of_forall fun x => by rw [hcfm]; exact tendsto_const_nhds, fun k _ => ?_⟩
  have hP : ∀ n : ℕ, realizedPalatini K (fun μ (_ : Fin 4 → ℝ) => (Pi.single μ 1 : Fin 4 → ℝ))
      (fun _ => metricTestGenerator minkowski 1 k) (fun _ _ _ => 0) = 0 := fun n => by
    unfold realizedPalatini
    refine integral_eq_zero_of_ae (Eventually.of_forall fun x => ?_)
    simp only [rcf_zero]
    simp [palatiniVariation, PalatiniEinsteinAlgebra.pal4]
  refine tendsto_const_nhds.congr fun n => ?_
  simp only [classifiedVariationRemainder, holstCoeff_palatiniDensity, palatiniCoeff_palatiniDensity,
    volumeCoeff_palatiniDensity, hP n]
  ring

/-- **Non-vacuity of `renewal_vacuum_equation`**: the flat packet of
`renewalPalatiniHypotheses_flat` (including the amendment), the certified constant tests of
`certifiedMetricTests_flat`, and the vanishing zero variations satisfy every hypothesis. -/
example (K : Set (Fin 4 → ℝ)) (hK : IsCompact K) :=
  renewal_vacuum_equation (Test := Matrix (Fin 4) (Fin 4) ℝ) renewalPalatiniHypotheses_flat hK
    (Set.subset_univ K) (certifiedMetricTests_flat K) tendsto_id
    (fun _ _ => tendsto_const_nhds)


/-- The certified-test hypotheses restrict to a smaller core. -/
theorem CertifiedMetricTests.mono {K : Set (Fin 4 → ℝ)} {score : ℕ → GravitationalClassDensity}
    {e : ℕ → Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ)}
    {R : ℕ → Fin 4 → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ}
    {eL : Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ)} {Test : Type*}
    {kOf : Test → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ} {core core' : Set Test}
    {H : Test → ℕ → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ} {M : Test → ℝ} {δA : Test → ℕ → ℝ}
    (h : CertifiedMetricTests K score e R eL kOf core H M δA) (hsub : core' ⊆ core) :
    CertifiedMetricTests K score e R eL kOf core' H M δA :=
  ⟨fun τ hτ => h.lift_measurable τ (hsub hτ), fun τ hτ => h.lift_bounded τ (hsub hτ),
    fun τ hτ => h.lift_tendsto τ (hsub hτ), fun τ hτ => h.firstVariationRemainder τ (hsub hτ)⟩

/-- **Non-vacuity of `renewal_vacuum_equation_almost_surely`**: a one-point coupling carrying the
flat packet (including the amendment), a countable core of constant tests `k_m = m • 1`, zero
realized variations and zero scaled test gaps. -/
example (K : Set (Fin 4 → ℝ)) (hK : IsCompact K) :=
  renewal_vacuum_equation_almost_surely (Measure.dirac ()) (Ω := ⊤)
    (score := fun _ _ => RenewalGeometry.palatiniDensity)
    (e := fun _ _ μ _ => (Pi.single μ 1 : Fin 4 → ℝ)) (ω := fun _ _ _ _ => 0)
    (R := fun _ _ _ _ _ => 0) (T := fun _ _ _ _ _ => 0)
    (eL := fun _ μ _ => (Pi.single μ 1 : Fin 4 → ℝ)) (ωL := fun _ _ _ => 0)
    (α := fun _ => 0) (β := fun _ => 1) (lam := fun _ => 0) (t := 0) hK (Set.subset_univ K)
    (Test := Matrix (Fin 4) (Fin 4) ℝ) (fun k _ => k) (fun m => (m : ℝ) • 1)
    (fun _ k _ _ => metricTestGenerator minkowski 1 k)
    (fun _ k => ‖metricTestGenerator minkowski 1 k‖) (fun _ _ _ => 0)
    (fun _ _ => by simp) (fun _ _ => aemeasurable_const) (fun _ _ => 0) (fun _ _ => by simp)
    (fun _ => tendsto_const_nhds)
    (fun _ _ => Eventually.of_forall fun _ =>
      ⟨renewalPalatiniHypotheses_flat, (certifiedMetricTests_flat K).mono (Set.subset_univ _)⟩)


/-! ### Pointwise form on a rich core -/

/-- The symmetric unit inverse-metric test `E_{ij} + E_{ji}`. -/
def symmUnit (i j : Fin 4) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.single i j 1 + Matrix.single j i 1

/-- The Einstein-plus-cosmological density is linear in the test. -/
theorem einsteinCosmologicalDensity_smul (Λ c : ℝ) (e S : Matrix (Fin 4) (Fin 4) ℝ)
    (R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    einsteinCosmologicalDensity Λ e (c • S) R = c * einsteinCosmologicalDensity Λ e S R := by
  unfold einsteinCosmologicalDensity
  simp only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun γ _ => Finset.sum_congr rfl fun b _ => ?_
  ring

/-- **Pointwise vacuum equation on a rich core.**  If the Einstein-plus-cosmological densities of
the core tests are integrable on `K` and their pairings vanish (the exported conclusions of
`renewal_vacuum_equation`), and the core contains the constant symmetric unit tests
`E_{ij} + E_{ji}` and their localizations `φ (E_{ij} + E_{ji})`, `φ ∈ 𝓓(int K)`, then the
symmetrized tensor density `√(-g) ((G + Λ g)_{ij} + (G + Λ g)_{ji})` vanishes almost everywhere
on `int K` (fundamental lemma of the calculus of variations). -/
theorem ae_einsteinCosmologicalDensity_symmUnit_eq_zero {K : Set (Fin 4 → ℝ)} {Λ : ℝ}
    {eL : Fin 4 → (Fin 4 → ℝ) → (Fin 4 → ℝ)}
    {RL : Fin 4 → Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ} {Test : Type*}
    {kOf : Test → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℝ} {core : Set Test}
    (hint : ∀ τ ∈ core, Integrable (fun x => einsteinCosmologicalDensity Λ (cfm eL x) (kOf τ x)
      (rcf RL x)) (volume.restrict K))
    (hzero : ∀ τ ∈ core, einsteinCosmologicalPairing K Λ eL RL (kOf τ) = 0)
    (hconst : ∀ i j, ∃ τ ∈ core, kOf τ = fun _ => symmUnit i j)
    (hloc : ∀ (φ : 𝓓(interiorOpens K, ℝ)) (i j : Fin 4), ∃ τ ∈ core,
      kOf τ = fun x => φ x • symmUnit i j) :
    ∀ᵐ x, x ∈ interior K → ∀ i j,
      einsteinCosmologicalDensity Λ (cfm eL x) (symmUnit i j) (rcf RL x) = 0 := by
  have hone : ∀ i j, ∀ᵐ x, x ∈ interior K →
      einsteinCosmologicalDensity Λ (cfm eL x) (symmUnit i j) (rcf RL x) = 0 := by
    intro i j
    set w : (Fin 4 → ℝ) → ℝ :=
      fun x => einsteinCosmologicalDensity Λ (cfm eL x) (symmUnit i j) (rcf RL x)
    obtain ⟨τ0, hτ0, hk0⟩ := hconst i j
    have hwK : IntegrableOn w K := by
      have := hint τ0 hτ0
      rw [hk0] at this
      exact this
    have hlocw : LocallyIntegrableOn w (interior K) :=
      (hwK.mono_set interior_subset).locallyIntegrableOn
    refine isOpen_interior.ae_eq_zero_of_integral_contDiff_smul_eq_zero hlocw
      fun g hg hgc hgs => ?_
    set ψ : 𝓓(interiorOpens K, ℝ) := ⟨g, hg, hgc, hgs⟩
    obtain ⟨τ, hτ, hk⟩ := hloc ψ i j
    have h0 := hzero τ hτ
    rw [einsteinCosmologicalPairing, hk] at h0
    simp only [einsteinCosmologicalDensity_smul] at h0
    have hout : ∀ x ∉ K, g x • w x = 0 := fun x hx => by
      have : g x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (interior_subset (hgs h))
      simp [this]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hout]
    exact h0
  have : ∀ᵐ x, ∀ i j : Fin 4, x ∈ interior K →
      einsteinCosmologicalDensity Λ (cfm eL x) (symmUnit i j) (rcf RL x) = 0 := by
    simp only [ae_all_iff]; exact hone
  filter_upwards [this] with x hx hxK i j using hx i j hxK

end RenewalGeometry.RenewalEinstein
