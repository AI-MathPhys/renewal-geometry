/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.DistributionalCurvatureCompactness

/-!
# Distributional torsion of represented coframes and connections, and its strong limits
  (torsion clause of `thm:supp-renewal-palatini`, full-connection route;
  emergent-spacetime manuscript, supplement)

For a coframe `e = Σ_a e_a dx^a` with values in a fibre `V` (e.g. `ℝ^{1,3}`) and a connection
`ω = Σ_a ω_a dx^a` with values in a space `A` acting on `V` through a continuous bilinear map
`act : A →L V →L V` (e.g. matrix–vector multiplication), the torsion `T = d e + ω ∧ e` is tested
against `φ ∈ 𝓓(Ω)` by
`⟨T, φ⟩_{ab} = -∫ ∂_a φ e_b + ∫ ∂_b φ e_a + ∫ φ (act ω_a e_b - act ω_b e_a)` (`torsionPairing`).

* `tendsto_integral_smul_bilin_of_L2`: bounded weights against a bilinear product of two
  strongly `L²`-convergent sequences (strong `L²` × strong `L²` → strong `L¹`);
* `tendsto_torsionPairing`: strong `L²_loc` convergence of `(e_X, ω_X)` passes to the limit in
  the distributional torsion (the Cartan product passes directly, `thm:supp-renewal-palatini`,
  full-connection route);
* `isTorsionFree_of_tendsto`: if the tested torsion residuals tend to zero (e.g. by the vanishing
  connection Euler residual with the uniform Cartan inverse of `thm:supp-palatini-torsion`), the
  limiting represented connection is torsion-free in distributions.
-/

open MeasureTheory Filter Topology ENNReal TopologicalSpace
open scoped NNReal Distributions

noncomputable section

namespace RenewalGeometry.DistributionalTorsion

open DistributionalCurvature

set_option linter.unusedSectionVars false

variable {A V : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [CompleteSpace A]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- A bounded weight integrated against a bilinear product of two `L²`-convergent sequences
converges. -/
theorem tendsto_integral_smul_bilin_of_L2 {X : Type*} [MeasurableSpace X] {ν : Measure X}
    [IsFiniteMeasure ν] (act : A →L[ℝ] V →L[ℝ] V) {ψ : X → ℝ} (hψ : AEStronglyMeasurable ψ ν)
    {M : ℝ} (hM : ∀ x, ‖ψ x‖ ≤ M) {u : ℕ → X → A} {v : ℕ → X → V} {u' : X → A} {v' : X → V}
    (hu : ∀ n, MemLp (u n) 2 ν) (hv : ∀ n, MemLp (v n) 2 ν) (hu' : MemLp u' 2 ν)
    (hv' : MemLp v' 2 ν) (hulim : Tendsto (fun n => eLpNorm (u n - u') 2 ν) atTop (𝓝 0))
    (hvlim : Tendsto (fun n => eLpNorm (v n - v') 2 ν) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, ψ x • act (u n x) (v n x) ∂ν) atTop
      (𝓝 (∫ x, ψ x • act (u' x) (v' x) ∂ν)) := by
  have hψ : MemLp ψ ∞ ν := memLp_top_of_bound hψ M (Eventually.of_forall hM)
  let H := ContinuousLinearMap.holderL ν 2 2 1 act
  let L := ContinuousLinearMap.lpPairing ν ∞ 1 (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] V →L[ℝ] V)
  have hU : Tendsto (fun n => (hu n).toLp (u n)) atTop (𝓝 (hu'.toLp u')) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ _ _ _).2 hulim
  have hV : Tendsto (fun n => (hv n).toLp (v n)) atTop (𝓝 (hv'.toLp v')) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ _ _ _).2 hvlim
  have hW := (H.continuous₂.tendsto (hu'.toLp u', hv'.toLp v')).comp (hU.prodMk_nhds hV)
  have h := ((L (hψ.toLp ψ)).continuous.tendsto _).comp hW
  have heq : ∀ (a : X → A) (b : X → V) (ha : MemLp a 2 ν) (hb : MemLp b 2 ν),
      L (hψ.toLp ψ) (H (ha.toLp a) (hb.toLp b)) = ∫ x, ψ x • act (a x) (b x) ∂ν := by
    intro a b ha hb
    rw [ContinuousLinearMap.lpPairing_eq_integral]
    apply integral_congr_ae
    filter_upwards [hψ.coeFn_toLp, ha.coeFn_toLp, hb.coeFn_toLp,
      ContinuousLinearMap.coeFn_holder (r := 1) act (ha.toLp a) (hb.toLp b)] with x h1 h2 h3 h4
    simp only [H, ContinuousLinearMap.holderL_apply_apply] at *
    rw [h4, h1, h2, h3]
    simp
  simp only [Function.comp_def, Function.uncurry_apply_pair] at h
  rw [heq] at h
  exact h.congr fun n => heq _ _ _ _

variable {d : ℕ}

/-- Strong `L²_loc(Ω)` convergence of `E`-valued one-forms (componentwise, on every compact
subset of `Ω`). -/
structure L2LocTendsto {E : Type*} [NormedAddCommGroup E] (Ω : Opens (Fin d → ℝ))
    (u : ℕ → Fin d → (Fin d → ℝ) → E) (u' : Fin d → (Fin d → ℝ) → E) : Prop where
  memLp : ∀ n a (C : Set (Fin d → ℝ)), IsCompact C → C ⊆ Ω → MemLp (u n a) 2 (volume.restrict C)
  memLp_lim : ∀ a (C : Set (Fin d → ℝ)), IsCompact C → C ⊆ Ω → MemLp (u' a) 2 (volume.restrict C)
  tendsto : ∀ a (C : Set (Fin d → ℝ)), IsCompact C → C ⊆ Ω →
    Tendsto (fun n => eLpNorm (u n a - u' a) 2 (volume.restrict C)) atTop (𝓝 0)

/-- The distributional torsion pairing `⟨d e + ω ∧ e, φ⟩_{ab}`. -/
def torsionPairing (act : A →L[ℝ] V →L[ℝ] V) (e : Fin d → (Fin d → ℝ) → V)
    (ω : Fin d → (Fin d → ℝ) → A) (φ : (Fin d → ℝ) → ℝ) (a b : Fin d) : V :=
  -(∫ x, pderiv a φ x • e b x) + (∫ x, pderiv b φ x • e a x) +
    ((∫ x, φ x • act (ω a x) (e b x)) - ∫ x, φ x • act (ω b x) (e a x))

/-- The represented connection `ω` is torsion-free for the coframe `e` in distributions on `Ω`:
`d e + ω ∧ e = 0` tested against every `φ ∈ 𝓓(Ω)`. -/
def IsTorsionFree (act : A →L[ℝ] V →L[ℝ] V) (Ω : Opens (Fin d → ℝ))
    (e : Fin d → (Fin d → ℝ) → V) (ω : Fin d → (Fin d → ℝ) → A) : Prop :=
  ∀ φ : 𝓓(Ω, ℝ), ∀ a b, torsionPairing act e ω φ a b = 0

theorem tendsto_integral_smul_of_L2' {X : Type*} [MeasurableSpace X] {ν : Measure X}
    [IsFiniteMeasure ν] {ψ : X → ℝ} (hψ : AEStronglyMeasurable ψ ν) {M : ℝ}
    (hM : ∀ x, ‖ψ x‖ ≤ M) {u : ℕ → X → V} {u' : X → V} (hu : ∀ n, MemLp (u n) 2 ν)
    (hu' : MemLp u' 2 ν) (hlim : Tendsto (fun n => eLpNorm (u n - u') 2 ν) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, ψ x • u n x ∂ν) atTop (𝓝 (∫ x, ψ x • u' x ∂ν)) := by
  have hψ2 : MemLp ψ 2 ν := MemLp.of_bound hψ M (Eventually.of_forall hM)
  let L := ContinuousLinearMap.lpPairing ν 2 2 (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] V →L[ℝ] V)
  have hU : Tendsto (fun n => (hu n).toLp (u n)) atTop (𝓝 (hu'.toLp u')) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ _ _ _).2 hlim
  have h := ((L (hψ2.toLp ψ)).continuous.tendsto _).comp hU
  have heq : ∀ (v : X → V) (hv : MemLp v 2 ν), L (hψ2.toLp ψ) (hv.toLp v) = ∫ x, ψ x • v x ∂ν := by
    intro v hv
    rw [ContinuousLinearMap.lpPairing_eq_integral]
    apply integral_congr_ae
    filter_upwards [hψ2.coeFn_toLp, hv.coeFn_toLp] with x h1 h2
    simp [h1, h2]
  rw [heq] at h
  exact h.congr fun n => heq _ _

/-- **Strong limits pass through the distributional torsion.**  If `e_n → e` and `ω_n → ω`
strongly in `L²_loc(Ω)`, then `⟨d e_n + ω_n ∧ e_n, φ⟩ → ⟨d e + ω ∧ e, φ⟩` for every test
function `φ ∈ 𝓓(Ω)`. -/
theorem tendsto_torsionPairing (act : A →L[ℝ] V →L[ℝ] V) {Ω : Opens (Fin d → ℝ)}
    {e : ℕ → Fin d → (Fin d → ℝ) → V} {e' : Fin d → (Fin d → ℝ) → V}
    {ω : ℕ → Fin d → (Fin d → ℝ) → A} {ω' : Fin d → (Fin d → ℝ) → A}
    (he : L2LocTendsto Ω e e') (hω : L2LocTendsto Ω ω ω') (φ : 𝓓(Ω, ℝ)) (a b : Fin d) :
    Tendsto (fun n => torsionPairing act (e n) (ω n) φ a b) atTop
      (𝓝 (torsionPairing act e' ω' φ a b)) := by
  set C := tsupport (φ : (Fin d → ℝ) → ℝ)
  have hC : IsCompact C := φ.hasCompactSupport
  have hCΩ : C ⊆ Ω := φ.tsupport_subset
  have : IsFiniteMeasure (volume.restrict C) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hC.measure_lt_top⟩
  have hloc : ∀ (ψ : (Fin d → ℝ) → ℝ) (F : (Fin d → ℝ) → V), (∀ x, x ∉ C → ψ x = 0) →
      ∫ x, ψ x • F x = ∫ x in C, ψ x • F x := fun ψ F hψ =>
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      rw [hψ x hx, zero_smul]).symm
  obtain ⟨M0, hM0⟩ := exists_bound_of_eq_zero_off φ.continuous hC fun x hx =>
    test_eq_zero_off φ hx
  have hd : ∀ c, ∃ M, ∀ x, ‖pderiv c φ x‖ ≤ M := fun c =>
    exists_bound_of_eq_zero_off (continuous_pderiv φ c) hC fun x hx => pderiv_eq_zero_off φ c hx
  obtain ⟨Ma, hMa⟩ := hd a
  obtain ⟨Mb, hMb⟩ := hd b
  have t1 := tendsto_integral_smul_of_L2' (continuous_pderiv φ a).aestronglyMeasurable hMa
    (fun n => he.memLp n b C hC hCΩ) (he.memLp_lim b C hC hCΩ) (he.tendsto b C hC hCΩ)
  have t2 := tendsto_integral_smul_of_L2' (continuous_pderiv φ b).aestronglyMeasurable hMb
    (fun n => he.memLp n a C hC hCΩ) (he.memLp_lim a C hC hCΩ) (he.tendsto a C hC hCΩ)
  have t3 := tendsto_integral_smul_bilin_of_L2 act φ.continuous.aestronglyMeasurable hM0
    (fun n => hω.memLp n a C hC hCΩ) (fun n => he.memLp n b C hC hCΩ)
    (hω.memLp_lim a C hC hCΩ) (he.memLp_lim b C hC hCΩ) (hω.tendsto a C hC hCΩ)
    (he.tendsto b C hC hCΩ)
  have t4 := tendsto_integral_smul_bilin_of_L2 act φ.continuous.aestronglyMeasurable hM0
    (fun n => hω.memLp n b C hC hCΩ) (fun n => he.memLp n a C hC hCΩ)
    (hω.memLp_lim b C hC hCΩ) (he.memLp_lim a C hC hCΩ) (hω.tendsto b C hC hCΩ)
    (he.tendsto a C hC hCΩ)
  have hza : ∀ c, ∀ x, x ∉ C → pderiv c φ x = 0 := fun c x hx => pderiv_eq_zero_off φ c hx
  have hz0 : ∀ x, x ∉ C → φ x = 0 := fun x hx => test_eq_zero_off φ hx
  unfold torsionPairing
  simp only [hloc _ _ (hza a), hloc _ _ (hza b), hloc _ _ hz0]
  exact (t1.neg.add t2).add (t3.sub t4)

/-- **Torsion-free limit** (torsion clause of `thm:supp-renewal-palatini`, full-connection
route): if `e_n → e`, `ω_n → ω` strongly in `L²_loc(Ω)` and the tested torsion residuals
`⟨d e_n + ω_n ∧ e_n, φ⟩` tend to zero for every test function, then the limiting represented
connection is torsion-free in distributions. -/
theorem isTorsionFree_of_tendsto (act : A →L[ℝ] V →L[ℝ] V) {Ω : Opens (Fin d → ℝ)}
    {e : ℕ → Fin d → (Fin d → ℝ) → V} {e' : Fin d → (Fin d → ℝ) → V}
    {ω : ℕ → Fin d → (Fin d → ℝ) → A} {ω' : Fin d → (Fin d → ℝ) → A}
    (he : L2LocTendsto Ω e e') (hω : L2LocTendsto Ω ω ω')
    (hres : ∀ φ : 𝓓(Ω, ℝ), ∀ a b,
      Tendsto (fun n => torsionPairing act (e n) (ω n) φ a b) atTop (𝓝 0)) :
    IsTorsionFree act Ω e' ω' := fun φ a b =>
  tendsto_nhds_unique (tendsto_torsionPairing act he hω φ a b) (hres φ a b)

/-- Non-vacuity: the zero coframe and connection (connection values acting on `ℝ⁴` as
endomorphisms) are torsion-free. -/
example (Ω : Opens (Fin 4 → ℝ)) :
    IsTorsionFree (ContinuousLinearMap.id ℝ ((Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ)))
      Ω (fun _ _ => (0 : Fin 4 → ℝ)) (fun _ _ => (0 : (Fin 4 → ℝ) →L[ℝ] (Fin 4 → ℝ))) := by
  intro φ a b
  simp [torsionPairing]

end RenewalGeometry.DistributionalTorsion
