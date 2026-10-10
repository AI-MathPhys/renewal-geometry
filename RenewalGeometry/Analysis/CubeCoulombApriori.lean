/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.CubeGaffney

/-!
# The critical Coulomb a-priori estimate on the cube with the Neumann condition
  (stage A4 of the cube rendering of Uhlenbeck's small-energy gauge theorem)

Generic infrastructure (no renewal notions) for `prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript (K. Uhlenbeck, CMP 83 (1982), Thm 1.3, the
"closedness" estimate of the continuity method, on a domain: the Coulomb gauge `d^*A = 0` in
`Q₀` with `A·ν = 0` on `∂Q₀`).

Matrix-valued one-forms on `Q₀ = (0,1/2)⁴` are given entrywise, `b ν c e`, with weak partials
`db ν c e μ = ∂_μ b_{ν,ce}`; the curvature is `cCurv b db μ ν = ∂_μ b_ν - ∂_ν b_μ + [b_μ, b_ν]`.

* `IsNeumannMH1 b db`: every entry is in the Neumann class `IsNeumannH1` (vanishing normal
  component on the faces, expressed through the reflection);
* `CubeCoulomb db`: `Σ_μ ∂_μ b_μ = 0` a.e. on `Q₀`;
* `extF`, `extG`, `tCurv_ext` (the torus curvature of the reflected form is the reflection of the
  cube curvature, pattern `{μ} ∆ {ν}`), `gradNorm_ext`, `curvNorm_ext` (factor `4`);
* `coulomb_apriori_cube` (**Coulomb a-priori estimate on the cube**): there is `δ(m) > 0` such
  that every Neumann, Coulomb one-form on `Q₀` with `‖∇b‖_{L²(Q₀)} ≤ δ` satisfies
  `‖∇b‖_{L²(Q₀)} ≤ 32 m² ‖F_b‖_{L²(Q₀)}`, `‖b‖_{L²(Q₀)} ≤ 32 m² ‖F_b‖_{L²(Q₀)}` and
  `‖b‖_{L⁴(Q₀)} ≤ 448 m² ‖F_b‖_{L²(Q₀)}` — **no mean-zero hypothesis** (there are no harmonic
  one-forms with vanishing normal component, `neumann_harmonic_cube`); `coulomb_apriori_gap_cube`
  is the first-exit gap.  Proof: reflection to `𝕋⁴` and `UhlenbeckTorus.coulomb_apriori_torus_L4`.
-/

open MeasureTheory Filter Topology Set UnitAddTorus
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace RenewalGeometry.CubeNeumann

open SobolevOpen TorusSobolev UhlenbeckTorus

set_option linter.unusedSectionVars false

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local notation "𝕋⁴" => UnitAddTorus (Fin 4)

variable {m : ℕ}

/-- Matrix-valued one-forms on the cube in the Neumann class (entrywise). -/
def IsNeumannMH1 (b : Fin 4 → Fin m → Fin m → (Fin 4 → ℝ) → ℂ)
    (db : Fin 4 → Fin m → Fin m → Fin 4 → (Fin 4 → ℝ) → ℂ) : Prop :=
  ∀ c e, IsNeumannH1 (fun ν => b ν c e) (fun ν μ => db ν c e μ)

/-- The Coulomb condition on the cube: `Σ_μ ∂_μ b_{μ,ce} = 0` a.e. on `Q₀`. -/
def CubeCoulomb (db : Fin 4 → Fin m → Fin m → Fin 4 → (Fin 4 → ℝ) → ℂ) : Prop :=
  ∀ c e, (fun x => ∑ μ, db μ c e μ x) =ᵐ[volume.restrict Q0] 0

/-- The curvature `F_{μν} = ∂_μ b_ν - ∂_ν b_μ + [b_μ, b_ν]` of a cube one-form (entries). -/
def cCurv (b : Fin 4 → Fin m → Fin m → (Fin 4 → ℝ) → ℂ)
    (db : Fin 4 → Fin m → Fin m → Fin 4 → (Fin 4 → ℝ) → ℂ) (μ ν : Fin 4) (c e : Fin m)
    (x : Fin 4 → ℝ) : ℂ :=
  db ν c e μ x - db μ c e ν x + ∑ k, (b μ c k x * b ν k e x - b ν c k x * b μ k e x)

/-- `Σ_{νceμ} ‖∂_μ b_{ν,ce}‖_{L²(Q₀)}`. -/
def cGradNorm (db : Fin 4 → Fin m → Fin m → Fin 4 → (Fin 4 → ℝ) → ℂ) : ℝ≥0∞ :=
  ∑ ν, ∑ c, ∑ e, ∑ μ, eLpNorm (db ν c e μ) 2 (volume.restrict Q0)

/-- `Σ_{μνce} ‖F_{μν,ce}‖_{L²(Q₀)}`. -/
def cCurvNorm (b : Fin 4 → Fin m → Fin m → (Fin 4 → ℝ) → ℂ)
    (db : Fin 4 → Fin m → Fin m → Fin 4 → (Fin 4 → ℝ) → ℂ) : ℝ≥0∞ :=
  ∑ μ, ∑ ν, ∑ c, ∑ e, eLpNorm (cCurv b db μ ν c e) 2 (volume.restrict Q0)

/-- The reflected one-form on `𝕋⁴`. -/
def extF (b : Fin 4 → Fin m → Fin m → (Fin 4 → ℝ) → ℂ) : Fin 4 → Fin m → Fin m → 𝕋⁴ → ℂ :=
  fun ν c e => parExt {ν} (b ν c e)

/-- The reflected gradient on `𝕋⁴`. -/
def extG (db : Fin 4 → Fin m → Fin m → Fin 4 → (Fin 4 → ℝ) → ℂ) :
    Fin 4 → Fin m → Fin m → Fin 4 → 𝕋⁴ → ℂ :=
  fun ν c e μ => parExt (symmDiff {ν} {μ}) (db ν c e μ)

theorem isH1Form_ext {b : Fin 4 → Fin m → Fin m → (Fin 4 → ℝ) → ℂ}
    {db : Fin 4 → Fin m → Fin m → Fin 4 → (Fin 4 → ℝ) → ℂ} (h : IsNeumannMH1 b db) :
    IsH1Form (extF b) (extG db) :=
  ⟨fun ν c e => (h c e).memLp_ext ν, fun ν c e μ => (h c e).memLp_ext_grad ν μ,
    fun ν c e μ => (h c e).hasPartial ν μ⟩

theorem ext_odd {b : Fin 4 → Fin m → Fin m → (Fin 4 → ℝ) → ℂ} (ν : Fin 4) (c e : Fin m) :
    ∀ᵐ x ∂volume, extF b ν c e (reflect ν x) = -extF b ν c e x := by
  filter_upwards [hasParity_parExt {ν} (b ν c e) ν] with x hx
  simp only [extF, hx, pSign, Finset.mem_singleton, if_true]; ring

theorem isCoulomb_ext {db : Fin 4 → Fin m → Fin m → Fin 4 → (Fin 4 → ℝ) → ℂ}
    (hC : CubeCoulomb db) : IsCoulomb (extG db) := by
  intro c e
  filter_upwards [parExt_ae_zero (S := ∅) (hC c e)] with t ht
  rw [parExt_finset_sum] at ht
  simp only [extG, symmDiff_self, Finset.bot_eq_empty]
  exact ht

theorem gradNorm_ext {b : Fin 4 → Fin m → Fin m → (Fin 4 → ℝ) → ℂ}
    {db : Fin 4 → Fin m → Fin m → Fin 4 → (Fin 4 → ℝ) → ℂ} (h : IsNeumannMH1 b db) :
    gradNorm (extG db) = 4 * cGradNorm db := by
  simp only [gradNorm, cGradNorm, extG, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun c _ =>
    Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun μ _ => ?_
  exact eLpNorm_parExt_two ((h c e).memLp_grad ν μ)

/-- The torus curvature of the reflected form is the reflection of the cube curvature. -/
theorem tCurv_ext (b : Fin 4 → Fin m → Fin m → (Fin 4 → ℝ) → ℂ)
    (db : Fin 4 → Fin m → Fin m → Fin 4 → (Fin 4 → ℝ) → ℂ) (μ ν : Fin 4) (c e : Fin m) :
    tCurv (extF b) (extG db) μ ν c e = parExt (symmDiff {μ} {ν}) (cCurv b db μ ν c e) := by
  funext t
  have hc : symmDiff ({ν} : Finset (Fin 4)) {μ} = symmDiff {μ} {ν} := symmDiff_comm _ _
  simp only [tCurv, extF, extG, parExt_mul, hc]
  have e : cCurv b db μ ν c e = fun x => (db ν c e μ x - db μ c e ν x) +
      ∑ k, (b μ c k x * b ν k e x - b ν c k x * b μ k e x) := rfl
  rw [e, parExt_add, parExt_sub, parExt_finset_sum]
  simp only [parExt_sub]

theorem memLp_cCurv {b : Fin 4 → Fin m → Fin m → (Fin 4 → ℝ) → ℂ}
    {db : Fin 4 → Fin m → Fin m → Fin 4 → (Fin 4 → ℝ) → ℂ} (h : IsNeumannMH1 b db)
    (μ ν : Fin 4) (c e : Fin m) : MemLp (cCurv b db μ ν c e) 2 (volume.restrict Q0) := by
  have h4 : ∀ ν c e, MemLp (b ν c e) 4 (volume.restrict Q0) := fun ν c e =>
    (sobolev_cube ((h c e).memW12 ν)).1
  unfold cCurv
  refine (((h c e).memLp_grad ν μ).sub ((h c e).memLp_grad μ ν)).add
    (memLp_finsetSum _ fun k _ => ?_)
  exact ((h4 ν k e).mul' (h4 μ c k) (r := 2)).sub ((h4 μ k e).mul' (h4 ν c k) (r := 2))

theorem curvNorm_ext {b : Fin 4 → Fin m → Fin m → (Fin 4 → ℝ) → ℂ}
    {db : Fin 4 → Fin m → Fin m → Fin 4 → (Fin 4 → ℝ) → ℂ} (h : IsNeumannMH1 b db) :
    curvNorm (extF b) (extG db) = 4 * cCurvNorm b db := by
  simp only [curvNorm, cCurvNorm, tCurv_ext, Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ =>
    Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun e _ => ?_
  exact eLpNorm_parExt_two (memLp_cCurv h μ ν c e)

/-- **The critical Coulomb a-priori estimate on the cube `Q₀` with the Neumann condition**
(Uhlenbeck's closedness estimate on a domain): there is `δ > 0` depending only on `m` such that
every matrix-valued one-form `b` on `Q₀` in the Neumann class (`b·ν = 0` on `∂Q₀`, through the
reflection), in Coulomb gauge on `Q₀`, with `‖∇b‖_{L²(Q₀)} ≤ δ`, satisfies
`‖∇b‖_{L²(Q₀)} ≤ 32 m² ‖F_b‖_{L²(Q₀)}`, `‖b_{ν,ce}‖_{L²(Q₀)} ≤ 32 m² ‖F_b‖_{L²(Q₀)}` and
`‖b_{ν,ce}‖_{L⁴(Q₀)} ≤ 448 m² ‖F_b‖_{L²(Q₀)}`.  No mean-zero hypothesis. -/
theorem coulomb_apriori_cube (m : ℕ) : ∃ δ : ℝ≥0, 0 < δ ∧
    ∀ (b : Fin 4 → Fin m → Fin m → (Fin 4 → ℝ) → ℂ)
      (db : Fin 4 → Fin m → Fin m → Fin 4 → (Fin 4 → ℝ) → ℂ),
      IsNeumannMH1 b db → CubeCoulomb db → cGradNorm db ≤ δ →
      cGradNorm db ≤ 32 * (m : ℝ≥0∞) ^ 2 * cCurvNorm b db ∧
      (∀ ν c e, eLpNorm (b ν c e) 2 (volume.restrict Q0) ≤ 32 * (m : ℝ≥0∞) ^ 2 * cCurvNorm b db) ∧
      (∀ ν c e, eLpNorm (b ν c e) 4 (volume.restrict Q0) ≤
        448 * (m : ℝ≥0∞) ^ 2 * cCurvNorm b db) := by
  obtain ⟨δ, hδ, hT⟩ := coulomb_apriori_torus_L4 m
  refine ⟨δ / 4, by positivity, fun b db hN hC hX => ?_⟩
  have hX' : gradNorm (extG db) ≤ δ := by
    rw [gradNorm_ext hN]
    calc 4 * cGradNorm db ≤ 4 * ((δ / 4 : ℝ≥0) : ℝ≥0∞) := by gcongr
      _ = δ := by
          rw [← ENNReal.coe_ofNat, ← ENNReal.coe_mul, mul_div_cancel₀ _ (by norm_num : (4 : ℝ≥0) ≠ 0)]
  have hmean : ∀ ν c e, mFourierCoeff (extF b ν c e) 0 = 0 := fun ν c e =>
    mFourierCoeff_zero_eq_zero_of_odd (ext_odd ν c e)
  obtain ⟨h1, h2, h3⟩ := hT (extF b) (extG db) (isH1Form_ext hN) hmean (isCoulomb_ext hC) hX'
  rw [gradNorm_ext hN, curvNorm_ext hN] at h1
  rw [curvNorm_ext hN] at h2 h3
  refine ⟨ennreal_cancel_four (h1.trans (le_of_eq (by ring))), fun ν c e => ?_, fun ν c e => ?_⟩
  · have := h2 ν c e
    rw [show extF b ν c e = parExt {ν} (b ν c e) from rfl,
      eLpNorm_parExt_two ((hN c e).memLp ν)] at this
    exact ennreal_cancel_four (this.trans (le_of_eq (by ring)))
  · have := h3 ν c e
    have hm4 : MemLp (b ν c e) 4 (volume.restrict Q0) := (sobolev_cube ((hN c e).memW12 ν)).1
    rw [show extF b ν c e = parExt {ν} (b ν c e) from rfl, eLpNorm_parExt_four hm4] at this
    have h' : 2 * eLpNorm (b ν c e) 4 (volume.restrict Q0) ≤
        2 * (448 * (m : ℝ≥0∞) ^ 2 * cCurvNorm b db) := this.trans (le_of_eq (by ring))
    exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).1 h'

/-- **The first-exit gap on the cube**: under the hypotheses of `coulomb_apriori_cube`, if also
`64 m² ‖F_b‖_{L²(Q₀)} ≤ δ`, then `‖∇b‖_{L²(Q₀)} ≤ δ/2`. -/
theorem coulomb_apriori_gap_cube (m : ℕ) : ∃ δ : ℝ≥0, 0 < δ ∧
    ∀ (b : Fin 4 → Fin m → Fin m → (Fin 4 → ℝ) → ℂ)
      (db : Fin 4 → Fin m → Fin m → Fin 4 → (Fin 4 → ℝ) → ℂ),
      IsNeumannMH1 b db → CubeCoulomb db → cGradNorm db ≤ δ →
      64 * (m : ℝ≥0∞) ^ 2 * cCurvNorm b db ≤ δ → cGradNorm db ≤ (δ : ℝ≥0∞) / 2 := by
  obtain ⟨δ, hδ, h⟩ := coulomb_apriori_cube m
  refine ⟨δ, hδ, fun b db hN hC hX hF => ?_⟩
  refine (h b db hN hC hX).1.trans ?_
  rw [ENNReal.le_div_iff_mul_le (by norm_num) (by norm_num)]
  calc (32 * (m : ℝ≥0∞) ^ 2 * cCurvNorm b db * 2 : ℝ≥0∞) =
        64 * (m : ℝ≥0∞) ^ 2 * cCurvNorm b db := by ring
    _ ≤ (δ : ℝ≥0∞) := hF

/-- Non-vacuity: the zero form satisfies the hypotheses of `coulomb_apriori_cube`. -/
example (m : ℕ) : IsNeumannMH1 (m := m) (fun _ _ _ _ => 0) (fun _ _ _ _ _ => 0) ∧
    CubeCoulomb (m := m) (fun _ _ _ _ _ => 0) := by
  refine ⟨fun c e => ⟨fun _ => MemLp.zero, fun _ _ => MemLp.zero, fun ν μ => ?_⟩,
    fun c e => Eventually.of_forall fun x => by simp⟩
  have e1 : parExt {ν} (fun _ : Fin 4 → ℝ => (0 : ℂ)) = fun _ => 0 := funext (parExt_zero _)
  have e2 : parExt (symmDiff {ν} {μ}) (fun _ : Fin 4 → ℝ => (0 : ℂ)) = fun _ => 0 :=
    funext (parExt_zero _)
  simp only [e1, e2]
  exact isTPartial_const μ 0

end RenewalGeometry.CubeNeumann
