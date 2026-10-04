/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.NativeYangMillsIdentification
import RenewalGeometry.OperatorLimits.VariableTorusDiracEstimates

/-!
# `C²` test fields on `𝕋⁴`, their nodal samples, and lattice shifts of raw reconstructions

Generic infrastructure (no renewal notions) for test-uniform consistency statements of the
Einstein–SM action-closure manuscript (`prop:native-gravity-firstjet`: `sup_{‖k‖_{C^r} ≤ 1}`), in
the unit-torus rendering of `Continuum/TorusTrigReconstruction.lean` (grid `(ℤ/N)⁴`, mesh
`h = 1/N`, nodes `samplePt x = x/N`, raw reconstruction `pc`).

* `C2Test F`: an `F`-valued test field on `𝕋⁴` with continuous coordinate partial derivatives up
  to order two (every smooth periodic test is one), with the `C²` norm
  `‖k‖_{C²} = sup‖k‖ + Σ_μ sup‖∂_μk‖ + Σ_{μν} sup‖∂_μ∂_νk‖` (`C2Test.norm`).
* Quantitative sampling estimates: Lipschitz bounds along lines and between arbitrary points
  (`norm_f_sub_le_of_coord`, `norm_df_sub_le_of_coord`, coordinatewise distance `δ`), and the
  finite-difference consistency `‖s⁻¹(k(y + s e_μ) - k(y)) - ∂_μk(y)‖ ≤ s ‖∂_μ²k‖`
  (`norm_fd_sub_le`).
* `integral_pc`: `∫ R^0 G = N⁻⁴ Σ_x G(x)` (vector-valued).
* `LpTendsto.shiftInt`: integer lattice shifts of a strongly `L^p`-convergent sequence of raw
  reconstructions have the same limit; `LpTendsto.pi`: componentwise strong convergence of
  finitely many components gives strong convergence of the tuple.
-/

open MeasureTheory Set Finset Filter Topology UnitAddTorus
open scoped BigOperators Real ENNReal

namespace RenewalGeometry.TorusC2Tests

open TorusPiecewiseConstantTranslation NativeYMIdentification

noncomputable section

set_option linter.unusedSectionVars false

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance : (volume : Measure UnitAddCircle).IsAddHaarMeasure :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

/-- The coordinate translation `y ↦ y + s e_μ` on `𝕋⁴`. -/
abbrev cpt (μ : Fin 4) (s : ℝ) : UnitAddTorus (Fin 4) := KolmogorovRieszTorus.coordPt μ s

theorem cpt_zero (μ : Fin 4) : cpt μ 0 = 0 := by
  simp [cpt, KolmogorovRieszTorus.coordPt]

theorem cpt_add (μ : Fin 4) (a b : ℝ) : cpt μ a + cpt μ b = cpt μ (a + b) :=
  TorusPiecewiseConstantTranslation.coordPt_add μ a b

/-! ### `C²` test fields -/

section Tests

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A `C²` test field on `𝕋⁴`: continuous values, first and second coordinate partial
derivatives. -/
structure C2Test (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] where
  /-- the field `k` -/
  f : C(UnitAddTorus (Fin 4), F)
  /-- the partial derivatives `df μ = ∂_μ k` -/
  df : Fin 4 → C(UnitAddTorus (Fin 4), F)
  /-- the second partial derivatives `ddf μ ν = ∂_μ ∂_ν k` -/
  ddf : Fin 4 → Fin 4 → C(UnitAddTorus (Fin 4), F)
  hasDerivAt_f : ∀ μ y, HasDerivAt (fun s : ℝ => f (y + cpt μ s)) (df μ y) 0
  hasDerivAt_df : ∀ μ ν y, HasDerivAt (fun s : ℝ => df ν (y + cpt μ s)) (ddf μ ν y) 0

namespace C2Test

/-- The `C²` norm `sup‖k‖ + Σ_μ sup‖∂_μk‖ + Σ_{μν} sup‖∂_μ∂_νk‖`. -/
def norm (k : C2Test F) : ℝ := ‖k.f‖ + ∑ μ, ‖k.df μ‖ + ∑ μ, ∑ ν, ‖k.ddf μ ν‖

theorem norm_nonneg (k : C2Test F) : 0 ≤ k.norm := by
  unfold norm; positivity

theorem sum_df_le (k : C2Test F) : ∑ μ, ‖k.df μ‖ ≤ k.norm := by
  unfold norm
  have : 0 ≤ ∑ μ, ∑ ν, ‖k.ddf μ ν‖ := by positivity
  linarith [_root_.norm_nonneg k.f]

theorem df_le (k : C2Test F) (μ : Fin 4) : ‖k.df μ‖ ≤ k.norm :=
  (Finset.single_le_sum (f := fun μ => ‖k.df μ‖) (fun _ _ => _root_.norm_nonneg _)
    (Finset.mem_univ μ)).trans k.sum_df_le

theorem f_le (k : C2Test F) : ‖k.f‖ ≤ k.norm := by
  unfold norm
  have : 0 ≤ ∑ μ, ∑ ν, ‖k.ddf μ ν‖ := by positivity
  have : 0 ≤ ∑ μ, ‖k.df μ‖ := by positivity
  linarith

theorem sum_ddf_le (k : C2Test F) (ν : Fin 4) : ∑ μ, ‖k.ddf μ ν‖ ≤ k.norm := by
  unfold norm
  have h1 : ∑ μ, ‖k.ddf μ ν‖ ≤ ∑ μ, ∑ ν, ‖k.ddf μ ν‖ :=
    Finset.sum_le_sum fun μ _ => Finset.single_le_sum (f := fun ν => ‖k.ddf μ ν‖)
      (fun _ _ => _root_.norm_nonneg _) (Finset.mem_univ ν)
  have : 0 ≤ ∑ μ, ‖k.df μ‖ := by positivity
  linarith [_root_.norm_nonneg k.f]

theorem ddf_le (k : C2Test F) (μ ν : Fin 4) : ‖k.ddf μ ν‖ ≤ k.norm :=
  (Finset.single_le_sum (f := fun μ => ‖k.ddf μ ν‖) (fun _ _ => _root_.norm_nonneg _)
    (Finset.mem_univ μ)).trans (k.sum_ddf_le ν)

theorem hasDerivAt_line_f (k : C2Test F) (μ : Fin 4) (y : UnitAddTorus (Fin 4)) (s : ℝ) :
    HasDerivAt (fun u : ℝ => k.f (y + cpt μ u)) (k.df μ (y + cpt μ s)) s := by
  have h := k.hasDerivAt_f μ (y + cpt μ s)
  have h' : HasDerivAt (fun r : ℝ => k.f (y + cpt μ (s + r))) (k.df μ (y + cpt μ s)) (s - s) := by
    rw [sub_self]
    refine h.congr_of_eventuallyEq (Eventually.of_forall fun r => ?_)
    simp only [add_assoc, cpt_add]
  have := h'.comp_sub_const s s
  simpa only [add_sub_cancel] using this

theorem hasDerivAt_line_df (k : C2Test F) (μ ν : Fin 4) (y : UnitAddTorus (Fin 4)) (s : ℝ) :
    HasDerivAt (fun u : ℝ => k.df ν (y + cpt μ u)) (k.ddf μ ν (y + cpt μ s)) s := by
  have h := k.hasDerivAt_df μ ν (y + cpt μ s)
  have h' : HasDerivAt (fun r : ℝ => k.df ν (y + cpt μ (s + r))) (k.ddf μ ν (y + cpt μ s))
      (s - s) := by
    rw [sub_self]
    refine h.congr_of_eventuallyEq (Eventually.of_forall fun r => ?_)
    simp only [add_assoc, cpt_add]
  have := h'.comp_sub_const s s
  simpa only [add_sub_cancel] using this

/-- Lipschitz bound along a coordinate line. -/
theorem norm_f_add_sub_le (k : C2Test F) (μ : Fin 4) (y : UnitAddTorus (Fin 4)) (s : ℝ) :
    ‖k.f (y + cpt μ s) - k.f y‖ ≤ |s| * ‖k.df μ‖ := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := fun u : ℝ => k.f (y + cpt μ u))
    (s := univ) (x := 0) (y := s) (C := ‖k.df μ‖)
    (fun u _ => (k.hasDerivAt_line_f μ y u).differentiableAt)
    (fun u _ => by rw [(k.hasDerivAt_line_f μ y u).deriv]; exact (k.df μ).norm_coe_le_norm _)
    convex_univ (mem_univ _) (mem_univ _)
  simpa [cpt_zero, Real.norm_eq_abs, mul_comm] using h

theorem norm_df_add_sub_le (k : C2Test F) (μ ν : Fin 4) (y : UnitAddTorus (Fin 4)) (s : ℝ) :
    ‖k.df ν (y + cpt μ s) - k.df ν y‖ ≤ |s| * ‖k.ddf μ ν‖ := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := fun u : ℝ => k.df ν (y + cpt μ u))
    (s := univ) (x := 0) (y := s) (C := ‖k.ddf μ ν‖)
    (fun u _ => (k.hasDerivAt_line_df μ ν y u).differentiableAt)
    (fun u _ => by
      rw [(k.hasDerivAt_line_df μ ν y u).deriv]; exact (k.ddf μ ν).norm_coe_le_norm _)
    convex_univ (mem_univ _) (mem_univ _)
  simpa [cpt_zero, Real.norm_eq_abs, mul_comm] using h

/-- **Finite-difference consistency**: `‖s⁻¹(k(y + s e_μ) - k(y)) - ∂_μk(y)‖ ≤ s ‖∂_μ²k‖`. -/
theorem norm_fd_sub_le (k : C2Test F) (μ : Fin 4) (y : UnitAddTorus (Fin 4)) {s : ℝ}
    (hs : 0 < s) : ‖s⁻¹ • (k.f (y + cpt μ s) - k.f y) - k.df μ y‖ ≤ s * ‖k.ddf μ μ‖ := by
  set g : ℝ → F := fun u => k.f (y + cpt μ u) - u • k.df μ y
  have hg : ∀ u, HasDerivAt g (k.df μ (y + cpt μ u) - k.df μ y) u := by
    intro u
    have := (k.hasDerivAt_line_f μ y u).sub ((hasDerivAt_id u).smul_const (k.df μ y))
    rw [one_smul] at this
    exact this
  have hmv := Convex.norm_image_sub_le_of_norm_deriv_le (f := g) (s := Icc 0 s) (x := 0) (y := s)
    (C := s * ‖k.ddf μ μ‖) (fun u _ => (hg u).differentiableAt)
    (fun u hu => by
      rw [(hg u).deriv]
      refine (k.norm_df_add_sub_le μ μ y u).trans ?_
      rw [abs_of_nonneg hu.1]
      exact mul_le_mul_of_nonneg_right hu.2 (_root_.norm_nonneg _))
    (convex_Icc 0 s) ⟨le_rfl, hs.le⟩ ⟨hs.le, le_rfl⟩
  have e : s⁻¹ • (k.f (y + cpt μ s) - k.f y) - k.df μ y = s⁻¹ • (g s - g 0) := by
    simp only [g, cpt_zero, add_zero, zero_smul, sub_zero, smul_sub, smul_smul,
      inv_mul_cancel₀ hs.ne', one_smul]
    abel
  rw [e, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hs.le)]
  calc s⁻¹ * ‖g s - g 0‖ ≤ s⁻¹ * (s * ‖k.ddf μ μ‖ * ‖s - 0‖) :=
        mul_le_mul_of_nonneg_left hmv (by positivity)
    _ = s * ‖k.ddf μ μ‖ := by
        rw [sub_zero, Real.norm_of_nonneg hs.le]; field_simp

/-- Every displacement on `𝕋⁴` is a sum of four coordinate translations by representatives of
the coordinate differences. -/
theorem exists_coord_decomp (y y' : UnitAddTorus (Fin 4)) :
    ∃ t : Fin 4 → ℝ, (∀ i, |t i| = ‖y' i - y i‖) ∧
      y' = y + cpt 0 (t 0) + cpt 1 (t 1) + cpt 2 (t 2) + cpt 3 (t 3) := by
  have hrep : ∀ i, ∃ r : ℝ, ((r : ℝ) : UnitAddCircle) = y' i - y i ∧ |r| = ‖y' i - y i‖ := by
    intro i
    obtain ⟨r, hr⟩ := QuotientAddGroup.mk_surjective (y' i - y i)
    refine ⟨r - round r, ?_, ?_⟩
    · have : ((r - round r : ℝ) : UnitAddCircle) = (r : UnitAddCircle) := by
        rw [AddCircle.coe_sub]
        have : ((round r : ℝ) : UnitAddCircle) = 0 := by
          rw [AddCircle.coe_eq_zero_iff]; exact ⟨round r, by simp⟩
        rw [this, sub_zero]
      rw [this]; exact hr
    · rw [← hr]
      exact (UnitAddCircle.norm_eq (x := r)).symm
  choose t ht1 ht2 using hrep
  refine ⟨t, ht2, ?_⟩
  funext i
  fin_cases i <;>
    simp [cpt, KolmogorovRieszTorus.coordPt, Pi.single_apply, ht1]

/-- Lipschitz bound between two points with coordinate distance `≤ δ`. -/
theorem norm_f_sub_le_of_coord (k : C2Test F) {y y' : UnitAddTorus (Fin 4)} {δ : ℝ}
    (hδ : ∀ i, ‖y' i - y i‖ ≤ δ) : ‖k.f y' - k.f y‖ ≤ δ * ∑ μ, ‖k.df μ‖ := by
  obtain ⟨t, ht, rfl⟩ := exists_coord_decomp y y'
  have hb : ∀ i, |t i| ≤ δ := fun i => (ht i).le.trans (by simpa using hδ i)
  set y1 := y + cpt 0 (t 0)
  set y2 := y1 + cpt 1 (t 1)
  set y3 := y2 + cpt 2 (t 2)
  have e : k.f (y3 + cpt 3 (t 3)) - k.f y = (k.f (y3 + cpt 3 (t 3)) - k.f y3) +
      (k.f (y2 + cpt 2 (t 2)) - k.f y2) + (k.f (y1 + cpt 1 (t 1)) - k.f y1) +
      (k.f (y + cpt 0 (t 0)) - k.f y) := by
    simp only [y1, y2, y3]; abel
  rw [e, Fin.sum_univ_four]
  have h0 := (k.norm_f_add_sub_le 0 y (t 0)).trans (mul_le_mul_of_nonneg_right (hb 0)
    (_root_.norm_nonneg _))
  have h1 := (k.norm_f_add_sub_le 1 y1 (t 1)).trans (mul_le_mul_of_nonneg_right (hb 1)
    (_root_.norm_nonneg _))
  have h2 := (k.norm_f_add_sub_le 2 y2 (t 2)).trans (mul_le_mul_of_nonneg_right (hb 2)
    (_root_.norm_nonneg _))
  have h3 := (k.norm_f_add_sub_le 3 y3 (t 3)).trans (mul_le_mul_of_nonneg_right (hb 3)
    (_root_.norm_nonneg _))
  calc _ ≤ ‖k.f (y3 + cpt 3 (t 3)) - k.f y3‖ + ‖k.f (y2 + cpt 2 (t 2)) - k.f y2‖ +
        ‖k.f (y1 + cpt 1 (t 1)) - k.f y1‖ + ‖k.f (y + cpt 0 (t 0)) - k.f y‖ := norm_add₄_le
    _ ≤ _ := by nlinarith

theorem norm_df_sub_le_of_coord (k : C2Test F) (ν : Fin 4) {y y' : UnitAddTorus (Fin 4)} {δ : ℝ}
    (hδ : ∀ i, ‖y' i - y i‖ ≤ δ) : ‖k.df ν y' - k.df ν y‖ ≤ δ * ∑ μ, ‖k.ddf μ ν‖ := by
  obtain ⟨t, ht, rfl⟩ := exists_coord_decomp y y'
  have hb : ∀ i, |t i| ≤ δ := fun i => (ht i).le.trans (by simpa using hδ i)
  set y1 := y + cpt 0 (t 0)
  set y2 := y1 + cpt 1 (t 1)
  set y3 := y2 + cpt 2 (t 2)
  have e : k.df ν (y3 + cpt 3 (t 3)) - k.df ν y = (k.df ν (y3 + cpt 3 (t 3)) - k.df ν y3) +
      (k.df ν (y2 + cpt 2 (t 2)) - k.df ν y2) + (k.df ν (y1 + cpt 1 (t 1)) - k.df ν y1) +
      (k.df ν (y + cpt 0 (t 0)) - k.df ν y) := by
    simp only [y1, y2, y3]; abel
  rw [e, Fin.sum_univ_four]
  have h0 := (k.norm_df_add_sub_le 0 ν y (t 0)).trans (mul_le_mul_of_nonneg_right (hb 0)
    (_root_.norm_nonneg _))
  have h1 := (k.norm_df_add_sub_le 1 ν y1 (t 1)).trans (mul_le_mul_of_nonneg_right (hb 1)
    (_root_.norm_nonneg _))
  have h2 := (k.norm_df_add_sub_le 2 ν y2 (t 2)).trans (mul_le_mul_of_nonneg_right (hb 2)
    (_root_.norm_nonneg _))
  have h3 := (k.norm_df_add_sub_le 3 ν y3 (t 3)).trans (mul_le_mul_of_nonneg_right (hb 3)
    (_root_.norm_nonneg _))
  calc _ ≤ ‖k.df ν (y3 + cpt 3 (t 3)) - k.df ν y3‖ + ‖k.df ν (y2 + cpt 2 (t 2)) - k.df ν y2‖ +
        ‖k.df ν (y1 + cpt 1 (t 1)) - k.df ν y1‖ + ‖k.df ν (y + cpt 0 (t 0)) - k.df ν y‖ :=
          norm_add₄_le
    _ ≤ _ := by nlinarith

end C2Test

end Tests

/-! ### Integrals of raw reconstructions -/

section Integral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- `∫ R^0 G = N⁻⁴ Σ_x G(x)`. -/
theorem integral_pc {N : ℕ} [NeZero N] (G : (Fin 4 → ZMod N) → E) :
    ∫ y, pc G y = ((N : ℝ) ^ 4)⁻¹ • ∑ g, G g := by
  rw [pc_eq_sum_indicator]
  simp only [Finset.sum_apply]
  rw [integral_finset_sum _ fun g _ =>
    (integrable_const (G g)).indicator (measurableSet_cellD g)]
  simp_rw [integral_indicator_const _ (measurableSet_cellD _)]
  have hv : ∀ g : Fin 4 → ZMod N, (volume : Measure (UnitAddTorus (Fin 4))).real (cellD g) =
      ((N : ℝ) ^ 4)⁻¹ := by
    intro g
    rw [Measure.real_def, volume_cellD, ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity),
      Fintype.card_fin, one_div, inv_pow]
  simp only [hv, Finset.smul_sum]

end Integral

/-! ### Lattice shifts and finite tuples under strong convergence -/

section Shifts

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n : ℕ → ℕ} [∀ k, NeZero (n k)]

theorem tendsto_cpt_int (hn : Tendsto n atTop atTop) (μ : Fin 4) (m : ℤ) :
    Tendsto (fun k => cpt μ ((m : ℝ) / (n k : ℝ))) atTop (𝓝 0) := by
  have h0 : Tendsto (fun k => ((m : ℝ) / (n k : ℝ))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hn)
  have hc : Continuous fun s : ℝ => (Pi.single μ (s : UnitAddCircle) : UnitAddTorus (Fin 4)) :=
    continuous_pi fun i => by
      by_cases h : i = μ
      · subst h; simpa using QuotientAddGroup.continuous_mk
      · simp only [Pi.single_eq_of_ne h]; exact continuous_const
  have := (hc.tendsto 0).comp h0
  have h1 : (Pi.single μ ((0 : ℝ) : UnitAddCircle) : UnitAddTorus (Fin 4)) = 0 := by simp
  rw [h1] at this
  exact this

/-- Integer lattice shifts of a strongly convergent sequence of raw reconstructions have the same
limit. -/
theorem _root_.RenewalGeometry.LpTendsto.shiftInt (hn : Tendsto n atTop atTop) {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (hp : p ≠ ∞) {v : ∀ k, (Fin 4 → ZMod (n k)) → E}
    {g : UnitAddTorus (Fin 4) → E} (hv : LpTendsto volume p (fun k => pc (v k)) g) (μ : Fin 4)
    (m : ℤ) : LpTendsto volume p (fun k => pc (shift μ m (v k))) g := by
  refine ⟨fun k => memLp_pc_gen _ p, hv.memLp_lim, ?_⟩
  have htr := (transl_tendsto hp hv.memLp_lim).comp (tendsto_cpt_int hn μ m)
  have hup := hv.tendsto.add htr
  rw [zero_add] at hup
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun k => zero_le)
    fun k => ?_
  set z := cpt μ ((m : ℝ) / (n k : ℝ))
  have hsplit : pc (shift μ m (v k)) - g = (fun y => (pc (v k) - g) (y + z)) +
      fun y => g (y + z) - g y := by
    funext y
    simp only [Pi.sub_apply, Pi.add_apply, z, cpt, ← pc_add_coordPt_int]
    abel
  rw [hsplit]
  have hm := (hv.memLp k).1.sub hv.memLp_lim.1
  refine (eLpNorm_add_le (hm.comp_measurePreserving (measurePreserving_add_right volume z))
    ((hv.memLp_lim.1.comp_measurePreserving (measurePreserving_add_right volume z)).sub
      hv.memLp_lim.1) Fact.out).trans (le_of_eq ?_)
  congr 1
  exact eLpNorm_comp_measurePreserving hm (measurePreserving_add_right volume z)

end Shifts

section Pi

variable {X : Type*} [MeasurableSpace X] {ν : Measure X} {ι : Type*} [Fintype ι]
variable {E : Type*} [NormedAddCommGroup E]

theorem norm_pi_le_sum (f : ι → E) : ‖f‖ ≤ ∑ i, ‖f i‖ :=
  (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)).2 fun i =>
    Finset.single_le_sum (f := fun i => ‖f i‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i)

/-- Strong convergence of finitely many components gives strong convergence of the tuple. -/
theorem _root_.RenewalGeometry.LpTendsto.pi {p : ℝ≥0∞} [Fact (1 ≤ p)] {u : ℕ → X → ι → E}
    {u₀ : X → ι → E} (h : ∀ i, LpTendsto ν p (fun k x => u k x i) (fun x => u₀ x i)) :
    LpTendsto ν p u u₀ := by
  refine ⟨fun k => memLp_pi_iff.2 fun i => (h i).memLp k,
    memLp_pi_iff.2 fun i => (h i).memLp_lim, ?_⟩
  have hsum : Tendsto (fun k => ∑ i, eLpNorm ((fun x => u k x i) - fun x => u₀ x i) p ν) atTop
      (𝓝 0) := by
    simpa using tendsto_finsetSum (Finset.univ : Finset ι) fun i _ => (h i).tendsto
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun k => zero_le)
    fun k => ?_
  have hm : ∀ i, AEStronglyMeasurable ((fun x => u k x i) - fun x => u₀ x i) ν := fun i =>
    ((h i).memLp k).1.sub (h i).memLp_lim.1
  calc eLpNorm (u k - u₀) p ν ≤ eLpNorm (fun x => ∑ i, ‖u k x i - u₀ x i‖) p ν := by
        refine eLpNorm_mono fun x => ?_
        rw [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)]
        exact norm_pi_le_sum _
    _ = eLpNorm (∑ i, fun x => ‖((fun x => u k x i) - fun x => u₀ x i) x‖) p ν := by
        congr 1; funext x; simp only [Finset.sum_apply, Pi.sub_apply]
    _ ≤ ∑ i, eLpNorm (fun x => ‖((fun x => u k x i) - fun x => u₀ x i) x‖) p ν :=
        eLpNorm_sum_le (fun i _ => (hm i).norm) Fact.out
    _ = ∑ i, eLpNorm ((fun x => u k x i) - fun x => u₀ x i) p ν := by
        refine Finset.sum_congr rfl fun i _ => eLpNorm_norm _

end Pi

/-! ### Sampling a test at lattice points near a point -/

section Sampling

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem lineVec_eq_cpt (μ : Fin 4) (t : ℝ) : VariableTorusDirac.lineVec μ t = cpt μ t := rfl

/-- The lattice point of the cell of `y`, and its unit neighbours, are within coordinate distance
`2/N` of `y`. -/
theorem norm_samplePt_index_add_sub_le {N : ℕ} [NeZero N] (y : UnitAddTorus (Fin 4))
    (g : Fin 4 → ZMod N) (hg : g = 0 ∨ ∃ μ, g = Pi.single μ 1 ∨ g = -Pi.single μ 1)
    (i : Fin 4) :
    ‖TorusCellEmbedding.samplePt (index N y + g) i - y i‖ ≤ 2 * (N : ℝ)⁻¹ := by
  have h0 : ‖y i - TorusCellEmbedding.samplePt (TorusCellEmbedding.index N y) i‖ ≤ (N : ℝ)⁻¹ :=
    VariableTorusDirac.norm_sub_samplePt_index_le y i
  have hidx : index N y = TorusCellEmbedding.index N y := rfl
  have hN : (0 : ℝ) ≤ (N : ℝ)⁻¹ := by positivity
  rcases hg with rfl | ⟨μ, rfl | rfl⟩
  · rw [add_zero, hidx, ← norm_neg, neg_sub]; linarith
  · rw [hidx, VariableTorusDirac.samplePt_add_single]
    have h1 := VariableTorusDirac.norm_lineVec_apply_le μ i (N : ℝ)⁻¹
    calc ‖(TorusCellEmbedding.samplePt (TorusCellEmbedding.index N y) +
          VariableTorusDirac.lineVec μ (N : ℝ)⁻¹) i - y i‖
        = ‖VariableTorusDirac.lineVec μ (N : ℝ)⁻¹ i -
            (y i - TorusCellEmbedding.samplePt (TorusCellEmbedding.index N y) i)‖ := by
          congr 1; simp only [Pi.add_apply]; abel
      _ ≤ _ := (norm_sub_le _ _).trans (by rw [abs_of_nonneg hN] at h1; linarith)
  · rw [hidx, ← sub_eq_add_neg, VariableTorusDirac.samplePt_sub_single]
    have h1 := VariableTorusDirac.norm_lineVec_apply_le μ i (-(N : ℝ)⁻¹)
    calc ‖(TorusCellEmbedding.samplePt (TorusCellEmbedding.index N y) +
          VariableTorusDirac.lineVec μ (-(N : ℝ)⁻¹)) i - y i‖
        = ‖VariableTorusDirac.lineVec μ (-(N : ℝ)⁻¹) i -
            (y i - TorusCellEmbedding.samplePt (TorusCellEmbedding.index N y) i)‖ := by
          congr 1; simp only [Pi.add_apply]; abel
      _ ≤ _ := (norm_sub_le _ _).trans (by rw [abs_neg, abs_of_nonneg hN] at h1; linarith)

/-- A sampled test value near `y`. -/
theorem norm_f_samplePt_sub_le (k : C2Test F) {N : ℕ} [NeZero N] (y : UnitAddTorus (Fin 4))
    (g : Fin 4 → ZMod N) {δ : ℝ} (hg : ∀ i, ‖TorusCellEmbedding.samplePt g i - y i‖ ≤ δ) :
    ‖k.f (TorusCellEmbedding.samplePt g) - k.f y‖ ≤ δ * k.norm := by
  have hδ : 0 ≤ δ := (norm_nonneg _).trans (hg 0)
  exact (k.norm_f_sub_le_of_coord hg).trans (mul_le_mul_of_nonneg_left k.sum_df_le hδ)

/-- A sampled finite difference of a test near `y`:
`‖N(k(x/N + e_λ/N) - k(x/N)) - ∂_λ k(y)‖ ≤ (1/N + δ) ‖k‖_{C²}`. -/
theorem norm_fd_samplePt_sub_le (k : C2Test F) {N : ℕ} [NeZero N] (y : UnitAddTorus (Fin 4))
    (g : Fin 4 → ZMod N) (lam : Fin 4) {δ : ℝ}
    (hg : ∀ i, ‖TorusCellEmbedding.samplePt g i - y i‖ ≤ δ) :
    ‖(N : ℝ) • (k.f (TorusCellEmbedding.samplePt (g + Pi.single lam 1)) -
        k.f (TorusCellEmbedding.samplePt g)) - k.df lam y‖ ≤ ((N : ℝ)⁻¹ + δ) * k.norm := by
  have hδ : 0 ≤ δ := (norm_nonneg _).trans (hg 0)
  have hN : (0 : ℝ) < (N : ℝ)⁻¹ := by
    have : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    positivity
  rw [VariableTorusDirac.samplePt_add_single, lineVec_eq_cpt]
  set z := TorusCellEmbedding.samplePt g
  have h1 := k.norm_fd_sub_le lam z hN
  rw [inv_inv] at h1
  have h2 : ‖k.df lam z - k.df lam y‖ ≤ δ * ∑ μ, ‖k.ddf μ lam‖ := k.norm_df_sub_le_of_coord lam hg
  calc ‖(N : ℝ) • (k.f (z + cpt lam (N : ℝ)⁻¹) - k.f z) - k.df lam y‖
      = ‖((N : ℝ) • (k.f (z + cpt lam (N : ℝ)⁻¹) - k.f z) - k.df lam z) +
          (k.df lam z - k.df lam y)‖ := by congr 1; abel
    _ ≤ (N : ℝ)⁻¹ * ‖k.ddf lam lam‖ + δ * ∑ μ, ‖k.ddf μ lam‖ := (norm_add_le _ _).trans
        (add_le_add h1 h2)
    _ ≤ (N : ℝ)⁻¹ * k.norm + δ * k.norm := add_le_add
        (mul_le_mul_of_nonneg_left (k.ddf_le lam lam) hN.le)
        (mul_le_mul_of_nonneg_left (k.sum_ddf_le lam) hδ)
    _ = _ := by ring

end Sampling

end

end RenewalGeometry.TorusC2Tests
