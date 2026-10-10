/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.CubeNeumannSobolev

/-!
# Gaffney, Poincaré and critical Sobolev inequalities on the cube `Q₀ = (0,1/2)⁴`
  (stage A3 of the cube rendering of Uhlenbeck's small-energy gauge theorem)

Generic infrastructure (no renewal notions) for `prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript.

* `IsNeumannH1 b db`: the **Neumann class** `H¹_N(Q₀)` of one-forms on the cube with vanishing
  normal component on `∂Q₀`, defined through the reflection: the parity extension
  `ν ↦ parExt {ν} (b ν)` (normal component odd, tangential components even) is an `H¹(𝕋⁴)` one-form
  whose torus partials are the parity extensions `parExt ({ν} ∆ {μ}) (db ν μ)`.
  `IsNeumannH1.memW12`: Neumann forms are in `W^{1,2}(Q₀)` (weak derivatives of
  `SobolevOpen`); `IsNeumannH1.isNeumannForm`: their extensions are Neumann forms on `𝕋⁴`.
* algebra of parity extensions: `parExt_add`, `parExt_sub`, `parExt_const_mul`,
  `parExt_finset_sum`, `parExt_mul` (patterns add modulo 2), `parExt_conj`, `parExt_chart0`
  (restriction to `Q₀` returns the function), `eLpNorm_parExt_two` (factor `4`),
  `eLpNorm_parExt_four` (factor `2`), `parExt_ae_zero`.
* `gaffney_cube` (**Gaffney inequality on `Q₀`**, no boundary term since the faces are flat):
  `‖∂_μ b_ν‖_{L²(Q₀)} ≤ Σ_{μ'ν'} ‖∂_{μ'} b_{ν'} - ∂_{ν'} b_{μ'}‖_{L²(Q₀)} + ‖Σ_μ ∂_μ b_μ‖_{L²(Q₀)}`;
* `poincare_cube` (**no mean condition**): `‖b_ν‖_{L²(Q₀)} ≤ Σ_μ ‖∂_μ b_ν‖_{L²(Q₀)}`;
* `sobolev_cube_neumann` (**critical Sobolev**): `‖b_ν‖_{L⁴(Q₀)} ≤ 14 Σ_μ ‖∂_μ b_ν‖_{L²(Q₀)}`;
* `sobolev_cube` (all of `W^{1,2}(Q₀)`): `‖u‖_{L⁴(Q₀)} ≤ 6 Σ_μ ‖∂_μ u‖_{L²(Q₀)} + 8 ‖u‖_{L²(Q₀)}`,
  and `poincare_cube_scalar` (`∫_{Q₀} u = 0 ⇒ ‖u‖_{L²(Q₀)} ≤ Σ_μ ‖∂_μ u‖_{L²(Q₀)}`);
* `neumann_harmonic_cube` (**no harmonic one-forms with vanishing normal component on `Q₀`**).
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

/-! ### Algebra of parity extensions -/

theorem extR_add (S : Finset (Fin 4)) (u v : (Fin 4 → ℝ) → ℂ) (y : Fin 4 → ℝ) :
    extR S (fun x => u x + v x) y = extR S u y + extR S v y := by
  simp only [extR]; ring

theorem parExt_add (S : Finset (Fin 4)) (u v : (Fin 4 → ℝ) → ℂ) (t : 𝕋⁴) :
    parExt S (fun x => u x + v x) t = parExt S u t + parExt S v t := extR_add S u v _

theorem parExt_sub (S : Finset (Fin 4)) (u v : (Fin 4 → ℝ) → ℂ) (t : 𝕋⁴) :
    parExt S (fun x => u x - v x) t = parExt S u t - parExt S v t := by
  simp only [parExt, extR]; ring

theorem parExt_const_mul (S : Finset (Fin 4)) (c : ℂ) (u : (Fin 4 → ℝ) → ℂ) (t : 𝕋⁴) :
    parExt S (fun x => c * u x) t = c * parExt S u t := by
  simp only [parExt, extR]; ring

theorem parExt_finset_sum (S : Finset (Fin 4)) {κ : Type*} (s : Finset κ)
    (u : κ → (Fin 4 → ℝ) → ℂ) (t : 𝕋⁴) :
    parExt S (fun x => ∑ k ∈ s, u k x) t = ∑ k ∈ s, parExt S (u k) t := by
  simp only [parExt, extR, Finset.mul_sum]

theorem parExt_zero (S : Finset (Fin 4)) (t : 𝕋⁴) : parExt S (fun _ => 0) t = 0 := by
  simp [parExt, extR]

theorem prod_sign_mul (S T : Finset (Fin 4)) (s : Fin 4 → ℂ) (hs : ∀ i, s i * s i = 1) :
    (∏ i ∈ S, s i) * (∏ i ∈ T, s i) = ∏ i ∈ symmDiff S T, s i := by
  have h : ∀ A : Finset (Fin 4), ∏ i ∈ A, s i = ∏ i, if i ∈ A then s i else 1 := fun A => by
    rw [Finset.prod_ite_mem, Finset.univ_inter]
  rw [h S, h T, h (symmDiff S T), ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;> simp [Finset.mem_symmDiff, hS, hT, hs i]

/-- **Products of parity extensions**: the patterns add modulo 2. -/
theorem parExt_mul (S T : Finset (Fin 4)) (u v : (Fin 4 → ℝ) → ℂ) (t : 𝕋⁴) :
    parExt S u t * parExt T v t = parExt (symmDiff S T) (fun x => u x * v x) t := by
  simp only [parExt, extR]
  rw [← prod_sign_mul S T (fun i => ((sgnTri (torusRep t i) : ℝ) : ℂ)) fun i => by
    simp only [sgnTri]; split_ifs <;> norm_num]
  ring

theorem parExt_conj (S : Finset (Fin 4)) (u : (Fin 4 → ℝ) → ℂ) (t : 𝕋⁴) :
    conj (parExt S u t) = parExt S (fun x => conj (u x)) t := by
  simp only [parExt, extR, map_mul, map_prod, Complex.conj_ofReal]

theorem torusRep_chart0 {x : Fin 4 → ℝ} (hx : x ∈ Q0) : torusRep (chart0 x) = x := by
  have hc : chart0 x = fun i => (x i : UnitAddCircle) := by
    funext i; simp [TorusChart.chart]
  rw [hc, torusRep_mk]
  intro i; have := mem_Q0.1 hx i; exact ⟨this.1, by linarith [this.2]⟩

/-- Restricting a parity extension to the cube returns the function. -/
theorem parExt_chart0 (S : Finset (Fin 4)) (u : (Fin 4 → ℝ) → ℂ) {x : Fin 4 → ℝ}
    (hx : x ∈ Q0) : parExt S u (chart0 x) = u x := by
  rw [parExt, torusRep_chart0 hx, extR_of_mem_Q0 S u hx]

theorem sixteen_rpow_half : (16 : ℝ≥0∞) ^ (1 / (2 : ℝ≥0∞).toReal) = 4 := by
  rw [show (16 : ℝ≥0∞) = 4 ^ (2 : ℝ) by norm_num, ← ENNReal.rpow_mul]; norm_num

theorem sixteen_rpow_quarter : (16 : ℝ≥0∞) ^ (1 / (4 : ℝ≥0∞).toReal) = 2 := by
  rw [show (16 : ℝ≥0∞) = 2 ^ (4 : ℝ) by norm_num, ← ENNReal.rpow_mul]; norm_num

theorem eLpNorm_parExt_two {S : Finset (Fin 4)} {u : (Fin 4 → ℝ) → ℂ}
    (hu : MemLp u 2 (volume.restrict Q0)) :
    eLpNorm (parExt S u) 2 volume = 4 * eLpNorm u 2 (volume.restrict Q0) := by
  rw [eLpNorm_parExt (by norm_num) (by norm_num) hu, sixteen_rpow_half]

theorem eLpNorm_parExt_four {S : Finset (Fin 4)} {u : (Fin 4 → ℝ) → ℂ}
    (hu : MemLp u 4 (volume.restrict Q0)) :
    eLpNorm (parExt S u) 4 volume = 2 * eLpNorm u 4 (volume.restrict Q0) := by
  rw [eLpNorm_parExt (by norm_num) (by norm_num) hu, sixteen_rpow_quarter]

/-- The extension of a function vanishing a.e. on `Q₀` vanishes a.e. -/
theorem parExt_ae_zero {S : Finset (Fin 4)} {u : (Fin 4 → ℝ) → ℂ}
    (hu : u =ᵐ[volume.restrict Q0] 0) : parExt S u =ᵐ[volume] 0 := by
  have hm : MemLp u 2 (volume.restrict Q0) := MemLp.ae_eq hu.symm MemLp.zero
  have h := eLpNorm_parExt_two (S := S) hm
  rw [eLpNorm_eq_zero_iff hm.1 (by norm_num) |>.2 hu, mul_zero] at h
  exact (eLpNorm_eq_zero_iff (memLp_parExt (by norm_num) (by norm_num) hm).1 (by norm_num)).1 h

theorem parExt_congr_ae {S : Finset (Fin 4)} {u v : (Fin 4 → ℝ) → ℂ}
    (huv : u =ᵐ[volume.restrict Q0] v) : parExt S u =ᵐ[volume] parExt S v := by
  have h0 : (fun x => u x - v x) =ᵐ[volume.restrict Q0] 0 := by
    filter_upwards [huv] with x hx; simp [hx]
  filter_upwards [parExt_ae_zero (S := S) h0] with t ht
  rw [parExt_sub] at ht
  exact sub_eq_zero.1 ht

/-- If the parity extension of `u` is in `L^p(𝕋⁴)`, then `u ∈ L^p(Q₀)` (restriction inequality). -/
theorem memLp_of_parExt {S : Finset (Fin 4)} {u : (Fin 4 → ℝ) → ℂ}
    (hu : AEStronglyMeasurable u (volume.restrict Q0)) {p : ℝ} (hp : 0 < p)
    (hF : eLpNorm (parExt S u) (ENNReal.ofReal p) volume < ⊤) :
    MemLp u (ENNReal.ofReal p) (volume.restrict Q0) := by
  refine ⟨hu, ?_⟩
  have hQ : MeasurableSet Q0 := (isOpen_box _ _).measurableSet
  have e : eLpNorm u (ENNReal.ofReal p) (volume.restrict Q0) =
      eLpNorm (fun x => parExt S u (chart0 x)) (ENNReal.ofReal p) (volume.restrict Q0) :=
    eLpNorm_congr_ae ((ae_restrict_mem hQ).mono fun x hx => (parExt_chart0 S u hx).symm)
  rw [e]
  refine (TorusChart.eLpNorm_chart_le one_pos Q0_subset_cubeAt (parExt S u) hp).trans_lt ?_
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hF

/-! ### The Neumann class of one-forms on the cube -/

/-- **The Neumann class `H¹_N(Q₀)`** of one-forms with vanishing normal component on `∂Q₀`:
`b ν ∈ L²(Q₀)`, `db ν μ ∈ L²(Q₀)`, and the parity extension `ν ↦ parExt {ν} (b ν)` (odd normal,
even tangential components) has the torus partials `parExt ({ν} ∆ {μ}) (db ν μ)`. -/
structure IsNeumannH1 (b : Fin 4 → (Fin 4 → ℝ) → ℂ) (db : Fin 4 → Fin 4 → (Fin 4 → ℝ) → ℂ) :
    Prop where
  memLp : ∀ ν, MemLp (b ν) 2 (volume.restrict Q0)
  memLp_grad : ∀ ν μ, MemLp (db ν μ) 2 (volume.restrict Q0)
  hasPartial : ∀ ν μ, IsTPartial μ (parExt {ν} (b ν)) (parExt (symmDiff {ν} {μ}) (db ν μ))

namespace IsNeumannH1

variable {b : Fin 4 → (Fin 4 → ℝ) → ℂ} {db : Fin 4 → Fin 4 → (Fin 4 → ℝ) → ℂ}

theorem memLp_ext (h : IsNeumannH1 b db) (ν : Fin 4) : MemLp (parExt {ν} (b ν)) 2 volume :=
  memLp_parExt (by norm_num) (by norm_num) (h.memLp ν)

theorem memLp_ext_grad (h : IsNeumannH1 b db) (ν μ : Fin 4) :
    MemLp (parExt (symmDiff {ν} {μ}) (db ν μ)) 2 volume :=
  memLp_parExt (by norm_num) (by norm_num) (h.memLp_grad ν μ)

/-- The extension is a Neumann one-form on `𝕋⁴`. -/
theorem isNeumannForm (_h : IsNeumannH1 b db) : IsNeumannForm fun ν => parExt {ν} (b ν) :=
  fun ν => hasParity_parExt {ν} (b ν)

/-- **Neumann forms are in `W^{1,2}(Q₀)`** (with the given weak gradient). -/
theorem memW12 (h : IsNeumannH1 b db) (ν : Fin 4) : MemW12 Q0 (b ν) (db ν) := by
  have hW := memW12_restrict (h.memLp_ext ν) (fun μ => h.memLp_ext_grad ν μ) (h.hasPartial ν)
  have hQ : MeasurableSet Q0 := (isOpen_box _ _).measurableSet
  have e1 : (fun x => parExt {ν} (b ν) (chart0 x)) =ᵐ[volume.restrict Q0] b ν :=
    (ae_restrict_mem hQ).mono fun x hx => parExt_chart0 _ _ hx
  have e2 : ∀ μ, (fun x => parExt (symmDiff {ν} {μ}) (db ν μ) (chart0 x)) =ᵐ[volume.restrict Q0]
      db ν μ := fun μ => (ae_restrict_mem hQ).mono fun x hx => parExt_chart0 _ _ hx
  exact ⟨h.memLp ν, h.memLp_grad ν, fun μ =>
    hasWeakPartial_congr_ae_restrict hQ (hW.weak μ) e1 (e2 μ)⟩

end IsNeumannH1

/-! ### Gaffney, Poincaré, Sobolev on `Q₀` -/

theorem ennreal_cancel_four {x y : ℝ≥0∞} (h : 4 * x ≤ 4 * y) : x ≤ y :=
  (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).1 h

/-- **Gaffney inequality on the cube** for one-forms with vanishing normal component:
`‖∂_μ b_ν‖_{L²(Q₀)} ≤ Σ_{μ'ν'} ‖∂_{μ'} b_{ν'} - ∂_{ν'} b_{μ'}‖_{L²(Q₀)} + ‖Σ_{μ'} ∂_{μ'} b_{μ'}‖_{L²(Q₀)}`.
(The boundary term of the general Gaffney inequality, the second fundamental form, vanishes on
the flat faces.) -/
theorem gaffney_cube {b : Fin 4 → (Fin 4 → ℝ) → ℂ} {db : Fin 4 → Fin 4 → (Fin 4 → ℝ) → ℂ}
    (h : IsNeumannH1 b db) (ν μ : Fin 4) :
    eLpNorm (db ν μ) 2 (volume.restrict Q0) ≤
      ∑ μ', ∑ ν', eLpNorm (fun x => db ν' μ' x - db μ' ν' x) 2 (volume.restrict Q0) +
        eLpNorm (fun x => ∑ μ', db μ' μ' x) 2 (volume.restrict Q0) := by
  have hT := eLpNorm_partial_le_curl_div (fun ν μ => h.memLp_ext_grad ν μ) h.hasPartial ν μ
  rw [eLpNorm_parExt_two (h.memLp_grad ν μ)] at hT
  have hc : ∀ μ' ν', eLpNorm (fun x => parExt (symmDiff {ν'} {μ'}) (db ν' μ') x -
      parExt (symmDiff {μ'} {ν'}) (db μ' ν') x) 2 volume =
      4 * eLpNorm (fun x => db ν' μ' x - db μ' ν' x) 2 (volume.restrict Q0) := by
    intro μ' ν'
    rw [symmDiff_comm ({μ'} : Finset (Fin 4)) {ν'}]
    have e : (fun x => parExt (symmDiff {ν'} {μ'}) (db ν' μ') x -
        parExt (symmDiff {ν'} {μ'}) (db μ' ν') x) =
        parExt (symmDiff {ν'} {μ'}) (fun x => db ν' μ' x - db μ' ν' x) := by
      funext t; rw [parExt_sub]
    rw [e]
    exact eLpNorm_parExt_two (u := fun x => db ν' μ' x - db μ' ν' x)
      ((h.memLp_grad ν' μ').sub (h.memLp_grad μ' ν'))
  have hd : eLpNorm (fun x => ∑ μ', parExt (symmDiff {μ'} {μ'}) (db μ' μ') x) 2 volume =
      4 * eLpNorm (fun x => ∑ μ', db μ' μ' x) 2 (volume.restrict Q0) := by
    have e : (fun x => ∑ μ', parExt (symmDiff {μ'} {μ'}) (db μ' μ') x) =
        parExt ∅ (fun x => ∑ μ', db μ' μ' x) := by
      funext t; simp only [symmDiff_self, Finset.bot_eq_empty]; rw [parExt_finset_sum]
    rw [e, eLpNorm_parExt_two (memLp_finsetSum _ fun μ' _ => h.memLp_grad μ' μ')]
  simp only [hc, hd, ← Finset.mul_sum, ← mul_add] at hT
  exact ennreal_cancel_four hT

/-- **Poincaré inequality on the cube for Neumann forms** (no mean-zero hypothesis: the normal
component is odd, so the extension has mean zero): `‖b_ν‖_{L²(Q₀)} ≤ Σ_μ ‖∂_μ b_ν‖_{L²(Q₀)}`. -/
theorem poincare_cube {b : Fin 4 → (Fin 4 → ℝ) → ℂ} {db : Fin 4 → Fin 4 → (Fin 4 → ℝ) → ℂ}
    (h : IsNeumannH1 b db) (ν : Fin 4) :
    eLpNorm (b ν) 2 (volume.restrict Q0) ≤ ∑ μ, eLpNorm (db ν μ) 2 (volume.restrict Q0) := by
  have hT := eLpNorm_le_of_mean_zero (h.memLp_ext ν) (fun μ => h.memLp_ext_grad ν μ)
    (h.hasPartial ν) (h.isNeumannForm.mean_zero ν)
  rw [eLpNorm_parExt_two (h.memLp ν)] at hT
  simp only [fun μ => eLpNorm_parExt_two (S := symmDiff {ν} {μ}) (h.memLp_grad ν μ)] at hT
  rw [← Finset.mul_sum] at hT
  exact ennreal_cancel_four hT

/-- **Critical Sobolev inequality on the cube for Neumann forms**:
`‖b_ν‖_{L⁴(Q₀)} ≤ 14 Σ_μ ‖∂_μ b_ν‖_{L²(Q₀)}`. -/
theorem sobolev_cube_neumann {b : Fin 4 → (Fin 4 → ℝ) → ℂ}
    {db : Fin 4 → Fin 4 → (Fin 4 → ℝ) → ℂ} (h : IsNeumannH1 b db) (ν : Fin 4) :
    eLpNorm (b ν) 4 (volume.restrict Q0) ≤ 14 * ∑ μ, eLpNorm (db ν μ) 2 (volume.restrict Q0) := by
  have hT := eLpNorm_four_le_of_mean_zero (h.memLp_ext ν) (fun μ => h.memLp_ext_grad ν μ)
    (h.hasPartial ν) (h.isNeumannForm.mean_zero ν)
  simp only [fun μ => eLpNorm_parExt_two (S := symmDiff {ν} {μ}) (h.memLp_grad ν μ)] at hT
  rw [← Finset.mul_sum] at hT
  -- the `L⁴` norm of the extension
  have h4 : eLpNorm (parExt {ν} (b ν)) 4 volume = 2 * eLpNorm (b ν) 4 (volume.restrict Q0) := by
    have hfin : eLpNorm (parExt {ν} (b ν)) 4 volume < ⊤ :=
      hT.trans_lt (ENNReal.mul_lt_top (by norm_num) (ENNReal.mul_lt_top (by norm_num)
        (ENNReal.sum_lt_top.2 fun μ _ => (h.memLp_grad ν μ).2)))
    have hm4 : MemLp (b ν) 4 (volume.restrict Q0) := by
      have := memLp_of_parExt (S := {ν}) (h.memLp ν).1 (p := 4) (by norm_num)
        (by rw [ENNReal.ofReal_ofNat]; exact hfin)
      rwa [ENNReal.ofReal_ofNat] at this
    exact eLpNorm_parExt_four hm4
  rw [h4] at hT
  have : 2 * eLpNorm (b ν) 4 (volume.restrict Q0) ≤
      2 * (14 * ∑ μ, eLpNorm (db ν μ) 2 (volume.restrict Q0)) := by
    calc 2 * eLpNorm (b ν) 4 (volume.restrict Q0) ≤ 7 * (4 * ∑ μ, eLpNorm (db ν μ) 2
          (volume.restrict Q0)) := hT
      _ = 2 * (14 * ∑ μ, eLpNorm (db ν μ) 2 (volume.restrict Q0)) := by ring
  exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).1 this

/-- **Critical Sobolev inequality on the cube** for all of `W^{1,2}(Q₀)` (even reflection):
`u ∈ L⁴(Q₀)` and `‖u‖_{L⁴(Q₀)} ≤ 6 Σ_μ ‖∂_μ u‖_{L²(Q₀)} + 8 ‖u‖_{L²(Q₀)}`. -/
theorem sobolev_cube {u : (Fin 4 → ℝ) → ℂ} {g : Fin 4 → (Fin 4 → ℝ) → ℂ} (hW : MemW12 Q0 u g) :
    MemLp u 4 (volume.restrict Q0) ∧
      eLpNorm u 4 (volume.restrict Q0) ≤
        6 * ∑ μ, eLpNorm (g μ) 2 (volume.restrict Q0) + 8 * eLpNorm u 2 (volume.restrict Q0) := by
  obtain ⟨h1, h2, h3⟩ := isTPartial_parExt hW
  have hT := eLpNorm_four_le_torus h1 h2 h3
  simp only [fun μ => eLpNorm_parExt_two (S := {μ}) (hW.memLp_grad μ),
    eLpNorm_parExt_two (S := ∅) hW.memLp] at hT
  have hfin : eLpNorm (parExt ∅ u) 4 volume < ⊤ :=
    hT.trans_lt (ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (by norm_num)
      (ENNReal.sum_lt_top.2 fun μ _ => ENNReal.mul_lt_top (by norm_num) (hW.memLp_grad μ).2),
      ENNReal.mul_lt_top (by norm_num) (ENNReal.mul_lt_top (by norm_num) hW.memLp.2)⟩)
  have hm4 : MemLp u 4 (volume.restrict Q0) := by
    have := memLp_of_parExt (S := ∅) hW.memLp.1 (p := 4) (by norm_num)
      (by rw [ENNReal.ofReal_ofNat]; exact hfin)
    rwa [ENNReal.ofReal_ofNat] at this
  refine ⟨hm4, ?_⟩
  rw [eLpNorm_parExt_four hm4] at hT
  have : 2 * eLpNorm u 4 (volume.restrict Q0) ≤
      2 * (6 * ∑ μ, eLpNorm (g μ) 2 (volume.restrict Q0) +
        8 * eLpNorm u 2 (volume.restrict Q0)) := by
    refine hT.trans (le_of_eq ?_)
    rw [← Finset.mul_sum]; ring
  exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).1 this

theorem mFourierCoeff_zero_eq_integral (f : 𝕋⁴ → ℂ) : mFourierCoeff f 0 = ∫ t, f t := by
  unfold mFourierCoeff; simp [mFourier_zero]

/-- **Neumann–Poincaré inequality for functions on the cube**: if `∫_{Q₀} u = 0` then
`‖u‖_{L²(Q₀)} ≤ Σ_μ ‖∂_μ u‖_{L²(Q₀)}`. -/
theorem poincare_cube_scalar {u : (Fin 4 → ℝ) → ℂ} {g : Fin 4 → (Fin 4 → ℝ) → ℂ}
    (hW : MemW12 Q0 u g) (h0 : ∫ x in Q0, u x = 0) :
    eLpNorm u 2 (volume.restrict Q0) ≤ ∑ μ, eLpNorm (g μ) 2 (volume.restrict Q0) := by
  obtain ⟨h1, h2, h3⟩ := isTPartial_parExt hW
  have : IsFiniteMeasure (volume.restrict Q0) :=
    isFiniteMeasure_restrict.2 (volume_box_ne_top _ _)
  have hmean : mFourierCoeff (parExt ∅ u) 0 = 0 := by
    rw [mFourierCoeff_zero_eq_integral,
      integral_parExt (hW.memLp.integrable (by norm_num)), h0, mul_zero]
  have hT := eLpNorm_le_of_mean_zero h1 h2 h3 hmean
  simp only [fun μ => eLpNorm_parExt_two (S := {μ}) (hW.memLp_grad μ),
    eLpNorm_parExt_two (S := ∅) hW.memLp, ← Finset.mul_sum] at hT
  exact ennreal_cancel_four hT

/-- **No harmonic one-forms with vanishing normal component on the cube**: a Neumann-class
one-form with `db_{νμ} = db_{μν}` (closed) and `Σ_μ db_{μμ} = 0` (co-closed) a.e. on `Q₀`
vanishes a.e. on `Q₀`. -/
theorem neumann_harmonic_cube {b : Fin 4 → (Fin 4 → ℝ) → ℂ}
    {db : Fin 4 → Fin 4 → (Fin 4 → ℝ) → ℂ} (h : IsNeumannH1 b db)
    (hclosed : ∀ μ ν, db ν μ =ᵐ[volume.restrict Q0] db μ ν)
    (hcoclosed : (fun x => ∑ μ, db μ μ x) =ᵐ[volume.restrict Q0] 0) :
    ∀ ν, b ν =ᵐ[volume.restrict Q0] 0 := by
  have hT := neumann_harmonic_eq_zero (a := fun ν => parExt {ν} (b ν))
    (g := fun ν μ => parExt (symmDiff {ν} {μ}) (db ν μ)) (fun ν => h.memLp_ext ν)
    (fun ν μ => h.memLp_ext_grad ν μ) h.hasPartial h.isNeumannForm
    (fun μ ν => by
      rw [symmDiff_comm ({μ} : Finset (Fin 4)) {ν}]
      exact parExt_congr_ae (hclosed μ ν))
    (by
      have := parExt_ae_zero (S := ∅) hcoclosed
      filter_upwards [this] with t ht
      rw [parExt_finset_sum] at ht
      simp only [symmDiff_self, Finset.bot_eq_empty, Pi.zero_apply]
      exact ht)
  intro ν
  have hQ : MeasurableSet Q0 := (isOpen_box _ _).measurableSet
  have h1 := TorusChart.ae_chart_of_ae one_pos Q0_subset_cubeAt (hT ν)
  filter_upwards [h1, ae_restrict_mem hQ] with x hx hxQ
  have := parExt_chart0 {ν} (b ν) hxQ
  simp only [Pi.zero_apply] at hx ⊢
  rw [← this]; exact hx

/-! ### Non-vacuity -/

/-- The zero one-form is in the Neumann class. -/
example : IsNeumannH1 (fun _ _ => 0) (fun _ _ _ => 0) :=
  ⟨fun _ => MemLp.zero, fun _ _ => MemLp.zero, fun ν μ => by
    have e1 : parExt {ν} (fun _ : Fin 4 → ℝ => (0 : ℂ)) = fun _ => 0 := funext (parExt_zero _)
    have e2 : parExt (symmDiff {ν} {μ}) (fun _ : Fin 4 → ℝ => (0 : ℂ)) = fun _ => 0 :=
      funext (parExt_zero _)
    rw [e1, e2]; exact isTPartial_const μ 0⟩

end RenewalGeometry.CubeNeumann
