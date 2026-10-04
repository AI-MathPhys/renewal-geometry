/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.GaugeTheory.DeterminantFluxExact
import RenewalGeometry.DiscreteAnalysis.PeriodicGridHodge

/-!
# Zero-flux determinant normalization with the discrete Hodge primitive
  (`prop:periodic-determinant-normalization`, `prop:native-determinant-split`,
  `lem:determinant-Hodge-stability`; Einstein–SM action closure)

The exact gauge constructions `DeterminantFlux.periodic_abelian_normalization` and
`DeterminantFlux.native_determinant_split_of_primitive` take a real primitive `a⁰` of the
determinant curvature as a hypothesis.  Here the primitive is constructed: for periodic `U(1)`
links `u` on `(ℤ/n)^ι` with `max |φ| < π/3` (`φ = Arg p_u`) and zero flux, the curvature
`f = h⁻² φ` is closed (`DeterminantFlux.cubeSum_eq_zero`) and has zero-mean components
(`DeterminantFlux.sum_phase_eq_flux`), so `a⁰ = δ_h Δ_h^† f` (`GridHodge.scaledPrimitive`) is
defined and satisfies `h · h(d_h a⁰) = φ`, `δ_h a⁰ = 0`, `\bar{a⁰} = 0`,
`‖D^+a⁰‖_{2,h} = ‖f‖_{2,h}` and, in four dimensions,
`L⁻¹‖a⁰_ν‖_{2,h} + ‖a⁰_ν‖_{4,h} ≤ (6 + 5√2)‖f‖_{2,h}`
(`DiscreteAnalysis/PeriodicGridHodge.lean`, `DiscreteAnalysis/GridSobolevInequality.lean`).

* `periodic_determinant_normalization_exact` — `eq:determinant-Abelian-normalization` with the
  paper's potential: constants `c_μ ∈ (-π/L, π/L]` retaining the cycle holonomies of the flat
  residual, site phases `t` with `e^{it(x)} u_μ(x) e^{-it(x+e_μ)} = e^{ih(a⁰+c)_μ(x)}`, and
  `δ_h(a⁰ + c) = 0`; no smallness of `f`, `a⁰` or the cycle phases.
* `native_determinant_split_exact` — `prop:native-determinant-split` on the periodic grid with
  the Hodge primitive constructed; the only remaining analytic input is the admissibility of
  the logarithms of the full plaquettes (eventual smallness from the curvature screen,
  `lem:determinant-screen-flux`).
-/

open Finset Matrix

namespace RenewalGeometry.DeterminantFlux

open GridSobolev GridHodge DeterminantSplit SMDescentYukawa

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} [NeZero n]

omit [Fintype ι] [NeZero n] in
theorem cubeSum_eq_gridHodge (φ : (ι → ZMod n) → ι → ι → ℝ) (x : ι → ZMod n) (μ ν κ : ι) :
    DeterminantFlux.cubeSum φ x μ ν κ = GridHodge.cubeSum φ x μ ν κ := rfl

omit [Fintype ι] [NeZero n] in
theorem gridCurl_eq_curl (a : (ι → ZMod n) → ι → ℝ) (x : ι → ZMod n) (μ ν : ι) :
    gridCurl a x μ ν = GridHodge.curl a x μ ν := rfl

omit [NeZero n] in
theorem gridDiv_eq_div (a : (ι → ZMod n) → ι → ℝ) (x : ι → ZMod n) :
    gridDiv a x = GridHodge.div a x := rfl

omit [Fintype ι] [NeZero n] in
/-- The Abelian plaquette of circle-valued links is the group plaquette. -/
theorem abPhase_coe_eq_arg_gPlaq (u : (ι → ZMod n) → ι → Circle) (x : ι → ZMod n) (μ ν : ι) :
    abPhase (fun x μ => (u x μ : ℂ)) x μ ν = Complex.arg ((gPlaq u x μ ν : Circle) : ℂ) := by
  simp only [abPhase, abPlaq, gPlaq, Circle.coe_mul, Circle.coe_inv]
  congr 1
  rw [div_eq_mul_inv, _root_.mul_inv]
  ring

/-- The determinant curvature `f = h⁻² φ`. -/
def detCurvature (u : (ι → ZMod n) → ι → ℂ) (h : ℝ) : (ι → ZMod n) → ι → ι → ℝ :=
  fun x μ ν => abPhase u x μ ν / h ^ 2

/-- The paper's determinant potential `a⁰ = δ_h Δ_h^† f`, as a one-form `x ↦ (μ ↦ a⁰_μ(x))`. -/
def detPotential (u : (ι → ZMod n) → ι → ℂ) (h : ℝ) : (ι → ZMod n) → ι → ℝ :=
  fun x ν => scaledPrimitive h (detCurvature u h) ν x

/-- Closedness and zero mean of the determinant curvature under the screen hypotheses. -/
theorem detCurvature_closed_meanZero (u : (ι → ZMod n) → ι → ℂ) (hu : ∀ x μ, ‖u x μ‖ = 1)
    (hsmall : ∀ x μ ν, |abPhase u x μ ν| < Real.pi / 3)
    (hflux : ∀ μ ν, planeFlux u 0 μ ν = 0) (h : ℝ) :
    (∀ x μ ν κ, GridHodge.cubeSum (detCurvature u h) x μ ν κ = 0) ∧
    (∀ μ ν, ∑ x, detCurvature u h x μ ν = 0) := by
  have hd := cubeSum_eq_zero u hu hsmall
  refine ⟨fun x μ ν κ => ?_, fun μ ν => ?_⟩
  · have h0 : GridHodge.cubeSum (abPhase u) x μ ν κ = 0 := hd x μ ν κ
    have h1 : GridHodge.cubeSum (detCurvature u h) x μ ν κ =
        GridHodge.cubeSum (abPhase u) x μ ν κ / h ^ 2 := by
      simp only [GridHodge.cubeSum, detCurvature]; ring
    rw [h1, h0, zero_div]
  · have hS := sum_phase_eq_flux u hd μ ν
    rw [hflux, mul_zero] at hS
    have hn : (n : ℝ) ^ 2 ≠ 0 := by
      have : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
      positivity
    have h0 : ∑ x : ι → ZMod n, abPhase u x μ ν = 0 := (mul_eq_zero.1 hS).resolve_left hn
    simp only [detCurvature, ← sum_div, h0, zero_div]

/-- The potential is a primitive of the principal plaquette argument:
`h · h (d_h a⁰) = φ` (the hypothesis `hprim` of the gauge constructions). -/
theorem detPotential_prim (u : (ι → ZMod n) → ι → ℂ) (hu : ∀ x μ, ‖u x μ‖ = 1)
    (hsmall : ∀ x μ ν, |abPhase u x μ ν| < Real.pi / 3)
    (hflux : ∀ μ ν, planeFlux u 0 μ ν = 0) {h : ℝ} (hh : 0 < h) (x : ι → ZMod n) (μ ν : ι) :
    h * gridCurl (detPotential u h) x μ ν = abPhase u x μ ν := by
  obtain ⟨hc, hm⟩ := detCurvature_closed_meanZero u hu hsmall hflux h
  have hcurl := hodgePrimitive_curl (detCurvature u h) hc hm x μ ν
  simp only [GridHodge.curl] at hcurl
  simp only [gridCurl, detPotential, scaledPrimitive, unitStep]
  have : h * (h * hodgePrimitive (detCurvature u h) x μ +
      h * hodgePrimitive (detCurvature u h) (x + Pi.single μ 1) ν -
      h * hodgePrimitive (detCurvature u h) (x + Pi.single ν 1) μ -
      h * hodgePrimitive (detCurvature u h) x ν) = h ^ 2 * detCurvature u h x μ ν := by
    rw [← hcurl]; simp only [gridStep]; ring
  rw [this, detCurvature]
  field_simp

/-- **`prop:periodic-determinant-normalization`, exact part with the paper's potential.**
Let `u` be periodic `U(1)` links on `(ℤ/n)^ι` with `max |φ| < π/3` (`φ = Arg p_u`) and zero flux
(all coordinate-plane fluxes vanish), and let `h > 0`, `L = n h`.  With
`a⁰ = δ_h Δ_h^† f`, `f = h⁻² φ` (`detPotential`), there are constants `c_μ` with
`L c_μ ∈ (-π, π]` equal to the principal argument of the cycle holonomy of the flat residual
`u e^{-iha⁰}`, and real site phases `t`, such that
`e^{it(x)} u_μ(x) e^{-it(x+e_μ)} = e^{ih(a⁰ + c)_μ(x)}` and `δ_h(a⁰ + c) = 0`; moreover
`h·h(d_h a⁰) = φ` and `\bar{a⁰} = 0`. -/
theorem periodic_determinant_normalization_exact (u : (ι → ZMod n) → ι → Circle)
    (hsmall : ∀ x μ ν, |abPhase (fun x μ => (u x μ : ℂ)) x μ ν| < Real.pi / 3)
    (hflux : ∀ μ ν, planeFlux (fun x μ => (u x μ : ℂ)) 0 μ ν = 0) {h : ℝ} (hh : 0 < h) :
    let a0 := detPotential (fun x μ => (u x μ : ℂ)) h
    (∀ x μ ν, h * gridCurl a0 x μ ν = abPhase (fun x μ => (u x μ : ℂ)) x μ ν) ∧
    (∀ ν, ∑ x, a0 x ν = 0) ∧
    ∃ (c : ι → ℝ) (t : (ι → ZMod n) → ℝ),
      (∀ μ, -Real.pi < n * h * c μ ∧ n * h * c μ ≤ Real.pi) ∧
      (∀ μ x, Circle.exp (n * h * c μ) =
        cycProd (fun x μ => u x μ * (Circle.exp (h * a0 x μ))⁻¹) x μ) ∧
      (∀ x μ, Circle.exp (t x) * u x μ * (Circle.exp (t (x + unitStep μ)))⁻¹ =
        Circle.exp (h * (a0 x μ + c μ))) ∧
      (∀ x, gridDiv (fun x μ => a0 x μ + c μ) x = 0) := by
  intro a0
  set u' : (ι → ZMod n) → ι → ℂ := fun x μ => (u x μ : ℂ)
  have hu : ∀ x μ, ‖u' x μ‖ = 1 := fun x μ => mem_sphere_zero_iff_norm.1 (u x μ).2
  obtain ⟨hc, hm⟩ := detCurvature_closed_meanZero u' hu hsmall hflux h
  have hprim := detPotential_prim u' hu hsmall hflux hh
  have hprim' : ∀ x μ ν, h * gridCurl a0 x μ ν = Complex.arg ((gPlaq u x μ ν : Circle) : ℂ) :=
    fun x μ ν => by rw [hprim, abPhase_coe_eq_arg_gPlaq]
  obtain ⟨c, t, hcst, hcyc, hnorm, hdiv⟩ := periodic_abelian_normalization u h hh a0 hprim'
  refine ⟨hprim, fun ν => ?_, c, t, hcst, hcyc, hnorm, fun x => ?_⟩
  · simp only [a0, detPotential, scaledPrimitive, ← mul_sum]
    rw [sum_hodgePrimitive, mul_zero]
  · rw [hdiv, gridDiv_eq_div]
    have := hodgePrimitive_div (detCurvature u' h) hc hm x
    simp only [GridHodge.div] at this ⊢
    simp only [a0, detPotential, scaledPrimitive, ← mul_sub, ← mul_sum]
    rw [this, mul_zero]

/-- The four-dimensional bounds of `lem:determinant-Hodge-stability` for the determinant
potential: `‖D^+ a⁰‖_{2,h} = ‖f‖_{2,h}` and
`L⁻¹ ‖a⁰_ν‖_{2,h} + ‖a⁰_ν‖_{4,h} ≤ (6 + 5√2) ‖f‖_{2,h}` (uniform in `n`). -/
theorem detPotential_bounds [LinearOrder ι] (hι : Fintype.card ι = 4)
    (u : (ι → ZMod n) → ι → ℂ) (hu : ∀ x μ, ‖u x μ‖ = 1)
    (hsmall : ∀ x μ ν, |abPhase u x μ ν| < Real.pi / 3)
    (hflux : ∀ μ ν, planeFlux u 0 μ ν = 0) {h : ℝ} (hh : 0 < h) :
    (∑ μ, ∑ ν, periodicHodgeNormSq ι h
        (periodicHodgeFwd h gridStep μ (scaledPrimitive h (detCurvature u h) ν)) =
      ∑ p ∈ (univ : Finset (ι × ι)).filter (fun p => p.1 < p.2),
        periodicHodgeNormSq ι h (comp (detCurvature u h) p.1 p.2)) ∧
    ∀ ν, ((n : ℝ) * h)⁻¹ * gridL2Norm h (scaledPrimitive h (detCurvature u h) ν) +
        gridL4Norm h (scaledPrimitive h (detCurvature u h) ν) ≤
      (6 + 5 * √2) * √(∑ p ∈ (univ : Finset (ι × ι)).filter (fun p => p.1 < p.2),
        periodicHodgeNormSq ι h (comp (detCurvature u h) p.1 p.2)) := by
  obtain ⟨hc, hm⟩ := detCurvature_closed_meanZero u hu hsmall hflux h
  exact ⟨(hodge_stability_exact _ hc hm hh).2.2.2,
    fun ν => hodge_stability_bounds _ hc hm hι hh ν⟩

/-- **`prop:native-determinant-split` on the periodic grid, with the Hodge primitive
constructed.**  Let `U` be `G_SM` links on `(ℤ/n)^ι`, `h > 0`, with principal determinant
arguments `|Arg χ(P_U)| < π/3` and zero determinant flux, and let `L` be logarithms of the full
plaquettes with entries bounded by `c`, `2c < min(r, π)` (admissibility; supplied for small `h` by
the curvature screen, `lem:determinant-screen-flux`).  Then, with the paper's potential
`a⁰ = δ_h Δ_h^† f` (`detPotential`), all conclusions of
`native_determinant_split_of_primitive` hold, and in addition `δ_h(a⁰ + c) = 0`. -/
theorem native_determinant_split_exact (U : (ι → ZMod n) → ι → SMGaugeGroup) {h : ℝ}
    (hh : 0 < h)
    (hsmall : ∀ x μ ν, |Complex.arg (smChi (plaq gridShift U x μ ν))| < Real.pi / 3)
    (hflux : ∀ μ ν, planeFlux (fun x μ => smChi (U x μ)) 0 μ ν = 0)
    (c : ℝ) (hc : 2 * c < min pairChart Real.pi)
    (L : (ι → ZMod n) → ι → ι → LiePair)
    (hL3 : ∀ x μ ν, NormedSpace.exp (L x μ ν).1 = smU3 (plaq gridShift U x μ ν))
    (hL2 : ∀ x μ ν, NormedSpace.exp (L x μ ν).2 = smU2 (plaq gridShift U x μ ν))
    (hsmall₃ : ∀ x μ ν i j, ‖(L x μ ν).1 i j‖ ≤ c)
    (hsmall₂ : ∀ x μ ν i j, ‖(L x μ ν).2 i j‖ ≤ c) :
    let a0 := detPotential (fun x μ => smChi (U x μ)) h
    ∃ (cst : ι → ℝ) (t : (ι → ZMod n) → ℝ),
      (∀ μ, -Real.pi < n * h * cst μ ∧ n * h * cst μ ≤ Real.pi) ∧
      (∀ x μ, Complex.exp (t x * Complex.I) * smChi (U x μ) *
        Complex.exp (-(t (gridShift x μ) * Complex.I)) =
          Complex.exp (h * ((a0 x μ + cst μ : ℝ) : ℂ) * Complex.I)) ∧
      (∀ x, gridDiv (fun x μ => a0 x μ + cst μ) x = 0) ∧
      let a : (ι → ZMod n) → ι → ℝ := fun x μ => a0 x μ + cst μ
      let f : (ι → ZMod n) → ι → ι → ℝ :=
        fun x μ ν => Complex.arg (smChi (plaq gridShift U x μ ν)) / h ^ 2
      (∀ x μ ν, ellC (L x μ ν) = (h ^ 2 * f x μ ν : ℝ)) ∧
      (∀ x μ, smChi (splitLinks gridShift h t a U x μ) = 1 ∧
        (smU3 (splitLinks gridShift h t a U x μ)).det = 1 ∧
        (smU2 (splitLinks gridShift h t a U x μ)).det = 1) ∧
      (∀ x μ ν, plaq gridShift (gaugeTr gridShift (fun x => centralElem (t x)) U) x μ ν =
        centralElem (h ^ 2 * f x μ ν) * plaq gridShift (splitLinks gridShift h t a U) x μ ν) ∧
      (∀ x μ ν, ∀ Y ∈ pairBall pairChart,
        NormedSpace.exp Y.1 = smU3 (plaq gridShift (splitLinks gridShift h t a U) x μ ν) →
        NormedSpace.exp Y.2 = smU2 (plaq gridShift (splitLinks gridShift h t a U) x μ ν) →
        Y = piSS (L x μ ν)) ∧
      (∀ x μ w, splitLinks gridShift h t a U x μ * w * (splitLinks gridShift h t a U x μ)⁻¹ =
        gaugeTr gridShift (fun x => centralElem (t x)) U x μ * w *
          (gaugeTr gridShift (fun x => centralElem (t x)) U x μ)⁻¹) ∧
      (∀ (k : (ι → ZMod n) → ℤ) x μ,
        splitLinks gridShift h (fun x => t x + 2 * Real.pi * k x) a U x μ =
          gaugeTr gridShift (fun x => zSix ^ k x) (splitLinks gridShift h t a U) x μ) := by
  intro a0
  set u' : (ι → ZMod n) → ι → ℂ := fun x μ => smChi (U x μ)
  have hu : ∀ x μ, ‖u' x μ‖ = 1 := fun x μ => norm_smChi _
  have hφ : ∀ x μ ν, abPhase u' x μ ν = Complex.arg (smChi (plaq gridShift U x μ ν)) := by
    intro x μ ν; simp only [abPhase, u', smChi_plaq_eq_abPlaq]
  have hsmall' : ∀ x μ ν, |abPhase u' x μ ν| < Real.pi / 3 := fun x μ ν => by
    rw [hφ]; exact hsmall x μ ν
  obtain ⟨hcl, hm⟩ := detCurvature_closed_meanZero u' hu hsmall' hflux h
  have hprim : ∀ x μ ν, h * gridCurl a0 x μ ν = Complex.arg (smChi (plaq gridShift U x μ ν)) :=
    fun x μ ν => by rw [detPotential_prim u' hu hsmall' hflux hh, hφ]
  obtain ⟨cst, t, hcst, hN, hdiv, rest⟩ := native_determinant_split_of_primitive U h hh a0 hprim
    c hc L hL3 hL2 hsmall₃ hsmall₂
  refine ⟨cst, t, hcst, hN, fun x => ?_, rest⟩
  rw [hdiv, gridDiv_eq_div]
  have := hodgePrimitive_div (detCurvature u' h) hcl hm x
  simp only [GridHodge.div] at this ⊢
  simp only [a0, detPotential, scaledPrimitive, ← mul_sub, ← mul_sum]
  rw [this, mul_zero]

/-- Non-vacuity: trivial `G_SM` links satisfy every hypothesis of
`native_determinant_split_exact` (zero phases, zero flux, zero logarithms). -/
example (n : ℕ) [NeZero n] (h : ℝ) (hh : 0 < h) :
    ∃ (cst : Fin 4 → ℝ) (_t : (Fin 4 → ZMod n) → ℝ),
      ∀ x, gridDiv (fun x μ => detPotential (fun (x : Fin 4 → ZMod n) (μ : Fin 4) =>
        smChi ((fun _ _ => (1 : SMGaugeGroup)) x μ)) h x μ + cst μ) x = 0 := by
  have hpl : ∀ (x : Fin 4 → ZMod n) (μ ν : Fin 4),
      plaq gridShift (fun (_ : Fin 4 → ZMod n) (_ : Fin 4) => (1 : SMGaugeGroup)) x μ ν = 1 :=
    plaq_one_links
  have hflux : ∀ μ ν, planeFlux (fun (x : Fin 4 → ZMod n) (μ : Fin 4) =>
      smChi ((fun _ _ => (1 : SMGaugeGroup)) x μ)) 0 μ ν = 0 := by
    intro μ ν
    simp [planeFlux, abPhase, abPlaq]
  obtain ⟨cst, t, -, -, hdiv, -⟩ := native_determinant_split_exact
    (fun (_ : Fin 4 → ZMod n) (_ : Fin 4) => (1 : SMGaugeGroup)) hh
    (fun x μ ν => by rw [hpl]; simp [Real.pi_pos]) hflux 0
    (by rw [mul_zero]; exact lt_min pairChart_pos Real.pi_pos)
    (fun _ _ _ => 0) (fun x μ ν => by rw [hpl]; simp)
    (fun x μ ν => by rw [hpl]; simp) (fun _ _ _ _ _ => by simp) (fun _ _ _ _ _ => by simp)
  exact ⟨cst, t, hdiv⟩

end

end RenewalGeometry.DeterminantFlux
