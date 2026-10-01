/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.MatrixDetExp
import RenewalGeometry.GaugeTheory.DeterminantSemisimpleSplitExact

/-!
# Determinant character of logarithms, the exponential chart, and the exact flux algebra
  (`lem:determinant-screen-flux`, `prop:native-determinant-split`, Einstein–SM action closure)

**Determinant of a logarithm.**  With `det exp = exp tr` (`Analysis/MatrixDetExp.lean`):
* `smChi_eq_exp_ellC`: `χ(e^X) = e^{i ℓ_c(X)}`;
* `arg_smChi_eq_ellC`: if `ℓ_c(X)` is real in `(-π, π]`, the principal determinant argument
  of `e^X` is `ℓ_c(X)` (so `f_h = ℓ_c(𝔽_h)`, the first identity of
  `eq:determinant-inherited-screen`, on the admissible chart);
* `pairChart`: a radius `r > 0` on whose entrywise pair-ball the pair exponential
  `(X₃, X₂) ↦ (e^{X₃}, e^{X₂})` is injective (`pairChart_injOn`); logarithms of unitary
  matrices inside the chart are anti-Hermitian (`skew_of_exp_unitary`), so `ℓ_c` is real on
  them (`ellC_im_eq_zero_of_skew`).
* `native_determinant_split_of_small_logs`: `DeterminantSplit.native_determinant_split_core`
  with the abstract chart `Ω` and the identity `ℓ_c(L) = h² f` discharged: the curvature is
  the principal argument `f = h⁻² Arg χ(P_U)` of `eq:determinant-real-curvature`, and the
  logarithms are only required to be small.

**Exact Abelian flux algebra** on the periodic grid `Λ = ι → ZMod n`
(`lem:determinant-screen-flux`, finite part): for `U(1)` (or any commutative-group) links,
* `cube_plaquette_prod`: the six oriented plaquettes around a cube multiply to one;
* `cubeSum_eq_zero`: if `max |φ| < π/3` the real cube sum of the principal arguments vanishes
  (`d_h f_h = 0`);
* `plane_plaquette_prod`, `planeFlux_integer`: every periodic coordinate-plane flux is `2π m`;
* `planeFlux_shift`, `planeFlux_const`: the flux is independent of the transverse base point;
* `sum_phase_eq_flux`: `∑_x φ_{μν}(x) = n² · 2π m_{μν}` (the average identity
  `\bar f = 2π m / L²` after multiplying by `h⁴ / L⁴` with `L = n h`);
* `two_pi_abs_flux_le`: `2π |m_{μν}| ≤ (∑_x φ_{μν}(x)²)^{1/2} = ‖f_{μν}‖_{2,h}`;
  `mean_curvature_eq_flux`: `ar f_{μν} = 2π m_{μν}/L²`;
* `determinant_screen_flux_exact`: these clauses for `G_SM` links with `u = χ(U)`.

**Flat Abelian links are pure gauge** (`prop:periodic-determinant-normalization`, exact part),
for any commutative group: cycle holonomies of flat links are base-point independent
(`cycProd_const`), and a flat field with trivial cycle holonomies is `g(x)⁻¹ g(x + e_μ)`
(`pureGauge_of_flat`, by successive line gauges).  `periodic_abelian_normalization`: given a
real primitive `a⁰` of the curvature (`d_h a⁰ = f`), constants `c_μ ∈ (-π/L, π/L]` retaining
the cycle holonomies and real site phases `t` give `e^{it(x)} u_μ(x) e^{-it(x+μ)} = e^{ih(a⁰+c)}`,
`δ_h(a⁰ + c) = δ_h a⁰` (`eq:determinant-Abelian-normalization`), without any smallness.

**Assembly** `native_determinant_split_of_primitive`: on the periodic grid, normalization
followed by the semisimple split, modulo exactly two inputs: the Hodge primitive `a⁰` and the
admissible (small) logarithms of the full plaquettes.

Not formalised here: the existence of the Hodge primitive `a⁰ = δ_h Δ_h^† f`
(`lem:determinant-Hodge-stability`), the eventual smallness of the scaled curvature and the
modulus transfer / `L²` precompactness (`thm:native-Wilson-compactness`,
`lem:native-discrete-KR`), and the raw `L⁴/L²/H¹` precompactness of the coordinates.
-/

open Matrix

namespace RenewalGeometry

namespace DeterminantFlux

open DeterminantSplit SMDescentYukawa

noncomputable section

/-! ### The determinant character of a logarithm -/

/-- `det (exp X₂) = exp (i ℓ_c(X))`. -/
theorem det_exp_snd_eq (X : LiePair) :
    (NormedSpace.exp X.2).det = Complex.exp (Complex.I * ellC X) := by
  rw [MatrixDetExp.det_exp_eq_complex_exp_trace]
  congr 1
  simp only [ellC]
  field_simp

/-- **`χ(e^X) = e^{i ℓ_c(X)}`**: if `exp X₂` is the weak component of `y ∈ G_SM` then
`χ(y) = e^{i ℓ_c(X)}`. -/
theorem smChi_eq_exp_ellC (y : SMGaugeGroup) (X : LiePair)
    (h2 : NormedSpace.exp X.2 = smU2 y) : smChi y = Complex.exp (Complex.I * ellC X) := by
  rw [smChi_apply, ← h2, det_exp_snd_eq]

/-- **Principal determinant argument of a logarithm**: if `ℓ_c(X) = φ` is real with
`φ ∈ (-π, π]`, then `Arg χ(e^X) = φ`. -/
theorem arg_smChi_eq_ellC (y : SMGaugeGroup) (X : LiePair)
    (h2 : NormedSpace.exp X.2 = smU2 y) (φ : ℝ) (hφ : ellC X = φ)
    (hlo : -Real.pi < φ) (hhi : φ ≤ Real.pi) : Complex.arg (smChi y) = φ := by
  rw [smChi_eq_exp_ellC y X h2, hφ, mul_comm, Complex.exp_mul_I]
  exact Complex.arg_cos_add_sin_mul_I ⟨hlo, hhi⟩

/-- `ℓ_c` is real on anti-Hermitian weak components. -/
theorem ellC_im_eq_zero_of_skew (X : LiePair) (hX : X.2ᴴ = -X.2) : (ellC X).im = 0 := by
  have ht : star (trace X.2) = -trace X.2 := by
    rw [← trace_conjTranspose, hX, trace_neg]
  have hre : (trace X.2).re = 0 := by
    have := congrArg Complex.re ht
    simp only [Complex.star_def, Complex.conj_re, Complex.neg_re] at this
    linarith
  simp [ellC, hre]

/-- `|ℓ_c(X)| ≤ 2c` when every weak entry is bounded by `c`. -/
theorem norm_ellC_le (X : LiePair) (c : ℝ) (h2 : ∀ i j, ‖X.2 i j‖ ≤ c) : ‖ellC X‖ ≤ 2 * c := by
  simp only [ellC, norm_div, Complex.norm_I, div_one, Matrix.trace, Matrix.diag,
    Fin.sum_univ_two]
  linarith [norm_add_le (X.2 0 0) (X.2 1 1), h2 0 0, h2 1 1]

/-! ### The pair exponential chart -/

/-- The entrywise pair-ball `{(X₃, X₂) | all entries of norm < r}`. -/
def pairBall (r : ℝ) : Set LiePair :=
  {Y | (∀ i j, ‖Y.1 i j‖ < r) ∧ ∀ i j, ‖Y.2 i j‖ < r}

/-- Existence of an injectivity radius for the pair exponential. -/
theorem exists_pairChart :
    ∃ r : ℝ, 0 < r ∧ ∀ Y ∈ pairBall r, ∀ Y' ∈ pairBall r,
      NormedSpace.exp Y.1 = NormedSpace.exp Y'.1 →
        NormedSpace.exp Y.2 = NormedSpace.exp Y'.2 → Y = Y' := by
  obtain ⟨r₃, hr₃, hinj₃⟩ := MatrixDetExp.exists_injOn_exp_entry_ball (𝕂 := ℂ) (n := Fin 3)
  obtain ⟨r₂, hr₂, hinj₂⟩ := MatrixDetExp.exists_injOn_exp_entry_ball (𝕂 := ℂ) (n := Fin 2)
  refine ⟨min r₃ r₂, lt_min hr₃ hr₂, fun Y hY Y' hY' e₃ e₂ => Prod.ext ?_ ?_⟩
  · exact hinj₃ (fun i j => (hY.1 i j).trans_le (min_le_left _ _))
      (fun i j => (hY'.1 i j).trans_le (min_le_left _ _)) e₃
  · exact hinj₂ (fun i j => (hY.2 i j).trans_le (min_le_right _ _))
      (fun i j => (hY'.2 i j).trans_le (min_le_right _ _)) e₂

/-- A fixed injectivity radius of the pair exponential (the declared logarithm chart). -/
def pairChart : ℝ := Classical.choose exists_pairChart

theorem pairChart_pos : 0 < pairChart := (Classical.choose_spec exists_pairChart).1

/-- **The pair exponential is injective on the chart `pairBall pairChart`.** -/
theorem pairChart_injOn : ∀ Y ∈ pairBall pairChart, ∀ Y' ∈ pairBall pairChart,
    NormedSpace.exp Y.1 = NormedSpace.exp Y'.1 →
      NormedSpace.exp Y.2 = NormedSpace.exp Y'.2 → Y = Y' :=
  (Classical.choose_spec exists_pairChart).2

/-- **Logarithms of unitary matrices in a conjugation-invariant injectivity chart are
anti-Hermitian.**  If `exp` is injective on a set `S` stable under `X ↦ -Xᴴ` and `exp X` is
unitary with `X ∈ S`, then `Xᴴ = -X`. -/
theorem skew_of_exp_unitary {m : Type*} [Fintype m] [DecidableEq m]
    (S : Set (Matrix m m ℂ)) (hinj : Set.InjOn NormedSpace.exp S)
    (hS : ∀ X ∈ S, -Xᴴ ∈ S) (X : Matrix m m ℂ) (hX : X ∈ S)
    (hU : NormedSpace.exp X ∈ Matrix.unitaryGroup m ℂ) : Xᴴ = -X := by
  have hP : (NormedSpace.exp X)ᴴ * NormedSpace.exp X = 1 := by
    have := (Matrix.mem_unitaryGroup_iff' (A := NormedSpace.exp X)).mp hU
    simpa [Matrix.star_eq_conjTranspose] using this
  have hexp : NormedSpace.exp (-Xᴴ) = NormedSpace.exp X := by
    rw [Matrix.exp_neg, Matrix.exp_conjTranspose]
    exact Matrix.inv_eq_right_inv hP
  have := hinj (hS X hX) hX hexp
  rw [← neg_neg Xᴴ, this]

/-- The entrywise ball is stable under `X ↦ -Xᴴ`. -/
theorem neg_conjTranspose_mem_entryBall {m : Type*} (r : ℝ) (X : Matrix m m ℂ)
    (hX : ∀ i j, ‖X i j‖ < r) : ∀ i j, ‖(-Xᴴ) i j‖ < r := by
  intro i j
  simpa [Matrix.neg_apply, Matrix.conjTranspose_apply] using hX j i


/-! ### `prop:native-determinant-split` with the chart and the determinant identity discharged -/

section Assembly

variable {X D : Type*} (shift : X → D → X)

/-- The determinant character is a nowhere-vanishing homomorphism. -/
theorem smChi_ne_zero (y : SMGaugeGroup) : smChi y ≠ 0 := by
  intro h0
  have : smChi y * smChi y⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  rw [h0, zero_mul] at this
  exact zero_ne_one this

/-- The weak component of an element of `G_SM` is unitary. -/
theorem smU2_mem_unitaryGroup (y : SMGaugeGroup) : smU2 y ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
  ((y : SMGaugeU3 × SMGaugeU2).2).2

/-- **The Abelian plaquette is site-gauge invariant** (commuting lattice shifts):
`χ(P_{U^g}) = χ(P_U)`. -/
theorem smChi_plaq_gaugeTr (hcomm : ∀ x μ ν, shift (shift x μ) ν = shift (shift x ν) μ)
    (g : X → SMGaugeGroup) (U : X → D → SMGaugeGroup) (x : X) (μ ν : D) :
    smChi (plaq shift (gaugeTr shift g U) x μ ν) = smChi (plaq shift U x μ ν) := by
  have hne : ∀ z, smChi (g z) ≠ 0 := fun z => smChi_ne_zero (g z)
  have hne' : ∀ y μ, smChi (U y μ) ≠ 0 := fun y μ => smChi_ne_zero (U y μ)
  simp only [plaq, gaugeTr, map_mul, map_inv, hcomm x μ ν]
  have := hne (shift (shift x ν) μ)
  have := hne (shift x μ)
  have := hne (shift x ν)
  have := hne x
  have := hne' x μ
  have := hne' x ν
  have := hne' (shift x μ) ν
  have := hne' (shift x ν) μ
  field_simp

/-- Inside the chart, the weak component of a logarithm of a `G_SM` element is
anti-Hermitian. -/
theorem skew_snd_of_mem_pairBall (Y : LiePair) (hY : ∀ i j, ‖Y.2 i j‖ < pairChart)
    (y : SMGaugeGroup) (h2 : NormedSpace.exp Y.2 = smU2 y) : Y.2ᴴ = -Y.2 := by
  have hinj : Set.InjOn NormedSpace.exp
      {A : Matrix (Fin 2) (Fin 2) ℂ | ∀ i j, ‖A i j‖ < pairChart} := by
    intro A hA B hB hAB
    have h0 : ∀ i j, ‖(0 : Matrix (Fin 3) (Fin 3) ℂ) i j‖ < pairChart := by
      intro i j; simpa using pairChart_pos
    have := pairChart_injOn ((0 : Matrix (Fin 3) (Fin 3) ℂ), A) ⟨h0, hA⟩
      ((0 : Matrix (Fin 3) (Fin 3) ℂ), B) ⟨h0, hB⟩ rfl hAB
    exact congrArg Prod.snd this
  exact skew_of_exp_unitary _ hinj (fun A hA => neg_conjTranspose_mem_entryBall _ A hA) Y.2 hY
    (h2 ▸ smU2_mem_unitaryGroup y)

/-- **`f_h = ℓ_c(𝔽_h)` on the chart** (first identity of `eq:determinant-inherited-screen`):
a logarithm `L` of the full plaquette `P` with weak entries bounded by `c`, `2c < min(r, π)`
(`r` the chart radius), has `ℓ_c(L) = Arg χ(P)`, the principal determinant argument. -/
theorem ellC_eq_arg_smChi (L : LiePair) (P : SMGaugeGroup) (c : ℝ)
    (hc : 2 * c < min pairChart Real.pi)
    (hL2 : NormedSpace.exp L.2 = smU2 P) (hsmall : ∀ i j, ‖L.2 i j‖ ≤ c) :
    ellC L = (Complex.arg (smChi P) : ℂ) := by
  have hcr : 2 * c < pairChart := hc.trans_le (min_le_left _ _)
  have hcπ : 2 * c < Real.pi := hc.trans_le (min_le_right _ _)
  have hc0 : 0 ≤ c := (norm_nonneg _).trans (hsmall 0 0)
  have hball : ∀ i j, ‖L.2 i j‖ < pairChart := fun i j => by linarith [hsmall i j]
  have hskew := skew_snd_of_mem_pairBall L hball P hL2
  have him := ellC_im_eq_zero_of_skew L hskew
  have hre : ellC L = ((ellC L).re : ℂ) := Complex.ext (by simp) (by simp [him])
  have hnorm := norm_ellC_le L c hsmall
  have habs : |(ellC L).re| ≤ 2 * c := by
    rw [hre, Complex.norm_real, Real.norm_eq_abs] at hnorm
    exact hnorm
  have harg := arg_smChi_eq_ellC P L hL2 (ellC L).re hre
    (by linarith [neg_abs_le (ellC L).re]) (by linarith [le_abs_self (ellC L).re])
  rw [harg]
  exact hre

/-- **`prop:native-determinant-split`, group algebra with the chart discharged.**  On a lattice
with commuting shifts, let `U` be `G_SM` links, `t` real site lifts and `a` a real potential with
* (normalization, the conclusion of `prop:periodic-determinant-normalization`)
  `e^{it(x)} χ(U_μ(x)) e^{-it(x+μ)} = e^{i h a_μ(x)}` and `h (d_h a)_{μν} = Arg χ(P_{U,μν})`,
  i.e. `d_h a = f` for the principal-argument curvature `f = h⁻² Arg χ(P_U)`
  (`eq:determinant-real-curvature`);
* (admissibility, the conclusion "scaled full curvature uniformly small" of
  `lem:determinant-screen-flux`) logarithms `L` of the full plaquettes of `U' = U^{e^{tZ_c}}`
  with entries bounded by `c`, `2c < min(r, π)`, `r = pairChart` the injectivity radius.
Then, for `V = e^{-haZ_c}U'`: `ℓ_c(L) = h² f` (`f_h = ℓ_c(𝔽_h)`); `V ∈ G_ss`;
`P_{U'} = e^{h² f Z_c} P_V`; the chart logarithm of `P_V` is `Π_ss L`, which lies in the chart
(`eq:determinant-semisimple-curvature`); `Ad V = Ad U'`; the lift change is the central
`G_ss` gauge `z₆^k`. -/
theorem native_determinant_split_of_small_logs
    (hcomm : ∀ x μ ν, shift (shift x μ) ν = shift (shift x ν) μ)
    (h : ℝ) (hh : h ≠ 0) (t : X → ℝ) (a : X → D → ℝ) (U : X → D → SMGaugeGroup)
    (hN : ∀ x μ, Complex.exp (t x * Complex.I) * smChi (U x μ) *
      Complex.exp (-(t (shift x μ) * Complex.I)) = Complex.exp (h * a x μ * Complex.I))
    (hcurl : ∀ x μ ν, h * curl shift a x μ ν = Complex.arg (smChi (plaq shift U x μ ν)))
    (c : ℝ) (hc : 2 * c < min pairChart Real.pi)
    (L : X → D → D → LiePair)
    (hL3 : ∀ x μ ν, NormedSpace.exp (L x μ ν).1 =
      smU3 (plaq shift (gaugeTr shift (fun x => centralElem (t x)) U) x μ ν))
    (hL2 : ∀ x μ ν, NormedSpace.exp (L x μ ν).2 =
      smU2 (plaq shift (gaugeTr shift (fun x => centralElem (t x)) U) x μ ν))
    (hsmall₃ : ∀ x μ ν i j, ‖(L x μ ν).1 i j‖ ≤ c)
    (hsmall₂ : ∀ x μ ν i j, ‖(L x μ ν).2 i j‖ ≤ c) :
    let f : X → D → D → ℝ := fun x μ ν => Complex.arg (smChi (plaq shift U x μ ν)) / h ^ 2
    (∀ x μ ν, ellC (L x μ ν) = (h ^ 2 * f x μ ν : ℝ)) ∧
    (∀ x μ, smChi (splitLinks shift h t a U x μ) = 1 ∧
      (smU3 (splitLinks shift h t a U x μ)).det = 1 ∧
      (smU2 (splitLinks shift h t a U x μ)).det = 1) ∧
    (∀ x μ ν, plaq shift (gaugeTr shift (fun x => centralElem (t x)) U) x μ ν =
      centralElem (h ^ 2 * f x μ ν) * plaq shift (splitLinks shift h t a U) x μ ν) ∧
    (∀ x μ ν, ∀ Y ∈ pairBall pairChart,
      NormedSpace.exp Y.1 = smU3 (plaq shift (splitLinks shift h t a U) x μ ν) →
      NormedSpace.exp Y.2 = smU2 (plaq shift (splitLinks shift h t a U) x μ ν) →
      Y = piSS (L x μ ν)) ∧
    (∀ x μ ν, piSS (L x μ ν) ∈ pairBall pairChart) ∧
    (∀ x μ w, splitLinks shift h t a U x μ * w * (splitLinks shift h t a U x μ)⁻¹ =
      gaugeTr shift (fun x => centralElem (t x)) U x μ * w *
        (gaugeTr shift (fun x => centralElem (t x)) U x μ)⁻¹) ∧
    (∀ (k : X → ℤ) x μ, splitLinks shift h (fun x => t x + 2 * Real.pi * k x) a U x μ =
      gaugeTr shift (fun x => zSix ^ k x) (splitLinks shift h t a U) x μ) ∧
    (smChi zSix = 1 ∧ zSix ^ 6 = 1) := by
  intro f
  have hcr : 2 * c < pairChart := hc.trans_le (min_le_left _ _)
  have hhf : ∀ x μ ν, h ^ 2 * f x μ ν = Complex.arg (smChi (plaq shift U x μ ν)) := by
    intro x μ ν
    simp only [f]
    field_simp
  have hLc : ∀ x μ ν, ellC (L x μ ν) = (h ^ 2 * f x μ ν : ℝ) := by
    intro x μ ν
    rw [hhf, ellC_eq_arg_smChi (L x μ ν) _ c hc (hL2 x μ ν) (hsmall₂ x μ ν),
      smChi_plaq_gaugeTr shift hcomm]
  have hΩ : ∀ x μ ν, piSS (L x μ ν) ∈ pairBall pairChart := by
    intro x μ ν
    obtain ⟨e3, e2⟩ := piSS_entry_le (L x μ ν) c (hsmall₃ x μ ν)
      (hsmall₂ x μ ν)
    exact ⟨fun i j => (e3 i j).trans_lt (by linarith), fun i j => (e2 i j).trans_lt
      (by linarith)⟩
  have hcurl' : ∀ x μ ν, h * curl shift a x μ ν = h ^ 2 * f x μ ν := fun x μ ν => by
    rw [hhf, hcurl]
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := native_determinant_split_core shift h t a U f hN hcurl'
    (pairBall pairChart) pairChart_injOn L hL3 hL2 hLc hΩ
  exact ⟨hLc, h1, h2, h3, hΩ, h4, h5, h6⟩

end Assembly


/-! ### Exact Abelian flux algebra on the periodic grid (`lem:determinant-screen-flux`) -/

section Flux

variable {ι : Type*} [DecidableEq ι] {n : ℕ}

/-- The unit lattice step `h e_μ` on the periodic grid `ι → ZMod n`. -/
def unitStep (μ : ι) : ι → ZMod n := Pi.single μ 1

/-- The oriented Abelian plaquette `p_{μν}(x) = u_μ(x) u_ν(x+μ) / (u_μ(x+ν) u_ν(x))`. -/
def abPlaq (u : (ι → ZMod n) → ι → ℂ) (x : ι → ZMod n) (μ ν : ι) : ℂ :=
  u x μ * u (x + unitStep μ) ν / (u (x + unitStep ν) μ * u x ν)

/-- The principal plaquette argument `φ_{μν}(x) = Arg p_{μν}(x) ∈ (-π, π]`
(`eq:determinant-real-curvature`; `f = h⁻² φ`). -/
def abPhase (u : (ι → ZMod n) → ι → ℂ) (x : ι → ZMod n) (μ ν : ι) : ℝ :=
  Complex.arg (abPlaq u x μ ν)

/-- The real cube sum `h²(d_h f)_{μνκ}(x)` of a real two-form `φ`. -/
def cubeSum (φ : (ι → ZMod n) → ι → ι → ℝ) (x : ι → ZMod n) (μ ν κ : ι) : ℝ :=
  φ (x + unitStep μ) ν κ - φ x ν κ - φ (x + unitStep ν) μ κ + φ x μ κ +
    φ (x + unitStep κ) μ ν - φ x μ ν

/-- **The six oriented plaquettes around a cube multiply to one.** -/
theorem cube_plaquette_prod (u : (ι → ZMod n) → ι → ℂ) (hu : ∀ x μ, u x μ ≠ 0)
    (x : ι → ZMod n) (μ ν κ : ι) :
    abPlaq u (x + unitStep μ) ν κ / abPlaq u x ν κ / abPlaq u (x + unitStep ν) μ κ *
      abPlaq u x μ κ * abPlaq u (x + unitStep κ) μ ν / abPlaq u x μ ν = 1 := by
  unfold abPlaq
  have e1 : x + unitStep ν + unitStep μ = x + unitStep μ + unitStep ν := add_right_comm _ _ _
  have e2 : x + unitStep κ + unitStep μ = x + unitStep μ + unitStep κ := add_right_comm _ _ _
  have e3 : x + unitStep κ + unitStep ν = x + unitStep ν + unitStep κ := add_right_comm _ _ _
  rw [e1, e2, e3]
  have := hu x μ; have := hu x ν; have := hu x κ
  have := hu (x + unitStep μ) ν; have := hu (x + unitStep μ) κ
  have := hu (x + unitStep ν) μ; have := hu (x + unitStep ν) κ
  have := hu (x + unitStep κ) μ; have := hu (x + unitStep κ) ν
  have := hu (x + unitStep μ + unitStep ν) κ; have := hu (x + unitStep μ + unitStep κ) ν
  have := hu (x + unitStep ν + unitStep κ) μ
  field_simp

theorem norm_abPlaq (u : (ι → ZMod n) → ι → ℂ) (hu : ∀ x μ, ‖u x μ‖ = 1) (x : ι → ZMod n)
    (μ ν : ι) : ‖abPlaq u x μ ν‖ = 1 := by
  simp [abPlaq, hu]

/-- A unimodular complex number is `exp (i Arg)`. -/
theorem exp_arg_mul_I_of_norm_one (p : ℂ) (hp : ‖p‖ = 1) :
    Complex.exp (Complex.arg p * Complex.I) = p := by
  have := Complex.norm_mul_exp_arg_mul_I p
  rwa [hp, Complex.ofReal_one, one_mul] at this

/-- The cube sum of the principal arguments is `2π` times an integer. -/
theorem cubeSum_abPhase_integer (u : (ι → ZMod n) → ι → ℂ) (hu : ∀ x μ, ‖u x μ‖ = 1)
    (x : ι → ZMod n) (μ ν κ : ι) :
    ∃ k : ℤ, cubeSum (abPhase u) x μ ν κ = 2 * Real.pi * k := by
  have hu0 : ∀ x μ, u x μ ≠ 0 := fun x μ h => by simpa [h] using hu x μ
  have hcube := cube_plaquette_prod u hu0 x μ ν κ
  have hexp : Complex.exp (cubeSum (abPhase u) x μ ν κ * Complex.I) = 1 := by
    simp only [cubeSum, abPhase]
    push_cast
    simp only [sub_mul, add_mul, Complex.exp_sub, Complex.exp_add,
      exp_arg_mul_I_of_norm_one _ (norm_abPlaq u hu _ _ _)]
    exact hcube
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp hexp
  refine ⟨k, ?_⟩
  have := congrArg Complex.im hk
  simp at this
  linarith

/-- **`d_h f_h = 0` on admissible links**: if every principal plaquette argument satisfies
`|φ| < π/3`, the cube sum vanishes exactly. -/
theorem cubeSum_eq_zero (u : (ι → ZMod n) → ι → ℂ) (hu : ∀ x μ, ‖u x μ‖ = 1)
    (hsmall : ∀ x μ ν, |abPhase u x μ ν| < Real.pi / 3)
    (x : ι → ZMod n) (μ ν κ : ι) : cubeSum (abPhase u) x μ ν κ = 0 := by
  obtain ⟨k, hk⟩ := cubeSum_abPhase_integer u hu x μ ν κ
  have hb : |cubeSum (abPhase u) x μ ν κ| < 2 * Real.pi := by
    unfold cubeSum
    have h1 := hsmall (x + unitStep μ) ν κ
    have h2 := hsmall x ν κ
    have h3 := hsmall (x + unitStep ν) μ κ
    have h4 := hsmall x μ κ
    have h5 := hsmall (x + unitStep κ) μ ν
    have h6 := hsmall x μ ν
    rw [abs_lt] at h1 h2 h3 h4 h5 h6 ⊢
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2, h5.1, h5.2,
      h6.1, h6.2]
  rw [hk] at hb ⊢
  have hpi := Real.pi_pos
  have hk0 : k = 0 := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at hb
    have : |(k : ℝ)| < 1 := by
      by_contra hc
      push Not at hc
      nlinarith
    have : |k| < 1 := by exact_mod_cast this
    have := abs_lt.mp this
    omega
  simp [hk0]

/-! #### Periodic coordinate planes -/

/-- The point `x₀ + a e_μ + b e_ν` of the coordinate plane through `x₀`. -/
def planePt (x₀ : ι → ZMod n) (μ ν : ι) (a b : ZMod n) : ι → ZMod n :=
  x₀ + Pi.single μ a + Pi.single ν b

theorem planePt_add_unitStep_left (x₀ : ι → ZMod n) (μ ν : ι) (a b : ZMod n) :
    planePt x₀ μ ν a b + unitStep μ = planePt x₀ μ ν (a + 1) b := by
  simp only [planePt, unitStep, Pi.single_add]
  abel

theorem planePt_add_unitStep_right (x₀ : ι → ZMod n) (μ ν : ι) (a b : ZMod n) :
    planePt x₀ μ ν a b + unitStep ν = planePt x₀ μ ν a (b + 1) := by
  simp only [planePt, unitStep, Pi.single_add]
  abel

theorem planePt_add (x₀ z : ι → ZMod n) (μ ν : ι) (a b : ZMod n) :
    planePt x₀ μ ν a b + z = planePt (x₀ + z) μ ν a b := by
  simp only [planePt]
  abel

variable [NeZero n]

/-- **The product of the plaquettes of a periodic coordinate plane is one** (telescoping). -/
theorem plane_plaquette_prod (u : (ι → ZMod n) → ι → ℂ) (hu : ∀ x μ, u x μ ≠ 0)
    (x₀ : ι → ZMod n) (μ ν : ι) :
    ∏ a : ZMod n, ∏ b : ZMod n, abPlaq u (planePt x₀ μ ν a b) μ ν = 1 := by
  simp only [abPlaq, planePt_add_unitStep_left, planePt_add_unitStep_right]
  simp only [Finset.prod_div_distrib, Finset.prod_mul_distrib]
  have hA : ∏ a : ZMod n, ∏ b : ZMod n, u (planePt x₀ μ ν (a + 1) b) ν =
      ∏ a : ZMod n, ∏ b : ZMod n, u (planePt x₀ μ ν a b) ν :=
    Fintype.prod_equiv (Equiv.addRight 1) _ _ (fun a => rfl)
  have hB : ∀ a : ZMod n, ∏ b : ZMod n, u (planePt x₀ μ ν a (b + 1)) μ =
      ∏ b : ZMod n, u (planePt x₀ μ ν a b) μ := fun a =>
    Fintype.prod_equiv (Equiv.addRight 1) _ _ (fun b => rfl)
  simp only [hA, hB]
  have h1 : ∏ a : ZMod n, ∏ b : ZMod n, u (planePt x₀ μ ν a b) μ ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun a _ => Finset.prod_ne_zero_iff.mpr fun b _ => hu _ _
  have h2 : ∏ a : ZMod n, ∏ b : ZMod n, u (planePt x₀ μ ν a b) ν ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun a _ => Finset.prod_ne_zero_iff.mpr fun b _ => hu _ _
  field_simp

/-- The flux `h² ∑_{plane} f_{μν} = ∑_{plane} φ_{μν}` through the coordinate plane at `x₀`. -/
def planeFlux (u : (ι → ZMod n) → ι → ℂ) (x₀ : ι → ZMod n) (μ ν : ι) : ℝ :=
  ∑ a : ZMod n, ∑ b : ZMod n, abPhase u (planePt x₀ μ ν a b) μ ν

/-- **Integer flux** (`eq:determinant-flux`): `∑_{plane} φ_{μν} = 2π m`. -/
theorem planeFlux_integer (u : (ι → ZMod n) → ι → ℂ) (hu : ∀ x μ, ‖u x μ‖ = 1)
    (x₀ : ι → ZMod n) (μ ν : ι) : ∃ m : ℤ, planeFlux u x₀ μ ν = 2 * Real.pi * m := by
  have hu0 : ∀ x μ, u x μ ≠ 0 := fun x μ h => by simpa [h] using hu x μ
  have hexp : Complex.exp (planeFlux u x₀ μ ν * Complex.I) = 1 := by
    simp only [planeFlux, abPhase]
    push_cast
    simp only [Finset.sum_mul, Complex.exp_sum,
      exp_arg_mul_I_of_norm_one _ (norm_abPlaq u hu _ _ _)]
    exact plane_plaquette_prod u hu0 x₀ μ ν
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp hexp
  refine ⟨k, ?_⟩
  have := congrArg Complex.im hk
  simp at this
  linarith

/-- **Transverse base-point independence**: if the cube sums vanish (`d_h f = 0`), the flux
through the plane at `x₀ + e_κ` equals the flux at `x₀`. -/
theorem planeFlux_shift (u : (ι → ZMod n) → ι → ℂ)
    (hd : ∀ x μ ν κ, cubeSum (abPhase u) x μ ν κ = 0) (x₀ : ι → ZMod n) (μ ν κ : ι) :
    planeFlux u (x₀ + unitStep κ) μ ν = planeFlux u x₀ μ ν := by
  have hsum : ∑ a : ZMod n, ∑ b : ZMod n, cubeSum (abPhase u) (planePt x₀ μ ν a b) μ ν κ = 0 := by
    simp [hd]
  simp only [cubeSum, planePt_add_unitStep_left, planePt_add_unitStep_right,
    Finset.sum_add_distrib, Finset.sum_sub_distrib] at hsum
  simp only [planePt_add] at hsum
  have hA : ∑ a : ZMod n, ∑ b : ZMod n, abPhase u (planePt x₀ μ ν (a + 1) b) ν κ =
      ∑ a : ZMod n, ∑ b : ZMod n, abPhase u (planePt x₀ μ ν a b) ν κ :=
    Fintype.sum_equiv (Equiv.addRight 1) _ _ (fun a => rfl)
  have hB : ∑ a : ZMod n, ∑ b : ZMod n, abPhase u (planePt x₀ μ ν a (b + 1)) μ κ =
      ∑ a : ZMod n, ∑ b : ZMod n, abPhase u (planePt x₀ μ ν a b) μ κ :=
    Finset.sum_congr rfl fun a _ => Fintype.sum_equiv (Equiv.addRight 1) _ _ (fun b => rfl)
  rw [hA, hB] at hsum
  unfold planeFlux
  linarith

/-- Iterated shifts by `c e_κ` preserve the flux. -/
theorem planeFlux_add_single (u : (ι → ZMod n) → ι → ℂ)
    (hd : ∀ x μ ν κ, cubeSum (abPhase u) x μ ν κ = 0) (μ ν κ : ι) (c : ZMod n)
    (x₀ : ι → ZMod n) : planeFlux u (x₀ + Pi.single κ c) μ ν = planeFlux u x₀ μ ν := by
  have key : ∀ k : ℕ, ∀ x₀ : ι → ZMod n,
      planeFlux u (x₀ + Pi.single κ (k : ZMod n)) μ ν = planeFlux u x₀ μ ν := by
    intro k
    induction k with
    | zero => intro x₀; simp
    | succ k ih =>
      intro x₀
      have : x₀ + Pi.single κ ((k + 1 : ℕ) : ZMod n) =
          (x₀ + Pi.single κ (k : ZMod n)) + unitStep κ := by
        simp only [unitStep, Nat.cast_add, Nat.cast_one, Pi.single_add]
        abel
      rw [this, planeFlux_shift u hd, ih]
  have hc : c = ((c.val : ℕ) : ZMod n) := (ZMod.natCast_zmod_val c).symm
  rw [hc]
  exact key _ x₀

variable [Fintype ι]

/-- **The flux is the same through every parallel plane** (given `d_h f = 0`). -/
theorem planeFlux_const (u : (ι → ZMod n) → ι → ℂ)
    (hd : ∀ x μ ν κ, cubeSum (abPhase u) x μ ν κ = 0) (μ ν : ι) (x : ι → ZMod n) :
    planeFlux u x μ ν = planeFlux u 0 μ ν := by
  have hQ : ∀ z : ι → ZMod n, (fun z => ∀ y, planeFlux u (y + z) μ ν = planeFlux u y μ ν) z := by
    intro z
    rw [← Finset.univ_sum_single z]
    refine Finset.sum_induction _ (fun z => ∀ y, planeFlux u (y + z) μ ν = planeFlux u y μ ν)
      ?_ ?_ ?_
    · intro z w hz hw y
      rw [← add_assoc, hw, hz]
    · intro y; simp
    · intro κ _ y
      exact planeFlux_add_single u hd μ ν κ (z κ) y
  have := hQ x 0
  simpa using this

/-- **Average identity** (`eq:determinant-flux`, second identity, before scaling):
`n² ∑_x φ_{μν}(x) = |Λ| · 2π m_{μν}`; with `f = h⁻² φ`, `L = n h` and `|Λ| = n⁴` this is
`\bar f_{μν} = L⁻⁴ h⁴ ∑_x f_{μν}(x) = 2π m_{μν} / L²`. -/
theorem sum_phase_eq_flux (u : (ι → ZMod n) → ι → ℂ)
    (hd : ∀ x μ ν κ, cubeSum (abPhase u) x μ ν κ = 0) (μ ν : ι) :
    (n : ℝ) ^ 2 * ∑ x : ι → ZMod n, abPhase u x μ ν =
      (Fintype.card (ι → ZMod n) : ℝ) * planeFlux u 0 μ ν := by
  have h1 : ∀ a b : ZMod n, ∑ x : ι → ZMod n, abPhase u (planePt x μ ν a b) μ ν =
      ∑ x : ι → ZMod n, abPhase u x μ ν := fun a b =>
    Fintype.sum_equiv (Equiv.addRight (Pi.single μ a + Pi.single ν b)) _ _
      (fun x => by simp [planePt, add_assoc])
  have h2 : ∑ x : ι → ZMod n, planeFlux u x μ ν =
      (n : ℝ) ^ 2 * ∑ x : ι → ZMod n, abPhase u x μ ν := by
    simp only [planeFlux]
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (ι → ZMod n))) (t := Finset.univ)]
    simp [h1, ZMod.card, pow_two, mul_assoc]
  rw [← h2]
  simp [planeFlux_const u hd μ ν]

/-- **Integer bound** `2π|m| ≤ ‖f‖_{2,h}`, in its scale-free form on a four-dimensional grid:
`(2π m_{μν})² ≤ ∑_x φ_{μν}(x)² = h⁴ ∑_x f_{μν}(x)²` (Cauchy–Schwarz). -/
theorem two_pi_flux_sq_le (u : (ι → ZMod n) → ι → ℂ)
    (hd : ∀ x μ ν κ, cubeSum (abPhase u) x μ ν κ = 0) (hι : Fintype.card ι = 4) (μ ν : ι) :
    (planeFlux u 0 μ ν) ^ 2 ≤ ∑ x : ι → ZMod n, (abPhase u x μ ν) ^ 2 := by
  have hcard : (Fintype.card (ι → ZMod n) : ℝ) = (n : ℝ) ^ 4 := by
    simp [ZMod.card, hι]
  have hS := sum_phase_eq_flux u hd μ ν
  rw [hcard] at hS
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hCS := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (ι → ZMod n)))
    (f := fun x => abPhase u x μ ν)
  rw [Finset.card_univ] at hCS
  rw [hcard] at hCS
  have hS' : ∑ x : ι → ZMod n, abPhase u x μ ν = (n : ℝ) ^ 2 * planeFlux u 0 μ ν := by
    have hn2 : (n : ℝ) ^ 2 ≠ 0 := by positivity
    have : (n : ℝ) ^ 4 = (n : ℝ) ^ 2 * (n : ℝ) ^ 2 := by ring
    rw [this, mul_assoc] at hS
    exact mul_left_cancel₀ hn2 hS
  rw [hS'] at hCS
  have hn4 : (0 : ℝ) < (n : ℝ) ^ 4 := by positivity
  have : (n : ℝ) ^ 4 * planeFlux u 0 μ ν ^ 2 ≤ (n : ℝ) ^ 4 * ∑ x, abPhase u x μ ν ^ 2 := by
    nlinarith [hCS]
  exact le_of_mul_le_mul_left this hn4

/-- **`2π |m_{μν}| ≤ ‖f_{μν}‖_{2,h}`** with `‖f‖_{2,h}² = h⁴ ∑_x f(x)²` and `f = h⁻² φ`. -/
theorem two_pi_abs_flux_le (u : (ι → ZMod n) → ι → ℂ)
    (hd : ∀ x μ ν κ, cubeSum (abPhase u) x μ ν κ = 0) (hι : Fintype.card ι = 4) (μ ν : ι)
    (h : ℝ) (hh : 0 < h) (m : ℤ) (hm : planeFlux u 0 μ ν = 2 * Real.pi * m) :
    2 * Real.pi * |(m : ℝ)| ≤
      Real.sqrt (h ^ 4 * ∑ x : ι → ZMod n, (abPhase u x μ ν / h ^ 2) ^ 2) := by
  have hrw : h ^ 4 * ∑ x : ι → ZMod n, (abPhase u x μ ν / h ^ 2) ^ 2 =
      ∑ x : ι → ZMod n, (abPhase u x μ ν) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    field_simp
  rw [hrw]
  apply Real.le_sqrt_of_sq_le
  have := two_pi_flux_sq_le u hd hι μ ν
  rw [hm] at this
  calc (2 * Real.pi * |(m : ℝ)|) ^ 2 = (2 * Real.pi * m) ^ 2 := by
        rw [mul_pow, sq_abs]; ring
    _ ≤ _ := this

end Flux


/-! ### The determinant screen of `G_SM` links on the periodic grid -/

section ScreenFlux

variable {ι : Type*} [DecidableEq ι] {n : ℕ}

/-- `|χ(y)| = 1`. -/
theorem norm_smChi (y : SMGaugeGroup) : ‖smChi y‖ = 1 :=
  CStarRing.norm_of_mem_unitary (Matrix.det_of_mem_unitary (smU2_mem_unitaryGroup y))

/-- The lattice shift `x ↦ x + h e_μ` of the periodic grid. -/
def gridShift (x : ι → ZMod n) (μ : ι) : ι → ZMod n := x + unitStep μ

theorem gridShift_comm (x : ι → ZMod n) (μ ν : ι) :
    gridShift (gridShift x μ) ν = gridShift (gridShift x ν) μ :=
  add_right_comm _ _ _

/-- The determinant of the full plaquette is the Abelian plaquette of `u = χ(U)`. -/
theorem smChi_plaq_eq_abPlaq (U : (ι → ZMod n) → ι → SMGaugeGroup) (x : ι → ZMod n)
    (μ ν : ι) :
    smChi (plaq gridShift U x μ ν) = abPlaq (fun x μ => smChi (U x μ)) x μ ν := by
  simp only [plaq, abPlaq, map_mul, map_inv, gridShift]
  rw [div_eq_mul_inv, _root_.mul_inv]
  ring

/-- **Mean curvature** (second identity of `eq:determinant-flux`): on a four-dimensional
grid of side `L = n h`, `\bar f_{μν} = L⁻⁴ h⁴ ∑_x f_{μν}(x) = 2π m_{μν} / L²` with
`f = h⁻² φ`. -/
theorem mean_curvature_eq_flux [NeZero n] [Fintype ι] (u : (ι → ZMod n) → ι → ℂ)
    (hd : ∀ x μ ν κ, cubeSum (abPhase u) x μ ν κ = 0) (hι : Fintype.card ι = 4) (μ ν : ι)
    (h : ℝ) (hh : 0 < h) (m : ℤ) (hm : planeFlux u 0 μ ν = 2 * Real.pi * m) :
    ((n : ℝ) * h)⁻¹ ^ 4 * (h ^ 4 * ∑ x : ι → ZMod n, abPhase u x μ ν / h ^ 2) =
      2 * Real.pi * m / ((n : ℝ) * h) ^ 2 := by
  have hcard : (Fintype.card (ι → ZMod n) : ℝ) = (n : ℝ) ^ 4 := by
    simp [ZMod.card, hι]
  have hS := sum_phase_eq_flux u hd μ ν
  rw [hcard, hm] at hS
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hS' : ∑ x : ι → ZMod n, abPhase u x μ ν = (n : ℝ) ^ 2 * (2 * Real.pi * m) := by
    have hn2 : (n : ℝ) ^ 2 ≠ 0 := by positivity
    have : (n : ℝ) ^ 4 = (n : ℝ) ^ 2 * (n : ℝ) ^ 2 := by ring
    rw [this, mul_assoc] at hS
    exact mul_left_cancel₀ hn2 hS
  rw [← Finset.sum_div, hS']
  field_simp

/-- **`lem:determinant-screen-flux`, exact finite content** for `G_SM` links `U` on the
periodic grid `(ℤ/n)⁴` with principal determinant arguments `φ = Arg χ(P_U)`:
1. (`f_h = ℓ_c(𝔽_h)`) every logarithm `L` of a full plaquette with entries bounded by `c`,
   `2c < min(r, π)`, has `ℓ_c(L) = φ`;
2. if `max |φ| < π/3`: `d_h f_h = 0` exactly (cube sums vanish);
3. every periodic coordinate-plane flux is `2π m` with `m ∈ ℤ`;
4. the flux does not depend on the base point of the plane;
5. `n² ∑_x φ_{μν}(x) = n⁴ · 2π m_{μν}` (the mean-curvature identity);
6. `2π |m_{μν}| ≤ ‖f_{μν}‖_{2,h}` for every `h > 0`. -/
theorem determinant_screen_flux_exact [NeZero n] [Fintype ι] (hι : Fintype.card ι = 4)
    (U : (ι → ZMod n) → ι → SMGaugeGroup)
    (hsmall : ∀ x μ ν, |Complex.arg (smChi (plaq gridShift U x μ ν))| < Real.pi / 3) :
    let u : (ι → ZMod n) → ι → ℂ := fun x μ => smChi (U x μ)
    (∀ x μ ν (L : LiePair) (c : ℝ), 2 * c < min pairChart Real.pi →
      NormedSpace.exp L.2 = smU2 (plaq gridShift U x μ ν) → (∀ i j, ‖L.2 i j‖ ≤ c) →
      ellC L = (abPhase u x μ ν : ℂ)) ∧
    (∀ x μ ν κ, cubeSum (abPhase u) x μ ν κ = 0) ∧
    (∀ x₀ μ ν, ∃ m : ℤ, planeFlux u x₀ μ ν = 2 * Real.pi * m) ∧
    (∀ x₀ μ ν, planeFlux u x₀ μ ν = planeFlux u 0 μ ν) ∧
    (∀ μ ν, (n : ℝ) ^ 2 * ∑ x : ι → ZMod n, abPhase u x μ ν =
      (n : ℝ) ^ 4 * planeFlux u 0 μ ν) ∧
    (∀ μ ν (h : ℝ), 0 < h → ∀ m : ℤ, planeFlux u 0 μ ν = 2 * Real.pi * m →
      2 * Real.pi * |(m : ℝ)| ≤
        Real.sqrt (h ^ 4 * ∑ x : ι → ZMod n, (abPhase u x μ ν / h ^ 2) ^ 2)) := by
  intro u
  have hu : ∀ x μ, ‖u x μ‖ = 1 := fun x μ => norm_smChi _
  have hφ : ∀ x μ ν, abPhase u x μ ν = Complex.arg (smChi (plaq gridShift U x μ ν)) := by
    intro x μ ν
    simp only [abPhase, u, smChi_plaq_eq_abPlaq]
  have hsmall' : ∀ x μ ν, |abPhase u x μ ν| < Real.pi / 3 := fun x μ ν => by
    rw [hφ]; exact hsmall x μ ν
  have hd := cubeSum_eq_zero u hu hsmall'
  have hcard : (Fintype.card (ι → ZMod n) : ℝ) = (n : ℝ) ^ 4 := by
    simp [ZMod.card, hι]
  refine ⟨?_, hd, fun x₀ μ ν => planeFlux_integer u hu x₀ μ ν,
    fun x₀ μ ν => planeFlux_const u hd μ ν x₀, fun μ ν => ?_,
    fun μ ν h hh m hm => two_pi_abs_flux_le u hd hι μ ν h hh m hm⟩
  · intro x μ ν L c hc hL hLs
    rw [hφ]
    exact ellC_eq_arg_smChi L _ c hc hL hLs
  · rw [← hcard]
    exact sum_phase_eq_flux u hd μ ν

end ScreenFlux


/-! ### Flat Abelian links on the periodic grid are pure gauge
  (`prop:periodic-determinant-normalization`, exact finite content) -/

section PureGauge

variable {ι : Type*} [DecidableEq ι] {n : ℕ} {G : Type*} [CommGroup G]

/-- The oriented plaquette of a link field with values in a commutative group. -/
def gPlaq (r : (ι → ZMod n) → ι → G) (x : ι → ZMod n) (μ ν : ι) : G :=
  r x μ * r (x + unitStep μ) ν * (r (x + unitStep ν) μ)⁻¹ * (r x ν)⁻¹

/-- The site-gauge action `r_μ(x) ↦ g(x) r_μ(x) g(x + e_μ)⁻¹`. -/
def gaugeAct (g : (ι → ZMod n) → G) (r : (ι → ZMod n) → ι → G) (x : ι → ZMod n) (μ : ι) : G :=
  g x * r x μ * (g (x + unitStep μ))⁻¹

theorem update_add_unitStep_self (x : ι → ZMod n) (ν : ι) (m : ZMod n) :
    Function.update x ν m + unitStep ν = Function.update x ν (m + 1) := by
  funext i
  by_cases hi : i = ν
  · subst hi; simp [unitStep]
  · simp [unitStep, hi]

theorem update_add_unitStep_ne (x : ι → ZMod n) {μ ν : ι} (h : μ ≠ ν) (m : ZMod n) :
    Function.update (x + unitStep μ) ν m = Function.update x ν m + unitStep μ := by
  funext i
  by_cases hi : i = ν
  · subst hi; simp [unitStep, Pi.single_eq_of_ne' h]
  · simp [unitStep, Function.update_of_ne hi]

theorem update_add_unitStep_same (x : ι → ZMod n) (ν : ι) (m : ZMod n) :
    Function.update (x + unitStep ν) ν m = Function.update x ν m := by
  funext i
  by_cases hi : i = ν
  · subst hi; simp
  · simp [unitStep, hi]

theorem add_unitStep_apply_ne (x : ι → ZMod n) {μ ν : ι} (h : μ ≠ ν) :
    (x + unitStep μ : ι → ZMod n) ν = x ν := by
  simp [unitStep, Pi.single_eq_of_ne' h]

theorem gPlaq_mul (r r' : (ι → ZMod n) → ι → G) (x : ι → ZMod n) (μ ν : ι) :
    gPlaq (fun x μ => r x μ * r' x μ) x μ ν = gPlaq r x μ ν * gPlaq r' x μ ν := by
  simp only [gPlaq, mul_inv]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem gPlaq_inv (r : (ι → ZMod n) → ι → G) (x : ι → ZMod n) (μ ν : ι) :
    gPlaq (fun x μ => (r x μ)⁻¹) x μ ν = (gPlaq r x μ ν)⁻¹ := by
  simp only [gPlaq, mul_inv, inv_inv]

/-- Site gauges do not change plaquettes. -/
theorem gPlaq_gaugeAct (g : (ι → ZMod n) → G) (r : (ι → ZMod n) → ι → G) (x : ι → ZMod n)
    (μ ν : ι) : gPlaq (gaugeAct g r) x μ ν = gPlaq r x μ ν := by
  simp only [gPlaq, gaugeAct, add_right_comm x (unitStep ν) (unitStep μ), mul_inv]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, inv_inv]
  abel

/-- Gauge actions compose. -/
theorem gaugeAct_mul (g g' : (ι → ZMod n) → G) (r : (ι → ZMod n) → ι → G) :
    gaugeAct (g' * g) r = gaugeAct g' (gaugeAct g r) := by
  funext x μ
  simp only [gaugeAct, Pi.mul_apply, mul_inv]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

variable [NeZero n]

/-- The product over a periodic coordinate line `∏_{m ∈ ℤ/n} f(m)` as a product over
`0 ≤ j < n`. -/
theorem prod_zmod_eq_prod_range (f : ZMod n → G) :
    ∏ m : ZMod n, f m = ∏ j ∈ Finset.range n, f (j : ZMod n) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, (Nat.succ_pred_eq_of_pos (NeZero.pos n)).symm⟩
  rw [Finset.prod_range]
  exact Fintype.prod_equiv (Equiv.refl _) _ _ (fun i => congrArg f (ZMod.natCast_zmod_val i).symm)

/-- The cycle holonomy `w_ν(x) = ∏_{m ∈ ℤ/n} r_ν(x with ν-coordinate m)`. -/
def cycProd (r : (ι → ZMod n) → ι → G) (x : ι → ZMod n) (ν : ι) : G :=
  ∏ m : ZMod n, r (Function.update x ν m) ν

/-- Site gauges do not change cycle holonomies. -/
theorem cycProd_gaugeAct (g : (ι → ZMod n) → G) (r : (ι → ZMod n) → ι → G)
    (x : ι → ZMod n) (ν : ι) : cycProd (gaugeAct g r) x ν = cycProd r x ν := by
  simp only [cycProd, gaugeAct, update_add_unitStep_self, Finset.prod_mul_distrib,
    Finset.prod_inv_distrib]
  have : ∏ m : ZMod n, g (Function.update x ν (m + 1)) = ∏ m : ZMod n, g (Function.update x ν m) :=
    Fintype.prod_equiv (Equiv.addRight 1) _ _ (fun m => rfl)
  rw [this, mul_right_comm, mul_inv_cancel, one_mul]

/-- **Flat cycle holonomies do not depend on the base point**: if all plaquettes are trivial,
`w_ν(x + e_μ) = w_ν(x)`. -/
theorem cycProd_add_unitStep (r : (ι → ZMod n) → ι → G) (hflat : ∀ x μ ν, gPlaq r x μ ν = 1)
    (x : ι → ZMod n) (μ ν : ι) : cycProd r (x + unitStep μ) ν = cycProd r x ν := by
  by_cases hμν : μ = ν
  · subst hμν
    simp [cycProd, update_add_unitStep_same]
  · have hstrip : ∏ m : ZMod n, gPlaq r (Function.update x ν m) ν μ = 1 := by simp [hflat]
    simp only [gPlaq, update_add_unitStep_self, ← update_add_unitStep_ne x hμν,
      Finset.prod_mul_distrib, Finset.prod_inv_distrib] at hstrip
    have : ∏ m : ZMod n, r (Function.update x ν (m + 1)) μ =
        ∏ m : ZMod n, r (Function.update x ν m) μ :=
      Fintype.prod_equiv (Equiv.addRight 1) _ _ (fun m => rfl)
    rw [this, mul_right_comm _ _ (∏ m : ZMod n, r (Function.update x ν m) μ)⁻¹, mul_assoc _ _
      (∏ m : ZMod n, r (Function.update x ν m) μ)⁻¹, mul_inv_cancel, mul_one,
      mul_inv_eq_one] at hstrip
    exact hstrip.symm

/-- **Flat cycle holonomies are constant on the grid.** -/
theorem cycProd_const [Fintype ι] (r : (ι → ZMod n) → ι → G)
    (hflat : ∀ x μ ν, gPlaq r x μ ν = 1) (x : ι → ZMod n) (ν : ι) :
    cycProd r x ν = cycProd r 0 ν := by
  have hsingle : ∀ (κ : ι) (c : ZMod n) (y : ι → ZMod n),
      cycProd r (y + Pi.single κ c) ν = cycProd r y ν := by
    intro κ c
    have key : ∀ k : ℕ, ∀ y : ι → ZMod n,
        cycProd r (y + Pi.single κ (k : ZMod n)) ν = cycProd r y ν := by
      intro k
      induction k with
      | zero => intro y; simp
      | succ k ih =>
        intro y
        have : y + Pi.single κ ((k + 1 : ℕ) : ZMod n) =
            (y + Pi.single κ (k : ZMod n)) + unitStep κ := by
          simp only [unitStep, Nat.cast_add, Nat.cast_one, Pi.single_add]
          abel
        rw [this, cycProd_add_unitStep r hflat, ih]
    intro y
    rw [show c = ((c.val : ℕ) : ZMod n) from (ZMod.natCast_zmod_val c).symm]
    exact key _ y
  have hQ : ∀ y : ι → ZMod n, cycProd r (0 + ∑ κ, Pi.single κ (x κ)) ν = cycProd r 0 ν := by
    intro y
    refine Finset.sum_induction _ (fun z => ∀ y, cycProd r (y + z) ν = cycProd r y ν)
      (fun z w hz hw y => by rw [← add_assoc, hw, hz]) (fun y => by simp)
      (fun κ _ y => hsingle κ (x κ) y) 0
  simpa [Finset.univ_sum_single] using hQ 0

/-- The line gauge in direction `ν`: `g(x) = ∏_{0 ≤ j < x_ν} r_ν(x with ν-coordinate j)`. -/
def lineGauge (r : (ι → ZMod n) → ι → G) (ν : ι) (x : ι → ZMod n) : G :=
  ∏ j ∈ Finset.range (x ν).val, r (Function.update x ν (j : ZMod n)) ν

/-- The line gauge trivialises direction `ν` when the `ν`-cycles are trivial. -/
theorem gaugeAct_lineGauge_self (r : (ι → ZMod n) → ι → G) (ν : ι)
    (hcyc : ∀ x, cycProd r x ν = 1) (x : ι → ZMod n) :
    gaugeAct (lineGauge r ν) r x ν = 1 := by
  set v := (x ν).val with hv
  have hxv : ((v : ℕ) : ZMod n) = x ν := ZMod.natCast_zmod_val _
  have hstep : (x + unitStep ν : ι → ZMod n) ν = ((v + 1 : ℕ) : ZMod n) := by
    simp [unitStep, hxv]
  have hupd : ∀ j : ℕ, Function.update (x + unitStep ν) ν (j : ZMod n) =
      Function.update x ν (j : ZMod n) := fun j => update_add_unitStep_same x ν _
  have hgx : lineGauge r ν x * r x ν =
      ∏ j ∈ Finset.range (v + 1), r (Function.update x ν (j : ZMod n)) ν := by
    rw [Finset.prod_range_succ, hxv, Function.update_eq_self]
    rfl
  unfold gaugeAct
  rw [hgx]
  have hvn : v < n := ZMod.val_lt _
  rcases Nat.lt_or_ge (v + 1) n with hlt | hge
  · have hval : ((x + unitStep ν : ι → ZMod n) ν).val = v + 1 := by
      rw [hstep, ZMod.val_cast_of_lt hlt]
    simp only [lineGauge, hval, hupd]
    exact mul_inv_cancel _
  · have hvn' : v + 1 = n := le_antisymm hvn hge
    have hval : ((x + unitStep ν : ι → ZMod n) ν).val = 0 := by
      rw [hstep, hvn', ZMod.natCast_self, ZMod.val_zero]
    simp only [lineGauge, hval, Finset.range_zero, Finset.prod_empty, inv_one, mul_one]
    rw [hvn', ← prod_zmod_eq_prod_range (fun m => r (Function.update x ν m) ν)]
    exact hcyc x

/-- If the already-trivialised directions `μ ≠ ν` carry `r_μ = 1` and `r` is flat, the line
gauge in direction `ν` keeps them trivial. -/
theorem gaugeAct_lineGauge_other (r : (ι → ZMod n) → ι → G)
    (hflat : ∀ x μ ν, gPlaq r x μ ν = 1) {μ ν : ι} (hμν : μ ≠ ν)
    (hμ : ∀ x, r x μ = 1) (x : ι → ZMod n) :
    gaugeAct (lineGauge r ν) r x μ = 1 := by
  have hinv : ∀ y, r (y + unitStep μ) ν = r y ν := by
    intro y
    have := hflat y μ ν
    simp only [gPlaq, hμ, one_mul, inv_one, mul_one] at this
    exact mul_inv_eq_one.mp this
  have hg : lineGauge r ν (x + unitStep μ) = lineGauge r ν x := by
    simp only [lineGauge, add_unitStep_apply_ne x hμν, update_add_unitStep_ne x hμν, hinv]
  simp [gaugeAct, hg, hμ]

/-- **A flat link field with trivial cycle holonomies is pure gauge** on the periodic grid:
`r_μ(x) = g(x)⁻¹ g(x + e_μ)`. -/
theorem pureGauge_of_flat [Fintype ι] (r : (ι → ZMod n) → ι → G)
    (hflat : ∀ x μ ν, gPlaq r x μ ν = 1) (hcyc : ∀ x ν, cycProd r x ν = 1) :
    ∃ g : (ι → ZMod n) → G, ∀ x μ, gaugeAct g r x μ = 1 := by
  have key : ∀ F : Finset ι, ∃ g : (ι → ZMod n) → G, ∀ μ ∈ F, ∀ x, gaugeAct g r x μ = 1 := by
    intro F
    induction F using Finset.induction_on with
    | empty => exact ⟨1, fun μ hμ => absurd hμ (Finset.notMem_empty μ)⟩
    | @insert ν F hνF ih =>
      obtain ⟨g, hg⟩ := ih
      set r₁ := gaugeAct g r
      have hflat₁ : ∀ x μ ν, gPlaq r₁ x μ ν = 1 := fun x μ ν => by
        rw [gPlaq_gaugeAct]; exact hflat x μ ν
      have hcyc₁ : ∀ x, cycProd r₁ x ν = 1 := fun x => by
        rw [cycProd_gaugeAct]; exact hcyc x ν
      refine ⟨lineGauge r₁ ν * g, fun μ hμ x => ?_⟩
      rw [gaugeAct_mul]
      rcases Finset.mem_insert.mp hμ with h | hμF
      · rw [h]
        exact gaugeAct_lineGauge_self r₁ ν hcyc₁ x
      · exact gaugeAct_lineGauge_other r₁ hflat₁ (fun h => hνF (by rw [← h]; exact hμF))
          (hg μ hμF) x
  obtain ⟨g, hg⟩ := key Finset.univ
  exact ⟨g, fun x μ => hg μ (Finset.mem_univ μ) x⟩

theorem eq_of_gaugeAct_eq_one (g : (ι → ZMod n) → G) (r : (ι → ZMod n) → ι → G)
    (x : ι → ZMod n) (μ : ι) (h : gaugeAct g r x μ = 1) :
    r x μ = (g x)⁻¹ * g (x + unitStep μ) := by
  unfold gaugeAct at h
  rw [← mul_inv_eq_one.mp h, inv_mul_cancel_left]

end PureGauge


/-! ### The exact Abelian normalization given the Hodge primitive -/

section Normalization

variable {ι : Type*} [DecidableEq ι] {n : ℕ}

/-- The discrete curl `h (d_h a)_{μν}(x) = a_μ(x) + a_ν(x+μ) - a_μ(x+ν) - a_ν(x)`. -/
def gridCurl (a : (ι → ZMod n) → ι → ℝ) (x : ι → ZMod n) (μ ν : ι) : ℝ :=
  a x μ + a (x + unitStep μ) ν - a (x + unitStep ν) μ - a x ν

/-- The backward divergence `h (δ_h a)(x) = ∑_μ (a_μ(x) - a_μ(x - e_μ))` (up to sign
convention). -/
def gridDiv [Fintype ι] (a : (ι → ZMod n) → ι → ℝ) (x : ι → ZMod n) : ℝ :=
  ∑ μ, (a x μ - a (x - unitStep μ) μ)

/-- Constant one-forms are co-closed: `δ_h (a + c) = δ_h a`. -/
theorem gridDiv_add_const [Fintype ι] (a : (ι → ZMod n) → ι → ℝ) (c : ι → ℝ)
    (x : ι → ZMod n) : gridDiv (fun x μ => a x μ + c μ) x = gridDiv a x := by
  simp only [gridDiv]
  exact Finset.sum_congr rfl fun μ _ => by ring

/-- The plaquette of `e^{i h a}` is `e^{i h (h d_h a)}`. -/
theorem gPlaq_circleExp (h : ℝ) (a : (ι → ZMod n) → ι → ℝ) (x : ι → ZMod n) (μ ν : ι) :
    gPlaq (fun x μ => Circle.exp (h * a x μ)) x μ ν = Circle.exp (h * gridCurl a x μ ν) := by
  simp only [gPlaq, gridCurl, ← Circle.exp_neg, ← Circle.exp_add]
  congr 1
  ring

theorem gPlaq_const (k : ι → Circle) (x : ι → ZMod n) (μ ν : ι) :
    gPlaq (fun _ μ => k μ) x μ ν = 1 := by
  simp only [gPlaq]
  rw [mul_right_comm (k μ), mul_inv_cancel_right, mul_inv_cancel]

theorem circleExp_pow (θ : ℝ) (k : ℕ) : Circle.exp θ ^ k = Circle.exp (k * θ) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ih, ← Circle.exp_add]; congr 1; push_cast; ring

variable [NeZero n]

/-- **`prop:periodic-determinant-normalization`, exact gauge construction.**  Let `u` be
periodic `U(1)` links on the grid `(ℤ/n)^ι` and let `a⁰` be a real primitive of their curvature,
`h · h(d_h a⁰) = Arg p_u` (i.e. `d_h a⁰ = f`; for the paper's `a⁰ = δ_h Δ_h^† f` this is the
Hodge identity of `lem:determinant-Hodge-stability`).  Then there are constants
`c_μ ∈ (-π/L, π/L]` (`L = n h`) and real site phases `t` with
* `L c_μ` the principal argument of the cycle holonomy of the flat residual `u e^{-i h a⁰}`
  (the constants retain the cycle holonomies; they are base-point independent);
* `e^{i t(x)} u_μ(x) e^{-i t(x + e_μ)} = e^{i h a_μ(x)}`, `a = a⁰ + c`
  (`eq:determinant-Abelian-normalization`);
* `δ_h a = δ_h a⁰`.
No smallness of `a⁰`, `f` or the cycle phases is used. -/
theorem periodic_abelian_normalization [Fintype ι] (u : (ι → ZMod n) → ι → Circle) (h : ℝ)
    (hh : 0 < h) (a0 : (ι → ZMod n) → ι → ℝ)
    (hprim : ∀ x μ ν, h * gridCurl a0 x μ ν = Complex.arg ((gPlaq u x μ ν : Circle) : ℂ)) :
    ∃ (c : ι → ℝ) (t : (ι → ZMod n) → ℝ),
      (∀ μ, -Real.pi < n * h * c μ ∧ n * h * c μ ≤ Real.pi) ∧
      (∀ μ x, Circle.exp (n * h * c μ) =
        cycProd (fun x μ => u x μ * (Circle.exp (h * a0 x μ))⁻¹) x μ) ∧
      (∀ x μ, Circle.exp (t x) * u x μ * (Circle.exp (t (x + unitStep μ)))⁻¹ =
        Circle.exp (h * (a0 x μ + c μ))) ∧
      (∀ x, gridDiv (fun x μ => a0 x μ + c μ) x = gridDiv a0 x) := by
  set r : (ι → ZMod n) → ι → Circle := fun x μ => u x μ * (Circle.exp (h * a0 x μ))⁻¹ with hr
  have hflat : ∀ x μ ν, gPlaq r x μ ν = 1 := by
    intro x μ ν
    rw [hr, gPlaq_mul, gPlaq_inv, gPlaq_circleExp, ← Circle.exp_arg (gPlaq u x μ ν), ← hprim,
      mul_inv_cancel]
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hnh : (n : ℝ) * h ≠ 0 := by positivity
  set w : ι → Circle := fun μ => cycProd r 0 μ with hw
  set c : ι → ℝ := fun μ => Complex.arg (w μ : ℂ) / (n * h) with hc
  have hcw : ∀ μ, (n : ℝ) * h * c μ = Complex.arg (w μ : ℂ) := fun μ => by
    simp only [hc]; field_simp
  set r' : (ι → ZMod n) → ι → Circle := fun x μ => r x μ * (Circle.exp (h * c μ))⁻¹ with hr'
  have hflat' : ∀ x μ ν, gPlaq r' x μ ν = 1 := by
    intro x μ ν
    rw [hr', gPlaq_mul, gPlaq_inv, gPlaq_const (fun μ => Circle.exp (h * c μ)), hflat, inv_one,
      mul_one]
  have hcyc' : ∀ x ν, cycProd r' x ν = 1 := by
    intro x ν
    have : cycProd r' x ν = cycProd r x ν * ((Circle.exp (h * c ν))⁻¹) ^ n := by
      simp only [cycProd, hr', Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        ZMod.card]
    rw [this, cycProd_const r hflat, inv_pow, circleExp_pow, ← mul_assoc, hcw, Circle.exp_arg]
    exact mul_inv_cancel _
  obtain ⟨g, hg⟩ := pureGauge_of_flat r' hflat' hcyc'
  refine ⟨c, fun x => Complex.arg (g x : ℂ), fun μ => ?_, fun μ x => ?_, fun x μ => ?_,
    fun x => gridDiv_add_const a0 c x⟩
  · rw [hcw]
    exact ⟨Complex.neg_pi_lt_arg _, Complex.arg_le_pi _⟩
  · rw [hcw, Circle.exp_arg, cycProd_const r hflat x μ]
  · simp only [Circle.exp_arg]
    have h1 := hg x μ
    simp only [gaugeAct, hr', hr] at h1
    rw [mul_add, Circle.exp_add, ← mul_inv_eq_one]
    rw [← h1]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel

end Normalization


/-! ### Assembly on the periodic grid: normalization followed by the semisimple split -/

section GridAssembly

variable {ι : Type*} [DecidableEq ι] {n : ℕ}

/-- `χ(y)` as a point of the unit circle. -/
def smChiCircle (y : SMGaugeGroup) : Circle :=
  ⟨smChi y, mem_sphere_zero_iff_norm.2 (norm_smChi y)⟩

@[simp] theorem coe_smChiCircle (y : SMGaugeGroup) : (smChiCircle y : ℂ) = smChi y := rfl

theorem coe_gPlaq_smChiCircle (U : (ι → ZMod n) → ι → SMGaugeGroup) (x : ι → ZMod n)
    (μ ν : ι) :
    ((gPlaq (fun x μ => smChiCircle (U x μ)) x μ ν : Circle) : ℂ) =
      smChi (plaq gridShift U x μ ν) := by
  simp only [gPlaq, Circle.coe_mul, Circle.coe_inv, coe_smChiCircle, plaq, gridShift, map_mul,
    map_inv]

/-- Central site gauges `e^{tZ_c}` do not change plaquettes. -/
theorem plaq_gaugeTr_centralElem (t : (ι → ZMod n) → ℝ) (U : (ι → ZMod n) → ι → SMGaugeGroup)
    (x : ι → ZMod n) (μ ν : ι) :
    plaq gridShift (gaugeTr gridShift (fun x => centralElem (t x)) U) x μ ν =
      plaq gridShift U x μ ν := by
  simp only [plaq, gaugeTr, central_conj]
  rw [plaq_central, gridShift_comm x μ ν]
  have h0 : t x - t (gridShift x μ) + (t (gridShift x μ) - t (gridShift (gridShift x ν) μ)) -
      (t (gridShift x ν) - t (gridShift (gridShift x ν) μ)) - (t x - t (gridShift x ν)) = 0 := by
    ring
  rw [h0, centralElem_zero, one_mul]

theorem gridCurl_add_const (a : (ι → ZMod n) → ι → ℝ) (c : ι → ℝ) (x : ι → ZMod n)
    (μ ν : ι) : gridCurl (fun x μ => a x μ + c μ) x μ ν = gridCurl a x μ ν := by
  simp only [gridCurl]
  ring

/-- **`prop:native-determinant-split` on the periodic grid, modulo its two analytic inputs.**
Let `U` be `G_SM` links on `(ℤ/n)^ι`, `h > 0`, and assume
* (Hodge primitive; the identity `d_h a⁰ = f_h` of `lem:determinant-Hodge-stability`) a real
  `a⁰` with `h · h (d_h a⁰) = Arg χ(P_U)`;
* (admissibility; eventual smallness of the scaled full curvature, `lem:determinant-screen-flux`)
  logarithms `L` of the full plaquettes `P_U` with entries bounded by `c`, `2c < min(r, π)`.
Then there are constants `c_μ ∈ (-π/L, π/L]` retaining the cycle holonomies and real site lifts
`t` such that, with `a = a⁰ + c`: the Abelian normalization
`e^{it(x)} χ(U_μ(x)) e^{-it(x+μ)} = e^{i h a_μ(x)}` holds, `δ_h a = δ_h a⁰`, and all the
conclusions of `native_determinant_split_of_small_logs` hold for `V = e^{-haZ_c}U^{e^{tZ_c}}`:
`V ∈ G_ss`, `ℓ_c(L) = h² f`, `P_{U'} = e^{h² f Z_c} P_V`, chart logarithm of `P_V` equal to
`Π_ss L`, `Ad V = Ad U'`, lift changes are central `G_ss` gauges. -/
theorem native_determinant_split_of_primitive [Fintype ι] [NeZero n]
    (U : (ι → ZMod n) → ι → SMGaugeGroup) (h : ℝ) (hh : 0 < h) (a0 : (ι → ZMod n) → ι → ℝ)
    (hprim : ∀ x μ ν, h * gridCurl a0 x μ ν = Complex.arg (smChi (plaq gridShift U x μ ν)))
    (c : ℝ) (hc : 2 * c < min pairChart Real.pi)
    (L : (ι → ZMod n) → ι → ι → LiePair)
    (hL3 : ∀ x μ ν, NormedSpace.exp (L x μ ν).1 = smU3 (plaq gridShift U x μ ν))
    (hL2 : ∀ x μ ν, NormedSpace.exp (L x μ ν).2 = smU2 (plaq gridShift U x μ ν))
    (hsmall₃ : ∀ x μ ν i j, ‖(L x μ ν).1 i j‖ ≤ c)
    (hsmall₂ : ∀ x μ ν i j, ‖(L x μ ν).2 i j‖ ≤ c) :
    ∃ (cst : ι → ℝ) (t : (ι → ZMod n) → ℝ),
      (∀ μ, -Real.pi < n * h * cst μ ∧ n * h * cst μ ≤ Real.pi) ∧
      (∀ x μ, Complex.exp (t x * Complex.I) * smChi (U x μ) *
        Complex.exp (-(t (gridShift x μ) * Complex.I)) =
          Complex.exp (h * ((a0 x μ + cst μ : ℝ) : ℂ) * Complex.I)) ∧
      (∀ x, gridDiv (fun x μ => a0 x μ + cst μ) x = gridDiv a0 x) ∧
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
  set u : (ι → ZMod n) → ι → Circle := fun x μ => smChiCircle (U x μ) with hu
  have hprim' : ∀ x μ ν, h * gridCurl a0 x μ ν = Complex.arg ((gPlaq u x μ ν : Circle) : ℂ) := by
    intro x μ ν
    rw [hu, coe_gPlaq_smChiCircle]
    exact hprim x μ ν
  obtain ⟨cst, t, hcst, -, hnorm, hdiv⟩ := periodic_abelian_normalization u h hh a0 hprim'
  have hN : ∀ x μ, Complex.exp (t x * Complex.I) * smChi (U x μ) *
      Complex.exp (-(t (gridShift x μ) * Complex.I)) =
        Complex.exp (h * ((a0 x μ + cst μ : ℝ) : ℂ) * Complex.I) := by
    intro x μ
    have := congrArg (fun z : Circle => (z : ℂ)) (hnorm x μ)
    simp only [Circle.coe_mul, Circle.coe_inv, Circle.coe_exp, hu, coe_smChiCircle] at this
    rw [Complex.exp_neg]
    simp only [gridShift]
    rw [this]
    push_cast
    ring_nf
  refine ⟨cst, t, hcst, hN, hdiv, ?_⟩
  intro a f
  have hcurl : ∀ x μ ν, h * curl gridShift a x μ ν =
      Complex.arg (smChi (plaq gridShift U x μ ν)) := by
    intro x μ ν
    have : curl gridShift a x μ ν = gridCurl a x μ ν := rfl
    rw [this, gridCurl_add_const, hprim]
  have hL3' : ∀ x μ ν, NormedSpace.exp (L x μ ν).1 =
      smU3 (plaq gridShift (gaugeTr gridShift (fun x => centralElem (t x)) U) x μ ν) := by
    intro x μ ν; rw [plaq_gaugeTr_centralElem]; exact hL3 x μ ν
  have hL2' : ∀ x μ ν, NormedSpace.exp (L x μ ν).2 =
      smU2 (plaq gridShift (gaugeTr gridShift (fun x => centralElem (t x)) U) x μ ν) := by
    intro x μ ν; rw [plaq_gaugeTr_centralElem]; exact hL2 x μ ν
  obtain ⟨h1, h2, h3, h4, -, h6, h7, -⟩ := native_determinant_split_of_small_logs gridShift
    gridShift_comm h hh.ne' t a U hN hcurl c hc L hL3' hL2' hsmall₃ hsmall₂
  exact ⟨h1, h2, h3, h4, h6, h7⟩

end GridAssembly


/-! ### Non-vacuity witnesses (the trivial links satisfy all hypotheses) -/

section Witness

theorem plaq_one_links {ι : Type*} [DecidableEq ι] {n : ℕ} (x : ι → ZMod n) (μ ν : ι) :
    plaq gridShift (fun _ _ => (1 : SMGaugeGroup)) x μ ν = 1 := by
  simp [plaq]

example : ∀ (n : ℕ) [NeZero n], ∀ x μ ν,
    |Complex.arg (smChi (plaq gridShift (fun (_ : Fin 4 → ZMod n) (_ : Fin 4) =>
      (1 : SMGaugeGroup)) x μ ν))| < Real.pi / 3 := by
  intro n _ x μ ν
  rw [plaq_one_links]
  simp [Real.pi_pos]

example (n : ℕ) [NeZero n] (h : ℝ) (hh : 0 < h) :
    ∃ (cst : Fin 4 → ℝ) (t : (Fin 4 → ZMod n) → ℝ),
      ∀ x μ, Complex.exp (t x * Complex.I) * smChi ((fun _ _ => (1 : SMGaugeGroup)) x μ) *
        Complex.exp (-(t (gridShift x μ) * Complex.I)) =
          Complex.exp (h * (((0 : ℝ) + cst μ : ℝ) : ℂ) * Complex.I) := by
  obtain ⟨cst, t, -, hN, -⟩ := native_determinant_split_of_primitive
    (fun (_ : Fin 4 → ZMod n) (_ : Fin 4) => (1 : SMGaugeGroup)) h hh (fun _ _ => 0)
    (fun x μ ν => by rw [plaq_one_links]; simp [gridCurl]) 0
    (by rw [mul_zero]; exact lt_min pairChart_pos Real.pi_pos)
    (fun _ _ _ => 0) (fun x μ ν => by rw [plaq_one_links]; simp)
    (fun x μ ν => by rw [plaq_one_links]; simp) (fun _ _ _ _ _ => by simp)
    (fun _ _ _ _ _ => by simp)
  exact ⟨cst, t, hN⟩

end Witness

end

end DeterminantFlux

end RenewalGeometry
