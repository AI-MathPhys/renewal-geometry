/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.TorusTrigReconstruction
import RenewalGeometry.DiscreteAnalysis.PeriodicGridHodge

/-!
# Strong stability of the periodic discrete Hodge inverse
  (`lem:determinant-Hodge-stability`, strong-convergence clause; Einstein–SM action closure)

The finite identities and uniform bounds of `lem:determinant-Hodge-stability` are proved in
`DiscreteAnalysis/PeriodicGridHodge.lean` (`GridHodge.hodge_stability_exact`,
`GridHodge.hodge_stability_bounds`).  This file proves the remaining clause: if the raw
reconstructions of the two-forms converge strongly in `L²`, then the raw reconstructions of the
co-closed primitives `a⁰_h = δ_h Δ_h^† f_h` (`GridHodge.scaledPrimitive`) converge strongly in
`L²` (and in `L⁴` in four dimensions) to `a⁰ = δ Δ^† f`, their forward differences converge
strongly in `L²` to `∂ a⁰`, and their trigonometric reconstructions converge strongly in `H¹`.

Rendering: the unit torus `𝕋^d` with grid `(ℤ/N)^d` and mesh `h = 1/N` (see
`Continuum/TorusTrigReconstruction.lean`); the paper's box of side `L = 2π` is its dilation, under
which `f ↦ L⁻² f`-type constant rescalings commute with all statements (`scaledPrimitive` is
linear).  Real grid forms are embedded in `ℂ` (`realC`).

* `dft_realC_bwd`, `dft_realC_lap`, `dft_realC_lapInv`: the backward difference, the lattice
  Laplacian and its inverse on mean-zero data are DFT multipliers (`lamLat k = Σ_i |e(k_i) - 1|²`).
* `coef_scaledPrimitive`: **the multiplier of `δ_h Δ_h^†`**:
  `coef a⁰_ν m = Σ_κ hodgeMult N κ m · coef f_{κν} m`,
  `hodgeMult N κ m = conj(sym_κ)/Σ_i |sym_i|²` on the represented range;
  `norm_hodgeMult_le` (`≤ 1/4`), `norm_sym_mul_hodgeMult_le` (the multiplier of each first
  difference is bounded by `1`), and both converge at each fixed frequency to the continuum
  multipliers (`tendsto_hodgeMult`).
* `contPrimitive F ν` (`a⁰ = δ Δ^† F` in Fourier form: `â⁰_ν(m) = Σ_κ conj(2πi m_κ) F̂_{κν}(m) /
  (4π²|m|²)`, zero at `m = 0`).
* `hodge_strong_convergence` (any `d`) and `hodge_strong_convergence_four` (`d = 4`, adds the
  raw `L⁴` clause).
-/

open MeasureTheory Set Finset Filter Topology UnitAddTorus ComplexConjugate
open scoped BigOperators Real ENNReal

namespace RenewalGeometry.HodgeStrongConvergence

open TorusTrigReconstruction LatticeTorusPlancherel TorusCellEmbedding
  TorusPiecewiseConstantTranslation TorusSobolev GridHodge

noncomputable section

set_option linter.unusedSectionVars false

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance : (volume : Measure UnitAddCircle).IsAddHaarMeasure :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

local notation "L²(" α ")" => Lp ℂ 2 (volume : Measure α)

/-! ### Generic `ℓ²` helpers -/

section Helpers

variable {J : Type*} {α : Type*} {l : Filter α}

theorem norm_sum_sq_le {K : Type*} (s : Finset K) (a : K → ℂ) :
    ‖∑ κ ∈ s, a κ‖ ^ 2 ≤ s.card * ∑ κ ∈ s, ‖a κ‖ ^ 2 := by
  have h1 := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le s a) 2
  exact h1.trans (sq_sum_le_card_mul_sum_sq (s := s) (f := fun κ => ‖a κ‖))

/-- `ℓ²` convergence of finitely many families gives `ℓ²` convergence of their sum. -/
theorem tendsto_tsum_sq_sum_sub {K : Type*} (s : Finset K) {x : K → α → J → ℂ} {x₀ : K → J → ℂ}
    (hs : ∀ κ ∈ s, ∀ a, Summable fun j => ‖x κ a j - x₀ κ j‖ ^ 2)
    (hc : ∀ κ ∈ s, Tendsto (fun a => ∑' j, ‖x κ a j - x₀ κ j‖ ^ 2) l (𝓝 0)) :
    Tendsto (fun a => ∑' j, ‖∑ κ ∈ s, x κ a j - ∑ κ ∈ s, x₀ κ j‖ ^ 2) l (𝓝 0) := by
  have hle : ∀ a, ∑' j, ‖∑ κ ∈ s, x κ a j - ∑ κ ∈ s, x₀ κ j‖ ^ 2 ≤
      s.card * ∑ κ ∈ s, ∑' j, ‖x κ a j - x₀ κ j‖ ^ 2 := by
    intro a
    have hsum : Summable fun j => (s.card : ℝ) * ∑ κ ∈ s, ‖x κ a j - x₀ κ j‖ ^ 2 :=
      (summable_sum fun κ hκ => hs κ hκ a).mul_left _
    rw [← Summable.tsum_finsetSum fun κ hκ => hs κ hκ a, ← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun j => ?_) (Summable.of_nonneg_of_le (fun j => sq_nonneg _)
      (fun j => ?_) hsum) hsum
    · rw [← Finset.sum_sub_distrib]; exact norm_sum_sq_le s _
    · rw [← Finset.sum_sub_distrib]; exact norm_sum_sq_le s _
  have hlim : Tendsto (fun a => (s.card : ℝ) * ∑ κ ∈ s, ∑' j, ‖x κ a j - x₀ κ j‖ ^ 2) l (𝓝 0) := by
    simpa using (tendsto_finset_sum s hc).const_mul (s.card : ℝ)
  exact squeeze_zero (fun a => tsum_nonneg fun j => sq_nonneg _) hle hlim

/-- A bounded multiplier of an `ℓ²` family is in `ℓ²`. -/
theorem summable_mul_sq {c x : J → ℂ} {M : ℝ} (hc : ∀ j, ‖c j‖ ≤ M)
    (hx : Summable fun j => ‖x j‖ ^ 2) : Summable fun j => ‖c j * x j‖ ^ 2 :=
  Summable.of_nonneg_of_le (fun j => sq_nonneg _) (fun j => by
    rw [norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hc j) 2) (sq_nonneg _))
    (hx.mul_left (M ^ 2))

end Helpers

/-! ### The lattice Hodge operators as DFT multipliers -/

section Multipliers

variable {d N : ℕ} [NeZero N]

/-- Complexification of a real grid function. -/
def realC (g : Grid d N → ℝ) : Grid d N → ℂ := fun x => (g x : ℂ)

/-- The lattice symbol `lamLat k = Σ_i |e(k_i) - 1|²` of `-lap`. -/
def lamLat (k : Grid d N) : ℝ := ∑ i, ‖(ZMod.stdAddChar (k i) : ℂ) - 1‖ ^ 2

theorem norm_stdAddChar (a : ZMod N) : ‖(ZMod.stdAddChar a : ℂ)‖ = 1 := by
  simp

theorem dft_realC_bwd (κ : Fin d) (g : Grid d N → ℝ) (k : Grid d N) :
    dft (realC (bwd κ g)) k = (1 - conj (ZMod.stdAddChar (k κ) : ℂ)) * dft (realC g) k := by
  have e : realC (bwd κ g) = realC g - LatticeTorusPlancherel.shiftAdj κ (realC g) := by
    funext x; simp [realC, bwd, LatticeTorusPlancherel.shiftAdj, GridSobolev.gridStep]
  rw [e, dft_sub, dft_shiftAdj, smul_eq_mul]
  ring

theorem dft_realC_lap (g : Grid d N → ℝ) (k : Grid d N) :
    dft (realC (lap g)) k = -(lamLat k : ℂ) * dft (realC g) k := by
  have e : realC (lap g) = ∑ i, (LatticeTorusPlancherel.shift i (realC g) +
      LatticeTorusPlancherel.shiftAdj i (realC g) - (2 : ℂ) • realC g) := by
    funext x
    simp only [realC, lap, fwd, bwd, Finset.sum_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
      LatticeTorusPlancherel.shift, LatticeTorusPlancherel.shiftAdj, GridSobolev.gridStep,
      smul_eq_mul]
    push_cast
    refine Finset.sum_congr rfl fun i _ => by ring
  have hsum : ∀ (F : Fin d → Grid d N → ℂ), dft (∑ i, F i) k = ∑ i, dft (F i) k := by
    intro F
    rw [show (∑ i, F i) = fun x => ∑ i, F i x from by funext x; simp [Finset.sum_apply]]
    exact dft_sum _ F k
  rw [e, hsum]
  simp only [dft_sub, dft_add, dft_shift, dft_shiftAdj, dft_smul, smul_eq_mul]
  unfold lamLat
  push_cast
  rw [neg_mul, Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  set e := (ZMod.stdAddChar (k i) : ℂ)
  have he : e * conj e = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_stdAddChar]; norm_num
  have hn : (‖e - 1‖ : ℂ) ^ 2 = (e - 1) * conj (e - 1) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  rw [hn, map_sub, map_one]
  linear_combination (dft (realC g) k) * he

theorem lamLat_ne_zero {k : Grid d N} (hk : k ≠ 0) : lamLat k ≠ 0 := by
  obtain ⟨i, hi⟩ : ∃ i, k i ≠ 0 := Function.ne_iff.1 hk
  have hpos : 0 < ‖(ZMod.stdAddChar (k i) : ℂ) - 1‖ ^ 2 := by
    have hs := four_mul_abs_le_norm_sym (N := N) i (abs_signedRep_le k i)
    have hm : signedRep k i ≠ 0 := by
      intro h0
      apply hi
      rw [← zcast_signedRep k]
      simp [zcast, h0]
    have hm' : (0 : ℝ) < |(signedRep k i : ℝ)| := by
      rw [abs_pos]; exact_mod_cast hm
    have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    have e : sym N i (signedRep k) = (N : ℂ) * ((ZMod.stdAddChar (k i) : ℂ) - 1) := by
      rw [sym, stdAddChar_eq_exp]
    rw [e, norm_mul, Complex.norm_natCast] at hs
    have : 0 < ‖(ZMod.stdAddChar (k i) : ℂ) - 1‖ := by
      by_contra h0
      have h0' := le_antisymm (not_lt.1 h0) (norm_nonneg ((ZMod.stdAddChar (k i) : ℂ) - 1))
      rw [h0', mul_zero] at hs
      linarith
    positivity
  exact (lt_of_lt_of_le hpos (Finset.single_le_sum (f := fun j =>
    ‖(ZMod.stdAddChar (k j) : ℂ) - 1‖ ^ 2) (fun j _ => sq_nonneg _) (mem_univ i))).ne'

theorem dft_zero_eq_mean (u : Grid d N → ℂ) :
    dft u 0 = ((N : ℂ) ^ d)⁻¹ * ∑ x, u x := by
  simp [dft, latticeChar]

theorem dft_realC_lapInv (g : Grid d N → ℝ) (hg : ∑ x, g x = 0) (k : Grid d N) :
    dft (realC (lapInv g)) k = -dft (realC g) k / lamLat k := by
  by_cases hk : k = 0
  · subst hk
    have h0 : ∑ x, realC (lapInv g) x = 0 := by
      simp only [realC]; rw [← Complex.ofReal_sum, sum_lapInv g hg, Complex.ofReal_zero]
    have h1 : ∑ x, realC g x = 0 := by
      simp only [realC]; rw [← Complex.ofReal_sum, hg, Complex.ofReal_zero]
    rw [dft_zero_eq_mean, dft_zero_eq_mean, h0, h1]; simp
  · have hl := lamLat_ne_zero hk
    have h := dft_realC_lap (lapInv g) k
    have e : realC (lap (lapInv g)) = realC g := by
      funext x; simp only [realC, lap_lapInv g hg]
    rw [e] at h
    rw [h]
    have : (lamLat k : ℂ) ≠ 0 := by exact_mod_cast hl
    field_simp

/-- The multiplier of `δ_h Δ_h^†` (mesh `1/N`) on the represented range. -/
def hodgeMult (N : ℕ) (κ : Fin d) (m : Fin d → ℤ) : ℂ :=
  if ∀ i, |(m i : ℝ)| * 2 ≤ N then conj (sym N κ m) / ((∑ i, ‖sym N i m‖ ^ 2 : ℝ) : ℂ) else 0

/-- The continuum multiplier of `δ Δ^†`: `conj(2πi m_κ) / (4π²|m|²)` (`0` at `m = 0`). -/
def contMult (κ : Fin d) (m : Fin d → ℤ) : ℂ :=
  conj (2 * π * Complex.I * m κ) / ((∑ i, ‖(2 * π * Complex.I * m i : ℂ)‖ ^ 2 : ℝ) : ℂ)

end Multipliers

/-! ### The multiplier of the Hodge primitive -/

section Primitive

variable {d N : ℕ} [NeZero N]

theorem sym_eq_of_signedRep {k : Grid d N} {m : Fin d → ℤ} (hk : signedRep k = m) (i : Fin d) :
    sym N i m = (N : ℂ) * ((ZMod.stdAddChar (k i) : ℂ) - 1) := by
  rw [sym, stdAddChar_eq_exp, hk]

theorem sum_norm_sym_sq_eq {k : Grid d N} {m : Fin d → ℤ} (hk : signedRep k = m) :
    ∑ i, ‖sym N i m‖ ^ 2 = (N : ℝ) ^ 2 * lamLat k := by
  unfold lamLat
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sym_eq_of_signedRep hk, norm_mul, Complex.norm_natCast, mul_pow]

theorem hodgeMult_eq {k : Grid d N} {m : Fin d → ℤ} (hk : signedRep k = m) (κ : Fin d) :
    hodgeMult N κ m = (N : ℂ)⁻¹ * conj ((ZMod.stdAddChar (k κ) : ℂ) - 1) / (lamLat k : ℂ) := by
  have hr : ∀ i, |(m i : ℝ)| * 2 ≤ N := fun i => by rw [← hk]; exact abs_signedRep_le k i
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  rw [hodgeMult, if_pos hr, sum_norm_sym_sq_eq hk, sym_eq_of_signedRep hk, map_mul,
    Complex.conj_natCast]
  push_cast
  by_cases hl : (lamLat k : ℂ) = 0
  · rw [hl]; simp
  · field_simp

theorem dft_realC_scaledPrimitive (f : Grid d N → Fin d → Fin d → ℝ)
    (hmean : ∀ μ ν, ∑ x, f x μ ν = 0) (ν : Fin d) (k : Grid d N) :
    dft (realC (scaledPrimitive ((N : ℝ)⁻¹) f ν)) k =
      ∑ κ, (N : ℂ)⁻¹ * ((1 - conj (ZMod.stdAddChar (k κ) : ℂ)) *
        (-dft (realC (comp f κ ν)) k / lamLat k)) := by
  have e : realC (scaledPrimitive ((N : ℝ)⁻¹) f ν) =
      fun x => ∑ κ, ((N : ℂ)⁻¹ • realC (bwd κ (lapInv (comp f κ ν)))) x := by
    funext x
    simp only [realC, scaledPrimitive, hodgePrimitive, Pi.smul_apply, smul_eq_mul]
    push_cast
    rw [Finset.mul_sum]
  rw [e, dft_sum]
  refine Finset.sum_congr rfl fun κ _ => ?_
  rw [dft_smul, smul_eq_mul, dft_realC_bwd, dft_realC_lapInv (comp f κ ν) (hmean κ ν)]

/-- **The multiplier of `δ_h Δ_h^†`**: `coef a⁰_ν m = Σ_κ hodgeMult N κ m · coef f_{κν} m`. -/
theorem coef_scaledPrimitive (f : Grid d N → Fin d → Fin d → ℝ)
    (hmean : ∀ μ ν, ∑ x, f x μ ν = 0) (ν : Fin d) (m : Fin d → ℤ) :
    coef (realC (scaledPrimitive ((N : ℝ)⁻¹) f ν)) m =
      ∑ κ, hodgeMult N κ m * coef (realC (comp f κ ν)) m := by
  simp only [coef_eq]
  split_ifs with h
  · rw [dft_realC_scaledPrimitive f hmean]
    refine Finset.sum_congr rfl fun κ _ => ?_
    rw [hodgeMult_eq h κ, map_sub, map_one]
    ring
  · simp

/-- `|hodgeMult| ≤ 1/4`. -/
theorem norm_hodgeMult_le (N : ℕ) (κ : Fin d) (m : Fin d → ℤ) : ‖hodgeMult N κ m‖ ≤ 1 / 4 := by
  unfold hodgeMult
  split_ifs with hr
  · rw [norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg
      (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    set S := ∑ i, ‖sym N i m‖ ^ 2
    have hS : ‖sym N κ m‖ ^ 2 ≤ S :=
      Finset.single_le_sum (f := fun i => ‖sym N i m‖ ^ 2) (fun i _ => sq_nonneg _) (mem_univ κ)
    by_cases hs : ‖sym N κ m‖ = 0
    · rw [hs, zero_div]; norm_num
    · have hm : m κ ≠ 0 := by
        intro h0; apply hs; simp [sym, h0]
      have h4 := four_mul_abs_le_norm_sym κ (hr κ)
      have hm1 : (1 : ℝ) ≤ |(m κ : ℝ)| := by
        have : (1 : ℤ) ≤ |m κ| := Int.one_le_abs hm
        exact_mod_cast this
      have hpos : 0 < ‖sym N κ m‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hs)
      rw [div_le_iff₀ (lt_of_lt_of_le (by positivity) hS)]
      nlinarith
  · rw [norm_zero]; norm_num

/-- The multiplier of every first difference of `δ_h Δ_h^†` is bounded by `1`. -/
theorem norm_sym_mul_hodgeMult_le (N : ℕ) (μ κ : Fin d) (m : Fin d → ℤ) :
    ‖sym N μ m * hodgeMult N κ m‖ ≤ 1 := by
  unfold hodgeMult
  split_ifs with hr
  · rw [norm_mul, norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg
      (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    set S := ∑ i, ‖sym N i m‖ ^ 2
    have hSμ : ‖sym N μ m‖ ^ 2 ≤ S :=
      Finset.single_le_sum (f := fun i => ‖sym N i m‖ ^ 2) (fun i _ => sq_nonneg _) (mem_univ μ)
    have hSκ : ‖sym N κ m‖ ^ 2 ≤ S :=
      Finset.single_le_sum (f := fun i => ‖sym N i m‖ ^ 2) (fun i _ => sq_nonneg _) (mem_univ κ)
    by_cases hS : S = 0
    · rw [hS, div_zero, mul_zero]; norm_num
    · have hSpos : 0 < S := lt_of_le_of_ne (Finset.sum_nonneg fun i _ => sq_nonneg _) (Ne.symm hS)
      rw [← mul_div_assoc, div_le_one hSpos]
      nlinarith [sq_nonneg (‖sym N μ m‖ - ‖sym N κ m‖)]
  · rw [mul_zero, norm_zero]; norm_num

theorem sym_zero_of (N : ℕ) {μ : Fin d} {m : Fin d → ℤ} (h : m μ = 0) : sym N μ m = 0 := by
  simp [sym, h]

/-- The discrete multipliers converge at every fixed frequency. -/
theorem tendsto_hodgeMult {n : ℕ → ℕ} (hn : Tendsto n atTop atTop) (κ : Fin d) (m : Fin d → ℤ) :
    Tendsto (fun k => hodgeMult (n k) κ m) atTop (𝓝 (contMult κ m)) := by
  have hev : ∀ᶠ k in atTop, ∀ i, |(m i : ℝ)| * 2 ≤ n k := by
    rw [Filter.eventually_all]
    intro i
    exact (tendsto_natCast_atTop_atTop.comp hn).eventually_ge_atTop _
  by_cases hm0 : m = 0
  · subst hm0
    have h0 : ∀ N, hodgeMult N κ (0 : Fin d → ℤ) = 0 := fun N => by
      simp [hodgeMult, sym_zero_of N (μ := κ) (m := 0) rfl]
    have hc : contMult κ (0 : Fin d → ℤ) = 0 := by simp [contMult]
    simp only [h0, hc]
    exact tendsto_const_nhds
  · have hden : ((∑ i, ‖(2 * π * Complex.I * m i : ℂ)‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
      obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := Function.ne_iff.1 hm0
      have hpos : 0 < ‖(2 * π * Complex.I * m i : ℂ)‖ ^ 2 := by
        rw [TorusSobolev.norm_symbol_sq]
        have : (m i : ℝ) ≠ 0 := by exact_mod_cast hi
        positivity
      have := lt_of_lt_of_le hpos (Finset.single_le_sum (f := fun j =>
        ‖(2 * π * Complex.I * m j : ℂ)‖ ^ 2) (fun j _ => sq_nonneg _) (mem_univ i))
      exact_mod_cast this.ne'
    have hnum : Tendsto (fun k => conj (sym (n k) κ m)) atTop (𝓝 (conj (2 * π * Complex.I * m κ))) :=
      (Complex.continuous_conj.tendsto _).comp (tendsto_sym hn κ m)
    have hd : Tendsto (fun k => ((∑ i, ‖sym (n k) i m‖ ^ 2 : ℝ) : ℂ)) atTop
        (𝓝 ((∑ i, ‖(2 * π * Complex.I * m i : ℂ)‖ ^ 2 : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto _).comp
        (tendsto_finset_sum _ fun i _ => ((tendsto_sym hn i m).norm).pow 2)
    refine (hnum.div hd hden).congr' ?_
    filter_upwards [hev] with k hk
    simp [hodgeMult, hk]

theorem tendsto_sym_mul_hodgeMult {n : ℕ → ℕ} (hn : Tendsto n atTop atTop) (μ κ : Fin d)
    (m : Fin d → ℤ) :
    Tendsto (fun k => sym (n k) μ m * hodgeMult (n k) κ m) atTop
      (𝓝 (2 * π * Complex.I * m μ * contMult κ m)) :=
  (tendsto_sym hn μ m).mul (tendsto_hodgeMult hn κ m)

theorem norm_contMult_le (κ : Fin d) (m : Fin d → ℤ) : ‖contMult κ m‖ ≤ 1 / 4 :=
  le_of_tendsto (tendsto_hodgeMult (n := fun k => k + 1) (tendsto_add_atTop_nat 1) κ m).norm
    (Eventually.of_forall fun k => norm_hodgeMult_le _ κ m)

theorem norm_symbol_mul_contMult_le (μ κ : Fin d) (m : Fin d → ℤ) :
    ‖2 * π * Complex.I * m μ * contMult κ m‖ ≤ 1 :=
  le_of_tendsto (tendsto_sym_mul_hodgeMult (n := fun k => k + 1) (tendsto_add_atTop_nat 1) μ κ m).norm
    (Eventually.of_forall fun k => norm_sym_mul_hodgeMult_le _ μ κ m)

end Primitive

/-! ### The continuum primitive `a⁰ = δ Δ^† F` -/

section Continuum

variable {d : ℕ}

theorem memℓp_mult_sum (c : Fin d → (Fin d → ℤ) → ℂ) {M : ℝ} (hc : ∀ κ m, ‖c κ m‖ ≤ M)
    (G : Fin d → L²(UnitAddTorus (Fin d))) :
    Memℓp (fun m => ∑ κ, c κ m * mFourierCoeff (G κ) m) 2 := by
  refine memℓp_gen ?_
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  have hs : ∀ κ, Summable fun m => ‖c κ m * mFourierCoeff (G κ) m‖ ^ 2 := fun κ =>
    summable_mul_sq (hc κ) (KolmogorovRieszTorus.hasSum_norm_sq_mFourierCoeff (G κ)).summable
  refine Summable.of_nonneg_of_le (fun m => sq_nonneg _) (fun m => norm_sum_sq_le univ _)
    ((summable_sum fun κ _ => hs κ).mul_left _)

/-- **`a⁰ = δ Δ^† F`** on `𝕋^d` in Fourier form: `â⁰_ν(m) = Σ_κ conj(2πi m_κ) F̂_{κν}(m)/(4π²|m|²)`
(`δ = -Σ_κ ∂_κ ι_κ` on two-forms, `Δ^†` the inverse of `-Σ ∂²` vanishing on constants). -/
def contPrimitive (F : Fin d → Fin d → L²(UnitAddTorus (Fin d))) (ν : Fin d) :
    L²(UnitAddTorus (Fin d)) :=
  mFourierBasis.repr.symm ⟨fun m => ∑ κ, contMult κ m * mFourierCoeff (F κ ν) m,
    memℓp_mult_sum _ norm_contMult_le _⟩

/-- The function with the Fourier coefficients `2πi m_μ â⁰_ν(m)` (it is `∂_μ a⁰_ν`). -/
def derivPrimitive (F : Fin d → Fin d → L²(UnitAddTorus (Fin d))) (μ ν : Fin d) :
    L²(UnitAddTorus (Fin d)) :=
  mFourierBasis.repr.symm ⟨fun m => ∑ κ, (2 * π * Complex.I * m μ * contMult κ m) *
    mFourierCoeff (F κ ν) m, memℓp_mult_sum _ (norm_symbol_mul_contMult_le μ) _⟩

theorem mFourierCoeff_contPrimitive (F : Fin d → Fin d → L²(UnitAddTorus (Fin d))) (ν : Fin d)
    (m : Fin d → ℤ) :
    mFourierCoeff (contPrimitive F ν) m = ∑ κ, contMult κ m * mFourierCoeff (F κ ν) m := by
  rw [← mFourierBasis_repr, contPrimitive, LinearIsometryEquiv.apply_symm_apply]

theorem mFourierCoeff_derivPrimitive (F : Fin d → Fin d → L²(UnitAddTorus (Fin d)))
    (μ ν : Fin d) (m : Fin d → ℤ) :
    mFourierCoeff (derivPrimitive F μ ν) m =
      ∑ κ, (2 * π * Complex.I * m μ * contMult κ m) * mFourierCoeff (F κ ν) m := by
  rw [← mFourierBasis_repr, derivPrimitive, LinearIsometryEquiv.apply_symm_apply]

end Continuum

/-! ### Strong convergence -/

section Convergence

variable {d : ℕ} {n : ℕ → ℕ} [∀ k, NeZero (n k)]

/-- The co-closed primitive `a⁰_h = δ_h Δ_h^† f_h` (mesh `1/N`), complexified. -/
def primC (f : ∀ k, Grid d (n k) → Fin d → Fin d → ℝ) (k : ℕ) (ν : Fin d) : Grid d (n k) → ℂ :=
  realC (scaledPrimitive ((n k : ℝ)⁻¹) (f k) ν)

theorem tendsto_coef_primitive (hn : Tendsto n atTop atTop)
    {f : ∀ k, Grid d (n k) → Fin d → Fin d → ℝ}
    {F : Fin d → Fin d → L²(UnitAddTorus (Fin d))}
    (hF : ∀ μ ν, Tendsto (fun k => ‖pcLp (realC (comp (f k) μ ν)) - F μ ν‖) atTop (𝓝 0))
    (c : ℕ → Fin d → (Fin d → ℤ) → ℂ) (c₀ : Fin d → (Fin d → ℤ) → ℂ) {M : ℝ}
    (hc : ∀ k κ m, ‖c k κ m‖ ≤ M) (hc₀ : ∀ κ m, Tendsto (fun k => c k κ m) atTop (𝓝 (c₀ κ m)))
    (ν : Fin d) :
    Tendsto (fun k => ∑' m, ‖∑ κ, c k κ m * coef (realC (comp (f k) κ ν)) m -
      ∑ κ, c₀ κ m * mFourierCoeff (F κ ν) m‖ ^ 2) atTop (𝓝 0) := by
  have hFs : ∀ κ, Summable fun m => ‖mFourierCoeff (F κ ν) m‖ ^ 2 := fun κ =>
    (KolmogorovRieszTorus.hasSum_norm_sq_mFourierCoeff (F κ ν)).summable
  have hM : ∀ κ m, ‖c₀ κ m‖ ≤ M := fun κ m =>
    le_of_tendsto (hc₀ κ m).norm (Eventually.of_forall fun k => hc k κ m)
  refine tendsto_tsum_sq_sum_sub univ (fun κ _ k => ?_) (fun κ _ => ?_)
  · exact summable_norm_sub_sq (summable_mul_sq (hc k κ) (summable_coef_sq _))
      (summable_mul_sq (hM κ) (hFs κ))
  · exact tendsto_tsum_sq_mul_sub (fun k => summable_norm_sub_sq (summable_coef_sq _) (hFs κ))
      (hFs κ) (tendsto_tsum_coef_sub_sq hn (hF κ ν)) (fun k m => hc k κ m) (hc₀ κ)

/-- **`lem:determinant-Hodge-stability`, strong-convergence clause** (any dimension, unit-torus
rendering).  Let `f_h` be real two-forms with zero-mean components (for all large `h⁻¹`) and `R_h^0 f_h → F` strongly in
`L²`.  Then `R_h^0 a⁰_h → a⁰ = δ Δ^† F` strongly in `L²`, `R_h^0 D⁺_μ a⁰_h → ∂_μ a⁰` strongly in
`L²` (weak derivative, `a⁰ ∈ H¹`), and `𝓘_h^trig a⁰_h → a⁰` strongly in `H¹`. -/
theorem hodge_strong_convergence (hn : Tendsto n atTop atTop)
    {f : ∀ k, Grid d (n k) → Fin d → Fin d → ℝ} (hmean : ∀ᶠ k in atTop, ∀ μ ν, ∑ x, f k x μ ν = 0)
    {F : Fin d → Fin d → L²(UnitAddTorus (Fin d))}
    (hF : ∀ μ ν, Tendsto (fun k => ‖pcLp (realC (comp (f k) μ ν)) - F μ ν‖) atTop (𝓝 0)) :
    (∀ ν, Tendsto (fun k => ‖pcLp (primC f k ν) - contPrimitive F ν‖) atTop (𝓝 0)) ∧
    (∀ μ ν, weakDeriv μ (contPrimitive F ν) = derivPrimitive F μ ν) ∧
    (∀ μ ν, Tendsto (fun k => ‖pcLp (Dp μ (primC f k ν)) - weakDeriv μ (contPrimitive F ν)‖)
      atTop (𝓝 0)) ∧
    (∀ ν, Tendsto (fun k => sobSq 1 ⇑(trigLp (primC f k ν) - contPrimitive F ν)) atTop (𝓝 0)) := by
  have hu : ∀ ν, Tendsto (fun k => ‖pcLp (primC f k ν) - contPrimitive F ν‖) atTop (𝓝 0) := by
    intro ν
    refine tendsto_pcLp_of_tsum_coef hn ?_
    have h := tendsto_coef_primitive hn hF (fun k => hodgeMult (n k)) contMult
      (fun k κ m => norm_hodgeMult_le _ κ m) (tendsto_hodgeMult hn) ν
    refine h.congr' ?_
    filter_upwards [hmean] with k hk
    refine tsum_congr fun m => ?_
    rw [primC, coef_scaledPrimitive _ hk, mFourierCoeff_contPrimitive]
  have hv : ∀ μ ν, Tendsto (fun k => ‖pcLp (Dp μ (primC f k ν)) - derivPrimitive F μ ν‖)
      atTop (𝓝 0) := by
    intro μ ν
    refine tendsto_pcLp_of_tsum_coef hn ?_
    have h := tendsto_coef_primitive hn hF (fun k κ m => sym (n k) μ m * hodgeMult (n k) κ m)
      (fun κ m => 2 * π * Complex.I * m μ * contMult κ m)
      (fun k κ m => norm_sym_mul_hodgeMult_le _ μ κ m) (fun κ m => tendsto_sym_mul_hodgeMult hn μ κ m) ν
    refine h.congr' ?_
    filter_upwards [hmean] with k hk
    refine tsum_congr fun m => ?_
    rw [primC, coef_Dp, coef_scaledPrimitive _ hk, mFourierCoeff_derivPrimitive,
      Finset.mul_sum]
    simp only [mul_assoc]
  have hw : ∀ μ ν, weakDeriv μ (contPrimitive F ν) = derivPrimitive F μ ν := fun μ ν =>
    weakDeriv_eq_of_tendsto hn (hu ν) (fun μ => hv μ ν) μ
  refine ⟨hu, hw, fun μ ν => ?_, fun ν => tendsto_sobSq_trigLp_sub hn (hu ν) (fun μ => hv μ ν)⟩
  rw [hw]
  exact hv μ ν

/-- **`lem:determinant-Hodge-stability`, strong-convergence clause in four dimensions**: in
addition, `R_h^0 a⁰_h → a⁰` strongly in `L⁴`. -/
theorem hodge_strong_convergence_four {n : ℕ → ℕ} [∀ k, NeZero (n k)] (hn : Tendsto n atTop atTop)
    {f : ∀ k, Grid 4 (n k) → Fin 4 → Fin 4 → ℝ}
    (hmean : ∀ᶠ k in atTop, ∀ μ ν, ∑ x, f k x μ ν = 0)
    {F : Fin 4 → Fin 4 → L²(UnitAddTorus (Fin 4))}
    (hF : ∀ μ ν, Tendsto (fun k => ‖pcLp (realC (comp (f k) μ ν)) - F μ ν‖) atTop (𝓝 0)) :
    (∀ ν, Tendsto (fun k => ‖pcLp (primC f k ν) - contPrimitive F ν‖) atTop (𝓝 0)) ∧
    (∀ μ ν, Tendsto (fun k => ‖pcLp (Dp μ (primC f k ν)) - weakDeriv μ (contPrimitive F ν)‖)
      atTop (𝓝 0)) ∧
    (∀ ν, Tendsto (fun k => sobSq 1 ⇑(trigLp (primC f k ν) - contPrimitive F ν)) atTop (𝓝 0)) ∧
    (∀ ν, MemLp ((contPrimitive F ν : L²(UnitAddTorus (Fin 4))) : UnitAddTorus (Fin 4) → ℂ) 4
        volume ∧
      Tendsto (fun k => eLpNorm (fun y => pc (primC f k ν) y - contPrimitive F ν y) 4 volume)
        atTop (𝓝 0)) := by
  obtain ⟨hu, -, hv, hH⟩ := hodge_strong_convergence hn hmean hF
  exact ⟨hu, hv, hH, fun ν => tendsto_eLpNorm_four_pc hn (hu ν) (fun μ => hv μ ν)⟩

/-- Non-vacuity: the zero forms satisfy the hypotheses. -/
example : ∀ ν : Fin 2, Tendsto (fun k => ‖pcLp (primC (d := 2) (n := fun k => k + 1)
    (fun _ _ _ _ => (0 : ℝ)) k ν) - contPrimitive (d := 2) (fun _ _ => 0) ν‖) atTop (𝓝 0) := by
  refine (hodge_strong_convergence (d := 2) (n := fun k => k + 1) (tendsto_add_atTop_nat 1)
    (Eventually.of_forall fun k μ ν => by simp) (F := fun _ _ => 0) (fun μ ν => ?_)).1
  have h0 : ∀ k, realC (comp (fun (_ : Grid 2 (k + 1)) (_ _ : Fin 2) => (0 : ℝ)) μ ν) = 0 := by
    intro k; funext x; simp [realC, comp]
  have : ∀ k, pcLp (realC (comp (fun (_ : Grid 2 (k + 1)) (_ _ : Fin 2) => (0 : ℝ)) μ ν)) = 0 := by
    intro k
    rw [h0, ← norm_eq_zero, norm_pcLp, gridNorm_zero]
  simp [this]

end Convergence

end

end RenewalGeometry.HodgeStrongConvergence
