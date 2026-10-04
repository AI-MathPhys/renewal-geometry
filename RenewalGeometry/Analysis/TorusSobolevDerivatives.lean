/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.TorusSobolevEmbedding

/-!
# Classical derivatives of Sobolev functions on `𝕋^d`: `H^m ⊂ C^r` for `m > r + d/2`

Continuation of `Analysis/TorusSobolevEmbedding.lean` (generic, no renewal notions), serving the
embedding steps of `prop:sobolev-bosonic` (`H^s ⊂ W^{1,∞}`) and `cor:stress-topology`
(`H^m_0 ⊂ C^{r_0}` for `m > r_0 + d/2`, and the dual comparison) of the Einstein–Standard-Model
action-closure manuscript.

* `lineShift`, `IsLineDeriv`: the coordinate line `t ↦ t eᵢ` in `𝕋^d` and classical partial
  derivatives along it (generalising `Continuum/TorusSobolevTransfer.lean` from `Fin 3` to any
  finite index type).
* `dCoeff i c = (2πi nᵢ) c`, `coeffMemH_dCoeff`: one derivative costs one Sobolev order.
* `isLineDeriv_fourierSum` (**`H^s ⊂ C¹` for `s > d/2 + 1`**): the Fourier series of an `H^s`
  family is continuously differentiable along every coordinate line, with derivative the Fourier
  series of `2πi nᵢ c_n` (termwise differentiation, `hasDerivAt_tsum`);
  `memH_isLineDeriv` is the form for continuous functions: `‖∂ᵢF‖_∞ ≤ C ‖F‖_{H^s}`.
* `derivCoeff α c = (2πi n)^α c`, `exists_derivatives_of_memH` (**`H^m ⊂ C^r`,
  `m > r + d/2`**): a continuous `H^m` function has continuous classical iterated derivatives
  `D α` for `|α| ≤ r` (each `D (α + eᵢ)` the line derivative of `D α`), with
  `‖D α‖_∞ ≤ C_{m - |α|, d} ‖F‖_{H^m}`; `crNorm_le` sums these into `‖F‖_{C^r} ≤ C ‖F‖_{H^m}`.
* `tendsto_comp_clm`, `dual_bound_transfer`, `dual_Cr_to_negSobolev`: the abstract **dual
  comparison** (convergence in the dual of a weaker norm implies convergence in the dual of a
  stronger one), and its instance `C^r`-dual ⇒ `H^{-m}` on `𝕋^d`.
-/

open Finset Filter Topology MeasureTheory UnitAddTorus
open scoped BigOperators Real ENNReal

namespace RenewalGeometry.TorusSobolev

set_option linter.unusedSectionVars false

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)

noncomputable section

variable {d : Type*} [Fintype d] [DecidableEq d]

/-! ### Coordinate lines and classical partial derivatives -/

/-- The coordinate line `t ↦ t eᵢ` in `𝕋^d`. -/
def lineShift (i : d) (t : ℝ) : UnitAddTorus d := Pi.single i (t : UnitAddCircle)

theorem lineShift_zero (i : d) : lineShift i 0 = 0 := by
  unfold lineShift
  simp

theorem mFourier_add_apply (n : d → ℤ) (x y : UnitAddTorus d) :
    mFourier n (x + y) = mFourier n x * mFourier n y := by
  simp only [mFourier, ContinuousMap.coe_mk, Pi.add_apply, ← prod_mul_distrib]
  refine prod_congr rfl fun i _ => ?_
  rw [fourier_apply, fourier_apply, fourier_apply, smul_add, AddCircle.toCircle_add,
    Circle.coe_mul]

theorem mFourier_lineShift (n : d → ℤ) (i : d) (t : ℝ) :
    mFourier n (lineShift i t) = Complex.exp (2 * π * Complex.I * n i * t) := by
  simp only [mFourier, ContinuousMap.coe_mk, lineShift]
  rw [Finset.prod_eq_single i]
  · rw [Pi.single_eq_same, fourier_coe_apply]
    congr 1
    push_cast
    ring
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, fourier_apply, smul_zero, AddCircle.toCircle_zero, Circle.coe_one]
  · intro h; exact absurd (mem_univ i) h

/-- `F'` is the classical partial derivative of `F` in the `i`-th coordinate direction:
`t ↦ F(x + t eᵢ)` has derivative `F'(x)` at `t = 0`, for every `x ∈ 𝕋^d`. -/
def IsLineDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (i : d)
    (F F' : UnitAddTorus d → E) : Prop :=
  ∀ x, HasDerivAt (fun t : ℝ => F (x + lineShift i t)) (F' x) 0

/-! ### One derivative -/

/-- The Fourier symbol of `∂ᵢ`: `(∂ᵢ c)(n) = 2πi nᵢ c(n)`. -/
def dCoeff (i : d) (c : (d → ℤ) → ℂ) : (d → ℤ) → ℂ :=
  fun n => (2 * π * Complex.I * n i) * c n

theorem norm_symbol_sq (i : d) (n : d → ℤ) :
    ‖(2 * π * Complex.I * n i : ℂ)‖ ^ 2 = (2 * π * n i) ^ 2 := by
  have : (2 * π * Complex.I * n i : ℂ) = ((2 * π * n i : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem norm_symbol_sq_le (i : d) (n : d → ℤ) :
    ‖(2 * π * Complex.I * n i : ℂ)‖ ^ 2 ≤ sobWeight n := by
  rw [norm_symbol_sq]; exact sq_symbol_le_sobWeight n i

/-- **One derivative costs one Sobolev order**: `c ∈ H^s ⇒ ∂ᵢ c ∈ H^{s-1}` with
`‖∂ᵢ c‖_{H^{s-1}} ≤ ‖c‖_{H^s}`. -/
theorem coeffMemH_dCoeff {s : ℝ} {c : (d → ℤ) → ℂ} (hc : CoeffMemH s c) (i : d) :
    CoeffMemH (s - 1) (dCoeff i c) ∧ coeffSobSq (s - 1) (dCoeff i c) ≤ coeffSobSq s c := by
  have hle : ∀ n, sobWeight n ^ (s - 1) * ‖dCoeff i c n‖ ^ 2 ≤ sobWeight n ^ s * ‖c n‖ ^ 2 := by
    intro n
    simp only [dCoeff]
    rw [norm_mul, mul_pow]
    have hw := sobWeight_pos n
    rw [Real.rpow_sub_one hw.ne']
    have h1 := norm_symbol_sq_le i n
    calc sobWeight n ^ s / sobWeight n * (‖(2 * π * Complex.I * n i : ℂ)‖ ^ 2 * ‖c n‖ ^ 2)
        ≤ sobWeight n ^ s / sobWeight n * (sobWeight n * ‖c n‖ ^ 2) := by
          gcongr
      _ = sobWeight n ^ s * ‖c n‖ ^ 2 := by field_simp
  have hsum : CoeffMemH (s - 1) (dCoeff i c) :=
    Summable.of_nonneg_of_le (coeffSobSq_term_nonneg _ _) hle hc
  exact ⟨hsum, Summable.tsum_le_tsum hle hsum hc⟩

/-- **`H^s ⊂ C¹` for `s > d/2 + 1`** (termwise differentiation of the Fourier series): the Fourier
series of an `H^s` family has, along every coordinate line, the classical derivative given by the
Fourier series of `2πi nᵢ c_n`. -/
theorem isLineDeriv_fourierSum {s : ℝ} (hs : (Fintype.card d : ℝ) / 2 + 1 < s)
    {c : (d → ℤ) → ℂ} (hc : CoeffMemH s c) (i : d) :
    IsLineDeriv i (fourierSum c) (fourierSum (dCoeff i c)) := by
  have hc1 := (summable_norm_of_coeffMemH (by linarith) hc).1
  have hd := (coeffMemH_dCoeff hc i).1
  have hd1 := (summable_norm_of_coeffMemH (by linarith) hd).1
  intro x
  set a : (d → ℤ) → ℂ := fun n => 2 * π * Complex.I * n i
  set g : (d → ℤ) → ℝ → ℂ := fun n t => c n * mFourier n (x + lineShift i t)
  set g' : (d → ℤ) → ℝ → ℂ := fun n t => dCoeff i c n * mFourier n (x + lineShift i t)
  have hgform : ∀ n t, g n t = (c n * mFourier n x) * Complex.exp (a n * t) := by
    intro n t
    simp only [g, a, mFourier_add_apply, mFourier_lineShift]
    ring
  have hg : ∀ n t, HasDerivAt (g n) (g' n t) t := by
    intro n t
    have h1 : HasDerivAt (fun t : ℝ => a n * (t : ℂ)) (a n) t := by
      simpa using ((hasDerivAt_id t).ofReal_comp).const_mul (a n)
    have h2 := (h1.cexp).const_mul (c n * mFourier n x)
    have e1 : g n = fun t : ℝ => (c n * mFourier n x) * Complex.exp (a n * t) :=
      funext fun t => hgform n t
    rw [e1]
    refine h2.congr_deriv ?_
    simp only [g', dCoeff, a]
    rw [mFourier_add_apply, mFourier_lineShift]
    ring
  have hg' : ∀ n t, ‖g' n t‖ ≤ ‖dCoeff i c n‖ := by
    intro n t
    simp only [g', norm_mul, norm_mFourier_apply, mul_one, le_refl]
  have hg0 : Summable fun n => g n 0 := (fourierSum_apply hc1 (x + lineShift i 0)).summable
  have H := hasDerivAt_tsum hd1 hg hg' hg0 0
  have e1 : (fun t : ℝ => fourierSum c (x + lineShift i t)) = fun t => ∑' n, g n t :=
    funext fun t => (fourierSum_apply hc1 _).tsum_eq.symm
  have e2 : ∑' n, g' n 0 = fourierSum (dCoeff i c) x := by
    simp only [g', lineShift_zero, add_zero]
    exact (fourierSum_apply hd1 x).tsum_eq
  rw [e1, ← e2]
  exact H

/-- **`H^s ⊂ W^{1,∞}` / `C¹` for continuous functions, `s > d/2 + 1`** (`prop:sobolev-bosonic`):
a continuous `F ∈ H^s(𝕋^d)` has a continuous classical partial derivative `∂ᵢF` in every
direction, with Fourier coefficients `2πi nᵢ F̂(n)` and `‖∂ᵢF‖_∞ ≤ C_{s-1,d} ‖F‖_{H^s}`. -/
theorem memH_isLineDeriv {s : ℝ} (hs : (Fintype.card d : ℝ) / 2 + 1 < s)
    (F : C(UnitAddTorus d, ℂ)) (hF : MemH s F) (i : d) :
    ∃ F' : C(UnitAddTorus d, ℂ), IsLineDeriv i ⇑F ⇑F' ∧
      (∀ n, mFourierCoeff F' n = (2 * π * Complex.I * n i) * mFourierCoeff F n) ∧
      ‖F'‖ ≤ embConst d (s - 1) * sobNorm s F := by
  have hd := coeffMemH_dCoeff hF i
  obtain ⟨hd1, hd2⟩ := summable_norm_of_coeffMemH (by linarith) hd.1
  refine ⟨fourierSum (dCoeff i (mFourierCoeff F)), ?_, mFourierCoeff_fourierSum hd1, ?_⟩
  · have := isLineDeriv_fourierSum hs hF i
    rwa [← eq_fourierSum_of_memH (by linarith) F hF] at this
  · refine (norm_fourierSum_le hd1).trans (hd2.trans ?_)
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hd.2) (embConst_nonneg _)

/-! ### Iterated derivatives: `H^m ⊂ C^r` for `m > r + d/2` -/

/-- The order `|α| = Σ_j α_j` of a multi-index. -/
def mOrder (α : d → ℕ) : ℕ := ∑ j, α j

/-- The Fourier symbol `(2πi n)^α = Π_j (2πi n_j)^{α_j}` of `∂^α`. -/
def symbol (α : d → ℕ) (n : d → ℤ) : ℂ := ∏ j, (2 * π * Complex.I * n j) ^ α j

/-- The coefficients `(2πi n)^α c(n)` of `∂^α`. -/
def derivCoeff (α : d → ℕ) (c : (d → ℤ) → ℂ) : (d → ℤ) → ℂ := fun n => symbol α n * c n

theorem derivCoeff_zero (c : (d → ℤ) → ℂ) : derivCoeff 0 c = c := by
  funext n; simp [derivCoeff, symbol]

theorem symbol_add_single (α : d → ℕ) (i : d) (n : d → ℤ) :
    (2 * π * Complex.I * n i) * symbol α n = symbol (α + Pi.single i 1) n := by
  unfold symbol
  simp only [Pi.add_apply, pow_add, prod_mul_distrib]
  rw [mul_comm]
  congr 1
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hj; rw [Pi.single_eq_of_ne hj, pow_zero]
  · intro h; exact absurd (mem_univ i) h

theorem dCoeff_derivCoeff (i : d) (α : d → ℕ) (c : (d → ℤ) → ℂ) :
    dCoeff i (derivCoeff α c) = derivCoeff (α + Pi.single i 1) c := by
  funext n
  simp only [dCoeff, derivCoeff]
  rw [← symbol_add_single]
  ring

theorem mOrder_add_single (α : d → ℕ) (i : d) : mOrder (α + Pi.single i 1) = mOrder α + 1 := by
  unfold mOrder
  simp only [Pi.add_apply, sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj; rw [Pi.single_eq_of_ne hj]
  · intro h; exact absurd (mem_univ i) h

/-- `|(2πi n)^α|² ≤ ⟨n⟩^{2|α|}`. -/
theorem norm_symbol_sq_le_pow (α : d → ℕ) (n : d → ℤ) :
    ‖symbol α n‖ ^ 2 ≤ sobWeight n ^ mOrder α := by
  unfold symbol mOrder
  rw [norm_prod, ← prod_pow, ← prod_pow_eq_pow_sum]
  refine prod_le_prod (fun j _ => by positivity) (fun j _ => ?_)
  rw [norm_pow, ← pow_mul, mul_comm (α j) 2, pow_mul]
  exact pow_le_pow_left₀ (sq_nonneg _) (norm_symbol_sq_le j n) _

/-- **`|α|` derivatives cost `|α|` Sobolev orders**: `c ∈ H^s ⇒ ∂^α c ∈ H^{s-|α|}` with
`‖∂^α c‖_{H^{s-|α|}} ≤ ‖c‖_{H^s}`. -/
theorem coeffMemH_derivCoeff {s : ℝ} {c : (d → ℤ) → ℂ} (hc : CoeffMemH s c) (α : d → ℕ) :
    CoeffMemH (s - mOrder α) (derivCoeff α c) ∧
      coeffSobSq (s - mOrder α) (derivCoeff α c) ≤ coeffSobSq s c := by
  have hle : ∀ n, sobWeight n ^ (s - mOrder α) * ‖derivCoeff α c n‖ ^ 2 ≤
      sobWeight n ^ s * ‖c n‖ ^ 2 := by
    intro n
    simp only [derivCoeff]
    rw [norm_mul, mul_pow]
    have hw := sobWeight_pos n
    rw [Real.rpow_sub hw, Real.rpow_natCast]
    have h1 := norm_symbol_sq_le_pow α n
    have hk : 0 < sobWeight n ^ mOrder α := pow_pos hw _
    calc sobWeight n ^ s / sobWeight n ^ mOrder α * (‖symbol α n‖ ^ 2 * ‖c n‖ ^ 2)
        ≤ sobWeight n ^ s / sobWeight n ^ mOrder α * (sobWeight n ^ mOrder α * ‖c n‖ ^ 2) := by
          gcongr
      _ = sobWeight n ^ s * ‖c n‖ ^ 2 := by field_simp
  have hsum : CoeffMemH (s - mOrder α) (derivCoeff α c) :=
    Summable.of_nonneg_of_le (coeffSobSq_term_nonneg _ _) hle hc
  exact ⟨hsum, Summable.tsum_le_tsum hle hsum hc⟩

/-- The candidate `∂^α F = Σ_n (2πi n)^α F̂(n) e_n` (a continuous function). -/
def fourierDeriv (α : d → ℕ) (F : UnitAddTorus d → ℂ) : C(UnitAddTorus d, ℂ) :=
  fourierSum (derivCoeff α (mFourierCoeff F))

theorem fourierDeriv_zero {m : ℝ} (hm : (Fintype.card d : ℝ) / 2 < m)
    (F : C(UnitAddTorus d, ℂ)) (hF : MemH m F) : fourierDeriv 0 F = F := by
  unfold fourierDeriv
  rw [derivCoeff_zero]
  exact (eq_fourierSum_of_memH hm F hF).symm

/-- The Fourier coefficients of `∂^α F` are `(2πi n)^α F̂(n)`. -/
theorem mFourierCoeff_fourierDeriv {m : ℝ} {α : d → ℕ}
    (hm : (Fintype.card d : ℝ) / 2 + mOrder α < m) {F : UnitAddTorus d → ℂ} (hF : MemH m F)
    (n : d → ℤ) : mFourierCoeff (fourierDeriv α F) n = symbol α n * mFourierCoeff F n := by
  have h := (coeffMemH_derivCoeff hF α).1
  exact mFourierCoeff_fourierSum (summable_norm_of_coeffMemH (by linarith) h).1 n

/-- `∂^{α + eᵢ} F` is the classical `i`-th line derivative of `∂^α F` when `m > d/2 + |α| + 1`. -/
theorem isLineDeriv_fourierDeriv {m : ℝ} {α : d → ℕ}
    (hm : (Fintype.card d : ℝ) / 2 + mOrder α + 1 < m) {F : UnitAddTorus d → ℂ}
    (hF : MemH m F) (i : d) :
    IsLineDeriv i (fourierDeriv α F) (fourierDeriv (α + Pi.single i 1) F) := by
  have h := (coeffMemH_derivCoeff hF α).1
  have := isLineDeriv_fourierSum (s := m - mOrder α) (by linarith) h i
  rwa [dCoeff_derivCoeff] at this

/-- `‖∂^α F‖_∞ ≤ C_{m-|α|,d} ‖F‖_{H^m}` when `m > d/2 + |α|`. -/
theorem norm_fourierDeriv_le {m : ℝ} {α : d → ℕ} (hm : (Fintype.card d : ℝ) / 2 + mOrder α < m)
    {F : UnitAddTorus d → ℂ} (hF : MemH m F) :
    ‖fourierDeriv α F‖ ≤ embConst d (m - mOrder α) * sobNorm m F := by
  obtain ⟨h, hle⟩ := coeffMemH_derivCoeff hF α
  obtain ⟨h1, h2⟩ := summable_norm_of_coeffMemH (by linarith) h
  refine (norm_fourierSum_le h1).trans (h2.trans ?_)
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hle) (embConst_nonneg _)

/-- The multi-indices of order at most `r`. -/
def multiIndices (d : Type*) [Fintype d] [DecidableEq d] (r : ℕ) : Finset (d → ℕ) :=
  (Fintype.piFinset fun _ => Finset.range (r + 1)).filter fun α => mOrder α ≤ r

theorem mem_multiIndices {r : ℕ} {α : d → ℕ} : α ∈ multiIndices d r ↔ mOrder α ≤ r := by
  unfold multiIndices
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  refine ⟨fun h => h.2, fun h => ⟨fun j => ?_, h⟩⟩
  rw [Finset.mem_range, Nat.lt_succ_iff]
  exact (Finset.single_le_sum (f := α) (fun _ _ => Nat.zero_le _) (mem_univ j)).trans h

/-- The `C^r(𝕋^d)` norm `Σ_{|α| ≤ r} ‖∂^α F‖_∞`, with the derivatives computed by
`fourierDeriv` (these are the classical iterated derivatives, `exists_derivatives_of_memH`). -/
def crNorm (r : ℕ) (F : UnitAddTorus d → ℂ) : ℝ := ∑ α ∈ multiIndices d r, ‖fourierDeriv α F‖

/-- The constant `Σ_{|α| ≤ r} C_{m-|α|,d}` of the embedding `H^m ⊂ C^r`. -/
def crConst (d : Type*) [Fintype d] [DecidableEq d] (r : ℕ) (m : ℝ) : ℝ :=
  ∑ α ∈ multiIndices d r, embConst d (m - mOrder α)

theorem crConst_nonneg (r : ℕ) (m : ℝ) : 0 ≤ crConst d r m :=
  sum_nonneg fun _ _ => embConst_nonneg _

/-- **`‖F‖_{C^r} ≤ C ‖F‖_{H^m}` for `m > r + d/2`.** -/
theorem crNorm_le {r : ℕ} {m : ℝ} (hm : (Fintype.card d : ℝ) / 2 + r < m)
    {F : UnitAddTorus d → ℂ} (hF : MemH m F) : crNorm r F ≤ crConst d r m * sobNorm m F := by
  unfold crNorm crConst
  rw [Finset.sum_mul]
  refine sum_le_sum fun α hα => norm_fourierDeriv_le ?_ hF
  have : (mOrder α : ℝ) ≤ r := by exact_mod_cast mem_multiIndices.mp hα
  linarith

/-- **Sobolev embedding `H^m(𝕋^d) ⊂ C^r(𝕋^d)` for `m > r + d/2`** (`cor:stress-topology`, the
embedding `H^m_0 ⊂ C^{r_0}` for `m > r_0 + 2` in four dimensions, torus form): a continuous
`F ∈ H^m` has continuous classical iterated derivatives `D α = ∂^α F` for `|α| ≤ r` —
`D 0 = F`, and `D (α + eᵢ)` is the classical `i`-th partial derivative of `D α` whenever
`|α| < r` — with `‖D α‖_∞ ≤ C_{m-|α|,d} ‖F‖_{H^m}` and `‖F‖_{C^r} ≤ C_{r,m,d} ‖F‖_{H^m}`. -/
theorem exists_derivatives_of_memH {r : ℕ} {m : ℝ} (hm : (Fintype.card d : ℝ) / 2 + r < m)
    (F : C(UnitAddTorus d, ℂ)) (hF : MemH m F) :
    ∃ D : (d → ℕ) → C(UnitAddTorus d, ℂ), D 0 = F ∧
      (∀ α i, mOrder α < r → IsLineDeriv i ⇑(D α) ⇑(D (α + Pi.single i 1))) ∧
      (∀ α, mOrder α ≤ r → ∀ n, mFourierCoeff (D α) n = symbol α n * mFourierCoeff F n) ∧
      (∀ α, mOrder α ≤ r → ‖D α‖ ≤ embConst d (m - mOrder α) * sobNorm m F) ∧
      ∑ α ∈ multiIndices d r, ‖D α‖ ≤ crConst d r m * sobNorm m F := by
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  refine ⟨fun α => fourierDeriv α F, fourierDeriv_zero (by linarith) F hF, ?_, ?_, ?_,
    crNorm_le hm hF⟩
  · intro α i hα
    have : (mOrder α : ℝ) + 1 ≤ r := by exact_mod_cast hα
    exact isLineDeriv_fourierDeriv (by linarith) hF i
  · intro α hα n
    have : (mOrder α : ℝ) ≤ r := by exact_mod_cast hα
    exact mFourierCoeff_fourierDeriv (by linarith) hF n
  · intro α hα
    have : (mOrder α : ℝ) ≤ r := by exact_mod_cast hα
    exact norm_fourierDeriv_le (by linarith) hF

/-! ### Dual comparison -/

/-- **Dual comparison, operator form** (`cor:stress-topology`): if `ι : E →L F` is a continuous
linear map (e.g. the embedding `H^m ↪ C^{r_0}`), convergence `T_h → T` in the dual of `F` implies
convergence of the restrictions `T_h ∘ ι → T ∘ ι` in the dual of `E`. -/
theorem tendsto_comp_clm {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G]
    [NormedSpace 𝕜 G] (ι : E →L[𝕜] F) {T : ℕ → F →L[𝕜] G} {T₀ : F →L[𝕜] G}
    (h : Tendsto T atTop (𝓝 T₀)) :
    Tendsto (fun k => (T k).comp ι) atTop (𝓝 (T₀.comp ι)) :=
  (((ContinuousLinearMap.compL 𝕜 E F G).flip ι).continuous.tendsto T₀).comp h

/-- **Dual comparison, seminorm form** (`cor:stress-topology`): if `p ≤ C q` and a functional is
bounded by `ε p`, it is bounded by `ε C q`. -/
theorem dual_bound_transfer {V : Type*} (p q : V → ℝ) {C : ℝ} (hpq : ∀ v, p v ≤ C * q v)
    (L : V → ℂ) {ε : ℝ} (hε : 0 ≤ ε) (hL : ∀ v, ‖L v‖ ≤ ε * p v) (v : V) :
    ‖L v‖ ≤ ε * C * q v :=
  (hL v).trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hpq v) hε)

/-- **`C^r`-dual convergence implies `H^{-m}` convergence on `𝕋^d`, `m > r + d/2`**
(`cor:stress-topology`, the embedding/duality step, torus form): if
`|L_k v - L v| ≤ ε_k ‖v‖_{C^r}` for all continuous test functions with `ε_k → 0`, then
`|L_k v - L v| ≤ ε_k C ‖v‖_{H^m}` for every continuous `v ∈ H^m`, with `ε_k C → 0`. -/
theorem dual_Cr_to_negSobolev {r : ℕ} {m : ℝ} (hm : (Fintype.card d : ℝ) / 2 + r < m)
    (L : ℕ → C(UnitAddTorus d, ℂ) → ℂ) (L₀ : C(UnitAddTorus d, ℂ) → ℂ) (ε : ℕ → ℝ)
    (hε0 : ∀ k, 0 ≤ ε k) (hε : Tendsto ε atTop (𝓝 0))
    (hL : ∀ k v, ‖L k v - L₀ v‖ ≤ ε k * crNorm r v) :
    (∀ k (v : C(UnitAddTorus d, ℂ)), MemH m v →
        ‖L k v - L₀ v‖ ≤ ε k * crConst d r m * sobNorm m v) ∧
      Tendsto (fun k => ε k * crConst d r m) atTop (𝓝 0) := by
  refine ⟨fun k v hv => ?_, by simpa using hε.mul_const (crConst d r m)⟩
  refine (hL k v).trans ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (crNorm_le hm hv) (hε0 k)

/-! ### Non-vacuity -/

/-- Non-vacuity of `H^m ⊂ C^r`: a monomial on `𝕋⁴` with `r = 2`, `m = 5 > 2 + 4/2`. -/
example (v : Fin 4 → ℤ) :
    ∃ D : (Fin 4 → ℕ) → C(UnitAddTorus (Fin 4), ℂ), D 0 = mFourier v ∧
      (∀ α i, mOrder α < 2 → IsLineDeriv i ⇑(D α) ⇑(D (α + Pi.single i 1))) ∧
      (∀ α, mOrder α ≤ 2 → ∀ n, mFourierCoeff (D α) n = symbol α n * mFourierCoeff (mFourier v) n) ∧
      (∀ α, mOrder α ≤ 2 → ‖D α‖ ≤ embConst (Fin 4) (5 - mOrder α) * sobNorm 5 (mFourier v)) ∧
      ∑ α ∈ multiIndices (Fin 4) 2, ‖D α‖ ≤ crConst (Fin 4) 2 5 * sobNorm 5 (mFourier v) :=
  exists_derivatives_of_memH (by norm_num) _ (memH_mFourier 5 v)

/-- Non-vacuity of the `C^r`-dual to `H^{-m}` comparison: the zero functional sequence. -/
example : (∀ k (v : C(UnitAddTorus (Fin 4), ℂ)), MemH 5 v →
        ‖(fun (_ : ℕ) (_ : C(UnitAddTorus (Fin 4), ℂ)) => (0 : ℂ)) k v - 0‖ ≤
          (fun _ : ℕ => (0 : ℝ)) k * crConst (Fin 4) 2 5 * sobNorm 5 v) ∧
      Tendsto (fun k => (fun _ : ℕ => (0 : ℝ)) k * crConst (Fin 4) 2 5) atTop (𝓝 0) :=
  dual_Cr_to_negSobolev (r := 2) (m := 5) (by norm_num) (fun _ _ => 0) (fun _ => 0)
    (fun _ => 0) (fun _ => le_rfl) tendsto_const_nhds (fun k v => by simp)

end

end RenewalGeometry.TorusSobolev
