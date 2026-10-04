/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.TorusSobolevDerivatives
import RenewalGeometry.Analysis.TorusSobolevL4

/-!
# Weak derivatives on `𝕋^d` and strong `L²` convergence of curvatures `dA + A ∧ A`

Generic infrastructure (no renewal notions) for the curvature step of `prop:sobolev-bosonic`
of the Einstein–Standard-Model action-closure manuscript: strong `H¹` convergence of gauge
potentials with uniform `L^∞` bounds gives strong `L²` convergence of `F_A = dA + A ∧ A`.

* `weakDeriv i f`: the weak partial derivative of `f ∈ L²(𝕋^d) ∩ H¹` as the Fourier multiplier
  `(∂ᵢ f)^(n) = 2πi nᵢ f̂(n)` (`mFourierCoeff_weakDeriv`), i.e. the distributional derivative
  tested against the monomials; it agrees with the classical derivative of a `C¹` function
  (`weakDeriv_toLp_eq`), and `‖∂ᵢ f - ∂ᵢ g‖_{L²} ≤ ‖f - g‖_{H¹}` (`norm_weakDeriv_sub_le`).
* `tendsto_eLpNorm_mul_of_bounded` (any measure space): `a_k → a`, `b_k → b` in `L^p` with
  `|a_k| ≤ K`, `|b| ≤ K` a.e. give `a_k b_k → a b` in `L^p` (bounded × strong).
* `curvature`, `tendsto_curvature` (matrix gauge potentials `A_μ^{ab}`):
  `F_{μν}^{ab} = ∂_μ A_ν^{ab} - ∂_ν A_μ^{ab} + Σ_c (A_μ^{ac} A_ν^{cb} - A_ν^{ac} A_μ^{cb})`
  converges in `L²` when `A_k → A` in `H¹` componentwise with a uniform `L^∞` bound.
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

local notation "L²(" α ")" => Lp ℂ 2 (volume : Measure α)

/-! ### Bounded × strong products in `L^p` (any measure space) -/

/-- **Bounded × strong convergence of products** (`prop:sobolev-bosonic`, the `A ∧ A` step):
if `a_k → a`, `b_k → b` in `L^p` (`p ≥ 1`), `|a_k| ≤ K` and `|b| ≤ K` a.e., then
`a_k b_k → a b` in `L^p`. -/
theorem tendsto_eLpNorm_mul_of_bounded {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {p : ℝ≥0∞} (hp : 1 ≤ p) {a b : ℕ → α → ℂ} {a₀ b₀ : α → ℂ}
    (ha : ∀ k, AEStronglyMeasurable (a k) μ) (hb : ∀ k, AEStronglyMeasurable (b k) μ)
    (ha₀ : AEStronglyMeasurable a₀ μ) (hb₀ : AEStronglyMeasurable b₀ μ) {K : ℝ}
    (hK : ∀ k, ∀ᵐ x ∂μ, ‖a k x‖ ≤ K) (hK₀ : ∀ᵐ x ∂μ, ‖b₀ x‖ ≤ K)
    (hac : Tendsto (fun k => eLpNorm (a k - a₀) p μ) atTop (𝓝 0))
    (hbc : Tendsto (fun k => eLpNorm (b k - b₀) p μ) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm (a k * b k - a₀ * b₀) p μ) atTop (𝓝 0) := by
  have hsplit : ∀ k, a k * b k - a₀ * b₀ = a k * (b k - b₀) + (a k - a₀) * b₀ := by
    intro k; ring
  have hle : ∀ k, eLpNorm (a k * b k - a₀ * b₀) p μ ≤
      ENNReal.ofReal K * eLpNorm (b k - b₀) p μ + ENNReal.ofReal K * eLpNorm (a k - a₀) p μ := by
    intro k
    rw [hsplit]
    refine (eLpNorm_add_le ((ha k).mul ((hb k).sub hb₀)) (((ha k).sub ha₀).mul hb₀) hp).trans ?_
    gcongr
    · refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul ?_ p
      filter_upwards [hK k] with x hx
      simp only [Pi.mul_apply, norm_mul]
      exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
    · refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul ?_ p
      filter_upwards [hK₀] with x hx
      simp only [Pi.mul_apply, norm_mul]
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
  have hlim : Tendsto (fun k => ENNReal.ofReal K * eLpNorm (b k - b₀) p μ +
      ENNReal.ofReal K * eLpNorm (a k - a₀) p μ) atTop (𝓝 0) := by
    have h1 := ENNReal.Tendsto.const_mul hbc (Or.inr (ENNReal.ofReal_ne_top (r := K)))
    have h2 := ENNReal.Tendsto.const_mul hac (Or.inr (ENNReal.ofReal_ne_top (r := K)))
    simpa using h1.add h2
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun k => zero_le)
    hle

/-! ### Weak derivatives as Fourier multipliers -/

variable {d : Type*} [Fintype d] [DecidableEq d]

theorem memℓp_dCoeff {f : UnitAddTorus d → ℂ} (hf : MemH 1 f) (i : d) :
    Memℓp (dCoeff i (mFourierCoeff f)) 2 := by
  have h := (coeffMemH_dCoeff hf i).1
  rw [sub_self, coeffMemH_zero_iff] at h
  refine memℓp_gen ?_
  simpa using h

open Classical in
/-- **The weak partial derivative on `𝕋^d`** of an `L²` function with finite `H¹` norm, as the
Fourier multiplier `2πi nᵢ` (it is `0` outside `H¹`).  Its Fourier coefficients
(`mFourierCoeff_weakDeriv`) are those of the distributional derivative tested against the
monomials, `⟨∂ᵢ f, e_n⟩ = -⟨f, ∂ᵢ e_n⟩`. -/
def weakDeriv (i : d) (f : L²(UnitAddTorus d)) : L²(UnitAddTorus d) :=
  if h : MemH 1 f then mFourierBasis.repr.symm ⟨dCoeff i (mFourierCoeff f), memℓp_dCoeff h i⟩
  else 0

theorem mFourierCoeff_weakDeriv {i : d} {f : L²(UnitAddTorus d)} (hf : MemH 1 f) (n : d → ℤ) :
    mFourierCoeff (weakDeriv i f) n = (2 * π * Complex.I * n i) * mFourierCoeff f n := by
  rw [← mFourierBasis_repr, weakDeriv, dif_pos hf]
  simp [dCoeff]

/-- **Weak = classical derivative** for `C¹` functions in `H^s`, `s > d/2 + 1`: the weak derivative
of `F` is (the `L²` class of) its classical partial derivative. -/
theorem weakDeriv_toLp_eq {s : ℝ} (hs : (Fintype.card d : ℝ) / 2 + 1 < s)
    (F : C(UnitAddTorus d, ℂ)) (hF : MemH s F) (i : d) :
    ∃ F' : C(UnitAddTorus d, ℂ), IsLineDeriv i ⇑F ⇑F' ∧
      weakDeriv i (F.toLp 2 volume ℂ) = F'.toLp 2 volume ℂ := by
  obtain ⟨F', hF', hc, -⟩ := memH_isLineDeriv hs F hF i
  refine ⟨F', hF', ?_⟩
  have hF1 : MemH 1 ⇑(F.toLp 2 volume ℂ) := by
    have h1 : MemH 1 ⇑F := hF.mono (by
      have : (0 : ℝ) ≤ (Fintype.card d : ℝ) / 2 := by positivity
      linarith)
    unfold MemH CoeffMemH at h1 ⊢
    simp_rw [mFourierCoeff_toLp]
    exact h1
  apply mFourierBasis.repr.injective
  ext n
  rw [mFourierBasis_repr, mFourierBasis_repr, mFourierCoeff_weakDeriv hF1, mFourierCoeff_toLp,
    mFourierCoeff_toLp, hc]

/-- **`‖∂ᵢ f - ∂ᵢ g‖_{L²} ≤ ‖f - g‖_{H¹}`**: the weak derivative is continuous `H¹ → L²`. -/
theorem norm_weakDeriv_sub_le {i : d} {f g : L²(UnitAddTorus d)} (hf : MemH 1 f)
    (hg : MemH 1 g) : ‖weakDeriv i f - weakDeriv i g‖ ≤ sobNorm 1 ⇑(f - g) := by
  have hfg := memH_Lp_sub hf hg
  rw [← sobNorm_zero_eq_norm]
  have hcoef : mFourierCoeff ⇑(weakDeriv i f - weakDeriv i g) =
      dCoeff i (mFourierCoeff ⇑(f - g)) := by
    funext n
    rw [mFourierCoeff_Lp_sub, mFourierCoeff_weakDeriv hf, mFourierCoeff_weakDeriv hg]
    simp only [dCoeff]
    rw [mFourierCoeff_Lp_sub]
    ring
  unfold sobNorm sobSq
  rw [hcoef]
  have h := (coeffMemH_dCoeff hfg i).2
  rw [sub_self] at h
  exact Real.sqrt_le_sqrt h

/-- `L²` distance of `L²` classes as an `eLpNorm` of representatives. -/
theorem eLpNorm_coe_sub_eq (f g : L²(UnitAddTorus d)) :
    eLpNorm (⇑f - ⇑g) 2 volume = ENNReal.ofReal ‖f - g‖ := by
  rw [← Lp.edist_def, Lp.edist_dist, dist_eq_norm]

/-- Strong `H¹` convergence gives strong `L²` convergence of every weak derivative. -/
theorem tendsto_weakDeriv {i : d} {f : ℕ → L²(UnitAddTorus d)} {f₀ : L²(UnitAddTorus d)}
    (hf : ∀ k, MemH 1 (f k)) (hf₀ : MemH 1 f₀)
    (hconv : Tendsto (fun k => sobSq 1 ⇑(f k - f₀)) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm (⇑(weakDeriv i (f k)) - ⇑(weakDeriv i f₀)) 2 volume) atTop
      (𝓝 0) := by
  simp_rw [eLpNorm_coe_sub_eq]
  have h := ENNReal.tendsto_ofReal ((Real.continuous_sqrt.tendsto 0).comp hconv)
  simp only [Real.sqrt_zero, ENNReal.ofReal_zero] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun k => zero_le)
    (fun k => ENNReal.ofReal_le_ofReal ?_)
  exact norm_weakDeriv_sub_le (hf k) hf₀

/-- Strong `H¹` convergence gives strong `L²` convergence. -/
theorem tendsto_eLpNorm_of_H1 {f : ℕ → L²(UnitAddTorus d)} {f₀ : L²(UnitAddTorus d)}
    (hf : ∀ k, MemH 1 (f k)) (hf₀ : MemH 1 f₀)
    (hconv : Tendsto (fun k => sobSq 1 ⇑(f k - f₀)) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm (⇑(f k) - ⇑f₀) 2 volume) atTop (𝓝 0) := by
  simp_rw [eLpNorm_coe_sub_eq]
  have h := ENNReal.tendsto_ofReal ((Real.continuous_sqrt.tendsto 0).comp hconv)
  simp only [Real.sqrt_zero, ENNReal.ofReal_zero] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun k => zero_le)
    (fun k => ENNReal.ofReal_le_ofReal ?_)
  rw [← sobNorm_zero_eq_norm]
  exact sobNorm_mono zero_le_one (memH_Lp_sub (hf k) hf₀)

/-! ### Curvature `dA + A ∧ A` of matrix-valued gauge potentials -/

variable {r : Type*} [Fintype r]

/-- The curvature components of a matrix-valued (`r × r`) gauge potential `A_μ^{ab} ∈ L²(𝕋^d)`:
`F_{μν}^{ab} = ∂_μ A_ν^{ab} - ∂_ν A_μ^{ab} + Σ_c (A_μ^{ac} A_ν^{cb} - A_ν^{ac} A_μ^{cb})`
(`F_A = dA + A ∧ A`, weak derivatives), as an a.e.-defined function. -/
def curvature (A : d → r → r → L²(UnitAddTorus d)) (μ ν : d) (a b : r) :
    UnitAddTorus d → ℂ :=
  (⇑(weakDeriv μ (A ν a b)) - ⇑(weakDeriv ν (A μ a b))) +
    ∑ c, (⇑(A μ a c) * ⇑(A ν c b) - ⇑(A ν a c) * ⇑(A μ c b))

/-- Curvature convergence from its pieces: `H¹` convergence of the components (for `dA`) and
`L²` convergence of all products `A_μ^{ac} A_ν^{cb}` (for `A ∧ A`). -/
theorem tendsto_curvature_of_pieces {A : ℕ → d → r → r → L²(UnitAddTorus d)}
    {A₀ : d → r → r → L²(UnitAddTorus d)} (hA : ∀ k μ a b, MemH 1 (A k μ a b))
    (hA₀ : ∀ μ a b, MemH 1 (A₀ μ a b))
    (hconv : ∀ μ a b, Tendsto (fun k => sobSq 1 ⇑(A k μ a b - A₀ μ a b)) atTop (𝓝 0))
    (hprod : ∀ μ ν a c b, Tendsto (fun k => eLpNorm (⇑(A k μ a c) * ⇑(A k ν c b) -
      ⇑(A₀ μ a c) * ⇑(A₀ ν c b)) 2 volume) atTop (𝓝 0)) (μ ν : d) (a b : r) :
    Tendsto (fun k => eLpNorm (curvature (A k) μ ν a b - curvature A₀ μ ν a b) 2 volume) atTop
      (𝓝 0) := by
  -- decomposition of the difference into finitely many pieces
  set P : ℕ → Option (Option r) → UnitAddTorus d → ℂ := fun k j =>
    match j with
    | none => ⇑(weakDeriv μ (A k ν a b)) - ⇑(weakDeriv μ (A₀ ν a b))
    | some none => -(⇑(weakDeriv ν (A k μ a b)) - ⇑(weakDeriv ν (A₀ μ a b)))
    | some (some c) => (⇑(A k μ a c) * ⇑(A k ν c b) - ⇑(A₀ μ a c) * ⇑(A₀ ν c b)) -
        (⇑(A k ν a c) * ⇑(A k μ c b) - ⇑(A₀ ν a c) * ⇑(A₀ μ c b))
  have hdecomp : ∀ k, curvature (A k) μ ν a b - curvature A₀ μ ν a b = ∑ j, P k j := by
    intro k
    rw [Fintype.sum_option, Fintype.sum_option]
    have hs : ∑ c, P k (some (some c)) =
        (∑ c, (⇑(A k μ a c) * ⇑(A k ν c b) - ⇑(A k ν a c) * ⇑(A k μ c b))) -
          ∑ c, (⇑(A₀ μ a c) * ⇑(A₀ ν c b) - ⇑(A₀ ν a c) * ⇑(A₀ μ c b)) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      simp only [P]
      ring
    rw [hs]
    simp only [P, curvature]
    ring
  have hmeas : ∀ k j, AEStronglyMeasurable (P k j) volume := by
    intro k j
    rcases j with _ | _ | c
    · exact (Lp.aestronglyMeasurable _).sub (Lp.aestronglyMeasurable _)
    · exact ((Lp.aestronglyMeasurable _).sub (Lp.aestronglyMeasurable _)).neg
    · exact (((Lp.aestronglyMeasurable _).mul (Lp.aestronglyMeasurable _)).sub
        ((Lp.aestronglyMeasurable _).mul (Lp.aestronglyMeasurable _))).sub
        (((Lp.aestronglyMeasurable _).mul (Lp.aestronglyMeasurable _)).sub
        ((Lp.aestronglyMeasurable _).mul (Lp.aestronglyMeasurable _)))
  have hpiece : ∀ j, Tendsto (fun k => eLpNorm (P k j) 2 volume) atTop (𝓝 0) := by
    intro j
    rcases j with _ | _ | c
    · exact tendsto_weakDeriv (fun k => hA k ν a b) (hA₀ ν a b) (hconv ν a b)
    · simp only [P, eLpNorm_neg]
      exact tendsto_weakDeriv (fun k => hA k μ a b) (hA₀ μ a b) (hconv μ a b)
    · have h1 := hprod μ ν a c b
      have h2 := hprod ν μ a c b
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (by simpa using h1.add h2)
        (fun k => zero_le) (fun k => ?_)
      exact eLpNorm_sub_le (((Lp.aestronglyMeasurable _).mul (Lp.aestronglyMeasurable _)).sub
        ((Lp.aestronglyMeasurable _).mul (Lp.aestronglyMeasurable _)))
        (((Lp.aestronglyMeasurable _).mul (Lp.aestronglyMeasurable _)).sub
        ((Lp.aestronglyMeasurable _).mul (Lp.aestronglyMeasurable _))) (by norm_num)
  simp_rw [hdecomp]
  have hsum : Tendsto (fun k => ∑ j, eLpNorm (P k j) 2 volume) atTop (𝓝 0) := by
    simpa using tendsto_finset_sum (Finset.univ : Finset (Option (Option r)))
      fun j _ => hpiece j
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun k => zero_le)
    (fun k => eLpNorm_sum_le (fun j _ => hmeas k j) (by norm_num))

/-- **Strong `L²` convergence of curvatures, bounded potentials** (`prop:sobolev-bosonic`, the
step `dA_h → dA`, `A_h ∧ A_h → A ∧ A` in `L²`, torus form): if every component of the matrix gauge
potentials converges strongly in `H¹(𝕋^d)` and the potentials are uniformly bounded a.e.
(e.g. from an `H^{2+σ}(𝕋⁴)` bound via `exists_continuous_of_memH`), then `F_{A_k} → F_A` in
`L²`. -/
theorem tendsto_curvature {A : ℕ → d → r → r → L²(UnitAddTorus d)}
    {A₀ : d → r → r → L²(UnitAddTorus d)} (hA : ∀ k μ a b, MemH 1 (A k μ a b))
    (hA₀ : ∀ μ a b, MemH 1 (A₀ μ a b))
    (hconv : ∀ μ a b, Tendsto (fun k => sobSq 1 ⇑(A k μ a b - A₀ μ a b)) atTop (𝓝 0))
    {K : ℝ} (hK : ∀ k μ a b, ∀ᵐ x ∂volume, ‖A k μ a b x‖ ≤ K)
    (hK₀ : ∀ μ a b, ∀ᵐ x ∂volume, ‖A₀ μ a b x‖ ≤ K) (μ ν : d) (a b : r) :
    Tendsto (fun k => eLpNorm (curvature (A k) μ ν a b - curvature A₀ μ ν a b) 2 volume) atTop
      (𝓝 0) := by
  have hL2 : ∀ μ a b, Tendsto (fun k => eLpNorm (⇑(A k μ a b) - ⇑(A₀ μ a b)) 2 volume) atTop
      (𝓝 0) := fun μ a b => tendsto_eLpNorm_of_H1 (fun k => hA k μ a b) (hA₀ μ a b) (hconv μ a b)
  exact tendsto_curvature_of_pieces hA hA₀ hconv (fun μ ν a c b =>
    tendsto_eLpNorm_mul_of_bounded (by norm_num) (fun k => Lp.aestronglyMeasurable _)
      (fun k => Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
      (Lp.aestronglyMeasurable _) (fun k => hK k μ a c) (hK₀ ν c b) (hL2 μ a c) (hL2 ν c b))
    μ ν a b

/-- Non-vacuity of `tendsto_curvature`: the hypotheses hold for a constant `2 × 2` potential whose
components are the `L²` class of a monomial on `𝕋⁴`. -/
example (m : Fin 4 → ℤ) (μ ν : Fin 4) (a b : Fin 2) :
    Tendsto (fun _ : ℕ => eLpNorm
      (curvature (fun _ _ _ => (mFourier m).toLp 2 volume ℂ) μ ν a b -
        curvature (fun _ _ _ => (mFourier m).toLp 2 volume ℂ) μ ν a b) 2 volume) atTop (𝓝 0) := by
  have hmem : MemH 1 ⇑((mFourier m).toLp 2 volume ℂ) := by
    have := memH_mFourier (d := Fin 4) 1 m
    unfold MemH CoeffMemH at this ⊢
    simp_rw [mFourierCoeff_toLp]
    exact this
  have hzero : sobSq 1 ⇑((mFourier m).toLp 2 volume ℂ - (mFourier m).toLp 2 volume ℂ) = 0 := by
    unfold sobSq coeffSobSq
    simp_rw [mFourierCoeff_Lp_sub, sub_self]
    simp
  have hb : ∀ᵐ x ∂volume, ‖((mFourier m).toLp 2 volume ℂ) x‖ ≤ 1 := by
    filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (μ := volume) (𝕜 := ℂ) (mFourier m)]
      with x hx
    rw [hx, norm_mFourier_apply]
  exact tendsto_curvature (A := fun _ _ _ _ => (mFourier m).toLp 2 volume ℂ)
    (fun _ _ _ _ => hmem) (fun _ _ _ => hmem)
    (fun _ _ _ => by simp only [hzero]; exact tendsto_const_nhds) (fun _ _ _ _ => hb)
    (fun _ _ _ => hb) μ ν a b

/-! ### `L⁴ × L⁴ → L²` products and the `H^{1+σ}` curvature step -/

theorem holderTriple_four_four_two : ENNReal.HolderTriple 4 4 2 := by
  refine ⟨?_⟩
  rw [← two_mul, show (4 : ℝ≥0∞) = 2 * 2 by norm_num, ENNReal.mul_inv (by simp) (by simp),
    ← mul_assoc, ENNReal.mul_inv_cancel (by simp) (by simp), one_mul]

/-- Hölder `L⁴ × L⁴ → L²`. -/
theorem eLpNorm_mul_le_four {α : Type*} [MeasurableSpace α] {μ : Measure α} {a b : α → ℂ}
    (ha : AEStronglyMeasurable a μ) (hb : AEStronglyMeasurable b μ) :
    eLpNorm (a * b) 2 μ ≤ eLpNorm a 4 μ * eLpNorm b 4 μ := by
  have := holderTriple_four_four_two
  have h := eLpNorm_smul_le_mul_eLpNorm (p := 4) (q := 4) (r := 2) hb ha
  have e : a • b = a * b := by funext x; simp [smul_eq_mul]
  rwa [e] at h

/-- **Strong `L⁴` convergence of factors gives strong `L²` convergence of products**
(`prop:sobolev-bosonic`: `A_h ∧ A_h → A ∧ A` and `ρ(A_h) H_h → ρ(A) H` in `L²`). -/
theorem tendsto_eLpNorm_mul_of_L4 {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {a b : ℕ → α → ℂ} {a₀ b₀ : α → ℂ}
    (ha : ∀ k, AEStronglyMeasurable (a k) μ) (hb : ∀ k, AEStronglyMeasurable (b k) μ)
    (ha₀ : MemLp a₀ 4 μ) (hb₀ : MemLp b₀ 4 μ)
    (hac : Tendsto (fun k => eLpNorm (a k - a₀) 4 μ) atTop (𝓝 0))
    (hbc : Tendsto (fun k => eLpNorm (b k - b₀) 4 μ) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm (a k * b k - a₀ * b₀) 2 μ) atTop (𝓝 0) := by
  have hsplit : ∀ k, a k * b k - a₀ * b₀ = a k * (b k - b₀) + (a k - a₀) * b₀ := by
    intro k; ring
  have hak : ∀ k, eLpNorm (a k) 4 μ ≤ eLpNorm (a k - a₀) 4 μ + eLpNorm a₀ 4 μ := by
    intro k
    have e : a k = (a k - a₀) + a₀ := by ring
    calc eLpNorm (a k) 4 μ = eLpNorm ((a k - a₀) + a₀) 4 μ := by rw [← e]
      _ ≤ _ := eLpNorm_add_le ((ha k).sub ha₀.1) ha₀.1 (by norm_num)
  have hle : ∀ k, eLpNorm (a k * b k - a₀ * b₀) 2 μ ≤
      (eLpNorm (a k - a₀) 4 μ + eLpNorm a₀ 4 μ) * eLpNorm (b k - b₀) 4 μ +
        eLpNorm (a k - a₀) 4 μ * eLpNorm b₀ 4 μ := by
    intro k
    rw [hsplit]
    refine (eLpNorm_add_le ((ha k).mul ((hb k).sub hb₀.1)) (((ha k).sub ha₀.1).mul hb₀.1)
      (by norm_num)).trans ?_
    gcongr
    · exact (eLpNorm_mul_le_four (ha k) ((hb k).sub hb₀.1)).trans (by gcongr; exact hak k)
    · exact eLpNorm_mul_le_four ((ha k).sub ha₀.1) hb₀.1
  have h1 : Tendsto (fun k => (eLpNorm (a k - a₀) 4 μ + eLpNorm a₀ 4 μ) *
      eLpNorm (b k - b₀) 4 μ) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.mul (hac.add tendsto_const_nhds)
      (Or.inr (by simp)) hbc (Or.inr (by simpa using ha₀.eLpNorm_ne_top))
    simpa using this
  have h2 : Tendsto (fun k => eLpNorm (a k - a₀) 4 μ * eLpNorm b₀ 4 μ) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.mul_const hac (Or.inr hb₀.eLpNorm_ne_top)
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (by simpa using h1.add h2)
    (fun k => zero_le) hle

/-- **Strong `L²` convergence of curvatures under `H^s` convergence, `s ≥ 1`, `s > d/4`**
(`prop:sobolev-bosonic`, torus form, without any `L^∞` bound: on `𝕋⁴` an `H^{1+σ}` convergence
of the potentials suffices, through `H^s ⊂ L⁴`). -/
theorem tendsto_curvature_of_H {s : ℝ} (hs1 : 1 ≤ s) (hs : (Fintype.card d : ℝ) / 4 < s)
    {A : ℕ → d → r → r → L²(UnitAddTorus d)} {A₀ : d → r → r → L²(UnitAddTorus d)}
    (hA : ∀ k μ a b, MemH s (A k μ a b)) (hA₀ : ∀ μ a b, MemH s (A₀ μ a b))
    (hconv : ∀ μ a b, Tendsto (fun k => sobSq s ⇑(A k μ a b - A₀ μ a b)) atTop (𝓝 0))
    (μ ν : d) (a b : r) :
    Tendsto (fun k => eLpNorm (curvature (A k) μ ν a b - curvature A₀ μ ν a b) 2 volume) atTop
      (𝓝 0) := by
  have hconv1 : ∀ μ a b, Tendsto (fun k => sobSq 1 ⇑(A k μ a b - A₀ μ a b)) atTop (𝓝 0) :=
    fun μ a b => squeeze_zero (fun k => sobSq_nonneg _ _)
      (fun k => coeffSobSq_mono hs1 (memH_Lp_sub (hA k μ a b) (hA₀ μ a b))) (hconv μ a b)
  have hL4 : ∀ μ a b, Tendsto (fun k => eLpNorm (⇑(A k μ a b) - ⇑(A₀ μ a b)) 4 volume) atTop
      (𝓝 0) := fun μ a b =>
    tendsto_eLpNorm_four_of_H hs (fun k => hA k μ a b) (hA₀ μ a b) (hconv μ a b)
  exact tendsto_curvature_of_pieces (fun k μ a b => (hA k μ a b).mono hs1)
    (fun μ a b => (hA₀ μ a b).mono hs1) hconv1 (fun μ ν a c b =>
      tendsto_eLpNorm_mul_of_L4 (fun k => Lp.aestronglyMeasurable _)
        (fun k => Lp.aestronglyMeasurable _) (memLp_four_of_memH hs _ (hA₀ μ a c))
        (memLp_four_of_memH hs _ (hA₀ ν c b)) (hL4 μ a c) (hL4 ν c b)) μ ν a b

/-! ### Covariant derivatives `D_A H = dH + ρ(A) H` -/

variable {r' : Type*} [Fintype r']

/-- The covariant derivative of a Higgs field `H^a ∈ L²(𝕋^d)` (`a ∈ r'`) for a gauge potential
`A_μ^{cc'}` and a representation given by the fixed coefficients `R`:
`(D_μ H)^a = ∂_μ H^a + Σ_{b,c,c'} R^{ab}_{cc'} A_μ^{cc'} H^b`. -/
def covDeriv (R : r' → r' → r → r → ℂ) (A : d → r → r → L²(UnitAddTorus d))
    (H : r' → L²(UnitAddTorus d)) (μ : d) (a : r') : UnitAddTorus d → ℂ :=
  ⇑(weakDeriv μ (H a)) + ∑ q : r' × r × r, R a q.1 q.2.1 q.2.2 • (⇑(A μ q.2.1 q.2.2) * ⇑(H q.1))

/-- **Strong `L²` convergence of `D_{A_h} H_h`** (`prop:sobolev-bosonic`, torus form): `H^s`
convergence (`s ≥ 1`, `s > d/4`) of the potentials and of the Higgs components gives
`D_{A_k} H_k → D_A H` in `L²`. -/
theorem tendsto_covDeriv_of_H {s : ℝ} (hs1 : 1 ≤ s) (hs : (Fintype.card d : ℝ) / 4 < s)
    (R : r' → r' → r → r → ℂ)
    {A : ℕ → d → r → r → L²(UnitAddTorus d)} {A₀ : d → r → r → L²(UnitAddTorus d)}
    {H : ℕ → r' → L²(UnitAddTorus d)} {H₀ : r' → L²(UnitAddTorus d)}
    (hA : ∀ k μ a b, MemH s (A k μ a b)) (hA₀ : ∀ μ a b, MemH s (A₀ μ a b))
    (hH : ∀ k a, MemH s (H k a)) (hH₀ : ∀ a, MemH s (H₀ a))
    (hconvA : ∀ μ a b, Tendsto (fun k => sobSq s ⇑(A k μ a b - A₀ μ a b)) atTop (𝓝 0))
    (hconvH : ∀ a, Tendsto (fun k => sobSq s ⇑(H k a - H₀ a)) atTop (𝓝 0)) (μ : d) (a : r') :
    Tendsto (fun k => eLpNorm (covDeriv R (A k) (H k) μ a - covDeriv R A₀ H₀ μ a) 2 volume)
      atTop (𝓝 0) := by
  set P : ℕ → Option (r' × r × r) → UnitAddTorus d → ℂ := fun k j =>
    match j with
    | none => ⇑(weakDeriv μ (H k a)) - ⇑(weakDeriv μ (H₀ a))
    | some q => R a q.1 q.2.1 q.2.2 • (⇑(A k μ q.2.1 q.2.2) * ⇑(H k q.1) -
        ⇑(A₀ μ q.2.1 q.2.2) * ⇑(H₀ q.1))
  have hdecomp : ∀ k, covDeriv R (A k) (H k) μ a - covDeriv R A₀ H₀ μ a = ∑ j, P k j := by
    intro k
    rw [Fintype.sum_option]
    have hs' : ∑ q, P k (some q) =
        (∑ q : r' × r × r, R a q.1 q.2.1 q.2.2 • (⇑(A k μ q.2.1 q.2.2) * ⇑(H k q.1))) -
          ∑ q : r' × r × r, R a q.1 q.2.1 q.2.2 • (⇑(A₀ μ q.2.1 q.2.2) * ⇑(H₀ q.1)) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun q _ => ?_
      simp only [P, smul_sub]
    rw [hs']
    simp only [P, covDeriv]
    abel
  have hmeas : ∀ k j, AEStronglyMeasurable (P k j) volume := by
    intro k j
    rcases j with _ | q
    · exact (Lp.aestronglyMeasurable _).sub (Lp.aestronglyMeasurable _)
    · exact (((Lp.aestronglyMeasurable _).mul (Lp.aestronglyMeasurable _)).sub
        ((Lp.aestronglyMeasurable _).mul (Lp.aestronglyMeasurable _))).const_smul _
  have hconvH1 : Tendsto (fun k => sobSq 1 ⇑(H k a - H₀ a)) atTop (𝓝 0) :=
    squeeze_zero (fun k => sobSq_nonneg _ _)
      (fun k => coeffSobSq_mono hs1 (memH_Lp_sub (hH k a) (hH₀ a))) (hconvH a)
  have hpiece : ∀ j, Tendsto (fun k => eLpNorm (P k j) 2 volume) atTop (𝓝 0) := by
    intro j
    rcases j with _ | q
    · exact tendsto_weakDeriv (fun k => (hH k a).mono hs1) ((hH₀ a).mono hs1) hconvH1
    · have hprod := tendsto_eLpNorm_mul_of_L4 (μ := volume)
        (a := fun k => ⇑(A k μ q.2.1 q.2.2)) (b := fun k => ⇑(H k q.1))
        (fun k => Lp.aestronglyMeasurable _) (fun k => Lp.aestronglyMeasurable _)
        (memLp_four_of_memH hs _ (hA₀ μ q.2.1 q.2.2)) (memLp_four_of_memH hs _ (hH₀ q.1))
        (tendsto_eLpNorm_four_of_H hs (fun k => hA k μ q.2.1 q.2.2) (hA₀ μ q.2.1 q.2.2)
          (hconvA μ q.2.1 q.2.2))
        (tendsto_eLpNorm_four_of_H hs (fun k => hH k q.1) (hH₀ q.1) (hconvH q.1))
      simp only [P]
      simp_rw [eLpNorm_const_smul]
      have := ENNReal.Tendsto.const_mul hprod (Or.inr (enorm_ne_top (x := R a q.1 q.2.1 q.2.2)))
      simpa using this
  simp_rw [hdecomp]
  have hsum : Tendsto (fun k => ∑ j, eLpNorm (P k j) 2 volume) atTop (𝓝 0) := by
    simpa using tendsto_finset_sum (Finset.univ : Finset (Option (r' × r × r)))
      fun j _ => hpiece j
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum (fun k => zero_le)
    (fun k => eLpNorm_sum_le (fun j _ => hmeas k j) (by norm_num))

end

end RenewalGeometry.TorusSobolev
