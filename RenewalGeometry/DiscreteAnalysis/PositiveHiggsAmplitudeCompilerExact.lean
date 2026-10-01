/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# A positive amplitude–energy compiler
  (`cor:positive-Higgs-amplitude-criterion`, with the pointwise part of
  `prop:positive-Higgs-envelope`, Einstein–SM action closure)

Setting (`app:positive-Higgs-envelope`).  For each cutoff `h : ι` the chart is
a finite set of cells `Cell h`; the directions form a finite type `D`
(`D = Fin 4`); the covariant Higgs edge packet is `K h x : D → F` with values
in a real inner product space `F` (the Higgs fibre with the real part of its
Hermitian inner product); `r h x μ ν` is the sampled positive one-form metric
and `m h x ≥ 0` the cell mass.

* `positiveHiggsDensity` — `e_h^{H,+}(x) = r^{μν} Re⟨K_μ, K_ν⟩`
  (`eq:positive-Higgs-density`);
* `positiveHiggsAmpSq` — `|K_h^H(x)|² = Σ_μ ‖K_μ(x)‖²`;
* `positiveHiggsLpNorm` — `‖f‖_{L_h^p} = (Σ_x m_h(x) |f(x)|^p)^{1/p}`
  (`eq:positive-discrete-Lp`).

Results:

* `positiveHiggs_envelope` — pointwise part of `prop:positive-Higgs-envelope`
  (`eq:positive-Higgs-envelope`) with `c_0 = c_r`, `C_0 = C_r`, directly from the
  comparison `eq:positive-Higgs-Hodge-comparison`;
* `positiveHiggs_L43_interpolation` — `Σ m e^{4/3} ≤ ‖e‖_∞^{1/3} Σ m e` for
  `0 ≤ e ≤ B`;
* `positiveHiggs_L83_le_L43` — `Σ m |K|^{8/3} ≤ c_r^{-4/3} Σ m e^{4/3}`;
* `positiveHiggs_amplitude_criterion` — `cor:positive-Higgs-amplitude-criterion`:
  uniform `L¹_h` and `L^∞_h` bounds on `e_h^{H,+}` give uniform
  `L_h^{4/3}` bounds on `e_h^{H,+}` and `L_h^{8/3}` bounds on `K_h^H`.

Scoped hypotheses: only the lower comparison constant `c_r > 0` of
`eq:positive-Higgs-Hodge-comparison` is used, and only `m_h ≥ 0` of the mass
comparison.  The `L^∞_h` norm is the maximum over cells (this equals the
mass-weighted essential supremum since the masses are positive).  The
sentence of the corollary about microscopic mechanisms is interpretive and
has no formal content.
-/

namespace RenewalGeometry

open Finset

noncomputable section

section PositiveHiggs

variable {D : Type*} [Fintype D]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The cellwise positive Higgs density `e_h^{H,+} = r^{μν} Re⟨K_μ, K_ν⟩`
(`eq:positive-Higgs-density`). -/
def positiveHiggsDensity (r : D → D → ℝ) (K : D → F) : ℝ :=
  ∑ μ, ∑ ν, r μ ν * inner ℝ (K μ) (K ν)

/-- The squared packet amplitude `|K|² = Σ_μ ‖K_μ‖²`. -/
def positiveHiggsAmpSq (K : D → F) : ℝ :=
  ∑ μ, ‖K μ‖ ^ 2

theorem positiveHiggsAmpSq_nonneg (K : D → F) : 0 ≤ positiveHiggsAmpSq K :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- `prop:positive-Higgs-envelope`, pointwise envelope `eq:positive-Higgs-envelope`:
the comparison `c_r |ξ|² ≤ r^{μν} Re⟨ξ_μ, ξ_ν⟩ ≤ C_r |ξ|²` evaluated at the packet
gives `c_0 |K|² ≤ e^{H,+} ≤ C_0 |K|²` with `c_0 = c_r`, `C_0 = C_r`. -/
theorem positiveHiggs_envelope (r : D → D → ℝ) (cr Cr : ℝ)
    (hcomp : ∀ ξ : D → F, cr * positiveHiggsAmpSq ξ ≤ positiveHiggsDensity r ξ ∧
      positiveHiggsDensity r ξ ≤ Cr * positiveHiggsAmpSq ξ) (K : D → F) :
    cr * positiveHiggsAmpSq K ≤ positiveHiggsDensity r K ∧
      positiveHiggsDensity r K ≤ Cr * positiveHiggsAmpSq K :=
  hcomp K

variable {C : Type*} [Fintype C]

/-- Discrete positive norm `‖f‖_{L_h^p} = (Σ_x m(x) |f(x)|^p)^{1/p}`
(`eq:positive-discrete-Lp`). -/
def positiveHiggsLpNorm (m : C → ℝ) (p : ℝ) (f : C → ℝ) : ℝ :=
  (∑ x, m x * |f x| ^ p) ^ (1 / p)

/-- Interpolation step of `cor:positive-Higgs-amplitude-criterion`:
for `0 ≤ e ≤ B` and nonnegative masses, `Σ m e^{4/3} ≤ B^{1/3} Σ m e`. -/
theorem positiveHiggs_L43_interpolation (m e : C → ℝ) (B : ℝ) (hm : ∀ x, 0 ≤ m x)
    (he : ∀ x, 0 ≤ e x) (heB : ∀ x, e x ≤ B) :
    ∑ x, m x * e x ^ (4 / 3 : ℝ) ≤ B ^ (1 / 3 : ℝ) * ∑ x, m x * e x := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun x _ => ?_
  have hsplit : e x ^ (4 / 3 : ℝ) = e x ^ (1 / 3 : ℝ) * e x := by
    rw [show (4 / 3 : ℝ) = 1 / 3 + 1 by norm_num, Real.rpow_add' (he x) (by norm_num),
      Real.rpow_one]
  have hpow : e x ^ (1 / 3 : ℝ) ≤ B ^ (1 / 3 : ℝ) :=
    Real.rpow_le_rpow (he x) (heB x) (by norm_num)
  rw [hsplit]
  have := mul_le_mul_of_nonneg_right hpow (mul_nonneg (hm x) (he x))
  nlinarith [this]

/-- `|K|^{8/3} = (|K|²)^{4/3}` with `|K| = √(Σ_μ ‖K_μ‖²)`. -/
theorem positiveHiggs_amp_rpow (Q : ℝ) (hQ : 0 ≤ Q) :
    Real.sqrt Q ^ (8 / 3 : ℝ) = Q ^ (4 / 3 : ℝ) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hQ]
  norm_num

/-- Envelope step of `cor:positive-Higgs-amplitude-criterion`
(`prop:positive-Higgs-envelope`): if `c |K(x)|² ≤ e(x)` with `c > 0`, then
`Σ m |K|^{8/3} ≤ c^{-4/3} Σ m e^{4/3}`. -/
theorem positiveHiggs_L83_le_L43 (m e Q : C → ℝ) (c : ℝ) (hc : 0 < c) (hm : ∀ x, 0 ≤ m x)
    (hQ : ∀ x, 0 ≤ Q x) (henv : ∀ x, c * Q x ≤ e x) :
    ∑ x, m x * Real.sqrt (Q x) ^ (8 / 3 : ℝ) ≤
      (c ^ (4 / 3 : ℝ))⁻¹ * ∑ x, m x * e x ^ (4 / 3 : ℝ) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun x _ => ?_
  rw [positiveHiggs_amp_rpow _ (hQ x)]
  have hQe : Q x ≤ e x / c := by rw [le_div_iff₀ hc]; linarith [henv x]
  have hpow : Q x ^ (4 / 3 : ℝ) ≤ (e x / c) ^ (4 / 3 : ℝ) :=
    Real.rpow_le_rpow (hQ x) hQe (by norm_num)
  have he0 : 0 ≤ e x := le_trans (mul_nonneg hc.le (hQ x)) (henv x)
  rw [Real.div_rpow he0 hc.le] at hpow
  have hcpos : 0 < c ^ (4 / 3 : ℝ) := Real.rpow_pos_of_pos hc _
  have : m x * Q x ^ (4 / 3 : ℝ) ≤ m x * (e x ^ (4 / 3 : ℝ) / c ^ (4 / 3 : ℝ)) :=
    mul_le_mul_of_nonneg_left hpow (hm x)
  calc m x * Q x ^ (4 / 3 : ℝ) ≤ m x * (e x ^ (4 / 3 : ℝ) / c ^ (4 / 3 : ℝ)) := this
    _ = (c ^ (4 / 3 : ℝ))⁻¹ * (m x * e x ^ (4 / 3 : ℝ)) := by
        field_simp

end PositiveHiggs

section PositiveHiggsFamily

variable {D : Type*} [Fintype D]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {ι : Type*} {Cell : ι → Type*} [∀ h, Fintype (Cell h)]

/-- `cor:positive-Higgs-amplitude-criterion`.  Let `K h x : D → F` be the covariant
Higgs packets, `r h x` the sampled positive one-form metrics satisfying the lower
comparison `c_r |ξ|² ≤ r^{μν} Re⟨ξ_μ, ξ_ν⟩` with a cutoff-independent `c_r > 0`
(`eq:positive-Higgs-Hodge-comparison`), and `m h x ≥ 0` the cell masses.  If
`sup_h ‖e_h^{H,+}‖_{L¹_h} < ∞` and `sup_h ‖e_h^{H,+}‖_{L^∞_h} < ∞`
(`eq:positive-Higgs-amplitude-energy`), then
`sup_h ‖e_h^{H,+}‖_{L_h^{4/3}} < ∞` and `sup_h ‖K_h^H‖_{L_h^{8/3}} < ∞`
(`eq:positive-Higgs-compiled-endpoint`). -/
theorem positiveHiggs_amplitude_criterion
    (K : ∀ h, Cell h → D → F) (r : ∀ h, Cell h → D → D → ℝ) (m : ∀ h, Cell h → ℝ)
    (cr : ℝ) (hcr : 0 < cr) (hm : ∀ h x, 0 ≤ m h x)
    (hcomp : ∀ h x, ∀ ξ : D → F,
      cr * positiveHiggsAmpSq ξ ≤ positiveHiggsDensity (r h x) ξ)
    (hL1 : ∃ A, ∀ h, positiveHiggsLpNorm (m h) 1
      (fun x => positiveHiggsDensity (r h x) (K h x)) ≤ A)
    (hLinf : ∃ B, ∀ h x, |positiveHiggsDensity (r h x) (K h x)| ≤ B) :
    (∃ C₁, ∀ h, positiveHiggsLpNorm (m h) (4 / 3)
        (fun x => positiveHiggsDensity (r h x) (K h x)) ≤ C₁) ∧
    (∃ C₂, ∀ h, positiveHiggsLpNorm (m h) (8 / 3)
        (fun x => Real.sqrt (positiveHiggsAmpSq (K h x))) ≤ C₂) := by
  obtain ⟨A, hA⟩ := hL1
  obtain ⟨B, hB⟩ := hLinf
  set e : ∀ h, Cell h → ℝ := fun h x => positiveHiggsDensity (r h x) (K h x) with he_def
  have he0 : ∀ h x, 0 ≤ e h x := fun h x =>
    le_trans (mul_nonneg hcr.le (positiveHiggsAmpSq_nonneg _)) (hcomp h x (K h x))
  set B' := max B 0 with hB'
  have heB : ∀ h x, e h x ≤ B' := fun h x =>
    le_trans (le_trans (le_abs_self _) (hB h x)) (le_max_left _ _)
  have hB'0 : 0 ≤ B' := le_max_right _ _
  -- the L¹ bound in unrolled form
  have hA' : ∀ h, ∑ x, m h x * e h x ≤ A := by
    intro h
    have := hA h
    simp only [positiveHiggsLpNorm, Real.rpow_one, div_one] at this
    refine le_trans (le_of_eq ?_) this
    refine Finset.sum_congr rfl fun x _ => ?_
    exact congrArg _ (abs_of_nonneg (he0 h x)).symm
  -- the 4/3 power sums
  have hS43 : ∀ h, ∑ x, m h x * e h x ^ (4 / 3 : ℝ) ≤ B' ^ (1 / 3 : ℝ) * A := by
    intro h
    refine le_trans (positiveHiggs_L43_interpolation (m h) (e h) B' (hm h) (he0 h)
      (heB h)) ?_
    exact mul_le_mul_of_nonneg_left (hA' h) (Real.rpow_nonneg hB'0 _)
  have hS43' : ∀ h, ∑ x, m h x * |e h x| ^ (4 / 3 : ℝ) ≤ B' ^ (1 / 3 : ℝ) * A := by
    intro h
    simpa [abs_of_nonneg (he0 h _)] using hS43 h
  have hS43nn : ∀ h, 0 ≤ ∑ x, m h x * |e h x| ^ (4 / 3 : ℝ) := fun h =>
    Finset.sum_nonneg fun x _ => mul_nonneg (hm h x) (Real.rpow_nonneg (abs_nonneg _) _)
  refine ⟨⟨(B' ^ (1 / 3 : ℝ) * A) ^ (1 / (4 / 3) : ℝ), fun h => ?_⟩,
    ⟨((cr ^ (4 / 3 : ℝ))⁻¹ * (B' ^ (1 / 3 : ℝ) * A)) ^ (1 / (8 / 3) : ℝ), fun h => ?_⟩⟩
  · exact Real.rpow_le_rpow (hS43nn h) (hS43' h) (by norm_num)
  · have hQ0 : ∀ x, 0 ≤ positiveHiggsAmpSq (K h x) := fun x => positiveHiggsAmpSq_nonneg _
    have hle := positiveHiggs_L83_le_L43 (m h) (e h) (fun x => positiveHiggsAmpSq (K h x))
      cr hcr (hm h) hQ0 (fun x => hcomp h x (K h x))
    have hS83 : ∑ x, m h x * |Real.sqrt (positiveHiggsAmpSq (K h x))| ^ (8 / 3 : ℝ) ≤
        (cr ^ (4 / 3 : ℝ))⁻¹ * (B' ^ (1 / 3 : ℝ) * A) := by
      simp only [abs_of_nonneg (Real.sqrt_nonneg _)]
      refine le_trans hle ?_
      exact mul_le_mul_of_nonneg_left (hS43 h)
        (inv_nonneg.mpr (Real.rpow_nonneg hcr.le _))
    have hnn : 0 ≤ ∑ x, m h x * |Real.sqrt (positiveHiggsAmpSq (K h x))| ^ (8 / 3 : ℝ) :=
      Finset.sum_nonneg fun x _ => mul_nonneg (hm h x) (Real.rpow_nonneg (abs_nonneg _) _)
    exact Real.rpow_le_rpow hnn hS83 (by norm_num)

end PositiveHiggsFamily

end

end RenewalGeometry
