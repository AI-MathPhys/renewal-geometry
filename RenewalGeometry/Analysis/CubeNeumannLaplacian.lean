/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.CubeGaffney
import RenewalGeometry.Analysis.UhlenbeckCoulombIFT

/-!
# The Neumann Laplacian on the cube `Q₀ = (0,1/2)⁴`: solvability, `H²` and `H^{k+2}` regularity
  (stage B1 of the cube rendering of Uhlenbeck's small-energy gauge theorem)

Generic infrastructure (no renewal notions) for `prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript.

The Neumann problem `Δξ = f` in `Q₀`, `∂_ν ξ = 0` on `∂Q₀` (compatibility `∫_{Q₀} f = 0`) is the
torus problem `Δξ̃ = f̃` for the even extension (cosine series):

* `integral_conj_parExt_mul`: `∫_{𝕋⁴} conj(parExt S u) · parExt S v = 16 ∫_{Q₀} conj(u) v`;
* `hasParity_laplace_solution`: the mean-zero torus solution of `Δξ = f` has the parity of `f`;
* `neumann_laplace_cube` (**solvability with `H²` regularity up to the boundary**): for
  `f ∈ L²(Q₀)` with `∫_{Q₀} f = 0` there is `ξ ∈ W^{1,2}(Q₀)` with `∫_{Q₀} ξ = 0`, first partials
  `∂_μ ξ ∈ W^{1,2}(Q₀)` (so `ξ ∈ H²(Q₀)`), the **weak Neumann identity**
  `Σ_μ ∫_{Q₀} conj(∂_μ φ) ∂_μ ξ = -∫_{Q₀} conj(φ) f` for every `φ ∈ W^{1,2}(Q₀)` (no boundary
  condition on `φ`: the Neumann condition is natural), `Σ_μ ∂_μ∂_μ ξ = f` a.e. on `Q₀`, the bounds
  `‖∂²ξ‖, ‖∂ξ‖, ‖ξ‖ ≤ ‖f‖` in `L²(Q₀)`, and **`H^{k+2}` regularity for compatible data**: if the
  even extension of `f` is in `H^k(𝕋⁴)` (compatibility of the odd normal derivatives of `f` with
  the reflection), then the even extension of `ξ` is in `H^{k+2}(𝕋⁴)`, for every real `k ≥ 0`;
* `neumann_laplace_cube_unique`: uniqueness among mean-zero `W^{1,2}(Q₀)` weak solutions.
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

/-! ### Integral transfer for products -/

theorem integrable_conj_mul_Q0 {u v : (Fin 4 → ℝ) → ℂ} (hu : MemLp u 2 (volume.restrict Q0))
    (hv : MemLp v 2 (volume.restrict Q0)) :
    Integrable (fun x => conj (u x) * v x) (volume.restrict Q0) :=
  hu.star.integrable_mul hv

/-- `∫_{𝕋⁴} conj(parExt S u) · parExt S v = 16 ∫_{Q₀} conj(u) · v`. -/
theorem integral_conj_parExt_mul {S : Finset (Fin 4)} {u v : (Fin 4 → ℝ) → ℂ}
    (hu : MemLp u 2 (volume.restrict Q0)) (hv : MemLp v 2 (volume.restrict Q0)) :
    ∫ t, conj (parExt S u t) * parExt S v t = 16 * ∫ x in Q0, conj (u x) * v x := by
  have e : (fun t => conj (parExt S u t) * parExt S v t) =
      parExt ∅ (fun x => conj (u x) * v x) := by
    funext t
    rw [parExt_conj, parExt_mul, symmDiff_self, Finset.bot_eq_empty]
  rw [e]
  exact integral_parExt (integrable_conj_mul_Q0 hu hv)

theorem mFourierCoeff_congr_ae {f g : 𝕋⁴ → ℂ} (h : f =ᵐ[volume] g) :
    mFourierCoeff f = mFourierCoeff g := by
  funext n; unfold mFourierCoeff
  exact integral_congr_ae (h.mono fun x hx => by simp only [hx])

/-! ### Parity of the torus solution -/

theorem lapSym_flip (j : Fin 4) (n : Fin 4 → ℤ) : lapSym (flip j n) = lapSym n := by
  unfold lapSym
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : i = j
  · subst hi; rw [flip_apply_self]; push_cast; ring
  · rw [flip_apply_ne hi]

/-- Fourier form of `Σ_μ ∂_μ∂_μ ξ = f`: `-|n|² ξ̂(n) = f̂(n)`. -/
theorem coeff_laplace {ξ f : 𝕋⁴ → ℂ} {dξ : Fin 4 → 𝕋⁴ → ℂ} {d2ξ : Fin 4 → Fin 4 → 𝕋⁴ → ℂ}
    (hd2 : ∀ μ ν, MemLp (d2ξ μ ν) 2 volume) (hd : ∀ μ, IsTPartial μ ξ (dξ μ))
    (hdd : ∀ μ ν, IsTPartial ν (dξ μ) (d2ξ μ ν)) (heq : ∀ᵐ x ∂volume, ∑ μ, d2ξ μ μ x = f x)
    (n : Fin 4 → ℤ) : -(lapSym n : ℂ) * mFourierCoeff ξ n = mFourierCoeff f n := by
  have h1 : mFourierCoeff f n = mFourierCoeff (fun x => ∑ μ, d2ξ μ μ x) n :=
    congrFun (mFourierCoeff_congr_ae (heq.mono fun x hx => hx.symm)) n
  rw [h1, mFourierCoeff_finset_sum _ fun μ => integrable_of_memLp_two (hd2 μ μ)]
  simp only [hdd _ _ n, hd _ n]
  rw [← sum_sym_sq, Finset.sum_mul]
  exact Finset.sum_congr rfl fun μ _ => by ring

/-- **The mean-zero solution of `Δξ = f` inherits the parity pattern of `f`.** -/
theorem hasParity_laplace_solution {S : Finset (Fin 4)} {ξ f : 𝕋⁴ → ℂ}
    {dξ : Fin 4 → 𝕋⁴ → ℂ} {d2ξ : Fin 4 → Fin 4 → 𝕋⁴ → ℂ} (hξ : MemLp ξ 2 volume)
    (hf : MemLp f 2 volume) (hfS : HasParity S f)
    (hd2 : ∀ μ ν, MemLp (d2ξ μ ν) 2 volume) (hd : ∀ μ, IsTPartial μ ξ (dξ μ))
    (hdd : ∀ μ ν, IsTPartial ν (dξ μ) (d2ξ μ ν)) (heq : ∀ᵐ x ∂volume, ∑ μ, d2ξ μ μ x = f x)
    (h0 : mFourierCoeff ξ 0 = 0) : HasParity S ξ := by
  rw [hasParity_iff_coeff hξ]
  intro j n
  have hc := coeff_laplace hd2 hd hdd heq
  by_cases hn : n = 0
  · subst hn; rw [flip_zero, h0, mul_zero]
  · have hfn : flip j n ≠ 0 := fun h => hn (flip_eq_zero_iff.1 h)
    have hL : (lapSym n : ℂ) ≠ 0 := by
      have := one_le_lapSym hn; exact_mod_cast (show lapSym n ≠ 0 by linarith)
    have h1 := hc (flip j n)
    rw [lapSym_flip, (hasParity_iff_coeff hf).1 hfS j n, ← hc n] at h1
    have : -(lapSym n : ℂ) * (mFourierCoeff ξ (flip j n) - pSign S j * mFourierCoeff ξ n) = 0 := by
      rw [mul_sub, h1]; ring
    rcases mul_eq_zero.1 this with h | h
    · exact absurd (neg_eq_zero.1 h) hL
    · exact sub_eq_zero.1 h

/-! ### The Neumann problem on the cube -/

/-- Mean value of a function on `Q₀` through the torus. -/
theorem integral_Q0_eq_of_parExt {u : (Fin 4 → ℝ) → ℂ} (hu : MemLp u 2 (volume.restrict Q0)) :
    16 * ∫ x in Q0, u x = mFourierCoeff (parExt ∅ u) 0 := by
  have : IsFiniteMeasure (volume.restrict Q0) := isFiniteMeasure_restrict.2 (volume_box_ne_top _ _)
  rw [mFourierCoeff_zero_eq_integral, integral_parExt (hu.integrable (by norm_num))]

/-- **The Neumann problem on the cube** `Δξ = f` in `Q₀`, `∂_ν ξ = 0` on `∂Q₀`
(compatibility `∫_{Q₀} f = 0`): existence of a mean-zero weak solution with `H²(Q₀)` regularity up
to the boundary, `L²` bounds, the weak Neumann identity against all `φ ∈ W^{1,2}(Q₀)`, and
`H^{k+2}` regularity of the even extension for data with `H^k` even extension. -/
theorem neumann_laplace_cube {f : (Fin 4 → ℝ) → ℂ} (hf : MemLp f 2 (volume.restrict Q0))
    (hf0 : ∫ x in Q0, f x = 0) :
    ∃ (ξ : (Fin 4 → ℝ) → ℂ) (g : Fin 4 → (Fin 4 → ℝ) → ℂ) (g2 : Fin 4 → Fin 4 → (Fin 4 → ℝ) → ℂ),
      MemW12 Q0 ξ g ∧ (∀ μ, MemW12 Q0 (g μ) (g2 μ)) ∧ ∫ x in Q0, ξ x = 0 ∧
      (∀ᵐ x ∂(volume.restrict Q0), ∑ μ, g2 μ μ x = f x) ∧
      (∀ (φ : (Fin 4 → ℝ) → ℂ) (gφ : Fin 4 → (Fin 4 → ℝ) → ℂ), MemW12 Q0 φ gφ →
        ∑ μ, ∫ x in Q0, conj (gφ μ x) * g μ x = -∫ x in Q0, conj (φ x) * f x) ∧
      (∀ μ ν, eLpNorm (g2 μ ν) 2 (volume.restrict Q0) ≤ eLpNorm f 2 (volume.restrict Q0)) ∧
      (∀ μ, eLpNorm (g μ) 2 (volume.restrict Q0) ≤ eLpNorm f 2 (volume.restrict Q0)) ∧
      eLpNorm ξ 2 (volume.restrict Q0) ≤ eLpNorm f 2 (volume.restrict Q0) ∧
      (∀ k : ℝ, 0 ≤ k → MemH k (parExt ∅ f) → MemH (k + 2) (parExt ∅ ξ)) := by
  set F := parExt ∅ f
  have hF : MemLp F 2 volume := memLp_parExt (by norm_num) (by norm_num) hf
  have hF0 : mFourierCoeff F 0 = 0 := by rw [← integral_Q0_eq_of_parExt hf, hf0, mul_zero]
  obtain ⟨Ξ, dΞ, d2Ξ, hΞ, hdΞ, hd2Ξ, hΞ0, hd, hdd, heq, hb2, hb1, hb0⟩ := laplace_solve hF hF0
  -- parities
  have hpΞ : HasParity ∅ Ξ :=
    hasParity_laplace_solution hΞ hF (hasParity_parExt ∅ f) hd2Ξ hd hdd heq hΞ0
  have hpdΞ : ∀ μ, HasParity {μ} (dΞ μ) := fun μ => by
    have := hpΞ.partial hΞ (hdΞ μ) (hd μ)
    rwa [show symmDiff (∅ : Finset (Fin 4)) {μ} = {μ} by ext; simp [Finset.mem_symmDiff]] at this
  have hpd2Ξ : ∀ μ ν, HasParity (symmDiff {μ} {ν}) (d2Ξ μ ν) := fun μ ν =>
    (hpdΞ μ).partial (hdΞ μ) (hd2Ξ μ ν) (hdd μ ν)
  -- cube functions
  set ξ : (Fin 4 → ℝ) → ℂ := fun x => Ξ (chart0 x)
  set g : Fin 4 → (Fin 4 → ℝ) → ℂ := fun μ x => dΞ μ (chart0 x)
  set g2 : Fin 4 → Fin 4 → (Fin 4 → ℝ) → ℂ := fun μ ν x => d2Ξ μ ν (chart0 x)
  have hW : MemW12 Q0 ξ g := memW12_restrict hΞ hdΞ hd
  have hW2 : ∀ μ, MemW12 Q0 (g μ) (g2 μ) := fun μ =>
    memW12_restrict (hdΞ μ) (hd2Ξ μ) (hdd μ)
  -- the torus functions are the extensions of the cube functions
  have eΞ : Ξ =ᵐ[volume] parExt ∅ ξ := parExt_restrict hpΞ
  have edΞ : ∀ μ, dΞ μ =ᵐ[volume] parExt {μ} (g μ) := fun μ => parExt_restrict (hpdΞ μ)
  have ed2Ξ : ∀ μ ν, d2Ξ μ ν =ᵐ[volume] parExt (symmDiff {μ} {ν}) (g2 μ ν) := fun μ ν =>
    parExt_restrict (hpd2Ξ μ ν)
  have hQ : MeasurableSet Q0 := (isOpen_box _ _).measurableSet
  -- norms
  have norm2 : ∀ {S : Finset (Fin 4)} {H : 𝕋⁴ → ℂ} {h : (Fin 4 → ℝ) → ℂ},
      MemLp h 2 (volume.restrict Q0) → H =ᵐ[volume] parExt S h →
      eLpNorm H 2 volume = 4 * eLpNorm h 2 (volume.restrict Q0) := fun hh hH => by
    rw [eLpNorm_congr_ae hH, eLpNorm_parExt_two hh]
  have hfn : eLpNorm F 2 volume = 4 * eLpNorm f 2 (volume.restrict Q0) := eLpNorm_parExt_two hf
  refine ⟨ξ, g, g2, hW, hW2, ?_, ?_, ?_, fun μ ν => ?_, fun μ => ?_, ?_, ?_⟩
  · -- mean zero
    have := integral_Q0_eq_of_parExt hW.memLp
    rw [← mFourierCoeff_congr_ae eΞ, hΞ0] at this
    exact (mul_eq_zero.1 this).resolve_left (by norm_num)
  · -- the equation on `Q₀`
    have h1 := TorusChart.ae_chart_of_ae one_pos Q0_subset_cubeAt heq
    filter_upwards [h1, ae_restrict_mem hQ] with x hx hxQ
    simp only [g2]
    rw [hx]
    exact parExt_chart0 ∅ f hxQ
  · -- the weak Neumann identity
    intro φ gφ hφ
    obtain ⟨hφ1, hφ2, hφ3⟩ := isTPartial_parExt hφ
    have hT : ∀ μ, ∫ t, conj (parExt {μ} (gφ μ) t) * dΞ μ t =
        -∫ t, conj (parExt ∅ φ t) * d2Ξ μ μ t := fun μ =>
      integral_conj_partial_mul hφ1 (hdΞ μ) (hφ2 μ) (hd2Ξ μ μ) (hφ3 μ) (hdd μ μ)
    have hsum : ∑ μ, ∫ t, conj (parExt {μ} (gφ μ) t) * dΞ μ t =
        -∫ t, conj (parExt ∅ φ t) * F t := by
      simp only [hT, Finset.sum_neg_distrib]
      congr 1
      rw [← integral_finset_sum _ fun μ _ => integrable_conj_mul hφ1 (hd2Ξ μ μ)]
      refine integral_congr_ae (heq.mono fun t ht => ?_)
      simp only [← Finset.mul_sum, ht]
    have hL : ∀ μ, ∫ t, conj (parExt {μ} (gφ μ) t) * dΞ μ t =
        16 * ∫ x in Q0, conj (gφ μ x) * g μ x := fun μ => by
      rw [← integral_conj_parExt_mul (S := {μ}) (hφ.memLp_grad μ) (hW.memLp_grad μ)]
      exact integral_congr_ae ((edΞ μ).mono fun t ht => by simp only [ht])
    have hR : ∫ t, conj (parExt ∅ φ t) * F t = 16 * ∫ x in Q0, conj (φ x) * f x :=
      integral_conj_parExt_mul hφ.memLp hf
    rw [hR] at hsum
    simp only [hL, ← Finset.mul_sum] at hsum
    have h16 : (16 : ℂ) ≠ 0 := by norm_num
    have : (16 : ℂ) * ((∑ μ, ∫ x in Q0, conj (gφ μ x) * g μ x) + ∫ x in Q0, conj (φ x) * f x)
        = 0 := by
      rw [mul_add, hsum]; ring
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h h16
    · exact eq_neg_of_add_eq_zero_left h
  · have := hb2 μ ν
    rw [norm2 ((hW2 μ).memLp_grad ν) (ed2Ξ μ ν), hfn] at this
    exact ennreal_cancel_four this
  · have := hb1 μ
    rw [norm2 (hW.memLp_grad μ) (edΞ μ), hfn] at this
    exact ennreal_cancel_four this
  · have := hb0
    rw [norm2 hW.memLp eΞ, hfn] at this
    exact ennreal_cancel_four this
  · -- `H^{k+2}` regularity of the even extension
    intro k hk hFk
    unfold MemH CoeffMemH at hFk ⊢
    rw [← mFourierCoeff_congr_ae eΞ]
    refine (hFk.mul_left 4).of_nonneg_of_le
      (fun n => mul_nonneg (sobWeight_rpow_nonneg n _) (sq_nonneg _)) fun n => ?_
    have hc := coeff_laplace hd2Ξ hd hdd heq n
    have hw : sobWeight n = 1 + lapSym n := by
      simp only [sobWeight, lapSym]
      rw [Finset.mul_sum]; congr 1
      refine Finset.sum_congr rfl fun i _ => by ring
    by_cases hn : n = 0
    · subst hn
      rw [hΞ0, norm_zero, zero_pow two_ne_zero, mul_zero]
      exact mul_nonneg (by norm_num) (mul_nonneg (sobWeight_rpow_nonneg _ _) (sq_nonneg _))
    · have hL := one_le_lapSym hn
      have hξn : ‖mFourierCoeff Ξ n‖ = ‖mFourierCoeff F n‖ / lapSym n := by
        rw [← hc, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by linarith)]
        field_simp
      rw [hξn, Real.rpow_add (sobWeight_pos n), Real.rpow_two]
      have hS : sobWeight n ^ (2 : ℝ) / lapSym n ^ 2 ≤ 4 := by
        rw [hw, Real.rpow_two, div_le_iff₀ (by positivity)]
        nlinarith
      rw [Real.rpow_two] at hS
      calc sobWeight n ^ k * sobWeight n ^ 2 * (‖mFourierCoeff F n‖ / lapSym n) ^ 2
          = sobWeight n ^ k * ‖mFourierCoeff F n‖ ^ 2 * (sobWeight n ^ 2 / lapSym n ^ 2) := by
            field_simp
        _ ≤ sobWeight n ^ k * ‖mFourierCoeff F n‖ ^ 2 * 4 := by
            gcongr
            exact mul_nonneg (sobWeight_rpow_nonneg n k) (sq_nonneg _)
        _ = 4 * (sobWeight n ^ k * ‖mFourierCoeff F n‖ ^ 2) := by ring

/-! ### Uniqueness -/

theorem hasWeakPartial_sub {Ω : Set (Fin 4 → ℝ)} {i : Fin 4} {u v gu gv : (Fin 4 → ℝ) → ℂ}
    (hu : HasWeakPartial Ω i u gu) (hv : HasWeakPartial Ω i v gv)
    (hu1 : LocallyIntegrableOn u Ω) (hv1 : LocallyIntegrableOn v Ω)
    (hgu1 : LocallyIntegrableOn gu Ω) (hgv1 : LocallyIntegrableOn gv Ω) :
    HasWeakPartial Ω i (fun x => u x - v x) (fun x => gu x - gv x) := by
  intro φ hφ
  have hc : Continuous fun x => ((pd φ i x : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_pd (hφ.smooth.of_le (by simp)) i)
  have hcs : HasCompactSupport fun x => ((pd φ i x : ℝ) : ℂ) :=
    (hasCompactSupport_pd hφ.compact i).comp_left Complex.ofReal_zero
  have hts : tsupport (fun x => ((pd φ i x : ℝ) : ℂ)) ⊆ Ω :=
    (tsupport_comp_subset Complex.ofReal_zero _).trans ((tsupport_pd_subset φ i).trans hφ.subset)
  have hc' : Continuous fun x => ((φ x : ℝ) : ℂ) := Complex.continuous_ofReal.comp hφ.continuous
  have hcs' : HasCompactSupport fun x => ((φ x : ℝ) : ℂ) := hφ.compact.comp_left Complex.ofReal_zero
  have hts' : tsupport (fun x => ((φ x : ℝ) : ℂ)) ⊆ Ω :=
    (tsupport_comp_subset Complex.ofReal_zero _).trans hφ.subset
  have i1 := integrable_mul_of_locallyIntegrableOn hu1 hc hcs hts
  have i2 := integrable_mul_of_locallyIntegrableOn hv1 hc hcs hts
  have i3 := integrable_mul_of_locallyIntegrableOn hgu1 hc' hcs' hts'
  have i4 := integrable_mul_of_locallyIntegrableOn hgv1 hc' hcs' hts'
  simp only [mul_sub]
  rw [integral_sub i1 i2, integral_sub i3 i4, hu φ hφ, hv φ hφ]
  ring

theorem memW12_sub {Ω : Set (Fin 4 → ℝ)} {u v : (Fin 4 → ℝ) → ℂ}
    {gu gv : Fin 4 → (Fin 4 → ℝ) → ℂ} (hu : MemW12 Ω u gu) (hv : MemW12 Ω v gv) :
    MemW12 Ω (fun x => u x - v x) (fun i x => gu i x - gv i x) :=
  ⟨hu.memLp.sub hv.memLp, fun i => (hu.memLp_grad i).sub (hv.memLp_grad i), fun i =>
    hasWeakPartial_sub (hu.weak i) (hv.weak i) (locallyIntegrableOn_of_memLp hu.memLp)
      (locallyIntegrableOn_of_memLp hv.memLp) (locallyIntegrableOn_of_memLp (hu.memLp_grad i))
      (locallyIntegrableOn_of_memLp (hv.memLp_grad i))⟩

theorem integral_conj_mul_self_Q0 {h : (Fin 4 → ℝ) → ℂ} (hh : MemLp h 2 (volume.restrict Q0)) :
    ∫ x in Q0, conj (h x) * h x = ((∫ x in Q0, ‖h x‖ ^ 2 : ℝ) : ℂ) := by
  rw [← integral_complex_ofReal]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [Complex.conj_mul', Complex.ofReal_pow]

/-- **Uniqueness for the weak Neumann problem**: a mean-zero `W^{1,2}(Q₀)` function whose
gradient is orthogonal to all gradients, `Σ_μ ∫_{Q₀} conj(∂_μ φ) ∂_μ w = 0` for every
`φ ∈ W^{1,2}(Q₀)`, vanishes a.e. on `Q₀` (and so does its gradient). -/
theorem neumann_cube_unique {w : (Fin 4 → ℝ) → ℂ} {gw : Fin 4 → (Fin 4 → ℝ) → ℂ}
    (hw : MemW12 Q0 w gw) (h0 : ∫ x in Q0, w x = 0)
    (hweak : ∀ (φ : (Fin 4 → ℝ) → ℂ) (gφ : Fin 4 → (Fin 4 → ℝ) → ℂ), MemW12 Q0 φ gφ →
      ∑ μ, ∫ x in Q0, conj (gφ μ x) * gw μ x = 0) :
    w =ᵐ[volume.restrict Q0] 0 ∧ ∀ μ, gw μ =ᵐ[volume.restrict Q0] 0 := by
  have h1 := hweak w gw hw
  simp only [fun μ => integral_conj_mul_self_Q0 (hw.memLp_grad μ)] at h1
  rw [← Complex.ofReal_sum, Complex.ofReal_eq_zero] at h1
  have hnn : ∀ μ, 0 ≤ ∫ x in Q0, ‖gw μ x‖ ^ 2 := fun μ => integral_nonneg fun _ => by positivity
  have hz : ∀ μ, ∫ x in Q0, ‖gw μ x‖ ^ 2 = 0 := fun μ =>
    (Finset.sum_eq_zero_iff_of_nonneg fun μ _ => hnn μ).1 h1 μ (Finset.mem_univ μ)
  have hg0 : ∀ μ, eLpNorm (gw μ) 2 (volume.restrict Q0) = 0 := fun μ => by
    rw [eLpNorm_two_eq_sqrt (hw.memLp_grad μ), hz μ, Real.sqrt_zero, ENNReal.ofReal_zero]
  have hP := poincare_cube_scalar hw h0
  simp only [hg0, Finset.sum_const_zero, nonpos_iff_eq_zero] at hP
  exact ⟨(eLpNorm_eq_zero_iff hw.memLp.1 (by norm_num)).1 hP, fun μ =>
    (eLpNorm_eq_zero_iff (hw.memLp_grad μ).1 (by norm_num)).1 (hg0 μ)⟩

end RenewalGeometry.CubeNeumann
