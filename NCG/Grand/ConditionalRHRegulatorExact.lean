/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.FiniteSpectralDeterminantZeroLines

/-!
# Conditional critical-line regulator theorem
  (`thm:conditional-RH-regulator`)

Nonzero holomorphic regulators `F_X = h_X·D_{A_X}` with
nowhere-zero `h_X` and co-isometric normal families
(`A_X* A_X = c_X I`) have all their determinant zeros on the
moving critical lines `Re s = a_X/2`; if `F_X → F` locally
uniformly with `F ≢ 0` and `a_X → a`, every zero of the limit
lies on `Re s = a/2`.

This file proves the record's two missing layers exactly:

* `hurwitz_ne_zero`: **Hurwitz's theorem** in local
  nonvanishing form, by the maximum-modulus principle applied
  to `1/F_X` on a small disc around a putative zero — the
  first Hurwitz formalization in this development;
* `specDet_zero_re`: zeros of the finite spectral determinant
  of a co-isometric matrix lie on `Re s = log c/(2ℓ)` (via an
  explicit resonating eigenvector and the norm identity
  `‖Av‖² = c‖v‖²`);
* `conditional_RH_regulator`: the boxed conclusion — every
  zero of `F` lies on `Re s = a/2`.
-/

open Metric Filter Topology Matrix

namespace NCG
namespace RHRegulator

/-! ### Hurwitz's theorem -/

/-- **Hurwitz's theorem, local nonvanishing form**: if
holomorphic `Fn → F` locally uniformly on an open set, the
`Fn` are eventually zero-free on a closed ball around `z₀`
inside the set, and `F` is not locally identically zero at
`z₀`, then `F z₀ ≠ 0`. -/
theorem hurwitz_ne_zero
    {Fn : ℕ → ℂ → ℂ} {F : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U)
    (hd : ∀ n, DifferentiableOn ℂ (Fn n) U)
    (hlim : TendstoLocallyUniformlyOn Fn F atTop U)
    (z₀ : ℂ) (hz₀ : z₀ ∈ U) {r : ℝ} (hr : 0 < r)
    (hball : closedBall z₀ r ⊆ U)
    (hev : ∀ᶠ n in atTop,
      ∀ z ∈ closedBall z₀ r, Fn n z ≠ 0)
    (hnloc : ¬ (F =ᶠ[𝓝 z₀] 0)) :
    F z₀ ≠ 0 := by
  intro hF0
  have hFd : DifferentiableOn ℂ F U :=
    hlim.differentiableOn (Eventually.of_forall hd) hU
  have han : AnalyticAt ℂ F z₀ :=
    (hFd.analyticOnNhd hU) z₀ hz₀
  rcases han.eventually_eq_zero_or_eventually_ne_zero
    with hcase | hcase
  · exact hnloc hcase
  -- extract a punctured radius on which `F` is zero-free
  rw [(Metric.nhdsWithin_basis_ball).eventually_iff]
    at hcase
  obtain ⟨ρ₀, hρ₀, hpunct⟩ := hcase
  set ρ : ℝ := min (ρ₀ / 2) r with hρdef
  have hρpos : 0 < ρ :=
    lt_min (by positivity) hr
  have hρr : ρ ≤ r := min_le_right _ _
  have hρρ₀ : ρ < ρ₀ :=
    lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hcbU : closedBall z₀ ρ ⊆ U :=
    (closedBall_subset_closedBall hρr).trans hball
  -- `F` is zero-free on the sphere of radius `ρ`
  have hFsphere : ∀ z ∈ sphere z₀ ρ, F z ≠ 0 := by
    intro z hz
    refine hpunct ⟨?_, ?_⟩
    · rw [mem_ball, mem_sphere] at *
      rw [hz]
      exact hρρ₀
    · rw [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro hzz
      rw [hzz] at hz
      simp only [mem_sphere, dist_self] at hz
      exact (ne_of_gt hρpos) hz.symm
  -- minimum of `‖F‖` on the sphere
  have hFc : ContinuousOn F (sphere z₀ ρ) :=
    (hFd.continuousOn).mono
      (sphere_subset_closedBall.trans hcbU)
  obtain ⟨w, hw, hwmin⟩ :=
    (isCompact_sphere z₀ ρ).exists_isMinOn
      (NormedSpace.sphere_nonempty.mpr hρpos.le) hFc.norm
  set δ : ℝ := ‖F w‖ with hδdef
  have hδpos : 0 < δ :=
    norm_pos_iff.mpr (hFsphere w hw)
  -- uniform convergence on the closed ball of radius `ρ`
  have hunif :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact
      hU).mp hlim (closedBall z₀ ρ) hcbU
      (isCompact_closedBall _ _)
  have hclose := Metric.tendstoUniformlyOn_iff.mp hunif
    (δ / 2) (by positivity)
  obtain ⟨n, hn1, hn2⟩ := (hclose.and hev).exists
  -- maximum modulus for `(Fn n)⁻¹` on the ball
  have hg : DiffContOnCl ℂ (Fn n)⁻¹ (ball z₀ ρ) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball z₀ (ne_of_gt hρpos)]
    refine DifferentiableOn.inv
      ((hd n).mono hcbU) ?_
    intro x hx
    exact hn2 x (closedBall_subset_closedBall hρr hx)
  have hfr : ∀ z ∈ frontier (ball z₀ ρ),
      ‖(Fn n)⁻¹ z‖ ≤ (δ / 2)⁻¹ := by
    rw [frontier_ball z₀ (ne_of_gt hρpos)]
    intro z hz
    have h1 : δ ≤ ‖F z‖ := hwmin hz
    have h2 : dist (F z) (Fn n z) < δ / 2 :=
      hn1 z (sphere_subset_closedBall hz)
    have h3 : ‖F z‖ - ‖Fn n z‖ ≤ ‖F z - Fn n z‖ :=
      norm_sub_norm_le _ _
    rw [dist_eq_norm] at h2
    have hFnz : δ / 2 ≤ ‖Fn n z‖ := by linarith
    rw [Pi.inv_apply, norm_inv]
    exact (inv_le_inv₀
      (lt_of_lt_of_le (by positivity) hFnz)
      (by positivity)).mpr hFnz
  have hmax := Complex.norm_le_of_forall_mem_frontier_norm_le
    isBounded_ball hg hfr
    (show z₀ ∈ closure (ball z₀ ρ) by
      rw [closure_ball z₀ (ne_of_gt hρpos)]
      exact mem_closedBall_self hρpos.le)
  -- hence `Fn n` is bounded below at `z₀`
  have hFn0 : Fn n z₀ ≠ 0 :=
    hn2 z₀ (mem_closedBall_self (le_trans hρpos.le hρr))
  have h4 : δ / 2 ≤ ‖Fn n z₀‖ := by
    rw [Pi.inv_apply, norm_inv] at hmax
    by_contra hcon
    push Not at hcon
    have hpos : 0 < ‖Fn n z₀‖ := norm_pos_iff.mpr hFn0
    have h5 : (δ / 2)⁻¹ < ‖Fn n z₀‖⁻¹ :=
      (inv_lt_inv₀ (by positivity) hpos).mpr hcon
    linarith
  -- contradiction with convergence at `z₀`
  have h6 : dist (F z₀) (Fn n z₀) < δ / 2 :=
    hn1 z₀ (mem_closedBall_self hρpos.le)
  rw [hF0, dist_comm, dist_zero_right] at h6
  linarith

/-! ### Zero lines of co-isometric spectral determinants -/

/-- The dot-product norm identity forced by `Aᴴ A = c•1`. -/
theorem dotProduct_mulVec_self {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℂ) (c : ℝ)
    (hAA : Aᴴ * A = (c : ℂ) • 1) (v : Fin d → ℂ) :
    star (A.mulVec v) ⬝ᵥ A.mulVec v
      = (c : ℂ) * (star v ⬝ᵥ v) := by
  rw [Matrix.star_mulVec,
    ← Matrix.dotProduct_mulVec (star v) Aᴴ (A.mulVec v),
    Matrix.mulVec_mulVec, hAA, Matrix.smul_mulVec,
    Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]

/-- **Zero-line theorem for co-isometric determinants**: every
zero of the finite spectral determinant of `A` with
`Aᴴ A = c•1` lies on `Re s = log c / (2ℓ)`. -/
theorem specDet_zero_re {d : ℕ}
    (A : Matrix (Fin d) (Fin d) ℂ) (ℓ c : ℝ)
    (hℓ : 0 < ℓ) (_hc : 0 < c)
    (hAA : Aᴴ * A = (c : ℂ) • 1) (s : ℂ)
    (hzero : finiteSpectralDeterminant A ℓ s = 0) :
    s.re = Real.log c / (2 * ℓ) := by
  have hdet : (1 - Complex.exp (-(ℓ:ℂ) * s) • A).det = 0 :=
    hzero
  obtain ⟨v, hv0, hvec⟩ :=
    Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  set e : ℂ := Complex.exp (-(ℓ:ℂ) * s) with he
  have hene : e ≠ 0 := Complex.exp_ne_zero _
  have hAv : A.mulVec v = e⁻¹ • v := by
    have h1 : v - e • A.mulVec v = 0 := by
      have h2 := hvec
      rwa [Matrix.sub_mulVec, Matrix.one_mulVec,
        Matrix.smul_mulVec] at h2
    have h3 : v = e • A.mulVec v := by
      rwa [sub_eq_zero] at h1
    conv_rhs => rw [h3]
    rw [smul_smul, inv_mul_cancel₀ hene, one_smul]
  have hnorm := dotProduct_mulVec_self A c hAA v
  rw [hAv] at hnorm
  have hL : star (e⁻¹ • v) ⬝ᵥ (e⁻¹ • v)
      = (starRingEnd ℂ e⁻¹ * e⁻¹) * (star v ⬝ᵥ v) := by
    rw [star_smul, smul_dotProduct, dotProduct_smul,
      smul_eq_mul, smul_eq_mul, Complex.star_def]
    ring
  rw [hL] at hnorm
  have hS : star v ⬝ᵥ v
      = ((∑ i, Complex.normSq (v i) : ℝ) : ℂ) := by
    unfold dotProduct
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.star_apply, Complex.star_def, mul_comm,
      Complex.mul_conj]
  have hSpos : (0:ℝ) < ∑ i, Complex.normSq (v i) := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv0
    refine Finset.sum_pos'
      (fun j _ => Complex.normSq_nonneg _)
      ⟨i, Finset.mem_univ i, ?_⟩
    exact Complex.normSq_pos.mpr hi
  have hSne : ((∑ i, Complex.normSq (v i) : ℝ) : ℂ)
      ≠ 0 := by
    exact_mod_cast ne_of_gt hSpos
  have hmodc : starRingEnd ℂ e⁻¹ * e⁻¹ = (c : ℂ) := by
    have h1 : (starRingEnd ℂ e⁻¹ * e⁻¹)
        * ((∑ i, Complex.normSq (v i) : ℝ) : ℂ)
        = (c : ℂ)
          * ((∑ i, Complex.normSq (v i) : ℝ) : ℂ) := by
      rw [← hS]
      exact hnorm
    exact mul_right_cancel₀ hSne h1
  have hns : Complex.normSq e⁻¹ = c := by
    have h1 : ((Complex.normSq e⁻¹ : ℝ) : ℂ)
        = (c : ℂ) := by
      rw [← hmodc, mul_comm, Complex.mul_conj]
    exact_mod_cast h1
  have hnorm_e : ‖e‖ = Real.exp (-(ℓ * s.re)) := by
    rw [he, Complex.norm_exp]
    congr 1
    simp [Complex.mul_re]
  have hns2 : Complex.normSq e⁻¹ = ‖e‖⁻¹ ^ 2 := by
    rw [Complex.normSq_eq_norm_sq, norm_inv]
  rw [hns2, hnorm_e] at hns
  have hexp : Real.exp (ℓ * s.re) ^ 2 = c := by
    rw [← hns, Real.exp_neg, inv_inv]
  have hlog := congrArg Real.log hexp
  rw [Real.log_pow, Real.log_exp] at hlog
  push_cast at hlog
  have hℓne : ℓ ≠ 0 := ne_of_gt hℓ
  field_simp
  linarith

/-! ### The conditional critical-line regulator -/

/-- **Conditional critical-line regulator theorem**: locally
uniform limits of co-isometric spectral regulators have every
zero on the limiting critical line `Re s = a/2`. -/
theorem conditional_RH_regulator
    {Ω : Set ℂ} (hΩo : IsOpen Ω) (hΩc : IsPreconnected Ω)
    {F : ℂ → ℂ} {Fn : ℕ → ℂ → ℂ} {d : ℕ → ℕ}
    {A : (n : ℕ) → Matrix (Fin (d n)) (Fin (d n)) ℂ}
    {h : ℕ → ℂ → ℂ} {ℓ c : ℕ → ℝ} {a : ℝ}
    (hd : ∀ n, DifferentiableOn ℂ (Fn n) Ω)
    (hlim : TendstoLocallyUniformlyOn Fn F atTop Ω)
    (hFne : ∃ z ∈ Ω, F z ≠ 0)
    (hfact : ∀ n, ∀ z ∈ Ω, Fn n z
      = h n z * finiteSpectralDeterminant (A n) (ℓ n) z)
    (hh : ∀ n, ∀ z ∈ Ω, h n z ≠ 0)
    (hAA : ∀ n, (A n)ᴴ * A n = ((c n : ℝ) : ℂ) • 1)
    (hℓ : ∀ n, 0 < ℓ n) (hc : ∀ n, 0 < c n)
    (ha : Tendsto (fun n => Real.log (c n) / (2 * ℓ n))
      atTop (𝓝 (a / 2)))
    (z₀ : ℂ) (hz₀ : z₀ ∈ Ω) (hF0 : F z₀ = 0) :
    z₀.re = a / 2 := by
  by_contra hre
  set ε : ℝ := |z₀.re - a / 2| with hεdef
  have hεpos : 0 < ε := abs_pos.mpr (sub_ne_zero.mpr hre)
  obtain ⟨r₀, hr₀, hball₀⟩ :=
    Metric.isOpen_iff.mp hΩo z₀ hz₀
  set ρ : ℝ := min (r₀ / 2) (ε / 2) with hρdef
  have hρpos : 0 < ρ :=
    lt_min (by positivity) (by positivity)
  have hρr : ρ ≤ r₀ / 2 := min_le_left _ _
  have hρε : ρ ≤ ε / 2 := min_le_right _ _
  have hballΩ : closedBall z₀ ρ ⊆ Ω := by
    refine (closedBall_subset_ball ?_).trans hball₀
    linarith
  have hev_line : ∀ᶠ n in atTop,
      |Real.log (c n) / (2 * ℓ n) - a / 2| < ε / 2 := by
    have hmem := ha (Metric.ball_mem_nhds (a / 2)
      (show (0:ℝ) < ε / 2 by positivity))
    filter_upwards [hmem] with n hn
    rw [Set.mem_preimage, mem_ball, Real.dist_eq] at hn
    exact hn
  have hev : ∀ᶠ n in atTop,
      ∀ z ∈ closedBall z₀ ρ, Fn n z ≠ 0 := by
    filter_upwards [hev_line] with n hn z hz
    rw [hfact n z (hballΩ hz)]
    refine mul_ne_zero (hh n z (hballΩ hz)) ?_
    intro hdet0
    have hz_re := specDet_zero_re (A n) (ℓ n) (c n)
      (hℓ n) (hc n) (hAA n) z hdet0
    have h1 : |z.re - z₀.re| ≤ ρ := by
      have h2 : |(z - z₀).re| ≤ ‖z - z₀‖ :=
        Complex.abs_re_le_norm _
      rw [Complex.sub_re] at h2
      rw [mem_closedBall, dist_eq_norm] at hz
      linarith
    rw [hz_re] at h1
    have h3 := abs_sub_le z₀.re
      (Real.log (c n) / (2 * ℓ n)) (a / 2)
    have h4 : |z₀.re - Real.log (c n) / (2 * ℓ n)|
        ≤ ρ := by
      rw [abs_sub_comm]
      exact h1
    have h5 : ε < ε := by
      calc ε = |z₀.re - a / 2| := hεdef
        _ ≤ |z₀.re - Real.log (c n) / (2 * ℓ n)|
            + |Real.log (c n) / (2 * ℓ n) - a / 2| := h3
        _ < ε / 2 + ε / 2 := by
            have := hρε
            linarith
        _ = ε := by ring
    exact absurd h5 (lt_irrefl ε)
  have hnloc : ¬ (F =ᶠ[𝓝 z₀] 0) := by
    intro hloc
    obtain ⟨w, hwΩ, hwne⟩ := hFne
    have hFd : DifferentiableOn ℂ F Ω :=
      hlim.differentiableOn (Eventually.of_forall hd) hΩo
    have hzero := (hFd.analyticOnNhd
      hΩo).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      hΩc hz₀ hloc
    exact hwne (hzero hwΩ)
  exact hurwitz_ne_zero hΩo hd hlim z₀ hz₀ hρpos hballΩ
    hev hnloc hF0

end RHRegulator
end NCG
