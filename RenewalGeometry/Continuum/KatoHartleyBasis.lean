/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.QuasilinearSymmetricEnergy

/-!
# The real Hartley (`cas`) basis of the slab calculus on `𝕋^d`

Generic infrastructure (no renewal notions) for the spectral Galerkin construction of
`thm:generated-dynamics` / `lem:generated-physical-identification` (Einstein–Standard-Model
action-closure manuscript, `app:generated-dynamics`).

Setting: the slab calculus of `SlabSobolevAlgebra` (space-time `ℝ^{1+d}`, fields smooth and
`ℤ^d`-periodic in space, slices integrated over `[0,1]^d`, classical `H^q` slice norms
`Q q f t = Σ_{|L| ≤ q} ∫ |∂^L f(t,·)|²`).  The real trigonometric basis is the **Hartley basis**
`cas_k(x) = cos(2π k·y) + sin(2π k·y)` (`y` the spatial part of `x`, `k ∈ ℤ^d`), for which
`∂_i cas_k = 2π k_i cas_{-k}` — a real basis closed under differentiation, with a symmetric
frequency set.

* `casS k`: the time-independent field `cas_k`; smooth, periodic, `pd_casS` (`∂_i cas_k =
  2πk_i cas_{-k}`, `∂_t cas_k = 0`).
* `integral_cos_phase`, `integral_sin_phase`: `∫_{[0,1]^d} cos(2πm·y) = [m = 0]`,
  `∫ sin(2πm·y) = 0`; **`integral_casS_mul_casS`**: `{cas_k}` is orthonormal in `L²([0,1]^d)`.
* `wq q k = Σ_{|L| ≤ q} Π_{j ∈ L} (2πk_j)²` (the `H^q` weight of the mode `k`) and
  **`sum_integral_sd_casS_mul`**: for every smooth periodic `g`,
  `Σ_{|L| ≤ q} ∫ ∂^L cas_k ∂^L g = wq q k ∫ cas_k g` (iterated integration by parts).
* Trigonometric fields `tfs S c = Σ_{k ∈ S} c_k cas_k`: coefficients (`coef_tfs`), `L²` norm
  (`integral_tfs_sq`), the `H^q` pairing with any smooth periodic field (`pairWords_tfs`), the
  `H^q` norm `Q q (tfs S c) t = Σ_{k ∈ S} wq q k c_k²` (`Q_tfs`).
* Bessel inequalities in `L²` and in `H^q` (`bessel_L2`, `bessel_Hq`).
* **Completeness** (`eq_zero_of_coef_eq_zero`): a continuous periodic slice all of whose `cas`
  coefficients vanish is zero (through Parseval on `UnitAddTorus`, `hasSum_sq_descend`).
-/

open MeasureTheory Filter Topology Set Finset
open scoped BigOperators ContDiff Real

noncomputable section

namespace RenewalGeometry.KatoGalerkin

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk SlabSobAlg

set_option linter.unusedSectionVars false

variable {d : ℕ}

/-! ### The phase functional and the `cas` fields -/

/-- The phase functional `λ_k(x) = 2π Σ_i k_i x_{i+1}` on space-time. -/
def phL (k : Fin d → ℤ) : ST d →L[ℝ] ℝ :=
  ∑ i, (2 * π * (k i : ℝ)) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (d + 1) => ℝ)
    i.succ

theorem phL_apply (k : Fin d → ℤ) (x : ST d) :
    phL k x = ∑ i, 2 * π * (k i : ℝ) * x i.succ := by
  simp [phL, smul_eq_mul]

theorem phL_neg (k : Fin d → ℤ) (x : ST d) : phL (-k) x = -phL k x := by
  simp only [phL_apply, Pi.neg_apply, Int.cast_neg, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem phL_single_succ (k : Fin d → ℤ) (i : Fin d) :
    phL k (Pi.single i.succ 1) = 2 * π * (k i : ℝ) := by
  rw [phL_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [(Fin.succ_injective _).ne hj]
  · simp

theorem phL_single_zero (k : Fin d → ℤ) : phL k (Pi.single 0 1) = 0 := by
  rw [phL_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  simp [Fin.succ_ne_zero]

theorem phL_cons (k : Fin d → ℤ) (t : ℝ) (y : Fin d → ℝ) :
    phL k (Fin.cons t y : ST d) = 2 * π * ∑ i, (k i : ℝ) * y i := by
  rw [phL_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Fin.cons_succ]; ring

/-- `cas θ = cos θ + sin θ`. -/
def cas (θ : ℝ) : ℝ := Real.cos θ + Real.sin θ

theorem hasDerivAt_cas (θ : ℝ) : HasDerivAt cas (cas (-θ)) θ := by
  have h := (Real.hasDerivAt_cos θ).add (Real.hasDerivAt_sin θ)
  have h2 : cas (-θ) = -Real.sin θ + Real.cos θ := by
    unfold cas; rw [Real.cos_neg, Real.sin_neg]; ring
  rw [h2]; exact h

theorem contDiff_cas : ContDiff ℝ ∞ cas := Real.contDiff_cos.add Real.contDiff_sin

theorem abs_cas_le (θ : ℝ) : |cas θ| ≤ 2 := by
  unfold cas
  refine (abs_add_le _ _).trans ?_
  linarith [Real.abs_cos_le_one θ, Real.abs_sin_le_one θ]

/-- The Hartley mode `cas_k(t, y) = cas(2π k·y)` as a (time-independent) space-time field. -/
def casS (k : Fin d → ℤ) (x : ST d) : ℝ := cas (phL k x)

theorem casS_cons (k : Fin d → ℤ) (t : ℝ) (y : Fin d → ℝ) :
    casS k (Fin.cons t y : ST d) = cas (2 * π * ∑ i, (k i : ℝ) * y i) := by
  rw [casS, phL_cons]

theorem contDiff_casS (k : Fin d → ℤ) : ContDiff ℝ ∞ (casS k) :=
  contDiff_cas.comp (phL k).contDiff

theorem abs_casS_le (k : Fin d → ℤ) (x : ST d) : |casS k x| ≤ 2 := abs_cas_le _

theorem hasFDerivAt_casS (k : Fin d → ℤ) (x : ST d) :
    HasFDerivAt (casS k) (cas (-phL k x) • phL k) x :=
  (hasDerivAt_cas (phL k x)).comp_hasFDerivAt x (phL k).hasFDerivAt

/-- **`∂_i cas_k = 2π k_i cas_{-k}`.** -/
theorem pd_casS_succ (k : Fin d → ℤ) (i : Fin d) :
    pd (casS k) i.succ = fun x => 2 * π * (k i : ℝ) * casS (-k) x := by
  funext x
  unfold SobolevOpen.pd
  rw [(hasFDerivAt_casS k x).fderiv]
  simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul, phL_single_succ, casS, phL_neg]
  ring

theorem pd_casS_zero (k : Fin d → ℤ) : pd (casS k) 0 = fun _ => 0 := by
  funext x
  unfold SobolevOpen.pd
  rw [(hasFDerivAt_casS k x).fderiv]
  simp [phL_single_zero]

theorem phL_sshift (k m : Fin d → ℤ) :
    phL k (sshift m : ST d) = ((∑ i, k i * m i : ℤ) : ℝ) * (2 * π) := by
  rw [phL_apply]
  push_cast
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [sshift, zvec]; ring

theorem isSPeriodic_casS (k : Fin d → ℤ) : IsSPeriodic (casS k) := by
  intro m x
  simp only [casS, map_add, phL_sshift, cas]
  rw [Real.cos_add_int_mul_two_pi, Real.sin_add_int_mul_two_pi]

theorem casS_neg_neg (k : Fin d → ℤ) : casS (-(-k)) = casS k := by rw [neg_neg]

/-! ### Integrals of the characters over the unit cube -/

theorem integral_exp_one (m : ℤ) :
    ∫ t in Icc (0 : ℝ) 1, Complex.exp (((2 * π * (m : ℝ) * t : ℝ) : ℂ) * Complex.I) =
      if m = 0 then 1 else 0 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  by_cases hm : m = 0
  · subst hm; simp
  · rw [if_neg hm]
    have hc : (2 * π * (m : ℂ) * Complex.I) ≠ 0 := by
      have : (m : ℂ) ≠ 0 := by exact_mod_cast hm
      have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      simp [hpi, this, Complex.I_ne_zero]
    have e : (fun t : ℝ => Complex.exp (((2 * π * (m : ℝ) * t : ℝ) : ℂ) * Complex.I)) =
        fun t : ℝ => Complex.exp ((2 * π * (m : ℂ) * Complex.I) * t) := by
      funext t; push_cast; ring_nf
    rw [e, integral_exp_mul_complex hc]
    have h1 : Complex.exp ((2 * π * (m : ℂ) * Complex.I) * ((1 : ℝ) : ℂ)) = 1 := by
      have := Complex.exp_int_mul_two_pi_mul_I m
      rw [← this]; congr 1; push_cast; ring
    rw [h1]; simp

theorem volume_restrict_cube :
    (volume : Measure (Fin d → ℝ)).restrict (Icc 0 1) =
      Measure.pi fun _ => (volume : Measure ℝ).restrict (Icc 0 1) := by
  rw [← Set.pi_univ_Icc, volume_pi, Measure.restrict_pi_pi]
  rfl

/-- `∫_{[0,1]^d} e^{2πi m·y} dy = [m = 0]`. -/
theorem integral_exp_phase (m : Fin d → ℤ) :
    ∫ y in Icc (0 : Fin d → ℝ) 1,
      Complex.exp (((2 * π * ∑ i, (m i : ℝ) * y i : ℝ) : ℂ) * Complex.I) =
      if m = 0 then 1 else 0 := by
  have e : ∀ y : Fin d → ℝ, Complex.exp (((2 * π * ∑ i, (m i : ℝ) * y i : ℝ) : ℂ) * Complex.I) =
      ∏ i, (fun i (t : ℝ) => Complex.exp (((2 * π * (m i : ℝ) * t : ℝ) : ℂ) * Complex.I)) i
        (y i) := by
    intro y
    rw [← Complex.exp_sum]
    congr 1
    push_cast
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => by ring
  simp_rw [e]
  rw [volume_restrict_cube]
  have hp := integral_fintype_prod_eq_prod (𝕜 := ℂ) (ι := Fin d) (E := fun _ => ℝ)
    (fun i (t : ℝ) => Complex.exp (((2 * π * (m i : ℝ) * t : ℝ) : ℂ) * Complex.I))
    (μ := fun _ => (volume : Measure ℝ).restrict (Icc 0 1))
  refine hp.trans ?_
  simp_rw [integral_exp_one]
  by_cases hm : m = 0
  · subst hm; simp
  · rw [if_neg hm]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hm
    simp only [Pi.zero_apply] at hi
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

theorem integrable_exp_phase (m : Fin d → ℤ) :
    IntegrableOn (fun y : Fin d → ℝ =>
      Complex.exp (((2 * π * ∑ i, (m i : ℝ) * y i : ℝ) : ℂ) * Complex.I)) (Icc 0 1) :=
  integrableOn_cube_of_continuousOn (by fun_prop)

/-- `∫_{[0,1]^d} cos(2π m·y) dy = [m = 0]`. -/
theorem integral_cos_phase (m : Fin d → ℤ) :
    ∫ y in Icc (0 : Fin d → ℝ) 1, Real.cos (2 * π * ∑ i, (m i : ℝ) * y i) =
      if m = 0 then 1 else 0 := by
  have h := congrArg Complex.re (integral_exp_phase m)
  have h2 := integral_re (integrable_exp_phase m)
  simp only [RCLike.re_to_complex, Complex.exp_ofReal_mul_I_re] at h2
  rw [← h2] at h
  rw [h]; split_ifs <;> simp

/-- `∫_{[0,1]^d} sin(2π m·y) dy = 0`. -/
theorem integral_sin_phase (m : Fin d → ℤ) :
    ∫ y in Icc (0 : Fin d → ℝ) 1, Real.sin (2 * π * ∑ i, (m i : ℝ) * y i) = 0 := by
  have h := congrArg Complex.im (integral_exp_phase m)
  have h2 := integral_im (integrable_exp_phase m)
  simp only [RCLike.im_to_complex, Complex.exp_ofReal_mul_I_im] at h2
  rw [← h2] at h
  rw [h]; split_ifs <;> simp

theorem phase_sub (k l : Fin d → ℤ) (y : Fin d → ℝ) :
    2 * π * ∑ i, ((k - l) i : ℝ) * y i =
      2 * π * ∑ i, (k i : ℝ) * y i - 2 * π * ∑ i, (l i : ℝ) * y i := by
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1; refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.sub_apply, Pi.add_apply, Int.cast_sub, Int.cast_add]; ring

theorem phase_add (k l : Fin d → ℤ) (y : Fin d → ℝ) :
    2 * π * ∑ i, ((k + l) i : ℝ) * y i =
      2 * π * ∑ i, (k i : ℝ) * y i + 2 * π * ∑ i, (l i : ℝ) * y i := by
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1; refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.sub_apply, Pi.add_apply, Int.cast_sub, Int.cast_add]; ring

/-- `cas a cas b = cos(a - b) + sin(a + b)`. -/
theorem cas_mul_cas (a b : ℝ) : cas a * cas b = Real.cos (a - b) + Real.sin (a + b) := by
  unfold cas; rw [Real.cos_sub, Real.sin_add]; ring

/-- **Orthonormality of the Hartley basis** on every slice:
`∫_{[0,1]^d} cas_k cas_l = [k = l]`. -/
theorem integral_casS_mul_casS (k l : Fin d → ℤ) (t : ℝ) :
    ∫ y in Icc (0 : Fin d → ℝ) 1, casS k (Fin.cons t y) * casS l (Fin.cons t y) =
      if k = l then 1 else 0 := by
  have e : ∀ y : Fin d → ℝ, casS k (Fin.cons t y) * casS l (Fin.cons t y) =
      Real.cos (2 * π * ∑ i, ((k - l) i : ℝ) * y i) +
        Real.sin (2 * π * ∑ i, ((k + l) i : ℝ) * y i) := by
    intro y
    rw [casS_cons, casS_cons, cas_mul_cas, phase_sub, phase_add]
  simp_rw [e]
  rw [integral_add (integrableOn_cube_of_continuousOn (by fun_prop))
    (integrableOn_cube_of_continuousOn (by fun_prop)), integral_cos_phase, integral_sin_phase,
    add_zero]
  simp only [sub_eq_zero]

/-! ### Slice integrals -/

/-- The slice integral `∫_{[0,1]^d} f(t, y) dy`. -/
def sint (f : ST d → ℝ) (t : ℝ) : ℝ := ∫ y in Icc (0 : Fin d → ℝ) 1, f (Fin.cons t y)

theorem sint_add {f g : ST d → ℝ} (hf : Continuous f) (hg : Continuous g) (t : ℝ) :
    sint (fun x => f x + g x) t = sint f t + sint g t :=
  integral_add (integrableOn_slice hf t) (integrableOn_slice hg t)

theorem sint_sub {f g : ST d → ℝ} (hf : Continuous f) (hg : Continuous g) (t : ℝ) :
    sint (fun x => f x - g x) t = sint f t - sint g t :=
  integral_sub (integrableOn_slice hf t) (integrableOn_slice hg t)

theorem sint_const_mul (c : ℝ) (f : ST d → ℝ) (t : ℝ) :
    sint (fun x => c * f x) t = c * sint f t :=
  integral_const_mul c _

theorem sint_neg (f : ST d → ℝ) (t : ℝ) : sint (fun x => -f x) t = -sint f t :=
  integral_neg _

theorem sint_sum {κ : Type*} (s : Finset κ) {f : κ → ST d → ℝ} (hf : ∀ i, Continuous (f i))
    (t : ℝ) : sint (fun x => ∑ i ∈ s, f i x) t = ∑ i ∈ s, sint (f i) t :=
  integral_finset_sum s fun i _ => integrableOn_slice (hf i) t

theorem sint_nonneg {f : ST d → ℝ} (hf : ∀ x, 0 ≤ f x) (t : ℝ) : 0 ≤ sint f t :=
  setIntegral_nonneg measurableSet_Icc fun _ _ => hf _

theorem sint_mono {f g : ST d → ℝ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ x, f x ≤ g x) (t : ℝ) : sint f t ≤ sint g t :=
  setIntegral_mono_on (integrableOn_slice hf t) (integrableOn_slice hg t) measurableSet_Icc
    fun _ _ => h _

theorem sint_const (c : ℝ) (t : ℝ) : sint (d := d) (fun _ => c) t = c := by
  simp [sint, Measure.real, volume_cube]

theorem abs_sint_le {f : ST d → ℝ} {C : ℝ} (h : ∀ x, |f x| ≤ C) (t : ℝ) : |sint f t| ≤ C := by
  unfold sint
  have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Icc (0 : Fin d → ℝ) 1)
    (C := C) (f := fun y => f (Fin.cons t y)) (by rw [volume_cube]; simp)
    (fun y _ => by rw [Real.norm_eq_abs]; exact h _)
  rw [Real.norm_eq_abs] at this
  refine this.trans ?_
  rw [Measure.real, volume_cube]; simp

/-- **Integration by parts on a slice**: `∫ f ∂_i g = -∫ ∂_i f g`. -/
theorem sint_mul_pd {f g : ST d → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfp : IsSPeriodic f) (hgp : IsSPeriodic g) (i : Fin d) (t : ℝ) :
    sint (fun x => f x * pd g i.succ x) t = -sint (fun x => pd f i.succ x * g x) t := by
  have hh : ContDiff ℝ ∞ (fun x => f x * g x) := hf.mul hg
  have h0 := integral_slice_pd_eq_zero (hh.of_le (by exact_mod_cast le_top))
    (isSPeriodic_mul hfp hgp) t i
  have e : ∀ x, pd (fun x => f x * g x) i.succ x = pd f i.succ x * g x + f x * pd g i.succ x :=
    fun x => SobolevOpen.pd_mul (hf.of_le (by exact_mod_cast le_top))
      (hg.of_le (by exact_mod_cast le_top)) _ x
  simp_rw [e] at h0
  have c1 : Continuous fun x => pd f i.succ x * g x :=
    (contDiff_pd_top hf _).continuous.mul hg.continuous
  have c2 : Continuous fun x => f x * pd g i.succ x :=
    hf.continuous.mul (contDiff_pd_top hg _).continuous
  have := sint_add c1 c2 t
  unfold sint at this ⊢
  rw [h0] at this
  linarith

/-! ### Word derivatives of the modes and the `H^q` weights -/

/-- `μ_L(k) = Π_{j ∈ L} (2π k_j)²`. -/
def muL (L : List (Fin d)) (k : Fin d → ℤ) : ℝ := (L.map fun j => (2 * π * (k j : ℝ)) ^ 2).prod

theorem muL_nil (k : Fin d → ℤ) : muL [] k = 1 := rfl

theorem muL_cons (i : Fin d) (L : List (Fin d)) (k : Fin d → ℤ) :
    muL (i :: L) k = (2 * π * (k i : ℝ)) ^ 2 * muL L k := by
  simp [muL]

theorem muL_neg (L : List (Fin d)) (k : Fin d → ℤ) : muL L (-k) = muL L k := by
  simp [muL, neg_sq]

theorem muL_nonneg (L : List (Fin d)) (k : Fin d → ℤ) : 0 ≤ muL L k := by
  induction L with
  | nil => simp [muL]
  | cons i L ih => rw [muL_cons]; positivity

/-- The `H^q` weight of the mode `k`: `wq q k = Σ_{|L| ≤ q} Π_{j ∈ L} (2πk_j)²`. -/
def wq (q : ℕ) (k : Fin d → ℤ) : ℝ := ∑ L ∈ wordsLE d q, muL L k

theorem wq_nonneg (q : ℕ) (k : Fin d → ℤ) : 0 ≤ wq q k :=
  Finset.sum_nonneg fun L _ => muL_nonneg L k

theorem one_le_wq (q : ℕ) (k : Fin d → ℤ) : 1 ≤ wq q k := by
  unfold wq
  have := Finset.single_le_sum (f := fun L => muL L k) (fun L _ => muL_nonneg L k)
    (nil_mem_wordsLE (d := d) q)
  simpa [muL_nil] using this

theorem wq_pos (q : ℕ) (k : Fin d → ℤ) : 0 < wq q k := lt_of_lt_of_le one_pos (one_le_wq q k)

theorem wq_mono {q q' : ℕ} (h : q ≤ q') (k : Fin d → ℤ) : wq q k ≤ wq q' k :=
  Finset.sum_le_sum_of_subset_of_nonneg (wordsLE_mono h) fun L _ _ => muL_nonneg L k

/-- **Word derivatives of a mode against a smooth periodic field**:
`∫ ∂^L cas_k ∂^L g = μ_L(k) ∫ cas_k g` (iterated integration by parts). -/
theorem sint_sd_casS_mul : ∀ (L : List (Fin d)) (k : Fin d → ℤ) {g : ST d → ℝ},
    ContDiff ℝ ∞ g → IsSPeriodic g → ∀ t : ℝ,
      sint (fun x => sd L (casS k) x * sd L g x) t = muL L k * sint (fun x => casS k x * g x) t
  | [], k, g, _, _, t => by simp [muL_nil]
  | i :: L, k, g, hg, hgp, t => by
    have hsd : sd (i :: L) (casS k) = fun x => 2 * π * (k i : ℝ) * sd L (casS (-k)) x := by
      rw [sd_cons, pd_casS_succ, sd_const_mul L (contDiff_casS (-k))]
    rw [hsd, sd_cons]
    have ih := sint_sd_casS_mul L (-k) (contDiff_pd_top hg i.succ) (isSPeriodic_pd hgp _) t
    have e1 : sint (fun x => 2 * π * (k i : ℝ) * sd L (casS (-k)) x * sd L (pd g i.succ) x) t =
        2 * π * (k i : ℝ) * sint (fun x => sd L (casS (-k)) x * sd L (pd g i.succ) x) t := by
      rw [← sint_const_mul]; congr 1; funext x; ring
    rw [e1, ih, sint_mul_pd (contDiff_casS _) hg (isSPeriodic_casS _) hgp, pd_casS_succ,
      muL_neg, muL_cons]
    have e2 : sint (fun x => 2 * π * ((-k) i : ℝ) * casS (-(-k)) x * g x) t =
        2 * π * ((-k) i : ℝ) * sint (fun x => casS k x * g x) t := by
      rw [← sint_const_mul, neg_neg]; congr 1; funext x; ring
    rw [e2]
    simp only [Pi.neg_apply, Int.cast_neg]
    ring

/-- **The `H^q` pairing of a mode**: `Σ_{|L| ≤ q} ∫ ∂^L cas_k ∂^L g = wq q k ∫ cas_k g`. -/
theorem sum_sint_sd_casS_mul (q : ℕ) (k : Fin d → ℤ) {g : ST d → ℝ} (hg : ContDiff ℝ ∞ g)
    (hgp : IsSPeriodic g) (t : ℝ) :
    ∑ L ∈ wordsLE d q, sint (fun x => sd L (casS k) x * sd L g x) t =
      wq q k * sint (fun x => casS k x * g x) t := by
  rw [wq, Finset.sum_mul]
  exact Finset.sum_congr rfl fun L _ => sint_sd_casS_mul L k hg hgp t

/-! ### Trigonometric fields -/

/-- The trigonometric field `Σ_{k ∈ S} c_k cas_k` (time independent). -/
def tfs (S : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℝ) (x : ST d) : ℝ :=
  ∑ k ∈ S, c k * casS k x

/-- The `cas` coefficient `⟨f(t, ·), cas_k⟩_{L²}` of the slice of `f` at time `t`. -/
def coef (f : ST d → ℝ) (t : ℝ) (k : Fin d → ℤ) : ℝ := sint (fun x => casS k x * f x) t

theorem contDiff_tfs (S : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℝ) :
    ContDiff ℝ ∞ (tfs S c) :=
  ContDiff.sum fun k _ => contDiff_const.mul (contDiff_casS k)

theorem isSPeriodic_tfs (S : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℝ) :
    IsSPeriodic (tfs S c) := fun m x => by
  simp only [tfs, isSPeriodic_casS _ m x]

theorem sint_casS_mul_casS (k l : Fin d → ℤ) (t : ℝ) :
    sint (fun x => casS k x * casS l x) t = if k = l then 1 else 0 :=
  integral_casS_mul_casS k l t

/-- `⟨tfs S c, g⟩_{L²} = Σ_{k ∈ S} c_k ⟨cas_k, g⟩`. -/
theorem sint_tfs_mul (S : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℝ) {g : ST d → ℝ}
    (hg : Continuous g) (t : ℝ) :
    sint (fun x => tfs S c x * g x) t = ∑ k ∈ S, c k * coef g t k := by
  have e : (fun x => tfs S c x * g x) = fun x => ∑ k ∈ S, c k * (casS k x * g x) := by
    funext x; rw [tfs, Finset.sum_mul]; exact Finset.sum_congr rfl fun k _ => by ring
  rw [e, sint_sum S (f := fun k x => c k * (casS k x * g x))
    (fun k => continuous_const.mul ((contDiff_casS k).continuous.mul hg))]
  exact Finset.sum_congr rfl fun k _ => sint_const_mul _ _ _

/-- The coefficients of a trigonometric field. -/
theorem coef_tfs (S : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℝ) (t : ℝ) (l : Fin d → ℤ) :
    coef (tfs S c) t l = if l ∈ S then c l else 0 := by
  unfold coef
  have e : (fun x => casS l x * tfs S c x) = fun x => tfs S c x * casS l x := by
    funext x; ring
  rw [e, sint_tfs_mul S c (contDiff_casS l).continuous]
  unfold coef
  simp_rw [sint_casS_mul_casS]
  simp [mul_ite]

theorem coef_tfs_of_mem {S : Finset (Fin d → ℤ)} (c : (Fin d → ℤ) → ℝ) (t : ℝ)
    {l : Fin d → ℤ} (hl : l ∈ S) : coef (tfs S c) t l = c l := by
  rw [coef_tfs, if_pos hl]

theorem sd_tfs (L : List (Fin d)) (S : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℝ) :
    sd L (tfs S c) = fun x => ∑ k ∈ S, c k * sd L (casS k) x := by
  have := sd_sum L S (f := fun k x => c k * casS k x)
    (fun k => contDiff_const.mul (contDiff_casS k))
  unfold tfs
  rw [this]
  funext x
  exact Finset.sum_congr rfl fun k _ => by rw [sd_const_mul L (contDiff_casS k)]

/-- **The `H^q` pairing of a trigonometric field with a smooth periodic field**:
`Σ_{|L| ≤ q} ∫ ∂^L(tfs S c) ∂^L g = Σ_{k ∈ S} c_k wq q k ⟨cas_k, g⟩`. -/
theorem pairWords_tfs (q : ℕ) (S : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℝ) {g : ST d → ℝ}
    (hg : ContDiff ℝ ∞ g) (hgp : IsSPeriodic g) (t : ℝ) :
    ∑ L ∈ wordsLE d q, sint (fun x => sd L (tfs S c) x * sd L g x) t =
      ∑ k ∈ S, c k * wq q k * coef g t k := by
  have hL : ∀ L : List (Fin d), sint (fun x => sd L (tfs S c) x * sd L g x) t =
      ∑ k ∈ S, c k * sint (fun x => sd L (casS k) x * sd L g x) t := by
    intro L
    rw [sd_tfs]
    have e : (fun x => (∑ k ∈ S, c k * sd L (casS k) x) * sd L g x) =
        fun x => ∑ k ∈ S, c k * (sd L (casS k) x * sd L g x) := by
      funext x; rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun k _ => by ring
    rw [e, sint_sum S (f := fun k x => c k * (sd L (casS k) x * sd L g x)) (fun k =>
      continuous_const.mul
        ((contDiff_sd L (contDiff_casS k)).continuous.mul (contDiff_sd L hg).continuous))]
    exact Finset.sum_congr rfl fun k _ => sint_const_mul _ _ _
  simp_rw [hL]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.mul_sum, sum_sint_sd_casS_mul q k hg hgp t, coef]
  ring

theorem Q_eq_sum_sint (q : ℕ) (f : ST d → ℝ) (t : ℝ) :
    Q q f t = ∑ L ∈ wordsLE d q, sint (fun x => sd L f x * sd L f x) t := by
  unfold Q sint
  exact Finset.sum_congr rfl fun L _ => by simp_rw [sq]

/-- **The `H^q` norm of a trigonometric field**: `Q_q(tfs S c) = Σ_{k ∈ S} wq q k c_k²`. -/
theorem Q_tfs (q : ℕ) (S : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℝ) (t : ℝ) :
    Q q (tfs S c) t = ∑ k ∈ S, wq q k * c k ^ 2 := by
  rw [Q_eq_sum_sint, pairWords_tfs q S c (contDiff_tfs S c) (isSPeriodic_tfs S c) t]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [coef_tfs_of_mem c t hk]; ring

/-- The `L²` norm of a trigonometric field (Parseval). -/
theorem sint_tfs_sq (S : Finset (Fin d → ℤ)) (c : (Fin d → ℤ) → ℝ) (t : ℝ) :
    sint (fun x => tfs S c x ^ 2) t = ∑ k ∈ S, c k ^ 2 := by
  have h := Q_tfs 0 S c t
  have hQ : Q 0 (tfs S c) t = sint (fun x => tfs S c x ^ 2) t := by
    simp [Q, wordsLE, sint]
  have hw : ∀ k : Fin d → ℤ, wq 0 k = 1 := fun k => by simp [wq, wordsLE, muL_nil]
  rw [hQ] at h
  rw [h]; simp [hw]

/-- Expansion of the `H^q` norm of a difference. -/
theorem Q_sub_eq (q : ℕ) {f g : ST d → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (t : ℝ) :
    Q q (fun x => g x - f x) t = Q q g t -
      2 * ∑ L ∈ wordsLE d q, sint (fun x => sd L f x * sd L g x) t + Q q f t := by
  rw [Q_eq_sum_sint, Q_eq_sum_sint, Q_eq_sum_sint, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun L _ => ?_
  rw [sd_sub L hg hf]
  have cf := (contDiff_sd L hf).continuous
  have cg := (contDiff_sd L hg).continuous
  have e : (fun x => (sd L g x - sd L f x) * (sd L g x - sd L f x)) =
      fun x => (sd L g x * sd L g x - 2 * (sd L f x * sd L g x)) + sd L f x * sd L f x := by
    funext x; ring
  rw [e, sint_add (f := fun x => sd L g x * sd L g x - 2 * (sd L f x * sd L g x))
    (g := fun x => sd L f x * sd L f x) ((cg.mul cg).sub (continuous_const.mul (cf.mul cg)))
    (cf.mul cf),
    sint_sub (f := fun x => sd L g x * sd L g x) (g := fun x => 2 * (sd L f x * sd L g x))
      (cg.mul cg) (continuous_const.mul (cf.mul cg)), sint_const_mul]

/-- **Bessel's inequality in `H^q`**: `Σ_{k ∈ S} wq q k ⟨g, cas_k⟩² ≤ ‖g‖²_{H^q}`. -/
theorem bessel_Hq (q : ℕ) (S : Finset (Fin d → ℤ)) {g : ST d → ℝ} (hg : ContDiff ℝ ∞ g)
    (hgp : IsSPeriodic g) (t : ℝ) :
    ∑ k ∈ S, wq q k * coef g t k ^ 2 ≤ Q q g t := by
  have h := Q_sub_eq q (contDiff_tfs S (coef g t)) hg t
  rw [pairWords_tfs q S _ hg hgp t, Q_tfs] at h
  have h0 := Q_nonneg q (fun x => g x - tfs S (coef g t) x) t
  have e : ∑ k ∈ S, coef g t k * wq q k * coef g t k = ∑ k ∈ S, wq q k * coef g t k ^ 2 :=
    Finset.sum_congr rfl fun k _ => by ring
  rw [e] at h
  linarith

/-- **Bessel's inequality in `L²`**. -/
theorem bessel_L2 (S : Finset (Fin d → ℤ)) {g : ST d → ℝ} (hg : Continuous g) (t : ℝ) :
    ∑ k ∈ S, coef g t k ^ 2 ≤ sint (fun x => g x ^ 2) t := by
  set P := tfs S (coef g t)
  have hP : Continuous P := (contDiff_tfs S _).continuous
  have h0 : 0 ≤ sint (fun x => (g x - P x) ^ 2) t := sint_nonneg (fun x => sq_nonneg _) t
  have e : (fun x => (g x - P x) ^ 2) = fun x => (g x ^ 2 - 2 * (P x * g x)) + P x ^ 2 := by
    funext x; ring
  rw [e, sint_add (f := fun x => g x ^ 2 - 2 * (P x * g x)) (g := fun x => P x ^ 2)
    ((hg.pow 2).sub (continuous_const.mul (hP.mul hg))) (hP.pow 2),
    sint_sub (f := fun x => g x ^ 2) (g := fun x => 2 * (P x * g x)) (hg.pow 2)
      (continuous_const.mul (hP.mul hg)), sint_const_mul,
    sint_tfs_mul S _ hg, sint_tfs_sq] at h0
  have e2 : ∑ k ∈ S, coef g t k * coef g t k = ∑ k ∈ S, coef g t k ^ 2 :=
    Finset.sum_congr rfl fun k _ => by ring
  rw [e2] at h0
  linarith

/-! ### Completeness of the Hartley basis -/

theorem eq_zero_on_cube_of_sint_sq {f : ST d → ℝ} (hf : Continuous f) (t : ℝ)
    (h : sint (fun x => f x ^ 2) t = 0) : ∀ y ∈ Icc (0 : Fin d → ℝ) 1, f (Fin.cons t y) = 0 := by
  have hc : Continuous fun y : Fin d → ℝ => f (Fin.cons t y) ^ 2 :=
    (hf.comp (continuous_cons t)).pow 2
  have hint : IntegrableOn (fun y : Fin d → ℝ => f (Fin.cons t y) ^ 2) (Icc 0 1) :=
    integrableOn_cube_of_continuousOn hc.continuousOn
  have hae : (fun y : Fin d → ℝ => f (Fin.cons t y) ^ 2) =ᵐ[volume.restrict (Icc 0 1)] 0 :=
    (setIntegral_eq_zero_iff_of_nonneg_ae (ae_of_all _ fun y => sq_nonneg _) hint).mp h
  set S : Set (Fin d → ℝ) := Set.pi univ fun _ => Ioo (0 : ℝ) 1 with hS
  have hSsub : S ⊆ Icc (0 : Fin d → ℝ) 1 := by
    intro y hy
    rw [← Set.pi_univ_Icc]
    exact fun i _ => Ioo_subset_Icc_self (hy i (mem_univ i))
  have hSopen : IsOpen S := isOpen_set_pi finite_univ fun _ _ => isOpen_Ioo
  have hae' : (fun y : Fin d → ℝ => f (Fin.cons t y) ^ 2) =ᵐ[volume.restrict S] 0 :=
    ae_restrict_of_ae_restrict_of_subset hSsub hae
  have heq : EqOn (fun y : Fin d → ℝ => f (Fin.cons t y) ^ 2) 0 S :=
    Measure.eqOn_open_of_ae_eq hae' hSopen hc.continuousOn continuousOn_const
  have hz : EqOn (fun y : Fin d → ℝ => f (Fin.cons t y)) 0 S := fun y hy => by
    have := heq hy
    simpa using this
  have hcl := hz.closure (hf.comp (continuous_cons t)) continuous_const
  have hclS : closure S = Icc (0 : Fin d → ℝ) 1 := by
    rw [hS, closure_pi_set, ← Set.pi_univ_Icc]
    congr 1; funext i
    exact closure_Ioo zero_ne_one
  intro y hy
  rw [← hclS] at hy
  exact hcl hy

theorem eq_zero_of_sint_sq {f : ST d → ℝ} (hf : Continuous f) (hp : IsSPeriodic f) (t : ℝ)
    (h : sint (fun x => f x ^ 2) t = 0) (y : Fin d → ℝ) : f (Fin.cons t y) = 0 := by
  have hcube := eq_zero_on_cube_of_sint_sq hf t h
  have hper := hp.slice t
  have hfr : (fun i => Int.fract (y i)) ∈ Icc (0 : Fin d → ℝ) 1 :=
    ⟨fun i => Int.fract_nonneg _, fun i => (Int.fract_lt_one _).le⟩
  have := hcube _ hfr
  rwa [hper.apply_fract y] at this

theorem mFourier_torusMk (n : Fin d → ℤ) (y : Fin d → ℝ) :
    UnitAddTorus.mFourier n (SobolevBoxCr.torusMk y) =
      Complex.exp (((2 * π * ∑ i, (n i : ℝ) * y i : ℝ) : ℂ) * Complex.I) := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, SobolevBoxCr.torusMk]
  simp_rw [fourier_coe_apply]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  field_simp

theorem cos_eq_casS (n : Fin d → ℤ) (t : ℝ) (y : Fin d → ℝ) :
    Real.cos (2 * π * ∑ i, (n i : ℝ) * y i) =
      (casS n (Fin.cons t y) + casS (-n) (Fin.cons t y)) / 2 := by
  rw [casS_cons, casS_cons]
  have e : 2 * π * ∑ i, ((-n) i : ℝ) * y i = -(2 * π * ∑ i, (n i : ℝ) * y i) := by
    rw [← mul_neg, ← Finset.sum_neg_distrib]; congr 1
    refine Finset.sum_congr rfl fun i _ => ?_; simp
  rw [e]; unfold cas; rw [Real.cos_neg, Real.sin_neg]; ring

theorem sin_eq_casS (n : Fin d → ℤ) (t : ℝ) (y : Fin d → ℝ) :
    Real.sin (2 * π * ∑ i, (n i : ℝ) * y i) =
      (casS n (Fin.cons t y) - casS (-n) (Fin.cons t y)) / 2 := by
  rw [casS_cons, casS_cons]
  have e : 2 * π * ∑ i, ((-n) i : ℝ) * y i = -(2 * π * ∑ i, (n i : ℝ) * y i) := by
    rw [← mul_neg, ← Finset.sum_neg_distrib]; congr 1
    refine Finset.sum_congr rfl fun i _ => ?_; simp
  rw [e]; unfold cas; rw [Real.cos_neg, Real.sin_neg]; ring

theorem unitCube_ae_eq_Icc :
    (SobolevOpen.unitCube : Set (Fin d → ℝ)) =ᵐ[volume] Icc (0 : Fin d → ℝ) 1 := by
  have h := boxIoc_ae_eq (ι := Fin d) 0
  rw [zero_add] at h
  have e : (SobolevOpen.unitCube : Set (Fin d → ℝ)) = boxIoc 0 := by
    ext y; simp [SobolevOpen.unitCube, boxIoc]
  rw [e]; exact h

/-- **Completeness of the Hartley basis**: a continuous spatially periodic field whose slice at
time `t` has all `cas` coefficients zero vanishes on that slice. -/
theorem eq_zero_of_coef_eq_zero {f : ST d → ℝ} (hf : Continuous f) (hp : IsSPeriodic f)
    (t : ℝ) (h : ∀ k, coef f t k = 0) (y : Fin d → ℝ) : f (Fin.cons t y) = 0 := by
  set g : (Fin d → ℝ) → ℂ := fun y => (f (Fin.cons t y) : ℂ) with hg
  have hgc : Continuous g := Complex.continuous_ofReal.comp (hf.comp (continuous_cons t))
  have hgp : SobolevBoxCr.IsPeriodic g := fun m x => by
    simp only [hg]
    congr 1
    exact hp.slice t m x
  have hcos : ∀ n : Fin d → ℤ, ∫ y in Icc (0 : Fin d → ℝ) 1,
      Real.cos (2 * π * ∑ i, (n i : ℝ) * y i) * f (Fin.cons t y) = 0 := by
    intro n
    have e : (fun y : Fin d → ℝ => Real.cos (2 * π * ∑ i, (n i : ℝ) * y i) * f (Fin.cons t y)) =
        fun y => (1 / 2) * ((fun x => casS n x * f x + casS (-n) x * f x) (Fin.cons t y)) := by
      funext y; rw [cos_eq_casS n t y]; ring
    rw [e]
    have := sint_add (f := fun x => casS n x * f x) (g := fun x => casS (-n) x * f x)
      ((contDiff_casS n).continuous.mul hf) ((contDiff_casS (-n)).continuous.mul hf) t
    rw [integral_const_mul]
    unfold sint at this
    rw [this]
    have h1 := h n; have h2 := h (-n); unfold coef sint at h1 h2
    rw [h1, h2]; ring
  have hsin : ∀ n : Fin d → ℤ, ∫ y in Icc (0 : Fin d → ℝ) 1,
      Real.sin (2 * π * ∑ i, (n i : ℝ) * y i) * f (Fin.cons t y) = 0 := by
    intro n
    have e : (fun y : Fin d → ℝ => Real.sin (2 * π * ∑ i, (n i : ℝ) * y i) * f (Fin.cons t y)) =
        fun y => (1 / 2) * ((fun x => casS n x * f x - casS (-n) x * f x) (Fin.cons t y)) := by
      funext y; rw [sin_eq_casS n t y]; ring
    rw [e]
    have := sint_sub (f := fun x => casS n x * f x) (g := fun x => casS (-n) x * f x)
      ((contDiff_casS n).continuous.mul hf) ((contDiff_casS (-n)).continuous.mul hf) t
    rw [integral_const_mul]
    unfold sint at this
    rw [this]
    have h1 := h n; have h2 := h (-n); unfold coef sint at h1 h2
    rw [h1, h2]; ring
  have hcoef : ∀ n, UnitAddTorus.mFourierCoeff (SobolevBoxCr.descendFun g) n = 0 := by
    intro n
    unfold UnitAddTorus.mFourierCoeff
    rw [SobolevOpen.integral_torus_eq_unitCube]
    have e : ∀ y : Fin d → ℝ, UnitAddTorus.mFourier (-n) (fun i => (y i : UnitAddCircle)) •
        SobolevBoxCr.descendFun g (fun i => (y i : UnitAddCircle)) =
        ((Real.cos (2 * π * ∑ i, (n i : ℝ) * y i) * f (Fin.cons t y) : ℝ) : ℂ) -
          ((Real.sin (2 * π * ∑ i, (n i : ℝ) * y i) * f (Fin.cons t y) : ℝ) : ℂ) *
            Complex.I := by
      intro y
      have h1 := SobolevBoxCr.descendFun_mk hgp y
      have h2 := mFourier_torusMk (-n) y
      rw [show (fun i => (y i : UnitAddCircle)) = SobolevBoxCr.torusMk y from rfl, h1, h2,
        smul_eq_mul]
      have e3 : 2 * π * ∑ i, ((-n) i : ℝ) * y i = -(2 * π * ∑ i, (n i : ℝ) * y i) := by
        rw [← mul_neg, ← Finset.sum_neg_distrib]; congr 1
        refine Finset.sum_congr rfl fun i _ => ?_; simp
      rw [e3, Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg]
      push_cast; ring
    simp_rw [e]
    rw [setIntegral_congr_set unitCube_ae_eq_Icc]
    have i1 : IntegrableOn (fun y : Fin d → ℝ =>
        ((Real.cos (2 * π * ∑ i, (n i : ℝ) * y i) * f (Fin.cons t y) : ℝ) : ℂ)) (Icc 0 1) :=
      integrableOn_cube_of_continuousOn
        (Complex.continuous_ofReal.comp (by fun_prop : Continuous fun y : Fin d → ℝ =>
          Real.cos (2 * π * ∑ i, (n i : ℝ) * y i) * f (Fin.cons t y))).continuousOn
    have i2 : IntegrableOn (fun y : Fin d → ℝ =>
        ((Real.sin (2 * π * ∑ i, (n i : ℝ) * y i) * f (Fin.cons t y) : ℝ) : ℂ) * Complex.I)
        (Icc 0 1) :=
      integrableOn_cube_of_continuousOn
        ((Complex.continuous_ofReal.comp (by fun_prop : Continuous fun y : Fin d → ℝ =>
          Real.sin (2 * π * ∑ i, (n i : ℝ) * y i) * f (Fin.cons t y))).mul
          continuous_const).continuousOn
    rw [integral_sub i1 i2, integral_mul_const, integral_complex_ofReal, integral_complex_ofReal, hcos n,
      hsin n]
    simp
  have hsum := SobolevBoxCr.hasSum_sq_descend hgc hgp
  simp only [hcoef, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hsum
  have h0 : ∫ y in SobolevOpen.unitCube, ‖g y‖ ^ 2 = 0 := hsum.unique hasSum_zero
  rw [setIntegral_congr_set unitCube_ae_eq_Icc] at h0
  have h0' : sint (fun x => f x ^ 2) t = 0 := by
    unfold sint
    rw [← h0]
    refine setIntegral_congr_fun measurableSet_Icc fun y _ => ?_
    simp [hg, Complex.norm_real, sq_abs]
  exact eq_zero_of_sint_sq hf hp t h0' y

end RenewalGeometry.KatoGalerkin
