/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.SobolevTorusBridge

/-!
# Calculus of `ℤ^ι`-periodic functions on the unit cube

Generic infrastructure (no renewal notions) for energy estimates on `𝕋^ι = ℝ^ι / ℤ^ι`, written
for functions on `ℝ^ι` that are periodic under integer translations, integrated over the closed
unit cube `[0,1]^ι = Icc 0 1` (Lebesgue measure; the cube `[0,1)^ι` or `(0,1]^ι` gives the same
integrals).

* `IsZPeriodic f`: `f (x + k) = f x` for all `k ∈ ℤ^ι`.
* `lintegral_boxIoc_eq`, `integral_boxIoc_eq`: the integral over any translate
  `Π (a_i, a_i + 1]` of the unit cube is the same (through `UnitAddTorus.integral_preimage`).
* `integral_cube_comp_add` (**translation invariance**): `∫_{[0,1]^ι} f(x + v) dx = ∫ f`.
* `IsZPeriodic.exists_bound`: periodic continuous functions are bounded.
* `integral_pd_eq_zero` (**integration by parts**): `∫_{[0,1]^ι} ∂_j h = 0` for `C¹` periodic `h`.
* `neg_two_integral_ip_pd_le` (**Lipschitz commutator / Friedrichs lemma**): for a Hermitian,
  `L`-Lipschitz, periodic matrix field `A` and a `C¹` periodic vector field `f`,
  `-2 ∫ Re⟨A ∂_j f, f⟩ ≤ |N|² L ∫ ‖f‖²`; no derivative of `A` is used (the classical
  `∫ Re⟨A∂f,f⟩ = -½∫⟨(∂A)f,f⟩` for `W^{1,∞}` coefficients, proved by symmetric difference
  quotients).
* `integral_norm_pd_sq_le` (**interpolation `H¹` between `L²` and `H²`**): for `C²` periodic
  `g : ℝ^ι → ℂ` and every `λ > 0`,
  `∫ |∂_j g|² ≤ (λ/2) ∫ |∂_j∂_j g|² + (2λ)⁻¹ ∫ |g|²`.

The pointwise inner product `ip u v = Re Σ_i conj(u_i) v_i` on `ℂ^N` and the matrix action
`mv A v` (`(A v)_i = Σ_j A_ij v_j`) are used with the sup norms of `N → ℂ` and `N → N → ℂ`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff

noncomputable section

namespace RenewalGeometry.PeriodicCube

open SobolevOpen (pd)

set_option linter.unusedSectionVars false

/-! ### Pointwise algebra on `ℂ^N` -/

section Algebra

variable {N : Type*} [Fintype N]

/-- The real inner product `Re Σ_i conj(u_i) v_i` on `ℂ^N`. -/
def ip (u v : N → ℂ) : ℝ := (∑ i, star (u i) * v i).re

/-- Matrix–vector product `(A v)_i = Σ_j A_ij v_j`. -/
def mv (A : N → N → ℂ) (v : N → ℂ) : N → ℂ := fun i => ∑ j, A i j * v j

theorem ip_comm (u v : N → ℂ) : ip u v = ip v u := by
  unfold ip
  rw [← Complex.conj_re, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [mul_comm]

theorem ip_add_left (u u' v : N → ℂ) : ip (u + u') v = ip u v + ip u' v := by
  simp [ip, add_mul, Finset.sum_add_distrib]

theorem ip_add_right (u v v' : N → ℂ) : ip u (v + v') = ip u v + ip u v' := by
  simp [ip, mul_add, Finset.sum_add_distrib]

theorem ip_sub_left (u u' v : N → ℂ) : ip (u - u') v = ip u v - ip u' v := by
  simp [ip, sub_mul, Finset.sum_sub_distrib]

theorem ip_sub_right (u v v' : N → ℂ) : ip u (v - v') = ip u v - ip u v' := by
  simp [ip, mul_sub, Finset.sum_sub_distrib]

theorem ip_smul_left (r : ℝ) (u v : N → ℂ) : ip (r • u) v = r * ip u v := by
  simp only [ip, Pi.smul_apply, Complex.real_smul, star_mul', Complex.star_def,
    Complex.conj_ofReal, mul_assoc, ← Finset.mul_sum, Complex.re_ofReal_mul]

theorem ip_smul_right (r : ℝ) (u v : N → ℂ) : ip u (r • v) = r * ip u v := by
  rw [ip_comm, ip_smul_left, ip_comm]

theorem ip_neg_left (u v : N → ℂ) : ip (-u) v = -ip u v := by
  simp [ip, Finset.sum_neg_distrib]

theorem ip_zero_left (v : N → ℂ) : ip 0 v = 0 := by simp [ip]

theorem mv_add (A : N → N → ℂ) (u v : N → ℂ) : mv A (u + v) = mv A u + mv A v := by
  funext i; simp [mv, mul_add, Finset.sum_add_distrib]

theorem mv_sub (A : N → N → ℂ) (u v : N → ℂ) : mv A (u - v) = mv A u - mv A v := by
  funext i; simp [mv, mul_sub, Finset.sum_sub_distrib]

theorem mv_smul (A : N → N → ℂ) (r : ℝ) (v : N → ℂ) : mv A (r • v) = r • mv A v := by
  funext i
  simp only [mv, Pi.smul_apply, Complex.real_smul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem mv_sub_left (A B : N → N → ℂ) (v : N → ℂ) : mv (A - B) v = mv A v - mv B v := by
  funext i; simp [mv, sub_mul, Finset.sum_sub_distrib]

theorem mv_add_left (A B : N → N → ℂ) (v : N → ℂ) : mv (A + B) v = mv A v + mv B v := by
  funext i; simp [mv, add_mul, Finset.sum_add_distrib]

theorem mv_zero (A : N → N → ℂ) : mv A 0 = 0 := by funext i; simp [mv]

/-- Hermitian matrices are symmetric for `ip`. -/
theorem ip_mv_herm {A : N → N → ℂ} (hA : ∀ i k, A k i = star (A i k)) (u v : N → ℂ) :
    ip (mv A u) v = ip u (mv A v) := by
  unfold ip mv
  congr 1
  simp only [star_sum, star_mul', Finset.sum_mul, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [← hA b a]
  ring

theorem norm_le_of_forall {u : N → ℂ} {C : ℝ} (hC : 0 ≤ C) (h : ∀ i, ‖u i‖ ≤ C) : ‖u‖ ≤ C :=
  (pi_norm_le_iff_of_nonneg hC).mpr h

theorem abs_ip_le (u v : N → ℂ) : |ip u v| ≤ Fintype.card N * (‖u‖ * ‖v‖) := by
  unfold ip
  refine (Complex.abs_re_le_norm _).trans ((norm_sum_le _ _).trans ?_)
  calc ∑ i, ‖star (u i) * v i‖ ≤ ∑ _i : N, ‖u‖ * ‖v‖ := Finset.sum_le_sum fun i _ => by
        rw [norm_mul, norm_star]
        exact mul_le_mul (norm_le_pi_norm u i) (norm_le_pi_norm v i) (norm_nonneg _)
          (norm_nonneg _)
    _ = _ := by simp

theorem norm_mv_le (A : N → N → ℂ) (v : N → ℂ) : ‖mv A v‖ ≤ Fintype.card N * (‖A‖ * ‖v‖) := by
  refine norm_le_of_forall (by positivity) fun i => (norm_sum_le _ _).trans ?_
  calc ∑ j, ‖A i j * v j‖ ≤ ∑ _j : N, ‖A‖ * ‖v‖ := Finset.sum_le_sum fun j _ => by
        rw [norm_mul]
        exact mul_le_mul ((norm_le_pi_norm (A i) j).trans (norm_le_pi_norm A i))
          (norm_le_pi_norm v j) (norm_nonneg _) (norm_nonneg _)
    _ = _ := by simp

/-- `|Re⟨u, A v⟩| ≤ |N|² ‖A‖ ‖u‖ ‖v‖`. -/
theorem abs_ip_mv_le (A : N → N → ℂ) (u v : N → ℂ) :
    |ip u (mv A v)| ≤ (Fintype.card N : ℝ) ^ 2 * ‖A‖ * (‖u‖ * ‖v‖) := by
  refine (abs_ip_le _ _).trans ?_
  have := norm_mv_le A v
  have h0 : (0 : ℝ) ≤ Fintype.card N := Nat.cast_nonneg _
  calc (Fintype.card N : ℝ) * (‖u‖ * ‖mv A v‖)
      ≤ Fintype.card N * (‖u‖ * (Fintype.card N * (‖A‖ * ‖v‖))) := by gcongr
    _ = _ := by ring

theorem ip_self_eq (u : N → ℂ) : ip u u = ∑ i, ‖u i‖ ^ 2 := by
  unfold ip
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  norm_cast

theorem norm_sq_le_sum (u : N → ℂ) : ‖u‖ ^ 2 ≤ ∑ i, ‖u i‖ ^ 2 := by
  have hs : 0 ≤ ∑ i, ‖u i‖ ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have h : ‖u‖ ≤ Real.sqrt (∑ i, ‖u i‖ ^ 2) := norm_le_of_forall (Real.sqrt_nonneg _) fun i =>
    Real.le_sqrt_of_sq_le (Finset.single_le_sum (f := fun i => ‖u i‖ ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i))
  calc ‖u‖ ^ 2 ≤ (Real.sqrt (∑ i, ‖u i‖ ^ 2)) ^ 2 := by gcongr
    _ = _ := Real.sq_sqrt hs

theorem sum_norm_sq_le (u : N → ℂ) : ∑ i, ‖u i‖ ^ 2 ≤ Fintype.card N * ‖u‖ ^ 2 := by
  calc ∑ i, ‖u i‖ ^ 2 ≤ ∑ _i : N, ‖u‖ ^ 2 := Finset.sum_le_sum fun i _ => by
        gcongr; exact norm_le_pi_norm u i
    _ = _ := by simp

/-- Uniform positivity gives the coercive bound `‖ξ‖ ≤ (|N|/c) ‖A ξ‖`. -/
theorem norm_le_of_coercive {A : N → N → ℂ} {c : ℝ} (hc : 0 < c)
    (hpos : ∀ ξ : N → ℂ, c * ∑ i, ‖ξ i‖ ^ 2 ≤ ip ξ (mv A ξ)) (ξ : N → ℂ) :
    ‖ξ‖ ≤ Fintype.card N / c * ‖mv A ξ‖ := by
  have h1 : c * ‖ξ‖ ^ 2 ≤ Fintype.card N * (‖ξ‖ * ‖mv A ξ‖) :=
    (mul_le_mul_of_nonneg_left (norm_sq_le_sum ξ) hc.le).trans
      ((hpos ξ).trans ((le_abs_self _).trans (abs_ip_le _ _)))
  rcases (norm_nonneg ξ).eq_or_lt with h | h
  · rw [← h]; positivity
  · rw [div_mul_eq_mul_div, le_div_iff₀ hc]
    nlinarith

end Algebra

/-! ### Periodic functions and the unit cube -/

variable {ι : Type*} [Fintype ι]

/-- The integer translation vector `k ∈ ℤ^ι ⊂ ℝ^ι`. -/
def zvec (k : ι → ℤ) : ι → ℝ := fun i => (k i : ℝ)

/-- `ℤ^ι`-periodicity. -/
def IsZPeriodic {α : Type*} (f : (ι → ℝ) → α) : Prop :=
  ∀ (k : ι → ℤ) (x : ι → ℝ), f (x + zvec k) = f x

/-- The half-open cube `Π (a_i, a_i + 1]`. -/
def boxIoc (a : ι → ℝ) : Set (ι → ℝ) := {x | ∀ i, x i ∈ Ioc (a i) (a i + 1)}

theorem boxIoc_eq_pi (a : ι → ℝ) : boxIoc a = univ.pi fun i => Ioc (a i) (a i + 1) := by
  ext x; simp [boxIoc]

theorem measurableSet_boxIoc (a : ι → ℝ) : MeasurableSet (boxIoc a) := by
  rw [boxIoc_eq_pi]; exact MeasurableSet.univ_pi fun _ => measurableSet_Ioc

theorem boxIoc_ae_eq (a : ι → ℝ) : boxIoc a =ᵐ[volume] Icc a (a + 1) := by
  rw [boxIoc_eq_pi, volume_pi]
  exact Measure.univ_pi_Ioc_ae_eq_Icc (f := a) (g := a + 1)

theorem IsZPeriodic.comp {α β : Type*} {f : (ι → ℝ) → α} (hf : IsZPeriodic f) (g : α → β) :
    IsZPeriodic (g ∘ f) := fun k x => by simp [hf k x]

theorem IsZPeriodic.comp_add {α : Type*} {f : (ι → ℝ) → α} (hf : IsZPeriodic f) (v : ι → ℝ) :
    IsZPeriodic (fun x => f (x + v)) := fun k x => by
  show f (x + zvec k + v) = f (x + v)
  rw [add_right_comm, hf]

theorem IsZPeriodic.sub_zvec {α : Type*} {f : (ι → ℝ) → α} (hf : IsZPeriodic f) (k : ι → ℤ)
    (x : ι → ℝ) : f (x - zvec k) = f x := by
  rw [← hf k (x - zvec k), sub_add_cancel]

theorem IsZPeriodic.apply_fract {α : Type*} {f : (ι → ℝ) → α} (hf : IsZPeriodic f)
    (x : ι → ℝ) : f (fun i => Int.fract (x i)) = f x := by
  have : (fun i => Int.fract (x i)) = x - zvec (fun i => ⌊x i⌋) := by
    funext i; rfl
  rw [this, hf.sub_zvec]

/-- The function on `𝕋^ι` induced by a periodic function. -/
def descend {α : Type*} (f : (ι → ℝ) → α) : UnitAddTorus ι → α :=
  fun t => f (fun i => (AddCircle.equivIco (1 : ℝ) 0 (t i) : ℝ))

theorem descend_mk {α : Type*} {f : (ι → ℝ) → α} (hf : IsZPeriodic f) (x : ι → ℝ) :
    descend f (fun i => (x i : UnitAddCircle)) = f x := by
  unfold descend
  have : (fun i => (AddCircle.equivIco (1 : ℝ) 0 ((x i : ℝ) : UnitAddCircle) : ℝ)) =
      fun i => Int.fract (x i) := by
    funext i
    rw [AddCircle.coe_equivIco_mk_apply]
    simp
  rw [this, hf.apply_fract]

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

theorem lintegral_boxIoc_eq {f : (ι → ℝ) → ℝ≥0∞} (hf : IsZPeriodic f) (a b : ι → ℝ) :
    ∫⁻ x in boxIoc a, f x = ∫⁻ x in boxIoc b, f x := by
  have ha := UnitAddTorus.lintegral_preimage (descend f) a
  have hb := UnitAddTorus.lintegral_preimage (descend f) b
  simp only [descend_mk hf] at ha hb
  exact ha.symm.trans hb

theorem integral_boxIoc_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : (ι → ℝ) → E} (hf : IsZPeriodic f) (a b : ι → ℝ) :
    ∫ x in boxIoc a, f x = ∫ x in boxIoc b, f x := by
  have ha := UnitAddTorus.integral_preimage (descend f) a
  have hb := UnitAddTorus.integral_preimage (descend f) b
  simp only [descend_mk hf] at ha hb
  exact ha.symm.trans hb

theorem integral_boxIoc_comp_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : (ι → ℝ) → E) (a v : ι → ℝ) :
    ∫ x in boxIoc a, f (x + v) = ∫ x in boxIoc (a + v), f x := by
  rw [← integral_indicator (measurableSet_boxIoc a),
    ← integral_indicator (measurableSet_boxIoc (a + v))]
  rw [← integral_add_right_eq_self (μ := volume) (fun x => (boxIoc (a + v)).indicator f x) v]
  congr 1
  funext x
  have hmem : x + v ∈ boxIoc (a + v) ↔ x ∈ boxIoc a := by
    simp only [boxIoc, mem_ofPred_eq, mem_Ioc, Pi.add_apply]
    refine forall_congr' fun i => ?_
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  by_cases hx : x ∈ boxIoc a
  · rw [indicator_of_mem hx, indicator_of_mem (hmem.mpr hx)]
  · rw [indicator_of_notMem hx, indicator_of_notMem (fun h => hx (hmem.mp h))]

theorem lintegral_boxIoc_comp_add (f : (ι → ℝ) → ℝ≥0∞) (a v : ι → ℝ) :
    ∫⁻ x in boxIoc a, f (x + v) = ∫⁻ x in boxIoc (a + v), f x := by
  rw [← lintegral_indicator (measurableSet_boxIoc a),
    ← lintegral_indicator (measurableSet_boxIoc (a + v))]
  rw [← lintegral_add_right_eq_self (μ := volume) (fun x => (boxIoc (a + v)).indicator f x) v]
  congr 1
  funext x
  have hmem : x + v ∈ boxIoc (a + v) ↔ x ∈ boxIoc a := by
    simp only [boxIoc, mem_ofPred_eq, mem_Ioc, Pi.add_apply]
    refine forall_congr' fun i => ?_
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  by_cases hx : x ∈ boxIoc a
  · rw [indicator_of_mem hx, indicator_of_mem (hmem.mpr hx)]
  · rw [indicator_of_notMem hx, indicator_of_notMem (fun h => hx (hmem.mp h))]

/-- The integral over the closed unit cube equals the integral over `(0,1]^ι`. -/
theorem integral_Icc_eq_boxIoc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : (ι → ℝ) → E) : ∫ x in Icc (0 : ι → ℝ) 1, f x = ∫ x in boxIoc 0, f x := by
  have h := boxIoc_ae_eq (0 : ι → ℝ)
  rw [zero_add] at h
  exact setIntegral_congr_set h.symm

theorem lintegral_Icc_eq_boxIoc (f : (ι → ℝ) → ℝ≥0∞) :
    ∫⁻ x in Icc (0 : ι → ℝ) 1, f x = ∫⁻ x in boxIoc 0, f x := by
  have h := boxIoc_ae_eq (0 : ι → ℝ)
  rw [zero_add] at h
  exact setLIntegral_congr h.symm

/-- **Translation invariance** of the cube integral of a periodic function. -/
theorem integral_cube_comp_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : (ι → ℝ) → E} (hf : IsZPeriodic f) (v : ι → ℝ) :
    ∫ x in Icc (0 : ι → ℝ) 1, f (x + v) = ∫ x in Icc (0 : ι → ℝ) 1, f x := by
  rw [integral_Icc_eq_boxIoc, integral_Icc_eq_boxIoc, integral_boxIoc_comp_add, zero_add,
    integral_boxIoc_eq hf v 0]

/-- The cube integral of a periodic function over any translate `Π (a_i, a_i+1]`. -/
theorem lintegral_boxIoc_eq_cube {f : (ι → ℝ) → ℝ≥0∞} (hf : IsZPeriodic f) (a : ι → ℝ) :
    ∫⁻ x in boxIoc a, f x = ∫⁻ x in Icc (0 : ι → ℝ) 1, f x := by
  rw [lintegral_Icc_eq_boxIoc, lintegral_boxIoc_eq hf a 0]

theorem volume_cube : volume (Icc (0 : ι → ℝ) 1) = 1 := by
  rw [Real.volume_Icc_pi]; simp

instance : IsFiniteMeasure (volume.restrict (Icc (0 : ι → ℝ) 1)) :=
  isFiniteMeasure_restrict.mpr (by rw [volume_cube]; exact ENNReal.one_ne_top)

theorem integrableOn_cube_of_continuousOn {E : Type*} [NormedAddCommGroup E] {f : (ι → ℝ) → E}
    (hf : ContinuousOn f (Icc 0 1)) : IntegrableOn f (Icc (0 : ι → ℝ) 1) :=
  hf.integrableOn_compact isCompact_Icc

/-- Periodic continuous functions are bounded. -/
theorem IsZPeriodic.exists_bound {E : Type*} [NormedAddCommGroup E] {f : (ι → ℝ) → E}
    (hf : IsZPeriodic f) (hc : Continuous f) : ∃ C, 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ι → ℝ)) (b := 1)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  rw [← hf.apply_fract x]
  refine (hC _ ⟨fun i => Int.fract_nonneg _, fun i => (Int.fract_lt_one _).le⟩).trans
    (le_max_left _ _)

theorem IsZPeriodic.fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : (ι → ℝ) → E} (hf : IsZPeriodic f) : IsZPeriodic (fderiv ℝ f) := fun k x => by
  have h : (fun z => f (z + zvec k)) = f := funext (hf k)
  rw [← fderiv_comp_add_right, h]

variable [DecidableEq ι]

theorem IsZPeriodic.pd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : (ι → ℝ) → E} (hf : IsZPeriodic f) (j : ι) : IsZPeriodic (pd f j) := fun k x => by
  unfold SobolevOpen.pd
  rw [hf.fderiv k x]

/-! ### Difference quotients -/

/-- The unit vector `e_j`. -/
abbrev ev (j : ι) : ι → ℝ := Pi.single j 1

theorem norm_ev (j : ι) : ‖(ev j : ι → ℝ)‖ = 1 := by
  rw [ev, Pi.norm_single, norm_one]

theorem norm_smul_ev (s : ℝ) (j : ι) : ‖s • (ev j : ι → ℝ)‖ = |s| := by
  rw [norm_smul, norm_ev, mul_one, Real.norm_eq_abs]

/-- The derivative of `s ↦ f (x + s e_j)`. -/
theorem hasDerivAt_line {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : (ι → ℝ) → E} {x : ι → ℝ} (j : ι) {s : ℝ}
    (hf : DifferentiableAt ℝ f (x + s • ev j)) :
    HasDerivAt (fun s : ℝ => f (x + s • ev j)) (pd f j (x + s • ev j)) s := by
  have hl : HasDerivAt (fun s : ℝ => x + s • (ev j : ι → ℝ)) (ev j) s := by
    simpa using ((hasDerivAt_id s).smul_const (ev j : ι → ℝ)).const_add x
  exact hf.hasFDerivAt.comp_hasDerivAt s hl

/-- Global Lipschitz bound along `e_j` for a `C¹` periodic function. -/
theorem exists_line_lipschitz {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : (ι → ℝ) → E} (hf : ContDiff ℝ 1 f) (hper : IsZPeriodic f) :
    ∃ C, 0 ≤ C ∧ ∀ x y, ‖f y - f x‖ ≤ C * ‖y - x‖ := by
  obtain ⟨C, hC0, hC⟩ := hper.fderiv.exists_bound (hf.continuous_fderiv one_ne_zero)
  refine ⟨C, hC0, fun x y => ?_⟩
  exact convex_univ.norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => hf.differentiable one_ne_zero z) (fun z _ => hC z) (mem_univ x) (mem_univ y)

/-- Dominated convergence on the unit cube with a constant bound. -/
theorem tendsto_integral_cube {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {l : Filter ℝ} [l.IsCountablyGenerated] {F : ℝ → (ι → ℝ) → E} {G : (ι → ℝ) → E} (C : ℝ)
    (hmeas : ∀ᶠ s in l, AEStronglyMeasurable (F s) (volume.restrict (Icc (0 : ι → ℝ) 1)))
    (hb : ∀ᶠ s in l, ∀ x, ‖F s x‖ ≤ C) (hlim : ∀ x, Tendsto (fun s => F s x) l (𝓝 (G x))) :
    Tendsto (fun s => ∫ x in Icc (0 : ι → ℝ) 1, F s x) l (𝓝 (∫ x in Icc (0 : ι → ℝ) 1, G x)) :=
  tendsto_integral_filter_of_dominated_convergence (fun _ => C) hmeas
    (hb.mono fun s hs => Eventually.of_forall hs) (integrable_const C)
    (Eventually.of_forall hlim)

/-- **Integration by parts on the torus**: `∫_{[0,1]^ι} ∂_j h = 0` for `C¹` periodic `h`. -/
theorem integral_pd_eq_zero {h : (ι → ℝ) → ℝ} (hh : ContDiff ℝ 1 h) (hper : IsZPeriodic h)
    (j : ι) : ∫ x in Icc (0 : ι → ℝ) 1, pd h j x = 0 := by
  obtain ⟨C, hC0, hC⟩ := exists_line_lipschitz hh hper
  have hcont : Continuous h := hh.continuous
  have hlim : Tendsto (fun s : ℝ => ∫ x in Icc (0 : ι → ℝ) 1, s⁻¹ • (h (x + s • ev j) - h x))
      (𝓝[≠] 0) (𝓝 (∫ x in Icc (0 : ι → ℝ) 1, pd h j x)) := by
    refine tendsto_integral_cube C (Eventually.of_forall fun s =>
      (Continuous.aestronglyMeasurable (by fun_prop))) ?_ fun x => ?_
    · filter_upwards [self_mem_nhdsWithin] with s hs x
      have := hC x (x + s • ev j)
      rw [add_sub_cancel_left, norm_smul_ev] at this
      rw [norm_smul, Real.norm_eq_abs, abs_inv]
      calc |s|⁻¹ * ‖h (x + s • ev j) - h x‖ ≤ |s|⁻¹ * (C * |s|) := by gcongr
        _ = C := by
          rw [← mul_assoc, mul_comm (|s|⁻¹) C, mul_assoc, inv_mul_cancel₀ (abs_pos.mpr hs).ne',
            mul_one]
    · have hd := hasDerivAt_line (f := h) (x := x) j (s := 0)
        ((hh.differentiable one_ne_zero) _)
      simp only [zero_smul, add_zero] at hd
      have := hd.tendsto_slope_zero
      simpa only [zero_add, zero_smul, add_zero] using this
  have hzero : ∀ s : ℝ, ∫ x in Icc (0 : ι → ℝ) 1, s⁻¹ • (h (x + s • ev j) - h x) = 0 := by
    intro s
    rw [integral_smul, integral_sub
      (integrableOn_cube_of_continuousOn (by fun_prop))
      (integrableOn_cube_of_continuousOn (by fun_prop)),
      integral_cube_comp_add hper, sub_self, smul_zero]
  simp only [hzero] at hlim
  exact tendsto_nhds_unique tendsto_const_nhds hlim |>.symm

/-- The derivative of `s ↦ f (x + s v)` in any direction. -/
theorem hasDerivAt_dir {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : (ι → ℝ) → E} {x v : ι → ℝ} {s : ℝ} (hf : DifferentiableAt ℝ f (x + s • v)) :
    HasDerivAt (fun s : ℝ => f (x + s • v)) (fderiv ℝ f (x + s • v) v) s := by
  have hl : HasDerivAt (fun s : ℝ => x + s • v) v s := by
    simpa using ((hasDerivAt_id s).smul_const v).const_add x
  exact hf.hasFDerivAt.comp_hasDerivAt s hl

/-- Forward difference quotients converge to the partial derivative. -/
theorem tendsto_fwd_quot {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : (ι → ℝ) → E} (hf : Differentiable ℝ f) (x : ι → ℝ) (j : ι) :
    Tendsto (fun s : ℝ => s⁻¹ • (f (x + s • ev j) - f x)) (𝓝[≠] 0) (𝓝 (pd f j x)) := by
  have hd := hasDerivAt_dir (f := f) (x := x) (v := ev j) (s := 0) (hf _)
  simp only [zero_smul, add_zero] at hd
  have h := hd.tendsto_slope_zero
  simp only [zero_add, zero_smul, add_zero] at h
  exact h

/-- Backward difference quotients converge to the partial derivative. -/
theorem tendsto_bwd_quot {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : (ι → ℝ) → E} (hf : Differentiable ℝ f) (x : ι → ℝ) (j : ι) :
    Tendsto (fun s : ℝ => s⁻¹ • (f x - f (x - s • ev j))) (𝓝[≠] 0) (𝓝 (pd f j x)) := by
  have hd := hasDerivAt_dir (f := f) (x := x) (v := -ev j) (s := 0) (hf _)
  simp only [zero_smul, add_zero] at hd
  have h := hd.tendsto_slope_zero.neg
  simp only [zero_add, zero_smul, add_zero, map_neg, neg_neg] at h
  refine h.congr fun s => ?_
  simp only [smul_neg, ← sub_eq_add_neg, smul_sub, neg_sub]

theorem continuous_ip_mv {N : Type*} [Fintype N] (v : N → ℂ) :
    Continuous fun p : (N → N → ℂ) × (N → ℂ) => ip (mv p.1 p.2) v := by
  unfold ip mv
  fun_prop

theorem tendsto_ip_mv {N : Type*} [Fintype N] {l : Filter ℝ} {B : ℝ → N → N → ℂ}
    {u : ℝ → N → ℂ} {B0 : N → N → ℂ} {u0 : N → ℂ} (v : N → ℂ) (hB : Tendsto B l (𝓝 B0))
    (hu : Tendsto u l (𝓝 u0)) :
    Tendsto (fun s => ip (mv (B s) (u s)) v) l (𝓝 (ip (mv B0 u0) v)) := by
  have h := (continuous_ip_mv v).tendsto (B0, u0)
  have h2 := hB.prodMk_nhds hu
  have h3 := h.comp h2
  exact h3

theorem continuous_ip_mv' {N : Type*} [Fintype N] {B : (ι → ℝ) → N → N → ℂ}
    {u v : (ι → ℝ) → N → ℂ} (hB : Continuous B) (hu : Continuous u) (hv : Continuous v) :
    Continuous fun x => ip (mv (B x) (u x)) (v x) := by
  unfold ip mv
  fun_prop

/-- **Lipschitz commutator (Friedrichs) lemma on the torus.**  For a Hermitian, `L`-Lipschitz,
periodic matrix field `A` and a `C¹` periodic vector field `f`,
`-2 ∫_{[0,1]^ι} Re⟨A ∂_j f, f⟩ ≤ |N|² L ∫_{[0,1]^ι} ‖f‖²`.  (For differentiable `A` this is
`2∫Re⟨A∂_jf,f⟩ = -∫⟨(∂_jA)f,f⟩`; here only the Lipschitz constant of `A` enters, through the
symmetric difference quotients and the translation invariance of the cube integral.) -/
theorem neg_two_integral_ip_pd_le {N : Type*} [Fintype N] {A : (ι → ℝ) → N → N → ℂ}
    {f : (ι → ℝ) → N → ℂ} {L : ℝ≥0} (j : ι) (hf : ContDiff ℝ 1 f) (hfper : IsZPeriodic f)
    (hAper : IsZPeriodic A) (hH : ∀ x i k, A x k i = star (A x i k)) (hL : LipschitzWith L A) :
    -(2 * ∫ x in Icc (0 : ι → ℝ) 1, ip (mv (A x) (pd f j x)) (f x)) ≤
      (Fintype.card N : ℝ) ^ 2 * L * ∫ x in Icc (0 : ι → ℝ) 1, ‖f x‖ ^ 2 := by
  set κ : ℝ := (Fintype.card N : ℝ) ^ 2 with hκ
  have hκ0 : 0 ≤ κ := by positivity
  have hfc : Continuous f := hf.continuous
  have hAc : Continuous A := hL.continuous
  have hfd : Differentiable ℝ f := hf.differentiable one_ne_zero
  obtain ⟨Cf, hCf0, hCf⟩ := hfper.exists_bound hfc
  obtain ⟨CA, hCA0, hCA⟩ := hAper.exists_bound hAc
  obtain ⟨C1, hC10, hC1⟩ := exists_line_lipschitz hf hfper
  set D := ∫ x in Icc (0 : ι → ℝ) 1, ip (mv (A x) (pd f j x)) (f x) with hD
  set M := ∫ x in Icc (0 : ι → ℝ) 1, ‖f x‖ ^ 2 with hM
  have hint : ∀ g : (ι → ℝ) → ℝ, Continuous g → IntegrableOn g (Icc (0 : ι → ℝ) 1) :=
    fun g hg => integrableOn_cube_of_continuousOn hg.continuousOn
  have hcA : ∀ s : ℝ, Continuous fun x => A (x - s • ev j) := fun s => hAc.comp (by fun_prop)
  have hcf : ∀ s : ℝ, Continuous fun x => f (x - s • ev j) := fun s => hfc.comp (by fun_prop)
  have hcf' : ∀ s : ℝ, Continuous fun x => f (x + s • ev j) := fun s => hfc.comp (by fun_prop)
  -- the key identity, for every `s`
  have hkey : ∀ s : ℝ,
      (∫ x in Icc (0 : ι → ℝ) 1, ip (mv (A x) (f (x + s • ev j) - f x)) (f x)) +
        ∫ x in Icc (0 : ι → ℝ) 1, ip (mv (A (x - s • ev j)) (f x - f (x - s • ev j))) (f x) =
      ∫ x in Icc (0 : ι → ℝ) 1, ip (mv (A (x - s • ev j) - A x) (f x)) (f x) := by
    intro s
    -- translation: `∫ a = ∫ d`
    have htr : ∫ x in Icc (0 : ι → ℝ) 1, ip (mv (A x) (f (x + s • ev j))) (f x) =
        ∫ x in Icc (0 : ι → ℝ) 1, ip (mv (A (x - s • ev j)) (f (x - s • ev j))) (f x) := by
      have hper : IsZPeriodic fun x => ip (mv (A x) (f (x + s • ev j))) (f x) := fun k x => by
        show ip (mv (A (x + zvec k)) (f (x + zvec k + s • ev j))) (f (x + zvec k)) = _
        rw [hAper, hfper, add_right_comm, hfper]
      rw [← integral_cube_comp_add hper (-(s • ev j))]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [← sub_eq_add_neg, sub_add_cancel]
      rw [ip_mv_herm (hH _), ip_comm]
    simp only [mv_sub, mv_sub_left, ip_sub_left]
    rw [integral_sub (hint _ (continuous_ip_mv' hAc (hcf' s) hfc))
        (hint _ (continuous_ip_mv' hAc hfc hfc)),
      integral_sub (hint _ (continuous_ip_mv' (hcA s) hfc hfc))
        (hint _ (continuous_ip_mv' (hcA s) (hcf s) hfc)),
      integral_sub (hint _ (continuous_ip_mv' (hcA s) hfc hfc))
        (hint _ (continuous_ip_mv' hAc hfc hfc)), htr]
    ring
  -- lower bound of the commutator term
  have hlow : ∀ s : ℝ, 0 < s → -(κ * L * s * M) ≤
      ∫ x in Icc (0 : ι → ℝ) 1, ip (mv (A (x - s • ev j) - A x) (f x)) (f x) := by
    intro s hs
    rw [hM, ← integral_const_mul, ← integral_neg]
    refine integral_mono (hint _ (by fun_prop))
      (hint _ (continuous_ip_mv' ((hcA s).sub hAc) hfc hfc)) fun x => ?_
    have h1 := abs_ip_mv_le (A (x - s • ev j) - A x) (f x) (f x)
    rw [← ip_mv_herm] at h1
    · have h2 : ‖A (x - s • ev j) - A x‖ ≤ L * s := by
        have := hL.norm_sub_le (x - s • ev j) x
        rwa [sub_sub_cancel_left, norm_neg, norm_smul_ev, abs_of_pos hs] at this
      have h3 : |ip (mv (A (x - s • ev j) - A x) (f x)) (f x)| ≤ κ * (L * s) * ‖f x‖ ^ 2 := by
        rw [← hκ] at h1
        calc _ ≤ _ := h1
          _ ≤ κ * (L * s) * (‖f x‖ * ‖f x‖) := by gcongr
          _ = _ := by ring
      have := neg_abs_le (ip (mv (A (x - s • ev j) - A x) (f x)) (f x))
      nlinarith
    · intro i k
      rw [Pi.sub_apply, Pi.sub_apply, Pi.sub_apply, Pi.sub_apply, star_sub, ← hH, ← hH]
  -- the two difference-quotient limits
  have hbound : ∀ x (s : ℝ), s ≠ 0 → ‖s⁻¹ • (f (x + s • ev j) - f x)‖ ≤ C1 ∧
      ‖s⁻¹ • (f x - f (x - s • ev j))‖ ≤ C1 := by
    intro x s hs
    have hs' : 0 < |s| := abs_pos.mpr hs
    constructor
    · have := hC1 x (x + s • ev j)
      rw [add_sub_cancel_left, norm_smul_ev] at this
      rw [norm_smul, Real.norm_eq_abs, abs_inv]
      calc |s|⁻¹ * ‖f (x + s • ev j) - f x‖ ≤ |s|⁻¹ * (C1 * |s|) := by gcongr
        _ = C1 := by
          rw [← mul_assoc, mul_comm (|s|⁻¹) C1, mul_assoc, inv_mul_cancel₀ hs'.ne', mul_one]
    · have := hC1 (x - s • ev j) x
      rw [sub_sub_cancel, norm_smul_ev] at this
      rw [norm_smul, Real.norm_eq_abs, abs_inv]
      calc |s|⁻¹ * ‖f x - f (x - s • ev j)‖ ≤ |s|⁻¹ * (C1 * |s|) := by gcongr
        _ = C1 := by
          rw [← mul_assoc, mul_comm (|s|⁻¹) C1, mul_assoc, inv_mul_cancel₀ hs'.ne', mul_one]
  have hB : ∀ (B : N → N → ℂ) (u v : N → ℂ), ‖B‖ ≤ CA → ‖u‖ ≤ C1 → ‖v‖ ≤ Cf →
      ‖ip (mv B u) v‖ ≤ κ * CA * (C1 * Cf) := by
    intro B u v hBn hu hv
    rw [Real.norm_eq_abs, ip_comm]
    refine (abs_ip_mv_le B v u).trans ?_
    calc κ * ‖B‖ * (‖v‖ * ‖u‖) ≤ κ * CA * (Cf * C1) := by gcongr
      _ = _ := by ring
  have hlimI : Tendsto (fun s : ℝ => ∫ x in Icc (0 : ι → ℝ) 1,
      ip (mv (A x) (s⁻¹ • (f (x + s • ev j) - f x))) (f x)) (𝓝[≠] 0) (𝓝 D) := by
    refine tendsto_integral_cube (κ * CA * (C1 * Cf)) (Eventually.of_forall fun s => by
      have hq : Continuous fun x => s⁻¹ • (f (x + s • ev j) - f x) := by fun_prop
      exact (continuous_ip_mv' hAc hq hfc).aestronglyMeasurable) ?_ fun x => ?_
    · filter_upwards [self_mem_nhdsWithin] with s hs x
      exact hB _ _ _ (hCA x) (hbound x s hs).1 (hCf x)
    · exact tendsto_ip_mv (f x) tendsto_const_nhds (tendsto_fwd_quot hfd x j)
  have hlimJ : Tendsto (fun s : ℝ => ∫ x in Icc (0 : ι → ℝ) 1,
      ip (mv (A (x - s • ev j)) (s⁻¹ • (f x - f (x - s • ev j)))) (f x)) (𝓝[≠] 0) (𝓝 D) := by
    refine tendsto_integral_cube (κ * CA * (C1 * Cf)) (Eventually.of_forall fun s => by
      have hq : Continuous fun x => s⁻¹ • (f x - f (x - s • ev j)) := by fun_prop
      exact (continuous_ip_mv' (hcA s) hq hfc).aestronglyMeasurable) ?_ fun x => ?_
    · filter_upwards [self_mem_nhdsWithin] with s hs x
      exact hB _ _ _ (hCA _) (hbound x s hs).2 (hCf x)
    · have hA' : Tendsto (fun s : ℝ => A (x - s • ev j)) (𝓝[≠] 0) (𝓝 (A x)) := by
        have : Continuous fun s : ℝ => A (x - s • ev j) := hAc.comp (by fun_prop)
        have h0 := this.tendsto 0
        simp only [zero_smul, sub_zero] at h0
        exact h0.mono_left nhdsWithin_le_nhds
      exact tendsto_ip_mv (f x) hA' (tendsto_bwd_quot hfd x j)
  have hsum := (hlimI.add hlimJ).mono_left (nhdsGT_le_nhdsNE (0 : ℝ))
  have hge : ∀ᶠ s in 𝓝[>] (0 : ℝ), -(κ * L * M) ≤
      (∫ x in Icc (0 : ι → ℝ) 1, ip (mv (A x) (s⁻¹ • (f (x + s • ev j) - f x))) (f x)) +
      ∫ x in Icc (0 : ι → ℝ) 1, ip (mv (A (x - s • ev j)) (s⁻¹ • (f x - f (x - s • ev j))))
        (f x) := by
    filter_upwards [self_mem_nhdsWithin] with s (hs : 0 < s)
    simp only [mv_smul, ip_smul_left, integral_const_mul]
    rw [← mul_add, hkey s]
    have := hlow s hs
    calc -(κ * L * M) = s⁻¹ * (-(κ * L * s * M)) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left this (inv_pos.mpr hs).le
  have := ge_of_tendsto hsum hge
  linarith

/-- `Re` of a complex derivative. -/
theorem _root_.HasDerivAt.complex_re {f : ℝ → ℂ} {f' : ℂ} {x : ℝ} (h : HasDerivAt f f' x) :
    HasDerivAt (fun x => (f x).re) f'.re x :=
  Complex.reCLM.hasFDerivAt.comp_hasDerivAt x h

/-- **Interpolation of `H¹` between `L²` and `H²` on the torus.**  For a `C²` periodic
`g : ℝ^ι → ℂ`, `∫ |∂_j g|² = -Re ∫ conj(g) ∂_j∂_j g`, hence for every `λ > 0`,
`∫ |∂_j g|² ≤ (λ/2) ∫ |∂_j∂_j g|² + (2λ)⁻¹ ∫ |g|²`. -/
theorem integral_norm_pd_sq_le {g : (ι → ℝ) → ℂ} (hg : ContDiff ℝ 2 g) (hper : IsZPeriodic g)
    (j : ι) {lam : ℝ} (hlam : 0 < lam) :
    ∫ x in Icc (0 : ι → ℝ) 1, ‖pd g j x‖ ^ 2 ≤
      lam / 2 * (∫ x in Icc (0 : ι → ℝ) 1, ‖pd (pd g j) j x‖ ^ 2) +
        (2 * lam)⁻¹ * ∫ x in Icc (0 : ι → ℝ) 1, ‖g x‖ ^ 2 := by
  have hpd : ContDiff ℝ 1 (pd g j) := by
    unfold SobolevOpen.pd
    exact (hg.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hgd : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hpdd : Differentiable ℝ (pd g j) := hpd.differentiable one_ne_zero
  set h : (ι → ℝ) → ℝ := fun x => (star (g x) * pd g j x).re with hh
  have hhC : ContDiff ℝ 1 h := by
    have hs : ContDiff ℝ 1 fun x => star (g x) := by
      have := Complex.conjCLE.contDiff.comp (hg.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2))
      convert this using 1
      funext x
      simp [Complex.star_def]
    have : ContDiff ℝ 1 fun x => star (g x) * pd g j x := hs.mul hpd
    exact Complex.reCLM.contDiff.comp this
  have hhper : IsZPeriodic h := fun k x => by
    simp only [hh, hper k x, hper.pd j k x]
  have hpdh : ∀ x, pd h j x = ‖pd g j x‖ ^ 2 + (star (g x) * pd (pd g j) j x).re := by
    intro x
    have h1 := hasDerivAt_line (f := h) (x := x) j (s := 0) ((hhC.differentiable one_ne_zero) _)
    have h2 : HasDerivAt (fun s : ℝ => h (x + s • ev j))
        ((star (pd g j x) * pd g j x + star (g x) * pd (pd g j) j x).re) 0 := by
      have hG := hasDerivAt_line (f := g) (x := x) j (s := 0) (hgd _)
      have hP := hasDerivAt_line (f := pd g j) (x := x) j (s := 0) (hpdd _)
      simp only [zero_smul, add_zero] at hG hP
      have := (hG.star.mul hP).complex_re
      simp only [zero_smul, add_zero] at this
      exact this
    simp only [zero_smul, add_zero] at h1
    rw [h1.unique h2, Complex.add_re]
    congr 1
    rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    norm_cast
  have hzero := integral_pd_eq_zero hhC hhper j
  have hcg : Continuous g := hg.continuous
  have hcp : Continuous (pd g j) := hpd.continuous
  have hcpp : Continuous (pd (pd g j) j) := by
    unfold SobolevOpen.pd
    exact (hpd.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hint : ∀ u : (ι → ℝ) → ℝ, Continuous u → IntegrableOn u (Icc (0 : ι → ℝ) 1) :=
    fun u hu => integrableOn_cube_of_continuousOn hu.continuousOn
  simp only [hpdh] at hzero
  rw [integral_add (hint _ (by fun_prop)) (hint _ (by fun_prop))] at hzero
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hint _ (by fun_prop))
    (hint _ (by fun_prop))]
  have hre : ∫ x in Icc (0 : ι → ℝ) 1, ‖pd g j x‖ ^ 2 =
      ∫ x in Icc (0 : ι → ℝ) 1, -(star (g x) * pd (pd g j) j x).re := by
    rw [integral_neg]; linarith
  rw [hre]
  refine integral_mono (hint _ (by fun_prop)) (hint _ (by fun_prop)) fun x => ?_
  have h1 : -(star (g x) * pd (pd g j) j x).re ≤ ‖g x‖ * ‖pd (pd g j) j x‖ := by
    refine (neg_le_abs _).trans ((Complex.abs_re_le_norm _).trans ?_)
    rw [norm_mul, norm_star]
  have h2 : ‖g x‖ * ‖pd (pd g j) j x‖ ≤
      lam / 2 * ‖pd (pd g j) j x‖ ^ 2 + (2 * lam)⁻¹ * ‖g x‖ ^ 2 := by
    have hsq : 0 ≤ (lam * ‖pd (pd g j) j x‖ - ‖g x‖) ^ 2 / (2 * lam) := by positivity
    have : (lam * ‖pd (pd g j) j x‖ - ‖g x‖) ^ 2 / (2 * lam) =
        lam / 2 * ‖pd (pd g j) j x‖ ^ 2 + (2 * lam)⁻¹ * ‖g x‖ ^ 2 -
          ‖g x‖ * ‖pd (pd g j) j x‖ := by
      field_simp
      ring
    linarith
  exact h1.trans h2

end RenewalGeometry.PeriodicCube
