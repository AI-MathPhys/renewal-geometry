/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.SobolevCriticalEmbedding

/-!
# Reflection extension of `W^{1,2}` functions on coordinate boxes

Generic infrastructure (no renewal notions).  For the reflection `R_{j,c}` of `ℝ^ι` across the
hyperplane `x_j = c` and an open `R`-invariant set `Ω'`, the **even reflection**

  `E u (x) = u(x)` for `x_j < c`,  `E u (x) = u(R x)` for `x_j ≥ c`

maps `W^{1,2}(Ω' ∩ {x_j < c})` into `W^{1,2}(Ω')`, the weak partials being the even reflections
of `∂_i u` for `i ≠ j` and the odd reflection of `∂_j u` (`hasWeakPartial_reflExt`).  The proof
tests against `φ ± φ∘R`, cut off by `η_k(x) = θ(k(c - x_j))`, and passes to the limit by dominated
convergence; for `i = j` the boundary term is controlled because `φ - φ∘R` vanishes on the
hyperplane (Lipschitz bound).  Iterating over the `2d` faces of a box `Q = Π (a_i, b_i)` and
multiplying by a cutoff gives a **bounded extension operator** `W^{1,2}(Q) → W^{1,2}_c(ℝ^ι)`
(`exists_extension_box`).

* `refl`, `measurePreserving_refl`, `pd_comp_refl`: the reflection and its calculus;
* `HasWeakPartial.comp_refl`: weak derivatives transform under reflections;
* `weak_halfspace_limit`: the cutoff limit `∫_{x_j<c} ∂_iψ u = -∫_{x_j<c} ψ ∂_i u` for smooth
  compactly supported `ψ` (supported in `Ω'`, and vanishing on the face when `i = j`);
* `hasWeakPartial_reflExt`, `memW12_reflExt`: the one-face extension with norm bounds;
  `MemW12.comp_refl`: `W^{1,2}` is reflection invariant (isometrically);
* `exists_ext_upper`, `exists_ext_lower`, `exists_ext_iter`: extension across the faces of a box
  `box a b = Π (a_i, b_i)`, iterated over all coordinates (to `Π (3a_i - 2b_i, 2b_i - a_i)`, norm
  factor `4^d`);
* `exists_extension_box` (**bounded extension operator**): `W^{1,2}(Q) → W^{1,2}(ℝ^ι)`,
  compactly supported in a fixed ball, equal to `u` (and to its weak gradient) on `Q`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff

noncomputable section

namespace RenewalGeometry.SobolevOpen

set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The reflection `R_{j,c}` -/

/-- The reflection of `ℝ^ι` across the hyperplane `x_j = c`. -/
def refl (j : ι) (c : ℝ) (x : ι → ℝ) : ι → ℝ := x - (2 * (x j - c)) • Pi.single j 1

theorem refl_apply_self (j : ι) (c : ℝ) (x : ι → ℝ) : refl j c x j = 2 * c - x j := by
  simp [refl]; ring

theorem refl_apply_ne {j i : ι} (h : i ≠ j) (c : ℝ) (x : ι → ℝ) : refl j c x i = x i := by
  simp [refl, Pi.single_apply, h]

theorem refl_refl (j : ι) (c : ℝ) (x : ι → ℝ) : refl j c (refl j c x) = x := by
  funext i
  by_cases h : i = j
  · subst h; rw [refl_apply_self, refl_apply_self]; ring
  · rw [refl_apply_ne h, refl_apply_ne h]

theorem refl_involutive (j : ι) (c : ℝ) : Function.Involutive (refl j c) := refl_refl j c

theorem continuous_refl (j : ι) (c : ℝ) : Continuous (refl j c) := by
  unfold refl; fun_prop

/-- The reflection as a measurable equivalence. -/
def reflEquiv (j : ι) (c : ℝ) : (ι → ℝ) ≃ᵐ (ι → ℝ) where
  toFun := refl j c
  invFun := refl j c
  left_inv := refl_refl j c
  right_inv := refl_refl j c
  measurable_toFun := (continuous_refl j c).measurable
  measurable_invFun := (continuous_refl j c).measurable

theorem measurePreserving_refl (j : ι) (c : ℝ) :
    MeasurePreserving (refl j c) (volume : Measure (ι → ℝ)) volume := by
  let f : ι → ℝ → ℝ := fun i t => if i = j then 2 * c - t else t
  have hf : ∀ i, MeasurePreserving (f i) volume volume := by
    intro i
    by_cases h : i = j
    · simp only [f, h, if_true]
      have h1 := Measure.measurePreserving_sub_left (volume : Measure ℝ) (2 * c)
      exact h1
    · simp only [f, h, if_false]; exact MeasurePreserving.id volume
  have hp := measurePreserving_pi (fun _ : ι => (volume : Measure ℝ))
    (fun _ : ι => (volume : Measure ℝ)) hf
  have e : (fun (a : ι → ℝ) (i : ι) => f i (a i)) = refl j c := by
    funext a i
    by_cases h : i = j
    · subst h; simp [f, refl_apply_self]
    · simp [f, h, refl_apply_ne h]
  rw [e] at hp
  simpa [volume_pi] using hp

/-- Change of variables under the reflection. -/
theorem integral_comp_refl {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (j : ι) (c : ℝ)
    (f : (ι → ℝ) → F) : ∫ x, f (refl j c x) = ∫ x, f x :=
  (measurePreserving_refl j c).integral_comp (reflEquiv j c).measurableEmbedding f

theorem integrable_comp_refl_iff {F : Type*} [NormedAddCommGroup F] (j : ι) (c : ℝ)
    {f : (ι → ℝ) → F} : Integrable (fun x => f (refl j c x)) ↔ Integrable f :=
  (measurePreserving_refl j c).integrable_comp_emb (reflEquiv j c).measurableEmbedding

/-- The linear part of the reflection. -/
def reflLin (j : ι) : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  ContinuousLinearMap.id ℝ (ι → ℝ) -
    (2 : ℝ) • (ContinuousLinearMap.smulRight (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) j) (Pi.single j 1))

theorem hasFDerivAt_refl (j : ι) (c : ℝ) (x : ι → ℝ) :
    HasFDerivAt (refl j c) (reflLin j) x := by
  have h1 : HasFDerivAt (fun x : ι → ℝ => (2 * (x j - c)) • (Pi.single j 1 : ι → ℝ))
      ((2 : ℝ) • (ContinuousLinearMap.smulRight (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) j)
        (Pi.single j 1))) x := by
    have h2 : (fun x : ι → ℝ => (2 * (x j - c)) • (Pi.single j 1 : ι → ℝ)) =
        fun x => ((2 : ℝ) • (ContinuousLinearMap.smulRight (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) j)
          (Pi.single j 1 : ι → ℝ))) x - (2 * c) • (Pi.single j 1 : ι → ℝ) := by
      funext x; simp [sub_smul, mul_sub, smul_smul]
    rw [h2]
    exact (ContinuousLinearMap.hasFDerivAt _).sub_const _
  exact (hasFDerivAt_id x).sub h1

/-- The sign `σ_i = -1` for `i = j`, `+1` otherwise. -/
def reflSign (j i : ι) : ℝ := if i = j then -1 else 1

theorem reflSign_sq (j i : ι) : reflSign j i * reflSign j i = 1 := by
  unfold reflSign; split_ifs <;> norm_num

theorem reflLin_single (j i : ι) :
    reflLin j (Pi.single i 1) = reflSign j i • (Pi.single i 1 : ι → ℝ) := by
  funext k
  simp only [reflLin, ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, reflSign]
  by_cases h : i = j
  · subst h; by_cases hk : k = i <;> simp [Pi.single_apply, hk]; norm_num
  · by_cases hk : k = i
    · subst hk; simp [Pi.single_apply, h]
    · simp [Pi.single_apply, hk, Ne.symm h]

/-- `∂_i(φ ∘ R)(x) = σ_i ∂_iφ(R x)`. -/
theorem pd_comp_refl {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {φ : (ι → ℝ) → F}
    (hφ : Differentiable ℝ φ) (j : ι) (c : ℝ) (i : ι) (x : ι → ℝ) :
    pd (fun y => φ (refl j c y)) i x = reflSign j i • pd φ i (refl j c x) := by
  unfold pd
  have h := (hφ (refl j c x)).hasFDerivAt.comp x (hasFDerivAt_refl j c x)
  rw [show (fun y => φ (refl j c y)) = φ ∘ refl j c from rfl, h.fderiv]
  simp [ContinuousLinearMap.comp_apply, reflLin_single, map_smul]


theorem contDiff_refl (j : ι) (c : ℝ) : ContDiff ℝ ∞ (refl j c) := by
  unfold refl
  have : ContDiff ℝ ∞ fun x : ι → ℝ => (2 * (x j - c)) := by fun_prop
  exact contDiff_id.sub (this.smul contDiff_const)

/-- The reflection as a homeomorphism. -/
def reflHomeo (j : ι) (c : ℝ) : (ι → ℝ) ≃ₜ (ι → ℝ) where
  toFun := refl j c
  invFun := refl j c
  left_inv := refl_refl j c
  right_inv := refl_refl j c
  continuous_toFun := continuous_refl j c
  continuous_invFun := continuous_refl j c

/-- **Weak derivatives under a reflection**: if `g` is the weak `i`-th partial of `u` on `Ω`, then
`σ_i g ∘ R` is the weak `i`-th partial of `u ∘ R` on `R⁻¹ Ω`. -/
theorem HasWeakPartial.comp_refl {Ω : Set (ι → ℝ)} {i : ι} {u g : (ι → ℝ) → ℂ}
    (h : HasWeakPartial Ω i u g) (j : ι) (c : ℝ) :
    HasWeakPartial (refl j c ⁻¹' Ω) i (fun x => u (refl j c x))
      (fun x => ((reflSign j i : ℝ) : ℂ) * g (refl j c x)) := by
  intro φ hφ
  set ψ : (ι → ℝ) → ℝ := fun y => φ (refl j c y) with hψdef
  have hψt : IsTest Ω ψ := by
    refine ⟨hφ.smooth.comp (contDiff_refl j c), hφ.compact.comp_homeomorph (reflHomeo j c), ?_⟩
    intro y hy
    have : tsupport ψ = (reflHomeo j c) ⁻¹' tsupport φ := tsupport_comp_eq_preimage φ (reflHomeo j c)
    rw [this] at hy
    have := hφ.subset hy
    simpa [reflHomeo, refl_refl] using this
  have key := h ψ hψt
  have hpdψ : ∀ y, pd ψ i y = reflSign j i * pd φ i (refl j c y) := fun y =>
    pd_comp_refl (hφ.smooth.differentiable (by simp)) j c i y
  have e1 : ∫ x, ((pd φ i x : ℝ) : ℂ) * u (refl j c x) =
      ((reflSign j i : ℝ) : ℂ) * ∫ y, ((pd ψ i y : ℝ) : ℂ) * u y := by
    rw [← integral_const_mul, ← integral_comp_refl j c]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hpdψ, refl_refl]
    push_cast
    rw [← mul_assoc, ← mul_assoc, ← Complex.ofReal_mul, reflSign_sq, Complex.ofReal_one, one_mul]
  have e2 : ∫ x, ((φ x : ℝ) : ℂ) * (((reflSign j i : ℝ) : ℂ) * g (refl j c x)) =
      ((reflSign j i : ℝ) : ℂ) * ∫ y, ((ψ y : ℝ) : ℂ) * g y := by
    rw [← integral_const_mul, ← integral_comp_refl j c]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hψdef, refl_refl]
    ring
  rw [e1, e2, key]
  ring

/-! ### The face cutoff -/

/-- A smooth step: `0` on `(-∞, 1]`, `1` on `[2, ∞)`. -/
def halfCut (t : ℝ) : ℝ := Real.smoothTransition (t - 1)

theorem contDiff_halfCut : ContDiff ℝ ∞ halfCut :=
  (Real.smoothTransition.contDiff (n := ⊤)).comp (contDiff_id.sub contDiff_const)

theorem halfCut_eq_zero {t : ℝ} (ht : t ≤ 1) : halfCut t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem halfCut_eq_one {t : ℝ} (ht : 2 ≤ t) : halfCut t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem halfCut_nonneg (t : ℝ) : 0 ≤ halfCut t := Real.smoothTransition.nonneg _

theorem halfCut_le_one (t : ℝ) : halfCut t ≤ 1 := Real.smoothTransition.le_one _

theorem deriv_halfCut_eq_zero {t : ℝ} (ht : t < 1 ∨ 2 < t) : deriv halfCut t = 0 := by
  rcases ht with ht | ht
  · have : halfCut =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds ht] with s hs
      exact halfCut_eq_zero (le_of_lt hs)
    rw [this.deriv_eq]; simp
  · have : halfCut =ᶠ[𝓝 t] fun _ => (1 : ℝ) := by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      exact halfCut_eq_one (le_of_lt hs)
    rw [this.deriv_eq]; simp

theorem exists_bound_deriv_halfCut : ∃ C : ℝ, 0 ≤ C ∧ ∀ t, |deriv halfCut t| ≤ C := by
  have hc : Continuous (deriv halfCut) := contDiff_halfCut.continuous_deriv (by simp)
  have hcs : HasCompactSupport (deriv halfCut) := by
    refine HasCompactSupport.intro (isCompact_Icc (a := (1 : ℝ)) (b := 2)) fun t ht => ?_
    simp only [mem_Icc, not_and_or, not_le] at ht
    exact deriv_halfCut_eq_zero (ht.imp id id)
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hcs
  exact ⟨max C 0, le_max_right _ _, fun t => (by simpa using hC t : |deriv halfCut t| ≤ C).trans
    (le_max_left _ _)⟩

/-- The face cutoff `η(x) = θ(k (c - x_j))`: `0` near and beyond the face `x_j = c`, `1` at
distance `≥ 2/k` inside. -/
def faceCut (j : ι) (c k : ℝ) (x : ι → ℝ) : ℝ := halfCut (k * (c - x j))

theorem contDiff_faceCut (j : ι) (c k : ℝ) : ContDiff ℝ ∞ (faceCut j c k) := by
  unfold faceCut
  exact contDiff_halfCut.comp (by fun_prop)

theorem pd_faceCut (j : ι) (c k : ℝ) (i : ι) (x : ι → ℝ) :
    pd (faceCut j c k) i x =
      deriv halfCut (k * (c - x j)) * (-k) * (if i = j then 1 else 0) := by
  unfold pd faceCut
  have hf : HasFDerivAt (fun x : ι → ℝ => k * (c - x j))
      (k • (-(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) j))) x := by
    have h0 : HasFDerivAt (fun x : ι → ℝ => x j)
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) j) x := hasFDerivAt_apply j x
    exact (h0.const_sub c).const_mul k
  have hh := ((contDiff_halfCut.differentiable (by simp)) (k * (c - x j))).hasDerivAt
  have := hh.comp_hasFDerivAt x hf
  rw [show (fun x : ι → ℝ => halfCut (k * (c - x j))) =
    halfCut ∘ fun x : ι → ℝ => k * (c - x j) from rfl, this.fderiv]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Pi.single_apply, Ne.symm h]


/-! ### The half-space cutoff limit -/

/-- Dominated convergence for `∫ a_k w` with continuous uniformly bounded multipliers
`a_k → A` pointwise and `w ∈ L¹`. -/
theorem tendsto_integral_mul_of_bounded {w : (ι → ℝ) → ℂ} (hw : Integrable w)
    {a : ℕ → (ι → ℝ) → ℝ} {A : (ι → ℝ) → ℝ} (ha : ∀ k, Continuous (a k)) {M : ℝ}
    (hab : ∀ k x, |a k x| ≤ M) (hlim : ∀ x, Tendsto (fun k => a k x) atTop (𝓝 (A x))) :
    Tendsto (fun k => ∫ x, ((a k x : ℝ) : ℂ) * w x) atTop (𝓝 (∫ x, ((A x : ℝ) : ℂ) * w x)) := by
  refine tendsto_integral_of_dominated_convergence (fun x => M * ‖w x‖)
    (fun k => (Complex.continuous_ofReal.comp (ha k)).aestronglyMeasurable.mul hw.1)
    (hw.norm.const_mul M) (fun k => Eventually.of_forall fun x => ?_)
    (Eventually.of_forall fun x => ?_)
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hab k x) (norm_nonneg _)
  · exact ((Complex.continuous_ofReal.tendsto _).comp (hlim x)).mul_const _

theorem integrable_ofReal_mul_of_bounded {w : (ι → ℝ) → ℂ} (hw : Integrable w)
    {a : (ι → ℝ) → ℝ} (ha : Continuous a) {M : ℝ} (hab : ∀ x, |a x| ≤ M) :
    Integrable fun x => ((a x : ℝ) : ℂ) * w x :=
  hw.bdd_mul (Complex.continuous_ofReal.comp ha).aestronglyMeasurable
    (Eventually.of_forall fun x => by rw [Complex.norm_real, Real.norm_eq_abs]; exact hab x)

/-- **The half-space cutoff limit.**  Let `g` be the weak `i`-th partial of `u` on
`Ω' ∩ {x_j < c}` with `u, g ∈ L¹(ℝ^ι)`, and let `ψ` be smooth with compact support in `Ω'`
(not necessarily vanishing near the face `x_j = c`), with `|ψ(x)| ≤ L |x_j - c|` when `i = j`.
Then `∫_{x_j<c} ∂_iψ u = -∫_{x_j<c} ψ g`. -/
theorem weak_halfspace_limit {Ω' : Set (ι → ℝ)} {j : ι} {c : ℝ} {i : ι} {u g : (ι → ℝ) → ℂ}
    (h : HasWeakPartial (Ω' ∩ {x | x j < c}) i u g) (hu : Integrable u) (hg : Integrable g)
    {ψ : (ι → ℝ) → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψs : tsupport ψ ⊆ Ω') (hface : i = j → ∃ L : ℝ, ∀ x, |ψ x| ≤ L * |x j - c|) :
    ∫ x, {x : ι → ℝ | x j < c}.indicator (fun x => ((pd ψ i x : ℝ) : ℂ) * u x) x =
      -∫ x, {x : ι → ℝ | x j < c}.indicator (fun x => ((ψ x : ℝ) : ℂ) * g x) x := by
  set H : Set (ι → ℝ) := {x | x j < c} with hH
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
  obtain ⟨Mψ, hMψ⟩ := hψ1.continuous.bounded_above_of_compact_support hψc
  obtain ⟨Mψ', hMψ'⟩ :=
    (continuous_pd hψ1 i).bounded_above_of_compact_support (hasCompactSupport_pd hψc i)
  obtain ⟨Cθ, hCθ0, hCθ⟩ := exists_bound_deriv_halfCut
  set η : ℕ → (ι → ℝ) → ℝ := fun k => faceCut j c ((k : ℝ) + 1) with hηdef
  have hηc : ∀ k, ContDiff ℝ ∞ (η k) := fun k => contDiff_faceCut j c _
  have hη1 : ∀ k, ContDiff ℝ 1 (η k) := fun k => (hηc k).of_le (by simp)
  have hk1 : ∀ k : ℕ, (0 : ℝ) < (k : ℝ) + 1 := fun k => by positivity
  -- facts on `η`
  have hη_out : ∀ (k : ℕ) (x : ι → ℝ), c ≤ x j → η k x = 0 := fun k x hx => by
    simp only [hηdef, faceCut]
    exact halfCut_eq_zero (by nlinarith [hk1 k])
  have hη_abs : ∀ k x, |η k x| ≤ 1 := fun k x => by
    simp only [hηdef, faceCut]
    rw [abs_of_nonneg (halfCut_nonneg _)]; exact halfCut_le_one _
  have hη_in : ∀ x : ι → ℝ, x j < c → ∀ᶠ k : ℕ in atTop, (2 : ℝ) < ((k : ℝ) + 1) * (c - x j) := by
    intro x hx
    obtain ⟨N, hN⟩ := exists_nat_gt (2 / (c - x j))
    filter_upwards [eventually_ge_atTop N] with k hk
    have hpos : 0 < c - x j := by linarith
    have : (2 : ℝ) / (c - x j) < (k : ℝ) + 1 := by
      have : (N : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    rwa [div_lt_iff₀ hpos] at this
  have hη_lim : ∀ x : ι → ℝ, Tendsto (fun k => η k x) atTop (𝓝 (H.indicator 1 x)) := by
    intro x
    by_cases hx : x j < c
    · rw [indicator_of_mem (show x ∈ H from hx), Pi.one_apply]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hη_in x hx] with k hk
      simp only [hηdef, faceCut]
      exact (halfCut_eq_one hk.le).symm
    · rw [indicator_of_notMem (show x ∉ H from hx)]
      exact tendsto_const_nhds.congr fun k => (hη_out k x (not_lt.mp hx)).symm
  -- the derivative of the cutoff
  have hpdη : ∀ k x, pd (η k) i x =
      deriv halfCut (((k : ℝ) + 1) * (c - x j)) * (-((k : ℝ) + 1)) * (if i = j then 1 else 0) :=
    fun k x => pd_faceCut j c _ i x
  have hpdη_out : ∀ (k : ℕ) (x : ι → ℝ), c ≤ x j → pd (η k) i x = 0 := fun k x hx => by
    rw [hpdη, deriv_halfCut_eq_zero (Or.inl (by nlinarith [hk1 k]))]; ring
  have hpdη_lim : ∀ x : ι → ℝ, Tendsto (fun k => pd (η k) i x * ψ x) atTop (𝓝 0) := by
    intro x
    by_cases hx : x j < c
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [hη_in x hx] with k hk
      rw [hpdη, deriv_halfCut_eq_zero (Or.inr hk)]; ring
    · exact tendsto_const_nhds.congr fun k => by rw [hpdη_out k x (not_lt.mp hx), zero_mul]
  have hpdη_bound : ∃ M : ℝ, ∀ k x, |pd (η k) i x * ψ x| ≤ M := by
    by_cases hij : i = j
    · obtain ⟨L, hL⟩ := hface hij
      refine ⟨Cθ * (2 * |L|), fun k x => ?_⟩
      rw [hpdη, if_pos hij, mul_one]
      set t := ((k : ℝ) + 1) * (c - x j)
      by_cases ht : t < 1 ∨ 2 < t
      · rw [deriv_halfCut_eq_zero ht]; simp; positivity
      · push_neg at ht
        obtain ⟨ht1, ht2⟩ := ht
        have hpos : 0 < c - x j := by
          by_contra hn; push_neg at hn; nlinarith [hk1 k]
        have hψx : |ψ x| ≤ |L| * (c - x j) := by
          refine (hL x).trans ?_
          rw [abs_sub_comm, abs_of_pos hpos]
          exact mul_le_mul_of_nonneg_right (le_abs_self L) hpos.le
        rw [abs_mul, abs_mul, abs_neg, abs_of_pos (hk1 k)]
        calc |deriv halfCut t| * ((k : ℝ) + 1) * |ψ x|
            ≤ Cθ * ((k : ℝ) + 1) * (|L| * (c - x j)) := by
              gcongr
              · exact hCθ t
          _ = Cθ * |L| * t := by simp only [t]; ring
          _ ≤ Cθ * |L| * 2 := by gcongr
          _ = Cθ * (2 * |L|) := by ring
    · exact ⟨0, fun k x => by rw [hpdη, if_neg hij]; simp⟩
  obtain ⟨Mb, hMb⟩ := hpdη_bound
  -- the test functions `η_k ψ`
  have htest : ∀ k, IsTest (Ω' ∩ H) (fun x => η k x * ψ x) := by
    intro k
    refine ⟨(hηc k).mul hψ, hψc.mul_left, ?_⟩
    have hsη : tsupport (η k) ⊆ {x | x j ≤ c - 1 / ((k : ℝ) + 1)} := by
      refine closure_minimal (fun x hx => ?_) (isClosed_le (continuous_apply j) continuous_const)
      by_contra hn
      simp only [mem_setOf_eq, not_le] at hn
      apply hx
      simp only [hηdef, faceCut]
      apply halfCut_eq_zero
      have : ((k : ℝ) + 1) * (c - x j) < ((k : ℝ) + 1) * (1 / ((k : ℝ) + 1)) :=
        mul_lt_mul_of_pos_left (by linarith) (hk1 k)
      rw [mul_one_div_cancel (hk1 k).ne'] at this
      exact this.le
    intro x hx
    have h1 := hsη ((tsupport_mul_subset_left) hx)
    have h2 := hψs ((tsupport_mul_subset_right) hx)
    refine ⟨h2, ?_⟩
    show x j < c
    simp only [mem_setOf_eq] at h1
    have : 0 < 1 / ((k : ℝ) + 1) := by positivity
    linarith
  have hk := fun k => h _ (htest k)
  -- split the derivative of the product
  have hsplit : ∀ k, ∫ x, ((pd (fun x => η k x * ψ x) i x : ℝ) : ℂ) * u x =
      (∫ x, ((η k x * pd ψ i x : ℝ) : ℂ) * u x) + ∫ x, ((pd (η k) i x * ψ x : ℝ) : ℂ) * u x := by
    intro k
    have i1 : Integrable fun x => ((η k x * pd ψ i x : ℝ) : ℂ) * u x :=
      integrable_ofReal_mul_of_bounded hu ((hη1 k).continuous.mul (continuous_pd hψ1 i))
        (M := Mψ') fun x => by
          rw [abs_mul]
          calc |η k x| * |pd ψ i x| ≤ 1 * Mψ' := by
                gcongr
                · exact hη_abs k x
                · simpa using hMψ' x
            _ = Mψ' := one_mul _
    have i2 : Integrable fun x => ((pd (η k) i x * ψ x : ℝ) : ℂ) * u x :=
      integrable_ofReal_mul_of_bounded hu ((continuous_pd (hη1 k) i).mul hψ1.continuous) (hMb k)
    have e : (fun x => ((pd (fun x => η k x * ψ x) i x : ℝ) : ℂ) * u x) =
        fun x => ((η k x * pd ψ i x : ℝ) : ℂ) * u x + ((pd (η k) i x * ψ x : ℝ) : ℂ) * u x := by
      funext x
      simp only [pd_mul (hη1 k) hψ1]
      push_cast; ring
    rw [e, integral_add i1 i2]
  -- the three limits
  have hA : Tendsto (fun k => ∫ x, ((η k x * pd ψ i x : ℝ) : ℂ) * u x) atTop
      (𝓝 (∫ x, ((H.indicator 1 x * pd ψ i x : ℝ) : ℂ) * u x)) :=
    tendsto_integral_mul_of_bounded hu (fun k => (hη1 k).continuous.mul (continuous_pd hψ1 i))
      (M := Mψ') (fun k x => by
        rw [abs_mul]
        calc |η k x| * |pd ψ i x| ≤ 1 * Mψ' := by
              gcongr
              · exact hη_abs k x
              · simpa using hMψ' x
          _ = Mψ' := one_mul _)
      (fun x => (hη_lim x).mul_const _)
  have hB : Tendsto (fun k => ∫ x, ((pd (η k) i x * ψ x : ℝ) : ℂ) * u x) atTop
      (𝓝 (∫ x, (((0 : ℝ) : ℝ) : ℂ) * u x)) :=
    tendsto_integral_mul_of_bounded hu (fun k => (continuous_pd (hη1 k) i).mul hψ1.continuous)
      hMb hpdη_lim
  have hC : Tendsto (fun k => ∫ x, ((η k x * ψ x : ℝ) : ℂ) * g x) atTop
      (𝓝 (∫ x, ((H.indicator 1 x * ψ x : ℝ) : ℂ) * g x)) :=
    tendsto_integral_mul_of_bounded hg (fun k => (hη1 k).continuous.mul hψ1.continuous)
      (M := Mψ) (fun k x => by
        rw [abs_mul]
        calc |η k x| * |ψ x| ≤ 1 * Mψ := by
              gcongr
              · exact hη_abs k x
              · simpa using hMψ x
          _ = Mψ := one_mul _)
      (fun x => (hη_lim x).mul_const _)
  have hlhs : Tendsto (fun k => ∫ x, ((pd (fun x => η k x * ψ x) i x : ℝ) : ℂ) * u x) atTop
      (𝓝 ((∫ x, ((H.indicator 1 x * pd ψ i x : ℝ) : ℂ) * u x) + 0)) := by
    simp only [hsplit]
    simpa using hA.add hB
  have hrhs : Tendsto (fun k => ∫ x, ((pd (fun x => η k x * ψ x) i x : ℝ) : ℂ) * u x) atTop
      (𝓝 (-∫ x, ((H.indicator 1 x * ψ x : ℝ) : ℂ) * g x)) := by
    simp only [hk]
    exact hC.neg
  have heq := tendsto_nhds_unique hlhs hrhs
  rw [add_zero] at heq
  have e1 : (fun x => H.indicator (fun x => ((pd ψ i x : ℝ) : ℂ) * u x) x) =
      fun x => ((H.indicator 1 x * pd ψ i x : ℝ) : ℂ) * u x := by
    funext x; by_cases hx : x ∈ H <;> simp [hx]
  have e2 : (fun x => H.indicator (fun x => ((ψ x : ℝ) : ℂ) * g x) x) =
      fun x => ((H.indicator 1 x * ψ x : ℝ) : ℂ) * g x := by
    funext x; by_cases hx : x ∈ H <;> simp [hx]
  rw [e1, e2]
  exact heq


/-! ### The even reflection across one face -/

/-- The even reflection extension of `u` from `{x_j < c}`:
`u` on `{x_j < c}`, `u ∘ R` on `{x_j > c}` (and `0` on the hyperplane, a null set). -/
def reflExt (j : ι) (c : ℝ) (u : (ι → ℝ) → ℂ) : (ι → ℝ) → ℂ :=
  {x | x j < c}.indicator u + {x | c < x j}.indicator (fun x => u (refl j c x))

/-- The reflected weak gradient: even for `i ≠ j`, odd for `i = j`. -/
def reflExtGrad (j : ι) (c : ℝ) (i : ι) (g : (ι → ℝ) → ℂ) : (ι → ℝ) → ℂ :=
  {x | x j < c}.indicator g +
    {x | c < x j}.indicator (fun x => ((reflSign j i : ℝ) : ℂ) * g (refl j c x))

theorem reflExt_of_lt {j : ι} {c : ℝ} {u : (ι → ℝ) → ℂ} {x : ι → ℝ} (hx : x j < c) :
    reflExt j c u x = u x := by
  simp [reflExt, hx, not_lt.mpr hx.le]

theorem refl_mem_lt_iff {j : ι} {c : ℝ} {x : ι → ℝ} : refl j c x j < c ↔ c < x j := by
  rw [refl_apply_self]; constructor <;> intro h <;> linarith

/-- The reflected half of an indicator integral: `∫_{x_j>c} F(R x) dx = ∫_{x_j<c} F`. -/
theorem integral_indicator_comp_refl {F : (ι → ℝ) → ℂ} (j : ι) (c : ℝ) :
    ∫ x, {x : ι → ℝ | c < x j}.indicator (fun x => F (refl j c x)) x =
      ∫ y, {y : ι → ℝ | y j < c}.indicator F y := by
  rw [← integral_comp_refl j c]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  by_cases hy : y j < c
  · have : c < refl j c y j := by rw [refl_apply_self]; linarith
    simp [hy, this, refl_refl]
  · have : ¬ c < refl j c y j := by rw [refl_apply_self]; intro h; exact hy (by linarith)
    simp [hy, this]

theorem HasWeakPartial.indicator {Ω : Set (ι → ℝ)} {i : ι} {u g : (ι → ℝ) → ℂ}
    (h : HasWeakPartial Ω i u g) : HasWeakPartial Ω i (Ω.indicator u) (Ω.indicator g) := by
  intro φ hφ
  have e1 : (fun x => ((pd φ i x : ℝ) : ℂ) * Ω.indicator u x) =
      fun x => ((pd φ i x : ℝ) : ℂ) * u x := by
    funext x
    by_cases hx : x ∈ Ω
    · simp [hx]
    · have : pd φ i x = 0 :=
        image_eq_zero_of_notMem_tsupport fun h' => hx (hφ.subset (tsupport_pd_subset φ i h'))
      simp [this]
  have e2 : (fun x => ((φ x : ℝ) : ℂ) * Ω.indicator g x) = fun x => ((φ x : ℝ) : ℂ) * g x := by
    funext x
    by_cases hx : x ∈ Ω
    · simp [hx]
    · have : φ x = 0 := image_eq_zero_of_notMem_tsupport fun h' => hx (hφ.subset h')
      simp [this]
  rw [e1, e2]
  exact h φ hφ

/-- **One-face reflection extension.**  Let `Ω'` be open and invariant under the reflection `R`
across `x_j = c`.  If `g` is the weak `i`-th partial of `u` on `Ω' ∩ {x_j < c}` and `u, g` are
integrable there, then the even reflection `E u` has the weak `i`-th partial `E_i g` on `Ω'`. -/
theorem hasWeakPartial_reflExt {Ω' : Set (ι → ℝ)} (hΩ' : IsOpen Ω') {j : ι} {c : ℝ}
    (hinv : ∀ x, x ∈ Ω' → refl j c x ∈ Ω') {i : ι} {u g : (ι → ℝ) → ℂ}
    (h : HasWeakPartial (Ω' ∩ {x | x j < c}) i u g)
    (hu : IntegrableOn u (Ω' ∩ {x | x j < c})) (hg : IntegrableOn g (Ω' ∩ {x | x j < c})) :
    HasWeakPartial Ω' i (reflExt j c u) (reflExtGrad j c i g) := by
  intro φ hφ
  set H : Set (ι → ℝ) := {x | x j < c} with hH
  set H' : Set (ι → ℝ) := {x | c < x j} with hH'
  set Ω := Ω' ∩ H
  have hHm : MeasurableSet H := measurableSet_lt (measurable_pi_apply j) measurable_const
  have hΩm : MeasurableSet Ω := hΩ'.measurableSet.inter hHm
  set ut := Ω.indicator u
  set gt := Ω.indicator g
  have hut : Integrable ut := (integrable_indicator_iff hΩm).mpr hu
  have hgt : Integrable gt := (integrable_indicator_iff hΩm).mpr hg
  have ht := h.indicator
  set σ := reflSign j i
  have hφ1 : ContDiff ℝ 1 φ := hφ.smooth.of_le (by simp)
  have hφd : Differentiable ℝ φ := hφ1.differentiable one_ne_zero
  -- the symmetrised test function
  set ψ : (ι → ℝ) → ℝ := fun x => φ x + σ * φ (refl j c x) with hψdef
  have hψs : ContDiff ℝ ∞ ψ := hφ.smooth.add (contDiff_const.mul (hφ.smooth.comp (contDiff_refl j c)))
  have hcR : HasCompactSupport fun x => φ (refl j c x) :=
    hφ.compact.comp_homeomorph (reflHomeo j c)
  have hψc : HasCompactSupport ψ := hφ.compact.add hcR.mul_left
  have hRsub : tsupport (fun x => φ (refl j c x)) ⊆ Ω' := by
    intro y hy
    have : tsupport (fun x => φ (refl j c x)) = (reflHomeo j c) ⁻¹' tsupport φ :=
      tsupport_comp_eq_preimage φ (reflHomeo j c)
    rw [this] at hy
    have h1 := hinv _ (hφ.subset hy)
    simpa [reflHomeo, refl_refl] using h1
  have hψsub : tsupport ψ ⊆ Ω' := by
    refine (tsupport_add _ _).trans (union_subset hφ.subset ?_)
    exact (tsupport_mul_subset_right).trans hRsub
  have hface : i = j → ∃ L : ℝ, ∀ x, |ψ x| ≤ L * |x j - c| := by
    intro hij
    obtain ⟨K, hK⟩ := hφ1.lipschitzWith_of_hasCompactSupport hφ.compact one_ne_zero
    refine ⟨2 * K, fun x => ?_⟩
    have hσ : σ = -1 := by simp [σ, reflSign, hij]
    have hd : dist x (refl j c x) = 2 * |x j - c| := by
      rw [dist_eq_norm]
      have : x - refl j c x = (2 * (x j - c)) • (Pi.single j 1 : ι → ℝ) := by
        simp [refl]
      rw [this, norm_smul, norm_mul, Real.norm_two, Real.norm_eq_abs]
      have : ‖(Pi.single j (1 : ℝ) : ι → ℝ)‖ = 1 := by
        rw [show (Pi.single j (1 : ℝ) : ι → ℝ) = Pi.single j 1 from rfl, Pi.norm_single, norm_one]
      rw [this, mul_one]
    have := hK.dist_le_mul x (refl j c x)
    rw [hd, Real.dist_eq] at this
    simp only [hψdef, hσ, neg_one_mul, ← sub_eq_add_neg]
    calc |φ x - φ (refl j c x)| ≤ K * (2 * |x j - c|) := this
      _ = 2 * K * |x j - c| := by ring
  have hpdψ : ∀ x, pd ψ i x = pd φ i x + pd φ i (refl j c x) := by
    intro x
    have h1 : pd ψ i x = pd φ i x + σ * pd (fun y => φ (refl j c y)) i x := by
      unfold pd
      have hdR : DifferentiableAt ℝ (fun y => φ (refl j c y)) x :=
        (hφd (refl j c x)).comp x (hasFDerivAt_refl j c x).differentiableAt
      have hD : HasFDerivAt (fun y => φ y + σ * φ (refl j c y))
          (fderiv ℝ φ x + σ • fderiv ℝ (fun y => φ (refl j c y)) x) x :=
        (hφd x).hasFDerivAt.add (hdR.hasFDerivAt.const_mul σ)
      rw [show ψ = fun y => φ y + σ * φ (refl j c y) from rfl, hD.fderiv]
      simp
    rw [h1, pd_comp_refl hφd j c i x, smul_eq_mul, ← mul_assoc, reflSign_sq, one_mul]
  have core := weak_halfspace_limit (Ω' := Ω') ht hut hgt hψs hψc hψsub hface
  -- bounded multipliers
  have hpdφb := (continuous_pd hφ1 i).bounded_above_of_compact_support
    (hasCompactSupport_pd hφ.compact i)
  obtain ⟨Mp, hMp⟩ := hpdφb
  obtain ⟨Mφ, hMφ⟩ := hφ1.continuous.bounded_above_of_compact_support hφ.compact
  have hpd0 : ∀ x, x ∉ Ω' → pd φ i x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h' => hx (hφ.subset (tsupport_pd_subset φ i h'))
  have hφ0 : ∀ x, x ∉ Ω' → φ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport fun h' => hx (hφ.subset h')
  have hutR : Integrable fun x => ut (refl j c x) := (integrable_comp_refl_iff j c).mpr hut
  have hgtR : Integrable fun x => gt (refl j c x) := (integrable_comp_refl_iff j c).mpr hgt
  have iA : Integrable fun x => ((pd φ i x : ℝ) : ℂ) * ut x :=
    integrable_ofReal_mul_of_bounded hut (continuous_pd hφ1 i) (fun x => by simpa using hMp x)
  have iB : Integrable fun x => ((pd φ i (refl j c x) : ℝ) : ℂ) * ut x :=
    integrable_ofReal_mul_of_bounded hut ((continuous_pd hφ1 i).comp (continuous_refl j c))
      (fun x => by simpa using hMp _)
  have iC : Integrable fun x => ((φ x : ℝ) : ℂ) * gt x :=
    integrable_ofReal_mul_of_bounded hgt hφ1.continuous (fun x => by simpa using hMφ x)
  have iD : Integrable fun x => ((φ (refl j c x) : ℝ) : ℂ) * gt x :=
    integrable_ofReal_mul_of_bounded hgt (hφ1.continuous.comp (continuous_refl j c))
      (fun x => by simpa using hMφ _)
  -- the left-hand side
  have eL : (fun x => ((pd φ i x : ℝ) : ℂ) * reflExt j c u x) =
      fun x => H.indicator (fun x => ((pd φ i x : ℝ) : ℂ) * ut x) x +
        H'.indicator (fun x => ((pd φ i (refl j c (refl j c x)) : ℝ) : ℂ) * ut (refl j c x)) x := by
    funext x
    by_cases hx : x j < c
    · have hx' : ¬ c < x j := not_lt.mpr hx.le
      by_cases hxΩ : x ∈ Ω'
      · simp [reflExt, Set.indicator_apply, hx, hx', hxΩ, ut, Ω, hH, hH']
      · simp [reflExt, Set.indicator_apply, hx, hx', hpd0 x hxΩ, hH, hH']
    · by_cases hx' : c < x j
      · by_cases hxΩ : x ∈ Ω'
        · have h1 : refl j c x j < c := refl_mem_lt_iff.mpr hx'
          have h2 : refl j c x ∈ Ω' := hinv x hxΩ
          simp [reflExt, Set.indicator_apply, hx, hx', h1, h2, refl_refl, ut, Ω, hH, hH']
        · simp [reflExt, Set.indicator_apply, hx, hx', hpd0 x hxΩ, hH, hH', refl_refl]
      · simp [reflExt, Set.indicator_apply, hx, hx', hH, hH']
  have hL : ∫ x, ((pd φ i x : ℝ) : ℂ) * reflExt j c u x =
      ∫ x, H.indicator (fun x => ((pd ψ i x : ℝ) : ℂ) * ut x) x := by
    rw [eL, integral_add ((integrable_indicator_iff hHm).mpr iA.integrableOn)
      (by
        have : Integrable fun x => ((pd φ i (refl j c (refl j c x)) : ℝ) : ℂ) * ut (refl j c x) :=
          (integrable_comp_refl_iff j c (f := fun y => ((pd φ i (refl j c y) : ℝ) : ℂ) * ut y)).mpr iB
        exact (integrable_indicator_iff (measurableSet_lt measurable_const
          (measurable_pi_apply j))).mpr this.integrableOn),
      integral_indicator_comp_refl (F := fun y => ((pd φ i (refl j c y) : ℝ) : ℂ) * ut y) j c,
      integral_indicator hHm, integral_indicator hHm, integral_indicator hHm,
      ← integral_add iA.integrableOn iB.integrableOn]
    refine setIntegral_congr_fun hHm fun x _ => ?_
    simp only [hpdψ]; push_cast; ring
  -- the right-hand side
  have eR : (fun x => ((φ x : ℝ) : ℂ) * reflExtGrad j c i g x) =
      fun x => H.indicator (fun x => ((φ x : ℝ) : ℂ) * gt x) x +
        H'.indicator (fun x => ((σ : ℝ) : ℂ) *
          (((φ (refl j c (refl j c x)) : ℝ) : ℂ) * gt (refl j c x))) x := by
    funext x
    by_cases hx : x j < c
    · have hx' : ¬ c < x j := not_lt.mpr hx.le
      by_cases hxΩ : x ∈ Ω'
      · simp [reflExtGrad, Set.indicator_apply, hx, hx', hxΩ, gt, Ω, hH, hH']
      · simp [reflExtGrad, Set.indicator_apply, hx, hx', hφ0 x hxΩ, hH, hH']
    · by_cases hx' : c < x j
      · by_cases hxΩ : x ∈ Ω'
        · have h1 : refl j c x j < c := refl_mem_lt_iff.mpr hx'
          have h2 : refl j c x ∈ Ω' := hinv x hxΩ
          simp [reflExtGrad, Set.indicator_apply, hx, hx', h1, h2, refl_refl, gt, Ω, hH, hH', σ]
          ring
        · simp [reflExtGrad, Set.indicator_apply, hx, hx', hφ0 x hxΩ, hH, hH', refl_refl]
      · simp [reflExtGrad, Set.indicator_apply, hx, hx', hH, hH']
  have hR : ∫ x, ((φ x : ℝ) : ℂ) * reflExtGrad j c i g x =
      ∫ x, H.indicator (fun x => ((ψ x : ℝ) : ℂ) * gt x) x := by
    have iD' : Integrable fun x => ((σ : ℝ) : ℂ) * (((φ (refl j c x) : ℝ) : ℂ) * gt x) :=
      iD.const_mul _
    rw [eR, integral_add ((integrable_indicator_iff hHm).mpr iC.integrableOn)
      (by
        have : Integrable fun x => ((σ : ℝ) : ℂ) *
            (((φ (refl j c (refl j c x)) : ℝ) : ℂ) * gt (refl j c x)) :=
          (integrable_comp_refl_iff j c
            (f := fun y => ((σ : ℝ) : ℂ) * (((φ (refl j c y) : ℝ) : ℂ) * gt y))).mpr iD'
        exact (integrable_indicator_iff (measurableSet_lt measurable_const
          (measurable_pi_apply j))).mpr this.integrableOn),
      integral_indicator_comp_refl
        (F := fun y => ((σ : ℝ) : ℂ) * (((φ (refl j c y) : ℝ) : ℂ) * gt y)) j c,
      integral_indicator hHm, integral_indicator hHm, integral_indicator hHm,
      ← integral_add iC.integrableOn iD'.integrableOn]
    refine setIntegral_congr_fun hHm fun x _ => ?_
    simp only [hψdef]; push_cast; ring
  rw [hL, hR]
  exact core


/-! ### Norm bounds and the `W^{1,2}` versions -/

theorem refl_preimage_inter {Ω' : Set (ι → ℝ)} {j : ι} {c : ℝ}
    (hinv : ∀ x, x ∈ Ω' → refl j c x ∈ Ω') :
    refl j c ⁻¹' (Ω' ∩ {x | x j < c}) = {x | c < x j} ∩ Ω' := by
  ext x
  simp only [mem_preimage, mem_inter_iff, mem_setOf_eq, refl_mem_lt_iff]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h2, by simpa [refl_refl] using hinv _ h1⟩
  · rintro ⟨h1, h2⟩; exact ⟨hinv _ h2, h1⟩

theorem measurePreserving_refl_restrict (j : ι) (c : ℝ) (S : Set (ι → ℝ)) :
    MeasurePreserving (refl j c) (volume.restrict (refl j c ⁻¹' S)) (volume.restrict S) :=
  (measurePreserving_refl j c).restrict_preimage_emb (reflEquiv j c).measurableEmbedding S

theorem eLpNorm_unit_mul {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : ℂ} (hs : ‖s‖ = 1)
    (f : α → ℂ) (p : ℝ≥0∞) : eLpNorm (fun x => s * f x) p μ = eLpNorm f p μ := by
  rw [show (fun x => s * f x) = s • f from rfl, eLpNorm_const_smul]
  rw [show ‖s‖ₑ = 1 by rw [← ofReal_norm_eq_enorm, hs, ENNReal.ofReal_one], one_mul]

/-- `L²` bound for the reflection combination `1_{x_j<c} w + 1_{x_j>c} s · w∘R` (`|s| = 1`). -/
theorem memLp_reflCombo {Ω' : Set (ι → ℝ)} (hΩ' : IsOpen Ω') {j : ι} {c : ℝ}
    (hinv : ∀ x, x ∈ Ω' → refl j c x ∈ Ω') {w : (ι → ℝ) → ℂ}
    (hw : MemLp w 2 (volume.restrict (Ω' ∩ {x | x j < c}))) (s : ℂ) (hs : ‖s‖ = 1) :
    MemLp ({x | x j < c}.indicator w + {x | c < x j}.indicator (fun x => s * w (refl j c x))) 2
        (volume.restrict Ω') ∧
      eLpNorm ({x | x j < c}.indicator w + {x | c < x j}.indicator
        (fun x => s * w (refl j c x))) 2 (volume.restrict Ω') ≤
        2 * eLpNorm w 2 (volume.restrict (Ω' ∩ {x | x j < c})) := by
  have hHm : MeasurableSet {x : ι → ℝ | x j < c} :=
    measurableSet_lt (measurable_pi_apply j) measurable_const
  have hH'm : MeasurableSet {x : ι → ℝ | c < x j} :=
    measurableSet_lt measurable_const (measurable_pi_apply j)
  have e1 : (volume.restrict Ω').restrict {x : ι → ℝ | x j < c} =
      volume.restrict (Ω' ∩ {x | x j < c}) := by
    rw [Measure.restrict_restrict hHm, inter_comm]
  have hmp : MeasurePreserving (refl j c) (volume.restrict ({x : ι → ℝ | c < x j} ∩ Ω'))
      (volume.restrict (Ω' ∩ {x | x j < c})) := by
    have := measurePreserving_refl_restrict j c (Ω' ∩ {x | x j < c})
    rwa [refl_preimage_inter hinv] at this
  have e2 : (volume.restrict Ω').restrict {x : ι → ℝ | c < x j} =
      volume.restrict ({x | c < x j} ∩ Ω') := by
    rw [Measure.restrict_restrict hH'm]
  have hR : MemLp (fun x => s * w (refl j c x)) 2 (volume.restrict ({x | c < x j} ∩ Ω')) :=
    (hw.comp_measurePreserving hmp).const_mul s
  have hRn : eLpNorm (fun x => s * w (refl j c x)) 2 (volume.restrict ({x | c < x j} ∩ Ω')) =
      eLpNorm w 2 (volume.restrict (Ω' ∩ {x | x j < c})) := by
    rw [eLpNorm_unit_mul hs]
    exact eLpNorm_comp_measurePreserving hw.1 hmp
  have m1 : MemLp ({x | x j < c}.indicator w) 2 (volume.restrict Ω') := by
    rw [memLp_indicator_iff_restrict hHm, e1]; exact hw
  have m2 : MemLp ({x | c < x j}.indicator (fun x => s * w (refl j c x))) 2
      (volume.restrict Ω') := by
    rw [memLp_indicator_iff_restrict hH'm, e2]; exact hR
  refine ⟨m1.add m2, ?_⟩
  refine (eLpNorm_add_le m1.1 m2.1 (by norm_num)).trans ?_
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hHm, e1, eLpNorm_indicator_eq_eLpNorm_restrict hH'm,
    e2, hRn, two_mul]

theorem norm_reflSign (j i : ι) : ‖((reflSign j i : ℝ) : ℂ)‖ = 1 := by
  unfold reflSign; split_ifs <;> simp

/-- **One-face extension in `W^{1,2}`**: for `Ω'` open and `R`-invariant with
`Ω' ∩ {x_j < c}` of finite measure, the even reflection maps `W^{1,2}(Ω' ∩ {x_j < c})` to
`W^{1,2}(Ω')` with `‖E u‖ ≤ 2 ‖u‖`, and `E u = u` on `{x_j < c}`. -/
theorem memW12_reflExt {Ω' : Set (ι → ℝ)} (hΩ' : IsOpen Ω') {j : ι} {c : ℝ}
    (hinv : ∀ x, x ∈ Ω' → refl j c x ∈ Ω') {u : (ι → ℝ) → ℂ} {g : ι → (ι → ℝ) → ℂ}
    (hW : MemW12 (Ω' ∩ {x | x j < c}) u g) (hfin : volume (Ω' ∩ {x | x j < c}) ≠ ⊤) :
    MemW12 Ω' (reflExt j c u) (fun i => reflExtGrad j c i (g i)) ∧
      w12Norm Ω' (reflExt j c u) (fun i => reflExtGrad j c i (g i)) ≤
        2 * w12Norm (Ω' ∩ {x | x j < c}) u g := by
  have : IsFiniteMeasure (volume.restrict (Ω' ∩ {x : ι → ℝ | x j < c})) :=
    isFiniteMeasure_restrict.mpr hfin
  have hu1 : IntegrableOn u (Ω' ∩ {x | x j < c}) := hW.memLp.integrable (by norm_num)
  have hg1 : ∀ i, IntegrableOn (g i) (Ω' ∩ {x | x j < c}) := fun i =>
    (hW.memLp_grad i).integrable (by norm_num)
  have hcu := memLp_reflCombo hΩ' hinv hW.memLp 1 (by simp)
  have hcg := fun i => memLp_reflCombo hΩ' hinv (hW.memLp_grad i) _ (norm_reflSign j i)
  have eu : reflExt j c u = {x | x j < c}.indicator u +
      {x | c < x j}.indicator (fun x => (1 : ℂ) * u (refl j c x)) := by
    simp [reflExt]
  refine ⟨⟨?_, fun i => (hcg i).1, fun i => hasWeakPartial_reflExt hΩ' hinv (hW.weak i) hu1
    (hg1 i)⟩, ?_⟩
  · rw [eu]; exact hcu.1
  · unfold w12Norm
    rw [eu, mul_add, Finset.mul_sum]
    exact add_le_add hcu.2 (Finset.sum_le_sum fun i _ => (hcg i).2)

/-- **`W^{1,2}` under a reflection** (isometric). -/
theorem MemW12.comp_refl {Ω : Set (ι → ℝ)} {u : (ι → ℝ) → ℂ} {g : ι → (ι → ℝ) → ℂ}
    (hW : MemW12 Ω u g) (j : ι) (c : ℝ) :
    MemW12 (refl j c ⁻¹' Ω) (fun x => u (refl j c x))
        (fun i x => ((reflSign j i : ℝ) : ℂ) * g i (refl j c x)) ∧
      w12Norm (refl j c ⁻¹' Ω) (fun x => u (refl j c x))
        (fun i x => ((reflSign j i : ℝ) : ℂ) * g i (refl j c x)) = w12Norm Ω u g := by
  have hmp := measurePreserving_refl_restrict j c Ω
  refine ⟨⟨hW.memLp.comp_measurePreserving hmp, fun i =>
    ((hW.memLp_grad i).comp_measurePreserving hmp).const_mul _,
    fun i => (hW.weak i).comp_refl j c⟩, ?_⟩
  unfold w12Norm
  congr 1
  · exact eLpNorm_comp_measurePreserving hW.memLp.1 hmp
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [eLpNorm_unit_mul (norm_reflSign j i)]
    exact eLpNorm_comp_measurePreserving (hW.memLp_grad i).1 hmp


/-! ### Coordinate boxes -/

/-- The open coordinate box `Π_i (a_i, b_i)`. -/
def box (a b : ι → ℝ) : Set (ι → ℝ) := Set.pi univ fun i => Ioo (a i) (b i)

theorem isOpen_box (a b : ι → ℝ) : IsOpen (box a b) :=
  isOpen_set_pi finite_univ fun _ _ => isOpen_Ioo

theorem mem_box {a b x : ι → ℝ} : x ∈ box a b ↔ ∀ i, a i < x i ∧ x i < b i := by
  simp [box]

theorem box_subset_Icc (a b : ι → ℝ) : box a b ⊆ Icc a b := fun x hx =>
  ⟨fun i => (mem_box.mp hx i).1.le, fun i => (mem_box.mp hx i).2.le⟩

theorem volume_box_ne_top (a b : ι → ℝ) : volume (box a b) ≠ ⊤ :=
  ((Metric.isBounded_Icc a b).subset (box_subset_Icc a b)).measure_lt_top.ne

theorem box_mono {a b a' b' : ι → ℝ} (ha : ∀ i, a' i ≤ a i) (hb : ∀ i, b i ≤ b' i) :
    box a b ⊆ box a' b' := fun x hx => mem_box.mpr fun i =>
  ⟨(ha i).trans_lt (mem_box.mp hx i).1, (mem_box.mp hx i).2.trans_le (hb i)⟩

theorem box_upper_inter {a b : ι → ℝ} (j : ι) (hab : a j ≤ b j) :
    box a (Function.update b j (2 * b j - a j)) ∩ {x | x j < b j} = box a b := by
  ext x
  simp only [mem_inter_iff, mem_box, mem_setOf_eq]
  constructor
  · rintro ⟨h1, h2⟩ i
    by_cases hi : i = j
    · subst hi; exact ⟨(h1 i).1, h2⟩
    · have := h1 i; rwa [Function.update_of_ne hi] at this
  · intro h
    refine ⟨fun i => ?_, (h j).2⟩
    by_cases hi : i = j
    · subst hi; rw [Function.update_self]; exact ⟨(h i).1, by linarith [(h i).2]⟩
    · rw [Function.update_of_ne hi]; exact h i

theorem refl_mem_box_upper {a b : ι → ℝ} (j : ι) {x : ι → ℝ}
    (hx : x ∈ box a (Function.update b j (2 * b j - a j))) :
    refl j (b j) x ∈ box a (Function.update b j (2 * b j - a j)) := by
  rw [mem_box] at hx ⊢
  intro i
  by_cases hi : i = j
  · subst hi
    have := hx i
    rw [Function.update_self] at this ⊢
    rw [refl_apply_self]
    constructor <;> linarith [this.1, this.2]
  · rw [refl_apply_ne hi]; exact hx i

theorem reflExtGrad_of_lt {j : ι} {c : ℝ} {i : ι} {g : (ι → ℝ) → ℂ} {x : ι → ℝ} (hx : x j < c) :
    reflExtGrad j c i g x = g x := by
  simp [reflExtGrad, hx, not_lt.mpr hx.le]

/-- Extension across the upper face `x_j = b_j` of a box. -/
theorem exists_ext_upper {a b : ι → ℝ} (j : ι) (hab : a j ≤ b j) {u : (ι → ℝ) → ℂ}
    {g : ι → (ι → ℝ) → ℂ} (hW : MemW12 (box a b) u g) :
    ∃ (U : (ι → ℝ) → ℂ) (G : ι → (ι → ℝ) → ℂ),
      MemW12 (box a (Function.update b j (2 * b j - a j))) U G ∧
      (∀ x ∈ box a b, U x = u x ∧ ∀ i, G i x = g i x) ∧
      w12Norm (box a (Function.update b j (2 * b j - a j))) U G ≤ 2 * w12Norm (box a b) u g := by
  have hinter := box_upper_inter j hab
  rw [← hinter] at hW
  obtain ⟨h1, h2⟩ := memW12_reflExt (isOpen_box _ _) (fun x hx => refl_mem_box_upper j hx) hW
    (by rw [hinter]; exact volume_box_ne_top a b)
  rw [hinter] at h2
  refine ⟨_, _, h1, fun x hx => ?_, h2⟩
  have hxj : x j < b j := (mem_box.mp hx j).2
  exact ⟨reflExt_of_lt hxj, fun i => reflExtGrad_of_lt hxj⟩

/-- Extension across the lower face `x_j = a_j` of a box (conjugate the upper extension by the
reflection). -/
theorem exists_ext_lower {a b : ι → ℝ} (j : ι) (hab : a j ≤ b j) {u : (ι → ℝ) → ℂ}
    {g : ι → (ι → ℝ) → ℂ} (hW : MemW12 (box a b) u g) :
    ∃ (U : (ι → ℝ) → ℂ) (G : ι → (ι → ℝ) → ℂ),
      MemW12 (box (Function.update a j (2 * a j - b j)) b) U G ∧
      (∀ x ∈ box a b, U x = u x ∧ ∀ i, G i x = g i x) ∧
      w12Norm (box (Function.update a j (2 * a j - b j)) b) U G ≤ 2 * w12Norm (box a b) u g := by
  set c := a j
  set a₁ := Function.update a j (2 * a j - b j)
  set b₁ := Function.update b j c
  -- the reflected box is the lower half of the symmetric box
  have hpre : refl j c ⁻¹' box a b = box a₁ b₁ := by
    ext x
    simp only [mem_preimage, mem_box]
    constructor
    · intro h i
      by_cases hi : i = j
      · subst hi
        have := h i
        rw [refl_apply_self] at this
        simp only [a₁, b₁, Function.update_self]
        constructor <;> linarith [this.1, this.2]
      · have := h i; rw [refl_apply_ne hi] at this
        simp only [a₁, b₁, Function.update_of_ne hi]; exact this
    · intro h i
      by_cases hi : i = j
      · subst hi
        have := h i
        simp only [a₁, b₁, Function.update_self] at this
        rw [refl_apply_self]
        constructor <;> linarith [this.1, this.2]
      · have := h i; simp only [a₁, b₁, Function.update_of_ne hi] at this
        rw [refl_apply_ne hi]; exact this
  obtain ⟨hv, hvn⟩ := hW.comp_refl j c
  rw [hpre] at hv hvn
  have hb₁ : b₁ j = c := by simp [b₁]
  have hupd : Function.update b₁ j (2 * b₁ j - a₁ j) = b := by
    funext i
    by_cases hi : i = j
    · subst hi; simp only [a₁, b₁, c, Function.update_self]; ring
    · simp [b₁, Function.update_of_ne hi]
  obtain ⟨V, GV, hV, hVagree, hVn⟩ := exists_ext_upper j (by simp [a₁, b₁, c]; linarith) hv
  rw [hupd] at hV hVn
  -- the symmetric box is invariant
  have hsym : refl j c ⁻¹' box a₁ b = box a₁ b := by
    ext x
    simp only [mem_preimage, mem_box]
    constructor
    · intro h i
      by_cases hi : i = j
      · subst hi
        have := h i
        rw [refl_apply_self] at this
        simp only [a₁, Function.update_self] at this ⊢
        constructor <;> linarith [this.1, this.2]
      · have := h i; rwa [refl_apply_ne hi] at this
    · intro h i
      by_cases hi : i = j
      · subst hi
        have := h i
        rw [refl_apply_self]
        simp only [a₁, Function.update_self] at this ⊢
        constructor <;> linarith [this.1, this.2]
      · rw [refl_apply_ne hi]; exact h i
  obtain ⟨hU, hUn⟩ := hV.comp_refl j c
  rw [hsym] at hU hUn
  refine ⟨_, _, hU, fun x hx => ?_, ?_⟩
  · have hRx : refl j c x ∈ box a₁ b₁ := by rw [← hpre]; simpa [refl_refl] using hx
    obtain ⟨e1, e2⟩ := hVagree _ hRx
    refine ⟨by rw [e1, refl_refl], fun i => ?_⟩
    rw [e2 i, refl_refl, ← mul_assoc, ← Complex.ofReal_mul, reflSign_sq, Complex.ofReal_one,
      one_mul]
  · rw [hUn]; exact hVn.trans (by rw [hvn])

/-- Lower corner of the iterated reflected box. -/
def extA (a b : ι → ℝ) (S : Finset ι) : ι → ℝ := fun i => if i ∈ S then 3 * a i - 2 * b i else a i

/-- Upper corner of the iterated reflected box. -/
def extB (a b : ι → ℝ) (S : Finset ι) : ι → ℝ := fun i => if i ∈ S then 2 * b i - a i else b i

theorem extA_le {a b : ι → ℝ} (hab : ∀ i, a i < b i) (S : Finset ι) (i : ι) :
    extA a b S i ≤ a i := by
  unfold extA; split_ifs <;> linarith [hab i]

theorem le_extB {a b : ι → ℝ} (hab : ∀ i, a i < b i) (S : Finset ι) (i : ι) :
    b i ≤ extB a b S i := by
  unfold extB; split_ifs <;> linarith [hab i]

/-- Iterated reflection over a finite set of coordinates. -/
theorem exists_ext_iter {a b : ι → ℝ} (hab : ∀ i, a i < b i) (S : Finset ι) :
    ∀ (u : (ι → ℝ) → ℂ) (g : ι → (ι → ℝ) → ℂ), MemW12 (box a b) u g →
      ∃ (U : (ι → ℝ) → ℂ) (G : ι → (ι → ℝ) → ℂ),
        MemW12 (box (extA a b S) (extB a b S)) U G ∧
        (∀ x ∈ box a b, U x = u x ∧ ∀ i, G i x = g i x) ∧
        w12Norm (box (extA a b S) (extB a b S)) U G ≤ 4 ^ S.card * w12Norm (box a b) u g := by
  induction S using Finset.induction_on with
  | empty =>
    intro u g hW
    have hA : extA a b ∅ = a := by funext i; simp [extA]
    have hB : extB a b ∅ = b := by funext i; simp [extB]
    rw [hA, hB]
    exact ⟨u, g, hW, fun x _ => ⟨rfl, fun _ => rfl⟩, by simp⟩
  | insert j S hj ih =>
    intro u g hW
    obtain ⟨U, G, hU, hUa, hUn⟩ := ih u g hW
    have hAj : extA a b S j = a j := by simp [extA, hj]
    have hBj : extB a b S j = b j := by simp [extB, hj]
    obtain ⟨U1, G1, hU1, hU1a, hU1n⟩ := exists_ext_upper j
      (by rw [hAj, hBj]; exact (hab j).le) hU
    obtain ⟨U2, G2, hU2, hU2a, hU2n⟩ := exists_ext_lower j
      (by simp only [Function.update_self, hAj, hBj]; linarith [hab j]) hU1
    have hA' : Function.update (extA a b S) j
        (2 * extA a b S j - Function.update (extB a b S) j (2 * extB a b S j - extA a b S j) j) =
        extA a b (insert j S) := by
      funext i
      by_cases hi : i = j
      · subst hi; simp [extA, extB, hj]; ring
      · simp [extA, Function.update_of_ne hi, hi]
    have hB' : Function.update (extB a b S) j (2 * extB a b S j - extA a b S j) =
        extB a b (insert j S) := by
      funext i
      by_cases hi : i = j
      · subst hi; simp [extA, extB, hj]
      · simp [extB, Function.update_of_ne hi, hi]
    rw [hA', hB'] at hU2 hU2n
    rw [hB'] at hU1n
    have hsub1 : box a b ⊆ box (extA a b S) (extB a b S) :=
      box_mono (extA_le hab S) (le_extB hab S)
    have hsub2 : box (extA a b S) (extB a b S) ⊆
        box (extA a b S) (Function.update (extB a b S) j (2 * extB a b S j - extA a b S j)) := by
      refine box_mono (fun i => le_rfl) fun i => ?_
      by_cases hi : i = j
      · subst hi; rw [Function.update_self, hAj, hBj]; linarith [hab i]
      · rw [Function.update_of_ne hi]
    refine ⟨U2, G2, hU2, fun x hx => ?_, ?_⟩
    · obtain ⟨e1, e2⟩ := hU2a x (hsub2 (hsub1 hx))
      obtain ⟨f1, f2⟩ := hU1a x (hsub1 hx)
      obtain ⟨g1, g2⟩ := hUa x hx
      exact ⟨by rw [e1, f1, g1], fun i => by rw [e2, f2, g2]⟩
    · rw [Finset.card_insert_of_notMem hj, pow_succ]
      calc w12Norm (box (extA a b (insert j S)) (extB a b (insert j S))) U2 G2
          ≤ 2 * (2 * (4 ^ S.card * w12Norm (box a b) u g)) := by
            refine hU2n.trans ?_
            gcongr
            exact hU1n.trans (by gcongr)
        _ = 4 ^ S.card * 4 * w12Norm (box a b) u g := by ring

/-- **Bounded extension operator for coordinate boxes.**  For a box `Q = Π (a_i, b_i)` there
are `R ≥ 0` and `C` such that every `u ∈ W^{1,2}(Q)` (weak gradient `g`) has an extension
`U ∈ W^{1,2}(ℝ^ι)` (weak gradient `G`) with `U = u`, `G = g` on `Q`, `U`, `G` vanishing outside the
ball of radius `R`, and `‖U‖_{W^{1,2}(ℝ^ι)} ≤ C ‖u‖_{W^{1,2}(Q)}`. -/
theorem exists_extension_box {a b : ι → ℝ} (hab : ∀ i, a i < b i) :
    ∃ (R : ℝ) (C : ℝ≥0), 0 ≤ R ∧ ∀ (u : (ι → ℝ) → ℂ) (g : ι → (ι → ℝ) → ℂ),
      MemW12 (box a b) u g → ∃ (U : (ι → ℝ) → ℂ) (G : ι → (ι → ℝ) → ℂ),
        MemW12 univ U G ∧ (∀ x ∈ box a b, U x = u x ∧ ∀ i, G i x = g i x) ∧
        (∀ x, R < ‖x‖ → U x = 0) ∧ (∀ i x, R < ‖x‖ → G i x = 0) ∧
        w12Norm univ U G ≤ C * w12Norm (box a b) u g := by
  set A := extA a b Finset.univ
  set B := extB a b Finset.univ
  have hK : Icc a b ⊆ box A B := fun x hx => mem_box.mpr fun i => by
    simp only [A, B, extA, extB, Finset.mem_univ, if_true]
    constructor <;> linarith [hx.1 i, hx.2 i, hab i]
  obtain ⟨χ, hχ, hχ1, -⟩ := exists_cutoff (isOpen_box A B) isCompact_Icc hK
  obtain ⟨R, C, hR, hχ0, hpd0, hcut⟩ := cutoff_ball (isOpen_box A B) hχ
  refine ⟨R, C * 4 ^ Fintype.card ι, hR, fun u g hW => ?_⟩
  obtain ⟨U, G, hU, hUa, hUn⟩ := exists_ext_iter hab Finset.univ u g hW
  obtain ⟨hV, hVn⟩ := hcut U G hU
  refine ⟨_, _, hV, fun x hx => ?_, fun x hx => by simp [hχ0 x hx],
    fun i x hx => by simp [hχ0 x hx, hpd0 i x hx], ?_⟩
  · have hxK : x ∈ Icc a b := box_subset_Icc a b hx
    have hev : χ =ᶠ[𝓝 x] fun _ => 1 :=
      (hχ1.filter_mono (nhds_le_nhdsSet hxK))
    have hχx : χ x = 1 := hev.self_of_nhds
    have hpdx : ∀ i, pd χ i x = 0 := fun i => by
      unfold pd; rw [hev.fderiv_eq]; simp
    obtain ⟨e1, e2⟩ := hUa x hx
    exact ⟨by simp [hχx, e1], fun i => by simp [hχx, hpdx i, e2 i]⟩
  · refine hVn.trans ?_
    rw [Finset.card_univ] at hUn
    calc (C : ℝ≥0∞) * w12Norm (box A B) U G ≤ C * (4 ^ Fintype.card ι * w12Norm (box a b) u g) := by
          gcongr
      _ = ((C * 4 ^ Fintype.card ι : ℝ≥0) : ℝ≥0∞) * w12Norm (box a b) u g := by
          push_cast; ring

end RenewalGeometry.SobolevOpen
