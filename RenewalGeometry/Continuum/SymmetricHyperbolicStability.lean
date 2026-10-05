/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.SymmetricHyperbolicEnergy

/-!
# Stability of symmetric hyperbolic systems: Cauchy sequences in `C_t L²`, `C_t H¹` and `H¹`

Generic infrastructure (no renewal notions) for `prop:dirac-stability` of the
Einstein–Standard-Model action-closure manuscript, on the slab `[t₀,t₁] × 𝕋^d` (`ℤ^d`-periodic
fields on `ℝ^{1+d}`, fundamental domain `slabFundD t₀ t₁ = [t₀,t₁] × [0,1)^d`).

* Slab Lebesgue calculus: `lintegral_cyl` (Tonelli for cylinders `I × S`),
  `lintegral_slabFund_eq` (`∫_{slab} ‖f‖² = ∫_{t₀}^{t₁} ∫_{[0,1]^d} ‖f(τ,y)‖²` for `f` continuous on
  the closed slab), and the real `L²(slab)` seminorm `nrm` with its triangle inequality.
* `nrm_le_of_le_add_nonmeas` (**measurable minorant**): a measurable `f` with
  `‖f‖ ≤ ‖g‖ + h` a.e., `g` arbitrary (possibly non-measurable, as a residual containing the
  non-measurable product `B_h Ψ_h` of the encoding) and `‖g‖_{L²} ≤ δ` has `‖f‖_{L²} ≤ δ + ‖h‖_{L²}`.
* `StabHyp`: a sequence `ψ_n` of `C²` periodic solutions of symmetric hyperbolic systems
  `A_n^μ ∂_μψ_n + B_nψ_n = r_n` (residual defined by the equation) with uniformly positive `A_n⁰`,
  uniform `W^{1,∞}` bounds on `A_n^μ`, `L^∞` bounds on `B_n`, uniform `L^∞_t H²_x` bounds on `ψ_n`,
  coefficients Cauchy in `L^∞`, initial data Cauchy in `L²`, residuals Cauchy in `L²_t L²_x`.
* **`StabHyp.cauchy`** (`prop:dirac-stability`, generic form): `ψ_n` is Cauchy in `C_t L²_x`, its
  spatial derivatives are Cauchy in `C_t L²_x` (`C_t H¹_x`, by interpolation between `L²` and the
  uniform `H²` bound), and its time derivative is Cauchy in `L²_t L²_x`; hence `ψ_n` is Cauchy in
  `H¹(I × Σ)`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff

noncomputable section

namespace RenewalGeometry.SymHypEnergy

open PeriodicCube
open SobolevOpen (pd)

set_option linter.unusedSectionVars false

variable {d : ℕ}

/-! ### Lebesgue calculus on the slab -/

/-- The cube `[0,1)^d`. -/
def cubeD (d : ℕ) : Set (Fin d → ℝ) := univ.pi fun _ => Ico 0 1

/-- The fundamental domain `[t₀,t₁] × [0,1)^d` of the slab. -/
def slabFundD (t₀ t₁ : ℝ) : Set (Fin (d + 1) → ℝ) :=
  {x | x 0 ∈ Icc t₀ t₁ ∧ ∀ i : Fin d, x i.succ ∈ Ico 0 1}

/-- The cylinder `{x | x₀ ∈ I, (x₁,…,x_d) ∈ S}`. -/
def cyl (I : Set ℝ) (S : Set (Fin d → ℝ)) : Set (Fin (d + 1) → ℝ) :=
  {x | x 0 ∈ I ∧ Fin.tail x ∈ S}

theorem cyl_eq_preimage (I : Set ℝ) (S : Set (Fin d → ℝ)) :
    cyl I S = (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0) ⁻¹' (I ×ˢ S) := by
  ext x
  simp [cyl, MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv]

theorem slabFundD_eq (t₀ t₁ : ℝ) : slabFundD (d := d) t₀ t₁ = cyl (Icc t₀ t₁) (cubeD d) := by
  ext x
  simp [slabFundD, cyl, cubeD, Fin.tail]

theorem piFinSuccAbove_symm_zero (t : ℝ) (y : Fin d → ℝ) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0).symm (t, y) = Fin.cons t y := by
  simp [MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv, Fin.insertNth_zero']

theorem measurableSet_cyl {I : Set ℝ} {S : Set (Fin d → ℝ)} (hI : MeasurableSet I)
    (hS : MeasurableSet S) : MeasurableSet (cyl I S) := by
  rw [cyl_eq_preimage]
  exact (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0).measurable (hI.prod hS)

/-- **Tonelli on a cylinder.** -/
theorem lintegral_cyl {I : Set ℝ} {S : Set (Fin d → ℝ)} (hI : MeasurableSet I)
    (hS : MeasurableSet S) (g : (Fin (d + 1) → ℝ) → ℝ≥0∞)
    (hg : AEMeasurable g (volume.restrict (cyl I S))) :
    ∫⁻ x in cyl I S, g x = ∫⁻ t in I, ∫⁻ y in S, g (Fin.cons t y) := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0 with he
  have hmp : MeasurePreserving e volume (volume.prod volume) :=
    volume_preserving_piFinSuccAbove (fun _ : Fin (d + 1) => ℝ) 0
  have hsymm : MeasurePreserving e.symm (volume.prod volume) volume := hmp.symm e
  rw [cyl_eq_preimage]
  have h1 : ∫⁻ x in e ⁻¹' (I ×ˢ S), g x = ∫⁻ x in e ⁻¹' (I ×ˢ S), (g ∘ e.symm) (e x) := by
    simp
  rw [h1, hmp.setLIntegral_comp_preimage_emb e.measurableEmbedding, ← Measure.prod_restrict]
  have hae : AEMeasurable (g ∘ e.symm) ((volume.restrict I).prod (volume.restrict S)) := by
    rw [Measure.prod_restrict]
    have hres := hsymm.restrict_preimage_emb e.symm.measurableEmbedding (e ⁻¹' (I ×ˢ S))
    have hpre : e.symm ⁻¹' (e ⁻¹' (I ×ˢ S)) = I ×ˢ S := by
      ext p; simp
    rw [hpre] at hres
    have hset : e ⁻¹' (I ×ˢ S) = cyl I S := (cyl_eq_preimage I S).symm
    rw [hset] at hres
    exact AEMeasurable.comp_quasiMeasurePreserving hg hres.quasiMeasurePreserving
  rw [lintegral_prod _ hae]
  simp only [Function.comp_apply, he, piFinSuccAbove_symm_zero]

theorem measurableSet_slabFundD (t₀ t₁ : ℝ) : MeasurableSet (slabFundD (d := d) t₀ t₁) := by
  rw [slabFundD_eq]
  exact measurableSet_cyl measurableSet_Icc (MeasurableSet.univ_pi fun _ => measurableSet_Ico)

theorem slabFundD_subset (t₀ t₁ : ℝ) : slabFundD (d := d) t₀ t₁ ⊆ slab t₀ t₁ := fun _ hx => hx.1

theorem cubeD_ae_eq : cubeD d =ᵐ[volume] Icc (0 : Fin d → ℝ) 1 := by
  rw [cubeD, volume_pi]
  exact Measure.univ_pi_Ico_ae_eq_Icc

theorem slabFundD_subset_compact (t₀ t₁ : ℝ) :
    slabFundD (d := d) t₀ t₁ ⊆ (fun p : ℝ × (Fin d → ℝ) => (Fin.cons p.1 p.2 : Fin (d + 1) → ℝ))
      '' (Icc t₀ t₁ ×ˢ Icc 0 1) := by
  intro x hx
  refine ⟨(x 0, Fin.tail x), ⟨hx.1, fun i => (hx.2 i).1, fun i => (hx.2 i).2.le⟩, ?_⟩
  simp

/-- Functions continuous on the closed slab are in `L²` of the fundamental domain. -/
theorem memLp_slab {F : Type*} [NormedAddCommGroup F] {f : (Fin (d + 1) → ℝ) → F} {t₀ t₁ : ℝ}
    (hf : ContinuousOn f (slab t₀ t₁)) :
    MemLp f 2 (volume.restrict (slabFundD (d := d) t₀ t₁)) := by
  set K := (fun p : ℝ × (Fin d → ℝ) => (Fin.cons p.1 p.2 : Fin (d + 1) → ℝ))
    '' (Icc t₀ t₁ ×ˢ Icc 0 1)
  have hK : IsCompact K := (isCompact_Icc.prod isCompact_Icc).image continuous_cons2
  have hKs : K ⊆ slab t₀ t₁ := by
    rintro _ ⟨p, hp, rfl⟩
    exact (cons_mem_slab _).mpr hp.1
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hf.mono hKs)
  haveI : IsFiniteMeasure (volume.restrict (slabFundD (d := d) t₀ t₁)) := by
    refine isFiniteMeasure_restrict.mpr (ne_top_of_le_ne_top ?_
      (measure_mono (slabFundD_subset_compact t₀ t₁)))
    exact hK.measure_lt_top.ne
  refine MemLp.of_bound ((hf.mono (slabFundD_subset t₀ t₁)).aestronglyMeasurable
    (measurableSet_slabFundD t₀ t₁)) C ?_
  exact ae_restrict_of_forall_mem (measurableSet_slabFundD t₀ t₁) fun x hx =>
    hC x (slabFundD_subset_compact t₀ t₁ hx)

theorem eLpNorm_two_sq {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F] (f : α → F)
    (μ : Measure α) : eLpNorm f 2 μ ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
  simp only [ENNReal.toReal_ofNat, one_div]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- `∫_{slab} ‖f‖² = ∫_{t₀}^{t₁} ∫_{[0,1]^d} ‖f(τ, y)‖² dy dτ` for `f` continuous on the slab. -/
theorem lintegral_slabFund_eq {F : Type*} [NormedAddCommGroup F] {f : (Fin (d + 1) → ℝ) → F}
    {t₀ t₁ : ℝ} (h01 : t₀ ≤ t₁) (hf : ContinuousOn f (slab t₀ t₁)) :
    ∫⁻ x in slabFundD t₀ t₁, ‖f x‖ₑ ^ 2 =
      ENNReal.ofReal (∫ τ in t₀..t₁, ∫ y in Icc (0 : Fin d → ℝ) 1, ‖f (Fin.cons τ y)‖ ^ 2) := by
  have hmeas : AEMeasurable (fun x => ‖f x‖ₑ ^ 2) (volume.restrict (slabFundD (d := d) t₀ t₁)) :=
    ((hf.mono (slabFundD_subset t₀ t₁)).aestronglyMeasurable
      (measurableSet_slabFundD t₀ t₁)).enorm.pow_const 2
  rw [slabFundD_eq] at hmeas ⊢
  rw [lintegral_cyl (S := cubeD d) measurableSet_Icc
    (MeasurableSet.univ_pi fun _ => measurableSet_Ico) _ hmeas]
  have hinner : ∀ t ∈ Icc t₀ t₁, ∫⁻ y in cubeD d, ‖f (Fin.cons t y)‖ₑ ^ 2 =
      ENNReal.ofReal (∫ y in Icc (0 : Fin d → ℝ) 1, ‖f (Fin.cons t y)‖ ^ 2) := by
    intro t ht
    have hc : Continuous fun y : Fin d → ℝ => f (Fin.cons t y) := continuous_slice hf ht
    rw [setLIntegral_congr cubeD_ae_eq, ofReal_integral_eq_lintegral_ofReal
      (f := fun y => ‖f (Fin.cons t y)‖ ^ 2)
      (integrableOn_cube_of_continuousOn (hc.norm.pow 2).continuousOn)
      (Eventually.of_forall fun y => sq_nonneg _)]
    refine setLIntegral_congr_fun measurableSet_Icc fun y _ => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  rw [setLIntegral_congr_fun measurableSet_Icc hinner]
  have hcont : ContinuousOn (fun t => ∫ y in Icc (0 : Fin d → ℝ) 1, ‖f (Fin.cons t y)‖ ^ 2)
      (Icc t₀ t₁) :=
    continuousOn_sliceIntegral (Φ := fun x => ‖f x‖ ^ 2) h01 (hf.norm.pow 2)
  rw [← ofReal_integral_eq_lintegral_ofReal (hcont.integrableOn_compact isCompact_Icc)
    (ae_restrict_of_forall_mem measurableSet_Icc fun t _ =>
      setIntegral_nonneg measurableSet_Icc fun y _ => sq_nonneg _),
    intervalIntegral.integral_of_le h01, integral_Icc_eq_integral_Ioc]

/-! ### The real `L²(slab)` seminorm -/

/-- The `L²` seminorm on the fundamental domain of the slab, as a real number. -/
def nrm {F : Type*} [NormedAddCommGroup F] (t₀ t₁ : ℝ) (f : (Fin (d + 1) → ℝ) → F) : ℝ :=
  (eLpNorm f 2 (volume.restrict (slabFundD (d := d) t₀ t₁))).toReal

theorem nrm_nonneg {F : Type*} [NormedAddCommGroup F] (t₀ t₁ : ℝ)
    (f : (Fin (d + 1) → ℝ) → F) : 0 ≤ nrm t₀ t₁ f := ENNReal.toReal_nonneg

theorem nrm_sq_eq {F : Type*} [NormedAddCommGroup F] {f : (Fin (d + 1) → ℝ) → F} {t₀ t₁ : ℝ}
    (h01 : t₀ ≤ t₁) (hf : ContinuousOn f (slab t₀ t₁)) :
    nrm t₀ t₁ f ^ 2 = ∫ τ in t₀..t₁, ∫ y in Icc (0 : Fin d → ℝ) 1, ‖f (Fin.cons τ y)‖ ^ 2 := by
  unfold nrm
  rw [← ENNReal.toReal_pow, eLpNorm_two_sq, lintegral_slabFund_eq h01 hf, ENNReal.toReal_ofReal]
  refine intervalIntegral.integral_nonneg h01 fun τ _ => ?_
  exact setIntegral_nonneg measurableSet_Icc fun y _ => sq_nonneg _

/-- If `∫_{[0,1]^d} ‖f(t)‖² ≤ C` for all `t ∈ [t₀,t₁]`, then `‖f‖²_{L²(slab)} ≤ (t₁ - t₀) C`. -/
theorem nrm_sq_le {F : Type*} [NormedAddCommGroup F] {f : (Fin (d + 1) → ℝ) → F} {t₀ t₁ C : ℝ}
    (h01 : t₀ ≤ t₁) (hf : ContinuousOn f (slab t₀ t₁))
    (hC : ∀ t ∈ Icc t₀ t₁, ∫ y in Icc (0 : Fin d → ℝ) 1, ‖f (Fin.cons t y)‖ ^ 2 ≤ C) :
    nrm t₀ t₁ f ^ 2 ≤ (t₁ - t₀) * C := by
  rw [nrm_sq_eq h01 hf]
  have := intervalIntegral.integral_mono_on h01
    ((continuousOn_sliceIntegral (Φ := fun x => ‖f x‖ ^ 2) h01 (hf.norm.pow 2)).intervalIntegrable_of_Icc h01)
    (intervalIntegrable_const (μ := volume)) hC
  simpa [mul_comm] using this

theorem nrm_le_of_sq_le {F : Type*} [NormedAddCommGroup F] {f : (Fin (d + 1) → ℝ) → F}
    {t₀ t₁ C : ℝ} (h01 : t₀ ≤ t₁) (hf : ContinuousOn f (slab t₀ t₁)) (hC0 : 0 ≤ C)
    (hC : ∀ t ∈ Icc t₀ t₁, ∫ y in Icc (0 : Fin d → ℝ) 1, ‖f (Fin.cons t y)‖ ^ 2 ≤ C) :
    nrm t₀ t₁ f ≤ Real.sqrt ((t₁ - t₀) * C) :=
  Real.le_sqrt_of_sq_le (nrm_sq_le h01 hf hC)

section Seminorm

variable {t₀ t₁ : ℝ} {F : Type*} [NormedAddCommGroup F]

local notation "μS" => volume.restrict (slabFundD (d := d) t₀ t₁)

theorem nrm_le_of_ae_le {G : Type*} [NormedAddCommGroup G] {f : (Fin (d + 1) → ℝ) → F}
    {g : (Fin (d + 1) → ℝ) → G} (hg : MemLp g 2 μS) (h : ∀ᵐ x ∂μS, ‖f x‖ ≤ ‖g x‖) :
    nrm t₀ t₁ f ≤ nrm t₀ t₁ g :=
  ENNReal.toReal_mono hg.eLpNorm_ne_top (eLpNorm_mono_ae h)

theorem nrm_add_le {f g : (Fin (d + 1) → ℝ) → F} (hf : MemLp f 2 μS) (hg : MemLp g 2 μS) :
    nrm t₀ t₁ (f + g) ≤ nrm t₀ t₁ f + nrm t₀ t₁ g := by
  unfold nrm
  rw [← ENNReal.toReal_add hf.eLpNorm_ne_top hg.eLpNorm_ne_top]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hf.eLpNorm_ne_top, hg.eLpNorm_ne_top⟩)
    (eLpNorm_add_le hf.1 hg.1 (by norm_num))

theorem nrm_const_mul (c : ℝ) (f : (Fin (d + 1) → ℝ) → ℝ) :
    nrm t₀ t₁ (fun x => c * f x) = |c| * nrm t₀ t₁ f := by
  unfold nrm
  have : (fun x => c * f x) = c • f := rfl
  rw [this, eLpNorm_const_smul, ENNReal.toReal_mul, Real.enorm_eq_ofReal_abs,
    ENNReal.toReal_ofReal (abs_nonneg c)]

theorem nrm_norm (f : (Fin (d + 1) → ℝ) → F) :
    nrm t₀ t₁ (fun x => ‖f x‖) = nrm t₀ t₁ f := by
  unfold nrm; rw [eLpNorm_norm]

/-- Pointwise domination by a finite sum of `L²` real functions. -/
theorem nrm_le_sum {ι : Type*} (s : Finset ι) {f : (Fin (d + 1) → ℝ) → F}
    {g : ι → (Fin (d + 1) → ℝ) → ℝ} (hg : ∀ i ∈ s, MemLp (g i) 2 μS)
    (h : ∀ᵐ x ∂μS, ‖f x‖ ≤ ∑ i ∈ s, g i x) :
    nrm t₀ t₁ f ≤ ∑ i ∈ s, nrm t₀ t₁ (g i) := by
  classical
  have hsum : MemLp (fun x => ∑ i ∈ s, g i x) 2 μS := by
    have := memLp_finsetSum' s hg
    convert this using 1
    funext x; simp
  refine (nrm_le_of_ae_le hsum (h.mono fun x hx => hx.trans (le_abs_self _))).trans ?_
  have he : (fun x => ∑ i ∈ s, g i x) = ∑ i ∈ s, g i := by funext x; simp
  unfold nrm
  rw [he, ← ENNReal.toReal_sum fun i hi => (hg i hi).eLpNorm_ne_top]
  exact ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr fun i hi => (hg i hi).eLpNorm_ne_top)
    (eLpNorm_sum_le (fun i hi => (hg i hi).1) (by norm_num))

theorem nrm_finset_sum_le {ι : Type*} (s : Finset ι) {g : ι → (Fin (d + 1) → ℝ) → ℝ}
    (hg : ∀ i ∈ s, MemLp (g i) 2 μS) :
    nrm t₀ t₁ (fun x => ∑ i ∈ s, g i x) ≤ ∑ i ∈ s, nrm t₀ t₁ (g i) := by
  have he : (fun x => ∑ i ∈ s, g i x) = ∑ i ∈ s, g i := by funext x; simp
  unfold nrm
  rw [he, ← ENNReal.toReal_sum fun i hi => (hg i hi).eLpNorm_ne_top]
  exact ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr fun i hi => (hg i hi).eLpNorm_ne_top)
    (eLpNorm_sum_le (fun i hi => (hg i hi).1) (by norm_num))

/-- **Measurable minorant.**  If `f` is measurable, `‖f‖ ≤ ‖g‖ + h` a.e. with `g` arbitrary
(possibly non-measurable) and `h ≥ 0` in `L²`, and `‖g‖_{L²} ≤ δ`, then `‖f‖_{L²} ≤ δ + ‖h‖_{L²}`. -/
theorem nrm_le_of_le_add_nonmeas {G : Type*} [NormedAddCommGroup G]
    {f : (Fin (d + 1) → ℝ) → F} {g : (Fin (d + 1) → ℝ) → G} {h : (Fin (d + 1) → ℝ) → ℝ}
    (hf : AEStronglyMeasurable f μS) (hh : MemLp h 2 μS) {δ : ℝ} (hδ : 0 ≤ δ)
    (hg : eLpNorm g 2 μS ≤ ENNReal.ofReal δ) (hle : ∀ᵐ x ∂μS, ‖f x‖ ≤ ‖g x‖ + h x) :
    nrm t₀ t₁ f ≤ δ + nrm t₀ t₁ h := by
  set k : (Fin (d + 1) → ℝ) → ℝ := fun x => max (‖f x‖ - h x) 0 with hk
  have hkm : AEStronglyMeasurable k μS := (hf.norm.sub hh.1).sup aestronglyMeasurable_const
  have hkg : eLpNorm k 2 μS ≤ ENNReal.ofReal δ := by
    refine (eLpNorm_mono_ae (hle.mono fun x hx => ?_)).trans hg
    rw [hk, Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact max_le (by linarith) (norm_nonneg _)
  have hkL : MemLp k 2 μS := ⟨hkm, (hkg.trans_lt ENNReal.ofReal_lt_top)⟩
  have hk1 : nrm t₀ t₁ k ≤ δ := by
    unfold nrm
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hkg).trans (ENNReal.toReal_ofReal hδ).le
  have hfk : ∀ᵐ x ∂μS, ‖f x‖ ≤ ∑ i ∈ ({0, 1} : Finset (Fin 2)), ![k, h] i x := by
    have hh0 : ∀ᵐ x ∂μS, ‖f x‖ ≤ k x + h x :=
      Eventually.of_forall fun x => by
        simp only [hk]
        have := le_max_left (‖f x‖ - h x) 0
        linarith
    filter_upwards [hh0] with x hx
    simpa using hx
  have := nrm_le_sum ({0, 1} : Finset (Fin 2)) (g := ![k, h]) (fun i _ => by
    fin_cases i
    · exact hkL
    · exact hh) hfk
  simp at this
  linarith

end Seminorm

/-! ### Generic calculus helpers -/

theorem pd_sub' {ι E : Type*} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : (ι → ℝ) → E} {x : ι → ℝ} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (i : ι) : pd (f - g) i x = pd f i x - pd g i x := by
  unfold SobolevOpen.pd
  rw [fderiv_sub hf hg]
  rfl

theorem pd_apply' {ι N : Type*} [Fintype ι] [DecidableEq ι] [Fintype N] {G : (ι → ℝ) → N → ℂ} {y : ι → ℝ}
    (hG : DifferentiableAt ℝ G y) (k : N) (j : ι) :
    pd (fun y => G y k) j y = pd G j y k := by
  unfold SobolevOpen.pd
  have h := ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : N => ℂ) k).hasFDerivAt).comp y
    hG.hasFDerivAt
  rw [show (fun y => G y k) = (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : N => ℂ) k) ∘ G
    from rfl, h.fderiv]
  rfl

/-! ### The stability hypotheses -/

variable {N : Type*} [Fintype N]

/-- The residual `r = A^μ ∂_μψ + Bψ` defined by the equation. -/
def resid (A : Fin (d + 1) → (Fin (d + 1) → ℝ) → N → N → ℂ) (B : (Fin (d + 1) → ℝ) → N → N → ℂ)
    (ψ : (Fin (d + 1) → ℝ) → N → ℂ) (x : Fin (d + 1) → ℝ) : N → ℂ :=
  princ A ψ x + mv (B x) (ψ x)

/-- **Hypotheses of `prop:dirac-stability`** (generic form, on `[t₀,t₁] × 𝕋^d`): `C²` periodic
solutions `ψ_n` on the open slab `(a,b) × ℝ^d` of symmetric hyperbolic systems
`A_n^μ ∂_μψ_n + B_nψ_n = r_n` with Hermitian `A_n^μ`, uniformly positive `A_n⁰ ≥ c`, uniform
`W^{1,∞}` bounds on `A_n^μ` (`‖A‖ ≤ C_b`, `C_b`-Lipschitz), `‖B_n‖ ≤ C_b` a.e., uniform
`L^∞_t H²_x` bounds on `ψ_n` (in the form used: values, first and pure second spatial derivatives
in `L²` uniformly in time), coefficients Cauchy in `L^∞`, initial data Cauchy in `L²(𝕋^d)`,
residuals Cauchy in `L²_t L²_x` (with no measurability assumed on `B_n` or `r_n`). -/
structure StabHyp (ψ : ℕ → (Fin (d + 1) → ℝ) → N → ℂ)
    (A : ℕ → Fin (d + 1) → (Fin (d + 1) → ℝ) → N → N → ℂ) (B : ℕ → (Fin (d + 1) → ℝ) → N → N → ℂ)
    (a t₀ t₁ b c : ℝ) (Cb : ℝ≥0) : Prop where
  ha : a < t₀
  h01 : t₀ < t₁
  hb : t₁ < b
  smooth : ∀ n, ContDiffOn ℝ 2 (ψ n) (openSlab a b)
  ψper : ∀ n, IsSPeriodic (ψ n)
  Aper : ∀ n μ, IsSPeriodic (A n μ)
  herm : ∀ n μ x i k, A n μ x k i = star (A n μ x i k)
  hc : 0 < c
  pos : ∀ n, ∀ x ∈ slab t₀ t₁, ∀ ξ : N → ℂ, c * ∑ i, ‖ξ i‖ ^ 2 ≤ ip ξ (mv (A n 0 x) ξ)
  Abound : ∀ n μ, ∀ x ∈ slab t₀ t₁, ‖A n μ x‖ ≤ Cb
  Alip : ∀ n μ, LipschitzOnWith Cb (A n μ) (slab t₀ t₁)
  Bbound : ∀ n, ∀ᵐ x ∂(volume.restrict (slab t₀ t₁)), ‖B n x‖ ≤ Cb
  H0 : ∀ n, ∀ t ∈ Icc t₀ t₁, ∫ y in Icc (0 : Fin d → ℝ) 1, ‖ψ n (Fin.cons t y)‖ ^ 2 ≤ (Cb : ℝ) ^ 2
  H1 : ∀ n (j : Fin d), ∀ t ∈ Icc t₀ t₁,
    ∫ y in Icc (0 : Fin d → ℝ) 1, ‖pd (ψ n) j.succ (Fin.cons t y)‖ ^ 2 ≤ (Cb : ℝ) ^ 2
  H2 : ∀ n (j : Fin d) (k : N), ∀ t ∈ Icc t₀ t₁,
    ∫ y in Icc (0 : Fin d → ℝ) 1, ‖pd (pd (fun y => ψ n (Fin.cons t y) k) j) j y‖ ^ 2 ≤
      (Cb : ℝ) ^ 2
  coef : ∀ ε > (0 : ℝ), ∃ N₀ : ℕ, ∀ m ≥ N₀, ∀ n ≥ N₀,
    (∀ μ, ∀ x ∈ slab t₀ t₁, ‖A m μ x - A n μ x‖ ≤ ε) ∧
      ∀ᵐ x ∂(volume.restrict (slab t₀ t₁)), ‖B m x - B n x‖ ≤ ε
  init : ∀ ε > (0 : ℝ), ∃ N₀ : ℕ, ∀ m ≥ N₀, ∀ n ≥ N₀,
    ∫ y in Icc (0 : Fin d → ℝ) 1, ‖ψ m (Fin.cons t₀ y) - ψ n (Fin.cons t₀ y)‖ ^ 2 ≤ ε
  res : ∀ ε > (0 : ℝ), ∃ N₀ : ℕ, ∀ m ≥ N₀, ∀ n ≥ N₀,
    eLpNorm (resid (A m) (B m) (ψ m) - resid (A n) (B n) (ψ n)) 2
      (volume.restrict (slabFundD t₀ t₁)) ≤ ENNReal.ofReal ε

namespace StabHyp

variable {ψ : ℕ → (Fin (d + 1) → ℝ) → N → ℂ}
  {A : ℕ → Fin (d + 1) → (Fin (d + 1) → ℝ) → N → N → ℂ} {B : ℕ → (Fin (d + 1) → ℝ) → N → N → ℂ}
  {a t₀ t₁ b c : ℝ} {Cb : ℝ≥0}

local notation "μS" => volume.restrict (slabFundD (d := d) t₀ t₁)

theorem sub (h : StabHyp ψ A B a t₀ t₁ b c Cb) : slab (d := d) t₀ t₁ ⊆ openSlab a b :=
  slab_subset_openSlab h.ha h.hb

theorem diff (h : StabHyp ψ A B a t₀ t₁ b c Cb) (n : ℕ) {x : Fin (d + 1) → ℝ}
    (hx : x ∈ openSlab a b) : DifferentiableAt ℝ (ψ n) x :=
  ((h.smooth n).differentiableOn (by norm_num) x hx).differentiableAt
    ((isOpen_openSlab a b).mem_nhds hx)

theorem cont (h : StabHyp ψ A B a t₀ t₁ b c Cb) (n : ℕ) : ContinuousOn (ψ n) (slab t₀ t₁) :=
  (h.smooth n).continuousOn.mono h.sub

theorem pdcont (h : StabHyp ψ A B a t₀ t₁ b c Cb) (n : ℕ) (μ : Fin (d + 1)) :
    ContinuousOn (pd (ψ n) μ) (slab t₀ t₁) :=
  (((h.smooth n).continuousOn_fderiv_of_isOpen (isOpen_openSlab a b) (by norm_num)).clm_apply
    continuousOn_const).mono h.sub

theorem Acont (h : StabHyp ψ A B a t₀ t₁ b c Cb) (n : ℕ) (μ : Fin (d + 1)) :
    ContinuousOn (A n μ) (slab t₀ t₁) :=
  (h.Alip n μ).continuousOn

theorem princ_cont (h : StabHyp ψ A B a t₀ t₁ b c Cb) (m n : ℕ) :
    ContinuousOn (princ (A m) (ψ n)) (slab t₀ t₁) := by
  have hA := h.Acont m
  have hp := h.pdcont n
  unfold princ mv
  fun_prop

theorem ae_slab : ∀ᵐ x ∂μS, x ∈ slab (d := d) t₀ t₁ :=
  (ae_restrict_mem (measurableSet_slabFundD t₀ t₁)).mono fun _ hx => slabFundD_subset t₀ t₁ hx

theorem ae_restrict_slab {p : (Fin (d + 1) → ℝ) → Prop}
    (hp : ∀ᵐ x ∂(volume.restrict (slab (d := d) t₀ t₁)), p x) : ∀ᵐ x ∂μS, p x :=
  ae_restrict_of_ae_restrict_of_subset (slabFundD_subset t₀ t₁) hp

/-- Uniform `L²(slab)` bound of the values and spatial derivatives. -/
theorem nrm_le_U0 (h : StabHyp ψ A B a t₀ t₁ b c Cb) (n : ℕ) :
    nrm t₀ t₁ (ψ n) ≤ Real.sqrt ((t₁ - t₀) * (Cb : ℝ) ^ 2) :=
  nrm_le_of_sq_le h.h01.le (h.cont n) (by positivity) (h.H0 n)

theorem nrm_pd_le_U0 (h : StabHyp ψ A B a t₀ t₁ b c Cb) (n : ℕ) (j : Fin d) :
    nrm t₀ t₁ (pd (ψ n) j.succ) ≤ Real.sqrt ((t₁ - t₀) * (Cb : ℝ) ^ 2) :=
  nrm_le_of_sq_le h.h01.le (h.pdcont n j.succ) (by positivity) (h.H1 n j)

theorem nrm_add_le' {F : Type*} [NormedAddCommGroup F] {f g : (Fin (d + 1) → ℝ) → F}
    (hf : ContinuousOn f (slab t₀ t₁)) (hg : ContinuousOn g (slab t₀ t₁)) :
    nrm t₀ t₁ (fun x => f x + g x) ≤ nrm t₀ t₁ f + nrm t₀ t₁ g :=
  nrm_add_le (memLp_slab hf) (memLp_slab hg)

/-- The coercive bound for the time derivative:
`‖∂ₜψ‖ ≤ (|N|/c) (‖A^μ∂_μψ‖ + Σ_j |N| C_b ‖∂_jψ‖)`. -/
theorem norm_pd0_le (h : StabHyp ψ A B a t₀ t₁ b c Cb) (m : ℕ) {f : (Fin (d + 1) → ℝ) → N → ℂ}
    {x : Fin (d + 1) → ℝ} (hx : x ∈ slab t₀ t₁) :
    ‖pd f 0 x‖ ≤ (Fintype.card N : ℝ) / c * (‖princ (A m) f x‖ +
      ∑ j : Fin d, (Fintype.card N : ℝ) * Cb * ‖pd f j.succ x‖) := by
  have h1 := norm_le_of_coercive h.hc (h.pos m x hx) (pd f 0 x)
  have h2 : mv (A m 0 x) (pd f 0 x) = princ (A m) f x -
      ∑ j : Fin d, mv (A m j.succ x) (pd f j.succ x) := by
    simp only [princ, Fin.sum_univ_succ]; abel
  have h3 : ‖mv (A m 0 x) (pd f 0 x)‖ ≤ ‖princ (A m) f x‖ +
      ∑ j : Fin d, (Fintype.card N : ℝ) * Cb * ‖pd f j.succ x‖ := by
    rw [h2]
    refine (norm_sub_le _ _).trans (add_le_add_right ((norm_sum_le _ _).trans
      (Finset.sum_le_sum fun j _ => ?_)) _)
    refine (norm_mv_le _ _).trans ?_
    have := h.Abound m j.succ x hx
    calc (Fintype.card N : ℝ) * (‖A m j.succ x‖ * ‖pd f j.succ x‖)
        ≤ Fintype.card N * (Cb * ‖pd f j.succ x‖) := by gcongr
      _ = _ := by ring
  exact h1.trans (mul_le_mul_of_nonneg_left h3 (by have := h.hc; positivity))

/-- **Uniform `L²_t L²_x` bound of the time derivatives** (solve the equation for `∂ₜψ_n`,
using the uniform invertibility of `A_n⁰` and the boundedness of the residuals). -/
theorem time_bound (h : StabHyp ψ A B a t₀ t₁ b c Cb) :
    ∃ (N₁ : ℕ) (U : ℝ), ∀ n ≥ N₁, nrm t₀ t₁ (pd (ψ n) 0) ≤ U := by
  obtain ⟨N₁, hN₁⟩ := h.res 1 one_pos
  set n₀ : ℝ := (Fintype.card N : ℝ)
  set U0 := Real.sqrt ((t₁ - t₀) * (Cb : ℝ) ^ 2)
  have hc := h.hc
  have hn₀ : 0 ≤ n₀ := Nat.cast_nonneg _
  refine ⟨N₁, n₀ / c * 1 + n₀ / c * (nrm t₀ t₁ (princ (A N₁) (ψ N₁)) + n₀ * Cb * U0 +
    n₀ * Cb * nrm t₀ t₁ (ψ N₁) + ∑ _j : Fin d, n₀ * Cb * U0), fun n hn => ?_⟩
  have hres := hN₁ n hn N₁ le_rfl
  -- the a.e. pointwise bound
  set hfun : (Fin (d + 1) → ℝ) → ℝ := fun x => n₀ / c * (‖princ (A N₁) (ψ N₁) x‖ +
    n₀ * Cb * ‖ψ n x‖ + n₀ * Cb * ‖ψ N₁ x‖ + ∑ j : Fin d, n₀ * Cb * ‖pd (ψ n) j.succ x‖)
  have hcont : ContinuousOn hfun (slab t₀ t₁) := by
    have h1 := (h.princ_cont N₁ N₁).norm
    have h2 := (h.cont n).norm
    have h3 := (h.cont N₁).norm
    have h4 : ∀ j : Fin d, ContinuousOn (fun x => ‖pd (ψ n) j.succ x‖) (slab t₀ t₁) :=
      fun j => (h.pdcont n j.succ).norm
    exact continuousOn_const.mul (((h1.add (continuousOn_const.mul h2)).add
      (continuousOn_const.mul h3)).add (continuousOn_finsetSum _ fun j _ =>
        continuousOn_const.mul (h4 j)))
  have hle : ∀ᵐ x ∂μS, ‖pd (ψ n) 0 x‖ ≤
      ‖((n₀ / c) • (resid (A n) (B n) (ψ n) - resid (A N₁) (B N₁) (ψ N₁))) x‖ + hfun x := by
    filter_upwards [ae_slab, ae_restrict_slab (h.Bbound n), ae_restrict_slab (h.Bbound N₁)]
      with x hx hBn hBN
    have h1 := h.norm_pd0_le n (f := ψ n) hx
    have h2 : ‖princ (A n) (ψ n) x‖ ≤ ‖resid (A n) (B n) (ψ n) x - resid (A N₁) (B N₁) (ψ N₁) x‖ +
        ‖princ (A N₁) (ψ N₁) x‖ + n₀ * Cb * ‖ψ n x‖ + n₀ * Cb * ‖ψ N₁ x‖ := by
      have he : princ (A n) (ψ n) x = (resid (A n) (B n) (ψ n) x - resid (A N₁) (B N₁) (ψ N₁) x) +
          princ (A N₁) (ψ N₁) x + mv (B N₁ x) (ψ N₁ x) - mv (B n x) (ψ n x) := by
        simp only [resid]; abel
      rw [he]
      have e1 := norm_mv_le (B N₁ x) (ψ N₁ x)
      have e2 := norm_mv_le (B n x) (ψ n x)
      have e3 : n₀ * (‖B N₁ x‖ * ‖ψ N₁ x‖) ≤ n₀ * Cb * ‖ψ N₁ x‖ := by
        rw [mul_assoc]; gcongr
      have e4 : n₀ * (‖B n x‖ * ‖ψ n x‖) ≤ n₀ * Cb * ‖ψ n x‖ := by
        rw [mul_assoc]; gcongr
      calc _ ≤ ‖(resid (A n) (B n) (ψ n) x - resid (A N₁) (B N₁) (ψ N₁) x) +
            princ (A N₁) (ψ N₁) x + mv (B N₁ x) (ψ N₁ x)‖ + ‖mv (B n x) (ψ n x)‖ := norm_sub_le _ _
        _ ≤ ‖resid (A n) (B n) (ψ n) x - resid (A N₁) (B N₁) (ψ N₁) x‖ +
            ‖princ (A N₁) (ψ N₁) x‖ + ‖mv (B N₁ x) (ψ N₁ x)‖ + ‖mv (B n x) (ψ n x)‖ := by
          gcongr
          exact (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
        _ ≤ _ := by linarith
    rw [Pi.smul_apply, Pi.sub_apply, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    simp only [hfun]
    have hcn : 0 ≤ n₀ / c := by positivity
    calc ‖pd (ψ n) 0 x‖ ≤ n₀ / c * (‖princ (A n) (ψ n) x‖ +
          ∑ j : Fin d, n₀ * Cb * ‖pd (ψ n) j.succ x‖) := h1
      _ ≤ n₀ / c * (‖resid (A n) (B n) (ψ n) x - resid (A N₁) (B N₁) (ψ N₁) x‖ +
          ‖princ (A N₁) (ψ N₁) x‖ + n₀ * Cb * ‖ψ n x‖ + n₀ * Cb * ‖ψ N₁ x‖ +
          ∑ j : Fin d, n₀ * Cb * ‖pd (ψ n) j.succ x‖) := by gcongr
      _ = _ := by ring
  have hg : eLpNorm ((n₀ / c) • (resid (A n) (B n) (ψ n) - resid (A N₁) (B N₁) (ψ N₁))) 2 μS ≤
      ENNReal.ofReal (n₀ / c * 1) := by
    rw [eLpNorm_const_smul, Real.enorm_eq_ofReal_abs, abs_of_nonneg (by positivity),
      ENNReal.ofReal_mul (by positivity)]
    gcongr
  have hmain := nrm_le_of_le_add_nonmeas (((h.pdcont n 0).mono (slabFundD_subset t₀ t₁)
    ).aestronglyMeasurable (measurableSet_slabFundD t₀ t₁)) (memLp_slab hcont)
    (by positivity) hg hle
  refine hmain.trans (add_le_add_right ?_ _)
  -- bound `nrm hfun`
  have hb : nrm t₀ t₁ hfun ≤ n₀ / c * (nrm t₀ t₁ (princ (A N₁) (ψ N₁)) + n₀ * Cb * U0 +
      n₀ * Cb * nrm t₀ t₁ (ψ N₁) + ∑ _j : Fin d, n₀ * Cb * U0) := by
    simp only [hfun]
    rw [nrm_const_mul, abs_of_nonneg (by positivity)]
    gcongr
    have hc1 := (h.princ_cont N₁ N₁).norm
    have hc2 : ContinuousOn (fun x => n₀ * Cb * ‖ψ n x‖) (slab t₀ t₁) :=
      continuousOn_const.mul (h.cont n).norm
    have hc3 : ContinuousOn (fun x => n₀ * Cb * ‖ψ N₁ x‖) (slab t₀ t₁) :=
      continuousOn_const.mul (h.cont N₁).norm
    have hc4 : ∀ j : Fin d, ContinuousOn (fun x => n₀ * Cb * ‖pd (ψ n) j.succ x‖) (slab t₀ t₁) :=
      fun j => continuousOn_const.mul (h.pdcont n j.succ).norm
    have hc4' : ContinuousOn (fun x => ∑ j : Fin d, n₀ * Cb * ‖pd (ψ n) j.succ x‖)
        (slab t₀ t₁) := continuousOn_finsetSum _ fun j _ => hc4 j
    refine (nrm_add_le' ((hc1.add hc2).add hc3) hc4').trans ?_
    refine add_le_add ((nrm_add_le' (hc1.add hc2) hc3).trans (add_le_add
      ((nrm_add_le' hc1 hc2).trans (add_le_add ?_ ?_)) ?_)) ?_
    · rw [nrm_norm]
    · rw [nrm_const_mul, nrm_norm, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left (h.nrm_le_U0 n) (by positivity)
    · rw [nrm_const_mul, nrm_norm, abs_of_nonneg (by positivity)]
    · have hm : ∀ j ∈ (Finset.univ : Finset (Fin d)),
          MemLp (fun x => n₀ * Cb * ‖pd (ψ n) j.succ x‖) 2 μS := fun j _ => memLp_slab (hc4 j)
      refine (nrm_finset_sum_le Finset.univ hm).trans (Finset.sum_le_sum fun j _ => ?_)
      rw [nrm_const_mul, nrm_norm, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left (h.nrm_pd_le_U0 n j) (by positivity)
  exact hb

/-- The pointwise identity for the difference `w = ψ_m - ψ_n` with the `m`-system as principal
operator: `A_m^μ∂_μ w = (r_m - r_n) - B_m w - (B_m - B_n)ψ_n - (A_m^μ - A_n^μ)∂_μψ_n`. -/
theorem diff_identity (h : StabHyp ψ A B a t₀ t₁ b c Cb) (m n : ℕ) {x : Fin (d + 1) → ℝ}
    (hx : x ∈ slab t₀ t₁) :
    princ (A m) (ψ m - ψ n) x =
      (resid (A m) (B m) (ψ m) x - resid (A n) (B n) (ψ n) x) - mv (B m x) ((ψ m - ψ n) x) -
        mv (B m x - B n x) (ψ n x) - ∑ μ, mv (A m μ x - A n μ x) (pd (ψ n) μ x) := by
  have hpd : ∀ μ, pd (ψ m - ψ n) μ x = pd (ψ m) μ x - pd (ψ n) μ x := fun μ =>
    pd_sub' (h.diff m (h.sub hx)) (h.diff n (h.sub hx)) μ
  simp only [princ, resid, hpd, mv_sub, mv_sub_left, Finset.sum_sub_distrib, Pi.sub_apply]
  abel

/-- The measurable minorant `m₀ = (‖A_m^μ∂_μw‖ - |N|C_b‖w‖)⁺` of the residual difference. -/
def m0 (ψ : ℕ → (Fin (d + 1) → ℝ) → N → ℂ) (A : ℕ → Fin (d + 1) → (Fin (d + 1) → ℝ) → N → N → ℂ)
    (Cb : ℝ≥0) (m n : ℕ) (x : Fin (d + 1) → ℝ) : ℝ :=
  max (‖princ (A m) (ψ m - ψ n) x‖ - (Fintype.card N : ℝ) * Cb * ‖(ψ m - ψ n) x‖) 0

theorem m0_cont (h : StabHyp ψ A B a t₀ t₁ b c Cb) (m n : ℕ) :
    ContinuousOn (m0 ψ A Cb m n) (slab t₀ t₁) := by
  have hw : ContinuousOn (ψ m - ψ n) (slab t₀ t₁) := (h.cont m).sub (h.cont n)
  have hP : ContinuousOn (princ (A m) (ψ m - ψ n)) (slab t₀ t₁) := by
    have hA := h.Acont m
    have hp : ∀ μ, ContinuousOn (pd (ψ m - ψ n) μ) (slab t₀ t₁) := fun μ =>
      ((h.pdcont m μ).sub (h.pdcont n μ)).congr fun x hx =>
        pd_sub' (h.diff m (h.sub hx)) (h.diff n (h.sub hx)) μ
    unfold princ mv
    fun_prop
  unfold m0
  exact ContinuousOn.sup (ContinuousOn.sub hP.norm (continuousOn_const.mul hw.norm))
    continuousOn_const

theorem m0_nonneg (m n : ℕ) (x : Fin (d + 1) → ℝ) : 0 ≤ m0 ψ A Cb m n x := le_max_right _ _

/-- The pointwise bound of the minorant by the residual difference and the coefficient
differences. -/
theorem m0_le (h : StabHyp ψ A B a t₀ t₁ b c Cb) {m n : ℕ} {ε : ℝ}
    (hA : ∀ μ, ∀ x ∈ slab t₀ t₁, ‖A m μ x - A n μ x‖ ≤ ε)
    (hB : ∀ᵐ x ∂(volume.restrict (slab t₀ t₁)), ‖B m x - B n x‖ ≤ ε) :
    ∀ᵐ x ∂μS, m0 ψ A Cb m n x ≤
      ‖(resid (A m) (B m) (ψ m) - resid (A n) (B n) (ψ n)) x‖ +
        (ε * (Fintype.card N : ℝ) * ‖ψ n x‖ +
          ∑ μ, ε * (Fintype.card N : ℝ) * ‖pd (ψ n) μ x‖) := by
  filter_upwards [ae_slab, ae_restrict_slab (h.Bbound m), ae_restrict_slab hB] with x hx hBm hBd
  set n₀ : ℝ := (Fintype.card N : ℝ)
  have hn₀ : 0 ≤ n₀ := Nat.cast_nonneg _
  have hε : 0 ≤ ε := (norm_nonneg _).trans hBd
  have hP : ‖princ (A m) (ψ m - ψ n) x‖ ≤
      ‖(resid (A m) (B m) (ψ m) - resid (A n) (B n) (ψ n)) x‖ + n₀ * Cb * ‖(ψ m - ψ n) x‖ +
        (ε * n₀ * ‖ψ n x‖ + ∑ μ, ε * n₀ * ‖pd (ψ n) μ x‖) := by
    rw [h.diff_identity m n hx]
    have e1 : ‖mv (B m x) ((ψ m - ψ n) x)‖ ≤ n₀ * Cb * ‖(ψ m - ψ n) x‖ := by
      refine (norm_mv_le _ _).trans ?_
      rw [mul_assoc]; gcongr
    have e2 : ‖mv (B m x - B n x) (ψ n x)‖ ≤ ε * n₀ * ‖ψ n x‖ := by
      refine (norm_mv_le _ _).trans ?_
      calc n₀ * (‖B m x - B n x‖ * ‖ψ n x‖) ≤ n₀ * (ε * ‖ψ n x‖) := by gcongr
        _ = _ := by ring
    have e3 : ‖∑ μ, mv (A m μ x - A n μ x) (pd (ψ n) μ x)‖ ≤ ∑ μ, ε * n₀ * ‖pd (ψ n) μ x‖ := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun μ _ => ?_)
      refine (norm_mv_le _ _).trans ?_
      calc n₀ * (‖A m μ x - A n μ x‖ * ‖pd (ψ n) μ x‖) ≤ n₀ * (ε * ‖pd (ψ n) μ x‖) := by
            gcongr; exact hA μ x hx
        _ = _ := by ring
    have e0 : ‖(resid (A m) (B m) (ψ m) x - resid (A n) (B n) (ψ n) x) - mv (B m x) ((ψ m - ψ n) x) -
        mv (B m x - B n x) (ψ n x) - ∑ μ, mv (A m μ x - A n μ x) (pd (ψ n) μ x)‖ ≤
        ‖resid (A m) (B m) (ψ m) x - resid (A n) (B n) (ψ n) x‖ + ‖mv (B m x) ((ψ m - ψ n) x)‖ +
          ‖mv (B m x - B n x) (ψ n x)‖ + ‖∑ μ, mv (A m μ x - A n μ x) (pd (ψ n) μ x)‖ := by
      refine (norm_sub_le _ _).trans (add_le_add_left ((norm_sub_le _ _).trans
        (add_le_add_left (norm_sub_le _ _) _)) _)
    simp only [Pi.sub_apply] at e0 e1 ⊢
    linarith
  unfold m0
  refine max_le ?_ (by positivity)
  linarith

/-- The `L²(slab)` bound of the minorant. -/
theorem nrm_m0_le (h : StabHyp ψ A B a t₀ t₁ b c Cb) {m n : ℕ} {ε U : ℝ} (hε : 0 ≤ ε)
    (hA : ∀ μ, ∀ x ∈ slab t₀ t₁, ‖A m μ x - A n μ x‖ ≤ ε)
    (hB : ∀ᵐ x ∂(volume.restrict (slab t₀ t₁)), ‖B m x - B n x‖ ≤ ε)
    (hR : eLpNorm (resid (A m) (B m) (ψ m) - resid (A n) (B n) (ψ n)) 2 μS ≤ ENNReal.ofReal ε)
    (hU : nrm t₀ t₁ (pd (ψ n) 0) ≤ U) :
    nrm t₀ t₁ (m0 ψ A Cb m n) ≤ ε * (1 + (Fintype.card N : ℝ) *
      (Real.sqrt ((t₁ - t₀) * (Cb : ℝ) ^ 2) + (U + ∑ _j : Fin d,
        Real.sqrt ((t₁ - t₀) * (Cb : ℝ) ^ 2)))) := by
  set n₀ : ℝ := (Fintype.card N : ℝ)
  have hn₀ : 0 ≤ n₀ := Nat.cast_nonneg _
  set U0 := Real.sqrt ((t₁ - t₀) * (Cb : ℝ) ^ 2)
  have c1 : ContinuousOn (fun x => ε * n₀ * ‖ψ n x‖) (slab t₀ t₁) :=
    continuousOn_const.mul (h.cont n).norm
  have c2 : ∀ μ, ContinuousOn (fun x => ε * n₀ * ‖pd (ψ n) μ x‖) (slab t₀ t₁) := fun μ =>
    continuousOn_const.mul (h.pdcont n μ).norm
  have c3 : ContinuousOn (fun x => ∑ μ, ε * n₀ * ‖pd (ψ n) μ x‖) (slab t₀ t₁) :=
    continuousOn_finsetSum _ fun μ _ => c2 μ
  have hmain := nrm_le_of_le_add_nonmeas (((m0_cont h m n).mono (slabFundD_subset t₀ t₁)
    ).aestronglyMeasurable (measurableSet_slabFundD t₀ t₁)) (memLp_slab (c1.add c3)) hε hR
    ((m0_le h hA hB).mono fun x hx => by
      rw [Real.norm_eq_abs, abs_of_nonneg (m0_nonneg m n x)]; exact hx)
  refine hmain.trans ?_
  have hsum : nrm t₀ t₁ (fun x => ∑ μ, ε * n₀ * ‖pd (ψ n) μ x‖) ≤
      ε * n₀ * (U + ∑ _j : Fin d, U0) := by
    have hm : ∀ μ ∈ (Finset.univ : Finset (Fin (d + 1))),
        MemLp (fun x => ε * n₀ * ‖pd (ψ n) μ x‖) 2 μS := fun μ _ => memLp_slab (c2 μ)
    refine (nrm_finset_sum_le Finset.univ hm).trans ?_
    rw [Fin.sum_univ_succ, mul_add, Finset.mul_sum]
    refine add_le_add ?_ (Finset.sum_le_sum fun j _ => ?_)
    · rw [nrm_const_mul, nrm_norm, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left hU (by positivity)
    · rw [nrm_const_mul, nrm_norm, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left (h.nrm_pd_le_U0 n j) (by positivity)
  have h1 : nrm t₀ t₁ (fun x => ε * n₀ * ‖ψ n x‖) ≤ ε * n₀ * U0 := by
    rw [nrm_const_mul, nrm_norm, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (h.nrm_le_U0 n) (by positivity)
  have h2 := nrm_add_le' (f := fun x => ε * n₀ * ‖ψ n x‖)
    (g := fun x => ∑ μ, ε * n₀ * ‖pd (ψ n) μ x‖) c1 c3
  have : ε + (ε * n₀ * U0 + ε * n₀ * (U + ∑ _j : Fin d, U0)) =
      ε * (1 + n₀ * (U0 + (U + ∑ _j : Fin d, U0))) := by ring
  simp only [Pi.add_def] at hmain ⊢
  linarith

theorem pd_diff_eq (h : StabHyp ψ A B a t₀ t₁ b c Cb) (m n : ℕ) (μ : Fin (d + 1))
    {x : Fin (d + 1) → ℝ} (hx : x ∈ slab t₀ t₁) :
    pd (ψ m - ψ n) μ x = pd (ψ m) μ x - pd (ψ n) μ x :=
  pd_sub' (h.diff m (h.sub hx)) (h.diff n (h.sub hx)) μ

theorem pd_diff_cont (h : StabHyp ψ A B a t₀ t₁ b c Cb) (m n : ℕ) (μ : Fin (d + 1)) :
    ContinuousOn (pd (ψ m - ψ n) μ) (slab t₀ t₁) :=
  ((h.pdcont m μ).sub (h.pdcont n μ)).congr fun x hx => h.pd_diff_eq m n μ hx

theorem symHyp_diff (h : StabHyp ψ A B a t₀ t₁ b c Cb) (m n : ℕ) :
    SymHyp (A m) (ψ m - ψ n) a t₀ t₁ b Cb Cb where
  ha := h.ha
  h01 := h.h01
  hb := h.hb
  smooth := ((h.smooth m).sub (h.smooth n)).of_le (by norm_num)
  wper := fun k x => by simp [h.ψper m k x, h.ψper n k x]
  Aper := h.Aper m
  herm := h.herm m
  lip := h.Alip m
  bound := h.Abound m

theorem l2sq_init_le (m n : ℕ) :
    l2sq (ψ m - ψ n) t₀ =
      ∫ y in Icc (0 : Fin d → ℝ) 1, ‖ψ m (Fin.cons t₀ y) - ψ n (Fin.cons t₀ y)‖ ^ 2 := rfl

/-- **The `C_t L²` estimate** (`eq:dirac-L2-stability` with Gronwall): there is `C` such that for
every `ε ∈ (0,1]`, eventually `sup_t ‖ψ_m(t) - ψ_n(t)‖²_{L²} ≤ Cε` (and the minorant of the
source is `O(ε)` in `L²(slab)`). -/
theorem l2_bound (h : StabHyp ψ A B a t₀ t₁ b c Cb) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ N₀ : ℕ, ∀ m ≥ N₀, ∀ n ≥ N₀,
      (∀ t ∈ Icc t₀ t₁, l2sq (ψ m - ψ n) t ≤ C * ε) ∧ nrm t₀ t₁ (m0 ψ A Cb m n) ≤ C * ε ∧
        nrm t₀ t₁ (pd (ψ n) 0) ≤ C := by
  obtain ⟨N₁, U, hU⟩ := h.time_bound
  have hU0' : 0 ≤ U := (nrm_nonneg _ _ _).trans (hU N₁ le_rfl)
  set n₀ : ℝ := (Fintype.card N : ℝ) with hn₀def
  have hn₀ : 0 ≤ n₀ := Nat.cast_nonneg _
  have hc := h.hc
  set U0 := Real.sqrt ((t₁ - t₀) * (Cb : ℝ) ^ 2)
  have hU0 : 0 ≤ U0 := Real.sqrt_nonneg _
  set Cm : ℝ := 1 + n₀ * (U0 + (U + ∑ _j : Fin d, U0)) with hCm
  have hCm0 : 0 ≤ Cm := by rw [hCm]; positivity
  set K : ℝ := ((((d : ℝ) + 1) * (n₀ ^ 2 * Cb) + n₀ * (1 + 2 * (n₀ * Cb))) / c + 1)
  set E := Real.exp (K * (t₁ - t₀))
  have hE : 0 < E := Real.exp_pos _
  set C : ℝ := max (max Cm U) (E / c * (n₀ ^ 2 * Cb + n₀ * Cm ^ 2)) with hC
  have hC0 : 0 ≤ C := le_max_of_le_left (le_max_of_le_left hCm0)
  refine ⟨C, hC0, fun ε hε hε1 => ?_⟩
  obtain ⟨Nc, hNc⟩ := h.coef ε hε
  obtain ⟨Ni, hNi⟩ := h.init ε hε
  obtain ⟨Nr, hNr⟩ := h.res ε hε
  refine ⟨max (max N₁ Nc) (max Ni Nr), fun m hm n hn => ?_⟩
  have hm1 : N₁ ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hm
  have hn1 : N₁ ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hmc : Nc ≤ m := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hm
  have hnc : Nc ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hmi : Ni ≤ m := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hm
  have hni : Ni ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hn
  have hmr : Nr ≤ m := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hm
  have hnr : Nr ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hn
  obtain ⟨hAc, hBc⟩ := hNc m hmc n hnc
  have hm0 : nrm t₀ t₁ (m0 ψ A Cb m n) ≤ ε * Cm :=
    nrm_m0_le h hε.le hAc hBc (hNr m hmr n hnr) (hU n hn1)
  have hsym := h.symHyp_diff m n
  have hF : ∀ x ∈ slab t₀ t₁, ‖princ (A m) (ψ m - ψ n) x‖ ≤
      m0 ψ A Cb m n x + n₀ * Cb * ‖(ψ m - ψ n) x‖ := by
    intro x _
    have := le_max_left (‖princ (A m) (ψ m - ψ n) x‖ - n₀ * Cb * ‖(ψ m - ψ n) x‖) 0
    simp only [m0]
    linarith
  have hen := l2_energy_estimate hsym hc (by positivity) (h.pos m) (m0_cont h m n) hF
  have hm0sq : ∫ τ in t₀..t₁, ∫ y in Icc (0 : Fin d → ℝ) 1, m0 ψ A Cb m n (Fin.cons τ y) ^ 2 =
      nrm t₀ t₁ (m0 ψ A Cb m n) ^ 2 := by
    rw [nrm_sq_eq h.h01.le (m0_cont h m n)]
    simp only [Real.norm_eq_abs, sq_abs]
  have hinit : l2sq (ψ m - ψ n) t₀ ≤ ε := by
    rw [l2sq_init_le]; exact hNi m hmi n hni
  refine ⟨fun t ht => ?_, hm0.trans (by
    rw [mul_comm]; exact mul_le_mul_of_nonneg_right (le_max_of_le_left (le_max_left _ _))
      hε.le), (hU n hn1).trans (le_max_of_le_left (le_max_right _ _))⟩
  have h1 := hen t ht
  rw [hm0sq] at h1
  have hl0 : 0 ≤ l2sq (ψ m - ψ n) t₀ :=
    setIntegral_nonneg measurableSet_Icc fun y _ => sq_nonneg _
  have hm0' : nrm t₀ t₁ (m0 ψ A Cb m n) ^ 2 ≤ (ε * Cm) ^ 2 :=
    pow_le_pow_left₀ (nrm_nonneg _ _ _) hm0 2
  have h2 : c * l2sq (ψ m - ψ n) t ≤ E * (n₀ ^ 2 * Cb * ε + n₀ * (ε * Cm) ^ 2) := by
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ hE.le)
    gcongr
  have h3 : n₀ ^ 2 * Cb * ε + n₀ * (ε * Cm) ^ 2 ≤ (n₀ ^ 2 * Cb + n₀ * Cm ^ 2) * ε := by
    have : ε ^ 2 ≤ ε := by nlinarith
    have : n₀ * (ε * Cm) ^ 2 ≤ n₀ * Cm ^ 2 * ε := by
      rw [mul_pow]
      calc n₀ * (ε ^ 2 * Cm ^ 2) ≤ n₀ * (ε * Cm ^ 2) := by gcongr
        _ = _ := by ring
    linarith
  have h4 : l2sq (ψ m - ψ n) t ≤ E / c * (n₀ ^ 2 * Cb + n₀ * Cm ^ 2) * ε := by
    have h5 : c * l2sq (ψ m - ψ n) t ≤ E * ((n₀ ^ 2 * Cb + n₀ * Cm ^ 2) * ε) :=
      h2.trans (mul_le_mul_of_nonneg_left h3 hE.le)
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hc]
    linarith
  exact h4.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hε.le)

theorem slice_comp_contDiff (h : StabHyp ψ A B a t₀ t₁ b c Cb) (n : ℕ) {t : ℝ}
    (ht : t ∈ Icc t₀ t₁) (k : N) :
    ContDiff ℝ 2 (fun y : Fin d → ℝ => ψ n (Fin.cons t y) k) := by
  have hs : ContDiff ℝ 2 (fun y : Fin d → ℝ => ψ n (Fin.cons t y)) :=
    (h.smooth n).comp_contDiff (contDiff_cons t) fun y =>
      h.sub ((cons_mem_slab y).mpr ht)
  exact contDiff_pi.mp hs k

/-- **`C_t H¹_x` by interpolation**: if `sup_t ‖w(t)‖²_{L²} ≤ Cε`, then for every spatial
direction `sup_t ‖∂_j w(t)‖²_{L²} ≤ |N| (2C_b² + C/2) √ε` (interpolation between `L²` and the
uniform `H²` bound). -/
theorem grad_bound (h : StabHyp ψ A B a t₀ t₁ b c Cb) {m n : ℕ} {C ε : ℝ} (hε : 0 < ε)
    (hl2 : ∀ t ∈ Icc t₀ t₁, l2sq (ψ m - ψ n) t ≤ C * ε) {t : ℝ} (ht : t ∈ Icc t₀ t₁)
    (j : Fin d) :
    ∫ y in Icc (0 : Fin d → ℝ) 1, ‖pd (ψ m - ψ n) j.succ (Fin.cons t y)‖ ^ 2 ≤
      (Fintype.card N : ℝ) * ((2 * (Cb : ℝ) ^ 2 + C / 2) * Real.sqrt ε) := by
  set lam := Real.sqrt ε with hlam
  have hlam0 : 0 < lam := Real.sqrt_pos.mpr hε
  have hdiff : ∀ y : Fin d → ℝ, DifferentiableAt ℝ (ψ m - ψ n) (Fin.cons t y) := fun y =>
    (h.diff m (h.sub ((cons_mem_slab y).mpr ht))).sub (h.diff n (h.sub ((cons_mem_slab y).mpr ht)))
  set g : N → (Fin d → ℝ) → ℂ := fun k y => (ψ m - ψ n) (Fin.cons t y) k with hg
  have hgm : ∀ k, ContDiff ℝ 2 (fun y : Fin d → ℝ => ψ m (Fin.cons t y) k) := fun k =>
    h.slice_comp_contDiff m ht k
  have hgn : ∀ k, ContDiff ℝ 2 (fun y : Fin d → ℝ => ψ n (Fin.cons t y) k) := fun k =>
    h.slice_comp_contDiff n ht k
  have hgeq : ∀ k, g k = (fun y => ψ m (Fin.cons t y) k) - fun y => ψ n (Fin.cons t y) k :=
    fun k => by funext y; simp [hg]
  have hgC : ∀ k, ContDiff ℝ 2 (g k) := fun k => by rw [hgeq]; exact (hgm k).sub (hgn k)
  have hgper : ∀ k, IsZPeriodic (g k) := fun k q y => by
    have e1 := (h.ψper m).slice t q y
    have e2 := (h.ψper n).slice t q y
    simp only at e1 e2
    simp only [hg, Pi.sub_apply, e1, e2]
  -- pointwise: the vector derivative is controlled by its components
  have hpt : ∀ y : Fin d → ℝ, ‖pd (ψ m - ψ n) j.succ (Fin.cons t y)‖ ^ 2 ≤
      ∑ k, ‖pd (g k) j y‖ ^ 2 := by
    intro y
    have hsd : DifferentiableAt ℝ (fun y => (ψ m - ψ n) (Fin.cons t y)) y :=
      (hdiff y).comp y ((contDiff_cons (n := 1) t).differentiable one_ne_zero y)
    rw [← pd_slice j (hdiff y)]
    refine (norm_sq_le_sum _).trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_))
    rw [← pd_apply' hsd k j]
  -- the second derivatives
  have hsec : ∀ k, ∫ y in Icc (0 : Fin d → ℝ) 1, ‖pd (pd (g k) j) j y‖ ^ 2 ≤ 4 * (Cb : ℝ) ^ 2 := by
    intro k
    have hd1 : Differentiable ℝ (fun y : Fin d → ℝ => ψ m (Fin.cons t y) k) :=
      (hgm k).differentiable (by norm_num)
    have hd2 : Differentiable ℝ (fun y : Fin d → ℝ => ψ n (Fin.cons t y) k) :=
      (hgn k).differentiable (by norm_num)
    have hp1 : ContDiff ℝ 1 (pd (fun y : Fin d → ℝ => ψ m (Fin.cons t y) k) j) := by
      unfold SobolevOpen.pd
      exact ((hgm k).fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
    have hp2 : ContDiff ℝ 1 (pd (fun y : Fin d → ℝ => ψ n (Fin.cons t y) k) j) := by
      unfold SobolevOpen.pd
      exact ((hgn k).fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
    have he1 : pd (g k) j = pd (fun y : Fin d → ℝ => ψ m (Fin.cons t y) k) j -
        pd (fun y : Fin d → ℝ => ψ n (Fin.cons t y) k) j := by
      funext y; rw [hgeq, pd_sub' (hd1 y) (hd2 y)]; rfl
    have he2 : ∀ y, pd (pd (g k) j) j y =
        pd (pd (fun y : Fin d → ℝ => ψ m (Fin.cons t y) k) j) j y -
          pd (pd (fun y : Fin d → ℝ => ψ n (Fin.cons t y) k) j) j y := by
      intro y; rw [he1, pd_sub' ((hp1.differentiable one_ne_zero) y)
        ((hp2.differentiable one_ne_zero) y)]
    have hc1 : Continuous (pd (pd (fun y : Fin d → ℝ => ψ m (Fin.cons t y) k) j) j) := by
      unfold SobolevOpen.pd
      exact (hp1.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hc2 : Continuous (pd (pd (fun y : Fin d → ℝ => ψ n (Fin.cons t y) k) j) j) := by
      unfold SobolevOpen.pd
      exact (hp2.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hI1 := h.H2 m j k t ht
    have hI2 := h.H2 n j k t ht
    calc ∫ y in Icc (0 : Fin d → ℝ) 1, ‖pd (pd (g k) j) j y‖ ^ 2
        ≤ ∫ y in Icc (0 : Fin d → ℝ) 1,
          (2 * ‖pd (pd (fun y : Fin d → ℝ => ψ m (Fin.cons t y) k) j) j y‖ ^ 2 +
            2 * ‖pd (pd (fun y : Fin d → ℝ => ψ n (Fin.cons t y) k) j) j y‖ ^ 2) := by
          refine integral_mono (integrableOn_cube_of_continuousOn (by
            simp only [he2]; fun_prop)) (integrableOn_cube_of_continuousOn (by fun_prop))
            fun y => ?_
          simp only [he2]
          set p1 := pd (pd (fun y : Fin d → ℝ => ψ m (Fin.cons t y) k) j) j y
          set p2 := pd (pd (fun y : Fin d → ℝ => ψ n (Fin.cons t y) k) j) j y
          have e1 : ‖p1 - p2‖ ^ 2 ≤ (‖p1‖ + ‖p2‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le p1 p2) 2
          nlinarith [sq_nonneg (‖p1‖ - ‖p2‖)]
      _ = 2 * (∫ y in Icc (0 : Fin d → ℝ) 1,
            ‖pd (pd (fun y : Fin d → ℝ => ψ m (Fin.cons t y) k) j) j y‖ ^ 2) +
          2 * ∫ y in Icc (0 : Fin d → ℝ) 1,
            ‖pd (pd (fun y : Fin d → ℝ => ψ n (Fin.cons t y) k) j) j y‖ ^ 2 := by
          rw [integral_add (integrableOn_cube_of_continuousOn (by fun_prop))
            (integrableOn_cube_of_continuousOn (by fun_prop))]
          simp only [integral_const_mul]
      _ ≤ 4 * (Cb : ℝ) ^ 2 := by linarith
  -- the values
  have hval : ∀ k, ∫ y in Icc (0 : Fin d → ℝ) 1, ‖g k y‖ ^ 2 ≤ C * ε := by
    intro k
    refine le_trans ?_ (hl2 t ht)
    have hcw : Continuous fun y : Fin d → ℝ => (ψ m - ψ n) (Fin.cons t y) :=
      continuous_slice ((h.cont m).sub (h.cont n)) ht
    refine integral_mono (integrableOn_cube_of_continuousOn ((hgC k).continuous.norm.pow 2
      ).continuousOn) (integrableOn_cube_of_continuousOn (hcw.norm.pow 2).continuousOn)
      fun y => ?_
    simp only [hg]
    gcongr
    exact norm_le_pi_norm _ k
  -- interpolation, component by component
  have hcomp : ∀ k, ∫ y in Icc (0 : Fin d → ℝ) 1, ‖pd (g k) j y‖ ^ 2 ≤
      (2 * (Cb : ℝ) ^ 2 + C / 2) * lam := by
    intro k
    have hi := integral_norm_pd_sq_le (hgC k) (hgper k) j hlam0
    have hlsq : lam * lam = ε := Real.mul_self_sqrt hε.le
    have e1 : lam / 2 * ∫ y in Icc (0 : Fin d → ℝ) 1, ‖pd (pd (g k) j) j y‖ ^ 2 ≤
        lam / 2 * (4 * (Cb : ℝ) ^ 2) := mul_le_mul_of_nonneg_left (hsec k) (by positivity)
    have e2 : (2 * lam)⁻¹ * ∫ y in Icc (0 : Fin d → ℝ) 1, ‖g k y‖ ^ 2 ≤ (2 * lam)⁻¹ * (C * ε) :=
      mul_le_mul_of_nonneg_left (hval k) (by positivity)
    have e3 : (2 * lam)⁻¹ * (C * ε) = C / 2 * lam := by
      rw [← hlsq]; field_simp
    nlinarith
  have hcpd : ∀ k, Continuous (pd (g k) j) := fun k => by
    unfold SobolevOpen.pd
    exact ((hgC k).continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hcv : Continuous fun y : Fin d → ℝ => pd (ψ m - ψ n) j.succ (Fin.cons t y) :=
    continuous_slice (h.pd_diff_cont m n j.succ) ht
  calc ∫ y in Icc (0 : Fin d → ℝ) 1, ‖pd (ψ m - ψ n) j.succ (Fin.cons t y)‖ ^ 2
      ≤ ∫ y in Icc (0 : Fin d → ℝ) 1, ∑ k, ‖pd (g k) j y‖ ^ 2 :=
        integral_mono (integrableOn_cube_of_continuousOn (hcv.norm.pow 2).continuousOn)
          (integrableOn_cube_of_continuousOn (continuous_finset_sum _ fun k _ =>
            (hcpd k).norm.pow 2).continuousOn) hpt
    _ = ∑ k, ∫ y in Icc (0 : Fin d → ℝ) 1, ‖pd (g k) j y‖ ^ 2 :=
        integral_finset_sum _ fun k _ =>
          integrableOn_cube_of_continuousOn ((hcpd k).norm.pow 2).continuousOn
    _ ≤ ∑ _k : N, (2 * (Cb : ℝ) ^ 2 + C / 2) * lam := Finset.sum_le_sum fun k _ => hcomp k
    _ = _ := by simp

/-- The time derivative of the difference, solved from the `m`-system. -/
theorem nrm_pd0_diff_le (h : StabHyp ψ A B a t₀ t₁ b c Cb) (m n : ℕ) :
    nrm t₀ t₁ (pd (ψ m - ψ n) 0) ≤ (Fintype.card N : ℝ) / c *
      (nrm t₀ t₁ (m0 ψ A Cb m n) + (Fintype.card N : ℝ) * Cb * nrm t₀ t₁ (ψ m - ψ n) +
        ∑ j : Fin d, (Fintype.card N : ℝ) * Cb * nrm t₀ t₁ (pd (ψ m - ψ n) j.succ)) := by
  set n₀ : ℝ := (Fintype.card N : ℝ)
  have hn₀ : 0 ≤ n₀ := Nat.cast_nonneg _
  have hc := h.hc
  have hw : ContinuousOn (ψ m - ψ n) (slab t₀ t₁) := (h.cont m).sub (h.cont n)
  have c1 := m0_cont h m n
  have c2 : ContinuousOn (fun x => n₀ * Cb * ‖(ψ m - ψ n) x‖) (slab t₀ t₁) :=
    continuousOn_const.mul hw.norm
  have c3 : ∀ j : Fin d, ContinuousOn (fun x => n₀ * Cb * ‖pd (ψ m - ψ n) j.succ x‖)
      (slab t₀ t₁) := fun j => continuousOn_const.mul (h.pd_diff_cont m n j.succ).norm
  have c3' : ContinuousOn (fun x => ∑ j : Fin d, n₀ * Cb * ‖pd (ψ m - ψ n) j.succ x‖)
      (slab t₀ t₁) := continuousOn_finsetSum _ fun j _ => c3 j
  have cg : ContinuousOn (fun x => n₀ / c * (m0 ψ A Cb m n x + n₀ * Cb * ‖(ψ m - ψ n) x‖ +
      ∑ j : Fin d, n₀ * Cb * ‖pd (ψ m - ψ n) j.succ x‖)) (slab t₀ t₁) :=
    continuousOn_const.mul ((c1.add c2).add c3')
  have hpt : ∀ᵐ x ∂μS, ‖pd (ψ m - ψ n) 0 x‖ ≤ ‖n₀ / c * (m0 ψ A Cb m n x +
      n₀ * Cb * ‖(ψ m - ψ n) x‖ + ∑ j : Fin d, n₀ * Cb * ‖pd (ψ m - ψ n) j.succ x‖)‖ := by
    filter_upwards [ae_slab] with x hx
    have h1 := h.norm_pd0_le m (f := ψ m - ψ n) hx
    have h2 : ‖princ (A m) (ψ m - ψ n) x‖ ≤ m0 ψ A Cb m n x + n₀ * Cb * ‖(ψ m - ψ n) x‖ := by
      have := le_max_left (‖princ (A m) (ψ m - ψ n) x‖ - n₀ * Cb * ‖(ψ m - ψ n) x‖) 0
      simp only [m0]; linarith
    refine h1.trans (le_trans ?_ (le_abs_self _))
    gcongr
  refine (nrm_le_of_ae_le (memLp_slab cg) hpt).trans ?_
  rw [nrm_const_mul, abs_of_nonneg (by positivity)]
  gcongr
  refine (nrm_add_le' (c1.add c2) c3').trans (add_le_add ((nrm_add_le' c1 c2).trans
    (add_le_add le_rfl ?_)) ?_)
  · rw [nrm_const_mul, nrm_norm, abs_of_nonneg (by positivity)]
  · have hm : ∀ j ∈ (Finset.univ : Finset (Fin d)),
        MemLp (fun x => n₀ * Cb * ‖pd (ψ m - ψ n) j.succ x‖) 2 μS := fun j _ =>
      memLp_slab (c3 j)
    refine (nrm_finset_sum_le Finset.univ hm).trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
    rw [nrm_const_mul, nrm_norm, abs_of_nonneg (by positivity)]

theorem le_mul_of_sq_le {x K s : ℝ} (hx : 0 ≤ x) (hK : 1 ≤ K) (hs : 0 ≤ s)
    (h : x ^ 2 ≤ K * s ^ 2) : x ≤ K * s := by
  by_contra hc
  push_neg at hc
  have h1 : (K * s) ^ 2 < x ^ 2 := by
    have := mul_nonneg (le_trans zero_le_one hK) hs
    nlinarith
  nlinarith [sq_nonneg s]

/-- **`prop:dirac-stability` (generic form).**  Under `StabHyp`, the sequence `ψ_n` is Cauchy in
`C_t L²_x` (`sup_t ‖ψ_m(t) - ψ_n(t)‖²_{L²(𝕋^d)} → 0`), its spatial derivatives are Cauchy in
`C_t L²_x` (`C_t H¹_x`), and all its first derivatives (time and space) and values are Cauchy in
`L²([t₀,t₁] × 𝕋^d)`: `ψ_n` is Cauchy in `H¹(I × Σ)`. -/
theorem cauchy (h : StabHyp ψ A B a t₀ t₁ b c Cb) :
    ∀ δ > (0 : ℝ), ∃ N₀ : ℕ, ∀ m ≥ N₀, ∀ n ≥ N₀,
      (∀ t ∈ Icc t₀ t₁, l2sq (ψ m - ψ n) t ≤ δ) ∧
      (∀ t ∈ Icc t₀ t₁, ∀ j : Fin d,
        ∫ y in Icc (0 : Fin d → ℝ) 1, ‖pd (ψ m - ψ n) j.succ (Fin.cons t y)‖ ^ 2 ≤ δ) ∧
      nrm t₀ t₁ (ψ m - ψ n) ≤ δ ∧ ∀ μ, nrm t₀ t₁ (pd (ψ m - ψ n) μ) ≤ δ := by
  obtain ⟨C, hC0, hCb⟩ := h.l2_bound
  set n₀ : ℝ := (Fintype.card N : ℝ)
  have hn₀ : 0 ≤ n₀ := Nat.cast_nonneg _
  have hc := h.hc
  set T := t₁ - t₀
  have hT : 0 ≤ T := sub_nonneg.mpr h.h01.le
  set G : ℝ := n₀ * (2 * (Cb : ℝ) ^ 2 + C / 2)
  have hG : 0 ≤ G := by positivity
  set K₁ : ℝ := T * C + 1
  have hK₁ : 1 ≤ K₁ := by have := mul_nonneg hT hC0; linarith
  set K₂ : ℝ := T * G + 1
  have hK₂ : 1 ≤ K₂ := by have := mul_nonneg hT hG; linarith
  set K₃ : ℝ := n₀ / c * (C + n₀ * Cb * K₁ + ∑ _j : Fin d, n₀ * Cb * K₂)
  have hK₃ : 0 ≤ K₃ := by positivity
  set Cbig : ℝ := C + G + K₁ + K₂ + K₃ + 1
  have hCbig : 0 < Cbig := by positivity
  intro δ hδ
  set η : ℝ := min 1 (δ / Cbig)
  have hη0 : 0 < η := lt_min one_pos (div_pos hδ hCbig)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηδ : Cbig * η ≤ δ := by
    have := min_le_right 1 (δ / Cbig)
    calc Cbig * η ≤ Cbig * (δ / Cbig) := mul_le_mul_of_nonneg_left this hCbig.le
      _ = δ := by field_simp
  have hle : ∀ K : ℝ, 0 ≤ K → K ≤ Cbig → K * η ≤ δ := fun K hK hKC =>
    (mul_le_mul_of_nonneg_right hKC hη0.le).trans hηδ
  have hη4 : η ^ 4 ≤ η := by
    calc η ^ 4 = η * η ^ 3 := by ring
      _ ≤ η * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ hη0.le hη1) hη0.le
      _ = η := mul_one η
  have hη2 : η ^ 2 ≤ η := by
    calc η ^ 2 = η * η := sq η
      _ ≤ η * 1 := mul_le_mul_of_nonneg_left hη1 hη0.le
      _ = η := mul_one η
  have hε0 : 0 < η ^ 4 := by positivity
  have hε1 : η ^ 4 ≤ 1 := pow_le_one₀ hη0.le hη1
  have hsq : Real.sqrt (η ^ 4) = η ^ 2 := by
    rw [show η ^ 4 = (η ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  obtain ⟨N₀, hN⟩ := hCb (η ^ 4) hε0 hε1
  refine ⟨N₀, fun m hm n hn => ?_⟩
  obtain ⟨hl2, hm0, -⟩ := hN m hm n hn
  have hw : ContinuousOn (ψ m - ψ n) (slab t₀ t₁) := (h.cont m).sub (h.cont n)
  -- (1) `C_t L²`
  have h1 : ∀ t ∈ Icc t₀ t₁, l2sq (ψ m - ψ n) t ≤ C * η := fun t ht =>
    (hl2 t ht).trans (mul_le_mul_of_nonneg_left hη4 hC0)
  -- (2) `C_t H¹`
  have h2 : ∀ t ∈ Icc t₀ t₁, ∀ j : Fin d,
      ∫ y in Icc (0 : Fin d → ℝ) 1, ‖pd (ψ m - ψ n) j.succ (Fin.cons t y)‖ ^ 2 ≤ G * η ^ 2 := by
    intro t ht j
    have := grad_bound h hε0 hl2 ht j
    rw [hsq] at this
    calc _ ≤ _ := this
      _ = G * η ^ 2 := by ring
  -- (3) values in `L²(slab)`
  have h3 : nrm t₀ t₁ (ψ m - ψ n) ≤ K₁ * η ^ 2 := by
    refine le_mul_of_sq_le (nrm_nonneg _ _ _) hK₁ (by positivity) ?_
    have := nrm_sq_le h.h01.le hw hl2
    calc _ ≤ T * (C * η ^ 4) := this
      _ ≤ K₁ * (η ^ 2) ^ 2 := by
        rw [show (η ^ 2) ^ 2 = η ^ 4 by ring]
        have : T * C ≤ K₁ := by linarith
        nlinarith [pow_pos hη0 4]
  -- (4) spatial derivatives in `L²(slab)`
  have h4 : ∀ j : Fin d, nrm t₀ t₁ (pd (ψ m - ψ n) j.succ) ≤ K₂ * η := by
    intro j
    refine le_mul_of_sq_le (nrm_nonneg _ _ _) hK₂ hη0.le ?_
    have := nrm_sq_le h.h01.le (h.pd_diff_cont m n j.succ) fun t ht => h2 t ht j
    calc _ ≤ T * (G * η ^ 2) := this
      _ ≤ K₂ * η ^ 2 := by
        have : T * G ≤ K₂ := by linarith
        nlinarith [pow_pos hη0 2]
  -- (5) the time derivative in `L²(slab)`
  have h5 : nrm t₀ t₁ (pd (ψ m - ψ n) 0) ≤ K₃ * η := by
    refine (nrm_pd0_diff_le h m n).trans ?_
    have e1 : nrm t₀ t₁ (m0 ψ A Cb m n) ≤ C * η := hm0.trans (mul_le_mul_of_nonneg_left hη4 hC0)
    have e2 : nrm t₀ t₁ (ψ m - ψ n) ≤ K₁ * η :=
      h3.trans (mul_le_mul_of_nonneg_left hη2 (by linarith))
    have e3 : ∑ j : Fin d, n₀ * Cb * nrm t₀ t₁ (pd (ψ m - ψ n) j.succ) ≤
        ∑ _j : Fin d, n₀ * Cb * K₂ * η :=
      Finset.sum_le_sum fun j _ => by
        rw [mul_assoc (n₀ * Cb)]; exact mul_le_mul_of_nonneg_left (h4 j) (by positivity)
    have e4 : n₀ * Cb * nrm t₀ t₁ (ψ m - ψ n) ≤ n₀ * Cb * (K₁ * η) :=
      mul_le_mul_of_nonneg_left e2 (by positivity)
    calc _ ≤ n₀ / c * (C * η + n₀ * Cb * (K₁ * η) + ∑ _j : Fin d, n₀ * Cb * K₂ * η) := by
          gcongr
      _ = K₃ * η := by
          simp only [K₃, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          ring
  have hCG : C ≤ Cbig := by have := hK₃; linarith
  refine ⟨fun t ht => (h1 t ht).trans (hle C hC0 hCG), fun t ht j => (h2 t ht j).trans
    ((mul_le_mul_of_nonneg_left hη2 hG).trans (hle G hG (by linarith))),
    h3.trans ((mul_le_mul_of_nonneg_left hη2 (by linarith)).trans (hle K₁ (by linarith)
      (by linarith))), fun μ => ?_⟩
  induction μ using Fin.cases with
  | zero => exact h5.trans (hle K₃ hK₃ (by linarith))
  | succ j => exact (h4 j).trans (hle K₂ (by linarith) (by linarith))

end StabHyp

end RenewalGeometry.SymHypEnergy
