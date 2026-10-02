/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.GaugeTheory.LiteralLinkCompactnessLimit

/-!
# The product tests `χ(t) e_k(x)` separate `L²((0,T] × 𝕋³)`
  (infrastructure for `thm:main-literal-link-compactness`; emergent-spacetime manuscript)

* `modeCoeff G k t = ∫_{𝕋³} e_k(x) G(t,x) dx` (the `(-k)`-th spatial Fourier coefficient of the
  time slice) and `cylPair_eq_integral_modeCoeff` (Fubini).
* `ae_modeCoeff_eq_zero`: if `⟨G, χ ⊗ e_k⟩ = 0` for every smooth `χ` compactly supported in
  `(0,T)`, then `modeCoeff G k = 0` for a.e. `t ∈ (0,T]` (fundamental lemma of the calculus of
  variations, `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`).
* `ae_eq_zero_of_cylPair_eq_zero`: **separation** — an `L²((0,T] × 𝕋³)` function annihilated by
  every product test `χ(t) e_k(x)` vanishes a.e. (time: fundamental lemma; space: Parseval /
  Fourier uniqueness on `L²(𝕋³)`, `hasSum_sq_mFourierCoeff`).
* `ae_eq_of_cylPair_eq`: two `L²` functions with equal product-tested integrals agree a.e.; in
  particular the weak limits `E_i^∞`, `F_{ij}^∞` of `literal_link_compactness` are the unique
  `L²` functions satisfying the tested curvature identities (`elim_unique`, `flim_unique`).
-/

open MeasureTheory Filter Topology UnitAddTorus
open scoped ComplexConjugate ContDiff

noncomputable section

set_option linter.unusedSectionVars false

namespace RenewalGeometry.LiteralLinkLimit

open GridAubinLions

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : MeasureTheory.IsProbabilityMeasure
    (MeasureTheory.volume : MeasureTheory.Measure UnitAddCircle) :=
  inferInstanceAs (MeasureTheory.IsProbabilityMeasure AddCircle.haarAddCircle)

variable {T : ℝ}

/-- The spatial mode coefficient `t ↦ ∫_{𝕋³} e_k(x) G(t,x) dx`. -/
def modeCoeff (G : ℝ × UnitAddTorus (Fin 3) → ℂ) (k : Fin 3 → ℤ) (t : ℝ) : ℂ :=
  ∫ x, mFourier k x * G (t, x)

theorem integrable_mFourier_mul {G : ℝ × UnitAddTorus (Fin 3) → ℂ}
    (hG : Integrable G (cylMeasure T)) (k : Fin 3 → ℤ) :
    Integrable (fun p : ℝ × UnitAddTorus (Fin 3) => mFourier k p.2 * G p) (cylMeasure T) :=
  hG.bdd_mul (c := 1) ((mFourier k).continuous.comp continuous_snd).aestronglyMeasurable
    (ae_of_all _ fun p => (norm_mFourier_apply k p.2).le)

theorem integrableOn_modeCoeff {G : ℝ × UnitAddTorus (Fin 3) → ℂ}
    (hG : Integrable G (cylMeasure T)) (k : Fin 3 → ℤ) :
    IntegrableOn (modeCoeff G k) (Set.Ioc 0 T) :=
  (integrable_mFourier_mul hG k).integral_prod_left

/-- Fubini for the product test. -/
theorem cylPair_eq_integral_modeCoeff {G : ℝ × UnitAddTorus (Fin 3) → ℂ}
    (hG : Integrable G (cylMeasure T)) {χ : ℝ → ℝ} (hχ : Continuous χ) {C : ℝ}
    (hC : ∀ t, ‖((χ t : ℝ) : ℂ)‖ ≤ C) (k : Fin 3 → ℤ) :
    cylPair T χ k G = ∫ t in Set.Ioc 0 T, ((χ t : ℝ) : ℂ) * modeCoeff G k t := by
  have hint : Integrable (fun p : ℝ × UnitAddTorus (Fin 3) =>
      ((χ p.1 : ℝ) : ℂ) * (mFourier k p.2 * G p)) (cylMeasure T) :=
    (integrable_mFourier_mul hG k).bdd_mul (c := C)
      ((Complex.continuous_ofReal.comp hχ).comp continuous_fst).aestronglyMeasurable
      (ae_of_all _ fun p => hC p.1)
  unfold cylPair
  have e : (fun p : ℝ × UnitAddTorus (Fin 3) => ((χ p.1 : ℝ) : ℂ) * mFourier k p.2 * G p) =
      fun p => ((χ p.1 : ℝ) : ℂ) * (mFourier k p.2 * G p) := by funext p; ring
  rw [e, cylMeasure, integral_prod _ hint]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  simp only [modeCoeff]
  exact integral_const_mul _ _

/-- **Fundamental lemma in time, mode by mode.** -/
theorem ae_modeCoeff_eq_zero {G : ℝ × UnitAddTorus (Fin 3) → ℂ}
    (hG : Integrable G (cylMeasure T)) (k : Fin 3 → ℤ)
    (h : ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ → tsupport χ ⊆ Set.Ioo 0 T →
      cylPair T χ k G = 0) :
    ∀ᵐ t ∂(volume.restrict (Set.Ioc 0 T)), modeCoeff G k t = 0 := by
  have hloc : LocallyIntegrableOn (modeCoeff G k) (Set.Ioo 0 T) volume :=
    ((integrableOn_modeCoeff hG k).mono_set Set.Ioo_subset_Ioc_self).locallyIntegrableOn
  have key := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc
    (fun g hg hgc hgs => by
      obtain ⟨C, hC⟩ := hg.continuous.bounded_above_of_compact_support hgc
      have h1 := cylPair_eq_integral_modeCoeff hG hg.continuous
        (fun t => by rw [Complex.norm_real]; exact hC t) k
      rw [h g hg hgc hgs] at h1
      have h2 : ∫ x in Set.Ioc 0 T, g x • modeCoeff G k x = ∫ x, g x • modeCoeff G k x :=
        setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
          have : g x = 0 := image_eq_zero_of_notMem_tsupport fun hxs =>
            hx (Set.Ioo_subset_Ioc_self (hgs hxs))
          simp [this]
      rw [← h2, h1]
      refine integral_congr_ae (ae_of_all _ fun t => ?_)
      simp [Complex.real_smul])
  rw [ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [key, (Set.countable_singleton T).ae_notMem volume] with t ht hT ht'
  exact ht ⟨ht'.1, lt_of_le_of_ne ht'.2 hT⟩

/-- **Separation by product tests.**  An `L²((0,T] × 𝕋³)` function `G` with
`∫ χ(t) e_k(x) G = 0` for every `k ∈ ℤ³` and every smooth `χ` compactly supported in `(0,T)` vanishes
almost everywhere. -/
theorem ae_eq_zero_of_cylPair_eq_zero {G : ℝ × UnitAddTorus (Fin 3) → ℂ}
    (hG : MemLp G 2 (cylMeasure T))
    (h : ∀ (k : Fin 3 → ℤ) (χ : ℝ → ℝ), ContDiff ℝ ∞ χ → HasCompactSupport χ →
      tsupport χ ⊆ Set.Ioo 0 T → cylPair T χ k G = 0) :
    G =ᵐ[cylMeasure T] 0 := by
  have hG1 : Integrable G (cylMeasure T) := hG.integrable one_le_two
  have hsq : Integrable (fun p => ‖G p‖ ^ 2) (cylMeasure T) := hG.norm.integrable_sq
  have hall : ∀ᵐ t ∂(volume.restrict (Set.Ioc 0 T)), ∀ k, modeCoeff G k t = 0 :=
    ae_all_iff.2 fun k => ae_modeCoeff_eq_zero hG1 k (h k)
  have hsl : ∀ᵐ t ∂(volume.restrict (Set.Ioc 0 T)),
      Integrable (fun x => ‖G (t, x)‖ ^ 2) volume := by
    have := hsq.prod_right_ae
    simpa [cylMeasure] using this
  have hslm : ∀ᵐ t ∂(volume.restrict (Set.Ioc 0 T)),
      AEStronglyMeasurable (fun x => G (t, x)) volume :=
    hG.aestronglyMeasurable.prodMk_left
  have hzero : ∀ᵐ t ∂(volume.restrict (Set.Ioc 0 T)), ∫ x, ‖G (t, x)‖ ^ 2 = 0 := by
    filter_upwards [hall, hsl, hslm] with t ht hti htm
    have hf : MemLp (fun x => G (t, x)) 2 volume :=
      (memLp_two_iff_integrable_sq_norm htm).2 hti
    have hs := hasSum_sq_mFourierCoeff (hf.toLp (fun x => G (t, x)))
    have hc : ∀ n, mFourierCoeff (⇑(hf.toLp (fun x => G (t, x)))) n = 0 := by
      intro n
      have e : mFourierCoeff (⇑(hf.toLp (fun x => G (t, x)))) n =
          mFourierCoeff (fun x => G (t, x)) n :=
        integral_congr_ae (hf.coeFn_toLp.mono fun x hx => by simp only [smul_eq_mul, hx])
      rw [e]
      have := ht (-n)
      simpa [mFourierCoeff, modeCoeff, smul_eq_mul] using this
    simp only [hc, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hs
    have h0 := hs.unique hasSum_zero
    rw [← h0]
    exact integral_congr_ae (hf.coeFn_toLp.mono fun x hx => by simp only [hx])
  have hI : ∫ p, ‖G p‖ ^ 2 ∂cylMeasure T = 0 := by
    rw [cylMeasure, integral_prod _ hsq]
    rw [integral_congr_ae hzero]
    simp
  have := (integral_eq_zero_iff_of_nonneg (fun p => by positivity) hsq).1 hI
  filter_upwards [this] with p hp
  simpa using hp

theorem cylPair_sub {F G : ℝ × UnitAddTorus (Fin 3) → ℂ} (hF : Integrable F (cylMeasure T))
    (hG : Integrable G (cylMeasure T)) {χ : ℝ → ℝ} (hχ : Continuous χ) {C : ℝ}
    (hC : ∀ t, ‖((χ t : ℝ) : ℂ)‖ ≤ C) (k : Fin 3 → ℤ) :
    cylPair T χ k (fun p => F p - G p) = cylPair T χ k F - cylPair T χ k G := by
  have hm : AEStronglyMeasurable (fun p : ℝ × UnitAddTorus (Fin 3) =>
      ((χ p.1 : ℝ) : ℂ) * mFourier k p.2) (cylMeasure T) :=
    (((Complex.continuous_ofReal.comp hχ).comp continuous_fst).mul
      ((mFourier k).continuous.comp continuous_snd)).aestronglyMeasurable
  have hb : ∀ p : ℝ × UnitAddTorus (Fin 3), ‖((χ p.1 : ℝ) : ℂ) * mFourier k p.2‖ ≤ C := fun p => by
    rw [norm_mul, norm_mFourier_apply, mul_one]; exact hC p.1
  have i1 : Integrable (fun p : ℝ × UnitAddTorus (Fin 3) => ((χ p.1 : ℝ) : ℂ) * mFourier k p.2 * F p)
      (cylMeasure T) := hF.bdd_mul (c := C) hm (ae_of_all _ hb)
  have i2 : Integrable (fun p : ℝ × UnitAddTorus (Fin 3) => ((χ p.1 : ℝ) : ℂ) * mFourier k p.2 * G p)
      (cylMeasure T) := hG.bdd_mul (c := C) hm (ae_of_all _ hb)
  unfold cylPair
  rw [← integral_sub i1 i2]
  congr 1; funext p; ring

/-- Two `L²((0,T] × 𝕋³)` functions with the same product-tested integrals agree a.e. -/
theorem ae_eq_of_cylPair_eq {F G : ℝ × UnitAddTorus (Fin 3) → ℂ} (hF : MemLp F 2 (cylMeasure T))
    (hG : MemLp G 2 (cylMeasure T))
    (h : ∀ (k : Fin 3 → ℤ) (χ : ℝ → ℝ), ContDiff ℝ ∞ χ → HasCompactSupport χ →
      tsupport χ ⊆ Set.Ioo 0 T → cylPair T χ k F = cylPair T χ k G) :
    F =ᵐ[cylMeasure T] G := by
  have h0 := ae_eq_zero_of_cylPair_eq_zero (G := fun p => F p - G p) (hF.sub hG)
    (fun k χ hχ hc hs => by
      obtain ⟨C, hC⟩ := hχ.continuous.bounded_above_of_compact_support hc
      rw [cylPair_sub (hF.integrable one_le_two) (hG.integrable one_le_two) hχ.continuous
        (fun t => by rw [Complex.norm_real]; exact hC t) k, h k χ hχ hc hs, sub_self])
  filter_upwards [h0] with p hp
  simpa [sub_eq_zero] using hp

end RenewalGeometry.LiteralLinkLimit
