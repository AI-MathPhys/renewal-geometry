/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.GaugeTheory.LiteralLinkCompactness

/-!
# Products, modulations and shifts of trigonometric interpolants on odd periodic grids
  (infrastructure for `thm:main-literal-link-compactness`; emergent-spacetime manuscript)

On the periodic grid `(ℤ/N)³` (`h = 1/N`) with the trigonometric interpolant `𝓘_h`
(`PeriodicGridSobolev.interp`), this file proves the exact and asymptotic identities used to pass
to the limit in products of grid arrays:

* `freqVec_neg_of_odd`: on an **odd** grid the signed frequency cube is symmetric.
* `integral_interp_mul`: on an odd grid, `∫_{𝕋³} 𝓘_h u · 𝓘_h v = h³ Σ_x u(x) v(x)` exactly
  (bilinear Parseval; this is where the odd periodic regulator is used).
* `integral_norm_interp_sq`: Parseval `‖𝓘_h u‖²_{L²(𝕋³)} = ‖u‖_h²`.
* `integral_norm_trigSum_sq`: orthogonality of finite trigonometric sums with distinct frequencies.
* `modChar`, `interp_modChar`: the sampled Fourier mode `e_n(x/N)` and its interpolant `e_n`.
* `integral_norm_interp_mul_modChar_sub_le`: the **modulation (aliasing) estimate**
  `‖𝓘_h(u · e_n) − e_n 𝓘_h u‖²_{L²} ≤ Σ_i ‖D_i⁺u‖_h² / (N − 2M)²` for `|n_i| ≤ M < N/2`.
* `sum_mul_modChar_sub_unit`, `tendsto_natCast_mul_modChar_unit`: the shift of a sampled mode is a
  scalar `ζ_N = e_n(-e_i/N)` with `N(ζ_N − 1) → −2πi n_i`.
-/

open MeasureTheory Filter Topology UnitAddTorus
open scoped ComplexConjugate

noncomputable section

set_option linter.unusedSectionVars false

namespace RenewalGeometry.LiteralLinkLimit

open PeriodicGridSobolev LatticeTorusPlancherel GridAubinLions

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : MeasureTheory.IsProbabilityMeasure
    (MeasureTheory.volume : MeasureTheory.Measure UnitAddCircle) :=
  inferInstanceAs (MeasureTheory.IsProbabilityMeasure AddCircle.haarAddCircle)

variable {N : ℕ} [NeZero N]

/-! ### Odd grids: symmetric signed frequencies -/

theorem freq_neg_of_odd (hN : Odd N) (i : Fin 3) (k : Grid N) : freq i (-k) = -freq i k := by
  unfold freq
  simp only [Pi.neg_apply]
  apply ZMod.valMinAbs_neg_of_ne_half
  intro h
  obtain ⟨r, hr⟩ := hN
  omega

theorem freqVec_neg_of_odd (hN : Odd N) (k : Grid N) : freqVec (-k) = -freqVec k := by
  funext i
  exact freq_neg_of_odd hN i k

theorem integrable_continuousMap (f : C(UnitAddTorus (Fin 3), ℂ)) : Integrable f :=
  f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-! ### Characters and their interpolants -/

theorem dft_latticeChar (k ℓ : Grid N) :
    dft (fun x => latticeChar k x) ℓ = if ℓ = k then 1 else 0 := by
  have h := LiteralLinkCompactness.dft_synth (N := N) (fun k' => if k' = k then 1 else 0) ℓ
  have e : (fun x => ∑ k', latticeChar k' x * (if k' = k then (1 : ℂ) else 0)) =
      fun x => latticeChar k x := by
    funext x
    rw [Finset.sum_eq_single k]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  rw [e] at h
  exact h

theorem interp_latticeChar (k : Grid N) :
    interp (fun x => latticeChar k x) = mFourier (freqVec k) := by
  unfold interp
  simp only [dft_latticeChar]
  rw [Finset.sum_eq_single k]
  · simp
  · intro b _ hb; rw [if_neg hb]; ext x; simp
  · simp

/-! ### Bilinear Parseval on odd grids -/

/-- `∫ e_{k̃}(x) f(x) dx` is the Fourier coefficient of `f` at `-k̃`. -/
theorem integral_mFourier_mul (m : Fin 3 → ℤ) (f : UnitAddTorus (Fin 3) → ℂ) :
    ∫ x, mFourier m x * f x = mFourierCoeff f (-m) := by
  simp only [mFourierCoeff, neg_neg, smul_eq_mul]

/-- **Bilinear Parseval identity on an odd grid**: `∫_{𝕋³} 𝓘_h u 𝓘_h v = h³ Σ_x u(x) v(x)`. -/
theorem integral_interp_mul (hN : Odd N) (u v : Grid N → ℂ) :
    ∫ x, interp u x * interp v x = ((N : ℂ) ^ 3)⁻¹ * ∑ x, u x * v x := by
  have hv : ∀ x, interp v x = ∑ k, dft v k * mFourier (freqVec k) x := fun x => by
    simp only [interp, ContinuousMap.coe_sum, ContinuousMap.coe_smul, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul]
  have hL : ∫ x, interp u x * interp v x = ∑ k, dft v k * dft u (-k) := by
    simp only [hv, Finset.mul_sum]
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun k _ => ?_
      have e : ∀ x, interp u x * (dft v k * mFourier (freqVec k) x) =
          dft v k * (mFourier (freqVec k) x * interp u x) := fun x => by ring
      simp only [e]
      rw [integral_const_mul, integral_mFourier_mul, ← freqVec_neg_of_odd hN,
        mFourierCoeff_interp_freqVec]
    · intro k _
      exact integrable_continuousMap (interp u * (dft v k • mFourier (freqVec k)))
  have hR : ((N : ℂ) ^ 3)⁻¹ * ∑ x, u x * v x = ∑ k, dft v k * dft u (-k) := by
    have hinv : ∀ x, v x = ∑ k, latticeChar k x * dft v k := fun x => (dft_inversion (N := N) v x).symm
    have hc : ∀ k x : Grid N, conj (latticeChar (-k) x) = latticeChar k x := fun k x => by
      rw [latticeChar_comm, latticeChar_neg_right, Complex.conj_conj, latticeChar_comm]
    have hdu : ∀ k : Grid N, dft u (-k) = ((N : ℂ) ^ 3)⁻¹ * ∑ x, latticeChar k x * u x :=
      fun k => by simp only [dft, smul_eq_mul, hc]
    rw [show (∑ x, u x * v x) = ∑ x, ∑ k, u x * (latticeChar k x * dft v k) from
      Finset.sum_congr rfl fun x _ => by rw [hinv x, Finset.mul_sum]]
    simp only [hdu, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun x _ => by ring
  rw [hL, hR]

/-- Parseval: `‖𝓘_h u‖²_{L²(𝕋³)} = ‖u‖_h²`. -/
theorem integral_norm_interp_sq (u : Grid N → ℂ) : ∫ x, ‖interp u x‖ ^ 2 = gridNormSq u := by
  rw [integral_norm_sq_eq_tsum]
  have := tsum_interp (fun _ => (1 : ℝ)) u
  simp only [one_mul] at this
  rw [this, gridNormSq_eq_sum_dft]

/-- Orthogonality of a finite trigonometric sum with pairwise distinct frequencies. -/
theorem integral_norm_trigSum_sq {ι : Type*} (s : Finset ι) (a : ι → ℂ) (φ : ι → Fin 3 → ℤ)
    (hφ : Set.InjOn φ s) :
    ∫ x, ‖(∑ i ∈ s, a i • mFourier (φ i)) x‖ ^ 2 = ∑ i ∈ s, ‖a i‖ ^ 2 := by
  classical
  rw [integral_norm_sq_eq_tsum]
  simp only [mFourierCoeff_trigSum]
  rw [tsum_eq_sum (s := s.image φ)]
  · rw [Finset.sum_image hφ]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.sum_eq_single i]
    · simp
    · intro j hj hji
      rw [if_neg]
      exact fun h => hji (hφ hj hi h)
    · intro h; exact absurd hi h
  · intro n hn
    rw [Finset.sum_eq_zero]
    · simp
    · intro i hi
      rw [if_neg]
      exact fun h => hn (h ▸ Finset.mem_image_of_mem φ hi)

/-! ### Sampled Fourier modes and the modulation estimate -/

/-- The grid frequency `(n_i mod N)_i` of an integer frequency. -/
def castFreq (N : ℕ) (n : Fin 3 → ℤ) : Grid N := fun i => ((n i : ℤ) : ZMod N)

/-- The sampled Fourier mode `x ↦ e_n(x/N)` on the grid. -/
def modChar (n : Fin 3 → ℤ) (x : Grid N) : ℂ := latticeChar (castFreq N n) x

theorem norm_modChar (n : Fin 3 → ℤ) (x : Grid N) : ‖modChar n x‖ = 1 := by
  unfold modChar latticeChar
  rw [norm_prod]
  exact Finset.prod_eq_one fun i _ => by simp

theorem freqVec_castFreq {n : Fin 3 → ℤ} {M : ℕ} (hM : ∀ i, |n i| ≤ M) (hMN : 2 * M < N) :
    freqVec (castFreq N n) = n := by
  funext i
  simp only [freqVec, freq, castFreq]
  rw [ZMod.valMinAbs_spec]
  refine ⟨rfl, ?_, ?_⟩
  · have := hM i; rw [abs_le] at this; push_cast; omega
  · have := hM i; rw [abs_le] at this; push_cast; omega

/-- The interpolant of a sampled mode is the mode, for `|n_i| ≤ M < N/2`. -/
theorem interp_modChar {n : Fin 3 → ℤ} {M : ℕ} (hM : ∀ i, |n i| ≤ M) (hMN : 2 * M < N) :
    interp (modChar (N := N) n) = mFourier n := by
  have := interp_latticeChar (N := N) (castFreq N n)
  rw [freqVec_castFreq hM hMN] at this
  exact this

theorem dft_mul_modChar (u : Grid N → ℂ) (n : Fin 3 → ℤ) (k : Grid N) :
    dft (fun x => u x * modChar n x) k = dft u (k - castFreq N n) := by
  unfold dft modChar
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [latticeChar_comm (k - castFreq N n), sub_eq_add_neg, latticeChar_add_right,
    latticeChar_neg_right, map_mul, Complex.conj_conj, latticeChar_comm x k,
    latticeChar_comm x (castFreq N n)]
  simp only [smul_eq_mul]
  ring

theorem interp_mul_modChar_eq (u : Grid N → ℂ) (n : Fin 3 → ℤ) :
    interp (fun x => u x * modChar n x) =
      ∑ j, dft u j • mFourier (freqVec (j + castFreq N n)) := by
  unfold interp
  simp only [dft_mul_modChar]
  exact Fintype.sum_equiv (Equiv.subRight (castFreq N n)) _ _ fun k => by
    simp [Equiv.subRight_apply]

theorem mFourier_mul_interp_eq (u : Grid N → ℂ) (n : Fin 3 → ℤ) (x : UnitAddTorus (Fin 3)) :
    mFourier n x * interp u x = ∑ j, dft u j * mFourier (freqVec j + n) x := by
  simp only [interp, ContinuousMap.coe_sum, ContinuousMap.coe_smul, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mFourier_add]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- A wrapped frequency has a large signed component. -/
theorem wrap_large {n : Fin 3 → ℤ} {M : ℕ} (hM : ∀ i, |n i| ≤ M) (j : Grid N)
    (hj : freqVec (j + castFreq N n) ≠ freqVec j + n) :
    ∃ i, ((N : ℝ) - 2 * M) ≤ 2 * |(freqVec j i : ℝ)| := by
  by_contra hcon
  push Not at hcon
  apply hj
  funext i
  simp only [freqVec, freq, Pi.add_apply, castFreq]
  rw [ZMod.valMinAbs_spec]
  have hc := hcon i
  have hn := hM i
  rw [abs_le] at hn
  have hc' : 2 * |freqVec j i| < (N : ℤ) - 2 * M := by
    have : 2 * |((freqVec j i : ℤ) : ℝ)| < ((N : ℝ) - 2 * M) := hc
    exact_mod_cast this
  refine ⟨?_, ?_, ?_⟩
  · push_cast
    simp
  · simp only [freqVec, freq] at hc'
    rcases abs_cases ((j i).valMinAbs) with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
  · simp only [freqVec, freq] at hc'
    rcases abs_cases ((j i).valMinAbs) with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega

/-- **Modulation (aliasing) estimate.**  For `|n_i| ≤ M` and `2M < N`,
`‖𝓘_h(u · e_n) − e_n 𝓘_h u‖²_{L²(𝕋³)} ≤ (Σ_i ‖D_i⁺u‖_h²) / (N − 2M)²`. -/
theorem integral_norm_interp_mul_modChar_sub_le (u : Grid N → ℂ) {n : Fin 3 → ℤ} {M : ℕ}
    (hM : ∀ i, |n i| ≤ M) (hMN : 2 * M < N) :
    ∫ x, ‖interp (fun y => u y * modChar n y) x - mFourier n x * interp u x‖ ^ 2 ≤
      coordForm u / ((N : ℝ) - 2 * M) ^ 2 := by
  classical
  set W := (Finset.univ : Finset (Grid N)).filter
    fun j => freqVec (j + castFreq N n) ≠ freqVec j + n with hW
  obtain ⟨a, ha⟩ : ∃ a : C(UnitAddTorus (Fin 3), ℂ),
      a = ∑ j ∈ W, dft u j • mFourier (freqVec (j + castFreq N n)) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : C(UnitAddTorus (Fin 3), ℂ),
      b = ∑ j ∈ W, dft u j • mFourier (freqVec j + n) := ⟨_, rfl⟩
  have hD : 0 < (N : ℝ) - 2 * M := by
    have : ((2 * M : ℕ) : ℝ) < N := by exact_mod_cast hMN
    push_cast at this; linarith
  have hdiff : ∀ x, interp (fun y => u y * modChar n y) x - mFourier n x * interp u x =
      a x - b x := by
    intro x
    rw [interp_mul_modChar_eq, mFourier_mul_interp_eq]
    simp only [ha, hb, ContinuousMap.coe_sum, ContinuousMap.coe_smul, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun j => freqVec (j + castFreq N n) ≠ freqVec j + n)]
    rw [← hW]
    have hz : ∑ j ∈ Finset.univ.filter
        (fun j => ¬ freqVec (j + castFreq N n) ≠ freqVec j + n),
        (dft u j * mFourier (freqVec (j + castFreq N n)) x - dft u j * mFourier (freqVec j + n) x)
          = 0 := by
      refine Finset.sum_eq_zero fun j hj => ?_
      rw [Finset.mem_filter, not_not] at hj
      rw [hj.2, sub_self]
    rw [hz, add_zero]
  have hinjA : Set.InjOn (fun j : Grid N => freqVec (j + castFreq N n)) (W : Set (Grid N)) :=
    fun j _ j' _ h => add_right_cancel (freqVec_injective h)
  have hinjB : Set.InjOn (fun j : Grid N => freqVec j + n) (W : Set (Grid N)) := fun j _ j' _ h =>
    freqVec_injective (add_right_cancel h)
  have hIa : ∫ x, ‖a x‖ ^ 2 = ∑ j ∈ W, ‖dft u j‖ ^ 2 := by
    rw [ha]; exact integral_norm_trigSum_sq W (dft u) _ hinjA
  have hIb : ∫ x, ‖b x‖ ^ 2 = ∑ j ∈ W, ‖dft u j‖ ^ 2 := by
    rw [hb]; exact integral_norm_trigSum_sq W (dft u) _ hinjB
  have hpt : ∀ x, ‖a x - b x‖ ^ 2 ≤ 2 * ‖a x‖ ^ 2 + 2 * ‖b x‖ ^ 2 := fun x => by
    have h1 := norm_sub_le (a x) (b x)
    have h2 := mul_self_le_mul_self (norm_nonneg _) h1
    nlinarith [sq_nonneg (‖a x‖ - ‖b x‖)]
  have hint : ∀ f : C(UnitAddTorus (Fin 3), ℂ),
      Integrable (fun x : UnitAddTorus (Fin 3) => ‖f x‖ ^ 2) volume := fun f =>
    (f.continuous.norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h1 : ∫ x, ‖interp (fun y => u y * modChar n y) x - mFourier n x * interp u x‖ ^ 2 ≤
      4 * ∑ j ∈ W, ‖dft u j‖ ^ 2 := by
    simp only [hdiff]
    calc ∫ x, ‖a x - b x‖ ^ 2 ≤ ∫ x, (2 * ‖a x‖ ^ 2 + 2 * ‖b x‖ ^ 2) :=
          integral_mono ((hint (a - b)).congr (ae_of_all _ fun x => by simp))
            (((hint a).const_mul 2).add ((hint b).const_mul 2)) hpt
      _ = 2 * (∫ x, ‖a x‖ ^ 2) + 2 * ∫ x, ‖b x‖ ^ 2 := by
          rw [integral_add ((hint a).const_mul 2) ((hint b).const_mul 2), integral_const_mul,
            integral_const_mul]
      _ = 4 * ∑ j ∈ W, ‖dft u j‖ ^ 2 := by
          rw [hIa, hIb]
          ring
  -- each wrapped mode carries a large gradient weight
  have hwt : ∀ j ∈ W, ‖dft u j‖ ^ 2 ≤
      (∑ i, (2 * Real.pi * freqVec j i) ^ 2) * ‖dft u j‖ ^ 2 / (Real.pi ^ 2 * ((N : ℝ) - 2 * M) ^ 2) := by
    intro j hj
    rw [hW, Finset.mem_filter] at hj
    obtain ⟨i, hi⟩ := wrap_large hM j hj.2
    have hle : Real.pi ^ 2 * ((N : ℝ) - 2 * M) ^ 2 ≤ ∑ i, (2 * Real.pi * freqVec j i) ^ 2 := by
      have h1 : Real.pi ^ 2 * ((N : ℝ) - 2 * M) ^ 2 ≤ (2 * Real.pi * freqVec j i) ^ 2 := by
        have hp := Real.pi_pos
        have h2 : ((N : ℝ) - 2 * M) ^ 2 ≤ (2 * |(freqVec j i : ℝ)|) ^ 2 :=
          pow_le_pow_left₀ hD.le hi 2
        have h3 : (2 * |(freqVec j i : ℝ)|) ^ 2 = 4 * (freqVec j i : ℝ) ^ 2 := by
          rw [mul_pow, sq_abs]; ring
        nlinarith
      exact h1.trans (Finset.single_le_sum (f := fun i => (2 * Real.pi * freqVec j i) ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ i))
    have hpos : 0 < Real.pi ^ 2 * ((N : ℝ) - 2 * M) ^ 2 := by have := Real.pi_pos; positivity
    rw [le_div_iff₀ hpos]
    nlinarith [mul_le_mul_of_nonneg_right hle (sq_nonneg ‖dft u j‖)]
  have hsum : ∑ j ∈ W, ‖dft u j‖ ^ 2 ≤
      trigGradSq (interp u) / (Real.pi ^ 2 * ((N : ℝ) - 2 * M) ^ 2) := by
    rw [trigGradSq_interp, Finset.sum_div]
    refine (Finset.sum_le_sum hwt).trans ?_
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun j _ _ => by
      have := Real.pi_pos
      positivity
  have hgrad := trigGradSq_interp_le_coordForm u
  have hp := Real.pi_pos
  have hD2 : 0 < ((N : ℝ) - 2 * M) ^ 2 := by positivity
  calc _ ≤ 4 * ∑ j ∈ W, ‖dft u j‖ ^ 2 := h1
    _ ≤ 4 * (trigGradSq (interp u) / (Real.pi ^ 2 * ((N : ℝ) - 2 * M) ^ 2)) := by gcongr
    _ ≤ coordForm u / ((N : ℝ) - 2 * M) ^ 2 := by
        have e : 4 * (trigGradSq (interp u) / (Real.pi ^ 2 * ((N : ℝ) - 2 * M) ^ 2)) =
            ((2 / Real.pi) ^ 2 * trigGradSq (interp u)) / ((N : ℝ) - 2 * M) ^ 2 := by
          field_simp; ring
        rw [e]
        exact div_le_div_of_nonneg_right hgrad hD2.le

/-! ### Shifts of sampled modes -/

theorem modChar_sub_unit (n : Fin 3 → ℤ) (x : Grid N) (i : Fin 3) :
    modChar n (x - unit i) = conj (modChar (N := N) n (unit i)) * modChar n x := by
  unfold modChar
  rw [latticeChar_sub_right]
  ring

/-- `Σ_x f(x + e_i) e_n(x) = conj(e_n(e_i)) Σ_x f(x) e_n(x)`. -/
theorem sum_shift_mul_modChar (f : Grid N → ℂ) (n : Fin 3 → ℤ) (i : Fin 3) :
    ∑ x, f (x + unit i) * modChar n x = conj (modChar (N := N) n (unit i)) * ∑ x, f x * modChar n x := by
  calc ∑ x, f (x + unit i) * modChar n x
      = ∑ x, (fun y => f y * modChar n (y - unit i)) (x + unit i) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        simp only [add_sub_cancel_right]
    _ = ∑ y, f y * modChar n (y - unit i) :=
        sum_shift_reindex (N := N) (fun y => f y * modChar n (y - unit i)) (unit i)
    _ = _ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [modChar_sub_unit]; ring

theorem modChar_unit (n : Fin 3 → ℤ) (i : Fin 3) :
    modChar (N := N) n (unit i) = Complex.exp (2 * Real.pi * Complex.I * (n i) / N) := by
  unfold modChar unit
  rw [latticeChar_single]
  simp only [castFreq]
  rw [ZMod.stdAddChar_coe]

/-- `N (conj e_n(e_i/N) − 1) → −2πi n_i` as `N → ∞` along any sequence of grids. -/
theorem tendsto_natCast_mul_modChar_unit {Nm : ℕ → ℕ} [∀ m, NeZero (Nm m)]
    (hN : Tendsto Nm atTop atTop) (n : Fin 3 → ℤ) (i : Fin 3) :
    Tendsto (fun m => ((Nm m : ℂ)) * (conj (modChar (N := Nm m) n (unit i)) - 1)) atTop
      (𝓝 (-(2 * Real.pi * Complex.I * n i))) := by
  set c : ℂ := -(2 * Real.pi * Complex.I * n i)
  have hd : HasDerivAt (fun t : ℂ => Complex.exp (c * t)) c 0 := by
    have := ((hasDerivAt_id (0 : ℂ)).const_mul c).cexp
    simpa using this
  have hs := (hasDerivAt_iff_tendsto_slope_zero.1 hd)
  have hto : Tendsto (fun m => ((Nm m : ℂ))⁻¹) atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun m => ?_⟩
    · have h1 : Tendsto (fun m => ((Nm m : ℝ))⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hN)
      have h2 := (Complex.continuous_ofReal.tendsto 0).comp h1
      simpa [Function.comp_def] using h2
    · simp [NeZero.ne (Nm m)]
  have := hs.comp hto
  refine this.congr fun m => ?_
  simp only [Function.comp_apply, zero_add, mul_zero, Complex.exp_zero, smul_eq_mul, inv_inv]
  rw [modChar_unit, ← Complex.exp_conj]
  congr 2
  simp only [c, map_div₀, map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, map_intCast,
    map_natCast]
  ring

end RenewalGeometry.LiteralLinkLimit
