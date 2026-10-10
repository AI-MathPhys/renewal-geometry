/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.UhlenbeckCoulombIFT
import RenewalGeometry.Analysis.UhlenbeckLocalisationObstructions

/-!
# The linearised Coulomb operator at a small connection is an isomorphism `H¹₀ → H⁻¹₀`
  (the linear input of the openness step of Uhlenbeck's continuity method)

Generic infrastructure (no renewal notions) for `prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript (K. Uhlenbeck, CMP 83 (1982), Thm 1.3).  In the
implicit-function (openness) step the Coulomb condition `d^*(e^{ξ}·(a + β)) = 0` is linearised at
`ξ = 0`, `β = 0`; the linearisation is `L_a ξ = d^* d_a ξ`, `d_a ξ = dξ + [a, ξ]`, which must be
an isomorphism.  `UhlenbeckCoulombIFT.laplace_solve` treats `a = 0` and
`UhlenbeckTorus.linearized_coulomb_kernel_const` the kernel at a small Coulomb `a`; this file
proves the full isomorphism (surjectivity and injectivity) at every connection `a` with small
`L⁴` norm, on the flat torus `𝕋⁴`, in the weak (`H¹₀ → H⁻¹₀`) formulation: for every `L²`
matrix-valued one-form `h` there is a unique mean-zero `ξ ∈ H¹` with `d^* d_a ξ = d^* h` weakly,
and `‖∇ξ‖ ≤ 2 Σ‖h‖`.  No Coulomb condition on `a` is needed.

Proof: a contraction in the Fourier model.  The unknown is `w = |∇|ξ ∈ L²` (Fourier coefficients
`|n| ξ̂(n)`, `|n|² = lapSym n`); `ξ = |∇|⁻¹ w` (`potL`) has `‖∂_μ ξ‖_2 ≤ ‖w‖_2` and, by the critical
Sobolev–Poincaré inequality, `‖ξ‖_4 ≤ 28 ‖w‖_2`.  The equation is the fixed-point problem
`w = T w = Π(h - [a, |∇|⁻¹ w])`, where `Π g = |∇|⁻¹ d^* g` (`projC`) satisfies `‖Π g‖ ≤ Σ_μ‖g_μ‖`;
Hölder gives `‖[a, ξ]‖_2 ≤ 2 ‖a‖_4 · 28 ‖w‖_2`, so `T` is a contraction with constant `1/2`
when `Σ ‖a_{μ,ce}‖_{L⁴} ≤ 1/112` (Banach fixed point theorem).

* `potL`, `potGradL`: the potential `|∇|⁻¹ w` and its partials; `eLpNorm_potGradL_le`,
  `eLpNorm_four_potL_le`.
* `projC`: the coefficients of `|∇|⁻¹ d^* g`; `eLpNorm_ofCoeff_projC_le`.
* `weak_of_fourier`: the Fourier identity `Σ_μ conj(2πi n_μ) Ĝ_μ(n) = 0` for all `n` is the weak
  equation `d^* G = 0`; `fourier_of_weak`: the converse (test with monomials).
* `linearized_coulomb_iso` (**main theorem**).
-/

open MeasureTheory Filter Topology Set UnitAddTorus
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace RenewalGeometry.UhlenbeckOpenness

open SobolevOpen TorusSobolev UhlenbeckTorus UhlenbeckObstruction

set_option linter.unusedSectionVars false

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local notation "𝕋⁴" => UnitAddTorus (Fin 4)

local notation "L2" => Lp ℂ 2 (volume : Measure 𝕋⁴)

/-! ### Coefficient bounds -/

theorem one_le_sqrt_lapSym {n : Fin 4 → ℤ} (hn : n ≠ 0) : 1 ≤ √(lapSym n) := by
  rw [Real.le_sqrt (by norm_num) (lapSym_nonneg n)]; simpa using one_le_lapSym hn

theorem norm_sym_le_sqrt_lapSym (μ : Fin 4) (n : Fin 4 → ℤ) : ‖sym μ n‖ ≤ √(lapSym n) := by
  rw [Real.le_sqrt (norm_nonneg _) (lapSym_nonneg n), norm_sym_sq]
  exact sq_sym_le_lapSym μ n

/-- `n ↦ W(n) / |n|` (and `0` at `n = 0`): the coefficients of `|∇|⁻¹ W`. -/
def invC (W : (Fin 4 → ℤ) → ℂ) (n : Fin 4 → ℤ) : ℂ :=
  if n = 0 then 0 else W n / (√(lapSym n) : ℂ)

theorem norm_mul_invC_le (W : (Fin 4 → ℤ) → ℂ) (n : Fin 4 → ℤ) (z : ℂ)
    (hz : ‖z‖ ≤ √(lapSym n)) : ‖z * invC W n‖ ≤ ‖W n‖ := by
  unfold invC
  split_ifs with hn
  · simp
  · have h1 := one_le_sqrt_lapSym hn
    rw [norm_mul, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith),
      mul_div_assoc', div_le_iff₀ (by linarith)]
    calc ‖z‖ * ‖W n‖ ≤ √(lapSym n) * ‖W n‖ := by gcongr
      _ = ‖W n‖ * √(lapSym n) := by ring

theorem norm_invC_le (W : (Fin 4 → ℤ) → ℂ) (n : Fin 4 → ℤ) : ‖invC W n‖ ≤ ‖W n‖ := by
  by_cases hn : n = 0
  · simp [invC, hn]
  · simpa using norm_mul_invC_le W n 1 (by simpa using one_le_sqrt_lapSym hn)

theorem summable_sq_mFourierCoeff {f : 𝕋⁴ → ℂ} (hf : MemLp f 2 volume) :
    Summable fun n => ‖mFourierCoeff f n‖ ^ 2 :=
  (hasSum_sq_mFourierCoeff_of_memLp hf).summable

/-- Parseval comparison: if `|c(n)| ≤ |ĝ(n)|` for all `n`, then `‖ofCoeff c‖_2 ≤ ‖g‖_2`. -/
theorem eLpNorm_ofCoeff_le {c : (Fin 4 → ℤ) → ℂ} (hc : Memℓp c 2) {g : 𝕋⁴ → ℂ}
    (hg : MemLp g 2 volume) (h : ∀ n, ‖c n‖ ≤ ‖mFourierCoeff g n‖) :
    eLpNorm (ofCoeff c hc) 2 volume ≤ eLpNorm g 2 volume := by
  have h1 := hasSum_sq_mFourierCoeff_of_memLp (Lp.memLp (ofCoeff c hc))
  simp only [mFourierCoeff_ofCoeff] at h1
  rw [eLpNorm_two_eq_sqrt (Lp.memLp _), eLpNorm_two_eq_sqrt hg]
  refine ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt ?_)
  exact hasSum_le (fun n => pow_le_pow_left₀ (norm_nonneg _) (h n) 2) h1
    (hasSum_sq_mFourierCoeff_of_memLp hg)

/-! ### The potential `|∇|⁻¹ w` -/

theorem memℓp_invC {f : 𝕋⁴ → ℂ} (hf : MemLp f 2 volume) :
    Memℓp (invC (mFourierCoeff f)) 2 :=
  memℓp_two_of_le (summable_sq_mFourierCoeff hf) (norm_invC_le _)

theorem memℓp_sym_invC {f : 𝕋⁴ → ℂ} (hf : MemLp f 2 volume) (μ : Fin 4) :
    Memℓp (fun n => sym μ n * invC (mFourierCoeff f) n) 2 :=
  memℓp_two_of_le (summable_sq_mFourierCoeff hf) fun n =>
    norm_mul_invC_le _ n _ (norm_sym_le_sqrt_lapSym μ n)

/-- The potential `ξ = |∇|⁻¹ w` of `w ∈ L²(𝕋⁴)` (mean zero). -/
def potL (w : L2) : L2 := ofCoeff (invC (mFourierCoeff ⇑w)) (memℓp_invC (Lp.memLp w))

/-- Its partial derivatives `∂_μ |∇|⁻¹ w`. -/
def potGradL (w : L2) (μ : Fin 4) : L2 :=
  ofCoeff (fun n => sym μ n * invC (mFourierCoeff ⇑w) n) (memℓp_sym_invC (Lp.memLp w) μ)

theorem mFourierCoeff_potL (w : L2) (n : Fin 4 → ℤ) :
    mFourierCoeff ⇑(potL w) n = invC (mFourierCoeff ⇑w) n :=
  mFourierCoeff_ofCoeff _ _ n

theorem isTPartial_potL (w : L2) (μ : Fin 4) : IsTPartial μ ⇑(potL w) ⇑(potGradL w μ) := by
  intro n
  rw [mFourierCoeff_potL, potGradL, mFourierCoeff_ofCoeff]

theorem potL_mean_zero (w : L2) : mFourierCoeff ⇑(potL w) 0 = 0 := by
  rw [mFourierCoeff_potL]; simp [invC]

theorem eLpNorm_potGradL_le (w : L2) (μ : Fin 4) :
    eLpNorm ⇑(potGradL w μ) 2 volume ≤ eLpNorm ⇑w 2 volume :=
  eLpNorm_ofCoeff_le _ (Lp.memLp w) fun n =>
    norm_mul_invC_le _ n _ (norm_sym_le_sqrt_lapSym μ n)

/-- **Critical Sobolev bound for the potential**: `‖|∇|⁻¹ w‖_{L⁴} ≤ 28 ‖w‖_{L²}`. -/
theorem eLpNorm_four_potL_le (w : L2) :
    eLpNorm ⇑(potL w) 4 volume ≤ 28 * eLpNorm ⇑w 2 volume := by
  refine (eLpNorm_four_le_of_mean_zero (Lp.memLp _) (fun μ => Lp.memLp (potGradL w μ))
    (isTPartial_potL w) (potL_mean_zero w)).trans ?_
  calc 7 * ∑ μ, eLpNorm ⇑(potGradL w μ) 2 volume ≤ 7 * ∑ _μ : Fin 4, eLpNorm ⇑w 2 volume := by
        gcongr with μ; exact eLpNorm_potGradL_le w μ
    _ = 28 * eLpNorm ⇑w 2 volume := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast; ring

theorem memLp_four_potL (w : L2) : MemLp ⇑(potL w) 4 volume :=
  ⟨(Lp.memLp _).1, lt_of_le_of_lt (eLpNorm_four_potL_le w)
    (ENNReal.mul_lt_top (by norm_num) (Lp.eLpNorm_lt_top w))⟩

/-- `|∇|⁻¹` is linear (up to a.e. equality). -/
theorem potL_sub (w w' : L2) : potL (w - w') =ᵐ[volume] fun x => potL w x - potL w' x := by
  refine ae_eq_of_mFourierCoeff_eq (Lp.memLp _) ((Lp.memLp _).sub (Lp.memLp _)) fun n => ?_
  have hc : mFourierCoeff ⇑(w - w') = fun n => mFourierCoeff ⇑w n - mFourierCoeff ⇑w' n := by
    funext n
    rw [← mFourierCoeff_sub (integrable_of_memLp_two (Lp.memLp w))
      (integrable_of_memLp_two (Lp.memLp w'))]
    unfold mFourierCoeff
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub w w'] with x hx
    rw [hx]; rfl
  rw [mFourierCoeff_sub (integrable_of_memLp_two (Lp.memLp _))
    (integrable_of_memLp_two (Lp.memLp _)), mFourierCoeff_potL, mFourierCoeff_potL,
    mFourierCoeff_potL, hc]
  unfold invC
  split_ifs <;> ring

/-! ### The projection `|∇|⁻¹ d^*` -/

/-- Coefficients of `|∇|⁻¹ d^* g` for a one-form `g`:
`n ↦ (Σ_μ conj(2πi n_μ) ĝ_μ(n)) / |n|`. -/
def projC (g : Fin 4 → 𝕋⁴ → ℂ) (n : Fin 4 → ℤ) : ℂ :=
  ∑ μ, conj (sym μ n) * invC (mFourierCoeff (g μ)) n

theorem norm_conj_sym_le (μ : Fin 4) (n : Fin 4 → ℤ) : ‖conj (sym μ n)‖ ≤ √(lapSym n) := by
  rw [Complex.norm_conj]; exact norm_sym_le_sqrt_lapSym μ n

theorem memℓp_projC_term {g : 𝕋⁴ → ℂ} (hg : MemLp g 2 volume) (μ : Fin 4) :
    Memℓp (fun n => conj (sym μ n) * invC (mFourierCoeff g) n) 2 :=
  memℓp_two_of_le (summable_sq_mFourierCoeff hg) fun n =>
    norm_mul_invC_le _ n _ (norm_conj_sym_le μ n)

theorem norm_projC_le (g : Fin 4 → 𝕋⁴ → ℂ) (n : Fin 4 → ℤ) :
    ‖projC g n‖ ≤ ∑ μ, ‖mFourierCoeff (g μ) n‖ :=
  (norm_sum_le _ _).trans (Finset.sum_le_sum fun μ _ =>
    norm_mul_invC_le _ n _ (norm_conj_sym_le μ n))

theorem memℓp_projC {g : Fin 4 → 𝕋⁴ → ℂ} (hg : ∀ μ, MemLp (g μ) 2 volume) :
    Memℓp (projC g) 2 := by
  refine memℓp_two_of_le (f := fun n => ((∑ μ, ‖mFourierCoeff (g μ) n‖ : ℝ) : ℂ)) ?_ fun n => ?_
  · have hs : Summable fun n => 4 * ∑ μ, ‖mFourierCoeff (g μ) n‖ ^ 2 :=
      (summable_sum fun μ _ => summable_sq_mFourierCoeff (hg μ)).mul_left 4
    refine hs.of_nonneg_of_le (fun n => by positivity) fun n => ?_
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have := sq_sum_le_card_mul (fun μ : Fin 4 => ‖mFourierCoeff (g μ) n‖)
    simpa using this
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun _ _ =>
      norm_nonneg _)]
    exact norm_projC_le g n

/-- **`‖|∇|⁻¹ d^* g‖_{L²} ≤ Σ_μ ‖g_μ‖_{L²}`.** -/
theorem eLpNorm_ofCoeff_projC_le {g : Fin 4 → 𝕋⁴ → ℂ} (hg : ∀ μ, MemLp (g μ) 2 volume) :
    eLpNorm ⇑(ofCoeff (projC g) (memℓp_projC hg)) 2 volume ≤ ∑ μ, eLpNorm (g μ) 2 volume := by
  let F : Fin 4 → L2 := fun μ =>
    ofCoeff (fun n => conj (sym μ n) * invC (mFourierCoeff (g μ)) n) (memℓp_projC_term (hg μ) μ)
  have hF : ∀ μ, eLpNorm ⇑(F μ) 2 volume ≤ eLpNorm (g μ) 2 volume := fun μ =>
    eLpNorm_ofCoeff_le _ (hg μ) fun n => norm_mul_invC_le _ n _ (norm_conj_sym_le μ n)
  have hae : ⇑(ofCoeff (projC g) (memℓp_projC hg)) =ᵐ[volume] ∑ μ, ⇑(F μ) := by
    have hsum : MemLp (∑ μ, ⇑(F μ)) 2 volume := memLp_finset_sum' _ fun μ _ => Lp.memLp _
    refine ae_eq_of_mFourierCoeff_eq (Lp.memLp _) hsum fun n => ?_
    have e : (∑ μ, ⇑(F μ)) = fun x => ∑ μ, F μ x := by
      funext x; simp [Finset.sum_apply]
    rw [e, SobolevOpen.mFourierCoeff_finset_sum _ fun μ => integrable_of_memLp_two (Lp.memLp _),
      mFourierCoeff_ofCoeff]
    simp only [F, mFourierCoeff_ofCoeff, projC]
  rw [eLpNorm_congr_ae hae]
  exact (eLpNorm_sum_le (fun μ _ => (Lp.memLp (F μ)).1) (by norm_num)).trans
    (Finset.sum_le_sum fun μ _ => hF μ)

/-! ### Fourier calculus for the weak equation -/

theorem mFourierCoeff_Lp_sub (f g : L2) (n : Fin 4 → ℤ) :
    mFourierCoeff ⇑(f - g) n = mFourierCoeff ⇑f n - mFourierCoeff ⇑g n := by
  rw [← mFourierCoeff_sub (integrable_of_memLp_two (Lp.memLp f))
    (integrable_of_memLp_two (Lp.memLp g))]
  unfold mFourierCoeff
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_sub f g] with x hx
  rw [hx]; rfl

theorem sum_conj_sym_mul_sym (n : Fin 4 → ℤ) :
    ∑ μ, conj (sym μ n) * sym μ n = (lapSym n : ℂ) := by
  have h := sum_sym_sq n
  simp only [conj_sym, neg_mul, Finset.sum_neg_distrib]
  rw [h, neg_neg]

/-- Pairing with a monomial test: `∫ conj(z e_n) f = conj(z) f̂(n)`. -/
theorem integral_conj_monomial_mul (z : ℂ) (n : Fin 4 → ℤ) (f : 𝕋⁴ → ℂ) :
    ∫ x, conj (z * mFourier n x) * f x = conj z * mFourierCoeff f n := by
  unfold mFourierCoeff
  rw [← integral_const_mul]
  congr 1; funext x
  rw [mFourier_neg, smul_eq_mul, map_mul]; ring

/-- **Weak equation from the Fourier identity**: if the one-form `G` (entries in `L²`) satisfies
`Σ_μ conj(2πi n_μ) Ĝ_μ(n) = 0` for every frequency, then `d^*G = 0` weakly:
`Σ_μ ⟨∂_μ u, G_μ⟩ = 0` for every `u ∈ H¹`. -/
theorem weak_of_fourier {G : Fin 4 → 𝕋⁴ → ℂ} (hG : ∀ μ, MemLp (G μ) 2 volume)
    (hF : ∀ n, ∑ μ, conj (sym μ n) * mFourierCoeff (G μ) n = 0)
    {u : 𝕋⁴ → ℂ} {gu : Fin 4 → 𝕋⁴ → ℂ} (hu : MemLp u 2 volume)
    (hgu : ∀ μ, MemLp (gu μ) 2 volume) (hdu : ∀ μ, IsTPartial μ u (gu μ)) :
    ∑ μ, ∫ x, conj (gu μ x) * G μ x = 0 := by
  have h1 : ∀ μ, HasSum (fun n => conj (mFourierCoeff (gu μ) n) * mFourierCoeff (G μ) n)
      (∫ x, conj (gu μ x) * G μ x) := by
    intro μ
    have h := hasSum_prod_mFourierCoeff ((hgu μ).toLp (gu μ)) ((hG μ).toLp (G μ))
    rw [mFourierCoeff_toLp (hgu μ), mFourierCoeff_toLp (hG μ)] at h
    have e : ∫ t, conj (((hgu μ).toLp (gu μ)) t) * ((hG μ).toLp (G μ)) t =
        ∫ x, conj (gu μ x) * G μ x := by
      refine integral_congr_ae ?_
      filter_upwards [(hgu μ).coeFn_toLp, (hG μ).coeFn_toLp] with t h₁ h₂
      rw [h₁, h₂]
    rwa [e] at h
  have h2 := hasSum_sum (s := Finset.univ) fun μ _ => h1 μ
  have h0 : (fun n => ∑ μ, conj (mFourierCoeff (gu μ) n) * mFourierCoeff (G μ) n) = fun _ => 0 := by
    funext n
    simp only [hdu _ n, map_mul]
    have : ∑ μ, conj (sym μ n) * conj (mFourierCoeff u n) * mFourierCoeff (G μ) n =
        conj (mFourierCoeff u n) * ∑ μ, conj (sym μ n) * mFourierCoeff (G μ) n := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun μ _ => by ring
    rw [this, hF n, mul_zero]
  rw [h0] at h2
  exact (hasSum_zero.unique h2).symm

/-- **Fourier identity from the weak equation** (test with the monomials `e_n`). -/
theorem fourier_of_weak {G : Fin 4 → 𝕋⁴ → ℂ}
    (hw : ∀ (u : 𝕋⁴ → ℂ) (gu : Fin 4 → 𝕋⁴ → ℂ), MemLp u 2 volume →
      (∀ μ, MemLp (gu μ) 2 volume) → (∀ μ, IsTPartial μ u (gu μ)) →
      ∑ μ, ∫ x, conj (gu μ x) * G μ x = 0) (n : Fin 4 → ℤ) :
    ∑ μ, conj (sym μ n) * mFourierCoeff (G μ) n = 0 := by
  have h := hw (fun x => 1 * mFourier n x) (fun μ x => sym μ n * (1 * mFourier n x))
    (memLp_monomial 1 n 2) (fun μ => by
      have e : (fun x => sym μ n * (1 * mFourier n x)) = fun x => sym μ n * mFourier n x := by
        funext x; ring
      rw [e]; exact memLp_monomial _ n 2) (fun μ => isTPartial_monomial μ 1 n)
  have e : ∀ μ, ∫ x, conj (sym μ n * (1 * mFourier n x)) * G μ x =
      conj (sym μ n) * mFourierCoeff (G μ) n := by
    intro μ
    have := integral_conj_monomial_mul (sym μ n) n (G μ)
    simpa only [one_mul] using this
  simpa only [e] using h

/-! ### The fixed-point map -/

variable {m : ℕ}

/-- The weak linearised Coulomb equation `d^* d_a ξ = d^* h` (`d_a ξ = dξ + [a, ξ]`, `covLin`):
`Σ_μ ⟨∂_μ u, (d_a ξ)_μ⟩ = Σ_μ ⟨∂_μ u, h_μ⟩` for every `u ∈ H¹`, entrywise. -/
def WeakLinCoulomb (a : Fin 4 → Fin m → Fin m → 𝕋⁴ → ℂ) (h : Fin m → Fin m → Fin 4 → 𝕋⁴ → ℂ)
    (ξ : Fin m → Fin m → 𝕋⁴ → ℂ) (dξ : Fin m → Fin m → Fin 4 → 𝕋⁴ → ℂ) : Prop :=
  ∀ (u : 𝕋⁴ → ℂ) (gu : Fin 4 → 𝕋⁴ → ℂ), MemLp u 2 volume → (∀ μ, MemLp (gu μ) 2 volume) →
    (∀ μ, IsTPartial μ u (gu μ)) → ∀ c e,
      ∑ μ, ∫ x, conj (gu μ x) * covLin a ξ dξ c e μ x = ∑ μ, ∫ x, conj (gu μ x) * h c e μ x

/-- The commutator `[a_μ, |∇|⁻¹ w]_{ce}`. -/
def commW (a : Fin 4 → Fin m → Fin m → 𝕋⁴ → ℂ) (w : Fin m → Fin m → L2) (c e : Fin m)
    (μ : Fin 4) : 𝕋⁴ → ℂ :=
  fun x => ∑ k, (a μ c k x * potL (w k e) x - potL (w c k) x * a μ k e x)

theorem memLp_commW {a : Fin 4 → Fin m → Fin m → 𝕋⁴ → ℂ} (ha : ∀ μ c e, MemLp (a μ c e) 4 volume)
    (w : Fin m → Fin m → L2) (c e : Fin m) (μ : Fin 4) : MemLp (commW a w c e μ) 2 volume :=
  memLp_finsetSum _ fun k _ => ((memLp_four_potL (w k e)).mul' (ha μ c k) (r := 2)).sub
    ((ha μ k e).mul' (memLp_four_potL (w c k)) (r := 2))

/-- `ofCoeff`, with junk value `0` off `ℓ²`. -/
def ofCoeffJ (c : (Fin 4 → ℤ) → ℂ) : L2 :=
  haveI := Classical.propDecidable (Memℓp c 2)
  if hc : Memℓp c 2 then ofCoeff c hc else 0

theorem ofCoeffJ_eq {c : (Fin 4 → ℤ) → ℂ} (hc : Memℓp c 2) : ofCoeffJ c = ofCoeff c hc := by
  unfold ofCoeffJ
  exact dite_cond_eq_true (eq_true hc)

/-- **The fixed-point map** `T w = |∇|⁻¹ d^* (h - [a, |∇|⁻¹ w])`. -/
def Tmap (a : Fin 4 → Fin m → Fin m → 𝕋⁴ → ℂ) (h : Fin m → Fin m → Fin 4 → 𝕋⁴ → ℂ)
    (w : Fin m → Fin m → L2) : Fin m → Fin m → L2 :=
  fun c e => ofCoeffJ (projC fun μ x => h c e μ x - commW a w c e μ x)

theorem memLp_h_sub_commW {a : Fin 4 → Fin m → Fin m → 𝕋⁴ → ℂ}
    (ha : ∀ μ c e, MemLp (a μ c e) 4 volume) {h : Fin m → Fin m → Fin 4 → 𝕋⁴ → ℂ}
    (hh : ∀ c e μ, MemLp (h c e μ) 2 volume) (w : Fin m → Fin m → L2) (c e : Fin m)
    (μ : Fin 4) : MemLp (fun x => h c e μ x - commW a w c e μ x) 2 volume :=
  (hh c e μ).sub (memLp_commW ha w c e μ)

theorem mFourierCoeff_Tmap {a : Fin 4 → Fin m → Fin m → 𝕋⁴ → ℂ}
    (ha : ∀ μ c e, MemLp (a μ c e) 4 volume) {h : Fin m → Fin m → Fin 4 → 𝕋⁴ → ℂ}
    (hh : ∀ c e μ, MemLp (h c e μ) 2 volume) (w : Fin m → Fin m → L2) (c e : Fin m)
    (n : Fin 4 → ℤ) :
    mFourierCoeff ⇑(Tmap a h w c e) n = projC (fun μ x => h c e μ x - commW a w c e μ x) n := by
  rw [Tmap, ofCoeffJ_eq (memℓp_projC (memLp_h_sub_commW ha hh w c e)), mFourierCoeff_ofCoeff]

/-! ### The contraction estimate -/

theorem eLpNorm_Lp_eq (f : L2) : eLpNorm ⇑f 2 volume = ENNReal.ofReal ‖f‖ := by
  rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top f)]

theorem eLpNorm_four_potL_sub_le (w w' : Fin m → Fin m → L2) (k e : Fin m) :
    eLpNorm ⇑(potL (w' k e - w k e)) 4 volume ≤ 28 * ENNReal.ofReal (dist w' w) := by
  refine (eLpNorm_four_potL_le _).trans ?_
  gcongr
  rw [eLpNorm_Lp_eq, ← dist_eq_norm]
  exact ENNReal.ofReal_le_ofReal ((dist_le_pi_dist (w' k) (w k) e).trans (dist_le_pi_dist w' w k))

/-- `‖[a_μ, |∇|⁻¹(w' - w)]_{ce}‖_{L²} ≤ 28 ‖w' - w‖ Σ_k (‖a_{μ,ck}‖_4 + ‖a_{μ,ke}‖_4)`. -/
theorem eLpNorm_commW_sub_le {a : Fin 4 → Fin m → Fin m → 𝕋⁴ → ℂ}
    (ha : ∀ μ c e, MemLp (a μ c e) 4 volume) (w w' : Fin m → Fin m → L2) (c e : Fin m)
    (μ : Fin 4) :
    eLpNorm (fun x => commW a w' c e μ x - commW a w c e μ x) 2 volume ≤
      28 * ENNReal.ofReal (dist w' w) *
        ∑ k, (eLpNorm (a μ c k) 4 volume + eLpNorm (a μ k e) 4 volume) := by
  set Z : Fin m → Fin m → 𝕋⁴ → ℂ := fun k e => ⇑(potL (w' k e - w k e))
  have hZ : ∀ᵐ x ∂volume, ∀ k e, Z k e x = potL (w' k e) x - potL (w k e) x :=
    Filter.eventually_all.2 fun k => Filter.eventually_all.2 fun e => potL_sub _ _
  have hpt : (fun x => commW a w' c e μ x - commW a w c e μ x) =ᵐ[volume]
      ∑ k, fun x => a μ c k x * Z k e x - Z c k x * a μ k e x := by
    filter_upwards [hZ] with x hx
    simp only [commW, Finset.sum_apply, hx, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hZm : ∀ k e, AEStronglyMeasurable (Z k e) volume := fun k e => (Lp.memLp _).1
  have ham : ∀ μ c e, AEStronglyMeasurable (a μ c e) volume := fun μ c e => (ha μ c e).1
  rw [eLpNorm_congr_ae hpt]
  refine (eLpNorm_sum_le (fun k _ => ((ham μ c k).mul (hZm k e)).sub
    ((hZm c k).mul (ham μ k e))) (by norm_num)).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  refine (eLpNorm_sub_le ((ham μ c k).mul (hZm k e)) ((hZm c k).mul (ham μ k e))
    (by norm_num)).trans ?_
  refine (add_le_add (eLpNorm_mul_le_L4 (ham μ c k) (hZm k e))
    (eLpNorm_mul_le_L4 (hZm c k) (ham μ k e))).trans ?_
  calc eLpNorm (a μ c k) 4 volume * eLpNorm (Z k e) 4 volume +
        eLpNorm (Z c k) 4 volume * eLpNorm (a μ k e) 4 volume
      ≤ eLpNorm (a μ c k) 4 volume * (28 * ENNReal.ofReal (dist w' w)) +
        28 * ENNReal.ofReal (dist w' w) * eLpNorm (a μ k e) 4 volume := by
        gcongr
        · exact eLpNorm_four_potL_sub_le w w' k e
        · exact eLpNorm_four_potL_sub_le w w' c k
    _ = 28 * ENNReal.ofReal (dist w' w) *
        (eLpNorm (a μ c k) 4 volume + eLpNorm (a μ k e) 4 volume) := by ring

/-- The difference of two values of `T` is `|∇|⁻¹ d^*` of the commutator difference. -/
theorem Tmap_sub_ae {a : Fin 4 → Fin m → Fin m → 𝕋⁴ → ℂ}
    (ha : ∀ μ c e, MemLp (a μ c e) 4 volume) {h : Fin m → Fin m → Fin 4 → 𝕋⁴ → ℂ}
    (hh : ∀ c e μ, MemLp (h c e μ) 2 volume) (w w' : Fin m → Fin m → L2) (c e : Fin m) :
    ⇑(Tmap a h w' c e - Tmap a h w c e) =ᵐ[volume]
      ⇑(ofCoeff (projC fun μ x => commW a w c e μ x - commW a w' c e μ x)
        (memℓp_projC fun μ => (memLp_commW ha w c e μ).sub (memLp_commW ha w' c e μ))) := by
  refine ae_eq_of_mFourierCoeff_eq (Lp.memLp _) (Lp.memLp _) fun n => ?_
  rw [mFourierCoeff_Lp_sub, mFourierCoeff_Tmap ha hh, mFourierCoeff_Tmap ha hh,
    mFourierCoeff_ofCoeff]
  have hi : ∀ (w : Fin m → Fin m → L2) μ, Integrable (commW a w c e μ) volume := fun w μ =>
    integrable_of_memLp_two (memLp_commW ha w c e μ)
  have hhi : ∀ μ, Integrable (h c e μ) volume := fun μ => integrable_of_memLp_two (hh c e μ)
  have e1 : ∀ (w : Fin m → Fin m → L2) μ,
      mFourierCoeff (fun x => h c e μ x - commW a w c e μ x) n =
        mFourierCoeff (h c e μ) n - mFourierCoeff (commW a w c e μ) n := fun w μ =>
    mFourierCoeff_sub (hhi μ) (hi w μ) n
  have e2 : ∀ μ, mFourierCoeff (fun x => commW a w c e μ x - commW a w' c e μ x) n =
      mFourierCoeff (commW a w c e μ) n - mFourierCoeff (commW a w' c e μ) n := fun μ =>
    mFourierCoeff_sub (hi w μ) (hi w' μ) n
  simp only [projC, invC, e1, e2]
  split_ifs with hn
  · simp
  · rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun μ _ => by ring

/-- **`T` is a contraction with constant `1/2`** when `Σ ‖a_{μ,ce}‖_{L⁴} ≤ 1/112`. -/
theorem dist_Tmap_le {a : Fin 4 → Fin m → Fin m → 𝕋⁴ → ℂ}
    (ha : ∀ μ c e, MemLp (a μ c e) 4 volume)
    (hsmall : ∑ μ, ∑ c, ∑ e, eLpNorm (a μ c e) 4 volume ≤ ENNReal.ofReal (1 / 112))
    {h : Fin m → Fin m → Fin 4 → 𝕋⁴ → ℂ} (hh : ∀ c e μ, MemLp (h c e μ) 2 volume)
    (w w' : Fin m → Fin m → L2) :
    dist (Tmap a h w') (Tmap a h w) ≤ (1 / 2) * dist w' w := by
  set A := ∑ μ, ∑ c, ∑ e, eLpNorm (a μ c e) 4 volume
  set D := ENNReal.ofReal (dist w' w)
  have hD : 0 ≤ (1 / 2) * dist w' w := by positivity
  rw [dist_pi_le_iff hD]; intro c
  rw [dist_pi_le_iff hD]; intro e
  rw [dist_eq_norm, Lp.norm_def]
  refine ENNReal.toReal_le_of_le_ofReal hD ?_
  rw [eLpNorm_congr_ae (Tmap_sub_ae ha hh w w' c e)]
  refine (eLpNorm_ofCoeff_projC_le fun μ =>
    (memLp_commW ha w c e μ).sub (memLp_commW ha w' c e μ)).trans ?_
  have h1 : ∀ μ, eLpNorm (fun x => commW a w c e μ x - commW a w' c e μ x) 2 volume ≤
      28 * D * ∑ k, (eLpNorm (a μ c k) 4 volume + eLpNorm (a μ k e) 4 volume) := by
    intro μ
    have := eLpNorm_commW_sub_le ha w' w c e μ
    rwa [dist_comm] at this
  have hA1 : ∑ μ, ∑ k, eLpNorm (a μ c k) 4 volume ≤ A :=
    Finset.sum_le_sum fun μ _ => Finset.single_le_sum
      (f := fun c' => ∑ k, eLpNorm (a μ c' k) 4 volume) (fun _ _ => zero_le) (Finset.mem_univ c)
  have hA2 : ∑ μ, ∑ k, eLpNorm (a μ k e) 4 volume ≤ A :=
    Finset.sum_le_sum fun μ _ => Finset.sum_le_sum fun k _ => Finset.single_le_sum
      (f := fun e' => eLpNorm (a μ k e') 4 volume) (fun _ _ => zero_le) (Finset.mem_univ e)
  calc ∑ μ, eLpNorm (fun x => commW a w c e μ x - commW a w' c e μ x) 2 volume
      ≤ ∑ μ, 28 * D * ∑ k, (eLpNorm (a μ c k) 4 volume + eLpNorm (a μ k e) 4 volume) :=
        Finset.sum_le_sum fun μ _ => h1 μ
    _ = 28 * D * (∑ μ, ∑ k, eLpNorm (a μ c k) 4 volume +
          ∑ μ, ∑ k, eLpNorm (a μ k e) 4 volume) := by
        rw [← Finset.mul_sum, ← Finset.sum_add_distrib]
        simp only [Finset.sum_add_distrib]
    _ ≤ 28 * D * (ENNReal.ofReal (1 / 112) + ENNReal.ofReal (1 / 112)) := by
        gcongr
        · exact hA1.trans hsmall
        · exact hA2.trans hsmall
    _ = ENNReal.ofReal ((1 / 2) * dist w' w) := by
        rw [← ENNReal.ofReal_add (by norm_num) (by norm_num), show (28 : ℝ≥0∞) =
          ENNReal.ofReal 28 by simp, ← ENNReal.ofReal_mul (by norm_num),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring

theorem contractingWith_Tmap {a : Fin 4 → Fin m → Fin m → 𝕋⁴ → ℂ}
    (ha : ∀ μ c e, MemLp (a μ c e) 4 volume)
    (hsmall : ∑ μ, ∑ c, ∑ e, eLpNorm (a μ c e) 4 volume ≤ ENNReal.ofReal (1 / 112))
    {h : Fin m → Fin m → Fin 4 → 𝕋⁴ → ℂ} (hh : ∀ c e μ, MemLp (h c e μ) 2 volume) :
    ContractingWith (1 / 2 : ℝ≥0) (Tmap a h) := by
  refine ⟨by rw [one_div]; exact inv_lt_one_of_one_lt₀ (by norm_num), ?_⟩
  refine LipschitzWith.of_dist_le_mul fun w' w => ?_
  have := dist_Tmap_le ha hsmall hh w w'
  simpa using this

/-! ### The fixed point solves the weak equation -/

/-- The candidate solution attached to `w`: `ξ = |∇|⁻¹ w` and its partials. -/
abbrev xiW (w : Fin m → Fin m → L2) : Fin m → Fin m → 𝕋⁴ → ℂ := fun c e => ⇑(potL (w c e))

abbrev dxiW (w : Fin m → Fin m → L2) : Fin m → Fin m → Fin 4 → 𝕋⁴ → ℂ :=
  fun c e μ => ⇑(potGradL (w c e) μ)

theorem covLin_xiW_sub (a : Fin 4 → Fin m → Fin m → 𝕋⁴ → ℂ)
    (h : Fin m → Fin m → Fin 4 → 𝕋⁴ → ℂ) (w : Fin m → Fin m → L2) (c e : Fin m) (μ : Fin 4) :
    (fun x => covLin a (xiW w) (dxiW w) c e μ x - h c e μ x) =
      fun x => potGradL (w c e) μ x - (h c e μ x - commW a w c e μ x) := by
  funext x; simp only [covLin, commW, xiW, dxiW]; ring

theorem memLp_covLin_xiW_sub {a : Fin 4 → Fin m → Fin m → 𝕋⁴ → ℂ}
    (ha : ∀ μ c e, MemLp (a μ c e) 4 volume) {h : Fin m → Fin m → Fin 4 → 𝕋⁴ → ℂ}
    (hh : ∀ c e μ, MemLp (h c e μ) 2 volume) (w : Fin m → Fin m → L2) (c e : Fin m)
    (μ : Fin 4) :
    MemLp (fun x => covLin a (xiW w) (dxiW w) c e μ x - h c e μ x) 2 volume := by
  rw [covLin_xiW_sub]
  exact (Lp.memLp _).sub (memLp_h_sub_commW ha hh w c e μ)

/-- **At a fixed point of `T`, the Fourier identity of `d^* (d_a ξ - h) = 0` holds.** -/
theorem fourier_fixedPoint {a : Fin 4 → Fin m → Fin m → 𝕋⁴ → ℂ}
    (ha : ∀ μ c e, MemLp (a μ c e) 4 volume) {h : Fin m → Fin m → Fin 4 → 𝕋⁴ → ℂ}
    (hh : ∀ c e μ, MemLp (h c e μ) 2 volume) {w : Fin m → Fin m → L2} (hw : Tmap a h w = w)
    (c e : Fin m) (n : Fin 4 → ℤ) :
    ∑ μ, conj (sym μ n) *
      mFourierCoeff (fun x => covLin a (xiW w) (dxiW w) c e μ x - h c e μ x) n = 0 := by
  have hc : ∀ μ, mFourierCoeff (fun x => covLin a (xiW w) (dxiW w) c e μ x - h c e μ x) n =
      sym μ n * invC (mFourierCoeff ⇑(w c e)) n -
        mFourierCoeff (fun x => h c e μ x - commW a w c e μ x) n := by
    intro μ
    rw [covLin_xiW_sub, mFourierCoeff_sub (integrable_of_memLp_two (Lp.memLp _))
      (integrable_of_memLp_two (memLp_h_sub_commW ha hh w c e μ)), potGradL,
      mFourierCoeff_ofCoeff]
  have hw' : mFourierCoeff ⇑(w c e) n = projC (fun μ x => h c e μ x - commW a w c e μ x) n := by
    rw [← mFourierCoeff_Tmap ha hh w c e n, hw]
  simp only [hc]
  by_cases hn : n = 0
  · subst hn; simp [sym_zero]
  · have hs : (√(lapSym n) : ℂ) ≠ 0 := by
      have := one_le_sqrt_lapSym hn
      exact_mod_cast (show √(lapSym n) ≠ 0 by linarith)
    have hs2 : (√(lapSym n) : ℂ) ^ 2 = (lapSym n : ℂ) := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (lapSym_nonneg n)]
    set H : Fin 4 → ℂ := fun ν => mFourierCoeff (fun x => h c e ν x - commW a w c e ν x) n
    have hP : projC (fun μ x => h c e μ x - commW a w c e μ x) n =
        (∑ ν, conj (sym ν n) * H ν) / (√(lapSym n) : ℂ) := by
      simp only [projC, invC, if_neg hn, H, Finset.sum_div]
      exact Finset.sum_congr rfl fun ν _ => by ring
    have hS : invC (mFourierCoeff ⇑(w c e)) n =
        (∑ ν, conj (sym ν n) * H ν) / (√(lapSym n) : ℂ) / (√(lapSym n) : ℂ) := by
      simp only [invC, if_neg hn, hw', hP]
    simp only [hS]
    have e1 : ∑ μ, conj (sym μ n) * (sym μ n * ((∑ ν, conj (sym ν n) * H ν) /
        (√(lapSym n) : ℂ) / (√(lapSym n) : ℂ)) - H μ) =
        (∑ μ, conj (sym μ n) * sym μ n) * ((∑ ν, conj (sym ν n) * H ν) /
          (√(lapSym n) : ℂ) / (√(lapSym n) : ℂ)) - ∑ μ, conj (sym μ n) * H μ := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun μ _ => by ring
    rw [e1, sum_conj_sym_mul_sym, ← hs2]
    field_simp
    ring

/-- **The fixed point solves the weak linearised Coulomb equation.** -/
theorem weakLinCoulomb_fixedPoint {a : Fin 4 → Fin m → Fin m → 𝕋⁴ → ℂ}
    (ha : ∀ μ c e, MemLp (a μ c e) 4 volume) {h : Fin m → Fin m → Fin 4 → 𝕋⁴ → ℂ}
    (hh : ∀ c e μ, MemLp (h c e μ) 2 volume) {w : Fin m → Fin m → L2} (hw : Tmap a h w = w) :
    WeakLinCoulomb a h (xiW w) (dxiW w) := by
  intro u gu hu hgu hdu c e
  have h0 := weak_of_fourier (G := fun μ x => covLin a (xiW w) (dxiW w) c e μ x - h c e μ x)
    (memLp_covLin_xiW_sub ha hh w c e) (fourier_fixedPoint ha hh hw c e) hu hgu hdu
  have hC : ∀ μ, MemLp (fun x => covLin a (xiW w) (dxiW w) c e μ x) 2 volume := fun μ => by
    have := (memLp_covLin_xiW_sub ha hh w c e μ).add (hh c e μ)
    convert this using 1
    funext x; simp
  have e : ∀ μ, ∫ x, conj (gu μ x) * (covLin a (xiW w) (dxiW w) c e μ x - h c e μ x) =
      (∫ x, conj (gu μ x) * covLin a (xiW w) (dxiW w) c e μ x) -
        ∫ x, conj (gu μ x) * h c e μ x := fun μ => by
    simp_rw [mul_sub]
    exact integral_sub (integrable_conj_mul (hgu μ) (hC μ)) (integrable_conj_mul (hgu μ) (hh c e μ))
  simp only [e, Finset.sum_sub_distrib] at h0
  exact sub_eq_zero.1 h0

/-! ### Uniqueness: every weak solution comes from a fixed point -/

/-- The coefficients `|n| ξ̂(n)` of `w = |∇|ξ`. -/
def gradC (ξ : 𝕋⁴ → ℂ) (n : Fin 4 → ℤ) : ℂ := (√(lapSym n) : ℂ) * mFourierCoeff ξ n

theorem sum_norm_sym_sq (n : Fin 4 → ℤ) : ∑ μ, ‖sym μ n‖ ^ 2 = lapSym n := by
  simp only [norm_sym_sq, lapSym]

theorem memℓp_gradC {ξ : 𝕋⁴ → ℂ} {dξ : Fin 4 → 𝕋⁴ → ℂ} (hdξ : ∀ μ, MemLp (dξ μ) 2 volume)
    (hd : ∀ μ, IsTPartial μ ξ (dξ μ)) : Memℓp (gradC ξ) 2 := by
  refine memℓp_two_of_le (f := fun n => ((√(∑ μ, ‖mFourierCoeff (dξ μ) n‖ ^ 2) : ℝ) : ℂ))
    ?_ fun n => ?_
  · refine (summable_sum (s := Finset.univ) fun μ _ =>
      summable_sq_mFourierCoeff (hdξ μ)).congr fun n => ?_
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs,
      Real.sq_sqrt (Finset.sum_nonneg fun _ _ => by positivity)]
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), gradC,
      norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    have e : ∑ μ, ‖mFourierCoeff (dξ μ) n‖ ^ 2 = lapSym n * ‖mFourierCoeff ξ n‖ ^ 2 := by
      simp only [hd _ n, norm_mul, mul_pow, ← Finset.sum_mul, sum_norm_sym_sq]
    rw [e, Real.sqrt_mul (lapSym_nonneg n), Real.sqrt_sq (norm_nonneg _)]

theorem potL_ofCoeff_gradC {ξ : 𝕋⁴ → ℂ} (hξ : MemLp ξ 2 volume) (h0 : mFourierCoeff ξ 0 = 0)
    (hg : Memℓp (gradC ξ) 2) : ⇑(potL (ofCoeff (gradC ξ) hg)) =ᵐ[volume] ξ := by
  refine ae_eq_of_mFourierCoeff_eq (Lp.memLp _) hξ fun n => ?_
  have e : mFourierCoeff ⇑(ofCoeff (gradC ξ) hg) = gradC ξ := funext (mFourierCoeff_ofCoeff _ _)
  rw [mFourierCoeff_potL, e, invC]
  split_ifs with hn
  · subst hn; exact h0.symm
  · have hs : (√(lapSym n) : ℂ) ≠ 0 := by
      have := one_le_sqrt_lapSym hn
      exact_mod_cast (show √(lapSym n) ≠ 0 by linarith)
    rw [gradC]; field_simp

/-- **Uniqueness**: a mean-zero `H¹` weak solution of `d^* d_a ξ' = d^* h` is `|∇|⁻¹ w` for a
fixed point `w` of `T` (and the fixed point is unique). -/
theorem eq_of_weakLinCoulomb {a : Fin 4 → Fin m → Fin m → 𝕋⁴ → ℂ}
    (ha : ∀ μ c e, MemLp (a μ c e) 4 volume)
    (hsmall : ∑ μ, ∑ c, ∑ e, eLpNorm (a μ c e) 4 volume ≤ ENNReal.ofReal (1 / 112))
    {h : Fin m → Fin m → Fin 4 → 𝕋⁴ → ℂ} (hh : ∀ c e μ, MemLp (h c e μ) 2 volume)
    {w : Fin m → Fin m → L2} (hw : Tmap a h w = w)
    {ξ' : Fin m → Fin m → 𝕋⁴ → ℂ} {dξ' : Fin m → Fin m → Fin 4 → 𝕋⁴ → ℂ}
    (hξ' : ∀ c e, MemLp (ξ' c e) 2 volume) (hdξ' : ∀ c e μ, MemLp (dξ' c e μ) 2 volume)
    (hd' : ∀ c e μ, IsTPartial μ (ξ' c e) (dξ' c e μ)) (h0' : ∀ c e, mFourierCoeff (ξ' c e) 0 = 0)
    (hweak : WeakLinCoulomb a h ξ' dξ') : ∀ c e, ξ' c e =ᵐ[volume] ⇑(potL (w c e)) := by
  have hg : ∀ c e, Memℓp (gradC (ξ' c e)) 2 := fun c e => memℓp_gradC (hdξ' c e) (hd' c e)
  set w' : Fin m → Fin m → L2 := fun c e => ofCoeff (gradC (ξ' c e)) (hg c e)
  have hpot : ∀ c e, ⇑(potL (w' c e)) =ᵐ[volume] ξ' c e := fun c e =>
    potL_ofCoeff_gradC (hξ' c e) (h0' c e) (hg c e)
  have hpotall : ∀ᵐ x ∂volume, ∀ c e, potL (w' c e) x = ξ' c e x :=
    Filter.eventually_all.2 fun c => Filter.eventually_all.2 fun e => hpot c e
  -- the weak equation, as a Fourier identity
  have hG : ∀ c e μ, (fun x => covLin a ξ' dξ' c e μ x - h c e μ x) =ᵐ[volume]
      fun x => dξ' c e μ x - (h c e μ x - commW a w' c e μ x) := by
    intro c e μ
    filter_upwards [hpotall] with x hx
    simp only [covLin, commW, hx]; ring
  have hGm : ∀ c e μ, MemLp (fun x => covLin a ξ' dξ' c e μ x - h c e μ x) 2 volume :=
    fun c e μ => ((hdξ' c e μ).sub (memLp_h_sub_commW ha hh w' c e μ)).ae_eq (hG c e μ).symm
  have hCm : ∀ c e μ, MemLp (fun x => covLin a ξ' dξ' c e μ x) 2 volume := fun c e μ => by
    have := (hGm c e μ).add (hh c e μ)
    convert this using 1
    funext x; simp
  have hF : ∀ c e n, ∑ μ, conj (sym μ n) *
      (sym μ n * mFourierCoeff (ξ' c e) n -
        mFourierCoeff (fun x => h c e μ x - commW a w' c e μ x) n) = 0 := by
    intro c e n
    have hw0 := fourier_of_weak (G := fun μ x => covLin a ξ' dξ' c e μ x - h c e μ x)
      (fun u gu hu hgu hdu => by
        have he : ∀ μ, ∫ x, conj (gu μ x) * (covLin a ξ' dξ' c e μ x - h c e μ x) =
            (∫ x, conj (gu μ x) * covLin a ξ' dξ' c e μ x) -
              ∫ x, conj (gu μ x) * h c e μ x := fun μ => by
          simp_rw [mul_sub]
          exact integral_sub (integrable_conj_mul (hgu μ) (hCm c e μ))
            (integrable_conj_mul (hgu μ) (hh c e μ))
        simp only [he, Finset.sum_sub_distrib]
        exact sub_eq_zero.2 (hweak u gu hu hgu hdu c e)) n
    have hc : ∀ μ, mFourierCoeff (fun x => covLin a ξ' dξ' c e μ x - h c e μ x) n =
        sym μ n * mFourierCoeff (ξ' c e) n -
          mFourierCoeff (fun x => h c e μ x - commW a w' c e μ x) n := by
      intro μ
      have e1 : mFourierCoeff (fun x => covLin a ξ' dξ' c e μ x - h c e μ x) n =
          mFourierCoeff (fun x => dξ' c e μ x - (h c e μ x - commW a w' c e μ x)) n := by
        unfold mFourierCoeff
        exact integral_congr_ae ((hG c e μ).mono fun x hx => by simp only [hx])
      rw [e1, mFourierCoeff_sub (integrable_of_memLp_two (hdξ' c e μ))
        (integrable_of_memLp_two (memLp_h_sub_commW ha hh w' c e μ)), hd' c e μ n]
    simpa only [hc] using hw0
  -- `w'` is a fixed point
  have hfix : Tmap a h w' = w' := by
    funext c e
    refine Lp.ext (ae_eq_of_mFourierCoeff_eq (Lp.memLp _) (Lp.memLp _) fun n => ?_)
    rw [mFourierCoeff_Tmap ha hh, show mFourierCoeff ⇑(w' c e) n = gradC (ξ' c e) n from
      mFourierCoeff_ofCoeff _ _ n]
    set H : Fin 4 → ℂ := fun ν => mFourierCoeff (fun x => h c e ν x - commW a w' c e ν x) n
    by_cases hn : n = 0
    · subst hn; simp [projC, invC, gradC, h0' c e]
    · have hs : (√(lapSym n) : ℂ) ≠ 0 := by
        have := one_le_sqrt_lapSym hn
        exact_mod_cast (show √(lapSym n) ≠ 0 by linarith)
      have hs2 : (√(lapSym n) : ℂ) ^ 2 = (lapSym n : ℂ) := by
        rw [← Complex.ofReal_pow, Real.sq_sqrt (lapSym_nonneg n)]
      have hF' := hF c e n
      have e1 : ∑ μ, conj (sym μ n) * (sym μ n * mFourierCoeff (ξ' c e) n - H μ) =
          (lapSym n : ℂ) * mFourierCoeff (ξ' c e) n - ∑ μ, conj (sym μ n) * H μ := by
        rw [← sum_conj_sym_mul_sym, Finset.sum_mul, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun μ _ => by ring
      rw [e1, sub_eq_zero] at hF'
      have hP : projC (fun μ x => h c e μ x - commW a w' c e μ x) n =
          (∑ ν, conj (sym ν n) * H ν) / (√(lapSym n) : ℂ) := by
        simp only [projC, invC, if_neg hn, H, Finset.sum_div]
        exact Finset.sum_congr rfl fun ν _ => by ring
      rw [hP, ← hF', gradC, ← hs2]
      field_simp
  -- uniqueness of the fixed point
  have hK := contractingWith_Tmap ha hsmall hh
  have hww : w' = w := hK.fixedPoint_unique' hfix hw
  intro c e
  rw [← hww]
  exact (hpot c e).symm

/-! ### The isomorphism theorem -/

theorem potL_zero_ae : ⇑(potL (0 : L2)) =ᵐ[volume] 0 := by
  refine ae_eq_zero_of_mFourierCoeff_eq_zero (Lp.memLp _) fun n => ?_
  have hz : ∀ k, mFourierCoeff ⇑(0 : L2) k = 0 := by
    intro k
    unfold mFourierCoeff
    rw [integral_congr_ae ((Lp.coeFn_zero ℂ 2 volume).mono fun x hx => by
      show mFourier (-k) x • (0 : L2) x = mFourier (-k) x • (0 : 𝕋⁴ → ℂ) x; rw [hx])]
    simp
  rw [mFourierCoeff_potL]
  unfold invC
  split_ifs with hn
  · rfl
  · rw [hz n, zero_div]

theorem eLpNorm_Tmap_zero_le {a : Fin 4 → Fin m → Fin m → 𝕋⁴ → ℂ}
    (ha : ∀ μ c e, MemLp (a μ c e) 4 volume) {h : Fin m → Fin m → Fin 4 → 𝕋⁴ → ℂ}
    (hh : ∀ c e μ, MemLp (h c e μ) 2 volume) (c e : Fin m) :
    eLpNorm ⇑(Tmap a h 0 c e) 2 volume ≤ ∑ μ, eLpNorm (h c e μ) 2 volume := by
  rw [Tmap, ofCoeffJ_eq (memℓp_projC (memLp_h_sub_commW ha hh 0 c e))]
  refine (eLpNorm_ofCoeff_projC_le (memLp_h_sub_commW ha hh 0 c e)).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun μ _ => eLpNorm_congr_ae ?_
  filter_upwards [potL_zero_ae] with x hx
  simp [commW, hx]

/-- **The linearised Coulomb operator at a connection with small `L⁴` norm is an isomorphism
`H¹₀ → H⁻¹₀` on `𝕋⁴`** (the linear input of the implicit-function / openness step of Uhlenbeck's
continuity method; the case `a = 0` is the Laplacian, `laplace_solve`).  If the entries of the
matrix-valued one-form `a` lie in `L⁴` with `Σ_{μ,c,e} ‖a_{μ,ce}‖_{L⁴} ≤ 1/112`, then for every
matrix-valued one-form `h` with `L²` entries there is a mean-zero matrix function `ξ` with `H¹`
entries solving `d^*(dξ + [a, ξ]) = d^* h` weakly (`WeakLinCoulomb`), with
`‖∂_μ ξ_{ce}‖_{L²} ≤ 2 Σ ‖h‖_{L²}`, and every other mean-zero `H¹` weak solution agrees with `ξ`
a.e.  (No Coulomb condition on `a` is needed.) -/
theorem linearized_coulomb_iso (a : Fin 4 → Fin m → Fin m → 𝕋⁴ → ℂ)
    (ha : ∀ μ c e, MemLp (a μ c e) 4 volume)
    (hsmall : ∑ μ, ∑ c, ∑ e, eLpNorm (a μ c e) 4 volume ≤ ENNReal.ofReal (1 / 112))
    (h : Fin m → Fin m → Fin 4 → 𝕋⁴ → ℂ) (hh : ∀ c e μ, MemLp (h c e μ) 2 volume) :
    ∃ (ξ : Fin m → Fin m → 𝕋⁴ → ℂ) (dξ : Fin m → Fin m → Fin 4 → 𝕋⁴ → ℂ),
      (∀ c e, MemLp (ξ c e) 2 volume) ∧ (∀ c e μ, MemLp (dξ c e μ) 2 volume) ∧
      (∀ c e μ, IsTPartial μ (ξ c e) (dξ c e μ)) ∧ (∀ c e, mFourierCoeff (ξ c e) 0 = 0) ∧
      WeakLinCoulomb a h ξ dξ ∧
      (∀ c e μ, eLpNorm (dξ c e μ) 2 volume ≤
        2 * ∑ c', ∑ e', ∑ μ', eLpNorm (h c' e' μ') 2 volume) ∧
      ∀ (ξ' : Fin m → Fin m → 𝕋⁴ → ℂ) (dξ' : Fin m → Fin m → Fin 4 → 𝕋⁴ → ℂ),
        (∀ c e, MemLp (ξ' c e) 2 volume) → (∀ c e μ, MemLp (dξ' c e μ) 2 volume) →
        (∀ c e μ, IsTPartial μ (ξ' c e) (dξ' c e μ)) → (∀ c e, mFourierCoeff (ξ' c e) 0 = 0) →
        WeakLinCoulomb a h ξ' dξ' → ∀ c e, ξ' c e =ᵐ[volume] ξ c e := by
  have hK := contractingWith_Tmap ha hsmall hh
  set w := ContractingWith.fixedPoint (Tmap a h) hK
  have hw : Tmap a h w = w := ContractingWith.fixedPoint_isFixedPt hK
  refine ⟨xiW w, dxiW w, fun c e => Lp.memLp _, fun c e μ => Lp.memLp _,
    fun c e μ => isTPartial_potL _ μ, fun c e => potL_mean_zero _,
    weakLinCoulomb_fixedPoint ha hh hw, ?_, fun ξ' dξ' hξ' hdξ' hd' h0' hweak =>
      eq_of_weakLinCoulomb ha hsmall hh hw hξ' hdξ' hd' h0' hweak⟩
  -- the bound
  set S : ℝ≥0∞ := ∑ c', ∑ e', ∑ μ', eLpNorm (h c' e' μ') 2 volume
  have hSt : S ≠ ⊤ := ENNReal.sum_ne_top.2 fun c _ => ENNReal.sum_ne_top.2 fun e _ =>
    ENNReal.sum_ne_top.2 fun μ _ => (hh c e μ).2.ne
  have hT0 : ‖Tmap a h 0‖ ≤ S.toReal := by
    refine (pi_norm_le_iff_of_nonneg ENNReal.toReal_nonneg).2 fun c => ?_
    refine (pi_norm_le_iff_of_nonneg ENNReal.toReal_nonneg).2 fun e => ?_
    rw [Lp.norm_def]
    refine ENNReal.toReal_mono hSt ((eLpNorm_Tmap_zero_le ha hh c e).trans ?_)
    exact (Finset.single_le_sum (f := fun e' => ∑ μ', eLpNorm (h c e' μ') 2 volume)
      (fun _ _ => zero_le) (Finset.mem_univ e)).trans
      (Finset.single_le_sum (f := fun c' => ∑ e', ∑ μ', eLpNorm (h c' e' μ') 2 volume)
        (fun _ _ => zero_le) (Finset.mem_univ c))
  have hwn : ‖w‖ ≤ 2 * S.toReal := by
    have h1 := hK.dist_fixedPoint_le 0
    rw [dist_zero_left, dist_zero_left] at h1
    have h2 : (1 : ℝ) - ((1 / 2 : ℝ≥0) : ℝ) = 1 / 2 := by norm_num
    rw [h2] at h1
    linarith
  intro c e μ
  refine (eLpNorm_potGradL_le _ μ).trans ?_
  rw [eLpNorm_Lp_eq]
  calc ENNReal.ofReal ‖w c e‖ ≤ ENNReal.ofReal (2 * S.toReal) :=
        ENNReal.ofReal_le_ofReal ((norm_le_pi_norm (w c) e).trans ((norm_le_pi_norm w c).trans hwn))
    _ = 2 * S := by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_toReal hSt]; simp

/-- Non-vacuity: the hypotheses of `linearized_coulomb_iso` hold for `a = 0`, `h = 0`. -/
example (m : ℕ) : ∃ (ξ : Fin m → Fin m → 𝕋⁴ → ℂ) (dξ : Fin m → Fin m → Fin 4 → 𝕋⁴ → ℂ),
    WeakLinCoulomb (m := m) (fun _ _ _ _ => 0) (fun _ _ _ _ => 0) ξ dξ := by
  obtain ⟨ξ, dξ, -, -, -, -, hw, -⟩ := linearized_coulomb_iso (m := m) (fun _ _ _ _ => 0)
    (fun _ _ _ => memLp_const 0) (by simp) (fun _ _ _ _ => 0) (fun _ _ _ => memLp_const 0)
  exact ⟨ξ, dξ, hw⟩

end RenewalGeometry.UhlenbeckOpenness
