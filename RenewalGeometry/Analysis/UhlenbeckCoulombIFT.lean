/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.UhlenbeckHodgeEstimate

/-!
# The linearised Coulomb problem at the trivial connection: the Laplacian on mean-zero functions,
  and the abelian Coulomb gauge (step (b) of Uhlenbeck's small-energy gauge theorem)

Generic infrastructure (no renewal notions) for `prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript (K. Uhlenbeck, Comm. Math. Phys. 83 (1982),
Thm 1.3).  In the implicit-function step of Uhlenbeck's proof the Coulomb condition
`d^*(e^{ξ}·A) = 0` is linearised at `A = 0`, `ξ = 0`; the linearisation is the Laplacian
`ξ ↦ Δξ`, which must be an isomorphism from mean-zero `H²` onto mean-zero `L²`.  This file proves
that isomorphism on the flat torus `𝕋^d` (Fourier multipliers), and, as the linear (abelian)
instance of the theorem, the existence of the Coulomb gauge for abelian connections.

* `ofCoeff`, `mFourierCoeff_ofCoeff`: the `L²` function with prescribed square-summable Fourier
  coefficients (inverse of Parseval, `mFourierBasis.repr.symm`).
* `ae_eq_zero_of_mFourierCoeff_eq_zero`: an `L²` function with vanishing Fourier coefficients
  vanishes a.e.
* `lapSym n = 4π²|n|²` and `laplace_solve` (**the Laplacian is onto mean-zero `L²`, with `H²`
  bounds**): for `f ∈ L²` with `f̂(0) = 0` there is a mean-zero `ξ ∈ L²` with partials
  `∂_μ ξ ∈ L²` and second partials `∂_ν ∂_μ ξ ∈ L²` such that `Σ_μ ∂_μ∂_μ ξ = f` a.e. and
  `‖∂_ν∂_μ ξ‖_{L²} ≤ ‖f‖_{L²}`, `‖∂_μ ξ‖_{L²} ≤ ‖f‖_{L²}`, `‖ξ‖_{L²} ≤ ‖f‖_{L²}`.
* `laplace_unique` (**injectivity**): a mean-zero `ξ` with `Δξ = 0` vanishes a.e.
* `abelian_coulomb_gauge` (**Coulomb gauge for abelian connections**, `G = U(1)` or any torus
  group, every energy): every one-form `a` on `𝕋^d` with `H¹` components can be written
  `a = a' + dψ` with `a'` co-closed (`d^*a' = 0`), `da' = da`, and
  `‖∂_μ a'_ν‖_{L²} ≤ Σ_{μ'ν'} ‖(da)_{μ'ν'}‖_{L²}` — the abelian case of Uhlenbeck's theorem
  (`a' = e^{ψ}·a` for the gauge `e^{ψ}`); no smallness is needed since `[a ∧ a] = 0`.

The nonlinear implicit-function step itself (`C¹`-dependence of `ξ ↦ d^*(e^{ξ}·A)` in a Banach
algebra of matrix functions on which the exponential acts, `H^s`, `s > 2`, in dimension four) and
the surjectivity of the linearisation at a nonzero small Coulomb connection (Fredholm index zero
plus `linearized_coulomb_kernel_const`) are **not** proved here.
-/

open MeasureTheory Filter Topology Set UnitAddTorus
open scoped ENNReal NNReal Real ComplexConjugate

noncomputable section

namespace RenewalGeometry.UhlenbeckTorus

open SobolevOpen TorusSobolev

set_option linter.unusedSectionVars false

attribute [local instance 2000] instMeasureSpaceUnitAddCircle

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

local notation "L²(" α ")" => Lp ℂ 2 (volume : Measure α)

variable {d : Type*} [Fintype d] [DecidableEq d]

/-! ### Functions from Fourier coefficients -/

/-- The `L²(𝕋^d)` function with square-summable Fourier coefficients `c`. -/
def ofCoeff (c : (d → ℤ) → ℂ) (hc : Memℓp c 2) : L²(UnitAddTorus d) :=
  mFourierBasis.repr.symm ⟨c, hc⟩

theorem mFourierCoeff_ofCoeff (c : (d → ℤ) → ℂ) (hc : Memℓp c 2) (n : d → ℤ) :
    mFourierCoeff (ofCoeff c hc) n = c n := by
  rw [← mFourierBasis_repr]
  simp [ofCoeff]

theorem memℓp_two_of_le {c f : (d → ℤ) → ℂ} (hf : Summable fun n => ‖f n‖ ^ 2)
    (hle : ∀ n, ‖c n‖ ≤ ‖f n‖) : Memℓp c 2 := by
  rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
  refine hf.of_nonneg_of_le (fun n => by positivity) fun n => ?_
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  exact pow_le_pow_left₀ (norm_nonneg _) (hle n) 2

/-- An `L²` function all of whose Fourier coefficients vanish is zero a.e. -/
theorem ae_eq_zero_of_mFourierCoeff_eq_zero {f : UnitAddTorus d → ℂ} (hf : MemLp f 2 volume)
    (h : ∀ n, mFourierCoeff f n = 0) : f =ᵐ[volume] 0 := by
  have hs := hasSum_sq_mFourierCoeff_of_memLp hf
  simp only [h, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hs
  have hI : ∫ t, ‖f t‖ ^ 2 = 0 := (hasSum_zero.unique hs).symm
  have hE : eLpNorm f 2 volume = 0 := by
    rw [eLpNorm_two_eq_sqrt hf, hI, Real.sqrt_zero, ENNReal.ofReal_zero]
  exact (eLpNorm_eq_zero_iff hf.1 (by norm_num)).1 hE

/-- Two `L²` functions with the same Fourier coefficients agree a.e. -/
theorem ae_eq_of_mFourierCoeff_eq {f g : UnitAddTorus d → ℂ} (hf : MemLp f 2 volume)
    (hg : MemLp g 2 volume) (h : ∀ n, mFourierCoeff f n = mFourierCoeff g n) :
    f =ᵐ[volume] g := by
  have h0 := ae_eq_zero_of_mFourierCoeff_eq_zero (hf.sub hg) fun n => by
    rw [show (f - g) = fun x => f x - g x from rfl,
      mFourierCoeff_sub (integrable_of_memLp_two hf) (integrable_of_memLp_two hg), h n, sub_self]
  filter_upwards [h0] with x hx
  simpa [sub_eq_zero] using hx

/-! ### The Laplacian on mean-zero functions -/

/-- The symbol `4π²|n|² = Σ_i (2π n_i)²` of `-Δ`. -/
def lapSym (n : d → ℤ) : ℝ := ∑ i, (2 * π * (n i : ℝ)) ^ 2

theorem lapSym_nonneg (n : d → ℤ) : 0 ≤ lapSym n := Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem one_le_lapSym {n : d → ℤ} (hn : n ≠ 0) : 1 ≤ lapSym n := by
  obtain ⟨μ, hμ⟩ : ∃ μ, n μ ≠ 0 := by
    by_contra h; exact hn (funext fun μ => by simpa using not_exists.mp h μ)
  have h1 : (1 : ℝ) ≤ (n μ : ℝ) ^ 2 := by
    have : (1 : ℤ) ≤ (n μ) ^ 2 := by
      rcases lt_or_gt_of_ne hμ with h | h <;> nlinarith
    exact_mod_cast this
  have h2 : 1 ≤ (2 * π * (n μ : ℝ)) ^ 2 := by
    have := four_pi_sq_ge_one
    calc (1 : ℝ) ≤ 4 * π ^ 2 * 1 := by linarith
      _ ≤ 4 * π ^ 2 * (n μ : ℝ) ^ 2 := by gcongr
      _ = (2 * π * (n μ : ℝ)) ^ 2 := by ring
  exact h2.trans (Finset.single_le_sum (f := fun i => (2 * π * (n i : ℝ)) ^ 2)
    (fun _ _ => sq_nonneg _) (Finset.mem_univ μ))

theorem sq_sym_le_lapSym (μ : d) (n : d → ℤ) : (2 * π * (n μ : ℝ)) ^ 2 ≤ lapSym n :=
  Finset.single_le_sum (f := fun i => (2 * π * (n i : ℝ)) ^ 2) (fun _ _ => sq_nonneg _)
    (Finset.mem_univ μ)

theorem sum_sym_sq (n : d → ℤ) : ∑ μ, sym μ n * sym μ n = -(lapSym n : ℂ) := by
  simp only [lapSym, sym]
  push_cast
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The coefficients of the mean-zero solution of `Δξ = f`. -/
def lapInvCoeff (f : (d → ℤ) → ℂ) (n : d → ℤ) : ℂ :=
  if n = 0 then 0 else -f n / (lapSym n : ℂ)

theorem norm_lapInvCoeff_mul_le (f : (d → ℤ) → ℂ) (n : d → ℤ) (w : ℂ)
    (hw : ‖w‖ ≤ lapSym n) : ‖w * lapInvCoeff f n‖ ≤ ‖f n‖ := by
  unfold lapInvCoeff
  split_ifs with hn
  · simp
  · have hL := one_le_lapSym hn
    rw [norm_mul, norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith)]
    rw [mul_div_assoc', div_le_iff₀ (by linarith)]
    calc ‖w‖ * ‖f n‖ ≤ lapSym n * ‖f n‖ := by gcongr
      _ = ‖f n‖ * lapSym n := by ring

theorem norm_sym_le_lapSym (μ : d) (n : d → ℤ) : ‖sym μ n‖ ≤ lapSym n ∨ n = 0 := by
  by_cases hn : n = 0
  · exact Or.inr hn
  · left
    have hL := one_le_lapSym hn
    have h1 : ‖sym μ n‖ ^ 2 ≤ lapSym n := by rw [norm_sym_sq]; exact sq_sym_le_lapSym μ n
    nlinarith [norm_nonneg (sym μ n)]

theorem norm_sym_mul_sym_le (μ ν : d) (n : d → ℤ) : ‖sym μ n * sym ν n‖ ≤ lapSym n := by
  rw [norm_mul]
  have h1 := norm_sym_sq μ n
  have h2 := norm_sym_sq ν n
  have h3 := sq_sym_le_lapSym μ n
  have h4 := sq_sym_le_lapSym ν n
  by_cases hμν : μ = ν
  · subst hμν; rw [← sq, h1]; exact h3
  · have h5 : (2 * π * (n μ : ℝ)) ^ 2 + (2 * π * (n ν : ℝ)) ^ 2 ≤ lapSym n := by
      have := Finset.sum_le_sum_of_subset_of_nonneg (f := fun i => (2 * π * (n i : ℝ)) ^ 2)
        (Finset.subset_univ {μ, ν}) (fun _ _ _ => sq_nonneg _)
      rw [Finset.sum_pair hμν] at this
      exact this
    nlinarith [norm_nonneg (sym μ n), norm_nonneg (sym ν n),
      sq_nonneg (‖sym μ n‖ - ‖sym ν n‖)]

/-- **The Laplacian is an isomorphism from mean-zero `H²` onto mean-zero `L²`** (existence with
the `H²` bound; uniqueness is `laplace_unique`).  For `f ∈ L²(𝕋^d)` with `f̂(0) = 0` there are
`ξ, ∂_μ ξ, ∂_ν∂_μ ξ ∈ L²` (Fourier rule), `ξ̂(0) = 0`, with `Σ_μ ∂_μ∂_μ ξ = f` a.e. and
`‖∂_ν∂_μ ξ‖_{L²}, ‖∂_μ ξ‖_{L²}, ‖ξ‖_{L²} ≤ ‖f‖_{L²}`. -/
theorem laplace_solve {f : UnitAddTorus d → ℂ} (hf : MemLp f 2 volume)
    (h0 : mFourierCoeff f 0 = 0) :
    ∃ (ξ : UnitAddTorus d → ℂ) (dξ : d → UnitAddTorus d → ℂ) (d2ξ : d → d → UnitAddTorus d → ℂ),
      MemLp ξ 2 volume ∧ (∀ μ, MemLp (dξ μ) 2 volume) ∧ (∀ μ ν, MemLp (d2ξ μ ν) 2 volume) ∧
      mFourierCoeff ξ 0 = 0 ∧ (∀ μ, IsTPartial μ ξ (dξ μ)) ∧
      (∀ μ ν, IsTPartial ν (dξ μ) (d2ξ μ ν)) ∧ (∀ᵐ x ∂volume, ∑ μ, d2ξ μ μ x = f x) ∧
      (∀ μ ν, eLpNorm (d2ξ μ ν) 2 volume ≤ eLpNorm f 2 volume) ∧
      (∀ μ, eLpNorm (dξ μ) 2 volume ≤ eLpNorm f 2 volume) ∧
      eLpNorm ξ 2 volume ≤ eLpNorm f 2 volume := by
  set F := mFourierCoeff f
  have hFs : Summable fun n => ‖F n‖ ^ 2 := (hasSum_sq_mFourierCoeff_of_memLp hf).summable
  set c := lapInvCoeff F
  -- coefficient bounds
  have hb0 : ∀ n, ‖c n‖ ≤ ‖F n‖ := fun n => by
    by_cases hn : n = 0
    · subst hn; simp [c, lapInvCoeff]
    · have := norm_lapInvCoeff_mul_le F n 1 (by simpa using one_le_lapSym hn)
      simpa using this
  have hb1 : ∀ μ n, ‖sym μ n * c n‖ ≤ ‖F n‖ := fun μ n => by
    rcases norm_sym_le_lapSym μ n with h | h
    · exact norm_lapInvCoeff_mul_le F n _ h
    · subst h; simp [c, lapInvCoeff]
  have hb2 : ∀ μ ν n, ‖sym ν n * (sym μ n * c n)‖ ≤ ‖F n‖ := fun μ ν n => by
    rw [← mul_assoc, mul_comm (sym ν n)]
    exact norm_lapInvCoeff_mul_le F n _ (norm_sym_mul_sym_le μ ν n)
  have hm0 : Memℓp c 2 := memℓp_two_of_le hFs hb0
  have hm1 : ∀ μ, Memℓp (fun n => sym μ n * c n) 2 := fun μ => memℓp_two_of_le hFs (hb1 μ)
  have hm2 : ∀ μ ν, Memℓp (fun n => sym ν n * (sym μ n * c n)) 2 := fun μ ν =>
    memℓp_two_of_le hFs (hb2 μ ν)
  refine ⟨ofCoeff c hm0, fun μ => ofCoeff _ (hm1 μ), fun μ ν => ofCoeff _ (hm2 μ ν),
    Lp.memLp _, fun μ => Lp.memLp _, fun μ ν => Lp.memLp _, ?_, fun μ n => ?_,
    fun μ ν n => ?_, ?_, ?_, ?_, ?_⟩
  · rw [mFourierCoeff_ofCoeff]; simp [c, lapInvCoeff]
  · rw [mFourierCoeff_ofCoeff, mFourierCoeff_ofCoeff]
  · rw [mFourierCoeff_ofCoeff, mFourierCoeff_ofCoeff]
  · -- `Σ_μ ∂_μ∂_μ ξ = f`
    have hsum2 : MemLp (fun x => ∑ μ, (ofCoeff _ (hm2 μ μ) : UnitAddTorus d → ℂ) x) 2 volume :=
      memLp_finsetSum _ fun μ _ => Lp.memLp _
    refine ae_eq_of_mFourierCoeff_eq hsum2 hf fun n => ?_
    rw [mFourierCoeff_finset_sum _ fun μ => integrable_of_memLp_two (Lp.memLp _)]
    simp only [mFourierCoeff_ofCoeff]
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul, sum_sym_sq]
    simp only [c, lapInvCoeff]
    split_ifs with hn
    · subst hn; simp [F, h0]
    · have hL : (lapSym n : ℂ) ≠ 0 := by
        have := one_le_lapSym hn
        exact_mod_cast (show lapSym n ≠ 0 by linarith)
      field_simp
      rfl
  · intro μ ν
    have h1 := hasSum_sq_mFourierCoeff_of_memLp (Lp.memLp (ofCoeff _ (hm2 μ ν)))
    simp only [mFourierCoeff_ofCoeff] at h1
    rw [eLpNorm_two_eq_sqrt (Lp.memLp _), eLpNorm_two_eq_sqrt hf]
    refine ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt ?_)
    exact hasSum_le (fun n => pow_le_pow_left₀ (norm_nonneg _) (hb2 μ ν n) 2) h1
      (hasSum_sq_mFourierCoeff_of_memLp hf)
  · intro μ
    have h1 := hasSum_sq_mFourierCoeff_of_memLp (Lp.memLp (ofCoeff _ (hm1 μ)))
    simp only [mFourierCoeff_ofCoeff] at h1
    rw [eLpNorm_two_eq_sqrt (Lp.memLp _), eLpNorm_two_eq_sqrt hf]
    refine ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt ?_)
    exact hasSum_le (fun n => pow_le_pow_left₀ (norm_nonneg _) (hb1 μ n) 2) h1
      (hasSum_sq_mFourierCoeff_of_memLp hf)
  · have h1 := hasSum_sq_mFourierCoeff_of_memLp (Lp.memLp (ofCoeff c hm0))
    simp only [mFourierCoeff_ofCoeff] at h1
    rw [eLpNorm_two_eq_sqrt (Lp.memLp _), eLpNorm_two_eq_sqrt hf]
    refine ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt ?_)
    exact hasSum_le (fun n => pow_le_pow_left₀ (norm_nonneg _) (hb0 n) 2) h1
      (hasSum_sq_mFourierCoeff_of_memLp hf)

/-- **Uniqueness for the Laplacian on mean-zero functions**: if `ξ ∈ L²` has mean zero, `L²`
partials and second partials, and `Σ_μ ∂_μ∂_μ ξ = 0` a.e., then `ξ = 0` a.e. -/
theorem laplace_unique {ξ : UnitAddTorus d → ℂ} {dξ : d → UnitAddTorus d → ℂ}
    {d2ξ : d → d → UnitAddTorus d → ℂ} (hξ : MemLp ξ 2 volume)
    (hd2 : ∀ μ ν, MemLp (d2ξ μ ν) 2 volume) (h0 : mFourierCoeff ξ 0 = 0)
    (hd : ∀ μ, IsTPartial μ ξ (dξ μ)) (hdd : ∀ μ ν, IsTPartial ν (dξ μ) (d2ξ μ ν))
    (hΔ : ∀ᵐ x ∂volume, ∑ μ, d2ξ μ μ x = 0) : ξ =ᵐ[volume] 0 := by
  refine ae_eq_zero_of_mFourierCoeff_eq_zero hξ fun n => ?_
  have hc : mFourierCoeff (fun x => ∑ μ, d2ξ μ μ x) n = 0 := by
    rw [show mFourierCoeff (fun x => ∑ μ, d2ξ μ μ x) n = mFourierCoeff (fun _ => (0 : ℂ)) n from
      congrArg (fun g => mFourierCoeff g n) (funext_iff.mpr fun _ => rfl) |>.trans
        (by unfold mFourierCoeff; exact integral_congr_ae (hΔ.mono fun x hx => by simp [hx]))]
    simp [mFourierCoeff_const]
  rw [mFourierCoeff_finset_sum _ fun μ => integrable_of_memLp_two (hd2 μ μ)] at hc
  simp only [hdd _ _ _, hd _ _] at hc
  simp_rw [← mul_assoc] at hc
  rw [← Finset.sum_mul, sum_sym_sq] at hc
  by_cases hn : n = 0
  · subst hn; exact h0
  · have hL : (lapSym n : ℂ) ≠ 0 := by
      have := one_le_lapSym hn
      exact_mod_cast (show lapSym n ≠ 0 by linarith)
    rcases mul_eq_zero.1 hc with h | h
    · exact absurd (neg_eq_zero.1 h) hL
    · exact h

/-! ### The abelian Coulomb gauge -/

/-- **Coulomb gauge for abelian connections** (Uhlenbeck's theorem for `G = U(1)`, or any torus
group, on `𝕋^d`, with no smallness hypothesis): every one-form `a` with `H¹` components is
`a = a' + dψ` with `a'` co-closed, `da' = da` and `‖∂_μ a'_ν‖_{L²} ≤ Σ_{μ'ν'} ‖(da)_{μ'ν'}‖_{L²}`.
(For `a` with values in `i ℝ`, `a' = e^{ψ}·a` is the gauge transform by `e^{ψ}`.) -/
theorem abelian_coulomb_gauge {a : d → UnitAddTorus d → ℂ} {da : d → d → UnitAddTorus d → ℂ}
    (ha : ∀ ν, MemLp (a ν) 2 volume) (hda : ∀ ν μ, MemLp (da ν μ) 2 volume)
    (hd : ∀ ν μ, IsTPartial μ (a ν) (da ν μ)) :
    ∃ (ψ : UnitAddTorus d → ℂ) (dψ : d → UnitAddTorus d → ℂ) (a' : d → UnitAddTorus d → ℂ)
      (da' : d → d → UnitAddTorus d → ℂ),
      MemLp ψ 2 volume ∧ (∀ μ, MemLp (dψ μ) 2 volume) ∧ (∀ μ, IsTPartial μ ψ (dψ μ)) ∧
      (∀ ν, a ν = fun x => a' ν x + dψ ν x) ∧
      (∀ ν, MemLp (a' ν) 2 volume) ∧ (∀ ν μ, MemLp (da' ν μ) 2 volume) ∧
      (∀ ν μ, IsTPartial μ (a' ν) (da' ν μ)) ∧
      (∀ᵐ x ∂volume, ∑ μ, da' μ μ x = 0) ∧
      (∀ ν μ, (fun x => da' ν μ x - da' μ ν x) =ᵐ[volume] fun x => da ν μ x - da μ ν x) ∧
      (∀ ν μ, eLpNorm (da' ν μ) 2 volume ≤
        ∑ μ', ∑ ν', eLpNorm (fun x => da ν' μ' x - da μ' ν' x) 2 volume) := by
  -- solve `Δψ = Σ_μ ∂_μ a_μ`
  have hf : MemLp (fun x => ∑ μ, da μ μ x) 2 volume := memLp_finsetSum _ fun μ _ => hda μ μ
  have hf0 : mFourierCoeff (fun x => ∑ μ, da μ μ x) 0 = 0 := by
    rw [mFourierCoeff_finset_sum _ fun μ => integrable_of_memLp_two (hda μ μ)]
    exact Finset.sum_eq_zero fun μ _ => by rw [hd μ μ 0, sym_zero, zero_mul]
  obtain ⟨ψ, dψ, d2ψ, hψ, hdψ, hd2ψ, -, hψd, hψdd, hΔ, -, -, -⟩ := laplace_solve hf hf0
  have hint : ∀ ν, Integrable (a ν) volume := fun ν => integrable_of_memLp_two (ha ν)
  -- the symmetry of the second derivatives
  have hsymm : ∀ ν μ, d2ψ ν μ =ᵐ[volume] d2ψ μ ν := fun ν μ =>
    ae_eq_of_mFourierCoeff_eq (hd2ψ ν μ) (hd2ψ μ ν) fun n => by
      rw [hψdd ν μ n, hψd ν n, hψdd μ ν n, hψd μ n]; ring
  refine ⟨ψ, dψ, fun ν x => a ν x - dψ ν x, fun ν μ x => da ν μ x - d2ψ ν μ x, hψ, hdψ, hψd,
    fun ν => funext fun x => by ring, fun ν => (ha ν).sub (hdψ ν),
    fun ν μ => (hda ν μ).sub (hd2ψ ν μ), fun ν μ => ?_, ?_, fun ν μ => ?_, ?_⟩
  · exact (hd ν μ).sub (hψdd ν μ) (hint ν) (integrable_of_memLp_two (hdψ ν))
      (integrable_of_memLp_two (hda ν μ)) (integrable_of_memLp_two (hd2ψ ν μ))
  · filter_upwards [hΔ] with x hx
    rw [Finset.sum_sub_distrib, hx, sub_self]
  · filter_upwards [hsymm ν μ] with x hx
    rw [hx]; ring
  · -- the Hodge estimate for the co-closed form `a'`
    intro ν μ
    have hcl : ∀ᵐ x ∂volume, ∑ μ, (da μ μ x - d2ψ μ μ x) = 0 := by
      filter_upwards [hΔ] with x hx
      rw [Finset.sum_sub_distrib, hx, sub_self]
    have hH := eLpNorm_partial_le_curl_of_coclosed (w := fun ν x => a ν x - dψ ν x)
      (g := fun ν μ x => da ν μ x - d2ψ ν μ x) (fun ν μ => (hda ν μ).sub (hd2ψ ν μ))
      (fun ν μ => (hd ν μ).sub (hψdd ν μ) (hint ν) (integrable_of_memLp_two (hdψ ν))
        (integrable_of_memLp_two (hda ν μ)) (integrable_of_memLp_two (hd2ψ ν μ))) hcl ν μ
    refine hH.trans (le_of_eq (Finset.sum_congr rfl fun μ' _ => Finset.sum_congr rfl
      fun ν' _ => eLpNorm_congr_ae ?_))
    filter_upwards [hsymm ν' μ'] with x hx
    simp only [hx]; ring

end RenewalGeometry.UhlenbeckTorus
