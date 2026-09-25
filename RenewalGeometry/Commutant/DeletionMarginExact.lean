/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Commutant.IncidencePolymatroidExact

/-!
# Exact simultaneous-deletion margin

`prop:deletion-margin` of the spacetime–gauge duality paper.

## Generic form

Let `V` be a finite-dimensional complex inner product space and `G_e` (`e ∈ E`, `E`
finite) positive operators on `V` with `G = G_E = ∑_e G_e` positive definite (a positive
operator is positive definite iff it is injective).  With `G^{1/2} = CFC.sqrt G`
(`sqrtGram`), `G^{-1/2}` its inverse (`invSqrtGram`, as `Ring.inverse`),
`B_e = G^{-1/2} G_e G^{-1/2}` (`bmat`) and `B_R = ∑_{e ∈ R} B_e` (`bmatR`):

* `sum_bmat`: `∑_e B_e = I`;
* `gram_compl_eq` (`eq:deletion-factor`): `G_{E ∖ R} = G^{1/2} (I − B_R) G^{1/2}`;
* `bmatR_nonneg`, `bmatR_le_one`: `0 ⪯ B_R ⪯ I`;
* `injective_gram_compl_iff` (the operator half of `eq:deletion-margin`):
  `Ker G_{E ∖ R} = 0 ⟺ ‖B_R‖_op < 1`, where `‖·‖_op` is the operator norm of
  `V →L[ℂ] V` (the `C*`-norm); the proof is the manuscript's: `I − B_R` is invertible
  iff `1` is not in the spectrum of the positive contraction `B_R`, iff `‖B_R‖ < 1`;
* `re_inner_gram_compl_ge`, `lambda_min_bound`: if `β_R = ‖B_R‖ < 1` then
  `⟨x, G_{E∖R} x⟩ ≥ (1 − β_R) ⟨x, G x⟩` for all `x` (this is `G_{E∖R} ⪰ (1 − β_R) G` in
  the Loewner order), and every spectral lower bound `λ ≤ λ_min(G)` (i.e.
  `λ‖x‖² ≤ ⟨x, G x⟩`) yields `(1 − β_R) λ ≤ λ_min(G_{E∖R})`.

## The commutant form

For the incidence bank of `thm:incidence-polymatroid` (`IncidencePolymatroidExact`:
base algebra commutant `M₀`, constraint maps `D_e`, residual space `V`, restricted
maps `D_e|_V`), take `G_e = (D_e|_V)^* (D_e|_V)` (`residualGram`).  Then `G_E` is
automatically positive definite on `V` (`gram_residualGram_univ_injective`), and
`deletion_margin_commutant` is the boxed statement `eq:deletion-margin`:

`𝓜(E ∖ R) = 𝓜(E) ⟺ ‖B_R‖_op < 1`.

`deletion_margin` assembles the proposition.
-/

open Finset

namespace RenewalGeometry
namespace DeletionMargin

/-- Finite-dimensional inner product spaces are complete; a local instance so that
`V →L[ℂ] V` carries its `C*`-algebra structure. -/
theorem completeSpace_of_finiteDimensional (V : Type*) [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] : CompleteSpace V :=
  FiniteDimensional.complete ℂ V

attribute [local instance] completeSpace_of_finiteDimensional

section Generic

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `G_S = ∑_{e ∈ S} G_e`. -/
def gram (Ge : ι → V →L[ℂ] V) (S : Finset ι) : V →L[ℂ] V := ∑ e ∈ S, Ge e

/-- `G^{1/2}`, the positive square root of `G = G_E`. -/
noncomputable def sqrtGram (Ge : ι → V →L[ℂ] V) : V →L[ℂ] V :=
  CFC.sqrt (gram Ge Finset.univ)

/-- `G^{-1/2}`, the inverse of `G^{1/2}` (`Ring.inverse`; it is a genuine inverse once
`G` is positive definite). -/
noncomputable def invSqrtGram (Ge : ι → V →L[ℂ] V) : V →L[ℂ] V :=
  Ring.inverse (sqrtGram Ge)

/-- `B_e = G^{-1/2} G_e G^{-1/2}`. -/
noncomputable def bmat (Ge : ι → V →L[ℂ] V) (e : ι) : V →L[ℂ] V :=
  invSqrtGram Ge * Ge e * invSqrtGram Ge

/-- `B_R = ∑_{e ∈ R} B_e`. -/
noncomputable def bmatR (Ge : ι → V →L[ℂ] V) (R : Finset ι) : V →L[ℂ] V :=
  ∑ e ∈ R, bmat Ge e

variable (Ge : ι → V →L[ℂ] V)

theorem gram_nonneg (hpos : ∀ e, 0 ≤ Ge e) (S : Finset ι) : 0 ≤ gram Ge S :=
  Finset.sum_nonneg fun e _ => hpos e

theorem sqrtGram_nonneg : 0 ≤ sqrtGram Ge := CFC.sqrt_nonneg _

theorem sqrtGram_isSelfAdjoint : IsSelfAdjoint (sqrtGram Ge) :=
  IsSelfAdjoint.of_nonneg (sqrtGram_nonneg Ge)

theorem sqrtGram_mul_self (hpos : ∀ e, 0 ≤ Ge e) :
    sqrtGram Ge * sqrtGram Ge = gram Ge Finset.univ :=
  CFC.sqrt_mul_sqrt_self _ (gram_nonneg Ge hpos _)

theorem sqrtGram_injective (hpos : ∀ e, 0 ≤ Ge e)
    (hinj : Function.Injective (gram Ge Finset.univ)) :
    Function.Injective (sqrtGram Ge) := by
  intro x y hxy
  apply hinj
  rw [← sqrtGram_mul_self Ge hpos]
  simp only [ContinuousLinearMap.mul_apply, hxy]

theorem sqrtGram_bijective (hpos : ∀ e, 0 ≤ Ge e)
    (hinj : Function.Injective (gram Ge Finset.univ)) :
    Function.Bijective (sqrtGram Ge) :=
  ⟨sqrtGram_injective Ge hpos hinj,
    LinearMap.injective_iff_surjective.mp (sqrtGram_injective Ge hpos hinj)⟩

theorem sqrtGram_isUnit (hpos : ∀ e, 0 ≤ Ge e)
    (hinj : Function.Injective (gram Ge Finset.univ)) : IsUnit (sqrtGram Ge) :=
  ContinuousLinearMap.isUnit_iff_bijective.mpr (sqrtGram_bijective Ge hpos hinj)

theorem invSqrtGram_mul (hpos : ∀ e, 0 ≤ Ge e)
    (hinj : Function.Injective (gram Ge Finset.univ)) :
    invSqrtGram Ge * sqrtGram Ge = 1 :=
  Ring.inverse_mul_cancel _ (sqrtGram_isUnit Ge hpos hinj)

theorem mul_invSqrtGram (hpos : ∀ e, 0 ≤ Ge e)
    (hinj : Function.Injective (gram Ge Finset.univ)) :
    sqrtGram Ge * invSqrtGram Ge = 1 :=
  Ring.mul_inverse_cancel _ (sqrtGram_isUnit Ge hpos hinj)

theorem invSqrtGram_isSelfAdjoint : IsSelfAdjoint (invSqrtGram Ge) := by
  show star (Ring.inverse (sqrtGram Ge)) = Ring.inverse (sqrtGram Ge)
  rw [← Ring.inverse_star, (sqrtGram_isSelfAdjoint Ge).star_eq]

/-- `∑_e B_e = I`. -/
theorem sum_bmat (hpos : ∀ e, 0 ≤ Ge e) (hinj : Function.Injective (gram Ge Finset.univ)) :
    ∑ e, bmat Ge e = 1 := by
  unfold bmat
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  change invSqrtGram Ge * gram Ge Finset.univ * invSqrtGram Ge = 1
  rw [← sqrtGram_mul_self Ge hpos, ← mul_assoc, invSqrtGram_mul Ge hpos hinj, one_mul,
    mul_invSqrtGram Ge hpos hinj]

/-- `G^{1/2} B_R G^{1/2} = G_R`. -/
theorem sqrtGram_mul_bmatR_mul (hpos : ∀ e, 0 ≤ Ge e)
    (hinj : Function.Injective (gram Ge Finset.univ)) (R : Finset ι) :
    sqrtGram Ge * bmatR Ge R * sqrtGram Ge = gram Ge R := by
  unfold bmatR bmat gram
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [← mul_assoc, ← mul_assoc, mul_invSqrtGram Ge hpos hinj, one_mul, mul_assoc,
    invSqrtGram_mul Ge hpos hinj, mul_one]

/-- **`eq:deletion-factor`**: `G_{E ∖ R} = G^{1/2} (I − B_R) G^{1/2}`. -/
theorem gram_compl_eq (hpos : ∀ e, 0 ≤ Ge e)
    (hinj : Function.Injective (gram Ge Finset.univ)) (R : Finset ι) :
    gram Ge (Finset.univ \ R) = sqrtGram Ge * (1 - bmatR Ge R) * sqrtGram Ge := by
  rw [mul_sub, sub_mul, mul_one, sqrtGram_mul_self Ge hpos, sqrtGram_mul_bmatR_mul Ge hpos hinj]
  unfold gram
  rw [eq_sub_iff_add_eq, Finset.sum_sdiff (Finset.subset_univ R)]

theorem bmat_nonneg (hpos : ∀ e, 0 ≤ Ge e) (e : ι) : 0 ≤ bmat Ge e :=
  (invSqrtGram_isSelfAdjoint Ge).conjugate_nonneg (hpos e)

/-- `0 ⪯ B_R`. -/
theorem bmatR_nonneg (hpos : ∀ e, 0 ≤ Ge e) (R : Finset ι) : 0 ≤ bmatR Ge R :=
  Finset.sum_nonneg fun e _ => bmat_nonneg Ge hpos e

/-- `B_R ⪯ I`. -/
theorem bmatR_le_one (hpos : ∀ e, 0 ≤ Ge e)
    (hinj : Function.Injective (gram Ge Finset.univ)) (R : Finset ι) :
    bmatR Ge R ≤ 1 := by
  rw [← sum_bmat Ge hpos hinj, ← Finset.sum_sdiff (Finset.subset_univ R)]
  exact le_add_of_nonneg_left (Finset.sum_nonneg fun e _ => bmat_nonneg Ge hpos e)

/-- `‖B_R‖ ≤ 1`. -/
theorem norm_bmatR_le_one (hpos : ∀ e, 0 ≤ Ge e)
    (hinj : Function.Injective (gram Ge Finset.univ)) (R : Finset ι) :
    ‖bmatR Ge R‖ ≤ 1 :=
  (CStarAlgebra.norm_le_one_iff_of_nonneg _ (bmatR_nonneg Ge hpos R)).mpr
    (bmatR_le_one Ge hpos hinj R)

/-- Congruence by a bijective operator preserves injectivity. -/
theorem injective_conj_iff {S T : V →L[ℂ] V} (hS : Function.Bijective S) :
    Function.Injective (S * T * S) ↔ Function.Injective T := by
  constructor
  · intro h y y' hyy'
    obtain ⟨x, rfl⟩ := hS.2 y
    obtain ⟨x', rfl⟩ := hS.2 y'
    have : (S * T * S) x = (S * T * S) x' := by
      simp only [ContinuousLinearMap.mul_apply]
      rw [hyy']
    exact congrArg S (h this)
  · intro h x x' hxx'
    simp only [ContinuousLinearMap.mul_apply] at hxx'
    exact hS.1 (h (hS.1 hxx'))

/-- **The operator half of `eq:deletion-margin`**: `Ker G_{E∖R} = 0 ⟺ ‖B_R‖_op < 1`. -/
theorem injective_gram_compl_iff (hpos : ∀ e, 0 ≤ Ge e)
    (hinj : Function.Injective (gram Ge Finset.univ)) (R : Finset ι) :
    Function.Injective (gram Ge (Finset.univ \ R)) ↔ ‖bmatR Ge R‖ < 1 := by
  rw [gram_compl_eq Ge hpos hinj, injective_conj_iff (sqrtGram_bijective Ge hpos hinj)]
  constructor
  · intro h
    have hunit : IsUnit (1 - bmatR Ge R) :=
      ContinuousLinearMap.isUnit_iff_bijective.mpr
        ⟨h, LinearMap.injective_iff_surjective.mp h⟩
    rcases subsingleton_or_nontrivial (V →L[ℂ] V) with hsub | hnt
    · rw [Subsingleton.elim (bmatR Ge R) 0, norm_zero]
      exact one_pos
    · refine lt_of_le_of_ne (norm_bmatR_le_one Ge hpos hinj R) fun heq => ?_
      have hmem := CStarAlgebra.norm_mem_spectrum_of_nonneg (bmatR_nonneg Ge hpos R)
      rw [heq, spectrum.mem_iff, map_one] at hmem
      exact hmem hunit
  · intro h
    have hunit : IsUnit (1 - bmatR Ge R) := (Units.oneSub _ h).isUnit
    exact (ContinuousLinearMap.isUnit_iff_bijective.mp hunit).1

/-! ### Quadratic-form margins -/

/-- `Re ⟨T y, y⟩ ≤ ‖T‖ ‖y‖²`. -/
theorem re_inner_le (T : V →L[ℂ] V) (y : V) :
    RCLike.re (inner ℂ (T y) y) ≤ ‖T‖ * ‖y‖ ^ 2 :=
  calc RCLike.re (inner ℂ (T y) y) ≤ ‖inner ℂ (T y) y‖ := RCLike.re_le_norm _
    _ ≤ ‖T y‖ * ‖y‖ := norm_inner_le_norm _ _
    _ ≤ ‖T‖ * ‖y‖ * ‖y‖ := by gcongr; exact T.le_opNorm y
    _ = ‖T‖ * ‖y‖ ^ 2 := by ring

/-- `⟨(S T S) x, x⟩ = ⟨T (S x), S x⟩` for self-adjoint `S`. -/
theorem inner_conj {S : V →L[ℂ] V} (hS : IsSelfAdjoint S) (T : V →L[ℂ] V) (x : V) :
    inner ℂ ((S * T * S) x) x = inner ℂ (T (S x)) (S x) := by
  rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply]
  exact hS.isSymmetric (T (S x)) x

/-- `⟨G x, x⟩ = ⟨G^{1/2} x, G^{1/2} x⟩`. -/
theorem inner_gram_univ (hpos : ∀ e, 0 ≤ Ge e) (x : V) :
    inner ℂ (gram Ge Finset.univ x) x = inner ℂ (sqrtGram Ge x) (sqrtGram Ge x) := by
  rw [← sqrtGram_mul_self Ge hpos, ContinuousLinearMap.mul_apply]
  exact (sqrtGram_isSelfAdjoint Ge).isSymmetric (sqrtGram Ge x) x

/-- **`G_{E∖R} ⪰ (1 − β_R) G`** in quadratic-form terms: for every `x`,
`(1 − ‖B_R‖) Re ⟨G x, x⟩ ≤ Re ⟨G_{E∖R} x, x⟩`. -/
theorem re_inner_gram_compl_ge (hpos : ∀ e, 0 ≤ Ge e)
    (hinj : Function.Injective (gram Ge Finset.univ)) (R : Finset ι) (x : V) :
    (1 - ‖bmatR Ge R‖) * RCLike.re (inner ℂ (gram Ge Finset.univ x) x) ≤
      RCLike.re (inner ℂ (gram Ge (Finset.univ \ R) x) x) := by
  rw [gram_compl_eq Ge hpos hinj, inner_conj (sqrtGram_isSelfAdjoint Ge),
    inner_gram_univ Ge hpos, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
    inner_sub_left, map_sub, inner_self_eq_norm_sq]
  have := re_inner_le (bmatR Ge R) (sqrtGram Ge x)
  nlinarith [this]

/-- **`λ_min(G_{E∖R}) ≥ (1 − β_R) λ_min(G)`**: every spectral lower bound `λ` of `G`
(`λ‖x‖² ≤ Re ⟨G x, x⟩`) gives the spectral lower bound `(1 − β_R) λ` of `G_{E∖R}`, when
`β_R = ‖B_R‖ < 1`. -/
theorem lambda_min_bound (hpos : ∀ e, 0 ≤ Ge e)
    (hinj : Function.Injective (gram Ge Finset.univ)) (R : Finset ι)
    (hβ : ‖bmatR Ge R‖ < 1) (lam : ℝ)
    (hlam : ∀ x : V, lam * ‖x‖ ^ 2 ≤ RCLike.re (inner ℂ (gram Ge Finset.univ x) x)) (x : V) :
    (1 - ‖bmatR Ge R‖) * lam * ‖x‖ ^ 2 ≤
      RCLike.re (inner ℂ (gram Ge (Finset.univ \ R) x) x) := by
  have h1 := re_inner_gram_compl_ge Ge hpos hinj R x
  have h2 := hlam x
  have h3 : 0 ≤ 1 - ‖bmatR Ge R‖ := by linarith
  calc (1 - ‖bmatR Ge R‖) * lam * ‖x‖ ^ 2
      = (1 - ‖bmatR Ge R‖) * (lam * ‖x‖ ^ 2) := by ring
    _ ≤ (1 - ‖bmatR Ge R‖) * RCLike.re (inner ℂ (gram Ge Finset.univ x) x) := by gcongr
    _ ≤ _ := h1

end Generic

/-! ### The commutant form on the residual space of an incidence bank -/

section Commutant

open IncidencePolymatroid

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
variable {W : ι → Type*} [∀ e, NormedAddCommGroup (W e)] [∀ e, InnerProductSpace ℂ (W e)]
  [∀ e, FiniteDimensional ℂ (W e)]

/-- `G_e = (D_e|_V)^* (D_e|_V)` on the residual space `V`, as a continuous operator. -/
noncomputable def residualGram (M₀ : Submodule ℂ H) (D : ∀ e, H →ₗ[ℂ] W e) (e : ι) :
    residualSpace M₀ D →L[ℂ] residualSpace M₀ D :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.adjoint (residualMap M₀ D e)) ∘ₗ residualMap M₀ D e)

variable (M₀ : Submodule ℂ H) (D : ∀ e, H →ₗ[ℂ] W e)

theorem residualGram_nonneg (e : ι) : 0 ≤ residualGram M₀ D e := by
  rw [ContinuousLinearMap.nonneg_iff_isPositive]
  exact (LinearMap.isPositive_toContinuousLinearMap_iff _).mpr
    (LinearMap.isPositive_adjoint_comp_self _)

/-- `G_S` is the incidence Gram operator of `thm:incidence-polymatroid`. -/
theorem gram_residualGram (S : Finset ι) :
    gram (residualGram M₀ D) S =
      LinearMap.toContinuousLinearMap (incidenceGram (residualMap M₀ D) S) := by
  unfold gram residualGram incidenceGram
  rw [map_sum]

theorem injective_gram_residualGram_iff (S : Finset ι) :
    Function.Injective (gram (residualGram M₀ D) S) ↔
      LinearMap.ker (incidenceGram (residualMap M₀ D) S) = ⊥ := by
  rw [gram_residualGram, LinearMap.ker_eq_bot]
  rfl

/-- `G = G_E` is positive definite on the residual space (its kernel there is
`𝓜(E) ∩ V = 0`). -/
theorem gram_residualGram_univ_injective :
    Function.Injective (gram (residualGram M₀ D) Finset.univ) := by
  rw [injective_gram_residualGram_iff, ker_incidenceGram, constraintKer_eq_bot_iff]
  exact (enlargedCommutant_eq_full_iff M₀ D Finset.univ).mp rfl

/-- `𝓜(E ∖ R) = 𝓜(E)` iff `G_{E∖R}` is injective on `V` (`thm:incidence-polymatroid`). -/
theorem enlargedCommutant_eq_full_iff_injective (R : Finset ι) :
    enlargedCommutant M₀ D (Finset.univ \ R) = fullCommutant M₀ D ↔
      Function.Injective (gram (residualGram M₀ D) (Finset.univ \ R)) := by
  rw [enlargedCommutant_eq_full_iff, injective_gram_residualGram_iff, ker_incidenceGram,
    constraintKer_eq_bot_iff]

/-- **`eq:deletion-margin`** (boxed): `𝓜(E ∖ R) = 𝓜(E) ⟺ ‖B_R‖_op < 1`. -/
theorem deletion_margin_commutant (R : Finset ι) :
    enlargedCommutant M₀ D (Finset.univ \ R) = fullCommutant M₀ D ↔
      ‖bmatR (residualGram M₀ D) R‖ < 1 := by
  rw [enlargedCommutant_eq_full_iff_injective]
  exact injective_gram_compl_iff _ (residualGram_nonneg M₀ D)
    (gram_residualGram_univ_injective M₀ D) R

/-- **`prop:deletion-margin`** (exact simultaneous-deletion margin).  On the residual
space `V` of the incidence bank, with `G = G_E ≻ 0`, `B_e = G^{-1/2} G_e G^{-1/2}`,
`∑_e B_e = I` and `B_R = ∑_{e∈R} B_e`: for every `R ⊆ E`,
`G_{E∖R} = G^{1/2}(I − B_R)G^{1/2}` (`eq:deletion-factor`), `0 ⪯ B_R ⪯ I`,
`𝓜(E∖R) = 𝓜(E) ⟺ ‖B_R‖_op < 1` (`eq:deletion-margin`), and if `β_R = ‖B_R‖_op < 1`
then `G_{E∖R} ⪰ (1 − β_R) G` and `λ_min(G_{E∖R}) ≥ (1 − β_R) λ_min(G)` (both in
quadratic-form terms). -/
theorem deletion_margin (R : Finset ι) :
    ∑ e, bmat (residualGram M₀ D) e = 1 ∧
    gram (residualGram M₀ D) (Finset.univ \ R) =
      sqrtGram (residualGram M₀ D) * (1 - bmatR (residualGram M₀ D) R) *
        sqrtGram (residualGram M₀ D) ∧
    (0 ≤ bmatR (residualGram M₀ D) R ∧ bmatR (residualGram M₀ D) R ≤ 1) ∧
    (enlargedCommutant M₀ D (Finset.univ \ R) = fullCommutant M₀ D ↔
      ‖bmatR (residualGram M₀ D) R‖ < 1) ∧
    (‖bmatR (residualGram M₀ D) R‖ < 1 →
      (∀ x, (1 - ‖bmatR (residualGram M₀ D) R‖) *
          RCLike.re (inner ℂ (gram (residualGram M₀ D) Finset.univ x) x) ≤
        RCLike.re (inner ℂ (gram (residualGram M₀ D) (Finset.univ \ R) x) x)) ∧
      (∀ lam : ℝ, (∀ x, lam * ‖x‖ ^ 2 ≤
          RCLike.re (inner ℂ (gram (residualGram M₀ D) Finset.univ x) x)) →
        ∀ x, (1 - ‖bmatR (residualGram M₀ D) R‖) * lam * ‖x‖ ^ 2 ≤
          RCLike.re (inner ℂ (gram (residualGram M₀ D) (Finset.univ \ R) x) x))) := by
  have hpos := residualGram_nonneg M₀ D
  have hinj := gram_residualGram_univ_injective M₀ D
  refine ⟨sum_bmat _ hpos hinj, gram_compl_eq _ hpos hinj R,
    ⟨bmatR_nonneg _ hpos R, bmatR_le_one _ hpos hinj R⟩, deletion_margin_commutant M₀ D R,
    fun hβ => ⟨re_inner_gram_compl_ge _ hpos hinj R,
      fun lam hlam => lambda_min_bound _ hpos hinj R hβ lam hlam⟩⟩

end Commutant

end DeletionMargin
end RenewalGeometry
