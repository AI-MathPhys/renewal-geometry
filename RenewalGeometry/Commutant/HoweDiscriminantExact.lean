/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Commutant.RectangularCauchyBinet
import RenewalGeometry.Analysis.PolynomialZeroSetNull

/-!
# Howe enhancement discriminant and generic rigidity (`thm:howe-discriminant`)

`thm:howe-discriminant` of the spacetime–gauge duality paper.  A parameter family
`θ ↦ c_j(θ) ∈ M_n(ℂ)` (`θ ∈ ℝ^p`) with polynomial entries of degree `≤ d`, a protected algebra
`ℳ ⊆ M_n(ℂ)` commuting with every `c_j(θ)`, and a complement `𝒦` of `ℳ` (the paper's
`𝒦 = ℳ^⊥`) with basis `E_1, …, E_r` are given.  The stacked commutator map
`D(θ) X = ([c_j(θ), X])_j` on `𝒦` is the matrix `stackedCommutator` (row `(j, a, b)`, column `k`,
entry `[c_j(θ), E_k]_{ab}`), `G(θ) = D(θ)ᴴ D(θ)` is the relative Howe Gram and
`Δ_ℳ(θ) = det G(θ)` the Howe discriminant (`howeDiscriminant`, `eq:howe-discriminant`).

* `howe_discriminant`: **`thm:howe-discriminant`, polynomial family** —
  (1) `Δ_ℳ` is a nonnegative real polynomial of degree `≤ 2dr`;
  (2) the Cauchy–Binet representation `Δ_ℳ(θ) = ∑_{|I| = r} |det D_I(θ)|²`
  (`eq:howe-minor-sos`, via `CauchyBinet.det_conjTranspose_mul_eq_sum_normSq_minors`);
  (3) the enhancement locus `{Δ_ℳ = 0} = {θ : C*(c(θ))' ⊋ ℳ}` (`eq:howe-enhancement-locus`),
  the commutant strictly containing `ℳ` being rendered as "some `X` commuting with all
  `c_j(θ)` lies outside `ℳ`";
  (4) if the commutant is exact at one parameter value, the enhancement locus is
  Lebesgue-null with empty interior, and on every open region `U` the exact set
  `{θ ∈ U : Δ_ℳ(θ) ≠ 0}` is open, dense in `U` and of full measure in `U`
  (via `volume_mvPolynomial_zeroSet_eq_zero`);
* `howe_discriminant_analytic`: **the real-analytic clause** — for a real-analytic family on an
  open connected region `U` containing one exact point, the enhancement locus has empty
  interior in `U` and the exact set is open and dense in `U` (identity theorem
  `AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero`).

The identification of `ker D(θ)` with the additional commutant is `thm:howe-certificate`
(`howe_certificate`, `relative_howe_certificate_exact` in this library); here it is re-derived
directly for the basis `E` of the complement `𝒦` (`stackedCommutator_mulVec_eq_zero_iff`).
-/

open Matrix MvPolynomial MeasureTheory
open scoped ComplexOrder

namespace RenewalGeometry
namespace HoweDiscriminant

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι] {p r : ℕ}

/-! ### The stacked commutator matrix and the discriminant -/

/-- The complexified parameter point. -/
def cplx (θ : Fin p → ℝ) : Fin p → ℂ := fun t => (θ t : ℂ)

/-- The stacked commutator matrix `D(θ)` in the basis `E` of `𝒦`: row `(j, a, b)`, column `k`,
entry `[c_j(θ), E_k]_{ab}`. -/
def stackedCommutator (c : (Fin p → ℝ) → ι → Matrix n n ℂ) (E : Fin r → Matrix n n ℂ)
    (θ : Fin p → ℝ) : Matrix (ι × n × n) (Fin r) ℂ :=
  Matrix.of fun x k => (c θ x.1 * E k - E k * c θ x.1) x.2.1 x.2.2

/-- The Howe discriminant `Δ_ℳ(θ) = det (D(θ)ᴴ D(θ))` (`eq:howe-discriminant`). -/
noncomputable def howeDiscriminant (c : (Fin p → ℝ) → ι → Matrix n n ℂ)
    (E : Fin r → Matrix n n ℂ) (θ : Fin p → ℝ) : ℂ :=
  ((stackedCommutator c E θ)ᴴ * stackedCommutator c E θ).det

theorem stackedCommutator_mulVec (c : (Fin p → ℝ) → ι → Matrix n n ℂ) (E : Fin r → Matrix n n ℂ)
    (θ : Fin p → ℝ) (v : Fin r → ℂ) (x : ι × n × n) :
    (stackedCommutator c E θ).mulVec v x =
      (c θ x.1 * (∑ k, v k • E k) - (∑ k, v k • E k) * c θ x.1) x.2.1 x.2.2 := by
  simp only [Matrix.mulVec, dotProduct, stackedCommutator, Matrix.of_apply, Matrix.mul_sum,
    Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.sub_apply, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- **The kernel of `D(θ)` is the additional commutant**: `D(θ) v = 0` exactly when
`X = ∑_k v_k E_k` commutes with every `c_j(θ)`. -/
theorem stackedCommutator_mulVec_eq_zero_iff (c : (Fin p → ℝ) → ι → Matrix n n ℂ)
    (E : Fin r → Matrix n n ℂ) (θ : Fin p → ℝ) (v : Fin r → ℂ) :
    (stackedCommutator c E θ).mulVec v = 0 ↔
      ∀ j, c θ j * (∑ k, v k • E k) = (∑ k, v k • E k) * c θ j := by
  constructor
  · intro h j
    ext a b
    have := congrFun h (j, a, b)
    rw [stackedCommutator_mulVec, Pi.zero_apply, Matrix.sub_apply] at this
    exact sub_eq_zero.mp this
  · intro h
    funext x
    rw [stackedCommutator_mulVec, Pi.zero_apply, h x.1, sub_self, Matrix.zero_apply]

/-- The Gram determinant vanishes exactly when the matrix has a kernel vector. -/
theorem det_conjTranspose_mul_eq_zero_iff {m : Type*} [Fintype m] (A : Matrix m (Fin r) ℂ) :
    (Aᴴ * A).det = 0 ↔ ∃ v : Fin r → ℂ, v ≠ 0 ∧ A.mulVec v = 0 := by
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  constructor
  · rintro ⟨v, hv, hAv⟩
    refine ⟨v, hv, ?_⟩
    have h : star (A.mulVec v) ⬝ᵥ A.mulVec v = 0 := by
      rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hAv,
        dotProduct_zero]
    exact dotProduct_star_self_eq_zero.mp h
  · rintro ⟨v, hv, hAv⟩
    exact ⟨v, hv, by rw [← Matrix.mulVec_mulVec, hAv, Matrix.mulVec_zero]⟩

/-- **`eq:howe-enhancement-locus`, pointwise.**  With `𝒦` a complement of the protected
algebra `ℳ` (which commutes with the family) spanned by the independent `E_k`, the discriminant
vanishes at `θ` exactly when the commutant of `c(θ)` strictly contains `ℳ`. -/
theorem howeDiscriminant_eq_zero_iff (c : (Fin p → ℝ) → ι → Matrix n n ℂ)
    (E : Fin r → Matrix n n ℂ) (ℳ 𝒦 : Submodule ℂ (Matrix n n ℂ)) (hcompl : IsCompl ℳ 𝒦)
    (hE : LinearIndependent ℂ E) (hspan : Submodule.span ℂ (Set.range E) = 𝒦)
    (hℳ : ∀ θ, ∀ M ∈ ℳ, ∀ j, c θ j * M = M * c θ j) (θ : Fin p → ℝ) :
    howeDiscriminant c E θ = 0 ↔
      ∃ X : Matrix n n ℂ, (∀ j, c θ j * X = X * c θ j) ∧ X ∉ ℳ := by
  rw [howeDiscriminant, det_conjTranspose_mul_eq_zero_iff]
  constructor
  · rintro ⟨v, hv, hDv⟩
    rw [stackedCommutator_mulVec_eq_zero_iff] at hDv
    refine ⟨∑ k, v k • E k, hDv, fun hmem => ?_⟩
    have hK : (∑ k, v k • E k) ∈ 𝒦 := by
      rw [← hspan]
      exact Submodule.sum_mem _ fun k _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self k))
    have hzero : (∑ k, v k • E k) = 0 := by
      have hm : (∑ k, v k • E k) ∈ ℳ ⊓ 𝒦 := ⟨hmem, hK⟩
      rw [hcompl.inf_eq_bot] at hm
      exact (Submodule.mem_bot ℂ).mp hm
    apply hv
    funext k
    exact Fintype.linearIndependent_iff.mp hE v hzero k
  · rintro ⟨X, hX, hXM⟩
    have hsup : X ∈ ℳ ⊔ 𝒦 := by
      rw [hcompl.sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨M, hM, Y, hY, hMY⟩ := Submodule.mem_sup.mp hsup
    rw [← hspan] at hY
    obtain ⟨v, hv⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hY
    have hYX : Y = X - M := by
      rw [← hMY]
      abel
    refine ⟨v, ?_, ?_⟩
    · rintro rfl
      simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero] at hv
      apply hXM
      rw [← hMY, ← hv, add_zero]
      exact hM
    · rw [stackedCommutator_mulVec_eq_zero_iff, hv, hYX]
      intro j
      rw [Matrix.mul_sub, Matrix.sub_mul, hX j, hℳ θ M hM j]

/-! ### Polynomial structure -/

section Polynomial

variable (P : ι → n → n → MvPolynomial (Fin p) ℂ) (E : Fin r → Matrix n n ℂ)

/-- The polynomial entries of the stacked commutator matrix. -/
noncomputable def stackedPoly : Matrix (ι × n × n) (Fin r) (MvPolynomial (Fin p) ℂ) :=
  Matrix.of fun x k => ∑ t, (P x.1 x.2.1 t * C (E k t x.2.2) - C (E k x.2.1 t) * P x.1 t x.2.2)

theorem stackedCommutator_eq_map (c : (Fin p → ℝ) → ι → Matrix n n ℂ)
    (hc : ∀ θ j a b, c θ j a b = eval (cplx θ) (P j a b)) (θ : Fin p → ℝ) :
    stackedCommutator c E θ = (stackedPoly P E).map (eval (cplx θ)) := by
  ext x k
  simp only [stackedCommutator, stackedPoly, Matrix.of_apply, Matrix.map_apply, map_sum, map_sub,
    map_mul, eval_C, Matrix.sub_apply, Matrix.mul_apply, hc, Finset.sum_sub_distrib]

theorem totalDegree_stackedPoly_le {d : ℕ} (hdeg : ∀ j a b, (P j a b).totalDegree ≤ d)
    (x : ι × n × n) (k : Fin r) : (stackedPoly P E x k).totalDegree ≤ d := by
  simp only [stackedPoly, Matrix.of_apply]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun t _ => ?_)
  refine (totalDegree_sub _ _).trans (max_le ?_ ?_)
  · refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, add_zero]
    exact hdeg _ _ _
  · refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, zero_add]
    exact hdeg _ _ _

/-- The polynomial relative Howe Gram `DᴴD` (coefficients conjugated in the left factor). -/
noncomputable def gramPoly : Matrix (Fin r) (Fin r) (MvPolynomial (Fin p) ℂ) :=
  Matrix.of fun i j =>
    ∑ x, MvPolynomial.map (starRingEnd ℂ) (stackedPoly P E x i) * stackedPoly P E x j

/-- Conjugation commutes with evaluation at real points. -/
theorem conj_eval_cplx (F : MvPolynomial (Fin p) ℂ) (θ : Fin p → ℝ) :
    (starRingEnd ℂ) (eval (cplx θ) F) = eval (cplx θ) (MvPolynomial.map (starRingEnd ℂ) F) := by
  rw [← MvPolynomial.eval₂_eq_eval_map]
  change (starRingEnd ℂ) (eval₂ (RingHom.id ℂ) (cplx θ) F) = _
  rw [MvPolynomial.eval₂_comp_left, RingHom.comp_id]
  have hcomp : (starRingEnd ℂ) ∘ cplx θ = cplx θ := by
    funext t
    simp [cplx]
  rw [hcomp]

theorem gram_eq_map (c : (Fin p → ℝ) → ι → Matrix n n ℂ)
    (hc : ∀ θ j a b, c θ j a b = eval (cplx θ) (P j a b)) (θ : Fin p → ℝ) :
    (stackedCommutator c E θ)ᴴ * stackedCommutator c E θ = (gramPoly P E).map (eval (cplx θ)) := by
  ext i j
  rw [stackedCommutator_eq_map P E c hc θ]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply, gramPoly,
    Matrix.of_apply, map_sum, map_mul, Complex.star_def, conj_eval_cplx]

theorem howeDiscriminant_eq_eval (c : (Fin p → ℝ) → ι → Matrix n n ℂ)
    (hc : ∀ θ j a b, c θ j a b = eval (cplx θ) (P j a b)) (θ : Fin p → ℝ) :
    howeDiscriminant c E θ = eval (cplx θ) (gramPoly P E).det := by
  rw [howeDiscriminant, gram_eq_map P E c hc θ, RingHom.map_det]
  rfl

theorem totalDegree_gramPoly_le {d : ℕ} (hdeg : ∀ j a b, (P j a b).totalDegree ≤ d)
    (i j : Fin r) : (gramPoly P E i j).totalDegree ≤ 2 * d := by
  simp only [gramPoly, Matrix.of_apply]
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun x _ => ?_)
  refine (totalDegree_mul _ _).trans ?_
  have h1 : (MvPolynomial.map (starRingEnd ℂ) (stackedPoly P E x i)).totalDegree ≤ d :=
    (totalDegree_le_of_support_subset (support_map_subset _ _)).trans
      (totalDegree_stackedPoly_le P E hdeg x i)
  have h2 := totalDegree_stackedPoly_le P E hdeg x j
  omega

theorem totalDegree_gramPoly_det_le {d : ℕ} (hdeg : ∀ j a b, (P j a b).totalDegree ≤ d) :
    (gramPoly P E).det.totalDegree ≤ 2 * d * r := by
  rw [Matrix.det_apply']
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun σ _ => ?_)
  have hsign : ((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Fin p) ℂ) =
      C ((Equiv.Perm.sign σ : ℤ) : ℂ) := by
    rw [map_intCast]
  rw [hsign]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  refine (Finset.sum_le_sum fun i _ => totalDegree_gramPoly_le P E hdeg (σ i) i).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  exact le_of_eq (by ring)

end Polynomial

/-! ### The real polynomial behind a complex polynomial with real values -/

/-- The real polynomial whose coefficients are the real parts of the coefficients of `F`. -/
noncomputable def rePoly (F : MvPolynomial (Fin p) ℂ) : MvPolynomial (Fin p) ℝ :=
  ∑ d ∈ F.support, monomial d (coeff d F).re

theorem eval_rePoly (F : MvPolynomial (Fin p) ℂ) (θ : Fin p → ℝ) :
    eval θ (rePoly F) = (eval (cplx θ) F).re := by
  rw [rePoly, map_sum, eval_eq (cplx θ) F, Complex.re_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [eval_monomial]
  have hprod : (∏ i ∈ d.support, cplx θ i ^ d i) = ((∏ i ∈ d.support, θ i ^ d i : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hprod, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rfl

theorem totalDegree_rePoly_le (F : MvPolynomial (Fin p) ℂ) :
    (rePoly F).totalDegree ≤ F.totalDegree := by
  refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun d hd => ?_)
  refine (totalDegree_monomial_le _ _).trans ?_
  exact Finset.le_sup (f := fun s : Fin p →₀ ℕ => s.sum fun _ e => e) hd

/-! ### The theorem -/

/-- **`thm:howe-discriminant`** (Howe enhancement discriminant and generic rigidity, polynomial
family).  Let `c_j(θ) ∈ M_n(ℂ)` have entries given by complex polynomials `P_{jab}` of total
degree `≤ d` in the real parameters `θ ∈ ℝ^p`, let the protected algebra `ℳ` commute with every
`c_j(θ)`, let `𝒦` be a complement of `ℳ` with basis `E_1, …, E_r` (the paper's `𝒦 = ℳ^⊥`), and
let `enum I` enumerate each `r`-element set of rows of the stacked commutator matrix.  Then:

1. `Δ_ℳ` is a nonnegative real polynomial of degree at most `2dr`;
2. `Δ_ℳ(θ) = ∑_{|I| = r} |det D_I(θ)|²` (`eq:howe-minor-sos`);
3. `{Δ_ℳ = 0} = {θ : C*(c(θ))' ⊋ ℳ}` (`eq:howe-enhancement-locus`);
4. if the commutant is exact at one parameter value (`Δ_ℳ(θ₀) ≠ 0`), the enhancement locus is
   Lebesgue-null with empty interior, and for every open region `U` the exact set
   `{θ ∈ U : Δ_ℳ(θ) ≠ 0}` is open, dense in `U` and of full measure in `U`. -/
theorem howe_discriminant {d : ℕ} (c : (Fin p → ℝ) → ι → Matrix n n ℂ)
    (P : ι → n → n → MvPolynomial (Fin p) ℂ)
    (hc : ∀ θ j a b, c θ j a b = eval (cplx θ) (P j a b))
    (hdeg : ∀ j a b, (P j a b).totalDegree ≤ d)
    (E : Fin r → Matrix n n ℂ) (ℳ 𝒦 : Submodule ℂ (Matrix n n ℂ)) (hcompl : IsCompl ℳ 𝒦)
    (hE : LinearIndependent ℂ E) (hspan : Submodule.span ℂ (Set.range E) = 𝒦)
    (hℳ : ∀ θ, ∀ M ∈ ℳ, ∀ j, c θ j * M = M * c θ j)
    (enum : Finset (ι × n × n) → Fin r → ι × n × n)
    (henum : ∀ I, I.card = r → Function.Injective (enum I) ∧ ∀ j, enum I j ∈ I) :
    (∃ Q : MvPolynomial (Fin p) ℝ, Q.totalDegree ≤ 2 * d * r ∧ (∀ θ, 0 ≤ eval θ Q) ∧
      ∀ θ, howeDiscriminant c E θ = (eval θ Q : ℂ)) ∧
    (∀ θ, howeDiscriminant c E θ = ∑ I ∈ Finset.univ.powersetCard r,
      ((‖((stackedCommutator c E θ).submatrix (enum I) id).det‖ ^ 2 : ℝ) : ℂ)) ∧
    ({θ | howeDiscriminant c E θ = 0} =
      {θ | ∃ X : Matrix n n ℂ, (∀ j, c θ j * X = X * c θ j) ∧ X ∉ ℳ}) ∧
    ((∃ θ₀, howeDiscriminant c E θ₀ ≠ 0) →
      volume {θ | howeDiscriminant c E θ = 0} = 0 ∧
      interior {θ | howeDiscriminant c E θ = 0} = ∅ ∧
      ∀ U : Set (Fin p → ℝ), IsOpen U →
        IsOpen {θ ∈ U | howeDiscriminant c E θ ≠ 0} ∧
        U ⊆ closure {θ ∈ U | howeDiscriminant c E θ ≠ 0} ∧
        volume {θ ∈ U | howeDiscriminant c E θ = 0} = 0) := by
  -- Cauchy–Binet
  have hCB : ∀ θ, howeDiscriminant c E θ = ∑ I ∈ Finset.univ.powersetCard r,
      ((‖((stackedCommutator c E θ).submatrix (enum I) id).det‖ ^ 2 : ℝ) : ℂ) := fun θ =>
    CauchyBinet.det_conjTranspose_mul_eq_sum_normSq_minors _ enum henum
  -- the real value of the discriminant
  set s : (Fin p → ℝ) → ℝ := fun θ => ∑ I ∈ Finset.univ.powersetCard r,
    ‖((stackedCommutator c E θ).submatrix (enum I) id).det‖ ^ 2 with hs
  have hreal : ∀ θ, howeDiscriminant c E θ = (s θ : ℂ) := by
    intro θ
    rw [hCB, hs]
    push_cast
    rfl
  have hnonneg : ∀ θ, 0 ≤ s θ := fun θ =>
    Finset.sum_nonneg fun I _ => sq_nonneg _
  -- the real polynomial
  set Q := rePoly (gramPoly P E).det with hQ
  have hQeval : ∀ θ, eval θ Q = s θ := by
    intro θ
    rw [hQ, eval_rePoly, ← howeDiscriminant_eq_eval P E c hc θ, hreal, Complex.ofReal_re]
  have hΔQ : ∀ θ, howeDiscriminant c E θ = (eval θ Q : ℂ) := by
    intro θ
    rw [hQeval, hreal]
  refine ⟨⟨Q, (totalDegree_rePoly_le _).trans (totalDegree_gramPoly_det_le P E hdeg),
    fun θ => by rw [hQeval]; exact hnonneg θ, hΔQ⟩, hCB, ?_, ?_⟩
  · ext θ
    exact howeDiscriminant_eq_zero_iff c E ℳ 𝒦 hcompl hE hspan hℳ θ
  · rintro ⟨θ₀, hθ₀⟩
    have hQ0 : Q ≠ 0 := by
      rintro hQ0
      apply hθ₀
      rw [hΔQ, hQ0, map_zero, Complex.ofReal_zero]
    have hset : {θ | howeDiscriminant c E θ = 0} = {θ : Fin p → ℝ | eval θ Q = 0} := by
      ext θ
      simp only [Set.mem_setOf_eq, hΔQ, Complex.ofReal_eq_zero]
    refine ⟨?_, ?_, fun U hU => ?_⟩
    · rw [hset]
      exact volume_mvPolynomial_zeroSet_eq_zero Q hQ0
    · rw [hset]
      exact interior_mvPolynomial_zeroSet_eq_empty Q hQ0
    · have hset' : {θ ∈ U | howeDiscriminant c E θ ≠ 0} = {θ ∈ U | eval θ Q ≠ 0} := by
        ext θ
        simp only [Set.mem_setOf_eq, hΔQ, ne_eq, Complex.ofReal_eq_zero]
      have hset'' : {θ ∈ U | howeDiscriminant c E θ = 0} = {θ ∈ U | eval θ Q = 0} := by
        ext θ
        simp only [Set.mem_setOf_eq, hΔQ, Complex.ofReal_eq_zero]
      rw [hset', hset'']
      exact mvPolynomial_nonzeroSet_open_dense_full_measure Q hQ0 U hU

/-! ### The real-analytic clause -/

/-- The determinant of a matrix with real-analytic entries is real-analytic. -/
theorem analyticOnNhd_det {m : Type*} [Fintype m] [DecidableEq m] {U : Set (Fin p → ℝ)}
    (M : (Fin p → ℝ) → Matrix m m ℂ) (hM : ∀ i j, AnalyticOnNhd ℝ (fun θ => M θ i j) U) :
    AnalyticOnNhd ℝ (fun θ => (M θ).det) U := by
  simp_rw [Matrix.det_apply']
  have h : AnalyticOnNhd ℝ (∑ σ : Equiv.Perm m, fun θ =>
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, M θ (σ i) i) U := by
    refine Finset.analyticOnNhd_sum _ fun σ _ => ?_
    have hprod : AnalyticOnNhd ℝ (∏ i : m, fun θ => M θ (σ i) i) U :=
      Finset.analyticOnNhd_prod _ fun i _ => hM _ _
    have hprod' : (∏ i : m, fun θ => M θ (σ i) i) = fun θ => ∏ i, M θ (σ i) i := by
      funext θ
      simp [Finset.prod_apply]
    rw [hprod'] at hprod
    exact analyticOnNhd_const.mul hprod
  have h' : (∑ σ : Equiv.Perm m, fun θ => ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, M θ (σ i) i) =
      fun θ => ∑ σ : Equiv.Perm m, ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, M θ (σ i) i := by
    funext θ
    simp [Finset.sum_apply]
  rw [h'] at h
  exact h

/-- The discriminant of a real-analytic family is real-analytic. -/
theorem analyticOnNhd_howeDiscriminant (c : (Fin p → ℝ) → ι → Matrix n n ℂ)
    (E : Fin r → Matrix n n ℂ) {U : Set (Fin p → ℝ)}
    (hc : ∀ j a b, AnalyticOnNhd ℝ (fun θ => c θ j a b) U) :
    AnalyticOnNhd ℝ (howeDiscriminant c E) U := by
  have hD : ∀ x k, AnalyticOnNhd ℝ (fun θ => stackedCommutator c E θ x k) U := by
    intro x k
    simp only [stackedCommutator, Matrix.of_apply, Matrix.sub_apply, Matrix.mul_apply]
    refine AnalyticOnNhd.sub ?_ ?_
    · have := Finset.analyticOnNhd_sum (𝕜 := ℝ) (s := U)
        (f := fun t θ => c θ x.1 x.2.1 t * E k t x.2.2) Finset.univ
        fun t _ => (hc _ _ _).mul analyticOnNhd_const
      have heq : (∑ t : n, fun θ => c θ x.1 x.2.1 t * E k t x.2.2) =
          fun θ => ∑ t, c θ x.1 x.2.1 t * E k t x.2.2 := by
        funext θ
        simp [Finset.sum_apply]
      rw [heq] at this
      exact this
    · have := Finset.analyticOnNhd_sum (𝕜 := ℝ) (s := U)
        (f := fun t θ => E k x.2.1 t * c θ x.1 t x.2.2) Finset.univ
        fun t _ => analyticOnNhd_const.mul (hc _ _ _)
      have heq : (∑ t : n, fun θ => E k x.2.1 t * c θ x.1 t x.2.2) =
          fun θ => ∑ t, E k x.2.1 t * c θ x.1 t x.2.2 := by
        funext θ
        simp [Finset.sum_apply]
      rw [heq] at this
      exact this
  have hG : ∀ i j, AnalyticOnNhd ℝ
      (fun θ => ((stackedCommutator c E θ)ᴴ * stackedCommutator c E θ) i j) U := by
    intro i j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def]
    have := Finset.analyticOnNhd_sum (𝕜 := ℝ) (s := U)
      (f := fun x θ => (starRingEnd ℂ) (stackedCommutator c E θ x i) *
        stackedCommutator c E θ x j) Finset.univ fun x _ => ?_
    · have heq : (∑ x : ι × n × n, fun θ => (starRingEnd ℂ) (stackedCommutator c E θ x i) *
          stackedCommutator c E θ x j) =
          fun θ => ∑ x, (starRingEnd ℂ) (stackedCommutator c E θ x i) *
            stackedCommutator c E θ x j := by
        funext θ
        simp [Finset.sum_apply]
      rw [heq] at this
      exact this
    · refine AnalyticOnNhd.mul ?_ (hD x j)
      have := (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp_analyticOnNhd (hD x i)
      have heq : ((Complex.conjCLE : ℂ →L[ℝ] ℂ) ∘ fun θ => stackedCommutator c E θ x i) =
          fun θ => (starRingEnd ℂ) (stackedCommutator c E θ x i) := by
        funext θ
        simp [Complex.conjCLE_apply]
      rw [heq] at this
      exact this
  exact analyticOnNhd_det _ hG

/-- **`thm:howe-discriminant`, real-analytic clause.**  For a real-analytic family on an open
connected region `U` containing one exact point `θ₀` (`Δ_ℳ(θ₀) ≠ 0`), the enhancement locus has
empty interior in `U`, and the exact set `{θ ∈ U : Δ_ℳ(θ) ≠ 0}` is open and dense in `U`. -/
theorem howe_discriminant_analytic (c : (Fin p → ℝ) → ι → Matrix n n ℂ)
    (E : Fin r → Matrix n n ℂ) (U : Set (Fin p → ℝ)) (hU : IsOpen U) (hconn : IsPreconnected U)
    (hc : ∀ j a b, AnalyticOnNhd ℝ (fun θ => c θ j a b) U)
    (θ₀ : Fin p → ℝ) (hθ₀ : θ₀ ∈ U) (h0 : howeDiscriminant c E θ₀ ≠ 0) :
    interior {θ | howeDiscriminant c E θ = 0} ∩ U = ∅ ∧
    IsOpen {θ ∈ U | howeDiscriminant c E θ ≠ 0} ∧
    U ⊆ closure {θ ∈ U | howeDiscriminant c E θ ≠ 0} := by
  have hΔ := analyticOnNhd_howeDiscriminant c E hc
  -- no interior point of the zero set lies in `U`
  have hint : interior {θ | howeDiscriminant c E θ = 0} ∩ U = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro θ₁ ⟨h₁, hU₁⟩
    rw [mem_interior_iff_mem_nhds] at h₁
    have hev : howeDiscriminant c E =ᶠ[nhds θ₁] 0 :=
      Filter.eventuallyEq_of_mem h₁ fun θ hθ => hθ
    have := hΔ.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn hU₁ hev hθ₀
    exact h0 this
  refine ⟨hint, ?_, ?_⟩
  · have : {θ ∈ U | howeDiscriminant c E θ ≠ 0} =
        U ∩ (howeDiscriminant c E) ⁻¹' {0}ᶜ := by
      ext θ
      simp [Set.mem_setOf_eq]
    rw [this]
    exact hΔ.continuousOn.isOpen_inter_preimage hU isOpen_compl_singleton
  · intro θ hθ
    rw [mem_closure_iff_nhds]
    intro t ht
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    have hsub : t ∩ U ⊆ {θ | howeDiscriminant c E θ = 0} := by
      intro θ' ⟨ht', hU'⟩
      by_contra hne
      have : θ' ∈ t ∩ {θ ∈ U | howeDiscriminant c E θ ≠ 0} := ⟨ht', hU', hne⟩
      rw [hempty] at this
      exact this
    have hmem : θ ∈ interior {θ | howeDiscriminant c E θ = 0} ∩ U := by
      refine ⟨?_, hθ⟩
      rw [mem_interior_iff_mem_nhds]
      exact Filter.mem_of_superset (Filter.inter_mem ht (hU.mem_nhds hθ)) hsub
    rw [hint] at hmem
    exact hmem

end HoweDiscriminant
end RenewalGeometry
