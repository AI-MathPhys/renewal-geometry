/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GNSObservableLimit
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Bounded observable limits from a dense GNS core

This file proves the functional-analytic existence step in
`thm:GNS-observable-limit`: a uniformly bounded sequence of operators that
is pointwise Cauchy on a dense linear core has a unique bounded limit on the
whole Hilbert space.  It also supplies the exact centered-vacuum lower-limit
argument used to prove that the limit is non-scalar.
-/

open Filter
open scoped Topology InnerProductSpace

namespace NCG
namespace DenseGNSObservableLimit

noncomputable section

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The chosen complete-space limit at one vector of the dense core. -/
def pointLimit (D : Submodule ℂ E) (O : ℕ → E →L[ℂ] E)
    (hCauchy : ∀ x : D, CauchySeq (fun n => O n (x : E)))
    (x : D) : E :=
  Classical.choose (cauchySeq_tendsto_of_complete (hCauchy x))

theorem tendsto_pointLimit (D : Submodule ℂ E) (O : ℕ → E →L[ℂ] E)
    (hCauchy : ∀ x : D, CauchySeq (fun n => O n (x : E)))
    (x : D) :
    Tendsto (fun n => O n (x : E)) atTop
      (𝓝 (pointLimit D O hCauchy x)) :=
  Classical.choose_spec (cauchySeq_tendsto_of_complete (hCauchy x))

/-- Pointwise limits of linear operators are linear on the common core. -/
def pointLimitLinear (D : Submodule ℂ E) (O : ℕ → E →L[ℂ] E)
    (hCauchy : ∀ x : D, CauchySeq (fun n => O n (x : E))) :
    D →ₗ[ℂ] E where
  toFun := pointLimit D O hCauchy
  map_add' x y := by
    apply tendsto_nhds_unique (tendsto_pointLimit D O hCauchy (x + y))
    simpa using
      (tendsto_pointLimit D O hCauchy x).add
        (tendsto_pointLimit D O hCauchy y)
  map_smul' c x := by
    apply tendsto_nhds_unique (tendsto_pointLimit D O hCauchy (c • x))
    simpa using (tendsto_pointLimit D O hCauchy x).const_smul c

theorem pointLimit_norm_le
    (D : Submodule ℂ E) (O : ℕ → E →L[ℂ] E)
    (hCauchy : ∀ x : D, CauchySeq (fun n => O n (x : E)))
    (C : ℝ) (hO : ∀ n, ‖O n‖ ≤ C) (x : D) :
    ‖pointLimitLinear D O hCauchy x‖ ≤ C * ‖(x : E)‖ := by
  have hclosed : IsClosed {y : E | ‖y‖ ≤ C * ‖(x : E)‖} :=
    isClosed_le continuous_norm continuous_const
  refine hclosed.mem_of_tendsto
    (tendsto_pointLimit D O hCauchy x) ?_
  filter_upwards [] with n
  calc
    ‖O n (x : E)‖ ≤ ‖O n‖ * ‖(x : E)‖ := (O n).le_opNorm _
    _ ≤ C * ‖(x : E)‖ :=
      mul_le_mul_of_nonneg_right (hO n) (norm_nonneg _)

/-- The bounded extension of the pointwise limit from the dense core. -/
def limitOperator (D : Submodule ℂ E) (O : ℕ → E →L[ℂ] E)
    (hCauchy : ∀ x : D, CauchySeq (fun n => O n (x : E))) :
    E →L[ℂ] E :=
  (pointLimitLinear D O hCauchy).extendOfNorm D.subtypeL

/-- **Bounded observable convergence on a dense GNS direct-limit core.**
The limit operator exists, is unique, has norm at most the common bound, and
is the pointwise strong limit on the core. -/
theorem exists_unique_bounded_observable_limit
    (D : Submodule ℂ E) (hDense : Dense (D : Set E))
    (O : ℕ → E →L[ℂ] E) (C : ℝ) (hC : 0 ≤ C)
    (hO : ∀ n, ‖O n‖ ≤ C)
    (hCauchy : ∀ x : D, CauchySeq (fun n => O n (x : E))) :
    ∃! T : E →L[ℂ] E,
      ‖T‖ ≤ C ∧
      ∀ x : D, Tendsto (fun n => O n (x : E)) atTop (𝓝 (T x)) := by
  have hDenseRange : DenseRange D.subtypeL := by
    simpa [DenseRange] using hDense
  let T := limitOperator D O hCauchy
  have hBound : ∀ x : D,
      ‖pointLimitLinear D O hCauchy x‖ ≤ C * ‖D.subtypeL x‖ := by
    intro x
    exact pointLimit_norm_le D O hCauchy C hO x
  refine ⟨T, ?_, ?_⟩
  · constructor
    · exact LinearMap.opNorm_extendOfNorm_le hDenseRange hC hBound
    · intro x
      have hEq :
          T (x : E) = pointLimitLinear D O hCauchy x := by
        exact LinearMap.extendOfNorm_eq hDenseRange ⟨C, hBound⟩ x
      rw [hEq]
      exact tendsto_pointLimit D O hCauchy x
  · intro S hS
    apply limit_observable_unique S T (D : Set E) hDense
    intro x hx
    let dx : D := ⟨x, hx⟩
    exact tendsto_nhds_unique
      (hS.2 dx)
      ((show Tendsto (fun n => O n (dx : E)) atTop (𝓝 (T dx)) from
        (by
          have hEq :
              T (dx : E) = pointLimitLinear D O hCauchy dx := by
            exact LinearMap.extendOfNorm_eq hDenseRange ⟨C, hBound⟩ dx
          rw [hEq]
          exact tendsto_pointLimit D O hCauchy dx)))

/-- A convenient formulation of `liminf u_n ≥ c` for real sequences. -/
def LowerLimitAtLeast (u : ℕ → ℝ) (c : ℝ) : Prop :=
  ∀ epsilon, epsilon < c → ∀ᶠ n in atTop, epsilon ≤ u n

theorem positive_norm_of_lowerLimitAtLeast
    {v : ℕ → E} {limit : E} {c : ℝ}
    (hc : 0 < c) (hv : Tendsto v atTop (𝓝 limit))
    (hlower : LowerLimitAtLeast (fun n => ‖v n‖) c) :
    0 < ‖limit‖ := by
  have hnorm : Tendsto (fun n => ‖v n‖) atTop (𝓝 ‖limit‖) :=
    tendsto_norm.comp hv
  by_contra hzero
  have hle : ‖limit‖ ≤ 0 := le_of_not_gt hzero
  have heps : 0 < c / 2 := half_pos hc
  have hlowerHalf := hlower (c / 2) (by linarith)
  have hupperHalf : ∀ᶠ n in atTop, ‖v n‖ < c / 2 := by
    have : c / 2 ∈ Set.Ioi ‖limit‖ := by
      simp only [Set.mem_Ioi]
      linarith
    exact (tendsto_order.1 hnorm).2 _ this
  obtain ⟨n, hn1, hn2⟩ := (hlowerHalf.and hupperHalf).exists
  linarith

/-- A nonzero centered vacuum vector excludes every scalar operator. -/
theorem nonscalar_of_centered_vacuum
    (T : E →L[ℂ] E) (vacuum : E) (hVacuum : ‖vacuum‖ = 1)
    (hCentered :
      T vacuum - inner ℂ vacuum (T vacuum) • vacuum ≠ 0) :
    ∀ c : ℂ, T ≠ c • ContinuousLinearMap.id ℂ E := by
  intro c hScalar
  apply hCentered
  rw [hScalar]
  simp only [smul_apply, ContinuousLinearMap.id_apply,
    inner_smul_right, inner_self_eq_norm_sq_to_K, hVacuum]
  norm_num

/-- The manuscript's liminf clause: convergence of centered vacuum vectors,
together with a positive lower limit of their norms, makes the limiting
observable non-scalar. -/
theorem nonscalar_of_centered_vacuum_liminf
    (T : E →L[ℂ] E) (vacuum : E) (hVacuum : ‖vacuum‖ = 1)
    (centered : ℕ → E) (c : ℝ) (hc : 0 < c)
    (hCenteredLimit :
      Tendsto centered atTop
        (𝓝 (T vacuum - inner ℂ vacuum (T vacuum) • vacuum)))
    (hLower : LowerLimitAtLeast (fun n => ‖centered n‖) c) :
    ∀ scalar : ℂ, T ≠ scalar • ContinuousLinearMap.id ℂ E := by
  apply nonscalar_of_centered_vacuum T vacuum hVacuum
  exact norm_pos_iff.mp
    (positive_norm_of_lowerLimitAtLeast hc hCenteredLimit hLower)

/-! ### Strong star-polynomial calculus on the common local core -/

/-- A locally uniformly bounded operator family can act on a moving strongly
convergent vector.  This is the complex-Hilbert version needed for products
of observable families. -/
theorem tendsto_apply_moving_of_uniform_bound
    {I : Type*} {l : Filter I}
    (A : I → E →L[ℂ] E) (A0 : E →L[ℂ] E)
    (x : I → E) (x0 : E)
    (hx : Tendsto x l (𝓝 x0))
    (hAx0 : Tendsto (fun i => A i x0) l (𝓝 (A0 x0)))
    (hBound : ∃ C : ℝ, ∀ᶠ i in l, ‖A i‖ ≤ C) :
    Tendsto (fun i => A i (x i)) l (𝓝 (A0 x0)) := by
  rcases hBound with ⟨C, hC⟩
  have hdiff : Tendsto (fun i => x i - x0) l (𝓝 0) := by
    simpa using hx.sub_const x0
  have hsmall : Tendsto (fun i => A i (x i - x0)) l (𝓝 0) := by
    apply squeeze_zero_norm'
    · filter_upwards [hC] with i hi
      calc
        ‖A i (x i - x0)‖ ≤ ‖A i‖ * ‖x i - x0‖ :=
          (A i).le_opNorm _
        _ ≤ C * ‖x i - x0‖ :=
          mul_le_mul_of_nonneg_right hi (norm_nonneg _)
    · simpa using tendsto_const_nhds.mul hdiff.norm
  have hsum := hsmall.add hAx0
  simpa only [zero_add] using hsum.congr' (by
    filter_upwards with i
    rw [map_sub]
    abel)

/-- Finite noncommutative star-polynomials in an indexed operator bank. -/
inductive StarPolynomial (index : Type*)
  | scalar : ℂ → StarPolynomial index
  | atom : index → StarPolynomial index
  | starAtom : index → StarPolynomial index
  | add : StarPolynomial index → StarPolynomial index → StarPolynomial index
  | mul : StarPolynomial index → StarPolynomial index → StarPolynomial index

namespace StarPolynomial

variable {index : Type*}

/-- Evaluation of a star-polynomial in bounded Hilbert-space operators. -/
def eval : StarPolynomial index → (index → E →L[ℂ] E) → E →L[ℂ] E
  | scalar c, _ => c • ContinuousLinearMap.id ℂ E
  | atom i, A => A i
  | starAtom i, A => ContinuousLinearMap.adjoint (A i)
  | add p q, A => eval p A + eval q A
  | mul p q, A => (eval p A).comp (eval q A)

/-- A recursive common operator-norm bound. -/
def bound : StarPolynomial index → ℝ → ℝ
  | scalar c, _ => ‖c‖
  | atom _, C => C
  | starAtom _, C => C
  | add p q, C => bound p C + bound q C
  | mul p q, C => bound p C * bound q C

theorem bound_nonnegative (p : StarPolynomial index) {C : ℝ} (hC : 0 ≤ C) :
    0 ≤ p.bound C := by
  induction p with
  | scalar c => exact norm_nonneg c
  | atom i => exact hC
  | starAtom i => exact hC
  | add p q hp hq => exact add_nonneg hp hq
  | mul p q hp hq => exact mul_nonneg hp hq

theorem eval_norm_le (p : StarPolynomial index)
    (A : index → E →L[ℂ] E) (C : ℝ)
    (hC : 0 ≤ C)
    (hA : ∀ i, ‖A i‖ ≤ C) :
    ‖p.eval A‖ ≤ p.bound C := by
  induction p with
  | scalar c =>
      rw [eval, bound, norm_smul]
      exact mul_le_of_le_one_right (norm_nonneg c)
        ContinuousLinearMap.norm_id_le
  | atom i =>
      exact hA i
  | starAtom i =>
      simpa [eval, bound] using hA i
  | add p q hp hq =>
      exact (norm_add_le _ _).trans (add_le_add hp hq)
  | mul p q hp hq =>
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul hp hq (norm_nonneg _) (bound_nonnegative p hC))

/-- A bounded operator preserves a linear core. -/
def Preserves (D : Submodule ℂ E) (A : E →L[ℂ] E) : Prop :=
  ∀ x : D, A (x : E) ∈ D

theorem eval_preserves (p : StarPolynomial index)
    (D : Submodule ℂ E) (A : index → E →L[ℂ] E)
    (hA : ∀ i, Preserves D (A i))
    (hStar : ∀ i, Preserves D (ContinuousLinearMap.adjoint (A i))) :
    Preserves D (p.eval A) := by
  induction p with
  | scalar c =>
      intro x
      simpa [eval] using D.smul_mem c x.property
  | atom i => exact hA i
  | starAtom i => exact hStar i
  | add p q hp hq =>
      intro x
      exact D.add_mem (hp x) (hq x)
  | mul p q hp hq =>
      intro x
      exact hp ⟨q.eval A x, hq x⟩

/-- Strong convergence on an invariant common core is stable under every
finite noncommutative star-polynomial.  Adjoint atoms use the separately
declared strong convergence hypothesis required in the manuscript proof. -/
theorem tendsto_eval_on_core
    (p : StarPolynomial index) (D : Submodule ℂ E)
    (A : ℕ → index → E →L[ℂ] E) (A0 : index → E →L[ℂ] E)
    (C : ℝ) (hC : 0 ≤ C)
    (hBound : ∀ n i, ‖A n i‖ ≤ C)
    (hAtom : ∀ (i : index) (x : D),
      Tendsto (fun n => A n i (x : E)) atTop (𝓝 (A0 i x)))
    (hStarAtom : ∀ (i : index) (x : D),
      Tendsto (fun n => ContinuousLinearMap.adjoint (A n i) (x : E))
        atTop (𝓝 (ContinuousLinearMap.adjoint (A0 i) x)))
    (hPreserve0 : ∀ i, Preserves D (A0 i))
    (hStarPreserve0 : ∀ i,
      Preserves D (ContinuousLinearMap.adjoint (A0 i)))
    (x : D) :
    Tendsto (fun n => p.eval (A n) (x : E)) atTop
      (𝓝 (p.eval A0 x)) := by
  induction p generalizing x with
  | scalar c =>
      exact tendsto_const_nhds
  | atom i =>
      exact hAtom i x
  | starAtom i =>
      exact hStarAtom i x
  | add p q hp hq =>
      exact (hp x).add (hq x)
  | mul p q hp hq =>
      let y0 : D := ⟨q.eval A0 x,
        eval_preserves q D A0 hPreserve0 hStarPreserve0 x⟩
      apply tendsto_apply_moving_of_uniform_bound
        (fun n => p.eval (A n)) (p.eval A0)
        (fun n => q.eval (A n) (x : E)) (y0 : E)
        (hq x) (hp y0)
      exact ⟨p.bound C, Eventually.of_forall fun n =>
        eval_norm_le p (A n) C hC (hBound n)⟩

/-- Vanishing star-polynomial residuals on the dense local GNS core become an
exact operator identity in the limit. -/
theorem relation_persists
    (p : StarPolynomial index) (D : Submodule ℂ E)
    (hDense : Dense (D : Set E))
    (A : ℕ → index → E →L[ℂ] E) (A0 : index → E →L[ℂ] E)
    (C : ℝ) (hC : 0 ≤ C)
    (hBound : ∀ n i, ‖A n i‖ ≤ C)
    (hAtom : ∀ (i : index) (x : D),
      Tendsto (fun n => A n i (x : E)) atTop (𝓝 (A0 i x)))
    (hStarAtom : ∀ (i : index) (x : D),
      Tendsto (fun n => ContinuousLinearMap.adjoint (A n i) (x : E))
        atTop (𝓝 (ContinuousLinearMap.adjoint (A0 i) x)))
    (hPreserve0 : ∀ i, Preserves D (A0 i))
    (hStarPreserve0 : ∀ i,
      Preserves D (ContinuousLinearMap.adjoint (A0 i)))
    (hResidual : ∀ x : D,
      Tendsto (fun n => p.eval (A n) (x : E)) atTop (𝓝 0)) :
    p.eval A0 = 0 := by
  apply polynomial_relation_persists (p.eval A0) (D : Set E) hDense
  intro x hx
  let dx : D := ⟨x, hx⟩
  exact tendsto_nhds_unique
    (tendsto_eval_on_core p D A A0 C hC hBound hAtom hStarAtom
      hPreserve0 hStarPreserve0 dx)
    (hResidual dx)

end StarPolynomial

end
end DenseGNSObservableLimit
end NCG
