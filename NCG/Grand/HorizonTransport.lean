/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.TwoStateRenewal

/-!
# Projective horizon transport and the infinite marked path law
  (`thm:renewal-horizon-transport`, Gran-Tensor manuscript)

* `renewal_horizon_transport`: for any resolved branch family
  `T_a` with `Σ_a T_a = M`, row-stochastic `M`, and a
  probability phase law `α`, the cylinder tables
  `p_α[w] = α·T_{a₁}⋯T_{aₙ}·𝟙` satisfy the boxed consistency
  `Σ_a p_α[wa] = p_α[w]` and normalization
  `Σ_{|w|=n} p_α[w] = 1`.
* `two_state_horizon_transport`: instantiation on the fixed
  two-state renewal instrument with its five resolved branches
  `{hh, hp, pp, b₀, b₁}` summing to `M₀`.

Rendering disclosed: the unique infinite path law, the AF
cylinder-algebra state, and its faithfulness after null-support
quotient are the manuscript's measure-theoretic packaging of the
proved cylinder-consistency identities; the strict identity of
horizon maps on minimal predictors is the rank-two persistence
clause.
-/

open Matrix

namespace NCG

/-- Ordered branch-word product. -/
def branchWordProd {ι d : Type*} [Fintype d] [DecidableEq d]
    (T : ι → Matrix d d ℝ) {n : ℕ} (w : Fin n → ι) :
    Matrix d d ℝ :=
  (List.ofFn fun i => T (w i)).prod

/-- Cylinder probability of a resolved word. -/
def branchCylP {ι d : Type*} [Fintype d] [DecidableEq d]
    (T : ι → Matrix d d ℝ) (α : d → ℝ) {n : ℕ}
    (w : Fin n → ι) : ℝ :=
  α ⬝ᵥ (branchWordProd T w *ᵥ fun _ => 1)

/-- `thm:renewal-horizon-transport`: branch-sum cylinder
consistency and horizon normalization. -/
theorem renewal_horizon_transport {ι d : Type*} [Fintype ι]
    [Fintype d] [DecidableEq d]
    (T : ι → Matrix d d ℝ) (M : Matrix d d ℝ) (α : d → ℝ)
    (hsum : ∑ x : ι, T x = M)
    (hrow : M *ᵥ (fun _ => 1) = fun _ => 1)
    (hα : (α ⬝ᵥ fun _ => (1 : ℝ)) = 1) :
    (∀ (n : ℕ) (w : Fin n → ι),
      ∑ x : ι, branchCylP T α (Fin.snoc w x) = branchCylP T α w)
    ∧ (∀ n : ℕ, ∑ w : Fin n → ι, branchCylP T α w = 1) := by
  have hword : ∀ {n : ℕ} (w : Fin n → ι) (x : ι),
      branchWordProd T (Fin.snoc w x)
        = branchWordProd T w * T x := by
    intro n w x
    unfold branchWordProd
    rw [List.ofFn_succ']
    simp only [Fin.snoc_castSucc, Fin.snoc_last,
      List.concat_eq_append, List.prod_append,
      List.prod_cons, List.prod_nil, mul_one]
  have hcons : ∀ {n : ℕ} (x : ι) (w : Fin n → ι),
      branchWordProd T (Fin.cons x w)
        = T x * branchWordProd T w := by
    intro n x w
    unfold branchWordProd
    rw [List.ofFn_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, List.prod_cons]
  constructor
  · intro n w
    calc ∑ x : ι, branchCylP T α (Fin.snoc w x)
        = ∑ x : ι,
            α ⬝ᵥ ((branchWordProd T w * T x) *ᵥ fun _ => 1) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          unfold branchCylP
          rw [hword]
      _ = α ⬝ᵥ ((branchWordProd T w * M) *ᵥ fun _ => 1) := by
          rw [← hsum, Finset.mul_sum, Matrix.sum_mulVec,
            dotProduct_sum]
      _ = branchCylP T α w := by
          unfold branchCylP
          rw [← Matrix.mulVec_mulVec, hrow]
  · have hpow : ∀ n : ℕ,
        ∑ w : Fin n → ι, branchWordProd T w = M ^ n := by
      intro n
      induction n with
      | zero =>
          rw [pow_zero]
          rw [show (∑ w : Fin 0 → ι, branchWordProd T w)
              = ∑ _w : Fin 0 → ι, (1 : Matrix d d ℝ) from
            Finset.sum_congr rfl fun w _ => by
              simp [branchWordProd]]
          rw [Finset.sum_const]
          simp
      | succ k ih =>
          calc ∑ w : Fin (k + 1) → ι, branchWordProd T w
              = ∑ p : ι × (Fin k → ι),
                  branchWordProd T (Fin.cons p.1 p.2) :=
                (Fintype.sum_equiv (Fin.consEquiv fun _ => ι)
                  _ _ (fun p => rfl)).symm
            _ = ∑ p : ι × (Fin k → ι),
                  T p.1 * branchWordProd T p.2 :=
                Finset.sum_congr rfl fun p _ => hcons p.1 p.2
            _ = (∑ x : ι, T x)
                  * ∑ w : Fin k → ι, branchWordProd T w := by
                rw [Fintype.sum_prod_type,
                  Finset.sum_mul_sum]
            _ = M ^ (k + 1) := by
                rw [hsum, ih, pow_succ']
    have hMones : ∀ n : ℕ,
        (M ^ n) *ᵥ (fun _ => (1 : ℝ)) = fun _ => 1 := by
      intro n
      induction n with
      | zero => rw [pow_zero, Matrix.one_mulVec]
      | succ k ih =>
          rw [pow_succ', ← Matrix.mulVec_mulVec, ih, hrow]
    intro n
    calc ∑ w : Fin n → ι, branchCylP T α w
        = α ⬝ᵥ ((∑ w : Fin n → ι, branchWordProd T w)
            *ᵥ fun _ => 1) := by
          unfold branchCylP
          rw [Matrix.sum_mulVec, dotProduct_sum]
      _ = 1 := by rw [hpow, hMones, hα]

/-- The five resolved branches `{hh, hp, pp, b₀, b₁}` of the
two-state renewal instrument. -/
noncomputable def renBranch : Fin 5 → Matrix (Fin 2) (Fin 2) ℝ :=
  ![!![1/5, 0; 0, 0], !![0, 4/5; 0, 0], !![0, 0; 0, 1/3],
    !![0, 0; 1/3, 0], !![0, 0; 1/3, 0]]

/-- `thm:renewal-horizon-transport` (concrete instrument): the
five-branch resolution of `M₀` at the stationary phase law. -/
theorem two_state_horizon_transport :
    (∀ (n : ℕ) (w : Fin n → Fin 5),
      ∑ x : Fin 5,
        branchCylP renBranch ![5/11, 6/11] (Fin.snoc w x)
      = branchCylP renBranch ![5/11, 6/11] w)
    ∧ (∀ n : ℕ,
        ∑ w : Fin n → Fin 5,
          branchCylP renBranch ![5/11, 6/11] w = 1) := by
  refine renewal_horizon_transport renBranch renM0 _ ?_ ?_ ?_
  · ext i j
    fin_cases i <;> fin_cases j <;>
      (simp [renBranch, renM0, Fin.sum_univ_five,
        Matrix.sum_apply]; try norm_num)
  · funext i
    fin_cases i <;>
      (simp [renM0, Matrix.mulVec, dotProduct,
        Fin.sum_univ_two]; norm_num)
  · simp [dotProduct, Fin.sum_univ_two]
    norm_num

end NCG
