/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Exact Hoeffding proper-subset short
  (`thm:GT-Hoeffding-short`, Gran-Tensor manuscript)

* `gt_hoeffding_short`: for the complementary idempotent
  pair `P + Q = 1`, `PQ = QP = 0`, `P² = P`, `Q² = Q`
  (vacuum projection and its excitation complement) and
  the grade projections
  `Π_S = ⊗ᵢ (Q if i ∈ S else P)` on the `t`-fold tensor
  power (rendered as function-indexed Kronecker products),
  (i) the boxed resolution `∑_S Π_S = 1` — the tensor
      power splits into the `2^t` support grades;
  (ii) each `Π_S` is idempotent and distinct grades
      annihilate (`Π_S Π_{S'} = 0`) — the splitting is an
      orthogonal direct sum;
  (iii) the boxed complement identification: the top grade
      is `Q^{⊗t} = Π_{[t]}`, and
      `Q^{⊗t} = 1 - ∑_{S ⊊ [t]} Π_S`; hence
  (iv) the boxed simultaneous short
      `𝕌_t(Z) = Z*(1 - ∑_{S ⊊ [t]} Π_S)Z = Z*Q^{⊗t}Z`.

The identification of `P = |Ω⟩⟨Ω|` with the vacuum state
of `H₁ = ℂΩ ⊕ H₁⁰` and the variational (shorting) reading
of `𝕌_t` are the manuscript's Hilbert packaging.
-/

open Matrix Finset

namespace NCG

/-- Slotwise (t-fold) Kronecker product of a family of
matrices, on the function-indexed carrier. -/
def tensorPow {n : Type} (t : ℕ)
    (A : Fin t → Matrix n n ℂ) :
    Matrix (Fin t → n) (Fin t → n) ℂ :=
  Matrix.of fun x y => ∏ i, A i (x i) (y i)

theorem tensorPow_mul {n : Type} [Fintype n] (t : ℕ)
    (A B : Fin t → Matrix n n ℂ) :
    tensorPow t A * tensorPow t B
      = tensorPow t (fun i => A i * B i) := by
  ext x y
  simp only [tensorPow, Matrix.mul_apply, Matrix.of_apply]
  rw [show ∏ i, (∑ j, A i (x i) j * B i j (y i))
      = ∑ z ∈ Fintype.piFinset (fun _ => univ),
        ∏ i, A i (x i) (z i) * B i (z i) (y i) from
    Finset.prod_univ_sum _ _]
  rw [Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.prod_mul_distrib]

set_option linter.unusedFintypeInType false in
theorem tensorPow_one {n : Type} [Fintype n]
    [DecidableEq n] (t : ℕ) :
    tensorPow t (fun _ => (1 : Matrix n n ℂ)) = 1 := by
  ext x y
  simp only [tensorPow, Matrix.of_apply, Matrix.one_apply]
  rw [Finset.prod_boole]
  by_cases h : x = y
  · have h2 : ∀ i ∈ univ, x i = y i := fun i _ =>
      congrFun h i
    rw [if_pos h2, if_pos h]
  · have h2 : ¬ ∀ i ∈ univ, x i = y i := by
      intro hall
      exact h (funext fun i => hall i (mem_univ i))
    rw [if_neg h2, if_neg h]

set_option linter.unusedFintypeInType false in
theorem tensorPow_zero_slot {n : Type} [Fintype n]
    (t : ℕ) (A : Fin t → Matrix n n ℂ) (i0 : Fin t)
    (h : A i0 = 0) : tensorPow t A = 0 := by
  ext x y
  simp only [tensorPow, Matrix.of_apply,
    Matrix.zero_apply]
  exact Finset.prod_eq_zero (Finset.mem_univ i0)
    (by rw [h]; rfl)

/-- `thm:GT-Hoeffding-short`. -/
theorem gt_hoeffding_short {n : Type} [Fintype n]
    [DecidableEq n] (t : ℕ) (P Q : Matrix n n ℂ)
    (hPQ1 : P + Q = 1) (hPQ : P * Q = 0)
    (hQP : Q * P = 0) (hPP : P * P = P)
    (hQQ : Q * Q = Q) :
    -- the grade projections
    let Pi : Finset (Fin t)
        → Matrix (Fin t → n) (Fin t → n) ℂ :=
      fun S => tensorPow t
        (fun i => if i ∈ S then Q else P)
    -- (i) the boxed resolution of the identity
    (∑ S : Finset (Fin t), Pi S = 1)
    -- (ii) orthogonal idempotent grades
    ∧ (∀ S, Pi S * Pi S = Pi S)
    ∧ (∀ S S', S ≠ S' → Pi S * Pi S' = 0)
    -- (iii) the boxed complement identification
    ∧ (Pi univ = tensorPow t (fun _ => Q))
    ∧ (tensorPow t (fun _ => Q)
        = 1 - ∑ S ∈ univ.erase univ, Pi S)
    -- (iv) the boxed simultaneous short
    ∧ (∀ {m : Type} (Z : Matrix (Fin t → n) m ℂ),
        Zᴴ * (1 - ∑ S ∈ univ.erase univ, Pi S) * Z
          = Zᴴ * tensorPow t (fun _ => Q) * Z) := by
  intro Pi
  -- entrywise split of a grade projection
  have hsplit : ∀ (S : Finset (Fin t))
      (x y : Fin t → n),
      Pi S x y = (∏ i ∈ univ.filter (· ∈ S),
          Q (x i) (y i))
        * ∏ i ∈ univ.filter (¬ · ∈ S), P (x i) (y i) := by
    intro S x y
    simp only [Pi, tensorPow, Matrix.of_apply]
    rw [Finset.prod_congr rfl fun i _ =>
      apply_ite (fun M : Matrix n n ℂ => M (x i) (y i))
        (i ∈ S) Q P]
    exact Finset.prod_ite _ _
  -- (i): binomial resolution of the identity
  have hres : ∑ S : Finset (Fin t), Pi S = 1 := by
    have h : ∑ S : Finset (Fin t), Pi S
        = tensorPow t (fun _ => Q + P) := by
      ext x y
      rw [Matrix.sum_apply]
      simp only [tensorPow, Matrix.of_apply]
      rw [Finset.sum_congr rfl fun S _ => hsplit S x y]
      rw [Finset.sum_congr rfl (fun S _ => by
        rw [Finset.filter_mem_eq_inter,
          Finset.univ_inter, ← Finset.sdiff_eq_filter])]
      rw [← Finset.powerset_univ, ← Finset.prod_add]
      exact Finset.prod_congr rfl fun i _ =>
        (Matrix.add_apply _ _ _ _).symm
    rw [h, show (fun _ : Fin t => Q + P)
        = fun _ : Fin t => (1 : Matrix n n ℂ) from
      funext fun _ => by rw [add_comm, hPQ1],
      tensorPow_one]
  -- (ii) idempotent grades
  have hid : ∀ S, Pi S * Pi S = Pi S := by
    intro S
    rw [show Pi S * Pi S = tensorPow t
        (fun i => (if i ∈ S then Q else P)
          * (if i ∈ S then Q else P)) from
      tensorPow_mul t _ _]
    congr 1
    funext i
    by_cases hi : i ∈ S
    · simp [hi, hQQ]
    · simp [hi, hPP]
  -- distinct grades annihilate
  have horth : ∀ S S', S ≠ S' → Pi S * Pi S' = 0 := by
    intro S S' hne
    obtain ⟨i0, hi0⟩ : ∃ i, ¬(i ∈ S ↔ i ∈ S') := by
      by_contra hall
      push Not at hall
      exact hne (Finset.ext fun i => hall i)
    rw [show Pi S * Pi S' = tensorPow t
        (fun i => (if i ∈ S then Q else P)
          * (if i ∈ S' then Q else P)) from
      tensorPow_mul t _ _]
    apply tensorPow_zero_slot t _ i0
    rcases Classical.em (i0 ∈ S) with h1 | h1
    · have h2 : i0 ∉ S' := fun h =>
        hi0 ⟨fun _ => h, fun _ => h1⟩
      simp [h1, h2, hQP]
    · have h2 : i0 ∈ S' := by
        by_contra h2
        exact hi0 ⟨fun h => absurd h h1,
          fun h => absurd h h2⟩
      simp [h1, h2, hPQ]
  -- (iii) the top grade is the excitation power
  have htop : Pi univ = tensorPow t (fun _ => Q) := by
    simp only [Pi]
    congr 1
    funext i
    simp
  have hcompl : tensorPow t (fun _ => Q)
      = 1 - ∑ S ∈ univ.erase univ, Pi S := by
    have hsum := Finset.sum_erase_add univ Pi
      (Finset.mem_univ (univ : Finset (Fin t)))
    rw [hres] at hsum
    rw [← htop]
    exact eq_sub_of_add_eq' hsum
  refine ⟨hres, hid, horth, htop, hcompl, ?_⟩
  intro m Z
  rw [← hcompl]

end NCG
