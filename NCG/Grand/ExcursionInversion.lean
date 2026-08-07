/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SqrtPolar

/-!
# Resolved excursion inversion and the exact-lift normal form
  (`thm:resolved-excursion-inversion` and
  `cor:exact-lift-normal-form`, Gran-Tensor manuscript)

For branch lifts `T̃_a = [[A_a, B_a], [C_a, D_a]]` acting on
`ℒ ⊕ ℰ`, with word lifts `T̃_w = T̃_b·T̃_u·…` and visible
corner `X_w = P T̃_w J` (top-left block):

* `resolved_excursion_inversion`:
  (i) the length-one coefficients are `X_a = A_a`;
  (ii) the boxed irreducible hidden excursion is the
      connected coefficient:
      `B_b D_u C_a = X_{bua} - A_b X_{ua} - X_{bu} A_a
        + A_b A_u A_a`
      (the `z_b z_u z_a` coefficient of
      `𝐄 = 𝐁(I-𝐃)⁻¹𝐂`);
  (iii) exactness (`X_w = T_w` for every resolved word)
      forces `A_a = T_a`, kills every hidden excursion
      `B_b D_u C_a = 0`, and kills the whole provenance
      block: `B_b · H_w = 0` for every word `w`
      (`H_w` the bottom-left block of `T̃_w`) — this is
      `cor:exact-lift-normal-form`, since the
      source-reachable hidden sector is spanned by the
      columns of the `H_w`, on which every `B_b` vanishes,
      giving the boxed lower-triangular normal form
      `T̃_a = [[T_a, 0], [C_a, D_a]]`;
  (iv) the positive branch: a vanishing aggregate of
      positive-semidefinite excursion kernels kills every
      summand.

The formal-series packaging
`𝐗(z)⁻¹ = I - 𝐀(z) - 𝐄(z)` is the generating-function
form of the coefficient recursions (i)–(ii) over all words.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

set_option linter.unusedDecidableInType false

namespace NCG

variable {σ n p : Type*} [Fintype n] [Fintype p]
  [DecidableEq n] [DecidableEq p]

/-- The block word lift `T̃_w = T̃_b·T̃_u·…`. -/
def excursionLift (A : σ → Matrix n n ℂ)
    (B : σ → Matrix n p ℂ) (C : σ → Matrix p n ℂ)
    (D : σ → Matrix p p ℂ) :
    List σ → Matrix (n ⊕ p) (n ⊕ p) ℂ
  | [] => 1
  | a :: w => Matrix.fromBlocks (A a) (B a) (C a) (D a)
      * excursionLift A B C D w

/-- Visible corner `X_w = P T̃_w J`. -/
def excursionX (A : σ → Matrix n n ℂ)
    (B : σ → Matrix n p ℂ) (C : σ → Matrix p n ℂ)
    (D : σ → Matrix p p ℂ) (w : List σ) : Matrix n n ℂ :=
  (excursionLift A B C D w).toBlocks₁₁

/-- Hidden provenance corner `H_w`. -/
def excursionH (A : σ → Matrix n n ℂ)
    (B : σ → Matrix n p ℂ) (C : σ → Matrix p n ℂ)
    (D : σ → Matrix p p ℂ) (w : List σ) : Matrix p n ℂ :=
  (excursionLift A B C D w).toBlocks₂₁

variable (A : σ → Matrix n n ℂ) (B : σ → Matrix n p ℂ)
  (C : σ → Matrix p n ℂ) (D : σ → Matrix p p ℂ)

lemma excursionX_nil : excursionX A B C D [] = 1 := by
  simp only [excursionX, excursionLift,
    ← Matrix.fromBlocks_one, Matrix.toBlocks_fromBlocks₁₁]

lemma excursionH_nil : excursionH A B C D [] = 0 := by
  simp only [excursionH, excursionLift,
    ← Matrix.fromBlocks_one, Matrix.toBlocks_fromBlocks₂₁]

lemma excursionX_cons (a : σ) (w : List σ) :
    excursionX A B C D (a :: w)
      = A a * excursionX A B C D w
        + B a * excursionH A B C D w := by
  simp only [excursionX, excursionH, excursionLift]
  rw [← Matrix.fromBlocks_toBlocks (excursionLift A B C D w),
    Matrix.fromBlocks_multiply]
  simp [Matrix.toBlocks_fromBlocks₁₁,
    Matrix.toBlocks_fromBlocks₂₁]

lemma excursionH_cons (a : σ) (w : List σ) :
    excursionH A B C D (a :: w)
      = C a * excursionX A B C D w
        + D a * excursionH A B C D w := by
  simp only [excursionX, excursionH, excursionLift]
  rw [← Matrix.fromBlocks_toBlocks (excursionLift A B C D w),
    Matrix.fromBlocks_multiply]
  simp [Matrix.toBlocks_fromBlocks₁₁,
    Matrix.toBlocks_fromBlocks₂₁]

/-- `thm:resolved-excursion-inversion` together with
`cor:exact-lift-normal-form` (clause (iii)). -/
theorem resolved_excursion_inversion :
    -- (i) length-one coefficients
    (∀ a, excursionX A B C D [a] = A a)
    -- (ii) the boxed connected-coefficient identity
    ∧ (∀ a b u, B b * (D u * C a)
        = excursionX A B C D [b, u, a]
          - A b * excursionX A B C D [u, a]
          - excursionX A B C D [b, u] * A a
          + A b * (A u * A a))
    -- (iii) exactness ⟹ normal form
    ∧ (∀ T : σ → Matrix n n ℂ,
        (∀ w, excursionX A B C D w = (w.map T).prod) →
        (∀ a, A a = T a)
        ∧ (∀ a b u, B b * (D u * C a) = 0)
        ∧ (∀ (b : σ) (w : List σ),
            B b * excursionH A B C D w = 0))
    -- (iv) the positive branch
    ∧ (∀ {ι : Type} (s : Finset ι)
        (f : ι → Matrix n n ℂ),
        (∀ i ∈ s, (f i).PosSemidef) →
        (∑ i ∈ s, f i) = 0 → ∀ i ∈ s, f i = 0) := by
  have hXa : ∀ a, excursionX A B C D [a] = A a := by
    intro a
    rw [excursionX_cons, excursionX_nil, excursionH_nil,
      Matrix.mul_one, Matrix.mul_zero, add_zero]
  have hid : ∀ a b u, B b * (D u * C a)
      = excursionX A B C D [b, u, a]
        - A b * excursionX A B C D [u, a]
        - excursionX A B C D [b, u] * A a
        + A b * (A u * A a) := by
    intro a b u
    simp only [excursionX_cons, excursionH_cons,
      excursionX_nil, excursionH_nil, Matrix.mul_one,
      Matrix.mul_zero, add_zero, Matrix.mul_add,
      Matrix.add_mul, Matrix.mul_assoc]
    abel
  refine ⟨hXa, hid, ?_, ?_⟩
  · intro T hex
    have hA : ∀ a, A a = T a := by
      intro a
      have h := hex [a]
      rw [hXa] at h
      simpa using h
    refine ⟨hA, ?_, ?_⟩
    · intro a b u
      rw [hid a b u, hex [b, u, a], hex [u, a], hex [b, u],
        hA a, hA b, hA u]
      simp only [List.map_cons, List.map_nil,
        List.prod_cons, List.prod_nil, Matrix.mul_one,
        Matrix.mul_assoc]
      abel
    · intro b w
      have h1 := excursionX_cons A B C D b w
      rw [hex (b :: w), hex w, hA b, List.map_cons,
        List.prod_cons] at h1
      have h2 : ((b :: w).map T).prod
          + B b * excursionH A B C D w
          = ((b :: w).map T).prod + 0 := by
        rw [add_zero, List.map_cons, List.prod_cons]
        exact h1.symm
      rw [List.map_cons, List.prod_cons] at h2
      exact add_left_cancel h2
  · intro ι s f hf hsum i hi
    have htr : ∑ j ∈ s, (f j).trace = 0 := by
      rw [← Matrix.trace_sum, hsum, Matrix.trace_zero]
    have hz : (f i).trace = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun j hj => (hf j hj).trace_nonneg)).mp htr i hi
    have h2 : (CFC.sqrt (f i))ᴴ * CFC.sqrt (f i) = f i := by
      rw [sqrt_isHermitian, sqrt_mul_self_eq _ (hf i hi)]
    have h3 : ((CFC.sqrt (f i))ᴴ * CFC.sqrt (f i)).trace
        = 0 := by
      rw [h2]
      exact hz
    have h4 :=
      Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp h3
    rw [← h2, h4]
    simp

end NCG
