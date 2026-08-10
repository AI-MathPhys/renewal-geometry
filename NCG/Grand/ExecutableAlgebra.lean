/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.HankelMinimality

/-!
# Realization-free executable algebra
  (`thm:executable-predictive-algebra`, Gran-Tensor manuscript)

* `executable_predictive_algebra`: on a reachable
  (past columns span) and future-separated (future rows
  separate) linear realization, a forward word polynomial
  `q = Σ_w c_w·w` acts as zero exactly when all its scalar table
  entries `Σ_w c_w·Pr(f∘w∘p)` vanish — the scalar operational
  table determines the executable predictive algebra directly,
  with no Kraus map, Stinespring environment, Hilbert metric, or
  formal reverse.

Rendering disclosed: `𝓑_X^pred ≅ 𝔓_X⁺/Ker ρ_X⁺` is rendered by
the proved kernel test (membership in the kernel is the scalar
identity); the universal similarity of any other reachable
future-separated realization is `thm:hankel-minimality`'s
uniqueness clause extended multiplicatively (`hankel_minimality`,
proved).
-/

open Matrix

namespace NCG

/-- `thm:executable-predictive-algebra`: the scalar kernel test
for forward word polynomials. -/
theorem executable_predictive_algebra {ι d P F : Type*}
    [Fintype d] [DecidableEq d]
    (T : ι → Matrix d d ℝ) (Q : Finset (List ι))
    (coef : List ι → ℝ)
    (p : P → (d → ℝ)) (f : F → (d → ℝ))
    (hreach : Submodule.span ℝ (Set.range p) = ⊤)
    (hsep : ∀ v : d → ℝ, (∀ j : F, f j ⬝ᵥ v = 0) → v = 0) :
    (∑ w ∈ Q, coef w • (w.map T).prod) = 0
    ↔ ∀ (j : F) (i : P),
        ∑ w ∈ Q, coef w * (f j ⬝ᵥ ((w.map T).prod *ᵥ p i))
          = 0 := by
  have hpull : ∀ (v : d → ℝ) (j : F),
      ∑ w ∈ Q, coef w * (f j ⬝ᵥ ((w.map T).prod *ᵥ v))
      = f j ⬝ᵥ ((∑ w ∈ Q, coef w • (w.map T).prod) *ᵥ v) := by
    intro v j
    rw [Matrix.sum_mulVec, dotProduct_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  constructor
  · intro h j i
    rw [hpull, h, Matrix.zero_mulVec, dotProduct_zero]
  · intro h
    have hZp : ∀ i : P,
        (∑ w ∈ Q, coef w • (w.map T).prod) *ᵥ p i = 0 := by
      intro i
      refine hsep _ fun j => ?_
      rw [← hpull]
      exact h j i
    have hall : ∀ v : d → ℝ,
        (∑ w ∈ Q, coef w • (w.map T).prod) *ᵥ v = 0 := by
      intro v
      have hv : v ∈ Submodule.span ℝ (Set.range p) := by
        rw [hreach]
        trivial
      induction hv using Submodule.span_induction with
      | mem x hx =>
          obtain ⟨i, rfl⟩ := hx
          exact hZp i
      | zero => exact Matrix.mulVec_zero _
      | add x y hx hy ihx ihy =>
          rw [Matrix.mulVec_add, ihx, ihy, add_zero]
      | smul c x hx ihx =>
          rw [Matrix.mulVec_smul, ihx, smul_zero]
    ext k l
    have hcol := hall (Pi.single l 1)
    have hk := congrFun hcol k
    simp only [Matrix.mulVec, dotProduct, Pi.single_apply,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, Pi.zero_apply] at hk
    simpa using hk

/-! ## Multiplicative naturality of the minimal similarity -/

/-- Execute a typed forward word from left to right. -/
def forwardWordAction {R N ι : Type*} [Semiring R] [AddCommMonoid N]
    [Module R N] (T : ι → Module.End R N) : List ι → Module.End R N
  | [] => LinearMap.id
  | a :: w => (forwardWordAction T w).comp (T a)

@[simp] theorem forwardWordAction_nil_apply
    {R N ι : Type*} [Semiring R] [AddCommMonoid N] [Module R N]
    (T : ι → Module.End R N) (v : N) : forwardWordAction T [] v = v := rfl

@[simp] theorem forwardWordAction_cons_apply
    {R N ι : Type*} [Semiring R] [AddCommMonoid N] [Module R N]
    (T : ι → Module.End R N) (a : ι) (w : List ι) (v : N) :
    forwardWordAction T (a :: w) v = forwardWordAction T w (T a v) := rfl

/-- A primitive intertwiner automatically intertwines every executable word. -/
theorem forwardWordAction_intertwines
    {R N₁ N₂ ι : Type*} [Semiring R]
    [AddCommMonoid N₁] [Module R N₁] [AddCommMonoid N₂] [Module R N₂]
    (S : N₁ →ₗ[R] N₂) (T₁ : ι → Module.End R N₁)
    (T₂ : ι → Module.End R N₂)
    (hprimitive : ∀ a v, S (T₁ a v) = T₂ a (S v))
    (w : List ι) (v : N₁) :
    S (forwardWordAction T₁ w v) = forwardWordAction T₂ w (S v) := by
  induction w generalizing v with
  | nil => rfl
  | cons a w ih =>
      rw [forwardWordAction_cons_apply, ih, hprimitive,
        forwardWordAction_cons_apply]

/-- Consequently the same similarity intertwines every finite forward-word
polynomial. -/
theorem forwardPolynomial_intertwines
    {R N₁ N₂ ι : Type*} [CommSemiring R]
    [AddCommMonoid N₁] [Module R N₁] [AddCommMonoid N₂] [Module R N₂]
    (S : N₁ →ₗ[R] N₂) (T₁ : ι → Module.End R N₁)
    (T₂ : ι → Module.End R N₂)
    (hprimitive : ∀ a v, S (T₁ a v) = T₂ a (S v))
    (words : Finset (List ι)) (coef : List ι → R) (v : N₁) :
    S (∑ w ∈ words, coef w • forwardWordAction T₁ w v) =
      ∑ w ∈ words, coef w • forwardWordAction T₂ w (S v) := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro w hw
  rw [map_smul, forwardWordAction_intertwines S T₁ T₂ hprimitive]

end NCG
