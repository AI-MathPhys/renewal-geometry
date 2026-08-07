/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SpectatorProduct
import NCG.Grand.HorizonTransport

/-!
# Semantic stripping of the renewal packet
  (`thm:renewal-semantic-stripping`, Gran-Tensor manuscript)

* `semantic_stripping_marginal`: any label-resolved extension of
  the renewal branches whose label marginal reproduces the
  original branch family leaves every renewal-native cylinder
  probability unchanged (`Σ_ℓ p'[w,ℓ] = p[w]`) — conservative
  domain loading.
* `semantic_stripping_tensor`: conversely, tensoring with an
  arbitrary label system on which the renewal letters act
  trivially (any row-stochastic label transfer and normalized
  label law) reproduces all renewal-native probabilities — the
  loading is not determined by the renewal packet.

Rendering disclosed: "the minimal record, Hankel quotient,
branch maps, and first-return law are unchanged" is the
manuscript's citation of the Part-I uniqueness theorems applied
to the restricted table; the two clauses proved here are the
restriction identity and the inequivalent-tensor witness that
drive that argument.
-/

open Matrix
open scoped Kronecker

namespace NCG

private theorem word_cons {ι d : Type*} [Fintype d]
    [DecidableEq d] (T : ι → Matrix d d ℝ) {k : ℕ}
    (w : Fin (k + 1) → ι) :
    branchWordProd T w
      = T (w 0) * branchWordProd T (fun i => w i.succ) := by
  unfold branchWordProd
  rw [List.ofFn_succ]
  simp only [List.prod_cons]

/-- Label-resolved word sums collapse to marginal word
products. -/
theorem semantic_stripping_marginal {ι L d : Type*}
    [Fintype L] [Fintype d] [DecidableEq d]
    (T' : ι × L → Matrix d d ℝ) (T : ι → Matrix d d ℝ)
    (hmarg : ∀ a : ι, ∑ l : L, T' (a, l) = T a)
    (α : d → ℝ) :
    ∀ {n : ℕ} (w : Fin n → ι),
      ∑ ℓ : Fin n → L,
        branchCylP T' α (fun i => (w i, ℓ i))
      = branchCylP T α w := by
  have hprod : ∀ {n : ℕ} (w : Fin n → ι),
      ∑ ℓ : Fin n → L,
        branchWordProd T' (fun i => (w i, ℓ i))
      = branchWordProd T w := by
    intro n
    induction n with
    | zero =>
        intro w
        rw [show (∑ ℓ : Fin 0 → L,
            branchWordProd T' (fun i => (w i, ℓ i)))
            = ∑ _ℓ : Fin 0 → L, (1 : Matrix d d ℝ) from
          Finset.sum_congr rfl fun ℓ _ => by
            simp [branchWordProd]]
        rw [Finset.sum_const]
        simp [branchWordProd]
    | succ k ih =>
        intro w
        have hstep :
            ∑ ℓ : Fin (k + 1) → L,
              branchWordProd T' (fun i => (w i, ℓ i))
            = ∑ p : L × (Fin k → L),
                T' (w 0, p.1)
                  * branchWordProd T'
                    (fun i => (w i.succ, p.2 i)) := by
          rw [← Equiv.sum_comp (Fin.consEquiv fun _ => L)
            (fun ℓ : Fin (k + 1) → L =>
              branchWordProd T' (fun i => (w i, ℓ i)))]
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [show ((Fin.consEquiv fun _ => L) p :
              Fin (k + 1) → L) = Fin.cons p.1 p.2 from rfl]
          rw [word_cons]
          congr 1
        rw [hstep, Fintype.sum_prod_type]
        have hred : (∑ x : L, ∑ y : Fin k → L,
            T' (w 0, (x, y).1) * branchWordProd T'
              (fun i => (w i.succ, (x, y).2 i)))
            = ∑ x : L, ∑ y : Fin k → L,
                T' (w 0, x) * branchWordProd T'
                  (fun i => (w i.succ, y i)) := rfl
        rw [hred, ← Finset.sum_mul_sum, hmarg (w 0),
          ih (fun i => w i.succ), ← word_cons T w]
  intro n w
  unfold branchCylP
  rw [← hprod w, Matrix.sum_mulVec, dotProduct_sum]

/-- Trivially-acting label tensors reproduce all renewal-native
probabilities. -/
theorem semantic_stripping_tensor {ι d L : Type*}
    [Fintype d] [DecidableEq d] [Fintype L] [DecidableEq L]
    (T : ι → Matrix d d ℝ) (N : Matrix L L ℝ) (α : d → ℝ)
    (β : L → ℝ)
    (hN : N *ᵥ (fun _ => 1) = fun _ => 1)
    (hβ : (β ⬝ᵥ fun _ => (1 : ℝ)) = 1) :
    ∀ {n : ℕ} (w : Fin n → ι),
      branchCylP (fun a => T a ⊗ₖ N)
        (fun q : d × L => α q.1 * β q.2) w
      = branchCylP T α w := by
  have hword : ∀ {n : ℕ} (w : Fin n → ι),
      branchWordProd (fun a => T a ⊗ₖ N) w
      = branchWordProd T w ⊗ₖ (N ^ n) := by
    intro n
    induction n with
    | zero =>
        intro w
        simp [branchWordProd]
    | succ k ih =>
        intro w
        rw [word_cons (fun a => T a ⊗ₖ N) w,
          ih (fun i => w i.succ), word_cons T w,
          ← Matrix.mul_kronecker_mul, ← pow_succ']
  have hNn : ∀ m : ℕ,
      (N ^ m) *ᵥ (fun _ => (1 : ℝ)) = fun _ => 1 := by
    intro m
    induction m with
    | zero => rw [pow_zero, Matrix.one_mulVec]
    | succ k ih =>
        rw [pow_succ', ← Matrix.mulVec_mulVec, ih, hN]
  intro n w
  unfold branchCylP
  rw [hword w]
  have hβ1 : (∑ y : L, β y) = 1 := by
    simpa [dotProduct] using hβ
  have hvec : ((branchWordProd T w ⊗ₖ (N ^ n))
      *ᵥ fun _ : d × L => (1 : ℝ))
      = fun q : d × L =>
          (branchWordProd T w *ᵥ fun _ => 1) q.1 := by
    funext q
    have hrow : (∑ y : L, (N ^ n) q.2 y) = 1 := by
      have h := congrFun (hNn n) q.2
      simpa [Matrix.mulVec, dotProduct] using h
    simp only [Matrix.mulVec, dotProduct,
      Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
      mul_one]
    rw [← Finset.sum_mul_sum, hrow, mul_one]
  rw [hvec]
  simp only [dotProduct, Fintype.sum_prod_type]
  have hsplit : ∀ (u : d → ℝ) (v : L → ℝ) (g : d → ℝ),
      (∑ x : d, ∑ y : L, u x * v y * g x)
        = (∑ x, u x * g x) * ∑ y, v y := by
    intro u v g
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun x _ =>
      Finset.sum_congr rfl fun y _ => by ring
  rw [hsplit, hβ1, mul_one]

end NCG
