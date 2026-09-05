/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Universal block-Hankel exhaustion
  (`thm:universal-Hankel-exhaustion`, Gran-Tensor manuscript)

With the block controllability synthesis
`𝒞 = [S | TS | … | T^{n−1}S]`:

* `universal_hankel_exhaustion`:
  (1) the moment identity: the block entries of `𝒞ᴴ𝒞` are the
      Hankel moments `SᴴT^{i+j}S` (and of `𝒞ᴴT𝒞` the shifted
      moments `SᴴT^{i+j+1}S`) for hermitian `T`;
  (2) the boxed rank identity
      `rank 𝕳^{(0)} = rank 𝒞` (`= dim 𝒦_{R,n}`, the Krylov
      dimension, since rank is the dimension of the range of
      the controllability map by definition).

Rendering disclosed: the Rayleigh-quotient identification of
the generalized radius `q_{R,n}` with the norm of the
compression, and the sup-exhaustion over the dense union, are
the manuscript's spectral/continuity reading of the proved
moment and rank identities (the norm-continuity clause on the
dense union is the declared analytic input).
-/

open Matrix
open scoped ComplexOrder

namespace NCG

/-- The block controllability synthesis
`𝒞 = [S | TS | … | T^{n−1}S]`. -/
noncomputable def blockCtrl {h e : Type*} [Fintype h]
    [DecidableEq h] (T : Matrix h h ℂ) (S : Matrix h e ℂ) (n : ℕ) :
    Matrix h (Fin n × e) ℂ :=
  Matrix.of fun a p => (T ^ (p.1 : ℕ) * S) a p.2

/-- `thm:universal-Hankel-exhaustion`. -/
theorem universal_hankel_exhaustion {h e : Type*} [Fintype h]
    [Fintype e] [DecidableEq h] (T : Matrix h h ℂ) (S : Matrix h e ℂ)
    (hT : Tᴴ = T) (n : ℕ) :
    -- (1) the block moment identities
    (∀ (i j : Fin n) (a b : e),
      ((blockCtrl T S n)ᴴ * blockCtrl T S n) (i, a) (j, b)
        = (Sᴴ * T ^ ((i : ℕ) + (j : ℕ)) * S) a b)
    ∧ (∀ (i j : Fin n) (a b : e),
        ((blockCtrl T S n)ᴴ * T * blockCtrl T S n) (i, a) (j, b)
          = (Sᴴ * T ^ ((i : ℕ) + (j : ℕ) + 1) * S) a b)
    -- (2) the boxed rank identity (Krylov dimension)
    ∧ ((blockCtrl T S n)ᴴ * blockCtrl T S n).rank
        = (blockCtrl T S n).rank := by
  have hTpow : ∀ k : ℕ, (T ^ k)ᴴ = T ^ k := by
    intro k
    rw [Matrix.conjTranspose_pow, hT]
  have hmat : ∀ k l : ℕ,
      (T ^ k * S)ᴴ * (T ^ l * S)
        = Sᴴ * T ^ (k + l) * S := by
    intro k l
    rw [Matrix.conjTranspose_mul, hTpow, pow_add]
    simp only [Matrix.mul_assoc]
  have hTC : T * blockCtrl T S n
      = Matrix.of fun (x : h) (p : Fin n × e) =>
          (T ^ ((p.1 : ℕ) + 1) * S) x p.2 := by
    ext x p
    simp only [blockCtrl, Matrix.of_apply]
    calc (T * Matrix.of fun (y : h) (q : Fin n × e) =>
          (T ^ ((q.1 : ℕ)) * S) y q.2) x p
        = ∑ y, T x y * (T ^ ((p.1 : ℕ)) * S) y p.2 := by
          rw [Matrix.mul_apply]
          rfl
      _ = (T * (T ^ ((p.1 : ℕ)) * S)) x p.2 :=
          (Matrix.mul_apply).symm
      _ = (T ^ ((p.1 : ℕ) + 1) * S) x p.2 := by
          rw [← Matrix.mul_assoc, ← pow_succ']
  refine ⟨?_, ?_, ?_⟩
  · intro i j a b
    have h1 : ((blockCtrl T S n)ᴴ * blockCtrl T S n)
        (i, a) (j, b)
        = ((T ^ (i : ℕ) * S)ᴴ * (T ^ (j : ℕ) * S)) a b := by
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
        blockCtrl, Matrix.of_apply]
    rw [h1, hmat]
  · intro i j a b
    rw [Matrix.mul_assoc, hTC]
    have h1 : ((blockCtrl T S n)ᴴ
        * Matrix.of (fun (x : h) (p : Fin n × e) =>
            (T ^ ((p.1 : ℕ) + 1) * S) x p.2)) (i, a) (j, b)
        = ((T ^ (i : ℕ) * S)ᴴ
            * (T ^ ((j : ℕ) + 1) * S)) a b := by
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
        blockCtrl, Matrix.of_apply]
    rw [h1, hmat, Nat.add_assoc]
  · exact Matrix.rank_conjTranspose_mul_self _

end NCG
