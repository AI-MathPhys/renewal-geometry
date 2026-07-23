/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The graded Clifford commutator form and its Gram matrix

The **graded Clifford renewal memory**
(Construction `constr:graded-clifford-memory`) generates its projective
revision law from anticommuting reset generators.  This file proves the two
computational pillars of Lemma `lem:graded-clifford-form` and Theorem
`thm:intrinsic-graded-clifford-datum`:

* **generator exchange calculus**: moving a generator across a product of
  `k` distinct anticommuting generators costs `(−1)^k`
  (`NCG.gen_mul_prod`), and products over disjoint index lists exchange
  with the bilinear sign `(−1)^{k₁k₂}` (`NCG.prod_mul_prod_disjoint`) —
  the commutator form `ω(α,β) = |α||β| − |α∩β|` on disjoint supports;
* **the Gram matrix** `Ω = Jₙ − Iₙ` of the generator basis (all-ones off
  the diagonal, zero on it) is **invertible over `𝔽₂` exactly when `n` is
  even**: for even `n` it is an involution (`NCG.gramMatrix_sq`), for odd
  `n` the all-ones vector lies in its kernel
  (`NCG.gramMatrix_not_isUnit_of_odd`).  This is the rank computation that
  makes the rank-`(1+d)` revision block primitive precisely for odd
  spatial rank `d` — the `3+1` pattern `Ω = J₄ − I₄` being the minimal
  nondegenerate instance.
-/

namespace NCG

/-! ### Generator exchange calculus -/

section Generators

variable {A : Type*} [Ring A] {ι : Type*} [DecidableEq ι] (γ : ι → A)

omit [DecidableEq ι] in
/-- Moving a generator across a product of `k` distinct anticommuting
generators costs `(−1)^k` (Lemma `lem:graded-clifford-form`, single-move
case). -/
theorem gen_mul_prod
    (hanti : ∀ i j, i ≠ j → γ i * γ j = -(γ j * γ i))
    (j : ι) : ∀ (l : List ι), j ∉ l →
    γ j * (l.map γ).prod = ((-1 : ℤ) ^ l.length) • ((l.map γ).prod * γ j)
  | [], _ => by simp
  | i :: l, hj => by
      have hij : j ≠ i := fun h => hj (h ▸ List.mem_cons_self ..)
      have hj' : j ∉ l := fun h => hj (List.mem_cons_of_mem i h)
      have ih := gen_mul_prod hanti j l hj'
      simp only [List.map_cons, List.prod_cons, List.length_cons]
      calc γ j * (γ i * (l.map γ).prod)
          = (γ j * γ i) * (l.map γ).prod := by rw [mul_assoc]
        _ = -((γ i * γ j) * (l.map γ).prod) := by
            rw [hanti j i hij, neg_mul]
        _ = -(γ i * (γ j * (l.map γ).prod)) := by rw [mul_assoc]
        _ = -(γ i * (((-1 : ℤ) ^ l.length)
              • ((l.map γ).prod * γ j))) := by rw [ih]
        _ = (-((-1 : ℤ) ^ l.length))
              • (γ i * ((l.map γ).prod * γ j)) := by
            rw [mul_smul_comm, neg_smul]
        _ = ((-1 : ℤ) ^ (l.length + 1))
              • ((γ i * (l.map γ).prod) * γ j) := by
            rw [mul_assoc]
            congr 1
            rw [pow_succ]
            ring

omit [DecidableEq ι] in
/-- **Bilinear exchange sign on disjoint supports**
(Lemma `lem:graded-clifford-form`): products of anticommuting generators
over disjoint index lists exchange with the sign `(−1)^{k₁·k₂}` — the
`𝔽₂`-bilinear commutator form of the graded Clifford memory, whose Gram
matrix on the generator basis is `Ω = Jₙ − Iₙ`. -/
theorem prod_mul_prod_disjoint
    (hanti : ∀ i j, i ≠ j → γ i * γ j = -(γ j * γ i)) :
    ∀ (l₁ l₂ : List ι), (∀ x ∈ l₁, x ∉ l₂) →
    (l₁.map γ).prod * (l₂.map γ).prod
      = ((-1 : ℤ) ^ (l₁.length * l₂.length))
          • ((l₂.map γ).prod * (l₁.map γ).prod)
  | [], l₂, _ => by simp
  | j :: l₁, l₂, hdisj => by
      have hj : j ∉ l₂ := hdisj j (List.mem_cons_self ..)
      have hdisj' : ∀ x ∈ l₁, x ∉ l₂ := fun x hx =>
        hdisj x (List.mem_cons_of_mem j hx)
      have ih := prod_mul_prod_disjoint hanti l₁ l₂ hdisj'
      simp only [List.map_cons, List.prod_cons, List.length_cons]
      calc (γ j * (l₁.map γ).prod) * (l₂.map γ).prod
          = γ j * ((l₁.map γ).prod * (l₂.map γ).prod) := by rw [mul_assoc]
        _ = γ j * (((-1 : ℤ) ^ (l₁.length * l₂.length))
              • ((l₂.map γ).prod * (l₁.map γ).prod)) := by rw [ih]
        _ = ((-1 : ℤ) ^ (l₁.length * l₂.length))
              • ((γ j * (l₂.map γ).prod) * (l₁.map γ).prod) := by
            rw [mul_smul_comm, mul_assoc]
        _ = ((-1 : ℤ) ^ (l₁.length * l₂.length))
              • ((((-1 : ℤ) ^ l₂.length)
                  • ((l₂.map γ).prod * γ j)) * (l₁.map γ).prod) := by
            rw [gen_mul_prod γ hanti j l₂ hj]
        _ = ((-1 : ℤ) ^ ((l₁.length + 1) * l₂.length))
              • ((l₂.map γ).prod * (γ j * (l₁.map γ).prod)) := by
            rw [smul_mul_assoc, smul_smul, mul_assoc]
            congr 1
            rw [← pow_add]
            congr 1
            ring

end Generators

/-! ### The Gram matrix `Ω = Jₙ − Iₙ` over `𝔽₂` -/

open Matrix

/-- The all-ones matrix `Jₙ` over `𝔽₂`. -/
def allOnes (n : ℕ) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  Matrix.of fun _ _ => 1

/-- The **Gram matrix of the graded Clifford generator basis**:
`Ω = Jₙ − Iₙ = Jₙ + Iₙ` over `𝔽₂` — ones off the diagonal, zero on it
(Lemma `lem:graded-clifford-form`). -/
def gramMatrix (n : ℕ) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  allOnes n + 1

theorem allOnes_mul_allOnes (n : ℕ) :
    allOnes n * allOnes n = (n : ZMod 2) • allOnes n := by
  ext i j
  simp [allOnes, Matrix.mul_apply, Finset.sum_const, nsmul_eq_mul]

/-- **The even case** (Theorem `thm:intrinsic-graded-clifford-datum`): for
even `n` the Gram matrix is an involution, `Ω² = 1`, hence invertible: the
rank-`n` revision block is primitive.  For `n = 4` this is the minimal
nondegenerate `3+1` pattern `Ω = J₄ − I₄`. -/
theorem gramMatrix_sq {n : ℕ} (hn : Even n) :
    gramMatrix n * gramMatrix n = 1 := by
  have hJJ : allOnes n * allOnes n = 0 := by
    rw [allOnes_mul_allOnes]
    have hcast : (n : ZMod 2) = 0 :=
      (ZMod.natCast_eq_zero_iff n 2).mpr hn.two_dvd
    rw [hcast, zero_smul]
  have hJJ2 : allOnes n + allOnes n = 0 := by
    ext i j
    simp [CharTwo.add_self_eq_zero]
  calc gramMatrix n * gramMatrix n
      = allOnes n * allOnes n + (allOnes n + allOnes n) + 1 := by
        rw [gramMatrix]
        noncomm_ring
    _ = 1 := by rw [hJJ, hJJ2]; simp

/-- The Gram matrix is invertible for even rank. -/
theorem gramMatrix_isUnit {n : ℕ} (hn : Even n) : IsUnit (gramMatrix n) :=
  ⟨⟨gramMatrix n, gramMatrix n, gramMatrix_sq hn, gramMatrix_sq hn⟩, rfl⟩

/-- **The odd case** (Theorem `thm:intrinsic-graded-clifford-datum`,
degenerate branch): for odd `n` the all-ones vector lies in the kernel of
`Ω = Jₙ − Iₙ`, so the Gram matrix is singular and the rank-`n` block is
not primitive — even total rank, hence odd spatial rank, is forced. -/
theorem gramMatrix_not_isUnit_of_odd {n : ℕ} (hn : Odd n) (hpos : 0 < n) :
    ¬IsUnit (gramMatrix n) := by
  intro h
  have hcast : (n : ZMod 2) = 1 := by
    obtain ⟨k, hk⟩ := hn
    subst hk
    push_cast
    simp [CharTwo.two_eq_zero]
  have hones : gramMatrix n *ᵥ (fun _ => (1 : ZMod 2)) = 0 := by
    ext i
    rw [gramMatrix, Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply]
    simp only [Matrix.mulVec, dotProduct, allOnes, Matrix.of_apply,
      mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Pi.zero_apply, hcast]
    decide
  obtain ⟨U, hU⟩ := h
  have h2 := congrArg (fun v => (↑U⁻¹ : Matrix (Fin n) (Fin n) (ZMod 2))
    *ᵥ v) hones
  simp only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] at h2
  rw [show (↑U⁻¹ : Matrix (Fin n) (Fin n) (ZMod 2)) * gramMatrix n = 1 by
    rw [← hU]; exact U.inv_mul] at h2
  have h3 := congrFun h2 ⟨0, hpos⟩
  simp [Matrix.one_mulVec] at h3

end NCG
