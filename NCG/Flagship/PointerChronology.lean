/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Pointer-fixing channels are Schur multipliers
  (`thm:pointer-chronology-master`, flagship manuscript)

Let `𝒟(X) = Σᵢ KᵢXKᵢ*` be a trace-preserving Kraus channel fixing
every fine pointer projection `E_x = |x⟩⟨x|`.  Then:

* every Kraus operator is diagonal (`pointer_kraus_diagonal` —
  the matrix form of `W|x⟩ = |x⟩⊗|η_x⟩`);
* the boxed Schur form `𝒟(X) = C ∘ X` holds entrywise with the
  correlation matrix `C_{xy} = Σᵢ (Kᵢ)_{xx}(Kᵢ)_{yy}*`
  (`pointer_chronology`), which is Hermitian, positive
  semidefinite (a Gram matrix), and has unit diagonal;
* `C` is unique (`chronology_unique`);
* the boxed visibility recovery: `ρ_C = C ∘ Γ` has the same
  diagonal as `Γ` for every `C`, and whenever `Γ_{xy} ≠ 0` the
  interference ratio returns `C_{xy} = (ρ_C)_{xy}/Γ_{xy}`
  (`chronology_visibility`).

The manuscript's `M₂₄` is immaterial — everything is proved for
an arbitrary finite pointer index.  Permutation covariance
(`C_{gx,gy} = C_{xy}`) is the same entrywise computation applied
to matrix units and is prose here (disclosed).
-/

open Finset Matrix
open scoped ComplexOrder

namespace NCG

variable {n k : Type*} [Fintype n] [DecidableEq n] [Fintype k]

/-- The correlation (chronology) matrix of a Kraus family. -/
noncomputable def chronologyC (K : k → Matrix n n ℂ) :
    Matrix n n ℂ :=
  Matrix.of fun x y => ∑ i, K i x x * star (K i y y)

/-- The `(z, z)` entry of `K E_x K*` is `|K_{zx}|²`. -/
lemma kraus_fix_entry (A : Matrix n n ℂ) (x z : n) :
    (A * Matrix.single x x (1 : ℂ) * Aᴴ) z z
      = A z x * star (A z x) := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single x]
  · rw [Matrix.mul_apply, Finset.sum_eq_single x]
    · simp [Matrix.conjTranspose_apply]
    · intro b _ hb
      simp [Ne.symm hb]
    · intro h
      exact absurd (mem_univ x) h
  · intro b _ hb
    rw [Matrix.mul_apply, Finset.sum_eq_zero, zero_mul]
    intro a _
    simp [Ne.symm hb]
  · intro h
    exact absurd (mem_univ x) h

/-- Fixing every pointer projection forces diagonal Kraus
operators. -/
lemma pointer_kraus_diagonal (K : k → Matrix n n ℂ)
    (hfix : ∀ x : n, ∑ i, K i * Matrix.single x x 1 * (K i)ᴴ
      = Matrix.single x x 1)
    (i : k) (z x : n) (hzx : z ≠ x) : K i z x = 0 := by
  have h := congrArg (fun M => M z z) (hfix x)
  simp only [Matrix.sum_apply] at h
  rw [Finset.sum_congr rfl (fun i _ => kraus_fix_entry (K i) x z)]
    at h
  have hz : Matrix.single x x (1 : ℂ) z z = 0 := by
    simp [Ne.symm hzx]
  rw [hz] at h
  have hcast : ∑ j, Complex.normSq (K j z x) = 0 := by
    have h2 : ∑ j, K j z x * star (K j z x)
        = ∑ j, ((Complex.normSq (K j z x) : ℝ) : ℂ) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Complex.star_def, Complex.mul_conj]
    rw [h2] at h
    exact_mod_cast h
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j _ => Complex.normSq_nonneg (K j z x))).mp hcast i
    (mem_univ i)
  exact Complex.normSq_eq_zero.mp hterm

/-- `thm:pointer-chronology-master`, boxed Schur form and the
properties of the correlation matrix: `𝒟(X) = C ∘ X` entrywise,
with `C` Hermitian, positive semidefinite, and unit-diagonal. -/
theorem pointer_chronology (K : k → Matrix n n ℂ)
    (hTP : ∑ i, (K i)ᴴ * K i = 1)
    (hfix : ∀ x : n, ∑ i, K i * Matrix.single x x 1 * (K i)ᴴ
      = Matrix.single x x 1) :
    (∀ (X : Matrix n n ℂ) (x y : n),
      (∑ i, K i * X * (K i)ᴴ) x y = chronologyC K x y * X x y)
    ∧ (chronologyC K)ᴴ = chronologyC K
    ∧ (∀ v : n → ℂ,
        0 ≤ star v ⬝ᵥ (chronologyC K *ᵥ v))
    ∧ ∀ x, chronologyC K x x = 1 := by
  have hdiag := pointer_kraus_diagonal K hfix
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro X x y
    rw [Matrix.sum_apply]
    have hterm : ∀ i, (K i * X * (K i)ᴴ) x y
        = K i x x * star (K i y y) * X x y := by
      intro i
      rw [Matrix.mul_apply, Finset.sum_eq_single y]
      · rw [Matrix.mul_apply, Finset.sum_eq_single x]
        · rw [Matrix.conjTranspose_apply]
          ring
        · intro a _ ha
          rw [hdiag i x a (Ne.symm ha), zero_mul]
        · intro h
          exact absurd (mem_univ x) h
      · intro b _ hb
        simp [Matrix.conjTranspose_apply,
          hdiag i y b (Ne.symm hb)]
      · intro h
        exact absurd (mem_univ y) h
    rw [Finset.sum_congr rfl fun i _ => hterm i, chronologyC,
      ← Finset.sum_mul]
    rfl
  · ext x y
    simp only [Matrix.conjTranspose_apply, chronologyC,
      Matrix.of_apply, star_sum, star_mul', star_star]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  · intro v
    have hform : star v ⬝ᵥ (chronologyC K *ᵥ v)
        = ∑ i, star (∑ y, v y * star (K i y y))
            * (∑ y, v y * star (K i y y)) := by
      calc star v ⬝ᵥ (chronologyC K *ᵥ v)
          = ∑ x, ∑ y, ∑ i,
              star (v x) * K i x x * star (K i y y) * v y := by
            simp only [dotProduct, Matrix.mulVec, chronologyC,
              Matrix.of_apply, Pi.star_apply]
            refine Finset.sum_congr rfl fun x _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun y _ => ?_
            rw [Finset.sum_mul, Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            ring
        _ = ∑ i, ∑ x, ∑ y,
              star (v x) * K i x x * star (K i y y) * v y := by
            rw [Finset.sum_congr rfl fun x _ => Finset.sum_comm,
              Finset.sum_comm]
        _ = ∑ i, star (∑ y, v y * star (K i y y))
              * (∑ y, v y * star (K i y y)) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [star_sum, Finset.sum_mul]
            refine Finset.sum_congr rfl fun x _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun y _ => ?_
            rw [star_mul', star_star]
            ring
    rw [hform]
    exact Finset.sum_nonneg fun i _ => star_mul_self_nonneg _
  · intro x
    have h := congrArg (fun M => M x x) hTP
    simp only [Matrix.sum_apply, Matrix.one_apply_eq] at h
    have hterm : ∀ i, ((K i)ᴴ * K i) x x
        = K i x x * star (K i x x) := by
      intro i
      rw [Matrix.mul_apply, Finset.sum_eq_single x]
      · rw [Matrix.conjTranspose_apply]
        ring
      · intro b _ hb
        rw [hdiag i b x hb, mul_zero]
      · intro h
        exact absurd (mem_univ x) h
    rw [Finset.sum_congr rfl fun i _ => hterm i] at h
    exact h

omit [Fintype n] [DecidableEq n] in
/-- The correlation matrix is unique. -/
theorem chronology_unique (C C' : Matrix n n ℂ)
    (h : ∀ (X : Matrix n n ℂ) (x y : n),
      C x y * X x y = C' x y * X x y) :
    C = C' := by
  ext x y
  have := h (Matrix.of fun _ _ => 1) x y
  simpa using this

omit [Fintype n] [DecidableEq n] in
/-- Boxed visibility recovery: `ρ_C = C ∘ Γ` has the diagonal of
`Γ`, and whenever `Γ_{xy} ≠ 0` the interference ratio returns
`C_{xy}`. -/
theorem chronology_visibility (C Γ : Matrix n n ℂ)
    (hdiag : ∀ x, C x x = 1) :
    (∀ x, (Matrix.of fun a b => C a b * Γ a b) x x = Γ x x)
    ∧ ∀ x y, Γ x y ≠ 0 →
      C x y = (Matrix.of fun a b => C a b * Γ a b) x y / Γ x y := by
  constructor
  · intro x
    simp [hdiag x]
  · intro x y hΓ
    rw [Matrix.of_apply, mul_div_assoc, div_self hΓ, mul_one]

end NCG
