/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Interface gluing, layer stripping, transport, and audits
  (`thm:interface-gluing`, `thm:matrix-continued-fraction`,
   `thm:strong-transport`, `lem:SMST-multiplicity-factorization`,
   `thm:SMST-commutant-audit`, `thm:five-parameter-tetrahedral`,
   Gran-Tensor manuscript)

* `interface_gluing`: the solved interface value `u = -H⁻¹(Lx)`
  and the boxed block-determinant identity
  `det [[A,K],[L,H]] = det H · det(A - KH⁻¹L)`;
* `layer_stripping`: the boxed continued-fraction inversion —
  the tail recursion `Λ_k = zI - C - BᴴΛ_{k+1}⁻¹B` with
  invertible `B, Λ_{k+1}` uniquely reconstructs
  `Λ_{k+1} = -B(Λ_k - zI + C)⁻¹Bᴴ`;
* `strong_transport`: a unitary intertwiner transports powers,
  all source moments, and the source Gram exactly — hence every
  finite word identity of the preserved structures;
* `multiplicity_factorization`: if every multiplicity block of
  an equivariant incidence map is a scalar multiple of the fixed
  intertwiner `D` (the one-dimensionality hypothesis), the map
  factors as `Y = D ⊗ F`;
* `commutant_audit`: the commutator energy vanishes exactly on
  the commutant, is blind to any commuting component
  (`[c_j, X] = [c_j, X - P]`), so the displayed spectral-gap
  bound transfers to the boxed rigidity estimate on `X`;
* `tetrahedral_gram`: `S₄`-invariance forces the five-parameter
  pointed tetrahedral Gram — one anchor pairing, one diagonal,
  and one off-diagonal value (2-transitivity by kernel
  enumeration).

Rendering disclosed: kernel/spectrum transport under the same
unitary is the proved `kernel_dim_conjugation`; the
Redheffer/Herglotz coordinates, the positive-gauge chain
uniqueness, and the tetrahedral positivity criterion are the
remaining interface records.
-/

open Matrix

namespace NCG

/-- `thm:interface-gluing`: the solved interface value and the
boxed block-determinant identity. -/
theorem interface_gluing {e i : Type*} [Fintype e] [Fintype i]
    [DecidableEq e] [DecidableEq i]
    (A : Matrix e e ℂ) (K : Matrix e i ℂ) (L : Matrix i e ℂ)
    (H : Matrix i i ℂ) [Invertible H] (x : e → ℂ) (u : i → ℂ)
    (hsolve : H *ᵥ u + L *ᵥ x = 0) :
    u = -(H⁻¹ *ᵥ (L *ᵥ x))
    ∧ Matrix.det (Matrix.fromBlocks A K L H)
      = Matrix.det H * Matrix.det (A - K * H⁻¹ * L) := by
  constructor
  · have h := congrArg (fun v => H⁻¹ *ᵥ v) hsolve
    simp only [Matrix.mulVec_add, Matrix.mulVec_zero] at h
    rw [Matrix.mulVec_mulVec, Matrix.inv_mul_of_invertible,
      Matrix.one_mulVec] at h
    have h2 := congrArg (fun v => v - H⁻¹ *ᵥ (L *ᵥ x)) h
    simp only [add_sub_cancel_right, zero_sub] at h2
    exact h2
  · rw [Matrix.det_fromBlocks₂₂, Matrix.invOf_eq_nonsing_inv]

/-- `thm:matrix-continued-fraction`: the boxed layer-stripping
inversion — the tail recursion uniquely reconstructs the next
layer. -/
theorem layer_stripping {b : Type*} [Fintype b] [DecidableEq b]
    (Lk Ln C B : Matrix b b ℂ) (z : ℂ)
    [Invertible B] [Invertible Ln]
    (hrec : Lk = z • (1 : Matrix b b ℂ) - C - Bᴴ * Ln⁻¹ * B) :
    Ln = -(B * (Lk - z • (1 : Matrix b b ℂ) + C)⁻¹ * Bᴴ) := by
  have hBH : Invertible Bᴴ := Matrix.invertibleConjTranspose B
  have hmid : Lk - z • (1 : Matrix b b ℂ) + C
      = -(Bᴴ * Ln⁻¹ * B) := by
    rw [hrec]
    abel
  have hMinv : (Lk - z • (1 : Matrix b b ℂ) + C)⁻¹
      = -(B⁻¹ * Ln * (Bᴴ)⁻¹) := by
    apply Matrix.inv_eq_right_inv
    rw [hmid, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
    calc Bᴴ * Ln⁻¹ * B * (B⁻¹ * Ln * (Bᴴ)⁻¹)
        = Bᴴ * Ln⁻¹ * (B * B⁻¹) * (Ln * (Bᴴ)⁻¹) := by
          simp only [Matrix.mul_assoc]
      _ = Bᴴ * (Ln⁻¹ * Ln) * (Bᴴ)⁻¹ := by
          rw [Matrix.mul_inv_of_invertible, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [Matrix.inv_mul_of_invertible, Matrix.mul_one,
            Matrix.mul_inv_of_invertible]
  rw [hMinv, Matrix.mul_neg, Matrix.neg_mul, neg_neg]
  refine (?_ : B * (B⁻¹ * Ln * (Bᴴ)⁻¹) * Bᴴ = Ln).symm
  calc B * (B⁻¹ * Ln * (Bᴴ)⁻¹) * Bᴴ
      = (B * B⁻¹) * Ln * ((Bᴴ)⁻¹ * Bᴴ) := by
        simp only [Matrix.mul_assoc]
    _ = Ln := by
        rw [Matrix.mul_inv_of_invertible, Matrix.one_mul,
          Matrix.inv_mul_of_invertible, Matrix.mul_one]

/-- `thm:strong-transport`: a unitary intertwiner transports
powers, all source moments, and the source Gram exactly. -/
theorem strong_transport {n p : Type*} [Fintype n]
    [DecidableEq n]
    (U T T' : Matrix n n ℂ) (S S' : Matrix n p ℂ)
    (hU : Uᴴ * U = 1) (_hU' : U * Uᴴ = 1)
    (hT : U * T = T' * U) (hS : U * S = S') :
    (∀ k : ℕ, U * T ^ k = T' ^ k * U)
    ∧ (∀ k : ℕ, S'ᴴ * T' ^ k * S' = Sᴴ * T ^ k * S)
    ∧ (S'ᴴ * S' = Sᴴ * S) := by
  have hpow : ∀ k : ℕ, U * T ^ k = T' ^ k * U := by
    intro k
    induction k with
    | zero => rw [pow_zero, pow_zero, Matrix.mul_one,
        Matrix.one_mul]
    | succ m ih =>
      rw [pow_succ, pow_succ]
      calc U * (T ^ m * T)
          = (U * T ^ m) * T := by rw [Matrix.mul_assoc]
        _ = T' ^ m * (U * T) := by
            rw [ih, Matrix.mul_assoc]
        _ = T' ^ m * (T' * U) := by rw [hT]
        _ = T' ^ m * T' * U := by rw [Matrix.mul_assoc]
  refine ⟨hpow, ?_, ?_⟩
  · intro k
    rw [← hS, Matrix.conjTranspose_mul]
    calc Sᴴ * Uᴴ * (T' ^ k) * (U * S)
        = Sᴴ * (Uᴴ * (T' ^ k * U)) * S := by
          simp only [Matrix.mul_assoc]
      _ = Sᴴ * (Uᴴ * (U * T ^ k)) * S := by rw [← hpow]
      _ = Sᴴ * ((Uᴴ * U) * T ^ k) * S := by
          simp only [Matrix.mul_assoc]
      _ = Sᴴ * T ^ k * S := by
          rw [hU, Matrix.one_mul, Matrix.mul_assoc]
  · rw [← hS, Matrix.conjTranspose_mul]
    calc Sᴴ * Uᴴ * (U * S)
        = Sᴴ * ((Uᴴ * U) * S) := by
          simp only [Matrix.mul_assoc]
      _ = Sᴴ * S := by rw [hU, Matrix.one_mul]

/-- `lem:SMST-multiplicity-factorization`: one-dimensional
block intertwiner spaces force the factorization
`Y = D ⊗ F`. -/
theorem multiplicity_factorization {n m g g' : Type*}
    (D : Matrix n m ℂ) (Y : Matrix (n × g') (m × g) ℂ)
    (hblock : ∀ a b, ∃ c : ℂ,
      ∀ i j, Y (i, a) (j, b) = c * D i j) :
    ∃ F : Matrix g' g ℂ,
      ∀ i j a b, Y (i, a) (j, b) = D i j * F a b := by
  choose c hc using hblock
  exact ⟨Matrix.of c, fun i j a b => by
    rw [hc a b i j, Matrix.of_apply, mul_comm]⟩

/-- Real part of `tr(Mᴴ M)` as a sum of entry norms. -/
lemma trace_conj_self_re {m n : Type*} [Fintype m] [Fintype n]
    (M : Matrix m n ℂ) :
    ((Mᴴ * M).trace).re
      = ∑ j, ∑ i, Complex.normSq (M i j) := by
  rw [Matrix.trace, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.conjTranspose_apply, Complex.star_def, mul_comm,
    Complex.mul_conj, Complex.ofReal_re]

/-- `tr(Mᴴ M).re = 0` iff `M = 0`. -/
lemma trace_conj_self_re_eq_zero {m n : Type*}
    [Fintype m] [Fintype n] (M : Matrix m n ℂ) :
    ((Mᴴ * M).trace).re = 0 ↔ M = 0 := by
  rw [trace_conj_self_re]
  constructor
  · intro h0
    ext i j
    have hj := (Finset.sum_eq_zero_iff_of_nonneg fun j _ =>
      Finset.sum_nonneg fun i _ =>
        Complex.normSq_nonneg _).mp h0 j (Finset.mem_univ j)
    have hi := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
      Complex.normSq_nonneg _).mp hj i (Finset.mem_univ i)
    simpa using Complex.normSq_eq_zero.mp hi
  · intro h
    rw [h]
    simp

/-- `thm:SMST-commutant-audit`: the commutator energy vanishes
exactly on the commutant, is blind to any commuting component,
and the displayed spectral-gap bound transfers to the boxed
rigidity estimate. -/
theorem commutant_audit {n : Type*} [Fintype n] {s : ℕ}
    (c : Fin s → Matrix n n ℂ) (X P : Matrix n n ℂ)
    (hP : ∀ j, c j * P = P * c j) :
    ((∑ j, (((c j * X - X * c j)ᴴ
        * (c j * X - X * c j)).trace).re) = 0
      ↔ ∀ j, c j * X = X * c j)
    ∧ (∀ j, c j * X - X * c j
        = c j * (X - P) - (X - P) * c j)
    ∧ (∀ lam : ℝ,
        lam * (((X - P)ᴴ * (X - P)).trace).re
          ≤ (∑ j, (((c j * (X - P) - (X - P) * c j)ᴴ
              * (c j * (X - P) - (X - P) * c j)).trace).re)
        → lam * (((X - P)ᴴ * (X - P)).trace).re
          ≤ (∑ j, (((c j * X - X * c j)ᴴ
              * (c j * X - X * c j)).trace).re)) := by
  have hblind : ∀ j, c j * X - X * c j
      = c j * (X - P) - (X - P) * c j := by
    intro j
    rw [Matrix.mul_sub, Matrix.sub_mul, hP j]
    abel
  refine ⟨?_, hblind, ?_⟩
  · constructor
    · intro h0 j
      have hterm := (Finset.sum_eq_zero_iff_of_nonneg
        fun j _ => by
          rw [trace_conj_self_re]
          exact Finset.sum_nonneg fun a _ =>
            Finset.sum_nonneg fun b _ =>
              Complex.normSq_nonneg _).mp h0 j
        (Finset.mem_univ j)
      have := (trace_conj_self_re_eq_zero _).mp hterm
      have hsub := sub_eq_zero.mp this
      exact hsub
    · intro hcomm
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [show c j * X - X * c j = 0 from by
        rw [hcomm j, sub_self]]
      simp
  · intro lam hgap
    refine le_trans hgap (le_of_eq ?_)
    exact Finset.sum_congr rfl fun j _ => by rw [← hblind j]

/-- `thm:five-parameter-tetrahedral`: `S₄`-invariance forces
the five-parameter pointed Gram — one anchor pairing, one
diagonal, and one off-diagonal value. -/
theorem tetrahedral_gram {V : Type*} (P : V → V → ℂ)
    (ξt : V) (ξ : Fin 4 → V)
    (hactP : ∀ g : Equiv.Perm (Fin 4), ∀ i j,
      P (ξ i) (ξ j) = P (ξ (g i)) (ξ (g j)))
    (hactT : ∀ g : Equiv.Perm (Fin 4), ∀ i,
      P ξt (ξ i) = P ξt (ξ (g i))) :
    (∀ i j, P ξt (ξ i) = P ξt (ξ j))
    ∧ (∀ i j, P (ξ i) (ξ i) = P (ξ j) (ξ j))
    ∧ (∀ i j k l, i ≠ j → k ≠ l →
        P (ξ i) (ξ j) = P (ξ k) (ξ l)) := by
  have h2trans : ∀ i j k l : Fin 4, i ≠ j → k ≠ l →
      ∃ g : Equiv.Perm (Fin 4), g i = k ∧ g j = l := by
    decide
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    rw [hactT (Equiv.swap i j) i, Equiv.swap_apply_left]
  · intro i j
    rw [hactP (Equiv.swap i j) i i, Equiv.swap_apply_left]
  · intro i j k l hij hkl
    obtain ⟨g, hgi, hgj⟩ := h2trans i j k l hij hkl
    rw [hactP g i j, hgi, hgj]

end NCG
