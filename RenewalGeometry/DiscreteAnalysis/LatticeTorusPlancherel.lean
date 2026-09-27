/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Discrete Fourier transform on the lattice torus `(ℤ/nℤ)^d` with Plancherel

The `d`-dimensional characters `e(ℓ·x) = ∏_μ e(ℓ_μ x_μ)` (`latticeChar`) of the grid
`Grid d n = (ℤ/nℤ)^d`, their orthogonality (`sum_latticeChar`), the normalised DFT
`û(ℓ) = n⁻ᵈ Σ_x e(-ℓ·x) u(x)` (`dft`) of functions with values in a complex inner product
space, Parseval's identity (`sum_norm_dft_sq`), the shift multipliers
(`dft_shift`, `dft_shiftAdj`: a coordinate shift becomes multiplication by `e(ℓ_j)`), and the
componentwise transform of `ℂ^N`-valued sections (`dftVec`) with its Parseval identity for
the Euclidean norm (`sum_euclNormSq_dftVec`) and matrix-multiplier rule (`dftVec_matMul`).

This generalises the four-dimensional transform of `NodalRoundingTailExact` to every
dimension; it is used for the frozen discrete Gårding estimate of
`thm:supp-general-Wilson-ellipticity` (paper `predictive_spectral_geometry`).
-/

open Finset ZMod ComplexConjugate Matrix

namespace RenewalGeometry.LatticeTorusPlancherel

/-- The periodic `d`-dimensional grid with `n` nodes per direction. -/
abbrev Grid (d n : ℕ) := Fin d → ZMod n

variable {d n : ℕ} [NeZero n]

/-! ### Characters -/

/-- The character `e(ℓ·x) = ∏_μ e(ℓ_μ x_μ)`. -/
noncomputable def latticeChar (ℓ x : Grid d n) : ℂ := ∏ μ, stdAddChar (ℓ μ * x μ)

theorem latticeChar_comm (ℓ x : Grid d n) : latticeChar ℓ x = latticeChar x ℓ := by
  simp [latticeChar, mul_comm]

theorem latticeChar_zero_right (ℓ : Grid d n) : latticeChar ℓ 0 = 1 := by
  simp [latticeChar]

theorem latticeChar_add_right (ℓ x y : Grid d n) :
    latticeChar ℓ (x + y) = latticeChar ℓ x * latticeChar ℓ y := by
  simp [latticeChar, mul_add, AddChar.map_add_eq_mul, prod_mul_distrib]

theorem latticeChar_neg_right (ℓ x : Grid d n) : latticeChar ℓ (-x) = conj (latticeChar ℓ x) := by
  unfold latticeChar
  rw [map_prod]
  refine prod_congr rfl fun μ _ => ?_
  rw [Pi.neg_apply, mul_neg, AddChar.map_neg_eq_inv, stdAddChar_apply, ← Circle.coe_inv,
    Circle.coe_inv_eq_conj]

theorem latticeChar_sub_right (ℓ x y : Grid d n) :
    latticeChar ℓ (x - y) = latticeChar ℓ x * conj (latticeChar ℓ y) := by
  rw [sub_eq_add_neg, latticeChar_add_right, latticeChar_neg_right]

/-- The character of the unit step `e_j` is `e(ℓ_j)`. -/
theorem latticeChar_single (ℓ : Grid d n) (j : Fin d) :
    latticeChar ℓ (Pi.single j 1) = stdAddChar (ℓ j) := by
  unfold latticeChar
  rw [Finset.prod_eq_single j]
  · simp
  · intro μ _ hμ
    simp [hμ]
  · intro h
    exact absurd (mem_univ j) h

/-- One-dimensional character orthogonality on `ZMod n`. -/
theorem sum_stdAddChar_mul (t : ZMod n) :
    ∑ i : ZMod n, stdAddChar (i * t) = if t = 0 then (n : ℂ) else 0 := by
  have h' : ∀ i : ZMod n, stdAddChar (i * t) = stdAddChar (t * i) := fun i => by rw [mul_comm]
  simp_rw [h']
  split_ifs with h
  · simp [h, card_univ, ZMod.card]
  · exact AddChar.sum_eq_zero_of_ne_one (isPrimitive_stdAddChar n h)

/-- `d`-dimensional character orthogonality: `Σ_ℓ e(ℓ·x) = n^d [x = 0]`. -/
theorem sum_latticeChar (x : Grid d n) :
    ∑ ℓ : Grid d n, latticeChar ℓ x = if x = 0 then ((n : ℂ) ^ d) else 0 := by
  unfold latticeChar
  have hprod := Finset.prod_univ_sum (fun _ : Fin d => (univ : Finset (ZMod n)))
    (fun μ (k : ZMod n) => stdAddChar (k * x μ))
  rw [Fintype.piFinset_univ] at hprod
  rw [← hprod]
  simp_rw [sum_stdAddChar_mul]
  by_cases hx : x = 0
  · subst hx
    simp
  · obtain ⟨μ, hμ⟩ : ∃ μ, x μ ≠ 0 := by
      by_contra hc
      push Not at hc
      exact hx (funext hc)
    rw [ite_eq_right_iff.mpr (fun h => absurd h hx)]
    exact prod_eq_zero (mem_univ μ) (by simp [hμ])

/-! ### The normalised DFT and Parseval -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The normalised DFT `û(ℓ) = n⁻ᵈ Σ_x e(-ℓ·x) u(x)`. -/
noncomputable def dft (u : Grid d n → E) (ℓ : Grid d n) : E :=
  ((n : ℂ) ^ d)⁻¹ • ∑ x, conj (latticeChar ℓ x) • u x

theorem dft_add (u v : Grid d n → E) (ℓ : Grid d n) : dft (u + v) ℓ = dft u ℓ + dft v ℓ := by
  simp [dft, smul_add, sum_add_distrib]

theorem dft_sub (u v : Grid d n → E) (ℓ : Grid d n) : dft (u - v) ℓ = dft u ℓ - dft v ℓ := by
  simp [dft, smul_sub, sum_sub_distrib]

theorem dft_smul (c : ℂ) (u : Grid d n → E) (ℓ : Grid d n) : dft (c • u) ℓ = c • dft u ℓ := by
  simp only [dft, Pi.smul_apply, Finset.smul_sum, smul_smul]
  refine sum_congr rfl fun x _ => ?_
  congr 1
  ring

theorem dft_sum {ι : Type*} (s : Finset ι) (f : ι → Grid d n → E) (ℓ : Grid d n) :
    dft (fun x => ∑ k ∈ s, f k x) ℓ = ∑ k ∈ s, dft (f k) ℓ := by
  simp only [dft, smul_sum, sum_comm (s := univ) (t := s)]

theorem inner_dft_self (u : Grid d n → E) (ℓ : Grid d n) :
    inner ℂ (dft u ℓ) (dft u ℓ) =
      (((n : ℂ) ^ d)⁻¹) ^ 2 * ∑ x, ∑ y, latticeChar ℓ (x - y) * inner ℂ (u x) (u y) := by
  unfold dft
  simp only [inner_smul_left, inner_smul_right, sum_inner, inner_sum, latticeChar_sub_right,
    map_inv₀, map_pow, map_natCast, Complex.conj_conj, mul_sum]
  conv_lhs => rw [sum_comm]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
  ring

theorem sum_inner_dft_self (u : Grid d n → E) :
    ∑ ℓ, inner ℂ (dft u ℓ) (dft u ℓ) = ((n : ℂ) ^ d)⁻¹ * ∑ x, inner ℂ (u x) (u x) := by
  have hn : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  simp_rw [inner_dft_self]
  rw [← mul_sum, sum_comm]
  have hswap : ∀ x : Grid d n, ∑ ℓ : Grid d n, ∑ y, latticeChar ℓ (x - y) * inner ℂ (u x) (u y) =
      ∑ y, (∑ ℓ : Grid d n, latticeChar ℓ (x - y)) * inner ℂ (u x) (u y) := by
    intro x
    rw [sum_comm]
    simp_rw [sum_mul]
  simp only [hswap, sum_latticeChar, sub_eq_zero, ite_mul, zero_mul, sum_ite_eq, mem_univ,
    ite_true]
  rw [← mul_sum]
  field_simp

/-- **Parseval's identity** for the normalised DFT: `Σ_ℓ ‖û(ℓ)‖² = n⁻ᵈ Σ_x ‖u(x)‖²`. -/
theorem sum_norm_dft_sq (u : Grid d n → E) :
    ∑ ℓ, ‖dft u ℓ‖ ^ 2 = ((n : ℝ) ^ d)⁻¹ * ∑ x, ‖u x‖ ^ 2 := by
  have h := sum_inner_dft_self u
  simp_rw [inner_self_eq_norm_sq_to_K] at h
  apply Complex.ofReal_injective
  push_cast
  exact h

/-! ### Shift multipliers -/

/-- The coordinate shift `(S_j u)(x) = u(x + e_j)`. -/
def shift (j : Fin d) (u : Grid d n → E) : Grid d n → E := fun x => u (x + Pi.single j 1)

/-- The adjoint shift `(S_j^* u)(x) = u(x - e_j)`. -/
def shiftAdj (j : Fin d) (u : Grid d n → E) : Grid d n → E := fun x => u (x - Pi.single j 1)

/-- A coordinate shift is the Fourier multiplier `e(ℓ_j)`. -/
theorem dft_shift (u : Grid d n → E) (j : Fin d) (ℓ : Grid d n) :
    dft (shift j u) ℓ = stdAddChar (ℓ j) • dft u ℓ := by
  have hre : ∑ x, conj (latticeChar ℓ x) • u (x + Pi.single j 1) =
      stdAddChar (ℓ j) • ∑ x, conj (latticeChar ℓ x) • u x := by
    rw [Finset.smul_sum]
    refine (Fintype.sum_equiv (Equiv.addRight (Pi.single j 1 : Grid d n)) _
      (fun y => conj (latticeChar ℓ (y - Pi.single j 1)) • u y) (fun x => by simp)).trans ?_
    refine sum_congr rfl fun y _ => ?_
    rw [latticeChar_sub_right, map_mul, Complex.conj_conj, latticeChar_single, mul_comm,
      mul_smul]
  unfold dft shift
  rw [hre, smul_comm]

/-- The adjoint shift is the Fourier multiplier `e(-ℓ_j) = conj e(ℓ_j)`. -/
theorem dft_shiftAdj (u : Grid d n → E) (j : Fin d) (ℓ : Grid d n) :
    dft (shiftAdj j u) ℓ = conj (stdAddChar (ℓ j)) • dft u ℓ := by
  have hre : ∑ x, conj (latticeChar ℓ x) • u (x - Pi.single j 1) =
      conj (stdAddChar (ℓ j)) • ∑ x, conj (latticeChar ℓ x) • u x := by
    rw [Finset.smul_sum]
    refine (Fintype.sum_equiv (Equiv.subRight (Pi.single j 1 : Grid d n)) _
      (fun y => conj (latticeChar ℓ (y + Pi.single j 1)) • u y) (fun x => by simp)).trans ?_
    refine sum_congr rfl fun y _ => ?_
    rw [latticeChar_add_right, map_mul, latticeChar_single, mul_comm, mul_smul]
  unfold dft shiftAdj
  rw [hre, smul_comm]

/-! ### `ℂ^N`-valued sections -/

variable {N : ℕ}

/-- The Euclidean square norm `Σ_i |v_i|²` on `ℂ^N`. -/
noncomputable def euclNormSq (v : Fin N → ℂ) : ℝ := ∑ i, ‖v i‖ ^ 2

theorem euclNormSq_nonneg (v : Fin N → ℂ) : 0 ≤ euclNormSq v :=
  sum_nonneg fun _ _ => sq_nonneg _

theorem euclNormSq_smul (c : ℂ) (v : Fin N → ℂ) : euclNormSq (c • v) = ‖c‖ ^ 2 * euclNormSq v := by
  simp [euclNormSq, mul_pow, Finset.mul_sum]

/-- The componentwise DFT of a `ℂ^N`-valued section. -/
noncomputable def dftVec (u : Grid d n → (Fin N → ℂ)) (ℓ : Grid d n) : Fin N → ℂ :=
  fun i => dft (fun x => u x i) ℓ

theorem dftVec_add (u v : Grid d n → (Fin N → ℂ)) (ℓ : Grid d n) :
    dftVec (u + v) ℓ = dftVec u ℓ + dftVec v ℓ := by
  funext i
  exact dft_add (fun x => u x i) (fun x => v x i) ℓ

theorem dftVec_sub (u v : Grid d n → (Fin N → ℂ)) (ℓ : Grid d n) :
    dftVec (u - v) ℓ = dftVec u ℓ - dftVec v ℓ := by
  funext i
  exact dft_sub (fun x => u x i) (fun x => v x i) ℓ

theorem dftVec_smul (c : ℂ) (u : Grid d n → (Fin N → ℂ)) (ℓ : Grid d n) :
    dftVec (c • u) ℓ = c • dftVec u ℓ := by
  funext i
  exact dft_smul c (fun x => u x i) ℓ

theorem dftVec_shift (u : Grid d n → (Fin N → ℂ)) (j : Fin d) (ℓ : Grid d n) :
    dftVec (shift j u) ℓ = stdAddChar (ℓ j) • dftVec u ℓ := by
  funext i
  exact dft_shift (fun x => u x i) j ℓ

theorem dftVec_shiftAdj (u : Grid d n → (Fin N → ℂ)) (j : Fin d) (ℓ : Grid d n) :
    dftVec (shiftAdj j u) ℓ = conj (stdAddChar (ℓ j)) • dftVec u ℓ := by
  funext i
  exact dft_shiftAdj (fun x => u x i) j ℓ

theorem dftVec_sum {ι : Type*} (s : Finset ι) (f : ι → Grid d n → (Fin N → ℂ)) (ℓ : Grid d n) :
    dftVec (fun x => ∑ k ∈ s, f k x) ℓ = ∑ k ∈ s, dftVec (f k) ℓ := by
  funext i
  simp only [dftVec, Finset.sum_apply]
  exact dft_sum s (fun k x => f k x i) ℓ

/-- A constant matrix commutes with the componentwise DFT. -/
theorem dftVec_matMul (M : Matrix (Fin N) (Fin N) ℂ) (u : Grid d n → (Fin N → ℂ)) (ℓ : Grid d n) :
    dftVec (fun x => M *ᵥ u x) ℓ = M *ᵥ dftVec u ℓ := by
  funext i
  simp only [dftVec, Matrix.mulVec, dotProduct]
  rw [dft_sum univ (fun k x => M i k * u x k) ℓ]
  refine sum_congr rfl fun k _ => ?_
  exact dft_smul (M i k) (fun x => u x k) ℓ

/-- **Parseval for `ℂ^N`-valued sections**: `Σ_ℓ |û(ℓ)|² = n⁻ᵈ Σ_x |u(x)|²`. -/
theorem sum_euclNormSq_dftVec (u : Grid d n → (Fin N → ℂ)) :
    ∑ ℓ, euclNormSq (dftVec u ℓ) = ((n : ℝ) ^ d)⁻¹ * ∑ x, euclNormSq (u x) := by
  calc ∑ ℓ, euclNormSq (dftVec u ℓ) = ∑ i, ∑ ℓ, ‖dft (fun x => u x i) ℓ‖ ^ 2 := by
        unfold euclNormSq dftVec
        exact Finset.sum_comm
    _ = ∑ i, ((n : ℝ) ^ d)⁻¹ * ∑ x, ‖u x i‖ ^ 2 := sum_congr rfl fun i _ => sum_norm_dft_sq _
    _ = ((n : ℝ) ^ d)⁻¹ * ∑ x, euclNormSq (u x) := by
        unfold euclNormSq
        simp only [Finset.mul_sum]
        exact Finset.sum_comm

end RenewalGeometry.LatticeTorusPlancherel
