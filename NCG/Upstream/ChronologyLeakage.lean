/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Exact canonical chronology leakage
  (`thm:canonical-chronology-leakage-master`, flagship)

For the three-Read tensor-product chronology `A ⊗ A ⊗ A` evaluated on
the common-depth triple vector `k ⊗ k ⊗ k`, with `α = ⟨k, A k⟩`,
`β = ⟨k, A² k⟩`, `ν = β − α²`:

* `leakage_first_moment` / `leakage_second_moment` — the moments
  factor: `m₁ = α³`, `m₂ = β³`;
* `leakage_variance_polynomial` — `m₂ − m₁² = 3α⁴ν + 3α²ν² + ν³`;
* `leakage_nu_norm` — `ν = ‖(I − |k⟩⟨k|) A k‖²` for Hermitian `A` and
  unit `k`;
* `line_variance_eq_offline_norm` — for a Hermitian projection `P`
  fixing the unit vector `e` with `P M e ∈ ℂ e`, the return variance
  is the off-line norm: `‖Me‖² − |⟨e, Me⟩|² = ‖(I−P)Me‖²`;
* `line_variance_eq_commutator` / `commutator_norm_sq` — with
  `Z = 2P − 1`, `[M, Z] e = 2 (I−P) M e`, so the same quantity is
  `¼‖[M, Z] e‖²`.

The multiplicity-one input (`P M e_vol ∈ ℂ e_vol`, from equivariance
and uniqueness of the determinant line inside the coherent three-Read
support) enters as the hypothesis `hline`, exactly as in the
manuscript proof.
-/

namespace NCG

open Matrix

open scoped Kronecker

noncomputable section

variable {m n N : Type*} [Fintype m] [Fintype n] [Fintype N] [DecidableEq N]

/-! ## Kronecker products of vectors -/

/-- Kronecker (tensor) product of two vectors. -/
def kronVec (a : m → ℂ) (b : n → ℂ) : m × n → ℂ := fun p => a p.1 * b p.2

theorem mulVec_kronVec (A : Matrix m m ℂ) (B : Matrix n n ℂ)
    (a : m → ℂ) (b : n → ℂ) :
    (A ⊗ₖ B) *ᵥ kronVec a b = kronVec (A *ᵥ a) (B *ᵥ b) := by
  ext ⟨i, j⟩
  simp only [Matrix.mulVec, dotProduct, kronVec, kroneckerMap_apply,
    Fintype.sum_prod_type]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem star_kronVec_dotProduct (a c : m → ℂ) (b d : n → ℂ) :
    star (kronVec a b) ⬝ᵥ kronVec c d
      = (star a ⬝ᵥ c) * (star b ⬝ᵥ d) := by
  simp only [dotProduct, kronVec, Pi.star_apply, star_mul',
    Fintype.sum_prod_type]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

/-! ## Moment factorization on the common-depth triple vector -/

variable (A : Matrix n n ℂ) (k : n → ℂ)

/-- The triple tensor power of the depth vector `k`. -/
def tripleVec : (n × n) × n → ℂ := kronVec (kronVec k k) k

/-- The three-Read tensor-product chronology block. -/
def tripleMat : Matrix ((n × n) × n) ((n × n) × n) ℂ := (A ⊗ₖ A) ⊗ₖ A

/-- `thm:canonical-chronology-leakage-master`, first moment:
`m₁ = ⟨k⊗k⊗k, (A⊗A⊗A)(k⊗k⊗k)⟩ = α³`. -/
theorem leakage_first_moment :
    star (tripleVec k) ⬝ᵥ (tripleMat A *ᵥ tripleVec k)
      = (star k ⬝ᵥ (A *ᵥ k)) ^ 3 := by
  simp only [tripleMat, tripleVec]
  rw [mulVec_kronVec, mulVec_kronVec, star_kronVec_dotProduct,
    star_kronVec_dotProduct]
  ring

/-- `thm:canonical-chronology-leakage-master`, second moment:
`m₂ = ⟨k⊗k⊗k, (A⊗A⊗A)²(k⊗k⊗k)⟩ = β³`. -/
theorem leakage_second_moment :
    star (tripleVec k) ⬝ᵥ ((tripleMat A * tripleMat A) *ᵥ tripleVec k)
      = (star k ⬝ᵥ ((A * A) *ᵥ k)) ^ 3 := by
  have hsq : tripleMat A * tripleMat A = tripleMat (A * A) := by
    simp only [tripleMat]
    rw [Matrix.mul_kronecker_mul, Matrix.mul_kronecker_mul]
  rw [hsq]
  simp only [tripleMat, tripleVec]
  rw [mulVec_kronVec, mulVec_kronVec, star_kronVec_dotProduct,
    star_kronVec_dotProduct]
  ring

/-- `thm:canonical-chronology-leakage-master`, variance polynomial:
with `ν = β − α²`, `m₂ − m₁² = β³ − α⁶ = 3α⁴ν + 3α²ν² + ν³`. -/
theorem leakage_variance_polynomial (α β : ℂ) :
    β ^ 3 - (α ^ 3) ^ 2
      = 3 * α ^ 4 * (β - α ^ 2) + 3 * α ^ 2 * (β - α ^ 2) ^ 2
        + (β - α ^ 2) ^ 3 := by
  ring

/-- `thm:canonical-chronology-leakage-master`, the leakage norm:
for Hermitian `A` and a unit depth vector `k`,
`ν = β − α² = ‖(I − |k⟩⟨k|) A k‖²`. -/
theorem leakage_nu_norm (hA : Aᴴ = A) (hk : star k ⬝ᵥ k = 1) :
    star (A *ᵥ k - (star k ⬝ᵥ (A *ᵥ k)) • k)
        ⬝ᵥ (A *ᵥ k - (star k ⬝ᵥ (A *ᵥ k)) • k)
      = star k ⬝ᵥ ((A * A) *ᵥ k) - (star k ⬝ᵥ (A *ᵥ k)) ^ 2 := by
  set v : n → ℂ := A *ᵥ k with hv
  set α : ℂ := star k ⬝ᵥ v with hα
  have hexp : star (v - α • k) ⬝ᵥ (v - α • k)
      = star v ⬝ᵥ v - star α * (star k ⬝ᵥ v) - α * (star v ⬝ᵥ k)
        + α * star α * (star k ⬝ᵥ k) := by
    simp only [star_sub, star_smul, sub_dotProduct, dotProduct_sub,
      smul_dotProduct, dotProduct_smul, smul_eq_mul]
    ring
  -- hermiticity: `star (A k) = star k ᵥ* A`
  have hstar : star v = star k ᵥ* A := by
    rw [hv, Matrix.star_mulVec, hA]
  have hAA : star v ⬝ᵥ v = star k ⬝ᵥ ((A * A) *ᵥ k) := by
    rw [hstar, hv, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]
  have hvk : star v ⬝ᵥ k = α := by
    rw [hstar, ← Matrix.dotProduct_mulVec, hα, hv]
  rw [hexp, hAA, hvk, hk, ← hα]
  ring

/-! ## Off-line variance and the commutator identity -/

variable (P M : Matrix N N ℂ) (e : N → ℂ)

omit [DecidableEq N] in
/-- The line coefficient is the first moment: from `P e = e`,
`Pᴴ = P` and `P M e = c e` it follows that `c = ⟨e, M e⟩`. -/
theorem line_coefficient (hPh : Pᴴ = P) (hPe : P *ᵥ e = e)
    (he : star e ⬝ᵥ e = 1) {c : ℂ}
    (hline : P *ᵥ (M *ᵥ e) = c • e) :
    c = star e ⬝ᵥ (M *ᵥ e) := by
  have hstarP : star e ᵥ* P = star e := by
    conv_lhs => rw [← hPh]
    rw [← Matrix.star_mulVec, hPe]
  have h1 : star e ⬝ᵥ (P *ᵥ (M *ᵥ e)) = star e ⬝ᵥ (M *ᵥ e) := by
    rw [Matrix.dotProduct_mulVec (v := star e) (A := P), hstarP]
  rw [hline, dotProduct_smul, he, smul_eq_mul, mul_one] at h1
  exact h1

omit [DecidableEq N] in
/-- `thm:canonical-chronology-leakage-master`, variance identity:
`‖Me‖² − |⟨e, Me⟩|² = ‖(I − P) M e‖²` whenever the retained component
of `M e` lies on the line `ℂ e`. -/
theorem line_variance_eq_offline_norm (hPh : Pᴴ = P)
    (hPe : P *ᵥ e = e) (he : star e ⬝ᵥ e = 1) {c : ℂ}
    (hline : P *ᵥ (M *ᵥ e) = c • e) :
    star (M *ᵥ e) ⬝ᵥ (M *ᵥ e)
        - star (star e ⬝ᵥ (M *ᵥ e)) * (star e ⬝ᵥ (M *ᵥ e))
      = star (M *ᵥ e - P *ᵥ (M *ᵥ e))
          ⬝ᵥ (M *ᵥ e - P *ᵥ (M *ᵥ e)) := by
  set v : N → ℂ := M *ᵥ e with hv
  set t : ℂ := star e ⬝ᵥ v with ht
  have hc : c = t := line_coefficient P M e hPh hPe he hline
  have hPv : P *ᵥ v = t • e := by rw [← hc]; exact hline
  have hve : star v ⬝ᵥ e = star t := by
    rw [Matrix.star_dotProduct, ht]
  have hexp : star (v - t • e) ⬝ᵥ (v - t • e)
      = star v ⬝ᵥ v - star t * (star e ⬝ᵥ v) - t * (star v ⬝ᵥ e)
        + t * star t * (star e ⬝ᵥ e) := by
    simp only [star_sub, star_smul, sub_dotProduct, dotProduct_sub,
      smul_dotProduct, dotProduct_smul, smul_eq_mul]
    ring
  rw [hPv, hexp, hve, he, ← ht]
  ring

/-- `thm:canonical-chronology-leakage-master`, commutator form:
with `Z = 2P − 1`, `[M, Z] e = 2 (I − P) M e`. -/
theorem line_variance_eq_commutator (hPe : P *ᵥ e = e) :
    (M * ((2 : ℂ) • P - 1) - ((2 : ℂ) • P - 1) * M) *ᵥ e
      = (2 : ℂ) • (M *ᵥ e - P *ᵥ (M *ᵥ e)) := by
  have hZe : ((2 : ℂ) • P - 1) *ᵥ e = e := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, hPe, Matrix.one_mulVec]
    module
  rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    hZe, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  module

/-- Norm form of the commutator identity:
`‖[M, Z] e‖² = 4 ‖(I − P) M e‖²`. -/
theorem commutator_norm_sq (hPe : P *ᵥ e = e) :
    star ((M * ((2 : ℂ) • P - 1) - ((2 : ℂ) • P - 1) * M) *ᵥ e)
        ⬝ᵥ ((M * ((2 : ℂ) • P - 1) - ((2 : ℂ) • P - 1) * M) *ᵥ e)
      = 4 * (star (M *ᵥ e - P *ᵥ (M *ᵥ e))
          ⬝ᵥ (M *ᵥ e - P *ᵥ (M *ᵥ e))) := by
  rw [line_variance_eq_commutator P M e hPe]
  simp only [star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    star_ofNat]
  ring

end

end NCG
