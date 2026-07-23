/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Krein.ConePositive

/-!
# Rank two: structure group `{I,S}` and the two-cochains lemma

This file proves the rank-two layer of the classification of minimal
signed enrichments (Lemma `lem:minimal-rank-two`, Lemma
`lem:two-cochains-one-class`, feeding Theorem `thm:classification`).

* **Structure-group reduction** (`NCG.structure_group_rank_two`): on a
  rank-two renewal fibre, a cone-positive norm-preserving automorphism is
  the identity or the sheet swap on the distinguished basis — the
  structure group is `{I, S} ≅ ℤ/2`.  This specialises the cone-positive
  permutation lemma (`NCG.conePositive_perm`) to `n = 2`, where the only
  permutations are `1` and the transposition.

* **The two-cochain calculus** on the model fibre `R²` with
  `J₀ = diag(1,−1)` and sheet swap `S`:
  `S² = 1`, `J₀S = −SJ₀`, edge transport `S^{c(e)}` with
  `S^{α+β} = S^α S^β` (`NCG.spow_add`), the coboundary action of a sheet
  change `c ↦ c + δa` (`NCG.gauge_transport` =
  Lemma `lem:two-cochains-one-class` (iii)), and the **gauge-invariant
  homogeneity degree**
  `J_y T_e = (−1)^{ε(e)} T_e J_x` with `ε(e) = c(e) + j(x) + j(y)`
  (`NCG.homogeneity_degree` = Lemma `lem:two-cochains-one-class` (iv)),
  whence `[ε] = [c] ∈ H¹(G, ℤ/2)`.
-/

namespace NCG

/-! ### The structure group at rank two -/

/-- **Lemma `lem:minimal-rank-two`** (reduction of the structure group):
on a rank-two renewal fibre, every cone-positive norm-preserving linear
automorphism acts on the distinguished renewal basis as the identity or
the sheet swap — the structure group is `{I, S} ≅ ℤ/2`.  All `U(1)`
phases and residual signs are excluded by cone positivity. -/
theorem structure_group_rank_two
    (T : (Fin 2 → ℝ) ≃ₗ[ℝ] (Fin 2 → ℝ))
    (hT : T '' orthant 2 = orthant 2) (hnorm : ∀ x, ‖T x‖ = ‖x‖) :
    (∀ i, T (Pi.single i 1) = Pi.single i 1) ∨
    (∀ i, T (Pi.single i 1) = Pi.single (Equiv.swap 0 1 i) 1) := by
  obtain ⟨π, hπ⟩ := conePositive_perm T hT hnorm
  have hall : ∀ σ : Equiv.Perm (Fin 2),
      σ = Equiv.refl (Fin 2) ∨ σ = Equiv.swap 0 1 := by decide
  rcases hall π with rfl | rfl
  · exact Or.inl fun i => by rw [hπ i, Equiv.refl_apply]
  · exact Or.inr hπ

/-! ### The two-cochain sign calculus on the model fibre -/

section Cochains

variable (R : Type*) [CommRing R]

/-- The sign character `ℤ/2 → {±1} ⊆ R`. -/
def sgn (α : ZMod 2) : R := if α = 0 then 1 else -1

variable {R}

@[simp] theorem sgn_zero : sgn R 0 = 1 := rfl

@[simp] theorem sgn_one : sgn R 1 = -1 := rfl

theorem zmod2_cases : ∀ α : ZMod 2, α = 0 ∨ α = 1 := by decide

/-- The sign character is additive-to-multiplicative. -/
theorem sgn_add (α β : ZMod 2) :
    sgn R (α + β) = sgn R α * sgn R β := by
  rcases zmod2_cases α with rfl | rfl <;>
    rcases zmod2_cases β with rfl | rfl <;>
    simp [sgn, show (1 + 1 : ZMod 2) = 0 from rfl]

theorem sgn_mul_self (α : ZMod 2) : sgn R α * sgn R α = 1 := by
  rcases zmod2_cases α with rfl | rfl <;> simp

variable (R)

/-- The reference fundamental symmetry `J₀ = diag(1, −1)` of the rank-two
model fibre. -/
def refJ : Matrix (Fin 2) (Fin 2) R := Matrix.of ![![1, 0], ![0, -1]]

/-- The sheet swap `S` of the rank-two model fibre. -/
def sheetSwap : Matrix (Fin 2) (Fin 2) R := Matrix.of ![![0, 1], ![1, 0]]

/-- Edge transport `S^α` with `ℤ/2` exponent
(Lemma `lem:two-cochains-one-class` (i)). -/
def spow (α : ZMod 2) : Matrix (Fin 2) (Fin 2) R :=
  if α = 0 then 1 else sheetSwap R

/-- The fundamental symmetry at a vertex with sheet sign `j`:
`J = (−1)^j J₀`. -/
def vertexJ (j : ZMod 2) : Matrix (Fin 2) (Fin 2) R :=
  sgn R j • refJ R

variable {R}

/-- The sheet swap is an involution. -/
theorem sheetSwap_mul_self : sheetSwap R * sheetSwap R = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sheetSwap, Matrix.mul_apply, Fin.sum_univ_two]

/-- The fundamental symmetry anticommutes with the deck swap: in a sheet
trivialisation the deck involution is `J₀`-odd
(Remark `rem:cover-is-invariant`). -/
theorem refJ_mul_sheetSwap :
    refJ R * sheetSwap R = -(sheetSwap R * refJ R) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [refJ, sheetSwap, Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem spow_zero : spow R 0 = 1 := rfl

@[simp] theorem spow_one : spow R 1 = sheetSwap R := rfl

/-- `S^{α+β} = S^α S^β`: transport composes additively in the exponent. -/
theorem spow_add (α β : ZMod 2) :
    spow R (α + β) = spow R α * spow R β := by
  rcases zmod2_cases α with rfl | rfl <;>
    rcases zmod2_cases β with rfl | rfl <;>
    simp [spow, show (1 + 1 : ZMod 2) = 0 from rfl,
      sheetSwap_mul_self]

/-- Exchange rule: `J₀ S^α = (−1)^α S^α J₀`. -/
theorem refJ_mul_spow (α : ZMod 2) :
    refJ R * spow R α = sgn R α • (spow R α * refJ R) := by
  rcases zmod2_cases α with rfl | rfl
  · simp
  · simp only [spow_one, sgn_one, neg_smul, one_smul]
    rw [refJ_mul_sheetSwap]

/-- **Lemma `lem:two-cochains-one-class` (iii)** (coboundary action of a
sheet change): conjugating the edge transport `S^c` by the sheet-change
swaps `S^{a(y)}, S^{a(x)}` shifts the transition cochain by the
coboundary, `c ↦ c + δa` with `(δa)(e) = a(x) + a(y)`. -/
theorem gauge_transport (c ax ay : ZMod 2) :
    spow R ay * spow R c * spow R ax = spow R (c + (ax + ay)) := by
  rw [← spow_add, ← spow_add]
  congr 1
  ring

/-- **Lemma `lem:two-cochains-one-class` (iv)** (two cochains, one
cohomology class): with vertex symmetries `J_x = (−1)^{j(x)} J₀` and edge
transport `T_e = S^{c(e)}`, the exchange sign is the gauge-invariant
homogeneity degree `ε(e) = c(e) + j(x) + j(y)`:

`J_y T_e = (−1)^{ε(e)} T_e J_x`.

Since `ε = c + δj`, the classes agree: `[ε] = [c] ∈ H¹(G, ℤ/2)` — the
principal cover is the intrinsic invariant and the sheet signs are gauge
data. -/
theorem homogeneity_degree (c jx jy : ZMod 2) :
    vertexJ R jy * spow R c
      = sgn R (c + jx + jy) • (spow R c * vertexJ R jx) := by
  unfold vertexJ
  rw [Matrix.smul_mul, refJ_mul_spow, Matrix.mul_smul, smul_smul,
    smul_smul]
  congr 1
  have h := sgn_mul_self (R := R) jx
  rw [sgn_add, sgn_add]
  linear_combination (-(sgn R c * sgn R jy)) * h

end Cochains

end NCG
