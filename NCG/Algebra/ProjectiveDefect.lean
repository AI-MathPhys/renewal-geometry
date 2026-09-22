/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Projective defects and the automatic projective lift

The updated manuscript *derives* the scalar projective revision law instead
of assuming it (**automatic projective lift**,
`thm:spatial-multiplier-scalar-main`): reversible predictive revisions are
automorphisms (`thm:predictive-unit`), on a finite matrix factor
automorphisms are inner, and once implementers `R_α` of the *same* labelled
automorphism family are chosen, the defects
`σ(α,β) = R_α R_β R_{α+β}⁻¹` are central, satisfy the 2-cocycle identity,
and their antisymmetric ratio is an intrinsic alternating `𝔽₂`-valued form
(`lem:commutator-pm1`, Definition `def:revision-operators-main`).

This file proves that mechanism at its natural level of generality: a family
of implementers `R : L → G` in a group `G`, labelled by an additive
commutative group `L`.

## Main results

* `NCG.projDefect_mem_center_of_ad` — if `R_α R_β` and `R_{α+β}` implement
  the same conjugation, the defect is central (the Schur step of the
  automatic projective lift);
* `NCG.projDefect_cocycle` — central defects satisfy the two-cocycle
  identity (associativity of composition);
* `NCG.commutator_R_mul` — the commutator pairing
  `P(α,β) = ⁅R_α, R_β⁆` controls the exchange relation
  `R_α R_β = P(α,β) · R_β R_α`;
* `NCG.commutator_R_add_left` — with central pairwise commutators the
  pairing is **biadditive** in the labels;
* `NCG.commutator_R_sq_eq_one` — over an elementary abelian 2-group of
  labels the pairing is `{±1}`-valued (`P² = 1`): the polar form of the
  modular commutator datum is an alternating `𝔽₂`-form
  (`lem:commutator-pm1`).
-/

namespace NCG

open scoped commutatorElement

variable {G : Type*} [Group G] {L : Type*} [AddCommGroup L]

/-- The **projective defect** of a family of implementers `R : L → G`:
`σ(α,β) = R_α R_β R_{α+β}⁻¹` (the scalar `σ_s` of the automatic projective
lift `thm:spatial-multiplier-scalar-main`, before centrality is known). -/
def projDefect (R : L → G) (α β : L) : G :=
  R α * R β * (R (α + β))⁻¹

theorem projDefect_spec (R : L → G) (α β : L) :
    R α * R β = projDefect R α β * R (α + β) := by
  simp [projDefect]

/-- **The Schur step of the automatic projective lift**: if the composite
`R_α R_β` and the section value `R_{α+β}` implement the *same* conjugation
of `G`, the projective defect is central.  (In the manuscript `G` is the
unitary group of the irreducible finite revision factor, where conjugation
determines an element up to its central phase.) -/
theorem projDefect_mem_center_of_ad (R : L → G)
    (hAd : ∀ α β g, (R α * R β) * g * (R α * R β)⁻¹
      = R (α + β) * g * (R (α + β))⁻¹) (α β : L) :
    projDefect R α β ∈ Subgroup.center G := by
  rw [Subgroup.mem_center_iff]
  intro g
  have h := hAd α β ((R (α + β))⁻¹ * g * R (α + β))
  -- unfold and cancel to get `d g = g d` for the defect `d`
  have h' : (R α * R β) * ((R (α + β))⁻¹ * g * R (α + β))
        * (R α * R β)⁻¹ = g := by
    rw [h]
    group
  calc g * projDefect R α β
      = g * (R α * R β * (R (α + β))⁻¹) := rfl
    _ = ((R α * R β) * ((R (α + β))⁻¹ * g * R (α + β)) * (R α * R β)⁻¹)
        * (R α * R β * (R (α + β))⁻¹) := by rw [h']
    _ = (R α * R β * (R (α + β))⁻¹) * g := by group
    _ = projDefect R α β * g := rfl

/-- **The two-cocycle identity** (automatic projective lift,
`thm:spatial-multiplier-scalar-main`): central projective defects satisfy

`σ(α,β) σ(α+β,γ) = σ(β,γ) σ(α,β+γ)`,

which is exactly associativity of the implementers. -/
theorem projDefect_cocycle (R : L → G)
    (hZ : ∀ α β, projDefect R α β ∈ Subgroup.center G) (α β γ : L) :
    projDefect R α β * projDefect R (α + β) γ
      = projDefect R β γ * projDefect R α (β + γ) := by
  have hβγ := (Subgroup.mem_center_iff.mp (hZ β γ) (R α)).symm
  -- expand both sides of `(R α R β) R γ = R α (R β R γ)` through the defects
  have key : (projDefect R α β * projDefect R (α + β) γ) * R (α + β + γ)
      = (projDefect R β γ * projDefect R α (β + γ)) * R (α + β + γ) := by
    calc (projDefect R α β * projDefect R (α + β) γ) * R (α + β + γ)
        = projDefect R α β * (projDefect R (α + β) γ * R ((α + β) + γ)) := by
          rw [mul_assoc]
      _ = projDefect R α β * (R (α + β) * R γ) := by
          rw [← projDefect_spec]
      _ = (projDefect R α β * R (α + β)) * R γ := by rw [mul_assoc]
      _ = (R α * R β) * R γ := by rw [← projDefect_spec]
      _ = R α * (R β * R γ) := by rw [mul_assoc]
      _ = R α * (projDefect R β γ * R (β + γ)) := by rw [← projDefect_spec]
      _ = (R α * projDefect R β γ) * R (β + γ) := by rw [mul_assoc]
      _ = (projDefect R β γ * R α) * R (β + γ) := by rw [hβγ]
      _ = projDefect R β γ * (R α * R (β + γ)) := by rw [mul_assoc]
      _ = projDefect R β γ * (projDefect R α (β + γ) * R (α + (β + γ))) := by
          rw [← projDefect_spec]
      _ = (projDefect R β γ * projDefect R α (β + γ)) * R (α + (β + γ)) := by
          rw [mul_assoc]
      _ = (projDefect R β γ * projDefect R α (β + γ)) * R (α + β + γ) := by
          rw [add_assoc]
  exact mul_right_cancel key

omit [AddCommGroup L] in
/-- The **commutator pairing** of the implementers controls the exchange
relation: `R_α R_β = ⁅R_α, R_β⁆ · R_β R_α`. -/
theorem commutator_R_mul (R : L → G) (α β : L) :
    R α * R β = ⁅R α, R β⁆ * (R β * R α) := by
  rw [commutatorElement_def]
  group

/-- The commutator pairing equals the antisymmetric ratio of projective
defects: `⁅R_α, R_β⁆ = σ(α,β) σ(β,α)⁻¹` (the "gauge-invariant commutator
bicharacter" of Definition `def:revision-operators-main`). -/
theorem commutator_R_eq_defect_ratio (R : L → G) (α β : L) :
    ⁅R α, R β⁆ = projDefect R α β * (projDefect R β α)⁻¹ := by
  rw [commutatorElement_def, projDefect, projDefect, add_comm β α]
  group

/-- Multiplying by a central element does not change commutators. -/
theorem commutatorElement_central_mul {z a b : G}
    (hz : z ∈ Subgroup.center G) : ⁅z * a, b⁆ = ⁅a, b⁆ := by
  have hzinv := Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ hz)
  rw [commutatorElement_def, commutatorElement_def, mul_inv_rev]
  calc z * a * b * (a⁻¹ * z⁻¹) * b⁻¹
      = z * (a * b * a⁻¹ * z⁻¹) * b⁻¹ := by group
    _ = z * (z⁻¹ * (a * b * a⁻¹)) * b⁻¹ := by rw [hzinv (a * b * a⁻¹)]
    _ = a * b * a⁻¹ * b⁻¹ := by group

/-- **Biadditivity of the commutator pairing** (automatic projective lift):
if all pairwise commutators of the family are central, then
`⁅R_{α+α'}, R_β⁆ = ⁅R_α, R_β⁆ · ⁅R_{α'}, R_β⁆`. -/
theorem commutator_R_add_left (R : L → G)
    (hZ : ∀ α β, ⁅R α, R β⁆ ∈ Subgroup.center G)
    (hD : ∀ α β, projDefect R α β ∈ Subgroup.center G) (α α' β : L) :
    ⁅R (α + α'), R β⁆ = ⁅R α, R β⁆ * ⁅R α', R β⁆ := by
  -- replace `R (α+α')` by `R α R α'` at the cost of a central defect
  have hsec : R (α + α') = (projDefect R α α')⁻¹ * (R α * R α') := by
    rw [projDefect_spec R α α']
    group
  rw [hsec, commutatorElement_central_mul
    (Subgroup.inv_mem _ (hD α α'))]
  -- now prove `⁅R α * R α', R β⁆ = ⁅R α, R β⁆ ⁅R α', R β⁆`
  have hcomm' := Subgroup.mem_center_iff.mp (hZ α' β)
  have hswap : R α' * R β * (R α')⁻¹ = ⁅R α', R β⁆ * R β := by
    simp only [commutatorElement_def]
    group
  calc ⁅R α * R α', R β⁆
      = R α * (R α' * R β * (R α')⁻¹) * (R α)⁻¹ * (R β)⁻¹ := by
        simp only [commutatorElement_def, mul_inv_rev]
        group
    _ = R α * (⁅R α', R β⁆ * R β) * (R α)⁻¹ * (R β)⁻¹ := by rw [hswap]
    _ = (R α * ⁅R α', R β⁆) * R β * (R α)⁻¹ * (R β)⁻¹ := by group
    _ = (⁅R α', R β⁆ * R α) * R β * (R α)⁻¹ * (R β)⁻¹ := by
        rw [hcomm' (R α)]
    _ = ⁅R α', R β⁆ * ⁅R α, R β⁆ := by
        simp only [commutatorElement_def]
        group
    _ = ⁅R α, R β⁆ * ⁅R α', R β⁆ := by
        exact Subgroup.mem_center_iff.mp (hZ α β) _

/-- **The polar form is `{±1}`-valued** (`lem:commutator-pm1`): over an
elementary abelian 2-group of labels, with a normalized section, the
commutator pairing squares to one.  This is the intrinsic alternating
`𝔽₂`-valued form `ω` of the modular revision datum
(Definition `def:revision-operators-main`): the seed of the Clifford
anticommutation relations of the primitive sector. -/
theorem commutator_R_sq_eq_one (R : L → G)
    (hZ : ∀ α β, ⁅R α, R β⁆ ∈ Subgroup.center G)
    (hD : ∀ α β, projDefect R α β ∈ Subgroup.center G)
    (h2 : ∀ α : L, α + α = 0) (hR0 : R 0 = 1) (α β : L) :
    ⁅R α, R β⁆ * ⁅R α, R β⁆ = 1 := by
  have h := (commutator_R_add_left R hZ hD α α β).symm
  rw [h2 α, hR0] at h
  rw [h]
  rw [commutatorElement_def]
  group

omit [AddCommGroup L] in
/-- Alternation of the pairing: `⁅R_α, R_α⁆ = 1`. -/
@[simp]
theorem commutator_R_self (R : L → G) (α : L) : ⁅R α, R α⁆ = 1 := by
  rw [commutatorElement_def]
  group

end NCG
