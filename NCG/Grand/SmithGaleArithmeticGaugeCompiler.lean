/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SmithGaleCompiler
import NCG.Grand.SmithGale

/-!
# Smith--Gale arithmetic gauge compiler

This module derives the solution coordinates from a split Smith--Gale exact
sequence rather than assuming a bijective kernel labelling.  It also gives the
weighted reindexing on the original typed slots.
-/

namespace NCG
namespace SmithGaleArithmeticGaugeCompiler

noncomputable section

variable {G H Y T : Type*}
  [CommGroup G] [CommGroup H] [CommGroup Y] [CommGroup T]
  [Fintype G] [Fintype H] [Fintype Y] [Fintype T]
  [DecidableEq G] [DecidableEq H] [DecidableEq Y] [DecidableEq T]
  {n : ℕ}

abbrev ConstraintSpace (G : Type*) (n : ℕ) := Fin n → G

/-- A chosen integral Gale basis modulo `q`, the Smith torsion quotient, and
a section of that quotient.  The exactness field is precisely
`im B_q = ker β_q`; no bijective kernel parametrization is assumed. -/
structure SplitSmithGaleData
    (A : ConstraintSpace G n →* H) where
  gale : Y →* MonoidHom.ker A
  beta : MonoidHom.ker A →* T
  torsionSection : T → MonoidHom.ker A
  gale_injective : Function.Injective gale
  exactness : ∀ k, beta k = 1 ↔ ∃ y, gale y = k
  torsionSection_rightInverse : ∀ t, beta (torsionSection t) = t

namespace SplitSmithGaleData

variable {A : ConstraintSpace G n →* H}
  (D : SplitSmithGaleData (Y := Y) (T := T) A)

theorem beta_gale (y : Y) : D.beta (D.gale y) = 1 :=
  (D.exactness (D.gale y)).2 ⟨y, rfl⟩

theorem beta_difference (k : MonoidHom.ker A) :
    D.beta (k * (D.torsionSection (D.beta k))⁻¹) = 1 := by
  rw [map_mul, map_inv, D.torsionSection_rightInverse, mul_inv_cancel]

/-- The unique Gale coordinate in the fibre of `β_q`. -/
def galeCoordinate (k : MonoidHom.ker A) : Y :=
  Classical.choose ((D.exactness _).1 (D.beta_difference k))

theorem gale_galeCoordinate (k : MonoidHom.ker A) :
    D.gale (D.galeCoordinate k) =
      k * (D.torsionSection (D.beta k))⁻¹ :=
  Classical.choose_spec ((D.exactness _).1 (D.beta_difference k))

/-- Exactness plus the torsion section gives the manuscript's unique
`(y,t)` coordinates on the congruence kernel. -/
def kernelEquivGaleTimesTorsion :
    (Y × T) ≃ MonoidHom.ker A where
  toFun q := D.gale q.1 * D.torsionSection q.2
  invFun k := (D.galeCoordinate k, D.beta k)
  left_inv q := by
    dsimp
    apply Prod.ext
    · apply D.gale_injective
      rw [D.gale_galeCoordinate]
      rw [map_mul, D.beta_gale, one_mul, D.torsionSection_rightInverse]
      group
    · rw [map_mul, D.beta_gale, one_mul, D.torsionSection_rightInverse]
  right_inv k := by
    dsimp
    rw [D.gale_galeCoordinate]
    group

/-- The affine solution fibre of `A x = b`. -/
abbrev Solution (A : ConstraintSpace G n →* H) (b : H) :=
  {x : ConstraintSpace G n // A x = b}

/-- Translation by one solution identifies the whole solution fibre with the
kernel, and the split Smith--Gale sequence then supplies the unique
`x = x₀ B_q(y) s_q(t)` representation. -/
def labelsEquivSolutions (b : H) (x₀ : ConstraintSpace G n)
    (hx₀ : A x₀ = b) :
    (Y × T) ≃ Solution A b where
  toFun q :=
    ⟨x₀ * (D.kernelEquivGaleTimesTorsion q : ConstraintSpace G n), by
      rw [map_mul, hx₀, (D.kernelEquivGaleTimesTorsion q).property, mul_one]⟩
  invFun x := D.kernelEquivGaleTimesTorsion.symm
    ⟨x₀⁻¹ * x, by
      change A (x₀⁻¹ * x.1) = 1
      rw [map_mul, map_inv, x.property, hx₀, inv_mul_cancel]⟩
  left_inv q := by
    apply D.kernelEquivGaleTimesTorsion.injective
    apply Subtype.ext
    simp
  right_inv x := by
    apply Subtype.ext
    dsimp
    rw [D.kernelEquivGaleTimesTorsion.apply_symm_apply]
    group

theorem unique_solution_coordinates (b : H)
    (x₀ : ConstraintSpace G n) (hx₀ : A x₀ = b)
    (x : ConstraintSpace G n) :
    A x = b ↔ ∃! q : Y × T,
      x = x₀ * ((D.gale q.1 : ConstraintSpace G n) *
        (D.torsionSection q.2 : ConstraintSpace G n)) := by
  constructor
  · intro hx
    let xs : Solution A b := ⟨x, hx⟩
    refine ⟨(D.labelsEquivSolutions b x₀ hx₀).symm xs, ?_, ?_⟩
    · have h := (D.labelsEquivSolutions b x₀ hx₀).apply_symm_apply xs
      change x = x₀ * ((D.gale
        ((D.labelsEquivSolutions b x₀ hx₀).symm xs).1 : ConstraintSpace G n) *
        (D.torsionSection
          ((D.labelsEquivSolutions b x₀ hx₀).symm xs).2 : ConstraintSpace G n))
      exact congrArg Subtype.val h |>.symm
    · intro q hq
      let E := D.labelsEquivSolutions b x₀ hx₀
      apply E.injective
      exact (Subtype.ext hq.symm).trans (E.apply_symm_apply xs).symm
  · rintro ⟨q, rfl, -⟩
    rw [map_mul, map_mul, hx₀, (D.gale q.1).property,
      (D.torsionSection q.2).property]
    simp

/-- The first boxed compiler formula: arbitrary slot weights are reindexed by
the unique Gale and Smith-torsion coordinates, without changing the slots. -/
theorem weighted_solution_reindex (b : H)
    (x₀ : ConstraintSpace G n) (hx₀ : A x₀ = b)
    (w : Fin n → G → ℂ) :
    ∑ x : Solution A b, ∏ j, w j (x.1 j) =
      ∑ q : Y × T, ∏ j,
        w j (x₀ j * ((D.gale q.1 : ConstraintSpace G n) j *
          (D.torsionSection q.2 : ConstraintSpace G n) j)) := by
  symm
  exact Fintype.sum_equiv (D.labelsEquivSolutions b x₀ hx₀) _ _
    (fun q => by rfl)

/-- Changing the Gale basis or torsion section only changes the label
equivalence; the weighted fibre sum itself is intrinsic. -/
theorem weighted_sum_independent_of_split
    (D' : SplitSmithGaleData (Y := Y) (T := T) A)
    (b : H) (x₀ : ConstraintSpace G n) (hx₀ : A x₀ = b)
    (w : Fin n → G → ℂ) :
    (∑ q : Y × T, ∏ j,
        w j (x₀ j * ((D.gale q.1 : ConstraintSpace G n) j *
          (D.torsionSection q.2 : ConstraintSpace G n) j))) =
      ∑ q : Y × T, ∏ j,
        w j (x₀ j * ((D'.gale q.1 : ConstraintSpace G n) j *
          (D'.torsionSection q.2 : ConstraintSpace G n) j)) := by
  rw [← D.weighted_solution_reindex b x₀ hx₀ w,
    ← D'.weighted_solution_reindex b x₀ hx₀ w]

end SplitSmithGaleData

/-! ## Character normalization on the actual transpose image -/

variable {K : Type*} [CommGroup K] [Fintype K] [DecidableEq K]

/-- Constraint-character duality for an arbitrary finite abelian codomain.
This is the finite Fourier engine used below with the codomain restricted to
the actual image of the constraint map. -/
theorem constraintCharacter_general
    (A : ConstraintSpace G n →* K) (w : Fin n → G → ℂ) (b : K) :
    ∑ x ∈ Finset.univ.filter
        (fun x : ConstraintSpace G n => A x = b),
        ∏ j, w j (x j) =
      (Fintype.card K : ℂ)⁻¹ *
        ∑ η : K →* ℂˣ,
          ((η (b⁻¹) : ℂˣ) : ℂ) *
            ∏ j, ∑ g, w j g *
              ((η (A (Pi.mulSingle j g)) : ℂˣ) : ℂ) := by
  have hK0 : (Fintype.card K : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hswap : ∀ η : K →* ℂˣ,
      ∏ j, ∑ g, w j g * ((η (A (Pi.mulSingle j g)) : ℂˣ) : ℂ) =
        ∑ x : ConstraintSpace G n,
          (∏ j, w j (x j)) * ((η (A x) : ℂˣ) : ℂ) := by
    intro η
    rw [Fintype.prod_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.prod_mul_distrib]
    congr 1
    calc
      ∏ j, ((η (A (Pi.mulSingle j (x j))) : ℂˣ) : ℂ) =
          (((∏ j, η (A (Pi.mulSingle j (x j)))) : ℂˣ) : ℂ) :=
        (map_prod (Units.coeHom ℂ) _ Finset.univ).symm
      _ = ((η (∏ j, A (Pi.mulSingle j (x j))) : ℂˣ) : ℂ) := by
        rw [← map_prod η]
      _ = ((η (A (∏ j, Pi.mulSingle j (x j))) : ℂˣ) : ℂ) := by
        rw [← map_prod A]
      _ = ((η (A x) : ℂˣ) : ℂ) := by
        rw [Finset.univ_prod_mulSingle]
  have hmain :
      ∑ η : K →* ℂˣ,
          ((η (b⁻¹) : ℂˣ) : ℂ) *
            ∏ j, ∑ g, w j g *
              ((η (A (Pi.mulSingle j g)) : ℂˣ) : ℂ) =
        ∑ x : ConstraintSpace G n,
          if A x = b then (∏ j, w j (x j)) * (Fintype.card K : ℂ)
          else 0 := by
    calc
      ∑ η : K →* ℂˣ,
          ((η (b⁻¹) : ℂˣ) : ℂ) *
            ∏ j, ∑ g, w j g *
              ((η (A (Pi.mulSingle j g)) : ℂˣ) : ℂ) =
        ∑ η : K →* ℂˣ, ∑ x : ConstraintSpace G n,
          (∏ j, w j (x j)) * ((η (A x * b⁻¹) : ℂˣ) : ℂ) := by
            refine Finset.sum_congr rfl fun η _ => ?_
            rw [hswap η, Finset.mul_sum]
            refine Finset.sum_congr rfl fun x _ => ?_
            rw [map_mul, Units.val_mul]
            ring
      _ = ∑ x : ConstraintSpace G n, ∑ η : K →* ℂˣ,
          (∏ j, w j (x j)) * ((η (A x * b⁻¹) : ℂˣ) : ℂ) :=
        Finset.sum_comm
      _ = ∑ x : ConstraintSpace G n,
          (∏ j, w j (x j)) *
            ∑ η : K →* ℂˣ, ((η (A x * b⁻¹) : ℂˣ) : ℂ) := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum]
      _ = ∑ x : ConstraintSpace G n,
          if A x = b then (∏ j, w j (x j)) * (Fintype.card K : ℂ)
          else 0 := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [dual_sum_indicator (A x * b⁻¹), mul_ite, mul_zero,
          Nat.card_eq_fintype_card]
        exact if_congr mul_inv_eq_one rfl rfl
  rw [Finset.sum_filter, hmain, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [mul_ite, mul_zero]
  by_cases hx : A x = b
  · rw [if_pos hx, if_pos hx]
    field_simp
  · rw [if_neg hx, if_neg hx]

/-- The second boxed Smith--Gale formula, normalized directly by the dual of
the actual constraint image.  These are exactly the restricted transpose
characters; no duplicate extensions through the ambient codomain remain. -/
theorem constraintCharacter_restrictedToTransposeImage
    (A : ConstraintSpace G n →* H) (w : Fin n → G → ℂ)
    (x₀ : ConstraintSpace G n) :
    let Aimage : ConstraintSpace G n →* MonoidHom.range A := A.rangeRestrict
    let bimage : MonoidHom.range A := Aimage x₀
    ∑ x ∈ Finset.univ.filter
        (fun x : ConstraintSpace G n => A x = A x₀),
        ∏ j, w j (x j) =
      (Nat.card (MonoidHom.range A →* ℂˣ) : ℂ)⁻¹ *
        ∑ η : MonoidHom.range A →* ℂˣ,
          ((η (bimage⁻¹) : ℂˣ) : ℂ) *
            ∏ j, ∑ g, w j g *
              ((η (Aimage (Pi.mulSingle j g)) : ℂˣ) : ℂ) := by
  dsimp
  have h := constraintCharacter_general A.rangeRestrict w (A.rangeRestrict x₀)
  rw [dual_card, Nat.card_eq_fintype_card]
  simpa only [MonoidHom.coe_rangeRestrict, Subtype.ext_iff] using h

end
end SmithGaleArithmeticGaugeCompiler
end NCG
