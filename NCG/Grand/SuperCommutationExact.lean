/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.SuperDerivationExact

/-!
# Even–odd commutation on the super-algebra

Mixed-sector machinery for `thm:SM-common-action-integrability` (RG.1/RG.2): the even
super-derivation commutes with every interior product whose dual functional is compatible
with the connection (`evenDeriv_contractLeft`).  This is the operator identity
`[∂ᵢ, ∂ₐ] = 0` between even and odd derivatives on the super-algebra, proved by
`CliffordAlgebra.left_induction` from the two Leibniz rules — no basis structure
constants.
-/

open CliffordAlgebra

namespace NCG
namespace SuperDeriv

variable {R : Type*} [CommRing R]
variable {R₀ : Type*} [CommRing R₀] [Algebra R R₀]
variable {M : Type*} [AddCommGroup M] [Module R₀ M]
variable (d : Derivation R R₀ R₀) (co : Connection d M)

theorem evenDeriv_zero : evenDeriv d co (0 : ExteriorAlgebra R₀ M) = 0 := by
  have h := evenDeriv_algebraMap d co 0
  rwa [map_zero, map_zero, map_zero] at h

/-- The even derivation satisfies the scalar Leibniz rule. -/
theorem evenDeriv_smul (r : R₀) (x : ExteriorAlgebra R₀ M) :
    evenDeriv d co (r • x) = d r • x + r • evenDeriv d co x := by
  rw [Algebra.smul_def, evenDeriv_mul, evenDeriv_algebraMap, ← Algebra.smul_def,
    ← Algebra.smul_def]
  exact add_comm _ _

theorem evenDeriv_neg (x : ExteriorAlgebra R₀ M) :
    evenDeriv d co (-x) = -evenDeriv d co x := by
  have h := evenDeriv_smul d co (-1 : R₀) x
  rw [map_neg, Derivation.map_one_eq_zero, neg_zero, zero_smul, zero_add] at h
  rwa [neg_smul, one_smul, neg_smul, one_smul] at h

theorem evenDeriv_sub (x y : ExteriorAlgebra R₀ M) :
    evenDeriv d co (x - y) = evenDeriv d co x - evenDeriv d co y := by
  rw [sub_eq_add_neg, evenDeriv_add, evenDeriv_neg, sub_eq_add_neg]

/-- **Even–odd commutation**: the even super-derivation commutes with the interior
product by any dual functional compatible with the connection (`δ ∘ co = d ∘ δ`). -/
theorem evenDeriv_contractLeft (δ : Module.Dual R₀ M)
    (hδ : ∀ m, δ (co m) = d (δ m)) (x : ExteriorAlgebra R₀ M) :
    evenDeriv d co (contractLeft (Q := (0 : QuadraticForm R₀ M)) δ x)
      = contractLeft (Q := (0 : QuadraticForm R₀ M)) δ (evenDeriv d co x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r =>
    rw [contractLeft_algebraMap, evenDeriv_zero, evenDeriv_algebraMap,
      contractLeft_algebraMap]
  | add x y hx hy =>
    rw [map_add, evenDeriv_add, evenDeriv_add, map_add, hx, hy]
  | ι_mul x m hx =>
    have hL : evenDeriv d co (contractLeft (Q := (0 : QuadraticForm R₀ M)) δ
        (ι (0 : QuadraticForm R₀ M) m * x))
        = d (δ m) • x + δ m • evenDeriv d co x
          - (ι (0 : QuadraticForm R₀ M) m
              * contractLeft (Q := (0 : QuadraticForm R₀ M)) δ (evenDeriv d co x)
            + ExteriorAlgebra.ι R₀ (co m)
              * contractLeft (Q := (0 : QuadraticForm R₀ M)) δ x) := by
      rw [contractLeft_ι_mul, evenDeriv_sub, evenDeriv_smul, evenDeriv_mul, hx,
        evenDeriv_iota]
    have hR : contractLeft (Q := (0 : QuadraticForm R₀ M)) δ
        (evenDeriv d co (ι (0 : QuadraticForm R₀ M) m * x))
        = δ m • evenDeriv d co x
          - ι (0 : QuadraticForm R₀ M) m
            * contractLeft (Q := (0 : QuadraticForm R₀ M)) δ (evenDeriv d co x)
          + (d (δ m) • x - ExteriorAlgebra.ι R₀ (co m)
              * contractLeft (Q := (0 : QuadraticForm R₀ M)) δ x) := by
      rw [evenDeriv_mul, evenDeriv_iota, map_add, contractLeft_ι_mul,
        show (ExteriorAlgebra.ι R₀ (co m) : ExteriorAlgebra R₀ M)
          = ι (0 : QuadraticForm R₀ M) (co m) from rfl, contractLeft_ι_mul, hδ]
    rw [hL, hR]
    abel

end SuperDeriv
end NCG
