/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.PositiveCylinderAndTrine

/-!
# Dimension-minimal scalar trine history encoding

The three trine outcomes form an injective linear encoding of the three real
parameters `(t, Re z, Im z)`.  Any linear outcome space admitting exact
reconstruction of those parameters therefore has dimension at least three.
-/

open Finset

namespace NCG
namespace PositiveCylinderAndTrine

/-- The route-blind trine instrument as a linear map on the real parameter
triple `(t,x,y)`. -/
noncomputable def trineParameterEncoder :
    (Fin 3 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun u := trineOutcome (u 0) (u 1) (u 2)
  map_add' u v := by
    funext k
    fin_cases k <;> simp [trineOutcome] <;> ring
  map_smul' a u := by
    funext k
    fin_cases k <;> simp [trineOutcome] <;> ring

/-- The three trine outcomes retain all three real scalar-history
parameters. -/
theorem trineParameterEncoder_injective :
    Function.Injective trineParameterEncoder := by
  intro u v huv
  have h0 := congrFun huv (0 : Fin 3)
  have h1 := congrFun huv (1 : Fin 3)
  have h2 := congrFun huv (2 : Fin 3)
  simp only [trineParameterEncoder, LinearMap.coe_mk, AddHom.coe_mk,
    trineOutcome] at h0 h1 h2
  funext k
  fin_cases k
  · change u 0 = v 0
    linarith
  · change u 1 = v 1
    linarith
  · change u 2 = v 2
    have hsqrt : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
    nlinarith

/-- Any exact linear outcome encoding of total mass and one complex history
coordinate needs at least three real outcome coordinates. -/
theorem scalar_history_outcome_dimension_minimal
    {m : Type*} [Fintype m]
    (encode : (Fin 3 → ℝ) →ₗ[ℝ] (m → ℝ))
    (decode : (m → ℝ) →ₗ[ℝ] (Fin 3 → ℝ))
    (hexact : decode.comp encode = LinearMap.id) :
    3 ≤ Fintype.card m := by
  have hinj : Function.Injective encode := by
    intro u v huv
    have := congrArg decode huv
    simpa only [← LinearMap.comp_apply, hexact, LinearMap.id_apply] using this
  have hdim := LinearMap.finrank_le_finrank_of_injective hinj
  simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using hdim

/-- Full exact packet for `cor:canonical-trine-history`: reconstruction and
the quadratic disk criterion, together with dimension minimality. -/
theorem canonical_trine_history_exact
    {t x y : ℝ} (ht : 0 ≤ t) :
    (∑ k, trineOutcome t x y k = t)
    ∧ (x = trineOutcome t x y 0 -
          (trineOutcome t x y 1 + trineOutcome t x y 2) / 2)
    ∧ (Real.sqrt 3 * y =
          3 * (trineOutcome t x y 2 - trineOutcome t x y 1) / 2)
    ∧ ((∑ k, (trineOutcome t x y k) ^ 2 ≤ t ^ 2 / 2) ↔
          4 * (x ^ 2 + y ^ 2) ≤ t ^ 2)
    ∧ Function.Injective trineParameterEncoder := by
  exact ⟨trineOutcome_sum t x y,
    (trineOutcome_reconstruct t x y).1,
    (trineOutcome_reconstruct t x y).2,
    trine_quadratic_criterion ht,
    trineParameterEncoder_injective⟩

end PositiveCylinderAndTrine
end NCG
