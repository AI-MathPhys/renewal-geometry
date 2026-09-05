/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.DimensionActiveExchange
import NCG.Grand.ActiveResidualAlgebra

/-!
# Exact active tetrahedral carry--exchange instrument

This completes `thm:dimension-active-exchange` around the already certified
endpoint and unordered-pair spectral gaps.  It formalizes the retained control,
sharp target recovery, inverse pairing, conservative product extension,
three-dimensional endpoint contrast register, transient trit, and the
endpoint-only identity-carry obstruction.
-/

open Matrix Finset

noncomputable section

namespace NCG
namespace DimensionActiveExchange

/-- The three controls `s, r, r⁻¹` of DS.12. -/
def activeControlPermutation : Fin 3 → Equiv.Perm (Fin 4) :=
  ![ActiveResidual.sPerm, ActiveResidual.rPerm, ActiveResidual.rPerm⁻¹]

/-- Inversion of the retained control fixes `s` and exchanges `r, r⁻¹`. -/
def inverseControl : Fin 3 → Fin 3 := ![0, 2, 1]

/-- The uniform three-outcome control law. -/
def activeControlWeight (_ : Fin 3) : ℝ := 1 / 3

theorem activeControl_inverse (g : Fin 3) :
    activeControlPermutation (inverseControl g) =
      (activeControlPermutation g)⁻¹ := by
  fin_cases g <;> decide

theorem activeControl_weight_inverse (g : Fin 3) :
    activeControlWeight (inverseControl g) = activeControlWeight g := by
  rfl

/-- Retaining the control makes the previous endpoint sharply recoverable. -/
theorem recover_previous_endpoint (g : Fin 3) (t : Fin 4) :
    (activeControlPermutation g)⁻¹ (activeControlPermutation g t) = t := by
  simp

/-- Adding the independent three-outcome port and then forgetting it preserves
every old cylinder weight. -/
theorem forget_active_product_port
    {α : Type*} (p : α → ℝ) (x : α) :
    ∑ g : Fin 3, p x * activeControlWeight g = p x := by
  simp [activeControlWeight, Fin.sum_univ_three]
  ring

/-- Sum of the four sharp endpoint coordinates. -/
def endpointSum : (Fin 4 → ℝ) →ₗ[ℝ] ℝ where
  toFun f := ∑ i, f i
  map_add' f g := by simp [Finset.sum_add_distrib]
  map_smul' c f := by simp [Finset.mul_sum]

theorem endpointSum_range : LinearMap.range endpointSum = ⊤ := by
  rw [eq_top_iff]
  intro y _
  refine ⟨fun _ ↦ y / 4, ?_⟩
  simp [endpointSum, Fin.sum_univ_four]
  ring

/-- Four endpoint values have exactly three centered contrast directions. -/
theorem endpoint_contrast_finrank :
    Module.finrank ℝ (LinearMap.ker endpointSum) = 3 := by
  have h := LinearMap.finrank_range_add_finrank_ker endpointSum
  rw [endpointSum_range] at h
  norm_num at h ⊢
  omega

/-- An endpoint-only deterministic bridge that carries every target identically
acts trivially on every unordered endpoint pair. -/
theorem endpoint_only_identity_carry_no_pair_exchange
    (g : Equiv.Perm (Fin 4)) (hcarry : ∀ t, g t = t) :
    ∀ p : Sym2 (Fin 4), p.map g = p := by
  intro p
  induction p using Sym2.ind with
  | _ a b =>
      simp only [Sym2.map_mk, hcarry]

/-- Full finite certificate for the minimum active recurrent tetrahedral port. -/
theorem dimension_active_exchange_exact :
    (∀ g t,
      (activeControlPermutation g)⁻¹ (activeControlPermutation g t) = t)
    ∧ Subgroup.closure
        ({ActiveResidual.rPerm, ActiveResidual.sPerm} :
          Set (Equiv.Perm (Fin 4))) = ⊤
    ∧ (∀ g,
      activeControlPermutation (inverseControl g) =
          (activeControlPermutation g)⁻¹
        ∧ activeControlWeight (inverseControl g) = activeControlWeight g)
    ∧ (∀ (α : Type*) (p : α → ℝ) (x : α),
      ∑ g : Fin 3, p x * activeControlWeight g = p x)
    ∧ Module.finrank ℝ (LinearMap.ker endpointSum) = 3
    ∧ Fintype.card (Fin 3) = 3
    ∧ (∀ (g : Equiv.Perm (Fin 4)), (∀ t, g t = t) →
      ∀ p : Sym2 (Fin 4), p.map g = p) := by
  refine ⟨?_, ActiveResidual.closure_sr, ?_, ?_,
    endpoint_contrast_finrank, by simp, ?_⟩
  · exact recover_previous_endpoint
  · intro g
    exact ⟨activeControl_inverse g, activeControl_weight_inverse g⟩
  · intro α p x
    exact forget_active_product_port p x
  · exact endpoint_only_identity_carry_no_pair_exchange

end DimensionActiveExchange
end NCG
