/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GrandOrder

/-!
# Canonical endpoint-response coalescence

This file models the response factorization `C = R J` explicitly.  An
isometric endpoint response cannot enlarge the kernel of the endpoint writer;
the canonical response is the identity isometry.
-/

open Matrix

namespace NCG

/-- Response obtained by first collecting compiler histories at numerical
endpoints and then applying the endpoint response. -/
def collectedEndpointResponse {h e t : Type*} [Fintype e]
    (R : Matrix h e ℂ) (J : Matrix e t ℂ) : Matrix h t ℂ :=
  R * J

/-- An isometric endpoint response has exactly the same null histories as the
endpoint collector. -/
theorem collectedEndpointResponse_kernel_eq
    {h e t : Type*} [Fintype h] [Fintype e] [Fintype t]
    [DecidableEq e]
    (R : Matrix h e ℂ) (J : Matrix e t ℂ)
    (hR : Rᴴ * R = 1) (x : t → ℂ) :
    collectedEndpointResponse R J *ᵥ x = 0 ↔ J *ᵥ x = 0 := by
  constructor
  · intro h
    have hprod : (R * J) *ᵥ x = 0 := by
      simpa only [collectedEndpointResponse] using h
    have hnested : R *ᵥ (J *ᵥ x) = 0 := by
      rw [Matrix.mulVec_mulVec]
      exact hprod
    have hleft := congrArg (fun y => Rᴴ *ᵥ y) hnested
    rw [Matrix.mulVec_zero, Matrix.mulVec_mulVec, hR,
      Matrix.one_mulVec] at hleft
    exact hleft
  · intro h
    calc
      collectedEndpointResponse R J *ᵥ x = R *ᵥ (J *ᵥ x) := by
        rw [Matrix.mulVec_mulVec]
        rfl
      _ = 0 := by rw [h, Matrix.mulVec_zero]

/-- The canonical endpoint response is the identity, so its Gram is the
identity and the response factorization is derived rather than assumed. -/
theorem canonicalEndpointResponse_factorization
    {e t : Type*} [Fintype e] [Fintype t] [DecidableEq e]
    (J : Matrix e t ℂ) :
    let Rcan : Matrix e e ℂ := 1
    let Ccan := collectedEndpointResponse Rcan J
    Rcanᴴ * Rcan = 1 ∧ Ccan = J
      ∧ ∀ x : t → ℂ, Ccan *ᵥ x = 0 ↔ J *ᵥ x = 0 := by
  dsimp only
  have hR : ((1 : Matrix e e ℂ)ᴴ * 1) = 1 := by simp
  refine ⟨hR, ?_, ?_⟩
  · simp [collectedEndpointResponse]
  · exact collectedEndpointResponse_kernel_eq 1 J hR

/-- If the endpoint writer has a right inverse, every retained endpoint line
survives the common quotient.  This is the precise finite statement that
there is one noncollapsing source line per retained endpoint. -/
theorem canonicalEndpointResponse_retainedLines
    {e t : Type*} [Fintype e] [Fintype t] [DecidableEq e]
    (J : Matrix e t ℂ) (Q : Matrix t e ℂ) (hJQ : J * Q = 1) :
    Function.Injective (fun y : e → ℂ => Q *ᵥ y)
      ∧ ∀ y : e → ℂ,
          collectedEndpointResponse (1 : Matrix e e ℂ) J *ᵥ (Q *ᵥ y) = y := by
  have hrecover : ∀ y : e → ℂ, J *ᵥ (Q *ᵥ y) = y := by
    intro y
    rw [Matrix.mulVec_mulVec, hJQ, Matrix.one_mulVec]
  constructor
  · intro y z hyz
    calc
      y = J *ᵥ (Q *ᵥ y) := (hrecover y).symm
      _ = J *ᵥ (Q *ᵥ z) := congrArg (fun w => J *ᵥ w) hyz
      _ = z := hrecover z
  · intro y
    rw [collectedEndpointResponse, Matrix.one_mul,
      hrecover]

end NCG
