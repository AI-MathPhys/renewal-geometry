/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.SoftSourceBoundExact
import NCG.Grand.MoorePenroseSchurExact
import NCG.Grand.HilbertSchmidtExact

/-!
# The nonduplicating singular-event ledger

Exact formalization for `thm:GRH-soft-source-ledger` (GRH.4–GRH.6).

* **GRH.4** is `NCG.SoftSource.soft_source_bound`: the integrated soft-source mass of a
  singular Hermitian pencil is at least `arctan(c)/c`.
* **GRH.5** (`soft_innovation`): the fresh soft-source mass of an event is the Moore–
  Penrose Schur innovation `G_jj - G_{j,<j} (G_{<j,<j})† G_{<j,j} ⪰ 0`.
* **GRH.6** (`soft_ledger_trace`): `Tr Q̄_j = ‖P_{<j} 𝒮_j‖²_HS + Tr 𝕀_j` — the source
  projection Pythagoras splitting old-head loading from the irreducible fresh response.
-/

open Matrix ContinuousLinearMap
open scoped RealInnerProductSpace InnerProduct

namespace NCG
namespace SoftSource

open NCG.MoorePenrose NCG.HilbertSchmidt

variable {E F E' : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']

/-- **GRH.5**: the fresh soft-source mass of an event is the Moore–Penrose Schur
innovation of the soft Gram against the earlier events, and it is positive. -/
theorem soft_innovation (S : E →L[ℝ] F) (T : E' →L[ℝ] F) :
    ((T†) ∘L T - (crossGram S T)† ∘L gramPinv S ∘L crossGram S T
        = (T†) ∘L residual S T) ∧
      ((T†) ∘L residual S T).IsPositive :=
  ⟨schur_innovation S T, innovation_isPositive S T⟩

/-- **GRH.6**: the source projection Pythagoras — the total soft mass of an event splits
exactly into the old-head loading and the trace of the fresh innovation. -/
theorem soft_ledger_trace (S : E →L[ℝ] F) (T : E' →L[ℝ] F) :
    hsSq T = hsSq ((LinearMap.range S.toLinearMap).starProjection ∘L T)
      + LinearMap.trace ℝ E'
        (((T†) ∘L residual S T : E' →L[ℝ] E') : E' →ₗ[ℝ] E') := by
  set P := (LinearMap.range S.toLinearMap).starProjection with hP
  set A : E' →L[ℝ] F := P ∘L T with hA
  set B : E' →L[ℝ] F := residual S T with hB
  have hTAB : T = A + B := by
    refine ContinuousLinearMap.ext fun y => ?_
    rw [_root_.add_apply, hA, hB, ContinuousLinearMap.comp_apply, residual_apply]
    rw [hP]
    abel
  have hAB : (A†) ∘L B = 0 := by
    refine ContinuousLinearMap.ext fun y => ?_
    rw [_root_.zero_apply]
    have hw : ∀ z : E', ⟪((A†) ∘L B) y, z⟫ = 0 := by
      intro z
      rw [ContinuousLinearMap.comp_apply, adjoint_inner_left]
      have hmem : A z ∈ LinearMap.range S.toLinearMap := by
        rw [hA, ContinuousLinearMap.comp_apply, hP]
        exact (LinearMap.range S.toLinearMap).starProjection_apply_mem _
      obtain ⟨x, hx⟩ := hmem
      rw [show A z = S x from hx.symm]
      exact residual_inner_eq_zero S T y x
    have h0 := hw (((A†) ∘L B) y)
    rwa [real_inner_self_eq_norm_sq, sq_eq_zero_iff, norm_eq_zero] at h0
  have hsplit := hsSq_add_of_adjoint_comp_eq_zero (A := A) (B := B) hAB
  rw [hTAB, hsplit]
  congr 1
  have hTR : ((A + B)†) ∘L B = (B†) ∘L B := by
    rw [show ((A + B)†) = (A†) + (B†) from map_add adjoint A B, add_comp, hAB, zero_add]
  rw [hTR]
  rfl

/-- **Bundle for `thm:GRH-soft-source-ledger`**: the eventwise arctan lower bound, the
positive Schur innovation, and the source projection Pythagoras. -/
theorem grh_soft_source_ledger {n : Type*} [Fintype n] [DecidableEq n]
    (A₀ H : Matrix n n ℝ) (hA₀ : A₀.IsHermitian) (hH : H.IsHermitian)
    {a c : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hHb : ∀ w : n → ℝ, (H *ᵥ w) ⬝ᵥ (H *ᵥ w) ≤ (c * a) ^ 2 * (w ⬝ᵥ w))
    {s₀ : ℝ} (h0 : 0 ≤ s₀) (h1 : s₀ ≤ 1) (hsing : (A₀ + s₀ • H).det = 0)
    (S : E →L[ℝ] F) (T : E' →L[ℝ] F) :
    (Real.arctan c / c ≤ ∫ s in (0:ℝ)..1,
      (a ^ 2 • ((A₀ + s • H) * (A₀ + s • H) + a ^ 2 • (1 : Matrix n n ℝ))⁻¹).trace) ∧
    ((T†) ∘L T - (crossGram S T)† ∘L gramPinv S ∘L crossGram S T
        = (T†) ∘L residual S T) ∧
    ((T†) ∘L residual S T).IsPositive ∧
    (hsSq T = hsSq ((LinearMap.range S.toLinearMap).starProjection ∘L T)
      + LinearMap.trace ℝ E'
        (((T†) ∘L residual S T : E' →L[ℝ] E') : E' →ₗ[ℝ] E')) :=
  ⟨soft_source_bound A₀ H hA₀ hH ha hc hHb h0 h1 hsing,
   (soft_innovation S T).1, (soft_innovation S T).2, soft_ledger_trace S T⟩

end SoftSource
end NCG
