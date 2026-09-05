/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.TetrahedralGap

/-!
# Operator-level complete tetrahedral gap

This file proves `thm:tetrahedral-prototype-gap` on the actual six-edge `K₄`
carrier.  It replaces the former aggregate scalar error ledger by six router
defects and six bounded edge-Hessian error operators.
-/

open Finset
open scoped InnerProductSpace

namespace NCG

/-- Sources of the six lexicographically ordered unoriented edges of `K₄`. -/
def k4EdgeSource : Fin 6 → Fin 4 := ![0, 0, 0, 1, 1, 2]

/-- Targets of the six lexicographically ordered unoriented edges of `K₄`. -/
def k4EdgeTarget : Fin 6 → Fin 4 := ![1, 2, 3, 2, 3, 3]

section

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- Router defect on one of the six `K₄` edges. -/
def k4RouterDefect (U : Fin 6 → V ≃ₗᵢ[ℝ] V) (f : Fin 4 → V)
    (e : Fin 6) : V :=
  f (k4EdgeTarget e) - U e (f (k4EdgeSource e))

/-- Ideal six-edge router energy measured by the common whitened synthesis
`S`. -/
noncomputable def k4IdealRouterEnergy (S : V →L[ℝ] W)
    (U : Fin 6 → V ≃ₗᵢ[ℝ] V) (f : Fin 4 → V) : ℝ :=
  ∑ e : Fin 6, ‖S (k4RouterDefect U f e)‖ ^ 2

/-- Actual energy after adding the six self-adjoint edge-Hessian error blocks.
Self-adjointness is physically relevant but the lower bound only needs their
operator norms. -/
noncomputable def k4ActualRouterEnergy (S : V →L[ℝ] W)
    (U : Fin 6 → V ≃ₗᵢ[ℝ] V) (E : Fin 6 → V →L[ℝ] V)
    (f : Fin 4 → V) : ℝ :=
  ∑ e : Fin 6, (‖S (k4RouterDefect U f e)‖ ^ 2 +
    ⟪k4RouterDefect U f e, E e (k4RouterDefect U f e)⟫_ℝ)

/-- Every unitary-router defect is controlled by the two endpoint norms. -/
theorem k4RouterDefect_sq_le (U : Fin 6 → V ≃ₗᵢ[ℝ] V)
    (f : Fin 4 → V) (e : Fin 6) :
    ‖k4RouterDefect U f e‖ ^ 2 ≤
      2 * (‖f (k4EdgeSource e)‖ ^ 2 + ‖f (k4EdgeTarget e)‖ ^ 2) := by
  have hnorm : ‖k4RouterDefect U f e‖ ≤
      ‖f (k4EdgeTarget e)‖ + ‖f (k4EdgeSource e)‖ := by
    unfold k4RouterDefect
    calc
      ‖f (k4EdgeTarget e) - U e (f (k4EdgeSource e))‖
          ≤ ‖f (k4EdgeTarget e)‖ + ‖U e (f (k4EdgeSource e))‖ := norm_sub_le _ _
      _ = ‖f (k4EdgeTarget e)‖ + ‖f (k4EdgeSource e)‖ := by
        rw [LinearIsometryEquiv.norm_map]
  have hn : 0 ≤ ‖k4RouterDefect U f e‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖f (k4EdgeTarget e)‖ - ‖f (k4EdgeSource e)‖)]

/-- Summing the six endpoint bounds gives the exact incidence factor six. -/
theorem k4RouterDefect_sum_le_six (U : Fin 6 → V ≃ₗᵢ[ℝ] V)
    (f : Fin 4 → V) :
    ∑ e : Fin 6, ‖k4RouterDefect U f e‖ ^ 2 ≤
      6 * ∑ i : Fin 4, ‖f i‖ ^ 2 := by
  calc
    ∑ e : Fin 6, ‖k4RouterDefect U f e‖ ^ 2
        ≤ ∑ e : Fin 6,
          2 * (‖f (k4EdgeSource e)‖ ^ 2 + ‖f (k4EdgeTarget e)‖ ^ 2) :=
          Finset.sum_le_sum fun e _ => k4RouterDefect_sq_le U f e
    _ = 6 * ∑ i : Fin 4, ‖f i‖ ^ 2 := by
      simp [Fin.sum_univ_six, Fin.sum_univ_four,
        k4EdgeSource, k4EdgeTarget]
      ring

/-- A bounded Hessian block contributes at worst its operator norm times the
squared defect norm. -/
theorem edgeHessianError_lower (E : V →L[ℝ] V) (x : V) (ε : ℝ)
    (hE : ‖E‖ ≤ ε) :
    -ε * ‖x‖ ^ 2 ≤ ⟪x, E x⟫_ℝ := by
  have hi : -‖x‖ * ‖E x‖ ≤ ⟪x, E x⟫_ℝ :=
    by simpa only [neg_mul] using
      (neg_le_of_abs_le (abs_real_inner_le_norm x (E x)))
  have hEx : ‖E x‖ ≤ ε * ‖x‖ :=
    (E.le_opNorm x).trans (mul_le_mul_of_nonneg_right hE (norm_nonneg x))
  have hx : 0 ≤ ‖x‖ := norm_nonneg x
  calc
    -ε * ‖x‖ ^ 2 = -‖x‖ * (ε * ‖x‖) := by ring
    _ ≤ -‖x‖ * ‖E x‖ := mul_le_mul_of_nonpos_left hEx (neg_nonpos.mpr hx)
    _ ≤ ⟪x, E x⟫_ℝ := hi

/-- The six actual Hessian blocks lower the ideal router energy by at most
`6 ε ‖f‖²`. -/
theorem k4ActualEnergy_lower_ideal
    (S : V →L[ℝ] W) (U : Fin 6 → V ≃ₗᵢ[ℝ] V)
    (E : Fin 6 → V →L[ℝ] V) (f : Fin 4 → V) (ε : ℝ)
    (hε : 0 ≤ ε) (hE : ∀ e, ‖E e‖ ≤ ε) :
    k4IdealRouterEnergy S U f - 6 * ε * (∑ i : Fin 4, ‖f i‖ ^ 2)
      ≤ k4ActualRouterEnergy S U E f := by
  have herr : -ε * (∑ e : Fin 6, ‖k4RouterDefect U f e‖ ^ 2) ≤
      ∑ e : Fin 6,
        ⟪k4RouterDefect U f e, E e (k4RouterDefect U f e)⟫_ℝ := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun e _ =>
      edgeHessianError_lower (E e) _ ε (hE e)
  have hdef := k4RouterDefect_sum_le_six U f
  have hscaled : -6 * ε * (∑ i : Fin 4, ‖f i‖ ^ 2) ≤
      -ε * (∑ e : Fin 6, ‖k4RouterDefect U f e‖ ^ 2) := by
    nlinarith
  unfold k4IdealRouterEnergy k4ActualRouterEnergy
  rw [Finset.sum_add_distrib]
  linarith

/-- **Prototype triangle controls the complete tetrahedral gap**, now on the
actual six-edge operator carrier.

The first three routers are the star tree.  The final three are its
fundamental triangle holonomies; `h₁₂`, `h₁₃`, and `h₂₃` are their pointwise
operator estimates obtained from `‖I-H‖ ≤ δ` and `‖G‖ ≤ M`.
-/
theorem tetrahedralK4_operatorGap
    (S : V →L[ℝ] W) (U : Fin 6 → V ≃ₗᵢ[ℝ] V)
    (E : Fin 6 → V →L[ℝ] V) (f : Fin 4 → V)
    (m M δ ε : ℝ)
    (hsum : f 0 + f 1 + f 2 + f 3 = 0)
    (hm : ∀ x, m * ‖x‖ ^ 2 ≤ ‖S x‖ ^ 2)
    (hM : 0 ≤ M) (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (htree0 : U 0 = LinearIsometryEquiv.refl ℝ V)
    (htree1 : U 1 = LinearIsometryEquiv.refl ℝ V)
    (htree2 : U 2 = LinearIsometryEquiv.refl ℝ V)
    (h₁₂ : ‖S (f 2 - f 1)‖ ^ 2 ≤
      ‖S (f 2 - U 3 (f 1))‖ ^ 2 + M * δ * (‖f 1‖ ^ 2 + ‖f 2‖ ^ 2))
    (h₁₃ : ‖S (f 3 - f 1)‖ ^ 2 ≤
      ‖S (f 3 - U 4 (f 1))‖ ^ 2 + M * δ * (‖f 1‖ ^ 2 + ‖f 3‖ ^ 2))
    (h₂₃ : ‖S (f 3 - f 2)‖ ^ 2 ≤
      ‖S (f 3 - U 5 (f 2))‖ ^ 2 + M * δ * (‖f 2‖ ^ 2 + ‖f 3‖ ^ 2))
    (hE : ∀ e, ‖E e‖ ≤ ε) :
    (4 * m - 2 * M * δ - 6 * ε) * (∑ i : Fin 4, ‖f i‖ ^ 2)
      ≤ k4ActualRouterEnergy S U E f := by
  let nf : ℝ := ∑ i : Fin 4, ‖f i‖ ^ 2
  have hSsum : S (f 0) + S (f 1) + S (f 2) + S (f 3) = 0 := by
    rw [← map_add, ← map_add, ← map_add, hsum, map_zero]
  have hflat := (tetrahedral_prototype_gap (V := W)).1 (fun i => S (f i)) hSsum
  have hflatLower : 4 * m * nf ≤
      ‖S (f 1 - f 0)‖ ^ 2 + ‖S (f 2 - f 0)‖ ^ 2 +
      ‖S (f 3 - f 0)‖ ^ 2 + ‖S (f 2 - f 1)‖ ^ 2 +
      ‖S (f 3 - f 1)‖ ^ 2 + ‖S (f 3 - f 2)‖ ^ 2 := by
    rw [map_sub, map_sub, map_sub, map_sub, map_sub, map_sub, hflat]
    dsimp [nf]
    have hs := Finset.sum_le_sum fun i (_ : i ∈ (Finset.univ : Finset (Fin 4))) => hm (f i)
    simp only [Fin.sum_univ_four] at hs ⊢
    linarith
  have hideal : 4 * m * nf ≤
      k4IdealRouterEnergy S U f + 2 * M * δ * nf := by
    let tree : ℝ := ‖S (f 1 - f 0)‖ ^ 2 + ‖S (f 2 - f 0)‖ ^ 2 +
      ‖S (f 3 - f 0)‖ ^ 2
    let flatNT : ℝ := ‖S (f 2 - f 1)‖ ^ 2 + ‖S (f 3 - f 1)‖ ^ 2 +
      ‖S (f 3 - f 2)‖ ^ 2
    let idealNT : ℝ := ‖S (f 2 - U 3 (f 1))‖ ^ 2 +
      ‖S (f 3 - U 4 (f 1))‖ ^ 2 + ‖S (f 3 - U 5 (f 2))‖ ^ 2
    let errLeaf : ℝ :=
      2 * M * δ * (‖f 1‖ ^ 2 + ‖f 2‖ ^ 2 + ‖f 3‖ ^ 2)
    let errAll : ℝ := 2 * M * δ * nf
    have hflatLower' : 4 * m * nf ≤ tree + flatNT := by
      simpa only [tree, flatNT, add_assoc] using hflatLower
    have hnonTree :
        flatNT ≤ idealNT + errLeaf := by
      dsimp [flatNT, idealNT, errLeaf]
      linarith
    have hf0 : 0 ≤ ‖f 0‖ ^ 2 := sq_nonneg _
    have hleaf : errLeaf ≤ errAll := by
      have hsums : ‖f 1‖ ^ 2 + ‖f 2‖ ^ 2 + ‖f 3‖ ^ 2 ≤
          ‖f 0‖ ^ 2 + ‖f 1‖ ^ 2 + ‖f 2‖ ^ 2 + ‖f 3‖ ^ 2 := by
        linarith
      dsimp [errLeaf, errAll, nf]
      simp only [Fin.sum_univ_four]
      exact mul_le_mul_of_nonneg_left hsums (by positivity)
    have hchain : 4 * m * nf ≤ tree + idealNT + errAll := by
      calc
        4 * m * nf ≤ tree + flatNT := hflatLower'
        _ ≤ tree + (idealNT + errLeaf) := by
          simpa only [add_comm] using add_le_add_left hnonTree tree
        _ = tree + idealNT + errLeaf := by ring
        _ ≤ tree + idealNT + errAll := by
          simpa only [add_comm] using add_le_add_left hleaf (tree + idealNT)
    unfold k4IdealRouterEnergy k4RouterDefect
    simp [Fin.sum_univ_six, k4EdgeSource, k4EdgeTarget,
      htree0, htree1, htree2]
    simpa only [tree, idealNT, errAll, add_assoc, map_sub] using hchain
  have hactual := k4ActualEnergy_lower_ideal S U E f ε hε hE
  calc
    (4 * m - 2 * M * δ - 6 * ε) * (∑ i : Fin 4, ‖f i‖ ^ 2)
        = 4 * m * nf - 2 * M * δ * nf - 6 * ε * nf := by
          dsimp [nf]
          ring
    _ ≤ k4IdealRouterEnergy S U f - 6 * ε * nf := by
      linarith only [hideal]
    _ ≤ k4ActualRouterEnergy S U E f := by
      simpa only [nf] using hactual

end

end NCG
