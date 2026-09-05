/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Rank-three cycle fibre (`thm:b1-three`, SM manuscript)

The cellular cochain complex of the complete graph `K₄` is
`C⁰ = ℂ⁴ → C¹ = ℂ⁶` with `(df)_{ij} = f_j − f_i` on the six
oriented edges `i < j`.  With no two-cells,
`H¹(K₄;ℂ) = C¹/im d`, and

* `k4_edge_card` — `K₄` has six edges;
* `finrank_k4_coboundary_ker` — the kernel of `d` is the
  one-dimensional space of constants (connectivity);
* `finrank_k4_H1` — `b₁(K₄) = 6 − 4 + 1 = 3`;
* `k4_H1_equiv` — the generation fibre `𝒦 = H¹(K₄;ℂ) ≅ ℂ³`.
-/

open Module

namespace NCG

/-- The six oriented edges `i < j` of `K₄`. -/
def K4Edge : Type := {p : Fin 4 × Fin 4 // p.1 < p.2}

noncomputable instance : Fintype K4Edge := by
  unfold K4Edge
  infer_instance

instance : DecidableEq K4Edge := by
  unfold K4Edge
  infer_instance

/-- `K₄` has six edges. -/
theorem k4_edge_card : Fintype.card K4Edge = 6 := by
  rw [show Fintype.card K4Edge
      = Fintype.card {p : Fin 4 × Fin 4 // p.1 < p.2} from rfl]
  decide

/-- The cellular coboundary `d : C⁰(K₄;ℂ) → C¹(K₄;ℂ)`,
`(df)_{ij} = f_j − f_i`. -/
noncomputable def k4Coboundary : (Fin 4 → ℂ) →ₗ[ℂ] (K4Edge → ℂ) where
  toFun f := fun e => f e.1.2 - f e.1.1
  map_add' f g := by
    funext e
    simp only [Pi.add_apply]
    ring
  map_smul' c f := by
    funext e
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- Connectivity: the kernel of the coboundary is the line of
constant functions. -/
theorem finrank_k4_coboundary_ker :
    finrank ℂ (LinearMap.ker k4Coboundary) = 1 := by
  -- the kernel is linearly equivalent to `ℂ` via evaluation at `0`
  have hmem : ∀ f : Fin 4 → ℂ, f ∈ LinearMap.ker k4Coboundary
      → ∀ i : Fin 4, f i = f 0 := by
    intro f hf i
    rcases eq_or_ne i 0 with rfl | hi
    · rfl
    · have h0i : (0 : Fin 4) < i := by
        exact Fin.pos_iff_ne_zero.mpr hi
      have := congrFun (LinearMap.mem_ker.mp hf) ⟨(0, i), h0i⟩
      simpa [k4Coboundary] using sub_eq_zero.mp this
  let e : LinearMap.ker k4Coboundary ≃ₗ[ℂ] ℂ :=
    { toFun := fun f => (f : Fin 4 → ℂ) 0
      map_add' := fun f g => rfl
      map_smul' := fun c f => rfl
      invFun := fun c => ⟨fun _ => c, by
        rw [LinearMap.mem_ker]
        funext e
        simp [k4Coboundary]⟩
      left_inv := fun f => by
        ext i
        exact (hmem f f.2 i).symm
      right_inv := fun c => rfl }
  rw [e.finrank_eq, finrank_self]

/-- `thm:b1-three` (rank-three cycle fibre): the first Betti number
of `K₄` is `6 − 4 + 1 = 3`. -/
theorem finrank_k4_H1 :
    finrank ℂ ((K4Edge → ℂ) ⧸ LinearMap.range k4Coboundary) = 3 := by
  have h0 : finrank ℂ (Fin 4 → ℂ) = 4 := by
    rw [Module.finrank_pi]
    simp
  have h1 : finrank ℂ (K4Edge → ℂ) = 6 := by
    rw [Module.finrank_pi, k4_edge_card]
  have hrange : finrank ℂ (LinearMap.range k4Coboundary) = 3 := by
    have h2 := LinearMap.finrank_range_add_finrank_ker k4Coboundary
    rw [h0, finrank_k4_coboundary_ker] at h2
    omega
  have hquot := Submodule.finrank_quotient_add_finrank
    (LinearMap.range k4Coboundary)
  rw [h1, hrange] at hquot
  omega

/-- The generation fibre `𝒦 = H¹(K₄;ℂ)` is three-dimensional:
`𝒦 ≅ ℂ³`. -/
theorem k4_H1_equiv :
    Nonempty (((K4Edge → ℂ) ⧸ LinearMap.range k4Coboundary)
      ≃ₗ[ℂ] (Fin 3 → ℂ)) := by
  have h1 := finrank_k4_H1
  have h2 : finrank ℂ (Fin 3 → ℂ) = 3 := by
    rw [Module.finrank_pi]
    simp
  exact ⟨LinearEquiv.ofFinrankEq _ _ (by rw [h1, h2])⟩

end NCG
