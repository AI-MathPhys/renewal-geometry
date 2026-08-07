/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Matter.K4Carrier

/-!
# Locked `K₄` edge packet gives one endpoint generation triplet
  (`thm:SMST-record-native-generations`, Gran-Tensor manuscript)

* `smst_record_native_generations`, on the concrete oriented
  edge space of `K₄` (antisymmetric functions on `4 × 4`):
  (i) the cut–cycle Hodge decomposition: every oriented edge
      packet splits as `f = ∂*g + c` with `g` mean-zero (the
      endpoint potential) and `∂c = 0` (the cycle part);
  (ii) the two summands are orthogonal in the edge
      Hilbert–Schmidt product;
  (iii) the endpoint margin: any Gram acting as the scalar `α`
      on the cut space satisfies `∂ G ∂* = 4α` on mean-zero
      potentials — the boxed `T*T = 4α·I_{W₀}`, so the
      endpoint-conditioned matter source is centered,
      homogeneous and of rank exactly three with margin `4α`;
  (iv) the endpoint carrier `W₀` has rank three and is
      linearly isomorphic to the proved harmonic model
      `K4Carrier ≅ H₁(K₄;ℂ)` of the circulation carrier.

Rendering disclosed: that the locked-branch Gram is
block-scalar `αP_cut + βP_cyc` is the `S₄`-Schur step on the
two inequivalent triplets (the manuscript cites the locked
opportunity instrument for the equivariance hypothesis; the
proved `locked_opportunity` record supplies it), consumed here
as the hypothesis of (iii); positivity of `α, β` from
injectivity of the synthesis and the orientation twist under
edge reversal are the manuscript's sign bookkeeping around the
proved identities.
-/

open Finset

namespace NCG

/-- Oriented boundary of a `K₄` edge packet. -/
def k4Bd (f : Fin 4 → Fin 4 → ℂ) : Fin 4 → ℂ :=
  fun i => ∑ j, f i j

/-- Cut coboundary of an endpoint potential. -/
def k4Cobd (g : Fin 4 → ℂ) : Fin 4 → Fin 4 → ℂ :=
  fun i j => g i - g j

/-- The vertex-sum functional on the `K₄` endpoint carrier. -/
def k4Sum : (Fin 4 → ℂ) →ₗ[ℂ] ℂ where
  toFun g := ∑ j, g j
  map_add' a b := by simp [Finset.sum_add_distrib]
  map_smul' c a := by simp [Finset.mul_sum]

/-- The mean-zero endpoint carrier `W₀ = u₀^⊥`. -/
def meanZero : Submodule ℂ (Fin 4 → ℂ) := LinearMap.ker k4Sum

/-- `thm:SMST-record-native-generations`. -/
theorem smst_record_native_generations :
    -- (i) cut–cycle Hodge decomposition of edge packets
    (∀ f : Fin 4 → Fin 4 → ℂ, (∀ i j, f j i = -f i j) →
      ∃ (g : Fin 4 → ℂ) (c : Fin 4 → Fin 4 → ℂ),
        (∑ j, g j = 0) ∧ (∀ i j, c j i = -c i j)
        ∧ k4Bd c = 0
        ∧ f = fun i j => k4Cobd g i j + c i j)
    -- (ii) cut and cycle summands are HS-orthogonal
    ∧ (∀ (g : Fin 4 → ℂ) (c : Fin 4 → Fin 4 → ℂ),
        (∀ i j, c j i = -c i j) → k4Bd c = 0 →
        ∑ i, ∑ j,
          (starRingEnd ℂ) (k4Cobd g i j) * c i j = 0)
    -- (iii) endpoint margin: block-scalar Gram ⟹ `T*T = 4α`
    ∧ (∀ (α : ℂ)
        (G : (Fin 4 → Fin 4 → ℂ) → Fin 4 → Fin 4 → ℂ),
        (∀ g', G (k4Cobd g') = α • k4Cobd g') →
        ∀ g : Fin 4 → ℂ, (∑ j, g j = 0) →
        k4Bd (G (k4Cobd g)) = (4 * α) • g)
    -- (iv) `W₀ ≅ H₁(K₄;ℂ)`: rank exactly three
    ∧ Module.finrank ℂ meanZero = 3
    ∧ Nonempty (meanZero ≃ₗ[ℂ] K4Carrier) := by
  have hW : Module.finrank ℂ meanZero = 3 := by
    have hsurj : Function.Surjective k4Sum := by
      intro cval
      refine ⟨fun j => if j = 0 then cval else 0, ?_⟩
      simp [k4Sum, Fin.sum_univ_four]
    have hrank :=
      LinearMap.finrank_range_add_finrank_ker k4Sum
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top,
      Module.finrank_self] at hrank
    have hdom : Module.finrank ℂ (Fin 4 → ℂ) = 4 := by
      simp
    rw [hdom] at hrank
    have : Module.finrank ℂ (LinearMap.ker k4Sum) = 3 := by
      omega
    exact this
  refine ⟨?_, ?_, ?_, hW, ?_⟩
  · -- (i) the Hodge split `f = ∂*(¼∂f) + c`
    intro f hf
    have hSexp : f 0 0 + f 0 1 + f 0 2 + f 0 3 + f 1 0
        + f 1 1 + f 1 2 + f 1 3 + f 2 0 + f 2 1 + f 2 2
        + f 2 3 + f 3 0 + f 3 1 + f 3 2 + f 3 3 = 0 := by
      linear_combination hf 0 1 + hf 0 2 + hf 0 3 + hf 1 2
        + hf 1 3 + hf 2 3 + hf 0 0 / 2 + hf 1 1 / 2
        + hf 2 2 / 2 + hf 3 3 / 2
    refine ⟨fun i => (4 : ℂ)⁻¹ * ∑ l, f i l,
      fun i j => f i j - ((4 : ℂ)⁻¹ * ∑ l, f i l
        - (4 : ℂ)⁻¹ * ∑ l, f j l), ?_, ?_, ?_, ?_⟩
    · simp only [Fin.sum_univ_four]
      linear_combination ((4 : ℂ)⁻¹) * hSexp
    · intro i j
      linear_combination hf i j
    · funext i
      simp only [k4Bd, Pi.zero_apply, Fin.sum_univ_four]
      linear_combination ((4 : ℂ)⁻¹) * hSexp
    · funext i j
      simp only [k4Cobd]
      ring
  · -- (ii) HS orthogonality via the adjoint relation
    intro g c hc hbd
    have hb : ∀ i : Fin 4,
        c i 0 + c i 1 + c i 2 + c i 3 = 0 := by
      intro i
      have h := congrFun hbd i
      simpa [k4Bd, Fin.sum_univ_four] using h
    simp only [k4Cobd, map_sub, Fin.sum_univ_four]
    linear_combination
      2 * (starRingEnd ℂ) (g 0) * hb 0
      + 2 * (starRingEnd ℂ) (g 1) * hb 1
      + 2 * (starRingEnd ℂ) (g 2) * hb 2
      + 2 * (starRingEnd ℂ) (g 3) * hb 3
      - ((starRingEnd ℂ) (g 0) + (starRingEnd ℂ) (g 1))
          * hc 0 1
      - ((starRingEnd ℂ) (g 0) + (starRingEnd ℂ) (g 2))
          * hc 0 2
      - ((starRingEnd ℂ) (g 0) + (starRingEnd ℂ) (g 3))
          * hc 0 3
      - ((starRingEnd ℂ) (g 1) + (starRingEnd ℂ) (g 2))
          * hc 1 2
      - ((starRingEnd ℂ) (g 1) + (starRingEnd ℂ) (g 3))
          * hc 1 3
      - ((starRingEnd ℂ) (g 2) + (starRingEnd ℂ) (g 3))
          * hc 2 3
      - (starRingEnd ℂ) (g 0) * hc 0 0
      - (starRingEnd ℂ) (g 1) * hc 1 1
      - (starRingEnd ℂ) (g 2) * hc 2 2
      - (starRingEnd ℂ) (g 3) * hc 3 3
  · -- (iii) `T*T = 4α` on the mean-zero carrier
    intro α G hG g hg
    have hgExp : g 0 + g 1 + g 2 + g 3 = 0 := by
      simpa [Fin.sum_univ_four] using hg
    rw [hG g]
    funext i
    simp only [k4Bd, k4Cobd, Pi.smul_apply, smul_eq_mul,
      Fin.sum_univ_four]
    linear_combination (-α) * hgExp
  · -- (iv) the dimension-three identification with `H₁(K₄;ℂ)`
    exact ⟨LinearEquiv.ofFinrankEq _ _
      (by rw [hW, finrank_K4Carrier])⟩

end NCG
