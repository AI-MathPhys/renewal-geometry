/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.GTMobiusSecants
import NCG.Grand.CompleteConnectedOccurrenceSectorExact
import NCG.Grand.GTHellingerFisher
import NCG.Grand.RectangularFundamentalTheorem

/-!
# Physical Hellinger subset secants

This file supplies the physical specializations missing from
`thm:GT-subset-secants`.  In particular it records the normalization forced by
the manuscript's convention `𝔥(p) = 2√p`: on an independent product cube the
all-slot secant is `2^(1-|A|)` times the ordinary tensor product of the
one-slot secants.
-/

open Finset Matrix Filter
open scoped BigOperators ComplexOrder
open scoped Topology

namespace NCG

/-- Boolean vertex product on a finite set of intervention slots. -/
def booleanVertexProduct {ι R : Type*} [DecidableEq ι] [CommRing R]
    (x₀ x₁ : ι → R) (A B : Finset ι) : R :=
  ∏ i ∈ A, if i ∈ B then x₁ i else x₀ i

/-- The top Boolean Möbius coefficient of a product cube factors into the
product of its one-slot differences. -/
theorem alternating_booleanVertexProduct {ι R : Type*}
    [DecidableEq ι] [CommRing R]
    (x₀ x₁ : ι → R) (A : Finset ι) :
    ∑ B ∈ A.powerset,
        (-1 : R) ^ (#A - #B) * booleanVertexProduct x₀ x₁ A B
      = ∏ i ∈ A, (x₁ i - x₀ i) := by
  classical
  induction A using Finset.induction_on with
  | empty => simp [booleanVertexProduct]
  | @insert a A ha ih =>
      rw [Finset.sum_powerset_insert ha, ← Finset.sum_add_distrib]
      simp only [Finset.card_insert_of_notMem ha]
      have hsub : ∀ B ∈ A.powerset, #B ≤ #A := fun B hB =>
        Finset.card_le_card (Finset.mem_powerset.mp hB)
      calc
        ∑ B ∈ A.powerset,
            ((-1 : R) ^ (#A + 1 - #B) *
                booleanVertexProduct x₀ x₁ (insert a A) B +
              (-1 : R) ^ (#A + 1 - #(insert a B)) *
                booleanVertexProduct x₀ x₁ (insert a A) (insert a B))
            = ∑ B ∈ A.powerset,
                ((x₁ a - x₀ a) *
                  ((-1 : R) ^ (#A - #B) *
                    booleanVertexProduct x₀ x₁ A B)) := by
                apply Finset.sum_congr rfl
                intro B hB
                have haB : a ∉ B := fun hab => ha
                  (Finset.mem_powerset.mp hB hab)
                have hBA : #B ≤ #A := hsub B hB
                have hcard₁ : #A + 1 - #B = (#A - #B) + 1 := by
                  omega
                have hcard₂ : #A + 1 - #(insert a B) = #A - #B := by
                  rw [Finset.card_insert_of_notMem haB]
                  omega
                have hv₀ : booleanVertexProduct x₀ x₁ (insert a A) B =
                    x₀ a * booleanVertexProduct x₀ x₁ A B := by
                  rw [booleanVertexProduct, Finset.prod_insert ha]
                  simp [haB, booleanVertexProduct]
                have hv₁ : booleanVertexProduct x₀ x₁ (insert a A) (insert a B) =
                    x₁ a * booleanVertexProduct x₀ x₁ A B := by
                  rw [booleanVertexProduct, Finset.prod_insert ha]
                  simp only [Finset.mem_insert, true_or, ↓reduceIte,
                    booleanVertexProduct]
                  congr 1
                  apply Finset.prod_congr rfl
                  intro i hi
                  have hia : i ≠ a := fun hia => ha (hia ▸ hi)
                  simp [hia]
                rw [hcard₁, hcard₂, pow_succ]
                rw [hv₀, hv₁]
                ring
        _ = (x₁ a - x₀ a) * ∏ i ∈ A, (x₁ i - x₀ i) := by
              rw [← Finset.mul_sum, ih]
        _ = ∏ i ∈ insert a A, (x₁ i - x₀ i) := by
              rw [Finset.prod_insert ha]

/-- Coordinate of the Hellinger embedding at a vertex of an independent
product intervention cube. -/
noncomputable def independentHellingerVertex {ι : Type*} [DecidableEq ι]
    (p₀ p₁ : ι → ℝ) (A B : Finset ι) : ℝ :=
  2 * Real.sqrt (booleanVertexProduct p₀ p₁ A B)

/-- Exact independent-occurrence factorization at one sample coordinate.

The second equality exposes the normalization: the ordinary product of the
one-slot Hellinger secants is `2^|A|` times the product of square-root
differences, whereas the all-slot secant carries only the single global factor
`2` from `𝔥(p)=2√p`. -/
theorem independent_hellinger_allSlot_secant {ι : Type*}
    [DecidableEq ι]
    (p₀ p₁ : ι → ℝ) (A : Finset ι)
    (hp₀ : ∀ i ∈ A, 0 ≤ p₀ i) (hp₁ : ∀ i ∈ A, 0 ≤ p₁ i) :
    (∑ B ∈ A.powerset,
        (-1 : ℝ) ^ (#A - #B) * independentHellingerVertex p₀ p₁ A B
      = 2 * ∏ i ∈ A, (Real.sqrt (p₁ i) - Real.sqrt (p₀ i)))
    ∧ ((∏ i ∈ A,
          (2 * Real.sqrt (p₁ i) - 2 * Real.sqrt (p₀ i)))
        = (2 : ℝ) ^ #A *
          ∏ i ∈ A, (Real.sqrt (p₁ i) - Real.sqrt (p₀ i))) := by
  constructor
  · have hsqrt : ∀ B ∈ A.powerset,
        independentHellingerVertex p₀ p₁ A B =
          2 * booleanVertexProduct
            (fun i => Real.sqrt (p₀ i))
            (fun i => Real.sqrt (p₁ i)) A B := by
      intro B hB
      have hnonneg : ∀ i ∈ A,
          0 ≤ (if i ∈ B then p₁ i else p₀ i) := by
        intro i hi
        by_cases hiB : i ∈ B
        · simp [hiB, hp₁ i hi]
        · simp [hiB, hp₀ i hi]
      rw [independentHellingerVertex, booleanVertexProduct,
        Real.sqrt_prod A hnonneg]
      congr 1
      apply Finset.prod_congr rfl
      intro i hi
      by_cases hiB : i ∈ B <;> simp [booleanVertexProduct, hiB]
    calc
      ∑ B ∈ A.powerset,
          (-1 : ℝ) ^ (#A - #B) * independentHellingerVertex p₀ p₁ A B
          = ∑ B ∈ A.powerset,
              (-1 : ℝ) ^ (#A - #B) *
                (2 * booleanVertexProduct
                  (fun i => Real.sqrt (p₀ i))
                  (fun i => Real.sqrt (p₁ i)) A B) := by
                    apply Finset.sum_congr rfl
                    intro B hB
                    rw [hsqrt B hB]
      _ = 2 * ∑ B ∈ A.powerset,
              (-1 : ℝ) ^ (#A - #B) *
                booleanVertexProduct
                  (fun i => Real.sqrt (p₀ i))
                  (fun i => Real.sqrt (p₁ i)) A B := by
                    rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro B hB
                    ring
      _ = 2 * ∏ i ∈ A,
              (Real.sqrt (p₁ i) - Real.sqrt (p₀ i)) := by
                    rw [alternating_booleanVertexProduct]
  · calc
      ∏ i ∈ A, (2 * Real.sqrt (p₁ i) - 2 * Real.sqrt (p₀ i))
          = ∏ i ∈ A, (2 * (Real.sqrt (p₁ i) - Real.sqrt (p₀ i))) := by
              apply Finset.prod_congr rfl
              intro i hi
              ring
      _ = (∏ _i ∈ A, (2 : ℝ)) *
            ∏ i ∈ A, (Real.sqrt (p₁ i) - Real.sqrt (p₀ i)) := by
              rw [← Finset.prod_mul_distrib]
      _ = (2 : ℝ) ^ #A *
            ∏ i ∈ A, (Real.sqrt (p₁ i) - Real.sqrt (p₀ i)) := by
              simp

/-! ## Smooth physical cubes and the all-support Hellinger tangent -/

/-- Pointwise square-root family of a finite law-valued parameter family. -/
noncomputable def squareRootLawFamily {Ω : Type*} {n : ℕ}
    (p : (Fin n → ℝ) → Ω → ℝ) : (Fin n → ℝ) → Ω → ℝ :=
  fun θ ω => Real.sqrt (p θ ω)

/-- The manuscript's Hellinger embedding `𝔥(p)=2√p`, as a Banach-valued
parameter family. -/
noncomputable def hellingerLawFamily {Ω : Type*} {n : ℕ}
    (p : (Fin n → ℝ) → Ω → ℝ) : (Fin n → ℝ) → Ω → ℝ :=
  fun θ => (2 : ℝ) • squareRootLawFamily p θ

/-- For an independently physical `C^n` full-support family, the normalized
top subset secant converges to `2` times the ordered mixed derivative of
`√p`.  Side lengths may approach zero at arbitrary relative rates; only the
coordinate hyperplanes, where the normalization is undefined, are removed. -/
theorem hellinger_finsetCubeMobiusSecant_tendsto_mixedSqrtDerivative
    {Ω : Type*} [Fintype Ω] {n : ℕ}
    (p : (Fin n → ℝ) → Ω → ℝ)
    (_hp : ∀ θ ω, 0 < p θ ω)
    (D : OrderedDerivativeTower n (squareRootLawFamily p)) :
    Tendsto
      (fun h : Fin n → ℝ =>
        (∏ i, h i)⁻¹ •
          finsetCubeMobiusSecant n (hellingerLawFamily p) h)
      (𝓝[{h | ∀ i, h i ≠ 0}] (0 : Fin n → ℝ))
      (𝓝 ((2 : ℝ) • D.top 0)) := by
  let DH : OrderedDerivativeTower n (hellingerLawFamily p) := by
    change OrderedDerivativeTower n
      (fun θ => (2 : ℝ) • squareRootLawFamily p θ)
    exact D.const_smul (2 : ℝ)
  have ht := normalized_orderedCubeSecant_tendsto_top
    n (hellingerLawFamily p) DH
  have htm : Tendsto
      (fun h : Fin n → ℝ =>
        (∏ i, h i)⁻¹ •
          finsetCubeMobiusSecant n (hellingerLawFamily p) h)
      (𝓝[{h | ∀ i, h i ≠ 0}] (0 : Fin n → ℝ))
      (𝓝 (DH.top 0)) := by
    simpa only [orderedCubeSecant_eq_finsetCubeMobiusSecant] using ht
  convert htm using 1
  apply congrArg nhds
  change (2 : ℝ) • D.top 0 = (D.const_smul (2 : ℝ)).top 0
  rfl

/-- Simultaneous proper-support and nuisance shorting of a tangent bank.

The Hoeffding short first replaces the sum of all proper support grades by the
canonical top-support projector.  The nuisance projection is then taken inside
that retained range, yielding the Schur formula and a positive semidefinite
efficient Fisher Gram. -/
theorem properSupport_nuisanceShort_canonicalPositiveFisher
    {n m k : Type} [Fintype n] [Fintype m] [Fintype k]
    [DecidableEq n] [DecidableEq m]
    (t : ℕ) (P Q : Matrix n n ℂ)
    (hPQ1 : P + Q = 1) (hPQ : P * Q = 0) (hQP : Q * P = 0)
    (hPP : P * P = P) (hQQ : Q * Q = Q)
    (N₀ : Matrix (Fin t → n) m ℂ)
    (Tangent : Matrix (Fin t → n) k ℂ)
    [Invertible
      ((tensorPow t (fun _ => Q) * N₀)ᴴ *
        (tensorPow t (fun _ => Q) * N₀))] :
    let Pi : Finset (Fin t) →
        Matrix (Fin t → n) (Fin t → n) ℂ :=
      fun S => tensorPow t (fun i => if i ∈ S then Q else P)
    let Qtop := tensorPow t (fun _ => Q)
    let N := Qtop * N₀
    let S := Qtop * Tangent
    (∀ {r : Type} (Z : Matrix (Fin t → n) r ℂ),
      Zᴴ * (1 - ∑ A ∈ (Finset.univ : Finset (Finset (Fin t))).erase
          (Finset.univ : Finset (Fin t)), Pi A) * Z =
        Zᴴ * Qtop * Z)
    ∧ (Sᴴ * (1 - N * ((Nᴴ * N)⁻¹ * Nᴴ)) * S =
          Sᴴ * S - (Sᴴ * N) * ((Nᴴ * N)⁻¹ * (Nᴴ * S)))
    ∧ (Sᴴ * (1 - N * ((Nᴴ * N)⁻¹ * Nᴴ)) * S).PosSemidef := by
  dsimp only
  constructor
  · exact (gt_hoeffding_short t P Q hPQ1 hPQ hQP hPP hQQ).2.2.2.2.2
  · exact gt_hellinger_shorted_gram
      (tensorPow t (fun _ => Q) * N₀)
      (tensorPow t (fun _ => Q) * Tangent)

end NCG
