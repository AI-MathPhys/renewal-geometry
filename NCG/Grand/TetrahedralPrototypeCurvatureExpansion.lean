/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.TetrahedralConnection

/-!
# Tetrahedral prototype curvature expansion and real-fibre obstruction

This module completes the analytic and explicit representation-theoretic parts
of `thm:tetrahedral-prototype-connection` that are not present in the elementary
orbit-product core.

* `exp_secondOrder_remainder_isBigO` is the genuine Banach-algebra exponential
  Taylor theorem with cubic remainder.
* `tetrahedral_prototype_connection` (re-exported from the core module)
  identifies the ordered second-order coefficient with the commutator.
* the `standardK`, `standardS`, and `standardR` calculations are the concrete
  untwisted real `S₄` standard-fibre computation: the stabilizer and reversal
  conditions leave only `ℝ(e₃-e₄)`, whose order-three orbit sum is
  `(1,1,1,-3)`, so area cancellation forces the generator to vanish.
-/

open Asymptotics Filter Finset Topology

namespace NCG

section PrototypeOrbit

variable {G M : Type*} [Group G] [Monoid M]

/-- Router obtained by transporting one prototype with a group
representation. -/
def transportedPrototype (ρ : G →* Units M) (U : Units M) (g : G) : Units M :=
  ρ g * U * (ρ g)⁻¹

/-- Choice-independence under an ordered-edge stabilizer element is exactly
commutation of the prototype with that stabilizer.  This is the abstract
one-orbit mechanism used for the `(34)` stabilizer of `(1,2)`. -/
theorem transportedPrototype_stabilizer_iff
    (ρ : G →* Units M) (U : Units M) (k : G) :
    transportedPrototype ρ U k = U ↔ Commute U (ρ k) := by
  constructor
  · intro h
    have hc := congrArg (fun z : Units M => z * ρ k) h
    have hk : ρ k * U = U * ρ k := by
      simpa [transportedPrototype, mul_assoc] using hc
    exact hk.symm
  · intro h
    unfold transportedPrototype
    rw [← h.eq]
    group

/-- Orientation reversal sends the prototype router to its inverse exactly
when the reversing symmetry intertwines `U` with `U⁻¹`.  For unitary routers,
inverse is adjoint, giving the manuscript's reversal equation. -/
theorem transportedPrototype_reversal_iff
    (ρ : G →* Units M) (U : Units M) (s : G) :
    transportedPrototype ρ U s = U⁻¹ ↔
      ρ s * U = U⁻¹ * ρ s := by
  constructor
  · intro h
    have hc := congrArg (fun z : Units M => z * ρ s) h
    simpa [transportedPrototype, mul_assoc] using hc
  · intro h
    unfold transportedPrototype
    rw [h]
    group

/-- Conjugation transports an ordered triangle product as a whole.  Thus all
triangles in one group orbit have conjugate holonomy. -/
theorem transportedPrototype_triangleProduct
    (ρ : G →* Units M) (U₁ U₂ U₃ : Units M) (g : G) :
    transportedPrototype ρ (U₁ * U₂ * U₃) g =
      transportedPrototype ρ U₁ g * transportedPrototype ρ U₂ g *
        transportedPrototype ρ U₃ g := by
  unfold transportedPrototype
  group

/-- Reversing an oriented triangle inverts its holonomy. -/
theorem reverseTriangleHolonomy (U₁ U₂ U₃ : Units M) :
    (U₁ * U₂ * U₃)⁻¹ = U₃⁻¹ * U₂⁻¹ * U₁⁻¹ := by
  group

end PrototypeOrbit

section ExponentialRemainder

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [CompleteSpace E]

/-- The matrix/Banach-algebra exponential has its actual second-order Taylor
polynomial with an `O(‖z‖³)` remainder. -/
theorem exp_secondOrder_remainder_isBigO :
    (fun z : E →L[ℂ] E => NormedSpace.exp z -
      (1 + z + (2 : ℂ)⁻¹ • z ^ 2))
      =O[𝓝 0] fun z : E →L[ℂ] E => ‖z‖ ^ 3 := by
  have h := (NormedSpace.exp_hasFPowerSeriesAt_zero
    (𝕂 := ℂ) (𝔸 := E →L[ℂ] E)).isBigO_sub_partialSum_pow 3
  refine h.congr' ?_ EventuallyEq.rfl
  filter_upwards with z
  simp only [zero_add]
  congr 1
  norm_num [FormalMultilinearSeries.partialSum,
    NormedSpace.expSeries_apply_eq, Finset.sum_range_succ]

end ExponentialRemainder

section StandardTetrahedralFibre

/-- The mean-zero standard tetrahedral fibre. -/
def TetrahedralStandardVector := {a : Fin 4 → ℝ // ∑ i, a i = 0}

/-- Coordinate action of the odd stabilizer `(34)` on the permutation
representation. -/
def standardK (a : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![a 0, a 1, a 3, a 2]

/-- Coordinate action of the odd edge reversal `(12)`. -/
def standardS (a : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![a 1, a 0, a 2, a 3]

/-- Coordinate action of the order-three element `(123)`, fixing vertex four. -/
def standardR (a : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![a 2, a 0, a 1, a 3]

/-- The unique possible generator line after the stabilizer and reversal
relations. -/
def e₃Sube₄ : Fin 4 → ℝ := ![0, 0, 1, -1]

/-- The stabilizer/reversal equations on the untwisted real standard fibre
leave exactly the line `ℝ(e₃-e₄)`. -/
theorem standard_stabilizer_reversal_line (a : Fin 4 → ℝ)
    (hk : standardK a = -a) (hs : standardS a = a) :
    ∃ t : ℝ, a = t • e₃Sube₄ := by
  have hk0 := congrFun hk 0
  have hk1 := congrFun hk 1
  have hk2 := congrFun hk 2
  have hk3 := congrFun hk 3
  have hs01 := congrFun hs 0
  simp [standardK] at hk0 hk1 hk2 hk3
  simp [standardS] at hs01
  refine ⟨a 2, ?_⟩
  funext i
  fin_cases i <;> simp [e₃Sube₄] <;> linarith

/-- The order-three orbit of `e₃-e₄` has the manuscript's explicit nonzero
sum `(1,1,1,-3)`. -/
theorem standard_orderThree_orbitSum :
    e₃Sube₄ + standardR e₃Sube₄ + standardR (standardR e₃Sube₄) =
      ![1, 1, 1, -3] := by
  funext i
  fin_cases i
  · change (0 : ℝ) + 1 + 0 = 1
    norm_num
  · change (0 : ℝ) + 0 + 1 = 1
    norm_num
  · change (1 : ℝ) + 0 + 0 = 1
    norm_num
  · change (-1 : ℝ) + -1 + -1 = -3
    norm_num

/-- The explicit orbit sum is nonzero. -/
theorem standard_orderThree_orbitSum_ne_zero :
    e₃Sube₄ + standardR e₃Sube₄ + standardR (standardR e₃Sube₄) ≠ 0 := by
  rw [standard_orderThree_orbitSum]
  intro h
  have h0 := congrFun h 0
  norm_num at h0

/-- On the bare untwisted real standard tetrahedral fibre, stabilizer,
reversal, and area cancellation force the infinitesimal connection generator
to vanish. -/
theorem standard_tetrahedral_denseConnection_noGo (a : Fin 4 → ℝ)
    (hk : standardK a = -a) (hs : standardS a = a)
    (harea : a + standardR a + standardR (standardR a) = 0) :
    a = 0 := by
  obtain ⟨t, rfl⟩ := standard_stabilizer_reversal_line a hk hs
  have h0 := congrFun harea 0
  simp [standardR, e₃Sube₄] at h0
  have ht : t = 0 := by linarith
  simp [ht]

/-- Scalar/trivial fibres have no nonzero infinitesimal area-scaled
connection: the orbit sum is three copies of the same generator. -/
theorem trivialFibre_areaCancellation_noGo (A : ℂ) (harea : A + A + A = 0) :
    A = 0 := by
  linear_combination (1 / 3 : ℂ) * harea

end StandardTetrahedralFibre

end NCG
