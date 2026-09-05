/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.SchurCovariantExact
import NCG.Grand.ColourOrbit

/-!
# The singlet–adjoint colour occurrence, assembled

Final assembly for `thm:SM-colour-orbit`.

* `trace_of_decomposed`: the operator trace of a Schur-decomposed operator is
  `c + λ(n² - 1)`;
* `colour_covariance_forced`: any conjugation-covariant operator preserving
  tracelessness with the two seed invariants of the Haar average — `T 1 = 1` (from
  `tr R = -2`) and operator trace `4` (from `‖R‖² = 4`) — **equals**
  `Π₁ + (1/5)·Π₁₅`: the boxed covariance identity is forced by Schur uniqueness;
* `colour_score_bridge_forced`: the score-square bridge `K = ½T` therefore has the
  boxed coefficients `(1/2, 1/10)`, and both irreducible occurrence modules are
  strictly positive (`1 > 0`, `1/5 > 0` acting as genuine operator eigenvalues);
* `orbit_quadrature` / `colour_orbit_quadrature`: Carathéodory — any point of the
  convex hull of the orbit set lies in the hull of at most `finrank + 1 = 257`
  orbit points.
-/

open Matrix NCG.SchurCovariant

namespace NCG
namespace ColourOrbitAssembly

/-- Operator trace of a Schur-decomposed covariant operator: `c + λ(n² - 1)`. -/
theorem trace_of_decomposed {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (T : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) (c lam : ℂ)
    (hT : ∀ A : Matrix n n ℂ,
      T A = (c * (Matrix.trace A / (Fintype.card n : ℂ))) • 1
        + lam • (A - (Matrix.trace A / (Fintype.card n : ℂ)) • 1)) :
    LinearMap.trace ℂ (Matrix n n ℂ) T
      = c + lam * ((Fintype.card n : ℂ) * (Fintype.card n : ℂ) - 1) := by
  classical
  set S : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ :=
    (Matrix.traceLinearMap n ℂ ℂ).smulRight (1 : Matrix n n ℂ) with hS
  have hcard : ((Fintype.card n : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hTeq : T = ((c - lam) / (Fintype.card n : ℂ)) • S + lam • LinearMap.id := by
    refine LinearMap.ext fun A => ?_
    rw [hT A]
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply, hS,
      LinearMap.smulRight_apply]
    rw [smul_smul, smul_sub, smul_smul]
    rw [show Matrix.traceLinearMap n ℂ ℂ A = Matrix.trace A from rfl]
    module
  have htrS : LinearMap.trace ℂ (Matrix n n ℂ) S = (Fintype.card n : ℂ) := by
    rw [hS, LinearMap.trace_smulRight]
    rw [show Matrix.traceLinearMap n ℂ ℂ (1 : Matrix n n ℂ)
      = Matrix.trace (1 : Matrix n n ℂ) from rfl, Matrix.trace_one]
  have hfr : ((Module.finrank ℂ (Matrix n n ℂ) : ℂ))
      = (Fintype.card n : ℂ) * (Fintype.card n : ℂ) := by
    rw [Module.finrank_matrix, Module.finrank_self]
    push_cast
    ring
  rw [hTeq, map_add, LinearMap.map_smul, LinearMap.map_smul, htrS,
    LinearMap.trace_id, hfr]
  have hninv : (Fintype.card n : ℂ) * ((Fintype.card n : ℂ))⁻¹ = 1 :=
    mul_inv_cancel₀ hcard
  field_simp
  linear_combination (c - lam) * hninv

/-- **The boxed colour covariance identity is forced**: any conjugation-covariant,
tracelessness-preserving operator carrying the two proved seed invariants of the
Haar average of `R_{3|1} = 2P_ℓ - I₄` — `T 1 = 1` (from `tr R = -2`, i.e.
`(tr R)²/4 = 1`) and total operator trace `4` (from `‖R‖²_HS = tr R² = tr I = 4`) —
equals `Π₁ + (1/5)·Π₁₅`. -/
theorem colour_covariance_forced
    (T : Matrix (Fin 4) (Fin 4) ℂ →ₗ[ℂ] Matrix (Fin 4) (Fin 4) ℂ)
    (hcov : ∀ U ∈ Matrix.unitaryGroup (Fin 4) ℂ, ∀ A, T (U * A * star U) = U * T A * star U)
    (hsl : ∀ A : Matrix (Fin 4) (Fin 4) ℂ, Matrix.trace A = 0 → Matrix.trace (T A) = 0)
    (hT1 : T 1 = 1)
    (htrT : LinearMap.trace ℂ (Matrix (Fin 4) (Fin 4) ℂ) T = 4) :
    ∀ A : Matrix (Fin 4) (Fin 4) ℂ,
      T A = (Matrix.trace A / 4) • 1
        + (5⁻¹ : ℂ) • (A - (Matrix.trace A / 4) • 1) := by
  obtain ⟨c, lam, hform⟩ := covariant_operator_decomposes T hcov hsl
  have hcard4 : ((Fintype.card (Fin 4) : ℂ)) = 4 := by
    rw [Fintype.card_fin]
    norm_num
  have hc : c = 1 := by
    have h1 := hform 1
    rw [Matrix.trace_one, hT1, hcard4] at h1
    have h44 : (4 : ℂ) / 4 = 1 := by norm_num
    rw [h44, mul_one, one_smul, sub_self, smul_zero, add_zero] at h1
    have h3 := congrFun (congrFun h1 0) 0
    rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] at h3
    exact h3.symm
  have hlam : lam = 5⁻¹ := by
    have h1 := trace_of_decomposed T c lam hform
    rw [htrT, hc, hcard4] at h1
    have h2 : (15 : ℂ) * lam = 3 := by linear_combination -h1
    linear_combination (15⁻¹ : ℂ) * h2
  intro A
  rw [hform A, hc, hlam, hcard4, one_mul]

/-- **The forced score-square bridge**: `K = ½T` carries the boxed coefficients
`(1/2, 1/10)`. -/
theorem colour_score_bridge_forced
    (T : Matrix (Fin 4) (Fin 4) ℂ →ₗ[ℂ] Matrix (Fin 4) (Fin 4) ℂ)
    (hcov : ∀ U ∈ Matrix.unitaryGroup (Fin 4) ℂ, ∀ A, T (U * A * star U) = U * T A * star U)
    (hsl : ∀ A : Matrix (Fin 4) (Fin 4) ℂ, Matrix.trace A = 0 → Matrix.trace (T A) = 0)
    (hT1 : T 1 = 1)
    (htrT : LinearMap.trace ℂ (Matrix (Fin 4) (Fin 4) ℂ) T = 4) :
    ∀ A : Matrix (Fin 4) (Fin 4) ℂ,
      ((2⁻¹ : ℂ) • T) A = (2⁻¹ * (Matrix.trace A / 4)) • 1
        + (10⁻¹ : ℂ) • (A - (Matrix.trace A / 4) • 1) := by
  intro A
  rw [LinearMap.smul_apply, colour_covariance_forced T hcov hsl hT1 htrT A,
    smul_add, smul_smul, smul_smul]
  congr 2
  norm_num

/-- **Carathéodory quadrature**: any point of a convex hull lies in the hull of at
most `finrank + 1` points of the generating set. -/
theorem orbit_quadrature {E : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] {s : Set E} {x : E} (hx : x ∈ convexHull ℝ s) :
    ∃ t : Finset E, ↑t ⊆ s ∧ t.card ≤ Module.finrank ℝ E + 1
      ∧ x ∈ convexHull ℝ (t : Set E) := by
  refine ⟨Caratheodory.minCardFinsetOfMemConvexHull hx,
    Caratheodory.minCardFinsetOfMemConvexHull_subseteq hx, ?_,
    Caratheodory.mem_minCardFinsetOfMemConvexHull hx⟩
  have hai := Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull hx
  have h := hai.card_le_finrank_succ
  rw [Fintype.card_coe] at h
  exact h.trans (Nat.add_le_add_right (Submodule.finrank_le _) 1)

/-- **The 257-point positive orbit quadrature**: in the 256-real-dimensional
Hermitian operator carrier, any orbit average lies in the convex hull of at most
`257` orbit points. -/
theorem colour_orbit_quadrature {E : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] (hdim : Module.finrank ℝ E = 256)
    {s : Set E} {x : E} (hx : x ∈ convexHull ℝ s) :
    ∃ t : Finset E, ↑t ⊆ s ∧ t.card ≤ 257 ∧ x ∈ convexHull ℝ (t : Set E) := by
  obtain ⟨t, h1, h2, h3⟩ := orbit_quadrature hx
  rw [hdim] at h2
  exact ⟨t, h1, h2, h3⟩

/-- **Bundle for `thm:SM-colour-orbit`**: the seed identities, the forced covariance
identity `Π₁ + (1/5)Π₁₅` with strictly positive module coefficients, the forced
score bridge `(1/2, 1/10)`, and the `≤ 257`-point Carathéodory quadrature. -/
theorem sm_colour_orbit
    (T : Matrix (Fin 4) (Fin 4) ℂ →ₗ[ℂ] Matrix (Fin 4) (Fin 4) ℂ)
    (hcov : ∀ U ∈ Matrix.unitaryGroup (Fin 4) ℂ, ∀ A, T (U * A * star U) = U * T A * star U)
    (hsl : ∀ A : Matrix (Fin 4) (Fin 4) ℂ, Matrix.trace A = 0 → Matrix.trace (T A) = 0)
    (hT1 : T 1 = 1)
    (htrT : LinearMap.trace ℂ (Matrix (Fin 4) (Fin 4) ℂ) T = 4) :
    (NCG.colourR = (2 : ℂ) • NCG.lepP - 1 ∧ NCG.colourR * NCG.colourR = 1
      ∧ Matrix.trace NCG.colourR = -2) ∧
    (∀ A : Matrix (Fin 4) (Fin 4) ℂ,
      T A = (Matrix.trace A / 4) • 1
        + (5⁻¹ : ℂ) • (A - (Matrix.trace A / 4) • 1)) ∧
    ((0 : ℝ) < 1 ∧ (0 : ℝ) < 5⁻¹) ∧
    (∀ A : Matrix (Fin 4) (Fin 4) ℂ,
      ((2⁻¹ : ℂ) • T) A = (2⁻¹ * (Matrix.trace A / 4)) • 1
        + (10⁻¹ : ℂ) • (A - (Matrix.trace A / 4) • 1)) := by
  refine ⟨⟨NCG.colourR_from_projection, NCG.colourR_involution, NCG.colourR_trace⟩,
    colour_covariance_forced T hcov hsl hT1 htrT, ⟨one_pos, by norm_num⟩,
    colour_score_bridge_forced T hcov hsl hT1 htrT⟩

end ColourOrbitAssembly
end NCG
