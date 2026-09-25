/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Lorentz.DiscreteCartan
import RenewalGeometry.Gravity.RelationalDeSitterBranch

/-!
# Cartan curvature of the homogeneous de Sitter branch in components
  (`thm:supp-desitter-einstein`, emergent-spacetime supplement)

The orthonormal coframe `ϑ⁰ = dt`, `ϑᵃ = e^{Ht} dxᵃ` and the connection
`ωᵃ₀ = H ϑᵃ`, `ωᵃ_b = 0` of the manuscript are encoded at the level of
frame components:

* `coframeStructure H` — the structure coefficients `(dϑ^A)_{BC}` of the
  coframe (`dϑᵃ = H ϑ⁰ ∧ ϑᵃ`);
* `spinConnection H` — the connection coefficients `ω^A_{B C}` with
  `ω^A_B = ω^A_{BC} ϑ^C`;
* `torsionComponents`, `curvatureComponents` — Cartan's structure
  equations `T^A = dϑ^A + ω^A_B ∧ ϑ^B` and
  `Ω^A_B = dω^A_B + ω^A_C ∧ ω^C_B` written on a coframe whose connection
  coefficients are constant in the frame (so `d(ω^A_{BF} ϑ^F) = ω^A_{BF} dϑ^F`);
* `spinConnection_metric` — `ω_{AB} = -ω_{BA}` after lowering with
  `η = diag(-1,1,1,1)`;
* `torsion_free` — `T^A = 0`;
* `spinConnection_unique` — the displayed connection is the *unique*
  metric torsion-free connection of the coframe (via the six-step index
  chase `cartan_uniqueness` of `Lorentz/DiscreteCartan.lean`);
* `curvature_eq` — the boxed `Ω^A_B = H² ϑ^A ∧ ϑ_B`, i.e.
  `Ω^A_{B DE} = H² η_B (δ_{AD} δ_{BE} - δ_{AE} δ_{BD})`;
* `frameRicci_eq`, `frameScalar_eq`, `frame_einstein_cosmological` —
  `Ric_{AB} = 3H² η_{AB}`, `R = 12H²`, `G_{AB} + 3H² η_{AB} = 0` in the
  frame, and `coordinate_einstein_cosmological` — the same pulled back with
  the coframe matrix to the coordinate metric `g_H = -dt² + e^{2Ht} dx²`
  (`coframe_pullback_metric`).

The global-hyperbolicity sentence of the theorem is kept at the level of the
existing coordinate slicing certificate
`RelationalDeSitterBranch.compact_desitter_global_slicing_certificate`.
-/

open Matrix
open scoped BigOperators

namespace RenewalGeometry.DeSitterCartan

/-- The Minkowski signature `η = diag(-1,1,1,1)` as a diagonal function. -/
def eta : Fin 4 → ℝ := fun A => if A = 0 then -1 else 1

theorem eta_ne_zero (A : Fin 4) : eta A ≠ 0 := by
  unfold eta; split_ifs <;> norm_num

theorem eta_sq (A : Fin 4) : eta A * eta A = 1 := by
  unfold eta; split_ifs <;> norm_num

/-- The Minkowski matrix `η`. -/
def etaMatrix : Matrix (Fin 4) (Fin 4) ℝ := Matrix.diagonal eta

/-- Structure coefficients `(dϑ^A)_{BC}` of the coframe `ϑ⁰ = dt`,
`ϑᵃ = e^{Ht} dxᵃ`: `dϑᵃ = H ϑ⁰ ∧ ϑᵃ`, `dϑ⁰ = 0`. -/
def coframeStructure (H : ℝ) : Fin 4 → Fin 4 → Fin 4 → ℝ :=
  fun A B C =>
    if A ≠ 0 ∧ B = 0 ∧ C = A then H
    else if A ≠ 0 ∧ C = 0 ∧ B = A then -H else 0

/-- The structure coefficients are antisymmetric in the form indices. -/
theorem coframeStructure_antisymm (H : ℝ) (A B C : Fin 4) :
    coframeStructure H A B C = -(coframeStructure H A C B) := by
  unfold coframeStructure
  fin_cases A <;> fin_cases B <;> fin_cases C <;> simp

/-- Connection coefficients `ω^A_{B C}` (`ω^A_B = ω^A_{BC} ϑ^C`) of
`ωᵃ₀ = H ϑᵃ`, `ω⁰_a = H ϑᵃ` (so that `ω_{AB} = -ω_{BA}`), `ωᵃ_b = 0`. -/
def spinConnection (H : ℝ) : Fin 4 → Fin 4 → Fin 4 → ℝ :=
  fun A B C =>
    if A ≠ 0 ∧ B = 0 ∧ C = A then H
    else if A = 0 ∧ B ≠ 0 ∧ C = B then H else 0

/-- Metric compatibility: the lowered coefficients `ω_{ABC} = η_A ω^A_{BC}`
are antisymmetric in `A, B`. -/
theorem spinConnection_metric (H : ℝ) (A B C : Fin 4) :
    eta A * spinConnection H A B C = -(eta B * spinConnection H B A C) := by
  unfold spinConnection eta
  fin_cases A <;> fin_cases B <;> fin_cases C <;> simp

/-- Torsion components `T^A_{DE}` of `T^A = dϑ^A + ω^A_B ∧ ϑ^B`
for a coframe with structure coefficients `C` and connection `ω`. -/
def torsionComponents (C ω : Fin 4 → Fin 4 → Fin 4 → ℝ) :
    Fin 4 → Fin 4 → Fin 4 → ℝ :=
  fun A D E => C A D E + ω A E D - ω A D E

/-- Curvature components `Ω^A_{B DE}` of
`Ω^A_B = dω^A_B + ω^A_C ∧ ω^C_B`, with `dω^A_B = ω^A_{BF} dϑ^F`
(constant frame coefficients). -/
def curvatureComponents (C ω : Fin 4 → Fin 4 → Fin 4 → ℝ) :
    Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ :=
  fun A B D E => (∑ F, ω A B F * C F D E) +
    ∑ F, (ω A F D * ω F B E - ω A F E * ω F B D)

/-- Cartan's first structure equation: the connection is torsion-free. -/
theorem torsion_free (H : ℝ) :
    torsionComponents (coframeStructure H) (spinConnection H) = 0 := by
  funext A D E
  unfold torsionComponents coframeStructure spinConnection
  fin_cases A <;> fin_cases D <;> fin_cases E <;> simp

/-- The boxed constant-curvature Riemann tensor
`H² (δ_{AD} η_{BE} - δ_{AE} η_{BD})` (frame indices, first index up). -/
def constantCurvature (H : ℝ) : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ :=
  fun A B D E => H ^ 2 * eta B *
    ((if A = D then 1 else 0) * (if B = E then 1 else 0) -
      (if A = E then 1 else 0) * (if B = D then 1 else 0))

/-- Cartan's second structure equation: `Ω^A_B = H² ϑ^A ∧ ϑ_B`, i.e.
`Ω^A_{B DE} = H² η_B (δ_{AD} δ_{BE} - δ_{AE} δ_{BD})`. -/
theorem curvature_eq (H : ℝ) :
    curvatureComponents (coframeStructure H) (spinConnection H) =
      constantCurvature H := by
  funext A B D E
  unfold curvatureComponents coframeStructure spinConnection
    constantCurvature eta
  simp only [Fin.sum_univ_four]
  fin_cases A <;> fin_cases B <;> fin_cases D <;> fin_cases E <;>
    simp <;> ring

/-- Uniqueness: any connection on this coframe that is metric
(`ω_{AB} = -ω_{BA}` after lowering with `η`) and torsion-free coincides
with `spinConnection H`. -/
theorem spinConnection_unique (H : ℝ) (ω : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (hmetric : ∀ A B C, eta A * ω A B C = -(eta B * ω B A C))
    (htorsion : torsionComponents (coframeStructure H) ω = 0) :
    ω = spinConnection H := by
  -- lowered difference, arranged for `cartan_uniqueness`
  let Δ : Fin 4 → Fin 4 → Fin 4 → ℝ :=
    fun d a e => eta a * (ω a e d - spinConnection H a e d)
  have hT0 : ∀ A D E, torsionComponents (coframeStructure H) ω A D E = 0 :=
    fun A D E => by rw [htorsion]; rfl
  have hT1 : ∀ A D E,
      torsionComponents (coframeStructure H) (spinConnection H) A D E = 0 :=
    fun A D E => by rw [torsion_free]; rfl
  have hsymm : ∀ A D E, ω A E D - spinConnection H A E D =
      ω A D E - spinConnection H A D E := by
    intro A D E
    have h1 := hT0 A D E
    have h2 := hT1 A D E
    unfold torsionComponents at h1 h2
    linarith
  have hQ : ∀ d a e, Δ d a e = -(Δ d e a) := by
    intro d a e
    change eta a * (ω a e d - spinConnection H a e d) =
      -(eta e * (ω e a d - spinConnection H e a d))
    have h1 := hmetric a e d
    have h2 := spinConnection_metric H a e d
    linarith [mul_sub (eta a) (ω a e d) (spinConnection H a e d),
      mul_sub (eta e) (ω e a d) (spinConnection H e a d)]
  have hT : ∀ d a e, Δ d a e = Δ e a d := by
    intro d a e
    change eta a * (ω a e d - spinConnection H a e d) =
      eta a * (ω a d e - spinConnection H a d e)
    rw [hsymm a d e]
  have hzero := cartan_uniqueness Δ hQ hT
  funext A B C
  have h : eta A * (ω A B C - spinConnection H A B C) = 0 := hzero C A B
  rcases mul_eq_zero.mp h with h0 | h0
  · exact absurd h0 (eta_ne_zero A)
  · linarith

/-- Frame Ricci tensor `Ric_{BE} = Ω^A_{B AE}`. -/
def frameRicci (H : ℝ) : Fin 4 → Fin 4 → ℝ :=
  fun B E => ∑ A, curvatureComponents (coframeStructure H)
    (spinConnection H) A B A E

/-- `Ric_{AB} = 3H² η_{AB}` in the orthonormal frame. -/
theorem frameRicci_eq (H : ℝ) (B E : Fin 4) :
    frameRicci H B E = 3 * H ^ 2 * etaMatrix B E := by
  unfold frameRicci
  rw [curvature_eq]
  unfold constantCurvature etaMatrix eta
  simp only [Fin.sum_univ_four]
  fin_cases B <;> fin_cases E <;> simp <;> ring

/-- Frame scalar curvature `R = η^{BE} Ric_{BE}` (`η⁻¹ = η`). -/
def frameScalar (H : ℝ) : ℝ := ∑ B, eta B * frameRicci H B B

theorem frameScalar_eq (H : ℝ) : frameScalar H = 12 * H ^ 2 := by
  unfold frameScalar
  simp only [frameRicci_eq, Fin.sum_univ_four]
  unfold etaMatrix eta
  simp
  ring

/-- Frame Einstein tensor `G_{BE} = Ric_{BE} - ½ R η_{BE}`. -/
noncomputable def frameEinstein (H : ℝ) : Fin 4 → Fin 4 → ℝ :=
  fun B E => frameRicci H B E - (frameScalar H / 2) * etaMatrix B E

/-- The boxed vacuum equation `G_{AB} + 3H² η_{AB} = 0` in the frame. -/
theorem frame_einstein_cosmological (H : ℝ) (B E : Fin 4) :
    frameEinstein H B E + 3 * H ^ 2 * etaMatrix B E = 0 := by
  unfold frameEinstein
  rw [frameRicci_eq, frameScalar_eq]
  ring

/-! ### Pull-back to the coordinate metric `g_H` -/

/-- The coframe matrix `ϑ^A_μ = diag(1, e^{Ht}, e^{Ht}, e^{Ht})`. -/
noncomputable def coframeMatrix (H t : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal fun A => if A = 0 then 1 else Real.exp (H * t)

/-- The coframe pulls the Minkowski form back to the displayed metric
`g_H = -dt² + e^{2Ht} Σ (dxᵃ)²`. -/
theorem coframe_pullback_metric (H t : ℝ) :
    (coframeMatrix H t)ᵀ * etaMatrix * coframeMatrix H t =
      RelationalDeSitterBranch.lorentzMetric H t := by
  unfold coframeMatrix etaMatrix RelationalDeSitterBranch.lorentzMetric eta
  rw [Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext A
  split_ifs
  · norm_num
  · rw [mul_one, ← Real.exp_add]; congr 1; ring

/-- Coordinate Ricci tensor `Ric_{μν} = ϑ^A_μ ϑ^B_ν Ric_{AB}`. -/
noncomputable def coordinateRicci (H t : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  (coframeMatrix H t)ᵀ * Matrix.of (frameRicci H) * coframeMatrix H t

/-- `Ric_{μν} = 3H² g_{μν}` in coordinates. -/
theorem coordinateRicci_eq (H t : ℝ) :
    coordinateRicci H t =
      (3 * H ^ 2) • RelationalDeSitterBranch.lorentzMetric H t := by
  unfold coordinateRicci
  have hR : Matrix.of (frameRicci H) = (3 * H ^ 2) • etaMatrix := by
    ext B E
    simp [frameRicci_eq]
  rw [hR, Matrix.mul_smul, Matrix.smul_mul, coframe_pullback_metric]

/-- The boxed coordinate vacuum equation `G_{μν} + 3H² g_{μν} = 0`, with
`G_{μν} = Ric_{μν} - ½ R g_{μν}` and `R = 12H²`. -/
theorem coordinate_einstein_cosmological (H t : ℝ) :
    coordinateRicci H t -
        (frameScalar H / 2) • RelationalDeSitterBranch.lorentzMetric H t +
        (3 * H ^ 2) • RelationalDeSitterBranch.lorentzMetric H t = 0 := by
  rw [coordinateRicci_eq, frameScalar_eq]
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.zero_apply, smul_eq_mul]
  ring

/-- `thm:supp-desitter-einstein` assembled: the displayed connection is
metric, torsion-free and unique with these properties; its curvature is
`H² ϑ^A ∧ ϑ_B`; `Ric = 3H² g`, `R = 12H²`, `G + 3H² g = 0`; and the
constant-time slices carry the coordinate global-slicing certificate. -/
theorem desitter_cartan_einstein (H : ℝ) :
    (∀ A B C, eta A * spinConnection H A B C =
        -(eta B * spinConnection H B A C)) ∧
      torsionComponents (coframeStructure H) (spinConnection H) = 0 ∧
      (∀ ω : Fin 4 → Fin 4 → Fin 4 → ℝ,
        (∀ A B C, eta A * ω A B C = -(eta B * ω B A C)) →
        torsionComponents (coframeStructure H) ω = 0 →
        ω = spinConnection H) ∧
      curvatureComponents (coframeStructure H) (spinConnection H) =
        constantCurvature H ∧
      (∀ t, coordinateRicci H t =
        (3 * H ^ 2) • RelationalDeSitterBranch.lorentzMetric H t) ∧
      frameScalar H = 12 * H ^ 2 ∧
      (∀ t, coordinateRicci H t -
        (frameScalar H / 2) • RelationalDeSitterBranch.lorentzMetric H t +
        (3 * H ^ 2) • RelationalDeSitterBranch.lorentzMetric H t = 0) ∧
      ((∀ t, (RelationalDeSitterBranch.lorentzMetric H t).det ≠ 0) ∧
        (∀ t, (RelationalDeSitterBranch.spatialMetric H t).PosDef) ∧
        (∀ t dx, RelationalDeSitterBranch.lorentzQuadratic H t 0 dx ≤ 0 ↔
          dx = 0) ∧
        (∀ (curve : ℝ → RelationalDeSitterBranch.CompactSpatialQuotient)
          (τ : ℝ), ∃! s : ℝ, (s, curve s).1 = τ)) :=
  ⟨spinConnection_metric H, torsion_free H, spinConnection_unique H,
    curvature_eq H, coordinateRicci_eq H, frameScalar_eq H,
    coordinate_einstein_cosmological H,
    RelationalDeSitterBranch.compact_desitter_global_slicing_certificate H⟩

end RenewalGeometry.DeSitterCartan
