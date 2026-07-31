/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Coordinate curvature and the flat FLRW Einstein constraint
  (Phase-4 theory gap: curvature tensors in coordinates)

The first slice of the coordinate-curvature layer flagged in the
triage as the highest-leverage Phase-4 gap.  Everything is finite
index algebra over `Fin 4` at a point, with the metric jet supplied
by symbolic scale-factor data `(a, ȧ, ä)`:

* `christoffel` — the Levi-Civita Christoffel symbols
  `Γ^c_{ab} = ½ g^{ce}(∂_a g_{eb} + ∂_b g_{ea} - ∂_e g_{ab})` from a
  metric jet;
* `flrw_christoffel` — for the flat FLRW metric
  `diag(-1, a², a², a²)` the symbols are exactly
  `Γ⁰_{ij} = aȧδᵢⱼ`, `Γⁱ_{0j} = (ȧ/a)δᵢⱼ`;
* `riemann`, `ricci`, `scalarCurv` — curvature from a connection
  jet;
* `flrw_ricci_diag`, `flrw_scalar` — the FLRW curvature:
  `R₀₀ = -3ä/a`, `Rᵢᵢ = aä + 2ȧ²`, `R = 6(ä/a + (ȧ/a)²)`;
* `flrw_einstein_00` — the Einstein tensor component
  `G₀₀ = R₀₀ - ½g₀₀R = 3(ȧ/a)²`: exactly the curvature input
  `G₀₀ = d(d-1)/2·H²` (at `d = 3`, `k = 0`) that
  `lem:flrw-renewal-constraint` consumes;
* `scale_jet_consistent` — the jet data is faithful: for an actual
  scale factor `a(t)`, `(aȧ)' = ȧ² + aä` (product rule).

The spatially curved case and the general-`d` index algebra extend
this file; the constant-curvature contractions already live in
`NCG.Gravity.FLRWReduction`.
-/

namespace NCG

open Finset

/-- Christoffel symbols of the second kind from a metric jet:
`Γ^c_{ab} = ½ Σ_e g^{ce}(∂_a g_{eb} + ∂_b g_{ea} - ∂_e g_{ab})`. -/
noncomputable def christoffel (ginv : Fin 4 → Fin 4 → ℝ)
    (dg : Fin 4 → Fin 4 → Fin 4 → ℝ) :
    Fin 4 → Fin 4 → Fin 4 → ℝ :=
  fun c i j => (1 / 2) * ∑ e, ginv c e *
    (dg i e j + dg j e i - dg e i j)

/-- Riemann tensor from a connection jet:
`R^a_{bcd} = ∂_cΓ^a_{db} - ∂_dΓ^a_{cb} + Γ^a_{ce}Γ^e_{db} -
Γ^a_{de}Γ^e_{cb}`. -/
def riemann (Gam : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (dGam : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ :=
  fun a b c d => dGam c a d b - dGam d a c b
    + (∑ e, Gam a c e * Gam e d b) - ∑ e, Gam a d e * Gam e c b

/-- Ricci tensor `R_{bd} = R^a_{bad}`. -/
def ricci (Gam : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (dGam : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    Fin 4 → Fin 4 → ℝ :=
  fun b d => ∑ a, riemann Gam dGam a b a d

/-- Scalar curvature `R = g^{bd}R_{bd}`. -/
def scalarCurv (ginv : Fin 4 → Fin 4 → ℝ)
    (Gam : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (dGam : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) : ℝ :=
  ∑ b, ∑ d, ginv b d * ricci Gam dGam b d

/-! ## The flat FLRW jet -/

/-- The flat FLRW metric `diag(-1, a², a², a²)` at a point. -/
def flrwG (a : ℝ) : Fin 4 → Fin 4 → ℝ :=
  fun i j => if i = j then (if i = 0 then -1 else a ^ 2) else 0

/-- Its inverse `diag(-1, a⁻², a⁻², a⁻²)`. -/
noncomputable def flrwGinv (a : ℝ) : Fin 4 → Fin 4 → ℝ :=
  fun i j => if i = j then (if i = 0 then -1 else (a ^ 2)⁻¹) else 0

/-- The metric derivative jet: `∂₀ g_{ii} = 2aȧ` on the spatial
diagonal, all other entries zero. -/
def flrwdg (a adot : ℝ) : Fin 4 → Fin 4 → Fin 4 → ℝ :=
  fun c i j =>
    if c = 0 ∧ i = j ∧ i ≠ 0 then 2 * a * adot else 0

/-- The FLRW Christoffel symbols: `Γ⁰_{ij} = aȧδᵢⱼ` (spatial `i`),
`Γⁱ_{0j} = Γⁱ_{j0} = (ȧ/a)δᵢⱼ`. -/
noncomputable def flrwGamma (a adot : ℝ) :
    Fin 4 → Fin 4 → Fin 4 → ℝ :=
  fun c i j =>
    if c = 0 then (if i = j ∧ i ≠ 0 then a * adot else 0)
    else (if (i = 0 ∧ j = c) ∨ (j = 0 ∧ i = c) then adot / a else 0)

/-- The connection derivative jet (`∂₀` only; spatial derivatives
vanish by homogeneity): `∂₀Γ⁰_{ij} = (ȧ² + aä)δᵢⱼ`,
`∂₀Γⁱ_{0j} = (ä/a - ȧ²/a²)δᵢⱼ`. -/
noncomputable def flrwdGamma (a adot addot : ℝ) :
    Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ :=
  fun e c i j =>
    if e = 0 then
      (if c = 0 then (if i = j ∧ i ≠ 0 then adot ^ 2 + a * addot else 0)
       else (if (i = 0 ∧ j = c) ∨ (j = 0 ∧ i = c)
         then addot / a - adot ^ 2 / a ^ 2 else 0))
    else 0

/-- The FLRW jet produces exactly the FLRW Christoffel symbols. -/
theorem flrw_christoffel {a : ℝ} (ha : a ≠ 0) (adot : ℝ) :
    christoffel (flrwGinv a) (flrwdg a adot) = flrwGamma a adot := by
  funext c i j
  unfold christoffel flrwGinv flrwdg flrwGamma
  fin_cases c <;> fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_four] <;>
    field_simp

/-- Faithfulness of the jet: for an actual scale factor,
`(aȧ)' = ȧ² + aä`. -/
theorem scale_jet_consistent {af daf : ℝ → ℝ} {t v w : ℝ}
    (h1 : HasDerivAt af v t) (h2 : HasDerivAt daf w t)
    (hd : daf t = v) :
    HasDerivAt (fun s => af s * daf s) (v * v + af t * w) t := by
  have h := h1.mul h2
  rw [hd] at h
  exact h

/-- The FLRW Ricci tensor: `R₀₀ = -3ä/a` and
`Rᵢᵢ = aä + 2ȧ²` on the spatial diagonal (off-diagonal zero). -/
theorem flrw_ricci_diag {a : ℝ} (ha : a ≠ 0) (adot addot : ℝ) :
    (ricci (flrwGamma a adot) (flrwdGamma a adot addot) 0 0
        = -(3 * addot / a)) ∧
    (∀ i : Fin 4, i ≠ 0 →
      ricci (flrwGamma a adot) (flrwdGamma a adot addot) i i
        = a * addot + 2 * adot ^ 2) ∧
    (∀ i j : Fin 4, i ≠ j →
      ricci (flrwGamma a adot) (flrwdGamma a adot addot) i j = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold ricci riemann flrwGamma flrwdGamma
    simp [Fin.sum_univ_four]
    field_simp
    ring
  · intro i hi
    unfold ricci riemann flrwGamma flrwdGamma
    fin_cases i <;> simp_all <;>
      simp [Fin.sum_univ_four] <;> field_simp <;> ring
  · intro i j hij
    unfold ricci riemann flrwGamma flrwdGamma
    fin_cases i <;> fin_cases j <;> simp_all <;>
      simp [Fin.sum_univ_four]

/-- The FLRW scalar curvature `R = 6(ä/a + (ȧ/a)²)`. -/
theorem flrw_scalar {a : ℝ} (ha : a ≠ 0) (adot addot : ℝ) :
    scalarCurv (flrwGinv a) (flrwGamma a adot)
        (flrwdGamma a adot addot)
      = 6 * (addot / a + adot ^ 2 / a ^ 2) := by
  obtain ⟨h00, hdiag, hoff⟩ := flrw_ricci_diag ha adot addot
  unfold scalarCurv flrwGinv
  rw [Fin.sum_univ_four]
  simp only [Fin.sum_univ_four]
  rw [h00, hdiag 1 (by decide), hdiag 2 (by decide),
    hdiag 3 (by decide), hoff 0 1 (by decide), hoff 0 2 (by decide),
    hoff 0 3 (by decide), hoff 1 0 (by decide), hoff 1 2 (by decide),
    hoff 1 3 (by decide), hoff 2 0 (by decide), hoff 2 1 (by decide),
    hoff 2 3 (by decide), hoff 3 0 (by decide), hoff 3 1 (by decide),
    hoff 3 2 (by decide)]
  simp
  field_simp
  ring

/-- The FLRW Einstein constraint component:
`G₀₀ = R₀₀ - ½g₀₀R = 3(ȧ/a)²` — exactly the curvature input
`G₀₀ = d(d-1)/2·H²` (at `d = 3`) consumed by
`lem:flrw-renewal-constraint`. -/
theorem flrw_einstein_00 {a : ℝ} (ha : a ≠ 0) (adot addot : ℝ) :
    ricci (flrwGamma a adot) (flrwdGamma a adot addot) 0 0
        - 1 / 2 * flrwG a 0 0 *
          scalarCurv (flrwGinv a) (flrwGamma a adot)
            (flrwdGamma a adot addot)
      = 3 * (adot / a) ^ 2 := by
  obtain ⟨h00, _, _⟩ := flrw_ricci_diag ha adot addot
  rw [h00, flrw_scalar ha adot addot]
  unfold flrwG
  simp
  field_simp
  ring

/-- The de Sitter branch is an Einstein space: on the exponential
scale factor jet (`ȧ = Ha`, `ä = H²a`) the FLRW Ricci tensor is
exactly `Ric = 3H²·g` and the scalar curvature is `R = 12H²` —
`Ric = dH²g`, `R = d(d+1)H²` at `d = 3`, closing the FLRW side of
`lem:pure-deficiency-constant-curvature`. -/
theorem desitter_einstein_space {a H : ℝ} (ha : a ≠ 0) :
    (∀ i j : Fin 4,
      ricci (flrwGamma a (H * a)) (flrwdGamma a (H * a) (H ^ 2 * a)) i j
        = 3 * H ^ 2 * flrwG a i j) ∧
    scalarCurv (flrwGinv a) (flrwGamma a (H * a))
        (flrwdGamma a (H * a) (H ^ 2 * a)) = 12 * H ^ 2 := by
  obtain ⟨h00, hdiag, hoff⟩ := flrw_ricci_diag ha (H * a) (H ^ 2 * a)
  constructor
  · intro i j
    by_cases hij : i = j
    · subst hij
      by_cases hi0 : i = 0
      · subst hi0
        rw [h00]
        unfold flrwG
        simp
        field_simp
      · rw [hdiag i hi0]
        unfold flrwG
        simp [hi0]
        ring
    · rw [hoff i j hij]
      unfold flrwG
      simp [hij]
  · rw [flrw_scalar ha (H * a) (H ^ 2 * a)]
    field_simp
    ring

end NCG
