/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Gravity.CoordinateCurvature

/-!
# Spatially curved FLRW: the full Einstein constraint
  (Phase-4 curvature layer, `lem:flrw-renewal-constraint` at `k ≠ 0`)

The curved FLRW metric in polar coordinates
`diag(-1, a²/(1-kr²), a²r², a²r²sin²θ)`, evaluated at an equatorial
point (`θ = π/2`, where homogeneity makes the curvature
position-independent):

* `curvedGamma`, `curvedDGamma` — the connection jet, with
  faithfulness lemmas for the time-direction entries
  (`curved_time_jet₁`, `curved_time_jet₂`) and the radial entries
  (`curved_radial_jet₁`, `curved_radial_jet₂`);
* `curved_ricci_00`, `curved_einstein_00` — the curvature:
  `R₀₀ = -3ä/a` and the full constraint component
  `G₀₀ = 3((ȧ/a)² + k/a²)` — exactly the
  `G₀₀ = d(d-1)/2·(H² + k/a²)` input (at `d = 3`) of
  `lem:flrw-renewal-constraint` for every spatial curvature `k`.
-/

namespace NCG

open Finset

/-- The curved FLRW connection jet at an equatorial point:
nonzero entries `Γ⁰₁₁ = aȧ/(1-kr²)`, `Γ⁰₂₂ = aȧr²`,
`Γ⁰₃₃ = aȧr²`, `Γⁱ₀ᵢ = ȧ/a`, `Γ¹₁₁ = kr/(1-kr²)`,
`Γ¹₂₂ = Γ¹₃₃ = -r(1-kr²)`, `Γ²₁₂ = Γ³₁₃ = 1/r`. -/
noncomputable def curvedGamma (a adot r k : ℝ) :
    Fin 4 → Fin 4 → Fin 4 → ℝ := fun c i j =>
  if c = 0 then
    (if i = 1 ∧ j = 1 then a * adot / (1 - k * r ^ 2)
     else if (i = 2 ∧ j = 2) ∨ (i = 3 ∧ j = 3) then a * adot * r ^ 2
     else 0)
  else if (i = 0 ∧ j = c) ∨ (j = 0 ∧ i = c) then adot / a
  else if c = 1 then
    (if i = 1 ∧ j = 1 then k * r / (1 - k * r ^ 2)
     else if (i = 2 ∧ j = 2) ∨ (i = 3 ∧ j = 3) then
       -(r * (1 - k * r ^ 2))
     else 0)
  else if (i = 1 ∧ j = c) ∨ (j = 1 ∧ i = c) then 1 / r
  else 0

/-- The curved connection derivative jet at the equatorial point
(time and radial derivatives; the `θ`-derivatives contribute the
two entries `∂₂Γ²₃₃ = 1`, `∂₂Γ³₂₃ = -1` at `θ = π/2`). -/
noncomputable def curvedDGamma (a adot addot r k : ℝ) :
    Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ := fun e c i j =>
  if e = 0 then
    (if c = 0 then
      (if i = 1 ∧ j = 1 then
         (adot ^ 2 + a * addot) / (1 - k * r ^ 2)
       else if (i = 2 ∧ j = 2) ∨ (i = 3 ∧ j = 3) then
         (adot ^ 2 + a * addot) * r ^ 2
       else 0)
     else if (i = 0 ∧ j = c) ∨ (j = 0 ∧ i = c) then
       addot / a - adot ^ 2 / a ^ 2
     else 0)
  else if e = 1 then
    (if c = 0 then
      (if i = 1 ∧ j = 1 then
         a * adot * (2 * k * r) / (1 - k * r ^ 2) ^ 2
       else if (i = 2 ∧ j = 2) ∨ (i = 3 ∧ j = 3) then
         2 * a * adot * r
       else 0)
     else if c = 1 then
      (if i = 1 ∧ j = 1 then
         k * (1 + k * r ^ 2) / (1 - k * r ^ 2) ^ 2
       else if (i = 2 ∧ j = 2) ∨ (i = 3 ∧ j = 3) then
         -(1 - 3 * k * r ^ 2)
       else 0)
     else if (i = 1 ∧ j = c) ∨ (j = 1 ∧ i = c) then -(1 / r ^ 2)
     else 0)
  else if e = 2 then
    (if c = 2 ∧ i = 3 ∧ j = 3 then 1
     else if c = 3 ∧ ((i = 2 ∧ j = 3) ∨ (j = 2 ∧ i = 3)) then -1
     else 0)
  else 0

/-- Faithfulness (time): `(aȧ/(1-kr²))' = (ȧ² + aä)/(1-kr²)`. -/
theorem curved_time_jet₁ {af daf : ℝ → ℝ} {t v w r k : ℝ}
    (h1 : HasDerivAt af v t) (h2 : HasDerivAt daf w t)
    (hd : daf t = v) (_hden : 1 - k * r ^ 2 ≠ 0) :
    HasDerivAt (fun s => af s * daf s / (1 - k * r ^ 2))
      ((v * v + af t * w) / (1 - k * r ^ 2)) t :=
  (scale_jet_consistent h1 h2 hd).div_const _

/-- Faithfulness (time): `(ȧ/a)' = ä/a - (ȧ/a)²`. -/
theorem curved_time_jet₂ {af daf : ℝ → ℝ} {t v w : ℝ}
    (h1 : HasDerivAt af v t) (h2 : HasDerivAt daf w t)
    (hd : daf t = v) (ha : af t ≠ 0) :
    HasDerivAt (fun s => daf s / af s)
      (w / af t - v ^ 2 / af t ^ 2) t := by
  have h := h2.div h1 ha
  rw [hd] at h
  exact h.congr_deriv (by field_simp)

/-- Faithfulness (radial): `(kr/(1-kr²))' = k(1+kr²)/(1-kr²)²`. -/
theorem curved_radial_jet₁ {r k : ℝ} (hden : 1 - k * r ^ 2 ≠ 0) :
    HasDerivAt (fun x => k * x / (1 - k * x ^ 2))
      (k * (1 + k * r ^ 2) / (1 - k * r ^ 2) ^ 2) r := by
  have hnum : HasDerivAt (fun x : ℝ => k * x) k r := by
    simpa using (hasDerivAt_id r).const_mul k
  have hden' : HasDerivAt (fun x : ℝ => 1 - k * x ^ 2)
      (-(k * (2 * r))) r := by
    have := ((hasDerivAt_pow 2 r).const_mul k).const_sub 1
    simpa using this
  have h := hnum.div hden' hden
  exact h.congr_deriv (by field_simp; ring)

/-- Faithfulness (radial): `(-r(1-kr²))' = -(1 - 3kr²)`. -/
theorem curved_radial_jet₂ {r k : ℝ} :
    HasDerivAt (fun x : ℝ => -(x * (1 - k * x ^ 2)))
      (-(1 - 3 * k * r ^ 2)) r := by
  have h1 : HasDerivAt (fun x : ℝ => 1 - k * x ^ 2)
      (-(k * (2 * r))) r := by
    have := ((hasDerivAt_pow 2 r).const_mul k).const_sub 1
    simpa using this
  have h := ((hasDerivAt_id r).mul h1).neg
  exact h.congr_deriv (by simp only [id_eq]; ring)

/-- `R₀₀ = -3ä/a` on the curved FLRW background. -/
theorem curved_ricci_00 {a r k : ℝ} (ha : a ≠ 0) (_hr : r ≠ 0)
    (_hden : 1 - k * r ^ 2 ≠ 0) (adot addot : ℝ) :
    ricci (curvedGamma a adot r k) (curvedDGamma a adot addot r k) 0 0
      = -(3 * addot / a) := by
  unfold ricci riemann curvedGamma curvedDGamma
  simp [Fin.sum_univ_four]
  field_simp
  ring

/-- The inverse curved FLRW metric
`diag(-1, (1-kr²)/a², 1/(a²r²), 1/(a²r²))` at the equatorial
point. -/
noncomputable def curvedGinv (a r k : ℝ) : Fin 4 → Fin 4 → ℝ :=
  fun i j =>
    if i = j then
      (if i = 0 then -1
       else if i = 1 then (1 - k * r ^ 2) / a ^ 2
       else 1 / (a ^ 2 * r ^ 2))
    else 0

/-- The spatial Ricci entries of the curved background. -/
theorem curved_ricci_spatial {a r k : ℝ} (ha : a ≠ 0) (hr : r ≠ 0)
    (hden : 1 - k * r ^ 2 ≠ 0) (adot addot : ℝ) :
    (ricci (curvedGamma a adot r k) (curvedDGamma a adot addot r k) 1 1
        = (a * addot + 2 * adot ^ 2 + 2 * k) / (1 - k * r ^ 2)) ∧
    (ricci (curvedGamma a adot r k) (curvedDGamma a adot addot r k) 2 2
        = (a * addot + 2 * adot ^ 2 + 2 * k) * r ^ 2) ∧
    (ricci (curvedGamma a adot r k) (curvedDGamma a adot addot r k) 3 3
        = (a * addot + 2 * adot ^ 2 + 2 * k) * r ^ 2) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold ricci riemann curvedGamma curvedDGamma
    simp [Fin.sum_univ_four]
    field_simp
    ring
  · unfold ricci riemann curvedGamma curvedDGamma
    have hden' : (1 : ℝ) - r ^ 2 * k ≠ 0 := by
      rw [mul_comm (r ^ 2) k]
      exact hden
    simp [Fin.sum_univ_four]
    field_simp
    ring
  · unfold ricci riemann curvedGamma curvedDGamma
    have hden' : (1 : ℝ) - r ^ 2 * k ≠ 0 := by
      rw [mul_comm (r ^ 2) k]
      exact hden
    simp [Fin.sum_univ_four]
    field_simp
    ring

/-- The curved FLRW scalar curvature
`R = 6(ä/a + (ȧ/a)² + k/a²)`. -/
theorem curved_scalar {a r k : ℝ} (ha : a ≠ 0) (hr : r ≠ 0)
    (hden : 1 - k * r ^ 2 ≠ 0) (adot addot : ℝ) :
    (∑ b, ∑ d, curvedGinv a r k b d *
        ricci (curvedGamma a adot r k)
          (curvedDGamma a adot addot r k) b d)
      = 6 * (addot / a + adot ^ 2 / a ^ 2 + k / a ^ 2) := by
  obtain ⟨h11, h22, h33⟩ := curved_ricci_spatial ha hr hden adot addot
  have h00 := curved_ricci_00 ha hr hden adot addot
  rw [Fin.sum_univ_four]
  simp only [Fin.sum_univ_four]
  rw [h00, h11, h22, h33]
  unfold curvedGinv
  simp only [Fin.reduceEq, reduceIte]
  have hden' : (1 : ℝ) - r ^ 2 * k ≠ 0 := by
    rw [mul_comm (r ^ 2) k]
    exact hden
  field_simp
  ring

/-- The full curved Einstein constraint component
`G₀₀ = 3((ȧ/a)² + k/a²)` — the `d = 3` curvature input of
`lem:flrw-renewal-constraint` for arbitrary `k`. -/
theorem curved_einstein_00 {a r k : ℝ} (ha : a ≠ 0) (hr : r ≠ 0)
    (hden : 1 - k * r ^ 2 ≠ 0) (adot addot : ℝ) :
    ricci (curvedGamma a adot r k) (curvedDGamma a adot addot r k) 0 0
        - 1 / 2 * (-1 : ℝ) *
          (∑ b, ∑ d, curvedGinv a r k b d *
            ricci (curvedGamma a adot r k)
              (curvedDGamma a adot addot r k) b d)
      = 3 * ((adot / a) ^ 2 + k / a ^ 2) := by
  rw [curved_ricci_00 ha hr hden adot addot,
    curved_scalar ha hr hden adot addot]
  field_simp
  ring

end NCG
