/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# A polyhedral predictive cone is not exactly a Lorentz quadric
  (`lem:poly-not-quad`, GR_emergence)

A polyhedral cone with a genuine facet contains a relatively open
piece of a hyperplane.  A nondegenerate quadratic form that vanishes
on a relatively open subset of a subspace `H` must vanish on all of
`H` (line restriction: a real quadratic polynomial vanishing on an
interval has zero coefficients), making `H` totally isotropic; but a
nondegenerate form on `V` bounds every totally isotropic subspace by
`2·dim H ≤ dim V`.  A facet hyperplane of a cone in `ℝ^{d+1}` has
`dim H = d`, so `d + 1 < 2d` (any `d ≥ 2`) is a contradiction:

* `quadratic_coeffs_zero` — interval vanishing kills all three
  coefficients;
* `quadratic_vanish_on_subspace` — open-in-`H` vanishing of `Q`
  propagates to all of `H`;
* `isotropic_of_quadratic_zero` — polarization;
* `isotropic_finrank_bound` — `2·dim H ≤ dim V` for nondegenerate
  forms;
* `facet_cone_not_lorentz_quadric` — the contradiction, and the
  `d+1`-dimensional specialization `poly_cone_not_quadric`.
-/

namespace NCG

open Module

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A real quadratic polynomial vanishing on an interval around zero
has all coefficients zero. -/
theorem quadratic_coeffs_zero {a b c ε : ℝ} (hε : 0 < ε)
    (h : ∀ t : ℝ, |t| < ε → a + b * t + c * t ^ 2 = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  have h0 := h 0 (by simpa using hε)
  have ha : a = 0 := by linarith [h0]
  have hp := h (ε / 2) (by rw [abs_of_pos (by linarith)]; linarith)
  have hm := h (-(ε / 2)) (by rw [abs_neg, abs_of_pos (by linarith)]; linarith)
  have hm' : a + b * -(ε / 2) + c * (ε / 2) ^ 2 = 0 := by
    linear_combination hm
  have hcsq : c * (ε / 2) ^ 2 = 0 := by linarith
  have hc : c = 0 := by
    rcases mul_eq_zero.mp hcsq with h' | h'
    · exact h'
    · exact absurd h' (by positivity)
  have hbe : b * (ε / 2) = 0 := by linarith
  have hb : b = 0 := by
    rcases mul_eq_zero.mp hbe with h' | h'
    · exact h'
    · exact absurd h' (by positivity)
  exact ⟨ha, hb, hc⟩

/-- If a symmetric bilinear form's quadratic values vanish on a
relatively open subset of a subspace `H`, they vanish on all of
`H`. -/
theorem quadratic_vanish_on_subspace
    {B : LinearMap.BilinForm ℝ V} (hsym : ∀ x y, B x y = B y x)
    {H : Submodule ℝ V} {x0 : V} (hx0 : x0 ∈ H) {ε : ℝ} (hε : 0 < ε)
    (hvan : ∀ y ∈ H, ‖y - x0‖ < ε → B y y = 0) :
    ∀ y ∈ H, B y y = 0 := by
  intro y hy
  set v : V := y - x0 with hv
  set δ : ℝ := ε / (‖v‖ + 1) with hδ
  have hδ0 : 0 < δ := by
    apply div_pos hε
    positivity
  -- the restricted quadratic polynomial along the segment direction
  have hline : ∀ t : ℝ, |t| < δ →
      B x0 x0 + (2 * B x0 v) * t + B v v * t ^ 2 = 0 := by
    intro t ht
    have hmem : x0 + t • v ∈ H := H.add_mem hx0
      (H.smul_mem t (by simpa [hv] using H.sub_mem hy hx0))
    have hnorm : ‖x0 + t • v - x0‖ < ε := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
      calc |t| * ‖v‖ ≤ |t| * (‖v‖ + 1) := by
            apply mul_le_mul_of_nonneg_left _ (abs_nonneg t)
            linarith
      _ < δ * (‖v‖ + 1) := by
            apply mul_lt_mul_of_pos_right ht
            positivity
      _ = ε := by
            rw [hδ]
            field_simp
    have hval := hvan (x0 + t • v) hmem hnorm
    have hexp : B (x0 + t • v) (x0 + t • v)
        = B x0 x0 + (2 * B x0 v) * t + B v v * t ^ 2 := by
      simp only [map_add, map_smul, LinearMap.add_apply,
        LinearMap.smul_apply, smul_eq_mul]
      rw [hsym v x0]
      ring
    rw [hexp] at hval
    exact hval
  obtain ⟨ha, hb, hc⟩ := quadratic_coeffs_zero hδ0 hline
  have hy' : y = x0 + v := by
    rw [hv]
    abel
  rw [hy']
  have hexp2 : B (x0 + v) (x0 + v)
      = B x0 x0 + 2 * B x0 v + B v v := by
    simp only [map_add, LinearMap.add_apply]
    rw [hsym v x0]
    ring
  rw [hexp2, ha, hc]
  linarith [hb]

/-- Polarization: a subspace on which the quadratic form vanishes is
totally isotropic. -/
theorem isotropic_of_quadratic_zero
    {B : LinearMap.BilinForm ℝ V} (hsym : ∀ x y, B x y = B y x)
    {H : Submodule ℝ V} (hQ : ∀ y ∈ H, B y y = 0) :
    ∀ u ∈ H, ∀ w ∈ H, B u w = 0 := by
  intro u hu w hw
  have hsum := hQ (u + w) (H.add_mem hu hw)
  have hexp : B (u + w) (u + w) = B u u + 2 * B u w + B w w := by
    simp only [map_add, LinearMap.add_apply]
    rw [hsym w u]
    ring
  rw [hexp, hQ u hu, hQ w hw] at hsum
  linarith

/-- A totally isotropic subspace of a nondegenerate bilinear space
satisfies `2·dim H ≤ dim V`. -/
theorem isotropic_finrank_bound [FiniteDimensional ℝ V]
    {B : LinearMap.BilinForm ℝ V} (hnd : B.Nondegenerate)
    {H : Submodule ℝ V}
    (hiso : ∀ u ∈ H, ∀ w ∈ H, B u w = 0) :
    2 * finrank ℝ H ≤ finrank ℝ V := by
  have hle : H ≤ B.orthogonal H := by
    intro v hv
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro w hw
    exact hiso w hw v hv
  have h1 : finrank ℝ H ≤ finrank ℝ (B.orthogonal H) :=
    Submodule.finrank_mono hle
  rw [LinearMap.BilinForm.finrank_orthogonal hnd] at h1
  have h2 : finrank ℝ H ≤ finrank ℝ V := H.finrank_le
  omega

/-- `lem:poly-not-quad` (abstract form): a nondegenerate quadratic
form cannot vanish on a relatively open subset of a subspace that is
more than half the dimension of the space.  In particular the null
set of a nondegenerate form cannot contain a genuine facet of a
polyhedral cone. -/
theorem facet_cone_not_lorentz_quadric [FiniteDimensional ℝ V]
    {B : LinearMap.BilinForm ℝ V} (hsym : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) {H : Submodule ℝ V} {x0 : V}
    (hx0 : x0 ∈ H) {ε : ℝ} (hε : 0 < ε)
    (hface : ∀ y ∈ H, ‖y - x0‖ < ε → B y y = 0)
    (hdim : finrank ℝ V < 2 * finrank ℝ H) : False := by
  have hQ := quadratic_vanish_on_subspace hsym hx0 hε hface
  have hiso := isotropic_of_quadratic_zero hsym hQ
  have hbound := isotropic_finrank_bound hnd hiso
  omega

/-- `lem:poly-not-quad` (dimension count): in `ℝ^{d+1}` with `d ≥ 2`,
a facet hyperplane (`dim H = d`) of a polyhedral cone cannot lie in
the null set of a nondegenerate (in particular Lorentzian) quadratic
form. -/
theorem poly_cone_not_quadric [FiniteDimensional ℝ V] {d : ℕ}
    (hd : 2 ≤ d) (hV : finrank ℝ V = d + 1)
    {B : LinearMap.BilinForm ℝ V} (hsym : ∀ x y, B x y = B y x)
    (hnd : B.Nondegenerate) {H : Submodule ℝ V} {x0 : V}
    (hx0 : x0 ∈ H) (hH : finrank ℝ H = d) {ε : ℝ} (hε : 0 < ε)
    (hface : ∀ y ∈ H, ‖y - x0‖ < ε → B y y = 0) : False := by
  apply facet_cone_not_lorentz_quadric hsym hnd hx0 hε hface
  rw [hV, hH]
  omega

end NCG
