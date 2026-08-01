/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Rank-one invariant triplet no-go (`thm:v5-triplet-nogo`, SM manuscript)

For any twice-differentiable one-invariant right potential
`V₀(X) = F(Tr XX*)` on the right-breaking carrier
`𝒱_R = M_{2×4}(ℂ)`, stationary at the rank-one vacuum `X₀`, the
stationary Hessian is
`D²V₀|_{X₀}(Y,Z) = 4F″(u₀)·(X₀,Y)_ℝ·(X₀,Z)_ℝ`, hence has rank at
most one and annihilates every direction orthogonal to `X₀` — in
particular the complete physical triplet `Δ_R`.

* `rinner` — the real pairing `(A,B)_ℝ = Re Tr(AB*)`;
* `radial_expand` — the exact quadratic expansion of the invariant
  along a two-parameter slice;
* `triplet_nogo` — the boxed Hessian formula (the Hessian taken as
  the mixed second derivative along the slice `X₀ + tY + sZ`);
* `triplet_nogo_annihilates` — the Hessian vanishes on directions
  orthogonal to `X₀`.
-/

open Matrix

namespace NCG

/-- The real pairing `(A,B)_ℝ = Re Tr(AB*)` on `M_{2×4}(ℂ)`. -/
noncomputable def rinner (A B : Matrix (Fin 2) (Fin 4) ℂ) : ℝ :=
  (Matrix.trace (A * Bᴴ)).re

/-- The pairing is symmetric. -/
lemma rinner_comm (A B : Matrix (Fin 2) (Fin 4) ℂ) :
    rinner A B = rinner B A := by
  rw [rinner, rinner]
  have h1 : Matrix.trace (B * Aᴴ)
      = star (Matrix.trace (A * Bᴴ)) := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  rw [h1]
  simp

/-- Derivative of a real quadratic. -/
private lemma hasDerivAt_quadratic (q₀ q₁ q₂ x : ℝ) :
    HasDerivAt (fun t : ℝ => q₀ + q₁ * t + q₂ * t ^ 2)
      (q₁ + 2 * q₂ * x) x := by
  have h1 : HasDerivAt (fun t : ℝ => q₁ * t) q₁ x := by
    simpa using (hasDerivAt_id x).const_mul q₁
  have h2 : HasDerivAt (fun t : ℝ => q₂ * t ^ 2) (q₂ * (2 * x)) x := by
    simpa using (hasDerivAt_pow 2 x).const_mul q₂
  have h5 := ((hasDerivAt_const x q₀).add h1).add h2
  have h6 : HasDerivAt (fun t : ℝ => q₀ + q₁ * t + q₂ * t ^ 2)
      (0 + q₁ + q₂ * (2 * x)) x :=
    h5.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => rfl)
  refine h6.congr_deriv ?_
  ring

/-- Exact quadratic expansion of the radial invariant along a
two-parameter slice. -/
theorem radial_expand (X₀ Y Z : Matrix (Fin 2) (Fin 4) ℂ)
    (t s : ℝ) :
    (Matrix.trace ((X₀ + t • Y + s • Z)
        * (X₀ + t • Y + s • Z)ᴴ)).re
      = rinner X₀ X₀ + 2 * rinner X₀ Y * t + 2 * rinner X₀ Z * s
        + rinner Y Y * t ^ 2 + 2 * rinner Y Z * (t * s)
        + rinner Z Z * s ^ 2 := by
  have hsmul : ∀ (c : ℝ) (M : Matrix (Fin 2) (Fin 4) ℂ),
      (c • M)ᴴ = c • Mᴴ := by
    intro c M
    ext i j
    simp [Matrix.conjTranspose_apply]
  have hre : ∀ (c : ℝ) (w : ℂ), ((c : ℂ) * w).re = c * w.re := by
    intro c w
    simp [Complex.mul_re]
  have hsym : ∀ A B : Matrix (Fin 2) (Fin 4) ℂ,
      (Matrix.trace (A * Bᴴ)).re = (Matrix.trace (B * Aᴴ)).re := by
    intro A B
    have h := rinner_comm A B
    rw [rinner, rinner] at h
    exact h
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_add,
    hsmul, hsmul]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul,
    Complex.add_re, Complex.real_smul, hre, rinner]
  rw [hsym Y X₀, hsym Z X₀, hsym Z Y]
  ring

/-- `thm:v5-triplet-nogo`: the stationary Hessian of a
one-invariant radial potential is
`D²V₀|_{X₀}(Y,Z) = 4F″(u₀)(X₀,Y)_ℝ(X₀,Z)_ℝ`. -/
theorem triplet_nogo (F F' : ℝ → ℝ) (F''0 : ℝ)
    (X₀ Y Z : Matrix (Fin 2) (Fin 4) ℂ)
    (hF1 : ∀ x : ℝ, HasDerivAt F (F' x) x)
    (hF2 : HasDerivAt F' F''0 (rinner X₀ X₀))
    (hstat : F' (rinner X₀ X₀) = 0) :
    deriv (fun s : ℝ => deriv (fun t : ℝ =>
        F ((Matrix.trace ((X₀ + t • Y + s • Z)
          * (X₀ + t • Y + s • Z)ᴴ)).re)) 0) 0
      = 4 * F''0 * rinner X₀ Y * rinner X₀ Z := by
  set u₀ : ℝ := rinner X₀ X₀ with hu₀
  set a : ℝ := rinner X₀ Y with ha
  set b : ℝ := rinner X₀ Z with hb
  set cYY : ℝ := rinner Y Y with hcYY
  set cYZ : ℝ := rinner Y Z with hcYZ
  set cZZ : ℝ := rinner Z Z with hcZZ
  -- the inner derivative as an explicit function of `s`
  have hinner : ∀ s : ℝ, deriv (fun t : ℝ =>
      F ((Matrix.trace ((X₀ + t • Y + s • Z)
        * (X₀ + t • Y + s • Z)ᴴ)).re)) 0
      = F' (u₀ + 2 * b * s + cZZ * s ^ 2)
        * (2 * a + 2 * cYZ * s) := by
    intro s
    have hq : ∀ t : ℝ, (Matrix.trace ((X₀ + t • Y + s • Z)
        * (X₀ + t • Y + s • Z)ᴴ)).re
        = (u₀ + 2 * b * s + cZZ * s ^ 2)
          + (2 * a + 2 * cYZ * s) * t + cYY * t ^ 2 := by
      intro t
      rw [radial_expand]
      ring
    have hpoly : HasDerivAt (fun t : ℝ =>
        (u₀ + 2 * b * s + cZZ * s ^ 2)
          + (2 * a + 2 * cYZ * s) * t + cYY * t ^ 2)
        (2 * a + 2 * cYZ * s) 0 := by
      refine (hasDerivAt_quadratic _ _ _ 0).congr_deriv ?_
      ring
    have hq0 : (u₀ + 2 * b * s + cZZ * s ^ 2)
        + (2 * a + 2 * cYZ * s) * 0 + cYY * 0 ^ 2
        = u₀ + 2 * b * s + cZZ * s ^ 2 := by ring
    have hchain := (hF1 ((u₀ + 2 * b * s + cZZ * s ^ 2)
        + (2 * a + 2 * cYZ * s) * 0 + cYY * 0 ^ 2)).comp 0 hpoly
    have hchain' : HasDerivAt (fun t : ℝ =>
        F ((Matrix.trace ((X₀ + t • Y + s • Z)
          * (X₀ + t • Y + s • Z)ᴴ)).re))
        (F' (u₀ + 2 * b * s + cZZ * s ^ 2)
          * (2 * a + 2 * cYZ * s)) 0 := by
      have h1 := hchain.congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun t => congrArg F (hq t))
      refine h1.congr_deriv ?_
      rw [hq0]
    exact hchain'.deriv
  rw [funext hinner]
  -- the outer derivative
  have hqs : HasDerivAt (fun s : ℝ =>
      u₀ + 2 * b * s + cZZ * s ^ 2) (2 * b) 0 := by
    refine (hasDerivAt_quadratic _ _ _ 0).congr_deriv ?_
    ring
  have hqs0 : u₀ + 2 * b * 0 + cZZ * 0 ^ 2 = u₀ := by ring
  have hF2' : HasDerivAt (fun s : ℝ =>
      F' (u₀ + 2 * b * s + cZZ * s ^ 2)) (F''0 * (2 * b)) 0 := by
    have h0 : HasDerivAt F' F''0 (u₀ + 2 * b * 0 + cZZ * 0 ^ 2) := by
      rw [hqs0]
      exact hF2
    have h1 := h0.comp 0 hqs
    exact h1.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun s => rfl)
  have hlin : HasDerivAt (fun s : ℝ => 2 * a + 2 * cYZ * s)
      (2 * cYZ) 0 := by
    have h1 : HasDerivAt
        (fun s : ℝ => 2 * a + 2 * cYZ * s + 0 * s ^ 2)
        (2 * cYZ) 0 := by
      refine (hasDerivAt_quadratic _ _ _ 0).congr_deriv ?_
      ring
    exact h1.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun s => by ring)
  have hprod := hF2'.mul hlin
  have hval : F' (u₀ + 2 * b * 0 + cZZ * 0 ^ 2) = 0 := by
    rw [hqs0]
    exact hstat
  have hprod' : HasDerivAt (fun s : ℝ =>
      F' (u₀ + 2 * b * s + cZZ * s ^ 2) * (2 * a + 2 * cYZ * s))
      (F''0 * (2 * b) * (2 * a + 2 * cYZ * 0)
        + F' (u₀ + 2 * b * 0 + cZZ * 0 ^ 2) * (2 * cYZ)) 0 :=
    hprod.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun s => rfl)
  rw [hprod'.deriv, hval]
  ring

/-- The stationary Hessian annihilates every direction orthogonal
to the vacuum — in particular the complete physical triplet. -/
theorem triplet_nogo_annihilates (F F' : ℝ → ℝ) (F''0 : ℝ)
    (X₀ Y Z : Matrix (Fin 2) (Fin 4) ℂ)
    (hF1 : ∀ x : ℝ, HasDerivAt F (F' x) x)
    (hF2 : HasDerivAt F' F''0 (rinner X₀ X₀))
    (hstat : F' (rinner X₀ X₀) = 0)
    (hY : rinner X₀ Y = 0) :
    deriv (fun s : ℝ => deriv (fun t : ℝ =>
        F ((Matrix.trace ((X₀ + t • Y + s • Z)
          * (X₀ + t • Y + s • Z)ᴴ)).re)) 0) 0 = 0 := by
  rw [triplet_nogo F F' F''0 X₀ Y Z hF1 hF2 hstat, hY]
  ring

end NCG
