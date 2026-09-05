/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# FLRW reductions of the renewal action
  (GR_emergence, FLRW cluster)

* `flrw_flatness_master`, `flrw_flatness_selects`
  (`lem:flrw-renewal-constraint`): the lapse constraint on the
  matter-free pure-deficiency branch reduces to the flatness master
  equation `k/a² = M_ren + 𝓡₀₀`, and at leading Einstein order
  (`M_ren = 𝓡₀₀ = 0`) forces `k = 0` among `k ∈ {-1, 0, 1}`;
* `flrw_quadratic_collapse` (`lem:flrw-quadratic-collapse`): given
  the four-dimensional decomposition
  `δ∫Ric² = ⅓δ∫R² + ½δ∫C² - ½δ∫E₄` with the Gauss–Bonnet variation
  vanishing and the Bach variation vanishing on conformally flat
  FLRW, the quadratic sector collapses to `δ∫Ric² = ⅓δ∫R²` and the
  action probes only the Wilson combination `c₁ + c₂/3`;
* `constant_curvature_ricci`, `constant_curvature_scalar`
  (`lem:pure-deficiency-constant-curvature`): contracting the
  constant-curvature Riemann tensor
  `R_{μνρσ} = H²(g_{μρ}g_{νσ} - g_{μσ}g_{νρ})` with the inverse
  metric gives `Ric = (n-1)H² g` and `R = n(n-1)H²` (with
  `n = d + 1`, this is `Ric = dH²g`, `R = d(d+1)H²`).  The
  conformal-flatness/Weyl-vanishing input identifying the FLRW
  vacuum branch with this tensor is the disclosed geometric layer.
-/

namespace NCG

open Matrix

/-- `lem:flrw-renewal-constraint` (master equation): on the
matter-free pure-deficiency branch the lapse constraint reduces to
`k/a² = M_ren + 𝓡₀₀`. -/
theorem flrw_flatness_master {H a lam G M R00 rho : ℝ} {k : ℤ}
    {d : ℕ}
    (hconstraint : H ^ 2 + (k : ℝ) / a ^ 2
      = 16 * Real.pi * G / (d * (d - 1)) * rho
        + 2 * lam / (d * (d - 1)) + M + R00)
    (hmatterfree : rho = 0)
    (hpure : 2 * lam / (d * (d - 1)) = H ^ 2) :
    (k : ℝ) / a ^ 2 = M + R00 := by
  rw [hmatterfree, mul_zero, hpure] at hconstraint
  linarith

/-- `lem:flrw-renewal-constraint` (flatness selection): at leading
Einstein order the master equation forces `k = 0`. -/
theorem flrw_flatness_selects {a : ℝ} {k : ℤ} (ha : 0 < a)
    (hu : (k : ℝ) / a ^ 2 = 0) : k = 0 := by
  have ha2 : (a : ℝ) ^ 2 ≠ 0 := by positivity
  have : (k : ℝ) = 0 := by
    field_simp at hu
    simpa using hu
  exact_mod_cast this

/-- `lem:flrw-quadratic-collapse`: with the Gauss–Bonnet variation
vanishing and the Bach (Weyl-squared) variation vanishing on the
conformally flat FLRW background, the quadratic-curvature sector
collapses and probes only `c₁ + c₂/3`. -/
theorem flrw_quadratic_collapse {vR2 vRic2 vC2 vE4 c1 c2 c3 : ℝ}
    (hdecomp : vRic2 = 1 / 3 * vR2 + 1 / 2 * vC2 - 1 / 2 * vE4)
    (hbach : vC2 = 0) (heuler : vE4 = 0) :
    vRic2 = 1 / 3 * vR2 ∧
      c1 * vR2 + c2 * vRic2 + c3 * vC2 = (c1 + c2 / 3) * vR2 := by
  constructor
  · rw [hdecomp, hbach, heuler]
    ring
  · rw [hdecomp, hbach, heuler]
    ring

/-- The constant-curvature Riemann tensor
`R_{μνρσ} = H²(g_{μρ}g_{νσ} - g_{μσ}g_{νρ})`. -/
def constRiem {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ) (H : ℝ)
    (mu nu rho sigma : Fin n) : ℝ :=
  H ^ 2 * (G mu rho * G nu sigma - G mu sigma * G nu rho)

/-- `lem:pure-deficiency-constant-curvature` (Ricci contraction):
contracting the constant-curvature Riemann tensor with the inverse
metric gives `Ric = (n-1)H² g`. -/
theorem constant_curvature_ricci {n : ℕ}
    {G Ginv : Matrix (Fin n) (Fin n) ℝ} {H : ℝ}
    (hGsym : ∀ i j, G i j = G j i)
    (hsym : ∀ i j, Ginv i j = Ginv j i)
    (hinv : Ginv * G = 1) (nu sigma : Fin n) :
    ∑ mu, ∑ rho, Ginv mu rho * constRiem G H mu nu rho sigma
      = (n - 1) * H ^ 2 * G nu sigma := by
  have htrace : ∑ mu, ∑ rho, Ginv mu rho * G mu rho = (n : ℝ) := by
    have h1 : ∀ mu, ∑ rho, Ginv mu rho * G mu rho
        = (Ginv * G) mu mu := by
      intro mu
      rw [Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro rho _
      rw [hGsym mu rho]
    calc ∑ mu, ∑ rho, Ginv mu rho * G mu rho
        = ∑ mu, (Ginv * G) mu mu := Finset.sum_congr rfl fun mu _ => h1 mu
    _ = Matrix.trace (Ginv * G) := rfl
    _ = Matrix.trace (1 : Matrix (Fin n) (Fin n) ℝ) := by rw [hinv]
    _ = (n : ℝ) := by simp [Matrix.trace_one]
  have hdelta : ∑ mu, ∑ rho, Ginv mu rho * G mu sigma * G nu rho
      = G nu sigma := by
    have h1 : ∀ rho, ∑ mu, Ginv rho mu * G mu sigma
        = (Ginv * G) rho sigma := by
      intro rho
      rw [Matrix.mul_apply]
    calc ∑ mu, ∑ rho, Ginv mu rho * G mu sigma * G nu rho
        = ∑ rho, ∑ mu, Ginv mu rho * G mu sigma * G nu rho :=
          Finset.sum_comm
    _ = ∑ rho, G nu rho * ((Ginv * G) rho sigma) := by
          apply Finset.sum_congr rfl
          intro rho _
          rw [← h1 rho, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro mu _
          rw [hsym mu rho]
          ring
    _ = ∑ rho, G nu rho * (1 : Matrix (Fin n) (Fin n) ℝ) rho sigma := by
          rw [hinv]
    _ = G nu sigma := by
          simp [Matrix.one_apply]
  have hexpand : ∀ mu rho : Fin n,
      Ginv mu rho * constRiem G H mu nu rho sigma
      = H ^ 2 * G nu sigma * (Ginv mu rho * G mu rho)
        - H ^ 2 * (Ginv mu rho * G mu sigma * G nu rho) := by
    intro mu rho
    unfold constRiem
    ring
  calc ∑ mu, ∑ rho, Ginv mu rho * constRiem G H mu nu rho sigma
      = ∑ mu, ∑ rho, (H ^ 2 * G nu sigma * (Ginv mu rho * G mu rho)
        - H ^ 2 * (Ginv mu rho * G mu sigma * G nu rho)) := by
        apply Finset.sum_congr rfl
        intro mu _
        exact Finset.sum_congr rfl fun rho _ => hexpand mu rho
  _ = H ^ 2 * G nu sigma * (∑ mu, ∑ rho, Ginv mu rho * G mu rho)
        - H ^ 2 * (∑ mu, ∑ rho, Ginv mu rho * G mu sigma * G nu rho) := by
        simp [Finset.sum_sub_distrib, Finset.mul_sum]
  _ = H ^ 2 * G nu sigma * (n : ℝ) - H ^ 2 * G nu sigma := by
        rw [htrace, hdelta]
  _ = (n - 1) * H ^ 2 * G nu sigma := by ring

/-- `lem:pure-deficiency-constant-curvature` (scalar curvature):
the full contraction gives `R = n(n-1)H²`. -/
theorem constant_curvature_scalar {n : ℕ}
    {G Ginv : Matrix (Fin n) (Fin n) ℝ} {H : ℝ}
    (hGsym : ∀ i j, G i j = G j i)
    (hsym : ∀ i j, Ginv i j = Ginv j i)
    (hinv : Ginv * G = 1) :
    ∑ nu, ∑ sigma, Ginv nu sigma *
        (∑ mu, ∑ rho, Ginv mu rho * constRiem G H mu nu rho sigma)
      = n * (n - 1) * H ^ 2 := by
  have htrace : ∑ nu, ∑ sigma, Ginv nu sigma * G nu sigma = (n : ℝ) := by
    have h1 : ∀ nu, ∑ sigma, Ginv nu sigma * G nu sigma
        = (Ginv * G) nu nu := by
      intro nu
      rw [Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro sigma _
      rw [hGsym nu sigma]
    calc ∑ nu, ∑ sigma, Ginv nu sigma * G nu sigma
        = ∑ nu, (Ginv * G) nu nu :=
          Finset.sum_congr rfl fun nu _ => h1 nu
    _ = Matrix.trace (Ginv * G) := rfl
    _ = (n : ℝ) := by rw [hinv]; simp [Matrix.trace_one]
  calc ∑ nu, ∑ sigma, Ginv nu sigma *
        (∑ mu, ∑ rho, Ginv mu rho * constRiem G H mu nu rho sigma)
      = ∑ nu, ∑ sigma, Ginv nu sigma *
        ((n - 1) * H ^ 2 * G nu sigma) := by
        apply Finset.sum_congr rfl
        intro nu _
        apply Finset.sum_congr rfl
        intro sigma _
        rw [constant_curvature_ricci hGsym hsym hinv]
  _ = (n - 1) * H ^ 2 * ∑ nu, ∑ sigma, Ginv nu sigma * G nu sigma := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro nu _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro sigma _
        ring
  _ = n * (n - 1) * H ^ 2 := by
        rw [htrace]
        ring

end NCG
