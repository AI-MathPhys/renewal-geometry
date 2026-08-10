/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The locked incidence-orbit polytope

This module performs the exact four-orbit transform used in
`thm:SMST-locked-orbit-polytope`.  It proves feasibility, the eliminated
matching-coordinate interval, the equivalent parallelogram inequalities, the
four vertex images, and the independent tail/complement positivity test.
-/

namespace NCG

/-- Masses of the zero, touching, half-incident, and opposite diagonal-`S₄`
orbits. -/
@[ext] structure LockedOrbitMass where
  q0 : ℝ
  qt : ℝ
  qh : ℝ
  qo : ℝ

namespace LockedOrbitMass

def Nonnegative (q : LockedOrbitMass) : Prop :=
  0 ≤ q.q0 ∧ 0 ≤ q.qt ∧ 0 ≤ q.qh ∧ 0 ≤ q.qo

def total (q : LockedOrbitMass) : ℝ := q.q0 + q.qt + q.qh + q.qo

def standardE (q : LockedOrbitMass) : ℝ := q.q0 + q.qt - q.qh - q.qo

def standardA (q : LockedOrbitMass) : ℝ := 2 * q.q0 - q.qt + q.qh - 2 * q.qo

def matchingD (q : LockedOrbitMass) : ℝ := 2 * q.q0 - q.qt - q.qh + 2 * q.qo

/-- The inverse orbit transform from total and three orbit coordinates. -/
noncomputable def inverse (T E A D : ℝ) : LockedOrbitMass where
  q0 := (T + E + A + D) / 6
  qt := (2 * T + 2 * E - A - D) / 6
  qh := (2 * T - 2 * E + A - D) / 6
  qo := (T - E - A + D) / 6

@[simp] theorem total_inverse (T E A D : ℝ) :
    (inverse T E A D).total = T := by
  simp [inverse, total]
  ring

@[simp] theorem standardE_inverse (T E A D : ℝ) :
    (inverse T E A D).standardE = E := by
  simp [inverse, standardE]
  ring

@[simp] theorem standardA_inverse (T E A D : ℝ) :
    (inverse T E A D).standardA = A := by
  simp [inverse, standardA]
  ring

@[simp] theorem matchingD_inverse (T E A D : ℝ) :
    (inverse T E A D).matchingD = D := by
  simp [inverse, matchingD]
  ring

theorem inverse_coordinates (q : LockedOrbitMass) :
    inverse q.total q.standardE q.standardA q.matchingD = q := by
  ext <;> simp [inverse, total, standardE, standardA, matchingD] <;> ring

/-- Nonnegativity of all four raw masses is exactly the eliminated matching
coordinate interval. -/
theorem inverse_nonnegative_iff (T E A D : ℝ) :
    (inverse T E A D).Nonnegative ↔
      -T + |E + A| ≤ D ∧ D ≤ 2 * T - |2 * E - A| := by
  have hlower : -T + |E + A| ≤ D ↔
      -(T + D) ≤ E + A ∧ E + A ≤ T + D := by
    have hmove : -T + |E + A| ≤ D ↔ |E + A| ≤ T + D := by
      constructor <;> intro h <;> linarith
    rw [hmove, abs_le]
  have hupper : D ≤ 2 * T - |2 * E - A| ↔
      -(2 * T - D) ≤ 2 * E - A ∧ 2 * E - A ≤ 2 * T - D := by
    have hmove : D ≤ 2 * T - |2 * E - A| ↔
        |2 * E - A| ≤ 2 * T - D := by
      constructor <;> intro h <;> linarith
    rw [hmove, abs_le]
  rw [hlower, hupper]
  simp only [Nonnegative, inverse]
  constructor
  · rintro ⟨h0, ht, hh, ho⟩
    constructor
    · constructor <;> linarith
    · constructor <;> linarith
  · rintro ⟨⟨hl0, hl1⟩, hu0, hu1⟩
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩

end LockedOrbitMass

/-- The elementary planar identity converting a diamond to its rotated box. -/
theorem abs_add_abs_le_iff_rotated_box (x y b : ℝ) :
    |x| + |y| ≤ b ↔ |x + y| ≤ b ∧ |x - y| ≤ b := by
  constructor
  · intro h
    constructor
    · exact (abs_add_le x y).trans h
    · have h' : |x| + |-y| ≤ b := by simpa only [abs_neg] using h
      simpa only [sub_eq_add_neg] using (abs_add_le x (-y)).trans h'
  · intro h
    rcases le_total 0 x with hx | hx <;>
      rcases le_total 0 y with hy | hy
    · rw [abs_of_nonneg hx, abs_of_nonneg hy]
      have hxy : 0 ≤ x + y := add_nonneg hx hy
      have hh := h.1
      rw [abs_of_nonneg hxy] at hh
      exact hh
    · rw [abs_of_nonneg hx, abs_of_nonpos hy]
      have hxy : 0 ≤ x - y := sub_nonneg.mpr (hy.trans hx)
      have hh := h.2
      rw [abs_of_nonneg hxy] at hh
      linarith
    · rw [abs_of_nonpos hx, abs_of_nonneg hy]
      have hxy : x - y ≤ 0 := sub_nonpos.mpr (hx.trans hy)
      have hh := h.2
      rw [abs_of_nonpos hxy] at hh
      linarith
    · rw [abs_of_nonpos hx, abs_of_nonpos hy]
      have hxy : x + y ≤ 0 := add_nonpos hx hy
      have hh := h.1
      rw [abs_of_nonpos hxy] at hh
      linarith

/-- Existence of nonnegative raw orbit masses is exactly the projected
parallelogram inequality. -/
theorem lockedOrbitMass_exists_iff (T E A : ℝ) :
    (∃ q : LockedOrbitMass,
        q.Nonnegative ∧ q.total = T ∧ q.standardE = E ∧ q.standardA = A)
      ↔ |E + A| + |2 * E - A| ≤ 3 * T := by
  constructor
  · rintro ⟨q, hq, rfl, rfl, rfl⟩
    have hqi : (LockedOrbitMass.inverse q.total q.standardE q.standardA
        q.matchingD).Nonnegative := by
      simpa [LockedOrbitMass.inverse_coordinates q] using hq
    have hi := (LockedOrbitMass.inverse_nonnegative_iff
      q.total q.standardE q.standardA q.matchingD).mp hqi
    linarith
  · intro h
    let D := -T + |E + A|
    let q := LockedOrbitMass.inverse T E A D
    have hinterval : -T + |E + A| ≤ D
        ∧ D ≤ 2 * T - |2 * E - A| := by
      dsimp [D]
      constructor
      · rfl
      · linarith
    have hq := (LockedOrbitMass.inverse_nonnegative_iff T E A D).mpr hinterval
    exact ⟨q, hq, LockedOrbitMass.total_inverse _ _ _ _,
      LockedOrbitMass.standardE_inverse _ _ _ _,
      LockedOrbitMass.standardA_inverse _ _ _ _⟩

/-- Equivalent axis-aligned description of the projected orbit polytope. -/
theorem lockedOrbit_diamond_iff_box (T E A : ℝ) :
    |E + A| + |2 * E - A| ≤ 3 * T ↔
      |E| ≤ T ∧ |A - E / 2| ≤ 3 * T / 2 := by
  rw [abs_add_abs_le_iff_rotated_box (E + A) (2 * E - A) (3 * T)]
  have h1 : E + A + (2 * E - A) = 3 * E := by ring
  have h2 : E + A - (2 * E - A) = 2 * (A - E / 2) := by ring
  rw [h1, h2]
  have hEscale : |3 * E| = 3 * |E| := by
    rw [abs_mul]
    norm_num
  have hAscale : |2 * (A - E / 2)| = 2 * |A - E / 2| := by
    rw [abs_mul]
    norm_num
  rw [hEscale, hAscale]
  constructor <;> rintro ⟨hE, hA⟩ <;> constructor <;> linarith

/-- The four pure orbit masses give exactly the four displayed vertices. -/
theorem lockedOrbit_vertices (T : ℝ) (hT : 0 ≤ T) :
    let q0 : LockedOrbitMass := ⟨T, 0, 0, 0⟩
    let qt : LockedOrbitMass := ⟨0, T, 0, 0⟩
    let qh : LockedOrbitMass := ⟨0, 0, T, 0⟩
    let qo : LockedOrbitMass := ⟨0, 0, 0, T⟩
    q0.Nonnegative ∧ (q0.standardE, q0.standardA) = (T, 2 * T)
      ∧ qt.Nonnegative ∧ (qt.standardE, qt.standardA) = (T, -T)
      ∧ qh.Nonnegative ∧ (qh.standardE, qh.standardA) = (-T, T)
      ∧ qo.Nonnegative ∧ (qo.standardE, qo.standardA) = (-T, -2 * T) := by
  dsimp [LockedOrbitMass.Nonnegative, LockedOrbitMass.standardE,
    LockedOrbitMass.standardA]
  constructor
  · exact ⟨hT, by norm_num, by norm_num, by norm_num⟩
  constructor
  · congr <;> ring
  constructor
  · exact ⟨by norm_num, hT, by norm_num, by norm_num⟩
  constructor
  · congr <;> ring
  constructor
  · exact ⟨by norm_num, by norm_num, hT, by norm_num⟩
  constructor
  · congr <;> ring
  constructor
  · exact ⟨by norm_num, by norm_num, by norm_num, hT⟩
  · congr <;> ring

/-- Joint positivity of an aggregate table and its binary-tail subtable is the
pair of independent projected-polytope inequalities for tail and complement. -/
theorem lockedOrbit_tail_complement_iff
    (τ σ E A E1 A1 : ℝ) :
    (∃ tail rest : LockedOrbitMass,
        tail.Nonnegative ∧ rest.Nonnegative
          ∧ tail.total = σ ∧ tail.standardE = E1 ∧ tail.standardA = A1
          ∧ rest.total = τ - σ
          ∧ rest.standardE = E - E1 ∧ rest.standardA = A - A1)
      ↔ |E1 + A1| + |2 * E1 - A1| ≤ 3 * σ
        ∧ |(E - E1) + (A - A1)|
            + |2 * (E - E1) - (A - A1)| ≤ 3 * (τ - σ) := by
  rw [← lockedOrbitMass_exists_iff σ E1 A1,
    ← lockedOrbitMass_exists_iff (τ - σ) (E - E1) (A - A1)]
  constructor
  · rintro ⟨tail, rest, htail, hrest, ht, he, ha, hr, hre, hra⟩
    exact ⟨⟨tail, htail, ht, he, ha⟩, ⟨rest, hrest, hr, hre, hra⟩⟩
  · rintro ⟨⟨tail, htail, ht, he, ha⟩, ⟨rest, hrest, hr, hre, hra⟩⟩
    exact ⟨tail, rest, htail, hrest, ht, he, ha, hr, hre, hra⟩

/-- Complete exact bundle for `thm:SMST-locked-orbit-polytope`. -/
theorem locked_incidence_orbit_polytope_exact (T E A : ℝ) :
    ((∃ q : LockedOrbitMass,
        q.Nonnegative ∧ q.total = T ∧ q.standardE = E ∧ q.standardA = A)
      ↔ |E + A| + |2 * E - A| ≤ 3 * T)
    ∧ (|E + A| + |2 * E - A| ≤ 3 * T ↔
      |E| ≤ T ∧ |A - E / 2| ≤ 3 * T / 2)
    ∧ (∀ D, (LockedOrbitMass.inverse T E A D).Nonnegative ↔
      -T + |E + A| ≤ D ∧ D ≤ 2 * T - |2 * E - A|) := by
  exact ⟨lockedOrbitMass_exists_iff T E A,
    lockedOrbit_diamond_iff_box T E A,
    LockedOrbitMass.inverse_nonnegative_iff T E A⟩

end NCG
