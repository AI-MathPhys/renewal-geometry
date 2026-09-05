/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Rephasing reconstruction from mixing panels

The pair and quartet panels in `thm:SM-mixing-invariants` determine a
full-support relative eigenframe up to diagonal row and column phases.  This
module proves that assertion directly over arbitrary finite index types.
-/

open Matrix

namespace NCG
namespace MixingPanelRephasingReconstruction

/-- Squared-modulus pair panel, retained as a complex scalar for algebraic use. -/
def pairPanel {ι κ : Type*} (V : Matrix ι κ ℂ) (i : ι) (j : κ) : ℂ :=
  star (V i j) * V i j

/-- The four-entry rephasing-invariant quartet panel. -/
def quartetPanel {ι κ : Type*} (V : Matrix ι κ ℂ)
    (i k : ι) (j l : κ) : ℂ :=
  V i j * star (V k j) * V k l * star (V i l)

private lemma star_mul_self_ne_zero {z : ℂ} (hz : z ≠ 0) :
    star z * z ≠ 0 := by
  exact mul_ne_zero (star_ne_zero.mpr hz) hz

private lemma ratio_is_phase (x y : ℂ) (hy : y ≠ 0)
    (hxy : star x * x = star y * y) :
    star (x / y) * (x / y) = 1 := by
  rw [star_div₀]
  field_simp [hy, star_ne_zero.mpr hy]
  simpa [mul_assoc] using hxy

private lemma quotient_of_phases_is_phase (x y : ℂ)
    (hx : star x * x = 1) (hy : star y * y = 1) :
    star (x / y) * (x / y) = 1 := by
  have hy0 : y ≠ 0 := by
    intro h
    subst y
    simp at hy
  exact ratio_is_phase x y hy0 (hx.trans hy.symm)

/-- On the full-support branch, equality of every pair and quartet panel is
equivalent to equality up to diagonal row and column rephasing.

The proof constructs the phases from one base row and one base column; no
choice of eigenvector phases is hidden in the statement. -/
theorem fullSupport_panels_determine_rephasing
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (V W : Matrix ι κ ℂ) (i₀ : ι) (j₀ : κ)
    (hV : ∀ i j, V i j ≠ 0)
    (hW : ∀ i j, W i j ≠ 0)
    (hpair : ∀ i j, pairPanel V i j = pairPanel W i j)
    (hquartet : ∀ i k j l,
      quartetPanel V i k j l = quartetPanel W i k j l) :
    ∃ r : ι → ℂ, ∃ c : κ → ℂ,
      (∀ i, star (r i) * r i = 1) ∧
      (∀ j, star (c j) * c j = 1) ∧
      (∀ i j, W i j = r i * V i j * c j) := by
  let r : ι → ℂ := fun i => W i j₀ / V i j₀
  let q : κ → ℂ := fun j => W i₀ j / V i₀ j
  let c : κ → ℂ := fun j => q j / r i₀
  have hr : ∀ i, star (r i) * r i = 1 := by
    intro i
    apply ratio_is_phase
    · exact hV i j₀
    · exact (hpair i j₀).symm
  have hq : ∀ j, star (q j) * q j = 1 := by
    intro j
    apply ratio_is_phase
    · exact hV i₀ j
    · exact (hpair i₀ j).symm
  have hc : ∀ j, star (c j) * c j = 1 := by
    intro j
    exact quotient_of_phases_is_phase (q j) (r i₀) (hq j) (hr i₀)
  refine ⟨r, c, hr, hc, ?_⟩
  intro i j
  have hquart := hquartet i i₀ j j₀
  have hpRow := hpair i₀ j
  have hpCol := hpair i j₀
  simp only [quartetPanel, pairPanel] at hquart hpRow hpCol
  have hcross :
      W i j₀ * V i j * W i₀ j * V i₀ j₀ =
        W i j * V i j₀ * V i₀ j * W i₀ j₀ := by
    have hscaled :
        star (V i₀ j) * star (V i j₀) *
          (W i j₀ * V i j * W i₀ j * V i₀ j₀ -
            W i j * V i j₀ * V i₀ j * W i₀ j₀) = 0 := by
      linear_combination
        (W i₀ j * W i j₀) * (hquart) +
        (-W i j * W i₀ j₀ * (star (V i j₀) * V i j₀)) * (hpRow) +
        (-W i j * W i₀ j₀ * (star (W i₀ j) * W i₀ j)) * (hpCol)
    have hsRow : star (V i₀ j) ≠ 0 := star_ne_zero.mpr (hV i₀ j)
    have hsCol : star (V i j₀) ≠ 0 := star_ne_zero.mpr (hV i j₀)
    have hfactor : star (V i₀ j) * star (V i j₀) ≠ 0 :=
      mul_ne_zero hsRow hsCol
    have := (mul_eq_zero.mp hscaled)
    have hzero :
        W i j₀ * V i j * W i₀ j * V i₀ j₀ -
          W i j * V i j₀ * V i₀ j * W i₀ j₀ = 0 :=
      this.resolve_left hfactor
    exact sub_eq_zero.mp hzero
  dsimp [r, q, c]
  field_simp [hV i j₀, hV i₀ j, hV i₀ j₀, hW i₀ j₀]
  simpa [mul_assoc, mul_left_comm, mul_comm] using hcross.symm

end MixingPanelRephasingReconstruction
end NCG
