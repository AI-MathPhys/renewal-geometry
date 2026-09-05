/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteTorusCovariantSymbolCutoffLimit
import NCG.Grand.IntegerFourierBox

/-!
# Centered frequency windows for finite tori

This file realizes the frequency set of the `(N + 1)`-point torus as a
literal finite subset of the integer Fourier lattice.  It also records the
Nyquist estimate satisfied by every centered representative and the eventual
inclusion of each fixed continuum Fourier box.
-/

noncomputable section

open Filter Finset

namespace NCG

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The centered integer frequencies represented by the `(N + 1)`-point
finite torus. -/
def finiteTorusCenteredFrequencyWindow (N : ℕ) : Finset (d → ℤ) :=
  Finset.univ.image
    (finiteTorusCenteredFrequency (N := N + 1) (d := d))

theorem mem_finiteTorusCenteredFrequencyWindow_iff
    (N : ℕ) (k : d → ℤ) :
    k ∈ finiteTorusCenteredFrequencyWindow (d := d) N ↔
      ∃ q : d → ZMod (N + 1),
        finiteTorusCenteredFrequency q = k := by
  classical
  simp [finiteTorusCenteredFrequencyWindow]

/-- Every centered finite-torus frequency lies in the Nyquist band for the
cutoff mesh `1 / (N + 1)`. -/
theorem finiteTorusCenteredFrequency_nyquist
    (N : ℕ) (q : d → ZMod (N + 1)) (j : d) :
    |2 * Real.pi * finiteTorusCutoffMesh N *
        (finiteTorusCenteredFrequency q j : ℝ)| ≤ Real.pi := by
  have habsNat :
      (finiteTorusCenteredFrequency q j).natAbs ≤ (N + 1) / 2 := by
    exact ZMod.natAbs_valMinAbs_le (q j)
  have habs :
      |(finiteTorusCenteredFrequency q j : ℝ)| ≤ ((N + 1 : ℕ) : ℝ) / 2 := by
    calc
      |(finiteTorusCenteredFrequency q j : ℝ)| =
          ((finiteTorusCenteredFrequency q j).natAbs : ℝ) := by
            simpa only [Int.cast_abs, Int.cast_natCast] using
              congrArg (fun z : ℤ ↦ (z : ℝ))
                (Int.abs_eq_natAbs (finiteTorusCenteredFrequency q j))
      _ ≤ (((N + 1) / 2 : ℕ) : ℝ) :=
        Nat.cast_le.2 habsNat
      _ ≤ ((N + 1 : ℕ) : ℝ) / 2 := Nat.cast_div_le
  rw [abs_mul, abs_mul,
    abs_of_pos (mul_pos (by positivity : (0 : ℝ) < 2) Real.pi_pos)]
  unfold finiteTorusCutoffMesh
  have hpos : (0 : ℝ) < (N + 1 : ℕ) := by positivity
  rw [abs_of_pos (inv_pos.mpr hpos)]
  calc
    2 * Real.pi * ((N + 1 : ℕ) : ℝ)⁻¹ *
        |(finiteTorusCenteredFrequency q j : ℝ)|
        ≤ 2 * Real.pi * ((N + 1 : ℕ) : ℝ)⁻¹ *
            (((N + 1 : ℕ) : ℝ) / 2) := by
          exact mul_le_mul_of_nonneg_left habs (by positivity)
    _ = Real.pi := by field_simp

theorem mem_finiteTorusCenteredFrequencyWindow_nyquist
    (N : ℕ) {k : d → ℤ}
    (hk : k ∈ finiteTorusCenteredFrequencyWindow (d := d) N) :
    ∀ j, |2 * Real.pi * finiteTorusCutoffMesh N * (k j : ℝ)| ≤ Real.pi := by
  obtain ⟨q, rfl⟩ :=
    (mem_finiteTorusCenteredFrequencyWindow_iff (d := d) N k).1 hk
  exact finiteTorusCenteredFrequency_nyquist N q

/-- Every fixed finite set of continuum frequencies is eventually contained
in the centered finite-torus frequency window. -/
theorem eventually_finset_subset_finiteTorusCenteredFrequencyWindow
    (s : Finset (d → ℤ)) :
    ∀ᶠ N : ℕ in atTop,
      s ⊆ finiteTorusCenteredFrequencyWindow (d := d) N := by
  filter_upwards
      [eventually_forall_mem_finiteBox_centeredFrequency_intCast_eq s]
      with N hN k hk
  rw [mem_finiteTorusCenteredFrequencyWindow_iff]
  exact ⟨fun j ↦ (k j : ZMod (N + 1)), hN k hk⟩

theorem eventually_integerFourierBox_subset_finiteTorusCenteredFrequencyWindow
    (R : ℕ) :
    ∀ᶠ N : ℕ in atTop,
      integerFourierBox (d := d) R ⊆
        finiteTorusCenteredFrequencyWindow (d := d) N :=
  eventually_finset_subset_finiteTorusCenteredFrequencyWindow
    (integerFourierBox (d := d) R)

end NCG
