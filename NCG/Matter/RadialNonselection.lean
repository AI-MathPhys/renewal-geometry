/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Radial nonselection (`prop:radial-nonselection`, SM manuscript)

Fix nonzero profiles `A_s⁰, B_s⁰` with residues
`Z_Φ⁰ = Σ_s Tr(A_s⁰†A_s⁰)` and `4Z_Ω⁰ = Σ_s Tr(B_s⁰†B_s⁰)`.  For
every `p ∈ (0,1)`, the rescaled family
`A_s(p) = √((1−p)/Z_Φ⁰)·A_s⁰`, `B_s(p) = √(p/Z_Ω⁰)·B_s⁰` has

  `Z_Φ(p) = 1 − p`, `Z_Ω(p) = p`,

while all normalized profiles remain unchanged
(`A_s(p)/√Z_Φ(p) = A_s⁰/√Z_Φ⁰` and likewise for `B`), hence so do
ranks and singular subspaces: representation architecture and
normalized profile shape cannot select the singlet–adjoint radial
fraction (interpretive prose).
-/

open Matrix

namespace NCG

/-- The real residue trace `Σ_s Tr(M_s†M_s)`. -/
noncomputable def residueTrace {ι n m : Type*} [Fintype ι]
    [Fintype n] [Fintype m]
    (M : ι → Matrix n m ℂ) : ℝ :=
  ∑ s, (Matrix.trace ((M s)ᴴ * M s)).re

/-- Residues scale quadratically under real scalings. -/
lemma residueTrace_smul {ι n m : Type*} [Fintype ι] [Fintype n]
    [Fintype m] (c : ℝ) (M : ι → Matrix n m ℂ) :
    residueTrace (fun s => c • M s) = c ^ 2 * residueTrace M := by
  rw [residueTrace, residueTrace, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  have hsmul : (c • M s)ᴴ = c • (M s)ᴴ := by
    ext i j
    simp [Matrix.conjTranspose_apply]
  rw [hsmul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.trace_smul]
  have h2 : ((c * c : ℝ) • Matrix.trace ((M s)ᴴ * M s)).re
      = c ^ 2 * (Matrix.trace ((M s)ᴴ * M s)).re := by
    rw [Complex.real_smul, Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [h2]

/-- `prop:radial-nonselection`: the rescaled family realizes every
radial fraction `p` with unchanged normalized profiles. -/
theorem radial_nonselection {ι n m n' m' : Type*} [Fintype ι]
    [Fintype n] [Fintype m] [Fintype n'] [Fintype m']
    (A0 : ι → Matrix n m ℂ) (B0 : ι → Matrix n' m' ℂ)
    (hA : 0 < residueTrace A0) (hB : 0 < residueTrace B0 / 4)
    (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    -- the realized residues
    (residueTrace (fun s =>
        Real.sqrt ((1 - p) / residueTrace A0) • A0 s) = 1 - p) ∧
    (residueTrace (fun s =>
        Real.sqrt (p / (residueTrace B0 / 4)) • B0 s) / 4 = p) ∧
    -- unchanged normalized profiles
    (∀ s : ι, (Real.sqrt (1 - p))⁻¹
        • (Real.sqrt ((1 - p) / residueTrace A0) • A0 s)
      = (Real.sqrt (residueTrace A0))⁻¹ • A0 s) ∧
    (∀ s : ι, (Real.sqrt p)⁻¹
        • (Real.sqrt (p / (residueTrace B0 / 4)) • B0 s)
      = (Real.sqrt (residueTrace B0 / 4))⁻¹ • B0 s) := by
  have h1p : (0 : ℝ) < 1 - p := by linarith
  have hAne : residueTrace A0 ≠ 0 := hA.ne'
  have hBne : residueTrace B0 / 4 ≠ 0 := hB.ne'
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [residueTrace_smul,
      Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (1 - p) / residueTrace A0)]
    field_simp
  · rw [residueTrace_smul,
      Real.sq_sqrt (by positivity :
        (0 : ℝ) ≤ p / (residueTrace B0 / 4))]
    have hB0 : residueTrace B0 ≠ 0 := by
      intro h
      rw [h] at hBne
      norm_num at hBne
    field_simp
  · intro s
    rw [smul_smul]
    congr 1
    rw [Real.sqrt_div h1p.le, div_eq_mul_inv, ← mul_assoc,
      inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr h1p), one_mul]
  · intro s
    rw [smul_smul]
    congr 1
    rw [Real.sqrt_div hp0.le, div_eq_mul_inv, ← mul_assoc,
      inv_mul_cancel₀ (Real.sqrt_ne_zero'.mpr hp0), one_mul]

end NCG
