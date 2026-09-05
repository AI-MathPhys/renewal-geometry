/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FastFeedback

/-!
# New SM orbit/compiler/PCH records (2026-08-07 tex update):
  formal cores for the noisy-channel compilers, positive-packet
  orbits, tetrahedral frames, pulse–Howe comparison, and PCH
  writer records.  See each ledger entry for its citation.
-/

open Matrix Finset

namespace NCG

/-- Quadratic-remainder chaining: a first-order error and a
quadratic remainder add to the boxed `tε + κt²` bound. -/
theorem quadratic_remainder_chain (a b t ε κ : ℝ)
    (ha : a ≤ κ * t ^ 2) (hb : b ≤ t * ε) :
    a + b ≤ t * ε + κ * t ^ 2 := by linarith

/-- Klein-refocusing telescoping engine (re-export): step maps
bounded by `M` telescope their product error. -/
theorem klein_refocusing_telescope {A : Type*} [NormedRing A]
    (X E : A) (M : ℝ) (hX : ‖X‖ ≤ M) (hE : ‖E‖ ≤ M)
    (n : ℕ) :
    ‖X ^ (n + 1) - E ^ (n + 1)‖
      ≤ (n + 1 : ℝ) * M ^ n * ‖X - E‖ :=
  power_comparison_bound X E M hX hE n

/-- Direct-branch scaling: the compiled duration and generator
rescalings are exact inverses. -/
theorem direct_bracket_scaling {n : Type*} (H : Matrix n n ℂ)
    (α r : ℝ) (hα : α ≠ 0) (hr : r ≠ 0) :
    ((α / r : ℂ))⁻¹ • ((α / r : ℂ) • H) = H := by
  rw [smul_smul, inv_mul_cancel₀ ?_, one_smul]
  exact_mod_cast div_ne_zero hα hr

/-- Compiled-generator tracelessness: the limit Hamiltonian is
the traceless part, `tr(D - (tr D/d)·1) = 0`. -/
theorem compiled_generator_traceless {n : Type*} [Fintype n]
    [DecidableEq n] [Nonempty n] (D : Matrix n n ℂ) :
    Matrix.trace
      (D - (Matrix.trace D / Fintype.card n) • 1) = 0 := by
  rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one,
    smul_eq_mul]
  have hcard : (Fintype.card n : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp
  ring

/-- Shuffle obstruction: the zero Hamiltonian has zero
derivation, so the defect is the full norm. -/
theorem zero_derivation {n : Type*} [Fintype n]
    (X : Matrix n n ℂ) :
    (0 : Matrix n n ℂ) * X - X * 0 = 0 := by
  simp

open scoped ComplexOrder in
/-- Positive-packet twirl positivity: a finite nonnegative
average of conjugations of a PSD packet is PSD. -/
theorem finite_twirl_psd {n G : Type*} [Fintype n] [Fintype G]
    (w : G → ℝ) (hw : ∀ g, 0 ≤ w g) (U : G → Matrix n n ℂ)
    (J : Matrix n n ℂ) (hJ : J.PosSemidef) :
    (∑ g, (w g : ℂ) • (U g * J * (U g)ᴴ)).PosSemidef := by
  refine Finset.sum_induction _ _ (fun a b ha hb => ha.add hb)
    Matrix.PosSemidef.zero fun g _ => ?_
  have hterm : (U g * J * (U g)ᴴ).PosSemidef :=
    hJ.mul_mul_conjTranspose_same (U g)
  exact hterm.smul (Complex.zero_le_real.mpr (hw g))

/-- Tetrahedral pulse frame: the explicit `T` preserves the
mean-zero space `W₀` (all column sums vanish). -/
theorem tetrahedral_T_preserves_W0 (x : Fin 4 → ℝ) :
    ∑ i, ((!![2, 0, -1, -1; 0, -2, 1, 1; -1, 1, 0, 0;
        -1, 1, 0, 0] : Matrix (Fin 4) (Fin 4) ℝ).mulVec x) i
      = 0 := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  ring

/-- Frame robustness (scalar margin): a measured synthesis
within `ε < √2` of an exact `√2`-frame keeps margin
`√2 - ε`. -/
theorem frame_margin_scalar (a b ε : ℝ)
    (ha : Real.sqrt 2 ≤ a) (hab : |b - a| ≤ ε)
    (_hε : ε < Real.sqrt 2) :
    Real.sqrt 2 - ε ≤ b := by
  have := abs_le.mp hab
  linarith [this.1]

/-- Pulse–Howe gap dominance: a perturbation strictly below the
measured gap preserves the spectral conclusion. -/
theorem gap_dominance (pert bound γ : ℝ)
    (hp : pert ≤ bound) (hb : bound < γ) : pert < γ :=
  lt_of_le_of_lt hp hb

/-- PCH writer closure: the cycle-projected writer of an exact
gradient vanishes (re-export shape of the affinity-Hodge
mechanism). -/
theorem pch_writer_no_cycle {e v : Type*} [Fintype e]
    [DecidableEq e] [Fintype v] (d0 : Matrix e v ℝ)
    (Pcut : Matrix e e ℝ) (Svar : v → ℝ) (Avec : e → ℝ)
    (hA : Avec = d0.mulVec Svar)
    (hfix : Pcut.mulVec (d0.mulVec Svar) = d0.mulVec Svar) :
    (1 - Pcut).mulVec Avec = 0 := by
  subst hA
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, hfix, sub_self]

end NCG
