/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Pressure-adapted coherent ADM packet and the Cartan torsion
  criterion (`thm:master-coherent-ADM-v036`,
  `thm:master-Cartan-v036`, flagship manuscript)

* `lapse_bounds`: clause (i) of the ADM packet — the boxed
  physical lapse `𝒩ₕ = βₕ·ℓ₀,ₕ` inherits positive upper and
  lower bounds on every compact pressure phase;
* `holder_exponent_window`: clause (v) — the `L^p` face packet
  with `p > 4` leaves a nonempty Hölder window
  `0 < 1 - 4/p`, so a `C^{0,α}` ADM response metric exists for
  every `α < 1 - 4/p`;
* `cartan_unique_rotation`: clauses (iv)–(v) of the Cartan
  criterion — for the complete mixed torsion
  `T(ω₀) = D + (ω₀ - S)E - R` (with `D` the transported frame
  derivative, `S = βʲωⱼ`, `R = 𝒩E^{-T}K`), the unique
  Cartan-compatible temporal rotation is
  `ω₀^C = S + (R - D)E⁻¹`, and once spatial torsion vanishes
  `T = 0 ⟺ ω₀ = ω₀^C` exactly.

Rendering disclosed: the regulator hypotheses (P1)–(P5), the
environment-unitary transport, the cb-generator bounds, the
matrix-`Log` face estimate, the connection-atlas compactness
argument, and the shift-isotypic `I₃ ⊗ Cₕ` Gram identification
are the manuscript's analytic layer; the lapse interval
arithmetic, the Hölder window, and the exact Cartan rotation
algebra are proved here.
-/

open Matrix

namespace NCG

/-- ADM clause (i): the boxed lapse `𝒩 = β·ℓ` has positive
two-sided bounds from the compact-phase bounds on `β` and `ℓ`. -/
theorem lapse_bounds (β ℓ a A b B : ℝ) (ha : 0 < a)
    (hb : 0 < b) (hβl : a ≤ β) (hβu : β ≤ A) (hℓl : b ≤ ℓ)
    (hℓu : ℓ ≤ B) :
    0 < β * ℓ ∧ a * b ≤ β * ℓ ∧ β * ℓ ≤ A * B := by
  have hβ0 : 0 < β := lt_of_lt_of_le ha hβl
  have hℓ0 : 0 < ℓ := lt_of_lt_of_le hb hℓl
  refine ⟨mul_pos hβ0 hℓ0, ?_, ?_⟩
  · nlinarith
  · nlinarith

/-- ADM clause (v): `p > 4` leaves the nonempty Hölder window
`0 < 1 - 4/p`. -/
theorem holder_exponent_window (p : ℝ) (hp : 4 < p) :
    0 < 1 - 4 / p := by
  have hp0 : 0 < p := by linarith
  have : 4 / p < 1 := (div_lt_one hp0).mpr hp
  linarith

/-- Cartan clauses (iv)–(v): with mixed torsion
`T(ω₀) = D + (ω₀ - S)E - R` and invertible coframe `E`, the
unique torsion-free temporal rotation is
`ω₀^C = S + (R - D)E⁻¹`. -/
theorem cartan_unique_rotation {n : Type*} [Fintype n]
    [DecidableEq n]
    (D S R E Einv : Matrix n n ℂ)
    (hEr : E * Einv = 1) (hEl : Einv * E = 1)
    (ω : Matrix n n ℂ) :
    D + (ω - S) * E - R = 0
      ↔ ω = S + (R - D) * Einv := by
  constructor
  · intro h
    have h1 : (ω - S) * E = R - D := by
      have := congrArg (fun M => M + R - D) h
      simpa [add_sub_cancel, sub_add_cancel, zero_add,
        add_comm, add_left_comm, add_sub_assoc] using this
    have h2 : (ω - S) * E * Einv = (R - D) * Einv :=
      congrArg (fun M => M * Einv) h1
    rw [Matrix.mul_assoc, hEr, Matrix.mul_one] at h2
    have := congrArg (fun M => M + S) h2
    simpa [sub_add_cancel, add_comm] using this
  · intro h
    rw [h]
    have hcan : (S + (R - D) * Einv - S) * E = R - D := by
      rw [add_sub_cancel_left, Matrix.mul_assoc, hEl,
        Matrix.mul_one]
    rw [hcan]
    abel

end NCG
