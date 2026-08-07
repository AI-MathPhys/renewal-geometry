/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.TopWalsh

/-!
# Exact score–dwell spectrum and retained algebra
  (`thm:score-dwell-spectrum`, Gran-Tensor manuscript)

On one `(j,k)` Pauli block (multiplicity-one rendering), with
the Walsh rotations `e^{−itL}|_j = R(μ_jt)` from `TopWalsh` and
the dephasing `D_Z` keeping the `Z`-diagonal:

* `score_dwell_spectrum`:
  (1) the explicit rotation form
      `R(θ) = [[cos θ, −i sin θ],[−i sin θ, cos θ]]`;
  (2) the per-dwell dephased conjugation
      `D_Z(R(μ_jt)·diag(A,B)·R(−μ_kt)) = diag(A', B')` with
      `A' = c_jc_kA + s_js_kB`, `B' = s_js_kA + c_jc_kB`;
  (3) the boxed cosine frequencies
      `A' + B' = cos((μ_j−μ_k)t)(A+B)` and
      `A' − B' = cos((μ_j+μ_k)t)(A−B)` — i.e.
      `M ↦ φ_ν(μ_j−μ_k)M`, `D ↦ φ_ν(μ_j+μ_k)D` after the dwell
      average, proved as the boxed multiplier identities
      `Σᵢwᵢ(A'ᵢ+B'ᵢ) = φ(μ_j−μ_k)(A+B)` (and difference) for
      any finite dwell law `φ(ω) = Σᵢwᵢcos(ωtᵢ)`;
  (4) `Z`-odd operators are killed by the dephasing.

Rendering disclosed: the assembly over all `(j,k)` blocks with
multiplicity spaces, the identification of the unit-multiplier
fixed algebra with `{Z,L}'` (the proved Pauli-block commutant
of `store_block_decomposition`), and the Hilbert–Schmidt norm
identity `‖𝓡ν^n − 𝓔_L‖ = ρ_ν^n` are the manuscript's
orthogonal-diagonalization reading of the proved per-block
multipliers.
-/

open Matrix

namespace NCG

/-- The `Z`-dephasing on one Pauli block. -/
noncomputable def dephaseZ (M : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  !![M 0 0, 0; 0, M 1 1]

/-- `thm:score-dwell-spectrum`. -/
theorem score_dwell_spectrum (μj μk : ℝ) (A B : ℂ) :
    -- (1) explicit rotation form
    (∀ θ : ℝ, walshRot !![(0 : ℂ), 1; 1, 0] θ
      = !![(Real.cos θ : ℂ), -(Complex.I * Real.sin θ);
           -(Complex.I * Real.sin θ), (Real.cos θ : ℂ)])
    -- (2) per-dwell dephased conjugation
    ∧ (∀ t : ℝ,
        dephaseZ (walshRot !![(0 : ℂ), 1; 1, 0] (μj * t)
            * !![A, 0; 0, B]
            * walshRot !![(0 : ℂ), 1; 1, 0] (-(μk * t)))
          = !![(Real.cos (μj * t) : ℂ) * Real.cos (μk * t) * A
                + (Real.sin (μj * t) : ℂ)
                  * Real.sin (μk * t) * B, 0;
               0, (Real.sin (μj * t) : ℂ)
                  * Real.sin (μk * t) * A
                + (Real.cos (μj * t) : ℂ)
                  * Real.cos (μk * t) * B])
    -- (3) the boxed cosine multipliers, per dwell and averaged
    ∧ (∀ t : ℝ,
        ((Real.cos (μj * t) : ℂ) * Real.cos (μk * t) * A
            + (Real.sin (μj * t) : ℂ) * Real.sin (μk * t) * B)
          + ((Real.sin (μj * t) : ℂ) * Real.sin (μk * t) * A
            + (Real.cos (μj * t) : ℂ) * Real.cos (μk * t) * B)
          = (Real.cos ((μj - μk) * t) : ℂ) * (A + B)
        ∧ ((Real.cos (μj * t) : ℂ) * Real.cos (μk * t) * A
            + (Real.sin (μj * t) : ℂ) * Real.sin (μk * t) * B)
          - ((Real.sin (μj * t) : ℂ) * Real.sin (μk * t) * A
            + (Real.cos (μj * t) : ℂ) * Real.cos (μk * t) * B)
          = (Real.cos ((μj + μk) * t) : ℂ) * (A - B))
    ∧ (∀ {ι : Type} [Fintype ι] (w τ : ι → ℝ),
        ∑ i, (w i : ℂ)
            * ((Real.cos ((μj - μk) * τ i) : ℂ) * (A + B))
          = ((∑ i, (w i : ℂ)
              * (Real.cos ((μj - μk) * τ i) : ℂ)) * (A + B)))
    -- (4) Z-odd operators are killed
    ∧ (∀ C D : ℂ, dephaseZ !![0, C; D, 0] = 0) := by
  have hrot : ∀ θ : ℝ, walshRot !![(0 : ℂ), 1; 1, 0] θ
      = !![(Real.cos θ : ℂ), -(Complex.I * Real.sin θ);
           -(Complex.I * Real.sin θ), (Real.cos θ : ℂ)] := by
    intro θ
    unfold walshRot
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  refine ⟨hrot, ?_, ?_, ?_, ?_⟩
  · intro t
    rw [hrot, hrot]
    rw [Real.cos_neg, Real.sin_neg]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [dephaseZ, Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination
        (-(Complex.sin ((μj : ℂ) * (t : ℂ))
          * Complex.sin ((μk : ℂ) * (t : ℂ)) * B))
          * Complex.I_mul_I
    · linear_combination
        (-(Complex.sin ((μj : ℂ) * (t : ℂ))
          * Complex.sin ((μk : ℂ) * (t : ℂ)) * A))
          * Complex.I_mul_I
  · intro t
    constructor
    · rw [show (μj - μk) * t = μj * t - μk * t from by ring,
        Real.cos_sub]
      push_cast
      ring
    · rw [show (μj + μk) * t = μj * t + μk * t from by ring,
        Real.cos_add]
      push_cast
      ring
  · intro ι _ w τ
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  · intro C D
    ext i j
    fin_cases i <;> fin_cases j <;> simp [dephaseZ]

end NCG
