/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.OneGenerationAudit

/-!
# numerical one-generation incidence audit

This instantiates the general Schur, cross-incidence, and two-component
commutant engines at the manuscript's exact module dimensions. It also turns
a merely nonzero incidence block into coefficient-one cross matrix units and
checks both the `12+3` and neutral-singlet `12+4` residuals.
-/

open Matrix

namespace NCG

/-- A nonzero incidence block, together with the full endpoint matrix
algebras, produces every cross matrix unit with coefficient one. -/
theorem nonzero_incidence_generates_cross_units
    {s r : Type} [Fintype s] [Fintype r]
    [DecidableEq s] [DecidableEq r]
    (Y : Matrix s r ℂ) (hY : Y ≠ 0) :
    ∃ i : s, ∃ j : r, ∀ (a : s) (b : r),
      Matrix.single a b (1 : ℂ) =
        (Y i j)⁻¹ •
          (Matrix.single a i (1 : ℂ) * Y *
            Matrix.single j b (1 : ℂ)) := by
  have hex : ∃ i : s, ∃ j : r, Y i j ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hY
    ext i j
    exact hn i j
  obtain ⟨i, j, hij⟩ := hex
  refine ⟨i, j, fun a b => ?_⟩
  calc
    Matrix.single a b (1 : ℂ) =
        (Y i j)⁻¹ • (Y i j • Matrix.single a b (1 : ℂ)) := by
          rw [smul_smul, inv_mul_cancel₀ hij, one_smul]
    _ = (Y i j)⁻¹ •
        (Matrix.single a i (1 : ℂ) * Y *
          Matrix.single j b (1 : ℂ)) := by
          have hcross : Matrix.single a i (1 : ℂ) * Y *
              Matrix.single j b (1 : ℂ) =
              Y i j • Matrix.single a b (1 : ℂ) :=
            smst_one_generation_audit.2.1 Y a i j b
          exact congrArg
            (fun M : Matrix s r ℂ => (Y i j)⁻¹ • M)
            hcross.symm

/-- Exact one-generation numerical instantiation: five irreducible gauge
blocks of dimensions `6,3,3,2,1`; three nonzero incidence edges; and the
two connected-component residuals `12+3` (or `12+4` with a neutral singlet). -/
theorem smst_one_generation_audit_exact :
    -- the displayed component dimensions
    (6 + 3 + 3 = 12) ∧ (2 + 1 = 3) ∧ (2 + 1 + 1 = 4)
    -- Schur on each of the five typed gauge modules
    ∧ (∀ T : Matrix (Fin 6) (Fin 6) ℂ,
        (∀ A, T * A = A * T) ↔ ∃ c : ℂ, T = c • 1)
    ∧ (∀ T : Matrix (Fin 3) (Fin 3) ℂ,
        (∀ A, T * A = A * T) ↔ ∃ c : ℂ, T = c • 1)
    ∧ (∀ T : Matrix (Fin 2) (Fin 2) ℂ,
        (∀ A, T * A = A * T) ↔ ∃ c : ℂ, T = c • 1)
    ∧ (∀ T : Matrix (Fin 1) (Fin 1) ℂ,
        (∀ A, T * A = A * T) ↔ ∃ c : ℂ, T = c • 1)
    -- the Q-u, Q-d, and L-e edges generate all cross units
    ∧ (∀ Y : Matrix (Fin 6) (Fin 3) ℂ, Y ≠ 0 →
        ∃ (i : Fin 6) (j : Fin 3), ∀ (a : Fin 6) (b : Fin 3),
          Matrix.single a b (1 : ℂ) =
          (Y i j)⁻¹ •
            (Matrix.single a i (1 : ℂ) * Y *
              Matrix.single j b (1 : ℂ)))
    ∧ (∀ Y : Matrix (Fin 2) (Fin 1) ℂ, Y ≠ 0 →
        ∃ (i : Fin 2) (j : Fin 1), ∀ (a : Fin 2) (b : Fin 1),
          Matrix.single a b (1 : ℂ) =
          (Y i j)⁻¹ •
            (Matrix.single a i (1 : ℂ) * Y *
              Matrix.single j b (1 : ℂ)))
    -- residual commutants on the two connected components
    ∧ (∀ T : Matrix (Fin 12 ⊕ Fin 3) (Fin 12 ⊕ Fin 3) ℂ,
        (∀ (A : Matrix (Fin 12) (Fin 12) ℂ)
          (B : Matrix (Fin 3) (Fin 3) ℂ),
          T * Matrix.fromBlocks A 0 0 B =
            Matrix.fromBlocks A 0 0 B * T) ↔
        ∃ a b : ℂ,
          T = Matrix.fromBlocks (a • 1) 0 0 (b • 1))
    ∧ (∀ T : Matrix (Fin 12 ⊕ Fin 4) (Fin 12 ⊕ Fin 4) ℂ,
        (∀ (A : Matrix (Fin 12) (Fin 12) ℂ)
          (B : Matrix (Fin 4) (Fin 4) ℂ),
          T * Matrix.fromBlocks A 0 0 B =
            Matrix.fromBlocks A 0 0 B * T) ↔
        ∃ a b : ℂ,
          T = Matrix.fromBlocks (a • 1) 0 0 (b • 1)) := by
  refine ⟨by decide, by decide, by decide, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun T => smst_one_generation_audit.1 T
  · exact fun T => smst_one_generation_audit.1 T
  · exact fun T => smst_one_generation_audit.1 T
  · exact fun T => smst_one_generation_audit.1 T
  · intro Y hY
    exact nonzero_incidence_generates_cross_units Y hY
  · intro Y hY
    exact nonzero_incidence_generates_cross_units Y hY
  · exact fun T => smst_one_generation_audit.2.2 T
  · exact fun T => smst_one_generation_audit.2.2 T

end NCG
