/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteAnchorHowe
import NCG.Grand.RelativeHoweGramSpectralCertificateExact

/-!
# Finite-anchor locking for the actual Howe commutator source

This file specializes the abstract perturbative floor to the Hilbert--Schmidt joint commutator
map at two cutoffs and closes the kernel/exact-commutant conclusion with the Howe certificate.
-/

namespace NCG

/-- **Finite-anchor locking of the Howe commutant (`thm:SMST-finite-anchor-Howe`).**
For the actual stacked commutator sources, an anchor floor and the manuscript's strict
`4(C_X+C_X₀) ε < γ₀` perturbation budget give the exact later commutant and the advertised
positive lower spectral margin. -/
theorem finiteAnchorHowe_actualJointCommutator
    {n : Type*} [Fintype n] {s : ℕ}
    (c₀ c : Fin s → Matrix n n ℂ)
    (M : Submodule ℂ (EuclideanSpace ℂ (n × n)))
    (γ₀ C C₀ ε : ℝ)
    (hγ : 0 < γ₀) (hC : 0 ≤ C) (hC₀ : 0 ≤ C₀) (hε : 0 ≤ ε)
    (hM₀ : M ≤ LinearMap.ker (jointCommutatorL2 c₀))
    (hM : M ≤ LinearMap.ker (jointCommutatorL2 c))
    (hanchor : ∀ x ∈ Mᗮ,
      γ₀ * ‖x‖ ^ 2 ≤ ‖jointCommutatorL2 c₀ x‖ ^ 2)
    (hpert : ∀ x,
      |‖jointCommutatorL2 c x‖ ^ 2 - ‖jointCommutatorL2 c₀ x‖ ^ 2|
        ≤ 4 * (C + C₀) * ε * ‖x‖ ^ 2)
    (hsmall : 4 * (C + C₀) * ε < γ₀) :
    LinearMap.ker (jointCommutatorL2 c) = M
    ∧ 0 < γ₀ - 4 * (C + C₀) * ε
    ∧ (∀ x ∈ Mᗮ,
        (γ₀ - 4 * (C + C₀) * ε) * ‖x‖ ^ 2
          ≤ ‖jointCommutatorL2 c x‖ ^ 2)
    ∧ (∀ X : Matrix n n ℂ,
        matrixL2 X ∈ LinearMap.ker (jointCommutatorL2 c)
          ↔ ∀ j, c j * X = X * c j)
    ∧ RelativeHoweSpectralMargin c := by
  let δ : ℝ := 4 * (C + C₀) * ε
  have hδ : 0 ≤ δ := by
    dsimp [δ]
    positivity
  have hfloor : ∀ x ∈ Mᗮ,
      (γ₀ - δ) * ‖x‖ ^ 2 ≤ ‖jointCommutatorL2 c x‖ ^ 2 := by
    intro x hx
    have ha := hanchor x hx
    have hp := (abs_le.mp (hpert x)).1
    dsimp [δ] at hp ⊢
    nlinarith [sq_nonneg ‖x‖]
  have hmargin : 0 < γ₀ - δ := by
    dsimp [δ]
    linarith
  have hpos : ∀ x ∈ Mᗮ, x ≠ 0 → 0 < ‖jointCommutatorL2 c x‖ ^ 2 := by
    intro x hx hne
    have hxnorm : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hne)
    have hf := hfloor x hx
    nlinarith
  have hker : LinearMap.ker (jointCommutatorL2 c) = M :=
    (howe_certificate (jointCommutatorL2 c) M hM).1 hpos
  refine ⟨hker, ?_, ?_, matrixL2_mem_jointCommutator_ker_iff c, ?_⟩
  · simpa [δ] using hmargin
  · simpa [δ] using hfloor
  · exact matrix_commutant_least_eigenvalue_gap c

/-- The summable-tail hypothesis controls every later telescoped tuple displacement, the exact
budget input used by the finite-anchor theorem. -/
theorem finiteAnchorHowe_summableTail_budget
    (ε : ℕ → ℝ) (X₀ : ℕ) (b : ℝ)
    (hε : ∀ n, 0 ≤ ε n)
    (hsum : Summable fun n => ε (n + X₀))
    (hbound : (∑' n, ε (n + X₀)) < b) :
    ∀ N : ℕ, (∑ n ∈ Finset.range N, ε (n + X₀)) < b :=
  summable_tail_lock ε X₀ b hε hsum hbound

end NCG
