/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteCommutantPoincareGap
import NCG.Grand.RelativeHoweCertificate

/-!
# Actual relative Howe Gram certificate and spectral margin

This instantiates the generic Howe certificate at the stacked Hilbert--Schmidt commutator source
and couples it to the actual least eigenvalue of its restricted Gram matrix.
-/

open Matrix
open scoped ComplexOrder

namespace NCG

/-- The actual restricted commutator Gram has either zero carrier or an attained least positive
eigenvalue, with its sharp quadratic lower bound. -/
def RelativeHoweSpectralMargin {n : Type*} [Fintype n] {s : ℕ}
    (c : Fin s → Matrix n n ℂ) : Prop :=
  let K : Submodule ℂ (EuclideanSpace ℂ (n × n)) :=
    (LinearMap.ker (jointCommutatorL2 c))ᗮ
  K = ⊥ ∨
    ∃ (r : ℕ) (G : Matrix (Fin r) (Fin r) ℂ)
      (hG : G.PosDef) (lam : ℝ),
      r = Module.finrank ℂ K
      ∧ 0 < lam
      ∧ (∃ i : Fin r, lam = hG.1.eigenvalues i)
      ∧ (∀ i : Fin r, lam ≤ hG.1.eigenvalues i)
      ∧ ∀ (X P : Matrix n n ℂ),
        (∀ j, c j * P = P * c j) →
        matrixL2 (X - P) ∈ K →
        lam * (((X - P)ᴴ * (X - P)).trace).re ≤
          ∑ j, (((c j * X - X * c j)ᴴ *
            (c j * X - X * c j)).trace).re
/-- **Finite positive certificate for the exact multiplicity algebra
(`thm:SMST-relative-Howe-certificate`).**  Positivity of the actual joint-commutator Gram on the
orthogonal complement of the proposed algebra is equivalent to exactness; its kernel is the
matrix commutant; and the restricted Gram has an attained least positive eigenvalue unless its
orthogonal carrier is zero. -/
theorem relativeHoweGram_exact_certificate_and_margin
    {n : Type*} [Fintype n] {s : ℕ}
    (c : Fin s → Matrix n n ℂ)
    (M : Submodule ℂ (EuclideanSpace ℂ (n × n)))
    (hM : M ≤ LinearMap.ker (jointCommutatorL2 c)) :
    ((∀ X ∈ Mᗮ, X ≠ 0 → 0 < ‖jointCommutatorL2 c X‖ ^ 2)
        ↔ LinearMap.ker (jointCommutatorL2 c) = M)
    ∧ (∀ X : Matrix n n ℂ,
        matrixL2 X ∈ LinearMap.ker (jointCommutatorL2 c)
          ↔ ∀ j, c j * X = X * c j)
    ∧ (LinearMap.ker (jointCommutatorL2 c) = M →
        (LinearMap.ker (jointCommutatorL2 c))ᗮ = Mᗮ)
    ∧ RelativeHoweSpectralMargin c := by
  refine ⟨howe_certificate (jointCommutatorL2 c) M hM, ?_, ?_, ?_⟩
  · exact matrixL2_mem_jointCommutator_ker_iff c
  · intro hker
    rw [hker]
  · simpa [RelativeHoweSpectralMargin] using matrix_commutant_least_eigenvalue_gap c

end NCG




