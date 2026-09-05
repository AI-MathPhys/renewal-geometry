/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SingularPolarData
import NCG.Grand.PauliStoreBlockCommutant
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Exact SVD assembly for the store-block decomposition

This file supplies the basis-construction step in
`thm:store-block-decomposition`.  Starting with an arbitrary rectangular
corner, its positive polar factor is diagonalized by the finite-dimensional
spectral theorem.  The strictly positive eigenvalues are then grouped into
distinct frequencies, with their fibres as multiplicity spaces.  The latter
indexing is exactly the one used by the assembled Pauli-block commutant
theorem.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

namespace NCG
namespace StoreBlockSVDAssemblyExact

set_option maxHeartbeats 800000

/-- The distinct strictly positive values occurring in a finite frequency
list. -/
noncomputable def positiveFrequencies {e : ℕ} (mu : Fin e → ℝ) : Finset ℝ :=
  (Finset.univ.image mu).filter (0 < ·)

/-- Index type for the distinct positive singular frequencies. -/
abbrev FrequencyIndex {e : ℕ} (mu : Fin e → ℝ) :=
  {x : ℝ // x ∈ positiveFrequencies mu}

/-- The multiplicity space of a positive frequency. -/
abbrev Multiplicity {e : ℕ} (mu : Fin e → ℝ)
    (j : FrequencyIndex mu) :=
  {i : Fin e // mu i = j.1}

/-- The frequency attached to a grouped singular block. -/
def frequency {e : ℕ} (mu : Fin e → ℝ) (j : FrequencyIndex mu) : ℝ := j.1

theorem frequency_pos {e : ℕ} (mu : Fin e → ℝ) :
    ∀ j : FrequencyIndex mu, 0 < frequency mu j := by
  intro j
  exact (Finset.mem_filter.mp j.2).2

theorem frequency_injective {e : ℕ} (mu : Fin e → ℝ) :
    Function.Injective (frequency mu) := by
  intro i j h
  exact Subtype.ext h

/-- The exact Pauli-block and joint-commutant assertion associated with a
finite singular-frequency list. -/
def GroupedPositiveFrequencyCertificate {e : ℕ} (mu : Fin e → ℝ) : Prop :=
    let J := FrequencyIndex mu
    let M : J → Type := Multiplicity mu
    (PauliStoreBlockCommutant.storeGrading (J := J) (M := M))ᴴ =
        PauliStoreBlockCommutant.storeGrading (J := J) (M := M)
      ∧ (PauliStoreBlockCommutant.storeDwell (M := M) (frequency mu))ᴴ =
        PauliStoreBlockCommutant.storeDwell (M := M) (frequency mu)
      ∧ PauliStoreBlockCommutant.storeGrading (J := J) (M := M) *
          PauliStoreBlockCommutant.storeDwell (M := M) (frequency mu) =
        -(PauliStoreBlockCommutant.storeDwell (M := M) (frequency mu) *
          PauliStoreBlockCommutant.storeGrading (J := J) (M := M))
      ∧ ∀ R : Matrix (PauliStoreBlockCommutant.StoreIndex J M)
          (PauliStoreBlockCommutant.StoreIndex J M) ℂ,
        (R * PauliStoreBlockCommutant.storeGrading (J := J) (M := M) =
            PauliStoreBlockCommutant.storeGrading (J := J) (M := M) * R ∧
          R * PauliStoreBlockCommutant.storeDwell (M := M) (frequency mu) =
            PauliStoreBlockCommutant.storeDwell (M := M) (frequency mu) * R) ↔
          ∃ K : Matrix (PauliStoreBlockCommutant.MultiplicityIndex J M)
              (PauliStoreBlockCommutant.MultiplicityIndex J M) ℂ,
            R = PauliStoreBlockCommutant.multiplicityOperator K

/-- Once equal positive frequencies have been grouped, the Pauli normal form
has precisely the manuscript's joint commutant
`⊕j (I₂ ⊗ B(M_j))`. -/
theorem grouped_positive_frequency_certificate {e : ℕ} (mu : Fin e → ℝ) :
    GroupedPositiveFrequencyCertificate mu := by
  classical
  exact PauliStoreBlockCommutant.assembled_pauli_store_block_certificate
    (frequency mu) (frequency_pos mu) (frequency_injective mu)

/-- Genuine finite-dimensional polar SVD of an arbitrary rectangular corner.

`V` is unitary, `mu` is nonnegative, `P = V diag(mu) Vᴴ`, and hence
`F = U V diag(mu) Vᴴ`.  The last conjunct records the exact Pauli-block and
joint-commutant certificate obtained by grouping the positive values of
`mu`; zero modes are precisely the kernel discarded on `(ker L)⊥` in the
manuscript. -/
theorem exists_store_corner_svd {e : ℕ} {H : Type*} [Fintype H]
    (F : Matrix H (Fin e) ℂ) :
    ∃ (U : Matrix H (Fin e) ℂ) (P Pd V : Matrix (Fin e) (Fin e) ℂ)
      (mu : Fin e → ℝ),
      P.PosSemidef ∧ F = U * P ∧ P * P = Fᴴ * F ∧
      U * (Uᴴ * U) = U ∧ P * Pd = Uᴴ * U ∧ Pd * P = Uᴴ * U ∧
      Vᴴ * V = 1 ∧ V * Vᴴ = 1 ∧
      (∀ i, 0 ≤ mu i) ∧
      P = V * Matrix.diagonal (fun i => (mu i : ℂ)) * Vᴴ ∧
      F = U * V * Matrix.diagonal (fun i => (mu i : ℂ)) * Vᴴ ∧
      GroupedPositiveFrequencyCertificate mu := by
  classical
  rcases exists_singular_polar_data F with
    ⟨U, P, Pd, hP, hFUP, hP2, hUp, hPPd, hPdP, _⟩
  let hPH : P.IsHermitian := hP.isHermitian
  let W := hPH.eigenvectorUnitary
  let V : Matrix (Fin e) (Fin e) ℂ := W
  let mu : Fin e → ℝ := hPH.eigenvalues
  have hVstarV : Vᴴ * V = 1 := by
    change (star W : Matrix (Fin e) (Fin e) ℂ) * W = 1
    exact Unitary.coe_star_mul_self W
  have hVVstar : V * Vᴴ = 1 := by
    change (W : Matrix (Fin e) (Fin e) ℂ) * star W = 1
    exact Unitary.coe_mul_star_self W
  have hPdiag : P = V * Matrix.diagonal (fun i => (mu i : ℂ)) * Vᴴ := by
    change P = (W : Matrix (Fin e) (Fin e) ℂ) *
      Matrix.diagonal (Complex.ofReal ∘ hPH.eigenvalues) * star W
    exact hPH.spectral_theorem
  have hFdiag :
      F = U * V * Matrix.diagonal (fun i => (mu i : ℂ)) * Vᴴ := by
    rw [hFUP, hPdiag]
    simp only [Matrix.mul_assoc]
  exact ⟨U, P, Pd, V, mu, hP, hFUP, hP2, hUp, hPPd, hPdP,
    hVstarV, hVVstar, (fun i => hP.eigenvalues_nonneg i), hPdiag,
    hFdiag, grouped_positive_frequency_certificate mu⟩

/-- The store-block theorem with its previously separate ingredients assembled:
the grading corner form, the actual SVD basis construction, and the full
distinct-frequency multiplicity commutant. -/
theorem store_block_decomposition_with_svd {e h : ℕ}
    (F : Matrix (Fin h) (Fin e) ℂ) :
    (∃ (U : Matrix (Fin h) (Fin e) ℂ)
        (P Pd V : Matrix (Fin e) (Fin e) ℂ) (mu : Fin e → ℝ),
      P.PosSemidef ∧ F = U * P ∧ P * P = Fᴴ * F ∧
      U * (Uᴴ * U) = U ∧ P * Pd = Uᴴ * U ∧ Pd * P = Uᴴ * U ∧
      Vᴴ * V = 1 ∧ V * Vᴴ = 1 ∧ (∀ i, 0 ≤ mu i) ∧
      P = V * Matrix.diagonal (fun i => (mu i : ℂ)) * Vᴴ ∧
      F = U * V * Matrix.diagonal (fun i => (mu i : ℂ)) * Vᴴ ∧
      GroupedPositiveFrequencyCertificate mu)
    ∧ (∀ L : Matrix (Fin e ⊕ Fin h) (Fin e ⊕ Fin h) ℂ, Lᴴ = L →
      Matrix.fromBlocks (1 : Matrix (Fin e) (Fin e) ℂ) 0 0
          (-(1 : Matrix (Fin h) (Fin h) ℂ)) * L =
        -(L * Matrix.fromBlocks (1 : Matrix (Fin e) (Fin e) ℂ) 0 0
          (-(1 : Matrix (Fin h) (Fin h) ℂ))) →
      L = Matrix.fromBlocks 0 (L.toBlocks₂₁)ᴴ (L.toBlocks₂₁) 0) := by
  refine ⟨exists_store_corner_svd F, ?_⟩
  exact store_block_decomposition.1

end StoreBlockSVDAssemblyExact
end NCG
