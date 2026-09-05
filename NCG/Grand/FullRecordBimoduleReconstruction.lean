/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.EquivariantMultiplicityFactorization
import NCG.Grand.OtherLoadingEmergence

/-!
# Faithful full endpoint-record bimodule and flat reconstruction

The full algebraic tensor of the two endpoint matrix algebras is represented
on the Hilbert--Schmidt link modes by a permutation of its four coefficient
indices.  This makes faithfulness an explicit inverse coordinate calculation,
not merely a statement about individual simple tensors.
-/

open Matrix
open scoped Kronecker

namespace NCG
namespace FullRecordBimoduleReconstruction

/-- Coefficient form of the full left/right endpoint-record representation.
The input coefficient of E_ij tensor E_kl^op sends the link-mode coordinate
(j,k) to (i,l). -/
def fullRecordRepresentation
    {L R : Type*}
    (K : Matrix (L × R) (L × R) ℂ) :
    Matrix (L × R) (L × R) ℂ :=
  fun out input => K (out.1, input.2) (input.1, out.2)

/-- The coefficient permutation is an involution. -/
theorem fullRecordRepresentation_involution
    {L R : Type*} (K : Matrix (L × R) (L × R) ℂ) :
    fullRecordRepresentation (fullRecordRepresentation K) = K := by
  ext ⟨i, k⟩ ⟨j, l⟩
  rfl

/-- Hence the complete endpoint tensor algebra acts faithfully, not only its
simple tensors. -/
theorem fullRecordRepresentation_injective
    {L R : Type*} :
    Function.Injective
      (fullRecordRepresentation :
        Matrix (L × R) (L × R) ℂ →
          Matrix (L × R) (L × R) ℂ) := by
  intro K H h
  have := congrArg fullRecordRepresentation h
  simpa [fullRecordRepresentation_involution] using this

/-- On a simple tensor, the full coefficient representation is exactly the
matrix of the bimodule action F maps to a F b. -/
theorem fullRecordRepresentation_simpleTensor_entry
    {L R : Type*} [Fintype L] [Fintype R]
    (a : Matrix L L ℂ) (b : Matrix R R ℂ)
    (i j : L) (k l : R) :
    fullRecordRepresentation (a ⊗ₖ b) (i, l) (j, k) =
      a i j * b k l := by
  rfl

/-- Complete reconstruction packet: equivariance gives the unique carrier-line
times multiplicity factor, the whole endpoint tensor algebra is faithful on
link modes, and every nested flat loaded word hierarchy has its canonical
positive source-minimal reconstruction. -/
theorem full_record_bimodule_and_flat_reconstruction
    {κ n m g g' : Type*} {h e : Type}
    [Fintype n] [Fintype m] [Fintype g] [Fintype g']
    [DecidableEq g] [DecidableEq g']
    [Fintype h] [Fintype e]
    (L : κ → Matrix n n ℂ) (R : κ → Matrix m m ℂ)
    (D : Matrix n m ℂ)
    (hSchur : ∀ Z : Matrix n m ℂ,
      (∀ q, L q * Z = Z * R q) →
        ∃! c : ℂ, Z = c • D)
    (Y : Matrix (n × g') (m × g) ℂ)
    (hY : ∀ q,
      (L q ⊗ₖ (1 : Matrix g' g' ℂ)) * Y =
        Y * (R q ⊗ₖ (1 : Matrix g g ℂ)))
    (W : ℕ → Matrix h e ℂ)
    (hNested : ∀ r,
      LinearMap.range (W r).mulVecLin ≤
        LinearMap.range (W (r + 1)).mulVecLin) :
    (∃! F : Matrix g' g ℂ, Y = D ⊗ₖ F)
      ∧ Function.Injective
        (fullRecordRepresentation :
          Matrix (g' × g) (g' × g) ℂ →
            Matrix (g' × g) (g' × g) ℂ)
      ∧ IsCanonicalLoadedHierarchy W := by
  exact ⟨equivariantOperator_unique_kroneckerFactorization
      L R D hSchur Y hY,
    fullRecordRepresentation_injective,
    canonical_loaded_hierarchy W hNested⟩

end FullRecordBimoduleReconstruction
end NCG
