/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.Commutant.SMSTQuiverCommutantAssemblyExact

/-!
# Multiplicity quiver: arrow spaces from Hilbert--Schmidt slices

`def:multiplicity-quiver` of the spacetime--gauge duality manuscript defines,
for a block `T_{ba} : V_a ⊗ N_a → V_b ⊗ N_b` of a reconstructed generator,
the operator space
`𝔅_{ba}(T) = {(φ ⊗ id)(T_{ba}) : φ ∈ B(V_a, V_b)^*} ⊆ B(N_a, N_b)`,
the arrow spaces `𝔅_{ba} = Span_T 𝔅_{ba}(T)`, and the endomorphism algebra
`End 𝔅 = {(X_a) : X_b B = B X_a for every B ∈ 𝔅_{ba}}`.

Here the arrow blocks are derived from the generator blocks rather than
supplied as data: `functionalSlice φ T` is `(φ ⊗ id)(T)`, `blockSlice` is its
value on the matrix-entry functionals (the Hilbert--Schmidt basis slices),
`arrowSpace` is the span of all functional slices, and `QuiverEnd` is the
endomorphism space.  The span of the functional slices equals the span of the
finitely many entry slices (`arrowSpace_eq_span_blockSlice`), so membership in
`QuiverEnd` reduces to the finitely many coefficient equations
(`mem_quiverEnd_iff`) used by `QuiverEndomorphism`, and the two encodings are
equivalent (`quiverEndEquivEndomorphism`).  The isotypic decomposition
`𝓜 ≅ ⊕ V_a ⊗ N_a` of `S_F` is inherited as the indexing data `(V, N)`.
-/

open Matrix

namespace RenewalGeometry
namespace SMSTQuiverCommutantAssembly

section Slices

variable {Va Vb Na Nb : Type*} [Fintype Va] [Fintype Vb] [DecidableEq Va] [DecidableEq Vb]

/-- `(φ ⊗ id)(T)`: the slice of a block `T : V_a ⊗ N_a → V_b ⊗ N_b` along a
linear functional `φ ∈ B(V_a, V_b)^*`. -/
def functionalSlice (φ : Matrix Vb Va ℂ →ₗ[ℂ] ℂ)
    (T : Matrix (Vb × Nb) (Va × Na) ℂ) : Matrix Nb Na ℂ :=
  fun n m => φ (fun vb va => T (vb, n) (va, m))

/-- The Hilbert--Schmidt basis slice `(E_{vb,va}^* ⊗ id)(T)`, i.e. the
`(vb, va)` coefficient block of `T`. -/
def blockSlice (T : Matrix (Vb × Nb) (Va × Na) ℂ) (vb : Vb) (va : Va) :
    Matrix Nb Na ℂ :=
  fun n m => T (vb, n) (va, m)

/-- The entry slice is the functional slice along the entry functional. -/
theorem blockSlice_eq_functionalSlice (T : Matrix (Vb × Nb) (Va × Na) ℂ)
    (vb : Vb) (va : Va) :
    blockSlice T vb va = functionalSlice (Matrix.entryLinearMap ℂ ℂ vb va) T := by
  funext n m
  simp [blockSlice, functionalSlice]

/-- Every functional slice is a linear combination of the entry slices. -/
theorem functionalSlice_eq_sum (φ : Matrix Vb Va ℂ →ₗ[ℂ] ℂ)
    (T : Matrix (Vb × Nb) (Va × Na) ℂ) :
    functionalSlice φ T =
      ∑ vb : Vb, ∑ va : Va, φ (Matrix.single vb va 1) • blockSlice T vb va := by
  funext n m
  simp only [functionalSlice, Matrix.sum_apply, Matrix.smul_apply, blockSlice,
    smul_eq_mul]
  conv_lhs =>
    rw [Matrix.matrix_eq_sum_single (fun vb va => T (vb, n) (va, m))]
  rw [map_sum]
  refine Finset.sum_congr rfl fun vb _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun va _ => ?_
  have : Matrix.single vb va (T (vb, n) (va, m)) =
      T (vb, n) (va, m) • Matrix.single vb va (1 : ℂ) := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [this, map_smul, smul_eq_mul, mul_comm]

end Slices

variable {A J : Type} [Fintype J]
variable (V N : A → Type*) [∀ a, Fintype (V a)] [∀ a, Fintype (N a)]
variable [∀ a, DecidableEq (V a)]
variable (src dst : J → A)
variable (T : ∀ j, Matrix (V (dst j) × N (dst j)) (V (src j) × N (src j)) ℂ)

/-- `𝔅_{ba}(T_j)`: the operator space of all functional slices of the
`j`-th generator block. -/
def sliceSpace (j : J) : Set (Matrix (N (dst j)) (N (src j)) ℂ) :=
  Set.range (fun φ : Matrix (V (dst j)) (V (src j)) ℂ →ₗ[ℂ] ℂ => functionalSlice φ (T j))

/-- The arrow space of the multiplicity quiver on the arrow `j : src j → dst j`,
the span of the functional slices of `T_j` (`def:multiplicity-quiver`). -/
def arrowSpace (j : J) : Submodule ℂ (Matrix (N (dst j)) (N (src j)) ℂ) :=
  Submodule.span ℂ (sliceSpace V N src dst T j)

/-- The arrow space is spanned by the finitely many entry slices. -/
theorem arrowSpace_eq_span_blockSlice (j : J) :
    arrowSpace V N src dst T j =
      Submodule.span ℂ (Set.range
        (fun p : V (dst j) × V (src j) => blockSlice (T j) p.1 p.2)) := by
  apply le_antisymm
  · rw [arrowSpace, Submodule.span_le]
    rintro _ ⟨φ, rfl⟩
    rw [SetLike.mem_coe, functionalSlice_eq_sum]
    refine Submodule.sum_mem _ fun vb _ => Submodule.sum_mem _ fun va _ => ?_
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(vb, va), rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨⟨vb, va⟩, rfl⟩
    refine Submodule.subset_span ⟨Matrix.entryLinearMap ℂ ℂ vb va, ?_⟩
    exact (blockSlice_eq_functionalSlice (T j) vb va).symm

/-- `End 𝔔_F(𝑻)`: families `(X_a)` intertwining every arrow of the
multiplicity quiver (`def:multiplicity-quiver`). -/
def QuiverEnd :=
  {X : ∀ a, Matrix (N a) (N a) ℂ //
    ∀ j, ∀ B ∈ arrowSpace V N src dst T j, X (dst j) * B = B * X (src j)}

/-- Intertwining the whole arrow space is equivalent to the finitely many
coefficient equations on the entry slices. -/
theorem mem_quiverEnd_iff (X : ∀ a, Matrix (N a) (N a) ℂ) :
    (∀ j, ∀ B ∈ arrowSpace V N src dst T j, X (dst j) * B = B * X (src j)) ↔
      ∀ j vb va, X (dst j) * blockSlice (T j) vb va =
        blockSlice (T j) vb va * X (src j) := by
  constructor
  · intro hX j vb va
    apply hX j
    rw [arrowSpace_eq_span_blockSlice]
    exact Submodule.subset_span ⟨(vb, va), rfl⟩
  · intro hX j B hB
    rw [arrowSpace_eq_span_blockSlice] at hB
    induction hB using Submodule.span_induction with
    | mem B hB =>
        obtain ⟨⟨vb, va⟩, rfl⟩ := hB
        exact hX j vb va
    | zero => simp
    | add B C _ _ hB hC => rw [Matrix.mul_add, Matrix.add_mul, hB, hC]
    | smul c B _ hB => rw [Matrix.mul_smul, Matrix.smul_mul, hB]

/-- The derived quiver endomorphism space coincides with the data-supplied
encoding `QuiverEndomorphism` once the arrow blocks are the entry slices. -/
def quiverEndEquivEndomorphism :
    QuiverEnd V N src dst T ≃
      QuiverEndomorphism V N src dst (fun j vb va => blockSlice (T j) vb va) where
  toFun X := ⟨X.1, (mem_quiverEnd_iff V N src dst T X.1).mp X.2⟩
  invFun X := ⟨X.1, (mem_quiverEnd_iff V N src dst T X.1).mpr X.2⟩
  left_inv X := by cases X; rfl
  right_inv X := by cases X; rfl

end SMSTQuiverCommutantAssembly
end RenewalGeometry
