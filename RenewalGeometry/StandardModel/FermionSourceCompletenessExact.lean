/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Finite certificate for completeness of the retained fermion source
  (`prop:fermion-source-completeness`, spacetime–gauge duality manuscript)

Let `U_F : ℂ^M → H_F^amb` synthesize the physical fermion-source atlas and let `𝒦` be a
candidate carrier with orthogonal projector `P_𝒦` (a Hermitian idempotent).  The
completeness residual is

`ℂ_{F|𝒦} := U_F* (I − P_𝒦) U_F ⪰ 0`   (`eq:fermion-source-completeness`).

* `completenessResidual_eq_gram`, `completenessResidual_posSemidef`: `ℂ_{F|𝒦} = V* V`
  with `V = (I − P_𝒦) U_F`, hence positive semidefinite;
* `completenessResidual_eq_zero_iff`, `sourceRange_le_carrier_iff`: `ℂ_{F|𝒦} = 0` iff
  `Ran U_F ⊆ 𝒦`;
* `sourceRange_le_carrier_iff_invariant`: `Ran U_F ⊆ 𝒦` iff `𝒜_F Ran U_F ⊆ 𝒦`, for any
  set `𝒜_F` of operators containing `I` and leaving `𝒦` invariant
  (`eq:fermion-source-completeness-zero`);
* `completenessResidual_trace`: `Tr ℂ_{F|𝒦} = ‖(I − P_𝒦) U_F‖²_HS`;
* `completenessResidual_rank_add`: `rank ℂ_{F|𝒦} + dim(Ran U_F ∩ 𝒦) = dim Ran U_F`
  (`eq:fermion-source-completeness-rank`);
* `fermion_source_completeness`: the assembled statement.

Rendering disclosed: the ambient space is `N → ℂ` and `𝒦 = Ran P_𝒦` for a Hermitian
idempotent `P_𝒦`; the reducing algebra `𝒜_F` enters only through `I ∈ 𝒜_F` and
invariance of `𝒦` (its reducing property).  "Independently complete" is not used by
the certificate.  The closing remark (the rank need not equal the dimension of the
cyclic closure) is a remark, not a claim.
-/

open Matrix
open scoped ComplexOrder

namespace RenewalGeometry
namespace FermionSourceCompleteness

variable {N M : Type*} [Fintype N] [Fintype M] [DecidableEq N] [DecidableEq M]

/-- The candidate carrier `𝒦 = Ran P_𝒦`. -/
def carrier (P : Matrix N N ℂ) : Submodule ℂ (N → ℂ) :=
  LinearMap.range P.mulVecLin

/-- The range `Ran U_F` of a source synthesis. -/
def sourceRange (U : Matrix N M ℂ) : Submodule ℂ (N → ℂ) :=
  LinearMap.range U.mulVecLin

/-- The completeness residual `ℂ_{F|𝒦} = U_F* (I − P_𝒦) U_F`
(`eq:fermion-source-completeness`). -/
noncomputable def completenessResidual (P : Matrix N N ℂ) (U : Matrix N M ℂ) :
    Matrix M M ℂ :=
  Uᴴ * (1 - P) * U

/-- The squared Hilbert–Schmidt norm `‖A‖²_HS = ∑ |A i j|²`. -/
noncomputable def hsNormSq {m n : Type*} [Fintype m] [Fintype n] (A : Matrix m n ℂ) : ℝ :=
  ∑ i, ∑ j, Complex.normSq (A i j)

omit [DecidableEq N] [DecidableEq M] in
theorem mem_carrier_iff {P : Matrix N N ℂ} (hP : P * P = P) (v : N → ℂ) :
    v ∈ carrier P ↔ P *ᵥ v = v := by
  constructor
  · rintro ⟨w, rfl⟩
    simp only [Matrix.mulVecLin_apply, mulVec_mulVec, hP]
  · intro h
    exact ⟨v, h⟩

omit [DecidableEq M] in
/-- The kernel of `I − P_𝒦` is the carrier. -/
theorem ker_complement {P : Matrix N N ℂ} (hP : P * P = P) :
    LinearMap.ker (1 - P).mulVecLin = carrier P := by
  ext v
  rw [LinearMap.mem_ker, mem_carrier_iff hP, Matrix.mulVecLin_apply, sub_mulVec, one_mulVec,
    sub_eq_zero, eq_comm]

omit [Fintype M] [DecidableEq M] in
/-- `ℂ_{F|𝒦} = V* V` with `V = (I − P_𝒦) U_F`. -/
theorem completenessResidual_eq_gram {P : Matrix N N ℂ} (hP : P * P = P) (hPH : Pᴴ = P)
    (U : Matrix N M ℂ) :
    completenessResidual P U = ((1 - P) * U)ᴴ * ((1 - P) * U) := by
  have hQH : (1 - P)ᴴ = 1 - P := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPH]
  have hQ2 : (1 - P) * (1 - P) = 1 - P := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hP]
    abel
  rw [completenessResidual, Matrix.conjTranspose_mul, hQH]
  calc Uᴴ * (1 - P) * U = Uᴴ * ((1 - P) * (1 - P)) * U := by rw [hQ2]
    _ = Uᴴ * (1 - P) * ((1 - P) * U) := by simp only [Matrix.mul_assoc]

omit [DecidableEq M] in
/-- `ℂ_{F|𝒦} ⪰ 0`. -/
theorem completenessResidual_posSemidef {P : Matrix N N ℂ} (hP : P * P = P) (hPH : Pᴴ = P)
    (U : Matrix N M ℂ) : (completenessResidual P U).PosSemidef := by
  rw [completenessResidual_eq_gram hP hPH]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- `Ran U_F ⊆ 𝒦` iff `(I − P_𝒦) U_F = 0`. -/
theorem sourceRange_le_carrier_iff {P : Matrix N N ℂ} (hP : P * P = P) (U : Matrix N M ℂ) :
    sourceRange U ≤ carrier P ↔ (1 - P) * U = 0 := by
  rw [sourceRange, ← ker_complement hP, LinearMap.range_le_ker_iff, ← Matrix.mulVecLin_mul,
    ← Matrix.toLin'_apply', LinearEquiv.map_eq_zero_iff]

/-- **Zero test** (`eq:fermion-source-completeness-zero`, first equivalence):
`ℂ_{F|𝒦} = 0` iff `Ran U_F ⊆ 𝒦`. -/
theorem completenessResidual_eq_zero_iff {P : Matrix N N ℂ} (hP : P * P = P) (hPH : Pᴴ = P)
    (U : Matrix N M ℂ) :
    completenessResidual P U = 0 ↔ sourceRange U ≤ carrier P := by
  rw [completenessResidual_eq_gram hP hPH, Matrix.conjTranspose_mul_self_eq_zero,
    sourceRange_le_carrier_iff hP]

omit [DecidableEq M] in
/-- **Invariance clause** (`eq:fermion-source-completeness-zero`, second equivalence):
for any set `𝒜_F` of operators containing `I` and leaving `𝒦` invariant,
`Ran U_F ⊆ 𝒦` iff `𝒜_F Ran U_F ⊆ 𝒦`. -/
theorem sourceRange_le_carrier_iff_invariant (P : Matrix N N ℂ) (U : Matrix N M ℂ)
    (𝒜 : Set (Matrix N N ℂ)) (h1 : (1 : Matrix N N ℂ) ∈ 𝒜)
    (hinv : ∀ A ∈ 𝒜, Submodule.map A.mulVecLin (carrier P) ≤ carrier P) :
    sourceRange U ≤ carrier P ↔
      ∀ A ∈ 𝒜, Submodule.map A.mulVecLin (sourceRange U) ≤ carrier P := by
  constructor
  · intro h A hA
    exact (Submodule.map_mono h).trans (hinv A hA)
  · intro h
    have := h 1 h1
    rwa [Matrix.mulVecLin_one, Submodule.map_id] at this

omit [DecidableEq M] in
/-- **Trace identity** (`eq:fermion-source-completeness-rank`, first line):
`Tr ℂ_{F|𝒦} = ‖(I − P_𝒦) U_F‖²_HS`. -/
theorem completenessResidual_trace {P : Matrix N N ℂ} (hP : P * P = P) (hPH : Pᴴ = P)
    (U : Matrix N M ℂ) :
    (completenessResidual P U).trace = (hsNormSq ((1 - P) * U) : ℂ) := by
  rw [completenessResidual_eq_gram hP hPH]
  set V := (1 - P) * U
  have hentry : ∀ j, (Vᴴ * V) j j = ∑ i, ((Complex.normSq (V i j) : ℝ) : ℂ) := by
    intro j
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.conjTranspose_apply, Complex.normSq_eq_conj_mul_self, Complex.star_def]
  simp only [Matrix.trace, Matrix.diag, hentry, hsNormSq]
  push_cast
  rw [Finset.sum_comm]

omit [DecidableEq M] in
/-- **Rank identity** (`eq:fermion-source-completeness-rank`, second line):
`rank ℂ_{F|𝒦} + dim(Ran U_F ∩ 𝒦) = dim Ran U_F`, by rank–nullity for
`(I − P_𝒦)|_{Ran U_F}` and `rank(V* V) = rank V`. -/
theorem completenessResidual_rank_add {P : Matrix N N ℂ} (hP : P * P = P) (hPH : Pᴴ = P)
    (U : Matrix N M ℂ) :
    (completenessResidual P U).rank + Module.finrank ℂ ↥(sourceRange U ⊓ carrier P)
      = U.rank := by
  rw [completenessResidual_eq_gram hP hPH, Matrix.rank_conjTranspose_mul_self]
  have hrange : ((1 - P) * U).rank = Module.finrank ℂ
      ↥(LinearMap.range ((1 - P).mulVecLin.domRestrict (sourceRange U))) := by
    rw [Matrix.rank, Matrix.mulVecLin_mul, LinearMap.range_comp, LinearMap.range_domRestrict]
    rfl
  have hker : Module.finrank ℂ ↥(LinearMap.ker ((1 - P).mulVecLin.domRestrict (sourceRange U)))
      = Module.finrank ℂ ↥(sourceRange U ⊓ carrier P) := by
    rw [LinearMap.ker_domRestrict, ← ker_complement hP]
    have hcomap : Submodule.comap (sourceRange U).subtype (LinearMap.ker (1 - P).mulVecLin)
        = Submodule.comap (sourceRange U).subtype
            (LinearMap.ker (1 - P).mulVecLin ⊓ sourceRange U) := by
      rw [Submodule.comap_inf, Submodule.comap_subtype_self, inf_top_eq]
    rw [hcomap, (Submodule.comapSubtypeEquivOfLe (inf_le_right :
      LinearMap.ker (1 - P).mulVecLin ⊓ sourceRange U ≤ sourceRange U)).finrank_eq, inf_comm]
  have hrn := LinearMap.finrank_range_add_finrank_ker ((1 - P).mulVecLin.domRestrict (sourceRange U))
  rw [hrange, ← hker, hrn]
  rfl

/-- **`prop:fermion-source-completeness`**: the completeness residual is positive
semidefinite, vanishes exactly when `Ran U_F ⊆ 𝒦` (equivalently `𝒜_F Ran U_F ⊆ 𝒦`),
its trace is the source leakage `‖(I − P_𝒦) U_F‖²_HS`, and its rank counts the
independent source directions modulo `𝒦`. -/
theorem fermion_source_completeness {P : Matrix N N ℂ} (hP : P * P = P) (hPH : Pᴴ = P)
    (U : Matrix N M ℂ) (𝒜 : Set (Matrix N N ℂ)) (h1 : (1 : Matrix N N ℂ) ∈ 𝒜)
    (hinv : ∀ A ∈ 𝒜, Submodule.map A.mulVecLin (carrier P) ≤ carrier P) :
    (completenessResidual P U).PosSemidef
    ∧ (completenessResidual P U = 0 ↔ sourceRange U ≤ carrier P)
    ∧ (sourceRange U ≤ carrier P ↔
        ∀ A ∈ 𝒜, Submodule.map A.mulVecLin (sourceRange U) ≤ carrier P)
    ∧ (completenessResidual P U).trace = (hsNormSq ((1 - P) * U) : ℂ)
    ∧ (completenessResidual P U).rank + Module.finrank ℂ ↥(sourceRange U ⊓ carrier P)
        = U.rank :=
  ⟨completenessResidual_posSemidef hP hPH U, completenessResidual_eq_zero_iff hP hPH U,
    sourceRange_le_carrier_iff_invariant P U 𝒜 h1 hinv, completenessResidual_trace hP hPH U,
    completenessResidual_rank_add hP hPH U⟩

end FermionSourceCompleteness
end RenewalGeometry

