/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.EscapeHeadConcentrationExact
import NCG.Upstream.PrimitiveWeight

/-!
# Positive square contractions

If a positive matrix `P` has contractive square, then `P` itself is a
contraction.  We also record positivity of `P - P²`.  The proof isolates the
scalar spectral fact `0 ≤ λ` and `λ² ≤ 1` imply `λ ≤ 1`, and packages the
result through the finite Hermitian functional calculus.
-/

open Matrix
open scoped ComplexOrder

noncomputable section

namespace NCG
namespace PositiveSquareContraction

variable {d : ℕ}

/-- Every eigenvalue of a positive matrix with contractive square is at most
one. -/
theorem eigenvalue_le_one
    (P : Matrix (Fin d) (Fin d) ℂ) (hP : P.PosSemidef)
    (hIP2 : (1 - P * P).PosSemidef) (i : Fin d) :
    hP.1.eigenvalues i ≤ 1 := by
  let u : Fin d → ℂ := (hP.1.eigenvectorBasis i).ofLp
  have hun : star u ⬝ᵥ u = 1 := by
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct]
    rw [inner_self_eq_norm_sq_to_K,
      hP.1.eigenvectorBasis.orthonormal.1 i]
    norm_num
  have hq := hIP2.dotProduct_mulVec_nonneg u
  have hqre := (Complex.nonneg_iff.mp hq).1
  dsimp only [u] at hun hqre
  rw [Matrix.sub_mulVec, Matrix.one_mulVec,
    ← Matrix.mulVec_mulVec, hP.1.mulVec_eigenvectorBasis,
    Matrix.mulVec_smul, hP.1.mulVec_eigenvectorBasis,
    dotProduct_sub, dotProduct_smul, dotProduct_smul, hun] at hqre
  norm_num [Complex.real_smul, smul_smul] at hqre
  have hnon := hP.eigenvalues_nonneg i
  nlinarith

/-- A positive matrix whose square is at most the identity is itself at most
the identity; moreover `P - P²` is positive. -/
theorem positive_and_defect
    (P : Matrix (Fin d) (Fin d) ℂ) (hP : P.PosSemidef)
    (hIP2 : (1 - P * P).PosSemidef) :
    (1 - P).PosSemidef ∧ (P - P * P).PosSemidef := by
  let hH : P.IsHermitian := hP.1
  have hupper : ∀ i, hH.eigenvalues i ≤ 1 := by
    intro i
    exact eigenvalue_le_one P hP hIP2 i
  have hone : hH.cfc (fun _ => 1) =
      (1 : Matrix (Fin d) (Fin d) ℂ) := by
    rw [Upstream.PrimitiveWeight.cfc_const hH]
    simp
  have hPid : hH.cfc id = P :=
    Upstream.PrimitiveWeight.cfc_id' hH
  have hP2 : P * P = hH.cfc (fun x => x * x) := by
    calc
      P * P = hH.cfc id * hH.cfc id :=
        congrArg₂ (· * ·) hPid.symm hPid.symm
      _ = hH.cfc (fun x => id x * id x) :=
        Upstream.PrimitiveWeight.cfc_mul hH id id
      _ = hH.cfc (fun x => x * x) := by rfl
  have hOneSub : 1 - P = hH.cfc (fun x => 1 - x) := by
    calc
      1 - P = hH.cfc (fun _ => 1) - hH.cfc id :=
        congrArg₂ (· - ·) hone.symm hPid.symm
      _ = hH.cfc (fun x => (fun _ => 1) x - id x) :=
        Upstream.PrimitiveWeight.cfc_sub hH _ _
      _ = hH.cfc (fun x => 1 - x) := by rfl
  have hDiff : P - P * P = hH.cfc (fun x => x - x * x) := by
    calc
      P - P * P = hH.cfc id - hH.cfc (fun x => x * x) :=
        congrArg₂ (· - ·) hPid.symm hP2
      _ = hH.cfc (fun x => id x - (fun y => y * y) x) :=
        Upstream.PrimitiveWeight.cfc_sub hH _ _
      _ = hH.cfc (fun x => x - x * x) := by rfl
  constructor
  · rw [hOneSub]
    exact Upstream.PrimitiveWeight.cfc_posSemidef hH
      (fun i => sub_nonneg.mpr (hupper i))
  · rw [hDiff]
    exact Upstream.PrimitiveWeight.cfc_posSemidef hH fun i => by
      have hnon := hP.eigenvalues_nonneg i
      have hup := hupper i
      nlinarith

end PositiveSquareContraction
end NCG
