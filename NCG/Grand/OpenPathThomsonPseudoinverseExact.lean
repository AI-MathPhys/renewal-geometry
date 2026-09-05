/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.HermitianMoorePenroseInverse
import NCG.Grand.SourceCoercivityInfluenceExact
import NCG.Grand.OpenPathWassersteinDualityExact

/-!
# Weighted Thomson principle on a finite open path

This file supplies the pseudoinverse-energy half of `thm:GT-open-current`.
The path incidence, positive diagonal conductance inverse, weighted potential,
Laplacian, and its spectral Moore--Penrose inverse are all constructed
explicitly.
-/

open Matrix Finset

namespace NCG
namespace OpenPathThomsonPseudoinverse

/-- Oriented incidence matrix for `0 -> 1 -> ... -> N`. -/
def pathIncidence (N : ℕ) : Matrix (Fin (N + 1)) (Fin N) ℂ :=
  fun v e => if v.1 = e.1 then -1 else if v.1 = e.1 + 1 then 1 else 0

/-- Positive edge-energy matrix. -/
def pathWeightMatrix {N : ℕ} (a : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.diagonal fun e => (a e : ℂ)

/-- Reciprocal edge-weight matrix. -/
noncomputable def pathInvWeightMatrix {N : ℕ} (a : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.diagonal fun e => ((a e : ℂ)⁻¹)

/-- A potential whose edge gradient is the weighted current. -/
noncomputable def pathPotential {N : ℕ} (a : Fin N → ℝ)
    (j : Fin N → ℂ) (v : Fin (N + 1)) : ℂ :=
  ∑ k ∈ Finset.range v.1,
    if hk : k < N then (a ⟨k, hk⟩ : ℂ) * j ⟨k, hk⟩ else 0

theorem pathPotential_gradient {N : ℕ} (a : Fin N → ℝ)
    (j : Fin N → ℂ) (e : Fin N) :
    pathPotential a j ⟨e.1 + 1, by omega⟩ -
        pathPotential a j ⟨e.1, by omega⟩ =
      (a e : ℂ) * j e := by
  simp [pathPotential, Finset.sum_range_succ, e.2]

theorem pathIncidence_adjoint_mulVec {N : ℕ}
    (u : Fin (N + 1) → ℂ) (e : Fin N) :
    ((pathIncidence N)ᴴ *ᵥ u) e =
      u ⟨e.1 + 1, by omega⟩ - u ⟨e.1, by omega⟩ := by
  classical
  let v0 : Fin (N + 1) := ⟨e.1, by omega⟩
  let v1 : Fin (N + 1) := ⟨e.1 + 1, by omega⟩
  let f : Fin (N + 1) → ℂ := fun v =>
    star (pathIncidence N v e) * u v
  have hv10 : v1 ≠ v0 := by
    intro h
    have := congrArg Fin.val h
    dsimp [v0, v1] at this
    omega
  have hv1mem : v1 ∈ Finset.univ.erase v0 := by simp [hv10]
  have hrest : ∑ v ∈ (Finset.univ.erase v0).erase v1, f v = 0 := by
    apply Finset.sum_eq_zero
    intro v hv
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hv
    have hne0 : v.1 ≠ e.1 := by
      intro h
      exact hv.2 (Fin.ext h)
    have hne1 : v.1 ≠ e.1 + 1 := by
      intro h
      exact hv.1 (Fin.ext h)
    simp [f, pathIncidence, hne0, hne1]
  change ∑ v, f v = u v1 - u v0
  calc
    ∑ v, f v = f v0 + ∑ v ∈ Finset.univ.erase v0, f v := by
      rw [Finset.add_sum_erase _ _ (Finset.mem_univ v0)]
    _ = f v0 + (f v1 +
        ∑ v ∈ (Finset.univ.erase v0).erase v1, f v) := by
      rw [Finset.add_sum_erase _ _ hv1mem]
    _ = u v1 - u v0 := by
      rw [hrest]
      simp [f, v0, v1, pathIncidence]
      ring

theorem pathIncidence_adjoint_pathPotential {N : ℕ}
    (a : Fin N → ℝ) (j : Fin N → ℂ) :
    (pathIncidence N)ᴴ *ᵥ pathPotential a j =
      pathWeightMatrix a *ᵥ j := by
  funext e
  rw [pathIncidence_adjoint_mulVec, pathPotential_gradient]
  unfold pathWeightMatrix
  rw [Matrix.mulVec_diagonal]

theorem pathWeightMatrix_isHermitian {N : ℕ} (a : Fin N → ℝ) :
    (pathWeightMatrix a).IsHermitian := by
  unfold pathWeightMatrix
  rw [Matrix.isHermitian_diagonal_iff]
  intro e
  rw [isSelfAdjoint_iff]
  simp

theorem pathInvWeightMatrix_isHermitian {N : ℕ} (a : Fin N → ℝ) :
    (pathInvWeightMatrix a).IsHermitian := by
  unfold pathInvWeightMatrix
  rw [Matrix.isHermitian_diagonal_iff]
  intro e
  rw [isSelfAdjoint_iff]
  simp

theorem pathInvWeight_mul_weight {N : ℕ} (a : Fin N → ℝ)
    (ha : ∀ e, 0 < a e) :
    pathInvWeightMatrix a * pathWeightMatrix a = 1 := by
  rw [pathInvWeightMatrix, pathWeightMatrix, Matrix.diagonal_mul_diagonal]
  ext e f
  by_cases hef : e = f
  · subst f
    simp [(ne_of_gt (ha e))]
  · simp [Matrix.one_apply, hef]

/-- Weighted path Laplacian `L_N = ∂ A^{-1} ∂*`. -/
noncomputable def pathLaplacian {N : ℕ} (a : Fin N → ℝ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
  pathIncidence N * pathInvWeightMatrix a * (pathIncidence N)ᴴ

theorem pathLaplacian_isHermitian {N : ℕ} (a : Fin N → ℝ) :
    (pathLaplacian a).IsHermitian := by
  unfold pathLaplacian
  exact Matrix.isHermitian_mul_mul_conjTranspose
    (pathIncidence N) (pathInvWeightMatrix_isHermitian a)

/-- Spectral Moore--Penrose inverse of the weighted path Laplacian. -/
noncomputable def pathLaplacianPseudoinverse {N : ℕ} (a : Fin N → ℝ) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
  HermitianMoorePenroseInverse.hermitianMoorePenroseInverse
    (pathLaplacian a) (pathLaplacian_isHermitian a)

theorem pathLaplacian_penrose {N : ℕ} (a : Fin N → ℝ) :
    pathLaplacian a * pathLaplacianPseudoinverse a * pathLaplacian a =
      pathLaplacian a :=
  HermitianMoorePenroseInverse.hermitianMoorePenroseInverse_penrose_left
    (pathLaplacian a) (pathLaplacian_isHermitian a)

theorem pathLaplacian_pathPotential {N : ℕ} (a : Fin N → ℝ)
    (ha : ∀ e, 0 < a e) (j : Fin N → ℂ) :
    pathLaplacian a *ᵥ pathPotential a j = pathIncidence N *ᵥ j := by
  simp only [pathLaplacian, ← Matrix.mulVec_mulVec]
  rw [pathIncidence_adjoint_pathPotential,
    Matrix.mulVec_mulVec j (pathInvWeightMatrix a) (pathWeightMatrix a),
    pathInvWeight_mul_weight a ha, Matrix.one_mulVec]

theorem adjoint_pairing {N : ℕ} (B : Matrix (Fin (N + 1)) (Fin N) ℂ)
    (u : Fin (N + 1) → ℂ) (j : Fin N → ℂ) :
    star (Bᴴ *ᵥ u) ⬝ᵥ j = star u ⬝ᵥ (B *ᵥ j) := by
  rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose,
    Matrix.dotProduct_mulVec]

/-- Exact weighted Thomson/pseudoinverse quadratic identity for the unique
open-path current. -/
theorem path_current_energy_eq_pseudoinverse {N : ℕ}
    (a : Fin N → ℝ) (ha : ∀ e, 0 < a e) (j : Fin N → ℂ) :
    star j ⬝ᵥ (pathWeightMatrix a *ᵥ j) =
      let s := pathIncidence N *ᵥ j
      star s ⬝ᵥ (pathLaplacianPseudoinverse a *ᵥ s) := by
  let u := pathPotential a j
  let L := pathLaplacian a
  let G := pathLaplacianPseudoinverse a
  let s := pathIncidence N *ᵥ j
  have hgrad : (pathIncidence N)ᴴ *ᵥ u = pathWeightMatrix a *ᵥ j :=
    pathIncidence_adjoint_pathPotential a j
  have hLu : L *ᵥ u = s := pathLaplacian_pathPotential a ha j
  have hpen : L * G * L = L := pathLaplacian_penrose a
  have hLherm : L.IsHermitian := pathLaplacian_isHermitian a
  dsimp only
  calc
    star j ⬝ᵥ (pathWeightMatrix a *ᵥ j) =
        star (pathWeightMatrix a *ᵥ j) ⬝ᵥ j :=
      SourceCoercivityInfluence.dotProduct_mulVec_hermitian
        (pathWeightMatrix_isHermitian a) j j
    _ = star ((pathIncidence N)ᴴ *ᵥ u) ⬝ᵥ j := by rw [hgrad]
    _ = star u ⬝ᵥ (pathIncidence N *ᵥ j) := adjoint_pairing _ _ _
    _ = star u ⬝ᵥ (L *ᵥ u) := by rw [hLu]
    _ = star u ⬝ᵥ ((L * G * L) *ᵥ u) := by rw [hpen]
    _ = star u ⬝ᵥ (L *ᵥ (G *ᵥ (L *ᵥ u))) := by
      simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    _ = star (L *ᵥ u) ⬝ᵥ (G *ᵥ (L *ᵥ u)) :=
      SourceCoercivityInfluence.dotProduct_mulVec_hermitian
        hLherm u (G *ᵥ (L *ᵥ u))
    _ = star s ⬝ᵥ (G *ᵥ s) := by rw [hLu]

/-! ## Real open-path feasibility and the attained Thomson minimum -/

/-- The boundary equations for a real current on the path with `N` edges.
The definition is used only on the nonempty branch `1 ≤ N`. -/
def IsOpenPathCurrent (N : ℕ) (s j : ℕ → ℝ) : Prop :=
  -j 0 = s 0 ∧
  (∀ k, 1 ≤ k → k < N → j (k - 1) - j k = s k) ∧
  j (N - 1) = s N

/-- The current obtained by successively solving from the left endpoint. -/
def cumulativeCurrent (s : ℕ → ℝ) (k : ℕ) : ℝ :=
  -OpenPathWassersteinDuality.prefixMass s k

/-- Weighted current energy. -/
def realPathEnergy (N : ℕ) (a j : ℕ → ℝ) : ℝ :=
  ∑ k ∈ Finset.range N, a k * (j k) ^ 2

/-- The explicit cumulative-mass value of the Thomson energy. -/
def cumulativePathEnergy (N : ℕ) (a s : ℕ → ℝ) : ℝ :=
  ∑ k ∈ Finset.range N,
    a k * (OpenPathWassersteinDuality.prefixMass s k) ^ 2

/-- Exact solvability criterion, with the manuscript's displayed current. -/
theorem cumulativeCurrent_isOpenPathCurrent_iff {N : ℕ} (hN : 1 ≤ N)
    (s : ℕ → ℝ) :
    IsOpenPathCurrent N s (cumulativeCurrent s) ↔
      ∑ k ∈ Finset.range (N + 1), s k = 0 := by
  rcases NCG.gt_open_current N hN s with ⟨hleft, hinterior, _, hterminal⟩
  constructor
  · intro h
    apply hterminal.mp
    simpa [IsOpenPathCurrent, cumulativeCurrent,
      OpenPathWassersteinDuality.prefixMass] using h.2.2
  · intro hmass
    refine ⟨?_, ?_, ?_⟩
    · simpa [cumulativeCurrent,
        OpenPathWassersteinDuality.prefixMass] using hleft
    · intro k hk hkN
      simpa [cumulativeCurrent,
        OpenPathWassersteinDuality.prefixMass] using hinterior k hk
    · simpa [cumulativeCurrent,
        OpenPathWassersteinDuality.prefixMass] using hterminal.mpr hmass

/-- Boundary feasibility determines every edge current uniquely. -/
theorem openPathCurrent_unique_on_edges {N : ℕ} (s j : ℕ → ℝ)
    (hj : IsOpenPathCurrent N s j) :
    ∀ k < N, j k = cumulativeCurrent s k := by
  intro k hk
  induction k with
  | zero =>
      simp [cumulativeCurrent, OpenPathWassersteinDuality.prefixMass, ← hj.1]
  | succ k ih =>
      have hkN : k < N := Nat.lt_of_succ_lt hk
      have hrec := hj.2.1 (k + 1) (Nat.le_add_left 1 k) hk
      rw [Nat.add_sub_cancel] at hrec
      rw [cumulativeCurrent,
        OpenPathWassersteinDuality.prefixMass_succ]
      have hcurrent := ih hkN
      unfold cumulativeCurrent at hcurrent
      linarith

theorem realPathEnergy_cumulativeCurrent (N : ℕ) (a s : ℕ → ℝ) :
    realPathEnergy N a (cumulativeCurrent s) =
      cumulativePathEnergy N a s := by
  apply Finset.sum_congr rfl
  intro k hk
  simp [realPathEnergy, cumulativePathEnergy, cumulativeCurrent]

/-- The finite Thomson infimum in strong attained-minimum form.  Because an
open path has no cycle space, every feasible competitor is the displayed
cumulative current. -/
theorem openPathThomson_isLeast {N : ℕ} (hN : 1 ≤ N)
    (s a : ℕ → ℝ) (ha : ∀ k < N, 0 < a k)
    (hmass : ∑ k ∈ Finset.range (N + 1), s k = 0) :
    IsLeast
      {x : ℝ | ∃ j : ℕ → ℝ,
        IsOpenPathCurrent N s j ∧ x = realPathEnergy N a j}
      (cumulativePathEnergy N a s) := by
  have hc : IsOpenPathCurrent N s (cumulativeCurrent s) :=
    (cumulativeCurrent_isOpenPathCurrent_iff hN s).mpr hmass
  refine ⟨?_, ?_⟩
  · exact ⟨cumulativeCurrent s, hc,
      (realPathEnergy_cumulativeCurrent N a s).symm⟩
  · rintro x ⟨j, hj, rfl⟩
    have heq : realPathEnergy N a j = cumulativePathEnergy N a s := by
      rw [← realPathEnergy_cumulativeCurrent]
      apply Finset.sum_congr rfl
      intro k hk
      rw [openPathCurrent_unique_on_edges s j hj k (Finset.mem_range.mp hk)]
    rw [heq]

/-- All three boxes of `thm:GT-open-current`: exact solvability and unique
cumulative current, the attained weighted Thomson minimum, the spectral
Moore--Penrose quadratic identity, and attained `W₁` duality. -/
theorem exact_open_path_compiler {N : ℕ} (hN : 1 ≤ N)
    (s a : ℕ → ℝ) (ha : ∀ k < N, 0 < a k)
    (hmass : ∑ k ∈ Finset.range (N + 1), s k = 0) :
    IsOpenPathCurrent N s (cumulativeCurrent s) ∧
    IsLeast
      {x : ℝ | ∃ j : ℕ → ℝ,
        IsOpenPathCurrent N s j ∧ x = realPathEnergy N a j}
      (cumulativePathEnergy N a s) ∧
    IsGreatest
      {x : ℝ | ∃ φ : ℕ → ℝ,
        OpenPathWassersteinDuality.IsUnitLipschitz N φ ∧
        x = OpenPathWassersteinDuality.sourcePairing N s φ}
      (OpenPathWassersteinDuality.pathTransportCost N s) := by
  exact ⟨(cumulativeCurrent_isOpenPathCurrent_iff hN s).mpr hmass,
    openPathThomson_isLeast hN s a ha hmass,
    OpenPathWassersteinDuality.open_path_wasserstein_isGreatest hmass⟩

end OpenPathThomsonPseudoinverse
end NCG
