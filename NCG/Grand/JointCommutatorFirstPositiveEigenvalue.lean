/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteNormalResolventFirstPositiveEigenvalue
import NCG.Grand.JointCommutatorResolvent
import NCG.Grand.OperatorGraphResolventPositivity

/-!
# First positive eigenvalue of a finite joint-commutator Laplacian

The canonical projection onto the finite commutant kernel commutes with the commutant Laplacian
and its shifted resolvent.  Consequently the coordinate-free inverse-norm compiler identifies the
cutoff Howe gap with the attained least positive eigenvalue of the literal normal operator.
-/

open scoped InnerProduct

noncomputable section

namespace NCG

universe u

/-- Orthogonal projection onto the finite joint-commutator kernel. -/
noncomputable def jointCommutatorKernelProjection
    {n : Type u} [Fintype n] {s : ℕ} (c : Fin s → Matrix n n ℂ) :
    EuclideanSpace ℂ (n × n) →L[ℂ] EuclideanSpace ℂ (n × n) :=
  (LinearMap.ker (jointCommutatorCLM c).toLinearMap).starProjection

theorem jointCommutatorKernelProjection_isStarProjection
    {n : Type u} [Fintype n] {s : ℕ} (c : Fin s → Matrix n n ℂ) :
    IsStarProjection (jointCommutatorKernelProjection c) := by
  simp [jointCommutatorKernelProjection]

theorem range_jointCommutatorKernelProjection
    {n : Type u} [Fintype n] {s : ℕ} (c : Fin s → Matrix n n ℂ) :
    LinearMap.range (jointCommutatorKernelProjection c).toLinearMap =
      LinearMap.ker (jointCommutatorCLM c).toLinearMap := by
  simp [jointCommutatorKernelProjection]

theorem commutantLaplacianCLM_isPositive
    {n : Type u} [Fintype n] {s : ℕ} (c : Fin s → Matrix n n ℂ) :
    (commutantLaplacianCLM c).IsPositive := by
  simpa [commutantLaplacianCLM] using
    (jointCommutatorCLM c).isPositive_adjoint_comp_self

theorem ker_commutantLaplacianCLM
    {n : Type u} [Fintype n] {s : ℕ} (c : Fin s → Matrix n n ℂ) :
    LinearMap.ker (commutantLaplacianCLM c).toLinearMap =
      LinearMap.ker (jointCommutatorCLM c).toLinearMap := by
  simpa [commutantLaplacianCLM] using
    (jointCommutatorCLM c).ker_adjoint_comp_self

theorem commutantLaplacianCLM_commute_kernelProjection
    {n : Type u} [Fintype n] {s : ℕ} (c : Fin s → Matrix n n ℂ) :
    Commute (commutantLaplacianCLM c) (jointCommutatorKernelProjection c) := by
  let A := commutantLaplacianCLM c
  let K := LinearMap.ker (jointCommutatorCLM c).toLinearMap
  let P := jointCommutatorKernelProjection c
  change commutantLaplacianCLM c * jointCommutatorKernelProjection c =
    jointCommutatorKernelProjection c * commutantLaplacianCLM c
  apply ContinuousLinearMap.ext
  intro x
  have hPxKer : P x ∈ LinearMap.ker A.toLinearMap := by
    rw [ker_commutantLaplacianCLM c]
    exact (range_jointCommutatorKernelProjection c).symm ▸ ⟨x, rfl⟩
  have hAP : A (P x) = 0 := LinearMap.mem_ker.mp hPxKer
  have hAxOrth : A x ∈ Kᗮ := by
    intro z hz
    have hAz : A z = 0 := by
      apply LinearMap.mem_ker.mp
      rw [ker_commutantLaplacianCLM c]
      exact hz
    have hs := (commutantLaplacianCLM_isPositive c).isSymmetric x z
    change inner ℂ (A x) z = inner ℂ x (A z) at hs
    rw [hAz, inner_zero_right] at hs
    exact inner_eq_zero_symm.mpr hs
  have hPA : P (A x) = 0 := by
    exact (Submodule.starProjection_apply_eq_zero_iff (K := K)).2 hAxOrth
  change A (P x) = P (A x)
  rw [hAP, hPA]

theorem jointCommutatorResolvent_commute_kernelProjection
    {n : Type u} [Fintype n] {s : ℕ} (c : Fin s → Matrix n n ℂ)
    (b : ℝ) (hb : 0 < b) :
    Commute (jointCommutatorResolvent c b hb) (jointCommutatorKernelProjection c) := by
  let S := shiftedCommutantLaplacianCLM c b
  let T := jointCommutatorResolvent c b hb
  let P := jointCommutatorKernelProjection c
  have hSP : Commute S P := by
    change shiftedCommutantLaplacianCLM c b * jointCommutatorKernelProjection c =
      jointCommutatorKernelProjection c * shiftedCommutantLaplacianCLM c b
    apply ContinuousLinearMap.ext
    intro x
    have hAP := congrArg (fun Q : _ →L[ℂ] _ ↦ Q x)
      (commutantLaplacianCLM_commute_kernelProjection c).eq
    change commutantLaplacianCLM c (P x) = P (commutantLaplacianCLM c x) at hAP
    change commutantLaplacianCLM c (P x) + (b : ℂ) • P x =
      P (commutantLaplacianCLM c x + (b : ℂ) • x)
    rw [map_add, map_smul, hAP]
  have hST : S * T = 1 := by
    apply ContinuousLinearMap.ext
    intro x
    change shiftedCommutantLaplacianCLM c b (jointCommutatorResolvent c b hb x) = x
    exact jointCommutatorResolvent_laplacianEquation c b hb x
  have hTS : T * S = 1 := by
    apply ContinuousLinearMap.ext
    intro x
    change jointCommutatorResolvent c b hb (shiftedCommutantLaplacianCLM c b x) = x
    change (shiftedCommutantLaplacianEquiv c b hb).symm
      (shiftedCommutantLaplacianEquiv c b hb x) = x
    exact (shiftedCommutantLaplacianEquiv c b hb).symm_apply_apply x
  change T * P = P * T
  calc
    T * P = T * P * (S * T) := by rw [hST, mul_one]
    _ = T * (P * S) * T := by noncomm_ring
    _ = T * (S * P) * T := by rw [hSP.eq.symm]
    _ = (T * S) * P * T := by noncomm_ring
    _ = P * T := by rw [hTS, one_mul]

theorem jointCommutatorResolvent_eigenvector
    {n : Type u} [Fintype n] {s : ℕ} (c : Fin s → Matrix n n ℂ)
    (b : ℝ) (hb : 0 < b) (ν : ℝ) (hν : 0 ≤ ν)
    (x : EuclideanSpace ℂ (n × n))
    (hx : commutantLaplacianCLM c x = (ν : ℂ) • x) :
    jointCommutatorResolvent c b hb x = (((b + ν : ℝ) : ℂ)⁻¹) • x := by
  change (shiftedCommutantLaplacianEquiv c b hb).symm x =
    (((b + ν : ℝ) : ℂ)⁻¹) • x
  apply (shiftedCommutantLaplacianEquiv c b hb).injective
  rw [(shiftedCommutantLaplacianEquiv c b hb).apply_symm_apply]
  change x = shiftedCommutantLaplacianCLM c b ((((b + ν : ℝ) : ℂ)⁻¹) • x)
  symm
  rw [shiftedCommutantLaplacianCLM_apply,
    map_smul, hx]
  have hbν : (b + ν : ℝ) ≠ 0 := (add_pos_of_pos_of_nonneg hb hν).ne'
  have hbνc : (b : ℂ) + (ν : ℂ) ≠ 0 := by exact_mod_cast hbν
  simp only [smul_smul]
  have hscalar : ((b + ν : ℝ) : ℂ)⁻¹ * (ν : ℂ) +
      (b : ℂ) * ((b + ν : ℝ) : ℂ)⁻¹ = 1 := by
    calc
      _ = ((b + ν : ℝ) : ℂ)⁻¹ * ((b : ℂ) + (ν : ℂ)) := by ring
      _ = 1 := by
        rw [show (b : ℂ) + (ν : ℂ) = ((b + ν : ℝ) : ℂ) by norm_num]
        exact inv_mul_cancel₀ (by exact_mod_cast hbν)
  rw [← add_smul, hscalar, one_smul]

/-- The finite joint-commutator inverse-norm gap is exactly its attained least positive normal
eigenvalue. -/
theorem jointCommutator_inverseNormGap_is_leastPositiveEigenvalue
    {n : Type u} [Fintype n] {s : ℕ} (c : Fin s → Matrix n n ℂ)
    (b : ℝ) (hb : 0 < b)
    (hne : NCG.SpectralGap.complementCompression
      (jointCommutatorResolvent c b hb) (jointCommutatorKernelProjection c) ≠ 0) :
    let μ := ‖NCG.SpectralGap.complementCompression
      (jointCommutatorResolvent c b hb) (jointCommutatorKernelProjection c)‖⁻¹ - b
    0 < μ ∧ Module.End.HasEigenvalue (commutantLaplacianCLM c).toLinearMap (μ : ℂ) ∧
      ∀ ν : ℝ, 0 < ν →
        Module.End.HasEigenvalue (commutantLaplacianCLM c).toLinearMap (ν : ℂ) → μ ≤ ν := by
  apply NCG.SpectralGap.inverseNormGap_is_leastPositiveEigenvalue_of_normalResolvent
    (commutantLaplacianCLM c) (jointCommutatorResolvent c b hb)
      (jointCommutatorKernelProjection c) b hb
  · exact commutantLaplacianCLM_isPositive c
  · exact NCG.VaryingHilbert.operatorGraphResolvent_isPositive
      (⊤ : Submodule ℂ (EuclideanSpace ℂ (n × n)))
      (NCG.VaryingHilbert.boundedOperatorGraphMap (jointCommutatorCLM c)) b hb.le
      (jointCommutatorResolvent c b hb)
      (jointCommutatorResolvent_resolventEquation c b hb)
  · exact jointCommutatorKernelProjection_isStarProjection c
  · rw [range_jointCommutatorKernelProjection, ker_commutantLaplacianCLM]
  · exact jointCommutatorResolvent_commute_kernelProjection c b hb
  · exact jointCommutatorResolvent_laplacianEquation c b hb
  · exact jointCommutatorResolvent_eigenvector c b hb
  · exact hne

end NCG
