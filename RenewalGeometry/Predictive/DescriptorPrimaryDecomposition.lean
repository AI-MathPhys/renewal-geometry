/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.Predictive.DescriptorAnchoredPencil
import RenewalGeometry.Algebra.RootSubspaceProjection
import RenewalGeometry.Krein.JSelfAdjointRootSpaces

/-!
# The primary decomposition of an anchored descriptor pencil

Paper `predictive_spectral_geometry`, `cor:supp-all-rational` (partial: the primary decomposition
at infinity / at the finite spectral points of the anchored pencil of a regular descriptor
realization, "on the generalized zero eigenspace of an anchored descriptor pencil the resolvent
expansion is polynomial").

For a finite Pontryagin realization `P = (A, Γ, J)` (in the application, the anchored realization
`D.anchored t₀` of a descriptor realization, `A = T = E (A_D - t₀ E)⁻¹`):

* `PontryaginRealization.form_eq_zero_of_mem_rootSpace_zero_of_mem_rootComplement`: the root
  subspace `R₀ = ker A^∞` and the sum `W` of the other root subspaces are `J`-orthogonal, and
  the form splits, `[x, y] = [π₀ x, π₀ y] + [(1 - π₀) x, (1 - π₀) y]` (`form_eq_rootProj_add`)
  along the Riesz projection `π₀` (`rootProjL`), which commutes with `A` and with every
  resolvent `(1 - c A)⁻¹` (`rootProjL_comm_inverse`).
* `PontryaginRealization.inverse_one_sub_smul_rootProjL`: on the root subspace at `0` the
  resolvent `(1 - c A)⁻¹` is the polynomial `∑_{k < dim N} c^k A^k` (nilpotent infinity block).
* `DescriptorRealization.inner_transfer_eq_rootProj_add`: the transfer function of a regular
  descriptor realization at a real regular point `t₀` splits into the contribution of the
  infinity block (root subspace at `0` of the anchored operator `T`, where the resolvent is
  polynomial in `z`) and of the finite block (root complement, where `T` is injective):
  `⟪h', Q(z) h⟫ = [π₀ Γ h', (1 - (z - t₀) T)⁻¹ π₀ Γ h] + [(1 - π₀) Γ h', (1 - (z - t₀) T)⁻¹ (1 - π₀) Γ h]`.
-/

open scoped InnerProductSpace InnerProduct
open Module

noncomputable section

namespace RenewalGeometry

namespace PontryaginRealization

variable {H N : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup N] [InnerProductSpace ℂ N] [CompleteSpace N]
variable (P : PontryaginRealization H N)

/-- `((A - ν)^q) y` computed as a module endomorphism. -/
theorem sub_algebraMap_pow_apply_eq (ν : ℂ) (q : ℕ) (y : N) :
    ((P.A - algebraMap ℂ (N →L[ℂ] N) ν) ^ q) y = (((P.A : N →ₗ[ℂ] N) - ν • 1) ^ q) y := by
  have : ((P.A - algebraMap ℂ (N →L[ℂ] N) ν : N →L[ℂ] N) : N →ₗ[ℂ] N) =
      (P.A : N →ₗ[ℂ] N) - ν • 1 := by
    rw [Algebra.algebraMap_eq_smul_one]
    ext x
    simp
  rw [← this, ← ContinuousLinearMap.toLinearMap_pow]
  rfl

/-- **The root subspace at `0` and the root complement are `J`-orthogonal**
(`cor:supp-all-rational`, "the primary decomposition is Pontryagin orthogonal"). -/
theorem form_eq_zero_of_mem_rootSpace_zero_of_mem_rootComplement {x y : N}
    (hx : x ∈ Module.End.maxGenEigenspace (P.A : Module.End ℂ N) 0)
    (hy : y ∈ RootProjection.rootComplement (P.A : Module.End ℂ N) 0) : P.form x y = 0 := by
  obtain ⟨p, hp⟩ := (Module.End.mem_maxGenEigenspace _ _ _).mp hx
  let ℓ : N →L[ℂ] ℂ := (innerSL ℂ x) ∘L P.J
  have hℓ : ∀ y, ℓ y = P.form x y := fun y => by simp [ℓ, form]
  have hle : RootProjection.rootComplement (P.A : Module.End ℂ N) 0 ≤
      LinearMap.ker (ℓ : N →ₗ[ℂ] ℂ) := by
    refine iSup₂_le fun ν hν => ?_
    intro y hy
    obtain ⟨q, hq⟩ := (Module.End.mem_maxGenEigenspace _ _ _).mp hy
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hℓ]
    refine P.form_eq_zero_of_rootSpaces (lam := 0) (mu := ν) (by simpa using hν) p q x y ?_ ?_
    · rw [sub_algebraMap_pow_apply_eq]; exact hp
    · rw [sub_algebraMap_pow_apply_eq]; exact hq
  have := hle hy
  rwa [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, hℓ] at this

theorem form_eq_zero_of_mem_rootComplement_of_mem_rootSpace_zero {x y : N}
    (hx : x ∈ RootProjection.rootComplement (P.A : Module.End ℂ N) 0)
    (hy : y ∈ Module.End.maxGenEigenspace (P.A : Module.End ℂ N) 0) : P.form x y = 0 := by
  rw [P.form_conj_symm, P.form_eq_zero_of_mem_rootSpace_zero_of_mem_rootComplement hy hx,
    map_zero]

variable [FiniteDimensional ℂ N]

/-- **The Riesz projection onto the root subspace at `0`** of the state operator, as a continuous
linear map. -/
def rootProjL : N →L[ℂ] N :=
  LinearMap.toContinuousLinearMap (RootProjection.rootProj (P.A : Module.End ℂ N) 0)

theorem rootProjL_apply (x : N) :
    P.rootProjL x = RootProjection.rootProj (P.A : Module.End ℂ N) 0 x := rfl

theorem rootProjL_apply_mem (x : N) :
    P.rootProjL x ∈ Module.End.maxGenEigenspace (P.A : Module.End ℂ N) 0 :=
  RootProjection.rootProj_apply_mem (P.A : Module.End ℂ N) 0 x

theorem sub_rootProjL_mem (x : N) :
    x - P.rootProjL x ∈ RootProjection.rootComplement (P.A : Module.End ℂ N) 0 :=
  RootProjection.sub_rootProj_mem (P.A : Module.End ℂ N) 0 x

theorem rootProjL_rootProjL (x : N) : P.rootProjL (P.rootProjL x) = P.rootProjL x :=
  RootProjection.rootProj_rootProj (P.A : Module.End ℂ N) 0 x

/-- The Riesz projection commutes with the state operator. -/
theorem rootProjL_comm : P.rootProjL * P.A = P.A * P.rootProjL := by
  ext x
  exact RootProjection.rootProj_comm (P.A : Module.End ℂ N) 0 x

/-- The Riesz projection commutes with every resolvent `(1 - c A)⁻¹`. -/
theorem rootProjL_comm_inverse (c : ℂ) :
    P.rootProjL * Ring.inverse (1 - c • P.A) = Ring.inverse (1 - c • P.A) * P.rootProjL := by
  by_cases hu : IsUnit (1 - c • P.A)
  · have hc : P.rootProjL * (1 - c • P.A) = (1 - c • P.A) * P.rootProjL := by
      rw [mul_sub, sub_mul, mul_one, one_mul, mul_smul_comm, smul_mul_assoc, rootProjL_comm]
    calc P.rootProjL * Ring.inverse (1 - c • P.A)
        = 1 * P.rootProjL * Ring.inverse (1 - c • P.A) := by rw [one_mul]
      _ = Ring.inverse (1 - c • P.A) * (1 - c • P.A) * P.rootProjL *
            Ring.inverse (1 - c • P.A) := by rw [Ring.inverse_mul_cancel _ hu]
      _ = Ring.inverse (1 - c • P.A) * ((1 - c • P.A) * P.rootProjL) *
            Ring.inverse (1 - c • P.A) := by simp only [mul_assoc]
      _ = Ring.inverse (1 - c • P.A) * (P.rootProjL * (1 - c • P.A)) *
            Ring.inverse (1 - c • P.A) := by rw [hc]
      _ = Ring.inverse (1 - c • P.A) * P.rootProjL * ((1 - c • P.A) *
            Ring.inverse (1 - c • P.A)) := by simp only [mul_assoc]
      _ = Ring.inverse (1 - c • P.A) * P.rootProjL := by
          rw [Ring.mul_inverse_cancel _ hu, mul_one]
  · rw [Ring.inverse_non_unit _ hu, mul_zero, zero_mul]

/-- **The form splits along the primary decomposition**:
`[x, y] = [π₀ x, π₀ y] + [(1 - π₀) x, (1 - π₀) y]`. -/
theorem form_eq_rootProj_add (x y : N) :
    P.form x y = P.form (P.rootProjL x) (P.rootProjL y) +
      P.form (x - P.rootProjL x) (y - P.rootProjL y) := by
  have hx : x = P.rootProjL x + (x - P.rootProjL x) := by abel
  have hy : y = P.rootProjL y + (y - P.rootProjL y) := by abel
  conv_lhs => rw [hx, hy]
  rw [form_add_left, form_add_right, form_add_right,
    P.form_eq_zero_of_mem_rootSpace_zero_of_mem_rootComplement (P.rootProjL_apply_mem x)
      (P.sub_rootProjL_mem y),
    P.form_eq_zero_of_mem_rootComplement_of_mem_rootSpace_zero (P.sub_rootProjL_mem x)
      (P.rootProjL_apply_mem y)]
  abel

/-- `A^{dim N}` kills the root subspace at `0`: the infinity block is nilpotent. -/
theorem pow_finrank_rootProjL (x : N) : (P.A ^ finrank ℂ N) (P.rootProjL x) = 0 := by
  have h := RootProjection.pow_sub_algebraMap_rootProj (P.A : Module.End ℂ N) 0 x
  rw [map_zero, sub_zero] at h
  rw [rootProjL_apply, ← ContinuousLinearMap.coe_coe, ContinuousLinearMap.toLinearMap_pow]
  exact h

/-- **The resolvent is polynomial on the root subspace at `0`**
(`cor:supp-all-rational`, "on the generalized zero eigenspace of an anchored descriptor pencil,
the resolvent expansion is polynomial"): `(1 - c A)⁻¹ π₀ = ∑_{k < dim N} c^k A^k π₀` at every
regular point. -/
theorem inverse_one_sub_smul_rootProjL {c : ℂ} (hu : IsUnit (1 - c • P.A)) (x : N) :
    Ring.inverse (1 - c • P.A) (P.rootProjL x) =
      (∑ k ∈ Finset.range (finrank ℂ N), c ^ k • P.A ^ k) (P.rootProjL x) := by
  set n := finrank ℂ N
  set S := ∑ k ∈ Finset.range n, c ^ k • P.A ^ k with hS
  have hS' : S = ∑ k ∈ Finset.range n, (c • P.A) ^ k :=
    Finset.sum_congr rfl fun k _ => by rw [smul_pow]
  have hYS : (1 - c • P.A) * S = 1 - (c • P.A) ^ n := by rw [hS', mul_neg_geom_sum]
  have hkill : ((c • P.A) ^ n) (P.rootProjL x) = 0 := by
    rw [smul_pow, smul_apply, P.pow_finrank_rootProjL, smul_zero]
  have h1 : ((1 - c • P.A) * S) (P.rootProjL x) = P.rootProjL x := by
    rw [hYS, sub_apply, hkill, sub_zero, one_apply_eq_self]
  have h2 : (Ring.inverse (1 - c • P.A) * ((1 - c • P.A) * S)) (P.rootProjL x) =
      S (P.rootProjL x) := by
    rw [← mul_assoc, Ring.inverse_mul_cancel _ hu, one_mul]
  rw [mul_apply_eq_comp, h1] at h2
  exact h2

end PontryaginRealization

/-! ## The transfer function of a descriptor realization along the primary decomposition -/

namespace DescriptorRealization

variable {H N : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup N] [InnerProductSpace ℂ N] [CompleteSpace N] [FiniteDimensional ℂ N]
variable (D : DescriptorRealization H N) (t₀ : ℝ) (ht₀ : IsUnit (D.A - (t₀ : ℂ) • D.E))

include ht₀

/-- The transfer function as the anchored form: `⟪h', Q(z) h⟫ = [Γ h', (1 - (z - t₀) T)⁻¹ Γ h]`. -/
theorem inner_transfer_eq_anchored_form {z : ℂ} (hz : IsUnit (D.A - z • D.E)) (h' h : H) :
    ⟪h', D.transfer z h⟫_ℂ = (D.anchored t₀ ht₀).form (D.Γ h')
      (Ring.inverse (1 - (z - t₀ : ℂ) • (D.anchored t₀ ht₀).A) (D.Γ h)) := by
  rw [D.transfer_eq_anchored t₀ ht₀ hz, PontryaginRealization.sandwich_apply,
    PontryaginRealization.form, anchored_Γ, anchored_J]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]

/-- **The transfer function splits along the primary decomposition of the anchored pencil**
(`cor:supp-all-rational`, "the pencil of any regular finite descriptor realization has a primary
decomposition at infinity and at finite spectral points"): with `π₀` the Riesz projection onto the
root subspace at `0` of `T = E (A - t₀ E)⁻¹` and `Y(z) = 1 - (z - t₀) T`,
`⟪h', Q(z) h⟫ = [π₀ Γ h', Y(z)⁻¹ π₀ Γ h] + [(1 - π₀) Γ h', Y(z)⁻¹ (1 - π₀) Γ h]`
in the anchored form `J (A - t₀ E)⁻¹`; on the first block `Y(z)⁻¹` is the polynomial
`∑_k (z - t₀)^k T^k` (`PontryaginRealization.inverse_one_sub_smul_rootProjL`). -/
theorem inner_transfer_eq_rootProj_add {z : ℂ} (hz : IsUnit (D.A - z • D.E)) (h' h : H) :
    ⟪h', D.transfer z h⟫_ℂ =
      (D.anchored t₀ ht₀).form ((D.anchored t₀ ht₀).rootProjL (D.Γ h'))
        (Ring.inverse (1 - (z - t₀ : ℂ) • (D.anchored t₀ ht₀).A)
          ((D.anchored t₀ ht₀).rootProjL (D.Γ h))) +
      (D.anchored t₀ ht₀).form (D.Γ h' - (D.anchored t₀ ht₀).rootProjL (D.Γ h'))
        (Ring.inverse (1 - (z - t₀ : ℂ) • (D.anchored t₀ ht₀).A)
          (D.Γ h - (D.anchored t₀ ht₀).rootProjL (D.Γ h))) := by
  set P := D.anchored t₀ ht₀ with hP
  set Y := Ring.inverse (1 - (z - t₀ : ℂ) • P.A) with hY
  have hcomm : ∀ v, P.rootProjL (Y v) = Y (P.rootProjL v) := fun v => by
    have := congrArg (fun T : N →L[ℂ] N => T v) (P.rootProjL_comm_inverse (z - t₀))
    simpa [mul_apply_eq_comp] using this
  rw [D.inner_transfer_eq_anchored_form t₀ ht₀ hz, P.form_eq_rootProj_add, hcomm, map_sub]

/-- **The infinity part of the transfer function is a polynomial in `z`**: on the root subspace at
`0` of the anchored operator `T`, `[π₀ Γ h', Y(z)⁻¹ π₀ Γ h] = ∑_{k < dim N} (z - t₀)^k [π₀ Γ h', T^k π₀ Γ h]`
(`cor:supp-all-rational`, the polynomial resolvent expansion on the generalized zero eigenspace of
an anchored descriptor pencil). -/
theorem anchored_form_rootProj_inverse_eq_sum {z : ℂ} (hz : IsUnit (D.A - z • D.E)) (h' h : H) :
    (D.anchored t₀ ht₀).form ((D.anchored t₀ ht₀).rootProjL (D.Γ h'))
        (Ring.inverse (1 - (z - t₀ : ℂ) • (D.anchored t₀ ht₀).A)
          ((D.anchored t₀ ht₀).rootProjL (D.Γ h))) =
      ∑ k ∈ Finset.range (finrank ℂ N), (z - t₀ : ℂ) ^ k •
        (D.anchored t₀ ht₀).form ((D.anchored t₀ ht₀).rootProjL (D.Γ h'))
          (((D.anchored t₀ ht₀).A ^ k) ((D.anchored t₀ ht₀).rootProjL (D.Γ h))) := by
  rw [(D.anchored t₀ ht₀).inverse_one_sub_smul_rootProjL (D.isUnit_anchored_pencil t₀ ht₀ hz),
    sum_apply, PontryaginRealization.form_sum_right]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_apply, PontryaginRealization.form_smul_right, smul_eq_mul]

end DescriptorRealization


end RenewalGeometry

end
