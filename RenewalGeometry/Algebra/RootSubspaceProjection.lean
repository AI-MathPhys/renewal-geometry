/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The Riesz projection onto a root subspace

Infrastructure for `thm:supp-pole-Hankel` (P1)–(P2) of `papers/predictive_spectral_geometry`.

For an endomorphism `f` of a finite dimensional vector space over an algebraically closed field,
the primary decomposition `V = ⊕_ν R_ν` into the root subspaces `R_ν = ker (f - ν)^∞`
(Mathlib's `Module.End.maxGenEigenspace`) yields, for every `μ`, the *Riesz projection*
`rootProj f μ` onto `R_μ` along the sum `rootComplement f μ = ⨆_{ν ≠ μ} R_ν` of the other root
subspaces.  It commutes with `f` (`rootProj_comm`), is idempotent, and `(f - μ)^{dim V}` kills its
range (`pow_sub_algebraMap_rootProj`).  The "regular pencil" `(f - μ)(1 - π_μ) + π_μ`, which
agrees with `f - μ` on the complement and with the identity on `R_μ`, is invertible
(`isUnit_regularPencil`): this is the algebraic core of the statement that the resolvent of `f`
compressed to the complement of `R_μ` is regular at `μ`.
-/

open Module Submodule

namespace RenewalGeometry
namespace RootProjection

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
variable (f : Module.End K V) (μ : K)

/-- The sum of the root subspaces at the points other than `μ`. -/
def rootComplement : Submodule K V := ⨆ (ν) (_ : ν ≠ μ), f.maxGenEigenspace ν

theorem maxGenEigenspace_le_rootComplement {ν : K} (h : ν ≠ μ) :
    f.maxGenEigenspace ν ≤ rootComplement f μ :=
  le_iSup₂ (f := fun ν (_ : ν ≠ μ) => f.maxGenEigenspace ν) ν h

theorem disjoint_rootComplement : Disjoint (f.maxGenEigenspace μ) (rootComplement f μ) :=
  Module.End.independent_maxGenEigenspace f μ

theorem eq_zero_of_mem_of_mem_rootComplement {x : V} (hx : x ∈ f.maxGenEigenspace μ)
    (hx' : x ∈ rootComplement f μ) : x = 0 :=
  (Submodule.mem_bot K).mp ((disjoint_rootComplement f μ).eq_bot ▸ Submodule.mem_inf.mpr ⟨hx, hx'⟩)

/-- The root complement is `f`-invariant. -/
theorem apply_mem_rootComplement {x : V} (hx : x ∈ rootComplement f μ) :
    f x ∈ rootComplement f μ := by
  have hmap : Submodule.map f (rootComplement f μ) ≤ rootComplement f μ := by
    rw [rootComplement, Submodule.map_iSup]
    refine iSup_le fun ν => ?_
    rw [Submodule.map_iSup]
    refine iSup_le fun hν => ?_
    refine le_trans ?_ (maxGenEigenspace_le_rootComplement f μ hν)
    rw [Submodule.map_le_iff_le_comap]
    intro y hy
    exact Module.End.mapsTo_maxGenEigenspace_of_comm (Commute.refl f) ν hy
  exact hmap ⟨x, hx, rfl⟩

theorem apply_mem_maxGenEigenspace {x : V} (hx : x ∈ f.maxGenEigenspace μ) :
    f x ∈ f.maxGenEigenspace μ :=
  Module.End.mapsTo_maxGenEigenspace_of_comm (Commute.refl f) μ hx

/-- An eigenvector lies in the root subspace. -/
theorem mem_maxGenEigenspace_of_sub_apply_eq_zero {x : V}
    (hx : (f - algebraMap K (Module.End K V) μ) x = 0) : x ∈ f.maxGenEigenspace μ := by
  rw [Module.End.mem_maxGenEigenspace]
  exact ⟨1, by rw [pow_one, ← Algebra.algebraMap_eq_smul_one]; exact hx⟩

variable [IsAlgClosed K] [FiniteDimensional K V]

theorem sup_rootComplement : f.maxGenEigenspace μ ⊔ rootComplement f μ = ⊤ := by
  rw [rootComplement, ← iSup_split_single, Module.End.iSup_maxGenEigenspace_eq_top]

theorem isCompl_rootComplement : IsCompl (f.maxGenEigenspace μ) (rootComplement f μ) :=
  ⟨disjoint_rootComplement f μ, codisjoint_iff.mpr (sup_rootComplement f μ)⟩

/-- **The Riesz projection** onto the root subspace `R_μ` along the other root subspaces. -/
noncomputable def rootProj : Module.End K V :=
  (f.maxGenEigenspace μ).projection (rootComplement f μ) (isCompl_rootComplement f μ)

theorem rootProj_apply_mem (x : V) : rootProj f μ x ∈ f.maxGenEigenspace μ :=
  Submodule.projection_apply_mem _ x

theorem rootProj_apply_of_mem {x : V} (hx : x ∈ f.maxGenEigenspace μ) : rootProj f μ x = x :=
  Submodule.projection_apply_of_mem_left _ hx

theorem rootProj_apply_of_mem_rootComplement {x : V} (hx : x ∈ rootComplement f μ) :
    rootProj f μ x = 0 :=
  Submodule.projection_apply_of_mem_right _ hx

theorem rootProj_apply_eq_zero_iff {x : V} : rootProj f μ x = 0 ↔ x ∈ rootComplement f μ :=
  Submodule.projection_apply_eq_zero_iff _

theorem rootProj_apply_of_mem_maxGenEigenspace_ne {ν : K} (hν : ν ≠ μ) {x : V}
    (hx : x ∈ f.maxGenEigenspace ν) : rootProj f μ x = 0 :=
  rootProj_apply_of_mem_rootComplement f μ (maxGenEigenspace_le_rootComplement f μ hν hx)

theorem sub_rootProj_mem (x : V) : x - rootProj f μ x ∈ rootComplement f μ :=
  Submodule.sub_projection_mem _ x

theorem rootProj_rootProj (x : V) : rootProj f μ (rootProj f μ x) = rootProj f μ x :=
  rootProj_apply_of_mem f μ (rootProj_apply_mem f μ x)

/-- The projection of a sum `a + b` with `a ∈ R_μ` and `b` in the complement is `a`. -/
theorem rootProj_add_of_mem {a b : V} (ha : a ∈ f.maxGenEigenspace μ)
    (hb : b ∈ rootComplement f μ) : rootProj f μ (a + b) = a := by
  rw [map_add, rootProj_apply_of_mem f μ ha, rootProj_apply_of_mem_rootComplement f μ hb, add_zero]

/-- **The Riesz projection commutes with `f`.** -/
theorem rootProj_comm (x : V) : rootProj f μ (f x) = f (rootProj f μ x) := by
  have hx : x = rootProj f μ x + (x - rootProj f μ x) := by abel
  conv_lhs => rw [hx, map_add]
  exact rootProj_add_of_mem f μ (apply_mem_maxGenEigenspace f μ (rootProj_apply_mem f μ x))
    (apply_mem_rootComplement f μ (sub_rootProj_mem f μ x))

theorem commute_rootProj : Commute f (rootProj f μ) :=
  LinearMap.ext fun x => (rootProj_comm f μ x).symm

theorem rootProj_pow_comm (n : ℕ) (x : V) :
    rootProj f μ ((f ^ n) x) = (f ^ n) (rootProj f μ x) :=
  LinearMap.congr_fun ((commute_rootProj f μ).pow_left n).symm x

omit [IsAlgClosed K] in
/-- `(f - μ)^{dim V}` vanishes on the root subspace `R_μ`. -/
theorem pow_sub_algebraMap_finrank_apply_of_mem {x : V} (hx : x ∈ f.maxGenEigenspace μ) :
    ((f - algebraMap K (Module.End K V) μ) ^ finrank K V) x = 0 := by
  rw [Module.End.maxGenEigenspace_eq_genEigenspace_finrank, Module.End.mem_genEigenspace_nat,
    LinearMap.mem_ker] at hx
  rw [Algebra.algebraMap_eq_smul_one]
  exact hx

/-- `(f - μ)^{dim V}` kills the range of the Riesz projection. -/
theorem pow_sub_algebraMap_rootProj (x : V) :
    ((f - algebraMap K (Module.End K V) μ) ^ finrank K V) (rootProj f μ x) = 0 :=
  pow_sub_algebraMap_finrank_apply_of_mem f μ (rootProj_apply_mem f μ x)

omit [IsAlgClosed K] [FiniteDimensional K V] in
/-- `f - μ` is injective on the root complement. -/
theorem eq_zero_of_mem_rootComplement_of_sub_apply_eq_zero {x : V} (hx : x ∈ rootComplement f μ)
    (h : (f - algebraMap K (Module.End K V) μ) x = 0) : x = 0 :=
  eq_zero_of_mem_of_mem_rootComplement f μ (mem_maxGenEigenspace_of_sub_apply_eq_zero f μ h) hx

/-- The **regular pencil** `(f - μ)(1 - π_μ) + π_μ`: it agrees with `f - μ` on the complement of
`R_μ` and with the identity on `R_μ`. -/
noncomputable def regularPencil : Module.End K V :=
  (f - algebraMap K (Module.End K V) μ) * (1 - rootProj f μ) + rootProj f μ

theorem regularPencil_apply (x : V) :
    regularPencil f μ x = (f - algebraMap K (Module.End K V) μ) (x - rootProj f μ x) +
      rootProj f μ x := by
  simp [regularPencil]

/-- **The regular pencil is invertible.** -/
theorem isUnit_regularPencil : IsUnit (regularPencil f μ) := by
  rw [LinearMap.isUnit_iff_ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  rw [regularPencil_apply] at hx
  have hb : (f - algebraMap K (Module.End K V) μ) (x - rootProj f μ x) ∈ rootComplement f μ := by
    rw [LinearMap.sub_apply, Module.algebraMap_end_apply]
    exact Submodule.sub_mem _ (apply_mem_rootComplement f μ (sub_rootProj_mem f μ x))
      (Submodule.smul_mem _ _ (sub_rootProj_mem f μ x))
  have ha : rootProj f μ x ∈ f.maxGenEigenspace μ := rootProj_apply_mem f μ x
  have hπ : rootProj f μ x = 0 := by
    have : rootProj f μ x = -(f - algebraMap K (Module.End K V) μ) (x - rootProj f μ x) := by
      rw [eq_neg_iff_add_eq_zero, add_comm]; exact hx
    exact eq_zero_of_mem_of_mem_rootComplement f μ ha (this ▸ Submodule.neg_mem _ hb)
  rw [hπ, sub_zero, add_zero] at hx
  exact eq_zero_of_mem_rootComplement_of_sub_apply_eq_zero f μ
    ((rootProj_apply_eq_zero_iff f μ).mp hπ) hx

/-! ## The inverse of a regular pencil (ring identities) -/

section Ring

variable {R : Type*} [Ring R]

/-- If `X` is invertible with inverse `Xi` and commutes with the idempotent `π`, then
`X (1 - π) + π` is invertible with inverse `Xi (1 - π) + π`. -/
theorem pencil_mul_pencilInverse (X Xi π : R) (hXXi : X * Xi = 1) (hXiX : Xi * X = 1)
    (hcomm : X * π = π * X) (hidem : π * π = π) :
    (X * (1 - π) + π) * (Xi * (1 - π) + π) = 1 ∧ (Xi * (1 - π) + π) * (X * (1 - π) + π) = 1 := by
  have hcomm' : Xi * π = π * Xi := by
    calc Xi * π = Xi * π * (X * Xi) := by rw [hXXi, mul_one]
      _ = Xi * (π * X) * Xi := by simp only [mul_assoc]
      _ = Xi * (X * π) * Xi := by rw [hcomm]
      _ = π * Xi := by rw [← mul_assoc, hXiX, one_mul]
  have hc1 : (1 - π) * X = X * (1 - π) := by rw [sub_mul, mul_sub, one_mul, mul_one, hcomm]
  have hc1' : (1 - π) * Xi = Xi * (1 - π) := by rw [sub_mul, mul_sub, one_mul, mul_one, hcomm']
  have hππ : π * (1 - π) = 0 := by rw [mul_sub, mul_one, hidem, sub_self]
  have hππ' : (1 - π) * π = 0 := by rw [sub_mul, one_mul, hidem, sub_self]
  have h11 : (1 - π) * (1 - π) = 1 - π := by rw [sub_mul, one_mul, hππ, sub_zero]
  constructor
  · have e1 : X * (1 - π) * (Xi * (1 - π)) = 1 - π := by
      calc X * (1 - π) * (Xi * (1 - π)) = X * ((1 - π) * Xi) * (1 - π) := by simp only [mul_assoc]
        _ = X * (Xi * (1 - π)) * (1 - π) := by rw [hc1']
        _ = X * Xi * ((1 - π) * (1 - π)) := by simp only [mul_assoc]
        _ = 1 - π := by rw [hXXi, one_mul, h11]
    have e2 : X * (1 - π) * π = 0 := by rw [mul_assoc, hππ', mul_zero]
    have e3 : π * (Xi * (1 - π)) = 0 := by rw [← mul_assoc, ← hcomm', mul_assoc, hππ, mul_zero]
    rw [add_mul, mul_add, mul_add, e1, e2, e3, hidem]
    abel
  · have e1 : Xi * (1 - π) * (X * (1 - π)) = 1 - π := by
      calc Xi * (1 - π) * (X * (1 - π)) = Xi * ((1 - π) * X) * (1 - π) := by simp only [mul_assoc]
        _ = Xi * (X * (1 - π)) * (1 - π) := by rw [hc1]
        _ = Xi * X * ((1 - π) * (1 - π)) := by simp only [mul_assoc]
        _ = 1 - π := by rw [hXiX, one_mul, h11]
    have e2 : Xi * (1 - π) * π = 0 := by rw [mul_assoc, hππ', mul_zero]
    have e3 : π * (X * (1 - π)) = 0 := by rw [← mul_assoc, ← hcomm, mul_assoc, hππ, mul_zero]
    rw [add_mul, mul_add, mul_add, e1, e2, e3, hidem]
    abel

/-- `(Xi (1 - π) + π) (1 - π) = Xi (1 - π)` for an idempotent `π`. -/
theorem pencilInverse_mul_one_sub (Xi π : R) (hidem : π * π = π) :
    (Xi * (1 - π) + π) * (1 - π) = Xi * (1 - π) := by
  have hππ : π * (1 - π) = 0 := by rw [mul_sub, mul_one, hidem, sub_self]
  have h11 : (1 - π) * (1 - π) = 1 - π := by rw [sub_mul, one_mul, hππ, sub_zero]
  rw [add_mul, mul_assoc, h11, hππ, add_zero]

end Ring

end RootProjection
end RenewalGeometry
