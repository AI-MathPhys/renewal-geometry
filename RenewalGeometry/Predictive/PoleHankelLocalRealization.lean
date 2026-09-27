/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.Predictive.PoleHankelInvariants
import RenewalGeometry.Predictive.RationalKreinCanonicalRealization
import RenewalGeometry.Algebra.RootSubspaceProjection

/-!
# Pole–Hankel invariants: the local realization at a pole and the assembled theorem

Paper `predictive_spectral_geometry`, label `thm:supp-pole-Hankel`, items (P1) and (P2), and the
assembled theorem `NormalizedRationalHermitianData.poleHankelInvariants` collecting (P1)–(P4).

For a finite Pontryagin realization `P` and a point `λ`, the Riesz projection `rieszProj λ`
onto the root subspace `R_λ` along the other root subspaces (`Algebra/RootSubspaceProjection.lean`)
commutes with `A` and defines the **local realization** at `λ`:

* `localNilpotent λ = (A - λ)|_{R_λ}` (nilpotent), `localSource λ = π_λ Γ`, `localOutput λ = Γ* J|_{R_λ}`,
* its coefficients `localCoeff λ k = Γ* J (A - λ)^k π_λ Γ` are the **principal-part coefficients**
  of the transfer function at `λ`: `transfer_eq_principalPart_add_regularPart` proves
  `Q(z) = -∑_{k < dim N} (z - λ)^{-k-1} C_k + R_λ(z)` for every `z ≠ λ` in the resolvent set, with
  `R_λ(z) = Γ* J ((A - z)(1 - π_λ) + π_λ)⁻¹ (1 - π_λ) Γ` a resolvent of the regular pencil, which is
  defined and continuous at `z = λ` (`continuousAt_regularPart`): the principal part at `λ`.
* **(P1)** `finrank_range_localHankelMap`: for a source-cyclic realization the local realization is
  controllable and observable, so the rank of the shifted principal-part Hankel operator
  `[C_{i+j+s}]_{i,j < dim N}` equals `rank (A - λ)^s|_{R_λ}`; in particular (`s = 0`) it is the
  local McMillan degree `dim R_λ`, and the successive differences of these ranks are the Jordan
  block counts (`NilpotentHankel.card_chains_ge_eq_finrank_sub`).
* **(P2)** `subNegIndex_rootSpace_eq_negInertia_localHankelGram`: at a real `λ` the Gram matrix of
  the local Krylov family is the principal-part Hankel Gram `[⟪e_k, C_{i+j} e_l⟫]`, so the local
  negative and positive indices are its inertia, with `neg + pos = dim R_λ`.
* `NormalizedRationalHermitianData.poleHankelInvariants`: (P1)–(P4) for the canonical minimal
  realization of a normalized rational Hermitian `Q`.
-/

open scoped InnerProductSpace InnerProduct
open Module Filter Topology

noncomputable section

namespace RenewalGeometry
namespace PontryaginRealization

variable {H N : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup N] [InnerProductSpace ℂ N] [CompleteSpace N]
variable (P : PontryaginRealization H N) [FiniteDimensional ℂ N]

/-! ## The Riesz projection -/

/-- The Riesz projection `π_λ` onto the root subspace `R_λ` along the other root subspaces. -/
def rieszProj (lam : ℂ) : N →L[ℂ] N :=
  LinearMap.toContinuousLinearMap (RootProjection.rootProj P.endA lam)

variable (lam : ℂ)

theorem rieszProj_apply (x : N) : P.rieszProj lam x = RootProjection.rootProj P.endA lam x := rfl

theorem rieszProj_apply_mem (x : N) : P.rieszProj lam x ∈ P.rootSpace lam :=
  RootProjection.rootProj_apply_mem _ _ x

theorem rieszProj_apply_of_mem {x : N} (hx : x ∈ P.rootSpace lam) : P.rieszProj lam x = x :=
  RootProjection.rootProj_apply_of_mem _ _ hx

theorem rieszProj_apply_of_mem_rootSpace_ne {mu : ℂ} (hne : mu ≠ lam) {x : N}
    (hx : x ∈ P.rootSpace mu) : P.rieszProj lam x = 0 :=
  RootProjection.rootProj_apply_of_mem_maxGenEigenspace_ne _ _ hne hx

theorem sub_rieszProj_mem (x : N) :
    x - P.rieszProj lam x ∈ RootProjection.rootComplement P.endA lam :=
  RootProjection.sub_rootProj_mem _ _ x

theorem rieszProj_rieszProj (x : N) : P.rieszProj lam (P.rieszProj lam x) = P.rieszProj lam x :=
  RootProjection.rootProj_rootProj _ _ x

theorem rieszProj_A (x : N) : P.rieszProj lam (P.A x) = P.A (P.rieszProj lam x) :=
  RootProjection.rootProj_comm _ _ x

theorem rieszProj_pow_A (n : ℕ) (x : N) :
    P.rieszProj lam ((P.A ^ n) x) = (P.A ^ n) (P.rieszProj lam x) := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', mul_apply_eq_comp, rieszProj_A, ih, ← mul_apply_eq_comp, ← pow_succ']

theorem commute_A_rieszProj : Commute P.A (P.rieszProj lam) :=
  ContinuousLinearMap.ext fun x => (P.rieszProj_A lam x).symm

theorem commute_sub_algebraMap_rieszProj (z : ℂ) :
    Commute (P.A - algebraMap ℂ (N →L[ℂ] N) z) (P.rieszProj lam) :=
  (P.commute_A_rieszProj lam).sub_left (Algebra.commute_algebraMap_left z _)

theorem isIdempotentElem_rieszProj : IsIdempotentElem (P.rieszProj lam) :=
  ContinuousLinearMap.ext fun x => P.rieszProj_rieszProj lam x

/-- `(A - λ)^{dim N}` vanishes on `R_λ`. -/
theorem pow_sub_algebraMap_finrank_apply_of_mem {x : N} (hx : x ∈ P.rootSpace lam) :
    ((P.A - algebraMap ℂ (N →L[ℂ] N) lam) ^ finrank ℂ N) x = 0 := by
  rw [pow_sub_algebraMap_apply_eq]
  exact RootProjection.pow_sub_algebraMap_finrank_apply_of_mem _ _ hx

theorem pow_sub_algebraMap_finrank_rieszProj (x : N) :
    ((P.A - algebraMap ℂ (N →L[ℂ] N) lam) ^ finrank ℂ N) (P.rieszProj lam x) = 0 :=
  P.pow_sub_algebraMap_finrank_apply_of_mem lam (P.rieszProj_apply_mem lam x)

theorem sub_algebraMap_apply_eq (x : N) :
    (P.A - algebraMap ℂ (N →L[ℂ] N) lam) x = (P.endA - algebraMap ℂ (Module.End ℂ N) lam) x := by
  have := P.pow_sub_algebraMap_apply_eq lam 1 x
  rwa [pow_one, pow_one] at this

/-- `A - λ` maps `R_λ` to itself. -/
theorem sub_algebraMap_apply_mem {x : N} (hx : x ∈ P.rootSpace lam) :
    (P.A - algebraMap ℂ (N →L[ℂ] N) lam) x ∈ P.rootSpace lam := by
  rw [sub_algebraMap_apply_eq]
  exact Module.End.mapsTo_maxGenEigenspace_of_comm
    (Algebra.mul_sub_algebraMap_commutes P.endA lam) lam hx

theorem pow_sub_algebraMap_apply_mem (k : ℕ) {x : N} (hx : x ∈ P.rootSpace lam) :
    ((P.A - algebraMap ℂ (N →L[ℂ] N) lam) ^ k) x ∈ P.rootSpace lam := by
  induction k with
  | zero => simpa using hx
  | succ k ih => rw [pow_succ', mul_apply_eq_comp]; exact P.sub_algebraMap_apply_mem lam ih

omit [FiniteDimensional ℂ N] in
/-- The root complement of `R_λ` is `A`-invariant. -/
theorem A_mem_rootComplement {x : N} (hx : x ∈ RootProjection.rootComplement P.endA lam) :
    P.A x ∈ RootProjection.rootComplement P.endA lam :=
  RootProjection.apply_mem_rootComplement P.endA lam hx

/-! ## The local realization at `λ` -/

omit [FiniteDimensional ℂ N] in
theorem sub_algebraMap_mapsTo :
    Set.MapsTo (P.endA - algebraMap ℂ (Module.End ℂ N) lam) (P.rootSpace lam) (P.rootSpace lam) :=
  Module.End.mapsTo_maxGenEigenspace_of_comm (Algebra.mul_sub_algebraMap_commutes P.endA lam) lam

/-- The local nilpotent state operator `N_λ = (A - λ)|_{R_λ}`. -/
def localNilpotent : Module.End ℂ (P.rootSpace lam) :=
  (P.endA - algebraMap ℂ (Module.End ℂ N) lam).restrict fun _ hx => P.sub_algebraMap_mapsTo lam hx

/-- The local source `B_λ = π_λ Γ : H → R_λ`. -/
def localSource : H →ₗ[ℂ] P.rootSpace lam :=
  (RootProjection.rootProj P.endA lam ∘ₗ (P.Γ : H →ₗ[ℂ] N)).codRestrict (P.rootSpace lam)
    fun h => P.rieszProj_apply_mem lam (P.Γ h)

/-- The local output `L_λ = Γ* J|_{R_λ}`. -/
def localOutput : P.rootSpace lam →ₗ[ℂ] H :=
  ((P.Γ† ∘L P.J : N →L[ℂ] H) : N →ₗ[ℂ] H) ∘ₗ (P.rootSpace lam).subtype

/-- The **principal-part coefficients** `C_k = Γ* J (A - λ)^k π_λ Γ` at `λ`. -/
def localCoeff (k : ℕ) : H →L[ℂ] H :=
  ((P.Γ† ∘L P.J) ∘L (((P.A - algebraMap ℂ (N →L[ℂ] N) lam) ^ k) ∘L P.rieszProj lam)) ∘L P.Γ

theorem coe_localNilpotent_apply (x : P.rootSpace lam) :
    (P.localNilpotent lam x : N) = (P.A - algebraMap ℂ (N →L[ℂ] N) lam) x := by
  rw [localNilpotent, LinearMap.coe_restrict_apply,
    ← pow_one (P.endA - algebraMap ℂ (Module.End ℂ N) lam), ← pow_sub_algebraMap_apply_eq, pow_one]

theorem coe_localNilpotent_pow_apply (k : ℕ) (x : P.rootSpace lam) :
    ((P.localNilpotent lam ^ k) x : N) = ((P.A - algebraMap ℂ (N →L[ℂ] N) lam) ^ k) x := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, coe_localNilpotent_apply, ih, pow_succ',
        mul_apply_eq_comp]

theorem coe_localSource_apply (h : H) : (P.localSource lam h : N) = P.rieszProj lam (P.Γ h) := rfl

theorem localOutput_apply (x : P.rootSpace lam) :
    P.localOutput lam x = ContinuousLinearMap.adjoint P.Γ (P.J x) := rfl

/-- The coefficients of the local realization are the principal-part coefficients. -/
theorem localOutput_localNilpotent_pow_localSource (k : ℕ) (h : H) :
    P.localOutput lam ((P.localNilpotent lam ^ k) (P.localSource lam h)) = P.localCoeff lam k h := by
  rw [localOutput_apply, coe_localNilpotent_pow_apply, coe_localSource_apply]
  rfl

/-- The local Hankel operator has entries `C_{i+j+s}`. -/
theorem localHankelMap_apply (s p : ℕ) (u : Fin p → H) (i : Fin p) :
    NilpotentHankel.hankelMap (P.localNilpotent lam) (P.localSource lam) (P.localOutput lam) s p u i =
      ∑ j : Fin p, P.localCoeff lam ((i : ℕ) + j + s) (u j) := by
  rw [NilpotentHankel.hankelMap_apply]
  exact Finset.sum_congr rfl fun j _ => P.localOutput_localNilpotent_pow_localSource lam _ _

/-! ## The principal part of the transfer function at `λ` -/

/-- The **principal part** `-∑_{k < dim N} (z - λ)^{-k-1} C_k` of the transfer function at `λ`. -/
def principalPart (z : ℂ) : H →L[ℂ] H :=
  -∑ k ∈ Finset.range (finrank ℂ N), ((z - lam) ^ (k + 1))⁻¹ • P.localCoeff lam k

/-- The regular pencil `(A - z)(1 - π_λ) + π_λ`. -/
def regularPencil (z : ℂ) : N →L[ℂ] N :=
  (P.A - algebraMap ℂ (N →L[ℂ] N) z) * (1 - P.rieszProj lam) + P.rieszProj lam

/-- The **regular part** `Γ* J ((A - z)(1 - π_λ) + π_λ)⁻¹ (1 - π_λ) Γ` of the transfer function at
`λ`: a resolvent of the regular pencil, defined and continuous at `z = λ`. -/
def regularPart (z : ℂ) : H →L[ℂ] H :=
  P.sandwich (Ring.inverse (P.regularPencil lam z) * (1 - P.rieszProj lam))

theorem regularPencil_apply (z : ℂ) (x : N) :
    P.regularPencil lam z x = (P.A - algebraMap ℂ (N →L[ℂ] N) z) (x - P.rieszProj lam x) +
      P.rieszProj lam x := by
  simp [regularPencil, mul_apply_eq_comp]

theorem coe_regularPencil_self :
    (P.regularPencil lam lam : N →ₗ[ℂ] N) = RootProjection.regularPencil P.endA lam := by
  ext x
  rw [ContinuousLinearMap.coe_coe, regularPencil_apply, RootProjection.regularPencil_apply,
    sub_algebraMap_apply, LinearMap.sub_apply, Module.algebraMap_end_apply]
  rfl

/-- The regular pencil is invertible at `z = λ`. -/
theorem isUnit_regularPencil_self : IsUnit (P.regularPencil lam lam) := by
  rw [ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap, coe_regularPencil_self]
  exact RootProjection.isUnit_regularPencil _ _

theorem continuous_regularPencil : Continuous (P.regularPencil lam) := by
  unfold regularPencil
  fun_prop

/-- **The regular part is continuous at `λ`**: the principal part carries the whole singularity. -/
theorem continuousAt_regularPart : ContinuousAt (P.regularPart lam) lam := by
  have h1 : ContinuousAt (Ring.inverse : (N →L[ℂ] N) → N →L[ℂ] N) (P.regularPencil lam lam) := by
    have := NormedRing.inverse_continuousAt (P.isUnit_regularPencil_self lam).unit
    rwa [IsUnit.unit_spec] at this
  have h2 : ContinuousAt (fun z => Ring.inverse (P.regularPencil lam z) * (1 - P.rieszProj lam))
      lam :=
    (h1.comp (P.continuous_regularPencil lam).continuousAt).mul continuousAt_const
  exact P.sandwich.continuous.continuousAt.comp h2

/-- The resolvent of `A` compressed to the complement of `R_λ` is the resolvent of the regular
pencil. -/
theorem inverse_mul_one_sub_rieszProj {z : ℂ} (hz : IsUnit (P.A - algebraMap ℂ (N →L[ℂ] N) z)) :
    Ring.inverse (P.A - algebraMap ℂ (N →L[ℂ] N) z) * (1 - P.rieszProj lam) =
      Ring.inverse (P.regularPencil lam z) * (1 - P.rieszProj lam) := by
  set X := P.A - algebraMap ℂ (N →L[ℂ] N) z with hX
  set π := P.rieszProj lam with hπ
  have hcomm : X * π = π * X := (P.commute_sub_algebraMap_rieszProj lam z).eq
  obtain ⟨h1, h2⟩ := RootProjection.pencil_mul_pencilInverse X (Ring.inverse X) π
    (Ring.mul_inverse_cancel X hz) (Ring.inverse_mul_cancel X hz) hcomm
    (P.isIdempotentElem_rieszProj lam)
  have hinv : Ring.inverse (P.regularPencil lam z) = Ring.inverse X * (1 - π) + π := by
    let u : (N →L[ℂ] N)ˣ := ⟨P.regularPencil lam z, Ring.inverse X * (1 - π) + π, h1, h2⟩
    exact Ring.inverse_unit u
  rw [hinv]
  exact (RootProjection.pencilInverse_mul_one_sub (Ring.inverse X) π
    (P.isIdempotentElem_rieszProj lam)).symm

/-- The finite Laurent expansion of the resolvent on the root subspace: for `x ∈ R_λ` and `z ≠ λ`
in the resolvent set, `(A - z)⁻¹ x = -∑_{k < dim N} (z - λ)^{-k-1} (A - λ)^k x`. -/
theorem inverse_apply_of_mem_rootSpace {z : ℂ} (hz : IsUnit (P.A - algebraMap ℂ (N →L[ℂ] N) z))
    (hne : z ≠ lam) {x : N} (hx : x ∈ P.rootSpace lam) :
    Ring.inverse (P.A - algebraMap ℂ (N →L[ℂ] N) z) x =
      -∑ k ∈ Finset.range (finrank ℂ N),
        ((z - lam) ^ (k + 1))⁻¹ • ((P.A - algebraMap ℂ (N →L[ℂ] N) lam) ^ k) x := by
  set w := z - lam with hw
  have hw0 : w ≠ 0 := sub_ne_zero.mpr hne
  set Nn := P.A - algebraMap ℂ (N →L[ℂ] N) lam with hNn
  set g : ℕ → N := fun k => (w ^ k)⁻¹ • (Nn ^ k) x with hg
  set y := -∑ k ∈ Finset.range (finrank ℂ N), (w ^ (k + 1))⁻¹ • (Nn ^ k) x with hy
  have hsplit : P.A - algebraMap ℂ (N →L[ℂ] N) z = Nn - w • 1 := by
    rw [hNn, hw, sub_smul, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    abel
  have hNy : Nn y = -∑ k ∈ Finset.range (finrank ℂ N), g (k + 1) := by
    rw [hy, map_neg, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, hg]
    show _ = (w ^ (k + 1))⁻¹ • (Nn ^ (k + 1)) x
    rw [pow_succ' Nn, mul_apply_eq_comp]
  have hwy : (w • (1 : N →L[ℂ] N)) y = -∑ k ∈ Finset.range (finrank ℂ N), g k := by
    rw [smul_apply, one_apply_eq_self, hy, smul_neg, Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_smul, hg]
    simp only
    congr 1
    field_simp
    ring
  have hkey : (P.A - algebraMap ℂ (N →L[ℂ] N) z) y = x := by
    rw [hsplit, sub_apply, hNy, hwy, neg_sub_neg, ← Finset.sum_sub_distrib,
      Finset.sum_range_sub' g, hg]
    simp only
    rw [P.pow_sub_algebraMap_finrank_apply_of_mem lam hx, smul_zero, sub_zero, pow_zero, inv_one,
      one_smul, pow_zero, one_apply_eq_self]
  rw [← hkey, ← mul_apply_eq_comp, Ring.inverse_mul_cancel _ hz,
    one_apply_eq_self]

/-- **The principal-part decomposition of the transfer function at `λ`**: for every `z ≠ λ` in the
resolvent set, `Q(z) = -∑_{k < dim N} (z - λ)^{-k-1} C_k + R_λ(z)` with `C_k` the principal-part
coefficients and `R_λ` the regular part (continuous at `λ`).  Hence the `C_k` are the
principal-part coefficients of `Q` at the pole `λ` (`thm:supp-pole-Hankel`). -/
theorem transfer_eq_principalPart_add_regularPart {z : ℂ}
    (hz : IsUnit (P.A - algebraMap ℂ (N →L[ℂ] N) z)) (hne : z ≠ lam) :
    P.transfer z = P.principalPart lam z + P.regularPart lam z := by
  refine ContinuousLinearMap.ext fun h => ?_
  have hdec : P.Γ h = P.rieszProj lam (P.Γ h) + (1 - P.rieszProj lam) (P.Γ h) := by
    rw [sub_apply, one_apply_eq_self]; abel
  have h1 := P.inverse_apply_of_mem_rootSpace lam hz hne (P.rieszProj_apply_mem lam (P.Γ h))
  have h2 : Ring.inverse (P.A - algebraMap ℂ (N →L[ℂ] N) z) ((1 - P.rieszProj lam) (P.Γ h)) =
      Ring.inverse (P.regularPencil lam z) ((1 - P.rieszProj lam) (P.Γ h)) := by
    rw [← mul_apply_eq_comp, P.inverse_mul_one_sub_rieszProj lam hz, mul_apply_eq_comp]
  have hL : P.transfer z h = ContinuousLinearMap.adjoint P.Γ (P.J
      (Ring.inverse (P.A - algebraMap ℂ (N →L[ℂ] N) z) (P.Γ h))) := rfl
  have hR : (P.principalPart lam z + P.regularPart lam z) h =
      ContinuousLinearMap.adjoint P.Γ (P.J (-∑ k ∈ Finset.range (finrank ℂ N),
        ((z - lam) ^ (k + 1))⁻¹ • ((P.A - algebraMap ℂ (N →L[ℂ] N) lam) ^ k)
          (P.rieszProj lam (P.Γ h)))) +
      ContinuousLinearMap.adjoint P.Γ (P.J
        (Ring.inverse (P.regularPencil lam z) ((1 - P.rieszProj lam) (P.Γ h)))) := by
    simp only [principalPart, regularPart, sandwich_apply, localCoeff, add_apply, neg_apply,
      ContinuousLinearMap.sum_apply, smul_apply, ContinuousLinearMap.comp_apply, map_neg, map_sum,
      map_smul, mul_apply_eq_comp]
  rw [hL, hR]
  conv_lhs => rw [hdec, map_add, map_add, map_add]
  rw [h1, h2]

/-! ## Local controllability and observability from cyclicity -/

/-- The powers of `A` applied to a root vector `x ∈ R_λ` lie in the span of `(A - λ)^i x`,
`i < dim N`. -/
theorem pow_A_apply_mem_span_of_mem_rootSpace {x : N} (hx : x ∈ P.rootSpace lam) (j : ℕ) :
    (P.A ^ j) x ∈ Submodule.span ℂ (Set.range fun i : Fin (finrank ℂ N) =>
      ((P.A - algebraMap ℂ (N →L[ℂ] N) lam) ^ (i : ℕ)) x) := by
  set S := Submodule.span ℂ (Set.range fun i : Fin (finrank ℂ N) =>
    ((P.A - algebraMap ℂ (N →L[ℂ] N) lam) ^ (i : ℕ)) x) with hS
  have hgen : ∀ i : ℕ, ((P.A - algebraMap ℂ (N →L[ℂ] N) lam) ^ i) x ∈ S := by
    intro i
    by_cases hi : i < finrank ℂ N
    · exact Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.mp hi)
      rw [add_comm, pow_add, mul_apply_eq_comp,
        P.pow_sub_algebraMap_finrank_apply_of_mem lam hx, map_zero]
      exact Submodule.zero_mem _
  have hinv : ∀ y ∈ S, P.A y ∈ S := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨i, rfl⟩ := hy
        have : P.A (((P.A - algebraMap ℂ (N →L[ℂ] N) lam) ^ (i : ℕ)) x) =
            ((P.A - algebraMap ℂ (N →L[ℂ] N) lam) ^ ((i : ℕ) + 1)) x +
              lam • ((P.A - algebraMap ℂ (N →L[ℂ] N) lam) ^ (i : ℕ)) x := by
          rw [pow_succ', mul_apply_eq_comp, sub_algebraMap_apply]
          abel
        rw [this]
        exact Submodule.add_mem _ (hgen _) (Submodule.smul_mem _ _ (hgen _))
    | zero => simp
    | add y y' _ _ hy hy' => rw [map_add]; exact Submodule.add_mem _ hy hy'
    | smul c y _ hy => rw [map_smul]; exact Submodule.smul_mem _ _ hy
  induction j with
  | zero => simpa using hgen 0
  | succ j ih => rw [pow_succ', mul_apply_eq_comp]; exact hinv _ ih

/-- The local Krylov span `span {(A - λ)^i π_λ Γ h : i < dim N, h ∈ H}`. -/
def localSpan : Submodule ℂ N :=
  Submodule.span ℂ (Set.range fun p : Fin (finrank ℂ N) × H =>
    ((P.A - algebraMap ℂ (N →L[ℂ] N) lam) ^ (p.1 : ℕ)) (P.rieszProj lam (P.Γ p.2)))

theorem localSpan_le_rootSpace : P.localSpan lam ≤ P.rootSpace lam := by
  rw [localSpan, Submodule.span_le]
  rintro _ ⟨⟨i, h⟩, rfl⟩
  exact P.pow_sub_algebraMap_apply_mem lam _ (P.rieszProj_apply_mem lam _)

/-- **Local controllability**: for a source-cyclic realization the local Krylov family spans the
root subspace. -/
theorem rootSpace_le_localSpan (hcyc : P.IsCyclic) : P.rootSpace lam ≤ P.localSpan lam := by
  intro x hx
  have hx' : x ∈ Submodule.map (P.rieszProj lam : N →ₗ[ℂ] N)
      (Submodule.span ℂ (Set.range fun p : ℕ × H => (P.A ^ p.1) (P.Γ p.2))) := by
    rw [hcyc, Submodule.map_top]
    exact ⟨x, P.rieszProj_apply_of_mem lam hx⟩
  rw [Submodule.map_span] at hx'
  refine (Submodule.span_le.mpr ?_) hx'
  rintro _ ⟨_, ⟨⟨j, h⟩, rfl⟩, rfl⟩
  simp only [ContinuousLinearMap.coe_coe]
  rw [rieszProj_pow_A]
  refine Submodule.span_mono ?_ (P.pow_A_apply_mem_span_of_mem_rootSpace lam
    (P.rieszProj_apply_mem lam (P.Γ h)) j)
  rintro _ ⟨i, rfl⟩
  exact ⟨(i, h), rfl⟩

theorem localSpan_eq_rootSpace (hcyc : P.IsCyclic) : P.localSpan lam = P.rootSpace lam :=
  le_antisymm (P.localSpan_le_rootSpace lam) (P.rootSpace_le_localSpan lam hcyc)

/-- **Local controllability** of the local realization `(N_λ, B_λ)` for a source-cyclic
realization: the controllability map of length `dim N` is onto `R_λ`. -/
theorem range_localCtrlMap (hcyc : P.IsCyclic) :
    LinearMap.range (NilpotentHankel.ctrlMap (P.localNilpotent lam) (P.localSource lam)
      (finrank ℂ N)) = ⊤ := by
  rw [eq_top_iff]
  intro v _
  have hv : (v : N) ∈ P.localSpan lam := P.rootSpace_le_localSpan lam hcyc v.2
  have hle : P.localSpan lam ≤ Submodule.map (P.rootSpace lam).subtype
      (LinearMap.range (NilpotentHankel.ctrlMap (P.localNilpotent lam) (P.localSource lam)
        (finrank ℂ N))) := by
    rw [localSpan, Submodule.span_le]
    rintro _ ⟨⟨i, h⟩, rfl⟩
    refine ⟨(P.localNilpotent lam ^ (i : ℕ)) (P.localSource lam h), ?_, ?_⟩
    · refine ⟨Pi.single i h, ?_⟩
      rw [NilpotentHankel.ctrlMap_apply]
      rw [Finset.sum_eq_single i]
      · rw [Pi.single_eq_same]
      · intro j _ hj
        rw [Pi.single_eq_of_ne hj, map_zero, map_zero]
      · intro hi; exact absurd (Finset.mem_univ i) hi
    · simp only [Submodule.subtype_apply]
      rw [coe_localNilpotent_pow_apply, coe_localSource_apply]
  obtain ⟨t, ht, hte⟩ := hle hv
  have : t = v := Subtype.ext hte
  exact this ▸ ht

/-- `[Γ h, y] = ⟪h, Γ* J y⟫`. -/
theorem form_Γ_left (h : H) (y : N) :
    P.form (P.Γ h) y = ⟪h, ContinuousLinearMap.adjoint P.Γ (P.J y)⟫_ℂ := by
  rw [form, ContinuousLinearMap.adjoint_inner_right]

/-- **Local observability** of the local realization `(N_λ, L_λ)` for a source-cyclic
realization: the observability map of length `dim N` is injective on `R_λ`. -/
theorem ker_localObsMap (hcyc : P.IsCyclic) :
    LinearMap.ker (NilpotentHankel.obsMap (P.localNilpotent lam) (P.localOutput lam)
      (finrank ℂ N)) = ⊥ := by
  rw [LinearMap.ker_eq_bot']
  intro v hv
  have hread : ∀ i : Fin (finrank ℂ N), ∀ h : H,
      P.form (P.Γ h) (((P.A - algebraMap ℂ (N →L[ℂ] N) lam) ^ (i : ℕ)) v) = 0 := by
    intro i h
    have := congrFun hv i
    rw [NilpotentHankel.obsMap_apply, localOutput_apply, coe_localNilpotent_pow_apply,
      Pi.zero_apply] at this
    rw [form_Γ_left, this, inner_zero_right]
  have hspan : ∀ h : H, ∀ y ∈ Submodule.span ℂ (Set.range fun i : Fin (finrank ℂ N) =>
      ((P.A - algebraMap ℂ (N →L[ℂ] N) lam) ^ (i : ℕ)) (v : N)), P.form (P.Γ h) y = 0 := by
    intro h y hy
    induction hy using Submodule.span_induction with
    | mem y hy => obtain ⟨i, rfl⟩ := hy; exact hread i h
    | zero => exact P.form_zero_right _
    | add y y' _ _ hy hy' => rw [form_add_right, hy, hy', add_zero]
    | smul c y _ hy => rw [form_smul_right, hy, mul_zero]
  have hall : ∀ x : N, P.form x v = 0 := by
    intro x
    have hx : x ∈ Submodule.span ℂ (Set.range fun p : ℕ × H => (P.A ^ p.1) (P.Γ p.2)) := by
      rw [hcyc]; exact Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨⟨j, h⟩, rfl⟩ := hx
        simp only
        rw [form_pow_A_left]
        exact hspan h _ (P.pow_A_apply_mem_span_of_mem_rootSpace lam v.2 j)
    | zero => exact P.form_zero_left _
    | add x x' _ _ hx hx' => rw [form_add_left, hx, hx', add_zero]
    | smul c x _ hx => rw [form_smul_left, hx, mul_zero]
  exact Subtype.ext (P.eq_zero_of_form_eq_zero hall)

/-- **(P1) Shifted principal-part Hankel ranks.**  For a source-cyclic (minimal) realization, the
rank of the shifted principal-part Hankel operator `[C_{i+j+s}]_{i,j < dim N}` at `λ` equals the
rank of `(A - λ)^s|_{R_λ}`; so the principal part at `λ` determines the ranks of all powers of the
nilpotent local state operator, hence (`NilpotentHankel.card_chains_ge_eq_finrank_sub`) all Jordan
block sizes at `λ`. -/
theorem finrank_range_localHankelMap (hcyc : P.IsCyclic) (s : ℕ) :
    finrank ℂ (LinearMap.range (NilpotentHankel.hankelMap (P.localNilpotent lam)
      (P.localSource lam) (P.localOutput lam) s (finrank ℂ N))) =
      finrank ℂ (LinearMap.range (P.localNilpotent lam ^ s)) :=
  NilpotentHankel.finrank_range_hankelMap _ _ _ s _ (P.range_localCtrlMap lam hcyc)
    (P.ker_localObsMap lam hcyc)

/-- **(P1) Local McMillan degree.**  The unshifted principal-part Hankel rank at `λ` is the
dimension of the root subspace `R_λ`. -/
theorem finrank_range_localHankelMap_zero (hcyc : P.IsCyclic) :
    finrank ℂ (LinearMap.range (NilpotentHankel.hankelMap (P.localNilpotent lam)
      (P.localSource lam) (P.localOutput lam) 0 (finrank ℂ N))) = finrank ℂ (P.rootSpace lam) :=
  NilpotentHankel.finrank_range_hankelMap_zero _ _ _ _ (P.range_localCtrlMap lam hcyc)
    (P.ker_localObsMap lam hcyc)

/-! ## (P2) The principal-part Hankel Gram at a real pole -/

/-- For a real `λ`, `A - λ` is symmetric for the Pontryagin form. -/
theorem form_sub_algebraMap_left_of_real (hlam : lam.im = 0) (x y : N) :
    P.form ((P.A - algebraMap ℂ (N →L[ℂ] N) lam) x) y =
      P.form x ((P.A - algebraMap ℂ (N →L[ℂ] N) lam) y) := by
  have := P.form_sub_algebraMap_comm lam lam x y
  rw [Complex.conj_eq_iff_im.mpr hlam, sub_self, zero_mul, sub_eq_zero] at this
  exact this

theorem form_pow_sub_algebraMap_left_of_real (hlam : lam.im = 0) (k : ℕ) (x y : N) :
    P.form (((P.A - algebraMap ℂ (N →L[ℂ] N) lam) ^ k) x) y =
      P.form x (((P.A - algebraMap ℂ (N →L[ℂ] N) lam) ^ k) y) := by
  induction k generalizing y with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', mul_apply_eq_comp, form_sub_algebraMap_left_of_real P lam hlam, ih,
        ← mul_apply_eq_comp, ← pow_succ, ← pow_succ']

/-- For a real `λ` the root complement is form-orthogonal to `R_λ`. -/
theorem form_eq_zero_of_mem_rootComplement_of_real (hlam : lam.im = 0) {x y : N}
    (hx : x ∈ RootProjection.rootComplement P.endA lam) (hy : y ∈ P.rootSpace lam) :
    P.form x y = 0 := by
  have hle : RootProjection.rootComplement P.endA lam ≤ P.rightOrthogonal (P.rootSpace lam) := by
    refine iSup₂_le fun nu hnu => ?_
    intro x hx y hy
    refine P.form_eq_zero_of_mem_rootSpace ?_ hx hy
    intro h
    exact hnu (by rw [← Complex.conj_conj nu, ← h, Complex.conj_eq_iff_im.mpr hlam])
  exact hle hx y hy

/-- For a real `λ`, `[π_λ Γ u, y] = [Γ u, y]` for `y ∈ R_λ`. -/
theorem form_rieszProj_Γ_left_of_real (hlam : lam.im = 0) (u : H) {y : N}
    (hy : y ∈ P.rootSpace lam) : P.form (P.rieszProj lam (P.Γ u)) y = P.form (P.Γ u) y := by
  have hsplit : P.Γ u = P.rieszProj lam (P.Γ u) + (P.Γ u - P.rieszProj lam (P.Γ u)) := by abel
  conv_rhs => rw [hsplit, form_add_left,
    P.form_eq_zero_of_mem_rootComplement_of_real lam hlam (P.sub_rieszProj_mem lam _) hy, add_zero]

/-- The local Krylov family `(i, k) ↦ (A - λ)^i π_λ Γ e_k`, `i < dim N`. -/
def localKrylov {m : ℕ} (e : Fin m → H) : Fin (finrank ℂ N) × Fin m → N :=
  fun p => ((P.A - algebraMap ℂ (N →L[ℂ] N) lam) ^ (p.1 : ℕ)) (P.rieszProj lam (P.Γ (e p.2)))

/-- The **principal-part Hankel Gram** `[⟪e_k, C_{i+j} e_l⟫]_{(i,k),(j,l)}` at `λ`. -/
def localHankelGram {m : ℕ} (e : Fin m → H) :
    Matrix (Fin (finrank ℂ N) × Fin m) (Fin (finrank ℂ N) × Fin m) ℂ :=
  Matrix.of fun p q => ⟪e p.2, P.localCoeff lam ((p.1 : ℕ) + q.1) (e q.2)⟫_ℂ

/-- **(P2) mechanism**: at a real `λ` the Gram matrix of the local Krylov family is the
principal-part Hankel Gram. -/
theorem gram_localKrylov_of_real (hlam : lam.im = 0) {m : ℕ} (e : Fin m → H) :
    P.gram (P.localKrylov lam e) = P.localHankelGram lam e := by
  ext p q
  simp only [gram, localHankelGram, Matrix.of_apply, localKrylov]
  rw [form_pow_sub_algebraMap_left_of_real P lam hlam, ← mul_apply_eq_comp, ← pow_add,
    P.form_rieszProj_Γ_left_of_real lam hlam _
      (P.pow_sub_algebraMap_apply_mem lam _ (P.rieszProj_apply_mem lam _)), form_Γ_left]
  rfl

/-- For a source-cyclic realization the local Krylov family over a basis of `H` spans `R_λ`. -/
theorem span_localKrylov_eq_rootSpace (hcyc : P.IsCyclic) {m : ℕ} (e : Basis (Fin m) ℂ H) :
    Submodule.span ℂ (Set.range (P.localKrylov lam e)) = P.rootSpace lam := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨p, rfl⟩
    exact P.pow_sub_algebraMap_apply_mem lam _ (P.rieszProj_apply_mem lam _)
  · refine (P.rootSpace_le_localSpan lam hcyc).trans ?_
    rw [localSpan, Submodule.span_le]
    rintro _ ⟨⟨i, h⟩, rfl⟩
    have hexp : ((P.A - algebraMap ℂ (N →L[ℂ] N) lam) ^ (i : ℕ)) (P.rieszProj lam (P.Γ h)) =
        ∑ k, e.repr h k • P.localKrylov lam e (i, k) := by
      conv_lhs => rw [← e.sum_repr h]
      simp only [map_sum, map_smul, localKrylov]
    show ((P.A - algebraMap ℂ (N →L[ℂ] N) lam) ^ (i : ℕ)) (P.rieszProj lam (P.Γ h)) ∈ _
    rw [hexp]
    exact Submodule.sum_mem _ fun k _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨(i, k), rfl⟩)

/-- **(P2) Local negative index at a real pole**: for a source-cyclic realization the negative
index of the form on `R_λ` is the negative inertia of the principal-part Hankel Gram. -/
theorem subNegIndex_rootSpace_eq_negInertia_localHankelGram (hcyc : P.IsCyclic) (hlam : lam.im = 0)
    {m : ℕ} (e : Basis (Fin m) ℂ H) :
    P.subNegIndex (P.rootSpace lam) = negInertia (P.localHankelGram lam e) := by
  rw [← P.gram_localKrylov_of_real lam hlam e]
  exact P.subNegIndex_eq_negInertia_gram _ _ (P.span_localKrylov_eq_rootSpace lam hcyc e)

/-- **(P2) Local positive index at a real pole.** -/
theorem subPosIndex_rootSpace_eq_posInertia_localHankelGram (hcyc : P.IsCyclic) (hlam : lam.im = 0)
    {m : ℕ} (e : Basis (Fin m) ℂ H) :
    P.subPosIndex (P.rootSpace lam) = posInertia (P.localHankelGram lam e) := by
  rw [← P.gram_localKrylov_of_real lam hlam e]
  exact P.subPosIndex_eq_posInertia_gram _ _ (P.span_localKrylov_eq_rootSpace lam hcyc e)

/-- The form is nondegenerate on a real root subspace. -/
theorem isNondegenerateOn_rootSpace_of_real (hlam : lam.im = 0) :
    P.IsNondegenerateOn (P.rootSpace lam) := by
  by_cases hbot : P.rootSpace lam = ⊥
  · intro y hy _
    rw [hbot] at hy
    exact (Submodule.mem_bot ℂ).mp hy
  · obtain ⟨S, hS⟩ := P.exists_poleFinset
    have := P.isNondegenerateOn_poleBlock S hS ((hS lam hbot).1 hlam.ge)
    rwa [P.poleBlock_of_real hlam] at this

/-- **(P2) Sylvester count at a real pole**: `neg + pos = dim R_λ`, so the principal-part Hankel
Gram determines the complete local Pontryagin inertia. -/
theorem subNegIndex_add_subPosIndex_rootSpace_of_real (hlam : lam.im = 0) :
    P.subNegIndex (P.rootSpace lam) + P.subPosIndex (P.rootSpace lam) =
      finrank ℂ (P.rootSpace lam) :=
  P.subNegIndex_add_subPosIndex_eq_finrank _ (P.isNondegenerateOn_rootSpace_of_real lam hlam)

end PontryaginRealization

/-! ## The assembled theorem for a normalized rational Hermitian `Q` -/

namespace NormalizedRationalHermitianData

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
variable (Q : NormalizedRationalHermitianData H)

open PontryaginRealization

/-- **`thm:supp-pole-Hankel` (Pole–Hankel invariants).**  For the canonical minimal Pontryagin
realization `P = Q.canonical` of a normalized rational Hermitian `Q` (whose transfer function is the
rational continuation `Q(z) = Γ⁺ (A - z)⁻¹ Γ` of `Q`), at every point `λ`:

* the transfer function splits as principal part plus a part regular at `λ`,
  `Q(z) = -∑_{k < dim} (z - λ)^{-k-1} C_k + R_λ(z)` with `C_k = Γ* J (A - λ)^k π_λ Γ` and `R_λ`
  continuous at `λ` (so the `C_k` are the principal-part coefficients at the pole `λ`);
* **(P1)** the shifted principal-part Hankel ranks `rank [C_{i+j+s}]` are the ranks of the powers
  of the nilpotent local state operator `(A - λ)|_{R_λ}` (hence all Jordan block sizes, by
  `NilpotentHankel.card_chains_ge_eq_finrank_sub`), and the unshifted rank is the local McMillan
  degree `dim R_λ`;
* **(P2)** at a real `λ` the local negative and positive indices are the inertia of the
  principal-part Hankel Gram, and they add up to `dim R_λ`;
* **(P3)** for `Im λ > 0` the conjugate pair `R_λ ⊔ R_{λ̄}` is a neutral pairing contributing
  `dim R_λ` to both the negative and the positive index;
* **(P4)** the number of negative squares of the Nevanlinna kernel of `Q` (the minimum global
  negative index) is the sum of the local contributions over the poles. -/
theorem poleHankelInvariants :
    (∀ lam z : ℂ, IsUnit (Q.canonical.A - algebraMap ℂ (Q.Carrier →L[ℂ] Q.Carrier) z) → z ≠ lam →
      Q.canonical.transfer z =
        Q.canonical.principalPart lam z + Q.canonical.regularPart lam z) ∧
    (∀ lam : ℂ, ContinuousAt (Q.canonical.regularPart lam) lam) ∧
    (∀ (lam : ℂ) (s : ℕ),
      finrank ℂ (LinearMap.range (NilpotentHankel.hankelMap (Q.canonical.localNilpotent lam)
        (Q.canonical.localSource lam) (Q.canonical.localOutput lam) s
        (finrank ℂ Q.Carrier))) =
      finrank ℂ (LinearMap.range (Q.canonical.localNilpotent lam ^ s))) ∧
    (∀ lam : ℂ,
      finrank ℂ (LinearMap.range (NilpotentHankel.hankelMap (Q.canonical.localNilpotent lam)
        (Q.canonical.localSource lam) (Q.canonical.localOutput lam) 0
        (finrank ℂ Q.Carrier))) = finrank ℂ (Q.canonical.rootSpace lam)) ∧
    (∀ lam : ℂ, lam.im = 0 → ∀ (m : ℕ) (e : Basis (Fin m) ℂ H),
      Q.canonical.subNegIndex (Q.canonical.rootSpace lam) =
          negInertia (Q.canonical.localHankelGram lam e) ∧
        Q.canonical.subPosIndex (Q.canonical.rootSpace lam) =
          posInertia (Q.canonical.localHankelGram lam e) ∧
        Q.canonical.subNegIndex (Q.canonical.rootSpace lam) +
          Q.canonical.subPosIndex (Q.canonical.rootSpace lam) =
            finrank ℂ (Q.canonical.rootSpace lam)) ∧
    (∀ S : Finset ℂ, (∀ lam, Q.canonical.rootSpace lam ≠ ⊥ →
        (0 ≤ lam.im → lam ∈ S) ∧ (lam.im < 0 → starRingEnd ℂ lam ∈ S)) →
      ∀ lam ∈ S, 0 < lam.im →
        finrank ℂ (Q.canonical.rootSpace lam) =
            finrank ℂ (Q.canonical.rootSpace (starRingEnd ℂ lam)) ∧
          Q.canonical.subNegIndex (Q.canonical.poleBlock lam) =
            finrank ℂ (Q.canonical.rootSpace lam) ∧
          Q.canonical.subPosIndex (Q.canonical.poleBlock lam) =
            finrank ℂ (Q.canonical.rootSpace lam)) ∧
    (∀ S : Finset ℂ, (∀ lam, Q.canonical.rootSpace lam ≠ ⊥ →
        (0 ≤ lam.im → lam ∈ S) ∧ (lam.im < 0 → starRingEnd ℂ lam ∈ S)) →
      negSquares (nevanlinnaKernel Q.canonical.transfer) Q.canonical.upperResolventSet =
        ∑ lam ∈ S, Q.canonical.localIndex lam) := by
  have hcyc := Q.canonical_isCyclic
  refine ⟨fun lam z hz hne => Q.canonical.transfer_eq_principalPart_add_regularPart lam hz hne,
    fun lam => Q.canonical.continuousAt_regularPart lam,
    fun lam s => Q.canonical.finrank_range_localHankelMap lam hcyc s,
    fun lam => Q.canonical.finrank_range_localHankelMap_zero lam hcyc,
    fun lam hlam m e =>
      ⟨Q.canonical.subNegIndex_rootSpace_eq_negInertia_localHankelGram lam hcyc hlam e,
      Q.canonical.subPosIndex_rootSpace_eq_posInertia_localHankelGram lam hcyc hlam e,
      Q.canonical.subNegIndex_add_subPosIndex_rootSpace_of_real lam hlam⟩,
    fun S hS lam hlam hpos => Q.canonical.subNegIndex_poleBlock_of_pos S hS hlam hpos,
    fun S hS => Q.canonical.negSquares_eq_sum_localIndex hcyc S hS⟩

end NormalizedRationalHermitianData

end RenewalGeometry

end
