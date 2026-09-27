/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.Predictive.DescriptorPrimaryDecomposition

/-!
# The Weierstrass primary form of a regular descriptor realization and `cor:supp-all-rational`

Paper `predictive_spectral_geometry`, `cor:supp-all-rational` (all finite rational Hermitian
dynamics): the equivalence `eq:supp-all-rational-equivalence` between finite rational Hermitian
dynamic functions and minimal regular Pontryagin descriptor realizations, up to source-fixing
descriptor Pontryagin unitary.

## Contents

* **Compressions** (`restrictL`, `compressGram`, `codRestrictL`,
  `PontryaginRealization.compressToSub`): a self-adjoint Gram operator `G` on `N`, compressed to a
  subspace `U` on which its form is nondegenerate, together with a `G`-self-adjoint operator
  leaving `U` invariant and a source with values in `U`, is again a finite Pontryagin
  realization on `U`.
* **The Weierstrass reduction of a finite Pontryagin realization** `P = (T, Γ, J)` (in the
  application the anchored realization `D.anchored t₀` of a descriptor realization at a real
  regular point `t₀`, `T = E (A - t₀ E)⁻¹`): with `π₀` the Riesz projection onto the root subspace
  `R₀` at `0` and `W` its root complement, the **Weierstrass multiplier**
  `M = (1 + t₀ T) π₀ + T (1 - π₀)` is an invertible `J`-self-adjoint operator commuting with `T`
  and `π₀` (`weierstrassMul`); the **infinity block** is the compression of `(T M⁻¹, π₀ Γ, J M⁻¹)`
  to `R₀` (nilpotent), the **finite block** the compression of `((1 + t₀ T) M⁻¹, (1 - π₀) Γ, J M⁻¹)`
  to `W`, and `weierstrassPrimary` is the resulting realization in Weierstrass primary form.
  `isSourceFixingUnitary_primaryEquiv`: the descriptor realization
  `(T M⁻¹, (1 + t₀ T) M⁻¹, Γ, J M⁻¹)` is related to it by the source-fixing descriptor Pontryagin
  unitary `x ↦ (π₀ x, x - π₀ x)` (`primaryEquiv`).
* **The Weierstrass primary form of a descriptor realization** `D` at a real regular point `t₀`
  (`DescriptorRealization.weierstrassForm`): the right multiplication of `D` by
  `V = (A - t₀ E)⁻¹ M⁻¹` (`weierstrassDescriptor`, a `J`-self-adjoint unit) is related to the
  primary form by the source-fixing unitary `primaryEquiv` (`isSourceFixingUnitary_weierstrass`),
  and the primary form has the same transfer function as `D` at every regular point
  (`weierstrassForm_transfer`; a source-fixing unitary preserves the transfer function,
  `PrimaryDescriptor.IsSourceFixingUnitary.transfer_eq`).
* **Minimality of general descriptor realizations** (`DescriptorRealization.IsMinimal`: the
  resolvent-source vectors `(A - z E)⁻¹ Γ h` over the regular points `z` span the state space —
  the paper's source minimality): it is transported by right multiplications
  (`isMinimal_rightMul`) and by source-fixing unitaries (`IsSourceFixingUnitary.isMinimal`), and on
  a realization in primary form it is exactly the minimality of both blocks
  (`PrimaryDescriptor.toDescriptor_isMinimal_iff`: the resolvent-source span of a direct sum of an
  infinity chain and a finite block is the whole space iff both blocks are source-cyclic; the
  Laurent/Vandermonde argument is `coeff_eq_zero_of_tendsto_zero` for the polynomial part and the
  real-ray resolvent limit `Γ_mem_resolventSourceSpan_real` for the strictly proper part).
* **`cor:supp-all-rational`** (`FiniteRationalHermitianData.descriptor_isMinimal`,
  `DescriptorRealization.toData`, `existsUnique_sourceFixing_unitary_weierstrassForm`,
  `existsUnique_sourceFixing_unitary_weierstrassForm_descriptor`, `finrank_eq_of_isMinimal`,
  `cor_supp_all_rational`): every finite rational Hermitian `Q = P + Q₀` is realized by the minimal
  regular descriptor realization `Q.descriptor` (primary direct sum of the infinity chain of `P`
  and the canonical realization of `Q₀`); every minimal regular descriptor realization `D` has a
  finite rational Hermitian dynamic function `D.toData` (`Q` with `Q(t) = D.transfer t` for large
  real `t`); and any two minimal regular descriptor realizations with the same dynamic function
  are equivalent by reduction to Weierstrass primary form (right multiplication and the
  source-fixing unitary `primaryEquiv`) followed by a **unique** source-fixing descriptor
  Pontryagin unitary between the primary forms.  All minimal realizations of `Q` have state
  dimension `McM(P) + McM(Q₀)`.
-/

open scoped InnerProductSpace InnerProduct
open Module Filter Topology

noncomputable section

namespace RenewalGeometry

/-! ## Ring identities for idempotents and `J`-self-adjoint operators -/

section RingLemmas

variable {R : Type*} [Ring R]

theorem idem_mul_one_sub {π : R} (hidem : π * π = π) : π * (1 - π) = 0 := by
  rw [mul_sub, mul_one, hidem, sub_self]

theorem one_sub_mul_idem {π : R} (hidem : π * π = π) : (1 - π) * π = 0 := by
  rw [sub_mul, one_mul, hidem, sub_self]

theorem one_sub_mul_one_sub_idem {π : R} (hidem : π * π = π) : (1 - π) * (1 - π) = 1 - π := by
  rw [sub_mul, one_mul, idem_mul_one_sub hidem, sub_zero]

/-- The inverse of a unit commutes with everything the unit commutes with. -/
theorem inverse_mul_comm_of_comm {X Y : R} (hX : IsUnit X) (h : X * Y = Y * X) :
    Ring.inverse X * Y = Y * Ring.inverse X := by
  calc Ring.inverse X * Y = Ring.inverse X * Y * (X * Ring.inverse X) := by
        rw [Ring.mul_inverse_cancel X hX, mul_one]
    _ = Ring.inverse X * (Y * X) * Ring.inverse X := by simp only [mul_assoc]
    _ = Ring.inverse X * (X * Y) * Ring.inverse X := by rw [h]
    _ = Y * Ring.inverse X := by rw [← mul_assoc, Ring.inverse_mul_cancel X hX, one_mul]

end RingLemmas

section StarRingLemmas

variable {R : Type*} [Ring R] [StarRing R]

/-- A product of two commuting `J`-self-adjoint elements is `J`-self-adjoint. -/
theorem J_mul_mul_of_comm {J X Y : R} (hX : J * X = star X * J) (hY : J * Y = star Y * J)
    (hXY : X * Y = Y * X) : J * (X * Y) = star (X * Y) * J := by
  calc J * (X * Y) = star X * J * Y := by rw [← mul_assoc, hX]
    _ = star X * star Y * J := by rw [mul_assoc, hY, mul_assoc]
    _ = star (Y * X) * J := by rw [star_mul]
    _ = star (X * Y) * J := by rw [hXY]

/-- The inverse of a `J`-self-adjoint unit is `J`-self-adjoint. -/
theorem J_mul_inverse_of_J_mul {J X : R} (hX : IsUnit X) (hJX : J * X = star X * J) :
    J * Ring.inverse X = star (Ring.inverse X) * J := by
  have h1 : X * Ring.inverse X = 1 := Ring.mul_inverse_cancel X hX
  calc J * Ring.inverse X = star (X * Ring.inverse X) * J * Ring.inverse X := by
        rw [h1, star_one, one_mul]
    _ = star (Ring.inverse X) * (star X * J) * Ring.inverse X := by
        rw [star_mul]; simp only [mul_assoc]
    _ = star (Ring.inverse X) * J * (X * Ring.inverse X) := by rw [← hJX]; simp only [mul_assoc]
    _ = star (Ring.inverse X) * J := by rw [h1, mul_one]

/-- `(J X⁻¹) Y = Y* (J X⁻¹)` when `J Y = Y* J` and `Y` commutes with `X⁻¹`. -/
theorem J_mul_inverse_mul_of_comm {J X Y : R} (hJY : J * Y = star Y * J)
    (hXY : Y * Ring.inverse X = Ring.inverse X * Y) :
    J * Ring.inverse X * Y = star Y * (J * Ring.inverse X) := by
  rw [mul_assoc, ← hXY, ← mul_assoc, hJY, mul_assoc]

end StarRingLemmas

/-! ## Compressions of finite Pontryagin realizations -/

section Compression

variable {H N : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup N] [InnerProductSpace ℂ N] [CompleteSpace N] [FiniteDimensional ℂ N]

/-- The restriction of an operator to an invariant subspace, as a continuous linear map. -/
def restrictL (X : N →L[ℂ] N) (U : Submodule ℂ N) (hX : ∀ u ∈ U, X u ∈ U) : U →L[ℂ] U :=
  LinearMap.toContinuousLinearMap ((X : N →ₗ[ℂ] N).restrict fun u hu => hX u hu)

omit [CompleteSpace N] in
theorem restrictL_coe_apply (X : N →L[ℂ] N) (U : Submodule ℂ N) (hX : ∀ u ∈ U, X u ∈ U)
    (u : U) : (restrictL X U hX u : N) = X u := rfl

omit [CompleteSpace N] in
theorem restrictL_pow_coe_apply (X : N →L[ℂ] N) (U : Submodule ℂ N) (hX : ∀ u ∈ U, X u ∈ U)
    (n : ℕ) (u : U) : ((restrictL X U hX ^ n) u : N) = (X ^ n) u := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', mul_apply_eq_comp, restrictL_coe_apply, ih, pow_succ',
      mul_apply_eq_comp]

/-- The compression `P_U G ι_U` of an operator `G` to a subspace `U`. -/
def compressGram (G : N →L[ℂ] N) (U : Submodule ℂ N) : U →L[ℂ] U :=
  U.orthogonalProjectionOnto ∘L G ∘L U.subtypeL

omit [CompleteSpace N] in
theorem inner_compressGram (G : N →L[ℂ] N) (U : Submodule ℂ N) (u v : U) :
    ⟪u, compressGram G U v⟫_ℂ = ⟪(u : N), G v⟫_ℂ := by
  simp [compressGram]

omit [CompleteSpace N] in
theorem compressGram_inner (G : N →L[ℂ] N) (U : Submodule ℂ N) (u v : U) :
    ⟪compressGram G U u, v⟫_ℂ = ⟪G u, (v : N)⟫_ℂ := by
  rw [← inner_conj_symm, inner_compressGram, inner_conj_symm]

/-- The compression of a self-adjoint operator is self-adjoint. -/
theorem compressGram_isSelfAdjoint {G : N →L[ℂ] N} (hG : IsSelfAdjoint G) (U : Submodule ℂ N) :
    IsSelfAdjoint (compressGram G U) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro u v
  rw [compressGram_inner, inner_compressGram]
  have := ContinuousLinearMap.adjoint_inner_left G (v : N) (u : N)
  rw [ContinuousLinearMap.isSelfAdjoint_iff'.mp hG] at this
  exact this

/-- The compression of `G` to `U` is invertible when the form of `G` is nondegenerate on `U`. -/
theorem compressGram_isUnit (G : N →L[ℂ] N) (U : Submodule ℂ N)
    (hU : ∀ u ∈ U, (∀ v ∈ U, ⟪v, G u⟫_ℂ = 0) → u = 0) : IsUnit (compressGram G U) := by
  rw [ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap, LinearMap.isUnit_iff_ker_eq_bot,
    LinearMap.ker_eq_bot']
  intro u hu
  have hu' : compressGram G U u = 0 := hu
  apply Subtype.ext
  refine hU u u.2 fun v hv => ?_
  have := inner_compressGram G U ⟨v, hv⟩ u
  rw [hu', inner_zero_right] at this
  exact this.symm

/-- The compression of a `G`-self-adjoint operator to an invariant subspace is self-adjoint for
the compressed Gram operator. -/
theorem compressGram_mul_restrictL {G X : N →L[ℂ] N} (hJX : G * X = star X * G)
    (U : Submodule ℂ N) (hX : ∀ u ∈ U, X u ∈ U) :
    compressGram G U * restrictL X U hX = star (restrictL X U hX) * compressGram G U := by
  refine ContinuousLinearMap.ext fun u => ?_
  apply ext_inner_left ℂ
  intro v
  rw [mul_apply_eq_comp, mul_apply_eq_comp, inner_compressGram,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right,
    inner_compressGram, restrictL_coe_apply, restrictL_coe_apply,
    ← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.star_eq_adjoint,
    ← mul_apply_eq_comp (star X) G, ← hJX, mul_apply_eq_comp]

/-- The corestriction of a source to a subspace containing its range. -/
def codRestrictL (Γ : H →L[ℂ] N) (U : Submodule ℂ N) (hΓ : ∀ h, Γ h ∈ U) : H →L[ℂ] U where
  toLinearMap := LinearMap.codRestrict U (Γ : H →ₗ[ℂ] N) hΓ
  cont := Γ.continuous.subtype_mk _

omit [CompleteSpace H] [CompleteSpace N] [FiniteDimensional ℂ N] in
theorem codRestrictL_coe_apply (Γ : H →L[ℂ] N) (U : Submodule ℂ N) (hΓ : ∀ h, Γ h ∈ U) (h : H) :
    (codRestrictL Γ U hΓ h : N) = Γ h := rfl

/-- **The compression of a Pontryagin structure to a subspace**: a self-adjoint Gram operator `G`
whose form is nondegenerate on `U`, a `G`-self-adjoint operator `X` leaving `U` invariant and a
source with values in `U` form a finite Pontryagin realization on `U`. -/
def PontryaginRealization.compressToSub {G : N →L[ℂ] N} (hG : IsSelfAdjoint G) (U : Submodule ℂ N)
    (hU : ∀ u ∈ U, (∀ v ∈ U, ⟪v, G u⟫_ℂ = 0) → u = 0) {X : N →L[ℂ] N} (hX : ∀ u ∈ U, X u ∈ U)
    (hJX : G * X = star X * G) (Γ : H →L[ℂ] N) (hΓ : ∀ h, Γ h ∈ U) :
    PontryaginRealization H U where
  A := restrictL X U hX
  Γ := codRestrictL Γ U hΓ
  J := compressGram G U
  J_selfAdjoint := compressGram_isSelfAdjoint hG U
  J_isUnit := compressGram_isUnit G U hU
  J_mul_A := compressGram_mul_restrictL hJX U hX

theorem PontryaginRealization.compress_form {G : N →L[ℂ] N} (hG : IsSelfAdjoint G)
    (U : Submodule ℂ N) (hU : ∀ u ∈ U, (∀ v ∈ U, ⟪v, G u⟫_ℂ = 0) → u = 0) {X : N →L[ℂ] N}
    (hX : ∀ u ∈ U, X u ∈ U) (hJX : G * X = star X * G) (Γ : H →L[ℂ] N) (hΓ : ∀ h, Γ h ∈ U)
    (u v : U) : (PontryaginRealization.compressToSub hG U hU hX hJX Γ hΓ).form u v = ⟪(u : N), G v⟫_ℂ :=
  inner_compressGram G U u v

end Compression

/-! ## The Weierstrass reduction of a finite Pontryagin realization -/

namespace PontryaginRealization

variable {H N : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup N] [InnerProductSpace ℂ N] [CompleteSpace N] [FiniteDimensional ℂ N]
variable (P : PontryaginRealization H N)

/-- The root subspace at `0` of the state operator (the infinity block). -/
abbrev infSpace : Submodule ℂ N := Module.End.maxGenEigenspace (P.A : Module.End ℂ N) 0

/-- The sum of the root subspaces at the nonzero spectral points (the finite block). -/
abbrev finSpace : Submodule ℂ N := RootProjection.rootComplement (P.A : Module.End ℂ N) 0

theorem isCompl_infSpace_finSpace : IsCompl P.infSpace P.finSpace :=
  RootProjection.isCompl_rootComplement _ _

theorem rootProjL_apply_of_mem_infSpace {x : N} (hx : x ∈ P.infSpace) : P.rootProjL x = x :=
  RootProjection.rootProj_apply_of_mem _ _ hx

theorem rootProjL_apply_of_mem_finSpace {x : N} (hx : x ∈ P.finSpace) : P.rootProjL x = 0 :=
  RootProjection.rootProj_apply_of_mem_rootComplement _ _ hx

theorem mem_finSpace_of_rootProjL_eq_zero {x : N} (hx : P.rootProjL x = 0) : x ∈ P.finSpace :=
  (RootProjection.rootProj_apply_eq_zero_iff _ _).mp hx

theorem A_apply_mem_infSpace {x : N} (hx : x ∈ P.infSpace) : P.A x ∈ P.infSpace :=
  RootProjection.apply_mem_maxGenEigenspace _ _ hx

theorem A_apply_mem_finSpace {x : N} (hx : x ∈ P.finSpace) : P.A x ∈ P.finSpace :=
  RootProjection.apply_mem_rootComplement _ _ hx

theorem A_pow_finrank_apply_of_mem_infSpace {x : N} (hx : x ∈ P.infSpace) :
    (P.A ^ finrank ℂ N) x = 0 := by
  rw [← P.rootProjL_apply_of_mem_infSpace hx]; exact P.pow_finrank_rootProjL x

theorem eq_zero_of_mem_infSpace_of_mem_finSpace {x : N} (hx : x ∈ P.infSpace)
    (hx' : x ∈ P.finSpace) : x = 0 :=
  RootProjection.eq_zero_of_mem_of_mem_rootComplement _ _ hx hx'

/-- The state operator is injective on the finite block. -/
theorem eq_zero_of_mem_finSpace_of_A_apply_eq_zero {x : N} (hx : x ∈ P.finSpace)
    (h : P.A x = 0) : x = 0 :=
  RootProjection.eq_zero_of_mem_rootComplement_of_sub_apply_eq_zero _ _ hx (by simpa using h)

theorem rootProjL_mul_rootProjL : P.rootProjL * P.rootProjL = P.rootProjL := by
  refine ContinuousLinearMap.ext fun x => ?_
  rw [mul_apply_eq_comp]; exact P.rootProjL_rootProjL x

/-- The form of `π₀ x` against `y` only sees `π₀ y`. -/
theorem form_rootProjL_left (x y : N) :
    P.form (P.rootProjL x) y = P.form (P.rootProjL x) (P.rootProjL y) := by
  rw [P.form_eq_rootProj_add (P.rootProjL x) y, P.rootProjL_rootProjL, sub_self, form_zero_left,
    add_zero]

theorem form_rootProjL_right (x y : N) :
    P.form x (P.rootProjL y) = P.form (P.rootProjL x) (P.rootProjL y) := by
  rw [P.form_eq_rootProj_add x (P.rootProjL y), P.rootProjL_rootProjL, sub_self, form_zero_right,
    add_zero]

/-- **The Riesz projection is `J`-self-adjoint.** -/
theorem J_mul_rootProjL : P.J * P.rootProjL = star P.rootProjL * P.J := by
  refine ContinuousLinearMap.ext fun y => ?_
  apply ext_inner_left ℂ
  intro x
  rw [mul_apply_eq_comp, mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]
  change P.form x (P.rootProjL y) = P.form (P.rootProjL x) y
  rw [form_rootProjL_left, form_rootProjL_right]

theorem J_mul_one_sub_rootProjL : P.J * (1 - P.rootProjL) = star (1 - P.rootProjL) * P.J := by
  rw [mul_sub, mul_one, P.J_mul_rootProjL, star_sub, star_one, sub_mul, one_mul]

variable (t₀ : ℝ)

theorem J_mul_one_add_smul :
    P.J * (1 + (t₀ : ℂ) • P.A) = star (1 + (t₀ : ℂ) • P.A) * P.J := by
  rw [mul_add, mul_one, mul_smul_comm, P.J_mul_A, star_add, star_one, star_smul, Complex.star_def,
    Complex.conj_ofReal, add_mul, one_mul, smul_mul_assoc]

theorem commute_rootProjL_A : Commute P.rootProjL P.A := P.rootProjL_comm

theorem commute_A_one_add_smul : Commute P.A (1 + (t₀ : ℂ) • P.A) :=
  (Commute.one_right _).add_right ((Commute.refl _).smul_right _)

theorem commute_rootProjL_one_add_smul : Commute P.rootProjL (1 + (t₀ : ℂ) • P.A) :=
  (Commute.one_right _).add_right (P.commute_rootProjL_A.smul_right _)

theorem commute_A_one_sub_rootProjL : Commute P.A (1 - P.rootProjL) :=
  (Commute.one_right _).sub_right P.commute_rootProjL_A.symm

/-! ### The Weierstrass multiplier -/

/-- **The Weierstrass multiplier** `M = (1 + t₀ T) π₀ + T (1 - π₀)`: it agrees with the unipotent
`1 + t₀ T` on the infinity block and with the injective `T` on the finite block. -/
def weierstrassMul : N →L[ℂ] N :=
  (1 + (t₀ : ℂ) • P.A) * P.rootProjL + P.A * (1 - P.rootProjL)

theorem weierstrassMul_mul_rootProjL :
    P.weierstrassMul t₀ * P.rootProjL = (1 + (t₀ : ℂ) • P.A) * P.rootProjL := by
  rw [weierstrassMul, add_mul, mul_assoc, P.rootProjL_mul_rootProjL, mul_assoc,
    one_sub_mul_idem P.rootProjL_mul_rootProjL, mul_zero, add_zero]

theorem weierstrassMul_mul_one_sub_rootProjL :
    P.weierstrassMul t₀ * (1 - P.rootProjL) = P.A * (1 - P.rootProjL) := by
  rw [weierstrassMul, add_mul, mul_assoc, idem_mul_one_sub P.rootProjL_mul_rootProjL, mul_zero,
    zero_add, mul_assoc, one_sub_mul_one_sub_idem P.rootProjL_mul_rootProjL]

theorem rootProjL_mul_weierstrassMul :
    P.rootProjL * P.weierstrassMul t₀ = P.weierstrassMul t₀ * P.rootProjL := by
  rw [weierstrassMul_mul_rootProjL, weierstrassMul, mul_add, ← mul_assoc,
    (P.commute_rootProjL_one_add_smul t₀).eq, mul_assoc, P.rootProjL_mul_rootProjL, ← mul_assoc,
    P.commute_rootProjL_A.eq, mul_assoc, idem_mul_one_sub P.rootProjL_mul_rootProjL, mul_zero,
    add_zero]

theorem commute_A_weierstrassMul : Commute P.A (P.weierstrassMul t₀) :=
  ((P.commute_A_one_add_smul t₀).mul_right P.commute_rootProjL_A.symm).add_right
    ((Commute.refl _).mul_right P.commute_A_one_sub_rootProjL)

/-- The Weierstrass multiplier is `J`-self-adjoint. -/
theorem J_mul_weierstrassMul :
    P.J * P.weierstrassMul t₀ = star (P.weierstrassMul t₀) * P.J := by
  have h1 := J_mul_mul_of_comm (P.J_mul_one_add_smul t₀) P.J_mul_rootProjL
    (P.commute_rootProjL_one_add_smul t₀).symm.eq
  have h2 := J_mul_mul_of_comm P.J_mul_A P.J_mul_one_sub_rootProjL
    P.commute_A_one_sub_rootProjL.eq
  rw [weierstrassMul, mul_add, h1, h2, ← add_mul, star_add]

/-- `1 + t₀ T` is injective on the infinity block (`T` is nilpotent there). -/
theorem eq_zero_of_mem_infSpace_of_one_add_smul_A_apply_eq_zero {x : N} (hx : x ∈ P.infSpace)
    (h : (1 + (t₀ : ℂ) • P.A) x = 0) : x = 0 := by
  have h1 : x = (-(t₀ : ℂ)) • P.A x := by
    rw [add_apply, one_apply_eq_self,
      smul_apply] at h
    rw [neg_smul, eq_neg_iff_add_eq_zero]; exact h
  have hk : ∀ k : ℕ, x = (-(t₀ : ℂ)) ^ k • (P.A ^ k) x := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ, pow_succ, mul_apply_eq_comp, mul_smul, ← (P.A ^ k).map_smul, ← h1]
        exact ih
  rw [hk (finrank ℂ N), P.A_pow_finrank_apply_of_mem_infSpace hx, smul_zero]

omit [CompleteSpace N] [FiniteDimensional ℂ N] in
theorem eq_zero_of_isUnit_apply_eq_zero {X : N →L[ℂ] N} (hX : IsUnit X) {x : N} (h : X x = 0) :
    x = 0 := by
  have := congrArg (fun T : N →L[ℂ] N => T x) (Ring.inverse_mul_cancel X hX)
  simp only [mul_apply_eq_comp, one_apply_eq_self, h, map_zero] at this
  exact this.symm

/-- **The Weierstrass multiplier is invertible.** -/
theorem isUnit_weierstrassMul : IsUnit (P.weierstrassMul t₀) := by
  rw [ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap, LinearMap.isUnit_iff_ker_eq_bot,
    LinearMap.ker_eq_bot']
  intro x hx
  have hx' : (1 + (t₀ : ℂ) • P.A) (P.rootProjL x) + P.A (x - P.rootProjL x) = 0 := by
    have : P.weierstrassMul t₀ x = 0 := hx
    rw [weierstrassMul, add_apply, mul_apply_eq_comp, mul_apply_eq_comp,
      sub_apply, one_apply_eq_self] at this
    exact this
  have ha : (1 + (t₀ : ℂ) • P.A) (P.rootProjL x) ∈ P.infSpace := by
    rw [add_apply, one_apply_eq_self,
      smul_apply]
    exact Submodule.add_mem _ (P.rootProjL_apply_mem x)
      (Submodule.smul_mem _ _ (P.A_apply_mem_infSpace (P.rootProjL_apply_mem x)))
  have hb : P.A (x - P.rootProjL x) ∈ P.finSpace :=
    P.A_apply_mem_finSpace (P.sub_rootProjL_mem x)
  have ha0 : (1 + (t₀ : ℂ) • P.A) (P.rootProjL x) = 0 := by
    refine P.eq_zero_of_mem_infSpace_of_mem_finSpace ha ?_
    rw [eq_neg_of_add_eq_zero_left hx']
    exact Submodule.neg_mem _ hb
  have hb0 : P.A (x - P.rootProjL x) = 0 := by rw [ha0, zero_add] at hx'; exact hx'
  have h1 : P.rootProjL x = 0 :=
    P.eq_zero_of_mem_infSpace_of_one_add_smul_A_apply_eq_zero t₀ (P.rootProjL_apply_mem x) ha0
  have h2 : x - P.rootProjL x = 0 :=
    P.eq_zero_of_mem_finSpace_of_A_apply_eq_zero (P.sub_rootProjL_mem x) hb0
  rw [h1, sub_zero] at h2
  exact h2

/-- The inverse `M⁻¹` of the Weierstrass multiplier. -/
def weierstrassInv : N →L[ℂ] N := Ring.inverse (P.weierstrassMul t₀)

theorem isUnit_weierstrassInv : IsUnit (P.weierstrassInv t₀) := by
  rw [weierstrassInv, Ring.inverse_of_isUnit (P.isUnit_weierstrassMul t₀)]
  exact Units.isUnit _

theorem weierstrassMul_mul_weierstrassInv : P.weierstrassMul t₀ * P.weierstrassInv t₀ = 1 :=
  Ring.mul_inverse_cancel _ (P.isUnit_weierstrassMul t₀)

theorem weierstrassInv_mul_weierstrassMul : P.weierstrassInv t₀ * P.weierstrassMul t₀ = 1 :=
  Ring.inverse_mul_cancel _ (P.isUnit_weierstrassMul t₀)

theorem rootProjL_mul_weierstrassInv :
    P.rootProjL * P.weierstrassInv t₀ = P.weierstrassInv t₀ * P.rootProjL :=
  (inverse_mul_comm_of_comm (P.isUnit_weierstrassMul t₀)
    (P.rootProjL_mul_weierstrassMul t₀).symm).symm

theorem one_sub_rootProjL_mul_weierstrassInv :
    (1 - P.rootProjL) * P.weierstrassInv t₀ = P.weierstrassInv t₀ * (1 - P.rootProjL) := by
  rw [sub_mul, mul_sub, one_mul, mul_one, P.rootProjL_mul_weierstrassInv]

theorem A_mul_weierstrassInv : P.A * P.weierstrassInv t₀ = P.weierstrassInv t₀ * P.A :=
  (inverse_mul_comm_of_comm (P.isUnit_weierstrassMul t₀)
    (P.commute_A_weierstrassMul t₀).symm.eq).symm

theorem commute_A_weierstrassInv : Commute P.A (P.weierstrassInv t₀) := P.A_mul_weierstrassInv t₀

theorem one_add_smul_mul_weierstrassInv :
    (1 + (t₀ : ℂ) • P.A) * P.weierstrassInv t₀ = P.weierstrassInv t₀ * (1 + (t₀ : ℂ) • P.A) :=
  (((Commute.one_right _).add_right
    ((P.commute_A_weierstrassInv t₀).symm.smul_right _)).symm).eq

/-- `M⁻¹` is `J`-self-adjoint. -/
theorem J_mul_weierstrassInv :
    P.J * P.weierstrassInv t₀ = star (P.weierstrassInv t₀) * P.J :=
  J_mul_inverse_of_J_mul (P.isUnit_weierstrassMul t₀) (P.J_mul_weierstrassMul t₀)

/-- The Gram operator `J M⁻¹` of the reduced realization is self-adjoint. -/
theorem isSelfAdjoint_J_mul_weierstrassInv : IsSelfAdjoint (P.J * P.weierstrassInv t₀) := by
  rw [IsSelfAdjoint, star_mul, P.J_selfAdjoint.star_eq, P.J_mul_weierstrassInv t₀]

theorem weierstrassInv_apply_mem_infSpace {x : N} (hx : x ∈ P.infSpace) :
    P.weierstrassInv t₀ x ∈ P.infSpace := by
  rw [← P.rootProjL_apply_of_mem_infSpace hx, ← mul_apply_eq_comp,
    ← P.rootProjL_mul_weierstrassInv t₀, mul_apply_eq_comp]
  exact P.rootProjL_apply_mem _

theorem weierstrassInv_apply_mem_finSpace {x : N} (hx : x ∈ P.finSpace) :
    P.weierstrassInv t₀ x ∈ P.finSpace := by
  apply P.mem_finSpace_of_rootProjL_eq_zero
  rw [← mul_apply_eq_comp, P.rootProjL_mul_weierstrassInv t₀, mul_apply_eq_comp,
    P.rootProjL_apply_of_mem_finSpace hx, map_zero]

/-- On the finite block `T M⁻¹ = 1`. -/
theorem A_mul_weierstrassInv_mul_one_sub_rootProjL :
    P.A * P.weierstrassInv t₀ * (1 - P.rootProjL) = 1 - P.rootProjL := by
  have h1 : P.weierstrassMul t₀ * (1 - P.rootProjL) = (1 - P.rootProjL) * P.weierstrassMul t₀ := by
    rw [mul_sub, sub_mul, mul_one, one_mul, P.rootProjL_mul_weierstrassMul]
  calc P.A * P.weierstrassInv t₀ * (1 - P.rootProjL)
      = P.A * (1 - P.rootProjL) * P.weierstrassInv t₀ := by
        rw [mul_assoc, ← P.one_sub_rootProjL_mul_weierstrassInv, ← mul_assoc]
    _ = P.weierstrassMul t₀ * (1 - P.rootProjL) * P.weierstrassInv t₀ := by
        rw [weierstrassMul_mul_one_sub_rootProjL]
    _ = (1 - P.rootProjL) * (P.weierstrassMul t₀ * P.weierstrassInv t₀) := by
        rw [h1, mul_assoc]
    _ = 1 - P.rootProjL := by rw [weierstrassMul_mul_weierstrassInv, mul_one]

/-- On the infinity block `(1 + t₀ T) M⁻¹ = 1`. -/
theorem one_add_smul_mul_weierstrassInv_mul_rootProjL :
    (1 + (t₀ : ℂ) • P.A) * P.weierstrassInv t₀ * P.rootProjL = P.rootProjL := by
  calc (1 + (t₀ : ℂ) • P.A) * P.weierstrassInv t₀ * P.rootProjL
      = (1 + (t₀ : ℂ) • P.A) * P.rootProjL * P.weierstrassInv t₀ := by
        rw [mul_assoc, ← P.rootProjL_mul_weierstrassInv, ← mul_assoc]
    _ = P.weierstrassMul t₀ * P.rootProjL * P.weierstrassInv t₀ := by
        rw [weierstrassMul_mul_rootProjL]
    _ = P.rootProjL * (P.weierstrassMul t₀ * P.weierstrassInv t₀) := by
        rw [← P.rootProjL_mul_weierstrassMul, mul_assoc]
    _ = P.rootProjL := by rw [weierstrassMul_mul_weierstrassInv, mul_one]

theorem rootProjL_mul_A_mul_weierstrassInv :
    P.rootProjL * (P.A * P.weierstrassInv t₀) = P.A * P.weierstrassInv t₀ * P.rootProjL := by
  rw [← mul_assoc, P.commute_rootProjL_A.eq, mul_assoc, P.rootProjL_mul_weierstrassInv,
    ← mul_assoc]

theorem rootProjL_mul_one_add_smul_mul_weierstrassInv :
    P.rootProjL * ((1 + (t₀ : ℂ) • P.A) * P.weierstrassInv t₀) =
      (1 + (t₀ : ℂ) • P.A) * P.weierstrassInv t₀ * P.rootProjL := by
  rw [← mul_assoc, (P.commute_rootProjL_one_add_smul t₀).eq, mul_assoc,
    P.rootProjL_mul_weierstrassInv, ← mul_assoc]

/-! ### The two blocks -/

theorem inner_J_mul_weierstrassInv (x y : N) :
    ⟪x, (P.J * P.weierstrassInv t₀) y⟫_ℂ = P.form x (P.weierstrassInv t₀ y) := by
  rw [mul_apply_eq_comp]; rfl

/-- The reduced form `J M⁻¹` is nondegenerate on the infinity block. -/
theorem nondegenerate_infSpace :
    ∀ u ∈ P.infSpace, (∀ v ∈ P.infSpace, ⟪v, (P.J * P.weierstrassInv t₀) u⟫_ℂ = 0) → u = 0 := by
  intro u hu h
  have hMu : P.weierstrassInv t₀ u ∈ P.infSpace := P.weierstrassInv_apply_mem_infSpace t₀ hu
  have hJ : (P.J * P.weierstrassInv t₀) u = 0 := by
    apply ext_inner_left ℂ
    intro x
    rw [inner_zero_right, inner_J_mul_weierstrassInv, P.form_eq_rootProj_add,
      P.rootProjL_apply_of_mem_infSpace hMu, sub_self, form_zero_right, add_zero]
    have := h (P.rootProjL x) (P.rootProjL_apply_mem x)
    rwa [inner_J_mul_weierstrassInv] at this
  exact eq_zero_of_isUnit_apply_eq_zero (P.J_isUnit.mul (P.isUnit_weierstrassInv t₀)) hJ

/-- The reduced form `J M⁻¹` is nondegenerate on the finite block. -/
theorem nondegenerate_finSpace :
    ∀ u ∈ P.finSpace, (∀ v ∈ P.finSpace, ⟪v, (P.J * P.weierstrassInv t₀) u⟫_ℂ = 0) → u = 0 := by
  intro u hu h
  have hMu : P.weierstrassInv t₀ u ∈ P.finSpace := P.weierstrassInv_apply_mem_finSpace t₀ hu
  have hJ : (P.J * P.weierstrassInv t₀) u = 0 := by
    apply ext_inner_left ℂ
    intro x
    rw [inner_zero_right, inner_J_mul_weierstrassInv, P.form_eq_rootProj_add,
      P.rootProjL_apply_of_mem_finSpace hMu, form_zero_right, zero_add, sub_zero]
    have := h (x - P.rootProjL x) (P.sub_rootProjL_mem x)
    rwa [inner_J_mul_weierstrassInv] at this
  exact eq_zero_of_isUnit_apply_eq_zero (P.J_isUnit.mul (P.isUnit_weierstrassInv t₀)) hJ

theorem A_mul_weierstrassInv_apply_mem_infSpace {u : N} (hu : u ∈ P.infSpace) :
    (P.A * P.weierstrassInv t₀) u ∈ P.infSpace := by
  rw [mul_apply_eq_comp]
  exact P.A_apply_mem_infSpace (P.weierstrassInv_apply_mem_infSpace t₀ hu)

theorem one_add_smul_mul_weierstrassInv_apply_mem_finSpace {u : N} (hu : u ∈ P.finSpace) :
    ((1 + (t₀ : ℂ) • P.A) * P.weierstrassInv t₀) u ∈ P.finSpace := by
  rw [mul_apply_eq_comp, add_apply, one_apply_eq_self,
    smul_apply]
  exact Submodule.add_mem _ (P.weierstrassInv_apply_mem_finSpace t₀ hu)
    (Submodule.smul_mem _ _ (P.A_apply_mem_finSpace (P.weierstrassInv_apply_mem_finSpace t₀ hu)))

theorem J_mul_weierstrassInv_mul_A_mul :
    P.J * P.weierstrassInv t₀ * (P.A * P.weierstrassInv t₀) =
      star (P.A * P.weierstrassInv t₀) * (P.J * P.weierstrassInv t₀) := by
  rw [weierstrassInv]
  refine J_mul_inverse_mul_of_comm ?_ ?_
  · rw [← weierstrassInv]
    exact J_mul_mul_of_comm P.J_mul_A (P.J_mul_weierstrassInv t₀) (P.A_mul_weierstrassInv t₀)
  · rw [← weierstrassInv, mul_assoc, ← mul_assoc (P.weierstrassInv t₀), ← P.A_mul_weierstrassInv,
      mul_assoc]

theorem J_mul_weierstrassInv_mul_one_add_smul_mul :
    P.J * P.weierstrassInv t₀ * ((1 + (t₀ : ℂ) • P.A) * P.weierstrassInv t₀) =
      star ((1 + (t₀ : ℂ) • P.A) * P.weierstrassInv t₀) * (P.J * P.weierstrassInv t₀) := by
  rw [weierstrassInv]
  refine J_mul_inverse_mul_of_comm ?_ ?_
  · rw [← weierstrassInv]
    exact J_mul_mul_of_comm (P.J_mul_one_add_smul t₀) (P.J_mul_weierstrassInv t₀)
      (P.one_add_smul_mul_weierstrassInv t₀)
  · rw [← weierstrassInv, mul_assoc, ← mul_assoc (P.weierstrassInv t₀),
      ← P.one_add_smul_mul_weierstrassInv, mul_assoc]

/-- **The infinity block**: the compression of `(T M⁻¹, π₀ Γ, J M⁻¹)` to the root subspace at
`0`; its state operator is nilpotent (`weierstrassInf_A_pow_finrank`). -/
def weierstrassInf : PontryaginRealization H P.infSpace :=
  compressToSub (P.isSelfAdjoint_J_mul_weierstrassInv t₀) P.infSpace (P.nondegenerate_infSpace t₀)
    (fun _ hu => P.A_mul_weierstrassInv_apply_mem_infSpace t₀ hu)
    (P.J_mul_weierstrassInv_mul_A_mul t₀) (P.rootProjL ∘L P.Γ) fun _ => P.rootProjL_apply_mem _

/-- **The finite block**: the compression of `((1 + t₀ T) M⁻¹, (1 - π₀) Γ, J M⁻¹)` to the root
complement (where `(1 + t₀ T) M⁻¹ = T⁻¹ + t₀`). -/
def weierstrassFin : PontryaginRealization H P.finSpace :=
  compressToSub (P.isSelfAdjoint_J_mul_weierstrassInv t₀) P.finSpace (P.nondegenerate_finSpace t₀)
    (fun _ hu => P.one_add_smul_mul_weierstrassInv_apply_mem_finSpace t₀ hu)
    (P.J_mul_weierstrassInv_mul_one_add_smul_mul t₀) ((1 - P.rootProjL) ∘L P.Γ) fun _ =>
      P.sub_rootProjL_mem _

theorem weierstrassInf_A_coe_apply (u : P.infSpace) :
    ((P.weierstrassInf t₀).A u : N) = (P.A * P.weierstrassInv t₀) u := rfl

theorem weierstrassInf_Γ_coe_apply (h : H) :
    ((P.weierstrassInf t₀).Γ h : N) = P.rootProjL (P.Γ h) := rfl

theorem weierstrassInf_form (u v : P.infSpace) :
    (P.weierstrassInf t₀).form u v = ⟪(u : N), (P.J * P.weierstrassInv t₀) v⟫_ℂ :=
  compress_form _ _ _ _ _ _ _ u v

theorem weierstrassFin_A_coe_apply (u : P.finSpace) :
    ((P.weierstrassFin t₀).A u : N) = ((1 + (t₀ : ℂ) • P.A) * P.weierstrassInv t₀) u := rfl

theorem weierstrassFin_Γ_coe_apply (h : H) :
    ((P.weierstrassFin t₀).Γ h : N) = P.Γ h - P.rootProjL (P.Γ h) := rfl

theorem weierstrassFin_form (u v : P.finSpace) :
    (P.weierstrassFin t₀).form u v = ⟪(u : N), (P.J * P.weierstrassInv t₀) v⟫_ℂ :=
  compress_form _ _ _ _ _ _ _ u v

omit [CompleteSpace N] in
theorem pow_apply_mem_of_apply_mem {X : N →L[ℂ] N} {U : Submodule ℂ N}
    (hX : ∀ u ∈ U, X u ∈ U) (n : ℕ) {u : N} (hu : u ∈ U) : (X ^ n) u ∈ U := by
  induction n with
  | zero => simpa using hu
  | succ n ih => rw [pow_succ', mul_apply_eq_comp]; exact hX _ ih

/-- The infinity block is nilpotent. -/
theorem weierstrassInf_A_pow_finrank : (P.weierstrassInf t₀).A ^ finrank ℂ N = 0 := by
  refine ContinuousLinearMap.ext fun u => Subtype.ext ?_
  change ((restrictL (P.A * P.weierstrassInv t₀) P.infSpace
    (fun _ hu => P.A_mul_weierstrassInv_apply_mem_infSpace t₀ hu) ^ finrank ℂ N) u : N) = 0
  rw [restrictL_pow_coe_apply, (P.commute_A_weierstrassInv t₀).mul_pow,
    mul_apply_eq_comp, P.A_pow_finrank_apply_of_mem_infSpace]
  exact pow_apply_mem_of_apply_mem (fun _ hu => P.weierstrassInv_apply_mem_infSpace t₀ hu) _ u.2

/-- **The Weierstrass primary form** of a finite Pontryagin realization at `t₀`: the direct sum of
the (nilpotent) infinity block on the root subspace at `0` and the finite block on the root
complement. -/
def weierstrassPrimary : PrimaryDescriptor H P.infSpace P.finSpace where
  inf := P.weierstrassInf t₀
  inf_nilpotent := ⟨finrank ℂ N, P.weierstrassInf_A_pow_finrank t₀⟩
  fin := P.weierstrassFin t₀

/-- The primary decomposition `x ↦ (π₀ x, x - π₀ x)` as a linear isomorphism
`N ≃ R₀ ⊕ W`. -/
def primaryEquiv : N ≃ₗ[ℂ] WithLp 2 (P.infSpace × P.finSpace) :=
  (P.infSpace.prodEquivOfIsCompl P.finSpace P.isCompl_infSpace_finSpace).symm.trans
    (WithLp.linearEquiv 2 ℂ (P.infSpace × P.finSpace)).symm

theorem primaryEquiv_apply (x : N) :
    P.primaryEquiv x = WithLp.toLp 2
      (⟨P.rootProjL x, P.rootProjL_apply_mem x⟩, ⟨x - P.rootProjL x, P.sub_rootProjL_mem x⟩) := by
  rw [primaryEquiv, LinearEquiv.trans_apply]
  have : (P.infSpace.prodEquivOfIsCompl P.finSpace P.isCompl_infSpace_finSpace).symm x =
      (⟨P.rootProjL x, P.rootProjL_apply_mem x⟩, ⟨x - P.rootProjL x, P.sub_rootProjL_mem x⟩) := by
    rw [LinearEquiv.symm_apply_eq, Submodule.coe_prodEquivOfIsCompl']
    simp
  rw [this]
  rfl

variable [FiniteDimensional ℂ H]

/-- **The reduced descriptor realization is equivalent to its Weierstrass primary form by the
source-fixing unitary `x ↦ (π₀ x, x - π₀ x)`**: any descriptor realization with pencil
`(E, A) = (T M⁻¹, (1 + t₀ T) M⁻¹)`, source `Γ` and Gram operator `J M⁻¹` is related to
`weierstrassPrimary` by `primaryEquiv`. -/
theorem isSourceFixingUnitary_primaryEquiv (D : DescriptorRealization H N)
    (hE : D.E = P.A * P.weierstrassInv t₀) (hA : D.A = (1 + (t₀ : ℂ) • P.A) * P.weierstrassInv t₀)
    (hΓ : D.Γ = P.Γ) (hJ : D.J = P.J * P.weierstrassInv t₀) :
    PrimaryDescriptor.IsSourceFixingUnitary D (P.weierstrassPrimary t₀).toDescriptor
      P.primaryEquiv := by
  refine ⟨fun h => ?_, fun x => ?_, fun x => ?_, fun x y => ?_⟩
  · rw [primaryEquiv_apply, PrimaryDescriptor.toDescriptor_Γ_apply, hΓ]
    rfl
  · rw [PrimaryDescriptor.toDescriptor_E_apply, primaryEquiv_apply, primaryEquiv_apply, hE]
    refine PrimaryDescriptor.prod_ext (Subtype.ext ?_) (Subtype.ext ?_)
    · simp only [WithLp.toLp_fst]
      change P.rootProjL ((P.A * P.weierstrassInv t₀) x) =
        (P.A * P.weierstrassInv t₀) (P.rootProjL x)
      rw [← mul_apply_eq_comp, P.rootProjL_mul_A_mul_weierstrassInv t₀, mul_apply_eq_comp]
    · simp only [WithLp.toLp_snd]
      have h1 : P.rootProjL ((P.A * P.weierstrassInv t₀) x) =
          (P.A * P.weierstrassInv t₀) (P.rootProjL x) := by
        rw [← mul_apply_eq_comp, P.rootProjL_mul_A_mul_weierstrassInv t₀, mul_apply_eq_comp]
      have h2 := congrArg (fun T : N →L[ℂ] N => T x)
        (P.A_mul_weierstrassInv_mul_one_sub_rootProjL t₀)
      simp only [mul_apply_eq_comp, sub_apply, one_apply_eq_self] at h2
      rw [h1, ← h2]
      simp only [mul_apply_eq_comp, map_sub]
  · rw [PrimaryDescriptor.toDescriptor_A_apply, primaryEquiv_apply, primaryEquiv_apply, hA]
    refine PrimaryDescriptor.prod_ext (Subtype.ext ?_) (Subtype.ext ?_)
    · simp only [WithLp.toLp_fst]
      change P.rootProjL (((1 + (t₀ : ℂ) • P.A) * P.weierstrassInv t₀) x) = P.rootProjL x
      rw [← mul_apply_eq_comp, P.rootProjL_mul_one_add_smul_mul_weierstrassInv t₀,
        P.one_add_smul_mul_weierstrassInv_mul_rootProjL t₀]
    · simp only [WithLp.toLp_snd]
      change ((1 + (t₀ : ℂ) • P.A) * P.weierstrassInv t₀) x -
          P.rootProjL (((1 + (t₀ : ℂ) • P.A) * P.weierstrassInv t₀) x) =
        ((1 + (t₀ : ℂ) • P.A) * P.weierstrassInv t₀) (x - P.rootProjL x)
      have h1 : P.rootProjL (((1 + (t₀ : ℂ) • P.A) * P.weierstrassInv t₀) x) =
          ((1 + (t₀ : ℂ) • P.A) * P.weierstrassInv t₀) (P.rootProjL x) := by
        rw [← mul_apply_eq_comp, P.rootProjL_mul_one_add_smul_mul_weierstrassInv t₀,
          mul_apply_eq_comp]
      rw [h1, map_sub]
  · rw [PrimaryDescriptor.toDescriptor_form, primaryEquiv_apply, primaryEquiv_apply]
    simp only [WithLp.toLp_fst, WithLp.toLp_snd]
    change (P.weierstrassInf t₀).form ⟨P.rootProjL x, P.rootProjL_apply_mem x⟩
        ⟨P.rootProjL y, P.rootProjL_apply_mem y⟩ +
      (P.weierstrassFin t₀).form ⟨x - P.rootProjL x, P.sub_rootProjL_mem x⟩
        ⟨y - P.rootProjL y, P.sub_rootProjL_mem y⟩ = ⟪x, D.J y⟫_ℂ
    rw [weierstrassInf_form, weierstrassFin_form, hJ]
    have hc : P.rootProjL (P.weierstrassInv t₀ y) = P.weierstrassInv t₀ (P.rootProjL y) := by
      rw [← mul_apply_eq_comp, P.rootProjL_mul_weierstrassInv t₀, mul_apply_eq_comp]
    rw [inner_J_mul_weierstrassInv, inner_J_mul_weierstrassInv, inner_J_mul_weierstrassInv,
      P.form_eq_rootProj_add x (P.weierstrassInv t₀ y), hc, map_sub]

end PontryaginRealization

/-! ## The Weierstrass primary form of a regular descriptor realization -/

namespace DescriptorRealization

variable {H N : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup N] [InnerProductSpace ℂ N] [CompleteSpace N] [FiniteDimensional ℂ N]
variable (D : DescriptorRealization H N) (t₀ : ℝ) (ht₀ : IsUnit (D.A - (t₀ : ℂ) • D.E))

/-- **The Weierstrass multiplier** `V = (A - t₀ E)⁻¹ M⁻¹` of `D` at the real regular point `t₀`
(`M` the Weierstrass multiplier of the anchored realization). -/
def weierstrassMultiplier : N →L[ℂ] N :=
  D.resolventAt t₀ * (D.anchored t₀ ht₀).weierstrassInv t₀

theorem isUnit_weierstrassMultiplier : IsUnit (D.weierstrassMultiplier t₀ ht₀) :=
  (D.isUnit_resolventAt t₀ ht₀).mul ((D.anchored t₀ ht₀).isUnit_weierstrassInv t₀)

/-- `V` is `J`-self-adjoint. -/
theorem J_mul_weierstrassMultiplier :
    D.J * D.weierstrassMultiplier t₀ ht₀ = star (D.weierstrassMultiplier t₀ ht₀) * D.J := by
  have h1 : D.J * D.resolventAt t₀ = (D.anchored t₀ ht₀).J := rfl
  calc D.J * (D.resolventAt t₀ * (D.anchored t₀ ht₀).weierstrassInv t₀)
      = (D.J * D.resolventAt t₀) * (D.anchored t₀ ht₀).weierstrassInv t₀ := (mul_assoc _ _ _).symm
    _ = star ((D.anchored t₀ ht₀).weierstrassInv t₀) * (D.J * D.resolventAt t₀) := by
        rw [h1, (D.anchored t₀ ht₀).J_mul_weierstrassInv t₀]
    _ = star ((D.anchored t₀ ht₀).weierstrassInv t₀) * star (D.resolventAt t₀) * D.J := by
        rw [D.J_mul_resolventAt t₀ ht₀, mul_assoc]
    _ = star (D.resolventAt t₀ * (D.anchored t₀ ht₀).weierstrassInv t₀) * D.J := by
        rw [star_mul]

/-- **The reduced descriptor realization** `D.rightMul V`: the right multiplication of `D` by the
Weierstrass multiplier, `(E V, A V, Γ, J V) = (T M⁻¹, (1 + t₀ T) M⁻¹, Γ, J K M⁻¹)`. -/
def weierstrassDescriptor : DescriptorRealization H N :=
  D.rightMul (D.weierstrassMultiplier t₀ ht₀) (D.isUnit_weierstrassMultiplier t₀ ht₀)
    (D.J_mul_weierstrassMultiplier t₀ ht₀)

theorem weierstrassDescriptor_E :
    (D.weierstrassDescriptor t₀ ht₀).E =
      (D.anchored t₀ ht₀).A * (D.anchored t₀ ht₀).weierstrassInv t₀ := by
  change D.E * (D.resolventAt t₀ * _) = (D.E * D.resolventAt t₀) * _
  rw [mul_assoc]

theorem weierstrassDescriptor_A :
    (D.weierstrassDescriptor t₀ ht₀).A =
      (1 + (t₀ : ℂ) • (D.anchored t₀ ht₀).A) * (D.anchored t₀ ht₀).weierstrassInv t₀ := by
  change D.A * (D.resolventAt t₀ * _) = _
  rw [← mul_assoc, D.A_mul_resolventAt t₀ ht₀]
  rfl

theorem weierstrassDescriptor_Γ : (D.weierstrassDescriptor t₀ ht₀).Γ = (D.anchored t₀ ht₀).Γ :=
  rfl

theorem weierstrassDescriptor_J :
    (D.weierstrassDescriptor t₀ ht₀).J =
      (D.anchored t₀ ht₀).J * (D.anchored t₀ ht₀).weierstrassInv t₀ := by
  change D.J * (D.resolventAt t₀ * _) = (D.J * D.resolventAt t₀) * _
  rw [mul_assoc]

/-- The reduced descriptor realization has the same transfer function as `D` at every regular
point. -/
theorem weierstrassDescriptor_transfer {z : ℂ} (hz : IsUnit (D.A - z • D.E)) :
    (D.weierstrassDescriptor t₀ ht₀).transfer z = D.transfer z :=
  D.rightMul_transfer _ _ _ hz

/-- **The Weierstrass primary form of a regular descriptor realization** at a real regular point
`t₀`: infinity block on the root subspace at `0` of `T = E (A - t₀ E)⁻¹`, finite block on its
root complement. -/
def weierstrassForm :
    PrimaryDescriptor H (D.anchored t₀ ht₀).infSpace (D.anchored t₀ ht₀).finSpace :=
  (D.anchored t₀ ht₀).weierstrassPrimary t₀

/-- **Reduction to primary form** (`cor:supp-all-rational`, "the pencil of any regular finite
descriptor realization has a primary decomposition at infinity and at finite spectral points"):
the right multiplication `D.rightMul V` of `D` by the Weierstrass multiplier is related to the
Weierstrass primary form by the source-fixing descriptor Pontryagin unitary
`x ↦ (π₀ x, x - π₀ x)`. -/
theorem isSourceFixingUnitary_weierstrass [FiniteDimensional ℂ H] :
    PrimaryDescriptor.IsSourceFixingUnitary (D.weierstrassDescriptor t₀ ht₀)
      (D.weierstrassForm t₀ ht₀).toDescriptor (D.anchored t₀ ht₀).primaryEquiv :=
  (D.anchored t₀ ht₀).isSourceFixingUnitary_primaryEquiv t₀ _ (D.weierstrassDescriptor_E t₀ ht₀)
    (D.weierstrassDescriptor_A t₀ ht₀) (D.weierstrassDescriptor_Γ t₀ ht₀)
    (D.weierstrassDescriptor_J t₀ ht₀)

end DescriptorRealization

/-! ## Source-fixing unitaries preserve the transfer function -/

namespace PrimaryDescriptor

variable {H N N' : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup N] [InnerProductSpace ℂ N] [CompleteSpace N]
  [NormedAddCommGroup N'] [InnerProductSpace ℂ N'] [CompleteSpace N']
  {D : DescriptorRealization H N} {D' : DescriptorRealization H N'} {S : N ≃ₗ[ℂ] N'}

theorem IsSourceFixingUnitary.map_pencil (hS : IsSourceFixingUnitary D D' S) (z : ℂ) (x : N) :
    S ((D.A - z • D.E) x) = (D'.A - z • D'.E) (S x) := by
  rw [sub_apply, smul_apply, map_sub, map_smul, hS.2.1, hS.2.2.1, sub_apply, smul_apply]

/-- A source-fixing unitary maps regular points to regular points. -/
theorem IsSourceFixingUnitary.isUnit_pencil [FiniteDimensional ℂ N']
    (hS : IsSourceFixingUnitary D D' S) {z : ℂ} (hz : IsUnit (D.A - z • D.E)) :
    IsUnit (D'.A - z • D'.E) := by
  rw [ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap, LinearMap.isUnit_iff_ker_eq_bot,
    LinearMap.ker_eq_bot']
  intro y hy
  have hy' : (D'.A - z • D'.E) y = 0 := hy
  obtain ⟨x, rfl⟩ := S.surjective y
  rw [← hS.map_pencil, LinearEquiv.map_eq_zero_iff] at hy'
  rw [PontryaginRealization.eq_zero_of_isUnit_apply_eq_zero hz hy', map_zero]

theorem IsSourceFixingUnitary.map_inverse_pencil (hS : IsSourceFixingUnitary D D' S) {z : ℂ}
    (hz : IsUnit (D.A - z • D.E)) (hz' : IsUnit (D'.A - z • D'.E)) (x : N) :
    S (Ring.inverse (D.A - z • D.E) x) = Ring.inverse (D'.A - z • D'.E) (S x) := by
  have h1 : (D.A - z • D.E) (Ring.inverse (D.A - z • D.E) x) = x := by
    rw [← mul_apply_eq_comp, Ring.mul_inverse_cancel _ hz, one_apply_eq_self]
  have h2 : ∀ y, Ring.inverse (D'.A - z • D'.E) ((D'.A - z • D'.E) y) = y := fun y => by
    rw [← mul_apply_eq_comp, Ring.inverse_mul_cancel _ hz', one_apply_eq_self]
  calc S (Ring.inverse (D.A - z • D.E) x)
      = Ring.inverse (D'.A - z • D'.E) ((D'.A - z • D'.E) (S (Ring.inverse (D.A - z • D.E) x))) :=
        (h2 _).symm
    _ = Ring.inverse (D'.A - z • D'.E) (S ((D.A - z • D.E) (Ring.inverse (D.A - z • D.E) x))) := by
        rw [hS.map_pencil]
    _ = Ring.inverse (D'.A - z • D'.E) (S x) := by rw [h1]

/-- **A source-fixing descriptor unitary preserves the transfer function** at every common
regular point. -/
theorem IsSourceFixingUnitary.transfer_eq (hS : IsSourceFixingUnitary D D' S) {z : ℂ}
    (hz : IsUnit (D.A - z • D.E)) (hz' : IsUnit (D'.A - z • D'.E)) :
    D.transfer z = D'.transfer z := by
  ext h
  apply ext_inner_left ℂ
  intro h'
  simp only [DescriptorRealization.transfer, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right]
  change D.form (D.Γ h') (Ring.inverse (D.A - z • D.E) (D.Γ h)) =
    D'.form (D'.Γ h') (Ring.inverse (D'.A - z • D'.E) (D'.Γ h))
  rw [← hS.2.2.2, hS.1, hS.map_inverse_pencil hz hz', hS.1]

end PrimaryDescriptor

/-! ## Minimality of general descriptor realizations -/

namespace DescriptorRealization

variable {H N : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup N] [InnerProductSpace ℂ N] [CompleteSpace N]
variable (D : DescriptorRealization H N)

/-- The resolvent-source vectors `(A - z E)⁻¹ Γ h` over the regular points `z`. -/
def resolventSourceSet : Set N :=
  {x | ∃ (z : ℂ) (h : H), IsUnit (D.A - z • D.E) ∧ x = Ring.inverse (D.A - z • D.E) (D.Γ h)}

/-- The span of the resolvent-source vectors over the regular points. -/
def resolventSourceSpan : Submodule ℂ N := Submodule.span ℂ D.resolventSourceSet

/-- **Source minimality of a descriptor realization** (`cor:supp-all-rational`,
`thm:supp-complete-rational-Krein`): the resolvent-source vectors `(A - z E)⁻¹ Γ h` over the
regular points span the state space. -/
def IsMinimal : Prop := D.resolventSourceSpan = ⊤

theorem inverse_pencil_apply_mem_resolventSourceSpan {z : ℂ} (hz : IsUnit (D.A - z • D.E))
    (h : H) : Ring.inverse (D.A - z • D.E) (D.Γ h) ∈ D.resolventSourceSpan :=
  Submodule.subset_span ⟨z, h, hz, rfl⟩

theorem resolventSourceSpan_le_of_forall {Q : Submodule ℂ N}
    (hQ : ∀ (z : ℂ) (h : H), IsUnit (D.A - z • D.E) → Ring.inverse (D.A - z • D.E) (D.Γ h) ∈ Q) :
    D.resolventSourceSpan ≤ Q := by
  refine Submodule.span_le.mpr ?_
  rintro x ⟨z, h, hz, rfl⟩
  exact hQ z h hz

variable (V : N →L[ℂ] N) (hV : IsUnit V) (hJV : D.J * V = star V * D.J)

theorem isUnit_rightMul_pencil_iff (z : ℂ) :
    IsUnit ((D.rightMul V hV hJV).A - z • (D.rightMul V hV hJV).E) ↔ IsUnit (D.A - z • D.E) := by
  rw [rightMul_pencil]
  constructor
  · intro h
    have hVi : IsUnit (Ring.inverse V) := by
      rw [Ring.inverse_of_isUnit hV]; exact Units.isUnit _
    have : D.A - z • D.E = (D.A - z • D.E) * V * Ring.inverse V := by
      rw [mul_assoc, Ring.mul_inverse_cancel V hV, mul_one]
    rw [this]; exact h.mul hVi
  · intro h; exact h.mul hV

theorem rightMul_inverse_pencil {z : ℂ} (hz : IsUnit (D.A - z • D.E)) :
    Ring.inverse ((D.rightMul V hV hJV).A - z • (D.rightMul V hV hJV).E) =
      Ring.inverse V * Ring.inverse (D.A - z • D.E) := by
  rw [rightMul_pencil, inverse_mul_of_isUnit hz hV]

theorem resolventSourceSet_rightMul :
    (D.rightMul V hV hJV).resolventSourceSet =
      ((Ring.inverse V : N →L[ℂ] N) : N → N) '' D.resolventSourceSet := by
  ext x
  constructor
  · rintro ⟨z, h, hz, rfl⟩
    have hz' := (D.isUnit_rightMul_pencil_iff V hV hJV z).mp hz
    refine ⟨Ring.inverse (D.A - z • D.E) (D.Γ h), ⟨z, h, hz', rfl⟩, ?_⟩
    rw [D.rightMul_inverse_pencil V hV hJV hz', mul_apply_eq_comp]
    rfl
  · rintro ⟨_, ⟨z, h, hz, rfl⟩, rfl⟩
    refine ⟨z, h, (D.isUnit_rightMul_pencil_iff V hV hJV z).mpr hz, ?_⟩
    rw [D.rightMul_inverse_pencil V hV hJV hz, mul_apply_eq_comp]
    rfl

theorem resolventSourceSpan_rightMul :
    (D.rightMul V hV hJV).resolventSourceSpan =
      D.resolventSourceSpan.map (↑(Ring.inverse V : N →L[ℂ] N) : N →ₗ[ℂ] N) := by
  rw [resolventSourceSpan, resolventSourceSet_rightMul, resolventSourceSpan, Submodule.map_span]
  rfl

/-- **Right multiplication transports minimality.** -/
theorem isMinimal_rightMul_iff : (D.rightMul V hV hJV).IsMinimal ↔ D.IsMinimal := by
  have hVi : IsUnit (Ring.inverse V) := by
    rw [Ring.inverse_of_isUnit hV]; exact Units.isUnit _
  have hbij : Function.Bijective (↑(Ring.inverse V : N →L[ℂ] N) : N →ₗ[ℂ] N) :=
    (Module.End.isUnit_iff _).mp (ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap.mp hVi)
  rw [IsMinimal, IsMinimal, resolventSourceSpan_rightMul]
  constructor
  · intro h
    have := congrArg (Submodule.comap (↑(Ring.inverse V : N →L[ℂ] N) : N →ₗ[ℂ] N)) h
    rwa [Submodule.comap_map_eq_of_injective hbij.1, Submodule.comap_top] at this
  · intro h
    rw [h, Submodule.map_top, LinearMap.range_eq_top.mpr hbij.2]

end DescriptorRealization

namespace PrimaryDescriptor

variable {H N N' : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup N] [InnerProductSpace ℂ N] [CompleteSpace N]
  [NormedAddCommGroup N'] [InnerProductSpace ℂ N'] [CompleteSpace N'] [FiniteDimensional ℂ N']
  {D : DescriptorRealization H N} {D' : DescriptorRealization H N'} {S : N ≃ₗ[ℂ] N'}

theorem IsSourceFixingUnitary.map_resolventSourceSpan_le (hS : IsSourceFixingUnitary D D' S) :
    D.resolventSourceSpan.map (S : N →ₗ[ℂ] N') ≤ D'.resolventSourceSpan := by
  rw [DescriptorRealization.resolventSourceSpan, Submodule.map_span_le]
  rintro x ⟨z, h, hz, rfl⟩
  rw [LinearEquiv.coe_coe, hS.map_inverse_pencil hz (hS.isUnit_pencil hz), hS.1]
  exact D'.inverse_pencil_apply_mem_resolventSourceSpan (hS.isUnit_pencil hz) h

/-- **Source-fixing unitaries transport minimality.** -/
theorem IsSourceFixingUnitary.isMinimal (hS : IsSourceFixingUnitary D D' S) (hD : D.IsMinimal) :
    D'.IsMinimal := by
  refine top_unique (le_trans ?_ hS.map_resolventSourceSpan_le)
  rw [hD, Submodule.map_top, LinearEquiv.range]

end PrimaryDescriptor

/-! ## Minimality in primary form: the resolvent-source span of a direct sum -/

namespace PontryaginRealization

variable {H N : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup N] [InnerProductSpace ℂ N] [CompleteSpace N] [FiniteDimensional ℂ N]
variable (P : PontryaginRealization H N)

/-- The source vectors lie in the resolvent-source span over a real ray `t ≥ t₀` to infinity
(limit `-t (A - t)⁻¹ Γ h → Γ h`). -/
theorem Γ_mem_resolventSourceSpan_real {D : Set ℂ} (t₀ : ℝ) (ht₀ : ‖P.A‖ < t₀)
    (hD : ∀ t : ℝ, t₀ ≤ t → (t : ℂ) ∈ D) (h : H) : P.Γ h ∈ P.resolventSourceSpan D := by
  set w : ℕ → ℂ := fun k => (((k : ℝ) + t₀ : ℝ) : ℂ) with hw
  have hpos : ∀ k : ℕ, 0 ≤ (k : ℝ) + t₀ := fun k => by
    have := norm_nonneg P.A
    have := Nat.cast_nonneg (α := ℝ) k
    linarith
  have hnorm : ∀ k : ℕ, ‖w k‖ = (k : ℝ) + t₀ := by
    intro k
    show ‖(((k : ℝ) + t₀ : ℝ) : ℂ)‖ = (k : ℝ) + t₀
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hpos k)]
  have hwD : ∀ k, w k ∈ D := fun k => hD _ (by
    have := Nat.cast_nonneg (α := ℝ) k
    linarith)
  have htend_norm : Tendsto (fun k => ‖w k‖) atTop atTop := by
    simp_rw [hnorm]
    exact tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hop := tendsto_neg_smul_inverse_sub_algebraMap P.A norm_one_le w htend_norm
  have hev := ((ContinuousLinearMap.apply ℂ N (P.Γ h)).continuous.tendsto _).comp hop
  have htend : Tendsto (fun k => (-(w k)) • P.resolventSource (w k) h) atTop (𝓝 (P.Γ h)) := by
    refine hev.congr ?_
    intro k
    simp [resolventSource]
  have hmem : ∀ k, (-(w k)) • P.resolventSource (w k) h ∈ P.resolventSourceSpan D :=
    fun k => Submodule.smul_mem _ _ (P.resolventSource_mem_span (hwD k) h)
  exact (Submodule.closed_of_finiteDimensional (P.resolventSourceSpan D)).mem_of_tendsto htend
    (Eventually.of_forall hmem)

/-- The real ray `{t : t₀ ≤ t}` as a set of spectral parameters. -/
def realRay (t₀ : ℝ) : Set ℂ := {w | ∃ t : ℝ, t₀ ≤ t ∧ w = t}

/-- For a source-cyclic realization the resolvent-source vectors over a real ray beyond `‖A‖`
span the state space. -/
theorem resolventSourceSpan_realRay_eq_top (hcyc : P.IsCyclic) (t₀ : ℝ) (ht₀ : ‖P.A‖ < t₀) :
    P.resolventSourceSpan (realRay t₀) = ⊤ := by
  refine P.resolventSourceSpan_eq_top hcyc ?_ ?_
  · rintro _ ⟨t, ht, rfl⟩
    have ht0 : 0 < t := lt_of_le_of_lt (norm_nonneg _) (lt_of_lt_of_le ht₀ ht)
    exact P.isUnit_sub_algebraMap_ofReal ht0 (lt_of_lt_of_le ht₀ ht)
  · exact P.Γ_mem_resolventSourceSpan_real t₀ ht₀ fun t ht => ⟨t, ht, rfl⟩

omit [CompleteSpace N] in
/-- An invariant subspace of an invertible operator is invariant under the inverse. -/
theorem mem_of_isUnit_of_inverse_apply_mem {X : N →L[ℂ] N} (hX : IsUnit X) {C : Submodule ℂ N}
    (hC : ∀ c ∈ C, X c ∈ C) {c : N} (hc : c ∈ C) : Ring.inverse X c ∈ C := by
  let f : C →ₗ[ℂ] C := (X : N →ₗ[ℂ] N).restrict fun c hc => hC c hc
  have hinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    have h1 : X a = X b := congrArg Subtype.val hab
    have h0 : X ((a : N) - b) = 0 := by rw [map_sub, h1, sub_self]
    exact sub_eq_zero.mp (eq_zero_of_isUnit_apply_eq_zero hX h0)
  obtain ⟨⟨c', hc'⟩, hcc⟩ := LinearMap.injective_iff_surjective.mp hinj ⟨c, hc⟩
  have hXc : X c' = c := congrArg Subtype.val hcc
  rw [← hXc, ← mul_apply_eq_comp, Ring.inverse_mul_cancel X hX, one_apply_eq_self]
  exact hc'

end PontryaginRealization

namespace PrimaryDescriptor

variable {H Ninf Nfin : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup Ninf] [InnerProductSpace ℂ Ninf] [CompleteSpace Ninf]
  [NormedAddCommGroup Nfin] [InnerProductSpace ℂ Nfin] [CompleteSpace Nfin]
variable [FiniteDimensional ℂ H] [FiniteDimensional ℂ Ninf] [FiniteDimensional ℂ Nfin]
variable (R : PrimaryDescriptor H Ninf Nfin)

/-- The pencil of a primary form is block diagonal: `(1 - z A_∞) ⊕ (A_fin - z)`. -/
theorem toDescriptor_pencil (z : ℂ) :
    R.toDescriptor.A - z • R.toDescriptor.E =
      L2Prod.blockDiag (1 - z • R.inf.A) (R.fin.A - algebraMap ℂ (Nfin →L[ℂ] Nfin) z) := by
  change L2Prod.blockDiag 1 R.fin.A - z • L2Prod.blockDiag R.inf.A 1 = _
  rw [L2Prod.blockDiag_smul, L2Prod.blockDiag_sub, Algebra.algebraMap_eq_smul_one]

theorem isUnit_toDescriptor_pencil_of_norm_lt {z : ℂ} (hz : ‖R.fin.A‖ < ‖z‖) :
    IsUnit (R.toDescriptor.A - z • R.toDescriptor.E) := by
  obtain ⟨n, hn⟩ := R.inf_nilpotent
  rw [toDescriptor_pencil]
  exact L2Prod.isUnit_blockDiag _ _ (R.inf.isUnit_infinityChainOf_pencil hn z)
    (isUnit_sub_algebraMap_of_norm_lt _ hz)

/-- At a regular point of a primary form the finite block is regular. -/
theorem isUnit_fin_pencil_of_isUnit {z : ℂ}
    (hz : IsUnit (R.toDescriptor.A - z • R.toDescriptor.E)) :
    IsUnit (R.fin.A - algebraMap ℂ (Nfin →L[ℂ] Nfin) z) := by
  rw [toDescriptor_pencil] at hz
  rw [ContinuousLinearMap.isUnit_iff_isUnit_toLinearMap, LinearMap.isUnit_iff_ker_eq_bot,
    LinearMap.ker_eq_bot']
  intro b hb
  have hb' : (R.fin.A - algebraMap ℂ (Nfin →L[ℂ] Nfin) z) b = 0 := hb
  have h0 : L2Prod.blockDiag (1 - z • R.inf.A) (R.fin.A - algebraMap ℂ (Nfin →L[ℂ] Nfin) z)
      (WithLp.toLp 2 (0, b)) = 0 := by
    rw [L2Prod.blockDiag_apply]
    simp only [WithLp.toLp_fst, WithLp.toLp_snd, map_zero, hb']
    rfl
  have := congrArg WithLp.snd (PontryaginRealization.eq_zero_of_isUnit_apply_eq_zero hz h0)
  simpa using this

/-- The resolvent-source vectors of a primary form are the pairs of the block resolvent-source
vectors. -/
theorem inverse_pencil_Γ_apply {z : ℂ} (hz : IsUnit (R.toDescriptor.A - z • R.toDescriptor.E))
    (h : H) :
    Ring.inverse (R.toDescriptor.A - z • R.toDescriptor.E) (R.toDescriptor.Γ h) =
      WithLp.toLp 2 (Ring.inverse (1 - z • R.inf.A) (R.inf.Γ h), R.fin.resolventSource z h) := by
  obtain ⟨n, hn⟩ := R.inf_nilpotent
  have h1 : IsUnit (1 - z • R.inf.A) := R.inf.isUnit_infinityChainOf_pencil hn z
  have h2 := R.isUnit_fin_pencil_of_isUnit hz
  rw [toDescriptor_pencil, L2Prod.inverse_blockDiag _ _ h1 h2, toDescriptor_Γ_apply,
    L2Prod.blockDiag_apply]
  rfl

/-- The inclusion of the infinity block. -/
def inlL : Ninf →ₗ[ℂ] WithLp 2 (Ninf × Nfin) :=
  (WithLp.linearEquiv 2 ℂ (Ninf × Nfin)).symm ∘ₗ LinearMap.inl ℂ Ninf Nfin

/-- The inclusion of the finite block. -/
def inrL : Nfin →ₗ[ℂ] WithLp 2 (Ninf × Nfin) :=
  (WithLp.linearEquiv 2 ℂ (Ninf × Nfin)).symm ∘ₗ LinearMap.inr ℂ Ninf Nfin

theorem inlL_apply (a : Ninf) : (inlL a : WithLp 2 (Ninf × Nfin)) = WithLp.toLp 2 (a, 0) := rfl

theorem inrL_apply (b : Nfin) : (inrL b : WithLp 2 (Ninf × Nfin)) = WithLp.toLp 2 (0, b) := rfl

theorem toLp_eq_inlL_add_inrL (a : Ninf) (b : Nfin) :
    WithLp.toLp 2 (a, b) = (inlL a : WithLp 2 (Ninf × Nfin)) + inrL b := by
  rw [inlL_apply, inrL_apply, toLp_add_toLp]

/-- **The polynomial part of the resolvent-source vectors of a primary form** (the Laurent
argument): every power-cyclic vector `(A_∞^k Γ_∞ h, 0)` of the infinity block lies in the
resolvent-source span (a functional vanishing on the span kills the vector polynomial part of
`(A - t E)⁻¹ Γ h` as `t → ∞`, `coeff_eq_zero_of_tendsto_zero`). -/
theorem inlL_A_pow_Γ_mem_resolventSourceSpan (k : ℕ) (h : H) :
    (inlL ((R.inf.A ^ k) (R.inf.Γ h)) : WithLp 2 (Ninf × Nfin)) ∈
      R.toDescriptor.resolventSourceSpan := by
  obtain ⟨n, hn⟩ := R.inf_nilpotent
  by_cases hk : n ≤ k
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
    rw [pow_add, hn, zero_mul]
    simp
  rw [not_le] at hk
  by_contra hnot
  obtain ⟨ℓ, hℓx, hℓS⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
  have hℓ0 : ∀ y ∈ R.toDescriptor.resolventSourceSpan, ℓ y = 0 := fun y hy => by
    have : ℓ y ∈ R.toDescriptor.resolventSourceSpan.map ℓ := Submodule.mem_map_of_mem hy
    rw [hℓS] at this
    exact (Submodule.mem_bot ℂ).mp this
  have hev : ∀ᶠ t : ℝ in atTop,
      ∑ j ∈ Finset.range n, ((t : ℂ) ^ j) • ℓ (inlL ((R.inf.A ^ j) (R.inf.Γ h))) =
        -ℓ (inrL (R.fin.resolventSource t h)) := by
    filter_upwards [eventually_gt_atTop ‖R.fin.A‖, eventually_gt_atTop (0 : ℝ)] with t ht ht0
    have hz : IsUnit (R.toDescriptor.A - (t : ℂ) • R.toDescriptor.E) :=
      R.isUnit_toDescriptor_pencil_of_norm_lt
        (by rwa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0])
    have hgen := hℓ0 _ (R.toDescriptor.inverse_pencil_apply_mem_resolventSourceSpan hz h)
    rw [R.inverse_pencil_Γ_apply hz, toLp_eq_inlL_add_inrL, map_add,
      R.inf.inverse_one_sub_smul_of_pow_eq_zero hn, sum_apply, map_sum, map_sum] at hgen
    rw [eq_neg_iff_add_eq_zero, ← hgen]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_apply, map_smul, map_smul]
  have hlim : Tendsto (fun t : ℝ =>
      ∑ j ∈ Finset.range n, ((t : ℂ) ^ j) • ℓ (inlL ((R.inf.A ^ j) (R.inf.Γ h)))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => R.fin.resolventSource t h) atTop (𝓝 0) := by
      have := ((ContinuousLinearMap.apply ℂ Nfin (R.fin.Γ h)).continuous.tendsto _).comp
        (tendsto_inverse_sub_algebraMap (R := Nfin →L[ℂ] Nfin) R.fin.A)
      simpa [Function.comp_def, PontryaginRealization.resolventSource] using this
    have h2 : Tendsto (fun t : ℝ => -ℓ (inrL (R.fin.resolventSource t h))) atTop
        (𝓝 (-ℓ (inrL (0 : Nfin)))) :=
      (((LinearMap.continuous_of_finiteDimensional ℓ).tendsto _).comp
        (((LinearMap.continuous_of_finiteDimensional
          (inrL : Nfin →ₗ[ℂ] WithLp 2 (Ninf × Nfin))).tendsto _).comp h1)).neg
    rw [map_zero, map_zero, neg_zero] at h2
    exact h2.congr' (hev.mono fun t ht => ht.symm)
  exact hℓx (coeff_eq_zero_of_tendsto_zero n _ hlim k hk)

/-- **Minimality of the blocks implies minimality of the primary form** (`cor:supp-all-rational`,
"in finite dimension the resolvent-source span equals the power-cyclic span"): if both blocks are
source-cyclic, the resolvent-source vectors of the direct sum span the whole state space. -/
theorem toDescriptor_isMinimal_of_isMinimal (hR : R.IsMinimal) : R.toDescriptor.IsMinimal := by
  set S := R.toDescriptor.resolventSourceSpan with hS
  have hinl : ∀ a : Ninf, (inlL a : WithLp 2 (Ninf × Nfin)) ∈ S := by
    intro a
    have hle : Submodule.span ℂ (Set.range fun p : ℕ × H => (R.inf.A ^ p.1) (R.inf.Γ p.2)) ≤
        S.comap (inlL : Ninf →ₗ[ℂ] WithLp 2 (Ninf × Nfin)) := by
      rw [Submodule.span_le]
      rintro _ ⟨⟨k, h⟩, rfl⟩
      exact R.inlL_A_pow_Γ_mem_resolventSourceSpan k h
    have ha : a ∈ Submodule.span ℂ (Set.range fun p : ℕ × H => (R.inf.A ^ p.1) (R.inf.Γ p.2)) := by
      rw [hR.1]; exact Submodule.mem_top
    exact hle ha
  obtain ⟨t₁, ht₁⟩ := exists_gt ‖R.fin.A‖
  have hinr_gen : ∀ w ∈ PontryaginRealization.realRay t₁, ∀ h : H,
      (inrL (R.fin.resolventSource w h) : WithLp 2 (Ninf × Nfin)) ∈ S := by
    rintro _ ⟨t, ht, rfl⟩ h
    have ht0 : 0 < t := lt_of_le_of_lt (norm_nonneg _) (lt_of_lt_of_le ht₁ ht)
    have hz : IsUnit (R.toDescriptor.A - (t : ℂ) • R.toDescriptor.E) :=
      R.isUnit_toDescriptor_pencil_of_norm_lt
        (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]; linarith)
    have hgen := R.toDescriptor.inverse_pencil_apply_mem_resolventSourceSpan hz h
    rw [R.inverse_pencil_Γ_apply hz, toLp_eq_inlL_add_inrL] at hgen
    have := S.sub_mem hgen (hinl (Ring.inverse (1 - (t : ℂ) • R.inf.A) (R.inf.Γ h)))
    rwa [add_sub_cancel_left] at this
  have hinr : ∀ b : Nfin, (inrL b : WithLp 2 (Ninf × Nfin)) ∈ S := by
    intro b
    have htop := R.fin.resolventSourceSpan_realRay_eq_top hR.2 t₁ ht₁
    have hle : R.fin.resolventSourceSpan (PontryaginRealization.realRay t₁) ≤
        S.comap (inrL : Nfin →ₗ[ℂ] WithLp 2 (Ninf × Nfin)) := by
      rw [PontryaginRealization.resolventSourceSpan, Submodule.span_le]
      rintro _ ⟨⟨⟨w, hw⟩, h⟩, rfl⟩
      exact hinr_gen w hw h
    rw [htop] at hle
    exact hle Submodule.mem_top
  refine top_unique fun x _ => ?_
  have hx : x = inlL x.fst + inrL x.snd := by
    rw [inlL_apply, inrL_apply, ← toLp_add_toLp]
    rfl
  rw [hx]
  exact S.add_mem (hinl _) (hinr _)

/-- **Minimality of the primary form implies minimality of the blocks**: the resolvent-source
vectors of the direct sum lie in the product of the power-cyclic spans of the blocks. -/
theorem isMinimal_of_toDescriptor_isMinimal (hR : R.toDescriptor.IsMinimal) : R.IsMinimal := by
  obtain ⟨n, hn⟩ := R.inf_nilpotent
  set Cinf := Submodule.span ℂ (Set.range fun p : ℕ × H => (R.inf.A ^ p.1) (R.inf.Γ p.2)) with hCinf
  set Cfin := Submodule.span ℂ (Set.range fun p : ℕ × H => (R.fin.A ^ p.1) (R.fin.Γ p.2)) with hCfin
  let Q : Submodule ℂ (WithLp 2 (Ninf × Nfin)) := (Cinf.prod Cfin).comap
    (WithLp.linearEquiv 2 ℂ (Ninf × Nfin) : WithLp 2 (Ninf × Nfin) →ₗ[ℂ] Ninf × Nfin)
  have hQ : ∀ x : WithLp 2 (Ninf × Nfin), x ∈ Q ↔ x.fst ∈ Cinf ∧ x.snd ∈ Cfin := fun x =>
    Iff.rfl
  have hCfin_inv : ∀ c ∈ Cfin, R.fin.A c ∈ Cfin := by
    intro c hc
    induction hc using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨⟨k, h⟩, rfl⟩ := hx
        exact Submodule.subset_span ⟨(k + 1, h), by simp [pow_succ', mul_apply_eq_comp]⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx
  have hle : R.toDescriptor.resolventSourceSpan ≤ Q := by
    refine R.toDescriptor.resolventSourceSpan_le_of_forall fun z h hz => ?_
    rw [R.inverse_pencil_Γ_apply hz, hQ]
    simp only [WithLp.toLp_fst, WithLp.toLp_snd]
    constructor
    · rw [R.inf.inverse_one_sub_smul_of_pow_eq_zero hn, sum_apply]
      refine Submodule.sum_mem _ fun k _ => ?_
      rw [smul_apply]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(k, h), rfl⟩)
    · have hfin := R.isUnit_fin_pencil_of_isUnit hz
      refine PontryaginRealization.mem_of_isUnit_of_inverse_apply_mem hfin (fun c hc => ?_)
        (Submodule.subset_span ⟨(0, h), by simp⟩)
      rw [sub_apply, Algebra.algebraMap_eq_smul_one, smul_apply, one_apply_eq_self]
      exact Submodule.sub_mem _ (hCfin_inv c hc) (Submodule.smul_mem _ _ hc)
  rw [hR] at hle
  constructor
  · refine top_unique fun a _ => ?_
    have ha : WithLp.toLp 2 (a, 0) ∈ (⊤ : Submodule ℂ (WithLp 2 (Ninf × Nfin))) :=
      Submodule.mem_top
    exact ((hQ _).mp (hle ha)).1
  · refine top_unique fun b _ => ?_
    have hb : WithLp.toLp 2 (0, b) ∈ (⊤ : Submodule ℂ (WithLp 2 (Ninf × Nfin))) :=
      Submodule.mem_top
    exact ((hQ _).mp (hle hb)).2

/-- **Minimality of a primary form is minimality of both blocks.** -/
theorem toDescriptor_isMinimal_iff : R.toDescriptor.IsMinimal ↔ R.IsMinimal :=
  ⟨R.isMinimal_of_toDescriptor_isMinimal, R.toDescriptor_isMinimal_of_isMinimal⟩

end PrimaryDescriptor

/-! ## `cor:supp-all-rational`: the equivalence -/

namespace PrimaryDescriptor

variable {H N N' : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup N] [InnerProductSpace ℂ N] [CompleteSpace N]
  [NormedAddCommGroup N'] [InnerProductSpace ℂ N'] [CompleteSpace N']
  {D : DescriptorRealization H N} {D' : DescriptorRealization H N'} {S : N ≃ₗ[ℂ] N'}

/-- The inverse of a source-fixing descriptor unitary is a source-fixing descriptor unitary. -/
theorem IsSourceFixingUnitary.symm (hS : IsSourceFixingUnitary D D' S) :
    IsSourceFixingUnitary D' D S.symm := by
  refine ⟨fun h => ?_, fun y => ?_, fun y => ?_, fun x y => ?_⟩
  · rw [← hS.1, S.symm_apply_apply]
  · conv_lhs => rw [← S.apply_symm_apply y]
    rw [← hS.2.1, S.symm_apply_apply]
  · conv_lhs => rw [← S.apply_symm_apply y]
    rw [← hS.2.2.1, S.symm_apply_apply]
  · rw [← hS.2.2.2, S.apply_symm_apply, S.apply_symm_apply]

end PrimaryDescriptor

namespace DescriptorRealization

variable {H N : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup N] [InnerProductSpace ℂ N] [CompleteSpace N] [FiniteDimensional ℂ N]
variable (D : DescriptorRealization H N)

/-- **A regular pencil is regular at every sufficiently large real point** (the determinant
polynomial has finitely many roots). -/
theorem eventually_isUnit_pencil_ofReal : ∀ᶠ t : ℝ in atTop, IsUnit (D.A - (t : ℂ) • D.E) := by
  obtain ⟨z₀, hz₀⟩ := D.regular
  have hp : pencilPolynomial D.E D.A ≠ 0 := fun h => by
    have := (isUnit_pencil_iff D.E D.A z₀).mp hz₀
    rw [h, Polynomial.eval_zero] at this
    exact this rfl
  filter_upwards [eventually_gt_atTop
    (∑ r ∈ (pencilPolynomial D.E D.A).roots.toFinset, ‖r‖)] with t ht
  rw [isUnit_pencil_iff]
  intro h0
  have hmem : (t : ℂ) ∈ (pencilPolynomial D.E D.A).roots.toFinset := by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hp]
    exact h0
  have hle : ‖(t : ℂ)‖ ≤ ∑ r ∈ (pencilPolynomial D.E D.A).roots.toFinset, ‖r‖ :=
    Finset.single_le_sum (fun r _ => norm_nonneg r) hmem
  have ht0 : 0 ≤ t := le_trans (Finset.sum_nonneg fun r _ => norm_nonneg r) ht.le
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0] at hle
  linarith

variable (t₀ : ℝ) (ht₀ : IsUnit (D.A - (t₀ : ℂ) • D.E))

theorem isUnit_weierstrassDescriptor_pencil {z : ℂ} (hz : IsUnit (D.A - z • D.E)) :
    IsUnit ((D.weierstrassDescriptor t₀ ht₀).A - z • (D.weierstrassDescriptor t₀ ht₀).E) :=
  (D.isUnit_rightMul_pencil_iff _ _ _ z).mpr hz

variable [FiniteDimensional ℂ H]

/-- **The Weierstrass primary form has the same transfer function as `D`** at every regular
point of `D`. -/
theorem weierstrassForm_transfer {z : ℂ} (hz : IsUnit (D.A - z • D.E)) :
    (D.weierstrassForm t₀ ht₀).toDescriptor.transfer z = D.transfer z := by
  have hS := D.isSourceFixingUnitary_weierstrass t₀ ht₀
  have hz' := D.isUnit_weierstrassDescriptor_pencil t₀ ht₀ hz
  rw [← hS.transfer_eq hz' (hS.isUnit_pencil hz'), D.weierstrassDescriptor_transfer t₀ ht₀ hz]

/-- **Minimality is equivalent to minimality of the Weierstrass primary form** (both blocks
source-cyclic). -/
theorem isMinimal_iff_weierstrassForm_isMinimal :
    D.IsMinimal ↔ (D.weierstrassForm t₀ ht₀).IsMinimal := by
  constructor
  · intro hD
    exact (D.weierstrassForm t₀ ht₀).isMinimal_of_toDescriptor_isMinimal
      ((D.isSourceFixingUnitary_weierstrass t₀ ht₀).isMinimal
        ((D.isMinimal_rightMul_iff _ _ _).mpr hD))
  · intro hR
    exact (D.isMinimal_rightMul_iff _ _ _).mp
      ((D.isSourceFixingUnitary_weierstrass t₀ ht₀).symm.isMinimal
        ((D.weierstrassForm t₀ ht₀).toDescriptor_isMinimal_of_isMinimal hR))

theorem weierstrassForm_isMinimal (hD : D.IsMinimal) : (D.weierstrassForm t₀ ht₀).IsMinimal :=
  (D.isMinimal_iff_weierstrassForm_isMinimal t₀ ht₀).mp hD

/-- **The finite rational Hermitian dynamic function of a regular descriptor realization**: the
jet and strictly proper Laurent data of its Weierstrass primary form at `t₀`
(`cor:supp-all-rational`, direction "minimal regular Pontryagin descriptor realization ↦ finite
rational Hermitian dynamic function"; the coefficients do not depend on `t₀`, by
`toData_coeff_eq_of_transfer_eventuallyEq`). -/
def toData : FiniteRationalHermitianData H := (D.weierstrassForm t₀ ht₀).toData

/-- `D.toData` is the dynamic function of `D`: `Q(t) = Γ* J (A - t E)⁻¹ Γ` for all large real
`t`. -/
theorem eventually_toData_toFun_eq_transfer :
    ∀ᶠ t : ℝ in atTop, (D.toData t₀ ht₀).toFun t = D.transfer t := by
  filter_upwards [(D.weierstrassForm t₀ ht₀).eventually_toData_toFun_eq_transfer,
    D.eventually_isUnit_pencil_ofReal] with t h1 h2
  rw [toData, h1, D.weierstrassForm_transfer t₀ ht₀ h2]

/-- The dynamic function of `D` is determined by its transfer function near infinity
(`eq:supp-rational-split`, uniqueness of the split). -/
theorem toData_coeff_eq_of_transfer_eventuallyEq (Q : FiniteRationalHermitianData H)
    (h : ∀ᶠ t : ℝ in atTop, D.transfer t = Q.toFun t) :
    (∀ k, (D.toData t₀ ht₀).jet.coeff k = Q.jet.coeff k) ∧
      (∀ m, (D.toData t₀ ht₀).proper.coeff m = Q.proper.coeff m) :=
  (D.toData t₀ ht₀).coeff_eq_of_toFun_eventuallyEq Q (by
    filter_upwards [D.eventually_toData_toFun_eq_transfer t₀ ht₀, h] with t h1 h2
    rw [h1, h2])

/-- **Uniqueness up to source-fixing descriptor unitary** (`cor:supp-all-rational`): a minimal
regular descriptor realization `D` of `Q` is equivalent to the canonical primary realization
`Q.descriptor` by reduction to Weierstrass primary form followed by a **unique** source-fixing
descriptor Pontryagin unitary. -/
theorem existsUnique_sourceFixing_unitary_weierstrassForm_descriptor (hD : D.IsMinimal)
    (Q : FiniteRationalHermitianData H) (h : ∀ᶠ t : ℝ in atTop, D.transfer t = Q.toFun t) :
    ∃! S : WithLp 2 ((D.anchored t₀ ht₀).infSpace × (D.anchored t₀ ht₀).finSpace) ≃ₗ[ℂ]
        WithLp 2 (Q.jet.Carrier × Q.proper.Carrier),
      PrimaryDescriptor.IsSourceFixingUnitary (D.weierstrassForm t₀ ht₀).toDescriptor
        Q.descriptor S :=
  PrimaryDescriptor.existsUnique_sourceFixing_unitary_of_transfer _ Q.primary
    (D.weierstrassForm_isMinimal t₀ ht₀ hD) Q.primary_isMinimal (by
      filter_upwards [D.eventually_isUnit_pencil_ofReal, h,
        Q.eventually_toFun_eq_primary_transfer] with t h1 h2 h3
      rw [D.weierstrassForm_transfer t₀ ht₀ h1, h2, h3])

/-- **Any two minimal regular descriptor realizations with the same dynamic function are
equivalent**: their Weierstrass primary forms are related by a unique source-fixing descriptor
Pontryagin unitary (`cor:supp-all-rational`, "any second minimal realization splits into the same
invariant primary blocks, and the unique source-fixing unitaries on the finite and infinity blocks
combine to the unique descriptor equivalence"). -/
theorem existsUnique_sourceFixing_unitary_weierstrassForm {N' : Type*} [NormedAddCommGroup N']
    [InnerProductSpace ℂ N'] [CompleteSpace N'] [FiniteDimensional ℂ N']
    (D' : DescriptorRealization H N') (t₀' : ℝ) (ht₀' : IsUnit (D'.A - (t₀' : ℂ) • D'.E))
    (hD : D.IsMinimal) (hD' : D'.IsMinimal)
    (h : ∀ᶠ t : ℝ in atTop, D.transfer t = D'.transfer t) :
    ∃! S : WithLp 2 ((D.anchored t₀ ht₀).infSpace × (D.anchored t₀ ht₀).finSpace) ≃ₗ[ℂ]
        WithLp 2 ((D'.anchored t₀' ht₀').infSpace × (D'.anchored t₀' ht₀').finSpace),
      PrimaryDescriptor.IsSourceFixingUnitary (D.weierstrassForm t₀ ht₀).toDescriptor
        (D'.weierstrassForm t₀' ht₀').toDescriptor S :=
  PrimaryDescriptor.existsUnique_sourceFixing_unitary_of_transfer _ _
    (D.weierstrassForm_isMinimal t₀ ht₀ hD) (D'.weierstrassForm_isMinimal t₀' ht₀' hD') (by
      filter_upwards [D.eventually_isUnit_pencil_ofReal, D'.eventually_isUnit_pencil_ofReal, h]
        with t h1 h2 h3
      rw [D.weierstrassForm_transfer t₀ ht₀ h1, D'.weierstrassForm_transfer t₀' ht₀' h2, h3])

include t₀ ht₀ in
/-- **All minimal realizations of `Q` have state dimension `McM(P) + McM(Q₀)`**
(`cor:supp-all-rational`, "the direct sum attains both minimum state dimensions"). -/
theorem finrank_eq_of_isMinimal (hD : D.IsMinimal) (Q : FiniteRationalHermitianData H)
    (h : ∀ᶠ t : ℝ in atTop, D.transfer t = Q.toFun t) :
    finrank ℂ N = Q.jet.mcMillanDegree + Q.proper.mcMillanDegree := by
  obtain ⟨S, -, -⟩ :=
    D.existsUnique_sourceFixing_unitary_weierstrassForm_descriptor t₀ ht₀ hD Q h
  rw [← Q.finrank_descriptor_state, ← S.finrank_eq, ← (D.anchored t₀ ht₀).primaryEquiv.finrank_eq]

end DescriptorRealization

namespace FiniteRationalHermitianData

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
variable (Q : FiniteRationalHermitianData H)

/-- **The canonical primary descriptor realization of `Q` is minimal** as a descriptor
realization (`cor:supp-all-rational`, existence direction). -/
theorem descriptor_isMinimal : Q.descriptor.IsMinimal :=
  Q.primary.toDescriptor_isMinimal_of_isMinimal Q.primary_isMinimal

/-- `Q.descriptor` realizes `Q` for all large real `t`. -/
theorem eventually_descriptor_transfer_eq_toFun :
    ∀ᶠ t : ℝ in atTop, Q.descriptor.transfer t = Q.toFun t := by
  filter_upwards [Q.eventually_toFun_eq_primary_transfer] with t ht
  exact ht.symm

end FiniteRationalHermitianData

/-- **`cor:supp-all-rational` (all finite rational Hermitian dynamics)**, the equivalence
`eq:supp-all-rational-equivalence` between finite rational Hermitian dynamic functions
`Q = P + Q₀` and minimal regular Pontryagin descriptor realizations, up to source-fixing
descriptor Pontryagin unitary:

* (i) `Q.descriptor` (the primary direct sum of the canonical infinity chain of `P` and the
  canonical Pontryagin realization of `Q₀`) is a minimal regular descriptor realization of `Q`;
* (ii) every minimal regular descriptor realization `D` realizes the finite rational Hermitian
  dynamic function `D.toData` (its Laurent data at infinity is a polynomial jet plus a strictly
  proper part);
* (iii) `D` reduces to its Weierstrass primary form `D.weierstrassForm` (right multiplication by
  the Weierstrass multiplier followed by the source-fixing unitary `x ↦ (π₀ x, x - π₀ x)`), which
  is minimal and related to the canonical realization of `D.toData` by a unique source-fixing
  descriptor Pontryagin unitary;
* (iv) if `D` realizes `Q`, its Weierstrass form is related to `Q.descriptor` by a unique
  source-fixing descriptor Pontryagin unitary, and `dim N = McM(P) + McM(Q₀)`.

Here `t₀` is any real regular point of `D` (`DescriptorRealization.exists_real_regular`). -/
theorem cor_supp_all_rational {H N : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H] [NormedAddCommGroup N] [InnerProductSpace ℂ N] [CompleteSpace N]
    [FiniteDimensional ℂ N] (Q : FiniteRationalHermitianData H) (D : DescriptorRealization H N)
    (hD : D.IsMinimal) (t₀ : ℝ) (ht₀ : IsUnit (D.A - (t₀ : ℂ) • D.E)) :
    (Q.descriptor.IsMinimal ∧ ∀ᶠ t : ℝ in atTop, Q.descriptor.transfer t = Q.toFun t) ∧
    (∀ᶠ t : ℝ in atTop, (D.toData t₀ ht₀).toFun t = D.transfer t) ∧
    (PrimaryDescriptor.IsSourceFixingUnitary (D.weierstrassDescriptor t₀ ht₀)
        (D.weierstrassForm t₀ ht₀).toDescriptor (D.anchored t₀ ht₀).primaryEquiv ∧
      (D.weierstrassForm t₀ ht₀).IsMinimal ∧
      ∃! S : WithLp 2 ((D.anchored t₀ ht₀).infSpace × (D.anchored t₀ ht₀).finSpace) ≃ₗ[ℂ]
          WithLp 2 ((D.toData t₀ ht₀).jet.Carrier × (D.toData t₀ ht₀).proper.Carrier),
        PrimaryDescriptor.IsSourceFixingUnitary (D.weierstrassForm t₀ ht₀).toDescriptor
          (D.toData t₀ ht₀).descriptor S) ∧
    ((∀ᶠ t : ℝ in atTop, D.transfer t = Q.toFun t) →
      (∃! S : WithLp 2 ((D.anchored t₀ ht₀).infSpace × (D.anchored t₀ ht₀).finSpace) ≃ₗ[ℂ]
          WithLp 2 (Q.jet.Carrier × Q.proper.Carrier),
        PrimaryDescriptor.IsSourceFixingUnitary (D.weierstrassForm t₀ ht₀).toDescriptor
          Q.descriptor S) ∧
      finrank ℂ N = Q.jet.mcMillanDegree + Q.proper.mcMillanDegree) :=
  ⟨⟨Q.descriptor_isMinimal, Q.eventually_descriptor_transfer_eq_toFun⟩,
    D.eventually_toData_toFun_eq_transfer t₀ ht₀,
    ⟨D.isSourceFixingUnitary_weierstrass t₀ ht₀, D.weierstrassForm_isMinimal t₀ ht₀ hD,
      D.existsUnique_sourceFixing_unitary_weierstrassForm_descriptor t₀ ht₀ hD _ (by
        filter_upwards [D.eventually_toData_toFun_eq_transfer t₀ ht₀] with t ht
        exact ht.symm)⟩,
    fun h => ⟨D.existsUnique_sourceFixing_unitary_weierstrassForm_descriptor t₀ ht₀ hD Q h,
      D.finrank_eq_of_isMinimal t₀ ht₀ hD Q h⟩⟩

/-! ## Minimality of the state dimension -/

namespace PontryaginRealization

variable {H N : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [NormedAddCommGroup N] [InnerProductSpace ℂ N] [CompleteSpace N] [FiniteDimensional ℂ N]
variable (P : PontryaginRealization H N)

/-- The state dimension of any finite Pontryagin realization of the Laurent data `Q` is at least
the McMillan degree of `Q` (`eq:supp-rational-degree`). -/
theorem mcMillanDegree_le_finrank (Q : NormalizedRationalHermitianData H)
    (hQ : ∀ n, (P.markov n : H →ₗ[ℂ] H) = Q.coeff n) : Q.mcMillanDegree ≤ finrank ℂ N := by
  refine Q.mcMillanDegree_le_realization (P.A : N →ₗ[ℂ] N) (P.Γ : H →ₗ[ℂ] N)
    ((P.Γ† ∘L P.J : N →L[ℂ] H) : N →ₗ[ℂ] H) fun n h => ?_
  rw [← hQ n]
  simp only [markov, ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply]
  rw [← ContinuousLinearMap.toLinearMap_pow]
  rfl

end PontryaginRealization

namespace DescriptorRealization

variable {H N : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [NormedAddCommGroup N] [InnerProductSpace ℂ N] [CompleteSpace N] [FiniteDimensional ℂ N]
variable (D : DescriptorRealization H N) (t₀ : ℝ) (ht₀ : IsUnit (D.A - (t₀ : ℂ) • D.E))

include t₀ ht₀ in
/-- **Every regular descriptor realization of `Q` has state dimension at least
`McM(P) + McM(Q₀)`** (`cor:supp-all-rational`, "the direct sum attains both minimum state
dimensions": with `finrank_eq_of_isMinimal`, the minimal realizations attain the minimum). -/
theorem mcMillanDegree_add_le_finrank (Q : FiniteRationalHermitianData H)
    (h : ∀ᶠ t : ℝ in atTop, D.transfer t = Q.toFun t) :
    Q.jet.mcMillanDegree + Q.proper.mcMillanDegree ≤ finrank ℂ N := by
  have hev : ∀ᶠ t : ℝ in atTop, (D.weierstrassForm t₀ ht₀).toDescriptor.transfer t =
      Q.primary.toDescriptor.transfer t := by
    filter_upwards [D.eventually_isUnit_pencil_ofReal, h, Q.eventually_toFun_eq_primary_transfer]
      with t h1 h2 h3
    rw [D.weierstrassForm_transfer t₀ ht₀ h1, h2, h3]
  obtain ⟨hinf, hfin⟩ :=
    (D.weierstrassForm t₀ ht₀).markov_eq_of_transfer_eventuallyEq Q.primary hev
  have h1 : Q.jet.mcMillanDegree ≤ finrank ℂ (D.anchored t₀ ht₀).infSpace :=
    (D.weierstrassForm t₀ ht₀).inf.mcMillanDegree_le_finrank Q.jet fun n => by
      rw [hinf n]; exact Q.jet.canonical_markov n
  have h2 : Q.proper.mcMillanDegree ≤ finrank ℂ (D.anchored t₀ ht₀).finSpace :=
    (D.weierstrassForm t₀ ht₀).fin.mcMillanDegree_le_finrank Q.proper fun n => by
      rw [hfin n]; exact Q.proper.canonical_markov n
  have h3 : finrank ℂ N =
      finrank ℂ (D.anchored t₀ ht₀).infSpace + finrank ℂ (D.anchored t₀ ht₀).finSpace := by
    rw [(D.anchored t₀ ht₀).primaryEquiv.finrank_eq,
      (WithLp.linearEquiv 2 ℂ
        ((D.anchored t₀ ht₀).infSpace × (D.anchored t₀ ht₀).finSpace)).finrank_eq,
      finrank_prod]
  omega

end DescriptorRealization

end RenewalGeometry

end
