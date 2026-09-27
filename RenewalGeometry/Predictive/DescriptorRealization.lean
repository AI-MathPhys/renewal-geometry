/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.Predictive.RationalKreinCanonicalRealization

/-!
# Descriptor (pencil) realizations and the canonical infinity chain

Paper `predictive_spectral_geometry`, `eq:supp-rational-split` and `cor:supp-all-rational`
(partial: the objects and the infinity-chain realization of the polynomial part).

* `DescriptorRealization H N`: a regular Pontryagin descriptor realization `(E, A, Γ, J)` with
  transfer function `Q(z) = Γ* J (A - z E)⁻¹ Γ`; an ordinary Pontryagin realization is the
  descriptor realization with `E = 1` (`PontryaginRealization.toDescriptor`).
* `NormalizedRationalHermitianData.IsJet d`: the Laurent data is a polynomial jet of degree `≤ d`
  (coefficients `P_k = 0` for `k > d`); then the canonical Hankel state operator is nilpotent
  (`canonical_A_pow_eq_zero`) and the canonical realization, read with the roles of `A` and `E`
  exchanged (`infinityChain`: `E = A_P` nilpotent, `A = 1`), realizes the Hermitian polynomial
  `P(z) = ∑_{k ≤ d} P_k z^k` for every `z` (`infinityChain_transfer`): this is the canonical
  nilpotent infinity-chain descriptor realization of `cor:supp-all-rational`.
* `FiniteRationalHermitianData`: a general finite rational Hermitian function encoded by its
  split `Q = P + Q_0` (`eq:supp-rational-split`) into a Hermitian polynomial jet and a strictly
  proper part.
-/

open scoped InnerProductSpace InnerProduct
open Module Filter Topology

noncomputable section

namespace RenewalGeometry

/-! ## Descriptor realizations -/

/-- **A regular Pontryagin descriptor realization** `(E, A, Γ, J)`: the pencil `A - z E` is
regular, `J = J*` is invertible, `A` and `E` are `J`-self-adjoint, and the transfer function is
`Q(z) = Γ* J (A - z E)⁻¹ Γ` (`cor:supp-all-rational`). -/
structure DescriptorRealization (H N : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [NormedAddCommGroup N] [InnerProductSpace ℂ N] [CompleteSpace N] where
  /-- The descriptor (pencil) operator `E`. -/
  E : N →L[ℂ] N
  /-- The state operator `A`. -/
  A : N →L[ℂ] N
  /-- The source `Γ`. -/
  Γ : H →L[ℂ] N
  /-- The Gram operator `J` of the indefinite form. -/
  J : N →L[ℂ] N
  /-- `J = J*`. -/
  J_selfAdjoint : IsSelfAdjoint J
  /-- `J` is invertible. -/
  J_isUnit : IsUnit J
  /-- `J A = A* J`. -/
  J_mul_A : J * A = star A * J
  /-- `J E = E* J`. -/
  J_mul_E : J * E = star E * J
  /-- The pencil `A - z E` is regular: invertible for some `z`. -/
  regular : ∃ z : ℂ, IsUnit (A - z • E)

namespace DescriptorRealization

variable {H N : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup N] [InnerProductSpace ℂ N] [CompleteSpace N]
variable (D : DescriptorRealization H N)

/-- The transfer function `Q(z) = Γ* J (A - z E)⁻¹ Γ` of a descriptor realization. -/
def transfer (z : ℂ) : H →L[ℂ] H :=
  ((D.Γ† ∘L D.J) ∘L Ring.inverse (D.A - z • D.E)) ∘L D.Γ

/-- The indefinite form `[x, y] = ⟪x, J y⟫`. -/
def form (x y : N) : ℂ := ⟪x, D.J y⟫_ℂ

end DescriptorRealization

namespace PontryaginRealization

variable {H N : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup N] [InnerProductSpace ℂ N] [CompleteSpace N]
variable (P : PontryaginRealization H N)

/-- An ordinary Pontryagin realization is a descriptor realization with `E = 1`. -/
def toDescriptor [FiniteDimensional ℂ H] [FiniteDimensional ℂ N] : DescriptorRealization H N where
  E := 1
  A := P.A
  Γ := P.Γ
  J := P.J
  J_selfAdjoint := P.J_selfAdjoint
  J_isUnit := P.J_isUnit
  J_mul_A := P.J_mul_A
  J_mul_E := by simp
  regular := by
    obtain ⟨t, ht⟩ := exists_gt ‖P.A‖
    refine ⟨t, ?_⟩
    have ht' : ‖P.A‖ < ‖(t : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (lt_of_le_of_lt (norm_nonneg _) ht)]
      exact ht
    have := isUnit_sub_algebraMap_of_norm_lt P.A ht'
    rwa [Algebra.algebraMap_eq_smul_one] at this

theorem toDescriptor_transfer [FiniteDimensional ℂ H] [FiniteDimensional ℂ N] (z : ℂ) :
    P.toDescriptor.transfer z = P.transfer z := by
  simp [DescriptorRealization.transfer, toDescriptor, transfer, Algebra.algebraMap_eq_smul_one]

end PontryaginRealization

/-! ## Polynomial jets and the nilpotent infinity chain -/

namespace NormalizedRationalHermitianData

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
variable (Q : NormalizedRationalHermitianData H)

/-- The Laurent data is a polynomial jet of degree `≤ d`: `P_k = 0` for `k > d`. -/
def IsJet (d : ℕ) : Prop := ∀ n, d < n → Q.coeff n = 0

/-- The Hermitian polynomial `P(z) = ∑_{k ≤ d} P_k z^k` of a jet. -/
def jetPolynomial (d : ℕ) (z : ℂ) : H →L[ℂ] H :=
  ∑ k ∈ Finset.range (d + 1), z ^ k • LinearMap.toContinuousLinearMap (Q.coeff k)

theorem hermitianHankelColumnMap_eq_zero_of_isJet {d : ℕ} (hd : Q.IsJet d) (u : ℕ →₀ H)
    (r : ℕ) (hr : d < r) : hermitianHankelColumnMap Q.coeff u r = 0 := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv => simp [hu, hv]
  | single j h =>
      rw [hermitianHankelColumnMap_single, hermitianHankelColumn, hd (j + r) (by omega)]
      rfl

theorem hankelFormalShift_pow_apply (u : ℕ →₀ H) (k r : ℕ) :
    hermitianHankelColumnMap Q.coeff ((hankelFormalShift ^ k) u) r =
      hermitianHankelColumnMap Q.coeff u (r + k) := by
  induction k generalizing r with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, hermitianHankelColumnMap_shift, ih, add_assoc,
        add_comm 1 k]

theorem shift_pow_mk (u : ℕ →₀ H) (k : ℕ) :
    (Q.shift ^ k) (Submodule.Quotient.mk u) = Submodule.Quotient.mk ((hankelFormalShift ^ k) u) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, ih, pow_succ', Module.End.mul_apply]
      simp [shift, hankelShift, Submodule.mapQ_apply]

/-- For a jet of degree `≤ d` the Hankel shift is nilpotent: `A_P^{d+1} = 0`. -/
theorem shift_pow_eq_zero {d : ℕ} (hd : Q.IsJet d) : Q.shift ^ (d + 1) = 0 := by
  refine LinearMap.ext fun x => ?_
  induction x using Submodule.Quotient.induction_on with
  | H u =>
      rw [Q.shift_pow_mk u (d + 1), LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero,
        hankelNull_eq_ker Q.coeff Q.coeff_symmetric, LinearMap.mem_ker]
      funext r
      rw [Q.hankelFormalShift_pow_apply u (d + 1) r,
        Q.hermitianHankelColumnMap_eq_zero_of_isJet hd u _ (by omega)]
      rfl

/-- The canonical state operator of a jet is nilpotent: `A_P^{d+1} = 0`. -/
theorem canonical_A_pow_eq_zero {d : ℕ} (hd : Q.IsJet d) : Q.canonical.A ^ (d + 1) = 0 := by
  refine ContinuousLinearMap.ext fun x => ?_
  apply Q.stateEquiv.symm.injective
  rw [canonical_A, stateEquiv_symm_carrierShift_pow, Q.shift_pow_eq_zero hd]
  simp

/-- The finite Neumann series of the nilpotent pencil: `(1 - z A_P)⁻¹ = ∑_{k ≤ d} z^k A_P^k`. -/
theorem inverse_one_sub_smul_canonical_A {d : ℕ} (hd : Q.IsJet d) (z : ℂ) :
    Ring.inverse (1 - z • Q.canonical.A) =
      ∑ k ∈ Finset.range (d + 1), z ^ k • Q.canonical.A ^ k := by
  set x := z • Q.canonical.A with hx
  have hpow : x ^ (d + 1) = 0 := by
    rw [hx, smul_pow, Q.canonical_A_pow_eq_zero hd, smul_zero]
  have hsum : ∑ k ∈ Finset.range (d + 1), z ^ k • Q.canonical.A ^ k =
      ∑ k ∈ Finset.range (d + 1), x ^ k := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hx, smul_pow]
  have h1 : (1 - x) * ∑ k ∈ Finset.range (d + 1), x ^ k = 1 := by
    rw [mul_neg_geom_sum, hpow, sub_zero]
  have h2 : (∑ k ∈ Finset.range (d + 1), x ^ k) * (1 - x) = 1 := by
    rw [geom_sum_mul_neg, hpow, sub_zero]
  rw [hsum]
  let u : (Q.Carrier →L[ℂ] Q.Carrier)ˣ := ⟨1 - x, ∑ k ∈ Finset.range (d + 1), x ^ k, h1, h2⟩
  exact Ring.inverse_unit u

/-- **The canonical nilpotent infinity chain** of a jet: the canonical Hankel realization with the
roles of the pencil exchanged, `E = A_P` (nilpotent), `A = 1`. -/
def infinityChain : DescriptorRealization H Q.Carrier where
  E := Q.canonical.A
  A := 1
  Γ := Q.canonical.Γ
  J := Q.canonical.J
  J_selfAdjoint := Q.canonical.J_selfAdjoint
  J_isUnit := Q.canonical.J_isUnit
  J_mul_A := by simp
  J_mul_E := Q.canonical.J_mul_A
  regular := ⟨0, by simp⟩

/-- **The infinity chain realizes the Hermitian polynomial jet**: for a jet of degree `≤ d`,
`Γ* J (1 - z A_P)⁻¹ Γ = ∑_{k ≤ d} P_k z^k` for every `z ∈ ℂ` (`cor:supp-all-rational`, the
canonical finite infinity-chain descriptor realization of the polynomial part). -/
theorem infinityChain_transfer {d : ℕ} (hd : Q.IsJet d) (z : ℂ) :
    Q.infinityChain.transfer z = Q.jetPolynomial d z := by
  unfold DescriptorRealization.transfer infinityChain jetPolynomial
  simp only
  rw [Q.inverse_one_sub_smul_canonical_A hd z]
  refine ContinuousLinearMap.ext fun v => ?_
  have hmk : ∀ k, ContinuousLinearMap.adjoint Q.canonical.Γ
      (Q.canonical.J ((Q.canonical.A ^ k) (Q.canonical.Γ v))) = Q.coeff k v := fun k => by
    have := congrArg (fun T : H →ₗ[ℂ] H => T v) (Q.canonical_markov k)
    simp only [PontryaginRealization.markov, ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.comp_apply] at this
    exact this
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, map_sum, map_smul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hmk k]
  rfl

end NormalizedRationalHermitianData

/-! ## General finite rational Hermitian functions: the split `Q = P + Q₀` -/

/-- **A general finite rational Hermitian dynamic function**, encoded by its unique split
`Q(z) = P(z) + Q₀(z)` (`eq:supp-rational-split`) into a Hermitian polynomial jet `P` of degree
`≤ deg` (Laurent data vanishing beyond `deg`) and a strictly proper normalized rational Hermitian
part `Q₀`. -/
structure FiniteRationalHermitianData (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] where
  /-- The degree bound of the polynomial part. -/
  deg : ℕ
  /-- The polynomial jet `P`, as Laurent data. -/
  jet : NormalizedRationalHermitianData H
  /-- `P_k = 0` for `k > deg`. -/
  jet_isJet : jet.IsJet deg
  /-- The strictly proper part `Q₀`. -/
  proper : NormalizedRationalHermitianData H

namespace FiniteRationalHermitianData

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
variable (Q : FiniteRationalHermitianData H)

/-- The dynamic function `Q(z) = P(z) + Q₀(z)`. -/
def toFun (z : ℂ) : H →L[ℂ] H := Q.jet.jetPolynomial Q.deg z + Q.proper.toFun z

/-- The polynomial part is realized by the infinity chain and the strictly proper part by the
canonical Pontryagin realization (for `‖A‖ < ‖z‖`): `Q(z) = P_∞(z) + Q₀(z)` termwise. -/
theorem toFun_eq_infinityChain_add_canonical {z : ℂ} (hz : ‖Q.proper.canonical.A‖ < ‖z‖) :
    Q.toFun z = Q.jet.infinityChain.transfer z + Q.proper.canonical.transfer z := by
  rw [toFun, Q.jet.infinityChain_transfer Q.jet_isJet z, Q.proper.canonical_transfer_eq_toFun hz]

end FiniteRationalHermitianData

end RenewalGeometry

end
