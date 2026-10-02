/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.Predictive.NevanlinnaKernelCompression

/-!
# Effective-space compression of indefinite memory: index, degree and composition

Paper `predictive_spectral_geometry`, label `prop:extension-indefinite-compression`.
Let `Q` be a normalized rational Hermitian dynamic function on a finite-dimensional `H`
(`NormalizedRationalHermitianData`) and `V : H' → H` a bounded map (the paper takes an
isometry; no isometry assumption is needed).  Put `Q_V(z) = V* Q(z) V`.

* `PontryaginRealization.compressSource`: replacing the source `Γ` of a realization by `Γ V`
  realizes the compressed function (`transfer_compressSource`, `markov_compressSource`);
* `NormalizedRationalHermitianData.compress`: `Q_V` is again normalized rational Hermitian, with
  Laurent coefficients `V* M_n V` (finite Hankel rank from the realization
  `finiteDimensional_hankelState_of_realization`), and it agrees with `V* Q(z) V` on the Laurent
  region (`compress_toFun_eq`);
* `negIndex_compress_le`: the negative-square index of `N_{Q_V}` does not exceed that of `N_Q`;
* `mcMillanDegree_compress_le`: the minimal finite realization dimension (McMillan degree) of
  `Q_V` does not exceed that of `Q`;
* `PontryaginRealization.compress_compress`, `compress_compress`: nested compressions give the
  compressed function of the composite;
* `extension_indefinite_compression`: the packaged proposition.
-/

open scoped InnerProductSpace InnerProduct
open Matrix

noncomputable section

namespace RenewalGeometry

namespace PontryaginRealization

variable {H H' H'' N : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
  [NormedAddCommGroup H''] [InnerProductSpace ℂ H''] [CompleteSpace H'']
  [NormedAddCommGroup N] [InnerProductSpace ℂ N] [CompleteSpace N]

/-- **Nested compressions** (`prop:extension-indefinite-compression`, composition clause):
`V₂* (V₁* Q V₁) V₂ = (V₁ V₂)* Q (V₁ V₂)`. -/
theorem compress_compress (V₁ : H' →L[ℂ] H) (V₂ : H'' →L[ℂ] H') (Q : ℂ → H →L[ℂ] H) :
    compress V₂ (compress V₁ Q) = compress (V₁ ∘L V₂) Q := by
  funext z
  simp only [compress, ContinuousLinearMap.adjoint_comp]
  ext x
  simp

/-- The realization with compressed source `Γ V` (same state space, state operator and Gram). -/
def compressSource (P : PontryaginRealization H N) (V : H' →L[ℂ] H) :
    PontryaginRealization H' N where
  A := P.A
  Γ := P.Γ ∘L V
  J := P.J
  J_selfAdjoint := P.J_selfAdjoint
  J_isUnit := P.J_isUnit
  J_mul_A := P.J_mul_A

@[simp] theorem compressSource_A (P : PontryaginRealization H N) (V : H' →L[ℂ] H) :
    (P.compressSource V).A = P.A := rfl

/-- The Markov parameters of the compressed-source realization are `V* M_n V`. -/
theorem markov_compressSource (P : PontryaginRealization H N) (V : H' →L[ℂ] H) (n : ℕ) :
    (P.compressSource V).markov n = (V† ∘L P.markov n) ∘L V := by
  simp only [markov, compressSource, ContinuousLinearMap.adjoint_comp]
  ext x
  simp

/-- The transfer function of the compressed-source realization is the compressed transfer
function `V* Q(z) V`. -/
theorem transfer_compressSource (P : PontryaginRealization H N) (V : H' →L[ℂ] H) (z : ℂ) :
    (P.compressSource V).transfer z = compress V P.transfer z := by
  simp only [transfer, compress, compressSource, ContinuousLinearMap.adjoint_comp]
  ext x
  simp

/-- The negative squares of a Nevanlinna kernel on `D` only depend on the values of the
function on `D`. -/
theorem negSquares_nevanlinnaKernel_congr {Q Q' : ℂ → H →L[ℂ] H} {D : Set ℂ}
    (h : ∀ z ∈ D, Q z = Q' z) :
    negSquares (nevanlinnaKernel Q) D = negSquares (nevanlinnaKernel Q') D := by
  unfold negSquares
  congr 1
  ext κ
  constructor
  · rintro ⟨ι, _, _, z, v, hz, hκ⟩
    refine ⟨ι, inferInstance, inferInstance, z, v, hz, ?_⟩
    rw [← hκ]
    congr 1
    ext i j
    simp only [kernelGram, Matrix.of_apply, nevanlinnaKernel, h _ (hz i), h _ (hz j)]
  · rintro ⟨ι, _, _, z, v, hz, hκ⟩
    refine ⟨ι, inferInstance, inferInstance, z, v, hz, ?_⟩
    rw [← hκ]
    congr 1
    ext i j
    simp only [kernelGram, Matrix.of_apply, nevanlinnaKernel, h _ (hz i), h _ (hz j)]

end PontryaginRealization

/-! ### Finite Hankel rank from a finite realization -/

section HankelRealization

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **Kronecker, realization direction**: Hermitian coefficients `M_n = L Aⁿ Γ` admitting a
linear realization on a finite-dimensional state space have finite Hankel rank. -/
theorem finiteDimensional_hankelState_of_realization (M : ℕ → H →ₗ[ℂ] H)
    (hM : ∀ n, (M n).IsSymmetric) {N : Type*} [AddCommGroup N] [Module ℂ N]
    [FiniteDimensional ℂ N] (A : N →ₗ[ℂ] N) (Γ : H →ₗ[ℂ] N) (L : N →ₗ[ℂ] H)
    (hreal : ∀ n h, L ((A ^ n) (Γ h)) = M n h) :
    FiniteDimensional ℂ (hankelState M) := by
  classical
  let φ : (ℕ →₀ H) →ₗ[ℂ] N := Finsupp.lsum ℂ fun j => (A ^ j) ∘ₗ Γ
  have hφ_single : ∀ j h, φ (Finsupp.single j h) = (A ^ j) (Γ h) := by
    intro j h
    simp [φ, Finsupp.lsum_single]
  have hr : ∀ (u : ℕ →₀ H) (r : ℕ), L ((A ^ r) (φ u)) = hermitianHankelColumnMap M u r := by
    intro u r
    induction u using Finsupp.induction_linear with
    | zero => simp
    | add u u' hu hu' => simp only [map_add, Pi.add_apply, hu, hu']
    | single j h =>
        rw [hφ_single, hermitianHankelColumnMap_single, hermitianHankelColumn,
          ← Module.End.mul_apply, ← pow_add, hreal, add_comm]
  have hker : LinearMap.ker φ ≤ hankelNull M := by
    intro u hu
    rw [LinearMap.mem_ker] at hu
    rw [hankelNull_eq_ker M hM, LinearMap.mem_ker]
    funext r
    rw [← hr u r, hu, map_zero, map_zero]
    rfl
  let ψ : ((ℕ →₀ H) ⧸ LinearMap.ker φ) →ₗ[ℂ] hankelState M := Submodule.factor hker
  have hψ : Function.Surjective ψ := Submodule.factor_surjective hker
  have : FiniteDimensional ℂ ((ℕ →₀ H) ⧸ LinearMap.ker φ) :=
    LinearEquiv.finiteDimensional φ.quotKerEquivRange.symm
  exact Module.Finite.of_surjective ψ hψ

end HankelRealization

/-! ### The compressed normalized rational Hermitian function -/

namespace NormalizedRationalHermitianData

variable {H H' H'' : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [FiniteDimensional ℂ H']
  [NormedAddCommGroup H''] [InnerProductSpace ℂ H''] [FiniteDimensional ℂ H'']
variable (Q : NormalizedRationalHermitianData H)

/-- The compressed Laurent coefficients `V* M_n V`. -/
def compressCoeff (V : H' →L[ℂ] H) (n : ℕ) : H' →ₗ[ℂ] H' :=
  ((V† : H →L[ℂ] H') : H →ₗ[ℂ] H') ∘ₗ Q.coeff n ∘ₗ (V : H' →ₗ[ℂ] H)

theorem compressCoeff_apply (V : H' →L[ℂ] H) (n : ℕ) (x : H') :
    Q.compressCoeff V n x = ContinuousLinearMap.adjoint V (Q.coeff n (V x)) := rfl

theorem compressCoeff_isSymmetric (V : H' →L[ℂ] H) (n : ℕ) :
    (Q.compressCoeff V n).IsSymmetric := by
  intro x y
  rw [compressCoeff_apply, compressCoeff_apply, ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_right, Q.coeff_symmetric n]

private theorem clm_pow_apply {N : Type*} [NormedAddCommGroup N] [InnerProductSpace ℂ N]
    (A : N →L[ℂ] N) (n : ℕ) (x : N) : ((A : N →ₗ[ℂ] N) ^ n) x = (A ^ n) x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, ih, pow_succ, mul_apply_eq_comp]
    rfl

/-- The compressed coefficients are realized on the canonical state space of `Q` with source
`Γ_Q V` and output `V* Γ_Q⁺`. -/
theorem compressCoeff_realization (V : H' →L[ℂ] H) (n : ℕ) (h : H') :
    ((V† ∘L Q.canonical.output : Q.Carrier →L[ℂ] H') : Q.Carrier →ₗ[ℂ] H')
      (((Q.canonical.A : Q.Carrier →ₗ[ℂ] Q.Carrier) ^ n)
        (((Q.canonical.Γ ∘L V : H' →L[ℂ] Q.Carrier) : H' →ₗ[ℂ] Q.Carrier) h)) =
      Q.compressCoeff V n h := by
  rw [clm_pow_apply, compressCoeff_apply, ← Q.canonical_markov n]
  rfl

/-- **`Q_V` is normalized rational Hermitian**: the compressed data with coefficients
`V* M_n V` (Hermitian, finite Hankel rank). -/
def compress (V : H' →L[ℂ] H) : NormalizedRationalHermitianData H' where
  coeff := Q.compressCoeff V
  coeff_symmetric := Q.compressCoeff_isSymmetric V
  finiteRank := finiteDimensional_hankelState_of_realization (Q.compressCoeff V)
    (Q.compressCoeff_isSymmetric V) (Q.canonical.A : Q.Carrier →ₗ[ℂ] Q.Carrier)
    ((Q.canonical.Γ ∘L V : H' →L[ℂ] Q.Carrier) : H' →ₗ[ℂ] Q.Carrier)
    ((V† ∘L Q.canonical.output : Q.Carrier →L[ℂ] H') : Q.Carrier →ₗ[ℂ] H')
    (Q.compressCoeff_realization V)

@[simp] theorem compress_coeff (V : H' →L[ℂ] H) : (Q.compress V).coeff = Q.compressCoeff V := rfl

/-- On the Laurent region `‖A_Q‖ < ‖z‖`, the compressed data define the compressed function:
`Q_V(z) = V* Q(z) V`. -/
theorem compress_toFun_eq (V : H' →L[ℂ] H) {z : ℂ} (hz : ‖Q.canonical.A‖ < ‖z‖) :
    PontryaginRealization.compress V Q.toFun z = (Q.compress V).toFun z := by
  have h1 : PontryaginRealization.compress V Q.toFun z =
      PontryaginRealization.compress V Q.canonical.transfer z := by
    simp only [PontryaginRealization.compress, Q.canonical_transfer_eq_toFun hz]
  rw [h1, ← PontryaginRealization.transfer_compressSource,
    (Q.canonical.compressSource V).transfer_eq_laurent (by simpa using hz)]
  unfold toFun
  congr 1
  funext n
  ext x
  rw [PontryaginRealization.markov_compressSource]
  show ContinuousLinearMap.adjoint V (Q.canonical.markov n (V x)) = Q.compressCoeff V n x
  rw [compressCoeff_apply, ← Q.canonical_markov n]
  rfl

/-- **Index clause**: the negative-square index of `N_{Q_V}` (the Pontryagin index
`negIndex [·,·]_{Q_V}`, equal to the number of negative squares of `N_{Q_V}` on every upper
half-plane neighbourhood of infinity) does not exceed that of `N_Q`. -/
theorem negIndex_compress_le (V : H' →L[ℂ] H) : negIndex (Q.compress V).form ≤ negIndex Q.form := by
  set ρ : ℝ := max ‖Q.canonical.A‖ ‖(Q.compress V).canonical.A‖ with hρ
  have h1 : ‖Q.canonical.A‖ ≤ ρ := le_max_left _ _
  have h2 : ‖(Q.compress V).canonical.A‖ ≤ ρ := le_max_right _ _
  rw [← (Q.compress V).negSquares_toFun_eq_negIndex h2]
  have hcongr : PontryaginRealization.negSquares
      (PontryaginRealization.nevanlinnaKernel (Q.compress V).toFun) (upperNeighbourhood ρ) =
      PontryaginRealization.negSquares
      (PontryaginRealization.nevanlinnaKernel (PontryaginRealization.compress V Q.toFun))
        (upperNeighbourhood ρ) :=
    PontryaginRealization.negSquares_nevanlinnaKernel_congr fun z hz =>
      (Q.compress_toFun_eq V (lt_of_le_of_lt h1 hz.2)).symm
  rw [hcongr]
  exact Q.negSquares_compress_toFun_le h1 V

/-- **Degree clause**: the McMillan degree (minimal finite realization dimension,
`mcMillanDegree_le_realization`) of `Q_V` does not exceed that of `Q`; a realization of `Q_V`
on the canonical state space of `Q` is obtained by replacing the source `Γ` by `Γ V`. -/
theorem mcMillanDegree_compress_le (V : H' →L[ℂ] H) :
    (Q.compress V).mcMillanDegree ≤ Q.mcMillanDegree := by
  have := (Q.compress V).mcMillanDegree_le_realization
    (Q.canonical.A : Q.Carrier →ₗ[ℂ] Q.Carrier)
    ((Q.canonical.Γ ∘L V : H' →L[ℂ] Q.Carrier) : H' →ₗ[ℂ] Q.Carrier)
    ((V† ∘L Q.canonical.output : Q.Carrier →L[ℂ] H') : Q.Carrier →ₗ[ℂ] H')
    (Q.compressCoeff_realization V)
  rwa [finrank_carrier] at this

/-- **Composition clause** (data level): nested compressions give the compression along the
composite. -/
theorem compress_compress (V₁ : H' →L[ℂ] H) (V₂ : H'' →L[ℂ] H') :
    (Q.compress V₁).compress V₂ = Q.compress (V₁ ∘L V₂) := by
  have hc : ((Q.compress V₁).compress V₂).coeff = (Q.compress (V₁ ∘L V₂)).coeff := by
    funext n
    ext x
    show ContinuousLinearMap.adjoint V₂ (ContinuousLinearMap.adjoint V₁ (Q.coeff n (V₁ (V₂ x)))) =
      ContinuousLinearMap.adjoint (V₁ ∘L V₂) (Q.coeff n ((V₁ ∘L V₂) x))
    rw [ContinuousLinearMap.adjoint_comp]
    rfl
  cases h1 : (Q.compress V₁).compress V₂
  cases h2 : Q.compress (V₁ ∘L V₂)
  rw [h1, h2] at hc
  simp only at hc
  subst hc
  rfl

/-- **`prop:extension-indefinite-compression` (Negative-square index under effective-space
compression).**  For a normalized rational Hermitian dynamic function `Q` on a
finite-dimensional `H` and any bounded `V : H' → H` (in particular an isometry), with
`Q_V = V* Q V`:
1. `Q_V` is the normalized rational Hermitian function with coefficients `V* M_n V`, equal to
   `V* Q(z) V` on the Laurent region;
2. the negative-square index of `N_{Q_V}` does not exceed that of `N_Q`, intrinsically
   (`negIndex`) and on every upper half-plane neighbourhood of infinity with `ρ ≥ ‖A_Q‖`;
3. the McMillan degree (minimal finite realization dimension) of `Q_V` does not exceed that
   of `Q`;
4. nested compressions give the compressed function of the composite. -/
theorem extension_indefinite_compression (V : H' →L[ℂ] H) :
    (∀ z : ℂ, ‖Q.canonical.A‖ < ‖z‖ →
      PontryaginRealization.compress V Q.toFun z = (Q.compress V).toFun z) ∧
    negIndex (Q.compress V).form ≤ negIndex Q.form ∧
    (∀ ρ : ℝ, ‖Q.canonical.A‖ ≤ ρ →
      PontryaginRealization.negSquares
          (PontryaginRealization.nevanlinnaKernel (PontryaginRealization.compress V Q.toFun))
          (upperNeighbourhood ρ) ≤
        PontryaginRealization.negSquares (PontryaginRealization.nevanlinnaKernel Q.toFun)
          (upperNeighbourhood ρ)) ∧
    (Q.compress V).mcMillanDegree ≤ Q.mcMillanDegree ∧
    (∀ V₂ : H'' →L[ℂ] H',
      (Q.compress V).compress V₂ = Q.compress (V ∘L V₂) ∧
      PontryaginRealization.compress V₂ (PontryaginRealization.compress V Q.toFun) =
        PontryaginRealization.compress (V ∘L V₂) Q.toFun) := by
  refine ⟨fun z hz => Q.compress_toFun_eq V hz, Q.negIndex_compress_le V, fun ρ hρ => ?_,
    Q.mcMillanDegree_compress_le V, fun V₂ => ⟨Q.compress_compress V V₂,
      PontryaginRealization.compress_compress V V₂ Q.toFun⟩⟩
  rw [Q.negSquares_toFun_eq_negIndex hρ]
  exact Q.negSquares_compress_toFun_le hρ V

end NormalizedRationalHermitianData

end RenewalGeometry

end
