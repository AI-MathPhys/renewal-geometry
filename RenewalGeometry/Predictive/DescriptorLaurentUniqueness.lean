/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.Predictive.PrimaryDescriptorRealization
import RenewalGeometry.Analysis.PolynomialVanishingAtInfinity

/-!
# Laurent uniqueness and the primary-form equivalence of `cor:supp-all-rational`

Paper `predictive_spectral_geometry`, `eq:supp-rational-split` (uniqueness of the split) and
`cor:supp-all-rational` (the equivalence `eq:supp-all-rational-equivalence` between finite rational
Hermitian dynamic functions and minimal descriptor realizations **in Weierstrass primary form**).

* `PontryaginRealization.markov_eq_of_transfer_eventuallyEq`: two finite Pontryagin realizations
  whose transfer functions agree for all large real `t` have the same Markov parameters (Laurent
  uniqueness for the strictly proper part; proved by the shifted resolvent-source functions
  `G_m(t) = Γ* J A^m (A - t)⁻¹ Γ`, `G_{m+1} = M_m + t G_m`, `t G_m(t) → -M_m`).
* `PrimaryDescriptor.markov_eq_of_transfer_eventuallyEq`: two primary-form descriptor realizations
  with the same transfer function near infinity have the same jet Markov parameters and the same
  proper Markov parameters (the polynomial part is determined since the proper part vanishes at
  infinity, `coeff_eq_zero_of_tendsto_zero`).
* `FiniteRationalHermitianData.coeff_eq_of_toFun_eventuallyEq`: **uniqueness of the split**
  `Q = P + Q₀` of `eq:supp-rational-split`.
* `PrimaryDescriptor.existsUnique_sourceFixing_unitary_of_transfer`: two minimal primary-form
  realizations with the same dynamic function near infinity are related by a **unique** source-fixing
  descriptor Pontryagin unitary.
* `PrimaryDescriptor.toData`: the dynamic function of a primary-form realization is a finite
  rational Hermitian dynamic function (`toData_toFun`), so that `Q ↦ Q.primary` and `R ↦ R.toData`
  are mutually inverse up to the unique source-fixing unitary
  (`toData_primary_coeff`, `existsUnique_sourceFixing_unitary_toData_primary`): this is
  `eq:supp-all-rational-equivalence` for realizations in primary form.
-/

open scoped InnerProductSpace InnerProduct
open Module Filter Topology

noncomputable section

namespace RenewalGeometry

/-! ## Laurent uniqueness for finite Pontryagin realizations -/

namespace PontryaginRealization

variable {H N : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup N] [InnerProductSpace ℂ N] [CompleteSpace N]
variable (P : PontryaginRealization H N)

/-- The shifted resolvent-source functions `G_m(z) = Γ* J A^m (A - z)⁻¹ Γ`. -/
def shiftedTransfer (m : ℕ) (z : ℂ) : H →L[ℂ] H :=
  ((P.Γ† ∘L P.J) ∘L (P.A ^ m * Ring.inverse (P.A - algebraMap ℂ (N →L[ℂ] N) z))) ∘L P.Γ

theorem shiftedTransfer_zero (z : ℂ) : P.shiftedTransfer 0 z = P.transfer z := by
  simp [shiftedTransfer, transfer]

/-- `A (A - z)⁻¹ = 1 + z (A - z)⁻¹` at a regular point. -/
theorem A_mul_inverse {z : ℂ} (hz : IsUnit (P.A - algebraMap ℂ (N →L[ℂ] N) z)) :
    P.A * Ring.inverse (P.A - algebraMap ℂ (N →L[ℂ] N) z) =
      1 + z • Ring.inverse (P.A - algebraMap ℂ (N →L[ℂ] N) z) := by
  have h1 := Ring.mul_inverse_cancel _ hz
  set R := Ring.inverse (P.A - algebraMap ℂ (N →L[ℂ] N) z) with hR
  rw [← h1, sub_mul, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, sub_add_cancel]

/-- The recursion `G_{m+1}(z) = M_m + z G_m(z)` at a regular point. -/
theorem shiftedTransfer_succ {z : ℂ} (hz : IsUnit (P.A - algebraMap ℂ (N →L[ℂ] N) z)) (m : ℕ) :
    P.shiftedTransfer (m + 1) z = P.markov m + z • P.shiftedTransfer m z := by
  unfold shiftedTransfer markov
  rw [pow_succ, mul_assoc, P.A_mul_inverse hz, mul_add, mul_one, mul_smul_comm]
  ext h
  simp [ContinuousLinearMap.comp_apply, mul_apply_eq_comp]

/-- `t G_m(t) → -M_m` as the real parameter `t → +∞`. -/
theorem tendsto_smul_shiftedTransfer (m : ℕ) :
    Tendsto (fun t : ℝ => (t : ℂ) • P.shiftedTransfer m t) atTop (𝓝 (-P.markov m)) := by
  have h1 := tendsto_smul_inverse_sub_algebraMap (R := N →L[ℂ] N) P.A
  have h2 : Tendsto (fun t : ℝ => P.A ^ m *
      ((t : ℂ) • Ring.inverse (P.A - algebraMap ℂ (N →L[ℂ] N) t))) atTop
      (𝓝 (P.A ^ m * (-1))) := h1.const_mul _
  have h3 := (P.sandwich.continuous.tendsto (P.A ^ m * (-1))).comp h2
  have heq : (fun t : ℝ => (t : ℂ) • P.shiftedTransfer m t) = fun t : ℝ => P.sandwich
      (P.A ^ m * ((t : ℂ) • Ring.inverse (P.A - algebraMap ℂ (N →L[ℂ] N) t))) := by
    funext t
    rw [sandwich_apply, mul_smul_comm, shiftedTransfer]
    ext h
    simp
  have hlim : P.sandwich (P.A ^ m * (-1)) = -P.markov m := by
    rw [sandwich_apply, mul_neg, mul_one, markov]
    ext h
    simp
  rw [heq, ← hlim]
  exact h3

/-- The transfer function of a finite Pontryagin realization vanishes at infinity. -/
theorem tendsto_transfer_atTop : Tendsto (fun t : ℝ => P.transfer t) atTop (𝓝 0) := by
  have h := (P.sandwich.continuous.tendsto 0).comp
    (tendsto_inverse_sub_algebraMap (R := N →L[ℂ] N) P.A)
  rw [map_zero] at h
  refine h.congr fun t => ?_
  rw [Function.comp_apply, sandwich_apply]
  rfl

theorem isUnit_sub_algebraMap_ofReal {t : ℝ} (ht0 : 0 < t) (ht : ‖P.A‖ < t) :
    IsUnit (P.A - algebraMap ℂ (N →L[ℂ] N) t) :=
  isUnit_sub_algebraMap_of_norm_lt P.A
    (by rwa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0])

/-- **Laurent uniqueness for the strictly proper part**: two finite Pontryagin realizations whose
transfer functions agree for all large real `t` have the same Markov parameters
(`cor:supp-all-rational`, "if two minimal realizations have the same `Q`, their complete Hankel
moments agree"). -/
theorem markov_eq_of_transfer_eventuallyEq {N' : Type*} [NormedAddCommGroup N']
    [InnerProductSpace ℂ N'] [CompleteSpace N'] (P' : PontryaginRealization H N')
    (h : ∀ᶠ t : ℝ in atTop, P.transfer t = P'.transfer t) : ∀ m, P.markov m = P'.markov m := by
  have key : ∀ m, ∀ᶠ t : ℝ in atTop, P.shiftedTransfer m t = P'.shiftedTransfer m t := by
    intro m
    induction m with
    | zero => simpa only [shiftedTransfer_zero] using h
    | succ m ih =>
      have hm : P.markov m = P'.markov m := by
        have := tendsto_nhds_unique
          ((P.tendsto_smul_shiftedTransfer m).congr' (ih.mono fun t ht => by rw [ht]))
          (P'.tendsto_smul_shiftedTransfer m)
        exact neg_injective this
      filter_upwards [ih, eventually_gt_atTop ‖P.A‖, eventually_gt_atTop ‖P'.A‖,
        eventually_gt_atTop (0 : ℝ)] with t ht h1 h2 ht0
      rw [P.shiftedTransfer_succ (P.isUnit_sub_algebraMap_ofReal ht0 h1),
        P'.shiftedTransfer_succ (P'.isUnit_sub_algebraMap_ofReal ht0 h2), ht, hm]
  intro m
  have := tendsto_nhds_unique
    ((P.tendsto_smul_shiftedTransfer m).congr' ((key m).mono fun t ht => by rw [ht]))
    (P'.tendsto_smul_shiftedTransfer m)
  exact neg_injective this

end PontryaginRealization

/-! ## Laurent uniqueness in primary form -/

namespace PrimaryDescriptor

variable {H Ninf Nfin Ninf' Nfin' : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
  [NormedAddCommGroup Ninf] [InnerProductSpace ℂ Ninf] [CompleteSpace Ninf]
  [NormedAddCommGroup Nfin] [InnerProductSpace ℂ Nfin] [CompleteSpace Nfin]
  [NormedAddCommGroup Ninf'] [InnerProductSpace ℂ Ninf'] [CompleteSpace Ninf']
  [NormedAddCommGroup Nfin'] [InnerProductSpace ℂ Nfin'] [CompleteSpace Nfin']
variable [FiniteDimensional ℂ H] [FiniteDimensional ℂ Ninf] [FiniteDimensional ℂ Nfin]
  [FiniteDimensional ℂ Ninf'] [FiniteDimensional ℂ Nfin']
variable (R : PrimaryDescriptor H Ninf Nfin) (R' : PrimaryDescriptor H Ninf' Nfin')

/-- The jet Markov parameters vanish beyond the nilpotency order. -/
theorem inf_markov_eq_zero {n : ℕ} (hn : R.inf.A ^ n = 0) {k : ℕ} (hk : n ≤ k) :
    R.inf.markov k = 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  simp [PontryaginRealization.markov, pow_add, hn]

/-- **Laurent uniqueness in primary form**: two primary-form descriptor realizations whose transfer
functions agree for all large real `t` have the same jet Markov parameters and the same proper
Markov parameters (`cor:supp-all-rational`; the Hermitian polynomial part is determined because the
strictly proper part vanishes at infinity). -/
theorem markov_eq_of_transfer_eventuallyEq
    (h : ∀ᶠ t : ℝ in atTop, R.toDescriptor.transfer t = R'.toDescriptor.transfer t) :
    (∀ k, R.inf.markov k = R'.inf.markov k) ∧ (∀ m, R.fin.markov m = R'.fin.markov m) := by
  obtain ⟨n₁, hn₁⟩ := R.inf_nilpotent
  obtain ⟨n₂, hn₂⟩ := R'.inf_nilpotent
  have hn : R.inf.A ^ (n₁ + n₂) = 0 := by rw [pow_add, hn₁, zero_mul]
  have hn' : R'.inf.A ^ (n₁ + n₂) = 0 := by rw [pow_add, hn₂, mul_zero]
  have hev : ∀ᶠ t : ℝ in atTop,
      ∑ k ∈ Finset.range (n₁ + n₂), ((t : ℂ) ^ k) • (R.inf.markov k - R'.inf.markov k) =
        -(R.fin.transfer t - R'.fin.transfer t) := by
    filter_upwards [h, eventually_gt_atTop ‖R.fin.A‖, eventually_gt_atTop ‖R'.fin.A‖,
      eventually_gt_atTop (0 : ℝ)] with t ht h1 h2 ht0
    have hz : ‖R.fin.A‖ < ‖(t : ℂ)‖ := by
      rwa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
    have hz' : ‖R'.fin.A‖ < ‖(t : ℂ)‖ := by
      rwa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
    rw [R.toDescriptor_transfer hn hz, R'.toDescriptor_transfer hn' hz'] at ht
    simp only [smul_sub, Finset.sum_sub_distrib]
    calc _ = (∑ k ∈ Finset.range (n₁ + n₂), ((t : ℂ) ^ k) • R.inf.markov k + R.fin.transfer t) -
          (∑ k ∈ Finset.range (n₁ + n₂), ((t : ℂ) ^ k) • R'.inf.markov k + R.fin.transfer t) := by
          abel
      _ = _ := by rw [ht]; abel
  have hlim : Tendsto (fun t : ℝ =>
      ∑ k ∈ Finset.range (n₁ + n₂), ((t : ℂ) ^ k) • (R.inf.markov k - R'.inf.markov k))
      atTop (𝓝 0) := by
    have := (R.fin.tendsto_transfer_atTop.sub R'.fin.tendsto_transfer_atTop).neg
    rw [sub_zero, neg_zero] at this
    exact this.congr' (hev.mono fun t ht => ht.symm)
  have hinf := coeff_eq_zero_of_tendsto_zero (n₁ + n₂) _ hlim
  have hinf' : ∀ k, R.inf.markov k = R'.inf.markov k := by
    intro k
    by_cases hk : k < n₁ + n₂
    · exact sub_eq_zero.mp (hinf k hk)
    · rw [not_lt] at hk
      rw [R.inf_markov_eq_zero hn hk, R'.inf_markov_eq_zero hn' hk]
  refine ⟨hinf', ?_⟩
  apply R.fin.markov_eq_of_transfer_eventuallyEq R'.fin
  filter_upwards [hev] with t ht
  have hzero : ∑ k ∈ Finset.range (n₁ + n₂), ((t : ℂ) ^ k) • (R.inf.markov k - R'.inf.markov k) =
      0 := Finset.sum_eq_zero fun k _ => by rw [hinf' k, sub_self, smul_zero]
  rw [hzero, eq_comm, neg_eq_zero, sub_eq_zero] at ht
  exact ht

/-- **Equivalence in primary form, analytic version** (`cor:supp-all-rational`,
`eq:supp-all-rational-equivalence` for realizations in Weierstrass primary form): two minimal
primary-form descriptor realizations whose dynamic functions agree for all large real `t` are
related by a unique source-fixing descriptor Pontryagin unitary. -/
theorem existsUnique_sourceFixing_unitary_of_transfer (hR : R.IsMinimal) (hR' : R'.IsMinimal)
    (h : ∀ᶠ t : ℝ in atTop, R.toDescriptor.transfer t = R'.toDescriptor.transfer t) :
    ∃! S : WithLp 2 (Ninf × Nfin) ≃ₗ[ℂ] WithLp 2 (Ninf' × Nfin'),
      IsSourceFixingUnitary R.toDescriptor R'.toDescriptor S :=
  let ⟨hinf, hfin⟩ := R.markov_eq_of_transfer_eventuallyEq R' h
  existsUnique_sourceFixing_unitary R R' hR hR' hinf hfin

/-- The same with equality of the dynamic functions on a neighbourhood of infinity `‖z‖ > ρ`. -/
theorem existsUnique_sourceFixing_unitary_of_transfer_eq (hR : R.IsMinimal) (hR' : R'.IsMinimal)
    {ρ : ℝ} (h : ∀ z : ℂ, ρ < ‖z‖ → R.toDescriptor.transfer z = R'.toDescriptor.transfer z) :
    ∃! S : WithLp 2 (Ninf × Nfin) ≃ₗ[ℂ] WithLp 2 (Ninf' × Nfin'),
      IsSourceFixingUnitary R.toDescriptor R'.toDescriptor S := by
  refine existsUnique_sourceFixing_unitary_of_transfer R R' hR hR' ?_
  filter_upwards [eventually_gt_atTop ρ, eventually_gt_atTop (0 : ℝ)] with t ht ht0
  exact h t (by rwa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0])

end PrimaryDescriptor

/-! ## Uniqueness of the split `Q = P + Q₀` -/

namespace FiniteRationalHermitianData

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
variable (Q Q' : FiniteRationalHermitianData H)

/-- The dynamic function of `Q` is the transfer function of its canonical primary realization for
all large real `t`. -/
theorem eventually_toFun_eq_primary_transfer :
    ∀ᶠ t : ℝ in atTop, Q.toFun t = Q.primary.toDescriptor.transfer t := by
  filter_upwards [eventually_gt_atTop ‖Q.proper.canonical.A‖, eventually_gt_atTop (0 : ℝ)]
    with t ht ht0
  rw [primary_toDescriptor, Q.descriptor_transfer
    (by rwa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0])]

/-- **Uniqueness of the split `Q = P + Q₀`** (`eq:supp-rational-split`): two finite rational
Hermitian data with the same dynamic function for all large real `t` have the same polynomial
jet coefficients and the same strictly proper Laurent coefficients. -/
theorem coeff_eq_of_toFun_eventuallyEq (h : ∀ᶠ t : ℝ in atTop, Q.toFun t = Q'.toFun t) :
    (∀ k, Q.jet.coeff k = Q'.jet.coeff k) ∧ (∀ m, Q.proper.coeff m = Q'.proper.coeff m) := by
  have h' : ∀ᶠ t : ℝ in atTop,
      Q.primary.toDescriptor.transfer t = Q'.primary.toDescriptor.transfer t := by
    filter_upwards [h, Q.eventually_toFun_eq_primary_transfer,
      Q'.eventually_toFun_eq_primary_transfer] with t ht h1 h2
    rw [← h1, ← h2, ht]
  obtain ⟨hj, hp⟩ := Q.primary.markov_eq_of_transfer_eventuallyEq Q'.primary h'
  refine ⟨fun k => ?_, fun m => ?_⟩
  · rw [← Q.jet.canonical_markov k, ← Q'.jet.canonical_markov k]
    exact congrArg (fun T : H →L[ℂ] H => (T : H →ₗ[ℂ] H)) (hj k)
  · rw [← Q.proper.canonical_markov m, ← Q'.proper.canonical_markov m]
    exact congrArg (fun T : H →L[ℂ] H => (T : H →ₗ[ℂ] H)) (hp m)

/-- Uniqueness of the split with equality of the dynamic functions on `‖z‖ > ρ`. -/
theorem coeff_eq_of_toFun_eq {ρ : ℝ} (h : ∀ z : ℂ, ρ < ‖z‖ → Q.toFun z = Q'.toFun z) :
    (∀ k, Q.jet.coeff k = Q'.jet.coeff k) ∧ (∀ m, Q.proper.coeff m = Q'.proper.coeff m) := by
  refine Q.coeff_eq_of_toFun_eventuallyEq Q' ?_
  filter_upwards [eventually_gt_atTop ρ, eventually_gt_atTop (0 : ℝ)] with t ht ht0
  exact h t (by rwa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0])

end FiniteRationalHermitianData

/-! ## The dynamic function of a primary-form realization is finite rational Hermitian -/

namespace PontryaginRealization

variable {H N : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup N] [InnerProductSpace ℂ N] [CompleteSpace N]
variable (P : PontryaginRealization H N)

/-- The Markov parameters of a finite-dimensional realization have finite Hankel rank (Kronecker):
the Hankel state space is a quotient of the power-cyclic span of the source. -/
theorem finiteDimensional_hankelState_markov [FiniteDimensional ℂ N] :
    FiniteDimensional ℂ (hankelState fun n => (P.markov n : H →ₗ[ℂ] H)) := by
  classical
  set M : ℕ → H →ₗ[ℂ] H := fun n => (P.markov n : H →ₗ[ℂ] H) with hMdef
  have hM : ∀ n, (M n).IsSymmetric := fun n => P.markov_isSymmetric n
  let A : N →ₗ[ℂ] N := P.A
  let Γ : H →ₗ[ℂ] N := P.Γ
  let L : N →ₗ[ℂ] H := (P.Γ† ∘L P.J : N →L[ℂ] H)
  have hreal : ∀ n h, L ((A ^ n) (Γ h)) = M n h := by
    intro n h
    simp only [hMdef, L, A, Γ, PontryaginRealization.markov, ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.comp_apply]
    rw [← ContinuousLinearMap.toLinearMap_pow]
    rfl
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
  have : FiniteDimensional ℂ ((ℕ →₀ H) ⧸ LinearMap.ker φ) :=
    LinearEquiv.finiteDimensional φ.quotKerEquivRange.symm
  exact Module.Finite.of_surjective (Submodule.factor hker) (Submodule.factor_surjective hker)

/-- The normalized rational Hermitian data of the Markov parameters of a finite-dimensional
Pontryagin realization. -/
def markovData [FiniteDimensional ℂ N] : NormalizedRationalHermitianData H where
  coeff n := (P.markov n : H →ₗ[ℂ] H)
  coeff_symmetric n := P.markov_isSymmetric n
  finiteRank := P.finiteDimensional_hankelState_markov

@[simp] theorem markovData_coeff [FiniteDimensional ℂ N] (n : ℕ) :
    P.markovData.coeff n = (P.markov n : H →ₗ[ℂ] H) := rfl

/-- The dynamic function of the Markov data is the transfer function for `‖A‖ < ‖z‖`. -/
theorem markovData_toFun [FiniteDimensional ℂ H] [FiniteDimensional ℂ N] {z : ℂ}
    (hz : ‖P.A‖ < ‖z‖) : P.markovData.toFun z = P.transfer z := by
  rw [NormalizedRationalHermitianData.toFun, P.transfer_eq_laurent hz]
  rfl

end PontryaginRealization

namespace PrimaryDescriptor

variable {H Ninf Nfin : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup Ninf] [InnerProductSpace ℂ Ninf] [CompleteSpace Ninf]
  [NormedAddCommGroup Nfin] [InnerProductSpace ℂ Nfin] [CompleteSpace Nfin]
variable [FiniteDimensional ℂ H] [FiniteDimensional ℂ Ninf] [FiniteDimensional ℂ Nfin]
variable (R : PrimaryDescriptor H Ninf Nfin)

/-- The nilpotency order of the infinity block (a chosen witness). -/
def nilpotencyOrder : ℕ := Classical.choose R.inf_nilpotent

theorem inf_A_pow_nilpotencyOrder : R.inf.A ^ R.nilpotencyOrder = 0 :=
  Classical.choose_spec R.inf_nilpotent

theorem inf_A_pow_nilpotencyOrder_succ : R.inf.A ^ (R.nilpotencyOrder + 1) = 0 := by
  rw [pow_succ, R.inf_A_pow_nilpotencyOrder, zero_mul]

/-- The jet Markov data is a polynomial jet of degree `≤ nilpotencyOrder`. -/
theorem markovData_isJet : R.inf.markovData.IsJet R.nilpotencyOrder := fun n hn => by
  rw [PontryaginRealization.markovData_coeff, R.inf_markov_eq_zero R.inf_A_pow_nilpotencyOrder hn.le]
  rfl

/-- **The dynamic function of a primary-form realization as a finite rational Hermitian datum**:
jet = Markov parameters of the infinity block, strictly proper part = Markov parameters of the
finite block (`cor:supp-all-rational`, the direction "minimal regular Pontryagin descriptor
realization ↦ finite rational Hermitian dynamic function"). -/
def toData : FiniteRationalHermitianData H where
  deg := R.nilpotencyOrder
  jet := R.inf.markovData
  jet_isJet := R.markovData_isJet
  proper := R.fin.markovData

theorem toData_jet_coeff (k : ℕ) : R.toData.jet.coeff k = (R.inf.markov k : H →ₗ[ℂ] H) := rfl

theorem toData_proper_coeff (m : ℕ) : R.toData.proper.coeff m = (R.fin.markov m : H →ₗ[ℂ] H) :=
  rfl

/-- The dynamic function of `R.toData` is the transfer function of `R` for `‖A_fin‖ < ‖z‖`. -/
theorem toData_toFun {z : ℂ} (hz : ‖R.fin.A‖ < ‖z‖) :
    R.toData.toFun z = R.toDescriptor.transfer z := by
  rw [FiniteRationalHermitianData.toFun, R.toDescriptor_transfer R.inf_A_pow_nilpotencyOrder_succ hz,
    toData, NormalizedRationalHermitianData.jetPolynomial]
  simp only
  rw [PontryaginRealization.markovData_toFun _ hz]
  congr 1

theorem eventually_toData_toFun_eq_transfer :
    ∀ᶠ t : ℝ in atTop, R.toData.toFun t = R.toDescriptor.transfer t := by
  filter_upwards [eventually_gt_atTop ‖R.fin.A‖, eventually_gt_atTop (0 : ℝ)] with t ht ht0
  exact R.toData_toFun (by rwa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0])

/-- **The round trip `R ↦ R.toData ↦ R.toData.primary` returns to `R` up to the unique
source-fixing descriptor unitary** (`cor:supp-all-rational`, `eq:supp-all-rational-equivalence`
in primary form): for a minimal primary realization `R`, the canonical primary realization of its
dynamic function is related to `R` by a unique source-fixing descriptor Pontryagin unitary. -/
theorem existsUnique_sourceFixing_unitary_toData_primary (hR : R.IsMinimal) :
    ∃! S : WithLp 2 (Ninf × Nfin) ≃ₗ[ℂ] WithLp 2 (R.toData.jet.Carrier × R.toData.proper.Carrier),
      IsSourceFixingUnitary R.toDescriptor R.toData.primary.toDescriptor S := by
  refine existsUnique_sourceFixing_unitary_of_transfer R R.toData.primary hR
    R.toData.primary_isMinimal ?_
  filter_upwards [R.eventually_toData_toFun_eq_transfer,
    R.toData.eventually_toFun_eq_primary_transfer] with t h1 h2
  rw [← h1, ← h2]

end PrimaryDescriptor

namespace FiniteRationalHermitianData

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
variable (Q : FiniteRationalHermitianData H)

/-- **The round trip `Q ↦ Q.primary ↦ Q.primary.toData` returns the coefficients of `Q`**
(`cor:supp-all-rational`, `eq:supp-all-rational-equivalence` in primary form). -/
theorem toData_primary_coeff :
    (∀ k, Q.primary.toData.jet.coeff k = Q.jet.coeff k) ∧
      (∀ m, Q.primary.toData.proper.coeff m = Q.proper.coeff m) :=
  ⟨fun k => Q.jet.canonical_markov k, fun m => Q.proper.canonical_markov m⟩

end FiniteRationalHermitianData

end RenewalGeometry

end
