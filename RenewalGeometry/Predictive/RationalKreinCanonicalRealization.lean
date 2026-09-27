/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.Predictive.PontryaginRationalRealization

/-!
# The canonical Pontryagin realization of a rational Hermitian dynamic function

Paper `predictive_spectral_geometry`, label `thm:supp-complete-rational-Krein`
(complete normalized rational generalized-Nevanlinna realization).

Starting from the Hankel data of `def:supp-rational-Hermitian`
(`NormalizedRationalHermitianData`: Laurent coefficients `M_n = M_n*` with finite
Hankel rank; state space `𝒦_Q`, Hankel form `[·,·]_Q`, shift `A_Q`, source
`Γ_Q`), we transport the quotient state space to a Euclidean carrier (the
paper's Hilbert majorant) and obtain a finite Pontryagin realization
`NormalizedRationalHermitianData.canonical` whose Gram operator represents the
Hankel form.  The theorems:

* `canonical_markov` — the Laurent coefficients of the realization are the
  `M_n` (`L_Q A_Qⁿ Γ_Q = M_n`);
* `canonical_transfer_eq_toFun` — **`eq:supp-rational-realization`**,
  `Q(z) = Γ_Q⁺ (A_Q - z)⁻¹ Γ_Q` on the region `‖A_Q‖ < ‖z‖` where the Laurent
  series defines `Q` (rational continuation is the identity theorem);
* `finrank_carrier`, `mcMillanDegree_eq_finrank_columnSpace`,
  `mcMillanDegree_le_realization` — **`eq:supp-rational-degree`**: the
  dimension is the stabilized Hankel rank and no realization is smaller;
* `canonical_isCyclic` — the realization is source minimal (power-cyclic);
* `canonical_form_eq`, `negIndex_canonical_form` — the Pontryagin form is the
  Hankel form and the negative index is its inertia;
* `negSquares_canonical_transfer_eq`, `negSquares_toFun_eq_negIndex` — the
  Nevanlinna kernel `N_Q` (`eq:supp-Nevanlinna-kernel`) has exactly
  `negIndex [·,·]_Q` negative squares (on the upper half-plane of the resolvent
  set for the realization, and on every upper half-plane neighbourhood of
  infinity for the Laurent-series `Q`);
* `PontryaginRealization.existsUnique_sourceFixing_unitary` — every other
  source-minimal finite Pontryagin realization with the same Laurent
  coefficients is related to a given one by a unique source-fixing Pontryagin
  unitary (form-preserving intertwining linear isomorphism).
-/

open scoped InnerProductSpace InnerProduct
open Filter Topology Matrix

noncomputable section

namespace RenewalGeometry

/-! ## The Hankel state form is sesquilinear, Hermitian, nondegenerate and shift-symmetric -/

section HankelStateForm

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable (M : ℕ → H →ₗ[ℂ] H) (hM : ∀ n, (M n).IsSymmetric)

theorem hankelStateForm_add_left (x x' y : hankelState M) :
    hankelStateForm M hM (x + x') y = hankelStateForm M hM x y + hankelStateForm M hM x' y := by
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨u', rfl⟩ := Submodule.Quotient.mk_surjective _ x'
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [← Submodule.Quotient.mk_add, hankelStateForm_mk, hankelStateForm_mk, hankelStateForm_mk,
    map_add, LinearMap.add_apply]

theorem hankelStateForm_add_right (x y y' : hankelState M) :
    hankelStateForm M hM x (y + y') = hankelStateForm M hM x y + hankelStateForm M hM x y' := by
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  obtain ⟨v', rfl⟩ := Submodule.Quotient.mk_surjective _ y'
  rw [← Submodule.Quotient.mk_add, hankelStateForm_mk, hankelStateForm_mk, hankelStateForm_mk,
    map_add]

theorem hankelStateForm_smul_left (c : ℂ) (x y : hankelState M) :
    hankelStateForm M hM (c • x) y = starRingEnd ℂ c * hankelStateForm M hM x y := by
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [← Submodule.Quotient.mk_smul, hankelStateForm_mk, hankelStateForm_mk,
    LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]

theorem hankelStateForm_smul_right (c : ℂ) (x y : hankelState M) :
    hankelStateForm M hM x (c • y) = c * hankelStateForm M hM x y := by
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [← Submodule.Quotient.mk_smul, hankelStateForm_mk, hankelStateForm_mk, map_smul,
    smul_eq_mul]

theorem hankelStateForm_zero_left (y : hankelState M) : hankelStateForm M hM 0 y = 0 := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [← Submodule.Quotient.mk_zero, hankelStateForm_mk, map_zero, LinearMap.zero_apply]

theorem hankelStateForm_conj_symm (x y : hankelState M) :
    hankelStateForm M hM y x = starRingEnd ℂ (hankelStateForm M hM x y) := by
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [hankelStateForm_mk, hankelStateForm_mk, hankelForm_conj_symm M hM]

/-- Nondegeneracy of the descended Hankel form. -/
theorem hankelStateForm_eq_zero_of_forall {y : hankelState M}
    (h : ∀ x, hankelStateForm M hM x y = 0) : y = 0 := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [Submodule.Quotient.mk_eq_zero, mem_hankelNull_iff]
  intro u
  have := h (Submodule.Quotient.mk u)
  rw [hankelStateForm_mk] at this
  rw [hankelForm_conj_symm M hM, this, map_zero]

theorem hankelForm_formalShift_left (u v : ℕ →₀ H) :
    hankelForm M (hankelFormalShift u) v = hankelForm M u (hankelFormalShift v) := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u u' hu hu' => simp only [map_add, LinearMap.add_apply, hu, hu']
  | single i x =>
      induction v using Finsupp.induction_linear with
      | zero => simp
      | add v v' hv hv' => simp only [map_add, hv, hv']
      | single j y =>
          rw [hankelFormalShift_single, hankelFormalShift_single, hankelForm_single_single,
            hankelForm_single_single]
          have : i + 1 + j = i + (j + 1) := by omega
          rw [this]

theorem hankelShift_mk (u : ℕ →₀ H) :
    hankelShift M hM (Submodule.Quotient.mk u) = Submodule.Quotient.mk (hankelFormalShift u) := by
  simp [hankelShift, Submodule.mapQ_apply]

/-- The shift `A_Q` is symmetric for the Hankel form. -/
theorem hankelStateForm_shift_left (x y : hankelState M) :
    hankelStateForm M hM (hankelShift M hM x) y = hankelStateForm M hM x (hankelShift M hM y) := by
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [hankelShift_mk, hankelShift_mk, hankelStateForm_mk, hankelStateForm_mk,
    hankelForm_formalShift_left]

end HankelStateForm

/-! ## The canonical realization -/

namespace NormalizedRationalHermitianData

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
variable (Q : NormalizedRationalHermitianData H)

/-- The McMillan degree `McM(Q)`: the stabilized Hankel rank `dim 𝒦_Q`
(`eq:supp-rational-degree`). -/
def mcMillanDegree : ℕ := Module.finrank ℂ Q.State

/-- **`eq:supp-rational-degree`.**  The McMillan degree is the dimension of the
literal Hankel column span `𝒦_Q`. -/
theorem mcMillanDegree_eq_finrank_columnSpace :
    Q.mcMillanDegree = Module.finrank ℂ (hermitianHankelColumnSpace Q.coeff) :=
  Q.stateEquivColumnSpace.finrank_eq

/-- The Euclidean carrier (Hilbert majorant) of the canonical realization. -/
abbrev Carrier := EuclideanSpace ℂ (Fin Q.mcMillanDegree)

theorem finrank_carrier : Module.finrank ℂ Q.Carrier = Q.mcMillanDegree :=
  finrank_euclideanSpace_fin

/-- The identification of the Hankel state space with the Euclidean carrier. -/
def stateEquiv : Q.State ≃ₗ[ℂ] Q.Carrier :=
  LinearEquiv.ofFinrankEq _ _ (by rw [finrank_carrier]; rfl)

theorem form_zero_left (y : Q.State) : Q.form 0 y = 0 :=
  hankelStateForm_zero_left Q.coeff Q.coeff_symmetric y

theorem form_conj_symm (x y : Q.State) : Q.form y x = starRingEnd ℂ (Q.form x y) :=
  hankelStateForm_conj_symm Q.coeff Q.coeff_symmetric x y

theorem form_shift_left (x y : Q.State) : Q.form (Q.shift x) y = Q.form x (Q.shift y) :=
  hankelStateForm_shift_left Q.coeff Q.coeff_symmetric x y

/-- The Hankel form transported to the carrier. -/
def carrierForm (x y : Q.Carrier) : ℂ := Q.form (Q.stateEquiv.symm x) (Q.stateEquiv.symm y)

/-- The functional `x ↦ [y, x]_Q` on the carrier. -/
def carrierFunctional (y : Q.Carrier) : Q.Carrier →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => Q.carrierForm y x
      map_add' := fun x x' => by
        simp only [carrierForm, map_add]
        exact hankelStateForm_add_right _ _ _ _ _
      map_smul' := fun c x => by
        simp only [carrierForm, map_smul, RingHom.id_apply, smul_eq_mul]
        exact hankelStateForm_smul_right _ _ _ _ _ }

@[simp] theorem carrierFunctional_apply (y x : Q.Carrier) :
    Q.carrierFunctional y x = Q.carrierForm y x := rfl

/-- The Gram operator `J_Q` of the Hankel form on the carrier: `⟪x, J_Q y⟫ = [x, y]_Q`. -/
def gram : Q.Carrier →L[ℂ] Q.Carrier :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => (InnerProductSpace.toDual ℂ Q.Carrier).symm (Q.carrierFunctional y)
      map_add' := fun y y' => by
        rw [← map_add]
        congr 1
        ext x
        simp only [carrierFunctional_apply, ContinuousLinearMap.add_apply, carrierForm, map_add]
        exact hankelStateForm_add_left _ _ _ _ _
      map_smul' := fun c y => by
        have : Q.carrierFunctional (c • y) = starRingEnd ℂ c • Q.carrierFunctional y := by
          ext x
          simp only [carrierFunctional_apply, ContinuousLinearMap.smul_apply, carrierForm,
            map_smul, smul_eq_mul]
          exact hankelStateForm_smul_left _ _ _ _ _
        rw [this, LinearIsometryEquiv.map_smulₛₗ, starRingEnd_self_apply]
        rfl }

theorem inner_gram_left (y x : Q.Carrier) : ⟪Q.gram y, x⟫_ℂ = Q.carrierForm y x := by
  simp only [gram, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]
  rw [InnerProductSpace.toDual_symm_apply, carrierFunctional_apply]

/-- `⟪x, J_Q y⟫ = [x, y]_Q`. -/
theorem inner_gram (x y : Q.Carrier) : ⟪x, Q.gram y⟫_ℂ = Q.carrierForm x y := by
  rw [← inner_conj_symm, inner_gram_left, carrierForm, carrierForm, Q.form_conj_symm,
    starRingEnd_self_apply]

/-- The transported shift `A_Q` on the carrier. -/
def carrierShift : Q.Carrier →L[ℂ] Q.Carrier :=
  LinearMap.toContinuousLinearMap
    ((Q.stateEquiv : Q.State →ₗ[ℂ] Q.Carrier) ∘ₗ Q.shift ∘ₗ (Q.stateEquiv.symm : Q.Carrier →ₗ[ℂ] Q.State))

/-- The transported source `Γ_Q` on the carrier. -/
def carrierSource : H →L[ℂ] Q.Carrier :=
  LinearMap.toContinuousLinearMap ((Q.stateEquiv : Q.State →ₗ[ℂ] Q.Carrier) ∘ₗ Q.source)

theorem stateEquiv_symm_carrierShift (x : Q.Carrier) :
    Q.stateEquiv.symm (Q.carrierShift x) = Q.shift (Q.stateEquiv.symm x) := by
  simp [carrierShift]

theorem stateEquiv_symm_carrierSource (h : H) :
    Q.stateEquiv.symm (Q.carrierSource h) = Q.source h := by
  simp [carrierSource]

theorem stateEquiv_symm_carrierShift_pow (n : ℕ) (x : Q.Carrier) :
    Q.stateEquiv.symm ((Q.carrierShift ^ n) x) = (Q.shift ^ n) (Q.stateEquiv.symm x) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', mul_apply_eq_comp, stateEquiv_symm_carrierShift, ih, pow_succ',
        Module.End.mul_apply]

theorem gram_isSelfAdjoint : IsSelfAdjoint Q.gram := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [inner_gram_left, inner_gram]

theorem gram_injective : Function.Injective Q.gram := by
  intro y y' hyy'
  have hz : Q.gram (y - y') = 0 := by rw [map_sub, hyy', sub_self]
  have : ∀ x, Q.carrierForm x (y - y') = 0 := by
    intro x
    rw [← inner_gram, hz, inner_zero_right]
  have hsub : y - y' = 0 := by
    apply Q.stateEquiv.symm.injective
    rw [map_zero]
    apply hankelStateForm_eq_zero_of_forall Q.coeff Q.coeff_symmetric
    intro s
    have := this (Q.stateEquiv s)
    rwa [carrierForm, LinearEquiv.symm_apply_apply] at this
  exact sub_eq_zero.mp hsub

theorem gram_isUnit : IsUnit Q.gram := by
  rw [ContinuousLinearMap.isUnit_iff_bijective]
  refine ⟨Q.gram_injective, ?_⟩
  exact LinearMap.injective_iff_surjective.mp Q.gram_injective

theorem gram_mul_carrierShift : Q.gram * Q.carrierShift = star Q.carrierShift * Q.gram := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_left ℂ
  intro v
  rw [mul_apply_eq_comp, mul_apply_eq_comp, ContinuousLinearMap.adjoint_inner_right, inner_gram,
    inner_gram, carrierForm, carrierForm, stateEquiv_symm_carrierShift,
    stateEquiv_symm_carrierShift, Q.form_shift_left]

/-- **The canonical finite Pontryagin realization** of
`thm:supp-complete-rational-Krein`: Hankel state space (on its Euclidean
carrier), Hankel form as Gram operator, shift `A_Q`, source `Γ_Q`. -/
def canonical : PontryaginRealization H Q.Carrier where
  A := Q.carrierShift
  Γ := Q.carrierSource
  J := Q.gram
  J_selfAdjoint := Q.gram_isSelfAdjoint
  J_isUnit := Q.gram_isUnit
  J_mul_A := Q.gram_mul_carrierShift

@[simp] theorem canonical_A : Q.canonical.A = Q.carrierShift := rfl
@[simp] theorem canonical_Γ : Q.canonical.Γ = Q.carrierSource := rfl
@[simp] theorem canonical_J : Q.canonical.J = Q.gram := rfl

/-- The Pontryagin form of the canonical realization is the Hankel form. -/
theorem canonical_form_eq (x y : Q.Carrier) :
    Q.canonical.form x y = Q.form (Q.stateEquiv.symm x) (Q.stateEquiv.symm y) := by
  rw [PontryaginRealization.form, canonical_J, inner_gram]
  rfl

/-- **Negative index = inertia of the Hankel form.** -/
theorem negIndex_canonical_form : negIndex Q.canonical.form = negIndex Q.form := by
  have : Q.canonical.form = pullbackForm Q.form (Q.stateEquiv.symm : Q.Carrier →ₗ[ℂ] Q.State) := by
    funext x y
    rw [canonical_form_eq]
    rfl
  rw [this]
  exact negIndex_pullback_equiv Q.form (Q.form_zero_left 0) Q.stateEquiv.symm

/-- **`L_Q A_Qⁿ Γ_Q = M_n`.**  The Laurent coefficients of the canonical
realization are the given Hermitian coefficients. -/
theorem canonical_markov (n : ℕ) : (Q.canonical.markov n : H →ₗ[ℂ] H) = Q.coeff n := by
  ext v
  apply ext_inner_left ℂ
  intro u
  have h := Q.canonical.inner_markov 0 n u v
  rw [zero_add] at h
  rw [ContinuousLinearMap.coe_coe, h, pow_zero, one_apply_eq_self, canonical_form_eq,
    canonical_A, canonical_Γ, stateEquiv_symm_carrierShift_pow, stateEquiv_symm_carrierSource,
    stateEquiv_symm_carrierSource]
  have := Q.form_shift_pow_source 0 n u v
  rw [pow_zero, Module.End.one_apply, zero_add] at this
  exact this

/-- **`eq:supp-rational-realization`.**  On the region `‖A_Q‖ < ‖z‖` where the
Laurent series defines `Q`, `Q(z) = Γ_Q⁺ (A_Q - z)⁻¹ Γ_Q`. -/
theorem canonical_transfer_eq_toFun {z : ℂ} (hz : ‖Q.canonical.A‖ < ‖z‖) :
    Q.canonical.transfer z = Q.toFun z := by
  rw [Q.canonical.transfer_eq_laurent hz]
  unfold toFun
  congr 1
  funext n
  exact Q.canonical_markov n

/-- **Source minimality.**  The canonical realization is power-cyclic. -/
theorem canonical_isCyclic : Q.canonical.IsCyclic := by
  unfold PontryaginRealization.IsCyclic
  apply top_unique
  intro x hx
  clear hx
  obtain ⟨y, rfl⟩ := Q.stateEquiv.surjective x
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u u' hu hu' =>
      rw [Submodule.Quotient.mk_add, map_add]
      exact Submodule.add_mem _ hu hu'
  | single j h =>
      apply Submodule.subset_span
      refine ⟨(j, h), ?_⟩
      show (Q.carrierShift ^ j) (Q.carrierSource h) = _
      apply Q.stateEquiv.symm.injective
      rw [stateEquiv_symm_carrierShift_pow, stateEquiv_symm_carrierSource,
        LinearEquiv.symm_apply_apply]
      exact hankelShift_pow_source Q.coeff Q.coeff_symmetric j h

/-- **Negative squares of the Nevanlinna kernel (realization form).**  The kernel
of the canonical transfer function on the upper half-plane of the resolvent
set has exactly `negIndex [·,·]_Q` negative squares. -/
theorem negSquares_canonical_transfer_eq :
    PontryaginRealization.negSquares (PontryaginRealization.nevanlinnaKernel Q.canonical.transfer)
      Q.canonical.upperResolventSet = negIndex Q.form := by
  rw [Q.canonical.negSquares_transfer_eq_negIndex Q.canonical_isCyclic, negIndex_canonical_form]

end NormalizedRationalHermitianData

/-- The upper half-plane neighbourhood of infinity `{z | 0 < Im z ∧ ρ < ‖z‖}`. -/
def upperNeighbourhood (ρ : ℝ) : Set ℂ := {z | 0 < z.im ∧ ρ < ‖z‖}

namespace NormalizedRationalHermitianData

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
variable (Q : NormalizedRationalHermitianData H)

theorem kernelGram_toFun_eq {ρ : ℝ} (hρ : ‖Q.canonical.A‖ ≤ ρ) {ι : Type} [Fintype ι]
    (z : ι → ℂ) (h : ι → H) (hz : ∀ i, z i ∈ upperNeighbourhood ρ) :
    PontryaginRealization.kernelGram (PontryaginRealization.nevanlinnaKernel Q.toFun) z h =
      PontryaginRealization.kernelGram
        (PontryaginRealization.nevanlinnaKernel Q.canonical.transfer) z h := by
  ext i j
  simp only [PontryaginRealization.kernelGram, Matrix.of_apply,
    PontryaginRealization.nevanlinnaKernel]
  rw [Q.canonical_transfer_eq_toFun (lt_of_le_of_lt hρ (hz i).2),
    Q.canonical_transfer_eq_toFun (lt_of_le_of_lt hρ (hz j).2)]

/-- **Negative squares of the Nevanlinna kernel (intrinsic form).**  On every
upper half-plane neighbourhood of infinity `{0 < Im z, ρ < ‖z‖}` with
`ρ ≥ ‖A_Q‖`, the Nevanlinna kernel `N_Q(z, w) = (Q(z) - Q(w)*)/(z - w̄)` of the
Laurent-series function `Q` has exactly `negIndex [·,·]_Q` negative squares. -/
theorem negSquares_toFun_eq_negIndex {ρ : ℝ} (hρ : ‖Q.canonical.A‖ ≤ ρ) :
    PontryaginRealization.negSquares (PontryaginRealization.nevanlinnaKernel Q.toFun)
      (upperNeighbourhood ρ) = negIndex Q.form := by
  have hbdd : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (z : ι → ℂ) (h : ι → H),
      (∀ i, z i ∈ upperNeighbourhood ρ) →
        negInertia (PontryaginRealization.kernelGram
          (PontryaginRealization.nevanlinnaKernel Q.toFun) z h) ≤ negIndex Q.form := by
    intro ι _ _ z h hz
    rw [Q.kernelGram_toFun_eq hρ z h hz, ← negIndex_canonical_form]
    exact Q.canonical.negInertia_kernelGram_le_negIndex z h (fun i => (hz i).1)
      (fun i => isUnit_sub_algebraMap_of_norm_lt _ (lt_of_le_of_lt hρ (hz i).2))
  apply le_antisymm (PontryaginRealization.negSquares_le hbdd)
  have hA := norm_nonneg Q.canonical.A
  set D : Set ℂ := {w | w.im < 0 ∧ ρ < ‖w‖} with hDdef
  have hDim : ∀ w ∈ D, w.im < 0 := fun w hw => hw.1
  have hDu : ∀ w ∈ D, IsUnit (Q.canonical.A - algebraMap ℂ (Q.Carrier →L[ℂ] Q.Carrier) w) :=
    fun w hw => isUnit_sub_algebraMap_of_norm_lt _ (lt_of_le_of_lt hρ hw.2)
  have hD : ∀ t : ℝ, ρ + 1 ≤ t → -((t : ℂ)) * Complex.I ∈ D := by
    intro t ht
    refine ⟨?_, ?_⟩
    · simp only [Complex.mul_im, Complex.neg_re, Complex.ofReal_re, Complex.I_im, mul_one,
        Complex.neg_im, Complex.ofReal_im, Complex.I_re, mul_zero, add_zero]
      linarith
    · rw [norm_mul, norm_neg, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by linarith)]
      linarith
  obtain ⟨ι, _, _, z, h, hz, hκ⟩ :=
    Q.canonical.exists_kernelGram_negInertia_eq Q.canonical_isCyclic (ρ + 1) (by linarith)
      D hDim hDu hD
  have hzD : ∀ i, z i ∈ upperNeighbourhood ρ := by
    intro i
    have h1 := (hz i).1
    have h2 := (hz i).2
    rw [Complex.conj_im] at h1
    rw [Complex.norm_conj] at h2
    exact ⟨by linarith, h2⟩
  refine PontryaginRealization.le_negSquares hbdd ι z h hzD ?_
  rw [Q.kernelGram_toFun_eq hρ z h hzD, hκ, negIndex_canonical_form]

/-! ### Minimality among all realizations -/

/-- **`eq:supp-rational-degree`, minimality.**  Every linear realization
`L Aⁿ Γ = M_n` of the coefficients on a finite dimensional state space `N` has
dimension at least the McMillan degree. -/
theorem mcMillanDegree_le_realization {N : Type*} [AddCommGroup N] [Module ℂ N]
    [FiniteDimensional ℂ N] (A : N →ₗ[ℂ] N) (Γ : H →ₗ[ℂ] N) (L : N →ₗ[ℂ] H)
    (hreal : ∀ n h, L ((A ^ n) (Γ h)) = Q.coeff n h) :
    Q.mcMillanDegree ≤ Module.finrank ℂ N := by
  classical
  let φ : (ℕ →₀ H) →ₗ[ℂ] N := Finsupp.lsum ℂ fun j => (A ^ j) ∘ₗ Γ
  have hφ_single : ∀ j h, φ (Finsupp.single j h) = (A ^ j) (Γ h) := by
    intro j h
    simp [φ, Finsupp.lsum_single]
  have hr : ∀ (u : ℕ →₀ H) (r : ℕ), L ((A ^ r) (φ u)) = hermitianHankelColumnMap Q.coeff u r := by
    intro u r
    induction u using Finsupp.induction_linear with
    | zero => simp
    | add u u' hu hu' => simp only [map_add, Pi.add_apply, hu, hu']
    | single j h =>
        rw [hφ_single, hermitianHankelColumnMap_single, hermitianHankelColumn,
          ← Module.End.mul_apply, ← pow_add, hreal, add_comm]
  have hker : LinearMap.ker φ ≤ hankelNull Q.coeff := by
    intro u hu
    rw [LinearMap.mem_ker] at hu
    rw [hankelNull_eq_ker Q.coeff Q.coeff_symmetric, LinearMap.mem_ker]
    funext r
    rw [← hr u r, hu, map_zero, map_zero]
    rfl
  let ψ : ((ℕ →₀ H) ⧸ LinearMap.ker φ) →ₗ[ℂ] Q.State := Submodule.factor hker
  have hψ : Function.Surjective ψ := Submodule.factor_surjective hker
  have : FiniteDimensional ℂ ((ℕ →₀ H) ⧸ LinearMap.ker φ) :=
    LinearEquiv.finiteDimensional φ.quotKerEquivRange.symm
  calc Q.mcMillanDegree = Module.finrank ℂ Q.State := rfl
    _ = Module.finrank ℂ (LinearMap.range ψ) := by
        rw [LinearMap.range_eq_top.mpr hψ, finrank_top]
    _ ≤ Module.finrank ℂ ((ℕ →₀ H) ⧸ LinearMap.ker φ) := LinearMap.finrank_range_le ψ
    _ = Module.finrank ℂ (LinearMap.range φ) := φ.quotKerEquivRange.finrank_eq
    _ ≤ Module.finrank ℂ N := Submodule.finrank_le _

end NormalizedRationalHermitianData

/-! ## Uniqueness up to a source-fixing Pontryagin unitary -/

namespace PontryaginRealization

variable {H N₁ N₂ : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup N₁] [InnerProductSpace ℂ N₁] [CompleteSpace N₁]
  [NormedAddCommGroup N₂] [InnerProductSpace ℂ N₂] [CompleteSpace N₂]

/-- The past-state family `A^j Γ v`. -/
def pastState (P : PontryaginRealization H N₁) (p : ℕ × H) : N₁ := (P.A ^ p.1) (P.Γ p.2)

/-- The future-read functional `x ↦ [Aⁱ Γ u, x]`. -/
def futureRead (P : PontryaginRealization H N₁) (f : ℕ × H) : N₁ →ₗ[ℂ] ℂ where
  toFun x := P.form ((P.A ^ f.1) (P.Γ f.2)) x
  map_add' x y := P.form_add_right _ x y
  map_smul' c x := by simp [P.form_smul_right]

theorem futureRead_apply (P : PontryaginRealization H N₁) (f : ℕ × H) (x : N₁) :
    P.futureRead f x = P.form ((P.A ^ f.1) (P.Γ f.2)) x := rfl

theorem futureRead_pastState (P : PontryaginRealization H N₁) (f p : ℕ × H) :
    P.futureRead f (P.pastState p) = ⟪f.2, P.markov (f.1 + p.1) p.2⟫_ℂ := by
  rw [futureRead_apply, pastState, inner_markov]

/-- Source cyclicity plus nondegeneracy gives observability: the future reads
separate the state space. -/
theorem futureRead_separating (P : PontryaginRealization H N₁) (hcyc : P.IsCyclic) (v : N₁)
    (hv : ∀ f, P.futureRead f v = 0) : v = 0 := by
  apply P.eq_zero_of_form_eq_zero
  intro x
  have hx : x ∈ Submodule.span ℂ (Set.range fun p : ℕ × H => (P.A ^ p.1) (P.Γ p.2)) := by
    rw [hcyc]; exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨p, rfl⟩ := hx
      exact hv p
  | zero => exact P.form_zero_left v
  | add x y _ _ hx hy => rw [P.form_add_left, hx, hy, add_zero]
  | smul c x _ hx => rw [P.form_smul_left, hx, mul_zero]

theorem pastState_succ (P : PontryaginRealization H N₁) (p : ℕ × H) :
    P.A (P.pastState p) = P.pastState (p.1 + 1, p.2) := by
  simp only [pastState, pow_succ', mul_apply_eq_comp]

variable [FiniteDimensional ℂ N₁] [FiniteDimensional ℂ N₂]

/-- **Uniqueness up to a source-fixing Pontryagin unitary**
(`thm:supp-complete-rational-Krein`).  Two source-minimal finite Pontryagin
realizations with the same Laurent coefficients are related by a unique
linear isomorphism which fixes the source, intertwines the state operators and
preserves the indefinite forms. -/
theorem existsUnique_sourceFixing_unitary (P₁ : PontryaginRealization H N₁)
    (P₂ : PontryaginRealization H N₂) (hcyc₁ : P₁.IsCyclic) (hcyc₂ : P₂.IsCyclic)
    (hmarkov : ∀ n, P₁.markov n = P₂.markov n) :
    ∃! S : N₁ ≃ₗ[ℂ] N₂,
      (∀ h, S (P₁.Γ h) = P₂.Γ h) ∧ (∀ x, S (P₁.A x) = P₂.A (S x)) ∧
        (∀ x y, P₂.form (S x) (S y) = P₁.form x y) := by
  let tbl : ℕ × H → ℕ × H → ℂ := fun f p => ⟪f.2, P₁.markov (f.1 + p.1) p.2⟫_ℂ
  have hmatch₁ : ∀ f p, P₁.futureRead f (P₁.pastState p) = tbl f p := fun f p =>
    P₁.futureRead_pastState f p
  have hmatch₂ : ∀ f p, P₂.futureRead f (P₂.pastState p) = tbl f p := fun f p => by
    rw [P₂.futureRead_pastState f p]
    simp only [tbl, hmarkov]
  have hreach₁ : Submodule.span ℂ (Set.range P₁.pastState) = ⊤ := hcyc₁
  have hreach₂ : Submodule.span ℂ (Set.range P₂.pastState) = ⊤ := hcyc₂
  have hsep₁ := P₁.futureRead_separating hcyc₁
  have hsep₂ := P₂.futureRead_separating hcyc₂
  let S := minimalRealizationSimilarity tbl P₁.pastState P₂.pastState P₁.futureRead P₂.futureRead
    hmatch₁ hmatch₂ hreach₁ hreach₂ hsep₁ hsep₂
  have hS_state : ∀ p, S (P₁.pastState p) = P₂.pastState p :=
    minimalRealizationSimilarity_state tbl P₁.pastState P₂.pastState P₁.futureRead P₂.futureRead
      hmatch₁ hmatch₂ hreach₁ hreach₂ hsep₁ hsep₂
  have hS_future : ∀ f v, P₂.futureRead f (S v) = P₁.futureRead f v :=
    minimalRealizationSimilarity_future tbl P₁.pastState P₂.pastState P₁.futureRead P₂.futureRead
      hmatch₁ hmatch₂ hreach₁ hreach₂ hsep₁ hsep₂
  have hA₁ : ∀ p, (P₁.A : N₁ →ₗ[ℂ] N₁) (P₁.pastState p) = P₁.pastState (p.1 + 1, p.2) :=
    fun p => P₁.pastState_succ p
  have hA₂ : ∀ p, (P₂.A : N₂ →ₗ[ℂ] N₂) (P₂.pastState p) = P₂.pastState (p.1 + 1, p.2) :=
    fun p => P₂.pastState_succ p
  have hS_int : (S : N₁ →ₗ[ℂ] N₂).comp (P₁.A : N₁ →ₗ[ℂ] N₁) =
      (P₂.A : N₂ →ₗ[ℂ] N₂).comp (S : N₁ →ₗ[ℂ] N₂) :=
    minimalRealizationSimilarity_intertwines tbl P₁.pastState P₂.pastState P₁.futureRead
      P₂.futureRead hmatch₁ hmatch₂ hreach₁ hreach₂ hsep₁ hsep₂ (fun p => (p.1 + 1, p.2))
      (P₁.A : N₁ →ₗ[ℂ] N₁) (P₂.A : N₂ →ₗ[ℂ] N₂) hA₁ hA₂
  refine ⟨S, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro h
    have := hS_state (0, h)
    simpa [pastState] using this
  · intro x
    exact LinearMap.congr_fun hS_int x
  · intro x y
    have hx : x ∈ Submodule.span ℂ (Set.range P₁.pastState) := by
      rw [hreach₁]; exact Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨f, rfl⟩ := hx
        rw [hS_state f]
        have := hS_future f y
        rw [futureRead_apply, futureRead_apply] at this
        exact this
    | zero => rw [map_zero, P₂.form_zero_left, P₁.form_zero_left]
    | add x x' _ _ hx hx' => rw [map_add, P₂.form_add_left, P₁.form_add_left, hx, hx']
    | smul c x _ hx => rw [map_smul, P₂.form_smul_left, P₁.form_smul_left, hx]
  · rintro G ⟨hGΓ, hGA, _⟩
    have hG : ∀ p, G (P₁.pastState p) = P₂.pastState p := by
      rintro ⟨n, h⟩
      induction n with
      | zero => simpa [pastState] using hGΓ h
      | succ n ih =>
          have h1 := P₁.pastState_succ (n, h)
          have h2 := P₂.pastState_succ (n, h)
          simp only at h1 h2
          rw [← h1, ← h2, hGA, ih]
    apply LinearEquiv.ext
    intro x
    have := minimalRealizationSimilarity_unique tbl P₁.pastState P₂.pastState P₁.futureRead
      P₂.futureRead hmatch₁ hmatch₂ hreach₁ hreach₂ hsep₁ hsep₂ G hG
    exact LinearMap.congr_fun this x

end PontryaginRealization

end RenewalGeometry

end
