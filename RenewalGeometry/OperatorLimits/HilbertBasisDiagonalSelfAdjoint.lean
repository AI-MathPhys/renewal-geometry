/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.OperatorLimits.UnboundedSelfAdjointResolvent

/-!
# Self-adjoint operators that are diagonal in a Hilbert basis

General infrastructure for the flat-torus spin atlas (paper `predictive_spectral_geometry`,
`cor:supp-flat-torus-spin`): a Fourier multiplier with a Hermitian matrix symbol is, after
diagonalising the symbol fibrewise, an operator that is diagonal in a Hilbert basis with real
eigenvalues.

Let `b : HilbertBasis ι ℂ H` and `lam : ι → ℝ`.

* `mulCLM m hm`: the bounded diagonal multiplier `(a_i) ↦ (m_i a_i)` on `ℓ²(ι)` for a bounded
  family `m`, with `‖mulCLM m hm‖ ≤ C` (`norm_mulCLM_apply_le`).
* `isCompactOperator_mulCLM`: if `m_i → 0` along the cofinite filter, the multiplier is a compact
  operator (norm limit of finite-rank truncations).  This is the abstract Rellich step.
* `diagOp b lam`: the (unbounded) operator `f ↦ Σ_i lam_i ⟪b_i, f⟫ b_i` on its maximal domain
  `{f | Σ_i lam_i² |⟪b_i, f⟫|² < ∞}`; it is symmetric (`diagOp_isFormalAdjoint`).
* `data b lam : SelfAdjointResolventData H`: the resolvents are the bounded diagonal multipliers
  `(lam_i - z)⁻¹`; hence `diagOp b lam` is self-adjoint
  (`SelfAdjointResolventData.isSelfAdjoint_op`).
* `core b = span (range b)`: finite combinations of basis vectors form a core
  (`core_dense`: every domain vector is a graph-norm limit of finite truncations), and
  `diagOp_basis`: `diagOp (b i) = lam_i b i`.
-/

open Filter Topology ComplexConjugate
open scoped InnerProductSpace ENNReal lp

noncomputable section

namespace RenewalGeometry.HilbertBasisDiagonal

set_option linter.unusedSectionVars false

variable {ι : Type*}

/-! ### Square-summable families and bounded multipliers -/

theorem memℓp_two_iff (a : ι → ℂ) : Memℓp a 2 ↔ Summable fun i => ‖a i‖ ^ 2 := by
  rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]

theorem summable_norm_sq (a : ℓ²(ι, ℂ)) : Summable fun i => ‖a i‖ ^ 2 :=
  (memℓp_two_iff _).1 a.2

theorem norm_sq_eq_tsum (a : ℓ²(ι, ℂ)) : ‖a‖ ^ 2 = ∑' i, ‖a i‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal) a
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h

theorem norm_le_of_forall_le_mul {a c : ℓ²(ι, ℂ)} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ i, ‖c i‖ ≤ C * ‖a i‖) : ‖c‖ ≤ C * ‖a‖ := by
  have hsq : ‖c‖ ^ 2 ≤ (C * ‖a‖) ^ 2 := by
    rw [norm_sq_eq_tsum, mul_pow, norm_sq_eq_tsum, ← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun i => ?_) (summable_norm_sq c)
      ((summable_norm_sq a).mul_left _)
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (h i) 2
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq

theorem memℓp_two_mul {m : ι → ℂ} {C : ℝ} (hm : ∀ i, ‖m i‖ ≤ C) (a : ℓ²(ι, ℂ)) :
    Memℓp (fun i => m i * a i) 2 := by
  rw [memℓp_two_iff]
  refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_)
    ((summable_norm_sq a).mul_left (C ^ 2))
  rw [norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (norm_nonneg _) (hm i) 2) (by positivity)

/-- The diagonal multiplier `(a_i) ↦ (m_i a_i)` as a linear map on `ℓ²(ι)`. -/
def mulLinear (m : ι → ℂ) {C : ℝ} (hm : ∀ i, ‖m i‖ ≤ C) : ℓ²(ι, ℂ) →ₗ[ℂ] ℓ²(ι, ℂ) where
  toFun a := ⟨fun i => m i * a i, memℓp_two_mul hm a⟩
  map_add' a c := by
    ext i
    simp only [lp.coeFn_add, Pi.add_apply]
    change m i * (a i + c i) = m i * a i + m i * c i
    ring
  map_smul' z a := by
    ext i
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    change m i * (z * a i) = z * (m i * a i)
    ring

/-- The bounded diagonal multiplier `(a_i) ↦ (m_i a_i)` on `ℓ²(ι)`, `‖m_i‖ ≤ C`. -/
def mulCLM (m : ι → ℂ) {C : ℝ} (hm : ∀ i, ‖m i‖ ≤ C) : ℓ²(ι, ℂ) →L[ℂ] ℓ²(ι, ℂ) :=
  (mulLinear m hm).mkContinuous (max C 0) fun a =>
    norm_le_of_forall_le_mul (le_max_right _ _) fun i => by
      change ‖m i * a i‖ ≤ max C 0 * ‖a i‖
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right ((hm i).trans (le_max_left _ _)) (norm_nonneg _)

@[simp] theorem mulCLM_apply (m : ι → ℂ) {C : ℝ} (hm : ∀ i, ‖m i‖ ≤ C) (a : ℓ²(ι, ℂ))
    (i : ι) : mulCLM m hm a i = m i * a i := rfl

theorem norm_mulCLM_apply_le (m : ι → ℂ) {C : ℝ} (hC : 0 ≤ C) (hm : ∀ i, ‖m i‖ ≤ C)
    (a : ℓ²(ι, ℂ)) : ‖mulCLM m hm a‖ ≤ C * ‖a‖ :=
  norm_le_of_forall_le_mul hC fun i => by
    rw [mulCLM_apply, norm_mul]
    exact mul_le_mul_of_nonneg_right (hm i) (norm_nonneg _)

theorem norm_mulCLM_le (m : ι → ℂ) {C : ℝ} (hC : 0 ≤ C) (hm : ∀ i, ‖m i‖ ≤ C) :
    ‖mulCLM m hm‖ ≤ C :=
  ContinuousLinearMap.opNorm_le_bound _ hC (norm_mulCLM_apply_le m hC hm)

/-! ### Compact diagonal multipliers -/

section compact

variable [DecidableEq ι]

/-- A rank-one diagonal piece `a ↦ (m a_i) e_i` is compact. -/
theorem isCompactOperator_rankOne (i : ι) (c : ℂ) :
    IsCompactOperator fun a : ℓ²(ι, ℂ) =>
      (c * a i) • (lp.single (E := fun _ : ι => ℂ) 2 i (1 : ℂ)) := by
  let φ : ℓ²(ι, ℂ) →L[ℂ] ℂ := c • lp.evalCLM (E := fun _ : ι => ℂ) ℂ 2 i
  let ψ : ℂ →L[ℂ] ℓ²(ι, ℂ) := ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (lp.single 2 i 1)
  have hψ : IsCompactOperator ψ := isCompactOperator_of_locallyCompactSpace_rng ψ
  have h := hψ.comp_clm φ
  have heq : (fun a : ℓ²(ι, ℂ) =>
      (c * a i) • (lp.single (E := fun _ : ι => ℂ) 2 i (1 : ℂ))) = ⇑ψ ∘ ⇑φ := by
    funext a
    simp [φ, ψ, lp.evalCLM]
  rw [heq]
  exact h

/-- A finite sum of rank-one diagonal pieces is compact. -/
theorem isCompactOperator_finsum_rankOne (m : ι → ℂ) (F : Finset ι) :
    IsCompactOperator fun a : ℓ²(ι, ℂ) =>
      ∑ i ∈ F, (m i * a i) • (lp.single (E := fun _ : ι => ℂ) 2 i (1 : ℂ)) := by
  induction F using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact isCompactOperator_zero
  | insert i F hi ih =>
    simp only [Finset.sum_insert hi]
    exact (isCompactOperator_rankOne i (m i)).add ih

omit [DecidableEq ι] in
/-- A finitely supported diagonal multiplier is compact. -/
theorem isCompactOperator_mulCLM_finite (m : ι → ℂ) {C : ℝ} (hm : ∀ i, ‖m i‖ ≤ C)
    (F : Finset ι) (hF : ∀ i, i ∉ F → m i = 0) : IsCompactOperator (mulCLM m hm) := by
  classical
  have heq : ⇑(mulCLM m hm) = fun a => ∑ i ∈ F, (m i * a i) • lp.single 2 i (1 : ℂ) := by
    funext a
    ext j
    rw [mulCLM_apply]
    rw [show (∑ i ∈ F, (m i * a i) • lp.single 2 i (1 : ℂ)) j =
        ∑ i ∈ F, ((m i * a i) • lp.single 2 i (1 : ℂ)) j from by
      rw [lp.coeFn_sum, Finset.sum_apply]]
    simp only [lp.coeFn_smul, Pi.smul_apply, lp.single_apply, smul_eq_mul]
    by_cases hj : j ∈ F
    · rw [Finset.sum_eq_single j]
      · simp
      · intro i _ hij
        simp [Ne.symm hij]
      · intro h; exact absurd hj h
    · rw [hF j hj, zero_mul, Finset.sum_eq_zero]
      intro i hi
      have : j ≠ i := fun h => hj (h ▸ hi)
      simp [this]
  rw [heq]
  exact isCompactOperator_finsum_rankOne m F

omit [DecidableEq ι] in
/-- **Abstract Rellich lemma.** A diagonal multiplier on `ℓ²(ι)` whose entries tend to zero
along the cofinite filter is a compact operator. -/
theorem isCompactOperator_mulCLM (m : ι → ℂ) {C : ℝ} (hm : ∀ i, ‖m i‖ ≤ C)
    (hlim : Tendsto m cofinite (𝓝 0)) : IsCompactOperator (mulCLM m hm) := by
  classical
  have hclosed := isClosed_setOfPred_isCompactOperator (𝕜₁ := ℂ) (𝕜₂ := ℂ)
    (σ₁₂ := RingHom.id ℂ) (M₁ := ℓ²(ι, ℂ)) (M₂ := ℓ²(ι, ℂ))
  refine hclosed.closure_subset (Metric.mem_closure_iff.2 fun ε hε => ?_)
  have hfin : {i | ε / 2 ≤ ‖m i‖}.Finite := by
    have := (tendsto_zero_iff_norm_tendsto_zero.1 hlim).eventually
      (gt_mem_nhds (half_pos hε))
    rw [Filter.eventually_cofinite] at this
    simpa [not_lt] using this
  set F := hfin.toFinset
  set mF : ι → ℂ := fun i => if i ∈ F then m i else 0
  have hmF : ∀ i, ‖mF i‖ ≤ C := fun i => by
    by_cases hi : i ∈ F
    · simp [mF, hi, hm i]
    · simp only [mF, hi, ite_false, norm_zero]
      exact (norm_nonneg _).trans (hm i)
  refine ⟨mulCLM mF hmF, isCompactOperator_mulCLM_finite mF hmF F fun i hi => by simp [mF, hi],
    ?_⟩
  set r : ι → ℂ := fun i => if i ∈ F then 0 else m i
  have hr : ∀ i, ‖r i‖ ≤ ε / 2 := fun i => by
    by_cases hi : i ∈ F
    · simp only [r, hi, ite_true, norm_zero]; positivity
    · simp only [r, hi, ite_false]
      have : i ∉ {i | ε / 2 ≤ ‖m i‖} := by simpa [F] using hi
      simp only [Set.mem_ofPred_eq, not_le] at this
      exact this.le
  have hdiff : mulCLM m hm - mulCLM mF hmF = mulCLM r hr := by
    ext a i
    simp only [sub_apply, lp.coeFn_sub, Pi.sub_apply, mulCLM_apply, r, mF]
    split_ifs <;> ring
  rw [dist_eq_norm, hdiff]
  exact (norm_mulCLM_le r (by positivity) hr).trans_lt (half_lt_self hε)

end compact

/-! ### The diagonal operator -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable (b : HilbertBasis ι ℂ H) (lam : ι → ℝ)

/-- The maximal domain `{f | Σ_i lam_i² |⟪b_i, f⟫|² < ∞}`. -/
def domain : Submodule ℂ H where
  carrier := {f | Memℓp (fun i => (lam i : ℂ) * b.repr f i) 2}
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, map_zero, lp.coeFn_zero, Pi.zero_apply, mul_zero]
    exact zero_memℓp
  add_mem' {f g} hf hg := by
    have : (fun i => (lam i : ℂ) * b.repr (f + g) i) =
        (fun i => (lam i : ℂ) * b.repr f i) + fun i => (lam i : ℂ) * b.repr g i := by
      funext i; simp [mul_add]
    simpa only [Set.mem_ofPred_eq, this] using hf.add hg
  smul_mem' c f hf := by
    have : (fun i => (lam i : ℂ) * b.repr (c • f) i) = c • fun i => (lam i : ℂ) * b.repr f i := by
      funext i; simp only [map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]; ring
    simpa only [Set.mem_ofPred_eq, this] using hf.const_smul c

theorem mem_domain_iff (f : H) :
    f ∈ domain b lam ↔ Memℓp (fun i => (lam i : ℂ) * b.repr f i) 2 := Iff.rfl

/-- The coefficient sequence `(lam_i ⟪b_i, f⟫)` of a domain vector. -/
def scaledCoeff (f : domain b lam) : ℓ²(ι, ℂ) := ⟨fun i => (lam i : ℂ) * b.repr f i, f.2⟩

/-- The diagonal operator on its domain. -/
def opLinear : domain b lam →ₗ[ℂ] H where
  toFun f := b.repr.symm (scaledCoeff b lam f)
  map_add' f g := by
    rw [← map_add]; congr 1; ext i
    simp only [scaledCoeff, lp.coeFn_add, Pi.add_apply, Submodule.coe_add, map_add]
    change (lam i : ℂ) * (b.repr f i + b.repr g i) =
      (lam i : ℂ) * b.repr f i + (lam i : ℂ) * b.repr g i
    ring
  map_smul' c f := by
    rw [RingHom.id_apply, ← map_smul]; congr 1; ext i
    simp only [scaledCoeff, lp.coeFn_smul, Pi.smul_apply, Submodule.coe_smul, map_smul,
      smul_eq_mul]
    change (lam i : ℂ) * (c * b.repr f i) = c * ((lam i : ℂ) * b.repr f i)
    ring

/-- **The diagonal operator** `f ↦ Σ_i lam_i ⟪b_i, f⟫ b_i` on its maximal domain. -/
def diagOp : H →ₗ.[ℂ] H := ⟨domain b lam, opLinear b lam⟩

@[simp] theorem diagOp_domain : (diagOp b lam).domain = domain b lam := rfl

theorem repr_diagOp (f : (diagOp b lam).domain) (i : ι) :
    b.repr (diagOp b lam f) i = (lam i : ℂ) * b.repr f i := by
  change b.repr (b.repr.symm (scaledCoeff b lam f)) i = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

theorem inner_eq_tsum (f g : H) : ⟪f, g⟫_ℂ = ∑' i, conj (b.repr f i) * b.repr g i := by
  rw [← b.repr.inner_map_map, lp.inner_eq_tsum]
  exact tsum_congr fun i => RCLike.inner_apply' _ _

/-- The diagonal operator is symmetric. -/
theorem diagOp_isFormalAdjoint : (diagOp b lam).IsFormalAdjoint (diagOp b lam) := by
  intro f g
  rw [inner_eq_tsum b, inner_eq_tsum b]
  refine tsum_congr fun i => ?_
  rw [repr_diagOp, repr_diagOp, map_mul, Complex.conj_ofReal]
  ring

/-! ### Resolvents -/

theorem norm_sub_ofReal_ge (t : ℝ) (z : ℂ) : |z.im| ≤ ‖(t : ℂ) - z‖ := by
  have h := Complex.abs_im_le_norm ((t : ℂ) - z)
  simpa [abs_neg] using h

theorem ofReal_sub_ne_zero (t : ℝ) {z : ℂ} (hz : z.im ≠ 0) : (t : ℂ) - z ≠ 0 := by
  intro h
  have := norm_sub_ofReal_ge t z
  rw [h, norm_zero] at this
  exact hz (abs_nonpos_iff.1 this)

/-- The resolvent multiplier `(lam_i - z)⁻¹`. -/
def resMult (z : ℂ) : ι → ℂ := fun i => ((lam i : ℂ) - z)⁻¹

theorem norm_resMult_le {z : ℂ} (hz : z.im ≠ 0) (i : ι) : ‖resMult lam z i‖ ≤ |z.im|⁻¹ := by
  rw [resMult, norm_inv]
  exact inv_anti₀ (abs_pos.2 hz) (norm_sub_ofReal_ge _ _)

theorem lam_mul_resMult {z : ℂ} (hz : z.im ≠ 0) (i : ι) :
    (lam i : ℂ) * resMult lam z i = 1 + z * resMult lam z i := by
  have h := ofReal_sub_ne_zero (lam i) hz
  rw [resMult]
  field_simp
  ring

theorem norm_lam_mul_resMult_le {z : ℂ} (hz : z.im ≠ 0) (i : ι) :
    ‖(lam i : ℂ) * resMult lam z i‖ ≤ 1 + ‖z‖ * |z.im|⁻¹ := by
  rw [lam_mul_resMult lam hz]
  refine (norm_add_le _ _).trans ?_
  rw [norm_one, norm_mul]
  gcongr
  exact norm_resMult_le lam hz i

variable [CompleteSpace H]

/-- The resolvent `(diagOp - z)⁻¹ = Σ_i (lam_i - z)⁻¹ ⟪b_i, ·⟫ b_i`. -/
def diagResolvent (z : ℂ) (hz : z.im ≠ 0) : H →L[ℂ] H :=
  b.repr.symm.toLinearIsometry.toContinuousLinearMap ∘L
    mulCLM (resMult lam z) (norm_resMult_le lam hz) ∘L
    b.repr.toLinearIsometry.toContinuousLinearMap

theorem repr_diagResolvent {z : ℂ} (hz : z.im ≠ 0) (f : H) (i : ι) :
    b.repr (diagResolvent b lam z hz f) i = resMult lam z i * b.repr f i := by
  simp [diagResolvent]

theorem diagResolvent_mem {z : ℂ} (hz : z.im ≠ 0) (f : H) :
    diagResolvent b lam z hz f ∈ domain b lam := by
  rw [mem_domain_iff]
  have h := memℓp_two_mul (norm_lam_mul_resMult_le lam hz) (b.repr f)
  convert h using 1
  funext i
  rw [repr_diagResolvent]
  ring

theorem repr_sub_smul (f g : H) (z : ℂ) (i : ι) :
    b.repr (f - z • g) i = b.repr f i - z * b.repr g i := by
  simp only [map_sub, map_smul, lp.coeFn_sub, lp.coeFn_smul, Pi.sub_apply, Pi.smul_apply,
    smul_eq_mul]

/-- **The diagonal operator with real eigenvalues is self-adjoint**, presented by its resolvents. -/
def data : SelfAdjointResolventData H where
  op := diagOp b lam
  symm := diagOp_isFormalAdjoint b lam
  resolvent := diagResolvent b lam
  resolvent_mem z hz f := diagResolvent_mem b lam hz f
  op_resolvent z hz f := by
    apply b.repr.injective
    ext i
    rw [repr_sub_smul, repr_diagOp]
    change (lam i : ℂ) * b.repr (diagResolvent b lam z hz f) i -
      z * b.repr (diagResolvent b lam z hz f) i
      = b.repr f i
    have h := ofReal_sub_ne_zero (lam i) hz
    rw [repr_diagResolvent, ← sub_mul, ← mul_assoc, resMult, mul_inv_cancel₀ h, one_mul]
  resolvent_op z hz u := by
    apply b.repr.injective
    ext i
    rw [repr_diagResolvent, repr_sub_smul, repr_diagOp]
    have h := ofReal_sub_ne_zero (lam i) hz
    rw [resMult, ← sub_mul, ← mul_assoc, inv_mul_cancel₀ h, one_mul]

@[simp] theorem data_op : (data b lam).op = diagOp b lam := rfl

theorem data_resolvent {z : ℂ} (hz : z.im ≠ 0) :
    (data b lam).resolvent z hz = diagResolvent b lam z hz :=
  rfl

/-! ### The core of finite combinations -/

/-- Finite linear combinations of the basis vectors. -/
def core : Submodule ℂ H := Submodule.span ℂ (Set.range b)

theorem basis_mem_domain (i : ι) : b i ∈ domain b lam := by
  classical
  rw [mem_domain_iff, b.repr_self]
  have : (fun j => (lam j : ℂ) * (lp.single 2 i (1 : ℂ) : ℓ²(ι, ℂ)) j) =
      ⇑(lp.single 2 i ((lam i : ℂ)) : ℓ²(ι, ℂ)) := by
    funext j
    simp only [lp.single_apply, Pi.single_apply]
    split_ifs with h
    · subst h; simp
    · simp
  rw [this]
  exact (lp.single 2 i _).2

theorem core_le_domain : core b ≤ domain b lam := by
  classical
  refine Submodule.span_le.2 ?_
  rintro _ ⟨i, rfl⟩
  exact basis_mem_domain b lam i

/-- `diagOp (b i) = lam_i b i`. -/
theorem diagOp_basis (i : ι) :
    diagOp b lam ⟨b i, basis_mem_domain b lam i⟩ = (lam i : ℂ) • b i := by
  classical
  apply b.repr.injective
  ext j
  rw [repr_diagOp, map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  change (lam j : ℂ) * b.repr (b i) j = (lam i : ℂ) * b.repr (b i) j
  rw [b.repr_self, lp.single_apply, Pi.single_apply]
  split_ifs with h
  · subst h; rfl
  · simp

/-- `diagOp` on a finite combination of basis vectors. -/
theorem diagOp_finsum (s : Finset ι) (c : ι → ℂ)
    (hmem : (∑ i ∈ s, c i • b i) ∈ domain b lam) :
    diagOp b lam ⟨∑ i ∈ s, c i • b i, hmem⟩ = ∑ i ∈ s, ((lam i : ℂ) * c i) • b i := by
  classical
  apply b.repr.injective
  ext j
  rw [repr_diagOp]
  simp only [map_sum, map_smul, b.repr_self, lp.coeFn_sum, lp.coeFn_smul, Finset.sum_apply,
    Pi.smul_apply, lp.single_apply, smul_eq_mul, Pi.single_apply]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with h
  · subst h; ring
  · simp

/-- **The finite combinations form a core**: every domain vector is the graph-norm limit of its
finite truncations `Σ_{i ∈ F_k} ⟪b_i, u⟫ b_i`. -/
theorem core_dense [Countable ι] (u : (diagOp b lam).domain) :
    ∃ ψ : ℕ → (diagOp b lam).domain,
      (∀ k, (ψ k : H) ∈ core b) ∧ Tendsto (fun k => (ψ k : H)) atTop (𝓝 (u : H)) ∧
        Tendsto (fun k => diagOp b lam (ψ k)) atTop (𝓝 (diagOp b lam u)) := by
  classical
  obtain ⟨F, hF⟩ := (atTop : Filter (Finset ι)).exists_seq_tendsto
  have hcore : ∀ k, (∑ i ∈ F k, b.repr u i • b i) ∈ core b := fun k =>
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  refine ⟨fun k => ⟨∑ i ∈ F k, b.repr u i • b i, core_le_domain b lam (hcore k)⟩, hcore, ?_, ?_⟩
  · exact (b.hasSum_repr (u : H)).comp hF
  · have h := (b.hasSum_repr (diagOp b lam u)).comp hF
    refine h.congr fun k => ?_
    simp only [Function.comp_apply]
    rw [diagOp_finsum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [repr_diagOp]

end RenewalGeometry.HilbertBasisDiagonal
