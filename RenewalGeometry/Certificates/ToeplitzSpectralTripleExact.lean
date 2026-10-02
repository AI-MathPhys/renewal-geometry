/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.Certificates.ToeplitzNumberOperatorShiftCommutatorExact
import RenewalGeometry.Certificates.ToeplitzFiniteRankDiagonalProjectionExact
import RenewalGeometry.Spectralization.SpectralCompressionsSequential

open NCG
/-!
# The Toeplitz spectral triple is not spectrally quasidiagonal

Paper `predictive_spectral_geometry`, `thm:spectral-compressions` (properness clause).  On the
separable Hilbert space `ℓ²(ℕ, ℂ)`:

* the unbounded number operator `N e_k = k e_k` is symmetric (`toeplitz_numberOperator_symmetric`)
  and its compact resolvent `(N - i)⁻¹` is normal (`toeplitz_numberResolvent_isStarNormal`);
* the unilateral shift `S` and its adjoint `S* e_{k+1} = e_k` preserve the domain of `N` and
  have bounded commutators `[N, S] = S`, `[N, S*] = -S*`;
* the bounded operators `T` with `[N, T]` and `[N, T*]` bounded form a star subalgebra, hence
  every element of `A_D = alg(I, S, S*)` has bounded commutator;
* this gives an `NCG.SpectralTriple` (`toeplitzTriple`) on the separable space `ℓ²(ℕ, ℂ)`
  (`toeplitz_separableSpace`);
* it is **not spectrally quasidiagonal** (`toeplitzTriple_not_spectrallyQuasidiagonal`): every
  nonzero finite-rank spectral screen `P` of `N` has `‖[P, S]‖ ≥ 1`.
-/

noncomputable section

open Filter Topology Set
open scoped lp InnerProductSpace ComplexConjugate

namespace RenewalGeometry
namespace ToeplitzScreenObstruction

/-! ### Coordinates -/

theorem toeplitz_coord_eq_inner (f : H) (j : ℕ) : f j = ⟪basisVector j, f⟫_ℂ := by
  rw [basisVector, lp.inner_single_left]
  simp

theorem toeplitz_adjoint_shift_apply (f : H) (j : ℕ) :
    ContinuousLinearMap.adjoint unilateralShift f j = f (j + 1) := by
  rw [toeplitz_coord_eq_inner, ContinuousLinearMap.adjoint_inner_right,
    unilateralShift_basisVector, ← toeplitz_coord_eq_inner]

theorem toeplitz_adjoint_shift_basisVector_zero :
    ContinuousLinearMap.adjoint unilateralShift (basisVector 0) = 0 := by
  apply lp.ext
  funext j
  rw [toeplitz_adjoint_shift_apply, basisVector_apply]
  simp

theorem toeplitz_shift_apply_zero (f : H) : unilateralShift f 0 = 0 := by
  rw [toeplitz_coord_eq_inner, ← ContinuousLinearMap.adjoint_inner_left,
    toeplitz_adjoint_shift_basisVector_zero, inner_zero_left]

theorem toeplitz_shift_apply_succ (f : H) (j : ℕ) : unilateralShift f (j + 1) = f j := by
  rw [toeplitz_coord_eq_inner, ← unilateralShift_basisVector]
  show ⟪unilateralShiftIsometry (basisVector j), unilateralShiftIsometry f⟫_ℂ = _
  rw [LinearIsometry.inner_map_map, ← toeplitz_coord_eq_inner]

/-! ### The domain of the number operator -/

theorem toeplitz_mem_domain_iff (x : H) :
    x ∈ numberOperator.domain ↔ ∃ z : H, ∀ n, z n = (n : ℂ) * x n := by
  constructor
  · intro hx
    exact ⟨numberOperator ⟨x, hx⟩, fun n => numberOperator_apply_coordinate ⟨x, hx⟩ n⟩
  · rintro ⟨z, hz⟩
    refine ⟨z - Complex.I • x, ?_⟩
    apply lp.ext
    funext n
    change numberResolvent (z - Complex.I • x) n = x n
    rw [numberResolvent_apply]
    change ((n : ℂ) - Complex.I)⁻¹ * (z n - Complex.I * x n) = x n
    rw [hz n]
    field_simp [natCast_sub_I_ne_zero n]

/-! ### Symmetry and normal resolvent -/

theorem toeplitz_numberOperator_symmetric (x y : numberOperator.domain) :
    ⟪numberOperator x, (y : H)⟫_ℂ = ⟪(x : H), numberOperator y⟫_ℂ := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  congr 1
  funext n
  rw [numberOperator_apply_coordinate, numberOperator_apply_coordinate]
  simp only [RCLike.inner_apply, map_mul, Complex.conj_natCast]
  ring

theorem toeplitz_norm_conjBlock_le (n : ℕ) (z : ℂ) :
    ‖(((n : ℂ) + Complex.I)⁻¹ • (1 : ℂ →L[ℂ] ℂ)) z‖ ≤ 1 * ‖z‖ := by
  have h : 1 ≤ ‖(n : ℂ) + Complex.I‖ := by
    have := Complex.abs_im_le_norm ((n : ℂ) + Complex.I)
    simpa using this
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, norm_smul, norm_inv]
  exact mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ h) (norm_nonneg z)

/-- The diagonal operator with coefficients `(n + i)⁻¹`, the adjoint of the resolvent. -/
def toeplitzConjResolvent : H →L[ℂ] H :=
  l2BlockDiagonal (fun n : ℕ => ((n : ℂ) + Complex.I)⁻¹ • (1 : ℂ →L[ℂ] ℂ)) 1 zero_le_one
    toeplitz_norm_conjBlock_le

theorem toeplitzConjResolvent_apply (f : H) (n : ℕ) :
    toeplitzConjResolvent f n = ((n : ℂ) + Complex.I)⁻¹ * f n := by
  simp [toeplitzConjResolvent, smul_eq_mul]

theorem toeplitz_star_numberResolvent : star numberResolvent = toeplitzConjResolvent := by
  symm
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  congr 1
  funext n
  rw [toeplitzConjResolvent_apply, numberResolvent_apply]
  simp only [RCLike.inner_apply, map_mul, map_inv₀, map_add, Complex.conj_natCast,
    Complex.conj_I]
  ring

theorem toeplitz_numberResolvent_isStarNormal : IsStarNormal numberResolvent := by
  refine ⟨?_⟩
  rw [toeplitz_star_numberResolvent]
  ext f n
  change toeplitzConjResolvent (numberResolvent f) n = numberResolvent (toeplitzConjResolvent f) n
  rw [toeplitzConjResolvent_apply, numberResolvent_apply, numberResolvent_apply,
    toeplitzConjResolvent_apply]
  ring

/-! ### Bounded commutators -/

section Commutator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem commutatorBounded_nonneg {D : E →ₗ.[ℂ] E} {T : E →L[ℂ] E}
    (h : CommutatorBounded D T) :
    ∃ hpres : ∀ x, x ∈ D.domain → T x ∈ D.domain, ∃ C : ℝ, 0 ≤ C ∧
      ∀ x : D.domain, ‖D ⟨T x, hpres x x.2⟩ - T (D x)‖ ≤ C * ‖(x : E)‖ := by
  obtain ⟨hpres, C, hC⟩ := h
  refine ⟨hpres, max C 0, le_max_right _ _, fun x => (hC x).trans ?_⟩
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)

theorem commutatorBounded_add {D : E →ₗ.[ℂ] E} {T U : E →L[ℂ] E}
    (hT : CommutatorBounded D T) (hU : CommutatorBounded D U) :
    CommutatorBounded D (T + U) := by
  obtain ⟨pT, CT, hCT⟩ := hT
  obtain ⟨pU, CU, hCU⟩ := hU
  refine ⟨fun x hx => D.domain.add_mem (pT x hx) (pU x hx), CT + CU, fun x => ?_⟩
  have e : (⟨(T + U) x, D.domain.add_mem (pT x x.2) (pU x x.2)⟩ : D.domain) =
      ⟨T x, pT x x.2⟩ + ⟨U x, pU x x.2⟩ := rfl
  rw [e, LinearPMap.map_add, ContinuousLinearMap.add_apply]
  calc ‖D ⟨T x, pT x x.2⟩ + D ⟨U x, pU x x.2⟩ - (T (D x) + U (D x))‖
      = ‖(D ⟨T x, pT x x.2⟩ - T (D x)) + (D ⟨U x, pU x x.2⟩ - U (D x))‖ := by abel_nf
    _ ≤ ‖D ⟨T x, pT x x.2⟩ - T (D x)‖ + ‖D ⟨U x, pU x x.2⟩ - U (D x)‖ := norm_add_le _ _
    _ ≤ CT * ‖(x : E)‖ + CU * ‖(x : E)‖ := add_le_add (hCT x) (hCU x)
    _ = (CT + CU) * ‖(x : E)‖ := by ring

theorem commutatorBounded_mul {D : E →ₗ.[ℂ] E} {T U : E →L[ℂ] E}
    (hT : CommutatorBounded D T) (hU : CommutatorBounded D U) :
    CommutatorBounded D (T * U) := by
  obtain ⟨pT, CT, hCT0, hCT⟩ := commutatorBounded_nonneg hT
  obtain ⟨pU, CU, hCU0, hCU⟩ := commutatorBounded_nonneg hU
  refine ⟨fun x hx => pT _ (pU x hx), CT * ‖U‖ + ‖T‖ * CU, fun x => ?_⟩
  have h1 := hCT ⟨U x, pU x x.2⟩
  have h2 := hCU x
  change ‖D ⟨T (U x), pT _ (pU x x.2)⟩ - T (U (D x))‖ ≤ _
  have e : D ⟨T (U x), pT _ (pU x x.2)⟩ - T (U (D x)) =
      (D ⟨T (U x), pT _ (pU x x.2)⟩ - T (D ⟨U x, pU x x.2⟩)) +
        T (D ⟨U x, pU x x.2⟩ - U (D x)) := by
    rw [map_sub]; abel
  rw [e]
  calc ‖(D ⟨T (U x), pT _ (pU x x.2)⟩ - T (D ⟨U x, pU x x.2⟩)) +
        T (D ⟨U x, pU x x.2⟩ - U (D x))‖
      ≤ ‖D ⟨T (U x), pT _ (pU x x.2)⟩ - T (D ⟨U x, pU x x.2⟩)‖ +
        ‖T (D ⟨U x, pU x x.2⟩ - U (D x))‖ := norm_add_le _ _
    _ ≤ CT * ‖U x‖ + ‖T‖ * (CU * ‖(x : E)‖) := by
        refine add_le_add h1 ?_
        exact (T.le_opNorm _).trans (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))
    _ ≤ CT * (‖U‖ * ‖(x : E)‖) + ‖T‖ * (CU * ‖(x : E)‖) := by
        gcongr
        exact U.le_opNorm _
    _ = (CT * ‖U‖ + ‖T‖ * CU) * ‖(x : E)‖ := by ring

theorem commutatorBounded_algebraMap (D : E →ₗ.[ℂ] E) (c : ℂ) :
    CommutatorBounded D (algebraMap ℂ (E →L[ℂ] E) c) := by
  refine ⟨fun x hx => ?_, 0, fun x => ?_⟩
  · rw [Algebra.algebraMap_eq_smul_one, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply]
    exact D.domain.smul_mem c hx
  · have e : (⟨algebraMap ℂ (E →L[ℂ] E) c x, by
        rw [Algebra.algebraMap_eq_smul_one, ContinuousLinearMap.smul_apply,
          ContinuousLinearMap.one_apply]
        exact D.domain.smul_mem c x.2⟩ : D.domain) = c • x := by
      apply Subtype.ext
      simp [Algebra.algebraMap_eq_smul_one]
    rw [e, LinearPMap.map_smul]
    simp [Algebra.algebraMap_eq_smul_one]

/-- The bounded operators `T` such that both `[D, T]` and `[D, T*]` are bounded form a star
subalgebra. -/
def commutatorBoundedStarSubalgebra (D : E →ₗ.[ℂ] E) : StarSubalgebra ℂ (E →L[ℂ] E) where
  carrier := {T | CommutatorBounded D T ∧ CommutatorBounded D (star T)}
  mul_mem' {T U} hT hU := ⟨commutatorBounded_mul hT.1 hU.1, by
    rw [star_mul]; exact commutatorBounded_mul hU.2 hT.2⟩
  add_mem' {T U} hT hU := ⟨commutatorBounded_add hT.1 hU.1, by
    rw [star_add]; exact commutatorBounded_add hT.2 hU.2⟩
  algebraMap_mem' c := ⟨commutatorBounded_algebraMap D c, by
    rw [← algebraMap_star_comm]; exact commutatorBounded_algebraMap D (star c)⟩
  star_mem' {T} hT := ⟨hT.2, by rw [star_star]; exact hT.1⟩

end Commutator

/-- `[N, S] = S`: the shift preserves the domain and has bounded commutator. -/
theorem toeplitz_commutatorBounded_shift : CommutatorBounded numberOperator unilateralShift := by
  have hpres : ∀ x, x ∈ numberOperator.domain → unilateralShift x ∈ numberOperator.domain := by
    intro x hx
    obtain ⟨z, hz⟩ := (toeplitz_mem_domain_iff x).mp hx
    refine (toeplitz_mem_domain_iff _).mpr ⟨unilateralShift z + unilateralShift x, fun n => ?_⟩
    cases n with
    | zero => simp [toeplitz_shift_apply_zero]
    | succ m =>
      change unilateralShift z (m + 1) + unilateralShift x (m + 1) = _
      simp only [toeplitz_shift_apply_succ]
      rw [hz m]
      push_cast
      ring
  refine ⟨hpres, ‖unilateralShift‖, fun x => ?_⟩
  have e : numberOperator ⟨unilateralShift x, hpres x x.2⟩ - unilateralShift (numberOperator x) =
      unilateralShift x := by
    apply lp.ext
    funext n
    change numberOperator ⟨unilateralShift x, hpres x x.2⟩ n -
      unilateralShift (numberOperator x) n = unilateralShift x n
    rw [numberOperator_apply_coordinate]
    cases n with
    | zero => simp only [toeplitz_shift_apply_zero, mul_zero, sub_zero]
    | succ m =>
      simp only [toeplitz_shift_apply_succ]
      rw [numberOperator_apply_coordinate]
      push_cast
      ring
  rw [e]
  exact unilateralShift.le_opNorm _

/-- `[N, S*] = -S*`: the adjoint shift preserves the domain and has bounded commutator. -/
theorem toeplitz_commutatorBounded_star_shift :
    CommutatorBounded numberOperator (star unilateralShift) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  set B := ContinuousLinearMap.adjoint unilateralShift
  have hpres : ∀ x, x ∈ numberOperator.domain → B x ∈ numberOperator.domain := by
    intro x hx
    obtain ⟨z, hz⟩ := (toeplitz_mem_domain_iff x).mp hx
    refine (toeplitz_mem_domain_iff _).mpr ⟨B z - B x, fun n => ?_⟩
    change B z n - B x n = _
    simp only [B, toeplitz_adjoint_shift_apply]
    rw [hz (n + 1)]
    push_cast
    ring
  refine ⟨hpres, ‖B‖, fun x => ?_⟩
  have e : numberOperator ⟨B x, hpres x x.2⟩ - B (numberOperator x) = -B x := by
    apply lp.ext
    funext n
    change numberOperator ⟨B x, hpres x x.2⟩ n - B (numberOperator x) n = -(B x n)
    rw [numberOperator_apply_coordinate]
    simp only [B, toeplitz_adjoint_shift_apply]
    rw [numberOperator_apply_coordinate]
    push_cast
    ring
  rw [e, norm_neg]
  exact B.le_opNorm _

theorem toeplitz_shift_mem_commutatorBoundedStarSubalgebra :
    unilateralShift ∈ commutatorBoundedStarSubalgebra numberOperator :=
  ⟨toeplitz_commutatorBounded_shift, toeplitz_commutatorBounded_star_shift⟩

/-! ### Separability -/

/-- `ℓ²(ℕ, ℂ)` is separable: finite basis combinations are dense. -/
instance toeplitz_separableSpace : TopologicalSpace.SeparableSpace H := by
  rw [← TopologicalSpace.isSeparable_univ_iff]
  let F : ℕ → Set H := fun n => range (fun c : Fin n → ℂ => ∑ k : Fin n, c k • basisVector k)
  have hsep : TopologicalSpace.IsSeparable (⋃ n, F n) :=
    TopologicalSpace.IsSeparable.iUnion fun n =>
      TopologicalSpace.isSeparable_range (by fun_prop)
  refine hsep.closure.mono fun f _ => ?_
  refine mem_closure_of_tendsto (tendsto_l2FinsetScreen_range_apply f)
    (Eventually.of_forall fun n => mem_iUnion.2 ⟨n, fun k => f k, ?_⟩)
  rw [l2FinsetScreen_eq_sum_basisVector, Finset.sum_range (fun k => f k • basisVector k)]

/-! ### The Toeplitz spectral triple -/

/-- The Toeplitz spectral triple: `B(ℓ²(ℕ))` represented identically, the number operator as
Dirac operator, and `A_D = alg(I, S, S*)` the star subalgebra generated by the unilateral
shift. -/
def toeplitzTriple : SpectralTriple (H →L[ℂ] H) H where
  rep := StarAlgHom.id ℂ (H →L[ℂ] H)
  dirac := numberOperator
  dense_domain := numberOperator_dense_domain
  symmetric := toeplitz_numberOperator_symmetric
  compact_resolvent := ⟨numberResolvent, numberResolvent_mem_numberOperatorDomain,
    numberResolvent_isCompactOperator, toeplitz_numberResolvent_isStarNormal,
    numberResolvent_right_inverse, numberResolvent_left_inverse⟩
  smoothAlgebra := StarAlgebra.adjoin ℂ {unilateralShift}
  lipschitz a ha := (StarAlgebra.adjoin_le
    (singleton_subset_iff.mpr toeplitz_shift_mem_commutatorBoundedStarSubalgebra) ha).1

theorem toeplitzTriple_shift_mem_smoothAlgebra : unilateralShift ∈ toeplitzTriple.smoothAlgebra :=
  StarAlgebra.subset_adjoin ℂ _ (mem_singleton _)

open RenewalGeometry.SpectralCompressionsSequential
open RenewalGeometry.CompactResolventDiracSpectralScreensExact

/-- Every nonzero finite spectral screen of the Toeplitz triple has `‖[P, S]‖ ≥ 1`. -/
theorem toeplitzTriple_one_le_norm_commutator (s : Finset ℂ)
    (hne : diracSpectralScreen toeplitzTriple s ≠ 0) :
    1 ≤ ‖diracSpectralScreen toeplitzTriple s * unilateralShift -
      unilateralShift * diracSpectralScreen toeplitzTriple s‖ := by
  have := diracSpectralScreen_range_finiteDimensional toeplitzTriple s
  have hidem : (diracSpectralScreen toeplitzTriple s).comp (diracSpectralScreen toeplitzTriple s) =
      diracSpectralScreen toeplitzTriple s := screen_idempotent toeplitzTriple s
  exact one_le_norm_commutator_of_finiteRank_idempotent_commutes_numberOperator
    (diracSpectralScreen toeplitzTriple s)
    (fun n => screen_mem_domain toeplitzTriple s (basisVector n))
    (fun n => diracSpectralScreen_commutes_dirac toeplitzTriple s
      ⟨basisVector n, basisVector_mem_numberOperatorDomain n⟩) hidem hne

/-- **Properness**: the Toeplitz triple (separable, compact resolvent) is not spectrally
quasidiagonal. -/
theorem toeplitzTriple_not_spectrallyQuasidiagonal :
    ¬ SpectrallyQuasidiagonal toeplitzTriple := by
  rintro ⟨P, hP, hdecay⟩
  have hS := hdecay unilateralShift toeplitzTriple_shift_mem_smoothAlgebra
  have hne : ∀ᶠ n in atTop, P n ≠ 0 := by
    filter_upwards [(hP.2.2 (basisVector 0)).eventually (Metric.ball_mem_nhds _ one_pos)]
      with n hn hzero
    rw [hzero, ContinuousLinearMap.zero_apply] at hn
    rw [dist_zero_left, norm_basisVector] at hn
    exact lt_irrefl _ hn
  have hge : ∀ᶠ n in atTop, 1 ≤ ‖P n * unilateralShift - unilateralShift * P n‖ := by
    filter_upwards [hne] with n hn
    obtain ⟨s, hs⟩ := hP.1 n
    rw [hs] at hn ⊢
    exact toeplitzTriple_one_le_norm_commutator s hn
  have hlt := hS.eventually (gt_mem_nhds one_pos)
  obtain ⟨n, h1, h2⟩ := (hge.and hlt).exists
  exact absurd h1 (not_le.mpr h2)

/-- The spectrally quasidiagonal class is a proper subclass of the separable compact-resolvent
spectral triples: the Toeplitz triple is separable and has compact resolvent (so it admits
strong spectral compressions, `spectral_compressions_strong`) but is not spectrally
quasidiagonal, hence admits no norm-multiplicative spectral-compression sequence. -/
theorem spectrallyQuasidiagonal_proper :
    ∃ S : SpectralTriple (H →L[ℂ] H) H, TopologicalSpace.SeparableSpace H ∧
      ¬ SpectrallyQuasidiagonal S ∧ ¬ HasNormMultiplicativeCompression S :=
  ⟨toeplitzTriple, inferInstance, toeplitzTriple_not_spectrallyQuasidiagonal, fun h =>
    toeplitzTriple_not_spectrallyQuasidiagonal
      ((hasNormMultiplicativeCompression_iff_spectrallyQuasidiagonal _).mp h)⟩

end ToeplitzScreenObstruction
end RenewalGeometry
