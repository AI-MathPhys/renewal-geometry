/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Spectral subspaces of Hermitian operators and projector perturbation

Finite-dimensional infrastructure for the perturbation theory of spectral projectors of
self-adjoint (Hermitian) operators, used for `thm:incidence-slice-cluster` and
`thm:certified-support-stratum` of `papers/spacetime_gauge_duality`.

For a symmetric `T : E →ₗ[𝕜] E` on a finite-dimensional inner product space and `S : Set ℝ`,
`spectralSubspace T S = ⨆_{μ ∈ S} ker (T - μ)` is the range of the spectral projector
`𝟙_S(T)`; its orthogonal projection is `(spectralSubspace T S).starProjection`.

* `mem_spectralSubspace_iff`: coordinates in an eigenbasis vanish off `S`;
* `orthogonal_spectralSubspace`: `(𝟙_S(T) E)ᗮ = 𝟙_{Sᶜ}(T) E`;
* quadratic-form and norm bounds on spectral subspaces (`le_re_inner_of_mem`,
  `re_inner_le_of_mem`, strict versions, `norm_apply_le_of_mem`, `le_norm_apply_of_mem`,
  `exists_apply_eq_of_mem`);
* `norm_starProjection_sub_le`: two orthogonal projections are `c`-close in operator norm as
  soon as each range is `c`-close to the other (the `sin Θ` reduction);
* `norm_starProjection_le_swap`: `‖P_B|_A‖ ≤ c → ‖P_A|_B‖ ≤ c` (both are `‖P_B P_A‖`);
* `norm_starProjection_orthogonal_sq_le_of_finrank_eq`: for equal-dimensional ranges a
  one-sided angle bound `a < 1` gives the other side with `a² / (1 - a²)`;
* `hermitian_cluster_projector_perturbation`: **a Davis–Kahan / Riesz bound.** If the
  spectrum of `H` lies in `{0} ∪ [g, ∞)` and `‖H̃ - H‖ ≤ η < g/2`, then
  `rank 𝟙_{[g/2,∞)}(H̃) = rank 𝟙_{(0,∞)}(H)` and
  `‖𝟙_{[g/2,∞)}(H̃) - 𝟙_{(0,∞)}(H)‖ ≤ η / (g - η)`.
-/

open scoped InnerProductSpace
open Module Module.End

noncomputable section

namespace RenewalGeometry
namespace HermitianSpectral

set_option linter.unusedSectionVars false

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]

/-- The spectral subspace `𝟙_S(T) E = ⨆_{μ ∈ S} ker (T - μ)` of an operator `T` for a set of
real spectral parameters `S`.  For symmetric `T` it is the range of the spectral projector
`𝟙_S(T)`. -/
def spectralSubspace (T : E →ₗ[𝕜] E) (S : Set ℝ) : Submodule 𝕜 E :=
  ⨆ μ ∈ S, eigenspace T (μ : 𝕜)

/-- The spectral projector `𝟙_S(T)` as an orthogonal projection. -/
def spectralProjector (T : E →ₗ[𝕜] E) (S : Set ℝ) : E →L[𝕜] E :=
  (spectralSubspace T S).starProjection

theorem eigenspace_le_spectralSubspace (T : E →ₗ[𝕜] E) {S : Set ℝ} {μ : ℝ} (hμ : μ ∈ S) :
    eigenspace T (μ : 𝕜) ≤ spectralSubspace T S :=
  le_iSup₂ (f := fun (μ : ℝ) (_ : μ ∈ S) => eigenspace T (μ : 𝕜)) μ hμ

theorem spectralSubspace_mono (T : E →ₗ[𝕜] E) {S S' : Set ℝ} (h : S ⊆ S') :
    spectralSubspace T S ≤ spectralSubspace T S' :=
  iSup₂_le fun _ hμ => eigenspace_le_spectralSubspace T (h hμ)

variable {T : E →ₗ[𝕜] E} {n : ℕ}

/-- **Coordinates of a spectral subspace.**  In the (sorted) eigenbasis of a symmetric `T`,
`x ∈ 𝟙_S(T) E` iff the coordinates of `x` vanish at every eigenvalue outside `S`. -/
theorem mem_spectralSubspace_iff (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n) {S : Set ℝ}
    {x : E} :
    x ∈ spectralSubspace T S ↔
      ∀ i, hT.eigenvalues hn i ∉ S → (hT.eigenvectorBasis hn).repr x i = 0 := by
  set b := hT.eigenvectorBasis hn
  set ev := hT.eigenvalues hn
  constructor
  · intro hx
    let C : Submodule 𝕜 E :=
      { carrier := {x | ∀ i, ev i ∉ S → b.repr x i = 0}
        add_mem' := by
          intro a c ha hc i hi
          simp [ha i hi, hc i hi]
        zero_mem' := by
          intro i _
          simp
        smul_mem' := by
          intro c a ha i hi
          simp [ha i hi] }
    have hle : spectralSubspace T S ≤ C := by
      refine iSup₂_le fun μ hμ => ?_
      intro v hv i hi
      have hTv : T v = (μ : 𝕜) • v := mem_eigenspace_iff.mp hv
      have h := hT.eigenvectorBasis_apply_self_apply hn v i
      rw [hTv, map_smul] at h
      have h' : ((μ : 𝕜) - (ev i : 𝕜)) * b.repr v i = 0 := by
        rw [sub_mul]
        have : (μ : 𝕜) * b.repr v i = (ev i : 𝕜) * b.repr v i := by
          rw [PiLp.smul_apply, smul_eq_mul] at h
          exact h
        rw [this, sub_self]
      rcases mul_eq_zero.mp h' with h1 | h1
      · exfalso
        apply hi
        have : μ = ev i := by
          have := sub_eq_zero.mp h1
          exact_mod_cast this
        rw [← this]
        exact hμ
      · exact h1
    exact hle hx
  · intro hx
    rw [← b.sum_repr x]
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases hi : ev i ∈ S
    · refine Submodule.smul_mem _ _ (eigenspace_le_spectralSubspace T hi ?_)
      exact mem_eigenspace_iff.mpr (hT.apply_eigenvectorBasis hn i)
    · rw [hx i hi, zero_smul]
      exact zero_mem _

/-- Eigenvectors with eigenvalue in `S` lie in `𝟙_S(T) E`. -/
theorem eigenvectorBasis_mem_spectralSubspace (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n)
    {S : Set ℝ} {i : Fin n} (hi : hT.eigenvalues hn i ∈ S) :
    hT.eigenvectorBasis hn i ∈ spectralSubspace T S :=
  eigenspace_le_spectralSubspace T hi
    (mem_eigenspace_iff.mpr (hT.apply_eigenvectorBasis hn i))

/-- Spectral subspaces only see the eigenvalues: two parameter sets containing the same
eigenvalues give the same subspace. -/
theorem spectralSubspace_congr (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n) {S S' : Set ℝ}
    (h : ∀ i, hT.eigenvalues hn i ∈ S ↔ hT.eigenvalues hn i ∈ S') :
    spectralSubspace T S = spectralSubspace T S' := by
  ext x
  rw [mem_spectralSubspace_iff hT hn, mem_spectralSubspace_iff hT hn]
  exact forall_congr' fun i => by rw [h i]

/-- Spectral subspaces are invariant. -/
theorem apply_mem_spectralSubspace (hT : T.IsSymmetric) {S : Set ℝ} {x : E}
    (hx : x ∈ spectralSubspace T S) : T x ∈ spectralSubspace T S := by
  rw [mem_spectralSubspace_iff hT rfl] at hx ⊢
  intro i hi
  rw [hT.eigenvectorBasis_apply_self_apply rfl, hx i hi, mul_zero]

/-- **Orthogonal complement of a spectral subspace**: `(𝟙_S(T) E)ᗮ = 𝟙_{Sᶜ}(T) E`. -/
theorem orthogonal_spectralSubspace (hT : T.IsSymmetric) (S : Set ℝ) :
    (spectralSubspace T S)ᗮ = spectralSubspace T Sᶜ := by
  set b := hT.eigenvectorBasis rfl
  ext x
  rw [Submodule.mem_orthogonal, mem_spectralSubspace_iff hT rfl]
  constructor
  · intro h i hi
    rw [Set.notMem_compl_iff] at hi
    rw [b.repr_apply_apply]
    exact h _ (eigenvectorBasis_mem_spectralSubspace hT rfl hi)
  · intro h v hv
    rw [mem_spectralSubspace_iff hT rfl] at hv
    rw [← b.repr.inner_map_map, PiLp.inner_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hi : hT.eigenvalues rfl i ∈ S
    · rw [h i (by simpa using hi), inner_zero_right]
    · rw [hv i hi, inner_zero_left]

/-- Spectral subspaces of complementary parameter sets span. -/
theorem spectralSubspace_compl_eq (hT : T.IsSymmetric) (S : Set ℝ) :
    spectralSubspace T Sᶜ = (spectralSubspace T S)ᗮ :=
  (orthogonal_spectralSubspace hT S).symm

/-! ### Coordinate formulas -/

theorem norm_sq_eq_sum_repr (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n) (x : E) :
    ‖x‖ ^ 2 = ∑ i, ‖(hT.eigenvectorBasis hn).repr x i‖ ^ 2 := by
  rw [← (hT.eigenvectorBasis hn).repr.norm_map x, EuclideanSpace.norm_sq_eq]

theorem norm_apply_sq_eq_sum (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n) (x : E) :
    ‖T x‖ ^ 2 = ∑ i, hT.eigenvalues hn i ^ 2 * ‖(hT.eigenvectorBasis hn).repr x i‖ ^ 2 := by
  rw [norm_sq_eq_sum_repr hT hn (T x)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hT.eigenvectorBasis_apply_self_apply hn, norm_mul, mul_pow, RCLike.norm_ofReal, sq_abs]

theorem re_inner_apply_eq_sum (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n) (x : E) :
    RCLike.re ⟪x, T x⟫_𝕜 =
      ∑ i, hT.eigenvalues hn i * ‖(hT.eigenvectorBasis hn).repr x i‖ ^ 2 := by
  rw [← (hT.eigenvectorBasis hn).repr.inner_map_map, PiLp.inner_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hT.eigenvectorBasis_apply_self_apply hn, RCLike.inner_apply', mul_left_comm,
    RCLike.conj_mul, RCLike.re_ofReal_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re]

/-! ### Bounds on spectral subspaces -/

theorem le_re_inner_of_mem (hT : T.IsSymmetric) {S : Set ℝ} {a : ℝ}
    (hS : ∀ μ ∈ S, HasEigenvalue T (μ : 𝕜) → a ≤ μ) {x : E}
    (hx : x ∈ spectralSubspace T S) : a * ‖x‖ ^ 2 ≤ RCLike.re ⟪x, T x⟫_𝕜 := by
  rw [mem_spectralSubspace_iff hT rfl] at hx
  rw [re_inner_apply_eq_sum hT rfl, norm_sq_eq_sum_repr hT rfl, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases hi : hT.eigenvalues rfl i ∈ S
  · exact mul_le_mul_of_nonneg_right (hS _ hi (hT.hasEigenvalue_eigenvalues rfl i))
      (sq_nonneg _)
  · simp [hx i hi]

theorem re_inner_le_of_mem (hT : T.IsSymmetric) {S : Set ℝ} {b : ℝ}
    (hS : ∀ μ ∈ S, HasEigenvalue T (μ : 𝕜) → μ ≤ b) {x : E}
    (hx : x ∈ spectralSubspace T S) : RCLike.re ⟪x, T x⟫_𝕜 ≤ b * ‖x‖ ^ 2 := by
  rw [mem_spectralSubspace_iff hT rfl] at hx
  rw [re_inner_apply_eq_sum hT rfl, norm_sq_eq_sum_repr hT rfl, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  by_cases hi : hT.eigenvalues rfl i ∈ S
  · exact mul_le_mul_of_nonneg_right (hS _ hi (hT.hasEigenvalue_eigenvalues rfl i))
      (sq_nonneg _)
  · simp [hx i hi]

/-- A nonzero vector has a nonzero eigen-coordinate. -/
theorem exists_repr_ne_zero (hT : T.IsSymmetric) {x : E} (hx : x ≠ 0) :
    ∃ i, (hT.eigenvectorBasis rfl).repr x i ≠ 0 := by
  by_contra h
  push Not at h
  apply hx
  have : (hT.eigenvectorBasis rfl).repr x = 0 := by
    ext i
    simp [h i]
  simpa using this

theorem re_inner_lt_of_mem (hT : T.IsSymmetric) {S : Set ℝ} {b : ℝ}
    (hS : ∀ μ ∈ S, HasEigenvalue T (μ : 𝕜) → μ < b) {x : E}
    (hx : x ∈ spectralSubspace T S) (hx0 : x ≠ 0) : RCLike.re ⟪x, T x⟫_𝕜 < b * ‖x‖ ^ 2 := by
  obtain ⟨j, hj⟩ := exists_repr_ne_zero hT hx0
  rw [mem_spectralSubspace_iff hT rfl] at hx
  rw [re_inner_apply_eq_sum hT rfl, norm_sq_eq_sum_repr hT rfl, Finset.mul_sum]
  refine Finset.sum_lt_sum (fun i _ => ?_) ⟨j, Finset.mem_univ _, ?_⟩
  · by_cases hi : hT.eigenvalues rfl i ∈ S
    · exact mul_le_mul_of_nonneg_right (hS _ hi (hT.hasEigenvalue_eigenvalues rfl i)).le
        (sq_nonneg _)
    · simp [hx i hi]
  · have hjS : hT.eigenvalues rfl j ∈ S := by
      by_contra hjS
      exact hj (hx j hjS)
    exact mul_lt_mul_of_pos_right (hS _ hjS (hT.hasEigenvalue_eigenvalues rfl j))
      (by positivity)

theorem lt_re_inner_of_mem (hT : T.IsSymmetric) {S : Set ℝ} {a : ℝ}
    (hS : ∀ μ ∈ S, HasEigenvalue T (μ : 𝕜) → a < μ) {x : E}
    (hx : x ∈ spectralSubspace T S) (hx0 : x ≠ 0) : a * ‖x‖ ^ 2 < RCLike.re ⟪x, T x⟫_𝕜 := by
  obtain ⟨j, hj⟩ := exists_repr_ne_zero hT hx0
  rw [mem_spectralSubspace_iff hT rfl] at hx
  rw [re_inner_apply_eq_sum hT rfl, norm_sq_eq_sum_repr hT rfl, Finset.mul_sum]
  refine Finset.sum_lt_sum (fun i _ => ?_) ⟨j, Finset.mem_univ _, ?_⟩
  · by_cases hi : hT.eigenvalues rfl i ∈ S
    · exact mul_le_mul_of_nonneg_right (hS _ hi (hT.hasEigenvalue_eigenvalues rfl i)).le
        (sq_nonneg _)
    · simp [hx i hi]
  · have hjS : hT.eigenvalues rfl j ∈ S := by
      by_contra hjS
      exact hj (hx j hjS)
    exact mul_lt_mul_of_pos_right (hS _ hjS (hT.hasEigenvalue_eigenvalues rfl j))
      (by positivity)

theorem norm_apply_le_of_mem (hT : T.IsSymmetric) {S : Set ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hS : ∀ μ ∈ S, HasEigenvalue T (μ : 𝕜) → |μ| ≤ c) {x : E}
    (hx : x ∈ spectralSubspace T S) : ‖T x‖ ≤ c * ‖x‖ := by
  rw [mem_spectralSubspace_iff hT rfl] at hx
  have h2 : ‖T x‖ ^ 2 ≤ (c * ‖x‖) ^ 2 := by
    rw [norm_apply_sq_eq_sum hT rfl, mul_pow, norm_sq_eq_sum_repr hT rfl, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    by_cases hi : hT.eigenvalues rfl i ∈ S
    · refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      have := hS _ hi (hT.hasEigenvalue_eigenvalues rfl i)
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) this 2
    · simp [hx i hi]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h2

theorem le_norm_apply_of_mem (hT : T.IsSymmetric) {S : Set ℝ} {a : ℝ} (ha : 0 ≤ a)
    (hS : ∀ μ ∈ S, HasEigenvalue T (μ : 𝕜) → a ≤ |μ|) {x : E}
    (hx : x ∈ spectralSubspace T S) : a * ‖x‖ ≤ ‖T x‖ := by
  rw [mem_spectralSubspace_iff hT rfl] at hx
  have h2 : (a * ‖x‖) ^ 2 ≤ ‖T x‖ ^ 2 := by
    rw [norm_apply_sq_eq_sum hT rfl, mul_pow, norm_sq_eq_sum_repr hT rfl, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    by_cases hi : hT.eigenvalues rfl i ∈ S
    · refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      have := hS _ hi (hT.hasEigenvalue_eigenvalues rfl i)
      rw [← sq_abs (hT.eigenvalues rfl i)]
      exact pow_le_pow_left₀ ha this 2
    · simp [hx i hi]
  exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).mp h2

/-- On a spectral subspace avoiding `0`, `T` is onto. -/
theorem exists_apply_eq_of_mem (hT : T.IsSymmetric) {S : Set ℝ}
    (hS : ∀ μ ∈ S, HasEigenvalue T (μ : 𝕜) → μ ≠ 0) {x : E}
    (hx : x ∈ spectralSubspace T S) : ∃ z ∈ spectralSubspace T S, T z = x := by
  set b := hT.eigenvectorBasis rfl
  set ev := hT.eigenvalues rfl
  have hx' := (mem_spectralSubspace_iff hT rfl).mp hx
  refine ⟨∑ i, (((ev i : 𝕜))⁻¹ * b.repr x i) • b i, ?_, ?_⟩
  · refine Submodule.sum_mem _ fun i _ => ?_
    by_cases hi : ev i ∈ S
    · exact Submodule.smul_mem _ _ (eigenvectorBasis_mem_spectralSubspace hT rfl hi)
    · rw [hx' i hi, mul_zero, zero_smul]
      exact zero_mem _
  · rw [map_sum]
    conv_rhs => rw [← b.sum_repr x]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hT.apply_eigenvectorBasis rfl i, smul_smul]
    by_cases hi : ev i ∈ S
    · have hne : (ev i : 𝕜) ≠ 0 := by
        exact_mod_cast hS _ hi (hT.hasEigenvalue_eigenvalues rfl i)
      congr 1
      field_simp
      exact mul_comm _ _
    · have h0 : b.repr x i = 0 := hx' i hi
      simp [h0]

/-- Eigenvalues inherit lower quadratic-form bounds. -/
theorem le_of_hasEigenvalue_of_forall_le {m μ : ℝ}
    (h : ∀ x, m * ‖x‖ ^ 2 ≤ RCLike.re ⟪x, T x⟫_𝕜) (hμ : HasEigenvalue T (μ : 𝕜)) : m ≤ μ := by
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hv0 : v ≠ 0 := hv.2
  have hTv : T v = (μ : 𝕜) • v := mem_eigenspace_iff.mp hv.1
  have h1 := h v
  rw [hTv, inner_smul_right, RCLike.re_ofReal_mul, inner_self_eq_norm_sq] at h1
  have hpos : 0 < ‖v‖ ^ 2 := by positivity
  nlinarith

/-- Lower bound on the dimension of a subspace containing chosen eigenvectors. -/
theorem card_le_finrank_of_eigenvectorBasis_mem (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n)
    (V : Submodule 𝕜 E) (I : Finset (Fin n))
    (hI : ∀ i ∈ I, hT.eigenvectorBasis hn i ∈ V) : I.card ≤ finrank 𝕜 V := by
  have hli : LinearIndependent 𝕜 (fun i : I => hT.eigenvectorBasis hn i) :=
    (hT.eigenvectorBasis hn).orthonormal.linearIndependent.comp _ Subtype.val_injective
  have hspan : Submodule.span 𝕜 (Set.range fun i : I => hT.eigenvectorBasis hn i) ≤ V := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact hI i i.2
  have := Submodule.finrank_mono hspan
  rw [finrank_span_eq_card hli, Fintype.card_coe] at this
  exact this

/-! ### Dimension counting -/

/-- Two subspaces meeting only at `0` have total dimension at most `dim E`. -/
theorem finrank_add_finrank_le_of_inf_eq_bot (V W : Submodule 𝕜 E)
    (h : ∀ x ∈ V, x ∈ W → x = 0) : finrank 𝕜 V + finrank 𝕜 W ≤ finrank 𝕜 E := by
  have hinf : V ⊓ W = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    exact (Submodule.mem_bot 𝕜).mpr (h x hx.1 hx.2)
  have := Submodule.finrank_sup_add_finrank_inf_eq V W
  rw [hinf, finrank_bot, add_zero] at this
  rw [← this]
  exact Submodule.finrank_le _

/-- Two subspaces of total dimension exceeding `dim E` share a nonzero vector. -/
theorem exists_ne_zero_mem_of_finrank_lt (V W : Submodule 𝕜 E)
    (h : finrank 𝕜 E < finrank 𝕜 V + finrank 𝕜 W) : ∃ x ∈ V, x ∈ W ∧ x ≠ 0 := by
  by_contra hc
  push Not at hc
  exact absurd (finrank_add_finrank_le_of_inf_eq_bot V W hc) (not_le.mpr h)

/-! ### Pairs of orthogonal projections -/

theorem norm_sq_starProjection_eq_re_inner (K : Submodule 𝕜 E) (u : E) :
    ‖K.starProjection u‖ ^ 2 = RCLike.re ⟪K.starProjection u, u⟫_𝕜 := by
  have h1 : ⟪K.starProjection u, K.starProjection u⟫_𝕜 = ⟪K.starProjection u, u⟫_𝕜 := by
    rw [Submodule.inner_starProjection_left_eq_right,
      Submodule.starProjection_eq_self_iff.mpr (K.starProjection_apply_mem u)]
    exact (Submodule.inner_starProjection_left_eq_right K u u).symm
  rw [← h1, inner_self_eq_norm_sq]

/-- **Swap of one-sided angle bounds.**  `‖P_A y‖ ≤ c ‖y‖` on `B` implies `‖P_B x‖ ≤ c ‖x‖`
on `A` (both say `‖P_B P_A‖ ≤ c`). -/
theorem norm_starProjection_le_swap (A B : Submodule 𝕜 E) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ y ∈ B, ‖A.starProjection y‖ ≤ c * ‖y‖) :
    ∀ x ∈ A, ‖B.starProjection x‖ ≤ c * ‖x‖ := by
  intro x hx
  set w := B.starProjection x
  have hw : w ∈ B := B.starProjection_apply_mem x
  have hsq : ‖w‖ ^ 2 ≤ c * ‖w‖ * ‖x‖ := by
    rw [norm_sq_starProjection_eq_re_inner]
    have : ⟪w, x⟫_𝕜 = ⟪A.starProjection w, x⟫_𝕜 := by
      rw [Submodule.inner_starProjection_left_eq_right A w x,
        Submodule.starProjection_eq_self_iff.mpr hx]
    rw [this]
    calc RCLike.re ⟪A.starProjection w, x⟫_𝕜 ≤ ‖A.starProjection w‖ * ‖x‖ :=
          (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
      _ ≤ c * ‖w‖ * ‖x‖ := mul_le_mul_of_nonneg_right (h w hw) (norm_nonneg _)
  rcases (norm_nonneg w).eq_or_lt with h0 | h0
  · rw [← h0]
    positivity
  · nlinarith [norm_nonneg x]

/-- **Two orthogonal projections are close when their ranges are mutually close.**
If `‖P_{Wᗮ} u‖ ≤ c ‖u‖` on `U` and `‖P_{Uᗮ} w‖ ≤ c ‖w‖` on `W`, then `‖P_U - P_W‖ ≤ c`. -/
theorem norm_starProjection_sub_le (U W : Submodule 𝕜 E) {c : ℝ} (hc : 0 ≤ c)
    (h1 : ∀ u ∈ U, ‖Wᗮ.starProjection u‖ ≤ c * ‖u‖)
    (h2 : ∀ w ∈ W, ‖Uᗮ.starProjection w‖ ≤ c * ‖w‖) :
    ‖U.starProjection - W.starProjection‖ ≤ c := by
  have h1' := norm_starProjection_le_swap Wᗮ U hc h1
  refine ContinuousLinearMap.opNorm_le_bound _ hc fun x => ?_
  set w := W.starProjection x
  set a := Wᗮ.starProjection x
  have ha : a ∈ Wᗮ := Wᗮ.starProjection_apply_mem x
  have hw : w ∈ W := W.starProjection_apply_mem x
  have hxa : x = w + a := by
    simp only [a, w, Submodule.starProjection_orthogonal_val]
    abel
  have hdec : (U.starProjection - W.starProjection) x =
      U.starProjection a + -(Uᗮ.starProjection w) := by
    rw [ContinuousLinearMap.sub_apply, Submodule.starProjection_orthogonal_val]
    show U.starProjection x - w = _
    conv_lhs => rw [hxa]
    rw [map_add]
    abel
  have horth : ⟪U.starProjection a, -(Uᗮ.starProjection w)⟫_𝕜 = 0 := by
    rw [inner_neg_right, neg_eq_zero]
    have := (Submodule.mem_orthogonal _ _).mp (Uᗮ.starProjection_apply_mem w) _
      (U.starProjection_apply_mem a)
    exact this
  have hpy := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
  rw [norm_neg] at hpy
  have hx2 : ‖x‖ ^ 2 = ‖w‖ ^ 2 + ‖a‖ ^ 2 := Submodule.norm_sq_eq_add_norm_sq_starProjection x W
  have e1 := h1' a ha
  have e2 := h2 w hw
  have hsq : ‖(U.starProjection - W.starProjection) x‖ ^ 2 ≤ (c * ‖x‖) ^ 2 := by
    rw [hdec, sq, hpy, mul_pow, hx2]
    have := mul_self_le_mul_self (norm_nonneg _) e1
    have := mul_self_le_mul_self (norm_nonneg _) e2
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hsq

/-- **Equal dimensions transfer a one-sided angle bound.**  If `dim U = dim W` and
`‖P_{Wᗮ} u‖ ≤ a ‖u‖` on `U` with `a < 1`, then `(1 - a²) ‖P_{Uᗮ} w‖² ≤ a² ‖w‖²` on `W`. -/
theorem norm_starProjection_orthogonal_sq_le_of_finrank_eq (U W : Submodule 𝕜 E)
    (hdim : finrank 𝕜 U = finrank 𝕜 W) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1)
    (h : ∀ u ∈ U, ‖Wᗮ.starProjection u‖ ≤ a * ‖u‖) :
    ∀ w ∈ W, (1 - a ^ 2) * ‖Uᗮ.starProjection w‖ ^ 2 ≤ a ^ 2 * ‖w‖ ^ 2 := by
  let f : U →ₗ[𝕜] W := W.orthogonalProjectionOnto.toLinearMap ∘ₗ U.subtype
  have hfapply : ∀ u : U, ((f u : W) : E) = W.starProjection (u : E) := fun u => rfl
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro u hu
    rw [LinearMap.mem_ker] at hu
    have hu' : W.starProjection (u : E) = 0 := by
      rw [← hfapply, hu]
      rfl
    have hb := h u u.2
    rw [Submodule.starProjection_orthogonal_val, hu', sub_zero] at hb
    have : ‖(u : E)‖ = 0 := by
      have := norm_nonneg (u : E)
      nlinarith
    rw [Submodule.mem_bot]
    exact Subtype.ext (by simpa using this)
  have hsurj : Function.Surjective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hf
  intro w hw
  obtain ⟨u, hu⟩ := hsurj ⟨w, hw⟩
  have hWu : W.starProjection (u : E) = w := by
    rw [← hfapply, hu]
  have hperp : Wᗮ.starProjection (u : E) = (u : E) - w := by
    rw [Submodule.starProjection_orthogonal_val, hWu]
  have hb := h u u.2
  rw [hperp] at hb
  have hUu : Uᗮ.starProjection (u : E) = 0 := by
    rw [Submodule.starProjection_orthogonal_val, Submodule.starProjection_eq_self_iff.mpr u.2,
      sub_self]
  have e1 : ‖Uᗮ.starProjection w‖ ≤ a * ‖(u : E)‖ := by
    have : Uᗮ.starProjection w = Uᗮ.starProjection (w - (u : E)) := by
      rw [map_sub, hUu, sub_zero]
    rw [this]
    refine (Submodule.norm_starProjection_apply_le _ _).trans ?_
    rw [norm_sub_rev]
    exact hb
  have hpy : ‖(u : E)‖ ^ 2 = ‖w‖ ^ 2 + ‖(u : E) - w‖ ^ 2 := by
    have := Submodule.norm_sq_eq_add_norm_sq_starProjection (u : E) W
    rwa [hWu, hperp] at this
  have e2 : ‖(u : E) - w‖ ^ 2 ≤ a ^ 2 * ‖(u : E)‖ ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hb 2
  have e1' : ‖Uᗮ.starProjection w‖ ^ 2 ≤ a ^ 2 * ‖(u : E)‖ ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) e1 2
  have h1a : 0 ≤ 1 - a ^ 2 := by nlinarith
  have hu2 : (1 - a ^ 2) * ‖(u : E)‖ ^ 2 ≤ ‖w‖ ^ 2 := by nlinarith
  calc (1 - a ^ 2) * ‖Uᗮ.starProjection w‖ ^ 2 ≤ (1 - a ^ 2) * (a ^ 2 * ‖(u : E)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left e1' h1a
    _ = a ^ 2 * ((1 - a ^ 2) * ‖(u : E)‖ ^ 2) := by ring
    _ ≤ a ^ 2 * ‖w‖ ^ 2 := mul_le_mul_of_nonneg_left hu2 (sq_nonneg _)

/-! ### Further structure of spectral subspaces -/

theorem mem_spectralSubspace_univ (hT : T.IsSymmetric) (x : E) :
    x ∈ spectralSubspace T Set.univ := by
  rw [mem_spectralSubspace_iff hT rfl]
  intro i hi
  exact absurd (Set.mem_univ _) hi

/-- Orthogonal projections onto reducing subspaces commute with the operator. -/
theorem starProjection_apply_comm_of_invariant (V : Submodule 𝕜 E)
    (h1 : ∀ v ∈ V, T v ∈ V) (h2 : ∀ v ∈ Vᗮ, T v ∈ Vᗮ) (z : E) :
    V.starProjection (T z) = T (V.starProjection z) := by
  have hz : z = V.starProjection z + Vᗮ.starProjection z := by
    rw [Submodule.starProjection_orthogonal_val]
    abel
  refine Submodule.eq_starProjection_of_mem_orthogonal'
    (h1 _ (V.starProjection_apply_mem z))
    (z := T (Vᗮ.starProjection z)) (h2 _ (Vᗮ.starProjection_apply_mem z)) ?_
  conv_lhs => rw [hz]
  rw [map_add]

/-- Spectral subspaces reduce the operator. -/
theorem apply_mem_orthogonal_spectralSubspace (hT : T.IsSymmetric) {S : Set ℝ} {x : E}
    (hx : x ∈ (spectralSubspace T S)ᗮ) : T x ∈ (spectralSubspace T S)ᗮ := by
  rw [orthogonal_spectralSubspace hT] at hx ⊢
  exact apply_mem_spectralSubspace hT hx

/-- Spectral projectors commute with the operator. -/
theorem starProjection_spectralSubspace_apply (hT : T.IsSymmetric) (S : Set ℝ) (z : E) :
    (spectralSubspace T S).starProjection (T z) =
      T ((spectralSubspace T S).starProjection z) :=
  starProjection_apply_comm_of_invariant _ (fun _ hv => apply_mem_spectralSubspace hT hv)
    (fun _ hv => apply_mem_orthogonal_spectralSubspace hT hv) z

/-- Real part of the quadratic form under a perturbation of operator size `η`. -/
theorem abs_re_inner_sub_le {H H' : E →ₗ[𝕜] E} {η : ℝ} (hpert : ∀ x, ‖(H' - H) x‖ ≤ η * ‖x‖)
    (x : E) : |RCLike.re ⟪x, H' x⟫_𝕜 - RCLike.re ⟪x, H x⟫_𝕜| ≤ η * ‖x‖ ^ 2 := by
  have : RCLike.re ⟪x, H' x⟫_𝕜 - RCLike.re ⟪x, H x⟫_𝕜 = RCLike.re ⟪x, (H' - H) x⟫_𝕜 := by
    rw [LinearMap.sub_apply, inner_sub_right, map_sub]
  rw [this]
  calc |RCLike.re ⟪x, (H' - H) x⟫_𝕜| ≤ ‖⟪x, (H' - H) x⟫_𝕜‖ := RCLike.abs_re_le_norm _
    _ ≤ ‖x‖ * ‖(H' - H) x‖ := norm_inner_le_norm _ _
    _ ≤ ‖x‖ * (η * ‖x‖) := mul_le_mul_of_nonneg_left (hpert x) (norm_nonneg _)
    _ = η * ‖x‖ ^ 2 := by ring

/-! ### The cluster projector perturbation theorem -/

/-- **Hermitian cluster projector perturbation (Davis–Kahan / Riesz bound).**
Let `H` be symmetric with spectrum in `{0} ∪ [g, ∞)` (`g > 0`), and `H'` symmetric with
`‖H' - H‖ ≤ η < g / 2`.  Put `P = 𝟙_{(0,∞)}(H)` and `P' = 𝟙_{[g/2,∞)}(H')`.  Then
* `rank P' = rank P`;
* the spectral subspace of `H'` above `g/2` is already its spectral subspace above `g - η`
  and above `η` (the perturbed cluster stays in `[g - η, ∞)`, the rest in `[-η, η]`);
* `‖P' - P‖ ≤ η / (g - η)`. -/
theorem hermitian_cluster_projector_perturbation {H H' : E →ₗ[𝕜] E} (hH : H.IsSymmetric)
    (hH' : H'.IsSymmetric) {g η : ℝ} (hg : 0 < g) (hη0 : 0 ≤ η) (hη : η < g / 2)
    (hspec : ∀ μ : ℝ, HasEigenvalue H (μ : 𝕜) → μ = 0 ∨ g ≤ μ)
    (hpert : ∀ x, ‖(H' - H) x‖ ≤ η * ‖x‖) :
    finrank 𝕜 (spectralSubspace H' (Set.Ici (g / 2))) =
        finrank 𝕜 (spectralSubspace H (Set.Ioi 0)) ∧
      spectralSubspace H' (Set.Ici (g / 2)) = spectralSubspace H' (Set.Ici (g - η)) ∧
      spectralSubspace H' (Set.Ici (g / 2)) = spectralSubspace H' (Set.Ioi η) ∧
      ‖spectralProjector H' (Set.Ici (g / 2)) - spectralProjector H (Set.Ioi 0)‖ ≤
        η / (g - η) := by
  set U := spectralSubspace H (Set.Ioi 0) with hUdef
  set U' := spectralSubspace H' (Set.Ici (g / 2)) with hU'def
  have hgη : 0 < g - η := by linarith
  -- eigenvalues of `H` are nonnegative
  have hHev_nonneg : ∀ μ : ℝ, HasEigenvalue H (μ : 𝕜) → 0 ≤ μ := by
    intro μ hμ
    rcases hspec μ hμ with h | h
    · exact h.ge
    · linarith
  -- (F1) lower bound on `U`
  have hF1 : ∀ x ∈ U, g * ‖x‖ ^ 2 ≤ RCLike.re ⟪x, H x⟫_𝕜 := fun x hx =>
    le_re_inner_of_mem hH (fun μ hμ he => by
      rcases hspec μ he with h | h
      · exact absurd h (ne_of_gt hμ)
      · exact h) hx
  -- `Uᗮ = 𝟙_{(-∞,0]}(H)` is the kernel
  have hUperp : Uᗮ = spectralSubspace H (Set.Iic 0) := by
    rw [hUdef, orthogonal_spectralSubspace hH, Set.compl_Ioi]
  have hF2 : ∀ x ∈ Uᗮ, H x = 0 := by
    intro x hx
    rw [hUperp] at hx
    have := norm_apply_le_of_mem hH le_rfl (fun μ hμ he => by
      have h0 := hHev_nonneg μ he
      have : μ = 0 := le_antisymm hμ h0
      simp [this]) hx
    simpa using this
  -- `H` maps into `U`
  have hHU : ∀ z, H z ∈ U := by
    intro z
    have hz : z = U.starProjection z + Uᗮ.starProjection z := by
      rw [Submodule.starProjection_orthogonal_val]
      abel
    rw [hz, map_add, hF2 _ (Uᗮ.starProjection_apply_mem z), add_zero]
    exact apply_mem_spectralSubspace hH (U.starProjection_apply_mem z)
  -- quadratic-form perturbation
  have hF3 := abs_re_inner_sub_le hpert
  have hHnonneg : ∀ x, 0 ≤ RCLike.re ⟪x, H x⟫_𝕜 := fun x => by
    have := le_re_inner_of_mem hH (S := Set.univ) (a := 0)
      (fun μ _ he => hHev_nonneg μ he) (mem_spectralSubspace_univ hH x)
    simpa using this
  have hH'lower : ∀ x, -η * ‖x‖ ^ 2 ≤ RCLike.re ⟪x, H' x⟫_𝕜 := fun x => by
    have h1 := hF3 x
    have h2 := hHnonneg x
    have := (abs_le.mp h1).1
    nlinarith
  have hH'ev : ∀ μ : ℝ, HasEigenvalue H' (μ : 𝕜) → -η ≤ μ := fun μ hμ =>
    le_of_hasEigenvalue_of_forall_le hH'lower hμ
  -- dimension of `U` and its complement
  have hdimU : finrank 𝕜 U + finrank 𝕜 Uᗮ = finrank 𝕜 E := Submodule.finrank_add_finrank_orthogonal U
  -- (F5) the subspace of `H'` above `η` misses the kernel of `H`
  set W' := spectralSubspace H' (Set.Ioi η) with hW'def
  have hF5 : finrank 𝕜 W' ≤ finrank 𝕜 U := by
    have := finrank_add_finrank_le_of_inf_eq_bot W' Uᗮ (fun x hx hxK => by
      by_contra hx0
      have h1 := lt_re_inner_of_mem hH' (fun μ hμ _ => hμ) hx hx0
      have h2 := hF3 x
      have hHx : H x = 0 := hF2 x hxK
      rw [hHx, inner_zero_right, map_zero, sub_zero] at h2
      have := (abs_le.mp h2).2
      linarith)
    omega
  -- (F6) the subspace of `H'` below `g - η` misses `U`
  set L := spectralSubspace H' (Set.Iio (g - η)) with hLdef
  set M := spectralSubspace H' (Set.Ici (g - η)) with hMdef
  have hF6 : finrank 𝕜 U ≤ finrank 𝕜 M := by
    have h1 := finrank_add_finrank_le_of_inf_eq_bot L U (fun x hxL hxU => by
      by_contra hx0
      have h1 := re_inner_lt_of_mem hH' (fun μ hμ _ => hμ) hxL hx0
      have h2 := hF1 x hxU
      have h3 := (abs_le.mp (hF3 x)).1
      linarith)
    have hLM : Lᗮ = M := by
      rw [hLdef, hMdef, orthogonal_spectralSubspace hH', Set.compl_Iio]
    have h2 := Submodule.finrank_add_finrank_orthogonal L
    rw [hLM] at h2
    omega
  -- (F7) the nested chain `M ≤ U' ≤ W'` has constant dimension
  have hMU' : M ≤ U' := spectralSubspace_mono H' (Set.Ici_subset_Ici.mpr (by linarith))
  have hU'W' : U' ≤ W' := spectralSubspace_mono H' (fun x hx => by
    simp only [Set.mem_Ici] at hx
    simp only [Set.mem_Ioi]
    linarith)
  have hdM := Submodule.finrank_mono hMU'
  have hdU' := Submodule.finrank_mono hU'W'
  have hdimU' : finrank 𝕜 U' = finrank 𝕜 U := by omega
  have hU'M : U' = M := (Submodule.eq_of_le_of_finrank_eq hMU' (by omega)).symm
  have hU'W'eq : U' = W' := Submodule.eq_of_le_of_finrank_eq hU'W' (by omega)
  refine ⟨hdimU', hU'M, hU'W'eq, ?_⟩
  -- (F9) on `U'ᗮ`, `‖H' x‖ ≤ η ‖x‖`
  have hU'perp : U'ᗮ = spectralSubspace H' (Set.Iic η) := by
    rw [hU'W'eq, hW'def, orthogonal_spectralSubspace hH', Set.compl_Ioi]
  have hF9 : ∀ x ∈ U'ᗮ, ‖H' x‖ ≤ η * ‖x‖ := by
    intro x hx
    rw [hU'perp] at hx
    exact norm_apply_le_of_mem hH' hη0 (fun μ hμ he => abs_le.mpr ⟨by
      have := hH'ev μ he
      linarith, hμ⟩) hx
  set c := η / (g - η) with hc
  have hc0 : 0 ≤ c := div_nonneg hη0 hgη.le
  -- (F10) `U'` is close to `U`
  have hF10 : ∀ u ∈ U', ‖Uᗮ.starProjection u‖ ≤ c * ‖u‖ := by
    intro u hu
    have huM : u ∈ M := hU'M ▸ hu
    obtain ⟨z, hzM, rfl⟩ := exists_apply_eq_of_mem hH' (fun μ hμ _ => by
      simp only [Set.mem_Ici] at hμ
      exact ne_of_gt (lt_of_lt_of_le hgη hμ)) huM
    have hz : (g - η) * ‖z‖ ≤ ‖H' z‖ := le_norm_apply_of_mem hH' hgη.le (fun μ hμ _ => by
      simp only [Set.mem_Ici] at hμ
      rw [abs_of_nonneg (by linarith)]
      exact hμ) hzM
    have hsplit : H' z = (H' - H) z + H z := by
      rw [LinearMap.sub_apply]
      abel
    have hzero : Uᗮ.starProjection (H z) = 0 := by
      rw [Submodule.starProjection_orthogonal_val,
        Submodule.starProjection_eq_self_iff.mpr (hHU z), sub_self]
    have h1 : ‖Uᗮ.starProjection (H' z)‖ ≤ η * ‖z‖ := by
      rw [hsplit, map_add, hzero, add_zero]
      exact (Submodule.norm_starProjection_apply_le _ _).trans (hpert z)
    calc ‖Uᗮ.starProjection (H' z)‖ ≤ η * ‖z‖ := h1
      _ = c * ((g - η) * ‖z‖) := by
        rw [hc]
        field_simp
      _ ≤ c * ‖H' z‖ := mul_le_mul_of_nonneg_left hz hc0
  -- (F11) `U` is close to `U'`
  have hF11 : ∀ w ∈ U, ‖U'ᗮ.starProjection w‖ ≤ c * ‖w‖ := by
    set N := ‖U'ᗮ.starProjection.comp U.starProjection‖ with hN
    have hN0 : 0 ≤ N := norm_nonneg _
    have hbound : ∀ x, ‖(U'ᗮ.starProjection.comp U.starProjection) x‖ ≤
        (η * (1 + N) / g) * ‖x‖ := by
      intro x
      rw [ContinuousLinearMap.comp_apply]
      set u := U.starProjection x
      have huU : u ∈ U := U.starProjection_apply_mem x
      obtain ⟨z, hzU, hzu⟩ := exists_apply_eq_of_mem hH (fun μ hμ _ => ne_of_gt hμ) huU
      have hz : g * ‖z‖ ≤ ‖H z‖ := le_norm_apply_of_mem hH hg.le (fun μ hμ he => by
        rcases hspec μ he with h | h
        · exact absurd h (ne_of_gt hμ)
        · rw [abs_of_nonneg (by linarith)]
          exact h) hzU
      rw [hzu] at hz
      have hsplit : H z = (H - H') z + H' z := by
        rw [LinearMap.sub_apply]
        abel
      have hcomm : U'ᗮ.starProjection (H' z) = H' (U'ᗮ.starProjection z) := by
        refine starProjection_apply_comm_of_invariant _ (fun v hv => ?_) (fun v hv => ?_) z
        · exact apply_mem_orthogonal_spectralSubspace hH' hv
        · rw [Submodule.orthogonal_orthogonal] at hv ⊢
          exact apply_mem_spectralSubspace hH' hv
      have hpz : U'ᗮ.starProjection z =
          (U'ᗮ.starProjection.comp U.starProjection) z := by
        have hzz : U.starProjection z = z := Submodule.starProjection_eq_self_iff.mpr hzU
        rw [ContinuousLinearMap.comp_apply, hzz]
      have e1 : ‖U'ᗮ.starProjection ((H - H') z)‖ ≤ η * ‖z‖ := by
        refine (Submodule.norm_starProjection_apply_le _ _).trans ?_
        have : (H - H') z = -((H' - H) z) := by
          simp only [LinearMap.sub_apply, neg_sub]
        rw [this, norm_neg]
        exact hpert z
      have e2 : ‖H' (U'ᗮ.starProjection z)‖ ≤ η * (N * ‖z‖) := by
        refine (hF9 _ (U'ᗮ.starProjection_apply_mem z)).trans ?_
        refine mul_le_mul_of_nonneg_left ?_ hη0
        rw [hpz]
        exact ContinuousLinearMap.le_opNorm _ _
      have e3 : ‖U'ᗮ.starProjection u‖ ≤ η * (1 + N) * ‖z‖ := by
        rw [← hzu, hsplit, map_add, hcomm]
        calc ‖U'ᗮ.starProjection ((H - H') z) + H' (U'ᗮ.starProjection z)‖
            ≤ ‖U'ᗮ.starProjection ((H - H') z)‖ + ‖H' (U'ᗮ.starProjection z)‖ :=
              norm_add_le _ _
          _ ≤ η * ‖z‖ + η * (N * ‖z‖) := add_le_add e1 e2
          _ = η * (1 + N) * ‖z‖ := by ring
      have hux : ‖u‖ ≤ ‖x‖ := Submodule.norm_starProjection_apply_le _ _
      have hzx : ‖z‖ ≤ ‖x‖ / g := by
        rw [le_div_iff₀ hg]
        nlinarith
      calc ‖U'ᗮ.starProjection u‖ ≤ η * (1 + N) * ‖z‖ := e3
        _ ≤ η * (1 + N) * (‖x‖ / g) :=
            mul_le_mul_of_nonneg_left hzx (by positivity)
        _ = η * (1 + N) / g * ‖x‖ := by ring
    have hNle : N ≤ η * (1 + N) / g :=
      ContinuousLinearMap.opNorm_le_bound _ (by positivity) hbound
    have hNc : N ≤ c := by
      rw [hc, le_div_iff₀ hgη]
      rw [le_div_iff₀ hg] at hNle
      nlinarith
    intro w hw
    have : U'ᗮ.starProjection w = (U'ᗮ.starProjection.comp U.starProjection) w := by
      have hww : U.starProjection w = w := Submodule.starProjection_eq_self_iff.mpr hw
      rw [ContinuousLinearMap.comp_apply, hww]
    rw [this]
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right hNc (norm_nonneg _))
  exact norm_starProjection_sub_le U' U hc0 hF10 hF11

end HermitianSpectral
end RenewalGeometry
