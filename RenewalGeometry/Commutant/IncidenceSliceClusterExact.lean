/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Commutant.IncidenceSliceGramExact
import RenewalGeometry.Analysis.CertifiedSupportStratumExact

/-!
# Stable dominant coefficient space under incidence error (`thm:incidence-slice-cluster`)

For a represented incidence `Y ∈ B(K_s, K_t) ⊗ B(M_s, M_t)`, written as
`Y : Matrix (K_t × M_t) (K_s × M_s) ℂ`, the slice map `𝒮_Y` is, in Hilbert–Schmidt orthonormal
matrix-unit coordinates, the realignment `realign Y` (`IncidenceSliceGramExact.lean`).  Its
singular values are the operator–Schmidt coefficients `σ_k(Y)` of `Y` (zero-indexed:
`schmidtCoeff Y k = σ_{k+1}`), the operator–Schmidt rank is `rank 𝒮_Y`, and the slice Gram
`H_Y = 𝒮_Y 𝒮_Y^*` is `sliceGram Y` (`sliceGramOp_eq`).  `finrank_range_sliceMap_schmidt`
checks that for an operator–Schmidt decomposition `Y = ∑_{k ∈ ι} σ_k D_k ⊗ F_k` the rank of
`𝒮_Y` is `#ι`.

`incidence_slice_cluster`: if `Y` has operator–Schmidt rank `r`, nonzero Schmidt coefficients
`≥ s > 0`, all coefficients `≤ L`, and `‖Ỹ - Y‖_HS ≤ ε`, then
* `|σ_k(Ỹ) - σ_k(Y)| ≤ ε` for every `k` (`eq:incidence-Schmidt-Weyl`);
* if `ε < s/2`, the first `r` coefficients of `Ỹ` exceed `s/2` and the others are below it
  (an `r`-dimensional dominant cluster);
* `‖H_Ỹ - H_Y‖_op ≤ η = (2L + ε) ε`;
* if `η < s²/2`, then with `P = 𝟙_{(0,∞)}(H_Y)` and `P̃ = 𝟙_{[s²/2,∞)}(H_Ỹ)`,
  `rank P̃ = r` and `‖P̃ - P‖_op ≤ η / (s² - η)` (`eq:incidence-slice-projector`).
-/

open scoped InnerProductSpace
open Module Module.End Matrix
open RenewalGeometry.HermitianSpectral RenewalGeometry.SingularSubspace

noncomputable section

namespace RenewalGeometry
namespace IncidenceSliceCluster

open IncidenceSliceGram

set_option linter.unusedSectionVars false

variable {Kt Ks Mt Ms : Type*} [Fintype Kt] [Fintype Ks] [Fintype Mt] [Fintype Ms]
  [DecidableEq Kt] [DecidableEq Ks] [DecidableEq Mt] [DecidableEq Ms]

/-- The slice map `𝒮_Y : B(K_s, K_t) → B(M_s, M_t)` in Hilbert–Schmidt orthonormal coordinates. -/
def sliceMap (Y : Matrix (Kt × Mt) (Ks × Ms) ℂ) :
    EuclideanSpace ℂ (Kt × Ks) →ₗ[ℂ] EuclideanSpace ℂ (Mt × Ms) :=
  Matrix.toEuclideanLin (realign Y)

/-- The operator–Schmidt coefficients of `Y` (zero-indexed, decreasing): the singular values of
the slice map. -/
def schmidtCoeff (Y : Matrix (Kt × Mt) (Ks × Ms) ℂ) (k : ℕ) : ℝ :=
  (sliceMap Y).singularValues k

/-- The slice Gram `H_Y` as an operator on `B(M_s, M_t)` with its Hilbert–Schmidt structure. -/
def sliceGramOp (Y : Matrix (Kt × Mt) (Ks × Ms) ℂ) :
    EuclideanSpace ℂ (Mt × Ms) →ₗ[ℂ] EuclideanSpace ℂ (Mt × Ms) :=
  Matrix.toEuclideanLin (sliceGram Y)

/-- `H_Y = 𝒮_Y 𝒮_Y^*`. -/
theorem sliceGramOp_eq (Y : Matrix (Kt × Mt) (Ks × Ms) ℂ) :
    sliceGramOp Y = sliceMap Y ∘ₗ LinearMap.adjoint (sliceMap Y) := by
  unfold sliceGramOp sliceMap sliceGram
  rw [Matrix.toLpLin_mul_same, Matrix.toEuclideanLin_conjTranspose_eq_adjoint]

theorem realign_sub (Y Y' : Matrix (Kt × Mt) (Ks × Ms) ℂ) :
    realign (Y' - Y) = realign Y' - realign Y := by
  ext p q
  simp [realign]

theorem sliceMap_sub (Y Y' : Matrix (Kt × Mt) (Ks × Ms) ℂ) :
    sliceMap Y' - sliceMap Y = sliceMap (Y' - Y) := by
  unfold sliceMap
  rw [realign_sub, map_sub]

/-- The slice map is bounded by the Hilbert–Schmidt norm: `‖𝒮_D‖_op ≤ ‖D‖_HS`. -/
theorem norm_sliceMap_apply_le (D : Matrix (Kt × Mt) (Ks × Ms) ℂ) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hHS : ∑ a, ∑ b, ‖D a b‖ ^ 2 ≤ ε ^ 2) (x : EuclideanSpace ℂ (Kt × Ks)) :
    ‖sliceMap D x‖ ≤ ε * ‖x‖ := by
  set T := LinearMap.toContinuousLinearMap (sliceMap D)
  have hcol : ∀ q : Kt × Ks,
      ‖T (EuclideanSpace.basisFun (Kt × Ks) ℂ q)‖ ^ 2 = ∑ p : Mt × Ms, ‖realign D p q‖ ^ 2 := by
    intro q
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp [T, sliceMap, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct, Pi.single_apply]
  have hsum : ∑ q : Kt × Ks, ‖T (EuclideanSpace.basisFun (Kt × Ks) ℂ q)‖ ^ 2 =
      ∑ a, ∑ b, ‖D a b‖ ^ 2 := by
    simp only [hcol, realign, Matrix.of_apply]
    rw [← Fintype.sum_prod_type' (f := fun (q : Kt × Ks) (p : Mt × Ms) =>
        ‖D (q.1, p.1) (q.2, p.2)‖ ^ 2),
      ← Fintype.sum_prod_type' (f := fun (a : Kt × Mt) (b : Ks × Ms) => ‖D a b‖ ^ 2)]
    let e : (Kt × Ks) × (Mt × Ms) ≃ (Kt × Mt) × (Ks × Ms) :=
      { toFun := fun x => ((x.1.1, x.2.1), (x.1.2, x.2.2))
        invFun := fun y => ((y.1.1, y.2.1), (y.1.2, y.2.2))
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact Fintype.sum_equiv e _ _ (fun _ => rfl)
  have hT := CertifiedSupportStratum.opNorm_le_of_sum_norm_sq_le
    (EuclideanSpace.basisFun (Kt × Ks) ℂ) T hε0 (by rw [hsum]; exact hHS)
  have := T.le_opNorm x
  calc ‖sliceMap D x‖ = ‖T x‖ := rfl
    _ ≤ ‖T‖ * ‖x‖ := this
    _ ≤ ε * ‖x‖ := mul_le_mul_of_nonneg_right hT (norm_nonneg _)

/-- The operator–Schmidt rank (rank of the slice map) is the rank of the slice Gram `H_Y`. -/
theorem finrank_range_sliceMap (Y : Matrix (Kt × Mt) (Ks × Ms) ℂ) :
    finrank ℂ (LinearMap.range (sliceMap Y)) = (sliceGram Y).rank := by
  rw [Matrix.rank_eq_finrank_range_toLin (sliceGram Y)
    (EuclideanSpace.basisFun (Mt × Ms) ℂ).toBasis (EuclideanSpace.basisFun (Mt × Ms) ℂ).toBasis,
    ← Matrix.toEuclideanLin_eq_toLin_orthonormal]
  change _ = finrank ℂ (LinearMap.range (sliceGramOp Y))
  rw [sliceGramOp_eq, LinearMap.range_self_comp_adjoint]

/-- For an operator–Schmidt decomposition `Y = ∑_{k ∈ ι} σ_k D_k ⊗ F_k` (Hilbert–Schmidt
orthonormal families, nonzero real `σ_k`), the operator–Schmidt rank `rank 𝒮_Y` is `#ι`. -/
theorem finrank_range_sliceMap_schmidt {ι : Type*} [Fintype ι] [DecidableEq ι] (σ : ι → ℝ)
    (hσ : ∀ k, σ k ≠ 0) (D : ι → Matrix Kt Ks ℂ) (F : ι → Matrix Mt Ms ℂ)
    (hD : ∀ k l, hsInner (D k) (D l) = if k = l then 1 else 0)
    (hF : ∀ k l, hsInner (F k) (F l) = if k = l then 1 else 0) :
    finrank ℂ (LinearMap.range (sliceMap (∑ k, (σ k : ℂ) • Matrix.kroneckerMap (· * ·) (D k) (F k)))) =
      Fintype.card ι := by
  rw [finrank_range_sliceMap]
  exact rank_sliceGram_schmidt σ hσ D F hD hF

/-- Nonzero eigenvalues of `AA^*` are eigenvalues of `A^*A`. -/
theorem hasEigenvalue_adjoint_comp_self_of_self_comp_adjoint {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    (A : E →ₗ[ℂ] F) {μ : ℂ} (hμ : HasEigenvalue (A ∘ₗ LinearMap.adjoint A) μ) (hμ0 : μ ≠ 0) :
    HasEigenvalue (LinearMap.adjoint A ∘ₗ A) μ := by
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hAv : A (LinearMap.adjoint A v) = μ • v := by
    have := mem_eigenspace_iff.mp hv.1
    simpa using this
  have hw0 : LinearMap.adjoint A v ≠ 0 := by
    intro h
    rw [h, map_zero] at hAv
    exact hv.2 ((smul_eq_zero.mp hAv.symm).resolve_left hμ0)
  refine hasEigenvalue_of_hasEigenvector (x := LinearMap.adjoint A v) ⟨?_, hw0⟩
  rw [mem_eigenspace_iff, LinearMap.comp_apply, hAv, map_smul]

/-- **`thm:incidence-slice-cluster`.**  Let `Y` have operator–Schmidt rank `r`, nonzero
Schmidt coefficients bounded below by `s > 0` and all coefficients bounded above by `L`, and let
`‖Ỹ - Y‖_HS ≤ ε`.  Then:
1. `|σ_k(Ỹ) - σ_k(Y)| ≤ ε` for all `k` (`eq:incidence-Schmidt-Weyl`);
2. if `ε < s/2`, exactly the first `r` coefficients of `Ỹ` lie above `s/2`;
3. `‖H_Ỹ - H_Y‖_op ≤ η := (2L + ε) ε`;
4. if `η < s²/2`, then `P̃ = 𝟙_{[s²/2,∞)}(H_Ỹ)` has rank `r` and
   `‖P̃ - 𝟙_{(0,∞)}(H_Y)‖_op ≤ η / (s² - η)` (`eq:incidence-slice-projector`). -/
theorem incidence_slice_cluster (Y Yt : Matrix (Kt × Mt) (Ks × Ms) ℂ) {r : ℕ} {s L ε : ℝ}
    (hrank : finrank ℂ (LinearMap.range (sliceMap Y)) = r) (hs0 : 0 < s)
    (hs : ∀ k < r, s ≤ schmidtCoeff Y k) (hL : ∀ k, schmidtCoeff Y k ≤ L) (hε0 : 0 ≤ ε)
    (hHS : ∑ a, ∑ b, ‖(Yt - Y) a b‖ ^ 2 ≤ ε ^ 2) :
    (∀ k, |schmidtCoeff Yt k - schmidtCoeff Y k| ≤ ε) ∧
      (ε < s / 2 → (∀ k < r, s / 2 < schmidtCoeff Yt k) ∧
        (∀ k, r ≤ k → schmidtCoeff Yt k < s / 2)) ∧
      (∀ x, ‖(sliceGramOp Yt - sliceGramOp Y) x‖ ≤ (2 * L + ε) * ε * ‖x‖) ∧
      ((2 * L + ε) * ε < s ^ 2 / 2 →
        finrank ℂ (spectralSubspace (sliceGramOp Yt) (Set.Ici (s ^ 2 / 2))) = r ∧
        ‖spectralProjector (sliceGramOp Yt) (Set.Ici (s ^ 2 / 2)) -
            spectralProjector (sliceGramOp Y) (Set.Ioi 0)‖ ≤
          (2 * L + ε) * ε / (s ^ 2 - (2 * L + ε) * ε)) := by
  set S := sliceMap Y with hSdef
  set St := sliceMap Yt with hStdef
  -- the slice-map perturbation
  have hpert : ∀ x, ‖(St - S) x‖ ≤ ε * ‖x‖ := by
    intro x
    rw [hStdef, hSdef, sliceMap_sub]
    exact norm_sliceMap_apply_le _ hε0 hHS x
  -- (1) Weyl
  have hweyl : ∀ k, |schmidtCoeff Yt k - schmidtCoeff Y k| ≤ ε := fun k =>
    abs_singularValues_sub_le St S hε0 hpert k
  have hσzero : ∀ k, r ≤ k → schmidtCoeff Y k = 0 := by
    intro k hk
    exact (S.singularValues_eq_zero_iff_le_finrank_range).mpr (hrank ▸ hk)
  have hL0 : 0 ≤ L := (S.singularValues_nonneg 0).trans (hL 0)
  have hSL : ∀ x, ‖S x‖ ≤ L * ‖x‖ := fun x =>
    (norm_apply_le_singularValues_zero S x).trans
      (mul_le_mul_of_nonneg_right (hL 0) (norm_nonneg _))
  have hGram : ∀ x, ‖(sliceGramOp Yt - sliceGramOp Y) x‖ ≤ (2 * L + ε) * ε * ‖x‖ := by
    intro x
    rw [sliceGramOp_eq, sliceGramOp_eq, ← hSdef, ← hStdef]
    have hdec : (St ∘ₗ LinearMap.adjoint St - S ∘ₗ LinearMap.adjoint S) x =
        St ((LinearMap.adjoint (St - S)) x) + (St - S) (LinearMap.adjoint S x) := by
      simp only [LinearMap.sub_apply, LinearMap.comp_apply, map_sub]
      abel
    rw [hdec]
    have hStb : ∀ y, ‖St y‖ ≤ (L + ε) * ‖y‖ := by
      intro y
      have : St y = S y + (St - S) y := by
        rw [LinearMap.sub_apply]
        abel
      rw [this]
      calc ‖S y + (St - S) y‖ ≤ ‖S y‖ + ‖(St - S) y‖ := norm_add_le _ _
        _ ≤ L * ‖y‖ + ε * ‖y‖ := add_le_add (hSL y) (hpert y)
        _ = (L + ε) * ‖y‖ := by ring
    have e1 : ‖St ((LinearMap.adjoint (St - S)) x)‖ ≤ (L + ε) * (ε * ‖x‖) :=
      (hStb _).trans (mul_le_mul_of_nonneg_left
        (norm_adjoint_apply_le (St - S) hε0 hpert x) (by linarith))
    have e2 : ‖(St - S) (LinearMap.adjoint S x)‖ ≤ ε * (L * ‖x‖) :=
      (hpert _).trans (mul_le_mul_of_nonneg_left
        (norm_adjoint_apply_le S hL0 hSL x) hε0)
    calc ‖St ((LinearMap.adjoint (St - S)) x) + (St - S) (LinearMap.adjoint S x)‖
        ≤ ‖St ((LinearMap.adjoint (St - S)) x)‖ + ‖(St - S) (LinearMap.adjoint S x)‖ :=
          norm_add_le _ _
      _ ≤ (L + ε) * (ε * ‖x‖) + ε * (L * ‖x‖) := add_le_add e1 e2
      _ = (2 * L + ε) * ε * ‖x‖ := by ring
  refine ⟨hweyl, ?_, hGram, ?_⟩
  · -- (2) cluster separation
    intro hεs
    refine ⟨fun k hk => ?_, fun k hk => ?_⟩
    · have h1 := (abs_le.mp (hweyl k)).1
      have h2 := hs k hk
      linarith
    · have h1 := (abs_le.mp (hweyl k)).2
      rw [hσzero k hk] at h1
      linarith
  -- (4) the projector bound
  intro hη
  set η := (2 * L + ε) * ε with hηdef
  have hη0 : 0 ≤ η := mul_nonneg (by linarith) hε0
  have hG : sliceGramOp Y = S ∘ₗ LinearMap.adjoint S := sliceGramOp_eq Y
  have hGt : sliceGramOp Yt = St ∘ₗ LinearMap.adjoint St := sliceGramOp_eq Yt
  have hsym : (sliceGramOp Y).IsSymmetric := by
    rw [hG]; exact CertifiedSupportStratum.isSymmetric_self_comp_adjoint S
  have hsymt : (sliceGramOp Yt).IsSymmetric := by
    rw [hGt]; exact CertifiedSupportStratum.isSymmetric_self_comp_adjoint St
  -- spectrum of `H_Y` lies in `{0} ∪ [s², ∞)`
  have hspec : ∀ μ : ℝ, HasEigenvalue (sliceGramOp Y) (μ : ℂ) → μ = 0 ∨ s ^ 2 ≤ μ := by
    intro μ hμ
    by_cases hμ0 : μ = 0
    · exact Or.inl hμ0
    right
    rw [hG] at hμ
    have hμ' := hasEigenvalue_adjoint_comp_self_of_self_comp_adjoint S hμ
      (by exact_mod_cast hμ0)
    obtain ⟨i, hi⟩ := S.isSymmetric_adjoint_comp_self.exists_eigenvalues_eq rfl hμ'
    have hi' : S.isSymmetric_adjoint_comp_self.eigenvalues rfl i = μ :=
      Complex.ofReal_injective hi
    have hsq := S.sq_singularValues_of_lt rfl i.2
    rw [hi'] at hsq
    have hir : i.val < r := by
      by_contra hir
      have h0 : S.singularValues i.val = 0 := hσzero i.val (not_lt.mp hir)
      rw [h0] at hsq
      exact hμ0 (by rw [← hsq]; ring)
    have : s ≤ S.singularValues i.val := hs i.val hir
    rw [← hsq]
    exact pow_le_pow_left₀ hs0.le this 2
  have hg : 0 < s ^ 2 := by positivity
  obtain ⟨hdim, -, -, hnorm⟩ := hermitian_cluster_projector_perturbation hsym hsymt hg hη0 hη
    hspec (by intro x; rw [hηdef]; exact hGram x)
  refine ⟨?_, hnorm⟩
  rw [hdim]
  -- `rank 𝟙_{(0,∞)}(H_Y) = rank H_Y = rank 𝒮_Y = r`
  have hperp : (spectralSubspace (sliceGramOp Y) (Set.Ioi 0))ᗮ =
      spectralSubspace (sliceGramOp Y) (Set.Iic 0) := by
    rw [orthogonal_spectralSubspace hsym, Set.compl_Ioi]
  have hker : spectralSubspace (sliceGramOp Y) (Set.Iic 0) = LinearMap.ker (sliceGramOp Y) := by
    apply le_antisymm
    · intro x hx
      rw [LinearMap.mem_ker]
      have := norm_apply_le_of_mem hsym le_rfl (fun μ hμ he => by
        rcases hspec μ he with h | h
        · simp [h]
        · exfalso
          simp only [Set.mem_Iic] at hμ
          linarith) hx
      simpa using this
    · intro x hx
      refine eigenspace_le_spectralSubspace _ (Set.mem_Iic.mpr le_rfl) ?_
      rw [mem_eigenspace_iff]
      simpa using hx
  have h1 := Submodule.finrank_add_finrank_orthogonal
    (spectralSubspace (sliceGramOp Y) (Set.Ioi 0))
  rw [hperp, hker] at h1
  have h2 := LinearMap.finrank_range_add_finrank_ker (sliceGramOp Y)
  have h3 : finrank ℂ (LinearMap.range (sliceGramOp Y)) = r := by
    rw [hG, LinearMap.range_self_comp_adjoint, hrank]
  omega

theorem realign_zero : realign (0 : Matrix (Kt × Mt) (Ks × Ms) ℂ) = 0 := by
  ext p q
  simp [realign]

theorem sliceMap_zero : sliceMap (0 : Matrix (Kt × Mt) (Ks × Ms) ℂ) = 0 := by
  unfold sliceMap
  rw [realign_zero, map_zero]

/-- Non-vacuity: the hypotheses of `incidence_slice_cluster` hold for `Y = Ỹ = 0`, `r = 0`,
`s = 1`, `L = 0`, `ε = 0`. -/
example : (∀ k, |schmidtCoeff (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) k -
    schmidtCoeff (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) k| ≤ 0) :=
  (incidence_slice_cluster (0 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) 0 (r := 0) (s := 1)
    (L := 0) (ε := 0) (by rw [sliceMap_zero, LinearMap.range_zero, finrank_bot]) one_pos
    (fun k hk => absurd hk (Nat.not_lt_zero k))
    (fun k => by simp [schmidtCoeff, sliceMap_zero]) le_rfl (by simp)).1

end IncidenceSliceCluster
end RenewalGeometry
