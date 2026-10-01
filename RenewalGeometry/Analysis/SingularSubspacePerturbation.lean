/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.HermitianSpectralProjectorPerturbation

/-!
# Singular values and singular subspaces under perturbation

Finite-dimensional singular-value perturbation theory on top of Mathlib's
`LinearMap.singularValues` (square roots of the sorted eigenvalues of `A† A`) and the spectral
subspaces of `RenewalGeometry.HermitianSpectral`.  Used for `thm:incidence-slice-cluster` and
`thm:certified-support-stratum` of `papers/spacetime_gauge_duality`.

* `singularValues_le_add`, `abs_singularValues_sub_le`: **Weyl's inequality** for singular
  values, `|σ_k(A) - σ_k(B)| ≤ ‖A - B‖`;
* `norm_apply_le_singularValues_zero`: `‖A‖ ≤ σ_0(A)`;
* `norm_adjoint_apply_le`: operator-norm bounds pass to adjoints;
* `apply_mem_spectralSubspace_self_comp_adjoint`: `A` maps right singular subspaces of `A`
  (spectral subspaces of `A†A`) into the corresponding left singular subspaces (of `AA†`);
* `support_projector_perturbation`: **a Wedin-type bound for a low-rank target.**  If
  `rank G₀ ≤ r`, `‖G - G₀‖ ≤ ε`, and `V` is an `A†A`-invariant subspace of dimension `≥ r` on
  which `‖G v‖ ≥ σ ‖v‖` with `σ > 2ε`, then `rank G₀ = dim V = r` and
  `‖P_{(ker G₀)ᗮ} - P_V‖ ≤ ε / (σ - 2ε)`.
-/

open scoped InnerProductSpace
open Module Module.End
open RenewalGeometry.HermitianSpectral

noncomputable section

namespace RenewalGeometry
namespace SingularSubspace

set_option linter.unusedSectionVars false

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

theorem norm_apply_sq_eq_re_inner (A : E →ₗ[𝕜] F) (x : E) :
    ‖A x‖ ^ 2 = RCLike.re ⟪x, (LinearMap.adjoint A ∘ₗ A) x⟫_𝕜 := by
  rw [LinearMap.comp_apply, LinearMap.adjoint_inner_right, inner_self_eq_norm_sq]

/-- On the spectral subspace of `A†A` above `s²`, `‖A x‖ ≥ s ‖x‖`. -/
theorem le_norm_apply_of_mem_Ici (A : E →ₗ[𝕜] F) {s : ℝ} (hs : 0 ≤ s) {x : E}
    (hx : x ∈ spectralSubspace (LinearMap.adjoint A ∘ₗ A) (Set.Ici (s ^ 2))) :
    s * ‖x‖ ≤ ‖A x‖ := by
  have h := le_re_inner_of_mem A.isSymmetric_adjoint_comp_self (fun μ hμ _ => hμ) hx
  rw [← norm_apply_sq_eq_re_inner, ← mul_pow] at h
  exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).mp h

/-- On the spectral subspace of `A†A` below `s²`, `‖A x‖ ≤ s ‖x‖`. -/
theorem norm_apply_le_of_mem_Iic (A : E →ₗ[𝕜] F) {s : ℝ} (hs : 0 ≤ s) {x : E}
    (hx : x ∈ spectralSubspace (LinearMap.adjoint A ∘ₗ A) (Set.Iic (s ^ 2))) :
    ‖A x‖ ≤ s * ‖x‖ := by
  have h := re_inner_le_of_mem A.isSymmetric_adjoint_comp_self (fun μ hμ _ => hμ) hx
  rw [← norm_apply_sq_eq_re_inner, ← mul_pow] at h
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h

/-- The top `k + 1` right singular vectors lie above `σ_k²`. -/
theorem eigenvectorBasis_mem_Ici (A : E →ₗ[𝕜] F) {k : ℕ} (hk : k < finrank 𝕜 E)
    (i : Fin (finrank 𝕜 E)) (hi : i ≤ ⟨k, hk⟩) :
    A.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl i ∈
      spectralSubspace (LinearMap.adjoint A ∘ₗ A) (Set.Ici (A.singularValues k ^ 2)) := by
  refine eigenvectorBasis_mem_spectralSubspace _ rfl ?_
  rw [Set.mem_Ici, A.sq_singularValues_of_lt rfl hk]
  exact A.isSymmetric_adjoint_comp_self.eigenvalues_antitone rfl hi

/-- The bottom right singular vectors from index `k` on lie below `σ_k²`. -/
theorem eigenvectorBasis_mem_Iic (A : E →ₗ[𝕜] F) {k : ℕ} (hk : k < finrank 𝕜 E)
    (i : Fin (finrank 𝕜 E)) (hi : (⟨k, hk⟩ : Fin (finrank 𝕜 E)) ≤ i) :
    A.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl i ∈
      spectralSubspace (LinearMap.adjoint A ∘ₗ A) (Set.Iic (A.singularValues k ^ 2)) := by
  refine eigenvectorBasis_mem_spectralSubspace _ rfl ?_
  rw [Set.mem_Iic, A.sq_singularValues_of_lt rfl hk]
  exact A.isSymmetric_adjoint_comp_self.eigenvalues_antitone rfl hi

/-- `dim 𝟙_{[σ_k², ∞)}(A†A) ≥ k + 1`. -/
theorem succ_le_finrank_Ici (A : E →ₗ[𝕜] F) {k : ℕ} (hk : k < finrank 𝕜 E) :
    k + 1 ≤ finrank 𝕜
      (spectralSubspace (LinearMap.adjoint A ∘ₗ A) (Set.Ici (A.singularValues k ^ 2))) := by
  have h := card_le_finrank_of_eigenvectorBasis_mem A.isSymmetric_adjoint_comp_self rfl _
    (Finset.Iic ⟨k, hk⟩) (fun i hi => eigenvectorBasis_mem_Ici A hk i (Finset.mem_Iic.mp hi))
  rwa [Fin.card_Iic] at h

/-- `dim 𝟙_{(-∞, σ_k²]}(A†A) ≥ dim E - k`. -/
theorem finrank_sub_le_finrank_Iic (A : E →ₗ[𝕜] F) {k : ℕ} (hk : k < finrank 𝕜 E) :
    finrank 𝕜 E - k ≤ finrank 𝕜
      (spectralSubspace (LinearMap.adjoint A ∘ₗ A) (Set.Iic (A.singularValues k ^ 2))) := by
  have h := card_le_finrank_of_eigenvectorBasis_mem A.isSymmetric_adjoint_comp_self rfl _
    (Finset.Ici ⟨k, hk⟩) (fun i hi => eigenvectorBasis_mem_Iic A hk i (Finset.mem_Ici.mp hi))
  rwa [Fin.card_Ici] at h

/-- **Weyl's inequality for singular values** (one side). -/
theorem singularValues_le_add (A B : E →ₗ[𝕜] F) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x, ‖(A - B) x‖ ≤ c * ‖x‖) (k : ℕ) :
    A.singularValues k ≤ B.singularValues k + c := by
  by_cases hk : k < finrank 𝕜 E
  · have hV := succ_le_finrank_Ici A hk
    have hW := finrank_sub_le_finrank_Iic B hk
    have hnk : finrank 𝕜 E - k + k = finrank 𝕜 E := Nat.sub_add_cancel hk.le
    obtain ⟨x, hxV, hxW, hx0⟩ := exists_ne_zero_mem_of_finrank_lt
      (spectralSubspace (LinearMap.adjoint A ∘ₗ A) (Set.Ici (A.singularValues k ^ 2)))
      (spectralSubspace (LinearMap.adjoint B ∘ₗ B) (Set.Iic (B.singularValues k ^ 2)))
      (by omega)
    have h1 := le_norm_apply_of_mem_Ici A (A.singularValues_nonneg k) hxV
    have h2 := norm_apply_le_of_mem_Iic B (B.singularValues_nonneg k) hxW
    have h3 : ‖A x‖ ≤ ‖B x‖ + c * ‖x‖ := by
      have : A x = B x + (A - B) x := by
        rw [LinearMap.sub_apply]
        abel
      rw [this]
      exact (norm_add_le _ _).trans (add_le_add le_rfl (h x))
    have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have : A.singularValues k * ‖x‖ ≤ (B.singularValues k + c) * ‖x‖ := by nlinarith
    exact le_of_mul_le_mul_right this hxpos
  · rw [A.singularValues_of_finrank_le (not_lt.mp hk)]
    exact add_nonneg (B.singularValues_nonneg k) hc

/-- **Weyl's inequality for singular values**: `|σ_k(A) - σ_k(B)| ≤ ‖A - B‖`. -/
theorem abs_singularValues_sub_le (A B : E →ₗ[𝕜] F) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x, ‖(A - B) x‖ ≤ c * ‖x‖) (k : ℕ) :
    |A.singularValues k - B.singularValues k| ≤ c := by
  have h' : ∀ x, ‖(B - A) x‖ ≤ c * ‖x‖ := fun x => by
    rw [← norm_neg, ← LinearMap.neg_apply, neg_sub]
    exact h x
  have e1 := singularValues_le_add A B hc h k
  have e2 := singularValues_le_add B A hc h' k
  rw [abs_le]
  constructor <;> linarith

/-- **Weyl's inequality for continuous linear maps**: `|σ_k(A) - σ_k(B)| ≤ ‖A - B‖`. -/
theorem abs_singularValues_sub_le_opNorm (A B : E →L[𝕜] F) (k : ℕ) :
    |(A : E →ₗ[𝕜] F).singularValues k - (B : E →ₗ[𝕜] F).singularValues k| ≤ ‖A - B‖ :=
  abs_singularValues_sub_le _ _ (norm_nonneg _) (fun x => (A - B).le_opNorm x) k

/-- All eigenvalues of `A†A` lie below `σ_0(A)²`. -/
theorem mem_spectralSubspace_Iic_singularValues_zero (A : E →ₗ[𝕜] F) (x : E) :
    x ∈ spectralSubspace (LinearMap.adjoint A ∘ₗ A) (Set.Iic (A.singularValues 0 ^ 2)) := by
  rw [mem_spectralSubspace_iff A.isSymmetric_adjoint_comp_self rfl]
  intro i hi
  exfalso
  apply hi
  have hpos : 0 < finrank 𝕜 E := lt_of_le_of_lt (Nat.zero_le _) i.2
  rw [Set.mem_Iic, A.sq_singularValues_of_lt rfl hpos]
  exact A.isSymmetric_adjoint_comp_self.eigenvalues_antitone rfl
    (show (⟨0, hpos⟩ : Fin (finrank 𝕜 E)) ≤ i from Nat.zero_le _)

/-- `‖A x‖ ≤ σ_0(A) ‖x‖`: the largest singular value bounds the operator norm. -/
theorem norm_apply_le_singularValues_zero (A : E →ₗ[𝕜] F) (x : E) :
    ‖A x‖ ≤ A.singularValues 0 * ‖x‖ :=
  norm_apply_le_of_mem_Iic A (A.singularValues_nonneg 0)
    (mem_spectralSubspace_Iic_singularValues_zero A x)

/-- Operator-norm bounds pass to the adjoint. -/
theorem norm_adjoint_apply_le (A : E →ₗ[𝕜] F) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x, ‖A x‖ ≤ c * ‖x‖) (y : F) : ‖LinearMap.adjoint A y‖ ≤ c * ‖y‖ := by
  set z := LinearMap.adjoint A y
  have hsq : ‖z‖ ^ 2 ≤ c * ‖z‖ * ‖y‖ := by
    have : ‖z‖ ^ 2 = RCLike.re ⟪A z, y⟫_𝕜 := by
      rw [← LinearMap.adjoint_inner_right, inner_self_eq_norm_sq]
    rw [this]
    calc RCLike.re ⟪A z, y⟫_𝕜 ≤ ‖A z‖ * ‖y‖ :=
          (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
      _ ≤ c * ‖z‖ * ‖y‖ := mul_le_mul_of_nonneg_right (h z) (norm_nonneg _)
  rcases (norm_nonneg z).eq_or_lt with h0 | h0
  · rw [← h0]
    positivity
  · nlinarith [norm_nonneg y]

/-- `A` maps eigenvectors of `A†A` to eigenvectors of `AA†` with the same eigenvalue. -/
theorem apply_mem_eigenspace_self_comp_adjoint (A : E →ₗ[𝕜] F) {μ : 𝕜} {v : E}
    (hv : v ∈ eigenspace (LinearMap.adjoint A ∘ₗ A) μ) :
    A v ∈ eigenspace (A ∘ₗ LinearMap.adjoint A) μ := by
  rw [mem_eigenspace_iff] at hv ⊢
  rw [LinearMap.comp_apply]
  have : LinearMap.adjoint A (A v) = μ • v := by simpa using hv
  rw [this, map_smul]

/-- **Right to left singular subspaces**: `A (𝟙_S(A†A) E) ≤ 𝟙_S(AA†) F`. -/
theorem apply_mem_spectralSubspace_self_comp_adjoint (A : E →ₗ[𝕜] F) {S : Set ℝ} {v : E}
    (hv : v ∈ spectralSubspace (LinearMap.adjoint A ∘ₗ A) S) :
    A v ∈ spectralSubspace (A ∘ₗ LinearMap.adjoint A) S := by
  have hle : spectralSubspace (LinearMap.adjoint A ∘ₗ A) S ≤
      (spectralSubspace (A ∘ₗ LinearMap.adjoint A) S).comap A := by
    refine iSup₂_le fun μ hμ => ?_
    intro w hw
    exact eigenspace_le_spectralSubspace _ hμ (apply_mem_eigenspace_self_comp_adjoint A hw)
  exact hle hv

/-! ### Support projector perturbation -/

/-- **Support-projector perturbation for a low-rank target (Wedin-type bound).**
Let `G₀` have rank at most `r`, let `‖G - G₀‖ ≤ ε`, and let `V` be a `G†G`-invariant subspace
of dimension at least `r` on which `‖G v‖ ≥ σ ‖v‖`, with `σ > 2 ε`.  Then `rank G₀ = dim V = r`
and the support projector `P_{(ker G₀)ᗮ}` of `G₀` is within `ε / (σ - 2ε)` of `P_V`. -/
theorem support_projector_perturbation (G G₀ : E →ₗ[𝕜] F) {ε σ : ℝ} {r : ℕ}
    (V : Submodule 𝕜 E) (hε0 : 0 ≤ ε) (hε : ∀ x, ‖(G - G₀) x‖ ≤ ε * ‖x‖) (hσ : 2 * ε < σ)
    (hrank : finrank 𝕜 (LinearMap.range G₀) ≤ r) (hV : r ≤ finrank 𝕜 V)
    (hinv : ∀ v ∈ V, (LinearMap.adjoint G ∘ₗ G) v ∈ V) (hlow : ∀ v ∈ V, σ * ‖v‖ ≤ ‖G v‖) :
    finrank 𝕜 (LinearMap.range G₀) = r ∧ finrank 𝕜 V = r ∧
      ‖(LinearMap.ker G₀)ᗮ.starProjection - V.starProjection‖ ≤ ε / (σ - 2 * ε) := by
  set K := (LinearMap.ker G₀)ᗮ with hK
  have hσ0 : 0 < σ := by linarith
  have hd : 0 < σ - 2 * ε := by linarith
  set a := ε / σ with ha
  have ha0 : 0 ≤ a := div_nonneg hε0 hσ0.le
  have ha1 : a < 1 := by
    rw [ha, div_lt_one hσ0]
    linarith
  -- Step A: kernel vectors are almost orthogonal to `V`
  have hA : ∀ y ∈ Kᗮ, ‖V.starProjection y‖ ≤ a * ‖y‖ := by
    intro y hy
    rw [hK, Submodule.orthogonal_orthogonal, LinearMap.mem_ker] at hy
    set v := V.starProjection y
    set w := Vᗮ.starProjection y
    have hyvw : y = v + w := by
      simp only [v, w, Submodule.starProjection_orthogonal_val]
      abel
    have hvV : v ∈ V := V.starProjection_apply_mem y
    have hwV : w ∈ Vᗮ := Vᗮ.starProjection_apply_mem y
    have horth : ⟪G v, G w⟫_𝕜 = 0 := by
      rw [← LinearMap.adjoint_inner_left]
      exact (Submodule.mem_orthogonal V w).mp hwV _ (hinv v hvV)
    have hpy := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
    have hGy : G y = G v + G w := by rw [hyvw, map_add]
    have hGy' : ‖G y‖ ≤ ε * ‖y‖ := by
      have : G y = (G - G₀) y := by rw [LinearMap.sub_apply, hy, sub_zero]
      rw [this]
      exact hε y
    have hGv : ‖G v‖ ≤ ‖G y‖ := by
      rw [hGy]
      have : ‖G v‖ * ‖G v‖ ≤ ‖G v + G w‖ * ‖G v + G w‖ := by
        rw [hpy]
        nlinarith [norm_nonneg (G w)]
      exact (mul_self_le_mul_self_iff (norm_nonneg _) (norm_nonneg _)).mpr this
    have := (hlow v hvV).trans (hGv.trans hGy')
    rw [ha, div_mul_eq_mul_div, le_div_iff₀ hσ0]
    linarith
  -- Step B: `V` is almost inside `K`
  have hB : ∀ v ∈ V, ‖Kᗮ.starProjection v‖ ≤ a * ‖v‖ :=
    norm_starProjection_le_swap V Kᗮ ha0 hA
  -- Step C: dimensions
  have hVK : ∀ x ∈ V, x ∈ Kᗮ → x = 0 := by
    intro x hxV hxK
    have h1 := hA x hxK
    rw [Submodule.starProjection_eq_self_iff.mpr hxV] at h1
    have : ‖x‖ = 0 := by
      have := norm_nonneg x
      nlinarith
    exact norm_eq_zero.mp this
  have hdim1 := finrank_add_finrank_le_of_inf_eq_bot V Kᗮ hVK
  have hdim2 := Submodule.finrank_add_finrank_orthogonal K
  have hdim3 := Submodule.finrank_add_finrank_orthogonal (LinearMap.ker G₀)
  have hdim4 := LinearMap.finrank_range_add_finrank_ker G₀
  have hKr : finrank 𝕜 K = finrank 𝕜 (LinearMap.range G₀) := by
    rw [hK]
    omega
  have hVr : finrank 𝕜 V = r := by omega
  have hGr : finrank 𝕜 (LinearMap.range G₀) = r := by omega
  refine ⟨hGr, hVr, ?_⟩
  -- Step D: the other side, from equal dimensions
  have hD := norm_starProjection_orthogonal_sq_le_of_finrank_eq V K (by omega) ha0 ha1 hB
  -- Step E: assemble
  set c := ε / (σ - 2 * ε) with hc
  have hc0 : 0 ≤ c := div_nonneg hε0 hd.le
  have hac : a ≤ c := div_le_div_of_nonneg_left hε0 hd (by linarith)
  have h1 : ∀ v ∈ V, ‖Kᗮ.starProjection v‖ ≤ c * ‖v‖ := fun v hv =>
    (hB v hv).trans (mul_le_mul_of_nonneg_right hac (norm_nonneg _))
  have h2 : ∀ k ∈ K, ‖Vᗮ.starProjection k‖ ≤ c * ‖k‖ := by
    intro k hk
    have e := hD k hk
    set X := ‖Vᗮ.starProjection k‖
    set Y := ‖k‖
    have hX : 0 ≤ X := norm_nonneg _
    have hY : 0 ≤ Y := norm_nonneg _
    -- `(σ² - ε²) X² ≤ ε² Y²`
    have e' : (σ ^ 2 - ε ^ 2) * X ^ 2 ≤ ε ^ 2 * Y ^ 2 := by
      have hσ2 : 0 < σ ^ 2 := by positivity
      have : (1 - a ^ 2) * X ^ 2 * σ ^ 2 ≤ a ^ 2 * Y ^ 2 * σ ^ 2 :=
        mul_le_mul_of_nonneg_right e hσ2.le
      have haσ : a * σ = ε := by rw [ha]; field_simp
      have q1 : (1 - a ^ 2) * X ^ 2 * σ ^ 2 = (σ ^ 2 - ε ^ 2) * X ^ 2 := by
        rw [← haσ]; ring
      have q2 : a ^ 2 * Y ^ 2 * σ ^ 2 = ε ^ 2 * Y ^ 2 := by
        rw [← haσ]; ring
      linarith
    have hdd : (σ - 2 * ε) ^ 2 ≤ σ ^ 2 - ε ^ 2 := by nlinarith
    have e'' : ((σ - 2 * ε) * X) ^ 2 ≤ (ε * Y) ^ 2 := by
      rw [mul_pow, mul_pow]
      nlinarith [sq_nonneg X]
    have e3 : (σ - 2 * ε) * X ≤ ε * Y :=
      (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp e''
    rw [hc, div_mul_eq_mul_div, le_div_iff₀ hd]
    linarith
  have := norm_starProjection_sub_le V K hc0 h1 h2
  rwa [norm_sub_rev] at this

end SingularSubspace
end RenewalGeometry
