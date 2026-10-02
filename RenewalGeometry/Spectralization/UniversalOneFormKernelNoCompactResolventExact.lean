/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Spectralization.UniversalOneFormDiracKernelGrowthExact

/-!
# Retained universal one-form zero modes forbid a compact resolvent

Paper `predictive_spectral_geometry`, label `cth:supp-extensive-kernel`, final clause:
"any compatible cofinal limit that retains all these zero modes has infinite-dimensional
kernel and cannot have compact resolvent".

The limit operator is an arbitrary (possibly unbounded) partially defined linear operator
`T : H →ₗ.[𝕜] H` on a Hilbert space.  Its kernel is `partialKer T`.  A *resolvent of `T` at
`z`* is a bounded two-sided inverse of `T - z` (`IsResolventAt`), and `T` *has compact
resolvent* when some resolvent is a compact operator (`HasCompactResolvent`).

* `partialKer_le_eigenspace_resolvent`: the kernel of `T` lies in the eigenspace of the
  resolvent `R(z)` at the nonzero eigenvalue `(-z)⁻¹` (and is trivial when `z = 0`);
* `finiteDimensional_partialKer_of_hasCompactResolvent`: compact resolvent forces a
  finite-dimensional kernel (Mathlib's finite-dimensionality of nonzero eigenspaces of a
  compact operator);
* `not_finiteDimensional_partialKer_of_injections`: if finite-dimensional spaces of unbounded
  real dimension inject (real-linearly) into the kernel, the kernel is infinite-dimensional;
* `retained_universal_oneform_zero_modes_no_compact_resolvent`: the proposition's consequence.
  For a cofinal family of connected periodic `A₃` stages (`dim V_k = n_k`, `dim W_k = 12 n_k`,
  i.e. `e_k = 6 n_k`, connectedness as `dim ker d_k = 1`, `n_k` unbounded), any limit operator
  into whose kernel all the stage zero modes `ker D_k` (`D_k = universalDirac d_k`, of dimension
  `11 n_k + 2`) inject has infinite-dimensional kernel and no compact resolvent.  The
  compatibility of the stage embeddings is not needed for the conclusion, so it is not assumed.
-/

namespace RenewalGeometry.UniversalOneFormKernelNoCompactResolvent

open Module

section General

variable {𝕜 : Type*} [RCLike 𝕜] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- The kernel of a partially defined linear operator, as a subspace of the ambient space. -/
def partialKer (T : H →ₗ.[𝕜] H) : Submodule 𝕜 H :=
  (LinearMap.ker T.toFun).map T.domain.subtype

theorem mem_partialKer {T : H →ₗ.[𝕜] H} {v : H} :
    v ∈ partialKer T ↔ ∃ hv : v ∈ T.domain, T ⟨v, hv⟩ = 0 := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.2, by simpa using hx⟩
  · rintro ⟨hv, h⟩
    exact ⟨⟨v, hv⟩, by simpa using h, rfl⟩

/-- `R` is a resolvent of the partially defined operator `T` at `z`: a bounded two-sided inverse
of `T - z` (range in the domain, right inverse on `H`, left inverse on the domain). -/
structure IsResolventAt (T : H →ₗ.[𝕜] H) (z : 𝕜) (R : H →L[𝕜] H) : Prop where
  mem_domain : ∀ y, R y ∈ T.domain
  right_inv : ∀ y, T ⟨R y, mem_domain y⟩ - z • R y = y
  left_inv : ∀ x : T.domain, R (T x - z • (x : H)) = x

/-- `T` has compact resolvent: some resolvent `R(z) = (T - z)⁻¹` is a compact operator. -/
def HasCompactResolvent (T : H →ₗ.[𝕜] H) : Prop :=
  ∃ z : 𝕜, ∃ R : H →L[𝕜] H, IsResolventAt T z R ∧ IsCompactOperator R

/-- A zero mode `v` of `T` satisfies `R(z) (-z v) = v`. -/
theorem resolvent_apply_neg_smul_of_mem_partialKer {T : H →ₗ.[𝕜] H} {z : 𝕜} {R : H →L[𝕜] H}
    (hR : IsResolventAt T z R) {v : H} (hv : v ∈ partialKer T) : R (-(z • v)) = v := by
  obtain ⟨hvd, hT⟩ := mem_partialKer.mp hv
  have h := hR.left_inv ⟨v, hvd⟩
  simpa [hT] using h

/-- If `0` lies in the resolvent set, the kernel is trivial. -/
theorem partialKer_eq_bot_of_isResolventAt_zero {T : H →ₗ.[𝕜] H} {R : H →L[𝕜] H}
    (hR : IsResolventAt T 0 R) : partialKer T = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  have h := resolvent_apply_neg_smul_of_mem_partialKer hR hv
  simp only [zero_smul, neg_zero, map_zero] at h
  simp [← h]

/-- The kernel of `T` is contained in the eigenspace of the resolvent `R(z)` at the eigenvalue
`(-z)⁻¹`. -/
theorem partialKer_le_eigenspace_resolvent {T : H →ₗ.[𝕜] H} {z : 𝕜} {R : H →L[𝕜] H}
    (hR : IsResolventAt T z R) (hz : z ≠ 0) :
    partialKer T ≤ Module.End.eigenspace R.toLinearMap (-z)⁻¹ := by
  intro v hv
  rw [Module.End.mem_eigenspace_iff]
  have h := resolvent_apply_neg_smul_of_mem_partialKer hR hv
  rw [← neg_smul, map_smul] at h
  have hz' : -z ≠ 0 := neg_ne_zero.mpr hz
  calc R.toLinearMap v = (-z)⁻¹ • ((-z) • R v) := by
        rw [smul_smul, inv_mul_cancel₀ hz', one_smul]; rfl
    _ = (-z)⁻¹ • v := by rw [h]

/-- **Compact resolvent forces a finite-dimensional kernel.** -/
theorem finiteDimensional_partialKer_of_hasCompactResolvent [CompleteSpace H]
    {T : H →ₗ.[𝕜] H} (hT : HasCompactResolvent T) : FiniteDimensional 𝕜 (partialKer T) := by
  obtain ⟨z, R, hR, hcpt⟩ := hT
  by_cases hz : z = 0
  · subst hz
    rw [partialKer_eq_bot_of_isResolventAt_zero hR]
    infer_instance
  · have hz' : (-z)⁻¹ ≠ 0 := inv_ne_zero (neg_ne_zero.mpr hz)
    have := ContinuousLinearMap.finite_dimensional_eigenspace hcpt _ hz'
    exact Submodule.finiteDimensional_of_le (partialKer_le_eigenspace_resolvent hR hz)

variable [Module ℝ H] [IsScalarTower ℝ 𝕜 H]

/-- **Unboundedly many retained zero modes give an infinite-dimensional kernel.**  If, for every
bound `N`, some finite-dimensional real space of dimension `≥ N` injects real-linearly into the
kernel of `T`, then the kernel is not finite-dimensional. -/
theorem not_finiteDimensional_partialKer_of_injections {ι : Type*} (T : H →ₗ.[𝕜] H)
    (K : ι → Type*) [∀ i, AddCommGroup (K i)] [∀ i, Module ℝ (K i)]
    [∀ i, FiniteDimensional ℝ (K i)]
    (emb : ∀ i, K i →ₗ[ℝ] H) (hinj : ∀ i, Function.Injective (emb i))
    (hker : ∀ i x, emb i x ∈ partialKer T)
    (hunb : ∀ N : ℕ, ∃ i, N ≤ finrank ℝ (K i)) :
    ¬ FiniteDimensional 𝕜 (partialKer T) := by
  intro hfin
  let S : Submodule ℝ H := (partialKer T).restrictScalars ℝ
  have : FiniteDimensional ℝ S := by
    have : FiniteDimensional ℝ (partialKer T) := Module.Finite.trans 𝕜 (partialKer T)
    exact this
  obtain ⟨i, hi⟩ := hunb (finrank ℝ S + 1)
  have hle : LinearMap.range (emb i) ≤ S := by
    rintro _ ⟨x, rfl⟩
    exact hker i x
  have h1 := LinearMap.finrank_range_of_inj (hinj i)
  have h2 := Submodule.finrank_mono hle
  omega

/-- **No compact resolvent** under unboundedly many retained zero modes. -/
theorem not_hasCompactResolvent_of_injections [CompleteSpace H] {ι : Type*}
    (T : H →ₗ.[𝕜] H)
    (K : ι → Type*) [∀ i, AddCommGroup (K i)] [∀ i, Module ℝ (K i)]
    [∀ i, FiniteDimensional ℝ (K i)]
    (emb : ∀ i, K i →ₗ[ℝ] H) (hinj : ∀ i, Function.Injective (emb i))
    (hker : ∀ i x, emb i x ∈ partialKer T)
    (hunb : ∀ N : ℕ, ∃ i, N ≤ finrank ℝ (K i)) :
    ¬ HasCompactResolvent T := fun h =>
  not_finiteDimensional_partialKer_of_injections T K emb hinj hker hunb
    (finiteDimensional_partialKer_of_hasCompactResolvent h)

end General

open RenewalGeometry.UniversalOneFormDiracKernelGrowth

/-- **`cth:supp-extensive-kernel`, consequence clause.**  Let `d_k : V_k → W_k` be the
differentials of a cofinal family of connected periodic `A₃` root graphs with `n_k` vertices and
both orientations of the `e_k = 6 n_k` edges retained (`dim W_k = 12 n_k`; connectedness as
`dim ker d_k = 1`), with `n_k` unbounded.  Let `T` be a (possibly unbounded) limit operator on a
Hilbert space which retains all zero modes: each stage kernel `ker D_k` of the block Dirac operator
`D_k = universalDirac d_k` (dimension `11 n_k + 2`) injects real-linearly into `ker T`.  Then
`ker T` is infinite-dimensional and `T` has no compact resolvent. -/
theorem retained_universal_oneform_zero_modes_no_compact_resolvent
    {𝕜 : Type*} [RCLike 𝕜] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    [CompleteSpace H] [Module ℝ H] [IsScalarTower ℝ 𝕜 H]
    {V W : ℕ → Type*} [∀ k, NormedAddCommGroup (V k)] [∀ k, InnerProductSpace ℝ (V k)]
    [∀ k, FiniteDimensional ℝ (V k)] [∀ k, NormedAddCommGroup (W k)]
    [∀ k, InnerProductSpace ℝ (W k)] [∀ k, FiniteDimensional ℝ (W k)]
    (d : ∀ k, V k →L[ℝ] W k) (n : ℕ → ℕ)
    (hV : ∀ k, finrank ℝ (V k) = n k) (hW : ∀ k, finrank ℝ (W k) = 12 * n k)
    (hconn : ∀ k, finrank ℝ (LinearMap.ker (d k).toLinearMap) = 1)
    (hcofinal : ∀ N : ℕ, ∃ k, N ≤ n k)
    (T : H →ₗ.[𝕜] H)
    (emb : ∀ k, LinearMap.ker (universalDirac (d k)).toLinearMap →ₗ[ℝ] H)
    (hinj : ∀ k, Function.Injective (emb k))
    (hker : ∀ k x, emb k x ∈ partialKer T) :
    (∀ k, finrank ℝ (LinearMap.ker (universalDirac (d k)).toLinearMap) = 11 * n k + 2) ∧
      ¬ FiniteDimensional 𝕜 (partialKer T) ∧ ¬ HasCompactResolvent T := by
  have hdim : ∀ k, finrank ℝ (LinearMap.ker (universalDirac (d k)).toLinearMap) =
      11 * n k + 2 := fun k => periodic_A3_kernel_dimension (d k) (n k) (hV k) (hW k) (hconn k)
  have hunb : ∀ N : ℕ, ∃ k,
      N ≤ finrank ℝ (LinearMap.ker (universalDirac (d k)).toLinearMap) := by
    intro N
    obtain ⟨k, hk⟩ := hcofinal N
    exact ⟨k, by rw [hdim k]; omega⟩
  exact ⟨hdim,
    not_finiteDimensional_partialKer_of_injections T
      (fun k => LinearMap.ker (universalDirac (d k)).toLinearMap) emb hinj hker hunb,
    not_hasCompactResolvent_of_injections T
      (fun k => LinearMap.ker (universalDirac (d k)).toLinearMap) emb hinj hker hunb⟩

end RenewalGeometry.UniversalOneFormKernelNoCompactResolvent
