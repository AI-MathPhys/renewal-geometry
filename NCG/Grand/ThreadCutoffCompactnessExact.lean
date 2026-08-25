/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Thread-native cutoff compactness and full-sequence alternatives

Machinery for `thm:GT-thread-cutoff-compactness`.  Certified traces `y N ∈ C([0,T]; K)` with
values in a compact metric space `K` and one common continuation modulus form a relatively
compact family (Arzelà–Ascoli, `isCompact_closure_range`); every subsequential limit satisfies
every continuous defect that vanishes along the sequence (`defect_eq_zero_of_subseq`); the full
sequence converges when the limiting target is unique — every cluster point equals it
(`tendsto_of_unique_clusterPt`) — or when the traces obey a summable Cauchy estimate (TR.6c,
`tendsto_of_summable_dist`).
-/

open Filter Topology Set
open scoped BoundedContinuousFunction

namespace NCG
namespace ThreadCutoff

variable {K : Type*} [MetricSpace K] [CompactSpace K] {T : ℝ}

/-- A common continuation modulus for a family of traces: `dist (y N s) (y N t) ≤ ω (dist s t)`
with `ω → 0` at `0`. -/
structure IsCommonModulus (ω : ℝ → ℝ) (y : ℕ → C(Icc (0 : ℝ) T, K)) : Prop where
  bound : ∀ N : ℕ, ∀ s t : Icc (0 : ℝ) T, dist (y N s) (y N t) ≤ ω (dist s t)
  small : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 ≤ h → h < δ → ω h < ε

/-- The traces as bounded continuous functions. -/
noncomputable def bdd (y : ℕ → C(Icc (0 : ℝ) T, K)) (N : ℕ) : Icc (0 : ℝ) T →ᵇ K :=
  BoundedContinuousFunction.mkOfCompact (y N)

omit [CompactSpace K] in
theorem equicontinuous_of_modulus {ω : ℝ → ℝ} {y : ℕ → C(Icc (0 : ℝ) T, K)}
    (hω : IsCommonModulus ω y) :
    Equicontinuous ((↑) : Set.range (bdd y) → Icc (0 : ℝ) T → K) := by
  intro x₀
  rw [Metric.equicontinuousAt_iff]
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := hω.small ε hε
  refine ⟨δ, hδ, fun x hx f => ?_⟩
  obtain ⟨N, hN⟩ := f.2
  have h1 : (f : Icc (0 : ℝ) T →ᵇ K) x = y N x := by
    rw [← hN]; rfl
  have h2 : (f : Icc (0 : ℝ) T →ᵇ K) x₀ = y N x₀ := by
    rw [← hN]; rfl
  change dist ((f : Icc (0 : ℝ) T →ᵇ K) x₀) ((f : Icc (0 : ℝ) T →ᵇ K) x) < ε
  rw [h1, h2]
  refine lt_of_le_of_lt (hω.bound N x₀ x) (hδε _ dist_nonneg ?_)
  rwa [dist_comm]

/-- **Relative compactness** of the traces in `C([0,T]; K)` (Arzelà–Ascoli). -/
theorem isCompact_closure_range {ω : ℝ → ℝ} {y : ℕ → C(Icc (0 : ℝ) T, K)}
    (hω : IsCommonModulus ω y) : IsCompact (closure (Set.range y)) := by
  have hA : IsCompact (closure (Set.range (bdd y))) :=
    BoundedContinuousFunction.arzela_ascoli Set.univ isCompact_univ _ (fun _ _ _ => mem_univ _)
      (equicontinuous_of_modulus hω)
  set e : C(Icc (0 : ℝ) T, K) ≃ᵢ (Icc (0 : ℝ) T →ᵇ K) :=
    ContinuousMap.isometryEquivBoundedOfCompact (Icc (0 : ℝ) T) K with he
  have himage : e '' Set.range y = Set.range (bdd y) := by
    ext f
    constructor
    · rintro ⟨g, ⟨N, rfl⟩, rfl⟩
      exact ⟨N, rfl⟩
    · rintro ⟨N, rfl⟩
      exact ⟨y N, ⟨N, rfl⟩, rfl⟩
  have hpre : closure (Set.range y) = e.toHomeomorph ⁻¹' closure (Set.range (bdd y)) := by
    rw [e.toHomeomorph.preimage_closure, ← himage]
    congr 1
    exact (Equiv.preimage_image e.toHomeomorph.toEquiv _).symm
  rw [hpre]
  exact e.toHomeomorph.isCompact_preimage.mpr hA

/-- **Subsequential existence**: some subsequence converges in `C([0,T]; K)`. -/
theorem exists_subseq_tendsto {ω : ℝ → ℝ} {y : ℕ → C(Icc (0 : ℝ) T, K)}
    (hω : IsCommonModulus ω y) :
    ∃ z : C(Icc (0 : ℝ) T, K), ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (y ∘ φ) atTop (𝓝 z) := by
  obtain ⟨z, -, φ, hφ, hlim⟩ := (isCompact_closure_range hω).tendsto_subseq
    fun N => subset_closure (Set.mem_range_self N)
  exact ⟨z, φ, hφ, hlim⟩

omit [CompactSpace K] in
/-- **Core closure**: a continuous defect vanishing along the traces vanishes at every
subsequential limit. -/
theorem defect_eq_zero_of_subseq {y : ℕ → C(Icc (0 : ℝ) T, K)}
    {𝔡 : C(Icc (0 : ℝ) T, K) → ℝ} (hcont : Continuous 𝔡)
    (hvan : Tendsto (fun N => 𝔡 (y N)) atTop (𝓝 0)) {z : C(Icc (0 : ℝ) T, K)} {φ : ℕ → ℕ}
    (hφ : StrictMono φ) (hlim : Tendsto (y ∘ φ) atTop (𝓝 z)) : 𝔡 z = 0 := by
  have h1 : Tendsto (fun n => 𝔡 (y (φ n))) atTop (𝓝 (𝔡 z)) :=
    (hcont.tendsto z).comp hlim
  have h2 : Tendsto (fun n => 𝔡 (y (φ n))) atTop (𝓝 0) := hvan.comp hφ.tendsto_atTop
  exact tendsto_nhds_unique h1 h2

/-- **Full convergence under uniqueness**: if every cluster point of the traces is the declared
target, the whole sequence converges to it. -/
theorem tendsto_of_unique_clusterPt {ω : ℝ → ℝ} {y : ℕ → C(Icc (0 : ℝ) T, K)}
    (hω : IsCommonModulus ω y) {z : C(Icc (0 : ℝ) T, K)}
    (huniq : ∀ z' : C(Icc (0 : ℝ) T, K), MapClusterPt z' atTop y → z' = z) :
    Tendsto y atTop (𝓝 z) := by
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨a, -, φ, hφ, hlim⟩ := (isCompact_closure_range hω).tendsto_subseq
    (x := fun n => y (ns n)) fun n => subset_closure (Set.mem_range_self _)
  have hlim' : Tendsto (y ∘ (ns ∘ φ)) atTop (𝓝 a) := hlim
  have hcl : MapClusterPt a atTop y :=
    MapClusterPt.of_comp (hns.comp hφ.tendsto_atTop) hlim'.mapClusterPt
  refine ⟨φ, ?_⟩
  rw [huniq a hcl] at hlim
  exact hlim

/-- **(TR.6c)**: a summable Cauchy row gives full convergence. -/
theorem tendsto_of_summable_dist {y : ℕ → C(Icc (0 : ℝ) T, K)}
    (hsum : Summable fun N => dist (y N) (y (N + 1))) :
    ∃ z : C(Icc (0 : ℝ) T, K), Tendsto y atTop (𝓝 z) :=
  cauchySeq_tendsto_of_complete (cauchySeq_of_summable_dist hsum)

/-- **`thm:GT-thread-cutoff-compactness`**: relative compactness, subsequential existence,
closure of the defect core at every subsequential limit, and the two full-sequence
alternatives (unique target, summable Cauchy row). -/
theorem thread_cutoff_compactness {ω : ℝ → ℝ} {y : ℕ → C(Icc (0 : ℝ) T, K)}
    (hω : IsCommonModulus ω y) {ι : Type*} (𝔡 : ι → C(Icc (0 : ℝ) T, K) → ℝ)
    (hcont : ∀ j, Continuous (𝔡 j)) (hvan : ∀ j, Tendsto (fun N => 𝔡 j (y N)) atTop (𝓝 0)) :
    IsCompact (closure (Set.range y)) ∧
      (∃ z : C(Icc (0 : ℝ) T, K), ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (y ∘ φ) atTop (𝓝 z)) ∧
      (∀ (z : C(Icc (0 : ℝ) T, K)) (φ : ℕ → ℕ), StrictMono φ → Tendsto (y ∘ φ) atTop (𝓝 z) →
        ∀ j, 𝔡 j z = 0) ∧
      (∀ z : C(Icc (0 : ℝ) T, K),
        (∀ z', MapClusterPt z' atTop y → z' = z) → Tendsto y atTop (𝓝 z)) ∧
      ((Summable fun N => dist (y N) (y (N + 1))) →
        ∃ z : C(Icc (0 : ℝ) T, K), Tendsto y atTop (𝓝 z)) :=
  ⟨isCompact_closure_range hω, exists_subseq_tendsto hω,
    fun _z _φ hφ hlim j => defect_eq_zero_of_subseq (hcont j) (hvan j) hφ hlim,
    fun _z huniq => tendsto_of_unique_clusterPt hω huniq, tendsto_of_summable_dist⟩

end ThreadCutoff
end NCG
