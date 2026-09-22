/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.OperatorLimits.VaryingHilbertMosco
import RenewalGeometry.OperatorLimits.MoscoRecoveryEnergyConvergence
import Mathlib.Topology.Sequences
/-!
# Transported Mosco convergence with an explicit limit stage, and asymptotic
# form compactness

Encodes `def:transported-mosco` and `def:asymptotic-compactness` of the
spacetime--gauge duality manuscript on the varying-Hilbert `System` carrier.

* `System.TransportedMoscoConverges Jlim q qlim`: the limit form lives on its own
  Hilbert space `Hlim` embedded by `Jlim`; (M1) every transported weak limit
  `B` lies in `Jlim Hlim`, `B = Jlim A`, with `qlim A ≤ liminf q_X(A_X)`;
  (M2) every `A ∈ D(qlim)` has a recovery sequence with `Jlim A_X → Jlim A`
  strongly and `q_X(A_X) → qlim A`.
* `extendByTop`: the limit form pushed to the common carrier (`+∞` off the
  range of `Jlim`); `TransportedMoscoConverges.moscoConverges_extendByTop`
  shows that, given asymptotic density, this recovers the earlier
  `System.MoscoConverges` encoding.
* `System.AsymptoticallyCompact q`: every sequence with
  `sup_X (‖A_X‖² + q_X(A_X)) < ∞` has a subsequence whose transported vectors
  converge strongly in the common carrier; `LimitFormCompact Jlim qlim` is the
  same requirement imposed on the limiting form (the constant system embedded
  by `Jlim`), and `AsymptoticallyCompactFamily` bundles both, as in the
  manuscript's definition.
-/

open scoped ENNReal

open Filter Topology

noncomputable section

namespace RenewalGeometry.VaryingHilbert

universe u v w w'

variable {K : Type u} [RCLike K]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace K (Hn n)]
variable {Hlim : Type w'} [NormedAddCommGroup Hlim] [InnerProductSpace K Hlim]

/-- The limit form pushed forward to the common carrier: `qlim A` at `Jlim A`,
and `+∞` off the range of the limit embedding. -/
def extendByTop (Jlim : Hlim →ₗᵢ[K] H) (qlim : Hlim → ℝ≥0∞) (B : H) : ℝ≥0∞ :=
  ⨅ (A : Hlim) (_ : Jlim A = B), qlim A

theorem extendByTop_apply (Jlim : Hlim →ₗᵢ[K] H) (qlim : Hlim → ℝ≥0∞) (A : Hlim) :
    extendByTop Jlim qlim (Jlim A) = qlim A := by
  apply le_antisymm
  · exact iInf_le_of_le A (iInf_le_of_le rfl le_rfl)
  · refine le_iInf fun A' => le_iInf fun hA' => ?_
    rw [Jlim.injective hA']

theorem extendByTop_eq_top (Jlim : Hlim →ₗᵢ[K] H) (qlim : Hlim → ℝ≥0∞) (B : H)
    (hB : ¬ ∃ A : Hlim, Jlim A = B ∧ qlim A ≠ ∞) :
    extendByTop Jlim qlim B = ∞ := by
  rw [extendByTop, iInf_eq_top]
  intro A
  rw [iInf_eq_top]
  intro hA
  by_contra hne
  exact hB ⟨A, hA, hne⟩

/-- The limiting Hilbert space viewed as a constant varying-space system embedded
by `Jlim`. -/
def constantEmbeddingSystem (Jlim : Hlim →ₗᵢ[K] H) :
    System (K := K) (H := H) (Hn := fun _ ↦ Hlim) where
  embedding _ := Jlim

namespace System

variable (J : System (K := K) (H := H) (Hn := Hn))

/-- **`def:transported-mosco`** (spacetime--gauge duality manuscript).  Transported
Mosco convergence of the stage forms `q_X` on `H_X` to the limit form `qlim` on
`Hlim`, all compared inside the common carrier through the isometric embeddings
`J_X` and `Jlim`. -/
structure TransportedMoscoConverges (Jlim : Hlim →ₗᵢ[K] H)
    (q : (n : ℕ) → Hn n → ℝ≥0∞) (qlim : Hlim → ℝ≥0∞) : Prop where
  /-- (M1): a transported weak limit lies in `Jlim Hlim`, `B = Jlim A`, and
  `qlim A ≤ liminf q_X(A_X)`. -/
  weak_liminf : ∀ (x : ∀ n, Hn n) (B : H), J.WeaklyConverges x B →
    ∃ A : Hlim, Jlim A = B ∧ qlim A ≤ liminf (fun n ↦ q n (x n)) atTop
  /-- (M2): every `A ∈ D(qlim)` has a recovery sequence `A_X ∈ D(q_X)` with
  `J_X A_X → Jlim A` strongly and `q_X(A_X) → qlim A`. -/
  recovery : ∀ A : Hlim, qlim A ≠ ∞ →
    ∃ x : ∀ n, Hn n, J.StronglyConverges x (Jlim A) ∧
      Tendsto (fun n ↦ q n (x n)) atTop (𝓝 (qlim A))

/-- A recovery sequence of transported Mosco convergence has finite energies
eventually; in particular its members lie in the stage form domains. -/
theorem TransportedMoscoConverges.recovery_eventually_finite
    {Jlim : Hlim →ₗᵢ[K] H} {q : (n : ℕ) → Hn n → ℝ≥0∞} {qlim : Hlim → ℝ≥0∞}
    (h : J.TransportedMoscoConverges Jlim q qlim) (A : Hlim) (hA : qlim A ≠ ∞) :
    ∃ x : ∀ n, Hn n, J.StronglyConverges x (Jlim A) ∧
      Tendsto (fun n ↦ q n (x n)) atTop (𝓝 (qlim A)) ∧
      ∀ᶠ n in atTop, q n (x n) ≠ ∞ := by
  obtain ⟨x, hx, hq⟩ := h.recovery A hA
  refine ⟨x, hx, hq, ?_⟩
  have hlt : qlim A < ∞ := lt_top_iff_ne_top.2 hA
  exact (hq.eventually (gt_mem_nhds hlt)).mono fun n hn => hn.ne

/-- Transported Mosco convergence with an explicit limit stage yields the
common-carrier `MoscoConverges` encoding for the limit form extended by `+∞`
off `Jlim Hlim`, provided the stage images are asymptotically dense. -/
theorem TransportedMoscoConverges.moscoConverges_extendByTop
    {Jlim : Hlim →ₗᵢ[K] H} {q : (n : ℕ) → Hn n → ℝ≥0∞} {qlim : Hlim → ℝ≥0∞}
    (h : J.TransportedMoscoConverges Jlim q qlim)
    (hdense : J.IsAsymptoticallyDense) :
    J.MoscoConverges q (extendByTop Jlim qlim) where
  liminf_le x B hx := by
    obtain ⟨A, rfl, hA⟩ := h.weak_liminf x B hx
    rw [extendByTop_apply]
    exact hA
  recovery B := by
    by_cases hB : ∃ A : Hlim, Jlim A = B ∧ qlim A ≠ ∞
    · obtain ⟨A, rfl, hA⟩ := hB
      obtain ⟨x, hx, hq⟩ := h.recovery A hA
      exact ⟨x, hx, by rw [hq.limsup_eq, extendByTop_apply]⟩
    · obtain ⟨x, hx⟩ := hdense B
      refine ⟨x, hx, ?_⟩
      rw [extendByTop_eq_top Jlim qlim B hB]
      exact le_top

/-- Conversely, the common-carrier encoding for the extended limit form supplies
the recovery clause (M2) with an explicit limit stage. -/
theorem MoscoConverges.transported_recovery
    {Jlim : Hlim →ₗᵢ[K] H} {q : (n : ℕ) → Hn n → ℝ≥0∞} {qlim : Hlim → ℝ≥0∞}
    (h : J.MoscoConverges q (extendByTop Jlim qlim)) (A : Hlim) :
    ∃ x : ∀ n, Hn n, J.StronglyConverges x (Jlim A) ∧
      Tendsto (fun n ↦ q n (x n)) atTop (𝓝 (qlim A)) := by
  obtain ⟨x, hx, hq⟩ := h.exists_recovery_energy_tendsto (Jlim A)
  rw [extendByTop_apply] at hq
  exact ⟨x, hx, hq⟩

/-- **`def:asymptotic-compactness`**, stage clause (spacetime--gauge duality
manuscript).  Every dependent sequence with
`sup_X (‖A_X‖² + q_X(A_X)) < ∞` has a subsequence whose transported vectors
converge strongly in the common carrier. -/
def AsymptoticallyCompact (q : (n : ℕ) → Hn n → ℝ≥0∞) : Prop :=
  ∀ x : ∀ n, Hn n,
    (∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ n, ENNReal.ofReal (‖x n‖ ^ 2) + q n (x n) ≤ C) →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ y : H, Tendsto (fun k ↦ J.embedding (φ k) (x (φ k))) atTop (𝓝 y)

/-- A uniform compact container for all bounded-energy transported vectors gives
asymptotic compactness. -/
theorem asymptoticallyCompact_of_subset_compact (q : (n : ℕ) → Hn n → ℝ≥0∞)
    (S : ℝ≥0∞ → Set H) (hS : ∀ C, C ≠ ∞ → IsCompact (S C))
    (hsub : ∀ C n (x : Hn n), ENNReal.ofReal (‖x‖ ^ 2) + q n x ≤ C →
      J.embedding n x ∈ S C) :
    J.AsymptoticallyCompact q := by
  intro x hx
  obtain ⟨C, hC, hbound⟩ := hx
  obtain ⟨y, -, φ, hφ, hy⟩ :=
    (hS C hC).tendsto_subseq (x := fun n ↦ J.embedding n (x n))
      fun n ↦ hsub C n (x n) (hbound n)
  exact ⟨φ, hφ, y, hy⟩

end System

/-- **`def:asymptotic-compactness`**, limit clause: the same requirement imposed
on the limiting form, i.e. asymptotic compactness of the constant system
embedded by `Jlim`. -/
def LimitFormCompact (Jlim : Hlim →ₗᵢ[K] H) (qlim : Hlim → ℝ≥0∞) : Prop :=
  (constantEmbeddingSystem Jlim).AsymptoticallyCompact (fun _ ↦ qlim)

/-- Unfolded form of the limit clause: every bounded-energy sequence in `Hlim`
has a subsequence whose `Jlim`-images converge strongly in the common carrier. -/
theorem limitFormCompact_iff (Jlim : Hlim →ₗᵢ[K] H) (qlim : Hlim → ℝ≥0∞) :
    LimitFormCompact Jlim qlim ↔
      ∀ A : ℕ → Hlim,
        (∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ k, ENNReal.ofReal (‖A k‖ ^ 2) + qlim (A k) ≤ C) →
        ∃ φ : ℕ → ℕ, StrictMono φ ∧
          ∃ y : H, Tendsto (fun k ↦ Jlim (A (φ k))) atTop (𝓝 y) :=
  Iff.rfl

/-- **`def:asymptotic-compactness`** (spacetime--gauge duality manuscript): the
family `(q_X)` together with the limiting form is asymptotically compact. -/
def AsymptoticallyCompactFamily (J : System (K := K) (H := H) (Hn := Hn))
    (Jlim : Hlim →ₗᵢ[K] H) (q : (n : ℕ) → Hn n → ℝ≥0∞) (qlim : Hlim → ℝ≥0∞) :
    Prop :=
  J.AsymptoticallyCompact q ∧ LimitFormCompact Jlim qlim

end RenewalGeometry.VaryingHilbert
