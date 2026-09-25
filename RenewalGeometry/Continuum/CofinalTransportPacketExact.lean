/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Summable cofinal transport (`prop:cofinal-transport`, Einstein–SM action closure)

Abstract packet form of the proposition.  A local strong packet on a compact region
`K` is modelled as a finite family of components `z i ∈ E i` (`i : ι`, `ι` finite), each
`E i` a complete metric space — the curvature, covariant-derivative, spinor, …
norms entering `d_K`, and the coefficient bank `θ` — with the packet distance

  `d_K(z, w) = Σ_i dist (z i) (w i)`  (`packetDist`).

For a cofinal sequence `z n` with summable adjacent transport
`d_K(z (n+1), z n) ≤ η n`, `Σ η n < ∞` (**`eq:cofinal-transport`**):

* `packetDist_le_sum_Ico`: the telescoped triangle inequality
  `d_K(z m, z n) ≤ Σ_{j ∈ [n, m)} η j`;
* `cauchySeq_component`: every component sequence is Cauchy;
* `exists_unique_packet_limit`: the sequence converges in `d_K` to a unique packet limit;
* `packet_limit_unique`: uniqueness of `d_K`-limits (no subsequence choice remains);
* `subseq_limit_eq`: any subsequential `d_K`-limit (such as the strong-packet
  accumulation point supplied by `thm:certificate-packet`) coincides with the full
  limit — this is the identification clause of the proposition, with the curvature and
  covariant-derivative identifications carried by that subsequential limit;
* `route_limits_eq`: two admissible routes whose direct comparison
  `d_K(z n, z' n)` tends to zero have the same limit.

`tendsto_packetDist_zero_iff` records that `d_K`-convergence is convergence in the
product topology, so the limits above are ordinary limits in the packet space.
-/

open Filter Topology Finset

namespace RenewalGeometry.CofinalTransportPacket

variable {ι : Type*} [Fintype ι] {E : ι → Type*} [∀ i, MetricSpace (E i)]

/-- The packet distance `d_K(z, w) = Σ_i dist (z i) (w i)`. -/
noncomputable def packetDist (z w : (i : ι) → E i) : ℝ := ∑ i, dist (z i) (w i)

theorem packetDist_nonneg (z w : (i : ι) → E i) : 0 ≤ packetDist z w :=
  Finset.sum_nonneg fun i _ => dist_nonneg

theorem packetDist_comm (z w : (i : ι) → E i) : packetDist z w = packetDist w z := by
  unfold packetDist; simp_rw [dist_comm]

theorem packetDist_triangle (z w u : (i : ι) → E i) :
    packetDist z u ≤ packetDist z w + packetDist w u := by
  unfold packetDist
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => dist_triangle _ _ _

theorem dist_component_le_packetDist (z w : (i : ι) → E i) (i : ι) :
    dist (z i) (w i) ≤ packetDist z w :=
  Finset.single_le_sum (f := fun i => dist (z i) (w i)) (fun i _ => dist_nonneg)
    (Finset.mem_univ i)

/-- `d_K`-convergence is convergence in the product topology of the packet space. -/
theorem tendsto_packetDist_zero_iff (z : ℕ → (i : ι) → E i) (w : (i : ι) → E i) :
    Tendsto (fun n => packetDist (z n) w) atTop (𝓝 0) ↔ Tendsto z atTop (𝓝 w) := by
  constructor
  · intro h
    rw [tendsto_pi_nhds]
    intro i
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun n => dist_nonneg) (fun n => dist_component_le_packetDist _ _ i) h
  · intro h
    rw [tendsto_pi_nhds] at h
    have : Tendsto (fun n => ∑ i, dist (z n i) (w i)) atTop (𝓝 (∑ i : ι, (0 : ℝ))) :=
      tendsto_finsetSum _ fun i _ => (tendsto_iff_dist_tendsto_zero.1 (h i))
    simpa [packetDist] using this

/-- The telescoped triangle inequality `d_K(z m, z n) ≤ Σ_{j ∈ [n, m)} η j`. -/
theorem packetDist_le_sum_Ico (z : ℕ → (i : ι) → E i) (η : ℕ → ℝ)
    (hη : ∀ n, packetDist (z (n + 1)) (z n) ≤ η n) {n m : ℕ} (hnm : n ≤ m) :
    packetDist (z m) (z n) ≤ ∑ j ∈ Finset.Ico n m, η j := by
  induction m, hnm using Nat.le_induction with
  | base =>
    simp [packetDist]
  | succ m hnm ih =>
    rw [Finset.sum_Ico_succ_top hnm]
    calc packetDist (z (m + 1)) (z n)
        ≤ packetDist (z (m + 1)) (z m) + packetDist (z m) (z n) := packetDist_triangle _ _ _
      _ ≤ η m + ∑ j ∈ Finset.Ico n m, η j := add_le_add (hη m) ih
      _ = ∑ j ∈ Finset.Ico n m, η j + η m := add_comm _ _

/-- Every component of a summably transported cofinal sequence is Cauchy. -/
theorem cauchySeq_component (z : ℕ → (i : ι) → E i) (η : ℕ → ℝ)
    (hη : ∀ n, packetDist (z (n + 1)) (z n) ≤ η n) (hsum : Summable η) (i : ι) :
    CauchySeq (fun n => z n i) := by
  refine cauchySeq_of_dist_le_of_summable η (fun n => ?_) hsum
  calc dist (z n i) (z (n + 1) i) = dist (z (n + 1) i) (z n i) := dist_comm _ _
    _ ≤ packetDist (z (n + 1)) (z n) := dist_component_le_packetDist _ _ i
    _ ≤ η n := hη n

/-- **`prop:cofinal-transport`, convergence.**  A summably transported cofinal
sequence converges in `d_K` to a unique packet limit. -/
theorem exists_unique_packet_limit [∀ i, CompleteSpace (E i)]
    (z : ℕ → (i : ι) → E i) (η : ℕ → ℝ)
    (hη : ∀ n, packetDist (z (n + 1)) (z n) ≤ η n) (hsum : Summable η) :
    ∃! w : (i : ι) → E i, Tendsto (fun n => packetDist (z n) w) atTop (𝓝 0) := by
  have hlim : ∀ i, ∃ wi : E i, Tendsto (fun n => z n i) atTop (𝓝 wi) := fun i =>
    cauchySeq_tendsto_of_complete (cauchySeq_component z η hη hsum i)
  choose w hw using hlim
  refine ⟨w, ?_, fun w' hw' => ?_⟩
  · show Tendsto (fun n => packetDist (z n) w) atTop (𝓝 0)
    rw [tendsto_packetDist_zero_iff, tendsto_pi_nhds]
    exact hw
  · have hw'' : Tendsto (fun n => packetDist (z n) w') atTop (𝓝 0) := hw'
    rw [tendsto_packetDist_zero_iff] at hw''
    have hzw : Tendsto z atTop (𝓝 w) := tendsto_pi_nhds.2 hw
    exact tendsto_nhds_unique hw'' hzw

/-- Uniqueness of `d_K`-limits: no subsequence choice remains. -/
theorem packet_limit_unique (z : ℕ → (i : ι) → E i) (w w' : (i : ι) → E i)
    (hw : Tendsto (fun n => packetDist (z n) w) atTop (𝓝 0))
    (hw' : Tendsto (fun n => packetDist (z n) w') atTop (𝓝 0)) : w = w' := by
  rw [tendsto_packetDist_zero_iff] at hw hw'
  exact tendsto_nhds_unique hw hw'

/-- **Identification clause.**  A subsequential `d_K`-limit `w'` of the sequence (for
instance the strong-packet accumulation point supplied by `thm:certificate-packet`, which
carries the algebraic curvature and covariant-derivative identifications) coincides with
the full `d_K`-limit `w`. -/
theorem subseq_limit_eq (z : ℕ → (i : ι) → E i) (w w' : (i : ι) → E i)
    (hw : Tendsto (fun n => packetDist (z n) w) atTop (𝓝 0))
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hw' : Tendsto (fun k => packetDist (z (φ k)) w') atTop (𝓝 0)) : w = w' := by
  rw [tendsto_packetDist_zero_iff] at hw hw'
  exact tendsto_nhds_unique (hw.comp hφ.tendsto_atTop) hw'

/-- **Route independence.**  Two admissible cofinal routes with `d_K`-limits `w`, `w'`
whose direct comparison `d_K(z n, z' n)` tends to zero have the same limit. -/
theorem route_limits_eq (z z' : ℕ → (i : ι) → E i) (w w' : (i : ι) → E i)
    (hw : Tendsto (fun n => packetDist (z n) w) atTop (𝓝 0))
    (hw' : Tendsto (fun n => packetDist (z' n) w') atTop (𝓝 0))
    (hcmp : Tendsto (fun n => packetDist (z n) (z' n)) atTop (𝓝 0)) : w = w' := by
  have h : Tendsto (fun n => packetDist (z n) w') atTop (𝓝 0) := by
    have hmaj : Tendsto (fun n => packetDist (z n) (z' n) + packetDist (z' n) w')
        atTop (𝓝 0) := by simpa using hcmp.add hw'
    exact squeeze_zero (fun n => packetDist_nonneg _ _)
      (fun n => packetDist_triangle _ _ _) hmaj
  exact packet_limit_unique z w w' hw h

end RenewalGeometry.CofinalTransportPacket
