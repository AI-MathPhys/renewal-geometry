/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.Analysis.Complex.Liouville

/-!
# Critical weighted first and pair locality

This module proves `thm:GTLOC-critical-weighted-locality`.  It isolates the
jointly commanded, weighted holomorphic packet needed by the manuscript and
applies vector-valued Cauchy estimates once for the first response and twice
for the mixed response.  The last two conclusions use the packet's physical
Lipschitz-weight compression law.
-/

open Set

noncomputable section

namespace NCG
namespace CriticalWeightedResponseLocality

universe u v w

variable {Q : Type u} [Nonempty Q]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
variable {Region : Type w}

/-- Supremum over all admissible physical Lipschitz weights. -/
def weightedNorm (T : Q → F) : ℝ := sSup (Set.range fun q => ‖T q‖)

theorem weightedNorm_le {T : Q → F} {K : ℝ} (h : ∀ q, ‖T q‖ ≤ K) :
    weightedNorm T ≤ K := by
  apply csSup_le
  · exact Set.range_nonempty _
  · rintro r ⟨q, rfl⟩
    exact h q

/-- A literal weighted critical common-form packet.  `weightedFamily q z w`
is `W_q exp(-t A(z,w)) W_q⁻¹`.  The two compatibility fields record that the
same similarity is applied before differentiating the inherited semigroup.
The final field is exactly the physical Lipschitz off-diagonal estimate. -/
structure Packet (Q : Type u) (F : Type v) (Region : Type w)
    [NormedAddCommGroup F] [NormedSpace ℂ F] where
  weightedFamily : Q → ℂ → ℂ → F
  firstResponse : F
  pairResponse : F
  weight : Q → F → F
  weight_first : ∀ q,
    weight q firstResponse = deriv (fun z => weightedFamily q z 0) 0
  weight_pair : ∀ q,
    weight q pairResponse =
      deriv (fun z => deriv (fun w => weightedFamily q z w) 0) 0
  compress : Region → Region → F → F
  distance : Region → Region → ℝ
  compression_bound : ∀ (mu : ℝ), 0 ≤ mu → ∀ X Y T,
    ‖compress X Y T‖ ≤ Real.exp (-mu * distance X Y) *
      weightedNorm (fun q => weight q T)

/-- Closed-polydisc holomorphy in precisely the slices used by the two Cauchy
estimates.  This is the finite common-form holomorphic packet of the theorem. -/
def HolomorphicOnClosedPolydisc (P : Packet Q F Region) (rB rC : ℝ) : Prop :=
  (∀ q z, ‖z‖ ≤ rB →
      DiffContOnCl ℂ (fun w => P.weightedFamily q z w) (Metric.ball 0 rC)) ∧
  (∀ q, DiffContOnCl ℂ (fun z => P.weightedFamily q z 0) (Metric.ball 0 rB)) ∧
  (∀ q, DiffContOnCl ℂ
      (fun z => deriv (fun w => P.weightedFamily q z w) 0)
      (Metric.ball 0 rB))

/-- The weighted collar on the distinguished command circles. -/
def HasWeightedCollar (P : Packet Q F Region) (rB rC M v t : ℝ) : Prop :=
  ∀ q z w, ‖z‖ = rB → ‖w‖ = rC →
    ‖P.weightedFamily q z w‖ ≤ M * Real.exp (v * t)

private theorem value_on_outer_circle_bound
    (P : Packet Q F Region) {rB rC M v t : ℝ}
    (hrC : 0 < rC) (holo : HolomorphicOnClosedPolydisc P rB rC)
    (hcollar : HasWeightedCollar P rB rC M v t)
    (q : Q) (z : ℂ) (hz : ‖z‖ = rB) :
    ‖P.weightedFamily q z 0‖ ≤ M * Real.exp (v * t) := by
  have hzle : ‖z‖ ≤ rB := hz.le
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
    (F := F) 0 hrC (holo.1 q z hzle)
    (fun w hw => hcollar q z w hz (by simpa [Metric.mem_sphere] using hw))
  simpa using h

private theorem first_weight_pointwise
    (P : Packet Q F Region) {rB rC M v t : ℝ}
    (hrB : 0 < rB) (hrC : 0 < rC)
    (holo : HolomorphicOnClosedPolydisc P rB rC)
    (hcollar : HasWeightedCollar P rB rC M v t) (q : Q) :
    ‖P.weight q P.firstResponse‖ ≤ (M / rB) * Real.exp (v * t) := by
  rw [P.weight_first q]
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (c := (0 : ℂ)) (R := rB) (C := M * Real.exp (v * t))
    (f := fun z => P.weightedFamily q z 0)
    hrB (holo.2.1 q) (fun z hz =>
      value_on_outer_circle_bound P hrC holo hcollar q z
        (by simpa [Metric.mem_sphere] using hz))
  calc
    ‖deriv (fun z => P.weightedFamily q z 0) 0‖
        ≤ M * Real.exp (v * t) / rB := h
    _ = (M / rB) * Real.exp (v * t) := by
      field_simp

private theorem w_derivative_on_outer_circle_bound
    (P : Packet Q F Region) {rB rC M v t : ℝ}
    (hrC : 0 < rC) (holo : HolomorphicOnClosedPolydisc P rB rC)
    (hcollar : HasWeightedCollar P rB rC M v t)
    (q : Q) (z : ℂ) (hz : ‖z‖ = rB) :
    ‖deriv (fun w => P.weightedFamily q z w) 0‖ ≤
      M * Real.exp (v * t) / rC := by
  exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    hrC (holo.1 q z hz.le)
      (fun w hw => hcollar q z w hz (by simpa [Metric.mem_sphere] using hw))

private theorem pair_weight_pointwise
    (P : Packet Q F Region) {rB rC M v t : ℝ}
    (hrB : 0 < rB) (hrC : 0 < rC)
    (holo : HolomorphicOnClosedPolydisc P rB rC)
    (hcollar : HasWeightedCollar P rB rC M v t) (q : Q) :
    ‖P.weight q P.pairResponse‖ ≤ (M / (rB * rC)) * Real.exp (v * t) := by
  rw [P.weight_pair q]
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (c := (0 : ℂ)) (R := rB) (C := M * Real.exp (v * t) / rC)
    (f := fun z => deriv (fun w => P.weightedFamily q z w) 0)
    hrB (holo.2.2 q) (fun z hz =>
      w_derivative_on_outer_circle_bound P hrC holo hcollar q z
        (by simpa [Metric.mem_sphere] using hz))
  calc
    ‖deriv (fun z => deriv (fun w => P.weightedFamily q z w) 0) 0‖
        ≤ (M * Real.exp (v * t) / rC) / rB := h
    _ = (M / (rB * rC)) * Real.exp (v * t) := by
      field_simp
      <;> ring

/-- Weighted Cauchy bounds for the critical first and pair responses. -/
theorem critical_weighted_bounds
    (P : Packet Q F Region) {rB rC M v t : ℝ}
    (hrB : 0 < rB) (hrC : 0 < rC)
    (holo : HolomorphicOnClosedPolydisc P rB rC)
    (hcollar : HasWeightedCollar P rB rC M v t) :
    weightedNorm (fun q => P.weight q P.firstResponse) ≤
        (M / rB) * Real.exp (v * t) ∧
    weightedNorm (fun q => P.weight q P.pairResponse) ≤
        (M / (rB * rC)) * Real.exp (v * t) :=
  ⟨weightedNorm_le (first_weight_pointwise P hrB hrC holo hcollar),
    weightedNorm_le (pair_weight_pointwise P hrB hrC holo hcollar)⟩

/-- **`thm:GTLOC-critical-weighted-locality`.**  Cauchy estimates give the
two weighted bounds and the physical Lipschitz compression law gives the two
off-diagonal exponential collars. -/
theorem critical_weighted_first_pair_locality
    (P : Packet Q F Region) {rB rC M v t mu : ℝ}
    (hrB : 0 < rB) (hrC : 0 < rC) (hmu : 0 ≤ mu)
    (holo : HolomorphicOnClosedPolydisc P rB rC)
    (hcollar : HasWeightedCollar P rB rC M v t)
    (X Y : Region) :
    weightedNorm (fun q => P.weight q P.firstResponse) ≤
        (M / rB) * Real.exp (v * t) ∧
    weightedNorm (fun q => P.weight q P.pairResponse) ≤
        (M / (rB * rC)) * Real.exp (v * t) ∧
    ‖P.compress X Y P.firstResponse‖ ≤
        (M / rB) * Real.exp (v * t - mu * P.distance X Y) ∧
    ‖P.compress X Y P.pairResponse‖ ≤
        (M / (rB * rC)) * Real.exp (v * t - mu * P.distance X Y) := by
  obtain ⟨hfirst, hpair⟩ := critical_weighted_bounds P hrB hrC holo hcollar
  refine ⟨hfirst, hpair, ?_, ?_⟩
  · calc
      ‖P.compress X Y P.firstResponse‖
          ≤ Real.exp (-mu * P.distance X Y) *
              weightedNorm (fun q => P.weight q P.firstResponse) :=
            P.compression_bound mu hmu X Y P.firstResponse
      _ ≤ Real.exp (-mu * P.distance X Y) *
            ((M / rB) * Real.exp (v * t)) := by
              gcongr
      _ = (M / rB) * Real.exp (v * t - mu * P.distance X Y) := by
            rw [show v * t - mu * P.distance X Y =
              (-mu * P.distance X Y) + v * t by ring, Real.exp_add]
            ring
  · calc
      ‖P.compress X Y P.pairResponse‖
          ≤ Real.exp (-mu * P.distance X Y) *
              weightedNorm (fun q => P.weight q P.pairResponse) :=
            P.compression_bound mu hmu X Y P.pairResponse
      _ ≤ Real.exp (-mu * P.distance X Y) *
            ((M / (rB * rC)) * Real.exp (v * t)) := by
              gcongr
      _ = (M / (rB * rC)) *
            Real.exp (v * t - mu * P.distance X Y) := by
            rw [show v * t - mu * P.distance X Y =
              (-mu * P.distance X Y) + v * t by ring, Real.exp_add]
            ring

end CriticalWeightedResponseLocality
end NCG
