/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.VaryingHilbertCollectiveCompactness

/-!
# Operations on varying-Hilbert collectively compact families

Collective compactness is stable under addition, fixed scalar multiplication, and uniformly
bounded precomposition.  The last operation is the varying-space analogue of the elementary fact
that a compact operator composed on the right with a bounded operator remains compact, with the
uniform bound needed to control all cutoff stages simultaneously.
-/

open Set

open scoped Pointwise
noncomputable section

namespace NCG.VaryingHilbert.System

universe u v w v' w'

variable {K : Type u} [RCLike K]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace K (Hn n)]
variable {G : Type v'} [NormedAddCommGroup G] [InnerProductSpace K G]
variable {Gn : ℕ → Type w'}
variable [∀ n, NormedAddCommGroup (Gn n)] [∀ n, InnerProductSpace K (Gn n)]

variable (L : System (K := K) (H := G) (Hn := Gn))

/-- Addition preserves collective compactness for genuinely varying source and target spaces. -/
theorem CollectivelyCompact.add_family
    {Tn Sn : ∀ n, Hn n →L[K] Gn n}
    (hT : L.CollectivelyCompact Tn) (hS : L.CollectivelyCompact Sn) :
    L.CollectivelyCompact (fun n ↦ Tn n + Sn n) := by
  obtain ⟨C, hC, hTC⟩ := hT
  obtain ⟨D, hD, hSD⟩ := hS
  refine ⟨C + D, hC.add hD, ?_⟩
  intro n y hy
  obtain ⟨x, hx, rfl⟩ := hy
  change L.embedding n ((Tn n + Sn n) x) ∈ C + D
  rw [add_apply, map_add]
  exact Set.add_mem_add (hTC n ⟨x, hx, rfl⟩) (hSD n ⟨x, hx, rfl⟩)

/-- Multiplication by one fixed scalar preserves collective compactness. -/
theorem CollectivelyCompact.smul_family
    {Tn : ∀ n, Hn n →L[K] Gn n} (c : K)
    (hT : L.CollectivelyCompact Tn) :
    L.CollectivelyCompact (fun n ↦ c • Tn n) := by
  obtain ⟨C, hC, hTC⟩ := hT
  refine ⟨c • C, hC.image (continuous_id.const_smul c), ?_⟩
  intro n y hy
  obtain ⟨x, hx, rfl⟩ := hy
  change L.embedding n ((c • Tn n) x) ∈ c • C
  rw [smul_apply, map_smul]
  exact smul_mem_smul_set (hTC n ⟨x, hx, rfl⟩)

/-- A collectively compact family remains collectively compact after uniformly bounded
precomposition on its varying source spaces. -/
theorem CollectivelyCompact.precomp_uniformlyBounded
    {Tn : ∀ n, Hn n →L[K] Gn n} {Sn : ∀ n, Hn n →L[K] Hn n}
    (hT : L.CollectivelyCompact Tn) (B : ℝ) (hB : 0 < B)
    (hS : ∀ n, ‖Sn n‖ ≤ B) :
    L.CollectivelyCompact (fun n ↦ (Tn n).comp (Sn n)) := by
  obtain ⟨C, hC, hTC⟩ := hT
  let scale : G →L[K] G := (B : K) • ContinuousLinearMap.id K G
  refine ⟨scale '' C, hC.image scale.continuous, ?_⟩
  intro n y hy
  obtain ⟨x, hx, rfl⟩ := hy
  have hxNorm : ‖x‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hx
  have hSn : ‖Sn n x‖ ≤ B := by
    calc
      ‖Sn n x‖ ≤ ‖Sn n‖ * ‖x‖ := (Sn n).le_opNorm x
      _ ≤ B * 1 := mul_le_mul (hS n) hxNorm (norm_nonneg x) hB.le
      _ = B := mul_one B
  let z : Hn n := ((B : K)⁻¹) • Sn n x
  have hz : ‖z‖ ≤ 1 := by
    change ‖((B : K)⁻¹) • Sn n x‖ ≤ 1
    rw [norm_smul]
    have hnormB : ‖(B : K)‖ = B := by simp [abs_of_pos hB]
    rw [norm_inv, hnormB]
    rw [inv_mul_le_one₀ hB]
    exact hSn
  have hzC : L.embedding n (Tn n z) ∈ C :=
    hTC n ⟨z, by simpa only [Metric.mem_closedBall, dist_zero_right] using hz, rfl⟩
  refine ⟨L.embedding n (Tn n z), hzC, ?_⟩
  change ((B : K) • ContinuousLinearMap.id K G) (L.embedding n (Tn n z)) =
    L.embedding n (Tn n (Sn n x))
  simp only [smul_apply, ContinuousLinearMap.id_apply]
  rw [← map_smul, ← map_smul]
  dsimp [z]
  rw [smul_smul]
  have hB0 : (B : K) ≠ 0 := by exact_mod_cast ne_of_gt hB
  rw [mul_inv_cancel₀ hB0, one_smul]

/-- A reversed resolvent identity propagates collective compactness from one shift to another,
provided the new-shift resolvents are uniformly bounded. -/
theorem CollectivelyCompact.of_reversed_resolvent_identity
    (Rn : ℝ → ∀ n, Gn n →L[K] Gn n) (a b : ℝ)
    (ha : L.CollectivelyCompact (Rn a))
    (B : ℝ) (hB : 0 < B) (hbBound : ∀ n, ‖Rn b n‖ ≤ B)
    (hidentity : ∀ n,
      Rn b n = Rn a n + (((a - b : ℝ) : K)) •
        ((Rn a n).comp (Rn b n))) :
    L.CollectivelyCompact (Rn b) := by
  have hcomp : L.CollectivelyCompact
      (fun n ↦ (Rn a n).comp (Rn b n)) :=
    ha.precomp_uniformlyBounded L B hB hbBound
  have hsum := ha.add_family L
    (hcomp.smul_family L (((a - b : ℝ) : K)))
  have heq :
      (fun n ↦ Rn a n + (((a - b : ℝ) : K)) •
        ((Rn a n).comp (Rn b n))) = Rn b := by
    funext n
    exact (hidentity n).symm
  exact heq ▸ hsum

end NCG.VaryingHilbert.System
