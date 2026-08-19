/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteHermitianEulerEquicontinuity
import NCG.Grand.CompactEquicontinuousUniformConvergence

/-!
# Uniformity of limit Euler schemes on positive compact time sets

The sharp cutoff estimate is uniform in both cutoff and Euler order.  Under asymptotic density,
pointwise varying-space limits therefore inherit one common Lipschitz constant.  Ascoli then
upgrades pointwise convergence of the limit Euler scheme to uniform convergence on every compact
set bounded away from time zero.
-/

open Filter Set Topology Matrix
open scoped ComplexOrder Norms.L2Operator

noncomputable section

namespace NCG.VaryingHilbert.System

universe u v

variable {ι : ℕ → Type u}
variable [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Pointwise varying-space limits of the full finite Euler powers have a Lipschitz constant
uniform in the Euler order on a compact set of strictly positive times. -/
theorem exists_lipschitzOnWith_limit_finiteHermitianEulerPowers
    (J : System (K := ℂ) (H := H) (Hn := fun n ↦ EuclideanSpace ℂ (ι n)))
    (A : ∀ n, Matrix (ι n) (ι n) ℂ) (hA : ∀ n, (A n).PosSemidef)
    (Q : ℕ → ℝ → H →L[ℂ] H)
    (s : Set ℝ) (hs : IsCompact s) (hsPos : ∀ t ∈ s, 0 < t)
    (hdense : J.IsAsymptoticallyDense)
    (hQ : ∀ m, ∀ t ∈ s,
      J.StrongOperatorConverges J
        (fun n ↦ NCG.ImplicitEuler.finiteHermitianEulerResolventOperator
          (A n) t (m + 1))
        (Q m t))
    (x : H) :
    ∃ L : NNReal, ∀ m, LipschitzOnWith L (fun t ↦ Q m t x) s := by
  by_cases hsempty : s = ∅
  · refine ⟨0, fun m ↦ ?_⟩
    simp [hsempty, lipschitzOnWith_iff_norm_sub_le]
  obtain ⟨a, haMem, haMin⟩ := hs.exists_isMinOn (Set.nonempty_iff_ne_empty.mpr hsempty)
    continuous_id.continuousOn
  have ha : 0 < a := hsPos a haMem
  obtain ⟨xstage, hxstage⟩ := hdense x
  obtain ⟨C, hC, hCbound⟩ := hxstage.exists_pos_uniform_norm_bound J
  let L : NNReal := ⟨C / a, by positivity⟩
  refine ⟨L, fun m ↦ ?_⟩
  rw [lipschitzOnWith_iff_norm_sub_le]
  intro t ht r hr
  have hat : a ≤ t := haMin ht
  have har : a ≤ r := haMin hr
  have htconv : Tendsto
      (fun n ↦ J.embedding n
        (NCG.ImplicitEuler.finiteHermitianEulerResolventOperator
          (A n) t (m + 1) (xstage n)))
      atTop (𝓝 (Q m t x)) := by
    simpa only [StronglyConverges] using hQ m t ht xstage x hxstage
  have hrconv : Tendsto
      (fun n ↦ J.embedding n
        (NCG.ImplicitEuler.finiteHermitianEulerResolventOperator
          (A n) r (m + 1) (xstage n)))
      atTop (𝓝 (Q m r x)) := by
    simpa only [StronglyConverges] using hQ m r hr xstage x hxstage
  have hnorm : Tendsto
      (fun n ↦ ‖J.embedding n
          (NCG.ImplicitEuler.finiteHermitianEulerResolventOperator
            (A n) t (m + 1) (xstage n)) -
        J.embedding n
          (NCG.ImplicitEuler.finiteHermitianEulerResolventOperator
            (A n) r (m + 1) (xstage n))‖)
      atTop (𝓝 ‖Q m t x - Q m r x‖) :=
    (htconv.sub hrconv).norm
  apply le_of_tendsto hnorm
  filter_upwards [] with n
  rw [← map_sub]
  change ‖J.embedding n
    ((NCG.ImplicitEuler.finiteHermitianEulerResolventOperator
        (A n) t (m + 1) -
      NCG.ImplicitEuler.finiteHermitianEulerResolventOperator
        (A n) r (m + 1)) (xstage n))‖ ≤ _
  rw [(J.embedding n).norm_map]
  calc
    ‖(NCG.ImplicitEuler.finiteHermitianEulerResolventOperator
        (A n) t (m + 1) -
      NCG.ImplicitEuler.finiteHermitianEulerResolventOperator
        (A n) r (m + 1)) (xstage n)‖
        ≤ ‖NCG.ImplicitEuler.finiteHermitianEulerResolventOperator
              (A n) t (m + 1) -
            NCG.ImplicitEuler.finiteHermitianEulerResolventOperator
              (A n) r (m + 1)‖ * ‖xstage n‖ :=
          ContinuousLinearMap.le_opNorm _ _
    _ ≤ (|t - r| / a) * C :=
      mul_le_mul
        (NCG.ImplicitEuler.norm_finiteHermitianEulerResolventOperator_sub_le
          (hA n) (m + 1) (Nat.succ_pos m) ha har hat)
        (hCbound n) (norm_nonneg _) (by positivity)
    _ = (L : ℝ) * ‖t - r‖ := by
      rw [Real.norm_eq_abs]
      change (|t - r| / a) * C = (C / a) * |t - r|
      ring

/-- If the limit Euler powers converge pointwise in time, then they converge uniformly on every
compact set of strictly positive times.  No separate limit-side equicontinuity premise is needed.
-/
theorem tendstoUniformlyOn_limit_finiteHermitianEulerPowers_of_pointwise
    (J : System (K := ℂ) (H := H) (Hn := fun n ↦ EuclideanSpace ℂ (ι n)))
    (A : ∀ n, Matrix (ι n) (ι n) ℂ) (hA : ∀ n, (A n).PosSemidef)
    (Q : ℕ → ℝ → H →L[ℂ] H) (S : ℝ → H →L[ℂ] H)
    (s : Set ℝ) (hs : IsCompact s) (hsPos : ∀ t ∈ s, 0 < t)
    (hdense : J.IsAsymptoticallyDense)
    (hQ : ∀ m, ∀ t ∈ s,
      J.StrongOperatorConverges J
        (fun n ↦ NCG.ImplicitEuler.finiteHermitianEulerResolventOperator
          (A n) t (m + 1))
        (Q m t))
    (hpoint : ∀ x : H, ∀ t ∈ s,
      Tendsto (fun m ↦ Q m t x) atTop (𝓝 (S t x))) :
    ∀ x : H, TendstoUniformlyOn
      (fun m t ↦ Q m t x) (fun t ↦ S t x) atTop s := by
  intro x
  obtain ⟨L, hLip⟩ :=
    exists_lipschitzOnWith_limit_finiteHermitianEulerPowers
      J A hA Q s hs hsPos hdense hQ x
  exact NCG.IsCompact.tendstoUniformlyOn_of_equicontinuousOn hs
    ((LipschitzOnWith.uniformEquicontinuousOn _ L hLip).equicontinuousOn)
    (hpoint x)

end NCG.VaryingHilbert.System
