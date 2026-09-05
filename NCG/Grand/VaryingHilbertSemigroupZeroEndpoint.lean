/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.UniformSemigroupApproximation

/-!
# Attaching time zero to varying-Hilbert semigroup convergence

Uniform strong convergence on compact sets bounded away from zero extends to
nonnegative compact sets when both semigroup families are contractions and a
dense source family has a uniform linear small-time modulus.  This is the
abstract recovery/core argument at the endpoint in Mosco semigroup theorems.
-/

open Filter Set Topology

noncomputable section

namespace NCG.VaryingHilbert.System

universe u v w

variable {K : Type u} [RCLike K]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)]
  [∀ n, InnerProductSpace K (Hn n)]

/-- A dense core with a uniform linear modulus at zero upgrades convergence
on every positive-time truncation to convergence on the full nonnegative
parameter set. -/
theorem StrongOperatorConvergesUniformlyOn.of_positive_truncations_and_dense_zero_core
    (J : System (K := K) (H := H) (Hn := Hn))
    (Sn : ∀ n, ℝ → Hn n →L[K] Hn n)
    (S : ℝ → H →L[K] H) (s : Set ℝ)
    (hsNonneg : ∀ t ∈ s, 0 ≤ t)
    (hSnContraction : ∀ n t, t ∈ s → ‖Sn n t‖ ≤ 1)
    (hSContraction : ∀ t, t ∈ s → ‖S t‖ ≤ 1)
    (Core : Set H) (hCoreDense : Dense Core)
    (source : H → ∀ n, Hn n)
    (hsource : ∀ d ∈ Core, J.StronglyConverges (source d) d)
    (hstageCore : ∀ d ∈ Core, ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ n in atTop, ∀ t ∈ s,
        dist (Sn n t (source d n)) (source d n) ≤ t * C)
    (hlimitCore : ∀ d ∈ Core, ∃ C : ℝ, 0 ≤ C ∧
      ∀ t ∈ s, dist (S t d) d ≤ t * C)
    (hpositive : ∀ delta : ℝ, 0 < delta →
      J.StrongOperatorConvergesUniformlyOn Sn S (s ∩ Ici delta)) :
    J.StrongOperatorConvergesUniformlyOn Sn S s := by
  intro x xlim hx
  rw [Metric.tendstoUniformlyOn_iff]
  intro epsilon hepsilon
  let eta : ℝ := epsilon / 12
  have heta : 0 < eta := by positivity
  obtain ⟨d, hdCore, hdx⟩ :=
    hCoreDense.exists_dist_lt xlim heta
  obtain ⟨Cstage, hCstage, hstage⟩ := hstageCore d hdCore
  obtain ⟨Climit, hClimit, hlimit⟩ := hlimitCore d hdCore
  let C : ℝ := Cstage + Climit
  have hC : 0 ≤ C := add_nonneg hCstage hClimit
  let delta : ℝ := eta / (C + 1)
  have hdenom : 0 < C + 1 := by linarith
  have hdelta : 0 < delta := div_pos heta hdenom
  have hdeltaC : delta * C < eta := by
    rw [show delta = eta / (C + 1) by rfl]
    rw [div_mul_eq_mul_div, div_lt_iff₀ hdenom]
    nlinarith
  have hpositiveEvent :=
    (Metric.tendstoUniformlyOn_iff.mp
      (hpositive delta hdelta x xlim hx)) epsilon hepsilon
  have hxEvent : ∀ᶠ n in atTop,
      dist (J.embedding n (x n)) xlim < eta := by
    simpa [StronglyConverges, Metric.tendsto_atTop] using
      (Metric.tendsto_atTop.1 hx) eta heta
  have hsourceEvent : ∀ᶠ n in atTop,
      dist (J.embedding n (source d n)) d < eta := by
    simpa [StronglyConverges, Metric.tendsto_atTop] using
      (Metric.tendsto_atTop.1 (hsource d hdCore)) eta heta
  filter_upwards [hpositiveEvent, hxEvent, hsourceEvent, hstage] with
      n hnPositive hnx hnsource hnStage
  intro t ht
  by_cases htLarge : delta ≤ t
  · exact hnPositive t ⟨ht, htLarge⟩
  · have htSmall : t < delta := lt_of_not_ge htLarge
    have ht0 := hsNonneg t ht
    have hstageMove :
        dist (J.embedding n (Sn n t (source d n)))
          (J.embedding n (source d n)) ≤ t * Cstage := by
      simpa using hnStage t ht
    have hlimitMove : dist (S t d) d ≤ t * Climit :=
      hlimit t ht
    have hlimitContract :
        dist (S t xlim) (S t d) ≤ dist xlim d := by
      calc
        dist (S t xlim) (S t d) = ‖S t (xlim - d)‖ := by
          rw [dist_eq_norm, ← map_sub]
        _ ≤ ‖S t‖ * ‖xlim - d‖ := (S t).le_opNorm (xlim - d)
        _ ≤ 1 * ‖xlim - d‖ := by
          gcongr
          exact hSContraction t ht
        _ = dist xlim d := by rw [one_mul, dist_eq_norm]
    have hstageContract :
        dist (J.embedding n (Sn n t (source d n)))
          (J.embedding n (Sn n t (x n))) ≤
            dist (J.embedding n (source d n)) (J.embedding n (x n)) := by
      rw [LinearIsometry.dist_map, LinearIsometry.dist_map]
      calc
        dist (Sn n t (source d n)) (Sn n t (x n)) =
            ‖Sn n t (source d n - x n)‖ := by
              rw [dist_eq_norm, ← map_sub]
        _ ≤ ‖Sn n t‖ * ‖source d n - x n‖ :=
          (Sn n t).le_opNorm (source d n - x n)
        _ ≤ 1 * ‖source d n - x n‖ := by
          gcongr
          exact hSnContraction n t ht
        _ = dist (source d n) (x n) := by rw [one_mul, dist_eq_norm]
    have hsourceToX :
        dist (J.embedding n (source d n)) (J.embedding n (x n)) <
          eta + eta + eta := by
      have htri :
          dist (J.embedding n (source d n)) (J.embedding n (x n))
            ≤ dist (J.embedding n (source d n)) d +
                dist d xlim + dist xlim (J.embedding n (x n)) :=
        dist_triangle4 _ _ _ _
      have hdx' : dist d xlim < eta := by simpa [dist_comm] using hdx
      have hnx' : dist xlim (J.embedding n (x n)) < eta := by
        simpa [dist_comm] using hnx
      linarith
    have htime :
        t * Cstage + t * Climit < eta := by
      calc
        t * Cstage + t * Climit = t * C := by
          simp [C, mul_add]
        _ ≤ delta * C := mul_le_mul_of_nonneg_right htSmall.le hC
        _ < eta := hdeltaC
    have hchain :
        dist (S t xlim) (J.embedding n (Sn n t (x n)))
          ≤ dist (S t xlim) (S t d) +
              dist (S t d) d +
              dist d (J.embedding n (source d n)) +
              dist (J.embedding n (source d n))
                (J.embedding n (Sn n t (source d n))) +
              dist (J.embedding n (Sn n t (source d n)))
                (J.embedding n (Sn n t (x n))) := by
      calc
        dist (S t xlim) (J.embedding n (Sn n t (x n)))
            ≤ dist (S t xlim) (S t d) +
                dist (S t d) (J.embedding n (Sn n t (x n))) :=
          dist_triangle _ _ _
        _ ≤ dist (S t xlim) (S t d) +
              (dist (S t d) d +
                dist d (J.embedding n (Sn n t (x n)))) := by
          gcongr
          exact dist_triangle _ _ _
        _ ≤ dist (S t xlim) (S t d) +
              (dist (S t d) d +
                (dist d (J.embedding n (source d n)) +
                  dist (J.embedding n (source d n))
                    (J.embedding n (Sn n t (x n))))) := by
          gcongr
          exact dist_triangle _ _ _
        _ ≤ dist (S t xlim) (S t d) +
              dist (S t d) d +
              dist d (J.embedding n (source d n)) +
              (dist (J.embedding n (source d n))
                  (J.embedding n (Sn n t (source d n))) +
                dist (J.embedding n (Sn n t (source d n)))
                  (J.embedding n (Sn n t (x n)))) := by
          have hlast := dist_triangle
            (J.embedding n (source d n))
            (J.embedding n (Sn n t (source d n)))
            (J.embedding n (Sn n t (x n)))
          linarith
        _ = _ := by ring
    have hA : dist (S t xlim) (S t d) < eta :=
      hlimitContract.trans_lt hdx
    have hC : dist d (J.embedding n (source d n)) < eta := by
      simpa [dist_comm] using hnsource
    have hD :
        dist (J.embedding n (source d n))
          (J.embedding n (Sn n t (source d n))) ≤ t * Cstage := by
      simpa [dist_comm] using hstageMove
    have hE :
        dist (J.embedding n (Sn n t (source d n)))
          (J.embedding n (Sn n t (x n))) < eta + eta + eta :=
      hstageContract.trans_lt hsourceToX
    have htotal :
        dist (S t xlim) (J.embedding n (Sn n t (x n))) <
          6 * eta := by
      calc
        _ ≤ _ := hchain
        _ < 6 * eta := by nlinarith
    exact htotal.trans (by
      dsimp [eta]
      linarith)

end NCG.VaryingHilbert.System
