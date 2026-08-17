/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteENNRealMoscoRecovery
import NCG.Grand.VariationalConvergenceFromClusterUniqueness
import NCG.Grand.ResolventMinimizerWeakPrecompactness
import NCG.Grand.ResolventObjectiveLiminf
import NCG.Grand.VaryingHilbertStrongBoundedness
import NCG.Grand.ENNRealMoscoResolventConvergence

/-!
# Strong resolvent convergence for extended ENNReal forms

This is the domain-aware forward Mosco theorem.  It requires finiteness only at the actual
resolvent minimizers and at finite-energy competitors.  In particular, the forms may take the
value `∞` away from their effective domains.
-/

open scoped ENNReal

open Filter Topology Set

noncomputable section

namespace NCG.VaryingHilbert.System

universe u v w

variable {K : Type u} [RCLike K]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H]
  [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace K (Hn n)]
  [∀ n, InnerProductSpace ℝ (Hn n)] [∀ n, IsScalarTower ℝ K (Hn n)]
variable (J : System (K := K) (H := H) (Hn := Hn))

/-- Cofinal Mosco convergence of genuinely extended forms implies strong convergence of their
resolvents, provided finite-domain minimality and its coercive gap are available. -/
theorem strongOperatorConverges_resolvents_of_extendedCofinalMosco
    (q : (n : ℕ) → Hn n → ℝ≥0∞) (qlim : H → ℝ≥0∞)
    (hmosco : J.CofinalMoscoConverges q qlim)
    (lam : ℝ) (hlam : 0 < lam)
    (Tn : ∀ n, Hn n →L[K] Hn n) (T : H →L[K] H)
    (hq0 : ∀ n, q n 0 = 0)
    (hstageFinite : ∀ n (f : Hn n), q n (Tn n f) ≠ ∞)
    (hlimitFinite : ∀ f : H, qlim (T f) ≠ ∞)
    (hstageMin : ∀ n (f z : Hn n), q n z ≠ ∞ →
      resolventObjective (K := K) (fun w ↦ (q n w).toReal) lam f (Tn n f) ≤
        resolventObjective (K := K) (fun w ↦ (q n w).toReal) lam f z)
    (hlimitUnique : ∀ (f y : H), qlim y ≠ ∞ →
      resolventObjective (K := K) (fun w ↦ (qlim w).toReal) lam f y ≤
        resolventObjective (K := K) (fun w ↦ (qlim w).toReal) lam f (T f) →
          y = T f)
    (c : ℝ) (hc : 0 < c)
    (hstageGap : ∀ n (f z : Hn n), q n z ≠ ∞ →
      c * ‖Tn n f - z‖ ^ 2 ≤
        resolventObjective (K := K) (fun w ↦ (q n w).toReal) lam f z -
          resolventObjective (K := K) (fun w ↦ (q n w).toReal) lam f (Tn n f)) :
    J.StrongOperatorConverges J Tn T := by
  intro f flim hf
  let x : ∀ n, Hn n := fun n ↦ Tn n (f n)
  let xlim : H := T flim
  obtain ⟨recovery, hrecoveryStrong, hrecoveryEnergyENN, hrecoveryFinite⟩ :=
    (hmosco id tendsto_id).exists_finite_recovery_energy_tendsto hq0
      xlim (hlimitFinite flim)
  have hrecoveryEnergy : Tendsto
      (fun n ↦ (q n (recovery n)).toReal) atTop
      (𝓝 ((qlim xlim).toReal)) := by
    simpa using (ENNReal.tendsto_toReal (hlimitFinite flim)).comp hrecoveryEnergyENN
  have hrecoveryValue := resolventObjective_tendsto_of_recovery J
    (fun n z ↦ (q n z).toReal) (fun z ↦ (qlim z).toReal) lam
      f recovery flim xlim hrecoveryStrong hf hrecoveryEnergy
  obtain ⟨F, hF, hfBound⟩ := hf.exists_pos_uniform_norm_bound J
  let C : ℝ := 2 * F / lam
  have hxNonneg : ∀ n, 0 ≤ (q n (x n)).toReal :=
    fun n ↦ ENNReal.toReal_nonneg
  have hminZero : ∀ n,
      resolventObjective (K := K) (fun w ↦ (q n w).toReal) lam (f n) (x n) ≤
        resolventObjective (K := K) (fun w ↦ (q n w).toReal) lam (f n) 0 := by
    intro n
    exact hstageMin n (f n) 0 (by simp [hq0 n])
  have hxBound : ∀ n, ‖x n‖ ≤ C :=
    uniformlyBounded_resolventMinimizers
      (fun n z ↦ (q n z).toReal) lam hlam f x F hfBound
      (fun n ↦ by simp [hq0 n]) hxNonneg hminZero
  let Q : ℝ := 2 * C * F
  have hqUpper : ∀ n, (q n (x n)).toReal ≤ Q :=
    uniformlyBoundedAbove_resolventMinimizerEnergies
      (fun n z ↦ (q n z).toReal) lam hlam.le f x C F
      (by dsimp [C]; positivity) hxBound hfBound
      (fun n ↦ by simp [hq0 n]) hminZero
  have hcompact : J.IsSequentiallyWeaklyPrecompact x :=
    resolventMinimizers_isSequentiallyWeaklyPrecompact J
      (fun n z ↦ (q n z).toReal) lam hlam f x F hfBound
      (fun n ↦ by simp [hq0 n]) hxNonneg hminZero
  have hbelow : ∀ n, -(F ^ 2) / lam ≤
      resolventObjective (K := K) (fun w ↦ (q n w).toReal) lam (f n) (x n) :=
    uniformlyBoundedBelow_resolventObjectives
      (fun n z ↦ (q n z).toReal) lam hlam f x F hF.le hfBound hxNonneg
  have hclusterFinite : ∀ (ns : ℕ → ℕ), Tendsto ns atTop atTop →
      ∀ (ψ : ℕ → ℕ), StrictMono ψ → ∀ y : H,
      (J.reindex (ns ∘ ψ)).WeaklyConverges (fun k ↦ x (ns (ψ k))) y →
        qlim y ≠ ∞ := by
    intro ns hns ψ hψ y hweak
    let φ := ns ∘ ψ
    have hENN : qlim y ≤ liminf (fun k ↦ q (φ k) (x (φ k))) atTop :=
      (hmosco φ (hns.comp hψ.tendsto_atTop)).liminf_le
        (fun k ↦ x (φ k)) y hweak
    have hliminfUpper : liminf (fun k ↦ q (φ k) (x (φ k))) atTop ≤
        ENNReal.ofReal Q := by
      apply liminf_le_of_le ⟨0, by simp⟩
      intro b hb
      obtain ⟨k, hk⟩ := hb.exists
      refine hk.trans ?_
      rw [← ENNReal.ofReal_toReal (hstageFinite (φ k) (f (φ k)))]
      exact ENNReal.ofReal_le_ofReal (hqUpper (φ k))
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hENN.trans hliminfUpper)
  have hclusterLower : ∀ (ns : ℕ → ℕ), Tendsto ns atTop atTop →
      ∀ (ψ : ℕ → ℕ), StrictMono ψ → ∀ y : H,
      (J.reindex (ns ∘ ψ)).WeaklyConverges (fun k ↦ x (ns (ψ k))) y →
        resolventObjective (K := K) (fun z ↦ (qlim z).toReal) lam flim y ≤
          liminf (fun k ↦ resolventObjective (K := K)
            (fun z ↦ (q (ns (ψ k)) z).toReal) lam
              (f (ns (ψ k))) (x (ns (ψ k)))) atTop := by
    intro ns hns ψ hψ y hweak
    let φ := ns ∘ ψ
    have hENN : qlim y ≤ liminf (fun k ↦ q (φ k) (x (φ k))) atTop :=
      (hmosco φ (hns.comp hψ.tendsto_atTop)).liminf_le
        (fun k ↦ x (φ k)) y hweak
    have hform : (qlim y).toReal ≤
        liminf (fun k ↦ (q (φ k) (x (φ k))).toReal) atTop := by
      apply toReal_le_liminf_toReal_of_bounded
        (b := ENNReal.ofReal Q) ENNReal.ofReal_ne_top
      · intro k
        rw [← ENNReal.ofReal_toReal (hstageFinite (φ k) (f (φ k)))]
        exact ENNReal.ofReal_le_ofReal (hqUpper (φ k))
      · exact hENN
    apply resolventObjective_le_liminf (J.reindex φ)
      (fun k z ↦ (q (φ k) z).toReal) (fun z ↦ (qlim z).toReal)
      lam hlam (fun k ↦ f (φ k)) (fun k ↦ x (φ k)) flim y C F Q hweak
    · exact hf.reindex J (hns.comp hψ.tendsto_atTop)
    · exact fun k ↦ hxBound (φ k)
    · exact fun k ↦ hfBound (φ k)
    · exact fun k ↦ hxNonneg (φ k)
    · exact fun k ↦ hqUpper (φ k)
    · exact hform
  have hminRecovery : ∀ n,
      resolventObjective (K := K) (fun w ↦ (q n w).toReal) lam (f n) (x n) ≤
        resolventObjective (K := K) (fun w ↦ (q n w).toReal) lam
          (f n) (recovery n) :=
    fun n ↦ hstageMin n (f n) (recovery n) (hrecoveryFinite n)
  have hclusterUnique : ∀ (ns : ℕ → ℕ), Tendsto ns atTop atTop →
      ∀ (ψ : ℕ → ℕ), StrictMono ψ → ∀ y : H,
      (J.reindex (ns ∘ ψ)).WeaklyConverges (fun k ↦ x (ns (ψ k))) y →
        y = xlim := by
    intro ns hns ψ hψ y hweak
    apply hlimitUnique flim y (hclusterFinite ns hns ψ hψ y hweak)
    have hrecoverySub := hrecoveryValue.comp (hns.comp hψ.tendsto_atTop)
    have hboundedBelow : IsBoundedUnder (· ≥ ·) atTop
        (fun k ↦ resolventObjective (K := K)
          (fun z ↦ (q (ns (ψ k)) z).toReal) lam
            (f (ns (ψ k))) (x (ns (ψ k)))) :=
      isBoundedUnder_of ⟨-(F ^ 2) / lam, fun k ↦ hbelow (ns (ψ k))⟩
    have hliminfUpper : liminf (fun k ↦ resolventObjective (K := K)
          (fun z ↦ (q (ns (ψ k)) z).toReal) lam
            (f (ns (ψ k))) (x (ns (ψ k)))) atTop ≤
        resolventObjective (K := K) (fun z ↦ (qlim z).toReal) lam flim xlim := by
      apply liminf_le_of_le hboundedBelow
      intro b hb
      apply ge_of_tendsto hrecoverySub
      filter_upwards [hb] with k hk
      exact hk.trans (hminRecovery (ns (ψ k)))
    exact (hclusterLower ns hns ψ hψ y hweak).trans hliminfUpper
  apply stronglyConverges_of_variational_minimizers_of_coercive_gap_of_clusterUnique J
    (fun n z ↦ resolventObjective (K := K) (fun w ↦ (q n w).toReal) lam (f n) z)
    (resolventObjective (K := K) (fun w ↦ (qlim w).toReal) lam flim)
    x recovery xlim hcompact hminRecovery hrecoveryStrong hrecoveryValue
      (-(F ^ 2) / lam) hbelow hclusterLower hclusterUnique c hc
  exact fun n ↦ hstageGap n (f n) (recovery n) (hrecoveryFinite n)

end NCG.VaryingHilbert.System
