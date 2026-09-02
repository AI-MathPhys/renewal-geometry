/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.MoscoRecoveryEnergyConvergence
import NCG.Grand.MoscoResolventStrongConvergence

/-!
# Strong resolvent convergence from finite ENNReal Mosco forms

This bridges the manuscript's extended nonnegative Mosco definition to the real-valued
variational resolvent theorem.  Finiteness and the automatic minimizer energy bound justify
passing `ENNReal.toReal` through the relevant liminf.
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

/-- Mosco convergence of the extended forms after every cofinal reindexing. -/
def CofinalMoscoConverges
    (q : (n : ℕ) → Hn n → ℝ≥0∞) (qlim : H → ℝ≥0∞) : Prop :=
  ∀ (φ : ℕ → ℕ), Tendsto φ atTop atTop →
    (J.reindex φ).MoscoConverges (fun n ↦ q (φ n)) qlim

/-- Cofinal Mosco convergence remains cofinal after any cofinal reindexing. -/
theorem CofinalMoscoConverges.reindex
    {q : (n : ℕ) → Hn n → ℝ≥0∞} {qlim : H → ℝ≥0∞}
    (hmosco : J.CofinalMoscoConverges q qlim)
    (φ : ℕ → ℕ) (hφ : Tendsto φ atTop atTop) :
    (J.reindex φ).CofinalMoscoConverges (fun n ↦ q (φ n)) qlim := by
  intro ψ hψ
  simpa only [System.reindex, Function.comp_def] using
    hmosco (φ ∘ ψ) (hφ.comp hψ)

/-- A bounded ENNReal liminf inequality descends through `toReal`. -/
theorem toReal_le_liminf_toReal_of_bounded
    {u : ℕ → ℝ≥0∞} {a b : ℝ≥0∞}
    (hb : b ≠ ∞) (hu : ∀ n, u n ≤ b)
    (h : a ≤ liminf u atTop) :
    a.toReal ≤ liminf (fun n ↦ (u n).toReal) atTop := by
  have hliminfLe : liminf u atTop ≤ b := by
    apply liminf_le_of_le ⟨0, by simp⟩
    intro y hy
    obtain ⟨n, hn⟩ := hy.exists
    exact hn.trans (hu n)
  have hliminfNe : liminf u atTop ≠ ∞ :=
    ne_top_of_le_ne_top hb hliminfLe
  calc
    a.toReal ≤ (liminf u atTop).toReal := ENNReal.toReal_mono hliminfNe h
    _ = liminf (fun n ↦ (u n).toReal) atTop :=
      (ENNReal.liminf_toReal_eq hb (Eventually.of_forall hu)).symm

/-- Cofinal Mosco convergence of finite ENNReal forms implies strong convergence of the
associated resolvents. -/
theorem strongOperatorConverges_resolvents_of_cofinalMosco
    (q : (n : ℕ) → Hn n → ℝ≥0∞) (qlim : H → ℝ≥0∞)
    (hmosco : J.CofinalMoscoConverges q qlim)
    (hqFinite : ∀ n (z : Hn n), q n z ≠ ∞)
    (hqlimFinite : ∀ z : H, qlim z ≠ ∞)
    (lam : ℝ) (hlam : 0 < lam)
    (Tn : ∀ n, Hn n →L[K] Hn n) (T : H →L[K] H)
    (hqconvex : ∀ n, ConvexOn ℝ univ (fun z ↦ (q n z).toReal))
    (hq0 : ∀ n, q n 0 = 0)
    (hstageMin : ∀ n (f z : Hn n),
      resolventObjective (K := K) (fun w ↦ (q n w).toReal) lam f (Tn n f) ≤
        resolventObjective (K := K) (fun w ↦ (q n w).toReal) lam f z)
    (hlimitUnique : ∀ (f y : H),
      resolventObjective (K := K) (fun w ↦ (qlim w).toReal) lam f y ≤
        resolventObjective (K := K) (fun w ↦ (qlim w).toReal) lam f (T f) →
          y = T f) :
    J.StrongOperatorConverges J Tn T := by
  intro f flim hf
  obtain ⟨recovery, hrecoveryStrong, hrecoveryEnergyENN⟩ :=
    (hmosco id tendsto_id).exists_recovery_energy_tendsto (T flim)
  have hrecoveryEnergy : Tendsto
      (fun n ↦ (q (id n) (recovery n)).toReal) atTop
      (𝓝 ((qlim (T flim)).toReal)) := by
    simpa only [Function.comp_def] using
      (ENNReal.tendsto_toReal (hqlimFinite (T flim))).comp hrecoveryEnergyENN
  obtain ⟨F, hF, hfBound⟩ := hf.exists_pos_uniform_norm_bound J
  let C : ℝ := 2 * F / lam
  have hxBound : ∀ n, ‖Tn n (f n)‖ ≤ C :=
    uniformlyBounded_resolventMinimizers
      (fun n z ↦ (q n z).toReal) lam hlam f (fun n ↦ Tn n (f n)) F hfBound
      (fun n ↦ by simp [hq0 n]) (fun n ↦ ENNReal.toReal_nonneg)
      (fun n ↦ hstageMin n (f n) 0)
  have hqUpper : ∀ n, (q n (Tn n (f n))).toReal ≤ 2 * C * F :=
    uniformlyBoundedAbove_resolventMinimizerEnergies
      (fun n z ↦ (q n z).toReal) lam hlam.le f (fun n ↦ Tn n (f n)) C F
      (by dsimp [C]; positivity) hxBound hfBound
      (fun n ↦ by simp [hq0 n]) (fun n ↦ hstageMin n (f n) 0)
  apply resolventMinimizers_stronglyConverge_of_formLiminf J
    (fun n z ↦ (q n z).toReal) (fun z ↦ (qlim z).toReal)
    lam hlam f (fun n ↦ Tn n (f n)) recovery flim (T flim)
    hqconvex (fun n ↦ by simp [hq0 n]) (fun n ↦ ENNReal.toReal_nonneg)
    hf (fun n z ↦ hstageMin n (f n) z) hrecoveryStrong hrecoveryEnergy
  · intro ns hns ψ hψ y hweak
    let φ := ns ∘ ψ
    have hENN : qlim y ≤
        liminf (fun k ↦ q (φ k) (Tn (φ k) (f (φ k)))) atTop :=
      (hmosco φ (hns.comp hψ.tendsto_atTop)).liminf_le
        (fun k ↦ Tn (φ k) (f (φ k))) y hweak
    apply toReal_le_liminf_toReal_of_bounded
      (b := ENNReal.ofReal (2 * C * F)) ENNReal.ofReal_ne_top
    · intro k
      rw [← ENNReal.ofReal_toReal
        (hqFinite (ns (ψ k)) (Tn (ns (ψ k)) (f (ns (ψ k)))))]
      exact ENNReal.ofReal_le_ofReal (hqUpper (ns (ψ k)))
    · exact hENN
  · exact hlimitUnique flim

/-- The finite ENNReal forward implication assuming only the variational minimizer
characterizations; positive strong convexity derives limit uniqueness. -/
theorem strongOperatorConverges_resolvents_of_cofinalMosco_minimizers
    [InnerProductSpace ℝ H] [IsScalarTower ℝ K H]
    (q : (n : ℕ) → Hn n → ℝ≥0∞) (qlim : H → ℝ≥0∞)
    (hmosco : J.CofinalMoscoConverges q qlim)
    (hqFinite : ∀ n (z : Hn n), q n z ≠ ∞)
    (hqlimFinite : ∀ z : H, qlim z ≠ ∞)
    (lam : ℝ) (hlam : 0 < lam)
    (Tn : ∀ n, Hn n →L[K] Hn n) (T : H →L[K] H)
    (hqconvex : ∀ n, ConvexOn ℝ univ (fun z ↦ (q n z).toReal))
    (hqlimConvex : ConvexOn ℝ univ (fun z ↦ (qlim z).toReal))
    (hq0 : ∀ n, q n 0 = 0)
    (hstageMin : ∀ n (f z : Hn n),
      resolventObjective (K := K) (fun w ↦ (q n w).toReal) lam f (Tn n f) ≤
        resolventObjective (K := K) (fun w ↦ (q n w).toReal) lam f z)
    (hlimitMin : ∀ (f z : H),
      resolventObjective (K := K) (fun w ↦ (qlim w).toReal) lam f (T f) ≤
        resolventObjective (K := K) (fun w ↦ (qlim w).toReal) lam f z) :
    J.StrongOperatorConverges J Tn T := by
  apply strongOperatorConverges_resolvents_of_cofinalMosco J
    q qlim hmosco hqFinite hqlimFinite lam hlam Tn T
      hqconvex hq0 hstageMin
  intro f y hy
  exact resolventObjective_unique_minimizer
    (fun w ↦ (qlim w).toReal) hqlimConvex lam hlam
      f (T f) (hlimitMin f) y hy

end NCG.VaryingHilbert.System
