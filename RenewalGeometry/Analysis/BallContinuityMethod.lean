/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.BallContinuityOpen

/-!
# The continuity method for Uhlenbeck's Coulomb gauge on a ball
  (stage D3 of the ball rendering of Uhlenbeck's small-energy gauge theorem)

Generic infrastructure (no renewal notions) for `prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript.

* `coulomb_state_limit` (**closedness**) — limits of Coulomb gauge states along a convergent
  sequence of parameters, whose gauges are bounded in `H⁶(B, M_m(ℂ))`, are Coulomb gauge states
  (Rellich `rellich_MatSob`, closedness of all the defining conditions);
* `coulomb_state_zero` — the trivial connection has the trivial Coulomb state;
* `coulomb_continuity_method` (**main result**) — along a continuous path `t ↦ B_t` (`t ∈ [0,1]`) of
  tangential `𝔤`-valued connections with `B_0 = 0`, if the a-priori improvement `2κ ⇝ κ` and the
  uniform `H⁶` bound of the gauges hold for Coulomb states on `[0,1]`, then `B_1` has a Coulomb
  gauge state: the set of good parameters is non-empty, open (`coulomb_state_nhds`) and closed
  in the connected interval.
-/

open MeasureTheory Set Metric Filter Topology NormedSpace
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator

noncomputable section

namespace RenewalGeometry.BallAnalysis.BallAlg

open SobolevOpen BallReg SobAlg

set_option linter.unusedSectionVars false

variable {c : Fin 4 → ℝ} {r : ℝ} [hr : Fact (0 < r)] {m d : ℕ}

theorem isClosed_isNeumM : IsClosed {X : MatSob c r 5 m | IsNeumM X} := by
  have : {X : MatSob c r 5 m | IsNeumM X} =
      (fun X : MatSob c r 5 m => fun μ => derM (s := 4) μ X) ⁻¹' (tanM (c := c) (r := r) m) := rfl
  rw [this]
  exact isClosed_tanM.preimage (continuous_pi fun μ => (derM (s := 4) μ).continuous)

/-- Convergence in `H^s(B, M_m(ℂ))` gives a.e. convergence of the values along a subsequence. -/
theorem exists_subseq_ae_tendsto_evM {s : ℕ} [Fact (3 ≤ s)] {u : ℕ → MatSob c r s m}
    {u₀ : MatSob c r s m} (hu : Tendsto u atTop (𝓝 u₀)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ x ∂(volume.restrict (euclBall c r)),
      Tendsto (fun k => evM (u (φ k)) x) atTop (𝓝 (evM u₀ x)) := by
  have hD : Tendsto (fun k => u k - u₀) atTop (𝓝 0) := by
    simpa using hu.sub_const u₀
  have h1 := tendsto_eLpNorm_errFn hD
  have hm : ∀ k, AEStronglyMeasurable (errFn (u k - u₀)) (volume.restrict (euclBall c r)) :=
    fun k => by
      unfold errFn
      exact Finset.aestronglyMeasurable_sum _ fun i _ => Finset.aestronglyMeasurable_sum _ fun j _ =>
        (memLp_fn _).aestronglyMeasurable.norm.add (memLp_fn _).aestronglyMeasurable.norm
  obtain ⟨φ, hφ, hae⟩ := (tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num) hm
    aestronglyMeasurable_const h1).exists_seq_tendsto_ae
  refine ⟨φ, hφ, ?_⟩
  have hall : ∀ᵐ x ∂(volume.restrict (euclBall c r)), ∀ k, ∀ i j,
      ‖evM (u (φ k)) x i j - evM u₀ x i j‖ ≤ errFn (u (φ k) - u₀) x :=
    ae_all_iff.mpr fun k => ae_norm_evM_sub_le (u (φ k)) u₀
  filter_upwards [hae, hall] with x hx hk
  refine tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => ?_
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun _ => norm_nonneg _) (fun k => hk k i j) hx

/-- **Closedness**: a limit of Coulomb states with gauges bounded in `H⁶` is a Coulomb state. -/
theorem coulomb_state_limit (L : LieBasis m d) {G : Set (Matrix (Fin m) (Fin m) ℂ)}
    (hGD : GaugeGroupData L G) {κ : ℝ≥0∞} {B : ℝ → Fin 4 → MatSob c r 4 m} (hBc : Continuous B)
    {t : ℕ → ℝ} {t₀ : ℝ} (ht : Tendsto t atTop (𝓝 t₀)) {K : ℝ}
    (u : ℕ → MatSob c r 5 m) (a : ℕ → Fin 4 → Fin d → SobAlg c r 4)
    (hst : ∀ n, IsCoulombState L G κ (B (t n)) (u n) (a n))
    (hb : ∀ n, ∃ u6 : MatSob c r 6 m, rhoM u6 = u n ∧ ‖u6‖ ≤ K) :
    ∃ u₀ a₀, IsCoulombState L G κ (B t₀) u₀ a₀ := by
  choose u6 hu6 hK using hb
  obtain ⟨φ, uS, hφ, hlim⟩ := rellich_MatSob (s := 5) u6 hK
  have hlim' : Tendsto (fun n => u (φ n)) atTop (𝓝 uS) := by
    simpa [hu6] using hlim
  have htφ : Tendsto (fun n => t (φ n)) atTop (𝓝 t₀) := ht.comp hφ.tendsto_atTop
  have hBφ : Tendsto (fun n => B (t (φ n))) atTop (𝓝 (B t₀)) := (hBc.tendsto t₀).comp htφ
  have hstar : Tendsto (fun n => star (u (φ n))) atTop (𝓝 (star uS)) :=
    (continuous_star.tendsto uS).comp hlim'
  -- the gauge-transformed connections converge
  have hact : ∀ μ, Tendsto (fun n => actM (u (φ n)) (star (u (φ n))) (B (t (φ n))) μ) atTop
      (𝓝 (actM uS (star uS) (B t₀) μ)) := by
    intro μ
    unfold actM
    have hr1 := ((rhoM (c := c) (r := r) (s := 4) (m := m) : MatSob c r 5 m →+* _).toAddMonoidHom
      |> fun _ => (rhoML (c := c) (r := r) (s := 4) (m := m)).continuous.tendsto uS).comp hlim'
    have hr2 := ((rhoML (c := c) (r := r) (s := 4) (m := m)).continuous.tendsto (star uS)).comp hstar
    have hd := ((derM (c := c) (r := r) (s := 4) (m := m) μ).continuous.tendsto uS).comp hlim'
    have hBμ := ((continuous_apply μ).tendsto (B t₀)).comp hBφ
    exact ((hr1.mul hBμ).mul hr2).sub (hd.mul hr2)
  set a₀ : Fin 4 → Fin d → SobAlg c r 4 := fun μ => coordL L (actM uS (star uS) (B t₀) μ)
  have haφ : ∀ n μ, a (φ n) μ = coordL L (actM (u (φ n)) (star (u (φ n))) (B (t (φ n))) μ) :=
    fun n μ => by rw [(hst (φ n)).2.2.2.2.1 μ, coordL_embX]
  have halim : Tendsto (fun n => a (φ n)) atTop (𝓝 a₀) := by
    refine tendsto_pi_nhds.mpr fun μ => ?_
    simp only [haφ]
    exact ((coordL (c := c) (r := r) (s := 4) (m := m) L).continuous.tendsto _).comp (hact μ)
  refine ⟨uS, a₀, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- unitarity
    have h1 : Tendsto (fun n => u (φ n) * star (u (φ n))) atTop (𝓝 (uS * star uS)) :=
      hlim'.mul hstar
    have h2 : (fun n => u (φ n) * star (u (φ n))) = fun _ => 1 :=
      funext fun n => (hst (φ n)).1
    rw [h2] at h1
    exact (tendsto_nhds_unique h1 tendsto_const_nhds)
  · -- `G`-valued
    obtain ⟨ψ, hψ, hae⟩ := exists_subseq_ae_tendsto_evM hlim'
    have hG : ∀ᵐ x ∂(volume.restrict (euclBall c r)), ∀ n, evM (u (φ (ψ n))) x ∈ G :=
      ae_all_iff.mpr fun n => (hst (φ (ψ n))).2.1
    filter_upwards [hae, hG] with x hx hxG
    exact hGD.closed.mem_of_tendsto hx (Eventually.of_forall hxG)
  · -- Neumann
    exact isClosed_isNeumM.mem_of_tendsto hlim' (Eventually.of_forall fun n => (hst (φ n)).2.2.1)
  · -- tangential coefficients
    exact isClosed_TSp.mem_of_tendsto halim (Eventually.of_forall fun n => (hst (φ n)).2.2.2.1)
  · -- the coefficients describe the connection
    intro μ
    have h1 : Tendsto (fun n => embX L (a (φ n) μ)) atTop (𝓝 (embX L (a₀ μ))) :=
      ((embXL (c := c) (r := r) (s := 4) (m := m) L).continuous.tendsto _).comp
        (((continuous_apply μ).tendsto a₀).comp halim)
    have h2 : (fun n => embX L (a (φ n) μ)) =
        fun n => actM (u (φ n)) (star (u (φ n))) (B (t (φ n))) μ :=
      funext fun n => ((hst (φ n)).2.2.2.2.1 μ).symm
    rw [h2] at h1
    exact tendsto_nhds_unique (hact μ) h1
  · -- Coulomb
    have h1 : Tendsto (fun n => coulF L (a (φ n), 0)) atTop (𝓝 (coulF L (a₀, 0))) :=
      ((contDiff_coulF (c := c) (r := r) L).continuous.tendsto _).comp (halim.prodMk_nhds
        tendsto_const_nhds)
    have h2 : (fun n => coulF L (a (φ n), 0)) = fun _ => 0 :=
      funext fun n => (hst (φ n)).2.2.2.2.2.1
    rw [h2] at h1
    exact tendsto_nhds_unique h1 tendsto_const_nhds
  · -- the `L⁴` bound
    have h1 := ((continuous_coordL4 (c := c) (r := r) (d := d)).tendsto a₀).comp halim
    exact le_of_tendsto' h1 fun n => (hst (φ n)).2.2.2.2.2.2

/-- The trivial Coulomb state of the trivial connection. -/
theorem coulomb_state_zero (L : LieBasis m d) {G : Set (Matrix (Fin m) (Fin m) ℂ)}
    (hG1 : (1 : Matrix (Fin m) (Fin m) ℂ) ∈ G) (κ : ℝ≥0∞) :
    IsCoulombState L G κ (fun _ => (0 : MatSob c r 4 m)) 1 0 := by
  refine ⟨by simp, ?_, isNeumM_one, (TSp (c := c) (r := r) d).zero_mem, fun μ => ?_, ?_, ?_⟩
  · filter_upwards [evM_one (c := c) (r := r) (s := 5) (m := m)] with x hx
    rw [hx]; exact hG1
  · simp [actM, derM_one, embX_zero']
  · rw [coulF_zero]
    funext b
    simp
  · have h0 : eLpNorm (fn (0 : SobAlg c r 4)) 4 (volume.restrict (euclBall c r)) = 0 := by
      rw [eLpNorm_congr_ae fn_zero]; simp
    simp [coordL4, h0]

/-- **The continuity method.** Along a continuous path `t ↦ B_t` of tangential `𝔤`-valued
connections with `B_0 = 0`, if Coulomb states with bound `2κ` on `[0,1]` automatically have bound
`κ` (a-priori improvement) and Coulomb states with bound `κ` on `[0,1]` have gauges bounded in
`H⁶`, then `B_1` admits a Coulomb state (for `κ` below the openness threshold). -/
theorem coulomb_continuity_method (L : LieBasis m d) {G : Set (Matrix (Fin m) (Fin m) ℂ)}
    (hGD : GaugeGroupData L G) (hG1 : (1 : Matrix (Fin m) (Fin m) ℂ) ∈ G) :
    ∃ δ₁ : ℝ, 0 < δ₁ ∧ ∀ κ : ℝ≥0∞, 0 < κ → κ ≠ ⊤ → κ.toReal ≤ δ₁ →
      ∀ B : ℝ → Fin 4 → MatSob c r 4 m, Continuous B → (∀ t, B t ∈ tanM (c := c) (r := r) m) →
      (∀ t μ, ∀ᵐ x ∂(volume.restrict (euclBall c r)), evM (B t μ) x ∈ L.lieAlg) →
      B 0 = (fun _ => 0) →
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ u a, IsCoulombState L G (2 * κ) (B t) u a → coordL4 a ≤ κ) →
      (∃ K : ℝ, ∀ t ∈ Icc (0 : ℝ) 1, ∀ u a, IsCoulombState L G κ (B t) u a →
        ∃ u6 : MatSob c r 6 m, rhoM u6 = u ∧ ‖u6‖ ≤ K) →
      ∃ u a, IsCoulombState L G κ (B 1) u a := by
  obtain ⟨δ₁, hδ₁, hopen⟩ := coulomb_state_nhds (c := c) (r := r) L hGD
  refine ⟨δ₁, hδ₁, fun κ hκ0 hκt hκδ B hBc hBt hB𝔤 hB0 himp ⟨K, hK⟩ => ?_⟩
  -- the good set in the interval
  set S : Set (Icc (0 : ℝ) 1) := {t | ∃ u a, IsCoulombState L G κ (B t) u a}
  have hS0 : (⟨0, by simp⟩ : Icc (0 : ℝ) 1) ∈ S := ⟨1, 0, by
    show IsCoulombState L G κ (B 0) 1 0
    rw [hB0]; exact coulomb_state_zero L hG1 κ⟩
  have hSopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    rintro ⟨t₀, ht₀⟩ ⟨u, a, hst⟩
    have h1 := hopen κ hκ0 hκt hκδ B hBc hBt hB𝔤 t₀ u a hst
    have h2 : ∀ᶠ t : Icc (0 : ℝ) 1 in 𝓝 ⟨t₀, ht₀⟩, ∃ u' a',
        IsCoulombState L G (2 * κ) (B (t : ℝ)) u' a' :=
      (continuous_subtype_val.continuousAt (x := (⟨t₀, ht₀⟩ : Icc (0 : ℝ) 1))).eventually h1
    filter_upwards [h2] with t ⟨u', a', hst'⟩
    exact ⟨u', a', hst'.1, hst'.2.1, hst'.2.2.1, hst'.2.2.2.1, hst'.2.2.2.2.1, hst'.2.2.2.2.2.1,
      himp t t.2 u' a' hst'⟩
  have hSclosed : IsClosed S := by
    refine IsSeqClosed.isClosed fun {tn} {t₀} htn hlim => ?_
    choose u a hst using htn
    exact coulomb_state_limit L hGD hBc ((continuous_subtype_val.tendsto t₀).comp hlim) u a hst
      fun n => hK (tn n) (tn n).2 (u n) (a n) (hst n)
  have : ConnectedSpace (Icc (0 : ℝ) 1) :=
    isConnected_iff_connectedSpace.mp (isConnected_Icc (by norm_num))
  have hSu : S = univ := (isClopen_iff.mp ⟨hSclosed, hSopen⟩).resolve_left
    (Set.nonempty_iff_ne_empty.mp ⟨_, hS0⟩)
  have h1 : (⟨1, by simp⟩ : Icc (0 : ℝ) 1) ∈ S := by rw [hSu]; exact mem_univ _
  exact h1

end RenewalGeometry.BallAnalysis.BallAlg
