/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.BallSobolevSup
import RenewalGeometry.Analysis.BallMatSobRellich

/-!
# Coulomb gauge states along a path of connections: openness
  (stage D3 of the ball rendering of Uhlenbeck's small-energy gauge theorem)

Generic infrastructure (no renewal notions) for `prop:critical-uhlenbeck` of the
Einstein–Standard-Model action-closure manuscript.

* `GaugeGroupData L G` — the structure-group hypotheses: a skew-Hermitian basis `L` of the Lie
  algebra `𝔤 = span L.e`, `G` closed and multiplicative, `exp 𝔤 ⊆ G`, `Ad(G) 𝔤 ⊆ 𝔤`;
* `IsCoulombState L G κ B u a` — `u ∈ H⁵(B, M_m(ℂ))` is a unitary, `G`-valued, Neumann gauge and
  `u·B = Σ a^b e_b` is a tangential Coulomb connection with coefficient `L⁴` norm `≤ κ`;
* `coordL_mem_TSp`, `actM_mem_tanM`, `continuous_gaugeAct` — tangentiality of coordinates and of
  gauge transforms, continuity of the IFT gauge action;
* `coulomb_state_nhds` (**openness**): there is `δ₁ > 0` such that for `0 < κ < ∞`,
  `κ ≤ δ₁`, along a continuous path `t ↦ B_t` of tangential `𝔤`-valued connections, a Coulomb state
  at `t₀` (bound `κ`) produces Coulomb states at all `t` near `t₀` (bound `2κ`): implicit
  function theorem `coulomb_openness` at the coefficients of `u·B_t`, composition law
  `actM_comp`.
-/

open MeasureTheory Set Metric Filter Topology NormedSpace
open scoped ENNReal NNReal ContDiff Matrix.Norms.Operator

noncomputable section

namespace RenewalGeometry.BallAnalysis.BallAlg

open SobolevOpen BallReg SobAlg

set_option linter.unusedSectionVars false

variable {c : Fin 4 → ℝ} {r : ℝ} [hr : Fact (0 < r)] {m d : ℕ}

/-- **Structure-group data**: a skew-Hermitian real basis `L` of the Lie algebra
`𝔤 = span_ℝ L.e`, a closed multiplicative set `G` with `exp 𝔤 ⊆ G` and `Ad(G) 𝔤 ⊆ 𝔤`. -/
structure GaugeGroupData (L : LieBasis m d) (G : Set (Matrix (Fin m) (Fin m) ℂ)) : Prop where
  skew : ∀ b, star (L.e b) = -L.e b
  closed : IsClosed G
  mul_mem : ∀ g ∈ G, ∀ h ∈ G, g * h ∈ G
  exp_mem : ∀ X ∈ L.lieAlg, exp X ∈ G
  ad_mem : ∀ g ∈ G, ∀ X ∈ L.lieAlg, g * X * star g ∈ L.lieAlg

/-- **Coulomb gauge states**: `u` is a unitary `G`-valued Neumann gauge in `H⁵(B, M_m(ℂ))` and
`u·B = Σ_b a^b e_b` is tangential, Coulomb, with coefficient `L⁴` norm at most `κ`. -/
def IsCoulombState (L : LieBasis m d) (G : Set (Matrix (Fin m) (Fin m) ℂ)) (κ : ℝ≥0∞)
    (B : Fin 4 → MatSob c r 4 m) (u : MatSob c r 5 m) (a : Fin 4 → Fin d → SobAlg c r 4) :
    Prop :=
  u * star u = 1 ∧ (∀ᵐ x ∂(volume.restrict (euclBall c r)), evM u x ∈ G) ∧ IsNeumM u ∧
    a ∈ TSp (c := c) (r := r) d ∧ (∀ μ, actM u (star u) B μ = embX L (a μ)) ∧
    coulF L (a, 0) = 0 ∧ coordL4 a ≤ κ

/-! ### Helper lemmas -/

/-- Coordinates of a tangential matrix connection are tangential. -/
theorem coordL_mem_TSp (L : LieBasis m d) {X : Fin 4 → MatSob c r 4 m}
    (hX : X ∈ tanM (c := c) (r := r) m) :
    (fun μ => coordL L (X μ)) ∈ TSp (c := c) (r := r) d := by
  intro b
  rw [mem_tanM] at hX
  have e : (fun μ => coordL L (X μ) b) = ∑ i, ∑ j, (L.α b i j • (fun μ => (X μ i j).re) +
      L.β b i j • fun μ => (X μ i j).im) := by
    funext μ
    simp [coordL_apply, Finset.sum_apply]
  show (fun μ => coordL L (X μ) b) ∈ tanSub (c := c) (r := r)
  rw [e]
  exact Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ =>
    Submodule.add_mem _ (Submodule.smul_mem _ _ (hX i j).1) (Submodule.smul_mem _ _ (hX i j).2)

/-- Gauge transforms of tangential connections by Neumann gauges are tangential. -/
theorem actM_mem_tanM {u v : MatSob c r 5 m} (hu : IsNeumM u) {B : Fin 4 → MatSob c r 4 m}
    (hB : B ∈ tanM (c := c) (r := r) m) :
    (fun μ => actM u v B μ) ∈ tanM (c := c) (r := r) m := by
  unfold actM
  exact (tanM (c := c) (r := r) m).sub_mem
    (tanM_mul_right (tanM_mul_left hB _) _) (tanM_mul_right hu _)

theorem actM_sub_actM (u v : MatSob c r 5 m) (B B' : Fin 4 → MatSob c r 4 m) (μ : Fin 4) :
    actM u v B μ - actM u v B' μ = rhoM u * (B μ - B' μ) * rhoM v := by
  simp only [actM]; noncomm_ring

theorem continuous_actM (u v : MatSob c r 5 m) (μ : Fin 4) :
    Continuous fun B : Fin 4 → MatSob c r 4 m => actM u v B μ := by
  unfold actM
  exact ((continuous_const.mul (continuous_apply μ)).mul continuous_const).sub continuous_const

theorem continuous_exp_matSob {s : ℕ} [Fact (3 ≤ s)] :
    Continuous (exp : MatSob c r s m → MatSob c r s m) :=
  continuous_iff_continuousAt.mpr fun M => (analyticAt_exp_matSob M).continuousAt

theorem continuous_gaugeAct (L : LieBasis m d) (μ : Fin 4) :
    Continuous fun p : (Fin 4 → Fin d → SobAlg c r 4) × (Fin d → SobAlg c r 5) =>
      gaugeAct L p.1 p.2 μ := by
  unfold gaugeAct
  have hE : Continuous fun p : (Fin 4 → Fin d → SobAlg c r 4) × (Fin d → SobAlg c r 5) =>
      exp (embX L p.2) :=
    continuous_exp_matSob.comp ((embXL (c := c) (r := r) (s := 5) (m := m) L).continuous.comp
      continuous_snd)
  have hE' : Continuous fun p : (Fin 4 → Fin d → SobAlg c r 4) × (Fin d → SobAlg c r 5) =>
      exp (-embX L p.2) :=
    continuous_exp_matSob.comp ((embXL (c := c) (r := r) (s := 5) (m := m) L).continuous.comp
      continuous_snd).neg
  have hA : Continuous fun p : (Fin 4 → Fin d → SobAlg c r 4) × (Fin d → SobAlg c r 5) =>
      embX L (p.1 μ) :=
    (embXL (c := c) (r := r) (s := 4) (m := m) L).continuous.comp
      ((continuous_apply μ).comp continuous_fst)
  have hR := (rhoML (c := c) (r := r) (s := 4) (m := m)).continuous
  have hD := (derM (c := c) (r := r) (s := 4) (m := m) μ).continuous
  exact ((hR.comp hE).mul hA |>.mul (hR.comp hE')).sub ((hD.comp hE).mul (hR.comp hE'))

/-- The `𝔤`-valuedness of a gauge transform of a `𝔤`-valued connection, from that of another. -/
theorem ae_actM_mem (L : LieBasis m d) {G : Set (Matrix (Fin m) (Fin m) ℂ)}
    (hGD : GaugeGroupData L G) {u : MatSob c r 5 m}
    (huG : ∀ᵐ x ∂(volume.restrict (euclBall c r)), evM u x ∈ G)
    {B B' : Fin 4 → MatSob c r 4 m}
    (hB : ∀ μ, ∀ᵐ x ∂(volume.restrict (euclBall c r)), evM (B μ) x ∈ L.lieAlg)
    (hB' : ∀ μ, ∀ᵐ x ∂(volume.restrict (euclBall c r)), evM (B' μ) x ∈ L.lieAlg)
    (h0 : ∀ μ, ∀ᵐ x ∂(volume.restrict (euclBall c r)), evM (actM u (star u) B' μ) x ∈ L.lieAlg)
    (μ : Fin 4) :
    ∀ᵐ x ∂(volume.restrict (euclBall c r)), evM (actM u (star u) B μ) x ∈ L.lieAlg := by
  have e := actM_sub_actM u (star u) B B' μ
  have e2 : actM u (star u) B μ = actM u (star u) B' μ + rhoM u * (B μ - B' μ) * rhoM (star u) := by
    rw [← e]; abel
  rw [e2]
  filter_upwards [evM_add (actM u (star u) B' μ) (rhoM u * (B μ - B' μ) * rhoM (star u)),
    evM_mul (rhoM u * (B μ - B' μ)) (rhoM (star u)), evM_mul (rhoM u) (B μ - B' μ),
    evM_sub (B μ) (B' μ), evM_star u, h0 μ, hB μ, hB' μ, huG] with x h1 h2 h3 h4 h5 h6 h7 h8 h9
  have key : evM (actM u (star u) B' μ + rhoM u * (B μ - B' μ) * rhoM (star u)) x =
      evM (actM u (star u) B' μ) x + evM u x * (evM (B μ) x - evM (B' μ) x) * star (evM u x) := by
    rw [h1, h2, h3, h4, ← h5]
    exact congrArg₂ (· + ·) rfl (congrArg₂ (· * ·) (congrArg₂ (· * ·)
      (congrFun (evM_rhoM (s := 4) u) x) rfl) (congrFun (evM_rhoM (s := 4) (star u)) x))
  rw [key]
  exact L.lieAlg.add_mem h6 (hGD.ad_mem _ h9 _ (L.lieAlg.sub_mem h7 h8))

/-! ### Openness -/

/-- **Openness of Coulomb gauge states along a path** (implicit function theorem). -/
theorem coulomb_state_nhds (L : LieBasis m d) {G : Set (Matrix (Fin m) (Fin m) ℂ)}
    (hGD : GaugeGroupData L G) :
    ∃ δ₁ : ℝ, 0 < δ₁ ∧ ∀ κ : ℝ≥0∞, 0 < κ → κ ≠ ⊤ → κ.toReal ≤ δ₁ →
      ∀ B : ℝ → Fin 4 → MatSob c r 4 m, Continuous B → (∀ t, B t ∈ tanM (c := c) (r := r) m) →
      (∀ t μ, ∀ᵐ x ∂(volume.restrict (euclBall c r)), evM (B t μ) x ∈ L.lieAlg) →
      ∀ t₀ u a, IsCoulombState L G κ (B t₀) u a →
      ∀ᶠ t in 𝓝 t₀, ∃ u' a', IsCoulombState L G (2 * κ) (B t) u' a' := by
  obtain ⟨δ₁, hδ₁, hop⟩ := coulomb_openness (c := c) (r := r) L
  refine ⟨δ₁, hδ₁, fun κ hκ0 hκt hκδ B hBc hBt hB𝔤 t₀ u a hst => ?_⟩
  obtain ⟨huu, huG, huN, ha, hact, hcoul, hκa⟩ := hst
  -- the transported path
  set X : ℝ → Fin 4 → MatSob c r 4 m := fun t μ => actM u (star u) (B t) μ
  have hX0 : ∀ μ, ∀ᵐ x ∂(volume.restrict (euclBall c r)), evM (X t₀ μ) x ∈ L.lieAlg := by
    intro μ
    show ∀ᵐ x ∂(volume.restrict (euclBall c r)), evM (actM u (star u) (B t₀) μ) x ∈ L.lieAlg
    rw [hact μ]; exact evM_embX_mem L _
  have hX𝔤 : ∀ t μ, ∀ᵐ x ∂(volume.restrict (euclBall c r)), evM (X t μ) x ∈ L.lieAlg :=
    fun t μ => ae_actM_mem L hGD huG (hB𝔤 t) (hB𝔤 t₀) hX0 μ
  set at' : ℝ → Fin 4 → Fin d → SobAlg c r 4 := fun t μ => coordL L (X t μ)
  have hat_emb : ∀ t μ, embX L (at' t μ) = X t μ := fun t μ => embX_coordL_of_ae_mem L (hX𝔤 t μ)
  have hat_T : ∀ t, at' t ∈ TSp (c := c) (r := r) d := fun t =>
    coordL_mem_TSp L (actM_mem_tanM huN (hBt t))
  have hat0 : at' t₀ = a := by
    funext μ
    show coordL L (actM u (star u) (B t₀) μ) = a μ
    rw [hact μ, coordL_embX]
  have hatc : Continuous at' := by
    refine continuous_pi fun μ => ?_
    exact (coordL (c := c) (r := r) (s := 4) (m := m) L).continuous.comp
      ((continuous_actM u (star u) μ).comp hBc)
  -- the implicit function theorem at `a`
  have hfinκ : ∀ ν b, eLpNorm (fn (a ν b)) 4 (volume.restrict (euclBall c r)) ≠ ⊤ := by
    intro ν b
    refine ne_top_of_le_ne_top hκt (le_trans ?_ hκa)
    exact (Finset.single_le_sum (f := fun b' => eLpNorm (fn (a ν b')) 4
        (volume.restrict (euclBall c r))) (fun _ _ => zero_le) (Finset.mem_univ b)).trans
      (Finset.single_le_sum (f := fun ν' => ∑ b', eLpNorm (fn (a ν' b')) 4
        (volume.restrict (euclBall c r))) (fun _ _ => zero_le) (Finset.mem_univ ν))
  have hsum : ∑ ν, ∑ b, (eLpNorm (fn (a ν b)) 4 (volume.restrict (euclBall c r))).toReal ≤ δ₁ := by
    have e : ∑ ν, ∑ b, (eLpNorm (fn (a ν b)) 4 (volume.restrict (euclBall c r))).toReal =
        (coordL4 a).toReal := by
      unfold coordL4
      rw [ENNReal.toReal_sum fun ν _ => ENNReal.sum_ne_top.mpr fun b _ => hfinκ ν b]
      exact Finset.sum_congr rfl fun ν _ => (ENNReal.toReal_sum fun b _ => hfinκ ν b).symm
    rw [e]
    exact (ENNReal.toReal_mono hκt hκa).trans hκδ
  obtain ⟨ψ, hψ0, hψc, hψ⟩ := hop ⟨a, ha⟩ hcoul hsum
  set atT : ℝ → TSp (c := c) (r := r) d := fun t => ⟨at' t, hat_T t⟩
  have hatTc : Continuous atT := continuous_induced_rng.mpr hatc
  have hatT0 : atT t₀ = ⟨a, ha⟩ := Subtype.ext hat0
  have hev1 : ∀ᶠ t in 𝓝 t₀, coulIFT L (atT t, ψ (atT t)) = 0 := by
    have := hatTc.continuousAt (x := t₀)
    rw [ContinuousAt, hatT0] at this
    exact this.eventually hψ
  -- the new coordinates
  set ξ : ℝ → Fin d → SobAlg c r 5 := fun t => ((ψ (atT t) : XSp (c := c) (r := r) d) :
    Fin d → SobAlg c r 5)
  set a' : ℝ → Fin 4 → Fin d → SobAlg c r 4 := fun t μ => coordL L (gaugeAct L (at' t) (ξ t) μ)
  have hξc : ContinuousAt ξ t₀ := by
    have h1 : ContinuousAt (fun t => ψ (atT t)) t₀ := by
      refine ContinuousAt.comp (g := ψ) ?_ hatTc.continuousAt
      rw [hatT0]; exact hψc
    exact continuous_subtype_val.continuousAt.comp h1
  have ha'c : ContinuousAt a' t₀ := by
    refine continuousAt_pi.mpr fun μ => ?_
    have hp : ContinuousAt (fun t => (at' t, ξ t)) t₀ := hatc.continuousAt.prodMk hξc
    have hc2 : ContinuousAt (fun t => gaugeAct L (at' t) (ξ t) μ) t₀ :=
      ContinuousAt.comp (f := fun t => (at' t, ξ t))
        (g := fun p : (Fin 4 → Fin d → SobAlg c r 4) × (Fin d → SobAlg c r 5) =>
          gaugeAct L p.1 p.2 μ) (continuous_gaugeAct L μ).continuousAt hp
    exact ContinuousAt.comp (f := fun t => gaugeAct L (at' t) (ξ t) μ) (g := coordL L)
      (coordL (c := c) (r := r) (s := 4) (m := m) L).continuous.continuousAt hc2
  have ha'0 : a' t₀ = a := by
    funext μ
    have hξ0 : ξ t₀ = 0 := by
      show ((ψ (atT t₀) : XSp (c := c) (r := r) d) : Fin d → SobAlg c r 5) = 0
      rw [hatT0, hψ0]; rfl
    show coordL L (gaugeAct L (at' t₀) (ξ t₀) μ) = a μ
    rw [hξ0, gaugeAct_zero, coordL_embX, hat0]
  have hev2 : ∀ᶠ t in 𝓝 t₀, coordL4 (a' t) ≤ 2 * κ := by
    have h1 : Tendsto (fun t => coordL4 (a' t)) (𝓝 t₀) (𝓝 (coordL4 a)) := by
      have := (continuous_coordL4 (c := c) (r := r) (d := d)).continuousAt.tendsto.comp ha'c
      rwa [ha'0] at this
    have h2 : coordL4 a < 2 * κ := by
      refine lt_of_le_of_lt hκa ?_
      calc κ = 1 * κ := (one_mul κ).symm
        _ < 2 * κ := ENNReal.mul_lt_mul_left hκ0.ne' hκt (by norm_num)
    exact (h1.eventually (gt_mem_nhds h2)).mono fun t ht => ht.le
  filter_upwards [hev1, hev2] with t h1 h2
  set e := exp (embX L (ξ t))
  have he : e * star e = 1 := exp_embX_mul_star L hGD.skew (ξ t)
  have hse : star e = exp (-embX L (ξ t)) := star_exp_embX L hGD.skew (ξ t)
  have hXN : (ξ t) ∈ XSp (c := c) (r := r) d := (ψ (atT t)).2
  refine ⟨e * u, a' t, ?_, ?_, ?_, ?_, ?_, ?_, h2⟩
  · rw [star_mul, show e * u * (star u * star e) = e * (u * star u) * star e by noncomm_ring, huu,
      mul_one, he]
  · filter_upwards [evM_mul e u, huG, evM_exp_mem (hexp := hGD.exp_mem) (evM_embX_mem L (ξ t))]
      with x h1 h2 h3
    rw [h1]; exact hGD.mul_mem _ h3 _ h2
  · exact IsNeumM.mul (isNeumM_exp (isNeumM_embX L hXN)) huN
  · exact coordL_mem_TSp L (gaugeAct_mem_tanM L (hat_T t) hXN)
  · intro μ
    have h3 : actM (e * u) (star (e * u)) (B t) μ = gaugeAct L (at' t) (ξ t) μ := by
      rw [star_mul, actM_comp huu, hse, gaugeAct_eq_actM]
      congr 1
      funext κ'
      exact (hat_emb t κ').symm
    rw [h3]
    exact (embX_coordL_of_ae_mem L (ae_gaugeAct_mem L (at' t) (ξ t) μ)).symm
  · have h3 : ∀ μ, embX L (a' t μ) = gaugeAct L (at' t) (ξ t) μ := fun μ =>
      embX_coordL_of_ae_mem L (ae_gaugeAct_mem L (at' t) (ξ t) μ)
    have h4 := coulF_eq_zero_of_coulIFT L h1
    unfold coulF at h4 ⊢
    simp only [gaugeAct_zero, h3]
    exact h4

end RenewalGeometry.BallAnalysis.BallAlg
