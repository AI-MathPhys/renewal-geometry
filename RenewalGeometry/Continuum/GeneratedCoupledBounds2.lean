/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.GeneratedCoupledBounds

/-!
# Zero-order bounds for the coupled constraint system: the wave and Dirac rows

Einstein–Standard-Model action-closure manuscript, `lem:generated-physical-identification`,
coupled spinors.  On a period cell where the complete stress of `z` is conserved:

* **`ctrl_boxc`** — the wave operator `g^{αβ}∂_α∂_βc_ν` of the lowered harmonic defect is
  controlled by `𝒰 = (c, ∂c, Y, P, Ȳ, P̄)` (the coupled subsidiary equation with the controlled
  divergence of the auxiliary Dirac stress);
* `dirac_coord` — `N ε_0c_0Σ_aε_ac_ae_a(f) = ∂_tf + Σ_j𝒜^j∂_jf` (the frame Dirac operator in the
  coordinates of the symmetric system).
-/

open Filter Topology Set Finset
open scoped ContDiff

noncomputable section

namespace RenewalGeometry.GenCplBd

open SobolevOpen (pd)
open PeriodicCube SlabWaveHk FrameCurvature HarmonicDefect ActualJetWriter ActualJetFrame
  ActualJetSystem ActualJetSmooth ActualJetGauge SpinorProlongation TwistedHalfRicci
  ActualJetBridge ActualJetCompleteForcing ActualJetRecon ActualJetState SymHypEnergy GenSFJ
  GenCplCov GenCplN GenCplRows GenCplX GenCplP GenCplCont GenCtrl GenCplE

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable {S₀ : Type*} [NormedAddCommGroup S₀] [NormedSpace ℝ S₀] [FiniteDimensional ℝ S₀]

variable {SM : SMData (MatLie m) V S S'} {W : ST 3 → StateP m V S S'} {z : Tuple m V S S'}
  {a b : ℝ}

/-! ### The wave row -/

/-- **The wave operator on the harmonic defect is controlled** wherever the complete stress of
`z` is conserved. -/
theorem ctrl_boxc (hC : GenDStress.CoupledDirac SM) (hW : ContDiff ℝ ∞ W)
    (h : CplSol SM W z a b) {t₀ t₁ : ℝ} (ha : a < t₀) (hb : t₁ < b)
    (hdivT : ∀ x ∈ cube t₀ t₁, ∀ ν, GenStress.divT SM z x ν = 0) (i : Fin 4) :
    Ctrl (UF SM W z) (cube t₀ t₁) (fun x => GenCplBox.boxc z x i) := by
  obtain ⟨Mb, -, hMb⟩ := bdd_cube (GenHarmonic.continuous_coefSize z) t₀ t₁
  set M := max Mb 1 with hMdef
  have hM1 : 1 ≤ M := le_max_right _ _
  have hMx : ∀ x ∈ cube t₀ t₁, GenHarmonic.coefSize z x ≤ M := fun x hx => by
    have := hMb x hx
    rw [Real.norm_eq_abs, abs_of_pos (lt_of_lt_of_le one_pos (GenHarmonic.one_le_coefSize z x))]
      at this
    exact this.trans (le_max_left _ _)
  obtain ⟨Kd, hKd0, hKd⟩ := ctrl_divS hC hW h ha hb i
  refine ⟨2 * |SM.κ| * Kd + 1000 * M ^ 3 * 5, by positivity, fun x hx => ?_⟩
  have hxo : x ∈ openSlab a b := cube_subset_openSlab ha hb hx
  have e1 : GenCplBox.boxc z x i =
      ∑ e, ∑ a', (GenHarmonic.jet3 z x).G e a' * (GenHarmonic.jet3 z x).ddgc e a' i := by
    unfold GenCplBox.boxc
    refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun β _ => ?_
    rw [GenHarmonic.pd_pd_cF z x β μ]
    rfl
  have hMxx := hMx x hx
  have hX : ‖GenHarmonic.cF z x‖ ≤ ‖UF SM W z x‖ := by
    have := norm_fst_le (UF SM W z x); exact this
  have hY : ∑ γ, ‖pd (GenHarmonic.cF z) γ x‖ ≤ 4 * ‖UF SM W z x‖ := by
    have : ∀ γ, ‖pd (GenHarmonic.cF z) γ x‖ ≤ ‖UF SM W z x‖ := fun γ =>
      (norm_le_pi_norm (fun γ => pd (GenHarmonic.cF z) γ x) γ).trans
        ((norm_fst_le (UF SM W z x).2).trans (norm_snd_le (UF SM W z x)))
    calc ∑ γ, ‖pd (GenHarmonic.cF z) γ x‖ ≤ ∑ _γ : Fin 4, ‖UF SM W z x‖ :=
          Finset.sum_le_sum fun γ _ => this γ
      _ = 4 * ‖UF SM W z x‖ := by simp
  have hpr := GenHarmonic.principal_le (GenHarmonic.jet3 z x) (GenHarmonic.jet3 z x).gc
    (GenHarmonic.jet3 z x).dgc (GenHarmonic.jet3 z x).ddgc hM1
    (fun i j => (GenHarmonic.le_coefSize_gi z x i j).trans hMxx)
    (fun a' l s => by
      rw [GenHarmonic.jet3_chr]; exact (GenHarmonic.le_coefSize_chr z x l a' s).trans hMxx)
    (fun b' a' l s => by
      rw [GenHarmonic.jet3_dchr]; exact (GenHarmonic.le_coefSize_dchr z x b' l a' s).trans hMxx)
    (fun i j => by
      rw [GenHarmonic.jet3_ricM]; exact (GenHarmonic.le_coefSize_ricci z x i j).trans hMxx)
    (norm_nonneg (GenHarmonic.cF z x))
    (Finset.sum_nonneg fun γ _ => norm_nonneg (pd (GenHarmonic.cF z) γ x))
    (fun l => by
      rw [show (GenHarmonic.jet3 z x).gc l = GenHarmonic.cF z x l from
        (congrFun (GenHarmonic.cF_eq z x) l).symm]
      exact (Real.norm_eq_abs _).symm.le.trans (norm_le_pi_norm _ l))
    (fun e l => by
      have h1 : (GenHarmonic.jet3 z x).dgc e l = pd (GenHarmonic.cF z) e x l := by
        rw [GenHarmonic.pd_cF z x e]
      rw [h1]
      refine ((Real.norm_eq_abs _).symm.le.trans (norm_le_pi_norm _ l)).trans ?_
      exact Finset.single_le_sum (f := fun γ => ‖pd (GenHarmonic.cF z) γ x‖)
        (fun _ _ => norm_nonneg _) (Finset.mem_univ e)) i
  have hsub := GenCplSub.coupled_subsidiary hC hW h hxo i
  rw [hsub, hdivT x hx i, mul_zero, zero_add] at hpr
  show ‖GenCplBox.boxc z x i‖ ≤ _
  rw [e1, Real.norm_eq_abs]
  have hd : |ContractedBianchiJet.SubsidiarySource.divS (GenHarmonic.jet3 z x)
      (Matrix.of (GenCplSD.ΔSf hC W z x))
      (fun e => Matrix.of fun a' b' => pd (fun y => GenCplSD.ΔSf hC W z y a' b') e x) i| ≤
      Kd * ‖UF SM W z x‖ := by
    have := hKd x hx
    rw [Real.norm_eq_abs] at this
    exact this
  have hU0 := norm_nonneg (UF SM W z x)
  have hM0 : 0 ≤ 1000 * M ^ 3 := by positivity
  set dv := ContractedBianchiJet.SubsidiarySource.divS (GenHarmonic.jet3 z x)
      (Matrix.of (GenCplSD.ΔSf hC W z x))
      (fun e => Matrix.of fun a' b' => pd (fun y => GenCplSD.ΔSf hC W z y a' b') e x) i
    with hdv
  set XY := ‖GenHarmonic.cF z x‖ + ∑ γ, ‖pd (GenHarmonic.cF z) γ x‖ with hXY
  have hXY5 : XY ≤ 5 * ‖UF SM W z x‖ := by rw [hXY]; linarith
  have e2 : |-2 * (SM.κ * dv)| = 2 * |SM.κ| * |dv| := by
    rw [abs_mul, abs_mul, abs_neg, abs_two]; ring
  have h1 : 2 * |SM.κ| * |dv| ≤ 2 * |SM.κ| * (Kd * ‖UF SM W z x‖) :=
    mul_le_mul_of_nonneg_left hd (by positivity)
  have h2 : 1000 * M ^ 3 * XY ≤ 1000 * M ^ 3 * (5 * ‖UF SM W z x‖) :=
    mul_le_mul_of_nonneg_left hXY5 hM0
  rw [e2] at hpr
  calc _ ≤ 2 * |SM.κ| * |dv| + 1000 * M ^ 3 * XY := hpr
    _ ≤ 2 * |SM.κ| * (Kd * ‖UF SM W z x‖) + 1000 * M ^ 3 * (5 * ‖UF SM W z x‖) := by linarith
    _ = (2 * |SM.κ| * Kd + 1000 * M ^ 3 * 5) * ‖UF SM W z x‖ := by ring

/-! ### The frame Dirac operator in the coordinates of the symmetric system -/

/-- **`Nε_0c_0Σ_aε_ac_ae_a(f) = ∂_tf + Σ_j𝒜^j∂_jf`** for the Dirac principal operators
`𝒜^j = -βʲ - Ne_iʲc_0c_i`. -/
theorem dirac_coord (D : DiracData (MatLie m) V S₀) (AF : AdaptedFrame) (v : Fin 4 → S₀) :
    AF.N • (D.Fr.ε 0 • D.Fr.c 0 (∑ a', D.Fr.ε a' • D.Fr.c a' (fD AF v a'))) =
      v 0 + ∑ j : Fin 3, diracP AF D.Fr j (v j.succ) := by
  have hε0 : D.Fr.ε 0 = -1 := D.lorentz.1
  have hεi : ∀ i : Fin 3, D.Fr.ε i.succ = 1 := D.lorentz.2
  have hfd : ∀ i : Fin 3, fD AF v i.succ = ∑ j : Fin 3, AF.E i j • v j.succ := by
    intro i
    unfold fD
    rw [Fin.sum_univ_succ]
    simp only [AdaptedFrame.fr_succ_zero, zero_smul, zero_add, AdaptedFrame.fr_succ_succ]
  have h0 := N_fD_zero AF v
  rw [Fin.sum_univ_succ, hε0]
  simp only [hεi, one_smul, hfd, neg_smul, map_add, map_neg, map_sum, map_smul, c0c0, neg_neg,
    smul_add, smul_neg, h0]
  unfold diracP
  simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib, Module.End.smul_def,
    Module.End.mul_apply, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm (f := fun i j => (AF.N * AF.E i j) • D.Fr.c 0 (D.Fr.c i.succ (v j.succ)))]
  abel

/-! ### Coefficient continuity for the normal prolongation row -/

theorem pc_γF (D : DiracData (MatLie m) V S₀) (ν : Fin 4) : PC fun y => GenCplBox.γF z D y ν := by
  unfold GenCplBox.γF
  refine PC.sum _ fun A _ => PC.smul ?_ (PC.const _)
  exact continuous_const.mul (GenCplP.contDiff_fr (z := z) A ν).continuous

theorem continuous_N : Continuous fun y => (frameU (z.gi y)).N := by
  have e : (fun y => (frameU (z.gi y)).N) = fun y => ((frameU (z.gi y)).fr 0 0)⁻¹ := by
    funext y; rw [AdaptedFrame.fr_zero_zero, inv_inv]
  rw [e]
  exact (GenCplP.contDiff_fr (z := z) 0 0).continuous.inv₀ fun y => by
    rw [AdaptedFrame.fr_zero_zero]; exact inv_ne_zero (frameU (z.gi y)).N_pos.ne'

theorem pd_mul_real {f g : ST 3 → ℝ} {x : ST 3} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (i : Fin 4) :
    pd (fun y => f y * g y) i x = pd f i x * g x + f x * pd g i x := by
  unfold SobolevOpen.pd
  rw [fderiv_fun_mul hf hg]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem pd_add_real {f g : ST 3 → ℝ} {x : ST 3} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) (i : Fin 4) :
    pd (fun y => f y + g y) i x = pd f i x + pd g i x := by
  unfold SobolevOpen.pd
  rw [fderiv_fun_add hf hg]
  rfl

theorem pd_neg_sum_real {f : Fin 4 → ST 3 → ℝ} {x : ST 3} (hf : ∀ l, DifferentiableAt ℝ (f l) x)
    (i : Fin 4) : pd (fun y => -∑ l, f l y) i x = -∑ l, pd (f l) i x := by
  unfold SobolevOpen.pd
  rw [fderiv_fun_neg, fderiv_fun_sum fun l _ => hf l]
  simp

/-- `∂_α` of the Christoffel part of `∇_{(μ}c_{ν)}`. -/
theorem pd_sD1 (x : ST 3) (μ ν α : Fin 4) :
    pd (fun y => GenCplBox.sD1 z y μ ν) α x =
      -∑ l, (pd (fun y => chr (z.gi y) (z.dg y) l μ ν) α x * GenHarmonic.cF z x l +
        chr (z.gi x) (z.dg x) l μ ν * pd (GenHarmonic.cF z) α x l) := by
  have hc := GenHarmonic.contDiff_cF z
  have hcl : ∀ l, ContDiff ℝ ∞ (fun y => GenHarmonic.cF z y l) := fun l => contDiff_pi.1 hc l
  unfold GenCplBox.sD1
  rw [pd_neg_sum_real (fun l => ((z.contDiff_chr l μ ν).mul (hcl l)).differentiable (by simp) x)]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [pd_mul_real ((z.contDiff_chr l μ ν).differentiable (by simp) x)
    ((hcl l).differentiable (by simp) x), pd_apply (hc.differentiable (by simp) x)]

theorem ctrl_pd_sD1 {t₀ t₁ : ℝ} (μ ν α : Fin 4) :
    Ctrl (UF SM W z) (cube t₀ t₁) (fun x => pd (fun y => GenCplBox.sD1 z y μ ν) α x) := by
  refine Ctrl.congr ?_ fun x _ => pd_sD1 x μ ν α
  refine (Ctrl.sum _ fun l _ => (ctrl_real_mul ?_ (ctrl_cF_apply l)).add
    (ctrl_real_mul ?_ (ctrl_dcF_apply α l))).neg
  · exact bdd_of_continuous (contDiff_pd (z.contDiff_chr l μ ν) α).continuous t₀ t₁
  · exact bdd_of_continuous (z.contDiff_chr l μ ν).continuous t₀ t₁

theorem pd_sD_split (x : ST 3) (μ ν α : Fin 4) :
    pd (fun y => GenCplCov.sD z y μ ν) α x = pd (fun y => GenCplBox.sD2 z y μ ν) α x +
      pd (fun y => GenCplBox.sD1 z y μ ν) α x := by
  have hc := GenHarmonic.contDiff_cF z
  have h2 : ContDiff ℝ ∞ (fun y => GenCplBox.sD2 z y μ ν) := by
    unfold GenCplBox.sD2
    exact contDiff_const.mul ((contDiff_pi.1 (contDiff_pd hc μ) ν).add
      (contDiff_pi.1 (contDiff_pd hc ν) μ))
  have h1 : ContDiff ℝ ∞ (fun y => GenCplBox.sD1 z y μ ν) := by
    unfold GenCplBox.sD1
    exact (ContDiff.sum fun l _ => (z.contDiff_chr l μ ν).mul (contDiff_pi.1 hc l)).neg
  have e : (fun y => GenCplCov.sD z y μ ν) = fun y => GenCplBox.sD2 z y μ ν +
      GenCplBox.sD1 z y μ ν := funext fun y => GenCplBox.sD_split z y μ ν
  rw [e, pd_add_real (h2.differentiable (by simp) x) (h1.differentiable (by simp) x)]

/-! ### The normal prolongation row -/

/-- `κ𝒟'` of the mass part of the forcing, controlled. -/
theorem ctrl_kD_mass (D : DiracData (MatLie m) V S₀) {Y : ST 3 → Fin 4 → S₀} (hY : ContDiff ℝ ∞ Y)
    {t₀ t₁ : ℝ} (hYc : Ctrl (UF SM W z) (cube t₀ t₁) Y)
    (hQ : ∀ B, Ctrl (UF SM W z) (cube t₀ t₁) (fun y => QF z D Y y B)) :
    Ctrl (UF SM W z) (cube t₀ t₁)
      (fun x => GenCplBox.kD z D (fun y => fun A => mass D.m0 D.L (z.H y) (Y y A)) x) := by
  refine Ctrl.congr ?_ fun x _ => GenCplBox.kD_mass z D hY x
  refine (ctrl_mass D t₀ t₁ (Ctrl.lin (kap D.Fr) (Ctrl.pi (F' := fun _ => S₀) hQ))).add
    (Ctrl.sum _ fun A _ => Ctrl.sum _ fun a' _ => Ctrl.smul
      (bdd_of_continuous continuous_const t₀ t₁) (Ctrl.lin (D.Fr.c A) (Ctrl.lin (D.Fr.c a')
        ((Ctrl.bilin D.L (bdd_fd z.H_smooth a' t₀ t₁) (Ctrl.apply (F' := fun _ => S₀) hYc A)).add
          ((Ctrl.endo (T := fun y v => ωF z D y a' v) (endBdd_of_pc (pc_ωF z D a') t₀ t₁)
            (ctrl_mass D t₀ t₁ (Ctrl.apply (F' := fun _ => S₀) hYc A))).sub
          (ctrl_mass D t₀ t₁ (Ctrl.endo (T := fun y v => ωF z D y a' v)
            (endBdd_of_pc (pc_ωF z D a') t₀ t₁) (Ctrl.apply (F' := fun _ => S₀) hYc A))))))))

theorem bdd_γ (D : DiracData (MatLie m) V S₀) {f : ST 3 → S₀} (hf : Continuous f) (ν : Fin 4)
    (t₀ t₁ : ℝ) : Bdd (fun y => GenCplBox.γF z D y ν (f y)) (cube t₀ t₁) :=
  bdd_of_continuous ((pc_γF D ν).apply hf) t₀ t₁

theorem continuous_γ (D : DiracData (MatLie m) V S₀) {f : ST 3 → S₀} (hf : Continuous f)
    (ν : Fin 4) : Continuous (fun y => GenCplBox.γF z D y ν (f y)) := (pc_γF D ν).apply hf

theorem ctrl_Ξ (D : DiracData (MatLie m) V S₀) {T : ST 3 → Fin 4 → Fin 4 → ℝ} {ψ : ST 3 → S₀}
    (hψ : Continuous ψ) {t₀ t₁ : ℝ} (hT : ∀ μ ν, Ctrl (UF SM W z) (cube t₀ t₁) (fun y => T y μ ν))
    (μ : Fin 4) : Ctrl (UF SM W z) (cube t₀ t₁) (fun y => GenCplBox.Ξ z D T ψ μ y) := by
  unfold GenCplBox.Ξ
  exact Ctrl.smul (bdd_of_continuous continuous_const t₀ t₁)
    (Ctrl.sum _ fun ν _ => Ctrl.smul_vec (hT μ ν) (bdd_γ D hψ ν t₀ t₁))

/-- The remainder `remR` of `κ𝒟'(ricTerm(T)Ψ)` is controlled by `T`. -/
theorem ctrl_remR (D : DiracData (MatLie m) V S₀) {T : ST 3 → Fin 4 → Fin 4 → ℝ} {ψ : ST 3 → S₀}
    (hψ : ContDiff ℝ ∞ ψ) {t₀ t₁ : ℝ}
    (hT : ∀ μ ν, Ctrl (UF SM W z) (cube t₀ t₁) (fun y => T y μ ν)) :
    Ctrl (UF SM W z) (cube t₀ t₁) (fun x => GenCplBox.remR z D T ψ x) := by
  have hVric : ∀ A, Ctrl (UF SM W z) (cube t₀ t₁) (fun y => GenCplBox.Vric z D T ψ y A) :=
    fun A => ctrl_ricTerm D hψ.continuous t₀ t₁ hT A
  unfold GenCplBox.remR
  refine Ctrl.add (Ctrl.smul (bdd_of_continuous continuous_const t₀ t₁)
    (Ctrl.sum _ fun μ _ => Ctrl.sum _ fun α _ => Ctrl.sum _ fun ν _ => Ctrl.smul_vec (hT μ ν) ?_))
    (Ctrl.sum _ fun A _ => Ctrl.sum _ fun a' _ => Ctrl.smul
      (bdd_of_continuous continuous_const t₀ t₁) (Ctrl.lin (D.Fr.c A) (Ctrl.lin (D.Fr.c a')
        ((Ctrl.sum _ fun μ _ => Ctrl.smul (bdd_fd (GenCplP.contDiff_fr (z := z) A μ) a' t₀ t₁)
          (ctrl_Ξ D hψ.continuous hT μ)).add
          ((Ctrl.endo (T := fun y v => ωF z D y a' v) (endBdd_of_pc (pc_ωF z D a') t₀ t₁)
            (hVric A)).sub (Ctrl.sum _ fun C _ => Ctrl.smul
              (bdd_of_continuous (GenCplN.contDiff_ΓF z a' A C).continuous t₀ t₁) (hVric C)))))))
  have hp : Continuous fun y => pd (fun y' => GenCplBox.γF z D y' ν (ψ y')) α y :=
    (contDiff_pd (GenCplBox.contDiff_γψ z D hψ ν) α).continuous
  exact bdd_of_continuous (continuous_γ D (continuous_γ D hp α) μ) t₀ t₁

/-- **`κ𝒟'` of the forcing `R = 𝓜Y - ricTerm(∇_{(μ}c_{ν)})Ψ` is controlled** (the second
derivatives of `c` enter only through `□c`). -/
theorem ctrl_kD_R (D : DiracData (MatLie m) V S₀) {ψ : ST 3 → S₀} (hψ : ContDiff ℝ ∞ ψ)
    {Y : ST 3 → Fin 4 → S₀} (hY : ContDiff ℝ ∞ Y) {t₀ t₁ : ℝ}
    (hYc : Ctrl (UF SM W z) (cube t₀ t₁) Y)
    (hQ : ∀ B, Ctrl (UF SM W z) (cube t₀ t₁) (fun y => QF z D Y y B))
    (hbox : ∀ i, Ctrl (UF SM W z) (cube t₀ t₁) (fun x => GenCplBox.boxc z x i)) :
    Ctrl (UF SM W z) (cube t₀ t₁)
      (fun x => GenCplBox.kD z D (fun y A => GenCplCov.RF z D ψ Y y A) x) := by
  have hsD := fun μ ν => GenCplP.contDiff_sD (z := z) μ ν
  have hM : ContDiff ℝ ∞ (fun y => fun A => mass D.m0 D.L (z.H y) (Y y A)) :=
    GenCplBox.contDiff_massY z D hY
  have hV : ContDiff ℝ ∞ (GenCplBox.Vric z D (GenCplCov.sD z) ψ) :=
    GenCplBox.contDiff_Vric z D hψ hsD
  have eR : (fun y A => GenCplCov.RF z D ψ Y y A) =
      fun y => (fun A => mass D.m0 D.L (z.H y) (Y y A)) - GenCplBox.Vric z D (GenCplCov.sD z) ψ y :=
    rfl
  have hsplit : ∀ x, GenCplBox.kD z D (fun y A => GenCplCov.RF z D ψ Y y A) x =
      GenCplBox.kD z D (fun y => fun A => mass D.m0 D.L (z.H y) (Y y A)) x -
        ((1 / 2 : ℝ) • (-∑ ν, GenCplBox.boxc z x ν • GenCplBox.γF z D x ν (ψ x) +
          ∑ μ, ∑ α, ∑ ν, pd (fun y => GenCplBox.sD1 z y μ ν) α x •
            GenCplBox.γF z D x μ (GenCplBox.γF z D x α (GenCplBox.γF z D x ν (ψ x)))) +
          GenCplBox.remR z D (GenCplCov.sD z) ψ x) := by
    intro x
    rw [eR, GenCplBox.kD_sub z D (hM.differentiable (by simp) x) (hV.differentiable (by simp) x),
      GenCplBox.kD_ric z D hψ hsD x]
    congr 2
    rw [← GenCplBox.principal_sD2 z D x (ψ x)]
    simp only [pd_sD_split, add_smul, Finset.sum_add_distrib]
  refine Ctrl.congr ?_ fun x _ => hsplit x
  refine (ctrl_kD_mass D hY hYc hQ).sub (Ctrl.add (Ctrl.smul
    (bdd_of_continuous continuous_const t₀ t₁) (Ctrl.add (Ctrl.neg (Ctrl.sum _ fun ν _ =>
      Ctrl.smul_vec (hbox ν) (bdd_γ D hψ.continuous ν t₀ t₁))) (Ctrl.sum _ fun μ _ =>
        Ctrl.sum _ fun α _ => Ctrl.sum _ fun ν _ => Ctrl.smul_vec (ctrl_pd_sD1 μ ν α) ?_)))
    (ctrl_remR D hψ (ctrl_sD t₀ t₁)))
  exact bdd_of_continuous (continuous_γ D (continuous_γ D (continuous_γ D hψ.continuous ν) α) μ)
    t₀ t₁

/-- **The normal prolongation row is controlled** (generic form): if the prolongation defect `P`
of a one-form field `Y` obeys the twisted Dirac identity (`GenCplP.P_dirac`), then
`∂_tP + Σ_j𝒜^j∂_jP` is controlled by `𝒰`. -/
theorem ctrl_Prow_gen (D : DiracData (MatLie m) V S₀) {ψ : ST 3 → S₀} (hψ : ContDiff ℝ ∞ ψ)
    {Y : ST 3 → Fin 4 → S₀} (hY : ContDiff ℝ ∞ Y) {P : ST 3 → S₀} {t₀ t₁ : ℝ}
    (hYc : Ctrl (UF SM W z) (cube t₀ t₁) Y)
    (hQ : ∀ B, Ctrl (UF SM W z) (cube t₀ t₁) (fun y => QF z D Y y B))
    (hPc : Ctrl (UF SM W z) (cube t₀ t₁) P)
    (hbox : ∀ i, Ctrl (UF SM W z) (cube t₀ t₁) (fun x => GenCplBox.boxc z x i))
    (heq : ∀ x ∈ cube t₀ t₁, D.Fr.ε 0 • D.Fr.c 0 (∑ a', D.Fr.ε a' • D.Fr.c a' (fd z P a' x +
        ωF z D x a' (P x))) =
      (1 / 2 : ℝ) • ∑ a', ∑ b', (D.Fr.ε a' * D.Fr.ε b') • kap D.Fr
        (((liftFr D.Fr).c a' * (liftFr D.Fr).c b') • (curv (lcΛ D.Fr.ε (Jx z D x).G)
          (omegaP (ωF z D x) (ΓF z x)) (dωP z D x) a' b' • Y x)) -
      kap D.Fr (∑ a', (liftFr D.Fr).ε a' • ((liftFr D.Fr).c a' •
        (fd z (fun y A => GenCplCov.RF z D ψ Y y A) a' x +
          omegaP (ωF z D x) (ΓF z x) a' (fun A => GenCplCov.RF z D ψ Y x A)))) +
      ∑ A, ∑ a', (D.Fr.ε A * D.Fr.ε a' * ΓF z x a' A 0) • D.Fr.c A (D.Fr.c a' (P x))) :
    Ctrl (UF SM W z) (cube t₀ t₁) (fun x => pd P 0 x +
      ∑ j : Fin 3, diracP (frameU (z.gi x)) D.Fr j (pd P j.succ x)) := by
  have hrow : ∀ x ∈ cube t₀ t₁, pd P 0 x + ∑ j : Fin 3, diracP (frameU (z.gi x)) D.Fr j
      (pd P j.succ x) = (frameU (z.gi x)).N • (((1 / 2 : ℝ) • ∑ a', ∑ b',
        (D.Fr.ε a' * D.Fr.ε b') • kap D.Fr
        (((liftFr D.Fr).c a' * (liftFr D.Fr).c b') • (curv (lcΛ D.Fr.ε (Jx z D x).G)
          (omegaP (ωF z D x) (ΓF z x)) (dωP z D x) a' b' • Y x)) -
      GenCplBox.kD z D (fun y A => GenCplCov.RF z D ψ Y y A) x +
      ∑ A, ∑ a', (D.Fr.ε A * D.Fr.ε a' * ΓF z x a' A 0) • D.Fr.c A (D.Fr.c a' (P x))) -
      D.Fr.ε 0 • D.Fr.c 0 (∑ a', D.Fr.ε a' • D.Fr.c a' (ωF z D x a' (P x)))) := by
    intro x hx
    rw [← dirac_coord D (frameU (z.gi x)) (fun μ => pd P μ x)]
    congr 1
    have h := heq x hx
    unfold GenCplBox.kD
    rw [← h]
    simp only [map_add, Finset.sum_add_distrib, smul_add]
    show D.Fr.ε 0 • D.Fr.c 0 (∑ a', D.Fr.ε a' • D.Fr.c a' (fd z P a' x)) = _
    abel
  refine Ctrl.congr ?_ hrow
  refine Ctrl.smul (bdd_of_continuous continuous_N t₀ t₁) (Ctrl.sub (Ctrl.add (Ctrl.sub ?_ ?_) ?_)
    ?_)
  · refine Ctrl.smul (bdd_of_continuous continuous_const t₀ t₁) (Ctrl.sum _ fun a' _ =>
      Ctrl.sum _ fun b' _ => Ctrl.smul (bdd_of_continuous continuous_const t₀ t₁) ?_)
    refine Ctrl.lin (kap D.Fr) ((Ctrl.lin ((liftFr D.Fr).c a' * (liftFr D.Fr).c b')
      (Ctrl.endo (T := fun y v => curv (lcΛ D.Fr.ε (Jx z D y).G) (omegaP (ωF z D y) (ΓF z y))
        (dωP z D y) a' b' v) (endBdd_of_pc (pc_curv z D a' b') t₀ t₁) hYc)).congr fun y _ => rfl)
  · exact ctrl_kD_R D hψ hY hYc hQ hbox
  · refine Ctrl.sum _ fun A _ => Ctrl.sum _ fun a' _ => Ctrl.smul ?_
      (Ctrl.lin (D.Fr.c A) (Ctrl.lin (D.Fr.c a') hPc))
    exact bdd_of_continuous (continuous_const.mul (GenCplN.contDiff_ΓF z a' A 0).continuous) t₀ t₁
  · exact Ctrl.smul (bdd_of_continuous continuous_const t₀ t₁) (Ctrl.lin (D.Fr.c 0)
      (Ctrl.sum _ fun a' _ => Ctrl.smul (bdd_of_continuous continuous_const t₀ t₁)
        (Ctrl.lin (D.Fr.c a') (Ctrl.endo (T := fun y v => ωF z D y a' v)
          (endBdd_of_pc (pc_ωF z D a') t₀ t₁) hPc))))

/-! ### The tangential spinor defect rows -/

/-- **The forcing of the tangential spinor defect rows is controlled** (generic form). -/
theorem ctrl_Yrow_gen (D : DiracData (MatLie m) V S₀) {ψ : ST 3 → S₀} (hψ : Continuous ψ)
    {Y : ST 3 → Fin 4 → S₀} {t₀ t₁ : ℝ} (hYc : Ctrl (UF SM W z) (cube t₀ t₁) Y) (a' : Fin 4) :
    Ctrl (UF SM W z) (cube t₀ t₁) (fun x => (frameU (z.gi x)).N • (XrowFX D (z.g x) (z.gi x)
      (z.dg x) (frameU (z.gi x)) (z.de x) (z.A x) (z.H x) (Y x) a' + D.Fr.c 0 • ricTerm D (z.g x)
      (z.gi x) (frameU (z.gi x)) (fun μ ν => symDefect (z.g x) (z.gi x) (z.dg x) (z.ddg x) μ ν)
      (ψ x) a')) := by
  have hY := fun A => Ctrl.apply (F' := fun _ => S₀) hYc A
  have hΓ : ∀ B A C, Bdd (fun y => ΓF z y B A C) (cube t₀ t₁) := fun B A C =>
    bdd_of_continuous (GenCplN.contDiff_ΓF z B A C).continuous t₀ t₁
  refine Ctrl.smul (bdd_of_continuous continuous_N t₀ t₁) (Ctrl.add ?_ ?_)
  · unfold XrowFX
    refine Ctrl.sub (Ctrl.add (Ctrl.add (Ctrl.neg ?_) ?_) ?_) ?_
    · exact Ctrl.endo (T := fun y v => ωF z D y 0 v) (endBdd_of_pc (pc_ωF z D 0) t₀ t₁) (hY a')
    · exact Ctrl.sum _ fun c _ => Ctrl.smul (hΓ 0 a' c) (hY c)
    · exact Ctrl.lin (D.Fr.c 0) (Ctrl.sum _ fun i _ => Ctrl.lin (D.Fr.c i.succ)
        (Ctrl.sub (Ctrl.endo (T := fun y v => ωF z D y i.succ v)
          (endBdd_of_pc (pc_ωF z D i.succ) t₀ t₁) (hY a'))
          (Ctrl.sum _ fun c _ => Ctrl.smul (hΓ i.succ a' c) (hY c))))
    · exact Ctrl.lin (D.Fr.c 0) (ctrl_mass D t₀ t₁ (hY a'))
  · exact Ctrl.lin (D.Fr.c 0) (ctrl_ricTerm D hψ t₀ t₁ (ctrl_sD t₀ t₁) a')

end RenewalGeometry.GenCplBd
