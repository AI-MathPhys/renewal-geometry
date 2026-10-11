/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.GeneratedCoupledCont
import RenewalGeometry.Continuum.GeneratedControlCalculus

/-!
# Zero-order bounds for the coupled constraint system: the defects and their forcings

Einstein–Standard-Model action-closure manuscript, `lem:generated-physical-identification`,
coupled spinors.  The unknown of the coupled constraint system is
`𝒰 = (c, ∂c, Y, P, Ȳ, P̄)` (lowered harmonic defect with its first derivatives, tangential spinor
defects and normal prolongation defects).  On a period cell inside the slab where `W` solves the
shift-transported system with the bosonic blocks and head spinors of `z`, the forcings are
controlled by `𝒰`:

* `UF`, `wF` — the unknown and its first-order part;
* `ctrl_sD` — `∇_{(μ}c_{ν)}`; `ctrl_Rf`, `ctrl_Qf` — `R = 𝓜Y - ricTerm(∇_{(μ}c_{ν)})Ψ` and
  `𝒟'Y = R + Pe_0` (and duals).
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

/-! ### Generic control lemmas on the period cell -/

section Generic

variable {E F G : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
variable {U : ST 3 → E} {s : Set (ST 3)}

theorem bdd_of_continuous {c : ST 3 → G} (hc : Continuous c) (t₀ t₁ : ℝ) :
    Bdd c (cube t₀ t₁) := by
  obtain ⟨C, -, hC⟩ := bdd_cube hc t₀ t₁
  exact ⟨C, hC⟩

theorem endBdd_of_pc [NormedSpace ℝ F] [FiniteDimensional ℝ F] [NormedSpace ℝ G]
    {T : ST 3 → F →ₗ[ℝ] G} (hT : PC T) (t₀ t₁ : ℝ) :
    EndBdd (fun y v => T y v) (cube t₀ t₁) :=
  endBdd_cube hT t₀ t₁

theorem Ctrl.smul_vec [NormedSpace ℝ F] {c : ST 3 → ℝ} {v : ST 3 → F} (hc : Ctrl U s c)
    (hv : Bdd v s) : Ctrl U s (fun y => c y • v y) := by
  obtain ⟨C, hC0, hC⟩ := hv.nonneg_bound
  obtain ⟨K, hK, hb⟩ := hc
  refine ⟨K * C, mul_nonneg hK hC0, fun y hy => ?_⟩
  rw [norm_smul]
  calc ‖c y‖ * ‖v y‖ ≤ (K * ‖U y‖) * C := mul_le_mul (hb y hy) (hC y hy) (norm_nonneg _)
        (mul_nonneg hK (norm_nonneg _))
    _ = K * C * ‖U y‖ := by ring

theorem Ctrl.apply {ι : Type*} [Fintype ι] {F' : ι → Type*} [∀ i, NormedAddCommGroup (F' i)]
    {r : ST 3 → ∀ i, F' i} (h : Ctrl U s r) (i : ι) : Ctrl U s (fun y => r y i) :=
  h.of_norm_le fun y _ => norm_le_pi_norm (r y) i

theorem Ctrl.pi {ι : Type*} [Fintype ι] {F' : ι → Type*} [∀ i, NormedAddCommGroup (F' i)]
    {r : ST 3 → ∀ i, F' i} (h : ∀ i, Ctrl U s (fun y => r y i)) : Ctrl U s r := by
  choose K hK hb using h
  refine ⟨∑ i, K i, Finset.sum_nonneg fun i _ => hK i, fun y hy => ?_⟩
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg (Finset.sum_nonneg fun i _ => hK i)
    (norm_nonneg _))).2 fun i => (hb i y hy).trans ?_
  exact mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun j _ => hK j) (Finset.mem_univ i))
    (norm_nonneg _)

/-- A bilinear map of finite-dimensional spaces is bounded. -/
theorem exists_bilin_bound {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [FiniteDimensional ℝ E₁] [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂]
    [NormedSpace ℝ F] (B : E₁ →ₗ[ℝ] E₂ →ₗ[ℝ] F) :
    ∃ C, 0 ≤ C ∧ ∀ a b, ‖B a b‖ ≤ C * ‖a‖ * ‖b‖ := by
  set B' : E₁ →ₗ[ℝ] (E₂ →L[ℝ] F) :=
    (LinearMap.toContinuousLinearMap : (E₂ →ₗ[ℝ] F) ≃ₗ[ℝ] (E₂ →L[ℝ] F)).toLinearMap ∘ₗ B
  set L : E₁ →L[ℝ] (E₂ →L[ℝ] F) := LinearMap.toContinuousLinearMap B'
  refine ⟨‖L‖, L.opNorm_nonneg, fun a b => ?_⟩
  have : B a b = L a b := rfl
  rw [this]
  exact L.le_opNorm₂ a b

theorem Ctrl.bilin {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [FiniteDimensional ℝ E₁] [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂]
    [NormedSpace ℝ F] (B : E₁ →ₗ[ℝ] E₂ →ₗ[ℝ] F) {f : ST 3 → E₁} {g : ST 3 → E₂}
    (hf : Bdd f s) (hg : Ctrl U s g) : Ctrl U s (fun y => B (f y) (g y)) := by
  obtain ⟨C, hC0, hC⟩ := exists_bilin_bound B
  obtain ⟨M, hM0, hM⟩ := hf.nonneg_bound
  obtain ⟨K, hK, hb⟩ := hg
  refine ⟨C * M * K, by positivity, fun y hy => ?_⟩
  calc ‖B (f y) (g y)‖ ≤ C * ‖f y‖ * ‖g y‖ := hC _ _
    _ ≤ C * M * (K * ‖U y‖) := by
        gcongr
        · exact hM y hy
        · exact hb y hy
    _ = C * M * K * ‖U y‖ := by ring

theorem Ctrl.bilin' {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [FiniteDimensional ℝ E₁] [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂]
    [NormedSpace ℝ F] (B : E₁ →ₗ[ℝ] E₂ →ₗ[ℝ] F) {f : ST 3 → E₁} {g : ST 3 → E₂}
    (hf : Ctrl U s f) (hg : Bdd g s) : Ctrl U s (fun y => B (f y) (g y)) :=
  Ctrl.bilin B.flip hg hf

theorem Ctrl.lin {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [NormedSpace ℝ F] (L : E₁ →ₗ[ℝ] F) {f : ST 3 → E₁} (hf : Ctrl U s f) :
    Ctrl U s (fun y => L (f y)) :=
  Ctrl.endo (T := fun _ v => LinearMap.toContinuousLinearMap L v)
    (endBdd_clm (LinearMap.toContinuousLinearMap L)) hf

end Generic


/-! ### The unknown of the coupled constraint system -/

section Unknown

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable {S₀ : Type*} [NormedAddCommGroup S₀] [NormedSpace ℝ S₀] [FiniteDimensional ℝ S₀]

variable (SM : SMData (MatLie m) V S S') (W : ST 3 → StateP m V S S') (z : Tuple m V S S')

/-- The first-order part `(Y, P, Ȳ, P̄)` of the unknown. -/
def wF (y : ST 3) : (Fin 3 → S) × S × (Fin 3 → S') × S' :=
  (Yt SM W z y, Pf SM W z y, Ybt SM W z y, Pbf SM W z y)

/-- **The unknown** `𝒰 = (c, ∂c, Y, P, Ȳ, P̄)`. -/
def UF (y : ST 3) :
    (Fin 4 → ℝ) × (Fin 4 → Fin 4 → ℝ) × ((Fin 3 → S) × S × (Fin 3 → S') × S') :=
  (GenHarmonic.cF z y, fun γ => pd (GenHarmonic.cF z) γ y, wF SM W z y)

theorem norm_UF_le (y : ST 3) : ‖UF SM W z y‖ ≤ ‖GenHarmonic.cF z y‖ +
    ∑ γ, ‖pd (GenHarmonic.cF z) γ y‖ + ‖wF SM W z y‖ := by
  have h1 : ‖(fun γ => pd (GenHarmonic.cF z) γ y)‖ ≤ ∑ γ, ‖pd (GenHarmonic.cF z) γ y‖ :=
    (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)).2 fun γ =>
      Finset.single_le_sum (f := fun γ => ‖pd (GenHarmonic.cF z) γ y‖)
        (fun _ _ => norm_nonneg _) (Finset.mem_univ γ)
  have h0 := norm_nonneg (GenHarmonic.cF z y)
  have h2 := norm_nonneg (wF SM W z y)
  have h3 : 0 ≤ ∑ γ, ‖pd (GenHarmonic.cF z) γ y‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  unfold UF
  rw [Prod.norm_def, Prod.norm_def]
  refine max_le (by linarith) (max_le (by linarith) (by linarith))

variable {SM W z} {s : Set (ST 3)}

theorem ctrl_cF : Ctrl (UF SM W z) s (GenHarmonic.cF z) :=
  Ctrl.of_le_mul zero_le_one fun y _ => by rw [one_mul]; exact norm_fst_le (UF SM W z y)

theorem ctrl_dcF (γ : Fin 4) : Ctrl (UF SM W z) s (pd (GenHarmonic.cF z) γ) :=
  Ctrl.of_le_mul zero_le_one fun y _ => by
    rw [one_mul]
    exact (norm_le_pi_norm (fun γ => pd (GenHarmonic.cF z) γ y) γ).trans
      ((norm_fst_le (UF SM W z y).2).trans (norm_snd_le (UF SM W z y)))

theorem ctrl_wF : Ctrl (UF SM W z) s (wF SM W z) :=
  Ctrl.of_le_mul zero_le_one fun y _ => by
    rw [one_mul]
    exact (norm_snd_le (UF SM W z y).2).trans (norm_snd_le (UF SM W z y))

theorem ctrl_Yt : Ctrl (UF SM W z) s (Yt SM W z) :=
  ctrl_wF.of_norm_le fun y _ => norm_fst_le (wF SM W z y)

theorem ctrl_Pf : Ctrl (UF SM W z) s (Pf SM W z) :=
  ctrl_wF.of_norm_le fun y _ => (norm_fst_le (wF SM W z y).2).trans (norm_snd_le _)

theorem ctrl_Ybt : Ctrl (UF SM W z) s (Ybt SM W z) :=
  ctrl_wF.of_norm_le fun y _ =>
    (norm_fst_le (wF SM W z y).2.2).trans ((norm_snd_le (wF SM W z y).2).trans (norm_snd_le _))

theorem ctrl_Pbf : Ctrl (UF SM W z) s (Pbf SM W z) :=
  ctrl_wF.of_norm_le fun y _ =>
    (norm_snd_le (wF SM W z y).2.2).trans ((norm_snd_le (wF SM W z y).2).trans (norm_snd_le _))

theorem ctrl_Yf : Ctrl (UF SM W z) s (Yf SM W z) :=
  Ctrl.lin (oneFormL SM.D) ctrl_Yt

theorem ctrl_Ybf : Ctrl (UF SM W z) s (Ybf SM W z) :=
  Ctrl.lin (oneFormL SM.Db) ctrl_Ybt

theorem ctrl_cF_apply (l : Fin 4) : Ctrl (UF SM W z) s (fun y => GenHarmonic.cF z y l) :=
  Ctrl.apply ctrl_cF l

theorem ctrl_dcF_apply (γ l : Fin 4) :
    Ctrl (UF SM W z) s (fun y => pd (GenHarmonic.cF z) γ y l) :=
  Ctrl.apply (ctrl_dcF γ) l

theorem ctrl_real_mul {c r : ST 3 → ℝ} (hc : Bdd c s) (hr : Ctrl (UF SM W z) s r) :
    Ctrl (UF SM W z) s (fun y => c y * r y) := by
  simpa only [smul_eq_mul] using Ctrl.smul hc hr

/-- **`∇_{(μ}c_{ν)}` is controlled.** -/
theorem ctrl_sD (t₀ t₁ : ℝ) (μ ν : Fin 4) :
    Ctrl (UF SM W z) (cube t₀ t₁) (fun y => GenCplCov.sD z y μ ν) := by
  have e : (fun y => GenCplCov.sD z y μ ν) = fun y =>
      (1 / 2 : ℝ) * (pd (GenHarmonic.cF z) μ y ν + pd (GenHarmonic.cF z) ν y μ) -
        ∑ l, chr (z.gi y) (z.dg y) l μ ν * GenHarmonic.cF z y l :=
    funext fun y => GenCplBox.sD_eq z y μ ν
  rw [e]
  refine Ctrl.sub (ctrl_real_mul (bdd_of_continuous continuous_const t₀ t₁)
    ((ctrl_dcF_apply μ ν).add (ctrl_dcF_apply ν μ))) (Ctrl.sum _ fun l _ => ?_)
  exact ctrl_real_mul (bdd_of_continuous (z.contDiff_chr l μ ν).continuous t₀ t₁)
    (ctrl_cF_apply l)

theorem ricTerm_eq (D : DiracData (MatLie m) V S₀) (g gi : Fin 4 → Fin 4 → ℝ) (AF : AdaptedFrame)
    (T : Fin 4 → Fin 4 → ℝ) (ψ : S₀) (a : Fin 4) :
    ricTerm D g gi AF T ψ a = ∑ b, ((1 / 2 : ℝ) * (lorentzSign b * frT2 AF.fr T a b)) •
      D.Fr.c b ψ := by
  unfold ricTerm
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, Finset.smul_sum, smul_smul,
    Module.End.smul_def]

/-- **The Ricci-elimination term of a controlled array is controlled.** -/
theorem ctrl_ricTerm (D : DiracData (MatLie m) V S₀) {T : ST 3 → Fin 4 → Fin 4 → ℝ}
    {ψ : ST 3 → S₀} (hψ : Continuous ψ) (t₀ t₁ : ℝ)
    (hT : ∀ μ ν, Ctrl (UF SM W z) (cube t₀ t₁) (fun y => T y μ ν)) (A : Fin 4) :
    Ctrl (UF SM W z) (cube t₀ t₁) (fun y => ricTerm D (z.g y) (z.gi y) (frameU (z.gi y)) (T y)
      (ψ y) A) := by
  simp only [ricTerm_eq]
  refine Ctrl.sum _ fun b _ => Ctrl.smul_vec ?_ (bdd_of_continuous
    ((LinearMap.toContinuousLinearMap (D.Fr.c b)).continuous.comp hψ) t₀ t₁)
  refine ctrl_real_mul (bdd_of_continuous continuous_const t₀ t₁) (ctrl_real_mul
    (bdd_of_continuous continuous_const t₀ t₁) ?_)
  unfold frT2
  refine Ctrl.sum _ fun μ _ => Ctrl.sum _ fun ν _ => ctrl_real_mul ?_ (hT μ ν)
  exact bdd_of_continuous (((GenCplP.contDiff_fr (z := z) A μ).mul
    (GenCplP.contDiff_fr (z := z) b ν)).continuous) t₀ t₁

theorem ctrl_mass (D : DiracData (MatLie m) V S₀) {Y : ST 3 → S₀} (t₀ t₁ : ℝ)
    (hY : Ctrl (UF SM W z) (cube t₀ t₁) Y) :
    Ctrl (UF SM W z) (cube t₀ t₁) (fun y => mass D.m0 D.L (z.H y) (Y y)) := by
  simp only [mass, LinearMap.add_apply]
  exact (Ctrl.lin D.m0 hY).add (Ctrl.bilin D.L (bdd_of_continuous z.H_smooth.continuous t₀ t₁) hY)

/-- **The forcing `R` of the spinor defect rows is controlled.** -/
theorem ctrl_Rf (t₀ t₁ : ℝ) (A : Fin 4) :
    Ctrl (UF SM W z) (cube t₀ t₁) (fun y => Rf SM W z y A) := by
  show Ctrl (UF SM W z) (cube t₀ t₁) (fun y => mass SM.D.m0 SM.D.L (z.H y) (Yf SM W z y A) -
    ricTerm SM.D (z.g y) (z.gi y) (frameU (z.gi y)) (GenCplCov.sD z y) (z.ψ y) A)
  exact (ctrl_mass SM.D t₀ t₁ (Ctrl.apply ctrl_Yf A)).sub
    (ctrl_ricTerm SM.D z.ψ_smooth.continuous t₀ t₁ (ctrl_sD t₀ t₁) A)

theorem ctrl_Rbf (t₀ t₁ : ℝ) (A : Fin 4) :
    Ctrl (UF SM W z) (cube t₀ t₁) (fun y => Rbf SM W z y A) := by
  show Ctrl (UF SM W z) (cube t₀ t₁) (fun y => mass SM.Db.m0 SM.Db.L (z.H y) (Ybf SM W z y A) -
    ricTerm SM.Db (z.g y) (z.gi y) (frameU (z.gi y)) (GenCplCov.sD z y) (z.ψb y) A)
  exact (ctrl_mass SM.Db t₀ t₁ (Ctrl.apply ctrl_Ybf A)).sub
    (ctrl_ricTerm SM.Db z.ψb_smooth.continuous t₀ t₁ (ctrl_sD t₀ t₁) A)

variable {a b : ℝ}

theorem cube_subset_openSlab {t₀ t₁ : ℝ} (ha : a < t₀) (hb : t₁ < b) :
    cube t₀ t₁ ⊆ openSlab a b := fun _ hx =>
  slab_subset_openSlab ha hb (cube_subset_slab t₀ t₁ hx)

/-- **`𝒟'Y` is controlled** (it is `R + Pe_0`). -/
theorem ctrl_Qf (h : CplSol SM W z a b) {t₀ t₁ : ℝ} (ha : a < t₀) (hb : t₁ < b) (A : Fin 4) :
    Ctrl (UF SM W z) (cube t₀ t₁) (fun y => Qf SM W z y A) := by
  refine ((ctrl_Rf t₀ t₁ A).add (Ctrl.apply (F' := fun _ => S) (Ctrl.lin GenCplP.e0L (ctrl_Pf (s := cube t₀ t₁)))
    A)).congr fun y hy => ?_
  rw [Q_eq h (cube_subset_openSlab ha hb hy)]
  rfl

theorem ctrl_Qbf (h : CplSol SM W z a b) {t₀ t₁ : ℝ} (ha : a < t₀) (hb : t₁ < b) (A : Fin 4) :
    Ctrl (UF SM W z) (cube t₀ t₁) (fun y => Qbf SM W z y A) := by
  refine ((ctrl_Rbf t₀ t₁ A).add (Ctrl.apply (F' := fun _ => S') (Ctrl.lin GenCplP.e0L (ctrl_Pbf (s := cube t₀ t₁)))
    A)).congr fun y hy => ?_
  rw [Q_eq_b h (cube_subset_openSlab ha hb hy)]
  rfl

end Unknown


/-! ### Frame-Dirac and frame-divergence expressions of the defects -/

section FrameDirac

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable {S₀ : Type*} [NormedAddCommGroup S₀] [NormedSpace ℝ S₀] [FiniteDimensional ℝ S₀]

variable {SM : SMData (MatLie m) V S S'} {W : ST 3 → StateP m V S S'} {z : Tuple m V S S'}

theorem continuous_fd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ST 3 → E}
    (hf : ContDiff ℝ ∞ f) (A : Fin 4) : Continuous fun y => fd z f A y := by
  have e : (fun y => fd z f A y) = fun y => ∑ γ, (z.FJ y).e A γ • pd f γ y :=
    funext fun y => fd_eq_sum z f A y
  rw [e]
  exact continuous_finsetSum _ fun γ _ =>
    (z.contDiff_e A γ).continuous.smul (contDiff_pd hf γ).continuous

theorem ctrl_conn (D : DiracData (MatLie m) V S₀) {X : ST 3 → Fin 4 → S₀} (t₀ t₁ : ℝ)
    (hX : Ctrl (UF SM W z) (cube t₀ t₁) X) (C A : Fin 4) :
    Ctrl (UF SM W z) (cube t₀ t₁)
      (fun y => ωF z D y C (X y A) - ∑ E, ΓF z y C A E • X y E) := by
  refine Ctrl.sub (Ctrl.endo (T := fun y v => ωF z D y C v) (endBdd_of_pc (pc_ωF z D C) t₀ t₁)
    (Ctrl.apply (F' := fun _ => S₀) hX A)) (Ctrl.sum _ fun E _ => ?_)
  exact Ctrl.smul (bdd_of_continuous (GenCplN.contDiff_ΓF z C A E).continuous t₀ t₁)
    (Ctrl.apply (F' := fun _ => S₀) hX E)

/-- **The frame Dirac expression `Σ_Aε_Ac_Ae_A(X_B)` is controlled by `X` and `𝒟'X`.** -/
theorem ctrl_dirac_fd (D : DiracData (MatLie m) V S₀) {X : ST 3 → Fin 4 → S₀} (t₀ t₁ : ℝ)
    (hX : Ctrl (UF SM W z) (cube t₀ t₁) X)
    (hQ : ∀ B, Ctrl (UF SM W z) (cube t₀ t₁) (fun y => QF z D X y B)) (B : Fin 4) :
    Ctrl (UF SM W z) (cube t₀ t₁) (fun y => ∑ A, D.Fr.ε A • D.Fr.c A (fd z X A y B)) := by
  refine ((hQ B).sub (Ctrl.sum _ fun A _ => ?_)).congr fun y _ =>
    GenCplDiv.dirac_frame_Y z D X y B
  exact Ctrl.smul (bdd_of_continuous continuous_const t₀ t₁)
    (Ctrl.lin (D.Fr.c A) (ctrl_conn D t₀ t₁ hX A B))

/-- **The frame divergence `Σ_Aε_Ae_A(X_A)` of a Clifford-traceless one-form is controlled by
`X` and `𝒟'X`.** -/
theorem ctrl_div_fd (D : DiracData (MatLie m) V S₀) {X : ST 3 → Fin 4 → S₀} (t₀ t₁ : ℝ)
    (hX : Ctrl (UF SM W z) (cube t₀ t₁) X)
    (hQ : ∀ B, Ctrl (UF SM W z) (cube t₀ t₁) (fun y => QF z D X y B))
    (hκ : ∀ y C, kap D.Fr (fd z X C y) = 0) :
    Ctrl (UF SM W z) (cube t₀ t₁) (fun y => ∑ A, D.Fr.ε A • fd z X A y A) := by
  refine (Ctrl.smul (bdd_of_continuous continuous_const t₀ t₁)
    ((Ctrl.lin (kap D.Fr) (Ctrl.pi (F' := fun _ => S₀) hQ)).sub
      (Ctrl.sum _ fun A _ => Ctrl.sum _ fun C _ => ?_))).congr fun y _ =>
    GenCplDiv.div_frame_Y z D X y (hκ y)
  exact Ctrl.smul (bdd_of_continuous continuous_const t₀ t₁)
    (Ctrl.lin (D.Fr.c A) (Ctrl.lin (D.Fr.c C) (ctrl_conn D t₀ t₁ hX C A)))

variable (SM W z) in
theorem kap_fd_Yf (hW : ContDiff ℝ ∞ W) (y : ST 3) (C : Fin 4) :
    kap SM.D.Fr (fd z (Yf SM W z) C y) = 0 := by
  rw [← GenCplDiv.fd_clm_apply z (kap SM.D.Fr) (contDiff_Yf SM W z hW) C]
  have : (fun y => kap SM.D.Fr (Yf SM W z y)) = 0 := funext (kap_Yf SM W z)
  rw [this]
  exact fd_eq_zero_of_eventually z Filter.EventuallyEq.rfl C

variable (SM W z) in
theorem kap_fd_Ybf (hW : ContDiff ℝ ∞ W) (y : ST 3) (C : Fin 4) :
    kap SM.Db.Fr (fd z (Ybf SM W z) C y) = 0 := by
  rw [← GenCplDiv.fd_clm_apply z (kap SM.Db.Fr) (contDiff_Ybf SM W z hW) C]
  have : (fun y => kap SM.Db.Fr (Ybf SM W z y)) = 0 := funext (kap_Ybf SM W z)
  rw [this]
  exact fd_eq_zero_of_eventually z Filter.EventuallyEq.rfl C

end FrameDirac


/-! ### The divergence of the auxiliary Dirac stress -/

section DivS

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']

variable {SM : SMData (MatLie m) V S S'} {W : ST 3 → StateP m V S S'} {z : Tuple m V S S'}

/-- **The frame divergence of the kinetic stress**, regrouped into Dirac and divergence
expressions of the one-forms (transposition of the dual Clifford generators). -/
theorem frame_div_kinT (hP : GenDiracCur.DiracPairing SM) {ψ : ST 3 → S} {ψb : ST 3 → S'}
    {X : ST 3 → Fin 4 → S} {Xb : ST 3 → Fin 4 → S'} (hψ : ContDiff ℝ ∞ ψ)
    (hψb : ContDiff ℝ ∞ ψb) (hX : ContDiff ℝ ∞ X) (hXb : ContDiff ℝ ∞ Xb) (x : ST 3) (B : Fin 4) :
    ∑ A, lorentzSign A * fd z (fun y => GenDStress.kinT SM.D hP.P (ψ y) (X y) (ψb y) (Xb y) A B)
      A x = -(1 / 4 : ℝ) * (∑ A, SM.D.Fr.ε A * hP.P (fd z ψb A x) (SM.D.Fr.c A (X x B)) +
        hP.P (ψb x) (∑ A, SM.D.Fr.ε A • SM.D.Fr.c A (fd z X A x B)) +
        ∑ A, SM.D.Fr.ε A * hP.P (fd z ψb A x) (SM.D.Fr.c B (X x A)) +
        hP.P (ψb x) (SM.D.Fr.c B (∑ A, SM.D.Fr.ε A • fd z X A x A)) -
        hP.P (∑ A, SM.D.Fr.ε A • SM.Db.Fr.c A (fd z Xb A x B)) (ψ x) -
        ∑ A, SM.D.Fr.ε A * hP.P (Xb x B) (SM.D.Fr.c A (fd z ψ A x)) -
        hP.P (∑ A, SM.D.Fr.ε A • fd z Xb A x A) (SM.D.Fr.c B (ψ x)) -
        ∑ A, SM.D.Fr.ε A * hP.P (Xb x A) (SM.D.Fr.c B (fd z ψ A x))) := by
  have hε : SM.D.Fr.ε = lorentzSign := GenCplBox.eps_eq SM.D
  simp only [GenCplDiv.fd_kinT z SM.D hP.P hψ hψb hX hXb x, map_sum, map_smul, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul, hP.c_tr, hε]
  simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun A _ => ?_
  ring

theorem bdd_fd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ST 3 → E}
    (hf : ContDiff ℝ ∞ f) (A : Fin 4) (t₀ t₁ : ℝ) : Bdd (fun y => fd z f A y) (cube t₀ t₁) :=
  bdd_of_continuous (continuous_fd hf A) t₀ t₁

variable {a b : ℝ}

/-- **The frame divergence of the kinetic stress of the defects is controlled.** -/
theorem ctrl_frame_div (hC : GenDStress.CoupledDirac SM) (hW : ContDiff ℝ ∞ W)
    (h : CplSol SM W z a b) {t₀ t₁ : ℝ} (ha : a < t₀) (hb : t₁ < b) (B : Fin 4) :
    Ctrl (UF SM W z) (cube t₀ t₁) (fun y => ∑ A, lorentzSign A * fd z (fun y' =>
      GenDStress.kinT SM.D hC.P (z.ψ y') (Yf SM W z y') (z.ψb y') (Ybf SM W z y') A B) A y) := by
  have hY := contDiff_Yf SM W z hW
  have hYb := contDiff_Ybf SM W z hW
  have hψ := z.ψ_smooth
  have hψb := z.ψb_smooth
  have bψ := bdd_of_continuous hψ.continuous t₀ t₁
  have bψb := bdd_of_continuous hψb.continuous t₀ t₁
  have cY : Ctrl (UF SM W z) (cube t₀ t₁) (Yf SM W z) := ctrl_Yf
  have cYb : Ctrl (UF SM W z) (cube t₀ t₁) (Ybf SM W z) := ctrl_Ybf
  have hQ : ∀ B, Ctrl (UF SM W z) (cube t₀ t₁) (fun y => QF z SM.D (Yf SM W z) y B) :=
    fun B => ctrl_Qf h ha hb B
  have hQb : ∀ B, Ctrl (UF SM W z) (cube t₀ t₁) (fun y => QF z SM.Db (Ybf SM W z) y B) :=
    fun B => ctrl_Qbf h ha hb B
  have hεb : SM.Db.Fr.ε = SM.D.Fr.ε := GenDiracCur.eps_Db_eq
  refine Ctrl.congr ?_ fun y _ => frame_div_kinT hC.toDiracPairing hψ hψb hY hYb y B
  refine Ctrl.smul (bdd_of_continuous continuous_const t₀ t₁) ?_
  refine ((((((((Ctrl.sum _ fun A _ => ?_).add ?_).add (Ctrl.sum _ fun A _ => ?_)).add ?_).sub
    ?_).sub (Ctrl.sum _ fun A _ => ?_)).sub ?_).sub (Ctrl.sum _ fun A _ => ?_))
  · exact ctrl_real_mul (bdd_of_continuous continuous_const t₀ t₁) (Ctrl.bilin hC.P
      (bdd_fd hψb A t₀ t₁) (Ctrl.lin (SM.D.Fr.c A) (Ctrl.apply (F' := fun _ => S) cY B)))
  · exact Ctrl.bilin hC.P bψb (ctrl_dirac_fd SM.D t₀ t₁ cY hQ B)
  · exact ctrl_real_mul (bdd_of_continuous continuous_const t₀ t₁) (Ctrl.bilin hC.P
      (bdd_fd hψb A t₀ t₁) (Ctrl.lin (SM.D.Fr.c B) (Ctrl.apply (F' := fun _ => S) cY A)))
  · exact Ctrl.bilin hC.P bψb (Ctrl.lin (SM.D.Fr.c B)
      (ctrl_div_fd SM.D t₀ t₁ cY hQ (kap_fd_Yf SM W z hW)))
  · have := ctrl_dirac_fd SM.Db t₀ t₁ cYb hQb B
    rw [hεb] at this
    exact Ctrl.bilin' hC.P this bψ
  · exact ctrl_real_mul (bdd_of_continuous continuous_const t₀ t₁) (Ctrl.bilin' hC.P
      (Ctrl.apply (F' := fun _ => S') cYb B)
      (bdd_of_continuous ((LinearMap.toContinuousLinearMap (SM.D.Fr.c A)).continuous.comp
        (continuous_fd hψ A)) t₀ t₁))
  · have := ctrl_div_fd SM.Db t₀ t₁ cYb hQb (kap_fd_Ybf SM W z hW)
    rw [hεb] at this
    exact Ctrl.bilin' hC.P this (bdd_of_continuous
      ((LinearMap.toContinuousLinearMap (SM.D.Fr.c B)).continuous.comp hψ.continuous) t₀ t₁)
  · exact ctrl_real_mul (bdd_of_continuous continuous_const t₀ t₁) (Ctrl.bilin' hC.P
      (Ctrl.apply (F' := fun _ => S') cYb A)
      (bdd_of_continuous ((LinearMap.toContinuousLinearMap (SM.D.Fr.c B)).continuous.comp
        (continuous_fd hψ A)) t₀ t₁))

end DivS


section DivS2

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']

variable {SM : SMData (MatLie m) V S S'} {W : ST 3 → StateP m V S S'} {z : Tuple m V S S'}

variable (hC : GenDStress.CoupledDirac SM) (W z) in
/-- The frame kinetic stress `K_{AB}(Y, Ȳ)` of the defects. -/
def Kf (y : ST 3) (A B : Fin 4) : ℝ :=
  GenDStress.kinT SM.D hC.P (z.ψ y) (Yf SM W z y) (z.ψb y) (Ybf SM W z y) A B

theorem ΔSf_eq (hC : GenDStress.CoupledDirac SM) (y : ST 3) (μ ν : Fin 4) :
    GenCplSD.ΔSf hC W z y μ ν = GenCplDiv.frameTensor z (Kf W z hC) y μ ν := rfl

theorem ctrl_Kf (hC : GenDStress.CoupledDirac SM) (t₀ t₁ : ℝ) (A B : Fin 4) :
    Ctrl (UF SM W z) (cube t₀ t₁) (fun y => Kf W z hC y A B) := by
  have bψ := bdd_of_continuous z.ψ_smooth.continuous t₀ t₁
  have bψb := bdd_of_continuous z.ψb_smooth.continuous t₀ t₁
  have cY : Ctrl (UF SM W z) (cube t₀ t₁) (Yf SM W z) := ctrl_Yf
  have cYb : Ctrl (UF SM W z) (cube t₀ t₁) (Ybf SM W z) := ctrl_Ybf
  have bc : ∀ C, Bdd (fun y => SM.D.Fr.c C (z.ψ y)) (cube t₀ t₁) := fun C =>
    bdd_of_continuous ((LinearMap.toContinuousLinearMap (SM.D.Fr.c C)).continuous.comp
      z.ψ_smooth.continuous) t₀ t₁
  unfold Kf GenDStress.kinT
  refine ctrl_real_mul (bdd_of_continuous continuous_const t₀ t₁) ((((Ctrl.bilin hC.P bψb
    (Ctrl.lin (SM.D.Fr.c A) (Ctrl.apply (F' := fun _ => S) cY B))).add (Ctrl.bilin hC.P bψb
    (Ctrl.lin (SM.D.Fr.c B) (Ctrl.apply (F' := fun _ => S) cY A)))).sub
    (Ctrl.bilin' hC.P (Ctrl.apply (F' := fun _ => S') cYb B) (bc A))).sub
    (Ctrl.bilin' hC.P (Ctrl.apply (F' := fun _ => S') cYb A) (bc B)))

theorem ctrl_frameTensor {K : ST 3 → Fin 4 → Fin 4 → ℝ} {t₀ t₁ : ℝ}
    (hK : ∀ A B, Ctrl (UF SM W z) (cube t₀ t₁) (fun y => K y A B)) (a' b' : Fin 4) :
    Ctrl (UF SM W z) (cube t₀ t₁) (fun y => GenCplDiv.frameTensor z K y a' b') := by
  unfold GenCplDiv.frameTensor
  refine Ctrl.sum _ fun A _ => Ctrl.sum _ fun B _ => ctrl_real_mul ?_ (hK A B)
  exact bdd_of_continuous ((GenCplSub.contDiff_θF (z := z) A a').mul
    (GenCplSub.contDiff_θF (z := z) B b')).continuous t₀ t₁

theorem ctrl_remDiv {K : ST 3 → Fin 4 → Fin 4 → ℝ} {t₀ t₁ : ℝ}
    (hK : ∀ A B, Ctrl (UF SM W z) (cube t₀ t₁) (fun y => K y A B)) (b' : Fin 4) :
    Ctrl (UF SM W z) (cube t₀ t₁) (fun y => GenCplDiv.remDiv z K y b') := by
  have hθ := fun A a' => GenCplSub.contDiff_θF (z := z) A a'
  have hpθ := fun e A a' => (contDiff_pd (hθ A a') e).continuous
  unfold GenCplDiv.remDiv
  refine Ctrl.sum _ fun e _ => Ctrl.sum _ fun a' _ => ctrl_real_mul
    (bdd_of_continuous (z.contDiff_gi e a').continuous t₀ t₁) (Ctrl.sub (Ctrl.sub
      (Ctrl.sum _ fun A _ => Ctrl.sum _ fun B _ => ctrl_real_mul ?_ (hK A B))
      (Ctrl.sum _ fun l _ => ctrl_real_mul ?_ (ctrl_frameTensor hK l b')))
      (Ctrl.sum _ fun l _ => ?_))
  · exact bdd_of_continuous (((hpθ e A a').mul (hθ B b').continuous).add
      ((hθ A a').continuous.mul (hpθ e B b'))) t₀ t₁
  · exact bdd_of_continuous (z.contDiff_chr l e a').continuous t₀ t₁
  · simpa only [mul_comm] using ctrl_real_mul
      (bdd_of_continuous (z.contDiff_chr l e b').continuous t₀ t₁) (ctrl_frameTensor hK a' l)

variable {a b : ℝ}

/-- **The divergence of the auxiliary Dirac stress is controlled by the unknown.** -/
theorem ctrl_divS (hC : GenDStress.CoupledDirac SM) (hW : ContDiff ℝ ∞ W)
    (h : CplSol SM W z a b) {t₀ t₁ : ℝ} (ha : a < t₀) (hb : t₁ < b) (b' : Fin 4) :
    Ctrl (UF SM W z) (cube t₀ t₁) (fun y => ContractedBianchiJet.SubsidiarySource.divS
      (GenHarmonic.jet3 z y) (Matrix.of (GenCplSD.ΔSf hC W z y))
      (fun e => Matrix.of fun a' b'' => pd (fun y' => GenCplSD.ΔSf hC W z y' a' b'') e y) b') := by
  have hKs : ∀ A B, ContDiff ℝ ∞ (fun y => Kf W z hC y A B) := fun A B =>
    GenCplSub.contDiff_kinT SM.D hC.P z.ψ_smooth z.ψb_smooth (contDiff_Yf SM W z hW)
      (contDiff_Ybf SM W z hW) A B
  have hmain : ∀ y, ContractedBianchiJet.SubsidiarySource.divS
      (GenHarmonic.jet3 z y) (Matrix.of (GenCplSD.ΔSf hC W z y))
      (fun e => Matrix.of fun a' b'' => pd (fun y' => GenCplSD.ΔSf hC W z y' a' b'') e y) b' =
      ∑ B, GenCplSD.θF z y B b' * (∑ A, lorentzSign A * fd z (fun y' => GenDStress.kinT SM.D hC.P
        (z.ψ y') (Yf SM W z y') (z.ψb y') (Ybf SM W z y') A B) A y) +
        GenCplDiv.remDiv z (Kf W z hC) y b' := by
    intro y
    have e := GenCplDiv.divS_main z hKs y b'
    have e2 : ContractedBianchiJet.SubsidiarySource.divS
        (GenHarmonic.jet3 z y) (Matrix.of (GenCplSD.ΔSf hC W z y))
        (fun e => Matrix.of fun a' b'' => pd (fun y' => GenCplSD.ΔSf hC W z y' a' b'') e y) b' =
        ContractedBianchiJet.SubsidiarySource.divS (GenHarmonic.jet3 z y)
        (Matrix.of (GenCplDiv.frameTensor z (Kf W z hC) y))
        (fun e => Matrix.of fun a' b'' => pd (fun y' => GenCplDiv.frameTensor z (Kf W z hC) y' a'
          b'') e y) b' := rfl
    rw [e2, e]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun B _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun A _ => ?_
    unfold Kf
    ring
  refine Ctrl.congr ?_ fun y _ => hmain y
  refine (Ctrl.sum _ fun B _ => ctrl_real_mul ?_ (ctrl_frame_div hC hW h ha hb B)).add
    (ctrl_remDiv (fun A B => ctrl_Kf hC t₀ t₁ A B) b')
  exact bdd_of_continuous (GenCplSub.contDiff_θF (z := z) B b').continuous t₀ t₁

end DivS2

end RenewalGeometry.GenCplBd
