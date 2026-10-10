/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.CNSlabNorms

/-!
# `C^N` continuity of the actual-jet state and of the harmonic defect

Einstein–Standard-Model action-closure manuscript, `cor:local-calibration-nonempty` ("derivative
convergence controls the initial and harmonic mismatches") and `thm:native-closure`
(`eq:native-initial-gauge`: `i_{h,k} = ‖𝒰_h(0) - 𝒰_*(0)‖_{H^k}`,
`γ_{h,k} = ‖C(g_h)‖_{L²H^{k+1}} + ‖∂_tC(g_h)‖_{L²H^k}`).

For smooth actual field tuples `z_i → z₀` in `C^{N+1}` (`TupleCN`: metric, gauge potential, Higgs
field and both spinors converge uniformly with all derivatives of order `≤ N + 1`), with the
reference metric in a compact subset of the Lorentzian chart (`MetCompact`), for any theory data
`SM`:

* **`stateF_CN`** — the actual-jet state fields `𝒰(z_i) → 𝒰(z₀)` in `C^N`;
* **`CF_CN`** — the harmonic defects `C(g_i) → C(g₀)` in `C^N`.

The state is a smooth function of the metric 1-jet (through `g⁻¹`, the adapted frame
`e = frU(g⁻¹)` and its derivative, the connection coefficients `G_{ABC}`) and is multilinear in the
matter jets with fixed coefficients (Lie bracket, gauge action, Clifford generators); each step is
an instance of the generic calculus `CNConv` (`CN.comp`, `CN.bilin`, `CN.fderiv_apply`).

As a consequence (`init_tendsto`, `harm_tendsto`): in the concrete slab model of
`prop:coupled-bootstrap`, `i(z_i) = ‖init(z_i) - init(z₀)‖ → 0`, and if `z₀` is exact on the slab
(harmonic gauge `C(g₀) = 0` there), `γ(z_i) = harm(z_i) → 0`.
-/

open Filter Topology Set Metric
open scoped ContDiff

noncomputable section

namespace RenewalGeometry.StateConv

open SobolevOpen (pd)
open CNConv PeriodicCube SymHypEnergy SlabWaveHk SlabSobAlg QLEnergy FrameCurvature
  HarmonicDefect ActualJetWriter ActualJetFrame ActualJetSystem ActualJetSmooth ActualJetGauge
  ActualJetBridge ActualJetCompleteForcing ActualJetState SpinorProlongation TwistedHalfRicci
  CoupledBootstrap

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024

/-! ### Generic: composition with globally smooth maps; continuous bilinear maps -/

section Generic

universe u

variable {ι : Type*} {l : Filter ι} {N : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Composition with a globally smooth map** (the limit has bounded range). -/
theorem CN_comp_contDiff {Gc Hc : Type u} [NormedAddCommGroup Gc] [NormedSpace ℝ Gc]
    [FiniteDimensional ℝ Gc] [NormedAddCommGroup Hc] [NormedSpace ℝ Hc] {Ψ : Gc → Hc}
    (hΨ : ContDiff ℝ ∞ Ψ) {F : ι → E → Gc} {F₀ : E → Gc} (h : CN N l F F₀) :
    CN N l (fun i x => Ψ (F i x)) (fun x => Ψ (F₀ x)) := by
  obtain ⟨C, hC⟩ := h.bdd
  refine CN.comp isOpen_univ hΨ.contDiffOn (isCompact_closedBall (0 : Gc) C) (subset_univ _)
    (fun x => ?_) h
  rw [mem_closedBall, dist_zero_right]
  simpa using hC 0 (Nat.zero_le _) x

variable {F G H : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- A bilinear map on finite-dimensional spaces as a continuous bilinear map. -/
def toCLM₂ (B : F →ₗ[ℝ] G →ₗ[ℝ] H) : F →L[ℝ] G →L[ℝ] H :=
  LinearMap.toContinuousLinearMap
    ((LinearMap.toContinuousLinearMap : (G →ₗ[ℝ] H) ≃ₗ[ℝ] (G →L[ℝ] H)).toLinearMap ∘ₗ B)

@[simp] theorem toCLM₂_apply (B : F →ₗ[ℝ] G →ₗ[ℝ] H) (x : F) (y : G) : toCLM₂ B x y = B x y :=
  rfl

end Generic

/-! ### Charts -/

/-- The inverse metric is smooth on `{det g ≠ 0}`. -/
theorem contDiffOn_ginvOf :
    ContDiffOn ℝ ∞ (fun g : Fin 4 → Fin 4 → ℝ => ginvOf g) {g | (Matrix.of g).det ≠ 0} :=
  fun g hg => (contDiffAt_pi.2 fun i => contDiffAt_pi.2 fun j =>
    (contDiffAt_ginvOf' hg i j).of_le le_top).contDiffWithinAt

theorem isOpen_det_ne : IsOpen {g : Fin 4 → Fin 4 → ℝ | (Matrix.of g).det ≠ 0} :=
  isOpen_ne_fun (Continuous.matrix_det (A := fun g : Fin 4 → Fin 4 → ℝ => Matrix.of g)
    continuous_id) continuous_const

/-- The adapted frame is smooth on the Lorentzian chart. -/
theorem contDiffOn_frU : ContDiffOn ℝ ∞ (fun gi : IMet => frU gi) {gi | IsLorChart gi} :=
  fun _ hgi => (contDiffAt_pi.2 fun A => contDiffAt_pi.2 fun μ =>
    (contDiffAt_frU hgi A μ).of_le le_top).contDiffWithinAt

/-! ### Convergence of tuples -/

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable {ι : Type*} {l : Filter ι}

/-- **`C^N` convergence of actual field tuples**: metric, gauge potential, Higgs field and both
spinors. -/
structure TupleCN (N : ℕ) (l : Filter ι) (z : ι → Tuple m V S S') (z₀ : Tuple m V S S') :
    Prop where
  g : CN N l (fun i => (z i).g) z₀.g
  A : CN N l (fun i => (z i).A) z₀.A
  H : CN N l (fun i => (z i).H) z₀.H
  ψ : CN N l (fun i => (z i).ψ) z₀.ψ
  ψb : CN N l (fun i => (z i).ψb) z₀.ψb

theorem TupleCN.mono {N M : ℕ} {z : ι → Tuple m V S S'} {z₀ : Tuple m V S S'}
    (h : TupleCN N l z z₀) (hM : M ≤ N) : TupleCN M l z z₀ :=
  ⟨h.g.mono hM, h.A.mono hM, h.H.mono hM, h.ψ.mono hM, h.ψb.mono hM⟩

/-- **The reference metric stays in a compact subset of the Lorentzian chart.** -/
def MetCompact (z₀ : Tuple m V S S') : Prop :=
  ∃ Kg : Set (Fin 4 → Fin 4 → ℝ), IsCompact Kg ∧
    (∀ g ∈ Kg, (Matrix.of g).det ≠ 0 ∧ IsLorChart (ginvOf g)) ∧ ∀ x, z₀.g x ∈ Kg

variable {N : ℕ} {z : ι → Tuple m V S S'} {z₀ : Tuple m V S S'}

theorem cn_gi (h : CN N l (fun i => (z i).g) z₀.g) (hK : MetCompact z₀) :
    CN N l (fun i => (z i).gi) z₀.gi := by
  obtain ⟨Kg, hKg, hKc, hz⟩ := hK
  exact CN.comp isOpen_det_ne contDiffOn_ginvOf hKg (fun g hg => (hKc g hg).1) hz h

theorem cn_e (h : CN N l (fun i => (z i).g) z₀.g) (hK : MetCompact z₀) :
    CN N l (fun i => (z i).e) z₀.e := by
  have hgi := cn_gi h hK
  obtain ⟨Kg, hKg, hKc, hz⟩ := hK
  have hc : IsCompact ((fun g : Fin 4 → Fin 4 → ℝ => ginvOf g) '' Kg) :=
    hKg.image_of_continuousOn (contDiffOn_ginvOf.continuousOn.mono fun g hg => (hKc g hg).1)
  exact CN.comp isOpen_isLorChart contDiffOn_frU hc
    (by rintro _ ⟨g, hg, rfl⟩; exact (hKc g hg).2) (fun x => ⟨_, hz x, rfl⟩) hgi

theorem cn_dg (h : CN (N + 1) l (fun i => (z i).g) z₀.g) :
    CN N l (fun i => (z i).dg) z₀.dg :=
  CN.pi fun α => h.fderiv_apply (Pi.single α 1)

theorem cn_de (h : CN (N + 1) l (fun i => (z i).g) z₀.g) (hK : MetCompact z₀) :
    CN N l (fun i => (z i).de) z₀.de := by
  have he := cn_e h hK
  refine (CN.pi fun γ => CN.pi fun A => CN.pi fun μ =>
    (he.apply A |>.apply μ).fderiv_apply (Pi.single γ 1)).congr
    (Eventually.of_forall fun i => ?_) ?_
  · funext y γ A μ; exact ((z i).pd_e y γ A μ).symm
  · funext y γ A μ; exact (z₀.pd_e y γ A μ).symm

/-- The real frame-jet data `(g, g⁻¹, ∂g, e, ∂e)` of a tuple at a point. -/
abbrev FJP := (Fin 4 → Fin 4 → ℝ) × (Fin 4 → Fin 4 → ℝ) × (Fin 4 → Fin 4 → Fin 4 → ℝ) ×
  (Fin 4 → Fin 4 → ℝ) × (Fin 4 → Fin 4 → Fin 4 → ℝ)

/-- The frame-jet field of a tuple. -/
def fjet (z : Tuple m V S S') (y : ST 3) : FJP := (z.g y, z.gi y, z.dg y, z.e y, z.de y)

theorem cn_fjet (h : CN (N + 1) l (fun i => (z i).g) z₀.g) (hK : MetCompact z₀) :
    CN N l (fun i => fjet (z i)) (fjet z₀) :=
  (h.mono (Nat.le_succ N)).prod ((cn_gi (h.mono (Nat.le_succ N)) hK).prod
    ((cn_dg h).prod ((cn_e (h.mono (Nat.le_succ N)) hK).prod (cn_de h hK))))

/-- Any smooth function of the frame-jet data converges. -/
theorem cn_phi {R : Type} [NormedAddCommGroup R] [NormedSpace ℝ R] {Φ : FJP → R}
    (hΦ : ContDiff ℝ ∞ Φ) (h : CN (N + 1) l (fun i => (z i).g) z₀.g) (hK : MetCompact z₀) :
    CN N l (fun i y => Φ (fjet (z i) y)) (fun y => Φ (fjet z₀ y)) :=
  CN_comp_contDiff hΦ (cn_fjet h hK)

/-! ### The harmonic defect -/

/-- The harmonic defect as a function of the frame-jet data. -/
def phiC (p : FJP) : Fin 4 → ℝ := fun l => ActualJetWriter.C p.2.1 p.2.2.1 l

theorem contDiff_phiC : ContDiff ℝ ∞ phiC := by
  refine contDiff_pi.2 fun l => ?_
  show ContDiff ℝ ∞ (fun p : FJP => ActualJetWriter.C p.2.1 p.2.2.1 l)
  unfold ActualJetWriter.C cUp chr
  fun_prop

/-- **The harmonic defects converge in `C^N`.** -/
theorem CF_CN (h : TupleCN (N + 1) l z z₀) (hK : MetCompact z₀) :
    CN N l (fun i => CF (z i)) (CF z₀) :=
  cn_phi contDiff_phiC h.g hK

/-! ### The state components -/

section State

variable (SM : SMData (MatLie m) V S S')

/-- Real frame coefficients converge. -/
theorem cn_eAμ (h : TupleCN (N + 1) l z z₀) (hK : MetCompact z₀) (B μ : Fin 4) :
    CN N l (fun i y => (z i).e y B μ) (fun y => z₀.e y B μ) :=
  ((cn_e (h.g.mono (Nat.le_succ N)) hK).apply B).apply μ

/-- Products of a real field and a vector field. -/
theorem cn_smul {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {r : ι → ST 3 → ℝ}
    {r₀ : ST 3 → ℝ} {v : ι → ST 3 → G} {v₀ : ST 3 → G} (hr : CN N l r r₀) (hv : CN N l v v₀) :
    CN N l (fun i y => r i y • v i y) (fun y => r₀ y • v₀ y) :=
  hr.bilin hv (ContinuousLinearMap.lsmul ℝ ℝ)

/-- Products of real fields. -/
theorem cn_mul {r s : ι → ST 3 → ℝ} {r₀ s₀ : ST 3 → ℝ} (hr : CN N l r r₀) (hs : CN N l s s₀) :
    CN N l (fun i y => r i y * s i y) (fun y => r₀ y * s₀ y) :=
  hr.bilin hs (ContinuousLinearMap.mul ℝ ℝ)

theorem cn_p (h : TupleCN (N + 1) l z z₀) (hK : MetCompact z₀) :
    CN N l (fun i y => (((z i).jet y).state SM).p) (fun y => ((z₀.jet y).state SM).p) := by
  refine (cn_phi (Φ := fun q : FJP => fun μ ν => ∑ β, q.2.2.2.1 0 β * q.2.2.1 β μ ν)
    (by refine contDiff_pi.2 fun μ => contDiff_pi.2 fun ν => ?_; fun_prop) h.g hK).congr
    (Eventually.of_forall fun i => rfl) rfl

theorem cn_q (h : TupleCN (N + 1) l z z₀) (hK : MetCompact z₀) :
    CN N l (fun i y => (((z i).jet y).state SM).q) (fun y => ((z₀.jet y).state SM).q) := by
  refine (cn_phi (Φ := fun q : FJP => fun (a : Fin 3) μ ν => ∑ β, q.2.2.2.1 a.succ β * q.2.2.1 β μ ν)
    (by
      refine contDiff_pi.2 fun a => contDiff_pi.2 fun μ => contDiff_pi.2 fun ν => ?_
      fun_prop) h.g hK).congr
    (Eventually.of_forall fun i => rfl) rfl

/-- The Lie bracket of `gl(m)` as a continuous bilinear map. -/
def brL : MatLie m →L[ℝ] MatLie m →L[ℝ] MatLie m :=
  toCLM₂ (LinearMap.mk₂ ℝ (fun a b : MatLie m => ⁅a, b⁆) (fun a a' b => add_lie a a' b)
    (fun c a b => smul_lie c a b) (fun a b b' => lie_add a b b') (fun c a b => lie_smul c a b))

/-- The gauge action on the Higgs space as a continuous bilinear map. -/
def actL : MatLie m →L[ℝ] V →L[ℝ] V :=
  toCLM₂ (LinearMap.mk₂ ℝ (fun (a : MatLie m) (v : V) => ⁅a, v⁆) (fun a a' v => add_lie a a' v)
    (fun c a v => smul_lie c a v) (fun a v v' => lie_add a v v') (fun c a v => lie_smul c a v))

theorem brL_apply (a b : MatLie m) : brL a b = ⁅a, b⁆ := rfl

theorem actL_apply (a : MatLie m) (v : V) : actL a v = ⁅a, v⁆ := rfl

theorem cn_dA (h : TupleCN (N + 1) l z z₀) (γ μ : Fin 4) :
    CN N l (fun i y => pd (z i).A γ y μ) (fun y => pd z₀.A γ y μ) :=
  (h.A.fderiv_apply (Pi.single γ 1)).apply μ

theorem cn_Aμ (h : TupleCN (N + 1) l z z₀) (μ : Fin 4) :
    CN N l (fun i y => (z i).A y μ) (fun y => z₀.A y μ) :=
  (h.A.mono (Nat.le_succ N)).apply μ

/-- The field strength converges. -/
theorem cn_Fm (h : TupleCN (N + 1) l z z₀) (μ ν : Fin 4) :
    CN N l (fun i y => Fm ((z i).jet y).A ((z i).jet y).dA μ ν)
      (fun y => Fm (z₀.jet y).A (z₀.jet y).dA μ ν) := by
  refine (((cn_dA h μ ν).sub (cn_dA h ν μ)).add
    ((cn_Aμ h μ).bilin (cn_Aμ h ν) brL)).congr (Eventually.of_forall fun i => rfl) rfl

/-- Frame components of a tensor field `Σ_{μν} e_b^μ e_c^ν T_{μν}`. -/
theorem cn_frT {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] (h : TupleCN (N + 1) l z z₀)
    (hK : MetCompact z₀) {T : ι → ST 3 → Fin 4 → Fin 4 → G} {T₀ : ST 3 → Fin 4 → Fin 4 → G}
    (hT : ∀ μ ν, CN N l (fun i y => T i y μ ν) (fun y => T₀ y μ ν)) (b c : Fin 4) :
    CN N l (fun i y => ∑ μ, ∑ ν, ((z i).e y b μ * (z i).e y c ν) • T i y μ ν)
      (fun y => ∑ μ, ∑ ν, (z₀.e y b μ * z₀.e y c ν) • T₀ y μ ν) :=
  CN.sum _ fun μ _ => CN.sum _ fun ν _ =>
    cn_smul (cn_mul (cn_eAμ h hK b μ) (cn_eAμ h hK c ν)) (hT μ ν)

theorem cn_E (h : TupleCN (N + 1) l z z₀) (hK : MetCompact z₀) :
    CN N l (fun i y => (((z i).jet y).state SM).E) (fun y => ((z₀.jet y).state SM).E) :=
  CN.pi fun a => (cn_frT h hK (cn_Fm h) 0 a.succ).congr (Eventually.of_forall fun i => rfl) rfl

theorem cn_B (h : TupleCN (N + 1) l z z₀) (hK : MetCompact z₀) :
    CN N l (fun i y => (((z i).jet y).state SM).B) (fun y => ((z₀.jet y).state SM).B) := by
  refine CN.pi fun a => ?_
  have hS : ∀ b c : Fin 3, CN N l
      (fun i y => ∑ μ, ∑ ν, ((z i).e y b.succ μ * (z i).e y c.succ ν) •
        Fm ((z i).jet y).A ((z i).jet y).dA μ ν)
      (fun y => ∑ μ, ∑ ν, (z₀.e y b.succ μ * z₀.e y c.succ ν) •
        Fm (z₀.jet y).A (z₀.jet y).dA μ ν) :=
    fun b c => cn_frT h hK (cn_Fm h) b.succ c.succ
  have := (CN.sum Finset.univ fun b _ => CN.sum Finset.univ fun c _ =>
    (hS b c).clm ((eps3 a b c) • ContinuousLinearMap.id ℝ (MatLie m))).clm
    (-(1 / 2 : ℝ) • ContinuousLinearMap.id ℝ (MatLie m))
  refine this.congr (Eventually.of_forall fun i => funext fun y => ?_) (funext fun y => ?_) <;>
  · simp only [ActualJet.state, magn, dualVec, Fsp, frT, ContinuousLinearMap.coe_smul', Pi.smul_apply,
      ContinuousLinearMap.id_apply]
    rfl

theorem cn_H (h : TupleCN (N + 1) l z z₀) :
    CN N l (fun i y => (((z i).jet y).state SM).H) (fun y => ((z₀.jet y).state SM).H) :=
  h.H.mono (Nat.le_succ N)

/-- The covariant Higgs gradient in the frame converges. -/
theorem cn_frV (h : TupleCN (N + 1) l z z₀) (hK : MetCompact z₀) (B : Fin 4) :
    CN N l (fun i y => frV ((z i).jet y).AF ((z i).jet y).A ((z i).jet y).H ((z i).jet y).dH B)
      (fun y => frV (z₀.jet y).AF (z₀.jet y).A (z₀.jet y).H (z₀.jet y).dH B) := by
  have hD : ∀ μ, CN N l (fun i y => pd (z i).H μ y + ⁅(z i).A y μ, (z i).H y⁆)
      (fun y => pd z₀.H μ y + ⁅z₀.A y μ, z₀.H y⁆) := fun μ =>
    (h.H.fderiv_apply (Pi.single μ 1)).add ((cn_Aμ h μ).bilin (h.H.mono (Nat.le_succ N)) actL)
  exact (CN.sum Finset.univ fun μ _ => cn_smul (cn_eAμ h hK B μ) (hD μ)).congr
    (Eventually.of_forall fun i => rfl) rfl

theorem cn_Pm (h : TupleCN (N + 1) l z z₀) (hK : MetCompact z₀) :
    CN N l (fun i y => (((z i).jet y).state SM).Pm) (fun y => ((z₀.jet y).state SM).Pm) :=
  cn_frV h hK 0

theorem cn_Q (h : TupleCN (N + 1) l z z₀) (hK : MetCompact z₀) :
    CN N l (fun i y => (((z i).jet y).state SM).Q) (fun y => ((z₀.jet y).state SM).Q) :=
  CN.pi fun a => cn_frV h hK a.succ

/-- The connection coefficients `G_{ABC}` as a function of the frame-jet data. -/
def phiG (A B C : Fin 4) (q : FJP) : ℝ :=
  ∑ γ, q.2.2.2.1 A γ * ipg q.1
    (fun μ => cv1 (chr q.2.1 q.2.2.1) (q.2.2.2.1 B) (fun γ μ => q.2.2.2.2 γ B μ) γ μ)
    (q.2.2.2.1 C)

theorem contDiff_phiG (A B C : Fin 4) : ContDiff ℝ ∞ (phiG A B C) := by
  unfold phiG ipg cv1 chr
  fun_prop

theorem cn_G (h : TupleCN (N + 1) l z z₀) (hK : MetCompact z₀) (A B C : Fin 4) :
    CN N l (fun i y => ((z i).FJ y).G A B C) (fun y => (z₀.FJ y).G A B C) :=
  (cn_phi (contDiff_phiG A B C) h.g hK).congr (Eventually.of_forall fun i => rfl) rfl

/-- **The tangential spinor derivatives converge** (generic Dirac block and spinor field). -/
theorem cn_Xs {S₀ : Type*} [NormedAddCommGroup S₀] [NormedSpace ℝ S₀] [FiniteDimensional ℝ S₀]
    (D : DiracData (MatLie m) V S₀) {ψF : ι → ST 3 → S₀} {ψ₀ : ST 3 → S₀}
    (hψ : CN (N + 1) l ψF ψ₀) (h : TupleCN (N + 1) l z z₀) (hK : MetCompact z₀) (A : Fin 4) :
    CN N l (fun i y => ((z i).jet y).Xs D (ψF i y) (fun γ => pd (ψF i) γ y) A)
      (fun y => (z₀.jet y).Xs D (ψ₀ y) (fun γ => pd ψ₀ γ y) A) := by
  have hψN := hψ.mono (Nat.le_succ N)
  have h1 : CN N l (fun i y => ∑ γ, (z i).e y A γ • pd (ψF i) γ y)
      (fun y => ∑ γ, z₀.e y A γ • pd ψ₀ γ y) :=
    CN.sum _ fun γ _ => cn_smul (cn_eAμ h hK A γ) (hψ.fderiv_apply (Pi.single γ 1))
  have h2 : CN N l (fun i y => (1 / 4 : ℝ) • ∑ c, ∑ d, (D.Fr.ε c * D.Fr.ε d * ((z i).FJ y).G A c d) •
        ((D.Fr.c c * D.Fr.c d) (ψF i y)))
      (fun y => (1 / 4 : ℝ) • ∑ c, ∑ d, (D.Fr.ε c * D.Fr.ε d * (z₀.FJ y).G A c d) •
        ((D.Fr.c c * D.Fr.c d) (ψ₀ y))) := by
    refine (CN.sum Finset.univ fun c _ => CN.sum Finset.univ fun d _ => cn_smul
      ((cn_G h hK A c d).clm ((D.Fr.ε c * D.Fr.ε d) • ContinuousLinearMap.id ℝ ℝ))
      (hψN.clm (LinearMap.toContinuousLinearMap (D.Fr.c c * D.Fr.c d)))).clm
      ((1 / 4 : ℝ) • ContinuousLinearMap.id ℝ S₀) |>.congr
      (Eventually.of_forall fun i => funext fun y => ?_) (funext fun y => ?_) <;>
    · simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul,
        LinearMap.coe_toContinuousLinearMap']
  have h3 : CN N l (fun i y => ∑ μ, (z i).e y A μ • D.ρ ((z i).A y μ) (ψF i y))
      (fun y => ∑ μ, z₀.e y A μ • D.ρ (z₀.A y μ) (ψ₀ y)) :=
    CN.sum _ fun μ _ => cn_smul (cn_eAμ h hK A μ) ((cn_Aμ h μ).bilin hψN (toCLM₂ D.ρ))
  refine ((h1.add h2).add h3).congr (Eventually.of_forall fun i => funext fun y => ?_)
    (funext fun y => ?_) <;>
  · rw [ActualJetBridge.Xs_eq, ActualJetBridge.spinPart_apply_eq]
    rfl

theorem cn_X (h : TupleCN (N + 1) l z z₀) (hK : MetCompact z₀) :
    CN N l (fun i y => (((z i).jet y).state SM).X) (fun y => ((z₀.jet y).state SM).X) :=
  CN.pi fun a => cn_Xs SM.D h.ψ h hK a.succ

theorem cn_Xb (h : TupleCN (N + 1) l z z₀) (hK : MetCompact z₀) :
    CN N l (fun i y => (((z i).jet y).state SM).Xb) (fun y => ((z₀.jet y).state SM).Xb) :=
  CN.pi fun a => cn_Xs SM.Db h.ψb h hK a.succ

/-- **The actual-jet state fields converge in `C^N`.** -/
theorem stateF_CN (h : TupleCN (N + 1) l z z₀) (hK : MetCompact z₀) :
    CN N l (fun i => stateF SM (z i)) (stateF SM z₀) := by
  have c11 : CN N l (fun i y => (((z i).jet y).state SM).g) (fun y => ((z₀.jet y).state SM).g) :=
    h.g.mono (Nat.le_succ N)
  have c21 : CN N l (fun i y => (((z i).jet y).state SM).A) (fun y => ((z₀.jet y).state SM).A) :=
    CN.pi fun a => cn_Aμ h a.succ
  have c27 : CN N l (fun i y => (((z i).jet y).state SM).ψ)
      (fun y => ((z₀.jet y).state SM).ψ) := h.ψ.mono (Nat.le_succ N)
  have c29 : CN N l (fun i y => (((z i).jet y).state SM).ψb)
      (fun y => ((z₀.jet y).state SM).ψb) := h.ψb.mono (Nat.le_succ N)
  exact ((c11.prod ((cn_p SM h hK).prod (cn_q SM h hK))).prod
    (c21.prod ((cn_E SM h hK).prod ((cn_B SM h hK).prod ((cn_H SM h).prod
      ((cn_Pm SM h hK).prod ((cn_Q SM h hK).prod (c27.prod ((cn_X SM h hK).prod
        (c29.prod (cn_Xb SM h hK))))))))))).congr (Eventually.of_forall fun i => rfl) rfl

end State


/-! ### Initial and harmonic mismatches in the slab model -/

section Mismatch

variable (SM : SMData (MatLie m) V S S') {n : ℕ} (eX : (Fin n → ℝ) ≃L[ℝ] StateP m V S S')
variable {na nb : ℕ} (eY : (Fin na → ℝ) ≃L[ℝ] BosP m V) (eYD : (Fin nb → ℝ) ≃L[ℝ] S × S')

/-- **The initial `H^k` mismatch tends to zero** (`i_{h,k} → 0` of `eq:native-initial-gauge`)
under `C^{k+1}` convergence of the tuples. -/
theorem init_tendsto (hS : SMSmooth SM) {k : ℕ} {T : ℝ} (hT : 0 < T)
    (h : TupleCN (k + 1) l z z₀) (hK : MetCompact z₀) :
    Tendsto (fun i => ‖(slabModel SM eX eY eYD hS k T hT).init (z i) -
      (slabModel SM eX eY eYD hS k T hT).init z₀‖) l (𝓝 0) := by
  have hst := stateF_CN SM h hK
  have hU : ∀ a, CN k l (fun i => uC SM eX (z i) a) (uC SM eX z₀ a) := fun a =>
    (hst.clm (eX.symm : StateP m V S S' →L[ℝ] (Fin n → ℝ))).apply a
  have hE := tendsto_energyQ_of_CN (d := 3) hU 0
  have hs := (Real.continuous_sqrt.tendsto 0).comp hE
  rw [Real.sqrt_zero] at hs
  refine hs.congr fun i => ?_
  rw [norm_init_sub SM eX eY eYD hS k hT]
  rfl

/-- **The harmonic mismatch tends to zero** (`γ_{h,k} → 0` of `eq:native-initial-gauge`) under
`C^{k+3}` convergence of the tuples, when the reference is exact (in harmonic gauge) on the slab. -/
theorem harm_tendsto (hS : SMSmooth SM) {k : ℕ} {T : ℝ} (hT : 0 < T)
    (h : TupleCN (k + 3) l z z₀) (hK : MetCompact z₀) (hex : ExactOn SM T z₀) :
    Tendsto (fun i => (slabModel SM eX eY eYD hS k T hT).harm (z i)) l (𝓝 0) := by
  have hC : CN (k + 2) l (fun i => CF (z i)) (CF z₀) := CF_CN h hK
  have h1 : ∀ c, CN (k + 1) l (fun i => Cc (z i) c) (Cc z₀ c) := fun c =>
    (hC.mono (by omega)).apply c
  have h2 : ∀ c, CN k l (fun i => dtCc (z i) c) (dtCc z₀ c) := fun c =>
    ((hC.mono (by omega : k + 1 ≤ k + 2)).fderiv_apply (Pi.single 0 1)).apply c
  have z1 : ∀ c x, x 0 ∈ Icc 0 T → Cc z₀ c x = 0 := fun c x hx => by
    simp [Cc, (hex x hx).2.2]
  have z2 : ∀ c x, x 0 ∈ Icc 0 T → dtCc z₀ c x = 0 := fun c x hx => by
    simp [dtCc, pd_eq_zero_of_slab (contDiff_CF z₀) (fun y hy => (hex y hy).2.2) hx 0
      (Or.inr hT)]
  have t1 := (Real.continuous_sqrt.tendsto 0).comp (tendsto_l2Sq_of_CN h1 hT.le z1)
  have t2 := (Real.continuous_sqrt.tendsto 0).comp (tendsto_l2Sq_of_CN h2 hT.le z2)
  have := t1.add t2
  rw [Real.sqrt_zero, add_zero] at this
  exact this

end Mismatch


/-! ### Exact smooth solutions are regular references -/

section Ref

variable (SM : SMData (MatLie m) V S S') {n : ℕ} (eX : (Fin n → ℝ) ≃L[ℝ] StateP m V S S')

theorem continuous_uC_vec (z : Tuple m V S S') :
    Continuous (fun x : ST 3 => fun b => uC SM eX z b x) :=
  continuous_pi fun b => ((ContinuousLinearMap.proj b).comp
    (eX.symm : StateP m V S S' →L[ℝ] (Fin n → ℝ))).continuous.comp
      (contDiff_stateF SM z).continuous

/-- **Every exact smooth solution on the slab lies in a reference class** of
`prop:coupled-bootstrap`: its state coordinates on the slab lie in a compact subset of the chart
(spatial periodicity) and its `C_tH^{k+1}` energy is bounded on `[0, T]`. -/
theorem exists_refSet_of_exact {z₀ : Tuple m V S S'} {T : ℝ} (hex : ExactOn SM T z₀) (k : ℕ) :
    ∃ (K : Set (Fin n → ℝ)) (R₁ : ℝ), IsCompact K ∧ K ⊆ chartC eX ∧ 0 ≤ R₁ ∧
      z₀ ∈ refSet SM eX k T K R₁ := by
  set Q : Set (ST 3) := Set.pi univ (Fin.cons (Icc 0 T) (fun _ => Icc 0 1) : Fin 4 → Set ℝ)
    with hQ
  have hQc : IsCompact Q := isCompact_univ_pi fun i => by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact isCompact_Icc
    · exact isCompact_Icc
  set K : Set (Fin n → ℝ) := (fun x : ST 3 => fun b => uC SM eX z₀ b x) '' Q with hK
  have hKc : IsCompact K := hQc.image (continuous_uC_vec SM eX z₀)
  have hcont : ContinuousOn (fun t => energyQ (k + 1) (uC SM eX z₀) t) (Icc 0 T) := by
    refine Continuous.continuousOn ?_
    unfold energyQ
    exact continuous_finset_sum _ fun b _ => continuous_Q (k + 1)
      (((ContinuousLinearMap.proj b).comp
        (eX.symm : StateP m V S S' →L[ℝ] (Fin n → ℝ))).contDiff.comp (contDiff_stateF SM z₀))
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨K, Real.sqrt (max B 0), hKc, ?_, Real.sqrt_nonneg _, hex, fun x hx => ?_,
    fun t ht => ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact uC_mem_chart SM eX z₀ x
  · set kk : Fin 3 → ℤ := fun i => ⌊x i.succ⌋ with hkk
    set x' : ST 3 := x - sshift kk with hx'
    have hx'Q : x' ∈ Q := by
      intro i _
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa [hx', sshift] using hx
      · simp only [hx', Pi.sub_apply, sshift, Fin.cons_succ, zvec, Fin.cons_succ]
        constructor
        · linarith [Int.floor_le (x j.succ)]
        · linarith [Int.lt_floor_add_one (x j.succ)]
    refine ⟨x', hx'Q, funext fun b => ?_⟩
    have := isSPeriodic_uC SM eX z₀ b kk x'
    rw [show x' + sshift kk = x by simp [hx']] at this
    exact this.symm
  · have h1 := hB t ht
    rw [Real.sq_sqrt (le_max_right _ _)]
    exact (le_abs_self _).trans (h1.trans (le_max_left _ _))

end Ref


end RenewalGeometry.StateConv

end
