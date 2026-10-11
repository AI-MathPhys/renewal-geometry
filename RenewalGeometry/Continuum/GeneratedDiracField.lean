/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.GeneratedDiracEuler
import RenewalGeometry.Continuum.GeneratedMatterEuler

/-!
# The first variation of the Dirac density along a smooth tuple

Einstein–Standard-Model action-closure manuscript, `eq:dirac-density`, `app:generated-dynamics`
("integration by parts expresses `D S^{cmp}` through the physical rows").

Field-level calculus for a smooth tuple `z` and a smooth metric variation `k`:

* `deR_fderiv`, `edot_fderiv`, `dedot_eq` — the frame jets as derivatives of the analytic map
  `g ↦ frU(g⁻¹)`; **`line_edot`** — the coordinate derivative of the frame variation field
  `y ↦ ė(g(y))[k(y)]` is the jet-line variation `dedot` of the frame jets (symmetry of second
  derivatives);
* **`pd_Lam`** — the coordinate derivatives of the frame-variation field `Λ(y)` are the jets `dLg`;
* `frGR`, `divE_eq_divEf` — the tuple's frame connection is `GR` of its metric 1-jet;
* **`div_frame`** — `Σ_γ ∂_γ(ϱ e_C{}^γ F) = ϱ(div(e_C)F + e_C(F))`.
-/

open Finset Set Filter Topology
open scoped ContDiff

noncomputable section

namespace RenewalGeometry.GenDFld

open SobolevOpen (pd)
open HarmonicDefect EHJetVariation EHFieldVariation ActualJetSystem ActualJetRecon ActualJetSmooth
  ActualJetGauge ActualJetWriter ActualJetBridge ActualJetState GenMatVar GenFOAction FrameCurvature
  ActualJetFrame GenResMaps JetCurve GenDAlg GenDFJ GenDStress GenDiracCur SpinorProlongation
  GenDAct GenDEul GenNoether GenMatEuler PeriodicCube SlabWaveHk

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024

/-! ### The frame jets as derivatives of an analytic map -/

section Analytic

/-- The frame component `g ↦ frU(g⁻¹)_A{}^μ` as a function of the metric. -/
def Ffr (A μ : Fin 4) (g : Met) : ℝ := frR g A μ

theorem contDiffAt_Ffr {g : Met} (hdet : (Matrix.of g).det ≠ 0) (hc : IsLorChart (ginvOf g))
    (A μ : Fin 4) : ContDiffAt ℝ ω (Ffr A μ) g := by
  have hgi : ContDiffAt ℝ ω (fun g' : Met => ginvOf g') g :=
    ContDiffAt.ginvOf_fun contDiffAt_id hdet
  exact (contDiffAt_frU hc A μ).comp g hgi

theorem deR_fderiv {g : Met} (hg : ChartM g) (dgf : Fin 4 → Met) (δ A μ : Fin 4) :
    deR g dgf δ A μ = fderiv ℝ (Ffr A μ) g (dgf δ) := by
  have h1 := hasDerivAt_frR_line hg dgf δ A μ
  have hd : DifferentiableAt ℝ (Ffr A μ) g :=
    (contDiffAt_Ffr hg.1 hg.2.1 A μ).differentiableAt (by simp)
  have hl : HasDerivAt (fun s : ℝ => g + s • dgf δ) (dgf δ) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (dgf δ)).const_add g
  have h2 := hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  exact h1.unique h2

theorem edot_fderiv {g : Met} (hg : ChartM g) (k : Met) (A μ : Fin 4) :
    edot g k A μ = fderiv ℝ (Ffr A μ) g k :=
  deR_fderiv hg (fun _ => k) 0 A μ

/-- **The jet-line variation of the frame jets** is a mixed second derivative:
`dedot = D²F(g)[k, ∂_γg] + DF(g)[∂_γk]`. -/
theorem dedot_eq {g : Met} (hg : ChartM g) (dg : Fin 4 → Met) (k : Met)
    (hk : ∀ μ ν, k μ ν = k ν μ) (dk : Fin 4 → Met) (γ A μ : Fin 4) :
    dedot g dg k dk γ A μ =
      fderiv ℝ (fderiv ℝ (Ffr A μ)) g k (dg γ) + fderiv ℝ (Ffr A μ) g (dk γ) := by
  have hF := contDiffAt_Ffr hg.1 hg.2.1 A μ
  have hF' : DifferentiableAt ℝ (fderiv ℝ (Ffr A μ)) g :=
    ((hF.fderiv_right (m := ω) le_rfl).differentiableAt (by simp))
  have hl : HasDerivAt (fun s : ℝ => g + s • k) k 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const k).const_add g
  have h1 : HasDerivAt (fun s : ℝ => fderiv ℝ (Ffr A μ) (g + s • k)) (fderiv ℝ (fderiv ℝ (Ffr A μ)) g k) 0 :=
    hF'.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hl (by simp)
  have hw : HasDerivAt (fun s : ℝ => dg γ + s • dk γ) (dk γ) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (dk γ)).const_add (dg γ)
  have h2 := h1.clm_apply hw
  simp only [zero_smul, add_zero] at h2
  have hev : (fun ε : ℝ => deR (g + ε • k) (dg + ε • dk) γ A μ) =ᶠ[𝓝 0]
      fun ε => fderiv ℝ (Ffr A μ) (g + ε • k) (dg γ + ε • dk γ) := by
    filter_upwards [eventually_chartM hg hk] with ε hε
    rw [deR_fderiv hε]
    rfl
  exact (hasDerivAt_dedot hg dg k dk γ A μ).unique (h2.congr_of_eventuallyEq hev)

end Analytic

/-! ### Tuples -/

section TupleCalc

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable (z : Tuple m V S S')

theorem chartM_tuple (y : ST 3) : ChartM (z.g y) := ⟨z.det_ne y, z.lor y, z.g_symm y⟩

/-- **The coordinate derivative of the frame-variation field is the jet-line variation of the
frame jets** (symmetry of the second derivative of the analytic map `g ↦ frU(g⁻¹)`). -/
theorem line_edot {k : ST 3 → Met} (hk : ContDiff ℝ ∞ k) (hks : ∀ y μ ν, k y μ ν = k y ν μ)
    (x : ST 3) (γ A μ : Fin 4) :
    HasDerivAt (fun s : ℝ => edot (z.g (x + s • ev γ)) (k (x + s • ev γ)) A μ)
      (dedot (z.g x) (z.dg x) (k x) (fun α => pd k α x) γ A μ) 0 := by
  have hF := contDiffAt_Ffr (z.det_ne x) (z.lor x) A μ
  have hF' : DifferentiableAt ℝ (fderiv ℝ (Ffr A μ)) (z.g x) :=
    ((hF.fderiv_right (m := ω) le_rfl).differentiableAt (by simp))
  have hG := hasDerivAt_line0 (z.g_smooth.differentiable (by simp) x) γ
  have hK := hasDerivAt_line0 (hk.differentiable (by simp) x) γ
  have h0 : x + (0 : ℝ) • ev γ = x := by simp
  have h1 : HasDerivAt (fun s : ℝ => fderiv ℝ (Ffr A μ) (z.g (x + s • ev γ)))
      (fderiv ℝ (fderiv ℝ (Ffr A μ)) (z.g x) (pd z.g γ x)) 0 :=
    hF'.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hG (by rw [h0])
  have h2 := h1.clm_apply hK
  simp only [h0] at h2
  have hfun : (fun s : ℝ => edot (z.g (x + s • ev γ)) (k (x + s • ev γ)) A μ) =
      fun s => fderiv ℝ (Ffr A μ) (z.g (x + s • ev γ)) (k (x + s • ev γ)) := by
    funext s; exact edot_fderiv (chartM_tuple z _) _ A μ
  rw [hfun, dedot_eq (chartM_tuple z x) (z.dg x) (k x) (hks x) _ γ A μ]
  have hsym := hF.isSymmSndFDerivAt_of_omega (pd z.g γ x) (k x)
  refine h2.congr_deriv ?_
  rw [hsym]
  rfl

/-- **The coordinate derivatives of the frame-variation field** `Λ_{AC}(y) = g(ė_A, e_C)(y)` are
the jets `dLg`. -/
theorem line_Lam {k : ST 3 → Met} (hk : ContDiff ℝ ∞ k) (hks : ∀ y μ ν, k y μ ν = k y ν μ)
    (x : ST 3) (γ A C : Fin 4) :
    HasDerivAt (fun s : ℝ => Lam (z.g (x + s • ev γ)) (k (x + s • ev γ)) A C)
      (dLg (z.g x) (z.dg x) (k x) (fun α => pd k α x) γ A C) 0 := by
  unfold Lam dLg
  have h0 : x + (0 : ℝ) • ev γ = x := by simp
  have h := hasDerivAt_ipg (g := fun s : ℝ => z.g (x + s • ev γ))
    (X := fun s => edot (z.g (x + s • ev γ)) (k (x + s • ev γ)) A)
    (Y := fun s => frR (z.g (x + s • ev γ)) C) (t := 0) (dg := z.dg x)
    (dX := fun γ' μ => dedot (z.g x) (z.dg x) (k x) (fun α => pd k α x) γ' A μ)
    (dY := fun γ' μ => deR (z.g x) (z.dg x) γ' C μ) γ (fun μ ν => by
      simpa using z.line_g x γ μ ν) (fun μ => by simpa using line_edot z hk hks x γ A μ)
    (fun ν => z.line_e x γ C ν)
  simp only [h0] at h
  exact h

/-- The tuple's frame connection coefficients are `GR` of its metric 1-jet. -/
theorem FJ_G_eq (x : ST 3) : (z.FJ x).G = GR (z.g x) (z.dg x) := rfl

theorem divE_eq_divEf (x : ST 3) (C : Fin 4) : divE z x C = divEf (GR (z.g x) (z.dg x)) C := by
  rw [divE_eq_frame, FJ_G_eq]
  rfl

/-- **The frame divergence**: `Σ_γ ∂_γ(ϱ e_C{}^γ F) = ϱ(div(e_C)F + e_C(F))`. -/
theorem div_frame {F : ST 3 → ℝ} (hF : ContDiff ℝ ∞ F) (x : ST 3) (C : Fin 4) :
    ∑ γ, pd (fun y => rho z y * (z.e y C γ * F y)) γ x =
      rho z x * (divE z x C * F x + ∑ γ, z.e x C γ * pd F γ x) := by
  have h0 : ∀ γ : Fin 4, x + (0 : ℝ) • ev γ = x := fun γ => by simp
  have hpt : ∀ γ, pd (fun y => rho z y * (z.e y C γ * F y)) γ x =
      rho z x * (∑ k, chr (z.gi x) (z.dg x) k k γ) * (z.e x C γ * F x) +
        rho z x * (z.de x γ C γ * F x + z.e x C γ * pd F γ x) := by
    intro γ
    have hd : DifferentiableAt ℝ (fun y => rho z y * (z.e y C γ * F y)) x :=
      ((contDiff_rho z).mul ((z.contDiff_e C γ).mul hF)).differentiable (by simp) x
    refine pd_eq_of_line hd ?_
    have h1 := line_rho z x γ
    have h2 := z.line_e x γ C γ
    have h3 := hasDerivAt_line0 (hF.differentiable (by simp) x) γ
    have h := h1.fun_mul (h2.fun_mul h3)
    simp only [h0] at h
    exact h
  simp only [hpt]
  have hs := sum_coef_divE z x C
  have e : ∑ γ, (rho z x * (∑ k, chr (z.gi x) (z.dg x) k k γ) * (z.e x C γ * F x) +
      rho z x * (z.de x γ C γ * F x + z.e x C γ * pd F γ x)) =
      F x * ∑ ν, (rho z x * (∑ k, chr (z.gi x) (z.dg x) k k ν) * z.e x C ν + rho z x * z.de x ν C ν) +
        rho z x * ∑ γ, z.e x C γ * pd F γ x := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun γ _ => by ring
  rw [e, hs]
  ring

end TupleCalc

/-! ### The spin flux in expanded form -/

section Flux

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable {SM : SMData (MatLie m) V S S'} (hP : DiracPairing SM)

/-- The spin flux `Fl_C` in expanded form,
`-⅛ε_C Σ_{a,b} ε_aε_bM_{ab}⟨Ψ̄, (c_Cc_ac_b + c_ac_bc_C)Ψ⟩`. -/
def Flx (C : Fin 4) (M : Fin 4 → Fin 4 → ℝ) (ψ : S) (ψb : S') : ℝ :=
  -(1 / 8 : ℝ) * lorentzSign C * ∑ a, ∑ b, lorentzSign a * lorentzSign b * M a b *
    hP.P ψb ((SM.D.Fr.c C * SM.D.Fr.c a * SM.D.Fr.c b + SM.D.Fr.c a * SM.D.Fr.c b * SM.D.Fr.c C) ψ)

theorem lorFl_eq_Flx {M : Fin 4 → Fin 4 → ℝ} (hM : ∀ a b, M b a = -M a b) (ψ : S) (ψb : S')
    (C : Fin 4) : lorFl hP M ψ ψb C = Flx hP C M ψ ψb := by
  unfold lorFl Flx
  simp only [LinearMap.neg_apply, map_neg, LinearMap.neg_apply]
  rw [hP.P_spin M (fun c d => hM c d)]
  unfold spinPart
  rw [eps_D_eq]
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum, smul_eq_mul,
    Module.End.mul_apply, LinearMap.add_apply, map_add, Finset.mul_sum]
  rw [sub_neg_eq_add, ← neg_add, ← Finset.sum_add_distrib, ← Finset.sum_neg_distrib,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib, ← Finset.sum_neg_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

theorem lorFlD_eq_Flx {M : Fin 4 → Fin 4 → ℝ} (hM : ∀ a b, M b a = -M a b)
    {dM : Fin 4 → Fin 4 → Fin 4 → ℝ} (hdM : ∀ C a b, dM C b a = -dM C a b) (ψ : S)
    (Dψ : Fin 4 → S) (ψb : S') (Dψb : Fin 4 → S') (C : Fin 4) :
    lorFlD hP M dM ψ Dψ ψb Dψb C =
      Flx hP C (dM C) ψ ψb + Flx hP C M (Dψ C) ψb + Flx hP C M ψ (Dψb C) := by
  have e : lorFlD hP M dM ψ Dψ ψb Dψb C = lorFl hP (dM C) ψ ψb C + lorFl hP M (Dψ C) ψb C +
      lorFl hP M ψ (Dψb C) C := by
    unfold lorFlD lorFl
    ring
  rw [e, lorFl_eq_Flx hP (hdM C), lorFl_eq_Flx hP hM, lorFl_eq_Flx hP hM]

/-- The product rule for the expanded spin flux along curves. -/
theorem hasDerivAt_Flx (C : Fin 4) {M : ℝ → Fin 4 → Fin 4 → ℝ} {ψ : ℝ → S} {ψb : ℝ → S'}
    {M' : Fin 4 → Fin 4 → ℝ} {ψ' : S} {ψb' : S'}
    (hM : ∀ a b, HasDerivAt (fun s => M s a b) (M' a b) 0) (hψ : HasDerivAt ψ ψ' 0)
    (hψb : HasDerivAt ψb ψb' 0) :
    HasDerivAt (fun s => Flx hP C (M s) (ψ s) (ψb s))
      (Flx hP C M' (ψ 0) (ψb 0) + Flx hP C (M 0) ψ' (ψb 0) + Flx hP C (M 0) (ψ 0) ψb') 0 := by
  unfold Flx
  have hterm : ∀ a b, HasDerivAt (fun s => lorentzSign a * lorentzSign b * M s a b *
      hP.P (ψb s) ((SM.D.Fr.c C * SM.D.Fr.c a * SM.D.Fr.c b +
        SM.D.Fr.c a * SM.D.Fr.c b * SM.D.Fr.c C) (ψ s)))
      (lorentzSign a * lorentzSign b * M' a b *
        hP.P (ψb 0) ((SM.D.Fr.c C * SM.D.Fr.c a * SM.D.Fr.c b +
          SM.D.Fr.c a * SM.D.Fr.c b * SM.D.Fr.c C) (ψ 0)) +
       lorentzSign a * lorentzSign b * M 0 a b *
        (hP.P ψb' ((SM.D.Fr.c C * SM.D.Fr.c a * SM.D.Fr.c b +
          SM.D.Fr.c a * SM.D.Fr.c b * SM.D.Fr.c C) (ψ 0)) +
         hP.P (ψb 0) ((SM.D.Fr.c C * SM.D.Fr.c a * SM.D.Fr.c b +
          SM.D.Fr.c a * SM.D.Fr.c b * SM.D.Fr.c C) ψ'))) 0 := by
    intro a b
    have h1 := (hM a b).const_mul (lorentzSign a * lorentzSign b)
    have h2 := hasDerivAt_bilin hP.P hψb (hasDerivAt_lin (SM.D.Fr.c C * SM.D.Fr.c a * SM.D.Fr.c b +
      SM.D.Fr.c a * SM.D.Fr.c b * SM.D.Fr.c C) hψ)
    exact (h1.fun_mul h2).congr_deriv (by ring)
  refine ((HasDerivAt.fun_sum (u := Finset.univ) fun a _ =>
    HasDerivAt.fun_sum (u := Finset.univ) fun b _ => hterm a b).const_mul
    (-(1 / 8 : ℝ) * lorentzSign C)).congr_deriv ?_
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem Flx_sum_M (C : Fin 4) (f : Fin 4 → ℝ) (Mγ : Fin 4 → Fin 4 → Fin 4 → ℝ) (ψ : S)
    (ψb : S') : ∑ γ, f γ * Flx hP C (Mγ γ) ψ ψb = Flx hP C (fun a b => ∑ γ, f γ * Mγ γ a b) ψ ψb := by
  unfold Flx
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun γ _ => ?_
  ring

theorem Flx_sum_psi (C : Fin 4) (f : Fin 4 → ℝ) (M : Fin 4 → Fin 4 → ℝ) (v : Fin 4 → S)
    (ψb : S') : ∑ γ, f γ * Flx hP C M (v γ) ψb = Flx hP C M (∑ γ, f γ • v γ) ψb := by
  unfold Flx
  simp only [map_sum, map_smul, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun γ _ => ?_
  ring

theorem Flx_sum_psib (C : Fin 4) (f : Fin 4 → ℝ) (M : Fin 4 → Fin 4 → ℝ) (ψ : S)
    (v : Fin 4 → S') : ∑ γ, f γ * Flx hP C M ψ (v γ) = Flx hP C M ψ (∑ γ, f γ • v γ) := by
  unfold Flx
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun γ _ => ?_
  ring

end Flux

/-! ### The first variation along a tuple -/

section Field

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable {SM : SMData (MatLie m) V S S'} (hP : DiracPairing SM) (z : Tuple m V S S')

/-- The extended head 1-jet of a tuple. -/
def jC (x : ST 3) : HJ1C m V S S' :=
  (j1F z.g z.A z.H x, ((z.ψ x, fun γ => pd z.ψ γ x), (z.ψb x, fun γ => pd z.ψb γ x)))

/-- The extended 1-jet of a variation `(k, X, η, φ, φ̄)`. -/
def jW (k : ST 3 → Met) (X : ST 3 → Fin 4 → MatLie m) (η : ST 3 → V) (φ : ST 3 → S)
    (φb : ST 3 → S') (x : ST 3) : HJ1C m V S S' :=
  (j1F k X η x, ((φ x, fun γ => pd φ γ x), (φb x, fun γ => pd φb γ x)))

/-- The local Lorentz part `M = ½(Λ - Λᵀ)` of the frame variation induced by `k`, along the
tuple. -/
def Mf (k : ST 3 → Met) (y : ST 3) (A B : Fin 4) : ℝ :=
  (1 / 2 : ℝ) * (Lam (z.g y) (k y) A B - Lam (z.g y) (k y) B A)

theorem Mf_anti (k : ST 3 → Met) (y : ST 3) (A B : Fin 4) : Mf z k y B A = -Mf z k y A B := by
  unfold Mf; ring

theorem contDiff_Lam {k : ST 3 → Met} (hk : ContDiff ℝ ∞ k) (A B : Fin 4) :
    ContDiff ℝ ∞ (fun y => Lam (z.g y) (k y) A B) := by
  refine contDiff_iff_contDiffAt.2 fun y₀ => ?_
  have hdet := z.det_ne y₀
  have hlor : IsLorChart (ginvOf (z.g y₀)) := z.lor y₀
  have hg := z.g_smooth.contDiffAt (x := y₀)
  have hk' := hk.contDiffAt (x := y₀)
  have hgi : ContDiffAt ℝ ∞ (fun y => ginvOf (z.g y)) y₀ := ContDiffAt.ginvOf_fun hg hdet
  have hgij : ∀ a b, ContDiffAt ℝ ∞ (fun y => z.g y a b) y₀ := fun a b => by fun_prop
  have hkij : ∀ a b, ContDiffAt ℝ ∞ (fun y => k y a b) y₀ := fun a b => by fun_prop
  have hgi' : ∀ a b, ContDiffAt ℝ ∞ (fun y => ginvOf (z.g y) a b) y₀ := fun a b =>
    contDiffAt_pi.1 (contDiffAt_pi.1 hgi a) b
  have hdgi : ContDiffAt ℝ ∞ (fun y => fun (γ l σ : Fin 4) =>
      dginv (ginvOf (z.g y)) (fun _ => k y) γ l σ) y₀ := by
    unfold dginv
    rw [contDiffAt_pi]; intro γ; rw [contDiffAt_pi]; intro l; rw [contDiffAt_pi]; intro σ
    fun_prop
  have hed : ∀ a μ, ContDiffAt ℝ ∞ (fun y => edot (z.g y) (k y) a μ) y₀ := fun a μ =>
    ContDiffAt.frameJet hgi hdgi hlor 0 a μ
  have hfr : ∀ a μ, ContDiffAt ℝ ∞ (fun y => frR (z.g y) a μ) y₀ := fun a μ =>
    ContDiffAt.frU_comp hgi hlor a μ
  unfold Lam ipg
  fun_prop

theorem pd_sum' {ι : Type*} (s : Finset ι) {f : ι → ST 3 → ℝ} {x : ST 3}
    (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) x) (γ : Fin 4) :
    pd (fun y => ∑ i ∈ s, f i y) γ x = ∑ i ∈ s, pd (f i) γ x := by
  unfold SobolevOpen.pd
  rw [fderiv_fun_sum hf]
  simp

theorem contDiff_Mf {k : ST 3 → Met} (hk : ContDiff ℝ ∞ k) (a b : Fin 4) :
    ContDiff ℝ ∞ (fun y => Mf z k y a b) := by
  unfold Mf
  exact contDiff_const.mul ((contDiff_Lam z hk a b).sub (contDiff_Lam z hk b a))

theorem contDiff_Flx {k : ST 3 → Met} (hk : ContDiff ℝ ∞ k) (C : Fin 4) :
    ContDiff ℝ ∞ (fun y => Flx hP C (Mf z k y) (z.ψ y) (z.ψb y)) := by
  refine contDiff_iff_contDiffAt.2 fun y₀ => ?_
  have hM : ∀ a b, ContDiffAt ℝ ∞ (fun y => Mf z k y a b) y₀ := fun a b =>
    (contDiff_Mf z hk a b).contDiffAt
  have hψ := z.ψ_smooth.contDiffAt (x := y₀)
  have hψb := z.ψb_smooth.contDiffAt (x := y₀)
  unfold Flx
  fun_prop

theorem line_Mf {k : ST 3 → Met} (hk : ContDiff ℝ ∞ k) (hks : ∀ y μ ν, k y μ ν = k y ν μ)
    (x : ST 3) (γ a b : Fin 4) :
    HasDerivAt (fun s : ℝ => Mf z k (x + s • ev γ) a b)
      ((1 / 2 : ℝ) * (dLg (z.g x) (z.dg x) (k x) (fun α => pd k α x) γ a b -
        dLg (z.g x) (z.dg x) (k x) (fun α => pd k α x) γ b a)) 0 := by
  unfold Mf
  exact ((line_Lam z hk hks x γ a b).sub (line_Lam z hk hks x γ b a)).const_mul _

/-- **The frame derivative of the spin flux along the tuple** `e_C(Fl_C)`. -/
theorem frameD_Flx {k : ST 3 → Met} (hk : ContDiff ℝ ∞ k) (hks : ∀ y μ ν, k y μ ν = k y ν μ)
    (x : ST 3) (C : Fin 4) :
    ∑ γ, z.e x C γ * pd (fun y => Flx hP C (Mf z k y) (z.ψ y) (z.ψb y)) γ x =
      Flx hP C (fun a b => (1 / 2 : ℝ) * (dLam (z.g x) (z.dg x) (k x) (fun α => pd k α x) C a b -
          dLam (z.g x) (z.dg x) (k x) (fun α => pd k α x) C b a)) (z.ψ x) (z.ψb x) +
        Flx hP C (Mf z k x) (dψR (z.g x) (fun γ => pd z.ψ γ x) C) (z.ψb x) +
        Flx hP C (Mf z k x) (z.ψ x) (dψR (z.g x) (fun γ => pd z.ψb γ x) C) := by
  have h0 : ∀ γ : Fin 4, x + (0 : ℝ) • ev γ = x := fun γ => by simp
  have hpd : ∀ γ, pd (fun y => Flx hP C (Mf z k y) (z.ψ y) (z.ψb y)) γ x =
      Flx hP C (fun a b => (1 / 2 : ℝ) * (dLg (z.g x) (z.dg x) (k x) (fun α => pd k α x) γ a b -
          dLg (z.g x) (z.dg x) (k x) (fun α => pd k α x) γ b a)) (z.ψ x) (z.ψb x) +
        Flx hP C (Mf z k x) (pd z.ψ γ x) (z.ψb x) + Flx hP C (Mf z k x) (z.ψ x) (pd z.ψb γ x) := by
    intro γ
    refine pd_eq_of_line ((contDiff_Flx hP z hk C).differentiable (by simp) x) ?_
    have h := hasDerivAt_Flx hP C (M := fun s => Mf z k (x + s • ev γ))
      (ψ := fun s => z.ψ (x + s • ev γ)) (ψb := fun s => z.ψb (x + s • ev γ))
      (fun a b => line_Mf z hk hks x γ a b)
      (hasDerivAt_line0 (z.ψ_smooth.differentiable (by simp) x) γ)
      (hasDerivAt_line0 (z.ψb_smooth.differentiable (by simp) x) γ)
    simp only [h0] at h
    exact h
  simp only [hpd, mul_add, Finset.sum_add_distrib]
  rw [Flx_sum_M, Flx_sum_psi, Flx_sum_psib]
  have hM : (fun a b => ∑ γ, z.e x C γ * ((1 / 2 : ℝ) *
      (dLg (z.g x) (z.dg x) (k x) (fun α => pd k α x) γ a b -
        dLg (z.g x) (z.dg x) (k x) (fun α => pd k α x) γ b a))) =
      fun a b => (1 / 2 : ℝ) * (dLam (z.g x) (z.dg x) (k x) (fun α => pd k α x) C a b -
        dLam (z.g x) (z.dg x) (k x) (fun α => pd k α x) C b a) := by
    funext a b
    unfold dLam dLg
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun γ _ => ?_
    show z.e x C γ * _ = _
    rw [show z.e x C γ = frR (z.g x) C γ from rfl]
    ring
  rw [hM]
  rfl

/-- The spinor flux `f_C = ½ε_C⟨Ψ̄, c_Cφ⟩`. -/
def fPs (φ : ST 3 → S) (C : Fin 4) (y : ST 3) : ℝ :=
  (1 / 2 : ℝ) * lorentzSign C * hP.P (z.ψb y) (SM.D.Fr.c C (φ y))

/-- The co-spinor flux `f̄_C = ½ε_C⟨φ̄, c_CΨ⟩`. -/
def fPb (φb : ST 3 → S') (C : Fin 4) (y : ST 3) : ℝ :=
  (1 / 2 : ℝ) * lorentzSign C * hP.P (φb y) (SM.D.Fr.c C (z.ψ y))

theorem contDiff_fPs {φ : ST 3 → S} (hφ : ContDiff ℝ ∞ φ) (C : Fin 4) :
    ContDiff ℝ ∞ (fPs hP z φ C) := by
  refine contDiff_iff_contDiffAt.2 fun y₀ => ?_
  have h1 := z.ψb_smooth.contDiffAt (x := y₀)
  have h2 := hφ.contDiffAt (x := y₀)
  unfold fPs
  fun_prop

theorem contDiff_fPb {φb : ST 3 → S'} (hφb : ContDiff ℝ ∞ φb) (C : Fin 4) :
    ContDiff ℝ ∞ (fPb hP z φb C) := by
  refine contDiff_iff_contDiffAt.2 fun y₀ => ?_
  have h1 := z.ψ_smooth.contDiffAt (x := y₀)
  have h2 := hφb.contDiffAt (x := y₀)
  unfold fPb
  fun_prop

theorem frameD_fPs {φ : ST 3 → S} (hφ : ContDiff ℝ ∞ φ) (x : ST 3) (C : Fin 4) :
    ∑ γ, z.e x C γ * pd (fPs hP z φ C) γ x =
      (1 / 2 : ℝ) * lorentzSign C * (hP.P (dψR (z.g x) (fun γ => pd z.ψb γ x) C) (SM.D.Fr.c C (φ x)) +
        hP.P (z.ψb x) (SM.D.Fr.c C (dψR (z.g x) (fun γ => pd φ γ x) C))) := by
  have h0 : ∀ γ : Fin 4, x + (0 : ℝ) • ev γ = x := fun γ => by simp
  have hpd : ∀ γ, pd (fPs hP z φ C) γ x = (1 / 2 : ℝ) * lorentzSign C *
      (hP.P (pd z.ψb γ x) (SM.D.Fr.c C (φ x)) + hP.P (z.ψb x) (SM.D.Fr.c C (pd φ γ x))) := by
    intro γ
    refine pd_eq_of_line ((contDiff_fPs hP z hφ C).differentiable (by simp) x) ?_
    have h := (hasDerivAt_bilin hP.P (hasDerivAt_line0 (z.ψb_smooth.differentiable (by simp) x) γ)
      (hasDerivAt_lin (SM.D.Fr.c C) (hasDerivAt_line0 (hφ.differentiable (by simp) x) γ))).const_mul
        ((1 / 2 : ℝ) * lorentzSign C)
    simp only [h0] at h
    exact h
  simp only [hpd]
  unfold dψR
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [show z.e x C γ = frR (z.g x) C γ from rfl]
  ring

theorem frameD_fPb {φb : ST 3 → S'} (hφb : ContDiff ℝ ∞ φb) (x : ST 3) (C : Fin 4) :
    ∑ γ, z.e x C γ * pd (fPb hP z φb C) γ x =
      (1 / 2 : ℝ) * lorentzSign C * (hP.P (dψR (z.g x) (fun γ => pd φb γ x) C) (SM.D.Fr.c C (z.ψ x)) +
        hP.P (φb x) (SM.D.Fr.c C (dψR (z.g x) (fun γ => pd z.ψ γ x) C))) := by
  have h0 : ∀ γ : Fin 4, x + (0 : ℝ) • ev γ = x := fun γ => by simp
  have hpd : ∀ γ, pd (fPb hP z φb C) γ x = (1 / 2 : ℝ) * lorentzSign C *
      (hP.P (pd φb γ x) (SM.D.Fr.c C (z.ψ x)) + hP.P (φb x) (SM.D.Fr.c C (pd z.ψ γ x))) := by
    intro γ
    refine pd_eq_of_line ((contDiff_fPb hP z hφb C).differentiable (by simp) x) ?_
    have h := (hasDerivAt_bilin hP.P (hasDerivAt_line0 (hφb.differentiable (by simp) x) γ)
      (hasDerivAt_lin (SM.D.Fr.c C) (hasDerivAt_line0 (z.ψ_smooth.differentiable (by simp) x) γ))).const_mul
        ((1 / 2 : ℝ) * lorentzSign C)
    simp only [h0] at h
    exact h
  simp only [hpd]
  unfold dψR
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [show z.e x C γ = frR (z.g x) C γ from rfl]
  ring

/-- The combined Dirac flux density `F_C = Fl_C - f_C + f̄_C`. -/
def FsD (k : ST 3 → Met) (φ : ST 3 → S) (φb : ST 3 → S') (C : Fin 4) (y : ST 3) : ℝ :=
  Flx hP C (Mf z k y) (z.ψ y) (z.ψb y) - fPs hP z φ C y + fPb hP z φb C y

/-- **The Dirac flux** `B^γ = ϱΣ_C e_C{}^γF_C`. -/
def fluxD (k : ST 3 → Met) (φ : ST 3 → S) (φb : ST 3 → S') (γ : Fin 4) (y : ST 3) : ℝ :=
  ∑ C, rho z y * (z.e y C γ * FsD hP z k φ φb C y)

theorem contDiff_FsD {k : ST 3 → Met} (hk : ContDiff ℝ ∞ k) {φ : ST 3 → S} (hφ : ContDiff ℝ ∞ φ)
    {φb : ST 3 → S'} (hφb : ContDiff ℝ ∞ φb) (C : Fin 4) : ContDiff ℝ ∞ (FsD hP z k φ φb C) :=
  ((contDiff_Flx hP z hk C).sub (contDiff_fPs hP z hφ C)).add (contDiff_fPb hP z hφb C)

theorem contDiff_fluxD {k : ST 3 → Met} (hk : ContDiff ℝ ∞ k) {φ : ST 3 → S}
    (hφ : ContDiff ℝ ∞ φ) {φb : ST 3 → S'} (hφb : ContDiff ℝ ∞ φb) (γ : Fin 4) :
    ContDiff ℝ ∞ (fluxD hP z k φ φb γ) := by
  unfold fluxD
  exact ContDiff.sum fun C _ => (contDiff_rho z).mul ((z.contDiff_e C γ).mul
    (contDiff_FsD hP z hk hφ hφb C))

theorem isSPeriodic_fluxD_aux {f : ST 3 → ℝ} (hf : SymHypEnergy.IsSPeriodic f) :
    SymHypEnergy.IsSPeriodic f := hf

/-- **The divergence of the Dirac flux**. -/
theorem div_fluxD {k : ST 3 → Met} (hk : ContDiff ℝ ∞ k) (hks : ∀ y μ ν, k y μ ν = k y ν μ)
    {φ : ST 3 → S} (hφ : ContDiff ℝ ∞ φ) {φb : ST 3 → S'} (hφb : ContDiff ℝ ∞ φb) (x : ST 3) :
    ∑ γ, pd (fluxD hP z k φ φb γ) γ x = ∑ C, rho z x * (divE z x C * FsD hP z k φ φb C x +
      ((Flx hP C (fun a b => (1 / 2 : ℝ) * (dLam (z.g x) (z.dg x) (k x) (fun α => pd k α x) C a b -
          dLam (z.g x) (z.dg x) (k x) (fun α => pd k α x) C b a)) (z.ψ x) (z.ψb x) +
        Flx hP C (Mf z k x) (dψR (z.g x) (fun γ => pd z.ψ γ x) C) (z.ψb x) +
        Flx hP C (Mf z k x) (z.ψ x) (dψR (z.g x) (fun γ => pd z.ψb γ x) C)) -
      (1 / 2 : ℝ) * lorentzSign C * (hP.P (dψR (z.g x) (fun γ => pd z.ψb γ x) C) (SM.D.Fr.c C (φ x)) +
        hP.P (z.ψb x) (SM.D.Fr.c C (dψR (z.g x) (fun γ => pd φ γ x) C))) +
      (1 / 2 : ℝ) * lorentzSign C * (hP.P (dψR (z.g x) (fun γ => pd φb γ x) C) (SM.D.Fr.c C (z.ψ x)) +
        hP.P (φb x) (SM.D.Fr.c C (dψR (z.g x) (fun γ => pd z.ψ γ x) C))))) := by
  have hterm : ∀ C γ, ContDiff ℝ ∞ (fun y => rho z y * (z.e y C γ * FsD hP z k φ φb C y)) :=
    fun C γ => (contDiff_rho z).mul ((z.contDiff_e C γ).mul (contDiff_FsD hP z hk hφ hφb C))
  have h1 : ∀ γ, pd (fluxD hP z k φ φb γ) γ x =
      ∑ C, pd (fun y => rho z y * (z.e y C γ * FsD hP z k φ φb C y)) γ x := fun γ =>
    pd_sum' _ (fun C _ => (hterm C γ).differentiable (by simp) x) γ
  simp only [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun C _ => ?_
  rw [div_frame z (contDiff_FsD hP z hk hφ hφb C) x C]
  congr 2
  have hpd : ∀ γ, pd (FsD hP z k φ φb C) γ x = pd (fun y => Flx hP C (Mf z k y) (z.ψ y) (z.ψb y)) γ x -
      pd (fPs hP z φ C) γ x + pd (fPb hP z φb C) γ x := by
    intro γ
    unfold FsD SobolevOpen.pd
    have d1 := (contDiff_Flx hP z hk C).differentiable (by simp) x
    have d2 := (contDiff_fPs hP z hφ C).differentiable (by simp) x
    have d3 := (contDiff_fPb hP z hφb C).differentiable (by simp) x
    rw [fderiv_fun_add (d1.fun_sub d2) d3, fderiv_fun_sub d1 d2]
    rfl
  simp only [hpd, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [frameD_Flx hP z hk hks x C, frameD_fPs hP z hφ x C, frameD_fPb hP z hφb x C]
  ring

theorem pd_symm_of {k : ST 3 → Met} (hk : ContDiff ℝ ∞ k) (hks : ∀ y μ ν, k y μ ν = k y ν μ)
    (x : ST 3) (α μ ν : Fin 4) : pd k α x μ ν = pd k α x ν μ := by
  have d := hk.differentiable (by simp) x
  have h1 := pd_apply d α μ
  have hd2 : ∀ μ', DifferentiableAt ℝ (fun y => k y μ') x := fun μ' =>
    (contDiff_pi.1 hk μ').differentiable (by simp) x
  rw [← pd_apply d α μ, ← pd_apply (hd2 μ) α ν, ← pd_apply d α ν, ← pd_apply (hd2 ν) α μ]
  congr 1
  funext y
  exact hks y μ ν

/-- **The Dirac bulk rows** at a point of the tuple: the Hilbert stress paired with the metric
variation, the Dirac residuals paired with the induced local Lorentz rotation and with the spinor
variations, the Dirac current paired with the gauge variation and the Yukawa term. -/
def bulkD (k : ST 3 → Met) (X : ST 3 → Fin 4 → MatLie m) (η : ST 3 → V) (φ : ST 3 → S)
    (φb : ST 3 → S') (x : ST 3) : ℝ :=
  rho z x * ((1 / 2 : ℝ) * ∑ A, ∑ B, lorentzSign A * lorentzSign B *
      (symTD SM.D hP.P).frame (z.H x) (z.ψ x)
        (covX SM.D (GR (z.g x) (z.dg x)) (aR (z.g x) (z.A x)) (z.ψ x) (dψR (z.g x) (fun γ => pd z.ψ γ x)))
        (z.ψb x)
        (covX SM.Db (GR (z.g x) (z.dg x)) (aR (z.g x) (z.A x)) (z.ψb x)
          (dψR (z.g x) (fun γ => pd z.ψb γ x)))
        A B * kfr (z.g x) (k x) A B +
    (hP.P (rDf SM.Db (GR (z.g x) (z.dg x)) (aR (z.g x) (z.A x)) (z.H x) (z.ψb x)
        (dψR (z.g x) (fun γ => pd z.ψb γ x))) ((-spinPart SM.D.Fr (Mf z k x)) (z.ψ x)) -
      hP.P ((-spinPart SM.Db.Fr (Mf z k x)) (z.ψb x))
        (rDf SM.D (GR (z.g x) (z.dg x)) (aR (z.g x) (z.A x)) (z.H x) (z.ψ x)
          (dψR (z.g x) (fun γ => pd z.ψ γ x)))) +
    (1 / 2 : ℝ) * ∑ C, lorentzSign C *
      (hP.P (z.ψb x) (SM.D.Fr.c C (SM.D.ρ (aR (z.g x) (X x) C) (z.ψ x))) -
        hP.P (SM.Db.ρ (aR (z.g x) (X x) C) (z.ψb x)) (SM.D.Fr.c C (z.ψ x))) -
    hP.P (z.ψb x) (SM.D.L (η x) (z.ψ x)) -
    hP.P (rDf SM.Db (GR (z.g x) (z.dg x)) (aR (z.g x) (z.A x)) (z.H x) (z.ψb x)
      (dψR (z.g x) (fun γ => pd z.ψb γ x))) (φ x) +
    hP.P (φb x) (rDf SM.D (GR (z.g x) (z.dg x)) (aR (z.g x) (z.A x)) (z.H x) (z.ψ x)
      (dψR (z.g x) (fun γ => pd z.ψ γ x))))

set_option maxHeartbeats 4000000 in
/-- **The first variation of the first-order Dirac density along a smooth tuple**: the bulk rows
minus the divergence of the Dirac flux. -/
theorem fderiv_L1D_field {k : ST 3 → Met} (hk : ContDiff ℝ ∞ k)
    (hks : ∀ y μ ν, k y μ ν = k y ν μ) (X : ST 3 → Fin 4 → MatLie m) (η : ST 3 → V)
    {φ : ST 3 → S} (hφ : ContDiff ℝ ∞ φ) {φb : ST 3 → S'} (hφb : ContDiff ℝ ∞ φb) (x : ST 3) :
    fderiv ℝ (L1D SM hP.P) (jC z x) (jW k X η φ φb x) =
      bulkD hP z k X η φ φb x - ∑ γ, pd (fluxD hP z k φ φb γ) γ x := by
  have hchart : jC z x ∈ chart1C m V S S' := ⟨GenCell.Tuple_det_neg z x, z.lor x⟩
  rw [fderiv_L1D_eq SM hP (jC z x) hchart (chartM_tuple z x) (fun α μ ν => z.dg_symm x α μ ν)
    (jW k X η φ φb x) (hks x) (fun α μ ν => pd_symm_of hk hks x α μ ν)]
  rw [div_fluxD hP z hk hks hφ hφb x]
  have hM : ∀ a b, Mf z k x b a = -Mf z k x a b := Mf_anti z k x
  have hdM : ∀ (C a b : Fin 4), (fun B A C' => (1 / 2 : ℝ) *
      (dLam (z.g x) (z.dg x) (k x) (fun α => pd k α x) B A C' -
        dLam (z.g x) (z.dg x) (k x) (fun α => pd k α x) B C' A)) C b a =
      -(fun B A C' => (1 / 2 : ℝ) * (dLam (z.g x) (z.dg x) (k x) (fun α => pd k α x) B A C' -
        dLam (z.g x) (z.dg x) (k x) (fun α => pd k α x) B C' A)) C a b := fun C a b => by
    simp only; ring
  unfold dMet dGau dHig dPsi dPsib
  simp only [jC, jW, j1F]
  have hG : ∀ B A C, GR (z.g x) (fun α => pd z.g α x) B C A = -GR (z.g x) (fun α => pd z.g α x) B A C :=
    fun B A C => GR_anti (chartM_tuple z x) (z.dg x) (fun α μ ν => z.dg_symm x α μ ν) B A C
  have hl1 : ∀ C, lorFl hP (fun A B => (1 / 2 : ℝ) * (Lam (z.g x) (k x) A B - Lam (z.g x) (k x) B A))
      (z.ψ x) (z.ψb x) C = Flx hP C (Mf z k x) (z.ψ x) (z.ψb x) := fun C =>
    lorFl_eq_Flx hP hM _ _ C
  have hl2 : ∀ C, lorFlD hP (fun A B => (1 / 2 : ℝ) * (Lam (z.g x) (k x) A B - Lam (z.g x) (k x) B A))
      (fun B A C => (1 / 2 : ℝ) * (dLam (z.g x) (fun α => pd z.g α x) (k x) (fun α => pd k α x) B A C -
        dLam (z.g x) (fun α => pd z.g α x) (k x) (fun α => pd k α x) B C A))
      (z.ψ x) (dψR (z.g x) fun γ => pd z.ψ γ x) (z.ψb x) (dψR (z.g x) fun γ => pd z.ψb γ x) C =
      Flx hP C (fun a b => (1 / 2 : ℝ) * (dLam (z.g x) (z.dg x) (k x) (fun α => pd k α x) C a b -
          dLam (z.g x) (z.dg x) (k x) (fun α => pd k α x) C b a)) (z.ψ x) (z.ψb x) +
        Flx hP C (Mf z k x) (dψR (z.g x) (fun γ => pd z.ψ γ x) C) (z.ψb x) +
        Flx hP C (Mf z k x) (z.ψ x) (dψR (z.g x) (fun γ => pd z.ψb γ x) C) := fun C =>
    lorFlD_eq_Flx hP hM hdM _ _ _ _ C
  have hdiv : ∀ C, divEf (GR (z.g x) fun α => pd z.g α x) C = divE z x C := fun C =>
    (divE_eq_divEf z x C).symm
  rw [psi_row hP (z.H x) hG (aR (z.g x) (z.A x)) (z.ψb x) (dψR (z.g x) fun γ => pd z.ψb γ x) (φ x)
      (dψR (z.g x) fun γ => pd φ γ x),
    psib_row hP (z.H x) hG (aR (z.g x) (z.A x)) (z.ψ x) (dψR (z.g x) fun γ => pd z.ψ γ x) (φb x)
      (dψR (z.g x) fun γ => pd φb γ x)]
  simp only [hl1, hl2, hdiv, volM_eq_rho]
  have hMf : (fun A B => (1 / 2 : ℝ) * (Lam (z.g x) (k x) A B - Lam (z.g x) (k x) B A)) =
      Mf z k x := rfl
  rw [hMf]
  unfold bulkD FsD fPs fPb
  have hdgx : z.dg x = fun α => pd z.g α x := rfl
  rw [hdgx]
  set ρ := rho z x
  have hsum : ∑ C, ρ * (divE z x C * (Flx hP C (Mf z k x) (z.ψ x) (z.ψb x) -
        (1 / 2 : ℝ) * lorentzSign C * hP.P (z.ψb x) (SM.D.Fr.c C (φ x)) +
        (1 / 2 : ℝ) * lorentzSign C * hP.P (φb x) (SM.D.Fr.c C (z.ψ x))) +
      ((Flx hP C (fun a b => (1 / 2 : ℝ) * (dLam (z.g x) (z.dg x) (k x) (fun α => pd k α x) C a b -
          dLam (z.g x) (z.dg x) (k x) (fun α => pd k α x) C b a)) (z.ψ x) (z.ψb x) +
        Flx hP C (Mf z k x) (dψR (z.g x) (fun γ => pd z.ψ γ x) C) (z.ψb x) +
        Flx hP C (Mf z k x) (z.ψ x) (dψR (z.g x) (fun γ => pd z.ψb γ x) C)) -
      (1 / 2 : ℝ) * lorentzSign C * (hP.P (dψR (z.g x) (fun γ => pd z.ψb γ x) C) (SM.D.Fr.c C (φ x)) +
        hP.P (z.ψb x) (SM.D.Fr.c C (dψR (z.g x) (fun γ => pd φ γ x) C))) +
      (1 / 2 : ℝ) * lorentzSign C * (hP.P (dψR (z.g x) (fun γ => pd φb γ x) C) (SM.D.Fr.c C (z.ψ x)) +
        hP.P (φb x) (SM.D.Fr.c C (dψR (z.g x) (fun γ => pd z.ψ γ x) C))))) =
      ρ * ∑ C, (divE z x C * Flx hP C (Mf z k x) (z.ψ x) (z.ψb x) +
        (Flx hP C (fun a b => (1 / 2 : ℝ) * (dLam (z.g x) (z.dg x) (k x) (fun α => pd k α x) C a b -
          dLam (z.g x) (z.dg x) (k x) (fun α => pd k α x) C b a)) (z.ψ x) (z.ψb x) +
        Flx hP C (Mf z k x) (dψR (z.g x) (fun γ => pd z.ψ γ x) C) (z.ψb x) +
        Flx hP C (Mf z k x) (z.ψ x) (dψR (z.g x) (fun γ => pd z.ψb γ x) C))) -
      ρ * ∑ C, (divE z x C * ((1 / 2 : ℝ) * lorentzSign C * hP.P (z.ψb x) (SM.D.Fr.c C (φ x))) +
        (1 / 2 : ℝ) * lorentzSign C * (hP.P (dψR (z.g x) (fun γ => pd z.ψb γ x) C) (SM.D.Fr.c C (φ x)) +
          hP.P (z.ψb x) (SM.D.Fr.c C (dψR (z.g x) (fun γ => pd φ γ x) C)))) +
      ρ * ∑ C, (divE z x C * ((1 / 2 : ℝ) * lorentzSign C * hP.P (φb x) (SM.D.Fr.c C (z.ψ x))) +
        (1 / 2 : ℝ) * lorentzSign C * (hP.P (dψR (z.g x) (fun γ => pd φb γ x) C) (SM.D.Fr.c C (z.ψ x)) +
          hP.P (φb x) (SM.D.Fr.c C (dψR (z.g x) (fun γ => pd z.ψ γ x) C)))) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun C _ => by ring
  rw [← hdgx, hsum, hdgx]
  ring

end Field

end RenewalGeometry.GenDFld
