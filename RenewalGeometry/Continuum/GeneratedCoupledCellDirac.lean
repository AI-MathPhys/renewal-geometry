/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.GeneratedCoupledCellVar

/-!
# The Dirac part of the cell variation

Einstein–Standard-Model action-closure manuscript, `app:generated-dynamics` ("integration by
parts expresses `D S^{cmp}_{N,τ}` through the physical rows"), Dirac part.

* `fluxDJ` — the Dirac flux `B^γ = ϱΣ_C e_C{}^γ(Fl_C - f_C + f̄_C)` as a function of the
  **values** `(g, Ψ, Ψ̄; k, φ, φ̄)` (it contains no derivative); `fluxD_eq`;
* **`cell_dirac`** — for a smooth tuple and smooth periodic variations, the cell integral of the
  first variation of the first-order Dirac density is the cell integral of the Dirac bulk rows
  minus the difference of the Dirac time fluxes at the cell ends;
* `Lam_smul`, `Mk_smul`, `spinPart_smul'` — linearity of the local Lorentz rotation in `k`;
* **`exists_dirJ_bound`** — on a compact set of chart metrics and spinor values the Dirac bulk
  rows are bounded by `M ‖residual‖ ‖variation‖`.
-/

open Finset Set Filter Topology
open scoped ContDiff

noncomputable section

namespace RenewalGeometry.GenCplCD

open SobolevOpen (pd)
open HarmonicDefect EHJetVariation EHFieldVariation ActualJetSystem ActualJetRecon ActualJetSmooth
  ActualJetGauge ActualJetWriter ActualJetBridge ActualJetState GenMatVar GenFOAction FrameCurvature
  ActualJetFrame GenResMaps JetCurve GenDAlg GenDFJ GenDStress GenDiracCur SpinorProlongation
  GenDAct GenDEul GenNoether GenMatEuler PeriodicCube SlabWaveHk GenDFld GenCellVar GenCellBulk
  ActualJetCompleteForcing GenCplCV

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']
variable {SM : SMData (MatLie m) V S S'} (hP : DiracPairing SM)

/-! ### The Dirac flux as a function of values -/

/-- **The Dirac flux on values** `B^γ = √(-det g) Σ_C e_C{}^γ(Fl_C(M, Ψ, Ψ̄) - ½ε_C⟨Ψ̄, c_Cφ⟩ +
½ε_C⟨φ̄, c_CΨ⟩)`, `M = ½(Λ - Λᵀ)` the local Lorentz part of the frame variation induced by `k`. -/
def fluxDJ (γ : Fin 4) (g : Met) (ψ : S) (ψb : S') (k : Met) (φ : S) (φb : S') : ℝ :=
  ∑ C, volM g * (frR g C γ * (Flx hP C (Mk g k) ψ ψb -
    (1 / 2 : ℝ) * lorentzSign C * hP.P ψb (SM.D.Fr.c C φ) +
    (1 / 2 : ℝ) * lorentzSign C * hP.P φb (SM.D.Fr.c C ψ)))

theorem fluxD_eq (z : Tuple m V S S') (k : ST 3 → Met) (φ : ST 3 → S) (φb : ST 3 → S')
    (γ : Fin 4) (y : ST 3) :
    fluxD hP z k φ φb γ y = fluxDJ hP γ (z.g y) (z.ψ y) (z.ψb y) (k y) (φ y) (φb y) := by
  unfold fluxD fluxDJ FsD fPs fPb
  simp only [← volM_eq_rho z y]
  rfl

theorem isSPeriodic_fluxD (z : Tuple m V S S') {k : ST 3 → Met} (hkp : IsSPeriodic k)
    {φ : ST 3 → S} (hφp : IsSPeriodic φ) {φb : ST 3 → S'} (hφbp : IsSPeriodic φb) (γ : Fin 4) :
    IsSPeriodic (fluxD hP z k φ φb γ) := fun l x => by
  rw [fluxD_eq, fluxD_eq, z.g_per l x, z.ψ_per l x, z.ψb_per l x, hkp l x, hφp l x, hφbp l x]

/-! ### Linearity of the local Lorentz rotation -/

theorem Lam_smul {g : Met} (hg : ChartM g) (t : ℝ) (k : Met) (A B : Fin 4) :
    Lam g (t • k) A B = t * Lam g k A B := by
  have e : edot g (t • k) A = t • edot g k A := funext fun μ => by
    rw [edot_fderiv hg, edot_fderiv hg, map_smul]; rfl
  unfold Lam ipg
  rw [e, Finset.mul_sum]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem Lam_zero {g : Met} (hg : ChartM g) (A B : Fin 4) : Lam g 0 A B = 0 := by
  have := Lam_smul hg 0 0 A B
  simpa using this

theorem Mk_smul {g : Met} (hg : ChartM g) (t : ℝ) (k : Met) :
    Mk g (t • k) = fun A B => t * Mk g k A B := by
  funext A B
  unfold Mk
  rw [Lam_smul hg, Lam_smul hg]
  ring

theorem Mk_zero {g : Met} (hg : ChartM g) : Mk g 0 = fun _ _ => 0 := by
  funext A B
  unfold Mk
  rw [Lam_zero hg, Lam_zero hg]
  ring

theorem spinPart_smul' {ι A : Type*} [Fintype ι] [Ring A] [Algebra ℝ A] (Fr : CliffordFrame ι A)
    (t : ℝ) (W : ι → ι → ℝ) : spinPart Fr (fun a b => t * W a b) = t • spinPart Fr W := by
  unfold spinPart
  rw [smul_comm, Finset.smul_sum]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [smul_smul]
  congr 1
  ring

theorem fluxDJ_zero {g : Met} (hg : ChartM g) (γ : Fin 4) (ψ : S) (ψb : S') :
    fluxDJ hP γ g ψ ψb 0 0 0 = 0 := by
  unfold fluxDJ Flx
  simp [Mk_zero hg]

/-! ### The Dirac cell variation of a tuple -/

theorem continuous_jC (z : Tuple m V S S') : Continuous (jC (m := m) (V := V) z) := by
  have h1 := continuous_j1F z.g_smooth z.A_smooth z.H_smooth
  have h2 : Continuous fun x => fun γ => pd z.ψ γ x :=
    continuous_pi fun γ => (contDiff_pd z.ψ_smooth γ).continuous
  have h3 : Continuous fun x => fun γ => pd z.ψb γ x :=
    continuous_pi fun γ => (contDiff_pd z.ψb_smooth γ).continuous
  exact h1.prodMk ((z.ψ_smooth.continuous.prodMk h2).prodMk (z.ψb_smooth.continuous.prodMk h3))

theorem continuous_jW {k : ST 3 → Met} (hk : ContDiff ℝ ∞ k) {X : ST 3 → Fin 4 → MatLie m}
    (hX : ContDiff ℝ ∞ X) {η : ST 3 → V} (hη : ContDiff ℝ ∞ η) {φ : ST 3 → S}
    (hφ : ContDiff ℝ ∞ φ) {φb : ST 3 → S'} (hφb : ContDiff ℝ ∞ φb) :
    Continuous (jW k X η φ φb) := by
  have h1 := continuous_j1F hk hX hη
  have h2 : Continuous fun x => fun γ => pd φ γ x :=
    continuous_pi fun γ => (contDiff_pd hφ γ).continuous
  have h3 : Continuous fun x => fun γ => pd φb γ x :=
    continuous_pi fun γ => (contDiff_pd hφb γ).continuous
  exact h1.prodMk ((hφ.continuous.prodMk h2).prodMk (hφb.continuous.prodMk h3))

set_option maxHeartbeats 1000000 in
/-- **The Dirac part of the cell variation**: for a smooth tuple and smooth periodic variations
`(k, X, η, φ, φ̄)` (`k` symmetric) the cell integral of the first variation of the first-order
Dirac density is the cell integral of the Dirac bulk rows minus the difference of the Dirac time
fluxes at the cell ends. -/
theorem cell_dirac (z : Tuple m V S S') {k : ST 3 → Met} (hk : ContDiff ℝ ∞ k)
    (hks : ∀ y μ ν, k y μ ν = k y ν μ) (hkp : IsSPeriodic k) {X : ST 3 → Fin 4 → MatLie m}
    (hX : ContDiff ℝ ∞ X) {η : ST 3 → V} (hη : ContDiff ℝ ∞ η) {φ : ST 3 → S}
    (hφ : ContDiff ℝ ∞ φ) (hφp : IsSPeriodic φ) {φb : ST 3 → S'} (hφb : ContDiff ℝ ∞ φb)
    (hφbp : IsSPeriodic φb) {a b : ℝ} (hab : a ≤ b) :
    cellInt a b (fun x => fderiv ℝ (L1D SM hP.P) (jC z x) (jW k X η φ φb x)) =
      cellInt a b (bulkD hP z k X η φ φb) -
        (sint (fluxD hP z k φ φb 0) b - sint (fluxD hP z k φ φb 0) a) := by
  have ha : a - 1 < a := by linarith
  have hb : b < b + 1 := by linarith
  set D : ST 3 → ℝ := fun x => ∑ γ, pd (fluxD hP z k φ φb γ) γ x with hD
  have hpt : ∀ x, fderiv ℝ (L1D SM hP.P) (jC z x) (jW k X η φ φb x) =
      bulkD hP z k X η φ φb x - D x := fun x => fderiv_L1D_field hP z hk hks X η hφ hφb x
  have hF : ∀ γ, ContDiff ℝ ∞ (fluxD hP z k φ φb γ) := fun γ => contDiff_fluxD hP z hk hφ hφb γ
  have hcDγ : ∀ γ, ContinuousOn (pd (fluxD hP z k φ φb γ) γ) (openSlab (a - 1) (b + 1)) :=
    fun γ => (EHFieldVariation.contDiff_pd' (hF γ) γ).continuous.continuousOn
  have hcD : ContinuousOn D (openSlab (a - 1) (b + 1)) :=
    continuousOn_finset_sum _ fun γ _ => hcDγ γ
  have hcL : ContinuousOn (fun x => fderiv ℝ (L1D SM hP.P) (jC z x) (jW k X η φ φb x))
      (openSlab (a - 1) (b + 1)) :=
    continuousOn_fderiv_jet isOpen_chart1C (contDiffOn_L1D SM hP.P) (continuous_jC z)
      (continuous_jW hk hX hη hφ hφb) fun x _ => ⟨GenCell.Tuple_det_neg z x, z.lor x⟩
  have hcB : ContinuousOn (bulkD hP z k X η φ φb) (openSlab (a - 1) (b + 1)) :=
    (hcL.add hcD).congr fun x _ => by
      show bulkD hP z k X η φ φb x = fderiv ℝ (L1D SM hP.P) (jC z x) (jW k X η φ φb x) + D x
      rw [hpt x]; ring
  simp only [hpt]
  rw [cellInt_sub_on hcB hcD ha hab hb]
  have hDi : cellInt a b D = sint (fluxD hP z k φ φb 0) b - sint (fluxD hP z k φ φb 0) a := by
    rw [cellInt_sum_on _ hcDγ ha hab hb, Fin.sum_univ_succ,
      cellInt_pd_zero_loc (hF 0).contDiffOn ha hab hb]
    have hz : ∀ i : Fin 3, cellInt a b (pd (fluxD hP z k φ φb i.succ) i.succ) = 0 := fun i =>
      cellInt_pd_succ_loc (hF _).contDiffOn (isSPeriodic_fluxD hP z hkp hφp hφbp _) ha hab hb i
    simp only [hz, Finset.sum_const_zero, add_zero]
  rw [hDi]

end RenewalGeometry.GenCplCD
