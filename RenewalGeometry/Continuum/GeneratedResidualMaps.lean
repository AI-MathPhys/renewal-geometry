/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.ActualJetStateField

/-!
# Raw-jet residual maps of the Einstein–Standard-Model system

Einstein–Standard-Model action-closure manuscript, `thm:generated-dynamics`
(`eq:generated-bosonic`, `eq:generated-Dirac`, `app:generated-dynamics`: "The Riemann tensor is
linear in second metric derivatives plus smooth quadratic first-derivative terms ... The wave-type
Yang–Mills and Higgs rows have the same derivative count.  The Dirac row is first order").

The physical residuals of `prop:actual-jet-writer` (`ActualJetSystem.ActualJet.res`) are defined on
actual jets, i.e. on structures carrying the jet relations of a smooth field tuple.  For the
readouts of a reconstructed record we need them as **functions of the raw head jets**
`(g, ∂g, ∂²g, A, ∂A, ∂²A, H, ∂H, ∂²H, Ψ, ∂Ψ, Ψ̄, ∂Ψ̄)` (`HJ2`, a finite-dimensional normed space):

* `frR`, `deR`, `omR`, `dψR`, `XsR` — the adapted frame `frU(g⁻¹)`, its derivative jets, the
  twisted spin connection, the frame derivatives and covariant frame jets of a spinor, written as
  formulas in the raw jets;
* `TactR` — the complete off-shell stress `T^{YM} + T^H + T^D`;
* **`bosR`** — `R_B = (𝓔^{tr}, r^A, r_H)` (trace-reversed Einstein residual with the complete
  stress, Yang–Mills residual, Higgs residual); **`dirR`** — `R_D = (r_D, r̄_D)`;
  **`riemR`** — the coordinate Riemann tensor `R^λ{}_{σγρ}(g)`;
* `hj2 z x` — the head 2-jet of a smooth tuple; **`bosR_hj2`**, **`dirR_hj2`**: on the jets of
  every smooth tuple the raw maps are the actual-jet residuals (`bosF`, `dirF`), and
  `riemR_hj2` identifies the Riemann tensor field.

The raw maps are smooth on the Lorentzian chart (`GeneratedResidualSmooth.lean`).
-/

open Finset Set
open scoped ContDiff

noncomputable section

namespace RenewalGeometry.GenResMaps

open SobolevOpen (pd)
open PeriodicCube SlabWaveHk FrameCurvature HarmonicDefect ActualJetWriter ActualJetFrame
  ActualJetSystem ActualJetSmooth ActualJetGauge SpinorProlongation TwistedHalfRicci
  ActualJetBridge ActualJetState ActualJetCompleteForcing ActualJetRecon ActualJetSpinor

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']

variable (m V S S') in
/-- **The head 2-jets** `(g, ∂_αg, ∂_β∂_αg; A, ∂_γA, ∂_δ∂_γA; H, ∂H, ∂²H; Ψ, ∂Ψ; Ψ̄, ∂Ψ̄)` as a
finite-dimensional normed space (`dg α μ ν = ∂_αg_{μν}`, `ddg β α μ ν = ∂_β∂_αg_{μν}`). -/
abbrev HJ2 := (Met × (Fin 4 → Met) × (Fin 4 → Fin 4 → Met)) ×
  ((Fin 4 → MatLie m) × (Fin 4 → Fin 4 → MatLie m) × (Fin 4 → Fin 4 → Fin 4 → MatLie m)) ×
  (V × (Fin 4 → V) × (Fin 4 → Fin 4 → V)) × (S × (Fin 4 → S)) × (S' × (Fin 4 → S'))

/-! ### Raw frame and spinor jets -/

/-- The adapted frame `e_A{}^μ = frU(g⁻¹)`. -/
def frR (g : Met) : Fin 4 → Fin 4 → ℝ := fun A μ => frU (ginvOf g) A μ

/-- The frame derivative jets `∂_γe_A{}^μ = frameJet(g⁻¹, ∂g⁻¹)`. -/
def deR (g : Met) (dg : Fin 4 → Met) : Fin 4 → Fin 4 → Fin 4 → ℝ := fun γ A μ =>
  frameJet (ginvOf g) (fun γ l σ => dginv (ginvOf g) dg γ l σ) γ A μ

/-- The twisted spin connection `ω_B` from the raw jets. -/
def omR {S₀ : Type*} [AddCommGroup S₀] [Module ℝ S₀] (D : DiracData (MatLie m) V S₀) (g : Met)
    (dg : Fin 4 → Met) (A : Fin 4 → MatLie m) (B : Fin 4) : Module.End ℝ S₀ :=
  omegaU D g (ginvOf g) dg (frR g) (deR g dg) A B

/-- The frame derivatives `e_BΨ = e_B{}^γ∂_γΨ`. -/
def dψR {S₀ : Type*} [AddCommGroup S₀] [Module ℝ S₀] (g : Met) (cψ : Fin 4 → S₀) (B : Fin 4) :
    S₀ :=
  ∑ γ, frR g B γ • cψ γ

/-- The covariant frame jets `X_B = ∇_{e_B}Ψ`. -/
def XsR {S₀ : Type*} [AddCommGroup S₀] [Module ℝ S₀] (D : DiracData (MatLie m) V S₀) (g : Met)
    (dg : Fin 4 → Met) (A : Fin 4 → MatLie m) (ψ : S₀) (cψ : Fin 4 → S₀) (B : Fin 4) : S₀ :=
  cov (omR D g dg A) ψ (dψR g cψ) B

/-- The Dirac residual `r_D = 𝒟Ψ - 𝓜(H)Ψ` from the raw jets. -/
def rDR {S₀ : Type*} [AddCommGroup S₀] [Module ℝ S₀] (D : DiracData (MatLie m) V S₀) (g : Met)
    (dg : Fin 4 → Met) (A : Fin 4 → MatLie m) (H : V) (ψ : S₀) (cψ : Fin 4 → S₀) : S₀ :=
  resD D.Fr (omR D g dg A) D.m0 D.L H ψ (dψR g cψ)

/-! ### The raw residual maps -/

/-- The complete off-shell stress `T^{YM} + T^H + T^D` from the raw first jets. -/
def TactR (SM : SMData (MatLie m) V S S') (g : Met) (dg : Fin 4 → Met) (A : Fin 4 → MatLie m)
    (dA : Fin 4 → Fin 4 → MatLie m) (H : V) (dH : Fin 4 → V) (ψ : S) (cψ : Fin 4 → S) (ψb : S')
    (cψb : Fin 4 → S') (μ ν : Fin 4) : ℝ :=
  ymStressB SM.ipG g (ginvOf g) (Fm A dA) μ ν +
    higgsStressB SM.ipV SM.lamH SM.vH g (ginvOf g) H (ActualJetGauge.DH A H dH) μ ν +
    SM.TD.coord g lorentzSign (frR g) H ψ (XsR SM.D g dg A ψ cψ) ψb (XsR SM.Db g dg A ψb cψb) μ ν

/-- **The raw bosonic residual map** `R_B = (𝓔^{tr}, r^A, r_H)`. -/
def bosR (SM : SMData (MatLie m) V S S') (j : HJ2 m V S S') : BosP m V :=
  (traceRev j.1.1 (ginvOf j.1.1) (fun a b => einstein j.1.1 (ginvOf j.1.1) j.1.2.1 j.1.2.2 a b +
      SM.Λ * j.1.1 a b - SM.κ * TactR SM j.1.1 j.1.2.1 j.2.1.1 j.2.1.2.1 j.2.2.1.1 j.2.2.1.2.1
        j.2.2.2.1.1 j.2.2.2.1.2 j.2.2.2.2.1 j.2.2.2.2.2 a b),
    ymRes j.2.1.1 j.2.1.2.1 j.2.1.2.2 (ginvOf j.1.1) (chr (ginvOf j.1.1) j.1.2.1)
      (fun ν => SM.Jcur j.1.1 (ginvOf j.1.1) j.2.2.1.1
        (ActualJetGauge.DH j.2.1.1 j.2.2.1.1 j.2.2.1.2.1) j.2.2.2.1.1 j.2.2.2.2.1 ν),
    higgsRes j.2.1.1 j.2.1.2.1 j.2.2.1.1 j.2.2.1.2.1 j.2.2.1.2.2 (ginvOf j.1.1)
      (chr (ginvOf j.1.1) j.1.2.1)
      (SM.SH j.1.1 (ginvOf j.1.1) j.2.2.1.1 j.2.2.2.1.1 j.2.2.2.2.1))

/-- **The raw Dirac residual map** `R_D = (r_D, r̄_D)`. -/
def dirR (SM : SMData (MatLie m) V S S') (j : HJ2 m V S S') : S × S' :=
  (rDR SM.D j.1.1 j.1.2.1 j.2.1.1 j.2.2.1.1 j.2.2.2.1.1 j.2.2.2.1.2,
    rDR SM.Db j.1.1 j.1.2.1 j.2.1.1 j.2.2.1.1 j.2.2.2.2.1 j.2.2.2.2.2)

/-- **The raw Riemann map** `R^λ{}_{σγρ}` of the metric 2-jet. -/
def riemR (j : HJ2 m V S S') (c : Fin 4 × Fin 4 × Fin 4 × Fin 4) : ℝ :=
  rie (chr (ginvOf j.1.1) j.1.2.1) (dchr (ginvOf j.1.1) j.1.2.1 j.1.2.2) c.1 c.2.1 c.2.2.1 c.2.2.2

/-! ### The head 2-jet of a smooth tuple -/

/-- The head 2-jet of a smooth tuple at a point. -/
def hj2 (z : Tuple m V S S') (x : ST 3) : HJ2 m V S S' :=
  ((z.g x, fun α => pd z.g α x, fun β α => pd (pd z.g α) β x),
    (z.A x, fun γ => pd z.A γ x, fun δ γ => pd (pd z.A γ) δ x),
    (z.H x, fun γ => pd z.H γ x, fun δ γ => pd (pd z.H γ) δ x),
    (z.ψ x, fun γ => pd z.ψ γ x), (z.ψb x, fun γ => pd z.ψb γ x))

section TupleJets

variable (z : Tuple m V S S') (x : ST 3)

theorem jet_e : (z.jet x).FJ.e = frR (z.g x) := rfl

theorem jet_AF_fr : (z.jet x).AF.fr = frR (z.g x) := ((z.jet x).e_eq).symm

theorem jet_de : (z.jet x).FJ.de = deR (z.g x) (fun α => pd z.g α x) := rfl

theorem jet_omega {S₀ : Type*} [AddCommGroup S₀] [Module ℝ S₀] (D : DiracData (MatLie m) V S₀) :
    ((z.jet x).LJ D).ω = omR D (z.g x) (fun α => pd z.g α x) (z.A x) := by
  funext B
  rw [ActualJet.LJ_ω, jet_AF_fr]
  rfl

theorem jet_dψf {S₀ : Type*} [AddCommGroup S₀] [Module ℝ S₀] (cψ : Fin 4 → S₀) :
    dψf (z.jet x).FJ cψ = dψR (z.g x) cψ := rfl

theorem jet_Xs {S₀ : Type*} [AddCommGroup S₀] [Module ℝ S₀] (D : DiracData (MatLie m) V S₀)
    (ψ : S₀) (cψ : Fin 4 → S₀) :
    (z.jet x).Xs D ψ cψ = XsR D (z.g x) (fun α => pd z.g α x) (z.A x) ψ cψ := by
  funext B
  unfold ActualJet.Xs XsR
  rw [jet_omega, jet_dψf]

theorem jet_rD {S₀ : Type*} [AddCommGroup S₀] [Module ℝ S₀] (D : DiracData (MatLie m) V S₀)
    (ψ : S₀) (cψ : Fin 4 → S₀) :
    (z.jet x).rD D ψ cψ = rDR D (z.g x) (fun α => pd z.g α x) (z.A x) (z.H x) ψ cψ := by
  unfold ActualJet.rD rDR
  rw [jet_omega, jet_dψf]
  rfl

theorem jet_Tact (SM : SMData (MatLie m) V S S') (μ ν : Fin 4) :
    (z.jet x).Tact SM μ ν = TactR SM (z.g x) (fun α => pd z.g α x) (z.A x)
      (fun γ => pd z.A γ x) (z.H x) (fun γ => pd z.H γ x) (z.ψ x) (fun γ => pd z.ψ γ x) (z.ψb x)
      (fun γ => pd z.ψb γ x) μ ν := by
  unfold ActualJet.Tact TactR
  rw [jet_Xs, jet_Xs, jet_AF_fr]
  rfl

/-- **The raw bosonic residual map is the actual residual on the jets of every smooth tuple.** -/
theorem bosR_hj2 (SM : SMData (MatLie m) V S S') : bosR SM (hj2 z x) = bosF SM z x := by
  have hT : (fun a b => (z.jet x).Tact SM a b) = fun a b => TactR SM (z.g x)
      (fun α => pd z.g α x) (z.A x) (fun γ => pd z.A γ x) (z.H x) (fun γ => pd z.H γ x) (z.ψ x)
      (fun γ => pd z.ψ γ x) (z.ψb x) (fun γ => pd z.ψb γ x) a b := by
    funext a b; exact jet_Tact z x SM a b
  unfold bosF ActualJet.res bosR hj2
  simp only [jet_Tact z x SM]
  rfl

/-- **The raw Dirac residual map is the actual Dirac residual on the jets of every smooth
tuple.** -/
theorem dirR_hj2 (SM : SMData (MatLie m) V S S') : dirR SM (hj2 z x) = dirF SM z x := by
  unfold dirF ActualJet.res dirR hj2
  simp only
  rw [jet_rD, jet_rD]
  rfl

/-- The Riemann tensor field of a tuple in raw-jet form. -/
theorem riemR_hj2 (c : Fin 4 × Fin 4 × Fin 4 × Fin 4) :
    riemR (hj2 z x) c = rie (chr (z.gi x) (z.dg x)) (dchr (z.gi x) (z.dg x) (z.ddg x)) c.1 c.2.1
      c.2.2.1 c.2.2.2 := rfl

end TupleJets

end RenewalGeometry.GenResMaps
