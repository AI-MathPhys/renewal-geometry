/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import MathPhys.FieldTheory.Continuum.ActualJetSliceCongr

/-!
# Affine dependence of the actual-jet residuals on the free second-order data

Generic jet algebra for the Cauchy-data completion of `prop:generated-initial`
(Einstein–Standard-Model action-closure manuscript).  The residual rows of
`eq:actual-jet-writer` are affine in the second derivatives of the bosonic fields and in the
first derivatives of the spinors; we record the exact shifts:

* `ymRes_shift`: `∂²A ↦ ∂²A + δ` shifts `r^A_ν` by `g^{μρ}(δ_{ρμν} - δ_{ρνμ})`;
* `higgsRes_shift`: `∂²H ↦ ∂²H + δ` shifts `r_H` by `g^{μρ}δ_{ρμ}`;
* `rD_shift_jet`: `∂Ψ ↦ ∂Ψ + δ` shifts `r_D` by `Σ_b ε_b c_b(e_b{}^γδ_γ)`;
* `Etr_shift`: `∂²g ↦ ∂²g + δ` shifts `𝓔^{tr} - ∇_{(μ}C_{ν)}` by `-½ g^{αβ}δ_{αβμν}`
  (`eq:off-harmonic-metric-wave`).
-/

open Finset
open scoped ContDiff

noncomputable section

namespace MathPhys.GenSlice

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk FrameCurvature HarmonicDefect ActualJetWriter
  ActualJetFrame ActualJetSystem ActualJetSmooth ActualJetBridge ActualJetState ActualJetGauge
  ActualJetSpinor SpinorProlongation

set_option linter.unusedSectionVars false

section Algebra

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℝ 𝔤]

/-- **Shift of the Yang–Mills residual** under a change of the second gauge jet. -/
theorem ymRes_shift (A : Fin 4 → 𝔤) (dA : Fin 4 → Fin 4 → 𝔤) (ddA δ : Fin 4 → Fin 4 → Fin 4 → 𝔤)
    (gi : Fin 4 → Fin 4 → ℝ) (Γ : Fin 4 → Fin 4 → Fin 4 → ℝ) (J : Fin 4 → 𝔤) (ν : Fin 4) :
    ymRes A dA (fun a b c => ddA a b c + δ a b c) gi Γ J ν =
      ymRes A dA ddA gi Γ J ν + ∑ μ, ∑ ρ, gi μ ρ • (δ ρ μ ν - δ ρ ν μ) := by
  unfold ymRes ymDiv dFm
  simp only [smul_sub, smul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  abel

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [LieRingModule 𝔤 V] [LieModule ℝ 𝔤 V]

/-- **Shift of the Higgs residual** under a change of the second Higgs jet. -/
theorem higgsRes_shift (A : Fin 4 → 𝔤) (dA : Fin 4 → Fin 4 → 𝔤) (H : V) (dH : Fin 4 → V)
    (ddH δ : Fin 4 → Fin 4 → V) (gi : Fin 4 → Fin 4 → ℝ) (Γ : Fin 4 → Fin 4 → Fin 4 → ℝ)
    (SH : V) :
    higgsRes A dA H dH (fun a b => ddH a b + δ a b) gi Γ SH =
      higgsRes A dA H dH ddH gi Γ SH + ∑ μ, ∑ ρ, gi μ ρ • δ ρ μ := by
  unfold higgsRes waveH dDH
  simp only [smul_sub, smul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  abel

end Algebra

/-! ### The metric row -/

section Metric

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem waveOp_shift (gi : n → n → ℝ) (ddg δ : n → n → n → n → ℝ) (μ ν : n) :
    waveOp gi (fun a b c d => ddg a b c d + δ a b c d) μ ν =
      waveOp gi ddg μ ν + ∑ α, ∑ β, gi α β * δ α β μ ν := by
  unfold waveOp
  simp only [mul_add, Finset.sum_add_distrib]

/-- **Shift of the reduced Einstein row**: changing `∂²g` by a symmetric `δ` changes
`𝓔^{tr} - ∇_{(μ}C_{ν)}` by `-½ g^{αβ}δ_{αβμν}`. -/
theorem Etr_shift (g gi : n → n → ℝ) (dg : n → n → n → ℝ) (ddg δ : n → n → n → n → ℝ)
    (hgi : ∀ a b, gi a b = gi b a)
    (hinv : ∀ a c, ∑ b, g a b * gi b c = if a = c then 1 else 0)
    (hs1 : ∀ α β μ ν, ddg α β μ ν = ddg β α μ ν) (hs2 : ∀ α β μ ν, ddg α β μ ν = ddg α β ν μ)
    (hd1 : ∀ α β μ ν, δ α β μ ν = δ β α μ ν) (hd2 : ∀ α β μ ν, δ α β μ ν = δ α β ν μ)
    (hcard : Fintype.card n = 4) (T : n → n → ℝ) (Λ κ : ℝ) (μ ν : n) :
    traceRev g gi (fun a b => einstein g gi dg (fun a b c d => ddg a b c d + δ a b c d) a b +
        Λ * g a b - κ * T a b) μ ν - symDefect g gi dg (fun a b c d => ddg a b c d + δ a b c d) μ ν =
      traceRev g gi (fun a b => einstein g gi dg ddg a b + Λ * g a b - κ * T a b) μ ν -
        symDefect g gi dg ddg μ ν - (1 / 2) * ∑ α, ∑ β, gi α β * δ α β μ ν := by
  have h1 := off_harmonic_metric_wave g gi dg ddg hgi hinv hs1 hs2 hcard T Λ κ μ ν
  have h2 := off_harmonic_metric_wave g gi dg (fun a b c d => ddg a b c d + δ a b c d) hgi hinv
    (fun α β μ ν => by rw [hs1, hd1]) (fun α β μ ν => by rw [hs2, hd2]) hcard T Λ κ μ ν
  rw [waveOp_shift] at h2
  linarith

end Metric

/-! ### The Dirac row -/

section Dirac

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']

/-- **Shift of the Dirac residual** under a change of the spinor 1-jet. -/
theorem rD_shift_jet {S₀ : Type*} [NormedAddCommGroup S₀] [NormedSpace ℝ S₀]
    (J : ActualJet (MatLie m) V S S') (D : DiracData (MatLie m) V S₀) (ψ : S₀)
    (cψ δ : Fin 4 → S₀) :
    J.rD D ψ (fun γ => cψ γ + δ γ) =
      J.rD D ψ cψ + ∑ b, D.Fr.ε b • D.Fr.c b • ∑ γ, J.FJ.e b γ • δ γ := by
  unfold ActualJet.rD resD dirac cov dψf
  simp only [smul_add, Finset.sum_add_distrib]
  abel

end Dirac

end MathPhys.GenSlice
