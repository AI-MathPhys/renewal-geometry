/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.GeneratedMatterVariation
import RenewalGeometry.Continuum.GeneratedCellCalculus

/-!
# The Yang–Mills–Higgs Euler rows of the first-derivative action (field level)

Einstein–Standard-Model action-closure manuscript, `app:generated-dynamics` ("At the generated
record, integration by parts expresses `D S^{cmp}_{N,τ}` through the physical rows"), matter
sector, for variational theory data (`GenStress.VariationalStress`):

for a smooth actual field tuple `z` and smooth gauge and Higgs variations `X`, `η`,

`D_{(X,η)}(L_{YM} + L_H)(j¹z) = Σ_δ⟨ϱ g^{δβ}r^A_β, X_δ⟩ + 2ϱ⟨r_H, η⟩ - Σ_γ ∂_γ B^γ`,

`B^γ = Σ_δ⟨𝔉^{γδ}, X_δ⟩ + 2⟨𝔇^γ, η⟩` (**`matter_euler`**): the gauge and Higgs Euler rows of
the first-derivative density are the Yang–Mills and Higgs residuals of `prop:actual-jet-writer`
(`GenNoether.ymDensity_eq`, `GenNoether.div_densH`, the moment map of the Higgs current).
-/

namespace RenewalGeometry

namespace GenMatEuler

open HarmonicDefect EHJetVariation EHFieldVariation ActualJetSystem ActualJetRecon
  ActualJetSmooth ActualJetGauge SlabWaveHk ActualJetWriter ActualJetBridge ActualJetState
  GenMatVar GenNoether PeriodicCube
open SobolevOpen (pd)
open scoped ContDiff

noncomputable section

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 1024

variable {m : ℕ}
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [LieRingModule (MatLie m) V] [LieModule ℝ (MatLie m) V]
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [FiniteDimensional ℝ S]
variable {S' : Type*} [NormedAddCommGroup S'] [NormedSpace ℝ S'] [FiniteDimensional ℝ S']

variable (z : Tuple m V S S')

theorem volM_eq_rho (x : ST 3) : volM (z.g x) = rho z x := by
  unfold volM rho detF
  rw [abs_of_neg (GenCell.Tuple_det_neg z x)]

theorem DnJ_eq_dens (x : ST 3) (γ δ : Fin 4) :
    DnJ (volM (z.g x)) (ginvOf (z.g x)) (Fm (z.A x) (fun γ μ => pd z.A γ x μ)) γ δ =
      dens z x γ δ := by
  rw [volM_eq_rho]
  rfl

theorem DhJ_eq_densH (x : ST 3) (β : Fin 4) :
    DhJ (volM (z.g x)) (ginvOf (z.g x)) (ActualJetGauge.DH (z.A x) (z.H x) (fun γ => pd z.H γ x)) β =
      densH z x β := by
  rw [volM_eq_rho]
  rfl

/-- The matter flux `B^γ = Σ_δ⟨𝔉^{γδ}, X_δ⟩ + 2⟨𝔇^γ, η⟩`. -/
def matFlux (SM : SMData (MatLie m) V S S') (X : ST 3 → Fin 4 → MatLie m) (η : ST 3 → V)
    (γ : Fin 4) (y : ST 3) : ℝ :=
  ∑ δ, SM.ipG (dens z y γ δ) (X y δ) + 2 * SM.ipV (densH z y γ) (η y)

/-- **The Yang–Mills–Higgs Euler rows** (variational data): the jet-level gauge and Higgs
variations of the first-derivative matter density at the tuple are the residual rows minus the
divergence of the matter flux. -/
theorem matter_euler (SM : SMData (MatLie m) V S S') (hV : GenStress.VariationalStress SM)
    {X : ST 3 → Fin 4 → MatLie m} (hX : ContDiff ℝ ∞ X) {η : ST 3 → V} (hη : ContDiff ℝ ∞ η)
    (x : ST 3) :
    (-∑ γ, ∑ δ, SM.ipG (DnJ (volM (z.g x)) (ginvOf (z.g x)) (Fm (z.A x)
        (fun γ μ => pd z.A γ x μ)) γ δ) (pd X γ x δ) +
      ∑ γ, ∑ δ, SM.ipG ⁅z.A x γ, DnJ (volM (z.g x)) (ginvOf (z.g x)) (Fm (z.A x)
        (fun γ μ => pd z.A γ x μ)) γ δ⁆ (X x δ)) +
    (-(2 * ∑ β, SM.ipV (DhJ (volM (z.g x)) (ginvOf (z.g x))
        (ActualJetGauge.DH (z.A x) (z.H x) (fun γ => pd z.H γ x)) β) (pd η β x)) +
      2 * SM.ipV (∑ β, ⁅z.A x β, DhJ (volM (z.g x)) (ginvOf (z.g x))
        (ActualJetGauge.DH (z.A x) (z.H x) (fun γ => pd z.H γ x)) β⁆) (η x) -
      ∑ β, SM.ipG ((2 : ℝ) • hV.μ (z.H x) (DhJ (volM (z.g x)) (ginvOf (z.g x))
        (ActualJetGauge.DH (z.A x) (z.H x) (fun γ => pd z.H γ x)) β)) (X x β) -
      2 * volM (z.g x) * SM.ipV ((2 * SM.lamH * (SM.ipV (z.H x) (z.H x) - SM.vH ^ 2)) • z.H x)
        (η x)) =
    ∑ δ, SM.ipG (densR SM z x δ) (X x δ) + 2 * rho z x * SM.ipV ((bosF SM z x).2.2) (η x) -
      ∑ γ, pd (matFlux z SM X η γ) γ x := by
  simp only [DnJ_eq_dens, DhJ_eq_densH]
  simp only [volM_eq_rho]
  -- the divergence of the flux
  have hdens : ∀ γ δ, DifferentiableAt ℝ (fun y => dens z y γ δ) x := fun γ δ =>
    ((contDiff_pi.1 (contDiff_pi.1 (contDiff_dens z) γ) δ).differentiable (by simp)) x
  have hXd : ∀ δ, DifferentiableAt ℝ (fun y => X y δ) x := fun δ =>
    ((contDiff_pi.1 hX δ).differentiable (by simp)) x
  have hdH : ∀ γ, DifferentiableAt ℝ (fun y => densH z y γ) x := fun γ =>
    ((contDiff_densH z γ).differentiable (by simp)) x
  have hηd : DifferentiableAt ℝ η x := (hη.differentiable (by simp)) x
  have hpdX : ∀ γ δ, pd (fun y => X y δ) γ x = pd X γ x δ := fun γ δ =>
    pd_apply ((hX.differentiable (by simp)) x) γ δ
  have hflux : ∀ γ, pd (matFlux z SM X η γ) γ x =
      ∑ δ, (SM.ipG (pd (fun y => dens z y γ δ) γ x) (X x δ) +
        SM.ipG (dens z x γ δ) (pd X γ x δ)) +
      2 * (SM.ipV (pd (fun y => densH z y γ) γ x) (η x) + SM.ipV (densH z x γ) (pd η γ x)) := by
    intro γ
    have h1 : ∀ δ, DifferentiableAt ℝ (fun y => SM.ipG (dens z y γ δ) (X y δ)) x := fun δ => by
      have : (fun y => SM.ipG (dens z y γ δ) (X y δ)) =
          fun y => bilinCLM SM.ipG (dens z y γ δ) (X y δ) := rfl
      rw [this]
      exact ((bilinCLM SM.ipG).differentiableAt.comp x (hdens γ δ)).clm_apply (hXd δ)
    have h2 : DifferentiableAt ℝ (fun y => 2 * SM.ipV (densH z y γ) (η y)) x := by
      have : (fun y => 2 * SM.ipV (densH z y γ) (η y)) =
          fun y => 2 * bilinCLM SM.ipV (densH z y γ) (η y) := rfl
      rw [this]
      exact (((bilinCLM SM.ipV).differentiableAt.comp x (hdH γ)).clm_apply hηd).const_mul 2
    have hd : DifferentiableAt ℝ (matFlux z SM X η γ) x :=
      (DifferentiableAt.fun_sum fun δ _ => h1 δ).add h2
    refine pd_eq_of_line hd ?_
    have hl1 : ∀ δ, HasDerivAt (fun s : ℝ => SM.ipG (dens z (x + s • ev γ) γ δ)
        (X (x + s • ev γ) δ)) (SM.ipG (pd (fun y => dens z y γ δ) γ x) (X x δ) +
          SM.ipG (dens z x γ δ) (pd X γ x δ)) 0 := by
      intro δ
      have h := hasDerivAt_bilin SM.ipG (hasDerivAt_line0 (hdens γ δ) γ)
        (hasDerivAt_line0 (hXd δ) γ)
      simp only [zero_smul, add_zero] at h
      rw [← hpdX γ δ]
      exact h
    have hl2 : HasDerivAt (fun s : ℝ => 2 * SM.ipV (densH z (x + s • ev γ) γ) (η (x + s • ev γ)))
        (2 * (SM.ipV (pd (fun y => densH z y γ) γ x) (η x) + SM.ipV (densH z x γ) (pd η γ x)))
        0 := by
      have h := hasDerivAt_bilin SM.ipV (hasDerivAt_line0 (hdH γ) γ) (hasDerivAt_line0 hηd γ)
      simp only [zero_smul, add_zero] at h
      exact h.const_mul 2
    unfold matFlux
    exact (HasDerivAt.fun_sum fun δ _ => hl1 δ).add hl2
  simp only [hflux]
  -- the residual rows
  have hJ : ∀ δ, densJ SM z x δ = (2 : ℝ) • hV.μ (z.H x) (densH z x δ) := by
    intro δ
    unfold densJ densH Jf
    simp only [hV.J_eq, map_smul, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    simp only [smul_smul]
    congr 1
    ring
  have hR : ∀ δ, densR SM z x δ = ∑ γ, (pd (fun y => dens z y γ δ) γ x + ⁅z.A x γ, dens z x γ δ⁆) -
      (2 : ℝ) • hV.μ (z.H x) (densH z x δ) := by
    intro δ
    rw [densR_eq, ← hJ δ]
    congr 1
    rw [ymDensity_eq z x δ]
    rfl
  have hH : rho z x • (bosF SM z x).2.2 =
      ∑ β, (pd (fun y => densH z y β) β x + ⁅z.A x β, densH z x β⁆) -
        rho z x • ((2 * SM.lamH * (SM.ipV (z.H x) (z.H x) - SM.vH ^ 2)) • z.H x) := by
    rw [div_densH z x, ← smul_sub]
    congr 1
    show higgsRes (z.jet x).A (z.jet x).dA (z.jet x).H (z.jet x).dH (z.jet x).ddH (z.gi x)
      (chr (z.gi x) (z.dg x)) (SM.SH (z.g x) (z.gi x) (z.H x) (z.ψ x) (z.ψb x)) = _
    unfold higgsRes
    rw [hV.SH_eq]
  have hHr : 2 * rho z x * SM.ipV ((bosF SM z x).2.2) (η x) =
      2 * SM.ipV (rho z x • (bosF SM z x).2.2) (η x) := by
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul]; ring
  rw [hHr, hH]
  simp only [hR, map_sub, map_sum, map_add, LinearMap.sub_apply, LinearMap.add_apply,
    LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  have hc1 : ∑ δ, ∑ γ, SM.ipG (pd (fun y => dens z y γ δ) γ x) (X x δ) =
      ∑ γ, ∑ δ, SM.ipG (pd (fun y => dens z y γ δ) γ x) (X x δ) := Finset.sum_comm
  have hc2 : ∑ δ, ∑ γ, SM.ipG ⁅z.A x γ, dens z x γ δ⁆ (X x δ) =
      ∑ γ, ∑ δ, SM.ipG ⁅z.A x γ, dens z x γ δ⁆ (X x δ) := Finset.sum_comm
  rw [hc1, hc2]
  ring_nf
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul]
  ring

end

end GenMatEuler

end RenewalGeometry
