/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.EinsteinSMReducedClosure

/-!
# Smoothness of the first-variation covectors on the jet chart
  (Einstein–Standard-Model action-closure manuscript; infrastructure for
  `prop:variation-continuity` and `cor:strong-solution-upgrade`)

The first-variation covectors `gravCov`, `bosonCov`, `diracCov` (`EinsteinSMGravityFirstOrder`,
`EinsteinSMBosonicVariation`, `EinsteinSMFermionicContinuity`) are finite sums of coefficient
maps `Φ(e)` (multilinear maps into covectors on test jets, depending on the coframe value `e`)
evaluated on the jet packets.  The library proves the coefficient maps continuous on the
nondegenerate chart `coframeGL`; here they are proved `C^n` for every `n`:

* `contDiffOn_ymMetCoeff`, …, `contDiffOn_strongCoeff2`, `contDiffOn_weakCoeff`: every
  coefficient map is `C^n` on `coframeGL` (finite-dimensional targets, `contDiffOn_clm_apply`,
  derivatives of the `C^∞` coefficients `ymCoeff`, `higgsCoeff`, `volFactor`, `ehBilin`,
  `kinCoeff`, `potCoeff`);
* **`contDiffOn_gravCov`, `contDiffOn_bosonCov`, `contDiffOn_diracCov`**: the covector maps
  `R ↦ Cov(R) ∈ (RJet →L ℝ)` are `C^n` on the open jet chart `jetGL`.
-/

open MeasureTheory Filter Topology Set
open scoped ContDiff

noncomputable section

set_option synthInstance.maxSize 1024

namespace RenewalGeometry
namespace EinsteinSM
namespace CovSmooth

variable {C : Type} [Fintype C] {n : WithTop ℕ∞}

theorem contDiffOn_fderiv_ymCoeff (j : Fin 3) :
    ContDiffOn ℝ n (fderiv ℝ (ymCoeff j)) coframeGL :=
  (contDiffOn_ymCoeff j (n := n + 1)).fderiv_of_isOpen isOpen_coframeGL le_rfl

theorem contDiffOn_fderiv_higgsCoeff : ContDiffOn ℝ n (fderiv ℝ higgsCoeff) coframeGL :=
  (contDiffOn_higgsCoeff (n := n + 1)).fderiv_of_isOpen isOpen_coframeGL le_rfl

theorem contDiffOn_fderiv_volFactor : ContDiffOn ℝ n (fderiv ℝ volFactor) coframeGL :=
  (contDiffOn_volFactor (n := n + 1)).fderiv_of_isOpen isOpen_coframeGL le_rfl

theorem contDiff_fderiv_metricLiftL : ContDiff ℝ n (fderiv ℝ metricLiftL) :=
  (contDiff_metricLiftL (n := n + 1)).fderiv_right le_rfl

theorem contDiff_metricLiftL_apply (k : CoframeFibre) :
    ContDiff ℝ n fun e => metricLiftL e k :=
  contDiff_metricLiftL.clm_apply contDiff_const

theorem contDiff_dLiftL_apply (d : CoframeJet) (k : CoframeFibre) :
    ContDiff ℝ n fun e => dLiftL e d k :=
  contDiff_pi.mpr fun _ => (contDiff_fderiv_metricLiftL.clm_apply contDiff_const).clm_apply
    contDiff_const

theorem contDiff_liftJetL_apply (d : CoframeJet) : ContDiff ℝ n fun e => liftJetL e d :=
  contDiff_pi.mpr fun _ => contDiff_metricLiftL.clm_apply contDiff_const

/-! ### Bosonic coefficient maps -/

theorem contDiffOn_ymMetCoeff (j : Fin 3) :
    ContDiffOn ℝ n (ymMetCoeff (C := C) j) coframeGL := by
  refine contDiffOn_clm_apply.mpr fun F => contDiffOn_clm_apply.mpr fun F' =>
    contDiffOn_clm_apply.mpr fun T => ?_
  exact (((contDiffOn_fderiv_ymCoeff j).clm_apply (contDiff_metricLiftL_apply T.e).contDiffOn).clm_apply
    contDiffOn_const).clm_apply contDiffOn_const

theorem contDiffOn_ymDaCoeff (j : Fin 3) : ContDiffOn ℝ n (ymDaCoeff (C := C) j) coframeGL := by
  have hY := contDiffOn_ymCoeff j (n := n)
  refine contDiffOn_clm_apply.mpr fun F => contDiffOn_clm_apply.mpr fun T => ?_
  exact ((hY.clm_apply contDiffOn_const).clm_apply contDiffOn_const).add
    ((hY.clm_apply contDiffOn_const).clm_apply contDiffOn_const)

theorem contDiffOn_ymACoeff (j : Fin 3) : ContDiffOn ℝ n (ymACoeff (C := C) j) coframeGL := by
  have hY := contDiffOn_ymCoeff j (n := n)
  refine contDiffOn_clm_apply.mpr fun A => contDiffOn_clm_apply.mpr fun F =>
    contDiffOn_clm_apply.mpr fun T => ?_
  exact ((hY.clm_apply contDiffOn_const).clm_apply contDiffOn_const).add
    ((hY.clm_apply contDiffOn_const).clm_apply contDiffOn_const)

theorem contDiffOn_higgsMetCoeff : ContDiffOn ℝ n (higgsMetCoeff (C := C)) coframeGL := by
  refine contDiffOn_clm_apply.mpr fun K => contDiffOn_clm_apply.mpr fun K' =>
    contDiffOn_clm_apply.mpr fun T => ?_
  exact ((contDiffOn_fderiv_higgsCoeff.clm_apply (contDiff_metricLiftL_apply T.e).contDiffOn).clm_apply
    contDiffOn_const).clm_apply contDiffOn_const

theorem contDiffOn_higgsDCoeff : ContDiffOn ℝ n (higgsDCoeff (C := C)) coframeGL := by
  have hY := contDiffOn_higgsCoeff (n := n)
  refine contDiffOn_clm_apply.mpr fun K => contDiffOn_clm_apply.mpr fun T => ?_
  exact ((hY.clm_apply contDiffOn_const).clm_apply contDiffOn_const).add
    ((hY.clm_apply contDiffOn_const).clm_apply contDiffOn_const)

theorem contDiffOn_higgsHCoeff : ContDiffOn ℝ n (higgsHCoeff (C := C)) coframeGL := by
  have hY := contDiffOn_higgsCoeff (n := n)
  refine contDiffOn_clm_apply.mpr fun H => contDiffOn_clm_apply.mpr fun K =>
    contDiffOn_clm_apply.mpr fun T => ?_
  exact ((hY.clm_apply contDiffOn_const).clm_apply contDiffOn_const).add
    ((hY.clm_apply contDiffOn_const).clm_apply contDiffOn_const)

theorem contDiffOn_higgsACoeff : ContDiffOn ℝ n (higgsACoeff (C := C)) coframeGL := by
  have hY := contDiffOn_higgsCoeff (n := n)
  refine contDiffOn_clm_apply.mpr fun A => contDiffOn_clm_apply.mpr fun K =>
    contDiffOn_clm_apply.mpr fun T => ?_
  exact ((hY.clm_apply contDiffOn_const).clm_apply contDiffOn_const).add
    ((hY.clm_apply contDiffOn_const).clm_apply contDiffOn_const)

theorem contDiffOn_potHCoeff : ContDiffOn ℝ n (potHCoeff (C := C)) coframeGL := by
  have hV := contDiffOn_volFactor (n := n)
  refine contDiffOn_clm_apply.mpr fun Y => contDiffOn_clm_apply.mpr fun T => ?_
  exact contDiffOn_const.mul hV

theorem contDiffOn_potVCoeff : ContDiffOn ℝ n (potVCoeff (C := C)) coframeGL := by
  refine contDiffOn_clm_apply.mpr fun s => contDiffOn_clm_apply.mpr fun T => ?_
  exact (contDiffOn_const.mul (contDiffOn_fderiv_volFactor.clm_apply
    (contDiff_metricLiftL_apply T.e).contDiffOn)).neg

/-! ### Gravitational coefficient maps -/

theorem contDiffOn_gravC1 : ContDiffOn ℝ n (gravC1 (C := C)) coframeGL := by
  refine contDiffOn_clm_apply.mpr fun d => contDiffOn_clm_apply.mpr fun d' =>
    contDiffOn_clm_apply.mpr fun T => ?_
  have hb : ContDiffOn ℝ n ehBilin coframeGL := contDiffOn_ehBilin
  have hfd : ContDiffOn ℝ n (fderiv ℝ ehBilin) coframeGL :=
    (contDiffOn_ehBilin (n := n + 1)).fderiv_of_isOpen isOpen_coframeGL le_rfl
  have hdl : ContDiffOn ℝ n (fun e => dLiftL e d T.e) coframeGL :=
    (contDiff_dLiftL_apply d T.e).contDiffOn
  show ContDiffOn ℝ n (fun e => fderiv ℝ ehBilin e (metricLiftL e T.e) d d' +
    ehBilin e (dLiftL e d T.e) d' + ehBilin e d' (dLiftL e d T.e)) coframeGL
  exact ((((hfd.clm_apply (contDiff_metricLiftL_apply T.e).contDiffOn).clm_apply
    contDiffOn_const).clm_apply contDiffOn_const).add
    ((hb.clm_apply hdl).clm_apply contDiffOn_const)).add
    ((hb.clm_apply contDiffOn_const).clm_apply hdl)

theorem contDiffOn_gravC2 : ContDiffOn ℝ n (gravC2 (C := C)) coframeGL := by
  refine contDiffOn_clm_apply.mpr fun d => contDiffOn_clm_apply.mpr fun T => ?_
  have hb : ContDiffOn ℝ n ehBilin coframeGL := contDiffOn_ehBilin
  have hl : ContDiffOn ℝ n (fun e => liftJetL e T.de) coframeGL :=
    (contDiff_liftJetL_apply T.de).contDiffOn
  show ContDiffOn ℝ n (fun e => ehBilin e (liftJetL e T.de) d + ehBilin e d (liftJetL e T.de))
    coframeGL
  exact ((hb.clm_apply hl).clm_apply contDiffOn_const).add
    ((hb.clm_apply contDiffOn_const).clm_apply hl)

theorem contDiffOn_gravC3 : ContDiffOn ℝ n (gravC3 (C := C)) coframeGL := by
  refine contDiffOn_clm_apply.mpr fun s => contDiffOn_clm_apply.mpr fun T => ?_
  show ContDiffOn ℝ n (fun e => s * fderiv ℝ volFactor e (metricLiftL e T.e)) coframeGL
  exact contDiffOn_const.mul (contDiffOn_fderiv_volFactor.clm_apply
    (contDiff_metricLiftL_apply T.e).contDiffOn)

/-! ### Fermionic coefficient maps -/

section Fermionic

variable {Ysec : Type} (FC : FermionCarrier Ysec)

theorem contDiffOn_weakCoeff : ContDiffOn ℝ n (weakCoeff (C := C)) coframeGL := by
  refine contDiffOn_clm_apply.mpr fun sU => contDiffOn_clm_apply.mpr fun τ =>
    contDiffOn_clm_apply.mpr fun W => ?_
  have hfd : ContDiffOn ℝ n (fderiv ℝ (kinCoeff (C := C))) coframeGL :=
    (contDiffOn_kinCoeff (n := n + 1)).fderiv_of_isOpen isOpen_coframeGL le_rfl
  have hk : ContDiffOn ℝ n (kinCoeff (C := C)) coframeGL := contDiffOn_kinCoeff
  show ContDiffOn ℝ n (fun e => fderiv ℝ kinCoeff e (metricLiftL e τ.1) sU.2 W +
    sU.1 * kinCoeff e (τ.2.1, τ.2.2) W) coframeGL
  exact (((hfd.clm_apply (contDiff_metricLiftL_apply τ.1).contDiffOn).clm_apply
    contDiffOn_const).clm_apply contDiffOn_const).add
    (contDiffOn_const.mul ((hk.clm_apply contDiffOn_const).clm_apply contDiffOn_const))

theorem contDiffOn_strongCoeff1 : ContDiffOn ℝ n (strongCoeff1 FC) coframeGL := by
  refine contDiffOn_clm_apply.mpr fun Y' => contDiffOn_clm_apply.mpr fun U =>
    contDiffOn_clm_apply.mpr fun T => ?_
  have hk : ContDiffOn ℝ n (kinCoeff (C := FC.C)) coframeGL := contDiffOn_kinCoeff
  have hp : ContDiffOn ℝ n (potCoeff FC) coframeGL := contDiffOn_potCoeff FC
  show ContDiffOn ℝ n (fun e => Y'.1.2.2.2 * kinCoeff e U (T.dΨ, T.dΨb) +
    potCoeff FC e Y'.1 T.Ψb U.2 + potCoeff FC e Y'.1 U.1 T.Ψ) coframeGL
  exact ((contDiffOn_const.mul ((hk.clm_apply contDiffOn_const).clm_apply contDiffOn_const)).add
    (((hp.clm_apply contDiffOn_const).clm_apply contDiffOn_const).clm_apply
      contDiffOn_const)).add
    (((hp.clm_apply contDiffOn_const).clm_apply contDiffOn_const).clm_apply contDiffOn_const)

theorem contDiffOn_strongCoeff2 : ContDiffOn ℝ n (strongCoeff2 FC) coframeGL := by
  refine contDiffOn_clm_apply.mpr fun Y' => contDiffOn_clm_apply.mpr fun Ψb =>
    contDiffOn_clm_apply.mpr fun Ψ => contDiffOn_clm_apply.mpr fun T => ?_
  have hp : ContDiffOn ℝ n (potCoeff FC) coframeGL := contDiffOn_potCoeff FC
  have hfd : ContDiffOn ℝ n (fderiv ℝ (potCoeff FC)) coframeGL :=
    (contDiffOn_potCoeff FC (n := n + 1)).fderiv_of_isOpen isOpen_coframeGL le_rfl
  have h1 : ContDiffOn ℝ n (fun e => ιde FC (dLiftL e Y'.1.1 T.e)) coframeGL :=
    ((ιde FC).contDiff.comp (contDiff_dLiftL_apply Y'.1.1 T.e)).contDiffOn
  have h2 : ContDiffOn ℝ n (fun e => ιde FC (liftJetL e T.de) + ιA FC T.A) coframeGL :=
    (((ιde FC).contDiff.comp (contDiff_liftJetL_apply T.de)).add contDiff_const).contDiffOn
  show ContDiffOn ℝ n (fun e => strongForm2 FC e Y' Ψb Ψ T) coframeGL
  unfold strongForm2
  exact (((((hfd.clm_apply (contDiff_metricLiftL_apply T.e).contDiffOn).clm_apply
    contDiffOn_const).clm_apply contDiffOn_const).clm_apply contDiffOn_const).add
    (((hp.clm_apply h1).clm_apply contDiffOn_const).clm_apply contDiffOn_const)).add
    (contDiffOn_const.mul (((hp.clm_apply h2).clm_apply contDiffOn_const).clm_apply
      contDiffOn_const)) |>.add
    (((hp.clm_apply contDiffOn_const).clm_apply contDiffOn_const).clm_apply contDiffOn_const)

end Fermionic

/-! ### The covector maps on the jet chart -/

theorem mapsTo_πe_jetGL : MapsTo (fun R : RJet C => πe R) (jetGL C) coframeGL := fun _ hR => hR

theorem contDiffOn_comp_πe {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {Φ : CoframeFibre → Z} (hΦ : ContDiffOn ℝ n Φ coframeGL) :
    ContDiffOn ℝ n (fun R : RJet C => Φ R.e) (jetGL C) :=
  hΦ.comp (πe (C := C)).contDiff.contDiffOn mapsTo_πe_jetGL

/-- **The gravitational covector is `C^n` on the jet chart.** -/
theorem contDiffOn_gravCov {Ysec : Type} (θ : CoefficientBank Ysec) :
    ContDiffOn ℝ n (fun R : RJet C => gravCov θ R) (jetGL C) := by
  have hde : ContDiffOn ℝ n (fun R : RJet C => R.de) (jetGL C) :=
    (πde (C := C)).contDiff.contDiffOn
  have h1 := ((contDiffOn_comp_πe (contDiffOn_gravC1 (C := C) (n := n))).clm_apply hde).clm_apply hde
  have h2 := (contDiffOn_comp_πe (contDiffOn_gravC2 (C := C) (n := n))).clm_apply hde
  have h3 := (contDiffOn_comp_πe (C := C) (contDiffOn_gravC3 (C := C) (n := n))).clm_apply
    (contDiffOn_const (c := (1 : ℝ)) (s := jetGL C))
  exact ((h1.add h2).add (h3.const_smul (-(2 * θ.Lambda)))).const_smul (2 * θ.kappa)⁻¹

theorem contDiff_higgsQuad : ContDiff ℝ n higgsQuad := by
  show ContDiff ℝ n fun H => hInnerReL H H
  exact hInnerReL.contDiff.clm_apply contDiff_id

theorem contDiffOn_higgsMet_part :
    ContDiffOn ℝ n (fun R : RJet C => higgsMetCoeff (C := C) R.e R.K R.K) (jetGL C) := by
  have hK : ContDiffOn ℝ n (fun R : RJet C => R.K) (jetGL C) := (πK (C := C)).contDiff.contDiffOn
  have c1 : ContDiffOn ℝ n (fun R : RJet C => higgsMetCoeff (C := C) R.e) (jetGL C) :=
    contDiffOn_comp_πe contDiffOn_higgsMetCoeff
  have d1 : ContDiffOn ℝ n (fun R : RJet C => higgsMetCoeff (C := C) R.e R.K) (jetGL C) :=
    ContDiffOn.clm_apply c1 hK
  exact ContDiffOn.clm_apply d1 hK

theorem contDiffOn_higgsD_part :
    ContDiffOn ℝ n (fun R : RJet C => higgsDCoeff (C := C) R.e R.K) (jetGL C) := by
  have hK : ContDiffOn ℝ n (fun R : RJet C => R.K) (jetGL C) := (πK (C := C)).contDiff.contDiffOn
  have c2 : ContDiffOn ℝ n (fun R : RJet C => higgsDCoeff (C := C) R.e) (jetGL C) :=
    contDiffOn_comp_πe contDiffOn_higgsDCoeff
  exact ContDiffOn.clm_apply c2 hK

theorem contDiffOn_higgsH_part :
    ContDiffOn ℝ n (fun R : RJet C => higgsHCoeff (C := C) R.e R.H R.K) (jetGL C) := by
  have hK : ContDiffOn ℝ n (fun R : RJet C => R.K) (jetGL C) := (πK (C := C)).contDiff.contDiffOn
  have hH : ContDiffOn ℝ n (fun R : RJet C => R.H) (jetGL C) := (πH (C := C)).contDiff.contDiffOn
  have c3 : ContDiffOn ℝ n (fun R : RJet C => higgsHCoeff (C := C) R.e) (jetGL C) :=
    contDiffOn_comp_πe contDiffOn_higgsHCoeff
  have d3 : ContDiffOn ℝ n (fun R : RJet C => higgsHCoeff (C := C) R.e R.H) (jetGL C) :=
    ContDiffOn.clm_apply c3 hH
  exact ContDiffOn.clm_apply d3 hK

theorem contDiffOn_higgsA_part :
    ContDiffOn ℝ n (fun R : RJet C => higgsACoeff (C := C) R.e R.A R.K) (jetGL C) := by
  have hK : ContDiffOn ℝ n (fun R : RJet C => R.K) (jetGL C) := (πK (C := C)).contDiff.contDiffOn
  have hA : ContDiffOn ℝ n (fun R : RJet C => R.A) (jetGL C) := (πA (C := C)).contDiff.contDiffOn
  have c4 : ContDiffOn ℝ n (fun R : RJet C => higgsACoeff (C := C) R.e) (jetGL C) :=
    contDiffOn_comp_πe contDiffOn_higgsACoeff
  have d4 : ContDiffOn ℝ n (fun R : RJet C => higgsACoeff (C := C) R.e R.A) (jetGL C) :=
    ContDiffOn.clm_apply c4 hA
  exact ContDiffOn.clm_apply d4 hK

theorem contDiffOn_ym_part (j : Fin 3) :
    ContDiffOn ℝ n (fun R : RJet C => ymMetCoeff (C := C) j R.e R.F R.F +
      ymDaCoeff (C := C) j R.e R.F + ymACoeff (C := C) j R.e R.A R.F) (jetGL C) := by
  have hF : ContDiffOn ℝ n (fun R : RJet C => R.F) (jetGL C) := (πF (C := C)).contDiff.contDiffOn
  have hA : ContDiffOn ℝ n (fun R : RJet C => R.A) (jetGL C) := (πA (C := C)).contDiff.contDiffOn
  have c1 : ContDiffOn ℝ n (fun R : RJet C => ymMetCoeff (C := C) j R.e) (jetGL C) :=
    contDiffOn_comp_πe (contDiffOn_ymMetCoeff j)
  have c2 : ContDiffOn ℝ n (fun R : RJet C => ymDaCoeff (C := C) j R.e) (jetGL C) :=
    contDiffOn_comp_πe (contDiffOn_ymDaCoeff j)
  have c3 : ContDiffOn ℝ n (fun R : RJet C => ymACoeff (C := C) j R.e) (jetGL C) :=
    contDiffOn_comp_πe (contDiffOn_ymACoeff j)
  have d1 : ContDiffOn ℝ n (fun R : RJet C => ymMetCoeff (C := C) j R.e R.F) (jetGL C) :=
    ContDiffOn.clm_apply c1 hF
  have d3 : ContDiffOn ℝ n (fun R : RJet C => ymACoeff (C := C) j R.e R.A) (jetGL C) :=
    ContDiffOn.clm_apply c3 hA
  have e1 : ContDiffOn ℝ n (fun R : RJet C => ymMetCoeff (C := C) j R.e R.F R.F) (jetGL C) :=
    ContDiffOn.clm_apply d1 hF
  have e2 : ContDiffOn ℝ n (fun R : RJet C => ymDaCoeff (C := C) j R.e R.F) (jetGL C) :=
    ContDiffOn.clm_apply c2 hF
  have e3 : ContDiffOn ℝ n (fun R : RJet C => ymACoeff (C := C) j R.e R.A R.F) (jetGL C) :=
    ContDiffOn.clm_apply d3 hF
  exact (e1.add e2).add e3

theorem contDiffOn_pot_part {Y : Type} (θ : CoefficientBank Y) :
    ContDiffOn ℝ n (fun R : RJet C =>
      potHCoeff (C := C) R.e ((higgsQuad R.H - θ.vH ^ 2) • R.H) +
      potVCoeff (C := C) R.e ((higgsQuad R.H - θ.vH ^ 2) ^ 2)) (jetGL C) := by
  have hH : ContDiffOn ℝ n (fun R : RJet C => R.H) (jetGL C) := (πH (C := C)).contDiff.contDiffOn
  have hq : ContDiffOn ℝ n (fun R : RJet C => higgsQuad R.H - θ.vH ^ 2) (jetGL C) :=
    (contDiff_higgsQuad.comp_contDiffOn hH).sub contDiffOn_const
  have c1 : ContDiffOn ℝ n (fun R : RJet C => potHCoeff (C := C) R.e) (jetGL C) :=
    contDiffOn_comp_πe contDiffOn_potHCoeff
  have c2 : ContDiffOn ℝ n (fun R : RJet C => potVCoeff (C := C) R.e) (jetGL C) :=
    contDiffOn_comp_πe contDiffOn_potVCoeff
  have e1 : ContDiffOn ℝ n (fun R : RJet C =>
      potHCoeff (C := C) R.e ((higgsQuad R.H - θ.vH ^ 2) • R.H)) (jetGL C) :=
    ContDiffOn.clm_apply c1 (hq.smul hH)
  have e2 : ContDiffOn ℝ n (fun R : RJet C =>
      potVCoeff (C := C) R.e ((higgsQuad R.H - θ.vH ^ 2) ^ 2)) (jetGL C) :=
    ContDiffOn.clm_apply c2 (hq.pow 2)
  exact e1.add e2

theorem contDiffOn_ymMet_part (j : Fin 3) :
    ContDiffOn ℝ n (fun R : RJet C => ymMetCoeff (C := C) j R.e R.F R.F) (jetGL C) := by
  have hF : ContDiffOn ℝ n (fun R : RJet C => R.F) (jetGL C) := (πF (C := C)).contDiff.contDiffOn
  have c1 : ContDiffOn ℝ n (fun R : RJet C => ymMetCoeff (C := C) j R.e) (jetGL C) :=
    contDiffOn_comp_πe (contDiffOn_ymMetCoeff j)
  have d1 : ContDiffOn ℝ n (fun R : RJet C => ymMetCoeff (C := C) j R.e R.F) (jetGL C) :=
    ContDiffOn.clm_apply c1 hF
  exact ContDiffOn.clm_apply d1 hF

theorem contDiffOn_ymDa_part (j : Fin 3) :
    ContDiffOn ℝ n (fun R : RJet C => ymDaCoeff (C := C) j R.e R.F) (jetGL C) := by
  have hF : ContDiffOn ℝ n (fun R : RJet C => R.F) (jetGL C) := (πF (C := C)).contDiff.contDiffOn
  have c2 : ContDiffOn ℝ n (fun R : RJet C => ymDaCoeff (C := C) j R.e) (jetGL C) :=
    contDiffOn_comp_πe (contDiffOn_ymDaCoeff j)
  exact ContDiffOn.clm_apply c2 hF

theorem contDiffOn_ymA_part (j : Fin 3) :
    ContDiffOn ℝ n (fun R : RJet C => ymACoeff (C := C) j R.e R.A R.F) (jetGL C) := by
  have hF : ContDiffOn ℝ n (fun R : RJet C => R.F) (jetGL C) := (πF (C := C)).contDiff.contDiffOn
  have hA : ContDiffOn ℝ n (fun R : RJet C => R.A) (jetGL C) := (πA (C := C)).contDiff.contDiffOn
  have c3 : ContDiffOn ℝ n (fun R : RJet C => ymACoeff (C := C) j R.e) (jetGL C) :=
    contDiffOn_comp_πe (contDiffOn_ymACoeff j)
  have d3 : ContDiffOn ℝ n (fun R : RJet C => ymACoeff (C := C) j R.e R.A) (jetGL C) :=
    ContDiffOn.clm_apply c3 hA
  exact ContDiffOn.clm_apply d3 hF

theorem contDiffOn_potH_part {Y : Type} (θ : CoefficientBank Y) :
    ContDiffOn ℝ n (fun R : RJet C =>
      potHCoeff (C := C) R.e ((higgsQuad R.H - θ.vH ^ 2) • R.H)) (jetGL C) := by
  have hH : ContDiffOn ℝ n (fun R : RJet C => R.H) (jetGL C) := (πH (C := C)).contDiff.contDiffOn
  have hq : ContDiffOn ℝ n (fun R : RJet C => higgsQuad R.H - θ.vH ^ 2) (jetGL C) :=
    (contDiff_higgsQuad.comp_contDiffOn hH).sub contDiffOn_const
  have c1 : ContDiffOn ℝ n (fun R : RJet C => potHCoeff (C := C) R.e) (jetGL C) :=
    contDiffOn_comp_πe contDiffOn_potHCoeff
  exact ContDiffOn.clm_apply c1 (hq.smul hH)

theorem contDiffOn_potV_part {Y : Type} (θ : CoefficientBank Y) :
    ContDiffOn ℝ n (fun R : RJet C =>
      potVCoeff (C := C) R.e ((higgsQuad R.H - θ.vH ^ 2) ^ 2)) (jetGL C) := by
  have hH : ContDiffOn ℝ n (fun R : RJet C => R.H) (jetGL C) := (πH (C := C)).contDiff.contDiffOn
  have hq : ContDiffOn ℝ n (fun R : RJet C => higgsQuad R.H - θ.vH ^ 2) (jetGL C) :=
    (contDiff_higgsQuad.comp_contDiffOn hH).sub contDiffOn_const
  have c2 : ContDiffOn ℝ n (fun R : RJet C => potVCoeff (C := C) R.e) (jetGL C) :=
    contDiffOn_comp_πe contDiffOn_potVCoeff
  exact ContDiffOn.clm_apply c2 (hq.pow 2)

/-- **The bosonic covector is `C^n` on the jet chart.** -/
theorem contDiffOn_bosonCov {Y : Type} (θ : CoefficientBank Y) :
    ContDiffOn ℝ n (fun R : RJet C => bosonCov θ R) (jetGL C) := by
  refine contDiffOn_clm_apply.mpr fun T => ?_
  have e : (fun R : RJet C => bosonCov θ R T) = fun R =>
      (∑ j, gaugeScalars θ j * (ymMetCoeff (C := C) j R.e R.F R.F T +
        ymDaCoeff (C := C) j R.e R.F T + ymACoeff (C := C) j R.e R.A R.F T)) +
      (higgsMetCoeff (C := C) R.e R.K R.K T + higgsDCoeff (C := C) R.e R.K T +
        higgsHCoeff (C := C) R.e R.H R.K T + higgsACoeff (C := C) R.e R.A R.K T) +
      θ.lambdaH * (potHCoeff (C := C) R.e ((higgsQuad R.H - θ.vH ^ 2) • R.H) T +
        potVCoeff (C := C) R.e ((higgsQuad R.H - θ.vH ^ 2) ^ 2) T) := by
    funext R
    simp only [bosonCov, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_sum',
      Finset.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [e]
  have y1 := fun j => (contDiffOn_ymMet_part (C := C) (n := n) j).clm_apply
    (contDiffOn_const (c := T))
  have y2 := fun j => (contDiffOn_ymDa_part (C := C) (n := n) j).clm_apply
    (contDiffOn_const (c := T))
  have y3 := fun j => (contDiffOn_ymA_part (C := C) (n := n) j).clm_apply
    (contDiffOn_const (c := T))
  have b1 := (contDiffOn_higgsMet_part (C := C) (n := n)).clm_apply (contDiffOn_const (c := T))
  have b2 := (contDiffOn_higgsD_part (C := C) (n := n)).clm_apply (contDiffOn_const (c := T))
  have b3 := (contDiffOn_higgsH_part (C := C) (n := n)).clm_apply (contDiffOn_const (c := T))
  have b4 := (contDiffOn_higgsA_part (C := C) (n := n)).clm_apply (contDiffOn_const (c := T))
  have p1 := (contDiffOn_potH_part (C := C) (n := n) θ).clm_apply (contDiffOn_const (c := T))
  have p2 := (contDiffOn_potV_part (C := C) (n := n) θ).clm_apply (contDiffOn_const (c := T))
  have h1 : ContDiffOn ℝ n (fun R : RJet C => ∑ j, gaugeScalars θ j *
      (ymMetCoeff (C := C) j R.e R.F R.F T + ymDaCoeff (C := C) j R.e R.F T +
        ymACoeff (C := C) j R.e R.A R.F T)) (jetGL C) :=
    ContDiffOn.sum fun j _ => contDiffOn_const.mul (((y1 j).add (y2 j)).add (y3 j))
  exact (h1.add (((b1.add b2).add b3).add b4)).add (contDiffOn_const.mul (p1.add p2))

/-- **The fermionic covector is `C^n` on the jet chart.** -/
theorem contDiffOn_diracCov {Ysec : Type} (FC : FermionCarrier Ysec) (θ : CoefficientBank Ysec) :
    ContDiffOn ℝ n (fun R : RJet FC.C => diracCov FC θ R) (jetGL FC.C) := by
  have hpv : ContDiffOn ℝ n (fun R : RJet FC.C => potVar' FC θ R) (jetGL FC.C) := by
    have : (fun R : RJet FC.C => potVar' FC θ R) =
        fun R => (potVarL FC θ R + ((0, 0, FC.yukawa θ 0, 1) : PotVar FC), yukL FC θ) := by
      funext R; simp only [potVar', potVar_eq]
    rw [this]
    exact ((((potVarL FC θ).contDiff).add contDiff_const).prodMk contDiff_const).contDiffOn
  have hU : ContDiffOn ℝ n (fun R : RJet FC.C => pU FC R) (jetGL FC.C) :=
    (pU FC).contDiff.contDiffOn
  have hW : ContDiffOn ℝ n (fun R : RJet FC.C => pW FC R) (jetGL FC.C) :=
    (pW FC).contDiff.contDiffOn
  have hΨ : ContDiffOn ℝ n (fun R : RJet FC.C => R.Ψ) (jetGL FC.C) :=
    (πΨ (C := FC.C)).contDiff.contDiffOn
  have hΨb : ContDiffOn ℝ n (fun R : RJet FC.C => R.Ψb) (jetGL FC.C) :=
    (πΨb (C := FC.C)).contDiff.contDiffOn
  have h1 := ((contDiffOn_comp_πe (contDiffOn_strongCoeff1 FC (n := n))).clm_apply hpv).clm_apply hU
  have h2 := (((contDiffOn_comp_πe (contDiffOn_strongCoeff2 FC (n := n))).clm_apply hpv).clm_apply
    hΨb).clm_apply hΨ
  have hwk : ContDiffOn ℝ n (fun R : RJet FC.C => weakCoeff R.e ((1 : ℝ), pU FC R)) (jetGL FC.C) :=
    (contDiffOn_comp_πe (contDiffOn_weakCoeff (C := FC.C) (n := n))).clm_apply
      (contDiffOn_const.prodMk hU)
  have hflip : ContDiffOn ℝ n (fun R : RJet FC.C => (weakCoeff R.e ((1 : ℝ), pU FC R)).flip)
      (jetGL FC.C) :=
    (ContinuousLinearMap.flipₗᵢ ℝ (TestVal FC.C) (GradVal FC.C) ℝ).contDiff.comp_contDiffOn hwk
  have h3 : ContDiffOn ℝ n (fun R : RJet FC.C =>
      ((weakCoeff R.e ((1 : ℝ), pU FC R)).flip (pW FC R)).comp (πτ (C := FC.C))) (jetGL FC.C) :=
    (hflip.clm_apply hW).clm_comp contDiffOn_const
  exact (h1.add h2).add h3

end CovSmooth
end EinsteinSM
end RenewalGeometry
