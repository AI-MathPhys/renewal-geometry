/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.StandardModel.RenewalCommonAction
import RenewalGeometry.StandardModel.FiniteStandardModelSourceNativeEmergenceExact

/-!
# Renewal realization of the finite Einstein–Standard-Model interface
  (`prop:renewal-interface`; Einstein–Standard-Model action-closure manuscript)

`prop:renewal-interface`: the companion constructions realize `def:finite-interface` on a
selected Standard-Model branch, i.e. they provide a nonempty family of finite interfaces with the
structural bundle content and the common-action normalization required by (I1)–(I5).

`renewalInterface n θ h hh : TabulatedFiniteInterface h` is such an interface, for every lattice
size `n ≥ 1`, every coefficient bank `θ` (Yukawa sectors `u, d, e`) and every cutoff `h > 0`, on
the minimal branch of `tab:SM-representations`.  Every field is a genuine object built in
`RenewalLatticeCarrier.lean` and `RenewalCommonAction.lean`:

* (I1) sites: the periodic lattice `(ℤ/n)⁴`; `𝒬_h = ℝ^{sites × coordinates}`
  (`RenewalRealization.Config`); local coframes `e(x) = L(p(x))U(p(x))` from sixteen chart
  variables per site (oriented, time-oriented, `chartCoframe_zero = 1`);
* (I2) the table packet of the minimal branch (`TabulatedFiniteInterface.ofTable`), gauge group
  `S(U(3)×U(2))` with its `ℤ₆` presentation, three generations, the weak Higgs doublet;
* (I3) the incidence operator `diracOp`: link-transported lattice differences in the table
  representation plus the covariant Yukawa blocks of `lem:SM-descent` with the bank's
  `Y_u, Y_d, Y_e`; the coefficient bank is `θ`;
* (I4) the common action `S_{g,h} + 1 · S_{SM,h}` (`commonActionR`), differentiable on `𝒬_h` and
  exactly invariant under all site gauges `Grid → G_SM`;
* (I5) the positive cell-volume Gram `h⁴ ⟨·,·⟩`, positive definite on all variation directions.

`renewal_interface` records these identifications; `renewal_interface_structural` ties the
generation factor and the gauge-quotient presentation to the companion structural packet
`finiteStandardModel_sourceNative_emergence` (its endpoint generation rank `3` and the quotient
`smGaugeQuotientEquiv`).

Disclosed renderings: the selected branch is the minimal one (no `ν_R`; a Majorana block is
antilinear and cannot be a block of the `ℂ`-linear incidence operator of the Lean encoding); the
interface encoding's fermion carrier has no spacetime-spinor index, so the incidence operator is
the internal (generation × table-row) one; the plaquettes are taken in Wilson form (see
`RenewalCommonAction.lean`); the gauge links are matrices in the defining representation
`M₃(ℂ) × M₂(ℂ)` of `G_SM` (the group itself is not a vector space).
-/

open Matrix

noncomputable section

namespace RenewalGeometry
namespace RenewalRealization

open ShiftedJetAction (Grid unitVec)
open FiniteInterfaceTable SMDescentYukawa
open scoped RealInnerProductSpace

variable {n : ℕ} [NeZero n]

/-- The positive cell-volume Gram `h⁴ ⟨·,·⟩` on `𝒬_h`. -/
def cellGram (h : ℝ) : Config n →ₗ[ℝ] Config n := (h ^ 4) • LinearMap.id

/-- **The renewal realization of `def:finite-interface`** at cutoff `h > 0` on the lattice
`(ℤ/n)⁴`, with coefficient bank `θ`, on the minimal Standard-Model branch. -/
def renewalInterface (n : ℕ) [NeZero n] (θ : CoefficientBank (Fin 3)) (h : ℝ) (hh : 0 < h) :
    TabulatedFiniteInterface h :=
  TabulatedFiniteInterface.ofTable h .minimal (Grid n) (Config n)
    (fun q x => frameE q x)
    (fun q x => det_chartCoframe_pos (prm q x))
    (fun q x => chartCoframe_timeOriented (prm q x))
    (fun q x => hig q x) (Fin 3) θ
    (fun q => diracOp θ h q)
    gaugeAct
    (fun γ q x => by
      rw [hig_gaugeAct]
      rfl)
    (fun γ q ψ x g => diracFun_covariant θ h γ q ψ x g)
    (gravityActionR θ h) (matterActionR θ h) 1 one_pos
    (differentiable_commonActionR θ h)
    (fun γ q => commonActionR_gauge θ h γ q)
    ⊤ (cellGram h)
    (fun u v => by
      simp only [cellGram, LinearMap.smul_apply, LinearMap.id_apply, real_inner_smul_left,
        real_inner_smul_right])
    (fun v => by
      simp only [cellGram, LinearMap.smul_apply, LinearMap.id_apply, real_inner_smul_right]
      exact mul_nonneg (by positivity) real_inner_self_nonneg)
    (fun v _ hv => by
      simp only [cellGram, LinearMap.smul_apply, LinearMap.id_apply, real_inner_smul_right,
        real_inner_self_eq_norm_sq]
      exact mul_pos (by positivity) (pow_pos (norm_pos_iff.mpr hv) 2))

section Facts

variable (θ : CoefficientBank (Fin 3)) (h : ℝ) (hh : 0 < h)

@[simp] theorem renewalInterface_branch : (renewalInterface n θ h hh).branch = .minimal := rfl

@[simp] theorem renewalInterface_relativeNormalization :
    (renewalInterface n θ h hh).relativeNormalization = 1 := rfl

theorem renewalInterface_coefficients : (renewalInterface n θ h hh).coefficients = θ := rfl

theorem renewalInterface_gravityAction :
    (renewalInterface n θ h hh).gravityAction = gravityActionR θ h := rfl

theorem renewalInterface_matterAction :
    (renewalInterface n θ h hh).matterAction = matterActionR θ h := rfl

theorem renewalInterface_coframe (q : Config n) (x : Grid n) :
    (renewalInterface n θ h hh).coframe q x = chartCoframe (prm q x) := rfl

end Facts

/-- **`prop:renewal-interface`** (realization statement).  For every lattice size `n ≥ 1`, every
coefficient bank `θ` and every cutoff `h > 0`, `renewalInterface n θ h hh` is a finite
Einstein–Standard-Model interface (`def:finite-interface`, ledger encoding
`TabulatedFiniteInterface`) on the minimal Standard-Model branch, whose data are:

* (I1) the local coframes `e(x) = chartCoframe(p(x))` of the configuration, with Lorentzian
  reconstructed metric (`det g < 0`), the flat coframe at the origin of the chart;
* (I2) the one-generation carrier of dimension `15` with the table representation (fermion
  representation and chirality determined by `tab:SM-representations`);
* (I3) the coefficient bank `θ` and the incidence operator `diracOp θ h`;
* (I4) the common action `S_h = S_{g,h} + ν S_{SM,h}` with physical relative normalization
  `ν = 1`, `S_{g,h} = gravityActionR θ h` (the Palatini–Cartan action of the coframes with the
  `1/(2κ)`, `Λ/κ` coefficients) and `S_{SM,h} = matterActionR θ h` (Yang–Mills + Higgs +
  Dirac/Yukawa);
* (I5) the positive Gram `h⁴ ⟨·,·⟩` (`gram = h⁴ id`) on the retained directions `⊤`.

In particular the family of such interfaces is nonempty at every cutoff. -/
theorem renewal_interface (θ : CoefficientBank (Fin 3)) (h : ℝ) (hh : 0 < h) :
    let I := renewalInterface n θ h hh
    I.branch = .minimal ∧
    (∀ q x, I.coframe q x = chartCoframe (prm q x)) ∧
    (∀ q x, (I.metric q x).det < 0) ∧
    (∀ x, I.coframe 0 x = 1) ∧
    Module.finrank ℂ I.OneGeneration = 15 ∧
    I.coefficients = θ ∧
    I.relativeNormalization = 1 ∧
    (∀ q, I.action q = gravityActionR θ h q + matterActionR θ h q) ∧
    (∀ γ q, I.action (I.gaugeAct γ q) = I.action q) ∧
    I.retained = ⊤ ∧ (∀ v, I.gram v = (h ^ 4) • v) := by
  intro I
  refine ⟨rfl, fun _ _ => rfl, fun q x => I.metric_det_neg q x, fun x => ?_,
    I.finrank_oneGeneration_minimal rfl, rfl, rfl, fun q => ?_, fun γ q => I.action_gaugeAct γ q,
    rfl, fun v => rfl⟩
  · show chartCoframe (prm 0 x) = 1
    have : prm (0 : Config n) x = 0 := by funext a b; rfl
    rw [this, chartCoframe_zero]
  · show gravityActionR θ h q + 1 * matterActionR θ h q = _
    rw [one_mul]

/-- The family of finite interfaces is nonempty at every positive cutoff. -/
theorem renewal_interface_nonempty (h : ℝ) (hh : 0 < h) : Nonempty (TabulatedFiniteInterface h) :=
  ⟨renewalInterface 1 ⟨1, 0, 1, 1, 1, 1, 1, fun _ => 0⟩ h hh⟩

/-- **Structural provenance** (`prop:renewal-interface`, the Standard-Model packet).  Under the
hypotheses of `finiteStandardModel_sourceNative_emergence`, the companion structural certificate
exists, and the realized interface carries exactly its structural data: the generation factor of
the interface's spinor fields has the certificate's endpoint generation rank
(`finrank ker sumF = 3`), its Higgs doublet carries the weak
representation `repH = U₂` of the descent packet, and its fermion representation is the table
representation of the packet's rows. -/
theorem renewal_interface_structural
    {hh' e panel selected A B eY : Type}
    [Fintype hh'] [Fintype e] [Fintype panel] [Fintype eY]
    [Ring A] [StarRing A] [Ring B] [StarRing B]
    (L : AdmissibleLoadedSubhierarchyData hh' e panel selected A B eY)
    {Hc : Type} [Fintype Hc] [Nonempty Hc] [DecidableEq Hc]
    (u : Matrix (Fin 7) (Fin 7) ℂ)
    (hsupp : InternalAssembly.ColourSupported u)
    (hcol : 0 < InternalAssembly.omega7 u)
    (D0 Gamma : Matrix Hc Hc ℂ)
    (hDl : D0ᴴ * D0 = 1) (hDr : D0 * D0ᴴ = 1)
    (hself : D0ᴴ = D0) (hodd : Gamma * D0 = -(D0 * Gamma))
    (hGamma : Gamma * Gamma = 1)
    (t weakHiggs : Fin 2 → ℂ)
    (hind : t 0 * weakHiggs 1 - t 1 * weakHiggs 0 ≠ 0)
    (hover : (∑ m, star (t m) * weakHiggs m) ≠ 0)
    (T : DetIncidence.Shadow) (hT : DetIncidence.FullyAlternating T)
    (hdet : 0 < DetIncidence.mdet T)
    (θ : CoefficientBank (Fin 3)) (h : ℝ) (hh : 0 < h) :
    let I := renewalInterface n θ h hh
    Nonempty (FiniteStandardModelSourceNativeCertificate L u D0 Gamma t weakHiggs T) ∧
    Module.finrank ℂ (LinearMap.ker SMActive.sumF) = Fintype.card (Fin 3) ∧
    (∀ g v, higgsRep g v = repH g *ᵥ v) ∧
    (∀ g v, I.fermionRep g v = tableRep .minimal g *ᵥ v) := by
  intro I
  refine ⟨finiteStandardModel_sourceNative_emergence L u hsupp hcol D0 Gamma hDl hDr hself hodd
    hGamma t weakHiggs hind hover T hT hdet, ?_, fun g v => rfl, fun g v => rfl⟩
  rw [SMActive.generation_rank, Fintype.card_fin]

/-! ### Non-vacuity -/

/-- A concrete member of the family (single-site lattice, unit couplings and Yukawa matrices,
`h = 1`): the flat coframe at the origin of the chart and the common-action normalization. -/
example : (∀ x, (renewalInterface 1 ⟨1, 0, 1, 1, 1, 1, 1, fun _ => 1⟩ 1 one_pos).coframe 0 x = 1) ∧
    (renewalInterface 1 ⟨1, 0, 1, 1, 1, 1, 1, fun _ => 1⟩ 1 one_pos).relativeNormalization = 1 :=
  ⟨(renewal_interface _ 1 one_pos).2.2.2.1, rfl⟩

end RenewalRealization
end RenewalGeometry
