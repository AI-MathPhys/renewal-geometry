/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.Lorentz.LorentzNaturalBivectorClassificationExact

/-!
# The local curvature-linear gravitational class
  (`def:main-gravitational-class`, `eq:main-phv-densities`; emergent-spacetime manuscript)

`def:main-gravitational-class`: the gravitational class consists of local polynomial
four-form densities in an oriented coframe `e` and a metric-compatible Lorentz connection
`ω` whose curvature-dependent part has bidegree `(2,1)` in `(e, R)` and whose
curvature-independent part has degree four in `e`; the coefficients are spacetime-constant
real scalars; the only admitted internal contractions are the Lorentz metric `η`, its
oriented volume tensor `ε` and the represented scalar multiplicity commutant; no inverse
coframe, independent torsion polynomial, derivative of curvature, background tensor or
matter field is admitted.

Finite-dimensional algebraic model (the one used by
`LorentzNaturalBivectorClassificationExact.lean` for `thm:main-gravitational-classification`):

* `GravitationalClassDensity` — a member of the class.  Since `e ∧ e` and `R` both take
  values in `Λ²ℝ^{1,3}` (carrier `BivectorIndex`) and the spacetime four-form part of a
  bidegree-`(2,1)` term is fixed by the wedge `e^I ∧ e^J ∧ R^{KL}`, the curvature-linear
  part is exactly a spacetime-constant real bilinear pairing `pairing` of the coframe
  bivector with the curvature bivector (its internal coefficient tensor
  `c_{IJKL} e^I ∧ e^J ∧ R^{KL}`); the curvature-free part is an alternating four-form
  `volume` of the coframe (its coefficient tensor `c_{IJKL} e^I ∧ e^J ∧ e^K ∧ e^L`).
  The exclusions of the definition are the shape of the structure: there is no slot for an
  inverse coframe, a torsion polynomial, a curvature derivative, a background tensor or a
  matter field, and the coefficients are constants, not functions on spacetime.
* `GravitationalClassDensity.IsLorentzNatural` — the internal contractions are built from
  `η`, `ε` and scalars only: the pairing is invariant under the induced action of every
  proper Lorentz matrix on the bivector carrier (this is the "Lorentz natural" hypothesis
  of `thm:main-gravitational-classification`; the scalar residual commutant is the
  absence of any further internal index on the carrier).
* `holstDensity`, `palatiniDensity`, `volumeDensity` — the three densities of
  `eq:main-phv-densities`: `L_Holst = e^I ∧ e^J ∧ R_{IJ}` (`η`-contraction),
  `L_Palatini = ½ ε_{IJKL} e^I ∧ e^J ∧ R^{KL}` (`ε`-contraction),
  `L_vol = (1/4!) ε_{IJKL} e^I ∧ e^J ∧ e^K ∧ e^L = det e`.
* `GravitationalClassDensity.ofCoefficients` and
  `GravitationalClassDensity.classification` — every Lorentz-natural member of the class is
  `α L_Holst + β L_Palatini + λ L_vol` with unique real coefficients
  (`thm:main-gravitational-classification`, restated on the named class).

Not modelled (disclosed): the comparison of densities modulo exact terms whose variations
vanish on compactly supported bulk tests, and the separate retention of boundary
functionals — these concern the variational use of the densities, not the pointwise
algebraic class classified here.
-/

open Matrix

namespace RenewalGeometry

open BivectorRotationCommutant

noncomputable section

/-- `def:main-gravitational-class`: a member of the local curvature-linear gravitational
class — a spacetime-constant real bilinear pairing of the coframe bivector `e ∧ e` with
the curvature `R` on the bivector carrier (the bidegree-`(2,1)` part
`c_{IJKL} e^I ∧ e^J ∧ R^{KL}`) together with an alternating four-form of the coframe (the
curvature-free degree-four part).  No inverse coframe, torsion polynomial, curvature
derivative, background tensor or matter field enters. -/
structure GravitationalClassDensity where
  /-- the bidegree-`(2,1)` coefficient tensor `c_{IJKL}` of `e^I ∧ e^J ∧ R^{KL}`. -/
  pairing : Matrix BivectorIndex BivectorIndex ℝ
  /-- the curvature-independent degree-four coframe density. -/
  volume : (Fin 4 → ℝ) [⋀^Fin 4]→ₗ[ℝ] ℝ

namespace GravitationalClassDensity

@[ext] theorem ext {D D' : GravitationalClassDensity} (hp : D.pairing = D'.pairing)
    (hv : D.volume = D'.volume) : D = D' := by
  cases D; cases D'
  simp only at hp hv
  subst hp; subst hv
  rfl

/-- Lorentz naturality of a member of the class: its internal contractions use only the
Lorentz metric, the oriented volume tensor and scalars, i.e. the pairing is invariant
under the induced action of every proper Lorentz matrix on the bivector carrier. -/
def IsLorentzNatural (D : GravitationalClassDensity) : Prop :=
  ∀ Λ : Matrix (Fin 4) (Fin 4) ℝ, IsProperLorentz Λ →
    (inducedBivectorAction Λ)ᵀ * D.pairing * inducedBivectorAction Λ = D.pairing

/-- The density with given coefficients `α L_Holst + β L_Palatini + λ L_vol`. -/
def ofCoefficients (α β lam : ℝ) : GravitationalClassDensity where
  pairing := α • metricPairing + β • epsilonPairing
  volume := lam • (Pi.basisFun ℝ (Fin 4)).det

end GravitationalClassDensity

/-- `L_Holst = e^I ∧ e^J ∧ R_{IJ}` (`eq:main-phv-densities`): the `η`-contraction. -/
def holstDensity : GravitationalClassDensity :=
  GravitationalClassDensity.ofCoefficients 1 0 0

/-- `L_Palatini = ½ ε_{IJKL} e^I ∧ e^J ∧ R^{KL}` (`eq:main-phv-densities`): the
`ε`-contraction. -/
def palatiniDensity : GravitationalClassDensity :=
  GravitationalClassDensity.ofCoefficients 0 1 0

/-- `L_vol = (1/4!) ε_{IJKL} e^I ∧ e^J ∧ e^K ∧ e^L = det e` (`eq:main-phv-densities`). -/
def volumeDensity : GravitationalClassDensity :=
  GravitationalClassDensity.ofCoefficients 0 0 1

@[simp] theorem holstDensity_pairing : holstDensity.pairing = metricPairing := by
  simp [holstDensity, GravitationalClassDensity.ofCoefficients]

@[simp] theorem palatiniDensity_pairing : palatiniDensity.pairing = epsilonPairing := by
  simp [palatiniDensity, GravitationalClassDensity.ofCoefficients]

@[simp] theorem volumeDensity_volume :
    volumeDensity.volume = (Pi.basisFun ℝ (Fin 4)).det := by
  simp [volumeDensity, GravitationalClassDensity.ofCoefficients]

namespace GravitationalClassDensity

@[simp] theorem ofCoefficients_pairing (α β lam : ℝ) :
    (ofCoefficients α β lam).pairing = α • metricPairing + β • epsilonPairing := rfl

@[simp] theorem ofCoefficients_volume (α β lam : ℝ) :
    (ofCoefficients α β lam).volume = lam • (Pi.basisFun ℝ (Fin 4)).det := rfl

/-- **`thm:main-gravitational-classification` on the named class**: every Lorentz-natural
member of the local curvature-linear gravitational class is
`α L_Holst + β L_Palatini + λ L_vol` with unique real coefficients
(`eq:main-phv-classification`, `eq:main-phv-coefficients`). -/
theorem classification (D : GravitationalClassDensity) (hD : D.IsLorentzNatural) :
    ∃! c : ℝ × ℝ × ℝ, D = ofCoefficients c.1 c.2.1 c.2.2 := by
  obtain ⟨c, hc, huniq⟩ := gravitational_score_classification D.pairing D.volume hD
  refine ⟨c, GravitationalClassDensity.ext hc.1 hc.2, ?_⟩
  intro c' hc'
  refine huniq c' ⟨?_, ?_⟩
  · rw [hc']; rfl
  · rw [hc']; rfl

/-- The coefficients of a Lorentz-natural member of the class are determined by its
pairing and volume parts alone (no other slot exists in the class). -/
theorem coefficients_unique {α β lam α' β' lam' : ℝ}
    (h : ofCoefficients α β lam = ofCoefficients α' β' lam') :
    α = α' ∧ β = β' ∧ lam = lam' := by
  have hp := congrArg pairing h
  have hv := congrArg volume h
  simp only [ofCoefficients_pairing, ofCoefficients_volume] at hp hv
  obtain ⟨h1, h2⟩ := pairing_coefficients_unique hp
  refine ⟨h1, h2, ?_⟩
  have h3 := congrArg (fun f => f (Pi.basisFun ℝ (Fin 4))) hv
  simp only [AlternatingMap.smul_apply, Module.Basis.det_self, smul_eq_mul, mul_one] at h3
  exact h3

end GravitationalClassDensity

end

end RenewalGeometry
