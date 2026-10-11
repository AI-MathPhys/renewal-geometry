/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.SMGaugeJetInvariance

/-!
# Gauge invariance of the Dirac–Yukawa jet density on the defining carrier
  (`lem:equivariant-tests`, `thm:critical-quotient-defect`; Einstein–Standard-Model
  action-closure manuscript)

For the defining carrier (`SMGaugeJet.defCarrier`), the Dirac–Yukawa jet density `diracPt` is
invariant under the jet action `gaugeJet g dg` of a unitary `g` whose jet `dg` satisfies
`(dg)^* g = -g^* dg` (the jet of a unitary gauge): writing the density with the bilinear pairing
`⟪u, w⟫ = Σ_c u_c w_c` of dual-spinor and spinor rows (`kinC_normal`, `potC_normal`), the
Maurer–Cartan terms `⟪Ψ̄, g^* dg Ψ⟫` produced by the kinetic part (twice) and by the minimal
coupling `ρ(A')` (twice, with the opposite sign) cancel (`diracPt_gaugeJet`).
-/

open MeasureTheory Filter Topology Set Matrix
open scoped ENNReal NNReal ContDiff ComplexConjugate

noncomputable section

namespace RenewalGeometry.SMGaugeJet

open SobolevOpen CriticalGauge BallAnalysis.SMGaugeStructure EinsteinSM

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

/-- The bilinear pairing `⟪u, w⟫ = Σ_c u_c w_c` of a dual spinor row with a spinor row. -/
def pr (u w : Fin 5 → ℂ) : ℂ := u ⬝ᵥ w

/-- Pairings after the conjugate action on the left: `⟪(Y^*)ᵀ u, X w⟫ = ⟪u, (Y^* X) w⟫`. -/
theorem pr_conj_mulVec (Y X : M5) (u w : Fin 5 → ℂ) :
    pr ((star Y)ᵀ *ᵥ u) (X *ᵥ w) = pr u ((star Y * X) *ᵥ w) := by
  unfold pr
  rw [mulVec_transpose, ← dotProduct_mulVec, mulVec_mulVec]

theorem pr_add_right (u w w' : Fin 5 → ℂ) : pr u (w + w') = pr u w + pr u w' :=
  dotProduct_add _ _ _

theorem pr_add_left (u u' w : Fin 5 → ℂ) : pr (u + u') w = pr u w + pr u' w :=
  add_dotProduct _ _ _

theorem pr_mulVec_sub (u w : Fin 5 → ℂ) (X Y : M5) :
    pr u ((X - Y) *ᵥ w) = pr u (X *ᵥ w) - pr u (Y *ᵥ w) := by
  simp [pr, sub_mulVec, dotProduct_sub]

theorem pr_neg_mulVec (u w : Fin 5 → ℂ) (X : M5) : pr u ((-X) *ᵥ w) = -pr u (X *ᵥ w) := by
  simp [pr, neg_mulVec, dotProduct_neg]

/-- The complex kinetic expression whose real part is `kinForm`. -/
def kinC (γ : Fin 4 → Fin 4 → Fin 4 → ℂ) (U : SpinorFibre (Fin 5) × SpinorFibre (Fin 5))
    (W : (Fin 4 → SpinorFibre (Fin 5)) × (Fin 4 → SpinorFibre (Fin 5))) : ℂ :=
  (Complex.I / 2) * ∑ μ, ∑ s, ∑ s', ∑ c,
    (U.1 s c * γ μ s s' * W.1 μ s' c - W.2 μ s c * γ μ s s' * U.2 s' c)

theorem kinForm_eq_re (γ : Fin 4 → Fin 4 → Fin 4 → ℂ)
    (U : SpinorFibre (Fin 5) × SpinorFibre (Fin 5))
    (W : (Fin 4 → SpinorFibre (Fin 5)) × (Fin 4 → SpinorFibre (Fin 5))) :
    kinForm γ U W = (kinC γ U W).re := rfl

theorem kinC_normal (γ : Fin 4 → Fin 4 → Fin 4 → ℂ)
    (U : SpinorFibre (Fin 5) × SpinorFibre (Fin 5))
    (W : (Fin 4 → SpinorFibre (Fin 5)) × (Fin 4 → SpinorFibre (Fin 5))) :
    kinC γ U W = (Complex.I / 2) * ∑ μ, ∑ s, ∑ s₁,
      γ μ s s₁ * (pr (U.1 s) (W.1 μ s₁) - pr (W.2 μ s) (U.2 s₁)) := by
  unfold kinC
  congr 1
  refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun s _ =>
    Finset.sum_congr rfl fun s₁ _ => ?_
  simp only [pr, dotProduct, mul_sub, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun c _ => by ring

/-- The complex potential expression whose real part is `potForm` (defining carrier). -/
def potC (γ Ω : Fin 4 → Fin 4 → Fin 4 → ℂ) (A : ConnFibre) (M : Fin 5 → Fin 5 → ℂ)
    (Ψb Ψ : SpinorFibre (Fin 5)) : ℂ :=
  (Complex.I / 2) * ∑ μ, ∑ s, ∑ s₁, ∑ c,
      (Ψb s c * γ μ s s₁ * (∑ s₂, Ω μ s₁ s₂ * Ψ s₂ c + ∑ c₁, A μ c c₁ * Ψ s₁ c₁) +
        (∑ s₂, Ψb s₂ c * Ω μ s₂ s + ∑ c₁, Ψb s c₁ * A μ c₁ c) * γ μ s s₁ * Ψ s₁ c) -
    ∑ s, ∑ c, ∑ c₁, Ψb s c * M c c₁ * Ψ s c₁

theorem potForm_eq_re {Ysec : Type} (mY : CoefficientBank Ysec → ℂ)
    (γ Ω : Fin 4 → Fin 4 → Fin 4 → ℂ) (A : ConnFibre) (M : Fin 5 → Fin 5 → ℂ)
    (Ψb Ψ : SpinorFibre (Fin 5)) :
    potForm (defCarrier Ysec mY) γ Ω A M Ψb Ψ = (potC γ Ω A M Ψb Ψ).re := rfl

theorem potC_normal (γ Ω : Fin 4 → Fin 4 → Fin 4 → ℂ) (A : ConnFibre) (m : ℂ)
    (Ψb Ψ : SpinorFibre (Fin 5)) :
    potC γ Ω A (scalarM m) Ψb Ψ = (Complex.I / 2) * ∑ μ, ∑ s, ∑ s₁, γ μ s s₁ *
      (∑ s₂, Ω μ s₁ s₂ * pr (Ψb s) (Ψ s₂) + ∑ s₂, Ω μ s₂ s * pr (Ψb s₂) (Ψ s₁) +
        (pr (Ψb s) (Matrix.of (A μ) *ᵥ Ψ s₁) + pr (Ψb s) (Matrix.of (A μ) *ᵥ Ψ s₁))) -
        m * ∑ s, pr (Ψb s) (Ψ s) := by
  unfold potC
  congr 1
  · congr 1
    refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun s _ =>
      Finset.sum_congr rfl fun s₁ _ => ?_
    simp only [pr, mulVec, dotProduct, of_apply, Finset.mul_sum, Finset.sum_mul, mul_add,
      add_mul, Finset.sum_add_distrib]
    have h1 : ∑ c, ∑ s₂, Ψb s c * γ μ s s₁ * (Ω μ s₁ s₂ * Ψ s₂ c) =
        ∑ s₂, ∑ c, γ μ s s₁ * (Ω μ s₁ s₂ * (Ψb s c * Ψ s₂ c)) := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    have h2 : ∑ c, ∑ c₁, Ψb s c * γ μ s s₁ * (A μ c c₁ * Ψ s₁ c₁) =
        ∑ c, ∑ c₁, γ μ s s₁ * (Ψb s c * (A μ c c₁ * Ψ s₁ c₁)) :=
      Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    have h3 : ∑ c, ∑ s₂, Ψb s₂ c * Ω μ s₂ s * γ μ s s₁ * Ψ s₁ c =
        ∑ s₂, ∑ c, γ μ s s₁ * (Ω μ s₂ s * (Ψb s₂ c * Ψ s₁ c)) := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    have h4 : ∑ c, ∑ c₁, Ψb s c₁ * A μ c₁ c * γ μ s s₁ * Ψ s₁ c =
        ∑ c, ∑ c₁, γ μ s s₁ * (Ψb s c * (A μ c c₁ * Ψ s₁ c₁)) := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    rw [h1, h2, h3, h4]
    ring
  · simp only [pr, dotProduct, scalarM, Finset.mul_sum, mul_ite, ite_mul, mul_zero, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-! ### Components of the jet action -/

section Comp
variable (g : M5) (dg : Fin 4 → M5) (J : RJet (Fin 5))
@[simp] theorem gaugeJet_e : (gaugeJet g dg J).e = J.e := rfl
@[simp] theorem gaugeJet_de : (gaugeJet g dg J).de = J.de := rfl
@[simp] theorem gaugeJet_A : (gaugeJet g dg J).A = connG g dg J.A := rfl
@[simp] theorem gaugeJet_F : (gaugeJet g dg J).F = fun μ ν => adG g (J.F μ ν) := rfl
@[simp] theorem gaugeJet_H : (gaugeJet g dg J).H = higgsG g J.H := rfl
@[simp] theorem gaugeJet_K : (gaugeJet g dg J).K = fun μ => higgsG g (J.K μ) := rfl
@[simp] theorem gaugeJet_Ψ : (gaugeJet g dg J).Ψ = spinG g J.Ψ := rfl
@[simp] theorem gaugeJet_dΨ :
    (gaugeJet g dg J).dΨ = fun μ => spinG g (J.dΨ μ) + spinG (dg μ) J.Ψ := rfl
@[simp] theorem gaugeJet_Ψb : (gaugeJet g dg J).Ψb = cospinG g J.Ψb := rfl
@[simp] theorem gaugeJet_dΨb :
    (gaugeJet g dg J).dΨb = fun μ => cospinG g (J.dΨb μ) + cospinG (dg μ) J.Ψb := rfl
end Comp

/-! ### Pairings of gauge-transformed rows -/

theorem pr_gauge_kin {g : M5} (hg : star g * g = 1) (dg : M5) (u v w : Fin 5 → ℂ) :
    pr ((star g)ᵀ *ᵥ u) (g *ᵥ v + dg *ᵥ w) = pr u v + pr u ((star g * dg) *ᵥ w) := by
  rw [pr_add_right, pr_conj_mulVec, pr_conj_mulVec, hg, one_mulVec]

theorem pr_gauge_kin' {g : M5} (hg : star g * g = 1) (dg : M5)
    (hdg : star dg * g = -(star g * dg)) (u v w : Fin 5 → ℂ) :
    pr ((star g)ᵀ *ᵥ u + (star dg)ᵀ *ᵥ v) (g *ᵥ w) =
      pr u w - pr v ((star g * dg) *ᵥ w) := by
  rw [pr_add_left, pr_conj_mulVec, pr_conj_mulVec, hg, one_mulVec, hdg, pr_neg_mulVec,
    sub_eq_add_neg]

theorem pr_gauge_val {g : M5} (hg : star g * g = 1) (u w : Fin 5 → ℂ) :
    pr ((star g)ᵀ *ᵥ u) (g *ᵥ w) = pr u w := by
  rw [pr_conj_mulVec, hg, one_mulVec]

theorem pr_gauge_conn {g : M5} (hg : star g * g = 1) (A dg : M5) (u w : Fin 5 → ℂ) :
    pr ((star g)ᵀ *ᵥ u) ((g * A * star g - dg * star g) *ᵥ (g *ᵥ w)) =
      pr u (A *ᵥ w) - pr u ((star g * dg) *ᵥ w) := by
  rw [mulVec_mulVec, pr_conj_mulVec]
  have : star g * ((g * A * star g - dg * star g) * g) = A - star g * dg := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, hg, Matrix.mul_one]
    rw [← Matrix.mul_assoc (star g) g, hg, Matrix.one_mul]
  rw [this, pr_mulVec_sub]

/-- The Dirac–Yukawa jet density of the defining carrier in complex normal form. -/
theorem diracPt_defCarrier_eq {Ysec : Type} (mY : CoefficientBank Ysec → ℂ)
    (θ : CoefficientBank Ysec) (R : RJet (Fin 5)) :
    diracPt (defCarrier Ysec mY) θ R = volFactor R.e *
      (kinC (gammaE R.e) (R.Ψb, R.Ψ) (R.dΨ, R.dΨb) +
        potC (gammaE R.e) (spinGenE R.e R.de) R.A (scalarM (mY θ)) R.Ψb R.Ψ).re := by
  rw [Complex.add_re, mul_add]
  rfl

/-- **Gauge invariance of the Dirac–Yukawa jet density** (defining carrier): for `g` unitary and
`dg` with `g^* dg` skew-Hermitian (`(dg)^* g = -g^* dg`, the jet of a unitary gauge), the
Maurer–Cartan terms of the kinetic part and of the minimal coupling cancel. -/
theorem diracPt_gaugeJet {Ysec : Type} (mY : CoefficientBank Ysec → ℂ)
    (θ : CoefficientBank Ysec) {g : M5} (hg : g ∈ unitaryGroup (Fin 5) ℂ) (dg : Fin 4 → M5)
    (hdg : ∀ μ, star (dg μ) * g = -(star g * dg μ)) (J : RJet (Fin 5)) :
    diracPt (defCarrier Ysec mY) θ (gaugeJet g dg J) = diracPt (defCarrier Ysec mY) θ J := by
  have hu : star g * g = 1 := mem_unitaryGroup_iff'.mp hg
  rw [diracPt_defCarrier_eq, diracPt_defCarrier_eq, gaugeJet_e]
  congr 2
  rw [kinC_normal, kinC_normal, potC_normal, potC_normal]
  have hA : ∀ μ, Matrix.of (connG g dg J.A μ) = g * Matrix.of (J.A μ) * star g - dg μ * star g :=
    fun μ => rfl
  simp only [gaugeJet_de, gaugeJet_A, gaugeJet_Ψ, gaugeJet_dΨ, gaugeJet_Ψb, gaugeJet_dΨb,
    spinG, cospinG, Pi.add_apply, hA, pr_gauge_kin hu, pr_gauge_kin' hu _ (hdg _),
    pr_gauge_val hu, pr_gauge_conn hu]
  simp only [mul_sub, mul_add, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
  ring

end RenewalGeometry.SMGaugeJet
