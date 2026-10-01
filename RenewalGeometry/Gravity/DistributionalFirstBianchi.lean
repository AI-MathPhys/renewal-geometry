/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Gravity.DistributionalTorsionLimit

/-!
# The first Bianchi identity in distributions and its passage to weak–strong limits
  (Bianchi / Holst-inert step of `thm:supp-renewal-palatini`; emergent-spacetime manuscript,
  supplement)

For a coframe `e = Σ_a e_a dx^a` (values in a fibre `V`) and a connection `ω = Σ_a ω_a dx^a`
(values in a normed algebra `A` acting on `V` through a multiplicative continuous bilinear map
`act`), the first Bianchi identity is `D T = R ∧ e`, with `T = d e + ω ∧ e` and
`R = d ω + ω ∧ ω`.  In components (`T = ½ T_{ab} dx^a ∧ dx^b`, three-form indices `a b c`):
`(R ∧ e)_{abc} = ∑_{cyc} act(R_{ab}) e_c` and `(D T)_{abc} = ∑_{cyc} (∂_a T_{bc} + act(ω_a) T_{bc})`.

Main results:

* `integral_vpd_eq_zero`: the integral of a partial derivative of a compactly supported `C¹` map
  vanishes;
* `bianchi_integral_identity`: **the tested first Bianchi identity for `C¹` fields** —
  for every `φ ∈ 𝓓(Ω)`,
  `∫ φ (R ∧ e)_{abc} = ∑_{cyc} (-∫ ∂_a φ T_{bc} + ∫ φ act(ω_a) T_{bc})`;
  no second derivative of `e` or `ω` is used (the Hessian of the test function is symmetric);
* `bianchiPairing_tendsto_zero_of_approx` / `isDistributionalBianchi_of_approx`:
  **passage to the limit** — if `C¹` pairs `(e_n, ω_n)` have `e_n → e` strongly in `L²_loc(Ω)`,
  `L²_loc`-bounded connections, torsions `T_n → 0` strongly in `L²_loc(Ω)`, and curvatures
  `R(ω_n)` bounded in `L²_loc` and weakly convergent to `R` (tested against `L²` coframe
  pairings), then `R ∧ e = 0` in distributions on `Ω`;
* `ae_bianchi_of_isDistributionalBianchi`: with `R, e ∈ L²_loc(Ω)` the distributional identity
  holds pointwise almost everywhere on `Ω` (fundamental lemma of the calculus of variations);
* `tendsto_integral_smul_bilin_weak_strong`: general weak–strong product passage
  (`L²`-bounded × strongly convergent, with the weak limit tested on the strong limit);
* `tendsto_torsionPairing_weak`, `isTorsionFree_of_tendsto_weak`: the torsion passage on the
  literal-link route, where connection coefficients (the temporal one) converge only weakly.

What this does **not** prove (disclosed): the Bianchi identity directly for a limit pair at the
regularity `ω ∈ L²_loc`, `R ∈ L²`, `e ∈ L⁶` without approximants (the product rule for
`d(ω ∧ e)` is not available at that regularity); the theorem here needs `C¹` approximants with
`L²`-vanishing torsion (e.g. mollifications when `ω ∈ L³_loc`, `e ∈ L⁶_loc`).
-/

open MeasureTheory Filter Topology ENNReal TopologicalSpace
open scoped NNReal Distributions

noncomputable section

namespace RenewalGeometry.DistributionalBianchi

open DistributionalCurvature DistributionalTorsion

set_option linter.unusedSectionVars false

variable {d : ℕ}

/-- Partial derivative `∂_a f(x) = Df(x) e_a` of a map on `ℝ^d` with values in a normed space. -/
def vpd {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] (f : (Fin d → ℝ) → W)
    (a : Fin d) (x : Fin d → ℝ) : W :=
  fderiv ℝ f x (Pi.single a 1)

section Calculus

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]

/-- The integral of a partial derivative of a compactly supported `C¹` map vanishes. -/
theorem integral_vpd_eq_zero {F : (Fin d → ℝ) → W} (hF : ContDiff ℝ 1 F)
    (hc : HasCompactSupport F) (a : Fin d) : ∫ x, vpd F a x = 0 := by
  have hcont : Continuous fun x => fderiv ℝ F x (Pi.single a 1) :=
    (hF.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hcs : HasCompactSupport fun x => fderiv ℝ F x (Pi.single a 1) :=
    HasCompactSupport.fderiv_apply (𝕜 := ℝ) hc (Pi.single a 1)
  have hi1 := hcont.integrable_of_hasCompactSupport (μ := volume) hcs
  have hi2 := hF.continuous.integrable_of_hasCompactSupport (μ := volume) hc
  have h := integral_bilinear_hasFDerivAt_right_eq_neg_left_of_integrable (μ := volume)
    (B := (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] W →L[ℝ] W))
    (f := fun _ => (1 : ℝ)) (f' := fun _ => 0) (g := F) (g' := fderiv ℝ F)
    (v := Pi.single a 1) (by simp) (by simpa using hi1) (by simpa using hi2)
    (fun x _ => hasFDerivAt_const _ _)
    (fun x _ => ((hF.differentiable one_ne_zero) x).hasFDerivAt)
  simpa [vpd] using h

theorem vpd_smul {c : (Fin d → ℝ) → ℝ} {f : (Fin d → ℝ) → W} {x : Fin d → ℝ}
    (hc : DifferentiableAt ℝ c x) (hf : DifferentiableAt ℝ f x) (a : Fin d) :
    vpd (fun y => c y • f y) a x = vpd c a x • f x + c x • vpd f a x := by
  simp only [vpd, fderiv_fun_smul hc hf, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply]
  abel

theorem vpd_bilin {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] (B : E₁ →L[ℝ] E₂ →L[ℝ] W)
    {f : (Fin d → ℝ) → E₁} {g : (Fin d → ℝ) → E₂} {x : Fin d → ℝ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (a : Fin d) :
    vpd (fun y => B (f y) (g y)) a x = B (f x) (vpd g a x) + B (vpd f a x) (g x) := by
  simp only [vpd, B.fderiv_of_bilinear hf hg, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.precompR_apply, ContinuousLinearMap.precompL_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply]

theorem vpd_sub {f g : (Fin d → ℝ) → W} {x : Fin d → ℝ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (a : Fin d) :
    vpd (fun y => f y - g y) a x = vpd f a x - vpd g a x := by
  simp [vpd, fderiv_fun_sub hf hg]

/-- Symmetry of the Hessian of a smooth function: `∂_b ∂_a φ = ∂_a ∂_b φ`. -/
theorem vpd_vpd_comm {φ : (Fin d → ℝ) → ℝ} (hφ : ContDiff ℝ 2 φ) (a b : Fin d)
    (x : Fin d → ℝ) :
    vpd (vpd φ a) b x = vpd (vpd φ b) a x := by
  have hd : DifferentiableAt ℝ (fderiv ℝ φ) x :=
    ((hφ.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero) x
  have hsymm := (hφ.contDiffAt (x := x)).isSymmSndFDerivAt (by simp)
  show fderiv ℝ (fun y => fderiv ℝ φ y (Pi.single a 1)) x (Pi.single b 1) =
    fderiv ℝ (fun y => fderiv ℝ φ y (Pi.single b 1)) x (Pi.single a 1)
  rw [fderiv_clm_apply hd (differentiableAt_const _), fderiv_clm_apply hd
    (differentiableAt_const _)]
  simp
  exact hsymm _ _

end Calculus


/-! ### The tested Bianchi identity for `C¹` fields -/

section Identity

variable {A V : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- Classical curvature components `R_{ab} = ∂_a ω_b - ∂_b ω_a + ω_a ω_b - ω_b ω_a`. -/
def classicalCurvature (ω : Fin d → (Fin d → ℝ) → A) (a b : Fin d) (x : Fin d → ℝ) : A :=
  vpd (ω b) a x - vpd (ω a) b x + (ω a x * ω b x - ω b x * ω a x)

/-- Classical torsion components `T_{ab} = ∂_a e_b - ∂_b e_a + act(ω_a) e_b - act(ω_b) e_a`. -/
def classicalTorsion (act : A →L[ℝ] V →L[ℝ] V) (e : Fin d → (Fin d → ℝ) → V)
    (ω : Fin d → (Fin d → ℝ) → A) (a b : Fin d) (x : Fin d → ℝ) : V :=
  vpd (e b) a x - vpd (e a) b x + (act (ω a x) (e b x) - act (ω b x) (e a x))

/-- The Bianchi three-form density `(R ∧ e)_{abc} = ∑_{cyc} act(R_{ab}) e_c`. -/
def bianchiForm (act : A →L[ℝ] V →L[ℝ] V) (R : Fin d → Fin d → (Fin d → ℝ) → A)
    (e : Fin d → (Fin d → ℝ) → V) (a b c : Fin d) (x : Fin d → ℝ) : V :=
  act (R a b x) (e c x) + act (R b c x) (e a x) + act (R c a x) (e b x)

/-- The tested Bianchi three-form `⟨R ∧ e, φ⟩_{abc}`. -/
def bianchiPairing (act : A →L[ℝ] V →L[ℝ] V) (R : Fin d → Fin d → (Fin d → ℝ) → A)
    (e : Fin d → (Fin d → ℝ) → V) (φ : (Fin d → ℝ) → ℝ) (a b c : Fin d) : V :=
  ∫ x, φ x • bianchiForm act R e a b c x

/-- `R ∧ e = 0` in distributions on `Ω`. -/
def IsDistributionalBianchi (act : A →L[ℝ] V →L[ℝ] V) (Ω : Opens (Fin d → ℝ))
    (R : Fin d → Fin d → (Fin d → ℝ) → A) (e : Fin d → (Fin d → ℝ) → V) : Prop :=
  ∀ φ : 𝓓(Ω, ℝ), ∀ a b c, bianchiPairing act R e φ a b c = 0

/-- The tested covariant exterior derivative of a torsion two-form,
`⟨D T, φ⟩_{abc} = ∑_{cyc} (-∫ ∂_a φ T_{bc} + ∫ φ act(ω_a) T_{bc})`. -/
def torsionDerivPairing (act : A →L[ℝ] V →L[ℝ] V) (ω : Fin d → (Fin d → ℝ) → A)
    (T : Fin d → Fin d → (Fin d → ℝ) → V) (φ : (Fin d → ℝ) → ℝ) (a b c : Fin d) : V :=
  ((-(∫ x, vpd φ a x • T b c x)) + ∫ x, φ x • act (ω a x) (T b c x)) +
  ((-(∫ x, vpd φ b x • T c a x)) + ∫ x, φ x • act (ω b x) (T c a x)) +
  ((-(∫ x, vpd φ c x • T a b x)) + ∫ x, φ x • act (ω c x) (T a b x))

/-- The total-derivative field `φ (act(ω_b) e_c - act(ω_c) e_b)`. -/
def bianchiP (act : A →L[ℝ] V →L[ℝ] V) (φ : (Fin d → ℝ) → ℝ) (e : Fin d → (Fin d → ℝ) → V)
    (ω : Fin d → (Fin d → ℝ) → A) (b c : Fin d) : (Fin d → ℝ) → V :=
  fun y => φ y • (act (ω b y) (e c y) - act (ω c y) (e b y))

/-- The total-derivative field `∂_a φ e_c`. -/
def bianchiQ (φ : (Fin d → ℝ) → ℝ) (e : Fin d → (Fin d → ℝ) → V) (a c : Fin d) :
    (Fin d → ℝ) → V :=
  fun y => vpd φ a y • e c y

theorem integrable_of_continuous_of_eq_zero_off {W : Type*} [NormedAddCommGroup W]
    {f : (Fin d → ℝ) → W} (hf : Continuous f) {C : Set (Fin d → ℝ)} (hC : IsCompact C)
    (h : ∀ x, x ∉ C → f x = 0) : Integrable f := by
  refine hf.integrable_of_hasCompactSupport (HasCompactSupport.intro hC fun x hx => h x hx)

theorem contDiff_vpd_test {Ω : Opens (Fin d → ℝ)} (φ : 𝓓(Ω, ℝ)) (a : Fin d) :
    ContDiff ℝ 1 (vpd φ a) := by
  have h2 : ContDiff ℝ 2 (φ : (Fin d → ℝ) → ℝ) := φ.contDiff.of_le (by norm_cast)
  have h : ContDiff ℝ 1 (fderiv ℝ (φ : (Fin d → ℝ) → ℝ)) :=
    h2.fderiv_right (m := 1) (by norm_num)
  exact h.clm_apply contDiff_const

theorem vpd_test_eq_zero_off {Ω : Opens (Fin d → ℝ)} (φ : 𝓓(Ω, ℝ)) (a : Fin d)
    {x : Fin d → ℝ} (hx : x ∉ tsupport φ) : vpd φ a x = 0 :=
  pderiv_eq_zero_off φ a hx

theorem integrable_vpd {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {F : (Fin d → ℝ) → W} (hF : ContDiff ℝ 1 F) (hs : HasCompactSupport F) (a : Fin d) :
    Integrable (vpd F a) :=
  ((hF.continuous_fderiv one_ne_zero).clm_apply continuous_const).integrable_of_hasCompactSupport
    (HasCompactSupport.fderiv_apply (𝕜 := ℝ) hs (Pi.single a 1))

/-- **Tested first Bianchi identity for `C¹` fields.**  For a `C¹` coframe `e`, a `C¹`
connection `ω` acting multiplicatively on the fibre (`act (x y) = act x ∘ act y`) and every
test function `φ ∈ 𝓓(Ω)`,
`⟨R(ω) ∧ e, φ⟩_{abc} = ⟨D T, φ⟩_{abc}` with `T` the classical torsion; only first derivatives of
`e` and `ω` enter. -/
theorem bianchi_integral_identity (act : A →L[ℝ] V →L[ℝ] V)
    (hact : ∀ (x y : A) (v : V), act (x * y) v = act x (act y v))
    {e : Fin d → (Fin d → ℝ) → V} {ω : Fin d → (Fin d → ℝ) → A}
    (he : ∀ a, ContDiff ℝ 1 (e a)) (hω : ∀ a, ContDiff ℝ 1 (ω a))
    {Ω : Opens (Fin d → ℝ)} (φ : 𝓓(Ω, ℝ)) (a b c : Fin d) :
    bianchiPairing act (classicalCurvature ω) e φ a b c =
      torsionDerivPairing act ω (classicalTorsion act e ω) φ a b c := by
  set C := tsupport (φ : (Fin d → ℝ) → ℝ)
  have hC : IsCompact C := φ.hasCompactSupport
  have hφ2 : ContDiff ℝ 2 (φ : (Fin d → ℝ) → ℝ) := φ.contDiff.of_le (by norm_cast)
  have hφd : Differentiable ℝ (φ : (Fin d → ℝ) → ℝ) := hφ2.differentiable (by norm_num)
  have hz : ∀ x, x ∉ C → φ x = 0 := fun x hx => test_eq_zero_off φ hx
  have hzd : ∀ c x, x ∉ C → vpd φ c x = 0 := fun c x hx => vpd_test_eq_zero_off φ c hx
  have hed : ∀ a, Differentiable ℝ (e a) := fun a => (he a).differentiable one_ne_zero
  have hωd : ∀ a, Differentiable ℝ (ω a) := fun a => (hω a).differentiable one_ne_zero
  have hvd : ∀ a, Differentiable ℝ (vpd φ a) := fun a =>
    (contDiff_vpd_test φ a).differentiable one_ne_zero
  have hec : ∀ a, Continuous (e a) := fun a => (he a).continuous
  have hωc : ∀ a, Continuous (ω a) := fun a => (hω a).continuous
  have hdec : ∀ a b, Continuous (vpd (e a) b) := fun a b =>
    ((he a).continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hdωc : ∀ a b, Continuous (vpd (ω a) b) := fun a b =>
    ((hω a).continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hvc : ∀ a, Continuous (vpd φ a) := fun a => (contDiff_vpd_test φ a).continuous
  -- the total-derivative fields
  set P := bianchiP act (φ : (Fin d → ℝ) → ℝ) e ω with hP
  set Q := bianchiQ (φ : (Fin d → ℝ) → ℝ) e with hQ
  have hPc : ∀ b c, ContDiff ℝ 1 (P b c) := by
    intro b c
    have h1 : ContDiff ℝ 1 fun y => act (ω b y) (e c y) :=
      act.isBoundedBilinearMap.contDiff.comp ((hω b).prodMk (he c))
    have h2 : ContDiff ℝ 1 fun y => act (ω c y) (e b y) :=
      act.isBoundedBilinearMap.contDiff.comp ((hω c).prodMk (he b))
    exact (hφ2.of_le (by norm_num)).smul (h1.sub h2)
  have hPs : ∀ b c, HasCompactSupport (P b c) := fun b c =>
    HasCompactSupport.intro hC fun x hx => by simp [hP, bianchiP, hz x hx]
  have hQc : ∀ a c, ContDiff ℝ 1 (Q a c) := fun a c => (contDiff_vpd_test φ a).smul (he c)
  have hQs : ∀ a c, HasCompactSupport (Q a c) := fun a c =>
    HasCompactSupport.intro hC fun x hx => by simp [hQ, bianchiQ, hzd a x hx]
  -- derivatives of the total-derivative fields
  have hdP : ∀ b c a x, vpd (P b c) a x = vpd φ a x • (act (ω b x) (e c x) -
      act (ω c x) (e b x)) + φ x • ((act (ω b x) (vpd (e c) a x) + act (vpd (ω b) a x) (e c x)) -
      (act (ω c x) (vpd (e b) a x) + act (vpd (ω c) a x) (e b x))) := by
    intro b c a x
    have hb : DifferentiableAt ℝ (fun y => act (ω b y) (e c y)) x :=
      (act.isBoundedBilinearMap.differentiableAt _).comp x ((hωd b x).prodMk (hed c x))
    have hc : DifferentiableAt ℝ (fun y => act (ω c y) (e b y)) x :=
      (act.isBoundedBilinearMap.differentiableAt _).comp x ((hωd c x).prodMk (hed b x))
    show vpd (fun y => (φ : (Fin d → ℝ) → ℝ) y •
      (act (ω b y) (e c y) - act (ω c y) (e b y))) a x = _
    rw [vpd_smul (hφd x) (hb.fun_sub hc), vpd_sub hb hc, vpd_bilin act (hωd b x) (hed c x),
      vpd_bilin act (hωd c x) (hed b x)]
  have hdQ : ∀ a c b x, vpd (Q a c) b x = vpd (vpd φ a) b x • e c x +
      vpd φ a x • vpd (e c) b x := by
    intro a c b x
    show vpd (fun y => vpd (φ : (Fin d → ℝ) → ℝ) a y • e c y) b x = _
    rw [vpd_smul (hvd a x) (hed c x)]
  -- pointwise identity
  have hpt : ∀ x, φ x • bianchiForm act (classicalCurvature ω) e a b c x -
      (((-(vpd φ a x • classicalTorsion act e ω b c x)) +
        φ x • act (ω a x) (classicalTorsion act e ω b c x)) +
      ((-(vpd φ b x • classicalTorsion act e ω c a x)) +
        φ x • act (ω b x) (classicalTorsion act e ω c a x)) +
      ((-(vpd φ c x • classicalTorsion act e ω a b x)) +
        φ x • act (ω c x) (classicalTorsion act e ω a b x))) =
      vpd (P b c) a x + vpd (P c a) b x + vpd (P a b) c x +
      ((vpd (Q a c) b x - vpd (Q a b) c x) + (vpd (Q b a) c x - vpd (Q b c) a x) +
        (vpd (Q c b) a x - vpd (Q c a) b x)) := by
    intro x
    rw [hdP, hdP, hdP, hdQ, hdQ, hdQ, hdQ, hdQ, hdQ]
    rw [vpd_vpd_comm hφ2 b a, vpd_vpd_comm hφ2 c b, vpd_vpd_comm hφ2 a c]
    simp only [bianchiForm, classicalCurvature, classicalTorsion, map_add, map_sub,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, hact, smul_add, smul_sub]
    abel
  -- integrability of the pieces
  have hTc : ∀ b c, Continuous (classicalTorsion act e ω b c) := fun b c =>
    ((hdec c b).sub (hdec b c)).add
      ((act.continuous₂.comp₂ (hωc b) (hec c)).sub (act.continuous₂.comp₂ (hωc c) (hec b)))
  have hRc : ∀ a b, Continuous (classicalCurvature ω a b) := fun a b =>
    ((hdωc b a).sub (hdωc a b)).add (((hωc a).mul (hωc b)).sub ((hωc b).mul (hωc a)))
  have hBc : Continuous (bianchiForm act (classicalCurvature ω) e a b c) :=
    ((act.continuous₂.comp₂ (hRc a b) (hec c)).add (act.continuous₂.comp₂ (hRc b c) (hec a))).add
      (act.continuous₂.comp₂ (hRc c a) (hec b))
  have iL : Integrable fun x => φ x • bianchiForm act (classicalCurvature ω) e a b c x :=
    integrable_of_continuous_of_eq_zero_off (φ.continuous.smul hBc) hC
      fun x hx => by simp [hz x hx]
  have i1 : ∀ a b c, Integrable fun x => vpd φ a x • classicalTorsion act e ω b c x :=
    fun a b c => integrable_of_continuous_of_eq_zero_off ((hvc a).smul (hTc b c)) hC
      fun x hx => by simp [hzd a x hx]
  have i2 : ∀ a b c, Integrable fun x => φ x • act (ω a x) (classicalTorsion act e ω b c x) :=
    fun a b c => integrable_of_continuous_of_eq_zero_off
      (φ.continuous.smul (act.continuous₂.comp₂ (hωc a) (hTc b c))) hC
      fun x hx => by simp [hz x hx]
  have iP : ∀ b c a, Integrable (vpd (P b c) a) := fun b c a => integrable_vpd (hPc b c) (hPs b c) a
  have iQ : ∀ a c b, Integrable (vpd (Q a c) b) := fun a c b => integrable_vpd (hQc a c) (hQs a c) b
  have zP : ∀ b c a, ∫ x, vpd (P b c) a x = 0 := fun b c a => integral_vpd_eq_zero (hPc b c) (hPs b c) a
  have zQ : ∀ a c b, ∫ x, vpd (Q a c) b x = 0 := fun a c b => integral_vpd_eq_zero (hQc a c) (hQs a c) b
  -- the integral of the total derivatives vanishes
  have hzero : ∫ x, (φ x • bianchiForm act (classicalCurvature ω) e a b c x -
      (((-(vpd φ a x • classicalTorsion act e ω b c x)) +
        φ x • act (ω a x) (classicalTorsion act e ω b c x)) +
      ((-(vpd φ b x • classicalTorsion act e ω c a x)) +
        φ x • act (ω b x) (classicalTorsion act e ω c a x)) +
      ((-(vpd φ c x • classicalTorsion act e ω a b x)) +
        φ x • act (ω c x) (classicalTorsion act e ω a b x)))) = 0 := by
    rw [integral_congr_ae (Eventually.of_forall hpt)]
    rw [integral_add (((iP b c a).fun_add (iP c a b)).fun_add (iP a b c))
      ((((iQ a c b).sub' (iQ a b c)).fun_add ((iQ b a c).sub' (iQ b c a))).fun_add
        ((iQ c b a).sub' (iQ c a b))),
      integral_add ((iP b c a).fun_add (iP c a b)) (iP a b c),
      integral_add (iP b c a) (iP c a b),
      integral_add (((iQ a c b).sub' (iQ a b c)).fun_add ((iQ b a c).sub' (iQ b c a)))
        ((iQ c b a).sub' (iQ c a b)),
      integral_add ((iQ a c b).sub' (iQ a b c)) ((iQ b a c).sub' (iQ b c a)),
      integral_sub (iQ a c b) (iQ a b c), integral_sub (iQ b a c) (iQ b c a),
      integral_sub (iQ c b a) (iQ c a b)]
    simp only [zP, zQ]
    simp
  have iR : Integrable fun x => (((-(vpd φ a x • classicalTorsion act e ω b c x)) +
        φ x • act (ω a x) (classicalTorsion act e ω b c x)) +
      ((-(vpd φ b x • classicalTorsion act e ω c a x)) +
        φ x • act (ω b x) (classicalTorsion act e ω c a x)) +
      ((-(vpd φ c x • classicalTorsion act e ω a b x)) +
        φ x • act (ω c x) (classicalTorsion act e ω a b x))) :=
    ((((i1 a b c).neg.add (i2 a b c)).add ((i1 b c a).neg.add (i2 b c a))).add
      ((i1 c a b).neg.add (i2 c a b)))
  rw [integral_sub iL iR, sub_eq_zero] at hzero
  unfold bianchiPairing torsionDerivPairing
  rw [hzero, integral_add (((i1 a b c).fun_neg.fun_add (i2 a b c)).fun_add ((i1 b c a).fun_neg.fun_add (i2 b c a)))
      ((i1 c a b).fun_neg.fun_add (i2 c a b)),
    integral_add ((i1 a b c).fun_neg.fun_add (i2 a b c)) ((i1 b c a).fun_neg.fun_add (i2 b c a)),
    integral_add (i1 a b c).fun_neg (i2 a b c), integral_add (i1 b c a).fun_neg (i2 b c a),
    integral_add (i1 c a b).fun_neg (i2 c a b), integral_neg, integral_neg, integral_neg]

end Identity


/-! ### Passage to weak–strong limits -/

section Limit

variable {E₁ E₂ W : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W]

/-- A bounded weight times a bilinear product of two `L²` functions is integrable. -/
theorem integrable_smul_bilin {X : Type*} [MeasurableSpace X] {ν : Measure X}
    [IsFiniteMeasure ν] (B : E₁ →L[ℝ] E₂ →L[ℝ] W) {ψ : X → ℝ}
    (hψ : AEStronglyMeasurable ψ ν) {M : ℝ} (hM : ∀ x, ‖ψ x‖ ≤ M) {f : X → E₁} {g : X → E₂}
    (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) :
    Integrable (fun x => ψ x • B (f x) (g x)) ν := by
  have h1 : Integrable (fun x => B (f x) (g x)) ν := by
    have := (Lp.memLp (ContinuousLinearMap.holderL ν 2 2 1 B (hf.toLp f) (hg.toLp g))).integrable
      le_rfl
    refine this.congr ?_
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp,
      ContinuousLinearMap.coeFn_holder (r := 1) B (hf.toLp f) (hg.toLp g)] with x h2 h3 h4
    simp only [ContinuousLinearMap.holderL_apply_apply] at *
    rw [h4, h2, h3]
  exact h1.bdd_smul M hψ (Eventually.of_forall hM)

/-- The `L¹`-pairing identity behind the weak–strong arguments. -/
theorem lpPairing_holder_eq_integral {X : Type*} [MeasurableSpace X] {ν : Measure X}
    [IsFiniteMeasure ν] (B : E₁ →L[ℝ] E₂ →L[ℝ] W) {ψ : X → ℝ} (hψ : MemLp ψ ∞ ν)
    {f : X → E₁} {g : X → E₂} (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) :
    ContinuousLinearMap.lpPairing ν ∞ 1 (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] W →L[ℝ] W)
      (hψ.toLp ψ) (ContinuousLinearMap.holderL ν 2 2 1 B (hf.toLp f) (hg.toLp g)) =
      ∫ x, ψ x • B (f x) (g x) ∂ν := by
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [hψ.coeFn_toLp, hf.coeFn_toLp, hg.coeFn_toLp,
    ContinuousLinearMap.coeFn_holder (r := 1) B (hf.toLp f) (hg.toLp g)] with x h1 h2 h3 h4
  simp only [ContinuousLinearMap.holderL_apply_apply] at *
  rw [h4, h1, h2, h3]
  simp

/-- **Weak–strong product passage.**  If `u_n` is bounded in `L²`, `v_n → v` strongly in `L²`,
and `∫ ψ B(u_n, v) → ℓ`, then `∫ ψ B(u_n, v_n) → ℓ`. -/
theorem tendsto_integral_smul_bilin_weak_strong {X : Type*} [MeasurableSpace X]
    {ν : Measure X} [IsFiniteMeasure ν] (B : E₁ →L[ℝ] E₂ →L[ℝ] W) {ψ : X → ℝ}
    (hψ : AEStronglyMeasurable ψ ν) {M : ℝ} (hM : ∀ x, ‖ψ x‖ ≤ M) {u : ℕ → X → E₁}
    {v : ℕ → X → E₂} {v' : X → E₂} (hu : ∀ n, MemLp (u n) 2 ν) (hv : ∀ n, MemLp (v n) 2 ν)
    (hv' : MemLp v' 2 ν) {K : ℝ≥0∞} (hK : K ≠ ∞) (hub : ∀ n, eLpNorm (u n) 2 ν ≤ K)
    (hvlim : Tendsto (fun n => eLpNorm (v n - v') 2 ν) atTop (𝓝 0)) {ℓ : W}
    (hw : Tendsto (fun n => ∫ x, ψ x • B (u n x) (v' x) ∂ν) atTop (𝓝 ℓ)) :
    Tendsto (fun n => ∫ x, ψ x • B (u n x) (v n x) ∂ν) atTop (𝓝 ℓ) := by
  have hψ' : MemLp ψ ∞ ν := memLp_top_of_bound hψ M (Eventually.of_forall hM)
  set H := ContinuousLinearMap.holderL ν 2 2 1 B
  set L := ContinuousLinearMap.lpPairing ν ∞ 1
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] W →L[ℝ] W) (hψ'.toLp ψ)
  have hV : Tendsto (fun n => (hv n).toLp (v n)) atTop (𝓝 (hv'.toLp v')) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ _ _ _).2 hvlim
  have hVn : Tendsto (fun n => ‖(hv n).toLp (v n) - hv'.toLp v'‖) atTop (𝓝 0) :=
    (tendsto_iff_norm_sub_tendsto_zero.1 hV)
  have h0 : Tendsto (fun n => L (H ((hu n).toLp (u n)) ((hv n).toLp (v n) - hv'.toLp v')))
      atTop (𝓝 0) := by
    have hH : Tendsto (fun n => H ((hu n).toLp (u n)) ((hv n).toLp (v n) - hv'.toLp v'))
        atTop (𝓝 0) := by
      have hbound : Tendsto (fun n => ‖H‖ * K.toReal * ‖(hv n).toLp (v n) - hv'.toLp v'‖)
          atTop (𝓝 0) := by simpa using hVn.const_mul (‖H‖ * K.toReal)
      refine squeeze_zero_norm (fun n => ?_) hbound
      refine (H.le_opNorm₂ _ _).trans ?_
      rw [Lp.norm_toLp]
      gcongr
      exact hub n
    have := (L.continuous.tendsto 0).comp hH
    rw [map_zero] at this
    exact this
  have hdec : ∀ n, ∫ x, ψ x • B (u n x) (v n x) ∂ν =
      L (H ((hu n).toLp (u n)) ((hv n).toLp (v n) - hv'.toLp v')) +
        ∫ x, ψ x • B (u n x) (v' x) ∂ν := by
    intro n
    rw [← lpPairing_holder_eq_integral B hψ' (hu n) (hv n),
      ← lpPairing_holder_eq_integral B hψ' (hu n) hv', map_sub, map_sub]
    abel
  simp only [hdec]
  simpa using h0.add hw

/-- A bounded weight against a bilinear product of an `L²`-bounded sequence and an
`L²`-null sequence tends to zero. -/
theorem tendsto_integral_smul_bilin_zero {X : Type*} [MeasurableSpace X] {ν : Measure X}
    [IsFiniteMeasure ν] (B : E₁ →L[ℝ] E₂ →L[ℝ] W) {ψ : X → ℝ}
    (hψ : AEStronglyMeasurable ψ ν) {M : ℝ} (hM : ∀ x, ‖ψ x‖ ≤ M) {u : ℕ → X → E₁}
    {v : ℕ → X → E₂} (hu : ∀ n, MemLp (u n) 2 ν) (hv : ∀ n, MemLp (v n) 2 ν) {K : ℝ≥0∞}
    (hK : K ≠ ∞) (hub : ∀ n, eLpNorm (u n) 2 ν ≤ K)
    (hv0 : Tendsto (fun n => eLpNorm (v n) 2 ν) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, ψ x • B (u n x) (v n x) ∂ν) atTop (𝓝 0) := by
  refine tendsto_integral_smul_bilin_weak_strong B hψ hM hu hv (v' := 0) MemLp.zero' hK hub
    (by simpa using hv0) ?_
  simp

variable {A V : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- `L²_loc(Ω)`-boundedness of a family of fields indexed by `ι`. -/
structure L2LocBounded {E : Type*} [NormedAddCommGroup E] {ι : Type*} (Ω : Opens (Fin d → ℝ))
    (u : ℕ → ι → (Fin d → ℝ) → E) : Prop where
  memLp : ∀ n i (C : Set (Fin d → ℝ)), IsCompact C → C ⊆ Ω → MemLp (u n i) 2 (volume.restrict C)
  bdd : ∀ i (C : Set (Fin d → ℝ)), IsCompact C → C ⊆ Ω →
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ n, eLpNorm (u n i) 2 (volume.restrict C) ≤ K

/-- Strong `L²_loc(Ω)` convergence to zero of a family of fields indexed by `ι`. -/
structure L2LocNull {E : Type*} [NormedAddCommGroup E] {ι : Type*} (Ω : Opens (Fin d → ℝ))
    (u : ℕ → ι → (Fin d → ℝ) → E) : Prop where
  memLp : ∀ n i (C : Set (Fin d → ℝ)), IsCompact C → C ⊆ Ω → MemLp (u n i) 2 (volume.restrict C)
  tendsto : ∀ i (C : Set (Fin d → ℝ)), IsCompact C → C ⊆ Ω →
    Tendsto (fun n => eLpNorm (u n i) 2 (volume.restrict C)) atTop (𝓝 0)

/-- Weak `L²_loc(Ω)` convergence `R_n ⇀ R` of curvature two-forms, tested against the
coframe pairings `f ↦ ∫ ψ act(f) g` (`g ∈ L²(C)`, `ψ` continuous and vanishing off the compact
`C ⊆ Ω`).  These are continuous linear maps of `f ∈ L²(C; A)`, so this is implied by weak
`L²(C)` convergence (for finite-dimensional `V`, componentwise). -/
def WeakActTendsto (act : A →L[ℝ] V →L[ℝ] V) (Ω : Opens (Fin d → ℝ))
    (R : ℕ → Fin d → Fin d → (Fin d → ℝ) → A) (R' : Fin d → Fin d → (Fin d → ℝ) → A) : Prop :=
  ∀ a b (C : Set (Fin d → ℝ)), IsCompact C → C ⊆ Ω → ∀ g : (Fin d → ℝ) → V,
    MemLp g 2 (volume.restrict C) → ∀ ψ : (Fin d → ℝ) → ℝ, Continuous ψ →
      (∀ x, x ∉ C → ψ x = 0) →
      Tendsto (fun n => ∫ x, ψ x • act (R n a b x) (g x)) atTop
        (𝓝 (∫ x, ψ x • act (R' a b x) (g x)))

theorem integral_test_eq_setIntegral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ψ : (Fin d → ℝ) → ℝ} {C : Set (Fin d → ℝ)}
    (hz : ∀ x, x ∉ C → ψ x = 0) (F : (Fin d → ℝ) → E) :
    ∫ x, ψ x • F x = ∫ x in C, ψ x • F x :=
  (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by rw [hz x hx, zero_smul]).symm

/-- **The first Bianchi identity passes to weak–strong limits.**  Let `(e_n, ω_n)` be `C¹`
coframes and connections (connection values acting multiplicatively on the fibre) such that
`e_n → e` strongly in `L²_loc(Ω)`, `ω_n` is bounded in `L²_loc(Ω)`, the torsions
`T_n = d e_n + ω_n ∧ e_n` tend to zero strongly in `L²_loc(Ω)`, and the curvatures
`R(ω_n)` are bounded in `L²_loc(Ω)` and converge weakly to `R ∈ L²_loc(Ω)`.  Then
`R ∧ e = 0` in distributions on `Ω`. -/
theorem isDistributionalBianchi_of_approx (act : A →L[ℝ] V →L[ℝ] V)
    (hact : ∀ (x y : A) (v : V), act (x * y) v = act x (act y v)) {Ω : Opens (Fin d → ℝ)}
    {e : ℕ → Fin d → (Fin d → ℝ) → V} {ω : ℕ → Fin d → (Fin d → ℝ) → A}
    (he1 : ∀ n a, ContDiff ℝ 1 (e n a)) (hω1 : ∀ n a, ContDiff ℝ 1 (ω n a))
    {e' : Fin d → (Fin d → ℝ) → V} {R' : Fin d → Fin d → (Fin d → ℝ) → A}
    (he : L2LocTendsto Ω e e') (hωb : L2LocBounded Ω ω)
    (hT : L2LocNull Ω fun n (ab : Fin d × Fin d) => classicalTorsion act (e n) (ω n) ab.1 ab.2)
    (hRb : L2LocBounded Ω fun n (ab : Fin d × Fin d) => classicalCurvature (ω n) ab.1 ab.2)
    (hRw : WeakActTendsto act Ω (fun n => classicalCurvature (ω n)) R')
    (hR' : ∀ a b (C : Set (Fin d → ℝ)), IsCompact C → C ⊆ Ω →
      MemLp (R' a b) 2 (volume.restrict C)) :
    IsDistributionalBianchi act Ω R' e' := by
  intro φ a b c
  set C := tsupport (φ : (Fin d → ℝ) → ℝ)
  have hC : IsCompact C := φ.hasCompactSupport
  have hCΩ : C ⊆ Ω := φ.tsupport_subset
  have : IsFiniteMeasure (volume.restrict C) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hC.measure_lt_top⟩
  have hz0 : ∀ x, x ∉ C → φ x = 0 := fun x hx => test_eq_zero_off φ hx
  have hzd : ∀ c x, x ∉ C → vpd φ c x = 0 := fun c x hx => vpd_test_eq_zero_off φ c hx
  obtain ⟨M0, hM0⟩ := exists_bound_of_eq_zero_off φ.continuous hC hz0
  have hφm : AEStronglyMeasurable (φ : (Fin d → ℝ) → ℝ) (volume.restrict C) :=
    φ.continuous.aestronglyMeasurable
  -- the three curvature–coframe products converge
  have hprod : ∀ a b c, Tendsto (fun n => ∫ x, φ x • act (classicalCurvature (ω n) a b x)
      (e n c x)) atTop (𝓝 (∫ x, φ x • act (R' a b x) (e' c x))) := by
    intro a b c
    obtain ⟨K, hK, hKb⟩ := hRb.bdd (a, b) C hC hCΩ
    have hw := hRw a b C hC hCΩ (e' c) (he.memLp_lim c C hC hCΩ) φ φ.continuous hz0
    simp only [integral_test_eq_setIntegral hz0] at hw ⊢
    exact tendsto_integral_smul_bilin_weak_strong act hφm hM0
      (fun n => hRb.memLp n (a, b) C hC hCΩ) (fun n => he.memLp n c C hC hCΩ)
      (he.memLp_lim c C hC hCΩ) hK hKb (he.tendsto c C hC hCΩ) hw
  -- the torsion terms tend to zero
  have hT1 : ∀ a b c, Tendsto (fun n => ∫ x, vpd φ a x • classicalTorsion act (e n) (ω n) b c x)
      atTop (𝓝 0) := by
    intro a b c
    obtain ⟨Ma, hMa⟩ := exists_bound_of_eq_zero_off (contDiff_vpd_test φ a).continuous hC
      (hzd a)
    simp only [integral_test_eq_setIntegral (hzd a)]
    have h := tendsto_integral_smul_of_L2' (V := V)
      (contDiff_vpd_test φ a).continuous.aestronglyMeasurable hMa
      (fun n => hT.memLp n (b, c) C hC hCΩ) MemLp.zero'
      (by refine (hT.tendsto (b, c) C hC hCΩ).congr fun n => ?_; congr 1; funext x; simp)
    simpa using h
  have hT2 : ∀ a b c, Tendsto (fun n => ∫ x, φ x • act (ω n a x)
      (classicalTorsion act (e n) (ω n) b c x)) atTop (𝓝 0) := by
    intro a b c
    obtain ⟨K, hK, hKb⟩ := hωb.bdd a C hC hCΩ
    simp only [integral_test_eq_setIntegral hz0]
    exact tendsto_integral_smul_bilin_zero act hφm hM0 (fun n => hωb.memLp n a C hC hCΩ)
      (fun n => hT.memLp n (b, c) C hC hCΩ) hK hKb (hT.tendsto (b, c) C hC hCΩ)
  -- integrability for splitting the Bianchi pairing
  have hint : ∀ (Rf : Fin d → Fin d → (Fin d → ℝ) → A) (ef : Fin d → (Fin d → ℝ) → V),
      (∀ a b, MemLp (Rf a b) 2 (volume.restrict C)) → (∀ c, MemLp (ef c) 2 (volume.restrict C)) →
      bianchiPairing act Rf ef φ a b c = (∫ x, φ x • act (Rf a b x) (ef c x)) +
        (∫ x, φ x • act (Rf b c x) (ef a x)) + ∫ x, φ x • act (Rf c a x) (ef b x) := by
    intro Rf ef hRf hef
    have i : ∀ a b c, Integrable (fun x => φ x • act (Rf a b x) (ef c x)) (volume.restrict C) :=
      fun a b c => integrable_smul_bilin act hφm hM0 (hRf a b) (hef c)
    unfold bianchiPairing bianchiForm
    rw [integral_test_eq_setIntegral hz0, integral_test_eq_setIntegral hz0,
      integral_test_eq_setIntegral hz0, integral_test_eq_setIntegral hz0]
    simp only [smul_add]
    rw [integral_add ((i a b c).fun_add (i b c a)) (i c a b), integral_add (i a b c) (i b c a)]
  have hlim : Tendsto (fun n => bianchiPairing act (classicalCurvature (ω n)) (e n) φ a b c)
      atTop (𝓝 (bianchiPairing act R' e' φ a b c)) := by
    rw [hint R' e' (fun a b => hR' a b C hC hCΩ) (fun c => he.memLp_lim c C hC hCΩ)]
    refine ((hprod a b c).add (hprod b c a)).add (hprod c a b) |>.congr fun n => ?_
    rw [hint _ _ (fun a b => hRb.memLp n (a, b) C hC hCΩ) (fun c => he.memLp n c C hC hCΩ)]
  have hzero : Tendsto (fun n => bianchiPairing act (classicalCurvature (ω n)) (e n) φ a b c)
      atTop (𝓝 0) := by
    have h := ((((hT1 a b c).neg.add (hT2 a b c)).add ((hT1 b c a).neg.add (hT2 b c a))).add
      ((hT1 c a b).neg.add (hT2 c a b)))
    simp only [neg_zero, add_zero] at h
    refine h.congr fun n => ?_
    rw [bianchi_integral_identity act hact (he1 n) (hω1 n) φ a b c]
    rfl
  exact tendsto_nhds_unique hlim hzero

end Limit


/-! ### From the distributional to the pointwise identity -/

section Pointwise

variable {A V : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- **Pointwise first Bianchi identity almost everywhere.**  If `R, e ∈ L²_loc(Ω)` and
`R ∧ e = 0` in distributions on `Ω`, then `(R ∧ e)_{abc}(x) = 0` for almost every `x ∈ Ω`
(fundamental lemma of the calculus of variations). -/
theorem ae_bianchi_of_isDistributionalBianchi (act : A →L[ℝ] V →L[ℝ] V)
    {Ω : Opens (Fin d → ℝ)} {R : Fin d → Fin d → (Fin d → ℝ) → A}
    {e : Fin d → (Fin d → ℝ) → V}
    (hR : ∀ a b (C : Set (Fin d → ℝ)), IsCompact C → C ⊆ Ω →
      MemLp (R a b) 2 (volume.restrict C))
    (he : ∀ c (C : Set (Fin d → ℝ)), IsCompact C → C ⊆ Ω → MemLp (e c) 2 (volume.restrict C))
    (hB : IsDistributionalBianchi act Ω R e) (a b c : Fin d) :
    ∀ᵐ x, x ∈ Ω → bianchiForm act R e a b c x = 0 := by
  have hloc : LocallyIntegrableOn (bianchiForm act R e a b c) Ω := by
    rw [locallyIntegrableOn_iff Ω.isOpen.isLocallyClosed]
    intro K hKΩ hK
    have : IsFiniteMeasure (volume.restrict K) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
    have i : ∀ a b c, Integrable (fun x => act (R a b x) (e c x)) (volume.restrict K) := by
      intro a b c
      have := integrable_smul_bilin act (ψ := fun _ => (1 : ℝ)) aestronglyMeasurable_const
        (M := 1) (fun _ => by simp) (hR a b K hK hKΩ) (he c K hK hKΩ)
      simpa using this
    exact ((i a b c).fun_add (i b c a)).fun_add (i c a b)
  refine Ω.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc fun g hg hgc hgs => ?_
  exact hB ⟨g, hg, hgc, hgs⟩ a b c

end Pointwise


/-- Non-vacuity of `isDistributionalBianchi_of_approx`: the zero coframe and connection
sequences (scalar fibre, `act` = multiplication) satisfy every hypothesis. -/
example (Ω : Opens (Fin 4 → ℝ)) :
    IsDistributionalBianchi (ContinuousLinearMap.mul ℝ ℝ) Ω (fun _ _ _ => (0 : ℝ))
      (fun _ _ => (0 : ℝ)) := by
  have hv : ∀ (a : Fin 4) (x : Fin 4 → ℝ), vpd (fun _ : Fin 4 → ℝ => (0 : ℝ)) a x = 0 := by
    intro a x; simp [vpd]
  have hT : ∀ a b : Fin 4, classicalTorsion (ContinuousLinearMap.mul ℝ ℝ)
      (fun _ _ => (0 : ℝ)) (fun _ _ => (0 : ℝ)) a b = fun _ => 0 := by
    intro a b; funext x; simp [classicalTorsion, hv]
  have hR : ∀ a b : Fin 4, classicalCurvature (fun _ _ => (0 : ℝ)) a b = fun _ => 0 := by
    intro a b; funext x; simp [classicalCurvature, hv]
  refine isDistributionalBianchi_of_approx (ContinuousLinearMap.mul ℝ ℝ)
    (fun x y v => by simp [mul_assoc]) (e := fun _ _ _ => 0) (ω := fun _ _ _ => 0)
    (fun _ _ => contDiff_const) (fun _ _ => contDiff_const) ⟨fun _ _ _ _ _ => MemLp.zero',
      fun _ _ _ _ => MemLp.zero', fun _ _ _ _ => by simp⟩
    ⟨fun _ _ _ _ _ => MemLp.zero', fun _ _ _ _ => ⟨0, by simp, fun _ => by simp⟩⟩
    ⟨fun _ _ _ _ _ => by rw [hT]; exact MemLp.zero', fun _ _ _ _ => by simp [hT]⟩
    ⟨fun _ _ _ _ _ => by rw [hR]; exact MemLp.zero',
      fun _ _ _ _ => ⟨0, by simp, fun _ => by simp [hR]⟩⟩
    (fun _ _ _ _ _ _ _ _ _ _ => by simp [hR]) (fun _ _ _ _ _ => MemLp.zero')


/-! ### Torsion passage with weakly convergent connection coefficients (literal-link route) -/

section WeakTorsion

variable {A V : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [CompleteSpace A]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

/-- Weak `L²_loc(Ω)` convergence of connection one-forms `ω_n ⇀ ω`, tested against the coframe
pairings `f ↦ ∫ ψ act(f) g` (`g ∈ L²(C)`, `ψ` continuous vanishing off the compact `C ⊆ Ω`);
implied by weak `L²(C)` convergence, and by strong convergence. -/
def WeakActTendsto1 (act : A →L[ℝ] V →L[ℝ] V) (Ω : Opens (Fin d → ℝ))
    (ω : ℕ → Fin d → (Fin d → ℝ) → A) (ω' : Fin d → (Fin d → ℝ) → A) : Prop :=
  ∀ a (C : Set (Fin d → ℝ)), IsCompact C → C ⊆ Ω → ∀ g : (Fin d → ℝ) → V,
    MemLp g 2 (volume.restrict C) → ∀ ψ : (Fin d → ℝ) → ℝ, Continuous ψ →
      (∀ x, x ∉ C → ψ x = 0) →
      Tendsto (fun n => ∫ x, ψ x • act (ω n a x) (g x)) atTop
        (𝓝 (∫ x, ψ x • act (ω' a x) (g x)))

/-- **Weak–strong passage in the distributional torsion** (literal-link route of
`thm:supp-renewal-palatini`): if `e_n → e` strongly in `L²_loc(Ω)` and the connection
coefficients are bounded in `L²_loc(Ω)` and converge only weakly (e.g. the temporal coefficient
`A_{0,h} ⇀ A_0` of `eq:main-link-convergence`, the spatial ones converging strongly), then
`⟨d e_n + ω_n ∧ e_n, φ⟩ → ⟨d e + ω ∧ e, φ⟩` for every test function. -/
theorem tendsto_torsionPairing_weak (act : A →L[ℝ] V →L[ℝ] V) {Ω : Opens (Fin d → ℝ)}
    {e : ℕ → Fin d → (Fin d → ℝ) → V} {e' : Fin d → (Fin d → ℝ) → V}
    {ω : ℕ → Fin d → (Fin d → ℝ) → A} {ω' : Fin d → (Fin d → ℝ) → A}
    (he : L2LocTendsto Ω e e') (hωb : L2LocBounded Ω ω) (hωw : WeakActTendsto1 act Ω ω ω')
    (φ : 𝓓(Ω, ℝ)) (a b : Fin d) :
    Tendsto (fun n => torsionPairing act (e n) (ω n) φ a b) atTop
      (𝓝 (torsionPairing act e' ω' φ a b)) := by
  set C := tsupport (φ : (Fin d → ℝ) → ℝ)
  have hC : IsCompact C := φ.hasCompactSupport
  have hCΩ : C ⊆ Ω := φ.tsupport_subset
  have : IsFiniteMeasure (volume.restrict C) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hC.measure_lt_top⟩
  have hz0 : ∀ x, x ∉ C → φ x = 0 := fun x hx => test_eq_zero_off φ hx
  have hza : ∀ c, ∀ x, x ∉ C → pderiv c φ x = 0 := fun c x hx => pderiv_eq_zero_off φ c hx
  obtain ⟨M0, hM0⟩ := exists_bound_of_eq_zero_off φ.continuous hC hz0
  have hd : ∀ c, ∃ M, ∀ x, ‖pderiv c φ x‖ ≤ M := fun c =>
    exists_bound_of_eq_zero_off (continuous_pderiv φ c) hC (hza c)
  obtain ⟨Ma, hMa⟩ := hd a
  obtain ⟨Mb, hMb⟩ := hd b
  have t1 := tendsto_integral_smul_of_L2' (continuous_pderiv φ a).aestronglyMeasurable hMa
    (fun n => he.memLp n b C hC hCΩ) (he.memLp_lim b C hC hCΩ) (he.tendsto b C hC hCΩ)
  have t2 := tendsto_integral_smul_of_L2' (continuous_pderiv φ b).aestronglyMeasurable hMb
    (fun n => he.memLp n a C hC hCΩ) (he.memLp_lim a C hC hCΩ) (he.tendsto a C hC hCΩ)
  have hprod : ∀ a b, Tendsto (fun n => ∫ x in C, φ x • act (ω n a x) (e n b x)) atTop
      (𝓝 (∫ x in C, φ x • act (ω' a x) (e' b x))) := by
    intro a b
    obtain ⟨K, hK, hKb⟩ := hωb.bdd a C hC hCΩ
    have hw := hωw a C hC hCΩ (e' b) (he.memLp_lim b C hC hCΩ) φ φ.continuous hz0
    simp only [integral_test_eq_setIntegral hz0] at hw
    exact tendsto_integral_smul_bilin_weak_strong act φ.continuous.aestronglyMeasurable hM0
      (fun n => hωb.memLp n a C hC hCΩ) (fun n => he.memLp n b C hC hCΩ)
      (he.memLp_lim b C hC hCΩ) hK hKb (he.tendsto b C hC hCΩ) hw
  unfold torsionPairing
  simp only [integral_test_eq_setIntegral (hza a), integral_test_eq_setIntegral (hza b),
    integral_test_eq_setIntegral hz0]
  exact (t1.neg.add t2).add ((hprod a b).sub (hprod b a))

/-- Torsion-free limit on the literal-link route: weakly convergent connection coefficients,
strongly convergent coframes, and vanishing tested torsion residuals give a torsion-free
limiting represented connection. -/
theorem isTorsionFree_of_tendsto_weak (act : A →L[ℝ] V →L[ℝ] V) {Ω : Opens (Fin d → ℝ)}
    {e : ℕ → Fin d → (Fin d → ℝ) → V} {e' : Fin d → (Fin d → ℝ) → V}
    {ω : ℕ → Fin d → (Fin d → ℝ) → A} {ω' : Fin d → (Fin d → ℝ) → A}
    (he : L2LocTendsto Ω e e') (hωb : L2LocBounded Ω ω) (hωw : WeakActTendsto1 act Ω ω ω')
    (hres : ∀ φ : 𝓓(Ω, ℝ), ∀ a b,
      Tendsto (fun n => torsionPairing act (e n) (ω n) φ a b) atTop (𝓝 0)) :
    IsTorsionFree act Ω e' ω' := fun φ a b =>
  tendsto_nhds_unique (tendsto_torsionPairing_weak act he hωb hωw φ a b) (hres φ a b)

end WeakTorsion

end RenewalGeometry.DistributionalBianchi
