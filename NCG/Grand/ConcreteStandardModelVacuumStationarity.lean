/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ConcreteStandardModelInvariantVacuum
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Stationarity of the concrete finite Standard-Model vacuum

The field record is varied along arbitrary affine real lines.  This gives a
literal finite first-variation statement without requiring an artificial
topology or coordinate instance on the record itself.
-/

open Matrix
open ComplexConjugate
open scoped BigOperators ComplexOrder

namespace NCG
namespace StandardModelInvariantVacuum

open ColourRestriction

attribute [fun_prop] Complex.differentiable_re

@[fun_prop] theorem differentiableAt_complex_re_comp
    {f : ℝ → ℂ} {u : ℝ} (hf : DifferentiableAt ℝ f u) :
    DifferentiableAt ℝ (fun x => (f x).re) u :=
  Complex.differentiable_re.differentiableAt.comp u hf

@[fun_prop] theorem differentiableAt_complex_im_comp
    {f : ℝ → ℂ} {u : ℝ} (hf : DifferentiableAt ℝ f u) :
    DifferentiableAt ℝ (fun x => (f x).im) u :=
  Complex.differentiable_im.differentiableAt.comp u hf

@[fun_prop] theorem differentiableAt_complex_star_comp
    {f : ℝ → ℂ} {u : ℝ} (hf : DifferentiableAt ℝ f u) :
    DifferentiableAt ℝ (fun x => star (f x)) u := by
  change DifferentiableAt ℝ (fun x => conj (f x)) u
  exact Complex.differentiable_conj.differentiableAt.comp u hf

@[fun_prop] theorem differentiableAt_complex_normSq_comp
    {f : ℝ → ℂ} {u : ℝ} (hf : DifferentiableAt ℝ f u) :
    DifferentiableAt ℝ (fun x => Complex.normSq (f x)) u := by
  simp only [Complex.normSq_apply]
  fun_prop

variable {V E F : Type*} [Fintype V] [Fintype E] [Fintype F]

/-- The affine real line through a finite Standard-Model field in an arbitrary
field direction. -/
def affineFieldLine (Φ δΦ : SMField V E) (u : ℝ) : SMField V E where
  linkC e i j := Φ.linkC e i j + (u : ℂ) * δΦ.linkC e i j
  linkW e i j := Φ.linkW e i j + (u : ℂ) * δΦ.linkW e i j
  higgs v i := Φ.higgs v i + (u : ℂ) * δΦ.higgs v i
  psi v i := Φ.psi v i + (u : ℂ) * δΦ.psi v i

@[simp] theorem affineFieldLine_zero (Φ δΦ : SMField V E) :
    affineFieldLine Φ δΦ 0 = Φ := by
  cases Φ
  simp [affineFieldLine]

/-- Coordinate form of the Hilbert--Schmidt square used by the concrete
plaquette densities. -/
theorem hsNormSq_eq_sum_normSq {m : Type*} [Fintype m]
    (A : Matrix m m ℂ) :
    hsNormSq A = ∑ i, ∑ j, Complex.normSq (A i j) := by
  unfold hsNormSq
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h := congrArg Complex.re
    (Complex.normSq_eq_conj_mul_self (z := A i j))
  simpa [Complex.star_def] using h.symm

@[fun_prop] theorem differentiableAt_curvC_affine_entry
    (P : Plaquette V E) (Φ δΦ : SMField V E) (i j : Fin 3) (u : ℝ) :
    DifferentiableAt ℝ (fun x => curvC P (affineFieldLine Φ δΦ x) i j) u := by
  change DifferentiableAt ℝ (fun x =>
    (∑ k, (affineFieldLine Φ δΦ x).linkC P.e₁ i k *
      (affineFieldLine Φ δΦ x).linkC P.e₂ k j) -
    ∑ k, (affineFieldLine Φ δΦ x).linkC P.e₄ i k *
      (affineFieldLine Φ δΦ x).linkC P.e₃ k j) u
  simp only [affineFieldLine]
  fun_prop

@[fun_prop] theorem differentiableAt_curvW_affine_entry
    (P : Plaquette V E) (Φ δΦ : SMField V E) (i j : Fin 2) (u : ℝ) :
    DifferentiableAt ℝ (fun x => curvW P (affineFieldLine Φ δΦ x) i j) u := by
  change DifferentiableAt ℝ (fun x =>
    (∑ k, (affineFieldLine Φ δΦ x).linkW P.e₁ i k *
      (affineFieldLine Φ δΦ x).linkW P.e₂ k j) -
    ∑ k, (affineFieldLine Φ δΦ x).linkW P.e₄ i k *
      (affineFieldLine Φ δΦ x).linkW P.e₃ k j) u
  simp only [affineFieldLine]
  fun_prop

@[fun_prop] theorem differentiableAt_hsNormSq_curvC_affine
    (P : Plaquette V E) (Φ δΦ : SMField V E) (u : ℝ) :
    DifferentiableAt ℝ (fun x => hsNormSq (curvC P (affineFieldLine Φ δΦ x))) u := by
  simp only [hsNormSq_eq_sum_normSq]
  fun_prop

@[fun_prop] theorem differentiableAt_hsNormSq_curvW_affine
    (P : Plaquette V E) (Φ δΦ : SMField V E) (u : ℝ) :
    DifferentiableAt ℝ (fun x => hsNormSq (curvW P (affineFieldLine Φ δΦ x))) u := by
  simp only [hsNormSq_eq_sum_normSq]
  fun_prop

set_option maxHeartbeats 600000 in
@[fun_prop] theorem differentiableAt_faceDensity_affine
    (g₃ g₂ : ℝ) (plaq : F → Plaquette V E) (p : F)
    (Φ δΦ : SMField V E) (u : ℝ) :
    DifferentiableAt ℝ
      (fun x => faceDensity g₃ g₂ plaq p (affineFieldLine Φ δΦ x)) u := by
  unfold faceDensity
  exact
    (differentiableAt_hsNormSq_curvC_affine (plaq p) Φ δΦ u).const_mul g₃ |>.add
      ((differentiableAt_hsNormSq_curvW_affine (plaq p) Φ δΦ u).const_mul g₂)

@[fun_prop] theorem differentiableAt_edgeResidual_affine
    (s t : E → V) (e : E) (i : Fin 2)
    (Φ δΦ : SMField V E) (u : ℝ) :
    DifferentiableAt ℝ
      (fun x => ((affineFieldLine Φ δΦ x).linkW e *ᵥ
        (affineFieldLine Φ δΦ x).higgs (s e)) i -
        (affineFieldLine Φ δΦ x).higgs (t e) i) u := by
  simp only [affineFieldLine, Matrix.mulVec, dotProduct]
  fun_prop

@[fun_prop] theorem differentiableAt_edgeDensity_affine
    (s t : E → V) (e : E) (Φ δΦ : SMField V E) (u : ℝ) :
    DifferentiableAt ℝ
      (fun x => edgeDensity s t e (affineFieldLine Φ δΦ x)) u := by
  unfold edgeDensity
  fun_prop

@[fun_prop] theorem differentiableAt_siteDensity_affine
    (lam vH : ℝ) (v : V) (Φ δΦ : SMField V E) (u : ℝ) :
    DifferentiableAt ℝ
      (fun x => siteDensity lam vH v (affineFieldLine Φ δΦ x)) u := by
  unfold siteDensity affineFieldLine
  fun_prop

@[fun_prop] theorem differentiableAt_fermionDensity_affine
    (Y : Matrix (Fin 4) (Fin 4) ℂ) (v : V)
    (Φ δΦ : SMField V E) (u : ℝ) :
    DifferentiableAt ℝ
      (fun x => fermionDensity Y v (affineFieldLine Φ δΦ x)) u := by
  unfold fermionDensity affineFieldLine
  fun_prop

/-- Along an affine line through the zero-fermion vacuum, the fermion
bilinear is exactly quadratic in the line parameter. -/
theorem fermionDensity_affine_invariantVacuum
    (Y : Matrix (Fin 4) (Fin 4) ℂ) (v : V)
    (vH : ℝ) (h₀ : Fin 2 → ℂ) (δΦ : SMField V E) (x : ℝ) :
    fermionDensity Y v
        (affineFieldLine (invariantVacuum vH h₀) δΦ x) =
      x ^ 2 * fermionDensity Y v δΦ := by
  unfold fermionDensity affineFieldLine invariantVacuum embed
  simp only [Pi.zero_apply, zero_add, map_mul, Complex.star_def,
    Complex.conj_ofReal]
  have hsum :
      (∑ a, ∑ b, (x : ℂ) * (starRingEnd ℂ) (δΦ.psi v a) * Y a b *
          ((x : ℂ) * δΦ.psi v b)) =
        ((x ^ 2 : ℝ) : ℂ) *
          (∑ a, ∑ b, (starRingEnd ℂ) (δΦ.psi v a) * Y a b *
            δΦ.psi v b) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    push_cast
    ring
  rw [hsum]
  exact Complex.re_ofReal_mul (x ^ 2)
    (∑ a, ∑ b, (starRingEnd ℂ) (δΦ.psi v a) * Y a b * δΦ.psi v b)

/-- Bosonic part of the actual regulated action. -/
noncomputable def regulatedStandardModelBosonicAction
    (s t : E → V) (g₃ g₂ lam vH : ℝ)
    (plaq : F → Plaquette V E) (Φ : SMField V E) : ℝ :=
  (2 : ℝ)⁻¹ * ∑ p, faceDensity g₃ g₂ plaq p Φ +
    (2 : ℝ)⁻¹ * ∑ e, edgeDensity s t e Φ +
    ∑ v, siteDensity lam vH v Φ

theorem hsNormSq_nonnegative {m : Type*} [Fintype m]
    (A : Matrix m m ℂ) : 0 ≤ hsNormSq A := by
  unfold hsNormSq
  have h := (Matrix.posSemidef_conjTranspose_mul_self A).trace_nonneg
  exact (Complex.le_def.mp h).1

theorem faceDensity_nonnegative (g₃ g₂ : ℝ) (hg₃ : 0 ≤ g₃) (hg₂ : 0 ≤ g₂)
    (plaq : F → Plaquette V E) (p : F) (Φ : SMField V E) :
    0 ≤ faceDensity g₃ g₂ plaq p Φ := by
  unfold faceDensity
  exact add_nonneg (mul_nonneg hg₃ (hsNormSq_nonnegative _))
    (mul_nonneg hg₂ (hsNormSq_nonnegative _))

theorem edgeDensity_nonnegative (s t : E → V) (e : E) (Φ : SMField V E) :
    0 ≤ edgeDensity s t e Φ := by
  unfold edgeDensity
  exact Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

theorem siteDensity_nonnegative (lam vH : ℝ) (hlam : 0 ≤ lam)
    (v : V) (Φ : SMField V E) : 0 ≤ siteDensity lam vH v Φ := by
  unfold siteDensity
  exact mul_nonneg hlam (sq_nonneg _)

theorem regulatedStandardModelBosonicAction_nonnegative
    (s t : E → V) (g₃ g₂ lam vH : ℝ)
    (hg₃ : 0 ≤ g₃) (hg₂ : 0 ≤ g₂) (hlam : 0 ≤ lam)
    (plaq : F → Plaquette V E) (Φ : SMField V E) :
    0 ≤ regulatedStandardModelBosonicAction s t g₃ g₂ lam vH plaq Φ := by
  unfold regulatedStandardModelBosonicAction
  exact add_nonneg
    (add_nonneg
      (mul_nonneg (by positivity)
        (Finset.sum_nonneg fun p _ =>
          faceDensity_nonnegative g₃ g₂ hg₃ hg₂ plaq p Φ))
      (mul_nonneg (by positivity)
        (Finset.sum_nonneg fun e _ => edgeDensity_nonnegative s t e Φ)))
    (Finset.sum_nonneg fun v _ => siteDensity_nonnegative lam vH hlam v Φ)

theorem regulatedStandardModelBosonicAction_invariantVacuum
    (s t : E → V) (g₃ g₂ lam vH : ℝ)
    (plaq : F → Plaquette V E) (h₀ : Fin 2 → ℂ)
    (hnorm : ∑ i, Complex.normSq (h₀ i) = 1) :
    regulatedStandardModelBosonicAction s t g₃ g₂ lam vH plaq
      (invariantVacuum vH h₀) = 0 := by
  simp [regulatedStandardModelBosonicAction,
    faceDensity_invariantVacuum g₃ g₂ plaq vH h₀,
    edgeDensity_invariantVacuum s t vH h₀,
    siteDensity_invariantVacuum (E := E) lam vH h₀ hnorm]

@[fun_prop] theorem differentiableAt_bosonicAction_affine
    (s t : E → V) (g₃ g₂ lam vH : ℝ)
    (plaq : F → Plaquette V E) (Φ δΦ : SMField V E) (u : ℝ) :
    DifferentiableAt ℝ (fun x => regulatedStandardModelBosonicAction
      s t g₃ g₂ lam vH plaq (affineFieldLine Φ δΦ x)) u := by
  unfold regulatedStandardModelBosonicAction
  fun_prop

/-- Every directional derivative of the concrete bosonic action vanishes at
the flat normalized vacuum. -/
theorem hasDerivAt_bosonicAction_invariantVacuum
    (s t : E → V) (g₃ g₂ lam vH : ℝ)
    (hg₃ : 0 ≤ g₃) (hg₂ : 0 ≤ g₂) (hlam : 0 ≤ lam)
    (plaq : F → Plaquette V E) (h₀ : Fin 2 → ℂ)
    (hnorm : ∑ i, Complex.normSq (h₀ i) = 1)
    (δΦ : SMField V E) :
    HasDerivAt (fun x => regulatedStandardModelBosonicAction
      s t g₃ g₂ lam vH plaq
        (affineFieldLine (invariantVacuum vH h₀) δΦ x)) 0 0 := by
  let f : ℝ → ℝ := fun x => regulatedStandardModelBosonicAction
    s t g₃ g₂ lam vH plaq
      (affineFieldLine (invariantVacuum vH h₀) δΦ x)
  have hf0 : f 0 = 0 := by
    simp [f, regulatedStandardModelBosonicAction_invariantVacuum
      s t g₃ g₂ lam vH plaq h₀ hnorm]
  have hmin : IsLocalMin f 0 := by
    apply Filter.Eventually.of_forall
    intro x
    rw [hf0]
    exact regulatedStandardModelBosonicAction_nonnegative
      s t g₃ g₂ lam vH hg₃ hg₂ hlam plaq _
  have hdiff : DifferentiableAt ℝ f 0 := by
    exact differentiableAt_bosonicAction_affine s t g₃ g₂ lam vH plaq
      (invariantVacuum vH h₀) δΦ 0
  have hd : deriv f 0 = 0 := hmin.deriv_eq_zero
  simpa [f, hd] using hdiff.hasDerivAt

/-- The complete fermion summand is quadratic along every affine line through
the zero-fermion vacuum, hence has zero first derivative there. -/
theorem hasDerivAt_fermionAction_invariantVacuum
    (Y : Matrix (Fin 4) (Fin 4) ℂ) (vH : ℝ) (h₀ : Fin 2 → ℂ)
    (δΦ : SMField V E) :
    HasDerivAt (fun x : ℝ => ∑ v, fermionDensity Y v
      (affineFieldLine (invariantVacuum vH h₀) δΦ x)) 0 0 := by
  let c : ℝ := ∑ v, fermionDensity Y v δΦ
  have heq : (fun x : ℝ => ∑ v, fermionDensity Y v
      (affineFieldLine (invariantVacuum vH h₀) δΦ x)) =
      fun x => x ^ 2 * c := by
    funext x
    simp only [fermionDensity_affine_invariantVacuum]
    rw [Finset.mul_sum]
  rw [heq]
  simpa [c] using ((hasDerivAt_pow 2 (0 : ℝ)).mul_const c)

/-- CA.8, literal field stationarity: for nonnegative gauge and Higgs
couplings, the complete signed regulated action has zero derivative at the
concrete invariant vacuum in every affine field direction.  No positivity
assumption is imposed on the Yukawa matrix: its contribution is quadratic
because the vacuum fermion field is zero. -/
theorem hasDerivAt_regulatedAction_invariantVacuum
    (s t : E → V) (g₃ g₂ lam vH : ℝ)
    (hg₃ : 0 ≤ g₃) (hg₂ : 0 ≤ g₂) (hlam : 0 ≤ lam)
    (Y : Matrix (Fin 4) (Fin 4) ℂ) (plaq : F → Plaquette V E)
    (h₀ : Fin 2 → ℂ) (hnorm : ∑ i, Complex.normSq (h₀ i) = 1)
    (δΦ : SMField V E) :
    HasDerivAt
      (fun x : ℝ => regulatedStandardModelAction (faceDensity g₃ g₂ plaq)
        (edgeDensity s t) (siteDensity lam vH) (fermionDensity Y)
        (affineFieldLine (invariantVacuum vH h₀) δΦ x)) 0 0 := by
  have hb := hasDerivAt_bosonicAction_invariantVacuum
    s t g₃ g₂ lam vH hg₃ hg₂ hlam plaq h₀ hnorm δΦ
  have hf := hasDerivAt_fermionAction_invariantVacuum Y vH h₀ δΦ
  change HasDerivAt (fun x : ℝ => regulatedStandardModelBosonicAction
    s t g₃ g₂ lam vH plaq
      (affineFieldLine (invariantVacuum vH h₀) δΦ x) +
    ∑ v, fermionDensity Y v
      (affineFieldLine (invariantVacuum vH h₀) δΦ x)) 0 0
  have h := hb.add hf
  change HasDerivAt (fun x : ℝ => regulatedStandardModelBosonicAction
    s t g₃ g₂ lam vH plaq
      (affineFieldLine (invariantVacuum vH h₀) δΦ x) +
    ∑ v, fermionDensity Y v
      (affineFieldLine (invariantVacuum vH h₀) δΦ x)) (0 + 0) 0 at h
  simpa using h

/-- Equivalent derivative-value form of concrete internal Euler
stationarity, quantified over every field direction. -/
theorem all_directional_derivatives_regulatedAction_vanish
    (s t : E → V) (g₃ g₂ lam vH : ℝ)
    (hg₃ : 0 ≤ g₃) (hg₂ : 0 ≤ g₂) (hlam : 0 ≤ lam)
    (Y : Matrix (Fin 4) (Fin 4) ℂ) (plaq : F → Plaquette V E)
    (h₀ : Fin 2 → ℂ) (hnorm : ∑ i, Complex.normSq (h₀ i) = 1) :
    ∀ δΦ : SMField V E,
      deriv (fun x : ℝ => regulatedStandardModelAction
        (faceDensity g₃ g₂ plaq) (edgeDensity s t)
        (siteDensity lam vH) (fermionDensity Y)
        (affineFieldLine (invariantVacuum vH h₀) δΦ x)) 0 = 0 := by
  intro δΦ
  exact (hasDerivAt_regulatedAction_invariantVacuum
    s t g₃ g₂ lam vH hg₃ hg₂ hlam Y plaq h₀ hnorm δΦ).deriv

/-- The same local action with explicit geometric cell weights.  These are
the finite q-coordinates whose negative doubled derivative is the internal
stress. -/
noncomputable def geometricallyWeightedStandardModelAction
    (s t : E → V) (g₃ g₂ lam vH : ℝ)
    (Y : Matrix (Fin 4) (Fin 4) ℂ) (plaq : F → Plaquette V E)
    (wF : F → ℝ) (wE : E → ℝ) (wS wΨ : V → ℝ)
    (Φ : SMField V E) : ℝ :=
  ∑ p, wF p * faceDensity g₃ g₂ plaq p Φ +
    ∑ e, wE e * edgeDensity s t e Φ +
    ∑ v, wS v * siteDensity lam vH v Φ +
    ∑ v, wΨ v * fermionDensity Y v Φ

/-- At the concrete invariant vacuum the geometrically weighted action is
zero for every choice of cell weights. -/
theorem geometricallyWeightedAction_invariantVacuum
    (s t : E → V) (g₃ g₂ lam vH : ℝ)
    (Y : Matrix (Fin 4) (Fin 4) ℂ) (plaq : F → Plaquette V E)
    (h₀ : Fin 2 → ℂ) (hnorm : ∑ i, Complex.normSq (h₀ i) = 1)
    (wF : F → ℝ) (wE : E → ℝ) (wS wΨ : V → ℝ) :
    geometricallyWeightedStandardModelAction s t g₃ g₂ lam vH Y plaq
      wF wE wS wΨ (invariantVacuum vH h₀) = 0 := by
  simp [geometricallyWeightedStandardModelAction,
    faceDensity_invariantVacuum g₃ g₂ plaq vH h₀,
    edgeDensity_invariantVacuum s t vH h₀,
    siteDensity_invariantVacuum (E := E) lam vH h₀ hnorm,
    fermionDensity_invariantVacuum (E := E) Y vH h₀]

/-- CA.8, literal geometric stationarity: along any (even non-differentiable)
one-parameter variation of all cell weights, the vacuum action is identically
zero and hence has derivative zero. -/
theorem hasDerivAt_geometricWeights_invariantVacuum
    (s t : E → V) (g₃ g₂ lam vH : ℝ)
    (Y : Matrix (Fin 4) (Fin 4) ℂ) (plaq : F → Plaquette V E)
    (h₀ : Fin 2 → ℂ) (hnorm : ∑ i, Complex.normSq (h₀ i) = 1)
    (wF : ℝ → F → ℝ) (wE : ℝ → E → ℝ)
    (wS wΨ : ℝ → V → ℝ) (x₀ : ℝ) :
    HasDerivAt (fun x => geometricallyWeightedStandardModelAction
      s t g₃ g₂ lam vH Y plaq (wF x) (wE x) (wS x) (wΨ x)
      (invariantVacuum vH h₀)) 0 x₀ := by
  have hzero : (fun x => geometricallyWeightedStandardModelAction
      s t g₃ g₂ lam vH Y plaq (wF x) (wE x) (wS x) (wΨ x)
      (invariantVacuum vH h₀)) = fun _ : ℝ => 0 := by
    funext x
    exact geometricallyWeightedAction_invariantVacuum
      s t g₃ g₂ lam vH Y plaq h₀ hnorm (wF x) (wE x) (wS x) (wΨ x)
  rw [hzero]
  exact hasDerivAt_const x₀ 0

/-- With the manuscript convention T_int = -2 D_q S_int, the concrete
vacuum stress vanishes along every geometric-weight variation. -/
theorem internalStress_invariantVacuum
    (s t : E → V) (g₃ g₂ lam vH : ℝ)
    (Y : Matrix (Fin 4) (Fin 4) ℂ) (plaq : F → Plaquette V E)
    (h₀ : Fin 2 → ℂ) (hnorm : ∑ i, Complex.normSq (h₀ i) = 1)
    (wF : ℝ → F → ℝ) (wE : ℝ → E → ℝ)
    (wS wΨ : ℝ → V → ℝ) (x₀ : ℝ) :
    -2 * deriv (fun x => geometricallyWeightedStandardModelAction
      s t g₃ g₂ lam vH Y plaq (wF x) (wE x) (wS x) (wΨ x)
      (invariantVacuum vH h₀)) x₀ = 0 := by
  rw [(hasDerivAt_geometricWeights_invariantVacuum
    s t g₃ g₂ lam vH Y plaq h₀ hnorm wF wE wS wΨ x₀).deriv]
  ring

set_option maxHeartbeats 1000000 in
/-- The actual regulated action is differentiable at the concrete invariant
vacuum along every affine field direction. -/
theorem differentiableAt_regulatedAction_invariantVacuum
    (s t : E → V) (g₃ g₂ lam vH : ℝ)
    (Y : Matrix (Fin 4) (Fin 4) ℂ) (plaq : F → Plaquette V E)
    (h₀ : Fin 2 → ℂ) (hnorm : ∑ i, Complex.normSq (h₀ i) = 1)
    (δΦ : SMField V E) :
    DifferentiableAt ℝ
      (fun x : ℝ => regulatedStandardModelAction (faceDensity g₃ g₂ plaq)
        (edgeDensity s t) (siteDensity lam vH) (fermionDensity Y)
        (affineFieldLine (invariantVacuum vH h₀) δΦ x)) 0 := by
  unfold regulatedStandardModelAction
  fun_prop

end StandardModelInvariantVacuum
end NCG
