/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ActionRigidity

/-!
# Weak-doublet invariant quartic rigidity

This file proves the invariant-theory core of
`thm:SMST-action-rigidity`.  The standard `SU(2) ≤ U(2)` action is written
explicitly on `ℂ²`; every doublet is radialized by an explicit group element.
Consequently an invariant quartic is a quadratic polynomial in the squared
radius, and positivity with one nonzero source sphere forces the stated square.
-/

namespace NCG
namespace WeakDoubletInvariantQuartic

/-- Squared Hermitian norm on a weak doublet. -/
def doubletNormSq (phi : ℂ × ℂ) : ℝ :=
  Complex.normSq phi.1 + Complex.normSq phi.2

/-- The standard `SU(2)` action with first row `(a,b)`. -/
def su2Action (a b : ℂ) (phi : ℂ × ℂ) : ℂ × ℂ :=
  (a * phi.1 + b * phi.2,
    -star b * phi.1 + star a * phi.2)

/-- Invariance under the standard `SU(2)` subgroup; this is implied by weak
`U(2)` invariance. -/
def SU2Invariant (V : ℂ × ℂ → ℝ) : Prop :=
  ∀ a b, Complex.normSq a + Complex.normSq b = 1 →
    ∀ phi, V (su2Action a b phi) = V phi

theorem doubletNormSq_nonneg (phi : ℂ × ℂ) :
    0 ≤ doubletNormSq phi := by
  exact add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)

/-- Every weak doublet is carried to its positive radial representative by an
explicit `SU(2)` matrix. -/
theorem exists_su2_radializer (phi : ℂ × ℂ) :
    ∃ a b : ℂ,
      Complex.normSq a + Complex.normSq b = 1 ∧
      su2Action a b phi =
        ((((Real.sqrt (doubletNormSq phi) : ℝ) : ℂ), 0) : ℂ × ℂ) := by
  let s := doubletNormSq phi
  have hs : 0 ≤ s := doubletNormSq_nonneg phi
  by_cases hs0 : s = 0
  · have hz : Complex.normSq phi.1 = 0 := by
      dsimp [s] at hs0
      simp [doubletNormSq] at hs0
      have h1 := Complex.normSq_nonneg phi.1
      have h2 := Complex.normSq_nonneg phi.2
      linarith
    have hw : Complex.normSq phi.2 = 0 := by
      dsimp [s] at hs0
      simp [doubletNormSq] at hs0
      have h1 := Complex.normSq_nonneg phi.1
      have h2 := Complex.normSq_nonneg phi.2
      linarith
    have hphi1 : phi.1 = 0 := Complex.normSq_eq_zero.mp hz
    have hphi2 : phi.2 = 0 := Complex.normSq_eq_zero.mp hw
    refine ⟨1, 0, by simp, ?_⟩
    simp [su2Action, hphi1, hphi2, s, hs0]
  · have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
    let r := Real.sqrt s
    have hrpos : 0 < r := Real.sqrt_pos.2 hspos
    have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hrpos.ne'
    have hrsq : r * r = s := Real.mul_self_sqrt hs
    refine ⟨star phi.1 / (r : ℂ), star phi.2 / (r : ℂ), ?_, ?_⟩
    · simp [Complex.normSq_conj,
        Complex.normSq_ofReal, hrsq, s, doubletNormSq]
      rw [← add_div]
      exact div_self (by simpa [s, doubletNormSq] using hs0)
    · apply Prod.ext
      · change star phi.1 / (r : ℂ) * phi.1 +
          star phi.2 / (r : ℂ) * phi.2 = (r : ℂ)
        rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div]
        apply (div_eq_iff hr0).2
        change (starRingEnd ℂ) phi.1 * phi.1 +
          (starRingEnd ℂ) phi.2 * phi.2 =
          (r : ℂ) * (r : ℂ)
        rw [← Complex.normSq_eq_conj_mul_self,
          ← Complex.normSq_eq_conj_mul_self]
        exact_mod_cast hrsq.symm
      · simp [su2Action]
        field_simp [hr0]
        ring

/-- An invariant function is determined by the squared radius. -/
theorem invariant_eq_radial (V : ℂ × ℂ → ℝ) (hV : SU2Invariant V)
    (phi : ℂ × ℂ) :
    V phi = V (((Real.sqrt (doubletNormSq phi) : ℝ) : ℂ), 0) := by
  obtain ⟨a, b, hab, hrad⟩ := exists_su2_radializer phi
  have hinv := hV a b hab phi
  rw [hrad] at hinv
  exact hinv.symm

/-- A degree-at-most-four polynomial written on the real radial axis. -/
def axisQuartic (c4 c3 c2 c1 c0 r : ℝ) : ℝ :=
  c4 * r ^ 4 + c3 * r ^ 3 + c2 * r ^ 2 + c1 * r + c0

/-- `SU(2)` invariance kills the odd coefficients of a radial-axis quartic. -/
theorem invariant_axisQuartic_odd_coefficients_zero
    (V : ℂ × ℂ → ℝ) (hV : SU2Invariant V)
    (c4 c3 c2 c1 c0 : ℝ)
    (haxis : ∀ r : ℝ,
      V ((r : ℂ), 0) = axisQuartic c4 c3 c2 c1 c0 r) :
    c3 = 0 ∧ c1 = 0 := by
  have heven (r : ℝ) :
      axisQuartic c4 c3 c2 c1 c0 (-r) =
        axisQuartic c4 c3 c2 c1 c0 r := by
    have hneg := hV (-1) 0 (by norm_num) ((r : ℂ), 0)
    simp [su2Action] at hneg
    rw [haxis] at hneg
    calc
      axisQuartic c4 c3 c2 c1 c0 (-r) = V (((-r : ℝ) : ℂ), 0) :=
        (haxis (-r)).symm
      _ = V (-((r : ℂ)), 0) := by rw [Complex.ofReal_neg]
      _ = axisQuartic c4 c3 c2 c1 c0 r := hneg
  have h1 := heven 1
  have h2 := heven 2
  simp [axisQuartic] at h1 h2
  constructor <;> linarith

/-- Complete `U(2)`-quartic rigidity on one weak doublet.  The axis-polynomial
hypothesis is exactly the restriction of a real polynomial of total degree at
most four; invariance proves that no other coordinate dependence survives. -/
theorem weakDoublet_invariantQuartic_rigidity
    (V : ℂ × ℂ → ℝ) (hV : SU2Invariant V)
    (c4 c3 c2 c1 c0 rho : ℝ) (hrho : 0 < rho)
    (haxis : ∀ r : ℝ,
      V ((r : ℂ), 0) = axisQuartic c4 c3 c2 c1 c0 r)
    (hnonneg : ∀ phi, 0 ≤ V phi)
    (hzero : ∀ phi, V phi = 0 ↔ doubletNormSq phi = rho ^ 2) :
    ∃! lambda : ℝ, 0 < lambda ∧
      ∀ phi, V phi = lambda * (doubletNormSq phi - rho ^ 2) ^ 2 := by
  obtain ⟨hc3, hc1⟩ :=
    invariant_axisQuartic_odd_coefficients_zero V hV c4 c3 c2 c1 c0 haxis
  let q : ℝ → ℝ := fun s => c4 * s ^ 2 + c2 * s + c0
  have hVrad (phi : ℂ × ℂ) : V phi = q (doubletNormSq phi) := by
    rw [invariant_eq_radial V hV phi, haxis]
    have hsqrt : Real.sqrt (doubletNormSq phi) ^ 2 =
        doubletNormSq phi := Real.sq_sqrt (doubletNormSq_nonneg phi)
    have hsqrt4 : Real.sqrt (doubletNormSq phi) ^ 4 =
        doubletNormSq phi ^ 2 := by
      calc
        Real.sqrt (doubletNormSq phi) ^ 4 =
            (Real.sqrt (doubletNormSq phi) ^ 2) ^ 2 := by ring
        _ = doubletNormSq phi ^ 2 := by rw [hsqrt]
    simp [axisQuartic, q, hc3, hc1, hsqrt, hsqrt4]
  have hrho2 : 0 < rho ^ 2 := sq_pos_of_pos hrho
  have hqzero : q (rho ^ 2) = 0 := by
    have hnorm : doubletNormSq (((rho : ℂ), 0) : ℂ × ℂ) = rho ^ 2 := by
      simp [doubletNormSq, Complex.normSq_ofReal, pow_two]
    have hz : V (((rho : ℂ), 0) : ℂ × ℂ) = 0 :=
      (hzero _).2 hnorm
    rw [hVrad, hnorm] at hz
    exact hz
  have hqnonneg : ∀ s : ℝ, 0 ≤ s → 0 ≤ q s := by
    intro s hs
    let phi : ℂ × ℂ := (((Real.sqrt s : ℝ) : ℂ), 0)
    have hnorm : doubletNormSq phi = s := by
      simp [phi, doubletNormSq, Complex.normSq_ofReal]
      exact Real.mul_self_sqrt hs
    rw [← hnorm, ← hVrad]
    exact hnonneg phi
  have hlocal : IsLocalMin q (rho ^ 2) := by
    filter_upwards [Ioi_mem_nhds hrho2] with s hs
    rw [hqzero]
    exact hqnonneg s hs.le
  have hderiv : HasDerivAt q (2 * c4 * rho ^ 2 + c2) (rho ^ 2) := by
    have h := ((((hasDerivAt_id (𝕜 := ℝ) (rho ^ 2)).pow 2).const_mul c4).add
      ((hasDerivAt_id (𝕜 := ℝ) (rho ^ 2)).const_mul c2)).add_const c0
    simpa [q, mul_comm, mul_left_comm, mul_assoc] using h
  have hstationary : 2 * c4 * rho ^ 2 + c2 = 0 :=
    hlocal.hasDerivAt_eq_zero hderiv
  have hfactor (s : ℝ) : q s = c4 * (s - rho ^ 2) ^ 2 := by
    dsimp [q] at hqzero ⊢
    have hc2 : c2 = -(2 * c4 * rho ^ 2) := by linarith
    have hc0 : c0 = c4 * (rho ^ 2) ^ 2 := by
      rw [hc2] at hqzero
      linarith
    rw [hc2, hc0]
    ring
  have hc4pos : 0 < c4 := by
    have hn := hqnonneg (rho ^ 2 + 1) (by positivity)
    have hne : q (rho ^ 2 + 1) ≠ 0 := by
      intro hz
      let phi : ℂ × ℂ :=
        (((Real.sqrt (rho ^ 2 + 1) : ℝ) : ℂ), 0)
      have hnorm : doubletNormSq phi = rho ^ 2 + 1 := by
        simp [phi, doubletNormSq, Complex.normSq_ofReal]
        exact Real.mul_self_sqrt (by positivity)
      have hvz : V phi = 0 := by rw [hVrad, hnorm, hz]
      have := (hzero phi).1 hvz
      rw [hnorm] at this
      linarith
    rw [hfactor] at hn hne
    norm_num at hn hne
    exact lt_of_le_of_ne hn (Ne.symm hne)
  refine ⟨c4, ⟨hc4pos, fun phi => (hVrad phi).trans (hfactor _)⟩, ?_⟩
  intro lambda hlambda
  have htest := hlambda.2
    ((((Real.sqrt (rho ^ 2 + 1) : ℝ) : ℂ), 0) : ℂ × ℂ)
  have hnorm : doubletNormSq
      ((((Real.sqrt (rho ^ 2 + 1) : ℝ) : ℂ), 0) : ℂ × ℂ) =
        rho ^ 2 + 1 := by
    simp [doubletNormSq, Complex.normSq_ofReal]
    exact Real.mul_self_sqrt (by positivity)
  rw [hVrad, hnorm, hfactor] at htest
  norm_num at htest
  exact htest.symm

end WeakDoubletInvariantQuartic
end NCG
