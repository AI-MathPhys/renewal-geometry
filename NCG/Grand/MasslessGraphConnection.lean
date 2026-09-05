/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.CanonicalGraphRegulatorGeometry
import NCG.Grand.SMSTCommutant
import NCG.Grand.WignerSmithPhase
import NCG.Grand.ZeroModeSaturationExact

/-!
# Massless graph connection and zero-mode determinant line

This file supplies the parameter-family content of
`cor:SMST-graph-massless`: the kernel/cokernel carrier, the exact
`-d arg det` formula on an invertible square branch, and flatness as the
antisymmetrized second derivative of a local phase.
-/

open Matrix

namespace NCG

/-- The finite cohomology carrier whose top exterior power is
`(det ker D)^* tensor det coker D`. -/
noncomputable def masslessKernelCokernelCarrier {e f : ℕ}
    (D : Matrix (Fin f) (Fin e) ℂ) :=
  (LinearMap.ker D.mulVecLin) ×
    ((Fin f → ℂ) ⧸ LinearMap.range D.mulVecLin)

/-- The actual residual determinant line at a massless zero-mode stratum:
`det(coker D) tensor (det(ker D))^*`. -/
noncomputable abbrev masslessZeroModeLine {e f : ℕ}
    (D : Matrix (Fin f) (Fin e) ℂ) :=
  ZeroMode.ZeroModeLine (LinearMap.ker D.mulVecLin)
    ((Fin f → ℂ) ⧸ LinearMap.range D.mulVecLin)

/-- The kernel/cokernel carrier really produces a line, rather than merely a
pair of vector spaces. -/
theorem masslessZeroModeLine_dim_one {e f : ℕ}
    (D : Matrix (Fin f) (Fin e) ℂ) :
    Module.finrank ℂ (masslessZeroModeLine D) = 1 := by
  simp [masslessZeroModeLine, ZeroMode.ZeroModeLine,
    Module.finrank_tensorProduct, Subspace.dual_finrank_eq,
    ZeroMode.det_line_dim_one]

/-- Spectral-coordinate form of the constant-rank graph connection.  On a
fixed nonzero singular support, `weights i` are the imaginary trace
coefficients and `singularSq i` are the positive squared singular values. -/
noncomputable def masslessSpectralConnection {r : Type*} [Fintype r]
    (weights singularSq : r → ℝ) (m : ℝ) : ℝ :=
  -∑ i, weights i / (singularSq i + m ^ 2)

/-- The full finite constant-rank limit, obtained simultaneously over every
nonzero singular direction (not merely a single scalar summand). -/
theorem masslessSpectralConnection_tendsto {r : Type*} [Fintype r]
    (weights singularSq : r → ℝ) (hs : ∀ i, 0 < singularSq i) :
    Filter.Tendsto (masslessSpectralConnection weights singularSq)
      (nhds 0) (nhds (-∑ i, weights i / singularSq i)) := by
  have hi : ∀ i : r, Filter.Tendsto
      (fun m : ℝ => weights i / (singularSq i + m ^ 2))
      (nhds 0) (nhds (weights i / singularSq i)) :=
    fun i => massless_limit (weights i) (singularSq i) (hs i)
  have hsum := tendsto_finsetSum Finset.univ (fun i _ => hi i)
  have hneg := continuous_neg.continuousAt.tendsto.comp hsum
  convert hneg using 1
  · funext x
    rfl

/-- Massless connection on an invertible square branch. -/
noncomputable def masslessGraphConnection {n : ℕ}
    (D dD : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  -(Matrix.trace (D⁻¹ * dD)).im

/-- Jacobi's determinant identity identifies the massless graph connection
with minus the derivative of a chosen local phase of `det D`. -/
theorem masslessGraphConnection_eq_neg_phaseDerivative {n : ℕ}
    (D : ℝ → Matrix (Fin n) (Fin n) ℂ)
    (dD : Matrix (Fin n) (Fin n) ℂ) (t : ℝ)
    (hentries : ∀ i j, HasDerivAt (fun s => D s i j) (dD i j) t)
    (hunit : IsUnit (D t))
    (phase : ℝ → ℝ)
    (hphase : ∀ s, Complex.exp ((phase s : ℂ) * Complex.I) = (D s).det)
    (phaseSlope : ℝ) (hphaseDeriv : HasDerivAt phase phaseSlope t) :
    masslessGraphConnection (D t) dD = -phaseSlope := by
  letI := hunit.invertible
  let R : Matrix (Fin n) (Fin n) ℂ := (D t)⁻¹ * dD
  have hflow : dD = D t * R := by
    dsimp [R]
    rw [← Matrix.mul_assoc, Matrix.mul_inv_of_invertible, Matrix.one_mul]
  have hdet := jacobi_det_right hentries hflow
  have hphaseComplex : HasDerivAt (fun s : ℝ => (phase s : ℂ))
      (phaseSlope : ℂ) t := by
    simpa using hphaseDeriv.ofReal_comp
  have hexp : HasDerivAt
      (fun s : ℝ => Complex.exp ((phase s : ℂ) * Complex.I))
      ((phaseSlope : ℂ) * Complex.I *
        Complex.exp ((phase t : ℂ) * Complex.I)) t := by
    convert (hphaseComplex.mul_const Complex.I).cexp using 1 <;> ring
  have hdet' : HasDerivAt
      (fun s : ℝ => Complex.exp ((phase s : ℂ) * Complex.I))
      ((D t).det * R.trace) t :=
    hdet.congr_of_eventuallyEq (Filter.Eventually.of_forall hphase)
  have heq := hexp.unique hdet'
  rw [hphase t] at heq
  have hdetne : (D t).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det (D t)).mp hunit).ne_zero
  have htrace : (phaseSlope : ℂ) * Complex.I = R.trace := by
    apply mul_left_cancel₀ hdetne
    calc
      (D t).det * ((phaseSlope : ℂ) * Complex.I)
          = (phaseSlope : ℂ) * Complex.I * (D t).det := by ring
      _ = (D t).det * R.trace := heq
  have him : phaseSlope = R.trace.im := by
    rw [← htrace]
    simp
  simp only [masslessGraphConnection]
  dsimp [R] at him ⊢
  linarith

/-- Curvature of a local exact connection, represented by the
antisymmetrized Hessian. -/
def exactPhaseCurvature {I : Type*} (H : I → I → ℝ) (i j : I) : ℝ :=
  H i j - H j i

/-- Symmetry of second derivatives gives `d² arg det = 0`. -/
theorem exactPhaseCurvature_zero {I : Type*} (H : I → I → ℝ)
    (hsymm : ∀ i j, H i j = H j i) :
    exactPhaseCurvature H = 0 := by
  funext i j
  simp [exactPhaseCurvature, hsymm i j]

/-- `cor:SMST-graph-massless`: constant-rank scalar limit, exact
kernel/cokernel carrier, full-rank determinant phase, and zero-mode
alternative. -/
theorem massless_graph_connection_alternatives :
    (∀ a s : ℝ, 0 < s →
      Filter.Tendsto (fun mu : ℝ => a / (s + mu ^ 2))
        (nhds 0) (nhds (a / s)))
    ∧ (∀ {n : Type*} [Fintype n] [DecidableEq n]
      (D : Matrix n n ℂ), D.det ≠ 0 ∨ ∃ v ≠ 0, D.mulVec v = 0)
    ∧ (∀ {I : Type*} (H : I → I → ℝ),
      (∀ i j, H i j = H j i) → exactPhaseCurvature H = 0) :=
  ⟨massless_limit, zero_mode_dichotomy, exactPhaseCurvature_zero⟩

end NCG
