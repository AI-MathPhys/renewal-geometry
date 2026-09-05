/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteTorusFourierInterpolationProjection

/-!
# Finite-fibre amplification of torus Fourier interpolation

The scalar interpolation isometry is applied coordinatewise over an arbitrary
finite fibre index.  The `PiLp 2` norm is the sum of the component squared
norms, so this amplification is again an isometry.  This supplies the literal
finite-dimensional vector- and matrix-fibre common carrier used by the
periodic covariant regulator.
-/

noncomputable section

/-- Use the normalized Haar probability measure underlying the torus Fourier
basis. -/
local instance : MeasureTheory.MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance : MeasureTheory.Measure.IsAddHaarMeasure
    (MeasureTheory.volume : MeasureTheory.Measure UnitAddCircle) :=
  inferInstanceAs (MeasureTheory.Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : MeasureTheory.IsProbabilityMeasure
    (MeasureTheory.volume : MeasureTheory.Measure UnitAddCircle) :=
  inferInstanceAs (MeasureTheory.IsProbabilityMeasure AddCircle.haarAddCircle)

namespace NCG

variable {N : ℕ} [NeZero N]
variable {d : Type*} [Fintype d] [DecidableEq d]
variable {r : Type*} [Fintype r]

/-- Finite-fibre lattice Hilbert space, written as an `L²` family of scalar
lattice spaces. -/
abbrev FiniteFiberLatticeL2 :=
  PiLp 2 (fun _ : r => EuclideanSpace ℂ (d → ZMod N))

/-- Finite-fibre continuum torus Hilbert space, written as an `L²` family of
scalar torus `L²` spaces. -/
abbrev FiniteFiberContinuumTorusL2 :=
  PiLp 2 (fun _ : r =>
    MeasureTheory.Lp ℂ 2
      (MeasureTheory.volume : MeasureTheory.Measure (UnitAddTorus d)))

/-- Coordinatewise amplification of discrete Fourier interpolation to any
finite complex fibre. -/
noncomputable def finiteFiberFourierInterpolationLinearIsometry :
    FiniteFiberLatticeL2 (N := N) (d := d) (r := r) →ₗᵢ[ℂ]
      FiniteFiberContinuumTorusL2 (d := d) (r := r) where
  toFun Phi := WithLp.toLp 2 fun a =>
    finiteTorusFourierInterpolationLinearIsometry
      (N := N) (d := d) (Phi a)
  map_add' Phi Psi := by
    apply WithLp.ofLp_injective
    funext a
    simp only [WithLp.ofLp_add, Pi.add_apply, map_add]
  map_smul' c Phi := by
    apply WithLp.ofLp_injective
    funext a
    simp only [WithLp.ofLp_smul, Pi.smul_apply, map_smul, RingHom.id_apply]
  norm_map' Phi := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),
      PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
    apply Finset.sum_congr rfl
    intro a _
    change ‖finiteTorusFourierInterpolationLinearIsometry
      (N := N) (d := d) (Phi a)‖ ^ 2 = ‖Phi a‖ ^ 2
    rw [LinearIsometry.norm_map]

@[simp]
theorem finiteFiberFourierInterpolationLinearIsometry_apply
    (Phi : FiniteFiberLatticeL2 (N := N) (d := d) (r := r)) (a : r) :
    finiteFiberFourierInterpolationLinearIsometry Phi a =
      finiteTorusFourierInterpolationLinearIsometry (Phi a) := rfl

/-- The finite-fibre interpolation remains injective. -/
theorem finiteFiberFourierInterpolation_injective :
    Function.Injective
      (finiteFiberFourierInterpolationLinearIsometry
        (N := N) (d := d) (r := r)) :=
  LinearIsometry.injective _

/-- Finite-fibre interpolation as a continuous linear map. -/
noncomputable def finiteFiberFourierInterpolationCLM :
    FiniteFiberLatticeL2 (N := N) (d := d) (r := r) →L[ℂ]
      FiniteFiberContinuumTorusL2 (d := d) (r := r) :=
  (finiteFiberFourierInterpolationLinearIsometry
    (N := N) (d := d) (r := r)).toContinuousLinearMap

/-- Hilbert adjoint of finite-fibre interpolation. -/
noncomputable def finiteFiberFourierInterpolationAdjoint :
    FiniteFiberContinuumTorusL2 (d := d) (r := r) →L[ℂ]
      FiniteFiberLatticeL2 (N := N) (d := d) (r := r) :=
  (finiteFiberFourierInterpolationCLM
    (N := N) (d := d) (r := r)).adjoint

/-- Orthogonal projection onto the finite-fibre centered-mode subspace. -/
noncomputable def finiteFiberFourierInterpolationProjection :
    FiniteFiberContinuumTorusL2 (d := d) (r := r) →L[ℂ]
      FiniteFiberContinuumTorusL2 (d := d) (r := r) :=
  (finiteFiberFourierInterpolationCLM
    (N := N) (d := d) (r := r)).comp
      (finiteFiberFourierInterpolationAdjoint
        (N := N) (d := d) (r := r))

/-- The amplified adjoint remains a left inverse. -/
@[simp]
theorem finiteFiberFourierInterpolationAdjoint_apply_interpolation
    (Phi : FiniteFiberLatticeL2 (N := N) (d := d) (r := r)) :
    finiteFiberFourierInterpolationAdjoint (N := N) (d := d) (r := r)
        (finiteFiberFourierInterpolationCLM (N := N) (d := d) (r := r) Phi) =
      Phi := by
  change (finiteFiberFourierInterpolationLinearIsometry
      (N := N) (d := d) (r := r)).toContinuousLinearMap.adjoint
      ((finiteFiberFourierInterpolationLinearIsometry
        (N := N) (d := d) (r := r)).toContinuousLinearMap Phi) = Phi
  have h := congrArg
    (fun T : FiniteFiberLatticeL2 (N := N) (d := d) (r := r) →L[ℂ]
        FiniteFiberLatticeL2 (N := N) (d := d) (r := r) => T Phi)
    (finiteFiberFourierInterpolationLinearIsometry
      (N := N) (d := d) (r := r)).adjoint_comp_self
  simpa only [ContinuousLinearMap.comp_apply, one_apply_eq_self] using h

/-- The amplified projection fixes every interpolated fibre vector. -/
@[simp]
theorem finiteFiberFourierInterpolationProjection_apply_interpolation
    (Phi : FiniteFiberLatticeL2 (N := N) (d := d) (r := r)) :
    finiteFiberFourierInterpolationProjection (N := N) (d := d) (r := r)
        (finiteFiberFourierInterpolationCLM (N := N) (d := d) (r := r) Phi) =
      finiteFiberFourierInterpolationCLM (N := N) (d := d) (r := r) Phi := by
  change finiteFiberFourierInterpolationCLM (N := N) (d := d) (r := r)
      (finiteFiberFourierInterpolationAdjoint (N := N) (d := d) (r := r)
        (finiteFiberFourierInterpolationCLM (N := N) (d := d) (r := r) Phi)) = _
  rw [finiteFiberFourierInterpolationAdjoint_apply_interpolation]

/-- The amplified finite-mode projection is idempotent. -/
theorem finiteFiberFourierInterpolationProjection_idempotent :
    finiteFiberFourierInterpolationProjection (N := N) (d := d) (r := r) ∘L
        finiteFiberFourierInterpolationProjection (N := N) (d := d) (r := r) =
      finiteFiberFourierInterpolationProjection (N := N) (d := d) (r := r) := by
  apply ContinuousLinearMap.ext
  intro f
  change finiteFiberFourierInterpolationCLM (N := N) (d := d) (r := r)
      (finiteFiberFourierInterpolationAdjoint (N := N) (d := d) (r := r)
        (finiteFiberFourierInterpolationCLM (N := N) (d := d) (r := r)
          (finiteFiberFourierInterpolationAdjoint (N := N) (d := d) (r := r) f))) =
    finiteFiberFourierInterpolationCLM (N := N) (d := d) (r := r)
      (finiteFiberFourierInterpolationAdjoint (N := N) (d := d) (r := r) f)
  rw [finiteFiberFourierInterpolationAdjoint_apply_interpolation]

/-- The amplified finite-mode projection is self-adjoint. -/
theorem finiteFiberFourierInterpolationProjection_adjoint :
    (finiteFiberFourierInterpolationProjection
      (N := N) (d := d) (r := r)).adjoint =
        finiteFiberFourierInterpolationProjection (N := N) (d := d) (r := r) := by
  unfold finiteFiberFourierInterpolationProjection
  rw [ContinuousLinearMap.adjoint_comp]
  unfold finiteFiberFourierInterpolationAdjoint
  rw [ContinuousLinearMap.adjoint_adjoint]

end NCG
