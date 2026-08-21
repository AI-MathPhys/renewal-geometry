import NCG.Grand.ContinuumTorusFourierScreen
import NCG.Grand.FiniteFiberFourierInterpolation

/-!
# Fixed continuum Fourier screens with finite fibre

The scalar Fourier-box projection acts coordinatewise on any finite complex
fibre.  This is the common screen on the actual vector- and matrix-valued
continuum carrier used by the periodic covariant model.
-/

noncomputable section

namespace NCG

variable {d : Type*} [Fintype d] [DecidableEq d]
variable {r : Type*} [Fintype r]

/-- Coordinatewise scalar Fourier screen as a linear map on the finite-fibre
continuum carrier. -/
def finiteFiberContinuumFourierScreenLinearMap (R : ℕ) :
    FiniteFiberContinuumTorusL2 (d := d) (r := r) →ₗ[ℂ]
      FiniteFiberContinuumTorusL2 (d := d) (r := r) where
  toFun f := WithLp.toLp 2 fun a ↦
    continuumTorusFourierScreen (d := d) R (f a)
  map_add' f g := by
    apply WithLp.ofLp_injective
    funext a
    simp only [WithLp.ofLp_add, Pi.add_apply, map_add]
  map_smul' c f := by
    apply WithLp.ofLp_injective
    funext a
    simp only [WithLp.ofLp_smul, Pi.smul_apply, map_smul, RingHom.id_apply]

theorem finiteFiberContinuumFourierScreenLinearMap_norm_apply_le
    (R : ℕ) (f : FiniteFiberContinuumTorusL2 (d := d) (r := r)) :
    ‖finiteFiberContinuumFourierScreenLinearMap (d := d) (r := r) R f‖ ≤ ‖f‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _),
    PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  apply Finset.sum_le_sum
  intro a _
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2
    (continuumTorusFourierScreen_norm_apply_le R (f a))

/-- The fixed finite-fibre Fourier screen as a continuous linear map. -/
def finiteFiberContinuumFourierScreen (R : ℕ) :
    FiniteFiberContinuumTorusL2 (d := d) (r := r) →L[ℂ]
      FiniteFiberContinuumTorusL2 (d := d) (r := r) :=
  (finiteFiberContinuumFourierScreenLinearMap (d := d) (r := r) R).mkContinuous
    1 (fun f ↦ by
      simpa only [one_mul] using
        finiteFiberContinuumFourierScreenLinearMap_norm_apply_le
          (d := d) (r := r) R f)

@[simp]
theorem finiteFiberContinuumFourierScreen_apply
    (R : ℕ) (f : FiniteFiberContinuumTorusL2 (d := d) (r := r)) (a : r) :
    finiteFiberContinuumFourierScreen (d := d) (r := r) R f a =
      continuumTorusFourierScreen (d := d) R (f a) := rfl

theorem finiteFiberContinuumFourierScreen_norm_apply_le
    (R : ℕ) (f : FiniteFiberContinuumTorusL2 (d := d) (r := r)) :
    ‖finiteFiberContinuumFourierScreen (d := d) (r := r) R f‖ ≤ ‖f‖ :=
  finiteFiberContinuumFourierScreenLinearMap_norm_apply_le R f

theorem finiteFiberContinuumFourierScreen_opNorm_le_one (R : ℕ) :
    ‖finiteFiberContinuumFourierScreen (d := d) (r := r) R‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  simpa only [one_mul] using
    finiteFiberContinuumFourierScreen_norm_apply_le (d := d) (r := r) R f

/-- The finite-fibre Fourier screen is idempotent. -/
theorem finiteFiberContinuumFourierScreen_idempotent (R : ℕ) :
    (finiteFiberContinuumFourierScreen (d := d) (r := r) R).comp
        (finiteFiberContinuumFourierScreen (d := d) (r := r) R) =
      finiteFiberContinuumFourierScreen (d := d) (r := r) R := by
  apply ContinuousLinearMap.ext
  intro f
  apply WithLp.ofLp_injective
  funext a
  change continuumTorusFourierScreen (d := d) R
      (continuumTorusFourierScreen (d := d) R (f a)) =
    continuumTorusFourierScreen (d := d) R (f a)
  exact congrArg (fun T : ContinuumTorusL2 d →L[ℂ] ContinuumTorusL2 d ↦ T (f a))
    (continuumTorusFourierScreen_idempotent (d := d) R)

/-- The coordinatewise finite-fibre Fourier screen is self-adjoint. -/
theorem finiteFiberContinuumFourierScreen_adjoint (R : ℕ) :
    (finiteFiberContinuumFourierScreen (d := d) (r := r) R).adjoint =
      finiteFiberContinuumFourierScreen (d := d) (r := r) R := by
  symm
  apply (ContinuousLinearMap.eq_adjoint_iff
    (finiteFiberContinuumFourierScreen (d := d) (r := r) R)
    (finiteFiberContinuumFourierScreen (d := d) (r := r) R)).2
  intro f g
  simp only [PiLp.inner_apply, finiteFiberContinuumFourierScreen_apply]
  apply Finset.sum_congr rfl
  intro a _
  calc
    inner ℂ (continuumTorusFourierScreen (d := d) R (f a)) (g a) =
        inner ℂ (f a) ((continuumTorusFourierScreen (d := d) R).adjoint (g a)) :=
      ((continuumTorusFourierScreen (d := d) R).adjoint_inner_right
        (f a) (g a)).symm
    _ = inner ℂ (f a) (continuumTorusFourierScreen (d := d) R (g a)) := by
      rw [continuumTorusFourierScreen_adjoint]

end NCG
