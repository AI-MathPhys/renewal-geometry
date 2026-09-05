import NCG.Grand.ContinuumTorusFourierScreen
import NCG.Grand.FiniteTorusNormalizedFourierEquiv
import NCG.Grand.ZModCenteredFrequencyStabilization

/-!
# Compatibility of fixed Fourier screens with finite-torus interpolation

Every centered finite-torus Fourier mode lies in the range of the literal
interpolation isometry.  Since a fixed integer box is eventually represented
by centered residues without wraparound, the changing interpolation
projection eventually fixes the whole fixed continuum Fourier screen.
-/

open Filter

noncomputable section

local instance fixedFourierScreenCompatibility_measureSpace :
    MeasureTheory.MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩
local instance fixedFourierScreenCompatibility_isAddHaarMeasure :
    MeasureTheory.Measure.IsAddHaarMeasure
    (MeasureTheory.volume : MeasureTheory.Measure UnitAddCircle) :=
  inferInstanceAs (MeasureTheory.Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance fixedFourierScreenCompatibility_isProbabilityMeasure :
    MeasureTheory.IsProbabilityMeasure
    (MeasureTheory.volume : MeasureTheory.Measure UnitAddCircle) :=
  inferInstanceAs (MeasureTheory.IsProbabilityMeasure AddCircle.haarAddCircle)

namespace NCG

variable {N : ℕ} [NeZero N]
variable {d : Type*} [Fintype d] [DecidableEq d]

/-- A single centered continuum Fourier basis vector is the interpolation of
some finite-torus vector. -/
theorem exists_interpolation_eq_mFourierBasis_centered
    (q : d → ZMod N) :
    ∃ Phi : EuclideanSpace ℂ (d → ZMod N),
      finiteTorusFourierInterpolationCLM (N := N) (d := d) Phi =
        UnitAddTorus.mFourierBasis (finiteTorusCenteredFrequency q) := by
  let a : EuclideanSpace ℂ (d → ZMod N) :=
    EuclideanSpace.basisFun (d → ZMod N) ℂ q
  obtain ⟨Phi, hPhi⟩ :=
    exists_finiteTorus_function_with_normalizedFourier (N := N) (d := d) a
  refine ⟨Phi, ?_⟩
  change finiteTorusFourierInterpolation (WithLp.ofLp Phi) =
    UnitAddTorus.mFourierBasis (finiteTorusCenteredFrequency q)
  unfold finiteTorusFourierInterpolation
  simp_rw [hPhi]
  rw [Finset.sum_eq_single q]
  · simp [a, EuclideanSpace.basisFun_apply,
      UnitAddTorus.coe_mFourierBasis]
  · intro k _ hk
    simp [a, EuclideanSpace.basisFun_apply, hk]
  · simp

/-- The interpolation projection fixes every centered continuum Fourier
basis vector. -/
@[simp]
theorem finiteTorusFourierInterpolationProjection_apply_mFourierBasis_centered
    (q : d → ZMod N) :
    finiteTorusFourierInterpolationProjection (N := N) (d := d)
        (UnitAddTorus.mFourierBasis (finiteTorusCenteredFrequency q)) =
      UnitAddTorus.mFourierBasis (finiteTorusCenteredFrequency q) := by
  obtain ⟨Phi, hPhi⟩ := exists_interpolation_eq_mFourierBasis_centered q
  rw [← hPhi]
  exact finiteTorusFourierInterpolationProjection_apply_interpolation Phi

/-- Eventually, the changing interpolation projection fixes every basis mode
in one fixed integer Fourier box. -/
theorem eventually_interpolationProjection_fixes_mFourierBasis_in_box
    (R : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ k ∈ integerFourierBox d R,
      finiteTorusFourierInterpolationProjection (N := n + 1) (d := d)
          (UnitAddTorus.mFourierBasis k) =
        UnitAddTorus.mFourierBasis k := by
  filter_upwards
    [eventually_forall_mem_finiteBox_centeredFrequency_intCast_eq
      (integerFourierBox d R)] with n hn
  intro k hk
  let q : d → ZMod (n + 1) := fun j ↦ (k j : ZMod (n + 1))
  have hcenter : finiteTorusCenteredFrequency q = k := hn k hk
  rw [← hcenter]
  exact finiteTorusFourierInterpolationProjection_apply_mFourierBasis_centered q

/-- A linear map fixing every basis generator of a Fourier box fixes its
entire finite-dimensional span. -/
theorem continuousLinearMap_apply_eq_self_of_forall_mFourierBasis_box
    (R : ℕ) (T : ContinuumTorusL2 d →L[ℂ] ContinuumTorusL2 d)
    (hT : ∀ k ∈ integerFourierBox d R,
      T (UnitAddTorus.mFourierBasis k) = UnitAddTorus.mFourierBasis k) :
    ∀ f ∈ continuumTorusFourierBoxSubspace (d := d) R, T f = f := by
  intro f hf
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
  · intro x hx
    obtain ⟨k, hk, hkx⟩ := Finset.mem_map.mp hx
    rw [← hkx]
    simpa only [continuumTorusFourierBasisEmbedding,
      Function.Embedding.coeFn_mk, UnitAddTorus.coe_mFourierBasis] using hT k hk
  · exact map_zero T
  · intro x y _ _ hx hy
    rw [map_add, hx, hy]
  · intro c x _ hx
    rw [map_smul, hx]

/-- Eventually, the changing interpolation projection acts as the identity
on the whole fixed Fourier-box subspace. -/
theorem eventually_interpolationProjection_apply_eq_self_on_fourierBoxSubspace
    (R : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ f ∈
        continuumTorusFourierBoxSubspace (d := d) R,
      finiteTorusFourierInterpolationProjection (N := n + 1) (d := d) f = f := by
  filter_upwards
    [eventually_interpolationProjection_fixes_mFourierBasis_in_box
      (d := d) R] with n hn
  exact continuousLinearMap_apply_eq_self_of_forall_mFourierBasis_box R _ hn

/-- Eventually the changing interpolation projection is a left identity on
the fixed Fourier screen. -/
theorem eventually_interpolationProjection_comp_fourierScreen_eq
    (R : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      (finiteTorusFourierInterpolationProjection (N := n + 1) (d := d)).comp
          (continuumTorusFourierScreen (d := d) R) =
        continuumTorusFourierScreen (d := d) R := by
  filter_upwards
    [eventually_interpolationProjection_apply_eq_self_on_fourierBoxSubspace
      (d := d) R] with n hn
  apply ContinuousLinearMap.ext
  intro f
  apply hn
  rw [← continuumTorusFourierScreen_range (d := d) R]
  exact ⟨f, rfl⟩

/-- Eventually the fixed Fourier screen is also a left identity on the
changing interpolation projection. -/
theorem eventually_fourierScreen_comp_interpolationProjection_eq
    (R : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      (continuumTorusFourierScreen (d := d) R).comp
          (finiteTorusFourierInterpolationProjection (N := n + 1) (d := d)) =
        continuumTorusFourierScreen (d := d) R := by
  filter_upwards
    [eventually_interpolationProjection_comp_fourierScreen_eq
      (d := d) R] with n hn
  have hadj := congrArg ContinuousLinearMap.adjoint hn
  rw [ContinuousLinearMap.adjoint_comp,
    finiteTorusFourierInterpolationProjection_adjoint,
    continuumTorusFourierScreen_adjoint] at hadj
  exact hadj

/-- The fixed screen and changing interpolation projection eventually
commute (both compositions are the fixed screen). -/
theorem eventually_fourierScreen_commutes_interpolationProjection
    (R : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      (continuumTorusFourierScreen (d := d) R).comp
          (finiteTorusFourierInterpolationProjection (N := n + 1) (d := d)) =
        (finiteTorusFourierInterpolationProjection (N := n + 1) (d := d)).comp
          (continuumTorusFourierScreen (d := d) R) := by
  filter_upwards
    [eventually_fourierScreen_comp_interpolationProjection_eq (d := d) R,
      eventually_interpolationProjection_comp_fourierScreen_eq (d := d) R]
      with n hleft hright
  rw [hleft, hright]

end NCG
