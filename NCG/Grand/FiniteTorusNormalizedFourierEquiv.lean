import NCG.Grand.FiniteTorusFourierPlancherel

/-!
# The normalized finite-torus Fourier equivalence

Plancherel says that the cardinality-normalized product Fourier transform is
an isometry of the finite counting `L²` space.  Since source and target are
the same finite-dimensional space, it is surjective and hence a linear
isometric equivalence.  Bundling this fact makes it possible to prescribe
finite Fourier coefficients without repeatedly unfolding inversion.
-/

noncomputable section

namespace NCG

variable {N : ℕ} [NeZero N]
variable {d : Type*} [Fintype d] [DecidableEq d]

theorem finiteTorusNormalizedFourier_add
    (Phi Psi : (d → ZMod N) → ℂ) (k : d → ZMod N) :
    finiteTorusNormalizedFourier (Phi + Psi) k =
      finiteTorusNormalizedFourier Phi k +
        finiteTorusNormalizedFourier Psi k := by
  unfold finiteTorusNormalizedFourier finiteTorusFourier
  simp only [Pi.add_apply, smul_add, Finset.sum_add_distrib]

theorem finiteTorusNormalizedFourier_smul
    (c : ℂ) (Phi : (d → ZMod N) → ℂ) (k : d → ZMod N) :
    finiteTorusNormalizedFourier (c • Phi) k =
      c • finiteTorusNormalizedFourier Phi k := by
  unfold finiteTorusNormalizedFourier
  change ((Real.sqrt (Fintype.card (d → ZMod N)) : ℂ)⁻¹) •
      finiteTorusFourier (fun x ↦ c • Phi x) k =
    c • ((Real.sqrt (Fintype.card (d → ZMod N)) : ℂ)⁻¹) • finiteTorusFourier Phi k
  rw [finiteTorusFourier_const_smul]
  simp only [smul_smul]
  congr 1
  ring

/-- The normalized finite-torus Fourier transform as a linear isometry of
finite counting `L²`. -/
def finiteTorusNormalizedFourierLinearIsometry :
    EuclideanSpace ℂ (d → ZMod N) →ₗᵢ[ℂ]
      EuclideanSpace ℂ (d → ZMod N) where
  toFun Phi := WithLp.toLp 2 fun k ↦
    finiteTorusNormalizedFourier (WithLp.ofLp Phi) k
  map_add' Phi Psi := by
    apply WithLp.ofLp_injective
    funext k
    simpa only [WithLp.ofLp_add, Pi.add_apply] using
      finiteTorusNormalizedFourier_add
        (WithLp.ofLp Phi) (WithLp.ofLp Psi) k
  map_smul' c Phi := by
    apply WithLp.ofLp_injective
    funext k
    simpa only [WithLp.ofLp_smul, Pi.smul_apply, RingHom.id_apply] using
      finiteTorusNormalizedFourier_smul c (WithLp.ofLp Phi) k
  norm_map' Phi := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _),
      EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    exact sum_norm_sq_finiteTorusNormalizedFourier (WithLp.ofLp Phi)

@[simp]
theorem finiteTorusNormalizedFourierLinearIsometry_apply
    (Phi : EuclideanSpace ℂ (d → ZMod N)) (k : d → ZMod N) :
    finiteTorusNormalizedFourierLinearIsometry Phi k =
      finiteTorusNormalizedFourier (WithLp.ofLp Phi) k := rfl

theorem finiteTorusNormalizedFourierLinearIsometry_surjective :
    Function.Surjective
      (finiteTorusNormalizedFourierLinearIsometry
        (N := N) (d := d)) := by
  exact LinearMap.surjective_of_injective
    (f := (finiteTorusNormalizedFourierLinearIsometry
      (N := N) (d := d)).toLinearMap)
    (finiteTorusNormalizedFourierLinearIsometry
      (N := N) (d := d)).injective

/-- The normalized finite-torus Fourier transform as a linear isometric
equivalence. -/
def finiteTorusNormalizedFourierLinearIsometryEquiv :
    EuclideanSpace ℂ (d → ZMod N) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ (d → ZMod N) :=
  LinearIsometryEquiv.ofSurjective
    (finiteTorusNormalizedFourierLinearIsometry
      (N := N) (d := d))
    finiteTorusNormalizedFourierLinearIsometry_surjective

/-- Arbitrary normalized Fourier coefficient data are realized by a unique
finite-torus vector. -/
theorem exists_finiteTorus_function_with_normalizedFourier
    (a : EuclideanSpace ℂ (d → ZMod N)) :
    ∃ Phi : EuclideanSpace ℂ (d → ZMod N),
      ∀ k, finiteTorusNormalizedFourier (WithLp.ofLp Phi) k = a k := by
  refine ⟨(finiteTorusNormalizedFourierLinearIsometryEquiv
    (N := N) (d := d)).symm a, fun k ↦ ?_⟩
  have h := (finiteTorusNormalizedFourierLinearIsometryEquiv
    (N := N) (d := d)).apply_symm_apply a
  exact congrFun (congrArg WithLp.ofLp h) k

end NCG
