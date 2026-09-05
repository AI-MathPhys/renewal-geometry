import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic

/-!
# Orientation bundling and the complete calibration residual

The four parts of the manuscript theorem are separated here: the two-section
symmetry obstruction, affine fibres and exact anchor count, quotienting unit
conventions, and reconstruction of object calibrations from a cocycle.
-/

namespace NCG.OrientationCalibrationResidual

section Orientation

/-- A packet fixed by orientation reversal cannot support an equivariant
choice between the two sections of the orientation torsor. -/
theorem invariant_packet_no_equivariant_orientation
    {P : Type*} (reverse : P → P) (p : P) (hp : reverse p = p) :
    ¬ ∃ choose : P → Bool, ∀ q, choose (reverse q) = !(choose q) := by
  rintro ⟨choose, hchoose⟩
  have h := hchoose p
  rw [hp] at h
  cases hq : choose p <;> simp [hq] at h

/-- An actual encoder together with a Read and fixed decoder is exactly an
equivalence of presentations with the two orientation sections. -/
theorem orientation_absorbed_iff_read_decoder {P : Type*} :
    Nonempty (P ≃ Bool) ↔
      ∃ (encode : Bool → P) (read : P → Bool),
        (∀ θ, read (encode θ) = θ) ∧ (∀ p, encode (read p) = p) := by
  constructor
  · rintro ⟨e⟩
    exact ⟨e.symm, e, e.apply_symm_apply, e.symm_apply_apply⟩
  · rintro ⟨encode, read, hleft, hright⟩
    exact ⟨Equiv.mk read encode hright hleft⟩

end Orientation

section AffineFibre

variable {V Y : Type*} [AddCommGroup V] [Module ℝ V]
  [AddCommGroup Y] [Module ℝ Y]

/-- The solutions to `Lx=b`. -/
def affineFibre (L : V →ₗ[ℝ] Y) (b : Y) : Set V := {x | L x = b}

/-- The translate of the homogeneous calibration kernel through `x₀`. -/
def kernelTranslate (L : V →ₗ[ℝ] Y) (x₀ : V) : Set V :=
  {x | x - x₀ ∈ LinearMap.ker L}

/-- Every nonempty calibration fibre is precisely `x₀ + ker L`. -/
theorem affineFibre_eq_kernelTranslate (L : V →ₗ[ℝ] Y) (b : Y) (x₀ : V)
    (hx₀ : L x₀ = b) : affineFibre L b = kernelTranslate L x₀ := by
  ext x
  constructor
  · intro hx
    change L x = b at hx
    change L (x - x₀) = 0
    simp [hx, hx₀]
  · intro hx
    change L (x - x₀) = 0 at hx
    change L x = b
    rw [map_sub, sub_eq_zero] at hx
    simpa [hx₀] using hx

variable [Module.Finite ℝ V]

/-- Rank-nullity gives the exact number of independent calibration anchors. -/
theorem calibration_kernel_dimension (L : V →ₗ[ℝ] Y) :
    Module.finrank ℝ (LinearMap.ker L) =
      Module.finrank ℝ V - Module.finrank ℝ (LinearMap.range L) := by
  have h := L.finrank_range_add_finrank_ker
  omega

/-- Any separating bank of `k` scalar anchors has at least as many coordinates
as the calibration kernel has dimensions. -/
theorem anchor_bank_lower_bound (L : V →ₗ[ℝ] Y) (k : ℕ)
    (A : LinearMap.ker L →ₗ[ℝ] (Fin k → ℝ)) (hA : Function.Injective A) :
    Module.finrank ℝ (LinearMap.ker L) ≤ k := by
  have h := A.finrank_le_finrank_of_injective hA
  simpa using h

/-- A basis and its coordinate functionals give a separating bank with
exactly `dim ker L` scalar anchors. -/
theorem exists_minimal_anchor_bank (L : V →ₗ[ℝ] Y) :
    ∃ A : LinearMap.ker L →ₗ[ℝ]
        (Fin (Module.finrank ℝ (LinearMap.ker L)) → ℝ),
      Function.Bijective A := by
  let k := Module.finrank ℝ (LinearMap.ker L)
  let e : LinearMap.ker L ≃ₗ[ℝ] (Fin k → ℝ) :=
    LinearEquiv.ofFinrankEq _ _ (by simp [k])
  exact ⟨e.toLinearMap, e.bijective⟩

end AffineFibre

section PhysicalResidual

variable {V Y U : Type*} [AddCommGroup V] [Module ℝ V]
  [AddCommGroup Y] [Module ℝ Y] [AddCommGroup U] [Module ℝ U]
  [Module.Finite ℝ V] [Module.Finite ℝ U]

/-- Conventional changes of units, regarded as vectors in the physical
calibration kernel. -/
def conventionMap (L : V →ₗ[ℝ] Y) (J : U →ₗ[ℝ] V)
    (hLJ : L.comp J = 0) : U →ₗ[ℝ] LinearMap.ker L :=
  J.codRestrict (LinearMap.ker L) fun u => by
    change L (J u) = 0
    have h := LinearMap.congr_fun hLJ u
    simpa using h

/-- The intrinsic residual is the calibration kernel modulo changes of units. -/
abbrev PhysicalResidual (L : V →ₗ[ℝ] Y) (J : U →ₗ[ℝ] V)
    (hLJ : L.comp J = 0) :=
  LinearMap.ker L ⧸ LinearMap.range (conventionMap L J hLJ)

/-- For injective unit conventions, quotient rank-nullity subtracts exactly
`rank J = dim U` from the calibration residual. -/
theorem physicalResidual_dimension (L : V →ₗ[ℝ] Y) (J : U →ₗ[ℝ] V)
    (hLJ : L.comp J = 0) (hJ : Function.Injective J) :
    Module.finrank ℝ (PhysicalResidual L J hLJ) =
      Module.finrank ℝ V - Module.finrank ℝ (LinearMap.range L) -
        Module.finrank ℝ U := by
  have hc : Function.Injective (conventionMap L J hLJ) := by
    intro x y hxy
    apply hJ
    exact congrArg Subtype.val hxy
  rw [Submodule.finrank_quotient,
    LinearMap.finrank_range_of_inj hc,
    calibration_kernel_dimension]

end PhysicalResidual

section Cocycle

variable {ι K : Type*} [AddCommGroup K]

/-- An additive cutoff calibration cocycle. -/
structure CalibrationCocycle (ι K : Type*) [AddCommGroup K] where
  gamma : ι → ι → K
  trans : ∀ i j k, gamma i k = gamma i j + gamma j k

/-- Choosing one base object reconstructs object calibrations. -/
def CalibrationCocycle.potential (γ : CalibrationCocycle ι K) (base : ι) : ι → K :=
  fun i => γ.gamma i base

/-- Every cocycle is the difference of its reconstructed object calibrations. -/
theorem CalibrationCocycle.eq_potential_sub (γ : CalibrationCocycle ι K)
    (base i j : ι) :
    γ.gamma i j = γ.potential base i - γ.potential base j := by
  have h := γ.trans i j base
  dsimp [CalibrationCocycle.potential]
  rw [h]
  abel

/-- Two object calibrations produce the same cocycle exactly when they differ
by one global translation. -/
theorem same_cocycle_iff_global_translation (base : ι) (x y : ι → K) :
    (∀ i j, x i - x j = y i - y j) ↔
      ∃ c : K, ∀ i, x i = y i + c := by
  constructor
  · intro h
    refine ⟨x base - y base, fun i => ?_⟩
    have hi := h i base
    calc
      x i = (x i - x base) + x base := by abel
      _ = (y i - y base) + x base := by rw [hi]
      _ = y i + (x base - y base) := by abel
  · rintro ⟨c, hc⟩ i j
    rw [hc i, hc j]
    abel

/-- If both translated object calibrations preserve the same incidence value,
their unique global translation lies in the incidence kernel. -/
theorem incidence_preserving_translation_lies_in_kernel
    {V Y : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup Y] [Module ℝ Y]
    (L : V →ₗ[ℝ] Y) (b : Y) (base : ι) (x y : ι → V) (c : V)
    (hx : ∀ i, L (x i) = b) (hy : ∀ i, L (y i) = b)
    (hshift : ∀ i, x i = y i + c) : c ∈ LinearMap.ker L := by
  change L c = 0
  have h := hx base
  rw [hshift base, map_add, hy base] at h
  exact add_left_cancel (h.trans (add_zero b).symm)

/-- An anchor bank closes calibration exactly when it separates the physical
residual quotient; this is the precise finite-dimensional criterion. -/
theorem cofinal_anchor_bank_closes_iff_separates
    {Q A : Type*} [AddCommGroup Q] [Module ℝ Q]
    [AddCommGroup A] [Module ℝ A] (bank : Q →ₗ[ℝ] A) :
    Function.Injective bank ↔ LinearMap.ker bank = ⊥ :=
  LinearMap.ker_eq_bot.symm

/-- Bundled exact statement of the finite orientation/calibration theorem. -/
theorem orientation_bundling_and_complete_calibration_residual
    {P : Type*} (reverse : P → P) (p : P) (hp : reverse p = p)
    {V Y U : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup Y] [Module ℝ Y] [AddCommGroup U] [Module ℝ U]
    [Module.Finite ℝ V] [Module.Finite ℝ U]
    (L : V →ₗ[ℝ] Y) (J : U →ₗ[ℝ] V) (hLJ : L.comp J = 0)
    (hJ : Function.Injective J) :
    (¬ ∃ choose : P → Bool, ∀ q, choose (reverse q) = !(choose q)) ∧
      Module.finrank ℝ (LinearMap.ker L) =
        Module.finrank ℝ V - Module.finrank ℝ (LinearMap.range L) ∧
      Module.finrank ℝ (PhysicalResidual L J hLJ) =
        Module.finrank ℝ V - Module.finrank ℝ (LinearMap.range L) -
          Module.finrank ℝ U := by
  exact ⟨invariant_packet_no_equivariant_orientation reverse p hp,
    calibration_kernel_dimension L, physicalResidual_dimension L J hLJ hJ⟩

end Cocycle

end NCG.OrientationCalibrationResidual
