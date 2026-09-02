/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SourceIdealSplit
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal

/-!
# Primitive-writer saturation in the genuine GNS representation

This file instantiates the abstract closure lemma used for
`thm:primitive-writer-saturation` in Mathlib's GNS Hilbert space.  It proves
continuity of the cyclic orbit map from positivity of the state, identifies a
central projected sector with the range of its projection, transports norm
density to equality of closed GNS cyclic spans, and proves the faithful
detection clause by a nonzero primitive matrix coefficient.
-/

open scoped ComplexOrder InnerProductSpace
open UniformSpace

namespace NCG
namespace GNSPrimitiveWriterSaturation

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The canonical cyclic orbit map `a ↦ pi_omega(a) Omega_omega`, realized
as the completion class of the pre-GNS vector represented by `a`. -/
def cyclicOrbit (omega : A →ₚ[ℂ] ℂ) (a : A) : omega.GNS :=
  (omega.toPreGNS a : omega.GNS)

/-- The cyclic orbit map is complex linear. -/
def cyclicOrbitLinear (omega : A →ₚ[ℂ] ℂ) : A →ₗ[ℂ] omega.GNS where
  toFun := cyclicOrbit omega
  map_add' a b := by
    change ((omega.toPreGNS (a + b) : omega.PreGNS) : omega.GNS) =
      (omega.toPreGNS a : omega.GNS) + (omega.toPreGNS b : omega.GNS)
    rw [map_add, Completion.coe_add]
  map_smul' c a := by
    change ((omega.toPreGNS (c • a) : omega.PreGNS) : omega.GNS) =
      c • (omega.toPreGNS a : omega.GNS)
    rw [map_smul, Completion.coe_smul]

theorem cyclicOrbit_norm_sq (omega : A →ₚ[ℂ] ℂ) (a : A) :
    ‖cyclicOrbit omega a‖ ^ 2 =
      (omega (star a * a)).re := by
  have h := omega.preGNS_norm_sq (omega.toPreGNS a)
  have hre := congrArg Complex.re h
  simpa only [cyclicOrbit, Completion.norm_coe,
    ← Complex.ofReal_pow, Complex.ofReal_re,
    PositiveLinearMap.ofPreGNS_toPreGNS] using hre

/-- Positivity of the functional supplies the missing norm-continuity of the
GNS cyclic map. -/
theorem continuous_cyclicOrbit (omega : A →ₚ[ℂ] ℂ) :
    Continuous (cyclicOrbit omega) := by
  obtain ⟨C, hC⟩ := omega.exists_norm_apply_le
  have hbound : ∀ a : A,
      ‖cyclicOrbitLinear omega a‖ ≤ Real.sqrt (C : ℝ) * ‖a‖ := by
    intro a
    rw [← sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))]
    rw [mul_pow, Real.sq_sqrt C.coe_nonneg]
    calc
      ‖cyclicOrbitLinear omega a‖ ^ 2 =
          (omega (star a * a)).re := cyclicOrbit_norm_sq omega a
      _ ≤ ‖omega (star a * a)‖ := Complex.re_le_norm _
      _ ≤ (C : ℝ) * ‖star a * a‖ := hC _
      _ = (C : ℝ) * ‖a‖ ^ 2 := by
        rw [CStarRing.norm_star_mul_self]
        ring
  exact (cyclicOrbitLinear omega).mkContinuous
    (Real.sqrt (C : ℝ)) hbound |>.continuous

/-- The selected central sector `z A`, expressed intrinsically as the fixed
space of left multiplication by `z`. -/
def selectedSector (z : A) : Set A := {a | z * a = a}

theorem selectedSector_eq_range (z : A) (hz : z * z = z) :
    selectedSector z = Set.range (fun a : A => z * a) := by
  ext a
  constructor
  · intro ha
    exact ⟨a, ha⟩
  · rintro ⟨b, rfl⟩
    change z * (z * b) = z * b
    rw [← mul_assoc, hz]

/-- **Primitive-writer saturation.**  A norm-dense primitive subset of the
selected central sector has exactly the same closed GNS cyclic span as the
whole selected algebra. -/
theorem primitive_writer_saturation_gns
    (omega : A →ₚ[ℂ] ℂ) (z : A) (B : Set A)
    (hB : B ⊆ selectedSector z)
    (hdense : selectedSector z ⊆ closure B) :
    closure (cyclicOrbit omega '' B) =
      closure (cyclicOrbit omega '' selectedSector z) :=
  primitive_writer_saturation (cyclicOrbit omega)
    (continuous_cyclicOrbit omega) B (selectedSector z) hB hdense

/-- Faithfulness on the selected sector makes every nonzero selected element
detectable by one finite primitive vector: some `b ∈ B` has a nonzero GNS
matrix coefficient against it. -/
theorem exists_primitive_detection
    (omega : A →ₚ[ℂ] ℂ) (z : A) (B : Set A)
    (hB : B ⊆ selectedSector z)
    (hdense : selectedSector z ⊆ closure B)
    (hFaithful : ∀ a ∈ selectedSector z, a ≠ 0 →
      omega (star a * a) ≠ 0)
    {a : A} (ha : a ∈ selectedSector z) (ha0 : a ≠ 0) :
    ∃ b ∈ B,
      inner ℂ (cyclicOrbit omega b) (cyclicOrbit omega a) ≠ 0 := by
  have haClosure :
      cyclicOrbit omega a ∈ closure (cyclicOrbit omega '' B) := by
    rw [primitive_writer_saturation_gns omega z B hB hdense]
    exact subset_closure ⟨a, ha, rfl⟩
  by_contra h
  push_neg at h
  let Z : Set omega.GNS :=
    {v | inner ℂ v (cyclicOrbit omega a) = 0}
  have hZclosed : IsClosed Z := by
    exact isClosed_eq (by fun_prop) (by fun_prop)
  have hsub : cyclicOrbit omega '' B ⊆ Z := by
    rintro _ ⟨b, hb, rfl⟩
    exact h b hb
  have haa : inner ℂ (cyclicOrbit omega a) (cyclicOrbit omega a) = 0 :=
    hZclosed.closure_subset_iff.mpr hsub haClosure
  have horbit0 : cyclicOrbit omega a = 0 :=
    inner_self_eq_zero.mp haa
  have hnorm : ‖cyclicOrbit omega a‖ ^ 2 = 0 := by
    rw [horbit0, norm_zero, zero_pow (by norm_num)]
  have hre : (omega (star a * a)).re = 0 := by
    rw [← cyclicOrbit_norm_sq omega a, hnorm]
  have hnonneg : 0 ≤ omega (star a * a) :=
    omega.map_nonneg (star_mul_self_nonneg a)
  have homega0 : omega (star a * a) = 0 := by
    have hreal : ((omega (star a * a)).re : ℂ) =
        omega (star a * a) := by
      exact Complex.conj_eq_iff_re.mp
        (by simpa [Complex.star_def] using hnonneg.star_eq)
    rw [← hreal, hre]
    simp
  exact hFaithful a ha ha0 homega0

end
end GNSPrimitiveWriterSaturation
end NCG
