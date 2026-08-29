/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.DenseHankelNormExhaustion

/-!
# Hilbert-space source quotient for universal Hankel exhaustion

The finite matrix module proves that the block Hankel matrices are the two
compressions C*C and C*TC and that the Gram rank is the Krylov dimension.
This file proves the missing Hilbert-space statement: the generalized source
quotient is exactly the Rayleigh radius on the range of C. Combined with the
dense-subspace theorem, this gives the manuscript's full norm exhaustion.
-/

open scoped InnerProductSpace

namespace NCG
namespace UniversalHankelHilbert

/-- The source-generated carrier of a bounded synthesis. -/
def sourceRange {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (C : F →L[ℂ] E) : Submodule ℂ E :=
  LinearMap.range C.toLinearMap

/-- The Gram quadratic form c*H0 c = ||C c||^2. -/
noncomputable def sourceGramForm {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (C : F →L[ℂ] E) (c : F) : ℝ :=
  ‖C c‖ ^ 2

/-- The shifted Hankel form c*H1 c = Re <T Cc,Cc>. -/
noncomputable def sourceShiftedForm {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (T : E →L[ℂ] E) (C : F →L[ℂ] E) (c : F) : ℝ :=
  Complex.re (inner ℂ (T (C c)) (C c))

/-- The generalized source radius. Kernel coefficients contribute the
standard zero Rayleigh quotient and hence do not affect the supremum. -/
noncomputable def sourceRayleighRadius {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (T : E →L[ℂ] E) (C : F →L[ℂ] E) : ℝ :=
  ⨆ c : F, |T.rayleighQuotient (C c)|

/-- Away from the Gram kernel, the displayed generalized Hankel quotient is
literally the Rayleigh quotient of the synthesized history. -/
theorem source_ratio_eq_rayleighQuotient
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (T : E →L[ℂ] E) (C : F →L[ℂ] E)
    (c : F) (_hc : C c ≠ 0) :
    sourceShiftedForm T C c / sourceGramForm C c =
      T.rayleighQuotient (C c) := by
  rfl

/-- The generalized source radius equals the Rayleigh radius of the
compression to the source-generated carrier. -/
theorem sourceRayleighRadius_eq_subspaceRayleighRadius
    {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (T : E →L[ℂ] E) (C : F →L[ℂ] E) :
    sourceRayleighRadius T C =
      subspaceRayleighRadius T (sourceRange C) := by
  have hbE : BddAbove
      (Set.range fun c : F => |T.rayleighQuotient (C c)|) :=
    ⟨‖T‖, by
      rintro _ ⟨c, rfl⟩
      exact T.rayleighQuotient_le_norm (C c)⟩
  have hbK : BddAbove
      (Set.range fun x : sourceRange C =>
        |T.rayleighQuotient (x : E)|) :=
    ⟨‖T‖, by
      rintro _ ⟨x, rfl⟩
      exact T.rayleighQuotient_le_norm (x : E)⟩
  apply le_antisymm
  · apply ciSup_le
    intro c
    let x : sourceRange C := ⟨C c, ⟨c, rfl⟩⟩
    exact le_ciSup hbK x
  · apply ciSup_le
    intro x
    obtain ⟨c, hc⟩ := x.2
    have hxc : (x : E) = C c := hc.symm
    rw [hxc]
    exact le_ciSup hbE c

/-- Complete analytic exhaustion: a dense union of source ranges exhausts
the norm of a bounded symmetric transfer. -/
theorem norm_eq_iSup_sourceRayleighRadius
    {E ι : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (F : ι → Type*) [∀ i, NormedAddCommGroup (F i)]
    [∀ i, InnerProductSpace ℂ (F i)]
    (T : E →L[ℂ] E) (hT : T.IsSymmetric)
    (C : ∀ i, F i →L[ℂ] E)
    (hdense : Dense (⋃ i, (sourceRange (C i) : Set E))) :
    ‖T‖ = ⨆ i, sourceRayleighRadius T (C i) := by
  rw [norm_eq_iSup_subspaceRayleighRadius T hT
    (fun i => sourceRange (C i)) hdense]
  congr 1
  funext i
  exact (sourceRayleighRadius_eq_subspaceRayleighRadius T (C i)).symm

end UniversalHankelHilbert
end NCG
