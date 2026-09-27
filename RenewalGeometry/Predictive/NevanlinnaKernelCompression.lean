/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.Predictive.RationalKreinCanonicalRealization

/-!
# Head compression cannot increase the number of negative squares

Paper `predictive_spectral_geometry`, label `thm:supp-fibre-RG` (the clause
"Pontryagin negative-square index cannot increase" along an effective-space
compression `V`), proved through the mechanism of the paper's proof: "head
compression replaces each finite kernel Gram by a congruence".

* `PontryaginRealization.compress V Q = V* Q V` is the head-compressed matrix
  function.
* `PontryaginRealization.nevanlinnaKernel_compress`: the Nevanlinna kernel of
  `V* Q V` is `V* N_Q V`.
* `PontryaginRealization.kernelGram_compress`: every finite kernel Gram of the
  compressed function is a kernel Gram of `Q` (at the vectors `V h i`).
* `PontryaginRealization.negSquares_compress_le`: the number of negative
  squares cannot increase under compression (for a kernel whose Gram
  inertias are bounded, as is the case for every rational Hermitian `Q`).
* `NormalizedRationalHermitianData.negSquares_compress_toFun_le`: for a
  normalized rational Hermitian `Q` the compressed kernel has at most
  `negIndex [·,·]_Q` negative squares on every upper half-plane neighbourhood
  of infinity.

No isometry assumption on `V` is needed for these statements.
-/

open scoped InnerProductSpace InnerProduct
open Matrix

noncomputable section

namespace RenewalGeometry

namespace PontryaginRealization

variable {H H' : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']

/-- The head compression `V* Q V` of a matrix function along `V : H' → H`. -/
def compress (V : H' →L[ℂ] H) (Q : ℂ → H →L[ℂ] H) : ℂ → H' →L[ℂ] H' :=
  fun z => (V† ∘L Q z) ∘L V

/-- The Nevanlinna kernel of the compressed function is the compressed kernel. -/
theorem nevanlinnaKernel_compress (V : H' →L[ℂ] H) (Q : ℂ → H →L[ℂ] H) (z w : ℂ) :
    nevanlinnaKernel (compress V Q) z w = (V† ∘L nevanlinnaKernel Q z w) ∘L V := by
  unfold nevanlinnaKernel compress
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint]
  apply ContinuousLinearMap.ext
  intro x
  simp [ContinuousLinearMap.comp_apply, map_sub, map_smul]

/-- Every finite kernel Gram of the compressed function is a kernel Gram of the
original function (a congruence of the original Gram data). -/
theorem kernelGram_compress (V : H' →L[ℂ] H) (Q : ℂ → H →L[ℂ] H) {ι : Type*} [Fintype ι]
    (z : ι → ℂ) (h : ι → H') :
    kernelGram (nevanlinnaKernel (compress V Q)) z h =
      kernelGram (nevanlinnaKernel Q) z (fun i => V (h i)) := by
  ext i j
  simp only [kernelGram, Matrix.of_apply, nevanlinnaKernel_compress,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]

/-- **Compression monotonicity of the negative squares** (`thm:supp-fibre-RG`):
if the kernel Grams of `Q` on `D` have bounded negative inertia, then the
compressed function `V* Q V` has at most as many negative squares on `D`. -/
theorem negSquares_compress_le (V : H' →L[ℂ] H) (Q : ℂ → H →L[ℂ] H) (D : Set ℂ)
    (hbdd : BddAbove {κ | ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (z : ι → ℂ)
      (h : ι → H), (∀ i, z i ∈ D) ∧ negInertia (kernelGram (nevanlinnaKernel Q) z h) = κ}) :
    negSquares (nevanlinnaKernel (compress V Q)) D ≤ negSquares (nevanlinnaKernel Q) D := by
  apply negSquares_le
  intro ι _ _ z h hz
  rw [kernelGram_compress]
  exact le_csSup hbdd ⟨ι, inferInstance, inferInstance, z, fun i => V (h i), hz, rfl⟩

end PontryaginRealization

namespace NormalizedRationalHermitianData

variable {H H' : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
variable (Q : NormalizedRationalHermitianData H)

/-- Every kernel Gram of the Laurent-series function `Q` on an upper
half-plane neighbourhood of infinity has at most `negIndex [·,·]_Q` negative
eigenvalues. -/
theorem negInertia_kernelGram_toFun_le {ρ : ℝ} (hρ : ‖Q.canonical.A‖ ≤ ρ) {ι : Type}
    [Fintype ι] [DecidableEq ι] (z : ι → ℂ) (h : ι → H) (hz : ∀ i, z i ∈ upperNeighbourhood ρ) :
    negInertia (PontryaginRealization.kernelGram
      (PontryaginRealization.nevanlinnaKernel Q.toFun) z h) ≤ negIndex Q.form := by
  rw [Q.kernelGram_toFun_eq hρ z h hz, ← Q.negIndex_canonical_form]
  exact Q.canonical.negInertia_kernelGram_le_negIndex z h (fun i => (hz i).1)
    (fun i => isUnit_sub_algebraMap_of_norm_lt _ (lt_of_le_of_lt hρ (hz i).2))

/-- **`thm:supp-fibre-RG`, Pontryagin index clause.**  The head-compressed
function `V* Q V` has at most `negIndex [·,·]_Q` negative squares on every
upper half-plane neighbourhood of infinity `{0 < Im z, ρ < ‖z‖}`, `ρ ≥ ‖A_Q‖`
(and `Q` itself has exactly that many, `negSquares_toFun_eq_negIndex`). -/
theorem negSquares_compress_toFun_le {ρ : ℝ} (hρ : ‖Q.canonical.A‖ ≤ ρ) (V : H' →L[ℂ] H) :
    PontryaginRealization.negSquares
        (PontryaginRealization.nevanlinnaKernel (PontryaginRealization.compress V Q.toFun))
        (upperNeighbourhood ρ) ≤ negIndex Q.form := by
  rw [← Q.negSquares_toFun_eq_negIndex hρ]
  apply PontryaginRealization.negSquares_compress_le
  refine ⟨negIndex Q.form, ?_⟩
  rintro κ ⟨ι, _, _, z, h, hz, rfl⟩
  exact Q.negInertia_kernelGram_toFun_le hρ z h hz

end NormalizedRationalHermitianData

end RenewalGeometry

end
