/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.StandardModel.SMActiveStructural
import RenewalGeometry.Dimension.K4CutCycleIsotypicSchur

/-!
# Endpoint generation carrier (`prop:generation-carrier`)

`prop:generation-carrier` of the spacetime–gauge duality manuscript.  Let `G = G_{int|ST}` be
the shorted internal Gram (positive semidefinite, `thm:geometry-short`) on the categorical
carrier `ℂ^d`, and let `W₋` be the reversal-odd endpoint block of `eq:residual-S4` (the
standard `S₄` triplet, complex dimension three).  The source-minimal quotient is
`E / Ker G` (`eq:geometry-short-quotient`) and the supported complexification `G_gen` of
`W₋` is its image there (`supported`).

* `finrank_supported_of_strictlyPositiveOn`: if the restriction of a positive semidefinite
  Gram `G` to a subspace `W` is strictly positive, no direction of `W` enters the source kernel
  and `dim (image of W in E / Ker G) = dim W`;
* `endpoint_generation_carrier`: **`prop:generation-carrier`, boxed `dim_ℂ G_gen = 3`** —
  for the rank-three endpoint block `W₋` with strictly positive restricted shorted Gram;
* `strictlyPositiveOn_of_scalar`: on the explicit orthogonal active realization
  `G_{int|ST} = ϑ I_{12}`, `ϑ > 0`, the hypothesis is automatic (`endpoint_generation_carrier_explicit`);
* `signTwist_not_equivalent`: the sign-twisted triplet `(W ⊗ sgn)₋` is a distinct irreducible
  type — there is no invertible intertwiner from the standard triplet to its sign twist
  (`k4StandardToSignTwist_intertwiner_zero`), so it cannot be counted as a second generation
  source.

The value `dim W₋ = 3` on the explicit realization is `SMActive.generation_rank`
(`SMActiveStructural.lean`).
-/

open Matrix Module
open scoped ComplexOrder

namespace RenewalGeometry
namespace EndpointGenerationCarrier

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The source kernel `Ker G` of a Gram matrix on `ℂ^d`. -/
def sourceKernel (G : Matrix d d ℂ) : Submodule ℂ (d → ℂ) :=
  LinearMap.ker G.mulVecLin

/-- The supported complexification of a block `W`: its image in the source-minimal quotient
`E / Ker G`. -/
def supported (G : Matrix d d ℂ) (W : Submodule ℂ (d → ℂ)) :
    Submodule ℂ ((d → ℂ) ⧸ sourceKernel G) :=
  W.map (sourceKernel G).mkQ

/-- Strict positivity of the restriction of `G` to `W`: `⟨w, G w⟩ > 0` for `0 ≠ w ∈ W`. -/
def StrictlyPositiveOn (G : Matrix d d ℂ) (W : Submodule ℂ (d → ℂ)) : Prop :=
  ∀ w ∈ W, w ≠ 0 → 0 < (star w ⬝ᵥ G *ᵥ w).re

omit [DecidableEq d] in
/-- Strict positivity on `W` keeps `W` out of the source kernel. -/
theorem inf_sourceKernel_eq_bot {G : Matrix d d ℂ}
    {W : Submodule ℂ (d → ℂ)} (hpos : StrictlyPositiveOn G W) :
    W ⊓ sourceKernel G = ⊥ := by
  rw [Submodule.eq_bot_iff]
  rintro w ⟨hw, hker⟩
  by_contra hne
  have hGw : G *ᵥ w = 0 := hker
  have h := hpos w hw hne
  rw [hGw, dotProduct_zero, Complex.zero_re] at h
  exact lt_irrefl _ h

omit [DecidableEq d] in
/-- Strict positivity of the restricted Gram makes `W` inject into `E / Ker G`. -/
theorem finrank_supported_of_strictlyPositiveOn {G : Matrix d d ℂ}
    {W : Submodule ℂ (d → ℂ)} (hpos : StrictlyPositiveOn G W) :
    finrank ℂ (supported G W) = finrank ℂ W := by
  have hinj : Function.Injective ((sourceKernel G).mkQ ∘ₗ W.subtype) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_comp, Submodule.ker_mkQ, Submodule.eq_bot_iff]
    intro x hx
    rw [Submodule.mem_comap, Submodule.subtype_apply] at hx
    have hmem : (x : d → ℂ) ∈ W ⊓ sourceKernel G := ⟨x.2, hx⟩
    rw [inf_sourceKernel_eq_bot hpos, Submodule.mem_bot] at hmem
    exact Subtype.ext hmem
  have h := LinearMap.finrank_range_of_inj hinj
  rw [LinearMap.range_comp, Submodule.range_subtype] at h
  exact h

/-- **`prop:generation-carrier`, boxed `dim_ℂ G_gen = 3`.**  If the shorted Gram is positive
semidefinite and its restriction to the rank-three reversal-odd endpoint block `W₋` is strictly
positive, the supported complexification of `W₋` in the source-minimal quotient is
three-dimensional.  (Positive semidefiniteness is the standing `thm:geometry-short` context;
the count itself only uses the strict positivity on `W₋`.) -/
theorem endpoint_generation_carrier {G : Matrix d d ℂ} (_hG : G.PosSemidef)
    {Wminus : Submodule ℂ (d → ℂ)} (hdim : finrank ℂ Wminus = 3)
    (hpos : StrictlyPositiveOn G Wminus) :
    finrank ℂ (supported G Wminus) = 3 := by
  rw [finrank_supported_of_strictlyPositiveOn hpos, hdim]

/-- On the explicit orthogonal active realization `G = ϑ I`, `ϑ > 0`, the restricted Gram is
strictly positive on every subspace. -/
theorem strictlyPositiveOn_of_scalar {ϑ : ℝ} (hϑ : 0 < ϑ) (W : Submodule ℂ (d → ℂ)) :
    StrictlyPositiveOn ((ϑ : ℂ) • (1 : Matrix d d ℂ)) W := by
  intro w _ hne
  rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul,
    Complex.re_ofReal_mul]
  refine mul_pos hϑ ?_
  have hre : (star w ⬝ᵥ w).re = ∑ i, Complex.normSq (w i) := by
    simp only [dotProduct, Pi.star_apply, Complex.re_sum, Complex.star_def,
      ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
  rw [hre]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  exact Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _)
    ⟨i, Finset.mem_univ _, Complex.normSq_pos.mpr hi⟩

/-- The scalar Gram `ϑ I` is positive semidefinite for `ϑ ≥ 0`. -/
theorem posSemidef_scalar {ϑ : ℝ} (hϑ : 0 ≤ ϑ) :
    ((ϑ : ℂ) • (1 : Matrix d d ℂ)).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun w => ?_⟩
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
    simp
  · rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]
    have hre : (star w ⬝ᵥ w) = ((∑ i, Complex.normSq (w i) : ℝ) : ℂ) := by
      simp only [dotProduct, Pi.star_apply, Complex.star_def,
        ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_sum]
    rw [hre, ← Complex.ofReal_mul]
    exact Complex.zero_le_real.mpr
      (mul_nonneg hϑ (Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _))

/-- **`prop:generation-carrier` on the explicit orthogonal active realization**
`G_{int|ST} = ϑ I_{12}`: the hypothesis is automatic and the rank-three endpoint block `W₋`
has a three-dimensional supported complexification. -/
theorem endpoint_generation_carrier_explicit {ϑ : ℝ} (hϑ : 0 < ϑ)
    {Wminus : Submodule ℂ (Fin 12 → ℂ)} (hdim : finrank ℂ Wminus = 3) :
    finrank ℂ (supported ((ϑ : ℂ) • (1 : Matrix (Fin 12) (Fin 12) ℂ)) Wminus) = 3 :=
  endpoint_generation_carrier (posSemidef_scalar hϑ.le) hdim
    (strictlyPositiveOn_of_scalar hϑ Wminus)

/-- **The sign-twisted triplet is a distinct type.**  No invertible matrix intertwines the
standard `S₄` triplet (generated by the transposition and the four-cycle) with its sign twist,
so `(W ⊗ sgn)₋` is not a second copy of the generation type. -/
theorem signTwist_not_equivalent :
    ¬ ∃ B : Matrix (Fin 3) (Fin 3) ℂ, IsUnit B ∧
      B * k4StandardTransposition = -(k4StandardTransposition * B) ∧
      B * k4StandardFourCycle = -(k4StandardFourCycle * B) := by
  rintro ⟨B, hB, hs, ht⟩
  have h0 := k4StandardToSignTwist_intertwiner_zero B hs ht
  rw [h0] at hB
  exact not_isUnit_zero hB

/-- **`prop:generation-carrier`, assembled**: the boxed dimension count under the strict
positivity hypothesis, its automatic validity on the explicit `ϑ I` realization, and the
distinctness of the loop-provenance triplet. -/
theorem generation_carrier :
    (∀ {d : Type} [Fintype d] [DecidableEq d] {G : Matrix d d ℂ}, G.PosSemidef →
      ∀ {Wminus : Submodule ℂ (d → ℂ)}, finrank ℂ Wminus = 3 → StrictlyPositiveOn G Wminus →
        finrank ℂ (supported G Wminus) = 3)
    ∧ (∀ {ϑ : ℝ}, 0 < ϑ → ∀ {Wminus : Submodule ℂ (Fin 12 → ℂ)}, finrank ℂ Wminus = 3 →
        finrank ℂ (supported ((ϑ : ℂ) • (1 : Matrix (Fin 12) (Fin 12) ℂ)) Wminus) = 3)
    ∧ ¬ ∃ B : Matrix (Fin 3) (Fin 3) ℂ, IsUnit B ∧
        B * k4StandardTransposition = -(k4StandardTransposition * B) ∧
        B * k4StandardFourCycle = -(k4StandardFourCycle * B) := by
  refine ⟨?_, ?_, signTwist_not_equivalent⟩
  · intro d _ _ G hG Wminus hdim hpos
    exact endpoint_generation_carrier hG hdim hpos
  · intro ϑ hϑ Wminus hdim
    exact endpoint_generation_carrier_explicit hϑ hdim

end EndpointGenerationCarrier
end RenewalGeometry
