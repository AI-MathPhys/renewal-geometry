/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# A rank-one renewal cut cannot create a source short
  (`thm:cut-source-short-master`, flagship manuscript)

For the scalar positive source short
`𝔖_{o|c} = ‖o‖² - |⟨c,o⟩|²/‖c‖²` (the squared distance of `o`
from the line `ℂc`), if clock and geometry source vectors pass
through the same exact renewal cut with the same post-cut factor,
`c = c₋⊗f`, `o = o₋⊗f`, then the boxed scaling

  `𝔖_{o|c} = ‖f‖²·𝔖_{o₋|c₋}`

holds (`cut_source_short`): the short vanishes after the cut
exactly when it vanished before (`cut_source_short_zero_iff`) —
a positive clock–geometry short cannot be blamed on the common
fresh factor.  Tensors are realized as Kronecker vectors on the
product index (disclosed model).
-/

open Finset
open scoped ComplexOrder

namespace NCG

variable {n m : Type*} [Fintype n] [Fintype m]

/-- The Kronecker vector `(u ⊗ f)(i,j) = u_i f_j`. -/
noncomputable def kronLp (u : EuclideanSpace ℂ n)
    (f : EuclideanSpace ℂ m) : EuclideanSpace ℂ (n × m) :=
  WithLp.toLp 2 fun p => u p.1 * f p.2

/-- The scalar positive source short
`𝔖_{o|c} = ‖o‖² - |⟨c,o⟩|²/‖c‖²`. -/
noncomputable def sourceShort {ι : Type*} [Fintype ι]
    (o c : EuclideanSpace ℂ ι) : ℝ :=
  ‖o‖ ^ 2 - ‖(inner ℂ c o : ℂ)‖ ^ 2 / ‖c‖ ^ 2

/-- Inner products of Kronecker vectors factor. -/
lemma kronLp_inner (u v : EuclideanSpace ℂ n)
    (f g : EuclideanSpace ℂ m) :
    (inner ℂ (kronLp u f) (kronLp v g) : ℂ)
      = (inner ℂ u v : ℂ) * (inner ℂ f g : ℂ) := by
  rw [PiLp.inner_apply, PiLp.inner_apply, PiLp.inner_apply]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [kronLp, RCLike.inner_apply]
  ring_nf
  rw [map_mul]
  ring

/-- Norms of Kronecker vectors factor (squared form). -/
lemma kronLp_norm_sq (u : EuclideanSpace ℂ n)
    (f : EuclideanSpace ℂ m) :
    ‖kronLp u f‖ ^ 2 = ‖u‖ ^ 2 * ‖f‖ ^ 2 := by
  have h1 : (inner ℂ (kronLp u f) (kronLp u f) : ℂ)
      = (inner ℂ u u : ℂ) * (inner ℂ f f : ℂ) :=
    kronLp_inner u u f f
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K,
    inner_self_eq_norm_sq_to_K, RCLike.ofReal_eq_complex_ofReal]
    at h1
  exact_mod_cast h1

/-- `thm:cut-source-short-master`, boxed scaling:
`𝔖_{o₋⊗f | c₋⊗f} = ‖f‖²·𝔖_{o₋|c₋}`. -/
theorem cut_source_short (cm om : EuclideanSpace ℂ n)
    (f : EuclideanSpace ℂ m) (hc : cm ≠ 0) (hf : f ≠ 0) :
    sourceShort (kronLp om f) (kronLp cm f)
      = ‖f‖ ^ 2 * sourceShort om cm := by
  have hcn : ‖cm‖ ≠ 0 := norm_ne_zero_iff.mpr hc
  have hfn : ‖f‖ ≠ 0 := norm_ne_zero_iff.mpr hf
  rw [sourceShort, sourceShort, kronLp_norm_sq, kronLp_norm_sq,
    kronLp_inner]
  have hip : ‖(inner ℂ cm om : ℂ) * (inner ℂ f f : ℂ)‖
      = ‖(inner ℂ cm om : ℂ)‖ * ‖f‖ ^ 2 := by
    rw [norm_mul, inner_self_eq_norm_sq_to_K (𝕜 := ℂ) f]
    congr 1
    rw [norm_pow, RCLike.norm_ofReal, abs_of_nonneg (norm_nonneg f)]
  rw [hip]
  field_simp

/-- The short vanishes after the cut exactly when it vanished
before. -/
theorem cut_source_short_zero_iff (cm om : EuclideanSpace ℂ n)
    (f : EuclideanSpace ℂ m) (hc : cm ≠ 0) (hf : f ≠ 0) :
    sourceShort (kronLp om f) (kronLp cm f) = 0
      ↔ sourceShort om cm = 0 := by
  rw [cut_source_short cm om f hc hf, mul_eq_zero]
  have hfn : ‖f‖ ^ 2 ≠ 0 := by
    have := norm_ne_zero_iff.mpr hf
    positivity
  constructor
  · rintro (h | h)
    · exact absurd h hfn
    · exact h
  · intro h
    exact Or.inr h

end NCG
