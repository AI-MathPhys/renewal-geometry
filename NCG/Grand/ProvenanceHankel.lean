/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SealedProvenanceQuotient
import NCG.Grand.HankelMinimality

/-!
# Provenance-Hankel minimality
  (`thm:provenance-hankel-minimality`,
  Gran-Tensor manuscript)

* `provenance_hankel_minimality`: the boxed rank identity
  `rank 𝖧^prov = d_prov`: the source-reachable,
  Read-observable quotient of the sealed provenance carrier
  is canonically isomorphic to the column space of the
  provenance Hankel table
  `K_{λ;v,w} = R_λ·D_v·H_w` (so the Hankel rank equals the
  quotient dimension), and this rank is dominated by every
  finite sealed realization dimension.

The saturated-panel reconstruction formulas
`D̄_a[H_w x] = [H_{aw}x] - [H_a T_w x]` are the proved
reconstruction clause of `sealed_provenance_quotient`.
-/

open Matrix

namespace NCG

variable {σ ι l e y : Type*} [Fintype l] [Fintype e]
variable [Fintype y] [DecidableEq l] [DecidableEq e]

/-- The passive Read functional of a future label
`(λ, v, output)`. -/
def provRead (Dm : σ → Matrix e e ℂ) (R : ι → Matrix y e ℂ)
    (f : ι × List σ × y) : (e → ℂ) →ₗ[ℂ] ℂ where
  toFun n := ((R f.1 * wordD Dm f.2.1) *ᵥ n) f.2.2
  map_add' a b := by simp [Matrix.mulVec_add]
  map_smul' c a := by simp [Matrix.mulVec_smul]

/-- The provenance Hankel table `K_{λ;v,w}` in
coordinates. -/
def provTbl (T : σ → Matrix l l ℂ) (C : σ → Matrix e l ℂ)
    (Dm : σ → Matrix e e ℂ) (R : ι → Matrix y e ℂ)
    (f : ι × List σ × y) (q : List σ × l) : ℂ :=
  (R f.1 * wordD Dm f.2.1 * wordH T C Dm q.1) f.2.2 q.2

/-- The provenance state written by a past label
`(w, input)`. -/
def provState (T : σ → Matrix l l ℂ)
    (C : σ → Matrix e l ℂ) (Dm : σ → Matrix e e ℂ)
    (q : List σ × l) : e → ℂ :=
  fun j => wordH T C Dm q.1 j q.2

omit [Fintype y] in
/-- `thm:provenance-hankel-minimality`. -/
theorem provenance_hankel_minimality
    (T : σ → Matrix l l ℂ) (C : σ → Matrix e l ℂ)
    (Dm : σ → Matrix e e ℂ) (R : ι → Matrix y e ℂ) :
    Nonempty ((↥(Submodule.span ℂ
        (Set.range (provState T C Dm)))
        ⧸ (Submodule.comap
            (Submodule.span ℂ
              (Set.range (provState T C Dm))).subtype
            (⨅ f, LinearMap.ker (provRead Dm R f))))
      ≃ₗ[ℂ] ↥(Submodule.span ℂ
          (Set.range fun q (f : ι × List σ × y) =>
            provTbl T C Dm R f q)))
    ∧ Module.finrank ℂ (Submodule.span ℂ
        (Set.range fun q (f : ι × List σ × y) =>
          provTbl T C Dm R f q))
      ≤ Module.finrank ℂ (e → ℂ) := by
  apply hankel_minimality (provTbl T C Dm R)
    (provState T C Dm) (provRead Dm R)
  intro f q
  simp only [provRead, provTbl, provState,
    LinearMap.coe_mk, AddHom.coe_mk, Matrix.mulVec,
    dotProduct, Matrix.mul_apply]

end NCG
