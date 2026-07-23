/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Dimension.EvenRank

/-!
# The primitive reduction `H_prim = H / rad ω`

**Definition `def:primitive-reduction`** (primitive revision sector):
the primitive space is the quotient of the modular label space by the
radical of the commutator form, `H_prim := H / rad ω`, and the induced
form `ω̄` is **nondegenerate** — the reduced twisted revision algebra is
the primitive Clifford factor.

For an alternating bilinear form `B` the (left) radical is the kernel of
`B : V →ₗ (V →ₗ K)`.  This file constructs the descended form on
`V ⧸ ker B` (`NCG.inducedForm`), shows it computes `B` on
representatives, is alternating, and is **separating** — the
nondegeneracy claim implicit in `def:primitive-reduction` and used by
`thm:radical-centre` / `thm:factor-quotients-corrected`. -/

namespace NCG

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
variable (B : LinearMap.BilinForm K V)

/-- **The primitive quotient** `H_prim = H / rad ω`
(Definition `def:primitive-reduction`): the label space modulo the
radical `rad B = ker B` of the commutator form. -/
abbrev PrimitiveQuotient := V ⧸ LinearMap.ker B

section Induced

/-- Skew symmetry from alternation. -/
theorem isAlt_skew (halt : LinearMap.IsAlt B) (u v : V) :
    B u v = -B v u := by
  have h0 := halt (u + v)
  simp only [map_add, LinearMap.add_apply, halt u, halt v, zero_add,
    add_zero] at h0
  linear_combination h0

variable (halt : LinearMap.IsAlt B)

/-- Step one of the descent: for each `x`, the functional `B x` kills
the radical, hence descends to the quotient. -/
noncomputable def dualDescend : V →ₗ[K] (PrimitiveQuotient B →ₗ[K] K) where
  toFun x := Submodule.liftQ _ (B x) (by
    intro r hr
    rw [LinearMap.mem_ker] at hr ⊢
    rw [isAlt_skew B halt x r, hr]
    simp)
  map_add' x y := by
    refine Submodule.linearMap_qext _ ?_
    ext v
    simp [Submodule.liftQ_apply]
  map_smul' c x := by
    refine Submodule.linearMap_qext _ ?_
    ext v
    simp [Submodule.liftQ_apply]

/-- **The induced form `ω̄` on the primitive quotient**
(Definition `def:primitive-reduction`). -/
noncomputable def inducedForm :
    LinearMap.BilinForm K (PrimitiveQuotient B) :=
  Submodule.liftQ _ (dualDescend B halt) (by
    intro r hr
    rw [LinearMap.mem_ker] at hr
    refine LinearMap.ext fun z => ?_
    obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective _ z
    change dualDescend B halt r (Submodule.mkQ _ v) = 0
    simp only [dualDescend, LinearMap.coe_mk, AddHom.coe_mk,
      Submodule.mkQ_apply, Submodule.liftQ_apply]
    rw [hr]
    simp)

@[simp]
theorem inducedForm_mk (x y : V) :
    inducedForm B halt (Submodule.Quotient.mk x)
      (Submodule.Quotient.mk y) = B x y := rfl

/-- The induced form is alternating. -/
theorem inducedForm_isAlt : LinearMap.IsAlt (inducedForm B halt) := by
  intro z
  obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective _ z
  exact halt v

/-- **The induced form is nondegenerate**
(Definition `def:primitive-reduction`, content claim): the primitive
quotient carries a separating commutator form — the reduced revision
algebra is a factor (`thm:radical-centre`). -/
theorem inducedForm_separating (z : PrimitiveQuotient B)
    (hz : ∀ w : PrimitiveQuotient B, inducedForm B halt z w = 0) :
    z = 0 := by
  obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective _ z
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
    LinearMap.mem_ker]
  refine LinearMap.ext fun y => ?_
  have hy := hz (Submodule.Quotient.mk y)
  simpa [Submodule.mkQ_apply] using hy

/-- **Theorem `thm:primitivity-canonical` / `thm:rank-criterion-main`**
(rank core): the primitive quotient carries a nondegenerate alternating
form, hence has **even** rank `2m` — the canonical primitive factor is
`Cl_{2m}(ℂ) ≅ M_{2^m}(ℂ)` (the Stone–von Neumann dimension count is the
noted analytic step). -/
theorem even_finrank_primitiveQuotient {V' : Type*} [AddCommGroup V']
    [Module K V'] [FiniteDimensional K V']
    (B : LinearMap.BilinForm K V') (halt : LinearMap.IsAlt B) :
    Even (Module.finrank K (PrimitiveQuotient B)) := by
  have haltQ := inducedForm_isAlt B halt
  have hreflQ : LinearMap.IsRefl (inducedForm B halt) :=
    LinearMap.IsAlt.isRefl haltQ
  have hnd : LinearMap.Nondegenerate (inducedForm B halt) := by
    refine (LinearMap.IsRefl.nondegenerate_iff_separatingLeft
      hreflQ).mpr ?_
    intro z hz
    exact inducedForm_separating B halt z hz
  exact even_finrank_of_isAlt_nondegenerate _ haltQ hnd

end Induced

end NCG
