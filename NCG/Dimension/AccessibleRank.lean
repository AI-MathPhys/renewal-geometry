/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Dimension.EvenRank

/-!
# The parity-correct accessible modular rank

**Theorem `thm:accessible-modular-rank`**: if the full modular form is
nondegenerate on `H_full,acc = H_acc ⊕ ⟨t⟩`, then `b_eff = dim H_acc`
is **odd**, the spatial radical `rad(ω|_{H_acc})` is exactly
**one-dimensional**, the temporal generator `t` pairs nontrivially with
it, and `rank ω|_{H_full,acc} = 1 + b_eff`.

**Definition `def:accessible-revision-block`**: the accessible block is
`H_acc ≅ Hom(Λ/2Λ, 𝔽₂)` with `dim H_acc = b_eff` — encoded via the dual
space, whose dimension equals that of `Λ/2Λ`
(`NCG.finrank_accessibleBlock`). -/

namespace NCG

open Module

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

/-- The `B`-orthogonal annihilator of a subspace (with respect to the
first slot): the vectors pairing to zero with all of `H`. -/
def orthoAnn (B : LinearMap.BilinForm K V) (H : Submodule K V) :
    Submodule K V where
  carrier := {x | ∀ y ∈ H, B x y = 0}
  add_mem' := fun hx hy z hz => by
    rw [map_add, LinearMap.add_apply, hx z hz, hy z hz, add_zero]
  zero_mem' := fun z hz => by simp
  smul_mem' := fun c x hx z hz => by
    rw [map_smul, LinearMap.smul_apply, hx z hz, smul_zero]

theorem mem_orthoAnn {B : LinearMap.BilinForm K V} {H : Submodule K V}
    {x : V} : x ∈ orthoAnn B H ↔ ∀ y ∈ H, B x y = 0 := Iff.rfl

variable [FiniteDimensional K V]

/-- **Theorem `thm:accessible-modular-rank`**: for an alternating form
`B` nondegenerate on `V = H ⊕ ⟨t⟩` (every vector is `h + c·t`), with
`dim V = dim H + 1`:

* `b_eff = dim H` is odd;
* the spatial radical `H ⊓ H^⊥` is exactly one-dimensional (the
  temporal generator pairs injectively with it);
* `rank ω = dim V = 1 + b_eff`. -/
theorem accessible_modular_rank
    (B : LinearMap.BilinForm K V) (halt : LinearMap.IsAlt B)
    (hnd : LinearMap.Nondegenerate B)
    (H : Submodule K V) (t : V)
    (hspan : ∀ v : V, ∃ h ∈ H, ∃ c : K, v = h + c • t)
    (hdim : Module.finrank K V = Module.finrank K H + 1) :
    Odd (Module.finrank K H) ∧
      Module.finrank K ↥(H ⊓ orthoAnn B H) = 1 := by
  have hanti : ∀ u v : V, B u v = -B v u := by
    intro u v
    have h0 := halt (u + v)
    simp only [map_add, LinearMap.add_apply, halt u, halt v, zero_add,
      add_zero] at h0
    linear_combination h0
  have hrefl : LinearMap.IsRefl B := LinearMap.IsAlt.isRefl halt
  have hsep : ∀ x : V, (∀ y : V, B x y = 0) → x = 0 :=
    (LinearMap.IsRefl.nondegenerate_iff_separatingLeft hrefl).mp hnd
  -- b_eff is odd: dim V is even, dim V = dim H + 1
  have heven : Even (Module.finrank K V) :=
    even_finrank_of_isAlt_nondegenerate B halt hnd
  have hodd : Odd (Module.finrank K H) := by
    obtain ⟨k, hk⟩ := heven
    exact ⟨k - 1, by omega⟩
  refine ⟨hodd, le_antisymm ?_ ?_⟩
  · -- the radical injects into `K` via pairing with `t`
    set rad := H ⊓ orthoAnn B H with hrad
    have hinj : Function.Injective
        ((B.flip t).comp rad.subtype) := by
      rw [← LinearMap.ker_eq_bot]
      rw [Submodule.eq_bot_iff]
      rintro ⟨x, hx⟩ hker
      rw [LinearMap.mem_ker, LinearMap.comp_apply] at hker
      have hxt : B x t = 0 := by
        simpa [LinearMap.flip_apply] using hker
      have hxH : x ∈ H := hx.1
      have hxperp : ∀ y ∈ H, B x y = 0 := hx.2
      have hzero : x = 0 := by
        apply hsep
        intro v
        obtain ⟨h, hh, c, rfl⟩ := hspan v
        rw [map_add, map_smul, hxperp h hh, smul_eq_mul, hxt]
        ring
      simp [hzero]
    have := LinearMap.finrank_le_finrank_of_injective hinj
    simpa using this
  · -- the radical is nonzero: `H` is odd-dimensional, so `B|_H`
    -- degenerates
    have hoddH : Odd (Module.finrank K ↥H) := hodd
    have hnotnd := not_nondegenerate_of_isAlt_of_odd_finrank
      (B.restrict H) (fun w => halt (w : V)) hoddH
    have hreflH : LinearMap.IsRefl (B.restrict H) :=
      LinearMap.IsAlt.isRefl fun w => halt (w : V)
    rw [LinearMap.IsRefl.nondegenerate_iff_separatingLeft hreflH]
      at hnotnd
    have hex : ∃ w : ↥H, w ≠ 0 ∧ ∀ y : ↥H, B.restrict H w y = 0 := by
      by_contra hall
      push Not at hall
      exact hnotnd fun w hw => by
        by_contra hne
        obtain ⟨y, hy⟩ := hall w hne
        exact hy (hw y)
    obtain ⟨w, hw0, hwperp⟩ := hex
    have hmem : (w : V) ∈ H ⊓ orthoAnn B H := by
      refine ⟨w.2, fun y hy => ?_⟩
      exact hwperp ⟨y, hy⟩
    have hnontriv : Nontrivial ↥(H ⊓ orthoAnn B H) := by
      refine ⟨⟨⟨w, hmem⟩, 0, ?_⟩⟩
      intro hcontra
      apply hw0
      have hval : (w : V) = 0 := congrArg Subtype.val hcontra
      exact Subtype.coe_injective hval
    have hpos : 0 < Module.finrank K ↥(H ⊓ orthoAnn B H) :=
      (Module.finrank_pos_iff (R := K)).mpr hnontriv
    omega

omit [FiniteDimensional K V] in
/-- **Theorem `thm:accessible-modular-rank`, rank formula**: the full
accessible modular rank is `1 + b_eff` — a nondegenerate form has full
rank `dim V = dim H + 1`. -/
theorem accessible_rank_formula
    {H : Submodule K V}
    (hdim : Module.finrank K V = Module.finrank K H + 1) :
    Module.finrank K V = 1 + Module.finrank K H := by
  omega

/-- **Definition `def:accessible-revision-block`**: the accessible block
`H_acc ≅ Hom(Λ/2Λ, 𝔽₂)` has dimension `b_eff = dim Λ/2Λ` — universal
coefficients realise it as the dual of the mod-2 accessed lattice. -/
theorem finrank_accessibleBlock (W : Type*) [AddCommGroup W]
    [Module (ZMod 2) W] [Module.Finite (ZMod 2) W] :
    Module.finrank (ZMod 2) (Module.Dual (ZMod 2) W)
      = Module.finrank (ZMod 2) W :=
  Subspace.dual_finrank_eq

end NCG
