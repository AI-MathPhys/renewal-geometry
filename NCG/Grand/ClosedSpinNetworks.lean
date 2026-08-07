/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Closed spin networks separate gauge orbits
  (`cor:closed-spin-networks-separate-gauge-orbits`,
  Gran-Tensor manuscript)

* `closed_spin_networks_separate`: two gauge configurations
  agree on every gauge-invariant complex function exactly when
  they lie on the same gauge orbit — the separating witness is
  the invariant indicator of the orbit, and conversely
  invariant functions are constant on orbits.

Rendering disclosed: the manuscript's spin-network coefficients
form an orthonormal basis of the invariant functions
(Peter–Weyl, `thm` above it in the tex), so separation by all
spin-network coefficients is separation by all invariant
functions, which is the statement proved here on the finite
configuration space `G^E` with the gauge action of `G^V`.
-/

namespace NCG

/-- `cor:closed-spin-networks-separate-gauge-orbits`. -/
theorem closed_spin_networks_separate {G Ω : Type*} [Group G]
    [MulAction G Ω] (x y : Ω) :
    (∀ f : Ω → ℂ, (∀ (g : G) (z : Ω), f (g • z) = f z) →
      f x = f y)
      ↔ y ∈ MulAction.orbit G x := by
  classical
  constructor
  · intro hsep
    have hind := hsep
      (fun z => if z ∈ MulAction.orbit G x then 1 else 0)
      (fun g z => by
        by_cases hz : z ∈ MulAction.orbit G x
        · rw [if_pos hz, if_pos]
          obtain ⟨a, ha⟩ := hz
          have ha' : a • x = z := ha
          exact ⟨g * a, show (g * a) • x = g • z from by
            rw [mul_smul, ha']⟩
        · rw [if_neg hz, if_neg]
          intro hgz
          obtain ⟨a, ha⟩ := hgz
          have ha' : a • x = g • z := ha
          exact hz ⟨g⁻¹ * a, show (g⁻¹ * a) • x = z from by
            rw [mul_smul, ha', inv_smul_smul]⟩)
    rw [if_pos (MulAction.mem_orbit_self x)] at hind
    by_contra hy
    rw [if_neg hy] at hind
    exact one_ne_zero hind
  · rintro ⟨g, rfl⟩ f hf
    exact (hf g x).symm

end NCG
