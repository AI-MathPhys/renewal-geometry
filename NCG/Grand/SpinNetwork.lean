/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Finite holonomy–spin-network decomposition
  (`thm:spin-network`, Gran-Tensor manuscript)

With the gauge action `(h·g)_e = h_{t(e)}·g_e·h_{s(e)}⁻¹` of
`G^V` on `G^E`:

* `spin_network`:
  (1) the action laws `act 1 = id`, `act (h·k) = act h ∘ act k`
      (so each `U_h` is a permutation of configurations);
  (2) `U_h` is unitary on `ℓ²(G^E)`: the pairing
      `Σ_g conj(f(h·g))·f'(h·g) = Σ_g conj(f g)·f' g`;
  (3) the group-averaging projector
      `(Πf)(g) = |G^V|⁻¹ Σ_h f(h·g)` is idempotent and its
      fixed points are exactly the gauge invariants
      (`Πf = f ⟺ f` invariant) — the orthogonal projection
      onto `L²(G^E)^{G^V}`.

Rendering disclosed: the spin-network orthonormal basis (edge
irreducibles + vertex intertwiners) is the finite Peter–Weyl
refinement of the proved invariant-projection structure; its
separation corollary is the proved
`closed_spin_networks_separate`.
-/

namespace NCG

variable {G V E : Type*} [Group G] [Fintype G] [Fintype V]
  [Fintype E] [DecidableEq V] [DecidableEq E] (t s : E → V)

/-- The gauge action of `G^V` on configurations `G^E`. -/
def gaugeAct (h : V → G) (g : E → G) : E → G :=
  fun e => h (t e) * g e * (h (s e))⁻¹

/-- `thm:spin-network`. -/
theorem spin_network :
    -- (1) action laws
    (∀ g : E → G, gaugeAct t s (1 : V → G) g = g)
    ∧ (∀ (h k : V → G) (g : E → G),
        gaugeAct t s (h * k) g
          = gaugeAct t s h (gaugeAct t s k g))
    -- (2) each gauge transformation is ℓ²-unitary
    ∧ (∀ (h : V → G) (f f' : (E → G) → ℂ),
        ∑ g : E → G, star (f (gaugeAct t s h g))
            * f' (gaugeAct t s h g)
          = ∑ g : E → G, star (f g) * f' g)
    -- (3) the averaging projector and its fixed points
    ∧ (∀ f : (E → G) → ℂ,
        ((∀ h g, f (gaugeAct t s h g) = f g) ↔
          (fun g => (Fintype.card (V → G) : ℂ)⁻¹
            * ∑ h : V → G, f (gaugeAct t s h g)) = f)) := by
  have hact_one : ∀ g : E → G,
      gaugeAct t s (1 : V → G) g = g := by
    intro g
    funext e
    simp [gaugeAct]
  have hact_mul : ∀ (h k : V → G) (g : E → G),
      gaugeAct t s (h * k) g
        = gaugeAct t s h (gaugeAct t s k g) := by
    intro h k g
    funext e
    simp only [gaugeAct, Pi.mul_apply, mul_inv_rev]
    group
  -- the action equivalence for fixed h
  have hequiv : ∀ h : V → G,
      Function.Bijective (gaugeAct t s h) := by
    intro h
    constructor
    · intro g g' hgg
      funext e
      have he := congrFun hgg e
      simp only [gaugeAct] at he
      exact mul_left_cancel (mul_right_cancel he)
    · intro g
      refine ⟨gaugeAct t s h⁻¹ g, ?_⟩
      rw [← hact_mul, mul_inv_cancel, hact_one]
  refine ⟨hact_one, hact_mul, ?_, ?_⟩
  · intro h f f'
    exact Fintype.sum_bijective _ (hequiv h) _ _ fun g => rfl
  · intro f
    constructor
    · intro hinv
      funext g
      rw [show ∑ h : V → G, f (gaugeAct t s h g)
          = ∑ _h : V → G, f g from
        Finset.sum_congr rfl fun h _ => hinv h g]
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀, one_mul]
      exact_mod_cast Fintype.card_ne_zero
    · intro havg h g
      have h1 := congrFun havg (gaugeAct t s h g)
      have h2 := congrFun havg g
      rw [← h1, ← h2]
      congr 1
      rw [show (∑ k : V → G,
            f (gaugeAct t s k (gaugeAct t s h g)))
          = ∑ k : V → G, f (gaugeAct t s (k * h) g) from
        Finset.sum_congr rfl fun k _ => by
          rw [hact_mul]]
      exact Fintype.sum_bijective (· * h)
        (Group.mulRight_bijective h) _ _ fun k => rfl

end NCG
