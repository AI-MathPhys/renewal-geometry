/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
/-!
# Lattice walks, holonomy, and gauge covariance

Infrastructure for the gauge-covariance clause of `thm:finite-action-identities`
(spacetime–gauge duality paper).  On an oriented graph `(V, E, src, tgt)` with link variables
`U : E → G` in a group `G`:

* `LatticeWalk src tgt a b`: walks from `a` to `b` as sequences of oriented steps `(e, ±)`;
* `LatticeWalk.holonomy U w`: the ordered product of the links `U_e^{±1}` along `w`
  (later steps act on the left);
* `gaugeLinks src tgt g U`: the gauge transform `U_e ↦ g_{t(e)} U_e g_{s(e)}⁻¹`;
* `LatticeWalk.holonomy_gaugeLinks`: the holonomy of a walk from `a` to `b` transforms as
  `hol ↦ g_b · hol · g_a⁻¹`; for a closed walk (a plaquette boundary) it **conjugates** by
  the gauge element at the base point (`holonomy_gaugeLinks_closed`), so every class function
  of the plaquette holonomy is gauge invariant.
-/

namespace RenewalGeometry

universe u v

section Walks

variable {V : Type u} {E : Type v}

/-- The tail (start) vertex of the oriented step `(e, b)`: `src e` for the forward orientation
`b = true`, `tgt e` for the reversed one. -/
def stepTail (src tgt : E → V) (s : E × Bool) : V := cond s.2 (src s.1) (tgt s.1)

/-- The head (end) vertex of the oriented step `(e, b)`. -/
def stepHead (src tgt : E → V) (s : E × Bool) : V := cond s.2 (tgt s.1) (src s.1)

/-- Walks in the oriented graph `(V, E, src, tgt)` from `a` to `b`: the empty walk, or a
first oriented step `s` followed by a walk from the head of `s`. -/
inductive LatticeWalk (src tgt : E → V) : V → V → Type (max u v)
  | nil (v : V) : LatticeWalk src tgt v v
  | cons {b : V} (s : E × Bool) (w : LatticeWalk src tgt (stepHead src tgt s) b) :
      LatticeWalk src tgt (stepTail src tgt s) b

variable {G : Type*} [Group G]

/-- The link transported along one oriented step: `U_e` forward, `U_e⁻¹` backward. -/
def stepLink (U : E → G) (s : E × Bool) : G := cond s.2 (U s.1) (U s.1)⁻¹

/-- The holonomy (ordered product of links) along a walk; later steps act on the left. -/
def LatticeWalk.holonomy {src tgt : E → V} (U : E → G) :
    ∀ {a b : V}, LatticeWalk src tgt a b → G
  | _, _, .nil _ => 1
  | _, _, .cons s w => holonomy U w * stepLink U s

@[simp] theorem LatticeWalk.holonomy_nil {src tgt : E → V} (U : E → G) (v : V) :
    (LatticeWalk.nil (src := src) (tgt := tgt) v).holonomy U = 1 := rfl

@[simp] theorem LatticeWalk.holonomy_cons {src tgt : E → V} (U : E → G) {b : V}
    (s : E × Bool) (w : LatticeWalk src tgt (stepHead src tgt s) b) :
    (LatticeWalk.cons s w).holonomy U = w.holonomy U * stepLink U s := rfl

/-- The gauge transform of the link variables, `U_e ↦ g_{t(e)} U_e g_{s(e)}⁻¹`. -/
def gaugeLinks (src tgt : E → V) (g : V → G) (U : E → G) : E → G :=
  fun e => g (tgt e) * U e * (g (src e))⁻¹

theorem gaugeLinks_apply (src tgt : E → V) (g : V → G) (U : E → G) (e : E) :
    gaugeLinks src tgt g U e = g (tgt e) * U e * (g (src e))⁻¹ := rfl

/-- Gauge transforms compose: `(g h) · U = g · (h · U)`. -/
theorem gaugeLinks_mul (src tgt : E → V) (g h : V → G) (U : E → G) :
    gaugeLinks src tgt (g * h) U = gaugeLinks src tgt g (gaugeLinks src tgt h U) := by
  funext e
  simp [gaugeLinks, mul_inv_rev, mul_assoc]

theorem gaugeLinks_one (src tgt : E → V) (U : E → G) : gaugeLinks src tgt 1 U = U := by
  funext e
  simp [gaugeLinks]

/-- One oriented step transforms as `U_s ↦ g_{head s} U_s g_{tail s}⁻¹`. -/
theorem stepLink_gaugeLinks (src tgt : E → V) (g : V → G) (U : E → G) (s : E × Bool) :
    stepLink (gaugeLinks src tgt g U) s =
      g (stepHead src tgt s) * stepLink U s * (g (stepTail src tgt s))⁻¹ := by
  rcases s with ⟨e, b⟩
  cases b <;> simp [stepLink, gaugeLinks, stepHead, stepTail, mul_inv_rev, mul_assoc]

/-- **Gauge covariance of the holonomy**: along a walk from `a` to `b`,
`hol(g · U) = g_b · hol(U) · g_a⁻¹`. -/
theorem LatticeWalk.holonomy_gaugeLinks {src tgt : E → V} (g : V → G) (U : E → G) {a b : V}
    (w : LatticeWalk src tgt a b) :
    w.holonomy (gaugeLinks src tgt g U) = g b * w.holonomy U * (g a)⁻¹ := by
  induction w with
  | nil v => simp
  | cons s w ih =>
    rw [LatticeWalk.holonomy_cons, LatticeWalk.holonomy_cons, ih, stepLink_gaugeLinks]
    simp [mul_assoc]

/-- **Plaquette holonomy conjugates**: the holonomy of a closed walk based at `v` transforms
by conjugation with `g_v`. -/
theorem LatticeWalk.holonomy_gaugeLinks_closed {src tgt : E → V} (g : V → G) (U : E → G)
    {v : V} (w : LatticeWalk src tgt v v) :
    w.holonomy (gaugeLinks src tgt g U) = g v * w.holonomy U * (g v)⁻¹ :=
  w.holonomy_gaugeLinks g U

/-- Every class function of the holonomy of a closed walk is gauge invariant. -/
theorem LatticeWalk.classFunction_holonomy_gaugeLinks {src tgt : E → V} {X : Type*}
    (f : G → X) (hf : ∀ g P, f (g * P * g⁻¹) = f P) (g : V → G) (U : E → G) {v : V}
    (w : LatticeWalk src tgt v v) :
    f (w.holonomy (gaugeLinks src tgt g U)) = f (w.holonomy U) := by
  rw [w.holonomy_gaugeLinks_closed g U, hf]

end Walks

end RenewalGeometry
