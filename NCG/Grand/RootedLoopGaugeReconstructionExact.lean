/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Tactic.Group

/-!
# Rooted-loop reconstruction of lattice connections

Parallel transport is defined on actual graph walks. Its gauge covariance is
proved by induction. Chosen root paths turn each edge into a closed loop, and
equality of these loop holonomies is equivalent to equality of the connections
up to a gauge transformation fixing the root. This supplies a concrete
separation mechanism, including noncontractible loops.
-/

namespace NCG.RootedLoopGaugeReconstruction

variable {V K : Type*} [Group K] {Γ : SimpleGraph V}

/-- The connection on oriented edges, transformed at its two endpoints. -/
def gaugeTransform (h : V → K) (U : V → V → K) : V → V → K :=
  fun x y => h y * U x y * (h x)⁻¹

/-- Chronologically ordered edge transport along an actual graph walk. -/
def transport (U : V → V → K) {x y : V} : Γ.Walk x y → K
  | .nil => 1
  | .cons (u := a) (v := b) _ p => transport U p * U a b

@[simp] theorem transport_nil (U : V → V → K) (x : V) :
    transport U (SimpleGraph.Walk.nil : Γ.Walk x x) = 1 := rfl

theorem transport_append (U : V → V → K) {x y z : V}
    (p : Γ.Walk x y) (q : Γ.Walk y z) :
    transport U (p.append q) = transport U q * transport U p := by
  induction p with
  | nil => simp [transport]
  | cons h p ih => simp [transport, ih, mul_assoc]

theorem transport_gaugeTransform (h : V → K) (U : V → V → K)
    {x y : V} (p : Γ.Walk x y) :
    transport (gaugeTransform h U) p = h y * transport U p * (h x)⁻¹ := by
  induction p with
  | nil => simp [transport]
  | cons hxy p ih =>
      simp only [transport, ih, gaugeTransform]
      group

theorem transport_reverse (U : V → V → K)
    (hrev : ∀ x y, Γ.Adj x y → U y x = (U x y)⁻¹)
    {x y : V} (p : Γ.Walk x y) :
    transport U p.reverse = (transport U p)⁻¹ := by
  induction p with
  | nil => simp [transport]
  | @cons x y z hxy p ih =>
      rw [SimpleGraph.Walk.reverse_cons, transport_append]
      simp [transport, ih, hrev x y hxy, mul_inv_rev]

variable (root : V) (paths : ∀ v, Γ.Walk root v)

/-- The root-based holonomy associated with one oriented edge. -/
def rootedEdgeHolonomy (U : V → V → K) (x y : V) : K :=
  (transport U (paths y))⁻¹ * U x y * transport U (paths x)

/-- The expression above really is the transport of a closed graph walk. -/
theorem rootedEdgeHolonomy_eq_loop_transport (U : V → V → K)
    (hrev : ∀ x y, Γ.Adj x y → U y x = (U x y)⁻¹)
    {x y : V} (hxy : Γ.Adj x y) :
    rootedEdgeHolonomy root paths U x y =
      transport U ((paths x).append (.cons hxy (paths y).reverse)) := by
  rw [transport_append]
  simp [transport, transport_reverse U hrev, rootedEdgeHolonomy, mul_assoc]

/-- Rooted holonomies transform only by conjugation at the root. -/
theorem rootedEdgeHolonomy_gaugeTransform
    (h : V → K) (U : V → V → K) (x y : V) :
    rootedEdgeHolonomy root paths (gaugeTransform h U) x y =
      h root * rootedEdgeHolonomy root paths U x y * (h root)⁻¹ := by
  simp only [rootedEdgeHolonomy, transport_gaugeTransform, gaugeTransform]
  group

/-- The exact based-gauge reconstruction theorem. Equality is required only
on graph edges; values of the connection away from edges play no role. -/
theorem rootedEdgeHolonomy_eq_iff_based_gauge
    (hroot : paths root = .nil) (U W : V → V → K) :
    (∀ x y, Γ.Adj x y →
      rootedEdgeHolonomy root paths U x y = rootedEdgeHolonomy root paths W x y) ↔
    ∃ h : V → K, h root = 1 ∧
      ∀ x y, Γ.Adj x y → W x y = gaugeTransform h U x y := by
  constructor
  · intro heq
    let h : V → K := fun v => transport W (paths v) * (transport U (paths v))⁻¹
    refine ⟨h, ?_, ?_⟩
    · simp [h, hroot]
    · intro x y hxy
      have he := congrArg
        (fun a : K => transport W (paths y) * a * (transport W (paths x))⁻¹)
        (heq x y hxy)
      dsimp [rootedEdgeHolonomy] at he
      have hw : transport W (paths y) *
          ((transport W (paths y))⁻¹ * W x y * transport W (paths x)) *
          (transport W (paths x))⁻¹ = W x y := by group
      rw [hw] at he
      rw [← he]
      dsimp [gaugeTransform, h]
      group
  · rintro ⟨h, hh, hedge⟩ x y hxy
    have hp : ∀ {a b : V} (p : Γ.Walk a b),
        transport W p = transport (gaugeTransform h U) p := by
      intro a b p
      induction p with
      | nil => rfl
      | cons hab p ih => simp [transport, ih, hedge _ _ hab]
    calc
      rootedEdgeHolonomy root paths U x y =
          rootedEdgeHolonomy root paths (gaugeTransform h U) x y := by
        rw [rootedEdgeHolonomy_gaugeTransform, hh]
        simp
      _ = rootedEdgeHolonomy root paths W x y := by
        simp only [rootedEdgeHolonomy, hp, hedge x y hxy]

/-- Connectedness supplies a normalized root-path bank; it is not an extra
connectivity or path-existence oracle. -/
theorem exists_root_paths (hconn : Γ.Connected) :
    ∃ paths : ∀ v, Γ.Walk root v, paths root = .nil := by
  classical
  let paths : ∀ v, Γ.Walk root v := fun v =>
    if hv : v = root then hv.symm ▸ .nil else (hconn root v).some
  exact ⟨paths, by simp [paths]⟩

end NCG.RootedLoopGaugeReconstruction
