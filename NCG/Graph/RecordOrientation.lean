/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Graph.SignCocycle

/-!
# The stable-record determinant orientation class

Covers `prop:record-determinant-orientation` from
`manuscripts/lorentzian_emergence/lorentzian_emergence.tex`: assigning to every edge of a
predictive graph
an invertible record transport `L_e` on a constant-rank real record
space defines the determinant-parity sign cochain
`χ_rec(e) = sgn det L_e` (written additively in `ℤ/2`, so the
manuscript's multiplicative `±1` sign is `(−1)^{χ_rec}`).  We prove:

* a change of local record orientation — conjugating every transport
  by invertible basis changes `C_x` — transforms `χ_rec` by exactly
  the vertex coboundary of the orientation signs `sgn det C_x`
  (`recSign_basisChange`), so the class
  `[χ_rec] = w₁(det 𝓡) ∈ H¹(G, ℤ/2)` is well defined;
* the product of `χ_rec` around every loop is invariant under such
  orientation changes (`recSign_holonomy_basisChange_loop`);
* the loop holonomy of `χ_rec` is the orientation character of the
  composed record transport (`holonomy_recSign`): a walk preserves
  the determinant orientation iff its `χ_rec`-holonomy vanishes, so
  the principal double cover classified by `[χ_rec]` is exactly the
  orientation cover of the stable-record determinant line
  (Theorem `thm:cover` applied to this class).
-/

namespace NCG

/-- The `ℤ/2` orientation sign of a nonzero real number:
`0` for positive, `1` for negative (the additive avatar of
`sgn`). -/
noncomputable def orSign (x : ℝ) : ZMod 2 := if 0 < x then 0 else 1

@[simp]
theorem orSign_one : orSign 1 = 0 := if_pos one_pos

theorem orSign_mul {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    orSign (x * y) = orSign x + orSign y := by
  rcases lt_or_gt_of_ne hx with hx' | hx' <;> rcases lt_or_gt_of_ne hy with hy' | hy'
  · rw [orSign, orSign, orSign, if_pos (mul_pos_of_neg_of_neg hx' hy'),
      if_neg (not_lt.mpr hx'.le), if_neg (not_lt.mpr hy'.le)]
    decide
  · rw [orSign, orSign, orSign,
      if_neg (not_lt.mpr (mul_neg_of_neg_of_pos hx' hy').le),
      if_neg (not_lt.mpr hx'.le), if_pos hy']
    decide
  · rw [orSign, orSign, orSign,
      if_neg (not_lt.mpr (mul_neg_of_pos_of_neg hx' hy').le),
      if_pos hx', if_neg (not_lt.mpr hy'.le)]
    decide
  · rw [orSign, orSign, orSign, if_pos (mul_pos hx' hy'),
      if_pos hx', if_pos hy']
    decide

theorem orSign_inv {x : ℝ} (hx : x ≠ 0) : orSign x⁻¹ = orSign x := by
  rcases lt_or_gt_of_ne hx with h | h
  · rw [orSign, orSign, if_neg (not_lt.mpr (inv_nonpos.mpr h.le)),
      if_neg (not_lt.mpr h.le)]
  · rw [orSign, orSign, if_pos (inv_pos.mpr h), if_pos h]

namespace Multigraph

variable {G : Multigraph} {r : ℕ}

/-- **The determinant-parity cochain** of a record transport
assignment: `χ_rec(e) = sgn det L_e`, written additively in
`ℤ/2`. -/
noncomputable def recSign (L : G.E → Matrix (Fin r) (Fin r) ℝ) : G.E → ZMod 2 :=
  fun e => orSign (L e).det

/-- **Proposition `prop:record-determinant-orientation`
(coboundary action)**: changing the local record orientations by
invertible basis changes `C_x` transforms the determinant-parity
cochain by exactly the vertex coboundary of the orientation signs
`g(x) = sgn det C_x`. -/
theorem recSign_basisChange (L : G.E → Matrix (Fin r) (Fin r) ℝ)
    (C : G.V → Matrix (Fin r) (Fin r) ℝ)
    (hL : ∀ e, (L e).det ≠ 0) (hC : ∀ v, (C v).det ≠ 0) :
    recSign (fun e => (C (G.tgt e))⁻¹ * L e * C (G.src e))
      = gaugeAct (fun v => orSign (C v).det) (recSign L) := by
  funext e
  change orSign ((C (G.tgt e))⁻¹ * L e * C (G.src e)).det
      = orSign (L e).det + orSign (C (G.src e)).det
        + orSign (C (G.tgt e)).det
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
  rw [orSign_mul (mul_ne_zero (inv_ne_zero (hC (G.tgt e))) (hL e))
      (hC (G.src e)),
    orSign_mul (inv_ne_zero (hC (G.tgt e))) (hL e),
    orSign_inv (hC (G.tgt e))]
  ring

/-- **Proposition `prop:record-determinant-orientation`
(loop invariance)**: the determinant-parity holonomy around every
closed walk is invariant under changes of local record orientation —
the class `[χ_rec] = w₁(det 𝓡)` is well defined in
`H¹(G, ℤ/2)`. -/
theorem recSign_holonomy_basisChange_loop
    (L : G.E → Matrix (Fin r) (Fin r) ℝ)
    (C : G.V → Matrix (Fin r) (Fin r) ℝ)
    (hL : ∀ e, (L e).det ≠ 0) (hC : ∀ v, (C v).det ≠ 0)
    {v : G.V} (p : G.Walk v v) :
    p.holonomy (recSign fun e => (C (G.tgt e))⁻¹ * L e * C (G.src e))
      = p.holonomy (recSign L) := by
  rw [recSign_basisChange L C hL hC]
  exact Walk.holonomy_gauge_loop _ _ p

/-- The composed record transport along a walk (backward edges
contribute the inverse transport). -/
noncomputable def walkTransport (L : G.E → Matrix (Fin r) (Fin r) ℝ) :
    ∀ {u v : G.V}, G.Walk u v → Matrix (Fin r) (Fin r) ℝ
  | _, _, .nil _ => 1
  | _, _, .fwd e p => walkTransport L p * L e
  | _, _, .bwd e p => walkTransport L p * (L e)⁻¹

theorem walkTransport_det_ne_zero
    {L : G.E → Matrix (Fin r) (Fin r) ℝ} (hL : ∀ e, (L e).det ≠ 0) :
    ∀ {u v : G.V} (p : G.Walk u v), (walkTransport L p).det ≠ 0 := by
  intro u v p
  induction p with
  | nil w =>
    change (1 : Matrix (Fin r) (Fin r) ℝ).det ≠ 0
    rw [Matrix.det_one]
    exact one_ne_zero
  | fwd e p ih =>
    change (walkTransport L p * L e).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero ih (hL e)
  | bwd e p ih =>
    change (walkTransport L p * (L e)⁻¹).det ≠ 0
    rw [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
    exact mul_ne_zero ih (inv_ne_zero (hL e))

/-- **Proposition `prop:record-determinant-orientation`
(monodromy identification)**: the `χ_rec`-holonomy of a walk is the
orientation character of its composed record transport — it vanishes
exactly when the transport preserves the determinant orientation.
The principal cover of `[χ_rec]` is therefore the orientation cover
of the stable-record determinant line. -/
theorem holonomy_recSign {L : G.E → Matrix (Fin r) (Fin r) ℝ}
    (hL : ∀ e, (L e).det ≠ 0) :
    ∀ {u v : G.V} (p : G.Walk u v),
      p.holonomy (recSign L) = orSign (walkTransport L p).det := by
  intro u v p
  induction p with
  | nil w =>
    change (0 : ZMod 2) = orSign (1 : Matrix (Fin r) (Fin r) ℝ).det
    rw [Matrix.det_one, orSign_one]
  | fwd e p ih =>
    change recSign L e + p.holonomy (recSign L)
        = orSign (walkTransport L p * L e).det
    rw [Matrix.det_mul,
      orSign_mul (walkTransport_det_ne_zero hL p) (hL e), ih]
    show recSign L e + orSign (walkTransport L p).det
        = orSign (walkTransport L p).det + orSign (L e).det
    rw [recSign]
    ring
  | bwd e p ih =>
    change recSign L e + p.holonomy (recSign L)
        = orSign (walkTransport L p * (L e)⁻¹).det
    rw [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv,
      orSign_mul (walkTransport_det_ne_zero hL p)
        (inv_ne_zero (hL e)), ih, orSign_inv (hL e)]
    show recSign L e + orSign (walkTransport L p).det
        = orSign (walkTransport L p).det + orSign (L e).det
    rw [recSign]
    ring

/-- **Deterministic record permutations carry the permutation
parity** (`thm:noisy-record-orientation` (iv)): when the record
transport is the permutation matrix of `σ`, the determinant-parity
cochain evaluates to the ordinary parity of `σ`. -/
theorem recSign_permMatrix {r : ℕ} (σ : Equiv.Perm (Fin r)) :
    orSign ((σ.permMatrix ℝ).det)
      = (if Equiv.Perm.sign σ = 1 then (0 : ZMod 2) else 1) := by
  rw [Matrix.det_permutation]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
  · rw [h]
    simp [orSign]
  · rw [h]
    norm_num [orSign]

end Multigraph

end NCG
