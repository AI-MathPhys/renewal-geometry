/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Upstream.AffinityCohomology
import NCG.Graph.Cohomology
import NCG.Graph.RecordOrientation

/-!
# Independence of the affinity and orientation classes

Covers `thm:independence` from `manuscripts/renewal_emergence/renewal_emergence.tex`: the real
affinity class `[A] ∈ H¹(G;ℝ)` and the determinant orientation class
`[χ] ∈ H¹(G;ℤ/2)` are logically independent — on every graph with a
cycle (a closed walk traversing some edge exactly once) there are
resolved models realizing each of the four possibilities
`([A]=0 or ≠0) × ([χ]=0 or ≠0)`.

A resolved model is presented by its **positive capacities**
`w : E → ℝ` (whose logarithms are the affinity cochain) and its
**invertible record transports** `L : E → GL(1,ℝ)` (whose determinant
signs are the orientation cochain `recSign L`).  The four models are:
trivial capacities/transports for the vanishing classes, and a single
marked edge `e₀` of the cycle carrying capacity `exp 1` (affinity `1`)
or transport `−1` (orientation flip) for the nonvanishing ones.
Nontriviality is detected by the cycle: the affinity of the closed
walk is `±1 ≠ 0` and the `ℤ/2` holonomy is `1 ≠ 0`, while coboundaries
have vanishing cycle affinity/holonomy.

Consequently detailed balance (`[A] = 0`) neither implies nor is
implied by orientability of the record local system (`[χ] = 0`)
(`detailed_balance_indep_orientability`).
-/

namespace NCG.Multigraph

variable {G : Multigraph} [DecidableEq G.E]

/-- The number of forward traversals of the edge `e₀` by a walk. -/
def Walk.fwdCount (e₀ : G.E) : ∀ {u v : G.V}, G.Walk u v → ℕ
  | _, _, .nil _ => 0
  | _, _, .fwd e p => (if e = e₀ then 1 else 0) + p.fwdCount e₀
  | _, _, .bwd _ p => p.fwdCount e₀

/-- The number of backward traversals of the edge `e₀` by a walk. -/
def Walk.bwdCount (e₀ : G.E) : ∀ {u v : G.V}, G.Walk u v → ℕ
  | _, _, .nil _ => 0
  | _, _, .fwd _ p => p.bwdCount e₀
  | _, _, .bwd e p => (if e = e₀ then 1 else 0) + p.bwdCount e₀

/-- The total number of traversals of the edge `e₀` by a walk. -/
def Walk.usesCount (e₀ : G.E) {u v : G.V} (p : G.Walk u v) : ℕ :=
  p.fwdCount e₀ + p.bwdCount e₀

/-- The affinity of the indicator cochain of `e₀` counts signed
traversals of `e₀`. -/
theorem Walk.affinity_indicator (e₀ : G.E) :
    ∀ {u v : G.V} (p : G.Walk u v),
      p.affinity (fun e => if e = e₀ then (1 : ℝ) else 0)
        = (p.fwdCount e₀ : ℝ) - (p.bwdCount e₀ : ℝ) := by
  intro u v p
  induction p with
  | nil w => simp [fwdCount, bwdCount]
  | fwd e p ih =>
    simp only [affinity_fwd, fwdCount, bwdCount, ih]
    split <;> push_cast <;> ring
  | bwd e p ih =>
    simp only [affinity_bwd, fwdCount, bwdCount, ih]
    split <;> push_cast <;> ring

/-- The `ℤ/2` holonomy of the indicator cochain of `e₀` counts
traversals of `e₀` mod 2. -/
theorem Walk.holonomy_indicator (e₀ : G.E) :
    ∀ {u v : G.V} (p : G.Walk u v),
      p.holonomy (fun e => if e = e₀ then (1 : ZMod 2) else 0)
        = ((p.usesCount e₀ : ℕ) : ZMod 2) := by
  intro u v p
  induction p with
  | nil w => simp [usesCount, fwdCount, bwdCount]
  | fwd e p ih =>
    simp only [holonomy_fwd, usesCount, fwdCount, bwdCount, ih]
    split <;> push_cast <;> ring
  | bwd e p ih =>
    simp only [holonomy_bwd, usesCount, fwdCount, bwdCount, ih]
    split <;> push_cast <;> ring

/-- The real class of the indicator of an edge traversed exactly once
by a closed walk is nonzero. -/
theorem H1R.mk_indicator_ne_zero {v : G.V} {e₀ : G.E}
    (p : G.Walk v v) (hone : p.usesCount e₀ = 1) :
    H1R.mk G (fun e => if e = e₀ then (1 : ℝ) else 0) ≠ 0 := by
  intro h0
  have h1 : p.affinity (fun e => if e = e₀ then (1 : ℝ) else 0)
      = p.affinity (0 : G.E → ℝ) :=
    Walk.affinity_congr (by rw [h0, map_zero]) p
  rw [Walk.affinity_zero, Walk.affinity_indicator] at h1
  have h2 : p.fwdCount e₀ + p.bwdCount e₀ = 1 := hone
  have h3 : (p.fwdCount e₀ = 1 ∧ p.bwdCount e₀ = 0)
      ∨ (p.fwdCount e₀ = 0 ∧ p.bwdCount e₀ = 1) := by omega
  rcases h3 with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> rw [ha, hb] at h1 <;>
    norm_num at h1

/-- The `ℤ/2` class of the indicator of an edge traversed exactly
once by a closed walk is nonzero. -/
theorem H1.mk_indicator_ne_zero {v : G.V} {e₀ : G.E}
    (p : G.Walk v v) (hone : p.usesCount e₀ = 1) :
    H1.mk G (fun e => if e = e₀ then (1 : ZMod 2) else 0) ≠ 0 := by
  intro h0
  have hcob := H1.mk_eq_zero_iff.mp h0
  have h1 := holonomy_eq_zero_of_isCoboundary hcob p
  rw [Walk.holonomy_indicator, hone] at h1
  norm_num at h1

/-- **Theorem `thm:independence`**: on every graph with a cycle
(a closed walk traversing some edge `e₀` exactly once), resolved
models — positive capacities `w` with affinity cochain `log w`, and
invertible rank-one record transports `L` with orientation cochain
`recSign L` — realize all four combinations of
`[A] = 0 / ≠ 0` and `[χ] = 0 / ≠ 0`. -/
theorem independence_of_classes {v : G.V} {e₀ : G.E}
    (p : G.Walk v v) (hone : p.usesCount e₀ = 1) :
    ((∃ (w : G.E → ℝ) (L : G.E → Matrix (Fin 1) (Fin 1) ℝ),
        (∀ e, 0 < w e) ∧ (∀ e, (L e).det ≠ 0)
          ∧ H1R.mk G (fun e => Real.log (w e)) = 0
          ∧ H1.mk G (recSign L) = 0)
      ∧ (∃ (w : G.E → ℝ) (L : G.E → Matrix (Fin 1) (Fin 1) ℝ),
        (∀ e, 0 < w e) ∧ (∀ e, (L e).det ≠ 0)
          ∧ H1R.mk G (fun e => Real.log (w e)) ≠ 0
          ∧ H1.mk G (recSign L) = 0)
      ∧ (∃ (w : G.E → ℝ) (L : G.E → Matrix (Fin 1) (Fin 1) ℝ),
        (∀ e, 0 < w e) ∧ (∀ e, (L e).det ≠ 0)
          ∧ H1R.mk G (fun e => Real.log (w e)) = 0
          ∧ H1.mk G (recSign L) ≠ 0)
      ∧ (∃ (w : G.E → ℝ) (L : G.E → Matrix (Fin 1) (Fin 1) ℝ),
        (∀ e, 0 < w e) ∧ (∀ e, (L e).det ≠ 0)
          ∧ H1R.mk G (fun e => Real.log (w e)) ≠ 0
          ∧ H1.mk G (recSign L) ≠ 0)) := by
  classical
  -- the four building blocks
  set wtriv : G.E → ℝ := fun _ => 1 with hwtriv
  set wnon : G.E → ℝ := fun e => if e = e₀ then Real.exp 1 else 1
    with hwnon
  set Ltriv : G.E → Matrix (Fin 1) (Fin 1) ℝ := fun _ => 1 with hLtriv
  set Lnon : G.E → Matrix (Fin 1) (Fin 1) ℝ :=
    fun e => if e = e₀ then (-1 : Matrix (Fin 1) (Fin 1) ℝ) else 1
    with hLnon
  have hwtriv_pos : ∀ e, 0 < wtriv e := fun _ => one_pos
  have hwnon_pos : ∀ e, 0 < wnon e := by
    intro e
    rw [hwnon]
    dsimp only
    split
    · exact Real.exp_pos 1
    · exact one_pos
  have hdet_one : ((1 : Matrix (Fin 1) (Fin 1) ℝ)).det = 1 :=
    Matrix.det_one
  have hdet_neg : ((-1 : Matrix (Fin 1) (Fin 1) ℝ)).det = -1 := by
    rw [Matrix.det_fin_one]
    simp
  have hLtriv_det : ∀ e, (Ltriv e).det ≠ 0 := by
    intro e
    rw [hLtriv]
    dsimp only
    rw [hdet_one]
    exact one_ne_zero
  have hLnon_det : ∀ e, (Lnon e).det ≠ 0 := by
    intro e
    rw [hLnon]
    dsimp only
    split
    · rw [hdet_neg]; norm_num
    · rw [hdet_one]; exact one_ne_zero
  -- the associated cochains
  have hlog_triv : (fun e => Real.log (wtriv e)) = (0 : G.E → ℝ) := by
    funext e
    rw [hwtriv]
    dsimp only
    rw [Real.log_one]
    rfl
  have hlog_non : (fun e => Real.log (wnon e))
      = fun e => if e = e₀ then (1 : ℝ) else 0 := by
    funext e
    rw [hwnon]
    dsimp only
    split
    · rw [Real.log_exp]
    · rw [Real.log_one]
  have hrec_triv : recSign Ltriv = (0 : G.E → ZMod 2) := by
    funext e
    change orSign (Ltriv e).det = 0
    rw [hLtriv]
    dsimp only
    rw [hdet_one, orSign_one]
  have hrec_non : recSign Lnon
      = fun e => if e = e₀ then (1 : ZMod 2) else 0 := by
    funext e
    change orSign (Lnon e).det = _
    rw [hLnon]
    dsimp only
    split
    · rw [hdet_neg, orSign]
      rw [if_neg (by norm_num)]
    · rw [hdet_one, orSign_one]
  -- class computations
  have hAtriv : H1R.mk G (fun e => Real.log (wtriv e)) = 0 := by
    rw [hlog_triv, map_zero]
  have hAnon : H1R.mk G (fun e => Real.log (wnon e)) ≠ 0 := by
    rw [hlog_non]
    exact H1R.mk_indicator_ne_zero p hone
  have hXtriv : H1.mk G (recSign Ltriv) = 0 := by
    rw [hrec_triv, map_zero]
  have hXnon : H1.mk G (recSign Lnon) ≠ 0 := by
    rw [hrec_non]
    exact H1.mk_indicator_ne_zero p hone
  exact ⟨⟨wtriv, Ltriv, hwtriv_pos, hLtriv_det, hAtriv, hXtriv⟩,
    ⟨wnon, Ltriv, hwnon_pos, hLtriv_det, hAnon, hXtriv⟩,
    ⟨wtriv, Lnon, hwtriv_pos, hLnon_det, hAtriv, hXnon⟩,
    ⟨wnon, Lnon, hwnon_pos, hLnon_det, hAnon, hXnon⟩⟩

/-- **Theorem `thm:independence` (consequence)**: detailed balance
(`[A] = 0`) neither implies nor is implied by orientability of the
record local system (`[χ] = 0`). -/
theorem detailed_balance_indep_orientability {v : G.V} {e₀ : G.E}
    (p : G.Walk v v) (hone : p.usesCount e₀ = 1) :
    (∃ (w : G.E → ℝ) (L : G.E → Matrix (Fin 1) (Fin 1) ℝ),
      (∀ e, 0 < w e) ∧ (∀ e, (L e).det ≠ 0)
        ∧ H1R.mk G (fun e => Real.log (w e)) = 0
        ∧ H1.mk G (recSign L) ≠ 0)
    ∧ (∃ (w : G.E → ℝ) (L : G.E → Matrix (Fin 1) (Fin 1) ℝ),
      (∀ e, 0 < w e) ∧ (∀ e, (L e).det ≠ 0)
        ∧ H1R.mk G (fun e => Real.log (w e)) ≠ 0
        ∧ H1.mk G (recSign L) = 0) :=
  ⟨(independence_of_classes p hone).2.2.1,
    (independence_of_classes p hone).2.1⟩

end NCG.Multigraph
