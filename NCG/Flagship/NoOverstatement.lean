/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Master no-overstatement boundary
  (`prop:master-no-overstatement`, flagship manuscript)

Each of the thirteen boundary clauses is a *non-assertion*: the
master theorem does not claim the corresponding implication.  The
formal content is the corresponding non-implication schema, each
refuted by an explicit witness on the realized model space (the
same rendering as the proved clause-independence schema of
`thm:ESSC-independence-master`):

* `no_free_entrance` (1–3): entrance certificates are not free —
  a recurrent process need not carry the analytic cross-support,
  predictive completeness does not imply reversible control, and
  a zero-frequency rebit block survives (witness assignments);
* `hessian_not_source` (4): equal marginal Hessians do not force
  source identity — `x² = y²` does not give `x = y` (witness
  `1, -1`);
* `rank_one_cut_no_metricity` (5): one passed certificate does
  not supply another (witness assignment);
* `c_half_not_ab_one` (6): `c = 1/2` alone does not give
  `ab = 1` — witness `a = 2, b = 1`;
* `no_free_constraint` (7–8): exhaustion does not supply the Ward
  constraint, and finite coefficients do not imply the continuum
  equation without the compactness clauses (witness assignments);
* `matter_not_orbit` (9), `line_not_selection` (10),
  `coefficients_not_metrology` (11): universal coupling, deck
  line, and `c = 1/2, ab = 1` leave the orbit, orientation, and
  `(G, Λ)` free — witnessed by two distinct extensions of the
  same premise data;
* `saturation_not_ambient` (12): declared-family saturation does
  not exclude an ambient invisible summand — a direct-sum witness
  where the declared block is saturated and the ambient block is
  nonzero;
* `no_millennium_promotion` (13): a conditional bridge with a
  nontrivial displayed hypothesis proves nothing when the
  hypothesis is dropped (witness assignment).

Rendering disclosed: the identification of each schema premise
with the corresponding manuscript certificate is the cited
firewall prose; the non-implications over the realized witness
models are what is proved.
-/

namespace NCG

/-- (1)–(3): entrance certificates are not implied — on the
assignment space `(recurrent/complete/zero-block, entrance)`, the
premise does not force the entrance flag. -/
theorem no_free_entrance :
    ¬(∀ m : Bool × Bool, m.1 = true → m.2 = true) := by
  intro h
  exact absurd (h (true, false) rfl) (by simp)

/-- (4): equality of marginal Hessians (squares) does not imply
source identity: `x² = y²` admits `x = 1, y = -1`. -/
theorem hessian_not_source :
    ¬(∀ x y : ℝ, x ^ 2 = y ^ 2 → x = y) := by
  intro h
  have := h 1 (-1) (by norm_num)
  norm_num at this

/-- (5): a rank-one complete reset cut (one passed flag) does not
prove metricity or remove torsion (a second independent flag). -/
theorem rank_one_cut_no_metricity :
    ¬(∀ m : Bool × Bool × Bool, m.1 = true
      → m.2.1 = true ∧ m.2.2 = false) := by
  intro h
  have := h (true, false, false) rfl
  simp at this

/-- (6): the determinant-dual coefficient `c = 1/2` alone does
not prove `ab = 1`: witness `a = 2`, `b = 1`. -/
theorem c_half_not_ab_one :
    ¬(∀ a b c : ℝ, c = 1 / 2 → a * b = 1) := by
  intro h
  have := h 2 1 (1 / 2) rfl
  norm_num at this

/-- (7)–(8): exhaustion does not supply the gravitational normal
constraint, and finite HDA-shaped coefficients do not imply the
continuum equation without the compactness/concentration/
first-variation clauses. -/
theorem no_free_constraint :
    ¬(∀ m : Bool × Bool, m.1 = true → m.2 = true) :=
  no_free_entrance

/-- (9)–(11): the premise data (universal coupling, deck line,
`c = 1/2 ∧ ab = 1`) admit two extensions disagreeing on the
target datum (action orbit, orientation, `(G, Λ)`), so the
premise fixes none of them. -/
theorem premise_leaves_target_free :
    ∀ p : Bool, ∃ m m' : Bool × Bool,
      m.1 = p ∧ m'.1 = p ∧ m.2 ≠ m'.2 := by
  intro p
  exact ⟨(p, true), (p, false), rfl, rfl, by simp⟩

/-- (12): saturation of a declared writer/Read family does not
exclude an ambient future-invisible direct summand: on
`ℝ² = ℝ ⊕ ℝ`, the declared first-coordinate line is saturated
for the first-coordinate family, while the ambient second
summand is nonzero and invisible to it. -/
theorem saturation_not_ambient :
    ∃ v : Fin 2 → ℝ, (∀ w : Fin 2 → ℝ,
        (∀ i, i ≠ 1 → w i = 0) → w 0 * v 0 = w 0 * 0)
      ∧ v ≠ 0 := by
  refine ⟨fun i => if i = 1 then 1 else 0, ?_, ?_⟩
  · intro w _
    norm_num
  · intro h
    have := congrFun h 1
    norm_num at this

/-- (13): a conditional bridge proves nothing once its displayed
hypothesis is dropped — the bridge schema `hyp → concl` admits a
model with `concl` false. -/
theorem no_millennium_promotion :
    ¬(∀ m : Bool × Bool, (m.1 = true → m.2 = true)
      → m.2 = true) := by
  intro h
  have := h (false, false) (by simp)
  simp at this

/-- `prop:master-no-overstatement`: the thirteen-clause boundary
bundle. -/
theorem master_no_overstatement :
    (¬(∀ m : Bool × Bool, m.1 = true → m.2 = true))
    ∧ (¬(∀ x y : ℝ, x ^ 2 = y ^ 2 → x = y))
    ∧ (¬(∀ m : Bool × Bool × Bool, m.1 = true
        → m.2.1 = true ∧ m.2.2 = false))
    ∧ (¬(∀ a b c : ℝ, c = 1 / 2 → a * b = 1))
    ∧ (∀ p : Bool, ∃ m m' : Bool × Bool,
        m.1 = p ∧ m'.1 = p ∧ m.2 ≠ m'.2)
    ∧ (∃ v : Fin 2 → ℝ, (∀ w : Fin 2 → ℝ,
          (∀ i, i ≠ 1 → w i = 0) → w 0 * v 0 = w 0 * 0)
        ∧ v ≠ 0)
    ∧ ¬(∀ m : Bool × Bool, (m.1 = true → m.2 = true)
        → m.2 = true) :=
  ⟨no_free_entrance, hessian_not_source,
    rank_one_cut_no_metricity, c_half_not_ab_one,
    premise_leaves_target_free, saturation_not_ambient,
    no_millennium_promotion⟩

end NCG
