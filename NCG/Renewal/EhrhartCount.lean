/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Renewal.CommutingGrowth

/-!
# Exact Ehrhart count for the free commuting monoid

**Corollary `cor:ehrhart-free`**: for the free commuting monoid on `c`
generators the predictive counting function is the exact binomial
(stars and bars)

`N_c(R) = #{n ∈ ℕ^c : Σ nᵢ ≤ R} = C(R + c, c)`,

a polynomial in `R` of degree `c` with leading coefficient `1/c!` —
the Ehrhart polynomial of the standard simplex.  Proof: peel the first
coordinate (`NCG.shellSigmaEquiv`), apply the inductive hypothesis to
each fibre, and close with the hockey-stick identity
`∑_{m ∈ [k, n]} C(m, k) = C(n + 1, k + 1)`.

The shell increment `N(R+1) − N(R) = C(R + c, c − 1)`
(`NCG.latticeShellCard_shell`) is the exact degree multiplicity used by
the free case of the spectral action (Proposition
`prop:spectral-action`).
-/

namespace NCG

/-- The lattice shell `{n ∈ ℕ^c : Σ nᵢ ≤ R}` is a finite type — each
coordinate is bounded by `R`. -/
instance shellFinite (c R : ℕ) :
    Finite {n : Fin c → ℕ // ∑ i, n i ≤ R} := by
  have hinj : Function.Injective
      (fun n : {n : Fin c → ℕ // ∑ i, n i ≤ R} =>
        (fun i => (⟨n.1 i, by
          have hle : n.1 i ≤ ∑ j, n.1 j :=
            Finset.single_le_sum (fun j _ => Nat.zero_le _)
              (Finset.mem_univ i)
          have := n.2
          omega⟩ : Fin (R + 1))) : _ → (Fin c → Fin (R + 1))) := by
    intro a b hab
    apply Subtype.ext
    funext i
    exact congrArg Fin.val (congrFun hab i)
  exact Finite.of_injective _ hinj

/-- Peeling the first coordinate: a degree-`≤ R` exponent vector on
`c + 1` coordinates is a first entry `a ≤ R` together with a
degree-`≤ R − a` vector on the remaining `c` coordinates. -/
def shellSigmaEquiv (c R : ℕ) :
    {n : Fin (c + 1) → ℕ // ∑ i, n i ≤ R}
      ≃ (a : Fin (R + 1)) × {n : Fin c → ℕ // ∑ i, n i ≤ R - a.val} where
  toFun f :=
    ⟨⟨f.1 0, by
        have h0 : f.1 0 ≤ ∑ i, f.1 i :=
          Finset.single_le_sum (fun j _ => Nat.zero_le _)
            (Finset.mem_univ 0)
        have := f.2
        omega⟩,
      ⟨fun i => f.1 i.succ, by
        change ∑ i : Fin c, f.1 i.succ ≤ R - f.1 0
        have h := f.2
        rw [Fin.sum_univ_succ] at h
        omega⟩⟩
  invFun p :=
    ⟨Fin.cons p.1.val p.2.1, by
      rw [Fin.sum_cons]
      have h1 := p.2.2
      have h2 : p.1.val < R + 1 := p.1.2
      omega⟩
  left_inv f := by
    apply Subtype.ext
    exact Fin.cons_self_tail f.1
  right_inv p := by
    rcases p with ⟨a, g⟩
    refine Sigma.ext (Fin.ext ?_) ?_
    · change (Fin.cons a.val g.1 : Fin (c + 1) → ℕ) 0 = a.val
      exact Fin.cons_zero _ _
    · rw [Subtype.heq_iff_coe_eq (fun x => by
        change (∑ i, x i ≤ R - (Fin.cons a.val g.1 : Fin (c + 1) → ℕ) 0)
          ↔ ∑ i, x i ≤ R - a.val
        rw [Fin.cons_zero])]
      funext i
      change (Fin.cons a.val g.1 : Fin (c + 1) → ℕ) i.succ = g.1 i
      exact Fin.cons_succ _ _ _

/-- Fibre recursion for the shell count:
`N_{c+1}(R) = Σ_{a ≤ R} N_c(R − a)`. -/
theorem latticeShellCard_succ (c R : ℕ) :
    latticeShellCard (c + 1) R
      = ∑ a ∈ Finset.range (R + 1), latticeShellCard c (R - a) := by
  rw [latticeShellCard, Nat.card_congr (shellSigmaEquiv c R),
    Nat.card_sigma]
  exact Fin.sum_univ_eq_sum_range
    (fun a => Nat.card {n : Fin c → ℕ // ∑ i, n i ≤ R - a}) (R + 1)

/-- Hockey-stick identity on an initial segment:
`∑_{a ≤ R} C(a + c, c) = C(R + c + 1, c + 1)` — Pascal's rule folded
`R + 1` times. -/
theorem sum_range_choose_add (c R : ℕ) :
    ∑ a ∈ Finset.range (R + 1), (a + c).choose c
      = (R + c + 1).choose (c + 1) := by
  induction R with
  | zero => simp
  | succ R ih =>
    rw [Finset.sum_range_succ, ih,
      show R + 1 + c = R + c + 1 from by omega,
      Nat.choose_succ_succ]
    exact Nat.add_comm _ _

/-- **Corollary `cor:ehrhart-free`** (exact stars-and-bars count): the
free commuting predictive counting function is the binomial
`N_c(R) = C(R + c, c)` — the Ehrhart polynomial of the standard
`c`-simplex, of degree `c` with leading coefficient `1/c!`. -/
theorem latticeShellCard_eq_choose (c R : ℕ) :
    latticeShellCard c R = (R + c).choose c := by
  induction c generalizing R with
  | zero =>
    rw [Nat.add_zero, Nat.choose_zero_right]
    haveI : Unique {n : Fin 0 → ℕ // ∑ i, n i ≤ R} :=
      ⟨⟨⟨fun i => i.elim0, by simp⟩⟩,
        fun a => Subtype.ext (funext fun i => i.elim0)⟩
    rw [latticeShellCard]
    exact Nat.card_unique
  | succ c ih =>
    rw [latticeShellCard_succ,
      Finset.sum_congr rfl (fun a _ => ih (R - a))]
    calc ∑ a ∈ Finset.range (R + 1), ((R - a) + c).choose c
        = ∑ a ∈ Finset.range (R + 1), (a + c).choose c := by
          have h := Finset.sum_range_reflect
            (fun m => (m + c).choose c) (R + 1)
          rw [← h]
          refine Finset.sum_congr rfl fun a ha => ?_
          congr 1
      _ = (R + c + 1).choose (c + 1) := sum_range_choose_add c R

/-- **Corollary `cor:ehrhart-free` / Proposition `prop:spectral-action`
(free shell multiplicity)**: the exact degree-shell count is the Pascal
increment `N(R+1) − N(R) = C(R + 1 + c, c)` — the binomial multiplicity
entering the free-case degree spectral action. -/
theorem latticeShellCard_shell (c R : ℕ) :
    latticeShellCard (c + 1) (R + 1)
      = latticeShellCard (c + 1) R + (R + 1 + c).choose c := by
  rw [latticeShellCard_eq_choose, latticeShellCard_eq_choose,
    show R + 1 + (c + 1) = (R + 1 + c) + 1 from by omega,
    Nat.choose_succ_succ,
    show R + 1 + c = R + (c + 1) from by omega]
  exact Nat.add_comm _ _

end NCG
