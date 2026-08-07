/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Termination, exactness, and record margin
  (`thm:minimal-record-audit`, Gran-Tensor manuscript)

* `minimal_record_audit`: (P2) strictly refining block counts
  grow at least linearly, so refinement bounded by `n` blocks
  stabilizes within `n-1` strict rounds; (P1/P3) a fixed point
  of the refinement operator is word-equivalence (equality
  preserved by immediate coordinates and every primitive update
  propagates to every word); (P4) the boxed signature residual
  `‖v(r)-v(s)‖² = 0` iff the signatures agree; (P5) the
  robust-recovery margin: within-ε estimates keep same-class
  distances ≤ 2ε and distinct-class distances ≥ δ-2ε, separated
  when `4ε < δ`.

Rendering disclosed: partitions are rendered by their block
counts (P2), refinement fixed points (P1/P3), finite signature
vectors (P4), and normed estimates (P5) — the finite
operational data of the construction.
-/

namespace NCG

/-- `thm:minimal-record-audit`. -/
theorem minimal_record_audit :
    -- (P2) strict refinement rounds grow the block count
    --      linearly, hence stabilize within n - 1 rounds
    (∀ (dim : ℕ → ℕ), (∀ k, dim k < dim (k + 1)) →
      1 ≤ dim 0 → ∀ k, 1 + k ≤ dim k)
    -- (P1/P3) a refinement fixed point is word-equivalence
    ∧ (∀ {R Sig A : Type} (sig0 : R → Sig) (u : A → R → R)
        (P : R → R → Prop),
        (∀ r s, P r s ↔
          (sig0 r = sig0 s ∧ ∀ a, P (u a r) (u a s))) →
        ∀ (w : List A) (r s : R), P r s →
          sig0 (w.foldl (fun x a => u a x) r)
            = sig0 (w.foldl (fun x a => u a x) s))
    -- (P4) zero signature residual iff equal signatures
    ∧ (∀ {I : Type} [Fintype I] (x y : I → ℝ),
        (∑ i, (x i - y i) ^ 2 = 0) ↔ x = y)
    -- (P5) the robust-recovery margin
    ∧ (∀ {E R' : Type} [SeminormedAddCommGroup E]
        (v est : R' → E) (ε : ℝ),
        (∀ r, ‖est r - v r‖ ≤ ε) →
        (∀ r s, v r = v s → ‖est r - est s‖ ≤ 2 * ε)
        ∧ (∀ (δ : ℝ) (r s : R'), δ ≤ ‖v r - v s‖ →
            δ - 2 * ε ≤ ‖est r - est s‖)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro dim hstrict h0 k
    induction k with
    | zero => simpa using h0
    | succ m ih =>
        have := hstrict m
        omega
  · intro R Sig A sig0 u P hfix w
    induction w with
    | nil =>
        intro r s hP
        exact ((hfix r s).mp hP).1
    | cons a w ih =>
        intro r s hP
        exact ih (u a r) (u a s) (((hfix r s).mp hP).2 a)
  · intro I _ x y
    constructor
    · intro hsum
      funext i
      have hterm := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => sq_nonneg (x j - y j))).mp hsum i
        (Finset.mem_univ i)
      have := pow_eq_zero_iff (n := 2) (by norm_num)
        |>.mp hterm
      linarith [sub_eq_zero.mp this]
    · rintro rfl
      simp
  · intro E R' _ v est ε hest
    constructor
    · intro r s hv
      have hdec : est r - est s
          = (est r - v r) - (est s - v s) := by
        rw [hv]
        abel
      rw [hdec]
      calc ‖(est r - v r) - (est s - v s)‖
          ≤ ‖est r - v r‖ + ‖est s - v s‖ := norm_sub_le _ _
        _ ≤ ε + ε := add_le_add (hest r) (hest s)
        _ = 2 * ε := by ring
    · intro δ r s hδ
      have hdec : v r - v s
          = (v r - est r) + (est r - est s)
            + (est s - v s) := by abel
      have htri : ‖v r - v s‖
          ≤ ‖v r - est r‖ + ‖est r - est s‖
            + ‖est s - v s‖ := by
        rw [hdec]
        exact norm_add₃_le
      have h1 : ‖v r - est r‖ ≤ ε := by
        rw [norm_sub_rev]
        exact hest r
      have h2 : ‖est s - v s‖ ≤ ε := hest s
      linarith

end NCG
