/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Flagship.GramStability

/-!
# Robust polarized-clock factorization
  (`thm:robust-clock-factorization-master`, flagship manuscript)

For the normalized Gram `T` of polarized `N`-slot histories with
paired slot indices, slot factors `G_j`, and the successive-cut
hypothesis within `δ`:

* the entrywise telescoping bound
  `|T(c) - ∏_j G_j(c_j)| ≤ (N-1)δ` (`clock_entrywise_bound`):
  the difference telescopes into prefixed cut defects with unit
  prefix moduli, and the last cut is exact;
* the boxed operator bound `‖G - G_prod‖ ≤ D(N-1)δ` in the
  quadratic-form language that feeds the stability theorem
  (`clock_form_bound`), `D = m^N`, via the `1`/`2`-norm
  Cauchy–Schwarz comparison — the manuscript's maximal-row-sum
  bound is used exactly through this consequence;
* the boxed source-product bound
  (`robust_clock_factorization`): composing with
  `gram_source_stability`, a source-fixing unitary `U` from the
  product frame satisfies
  `‖Ξ_a - U(ξ_{1,a_1}⊗···⊗ξ_{N,a_N})‖ ≤ 1 - √(1 - D(N-1)δ/g)`;
* the tensor floor step (`kron_floor_posSemidef`): one binary
  step of the closing clause — if `A ⪰ aI`, `B ⪰ bI`, `B ⪰ 0`
  and `a ≥ 0`, then `A ⊗ B ⪰ abI`; the `N`-fold statement
  `g_prod ≥ g₁^N` is its iteration (the iteration is the prose
  remark).
-/

open Finset Matrix Kronecker
open scoped ComplexOrder

namespace NCG

variable {m N : ℕ}

/-- Zero out the first `j` slots of a paired history. -/
def maskBelow [NeZero m] (j : ℕ)
    (c : Fin N → Fin m × Fin m) : Fin N → Fin m × Fin m :=
  fun i => if (i : ℕ) < j then (0, 0) else c i

/-- The entrywise telescoping bound
`|T(c) - ∏_j G_j(c_j)| ≤ (N-1)δ`. -/
theorem clock_entrywise_bound [NeZero m]
    (T : (Fin N → Fin m × Fin m) → ℂ)
    (Gs : ℕ → Fin m × Fin m → ℂ) (δ : ℝ)
    (hT0 : T (fun _ => (0, 0)) = 1)
    (hG1 : ∀ j x, ‖Gs j x‖ ≤ 1)
    (hcut : ∀ j : ℕ, ∀ _ : j + 1 < N,
      ∀ c : Fin N → Fin m × Fin m,
      ‖T (maskBelow j c) - Gs j (c ⟨j, by omega⟩)
        * T (maskBelow (j + 1) c)‖ ≤ δ)
    (hlast : ∀ (_ : 0 < N) (c : Fin N → Fin m × Fin m),
      T (maskBelow (N - 1) c)
        = Gs (N - 1) (c ⟨N - 1, by omega⟩))
    (hN : 0 < N) (c : Fin N → Fin m × Fin m) :
    ‖T c - ∏ j : Fin N, Gs j (c j)‖ ≤ (N - 1) * δ := by
  classical
  set c' : ℕ → Fin m × Fin m := fun i =>
    if h : i < N then c ⟨i, h⟩ else (0, 0) with hc'
  set G' : ℕ → ℂ := fun i => Gs i (c' i) with hG'
  set A : ℕ → ℂ := fun j =>
    (∏ i ∈ Finset.range j, G' i) * T (maskBelow j c) with hA
  have hA0 : A 0 = T c := by
    simp only [hA]
    rw [Finset.range_zero, Finset.prod_empty, one_mul]
    congr 1
  have hmaskN : maskBelow (N : ℕ) c
      = (fun _ => ((0 : Fin m), (0 : Fin m))) := by
    funext i
    simp [maskBelow, i.isLt]
  have hAN : A N = ∏ j : Fin N, Gs j (c j) := by
    simp only [hA]
    rw [hmaskN, hT0, mul_one, ← Fin.prod_univ_eq_prod_range]
    refine Finset.prod_congr rfl fun j _ => ?_
    simp only [hG', hc']
    simp [j.isLt]
  have htel : T c - ∏ j : Fin N, Gs j (c j)
      = ∑ j ∈ Finset.range N, (A j - A (j + 1)) := by
    rw [Finset.sum_range_sub' A N, hA0, hAN]
  have hstep : ∀ j, A j - A (j + 1)
      = (∏ i ∈ Finset.range j, G' i)
        * (T (maskBelow j c) - G' j
          * T (maskBelow (j + 1) c)) := by
    intro j
    simp only [hA]
    rw [Finset.prod_range_succ]
    ring
  have hpref : ∀ j, ‖∏ i ∈ Finset.range j, G' i‖ ≤ 1 := by
    intro j
    rw [norm_prod]
    refine Finset.prod_le_one (fun i _ => norm_nonneg _)
      (fun i _ => hG1 i _)
  have hdefect : ∀ j ∈ Finset.range N,
      ‖A j - A (j + 1)‖ ≤ if j + 1 < N then δ else 0 := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [hstep j, norm_mul]
    by_cases hj1 : j + 1 < N
    · rw [if_pos hj1]
      calc ‖∏ i ∈ Finset.range j, G' i‖
            * ‖T (maskBelow j c) - G' j
              * T (maskBelow (j + 1) c)‖
          ≤ 1 * δ := by
            refine mul_le_mul (hpref j) ?_ (norm_nonneg _)
              zero_le_one
            have h9 := hcut j hj1 c
            simp only [hG', hc']
            rw [dif_pos (show j < N by omega)]
            exact h9
        _ = δ := one_mul δ
    · rw [if_neg hj1]
      have hjN : j = N - 1 := by omega
      have h9 : T (maskBelow j c) - G' j
          * T (maskBelow (j + 1) c) = 0 := by
        subst hjN
        have h10 : maskBelow (N - 1 + 1) c
            = (fun _ => ((0 : Fin m), (0 : Fin m))) := by
          funext i
          simp [maskBelow, show (i : ℕ) < N - 1 + 1 by omega]
        rw [h10, hT0, mul_one, hlast hN c]
        simp only [hG', hc']
        rw [dif_pos (show N - 1 < N by omega)]
        exact sub_self _
      rw [h9, norm_zero, mul_zero]
  calc ‖T c - ∏ j : Fin N, Gs j (c j)‖
      = ‖∑ j ∈ Finset.range N, (A j - A (j + 1))‖ := by
        rw [htel]
    _ ≤ ∑ j ∈ Finset.range N,
          (if j + 1 < N then δ else 0) :=
        (norm_sum_le _ _).trans
          (Finset.sum_le_sum hdefect)
    _ = ∑ _j ∈ Finset.range (N - 1), δ := by
        rw [show N = (N - 1) + 1 from by omega,
          Finset.sum_range_succ]
        rw [if_neg (by omega), add_zero]
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [Finset.mem_range] at hj
        rw [if_pos (by omega)]
    _ = ((N : ℝ) - 1) * δ := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one]

/-- The boxed operator bound in quadratic-form language:
`|z*(G - G_prod)z| ≤ D(N-1)δ·‖z‖²` with `D = m^N`. -/
theorem clock_form_bound [NeZero m]
    (T : (Fin N → Fin m × Fin m) → ℂ)
    (Gs : ℕ → Fin m × Fin m → ℂ) (δ : ℝ)
    (hent : ∀ c : Fin N → Fin m × Fin m,
      ‖T c - ∏ j : Fin N, Gs j (c j)‖ ≤ (N - 1) * δ)
    (hd : 0 ≤ ((N : ℝ) - 1) * δ)
    (z : (Fin N → Fin m) → ℂ) :
    ‖∑ a : Fin N → Fin m, ∑ b : Fin N → Fin m,
        starRingEnd ℂ (z a) * z b
          * (T (fun j => (a j, b j))
            - ∏ j : Fin N, Gs j (a j, b j))‖
      ≤ (Fintype.card (Fin N → Fin m) : ℝ) * ((N : ℝ) - 1)
        * δ * ∑ a, ‖z a‖ ^ 2 := by
  classical
  set Dc : ℝ := (Fintype.card (Fin N → Fin m) : ℝ) with hDc
  have h1 : ‖∑ a : Fin N → Fin m, ∑ b : Fin N → Fin m,
      starRingEnd ℂ (z a) * z b
        * (T (fun j => (a j, b j))
          - ∏ j : Fin N, Gs j (a j, b j))‖
      ≤ ∑ a : Fin N → Fin m, ∑ b : Fin N → Fin m,
        ‖z a‖ * ‖z b‖ * (((N : ℝ) - 1) * δ) := by
    refine (norm_sum_le _ _).trans ?_
    refine Finset.sum_le_sum fun a _ => ?_
    refine (norm_sum_le _ _).trans ?_
    refine Finset.sum_le_sum fun b _ => ?_
    rw [norm_mul, norm_mul, RCLike.norm_conj]
    exact mul_le_mul_of_nonneg_left (hent _)
      (by positivity)
  have h2 : ∑ a : Fin N → Fin m, ∑ b : Fin N → Fin m,
      ‖z a‖ * ‖z b‖ * (((N : ℝ) - 1) * δ)
      = (∑ a, ‖z a‖) ^ 2 * (((N : ℝ) - 1) * δ) := by
    rw [sq, Finset.sum_mul_sum]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_mul]
  have h3 : (∑ a, ‖z a‖) ^ 2 ≤ Dc * ∑ a, ‖z a‖ ^ 2 := by
    have h4 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun a : Fin N → Fin m => ‖z a‖) (fun _ => (1 : ℝ))
    simp only [mul_one, one_pow] at h4
    calc (∑ a, ‖z a‖) ^ 2
        ≤ (∑ a, ‖z a‖ ^ 2) * ∑ _a : Fin N → Fin m, (1 : ℝ) :=
          h4
      _ = Dc * ∑ a, ‖z a‖ ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ,
            nsmul_eq_mul, mul_one, mul_comm, hDc]
  calc ‖∑ a : Fin N → Fin m, ∑ b : Fin N → Fin m,
      starRingEnd ℂ (z a) * z b
        * (T (fun j => (a j, b j))
          - ∏ j : Fin N, Gs j (a j, b j))‖
      ≤ (∑ a, ‖z a‖) ^ 2 * (((N : ℝ) - 1) * δ) := by
        rw [← h2]
        exact h1
    _ ≤ Dc * (∑ a, ‖z a‖ ^ 2) * (((N : ℝ) - 1) * δ) :=
        mul_le_mul_of_nonneg_right h3 hd
    _ = Dc * ((N : ℝ) - 1) * δ * ∑ a, ‖z a‖ ^ 2 := by
        ring

/-- `thm:robust-clock-factorization-master`, boxed source-product
bound: composing the telescoped Gram bound with
`gram_source_stability` yields the source-fixing unitary within
`1 - √(1 - D(N-1)δ/g)`. -/
theorem robust_clock_factorization
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [NeZero m]
    (b : Module.Basis (Fin N → Fin m) ℂ E)
    (Ξ : (Fin N → Fin m) → E)
    (T : (Fin N → Fin m × Fin m) → ℂ)
    (Gs : ℕ → Fin m × Fin m → ℂ) (δ g : ℝ)
    (hg : 0 < g) (hδD : 0 ≤ ((N : ℝ) - 1) * δ)
    (hsmall : (Fintype.card (Fin N → Fin m) : ℝ)
      * ((N : ℝ) - 1) * δ < g)
    (hbnorm : ∀ a, ‖b a‖ = 1)
    (hent : ∀ c : Fin N → Fin m × Fin m,
      ‖T c - ∏ j : Fin N, Gs j (c j)‖ ≤ (N - 1) * δ)
    (hG0 : ∀ z : (Fin N → Fin m) → ℂ,
      g * ∑ a, ‖z a‖ ^ 2 ≤ ‖∑ a, z a • b a‖ ^ 2)
    (hlink : ∀ z : (Fin N → Fin m) → ℂ,
      ‖∑ a, z a • Ξ a‖ ^ 2 - ‖∑ a, z a • b a‖ ^ 2
        = (∑ a : Fin N → Fin m, ∑ b' : Fin N → Fin m,
            starRingEnd ℂ (z a) * z b'
              * (T (fun j => (a j, b' j))
                - ∏ j : Fin N, Gs j (a j, b' j))).re) :
    ∃ U : E →ₗ[ℂ] E,
      (∀ v w : E, inner ℂ (U v) (U w) = inner ℂ v w)
      ∧ ∀ a, ‖Ξ a - U (b a)‖
          ≤ 1 - Real.sqrt
            (1 - (Fintype.card (Fin N → Fin m) : ℝ)
              * ((N : ℝ) - 1) * δ / g) := by
  classical
  set εG : ℝ := (Fintype.card (Fin N → Fin m) : ℝ)
    * ((N : ℝ) - 1) * δ with hεG
  have hεG0 : 0 ≤ εG := by
    rw [hεG]
    have : (0 : ℝ) ≤ (Fintype.card (Fin N → Fin m) : ℝ) := by
      positivity
    nlinarith
  have hGd : ∀ z : (Fin N → Fin m) → ℂ,
      |‖∑ a, z a • Ξ a‖ ^ 2 - ‖∑ a, z a • b a‖ ^ 2|
        ≤ εG * ∑ a, ‖z a‖ ^ 2 := by
    intro z
    rw [hlink z]
    calc |(∑ a : Fin N → Fin m, ∑ b' : Fin N → Fin m,
        starRingEnd ℂ (z a) * z b'
          * (T (fun j => (a j, b' j))
            - ∏ j : Fin N, Gs j (a j, b' j))).re|
        ≤ ‖∑ a : Fin N → Fin m, ∑ b' : Fin N → Fin m,
            starRingEnd ℂ (z a) * z b'
              * (T (fun j => (a j, b' j))
                - ∏ j : Fin N, Gs j (a j, b' j))‖ :=
          Complex.abs_re_le_norm _
      _ ≤ εG * ∑ a, ‖z a‖ ^ 2 := by
          rw [hεG]
          exact clock_form_bound T Gs δ hent hδD z
  set r : ℝ := εG / g with hr
  have hr0 : 0 ≤ r := div_nonneg hεG0 hg.le
  have hr1 : r < 1 := by
    rw [hr, div_lt_one hg]
    exact hsmall
  have hframe := fun v => gram_frame_bounds b Ξ g εG hg hεG0
    hG0 hGd v
  exact gram_source_stability b Ξ r hr0 hr1 hbnorm
    (fun v => (hframe v).1) (fun v => (hframe v).2)

/-- One binary step of the tensor least-eigenvalue clause:
`A ⪰ aI`, `B ⪰ bI`, `B ⪰ 0`, `a ≥ 0` give `A ⊗ B ⪰ abI`. -/
theorem kron_floor_posSemidef {p q : ℕ}
    (A : Matrix (Fin p) (Fin p) ℂ)
    (B : Matrix (Fin q) (Fin q) ℂ) (a bb : ℝ) (ha : 0 ≤ a)
    (hA : (A - (a : ℂ) • 1).PosSemidef)
    (hB : (B - (bb : ℂ) • 1).PosSemidef)
    (hBp : B.PosSemidef) :
    ((A ⊗ₖ B) - ((a * bb : ℝ) : ℂ)
      • (1 : Matrix (Fin p × Fin q) (Fin p × Fin q) ℂ))
      |>.PosSemidef := by
  have hdecomp : (A ⊗ₖ B) - ((a * bb : ℝ) : ℂ)
      • (1 : Matrix (Fin p × Fin q) (Fin p × Fin q) ℂ)
      = ((A - (a : ℂ) • 1) ⊗ₖ B)
        + (((a : ℝ) : ℂ) • 1
            : Matrix (Fin p) (Fin p) ℂ)
          ⊗ₖ (B - (bb : ℂ) • 1) := by
    ext ⟨i, k⟩ ⟨j, l⟩
    simp only [Matrix.sub_apply, Matrix.add_apply,
      Matrix.smul_apply, Matrix.kroneckerMap_apply,
      Matrix.one_apply, Prod.mk.injEq, smul_eq_mul]
    by_cases hij : i = j <;> by_cases hkl : k = l <;>
      simp [hij, hkl] <;> ring
  rw [hdecomp]
  refine Matrix.PosSemidef.add ?_ ?_
  · exact hA.kronecker hBp
  · refine Matrix.PosSemidef.kronecker ?_ hB
    have hdiag : (((a : ℝ) : ℂ)
        • (1 : Matrix (Fin p) (Fin p) ℂ))
        = Matrix.diagonal (fun _ => ((a : ℝ) : ℂ)) := by
      ext i j
      by_cases hij : i = j <;>
        simp [Matrix.diagonal, hij]
    rw [hdiag]
    exact Matrix.PosSemidef.diagonal fun i =>
      Complex.zero_le_real.mpr ha

end NCG
