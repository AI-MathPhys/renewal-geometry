/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Mean-ergodic fixed/coboundary decomposition
  (`thm:GT-fixed-coboundary`, Gran-Tensor manuscript)

* `gt_fixed_coboundary`: for a linear contraction `T` on a
  finite-dimensional real inner-product space,
  (i) fixed vectors and co-fixed vectors coincide
      (`Tx = x ↔ T*x = x`);
  (ii) the boxed orthogonal decomposition — every fixed
      vector is orthogonal to every coboundary
      `(1-T)g`, and `Ker(1-T) ⊔ Ran(1-T) = ⊤` (the
      finite-dimensional form of
      `H = Ker(1-T) ⊕ cl Ran(1-T)`);
  (iii) the Cesàro means `M_N(T)` converge strongly to the
      fixed component on every decomposed vector
      `x = k + (1-T)g` (telescoping plus the uniform power
      bound `‖Tⁿg‖ ≤ ‖g‖`);
  (iv) a fixed accepted source reads only the zero mode:
      if `T*a = a` then `⟨a, k + (1-T)g⟩ = ⟨a, k⟩` — the
      boxed `A*Z = A*P₀Z`, and an exact coboundary has
      zero router.

The Hilbert–Schmidt variational identity
`Tr(Z*P₀Z) = inf_G ‖Z - (1-T)G‖²` and the matrix-limit
packaging `Z*P₀Z = lim Z*M_N*M_N Z` are the manuscript's
repackagings of clause (iii); the dominated router bound
`(A*Z)*(A*A)†(A*Z) ⪯ Z*P₀Z` is its Cauchy–Schwarz layer.
-/

open scoped InnerProductSpace
open Filter

namespace NCG

/-- `thm:GT-fixed-coboundary`. -/
theorem gt_fixed_coboundary {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V]
    (T : V →ₗ[ℝ] V) (hT : ∀ x, ‖T x‖ ≤ ‖x‖) :
    -- (i) fixed = co-fixed for a contraction
    (∀ x, T x = x ↔ LinearMap.adjoint T x = x)
    -- (ii) the boxed orthogonal decomposition
    ∧ (∀ k g, T k = k → ⟪k, g - T g⟫_ℝ = 0)
    ∧ LinearMap.ker (1 - T) ⊔ LinearMap.range (1 - T) = ⊤
    -- (iii) Cesàro means converge to the fixed component
    ∧ (∀ k g, T k = k →
        Tendsto (fun N : ℕ => (N : ℝ)⁻¹ •
            ∑ n ∈ Finset.range N,
              (T ^ n) (k + (g - T g)))
          atTop (nhds k))
    -- (iv) a fixed accepted source reads only the zero
    -- mode
    ∧ (∀ a k g, LinearMap.adjoint T a = a →
        ⟪a, k + (g - T g)⟫_ℝ = ⟪a, k⟫_ℝ) := by
  -- the adjoint of a contraction is a contraction
  have hTad : ∀ x, ‖LinearMap.adjoint T x‖ ≤ ‖x‖ := by
    intro x
    have h1 : ‖LinearMap.adjoint T x‖ ^ 2
        ≤ ‖x‖ * ‖LinearMap.adjoint T x‖ := by
      rw [← real_inner_self_eq_norm_sq]
      calc ⟪LinearMap.adjoint T x,
            LinearMap.adjoint T x⟫_ℝ
          = ⟪x, T (LinearMap.adjoint T x)⟫_ℝ :=
            LinearMap.adjoint_inner_left T _ x
        _ ≤ ‖x‖ * ‖T (LinearMap.adjoint T x)‖ :=
            real_inner_le_norm _ _
        _ ≤ ‖x‖ * ‖LinearMap.adjoint T x‖ :=
            mul_le_mul_of_nonneg_left (hT _)
              (norm_nonneg x)
    rcases eq_or_lt_of_le
        (norm_nonneg (LinearMap.adjoint T x)) with h0 | h0
    · rw [← h0]
      exact norm_nonneg x
    · have := h1
      rw [sq] at this
      exact le_of_mul_le_mul_right this h0
  -- one-directional fixed-point transfer for any
  -- contraction pair with the adjoint relation
  have hfix : ∀ x, T x = x → LinearMap.adjoint T x = x := by
    intro x hx
    have hcross : ⟪LinearMap.adjoint T x, x⟫_ℝ
        = ‖x‖ ^ 2 := by
      rw [LinearMap.adjoint_inner_left, hx,
        real_inner_self_eq_norm_sq]
    have hzero : ‖LinearMap.adjoint T x - x‖ ^ 2 = 0 := by
      have hexp := norm_sub_sq_real
        (LinearMap.adjoint T x) x
      have hb := hTad x
      have hnn : (0 : ℝ)
          ≤ ‖LinearMap.adjoint T x - x‖ ^ 2 :=
        sq_nonneg _
      nlinarith [hexp, hcross, hb,
        norm_nonneg (LinearMap.adjoint T x),
        norm_nonneg x]
    have := pow_eq_zero_iff (n := 2) (by norm_num)
      |>.mp hzero
    rw [norm_eq_zero, sub_eq_zero] at this
    exact this
  have hfix' : ∀ x, LinearMap.adjoint T x = x → T x = x := by
    intro x hx
    have hcross : ⟪T x, x⟫_ℝ = ‖x‖ ^ 2 := by
      rw [← LinearMap.adjoint_inner_right, hx,
        real_inner_self_eq_norm_sq]
    have hzero : ‖T x - x‖ ^ 2 = 0 := by
      have hexp := norm_sub_sq_real (T x) x
      have hb := hT x
      nlinarith [hexp, hcross, norm_nonneg (T x),
        norm_nonneg x]
    have := pow_eq_zero_iff (n := 2) (by norm_num)
      |>.mp hzero
    rw [norm_eq_zero, sub_eq_zero] at this
    exact this
  -- (ii) orthogonality
  have horth : ∀ k g, T k = k → ⟪k, g - T g⟫_ℝ = 0 := by
    intro k g hk
    rw [inner_sub_right, ← LinearMap.adjoint_inner_left,
      hfix k hk, sub_self]
  refine ⟨fun x => ⟨hfix x, hfix' x⟩, horth, ?_, ?_, ?_⟩
  · -- spanning: Ker(1-T) ⊔ Ran(1-T) = ⊤
    have hdisj : Disjoint (LinearMap.ker (1 - T))
        (LinearMap.range (1 - T)) := by
      rw [Submodule.disjoint_def]
      intro x hxk hxr
      obtain ⟨g, hg⟩ := hxr
      have hkx : T x = x := by
        have h := LinearMap.mem_ker.mp hxk
        simp only [LinearMap.sub_apply,
          Module.End.one_apply, sub_eq_zero] at h
        exact h.symm
      have hx : x = g - T g := by
        rw [← hg]
        simp [LinearMap.sub_apply, Module.End.one_apply]
      have h0 : ⟪x, x⟫_ℝ = 0 := by
        nth_rewrite 2 [hx]
        exact horth x g hkx
      exact inner_self_eq_zero.mp h0
    have hdim :=
      LinearMap.finrank_range_add_finrank_ker (1 - T)
    have hsup := Submodule.finrank_sup_add_finrank_inf_eq
      (LinearMap.ker (1 - T)) (LinearMap.range (1 - T))
    rw [Disjoint.eq_bot hdisj] at hsup
    simp only [finrank_bot, add_zero] at hsup
    exact Submodule.eq_top_of_finrank_eq (by omega)
  · -- (iii) Cesàro convergence
    intro k g hk
    have hpowk : ∀ n : ℕ, (T ^ n) k = k := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ, Module.End.mul_apply, hk, ih]
    have hpowg : ∀ n : ℕ, ‖(T ^ n) g‖ ≤ ‖g‖ := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ', Module.End.mul_apply]
        exact (hT _).trans ih
    have hterm : ∀ n : ℕ, (T ^ n) (k + (g - T g))
        = k + ((T ^ n) g - (T ^ (n + 1)) g) := by
      intro n
      rw [map_add, map_sub, hpowk]
      congr 2
    have hsum : ∀ N : ℕ,
        ∑ n ∈ Finset.range N, (T ^ n) (k + (g - T g))
          = N • k + (g - (T ^ N) g) := by
      intro N
      rw [Finset.sum_congr rfl fun n _ => hterm n,
        Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_range, Finset.sum_range_sub'
          (f := fun n => (T ^ n) g)]
      simp
    have hev : (fun N : ℕ => k
          + (N : ℝ)⁻¹ • (g - (T ^ N) g))
        =ᶠ[atTop] (fun N : ℕ => (N : ℝ)⁻¹ •
          ∑ n ∈ Finset.range N,
            (T ^ n) (k + (g - T g))) := by
      filter_upwards [Filter.eventually_ge_atTop 1]
        with N hN
      rw [hsum, smul_add]
      congr 1
      rw [← Nat.cast_smul_eq_nsmul ℝ N k, smul_smul,
        inv_mul_cancel₀ (by exact_mod_cast
          Nat.one_le_iff_ne_zero.mp hN), one_smul]
    have hr : Tendsto (fun N : ℕ =>
        (N : ℝ)⁻¹ • (g - (T ^ N) g)) atTop (nhds 0) := by
      refine squeeze_zero_norm (fun N => ?_)
        (tendsto_const_div_atTop_nhds_zero_nat
          (2 * ‖g‖))
      rw [norm_smul, Real.norm_eq_abs, abs_inv,
        Nat.abs_cast]
      calc ((N : ℝ))⁻¹ * ‖g - (T ^ N) g‖
          ≤ ((N : ℝ))⁻¹ * (2 * ‖g‖) := by
            apply mul_le_mul_of_nonneg_left _
              (by positivity)
            calc ‖g - (T ^ N) g‖
                ≤ ‖g‖ + ‖(T ^ N) g‖ := norm_sub_le _ _
              _ ≤ 2 * ‖g‖ := by
                  have := hpowg N
                  linarith
        _ = 2 * ‖g‖ / N := by
            rw [inv_mul_eq_div]
    have hfin := (tendsto_const_nhds (x := k)
      (f := atTop)).add hr
    rw [add_zero] at hfin
    exact hfin.congr' hev
  · -- (iv) zero-mode coupling
    intro a k g ha
    rw [inner_add_right, inner_sub_right,
      ← LinearMap.adjoint_inner_left, ha, sub_self,
      add_zero]

end NCG
