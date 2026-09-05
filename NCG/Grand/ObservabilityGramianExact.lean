/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The hypocoercive observability Gram and its kernel

Machinery for `thm:GT-hypocoercive-memory`, algebraic and spectral part.  On a
finite-dimensional complex Hilbert space with a positive loss `S` and a generator `A`:

* `obsGram A S r = ∑_{j ≤ r} (A*)^j S A^j` (FC.8) is positive, and its kernel is
  `⋂_{j ≤ r} ker (S A^j)` (`obsGram_apply_eq_zero_iff`);
* by Cayley–Hamilton the kernels stabilize by depth `d - 1` (`ker_obsGram_stabilizes`), and
  `ker O_{d-1}` is the largest `A`-invariant subspace of `ker S` (FC.9,
  `unobservable_isInvariantIn`, `le_unobservable_of_isInvariantIn`, `ker_obsGram_eq_unobservable`);
* (H1) `O_{d-1} ≻ 0` is equivalent to (H2) "no nonzero `A`-invariant subspace lies in `ker S`"
  (`posDef_obsGram_iff_no_invariant`);
* for `K = A - S` with `A` skew-adjoint, (H2) is equivalent to (H3) "every eigenvalue of `K` has
  negative real part" (`no_invariant_iff_eigenvalues_neg`).
-/

open ContinuousLinearMap Finset Module
open scoped InnerProductSpace

namespace NCG
namespace HypocoerciveMemory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-! ### A positive operator with vanishing quadratic form kills the vector -/

omit [CompleteSpace E] in
/-- If `T ≥ 0` and `re ⟪T x, x⟫ = 0` then `T x = 0`. -/
theorem apply_eq_zero_of_re_inner_eq_zero {T : E →L[ℂ] E} (hT : T.IsPositive) {x : E}
    (hx : RCLike.re ⟪T x, x⟫_ℂ = 0) : T x = 0 := by
  set a : ℝ := RCLike.re ⟪T x, T x⟫_ℂ with ha
  set b : ℝ := RCLike.re ⟪T (T x), T x⟫_ℂ with hb
  have hb0 : 0 ≤ b := hT.re_inner_nonneg_left (T x)
  have hsymm : ∀ u v : E, ⟪T u, v⟫_ℂ = ⟪u, T v⟫_ℂ := fun u v => hT.isSymmetric u v
  have him : (⟪T (T x), T x⟫_ℂ).im = 0 := by
    have h1 : ⟪T (T x), T x⟫_ℂ = (starRingEnd ℂ) ⟪T (T x), T x⟫_ℂ := by
      rw [inner_conj_symm, hsymm]
    exact Complex.conj_eq_iff_im.mp h1.symm
  have him2 : (⟪T x, T x⟫_ℂ).im = 0 := inner_self_im (𝕜 := ℂ) (T x)
  have hx' : (⟪T x, x⟫_ℂ).re = 0 := hx
  -- the quadratic form along `x + t • T x`
  have key : ∀ t : ℝ, 0 ≤ 2 * t * a + t ^ 2 * b := by
    intro t
    have h := hT.re_inner_nonneg_left (x + (t : ℂ) • T x)
    rw [map_add, map_smul, inner_add_left, inner_add_right, inner_add_right, inner_smul_left,
      inner_smul_right, inner_smul_left, inner_smul_right, hsymm (T x) x] at h
    simp only [RCLike.re_to_complex, Complex.add_re, Complex.mul_re, Complex.mul_im,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, hx', him, him2,
      mul_zero, zero_mul, sub_zero, neg_zero, add_zero, zero_add] at h
    rw [ha, hb, RCLike.re_to_complex, RCLike.re_to_complex]
    nlinarith [h]
  by_contra hne
  have hapos : 0 < a := by
    rw [ha, inner_self_eq_norm_sq (𝕜 := ℂ)]
    have : 0 < ‖T x‖ := norm_pos_iff.mpr hne
    positivity
  set t : ℝ := -a / (b + 1) with ht
  have hexpr : 2 * t * a + t ^ 2 * b = -(a ^ 2 * (b + 2)) / (b + 1) ^ 2 := by
    rw [ht]
    field_simp
    ring
  have hneg : -(a ^ 2 * (b + 2)) / (b + 1) ^ 2 < 0 := by
    apply div_neg_of_neg_of_pos
    · nlinarith [sq_nonneg a]
    · positivity
  have := key t
  rw [hexpr] at this
  linarith

/-! ### The observability Gram (FC.8) -/

/-- `O_r = ∑_{j=0}^{r} (A*)^j S A^j` (FC.8). -/
noncomputable def obsGram (A S : E →L[ℂ] E) (r : ℕ) : E →L[ℂ] E :=
  ∑ j ∈ range (r + 1), star A ^ j * S * A ^ j

theorem inner_obsGram (A S : E →L[ℂ] E) (r : ℕ) (x : E) :
    ⟪obsGram A S r x, x⟫_ℂ = ∑ j ∈ range (r + 1), ⟪S ((A ^ j) x), (A ^ j) x⟫_ℂ := by
  simp only [obsGram, _root_.sum_apply, sum_inner]
  refine sum_congr rfl fun j _ => ?_
  rw [← star_pow, star_eq_adjoint]
  exact adjoint_inner_left _ _ _

theorem obsGram_isPositive (A : E →L[ℂ] E) {S : E →L[ℂ] E} (hS : S.IsPositive) (r : ℕ) :
    (obsGram A S r).IsPositive := by
  refine isPositive_sum _ fun j _ => ?_
  have := hS.adjoint_conj (A ^ j)
  rwa [← star_eq_adjoint, star_pow] at this

theorem re_inner_obsGram (A S : E →L[ℂ] E) (r : ℕ) (x : E) :
    RCLike.re ⟪obsGram A S r x, x⟫_ℂ
      = ∑ j ∈ range (r + 1), RCLike.re ⟪S ((A ^ j) x), (A ^ j) x⟫_ℂ := by
  rw [inner_obsGram, map_sum]

/-- **Kernel of the observability Gram**: `O_r x = 0 ⟺ S A^j x = 0` for all `j ≤ r`. -/
theorem obsGram_apply_eq_zero_iff (A : E →L[ℂ] E) {S : E →L[ℂ] E} (hS : S.IsPositive) (r : ℕ)
    (x : E) : obsGram A S r x = 0 ↔ ∀ j ∈ range (r + 1), S ((A ^ j) x) = 0 := by
  constructor
  · intro h j hj
    have h0 : RCLike.re ⟪obsGram A S r x, x⟫_ℂ = 0 := by rw [h]; simp
    rw [re_inner_obsGram] at h0
    have hterm := (sum_eq_zero_iff_of_nonneg fun i _ => hS.re_inner_nonneg_left ((A ^ i) x)).mp
      h0 j hj
    exact apply_eq_zero_of_re_inner_eq_zero hS hterm
  · intro h
    simp only [obsGram, _root_.sum_apply]
    exact sum_eq_zero fun j hj => by
      change (star A ^ j) (S ((A ^ j) x)) = 0
      rw [h j hj, map_zero]

/-! ### Cayley–Hamilton: the kernels stabilize by depth `d - 1` -/

variable [FiniteDimensional ℂ E]

omit [CompleteSpace E] in
/-- Every `S A^k x` vanishes once `S A^j x = 0` for all `j < finrank E` (Cayley–Hamilton). -/
theorem apply_pow_eq_zero_of_lt_finrank (A S : E →L[ℂ] E) (x : E)
    (h : ∀ j ∈ range (finrank ℂ E), S ((A ^ j) x) = 0) (k : ℕ) : S ((A ^ k) x) = 0 := by
  set d := finrank ℂ E with hd
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · -- trivial space
    have : x = 0 := by
      have hsub : Subsingleton E := finrank_zero_iff.mp hd0
      exact Subsingleton.elim x 0
    rw [this, map_zero, map_zero]
  · set f : E →ₗ[ℂ] E := (A : E →ₗ[ℂ] E) with hf
    have hdeg : f.charpoly.natDegree = d := LinearMap.charpoly_natDegree f
    have hne1 : f.charpoly ≠ 1 := by
      intro h1
      rw [h1, Polynomial.natDegree_one] at hdeg
      omega
    have hlt : (Polynomial.X ^ k %ₘ f.charpoly).natDegree < d := by
      rw [← hdeg]
      exact Polynomial.natDegree_modByMonic_lt _ (LinearMap.charpoly_monic f) hne1
    have hpow : (A ^ k) x = ∑ i ∈ range d,
        (Polynomial.X ^ k %ₘ f.charpoly).coeff i • (A ^ i) x := by
      have h1 : (A ^ k) x = (f ^ k) x := by rw [hf, ← ContinuousLinearMap.coe_pow]; rfl
      rw [h1, LinearMap.pow_eq_aeval_mod_charpoly, Polynomial.aeval_eq_sum_range' hlt,
        LinearMap.sum_apply]
      refine sum_congr rfl fun i _ => ?_
      rw [LinearMap.smul_apply, hf, ← ContinuousLinearMap.coe_pow]
      rfl
    rw [hpow, map_sum]
    exact sum_eq_zero fun i hi => by rw [map_smul, h i hi, smul_zero]

/-- The unobservable subspace `⋂_j ker (S A^j)`. -/
noncomputable def unobservable (A S : E →L[ℂ] E) : Submodule ℂ E :=
  ⨅ j : ℕ, LinearMap.ker ((S * A ^ j : E →L[ℂ] E) : E →ₗ[ℂ] E)

omit [CompleteSpace E] [FiniteDimensional ℂ E] in
theorem mem_unobservable_iff (A S : E →L[ℂ] E) (x : E) :
    x ∈ unobservable A S ↔ ∀ j : ℕ, S ((A ^ j) x) = 0 := by
  unfold unobservable
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
  exact Iff.rfl

/-- **Rank stabilization / (FC.9)**: for `r ≥ d - 1` the kernel of `O_r` is the unobservable
subspace `⋂_j ker (S A^j)`. -/
theorem ker_obsGram_eq_unobservable (A : E →L[ℂ] E) {S : E →L[ℂ] E} (hS : S.IsPositive)
    {r : ℕ} (hr : finrank ℂ E ≤ r + 1) :
    LinearMap.ker ((obsGram A S r : E →L[ℂ] E) : E →ₗ[ℂ] E) = unobservable A S := by
  ext x
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, obsGram_apply_eq_zero_iff A hS,
    mem_unobservable_iff]
  constructor
  · intro h k
    refine apply_pow_eq_zero_of_lt_finrank A S x (fun j hj => h j ?_) k
    rw [mem_range] at hj ⊢
    omega
  · intro h j _
    exact h j

theorem ker_obsGram_stabilizes (A : E →L[ℂ] E) {S : E →L[ℂ] E} (hS : S.IsPositive)
    {r r' : ℕ} (hr : finrank ℂ E ≤ r + 1) (hr' : finrank ℂ E ≤ r' + 1) :
    LinearMap.ker ((obsGram A S r : E →L[ℂ] E) : E →ₗ[ℂ] E)
      = LinearMap.ker ((obsGram A S r' : E →L[ℂ] E) : E →ₗ[ℂ] E) := by
  rw [ker_obsGram_eq_unobservable A hS hr, ker_obsGram_eq_unobservable A hS hr']

/-- `W` is an `A`-invariant subspace contained in `ker S`. -/
def IsInvariantIn (A S : E →L[ℂ] E) (W : Submodule ℂ E) : Prop :=
  (∀ y ∈ W, A y ∈ W) ∧ ∀ y ∈ W, S y = 0

omit [CompleteSpace E] [FiniteDimensional ℂ E] in
theorem unobservable_isInvariantIn (A S : E →L[ℂ] E) :
    IsInvariantIn A S (unobservable A S) := by
  refine ⟨fun y hy => ?_, fun y hy => ?_⟩
  · rw [mem_unobservable_iff] at hy ⊢
    intro j
    have := hy (j + 1)
    rw [pow_succ] at this
    exact this
  · rw [mem_unobservable_iff] at hy
    simpa using hy 0

omit [CompleteSpace E] [FiniteDimensional ℂ E] in
/-- The unobservable subspace is the **largest** `A`-invariant subspace of `ker S`. -/
theorem le_unobservable_of_isInvariantIn (A S : E →L[ℂ] E) {W : Submodule ℂ E}
    (hW : IsInvariantIn A S W) : W ≤ unobservable A S := by
  intro x hx
  rw [mem_unobservable_iff]
  intro j
  have hmem : ∀ j : ℕ, (A ^ j) x ∈ W := by
    intro j
    induction j with
    | zero => simpa using hx
    | succ j ih =>
      rw [pow_succ']
      exact hW.1 _ ih
  exact hW.2 _ (hmem j)

/-! ### (H1) ⟺ (H2) -/

/-- (H1): the Gram `O_r` is positive definite. -/
def PosDefGram (A S : E →L[ℂ] E) (r : ℕ) : Prop :=
  ∀ x : E, x ≠ 0 → 0 < RCLike.re ⟪obsGram A S r x, x⟫_ℂ

/-- (H2): no nonzero `A`-invariant subspace lies in `ker S`. -/
def NoInvariant (A S : E →L[ℂ] E) : Prop :=
  ∀ W : Submodule ℂ E, IsInvariantIn A S W → W = ⊥

/-- **(H1) ⟺ (H2)** at any depth `r ≥ d - 1`. -/
theorem posDefGram_iff_noInvariant (A : E →L[ℂ] E) {S : E →L[ℂ] E} (hS : S.IsPositive)
    {r : ℕ} (hr : finrank ℂ E ≤ r + 1) : PosDefGram A S r ↔ NoInvariant A S := by
  constructor
  · intro h W hW
    rw [Submodule.eq_bot_iff]
    intro x hx
    by_contra hne
    have hlt := h x hne
    have hzero : obsGram A S r x = 0 := by
      rw [obsGram_apply_eq_zero_iff A hS]
      intro j _
      exact (mem_unobservable_iff A S x).mp (le_unobservable_of_isInvariantIn A S hW hx) j
    rw [hzero] at hlt
    simp at hlt
  · intro h x hx
    rcases ((obsGram_isPositive A hS r).re_inner_nonneg_left x).lt_or_eq with hlt | heq
    · exact hlt
    exfalso
    have hzero : obsGram A S r x = 0 := apply_eq_zero_of_re_inner_eq_zero
      (obsGram_isPositive A hS r) heq.symm
    have hmem : x ∈ unobservable A S := by
      rw [← ker_obsGram_eq_unobservable A hS hr, LinearMap.mem_ker]
      exact hzero
    have := h _ (unobservable_isInvariantIn A S)
    rw [this, Submodule.mem_bot] at hmem
    exact hx hmem

/-! ### (H2) ⟺ (H3) for `K = A - S` with `A` skew-adjoint -/

/-- (H3): every eigenvalue of `K` has negative real part. -/
def EigenvaluesNeg (K : E →L[ℂ] E) : Prop :=
  ∀ μ : ℂ, Module.End.HasEigenvalue (K : E →ₗ[ℂ] E) μ → μ.re < 0

omit [FiniteDimensional ℂ E] in
theorem re_inner_skew {A : E →L[ℂ] E} (hA : star A = -A) (x : E) :
    RCLike.re ⟪A x, x⟫_ℂ = 0 := by
  have h1 : (starRingEnd ℂ) ⟪A x, x⟫_ℂ = -⟪A x, x⟫_ℂ := by
    rw [inner_conj_symm, ← adjoint_inner_left, ← star_eq_adjoint, hA, neg_apply, inner_neg_left]
  have := congrArg Complex.re h1
  simp only [Complex.neg_re, Complex.conj_re] at this
  change (⟪A x, x⟫_ℂ).re = 0
  linarith

omit [CompleteSpace E] [FiniteDimensional ℂ E] in
theorem re_eigen_eq {K : E →L[ℂ] E} {μ : ℂ} {v : E} (hv : K v = μ • v) :
    RCLike.re ⟪K v, v⟫_ℂ = μ.re * ‖v‖ ^ 2 := by
  rw [hv, inner_smul_left, ← inner_self_eq_norm_sq (𝕜 := ℂ) v]
  have him : (⟪v, v⟫_ℂ).im = 0 := inner_self_im (𝕜 := ℂ) v
  rw [RCLike.re_to_complex, RCLike.re_to_complex, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    him]
  ring

omit [FiniteDimensional ℂ E] in
/-- **(H2) ⟹ (H3)**. -/
theorem eigenvaluesNeg_of_noInvariant {A S : E →L[ℂ] E} (hA : star A = -A) (hS : S.IsPositive)
    (h : NoInvariant A S) : EigenvaluesNeg (A - S) := by
  intro μ hμ
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hv0 : v ≠ 0 := hv.2
  have hKv : (A - S) v = μ • v := hv.apply_eq_smul
  have hre := re_eigen_eq hKv
  rw [sub_apply, inner_sub_left, map_sub, re_inner_skew hA, zero_sub] at hre
  have hS0 := hS.re_inner_nonneg_left v
  have hvpos : 0 < ‖v‖ ^ 2 := by positivity
  have hle : μ.re ≤ 0 := by nlinarith
  rcases hle.lt_or_eq with hlt | heq
  · exact hlt
  exfalso
  -- `re μ = 0` forces `S v = 0`, so `span {v}` is invariant in `ker S`
  have hSv0 : RCLike.re ⟪S v, v⟫_ℂ = 0 := by rw [heq] at hre; linarith
  have hSv : S v = 0 := apply_eq_zero_of_re_inner_eq_zero hS hSv0
  have hAv : A v = μ • v := by
    have := hKv
    rw [sub_apply, hSv, sub_zero] at this
    exact this
  have hinv : IsInvariantIn A S (Submodule.span ℂ {v}) := by
    refine ⟨fun y hy => ?_, fun y hy => ?_⟩
    · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
      rw [map_smul, hAv, smul_smul]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
    · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
      rw [map_smul, hSv, smul_zero]
  have := h _ hinv
  rw [Submodule.span_singleton_eq_bot] at this
  exact hv0 this

/-- **(H3) ⟹ (H2)**. -/
theorem noInvariant_of_eigenvaluesNeg {A S : E →L[ℂ] E} (hA : star A = -A)
    (h : EigenvaluesNeg (A - S)) : NoInvariant A S := by
  intro W hW
  by_contra hne
  haveI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hne
  -- restrict `A` to `W` and take an eigenvector
  have hmaps : ∀ y ∈ W, (A : E →ₗ[ℂ] E) y ∈ W := fun y hy => hW.1 y hy
  set A' : W →ₗ[ℂ] W := (A : E →ₗ[ℂ] E).restrict hmaps with hA'
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue A'
  obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
  have hw0 : (w : E) ≠ 0 := fun h0 => hw.2 (Subtype.ext h0)
  have hAw : A (w : E) = μ • (w : E) := by
    have := congrArg Subtype.val hw.apply_eq_smul
    simpa [hA', LinearMap.restrict_apply] using this
  have hSw : S (w : E) = 0 := hW.2 _ w.2
  have hKw : (A - S) (w : E) = μ • (w : E) := by rw [sub_apply, hSw, sub_zero, hAw]
  have heig : Module.End.HasEigenvalue ((A - S : E →L[ℂ] E) : E →ₗ[ℂ] E) μ :=
    Module.End.hasEigenvalue_of_hasEigenvector
      ⟨(Module.End.mem_eigenspace_iff).mpr hKw, hw0⟩
  have hneg := h μ heig
  -- but `A` skew forces `re μ = 0`
  have hre := re_eigen_eq (K := A) hAw
  rw [re_inner_skew hA] at hre
  have hvpos : 0 < ‖(w : E)‖ ^ 2 := by positivity
  have : μ.re = 0 := by
    rcases eq_or_ne μ.re 0 with h0 | h0
    · exact h0
    · exfalso
      have := mul_ne_zero h0 hvpos.ne'
      exact this hre.symm
  linarith

/-- **(H2) ⟺ (H3)**. -/
theorem noInvariant_iff_eigenvaluesNeg {A S : E →L[ℂ] E} (hA : star A = -A)
    (hS : S.IsPositive) : NoInvariant A S ↔ EigenvaluesNeg (A - S) :=
  ⟨eigenvaluesNeg_of_noInvariant hA hS, noInvariant_of_eigenvaluesNeg hA⟩

end HypocoerciveMemory
end NCG
