/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# Courant–Fischer min–max values of bounded operators on Hilbert spaces

This file provides the ordered-eigenvalue infrastructure used by the low-spectrum convergence
lemma (`lem:low-spectrum-convergence`) and the compact Mosco resolvent proposition
(`prop:compact-mosco-resolvent`) of the spacetime–gauge duality paper.

For a bounded operator `T` on an inner product space `E` over `𝕜 = ℝ` or `ℂ`, the `k`-th
Courant–Fischer value is

  `courantValue T k = ⨆ (V : finrank V = k + 1), ⨅ (x ∈ V, ‖x‖ = 1), re ⟪T x, x⟫`.

Its key properties are proved directly from the variational formula, without any spectral
theorem:

* one-Lipschitz dependence on the operator, `|courantValue A k - courantValue B k| ≤ ‖A - B‖`
  (`abs_courantValue_sub_le`), hence convergence under operator-norm convergence
  (`tendsto_courantValue`);
* a lower bound from any orthonormal family that is diagonal for `T`
  (`le_courantValue_of_orthonormal`);
* an upper bound from any Rayleigh bound on the orthogonal complement of a subspace of
  dimension at most `k` (`courantValue_le_of_orthogonal_bound`).

The identification of `courantValue T k` with the `k`-th positive eigenvalue of a compact
self-adjoint operator, repeated with multiplicity, is carried out in the second half of the file
(`CompactSelfAdjoint` section).
-/

open Filter Topology RCLike

noncomputable section

namespace RenewalGeometry.CourantFischer

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-! ## Definitions -/

/-- Unit sphere of a submodule, as a subtype. -/
abbrev UnitSphere (V : Submodule 𝕜 E) : Type _ := {x : V // ‖(x : E)‖ = 1}

/-- Infimum of the quadratic form `x ↦ re ⟪T x, x⟫` over the unit sphere of `V`
(with mathlib's convention that the real infimum over an empty index set is `0`). -/
def sphereInf (T : E →L[𝕜] E) (V : Submodule 𝕜 E) : ℝ :=
  ⨅ x : UnitSphere V, re ⟪T ((x : V) : E), ((x : V) : E)⟫

/-- Subspaces of dimension exactly `k + 1`. -/
abbrev SubspaceOfDim (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (k : ℕ) : Type _ :=
  {V : Submodule 𝕜 E // Module.finrank 𝕜 V = k + 1}

/-- The `k`-th Courant–Fischer (min–max) value of `T`: the supremum over all
`(k + 1)`-dimensional subspaces `V` of the infimum of `re ⟪T x, x⟫` over unit vectors of `V`.
For a compact self-adjoint operator this is the `k`-th positive eigenvalue repeated with
multiplicity (zero-indexed), see `courantValue_eq_eigenvalue_multiplicity` below. -/
def courantValue (T : E →L[𝕜] E) (k : ℕ) : ℝ :=
  ⨆ V : SubspaceOfDim 𝕜 E k, sphereInf T (V : Submodule 𝕜 E)

/-! ## Elementary bounds -/

theorem abs_re_inner_apply_self_le (T : E →L[𝕜] E) (x : E) :
    |re ⟪T x, x⟫| ≤ ‖T‖ * ‖x‖ ^ 2 := by
  calc |re ⟪T x, x⟫| ≤ ‖⟪T x, x⟫‖ := abs_re_le_norm _
    _ ≤ ‖T x‖ * ‖x‖ := norm_inner_le_norm _ _
    _ ≤ (‖T‖ * ‖x‖) * ‖x‖ := by gcongr; exact T.le_opNorm x
    _ = ‖T‖ * ‖x‖ ^ 2 := by ring

theorem abs_re_inner_apply_self_le_of_norm_eq_one (T : E →L[𝕜] E) {x : E}
    (hx : ‖x‖ = 1) : |re ⟪T x, x⟫| ≤ ‖T‖ := by
  simpa [hx] using abs_re_inner_apply_self_le T x

theorem re_inner_apply_self_le_of_norm_eq_one (T : E →L[𝕜] E) {x : E}
    (hx : ‖x‖ = 1) : re ⟪T x, x⟫ ≤ ‖T‖ :=
  (le_abs_self _).trans (abs_re_inner_apply_self_le_of_norm_eq_one T hx)

theorem neg_norm_le_re_inner_apply_self_of_norm_eq_one (T : E →L[𝕜] E) {x : E}
    (hx : ‖x‖ = 1) : -‖T‖ ≤ re ⟪T x, x⟫ :=
  neg_le_of_abs_le (abs_re_inner_apply_self_le_of_norm_eq_one T hx)

theorem bddBelow_range_sphere (T : E →L[𝕜] E) (V : Submodule 𝕜 E) :
    BddBelow (Set.range fun x : UnitSphere V ↦ re ⟪T ((x : V) : E), ((x : V) : E)⟫) := by
  refine ⟨-‖T‖, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact neg_norm_le_re_inner_apply_self_of_norm_eq_one T x.2

theorem sphereInf_le_of_mem (T : E →L[𝕜] E) (V : Submodule 𝕜 E) (x : UnitSphere V) :
    sphereInf T V ≤ re ⟪T ((x : V) : E), ((x : V) : E)⟫ :=
  ciInf_le (bddBelow_range_sphere T V) x

theorem le_sphereInf_of_nonneg_of_forall (T : E →L[𝕜] E) (V : Submodule 𝕜 E) {c : ℝ}
    (hc : c ≤ 0) (h : ∀ x : UnitSphere V, c ≤ re ⟪T ((x : V) : E), ((x : V) : E)⟫) :
    c ≤ sphereInf T V :=
  Real.le_iInf h hc

theorem neg_norm_le_sphereInf (T : E →L[𝕜] E) (V : Submodule 𝕜 E) :
    -‖T‖ ≤ sphereInf T V :=
  le_sphereInf_of_nonneg_of_forall T V (neg_nonpos.mpr (norm_nonneg _))
    fun x ↦ neg_norm_le_re_inner_apply_self_of_norm_eq_one T x.2

theorem sphereInf_le_norm (T : E →L[𝕜] E) (V : Submodule 𝕜 E) :
    sphereInf T V ≤ ‖T‖ := by
  rcases isEmpty_or_nonempty (UnitSphere V) with h | h
  · unfold sphereInf
    rw [Real.iInf_of_isEmpty]
    exact norm_nonneg _
  · obtain ⟨x⟩ := h
    exact (sphereInf_le_of_mem T V x).trans
      (re_inner_apply_self_le_of_norm_eq_one T x.2)

theorem bddAbove_range_sphereInf (T : E →L[𝕜] E) (k : ℕ) :
    BddAbove (Set.range fun V : SubspaceOfDim 𝕜 E k ↦ sphereInf T (V : Submodule 𝕜 E)) := by
  refine ⟨‖T‖, ?_⟩
  rintro _ ⟨V, rfl⟩
  exact sphereInf_le_norm T V

theorem sphereInf_le_courantValue (T : E →L[𝕜] E) (k : ℕ) (V : SubspaceOfDim 𝕜 E k) :
    sphereInf T (V : Submodule 𝕜 E) ≤ courantValue T k :=
  le_ciSup (bddAbove_range_sphereInf T k) V

theorem courantValue_le_norm (T : E →L[𝕜] E) (k : ℕ) : courantValue T k ≤ ‖T‖ :=
  Real.iSup_le (fun V ↦ sphereInf_le_norm T V) (norm_nonneg _)

theorem neg_norm_le_courantValue (T : E →L[𝕜] E) (k : ℕ) :
    -‖T‖ ≤ courantValue T k := by
  rcases isEmpty_or_nonempty (SubspaceOfDim 𝕜 E k) with h | h
  · unfold courantValue
    rw [Real.iSup_of_isEmpty]
    exact neg_nonpos.mpr (norm_nonneg _)
  · obtain ⟨V⟩ := h
    exact (neg_norm_le_sphereInf T V).trans (sphereInf_le_courantValue T k V)

theorem courantValue_le_of_forall (T : E →L[𝕜] E) (k : ℕ) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ V : SubspaceOfDim 𝕜 E k, sphereInf T (V : Submodule 𝕜 E) ≤ c) :
    courantValue T k ≤ c :=
  Real.iSup_le h hc

/-- The `k`-th min–max value of a positive operator is nonnegative. -/
theorem courantValue_nonneg_of_isPositive {T : E →L[𝕜] E} (hT : T.IsPositive) (k : ℕ) :
    0 ≤ courantValue T k := by
  rcases isEmpty_or_nonempty (SubspaceOfDim 𝕜 E k) with h | h
  · unfold courantValue
    rw [Real.iSup_of_isEmpty]
  · obtain ⟨V⟩ := h
    refine le_trans ?_ (sphereInf_le_courantValue T k V)
    exact le_sphereInf_of_nonneg_of_forall T V le_rfl fun x ↦ by
      simpa using hT.re_inner_nonneg_left ((x : (V : Submodule 𝕜 E)) : E)

/-! ## Lipschitz dependence on the operator -/

theorem sphereInf_le_sphereInf_add_norm_sub (A B : E →L[𝕜] E) (V : Submodule 𝕜 E) :
    sphereInf A V ≤ sphereInf B V + ‖A - B‖ := by
  rcases isEmpty_or_nonempty (UnitSphere V) with h | h
  · unfold sphereInf
    rw [Real.iInf_of_isEmpty, Real.iInf_of_isEmpty]
    simp
  · refine sub_le_iff_le_add.mp (le_ciInf fun x ↦ ?_)
    have h1 := sphereInf_le_of_mem A V x
    have h2 : re ⟪A ((x : V) : E), ((x : V) : E)⟫ - re ⟪B ((x : V) : E), ((x : V) : E)⟫
        ≤ ‖A - B‖ := by
      have := re_inner_apply_self_le_of_norm_eq_one (A - B) x.2
      simpa [inner_sub_left] using this
    linarith

theorem courantValue_le_courantValue_add_norm_sub (A B : E →L[𝕜] E) (k : ℕ) :
    courantValue A k ≤ courantValue B k + ‖A - B‖ := by
  rcases isEmpty_or_nonempty (SubspaceOfDim 𝕜 E k) with h | h
  · unfold courantValue
    rw [Real.iSup_of_isEmpty, Real.iSup_of_isEmpty]
    simp
  · refine ciSup_le fun V ↦ ?_
    exact (sphereInf_le_sphereInf_add_norm_sub A B V).trans
      (add_le_add (sphereInf_le_courantValue B k V) le_rfl)

/-- One-Lipschitz (Weyl-type) dependence of the min–max values on the operator: this is the
inequality `|μ_{k,X} - μ_{k,∞}| ≤ ‖R_X - R_∞‖` invoked in the proof of
`lem:low-spectrum-convergence`. -/
theorem abs_courantValue_sub_le (A B : E →L[𝕜] E) (k : ℕ) :
    |courantValue A k - courantValue B k| ≤ ‖A - B‖ := by
  have h1 := courantValue_le_courantValue_add_norm_sub A B k
  have h2 := courantValue_le_courantValue_add_norm_sub B A k
  rw [norm_sub_rev] at h2
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

/-- Operator-norm convergence implies convergence of every min–max value. -/
theorem tendsto_courantValue {ι : Type*} {l : Filter ι} {T : ι → E →L[𝕜] E}
    {Tlim : E →L[𝕜] E} (hT : Tendsto T l (𝓝 Tlim)) (k : ℕ) :
    Tendsto (fun i ↦ courantValue (T i) k) l (𝓝 (courantValue Tlim k)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero] at hT ⊢
  refine squeeze_zero (fun i ↦ norm_nonneg _) (fun i ↦ ?_) hT
  rw [Real.norm_eq_abs]
  exact abs_courantValue_sub_le (T i) Tlim k

/-! ## Lower bound from a `T`-diagonal orthonormal family -/

/-- Any orthonormal family `e₀, …, e_k` which is diagonal for `T` (`⟪T e_i, e_j⟫ = 0` for
`i ≠ j`) bounds the `k`-th min–max value from below by `min_i re ⟪T e_i, e_i⟫`. -/
theorem le_courantValue_of_orthonormal (T : E →L[𝕜] E) (k : ℕ) (e : Fin (k + 1) → E)
    (he : Orthonormal 𝕜 e) (hcross : ∀ i j, i ≠ j → ⟪T (e i), e j⟫ = 0)
    (c : ℝ) (hc : ∀ i, c ≤ re ⟪T (e i), e i⟫) :
    c ≤ courantValue T k := by
  classical
  let V : Submodule 𝕜 E := Submodule.span 𝕜 (Set.range e)
  have hV : Module.finrank 𝕜 V = k + 1 := by
    rw [finrank_span_eq_card he.linearIndependent]
    simp
  have hmem : ∀ i, e i ∈ V := fun i ↦ Submodule.subset_span (Set.mem_range_self i)
  have hnorm : ∀ i, ‖e i‖ = 1 := fun i ↦ he.1 i
  have : Nonempty (UnitSphere V) := ⟨⟨⟨e 0, hmem 0⟩, hnorm 0⟩⟩
  refine le_trans ?_ (sphereInf_le_courantValue T k ⟨V, hV⟩)
  refine le_ciInf fun x ↦ ?_
  obtain ⟨l, hl⟩ := Submodule.mem_span_range_iff_exists_fun 𝕜 |>.mp (x : V).2
  have hx1 : ‖((x : V) : E)‖ = 1 := x.2
  -- expand the inner product
  have hinner : ⟪T ((x : V) : E), ((x : V) : E)⟫ =
      ∑ i, (starRingEnd 𝕜) (l i) * (l i * ⟪T (e i), e i⟫) := by
    rw [← hl, map_sum]
    simp only [map_smul]
    rw [sum_inner]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [inner_sum]
    simp only [inner_smul_left, inner_smul_right]
    rw [Finset.sum_eq_single i]
    · ring
    · intro j _ hji
      rw [hcross i j (Ne.symm hji)]
      simp
    · intro h
      exact absurd (Finset.mem_univ i) h
  have hsq : ∑ i, ‖l i‖ ^ 2 = 1 := by
    have h := he.inner_sum l l Finset.univ
    rw [hl, inner_self_eq_norm_sq_to_K, hx1] at h
    have h' := congrArg re h
    simp only [map_sum, RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re, one_pow] at h'
    exact h'.symm
  have hre : re ⟪T ((x : V) : E), ((x : V) : E)⟫ =
      ∑ i, ‖l i‖ ^ 2 * re ⟪T (e i), e i⟫ := by
    rw [hinner, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← mul_assoc, RCLike.conj_mul]
    have : ((‖l i‖ ^ 2 : ℝ) : 𝕜) * ⟪T (e i), e i⟫ = ((‖l i‖ ^ 2 : ℝ) : 𝕜) * ⟪T (e i), e i⟫ := rfl
    rw [show ((‖l i‖ : 𝕜) ^ 2) = ((‖l i‖ ^ 2 : ℝ) : 𝕜) by push_cast; ring]
    exact RCLike.re_ofReal_mul _ _
  rw [hre]
  calc c = ∑ i, ‖l i‖ ^ 2 * c := by rw [← Finset.sum_mul, hsq, one_mul]
    _ ≤ ∑ i, ‖l i‖ ^ 2 * re ⟪T (e i), e i⟫ := by
      refine Finset.sum_le_sum fun i _ ↦ ?_
      exact mul_le_mul_of_nonneg_left (hc i) (sq_nonneg _)

/-! ## Upper bound from a Rayleigh bound on an orthogonal complement -/

/-- If `re ⟪T x, x⟫ ≤ c ‖x‖²` on the orthogonal complement of a subspace of dimension at most
`k`, then the `k`-th min–max value is at most `c` (for `c ≥ 0`; the sign condition only matters
when `E` has dimension at most `k`, where the min–max value is the junk value `0`). -/
theorem courantValue_le_of_orthogonal_bound (T : E →L[𝕜] E) (k : ℕ) (W : Submodule 𝕜 E)
    [FiniteDimensional 𝕜 W] (hW : Module.finrank 𝕜 W ≤ k) (c : ℝ) (hc0 : 0 ≤ c)
    (hc : ∀ x ∈ Wᗮ, re ⟪T x, x⟫ ≤ c * ‖x‖ ^ 2) :
    courantValue T k ≤ c := by
  refine courantValue_le_of_forall T k hc0 fun V ↦ ?_
  have : FiniteDimensional 𝕜 (V : Submodule 𝕜 E) :=
    Module.finite_of_finrank_pos (by rw [V.2]; omega)
  let f : (V : Submodule 𝕜 E) →ₗ[𝕜] W :=
    (W.orthogonalProjectionOnto : E →ₗ[𝕜] W).comp (V : Submodule 𝕜 E).subtype
  have hker : LinearMap.ker f ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by rw [V.2]; omega)
  obtain ⟨x, hxker, hx0⟩ := (Submodule.ne_bot_iff _).mp hker
  have hxW : (x : E) ∈ Wᗮ := by
    have : W.orthogonalProjectionOnto (x : E) = 0 := by
      simpa [f] using hxker
    rw [← Submodule.ker_orthogonalProjectionOnto]
    exact this
  have hxne : ((x : (V : Submodule 𝕜 E)) : E) ≠ 0 := by
    intro h
    exact hx0 (Subtype.ext h)
  let u : (V : Submodule 𝕜 E) := (‖(x : E)‖⁻¹ : 𝕜) • x
  have hu1 : ‖(u : E)‖ = 1 := by
    simp only [u, Submodule.coe_smul]
    exact norm_smul_inv_norm hxne
  have huW : (u : E) ∈ Wᗮ := by
    simp only [u, Submodule.coe_smul]
    exact Wᗮ.smul_mem _ hxW
  refine (sphereInf_le_of_mem T V ⟨u, hu1⟩).trans ?_
  have := hc (u : E) huW
  simpa [hu1] using this

/-! ## Near-antitonicity -/

/-- Every subspace of dimension `k + 2` contains a subspace of dimension `k + 1`. -/
theorem exists_le_finrank_eq_of_finrank_eq_succ (V : Submodule 𝕜 E) (k : ℕ)
    (hV : Module.finrank 𝕜 V = k + 1 + 1) :
    ∃ V' : Submodule 𝕜 E, V' ≤ V ∧ Module.finrank 𝕜 V' = k + 1 := by
  classical
  have : FiniteDimensional 𝕜 V := Module.finite_of_finrank_pos (by omega)
  let b := Module.finBasisOfFinrankEq 𝕜 V hV
  let e : Fin (k + 1) → E := fun i ↦ (b (Fin.castSucc i) : E)
  have he : LinearIndependent 𝕜 e := by
    have h1 : LinearIndependent 𝕜 (fun i : Fin (k + 1) ↦ b (Fin.castSucc i)) :=
      b.linearIndependent.comp _ (Fin.castSucc_injective _)
    exact h1.map' V.subtype V.ker_subtype
  refine ⟨Submodule.span 𝕜 (Set.range e), ?_, ?_⟩
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact (b (Fin.castSucc i)).2
  · rw [finrank_span_eq_card he]
    simp

theorem sphereInf_le_sphereInf_of_le (T : E →L[𝕜] E) {V' V : Submodule 𝕜 E} (hle : V' ≤ V)
    [Nonempty (UnitSphere V')] :
    sphereInf T V ≤ sphereInf T V' := by
  refine le_ciInf fun x ↦ ?_
  exact sphereInf_le_of_mem T V ⟨⟨(x : V'), hle (x : V').2⟩, x.2⟩

/-- The min–max values are antitone as long as the index set of `(k + 2)`-dimensional
subspaces is nonempty; in general `courantValue T (k + 1) ≤ max (courantValue T k) 0`. -/
theorem courantValue_succ_le_max (T : E →L[𝕜] E) (k : ℕ) :
    courantValue T (k + 1) ≤ max (courantValue T k) 0 := by
  refine courantValue_le_of_forall T (k + 1) (le_max_right _ _) fun V ↦ ?_
  obtain ⟨V', hle, hV'⟩ := exists_le_finrank_eq_of_finrank_eq_succ (V : Submodule 𝕜 E) k V.2
  have : FiniteDimensional 𝕜 V' := Module.finite_of_finrank_pos (by omega)
  have : Nonempty (UnitSphere V') := by
    have hne : V' ≠ ⊥ := by
      intro h
      rw [h, finrank_bot] at hV'
      omega
    obtain ⟨x, hxV', hx0⟩ := (Submodule.ne_bot_iff _).mp hne
    exact ⟨⟨⟨(‖x‖⁻¹ : 𝕜) • x, V'.smul_mem _ hxV'⟩, norm_smul_inv_norm hx0⟩⟩
  refine (sphereInf_le_sphereInf_of_le T hle).trans ?_
  exact (sphereInf_le_courantValue T k ⟨V', hV'⟩).trans (le_max_left _ _)

theorem courantValue_succ_le_of_pos (T : E →L[𝕜] E) (k : ℕ)
    (hpos : 0 < courantValue T (k + 1)) :
    courantValue T (k + 1) ≤ courantValue T k := by
  have h := courantValue_succ_le_max T k
  rcases le_or_gt 0 (courantValue T k) with h0 | h0
  · rwa [max_eq_left h0] at h
  · rw [max_eq_right h0.le] at h
    linarith

/-- For a positive operator the min–max values are antitone in `k`. -/
theorem courantValue_antitone_of_isPositive {T : E →L[𝕜] E} (hT : T.IsPositive) :
    Antitone (courantValue T) := by
  refine antitone_nat_of_succ_le fun k ↦ ?_
  have h := courantValue_succ_le_max T k
  rwa [max_eq_left (courantValue_nonneg_of_isPositive hT k)] at h

/-! ## Compact self-adjoint operators: the top eigenvector

The following results do not use any spectral theorem.  A positive operator `P` satisfies the
generalised Cauchy–Schwarz inequality `‖P x‖² ≤ ‖P‖ re ⟪P x, x⟫`; applied to `P = M - S`, it
shows that any sequence of unit vectors almost maximising the Rayleigh quotient of a compact
symmetric `S` is almost an eigenvector sequence, and compactness extracts an eigenvector. -/

section CompactSelfAdjoint

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- Generalised Cauchy–Schwarz inequality for a symmetric operator with nonnegative quadratic
form: `‖P x‖ ^ 2 ≤ ‖P‖ * re ⟪P x, x⟫`. -/
theorem norm_apply_sq_le_of_symmetric_of_nonneg (P : F →L[𝕜] F)
    (hsymm : LinearMap.IsSymmetric (P : F →ₗ[𝕜] F)) (hpos : ∀ x, 0 ≤ re ⟪P x, x⟫) (x : F) :
    ‖P x‖ ^ 2 ≤ ‖P‖ * re ⟪P x, x⟫ := by
  have hsymm' : ∀ x y : F, ⟪P x, y⟫ = ⟪x, P y⟫ := fun x y ↦ hsymm x y
  -- the semi-inner product `(x, y) ↦ ⟪P x, y⟫`
  let c : PreInnerProductSpace.Core 𝕜 F :=
    { inner := fun x y ↦ ⟪P x, y⟫
      conj_inner_symm := fun x y ↦ by
        rw [inner_conj_symm]
        exact (hsymm' x y).symm
      re_inner_nonneg := hpos
      add_left := fun x y z ↦ by
        rw [map_add, inner_add_left]
      smul_left := fun x y r ↦ by
        rw [map_smul, inner_smul_left] }
  have hcs : ‖⟪P x, P x⟫‖ * ‖⟪P (P x), x⟫‖ ≤ re ⟪P x, x⟫ * re ⟪P (P x), P x⟫ :=
    @InnerProductSpace.Core.inner_mul_inner_self_le 𝕜 F _ _ _ c x (P x)
  have h1 : ‖⟪P x, P x⟫‖ = ‖P x‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal, abs_norm]
  have h2 : ‖⟪P (P x), x⟫‖ = ‖P x‖ ^ 2 := by
    rw [hsymm' (P x) x, h1]
  have h3 : re ⟪P (P x), P x⟫ ≤ ‖P‖ * ‖P x‖ ^ 2 := by
    calc re ⟪P (P x), P x⟫ ≤ ‖P (P x)‖ * ‖P x‖ := re_inner_le_norm _ _
      _ ≤ (‖P‖ * ‖P x‖) * ‖P x‖ := by gcongr; exact P.le_opNorm _
      _ = ‖P‖ * ‖P x‖ ^ 2 := by ring
  rw [h1, h2] at hcs
  have hPxx := hpos x
  by_cases hzero : ‖P x‖ = 0
  · rw [hzero]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    exact mul_nonneg (norm_nonneg _) hPxx
  · have hpos' : 0 < ‖P x‖ ^ 2 := by positivity
    have : ‖P x‖ ^ 2 * ‖P x‖ ^ 2 ≤ (‖P‖ * re ⟪P x, x⟫) * ‖P x‖ ^ 2 := by
      calc ‖P x‖ ^ 2 * ‖P x‖ ^ 2 ≤ re ⟪P x, x⟫ * re ⟪P (P x), P x⟫ := hcs
        _ ≤ re ⟪P x, x⟫ * (‖P‖ * ‖P x‖ ^ 2) := by gcongr
        _ = (‖P‖ * re ⟪P x, x⟫) * ‖P x‖ ^ 2 := by ring
    exact le_of_mul_le_mul_right this hpos'

variable [CompleteSpace F]

/-- **Existence of a top eigenvector.**  Let `S` be a compact symmetric operator on a Hilbert
space, `M > 0` an upper bound of its quadratic form on the unit sphere which is approached by
unit vectors.  Then `M` is an eigenvalue of `S` with a unit eigenvector. -/
theorem exists_unit_eigenvector_of_sup_rayleigh (S : F →L[𝕜] F)
    (hsymm : LinearMap.IsSymmetric (S : F →ₗ[𝕜] F)) (hc : IsCompactOperator S)
    (M : ℝ) (hM : 0 < M) (hle : ∀ x, re ⟪S x, x⟫ ≤ M * ‖x‖ ^ 2)
    (happrox : ∀ ε > 0, ∃ x : F, ‖x‖ = 1 ∧ M - ε < re ⟪S x, x⟫) :
    ∃ e : F, ‖e‖ = 1 ∧ S e = (M : 𝕜) • e := by
  have hsymm' : ∀ x y : F, ⟪S x, y⟫ = ⟪x, S y⟫ := fun x y ↦ hsymm x y
  -- the maximising sequence
  have hseq : ∀ n : ℕ, ∃ x : F, ‖x‖ = 1 ∧ M - 1 / ((n : ℝ) + 1) < re ⟪S x, x⟫ :=
    fun n ↦ happrox _ (by positivity)
  choose x hx1 hxM using hseq
  have hlim : Tendsto (fun n ↦ re ⟪S (x n), x n⟫) atTop (𝓝 M) := by
    have hupper : ∀ n, re ⟪S (x n), x n⟫ ≤ M := fun n ↦ by
      simpa [hx1 n] using hle (x n)
    have hlow : Tendsto (fun n : ℕ ↦ M - 1 / ((n : ℝ) + 1)) atTop (𝓝 M) := by
      have h : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      simpa using tendsto_const_nhds.sub h
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
      (fun n ↦ (hxM n).le) hupper
  -- the positive operator `P = M - S`
  let P : F →L[𝕜] F := (M : 𝕜) • (1 : F →L[𝕜] F) - S
  have hP : ∀ y, P y = (M : 𝕜) • y - S y := fun y ↦ by simp [P]
  have hPsymm : LinearMap.IsSymmetric (P : F →ₗ[𝕜] F) := by
    intro y z
    simp only [ContinuousLinearMap.coe_coe, hP, inner_sub_left, inner_sub_right,
      inner_smul_left, inner_smul_right, RCLike.conj_ofReal]
    rw [hsymm' y z]
  have hPre : ∀ y, re ⟪P y, y⟫ = M * ‖y‖ ^ 2 - re ⟪S y, y⟫ := fun y ↦ by
    simp only [hP, inner_sub_left, inner_smul_left, RCLike.conj_ofReal, map_sub,
      inner_self_eq_norm_sq_to_K]
    simp
  have hPpos : ∀ y, 0 ≤ re ⟪P y, y⟫ := fun y ↦ by
    rw [hPre]
    linarith [hle y]
  -- `P (x n) → 0`
  have hPx : Tendsto (fun n ↦ P (x n)) atTop (𝓝 0) := by
    have hsq : Tendsto (fun n ↦ ‖P (x n)‖ ^ 2) atTop (𝓝 0) := by
      have hbound : ∀ n, ‖P (x n)‖ ^ 2 ≤ ‖P‖ * (M - re ⟪S (x n), x n⟫) := fun n ↦ by
        have := norm_apply_sq_le_of_symmetric_of_nonneg P hPsymm hPpos (x n)
        rwa [hPre, hx1 n, one_pow, mul_one] at this
      have hrhs : Tendsto (fun n ↦ ‖P‖ * (M - re ⟪S (x n), x n⟫)) atTop (𝓝 0) := by
        have := (tendsto_const_nhds (x := M)).sub hlim
        simpa using this.const_mul ‖P‖
      exact squeeze_zero (fun n ↦ sq_nonneg _) hbound hrhs
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have := (Real.continuous_sqrt.tendsto 0).comp hsq
    simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using this
  -- compactness: a convergent subsequence of `S (x n)`
  obtain ⟨K, hK, hSK⟩ :=
    IsCompactOperator.image_closedBall_subset_compact (f := (S : F →ₗ[𝕜] F)) hc 1
  have hmemK : ∀ n, S (x n) ∈ K := fun n ↦
    hSK ⟨x n, by simp [hx1 n], rfl⟩
  obtain ⟨y, -, φ, hφ, hy⟩ := hK.tendsto_subseq hmemK
  -- `M • x (φ n) → y`, hence `x (φ n) → M⁻¹ • y`
  have hMx : Tendsto (fun n ↦ (M : 𝕜) • x (φ n)) atTop (𝓝 y) := by
    have h := hy.add (hPx.comp hφ.tendsto_atTop)
    simp only [add_zero] at h
    refine h.congr fun n ↦ ?_
    simp [hP]
  have hMne : (M : 𝕜) ≠ 0 := by
    exact_mod_cast hM.ne'
  set e : F := (M : 𝕜)⁻¹ • y with he
  have hxe : Tendsto (fun n ↦ x (φ n)) atTop (𝓝 e) := by
    have h := hMx.const_smul (M : 𝕜)⁻¹
    refine h.congr fun n ↦ ?_
    rw [smul_smul, inv_mul_cancel₀ hMne, one_smul]
  refine ⟨e, ?_, ?_⟩
  · have h1 : Tendsto (fun n ↦ ‖x (φ n)‖) atTop (𝓝 ‖e‖) := hxe.norm
    have h2 : Tendsto (fun n ↦ ‖x (φ n)‖) atTop (𝓝 1) := by
      simp only [hx1]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique h1 h2
  · have h1 : Tendsto (fun n ↦ S (x (φ n))) atTop (𝓝 (S e)) :=
      (S.continuous.tendsto e).comp hxe
    have h2 : S e = y := tendsto_nhds_unique h1 hy
    rw [h2, he, smul_smul, mul_inv_cancel₀ hMne, one_smul]

/-- A symmetric operator preserving a subspace preserves its orthogonal complement. -/
theorem apply_mem_orthogonal_of_isSymmetric (T : F →L[𝕜] F)
    (hsymm : LinearMap.IsSymmetric (T : F →ₗ[𝕜] F)) (W : Submodule 𝕜 F)
    (hW : ∀ w ∈ W, T w ∈ W) {x : F} (hx : x ∈ Wᗮ) : T x ∈ Wᗮ := by
  have hsymm' : ∀ x y : F, ⟪T x, y⟫ = ⟪x, T y⟫ := fun x y ↦ hsymm x y
  rw [Submodule.mem_orthogonal] at hx ⊢
  intro u hu
  rw [← hsymm' u x]
  exact hx (T u) (hW u hu)

/-! ### Orthonormal eigenvector families -/

omit [CompleteSpace F] in
theorem re_inner_apply_self_of_eigen {T : F →L[𝕜] F} {v : F} {μ : ℝ}
    (hv : T v = (μ : 𝕜) • v) (hv1 : ‖v‖ = 1) : re ⟪T v, v⟫ = μ := by
  rw [hv, inner_smul_left, inner_self_eq_norm_sq_to_K, hv1]
  simp

omit [CompleteSpace F] in
theorem inner_apply_eq_zero_of_orthonormal_of_eigen {T : F →L[𝕜] F} {m : ℕ} {e : Fin m → F}
    (he : Orthonormal 𝕜 e) {μ : Fin m → ℝ} (heig : ∀ i, T (e i) = (μ i : 𝕜) • e i)
    {i j : Fin m} (hij : i ≠ j) : ⟪T (e i), e j⟫ = 0 := by
  classical
  rw [heig i, inner_smul_left, orthonormal_iff_ite.mp he i j, if_neg hij, mul_zero]

omit [CompleteSpace F] in
/-- Scaling of the quadratic form by a real scalar. -/
theorem re_inner_apply_self_real_smul (T : F →L[𝕜] F) (r : ℝ) (x : F) :
    re ⟪T ((r : 𝕜) • x), (r : 𝕜) • x⟫ = r ^ 2 * re ⟪T x, x⟫ := by
  rw [map_smul, inner_smul_left, inner_smul_right, RCLike.conj_ofReal, ← mul_assoc,
    ← RCLike.ofReal_mul, ← sq, RCLike.re_ofReal_mul]

omit [CompleteSpace F] in
/-- A bound of the quadratic form on unit vectors of a subspace extends to all its vectors. -/
theorem re_inner_apply_self_le_mul_of_forall_unit (T : F →L[𝕜] F) (C : Submodule 𝕜 F) (c : ℝ)
    (h : ∀ u ∈ C, ‖u‖ = 1 → re ⟪T u, u⟫ ≤ c) {x : F} (hx : x ∈ C) :
    re ⟪T x, x⟫ ≤ c * ‖x‖ ^ 2 := by
  by_cases hx0 : x = 0
  · subst hx0
    simp
  · have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have hu := h ((‖x‖⁻¹ : 𝕜) • x) (C.smul_mem _ hx) (norm_smul_inv_norm hx0)
    rw [← RCLike.ofReal_inv, re_inner_apply_self_real_smul] at hu
    have hpos : 0 < ‖x‖ ^ 2 := by positivity
    calc re ⟪T x, x⟫ = ‖x‖ ^ 2 * (‖x‖⁻¹ ^ 2 * re ⟪T x, x⟫) := by
          field_simp
      _ ≤ ‖x‖ ^ 2 * c := by gcongr
      _ = c * ‖x‖ ^ 2 := by ring

omit [CompleteSpace F] in
/-- Appending a unit vector orthogonal to the span keeps a family orthonormal. -/
theorem orthonormal_snoc {m : ℕ} {e : Fin m → F} (he : Orthonormal 𝕜 e) {v : F}
    (hv1 : ‖v‖ = 1) (hv : v ∈ (Submodule.span 𝕜 (Set.range e))ᗮ) :
    Orthonormal 𝕜 (Fin.snoc e v : Fin (m + 1) → F) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  have hmem : ∀ i, e i ∈ Submodule.span 𝕜 (Set.range e) := fun i ↦
    Submodule.subset_span (Set.mem_range_self i)
  refine Fin.lastCases ?_ (fun i' ↦ ?_) i
  · refine Fin.lastCases ?_ (fun j' ↦ ?_) j
    · simp [Fin.snoc_last, inner_self_eq_norm_sq_to_K, hv1]
    · rw [Fin.snoc_last, Fin.snoc_castSucc, if_neg (Fin.castSucc_lt_last j').ne']
      exact Submodule.inner_left_of_mem_orthogonal (hmem j') hv
  · refine Fin.lastCases ?_ (fun j' ↦ ?_) j
    · rw [Fin.snoc_last, Fin.snoc_castSucc, if_neg (Fin.castSucc_lt_last i').ne]
      exact Submodule.inner_right_of_mem_orthogonal (hmem i') hv
    · rw [Fin.snoc_castSucc, Fin.snoc_castSucc, orthonormal_iff_ite.mp he i' j']
      simp [Fin.castSucc_inj]

omit [CompleteSpace F] in
/-- The span of a family of eigenvectors is invariant. -/
theorem apply_mem_span_of_eigen {T : F →L[𝕜] F} {m : ℕ} {e : Fin m → F} {μ : Fin m → ℝ}
    (heig : ∀ i, T (e i) = (μ i : 𝕜) • e i) {w : F}
    (hw : w ∈ Submodule.span 𝕜 (Set.range e)) : T w ∈ Submodule.span 𝕜 (Set.range e) := by
  have hle : Submodule.map (T : F →ₗ[𝕜] F) (Submodule.span 𝕜 (Set.range e)) ≤
      Submodule.span 𝕜 (Set.range e) := by
    rw [Submodule.map_span_le]
    rintro _ ⟨i, rfl⟩
    change T (e i) ∈ _
    rw [heig i]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
  exact hle (Submodule.mem_map_of_mem hw)

omit [CompleteSpace F] in
/-- Monotonicity of the min–max values along a run of positive values. -/
theorem courantValue_le_courantValue_of_le_of_pos (T : F →L[𝕜] F) {i j : ℕ} (hij : i ≤ j)
    (hpos : 0 < courantValue T j) : courantValue T j ≤ courantValue T i := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih =>
    have h1 := courantValue_succ_le_of_pos T j hpos
    exact h1.trans (ih (lt_of_lt_of_le hpos h1))

omit [CompleteSpace F] in
/-- **Key variational step.**  Let `e₀, …, e_{m-1}` be orthonormal eigenvectors with real
eigenvalues `μ_i`, and `u` a unit vector orthogonal to their span whose Rayleigh quotient is
at most every `μ_i`.  Then `re ⟪T u, u⟫ ≤ courantValue T m`. -/
theorem re_inner_apply_self_le_courantValue_of_mem_orthogonal (T : F →L[𝕜] F)
    (hsymm : LinearMap.IsSymmetric (T : F →ₗ[𝕜] F)) {m : ℕ} {e : Fin m → F}
    (he : Orthonormal 𝕜 e) {μ : Fin m → ℝ} (heig : ∀ i, T (e i) = (μ i : 𝕜) • e i)
    {u : F} (hu1 : ‖u‖ = 1) (hu : u ∈ (Submodule.span 𝕜 (Set.range e))ᗮ)
    (hle : ∀ i, re ⟪T u, u⟫ ≤ μ i) :
    re ⟪T u, u⟫ ≤ courantValue T m := by
  classical
  have hsymm' : ∀ x y : F, ⟪T x, y⟫ = ⟪x, T y⟫ := fun x y ↦ hsymm x y
  have hmem : ∀ i, e i ∈ Submodule.span 𝕜 (Set.range e) := fun i ↦
    Submodule.subset_span (Set.mem_range_self i)
  let e' : Fin (m + 1) → F := Fin.snoc e u
  have he' : Orthonormal 𝕜 e' := orthonormal_snoc he hu1 hu
  refine le_courantValue_of_orthonormal T m e' he' ?_ (re ⟪T u, u⟫) ?_
  · intro i j hij
    refine Fin.lastCases ?_ (fun i' ↦ ?_) i hij
    · refine Fin.lastCases ?_ (fun j' ↦ ?_) j
      · intro h
        exact absurd rfl h
      · intro _
        simp only [e', Fin.snoc_last, Fin.snoc_castSucc]
        rw [hsymm' u (e j'), heig j', inner_smul_right,
          Submodule.inner_left_of_mem_orthogonal (hmem j') hu, mul_zero]
    · refine Fin.lastCases ?_ (fun j' ↦ ?_) j
      · intro _
        simp only [e', Fin.snoc_last, Fin.snoc_castSucc]
        rw [heig i', inner_smul_left, Submodule.inner_right_of_mem_orthogonal (hmem i') hu,
          mul_zero]
      · intro hij'
        simp only [e', Fin.snoc_castSucc]
        exact inner_apply_eq_zero_of_orthonormal_of_eigen he heig
          (fun h ↦ hij' (by rw [h]))
  · intro i
    refine Fin.lastCases ?_ (fun i' ↦ ?_) i
    · simp [e', Fin.snoc_last]
    · simp only [e', Fin.snoc_castSucc]
      rw [re_inner_apply_self_of_eigen (heig i') (he.1 i')]
      exact hle i'

/-- **Greedy orthonormal eigenvector family.**  For a compact symmetric operator `T` whose
first `n` min–max values are positive, there is an orthonormal family `e₀, …, e_{n-1}` of
eigenvectors, `T e_i = courantValue T i • e_i`, such that the quadratic form is bounded by
`courantValue T n` on the orthogonal complement of their span. -/
theorem exists_orthonormal_eigenvectors (T : F →L[𝕜] F)
    (hsymm : LinearMap.IsSymmetric (T : F →ₗ[𝕜] F)) (hc : IsCompactOperator T) (n : ℕ)
    (hpos : ∀ i < n, 0 < courantValue T i) :
    ∃ e : Fin n → F, Orthonormal 𝕜 e ∧
      (∀ i : Fin n, T (e i) = ((courantValue T i : ℝ) : 𝕜) • e i) ∧
      ∀ x ∈ (Submodule.span 𝕜 (Set.range e))ᗮ,
        re ⟪T x, x⟫ ≤ courantValue T n * ‖x‖ ^ 2 := by
  classical
  induction n with
  | zero =>
    refine ⟨fun i ↦ i.elim0, orthonormal_iff_ite.mpr fun i ↦ i.elim0, fun i ↦ i.elim0, ?_⟩
    intro x hx
    refine re_inner_apply_self_le_mul_of_forall_unit T _ _ (fun u hu hu1 ↦ ?_) hx
    exact re_inner_apply_self_le_courantValue_of_mem_orthogonal T hsymm
      (orthonormal_iff_ite.mpr fun i ↦ i.elim0) (μ := fun i ↦ i.elim0) (fun i ↦ i.elim0)
      hu1 hu (fun i ↦ i.elim0)
  | succ n ih =>
    obtain ⟨e, he, heig, hclause⟩ := ih fun i hi ↦ hpos i (by omega)
    have hMpos : 0 < courantValue T n := hpos n (by omega)
    set W : Submodule 𝕜 F := Submodule.span 𝕜 (Set.range e) with hWdef
    have hWinv : ∀ w ∈ W, T w ∈ W := fun w hw ↦ apply_mem_span_of_eigen heig hw
    have hinv : ∀ v ∈ Wᗮ, T v ∈ Wᗮ := fun v hv ↦
      apply_mem_orthogonal_of_isSymmetric T hsymm W hWinv hv
    have : FiniteDimensional 𝕜 W := Module.Finite.span_of_finite 𝕜 (Set.finite_range e)
    have hWrank : Module.finrank 𝕜 W = n := by
      rw [hWdef, finrank_span_eq_card he.linearIndependent]
      simp
    -- restriction of `T` to the orthogonal complement
    let S : Wᗮ →L[𝕜] Wᗮ := T.restrict hinv
    have hS : ∀ z : Wᗮ, (S z : F) = T z := fun z ↦ rfl
    have hSsymm : LinearMap.IsSymmetric (S : Wᗮ →ₗ[𝕜] Wᗮ) := by
      intro z w
      simp only [ContinuousLinearMap.coe_coe, Submodule.coe_inner, hS]
      exact hsymm (z : F) (w : F)
    have hScompact : IsCompactOperator S := hc.restrict' hinv
    have hSle : ∀ z : Wᗮ, re ⟪S z, z⟫ ≤ courantValue T n * ‖z‖ ^ 2 := fun z ↦ by
      rw [Submodule.coe_inner, hS]
      exact hclause (z : F) z.2
    have hSapprox : ∀ ε > 0, ∃ z : Wᗮ, ‖z‖ = 1 ∧ courantValue T n - ε < re ⟪S z, z⟫ := by
      intro ε hε
      by_contra hcon
      have hcon' : ∀ z : Wᗮ, ‖z‖ = 1 → re ⟪S z, z⟫ ≤ courantValue T n - ε := fun z hz ↦ by
        by_contra h
        exact hcon ⟨z, hz, lt_of_not_ge h⟩
      have hbound : ∀ x ∈ Wᗮ, re ⟪T x, x⟫ ≤ max (courantValue T n - ε) 0 * ‖x‖ ^ 2 := by
        intro x hx
        refine re_inner_apply_self_le_mul_of_forall_unit T Wᗮ _ (fun u hu hu1 ↦ ?_) hx
        have := hcon' ⟨u, hu⟩ hu1
        rw [Submodule.coe_inner, hS] at this
        exact this.trans (le_max_left _ _)
      have h1 := courantValue_le_of_orthogonal_bound T n W hWrank.le _ (le_max_right _ _) hbound
      have h2 : max (courantValue T n - ε) 0 < courantValue T n :=
        max_lt (by linarith) hMpos
      exact absurd h1 (not_le.mpr h2)
    obtain ⟨v, hv1, hSv⟩ := exists_unit_eigenvector_of_sup_rayleigh S hSsymm hScompact
      (courantValue T n) hMpos hSle hSapprox
    have hvE : T (v : F) = ((courantValue T n : ℝ) : 𝕜) • (v : F) := by
      have := congrArg Subtype.val hSv
      simpa [hS] using this
    have hvW : (v : F) ∈ Wᗮ := v.2
    have hv1' : ‖(v : F)‖ = 1 := hv1
    -- the extended family
    let e' : Fin (n + 1) → F := Fin.snoc e (v : F)
    have he' : Orthonormal 𝕜 e' := orthonormal_snoc he hv1' hvW
    have heig' : ∀ i : Fin (n + 1), T (e' i) = ((courantValue T i : ℝ) : 𝕜) • e' i := by
      intro i
      refine Fin.lastCases ?_ (fun i' ↦ ?_) i
      · simpa [e', Fin.snoc_last] using hvE
      · simpa [e', Fin.snoc_castSucc] using heig i'
    refine ⟨e', he', heig', ?_⟩
    have hspan : W ≤ Submodule.span 𝕜 (Set.range e') := by
      refine Submodule.span_mono ?_
      rintro _ ⟨i, rfl⟩
      exact ⟨i.castSucc, by simp [e', Fin.snoc_castSucc]⟩
    intro x hx
    refine re_inner_apply_self_le_mul_of_forall_unit T _ _ (fun u hu hu1 ↦ ?_) hx
    have huW : u ∈ Wᗮ := Submodule.orthogonal_le hspan hu
    have hun : re ⟪T u, u⟫ ≤ courantValue T n := by
      simpa [hu1] using hclause u huW
    refine re_inner_apply_self_le_courantValue_of_mem_orthogonal T hsymm he'
      (μ := fun i ↦ courantValue T i) heig' hu1 hu fun i ↦ ?_
    exact hun.trans (courantValue_le_courantValue_of_le_of_pos T (by omega) hMpos)

/-! ### Finiteness of the positive part -/

/-- Compactness bounds the size of every orthonormal family of eigenvectors with eigenvalues
at least `lam > 0`. -/
theorem exists_bound_card_orthonormal_eigenvectors (T : F →L[𝕜] F)
    (hc : IsCompactOperator T) (lam : ℝ) (hlam : 0 < lam) :
    ∃ N : ℕ, ∀ (m : ℕ) (e : Fin m → F) (μ : Fin m → ℝ), Orthonormal 𝕜 e →
      (∀ i, T (e i) = (μ i : 𝕜) • e i) → (∀ i, lam ≤ μ i) → m ≤ N := by
  classical
  have hK : IsCompact (closure (T '' Metric.closedBall 0 1)) :=
    IsCompactOperator.isCompact_closure_image_closedBall (f := (T : F →ₗ[𝕜] F)) hc 1
  obtain ⟨t, htfin, hcover⟩ :=
    Metric.totallyBounded_iff.mp hK.totallyBounded (lam / 2) (by positivity)
  refine ⟨htfin.toFinset.card, ?_⟩
  intro m e μ he heig hμ
  by_contra hm
  replace hm := not_le.mp hm
  have hex : ∀ i, ∃ y ∈ t, T (e i) ∈ Metric.ball y (lam / 2) := by
    intro i
    have hmem : T (e i) ∈ closure (T '' Metric.closedBall 0 1) :=
      subset_closure ⟨e i, by simp [he.1 i], rfl⟩
    have := hcover hmem
    simpa only [Set.mem_iUnion, exists_prop] using this
  choose y hyt hy using hex
  let f : Fin m → {z // z ∈ htfin.toFinset} := fun i ↦ ⟨y i, htfin.mem_toFinset.mpr (hyt i)⟩
  obtain ⟨i, j, hij, hfij⟩ := Fintype.exists_ne_map_eq_of_card_lt f (by simpa using hm)
  have hyij : y i = y j := by
    have := congrArg Subtype.val hfij
    simpa [f] using this
  have hdist : dist (T (e i)) (T (e j)) < lam := by
    calc dist (T (e i)) (T (e j)) ≤ dist (T (e i)) (y i) + dist (y i) (T (e j)) :=
          dist_triangle _ _ _
      _ < lam / 2 + lam / 2 := by
          gcongr
          · exact hy i
          · rw [hyij, dist_comm]
            exact hy j
      _ = lam := by ring
  have hsq : ‖T (e i) - T (e j)‖ ^ 2 = μ i ^ 2 + μ j ^ 2 := by
    rw [heig i, heig j, norm_sub_sq (𝕜 := 𝕜), inner_smul_left, inner_smul_right,
      orthonormal_iff_ite.mp he i j, if_neg hij, norm_smul, norm_smul,
      RCLike.norm_ofReal, RCLike.norm_ofReal, he.1 i, he.1 j]
    simp [sq_abs]
  rw [dist_eq_norm] at hdist
  have hd0 : 0 ≤ ‖T (e i) - T (e j)‖ := norm_nonneg _
  have hμi := hμ i
  have hμj := hμ j
  nlinarith [mul_pos hlam hlam, sq_nonneg (μ i - lam), sq_nonneg (μ j - lam)]

/-- Beyond some index, all min–max values of a compact symmetric operator are below any fixed
`lam > 0`. -/
theorem exists_forall_courantValue_lt (T : F →L[𝕜] F)
    (hsymm : LinearMap.IsSymmetric (T : F →ₗ[𝕜] F)) (hc : IsCompactOperator T)
    (lam : ℝ) (hlam : 0 < lam) :
    ∃ N : ℕ, ∀ k, N ≤ k → courantValue T k < lam := by
  obtain ⟨N, hN⟩ := exists_bound_card_orthonormal_eigenvectors T hc lam hlam
  refine ⟨N, fun k hk ↦ ?_⟩
  by_contra hcon
  have hlamk : lam ≤ courantValue T k := not_lt.mp hcon
  have hposk : 0 < courantValue T k := hlam.trans_le hlamk
  have hpos : ∀ i < k + 1, 0 < courantValue T i := fun i hi ↦
    hposk.trans_le (courantValue_le_courantValue_of_le_of_pos T (by omega) hposk)
  obtain ⟨e, he, heig, -⟩ := exists_orthonormal_eigenvectors T hsymm hc (k + 1) hpos
  have := hN (k + 1) e (fun i ↦ courantValue T i) he heig fun i ↦
    hlamk.trans (courantValue_le_courantValue_of_le_of_pos T (by omega) hposk)
  omega

/-- The set of indices at which the min–max value equals a given `lam > 0` is finite. -/
theorem finite_setOf_courantValue_eq (T : F →L[𝕜] F)
    (hsymm : LinearMap.IsSymmetric (T : F →ₗ[𝕜] F)) (hc : IsCompactOperator T)
    (lam : ℝ) (hlam : 0 < lam) : {k : ℕ | courantValue T k = lam}.Finite := by
  obtain ⟨N, hN⟩ := exists_forall_courantValue_lt T hsymm hc lam hlam
  refine (Set.finite_lt_nat N).subset fun k hk ↦ ?_
  by_contra h
  have := hN k (not_lt.mp h)
  rw [Set.mem_setOf_eq] at hk
  linarith

/-- The indices with `lam ≤ courantValue T k` form an initial segment `{0, …, n - 1}`. -/
theorem exists_initial_segment (T : F →L[𝕜] F)
    (hsymm : LinearMap.IsSymmetric (T : F →ₗ[𝕜] F)) (hc : IsCompactOperator T)
    (lam : ℝ) (hlam : 0 < lam) :
    ∃ n : ℕ, (∀ k < n, lam ≤ courantValue T k) ∧ ∀ k, n ≤ k → courantValue T k < lam := by
  classical
  obtain ⟨N, hN⟩ := exists_forall_courantValue_lt T hsymm hc lam hlam
  have hex : ∃ n, courantValue T n < lam := ⟨N, hN N le_rfl⟩
  refine ⟨Nat.find hex, fun k hk ↦ not_lt.mp (Nat.find_min hex hk), fun k hk ↦ ?_⟩
  by_contra hcon
  have hlamk : lam ≤ courantValue T k := not_lt.mp hcon
  have hposk : 0 < courantValue T k := hlam.trans_le hlamk
  have := courantValue_le_courantValue_of_le_of_pos T hk hposk
  have := Nat.find_spec hex
  linarith

/-! ### Multiplicities -/

/-- **Multiplicity theorem.**  For a compact symmetric operator `T` and `lam > 0`, the number
of indices `k` with `courantValue T k = lam` equals the dimension of the `lam`-eigenspace.
Together with `courantValue_antitone_of_isPositive` this identifies the min–max values of a
compact positive operator with its positive eigenvalues enumerated in decreasing order and
repeated with multiplicity. -/
theorem finrank_eigenspace_eq_ncard (T : F →L[𝕜] F)
    (hsymm : LinearMap.IsSymmetric (T : F →ₗ[𝕜] F)) (hc : IsCompactOperator T)
    (lam : ℝ) (hlam : 0 < lam) :
    Module.finrank 𝕜 (Module.End.eigenspace (T : F →ₗ[𝕜] F) (lam : 𝕜)) =
      {k : ℕ | courantValue T k = lam}.ncard := by
  classical
  have hsymm' : ∀ x y : F, ⟪T x, y⟫ = ⟪x, T y⟫ := fun x y ↦ hsymm x y
  obtain ⟨n, hlt, hge⟩ := exists_initial_segment T hsymm hc lam hlam
  obtain ⟨e, he, heig, hclause⟩ := exists_orthonormal_eigenvectors T hsymm hc n
    fun i hi ↦ hlam.trans_le (hlt i hi)
  have hμn : courantValue T n < lam := hge n le_rfl
  let I : Set (Fin n) := {i | courantValue T i = lam}
  let eI : I → F := fun i ↦ e i
  have heI : Orthonormal 𝕜 eI := he.comp Subtype.val Subtype.val_injective
  let S : Submodule 𝕜 F := Submodule.span 𝕜 (Set.range eI)
  -- the eigenspace is spanned by the `e_i` with `courantValue T i = lam`
  have hS : Module.End.eigenspace (T : F →ₗ[𝕜] F) (lam : 𝕜) = S := by
    apply le_antisymm
    · intro x hx
      have hTx : T x = (lam : 𝕜) • x := Module.End.mem_eigenspace_iff.mp hx
      let c : Fin n → 𝕜 := fun i ↦ if courantValue T i = lam then ⟪e i, x⟫ else 0
      let y : F := x - ∑ i, c i • e i
      -- `y` is orthogonal to every `e_j`
      have hy_orth : ∀ j, ⟪e j, y⟫ = 0 := by
        intro j
        have hsum : ⟪e j, ∑ i, c i • e i⟫ = c j := by
          rw [inner_sum]
          simp only [inner_smul_right, orthonormal_iff_ite.mp he]
          simp [Finset.sum_ite_eq']
        simp only [y, inner_sub_right, hsum, c]
        by_cases hj : courantValue T j = lam
        · rw [if_pos hj, sub_self]
        · rw [if_neg hj, sub_zero]
          -- eigenvectors for distinct eigenvalues are orthogonal
          have h1 : ⟪T (e j), x⟫ = ((courantValue T j : ℝ) : 𝕜) * ⟪e j, x⟫ := by
            rw [heig j, inner_smul_left, RCLike.conj_ofReal]
          have h2 : ⟪e j, T x⟫ = (lam : 𝕜) * ⟪e j, x⟫ := by
            rw [hTx, inner_smul_right]
          have h3 : (((courantValue T j : ℝ) : 𝕜) - (lam : 𝕜)) * ⟪e j, x⟫ = 0 := by
            rw [sub_mul, ← h1, ← h2, hsymm' (e j) x, sub_self]
          have hne : ((courantValue T j : ℝ) : 𝕜) - (lam : 𝕜) ≠ 0 := by
            intro h
            apply hj
            exact_mod_cast sub_eq_zero.mp h
          exact (mul_eq_zero.mp h3).resolve_left hne
      have hy_mem : y ∈ (Submodule.span 𝕜 (Set.range e))ᗮ := by
        have horth : Submodule.span 𝕜 (Set.range e) ⟂ Submodule.span 𝕜 {y} := by
          rw [Submodule.isOrtho_span]
          rintro _ ⟨j, rfl⟩ v hv
          rw [Set.mem_singleton_iff.mp hv]
          exact hy_orth j
        exact Submodule.isOrtho_iff_le.mp horth.symm (Submodule.mem_span_singleton_self y)
      -- `y` is again a `lam`-eigenvector
      have hTy : T y = (lam : 𝕜) • y := by
        simp only [y, map_sub, map_sum, map_smul, hTx, smul_sub, Finset.smul_sum]
        congr 1
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        by_cases hi : courantValue T i = lam
        · rw [heig i, hi, smul_comm]
        · simp [c, hi]
      have hre : re ⟪T y, y⟫ = lam * ‖y‖ ^ 2 := by
        rw [hTy, inner_smul_left, RCLike.conj_ofReal, inner_self_eq_norm_sq_to_K,
          ← RCLike.ofReal_pow, ← RCLike.ofReal_mul, RCLike.ofReal_re]
      have hbound := hclause y hy_mem
      rw [hre] at hbound
      have hy0 : y = 0 := by
        by_contra hy0
        have hpos : 0 < ‖y‖ ^ 2 := by positivity
        nlinarith
      -- hence `x` is the projection onto the `lam`-eigenvectors
      have hx_eq : x = ∑ i, c i • e i := sub_eq_zero.mp hy0
      rw [hx_eq]
      refine Submodule.sum_mem _ fun i _ ↦ ?_
      by_cases hi : courantValue T i = lam
      · refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩)
      · simp [c, hi]
    · rw [Submodule.span_le]
      rintro _ ⟨⟨i, hi⟩, rfl⟩
      rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff]
      change T (e i) = (lam : 𝕜) • e i
      rw [heig i]
      exact congrArg (fun r : ℝ ↦ ((r : 𝕜) • e i)) hi
  -- counting
  have hcount : {k : ℕ | courantValue T k = lam} = (fun i : Fin n ↦ (i : ℕ)) '' I := by
    ext k
    simp only [Set.mem_setOf_eq, Set.mem_image, I]
    constructor
    · intro hk
      have hkn : k < n := by
        by_contra h
        have := hge k (not_lt.mp h)
        linarith
      exact ⟨⟨k, hkn⟩, hk, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact hi
  rw [hS, hcount, Set.ncard_image_of_injective _ Fin.val_injective,
    finrank_span_eq_card heI.linearIndependent, ← Nat.card_eq_fintype_card,
    Nat.card_coe_set_eq]

/-- Every positive min–max value of a compact symmetric operator is an eigenvalue. -/
theorem hasEigenvalue_of_courantValue_pos (T : F →L[𝕜] F)
    (hsymm : LinearMap.IsSymmetric (T : F →ₗ[𝕜] F)) (hc : IsCompactOperator T)
    (k : ℕ) (hk : 0 < courantValue T k) :
    Module.End.HasEigenvalue (T : F →ₗ[𝕜] F) ((courantValue T k : ℝ) : 𝕜) := by
  have hfin := finite_setOf_courantValue_eq T hsymm hc _ hk
  have hpos : 0 < {j : ℕ | courantValue T j = courantValue T k}.ncard :=
    (Set.ncard_pos hfin).mpr ⟨k, rfl⟩
  rw [← finrank_eigenspace_eq_ncard T hsymm hc _ hk] at hpos
  have := Module.nontrivial_of_finrank_pos hpos
  exact Submodule.nontrivial_iff_ne_bot.mp this

/-- Every positive eigenvalue of a compact symmetric operator is attained by some min–max
value. -/
theorem exists_courantValue_eq_of_hasEigenvalue (T : F →L[𝕜] F)
    (hsymm : LinearMap.IsSymmetric (T : F →ₗ[𝕜] F)) (hc : IsCompactOperator T)
    (lam : ℝ) (hlam : 0 < lam)
    (heig : Module.End.HasEigenvalue (T : F →ₗ[𝕜] F) (lam : 𝕜)) :
    ∃ k, courantValue T k = lam := by
  have hlamne : (lam : 𝕜) ≠ 0 := by exact_mod_cast hlam.ne'
  have : FiniteDimensional 𝕜 (Module.End.eigenspace (T : F →ₗ[𝕜] F) (lam : 𝕜)) :=
    ContinuousLinearMap.finite_dimensional_eigenspace hc (lam : 𝕜) hlamne
  have : Nontrivial (Module.End.eigenspace (T : F →ₗ[𝕜] F) (lam : 𝕜)) :=
    Submodule.nontrivial_iff_ne_bot.mpr heig
  have hpos : 0 < Module.finrank 𝕜 (Module.End.eigenspace (T : F →ₗ[𝕜] F) (lam : 𝕜)) :=
    Module.finrank_pos
  rw [finrank_eigenspace_eq_ncard T hsymm hc lam hlam] at hpos
  obtain ⟨k, hk⟩ := (Set.ncard_pos (finite_setOf_courantValue_eq T hsymm hc lam hlam)).mp hpos
  exact ⟨k, hk⟩

end CompactSelfAdjoint

end RenewalGeometry.CourantFischer
