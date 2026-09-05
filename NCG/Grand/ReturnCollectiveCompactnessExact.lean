/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Collective return compactness and proper moments

Machinery for `thm:GT-return-collective-compactness`.  The tail energy space is a real Hilbert
space `H` with orthogonal finite-rank shells `Δ r` whose partial sums `Π R = ∑_{r ≤ R} Δ r` are
the finite-rank projections `Π_R ↑ I` (`Shells`: Parseval for the shells and for the heads, and
the tail identity `‖x - Π R x‖² = ∑_{r > R} ‖Δ r x‖²`).  For a uniformly bounded family of return
syntheses `𝒮 X : V →L[ℝ] H` the following are equivalent:

* (C1) `UniformTail`: `sup_X ‖(I - Π R) 𝒮 X‖ → 0`;
* (C2) `IsCompact (closure (unitImage 𝒮))`: the union of the unit-ball images is relatively
  compact;
* (C3) `ProperMoment`: positive proper weights `w r ↑ ∞` with
  `∑_r w r ‖Δ r 𝒮 X x‖² ≤ C ‖x‖²` uniformly (ER.9);

and on these branches `‖(I - Π R) 𝒮 X x‖² ≤ (C / w (R+1)) ‖x‖²` (ER.10,
`tail_sq_le_of_properMoment`).  Failure of (C1) returns normalized sources with order-one remote
mass beyond arbitrarily deep heads (`remote_source_of_not_uniformTail`).
-/

open Filter Topology Metric Finset
open scoped RealInnerProductSpace

namespace NCG
namespace ReturnCompactness

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Orthogonal finite-rank shells `Δ r` of the tail energy space with heads
`Π R = ∑_{r ≤ R} Δ r`: Parseval `‖x‖² = ∑_r ‖Δ r x‖²`, the head identity
`‖Π R x‖² = ∑_{r ≤ R} ‖Δ r x‖²`, and the tail identity `‖x - Π R x‖² = ∑_{r > R} ‖Δ r x‖²`. -/
structure Shells (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] where
  Δ : ℕ → H →L[ℝ] H
  finiteRank : ∀ r, FiniteDimensional ℝ (LinearMap.range (Δ r).toLinearMap)
  parseval : ∀ x : H, HasSum (fun r => ‖Δ r x‖ ^ 2) (‖x‖ ^ 2)
  head_sq : ∀ (x : H) (R : ℕ),
    ‖(∑ r ∈ range (R + 1), Δ r) x‖ ^ 2 = ∑ r ∈ range (R + 1), ‖Δ r x‖ ^ 2
  tail : ∀ (x : H) (R : ℕ),
    ‖x - (∑ r ∈ range (R + 1), Δ r) x‖ ^ 2 = ∑' k, ‖Δ (k + (R + 1)) x‖ ^ 2

variable (Sh : Shells H)

/-- The head projection `Π R = ∑_{r ≤ R} Δ r`. -/
noncomputable def head (R : ℕ) : H →L[ℝ] H := ∑ r ∈ range (R + 1), Sh.Δ r

omit [CompleteSpace H] in
theorem tail_eq (x : H) (R : ℕ) :
    ‖x - head Sh R x‖ ^ 2 = ∑' k, ‖Sh.Δ (k + (R + 1)) x‖ ^ 2 := Sh.tail x R

omit [CompleteSpace H] in
theorem summable_shells (x : H) : Summable fun r => ‖Sh.Δ r x‖ ^ 2 := (Sh.parseval x).summable

omit [CompleteSpace H] in
theorem tsum_shells (x : H) : ∑' r, ‖Sh.Δ r x‖ ^ 2 = ‖x‖ ^ 2 := (Sh.parseval x).tsum_eq

omit [CompleteSpace H] in
/-- Heads are contractions. -/
theorem norm_head_le (x : H) (R : ℕ) : ‖head Sh R x‖ ≤ ‖x‖ := by
  have h1 : ‖head Sh R x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [head, Sh.head_sq, ← tsum_shells Sh x]
    exact (summable_shells Sh x).sum_le_tsum _ (fun r _ => sq_nonneg _)
  exact le_of_sq_le_sq h1 (norm_nonneg _)

omit [CompleteSpace H] in
/-- Tails are contractions. -/
theorem norm_sub_head_le (x : H) (R : ℕ) : ‖x - head Sh R x‖ ≤ ‖x‖ := by
  have h1 : ‖x - head Sh R x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [tail_eq, ← tsum_shells Sh x]
    have hs := summable_shells Sh x
    have := Summable.sum_add_tsum_nat_add (R + 1) hs
    have hnn : 0 ≤ ∑ r ∈ range (R + 1), ‖Sh.Δ r x‖ ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
    linarith
  exact le_of_sq_le_sq h1 (norm_nonneg _)

omit [CompleteSpace H] in
/-- The tails of a fixed vector vanish. -/
theorem tendsto_tail (x : H) : Tendsto (fun R => ‖x - head Sh R x‖) atTop (𝓝 0) := by
  have h : Tendsto (fun R : ℕ => ∑' k, ‖Sh.Δ (k + (R + 1)) x‖ ^ 2) atTop (𝓝 0) :=
    (tendsto_sum_nat_add (fun r => ‖Sh.Δ r x‖ ^ 2)).comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun R => ‖x - head Sh R x‖ ^ 2) atTop (𝓝 0) := by
    simpa [tail_eq] using h
  rw [← Real.sqrt_zero]
  refine h2.sqrt.congr fun R => ?_
  rw [Real.sqrt_sq (norm_nonneg _)]

omit [CompleteSpace H] in
/-- The head range is finite-dimensional. -/
theorem finiteDimensional_head_range (R : ℕ) :
    FiniteDimensional ℝ (LinearMap.range (head Sh R).toLinearMap) := by
  haveI := Sh.finiteRank
  have hle : LinearMap.range (head Sh R).toLinearMap ≤
      (range (R + 1)).sup fun r => LinearMap.range (Sh.Δ r).toLinearMap := by
    rintro _ ⟨x, rfl⟩
    change (∑ r ∈ range (R + 1), Sh.Δ r) x ∈ _
    rw [_root_.sum_apply]
    exact Submodule.sum_mem _ fun r hr =>
      (Finset.le_sup (f := fun r => LinearMap.range (Sh.Δ r).toLinearMap) hr)
        (LinearMap.mem_range.mpr ⟨x, rfl⟩)
  exact Submodule.finiteDimensional_of_le hle

/-- A partial tail sum is bounded by the full tail. -/
theorem sum_filter_le_tail (a : ℕ → ℝ) (ha : ∀ r, 0 ≤ a r) (hs : Summable a) (m N : ℕ) :
    ∑ r ∈ (range N).filter (fun r => m < r), a r ≤ ∑' j, a (j + (m + 1)) := by
  have hset : (range N).filter (fun r => m < r) = Finset.Ico (m + 1) N := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [hset, sum_Ico_eq_sum_range]
  have hs' : Summable fun j => a (j + (m + 1)) := (summable_nat_add_iff (m + 1)).mpr hs
  calc ∑ k ∈ range (N - (m + 1)), a (m + 1 + k)
      = ∑ k ∈ range (N - (m + 1)), a (k + (m + 1)) := by
        refine sum_congr rfl fun k _ => ?_
        rw [add_comm]
    _ ≤ ∑' j, a (j + (m + 1)) := hs'.sum_le_tsum _ (fun _ _ => ha _)

/-! ### The family of return syntheses -/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {ι : Type*}

/-- The union of the unit-ball images `{𝒮 X x : X, ‖x‖ ≤ 1}`. -/
def unitImage (𝒮 : ι → V →L[ℝ] H) : Set H := {y | ∃ X x, ‖x‖ ≤ 1 ∧ y = 𝒮 X x}

/-- (C1): uniform finite-rank approximation `sup_X ‖(I - Π R) 𝒮 X‖ → 0`. -/
def UniformTail (𝒮 : ι → V →L[ℝ] H) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℕ, ∀ R, R₀ ≤ R → ∀ X x, ‖𝒮 X x - head Sh R (𝒮 X x)‖ ≤ ε * ‖x‖

/-- (C3): a proper moment bound (ER.9) with positive proper weights `w r ↑ ∞`. -/
def ProperMoment (𝒮 : ι → V →L[ℝ] H) : Prop :=
  ∃ w : ℕ → ℝ, (∀ r, 0 < w r) ∧ Monotone w ∧ Tendsto w atTop atTop ∧ ∃ C : ℝ, 0 ≤ C ∧
    ∀ X x N, ∑ r ∈ range N, w r * ‖Sh.Δ r (𝒮 X x)‖ ^ 2 ≤ C * ‖x‖ ^ 2

/-! ### (C1) ⟹ (C2) -/

omit [CompleteSpace H] in
/-- **(C1) ⟹ (C2)**: uniform finite-rank approximation of a bounded family gives total
boundedness of the unit-ball images. -/
theorem totallyBounded_unitImage_of_uniformTail {𝒮 : ι → V →L[ℝ] H} {M : ℝ}
    (hM : ∀ X, ‖𝒮 X‖ ≤ M) (h : UniformTail Sh 𝒮) : TotallyBounded (unitImage 𝒮) := by
  rw [Metric.totallyBounded_iff]
  intro ε hε
  obtain ⟨R, hR⟩ := h (ε / 2) (by positivity)
  haveI := finiteDimensional_head_range Sh R
  set U := LinearMap.range (head Sh R).toLinearMap with hU
  have hK : IsCompact (Subtype.val '' closedBall (0 : U) (max M 0)) :=
    (ProperSpace.isCompact_closedBall _ _).image continuous_subtype_val
  obtain ⟨t, htfin, htcov⟩ := Metric.totallyBounded_iff.mp hK.totallyBounded (ε / 2)
    (by positivity)
  refine ⟨t, htfin, fun y hy => ?_⟩
  obtain ⟨X, x, hx, rfl⟩ := hy
  have hmem : head Sh R (𝒮 X x) ∈ Subtype.val '' closedBall (0 : U) (max M 0) := by
    refine ⟨⟨head Sh R (𝒮 X x), LinearMap.mem_range.mpr ⟨𝒮 X x, rfl⟩⟩, ?_, rfl⟩
    rw [mem_closedBall, dist_zero_right]
    change ‖head Sh R (𝒮 X x)‖ ≤ max M 0
    calc ‖head Sh R (𝒮 X x)‖ ≤ ‖𝒮 X x‖ := norm_head_le Sh _ R
      _ ≤ ‖𝒮 X‖ * ‖x‖ := (𝒮 X).le_opNorm x
      _ ≤ M * 1 := mul_le_mul (hM X) hx (norm_nonneg _) ((norm_nonneg _).trans (hM X))
      _ ≤ max M 0 := by simp
  obtain ⟨z, hz, hyz⟩ := Set.mem_iUnion₂.mp (htcov hmem)
  refine Set.mem_iUnion₂.mpr ⟨z, hz, ?_⟩
  rw [mem_ball] at hyz ⊢
  calc dist (𝒮 X x) z ≤ dist (𝒮 X x) (head Sh R (𝒮 X x)) + dist (head Sh R (𝒮 X x)) z :=
        dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := by
        refine add_lt_add_of_le_of_lt ?_ hyz
        rw [dist_eq_norm]
        calc ‖𝒮 X x - head Sh R (𝒮 X x)‖ ≤ ε / 2 * ‖x‖ := hR R le_rfl X x
          _ ≤ ε / 2 * 1 := by gcongr
          _ = ε / 2 := mul_one _
    _ = ε := by ring

theorem isCompact_closure_unitImage_of_uniformTail {𝒮 : ι → V →L[ℝ] H} {M : ℝ}
    (hM : ∀ X, ‖𝒮 X‖ ≤ M) (h : UniformTail Sh 𝒮) : IsCompact (closure (unitImage 𝒮)) :=
  isCompact_iff_totallyBounded_isComplete.mpr
    ⟨(totallyBounded_unitImage_of_uniformTail Sh hM h).closure, isClosed_closure.isComplete⟩

/-! ### (C2) ⟹ (C1) -/

omit [CompleteSpace H] in
/-- **(C2) ⟹ (C1)**: relative compactness of the unit-ball images gives uniform finite-rank
approximation. -/
theorem uniformTail_of_isCompact_closure {𝒮 : ι → V →L[ℝ] H}
    (h : IsCompact (closure (unitImage 𝒮))) : UniformTail Sh 𝒮 := by
  have htb : TotallyBounded (unitImage 𝒮) := h.totallyBounded.subset subset_closure
  intro ε hε
  obtain ⟨t, htfin, htcov⟩ := Metric.totallyBounded_iff.mp htb (ε / 2) (by positivity)
  have hnet : ∀ z ∈ t, ∃ R₀ : ℕ, ∀ R, R₀ ≤ R → ‖z - head Sh R z‖ ≤ ε / 2 := by
    intro z _
    obtain ⟨R₀, hR₀⟩ := eventually_atTop.mp
      ((tendsto_tail Sh z).eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε / 2)))
    exact ⟨R₀, fun R hR => (hR₀ R hR).le⟩
  choose! R₀ hR₀ using hnet
  refine ⟨htfin.toFinset.sup R₀, fun R hR X x => ?_⟩
  -- unit-norm bound, then homogeneity
  have hunit : ∀ u : V, ‖u‖ ≤ 1 → ‖𝒮 X u - head Sh R (𝒮 X u)‖ ≤ ε := by
    intro u hu
    obtain ⟨z, hz, hyz⟩ := Set.mem_iUnion₂.mp (htcov ⟨X, u, hu, rfl⟩)
    rw [mem_ball, dist_eq_norm] at hyz
    have hRz : R₀ z ≤ R := (Finset.le_sup (htfin.mem_toFinset.mpr hz)).trans hR
    have hdecomp : 𝒮 X u - head Sh R (𝒮 X u)
        = ((𝒮 X u - z) - head Sh R (𝒮 X u - z)) + (z - head Sh R z) := by
      rw [map_sub]; abel
    calc ‖𝒮 X u - head Sh R (𝒮 X u)‖
        ≤ ‖(𝒮 X u - z) - head Sh R (𝒮 X u - z)‖ + ‖z - head Sh R z‖ := by
          rw [hdecomp]; exact norm_add_le _ _
      _ ≤ ‖𝒮 X u - z‖ + ε / 2 := add_le_add (norm_sub_head_le Sh _ R) (hR₀ z hz R hRz)
      _ ≤ ε / 2 + ε / 2 := by linarith
      _ = ε := by ring
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hu := hunit (‖x‖⁻¹ • x) (by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hxpos.ne'])
  rw [map_smul, map_smul, ← smul_sub, norm_smul, norm_inv, norm_norm] at hu
  rwa [inv_mul_le_iff₀ hxpos, mul_comm] at hu

/-! ### (C3) ⟹ (ER.10) ⟹ (C1) -/

omit [CompleteSpace H] in
/-- **(ER.10)**: a proper moment bound gives the tail bound `‖(I - Π R) 𝒮 X x‖² ≤ C/w(R+1) ‖x‖²`. -/
theorem tail_sq_le_of_properMoment {𝒮 : ι → V →L[ℝ] H} {w : ℕ → ℝ} (hw : ∀ r, 0 < w r)
    (hmono : Monotone w) {C : ℝ}
    (hC : ∀ X x N, ∑ r ∈ range N, w r * ‖Sh.Δ r (𝒮 X x)‖ ^ 2 ≤ C * ‖x‖ ^ 2) (X : ι) (x : V)
    (R : ℕ) : ‖𝒮 X x - head Sh R (𝒮 X x)‖ ^ 2 ≤ C / w (R + 1) * ‖x‖ ^ 2 := by
  rw [tail_eq]
  set a : ℕ → ℝ := fun r => ‖Sh.Δ r (𝒮 X x)‖ ^ 2 with ha
  refine Real.tsum_le_of_sum_range_le (fun _ => sq_nonneg _) fun N => ?_
  have hwR := hw (R + 1)
  have h1 : ∑ j ∈ range N, a (j + (R + 1))
      ≤ (1 / w (R + 1)) * ∑ j ∈ range N, w (j + (R + 1)) * a (j + (R + 1)) := by
    rw [mul_sum]
    refine sum_le_sum fun j _ => ?_
    have hwj : w (R + 1) ≤ w (j + (R + 1)) := hmono (by omega)
    have hann : 0 ≤ a (j + (R + 1)) := sq_nonneg _
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hwR, mul_comm]
    exact mul_le_mul_of_nonneg_right hwj hann
  have h2 : ∑ j ∈ range N, w (j + (R + 1)) * a (j + (R + 1))
      ≤ ∑ r ∈ range (N + (R + 1)), w r * a r := by
    have hshift : ∑ j ∈ range N, w (j + (R + 1)) * a (j + (R + 1))
        = ∑ r ∈ Finset.Ico (R + 1) (N + (R + 1)), w r * a r := by
      rw [sum_Ico_eq_sum_range, Nat.add_sub_cancel]
      refine sum_congr rfl fun j _ => ?_
      rw [add_comm]
    rw [hshift]
    exact sum_le_sum_of_subset_of_nonneg (fun r hr => by
        rw [Finset.mem_Ico] at hr; exact Finset.mem_range.mpr hr.2)
      fun r _ _ => mul_nonneg (hw r).le (sq_nonneg _)
  calc ∑ j ∈ range N, a (j + (R + 1))
      ≤ (1 / w (R + 1)) * ∑ j ∈ range N, w (j + (R + 1)) * a (j + (R + 1)) := h1
    _ ≤ (1 / w (R + 1)) * ∑ r ∈ range (N + (R + 1)), w r * a r :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ ≤ (1 / w (R + 1)) * (C * ‖x‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (hC X x _) (by positivity)
    _ = C / w (R + 1) * ‖x‖ ^ 2 := by ring

omit [CompleteSpace H] in
/-- **(C3) ⟹ (C1)**. -/
theorem uniformTail_of_properMoment {𝒮 : ι → V →L[ℝ] H} (h : ProperMoment Sh 𝒮) :
    UniformTail Sh 𝒮 := by
  obtain ⟨w, hw, hmono, hlim, C, hC0, hC⟩ := h
  intro ε hε
  -- choose `R₀` with `w (R+1) ≥ C / ε²` beyond it
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.mp (hlim.eventually (eventually_ge_atTop (C / ε ^ 2)))
  refine ⟨R₀, fun R hR X x => ?_⟩
  have hwR : C / ε ^ 2 ≤ w (R + 1) := hR₀ (R + 1) (by omega)
  have hsq : ‖𝒮 X x - head Sh R (𝒮 X x)‖ ^ 2 ≤ (ε * ‖x‖) ^ 2 := by
    calc ‖𝒮 X x - head Sh R (𝒮 X x)‖ ^ 2 ≤ C / w (R + 1) * ‖x‖ ^ 2 :=
          tail_sq_le_of_properMoment Sh hw hmono hC X x R
      _ ≤ ε ^ 2 * ‖x‖ ^ 2 := by
          refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
          rw [div_le_iff₀ (hw _)]
          calc C = C / ε ^ 2 * ε ^ 2 := by field_simp
            _ ≤ w (R + 1) * ε ^ 2 := by gcongr
            _ = ε ^ 2 * w (R + 1) := by ring
      _ = (ε * ‖x‖) ^ 2 := by ring
  exact le_of_sq_le_sq hsq (by positivity)

/-! ### (C1) ⟹ (C3) -/

omit [CompleteSpace H] in
/-- **(C1) ⟹ (C3)**: radii along which the uniform tails fall below `2^{-k}` and slowly
increasing constant weights on the intervening shell blocks give a uniformly bounded proper
weighted sum. -/
theorem properMoment_of_uniformTail {𝒮 : ι → V →L[ℝ] H} {M : ℝ}
    (hM : ∀ X, ‖𝒮 X‖ ≤ M) (h : UniformTail Sh 𝒮) : ProperMoment Sh 𝒮 := by
  classical
  have hex : ∀ k : ℕ, ∃ R₀ : ℕ, ∀ R, R₀ ≤ R → ∀ X x,
      ‖𝒮 X x - head Sh R (𝒮 X x)‖ ≤ (1 / 2 : ℝ) ^ k * ‖x‖ := fun k => h _ (by positivity)
  choose R₀ hR₀ using hex
  -- strictly increasing radii `Rk k ≥ R₀ k`, `Rk k ≥ k`
  set Rk : ℕ → ℕ := fun k => (∑ j ∈ range (k + 1), R₀ j) + k with hRk
  have hRk_ge : ∀ k, R₀ k ≤ Rk k := fun k =>
    (single_le_sum (fun j _ => Nat.zero_le (R₀ j))
      (Finset.mem_range.mpr (Nat.lt_succ_self k))).trans
      (Nat.le_add_right _ _)
  have hRk_k : ∀ k, k ≤ Rk k := fun k => Nat.le_add_left k _
  have hRk_mono : StrictMono Rk := by
    refine strictMono_nat_of_lt_succ fun k => ?_
    simp only [hRk, sum_range_succ]
    omega
  set w : ℕ → ℝ := fun r => 1 + (((range r).filter fun k => Rk k < r).card : ℝ) with hw
  refine ⟨w, fun r => by positivity, ?_, ?_, M ^ 2 + 2, by positivity, fun X x N => ?_⟩
  · intro r s hrs
    simp only [hw]
    have : ((range r).filter fun k => Rk k < r) ⊆ (range s).filter fun k => Rk k < s := by
      intro k hk
      rw [Finset.mem_filter, Finset.mem_range] at hk ⊢
      omega
    have hc : ((((range r).filter fun k => Rk k < r).card : ℕ) : ℝ)
        ≤ (((range s).filter fun k => Rk k < s).card : ℕ) := by
      exact_mod_cast card_le_card this
    linarith
  · rw [tendsto_atTop_atTop]
    intro b
    refine ⟨Rk ⌈b⌉₊ + 1, fun r hr => ?_⟩
    have hsub : range ⌈b⌉₊ ⊆ (range r).filter fun k => Rk k < r := by
      intro k hk
      rw [Finset.mem_range] at hk
      rw [Finset.mem_filter, Finset.mem_range]
      have h1 : Rk k < Rk ⌈b⌉₊ := hRk_mono hk
      have h2 := hRk_k k
      omega
    have hcard : (⌈b⌉₊ : ℝ) ≤ ((range r).filter fun k => Rk k < r).card := by
      exact_mod_cast (card_range ⌈b⌉₊).symm.le.trans (card_le_card hsub)
    simp only [hw]
    linarith [Nat.le_ceil b]
  · set y := 𝒮 X x with hy
    set a : ℕ → ℝ := fun r => ‖Sh.Δ r y‖ ^ 2 with ha
    have hann : ∀ r, 0 ≤ a r := fun r => sq_nonneg _
    have hs : Summable a := summable_shells Sh y
    -- expand the weights
    have hexp : ∑ r ∈ range N, w r * a r
        = ∑ r ∈ range N, a r + ∑ k ∈ range N, ∑ r ∈ (range N).filter (fun r => Rk k < r), a r := by
      simp only [hw, add_mul, one_mul, sum_add_distrib]
      congr 1
      calc ∑ r ∈ range N, (((range r).filter fun k => Rk k < r).card : ℝ) * a r
          = ∑ r ∈ range N, ∑ k ∈ (range r).filter (fun k => Rk k < r), a r := by
            refine sum_congr rfl fun r _ => ?_
            rw [sum_const, nsmul_eq_mul]
        _ = ∑ k ∈ range N, ∑ r ∈ (range N).filter (fun r => Rk k < r), a r := by
            rw [sum_comm']
            intro r k
            simp only [Finset.mem_filter, Finset.mem_range]
            have := hRk_k k
            omega
    rw [hexp]
    have hbound1 : ∑ r ∈ range N, a r ≤ (M * ‖x‖) ^ 2 := by
      calc ∑ r ∈ range N, a r ≤ ∑' r, a r := hs.sum_le_tsum _ (fun r _ => hann r)
        _ = ‖y‖ ^ 2 := tsum_shells Sh y
        _ ≤ (M * ‖x‖) ^ 2 := by
            gcongr
            exact ((𝒮 X).le_opNorm x).trans (mul_le_mul_of_nonneg_right (hM X) (norm_nonneg _))
    have hbound2 : ∀ k, ∑ r ∈ (range N).filter (fun r => Rk k < r), a r
        ≤ ((1 / 2 : ℝ) ^ k * ‖x‖) ^ 2 := by
      intro k
      calc ∑ r ∈ (range N).filter (fun r => Rk k < r), a r
          ≤ ∑' j, a (j + (Rk k + 1)) := sum_filter_le_tail a hann hs (Rk k) N
        _ = ‖y - head Sh (Rk k) y‖ ^ 2 := (tail_eq Sh y (Rk k)).symm
        _ ≤ ((1 / 2 : ℝ) ^ k * ‖x‖) ^ 2 := by
            gcongr
            exact hR₀ k (Rk k) (hRk_ge k) X x
    have hgeom : ∑ k ∈ range N, ((1 / 2 : ℝ) ^ k * ‖x‖) ^ 2 ≤ 2 * ‖x‖ ^ 2 := by
      have : ∑ k ∈ range N, ((1 / 2 : ℝ) ^ k * ‖x‖) ^ 2
          = (∑ k ∈ range N, (1 / 4 : ℝ) ^ k) * ‖x‖ ^ 2 := by
        rw [sum_mul]
        refine sum_congr rfl fun k _ => ?_
        rw [mul_pow, ← pow_mul, show (1 / 2 : ℝ) ^ (k * 2) = (1 / 4) ^ k by
          rw [mul_comm, pow_mul]; norm_num]
      rw [this]
      refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      calc ∑ k ∈ range N, (1 / 4 : ℝ) ^ k ≤ ∑' k, (1 / 4 : ℝ) ^ k :=
            (summable_geometric_of_lt_one (by norm_num) (by norm_num)).sum_le_tsum _
              (fun k _ => by positivity)
        _ = (1 - 1 / 4)⁻¹ := tsum_geometric_of_lt_one (by norm_num) (by norm_num)
        _ ≤ 2 := by norm_num
    calc ∑ r ∈ range N, a r + ∑ k ∈ range N, ∑ r ∈ (range N).filter (fun r => Rk k < r), a r
        ≤ (M * ‖x‖) ^ 2 + ∑ k ∈ range N, ((1 / 2 : ℝ) ^ k * ‖x‖) ^ 2 :=
          add_le_add hbound1 (sum_le_sum fun k _ => hbound2 k)
      _ ≤ (M * ‖x‖) ^ 2 + 2 * ‖x‖ ^ 2 := add_le_add_right hgeom _
      _ = (M ^ 2 + 2) * ‖x‖ ^ 2 := by ring

/-! ### Failure clause -/

omit [CompleteSpace H] in
/-- If uniform finite-rank approximation fails, normalized sources retain order-one remote mass
beyond arbitrarily deep heads. -/
theorem remote_source_of_not_uniformTail {𝒮 : ι → V →L[ℝ] H} (h : ¬ UniformTail Sh 𝒮) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ R₀ : ℕ, ∃ R, R₀ ≤ R ∧ ∃ X x, ‖x‖ = 1 ∧
      δ < ‖𝒮 X x - head Sh R (𝒮 X x)‖ := by
  simp only [UniformTail, not_forall, not_exists, not_le] at h
  obtain ⟨δ, hδ, hfail⟩ := h
  refine ⟨δ, hδ, fun R₀ => ?_⟩
  obtain ⟨R, hR, X, x, hx⟩ := hfail R₀
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  refine ⟨R, hR, X, ‖x‖⁻¹ • x, by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hxpos.ne'],
    ?_⟩
  rw [map_smul, map_smul, ← smul_sub, norm_smul, norm_inv, norm_norm, lt_inv_mul_iff₀ hxpos]
  linarith

/-! ### The bundled theorem -/

/-- **`thm:GT-return-collective-compactness`**: (C1) ⟺ (C2) ⟺ (C3) for a uniformly bounded
family of return syntheses, the tail bound (ER.10) on the proper-moment branch, and the failure
clause. -/
theorem return_collective_compactness {𝒮 : ι → V →L[ℝ] H} {M : ℝ}
    (hM : ∀ X, ‖𝒮 X‖ ≤ M) :
    (UniformTail Sh 𝒮 ↔ IsCompact (closure (unitImage 𝒮))) ∧
      (UniformTail Sh 𝒮 ↔ ProperMoment Sh 𝒮) ∧
      (∀ (w : ℕ → ℝ), (∀ r, 0 < w r) → Monotone w → ∀ C : ℝ,
        (∀ X x N, ∑ r ∈ range N, w r * ‖Sh.Δ r (𝒮 X x)‖ ^ 2 ≤ C * ‖x‖ ^ 2) →
        ∀ X x R, ‖𝒮 X x - head Sh R (𝒮 X x)‖ ^ 2 ≤ C / w (R + 1) * ‖x‖ ^ 2) ∧
      (¬ UniformTail Sh 𝒮 → ∃ δ : ℝ, 0 < δ ∧ ∀ R₀ : ℕ, ∃ R, R₀ ≤ R ∧ ∃ X x, ‖x‖ = 1 ∧
        δ < ‖𝒮 X x - head Sh R (𝒮 X x)‖) :=
  ⟨⟨isCompact_closure_unitImage_of_uniformTail Sh hM, uniformTail_of_isCompact_closure Sh⟩,
    ⟨properMoment_of_uniformTail Sh hM, uniformTail_of_properMoment Sh⟩,
    fun _w hw hmono _C hC X x R => tail_sq_le_of_properMoment Sh hw hmono hC X x R,
    remote_source_of_not_uniformTail Sh⟩

end ReturnCompactness
end NCG
