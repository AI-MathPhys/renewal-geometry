/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.GeneratedNonemptyClosed

/-!
# `thm:generated-dynamics` and `cor:generated-nonempty` in the manuscript's norms

Einstein–Standard-Model action-closure manuscript, `thm:generated-dynamics`
(`eq:generated-initial-rate`, `eq:generated-first`, `eq:generated-bosonic`, `eq:generated-Dirac`,
`eq:generated-stationarity`) and `cor:generated-nonempty`, with `Σ = 𝕋³`.

The readout package `GenReadout.generated_dynamics_closed` states its bounds in Fourier form (finite
weighted coefficient sums) and on the slices of the open time cells, with a data distance `δ`.
This file restates them in the norms of the manuscript and with the data distance `C N^{-p}`:

* `sliceH r f t` — the slice norm `‖f(t)‖_{H^r} = (Σ_b Q_r(f_b)(t))^{1/2}` (classical derivatives on
  the slice); `sliceH_le_iff_fourier` — its equivalence with the Fourier form (Parseval in the
  Hartley basis, `GenParseval.hasSum_wq_coef_sq`);
* `supNorm g a b = sup_{t ∈ [a,b]} g(t)` and `essNorm g a b = ess sup_{t ∈ (a,b)} g(t)` (values in
  `ℝ≥0∞`, so no junk value for unbounded families); `supNorm_le_iff`, `essNorm_le_of_off_countable`;
  hence `C_tH^r = supNorm (sliceH r ·)` and `L^∞_tH^r = essNorm (sliceH r ·)`;
* `cellIdx τ t` — the cell `[jτ, (j+1)τ]` used at time `t` (`j = ⌈t/τ⌉ - 1`, left cell at the
  nodes); the piecewise Hermite record is read on that cell, so its slice norms are functions of
  `t` alone (`recErr`, `recErrD`, the residual readouts), and at the nodes both adjacent cells give
  the same slice (`sliceH_recW_node`);
* `Q_cont_of_smooth_near` — slice norms of a field smooth near a closed slab are continuous there
  (used to extend the open-cell Dirac readout to the nodes, so the Dirac residual is bounded in
  `C_tH^{s+1}`);
* **`GenNorms.generated_dynamics_norms`** — `thm:generated-dynamics` in the manuscript's norms:
  for finite data with `‖U_{0,N}‖_{H^q} ≤ M` and `‖U_{0,N} - U₀‖_{H^{s+4}} ≤ C₀N^{-p}`,
  `‖z_{N,τ} - z‖_{C_tH^{s+2}} + ‖∂_tz_{N,τ} - ∂_tz‖_{C_tH^{s+2}} ≤ C(N^{-p} + τ²)` (state level,
  stronger than the stated `C_tH^{s+1}` for the time derivative),
  `‖Riem(g_{N,τ}) - Riem(g)‖_{L^∞_tH^s} + ‖R_B(z_{N,τ})‖_{L^∞_tH^s} ≤ C(N^{-p} + τ)`,
  `‖R_D(z_{N,τ})‖_{C_tH^{s+1}} ≤ C(N^{-p} + τ²)`, and
  `|DS^{cmp}[V]| ≤ C(N^{-p} + τ)‖V‖_{0,τ}`;
* **`GenNorms.initial_rate_P0`** — `eq:generated-initial-rate` exactly as stated for the finite data
  `U_{0,N} = P_N U₀`: `sup_N ‖U_{0,N}‖_{H^q} ≤ ‖U₀‖_{H^q}`, `‖U_{0,N} - U₀‖_{H^{s+4}} ≤ C N^{-p}`;
* **`GenNorms.generated_nonempty_norms`** — `cor:generated-nonempty` in these norms.
-/

open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal

noncomputable section

namespace RenewalGeometry.GenNorms

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk SlabSobAlg QLEnergy KatoGalerkin

set_option linter.unusedSectionVars false

/-! ### Slice norms and their Fourier form -/

section SliceNorms

variable {d n : ℕ}

/-- **The slice norm** `‖f(t)‖_{H^r} = (Σ_b Q_r(f_b)(t))^{1/2}` of a finite family of fields
(classical derivatives along the slice `{t} × 𝕋^d`). -/
def sliceH (r : ℕ) (f : Fin n → ST d → ℝ) (t : ℝ) : ℝ := Real.sqrt (∑ b, Q r (f b) t)

theorem sliceH_nonneg (r : ℕ) (f : Fin n → ST d → ℝ) (t : ℝ) : 0 ≤ sliceH r f t :=
  Real.sqrt_nonneg _

theorem sum_Q_nonneg (r : ℕ) (f : Fin n → ST d → ℝ) (t : ℝ) : 0 ≤ ∑ b, Q r (f b) t :=
  Finset.sum_nonneg fun b _ => Q_nonneg r (f b) t

/-- `‖f(t)‖_{H^r} ≤ B` iff `Σ_b Q_r(f_b)(t) ≤ B²`. -/
theorem sliceH_le_iff {r : ℕ} {f : Fin n → ST d → ℝ} {t B : ℝ} (hB : 0 ≤ B) :
    sliceH r f t ≤ B ↔ ∑ b, Q r (f b) t ≤ B ^ 2 := by
  unfold sliceH
  rw [Real.sqrt_le_left hB]

/-- **The slice norm in Fourier form** (Parseval in the Hartley basis): for smooth spatially
periodic fields, `‖f(t)‖_{H^r} ≤ B` iff every finite weighted coefficient sum
`Σ_b Σ_{k ∈ S} w_r(k) c_k(f_b(t))²` is at most `B²`. -/
theorem sliceH_le_iff_fourier {r : ℕ} {f : Fin n → ST d → ℝ} (hf : ∀ b, ContDiff ℝ ∞ (f b))
    (hp : ∀ b, IsSPeriodic (f b)) {t B : ℝ} (hB : 0 ≤ B) :
    sliceH r f t ≤ B ↔
      ∀ S : Finset (Fin d → ℤ), ∑ b, ∑ k ∈ S, wq r k * coef (f b) t k ^ 2 ≤ B ^ 2 := by
  rw [sliceH_le_iff hB]
  have hs : HasSum (fun k => ∑ b, wq r k * coef (f b) t k ^ 2) (∑ b, Q r (f b) t) :=
    hasSum_sum fun b _ => GenParseval.hasSum_wq_coef_sq r (hf b) (hp b) t
  constructor
  · intro h S
    rw [Finset.sum_comm]
    refine le_trans ?_ h
    exact sum_le_hasSum S (fun k _ => Finset.sum_nonneg fun b _ =>
      mul_nonneg (wq_nonneg r k) (sq_nonneg _)) hs
  · intro h
    exact GenHermite.sum_Q_le_of_sum_le r hf hp h

/-- The slice norm of a Galerkin field is the Euclidean norm of its Galerkin state
(`energyQ_fld`). -/
theorem sliceH_fld (q : ℕ) {N : ℕ} (a : GS d n N) (t : ℝ) : sliceH q (fld q a) t = ‖a‖ := by
  unfold sliceH
  have h := energyQ_fld q a t
  unfold energyQ at h
  rw [h, Real.sqrt_sq (norm_nonneg a)]

end SliceNorms

/-! ### Supremum and essential supremum in time -/

section TimeNorms

/-- **The supremum over the slices of `[a, b]`** (`C_t`-norm of a slice quantity), in `ℝ≥0∞`. -/
def supNorm (g : ℝ → ℝ) (a b : ℝ) : ℝ≥0∞ := ⨆ t ∈ Icc a b, ENNReal.ofReal (g t)

/-- **The essential supremum over the slices of `(a, b)`** (`L^∞_t`-norm of a slice quantity),
in `ℝ≥0∞`. -/
def essNorm (g : ℝ → ℝ) (a b : ℝ) : ℝ≥0∞ :=
  essSup (fun t => ENNReal.ofReal (g t)) (volume.restrict (Ioo a b))

/-- `sup_{[a,b]} g ≤ B` iff `g ≤ B` on every slice of `[a, b]`. -/
theorem supNorm_le_iff {g : ℝ → ℝ} {a b B : ℝ} (hB : 0 ≤ B) :
    supNorm g a b ≤ ENNReal.ofReal B ↔ ∀ t ∈ Icc a b, g t ≤ B := by
  unfold supNorm
  constructor
  · intro h t ht
    have := (le_iSup₂ (f := fun t (_ : t ∈ Icc a b) => ENNReal.ofReal (g t)) t ht).trans h
    exact (ENNReal.ofReal_le_ofReal_iff hB).1 this
  · intro h
    exact iSup₂_le fun t ht => ENNReal.ofReal_le_ofReal (h t ht)

/-- `ess sup_{(a,b)} g ≤ B` as soon as `g ≤ B` on `(a, b)` off a countable set (e.g. the nodes of
a time grid). -/
theorem essNorm_le_of_off_countable {g : ℝ → ℝ} {a b B : ℝ} {E : Set ℝ} (hE : E.Countable)
    (h : ∀ t ∈ Ioo a b, t ∉ E → g t ≤ B) : essNorm g a b ≤ ENNReal.ofReal B := by
  unfold essNorm
  refine essSup_le_of_ae_le _ ?_
  have h0 : ∀ᵐ t ∂volume, t ∉ E := measure_eq_zero_iff_ae_notMem.1 (hE.measure_zero volume)
  have h1 : ∀ᵐ t ∂(volume.restrict (Ioo a b)), t ∈ Ioo a b :=
    ae_restrict_mem measurableSet_Ioo
  filter_upwards [ae_restrict_of_ae h0, h1] with t ht ht'
  exact ENNReal.ofReal_le_ofReal (h t ht' ht)

theorem essNorm_le_supNorm {g : ℝ → ℝ} {a b : ℝ} : essNorm g a b ≤ supNorm g a b := by
  unfold essNorm supNorm
  refine essSup_le_of_ae_le _ ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  exact le_iSup₂ (f := fun t (_ : t ∈ Icc a b) => ENNReal.ofReal (g t)) t (Ioo_subset_Icc_self ht)

end TimeNorms

/-! ### The cells of a time grid -/

section Cells

/-- **The cell used at time `t`** of the grid of step `τ`: `j = ⌈t/τ⌉ - 1`, so that
`t ∈ [jτ, (j+1)τ]` (the left cell at a node, the cell `0` at `t ≤ 0`). -/
def cellIdx (τ t : ℝ) : ℕ := ⌈t / τ⌉₊ - 1

theorem cellIdx_mem {τ t : ℝ} (hτ : 0 < τ) (ht : 0 ≤ t) :
    (cellIdx τ t : ℝ) * τ ≤ t ∧ t ≤ ((cellIdx τ t : ℝ) + 1) * τ := by
  unfold cellIdx
  rcases (div_nonneg ht hτ.le).eq_or_lt with h0 | h0
  · have ht0 : t = 0 := by
      rcases (div_eq_zero_iff.1 h0.symm) with h | h
      · exact h
      · exact absurd h hτ.ne'
    subst ht0
    simp [hτ.le]
  · have hc : 1 ≤ ⌈t / τ⌉₊ := Nat.one_le_iff_ne_zero.2 (by
      rw [Ne, Nat.ceil_eq_zero, not_le]; exact h0)
    have hcast : ((⌈t / τ⌉₊ - 1 : ℕ) : ℝ) = (⌈t / τ⌉₊ : ℝ) - 1 := by
      rw [Nat.cast_sub hc, Nat.cast_one]
    rw [hcast]
    have h1 : t / τ ≤ ⌈t / τ⌉₊ := Nat.le_ceil _
    have h2 : (⌈t / τ⌉₊ : ℝ) < t / τ + 1 := Nat.ceil_lt_add_one (div_nonneg ht hτ.le)
    constructor
    · have : ((⌈t / τ⌉₊ : ℝ) - 1) < t / τ := by linarith
      have := (lt_div_iff₀ hτ).1 this
      linarith
    · have := (div_le_iff₀ hτ).1 h1
      linarith

theorem cellIdx_lt {τ t : ℝ} (hτ : 0 < τ) {J : ℕ} (hJ : 1 ≤ J) (ht : t ≤ (J : ℝ) * τ) :
    cellIdx τ t < J := by
  unfold cellIdx
  have : ⌈t / τ⌉₊ ≤ J := Nat.ceil_le.2 ((div_le_iff₀ hτ).2 ht)
  omega

theorem cellIdx_of_mem {τ t : ℝ} (hτ : 0 < τ) {j : ℕ}
    (ht : t ∈ Ioc ((j : ℝ) * τ) (((j : ℝ) + 1) * τ)) : cellIdx τ t = j := by
  unfold cellIdx
  have h1 : (j : ℝ) < t / τ := (lt_div_iff₀ hτ).2 ht.1
  have h2 : t / τ ≤ (j : ℝ) + 1 := (div_le_iff₀ hτ).2 ht.2
  have : ⌈t / τ⌉₊ = j + 1 := by
    rw [Nat.ceil_eq_iff (by omega)]
    push_cast
    constructor <;> linarith
  omega

/-- The nodes `{jτ}` of a grid form a countable set. -/
theorem nodes_countable (τ : ℝ) : (Set.range fun j : ℕ => (j : ℝ) * τ).Countable :=
  Set.countable_range _

/-- A time of `(0, Jτ)` that is not a node lies in the open interior of its cell. -/
theorem mem_open_cell {τ t : ℝ} (hτ : 0 < τ) (ht : 0 < t)
    (hn : t ∉ Set.range fun j : ℕ => (j : ℝ) * τ) :
    t ∈ Ioo ((cellIdx τ t : ℝ) * τ) (((cellIdx τ t : ℝ) + 1) * τ) := by
  obtain ⟨h1, h2⟩ := cellIdx_mem hτ ht.le
  refine ⟨lt_of_le_of_ne h1 fun h => hn ⟨_, h⟩, lt_of_le_of_ne h2 fun h => hn ⟨cellIdx τ t + 1, ?_⟩⟩
  push_cast
  exact h.symm

end Cells


/-! ### Continuity of slice norms near a closed slab -/

section Continuity



/-- A smooth time cutoff equal to `1` on `[a - ε/3, b + ε/3]` and to `0` outside
`(a - 2ε/3, b + 2ε/3)`. -/
def cutT (a b ε t : ℝ) : ℝ :=
  Real.smoothTransition ((t - (a - 2 * ε / 3)) / (ε / 3)) *
    Real.smoothTransition (((b + 2 * ε / 3) - t) / (ε / 3))

theorem contDiff_cutT (a b ε : ℝ) : ContDiff ℝ ∞ (cutT a b ε) := by
  unfold cutT
  have h1 : ContDiff ℝ ∞ (fun t : ℝ => (t - (a - 2 * ε / 3)) / (ε / 3)) := by fun_prop
  have h2 : ContDiff ℝ ∞ (fun t : ℝ => ((b + 2 * ε / 3) - t) / (ε / 3)) := by fun_prop
  exact (Real.smoothTransition.contDiff.comp h1).mul (Real.smoothTransition.contDiff.comp h2)

theorem cutT_one {a b ε t : ℝ} (hε : 0 < ε) (h1 : a - ε / 3 ≤ t) (h2 : t ≤ b + ε / 3) :
    cutT a b ε t = 1 := by
  unfold cutT
  rw [Real.smoothTransition.one_of_one_le, Real.smoothTransition.one_of_one_le, mul_one]
  · rw [le_div_iff₀ (by positivity)]; linarith
  · rw [le_div_iff₀ (by positivity)]; linarith

theorem cutT_zero {a b ε t : ℝ} (hε : 0 < ε) (h : t ≤ a - 2 * ε / 3 ∨ b + 2 * ε / 3 ≤ t) :
    cutT a b ε t = 0 := by
  unfold cutT
  rcases h with h | h
  · rw [Real.smoothTransition.zero_of_nonpos, zero_mul]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  · rw [Real.smoothTransition.zero_of_nonpos (x := ((b + 2 * ε / 3) - t) / (ε / 3)), mul_zero]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)

/-- The integer spatial shift bringing a point into the fundamental cell. -/
def fracShift (x : ST 3) : Fin 3 → ℤ := fun i => ⌊x i.succ⌋

theorem add_sshift_neg_frac (x : ST 3) (i : Fin 3) :
    (x + sshift (-fracShift x)) i.succ = x i.succ - ⌊x i.succ⌋ := by
  simp [sshift, fracShift, PeriodicCube.zvec, sub_eq_add_neg]

theorem add_sshift_zero (x : ST 3) (k : Fin 3 → ℤ) : (x + sshift k) 0 = x 0 := by
  simp [sshift]

/-- **A slab of smoothness around a closed slab.**  If a spatially periodic field is smooth at
every point of an open set containing the closed slab `[a, b] × ℝ^d`, it is smooth at every point
of a thickened open slab `(a - ε, b + ε) × ℝ^d`. -/
theorem exists_smooth_slab {f : ST 3 → ℝ} (hp : IsSPeriodic f) {U : Set (ST 3)} (hU : IsOpen U)
    {a b : ℝ} (hab : a ≤ b) (hsl : ∀ x : ST 3, x 0 ∈ Icc a b → x ∈ U)
    (hf : ∀ x ∈ U, ContDiffAt ℝ ∞ f x) :
    ∃ ε > 0, ∀ x : ST 3, x 0 ∈ Ioo (a - ε) (b + ε) → ContDiffAt ℝ ∞ f x := by
  set lo : ST 3 := Fin.cons a 0 with hlo
  set hi : ST 3 := Fin.cons b 1 with hhi
  have hK : IsCompact (Icc lo hi) := isCompact_Icc
  have hKU : Icc lo hi ⊆ U := fun x hx => hsl x ⟨by simpa [hlo] using hx.1 0,
    by simpa [hhi] using hx.2 0⟩
  obtain ⟨ε, hε, hth⟩ := hK.exists_cthickening_subset_open hU hKU
  refine ⟨ε, hε, fun x hx => ?_⟩
  set k := fracShift x with hk
  set x' : ST 3 := x + sshift (-k) with hx'
  -- the shifted point is within `ε` of the compact cell
  set c : ℝ := max a (min b (x 0)) with hc
  set y : ST 3 := Fin.cons c (fun i => x' i.succ) with hy
  have hyK : y ∈ Icc lo hi := by
    constructor
    · intro i
      induction i using Fin.cases with
      | zero => simp [hy, hlo, hc]
      | succ i =>
        simp only [hy, hlo, Fin.cons_succ, Pi.zero_apply]
        rw [hx', add_sshift_neg_frac]
        exact sub_nonneg.2 (Int.floor_le _)
    · intro i
      induction i using Fin.cases with
      | zero => simp [hy, hhi, hc, hab]
      | succ i =>
        simp only [hy, hhi, Fin.cons_succ, Pi.one_apply]
        rw [hx', add_sshift_neg_frac]
        have := Int.lt_floor_add_one (x i.succ)
        linarith
  have hdist : dist x' y ≤ ε := by
    rw [dist_pi_le_iff hε.le]
    intro i
    induction i using Fin.cases with
    | zero =>
      simp only [hy, Fin.cons_zero, hx', add_sshift_zero, Real.dist_eq]
      have h1 := hx.1
      have h2 := hx.2
      rw [abs_le]
      simp only [hc]
      rcases le_total (x 0) b with h | h
      · rw [min_eq_right h]
        rcases le_total a (x 0) with h' | h'
        · rw [max_eq_right h']; constructor <;> linarith
        · rw [max_eq_left h']; constructor <;> linarith
      · rw [min_eq_left h, max_eq_right hab]; constructor <;> linarith
    | succ i => simp [hy, hε.le]
  have hx'U : x' ∈ U := hth (Metric.mem_cthickening_of_dist_le x' y ε _ hyK hdist)
  have hfx' := hf x' hx'U
  -- transport by the period
  have hper : (f ∘ fun z : ST 3 => z + sshift (-k)) = f := funext fun z => hp (-k) z
  have htr : ContDiffAt ℝ ∞ (fun z : ST 3 => z + sshift (-k)) x :=
    (contDiff_id.add contDiff_const).contDiffAt
  have := ContDiffAt.comp (g := f) x hfx' htr
  rw [hper] at this
  exact this

/-- **Slice norms are continuous near a closed slab of smoothness.**  If a spatially periodic field
is smooth at every point of an open set containing `[a, b] × ℝ^d`, then `t ↦ Q_k(f)(t)` is
continuous on `[a, b]`. -/
theorem continuousOn_Q_of_smooth_near {f : ST 3 → ℝ} (hp : IsSPeriodic f) {U : Set (ST 3)}
    (hU : IsOpen U) {a b : ℝ} (hab : a ≤ b) (hsl : ∀ x : ST 3, x 0 ∈ Icc a b → x ∈ U)
    (hf : ∀ x ∈ U, ContDiffAt ℝ ∞ f x) (k : ℕ) : ContinuousOn (Q k f) (Icc a b) := by
  obtain ⟨ε, hε, hsm⟩ := exists_smooth_slab hp hU hab hsl hf
  set g : ST 3 → ℝ := fun x => cutT a b ε (x 0) * f x with hg
  have hgs : ContDiff ℝ ∞ g := by
    refine contDiff_iff_contDiffAt.2 fun x => ?_
    by_cases hx : x 0 ∈ Ioo (a - ε) (b + ε)
    · exact (((contDiff_cutT a b ε).comp (contDiff_apply ℝ ℝ (0 : Fin 4))).contDiffAt).mul
        (hsm x hx)
    · -- the cutoff vanishes near `x`
      have hx' : x 0 ≤ a - ε ∨ b + ε ≤ x 0 := by
        by_contra h
        push Not at h
        exact hx ⟨h.1, h.2⟩
      have hO : IsOpen {z : ST 3 | z 0 < a - 2 * ε / 3 ∨ b + 2 * ε / 3 < z 0} :=
        (isOpen_lt (continuous_apply 0) continuous_const).union
          (isOpen_lt continuous_const (continuous_apply 0))
      have hxO : x ∈ {z : ST 3 | z 0 < a - 2 * ε / 3 ∨ b + 2 * ε / 3 < z 0} := by
        rcases hx' with h | h
        · left; show x 0 < a - 2 * ε / 3; linarith
        · right; show b + 2 * ε / 3 < x 0; linarith
      have hev : g =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
        filter_upwards [hO.mem_nhds hxO] with z hz
        show cutT a b ε (z 0) * f z = 0
        rw [cutT_zero hε (hz.imp le_of_lt le_of_lt), zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  have hO : IsOpen {z : ST 3 | z 0 ∈ Ioo (a - ε / 3) (b + ε / 3)} :=
    isOpen_Ioo.preimage (continuous_apply 0)
  have heq : EqOn f g {z : ST 3 | z 0 ∈ Ioo (a - ε / 3) (b + ε / 3)} := by
    intro z hz
    show f z = cutT a b ε (z 0) * f z
    rw [cutT_one hε hz.1.le hz.2.le, one_mul]
  have hQ : EqOn (Q k g) (Q k f) (Icc a b) := by
    intro t ht
    refine (Q_congr fun w _ y => ?_).symm
    refine GenReadout.sd_eqOn hO heq w ?_
    show (Fin.cons t y : ST 3) 0 ∈ Ioo (a - ε / 3) (b + ε / 3)
    simp only [Fin.cons_zero]
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  exact ((continuous_Q k hgs).continuousOn).congr hQ.symm

/-- **Extension of an open-interval bound to the closed interval by continuity.** -/
theorem le_on_Icc_of_Ioo {h : ℝ → ℝ} {a b B : ℝ} (hab : a < b) (hc : ContinuousOn h (Icc a b))
    (hb : ∀ t ∈ Ioo a b, h t ≤ B) : ∀ t ∈ Icc a b, h t ≤ B := by
  intro t ht
  rw [← closure_Ioo hab.ne] at ht hc
  exact le_on_closure hb hc continuousOn_const ht

end Continuity

end RenewalGeometry.GenNorms
