/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Smooth cardinal quasi-interpolation (a mollified multilinear interpolant)

Generic infrastructure for the smooth comparison reconstruction of `eq:smooth-reconstruction`
(Einstein–Standard-Model action-closure manuscript, "A finite smooth comparison reconstruction":
`𝒥_h f = ρ_h * I_h f`, `I_h` a piecewise-affine nodal interpolant, `ρ_h` a fixed mollifier at
scale `h`).

## The kernel

* `bump t = s(t+1) - s(t)` (`s = Real.smoothTransition`) is a smooth nonnegative bump supported in
  `[-1,1]` whose integer translates form a partition of unity (`sum_bump_shift`).
* `kern t = ∫_{t-1/2}^{t+1/2} bump` is the convolution of `bump` with the unit box, i.e. the
  convolution of the hat function `Λ = 1_{[-½,½]} * 1_{[-½,½]}` with the mollifier
  `1_{[-½,½]} * …`; it is smooth, supported in `[-3/2, 3/2]`, its translates form a partition of
  unity (`sum_kern_shift`), and its derivative `kernD t = bump(t+½) - bump(t-½)` satisfies the
  two moment identities `Σ_j kernD(t-j) = 0`, `Σ_j (j-t) kernD(t-j) = 1` (`sum_kernD_shift`,
  `sum_moment_kernD_shift`): the translates reproduce affine functions to first order.
* `kernel u = Π_i kern(u_i)` on `ℝ^d` (tensor product: the mollified multilinear `Q1`
  interpolant), with the multi-dimensional identities `sum_kernel_win`, `sum_kernelD_win`,
  `sum_kernelD_moment_win`.

## The reconstruction

`recon h g y = Σ_{j ∈ ℤ^d} kernel(y/h - j) g(j)` (a locally finite sum, `win` the window of the
`8^d` relevant nodes) for nodal data `g : ℤ^d → W` in any real normed space.

* `contDiff_recon`, `hasFDerivAt_recon` (derivative `reconD`): the reconstruction is `C^∞`;
* `recon_mem`: it takes values in any real subspace containing the data;
* `recon_add_shift`: periodic data give periodic reconstructions;
* `recon_eq_zero_of`: locality (only nodes within `3/2` mesh widths contribute);
* **`eq:smooth-reconstruction-estimate`** for the samples `g j = f(h j)` of a `C^{1,1}` function
  (`‖f'‖ ≤ M₁`, `f'` `M₂`-Lipschitz):
  - `norm_recon_samp_sub_le`: `‖𝒥_h f - f‖_∞ ≤ C h M₁`,
  - `norm_reconD_samp_sub_le`: `‖D𝒥_h f - Df‖_∞ ≤ C h M₂`,
  - `norm_reconD_samp_sub_reconD_le`: `D𝒥_h f` is `C M₂`-Lipschitz (`‖𝒥_h f‖_{W^{2,∞}} ≤ C‖f‖_{C²}`),
  with constants depending only on `d`.

Disclosed rendering: the paper mollifies the simplicial piecewise-affine interpolant; here the
nodal basis is the tensor-product (multilinear, `Q1`) hat basis and the mollifier is the tensor
product of `1_{[-½,½]} * bump`, so that `𝒥_h` is a cardinal quasi-interpolant with a smooth
compactly supported kernel.  Only the properties listed above (smoothness, locality, partition of
unity and first-order affine reproduction) enter the estimates.
-/

open Set Finset Filter Topology MeasureTheory
open scoped ContDiff

noncomputable section

namespace RenewalGeometry.CardinalQI

/-! ### The one-dimensional bump and kernel -/

/-- The smooth bump `ψ(t) = s(t+1) - s(t)`, `s` the smooth transition. -/
def bump (t : ℝ) : ℝ := Real.smoothTransition (t + 1) - Real.smoothTransition t

theorem contDiff_bump : ContDiff ℝ ∞ bump := by
  have h : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff (n := ⊤)
  exact (h.comp (contDiff_id.add contDiff_const)).sub h

theorem continuous_bump : Continuous bump := contDiff_bump.continuous

theorem bump_eq_zero_of_le {t : ℝ} (ht : t ≤ -1) : bump t = 0 := by
  unfold bump
  rw [Real.smoothTransition.zero_of_nonpos (by linarith),
    Real.smoothTransition.zero_of_nonpos (by linarith), sub_zero]

theorem bump_eq_zero_of_ge {t : ℝ} (ht : 1 ≤ t) : bump t = 0 := by
  unfold bump
  rw [Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.one_of_one_le ht, sub_self]

theorem bump_eq_zero_of_abs {t : ℝ} (ht : 1 ≤ |t|) : bump t = 0 := by
  rcases le_abs'.mp ht with h | h
  · exact bump_eq_zero_of_le h
  · exact bump_eq_zero_of_ge h

/-- Telescoping over a window of consecutive integers. -/
theorem sum_range_telescope (G : ℤ → ℝ) (lo : ℤ) (m : ℕ) :
    ∑ k ∈ range m, (G (lo + k - 1) - G (lo + k)) = G (lo - 1) - G (lo + m - 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [sum_range_succ, ih]
      push_cast
      ring_nf

/-- **The translates of the bump form a partition of unity** (on any window of integers
containing `[t-2, t+2]`). -/
theorem sum_bump_shift {t : ℝ} {lo : ℤ} {m : ℕ} (hlo : (lo : ℝ) ≤ t)
    (hhi : t + 1 ≤ (lo : ℝ) + m) :
    ∑ k ∈ range m, bump (t - (lo + k : ℤ)) = 1 := by
  have e : ∀ k : ℕ, bump (t - (lo + k : ℤ)) =
      (fun j : ℤ => Real.smoothTransition (t - j)) (lo + k - 1) -
        (fun j : ℤ => Real.smoothTransition (t - j)) (lo + k) := by
    intro k
    simp only [bump]
    push_cast
    ring_nf
  rw [Finset.sum_congr rfl (fun k _ => e k),
    sum_range_telescope (fun j : ℤ => Real.smoothTransition (t - j))]
  push_cast
  rw [Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.zero_of_nonpos (by linarith), sub_zero]

/-- The primitive `Ψ(x) = ∫_0^x ψ`. -/
def bumpPrim (x : ℝ) : ℝ := ∫ s in (0 : ℝ)..x, bump s

theorem hasDerivAt_bumpPrim (x : ℝ) : HasDerivAt bumpPrim (bump x) x :=
  (continuous_bump.integral_hasStrictDerivAt 0 x).hasDerivAt

theorem contDiff_bumpPrim : ContDiff ℝ ∞ bumpPrim := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun x => (hasDerivAt_bumpPrim x).differentiableAt, ?_⟩
  have : deriv bumpPrim = bump := funext fun x => (hasDerivAt_bumpPrim x).deriv
  rw [this]
  exact contDiff_bump

theorem bumpPrim_sub (a b : ℝ) : bumpPrim b - bumpPrim a = ∫ s in a..b, bump s :=
  intervalIntegral.integral_interval_sub_left (continuous_bump.intervalIntegrable _ _)
    (continuous_bump.intervalIntegrable _ _)

/-- `∫_{-1}^{1} ψ = 1`. -/
theorem integral_bump : ∫ s in (-1 : ℝ)..1, bump s = 1 := by
  have hs : Continuous Real.smoothTransition := Real.smoothTransition.continuous
  have h1 : ∫ s in (-1 : ℝ)..1, bump s =
      (∫ s in (-1 : ℝ)..1, Real.smoothTransition (s + 1)) -
        ∫ s in (-1 : ℝ)..1, Real.smoothTransition s := by
    unfold bump
    exact intervalIntegral.integral_sub ((hs.comp (continuous_id.add continuous_const)).intervalIntegrable _ _)
      (hs.intervalIntegrable _ _)
  rw [h1, intervalIntegral.integral_comp_add_right (fun s => Real.smoothTransition s)]
  norm_num
  have a1 : ∫ s in (0 : ℝ)..2, Real.smoothTransition s =
      (∫ s in (0 : ℝ)..1, Real.smoothTransition s) + ∫ s in (1 : ℝ)..2, Real.smoothTransition s :=
    (intervalIntegral.integral_add_adjacent_intervals (hs.intervalIntegrable _ _)
      (hs.intervalIntegrable _ _)).symm
  have a2 : ∫ s in (-1 : ℝ)..1, Real.smoothTransition s =
      (∫ s in (-1 : ℝ)..0, Real.smoothTransition s) + ∫ s in (0 : ℝ)..1, Real.smoothTransition s :=
    (intervalIntegral.integral_add_adjacent_intervals (hs.intervalIntegrable _ _)
      (hs.intervalIntegrable _ _)).symm
  have a3 : ∫ s in (1 : ℝ)..2, Real.smoothTransition s = 1 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (1 : ℝ)) (fun s hs' => by
      rw [Set.uIcc_of_le (by norm_num)] at hs'
      exact Real.smoothTransition.one_of_one_le hs'.1)]
    norm_num
  have a4 : ∫ s in (-1 : ℝ)..0, Real.smoothTransition s = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun s hs' => by
      rw [Set.uIcc_of_le (by norm_num)] at hs'
      exact Real.smoothTransition.zero_of_nonpos hs'.2)]
    simp
  rw [a1, a2, a3, a4]
  ring

/-- `∫_a^b ψ = 1` whenever `a ≤ -1` and `1 ≤ b`. -/
theorem integral_bump_of {a b : ℝ} (ha : a ≤ -1) (hb : 1 ≤ b) : ∫ s in a..b, bump s = 1 := by
  have hi : ∀ x y : ℝ, IntervalIntegrable bump volume x y :=
    fun x y => continuous_bump.intervalIntegrable _ _
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi a (-1)) (hi (-1) b),
    ← intervalIntegral.integral_add_adjacent_intervals (hi (-1) 1) (hi 1 b), integral_bump]
  have z1 : ∫ s in a..(-1), bump s = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun s hs' => by
      rw [Set.uIcc_of_le ha] at hs'
      exact bump_eq_zero_of_le hs'.2)]
    simp
  have z2 : ∫ s in (1 : ℝ)..b, bump s = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun s hs' => by
      rw [Set.uIcc_of_le hb] at hs'
      exact bump_eq_zero_of_ge hs'.1)]
    simp
  rw [z1, z2]
  ring

/-- **The one-dimensional kernel** `φ(t) = ∫_{t-1/2}^{t+1/2} ψ` (box ∗ bump). -/
def kern (t : ℝ) : ℝ := bumpPrim (t + 1 / 2) - bumpPrim (t - 1 / 2)

/-- Its derivative `φ'(t) = ψ(t+½) - ψ(t-½)`. -/
def kernD (t : ℝ) : ℝ := bump (t + 1 / 2) - bump (t - 1 / 2)

theorem hasDerivAt_kern (t : ℝ) : HasDerivAt kern (kernD t) t := by
  have h1 : HasDerivAt (fun x => bumpPrim (x + 1 / 2)) (bump (t + 1 / 2)) t :=
    (hasDerivAt_bumpPrim (t + 1 / 2)).comp_add_const t (1 / 2)
  have h2 : HasDerivAt (fun x => bumpPrim (x - 1 / 2)) (bump (t - 1 / 2)) t :=
    (hasDerivAt_bumpPrim (t - 1 / 2)).comp_sub_const t (1 / 2)
  exact h1.sub h2

theorem contDiff_kern : ContDiff ℝ ∞ kern := by
  unfold kern
  exact (contDiff_bumpPrim.comp (contDiff_id.add contDiff_const)).sub
    (contDiff_bumpPrim.comp (contDiff_id.sub contDiff_const))

theorem contDiff_kernD : ContDiff ℝ ∞ kernD := by
  unfold kernD
  exact (contDiff_bump.comp (contDiff_id.add contDiff_const)).sub
    (contDiff_bump.comp (contDiff_id.sub contDiff_const))

theorem kern_eq_integral (t : ℝ) : kern t = ∫ s in (t - 1 / 2)..(t + 1 / 2), bump s := by
  unfold kern; rw [bumpPrim_sub]

theorem kern_eq_zero_of_abs {t : ℝ} (ht : 3 / 2 ≤ |t|) : kern t = 0 := by
  rw [kern_eq_integral]
  rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun s hs => ?_)]
  · simp
  rw [Set.uIcc_of_le (by linarith)] at hs
  apply bump_eq_zero_of_abs
  rcases le_abs'.mp ht with h | h
  · rw [abs_of_neg (by linarith [hs.2])]; linarith [hs.2]
  · rw [abs_of_pos (by linarith [hs.1])]; linarith [hs.1]

theorem kernD_eq_zero_of_abs {t : ℝ} (ht : 3 / 2 ≤ |t|) : kernD t = 0 := by
  unfold kernD
  rcases le_abs'.mp ht with h | h
  · rw [bump_eq_zero_of_le (by linarith), bump_eq_zero_of_le (by linarith), sub_zero]
  · rw [bump_eq_zero_of_ge (by linarith), bump_eq_zero_of_ge (by linarith), sub_zero]

/-- **Partition of unity of the kernel translates.** -/
theorem sum_kern_shift {t : ℝ} {lo : ℤ} {m : ℕ} (hlo : (lo : ℝ) ≤ t - 2)
    (hhi : t + 2 ≤ (lo : ℝ) + m - 1) :
    ∑ k ∈ range m, kern (t - (lo + k : ℤ)) = 1 := by
  have e' : ∀ k : ℕ, kern (t - (lo + k : ℤ)) =
      (fun j : ℤ => bumpPrim (t - j - 1 / 2)) (lo + k - 1) -
        (fun j : ℤ => bumpPrim (t - j - 1 / 2)) (lo + k) := by
    intro k
    simp only [kern]
    push_cast
    ring_nf
  rw [Finset.sum_congr rfl (fun k _ => e' k),
    sum_range_telescope (fun j : ℤ => bumpPrim (t - j - 1 / 2))]
  rw [bumpPrim_sub]
  push_cast
  exact integral_bump_of (by linarith) (by linarith)

/-- `Σ_j φ'(t - j) = 0`. -/
theorem sum_kernD_shift {t : ℝ} {lo : ℤ} {m : ℕ} (hlo : (lo : ℝ) ≤ t - 2)
    (hhi : t + 2 ≤ (lo : ℝ) + m - 1) :
    ∑ k ∈ range m, kernD (t - (lo + k : ℤ)) = 0 := by
  simp only [kernD, sum_sub_distrib]
  have h1 := sum_bump_shift (t := t + 1 / 2) (lo := lo) (m := m) (by linarith) (by linarith)
  have h2 := sum_bump_shift (t := t - 1 / 2) (lo := lo) (m := m) (by linarith) (by linarith)
  have e1 : ∀ k : ℕ, t - ((lo + k : ℤ) : ℝ) + 1 / 2 = t + 1 / 2 - ((lo + k : ℤ) : ℝ) :=
    fun k => by ring
  have e2 : ∀ k : ℕ, t - ((lo + k : ℤ) : ℝ) - 1 / 2 = t - 1 / 2 - ((lo + k : ℤ) : ℝ) :=
    fun k => by ring
  simp_rw [e1, e2, h1, h2, sub_self]

/-- **First-order affine reproduction**: `Σ_j (j - t) φ'(t - j) = 1`. -/
theorem sum_moment_kernD_shift {t : ℝ} {lo : ℤ} {m : ℕ} (hlo : (lo : ℝ) ≤ t - 2)
    (hhi : t + 2 ≤ (lo : ℝ) + m - 1) :
    ∑ k ∈ range m, (((lo + k : ℤ) : ℝ) - t) * kernD (t - (lo + k : ℤ)) = 1 := by
  set b : ℤ → ℝ := fun j => bump (t - j + 1 / 2) with hb
  have hk : ∀ k : ℕ, kernD (t - (lo + k : ℤ)) = b (lo + k) - b (lo + k + 1) := by
    intro k; simp only [kernD, hb]; push_cast; ring_nf
  have key : ∀ k : ℕ, (((lo + k : ℤ) : ℝ) - t) * kernD (t - (lo + k : ℤ)) =
      ((((lo + k : ℤ) : ℝ) - t) * b (lo + k) -
        (((lo + (k + 1 : ℕ) : ℤ) : ℝ) - t) * b (lo + (k + 1 : ℕ))) +
        b (lo + (k + 1 : ℕ)) := by
    intro k; rw [hk]; push_cast; ring_nf
  simp_rw [key]
  rw [sum_add_distrib, sum_range_sub']
  have b0 : b lo = 0 := by
    simp only [hb]; exact bump_eq_zero_of_ge (by linarith)
  have bm : b (lo + (m : ℕ)) = 0 := by
    simp only [hb]; push_cast; exact bump_eq_zero_of_le (by linarith)
  have hsum : ∑ k ∈ range m, b (lo + (k + 1 : ℕ)) = 1 := by
    have := sum_bump_shift (t := t - 1 / 2) (lo := lo) (m := m) (by linarith) (by linarith)
    rw [← this]
    refine sum_congr rfl fun k _ => ?_
    simp only [hb]; push_cast; ring_nf
  simp only [Nat.cast_zero, add_zero] at b0 ⊢
  rw [b0, bm, hsum]
  ring

/-! ### Windows of integers -/

/-- The one-dimensional window `{⌊t⌋ - 3, …, ⌊t⌋ + 4}`. -/
def win1 (t : ℝ) : Finset ℤ := (range 8).image fun k : ℕ => ⌊t⌋ - 3 + (k : ℤ)

theorem sum_win1 (t : ℝ) (f : ℤ → ℝ) :
    ∑ j ∈ win1 t, f j = ∑ k ∈ range 8, f (⌊t⌋ - 3 + (k : ℤ)) := by
  unfold win1
  rw [sum_image]
  intro a _ b _ hab
  simpa using hab

theorem mem_win1 {t : ℝ} {j : ℤ} (h1 : ⌊t⌋ - 3 ≤ j) (h2 : j ≤ ⌊t⌋ + 4) : j ∈ win1 t := by
  unfold win1
  rw [Finset.mem_image]
  refine ⟨(j - (⌊t⌋ - 3)).toNat, ?_, ?_⟩
  · rw [Finset.mem_range]; omega
  · omega

theorem abs_sub_le_of_mem_win1 {t : ℝ} {j : ℤ} (hj : j ∈ win1 t) : |(j : ℝ) - t| ≤ 4 := by
  unfold win1 at hj
  rw [Finset.mem_image] at hj
  obtain ⟨k, hk, rfl⟩ := hj
  rw [Finset.mem_range] at hk
  have h1 := Int.floor_le t
  have h2 := Int.lt_floor_add_one t
  have hk' : (k : ℝ) ≤ 7 := by exact_mod_cast Nat.lt_succ_iff.mp hk
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  rw [abs_le]
  push_cast
  constructor <;> linarith

theorem card_win1_le (t : ℝ) : (win1 t).card ≤ 8 := by
  unfold win1; exact card_image_le.trans (by simp)

theorem win1_bounds {t t' : ℝ} (ht : |t' - t| ≤ 1) :
    ((⌊t⌋ - 3 : ℤ) : ℝ) ≤ t' - 2 ∧ t' + 2 ≤ ((⌊t⌋ - 3 : ℤ) : ℝ) + (8 : ℕ) - 1 := by
  have h1 := Int.floor_le t
  have h2 := Int.lt_floor_add_one t
  rw [abs_le] at ht
  push_cast
  constructor <;> linarith [ht.1, ht.2]

theorem sum_win1_kern {t t' : ℝ} (ht : |t' - t| ≤ 1) : ∑ j ∈ win1 t, kern (t' - j) = 1 := by
  rw [sum_win1]
  obtain ⟨a, b⟩ := win1_bounds ht
  have := sum_kern_shift a b
  simpa using this

theorem sum_win1_kernD {t t' : ℝ} (ht : |t' - t| ≤ 1) : ∑ j ∈ win1 t, kernD (t' - j) = 0 := by
  rw [sum_win1]
  obtain ⟨a, b⟩ := win1_bounds ht
  have := sum_kernD_shift a b
  simpa using this

theorem sum_win1_moment {t t' : ℝ} (ht : |t' - t| ≤ 1) :
    ∑ j ∈ win1 t, kernD (t' - j) * ((j : ℝ) - t') = 1 := by
  rw [sum_win1 t (fun j => kernD (t' - j) * ((j : ℝ) - t'))]
  obtain ⟨a, b⟩ := win1_bounds ht
  have := sum_moment_kernD_shift a b
  rw [← this]
  refine sum_congr rfl fun k _ => ?_
  push_cast
  ring

/-! ### The `d`-dimensional kernel -/

variable {d : ℕ}

/-- The integer lattice point `j ∈ ℤ^d` as a point of `ℝ^d`. -/
def jc (j : Fin d → ℤ) : Fin d → ℝ := fun i => (j i : ℝ)

/-- **The tensor-product kernel** `Φ(u) = Π_i φ(u_i)`. -/
def kernel (u : Fin d → ℝ) : ℝ := ∏ i, kern (u i)

/-- The derivative `DΦ(u) = Σ_i (Π_{l ≠ i} φ(u_l)) φ'(u_i) dx_i`. -/
def kernelD (u : Fin d → ℝ) : (Fin d → ℝ) →L[ℝ] ℝ :=
  ∑ i, (∏ l ∈ univ.erase i, kern (u l)) • (kernD (u i) • ContinuousLinearMap.proj i)

theorem hasFDerivAt_kernel (u : Fin d → ℝ) : HasFDerivAt kernel (kernelD u) u := by
  have h : ∀ i ∈ (univ : Finset (Fin d)), HasFDerivAt (fun v : Fin d → ℝ => kern (v i))
      (kernD (u i) • (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ)) u := fun i _ =>
    HasDerivAt.comp_hasFDerivAt (f := fun v : Fin d → ℝ => v i) u (hasDerivAt_kern (u i))
      (hasFDerivAt_apply i u)
  have := HasFDerivAt.finsetProd h
  exact this

theorem fderiv_kernel : fderiv ℝ (kernel (d := d)) = kernelD :=
  funext fun u => (hasFDerivAt_kernel u).fderiv

theorem contDiff_kernel : ContDiff ℝ ∞ (kernel (d := d)) := by
  unfold kernel
  exact contDiff_prod fun i _ => contDiff_kern.comp (contDiff_apply ℝ ℝ i)

theorem kernel_eq_zero {u : Fin d → ℝ} {i : Fin d} (hi : 3 / 2 ≤ |u i|) : kernel u = 0 :=
  prod_eq_zero (mem_univ i) (kern_eq_zero_of_abs hi)

theorem kernelD_eq_zero {u : Fin d → ℝ} {i : Fin d} (hi : 3 / 2 ≤ |u i|) : kernelD u = 0 := by
  unfold kernelD
  refine sum_eq_zero fun l _ => ?_
  by_cases hl : l = i
  · subst hl; rw [kernD_eq_zero_of_abs hi, zero_smul, smul_zero]
  · rw [prod_eq_zero (mem_erase.mpr ⟨Ne.symm hl, mem_univ i⟩) (kern_eq_zero_of_abs hi),
      zero_smul]

theorem kernel_support_subset : Function.support (kernel (d := d)) ⊆
    Metric.closedBall 0 (3 / 2) := by
  intro u hu
  rw [Metric.mem_closedBall, dist_zero_right]
  refine (pi_norm_le_iff_of_nonneg (by norm_num)).mpr fun i => ?_
  by_contra hc
  push_neg at hc
  rw [Real.norm_eq_abs] at hc
  exact hu (kernel_eq_zero hc.le)

theorem hasCompactSupport_kernel : HasCompactSupport (kernel (d := d)) :=
  HasCompactSupport.intro (isCompact_closedBall 0 (3 / 2)) fun u hu => by
    by_contra h
    exact hu (kernel_support_subset h)

/-- Uniform bounds for the kernel and its derivative, and the Lipschitz constant of `DΦ`. -/
theorem exists_kernel_bounds : ∃ B₀ B₁ L : ℝ, 0 ≤ B₀ ∧ 0 ≤ B₁ ∧ 0 ≤ L ∧
    (∀ u : Fin d → ℝ, |kernel u| ≤ B₀) ∧ (∀ u : Fin d → ℝ, ‖kernelD u‖ ≤ B₁) ∧
    ∀ u v : Fin d → ℝ, ‖kernelD u - kernelD v‖ ≤ L * ‖u - v‖ := by
  obtain ⟨B₀, hB₀⟩ := hasCompactSupport_kernel.exists_bound_of_continuous
    (contDiff_kernel (d := d)).continuous
  have hD : HasCompactSupport (fderiv ℝ (kernel (d := d))) := hasCompactSupport_kernel.fderiv ℝ
  have hDc : ContDiff ℝ ∞ (fderiv ℝ (kernel (d := d))) :=
    contDiff_kernel.fderiv_right (m := ∞) le_rfl
  obtain ⟨B₁, hB₁⟩ := hD.exists_bound_of_continuous hDc.continuous
  obtain ⟨L, hL⟩ := hDc.lipschitzWith_of_hasCompactSupport hD (by simp)
  rw [fderiv_kernel] at hB₁ hL
  refine ⟨max B₀ 0, max B₁ 0, L, le_max_right _ _, le_max_right _ _, L.2, fun u => ?_,
    fun u => (hB₁ u).trans (le_max_left _ _), fun u v => ?_⟩
  · have := hB₀ u; rw [Real.norm_eq_abs] at this; exact this.trans (le_max_left _ _)
  · rw [← dist_eq_norm, ← dist_eq_norm]; exact hL.dist_le_mul u v

/-! ### The `d`-dimensional window and the moment identities -/

/-- The window `Π_i win1(u_i)` of `8^d` lattice points around `u`. -/
def win (u : Fin d → ℝ) : Finset (Fin d → ℤ) := Fintype.piFinset fun i => win1 (u i)

theorem card_win_le (u : Fin d → ℝ) : (win u).card ≤ 8 ^ d := by
  unfold win
  rw [Fintype.card_piFinset]
  calc ∏ i, (win1 (u i)).card ≤ ∏ _i : Fin d, 8 :=
        prod_le_prod' fun i _ => card_win1_le (u i)
    _ = 8 ^ d := by simp

theorem norm_jc_sub_le_of_mem_win {u : Fin d → ℝ} {j : Fin d → ℤ} (hj : j ∈ win u) :
    ‖jc j - u‖ ≤ 4 := by
  refine (pi_norm_le_iff_of_nonneg (by norm_num)).mpr fun i => ?_
  rw [Real.norm_eq_abs]
  exact abs_sub_le_of_mem_win1 (Fintype.mem_piFinset.mp hj i)

theorem abs_sub_le_of_norm {u u' : Fin d → ℝ} (h : ‖u' - u‖ ≤ 1) (i : Fin d) :
    |u' i - u i| ≤ 1 := by
  have := norm_le_pi_norm (u' - u) i
  rw [Real.norm_eq_abs] at this
  exact this.trans h

/-- Lattice points where the kernel at `u'` does not vanish lie in the window of `u`. -/
theorem mem_win_of {u u' : Fin d → ℝ} (h : ‖u' - u‖ ≤ 1) {j : Fin d → ℤ}
    (hj : ∀ i, |u' i - j i| < 3 / 2) : j ∈ win u := by
  refine Fintype.mem_piFinset.mpr fun i => ?_
  have h1 := abs_sub_le_of_norm h i
  have h2 := hj i
  rw [abs_lt] at h2
  rw [abs_le] at h1
  have f1 := Int.floor_le (u i)
  have f2 := Int.lt_floor_add_one (u i)
  apply mem_win1
  · have : ((⌊u i⌋ - 3 : ℤ) : ℝ) < j i := by push_cast; linarith
    exact_mod_cast this.le
  · have : (j i : ℝ) < ((⌊u i⌋ + 4 : ℤ) : ℝ) := by push_cast; linarith
    exact_mod_cast this.le

theorem support_kernel_subset_win {u u' : Fin d → ℝ} (h : ‖u' - u‖ ≤ 1) :
    (Function.support fun j : Fin d → ℤ => kernel (u' - jc j)) ⊆ win u := by
  intro j hj
  refine mem_win_of h fun i => ?_
  by_contra hc
  push_neg at hc
  exact hj (kernel_eq_zero (i := i) (by simpa [jc] using hc))

theorem support_kernelD_subset_win {u u' : Fin d → ℝ} (h : ‖u' - u‖ ≤ 1) :
    (Function.support fun j : Fin d → ℤ => kernelD (u' - jc j)) ⊆ win u := by
  intro j hj
  refine mem_win_of h fun i => ?_
  by_contra hc
  push_neg at hc
  exact hj (kernelD_eq_zero (i := i) (by simpa [jc] using hc))

theorem kernel_sub_jc (u : Fin d → ℝ) (j : Fin d → ℤ) :
    kernel (u - jc j) = ∏ i, kern (u i - j i) := rfl

/-- **Partition of unity**: `Σ_{j ∈ win u} Φ(u' - j) = 1` for `‖u' - u‖ ≤ 1`. -/
theorem sum_kernel_win {u u' : Fin d → ℝ} (h : ‖u' - u‖ ≤ 1) :
    ∑ j ∈ win u, kernel (u' - jc j) = 1 := by
  simp_rw [kernel_sub_jc]
  unfold win
  rw [← prod_univ_sum (fun i => win1 (u i)) (fun i k => kern (u' i - k))]
  exact prod_eq_one fun i _ => sum_win1_kern (abs_sub_le_of_norm h i)

theorem kernelD_apply (u v : Fin d → ℝ) :
    kernelD u v = ∑ i, v i * ∏ l, (if l = i then kernD (u l) else kern (u l)) := by
  unfold kernelD
  rw [ContinuousLinearMap.sum_apply]
  refine sum_congr rfl fun i _ => ?_
  rw [← mul_prod_erase univ _ (mem_univ i)]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]

  have : ∏ l ∈ univ.erase i, (if l = i then kernD (u l) else kern (u l)) =
      ∏ l ∈ univ.erase i, kern (u l) :=
    prod_congr rfl fun l hl => if_neg (ne_of_mem_erase hl)
  simp only [this, ↓reduceIte]
  ring

/-- **`Σ_{j ∈ win u} DΦ(u' - j) = 0`** for `‖u' - u‖ ≤ 1`. -/
theorem sum_kernelD_win {u u' : Fin d → ℝ} (h : ‖u' - u‖ ≤ 1) :
    ∑ j ∈ win u, kernelD (u' - jc j) = 0 := by
  ext1 v
  rw [ContinuousLinearMap.sum_apply, ContinuousLinearMap.zero_apply]
  simp_rw [kernelD_apply]
  rw [sum_comm]
  refine sum_eq_zero fun i _ => ?_
  rw [← mul_sum]
  have e : ∑ j ∈ win u, ∏ l, (if l = i then kernD ((u' - jc j) l) else kern ((u' - jc j) l)) =
      ∏ l, ∑ k ∈ win1 (u l), (if l = i then kernD (u' l - k) else kern (u' l - k)) := by
    unfold win
    rw [prod_univ_sum]
    rfl
  rw [e, prod_eq_zero (mem_univ i), mul_zero]
  simp only [if_pos rfl]
  exact sum_win1_kernD (abs_sub_le_of_norm h i)

/-- **First-order affine reproduction**: `Σ_{j ∈ win u} DΦ(u' - j)[v] (j - u') = v`. -/
theorem sum_kernelD_moment_win {u u' : Fin d → ℝ} (h : ‖u' - u‖ ≤ 1) (v : Fin d → ℝ) :
    ∑ j ∈ win u, kernelD (u' - jc j) v • (jc j - u') = v := by
  funext m
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  simp_rw [kernelD_apply, sum_mul]
  rw [sum_comm]
  have hi : ∀ i, ∑ j ∈ win u, v i * (∏ l, (if l = i then kernD ((u' - jc j) l)
      else kern ((u' - jc j) l))) * (jc j m - u' m) = v i * (if i = m then 1 else 0) := by
    intro i
    simp_rw [mul_assoc]
    rw [← mul_sum]
    congr 1
    have e : ∑ j ∈ win u, (∏ l, (if l = i then kernD ((u' - jc j) l)
        else kern ((u' - jc j) l))) * (jc j m - u' m) =
        ∏ l, ∑ k ∈ win1 (u l), ((if l = i then kernD (u' l - k) else kern (u' l - k)) *
          (if l = m then ((k : ℝ) - u' m) else 1)) := by
      unfold win
      rw [prod_univ_sum]
      refine sum_congr rfl fun j _ => ?_
      rw [prod_mul_distrib, prod_ite_eq' univ m]
      simp [jc]
    rw [e]
    by_cases him : i = m
    · subst him
      rw [if_pos rfl]
      refine prod_eq_one fun l _ => ?_
      by_cases hl : l = i
      · subst hl
        simp only [if_pos rfl]
        exact sum_win1_moment (abs_sub_le_of_norm h l)
      · simp only [if_neg hl, mul_one]
        exact sum_win1_kern (abs_sub_le_of_norm h l)
    · rw [if_neg him]
      refine prod_eq_zero (mem_univ i) ?_
      simp only [if_pos rfl, if_neg him, mul_one]
      exact sum_win1_kernD (abs_sub_le_of_norm h i)
  rw [sum_congr rfl fun i _ => hi i]
  simp

/-! ### The reconstruction -/

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- **The cardinal quasi-interpolant** `𝒥_h g(y) = Σ_{j ∈ ℤ^d} Φ(y/h - j) g(j)` of nodal data
`g : ℤ^d → W` (a locally finite sum). -/
def recon (h : ℝ) (g : (Fin d → ℤ) → W) (y : Fin d → ℝ) : W :=
  ∑ᶠ j, kernel (h⁻¹ • y - jc j) • g j

/-- Its derivative `D𝒥_h g(y) = Σ_j h⁻¹ DΦ(y/h - j) ⊗ g(j)`. -/
def reconD (h : ℝ) (g : (Fin d → ℤ) → W) (y : Fin d → ℝ) : (Fin d → ℝ) →L[ℝ] W :=
  ∑ᶠ j, h⁻¹ • (kernelD (h⁻¹ • y - jc j)).smulRight (g j)

theorem norm_smul_sub_le {h : ℝ} (hh : 0 < h) {y y' : Fin d → ℝ} (hy : ‖y' - y‖ ≤ h) :
    ‖h⁻¹ • y' - h⁻¹ • y‖ ≤ 1 := by
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hh]
  rw [inv_mul_le_iff₀ hh, mul_one]; exact hy

theorem recon_eq_sum {h : ℝ} (hh : 0 < h) (g : (Fin d → ℤ) → W) {y y' : Fin d → ℝ}
    (hy : ‖y' - y‖ ≤ h) :
    recon h g y' = ∑ j ∈ win (h⁻¹ • y), kernel (h⁻¹ • y' - jc j) • g j := by
  unfold recon
  refine finsum_eq_sum_of_support_subset _ fun j hj => ?_
  refine support_kernel_subset_win (u := h⁻¹ • y) (norm_smul_sub_le hh hy) ?_
  intro h0
  exact hj (by simp only [h0, zero_smul])

theorem reconD_eq_sum {h : ℝ} (hh : 0 < h) (g : (Fin d → ℤ) → W) {y y' : Fin d → ℝ}
    (hy : ‖y' - y‖ ≤ h) :
    reconD h g y' = ∑ j ∈ win (h⁻¹ • y),
      h⁻¹ • (kernelD (h⁻¹ • y' - jc j)).smulRight (g j) := by
  unfold reconD
  refine finsum_eq_sum_of_support_subset _ fun j hj => ?_
  refine support_kernelD_subset_win (u := h⁻¹ • y) (norm_smul_sub_le hh hy) ?_
  intro h0
  apply hj
  simp only [h0]
  ext v
  simp

theorem hasFDerivAt_sum_win {h : ℝ} (g : (Fin d → ℤ) → W) (S : Finset (Fin d → ℤ))
    (y : Fin d → ℝ) :
    HasFDerivAt (fun y' => ∑ j ∈ S, kernel (h⁻¹ • y' - jc j) • g j)
      (∑ j ∈ S, h⁻¹ • (kernelD (h⁻¹ • y - jc j)).smulRight (g j)) y := by
  refine HasFDerivAt.fun_sum fun j _ => ?_
  have hin : HasFDerivAt (fun y' : Fin d → ℝ => h⁻¹ • y' - jc j)
      (h⁻¹ • ContinuousLinearMap.id ℝ (Fin d → ℝ)) y :=
    ((hasFDerivAt_id y).const_smul h⁻¹).sub_const _
  have hk := (hasFDerivAt_kernel (h⁻¹ • y - jc j)).comp y hin
  refine (hk.smul_const (g j)).congr_fderiv ?_
  ext v
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, map_smul, smul_eq_mul, smul_smul]

/-- **The reconstruction is differentiable, with derivative `reconD`.** -/
theorem hasFDerivAt_recon {h : ℝ} (hh : 0 < h) (g : (Fin d → ℤ) → W) (y : Fin d → ℝ) :
    HasFDerivAt (recon h g) (reconD h g y) y := by
  have hev : recon h g =ᶠ[𝓝 y] fun y' =>
      ∑ j ∈ win (h⁻¹ • y), kernel (h⁻¹ • y' - jc j) • g j := by
    filter_upwards [Metric.closedBall_mem_nhds y hh] with y' hy'
    rw [Metric.mem_closedBall, dist_eq_norm] at hy'
    exact recon_eq_sum hh g hy'
  have h2 := (hasFDerivAt_sum_win (h := h) g (win (h⁻¹ • y)) y).congr_of_eventuallyEq hev
  rwa [← reconD_eq_sum hh g (y := y) (y' := y) (by simp [hh.le])] at h2

/-- **The reconstruction is `C^∞`.** -/
theorem contDiff_recon {h : ℝ} (hh : 0 < h) (g : (Fin d → ℤ) → W) :
    ContDiff ℝ ∞ (recon h g) := by
  refine contDiff_iff_contDiffAt.mpr fun y => ?_
  have hev : recon h g =ᶠ[𝓝 y] fun y' =>
      ∑ j ∈ win (h⁻¹ • y), kernel (h⁻¹ • y' - jc j) • g j := by
    filter_upwards [Metric.closedBall_mem_nhds y hh] with y' hy'
    rw [Metric.mem_closedBall, dist_eq_norm] at hy'
    exact recon_eq_sum hh g hy'
  refine ContDiffAt.congr_of_eventuallyEq ?_ hev
  have hj : ∀ j : Fin d → ℤ, ContDiff ℝ ∞ fun y' : Fin d → ℝ => kernel (h⁻¹ • y' - jc j) := by
    intro j
    have hl : ContDiff ℝ ∞ fun y' : Fin d → ℝ => h⁻¹ • y' - jc j :=
      (contDiff_id.const_smul h⁻¹).sub contDiff_const
    exact contDiff_kernel.comp hl
  exact (ContDiff.sum fun j _ => (hj j).smul contDiff_const).contDiffAt

theorem fderiv_recon {h : ℝ} (hh : 0 < h) (g : (Fin d → ℤ) → W) (y : Fin d → ℝ) :
    fderiv ℝ (recon h g) y = reconD h g y := (hasFDerivAt_recon hh g y).fderiv

/-- **Values in a subspace**: data in a real subspace give a reconstruction in that subspace. -/
theorem recon_mem {h : ℝ} (hh : 0 < h) {g : (Fin d → ℤ) → W} {S : Submodule ℝ W}
    (hg : ∀ j, g j ∈ S) (y : Fin d → ℝ) : recon h g y ∈ S := by
  rw [recon_eq_sum hh g (y := y) (y' := y) (by simp [hh.le])]
  exact S.sum_mem fun j _ => S.smul_mem _ (hg j)

/-- Linearity in the data. -/
theorem recon_add {h : ℝ} (hh : 0 < h) (g₁ g₂ : (Fin d → ℤ) → W) (y : Fin d → ℝ) :
    recon h (g₁ + g₂) y = recon h g₁ y + recon h g₂ y := by
  rw [recon_eq_sum hh _ (y := y) (y' := y) (by simp [hh.le]),
    recon_eq_sum hh g₁ (y := y) (y' := y) (by simp [hh.le]),
    recon_eq_sum hh g₂ (y := y) (y' := y) (by simp [hh.le]), ← sum_add_distrib]
  simp [smul_add]

theorem recon_smul {h : ℝ} (hh : 0 < h) (c : ℝ) (g : (Fin d → ℤ) → W) (y : Fin d → ℝ) :
    recon h (c • g) y = c • recon h g y := by
  rw [recon_eq_sum hh _ (y := y) (y' := y) (by simp [hh.le]),
    recon_eq_sum hh g (y := y) (y' := y) (by simp [hh.le]), smul_sum]
  simp [smul_comm c]

/-- Continuous linear maps commute with the reconstruction. -/
theorem recon_clm {h : ℝ} (hh : 0 < h) {W' : Type*} [NormedAddCommGroup W'] [NormedSpace ℝ W']
    (Λ : W →L[ℝ] W') (g : (Fin d → ℤ) → W) (y : Fin d → ℝ) :
    Λ (recon h g y) = recon h (fun j => Λ (g j)) y := by
  rw [recon_eq_sum hh (fun j => Λ (g j)) (y := y) (y' := y) (by simp [hh.le]),
    recon_eq_sum hh g (y := y) (y' := y) (by simp [hh.le]), map_sum]
  simp

/-- **Periodicity**: data invariant under the lattice translation `p` give a reconstruction
invariant under `h p`. -/
theorem recon_add_shift {h : ℝ} (hh : 0 < h) {g : (Fin d → ℤ) → W} (p : Fin d → ℤ)
    (hg : ∀ j, g (j + p) = g j) (y : Fin d → ℝ) : recon h g (y + h • jc p) = recon h g y := by
  unfold recon
  rw [← finsum_comp_equiv (Equiv.addRight p)]
  refine finsum_congr fun j => ?_
  simp only [Equiv.coe_addRight, hg]
  congr 2
  funext i
  simp only [jc, Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul, Int.cast_add]
  field_simp
  ring

/-- **Locality**: if the data vanish at all lattice points within `3/2` mesh widths of `y/h`, the
reconstruction vanishes at `y`. -/
theorem recon_eq_zero_of {h : ℝ} {g : (Fin d → ℤ) → W} {y : Fin d → ℝ}
    (hg : ∀ j, (∀ i, |(h⁻¹ • y) i - j i| < 3 / 2) → g j = 0) : recon h g y = 0 := by
  unfold recon
  refine finsum_eq_zero_of_forall_eq_zero fun j => ?_
  by_cases hj : ∀ i, |(h⁻¹ • y) i - j i| < 3 / 2
  · rw [hg j hj, smul_zero]
  · push_neg at hj
    obtain ⟨i, hi⟩ := hj
    rw [kernel_eq_zero (i := i) (by simpa [jc] using hi), zero_smul]

/-! ### Estimates for sampled `C^{1,1}` functions (`eq:smooth-reconstruction-estimate`) -/

/-- The nodal samples `j ↦ f(h j)`. -/
def samp (h : ℝ) (f : (Fin d → ℝ) → W) : (Fin d → ℤ) → W := fun j => f (h • jc j)

/-- The kernel sup bound. -/
def kB₀ : ℝ := (exists_kernel_bounds (d := d)).choose
/-- The kernel-derivative sup bound. -/
def kB₁ : ℝ := (exists_kernel_bounds (d := d)).choose_spec.choose
/-- The Lipschitz constant of the kernel derivative. -/
def kL : ℝ := (exists_kernel_bounds (d := d)).choose_spec.choose_spec.choose

theorem kB₀_nonneg : 0 ≤ kB₀ (d := d) :=
  (exists_kernel_bounds (d := d)).choose_spec.choose_spec.choose_spec.1
theorem kB₁_nonneg : 0 ≤ kB₁ (d := d) :=
  (exists_kernel_bounds (d := d)).choose_spec.choose_spec.choose_spec.2.1
theorem kL_nonneg : 0 ≤ kL (d := d) :=
  (exists_kernel_bounds (d := d)).choose_spec.choose_spec.choose_spec.2.2.1
theorem abs_kernel_le (u : Fin d → ℝ) : |kernel u| ≤ kB₀ (d := d) :=
  (exists_kernel_bounds (d := d)).choose_spec.choose_spec.choose_spec.2.2.2.1 u
theorem norm_kernelD_le (u : Fin d → ℝ) : ‖kernelD u‖ ≤ kB₁ (d := d) :=
  (exists_kernel_bounds (d := d)).choose_spec.choose_spec.choose_spec.2.2.2.2.1 u
theorem norm_kernelD_sub_le (u v : Fin d → ℝ) : ‖kernelD u - kernelD v‖ ≤ kL (d := d) * ‖u - v‖ :=
  (exists_kernel_bounds (d := d)).choose_spec.choose_spec.choose_spec.2.2.2.2.2 u v

/-- The constant of the value estimate. -/
def cVal (d : ℕ) : ℝ := 8 ^ d * kB₀ (d := d) * 4
/-- The constant of the derivative estimate. -/
def cDer (d : ℕ) : ℝ := 8 ^ d * kB₁ (d := d) * 16
/-- The constant of the Lipschitz estimate of the derivative. -/
def cLip (d : ℕ) : ℝ := max (8 ^ d * kL (d := d) * 16) (2 * cDer d + 1)

theorem cVal_nonneg : 0 ≤ cVal d := by unfold cVal; have := kB₀_nonneg (d := d); positivity
theorem cDer_nonneg : 0 ≤ cDer d := by unfold cDer; have := kB₁_nonneg (d := d); positivity
theorem cLip_nonneg : 0 ≤ cLip d :=
  le_max_of_le_right (by have := cDer_nonneg (d := d); linarith)

/-- Taylor remainder for a `C^{1,1}` function: `‖f(x) - f(y) - f'(y)(x - y)‖ ≤ M₂ ‖x - y‖²`. -/
theorem norm_taylor_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → W}
    {f' : E → E →L[ℝ] W} {M₂ : ℝ} (hM₂0 : 0 ≤ M₂) (hf : ∀ y, HasFDerivAt f (f' y) y)
    (hM₂ : ∀ y z, ‖f' y - f' z‖ ≤ M₂ * ‖y - z‖) (x y : E) :
    ‖f x - f y - f' y (x - y)‖ ≤ M₂ * ‖x - y‖ ^ 2 := by
  set φ : ℝ → W := fun t => f (y + t • (x - y)) - t • f' y (x - y) with hφ
  have hd : ∀ t, HasDerivAt φ (f' (y + t • (x - y)) (x - y) - f' y (x - y)) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => y + t • (x - y)) (x - y) t := by
      simpa using ((hasDerivAt_id t).smul_const (x - y)).const_add y
    have h2 : HasDerivAt (fun t : ℝ => f (y + t • (x - y))) (f' (y + t • (x - y)) (x - y)) t :=
      (hf (y + t • (x - y))).comp_hasDerivAt t h1
    have h3 : HasDerivAt (fun t : ℝ => t • f' y (x - y)) (f' y (x - y)) t := by
      simpa using (hasDerivAt_id t).smul_const (f' y (x - y))
    exact h2.sub h3
  have hb := norm_image_sub_le_of_norm_deriv_le_segment' (f := φ) (a := 0) (b := 1)
    (C := M₂ * ‖x - y‖ ^ 2) (fun t _ => (hd t).hasDerivWithinAt) (fun t ht => ?_) 1
    ⟨zero_le_one, le_rfl⟩
  · have e : φ 1 - φ 0 = f x - f y - f' y (x - y) := by
      simp only [hφ, one_smul, zero_smul, add_zero, sub_zero, add_sub_cancel]
      abel
    rw [e] at hb
    simpa using hb
  · rw [← ContinuousLinearMap.sub_apply]
    refine ((f' (y + t • (x - y)) - f' y).le_opNorm _).trans ?_
    have := hM₂ (y + t • (x - y)) y
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1] at this
    have ht1 : t ≤ 1 := ht.2.le
    calc ‖f' (y + t • (x - y)) - f' y‖ * ‖x - y‖ ≤ M₂ * (t * ‖x - y‖) * ‖x - y‖ :=
          mul_le_mul_of_nonneg_right this (norm_nonneg _)
      _ ≤ M₂ * (1 * ‖x - y‖) * ‖x - y‖ := by gcongr
      _ = M₂ * ‖x - y‖ ^ 2 := by ring

theorem smul_jc_sub {h : ℝ} (hh : h ≠ 0) (y : Fin d → ℝ) (j : Fin d → ℤ) :
    h • jc j - y = h • (jc j - h⁻¹ • y) := by
  rw [smul_sub, smul_inv_smul₀ hh]

theorem norm_smul_jc_sub_le {h : ℝ} (hh : 0 < h) {y : Fin d → ℝ} {j : Fin d → ℤ}
    (hj : j ∈ win (h⁻¹ • y)) : ‖h • jc j - y‖ ≤ 4 * h := by
  rw [smul_jc_sub hh.ne', norm_smul, Real.norm_eq_abs, abs_of_pos hh]
  have := norm_jc_sub_le_of_mem_win hj
  nlinarith

variable {f : (Fin d → ℝ) → W} {f' : (Fin d → ℝ) → (Fin d → ℝ) →L[ℝ] W}

/-- **Value estimate**: `‖𝒥_h f(y) - f(y)‖ ≤ C h M₁` for `‖f'‖ ≤ M₁`. -/
theorem norm_recon_samp_sub_le {h : ℝ} (hh : 0 < h) {M₁ : ℝ} (hf : ∀ y, HasFDerivAt f (f' y) y)
    (hM₁ : ∀ y, ‖f' y‖ ≤ M₁) (y : Fin d → ℝ) :
    ‖recon h (samp h f) y - f y‖ ≤ cVal d * M₁ * h := by
  have hM₁0 : 0 ≤ M₁ := (norm_nonneg _).trans (hM₁ y)
  set u := h⁻¹ • y
  have hPU := sum_kernel_win (u := u) (u' := u) (by simp)
  have e : recon h (samp h f) y - f y = ∑ j ∈ win u, kernel (u - jc j) • (f (h • jc j) - f y) := by
    rw [recon_eq_sum hh _ (y := y) (y' := y) (by simp [hh.le])]
    simp_rw [smul_sub]
    rw [sum_sub_distrib, ← sum_smul, hPU, one_smul]
    rfl
  rw [e]
  refine (norm_sum_le _ _).trans ?_
  have hb : ∀ j ∈ win u, ‖kernel (u - jc j) • (f (h • jc j) - f y)‖ ≤ kB₀ (d := d) * (M₁ * (4 * h)) := by
    intro j hj
    rw [norm_smul, Real.norm_eq_abs]
    refine mul_le_mul (abs_kernel_le _) ?_ (norm_nonneg _) kB₀_nonneg
    have := convex_univ.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun z _ => (hf z).hasFDerivWithinAt) (fun z _ => hM₁ z) (mem_univ y) (mem_univ (h • jc j))
    exact this.trans (mul_le_mul_of_nonneg_left (norm_smul_jc_sub_le hh hj) hM₁0)
  refine (sum_le_sum hb).trans ?_
  rw [sum_const, nsmul_eq_mul]
  have hc : ((win u).card : ℝ) ≤ 8 ^ d := by exact_mod_cast card_win_le u
  have : 0 ≤ kB₀ (d := d) * (M₁ * (4 * h)) := by have := kB₀_nonneg (d := d); positivity
  calc ((win u).card : ℝ) * (kB₀ * (M₁ * (4 * h))) ≤ 8 ^ d * (kB₀ * (M₁ * (4 * h))) :=
        mul_le_mul_of_nonneg_right hc this
    _ = cVal d * M₁ * h := by unfold cVal; ring

/-- The derivative error as a single window sum of Taylor remainders. -/
theorem reconD_samp_sub_eq {h : ℝ} (hh : 0 < h) (y y' : Fin d → ℝ) (hy : ‖y' - y‖ ≤ h) :
    reconD h (samp h f) y' - f' y = ∑ j ∈ win (h⁻¹ • y),
      h⁻¹ • (kernelD (h⁻¹ • y' - jc j)).smulRight
        (f (h • jc j) - f y - f' y (h • jc j - y)) := by
  set u := h⁻¹ • y
  set u' := h⁻¹ • y'
  have hu : ‖u' - u‖ ≤ 1 := norm_smul_sub_le hh hy
  rw [reconD_eq_sum hh _ hy]
  ext v
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply]
  simp only [smul_sub, sum_sub_distrib]
  have h1 : ∑ j ∈ win u, h⁻¹ • kernelD (u' - jc j) v • f y = 0 := by
    rw [← smul_sum, ← sum_smul]
    have := congrArg (fun L : (Fin d → ℝ) →L[ℝ] ℝ => L v) (sum_kernelD_win (u := u) (u' := u') hu)
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.zero_apply] at this
    rw [this, zero_smul, smul_zero]
  have h3 : ∑ j ∈ win u, kernelD (u' - jc j) v = 0 := by
    have := congrArg (fun L : (Fin d → ℝ) →L[ℝ] ℝ => L v) (sum_kernelD_win (u := u) (u' := u') hu)
    simpa using this
  have h2 : ∑ j ∈ win u, h⁻¹ • kernelD (u' - jc j) v • f' y (h • jc j - y) = f' y v := by
    have e : ∀ j, h • jc j - y = h • (jc j - u') + h • (u' - u) := by
      intro j
      rw [← smul_add, sub_add_sub_cancel, smul_jc_sub hh.ne']
    calc ∑ j ∈ win u, h⁻¹ • kernelD (u' - jc j) v • f' y (h • jc j - y)
        = ∑ j ∈ win u, (kernelD (u' - jc j) v • f' y (jc j - u') +
            kernelD (u' - jc j) v • f' y (u' - u)) := by
          refine sum_congr rfl fun j _ => ?_
          rw [e j, map_add, map_smul, map_smul, smul_add, smul_add]
          congr 1 <;> rw [smul_comm (kernelD (u' - jc j) v) h, smul_smul, inv_mul_cancel₀ hh.ne',
            one_smul]
      _ = f' y (∑ j ∈ win u, kernelD (u' - jc j) v • (jc j - u')) +
            (∑ j ∈ win u, kernelD (u' - jc j) v) • f' y (u' - u) := by
          rw [sum_add_distrib, map_sum, sum_smul]
          simp_rw [map_smul]
      _ = f' y v := by rw [sum_kernelD_moment_win hu v, h3, zero_smul, add_zero]
  rw [h1, h2]
  simp only [samp, sub_zero]
  rfl

theorem norm_window_sum_le {h : ℝ} (hh : 0 < h) {M₂ : ℝ} (hM₂0 : 0 ≤ M₂)
    (hf : ∀ y, HasFDerivAt f (f' y) y) (hM₂ : ∀ y z, ‖f' y - f' z‖ ≤ M₂ * ‖y - z‖)
    (y : Fin d → ℝ) {c : (Fin d → ℤ) → ℝ} (hc : ∀ j, 0 ≤ c j) (Λ : (Fin d → ℤ) → (Fin d → ℝ) →L[ℝ] ℝ)
    (hΛ : ∀ j, ‖Λ j‖ ≤ c j) :
    ‖∑ j ∈ win (h⁻¹ • y), h⁻¹ • (Λ j).smulRight (f (h • jc j) - f y - f' y (h • jc j - y))‖ ≤
      ∑ j ∈ win (h⁻¹ • y), h⁻¹ * c j * (M₂ * (4 * h) ^ 2) := by
  refine (norm_sum_le _ _).trans (sum_le_sum fun j hj => ?_)
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hh, ContinuousLinearMap.norm_smulRight_apply,
    mul_assoc]
  refine mul_le_mul_of_nonneg_left (mul_le_mul (hΛ j) ?_ (norm_nonneg _) (hc j)) (by positivity)
  refine (norm_taylor_le hM₂0 hf hM₂ _ _).trans ?_
  have := norm_smul_jc_sub_le hh hj
  gcongr

/-- **Derivative estimate**: `‖D𝒥_h f(y) - f'(y)‖ ≤ C h M₂` for `f'` `M₂`-Lipschitz. -/
theorem norm_reconD_samp_sub_le {h : ℝ} (hh : 0 < h) {M₂ : ℝ} (hM₂0 : 0 ≤ M₂)
    (hf : ∀ y, HasFDerivAt f (f' y) y) (hM₂ : ∀ y z, ‖f' y - f' z‖ ≤ M₂ * ‖y - z‖)
    (y : Fin d → ℝ) : ‖reconD h (samp h f) y - f' y‖ ≤ cDer d * M₂ * h := by
  rw [reconD_samp_sub_eq hh y y (by simp [hh.le])]
  refine (norm_window_sum_le hh hM₂0 hf hM₂ y (c := fun _ => kB₁ (d := d)) (fun _ => kB₁_nonneg)
    _ fun j => norm_kernelD_le _).trans ?_
  rw [sum_const, nsmul_eq_mul]
  have hc : ((win (h⁻¹ • y)).card : ℝ) ≤ 8 ^ d := by exact_mod_cast card_win_le _
  have : 0 ≤ h⁻¹ * kB₁ (d := d) * (M₂ * (4 * h) ^ 2) := by
    have := kB₁_nonneg (d := d); positivity
  calc ((win (h⁻¹ • y)).card : ℝ) * (h⁻¹ * kB₁ * (M₂ * (4 * h) ^ 2)) ≤
        8 ^ d * (h⁻¹ * kB₁ * (M₂ * (4 * h) ^ 2)) := mul_le_mul_of_nonneg_right hc this
    _ = cDer d * M₂ * h := by unfold cDer; field_simp; ring

/-- **Lipschitz estimate of the derivative** (`‖𝒥_h f‖_{W^{2,∞}} ≤ C ‖f‖_{C²}`):
`‖D𝒥_h f(y) - D𝒥_h f(y')‖ ≤ C M₂ ‖y - y'‖`. -/
theorem norm_reconD_samp_sub_reconD_le {h : ℝ} (hh : 0 < h) {M₂ : ℝ} (hM₂0 : 0 ≤ M₂)
    (hf : ∀ y, HasFDerivAt f (f' y) y) (hM₂ : ∀ y z, ‖f' y - f' z‖ ≤ M₂ * ‖y - z‖)
    (y y' : Fin d → ℝ) :
    ‖reconD h (samp h f) y - reconD h (samp h f) y'‖ ≤ cLip d * M₂ * ‖y - y'‖ := by
  by_cases hy : ‖y' - y‖ ≤ h
  · have e : reconD h (samp h f) y - reconD h (samp h f) y' =
        (reconD h (samp h f) y - f' y) - (reconD h (samp h f) y' - f' y) := by abel
    rw [e, reconD_samp_sub_eq hh y y (by simp [hh.le]), reconD_samp_sub_eq hh y y' hy,
      ← sum_sub_distrib]
    have e2 : ∀ j ∈ win (h⁻¹ • y), h⁻¹ • (kernelD (h⁻¹ • y - jc j)).smulRight
          (f (h • jc j) - f y - f' y (h • jc j - y)) -
        h⁻¹ • (kernelD (h⁻¹ • y' - jc j)).smulRight (f (h • jc j) - f y - f' y (h • jc j - y)) =
        h⁻¹ • (kernelD (h⁻¹ • y - jc j) - kernelD (h⁻¹ • y' - jc j)).smulRight
          (f (h • jc j) - f y - f' y (h • jc j - y)) := by
      intro j _
      ext v
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.smulRight_apply, sub_smul, smul_sub]
      abel
    rw [sum_congr rfl e2]
    have hk : ∀ j, ‖kernelD (h⁻¹ • y - jc j) - kernelD (h⁻¹ • y' - jc j)‖ ≤
        kL (d := d) * (h⁻¹ * ‖y - y'‖) := by
      intro j
      refine (norm_kernelD_sub_le _ _).trans (le_of_eq ?_)
      congr 1
      rw [sub_sub_sub_cancel_right, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_inv,
        abs_of_pos hh]
    refine (norm_window_sum_le hh hM₂0 hf hM₂ y
      (c := fun _ => kL (d := d) * (h⁻¹ * ‖y - y'‖)) (fun _ => by
        have := kL_nonneg (d := d); positivity) _ hk).trans ?_
    rw [sum_const, nsmul_eq_mul]
    have hc : ((win (h⁻¹ • y)).card : ℝ) ≤ 8 ^ d := by exact_mod_cast card_win_le _
    have : 0 ≤ h⁻¹ * (kL (d := d) * (h⁻¹ * ‖y - y'‖)) * (M₂ * (4 * h) ^ 2) := by
      have := kL_nonneg (d := d); positivity
    calc ((win (h⁻¹ • y)).card : ℝ) * (h⁻¹ * (kL * (h⁻¹ * ‖y - y'‖)) * (M₂ * (4 * h) ^ 2)) ≤
          8 ^ d * (h⁻¹ * (kL * (h⁻¹ * ‖y - y'‖)) * (M₂ * (4 * h) ^ 2)) :=
          mul_le_mul_of_nonneg_right hc this
      _ = (8 ^ d * kL (d := d) * 16) * M₂ * ‖y - y'‖ := by field_simp; ring
      _ ≤ cLip d * M₂ * ‖y - y'‖ := by
          gcongr
          exact le_max_left _ _
  · push_neg at hy
    have e : reconD h (samp h f) y - reconD h (samp h f) y' =
        (reconD h (samp h f) y - f' y) + (f' y - f' y') - (reconD h (samp h f) y' - f' y') := by
      abel
    rw [e]
    have h1 := norm_reconD_samp_sub_le hh hM₂0 hf hM₂ y
    have h2 := norm_reconD_samp_sub_le hh hM₂0 hf hM₂ y'
    have h3 := hM₂ y y'
    have hyy : h < ‖y - y'‖ := by rwa [norm_sub_rev]
    have hcd := cDer_nonneg (d := d)
    calc ‖reconD h (samp h f) y - f' y + (f' y - f' y') - (reconD h (samp h f) y' - f' y')‖
        ≤ cDer d * M₂ * h + M₂ * ‖y - y'‖ + cDer d * M₂ * h :=
          (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add h1 h3)) h2)
      _ ≤ (2 * cDer d + 1) * M₂ * ‖y - y'‖ := by nlinarith [mul_nonneg hcd hM₂0]
      _ ≤ cLip d * M₂ * ‖y - y'‖ := by
          gcongr
          exact le_max_right _ _

end RenewalGeometry.CardinalQI
