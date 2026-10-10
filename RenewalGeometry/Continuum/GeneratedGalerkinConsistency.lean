/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.GeneratedHartleyParseval
import RenewalGeometry.Continuum.KatoGalerkinSharpRate
import RenewalGeometry.Continuum.KatoSmoothness

/-!
# Spectral Galerkin solutions converge to every smooth solution

Generic infrastructure (no renewal notions) for `thm:generated-dynamics` (Einstein–Standard-Model
action-closure manuscript, `eq:generated-Galerkin-rate`: "where `U` is the physical Sobolev
solution with initial datum `U₀`").  The rates of `KatoGenDyn.generated_dynamics_rates` compare the
fully finite scheme with the Galerkin limit; this file identifies that limit with **any** smooth
classical solution with the same data (here: the actual-jet state of the physical solution of
`lem:generated-physical-identification`), by the symmetric `L²` energy method for the difference
`γ_N - P_N V`.

* `frz` — the frozen slice `x ↦ f(t, x_spatial)` (smooth, periodic, bounded, same spatial jets on
  the slice `t`);
* `sint_sub_tfs_sq_le` — the `L²` tail of a smooth field beyond the box `N` is at most
  `Q₁/(2π(N+1))²` (Parseval, `GenParseval.hasSum_wq_coef_sq`);
* **`galerkin_tendsto_smooth`** — for a cutoff-uniformly bounded family of spectral Galerkin
  solutions `γ_N` with data `P_NU₀` on `[0, T]` and a smooth spatially periodic `V` with
  `∂_tV = G(V)` on `[0, T]`, `V(0) = U₀`: `c_k(γ_N(t)) → c_k(V(t))` for every mode and time.
-/

open MeasureTheory Filter Topology Set
open scoped BigOperators ContDiff Real

noncomputable section

namespace RenewalGeometry.GenGalCons

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk SlabSobAlg QLEnergy KatoGalerkin

set_option linter.unusedSectionVars false

variable {d n : ℕ}

/-! ### Frozen slices -/

/-- The frozen slice `x ↦ f(t, x₁, …, x_d)` (time-independent). -/
def frz (t : ℝ) (f : ST d → ℝ) (x : ST d) : ℝ := f (Fin.cons t (Fin.tail x))

theorem frz_cons (t : ℝ) (f : ST d → ℝ) (s : ℝ) (y : Fin d → ℝ) :
    frz t f (Fin.cons s y) = f (Fin.cons t y) := by
  simp [frz]

theorem contDiff_tail : ContDiff ℝ ∞ (fun x : ST d => Fin.tail x) :=
  contDiff_pi.2 fun i => contDiff_apply ℝ ℝ i.succ

theorem contDiff_frz (t : ℝ) {f : ST d → ℝ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (frz t f) :=
  hf.comp ((contDiff_cons t).comp contDiff_tail)

theorem cons_tail_add_sshift (t : ℝ) (x : ST d) (k : Fin d → ℤ) :
    (Fin.cons t (Fin.tail (x + sshift k)) : ST d) = Fin.cons t (Fin.tail x) + sshift k := by
  funext μ
  induction μ using Fin.cases with
  | zero => simp [sshift]
  | succ i => simp [sshift, Fin.tail]

theorem isSPeriodic_frz (t : ℝ) {f : ST d → ℝ} (hp : IsSPeriodic f) : IsSPeriodic (frz t f) :=
  fun k x => by
    unfold frz
    rw [cons_tail_add_sshift, hp k]

theorem cons_tail_line (t : ℝ) (x : ST d) (i : Fin d) (s : ℝ) :
    (Fin.cons t (Fin.tail (x + s • ev i.succ)) : ST d) =
      Fin.cons t (Fin.tail x) + s • ev i.succ := by
  funext μ
  induction μ using Fin.cases with
  | zero => simp [Pi.single_apply, Fin.succ_ne_zero]
  | succ j => simp [Fin.tail, Pi.single_apply]

/-- Spatial derivatives of the frozen slice. -/
theorem pd_frz_succ (t : ℝ) {f : ST d → ℝ} (hf : ContDiff ℝ ∞ f) (i : Fin d) (x : ST d) :
    pd (frz t f) i.succ x = pd f i.succ (Fin.cons t (Fin.tail x)) := by
  have h1 := hasDerivAt_line0 (contDiff_frz t hf) x i.succ
  have h2 := hasDerivAt_line0 hf (Fin.cons t (Fin.tail x)) i.succ
  have e : (fun s : ℝ => frz t f (x + s • ev i.succ)) =
      fun s : ℝ => f (Fin.cons t (Fin.tail x) + s • ev i.succ) := by
    funext s; unfold frz; rw [cons_tail_line]
  rw [e] at h1
  exact h1.unique h2

theorem pd_frz_succ_cons (t : ℝ) {f : ST d → ℝ} (hf : ContDiff ℝ ∞ f) (i : Fin d)
    (y : Fin d → ℝ) (s : ℝ) :
    pd (frz t f) i.succ (Fin.cons s y) = pd f i.succ (Fin.cons t y) := by
  rw [pd_frz_succ t hf]; simp

/-- The generator of the frozen family agrees with the generator on the slice. -/
theorem genG_frz {A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ} {F : Fin n → (Fin n → ℝ) → ℝ}
    (t : ℝ) {V : Fin n → ST d → ℝ} (hV : ∀ b, ContDiff ℝ ∞ (V b)) (a : Fin n) (y : Fin d → ℝ) :
    genG A F (fun b => frz t (V b)) a (Fin.cons t y) = genG A F V a (Fin.cons t y) := by
  simp only [genG, compF, frz_cons, pd_frz_succ_cons t (hV _)]

/-! ### Slice integrals -/

theorem sint_congr_slice {f g : ST d → ℝ} {t : ℝ}
    (h : ∀ y : Fin d → ℝ, f (Fin.cons t y) = g (Fin.cons t y)) : sint f t = sint g t := by
  unfold sint
  exact setIntegral_congr_fun measurableSet_Icc fun y _ => h y

theorem coef_congr_slice {f g : ST d → ℝ} {t : ℝ}
    (h : ∀ y : Fin d → ℝ, f (Fin.cons t y) = g (Fin.cons t y)) (k : Fin d → ℤ) :
    coef f t k = coef g t k := by
  unfold coef
  exact sint_congr_slice fun y => by rw [h y]

/-- **The `L²` tail beyond the box `N`**: `‖f - P_Nf‖²_{L²} ≤ Q₁(f)/(2π(N+1))²`. -/
theorem sint_sub_tfs_sq_le {f : ST d → ℝ} (hf : ContDiff ℝ ∞ f) (hp : IsSPeriodic f) (t : ℝ)
    (N : ℕ) :
    sint (fun x => (f x - tfs (KatoGalerkin.box N) (coef f t) x) ^ 2) t ≤
      Q 1 f t / (2 * π * ((N : ℝ) + 1)) ^ 2 := by
  set g : ST d → ℝ := fun x => f x - tfs (KatoGalerkin.box N) (coef f t) x with hg
  have hgc : ContDiff ℝ ∞ g := hf.sub (contDiff_tfs _ _)
  have hgp : IsSPeriodic g := fun k x => by
    simp only [hg, hp k x, isSPeriodic_tfs _ _ k x]
  have hcoef : ∀ k, coef g t k = if k ∈ KatoGalerkin.box N then 0 else coef f t k := fun k => by
    rw [hg, coef_sub hf.continuous (contDiff_tfs _ _).continuous, coef_tfs]
    split_ifs <;> ring
  have h1 := GenParseval.hasSum_coef_sq hgc.continuous hgp t
  have h2 := GenParseval.hasSum_wq_coef_sq 1 hf hp t
  set s : ℝ := (2 * π * ((N : ℝ) + 1)) ^ 2 with hs
  have hs0 : 0 < s := by have := one_le_two_pi_succ N; positivity
  have h3 : HasSum (fun k => s * coef g t k ^ 2) (s * sint (fun x => g x ^ 2) t) :=
    h1.mul_left s
  have hle : ∀ k, s * coef g t k ^ 2 ≤ wq 1 k * coef f t k ^ 2 := fun k => by
    rw [hcoef k]
    split_ifs with hk
    · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
      exact mul_nonneg (wq_nonneg 1 k) (sq_nonneg _)
    · have := wq_ge_of_not_mem_box hk 1
      rw [pow_one] at this
      exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
  have h4 := hasSum_le hle h3 h2
  rw [le_div_iff₀ hs0]
  linarith

/-! ### Convergence of the Galerkin solutions to a smooth solution -/

variable {A : Fin d → Fin n → Fin n → (Fin n → ℝ) → ℝ} {F : Fin n → (Fin n → ℝ) → ℝ}

/-- The Galerkin pairing of a coefficient difference with a generator difference, as a slice
integral. -/
theorem sum_box_eq_sint (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b)) (hF : ∀ a, ContDiff ℝ ∞ (F a))
    (q : ℕ) {N : ℕ} (a : GS d n N) (b : Fin n) {v : ST d → ℝ} {G : ST d → ℝ}
    (hG : Continuous G) (t : ℝ) :
    ∑ k ∈ KatoGalerkin.box N, (cf q a b k - coef v t k) * (coef (genG A F (fld q a) b) 0 k - coef G t k) =
      sint (fun x => (fld q a b x - tfs (KatoGalerkin.box N) (coef v t) x) *
        (genG A F (fld q a) b x - G x)) t := by
  have hGN : Continuous (genG A F (fld q a) b) :=
    (contDiff_genG hA hF (fun b => contDiff_fld q a b) b).continuous
  have e1 : (fun x => (fld q a b x - tfs (KatoGalerkin.box N) (coef v t) x) *
      (genG A F (fld q a) b x - G x)) = fun x => tfs (KatoGalerkin.box N) (fun k => cf q a b k - coef v t k) x *
      (genG A F (fld q a) b x - G x) := by
    funext x; rw [fld, tfs_sub]
  rw [e1, sint_tfs_mul (g := fun x => genG A F (fld q a) b x - G x) _ _ (hGN.sub hG)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [coef_sub hGN hG, KatoRates.coef_slice_eq (fun s s' y => genG_fld_cons_eq q a b s s' y) 0 t]

set_option maxHeartbeats 1600000 in
/-- **Spectral Galerkin solutions converge to every smooth solution with the same data**: let
`γ_N` be spectral Galerkin solutions (`γ_N' = G_N(γ_N)`, `γ_N(0) = P_NU₀`) on `[0, T]` with the
cutoff-uniform bound `‖γ_N‖ ≤ R` (`‖·‖ = H^q`, `q ≥ m + 1`, `m > d/2`), and let `V` be a smooth
spatially periodic field with `∂_tV = G(V)` on `[0, T]` and `V(0) = U₀`.  Then every Fourier
coefficient converges: `c_k(γ_N(t)) → c_k(V(t))` for `t ∈ [0, T]`. -/
theorem galerkin_tendsto_smooth {m q : ℕ} (hm : (d : ℝ) / 2 < m) (hmq : m + 1 ≤ q)
    (hA : ∀ i a b, ContDiff ℝ ∞ (A i a b)) (hsym : ∀ i a b v, A i a b v = A i b a v)
    (hF : ∀ a, ContDiff ℝ ∞ (F a)) {T R : ℝ} (hT : 0 ≤ T) (hR : 0 ≤ R)
    {U₀ : Fin n → ST d → ℝ} {γ : (N : ℕ) → ℝ → GS d n N} (hγ0 : ∀ N, γ N 0 = P0 q N U₀)
    (hγ : ∀ N, ∀ t ∈ Icc 0 T, HasDerivWithinAt (γ N) (GN A F q (γ N t)) (Icc 0 T) t)
    (hγR : ∀ N, ∀ t ∈ Icc 0 T, ‖γ N t‖ ≤ R)
    {V : Fin n → ST d → ℝ} (hV : ∀ b, ContDiff ℝ ∞ (V b)) (hVp : ∀ b, IsSPeriodic (V b))
    (hV0 : ∀ b y, V b (Fin.cons 0 y) = U₀ b (Fin.cons 0 y))
    (hVeq : ∀ b, ∀ t ∈ Icc 0 T, ∀ y,
      pd (V b) 0 (Fin.cons t y) = genG A F V b (Fin.cons t y)) :
    ∀ t ∈ Icc 0 T, ∀ b k, Tendsto (fun N => cf q (γ N t) b k) atTop (𝓝 (coef (V b) t k)) := by
  -- uniform bounds
  obtain ⟨CS, hCS, hsup⟩ := exists_sup_sq_le (d := d) hm
  have hVb : ∀ b, ∃ C, ∀ x ∈ slab (d := d) 0 T, ‖V b x‖ ≤ C := fun b =>
    KatoGalerkin.exists_bound_slab (hV b).continuous.continuousOn (hVp b) (a := -1) (b := T + 1)
      (by norm_num) (by linarith)
  have hVdb : ∀ b (i : Fin d), ∃ C, ∀ x ∈ slab (d := d) 0 T, ‖pd (V b) i.succ x‖ ≤ C :=
    fun b i => KatoGalerkin.exists_bound_slab (contDiff_pd_top (hV b) i.succ).continuous.continuousOn
      (isSPeriodic_pd (hVp b) i.succ) (a := -1) (b := T + 1) (by norm_num) (by linarith)
  choose CV hCV using hVb
  choose CVd hCVd using hVdb
  set B : ℝ := Real.sqrt CS * R + ∑ b, |CV b| + ∑ b, ∑ i, |CVd b i| with hB
  have hB0 : 0 ≤ B := by positivity
  have hCVB : ∀ b, CV b ≤ B := fun b => by
    have h1 : |CV b| ≤ ∑ b, |CV b| :=
      Finset.single_le_sum (f := fun b => |CV b|) (fun _ _ => abs_nonneg _) (Finset.mem_univ b)
    have h2 : 0 ≤ ∑ b, ∑ i, |CVd b i| := by positivity
    have h3 : 0 ≤ Real.sqrt CS * R := by positivity
    linarith [le_abs_self (CV b)]
  have hCVdB : ∀ b i, CVd b i ≤ B := fun b i => by
    have h1 : |CVd b i| ≤ ∑ i, |CVd b i| :=
      Finset.single_le_sum (f := fun i => |CVd b i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    have h1' : ∑ i, |CVd b i| ≤ ∑ b, ∑ i, |CVd b i| :=
      Finset.single_le_sum (f := fun b => ∑ i, |CVd b i|) (fun _ _ => by positivity)
        (Finset.mem_univ b)
    have h2 : 0 ≤ ∑ b, |CV b| := by positivity
    have h3 : 0 ≤ Real.sqrt CS * R := by positivity
    linarith [le_abs_self (CVd b i)]
  have hRB : Real.sqrt CS * R ≤ B := by
    have h2 : 0 ≤ ∑ b, |CV b| := by positivity
    have h3 : 0 ≤ ∑ b, ∑ i, |CVd b i| := by positivity
    linarith
  obtain ⟨K₁, hK₁0, hK₁⟩ := sym_L2_diff hA hsym hF hB0
  set Φ : (Fin n ⊕ (Fin d × Fin n × Fin n)) → (Fin n → ℝ) → ℝ :=
    fun k => Sum.elim (fun a => F a) (fun p => A p.1 p.2.1 p.2.2) k with hΦ
  have hΦs : ∀ k, ContDiff ℝ ∞ (Φ k) := by
    intro k; cases k with
    | inl a => exact hF a
    | inr p => exact hA p.1 p.2.1 p.2.2
  obtain ⟨Mc, hMc0, hMc⟩ := exists_coeff_bounds hΦs B
  set Gm := Mc + d * n * Mc * B with hGm
  have hGm0 : 0 ≤ Gm := by positivity
  -- the frozen fields
  have hWb : ∀ t ∈ Icc 0 T, (∀ b x, |frz t (V b) x| ≤ B) ∧
      (∀ b (i : Fin d) x, |pd (frz t (V b)) i.succ x| ≤ B) := by
    intro t ht
    have hx : ∀ x : ST d, (Fin.cons t (Fin.tail x) : ST d) ∈ slab (d := d) 0 T := fun x => by
      show (Fin.cons t (Fin.tail x) : ST d) 0 ∈ Icc 0 T
      simpa using ht
    refine ⟨fun b x => ?_, fun b i x => ?_⟩
    · have := hCV b _ (hx x)
      rw [Real.norm_eq_abs] at this
      exact this.trans (hCVB b)
    · rw [pd_frz_succ t (hV b)]
      have := hCVd b i _ (hx x)
      rw [Real.norm_eq_abs] at this
      exact this.trans (hCVdB b i)
  have hbd : ∀ N, ∀ s ∈ Icc 0 T, (∀ b x, |fld q (γ N s) b x| ≤ B) ∧
      (∀ b (i : Fin d) x, |pd (fld q (γ N s) b) i.succ x| ≤ B) := by
    intro N s hs
    have hn := hγR N s hs
    refine ⟨fun b x => ?_, fun b i x => ?_⟩
    · exact ((abs_fld_le hmq hCS hsup (γ N s) b x).1.trans
        (mul_le_mul_of_nonneg_left hn (Real.sqrt_nonneg _))).trans hRB
    · exact (((abs_fld_le hmq hCS hsup (γ N s) b x).2 i).trans
        (mul_le_mul_of_nonneg_left hn (Real.sqrt_nonneg _))).trans hRB
  have hGbd : ∀ (u : Fin n → ST d → ℝ), (∀ b x, |u b x| ≤ B) →
      (∀ b (i : Fin d) x, |pd (u b) i.succ x| ≤ B) → ∀ b x, |genG A F u b x| ≤ Gm :=
    fun u hu hdu b x => abs_genG_le hB0 hMc0 hu hdu
      (fun a v hv => (hMc (Sum.inl a) v v hv hv).1)
      (fun i a b v hv => (hMc (Sum.inr (i, a, b)) v v hv hv).1) b x
  -- the `H¹` bound of `V`
  have hQc : ∀ b, ContinuousOn (fun t => Q 1 (V b) t) (Icc 0 T) := fun b =>
    (continuous_Q 1 (hV b)).continuousOn
  have hQb : ∀ b, ∃ C, ∀ t ∈ Icc (0 : ℝ) T, ‖Q 1 (V b) t‖ ≤ C := fun b =>
    isCompact_Icc.exists_bound_of_continuousOn (hQc b)
  choose CQ hCQ using hQb
  set MQ : ℝ := ∑ b, |CQ b| with hMQ
  have hMQ0 : 0 ≤ MQ := by positivity
  have hQle : ∀ t ∈ Icc 0 T, ∑ b, Q 1 (V b) t ≤ MQ := fun t ht =>
    Finset.sum_le_sum fun b _ => by
      have := hCQ b t ht
      rw [Real.norm_eq_abs] at this
      exact (le_abs_self _).trans (this.trans (le_abs_self _))
  -- the main estimate for a fixed cutoff
  have hmain : ∀ N : ℕ, ∀ t ∈ Icc 0 T, ∑ b, ∑ k ∈ KatoGalerkin.box N, (cf q (γ N t) b k - coef (V b) t k) ^ 2 ≤
      (4 * K₁ * n * MQ + n * MQ + 4 * n * Gm ^ 2) * T * Real.exp (4 * K₁ * T) /
        (2 * π * ((N : ℝ) + 1)) := by
    intro N
    set s : ℝ := 2 * π * ((N : ℝ) + 1) with hs
    have hs1 : 1 ≤ s := one_le_two_pi_succ N
    have hs0 : 0 < s := by linarith
    set η : ℝ := 1 / s with hη
    have hη0 : 0 < η := by positivity
    set D : ℝ → ℝ := fun t => ∑ b, ∑ k ∈ KatoGalerkin.box N, (cf q (γ N t) b k - coef (V b) t k) ^ 2 with hD
    set ĝ : ℝ → Fin n → (Fin d → ℤ) → ℝ := fun t b k =>
      coef (genG A F (fld q (γ N t)) b) 0 k with hĝ
    set D' : ℝ → ℝ := fun t => ∑ b, ∑ k ∈ KatoGalerkin.box N, 2 * (cf q (γ N t) b k - coef (V b) t k) *
      (ĝ t b k - coef (pd (V b) 0) t k) with hD'
    -- coefficient derivatives of `V`
    have hVc : ∀ b k t, HasDerivAt (fun s => coef (V b) s k) (coef (pd (V b) 0) t k) t := by
      intro b k t
      refine KatoSmooth.hasDerivAt_coef_of_time (a := t - 1) (b := t + 1) (hV b).continuous
        (contDiff_pd_top (hV b) 0).continuous (fun t' _ y => ?_) k ⟨by linarith, by linarith⟩
      have h := KatoSmooth.hasDerivAt_line_at (hV b) (Fin.cons 0 y) 0 t'
      have e : ∀ s : ℝ, (Fin.cons 0 y : ST d) + s • ev (0 : Fin (d + 1)) = Fin.cons s y := by
        intro s; funext μ
        induction μ using Fin.cases with
        | zero => simp
        | succ i => simp [Pi.single_apply, Fin.succ_ne_zero]
      simp only [e] at h
      exact h
    have hderiv : ∀ t ∈ Icc 0 T, HasDerivWithinAt D (D' t) (Icc 0 T) t := by
      intro t ht
      refine HasDerivWithinAt.fun_sum fun b _ => HasDerivWithinAt.fun_sum fun k hk => ?_
      exact hasDerivWithinAt_sq' ((hasDerivWithinAt_cf (hγ N t ht) b hk).sub
        (hVc b k t).hasDerivWithinAt)
    -- the derivative bound
    have hD'b : ∀ t ∈ Icc 0 T, D' t ≤ 4 * K₁ * D t +
        (4 * K₁ * n * MQ / s ^ 2 + n * MQ / (s ^ 2 * η) + 4 * n * η * Gm ^ 2) := by
      intro t ht
      set W : Fin n → ST d → ℝ := fun b => frz t (V b) with hW
      have hWs : ∀ b, ContDiff ℝ ∞ (W b) := fun b => contDiff_frz t (hV b)
      have hWp : ∀ b, IsSPeriodic (W b) := fun b => isSPeriodic_frz t (hVp b)
      set u : Fin n → ST d → ℝ := fld q (γ N t) with hu
      have hus : ∀ b, ContDiff ℝ ∞ (u b) := fun b => contDiff_fld q _ b
      have hGu : ∀ b, Continuous (genG A F u b) := fun b => (contDiff_genG hA hF hus b).continuous
      have hGW : ∀ b, Continuous (genG A F W b) := fun b => (contDiff_genG hA hF hWs b).continuous
      -- the projection of `V` on the box
      set P : Fin n → ST d → ℝ := fun b => tfs (KatoGalerkin.box N) (coef (V b) t) with hP
      have hPs : ∀ b, ContDiff ℝ ∞ (P b) := fun b => contDiff_tfs _ _
      -- slice identities
      have hsliceV : ∀ b k, coef (pd (V b) 0) t k = coef (genG A F W b) t k := fun b k =>
        coef_congr_slice (fun y => by rw [hVeq b t ht y, genG_frz t hV]) k
      have hcoefW : ∀ b, coef (V b) t = coef (W b) t := fun b => funext fun k =>
        coef_congr_slice (fun y => by rw [hW]; simp [frz_cons]) k
      -- the pairing as a slice integral
      have hpair : ∀ b, ∑ k ∈ KatoGalerkin.box N, (cf q (γ N t) b k - coef (V b) t k) *
          (ĝ t b k - coef (pd (V b) 0) t k) =
          sint (fun x => (u b x - W b x) * (genG A F u b x - genG A F W b x)) t +
          sint (fun x => (W b x - P b x) * (genG A F u b x - genG A F W b x)) t := by
        intro b
        have h1 := sum_box_eq_sint hA hF q (γ N t) b (v := V b) (hGW b) t
        simp only [hsliceV]
        rw [hĝ]
        simp only
        rw [h1, ← sint_add]
        · refine sint_congr_slice fun y => ?_
          simp only [hP, hu]
          ring
        · exact (((hus b).continuous.sub (hWs b).continuous)).mul ((hGu b).sub (hGW b))
        · exact (((hWs b).continuous.sub (hPs b).continuous)).mul ((hGu b).sub (hGW b))
      -- the tail
      have htail : ∀ b, sint (fun x => (W b x - P b x) ^ 2) t ≤ Q 1 (V b) t / s ^ 2 := by
        intro b
        have h := sint_sub_tfs_sq_le (hV b) (hVp b) t N
        refine le_of_eq_of_le ?_ h
        refine sint_congr_slice fun y => ?_
        simp [hW, hP, frz_cons]
      have htailsum : ∑ b, sint (fun x => (W b x - P b x) ^ 2) t ≤ MQ / s ^ 2 := by
        calc ∑ b, sint (fun x => (W b x - P b x) ^ 2) t ≤ ∑ b, Q 1 (V b) t / s ^ 2 :=
              Finset.sum_le_sum fun b _ => htail b
          _ = (∑ b, Q 1 (V b) t) / s ^ 2 := by rw [Finset.sum_div]
          _ ≤ MQ / s ^ 2 := div_le_div_of_nonneg_right (hQle t ht) (by positivity)
      have htail0 : ∀ b, 0 ≤ sint (fun x => (W b x - P b x) ^ 2) t := fun b =>
        sint_nonneg (fun x => sq_nonneg _) t
      -- term 1
      have hT1 : ∑ b, sint (fun x => (u b x - W b x) * (genG A F u b x - genG A F W b x)) t ≤
          K₁ * (2 * D t + 2 * ∑ b, sint (fun x => (W b x - P b x) ^ 2) t) := by
        have h := hK₁ u W hus hWs (fun b => isSPeriodic_fld q _ b) hWp (hbd N t ht).1
          (hWb t ht).1 (hbd N t ht).2 (hWb t ht).2 t
        refine h.trans (mul_le_mul_of_nonneg_left ?_ hK₁0)
        have hsq : ∀ b, sint (fun x => (u b x - W b x) ^ 2) t ≤
            2 * sint (fun x => (u b x - P b x) ^ 2) t +
              2 * sint (fun x => (W b x - P b x) ^ 2) t := by
          intro b
          have c1 : Continuous fun x => (u b x - W b x) ^ 2 :=
            ((hus b).continuous.sub (hWs b).continuous).pow 2
          have c2 : Continuous fun x => (u b x - P b x) ^ 2 :=
            ((hus b).continuous.sub (hPs b).continuous).pow 2
          have c3 : Continuous fun x => (W b x - P b x) ^ 2 :=
            ((hWs b).continuous.sub (hPs b).continuous).pow 2
          have hle := sint_mono (f := fun x => (u b x - W b x) ^ 2)
            (g := fun x => 2 * (u b x - P b x) ^ 2 + 2 * (W b x - P b x) ^ 2) c1
            ((continuous_const.mul c2).add (continuous_const.mul c3))
            (fun x => by nlinarith [sq_nonneg (u b x + W b x - 2 * P b x)]) t
          have e : sint (fun x => 2 * (u b x - P b x) ^ 2 + 2 * (W b x - P b x) ^ 2) t =
              2 * sint (fun x => (u b x - P b x) ^ 2) t +
                2 * sint (fun x => (W b x - P b x) ^ 2) t := by
            rw [sint_add (f := fun x => 2 * (u b x - P b x) ^ 2)
              (g := fun x => 2 * (W b x - P b x) ^ 2) (continuous_const.mul c2)
              (continuous_const.mul c3), sint_const_mul, sint_const_mul]
          linarith
        have hDb : ∀ b, sint (fun x => (u b x - P b x) ^ 2) t =
            ∑ k ∈ KatoGalerkin.box N, (cf q (γ N t) b k - coef (V b) t k) ^ 2 := by
          intro b
          have e : (fun x => (u b x - P b x) ^ 2) =
              fun x => tfs (KatoGalerkin.box N) (fun k => cf q (γ N t) b k - coef (V b) t k) x ^ 2 := by
            funext x; simp only [hu, hP, fld]; rw [tfs_sub]
          rw [e, sint_tfs_sq]
        calc ∑ b, sint (fun x => (u b x - W b x) ^ 2) t
            ≤ ∑ b, (2 * sint (fun x => (u b x - P b x) ^ 2) t +
              2 * sint (fun x => (W b x - P b x) ^ 2) t) := Finset.sum_le_sum fun b _ => hsq b
          _ = 2 * D t + 2 * ∑ b, sint (fun x => (W b x - P b x) ^ 2) t := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
              Finset.sum_congr rfl fun b _ => hDb b]
      -- term 2
      have hT2 : ∀ b, sint (fun x => (W b x - P b x) * (genG A F u b x - genG A F W b x)) t ≤
          sint (fun x => (W b x - P b x) ^ 2) t / (2 * η) + 2 * η * Gm ^ 2 := by
        intro b
        have hcW := (hWs b).continuous
        have hcP := (hPs b).continuous
        have hc1 : Continuous fun x => (W b x - P b x) * (genG A F u b x - genG A F W b x) :=
          (hcW.sub hcP).mul ((hGu b).sub (hGW b))
        have hc2 : Continuous fun x => (W b x - P b x) ^ 2 / (2 * η) + 2 * η * Gm ^ 2 :=
          (((hcW.sub hcP).pow 2).div_const _).add continuous_const
        have h := sint_mono hc1 hc2 (fun x => by
          have hg1 := hGbd u (hbd N t ht).1 (hbd N t ht).2 b x
          have hg2 := hGbd W (hWb t ht).1 (hWb t ht).2 b x
          have habs : |genG A F u b x - genG A F W b x| ≤ 2 * Gm := by
            have := abs_sub (genG A F u b x) (genG A F W b x)
            linarith
          set a := W b x - P b x
          set c := genG A F u b x - genG A F W b x
          have hc2 : c ^ 2 ≤ (2 * Gm) ^ 2 := by
            rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) habs 2
          have key : a * c ≤ a ^ 2 / (2 * η) + η * c ^ 2 / 2 := by
            rw [div_add_div _ _ (by positivity) (by norm_num), le_div_iff₀ (by positivity)]
            nlinarith [sq_nonneg (a - η * c), hη0]
          nlinarith) t
        refine h.trans (le_of_eq ?_)
        have e1 : sint (fun x => (W b x - P b x) ^ 2 / (2 * η) + 2 * η * Gm ^ 2) t =
            sint (fun x => (W b x - P b x) ^ 2 / (2 * η)) t + sint (fun _ => 2 * η * Gm ^ 2) t :=
          sint_add (((hcW.sub hcP).pow 2).div_const _) continuous_const t
        have e2 : sint (fun x => (W b x - P b x) ^ 2 / (2 * η)) t =
            sint (fun x => (W b x - P b x) ^ 2) t / (2 * η) := by
          unfold sint; exact integral_div _ _
        rw [e1, e2, sint_const]
      -- assembly
      have hsplit : D' t = 2 * ∑ b, sint (fun x => (u b x - W b x) *
          (genG A F u b x - genG A F W b x)) t +
          2 * ∑ b, sint (fun x => (W b x - P b x) * (genG A F u b x - genG A F W b x)) t := by
        simp only [hD']
        rw [← mul_add, ← Finset.sum_add_distrib, Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [← hpair b, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
      have hT2s : ∑ b, sint (fun x => (W b x - P b x) * (genG A F u b x - genG A F W b x)) t ≤
          (MQ / s ^ 2) / (2 * η) + n * (2 * η * Gm ^ 2) := by
        calc ∑ b, sint (fun x => (W b x - P b x) * (genG A F u b x - genG A F W b x)) t
            ≤ ∑ b, (sint (fun x => (W b x - P b x) ^ 2) t / (2 * η) + 2 * η * Gm ^ 2) :=
              Finset.sum_le_sum fun b _ => hT2 b
          _ = (∑ b, sint (fun x => (W b x - P b x) ^ 2) t) / (2 * η) + n * (2 * η * Gm ^ 2) := by
              rw [Finset.sum_add_distrib, Finset.sum_div, Finset.sum_const, Finset.card_univ,
                Fintype.card_fin, nsmul_eq_mul]
          _ ≤ (MQ / s ^ 2) / (2 * η) + n * (2 * η * Gm ^ 2) :=
              by
                have := div_le_div_of_nonneg_right htailsum (le_of_lt (by linarith : (0 : ℝ) < 2 * η))
                linarith
      have hnn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have hMQn : MQ ≤ n * MQ ∨ n = 0 := by
        rcases Nat.eq_zero_or_pos n with h | h
        · right; exact h
        · left
          have : (1 : ℝ) ≤ n := by exact_mod_cast h
          nlinarith
      rw [hsplit]
      have hfinal : 2 * (K₁ * (2 * D t + 2 * (MQ / s ^ 2))) +
          2 * ((MQ / s ^ 2) / (2 * η) + n * (2 * η * Gm ^ 2)) ≤
          4 * K₁ * D t + (4 * K₁ * n * MQ / s ^ 2 + n * MQ / (s ^ 2 * η) +
            4 * n * η * Gm ^ 2) := by
        rcases hMQn with h | h
        · have e1 : 2 * ((MQ / s ^ 2) / (2 * η)) = MQ / (s ^ 2 * η) := by
            field_simp
          have h1 : 4 * K₁ * MQ / s ^ 2 ≤ 4 * K₁ * n * MQ / s ^ 2 := by
            apply div_le_div_of_nonneg_right _ (by positivity)
            nlinarith
          have h2 : MQ / (s ^ 2 * η) ≤ n * MQ / (s ^ 2 * η) :=
            div_le_div_of_nonneg_right h (by positivity)
          have e2 : 2 * (K₁ * (2 * D t + 2 * (MQ / s ^ 2))) = 4 * K₁ * D t + 4 * K₁ * MQ / s ^ 2 := by
            ring
          nlinarith
        · -- `n = 0`: all sums over `Fin n` vanish
          subst h
          have hMQz : MQ = 0 := by simp [hMQ]
          rw [hMQz]
          simp
          exact le_of_eq (by ring)
      have hT1' := hT1.trans (mul_le_mul_of_nonneg_left
        (by linarith : 2 * D t + 2 * ∑ b, sint (fun x => (W b x - P b x) ^ 2) t ≤
          2 * D t + 2 * (MQ / s ^ 2)) hK₁0)
      nlinarith [hT1', hT2s]
    -- Grönwall
    have hcont : ContinuousOn D (Icc 0 T) := fun t ht => (hderiv t ht).continuousWithinAt
    set ε : ℝ := 4 * K₁ * n * MQ / s ^ 2 + n * MQ / (s ^ 2 * η) + 4 * n * η * Gm ^ 2 with hε
    have hε0 : 0 ≤ ε := by positivity
    have hgr := SpectralGalerkin.le_gronwall_scalar (f := D) (f' := D') (K := 4 * K₁) (ε := ε)
      hcont (fun t ht => (hderiv t (Ico_subset_Icc_self ht)).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ht)) (fun t ht => hD'b t (Ico_subset_Icc_self ht))
    have hD0 : D 0 = 0 := by
      simp only [hD, hγ0, cf_P0]
      refine Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun k hk => ?_
      rw [if_pos hk, coef_congr_slice (fun y => (hV0 b y).symm) k]
      ring
    have hεle : ε ≤ (4 * K₁ * n * MQ + n * MQ + 4 * n * Gm ^ 2) / s := by
      have e1 : n * MQ / (s ^ 2 * η) = n * MQ / s := by
        rw [hη]; field_simp
      have e2 : 4 * n * η * Gm ^ 2 = 4 * n * Gm ^ 2 / s := by rw [hη]; field_simp
      have h1 : 4 * K₁ * n * MQ / s ^ 2 ≤ 4 * K₁ * n * MQ / s := by
        apply div_le_div_of_nonneg_left (by positivity) hs0
        nlinarith
      rw [hε, e1, e2, add_div, add_div]
      linarith
    intro t ht
    have h1 := hgr t ht
    rw [hD0] at h1
    refine h1.trans ((KatoGalerkin.gronwallBound_le_mul_exp (by positivity) hε0 ht.1).trans ?_)
    have hexp : Real.exp (4 * K₁ * t) ≤ Real.exp (4 * K₁ * T) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left ht.2 (by positivity))
    calc (0 + ε * t) * Real.exp (4 * K₁ * t)
        ≤ ((4 * K₁ * n * MQ + n * MQ + 4 * n * Gm ^ 2) / s * T) * Real.exp (4 * K₁ * T) := by
          rw [zero_add]
          exact mul_le_mul (mul_le_mul hεle ht.2 ht.1 (by positivity)) hexp (by positivity)
            (by positivity)
      _ = (4 * K₁ * n * MQ + n * MQ + 4 * n * Gm ^ 2) * T * Real.exp (4 * K₁ * T) / s := by ring
  -- convergence
  intro t ht b k
  set C' := (4 * K₁ * n * MQ + n * MQ + 4 * n * Gm ^ 2) * T * Real.exp (4 * K₁ * T) with hC'
  have hC'0 : 0 ≤ C' := by positivity
  obtain ⟨N₀, hN₀⟩ := exists_mem_box k
  have hsq : ∀ N, N₀ ≤ N → (cf q (γ N t) b k - coef (V b) t k) ^ 2 ≤
      C' / (2 * π * ((N : ℝ) + 1)) := by
    intro N hN
    have hk : k ∈ KatoGalerkin.box N := box_mono hN hN₀
    refine le_trans ?_ (hmain N t ht)
    have h1 : (cf q (γ N t) b k - coef (V b) t k) ^ 2 ≤
        ∑ k' ∈ KatoGalerkin.box N, (cf q (γ N t) b k' - coef (V b) t k') ^ 2 :=
      Finset.single_le_sum (f := fun k' => (cf q (γ N t) b k' - coef (V b) t k') ^ 2)
        (fun _ _ => sq_nonneg _) hk
    have h2 : ∑ k' ∈ KatoGalerkin.box N, (cf q (γ N t) b k' - coef (V b) t k') ^ 2 ≤
        ∑ b, ∑ k' ∈ KatoGalerkin.box N, (cf q (γ N t) b k' - coef (V b) t k') ^ 2 :=
      Finset.single_le_sum (f := fun b => ∑ k' ∈ KatoGalerkin.box N, (cf q (γ N t) b k' - coef (V b) t k') ^ 2)
        (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ b)
    linarith
  have hlim : Tendsto (fun N : ℕ => Real.sqrt (C' / (2 * π * ((N : ℝ) + 1)))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => C' / (2 * π * ((N : ℝ) + 1))) atTop (𝓝 0) := by
      have : Tendsto (fun N : ℕ => 2 * π * ((N : ℝ) + 1)) atTop atTop := by
        refine Tendsto.const_mul_atTop (by positivity) ?_
        exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
      exact this.const_div_atTop C'
    have := (Real.continuous_sqrt.tendsto 0).comp h1
    rw [Real.sqrt_zero] at this
    exact this
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun N => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_ge_atTop N₀] with N hN
  rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (hsq N hN)

end RenewalGeometry.GenGalCons
