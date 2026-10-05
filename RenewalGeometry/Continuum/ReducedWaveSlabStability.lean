/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.ReducedWaveSlabForcing

/-!
# Common-slab metric stability: the difference energy estimate and the Cauchy property

The analytic core of `thm:hyperbolic` of the Einstein–Standard-Model action-closure manuscript
(`Σ = 𝕋³`, fields smooth and spatially periodic, hypotheses `ReducedWaveStab.MetricHyp`).

* `energyK_ge_Wn`, `energyK_le_Wn` — the differentiated wave energy `E_{h,j}` (order `s - 2`,
  coefficients of `g_h`) is uniformly equivalent to the squared difference norm
  `W = ‖g_h - g_j‖²_{H^{s-1}} + ‖∂ₜg_h - ∂ₜg_j‖²_{H^{s-2}}`.
* `normK_fdiff_le` — `‖F_{h,j}‖_{H^{s-2}} ≤ a_{h,j}√E_{h,j} + σ_{h,j}`,
  `a_{h,j} = C(16 + ‖𝒮ⱼ‖²_{H^{s-2}})^{1/2}`, `σ_{h,j} = C‖𝒮ₕ - 𝒮ⱼ‖_{H^{s-2}}`.
* **`hyperbolic_energy`** (`eq:hyperbolic-energy`):
  `E_{h,j}(t)^{1/2} ≤ (E_{h,j}(0)^{1/2} + C∫₀ᵗ‖𝒮ₕ - 𝒮ⱼ‖_{H^{s-2}}) exp(C∫₀ᵗ(1 + a_{h,j}))`, and
  `sources_bounded`: `sup_{h,j} ∫₀ᵀ a_{h,j} < ∞` when the sources are Cauchy in `L¹_tH^{s-2}`.
* **`common_slab_cauchy`** — "Cauchy initial and source data prove the first two limits":
  if the initial data are Cauchy in `H^{s-1} × H^{s-2}` and the sources are Cauchy in
  `L¹_tH^{s-2}`, then `(g_h)` is Cauchy in `C_tH^{s-1}` and `(∂ₜg_h)` in `C_tH^{s-2}`.
-/

open MeasureTheory Filter Topology Set
open scoped BigOperators ContDiff

noncomputable section

namespace RenewalGeometry.ReducedWaveStab

open SobolevOpen (pd)
open PeriodicCube SymHypEnergy SlabWaveHk SlabSobAlg

set_option linter.unusedSectionVars false

/-! ### Components of the prolongation and the norms of `SlabWaveHk` -/

section General

variable {d : ℕ}

/-- Every component of the `k`-fold prolongation is a spatial word derivative of order `≤ k`. -/
theorem exists_sd_eq_pUK : ∀ (k : ℕ) {ι : Type} (u : ι → ST d → ℝ) (p : PIdx d k ι),
    ∃ b v, v.length ≤ k ∧ pUK k u p = sd v (u b)
  | 0, _, _, p => ⟨p, [], le_rfl, rfl⟩
  | k + 1, _, u, p => by
    obtain ⟨⟨b, o⟩, v, hv, he⟩ := exists_sd_eq_pUK k (pU u) p
    cases o with
    | none => exact ⟨b, v, by omega, he⟩
    | some i =>
      refine ⟨b, i :: v, by simp; omega, ?_⟩
      rw [show pUK (k + 1) u p = pUK k (pU u) p from rfl, he]
      rfl

/-- Spatial word derivatives commute with `∂ₜ`. -/
theorem sd_pd_time : ∀ (v : List (Fin d)) {f : ST d → ℝ}, ContDiff ℝ ∞ f →
    sd v (pd f 0) = pd (sd v f) 0
  | [], _, _ => rfl
  | i :: v, f, hf => by
    rw [sd_cons, sd_cons, pd2_swap hf 0 i.succ]
    exact sd_pd_time v (contDiff_pd_top hf _)

theorem integral_sum_sq_slice {ι : Type*} [Fintype ι] {F : ι → ST d → ℝ}
    (hF : ∀ p, Continuous (F p)) (t : ℝ) :
    ∫ y in Icc (0 : Fin d → ℝ) 1, ∑ p, F p (Fin.cons t y) ^ 2 =
      ∑ p, ∫ y in Icc (0 : Fin d → ℝ) 1, F p (Fin.cons t y) ^ 2 :=
  integral_finsetSum _ fun p _ => integrableOn_sq (hF p) t

/-- `‖F‖_{H^k} = normK k F ≤ (|PIdx| Σ_b Q_k(F_b))^{1/2}`. -/
theorem normK_le {ι : Type} [Fintype ι] [DecidableEq ι] (k : ℕ) {F : ι → ST d → ℝ}
    (hF : ∀ b, ContDiff ℝ ∞ (F b)) (t : ℝ) :
    normK k F t ≤ Real.sqrt (Fintype.card (PIdx d k ι) * ∑ b, Q k (F b) t) := by
  unfold normK l2norm
  refine Real.sqrt_le_sqrt ?_
  have hc : ∀ p, Continuous (pUK k F p) := fun p => by
    obtain ⟨b, v, _, he⟩ := exists_sd_eq_pUK k F p
    rw [he]; exact (contDiff_sd v (hF b)).continuous
  rw [integral_sum_sq_slice hc t]
  calc ∑ p, ∫ y in Icc (0 : Fin d → ℝ) 1, pUK k F p (Fin.cons t y) ^ 2 ≤
      ∑ _p : PIdx d k ι, ∑ b, Q k (F b) t := Finset.sum_le_sum fun p _ => by
        obtain ⟨b, v, hv, he⟩ := exists_sd_eq_pUK k F p
        rw [he]
        exact (term_le_Q hv (F b) t).trans (Finset.single_le_sum (f := fun b => Q k (F b) t)
          (fun b _ => Q_nonneg _ _ _) (Finset.mem_univ b))
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **The energy controls the difference norm**: for a system with `SysHyp … k`,
`Q_{k+1}(u_b) + Q_k(∂ₜu_b) ≤ (|W_{k+1}| + |W_k|)/c · E_k`. -/
theorem Q_le_energyK {ι : Type} [Fintype ι] [DecidableEq ι] {k : ℕ} {S : WaveSys d ι}
    {u F : ι → ST d → ℝ} {T lam M : ℝ} (h : SysHyp S u F T lam M k) (hlam : 0 < lam) {t : ℝ}
    (ht : t ∈ Icc 0 T) (b : ι) :
    Q (k + 1) (u b) t + Q k (pd (u b) 0) t ≤
      ((wordsLE d (k + 1)).card + (wordsLE d k).card) / L2Hyp.cmin lam * energyK k S.γ u t := by
  set c := L2Hyp.cmin lam
  have hc : 0 < c := lt_min hlam one_pos
  set E := energyK k S.γ u t
  have hsu := h.su b
  -- the basic bound for words of length `≤ k`
  have key : ∀ v : List (Fin d), v.length ≤ k →
      ∫ y in Icc (0 : Fin d → ℝ) 1, (pd (sd v (u b)) 0 (Fin.cons t y) ^ 2 +
        ∑ i : Fin d, pd (sd v (u b)) i.succ (Fin.cons t y) ^ 2 + sd v (u b) (Fin.cons t y) ^ 2) ≤
        E / c := fun v hv => by
    rw [le_div_iff₀ hc, mul_comm]
    exact energyK_ge k h hlam ht b v hv
  have cont : ∀ v : List (Fin d), Continuous fun x => pd (sd v (u b)) 0 x ^ 2 +
      ∑ i : Fin d, pd (sd v (u b)) i.succ x ^ 2 + sd v (u b) x ^ 2 := fun v => by
    have := fun μ => (contDiff_pd_top (contDiff_sd v hsu) μ).continuous
    have := (contDiff_sd v hsu).continuous
    fun_prop
  have mono : ∀ (v : List (Fin d)) (G : ST d → ℝ), Continuous G →
      (∀ x, G x ^ 2 ≤ pd (sd v (u b)) 0 x ^ 2 + ∑ i : Fin d, pd (sd v (u b)) i.succ x ^ 2 +
        sd v (u b) x ^ 2) → v.length ≤ k →
      ∫ y in Icc (0 : Fin d → ℝ) 1, G (Fin.cons t y) ^ 2 ≤ E / c := fun v G hG hle hv =>
    (setIntegral_mono_on (integrableOn_sq hG t) (integrableOn_slice (cont v) t) measurableSet_Icc
      fun y _ => hle _).trans (key v hv)
  have hsq : ∀ v : List (Fin d), ∀ x, ∀ i : Fin d, pd (sd v (u b)) i.succ x ^ 2 ≤
      pd (sd v (u b)) 0 x ^ 2 + ∑ i : Fin d, pd (sd v (u b)) i.succ x ^ 2 + sd v (u b) x ^ 2 :=
    fun v x i => by
      have := Finset.single_le_sum (f := fun i : Fin d => pd (sd v (u b)) i.succ x ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
      nlinarith [sq_nonneg (pd (sd v (u b)) 0 x), sq_nonneg (sd v (u b) x)]
  have h1 : Q (k + 1) (u b) t ≤ (wordsLE d (k + 1)).card * (E / c) := by
    unfold Q
    calc _ ≤ ∑ _w ∈ wordsLE d (k + 1), E / c := Finset.sum_le_sum fun w hw => by
          have hw' := mem_wordsLE.mp hw
          by_cases hwk : w.length ≤ k
          · exact mono w (sd w (u b)) (contDiff_sd w hsu).continuous (fun x => by
              nlinarith [sq_nonneg (pd (sd w (u b)) 0 x), Finset.sum_nonneg fun i (_ : i ∈
                (Finset.univ : Finset (Fin d))) => sq_nonneg (pd (sd w (u b)) i.succ x)]) hwk
          · have hne : w ≠ [] := by rintro rfl; simp at hwk
            have e := List.dropLast_append_getLast hne
            have hl : w.dropLast.length ≤ k := by simp; omega
            rw [← e, sd_append_single]
            exact mono _ _ (contDiff_pd_top (contDiff_sd _ hsu) _).continuous
              (fun x => hsq _ x _) hl
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  have h2 : Q k (pd (u b) 0) t ≤ (wordsLE d k).card * (E / c) := by
    unfold Q
    calc _ ≤ ∑ _w ∈ wordsLE d k, E / c := Finset.sum_le_sum fun w hw => by
          rw [sd_pd_time w hsu]
          exact mono w _ (contDiff_pd_top (contDiff_sd w hsu) 0).continuous (fun x => by
            nlinarith [sq_nonneg (sd w (u b) x), Finset.sum_nonneg fun i (_ : i ∈
              (Finset.univ : Finset (Fin d))) => sq_nonneg (pd (sd w (u b)) i.succ x)])
            (mem_wordsLE.mp hw)
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  calc _ ≤ (wordsLE d (k + 1)).card * (E / c) + (wordsLE d k).card * (E / c) := add_le_add h1 h2
    _ = _ := by ring

/-- **The energy is controlled by the difference norm** (at any slab time): with
`|γ^{ij}| ≤ M` on the slab, `E_k ≤ (1 + d²M)|PIdx| Σ_b (Q_k(∂ₜu_b) + (d+1) Q_{k+1}(u_b))`. -/
theorem energyK_le_Q {ι : Type} [Fintype ι] [DecidableEq ι] {k : ℕ} {S : WaveSys d ι}
    {u F : ι → ST d → ℝ} {T lam M : ℝ} (h : SysHyp S u F T lam M k) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    energyK k S.γ u t ≤ (1 + (d : ℝ) ^ 2 * M) * Fintype.card (PIdx d k ι) *
      ∑ b, (Q k (pd (u b) 0) t + (d + 1) * Q (k + 1) (u b) t) := by
  unfold energyK SlabWaveHk.energy
  have hM := h.M_nonneg
  have hγ : ∀ y : Fin d → ℝ, ∀ i j, |S.γ i j (Fin.cons t y)| ≤ M := fun y i j =>
    h.bγ i j [] (Nat.zero_le _) _ (by rw [cons_zero_eq]; exact ht)
  have hcomp : ∀ p, ContDiff ℝ ∞ (pUK k u p) := fun p => by
    obtain ⟨b, v, _, he⟩ := exists_sd_eq_pUK k u p
    rw [he]; exact contDiff_sd v (h.su b)
  set G : PIdx d k ι → ST d → ℝ := fun p x => pd (pUK k u p) 0 x ^ 2 +
    ∑ i : Fin d, pd (pUK k u p) i.succ x ^ 2 + pUK k u p x ^ 2
  have hG : ∀ p, Continuous (G p) := fun p => by
    have := fun μ => (contDiff_pd_top (hcomp p) μ).continuous
    have := (hcomp p).continuous
    fun_prop
  -- pointwise: the density is at most `(1 + d² M) Σ_p G_p`
  have hpt : ∀ y : Fin d → ℝ, dens S.γ (pUK k u) (Fin.cons t y) ≤
      (1 + (d : ℝ) ^ 2 * M) * ∑ p, G p (Fin.cons t y) := by
    intro y
    unfold dens
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun p _ => ?_
    set a : Fin d → ℝ := fun i => pd (pUK k u p) i.succ (Fin.cons t y)
    have hq : ∑ i : Fin d, ∑ j : Fin d, S.γ i j (Fin.cons t y) * a i * a j ≤
        (d : ℝ) ^ 2 * M * ∑ i : Fin d, a i ^ 2 := by
      have h1 : ∀ i j, S.γ i j (Fin.cons t y) * a i * a j ≤ M * ∑ l : Fin d, a l ^ 2 := by
        intro i j
        have hai := Finset.single_le_sum (f := fun l : Fin d => a l ^ 2) (fun _ _ => sq_nonneg _)
          (Finset.mem_univ i)
        have haj := Finset.single_le_sum (f := fun l : Fin d => a l ^ 2) (fun _ _ => sq_nonneg _)
          (Finset.mem_univ j)
        have hab : |a i * a j| ≤ ∑ l : Fin d, a l ^ 2 := by
          rw [abs_mul]
          nlinarith [abs_nonneg (a i), abs_nonneg (a j), sq_abs (a i), sq_abs (a j),
            sq_nonneg (|a i| - |a j|)]
        calc S.γ i j (Fin.cons t y) * a i * a j ≤ |S.γ i j (Fin.cons t y) * (a i * a j)| := by
              rw [← mul_assoc]; exact le_abs_self _
          _ = |S.γ i j (Fin.cons t y)| * |a i * a j| := abs_mul _ _
          _ ≤ M * ∑ l : Fin d, a l ^ 2 := mul_le_mul (hγ y i j) hab (abs_nonneg _) hM
      calc _ ≤ ∑ _i : Fin d, ∑ _j : Fin d, M * ∑ l : Fin d, a l ^ 2 :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h1 i j
        _ = _ := by simp; ring
    have hs : 0 ≤ ∑ i : Fin d, a i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have h0 := sq_nonneg (pd (pUK k u p) 0 (Fin.cons t y))
    have h2 := sq_nonneg (pUK k u p (Fin.cons t y))
    show _ ≤ (1 + (d : ℝ) ^ 2 * M) * (pd (pUK k u p) 0 (Fin.cons t y) ^ 2 +
      ∑ i : Fin d, a i ^ 2 + pUK k u p (Fin.cons t y) ^ 2)
    have : 0 ≤ (d : ℝ) ^ 2 * M := by positivity
    nlinarith
  have hint : ∫ y in Icc (0 : Fin d → ℝ) 1, dens S.γ (pUK k u) (Fin.cons t y) ≤
      (1 + (d : ℝ) ^ 2 * M) * ∑ p, ∫ y in Icc (0 : Fin d → ℝ) 1, G p (Fin.cons t y) := by
    rw [← integral_finsetSum _ fun p _ => integrableOn_slice (hG p) t, ← integral_const_mul]
    refine setIntegral_mono_on ?_ ?_ measurableSet_Icc fun y _ => hpt y
    · exact integrableOn_slice (f := fun x => dens S.γ (pUK k u) x)
        ((SysHyp.prolongK (r := 0) k (by rw [Nat.zero_add]; exact h)).toL2Hyp.continuous_dens |>
          fun hc => by rw [prolongK_γ] at hc; exact hc) t
    · exact (integrable_finsetSum _ fun p _ => integrableOn_slice (hG p) t).const_mul _
  -- each component
  have hp : ∀ p, ∫ y in Icc (0 : Fin d → ℝ) 1, G p (Fin.cons t y) ≤
      ∑ b, (Q k (pd (u b) 0) t + (d + 1) * Q (k + 1) (u b) t) := by
    intro p
    obtain ⟨b, v, hv, he⟩ := exists_sd_eq_pUK k u p
    have hsb := h.su b
    have hcv := contDiff_sd v hsb
    have iA := integrableOn_sq (contDiff_sd v (contDiff_pd_top hsb 0)).continuous t
    have iB : ∀ i : Fin d, IntegrableOn (fun y => pd (sd v (u b)) i.succ (Fin.cons t y) ^ 2)
        (Icc 0 1) := fun i => integrableOn_sq (contDiff_pd_top hcv _).continuous t
    have iSm := integrable_finsetSum (s := Finset.univ) (fun i _ => iB i)
    have iC := integrableOn_sq hcv.continuous t
    have iAB : IntegrableOn (fun y => sd v (pd (u b) 0) (Fin.cons t y) ^ 2 +
        ∑ i : Fin d, pd (sd v (u b)) i.succ (Fin.cons t y) ^ 2) (Icc 0 1) := by
      have c1 := (contDiff_sd v (contDiff_pd_top hsb 0)).continuous
      have c2 := fun i : Fin d => (contDiff_pd_top hcv i.succ).continuous
      exact integrableOn_slice (f := fun x => sd v (pd (u b) 0) x ^ 2 +
        ∑ i : Fin d, pd (sd v (u b)) i.succ x ^ 2) (by fun_prop) t
    have eG : ∀ y : Fin d → ℝ, G p (Fin.cons t y) = sd v (pd (u b) 0) (Fin.cons t y) ^ 2 +
        ∑ i : Fin d, pd (sd v (u b)) i.succ (Fin.cons t y) ^ 2 + sd v (u b) (Fin.cons t y) ^ 2 :=
      fun y => by simp only [G, he, ← sd_pd_time v hsb]
    simp_rw [eG]
    rw [integral_add (μ := volume.restrict (Icc (0 : Fin d → ℝ) 1))
        (f := fun y => sd v (pd (u b) 0) (Fin.cons t y) ^ 2 +
        ∑ i : Fin d, pd (sd v (u b)) i.succ (Fin.cons t y) ^ 2)
        (g := fun y => sd v (u b) (Fin.cons t y) ^ 2) iAB iC,
      integral_add (μ := volume.restrict (Icc (0 : Fin d → ℝ) 1))
        (f := fun y => sd v (pd (u b) 0) (Fin.cons t y) ^ 2)
        (g := fun y => ∑ i : Fin d, pd (sd v (u b)) i.succ (Fin.cons t y) ^ 2) iA iSm,
      integral_finsetSum _ fun i _ => iB i]
    have t1 := term_le_Q hv (pd (u b) 0) t
    have t2 : ∀ i : Fin d, ∫ y in Icc (0 : Fin d → ℝ) 1, pd (sd v (u b)) i.succ (Fin.cons t y) ^ 2
        ≤ Q (k + 1) (u b) t := fun i => by
      rw [← sd_append_single]; exact term_le_Q (by simp; omega) _ t
    have t3 := term_le_Q (k := k + 1) (by omega) (u b) t (w := v)
    have t2' : ∑ i : Fin d, ∫ y in Icc (0 : Fin d → ℝ) 1,
        pd (sd v (u b)) i.succ (Fin.cons t y) ^ 2 ≤ d * Q (k + 1) (u b) t := by
      calc _ ≤ ∑ _i : Fin d, Q (k + 1) (u b) t := Finset.sum_le_sum fun i _ => t2 i
        _ = _ := by simp
    have hb : Q k (pd (u b) 0) t + (d + 1) * Q (k + 1) (u b) t ≤
        ∑ b, (Q k (pd (u b) 0) t + (d + 1) * Q (k + 1) (u b) t) :=
      Finset.single_le_sum (f := fun b => Q k (pd (u b) 0) t + (d + 1) * Q (k + 1) (u b) t)
        (fun b _ => add_nonneg (Q_nonneg _ _ _) (mul_nonneg (by positivity) (Q_nonneg _ _ _)))
        (Finset.mem_univ b)
    linarith
  have hsum : ∑ p, ∫ y in Icc (0 : Fin d → ℝ) 1, G p (Fin.cons t y) ≤
      Fintype.card (PIdx d k ι) * ∑ b, (Q k (pd (u b) 0) t + (d + 1) * Q (k + 1) (u b) t) := by
    calc ∑ p, ∫ y in Icc (0 : Fin d → ℝ) 1, G p (Fin.cons t y) ≤
        ∑ _p : PIdx d k ι, ∑ b, (Q k (pd (u b) 0) t + (d + 1) * Q (k + 1) (u b) t) :=
          Finset.sum_le_sum fun p _ => hp p
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h1M : 0 ≤ 1 + (d : ℝ) ^ 2 * M := by positivity
  calc _ ≤ (1 + (d : ℝ) ^ 2 * M) * ∑ p, ∫ y in Icc (0 : Fin d → ℝ) 1, G p (Fin.cons t y) := hint
    _ ≤ (1 + (d : ℝ) ^ 2 * M) * (Fintype.card (PIdx d k ι) *
        ∑ b, (Q k (pd (u b) 0) t + (d + 1) * Q (k + 1) (u b) t)) :=
        mul_le_mul_of_nonneg_left hsum h1M
    _ = _ := by ring


end General

theorem sqrt_add_le' {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  have h1 := Real.sq_sqrt ha
  have h2 := Real.sq_sqrt hb
  have h3 := mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)
  have h4 : a + b ≤ (Real.sqrt a + Real.sqrt b) ^ 2 := by nlinarith
  calc Real.sqrt (a + b) ≤ Real.sqrt ((Real.sqrt a + Real.sqrt b) ^ 2) := Real.sqrt_le_sqrt h4
    _ = Real.sqrt a + Real.sqrt b := Real.sqrt_sq (by positivity)

end ReducedWaveStab

end RenewalGeometry
