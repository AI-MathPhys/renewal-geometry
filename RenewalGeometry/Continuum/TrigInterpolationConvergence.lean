/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.SampledRecordSharpTail

/-!
# Convergence of trigonometric interpolation of samples of smooth periodic fields

Generic infrastructure (no renewal notions) for `cor:local-calibration-nonempty` of the
Einstein–Standard-Model action-closure manuscript ("Smooth Fourier decay and the aliasing formula
give uniform `H^q` bounds and convergence of each fixed number of reconstructed derivatives").

Setting: a smooth field `Y : ℝ⁴ → V` (finite-dimensional real normed `V`) of period `2π` in every
coordinate, its nodal samples `𝖲_h Y` on the periodic grid `(ℤ/n)⁴` (`h = 2π/n`) and the
trigonometric reconstruction `𝓘_h = TrigInterp.recon` (odd `n`).

## Main results

* `exists_bound_iteratedFDeriv`: smooth periodic fields have bounded derivatives of every order.
* `cn_coefOf_le`, `norm_iteratedFDeriv_recon_le'`: `‖D^i 𝓘_h u‖ ≤ 162·4^i sup|u| + τ_{h,i}(1)`.
* `exists_node_near`: every point is within sup-distance `h` of a node modulo `2πℤ⁴`.
* `norm_le_sum_evec`: operator norms of multilinear maps on `(ℝ⁴)^j` from coordinate vectors.
* `norm_cDiff_sub_le`: iterated differences are `O(h)`-consistent with derivatives,
  `‖Δ_wF - h^{|w|} D^{|w|}F(e_w)‖ ≤ |w| h^{|w|+1} sup_{i ≤ |w|+1} ‖D^iF‖`.
* `norm_recon_sub_le`: `‖𝓘_h(𝖲_hY) - Y‖_∞ ≤ (648 A + τ_{h,1}(1) + B₁) h`.
* **`norm_iteratedFDeriv_recon_sub_le`**: for every `j`, `‖D^j(𝓘_h(𝖲_hY) - Y)‖_∞ ≤ C_j M h`
  uniformly in odd `n`, where `M` bounds the derivatives of `Y` of order `≤ j + 5`.
-/

open Finset Filter Topology Set Metric
open scoped Real ContDiff

noncomputable section

namespace RenewalGeometry.TrigConv

open DiscreteEulerConsistency (R4 pos samp IsPeriodic evec realVec castVec)
open ShiftedJetAction (Grid)
open TrigInterp (recon reconLow tau)
open SampledTail

set_option linter.unusedSectionVars false

/-! ### Bounds for smooth periodic fields -/

section Periodic

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- A continuous field with period `L > 0` in every coordinate is bounded. -/
theorem exists_bound_of_periodic {G : R4 → W} (hG : Continuous G) {L : ℝ} (hL : 0 < L)
    (hper : IsPeriodic L G) : ∃ M, ∀ z, ‖G z‖ ≤ M := by
  set Q : Set R4 := Set.pi univ (fun _ => Icc 0 L)
  have hQ : IsCompact Q := isCompact_univ_pi fun _ => isCompact_Icc
  obtain ⟨M, hM⟩ := hQ.exists_bound_of_continuousOn hG.continuousOn
  refine ⟨M, fun z => ?_⟩
  set k : Fin 4 → ℤ := fun μ => ⌊z μ / L⌋
  set z' : R4 := z - L • realVec k
  have hz' : z' ∈ Q := by
    intro μ _
    simp only [z', Pi.sub_apply, Pi.smul_apply, realVec, smul_eq_mul, k]
    constructor
    · have := Int.floor_le (z μ / L); rw [le_div_iff₀ hL] at this; linarith
    · have := Int.lt_floor_add_one (z μ / L); rw [div_lt_iff₀ hL] at this; linarith
  have e : G z = G z' := by
    have := hper.add_intVec k z'
    rw [show z' + L • realVec k = z by simp [z']] at this
    exact this
  rw [e]; exact hM z' hz'

theorem isPeriodic_iteratedFDeriv {L : ℝ} {Y : R4 → W} (hY : IsPeriodic L Y) (r : ℕ) :
    IsPeriodic L (iteratedFDeriv ℝ r Y) := fun z μ => by
  rw [← iteratedFDeriv_comp_add_right]
  congr 1
  funext w
  exact hY w μ

/-- **A smooth periodic field has bounded derivatives of every order `≤ q`.** -/
theorem exists_bound_iteratedFDeriv {Y : R4 → W} (hY : ContDiff ℝ ∞ Y) {L : ℝ} (hL : 0 < L)
    (hper : IsPeriodic L Y) (q : ℕ) : ∃ M, ∀ r ≤ q, ∀ z, ‖iteratedFDeriv ℝ r Y z‖ ≤ M := by
  have hb : ∀ r : ℕ, ∃ M, ∀ z, ‖iteratedFDeriv ℝ r Y z‖ ≤ M := fun r =>
    exists_bound_of_periodic (hY.continuous_iteratedFDeriv (by exact_mod_cast le_top)) hL
      (isPeriodic_iteratedFDeriv hper r)
  induction q with
  | zero =>
    obtain ⟨M, hM⟩ := hb 0
    exact ⟨M, fun r hr z => by rw [Nat.le_zero.1 hr]; exact hM z⟩
  | succ q ih =>
    obtain ⟨M, hM⟩ := ih
    obtain ⟨M', hM'⟩ := hb (q + 1)
    refine ⟨max M M', fun r hr z => ?_⟩
    rcases Nat.lt_or_eq_of_le hr with h | h
    · exact (hM r (Nat.lt_succ_iff.mp h) z).trans (le_max_left _ _)
    · rw [h]; exact (hM' z).trans (le_max_right _ _)

end Periodic

/-! ### Uniform closeness of the reconstruction of samples -/

section Recon

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The real Fourier coefficient pair of a record bounded by `A` has size `≤ 2A`. -/
theorem cn_coefOf_le {n : ℕ} [NeZero n] {u : (Fin 4 → ZMod n) → V} {A : ℝ}
    (hA : ∀ y, ‖u y‖ ≤ A) (ℓ : Fin 4 → ℤ) : VecTrig.cn (TrigInterp.coefOf n u) ℓ ≤ 2 * A := by
  have hn : (0 : ℝ) < (n : ℝ) ^ 4 := by
    have : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
    positivity
  have hcard : ∑ _y : Fin 4 → ZMod n, A = (n : ℝ) ^ 4 * A := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; simp [ZMod.card]
  have key : ∀ g : (Fin 4 → ZMod n) → ℝ, (∀ y, |g y| ≤ 1) →
      ‖((n : ℝ) ^ 4)⁻¹ • ∑ y, g y • u y‖ ≤ A := by
    intro g hg
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hn.le)]
    have : ‖∑ y, g y • u y‖ ≤ (n : ℝ) ^ 4 * A := by
      refine (norm_sum_le _ _).trans ?_
      rw [← hcard]
      refine Finset.sum_le_sum fun y _ => ?_
      rw [norm_smul, Real.norm_eq_abs]
      have := hg y
      have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA y)
      nlinarith [norm_nonneg (u y), hA y, abs_nonneg (g y)]
    calc ((n : ℝ) ^ 4)⁻¹ * ‖∑ y, g y • u y‖ ≤ ((n : ℝ) ^ 4)⁻¹ * ((n : ℝ) ^ 4 * A) :=
          mul_le_mul_of_nonneg_left this (inv_nonneg.mpr hn.le)
      _ = A := by rw [← mul_assoc, inv_mul_cancel₀ hn.ne', one_mul]
  unfold VecTrig.cn TrigInterp.coefOf
  have h1 := key (fun y => Real.cos (VecTrig.phase ℓ (TrigInterp.gpos n y)))
    (fun y => Real.abs_cos_le_one _)
  have h2 := key (fun y => Real.sin (VecTrig.phase ℓ (TrigInterp.gpos n y)))
    (fun y => Real.abs_sin_le_one _)
  simp only at h1 h2 ⊢
  linarith

theorem card_lowBox_one_le (n : ℕ) : (TrigInterp.lowBox (d := 4) n 1).card ≤ 81 := by
  have hsub : TrigInterp.lowBox (d := 4) n 1 ⊆ SobolevReader.box 1 := by
    intro ℓ hℓ
    rw [TrigInterp.lowBox, Finset.mem_filter] at hℓ
    rw [SobolevReader.box, Fintype.mem_piFinset]
    intro μ
    have h := hℓ.2 μ
    rw [Finset.mem_Icc]
    have h' : |ℓ μ| ≤ 1 := by exact_mod_cast h
    constructor <;> push_cast <;> linarith [abs_le.mp h']
  have := Finset.card_le_card hsub
  rw [SobolevReader.card_box] at this
  simpa using this

/-- **Uniform first-derivative bound for the reconstruction**:
`‖D 𝓘_h u‖ ≤ 648 A + τ_{h,1}(1)` for a record bounded by `A`. -/
theorem norm_fderiv_recon_le {n : ℕ} [NeZero n] {u : (Fin 4 → ZMod n) → V} {A : ℝ}
    (hA : ∀ y, ‖u y‖ ≤ A) (x : Fin 4 → ℝ) :
    ‖iteratedFDeriv ℝ 1 (recon n u) x‖ ≤ 648 * A + tau n 1 1 u := by
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0)
  refine (VecTrig.norm_iteratedFDeriv_tp_le _ _ 1 x).trans ?_
  rw [← Finset.sum_filter_add_sum_filter_not (TrigInterp.box n 4)
    (fun ℓ => ∀ μ, |(ℓ μ : ℝ)| ≤ 1)]
  have hlow : ∑ ℓ ∈ (TrigInterp.box n 4).filter (fun ℓ => ∀ μ, |(ℓ μ : ℝ)| ≤ 1),
      VecTrig.l1 ℓ ^ 1 * VecTrig.cn (TrigInterp.coefOf n u) ℓ ≤ 648 * A := by
    calc ∑ ℓ ∈ (TrigInterp.box n 4).filter (fun ℓ => ∀ μ, |(ℓ μ : ℝ)| ≤ 1),
          VecTrig.l1 ℓ ^ 1 * VecTrig.cn (TrigInterp.coefOf n u) ℓ
        ≤ ∑ _ℓ ∈ TrigInterp.lowBox (d := 4) n 1, 4 * (2 * A) := by
          refine Finset.sum_le_sum fun ℓ hℓ => ?_
          rw [Finset.mem_filter] at hℓ
          have hl : VecTrig.l1 ℓ ≤ 4 := by
            unfold VecTrig.l1
            calc ∑ μ, |(ℓ μ : ℝ)| ≤ ∑ _μ : Fin 4, (1 : ℝ) := Finset.sum_le_sum fun μ _ => hℓ.2 μ
              _ = 4 := by simp
          rw [pow_one]
          exact mul_le_mul hl (cn_coefOf_le hA ℓ) (VecTrig.cn_nonneg _ _) (by norm_num)
      _ = (TrigInterp.lowBox (d := 4) n 1).card * (4 * (2 * A)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 81 * (4 * (2 * A)) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast card_lowBox_one_le n) (by positivity)
      _ = 648 * A := by ring
  have htail : ∑ ℓ ∈ (TrigInterp.box n 4).filter (fun ℓ => ¬ ∀ μ, |(ℓ μ : ℝ)| ≤ 1),
      VecTrig.l1 ℓ ^ 1 * VecTrig.cn (TrigInterp.coefOf n u) ℓ ≤ tau n 1 1 u := by
    unfold TrigInterp.tau TrigInterp.tailBox
    refine Finset.sum_le_sum fun ℓ _ => ?_
    refine mul_le_mul_of_nonneg_right ?_ (VecTrig.cn_nonneg _ _)
    rw [pow_one, pow_one, div_one]
    linarith
  linarith

/-- A point of `ℝ⁴` lies within sup-distance `h` of a node, modulo the period lattice `2π ℤ⁴`. -/
theorem exists_node_near {n : ℕ} [NeZero n] (z : R4) :
    ∃ (x : Grid n) (k : Fin 4 → ℤ),
      ‖z - (2 * π) • realVec k - pos (2 * π / n) x‖ ≤ 2 * π / n := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have h2π : (0 : ℝ) < 2 * π := by positivity
  set h : ℝ := 2 * π / n with hh
  have hh0 : 0 < h := by rw [hh]; positivity
  set k : Fin 4 → ℤ := fun μ => ⌊z μ / (2 * π)⌋
  set z' : R4 := z - (2 * π) • realVec k with hz'
  have hz'0 : ∀ μ, 0 ≤ z' μ ∧ z' μ < 2 * π := by
    intro μ
    simp only [z', Pi.sub_apply, Pi.smul_apply, realVec, smul_eq_mul, k]
    constructor
    · have := Int.floor_le (z μ / (2 * π)); rw [le_div_iff₀ h2π] at this; linarith
    · have := Int.lt_floor_add_one (z μ / (2 * π)); rw [div_lt_iff₀ h2π] at this; linarith
  set m : Fin 4 → ℕ := fun μ => ⌊z' μ / h⌋₊
  have hm : ∀ μ, m μ < n := by
    intro μ
    have h1 : z' μ / h < n := by
      rw [div_lt_iff₀ hh0, hh]; field_simp; linarith [(hz'0 μ).2]
    have := Nat.floor_lt' (n := n) (Nat.pos_of_ne_zero (NeZero.ne n)).ne' |>.mpr h1
    exact this
  refine ⟨fun μ => (m μ : ZMod n), k, ?_⟩
  rw [pi_norm_le_iff_of_nonneg hh0.le]
  intro μ
  have hval : ((m μ : ZMod n)).val = m μ := ZMod.val_natCast_of_lt (hm μ)
  simp only [Pi.sub_apply, pos, hval]
  rw [Real.norm_eq_abs, abs_le]
  have hfl := Nat.floor_le (div_nonneg (hz'0 μ).1 hh0.le) (a := z' μ / h)
  have hlt := Nat.lt_floor_add_one (z' μ / h)
  rw [le_div_iff₀ hh0] at hfl
  rw [div_lt_iff₀ hh0] at hlt
  have e : z μ - ((2 * π) • realVec k) μ = z' μ := by simp [z']
  rw [e]
  have hmμ : (m μ : ℝ) = (⌊z' μ / h⌋₊ : ℝ) := rfl
  rw [hmμ]
  constructor <;> nlinarith

/-- **The reconstruction of the samples is uniformly `O(h)`-close to the field** (odd `n`): for a
`C¹` field `Y` of period `2π` with `|Y| ≤ A`, `‖DY‖ ≤ B₁`,
`‖𝓘_h(𝖲_h Y)(z) - Y(z)‖ ≤ (648 A + τ_{h,1}(1) + B₁) h`. -/
theorem norm_recon_sub_le {n : ℕ} [NeZero n] (hn : Odd n) {Y : R4 → V} (hY : ContDiff ℝ 1 Y)
    (hper : IsPeriodic (2 * π) Y) {A B₁ : ℝ} (hA : ∀ z, ‖Y z‖ ≤ A)
    (hB : ∀ z, ‖iteratedFDeriv ℝ 1 Y z‖ ≤ B₁) (z : R4) :
    ‖recon n (samp (n := n) (2 * π / n) Y) z - Y z‖ ≤
      (648 * A + tau n 1 1 (samp (n := n) (2 * π / n) Y) + B₁) * (2 * π / n) := by
  set h : ℝ := 2 * π / n with hh
  set u : Grid n → V := samp (n := n) h Y with hu
  have huA : ∀ y, ‖u y‖ ≤ A := fun y => hA _
  obtain ⟨x, k, hx⟩ := exists_node_near (n := n) z
  set z' : R4 := z - (2 * π) • realVec k with hz'
  -- periodic reduction
  have hR : recon n u z = recon n u z' := by
    have := DiscreteEulerConsistency.IsPeriodic.add_intVec (Y := recon n u)
      (fun w μ => TrigInterp.recon_periodic n u w μ) k z'
    rw [show z' + (2 * π) • realVec k = z by simp [z']] at this
    exact this
  have hYz : Y z = Y z' := by
    have := hper.add_intVec k z'
    rw [show z' + (2 * π) • realVec k = z by simp [z']] at this
    exact this
  -- interpolation at the node
  have hnode : recon n u (pos h x) = Y (pos h x) := by
    have : pos h x = TrigInterp.gpos n x := rfl
    rw [this, TrigInterp.recon_gpos n hn u x]
    rfl
  -- mean value for both fields
  have hdR : ∀ w, ‖fderiv ℝ (recon n u) w‖ ≤ 648 * A + tau n 1 1 u := by
    intro w
    rw [← norm_iteratedFDeriv_one]
    exact norm_fderiv_recon_le huA w
  have hdY : ∀ w, ‖fderiv ℝ Y w‖ ≤ B₁ := by
    intro w; rw [← norm_iteratedFDeriv_one]; exact hB w
  have hRd : Differentiable ℝ (recon n u) :=
    (VecTrig.contDiff_tp (n := 1) _ _).differentiable one_ne_zero
  have hYd : Differentiable ℝ Y := hY.differentiable one_ne_zero
  have m1 := Convex.norm_image_sub_le_of_norm_fderiv_le (s := Set.univ) (fun w _ => hRd w)
    (fun w _ => hdR w) convex_univ (Set.mem_univ (pos h x)) (Set.mem_univ z')
  have m2 := Convex.norm_image_sub_le_of_norm_fderiv_le (s := Set.univ) (fun w _ => hYd w)
    (fun w _ => hdY w) convex_univ (Set.mem_univ (pos h x)) (Set.mem_univ z')
  have hdist : ‖z' - pos h x‖ ≤ h := hx
  have hτ0 : 0 ≤ tau n 1 1 u := TrigInterp.tau_nonneg n one_pos 1 u
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0)
  have hB0 : 0 ≤ B₁ := (norm_nonneg _).trans (hB 0)
  rw [hR, hYz]
  calc ‖recon n u z' - Y z'‖
      = ‖(recon n u z' - recon n u (pos h x)) - (Y z' - Y (pos h x))‖ := by
        rw [hnode]; congr 1; abel
    _ ≤ ‖recon n u z' - recon n u (pos h x)‖ + ‖Y z' - Y (pos h x)‖ := norm_sub_le _ _
    _ ≤ (648 * A + tau n 1 1 u) * ‖z' - pos h x‖ + B₁ * ‖z' - pos h x‖ := add_le_add m1 m2
    _ ≤ (648 * A + tau n 1 1 u + B₁) * h := by
        have := norm_nonneg (z' - pos h x)
        nlinarith

end Recon

/-! ### Higher derivatives of the reconstruction -/

section Derivs

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **Uniform derivative bounds for the reconstruction** of a record bounded by `A`:
`‖D^i 𝓘_h u‖ ≤ 162·4^i A + τ_{h,i}(1)`. -/
theorem norm_iteratedFDeriv_recon_le' {n : ℕ} [NeZero n] {u : (Fin 4 → ZMod n) → V} {A : ℝ}
    (hA : ∀ y, ‖u y‖ ≤ A) (i : ℕ) (x : Fin 4 → ℝ) :
    ‖iteratedFDeriv ℝ i (recon n u) x‖ ≤ 162 * 4 ^ i * A + tau n 1 i u := by
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0)
  refine (VecTrig.norm_iteratedFDeriv_tp_le _ _ i x).trans ?_
  rw [← Finset.sum_filter_add_sum_filter_not (TrigInterp.box n 4)
    (fun ℓ => ∀ μ, |(ℓ μ : ℝ)| ≤ 1)]
  have hlow : ∑ ℓ ∈ (TrigInterp.box n 4).filter (fun ℓ => ∀ μ, |(ℓ μ : ℝ)| ≤ 1),
      VecTrig.l1 ℓ ^ i * VecTrig.cn (TrigInterp.coefOf n u) ℓ ≤ 162 * 4 ^ i * A := by
    calc ∑ ℓ ∈ (TrigInterp.box n 4).filter (fun ℓ => ∀ μ, |(ℓ μ : ℝ)| ≤ 1),
          VecTrig.l1 ℓ ^ i * VecTrig.cn (TrigInterp.coefOf n u) ℓ
        ≤ ∑ _ℓ ∈ TrigInterp.lowBox (d := 4) n 1, (4 : ℝ) ^ i * (2 * A) := by
          refine Finset.sum_le_sum fun ℓ hℓ => ?_
          rw [Finset.mem_filter] at hℓ
          have hl : VecTrig.l1 ℓ ≤ 4 := by
            unfold VecTrig.l1
            calc ∑ μ, |(ℓ μ : ℝ)| ≤ ∑ _μ : Fin 4, (1 : ℝ) := Finset.sum_le_sum fun μ _ => hℓ.2 μ
              _ = 4 := by simp
          exact mul_le_mul (pow_le_pow_left₀ (VecTrig.l1_nonneg ℓ) hl i) (cn_coefOf_le hA ℓ)
            (VecTrig.cn_nonneg _ _) (by positivity)
      _ = (TrigInterp.lowBox (d := 4) n 1).card * ((4 : ℝ) ^ i * (2 * A)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 81 * ((4 : ℝ) ^ i * (2 * A)) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast card_lowBox_one_le n) (by positivity)
      _ = 162 * 4 ^ i * A := by ring
  have htail : ∑ ℓ ∈ (TrigInterp.box n 4).filter (fun ℓ => ¬ ∀ μ, |(ℓ μ : ℝ)| ≤ 1),
      VecTrig.l1 ℓ ^ i * VecTrig.cn (TrigInterp.coefOf n u) ℓ ≤ tau n 1 i u := by
    unfold TrigInterp.tau TrigInterp.tailBox
    refine Finset.sum_le_sum fun ℓ _ => ?_
    refine mul_le_mul_of_nonneg_right ?_ (VecTrig.cn_nonneg _ _)
    rw [div_one]
    exact pow_le_pow_left₀ (VecTrig.l1_nonneg ℓ) (by linarith) i
  linarith

end Derivs

/-! ### Multilinear maps on coordinate vectors -/

section Multilinear

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The operator norm of a multilinear map on `(ℝ⁴, sup norm)^j` is at most the sum of its values
on the coordinate vectors. -/
theorem norm_le_sum_evec {j : ℕ} (T : ContinuousMultilinearMap ℝ (fun _ : Fin j => R4) W) :
    ‖T‖ ≤ ∑ w : Fin j → Fin 4, ‖T (fun i => evec (w i))‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound
    (Finset.sum_nonneg fun w _ => norm_nonneg _) fun v => ?_
  have hv : v = fun i => ∑ μ, v i μ • evec μ := by
    funext i
    rw [show (∑ μ, v i μ • evec μ) = ∑ μ, Pi.single μ (v i μ) by
      refine Finset.sum_congr rfl fun μ _ => ?_
      rw [evec, ← Pi.single_smul', smul_eq_mul, mul_one]]
    exact (Finset.univ_sum_single (v i)).symm
  have hexp : T v = ∑ w : Fin j → Fin 4, (∏ i, v i (w i)) • T (fun i => evec (w i)) := by
    conv_lhs => rw [hv]
    rw [ContinuousMultilinearMap.map_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [ContinuousMultilinearMap.map_smul_univ]
  rw [hexp, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun w _ => ?_)
  rw [norm_smul, mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  rw [norm_prod]
  exact Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => norm_le_pi_norm (v i) (w i)

end Multilinear

/-! ### Consistency of iterated differences -/

section Consistency

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- **Second-order Taylor bound for an iterated derivative**: if `‖D^{r+2}F‖ ≤ B`, then
`‖D^rF(p+u) - D^rF(p) - D^{r+1}F(p)(u, ·)‖ ≤ B ‖u‖²`. -/
theorem norm_iteratedFDeriv_taylor_le {F : R4 → W} (hF : ContDiff ℝ ∞ F) {r : ℕ} {B : ℝ}
    (hB : ∀ z, ‖iteratedFDeriv ℝ (r + 2) F z‖ ≤ B) (p u : R4) :
    ‖iteratedFDeriv ℝ r F (p + u) - iteratedFDeriv ℝ r F p -
        fderiv ℝ (iteratedFDeriv ℝ r F) p u‖ ≤ B * ‖u‖ * ‖u‖ := by
  set Φ := iteratedFDeriv ℝ r F
  have hd : Differentiable ℝ Φ :=
    hF.differentiable_iteratedFDeriv (by exact_mod_cast WithTop.coe_lt_top _)
  have hd1 : Differentiable ℝ (iteratedFDeriv ℝ (r + 1) F) :=
    hF.differentiable_iteratedFDeriv (by exact_mod_cast WithTop.coe_lt_top _)
  -- the derivative of `Φ` is Lipschitz with constant `B`
  have hlip : ∀ z, ‖fderiv ℝ Φ z - fderiv ℝ Φ p‖ ≤ B * ‖z - p‖ := by
    intro z
    have e : ∀ y, ‖fderiv ℝ Φ y - fderiv ℝ Φ p‖ =
        ‖iteratedFDeriv ℝ (r + 1) F y - iteratedFDeriv ℝ (r + 1) F p‖ := by
      intro y
      rw [iteratedFDeriv_succ_eq_comp_left]
      simp only [Function.comp_apply]
      rw [← LinearIsometryEquiv.map_sub, LinearIsometryEquiv.norm_map]
    rw [e]
    exact Convex.norm_image_sub_le_of_norm_fderiv_le (s := Set.univ) (fun x _ => hd1 x)
      (fun x _ => by rw [norm_fderiv_iteratedFDeriv]; exact hB x) convex_univ
      (Set.mem_univ p) (Set.mem_univ z)
  have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le' (s := Metric.closedBall p ‖u‖)
    (f := Φ) (φ := fderiv ℝ Φ p) (C := B * ‖u‖) (fun x _ => hd x)
    (fun x hx => (hlip x).trans (mul_le_mul_of_nonneg_left (by
      rw [Metric.mem_closedBall, dist_eq_norm] at hx; exact hx) ((norm_nonneg _).trans
        (hB p)))) (convex_closedBall p ‖u‖) (Metric.mem_closedBall_self (norm_nonneg u))
    (by rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left])
  rw [add_sub_cancel_left] at hmv
  exact hmv

/-- **Consistency of iterated differences**: if `‖D^iF‖ ≤ B` for `i ≤ r + 1`, then for every
word `w` of length `r` and `h ≥ 0`,
`‖Δ_w F(p) - h^r D^rF(p)(e_{w_1}, …, e_{w_r})‖ ≤ r h^{r+1} B`. -/
theorem norm_cDiff_sub_le {h : ℝ} (hh : 0 ≤ h) :
    ∀ (r : ℕ) (w : Fin r → Fin 4) {F : R4 → W} {B : ℝ}, ContDiff ℝ ∞ F →
      (∀ i ≤ r + 1, ∀ z, ‖iteratedFDeriv ℝ i F z‖ ≤ B) → ∀ p,
      ‖cDiff h (List.ofFn w) F p - h ^ r • iteratedFDeriv ℝ r F p (fun i => evec (w i))‖ ≤
        r * h ^ (r + 1) * B
  | 0, w, F, B, _, _, p => by
    simp [cDiff, iteratedFDeriv_zero_apply]
  | r + 1, w, F, B, hF, hB, p => by
    rw [List.ofFn_succ]
    show ‖stepDiff h (w 0) (cDiff h (List.ofFn fun i => w i.succ) F) p - _‖ ≤ _
    rw [stepDiff_cDiff]
    set F' := stepDiff h (w 0) F
    have hF' : ContDiff ℝ ∞ F' := contDiff_stepDiff hF h (w 0)
    have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (Nat.zero_le _) p)
    have hB' : ∀ i ≤ r + 1, ∀ z, ‖iteratedFDeriv ℝ i F' z‖ ≤ h * B := by
      intro i hi z
      have := norm_iteratedFDeriv_stepDiff_le hF h (w 0) i (M := B)
        (fun z => hB (i + 1) (by omega) z) z
      rwa [abs_of_nonneg hh] at this
    have ih := norm_cDiff_sub_le hh r (fun i => w i.succ) hF' hB' p
    set m : Fin r → R4 := fun i => evec (w i.succ)
    set u : R4 := Pi.single (w 0) h
    have hu : u = h • evec (w 0) := by
      rw [evec, ← Pi.single_smul', smul_eq_mul, mul_one]
    have hun : ‖u‖ = h := by rw [Pi.norm_single, Real.norm_of_nonneg hh]
    -- `D^rF'(p)(m) = D^rF(p + u)(m) - D^rF(p)(m)`
    have ha : iteratedFDeriv ℝ r F' p m =
        iteratedFDeriv ℝ r F (p + u) m - iteratedFDeriv ℝ r F p m := by
      rw [iteratedFDeriv_stepDiff hF]; rfl
    -- Taylor
    have ht := norm_iteratedFDeriv_taylor_le hF (r := r) (B := B)
      (fun z => hB (r + 2) le_rfl z) p u
    have hm1 : ∏ i : Fin r, ‖m i‖ = 1 := by
      simp [m, DiscreteEulerConsistency.norm_evec]
    have hta : ‖iteratedFDeriv ℝ r F (p + u) m - iteratedFDeriv ℝ r F p m -
        h • iteratedFDeriv ℝ (r + 1) F p (fun i => evec (w i))‖ ≤ B * h * h := by
      have e : h • iteratedFDeriv ℝ (r + 1) F p (fun i => evec (w i)) =
          (fderiv ℝ (iteratedFDeriv ℝ r F) p u) m := by
        rw [iteratedFDeriv_succ_apply_left, hu, map_smul, ContinuousMultilinearMap.smul_apply]
        rfl
      rw [e, ← ContinuousMultilinearMap.sub_apply, ← ContinuousMultilinearMap.sub_apply]
      refine ((ContinuousMultilinearMap.le_opNorm _ m).trans ?_)
      rw [hm1, mul_one, ← hun]
      exact ht
    calc ‖cDiff h (List.ofFn fun i => w i.succ) F' p -
          h ^ (r + 1) • iteratedFDeriv ℝ (r + 1) F p (fun i => evec (w i))‖
        = ‖(cDiff h (List.ofFn fun i => w i.succ) F' p - h ^ r • iteratedFDeriv ℝ r F' p m) +
            h ^ r • (iteratedFDeriv ℝ r F (p + u) m - iteratedFDeriv ℝ r F p m -
              h • iteratedFDeriv ℝ (r + 1) F p (fun i => evec (w i)))‖ := by
          rw [ha]
          congr 1
          module
      _ ≤ ‖cDiff h (List.ofFn fun i => w i.succ) F' p - h ^ r • iteratedFDeriv ℝ r F' p m‖ +
            h ^ r * (B * h * h) := by
          refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
          rw [norm_smul, Real.norm_of_nonneg (pow_nonneg hh r)]
          exact mul_le_mul_of_nonneg_left hta (pow_nonneg hh r)
      _ ≤ r * h ^ (r + 1) * (h * B) + h ^ r * (B * h * h) := add_le_add ih le_rfl
      _ = ((r + 1 : ℕ) : ℝ) * h ^ (r + 1 + 1) * B := by push_cast; ring

end Consistency

/-! ### Convergence of trigonometric interpolation of samples -/

section Convergence

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

theorem pos_add_single' {n : ℕ} [NeZero n] {h : ℝ} {F : R4 → W}
    (hF : IsPeriodic ((n : ℝ) * h) F) (x : Grid n) (j : Fin 4) :
    F (pos h (x + Pi.single j 1)) = F (pos h x + Pi.single j h) := by
  have e1 : (Pi.single j 1 : Grid n) = castVec (Pi.single j 1) := by
    rw [DiscreteEulerConsistency.castVec_single]; rfl
  have e2 : h • realVec (Pi.single j 1) = Pi.single j h := by
    rw [DiscreteEulerConsistency.realVec_single, evec, ← Pi.single_smul', smul_eq_mul, mul_one]
  have := DiscreteEulerConsistency.samp_add_castVec hF x (Pi.single j 1)
  rw [← e1, e2] at this
  exact this

/-- Iterated differences of a periodic field vanishing at all nodes vanish at the nodes. -/
theorem cDiff_eq_zero_of_nodes {n : ℕ} [NeZero n] {h : ℝ} {G : R4 → W}
    (hG : IsPeriodic ((n : ℝ) * h) G) (h0 : ∀ x : Grid n, G (pos h x) = 0) :
    ∀ (w : List (Fin 4)) (x : Grid n), cDiff h w G (pos h x) = 0
  | [], x => h0 x
  | j :: w, x => by
    show cDiff h w G (pos h x + Pi.single j h) - cDiff h w G (pos h x) = 0
    rw [← pos_add_single' (isPeriodic_cDiff hG h w) x j, cDiff_eq_zero_of_nodes hG h0 w,
      cDiff_eq_zero_of_nodes hG h0 w, sub_zero]

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- **Convergence of trigonometric interpolation in every `C^j`.**  For every order `j` there is
`C` such that for every odd `n` (`h = 2π/n`) and every smooth field `Y` of period `2π` with
`‖D^rY‖ ≤ M` for `r ≤ j + 5`,
`‖D^j(𝓘_h(𝖲_h Y) - Y)(z)‖ ≤ C M h` at every point.  (The interpolant reproduces the samples, all
its differences vanish at the nodes, and differences are consistent with derivatives up to
`O(h)`, given uniform bounds on the derivatives of the interpolant from the sharp tail.) -/
theorem norm_iteratedFDeriv_recon_sub_le (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) [NeZero n], Odd n → ∀ (Y : R4 → V) (M : ℝ), ContDiff ℝ ∞ Y →
      IsPeriodic (2 * π) Y → (∀ r ≤ j + 5, ∀ z, ‖iteratedFDeriv ℝ r Y z‖ ≤ M) → ∀ z,
      ‖iteratedFDeriv ℝ j (fun z => recon n (samp (n := n) (2 * π / n) Y) z - Y z) z‖ ≤
        C * M * (2 * π / n) := by
  have hT : ∀ i : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) [NeZero n] (Y : R4 → V) (M : ℝ),
      ContDiff ℝ ∞ Y → IsPeriodic (2 * π) Y → (∀ r ≤ i + 3, ∀ z, ‖iteratedFDeriv ℝ r Y z‖ ≤ M) →
      ∀ K : ℝ, 1 ≤ K → tau n K i (samp (n := n) (2 * π / n) Y) ≤ C * M * K ^ (2 - ((i + 3 : ℕ) : ℝ)) :=
    fun i => SampledTail.tau_samp_le (V := V) i (i + 3) (by push_cast; linarith)
  choose Ci hCi0 hCi using hT
  set Bc : ℝ := ∑ i ∈ Finset.range (j + 3), (162 * 4 ^ i + Ci i + 1) with hBc
  have hBc0 : 0 ≤ Bc := Finset.sum_nonneg fun i _ => by have := hCi0 i; positivity
  refine ⟨(4 ^ j * j + 1) * Bc, by positivity, ?_⟩
  intro n _ hn Y M hY hper hM z
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (Nat.zero_le _) z)
  set h : ℝ := 2 * π / n with hh
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hnpos : (0 : ℝ) < n := by positivity
  have hh0 : 0 < h := by rw [hh]; positivity
  have hper' : IsPeriodic ((n : ℝ) * h) Y := by rw [hh, mul_div_cancel₀ _ hn0]; exact hper
  set u : Grid n → V := samp (n := n) h Y with hu
  set G : R4 → V := fun z => recon n u z - Y z with hG
  have hR : ContDiff ℝ ∞ (recon n u) := VecTrig.contDiff_tp _ _
  have hGs : ContDiff ℝ ∞ G := hR.sub hY
  have hGp : IsPeriodic ((n : ℝ) * h) G := by
    intro w μ
    simp only [hG]
    rw [show (n : ℝ) * h = 2 * π by rw [hh, mul_div_cancel₀ _ hn0], hper w μ,
      TrigInterp.recon_periodic n u w μ]
  have huA : ∀ y, ‖u y‖ ≤ M := fun y => by
    have := hM 0 (Nat.zero_le _) (pos h y); rwa [norm_iteratedFDeriv_zero] at this
  -- uniform derivative bounds for `G`
  have hGB : ∀ i ≤ j + 2, ∀ z, ‖iteratedFDeriv ℝ i G z‖ ≤ Bc * M := by
    intro i hi z
    have hsub : iteratedFDeriv ℝ i G z =
        iteratedFDeriv ℝ i (recon n u) z - iteratedFDeriv ℝ i Y z :=
      iteratedFDeriv_sub_apply (hR.of_le (by exact_mod_cast le_top)).contDiffAt
        (hY.of_le (by exact_mod_cast le_top)).contDiffAt
    have h1 := norm_iteratedFDeriv_recon_le' huA i z
    have h2 := hCi i n Y M hY hper (fun r hr z => hM r (by omega) z) 1 le_rfl
    rw [Real.one_rpow, mul_one] at h2
    have h3 := hM i (by omega) z
    have hterm : (162 * 4 ^ i + Ci i + 1) * M ≤ Bc * M := by
      refine mul_le_mul_of_nonneg_right ?_ hM0
      rw [hBc]
      exact Finset.single_le_sum (f := fun i => (162 * 4 ^ i + Ci i + 1 : ℝ))
        (fun i _ => by have := hCi0 i; positivity) (Finset.mem_range.mpr (by omega))
    rw [hsub]
    calc ‖iteratedFDeriv ℝ i (recon n u) z - iteratedFDeriv ℝ i Y z‖
        ≤ ‖iteratedFDeriv ℝ i (recon n u) z‖ + ‖iteratedFDeriv ℝ i Y z‖ := norm_sub_le _ _
      _ ≤ (162 * 4 ^ i * M + Ci i * M) + M := add_le_add (h1.trans (by linarith)) h3
      _ = (162 * 4 ^ i + Ci i + 1) * M := by ring
      _ ≤ Bc * M := hterm
  -- `G` vanishes at the nodes
  have hnode : ∀ x : Grid n, G (pos h x) = 0 := by
    intro x
    simp only [hG]
    have : pos h x = TrigInterp.gpos n x := rfl
    rw [this, TrigInterp.recon_gpos n hn u x, sub_eq_zero]
    rfl
  -- the bound at the nodes
  have hatnode : ∀ x : Grid n, ‖iteratedFDeriv ℝ j G (pos h x)‖ ≤ 4 ^ j * j * h * (Bc * M) := by
    intro x
    refine (norm_le_sum_evec _).trans ?_
    have hw : ∀ w : Fin j → Fin 4,
        ‖iteratedFDeriv ℝ j G (pos h x) (fun i => evec (w i))‖ ≤ j * h * (Bc * M) := by
      intro w
      have hc := norm_cDiff_sub_le hh0.le j w hGs (fun i hi z => hGB i (by omega) z) (pos h x)
      rw [cDiff_eq_zero_of_nodes hGp hnode, zero_sub, norm_neg, norm_smul,
        Real.norm_of_nonneg (pow_nonneg hh0.le j)] at hc
      have hpow : 0 < h ^ j := pow_pos hh0 j
      have : h ^ j * ‖iteratedFDeriv ℝ j G (pos h x) (fun i => evec (w i))‖ ≤
          h ^ j * (j * h * (Bc * M)) := by
        calc _ ≤ j * h ^ (j + 1) * (Bc * M) := hc
          _ = h ^ j * (j * h * (Bc * M)) := by ring
      exact le_of_mul_le_mul_left this hpow
    calc ∑ w : Fin j → Fin 4, ‖iteratedFDeriv ℝ j G (pos h x) (fun i => evec (w i))‖
        ≤ ∑ _w : Fin j → Fin 4, j * h * (Bc * M) := Finset.sum_le_sum fun w _ => hw w
      _ = 4 ^ j * j * h * (Bc * M) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        simp only [Fintype.card_fun, Fintype.card_fin]
        push_cast; ring
  -- from the nearest node
  obtain ⟨x, k, hx⟩ := exists_node_near (n := n) z
  set z' : R4 := z - (2 * π) • realVec k with hz'
  have hper2 : IsPeriodic (2 * π) (iteratedFDeriv ℝ j G) := by
    have := isPeriodic_iteratedFDeriv hGp j
    rwa [show (n : ℝ) * h = 2 * π by rw [hh, mul_div_cancel₀ _ hn0]] at this
  have hzz : iteratedFDeriv ℝ j G z = iteratedFDeriv ℝ j G z' := by
    have := DiscreteEulerConsistency.IsPeriodic.add_intVec hper2 k z'
    rw [show z' + (2 * π) • realVec k = z by simp [z']] at this
    exact this
  have hd : Differentiable ℝ (iteratedFDeriv ℝ j G) :=
    hGs.differentiable_iteratedFDeriv (by exact_mod_cast WithTop.coe_lt_top _)
  have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le (s := Set.univ) (fun w _ => hd w)
    (fun w _ => by rw [norm_fderiv_iteratedFDeriv]; exact hGB (j + 1) (by omega) w) convex_univ
    (Set.mem_univ (pos h x)) (Set.mem_univ z')
  have hdist : ‖z' - pos h x‖ ≤ h := hx
  rw [hzz]
  have hBM : 0 ≤ Bc * M := by positivity
  calc ‖iteratedFDeriv ℝ j G z'‖
      ≤ ‖iteratedFDeriv ℝ j G (pos h x)‖ +
          ‖iteratedFDeriv ℝ j G z' - iteratedFDeriv ℝ j G (pos h x)‖ := by
        have := norm_add_le (iteratedFDeriv ℝ j G (pos h x))
          (iteratedFDeriv ℝ j G z' - iteratedFDeriv ℝ j G (pos h x))
        rwa [add_sub_cancel] at this
    _ ≤ 4 ^ j * j * h * (Bc * M) + Bc * M * h :=
        add_le_add (hatnode x) (hmv.trans (mul_le_mul_of_nonneg_left hdist hBM))
    _ = (4 ^ j * j + 1) * Bc * M * h := by ring

end Convergence

end RenewalGeometry.TrigConv
