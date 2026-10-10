/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Uniform `C^N` convergence of families of smooth maps and its calculus

Generic infrastructure for `cor:local-calibration-nonempty` of the Einstein–Standard-Model
action-closure manuscript ("derivative convergence controls the initial and harmonic
mismatches"): uniform convergence of all derivatives up to order `N` is preserved by the
pointwise operations out of which the actual-jet state and the harmonic defect of a field tuple
are built.

`CN N l F F₀` (for a family `F : ι → E → G` along a filter `l`): eventually every `F i` is smooth,
`F₀` is smooth with uniformly bounded derivatives of order `≤ N`, and
`sup_x ‖D^j(F i - F₀)(x)‖ → 0` for every `j ≤ N`.

## Main results

* `CN.add`, `CN.sub`, `CN.sum`, `CN.clm` (post-composition with a continuous linear map),
  **`CN.bilin`** (continuous bilinear maps; Leibniz bound
  `ContinuousLinearMap.norm_iteratedFDeriv_le_of_bilinear`), `CN.prod`, `CN.pi`.
* **`CN.fderiv`** / **`CN.of_fderiv`** — the derivative shifts the order by one; `CN.pd`.
* `CN.affine` — reparametrisation by `x ↦ c • x + a`.
* **`CN.comp`** — the `C^N`-continuity of composition: if `Ψ` is smooth on an open set `U`, the
  limit `F₀` takes values in a compact `K ⊆ U` and `F i → F₀` in `C^N`, then
  `Ψ ∘ F i → Ψ ∘ F₀` in `C^N` (induction on `N` through `D(Ψ ∘ F) = (DΨ ∘ F) · DF`; the base case
  is the mean value inequality on balls inside a compact thickening of `K`).
-/

open Filter Topology Set Metric
open scoped ContDiff

noncomputable section

namespace RenewalGeometry.CNConv

theorem nat_le_inf (j : ℕ) : (j : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.2 le_top

section Defs

variable {ι : Type*}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- **Uniform `C^N` convergence** of a family `F i` to `F₀` along `l`, with `F₀` uniformly
`C^N`-bounded. -/
structure CN (N : ℕ) (l : Filter ι) (F : ι → E → G) (F₀ : E → G) : Prop where
  smooth : ∀ᶠ i in l, ContDiff ℝ ∞ (F i)
  smooth₀ : ContDiff ℝ ∞ F₀
  bdd : ∃ C, ∀ j ≤ N, ∀ x, ‖iteratedFDeriv ℝ j F₀ x‖ ≤ C
  conv : ∀ ε > 0, ∀ᶠ i in l, ∀ j ≤ N, ∀ x,
    ‖iteratedFDeriv ℝ j (fun y => F i y - F₀ y) x‖ ≤ ε

end Defs

variable {ι : Type*} {l : Filter ι} {N : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
variable {G' : Type*} [NormedAddCommGroup G'] [NormedSpace ℝ G']
variable {G'' : Type*} [NormedAddCommGroup G''] [NormedSpace ℝ G'']

namespace CN

theorem bdd_nonneg {F₀ : E → G} {C : ℝ} (h : ∀ j ≤ N, ∀ x, ‖iteratedFDeriv ℝ j F₀ x‖ ≤ C)
    [Nonempty E] : 0 ≤ C :=
  (norm_nonneg _).trans (h 0 (Nat.zero_le _) (Classical.arbitrary E))

theorem mono {F : ι → E → G} {F₀ : E → G} (h : CN N l F F₀) {M : ℕ} (hM : M ≤ N) :
    CN M l F F₀ := by
  obtain ⟨C, hC⟩ := h.bdd
  refine ⟨h.smooth, h.smooth₀, ⟨C, fun j hj => hC j (hj.trans hM)⟩, fun ε hε => ?_⟩
  filter_upwards [h.conv ε hε] with i hi j hj x using hi j (hj.trans hM) x

theorem congr {F F' : ι → E → G} {F₀ F₀' : E → G} (h : CN N l F F₀)
    (hF : ∀ᶠ i in l, F' i = F i) (h0 : F₀' = F₀) : CN N l F' F₀' := by
  subst h0
  refine ⟨?_, h.smooth₀, h.bdd, fun ε hε => ?_⟩
  · filter_upwards [h.smooth, hF] with i hi he
    rw [he]; exact hi
  · filter_upwards [h.conv ε hε, hF] with i hi he
    rw [he]; exact hi

/-- A constant family converges to itself. -/
theorem const_family {F₀ : E → G} (h0 : ContDiff ℝ ∞ F₀)
    (hb : ∃ C, ∀ j ≤ N, ∀ x, ‖iteratedFDeriv ℝ j F₀ x‖ ≤ C) :
    CN N l (fun _ => F₀) F₀ := by
  refine ⟨Eventually.of_forall fun _ => h0, h0, hb, fun ε hε => Eventually.of_forall
    fun i j _ x => ?_⟩
  have e : (fun y => F₀ y - F₀ y) = fun _ => (0 : G) := funext fun y => sub_self _
  rw [e, iteratedFDeriv_zero_fun]
  simpa using hε.le

theorem contDiffAt_sub {f g : E → G} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (j : ℕ) (x : E) :
    ContDiffAt ℝ j (fun y => f y - g y) x :=
  ((hf.sub hg).of_le (nat_le_inf j)).contDiffAt

/-- Sums. -/
theorem add {F Fg : ι → E → G} {F₀ G₀ : E → G} (hF : CN N l F F₀) (hG : CN N l Fg G₀) :
    CN N l (fun i x => F i x + Fg i x) (fun x => F₀ x + G₀ x) := by
  obtain ⟨C₁, hC₁⟩ := hF.bdd
  obtain ⟨C₂, hC₂⟩ := hG.bdd
  refine ⟨?_, hF.smooth₀.add hG.smooth₀, ⟨C₁ + C₂, fun j hj x => ?_⟩, fun ε hε => ?_⟩
  · filter_upwards [hF.smooth, hG.smooth] with i h1 h2 using h1.add h2
  · have e := iteratedFDeriv_add_apply (i := j) (x := x)
      ((hF.smooth₀.of_le (nat_le_inf j)).contDiffAt) ((hG.smooth₀.of_le (nat_le_inf j)).contDiffAt)
    rw [show (fun x => F₀ x + G₀ x) = F₀ + G₀ from rfl, e]
    exact (norm_add_le _ _).trans (add_le_add (hC₁ j hj x) (hC₂ j hj x))
  · filter_upwards [hF.smooth, hG.smooth, hF.conv (ε / 2) (by positivity),
      hG.conv (ε / 2) (by positivity)] with i s1 s2 h1 h2 j hj x
    have e0 : (fun y => F i y + Fg i y - (F₀ y + G₀ y)) =
        (fun y => F i y - F₀ y) + (fun y => Fg i y - G₀ y) := by
      funext y; simp only [Pi.add_apply]; abel
    rw [e0, iteratedFDeriv_add_apply (contDiffAt_sub s1 hF.smooth₀ j x)
      (contDiffAt_sub s2 hG.smooth₀ j x)]
    calc _ ≤ ε / 2 + ε / 2 := (norm_add_le _ _).trans (add_le_add (h1 j hj x) (h2 j hj x))
      _ = ε := by ring

/-- The zero family. -/
theorem zero : CN N l (fun _ _ => (0 : G)) (fun _ : E => (0 : G)) := by
  refine ⟨Eventually.of_forall fun _ => contDiff_const, contDiff_const, ⟨0, fun j _ x => ?_⟩,
    fun ε hε => Eventually.of_forall fun i j _ x => ?_⟩
  · rw [iteratedFDeriv_zero_fun]; simp
  · have e : (fun _ : E => (0 : G) - 0) = fun _ => (0 : G) := funext fun _ => sub_self _
    rw [e, iteratedFDeriv_zero_fun]; simpa using hε.le

/-- Finite sums. -/
theorem sum {κ : Type*} (s : Finset κ) {F : κ → ι → E → G} {F₀ : κ → E → G}
    (h : ∀ k ∈ s, CN N l (F k) (F₀ k)) :
    CN N l (fun i x => ∑ k ∈ s, F k i x) (fun x => ∑ k ∈ s, F₀ k x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero (N := N) (l := l) (E := E) (G := G))
  | insert a s has ih =>
    simp only [Finset.sum_insert has]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

/-- Post-composition with a continuous linear map. -/
theorem clm {F : ι → E → G} {F₀ : E → G} (h : CN N l F F₀) (L : G →L[ℝ] G') :
    CN N l (fun i x => L (F i x)) (fun x => L (F₀ x)) := by
  obtain ⟨C, hC⟩ := h.bdd
  refine ⟨?_, L.contDiff.comp h.smooth₀, ⟨‖L‖ * C, fun j hj x => ?_⟩, fun ε hε => ?_⟩
  · filter_upwards [h.smooth] with i hi using L.contDiff.comp hi
  · exact (L.norm_iteratedFDeriv_comp_left (f := F₀) h.smooth₀.contDiffAt (nat_le_inf j)).trans
      (mul_le_mul_of_nonneg_left (hC j hj x) (norm_nonneg _))
  · have hε' : 0 < ε / (‖L‖ + 1) := by positivity
    filter_upwards [h.smooth, h.conv _ hε'] with i si hi j hj x
    have e0 : (fun y => L (F i y) - L (F₀ y)) = L ∘ (fun y => F i y - F₀ y) := by
      funext y; simp
    rw [e0]
    refine (L.norm_iteratedFDeriv_comp_left (si.sub h.smooth₀).contDiffAt (nat_le_inf j)).trans ?_
    calc ‖L‖ * ‖iteratedFDeriv ℝ j (fun y => F i y - F₀ y) x‖ ≤ (‖L‖ + 1) * (ε / (‖L‖ + 1)) :=
          mul_le_mul (by linarith) (hi j hj x) (norm_nonneg _) (by positivity)
      _ = ε := by field_simp

/-- Differences. -/
theorem sub {F Fg : ι → E → G} {F₀ G₀ : E → G} (hF : CN N l F F₀) (hG : CN N l Fg G₀) :
    CN N l (fun i x => F i x - Fg i x) (fun x => F₀ x - G₀ x) := by
  have := hF.add (hG.clm (-ContinuousLinearMap.id ℝ G))
  simpa [sub_eq_add_neg] using this


/-- The Leibniz bound with uniform bounds on the factors. -/
theorem norm_iteratedFDeriv_bilin_le (B : G →L[ℝ] G' →L[ℝ] G'') {f : E → G} {g : E → G'}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) {j : ℕ} {x : E} {a b : ℝ}
    (ha : ∀ i ≤ j, ‖iteratedFDeriv ℝ i f x‖ ≤ a) (hb : ∀ i ≤ j, ‖iteratedFDeriv ℝ i g x‖ ≤ b) :
    ‖iteratedFDeriv ℝ j (fun y => B (f y) (g y)) x‖ ≤ ‖B‖ * 2 ^ j * (a * b) := by
  have ha0 : 0 ≤ a := (norm_nonneg _).trans (ha 0 (Nat.zero_le _))
  have hb0 : 0 ≤ b := (norm_nonneg _).trans (hb 0 (Nat.zero_le _))
  refine (B.norm_iteratedFDeriv_le_of_bilinear hf hg x (nat_le_inf j)).trans ?_
  rw [mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  calc ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i f x‖ *
        ‖iteratedFDeriv ℝ (j - i) g x‖
      ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * a * b := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' : i ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
        exact mul_le_mul (mul_le_mul_of_nonneg_left (ha i hi') (by positivity))
          (hb (j - i) (Nat.sub_le _ _)) (norm_nonneg _) (by positivity)
    _ = 2 ^ j * (a * b) := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        have : (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ)) = 2 ^ j := by
          exact_mod_cast Nat.sum_range_choose j
        rw [this]; ring

/-- **Continuous bilinear maps.** -/
theorem bilin {F : ι → E → G} {F₀ : E → G} {Fg : ι → E → G'} {G₀ : E → G'}
    (hF : CN N l F F₀) (hG : CN N l Fg G₀) (B : G →L[ℝ] G' →L[ℝ] G'') :
    CN N l (fun i x => B (F i x) (Fg i x)) (fun x => B (F₀ x) (G₀ x)) := by
  obtain ⟨C₁, hC₁⟩ := hF.bdd
  obtain ⟨C₂, hC₂⟩ := hG.bdd
  have hsm : ∀ {f : E → G} {g : E → G'}, ContDiff ℝ ∞ f → ContDiff ℝ ∞ g →
      ContDiff ℝ ∞ (fun y => B (f y) (g y)) := fun hf hg => (B.contDiff.comp hf).clm_apply hg
  have hC₁0 : 0 ≤ C₁ := (norm_nonneg _).trans (hC₁ 0 (Nat.zero_le _) 0)
  have hC₂0 : 0 ≤ C₂ := (norm_nonneg _).trans (hC₂ 0 (Nat.zero_le _) 0)
  refine ⟨?_, hsm hF.smooth₀ hG.smooth₀, ⟨‖B‖ * 2 ^ N * (C₁ * C₂), fun j hj x => ?_⟩,
    fun ε hε => ?_⟩
  · filter_upwards [hF.smooth, hG.smooth] with i h1 h2 using hsm h1 h2
  · refine (norm_iteratedFDeriv_bilin_le B hF.smooth₀ hG.smooth₀
      (fun i hi => hC₁ i (hi.trans hj) x) (fun i hi => hC₂ i (hi.trans hj) x)).trans ?_
    have h2j : (2 : ℝ) ^ j ≤ 2 ^ N := pow_le_pow_right₀ one_le_two hj
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2j (norm_nonneg _))
      (by positivity)
  · set K : ℝ := ‖B‖ * 2 ^ N * (1 + C₁ + C₂) + 1 with hK
    have hK0 : 0 < K := by positivity
    set ε' : ℝ := min 1 (ε / K) with hε'
    have hε'0 : 0 < ε' := lt_min one_pos (by positivity)
    have hε'1 : ε' ≤ 1 := min_le_left _ _
    have hε'2 : ε' ≤ ε / K := min_le_right _ _
    filter_upwards [hF.smooth, hG.smooth, hF.conv ε' hε'0, hG.conv ε' hε'0]
      with i s1 s2 h1 h2 j hj x
    have d1 := s1.sub hF.smooth₀
    have d2 := s2.sub hG.smooth₀
    have e0 : (fun y => B (F i y) (Fg i y) - B (F₀ y) (G₀ y)) =
        ((fun y => B (F i y - F₀ y) (Fg i y - G₀ y)) + (fun y => B (F i y - F₀ y) (G₀ y))) +
          (fun y => B (F₀ y) (Fg i y - G₀ y)) := by
      funext y
      simp only [Pi.add_apply, map_sub, ContinuousLinearMap.sub_apply]
      abel
    have c1 := ((hsm d1 d2).of_le (nat_le_inf j)).contDiffAt (x := x)
    have c2 := ((hsm d1 hG.smooth₀).of_le (nat_le_inf j)).contDiffAt (x := x)
    have c3 := ((hsm hF.smooth₀ d2).of_le (nat_le_inf j)).contDiffAt (x := x)
    have c12 : ContDiffAt ℝ j ((fun y => B (F i y - F₀ y) (Fg i y - G₀ y)) +
        (fun y => B (F i y - F₀ y) (G₀ y))) x := c1.add c2
    rw [e0, iteratedFDeriv_add_apply c12 c3, iteratedFDeriv_add_apply c1 c2]
    have t1 := norm_iteratedFDeriv_bilin_le B d1 d2 (j := j) (x := x)
      (fun i hi => h1 i (hi.trans hj) x) (fun i hi => h2 i (hi.trans hj) x)
    have t2 := norm_iteratedFDeriv_bilin_le B d1 hG.smooth₀ (j := j) (x := x)
      (fun i hi => h1 i (hi.trans hj) x) (fun i hi => hC₂ i (hi.trans hj) x)
    have t3 := norm_iteratedFDeriv_bilin_le B hF.smooth₀ d2 (j := j) (x := x)
      (fun i hi => hC₁ i (hi.trans hj) x) (fun i hi => h2 i (hi.trans hj) x)
    have h2j : (2 : ℝ) ^ j ≤ 2 ^ N := pow_le_pow_right₀ one_le_two hj
    calc _ ≤ ‖B‖ * 2 ^ j * (ε' * ε') + ‖B‖ * 2 ^ j * (ε' * C₂) +
          ‖B‖ * 2 ^ j * (C₁ * ε') :=
          (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add t1 t2)) t3)
      _ = ‖B‖ * 2 ^ j * (ε' + C₂ + C₁) * ε' := by ring
      _ ≤ ‖B‖ * 2 ^ N * (1 + C₁ + C₂) * ε' := by
          refine mul_le_mul_of_nonneg_right ?_ hε'0.le
          exact mul_le_mul (mul_le_mul_of_nonneg_left h2j (norm_nonneg _)) (by linarith)
            (by positivity) (by positivity)
      _ ≤ K * (ε / K) := mul_le_mul (by linarith) hε'2 hε'0.le hK0.le
      _ = ε := by field_simp

/-- **The derivative shifts the order by one.** -/
theorem fderiv {F : ι → E → G} {F₀ : E → G} (h : CN (N + 1) l F F₀) :
    CN N l (fun i => _root_.fderiv ℝ (F i)) (_root_.fderiv ℝ F₀) := by
  obtain ⟨C, hC⟩ := h.bdd
  have hsm : ∀ {f : E → G}, ContDiff ℝ ∞ f → ContDiff ℝ ∞ (_root_.fderiv ℝ f) :=
    fun hf => hf.fderiv_right (m := ∞) (by simp)
  refine ⟨?_, hsm h.smooth₀, ⟨C, fun j hj x => ?_⟩, fun ε hε => ?_⟩
  · filter_upwards [h.smooth] with i hi using hsm hi
  · rw [norm_iteratedFDeriv_fderiv]; exact hC (j + 1) (by omega) x
  · filter_upwards [h.smooth, h.conv ε hε] with i si hi j hj x
    have e0 : (fun y => _root_.fderiv ℝ (F i) y - _root_.fderiv ℝ F₀ y) =
        _root_.fderiv ℝ (fun y => F i y - F₀ y) := by
      funext y
      rw [fderiv_fun_sub (si.differentiable (by simp) y) (h.smooth₀.differentiable (by simp) y)]
    rw [e0, norm_iteratedFDeriv_fderiv]
    exact hi (j + 1) (by omega) x

/-- **Converse**: `C⁰` convergence and `C^N` convergence of the derivatives give `C^{N+1}`. -/
theorem of_fderiv {F : ι → E → G} {F₀ : E → G} (h0 : CN 0 l F F₀)
    (hd : CN N l (fun i => _root_.fderiv ℝ (F i)) (_root_.fderiv ℝ F₀)) :
    CN (N + 1) l F F₀ := by
  obtain ⟨C₀, hC₀⟩ := h0.bdd
  obtain ⟨C, hC⟩ := hd.bdd
  refine ⟨h0.smooth, h0.smooth₀, ⟨max C₀ C, fun j hj x => ?_⟩, fun ε hε => ?_⟩
  · rcases j with _ | j
    · exact (hC₀ 0 le_rfl x).trans (le_max_left _ _)
    · rw [← norm_iteratedFDeriv_fderiv]
      exact (hC j (by omega) x).trans (le_max_right _ _)
  · filter_upwards [h0.smooth, h0.conv ε hε, hd.conv ε hε] with i si h1 h2 j hj x
    rcases j with _ | j
    · exact h1 0 le_rfl x
    · have e0 : (fun y => _root_.fderiv ℝ (F i) y - _root_.fderiv ℝ F₀ y) =
          _root_.fderiv ℝ (fun y => F i y - F₀ y) := by
        funext y
        rw [fderiv_fun_sub (si.differentiable (by simp) y) (h0.smooth₀.differentiable (by simp) y)]
      have := h2 j (by omega) x
      rw [e0, norm_iteratedFDeriv_fderiv] at this
      exact this

/-- Directional derivatives along a fixed vector. -/
theorem fderiv_apply {F : ι → E → G} {F₀ : E → G} (h : CN (N + 1) l F F₀) (v : E) :
    CN N l (fun i x => _root_.fderiv ℝ (F i) x v) (fun x => _root_.fderiv ℝ F₀ x v) :=
  h.fderiv.clm (ContinuousLinearMap.apply ℝ G v)

/-- Pairs. -/
theorem prod {F : ι → E → G} {F₀ : E → G} {Fg : ι → E → G'} {G₀ : E → G'}
    (hF : CN N l F F₀) (hG : CN N l Fg G₀) :
    CN N l (fun i x => (F i x, Fg i x)) (fun x => (F₀ x, G₀ x)) := by
  have := (hF.clm (ContinuousLinearMap.inl ℝ G G')).add (hG.clm (ContinuousLinearMap.inr ℝ G G'))
  simpa using this

/-- Finite products of components. -/
theorem pi {κ : Type*} [Fintype κ] [DecidableEq κ] {F : ι → E → κ → G} {F₀ : E → κ → G}
    (h : ∀ k, CN N l (fun i x => F i x k) (fun x => F₀ x k)) : CN N l F F₀ := by
  have := sum Finset.univ fun k _ =>
    (h k).clm (ContinuousLinearMap.single ℝ (fun _ : κ => G) k)
  refine this.congr (Eventually.of_forall fun i => ?_) ?_ <;>
  · funext x
    ext k
    simp [Finset.sum_apply, Pi.single_apply]

/-- Components of a product. -/
theorem apply {κ : Type*} [Fintype κ] {F : ι → E → κ → G} {F₀ : E → κ → G}
    (h : CN N l F F₀) (k : κ) : CN N l (fun i x => F i x k) (fun x => F₀ x k) :=
  h.clm (ContinuousLinearMap.proj k)


/-- Derivatives of an affine reparametrisation. -/
theorem norm_iteratedFDeriv_affine_le {f : E → G} (hf : ContDiff ℝ ∞ f) (c : ℝ) (a : E) (j : ℕ)
    (x : E) : ‖iteratedFDeriv ℝ j (fun y => f (c • y + a)) x‖ ≤
      |c| ^ j * ‖iteratedFDeriv ℝ j f (c • x + a)‖ := by
  set g : E → G := fun z => f (z + a) with hg
  have hgs : ContDiff ℝ ∞ g := hf.comp (contDiff_id.add contDiff_const)
  have h := ContinuousLinearMap.iteratedFDeriv_comp_right (c • ContinuousLinearMap.id ℝ E) hgs x
    (i := j) (nat_le_inf j)
  rw [show (fun y => f (c • y + a)) = g ∘ ⇑(c • ContinuousLinearMap.id ℝ E) from rfl, h]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hn : ‖c • ContinuousLinearMap.id ℝ E‖ ≤ |c| := by
    refine (ContinuousLinearMap.opNorm_smul_le c (ContinuousLinearMap.id ℝ E)).trans ?_
    rw [Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg c) ContinuousLinearMap.norm_id_le
  have hprod : ∏ _i : Fin j, ‖c • ContinuousLinearMap.id ℝ E‖ ≤ |c| ^ j := by
    calc ∏ _i : Fin j, ‖c • ContinuousLinearMap.id ℝ E‖ ≤ ∏ _i : Fin j, |c| :=
          Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun _ _ => hn)
      _ = |c| ^ j := by simp
  have hx : (c • ContinuousLinearMap.id ℝ E) x = c • x := rfl
  rw [hx, hg, iteratedFDeriv_comp_add_right, mul_comm]
  exact mul_le_mul_of_nonneg_right hprod (norm_nonneg _)

/-- **Affine reparametrisation** `x ↦ c • x + a`. -/
theorem affine {F : ι → E → G} {F₀ : E → G} (h : CN N l F F₀) (c : ℝ) (a : E) :
    CN N l (fun i y => F i (c • y + a)) (fun y => F₀ (c • y + a)) := by
  obtain ⟨C, hC⟩ := h.bdd
  have haff : ContDiff ℝ ∞ (fun y : E => c • y + a) := (contDiff_const_smul c).add contDiff_const
  set M : ℝ := (|c| + 1) ^ N with hM
  have hM1 : ∀ j ≤ N, |c| ^ j ≤ M := fun j hj =>
    (pow_le_pow_left₀ (abs_nonneg c) (by linarith) j).trans
      (pow_le_pow_right₀ (by linarith [abs_nonneg c]) hj)
  have hM0 : 0 < M := by positivity
  refine ⟨?_, h.smooth₀.comp haff, ⟨M * C, fun j hj x => ?_⟩, fun ε hε => ?_⟩
  · filter_upwards [h.smooth] with i hi using hi.comp haff
  · have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 (Nat.zero_le _) x)
    exact (norm_iteratedFDeriv_affine_le h.smooth₀ c a j x).trans
      (mul_le_mul (hM1 j hj) (hC j hj _) (norm_nonneg _) hM0.le)
  · filter_upwards [h.smooth, h.conv (ε / M) (by positivity)] with i si hi j hj x
    have := norm_iteratedFDeriv_affine_le (si.sub h.smooth₀) c a j x
    refine this.trans ?_
    calc |c| ^ j * ‖iteratedFDeriv ℝ j (fun y => F i y - F₀ y) (c • x + a)‖ ≤ M * (ε / M) :=
          mul_le_mul (hM1 j hj) (hi j hj _) (norm_nonneg _) hM0.le
      _ = ε := by field_simp

end CN

/-! ### Composition with a map smooth on an open set -/

section Comp

universe u

variable {Gc Hc : Type u} [NormedAddCommGroup Gc] [NormedSpace ℝ Gc] [FiniteDimensional ℝ Gc]
  [NormedAddCommGroup Hc] [NormedSpace ℝ Hc]

/-- Eventually the family takes values in a compact thickening of the limit's compact range. -/
theorem CN.eventually_mem {F : ι → E → Gc} {F₀ : E → Gc} (h : CN N l F F₀) {K : Set Gc}
    (hF0 : ∀ x, F₀ x ∈ K) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ i in l, ∀ x, F i x ∈ cthickening δ K ∧ dist (F i x) (F₀ x) ≤ δ := by
  filter_upwards [h.conv δ hδ] with i hi x
  have h0 := hi 0 (Nat.zero_le _) x
  rw [norm_iteratedFDeriv_zero, ← dist_eq_norm] at h0
  exact ⟨mem_cthickening_of_dist_le _ _ _ _ (hF0 x) h0, h0⟩

/-- **`C⁰` continuity of composition.** -/
theorem CN.comp_zero {Ψ : Gc → Hc} {U : Set Gc} (hU : IsOpen U) (hΨ : ContDiffOn ℝ ∞ Ψ U)
    {K : Set Gc} (hK : IsCompact K) (hKU : K ⊆ U) {F : ι → E → Gc} {F₀ : E → Gc}
    (hF0 : ∀ x, F₀ x ∈ K) (h : CN 0 l F F₀) :
    CN 0 l (fun i x => Ψ (F i x)) (fun x => Ψ (F₀ x)) ∧ ∀ᶠ i in l, ∀ x, F i x ∈ U := by
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  have hK' : IsCompact (cthickening δ K) := hK.cthickening
  have hsm : ∀ {f : E → Gc}, ContDiff ℝ ∞ f → (∀ x, f x ∈ U) →
      ContDiff ℝ ∞ (fun x => Ψ (f x)) := fun hf hfU =>
    contDiff_iff_contDiffAt.2 fun x =>
      (hΨ.contDiffAt (hU.mem_nhds (hfU x))).comp x hf.contDiffAt
  obtain ⟨M₀, hM₀⟩ := hK.exists_bound_of_continuousOn (hΨ.continuousOn.mono hKU)
  have hDc : ContinuousOn (fun y => _root_.fderiv ℝ Ψ y) U :=
    hΨ.continuousOn_fderiv_of_isOpen hU (by simp)
  obtain ⟨M₁, hM₁⟩ := hK'.exists_bound_of_continuousOn (hDc.mono hδU)
  have hM₁0 : 0 ≤ M₁ := by
    obtain ⟨x0⟩ : Nonempty E := ⟨0⟩
    exact (norm_nonneg _).trans (hM₁ _ (self_subset_cthickening K (hF0 x0)))
  have hev := h.eventually_mem hF0 hδ
  have hUev : ∀ᶠ i in l, ∀ x, F i x ∈ U := by
    filter_upwards [hev] with i hi x using hδU (hi x).1
  refine ⟨⟨?_, hsm h.smooth₀ fun x => hKU (hF0 x), ⟨M₀, fun j hj x => ?_⟩, fun ε hε => ?_⟩,
    hUev⟩
  · filter_upwards [h.smooth, hUev] with i hi hU' using hsm hi hU'
  · rw [Nat.le_zero.1 hj, norm_iteratedFDeriv_zero]; exact hM₀ _ (hF0 x)
  · set ε' := min δ (ε / (M₁ + 1)) with hε'
    have hε'0 : 0 < ε' := lt_min hδ (by positivity)
    filter_upwards [h.eventually_mem hF0 hε'0] with i hi j hj x
    rw [Nat.le_zero.1 hj, norm_iteratedFDeriv_zero]
    have hball : closedBall (F₀ x) δ ⊆ cthickening δ K :=
      closedBall_subset_cthickening (hF0 x) δ
    have hin : F i x ∈ closedBall (F₀ x) δ :=
      mem_closedBall.2 ((hi x).2.trans (min_le_left _ _))
    have hmv := (convex_closedBall (F₀ x) δ).norm_image_sub_le_of_norm_fderiv_le
      (f := Ψ) (C := M₁)
      (fun y hy => (hΨ.differentiableOn (by simp) y (hδU (hball hy))).differentiableAt
        (hU.mem_nhds (hδU (hball hy))))
      (fun y hy => hM₁ y (hball hy)) (mem_closedBall_self hδ.le) hin
    refine hmv.trans ?_
    rw [← dist_eq_norm]
    calc M₁ * dist (F i x) (F₀ x) ≤ (M₁ + 1) * (ε / (M₁ + 1)) :=
          mul_le_mul (by linarith) ((hi x).2.trans (min_le_right _ _)) dist_nonneg
            (by positivity)
      _ = ε := by field_simp

/-- **`C^N` continuity of composition with a map smooth on an open set** (`Ψ ∘ F_h → Ψ ∘ F` in
`C^N` when `F_h → F` in `C^N` and `F` takes values in a compact subset of the open set). -/
theorem CN.comp {Ψ : Gc → Hc} {U : Set Gc} (hU : IsOpen U) (hΨ : ContDiffOn ℝ ∞ Ψ U)
    {K : Set Gc} (hK : IsCompact K) (hKU : K ⊆ U) {F : ι → E → Gc} {F₀ : E → Gc}
    (hF0 : ∀ x, F₀ x ∈ K) (h : CN N l F F₀) :
    CN N l (fun i x => Ψ (F i x)) (fun x => Ψ (F₀ x)) := by
  induction N generalizing Hc Ψ with
  | zero => exact (CN.comp_zero hU hΨ hK hKU hF0 h).1
  | succ N ih =>
    obtain ⟨h0, hUev⟩ := CN.comp_zero hU hΨ hK hKU hF0 (h.mono (Nat.zero_le _))
    have hDΨ : ContDiffOn ℝ ∞ (fun y => _root_.fderiv ℝ Ψ y) U :=
      hΨ.fderiv_of_isOpen hU (by simp)
    have h1 := ih (Hc := Gc →L[ℝ] Hc) hDΨ (h.mono (Nat.le_succ N))
    have h3 := h1.bilin h.fderiv (ContinuousLinearMap.compL ℝ E Gc Hc)
    refine CN.of_fderiv h0 (h3.congr ?_ ?_)
    · filter_upwards [h.smooth, hUev] with i hi hiU
      funext x
      have hΨd : DifferentiableAt ℝ Ψ (F i x) :=
        (hΨ.differentiableOn (by simp) _ (hiU x)).differentiableAt (hU.mem_nhds (hiU x))
      change _root_.fderiv ℝ (Ψ ∘ F i) x = _
      rw [fderiv_comp x hΨd (hi.differentiable (by simp) x)]
      rfl
    · funext x
      have hx : F₀ x ∈ U := hKU (hF0 x)
      have hΨd : DifferentiableAt ℝ Ψ (F₀ x) :=
        (hΨ.differentiableOn (by simp) _ hx).differentiableAt (hU.mem_nhds hx)
      change _root_.fderiv ℝ (Ψ ∘ F₀) x = _
      rw [fderiv_comp x hΨd (h.smooth₀.differentiable (by simp) x)]
      rfl

end Comp

namespace CN


end CN

end RenewalGeometry.CNConv
