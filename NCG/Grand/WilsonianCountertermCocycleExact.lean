/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Exact Wilsonian counterterm cocycle and source-minimal tail

Machinery for `thm:SMST-Wilsonian-counterterm-cocycle`.

* `counterterm` is the exact shell counterterm `C_{Y/X}(x) = -log ((π_{Y/X})_! W_Y(x) / W_X(x))`
  (QRP.13) for finite configuration spaces with strictly positive weights;
* `cocycle` is (QRP.14): `C_{Z/X}(x) = C_{Y/X}(x) - log 𝔼_{κ_{Y|x}} e^{-C_{Z/Y}}`, and
  `cocycle_additive_iff` identifies the additive branch with `C_{Z/Y}` constant on fibres;
* `head_split` is (QRP.15): the orthogonal split `C = C^head + T^gen` is the unique minimum-norm
  head approximation and obeys Pythagoras;
* `local_tail_bound` is (QRP.16): omitting interactions of diameter `> R` changes the `B`-local
  action by at most `|B| C e^{-aR}`.
-/

open Finset

namespace NCG
namespace Wilsonian

/-! ### The shell counterterm and its cocycle -/

section Cocycle

variable {ΩX ΩY ΩZ : Type*} [Fintype ΩY] [Fintype ΩZ] [DecidableEq ΩX] [DecidableEq ΩY]

/-- The pushforward `(π)_! W (x) = ∑_{y ↦ x} W y`. -/
def push (π : ΩY → ΩX) (W : ΩY → ℝ) (x : ΩX) : ℝ :=
  ∑ y ∈ univ.filter (fun y => π y = x), W y

/-- The exact shell counterterm `C_{Y/X}(x) = -log ((π)_! W_Y(x) / W_X(x))` (QRP.13). -/
noncomputable def counterterm (π : ΩY → ΩX) (WY : ΩY → ℝ) (WX : ΩX → ℝ) (x : ΩX) : ℝ :=
  -Real.log (push π WY x / WX x)

/-- The conditional fibre law `κ_{Y|x}(y) = W_Y(y) / (π)_! W_Y(x)`. -/
noncomputable def kappa (π : ΩY → ΩX) (WY : ΩY → ℝ) (x : ΩX) (y : ΩY) : ℝ :=
  WY y / push π WY x

omit [DecidableEq ΩY] in
theorem push_pos {π : ΩY → ΩX} {WY : ΩY → ℝ} (hW : ∀ y, 0 < WY y) (hsurj : Function.Surjective π)
    (x : ΩX) : 0 < push π WY x := by
  obtain ⟨y, hy⟩ := hsurj x
  exact sum_pos (fun y _ => hW y) ⟨y, by simp [hy]⟩

omit [DecidableEq ΩY] in
theorem exp_neg_counterterm {π : ΩY → ΩX} {WY : ΩY → ℝ} {WX : ΩX → ℝ} (hWY : ∀ y, 0 < WY y)
    (hWX : ∀ x, 0 < WX x) (hsurj : Function.Surjective π) (x : ΩX) :
    Real.exp (-(counterterm π WY WX x)) = push π WY x / WX x := by
  rw [counterterm, neg_neg, Real.exp_log (div_pos (push_pos hWY hsurj x) (hWX x))]

omit [DecidableEq ΩY] in
theorem push_eq_exp_mul {π : ΩY → ΩX} {WY : ΩY → ℝ} {WX : ΩX → ℝ} (hWY : ∀ y, 0 < WY y)
    (hWX : ∀ x, 0 < WX x) (hsurj : Function.Surjective π) (x : ΩX) :
    push π WY x = Real.exp (-(counterterm π WY WX x)) * WX x := by
  rw [exp_neg_counterterm hWY hWX hsurj x, div_mul_cancel₀ _ (hWX x).ne']

omit [DecidableEq ΩY] in
theorem sum_kappa {π : ΩY → ΩX} {WY : ΩY → ℝ} (hW : ∀ y, 0 < WY y)
    (hsurj : Function.Surjective π) (x : ΩX) :
    ∑ y ∈ univ.filter (fun y => π y = x), kappa π WY x y = 1 := by
  simp only [kappa]
  rw [← sum_div]
  exact div_self (push_pos hW hsurj x).ne'

/-- Pushforwards compose: `(π_{Y/X} ∘ π_{Z/Y})_! W_Z(x) = ∑_{y ↦ x} (π_{Z/Y})_! W_Z(y)`. -/
theorem push_comp (πYX : ΩY → ΩX) (πZY : ΩZ → ΩY) (WZ : ΩZ → ℝ) (x : ΩX) :
    push (πYX ∘ πZY) WZ x = ∑ y ∈ univ.filter (fun y => πYX y = x), push πZY WZ y := by
  unfold push
  rw [← sum_fiberwise_of_maps_to (s := univ.filter (fun z => (πYX ∘ πZY) z = x))
    (t := univ.filter (fun y => πYX y = x)) (g := πZY) (fun z hz => by simpa using hz)]
  refine sum_congr rfl fun y hy => ?_
  rw [mem_filter] at hy
  refine sum_congr ?_ fun _ _ => rfl
  ext z
  simp only [mem_filter, mem_univ, true_and, Function.comp]
  constructor
  · rintro ⟨-, h⟩
    exact h
  · intro h
    exact ⟨by rw [h]; exact hy.2, h⟩

/-- **(QRP.14)**: the exact cocycle
`C_{Z/X}(x) = C_{Y/X}(x) - log 𝔼_{κ_{Y|x}} e^{-C_{Z/Y}(Y)}`. -/
theorem cocycle {πYX : ΩY → ΩX} {πZY : ΩZ → ΩY} {WX : ΩX → ℝ} {WY : ΩY → ℝ} {WZ : ΩZ → ℝ}
    (hWX : ∀ x, 0 < WX x) (hWY : ∀ y, 0 < WY y) (hWZ : ∀ z, 0 < WZ z)
    (hYX : Function.Surjective πYX) (hZY : Function.Surjective πZY) (x : ΩX) :
    counterterm (πYX ∘ πZY) WZ WX x
      = counterterm πYX WY WX x
        - Real.log (∑ y ∈ univ.filter (fun y => πYX y = x),
            kappa πYX WY x y * Real.exp (-(counterterm πZY WZ WY y))) := by
  have hpY := push_pos hWY hYX x
  have hS : 0 < ∑ y ∈ univ.filter (fun y => πYX y = x),
      kappa πYX WY x y * Real.exp (-(counterterm πZY WZ WY y)) := by
    obtain ⟨y, hy⟩ := hYX x
    refine sum_pos (fun y _ => mul_pos (div_pos (hWY y) hpY) (Real.exp_pos _)) ⟨y, by simp [hy]⟩
  have hkey : push (πYX ∘ πZY) WZ x / WX x
      = (push πYX WY x / WX x) * ∑ y ∈ univ.filter (fun y => πYX y = x),
          kappa πYX WY x y * Real.exp (-(counterterm πZY WZ WY y)) := by
    rw [push_comp, div_mul_eq_mul_div, mul_sum]
    congr 1
    refine sum_congr rfl fun y _ => ?_
    rw [push_eq_exp_mul hWZ hWY hZY y, kappa]
    field_simp
  rw [counterterm, hkey, Real.log_mul (div_pos hpY (hWX x)).ne' hS.ne', counterterm]
  ring

/-- The cocycle is additive on a fibre exactly when `C_{Z/Y}` is constant on that fibre. -/
theorem cocycle_additive_iff {πYX : ΩY → ΩX} {πZY : ΩZ → ΩY} {WX : ΩX → ℝ} {WY : ΩY → ℝ}
    {WZ : ΩZ → ℝ} (hWX : ∀ x, 0 < WX x) (hWY : ∀ y, 0 < WY y) (hWZ : ∀ z, 0 < WZ z)
    (hYX : Function.Surjective πYX) (hZY : Function.Surjective πZY) (x : ΩX) :
    (∀ y, πYX y = x →
        counterterm (πYX ∘ πZY) WZ WX x = counterterm πYX WY WX x + counterterm πZY WZ WY y)
      ↔ ∃ c : ℝ, ∀ y, πYX y = x → counterterm πZY WZ WY y = c := by
  constructor
  · intro h
    refine ⟨counterterm (πYX ∘ πZY) WZ WX x - counterterm πYX WY WX x, fun y hy => ?_⟩
    rw [h y hy]
    ring
  · rintro ⟨c, hc⟩ y hy
    rw [cocycle hWX hWY hWZ hYX hZY x]
    have hsum : ∑ y ∈ univ.filter (fun y => πYX y = x),
        kappa πYX WY x y * Real.exp (-(counterterm πZY WZ WY y)) = Real.exp (-c) := by
      rw [show Real.exp (-c) = (∑ y ∈ univ.filter (fun y => πYX y = x), kappa πYX WY x y) *
          Real.exp (-c) by rw [sum_kappa hWY hYX x, one_mul], sum_mul]
      refine sum_congr rfl fun y' hy' => ?_
      rw [mem_filter] at hy'
      rw [hc y' hy'.2]
    rw [hsum, Real.log_exp, hc y hy]
    ring

end Cocycle

/-! ### The orthogonal head split (QRP.15) -/

section Head

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **(QRP.15)**: the orthogonal split `C = C^head + T^gen` onto a head space `K` is the unique
minimum-norm head approximation and obeys exact Pythagoras. -/
theorem head_split (K : Submodule ℝ E) [K.HasOrthogonalProjection] (C : E) :
    K.starProjection C ∈ K ∧ C - K.starProjection C ∈ Kᗮ ∧
      ‖C‖ ^ 2 = ‖K.starProjection C‖ ^ 2 + ‖C - K.starProjection C‖ ^ 2 ∧
      (∀ v ∈ K, ‖C - K.starProjection C‖ ≤ ‖C - v‖) ∧
      ∀ v ∈ K, ‖C - v‖ = ‖C - K.starProjection C‖ → v = K.starProjection C := by
  have hmem : K.starProjection C ∈ K := K.starProjection_apply_mem C
  have horth : C - K.starProjection C ∈ Kᗮ := K.sub_starProjection_mem_orthogonal C
  have hpyth : ∀ v ∈ K,
      ‖C - v‖ ^ 2 = ‖C - K.starProjection C‖ ^ 2 + ‖K.starProjection C - v‖ ^ 2 := by
    intro v hv
    have hdecomp : C - v = (C - K.starProjection C) + (K.starProjection C - v) := by abel
    rw [hdecomp, pow_two, pow_two, pow_two]
    exact norm_add_sq_eq_norm_sq_add_norm_sq_real
      (K.starProjection_inner_eq_zero C _ (K.sub_mem hmem hv))
  refine ⟨hmem, horth, ?_, fun v hv => ?_, fun v hv hnorm => ?_⟩
  · have h := hpyth 0 K.zero_mem
    simp only [sub_zero] at h
    linarith
  · have h := hpyth v hv
    have h2 : ‖C - K.starProjection C‖ ^ 2 ≤ ‖C - v‖ ^ 2 := by
      rw [h]
      exact le_add_of_nonneg_right (sq_nonneg _)
    exact le_of_sq_le_sq h2 (norm_nonneg _)
  · have h := hpyth v hv
    rw [hnorm] at h
    have h0 : ‖K.starProjection C - v‖ ^ 2 = 0 := by linarith
    have h1 : K.starProjection C - v = 0 :=
      norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h0)
    exact (sub_eq_zero.mp h1).symm

end Head

/-! ### The quasilocal tail bound (QRP.16) -/

section Tail

variable {Λ : Type*} [DecidableEq Λ]

/-- **(QRP.16)**: if `sup_x ∑_{A ∋ x} e^{a diam A} ‖Φ_A‖ ≤ C`, omitting the interactions of
diameter `> R` meeting a finite region `B` changes the `B`-local action by at most
`|B| C e^{-aR}`. -/
theorem local_tail_bound (𝒜 : Finset (Finset Λ)) (diam nrm : Finset Λ → ℝ)
    (hnrm : ∀ A, 0 ≤ nrm A) {a C R : ℝ} (ha : 0 ≤ a)
    (hsum : ∀ x : Λ, ∑ A ∈ 𝒜.filter (fun A => x ∈ A), Real.exp (a * diam A) * nrm A ≤ C)
    (B : Finset Λ) :
    ∑ A ∈ 𝒜.filter (fun A => (A ∩ B).Nonempty ∧ R < diam A), nrm A
      ≤ B.card * (C * Real.exp (-(a * R))) := by
  set S := 𝒜.filter (fun A => (A ∩ B).Nonempty ∧ R < diam A) with hS
  have h1 : ∑ A ∈ S, nrm A ≤ ∑ A ∈ S, ∑ _x ∈ A ∩ B, nrm A := by
    refine sum_le_sum fun A hA => ?_
    rw [sum_const, nsmul_eq_mul]
    have hcard : 1 ≤ (A ∩ B).card := (mem_filter.mp hA).2.1.card_pos
    have hcard' : (1 : ℝ) ≤ (A ∩ B).card := by exact_mod_cast hcard
    calc nrm A = 1 * nrm A := (one_mul _).symm
      _ ≤ (A ∩ B).card * nrm A := mul_le_mul_of_nonneg_right hcard' (hnrm A)
  have h2 : ∑ A ∈ S, ∑ _x ∈ A ∩ B, nrm A = ∑ x ∈ B, ∑ A ∈ S.filter (fun A => x ∈ A), nrm A := by
    rw [sum_comm']
    intro A x
    simp only [mem_inter, mem_filter]
    tauto
  have h3 : ∀ x ∈ B, ∑ A ∈ S.filter (fun A => x ∈ A), nrm A ≤ C * Real.exp (-(a * R)) := by
    intro x _
    have hsub : S.filter (fun A => x ∈ A) ⊆ 𝒜.filter (fun A => x ∈ A) :=
      filter_subset_filter _ (filter_subset _ _)
    calc ∑ A ∈ S.filter (fun A => x ∈ A), nrm A
        ≤ ∑ A ∈ S.filter (fun A => x ∈ A),
            Real.exp (-(a * R)) * (Real.exp (a * diam A) * nrm A) := by
          refine sum_le_sum fun A hA => ?_
          have hR : R < diam A := (mem_filter.mp (mem_filter.mp hA).1).2.2
          have hone : 1 ≤ Real.exp (-(a * R)) * Real.exp (a * diam A) := by
            rw [← Real.exp_add]
            apply Real.one_le_exp
            nlinarith
          calc nrm A = 1 * nrm A := (one_mul _).symm
            _ ≤ (Real.exp (-(a * R)) * Real.exp (a * diam A)) * nrm A :=
                mul_le_mul_of_nonneg_right hone (hnrm A)
            _ = Real.exp (-(a * R)) * (Real.exp (a * diam A) * nrm A) := by ring
      _ = Real.exp (-(a * R)) *
            ∑ A ∈ S.filter (fun A => x ∈ A), Real.exp (a * diam A) * nrm A := by
          rw [mul_sum]
      _ ≤ Real.exp (-(a * R)) *
            ∑ A ∈ 𝒜.filter (fun A => x ∈ A), Real.exp (a * diam A) * nrm A := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
          exact sum_le_sum_of_subset_of_nonneg hsub fun A _ _ =>
            mul_nonneg (Real.exp_pos _).le (hnrm A)
      _ ≤ Real.exp (-(a * R)) * C := mul_le_mul_of_nonneg_left (hsum x) (Real.exp_pos _).le
      _ = C * Real.exp (-(a * R)) := by ring
  calc ∑ A ∈ S, nrm A ≤ ∑ x ∈ B, ∑ A ∈ S.filter (fun A => x ∈ A), nrm A := h1.trans h2.le
    _ ≤ ∑ x ∈ B, C * Real.exp (-(a * R)) := sum_le_sum h3
    _ = B.card * (C * Real.exp (-(a * R))) := by rw [sum_const, nsmul_eq_mul]

end Tail

/-! ### The bundled theorem -/

/-- **`thm:SMST-Wilsonian-counterterm-cocycle`**: the exact cocycle (QRP.14) with its additive
branch, the orthogonal head split (QRP.15), and the quasilocal tail bound (QRP.16). -/
theorem wilsonian_counterterm_cocycle {ΩX ΩY ΩZ : Type*} [Fintype ΩY] [Fintype ΩZ]
    [DecidableEq ΩX] [DecidableEq ΩY] {πYX : ΩY → ΩX} {πZY : ΩZ → ΩY} {WX : ΩX → ℝ}
    {WY : ΩY → ℝ} {WZ : ΩZ → ℝ} (hWX : ∀ x, 0 < WX x) (hWY : ∀ y, 0 < WY y)
    (hWZ : ∀ z, 0 < WZ z) (hYX : Function.Surjective πYX) (hZY : Function.Surjective πZY)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (K : Submodule ℝ E)
    [K.HasOrthogonalProjection] {Λ : Type*} [DecidableEq Λ] (𝒜 : Finset (Finset Λ))
    (diam nrm : Finset Λ → ℝ) (hnrm : ∀ A, 0 ≤ nrm A) {a C R : ℝ} (ha : 0 ≤ a)
    (hsum : ∀ x : Λ, ∑ A ∈ 𝒜.filter (fun A => x ∈ A), Real.exp (a * diam A) * nrm A ≤ C) :
    (∀ x, counterterm (πYX ∘ πZY) WZ WX x
        = counterterm πYX WY WX x
          - Real.log (∑ y ∈ univ.filter (fun y => πYX y = x),
              kappa πYX WY x y * Real.exp (-(counterterm πZY WZ WY y)))) ∧
      (∀ x, (∀ y, πYX y = x → counterterm (πYX ∘ πZY) WZ WX x
            = counterterm πYX WY WX x + counterterm πZY WZ WY y)
          ↔ ∃ c : ℝ, ∀ y, πYX y = x → counterterm πZY WZ WY y = c) ∧
      (∀ Cf : E, K.starProjection Cf ∈ K ∧ Cf - K.starProjection Cf ∈ Kᗮ ∧
        ‖Cf‖ ^ 2 = ‖K.starProjection Cf‖ ^ 2 + ‖Cf - K.starProjection Cf‖ ^ 2 ∧
        (∀ v ∈ K, ‖Cf - K.starProjection Cf‖ ≤ ‖Cf - v‖) ∧
        ∀ v ∈ K, ‖Cf - v‖ = ‖Cf - K.starProjection Cf‖ → v = K.starProjection Cf) ∧
      ∀ B : Finset Λ, ∑ A ∈ 𝒜.filter (fun A => (A ∩ B).Nonempty ∧ R < diam A), nrm A
        ≤ B.card * (C * Real.exp (-(a * R))) :=
  ⟨cocycle hWX hWY hWZ hYX hZY, cocycle_additive_iff hWX hWY hWZ hYX hZY, head_split K,
    local_tail_bound 𝒜 diam nrm hnrm ha hsum⟩

end Wilsonian
end NCG
