/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The polyhedral Lorentzian continuum: reverse triangle inequality

**Theorem `thm:taxicab-limit`** (Lorentzian pre-length core): the
geometric-mean time separation
`τ_g(X,Y) = (∏ᵢ(Yᵢ−Xᵢ))^{1/c}` of the calibrated product continuum
satisfies the **reverse triangle inequality** along causal chains,

`τ_g(X,Y) + τ_g(Y,Z) ≤ τ_g(X,Z)`  for `X ≤ Y ≤ Z`

(`NCG.taxicab_reverse_triangle`), via the superadditivity of the
geometric mean — Mahler's inequality, proved here from two applications
of the weighted AM–GM (`NCG.geomMean_superadditive`).  Together with
the order-monotone calibrated rescaling (`NCG.calibratedRescale_mono`)
this is the Lorentzian pre-length structure of the deterministic
product cone; the measured Gromov–Hausdorff convergence bookkeeping is
not formalised. -/

namespace NCG

open Finset

/-- **Superadditivity of the geometric mean** (Mahler's inequality):
`(∏a)^{1/c} + (∏b)^{1/c} ≤ (∏(a+b))^{1/c}` for nonnegative families —
the concavity that makes `τ_g` a Lorentzian time separation
(Theorem `thm:taxicab-limit`). -/
theorem geomMean_superadditive {c : ℕ} (hc : 0 < c) (a b : Fin c → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) :
    (∏ i, a i) ^ ((1:ℝ)/c) + (∏ i, b i) ^ ((1:ℝ)/c)
      ≤ (∏ i, (a i + b i)) ^ ((1:ℝ)/c) := by
  have hc' : ((c:ℕ):ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hc.ne'
  have hr : ((1:ℝ)/c) ≠ 0 := one_div_ne_zero hc'
  by_cases hzero : ∃ i, a i + b i = 0
  · obtain ⟨i0, hi0⟩ := hzero
    have hai : a i0 = 0 := by
      have h1 := ha i0
      have h2 := hb i0
      linarith
    have hbi : b i0 = 0 := by
      have h1 := ha i0
      have h2 := hb i0
      linarith
    have hpa : (∏ i, a i) = 0 :=
      Finset.prod_eq_zero (mem_univ i0) hai
    have hpb : (∏ i, b i) = 0 :=
      Finset.prod_eq_zero (mem_univ i0) hbi
    rw [hpa, hpb, Real.zero_rpow hr, add_zero]
    exact Real.rpow_nonneg
      (Finset.prod_nonneg fun i _ => by
        have h1 := ha i
        have h2 := hb i
        linarith) _
  · push_neg at hzero
    have hs : ∀ i, 0 < a i + b i := fun i =>
      lt_of_le_of_ne (by
        have h1 := ha i
        have h2 := hb i
        linarith) (Ne.symm (hzero i))
    have hSpos : 0 < ∏ i, (a i + b i) :=
      Finset.prod_pos fun i _ => hs i
    have hx : ∀ i, 0 ≤ a i / (a i + b i) := fun i =>
      div_nonneg (ha i) (hs i).le
    have hy : ∀ i, 0 ≤ b i / (a i + b i) := fun i =>
      div_nonneg (hb i) (hs i).le
    have hw : ∑ _i : Fin c, (1:ℝ)/c = 1 := by
      rw [Finset.sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    have hgx := Real.geom_mean_le_arith_mean_weighted univ
      (fun _ => (1:ℝ)/c) (fun i => a i / (a i + b i))
      (fun i _ => by positivity) hw (fun i _ => hx i)
    have hgy := Real.geom_mean_le_arith_mean_weighted univ
      (fun _ => (1:ℝ)/c) (fun i => b i / (a i + b i))
      (fun i _ => by positivity) hw (fun i _ => hy i)
    have hsum : (∑ i, (1:ℝ)/c * (a i / (a i + b i)))
        + (∑ i, (1:ℝ)/c * (b i / (a i + b i))) = 1 := by
      rw [← Finset.sum_add_distrib]
      calc ∑ i, ((1:ℝ)/c * (a i / (a i + b i))
            + (1:ℝ)/c * (b i / (a i + b i)))
          = ∑ _i : Fin c, (1:ℝ)/c := by
            refine Finset.sum_congr rfl fun i _ => ?_
            have hne := (hs i).ne'
            field_simp
        _ = 1 := hw
    have hcomb : (∏ i, (a i / (a i + b i)) ^ ((1:ℝ)/c))
        + (∏ i, (b i / (a i + b i)) ^ ((1:ℝ)/c)) ≤ 1 := by
      calc (∏ i, (a i / (a i + b i)) ^ ((1:ℝ)/c))
          + (∏ i, (b i / (a i + b i)) ^ ((1:ℝ)/c))
          ≤ (∑ i, (1:ℝ)/c * (a i / (a i + b i)))
            + (∑ i, (1:ℝ)/c * (b i / (a i + b i))) :=
            add_le_add hgx hgy
        _ = 1 := hsum
    rw [Real.finsetProd_rpow univ _ (fun i _ => hx i) _,
      Real.finsetProd_rpow univ _ (fun i _ => hy i) _,
      Finset.prod_div_distrib, Finset.prod_div_distrib,
      Real.div_rpow (Finset.prod_nonneg fun i _ => ha i) hSpos.le,
      Real.div_rpow (Finset.prod_nonneg fun i _ => hb i) hSpos.le,
      ← add_div,
      div_le_one (Real.rpow_pos_of_pos hSpos _)] at hcomb
    exact hcomb

/-- **Theorem `thm:taxicab-limit`** (reverse triangle inequality): the
geometric-mean time separation is superadditive along causal chains
`X ≤ Y ≤ Z` — the polyhedral product continuum is a Lorentzian
pre-length space. -/
theorem taxicab_reverse_triangle {c : ℕ} (hc : 0 < c)
    (X Y Z : Fin c → ℝ) (hXY : ∀ i, X i ≤ Y i) (hYZ : ∀ i, Y i ≤ Z i) :
    (∏ i, (Y i - X i)) ^ ((1:ℝ)/c) + (∏ i, (Z i - Y i)) ^ ((1:ℝ)/c)
      ≤ (∏ i, (Z i - X i)) ^ ((1:ℝ)/c) := by
  have h := geomMean_superadditive hc (fun i => Y i - X i)
    (fun i => Z i - Y i) (fun i => by have := hXY i; linarith)
    (fun i => by have := hYZ i; linarith)
  calc (∏ i, (Y i - X i)) ^ ((1:ℝ)/c)
      + (∏ i, (Z i - Y i)) ^ ((1:ℝ)/c)
      ≤ (∏ i, ((Y i - X i) + (Z i - Y i))) ^ ((1:ℝ)/c) := h
    _ = (∏ i, (Z i - X i)) ^ ((1:ℝ)/c) := by
        congr 1
        refine Finset.prod_congr rfl fun i _ => ?_
        ring

/-- **Lemma `lem:optical-distance-stability` (core)**: the optical
(geometric-mean) time functional is stable under metric comparison —
if each channel factor of one metric is controlled by `K` times the
corresponding factor of another, `aᵢ ≤ K·bᵢ`, then the geometric means
compare with the *same* constant, `(∏a)^{1/c} ≤ K·(∏b)^{1/c}`.  Applied
with `K = 1 + ε` in both directions this gives bi-Lipschitz stability
of the optical distance under `ε`-perturbations of the metric. -/
theorem geomMean_scale_mono {c : ℕ} (hc : 0 < c) (a b : Fin c → ℝ)
    (K : ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (hK : 0 ≤ K)
    (hab : ∀ i, a i ≤ K * b i) :
    (∏ i, a i) ^ ((1:ℝ)/c) ≤ K * (∏ i, b i) ^ ((1:ℝ)/c) := by
  have hc0 : ((c:ℕ):ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hc.ne'
  have hprod : (∏ i, a i) ≤ ∏ i, (K * b i) :=
    Finset.prod_le_prod (fun i _ => ha i) (fun i _ => hab i)
  have hKb : (∏ i, (K * b i)) = K ^ c * ∏ i, b i := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  calc (∏ i, a i) ^ ((1:ℝ)/c)
      ≤ (K ^ c * ∏ i, b i) ^ ((1:ℝ)/c) := by
        refine Real.rpow_le_rpow (Finset.prod_nonneg fun i _ => ha i)
          ?_ (by positivity)
        rw [← hKb]
        exact hprod
    _ = (K ^ c) ^ ((1:ℝ)/c) * (∏ i, b i) ^ ((1:ℝ)/c) :=
        Real.mul_rpow (by positivity)
          (Finset.prod_nonneg fun i _ => hb i)
    _ = K * (∏ i, b i) ^ ((1:ℝ)/c) := by
        rw [← Real.rpow_natCast K c, ← Real.rpow_mul hK,
          mul_one_div, div_self hc0, Real.rpow_one]

end NCG
