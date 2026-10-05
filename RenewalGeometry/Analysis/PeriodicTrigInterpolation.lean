/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Analysis.VectorTrigPolynomial

/-!
# Trigonometric interpolation of periodic grid records with values in a real normed space

Generic infrastructure (no renewal notions) for `eq:native-tail` and `lem:native-tail-transfer` of
the Einstein–Standard-Model action-closure manuscript (`sec:native-branch`, "Finite residual and
leakage budgets").

## Setting (the manuscript's)

The periodic auxiliary box has period `2π` in each of the `d` coordinates; `n` is odd, the mesh is
`h = 2π/n` and the node `x ∈ (ℤ/n)^d` sits at `h x̃` (`gpos`, `x̃ ∈ {0, …, n-1}^d`).  The represented
frequencies are `Λ_h = {ℓ ∈ ℤ^d : |ℓ_μ| ≤ (n-1)/2}` (`box`).  For a record `u : (ℤ/n)^d → V` with
values in a real normed space, the discrete Fourier coefficients
`û(ℓ) = n^{-d} Σ_y e^{-iℓ·y} u(y)` have real and imaginary parts `(a_ℓ, -b_ℓ)` with
`a_ℓ = n^{-d} Σ_y cos(ℓ·y) u(y)`, `b_ℓ = n^{-d} Σ_y sin(ℓ·y) u(y)` (`coefOf`), and the trigonometric
reconstruction `𝓘_h^trig u = Σ_{ℓ ∈ Λ_h} û(ℓ) e^{iℓ·x}` is, written in real form,
`recon u = Σ_{ℓ ∈ Λ_h} (cos(ℓ·x) a_ℓ + sin(ℓ·x) b_ℓ)`.  The coefficient size
`|û(ℓ)| := |a_ℓ| + |b_ℓ|` (`VecTrig.cn`) is equivalent to any norm of the complex vector `û(ℓ)`.

For `K > 0` the low-frequency comparison head `z^lo = 𝓘_h^trig P_{≤K} u` is the same sum over
`|ℓ|_∞ ≤ K` (`reconLow`; `P_{≤K}` is the Fourier truncation of the record), and
`τ_j(K) = Σ_{ℓ ∈ Λ_h, |ℓ|_∞ > K} (1 + |ℓ|₁/K)^j |û(ℓ)|` (`tau`, `eq:native-tail`).

## Main results

* **`recon_gpos`** (`n` odd): the reconstruction interpolates the record, `𝓘_h^trig u(h x̃) = u(x)`
  (discrete orthogonality `sum_cexp_box`).
* `tp_periodic`, `recon_periodic`: period `2π` in every coordinate.
* `recon_sub_reconLow`: `z - z^lo` is the measured tail (no coefficient deleted).
* **`norm_iteratedFDeriv_tail_le`** (`eq:native-tail-derivatives`, iterated-derivative form):
  `‖D^i(z - z^lo)(x)‖ ≤ K^i τ_j(K)` for `i ≤ j` (operator norm in the sup norm of `ℝ^d`, which
  dominates `|∂^α|`, `|α| = i`; the constant is `C_j = 1` in the period-`2π` normalisation).
* **`norm_iteratedFDeriv_reconLow_le`** (Bernstein for the low head): if `|z^lo| ≤ A` then
  `‖D^j z^lo(x)‖ ≤ (60 d K)^j A`.
-/

open Finset

namespace RenewalGeometry.TrigInterp

open VecTrig

noncomputable section

set_option linter.unusedSectionVars false

variable {d : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-! ### Periodicity -/

theorem phase_add_two_pi (ℓ : Fin d → ℤ) (x : Fin d → ℝ) (μ : Fin d) :
    phase ℓ (x + Pi.single μ (2 * Real.pi)) = phase ℓ x + (ℓ μ : ℝ) * (2 * Real.pi) := by
  have := phase_add_single ℓ x μ (2 * Real.pi)
  rwa [show (2 * Real.pi) • (Pi.single μ (1 : ℝ) : Fin d → ℝ) = Pi.single μ (2 * Real.pi) by
    rw [← Pi.single_smul]; simp] at this

/-- Trigonometric polynomials with integer frequencies have period `2π` in every coordinate. -/
theorem tp_periodic (S : Finset (Fin d → ℤ)) (c : Coef d V) (x : Fin d → ℝ) (μ : Fin d) :
    tp S c (x + Pi.single μ (2 * Real.pi)) = tp S c x := by
  unfold tp
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [phase_add_two_pi]
  have hc : Real.cos (phase ℓ x + (ℓ μ : ℝ) * (2 * Real.pi)) = Real.cos (phase ℓ x) := by
    rw [show (ℓ μ : ℝ) * (2 * Real.pi) = ((ℓ μ : ℤ) : ℝ) * (2 * Real.pi) from rfl]
    exact Real.cos_add_int_mul_two_pi _ _
  have hs : Real.sin (phase ℓ x + (ℓ μ : ℝ) * (2 * Real.pi)) = Real.sin (phase ℓ x) := by
    exact Real.sin_add_int_mul_two_pi _ _
  rw [hc, hs]

/-! ### The grid, the frequency box and discrete orthogonality -/

variable (n : ℕ) [NeZero n]

/-- The node position `h x̃`, `h = 2π/n`. -/
def gpos (x : Fin d → ZMod n) : Fin d → ℝ := fun μ => (2 * Real.pi / n) * ((x μ).val : ℝ)

/-- `M = (n-1)/2`. -/
def half : ℕ := (n - 1) / 2

/-- The represented frequencies `Λ_h = {|ℓ_μ| ≤ (n-1)/2}`. -/
def box (d : ℕ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun _ : Fin d => Finset.Icc (-(half n : ℤ)) (half n)

/-- One-dimensional discrete orthogonality: for `n = 2M+1` and `|k| < n`,
`Σ_{|m| ≤ M} e^{2πimk/n} = n [k = 0]`. -/
theorem sum_cexp_Icc (hn : Odd n) (k : ℤ) (hk : |k| < n) :
    ∑ m ∈ Finset.Icc (-(half n : ℤ)) (half n),
        Complex.exp ((m : ℂ) * (2 * Real.pi * k / n : ℝ) * Complex.I) =
      if k = 0 then (n : ℂ) else 0 := by
  obtain ⟨M, rfl⟩ := hn
  have hM : half (2 * M + 1) = M := by unfold half; omega
  rw [hM]
  set θ : ℝ := 2 * Real.pi * k / (2 * M + 1 : ℕ)
  set r : ℂ := Complex.exp ((θ : ℂ) * Complex.I)
  have hterm : ∀ m : ℤ, Complex.exp ((m : ℂ) * (θ : ℂ) * Complex.I) = r ^ m := by
    intro m
    rw [← Complex.exp_int_mul]; congr 1; ring
  simp_rw [hterm]
  -- reindex `m = i - M`, `i ∈ [0, 2M]`
  have hre : ∑ m ∈ Finset.Icc (-(M : ℤ)) M, r ^ m =
      ∑ i ∈ Finset.range (2 * M + 1), r ^ ((i : ℤ) - M) := by
    refine Finset.sum_nbij' (fun m => (m + M).toNat) (fun i => (i : ℤ) - M) ?_ ?_ ?_ ?_ ?_
    · intro m hm; rw [Finset.mem_Icc] at hm
      show (m + M).toNat ∈ Finset.range (2 * M + 1)
      rw [Finset.mem_range]; omega
    · intro i hi; rw [Finset.mem_range] at hi
      show (i : ℤ) - M ∈ Finset.Icc (-(M : ℤ)) M
      rw [Finset.mem_Icc]; omega
    · intro m hm; rw [Finset.mem_Icc] at hm
      show (((m + M).toNat : ℕ) : ℤ) - M = m; omega
    · intro i _; show ((i : ℤ) - M + M).toNat = i; omega
    · intro m hm; rw [Finset.mem_Icc] at hm
      show r ^ m = r ^ ((((m + M).toNat : ℕ) : ℤ) - M)
      congr 1; omega
  rw [hre]
  have hr0 : r ≠ 0 := Complex.exp_ne_zero _
  have hsplit : ∀ i : ℕ, r ^ ((i : ℤ) - M) = r ^ (-(M : ℤ)) * r ^ i := by
    intro i
    rw [← zpow_natCast, ← zpow_add₀ hr0]; congr 1; ring
  simp_rw [hsplit]
  rw [← Finset.mul_sum]
  split_ifs with hk0
  · subst hk0
    have : r = 1 := by simp [r, θ]
    simp [this]
  · have hrn : r ^ (2 * M + 1) = 1 := by
      have e : ((2 * M + 1 : ℕ) : ℂ) * ((θ : ℂ) * Complex.I) = (k : ℂ) * (2 * Real.pi * Complex.I) := by
        simp only [θ]; push_cast
        have : (2 * (M : ℂ) + 1) ≠ 0 := by exact_mod_cast (by positivity : (2 * (M : ℝ) + 1) ≠ 0)
        field_simp
      rw [← Complex.exp_nat_mul, e, Complex.exp_int_mul_two_pi_mul_I]
    have hr1 : r ≠ 1 := by
      intro h
      rw [Complex.exp_eq_one_iff] at h
      obtain ⟨N, hN⟩ := h
      have hpos : (0 : ℝ) < 2 * M + 1 := by positivity
      have h2 : (θ : ℂ) = (N : ℂ) * (2 * Real.pi) := by
        have hI : Complex.I ≠ 0 := Complex.I_ne_zero
        have := hN
        rw [show (N : ℂ) * (2 * Real.pi * Complex.I) = ((N : ℂ) * (2 * Real.pi)) * Complex.I by ring]
          at this
        exact mul_right_cancel₀ hI this
      have h3 : θ = N * (2 * Real.pi) := by exact_mod_cast h2
      simp only [θ] at h3
      have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
      have h4 : (k : ℝ) = N * (2 * M + 1) := by
        push_cast at h3
        field_simp at h3
        nlinarith [h3]
      have h5 : k = N * (2 * M + 1) := by exact_mod_cast h4
      have : N = 0 := by
        push_cast at hk
        have h6 : |k| = |N| * (2 * M + 1) := by
          rw [h5, abs_mul, abs_of_pos (by positivity : (0 : ℤ) < 2 * M + 1)]
        have h7 : |N| < 1 := by nlinarith [abs_nonneg N]
        have := abs_lt.mp h7; omega
      rw [this, zero_mul] at h5
      exact hk0 h5
    rw [geom_sum_eq hr1, hrn, sub_self, zero_div, mul_zero]

/-- `d`-dimensional discrete orthogonality on the frequency box. -/
theorem sum_cexp_box (hn : Odd n) (k : Fin d → ℤ) (hk : ∀ μ, |k μ| < n) :
    ∑ ℓ ∈ box n d, Complex.exp ((∑ μ, (ℓ μ : ℂ) * (2 * Real.pi * k μ / n : ℝ)) * Complex.I) =
      if k = 0 then ((n : ℂ) ^ d) else 0 := by
  have hprod : ∀ ℓ : Fin d → ℤ,
      Complex.exp ((∑ μ, (ℓ μ : ℂ) * (2 * Real.pi * k μ / n : ℝ)) * Complex.I) =
        ∏ μ, Complex.exp ((ℓ μ : ℂ) * (2 * Real.pi * k μ / n : ℝ) * Complex.I) := by
    intro ℓ
    rw [Finset.sum_mul, Complex.exp_sum]
  simp_rw [hprod]
  have hpu := Finset.prod_univ_sum (fun _ : Fin d => Finset.Icc (-(half n : ℤ)) (half n))
    (fun μ (m : ℤ) => Complex.exp ((m : ℂ) * (2 * Real.pi * k μ / n : ℝ) * Complex.I))
  rw [box, ← hpu]
  simp_rw [sum_cexp_Icc n hn _ (hk _)]
  by_cases hk0 : k = 0
  · subst hk0; simp
  · rw [if_neg hk0]
    obtain ⟨μ, hμ⟩ : ∃ μ, k μ ≠ 0 := by
      by_contra h; push_neg at h; exact hk0 (funext h)
    exact Finset.prod_eq_zero (Finset.mem_univ μ) (by simp [hμ])

/-! ### The reconstruction -/

/-- The real Fourier coefficients `(a_ℓ, b_ℓ)` of a record. -/
def coefOf (u : (Fin d → ZMod n) → V) : Coef d V := fun ℓ =>
  (((n : ℝ) ^ d)⁻¹ • ∑ y, Real.cos (phase ℓ (gpos n y)) • u y,
    ((n : ℝ) ^ d)⁻¹ • ∑ y, Real.sin (phase ℓ (gpos n y)) • u y)

/-- **The trigonometric reconstruction** `z_h = 𝓘_h^trig u`. -/
def recon (u : (Fin d → ZMod n) → V) : (Fin d → ℝ) → V := tp (box n d) (coefOf n u)

/-- The low frequencies `|ℓ|_∞ ≤ K` of the box. -/
def lowBox (K : ℝ) : Finset (Fin d → ℤ) := (box n d).filter fun ℓ => ∀ μ, |(ℓ μ : ℝ)| ≤ K

/-- The measured tail frequencies `|ℓ|_∞ > K` of the box. -/
def tailBox (K : ℝ) : Finset (Fin d → ℤ) := (box n d).filter fun ℓ => ¬ ∀ μ, |(ℓ μ : ℝ)| ≤ K

/-- **The low-frequency comparison head** `z_h^lo = 𝓘_h^trig P_{≤K} u`. -/
def reconLow (K : ℝ) (u : (Fin d → ZMod n) → V) : (Fin d → ℝ) → V := tp (lowBox n K) (coefOf n u)

/-- **The measured tails** `τ_j(K) = Σ_{|ℓ|_∞ > K} (1 + |ℓ|₁/K)^j |û(ℓ)|` (`eq:native-tail`). -/
def tau (K : ℝ) (j : ℕ) (u : (Fin d → ZMod n) → V) : ℝ :=
  ∑ ℓ ∈ tailBox n K, (1 + l1 ℓ / K) ^ j * cn (coefOf n u) ℓ

theorem tau_nonneg {K : ℝ} (hK : 0 < K) (j : ℕ) (u : (Fin d → ZMod n) → V) : 0 ≤ tau n K j u :=
  Finset.sum_nonneg fun ℓ _ => mul_nonneg (pow_nonneg (by
    have := div_nonneg (l1_nonneg ℓ) hK.le; linarith) _) (cn_nonneg _ _)

theorem tau_mono {K : ℝ} (hK : 0 < K) {j m : ℕ} (hjm : j ≤ m) (u : (Fin d → ZMod n) → V) :
    tau n K j u ≤ tau n K m u :=
  Finset.sum_le_sum fun ℓ _ => mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by have := div_nonneg (l1_nonneg ℓ) hK.le; linarith) hjm) (cn_nonneg _ _)

theorem recon_periodic (u : (Fin d → ZMod n) → V) (x : Fin d → ℝ) (μ : Fin d) :
    recon n u (x + Pi.single μ (2 * Real.pi)) = recon n u x := tp_periodic _ _ _ _

theorem reconLow_periodic (K : ℝ) (u : (Fin d → ZMod n) → V) (x : Fin d → ℝ) (μ : Fin d) :
    reconLow n K u (x + Pi.single μ (2 * Real.pi)) = reconLow n K u x := tp_periodic _ _ _ _

/-- `z - z^lo` is the measured tail (no coefficient deleted). -/
theorem recon_sub_reconLow (K : ℝ) (u : (Fin d → ZMod n) → V) (x : Fin d → ℝ) :
    recon n u x - reconLow n K u x = tp (tailBox n K) (coefOf n u) x := by
  unfold recon reconLow lowBox tailBox tp
  rw [← Finset.sum_filter_add_sum_filter_not (box n d) (fun ℓ => ∀ μ, |(ℓ μ : ℝ)| ≤ K)]
  abel

theorem recon_sub_reconLow_fun (K : ℝ) (u : (Fin d → ZMod n) → V) :
    (fun x => recon n u x - reconLow n K u x) = tp (tailBox n K) (coefOf n u) :=
  funext (recon_sub_reconLow n K u)

/-- **`eq:native-tail-derivatives`** (iterated-derivative form): for `i ≤ j`,
`‖D^i(z - z^lo)(x)‖ ≤ K^i τ_j(K)`. -/
theorem norm_iteratedFDeriv_tail_le {K : ℝ} (hK : 0 < K) (u : (Fin d → ZMod n) → V) {i j : ℕ}
    (hij : i ≤ j) (x : Fin d → ℝ) :
    ‖iteratedFDeriv ℝ i (fun x => recon n u x - reconLow n K u x) x‖ ≤ K ^ i * tau n K j u := by
  rw [recon_sub_reconLow_fun]
  refine (norm_iteratedFDeriv_tp_le _ _ i x).trans ?_
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (tau_mono n hK hij u) (by positivity))
  rw [tau, Finset.mul_sum]
  refine Finset.sum_le_sum fun ℓ _ => ?_
  rw [← mul_assoc, ← mul_pow]
  refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (l1_nonneg ℓ) ?_ i) (cn_nonneg _ _)
  rw [mul_add, mul_one, mul_div_cancel₀ _ hK.ne']
  linarith

/-- The uniform distance of the full and low fields: `|z - z^lo| ≤ τ_0 ≤ τ_j`. -/
theorem norm_recon_sub_reconLow_le {K : ℝ} (hK : 0 < K) (u : (Fin d → ZMod n) → V) (j : ℕ)
    (x : Fin d → ℝ) : ‖recon n u x - reconLow n K u x‖ ≤ tau n K j u := by
  have h := norm_iteratedFDeriv_tail_le n hK u (Nat.zero_le j) x
  rwa [norm_iteratedFDeriv_zero, pow_zero, one_mul] at h

/-- **Bernstein for the low head**: if `|z^lo| ≤ A` on `ℝ^d` then `‖D^j z^lo(x)‖ ≤ (60 d K)^j A`. -/
theorem norm_iteratedFDeriv_reconLow_le {K : ℝ} (hK : 0 ≤ K) (u : (Fin d → ZMod n) → V) {A : ℝ}
    (hA : ∀ y, ‖reconLow n K u y‖ ≤ A) (j : ℕ) (x : Fin d → ℝ) :
    ‖iteratedFDeriv ℝ j (reconLow n K u) x‖ ≤ (60 * d * K) ^ j * A := by
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 0)
  have hS : ∀ ℓ ∈ lowBox (d := d) n K, ∀ μ, |(ℓ μ : ℝ)| ≤ (⌊K⌋₊ : ℕ) := by
    intro ℓ hℓ μ
    rw [lowBox, Finset.mem_filter] at hℓ
    have h1 := hℓ.2 μ
    have : |(ℓ μ : ℝ)| = ((ℓ μ).natAbs : ℝ) := by rw [Nat.cast_natAbs, Int.cast_abs]
    rw [this] at h1 ⊢
    exact_mod_cast Nat.le_floor h1
  have h := norm_iteratedFDeriv_tp_le_bernstein (lowBox n K) hS j (coefOf n u) hA x
  refine h.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) ?_ j) hA0)
  have := Nat.floor_le hK
  gcongr

/-- **The reconstruction interpolates the record** (`n` odd): `z_h(h x̃) = u(x)`. -/
theorem recon_gpos (hn : Odd n) (u : (Fin d → ZMod n) → V) (x : Fin d → ZMod n) :
    recon n u (gpos n x) = u x := by
  -- the kernel `Σ_ℓ cos(ℓ·(x - y))`
  have hker : ∀ y : Fin d → ZMod n,
      ∑ ℓ ∈ box n d, (Real.cos (phase ℓ (gpos n x)) * Real.cos (phase ℓ (gpos n y)) +
        Real.sin (phase ℓ (gpos n x)) * Real.sin (phase ℓ (gpos n y))) =
      if x = y then (n : ℝ) ^ d else 0 := by
    intro y
    set k : Fin d → ℤ := fun μ => ((x μ).val : ℤ) - (y μ).val
    have hk : ∀ μ, |k μ| < n := by
      intro μ
      have h1 := ZMod.val_lt (x μ); have h2 := ZMod.val_lt (y μ)
      simp only [k]; rw [abs_lt]; constructor <;> omega
    have hk0 : k = 0 ↔ x = y := by
      constructor
      · intro h; funext μ
        have := congrFun h μ
        simp only [k, Pi.zero_apply, sub_eq_zero] at this
        exact ZMod.val_injective n (by exact_mod_cast this)
      · intro h; subst h; funext μ; simp [k]
    have hc := sum_cexp_box n hn k hk
    have hre := congrArg Complex.re hc
    rw [Complex.re_sum] at hre
    have hpt : ∀ ℓ ∈ box n d, (Complex.exp ((∑ μ, (ℓ μ : ℂ) * (2 * Real.pi * k μ / n : ℝ)) *
        Complex.I)).re = Real.cos (phase ℓ (gpos n x)) * Real.cos (phase ℓ (gpos n y)) +
          Real.sin (phase ℓ (gpos n x)) * Real.sin (phase ℓ (gpos n y)) := by
      intro ℓ _
      rw [← Real.cos_sub]
      have : (∑ μ, (ℓ μ : ℂ) * (2 * Real.pi * k μ / n : ℝ)) =
          ((phase ℓ (gpos n x) - phase ℓ (gpos n y) : ℝ) : ℂ) := by
        simp only [phase, gpos, k]; push_cast
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun μ _ => ?_
        ring
      rw [this, Complex.exp_ofReal_mul_I_re]
    rw [Finset.sum_congr rfl hpt] at hre
    rw [hre]
    by_cases hxy : x = y
    · rw [if_pos hxy, if_pos ((hk0).mpr hxy)]; norm_cast
    · rw [if_neg hxy, if_neg (fun h => hxy (hk0.mp h))]; simp
  unfold recon tp coefOf
  simp only [smul_smul, Finset.smul_sum, ← Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  have : ∀ y, ∑ ℓ ∈ box n d, ((Real.cos (phase ℓ (gpos n x)) * (((n : ℝ) ^ d)⁻¹ *
      Real.cos (phase ℓ (gpos n y)))) • u y + (Real.sin (phase ℓ (gpos n x)) * (((n : ℝ) ^ d)⁻¹ *
        Real.sin (phase ℓ (gpos n y)))) • u y) =
      (((n : ℝ) ^ d)⁻¹ * if x = y then (n : ℝ) ^ d else 0) • u y := by
    intro y
    rw [← hker y, Finset.mul_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    rw [← add_smul]; congr 1; ring
  rw [Finset.sum_congr rfl fun y _ => this y]
  rw [Finset.sum_eq_single x]
  · rw [if_pos rfl, inv_mul_cancel₀ (pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne n))), one_smul]
  · intro y _ hy; rw [if_neg (Ne.symm hy), mul_zero, zero_smul]
  · simp

end

end RenewalGeometry.TrigInterp
