/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Sobolev positive-form reader criterion
  (`cor:native-reader-sobolev`, Einstein–Standard-Model action-closure
  manuscript)

The two finite pieces of `cor:native-reader-sobolev` on the
four-dimensional Fourier mode lattice `ℤ⁴`:

* `tail_le_sqrt_latticeSum_mul_sobolev`: Parseval–Cauchy–Schwarz
  `τ_{h,j}(K;u) ≤ A_{N,K,j,q} ‖u‖_{H^q}` (`eq:app-exact-tail-sum`) with
  `τ_{h,j}(K;u) = Σ_{|ℓ|_∞>K} (1+|ℓ|₁/K)^j |û(ℓ)|`,
  `‖u‖²_{H^q} = Σ_ℓ (1+|ℓ|₂²)^q |û(ℓ)|²`;
* `latticeSum_le`: the dyadic-shell lattice bound
  `A²_{N,K,j,q} ≤ 80·25^j/(2q-2j-4) · K^{4-2q}` for `q > j+2`, from the
  shell count `#{ℓ ∈ ℤ⁴ : |ℓ|_∞ = R} ≤ 80 R³` and the integral comparison
  `Σ_{K<R≤N} R^{-s} ≤ K^{1-s}/(s-1)` (`s = 2q-2j-3 > 1`);
* `tail_le_sobolev`: the sharp-exponent transfer
  `τ_{h,j}(K;u) ≤ C_{q,j} K^{2-q} ‖u‖_{H^q}` (`eq:app-sharp-tail`);
* `sobolev_reader_criterion`: `eq:source-reader-Sobolev` — under the
  positive-form inequality `𝖱^* 𝖫^{2q} 𝖱 ⪯ C_R Q` (rendered as
  `‖𝖱 ξ‖²_{H^q} ≤ C_R ⟪ξ, Q ξ⟫`) and `‖u^{soft}‖_{H^q} ≤ C_R`, every
  legal record with `⟪ξ, Q ξ⟫ ≤ V` satisfies
  `‖u_h(x)‖_{H^q} ≤ C (1 + √V)` and
  `τ_{h,j}(K;u_h(x)) ≤ C' K^{2-q} (1 + √V)` for every `j` with
  `q > j + 2`, with explicit constants.

Modes are `ℓ : Fin 4 → ℤ`, coefficients live in a normed space `F`,
`|ℓ|_∞` is a natural number, `|ℓ|₁` and `|ℓ|₂²` are real.  The mode set
`Λ` is any finite set contained in the box `|ℓ|_∞ ≤ N`, and
`1 ≤ K ≤ N`.  The sharpness clause (shell-supported examples) is not
formalised.
-/

open scoped BigOperators

namespace RenewalGeometry
namespace SobolevReader

/-- A four-dimensional Fourier mode. -/
abbrev Mode := Fin 4 → ℤ

/-- `|ℓ|_∞`. -/
def linf (ℓ : Mode) : ℕ := Finset.univ.sup fun μ => (ℓ μ).natAbs

/-- `|ℓ|₁`. -/
noncomputable def l1 (ℓ : Mode) : ℝ := ∑ μ, |(ℓ μ : ℝ)|

/-- `|ℓ|₂²`. -/
noncomputable def l2sq (ℓ : Mode) : ℝ := ∑ μ, (ℓ μ : ℝ) ^ 2

theorem l1_nonneg (ℓ : Mode) : 0 ≤ l1 ℓ := Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem l2sq_nonneg (ℓ : Mode) : 0 ≤ l2sq ℓ := Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- `|ℓ|₁ ≤ 4 |ℓ|_∞`. -/
theorem l1_le (ℓ : Mode) : l1 ℓ ≤ 4 * (linf ℓ : ℝ) := by
  unfold l1 linf
  have h : ∀ μ ∈ (Finset.univ : Finset (Fin 4)),
      |(ℓ μ : ℝ)| ≤ ((Finset.univ.sup fun μ => (ℓ μ).natAbs : ℕ) : ℝ) := by
    intro μ _
    rw [← Int.cast_abs, ← Nat.cast_natAbs]
    exact_mod_cast Finset.le_sup (f := fun μ => (ℓ μ).natAbs) (Finset.mem_univ μ)
  calc ∑ μ, |(ℓ μ : ℝ)|
      ≤ ∑ _μ : Fin 4, ((Finset.univ.sup fun μ => (ℓ μ).natAbs : ℕ) : ℝ) := Finset.sum_le_sum h
    _ = 4 * ((Finset.univ.sup fun μ => (ℓ μ).natAbs : ℕ) : ℝ) := by simp

/-- `|ℓ|_∞² ≤ |ℓ|₂²`. -/
theorem sq_linf_le_l2sq (ℓ : Mode) : (linf ℓ : ℝ) ^ 2 ≤ l2sq ℓ := by
  obtain ⟨μ₀, _, hμ₀⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin 4))
    ⟨0, Finset.mem_univ _⟩ (fun μ => (ℓ μ).natAbs)
  have h1 : (linf ℓ : ℝ) ^ 2 = (ℓ μ₀ : ℝ) ^ 2 := by
    unfold linf
    rw [hμ₀, Nat.cast_natAbs, Int.cast_abs, sq_abs]
  rw [h1]
  unfold l2sq
  exact Finset.single_le_sum (fun μ _ => sq_nonneg ((ℓ μ : ℝ))) (Finset.mem_univ μ₀)

/-! ### The box, the shell count -/

/-- The box `{ℓ : |ℓ|_∞ ≤ r}`. -/
noncomputable def box (r : ℕ) : Finset Mode :=
  Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-(r:ℤ)) r

theorem mem_box {r : ℕ} {ℓ : Mode} : ℓ ∈ box r ↔ linf ℓ ≤ r := by
  unfold box linf
  rw [Fintype.mem_piFinset, Finset.sup_le_iff]
  constructor
  · intro h μ _
    have := h μ
    rw [Finset.mem_Icc, ← abs_le, Int.abs_eq_natAbs] at this
    exact_mod_cast this
  · intro h μ
    have := h μ (Finset.mem_univ μ)
    rw [Finset.mem_Icc, ← abs_le, Int.abs_eq_natAbs]
    exact_mod_cast this

theorem card_box (r : ℕ) : (box r).card = (2 * r + 1) ^ 4 := by
  unfold box
  rw [Fintype.card_piFinset_const, Int.card_Icc]
  congr 1
  have : ((r:ℤ) + 1 - -(r:ℤ)) = ((2 * r + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [this, Int.toNat_natCast]

theorem box_mono {r s : ℕ} (h : r ≤ s) : box r ⊆ box s := by
  intro ℓ hℓ
  rw [mem_box] at hℓ ⊢
  exact hℓ.trans h

/-- The shell `{ℓ : |ℓ|_∞ = R}`. -/
noncomputable def shell (R : ℕ) : Finset Mode := (box R).filter fun ℓ => linf ℓ = R

theorem mem_shell {R : ℕ} {ℓ : Mode} : ℓ ∈ shell R ↔ linf ℓ = R := by
  unfold shell
  rw [Finset.mem_filter, mem_box]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨h.le, h⟩

/-- **Shell count**: `#{ℓ ∈ ℤ⁴ : |ℓ|_∞ = R+1} ≤ 80 (R+1)³`. -/
theorem card_shell_le (R : ℕ) : ((shell (R + 1)).card : ℝ) ≤ 80 * ((R + 1 : ℕ) : ℝ) ^ 3 := by
  have hsub : shell (R + 1) ⊆ box (R + 1) \ box R := by
    intro ℓ hℓ
    rw [mem_shell] at hℓ
    rw [Finset.mem_sdiff, mem_box, mem_box]
    omega
  have hcard : ((box (R + 1) \ box R).card : ℝ)
      = ((2 * (R + 1) + 1 : ℕ) : ℝ) ^ 4 - ((2 * R + 1 : ℕ) : ℝ) ^ 4 := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (box_mono (Nat.le_succ R)),
      card_box, card_box]
    rw [Nat.cast_sub (Nat.pow_le_pow_left (by omega) 4)]
    push_cast
    ring
  have h1 : ((shell (R + 1)).card : ℝ) ≤ ((box (R + 1) \ box R).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  rw [hcard] at h1
  have hR : (1:ℝ) ≤ ((R + 1 : ℕ) : ℝ) := by
    push_cast
    linarith [(Nat.cast_nonneg R : (0:ℝ) ≤ R)]
  have h2 : ((2 * (R + 1) + 1 : ℕ) : ℝ) ^ 4 - ((2 * R + 1 : ℕ) : ℝ) ^ 4
      ≤ 80 * ((R + 1 : ℕ) : ℝ) ^ 3 := by
    push_cast at hR ⊢
    nlinarith [sq_nonneg ((R:ℝ) + 1), mul_nonneg (by linarith : (0:ℝ) ≤ (R:ℝ) + 1)
      (sq_nonneg ((R:ℝ) + 1))]
  linarith

/-! ### Tails, Sobolev norms and the lattice sum -/

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The weighted tail `τ_{h,j}(K;u) = Σ_{ℓ∈Λ, |ℓ|_∞>K} (1+|ℓ|₁/K)^j ‖û(ℓ)‖`
(`eq:native-tail`). -/
noncomputable def tail (Λ : Finset Mode) (j K : ℕ) (u : Mode → F) : ℝ :=
  ∑ ℓ ∈ Λ.filter (fun ℓ => K < linf ℓ), (1 + l1 ℓ / K) ^ j * ‖u ℓ‖

/-- The squared discrete Sobolev norm `‖u‖²_{H^q} = Σ_{ℓ∈Λ} (1+|ℓ|₂²)^q ‖û(ℓ)‖²`. -/
noncomputable def sobolevSq (Λ : Finset Mode) (q : ℝ) (u : Mode → F) : ℝ :=
  ∑ ℓ ∈ Λ, (1 + l2sq ℓ) ^ q * ‖u ℓ‖ ^ 2

/-- The lattice sum `A²_{N,K,j,q} = Σ_{K<|ℓ|_∞} (1+|ℓ|₁/K)^{2j} (1+|ℓ|₂²)^{-q}`
(`eq:app-exact-tail-sum`). -/
noncomputable def latticeSum (Λ : Finset Mode) (j K : ℕ) (q : ℝ) : ℝ :=
  ∑ ℓ ∈ Λ.filter (fun ℓ => K < linf ℓ), (1 + l1 ℓ / K) ^ (2 * j) * (1 + l2sq ℓ) ^ (-q)

theorem sobolevSq_nonneg (Λ : Finset Mode) (q : ℝ) (u : Mode → F) : 0 ≤ sobolevSq Λ q u :=
  Finset.sum_nonneg fun ℓ _ =>
    mul_nonneg (Real.rpow_nonneg (by linarith [l2sq_nonneg ℓ]) _) (sq_nonneg _)

theorem latticeSum_nonneg (Λ : Finset Mode) (j K : ℕ) (q : ℝ) : 0 ≤ latticeSum Λ j K q :=
  Finset.sum_nonneg fun ℓ _ =>
    mul_nonneg (pow_nonneg (by have := l1_nonneg ℓ; positivity) _)
      (Real.rpow_nonneg (by linarith [l2sq_nonneg ℓ]) _)

/-- **Parseval–Cauchy–Schwarz** (`eq:app-exact-tail-sum`):
`τ_{h,j}(K;u) ≤ A_{N,K,j,q} ‖u‖_{H^q}`. -/
theorem tail_le_sqrt_latticeSum_mul_sobolev (Λ : Finset Mode) (j K : ℕ) (q : ℝ)
    (u : Mode → F) :
    tail Λ j K u ≤ Real.sqrt (latticeSum Λ j K q) * Real.sqrt (sobolevSq Λ q u) := by
  set Λ' := Λ.filter (fun ℓ => K < linf ℓ) with hΛ'
  have hpos : ∀ ℓ : Mode, 0 < 1 + l2sq ℓ := fun ℓ => by linarith [l2sq_nonneg ℓ]
  -- split the summand as a product
  have hsplit : ∀ ℓ ∈ Λ', (1 + l1 ℓ / K) ^ j * ‖u ℓ‖
      = ((1 + l1 ℓ / K) ^ j * (1 + l2sq ℓ) ^ (-q / 2))
        * ((1 + l2sq ℓ) ^ (q / 2) * ‖u ℓ‖) := by
    intro ℓ _
    have : (1 + l2sq ℓ) ^ (-q / 2) * (1 + l2sq ℓ) ^ (q / 2) = 1 := by
      rw [← Real.rpow_add (hpos ℓ)]
      rw [show -q / 2 + q / 2 = 0 by ring, Real.rpow_zero]
    calc (1 + l1 ℓ / K) ^ j * ‖u ℓ‖
        = (1 + l1 ℓ / K) ^ j * ((1 + l2sq ℓ) ^ (-q / 2) * (1 + l2sq ℓ) ^ (q / 2)) * ‖u ℓ‖ := by
          rw [this, mul_one]
      _ = _ := by ring
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt Λ'
    (fun ℓ => (1 + l1 ℓ / K) ^ j * (1 + l2sq ℓ) ^ (-q / 2))
    (fun ℓ => (1 + l2sq ℓ) ^ (q / 2) * ‖u ℓ‖)
  have hL : tail Λ j K u = ∑ ℓ ∈ Λ',
      ((1 + l1 ℓ / K) ^ j * (1 + l2sq ℓ) ^ (-q / 2)) * ((1 + l2sq ℓ) ^ (q / 2) * ‖u ℓ‖) :=
    Finset.sum_congr rfl hsplit
  have hA : ∑ ℓ ∈ Λ', ((1 + l1 ℓ / K) ^ j * (1 + l2sq ℓ) ^ (-q / 2)) ^ 2
      = latticeSum Λ j K q := by
    unfold latticeSum
    apply Finset.sum_congr rfl
    intro ℓ _
    rw [mul_pow, ← pow_mul, mul_comm j 2, ← Real.rpow_natCast ((1 + l2sq ℓ) ^ (-q / 2)),
      ← Real.rpow_mul (hpos ℓ).le]
    congr 2
    push_cast
    ring
  have hB : ∑ ℓ ∈ Λ', ((1 + l2sq ℓ) ^ (q / 2) * ‖u ℓ‖) ^ 2 ≤ sobolevSq Λ q u := by
    unfold sobolevSq
    have heq : ∀ ℓ, ((1 + l2sq ℓ) ^ (q / 2) * ‖u ℓ‖) ^ 2 = (1 + l2sq ℓ) ^ q * ‖u ℓ‖ ^ 2 := by
      intro ℓ
      rw [mul_pow, ← Real.rpow_natCast ((1 + l2sq ℓ) ^ (q / 2)), ← Real.rpow_mul (hpos ℓ).le]
      congr 2
      push_cast
      ring
    simp_rw [heq]
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro ℓ _ _
    exact mul_nonneg (Real.rpow_nonneg (hpos ℓ).le _) (sq_nonneg _)
  rw [hL]
  refine hcs.trans ?_
  rw [hA]
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hB) (Real.sqrt_nonneg _)

/-! ### The shell estimate -/

/-- Pointwise bound on a shell `|ℓ|_∞ = R` with `1 ≤ K ≤ R`. -/
theorem shell_term_le {ℓ : Mode} {R K : ℕ} (hℓ : linf ℓ = R) (hK : 1 ≤ K) (hKR : K ≤ R)
    (j : ℕ) (q : ℝ) (hq : 0 ≤ q) :
    (1 + l1 ℓ / K) ^ (2 * j) * (1 + l2sq ℓ) ^ (-q)
      ≤ (5 * (R:ℝ) / K) ^ (2 * j) * (((R:ℝ) ^ 2) ^ (-q)) := by
  have hKpos : (0:ℝ) < K := by exact_mod_cast hK
  have hKR' : (K:ℝ) ≤ R := by exact_mod_cast hKR
  have hRpos : (0:ℝ) < R := lt_of_lt_of_le hKpos hKR'
  have h1 : 1 + l1 ℓ / K ≤ 5 * (R:ℝ) / K := by
    have hl1 := l1_le ℓ
    rw [hℓ] at hl1
    have hRK : (1:ℝ) ≤ R / K := by rw [le_div_iff₀ hKpos]; linarith
    have : l1 ℓ / K ≤ 4 * (R:ℝ) / K := by
      apply div_le_div_of_nonneg_right hl1 hKpos.le
    calc 1 + l1 ℓ / K ≤ R / K + 4 * (R:ℝ) / K := by linarith
      _ = 5 * (R:ℝ) / K := by ring
  have h2 : (1 + l2sq ℓ) ^ (-q) ≤ ((R:ℝ) ^ 2) ^ (-q) := by
    apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by linarith)
    have := sq_linf_le_l2sq ℓ
    rw [hℓ] at this
    linarith
  apply mul_le_mul _ h2 (Real.rpow_nonneg (by linarith [l2sq_nonneg ℓ]) _) (by positivity)
  exact pow_le_pow_left₀ (by have := l1_nonneg ℓ; positivity) h1 _

/-- The shell bound rewritten in exponent form:
`80 R³ (5R/K)^{2j} (R²)^{-q} = 80·25^j K^{-2j} R^{-(2q-2j-3)}`. -/
theorem shell_bound_eq {R K : ℝ} (hR : 0 < R) (hK : 0 < K) (j : ℕ) (q : ℝ) :
    80 * R ^ 3 * ((5 * R / K) ^ (2 * j) * ((R ^ 2) ^ (-q)))
      = 80 * 25 ^ j * K ^ (-(2 * (j:ℝ))) * R ^ (-(2 * q - 2 * j - 3)) := by
  have hA : (R ^ 2) ^ (-q) = R ^ (-(2 * q)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hR.le]
    congr 1
    push_cast
    ring
  have hB : K ^ (-(2 * (j:ℝ))) = (K ^ (2 * j))⁻¹ := by
    rw [Real.rpow_neg hK.le]
    congr 1
    rw [← Real.rpow_natCast]
    congr 1
    push_cast
    ring
  have hC : R ^ (-(2 * q - 2 * j - 3)) = R ^ 3 * R ^ (2 * j) * R ^ (-(2 * q)) := by
    rw [show -(2 * q - 2 * (j:ℝ) - 3) = ((3 + 2 * j : ℕ) : ℝ) + -(2 * q) by push_cast; ring,
      Real.rpow_add hR, Real.rpow_natCast, pow_add]
  rw [hA, hB, hC]
  have hK0 : K ^ (2 * j) ≠ 0 := pow_ne_zero _ hK.ne'
  rw [div_pow, mul_pow, show (5:ℝ) ^ (2 * j) = 25 ^ j by rw [pow_mul]; norm_num]
  field_simp

/-- **Grouping into shells**: the lattice sum over `Λ ⊆ {|ℓ|_∞ ≤ N}` is
bounded by the shell sums `Σ_{K<R≤N} 80 R³ · (5R/K)^{2j} (R²)^{-q}`. -/
theorem latticeSum_le_shell_sum (Λ : Finset Mode) (j K N : ℕ) (q : ℝ) (hq : 0 ≤ q)
    (hK : 1 ≤ K) (hΛ : ∀ ℓ ∈ Λ, linf ℓ ≤ N) :
    latticeSum Λ j K q
      ≤ ∑ i ∈ Finset.Ico K N, 80 * ((i + 1 : ℕ) : ℝ) ^ 3
          * ((5 * ((i + 1 : ℕ) : ℝ) / K) ^ (2 * j) * ((((i + 1 : ℕ) : ℝ) ^ 2) ^ (-q))) := by
  unfold latticeSum
  set Λ' := Λ.filter (fun ℓ => K < linf ℓ) with hΛ'
  set f : Mode → ℝ := fun ℓ => (1 + l1 ℓ / K) ^ (2 * j) * (1 + l2sq ℓ) ^ (-q) with hf
  have hfnn : ∀ ℓ, 0 ≤ f ℓ := fun ℓ =>
    mul_nonneg (pow_nonneg (by have := l1_nonneg ℓ; positivity) _)
      (Real.rpow_nonneg (by linarith [l2sq_nonneg ℓ]) _)
  have hmaps : ∀ ℓ ∈ Λ', linf ℓ - 1 ∈ Finset.Ico K N := by
    intro ℓ hℓ
    rw [hΛ', Finset.mem_filter] at hℓ
    have := hΛ ℓ hℓ.1
    rw [Finset.mem_Ico]
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps f]
  apply Finset.sum_le_sum
  intro i hi
  rw [Finset.mem_Ico] at hi
  -- the fibre is contained in the shell `i+1`
  have hsub : Λ'.filter (fun ℓ => linf ℓ - 1 = i) ⊆ shell (i + 1) := by
    intro ℓ hℓ
    rw [Finset.mem_filter, hΛ', Finset.mem_filter] at hℓ
    rw [mem_shell]
    omega
  have hbound : ∀ ℓ ∈ shell (i + 1), f ℓ
      ≤ (5 * ((i + 1 : ℕ) : ℝ) / K) ^ (2 * j) * ((((i + 1 : ℕ) : ℝ) ^ 2) ^ (-q)) := by
    intro ℓ hℓ
    rw [mem_shell] at hℓ
    exact shell_term_le hℓ hK (by omega) j q hq
  calc ∑ ℓ ∈ Λ'.filter (fun ℓ => linf ℓ - 1 = i), f ℓ
      ≤ ∑ ℓ ∈ shell (i + 1), f ℓ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun ℓ _ _ => hfnn ℓ)
    _ ≤ (shell (i + 1)).card •
          ((5 * ((i + 1 : ℕ) : ℝ) / K) ^ (2 * j) * ((((i + 1 : ℕ) : ℝ) ^ 2) ^ (-q))) :=
        Finset.sum_le_card_nsmul _ _ _ hbound
    _ ≤ _ := by
        rw [nsmul_eq_mul]
        apply mul_le_mul_of_nonneg_right (card_shell_le i)
        positivity

/-- **Integral comparison**: `Σ_{i ∈ Ico K N} (i+1)^{-s} ≤ K^{1-s}/(s-1)` for
`s > 1` and `1 ≤ K ≤ N`. -/
theorem sum_rpow_neg_le {K N : ℕ} (hK : 1 ≤ K) (hKN : K ≤ N) {s : ℝ} (hs : 1 < s) :
    ∑ i ∈ Finset.Ico K N, ((i + 1 : ℕ) : ℝ) ^ (-s) ≤ (K:ℝ) ^ (1 - s) / (s - 1) := by
  have hKpos : (0:ℝ) < K := by exact_mod_cast hK
  have hKN' : (K:ℝ) ≤ N := by exact_mod_cast hKN
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-s)) (Set.Icc (K:ℝ) N) := by
    apply (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by linarith)).mono
    intro x hx
    exact lt_of_lt_of_le hKpos hx.1
  have hint := AntitoneOn.sum_le_integral_Ico hKN hanti
  have hval : ∫ x in (K:ℝ)..N, x ^ (-s) = ((N:ℝ) ^ (-s + 1) - (K:ℝ) ^ (-s + 1)) / (-s + 1) := by
    apply integral_rpow
    right
    refine ⟨by linarith, ?_⟩
    rw [Set.uIcc_of_le hKN']
    intro h
    linarith [h.1]
  rw [hval] at hint
  have hNnn : 0 ≤ (N:ℝ) ^ (-s + 1) := Real.rpow_nonneg (by linarith) _
  have hden : 0 < s - 1 := by linarith
  have h2 : ((N:ℝ) ^ (-s + 1) - (K:ℝ) ^ (-s + 1)) / (-s + 1)
      = ((K:ℝ) ^ (-s + 1) - (N:ℝ) ^ (-s + 1)) / (s - 1) := by
    rw [show (-s + 1) = -(s - 1) by ring, div_neg, neg_div', neg_sub]
  rw [h2] at hint
  rw [show (1 - s) = -s + 1 by ring]
  refine hint.trans ?_
  apply div_le_div_of_nonneg_right _ hden.le
  linarith

/-- **The lattice bound** (`app:native-reader-proof`):
`A²_{N,K,j,q} ≤ 80·25^j/(2q-2j-4) · K^{4-2q}` for `q > j+2`, `1 ≤ K ≤ N`. -/
theorem latticeSum_le (Λ : Finset Mode) (j K N : ℕ) (q : ℝ) (hq : (j:ℝ) + 2 < q)
    (hK : 1 ≤ K) (hKN : K ≤ N) (hΛ : ∀ ℓ ∈ Λ, linf ℓ ≤ N) :
    latticeSum Λ j K q ≤ 80 * 25 ^ j / (2 * q - 2 * j - 4) * (K:ℝ) ^ (4 - 2 * q) := by
  have hq0 : 0 ≤ q := by linarith [(Nat.cast_nonneg j : (0:ℝ) ≤ j)]
  have hKpos : (0:ℝ) < K := by exact_mod_cast hK
  refine (latticeSum_le_shell_sum Λ j K N q hq0 hK hΛ).trans ?_
  set s := 2 * q - 2 * (j:ℝ) - 3 with hs
  have hs1 : 1 < s := by rw [hs]; linarith
  have hrw : ∀ i ∈ Finset.Ico K N,
      80 * ((i + 1 : ℕ) : ℝ) ^ 3
          * ((5 * ((i + 1 : ℕ) : ℝ) / K) ^ (2 * j) * ((((i + 1 : ℕ) : ℝ) ^ 2) ^ (-q)))
        = 80 * 25 ^ j * (K:ℝ) ^ (-(2 * (j:ℝ))) * ((i + 1 : ℕ) : ℝ) ^ (-s) := by
    intro i _
    rw [shell_bound_eq (by positivity) hKpos j q]
  rw [Finset.sum_congr rfl hrw, ← Finset.mul_sum]
  have hsum := sum_rpow_neg_le hK hKN hs1
  have hcoef : 0 ≤ 80 * 25 ^ j * (K:ℝ) ^ (-(2 * (j:ℝ))) := by positivity
  calc 80 * 25 ^ j * (K:ℝ) ^ (-(2 * (j:ℝ))) * ∑ i ∈ Finset.Ico K N, ((i + 1 : ℕ) : ℝ) ^ (-s)
      ≤ 80 * 25 ^ j * (K:ℝ) ^ (-(2 * (j:ℝ))) * ((K:ℝ) ^ (1 - s) / (s - 1)) :=
        mul_le_mul_of_nonneg_left hsum hcoef
    _ = 80 * 25 ^ j / (2 * q - 2 * j - 4) * (K:ℝ) ^ (4 - 2 * q) := by
        rw [show (K:ℝ) ^ (4 - 2 * q) = (K:ℝ) ^ (-(2 * (j:ℝ))) * (K:ℝ) ^ (1 - s) by
          rw [← Real.rpow_add hKpos]; congr 1; rw [hs]; ring]
        rw [show s - 1 = 2 * q - 2 * j - 4 by rw [hs]; ring]
        field_simp

/-- **`eq:app-sharp-tail`**: for `q > j + 2` and `1 ≤ K ≤ N`,
`τ_{h,j}(K;u) ≤ C_{q,j} K^{2-q} ‖u‖_{H^q}` with
`C_{q,j} = √(80·25^j/(2q-2j-4))`. -/
theorem tail_le_sobolev (Λ : Finset Mode) (j K N : ℕ) (q : ℝ) (hq : (j:ℝ) + 2 < q)
    (hK : 1 ≤ K) (hKN : K ≤ N) (hΛ : ∀ ℓ ∈ Λ, linf ℓ ≤ N) (u : Mode → F) :
    tail Λ j K u
      ≤ Real.sqrt (80 * 25 ^ j / (2 * q - 2 * j - 4)) * (K:ℝ) ^ (2 - q)
          * Real.sqrt (sobolevSq Λ q u) := by
  have hKpos : (0:ℝ) < K := by exact_mod_cast hK
  refine (tail_le_sqrt_latticeSum_mul_sobolev Λ j K q u).trans ?_
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  have h1 := Real.sqrt_le_sqrt (latticeSum_le Λ j K N q hq hK hKN hΛ)
  refine h1.trans (le_of_eq ?_)
  rw [Real.sqrt_mul (by
    have : 0 < 2 * q - 2 * (j:ℝ) - 4 := by linarith
    positivity)]
  congr 1
  rw [show (4 - 2 * q) = (2 - q) * 2 by ring, Real.rpow_mul hKpos.le, Real.rpow_two,
    Real.sqrt_sq (Real.rpow_nonneg hKpos.le _)]

/-! ### The `H^q` bound from the positive form -/

/-- Minkowski's inequality for the weighted `ℓ²` Sobolev norm. -/
theorem sqrt_sobolevSq_add_le (Λ : Finset Mode) (q : ℝ) (u v : Mode → F) :
    Real.sqrt (sobolevSq Λ q (u + v))
      ≤ Real.sqrt (sobolevSq Λ q u) + Real.sqrt (sobolevSq Λ q v) := by
  have hw : ∀ ℓ : Mode, 0 ≤ (1 + l2sq ℓ) ^ q :=
    fun ℓ => Real.rpow_nonneg (by linarith [l2sq_nonneg ℓ]) _
  set A := Real.sqrt (sobolevSq Λ q u) with hA
  set B := Real.sqrt (sobolevSq Λ q v) with hB
  have hA2 : A ^ 2 = sobolevSq Λ q u := Real.sq_sqrt (sobolevSq_nonneg _ _ _)
  have hB2 : B ^ 2 = sobolevSq Λ q v := Real.sq_sqrt (sobolevSq_nonneg _ _ _)
  -- cross term by Cauchy–Schwarz
  have hcross : ∑ ℓ ∈ Λ, (1 + l2sq ℓ) ^ q * (‖u ℓ‖ * ‖v ℓ‖) ≤ A * B := by
    have hcs := Real.sum_mul_le_sqrt_mul_sqrt Λ
      (fun ℓ => Real.sqrt ((1 + l2sq ℓ) ^ q) * ‖u ℓ‖)
      (fun ℓ => Real.sqrt ((1 + l2sq ℓ) ^ q) * ‖v ℓ‖)
    have heq : ∀ ℓ ∈ Λ, (1 + l2sq ℓ) ^ q * (‖u ℓ‖ * ‖v ℓ‖)
        = (Real.sqrt ((1 + l2sq ℓ) ^ q) * ‖u ℓ‖) * (Real.sqrt ((1 + l2sq ℓ) ^ q) * ‖v ℓ‖) := by
      intro ℓ _
      have := Real.mul_self_sqrt (hw ℓ)
      calc (1 + l2sq ℓ) ^ q * (‖u ℓ‖ * ‖v ℓ‖)
          = (Real.sqrt ((1 + l2sq ℓ) ^ q) * Real.sqrt ((1 + l2sq ℓ) ^ q)) * (‖u ℓ‖ * ‖v ℓ‖) := by
            rw [this]
        _ = _ := by ring
    have hsu : ∑ ℓ ∈ Λ, (Real.sqrt ((1 + l2sq ℓ) ^ q) * ‖u ℓ‖) ^ 2 = sobolevSq Λ q u := by
      unfold sobolevSq
      apply Finset.sum_congr rfl
      intro ℓ _
      rw [mul_pow, Real.sq_sqrt (hw ℓ)]
    have hsv : ∑ ℓ ∈ Λ, (Real.sqrt ((1 + l2sq ℓ) ^ q) * ‖v ℓ‖) ^ 2 = sobolevSq Λ q v := by
      unfold sobolevSq
      apply Finset.sum_congr rfl
      intro ℓ _
      rw [mul_pow, Real.sq_sqrt (hw ℓ)]
    rw [Finset.sum_congr rfl heq]
    rw [hsu, hsv] at hcs
    exact hcs
  have hsum : sobolevSq Λ q (u + v) ≤ A ^ 2 + 2 * (A * B) + B ^ 2 := by
    rw [hA2, hB2]
    unfold sobolevSq
    have hpt : ∀ ℓ ∈ Λ, (1 + l2sq ℓ) ^ q * ‖(u + v) ℓ‖ ^ 2
        ≤ (1 + l2sq ℓ) ^ q * ‖u ℓ‖ ^ 2 + 2 * ((1 + l2sq ℓ) ^ q * (‖u ℓ‖ * ‖v ℓ‖))
          + (1 + l2sq ℓ) ^ q * ‖v ℓ‖ ^ 2 := by
      intro ℓ _
      have htri : ‖(u + v) ℓ‖ ≤ ‖u ℓ‖ + ‖v ℓ‖ := norm_add_le _ _
      have hsq : ‖(u + v) ℓ‖ ^ 2 ≤ (‖u ℓ‖ + ‖v ℓ‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) htri 2
      have := mul_le_mul_of_nonneg_left hsq (hw ℓ)
      nlinarith
    have := Finset.sum_le_sum hpt
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at this
    linarith
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  calc sobolevSq Λ q (u + v) ≤ A ^ 2 + 2 * (A * B) + B ^ 2 := hsum
    _ = (A + B) ^ 2 := by ring

/-- **`cor:native-reader-sobolev`, `eq:source-reader-Sobolev`.**  Let the
source space be a finite-dimensional real inner-product space `H` with
native energy form `Q`, let the affine physical reader
`u_h(x) = u^{soft} + 𝖱 ξ` have Fourier coefficients `u₀ + R ξ` with `R`
linear, and assume the positive-form inequality
`𝖱^* 𝖫^{2q} 𝖱 ⪯ C_R Q` (`‖R ξ‖²_{H^q} ≤ C_R ⟪ξ, Q ξ⟫`) together with
`‖u^{soft}‖_{H^q} ≤ C_R`.  Then for every record with `⟪ξ, Q ξ⟫ ≤ V`,
`‖u_h(x)‖_{H^q} ≤ max(C_R, √C_R) (1 + √V)`, and for every `j` with
`q > j + 2` and `1 ≤ K ≤ N`,
`τ_{h,j}(K;u_h(x)) ≤ C_{q,j} max(C_R, √C_R) K^{2-q} (1 + √V)`. -/
theorem sobolev_reader_criterion
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Q : H →ₗ[ℝ] H) (R : H →ₗ[ℝ] (Mode → F)) (u₀ : Mode → F)
    (Λ : Finset Mode) (N : ℕ) (hΛ : ∀ ℓ ∈ Λ, linf ℓ ≤ N)
    (q C_R : ℝ) (hC : 0 ≤ C_R)
    (hLMI : ∀ ξ, sobolevSq Λ q (R ξ) ≤ C_R * inner ℝ ξ (Q ξ))
    (hsoft : Real.sqrt (sobolevSq Λ q u₀) ≤ C_R)
    (ξ : H) (V : ℝ) (hξ : inner ℝ ξ (Q ξ) ≤ V) :
    Real.sqrt (sobolevSq Λ q (u₀ + R ξ)) ≤ max C_R (Real.sqrt C_R) * (1 + Real.sqrt V) ∧
    ∀ (j K : ℕ), (j:ℝ) + 2 < q → 1 ≤ K → K ≤ N →
      tail Λ j K (u₀ + R ξ)
        ≤ Real.sqrt (80 * 25 ^ j / (2 * q - 2 * j - 4)) * max C_R (Real.sqrt C_R)
            * (K:ℝ) ^ (2 - q) * (1 + Real.sqrt V) := by
  have hHq : Real.sqrt (sobolevSq Λ q (u₀ + R ξ))
      ≤ max C_R (Real.sqrt C_R) * (1 + Real.sqrt V) := by
    have h1 := sqrt_sobolevSq_add_le Λ q u₀ (R ξ)
    have h2 : Real.sqrt (sobolevSq Λ q (R ξ)) ≤ Real.sqrt C_R * Real.sqrt V := by
      rw [← Real.sqrt_mul hC]
      apply Real.sqrt_le_sqrt
      exact (hLMI ξ).trans (mul_le_mul_of_nonneg_left hξ hC)
    have hm1 : C_R ≤ max C_R (Real.sqrt C_R) := le_max_left _ _
    have hm2 : Real.sqrt C_R ≤ max C_R (Real.sqrt C_R) := le_max_right _ _
    have hsV : 0 ≤ Real.sqrt V := Real.sqrt_nonneg _
    calc Real.sqrt (sobolevSq Λ q (u₀ + R ξ))
        ≤ Real.sqrt (sobolevSq Λ q u₀) + Real.sqrt (sobolevSq Λ q (R ξ)) := h1
      _ ≤ C_R + Real.sqrt C_R * Real.sqrt V := add_le_add hsoft h2
      _ ≤ max C_R (Real.sqrt C_R) + max C_R (Real.sqrt C_R) * Real.sqrt V := by
          gcongr
      _ = max C_R (Real.sqrt C_R) * (1 + Real.sqrt V) := by ring
  refine ⟨hHq, ?_⟩
  intro j K hq hK hKN
  have hKpos : (0:ℝ) < K := by exact_mod_cast hK
  have ht := tail_le_sobolev Λ j K N q hq hK hKN hΛ (u₀ + R ξ)
  refine ht.trans ?_
  have hc : 0 ≤ Real.sqrt (80 * 25 ^ j / (2 * q - 2 * j - 4)) * (K:ℝ) ^ (2 - q) := by
    positivity
  calc Real.sqrt (80 * 25 ^ j / (2 * q - 2 * j - 4)) * (K:ℝ) ^ (2 - q)
        * Real.sqrt (sobolevSq Λ q (u₀ + R ξ))
      ≤ Real.sqrt (80 * 25 ^ j / (2 * q - 2 * j - 4)) * (K:ℝ) ^ (2 - q)
        * (max C_R (Real.sqrt C_R) * (1 + Real.sqrt V)) := mul_le_mul_of_nonneg_left hHq hc
    _ = _ := by ring

end SobolevReader
end RenewalGeometry
