/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.DiscreteAnalysis.LatticeTorusPlancherel

/-!
# Uniform discrete Sobolev calculus on the periodic grid `(ℤ/N)³`
  (`lem:supp-open-calculus`, `eq:supp-open-adjoints`, `eq:supp-open-shifted-product`,
  `eq:supp-open-norms`, `eq:supp-open-commutator`, `eq:supp-open-commutator-bounds`;
  emergent-spacetime manuscript, supplement)

On the periodic grid `Λ_h = (ℤ/N)³` with mesh `h = 1/N` and complex-valued arrays:

* shifts `S_i`, `S_i⁻¹` and the differences `D_i⁺ = (S_i - I)/h`, `D_i⁻ = (I - S_i⁻¹)/h`,
  `D_i⁰ = (D_i⁺ + D_i⁻)/2` (`eq:main-open-differences`) as linear maps;
* the grid inner product `⟨u, v⟩_h = h³ Σ_x conj(u x) v x` and the adjoint identities
  `(D_i⁺)* = -D_i⁻`, `(D_i⁰)* = -D_i⁰` (`gridInner_Dp_left`, `gridInner_D0_left`);
* the exact shifted product rule `D^α(f w) = Σ_{β ≤ α} binom(α, β)(S^{α-β} D^β f) D^{α-β} w`
  (`Dα_mul`), via the one-direction Leibniz rule `Dp_pow_mul`;
* Fourier inversion, the convolution theorem (`dft_mul`) and the multiplier calculus
  (`IsMult`) for the normalised DFT of `LatticeTorusPlancherel`, with symbols
  `d_i(k) = (e^{2πi h k_i} - 1)/h` and the uniform comparison
  `4|k_i| ≤ |d_i(k)| ≤ 2π|k_i|` on the signed frequency cube (`four_mul_le_norm_sym`,
  `norm_sym_le`);
* the grid Sobolev norms `‖u‖²_{r,h} = Σ_{|α| ≤ r} ‖D^α u‖_h²` (`sobSq`, `eq:supp-open-norms`)
  and their Fourier form (`sobSq_eq_weight`);
* the uniform weighted-convolution estimate (`conv_bound`) with the `N`-independent constant
  `K = 2 c₁³`, `c₁ = Σ_{n ∈ ℤ} (1 + 16 n²)^{-2/3}`, giving the bilinear bounds
  `‖ab‖_h² ≤ K ‖a‖²_{1,h}‖b‖²_{1,h}` and `‖ab‖_h² ≤ K ‖a‖²_{2,h}‖b‖_h²` (a uniform discrete
  `H² ⊂ L^∞`);
* the uniform product algebra for `r ≥ 2` (`sobSq_mul_le`) and both commutator bounds of
  `eq:supp-open-commutator-bounds` for `r ≥ 3`, `|α| ≤ r` and constant `f_*`
  (`commutator_norm_le`, `commutator_diff_norm_le`), packaged with one `N`-independent constant
  in `uniform_sobolev_calculus`.

The uniform equivalence with the trigonometric `H^r` norms of the interpolant is in
`PeriodicGridInterpolation`.
-/

open Finset ComplexConjugate
open scoped BigOperators Real

namespace RenewalGeometry.PeriodicGridSobolev

open LatticeTorusPlancherel

/-- The periodic grid `Λ_h = (ℤ/N)³` (mesh `h = 1/N`). -/
abbrev Grid (N : ℕ) := LatticeTorusPlancherel.Grid 3 N

set_option linter.unusedSectionVars false

variable {N : ℕ} [NeZero N]

/-- The unit step `e_i` on the grid. -/
def unit (i : Fin 3) : Grid N := Pi.single i 1

/-- The coordinate shift `(S_i u)(x) = u(x + e_i)`. -/
noncomputable def S (i : Fin 3) : Module.End ℂ (Grid N → ℂ) :=
  LinearMap.funLeft ℂ ℂ (fun x : Grid N => x + unit i)

/-- The inverse shift `(S_i⁻¹ u)(x) = u(x - e_i)`. -/
noncomputable def Sinv (i : Fin 3) : Module.End ℂ (Grid N → ℂ) :=
  LinearMap.funLeft ℂ ℂ (fun x : Grid N => x - unit i)

@[simp] theorem S_apply (i : Fin 3) (u : Grid N → ℂ) (x : Grid N) :
    S i u x = u (x + unit i) := rfl

@[simp] theorem Sinv_apply (i : Fin 3) (u : Grid N → ℂ) (x : Grid N) :
    Sinv i u x = u (x - unit i) := rfl

/-- Forward difference `D_i⁺ = (S_i - I)/h`, `h = 1/N`. -/
noncomputable def Dp (i : Fin 3) : Module.End ℂ (Grid N → ℂ) := (N : ℂ) • (S i - 1)

/-- Backward difference `D_i⁻ = (I - S_i⁻¹)/h`. -/
noncomputable def Dm (i : Fin 3) : Module.End ℂ (Grid N → ℂ) := (N : ℂ) • (1 - Sinv i)

/-- Central difference `D_i⁰ = (D_i⁺ + D_i⁻)/2`. -/
noncomputable def D0 (i : Fin 3) : Module.End ℂ (Grid N → ℂ) := (2 : ℂ)⁻¹ • (Dp i + Dm i)

theorem Dp_apply (i : Fin 3) (u : Grid N → ℂ) (x : Grid N) :
    Dp i u x = N * (u (x + unit i) - u x) := by
  simp [Dp]

theorem Dm_apply (i : Fin 3) (u : Grid N → ℂ) (x : Grid N) :
    Dm i u x = N * (u x - u (x - unit i)) := by
  simp [Dm]

theorem D0_apply (i : Fin 3) (u : Grid N → ℂ) (x : Grid N) :
    D0 i u x = (2 : ℂ)⁻¹ * (Dp i u x + Dm i u x) := by
  simp [D0, mul_add]

/-- The grid inner product `⟨u, v⟩_h = h³ Σ_x conj(u x) v x`. -/
noncomputable def gridInner (u v : Grid N → ℂ) : ℂ :=
  ((N : ℂ) ^ 3)⁻¹ * ∑ x, conj (u x) * v x

theorem sum_shift_reindex (f : Grid N → ℂ) (a : Grid N) :
    ∑ x, f (x + a) = ∑ x, f x :=
  Fintype.sum_equiv (Equiv.addRight a) _ _ (fun _ => rfl)

theorem sum_conj_shift (u v : Grid N → ℂ) (a : Grid N) :
    ∑ x, conj (u (x + a)) * v x = ∑ x, conj (u x) * v (x - a) := by
  rw [← sum_shift_reindex (fun x => conj (u x) * v (x - a)) a]
  simp

/-- `eq:supp-open-adjoints`: `(D_i⁺)* = -D_i⁻`. -/
theorem gridInner_Dp_left (i : Fin 3) (u v : Grid N → ℂ) :
    gridInner (Dp i u) v = - gridInner u (Dm i v) := by
  unfold gridInner
  simp only [Dp_apply, Dm_apply, map_mul, map_sub, map_natCast]
  have h1 := sum_conj_shift u v (unit i)
  have e1 : ∑ x, (N : ℂ) * (conj (u (x + unit i)) - conj (u x)) * v x =
      (N : ℂ) * (∑ x, conj (u (x + unit i)) * v x - ∑ x, conj (u x) * v x) := by
    rw [mul_sub, mul_sum, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun x _ => by ring
  have e2 : ∑ x, conj (u x) * ((N : ℂ) * (v x - v (x - unit i))) =
      (N : ℂ) * (∑ x, conj (u x) * v x - ∑ x, conj (u x) * v (x - unit i)) := by
    rw [mul_sub, mul_sum, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun x _ => by ring
  rw [e1, e2, h1]
  ring

/-- `(D_i⁻)* = -D_i⁺`. -/
theorem gridInner_Dm_left (i : Fin 3) (u v : Grid N → ℂ) :
    gridInner (Dm i u) v = - gridInner u (Dp i v) := by
  unfold gridInner
  simp only [Dp_apply, Dm_apply, map_mul, map_sub, map_natCast]
  have h1 : ∑ x, conj (u (x - unit i)) * v x = ∑ x, conj (u x) * v (x + unit i) := by
    rw [← sum_shift_reindex (fun x => conj (u (x - unit i)) * v x) (unit i)]
    simp
  have e1 : ∑ x, (N : ℂ) * (conj (u x) - conj (u (x - unit i))) * v x =
      (N : ℂ) * (∑ x, conj (u x) * v x - ∑ x, conj (u (x - unit i)) * v x) := by
    rw [mul_sub, mul_sum, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun x _ => by ring
  have e2 : ∑ x, conj (u x) * ((N : ℂ) * (v (x + unit i) - v x)) =
      (N : ℂ) * (∑ x, conj (u x) * v (x + unit i) - ∑ x, conj (u x) * v x) := by
    rw [mul_sub, mul_sum, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun x _ => by ring
  rw [e1, e2, h1]
  ring

/-- `eq:supp-open-adjoints`: `(D_i⁰)* = -D_i⁰`. -/
theorem gridInner_D0_left (i : Fin 3) (u v : Grid N → ℂ) :
    gridInner (D0 i u) v = - gridInner u (D0 i v) := by
  have hl : gridInner (D0 i u) v = (2 : ℂ)⁻¹ * (gridInner (Dp i u) v + gridInner (Dm i u) v) := by
    unfold gridInner
    simp only [D0_apply, map_mul, map_add, map_inv₀, map_ofNat]
    rw [← mul_add, ← sum_add_distrib]
    simp only [mul_sum]
    refine sum_congr rfl fun x _ => by ring
  have hr : gridInner u (D0 i v) = (2 : ℂ)⁻¹ * (gridInner u (Dp i v) + gridInner u (Dm i v)) := by
    unfold gridInner
    simp only [D0_apply]
    rw [← mul_add, ← sum_add_distrib]
    simp only [mul_sum]
    refine sum_congr rfl fun x _ => by ring
  rw [hl, hr, gridInner_Dp_left, gridInner_Dm_left]
  ring

/-! ### The shifted product rule -/

/-- One-step shifted product rule `D_i⁺(f w) = (S_i f) D_i⁺ w + (D_i⁺ f) w`. -/
theorem Dp_mul (i : Fin 3) (f w : Grid N → ℂ) :
    Dp i (f * w) = S i f * Dp i w + Dp i f * w := by
  funext x
  simp only [Dp_apply, Pi.mul_apply, Pi.add_apply, S_apply]
  ring

theorem S_mul (i : Fin 3) (f w : Grid N → ℂ) : S i (f * w) = S i f * S i w := rfl

theorem S_Dp_comm (i j : Fin 3) : S i * Dp j = Dp j * (S i : Module.End ℂ (Grid N → ℂ)) := by
  apply LinearMap.ext; intro u; funext x
  simp only [Module.End.mul_apply, S_apply, Dp_apply]
  rw [add_right_comm]

theorem S_pow_Dp_pow_comm (i j : Fin 3) (a b : ℕ) :
    (S i ^ a) * (Dp j ^ b) = (Dp j ^ b) * (S i ^ a : Module.End ℂ (Grid N → ℂ)) :=
  ((Commute.pow_pow (S_Dp_comm i j) a b)).eq

/-- Iterated one-direction shifted Leibniz rule. -/
theorem Dp_pow_mul (i : Fin 3) (n : ℕ) (f w : Grid N → ℂ) :
    (Dp i ^ n) (f * w) = ∑ j ∈ range (n + 1),
      n.choose j • ((S i ^ (n - j)) ((Dp i ^ j) f) * (Dp i ^ (n - j)) w) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, ih, map_sum]
    have key : ∀ j ∈ range (n + 1), Dp i (n.choose j •
        ((S i ^ (n - j)) ((Dp i ^ j) f) * (Dp i ^ (n - j)) w)) =
        n.choose j • ((S i ^ (n + 1 - j)) ((Dp i ^ j) f) * (Dp i ^ (n + 1 - j)) w) +
        n.choose j • ((S i ^ (n - j)) ((Dp i ^ (j + 1)) f) * (Dp i ^ (n - j)) w) := by
      intro j hj
      have hjn : j ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hj)
      rw [map_nsmul, Dp_mul, smul_add]
      congr 2
      · rw [show n + 1 - j = (n - j) + 1 by omega, pow_succ', pow_succ', Module.End.mul_apply,
          Module.End.mul_apply]
      · have hc := S_pow_Dp_pow_comm (N := N) i i (n - j) 1
        rw [pow_one] at hc
        rw [pow_succ' (Dp i) j, Module.End.mul_apply, ← Module.End.mul_apply (Dp i) (S i ^ (n - j)),
          ← hc, Module.End.mul_apply]
    rw [sum_congr rfl key, sum_add_distrib]
    have := Finset.sum_choose_succ_nsmul
      (fun j l => (S i ^ l) ((Dp i ^ j) f) * (Dp i ^ l) w) n
    rw [this]


/-! ### Fourier multipliers -/

/-- Fourier inversion for the normalised DFT: `u(x) = Σ_k e(k·x) û(k)`. -/
theorem dft_inversion (u : Grid N → ℂ) (x : Grid N) :
    ∑ k, latticeChar k x * dft u k = u x := by
  have hn : ((N : ℂ) ^ 3) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne N))
  unfold dft
  simp only [smul_eq_mul, mul_sum]
  rw [sum_comm]
  have hrow : ∀ y : Grid N, ∑ k : Grid N, latticeChar k x * (((N : ℂ) ^ 3)⁻¹ *
      (conj (latticeChar k y) * u y)) =
      ((N : ℂ) ^ 3)⁻¹ * (∑ k : Grid N, latticeChar k (x - y)) * u y := by
    intro y
    rw [mul_sum, sum_mul]
    refine sum_congr rfl fun k _ => ?_
    rw [latticeChar_sub_right]
    ring
  simp only [hrow, sum_latticeChar, sub_eq_zero]
  rw [Finset.sum_eq_single x]
  · simp [hn]
  · intro y _ hy
    simp [Ne.symm hy]
  · simp

/-- The DFT is injective. -/
theorem eq_of_dft_eq {u v : Grid N → ℂ} (h : ∀ k, dft u k = dft v k) : u = v := by
  funext x
  rw [← dft_inversion u x, ← dft_inversion v x]
  simp only [h]

/-- `T` acts as the Fourier multiplier `m`. -/
def IsMult (T : Module.End ℂ (Grid N → ℂ)) (m : Grid N → ℂ) : Prop :=
  ∀ u k, dft (T u) k = m k * dft u k

theorem IsMult.one : IsMult (1 : Module.End ℂ (Grid N → ℂ)) (fun _ => 1) := by
  intro u k; simp

theorem IsMult.mul {T T' : Module.End ℂ (Grid N → ℂ)} {m m' : Grid N → ℂ}
    (h : IsMult T m) (h' : IsMult T' m') : IsMult (T * T') (fun k => m k * m' k) := by
  intro u k
  rw [Module.End.mul_apply, h, h']
  ring

theorem IsMult.pow {T : Module.End ℂ (Grid N → ℂ)} {m : Grid N → ℂ} (h : IsMult T m) (n : ℕ) :
    IsMult (T ^ n) (fun k => m k ^ n) := by
  induction n with
  | zero => simpa using (IsMult.one (N := N))
  | succ n ih =>
    have := h.mul ih
    simpa [pow_succ', mul_comm] using this

theorem IsMult.sub {T T' : Module.End ℂ (Grid N → ℂ)} {m m' : Grid N → ℂ}
    (h : IsMult T m) (h' : IsMult T' m') : IsMult (T - T') (fun k => m k - m' k) := by
  intro u k
  rw [LinearMap.sub_apply, dft_sub, h, h']
  ring

theorem IsMult.add {T T' : Module.End ℂ (Grid N → ℂ)} {m m' : Grid N → ℂ}
    (h : IsMult T m) (h' : IsMult T' m') : IsMult (T + T') (fun k => m k + m' k) := by
  intro u k
  rw [LinearMap.add_apply, dft_add, h, h']
  ring

theorem IsMult.smul {T : Module.End ℂ (Grid N → ℂ)} {m : Grid N → ℂ}
    (h : IsMult T m) (c : ℂ) : IsMult (c • T) (fun k => c * m k) := by
  intro u k
  rw [LinearMap.smul_apply, dft_smul, h, smul_eq_mul]
  ring

theorem IsMult.apply_eq {T T' : Module.End ℂ (Grid N → ℂ)} {m : Grid N → ℂ}
    (h : IsMult T m) (h' : IsMult T' m) (u : Grid N → ℂ) : T u = T' u :=
  eq_of_dft_eq fun k => by rw [h, h']

/-- The shift multiplier `e(k_i)`. -/
noncomputable def chi (i : Fin 3) (k : Grid N) : ℂ := ZMod.stdAddChar (k i)

/-- The forward-difference symbol `d_i(k) = (e^{2πi h k_i} - 1)/h`. -/
noncomputable def sym (i : Fin 3) (k : Grid N) : ℂ := (N : ℂ) * (chi i k - 1)

theorem isMult_S (i : Fin 3) : IsMult (S (N := N) i) (chi i) := by
  intro u k
  exact dft_shift u i k

theorem isMult_Sinv (i : Fin 3) : IsMult (Sinv (N := N) i) (fun k => conj (chi i k)) := by
  intro u k
  exact dft_shiftAdj u i k

theorem isMult_Dp (i : Fin 3) : IsMult (Dp (N := N) i) (sym i) := by
  have := ((isMult_S (N := N) i).sub IsMult.one).smul (N : ℂ)
  intro u k
  rw [Dp, this u k]
  simp [sym]

theorem isMult_Dm (i : Fin 3) :
    IsMult (Dm (N := N) i) (fun k => (N : ℂ) * (1 - conj (chi i k))) := by
  have := (IsMult.one.sub (isMult_Sinv (N := N) i)).smul (N : ℂ)
  intro u k
  rw [Dm, this u k]

/-- Multi-index forward difference `D^α = Π_i (D_i⁺)^{α_i}`. -/
noncomputable def Dα (α : Fin 3 → ℕ) : Module.End ℂ (Grid N → ℂ) :=
  Dp 0 ^ α 0 * Dp 1 ^ α 1 * Dp 2 ^ α 2

/-- Multi-index shift `S^α = Π_i S_i^{α_i}`. -/
noncomputable def Sα (α : Fin 3 → ℕ) : Module.End ℂ (Grid N → ℂ) :=
  S 0 ^ α 0 * S 1 ^ α 1 * S 2 ^ α 2

/-- The symbol `d^α(k) = Π_i d_i(k)^{α_i}`. -/
noncomputable def dsym (α : Fin 3 → ℕ) (k : Grid N) : ℂ :=
  sym 0 k ^ α 0 * sym 1 k ^ α 1 * sym 2 k ^ α 2

/-- The shift symbol `Π_i e(k_i)^{α_i}`. -/
noncomputable def csym (α : Fin 3 → ℕ) (k : Grid N) : ℂ :=
  chi 0 k ^ α 0 * chi 1 k ^ α 1 * chi 2 k ^ α 2

theorem isMult_Dα (α : Fin 3 → ℕ) : IsMult (Dα (N := N) α) (dsym α) :=
  (((isMult_Dp 0).pow _).mul ((isMult_Dp 1).pow _)).mul ((isMult_Dp 2).pow _)

theorem isMult_Sα (α : Fin 3 → ℕ) : IsMult (Sα (N := N) α) (csym α) :=
  (((isMult_S 0).pow _).mul ((isMult_S 1).pow _)).mul ((isMult_S 2).pow _)

theorem Dα_add (α β : Fin 3 → ℕ) (u : Grid N → ℂ) : Dα (α + β) u = Dα α (Dα β u) := by
  have h2 : IsMult (Dα (N := N) α * Dα β) (dsym (α + β)) := by
    have := (isMult_Dα (N := N) α).mul (isMult_Dα β)
    intro v k; rw [this v k]; simp only [dsym, Pi.add_apply]; ring
  exact ((isMult_Dα (α + β)).apply_eq h2 u)

theorem norm_chi (i : Fin 3) (k : Grid N) : ‖chi i k‖ = 1 := by
  unfold chi
  rw [ZMod.stdAddChar_apply]
  exact Circle.norm_coe _

theorem norm_csym (α : Fin 3 → ℕ) (k : Grid N) : ‖csym α k‖ = 1 := by
  simp [csym, norm_chi]

/-! ### Grid norms and Parseval -/

/-- The squared grid norm `‖u‖_h² = h³ Σ_x |u(x)|²`. -/
noncomputable def gridNormSq (u : Grid N → ℂ) : ℝ := ((N : ℝ) ^ 3)⁻¹ * ∑ x, ‖u x‖ ^ 2

/-- The grid norm `‖u‖_h`. -/
noncomputable def gridNorm (u : Grid N → ℂ) : ℝ := Real.sqrt (gridNormSq u)

theorem gridNormSq_nonneg (u : Grid N → ℂ) : 0 ≤ gridNormSq u := by
  unfold gridNormSq; positivity

theorem gridNorm_nonneg (u : Grid N → ℂ) : 0 ≤ gridNorm u := Real.sqrt_nonneg _

theorem gridNorm_sq (u : Grid N → ℂ) : gridNorm u ^ 2 = gridNormSq u :=
  Real.sq_sqrt (gridNormSq_nonneg u)

/-- Parseval: `‖u‖_h² = Σ_k |û(k)|²`. -/
theorem gridNormSq_eq_sum_dft (u : Grid N → ℂ) : gridNormSq u = ∑ k, ‖dft u k‖ ^ 2 := by
  rw [sum_norm_dft_sq]; rfl

theorem gridNorm_eq_euclid (u : Grid N → ℂ) :
    gridNorm u = Real.sqrt (((N : ℝ) ^ 3)⁻¹) *
      ‖(WithLp.toLp 2 u : EuclideanSpace ℂ (Grid N))‖ := by
  rw [PiLp.norm_eq_of_L2, gridNorm, gridNormSq, Real.sqrt_mul (by positivity)]

theorem gridNorm_add_le (u v : Grid N → ℂ) : gridNorm (u + v) ≤ gridNorm u + gridNorm v := by
  rw [gridNorm_eq_euclid, gridNorm_eq_euclid, gridNorm_eq_euclid, WithLp.toLp_add, ← mul_add]
  exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (Real.sqrt_nonneg _)

theorem gridNorm_smul (c : ℂ) (u : Grid N → ℂ) : gridNorm (c • u) = ‖c‖ * gridNorm u := by
  rw [gridNorm_eq_euclid, gridNorm_eq_euclid, WithLp.toLp_smul, norm_smul]
  ring

theorem gridNorm_neg (u : Grid N → ℂ) : gridNorm (-u) = gridNorm u := by
  rw [gridNorm_eq_euclid, gridNorm_eq_euclid, WithLp.toLp_neg, norm_neg]

theorem gridNorm_sub_le (u v : Grid N → ℂ) : gridNorm (u - v) ≤ gridNorm u + gridNorm v := by
  rw [sub_eq_add_neg]
  exact (gridNorm_add_le _ _).trans (by rw [gridNorm_neg])

theorem gridNorm_sum_le {ι : Type*} (s : Finset ι) (f : ι → Grid N → ℂ) :
    gridNorm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, gridNorm (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp [gridNorm, gridNormSq]
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha]
    exact (gridNorm_add_le _ _).trans (by linarith)

theorem gridNorm_nsmul (n : ℕ) (u : Grid N → ℂ) : gridNorm (n • u) = n * gridNorm u := by
  rw [← Nat.cast_smul_eq_nsmul ℂ, gridNorm_smul]
  simp

/-- Multipliers of modulus one (shifts) preserve the grid norm. -/
theorem gridNormSq_of_unimodular {T : Module.End ℂ (Grid N → ℂ)} {m : Grid N → ℂ}
    (h : IsMult T m) (hm : ∀ k, ‖m k‖ = 1) (u : Grid N → ℂ) :
    gridNormSq (T u) = gridNormSq u := by
  rw [gridNormSq_eq_sum_dft, gridNormSq_eq_sum_dft]
  refine sum_congr rfl fun k _ => ?_
  rw [h, norm_mul, hm, one_mul]

theorem gridNorm_Sα (α : Fin 3 → ℕ) (u : Grid N → ℂ) : gridNorm (Sα α u) = gridNorm u := by
  unfold gridNorm
  rw [gridNormSq_of_unimodular (isMult_Sα α) (norm_csym α)]

/-- The squared norm of a multiplier image. -/
theorem gridNormSq_mult {T : Module.End ℂ (Grid N → ℂ)} {m : Grid N → ℂ}
    (h : IsMult T m) (u : Grid N → ℂ) :
    gridNormSq (T u) = ∑ k, ‖m k‖ ^ 2 * ‖dft u k‖ ^ 2 := by
  rw [gridNormSq_eq_sum_dft]
  refine sum_congr rfl fun k _ => ?_
  rw [h, norm_mul, mul_pow]


/-! ### The multi-index shifted product rule -/

/-- The box `{β : β ≤ α}` of multi-indices. -/
def box (α : Fin 3 → ℕ) : Finset (Fin 3 → ℕ) := Fintype.piFinset fun i => range (α i + 1)

/-- The multi-binomial coefficient `binom(α, β) = Π_i binom(α_i, β_i)`. -/
def mchoose (α β : Fin 3 → ℕ) : ℕ :=
  (α 0).choose (β 0) * (α 1).choose (β 1) * (α 2).choose (β 2)

theorem mem_box {α β : Fin 3 → ℕ} : β ∈ box α ↔ ∀ i, β i ≤ α i := by
  simp [box, Fintype.mem_piFinset]

theorem sum_box {M : Type*} [AddCommMonoid M] (α : Fin 3 → ℕ) (F : (Fin 3 → ℕ) → M) :
    ∑ β ∈ box α, F β = ∑ c ∈ range (α 2 + 1), ∑ b ∈ range (α 1 + 1),
      ∑ a ∈ range (α 0 + 1), F ![a, b, c] := by
  rw [← sum_product', ← sum_product']
  refine Finset.sum_nbij' (fun β => ((β 2, β 1), β 0)) (fun p => ![p.2, p.1.2, p.1.1])
    ?_ ?_ ?_ ?_ ?_
  · intro β hβ
    simp only [box, Fintype.mem_piFinset] at hβ
    simp only [mem_product]
    exact ⟨⟨hβ 2, hβ 1⟩, hβ 0⟩
  · intro p hp
    simp only [mem_product] at hp
    simp only [box, Fintype.mem_piFinset]
    intro i; fin_cases i
    · exact hp.2
    · exact hp.1.2
    · exact hp.1.1
  · intro β _
    funext i; fin_cases i <;> rfl
  · intro p _
    rfl
  · intro β _
    congr 1
    funext i; fin_cases i <;> rfl

theorem IsMult.apply_eq' {T T' : Module.End ℂ (Grid N → ℂ)} {m m' : Grid N → ℂ}
    (h : IsMult T m) (h' : IsMult T' m') (hm : ∀ k, m k = m' k) (u : Grid N → ℂ) :
    T u = T' u :=
  eq_of_dft_eq fun k => by rw [h, h', hm]

theorem nested_eq_Sα_Dα (p0 p1 p2 a b c : ℕ) (f : Grid N → ℂ) :
    (S 0 ^ p0) ((Dp 0 ^ a) ((S 1 ^ p1) ((Dp 1 ^ b) ((S 2 ^ p2) ((Dp 2 ^ c) f))))) =
      Sα ![p0, p1, p2] (Dα ![a, b, c] f) := by
  have h1 := (((((((isMult_S (N := N) 0).pow p0).mul ((isMult_Dp 0).pow a)).mul
    ((isMult_S 1).pow p1)).mul ((isMult_Dp 1).pow b)).mul ((isMult_S 2).pow p2)).mul
    ((isMult_Dp 2).pow c))
  have h2 := (isMult_Sα (N := N) ![p0, p1, p2]).mul (isMult_Dα ![a, b, c])
  exact h1.apply_eq' h2 (fun k => by simp only [csym, dsym]; simp; ring) f

theorem nested_eq_Dα (a b c : ℕ) (w : Grid N → ℂ) :
    (Dp 0 ^ a) ((Dp 1 ^ b) ((Dp 2 ^ c) w)) = Dα ![a, b, c] w := rfl

/-- `eq:supp-open-shifted-product`: the exact shifted product rule
`D^α(f w) = Σ_{β ≤ α} binom(α, β) (S^{α-β} D^β f) D^{α-β} w`. -/
theorem Dα_mul (α : Fin 3 → ℕ) (f w : Grid N → ℂ) :
    Dα α (f * w) = ∑ β ∈ box α, mchoose α β • (Sα (α - β) (Dα β f) * Dα (α - β) w) := by
  rw [sum_box]
  show (Dp 0 ^ α 0) ((Dp 1 ^ α 1) ((Dp 2 ^ α 2) (f * w))) = _
  simp only [Dp_pow_mul, map_sum, map_nsmul, smul_sum, smul_smul]
  refine sum_congr rfl fun c _ => sum_congr rfl fun b _ => sum_congr rfl fun a _ => ?_
  rw [nested_eq_Sα_Dα, nested_eq_Dα]
  have e1 : (α - ![a, b, c]) = ![α 0 - a, α 1 - b, α 2 - c] := by
    funext i; fin_cases i <;> rfl
  rw [e1]
  congr 1
  simp only [mchoose, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  ring

/-- The shifted commutator `𝒞_α(f, w) = D^α(f w) - (S^α f) D^α w`
(`eq:supp-open-commutator`). -/
noncomputable def commutator (α : Fin 3 → ℕ) (f w : Grid N → ℂ) : Grid N → ℂ :=
  Dα α (f * w) - Sα α f * Dα α w

theorem Dα_zero : Dα (N := N) 0 = 1 := by simp [Dα]

theorem mchoose_zero (α : Fin 3 → ℕ) : mchoose α 0 = 1 := by simp [mchoose]

theorem zero_mem_box (α : Fin 3 → ℕ) : (0 : Fin 3 → ℕ) ∈ box α := mem_box.mpr fun _ => Nat.zero_le _

/-- The commutator only involves the terms with at least one difference on `f`. -/
theorem commutator_eq_sum (α : Fin 3 → ℕ) (f w : Grid N → ℂ) :
    commutator α f w = ∑ β ∈ (box α).erase 0,
      mchoose α β • (Sα (α - β) (Dα β f) * Dα (α - β) w) := by
  rw [commutator, Dα_mul, ← add_sum_erase _ _ (zero_mem_box α)]
  simp [mchoose_zero, Dα_zero]

/-- The commutator is unchanged by subtracting a constant from the coefficient. -/
theorem commutator_sub_const (α : Fin 3 → ℕ) (f w : Grid N → ℂ) (c : ℂ) :
    commutator α f w = commutator α (f - fun _ => c) w := by
  have hc : commutator α (fun _ => c) w = 0 := by
    have h1 : (fun _ : Grid N => c) * w = c • w := by funext x; simp
    have h2 : Sα α (fun _ : Grid N => c) = fun _ => c := by
      simp only [Sα, Module.End.mul_apply]
      have hS : ∀ (i : Fin 3) (n : ℕ), (S (N := N) i ^ n) (fun _ => c) = fun _ => c := by
        intro i n
        induction n with
        | zero => rfl
        | succ n ih => rw [pow_succ', Module.End.mul_apply, ih]; rfl
      rw [hS, hS, hS]
    rw [commutator, h1, map_smul, h2]
    funext x; simp
  have : commutator α f w = commutator α (f - fun _ => c) w + commutator α (fun _ => c) w := by
    simp only [commutator, sub_mul, map_sub]
    abel
  rw [this, hc, add_zero]

/-! ### Grid Sobolev norms -/

/-- The order `|α| = α₀ + α₁ + α₂`. -/
def deg (α : Fin 3 → ℕ) : ℕ := α 0 + α 1 + α 2

/-- Multi-indices of order at most `r`. -/
def multiIndices (r : ℕ) : Finset (Fin 3 → ℕ) :=
  (Fintype.piFinset fun _ : Fin 3 => range (r + 1)).filter fun α => deg α ≤ r

theorem mem_multiIndices {r : ℕ} {α : Fin 3 → ℕ} : α ∈ multiIndices r ↔ deg α ≤ r := by
  simp only [multiIndices, mem_filter, Fintype.mem_piFinset, mem_range, and_iff_right_iff_imp]
  intro h i
  unfold deg at h
  fin_cases i <;> simp <;> omega

/-- The squared grid Sobolev norm `‖u‖_{r,h}² = Σ_{|α| ≤ r} ‖D^α u‖_h²`
(`eq:supp-open-norms`). -/
noncomputable def sobSq (r : ℕ) (u : Grid N → ℂ) : ℝ :=
  ∑ α ∈ multiIndices r, gridNormSq (Dα α u)

/-- The grid Sobolev norm `‖u‖_{r,h}`. -/
noncomputable def sobNorm (r : ℕ) (u : Grid N → ℂ) : ℝ := Real.sqrt (sobSq r u)

theorem sobSq_nonneg (r : ℕ) (u : Grid N → ℂ) : 0 ≤ sobSq r u :=
  sum_nonneg fun _ _ => gridNormSq_nonneg _

theorem sobNorm_sq (r : ℕ) (u : Grid N → ℂ) : sobNorm r u ^ 2 = sobSq r u :=
  Real.sq_sqrt (sobSq_nonneg r u)

theorem gridNormSq_Dα_le_sobSq {r : ℕ} {α : Fin 3 → ℕ} (h : deg α ≤ r) (u : Grid N → ℂ) :
    gridNormSq (Dα α u) ≤ sobSq r u :=
  single_le_sum (f := fun α => gridNormSq (Dα α u)) (fun _ _ => gridNormSq_nonneg _)
    (mem_multiIndices.mpr h)

theorem sobSq_zero (u : Grid N → ℂ) : sobSq 0 u = gridNormSq u := by
  have : multiIndices 0 = {0} := by
    ext α
    rw [mem_multiIndices, mem_singleton]
    constructor
    · intro h; funext i; unfold deg at h; fin_cases i <;> simp <;> omega
    · rintro rfl; simp [deg]
  rw [sobSq, this, sum_singleton, Dα_zero, Module.End.one_apply]

theorem sobSq_mono {r r' : ℕ} (h : r ≤ r') (u : Grid N → ℂ) : sobSq r u ≤ sobSq r' u :=
  sum_le_sum_of_subset_of_nonneg
    (fun α hα => mem_multiIndices.mpr ((mem_multiIndices.mp hα).trans h))
    (fun _ _ _ => gridNormSq_nonneg _)

theorem deg_add (α β : Fin 3 → ℕ) : deg (α + β) = deg α + deg β := by
  simp [deg]; ring

/-- `‖D^β u‖_{s,h} ≤ ‖u‖_{r,h}` when `|β| + s ≤ r`. -/
theorem sobSq_Dα_le {β : Fin 3 → ℕ} {s r : ℕ} (h : deg β + s ≤ r) (u : Grid N → ℂ) :
    sobSq s (Dα β u) ≤ sobSq r u := by
  unfold sobSq
  have e : ∑ α ∈ multiIndices s, gridNormSq (Dα α (Dα β u)) =
      ∑ γ ∈ (multiIndices s).image (· + β), gridNormSq (Dα γ u) := by
    rw [sum_image (fun a _ b _ hab => add_right_cancel hab)]
    refine sum_congr rfl fun α _ => ?_
    rw [Dα_add]
  rw [e]
  refine sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => gridNormSq_nonneg _)
  intro γ hγ
  obtain ⟨α, hα, rfl⟩ := mem_image.mp hγ
  rw [mem_multiIndices] at hα ⊢
  rw [deg_add]; omega

theorem Sα_Dα_comm (δ α : Fin 3 → ℕ) (u : Grid N → ℂ) : Dα α (Sα δ u) = Sα δ (Dα α u) :=
  ((isMult_Dα (N := N) α).mul (isMult_Sα δ)).apply_eq'
    ((isMult_Sα δ).mul (isMult_Dα α)) (fun k => mul_comm _ _) u

theorem sobSq_Sα (δ : Fin 3 → ℕ) (r : ℕ) (u : Grid N → ℂ) : sobSq r (Sα δ u) = sobSq r u := by
  unfold sobSq
  refine sum_congr rfl fun α _ => ?_
  rw [Sα_Dα_comm, gridNormSq_of_unimodular (isMult_Sα δ) (norm_csym δ)]

/-- Fourier form of the grid Sobolev norm. -/
noncomputable def gridWeight (r : ℕ) (k : Grid N) : ℝ :=
  ∑ α ∈ multiIndices r, ‖dsym α k‖ ^ 2

theorem sobSq_eq_weight (r : ℕ) (u : Grid N → ℂ) :
    sobSq r u = ∑ k, gridWeight r k * ‖dft u k‖ ^ 2 := by
  unfold sobSq gridWeight
  simp only [gridNormSq_mult (isMult_Dα _), sum_mul]
  rw [sum_comm]


/-! ### The difference symbol on the signed frequency cube -/

/-- The signed frequency `k_i ∈ (-N/2, N/2]` of a grid frequency. -/
def freq (i : Fin 3) (k : Grid N) : ℤ := (k i).valMinAbs

theorem abs_freq_le (i : Fin 3) (k : Grid N) : |(freq i k : ℝ)| * 2 ≤ N := by
  have h := (k i).valMinAbs_mem_Ioc
  have h2 : |(k i).valMinAbs| * 2 ≤ (N : ℤ) := by
    rcases h with ⟨h1, h2⟩
    rcases abs_cases (k i).valMinAbs with ⟨h3, _⟩ | ⟨h3, _⟩ <;> rw [h3] <;> omega
  unfold freq
  exact_mod_cast h2

theorem chi_eq_exp (i : Fin 3) (k : Grid N) :
    chi i k = Complex.exp (Complex.I * ((2 * π * freq i k / N : ℝ) : ℂ)) := by
  unfold chi freq
  conv_lhs => rw [← (k i).coe_valMinAbs]
  rw [ZMod.stdAddChar_coe]
  congr 1
  push_cast
  ring

theorem norm_sym_eq (i : Fin 3) (k : Grid N) :
    ‖sym i k‖ = N * (2 * |Real.sin (π * freq i k / N)|) := by
  unfold sym
  rw [norm_mul, chi_eq_exp, Complex.norm_exp_I_mul_ofReal_sub_one, Complex.norm_natCast,
    Real.norm_eq_abs, abs_mul, abs_two]
  congr 3
  ring_nf

/-- Upper symbol bound `|d_i(k)| ≤ 2π|k_i|`. -/
theorem norm_sym_le (i : Fin 3) (k : Grid N) : ‖sym i k‖ ≤ 2 * π * |(freq i k : ℝ)| := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  rw [norm_sym_eq]
  have := Real.abs_sin_le_abs (x := π * freq i k / N)
  rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hN] at this
  calc (N : ℝ) * (2 * |Real.sin (π * freq i k / N)|)
      ≤ N * (2 * (π * |(freq i k : ℝ)| / N)) := by gcongr
    _ = 2 * π * |(freq i k : ℝ)| := by field_simp

/-- Lower symbol bound `4|k_i| ≤ |d_i(k)|` on the signed cube. -/
theorem four_mul_le_norm_sym (i : Fin 3) (k : Grid N) : 4 * |(freq i k : ℝ)| ≤ ‖sym i k‖ := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  rw [norm_sym_eq]
  set y : ℝ := π * freq i k / N with hy
  have hyabs : |y| = π * |(freq i k : ℝ)| / N := by
    rw [hy, abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hN]
  have hyle : |y| ≤ π / 2 := by
    rw [hyabs, div_le_iff₀ hN]
    have := abs_freq_le i k
    nlinarith [Real.pi_pos]
  have hsin : 2 / π * |y| ≤ |Real.sin y| := by
    rcases le_total 0 y with h0 | h0
    · rw [abs_of_nonneg h0]
      have := Real.mul_le_sin h0 (by rwa [abs_of_nonneg h0] at hyle)
      exact this.trans (le_abs_self _)
    · rw [abs_of_nonpos h0]
      have := Real.mul_le_sin (neg_nonneg.mpr h0) (by rwa [abs_of_nonpos h0] at hyle)
      rw [Real.sin_neg] at this
      exact this.trans (neg_le_abs _)
  calc 4 * |(freq i k : ℝ)| = N * (2 * (2 / π * |y|)) := by
        rw [hyabs]; field_simp; ring
    _ ≤ N * (2 * |Real.sin y|) := by gcongr

theorem sq_le_norm_sym_sq (i : Fin 3) (k : Grid N) :
    16 * (freq i k : ℝ) ^ 2 ≤ ‖sym i k‖ ^ 2 := by
  have h := four_mul_le_norm_sym i k
  have h0 : 0 ≤ 4 * |(freq i k : ℝ)| := by positivity
  calc 16 * (freq i k : ℝ) ^ 2 = (4 * |(freq i k : ℝ)|) ^ 2 := by rw [mul_pow, sq_abs]; norm_num
    _ ≤ ‖sym i k‖ ^ 2 := pow_le_pow_left₀ h0 h 2

theorem norm_sym_sq_le (i : Fin 3) (k : Grid N) :
    ‖sym i k‖ ^ 2 ≤ (2 * π) ^ 2 * (freq i k : ℝ) ^ 2 := by
  have h := norm_sym_le i k
  calc ‖sym i k‖ ^ 2 ≤ (2 * π * |(freq i k : ℝ)|) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = (2 * π) ^ 2 * (freq i k : ℝ) ^ 2 := by rw [mul_pow, sq_abs]

/-! ### The uniform summation constant -/

/-- One-dimensional weight `(1 + 16 n²)^{-2/3}`. -/
noncomputable def w1d (n : ℤ) : ℝ := ((1 + 16 * (n : ℝ) ^ 2) ^ ((2 : ℝ) / 3))⁻¹

theorem w1d_nonneg (n : ℤ) : 0 ≤ w1d n := by unfold w1d; positivity

theorem summable_w1d : Summable w1d := by
  have hs : Summable fun n : ℤ => |(n : ℝ)| ^ (-((4 : ℝ) / 3)) + (if n = 0 then (1 : ℝ) else 0) :=
    (Real.summable_abs_int_rpow (by norm_num)).add (hasSum_ite_eq (0 : ℤ) (1 : ℝ)).summable
  refine Summable.of_nonneg_of_le w1d_nonneg (fun n => ?_) hs
  by_cases hn : n = 0
  · subst hn; simp [w1d]
  · rw [if_neg hn, add_zero, Real.rpow_neg (abs_nonneg _)]
    unfold w1d
    have hpos : 0 < |(n : ℝ)| := abs_pos.mpr (by exact_mod_cast hn)
    apply inv_anti₀ (by positivity)
    have e : |(n : ℝ)| ^ ((4 : ℝ) / 3) = ((n : ℝ) ^ 2) ^ ((2 : ℝ) / 3) := by
      rw [← sq_abs, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
      norm_num
    rw [e]
    exact Real.rpow_le_rpow (by positivity) (by nlinarith) (by norm_num)

/-- The summation constant `c₁ = Σ_{n ∈ ℤ} (1 + 16 n²)^{-2/3}`. -/
noncomputable def c1 : ℝ := ∑' n : ℤ, w1d n

theorem c1_nonneg : 0 ≤ c1 := tsum_nonneg w1d_nonneg

theorem sum_zmod_w1d_le : ∑ t : ZMod N, w1d t.valMinAbs ≤ c1 := by
  rw [← sum_image (f := w1d) (fun a _ b _ h => ZMod.injective_valMinAbs h)]
  exact summable_w1d.sum_le_tsum _ (fun _ _ => w1d_nonneg _)

/-- The cube weight `S(k) = 1 + 16 Σ_i k_i²`. -/
noncomputable def cubeWeight (k : Grid N) : ℝ := 1 + 16 * ∑ i, (freq i k : ℝ) ^ 2

theorem one_le_cubeWeight (k : Grid N) : 1 ≤ cubeWeight k := by
  unfold cubeWeight
  have : 0 ≤ ∑ i, (freq i k : ℝ) ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  linarith

theorem inv_cubeWeight_sq_le (k : Grid N) :
    (cubeWeight k ^ 2)⁻¹ ≤ ∏ i, w1d (freq i k) := by
  have hS := one_le_cubeWeight k
  have hai : ∀ i, (1 + 16 * (freq i k : ℝ) ^ 2) ^ ((2 : ℝ) / 3) ≤
      cubeWeight k ^ ((2 : ℝ) / 3) := by
    intro i
    apply Real.rpow_le_rpow (by positivity) _ (by norm_num)
    unfold cubeWeight
    have : (freq i k : ℝ) ^ 2 ≤ ∑ j, (freq j k : ℝ) ^ 2 :=
      single_le_sum (f := fun j => (freq j k : ℝ) ^ 2) (fun _ _ => sq_nonneg _) (mem_univ i)
    linarith
  unfold w1d
  rw [prod_inv_distrib]
  apply inv_anti₀ (by positivity)
  calc ∏ i, (1 + 16 * (freq i k : ℝ) ^ 2) ^ ((2 : ℝ) / 3)
      ≤ ∏ _i : Fin 3, cubeWeight k ^ ((2 : ℝ) / 3) :=
        prod_le_prod (fun _ _ => by positivity) (fun i _ => hai i)
    _ = cubeWeight k ^ 2 := by
        rw [prod_const, card_univ, Fintype.card_fin, ← Real.rpow_mul_natCast (by linarith)]
        norm_num

/-- `Σ_k S(k)^{-2} ≤ c₁³`, uniformly in `N`. -/
theorem sum_inv_cubeWeight_sq_le : ∑ k : Grid N, (cubeWeight k ^ 2)⁻¹ ≤ c1 ^ 3 := by
  calc ∑ k : Grid N, (cubeWeight k ^ 2)⁻¹ ≤ ∑ k : Grid N, ∏ i, w1d (freq i k) :=
        sum_le_sum fun k _ => inv_cubeWeight_sq_le k
    _ = ∏ _i : Fin 3, ∑ t : ZMod N, w1d t.valMinAbs := by
        rw [Finset.prod_univ_sum, Fintype.piFinset_univ]; rfl
    _ ≤ ∏ _i : Fin 3, c1 := prod_le_prod (fun _ _ => sum_nonneg fun _ _ => w1d_nonneg _)
        (fun _ _ => sum_zmod_w1d_le)
    _ = c1 ^ 3 := by simp

/-! ### Weight lower bounds -/

theorem gridWeight_nonneg (r : ℕ) (k : Grid N) : 0 ≤ gridWeight r k :=
  sum_nonneg fun _ _ => sq_nonneg _

/-- The first-order weight dominates `1 + Σ_i |d_i(k)|²`. -/
theorem gridWeight_one_ge (k : Grid N) :
    1 + ∑ i, ‖sym i k‖ ^ 2 ≤ gridWeight 1 k := by
  have hsub : ({![0, 0, 0], ![1, 0, 0], ![0, 1, 0], ![0, 0, 1]} : Finset (Fin 3 → ℕ)) ⊆
      multiIndices 1 := by
    intro α hα
    simp only [mem_insert, mem_singleton] at hα
    rw [mem_multiIndices]
    rcases hα with rfl | rfl | rfl | rfl <;> simp [deg]
  refine le_trans (le_of_eq ?_) (sum_le_sum_of_subset_of_nonneg hsub
    (fun _ _ _ => sq_nonneg _))
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton]
  simp [dsym, Fin.sum_univ_three]
  ring

/-- The second-order weight dominates `(1 + Σ_i |d_i(k)|²)² / 2`. -/
theorem gridWeight_two_ge (k : Grid N) :
    (1 + ∑ i, ‖sym i k‖ ^ 2) ^ 2 / 2 ≤ gridWeight 2 k := by
  have hsub : ({![0, 0, 0], ![1, 0, 0], ![0, 1, 0], ![0, 0, 1], ![2, 0, 0], ![0, 2, 0],
      ![0, 0, 2], ![1, 1, 0], ![1, 0, 1], ![0, 1, 1]} : Finset (Fin 3 → ℕ)) ⊆
      multiIndices 2 := by
    intro α hα
    simp only [mem_insert, mem_singleton] at hα
    rw [mem_multiIndices]
    rcases hα with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [deg]
  refine le_trans ?_ (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _))
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide),
    sum_insert (by decide), sum_insert (by decide), sum_insert (by decide),
    sum_insert (by decide), sum_insert (by decide), sum_insert (by decide), sum_singleton]
  simp only [dsym, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, pow_zero, pow_one, mul_one, one_mul,
    norm_mul, norm_pow, norm_one]
  set a := ‖sym 0 k‖
  set b := ‖sym 1 k‖
  set c := ‖sym 2 k‖
  nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a ^ 2 - c ^ 2), sq_nonneg (b ^ 2 - c ^ 2),
    sq_nonneg a, sq_nonneg b, sq_nonneg c, mul_nonneg (sq_nonneg a) (sq_nonneg b),
    mul_nonneg (sq_nonneg a) (sq_nonneg c), mul_nonneg (sq_nonneg b) (sq_nonneg c)]

theorem cubeWeight_le_sym (k : Grid N) : cubeWeight k ≤ 1 + ∑ i, ‖sym i k‖ ^ 2 := by
  unfold cubeWeight
  rw [mul_sum]
  have := sum_le_sum (s := univ) fun i (_ : i ∈ univ) => sq_le_norm_sym_sq i k
  linarith

theorem cubeWeight_le_gridWeight_one (k : Grid N) : cubeWeight k ≤ gridWeight 1 k :=
  (cubeWeight_le_sym k).trans (gridWeight_one_ge k)

theorem cubeWeight_sq_le_gridWeight_two (k : Grid N) : cubeWeight k ^ 2 / 2 ≤ gridWeight 2 k := by
  refine le_trans ?_ (gridWeight_two_ge k)
  have h0 : 0 ≤ cubeWeight k := le_trans zero_le_one (one_le_cubeWeight k)
  gcongr
  exact cubeWeight_le_sym k


/-! ### Products are convolutions; the weighted convolution estimate -/

theorem conj_latticeChar_sub (k p x : Grid N) :
    conj (latticeChar (k - p) x) = conj (latticeChar k x) * latticeChar p x := by
  rw [latticeChar_comm (k - p) x, latticeChar_sub_right, map_mul, Complex.conj_conj,
    latticeChar_comm x k, latticeChar_comm x p]

/-- Multiplication is convolution on the finite frequency group:
`(f w)^(k) = Σ_p f̂(p) ŵ(k - p)`. -/
theorem dft_mul (f w : Grid N → ℂ) (k : Grid N) :
    dft (f * w) k = ∑ p, dft f p * dft w (k - p) := by
  calc dft (f * w) k
      = ((N : ℂ) ^ 3)⁻¹ • ∑ x, conj (latticeChar k x) • (f x * w x) := rfl
    _ = ((N : ℂ) ^ 3)⁻¹ • ∑ x, conj (latticeChar k x) •
          ((∑ p, latticeChar p x * dft f p) * w x) := by simp_rw [dft_inversion]
    _ = ∑ p, dft f p * (((N : ℂ) ^ 3)⁻¹ • ∑ x, conj (latticeChar (k - p) x) • w x) := by
        simp only [smul_eq_mul, sum_mul, mul_sum]
        rw [sum_comm]
        refine sum_congr rfl fun p _ => sum_congr rfl fun x _ => ?_
        rw [conj_latticeChar_sub]
        ring
    _ = ∑ p, dft f p * dft w (k - p) := rfl

/-- Weighted convolution estimate on the finite frequency group: if
`Σ_p 1/(u(p) v(k-p)) ≤ M` for every `k`, then
`Σ_k |Σ_p A(p) B(k-p)|² ≤ M (Σ u |A|²)(Σ v |B|²)`. -/
theorem conv_bound (A B : Grid N → ℂ) (u v : Grid N → ℝ) (hu : ∀ p, 0 < u p)
    (hv : ∀ p, 0 < v p) (M : ℝ) (hM : ∀ k, ∑ p, 1 / (u p * v (k - p)) ≤ M) :
    ∑ k, ‖∑ p, A p * B (k - p)‖ ^ 2 ≤
      M * (∑ p, u p * ‖A p‖ ^ 2) * (∑ q, v q * ‖B q‖ ^ 2) := by
  have hpt : ∀ k, ‖∑ p, A p * B (k - p)‖ ^ 2 ≤
      M * ∑ p, (u p * ‖A p‖ ^ 2) * (v (k - p) * ‖B (k - p)‖ ^ 2) := by
    intro k
    have h1 : ‖∑ p, A p * B (k - p)‖ ≤ ∑ p, ‖A p‖ * ‖B (k - p)‖ :=
      (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun p _ => norm_mul _ _))
    have h2 : (∑ p, ‖A p‖ * ‖B (k - p)‖) ^ 2 ≤
        (∑ p, 1 / (u p * v (k - p))) *
          ∑ p, (u p * ‖A p‖ ^ 2) * (v (k - p) * ‖B (k - p)‖ ^ 2) := by
      refine sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun p _ => ?_) (fun p _ => ?_)
        (fun p _ => ?_)
      · have := hu p; have := hv (k - p); positivity
      · have := hu p; have := hv (k - p); positivity
      · have hu' := hu p; have hv' := hv (k - p)
        rw [le_iff_eq_or_lt]; left
        field_simp
    have h3 : 0 ≤ ∑ p, (u p * ‖A p‖ ^ 2) * (v (k - p) * ‖B (k - p)‖ ^ 2) :=
      sum_nonneg fun p _ => by have := hu p; have := hv (k - p); positivity
    calc ‖∑ p, A p * B (k - p)‖ ^ 2 ≤ (∑ p, ‖A p‖ * ‖B (k - p)‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ _ := h2
      _ ≤ _ := mul_le_mul_of_nonneg_right (hM k) h3
  calc ∑ k, ‖∑ p, A p * B (k - p)‖ ^ 2
      ≤ ∑ k, M * ∑ p, (u p * ‖A p‖ ^ 2) * (v (k - p) * ‖B (k - p)‖ ^ 2) :=
        sum_le_sum fun k _ => hpt k
    _ = M * ∑ p, (u p * ‖A p‖ ^ 2) * ∑ k, (v (k - p) * ‖B (k - p)‖ ^ 2) := by
        rw [← mul_sum, sum_comm]
        congr 1
        refine sum_congr rfl fun p _ => ?_
        rw [mul_sum]
    _ = M * (∑ p, u p * ‖A p‖ ^ 2) * (∑ q, v q * ‖B q‖ ^ 2) := by
        have hre : ∀ p : Grid N, ∑ k, (v (k - p) * ‖B (k - p)‖ ^ 2) = ∑ q, v q * ‖B q‖ ^ 2 :=
          fun p => Fintype.sum_equiv (Equiv.subRight p) _ _ (fun _ => rfl)
        simp only [hre]
        rw [mul_assoc, sum_mul]

/-- The uniform product constant `K = 2 c₁³` (independent of `N`). -/
noncomputable def Kprod : ℝ := 2 * c1 ^ 3

theorem Kprod_nonneg : 0 ≤ Kprod := by unfold Kprod; have := c1_nonneg; positivity

theorem gridWeight_one_pos (k : Grid N) : 0 < gridWeight 1 k :=
  lt_of_lt_of_le (by linarith [one_le_cubeWeight k]) (cubeWeight_le_gridWeight_one k)

theorem gridWeight_two_pos (k : Grid N) : 0 < gridWeight 2 k := by
  have h := cubeWeight_sq_le_gridWeight_two k
  have h1 := one_le_cubeWeight k
  nlinarith

/-- `H¹ × H¹ → L²` product bound: `‖a b‖_h² ≤ K ‖a‖_{1,h}² ‖b‖_{1,h}²`. -/
theorem gridNormSq_mul_le_one_one (a b : Grid N → ℂ) :
    gridNormSq (a * b) ≤ Kprod * sobSq 1 a * sobSq 1 b := by
  rw [gridNormSq_eq_sum_dft, sobSq_eq_weight, sobSq_eq_weight]
  simp_rw [dft_mul]
  refine (conv_bound _ _ _ _ gridWeight_one_pos gridWeight_one_pos Kprod fun k => ?_).trans
    le_rfl
  have hpt : ∀ p, 1 / (gridWeight 1 p * gridWeight 1 (k - p)) ≤
      ((cubeWeight p ^ 2)⁻¹ + (cubeWeight (k - p) ^ 2)⁻¹) / 2 := by
    intro p
    have h1 := cubeWeight_le_gridWeight_one p
    have h2 := cubeWeight_le_gridWeight_one (k - p)
    have c1p := one_le_cubeWeight p
    have c2p := one_le_cubeWeight (k - p)
    have step : 1 / (gridWeight 1 p * gridWeight 1 (k - p)) ≤
        1 / (cubeWeight p * cubeWeight (k - p)) :=
      one_div_le_one_div_of_le (by positivity) (mul_le_mul h1 h2 (by linarith) (by linarith))
    refine step.trans ?_
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    field_simp
    nlinarith [sq_nonneg (cubeWeight p - cubeWeight (k - p)), mul_pos (by linarith : (0:ℝ) < cubeWeight p) (by linarith : (0:ℝ) < cubeWeight (k - p))]
  calc ∑ p, 1 / (gridWeight 1 p * gridWeight 1 (k - p))
      ≤ ∑ p, ((cubeWeight p ^ 2)⁻¹ + (cubeWeight (k - p) ^ 2)⁻¹) / 2 :=
        sum_le_sum fun p _ => hpt p
    _ = ∑ p : Grid N, (cubeWeight p ^ 2)⁻¹ := by
        rw [← sum_div, sum_add_distrib]
        have : ∑ p : Grid N, (cubeWeight (k - p) ^ 2)⁻¹ = ∑ p : Grid N, (cubeWeight p ^ 2)⁻¹ :=
          Fintype.sum_equiv ((Equiv.neg _).trans (Equiv.addLeft k)) _ _
            (fun p => by simp [sub_eq_add_neg])
        rw [this]; ring
    _ ≤ c1 ^ 3 := sum_inv_cubeWeight_sq_le
    _ ≤ Kprod := by unfold Kprod; have := c1_nonneg; nlinarith [pow_nonneg c1_nonneg 3]

/-- `H² × L² → L²` product bound (the uniform discrete `H² ⊂ L^∞` embedding):
`‖a b‖_h² ≤ K ‖a‖_{2,h}² ‖b‖_h²`. -/
theorem gridNormSq_mul_le_two_zero (a b : Grid N → ℂ) :
    gridNormSq (a * b) ≤ Kprod * sobSq 2 a * sobSq 0 b := by
  rw [gridNormSq_eq_sum_dft, sobSq_eq_weight, sobSq_eq_weight]
  simp_rw [dft_mul]
  have hw0 : ∀ q : Grid N, gridWeight 0 q = 1 := by
    intro q
    have : multiIndices 0 = {0} := by
      ext α
      rw [mem_multiIndices, mem_singleton]
      constructor
      · intro h; funext i; unfold deg at h; fin_cases i <;> simp <;> omega
      · rintro rfl; simp [deg]
    simp [gridWeight, this, dsym]
  refine (conv_bound _ _ (gridWeight 2) (gridWeight 0) gridWeight_two_pos
    (fun q => by rw [hw0]; norm_num) Kprod fun k => ?_).trans le_rfl
  simp only [hw0, mul_one]
  calc ∑ p, 1 / gridWeight 2 p ≤ ∑ p : Grid N, 2 * (cubeWeight p ^ 2)⁻¹ := by
        refine sum_le_sum fun p _ => ?_
        have h := cubeWeight_sq_le_gridWeight_two p
        have h1 := one_le_cubeWeight p
        rw [div_le_iff₀ (gridWeight_two_pos p)]
        rw [show 2 * (cubeWeight p ^ 2)⁻¹ * gridWeight 2 p =
          2 * gridWeight 2 p / cubeWeight p ^ 2 by ring]
        rw [le_div_iff₀ (by positivity)]
        linarith
    _ = 2 * ∑ p : Grid N, (cubeWeight p ^ 2)⁻¹ := by rw [mul_sum]
    _ ≤ Kprod := by
        unfold Kprod
        have := sum_inv_cubeWeight_sq_le (N := N)
        linarith

theorem gridNormSq_mul_le_zero_two (a b : Grid N → ℂ) :
    gridNormSq (a * b) ≤ Kprod * sobSq 0 a * sobSq 2 b := by
  rw [mul_comm a b]
  have := gridNormSq_mul_le_two_zero b a
  linarith [show Kprod * sobSq 2 b * sobSq 0 a = Kprod * sobSq 0 a * sobSq 2 b by ring]

/-- The uniform term estimate behind the product and commutator bounds: for
`|β| ≤ p`, `|γ| ≤ q` and `|β| + |γ| + 2 ≤ p + q`,
`‖(S^δ D^β a)(D^γ b)‖_h² ≤ K ‖a‖_{p,h}² ‖b‖_{q,h}²`. -/
theorem term_le (a b : Grid N → ℂ) (β γ δ : Fin 3 → ℕ) (p q : ℕ) (hp : deg β ≤ p)
    (hq : deg γ ≤ q) (h : deg β + deg γ + 2 ≤ p + q) :
    gridNormSq (Sα δ (Dα β a) * Dα γ b) ≤ Kprod * sobSq p a * sobSq q b := by
  have hK := Kprod_nonneg
  have hp0 := sobSq_nonneg p a
  have hq0 := sobSq_nonneg q b
  by_cases h1 : deg β + 2 ≤ p
  · refine (gridNormSq_mul_le_two_zero _ _).trans ?_
    rw [sobSq_Sα]
    have e1 := sobSq_Dα_le (s := 2) h1 a
    have e2 := sobSq_Dα_le (s := 0) (by omega : deg γ + 0 ≤ q) b
    exact mul_le_mul (mul_le_mul_of_nonneg_left e1 hK) e2 (sobSq_nonneg _ _)
      (mul_nonneg hK hp0)
  · by_cases h2 : deg γ + 2 ≤ q
    · refine (gridNormSq_mul_le_zero_two _ _).trans ?_
      rw [sobSq_Sα]
      have e1 := sobSq_Dα_le (s := 0) (by omega : deg β + 0 ≤ p) a
      have e2 := sobSq_Dα_le (s := 2) h2 b
      exact mul_le_mul (mul_le_mul_of_nonneg_left e1 hK) e2 (sobSq_nonneg _ _)
        (mul_nonneg hK hp0)
    · refine (gridNormSq_mul_le_one_one _ _).trans ?_
      rw [sobSq_Sα]
      have e1 := sobSq_Dα_le (s := 1) (by omega : deg β + 1 ≤ p) a
      have e2 := sobSq_Dα_le (s := 1) (by omega : deg γ + 1 ≤ q) b
      exact mul_le_mul (mul_le_mul_of_nonneg_left e1 hK) e2 (sobSq_nonneg _ _)
        (mul_nonneg hK hp0)

theorem term_norm_le (a b : Grid N → ℂ) (β γ δ : Fin 3 → ℕ) (p q : ℕ) (hp : deg β ≤ p)
    (hq : deg γ ≤ q) (h : deg β + deg γ + 2 ≤ p + q) :
    gridNorm (Sα δ (Dα β a) * Dα γ b) ≤ Real.sqrt Kprod * sobNorm p a * sobNorm q b := by
  unfold gridNorm sobNorm
  rw [← Real.sqrt_mul Kprod_nonneg, ← Real.sqrt_mul (mul_nonneg Kprod_nonneg (sobSq_nonneg _ _))]
  exact Real.sqrt_le_sqrt (term_le a b β γ δ p q hp hq h)

/-- Norm of a binomially weighted sum of terms each bounded by `R`. -/
theorem gridNorm_sum_nsmul_le {ι : Type*} (s : Finset ι) (c : ι → ℕ) (X : ι → Grid N → ℂ)
    (R : ℝ) (hX : ∀ i ∈ s, gridNorm (X i) ≤ R) :
    gridNorm (∑ i ∈ s, c i • X i) ≤ (∑ i ∈ s, (c i : ℝ)) * R := by
  refine (gridNorm_sum_le _ _).trans ?_
  rw [sum_mul]
  refine sum_le_sum fun i hi => ?_
  rw [gridNorm_nsmul]
  exact mul_le_mul_of_nonneg_left (hX i hi) (Nat.cast_nonneg _)

theorem deg_sub_of_mem_box {α β : Fin 3 → ℕ} (h : β ∈ box α) :
    deg (α - β) = deg α - deg β ∧ deg β ≤ deg α := by
  rw [mem_box] at h
  have h0 := h 0; have h1 := h 1; have h2 := h 2
  simp only [deg, Pi.sub_apply]
  omega

theorem one_le_deg_of_ne_zero {β : Fin 3 → ℕ} (h : β ≠ 0) : 1 ≤ deg β := by
  by_contra hc
  apply h
  funext i
  unfold deg at hc
  fin_cases i <;> simp <;> omega

/-- The binomial mass `B(α) = Σ_{β ≤ α} binom(α, β)` (equal to `2^{|α|}`). -/
noncomputable def binomMass (α : Fin 3 → ℕ) : ℝ := ∑ β ∈ box α, (mchoose α β : ℝ)

theorem binomMass_nonneg (α : Fin 3 → ℕ) : 0 ≤ binomMass α :=
  sum_nonneg fun _ _ => Nat.cast_nonneg _

/-- **Uniform product algebra** (`lem:supp-open-calculus`): for `r ≥ 2`,
`‖f w‖_{r,h}² ≤ C_r ‖f‖_{r,h}² ‖w‖_{r,h}²` with
`C_r = K Σ_{|α| ≤ r} B(α)²` independent of `N`. -/
theorem sobSq_mul_le (r : ℕ) (hr : 2 ≤ r) (f w : Grid N → ℂ) :
    sobSq r (f * w) ≤
      (Kprod * ∑ α ∈ multiIndices r, binomMass α ^ 2) * sobSq r f * sobSq r w := by
  have hterm : ∀ α ∈ multiIndices r, gridNorm (Dα α (f * w)) ≤
      binomMass α * (Real.sqrt Kprod * sobNorm r f * sobNorm r w) := by
    intro α hα
    rw [mem_multiIndices] at hα
    rw [Dα_mul]
    refine gridNorm_sum_nsmul_le _ _ _ _ fun β hβ => ?_
    obtain ⟨hd, hle⟩ := deg_sub_of_mem_box hβ
    exact term_norm_le f w β (α - β) (α - β) r r (by omega) (by omega) (by omega)
  unfold sobSq
  have hsq : ∀ α ∈ multiIndices r, gridNormSq (Dα α (f * w)) ≤
      binomMass α ^ 2 * (Kprod * sobSq r f * sobSq r w) := by
    intro α hα
    rw [← gridNorm_sq]
    have h0 := gridNorm_nonneg (Dα α (f * w))
    have := pow_le_pow_left₀ h0 (hterm α hα) 2
    refine this.trans (le_of_eq ?_)
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt Kprod_nonneg, sobNorm_sq, sobNorm_sq]
  calc ∑ α ∈ multiIndices r, gridNormSq (Dα α (f * w))
      ≤ ∑ α ∈ multiIndices r, binomMass α ^ 2 * (Kprod * sobSq r f * sobSq r w) :=
        sum_le_sum hsq
    _ = _ := by rw [← sum_mul]; unfold sobSq; ring

/-- **Commutator bound, first line** (`eq:supp-open-commutator-bounds`): for
`r ≥ 3`, `|α| ≤ r` and any constant coefficient `f_*`,
`‖𝒞_α(f, w)‖_h ≤ C_α ‖f - f_*‖_{r,h} ‖w‖_{r-1,h}`, `C_α = B(α) √K`. -/
theorem commutator_norm_le (r : ℕ) (hr : 3 ≤ r) (α : Fin 3 → ℕ) (hα : deg α ≤ r)
    (f w : Grid N → ℂ) (c : ℂ) :
    gridNorm (commutator α f w) ≤
      (binomMass α * Real.sqrt Kprod) * sobNorm r (f - fun _ => c) * sobNorm (r - 1) w := by
  rw [commutator_sub_const α f w c, commutator_eq_sum]
  have hsub : (box α).erase 0 ⊆ box α := erase_subset _ _
  refine (gridNorm_sum_nsmul_le _ _ _ (Real.sqrt Kprod * sobNorm r (f - fun _ => c) *
    sobNorm (r - 1) w) fun β hβ => ?_).trans ?_
  · obtain ⟨hne, hβ'⟩ := mem_erase.mp hβ
    obtain ⟨hd, hle⟩ := deg_sub_of_mem_box hβ'
    have h1 := one_le_deg_of_ne_zero hne
    exact term_norm_le _ w β (α - β) (α - β) r (r - 1) (by omega) (by omega) (by omega)
  · have hm : ∑ β ∈ (box α).erase 0, (mchoose α β : ℝ) ≤ binomMass α :=
      sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.cast_nonneg _)
    have : 0 ≤ Real.sqrt Kprod * sobNorm r (f - fun _ => c) * sobNorm (r - 1) w := by
      unfold sobNorm; positivity
    calc (∑ β ∈ (box α).erase 0, (mchoose α β : ℝ)) *
          (Real.sqrt Kprod * sobNorm r (f - fun _ => c) * sobNorm (r - 1) w)
        ≤ binomMass α * (Real.sqrt Kprod * sobNorm r (f - fun _ => c) * sobNorm (r - 1) w) :=
          mul_le_mul_of_nonneg_right hm this
      _ = _ := by ring

/-- `‖D_i⁻ u‖_h = ‖D_i⁺ u‖_h`. -/
theorem gridNorm_Dm_eq (i : Fin 3) (u : Grid N → ℂ) : gridNorm (Dm i u) = gridNorm (Dp i u) := by
  unfold gridNorm
  rw [gridNormSq_mult (isMult_Dm i), gridNormSq_mult (isMult_Dp i)]
  congr 1
  refine sum_congr rfl fun k _ => ?_
  congr 2
  rw [sym, norm_mul, norm_mul]
  congr 1
  rw [← norm_neg, neg_sub, ← Complex.norm_conj (chi i k - 1), map_sub, map_one]

theorem gridNorm_D0_le (i : Fin 3) (u : Grid N → ℂ) : gridNorm (D0 i u) ≤ gridNorm (Dp i u) := by
  have e : D0 i u = (2 : ℂ)⁻¹ • (Dp i u + Dm i u) := by
    funext x; simp [D0_apply]
  rw [e, gridNorm_smul]
  have := gridNorm_add_le (Dp i u) (Dm i u)
  rw [gridNorm_Dm_eq] at this
  have h2 : ‖(2 : ℂ)⁻¹‖ = 1 / 2 := by simp
  rw [h2]
  linarith [gridNorm_nonneg (Dp i u)]

theorem S_Sα (i : Fin 3) (δ : Fin 3 → ℕ) (u : Grid N → ℂ) :
    S i (Sα δ u) = Sα (δ + Pi.single i 1) u := by
  refine ((isMult_S (N := N) i).mul (isMult_Sα δ)).apply_eq' (isMult_Sα _) (fun k => ?_) u
  simp only [csym, Pi.add_apply]
  fin_cases i <;> simp <;> ring

theorem Dp_Dα (i : Fin 3) (γ : Fin 3 → ℕ) (u : Grid N → ℂ) :
    Dp i (Dα γ u) = Dα (γ + Pi.single i 1) u := by
  refine ((isMult_Dp (N := N) i).mul (isMult_Dα γ)).apply_eq' (isMult_Dα _) (fun k => ?_) u
  simp only [dsym, Pi.add_apply]
  fin_cases i <;> simp <;> ring

theorem Dp_Sα_Dα (i : Fin 3) (δ β : Fin 3 → ℕ) (u : Grid N → ℂ) :
    Dp i (Sα δ (Dα β u)) = Sα δ (Dα (β + Pi.single i 1) u) := by
  refine ((isMult_Dp (N := N) i).mul ((isMult_Sα δ).mul (isMult_Dα β))).apply_eq'
    ((isMult_Sα δ).mul (isMult_Dα _)) (fun k => ?_) u
  simp only [dsym, Pi.add_apply]
  fin_cases i <;> simp <;> ring

theorem deg_add_single (γ : Fin 3 → ℕ) (i : Fin 3) : deg (γ + Pi.single i 1) = deg γ + 1 := by
  simp only [deg, Pi.add_apply]
  fin_cases i <;> simp <;> ring

/-- **Commutator bound, second line** (`eq:supp-open-commutator-bounds`): for
`r ≥ 3`, `|α| ≤ r` and any constant `f_*`,
`‖D_i⁻ 𝒞_α(f, w)‖_h + ‖D_i⁰ 𝒞_α(f, w)‖_h ≤ C_α ‖f - f_*‖_{r+1,h} ‖w‖_{r,h}`,
`C_α = 4 B(α) √K`. -/
theorem commutator_diff_norm_le (r : ℕ) (hr : 3 ≤ r) (α : Fin 3 → ℕ) (hα : deg α ≤ r)
    (i : Fin 3) (f w : Grid N → ℂ) (c : ℂ) :
    gridNorm (Dm i (commutator α f w)) + gridNorm (D0 i (commutator α f w)) ≤
      (4 * binomMass α * Real.sqrt Kprod) * sobNorm (r + 1) (f - fun _ => c) * sobNorm r w := by
  set R := Real.sqrt Kprod * sobNorm (r + 1) (f - fun _ => c) * sobNorm r w with hRdef
  have hR : 0 ≤ R := by rw [hRdef]; unfold sobNorm; positivity
  have hDp : gridNorm (Dp i (commutator α f w)) ≤ binomMass α * (2 * R) := by
    rw [commutator_sub_const α f w c, commutator_eq_sum, map_sum]
    simp only [map_nsmul]
    refine (gridNorm_sum_nsmul_le _ _ _ (2 * R) fun β hβ => ?_).trans ?_
    · obtain ⟨hne, hβ'⟩ := mem_erase.mp hβ
      obtain ⟨hd, hle⟩ := deg_sub_of_mem_box hβ'
      have h1 := one_le_deg_of_ne_zero hne
      rw [Dp_mul, S_Sα, Dp_Dα, Dp_Sα_Dα]
      refine (gridNorm_add_le _ _).trans ?_
      have t1 := term_norm_le (f - fun _ => c) w β (α - β + Pi.single i 1)
        (α - β + Pi.single i 1) (r + 1) r (by omega) (by rw [deg_add_single]; omega)
        (by rw [deg_add_single]; omega)
      have t2 := term_norm_le (f - fun _ => c) w (β + Pi.single i 1) (α - β) (α - β)
        (r + 1) r (by rw [deg_add_single]; omega) (by omega) (by rw [deg_add_single]; omega)
      rw [← hRdef] at t1 t2
      linarith
    · have hm : ∑ β ∈ (box α).erase 0, (mchoose α β : ℝ) ≤ binomMass α :=
        sum_le_sum_of_subset_of_nonneg (erase_subset _ _) (fun _ _ _ => Nat.cast_nonneg _)
      exact mul_le_mul_of_nonneg_right hm (by linarith)
  have hB := binomMass_nonneg α
  calc gridNorm (Dm i (commutator α f w)) + gridNorm (D0 i (commutator α f w))
      ≤ gridNorm (Dp i (commutator α f w)) + gridNorm (Dp i (commutator α f w)) := by
        rw [gridNorm_Dm_eq]; linarith [gridNorm_D0_le i (commutator α f w)]
    _ ≤ binomMass α * (2 * R) + binomMass α * (2 * R) := add_le_add hDp hDp
    _ = _ := by rw [hRdef]; ring

/-- `lem:supp-open-calculus`, uniform constants: for `r ≥ 3` there is one constant `C_r`,
independent of the mesh `h = 1/N`, such that for every `N`, every multi-index `|α| ≤ r`,
every coefficient `f`, every constant `f_*` and every `w`: the grid norms form a product
algebra, and the shifted commutator obeys both lines of `eq:supp-open-commutator-bounds`. -/
theorem uniform_sobolev_calculus (r : ℕ) (hr : 3 ≤ r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) [NeZero N],
      (∀ f w : Grid N → ℂ, sobSq r (f * w) ≤ C * sobSq r f * sobSq r w) ∧
      ∀ α : Fin 3 → ℕ, deg α ≤ r → ∀ (f w : Grid N → ℂ) (c : ℂ) (i : Fin 3),
        gridNorm (commutator α f w) ≤ C * sobNorm r (f - fun _ => c) * sobNorm (r - 1) w ∧
        gridNorm (Dm i (commutator α f w)) + gridNorm (D0 i (commutator α f w)) ≤
          C * sobNorm (r + 1) (f - fun _ => c) * sobNorm r w := by
  set C1 := Kprod * ∑ α ∈ multiIndices r, binomMass α ^ 2
  set C2 := ∑ α ∈ multiIndices r, 4 * binomMass α * Real.sqrt Kprod
  have hC1 : 0 ≤ C1 := mul_nonneg Kprod_nonneg (sum_nonneg fun _ _ => sq_nonneg _)
  have hC2 : 0 ≤ C2 := sum_nonneg fun α _ => by
    have := binomMass_nonneg α; positivity
  refine ⟨max C1 C2, le_max_of_le_left hC1, fun N _ => ⟨fun f w => ?_, fun α hα f w c i => ?_⟩⟩
  · refine (sobSq_mul_le r (by omega) f w).trans ?_
    have := sobSq_nonneg r f; have := sobSq_nonneg r w
    gcongr
    exact le_max_left _ _
  · have hmem : α ∈ multiIndices r := mem_multiIndices.mpr hα
    have hle : 4 * binomMass α * Real.sqrt Kprod ≤ max C1 C2 := by
      refine le_trans ?_ (le_max_right _ _)
      exact single_le_sum (f := fun α => 4 * binomMass α * Real.sqrt Kprod)
        (fun β _ => by have := binomMass_nonneg β; positivity) hmem
    have hB := binomMass_nonneg α
    have hK := Real.sqrt_nonneg Kprod
    have n1 : 0 ≤ sobNorm r (f - fun _ => c) := Real.sqrt_nonneg _
    have n2 : 0 ≤ sobNorm (r - 1) w := Real.sqrt_nonneg _
    have n3 : 0 ≤ sobNorm (r + 1) (f - fun _ => c) := Real.sqrt_nonneg _
    have n4 : 0 ≤ sobNorm r w := Real.sqrt_nonneg _
    constructor
    · refine (commutator_norm_le r hr α hα f w c).trans ?_
      have : binomMass α * Real.sqrt Kprod ≤ max C1 C2 := by nlinarith
      gcongr
    · refine (commutator_diff_norm_le r hr α hα i f w c).trans ?_
      gcongr

end RenewalGeometry.PeriodicGridSobolev
