/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Canonical Lyapunov metric for a stable one-way provenance
  quotient (`thm:one-way-provenance-Lyapunov`,
  Gran-Tensor manuscript)

* `one_way_provenance_power`: for the one-way transfer
  `R = [[A, 0], [C, D]]`:
  (i) the exact block power formula
      `Rⁿ = [[Aⁿ, 0], [∑_j D^{n-1-j} C A^j, Dⁿ]]`;
  (ii) the scalar summation estimate
      `n q^{n-1} ≤ rⁿ/(r-q)` for `q = max{a,d} < r`;
  (iii) the boxed uniform corner bound
      `‖∑_j D^{n-1-j} C A^j‖ ≤ M_A M_D c rⁿ/(r-q)` —
      no smallness of `C` required.

* `lyapunov_metric`: for any transfer with a uniform power
  bound `‖Rⁿ‖ ≤ M rⁿ` (`r < 1`):
  (a) the boxed word-Gram series
      `H = ∑ₙ R*ⁿRⁿ` converges (as a `HasSum`);
  (b) the boxed Stein/Lyapunov identity `H - R*HR = I`;
  (c) `H` is the unique solution;
  (d) the boxed conditioning window
      `I ⪯ H ⪯ M²/(1-r²) I`;
  (e) the boxed coercive contraction
      `R*HR ⪯ (1-γ*)H`, `γ* = (1-r²)/M²`;
  (f) the truncation tail bound
      `‖H - H_N‖ ≤ M² r^{2N+2}/(1-r²)`.

The aggregation of the three block bounds of
`one_way_provenance_power` into the single constant
`M_R = max{1, M_A + M_D + M_A M_D c/(r-q)}` with
`‖Rⁿ‖ ≤ M_R rⁿ` is the manuscript's `ℓ¹`-over-blocks
bookkeeping feeding hypothesis `hpow` of `lyapunov_metric`;
the uniformity in the cutoff `X` is the statement that all
constants are explicit and cutoff-free.
-/

open Matrix Filter
open scoped ComplexOrder MatrixOrder Norms.L2Operator

set_option linter.unusedSimpArgs false
set_option linter.style.show false

namespace NCG

/-- `thm:one-way-provenance-Lyapunov`, block power formula
and the boxed corner bound. -/
theorem one_way_provenance_power {l e : Type*} [Fintype l]
    [Fintype e] [DecidableEq l] [DecidableEq e]
    (A : Matrix l l ℂ) (C : Matrix e l ℂ) (D : Matrix e e ℂ)
    (MA MD c a d r : ℝ)
    (hA : ∀ n, ‖A ^ n‖ ≤ MA * a ^ n)
    (hD : ∀ n, ‖D ^ n‖ ≤ MD * d ^ n)
    (hC : ‖C‖ ≤ c)
    (ha : 0 ≤ a) (hd : 0 ≤ d) (hMA : 0 ≤ MA) (hMD : 0 ≤ MD)
    (hc0 : 0 ≤ c) (hq : max a d < r) (_hr1 : r < 1) :
    -- (i) exact one-way block power formula
    (∀ n, fromBlocks A 0 C D ^ n
      = fromBlocks (A ^ n) 0
          (∑ j ∈ Finset.range n, D ^ (n - 1 - j) * C * A ^ j)
          (D ^ n))
    -- (ii) the scalar summation estimate
    ∧ (∀ n : ℕ,
        (n : ℝ) * max a d ^ (n - 1)
          ≤ r ^ n / (r - max a d))
    -- (iii) the boxed uniform corner bound
    ∧ (∀ n, ‖∑ j ∈ Finset.range n,
          D ^ (n - 1 - j) * C * A ^ j‖
        ≤ MA * MD * c / (r - max a d) * r ^ n) := by
  set q : ℝ := max a d with hqdef
  have hq0 : 0 ≤ q := le_trans ha (le_max_left a d)
  have hrq : 0 < r - q := by linarith
  have hr0 : 0 < r := lt_of_le_of_lt hq0 hq
  -- (i)
  have hblock : ∀ n, fromBlocks A 0 C D ^ n
      = fromBlocks (A ^ n) 0
          (∑ j ∈ Finset.range n, D ^ (n - 1 - j) * C * A ^ j)
          (D ^ n) := by
    intro n
    induction n with
    | zero =>
      simp [Matrix.fromBlocks_one]
    | succ n ih =>
      rw [pow_succ', ih, Matrix.fromBlocks_multiply]
      congr 1
      · rw [Matrix.zero_mul, add_zero, ← pow_succ']
      · rw [Matrix.mul_zero, Matrix.zero_mul, add_zero]
      · rw [Finset.sum_range_succ]
        have hshift : ∑ j ∈ Finset.range n,
            D ^ (n + 1 - 1 - j) * C * A ^ j
            = D * ∑ j ∈ Finset.range n,
                D ^ (n - 1 - j) * C * A ^ j := by
          rw [Matrix.mul_sum]
          refine Finset.sum_congr rfl fun j hj => ?_
          have hjn : j < n := Finset.mem_range.mp hj
          have harith : n + 1 - 1 - j = (n - 1 - j) + 1 := by
            omega
          rw [harith, pow_succ']
          simp only [Matrix.mul_assoc]
        rw [hshift]
        have hlast : D ^ (n + 1 - 1 - n) * C * A ^ n
            = C * A ^ n := by
          have : n + 1 - 1 - n = 0 := by omega
          rw [this, pow_zero, Matrix.one_mul]
        rw [hlast, add_comm]
      · rw [Matrix.mul_zero, zero_add, ← pow_succ']
  -- (ii)
  have hscalar : ∀ n : ℕ,
      (n : ℝ) * q ^ (n - 1) ≤ r ^ n / (r - q) := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp only [Nat.cast_zero, zero_mul, pow_zero]
      positivity
    have hqr : q / r < 1 := (div_lt_one hr0).mpr hq
    have hqr0 : 0 ≤ q / r := div_nonneg hq0 hr0.le
    have h1 : (n : ℝ) * q ^ (n - 1)
        ≤ ∑ j ∈ Finset.range n, q ^ j * r ^ (n - 1 - j) := by
      have hconst : (n : ℝ) * q ^ (n - 1)
          = ∑ _j ∈ Finset.range n, q ^ (n - 1) := by
        rw [Finset.sum_const, Finset.card_range,
          nsmul_eq_mul]
      rw [hconst]
      refine Finset.sum_le_sum fun j hj => ?_
      have hjn : j < n := Finset.mem_range.mp hj
      have hqq : q ^ (n - 1) = q ^ j * q ^ (n - 1 - j) := by
        rw [← pow_add]
        congr 1
        omega
      rw [hqq]
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hq0 (le_of_lt hq) _)
        (pow_nonneg hq0 j)
    have h2 : ∑ j ∈ Finset.range n, q ^ j * r ^ (n - 1 - j)
        ≤ r ^ (n - 1) * (1 - q / r)⁻¹ := by
      have hterm : ∀ j ∈ Finset.range n,
          q ^ j * r ^ (n - 1 - j)
            = r ^ (n - 1) * (q / r) ^ j := by
        intro j hj
        have hjn : j < n := Finset.mem_range.mp hj
        have hrr : r ^ (n - 1) = r ^ (n - 1 - j) * r ^ j := by
          rw [← pow_add]
          congr 1
          omega
        rw [div_pow, hrr]
        field_simp
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_
        (pow_nonneg hr0.le _)
      have hsummable :=
        summable_geometric_of_lt_one hqr0 hqr
      calc ∑ j ∈ Finset.range n, (q / r) ^ j
          ≤ ∑' j : ℕ, (q / r) ^ j :=
            hsummable.sum_le_tsum _
              (fun j _ => pow_nonneg hqr0 j)
        _ = (1 - q / r)⁻¹ := tsum_geometric_of_lt_one hqr0 hqr
    have h3 : r ^ (n - 1) * (1 - q / r)⁻¹
        = r ^ n / (r - q) := by
      have hrn : r ^ n = r ^ (n - 1) * r := by
        rw [← pow_succ]
        congr 1
        omega
      rw [hrn]
      have hne : (1 : ℝ) - q / r ≠ 0 := by
        have h0 : 0 < 1 - q / r := by
          have hqr : q / r < 1 := (div_lt_one hr0).mpr hq
          linarith
        exact ne_of_gt h0
      field_simp
    calc (n : ℝ) * q ^ (n - 1)
        ≤ ∑ j ∈ Finset.range n, q ^ j * r ^ (n - 1 - j) := h1
      _ ≤ r ^ (n - 1) * (1 - q / r)⁻¹ := h2
      _ = r ^ n / (r - q) := h3
  refine ⟨hblock, hscalar, ?_⟩
  -- (iii)
  intro n
  have hstep : ∀ j ∈ Finset.range n,
      ‖D ^ (n - 1 - j) * C * A ^ j‖
        ≤ MA * MD * c * q ^ (n - 1) := by
    intro j hj
    have hjn : j < n := Finset.mem_range.mp hj
    have h1 : ‖D ^ (n - 1 - j) * C * A ^ j‖
        ≤ ‖D ^ (n - 1 - j)‖ * ‖C‖ * ‖A ^ j‖ := by
      calc ‖D ^ (n - 1 - j) * C * A ^ j‖
          ≤ ‖D ^ (n - 1 - j) * C‖ * ‖A ^ j‖ :=
            Matrix.l2_opNorm_mul _ _
        _ ≤ ‖D ^ (n - 1 - j)‖ * ‖C‖ * ‖A ^ j‖ :=
            mul_le_mul_of_nonneg_right
              (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
    have h2 : ‖D ^ (n - 1 - j)‖ * ‖C‖ * ‖A ^ j‖
        ≤ (MD * d ^ (n - 1 - j)) * c * (MA * a ^ j) := by
      have hDn := hD (n - 1 - j)
      have hAn := hA j
      have hd0 : (0 : ℝ) ≤ MD * d ^ (n - 1 - j) :=
        mul_nonneg hMD (pow_nonneg hd _)
      exact mul_le_mul
        (mul_le_mul hDn hC (norm_nonneg _) hd0)
        hAn (norm_nonneg _)
        (mul_nonneg hd0 hc0)
    have h3 : (MD * d ^ (n - 1 - j)) * c * (MA * a ^ j)
        ≤ MA * MD * c * q ^ (n - 1) := by
      have hda : d ^ (n - 1 - j) * a ^ j ≤ q ^ (n - 1) := by
        have hqq2 : q ^ (n - 1 - j) * q ^ j = q ^ (n - 1) := by
          rw [← pow_add]
          congr 1
          omega
        calc d ^ (n - 1 - j) * a ^ j
            ≤ q ^ (n - 1 - j) * q ^ j :=
              mul_le_mul
                (pow_le_pow_left₀ hd (le_max_right a d) _)
                (pow_le_pow_left₀ ha (le_max_left a d) _)
                (pow_nonneg ha j)
                (pow_nonneg (le_trans hd (le_max_right a d)) _)
          _ = q ^ (n - 1) := hqq2
      calc (MD * d ^ (n - 1 - j)) * c * (MA * a ^ j)
          = MA * MD * c * (d ^ (n - 1 - j) * a ^ j) := by
            ring
        _ ≤ MA * MD * c * q ^ (n - 1) :=
            mul_le_mul_of_nonneg_left hda
              (by positivity)
    linarith
  calc ‖∑ j ∈ Finset.range n, D ^ (n - 1 - j) * C * A ^ j‖
      ≤ ∑ j ∈ Finset.range n,
          ‖D ^ (n - 1 - j) * C * A ^ j‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _j ∈ Finset.range n,
          MA * MD * c * q ^ (n - 1) :=
        Finset.sum_le_sum hstep
    _ = (n : ℝ) * (MA * MD * c * q ^ (n - 1)) := by
        rw [Finset.sum_const, Finset.card_range,
          nsmul_eq_mul]
    _ ≤ MA * MD * c / (r - q) * r ^ n := by
        have hs := hscalar n
        have hcc : (0 : ℝ) ≤ MA * MD * c := by positivity
        calc (n : ℝ) * (MA * MD * c * q ^ (n - 1))
            = MA * MD * c * ((n : ℝ) * q ^ (n - 1)) := by
              ring
          _ ≤ MA * MD * c * (r ^ n / (r - q)) :=
              mul_le_mul_of_nonneg_left hs hcc
          _ = MA * MD * c / (r - q) * r ^ n := by
              field_simp

set_option maxHeartbeats 1000000 in
-- the word-Gram series and its Loewner clauses elaborate
-- large tsum terms; raise the elaboration budget
/-- `thm:one-way-provenance-Lyapunov`, the canonical
Lyapunov metric from a uniform power bound. -/
theorem lyapunov_metric {m : Type*} [Fintype m]
    [DecidableEq m] (R : Matrix m m ℂ) (M r : ℝ)
    (hM : 1 ≤ M) (hr0 : 0 ≤ r) (hr : r < 1)
    (hpow : ∀ n, ‖R ^ n‖ ≤ M * r ^ n) :
    ∃ H : Matrix m m ℂ,
      -- (a) the boxed word-Gram series
      HasSum (fun n => (R ^ n)ᴴ * R ^ n) H
      -- (b) the boxed Stein/Lyapunov identity
      ∧ H - Rᴴ * H * R = 1
      -- (c) uniqueness
      ∧ (∀ H' : Matrix m m ℂ,
          H' - Rᴴ * H' * R = 1 → H' = H)
      -- (d) the boxed conditioning window
      ∧ (H - 1).PosSemidef
      ∧ (((M ^ 2 / (1 - r ^ 2) : ℝ) : ℂ) • 1 - H).PosSemidef
      -- (e) the boxed coercive contraction
      ∧ (((1 - (1 - r ^ 2) / M ^ 2 : ℝ) : ℂ) • H
          - Rᴴ * H * R).PosSemidef
      -- (f) the truncation tail bound
      ∧ (∀ N, ‖H - ∑ n ∈ Finset.range (N + 1),
            (R ^ n)ᴴ * R ^ n‖
          ≤ M ^ 2 * r ^ (2 * N + 2) / (1 - r ^ 2)) := by
  have hM0 : (0 : ℝ) < M := lt_of_lt_of_le one_pos hM
  have hr2 : r ^ 2 < 1 := by nlinarith
  have hr20 : (0 : ℝ) ≤ r ^ 2 := sq_nonneg r
  have h1r2 : (0 : ℝ) < 1 - r ^ 2 := by linarith
  set g : ℕ → Matrix m m ℂ :=
    fun n => (R ^ n)ᴴ * R ^ n with hgdef
  -- norm bound on the summands
  have hgnorm : ∀ n, ‖g n‖ ≤ M ^ 2 * (r ^ 2) ^ n := by
    intro n
    have h1 : ‖g n‖ = ‖R ^ n‖ * ‖R ^ n‖ :=
      Matrix.l2_opNorm_conjTranspose_mul_self _
    rw [h1]
    calc ‖R ^ n‖ * ‖R ^ n‖
        ≤ (M * r ^ n) * (M * r ^ n) :=
          mul_le_mul (hpow n) (hpow n) (norm_nonneg _)
            (by positivity)
      _ = M ^ 2 * (r ^ 2) ^ n := by
          rw [← pow_mul, mul_comm 2 n, pow_mul]
          ring
  have hgeo := summable_geometric_of_lt_one hr20 hr2
  have hsummable : Summable g :=
    Summable.of_norm_bounded (hgeo.mul_left (M ^ 2)) hgnorm
  set H : Matrix m m ℂ := ∑' n, g n with hHdef
  have hH : HasSum g H := hsummable.hasSum
  -- the conjugation operator as a continuous linear map
  let Φ : Matrix m m ℂ →ₗ[ℂ] Matrix m m ℂ :=
    { toFun := fun X => Rᴴ * X * R
      map_add' := fun X Y => by
        simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun t X => by
        simp [Matrix.mul_smul, Matrix.smul_mul] }
  have hshift : ∀ n, g (n + 1) = Φ (g n) := by
    intro n
    show (R ^ (n + 1))ᴴ * R ^ (n + 1)
      = Rᴴ * ((R ^ n)ᴴ * R ^ n) * R
    rw [pow_succ, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  have hmap : HasSum (fun n => g (n + 1)) (Rᴴ * H * R) := by
    have h :=
      hH.mapL (LinearMap.toContinuousLinearMap Φ)
    simp only [LinearMap.coe_toContinuousLinearMap'] at h
    exact HasSum.congr_fun h (fun n => hshift n)
  have htail : HasSum (fun n => g (n + 1)) (H - g 0) := by
    have h := (hasSum_nat_add_iff' 1).mpr hH
    simpa using h
  have hg0 : g 0 = 1 := by
    show (R ^ 0)ᴴ * R ^ 0 = 1
    simp
  -- (b) the Stein identity
  have hidentity : H - Rᴴ * H * R = 1 := by
    have huniq := hmap.unique htail
    rw [hg0] at huniq
    have : Rᴴ * H * R = H - 1 := huniq
    rw [this]
    abel
  -- quadratic form of H as a convergent series
  have hquad : ∀ x : m → ℂ,
      HasSum (fun n => star x ⬝ᵥ (g n *ᵥ x))
        (star x ⬝ᵥ (H *ᵥ x)) := by
    intro x
    let φ : Matrix m m ℂ →ₗ[ℂ] ℂ :=
      { toFun := fun X => star x ⬝ᵥ (X *ᵥ x)
        map_add' := fun X Y => by
          simp [Matrix.add_mulVec]
        map_smul' := fun t X => by
          simp [Matrix.smul_mulVec] }
    have h := hH.mapL (LinearMap.toContinuousLinearMap φ)
    simp only [LinearMap.coe_toContinuousLinearMap',
      LinearMap.coe_mk, AddHom.coe_mk] at h
    exact h
  have hgquad : ∀ (n : ℕ) (x : m → ℂ),
      star x ⬝ᵥ (g n *ᵥ x)
        = star (R ^ n *ᵥ x) ⬝ᵥ (R ^ n *ᵥ x) := by
    intro n x
    show star x ⬝ᵥ (((R ^ n)ᴴ * R ^ n) *ᵥ x) = _
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      ← Matrix.star_mulVec]
  -- H is hermitian
  have hHherm : Hᴴ = H := by
    let ψ : Matrix m m ℂ →ₗ[ℝ] Matrix m m ℂ :=
      { toFun := fun X => Xᴴ
        map_add' := fun X Y => Matrix.conjTranspose_add X Y
        map_smul' := fun t X => by
          simp [Matrix.conjTranspose_smul] }
    have h := hH.mapL (LinearMap.toContinuousLinearMap ψ)
    simp only [LinearMap.coe_toContinuousLinearMap',
      LinearMap.coe_mk, AddHom.coe_mk] at h
    have h' : HasSum g Hᴴ := by
      refine HasSum.congr_fun h fun n => ?_
      have hgh : ((R ^ n)ᴴ * R ^ n)ᴴ
          = (R ^ n)ᴴ * R ^ n := by
        rw [Matrix.conjTranspose_mul,
          Matrix.conjTranspose_conjTranspose]
      exact hgh.symm
    exact h'.unique hH
  have hHpsd : H.PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      hHherm fun x => ?_
    have hterm : ∀ n, 0 ≤ star x ⬝ᵥ (g n *ᵥ x) := by
      intro n
      rw [hgquad n x]
      exact dotProduct_star_self_nonneg _
    exact hasSum_le (fun n => hterm n) hasSum_zero (hquad x)
  -- summability of the norms (for the tail bound)
  have hsumnorm : Summable fun n => ‖g n‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      hgnorm (hgeo.mul_left (M ^ 2))
  -- dot products as Euclidean norms
  have hy : ∀ v : m → ℂ, star v ⬝ᵥ v
      = ((‖(WithLp.toLp 2 v : EuclideanSpace ℂ m)‖ : ℝ) : ℂ)
        ^ 2 := by
    intro v
    rw [dotProduct_comm, ← EuclideanSpace.inner_toLp_toLp,
      inner_self_eq_norm_sq_to_K]
    rfl
  -- the per-term quadratic bound
  have hquadbound : ∀ (n : ℕ) (x : m → ℂ),
      star x ⬝ᵥ (g n *ᵥ x)
        ≤ ((M ^ 2 * (r ^ 2) ^ n : ℝ) : ℂ)
            * (star x ⬝ᵥ x) := by
    intro n x
    rw [hgquad n x, hy, hy]
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow,
      ← Complex.ofReal_mul, Complex.real_le_real]
    have hb : ‖(WithLp.toLp 2 (R ^ n *ᵥ x) :
          EuclideanSpace ℂ m)‖
        ≤ ‖R ^ n‖ * ‖(WithLp.toLp 2 x :
          EuclideanSpace ℂ m)‖ :=
      Matrix.l2_opNorm_mulVec (R ^ n) (WithLp.toLp 2 x)
    have hp := hpow n
    have h0 : (0 : ℝ) ≤ ‖(WithLp.toLp 2 (R ^ n *ᵥ x) :
        EuclideanSpace ℂ m)‖ := norm_nonneg _
    have h1 : (0 : ℝ) ≤ ‖(WithLp.toLp 2 x :
        EuclideanSpace ℂ m)‖ := norm_nonneg _
    have hbb : ‖(WithLp.toLp 2 (R ^ n *ᵥ x) :
          EuclideanSpace ℂ m)‖
        ≤ M * r ^ n
          * ‖(WithLp.toLp 2 x : EuclideanSpace ℂ m)‖ := by
      calc ‖(WithLp.toLp 2 (R ^ n *ᵥ x) :
            EuclideanSpace ℂ m)‖
          ≤ ‖R ^ n‖
            * ‖(WithLp.toLp 2 x : EuclideanSpace ℂ m)‖ :=
            hb
        _ ≤ M * r ^ n
            * ‖(WithLp.toLp 2 x : EuclideanSpace ℂ m)‖ :=
            mul_le_mul_of_nonneg_right hp h1
    calc ‖(WithLp.toLp 2 (R ^ n *ᵥ x) :
          EuclideanSpace ℂ m)‖ ^ 2
        ≤ (M * r ^ n
            * ‖(WithLp.toLp 2 x : EuclideanSpace ℂ m)‖)
            ^ 2 := by
          have h := mul_le_mul hbb hbb h0 (by positivity)
          simpa [pow_two] using h
      _ = M ^ 2 * (r ^ 2) ^ n
          * ‖(WithLp.toLp 2 x : EuclideanSpace ℂ m)‖
            ^ 2 := by
          ring
  -- (d) upper window
  have hupper : (((M ^ 2 / (1 - r ^ 2) : ℝ) : ℂ) • 1
      - H).PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      ?_ fun x => ?_
    · show (((M ^ 2 / (1 - r ^ 2) : ℝ) : ℂ) • 1 - H)ᴴ = _
      rw [Matrix.conjTranspose_sub,
        Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
        hHherm, Complex.star_def, Complex.conj_ofReal]
    · have hgr : HasSum (fun n => M ^ 2 * (r ^ 2) ^ n)
          (M ^ 2 / (1 - r ^ 2)) := by
        have h :=
          (hasSum_geometric_of_lt_one hr20 hr2).mul_left
            (M ^ 2)
        simpa [div_eq_mul_inv] using h
      have hC := hgr.mapL Complex.ofRealCLM
      have hgeoC : HasSum
          (fun n => ((M ^ 2 * (r ^ 2) ^ n : ℝ) : ℂ)
            * (star x ⬝ᵥ x))
          (((M ^ 2 / (1 - r ^ 2) : ℝ) : ℂ)
            * (star x ⬝ᵥ x)) := by
        simpa using hC.mul_right (star x ⬝ᵥ x)
      have hle := hasSum_le
        (fun n => hquadbound n x) (hquad x) hgeoC
      have hexp : star x ⬝ᵥ
          (((((M ^ 2 / (1 - r ^ 2) : ℝ) : ℂ) • 1 - H))
            *ᵥ x)
          = ((M ^ 2 / (1 - r ^ 2) : ℝ) : ℂ)
              * (star x ⬝ᵥ x)
            - star x ⬝ᵥ (H *ᵥ x) := by
      -- expand the affine quadratic form
        rw [Matrix.sub_mulVec, Matrix.smul_mulVec,
          Matrix.one_mulVec, dotProduct_sub,
          dotProduct_smul, smul_eq_mul]
      rw [hexp]
      exact sub_nonneg.mpr hle
  -- (e) the coercive contraction
  have hRHR : Rᴴ * H * R = H - 1 := by
    have h := sub_eq_iff_eq_add.mp hidentity
    nth_rewrite 2 [h]
    abel
  have hcoercive : (((1 - (1 - r ^ 2) / M ^ 2 : ℝ) : ℂ) • H
      - Rᴴ * H * R).PosSemidef := by
    set γ : ℝ := (1 - r ^ 2) / M ^ 2 with hγdef
    have hγ0 : 0 ≤ γ := by positivity
    have hkey : ((1 - γ : ℝ) : ℂ) • H - Rᴴ * H * R
        = 1 - ((γ : ℝ) : ℂ) • H := by
      rw [hRHR, Complex.ofReal_sub, Complex.ofReal_one,
        sub_smul, one_smul]
      abel
    rw [hkey]
    have hγc : ((γ : ℝ) : ℂ)
        * ((M ^ 2 / (1 - r ^ 2) : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, ← Complex.ofReal_one]
      congr 1
      rw [hγdef]
      field_simp
    have hfactor : (1 : Matrix m m ℂ) - ((γ : ℝ) : ℂ) • H
        = ((γ : ℝ) : ℂ)
            • (((M ^ 2 / (1 - r ^ 2) : ℝ) : ℂ) • 1 - H) := by
      rw [smul_sub, smul_smul, hγc, one_smul]
    rw [hfactor]
    refine hupper.smul ?_
    rw [Complex.zero_le_real]
    exact hγ0
  -- (c) uniqueness
  have huniq : ∀ H' : Matrix m m ℂ,
      H' - Rᴴ * H' * R = 1 → H' = H := by
    intro H' hH'
    set K : Matrix m m ℂ := H' - H with hKdef
    have hKrec : K = Rᴴ * K * R := by
      have hzero : K - Rᴴ * K * R = 0 := by
        rw [hKdef]
        calc H' - H - Rᴴ * (H' - H) * R
            = (H' - Rᴴ * H' * R) - (H - Rᴴ * H * R) := by
              simp only [Matrix.mul_sub, Matrix.sub_mul]
              abel
          _ = 0 := by rw [hH', hidentity, sub_self]
      have := sub_eq_zero.mp hzero
      exact this
    have hKn : ∀ n, K = (R ^ n)ᴴ * K * R ^ n := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have step : Rᴴ * ((R ^ n)ᴴ * K * R ^ n) * R
            = (R ^ (n + 1))ᴴ * K * R ^ (n + 1) := by
          rw [pow_succ, Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
        calc K = Rᴴ * K * R := hKrec
          _ = Rᴴ * ((R ^ n)ᴴ * K * R ^ n) * R := by
              rw [← ih]
          _ = (R ^ (n + 1))ᴴ * K * R ^ (n + 1) := step
    have hKnorm : ∀ n,
        ‖K‖ ≤ M ^ 2 * (r ^ 2) ^ n * ‖K‖ := by
      intro n
      calc ‖K‖ = ‖(R ^ n)ᴴ * K * R ^ n‖ := by
            rw [← hKn n]
        _ ≤ ‖(R ^ n)ᴴ * K‖ * ‖R ^ n‖ :=
            Matrix.l2_opNorm_mul _ _
        _ ≤ ‖(R ^ n)ᴴ‖ * ‖K‖ * ‖R ^ n‖ :=
            mul_le_mul_of_nonneg_right
              (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
        _ = ‖R ^ n‖ * ‖K‖ * ‖R ^ n‖ := by
            rw [Matrix.l2_opNorm_conjTranspose]
        _ ≤ (M * r ^ n) * ‖K‖ * (M * r ^ n) := by
            have h := hpow n
            have h0 : (0 : ℝ) ≤ ‖K‖ := norm_nonneg _
            have h1 : (0 : ℝ) ≤ ‖R ^ n‖ := norm_nonneg _
            have hb : (0 : ℝ) ≤ M * r ^ n := by positivity
            have hx2 : ‖R ^ n‖ * ‖R ^ n‖
                ≤ (M * r ^ n) * (M * r ^ n) :=
              mul_le_mul h h h1 hb
            nlinarith [hx2, h0]
        _ = M ^ 2 * (r ^ 2) ^ n * ‖K‖ := by
            rw [← pow_mul, mul_comm 2 n, pow_mul]
            ring
    have hlim : Tendsto
        (fun n => M ^ 2 * (r ^ 2) ^ n * ‖K‖) atTop
        (nhds 0) := by
      have h :=
        tendsto_pow_atTop_nhds_zero_of_lt_one hr20 hr2
      have h2 := (h.const_mul (M ^ 2)).mul_const ‖K‖
      simpa using h2
    have hK0 : ‖K‖ ≤ 0 :=
      le_of_tendsto_of_tendsto tendsto_const_nhds hlim
        (Filter.Eventually.of_forall hKnorm)
    have hKzero : K = 0 :=
      norm_eq_zero.mp (le_antisymm hK0 (norm_nonneg K))
    have := hKzero
    rw [hKdef] at this
    exact sub_eq_zero.mp this
  -- (f) the truncation tail bound
  have htailbound : ∀ N,
      ‖H - ∑ n ∈ Finset.range (N + 1), g n‖
        ≤ M ^ 2 * r ^ (2 * N + 2) / (1 - r ^ 2) := by
    intro N
    have hsplit := hsummable.sum_add_tsum_nat_add (N + 1)
    have hrest : H - ∑ n ∈ Finset.range (N + 1), g n
        = ∑' n, g (n + (N + 1)) := by
      rw [hHdef, ← hsplit]
      abel
    rw [hrest]
    have htails : Summable fun n => ‖g (n + (N + 1))‖ :=
      (summable_nat_add_iff (N + 1)).mpr hsumnorm
    have hmaj : Summable fun n : ℕ =>
        M ^ 2 * (r ^ 2) ^ (n + (N + 1)) :=
      (summable_nat_add_iff (N + 1)).mpr
        (hgeo.mul_left (M ^ 2))
    have hclosed : ∑' n : ℕ, M ^ 2 * (r ^ 2) ^ (n + (N + 1))
        = M ^ 2 * (r ^ 2) ^ (N + 1) / (1 - r ^ 2) := by
      have hterm : ∀ n : ℕ,
          M ^ 2 * (r ^ 2) ^ (n + (N + 1))
            = M ^ 2 * (r ^ 2) ^ (N + 1) * (r ^ 2) ^ n := by
        intro n
        rw [pow_add]
        ring
      rw [tsum_congr hterm, tsum_mul_left,
        tsum_geometric_of_lt_one hr20 hr2, div_eq_mul_inv]
    calc ‖∑' n, g (n + (N + 1))‖
        ≤ ∑' n, ‖g (n + (N + 1))‖ :=
          norm_tsum_le_tsum_norm htails
      _ ≤ ∑' n : ℕ, M ^ 2 * (r ^ 2) ^ (n + (N + 1)) :=
          htails.tsum_le_tsum
            (fun n => hgnorm (n + (N + 1))) hmaj
      _ = M ^ 2 * (r ^ 2) ^ (N + 1) / (1 - r ^ 2) := hclosed
      _ = M ^ 2 * r ^ (2 * N + 2) / (1 - r ^ 2) := by
          rw [← pow_mul]
          ring_nf
  -- (d) lower window
  have hlower : (H - 1).PosSemidef := by
    have h : H - 1 = Rᴴ * H * R := by
      rw [hRHR]
    rw [h]
    exact hHpsd.conjTranspose_mul_mul_same R
  exact ⟨H, hH, hidentity, huniq, hlower, hupper,
    hcoercive, htailbound⟩

end NCG
