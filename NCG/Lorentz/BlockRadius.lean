/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Lorentz.SubmatrixRadius

/-!
# Super-solutions and the growth rate

Collatz–Wielandt **upper** characterization of the Gelfand–Fekete
growth rate, eigenvector-free:

* `pRad_le_of_supersolution` — a positive super-solution
  `Bv ≤ μv` forces `pRad B ≤ μ` (powers propagate the bound and the
  entry-sum gauge is sandwiched);
* `exists_supersolution` — conversely, for every `μ > pRad B` there
  is a super-solution `v ≥ 1`: the truncated resolvent
  `v = Σ_{k ≤ K} μ^{-k} B^k 𝟙` works once
  `entrySum(B^{K+1}) ≤ μ^{K+1}`, which the growth limit supplies.

These are the tools for the block upper bound of
`prop:terminal-component` (ii) in `NCG/Lorentz/BlockRadius.lean`
(second half).
-/

namespace NCG

open Filter

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-- Nonnegative matrices act monotonically. -/
theorem mulVec_mono {B : Matrix V V ℝ} (hB : EntryNonneg B)
    {u v : V → ℝ} (huv : ∀ x, u x ≤ v x) (x : V) :
    B.mulVec u x ≤ B.mulVec v x := by
  rw [Matrix.mulVec, Matrix.mulVec, dotProduct, dotProduct]
  exact Finset.sum_le_sum fun y _ =>
    mul_le_mul_of_nonneg_left (huv y) (hB x y)

/-- A super-solution propagates through powers:
`B^k v ≤ μ^k v`. -/
theorem pow_mulVec_le_of_supersolution {B : Matrix V V ℝ}
    (hB : EntryNonneg B) {μ : ℝ} (hμ : 0 ≤ μ) {v : V → ℝ}
    (hv : ∀ x, 0 ≤ v x)
    (hsup : ∀ x, B.mulVec v x ≤ μ * v x) :
    ∀ (k : ℕ) (x : V), (B ^ k).mulVec v x ≤ μ ^ k * v x := by
  intro k
  induction k with
  | zero =>
    intro x
    rw [pow_zero, pow_zero, Matrix.one_mulVec, one_mul]
  | succ k ih =>
    intro x
    rw [pow_succ']
    rw [← Matrix.mulVec_mulVec]
    have h1 : B.mulVec ((B ^ k).mulVec v) x
        ≤ B.mulVec (fun y => μ ^ k * v y) x :=
      mulVec_mono hB (fun y => ih y) x
    refine le_trans h1 ?_
    have h2 : B.mulVec (fun y => μ ^ k * v y) x
        = μ ^ k * B.mulVec v x := by
      rw [Matrix.mulVec, Matrix.mulVec, dotProduct, dotProduct,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      ring
    rw [h2, pow_succ']
    have h3 : μ ^ k * B.mulVec v x ≤ μ ^ k * (μ * v x) :=
      mul_le_mul_of_nonneg_left (hsup x) (pow_nonneg hμ k)
    calc μ ^ k * B.mulVec v x ≤ μ ^ k * (μ * v x) := h3
      _ = μ * μ ^ k * v x := by ring

/-- **A positive super-solution bounds the growth rate**:
`Bv ≤ μv` with `v > 0` forces `pRad B ≤ μ`. -/
theorem pRad_le_of_supersolution {B : Matrix V V ℝ}
    (hB : EntryNonneg B) (hw : HasDiagWitness B) {μ : ℝ}
    (hμ : 0 < μ) {v : V → ℝ} (hv : ∀ x, 0 < v x)
    (hsup : ∀ x, B.mulVec v x ≤ μ * v x) :
    pRad B ≤ μ := by
  classical
  set vmin := Finset.univ.inf' Finset.univ_nonempty v with hvmin
  set vsum := ∑ x, v x with hvsum
  have hvminpos : 0 < vmin := by
    rw [hvmin, Finset.lt_inf'_iff]
    intro x _
    exact hv x
  have hvsumpos : 0 < vsum := by
    rw [hvsum]
    exact Finset.sum_pos (fun x _ => hv x) Finset.univ_nonempty
  have hbound : ∀ k : ℕ,
      entrySum (B ^ k) ≤ vsum / vmin * μ ^ k := by
    intro k
    have h1 : vmin * entrySum (B ^ k)
        ≤ ∑ x, (B ^ k).mulVec v x := by
      rw [entrySum, Finset.mul_sum]
      refine Finset.sum_le_sum fun x _ => ?_
      rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
      refine Finset.sum_le_sum fun y _ => ?_
      have h2 : vmin ≤ v y := by
        rw [hvmin]
        exact Finset.inf'_le _ (Finset.mem_univ y)
      calc vmin * (B ^ k) x y = (B ^ k) x y * vmin := by ring
        _ ≤ (B ^ k) x y * v y :=
          mul_le_mul_of_nonneg_left h2 (entryNonneg_pow hB k x y)
    have h3 : ∑ x, (B ^ k).mulVec v x ≤ μ ^ k * vsum := by
      rw [hvsum, Finset.mul_sum]
      exact Finset.sum_le_sum fun x _ =>
        pow_mulVec_le_of_supersolution hB hμ.le
          (fun y => (hv y).le) hsup k x
    have h4 : vmin * entrySum (B ^ k) ≤ μ ^ k * vsum :=
      le_trans h1 h3
    rw [div_mul_eq_mul_div, le_div_iff₀ hvminpos]
    calc entrySum (B ^ k) * vmin
        = vmin * entrySum (B ^ k) := by ring
      _ ≤ μ ^ k * vsum := h4
      _ = vsum * μ ^ k := by ring
  -- squeeze the growth limit
  have h5 := tendsto_growthSeq hB hw
  have h6 : Tendsto (fun k : ℕ =>
      (Real.log (vsum / vmin) + k * Real.log μ) / k) atTop
      (nhds (Real.log μ)) := by
    have h7 : Tendsto (fun k : ℕ => Real.log μ
        + Real.log (vsum / vmin) / k) atTop
        (nhds (Real.log μ + 0)) :=
      tendsto_const_nhds.add
        (tendsto_const_div_atTop_nhds_zero_nat _)
    rw [add_zero] at h7
    refine Tendsto.congr' ?_ h7
    filter_upwards [eventually_ne_atTop 0] with k hk
    have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    field_simp
    ring
  have h8 : Real.log (pRad B) ≤ Real.log μ := by
    refine le_of_tendsto_of_tendsto' h5 h6 fun k => ?_
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · have hkR : (0 : ℝ) < k := by exact_mod_cast hk
      rw [div_le_div_iff₀ hkR hkR]
      refine mul_le_mul_of_nonneg_right ?_ hkR.le
      rw [growthSeq]
      have h9 : Real.log (entrySum (B ^ k))
          ≤ Real.log (vsum / vmin * μ ^ k) :=
        Real.log_le_log (entrySum_pow_pos hB hw k) (hbound k)
      rw [Real.log_mul (by positivity) (by positivity),
        Real.log_pow] at h9
      linarith
  rw [← Real.exp_log (pRad_pos B), ← Real.exp_log hμ]
  exact Real.exp_le_exp.mpr h8

/-- **Existence of super-solutions above the growth rate**: for
every `μ > pRad B` the truncated resolvent applied to `𝟙` is a
super-solution bounded below by `1`. -/
theorem exists_supersolution {B : Matrix V V ℝ}
    (hB : EntryNonneg B) (hw : HasDiagWitness B) {μ : ℝ}
    (hμ : pRad B < μ) :
    ∃ v : V → ℝ, (∀ x, 1 ≤ v x)
      ∧ ∀ x, B.mulVec v x ≤ μ * v x := by
  classical
  have hμ0 : 0 < μ := lt_trans (pRad_pos B) hμ
  -- choose K with entrySum(B^{K+1}) ≤ μ^{K+1}
  have h1 := tendsto_growthSeq hB hw
  have h2 : ∀ᶠ k : ℕ in atTop, growthSeq B k / k < Real.log μ :=
    h1.eventually_lt_const (Real.log_lt_log (pRad_pos B) hμ)
  obtain ⟨K₀, hK₀⟩ := h2.exists_forall_of_atTop
  set K := max K₀ 1 with hK
  have hK1 : 1 ≤ K := le_max_right _ _
  have hKle : K₀ ≤ K + 1 := le_trans (le_max_left _ _)
    (Nat.le_succ K)
  have h3 : entrySum (B ^ (K + 1)) ≤ μ ^ (K + 1) := by
    have h4 := hK₀ (K + 1) hKle
    have h5 : (0 : ℝ) < (K + 1 : ℕ) := by positivity
    rw [div_lt_iff₀ h5, growthSeq] at h4
    have h6 : Real.log (entrySum (B ^ (K + 1)))
        < Real.log (μ ^ (K + 1)) := by
      rw [Real.log_pow]
      calc Real.log (entrySum (B ^ (K + 1)))
          < Real.log μ * (K + 1 : ℕ) := h4
        _ = ((K + 1 : ℕ) : ℝ) * Real.log μ := by ring
    have h7 := Real.exp_lt_exp.mpr h6
    rw [Real.exp_log (entrySum_pow_pos hB hw (K + 1)),
      Real.exp_log (by positivity)] at h7
    exact h7.le
  -- the truncated resolvent
  set v : V → ℝ := fun x => ∑ k ∈ Finset.range (K + 1),
    μ⁻¹ ^ k * (B ^ k).mulVec (fun _ => 1) x with hv
  have hones : ∀ (k : ℕ) (x : V),
      0 ≤ (B ^ k).mulVec (fun _ => 1) x := by
    intro k x
    rw [Matrix.mulVec, dotProduct]
    exact Finset.sum_nonneg fun y _ =>
      mul_nonneg (entryNonneg_pow hB k x y) zero_le_one
  refine ⟨v, ?_, ?_⟩
  · intro x
    simp only [hv]
    have h8 : μ⁻¹ ^ 0 * (B ^ 0).mulVec (fun _ => (1 : ℝ)) x
        = 1 := by
      rw [pow_zero, pow_zero, Matrix.one_mulVec, one_mul]
    calc (1 : ℝ)
        = μ⁻¹ ^ 0 * (B ^ 0).mulVec (fun _ => 1) x := h8.symm
      _ ≤ ∑ k ∈ Finset.range (K + 1),
            μ⁻¹ ^ k * (B ^ k).mulVec (fun _ => 1) x :=
          Finset.single_le_sum (f := fun k =>
            μ⁻¹ ^ k * (B ^ k).mulVec (fun _ => (1 : ℝ)) x)
            (fun k _ => mul_nonneg
              (pow_nonneg (by positivity) k) (hones k x))
            (by
              rw [Finset.mem_range]
              omega)
  · intro x
    -- B v = μ (v − 𝟙) + μ^{-(K+1)}·μ · B^{K+1} 𝟙 ≤ μ v
    have h11 : ∀ k : ℕ,
        ∑ y, B x y * (B ^ k).mulVec (fun _ => 1) y
          = (B ^ (k + 1)).mulVec (fun _ => 1) x := by
      intro k
      rw [pow_succ', ← Matrix.mulVec_mulVec]
      rfl
    have h9 : B.mulVec v x = ∑ k ∈ Finset.range (K + 1),
        μ⁻¹ ^ k * (B ^ (k + 1)).mulVec (fun _ => 1) x := by
      simp only [hv]
      rw [Matrix.mulVec, dotProduct]
      have h10 : ∀ y, B x y * (∑ k ∈ Finset.range (K + 1),
          μ⁻¹ ^ k * (B ^ k).mulVec (fun _ => 1) y)
          = ∑ k ∈ Finset.range (K + 1),
              μ⁻¹ ^ k * (B x y
                * (B ^ k).mulVec (fun _ => 1) y) := by
        intro y
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        ring
      rw [Finset.sum_congr rfl fun y _ => h10 y, Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Finset.mul_sum, h11 k]
    have hrow : (B ^ (K + 1)).mulVec (fun _ => 1) x
        ≤ μ ^ (K + 1) := by
      have h13 : (B ^ (K + 1)).mulVec (fun _ => 1) x
          = ∑ y, (B ^ (K + 1)) x y := by
        rw [Matrix.mulVec, dotProduct]
        refine Finset.sum_congr rfl fun y _ => mul_one _
      rw [h13]
      refine le_trans ?_ h3
      rw [entrySum]
      exact Finset.single_le_sum
        (f := fun x' => ∑ y, (B ^ (K + 1)) x' y)
        (fun x' _ => Finset.sum_nonneg fun y _ =>
          entryNonneg_pow hB _ x' y) (Finset.mem_univ x)
    have hpeel : v x = (∑ k ∈ Finset.range K,
        μ⁻¹ ^ (k + 1) * (B ^ (k + 1)).mulVec (fun _ => 1) x)
        + 1 := by
      simp only [hv]
      rw [Finset.sum_range_succ']
      congr 1
      rw [pow_zero, pow_zero, Matrix.one_mulVec, one_mul]
    have hterm : ∀ k : ℕ,
        μ * (μ⁻¹ ^ (k + 1)
          * (B ^ (k + 1)).mulVec (fun _ => 1) x)
        = μ⁻¹ ^ k * (B ^ (k + 1)).mulVec (fun _ => 1) x := by
      intro k
      rw [pow_succ]
      field_simp
    have h14 : ∑ k ∈ Finset.range (K + 1),
        μ⁻¹ ^ k * (B ^ (k + 1)).mulVec (fun _ => 1) x
        = μ * (v x - 1 + μ⁻¹ ^ (K + 1)
            * (B ^ (K + 1)).mulVec (fun _ => 1) x) := by
      rw [Finset.sum_range_succ, hpeel]
      have h15 : μ * ((∑ k ∈ Finset.range K,
          μ⁻¹ ^ (k + 1) * (B ^ (k + 1)).mulVec (fun _ => 1) x)
          + 1 - 1 + μ⁻¹ ^ (K + 1)
            * (B ^ (K + 1)).mulVec (fun _ => 1) x)
          = (∑ k ∈ Finset.range K,
              μ * (μ⁻¹ ^ (k + 1)
                * (B ^ (k + 1)).mulVec (fun _ => 1) x))
            + μ * (μ⁻¹ ^ (K + 1)
              * (B ^ (K + 1)).mulVec (fun _ => 1) x) := by
        rw [← Finset.mul_sum]
        ring
      rw [h15, Finset.sum_congr rfl fun k _ => hterm k, hterm K]
    rw [h9, h14]
    have h16 : μ⁻¹ ^ (K + 1)
        * (B ^ (K + 1)).mulVec (fun _ => 1) x ≤ 1 := by
      have h17 : μ⁻¹ ^ (K + 1)
          * (B ^ (K + 1)).mulVec (fun _ => 1) x
          ≤ μ⁻¹ ^ (K + 1) * μ ^ (K + 1) :=
        mul_le_mul_of_nonneg_left hrow (by positivity)
      have h18 : μ⁻¹ ^ (K + 1) * μ ^ (K + 1) = 1 := by
        rw [← mul_pow, inv_mul_cancel₀ hμ0.ne', one_pow]
      linarith
    have h19 : μ * (v x - 1 + μ⁻¹ ^ (K + 1)
        * (B ^ (K + 1)).mulVec (fun _ => 1) x)
        ≤ μ * (v x - 1 + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hμ0.le
    calc μ * (v x - 1 + μ⁻¹ ^ (K + 1)
        * (B ^ (K + 1)).mulVec (fun _ => 1) x)
        ≤ μ * (v x - 1 + 1) := h19
      _ = μ * v x := by ring

/-! ## The block-triangular upper bound -/

variable {P : V → Prop} [DecidablePred P]

/-- **The block-triangular upper bound**
(`prop:terminal-component` (ii), upper half, two blocks): if no
transition leads from the second block back into the first, the
growth rate of the whole matrix is dominated by the larger of the
two block growth rates — glue super-solutions of the blocks. -/
theorem pRad_blockTriangular_le
    [Nonempty {x // P x}] [Nonempty {x // ¬P x}]
    {B : Matrix V V ℝ} (hB : EntryNonneg B)
    (hw : HasDiagWitness B)
    (hwS : HasDiagWitness (B.submatrix
      (Function.Embedding.subtype P)
      (Function.Embedding.subtype P)))
    (hwC : HasDiagWitness (B.submatrix
      (Function.Embedding.subtype (fun x => ¬P x))
      (Function.Embedding.subtype (fun x => ¬P x))))
    (hblock : ∀ x y, ¬P x → P y → B x y = 0) :
    pRad B ≤ max
      (pRad (B.submatrix (Function.Embedding.subtype P)
        (Function.Embedding.subtype P)))
      (pRad (B.submatrix
        (Function.Embedding.subtype (fun x => ¬P x))
        (Function.Embedding.subtype (fun x => ¬P x)))) := by
  classical
  set BS := B.submatrix (Function.Embedding.subtype P)
    (Function.Embedding.subtype P) with hBS
  set BC := B.submatrix (Function.Embedding.subtype (fun x => ¬P x))
    (Function.Embedding.subtype (fun x => ¬P x)) with hBC
  have hBSnn : EntryNonneg BS := fun x y => hB _ _
  have hBCnn : EntryNonneg BC := fun x y => hB _ _
  by_contra hcon
  push_neg at hcon
  set M := max (pRad BS) (pRad BC) with hM
  set μ₂ := (M + pRad B) / 2 with hμ₂
  set μ₁ := (M + μ₂) / 2 with hμ₁
  have hMpos : 0 < M :=
    lt_of_lt_of_le (pRad_pos BS) (le_max_left _ _)
  have hM1 : M < μ₁ := by
    rw [hμ₁, hμ₂]
    linarith [hcon]
  have h12 : μ₁ < μ₂ := by
    rw [hμ₁, hμ₂]
    linarith [hcon]
  have h2B : μ₂ < pRad B := by
    rw [hμ₂]
    linarith [hcon]
  have hμ₁pos : 0 < μ₁ := lt_trans hMpos hM1
  have hμ₂pos : 0 < μ₂ := lt_trans hμ₁pos h12
  have hSlt : pRad BS < μ₁ := by
    have h := le_max_left (pRad BS) (pRad BC)
    rw [← hM] at h
    exact lt_of_le_of_lt h hM1
  have hClt : pRad BC < μ₁ := by
    have h := le_max_right (pRad BS) (pRad BC)
    rw [← hM] at h
    exact lt_of_le_of_lt h hM1
  obtain ⟨vS, hvS1, hvSsup⟩ :=
    exists_supersolution hBSnn hwS hSlt
  obtain ⟨vC, hvC1, hvCsup⟩ :=
    exists_supersolution hBCnn hwC hClt
  set CT := Finset.univ.sup' Finset.univ_nonempty
    (fun x : V => ∑ y : {y // ¬P y}, B x (y : V) * vC y)
    with hCT
  have hCT0 : 0 ≤ CT := by
    rw [hCT]
    refine le_trans ?_ (Finset.le_sup'
      (f := fun x : V => ∑ y : {y // ¬P y}, B x (y : V) * vC y)
      (Finset.mem_univ (Classical.arbitrary V)))
    exact Finset.sum_nonneg fun y _ => mul_nonneg (hB _ _)
      (le_trans zero_le_one (hvC1 y))
  set t := CT / (μ₂ - μ₁) + 1 with ht
  have ht1 : 1 ≤ t := by
    rw [ht]
    have h3 : 0 ≤ CT / (μ₂ - μ₁) :=
      div_nonneg hCT0 (by linarith)
    linarith
  have heqt : (μ₂ - μ₁) * t = CT + (μ₂ - μ₁) := by
    rw [ht]
    have hne : μ₂ - μ₁ ≠ 0 := by linarith
    field_simp
  set w : V → ℝ := fun x =>
    if hx : P x then t * vS ⟨x, hx⟩ else vC ⟨x, hx⟩ with hwdef
  have hw1 : ∀ x, 0 < w x := by
    intro x
    simp only [hwdef]
    by_cases hx : P x
    · rw [dif_pos hx]
      have h4 := hvS1 ⟨x, hx⟩
      nlinarith
    · rw [dif_neg hx]
      exact lt_of_lt_of_le zero_lt_one (hvC1 _)
  have hsup : ∀ x, B.mulVec w x ≤ μ₂ * w x := by
    intro x
    have hsplit : B.mulVec w x
        = (∑ y : {y // P y}, B x (y : V) * (t * vS y))
          + ∑ y : {y // ¬P y}, B x (y : V) * vC y := by
      rw [Matrix.mulVec, dotProduct,
        ← Fintype.sum_subtype_add_sum_subtype P
          (fun y => B x y * w y)]
      congr 1
      · refine Finset.sum_congr rfl fun y _ => ?_
        congr 1
        simp only [hwdef]
        rw [dif_pos y.2]
      · refine Finset.sum_congr rfl fun y _ => ?_
        congr 1
        simp only [hwdef]
        rw [dif_neg y.2]
    by_cases hx : P x
    · have hS : ∑ y : {y // P y}, B x (y : V) * (t * vS y)
          = t * BS.mulVec vS ⟨x, hx⟩ := by
        rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        have h5 : BS ⟨x, hx⟩ y = B x (y : V) := rfl
        rw [h5]
        ring
      have hcross : ∑ y : {y // ¬P y}, B x (y : V) * vC y
          ≤ CT := by
        rw [hCT]
        exact Finset.le_sup'
          (f := fun x : V =>
            ∑ y : {y // ¬P y}, B x (y : V) * vC y)
          (Finset.mem_univ x)
      have hwx : w x = t * vS ⟨x, hx⟩ := by
        simp only [hwdef]
        rw [dif_pos hx]
      rw [hsplit, hS, hwx]
      have h6 : t * BS.mulVec vS ⟨x, hx⟩
          ≤ t * (μ₁ * vS ⟨x, hx⟩) :=
        mul_le_mul_of_nonneg_left (hvSsup _) (by linarith)
      have h7 := hvS1 ⟨x, hx⟩
      nlinarith [mul_nonneg (mul_nonneg
        (show (0:ℝ) ≤ μ₂ - μ₁ by linarith)
        (show (0:ℝ) ≤ t by linarith))
        (show (0:ℝ) ≤ vS ⟨x, hx⟩ - 1 by linarith)]
    · have hzero : ∑ y : {y // P y}, B x (y : V) * (t * vS y)
          = 0 :=
        Finset.sum_eq_zero fun y _ => by
          rw [hblock x y hx y.2, zero_mul]
      have hC : ∑ y : {y // ¬P y}, B x (y : V) * vC y
          = BC.mulVec vC ⟨x, hx⟩ := by
        rw [Matrix.mulVec, dotProduct]
        refine Finset.sum_congr rfl fun y _ => ?_
        have h5 : BC ⟨x, hx⟩ y = B x (y : V) := rfl
        rw [h5]
      have hwx : w x = vC ⟨x, hx⟩ := by
        simp only [hwdef]
        rw [dif_neg hx]
      rw [hsplit, hzero, zero_add, hC, hwx]
      calc BC.mulVec vC ⟨x, hx⟩ ≤ μ₁ * vC ⟨x, hx⟩ := hvCsup _
        _ ≤ μ₂ * vC ⟨x, hx⟩ := by
            have h8 : (0:ℝ) ≤ vC ⟨x, hx⟩ :=
              le_trans zero_le_one (hvC1 _)
            nlinarith
  have hfinal := pRad_le_of_supersolution hB hw hμ₂pos hw1 hsup
  linarith

end NCG
