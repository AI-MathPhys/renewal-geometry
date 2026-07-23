/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Lorentz.PerronExistence

/-!
# Perron pressure selects the modular exponent

Covers `thm:pressure-selects-beta` from
`manuscripts/lorentzian_emergence/lorentzian_emergence.tex`: for the
length-weighted transfer kernel
`K(s)_{xy} = ∑_{e : x→y} q_e e^{−s ℓ_e}` (`q_e > 0`,
`0 < ℓ₀ ≤ ℓ_e ≤ ℓ₁`) on a strongly connected recurrent component, the
growth rate `r(s)` of `K(s)` is strictly decreasing and continuous
with `r(s) → 0`, and the pressure equation `r(β) = 1` has

* a **unique positive root** when `r(0) > 1` (supercritical);
* only the root `β = 0` when `r(0) = 1`;
* no nonnegative root when `r(0) < 1`.

Mathlib has no Perron–Frobenius theory, so the spectral radius is
implemented from scratch as the **Gelfand–Fekete growth rate**
`pRad A = exp (lim log(entrySum (A^k))/k)` of the total entry sum of
powers, which for entrywise-nonnegative matrices is submultiplicative;
irreducibility enters only through a positive diagonal entry of some
power, which bounds the growth from below and keeps every quantity
finite.  Strict monotonicity in `s` comes from the entrywise
exponential domination `K(t) ≤ e^{−(t−s)ℓ₀}·K(s)` together with
positive homogeneity of the growth rate — no eigenvector theory is
needed for the selection statement.  The Perron eigenvector theory
itself (existence, positivity, simplicity for irreducible matrices)
lives in `NCG.Lorentz.PerronExistence`; the final section here
identifies the Perron eigenvalue with the growth rate
(`eigenvalue_eq_pRad`), so `pRad` **is** the Perron root for every
irreducible nonnegative matrix
(`exists_pRad_eigenvector_of_isIrreducible`).
-/

namespace NCG

open Filter

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]

/-! ## The entry-sum gauge and its submultiplicativity -/

/-- Total entry sum of a matrix — the gauge for the growth rate. -/
def entrySum (A : Matrix V V ℝ) : ℝ := ∑ x, ∑ y, A x y

/-- Entrywise nonnegativity. -/
def EntryNonneg (A : Matrix V V ℝ) : Prop := ∀ x y, 0 ≤ A x y

omit [DecidableEq V] [Nonempty V] in
theorem entrySum_nonneg {A : Matrix V V ℝ} (hA : EntryNonneg A) :
    0 ≤ entrySum A :=
  Finset.sum_nonneg fun x _ =>
    Finset.sum_nonneg fun y _ => hA x y

omit [DecidableEq V] [Nonempty V] in
theorem le_entrySum {A : Matrix V V ℝ} (hA : EntryNonneg A)
    (x y : V) : A x y ≤ entrySum A := by
  calc A x y ≤ ∑ y', A x y' :=
        Finset.single_le_sum (fun y' _ => hA x y') (Finset.mem_univ y)
    _ ≤ ∑ x', ∑ y', A x' y' :=
        Finset.single_le_sum
          (f := fun x' => ∑ y', A x' y')
          (fun x' _ => Finset.sum_nonneg fun y' _ => hA x' y')
          (Finset.mem_univ x)

omit [DecidableEq V] [Nonempty V] in
theorem colSum_le_entrySum {A : Matrix V V ℝ} (hA : EntryNonneg A)
    (y : V) : (∑ x, A x y) ≤ entrySum A := by
  calc (∑ x, A x y) ≤ ∑ y', ∑ x, A x y' :=
        Finset.single_le_sum
          (f := fun y' => ∑ x, A x y')
          (fun y' _ => Finset.sum_nonneg fun x _ => hA x y')
          (Finset.mem_univ y)
    _ = entrySum A := Finset.sum_comm

omit [DecidableEq V] [Nonempty V] in
theorem entryNonneg_mul {A B : Matrix V V ℝ} (hA : EntryNonneg A)
    (hB : EntryNonneg B) : EntryNonneg (A * B) := by
  intro x y
  rw [Matrix.mul_apply]
  exact Finset.sum_nonneg fun z _ => mul_nonneg (hA x z) (hB z y)

omit [Nonempty V] in
theorem entryNonneg_pow {A : Matrix V V ℝ} (hA : EntryNonneg A) :
    ∀ k, EntryNonneg (A ^ k) := by
  intro k
  induction k with
  | zero =>
    intro x y
    rw [pow_zero]
    rcases eq_or_ne x y with rfl | hxy
    · rw [Matrix.one_apply_eq]
      norm_num
    · rw [Matrix.one_apply_ne hxy]
  | succ m ih =>
    rw [pow_succ]
    exact entryNonneg_mul ih hA

omit [DecidableEq V] [Nonempty V] in
theorem entrySum_mul_le {A B : Matrix V V ℝ} (hA : EntryNonneg A)
    (hB : EntryNonneg B) :
    entrySum (A * B) ≤ entrySum A * entrySum B := by
  calc entrySum (A * B) = ∑ x, ∑ z, ∑ y, A x y * B y z := by
        refine Finset.sum_congr rfl fun x _ => ?_
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [Matrix.mul_apply]
    _ = ∑ x, ∑ y, ∑ z, A x y * B y z := by
        refine Finset.sum_congr rfl fun x _ => ?_
        exact Finset.sum_comm
    _ = ∑ y, ∑ x, ∑ z, A x y * B y z := Finset.sum_comm
    _ = ∑ y, (∑ x, A x y) * ∑ z, B y z := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum]
    _ ≤ ∑ y, entrySum A * ∑ z, B y z := by
        refine Finset.sum_le_sum fun y _ => ?_
        exact mul_le_mul_of_nonneg_right (colSum_le_entrySum hA y)
          (Finset.sum_nonneg fun z _ => hB y z)
    _ = entrySum A * entrySum B := by
        rw [← Finset.mul_sum]
        rfl

omit [Nonempty V] in
theorem entrySum_pow_add_le {A : Matrix V V ℝ} (hA : EntryNonneg A)
    (j k : ℕ) :
    entrySum (A ^ (j + k)) ≤ entrySum (A ^ j) * entrySum (A ^ k) := by
  rw [pow_add]
  exact entrySum_mul_le (entryNonneg_pow hA j) (entryNonneg_pow hA k)

omit [Nonempty V] in
theorem entrySum_pow_mul_le {A : Matrix V V ℝ} (hA : EntryNonneg A)
    (k : ℕ) : ∀ m : ℕ, 1 ≤ m →
    entrySum (A ^ (k * m)) ≤ entrySum (A ^ k) ^ m := by
  intro m
  induction m with
  | zero => intro h; omega
  | succ j ih =>
    intro _
    rcases Nat.eq_or_lt_of_le (Nat.one_le_iff_ne_zero.mpr
      (Nat.succ_ne_zero j)) with h | h
    · rcases Nat.eq_zero_or_pos j with rfl | hj
      · simp
      · have h1 : k * (j + 1) = k * j + k := by ring
        rw [h1]
        calc entrySum (A ^ (k * j + k))
            ≤ entrySum (A ^ (k * j)) * entrySum (A ^ k) :=
              entrySum_pow_add_le hA _ _
          _ ≤ entrySum (A ^ k) ^ j * entrySum (A ^ k) := by
              refine mul_le_mul_of_nonneg_right (ih hj) ?_
              exact entrySum_nonneg (entryNonneg_pow hA k)
          _ = entrySum (A ^ k) ^ (j + 1) := by ring
    · rcases Nat.eq_zero_or_pos j with rfl | hj
      · simp
      · have h1 : k * (j + 1) = k * j + k := by ring
        rw [h1]
        calc entrySum (A ^ (k * j + k))
            ≤ entrySum (A ^ (k * j)) * entrySum (A ^ k) :=
              entrySum_pow_add_le hA _ _
          _ ≤ entrySum (A ^ k) ^ j * entrySum (A ^ k) := by
              refine mul_le_mul_of_nonneg_right (ih hj) ?_
              exact entrySum_nonneg (entryNonneg_pow hA k)
          _ = entrySum (A ^ k) ^ (j + 1) := by ring

/-! ## Diagonal witnesses and positivity of the gauge -/

/-- Irreducibility surrogate: some power has a positive diagonal
entry. -/
def HasDiagWitness (A : Matrix V V ℝ) : Prop :=
  ∃ (x : V) (m : ℕ), 0 < m ∧ 0 < (A ^ m) x x

omit [Nonempty V] in
theorem diag_pow_add {A : Matrix V V ℝ} (hA : EntryNonneg A)
    (x : V) (j k : ℕ) :
    (A ^ j) x x * (A ^ k) x x ≤ (A ^ (j + k)) x x := by
  rw [pow_add, Matrix.mul_apply]
  exact Finset.single_le_sum
    (f := fun z => (A ^ j) x z * (A ^ k) z x)
    (fun z _ => mul_nonneg (entryNonneg_pow hA j x z)
      (entryNonneg_pow hA k z x))
    (Finset.mem_univ x)

omit [Nonempty V] in
theorem diag_pow_mul_pos {A : Matrix V V ℝ} (hA : EntryNonneg A)
    {x : V} {m : ℕ} (hm : 0 < (A ^ m) x x) :
    ∀ k : ℕ, 1 ≤ k → (A ^ m) x x ^ k ≤ (A ^ (k * m)) x x := by
  intro k
  induction k with
  | zero => intro h; omega
  | succ j ih =>
    intro _
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp
    · have h1 : (j + 1) * m = j * m + m := by ring
      rw [h1]
      calc (A ^ m) x x ^ (j + 1)
          = (A ^ m) x x ^ j * (A ^ m) x x := by ring
        _ ≤ (A ^ (j * m)) x x * (A ^ m) x x :=
            mul_le_mul_of_nonneg_right (ih hj) hm.le
        _ ≤ (A ^ (j * m + m)) x x := diag_pow_add hA x _ _

theorem entrySum_pow_pos {A : Matrix V V ℝ} (hA : EntryNonneg A)
    (hw : HasDiagWitness A) (k : ℕ) : 0 < entrySum (A ^ k) := by
  obtain ⟨x, m, hm, hpos⟩ := hw
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [pow_zero]
    have h1 : entrySum (1 : Matrix V V ℝ)
        = (Fintype.card V : ℝ) := by
      unfold entrySum
      rw [show (∑ x : V, ∑ y : V, (1 : Matrix V V ℝ) x y)
          = ∑ x : V, (1 : ℝ) from Finset.sum_congr rfl fun x _ => by
        rw [Finset.sum_eq_single x]
        · rw [Matrix.one_apply_eq]
        · intro y _ hy
          rw [Matrix.one_apply_ne (Ne.symm hy)]
        · intro h
          exact absurd (Finset.mem_univ x) h]
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    rw [h1]
    have h2 : 0 < Fintype.card V := Fintype.card_pos
    exact_mod_cast h2
  · -- the k-th power cannot vanish: a diagonal entry of A^{km} is
    -- positive and factors through A^k
    have h3 : 0 < (A ^ (k * m)) x x :=
      lt_of_lt_of_le (pow_pos hpos k) (diag_pow_mul_pos hA hpos k hk)
    have h4 : (A ^ (k * m)) x x
        ≤ entrySum (A ^ k) * entrySum (A ^ (k * m - k)) := by
      have h5 : k + (k * m - k) = k * m := by
        have h6 : k ≤ k * m := Nat.le_mul_of_pos_right k hm
        omega
      calc (A ^ (k * m)) x x ≤ entrySum (A ^ (k * m)) :=
            le_entrySum (entryNonneg_pow hA _) x x
        _ = entrySum (A ^ (k + (k * m - k))) := by rw [h5]
        _ ≤ entrySum (A ^ k) * entrySum (A ^ (k * m - k)) :=
            entrySum_pow_add_le hA _ _
    by_contra hle
    push Not at hle
    have h6 : entrySum (A ^ k) = 0 :=
      le_antisymm hle (entrySum_nonneg (entryNonneg_pow hA k))
    rw [h6, zero_mul] at h4
    linarith

/-! ## The Gelfand–Fekete growth rate -/

/-- Logarithmic growth sequence of the entry-sum gauge. -/
noncomputable def growthSeq (A : Matrix V V ℝ) (k : ℕ) : ℝ :=
  Real.log (entrySum (A ^ k))

theorem growthSeq_subadditive {A : Matrix V V ℝ}
    (hA : EntryNonneg A) (hw : HasDiagWitness A) :
    Subadditive (growthSeq A) := by
  intro j k
  unfold growthSeq
  have h1 := entrySum_pow_add_le hA j k
  have h2 := entrySum_pow_pos hA hw j
  have h3 := entrySum_pow_pos hA hw k
  calc Real.log (entrySum (A ^ (j + k)))
      ≤ Real.log (entrySum (A ^ j) * entrySum (A ^ k)) := by
        refine Real.log_le_log ?_ h1
        exact entrySum_pow_pos hA hw (j + k)
    _ = Real.log (entrySum (A ^ j)) + Real.log (entrySum (A ^ k)) :=
        Real.log_mul h2.ne' h3.ne'

omit [Nonempty V] in
theorem growthSeq_div_bddBelow {A : Matrix V V ℝ}
    (hA : EntryNonneg A) (hw : HasDiagWitness A) :
    BddBelow (Set.range fun k : ℕ => growthSeq A k / k) := by
  obtain ⟨x, m, hm, hpos⟩ := hw
  refine ⟨min 0 (Real.log ((A ^ m) x x) / m), ?_⟩
  rintro v ⟨k, rfl⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · refine le_trans (min_le_right _ _) ?_
    -- m·(log entrySum(A^k)) ≥ log entrySum(A^{km}) ≥ k·log (A^m)xx
    have hm1 : (1 : ℕ) ≤ m := hm
    have h1 : entrySum (A ^ (k * m)) ≤ entrySum (A ^ k) ^ m :=
      entrySum_pow_mul_le hA k m hm1
    have h2 : (A ^ m) x x ^ k ≤ entrySum (A ^ (k * m)) := by
      refine le_trans (diag_pow_mul_pos hA hpos k hk) ?_
      exact le_entrySum (entryNonneg_pow hA _) x x
    have h3 : (A ^ m) x x ^ k ≤ entrySum (A ^ k) ^ m :=
      le_trans h2 h1
    have h4 : (k : ℝ) * Real.log ((A ^ m) x x)
        ≤ (m : ℝ) * Real.log (entrySum (A ^ k)) := by
      have h5 := Real.log_le_log (pow_pos hpos k) h3
      rw [Real.log_pow, Real.log_pow] at h5
      exact_mod_cast h5
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    rw [div_le_div_iff₀ hmR hkR]
    unfold growthSeq
    linarith

/-- The **Gelfand–Fekete growth rate** of a nonnegative matrix — the
implementation of its spectral radius. -/
noncomputable def pRad (A : Matrix V V ℝ) : ℝ :=
  Real.exp (sInf ((fun k : ℕ => growthSeq A k / k) '' Set.Ici 1))

omit [Nonempty V] in
theorem pRad_pos (A : Matrix V V ℝ) : 0 < pRad A := Real.exp_pos _

theorem tendsto_growthSeq {A : Matrix V V ℝ} (hA : EntryNonneg A)
    (hw : HasDiagWitness A) :
    Tendsto (fun k : ℕ => growthSeq A k / k) atTop
      (nhds (Real.log (pRad A))) := by
  have hsub := growthSeq_subadditive hA hw
  have h1 := hsub.tendsto_lim (growthSeq_div_bddBelow hA hw)
  have h2 : Real.log (pRad A) = hsub.lim := by
    rw [pRad, Real.log_exp, Subadditive.lim]
  rw [h2]
  exact h1

/-- Monotonicity of the growth rate under entrywise domination. -/
theorem pRad_le_of_entry_le {A B : Matrix V V ℝ}
    (hA : EntryNonneg A) (hw : HasDiagWitness A)
    (hAB : ∀ x y, A x y ≤ B x y) : pRad A ≤ pRad B := by
  have hB : EntryNonneg B := fun x y => le_trans (hA x y) (hAB x y)
  -- powers dominate entrywise
  have hpow : ∀ k, ∀ x y, (A ^ k) x y ≤ (B ^ k) x y := by
    intro k
    induction k with
    | zero =>
      intro x y
      rw [pow_zero, pow_zero]
    | succ j ih =>
      intro x y
      rw [pow_succ, pow_succ, Matrix.mul_apply, Matrix.mul_apply]
      refine Finset.sum_le_sum fun z _ => ?_
      exact mul_le_mul (ih x z) (hAB z y) (hA z y)
        (le_trans (entryNonneg_pow hA j x z) (ih x z))
  have hwB : HasDiagWitness B := by
    obtain ⟨x, m, hm, hpos⟩ := hw
    exact ⟨x, m, hm, lt_of_lt_of_le hpos (hpow m x x)⟩
  have hle : ∀ k : ℕ, growthSeq A k / k ≤ growthSeq B k / k := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · have hkR : (0 : ℝ) < k := by exact_mod_cast hk
      refine div_le_div_of_nonneg_right ?_ hkR.le
      unfold growthSeq
      refine Real.log_le_log (entrySum_pow_pos hA hw k) ?_
      unfold entrySum
      exact Finset.sum_le_sum fun x _ =>
        Finset.sum_le_sum fun y _ => hpow k x y
  have h1 := le_of_tendsto_of_tendsto'
    (tendsto_growthSeq hA hw) (tendsto_growthSeq hB hwB) hle
  calc pRad A = Real.exp (Real.log (pRad A)) :=
        (Real.exp_log (pRad_pos A)).symm
    _ ≤ Real.exp (Real.log (pRad B)) := Real.exp_le_exp.mpr h1
    _ = pRad B := Real.exp_log (pRad_pos B)

/-- Positive homogeneity of the growth rate. -/
theorem pRad_smul {A : Matrix V V ℝ} (hA : EntryNonneg A)
    (hw : HasDiagWitness A) {c : ℝ} (hc : 0 < c) :
    pRad (c • A) = c * pRad A := by
  have hcA : EntryNonneg (c • A) := by
    intro x y
    rw [Matrix.smul_apply]
    exact mul_nonneg hc.le (hA x y)
  have hwcA : HasDiagWitness (c • A) := by
    obtain ⟨x, m, hm, hpos⟩ := hw
    refine ⟨x, m, hm, ?_⟩
    rw [smul_pow, Matrix.smul_apply, smul_eq_mul]
    exact mul_pos (pow_pos hc m) hpos
  -- the growth sequence shifts by k·log c
  have hshift : ∀ k : ℕ, growthSeq (c • A) k
      = (k : ℝ) * Real.log c + growthSeq A k := by
    intro k
    unfold growthSeq
    rw [smul_pow]
    have h1 : entrySum ((c ^ k) • A ^ k)
        = c ^ k * entrySum (A ^ k) := by
      unfold entrySum
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [Matrix.smul_apply, smul_eq_mul]
    rw [h1, Real.log_mul (pow_pos hc k).ne'
      (entrySum_pow_pos hA hw k).ne', Real.log_pow]
  have h2 : Tendsto (fun k : ℕ => growthSeq (c • A) k / k) atTop
      (nhds (Real.log c + Real.log (pRad A))) := by
    have h3 : Tendsto
        (fun k : ℕ => Real.log c + growthSeq A k / k) atTop
        (nhds (Real.log c + Real.log (pRad A))) :=
      tendsto_const_nhds.add (tendsto_growthSeq hA hw)
    refine (h3.congr' ?_)
    filter_upwards [eventually_ne_atTop 0] with k hk
    rw [hshift k]
    have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    field_simp
  have h4 := tendsto_nhds_unique (tendsto_growthSeq hcA hwcA) h2
  calc pRad (c • A) = Real.exp (Real.log (pRad (c • A))) :=
        (Real.exp_log (pRad_pos _)).symm
    _ = Real.exp (Real.log c + Real.log (pRad A)) := by rw [h4]
    _ = c * pRad A := by
        rw [Real.exp_add, Real.exp_log hc, Real.exp_log (pRad_pos A)]

omit [DecidableEq V] [Fintype V] [Nonempty V] in
theorem entryNonneg_smul {A : Matrix V V ℝ} (hA : EntryNonneg A)
    {c : ℝ} (hc : 0 ≤ c) : EntryNonneg (c • A) := by
  intro x y
  rw [Matrix.smul_apply, smul_eq_mul]
  exact mul_nonneg hc (hA x y)

omit [Nonempty V] in
theorem hasDiagWitness_smul {A : Matrix V V ℝ} {c : ℝ} (hc : 0 < c)
    (hw : HasDiagWitness A) : HasDiagWitness (c • A) := by
  obtain ⟨x, m, hm, hpos⟩ := hw
  refine ⟨x, m, hm, ?_⟩
  rw [smul_pow, Matrix.smul_apply, smul_eq_mul]
  exact mul_pos (pow_pos hc m) hpos

omit [Nonempty V] in
theorem entry_pow_le {A B : Matrix V V ℝ} (hA : EntryNonneg A)
    (hAB : ∀ x y, A x y ≤ B x y) :
    ∀ k, ∀ x y, (A ^ k) x y ≤ (B ^ k) x y := by
  intro k
  induction k with
  | zero =>
    intro x y
    rw [pow_zero, pow_zero]
  | succ j ih =>
    intro x y
    rw [pow_succ, pow_succ, Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_le_sum fun z _ => ?_
    exact mul_le_mul (ih x z) (hAB z y) (hA z y)
      (le_trans (entryNonneg_pow hA j x z) (ih x z))

/-! ## The length-weighted transfer kernel -/

section Kernel

variable {E : Type*} [Fintype E]

/-- The length-weighted renewal transfer kernel
`K(s)_{xy} = ∑_{e : x→y} q_e e^{−s ℓ_e}`
(Definition inside `thm:pressure-selects-beta`). -/
noncomputable def pressureKernel (src tgt : E → V) (q ℓ : E → ℝ)
    (s : ℝ) : Matrix V V ℝ :=
  Matrix.of fun x y =>
    ∑ e ∈ Finset.univ.filter (fun e => src e = x ∧ tgt e = y),
      q e * Real.exp (-(s * ℓ e))

variable {src tgt : E → V} {q ℓ : E → ℝ}

omit [Fintype V] [Nonempty V] in
theorem pressureKernel_nonneg (hq : ∀ e, 0 ≤ q e) (s : ℝ) :
    EntryNonneg (pressureKernel src tgt q ℓ s) := by
  intro x y
  refine Finset.sum_nonneg fun e _ => ?_
  exact mul_nonneg (hq e) (Real.exp_pos _).le

omit [Fintype V] in
omit [Fintype V] [Nonempty V] in
/-- Entrywise exponential domination, upper form:
`K(t) ≤ e^{−(t−s)ℓ₀} K(s)` for `s ≤ t`. -/
theorem pressureKernel_le (hq : ∀ e, 0 ≤ q e) {ℓ₀ : ℝ}
    (hℓ₀ : ∀ e, ℓ₀ ≤ ℓ e) {s t : ℝ} (hst : s ≤ t) :
    ∀ x y, pressureKernel src tgt q ℓ t x y
      ≤ (Real.exp (-((t - s) * ℓ₀))
          • pressureKernel src tgt q ℓ s) x y := by
  intro x y
  rw [Matrix.smul_apply, smul_eq_mul]
  change (∑ e ∈ Finset.univ.filter
      (fun e => src e = x ∧ tgt e = y), q e * Real.exp (-(t * ℓ e)))
    ≤ Real.exp (-((t - s) * ℓ₀)) * ∑ e ∈ Finset.univ.filter
      (fun e => src e = x ∧ tgt e = y), q e * Real.exp (-(s * ℓ e))
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun e _ => ?_
  rw [show Real.exp (-((t - s) * ℓ₀)) * (q e * Real.exp (-(s * ℓ e)))
      = q e * (Real.exp (-((t - s) * ℓ₀)) * Real.exp (-(s * ℓ e)))
    from by ring]
  refine mul_le_mul_of_nonneg_left ?_ (hq e)
  rw [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have h2 : (t - s) * ℓ₀ ≤ (t - s) * ℓ e :=
    mul_le_mul_of_nonneg_left (hℓ₀ e) (sub_nonneg.mpr hst)
  linarith

omit [Fintype V] in
omit [Fintype V] [Nonempty V] in
/-- Entrywise exponential domination, lower form:
`e^{−(t−s)ℓ₁} K(s) ≤ K(t)` for `s ≤ t`. -/
theorem pressureKernel_ge (hq : ∀ e, 0 ≤ q e) {ℓ₁ : ℝ}
    (hℓ₁ : ∀ e, ℓ e ≤ ℓ₁) {s t : ℝ} (hst : s ≤ t) :
    ∀ x y, (Real.exp (-((t - s) * ℓ₁))
        • pressureKernel src tgt q ℓ s) x y
      ≤ pressureKernel src tgt q ℓ t x y := by
  intro x y
  rw [Matrix.smul_apply, smul_eq_mul]
  change Real.exp (-((t - s) * ℓ₁)) * (∑ e ∈ Finset.univ.filter
      (fun e => src e = x ∧ tgt e = y), q e * Real.exp (-(s * ℓ e)))
    ≤ ∑ e ∈ Finset.univ.filter
      (fun e => src e = x ∧ tgt e = y), q e * Real.exp (-(t * ℓ e))
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun e _ => ?_
  rw [show Real.exp (-((t - s) * ℓ₁)) * (q e * Real.exp (-(s * ℓ e)))
      = q e * (Real.exp (-((t - s) * ℓ₁)) * Real.exp (-(s * ℓ e)))
    from by ring]
  refine mul_le_mul_of_nonneg_left ?_ (hq e)
  rw [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have h2 : (t - s) * ℓ e ≤ (t - s) * ℓ₁ :=
    mul_le_mul_of_nonneg_left (hℓ₁ e) (sub_nonneg.mpr hst)
  linarith

omit [Nonempty V] in
/-- The diagonal witness of the recurrent component transfers from
`s = 0` to every inverse temperature. -/
theorem pressureKernel_witness (hq : ∀ e, 0 ≤ q e)
    {ℓ₀ ℓ₁ : ℝ} (hℓ₀ : ∀ e, ℓ₀ ≤ ℓ e) (hℓ₁ : ∀ e, ℓ e ≤ ℓ₁)
    (hw : HasDiagWitness (pressureKernel src tgt q ℓ 0)) (s : ℝ) :
    HasDiagWitness (pressureKernel src tgt q ℓ s) := by
  obtain ⟨x, m, hm, hpos⟩ := hw
  refine ⟨x, m, hm, ?_⟩
  rcases le_total 0 s with hs | hs
  · -- K s dominates a positive multiple of K 0
    have hdom := pressureKernel_ge (q := q) (ℓ := ℓ)
      (src := src) (tgt := tgt) hq hℓ₁ hs
    have h1 := entry_pow_le
      (entryNonneg_smul (pressureKernel_nonneg hq 0)
        (Real.exp_pos _).le)
      hdom m x x
    have h2 : Real.exp (-((s - 0) * ℓ₁)) ^ m
        * ((pressureKernel src tgt q ℓ 0) ^ m) x x
        ≤ ((pressureKernel src tgt q ℓ s) ^ m) x x := by
      rw [← smul_eq_mul, ← Matrix.smul_apply, ← smul_pow]
      exact h1
    refine lt_of_lt_of_le ?_ h2
    exact mul_pos (pow_pos (Real.exp_pos _) m) hpos
  · -- s ≤ 0: K s dominates a positive multiple of K 0 as well
    have hdom := pressureKernel_le (q := q) (ℓ := ℓ)
      (src := src) (tgt := tgt) hq hℓ₀ (t := 0) hs
    -- K 0 ≤ e^{−(0−s)ℓ₀} K s, hence e^{(0−s)ℓ₀}⁻¹-scaled lower bound
    have hc : (0 : ℝ) < Real.exp (-((0 - s) * ℓ₀)) := Real.exp_pos _
    have hdom' : ∀ x' y',
        (Real.exp (-((0 - s) * ℓ₀)))⁻¹
          * pressureKernel src tgt q ℓ 0 x' y'
        ≤ pressureKernel src tgt q ℓ s x' y' := by
      intro x' y'
      have h3 := hdom x' y'
      rw [Matrix.smul_apply, smul_eq_mul] at h3
      rw [inv_mul_le_iff₀ hc]
      exact h3
    have h1 := entry_pow_le
      (entryNonneg_smul (pressureKernel_nonneg hq 0)
        (inv_pos.mpr hc).le)
      (fun x' y' => by
        rw [Matrix.smul_apply, smul_eq_mul]
        exact hdom' x' y') m x x
    have h2 : ((Real.exp (-((0 - s) * ℓ₀)))⁻¹) ^ m
        * ((pressureKernel src tgt q ℓ 0) ^ m) x x
        ≤ ((pressureKernel src tgt q ℓ s) ^ m) x x := by
      rw [← smul_eq_mul, ← Matrix.smul_apply, ← smul_pow]
      exact h1
    refine lt_of_lt_of_le ?_ h2
    exact mul_pos (pow_pos (inv_pos.mpr hc) m) hpos

/-- The pressure/growth rate `r(s)` of the weighted transfer. -/
noncomputable def pressureRate (src tgt : E → V) (q ℓ : E → ℝ)
    (s : ℝ) : ℝ :=
  pRad (pressureKernel src tgt q ℓ s)

/-- **Theorem `thm:pressure-selects-beta`**: on a recurrent component
(positive weights, lengths in `[ℓ₀, ℓ₁]` with `ℓ₀ > 0`, and a
positive-weight cycle), the pressure rate is strictly decreasing,
continuous, and tends to `0`; consequently the pressure equation
`r(β) = 1` has a unique positive root in the supercritical phase
`r(0) > 1`, only the root `β = 0` in the critical phase `r(0) = 1`,
and no nonnegative root in the subcritical phase `r(0) < 1`. -/
theorem pressure_selects_beta
    (src tgt : E → V) (q ℓ : E → ℝ) (hq : ∀ e, 0 < q e)
    {ℓ₀ ℓ₁ : ℝ} (hℓ₀pos : 0 < ℓ₀) (hℓ₀ : ∀ e, ℓ₀ ≤ ℓ e)
    (hℓ₁ : ∀ e, ℓ e ≤ ℓ₁)
    (hconn : HasDiagWitness (pressureKernel src tgt q ℓ 0)) :
    StrictAnti (pressureRate src tgt q ℓ)
    ∧ Continuous (pressureRate src tgt q ℓ)
    ∧ Tendsto (pressureRate src tgt q ℓ) atTop (nhds 0)
    ∧ (1 < pressureRate src tgt q ℓ 0 →
        ∃! β : ℝ, 0 < β ∧ pressureRate src tgt q ℓ β = 1)
    ∧ (pressureRate src tgt q ℓ 0 = 1 →
        ∀ β : ℝ, 0 < β → pressureRate src tgt q ℓ β ≠ 1)
    ∧ (pressureRate src tgt q ℓ 0 < 1 →
        ∀ β : ℝ, 0 ≤ β → pressureRate src tgt q ℓ β ≠ 1) := by
  have hq0 : ∀ e, 0 ≤ q e := fun e => (hq e).le
  have hKnn : ∀ s, EntryNonneg (pressureKernel src tgt q ℓ s) :=
    pressureKernel_nonneg hq0
  have hKw : ∀ s, HasDiagWitness (pressureKernel src tgt q ℓ s) :=
    pressureKernel_witness hq0 hℓ₀ hℓ₁ hconn
  have hrpos : ∀ s, 0 < pressureRate src tgt q ℓ s :=
    fun s => pRad_pos _
  -- an effective upper length bound that is positive
  set L1 : ℝ := max ℓ₁ ℓ₀ with hL1def
  have hℓ₁' : ∀ e, ℓ e ≤ L1 :=
    fun e => le_trans (hℓ₁ e) (le_max_left _ _)
  -- the two rate estimates
  have hupper : ∀ {s t : ℝ}, s ≤ t →
      pressureRate src tgt q ℓ t
        ≤ Real.exp (-((t - s) * ℓ₀)) * pressureRate src tgt q ℓ s := by
    intro s t hst
    have h1 := pRad_le_of_entry_le (hKnn t) (hKw t)
      (pressureKernel_le hq0 hℓ₀ hst)
    rwa [pRad_smul (hKnn s) (hKw s) (Real.exp_pos _)] at h1
  have hlower : ∀ {s t : ℝ}, s ≤ t →
      Real.exp (-((t - s) * L1)) * pressureRate src tgt q ℓ s
        ≤ pressureRate src tgt q ℓ t := by
    intro s t hst
    have h1 := pRad_le_of_entry_le
      (entryNonneg_smul (hKnn s) (Real.exp_pos _).le)
      (hasDiagWitness_smul (Real.exp_pos _) (hKw s))
      (pressureKernel_ge hq0 hℓ₁' hst)
    rwa [pRad_smul (hKnn s) (hKw s) (Real.exp_pos _)] at h1
  -- helper: exp of nonneg / nonpos
  have hexp1 : ∀ u : ℝ, 0 ≤ u → 1 ≤ Real.exp u := by
    intro u hu
    have h2 := Real.exp_le_exp.mpr hu
    rwa [Real.exp_zero] at h2
  have hexp1' : ∀ u : ℝ, u ≤ 0 → Real.exp u ≤ 1 := by
    intro u hu
    have h2 := Real.exp_le_exp.mpr hu
    rwa [Real.exp_zero] at h2
  -- strict decrease
  have hanti : StrictAnti (pressureRate src tgt q ℓ) := by
    intro s t hst
    have h1 := hupper hst.le
    have h2 : Real.exp (-((t - s) * ℓ₀)) < 1 := by
      have h3 : 0 < (t - s) * ℓ₀ :=
        mul_pos (sub_pos.mpr hst) hℓ₀pos
      calc Real.exp (-((t - s) * ℓ₀)) < Real.exp 0 :=
            Real.exp_lt_exp.mpr (by linarith)
        _ = 1 := Real.exp_zero
    calc pressureRate src tgt q ℓ t
        ≤ Real.exp (-((t - s) * ℓ₀)) * pressureRate src tgt q ℓ s :=
          h1
      _ < 1 * pressureRate src tgt q ℓ s :=
          mul_lt_mul_of_pos_right h2 (hrpos s)
      _ = pressureRate src tgt q ℓ s := one_mul _
  have hmono : ∀ {s t : ℝ}, s ≤ t →
      pressureRate src tgt q ℓ t ≤ pressureRate src tgt q ℓ s := by
    intro s t hst
    have h1 := hupper hst
    have h2 : Real.exp (-((t - s) * ℓ₀)) ≤ 1 := by
      refine hexp1' _ ?_
      have h3 : 0 ≤ (t - s) * ℓ₀ :=
        mul_nonneg (sub_nonneg.mpr hst) hℓ₀pos.le
      linarith
    calc pressureRate src tgt q ℓ t
        ≤ Real.exp (-((t - s) * ℓ₀)) * pressureRate src tgt q ℓ s :=
          h1
      _ ≤ 1 * pressureRate src tgt q ℓ s :=
          mul_le_mul_of_nonneg_right h2 (hrpos s).le
      _ = pressureRate src tgt q ℓ s := one_mul _
  -- continuity by exponential squeeze
  have hcont : Continuous (pressureRate src tgt q ℓ) := by
    rw [continuous_iff_continuousAt]
    intro s
    have hLb : ∀ t, pressureRate src tgt q ℓ s
        * Real.exp (-(|t - s| * L1)) ≤ pressureRate src tgt q ℓ t := by
      intro t
      rcases le_total s t with h | h
      · rw [abs_of_nonneg (sub_nonneg.mpr h), mul_comm]
        exact hlower h
      · have h1 := hmono h
        have h2 : Real.exp (-(|t - s| * L1)) ≤ 1 := by
          refine hexp1' _ ?_
          have h3 : 0 ≤ |t - s| * L1 := by
            refine mul_nonneg (abs_nonneg _) ?_
            exact le_trans hℓ₀pos.le (le_max_right _ _)
          linarith
        calc pressureRate src tgt q ℓ s * Real.exp (-(|t - s| * L1))
            ≤ pressureRate src tgt q ℓ s * 1 :=
              mul_le_mul_of_nonneg_left h2 (hrpos s).le
          _ = pressureRate src tgt q ℓ s := mul_one _
          _ ≤ pressureRate src tgt q ℓ t := h1
    have hUb : ∀ t, pressureRate src tgt q ℓ t
        ≤ pressureRate src tgt q ℓ s
          * Real.exp (|t - s| * L1) := by
      intro t
      rcases le_total s t with h | h
      · calc pressureRate src tgt q ℓ t
            ≤ pressureRate src tgt q ℓ s := hmono h
          _ ≤ pressureRate src tgt q ℓ s * Real.exp (|t - s| * L1) := by
              refine le_mul_of_one_le_right (hrpos s).le ?_
              refine hexp1 _ ?_
              refine mul_nonneg (abs_nonneg _) ?_
              exact le_trans hℓ₀pos.le (le_max_right _ _)
      · have h1 := hlower (s := t) (t := s) h
        have h3 : pressureRate src tgt q ℓ t
            ≤ Real.exp ((s - t) * L1) * pressureRate src tgt q ℓ s := by
          have h4 := mul_le_mul_of_nonneg_left h1
            (Real.exp_pos ((s - t) * L1)).le
          rw [← mul_assoc, ← Real.exp_add,
            show (s - t) * L1 + -((s - t) * L1) = 0 from by ring,
            Real.exp_zero, one_mul] at h4
          exact h4
        rw [abs_of_nonpos (sub_nonpos.mpr h),
          show -(t - s) = s - t from by ring, mul_comm
            (pressureRate src tgt q ℓ s)]
        exact h3
    have hgcont : Continuous fun t : ℝ =>
        pressureRate src tgt q ℓ s * Real.exp (-(|t - s| * L1)) := by
      refine Continuous.mul continuous_const ?_
      refine Real.continuous_exp.comp ?_
      refine Continuous.neg ?_
      exact ((continuous_id.sub continuous_const).abs).mul
        continuous_const
    have hgcont' : Continuous fun t : ℝ =>
        pressureRate src tgt q ℓ s * Real.exp (|t - s| * L1) := by
      refine Continuous.mul continuous_const ?_
      refine Real.continuous_exp.comp ?_
      exact ((continuous_id.sub continuous_const).abs).mul
        continuous_const
    have hL0 : Tendsto (fun t : ℝ => pressureRate src tgt q ℓ s
        * Real.exp (-(|t - s| * L1))) (nhds s)
        (nhds (pressureRate src tgt q ℓ s)) := by
      have h5 := hgcont.tendsto s
      simpa using h5
    have hU0 : Tendsto (fun t : ℝ => pressureRate src tgt q ℓ s
        * Real.exp (|t - s| * L1)) (nhds s)
        (nhds (pressureRate src tgt q ℓ s)) := by
      have h5 := hgcont'.tendsto s
      simpa using h5
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hL0 hU0
      (Eventually.of_forall hLb) (Eventually.of_forall hUb)
  -- decay to zero
  have htend : Tendsto (pressureRate src tgt q ℓ) atTop (nhds 0) := by
    have hb : ∀ᶠ s : ℝ in atTop, pressureRate src tgt q ℓ s
        ≤ Real.exp (-(s * ℓ₀)) * pressureRate src tgt q ℓ 0 := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
      have h1 := hupper (s := 0) (t := s) hs
      rwa [sub_zero] at h1
    have h0 : ∀ᶠ s : ℝ in atTop,
        0 ≤ pressureRate src tgt q ℓ s :=
      Eventually.of_forall fun s => (hrpos s).le
    have hexp : Tendsto (fun s : ℝ =>
        Real.exp (-(s * ℓ₀)) * pressureRate src tgt q ℓ 0) atTop
        (nhds 0) := by
      have h6 : Tendsto (fun s : ℝ => Real.exp (-(s * ℓ₀))) atTop
          (nhds 0) := by
        have h7 : Tendsto (fun s : ℝ => -(s * ℓ₀)) atTop atBot :=
          tendsto_neg_atTop_atBot.comp
            (tendsto_id.atTop_mul_const hℓ₀pos)
        exact Real.tendsto_exp_atBot.comp h7
      have h8 := h6.mul_const (pressureRate src tgt q ℓ 0)
      rwa [zero_mul] at h8
    exact squeeze_zero' h0 hb hexp
  refine ⟨hanti, hcont, htend, ?_, ?_, ?_⟩
  · -- supercritical: a unique positive pressure root
    intro hsup
    obtain ⟨S, hSpos, hSlt⟩ : ∃ S : ℝ, 0 < S
        ∧ pressureRate src tgt q ℓ S < 1 := by
      have h9 := htend.eventually_lt_const
        (show (0 : ℝ) < 1 by norm_num)
      obtain ⟨S₀, hS₀⟩ := (h9.and (eventually_gt_atTop 0)).exists
      exact ⟨S₀, hS₀.2, hS₀.1⟩
    have hIVT := intermediate_value_Icc' hSpos.le
      hcont.continuousOn
    obtain ⟨β, hβmem, hβeq⟩ := hIVT ⟨hSlt.le, hsup.le⟩
    refine ⟨β, ⟨?_, hβeq⟩, ?_⟩
    · rcases lt_or_eq_of_le hβmem.1 with h | h
      · exact h
      · exfalso
        rw [← h] at hβeq
        linarith
    · rintro β' ⟨hβ'pos, hβ'eq⟩
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · have h1 := hanti h
        rw [hβeq, hβ'eq] at h1
        exact lt_irrefl _ h1
      · have h1 := hanti h
        rw [hβeq, hβ'eq] at h1
        exact lt_irrefl _ h1
  · -- critical: only the root β = 0
    intro hcrit β hβ hβeq
    have h1 := hanti hβ
    rw [hcrit, hβeq] at h1
    exact lt_irrefl _ h1
  · -- subcritical: no nonnegative root
    intro hsub β hβ hβeq
    rcases lt_or_eq_of_le hβ with h | h
    · have h1 := hanti h
      rw [hβeq] at h1
      linarith
    · rw [← h] at hβeq
      linarith

end Kernel

/-! ## The Perron root is the growth rate -/

section PerronRoot

open Matrix

/-- **The eigenvalue sandwich**: for a nonnegative matrix with a
diagonal witness, any eigenvalue carrying an entrywise positive
eigenvector equals the Gelfand–Fekete growth rate `pRad`.  The
eigenvector squeezes the entry sum of powers between two multiples of
`r ^ k`, and taking logarithmic averages identifies the limits. -/
theorem eigenvalue_eq_pRad {A : Matrix V V ℝ}
    (hA : EntryNonneg A) (hw : HasDiagWitness A) {r : ℝ} (hr : 0 < r)
    {h : V → ℝ} (hh : ∀ i, 0 < h i)
    (heig : A.mulVec h = r • h) :
    r = pRad A := by
  classical
  -- A^k h = r^k h
  have hpow : ∀ k : ℕ, (A ^ k).mulVec h = (r ^ k) • h := by
    intro k
    induction k with
    | zero =>
      rw [pow_zero, pow_zero, Matrix.one_mulVec, one_smul]
    | succ k ih =>
      rw [pow_succ', pow_succ']
      rw [← Matrix.mulVec_mulVec, ih]
      rw [Matrix.mulVec_smul, heig, smul_smul, mul_comm]
  -- entrywise sandwich for the entry sum
  set hmin := Finset.univ.inf' Finset.univ_nonempty h with hhmin
  set hmax := Finset.univ.sup' Finset.univ_nonempty h with hhmax
  have hminpos : 0 < hmin := by
    rw [hhmin, Finset.lt_inf'_iff]
    intro i _
    exact hh i
  have hmaxpos : 0 < hmax :=
    lt_of_lt_of_le (hh (Classical.arbitrary V))
      (Finset.le_sup' _ (Finset.mem_univ _))
  have hminle : ∀ i, hmin ≤ h i := by
    intro i
    rw [hhmin]
    exact Finset.inf'_le _ (Finset.mem_univ i)
  have hlemax : ∀ i, h i ≤ hmax := by
    intro i
    rw [hhmax]
    exact Finset.le_sup' _ (Finset.mem_univ i)
  -- hmin * entrySum(A^k) ≤ Σ_x r^k h x ≤ hmax * entrySum(A^k)
  have hsand : ∀ k : ℕ,
      hmin * entrySum (A ^ k) ≤ (∑ x, r ^ k * h x)
      ∧ (∑ x, r ^ k * h x) ≤ hmax * entrySum (A ^ k) := by
    intro k
    have hAk : ∀ x y, 0 ≤ (A ^ k) x y := entryNonneg_pow hA k
    have h4 : ∀ x, r ^ k * h x = ∑ y, (A ^ k) x y * h y := by
      intro x
      have h5 := congrFun (hpow k) x
      rw [Matrix.mulVec, dotProduct] at h5
      rw [Pi.smul_apply, smul_eq_mul] at h5
      exact h5.symm
    constructor
    · rw [entrySum, Finset.mul_sum]
      refine Finset.sum_le_sum fun x _ => ?_
      rw [h4 x, Finset.mul_sum]
      refine Finset.sum_le_sum fun y _ => ?_
      rw [mul_comm hmin ((A ^ k) x y)]
      exact mul_le_mul_of_nonneg_left (hminle y) (hAk x y)
    · rw [entrySum, Finset.mul_sum]
      refine Finset.sum_le_sum fun x _ => ?_
      rw [h4 x, Finset.mul_sum]
      refine Finset.sum_le_sum fun y _ => ?_
      rw [mul_comm hmax ((A ^ k) x y)]
      exact mul_le_mul_of_nonneg_left (hlemax y) (hAk x y)
  set H := ∑ x, h x with hH
  have hHpos : 0 < H := by
    rw [hH]
    exact Finset.sum_pos (fun i _ => hh i) Finset.univ_nonempty
  have hsum : ∀ k : ℕ, ∑ x, r ^ k * h x = r ^ k * H := by
    intro k
    rw [hH, Finset.mul_sum]
  -- squeeze the growth sequence
  have hgrow : Tendsto (fun k : ℕ => growthSeq A k / k) atTop
      (nhds (Real.log r)) := by
    have hES : ∀ k : ℕ, 0 < entrySum (A ^ k) :=
      fun k => entrySum_pow_pos hA hw k
    have hlow : ∀ k : ℕ,
        Real.log (r ^ k * H) - Real.log hmax
          ≤ growthSeq A k := by
      intro k
      have h6 := (hsand k).2
      rw [hsum k] at h6
      have h7 : Real.log (r ^ k * H)
          ≤ Real.log (hmax * entrySum (A ^ k)) :=
        Real.log_le_log (by positivity) h6
      rw [Real.log_mul hmaxpos.ne' (hES k).ne'] at h7
      rw [growthSeq]
      linarith
    have hup : ∀ k : ℕ,
        growthSeq A k ≤ Real.log (r ^ k * H)
          - Real.log hmin := by
      intro k
      have h6 := (hsand k).1
      rw [hsum k] at h6
      have h7 : Real.log (hmin * entrySum (A ^ k))
          ≤ Real.log (r ^ k * H) :=
        Real.log_le_log (mul_pos hminpos (hES k)) h6
      rw [Real.log_mul hminpos.ne' (hES k).ne'] at h7
      rw [growthSeq]
      linarith
    have hloglin : ∀ k : ℕ, Real.log (r ^ k * H)
        = k * Real.log r + Real.log H := by
      intro k
      rw [Real.log_mul (by positivity) hHpos.ne',
        Real.log_pow]
    have hsq : Tendsto (fun k : ℕ =>
        (k * Real.log r + Real.log H - Real.log hmax) / k)
        atTop (nhds (Real.log r)) := by
      have h8 : Tendsto (fun k : ℕ => Real.log r
          + (Real.log H - Real.log hmax) / k) atTop
          (nhds (Real.log r + 0)) :=
        tendsto_const_nhds.add
          (tendsto_const_div_atTop_nhds_zero_nat _)
      rw [add_zero] at h8
      refine Tendsto.congr' ?_ h8
      filter_upwards [eventually_ne_atTop 0] with k hk
      have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
      field_simp
      ring
    have hsq2 : Tendsto (fun k : ℕ =>
        (k * Real.log r + Real.log H - Real.log hmin) / k)
        atTop (nhds (Real.log r)) := by
      have h8 : Tendsto (fun k : ℕ => Real.log r
          + (Real.log H - Real.log hmin) / k) atTop
          (nhds (Real.log r + 0)) :=
        tendsto_const_nhds.add
          (tendsto_const_div_atTop_nhds_zero_nat _)
      rw [add_zero] at h8
      refine Tendsto.congr' ?_ h8
      filter_upwards [eventually_ne_atTop 0] with k hk
      have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
      field_simp
      ring
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hsq hsq2
      ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with k hk
      have hkR : (0 : ℝ) < k := by exact_mod_cast hk
      have h10 := hlow k
      rw [hloglin k] at h10
      rw [div_le_div_iff₀ hkR hkR]
      exact mul_le_mul_of_nonneg_right h10 hkR.le
    · filter_upwards [eventually_gt_atTop 0] with k hk
      have hkR : (0 : ℝ) < k := by exact_mod_cast hk
      have h10 := hup k
      rw [hloglin k] at h10
      rw [div_le_div_iff₀ hkR hkR]
      exact mul_le_mul_of_nonneg_right h10 hkR.le
  have h11 := tendsto_growthSeq hA hw
  have h12 : Real.log r = Real.log (pRad A) :=
    tendsto_nhds_unique hgrow h11
  have h13 : r = Real.exp (Real.log r) :=
    (Real.exp_log hr).symm
  rw [h13, h12, Real.exp_log (pRad_pos A)]

/-- Irreducibility provides a diagonal witness: some power has a
positive diagonal entry. -/
theorem hasDiagWitness_of_isIrreducible {A : Matrix V V ℝ}
    (hA : A.IsIrreducible) : HasDiagWitness A := by
  obtain ⟨k, hk, hpos⟩ :=
    ((Matrix.isIrreducible_iff_exists_pow_pos hA.nonneg).1 hA)
      (Classical.arbitrary V) (Classical.arbitrary V)
  exact ⟨Classical.arbitrary V, k, hk, hpos⟩

omit [DecidableEq V] in
/-- An eigenvalue of an irreducible matrix carrying an entrywise
positive eigenvector is strictly positive. -/
theorem eigenvalue_pos_of_isIrreducible {A : Matrix V V ℝ}
    (hA : A.IsIrreducible) {r : ℝ} {x : V → ℝ}
    (hx : ∀ i, 0 < x i) (heig : A.mulVec x = r • x) : 0 < r := by
  have i := Classical.arbitrary V
  obtain ⟨j₀, hj₀⟩ := hA.exists_pos_entry i
  have h1 : 0 < A.mulVec x i := by
    rw [Matrix.mulVec, dotProduct]
    exact Finset.sum_pos'
      (fun j _ => mul_nonneg (hA.nonneg i j) (hx j).le)
      ⟨j₀, Finset.mem_univ j₀, mul_pos hj₀ (hx j₀)⟩
  rw [heig, Pi.smul_apply, smul_eq_mul] at h1
  rcases mul_pos_iff.mp h1 with ⟨hr, _⟩ | ⟨_, hxneg⟩
  · exact hr
  · linarith [hx i]

/-- **The Perron root of an irreducible matrix is the growth rate**:
any eigenvalue with an entrywise positive eigenvector equals
`pRad A`. -/
theorem eigenvalue_eq_pRad_of_isIrreducible {A : Matrix V V ℝ}
    (hA : A.IsIrreducible) {r : ℝ} {x : V → ℝ}
    (hx : ∀ i, 0 < x i) (heig : A.mulVec x = r • x) :
    r = pRad A :=
  eigenvalue_eq_pRad hA.nonneg (hasDiagWitness_of_isIrreducible hA)
    (eigenvalue_pos_of_isIrreducible hA hx heig) hx heig

/-- **The Perron–Frobenius package for irreducible matrices**: the
Gelfand–Fekete growth rate `pRad A` is itself an eigenvalue, carried
by an entrywise positive eigenvector (which is unique up to a scalar
by `Matrix.IsIrreducible.exists_eq_smul_of_mulVec_eq_smul`, and whose
eigenvalue is the unique one admitting a positive eigenvector by
`Matrix.IsIrreducible.eigenvalue_eq_of_pos_eigenvectors`). -/
theorem exists_pRad_eigenvector_of_isIrreducible {A : Matrix V V ℝ}
    (hA : A.IsIrreducible) :
    ∃ x : V → ℝ, (∀ i, 0 < x i) ∧ A.mulVec x = pRad A • x := by
  obtain ⟨r, x, _, hx, heig⟩ := hA.exists_pos_eigenvector
  rw [← eigenvalue_eq_pRad_of_isIrreducible hA hx heig]
  exact ⟨x, hx, heig⟩

end PerronRoot

end NCG
