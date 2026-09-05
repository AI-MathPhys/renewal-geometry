/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Finite quantum relative entropy: Klein inequality and faithfulness

Foundation layer for `thm:accepted-Petz-sufficiency` (QS.1–QS.4) and
`cor:accepted-BKM-loss` (QS.5): the finite-dimensional quantum relative
entropy through the matrix spectral theorem.

* `matFun`: spectral functional calculus `f(S) = U diag(f ∘ λ) U^*`;
* `matLog`: the matrix logarithm (junk value `log 0 = 0` off the support);
* `relEntropy`: `D(ρ‖σ) = Re Tr ρ (log ρ − log σ)`;
* `relEntropy_nonneg` (**Klein inequality**): `D(ρ‖σ) ≥ 0` for states with
  faithful `σ`;
* `relEntropy_eq_zero_iff` (**faithfulness**): `D(ρ‖σ) = 0 ↔ ρ = σ` — the
  identity-channel case of the sufficiency criterion.
-/

open Matrix Unitary Finset
open scoped ComplexOrder

namespace NCG
namespace QRE

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {ρ σ S : Matrix n n ℂ}

/-- Spectral functional calculus of a Hermitian matrix. -/
noncomputable def matFun (hS : S.IsHermitian) (f : ℝ → ℝ) : Matrix n n ℂ :=
  conjStarAlgAut ℂ _ hS.eigenvectorUnitary
    (diagonal (RCLike.ofReal ∘ fun i => f (hS.eigenvalues i)))

/-- Matrix logarithm through the spectrum (junk `Real.log 0 = 0`). -/
noncomputable def matLog (hS : S.IsHermitian) : Matrix n n ℂ :=
  matFun hS Real.log

/-- Finite quantum relative entropy `D(ρ‖σ) = Re Tr ρ (log ρ − log σ)`. -/
noncomputable def relEntropy (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) : ℝ :=
  ((ρ * (matLog hρ - matLog hσ)).trace).re

/-- The eigenbasis overlap matrix `W = U_ρ^* U_σ`. -/
noncomputable def overlap (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    Matrix n n ℂ :=
  star (hρ.eigenvectorUnitary : Matrix n n ℂ) *
    (hσ.eigenvectorUnitary : Matrix n n ℂ)

theorem coe_mul_star (u : unitary (Matrix n n ℂ)) :
    (u : Matrix n n ℂ) * star (u : Matrix n n ℂ) = 1 :=
  Unitary.mul_star_self_of_mem u.prop

theorem star_mul_coe (u : unitary (Matrix n n ℂ)) :
    star (u : Matrix n n ℂ) * (u : Matrix n n ℂ) = 1 :=
  Unitary.star_mul_self_of_mem u.prop

theorem overlap_mul_star (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    overlap hρ hσ * star (overlap hρ hσ) = 1 := by
  unfold overlap
  rw [star_mul, star_star, Matrix.mul_assoc, ← Matrix.mul_assoc
    (hσ.eigenvectorUnitary : Matrix n n ℂ), coe_mul_star,
    Matrix.one_mul, star_mul_coe]

theorem star_mul_overlap (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    star (overlap hρ hσ) * overlap hρ hσ = 1 := by
  unfold overlap
  rw [star_mul, star_star, Matrix.mul_assoc, ← Matrix.mul_assoc
    (hρ.eigenvectorUnitary : Matrix n n ℂ), coe_mul_star,
    Matrix.one_mul, star_mul_coe]

/-! ### Trace computations -/

theorem trace_conj (u : unitary (Matrix n n ℂ)) (x : Matrix n n ℂ) :
    (conjStarAlgAut ℂ _ u x).trace = x.trace := by
  rw [conjStarAlgAut_apply, Matrix.trace_mul_cycle, star_mul_coe,
    Matrix.one_mul]

theorem trace_sandwich (u : unitary (Matrix n n ℂ)) (x : Matrix n n ℂ) :
    ((u : Matrix n n ℂ) * x * star (u : Matrix n n ℂ)).trace = x.trace := by
  rw [Matrix.trace_mul_cycle, star_mul_coe, Matrix.one_mul]

theorem matFun_mul (hS : S.IsHermitian) (f g : ℝ → ℝ) :
    matFun hS f * matFun hS g = matFun hS (fun x => f x * g x) := by
  unfold matFun
  rw [← map_mul (conjStarAlgAut ℂ _ hS.eigenvectorUnitary),
    diagonal_mul_diagonal]
  have harg : (fun i => (RCLike.ofReal (K := ℂ) ∘ fun i => f (hS.eigenvalues i)) i *
      (RCLike.ofReal (K := ℂ) ∘ fun i => g (hS.eigenvalues i)) i) =
      RCLike.ofReal (K := ℂ) ∘ fun i =>
        f (hS.eigenvalues i) * g (hS.eigenvalues i) := by
    funext i
    simp [Function.comp, RCLike.ofReal_mul]
  rw [harg]

/-- Trace of `diag(a) · W diag(b) W^*` as a double sum. -/
theorem trace_diag_mul_conj (a b : n → ℝ) (W : Matrix n n ℂ) :
    (diagonal (RCLike.ofReal ∘ a) *
        (W * diagonal (RCLike.ofReal ∘ b) * star W)).trace =
      ∑ i, ∑ j, ((a i : ℂ) * (b j : ℂ)) * (W i j * star (W i j)) := by
  have hentry : ∀ i, (diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ a) *
      (W * diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ b) * star W)) i i =
      ∑ j, ((a i : ℂ) * (b j : ℂ)) * (W i j * star (W i j)) := by
    intro i
    rw [Matrix.diagonal_mul, Function.comp_apply, Matrix.mul_apply,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mul_diagonal, Matrix.star_apply, Function.comp_apply]
    change (a i : ℂ) * (W i j * (b j : ℂ) * star (W i j)) =
      (a i : ℂ) * (b j : ℂ) * (W i j * star (W i j))
    ring
  simp only [Matrix.trace, Matrix.diag]
  exact Finset.sum_congr rfl fun i _ => hentry i

theorem trace_diag_mul_conj_re (a b : n → ℝ) (W : Matrix n n ℂ) :
    ((diagonal (RCLike.ofReal ∘ a) *
        (W * diagonal (RCLike.ofReal ∘ b) * star W)).trace).re =
      ∑ i, ∑ j, a i * b j * Complex.normSq (W i j) := by
  rw [trace_diag_mul_conj]
  have hterm : ∀ i j, ((a i : ℂ) * (b j : ℂ)) * (W i j * star (W i j)) =
      ((a i * b j * Complex.normSq (W i j) : ℝ) : ℂ) := by
    intro i j
    rw [Complex.star_def, Complex.mul_conj]
    push_cast
    ring
  simp only [hterm]
  push_cast
  simp

/-- Row sums of the squared overlap are one. -/
theorem sum_normSq_row {W : Matrix n n ℂ} (hW : W * star W = 1) (i : n) :
    ∑ j, Complex.normSq (W i j) = 1 := by
  have h := congrArg (fun M : Matrix n n ℂ => (M i i).re) hW
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq,
    Complex.one_re] at h
  rw [← h, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.mul_conj]
  simp

/-- Column sums of the squared overlap are one. -/
theorem sum_normSq_col {W : Matrix n n ℂ} (hW : star W * W = 1) (j : n) :
    ∑ i, Complex.normSq (W i j) = 1 := by
  have h := congrArg (fun M : Matrix n n ℂ => (M j j).re) hW
  simp only [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq,
    Complex.one_re] at h
  rw [← h, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, mul_comm, Complex.mul_conj]
  simp

/-- `Re Tr(ρ · f(ρ)) = ∑ p_i f(p_i)`. -/
theorem trace_mul_matFun_self (hρ : ρ.IsHermitian) (f : ℝ → ℝ) :
    ((ρ * matFun hρ f).trace).re =
      ∑ i, hρ.eigenvalues i * f (hρ.eigenvalues i) := by
  have hid : ρ = matFun hρ id := by
    unfold matFun
    exact hρ.spectral_theorem
  have hprod := matFun_mul hρ id f
  rw [← hid] at hprod
  simp only [id_eq] at hprod
  rw [hprod]
  unfold matFun
  rw [trace_conj, Matrix.trace_diagonal, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => by simp

set_option maxHeartbeats 1600000 in -- heavy unitary conjugation rewrites
/-- `Re Tr(ρ · f(σ)) = ∑_{ij} p_i f(q_j) |W_{ij}|²`. -/
theorem trace_mul_matFun_re (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian)
    (f : ℝ → ℝ) :
    ((ρ * matFun hσ f).trace).re =
      ∑ i, ∑ j, hρ.eigenvalues i * f (hσ.eigenvalues j) *
        Complex.normSq (overlap hρ hσ i j) := by
  have hρdec := hρ.spectral_theorem
  rw [conjStarAlgAut_apply] at hρdec
  have hσdec : matFun hσ f =
      (hσ.eigenvectorUnitary : Matrix n n ℂ) *
        diagonal (RCLike.ofReal ∘ fun j => f (hσ.eigenvalues j)) *
        star (hσ.eigenvectorUnitary : Matrix n n ℂ) := by
    unfold matFun
    rw [conjStarAlgAut_apply]
  have hmul : ρ * matFun hσ f =
      ((hρ.eigenvectorUnitary : Matrix n n ℂ) *
        diagonal (RCLike.ofReal ∘ hρ.eigenvalues) *
        star (hρ.eigenvectorUnitary : Matrix n n ℂ)) *
      ((hσ.eigenvectorUnitary : Matrix n n ℂ) *
        diagonal (RCLike.ofReal ∘ fun j => f (hσ.eigenvalues j)) *
        star (hσ.eigenvectorUnitary : Matrix n n ℂ)) := by
    rw [← hρdec, ← hσdec]
  have hshape : ((hρ.eigenvectorUnitary : Matrix n n ℂ) *
        diagonal (RCLike.ofReal ∘ hρ.eigenvalues) *
        star (hρ.eigenvectorUnitary : Matrix n n ℂ)) *
      ((hσ.eigenvectorUnitary : Matrix n n ℂ) *
        diagonal (RCLike.ofReal ∘ fun j => f (hσ.eigenvalues j)) *
        star (hσ.eigenvectorUnitary : Matrix n n ℂ)) =
      (hρ.eigenvectorUnitary : Matrix n n ℂ) *
        (diagonal (RCLike.ofReal ∘ hρ.eigenvalues) *
          (overlap hρ hσ *
            diagonal (RCLike.ofReal ∘ fun j => f (hσ.eigenvalues j)) *
            star (overlap hρ hσ))) *
        star (hρ.eigenvectorUnitary : Matrix n n ℂ) := by
    unfold overlap
    rw [star_mul, star_star]
    conv_lhs => rw [← Matrix.mul_one
      (((hρ.eigenvectorUnitary : Matrix n n ℂ) *
          diagonal (RCLike.ofReal ∘ hρ.eigenvalues) *
          star (hρ.eigenvectorUnitary : Matrix n n ℂ)) *
        ((hσ.eigenvectorUnitary : Matrix n n ℂ) *
          diagonal (RCLike.ofReal ∘ fun j => f (hσ.eigenvalues j)) *
          star (hσ.eigenvectorUnitary : Matrix n n ℂ))),
      ← coe_mul_star hρ.eigenvectorUnitary]
    simp only [Matrix.mul_assoc]
  rw [hmul]
  rw [hshape]
  rw [trace_sandwich]
  exact trace_diag_mul_conj_re hρ.eigenvalues
    (fun j => f (hσ.eigenvalues j)) (overlap hρ hσ)

/-! ### The scalar Klein inequality -/

theorem klein_scalar {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) :
    p - q ≤ p * Real.log p - p * Real.log q := by
  rcases eq_or_lt_of_le hp with h0 | hp
  · rw [← h0]
    simp only [zero_sub, zero_mul, sub_self]
    linarith
  · have hlog := Real.log_le_sub_one_of_pos (div_pos hq hp)
    rw [Real.log_div hq.ne' hp.ne'] at hlog
    have hmul := mul_le_mul_of_nonneg_left hlog hp.le
    have hpq : p * (q / p) = q := by
      field_simp
    nlinarith

theorem klein_scalar_eq {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q)
    (heq : p * Real.log p - p * Real.log q = p - q) : p = q := by
  rcases eq_or_lt_of_le hp with h0 | hp
  · exfalso
    rw [← h0] at heq
    simp only [zero_mul, sub_self, zero_sub] at heq
    linarith
  · by_contra hne
    have hqp : q / p ≠ 1 := by
      intro h
      apply hne
      field_simp at h
      linarith
    have hstrict := Real.log_lt_sub_one_of_pos (div_pos hq hp) hqp
    rw [Real.log_div hq.ne' hp.ne'] at hstrict
    have hmul := mul_lt_mul_of_pos_left hstrict hp
    have hpq : p * (q / p) = q := by
      field_simp
    nlinarith

/-! ### Klein inequality and faithfulness for the relative entropy -/

theorem sum_eigenvalues_eq_one (hρ : ρ.IsHermitian) (h1 : ρ.trace = 1) :
    ∑ i, hρ.eigenvalues i = 1 := by
  have h := hρ.trace_eq_sum_eigenvalues
  rw [h1] at h
  have h' : (1 : ℂ) = ∑ i, Complex.ofReal (hρ.eigenvalues i) := h
  exact_mod_cast h'.symm

/-- The relative entropy as a doubly indexed Klein sum. -/
theorem relEntropy_eq_klein_sum (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) :
    relEntropy hρ hσ =
      ∑ i, ∑ j, Complex.normSq (overlap hρ hσ i j) *
        (hρ.eigenvalues i * Real.log (hρ.eigenvalues i) -
          hρ.eigenvalues i * Real.log (hσ.eigenvalues j)) := by
  unfold relEntropy matLog
  rw [mul_sub, Matrix.trace_sub, Complex.sub_re,
    trace_mul_matFun_self hρ Real.log, trace_mul_matFun_re hρ hσ Real.log]
  have hrow : ∀ i, ∑ j, Complex.normSq (overlap hρ hσ i j) = 1 :=
    sum_normSq_row (overlap_mul_star hρ hσ)
  have hexp : ∑ i, hρ.eigenvalues i * Real.log (hρ.eigenvalues i) =
      ∑ i, ∑ j, Complex.normSq (overlap hρ hσ i j) *
        (hρ.eigenvalues i * Real.log (hρ.eigenvalues i)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_mul, hrow i, one_mul]
  rw [hexp, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => by ring

/-- The centered Klein sum vanishes for a pair of states. -/
theorem klein_center_zero (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian)
    (hρ1 : ρ.trace = 1) (hσ1 : σ.trace = 1) :
    ∑ i, ∑ j, Complex.normSq (overlap hρ hσ i j) *
      (hρ.eigenvalues i - hσ.eigenvalues j) = 0 := by
  have hrow : ∀ i, ∑ j, Complex.normSq (overlap hρ hσ i j) = 1 :=
    sum_normSq_row (overlap_mul_star hρ hσ)
  have hcol : ∀ j, ∑ i, Complex.normSq (overlap hρ hσ i j) = 1 :=
    sum_normSq_col (star_mul_overlap hρ hσ)
  have h1 : ∑ i, ∑ j, Complex.normSq (overlap hρ hσ i j) *
      hρ.eigenvalues i = 1 := by
    rw [← sum_eigenvalues_eq_one hρ hρ1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_mul, hrow i, one_mul]
  have h2 : ∑ i, ∑ j, Complex.normSq (overlap hρ hσ i j) *
      hσ.eigenvalues j = 1 := by
    rw [Finset.sum_comm, ← sum_eigenvalues_eq_one hσ hσ1]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_mul, hcol j, one_mul]
  have hsplit : ∑ i, ∑ j, Complex.normSq (overlap hρ hσ i j) *
      (hρ.eigenvalues i - hσ.eigenvalues j) =
      (∑ i, ∑ j, Complex.normSq (overlap hρ hσ i j) * hρ.eigenvalues i) -
        ∑ i, ∑ j, Complex.normSq (overlap hρ hσ i j) * hσ.eigenvalues j := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => by ring
  rw [hsplit, h1, h2, sub_self]

/-- **The Klein inequality**: `D(ρ‖σ) ≥ 0` for states with faithful `σ`. -/
theorem relEntropy_nonneg (hρp : ρ.PosSemidef) (hσp : σ.PosDef)
    (hρ1 : ρ.trace = 1) (hσ1 : σ.trace = 1) :
    0 ≤ relEntropy hρp.1 hσp.1 := by
  rw [relEntropy_eq_klein_sum]
  have hcenter := klein_center_zero hρp.1 hσp.1 hρ1 hσ1
  rw [← hcenter]
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  exact mul_le_mul_of_nonneg_left
    (klein_scalar (hρp.eigenvalues_nonneg i) (hσp.eigenvalues_pos j))
    (Complex.normSq_nonneg _)

/-- **Faithfulness**: `D(ρ‖σ) = 0` exactly when `ρ = σ`. -/
theorem relEntropy_eq_zero_iff (hρp : ρ.PosSemidef) (hσp : σ.PosDef)
    (hρ1 : ρ.trace = 1) (hσ1 : σ.trace = 1) :
    relEntropy hρp.1 hσp.1 = 0 ↔ ρ = σ := by
  constructor
  · intro h0
    have hcenter := klein_center_zero hρp.1 hσp.1 hρ1 hσ1
    have hnn : ∀ i ∈ Finset.univ (α := n), ∀ j ∈ Finset.univ (α := n),
        0 ≤ Complex.normSq (overlap hρp.1 hσp.1 i j) *
          (hρp.1.eigenvalues i * Real.log (hρp.1.eigenvalues i) -
            hρp.1.eigenvalues i * Real.log (hσp.1.eigenvalues j)) -
          Complex.normSq (overlap hρp.1 hσp.1 i j) *
            (hρp.1.eigenvalues i - hσp.1.eigenvalues j) := by
      intro i _ j _
      rw [sub_nonneg]
      exact mul_le_mul_of_nonneg_left
        (klein_scalar (hρp.eigenvalues_nonneg i) (hσp.eigenvalues_pos j))
        (Complex.normSq_nonneg _)
    have hsum0 : ∑ i, ∑ j, (Complex.normSq (overlap hρp.1 hσp.1 i j) *
        (hρp.1.eigenvalues i * Real.log (hρp.1.eigenvalues i) -
          hρp.1.eigenvalues i * Real.log (hσp.1.eigenvalues j)) -
        Complex.normSq (overlap hρp.1 hσp.1 i j) *
          (hρp.1.eigenvalues i - hσp.1.eigenvalues j)) = 0 := by
      have hsplit : ∑ i, ∑ j, (Complex.normSq (overlap hρp.1 hσp.1 i j) *
          (hρp.1.eigenvalues i * Real.log (hρp.1.eigenvalues i) -
            hρp.1.eigenvalues i * Real.log (hσp.1.eigenvalues j)) -
          Complex.normSq (overlap hρp.1 hσp.1 i j) *
            (hρp.1.eigenvalues i - hσp.1.eigenvalues j)) =
          (∑ i, ∑ j, Complex.normSq (overlap hρp.1 hσp.1 i j) *
            (hρp.1.eigenvalues i * Real.log (hρp.1.eigenvalues i) -
              hρp.1.eigenvalues i * Real.log (hσp.1.eigenvalues j))) -
            ∑ i, ∑ j, Complex.normSq (overlap hρp.1 hσp.1 i j) *
              (hρp.1.eigenvalues i - hσp.1.eigenvalues j) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ => by
          rw [Finset.sum_sub_distrib]
      rw [hsplit, ← relEntropy_eq_klein_sum, h0, hcenter, sub_self]
    have hterm0 : ∀ i j, Complex.normSq (overlap hρp.1 hσp.1 i j) *
        (hρp.1.eigenvalues i * Real.log (hρp.1.eigenvalues i) -
          hρp.1.eigenvalues i * Real.log (hσp.1.eigenvalues j)) -
        Complex.normSq (overlap hρp.1 hσp.1 i j) *
          (hρp.1.eigenvalues i - hσp.1.eigenvalues j) = 0 := by
      intro i j
      have houter := (Finset.sum_eq_zero_iff_of_nonneg
        (fun i hi => Finset.sum_nonneg fun j hj => hnn i hi j hj)).mp hsum0
        i (Finset.mem_univ i)
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (fun j hj => hnn i (Finset.mem_univ i) j hj)).mp houter
        j (Finset.mem_univ j)
    have hcases : ∀ i j, overlap hρp.1 hσp.1 i j = 0 ∨
        hρp.1.eigenvalues i = hσp.1.eigenvalues j := by
      intro i j
      have h := hterm0 i j
      rw [← mul_sub, mul_eq_zero] at h
      rcases h with h | h
      · exact Or.inl (Complex.normSq_eq_zero.mp h)
      · refine Or.inr (klein_scalar_eq (hρp.eigenvalues_nonneg i)
          (hσp.eigenvalues_pos j) ?_)
        have := sub_eq_zero.mp h
        linarith
    set U : Matrix n n ℂ := (hρp.1.eigenvectorUnitary : Matrix n n ℂ)
      with hUdef
    set V : Matrix n n ℂ := (hσp.1.eigenvectorUnitary : Matrix n n ℂ)
      with hVdef
    set W := overlap hρp.1 hσp.1 with hWdef
    set dp : Matrix n n ℂ :=
      diagonal (RCLike.ofReal ∘ hρp.1.eigenvalues) with hdp
    set dq : Matrix n n ℂ :=
      diagonal (RCLike.ofReal ∘ hσp.1.eigenvalues) with hdq
    have hintertwine : dp * W = W * dq := by
      ext i j
      rw [hdp, hdq, Matrix.diagonal_mul, Matrix.mul_diagonal]
      rcases hcases i j with h | h
      · rw [h, mul_zero, zero_mul]
      · rw [Function.comp_apply, Function.comp_apply, h, mul_comm]
    have hV : V = U * W := by
      rw [hVdef, hUdef, hWdef]
      unfold overlap
      rw [← Matrix.mul_assoc, coe_mul_star, Matrix.one_mul]
    have hσdec : σ = V * dq * star V := by
      have h := hσp.1.spectral_theorem
      rw [conjStarAlgAut_apply] at h
      rw [hVdef, hdq]
      exact h
    have hρdec : ρ = U * dp * star U := by
      have h := hρp.1.spectral_theorem
      rw [conjStarAlgAut_apply] at h
      rw [hUdef, hdp]
      exact h
    rw [hρdec, hσdec, hV, star_mul]
    have hWW : W * star W = 1 := overlap_mul_star hρp.1 hσp.1
    calc U * dp * star U
        = U * (dp * (W * star W)) * star U := by rw [hWW]; noncomm_ring
      _ = U * ((dp * W) * star W) * star U := by noncomm_ring
      _ = U * ((W * dq) * star W) * star U := by rw [hintertwine]
      _ = U * W * dq * (star W * star U) := by noncomm_ring
  · intro h
    subst h
    unfold relEntropy
    simp

end QRE
end NCG
