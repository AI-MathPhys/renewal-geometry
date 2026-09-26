/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.StandardModel.RecordWitnessNormalization
import RenewalGeometry.StandardModel.FiveKrausFreedomExact

/-!
# Record-complete nonidentifiability witness: the Clifford family

Third layer of `prop:record-witness` of the spacetime–gauge duality paper: the **Clifford**
realization `H^q_e = √(6/5) ∑_μ O_{eμ} Γ_μ ⊗ I₅`, for five pairwise anticommuting Hermitian
involutions `Γ_μ` (`CliffordFamily`) on a `d`-dimensional space and a Helmert frame `O`
(`FiveKraus.HelmertFrame`, `eq:helmert-frame`).

* `CliffordFamily.trace_eq_zero`, `CliffordFamily.trace_mul`: anticommuting involutions are
  traceless and pairwise trace-orthogonal, `Tr(Γ_μ Γ_ν) = d δ_{μν}`;
* `CliffordFamily.sum_smul_mul_self`: `(∑_μ a_μ Γ_μ)² = (∑_μ a_μ²) I`;
* `cliffordH F G e = √(6/5) ∑_μ O_{eμ} Γ_μ`: Hermitian involution (the rows of `√(6/5) O` are
  unit vectors), traceless, zero sum (`Oᵀ𝟏 = 0`), Gram `Tr(H_e H_f) = d` / `−d/5`
  (`OOᵀ = I − 𝟏𝟏ᵀ/6`);
* `cliffordHq F G e = cliffordH F G e ⊗ I₅`: the same on `d × 5`, with Gram `5d` / `−d`;
  for `d = 4` this is `20` / `−4`, the same Gram as the commuting family `H^c`;
* `clifford_record_data`: the Clifford completions `K^q_e = I/√18 + (i/3) H^q_e` on a
  `20`-dimensional carrier satisfy `eq:six-edge-normalization` and
  `eq:matching-record-data` (`∑ K^*K = I`, `∑ K = √2 I`, `K^*K = I/6`,
  `Tr K_e^* K_f = 10/3 | 2/3`).

Not formalised here: a concrete `CliffordFamily (Fin 4)` and a concrete Helmert frame (both
exist; the library's `CliffordTwirlMatterAudit` gammas are the natural instance), the algebra
identity `C*(K^q) = M₄(ℂ) ⊗ I₅`, the word effects `eq:record-word-effect` and the Choi
spectrum `eq:matching-Choi-spectrum`.
-/

open Matrix Kronecker

namespace RenewalGeometry
namespace RecordWitness

open FiveKraus

section Abstract

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- Five pairwise anticommuting Hermitian involutions (a Clifford family). -/
structure CliffordFamily (d : Type*) [Fintype d] [DecidableEq d] where
  /-- The generators `Γ_μ`. -/
  Γ : Fin 5 → Matrix d d ℂ
  /-- Hermitian. -/
  herm : ∀ μ, (Γ μ)ᴴ = Γ μ
  /-- Involutions. -/
  sq : ∀ μ, Γ μ * Γ μ = 1
  /-- Pairwise anticommuting. -/
  anticomm : ∀ μ ν, μ ≠ ν → Γ μ * Γ ν = -(Γ ν * Γ μ)

namespace CliffordFamily

variable (G : CliffordFamily d)

theorem exists_ne (μ : Fin 5) : ∃ ν : Fin 5, ν ≠ μ := by
  by_cases h : μ = 0
  · exact ⟨1, by rw [h]; decide⟩
  · exact ⟨0, Ne.symm h⟩

/-- Anticommuting involutions are traceless. -/
theorem trace_eq_zero (μ : Fin 5) : (G.Γ μ).trace = 0 := by
  obtain ⟨ν, hν⟩ := exists_ne μ
  have h1 : G.Γ μ = -(G.Γ ν * G.Γ μ * G.Γ ν) := by
    calc G.Γ μ = G.Γ ν * G.Γ ν * G.Γ μ := by rw [G.sq, Matrix.one_mul]
      _ = G.Γ ν * (G.Γ ν * G.Γ μ) := by rw [Matrix.mul_assoc]
      _ = G.Γ ν * (-(G.Γ μ * G.Γ ν)) := by rw [G.anticomm ν μ hν]
      _ = -(G.Γ ν * G.Γ μ * G.Γ ν) := by rw [Matrix.mul_neg, Matrix.mul_assoc]
  have h2 : (G.Γ ν * G.Γ μ * G.Γ ν).trace = (G.Γ μ).trace := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, G.sq, Matrix.one_mul]
  have h3 : (G.Γ μ).trace = -(G.Γ μ).trace := by
    conv_lhs => rw [h1]
    rw [Matrix.trace_neg, h2]
  linear_combination h3 / 2

/-- `Tr(Γ_μ Γ_ν) = d δ_{μν}`. -/
theorem trace_mul (μ ν : Fin 5) :
    (G.Γ μ * G.Γ ν).trace = if μ = ν then (Fintype.card d : ℂ) else 0 := by
  split_ifs with h
  · subst h; rw [G.sq, Matrix.trace_one]
  · have h1 : (G.Γ μ * G.Γ ν).trace = -(G.Γ μ * G.Γ ν).trace := by
      conv_lhs => rw [G.anticomm μ ν h]
      rw [Matrix.trace_neg, Matrix.trace_mul_comm]
    linear_combination h1 / 2

/-- `(∑_μ a_μ Γ_μ)² = (∑_μ a_μ²) I`. -/
theorem sum_smul_mul_self (a : Fin 5 → ℂ) :
    (∑ μ, a μ • G.Γ μ) * (∑ ν, a ν • G.Γ ν) = (∑ μ, a μ ^ 2) • (1 : Matrix d d ℂ) := by
  set f : Fin 5 → Fin 5 → Matrix d d ℂ := fun μ ν => (a μ * a ν) • (G.Γ μ * G.Γ ν) with hf
  have hexp : (∑ μ, a μ • G.Γ μ) * (∑ ν, a ν • G.Γ ν) = ∑ μ, ∑ ν, f μ ν := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [hf, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have hswap : ∀ μ ν, f ν μ = (if μ = ν then (2 : ℂ) • f μ μ else 0) - f μ ν := by
    intro μ ν
    by_cases h : μ = ν
    · subst h; rw [if_pos rfl, two_smul, add_sub_cancel_right]
    · rw [if_neg h, zero_sub, hf]
      simp only
      rw [G.anticomm ν μ (Ne.symm h), smul_neg, mul_comm (a ν)]
  have hS : (∑ μ, ∑ ν, f μ ν) = (2 : ℂ) • (∑ μ, f μ μ) - ∑ μ, ∑ ν, f μ ν := by
    conv_lhs => rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => hswap y x]
    simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [Finset.smul_sum]
  have hdiag : (∑ μ, f μ μ) = (∑ μ, a μ ^ 2) • (1 : Matrix d d ℂ) := by
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun μ _ => ?_
    show (a μ * a μ) • (G.Γ μ * G.Γ μ) = a μ ^ 2 • (1 : Matrix d d ℂ)
    rw [G.sq, pow_two]
  have h2 : (2 : ℂ) • (∑ μ, ∑ ν, f μ ν) = (2 : ℂ) • (∑ μ, f μ μ) := by
    rw [two_smul]
    nth_rewrite 1 [hS]
    abel
  rw [hexp, ← hdiag]
  exact smul_right_injective _ (two_ne_zero) h2

end CliffordFamily

/-- The Clifford edge operators `H_e = √(6/5) ∑_μ O_{eμ} Γ_μ` on the `d`-space. -/
noncomputable def cliffordH (F : HelmertFrame) (G : CliffordFamily d) (e : Fin 6) :
    Matrix d d ℂ :=
  ((Real.sqrt (6 / 5) : ℝ) : ℂ) • ∑ μ, ((F.O e μ : ℝ) : ℂ) • G.Γ μ

theorem sqrt_six_fifths_sq : ((Real.sqrt (6 / 5) : ℝ) : ℂ) * ((Real.sqrt (6 / 5) : ℝ) : ℂ) = 6 / 5 := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  push_cast
  ring

theorem cliffordH_conjTranspose (F : HelmertFrame) (G : CliffordFamily d) (e : Fin 6) :
    (cliffordH F G e)ᴴ = cliffordH F G e := by
  unfold cliffordH
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sum]
  simp only [Matrix.conjTranspose_smul, G.herm, Complex.star_def, Complex.conj_ofReal]

/-- `H_e² = I`: the rows of `√(6/5) O` are unit vectors. -/
theorem cliffordH_mul_self (F : HelmertFrame) (G : CliffordFamily d) (e : Fin 6) :
    cliffordH F G e * cliffordH F G e = 1 := by
  unfold cliffordH
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, G.sum_smul_mul_self, smul_smul,
    sqrt_six_fifths_sq]
  have h : (∑ μ, ((F.O e μ : ℝ) : ℂ) ^ 2) = 5 / 6 := by
    have := F.proj_apply e e
    rw [if_pos rfl] at this
    have h2 : (∑ μ, ((F.O e μ : ℝ) : ℂ) ^ 2) = ((∑ μ, F.O e μ * F.O e μ : ℝ) : ℂ) := by
      push_cast
      refine Finset.sum_congr rfl fun μ _ => ?_
      ring
    rw [h2, this]
    push_cast
    ring
  rw [h]
  norm_num

theorem cliffordH_trace (F : HelmertFrame) (G : CliffordFamily d) (e : Fin 6) :
    (cliffordH F G e).trace = 0 := by
  unfold cliffordH
  rw [Matrix.trace_smul, Matrix.trace_sum]
  simp [Matrix.trace_smul, G.trace_eq_zero]

/-- `∑_e H_e = 0` (`Oᵀ𝟏 = 0`). -/
theorem cliffordH_sum (F : HelmertFrame) (G : CliffordFamily d) : ∑ e, cliffordH F G e = 0 := by
  unfold cliffordH
  rw [← Finset.smul_sum, sum_colSum_smul F G.Γ, smul_zero]

/-- `Tr(H_e H_f) = (6/5) d ((δ_{ef}) − 1/6)`: `d` for `e = f`, `−d/5` otherwise. -/
theorem cliffordH_gram (F : HelmertFrame) (G : CliffordFamily d) (e f : Fin 6) :
    (cliffordH F G e * cliffordH F G f).trace =
      if e = f then (Fintype.card d : ℂ) else -(Fintype.card d : ℂ) / 5 := by
  unfold cliffordH
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, sqrt_six_fifths_sq, Matrix.trace_smul,
    Finset.sum_mul, Matrix.trace_sum]
  have hinner : ∀ μ, ((((F.O e μ : ℝ) : ℂ) • G.Γ μ) * ∑ ν, ((F.O f ν : ℝ) : ℂ) • G.Γ ν).trace =
      ((F.O e μ : ℝ) : ℂ) * ((F.O f μ : ℝ) : ℂ) * (Fintype.card d : ℂ) := by
    intro μ
    rw [Finset.mul_sum, Matrix.trace_sum]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.trace_smul, G.trace_mul,
      smul_eq_mul, mul_ite, mul_zero]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_univ, if_true]
    ring
  simp_rw [hinner]
  rw [← Finset.sum_mul, smul_eq_mul]
  have h : (∑ μ, ((F.O e μ : ℝ) : ℂ) * ((F.O f μ : ℝ) : ℂ)) =
      (((if e = f then (1 : ℝ) else 0) - 1 / 6 : ℝ) : ℂ) := by
    rw [← F.proj_apply e f]
    push_cast
    rfl
  rw [h]
  split_ifs <;> push_cast <;> ring

end Abstract

/-! ### Tensoring with `I₅` -/

section Tensor

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The Clifford edge operators on `ℂ^d ⊗ ℂ⁵`: `H^q_e = H_e ⊗ I₅`. -/
noncomputable def cliffordHq (F : HelmertFrame) (G : CliffordFamily d) (e : Fin 6) :
    Matrix (d × Fin 5) (d × Fin 5) ℂ :=
  cliffordH F G e ⊗ₖ (1 : Matrix (Fin 5) (Fin 5) ℂ)

theorem cliffordHq_conjTranspose (F : HelmertFrame) (G : CliffordFamily d) (e : Fin 6) :
    (cliffordHq F G e)ᴴ = cliffordHq F G e := by
  rw [cliffordHq, Matrix.conjTranspose_kronecker, cliffordH_conjTranspose,
    Matrix.conjTranspose_one]

theorem cliffordHq_mul_self (F : HelmertFrame) (G : CliffordFamily d) (e : Fin 6) :
    cliffordHq F G e * cliffordHq F G e = 1 := by
  rw [cliffordHq, ← Matrix.mul_kronecker_mul, cliffordH_mul_self, Matrix.one_mul,
    Matrix.one_kronecker_one]

theorem cliffordHq_trace (F : HelmertFrame) (G : CliffordFamily d) (e : Fin 6) :
    (cliffordHq F G e).trace = 0 := by
  rw [cliffordHq, Matrix.trace_kronecker, cliffordH_trace, zero_mul]

theorem cliffordHq_sum (F : HelmertFrame) (G : CliffordFamily d) :
    ∑ e, cliffordHq F G e = 0 := by
  have h : ∑ e, cliffordHq F G e = (∑ e, cliffordH F G e) ⊗ₖ (1 : Matrix (Fin 5) (Fin 5) ℂ) := by
    ext ⟨i, a⟩ ⟨j, b⟩
    simp [cliffordHq, Matrix.sum_apply, Matrix.kroneckerMap_apply, Finset.sum_mul]
  rw [h, cliffordH_sum, Matrix.zero_kronecker]

/-- `Tr(H^q_e H^q_f) = 5d` for `e = f` and `−d` otherwise. -/
theorem cliffordHq_gram (F : HelmertFrame) (G : CliffordFamily d) (e f : Fin 6) :
    (cliffordHq F G e * cliffordHq F G f).trace =
      if e = f then 5 * (Fintype.card d : ℂ) else -(Fintype.card d : ℂ) := by
  rw [cliffordHq, cliffordHq, ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.trace_kronecker,
    Matrix.trace_one, Fintype.card_fin, cliffordH_gram]
  split_ifs <;> push_cast <;> ring

/-- With `d = 4` the Clifford Gram matrix is `20` / `−4`, the same as for the commuting family. -/
theorem cliffordHq_gram_four (F : HelmertFrame) (G : CliffordFamily d)
    (hd : Fintype.card d = 4) (e f : Fin 6) :
    (cliffordHq F G e * cliffordHq F G f).trace = if e = f then 20 else -4 := by
  rw [cliffordHq_gram, hd]
  split_ifs <;> norm_num

/-- **The Clifford record data**: on the `20`-dimensional carrier `ℂ⁴ ⊗ ℂ⁵`, the completions
`K^q_e = I/√18 + (i/3) H^q_e` satisfy `eq:six-edge-normalization` and
`eq:matching-record-data`. -/
theorem clifford_record_data (F : HelmertFrame) (G : CliffordFamily d)
    (hd : Fintype.card d = 4) :
    (∑ e, (completion (cliffordHq F G e))ᴴ * completion (cliffordHq F G e) = 1) ∧
    (∑ e, completion (cliffordHq F G e) =
      ((Real.sqrt 2 : ℝ) : ℂ) • (1 : Matrix (d × Fin 5) (d × Fin 5) ℂ)) ∧
    (∀ e, (completion (cliffordHq F G e))ᴴ * completion (cliffordHq F G e) =
      (1 / 6 : ℂ) • (1 : Matrix (d × Fin 5) (d × Fin 5) ℂ)) ∧
    (∀ e f, ((completion (cliffordHq F G e))ᴴ * completion (cliffordHq F G f)).trace =
      if e = f then 10 / 3 else 2 / 3) := by
  have hcard : Fintype.card (d × Fin 5) = 20 := by
    rw [Fintype.card_prod, hd, Fintype.card_fin]
  exact ⟨sum_conjTranspose_mul_completion _ (cliffordHq_conjTranspose F G)
      (cliffordHq_mul_self F G),
    sum_completion _ (cliffordHq_sum F G),
    fun e => completion_conjTranspose_mul_self _ (cliffordHq_conjTranspose F G e)
      (cliffordHq_mul_self F G e),
    trace_conjTranspose_mul_completion_gram hcard _ (cliffordHq_conjTranspose F G)
      (cliffordHq_trace F G) (cliffordHq_gram_four F G hd)⟩

end Tensor

end RecordWitness
end RenewalGeometry
