/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.StandardModel.RecordWitnessCommutingFamily
import RenewalGeometry.StandardModel.RecordWitnessCliffordFamily
import RenewalGeometry.StandardModel.CliffordMarginalMatterNoGo

/-!
# Record-complete nonidentifiability witness: concrete instances and the algebra contrast

Fourth layer of `prop:record-witness` / `thm:record-nonidentifiability` of the spacetime–gauge
duality paper.

* `helmert`: a concrete Helmert frame `O` (`eq:helmert-frame`): `O_{eμ} = w_μ(e)/√(k(k+1))`,
  `k = μ + 1`, with the integer Helmert vectors `w_μ = (1, …, 1, −k, 0, …, 0)`;
* `cliffordSMST4`: a concrete Clifford family on `ℂ⁴ = ℂ^{Fin 2 × Fin 2}`: the four axes
  `gamma μ` of `NCG.CliffordConcrete` and the chirality `smstChirality`;
* the algebra contrast behind `eq:inequivalent-system-algebras`: the unital algebra generated
  by the Clifford family `H^q_e` contains the `Γ_μ ⊗ I₅` (`gammaTensor_mem_adjoin`), hence is
  **not** commutative (`adjoin_cliffordHq_not_commutative`), and its commutant contains
  `I ⊗ M₅(ℂ)`, hence is not commutative either (`centralizer_cliffordHq_not_commutative`);
  for the commuting family the commutant consists of diagonal matrices
  (`mem_centralizer_Hc_iff`) and is commutative (`centralizer_Hc_commutative`), and the
  generated algebra is commutative (`adjoin_Hc_commutative`, previous file).

The assembly of the two instruments on one `20`-dimensional carrier is in
`RecordWitnessInstrument.lean`.
-/

open Matrix Kronecker

namespace RenewalGeometry
namespace RecordWitness

open FiveKraus NCG.CommonOrigin

/-! ### A concrete Helmert frame -/

/-- The integer Helmert vectors `w_μ = (1, …, 1, −(μ+1), 0, …, 0)` (`μ + 1` ones). -/
def helmertZ (μ : Fin 5) (e : Fin 6) : ℤ :=
  ![![1, -1, 0, 0, 0, 0], ![1, 1, -2, 0, 0, 0], ![1, 1, 1, -3, 0, 0], ![1, 1, 1, 1, -4, 0],
    ![1, 1, 1, 1, 1, -5]] μ e

/-- `‖w_μ‖² = (μ+1)(μ+2)`. -/
def helmertNorm (μ : Fin 5) : ℝ := ((μ.val : ℝ) + 1) * ((μ.val : ℝ) + 2)

theorem helmertNorm_pos (μ : Fin 5) : 0 < helmertNorm μ := by
  unfold helmertNorm; positivity

theorem helmertZ_dot : ∀ μ ν : Fin 5,
    ∑ e, helmertZ μ e * helmertZ ν e =
      if μ = ν then ((μ.val : ℤ) + 1) * ((μ.val : ℤ) + 2) else 0 := by decide

theorem helmertZ_sum : ∀ μ : Fin 5, ∑ e, helmertZ μ e = 0 := by decide

/-- The concrete Helmert matrix `O_{eμ} = w_μ(e) / √((μ+1)(μ+2))`. -/
noncomputable def helmertO : Matrix (Fin 6) (Fin 5) ℝ :=
  Matrix.of fun e μ => (helmertZ μ e : ℝ) / Real.sqrt (helmertNorm μ)

theorem helmertO_mul (e f : Fin 6) (μ : Fin 5) :
    helmertO e μ * helmertO f μ = (helmertZ μ e * helmertZ μ f : ℤ) / helmertNorm μ := by
  simp only [helmertO, Matrix.of_apply]
  rw [div_mul_div_comm, Real.mul_self_sqrt (helmertNorm_pos μ).le]
  push_cast
  ring

theorem helmertO_orth : helmertOᵀ * helmertO = 1 := by
  ext μ ν
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, helmertO,
    Matrix.of_apply]
  have h : ∀ e : Fin 6, (helmertZ μ e : ℝ) / Real.sqrt (helmertNorm μ) *
      ((helmertZ ν e : ℝ) / Real.sqrt (helmertNorm ν)) =
      (helmertZ μ e * helmertZ ν e : ℤ) / (Real.sqrt (helmertNorm μ) * Real.sqrt (helmertNorm ν)) := by
    intro e
    push_cast
    rw [div_mul_div_comm]
  simp_rw [h]
  rw [← Finset.sum_div, ← Int.cast_sum, helmertZ_dot]
  split_ifs with hμν
  · subst hμν
    rw [Real.mul_self_sqrt (helmertNorm_pos μ).le]
    have := (helmertNorm_pos μ).ne'
    unfold helmertNorm at this ⊢
    push_cast
    field_simp
  · simp

theorem helmertO_colSum (μ : Fin 5) : ∑ e, helmertO e μ = 0 := by
  simp only [helmertO, Matrix.of_apply]
  rw [← Finset.sum_div, ← Int.cast_sum, helmertZ_sum]
  simp

theorem helmertO_proj :
    helmertO * helmertOᵀ = 1 - (1 / 6 : ℝ) • Matrix.of (fun _ _ => (1 : ℝ)) := by
  ext e f
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.sub_apply, Matrix.one_apply,
    Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, mul_one]
  simp_rw [helmertO_mul]
  fin_cases e <;> fin_cases f <;>
    simp [Fin.sum_univ_five, helmertZ, helmertNorm] <;> norm_num

/-- **A concrete Helmert frame** (`eq:helmert-frame`). -/
noncomputable def helmert : HelmertFrame :=
  ⟨helmertO, helmertO_orth, helmertO_colSum, helmertO_proj⟩

/-! ### A concrete Clifford family on `ℂ⁴` -/

theorem smstChirality_herm : smstChiralityᴴ = smstChirality := by
  rw [smstChirality_eq]
  simp [Matrix.conjTranspose_kronecker, pauli3_herm]

/-- The five generators `Γ₀, …, Γ₃, Γ₅ = Γ₀Γ₁Γ₂Γ₃` on `ℂ⁴`. -/
def cliffordSMST4Gen : Fin 5 → Matrix SMST4 SMST4 ℂ :=
  Fin.snoc gamma smstChirality

theorem cliffordSMST4Gen_castSucc (μ : Fin 4) : cliffordSMST4Gen μ.castSucc = gamma μ :=
  Fin.snoc_castSucc _ _ _

theorem cliffordSMST4Gen_last : cliffordSMST4Gen (Fin.last 4) = smstChirality :=
  Fin.snoc_last _ _

theorem gamma_smstChirality_anticomm (μ : Fin 4) :
    gamma μ * smstChirality = -(smstChirality * gamma μ) := by
  rw [smstChirality_anticomm μ, neg_neg]

/-- **A concrete Clifford family** on `ℂ⁴ = ℂ^{Fin 2 × Fin 2}`. -/
def cliffordSMST4 : CliffordFamily SMST4 where
  Γ := cliffordSMST4Gen
  herm := by
    intro μ
    refine Fin.lastCases ?_ (fun μ => ?_) μ
    · rw [cliffordSMST4Gen_last, smstChirality_herm]
    · rw [cliffordSMST4Gen_castSucc, gamma_herm]
  sq := by
    intro μ
    refine Fin.lastCases ?_ (fun μ => ?_) μ
    · rw [cliffordSMST4Gen_last, smstChirality_sq]
    · rw [cliffordSMST4Gen_castSucc, gamma_sq]
  anticomm := by
    intro μ ν
    refine Fin.lastCases ?_ (fun μ => ?_) μ <;> refine Fin.lastCases ?_ (fun ν => ?_) ν <;>
      intro h
    · exact absurd rfl h
    · rw [cliffordSMST4Gen_last, cliffordSMST4Gen_castSucc]
      exact smstChirality_anticomm ν
    · rw [cliffordSMST4Gen_last, cliffordSMST4Gen_castSucc]
      exact gamma_smstChirality_anticomm μ
    · rw [cliffordSMST4Gen_castSucc, cliffordSMST4Gen_castSucc]
      exact gamma_anticomm μ ν (fun h' => h (by rw [h']))

theorem card_SMST4 : Fintype.card SMST4 = 4 := by simp

/-! ### The Clifford system algebra is not commutative -/

section CliffordContrast

variable {d : Type*} [Fintype d] [DecidableEq d]

theorem cliffordHq_eq_sum (F : HelmertFrame) (G : CliffordFamily d) (e : Fin 6) :
    cliffordHq F G e = ((Real.sqrt (6 / 5) : ℝ) : ℂ) •
      ∑ μ, ((F.O e μ : ℝ) : ℂ) • (G.Γ μ ⊗ₖ (1 : Matrix (Fin 5) (Fin 5) ℂ)) := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp only [cliffordHq, cliffordH, Matrix.smul_apply, Matrix.sum_apply, Matrix.kroneckerMap_apply,
    smul_eq_mul]
  simp_rw [← mul_assoc, ← Finset.sum_mul]
  ring

theorem sqrt_five_sixths_mul_sqrt_six_fifths :
    ((Real.sqrt (5 / 6) : ℝ) : ℂ) * ((Real.sqrt (6 / 5) : ℝ) : ℂ) = 1 := by
  rw [← Complex.ofReal_mul, ← Real.sqrt_mul (by norm_num)]
  norm_num

/-- `Γ_μ ⊗ I₅ = √(5/6) ∑_e O_{eμ} H^q_e`: the Clifford generators lie in the span of the
`H^q_e` (`OᵀO = I`). -/
theorem gammaTensor_eq_sum (F : HelmertFrame) (G : CliffordFamily d) (μ : Fin 5) :
    G.Γ μ ⊗ₖ (1 : Matrix (Fin 5) (Fin 5) ℂ) =
      ((Real.sqrt (5 / 6) : ℝ) : ℂ) • ∑ e, ((F.O e μ : ℝ) : ℂ) • cliffordHq F G e := by
  simp_rw [cliffordHq_eq_sum]
  have h : ∑ e, ((F.O e μ : ℝ) : ℂ) • (((Real.sqrt (6 / 5) : ℝ) : ℂ) •
      ∑ ν, ((F.O e ν : ℝ) : ℂ) • (G.Γ ν ⊗ₖ (1 : Matrix (Fin 5) (Fin 5) ℂ))) =
      ((Real.sqrt (6 / 5) : ℝ) : ℂ) • ∑ e, ∑ ν, ((F.O e μ * F.O e ν : ℝ) : ℂ) •
        (G.Γ ν ⊗ₖ (1 : Matrix (Fin 5) (Fin 5) ℂ)) := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [smul_comm, Finset.smul_sum]
    refine congrArg _ (Finset.sum_congr rfl fun ν _ => ?_)
    rw [smul_smul]
    push_cast
    rfl
  rw [h, sum_orth_smul' F μ, smul_smul, sqrt_five_sixths_mul_sqrt_six_fifths, one_smul]

theorem gammaTensor_mem_adjoin (F : HelmertFrame) (G : CliffordFamily d) (μ : Fin 5) :
    G.Γ μ ⊗ₖ (1 : Matrix (Fin 5) (Fin 5) ℂ) ∈ Algebra.adjoin ℂ (Set.range (cliffordHq F G)) := by
  rw [gammaTensor_eq_sum F G μ]
  refine Subalgebra.smul_mem _ (Subalgebra.sum_mem _ fun e _ => Subalgebra.smul_mem _ ?_ _) _
  exact Algebra.subset_adjoin (Set.mem_range_self e)

omit [Fintype d] [DecidableEq d] in
theorem neg_kronecker_one (A : Matrix d d ℂ) :
    (-A) ⊗ₖ (1 : Matrix (Fin 5) (Fin 5) ℂ) = -(A ⊗ₖ (1 : Matrix (Fin 5) (Fin 5) ℂ)) := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp [Matrix.kroneckerMap_apply]

theorem gammaTensor_zero_one_ne [Nonempty d] (G : CliffordFamily d) :
    (G.Γ 0 ⊗ₖ (1 : Matrix (Fin 5) (Fin 5) ℂ)) * (G.Γ 1 ⊗ₖ (1 : Matrix (Fin 5) (Fin 5) ℂ)) ≠
      (G.Γ 1 ⊗ₖ (1 : Matrix (Fin 5) (Fin 5) ℂ)) * (G.Γ 0 ⊗ₖ (1 : Matrix (Fin 5) (Fin 5) ℂ)) := by
  intro h
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul,
    G.anticomm 0 1 (by decide)] at h
  have hzero : (G.Γ 1 * G.Γ 0) ⊗ₖ (1 : Matrix (Fin 5) (Fin 5) ℂ) = 0 := by
    have h2 : (2 : ℂ) • ((G.Γ 1 * G.Γ 0) ⊗ₖ (1 : Matrix (Fin 5) (Fin 5) ℂ)) = 0 := by
      rw [two_smul]
      nth_rewrite 1 [← neg_neg ((G.Γ 1 * G.Γ 0) ⊗ₖ (1 : Matrix (Fin 5) (Fin 5) ℂ))]
      rw [← neg_kronecker_one, h]
      abel
    exact (smul_eq_zero.mp h2).resolve_left two_ne_zero
  have hone : ((G.Γ 1 * G.Γ 0) ⊗ₖ (1 : Matrix (Fin 5) (Fin 5) ℂ)) *
      ((G.Γ 0 * G.Γ 1) ⊗ₖ (1 : Matrix (Fin 5) (Fin 5) ℂ)) = 1 := by
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (G.Γ 0),
      G.sq, Matrix.one_mul, G.sq, Matrix.one_kronecker_one]
  rw [hzero, Matrix.zero_mul] at hone
  have i : d := Classical.arbitrary d
  have := congrFun (congrFun hone (i, 0)) (i, 0)
  simp at this

/-- **`eq:inequivalent-system-algebras`, Clifford half (contrast form)**: the unital algebra
generated by the Clifford family is not commutative. -/
theorem adjoin_cliffordHq_not_commutative [Nonempty d] (F : HelmertFrame) (G : CliffordFamily d) :
    ¬ ∀ x ∈ Algebra.adjoin ℂ (Set.range (cliffordHq F G)),
      ∀ y ∈ Algebra.adjoin ℂ (Set.range (cliffordHq F G)), x * y = y * x := fun h =>
  gammaTensor_zero_one_ne G (h _ (gammaTensor_mem_adjoin F G 0) _ (gammaTensor_mem_adjoin F G 1))

/-- `I ⊗ A` commutes with every `H^q_e`. -/
theorem one_kronecker_mem_centralizer (F : HelmertFrame) (G : CliffordFamily d)
    (A : Matrix (Fin 5) (Fin 5) ℂ) :
    (1 : Matrix d d ℂ) ⊗ₖ A ∈ Subalgebra.centralizer ℂ (Set.range (cliffordHq F G)) := by
  rw [Subalgebra.mem_centralizer_iff]
  rintro _ ⟨e, rfl⟩
  rw [cliffordHq, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul,
    Matrix.mul_one, Matrix.one_mul, Matrix.mul_one]

/-- The matrix unit `E₀₁` on `ℂ⁵`. -/
def unit01 : Matrix (Fin 5) (Fin 5) ℂ := Matrix.of fun k l => if k = 0 ∧ l = 1 then 1 else 0

/-- The matrix unit `E₁₀` on `ℂ⁵`. -/
def unit10 : Matrix (Fin 5) (Fin 5) ℂ := Matrix.of fun k l => if k = 1 ∧ l = 0 then 1 else 0

theorem unit01_mul_unit10_apply : (unit01 * unit10) 0 0 = 1 := by
  simp [unit01, unit10, Matrix.mul_apply]

theorem unit10_mul_unit01_apply : (unit10 * unit01) 0 0 = 0 := by
  simp [unit01, unit10, Matrix.mul_apply]

/-- **The Clifford commutant is not commutative**: it contains `I ⊗ M₅(ℂ)`. -/
theorem centralizer_cliffordHq_not_commutative [Nonempty d] (F : HelmertFrame)
    (G : CliffordFamily d) :
    ¬ ∀ x ∈ Subalgebra.centralizer ℂ (Set.range (cliffordHq F G)),
      ∀ y ∈ Subalgebra.centralizer ℂ (Set.range (cliffordHq F G)), x * y = y * x := by
  intro h
  have h1 := h _ (one_kronecker_mem_centralizer F G unit01) _
    (one_kronecker_mem_centralizer F G unit10)
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul] at h1
  have i : d := Classical.arbitrary d
  have := congrFun (congrFun h1 (i, 0)) (i, 0)
  simp only [Matrix.kroneckerMap_apply, Matrix.one_apply_eq, one_mul,
    unit01_mul_unit10_apply, unit10_mul_unit01_apply] at this
  exact one_ne_zero this

end CliffordContrast

/-! ### The commutant of the commuting family is diagonal -/

set_option maxHeartbeats 4000000 in
theorem sgnZ_separates : ∀ S S' : Three, S ≠ S' → ∃ e, sgnZ e S ≠ sgnZ e S' := by decide

theorem sgn_separates (S S' : Three) (h : S ≠ S') : ∃ e, sgn e S ≠ sgn e S' := by
  obtain ⟨e, he⟩ := sgnZ_separates S S' h
  exact ⟨e, fun h' => he (by unfold sgn at h'; exact_mod_cast h')⟩

/-- The commutant of the commuting family consists of the diagonal matrices. -/
theorem mem_centralizer_Hc_iff (X : Matrix Three Three ℂ) :
    X ∈ Subalgebra.centralizer ℂ (Set.range Hc) ↔ ∃ x : Three → ℂ, X = Matrix.diagonal x := by
  rw [Subalgebra.mem_centralizer_iff]
  constructor
  · intro h
    refine ⟨fun S => X S S, ?_⟩
    ext S S'
    by_cases hS : S = S'
    · subst hS; simp
    · rw [Matrix.diagonal_apply_ne _ hS]
      obtain ⟨e, he⟩ := sgn_separates S S' hS
      have h1 := congrFun (congrFun (h (Hc e) ⟨e, rfl⟩) S) S'
      rw [Hc, Matrix.diagonal_mul, Matrix.mul_diagonal] at h1
      have h2 : (sgn e S - sgn e S') * X S S' = 0 := by linear_combination h1
      exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr he)
  · rintro ⟨x, rfl⟩ _ ⟨e, rfl⟩
    rw [Hc, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext S
    ring

/-- **The commuting commutant is commutative.** -/
theorem centralizer_Hc_commutative (x y : Matrix Three Three ℂ)
    (hx : x ∈ Subalgebra.centralizer ℂ (Set.range Hc))
    (hy : y ∈ Subalgebra.centralizer ℂ (Set.range Hc)) : x * y = y * x := by
  obtain ⟨a, rfl⟩ := (mem_centralizer_Hc_iff x).mp hx
  obtain ⟨b, rfl⟩ := (mem_centralizer_Hc_iff y).mp hy
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext S
  ring

end RecordWitness
end RenewalGeometry
