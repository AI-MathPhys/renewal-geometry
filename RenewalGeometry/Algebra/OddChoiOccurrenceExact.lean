/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Algebra.ChoiCriterion
import RenewalGeometry.Operational.ActiveOddLiftInvarianceExact

/-!
# Kraus-independent odd-Choi occurrence (`thm:odd-choi-occurrence`)

Spacetime–gauge duality manuscript, `app:odd-occurrence`.

Let `J` be a grading (`Jᴴ = J`, `J * J = 1`) with sign projections `P± = (1 ± J)/2`.
On Hilbert–Schmidt operator space, `Θ_J X = J X J` and `P_odd = (1 − Θ_J)/2`.
For a linear map `Φ` with Choi matrix `J_Φ` (`choi`, which is `choiMatrix` for `Fin d`
carriers) the odd Choi mass is `μ_J(Φ) = Tr(P_odd J_Φ)` (`oddChoiMass`).

* `oddProj_mulVec` — `oddProj J` is the matrix of `X ↦ (X − JXJ)/2` in the vectorization
  `vecOp` in which the Choi matrix of a Kraus family is `∑ |K_α⟩⟩⟨⟨K_α|`
  (`choi_krausLin`); `oddProj_mul_self`, `oddProj_conjTranspose`: it is an orthogonal
  projector;
* `oddChoiMass_eq_half_trace` — `μ_J(Φ) = (Tr Φ(1) − Tr[J Φ(J)])/2` for every linear `Φ`;
* `oddChoiMass_eq_activeCrossSignMass` — `μ_J(Φ) = Tr[P₋Φ(P₊)] + Tr[P₊Φ(P₋)]`;
* `oddChoiMass_eq_sum_hsSq_odd`, `oddChoiMass_eq_sum_hsSq_corners` — for every Kraus
  family, `μ_J(Φ) = ∑ ‖(K_α)_odd‖²_HS = ∑ (‖P₋K_αP₊‖² + ‖P₊K_αP₋‖²)`
  (`eq:odd-choi-identities`), hence Kraus independence (`sum_hsSq_odd_kraus_independent`);
* `oddChoiMass_eq_zero_iff` — `μ_J(Φ) = 0 ⟺ P_odd J_Φ = 0` (range of the Choi matrix in
  the grading-even operators) `⟺` every Kraus direction commutes with `J`
  (`eq:odd-choi-zero`);
* `oddChoiMass_two_sign` — `μ_J(Φ) = d₊ Tr[P₋Φ(ρ₊)] + d₋ Tr[P₊Φ(ρ₋)]`
  (`eq:odd-choi-two-sign`).

Packaged as `odd_choi_occurrence`.

Rendering disclosed: the protected grading is encoded by `J` with `Jᴴ = J`, `J * J = 1`
and `P± = (1 ± J)/2` (equivalent to `J = P₊ − P₋` with complementary orthogonal
projections); the carrier is a finite index type; a CP map is given through a finite
Kraus family (every CP map of matrix algebras has one, `choi_criterion`).  The trace
formula and the cross-sign identity hold for arbitrary linear `Φ`.
-/

open Matrix
open scoped Kronecker ComplexOrder

namespace RenewalGeometry
namespace OddChoiOccurrence

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The Choi matrix `C_Φ (i,k) (j,l) = Φ(E_ij) k l` on a general finite carrier
(`thm:odd-choi-occurrence`); for `Fin d` it is `choiMatrix` (`choi_eq_choiMatrix`). -/
noncomputable def choi (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) : Matrix (n × n) (n × n) ℂ :=
  Matrix.of fun p q => Φ (single p.1 q.1 1) p.2 q.2

theorem choi_eq_choiMatrix {d : ℕ}
    (Φ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ) :
    choi Φ = choiMatrix Φ := rfl

/-- Vectorization compatible with the Choi convention: `|X⟩⟩ (i,k) = X k i`. -/
def vecOp (X : Matrix n n ℂ) : n × n → ℂ := fun p => X p.2 p.1

/-- The Hilbert–Schmidt superoperator `Θ_J X = J X J` as a matrix on `n × n`. -/
def gradingConj (J : Matrix n n ℂ) : Matrix (n × n) (n × n) ℂ :=
  Matrix.of fun p q => J p.2 q.2 * J q.1 p.1

/-- The HS projection onto grading-odd operators, `P_odd = (1 − Θ_J)/2`. -/
noncomputable def oddProj (J : Matrix n n ℂ) : Matrix (n × n) (n × n) ℂ :=
  (2 : ℂ)⁻¹ • (1 - gradingConj J)

/-- The grading-odd part `K_odd = (K − J K J)/2`. -/
noncomputable def gradeOdd (J K : Matrix n n ℂ) : Matrix n n ℂ :=
  (2 : ℂ)⁻¹ • (K - J * K * J)

/-- The odd Choi mass `μ_J(Φ) = Tr(P_odd J_Φ)` (`eq:odd-choi-mass`). -/
noncomputable def oddChoiMass (J : Matrix n n ℂ) (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) : ℂ :=
  (oddProj J * choi Φ).trace

/-- Squared Hilbert–Schmidt norm. -/
noncomputable def hsSq {m k : Type*} [Fintype m] [Fintype k] (A : Matrix m k ℂ) : ℝ :=
  ∑ i, ∑ j, ‖A i j‖ ^ 2

/-- The CP map of a finite Kraus family, `X ↦ ∑ K_α X K_αᴴ`, as a linear map. -/
noncomputable def krausLin {ι : Type*} [Fintype ι] (K : ι → Matrix n n ℂ) :
    Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ where
  toFun X := ∑ a, K a * X * (K a)ᴴ
  map_add' X Y := by
    simp only [Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib]
  map_smul' c X := by
    simp only [Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum, RingHom.id_apply]

theorem krausLin_apply {ι : Type*} [Fintype ι] (K : ι → Matrix n n ℂ) (X : Matrix n n ℂ) :
    krausLin K X = ∑ a, K a * X * (K a)ᴴ := rfl

/-! ## The HS superoperators -/

theorem gradingConj_mulVec (J X : Matrix n n ℂ) :
    gradingConj J *ᵥ vecOp X = vecOp (J * X * J) := by
  ext ⟨i, k⟩
  simp only [mulVec, dotProduct, gradingConj, vecOp, Matrix.of_apply, Fintype.sum_prod_type,
    Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem oddProj_mulVec (J X : Matrix n n ℂ) :
    oddProj J *ᵥ vecOp X = vecOp (gradeOdd J X) := by
  rw [oddProj, Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, gradingConj_mulVec]
  ext p
  simp [vecOp, gradeOdd, Matrix.sub_apply, Matrix.smul_apply]

theorem gradingConj_mul_self {J : Matrix n n ℂ} (hJ : J * J = 1) :
    gradingConj J * gradingConj J = 1 := by
  ext ⟨i, k⟩ ⟨j, l⟩
  have h1 : ∀ a b, ∑ c, J a c * J c b = (1 : Matrix n n ℂ) a b := by
    intro a b; rw [← hJ, Matrix.mul_apply]
  simp only [Matrix.mul_apply, gradingConj, Matrix.of_apply, Fintype.sum_prod_type]
  calc ∑ x, ∑ y, J k y * J x i * (J y l * J j x)
      = (∑ y, J k y * J y l) * (∑ x, J j x * J x i) := by
        rw [Finset.sum_mul_sum, Finset.sum_comm]
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
        ring
    _ = (1 : Matrix (n × n) (n × n) ℂ) (i, k) (j, l) := by
        rw [h1, h1, Matrix.one_apply, Matrix.one_apply, Matrix.one_apply]
        by_cases h : i = j <;> by_cases h' : k = l <;> simp [h, h', eq_comm]

theorem oddProj_mul_self {J : Matrix n n ℂ} (hJ : J * J = 1) :
    oddProj J * oddProj J = oddProj J := by
  have h2 : (1 - gradingConj J) * (1 - gradingConj J) = (2 : ℂ) • (1 - gradingConj J) := by
    rw [sub_mul, mul_sub, mul_sub, one_mul, mul_one, one_mul, gradingConj_mul_self hJ]
    module
  rw [oddProj, smul_mul_smul_comm, h2, smul_smul]
  congr 1
  norm_num

theorem gradingConj_conjTranspose {J : Matrix n n ℂ} (hJh : Jᴴ = J) :
    (gradingConj J)ᴴ = gradingConj J := by
  have hs : ∀ a b, star (J a b) = J b a := by
    intro a b
    have := congrFun (congrFun hJh b) a
    simpa [Matrix.conjTranspose_apply] using this
  ext p q
  simp only [Matrix.conjTranspose_apply, gradingConj, Matrix.of_apply, star_mul', hs]

theorem oddProj_conjTranspose {J : Matrix n n ℂ} (hJh : Jᴴ = J) :
    (oddProj J)ᴴ = oddProj J := by
  rw [oddProj, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
    gradingConj_conjTranspose hJh]
  congr 1
  simp

/-! ## Trace formula -/

theorem trace_choi (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) :
    (choi Φ).trace = (Φ 1).trace := by
  rw [ActiveOddLift.linearMap_apply_eq_sum Φ 1]
  simp only [Matrix.trace, Matrix.diag, choi, Matrix.of_apply, Fintype.sum_prod_type,
    Matrix.sum_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, ite_mul, one_mul,
    zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [Finset.sum_comm]

omit [DecidableEq n] in
theorem sum3_reverse (f : n → n → n → ℂ) :
    ∑ i, ∑ j, ∑ l, f i j l = ∑ l, ∑ j, ∑ i, f i j l :=
  calc ∑ i, ∑ j, ∑ l, f i j l = ∑ i, ∑ l, ∑ j, f i j l :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ l, ∑ i, ∑ j, f i j l := Finset.sum_comm
    _ = ∑ l, ∑ j, ∑ i, f i j l := Finset.sum_congr rfl fun _ _ => Finset.sum_comm

theorem trace_gradingConj_mul_choi (J : Matrix n n ℂ) (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) :
    (gradingConj J * choi Φ).trace = (J * Φ J).trace := by
  conv_rhs => rw [ActiveOddLift.linearMap_apply_eq_sum Φ J]
  simp only [Matrix.trace, Matrix.diag, choi, gradingConj, Matrix.of_apply,
    Fintype.sum_prod_type, Matrix.mul_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [sum3_reverse (fun i j l => J k l * J j i * Φ (single j i 1) l k)]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun i _ => ?_
  ring

/-- `μ_J(Φ) = (Tr Φ(1) − Tr[J Φ(J)])/2` for every linear map `Φ`. -/
theorem oddChoiMass_eq_half_trace (J : Matrix n n ℂ) (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) :
    oddChoiMass J Φ = (2 : ℂ)⁻¹ * ((Φ 1).trace - (J * Φ J).trace) := by
  rw [oddChoiMass, oddProj, Matrix.smul_mul, Matrix.trace_smul, Matrix.sub_mul,
    Matrix.one_mul, Matrix.trace_sub, trace_choi, trace_gradingConj_mul_choi, smul_eq_mul]

/-- **Cross-sign line of `eq:odd-choi-identities`**: `μ_J(Φ) = Tr[P₋Φ(P₊)] + Tr[P₊Φ(P₋)]`
(the active cross-sign mass of `thm:active-odd-lift-invariance`), for every linear `Φ`. -/
theorem oddChoiMass_eq_activeCrossSignMass (J : Matrix n n ℂ)
    (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) :
    oddChoiMass J Φ = ActiveOddLift.activeCrossSignMass J Φ := by
  rw [oddChoiMass_eq_half_trace, ActiveOddLift.activeCrossSignMass, ActiveOddLift.gradingPlus,
    ActiveOddLift.gradingMinus]
  simp only [map_smul, map_add, map_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul,
    Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.one_mul,
    Matrix.trace_add, Matrix.trace_sub, smul_eq_mul]
  ring

/-! ## Hilbert–Schmidt norms -/

omit [DecidableEq n] in
theorem trace_mul_conjTranspose_eq_hsSq {m : Type*} [Fintype m] (A : Matrix m n ℂ) :
    (A * Aᴴ).trace = (hsSq A : ℂ) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply, hsSq,
    Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]

omit [DecidableEq n] in
theorem hsSq_nonneg {m : Type*} [Fintype m] (A : Matrix m n ℂ) : 0 ≤ hsSq A :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

omit [DecidableEq n] in
theorem hsSq_eq_zero_iff {m : Type*} [Fintype m] (A : Matrix m n ℂ) : hsSq A = 0 ↔ A = 0 := by
  rw [← Complex.ofReal_inj, Complex.ofReal_zero, ← trace_mul_conjTranspose_eq_hsSq,
    Matrix.trace_mul_conjTranspose_self_eq_zero_iff]

/-! ## Sign projections -/

section Grading

variable {J : Matrix n n ℂ}

local notation "Pp" => ActiveOddLift.gradingPlus J
local notation "Pm" => ActiveOddLift.gradingMinus J

theorem gradingPlus_mul_self (hJ : J * J = 1) : Pp * Pp = Pp := by
  simp only [ActiveOddLift.gradingPlus, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, hJ]
  ext i j
  simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  ring

theorem gradingMinus_mul_self (hJ : J * J = 1) : Pm * Pm = Pm := by
  simp only [ActiveOddLift.gradingMinus, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hJ]
  ext i j
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply, smul_eq_mul]
  ring

theorem gradingPlus_mul_gradingMinus (hJ : J * J = 1) : Pp * Pm = 0 := by
  simp only [ActiveOddLift.gradingPlus, ActiveOddLift.gradingMinus, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.add_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, hJ]
  module

theorem gradingMinus_mul_gradingPlus (hJ : J * J = 1) : Pm * Pp = 0 := by
  simp only [ActiveOddLift.gradingPlus, ActiveOddLift.gradingMinus, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, hJ]
  module

theorem gradingPlus_conjTranspose (hJh : Jᴴ = J) : Ppᴴ = Pp := by
  simp [ActiveOddLift.gradingPlus, Matrix.conjTranspose_smul, hJh]

theorem gradingMinus_conjTranspose (hJh : Jᴴ = J) : Pmᴴ = Pm := by
  simp [ActiveOddLift.gradingMinus, Matrix.conjTranspose_smul, hJh]

/-- `K_odd = P₋ K P₊ + P₊ K P₋`. -/
theorem gradeOdd_eq_corners (K : Matrix n n ℂ) : gradeOdd J K = Pm * K * Pp + Pp * K * Pm := by
  simp only [gradeOdd, ActiveOddLift.gradingPlus, ActiveOddLift.gradingMinus, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.one_mul, Matrix.mul_one, ← smul_add]
  ext i j
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply, smul_eq_mul]
  ring

/-- One cross corner: `Tr[P K Q Kᴴ] = ‖P K Q‖²_HS` for orthogonal projections `P, Q`. -/
theorem trace_corner {P Q : Matrix n n ℂ} (hP : P * P = P) (hPh : Pᴴ = P) (hQ : Q * Q = Q)
    (hQh : Qᴴ = Q) (K : Matrix n n ℂ) :
    (P * (K * Q * Kᴴ)).trace = (hsSq (P * K * Q) : ℂ) := by
  rw [← trace_mul_conjTranspose_eq_hsSq]
  calc (P * (K * Q * Kᴴ)).trace = ((P * P) * (K * (Q * Q) * Kᴴ)).trace := by rw [hP, hQ]
    _ = (P * (P * K * Q * Q * Kᴴ)).trace := by simp only [Matrix.mul_assoc]
    _ = ((P * K * Q * Q * Kᴴ) * P).trace := Matrix.trace_mul_comm _ _
    _ = _ := by
        rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hPh, hQh]
        simp only [Matrix.mul_assoc]

/-- The two odd corners are Hilbert–Schmidt orthogonal: `‖K_odd‖² = ‖P₋KP₊‖² + ‖P₊KP₋‖²`. -/
theorem hsSq_gradeOdd (hJh : Jᴴ = J) (hJ : J * J = 1) (K : Matrix n n ℂ) :
    hsSq (gradeOdd J K) = hsSq (Pm * K * Pp) + hsSq (Pp * K * Pm) := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_add, ← trace_mul_conjTranspose_eq_hsSq, ← trace_mul_conjTranspose_eq_hsSq,
    ← trace_mul_conjTranspose_eq_hsSq, gradeOdd_eq_corners]
  have h1 : Pm * K * Pp * (Pp * K * Pm)ᴴ = 0 := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, gradingPlus_conjTranspose hJh,
      gradingMinus_conjTranspose hJh]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Pp Pm, gradingPlus_mul_gradingMinus hJ]
    simp
  have h2 : Pp * K * Pm * (Pm * K * Pp)ᴴ = 0 := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, gradingPlus_conjTranspose hJh,
      gradingMinus_conjTranspose hJh]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Pm Pp, gradingMinus_mul_gradingPlus hJ]
    simp
  rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, h1, h2,
    add_zero, zero_add, Matrix.trace_add]

/-- `K_odd = 0 ⟺ K` commutes with the grading. -/
theorem gradeOdd_eq_zero_iff (hJ : J * J = 1) (K : Matrix n n ℂ) :
    gradeOdd J K = 0 ↔ K * J = J * K := by
  rw [gradeOdd, smul_eq_zero, sub_eq_zero]
  simp only [inv_eq_zero, two_ne_zero, false_or]
  constructor
  · intro h
    calc K * J = J * K * J * J := by rw [← h]
      _ = J * K := by rw [Matrix.mul_assoc, hJ, Matrix.mul_one]
  · intro h
    rw [Matrix.mul_assoc, h, ← Matrix.mul_assoc, hJ, Matrix.one_mul]

end Grading

/-! ## Kraus families -/

section Kraus

variable {ι : Type*} [Fintype ι]

/-- Vectorization of a Kraus family: `J_Φ = ∑_α |K_α⟩⟩⟨⟨K_α|`. -/
theorem choi_krausLin (K : ι → Matrix n n ℂ) :
    choi (krausLin K) = ∑ a, vecMulVec (vecOp (K a)) (star (vecOp (K a))) := by
  ext ⟨i, k⟩ ⟨j, l⟩
  simp only [choi, krausLin_apply, Matrix.of_apply, Matrix.sum_apply, vecMulVec_apply, vecOp,
    Pi.star_apply, Matrix.mul_apply, Matrix.single_apply, Matrix.conjTranspose_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem choi_congr {Φ Ψ : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ} (h : ∀ X, Φ X = Ψ X) :
    choi Φ = choi Ψ := by
  rw [LinearMap.ext h]

/-- **First line of `eq:odd-choi-identities`**: for every Kraus family of `Φ`,
`μ_J(Φ) = ∑_α ‖(K_α)_odd‖²_HS`. -/
theorem oddChoiMass_eq_sum_hsSq_corners {J : Matrix n n ℂ} (hJh : Jᴴ = J) (hJ : J * J = 1)
    (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) (K : ι → Matrix n n ℂ)
    (hΦ : ∀ X, Φ X = ∑ a, K a * X * (K a)ᴴ) :
    oddChoiMass J Φ = ((∑ a, (hsSq (ActiveOddLift.gradingMinus J * K a *
        ActiveOddLift.gradingPlus J) + hsSq (ActiveOddLift.gradingPlus J * K a *
        ActiveOddLift.gradingMinus J)) : ℝ) : ℂ) := by
  rw [oddChoiMass_eq_activeCrossSignMass, ActiveOddLift.activeCrossSignMass, hΦ, hΦ,
    Matrix.mul_sum, Matrix.mul_sum, Matrix.trace_sum, Matrix.trace_sum, ← Finset.sum_add_distrib,
    Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.ofReal_add,
    trace_corner (gradingMinus_mul_self hJ) (gradingMinus_conjTranspose hJh)
      (gradingPlus_mul_self hJ) (gradingPlus_conjTranspose hJh),
    trace_corner (gradingPlus_mul_self hJ) (gradingPlus_conjTranspose hJh)
      (gradingMinus_mul_self hJ) (gradingMinus_conjTranspose hJh)]

/-- **`eq:odd-choi-identities`, Kraus line**: `μ_J(Φ) = ∑_α ‖(K_α)_odd‖²_HS`. -/
theorem oddChoiMass_eq_sum_hsSq_odd {J : Matrix n n ℂ} (hJh : Jᴴ = J) (hJ : J * J = 1)
    (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) (K : ι → Matrix n n ℂ)
    (hΦ : ∀ X, Φ X = ∑ a, K a * X * (K a)ᴴ) :
    oddChoiMass J Φ = ((∑ a, hsSq (gradeOdd J (K a)) : ℝ) : ℂ) := by
  rw [oddChoiMass_eq_sum_hsSq_corners hJh hJ Φ K hΦ]
  congr 1
  exact Finset.sum_congr rfl fun a _ => (hsSq_gradeOdd hJh hJ (K a)).symm

/-- **Kraus independence**: two Kraus families of the same map have the same total odd
Hilbert–Schmidt mass. -/
theorem sum_hsSq_odd_kraus_independent {J : Matrix n n ℂ} (hJh : Jᴴ = J) (hJ : J * J = 1)
    {κ : Type*} [Fintype κ] (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) (K : ι → Matrix n n ℂ)
    (K' : κ → Matrix n n ℂ) (hK : ∀ X, Φ X = ∑ a, K a * X * (K a)ᴴ)
    (hK' : ∀ X, Φ X = ∑ b, K' b * X * (K' b)ᴴ) :
    ∑ a, hsSq (gradeOdd J (K a)) = ∑ b, hsSq (gradeOdd J (K' b)) := by
  apply Complex.ofReal_injective
  rw [← oddChoiMass_eq_sum_hsSq_odd hJh hJ Φ K hK, ← oddChoiMass_eq_sum_hsSq_odd hJh hJ Φ K' hK']

theorem oddChoiMass_nonneg {J : Matrix n n ℂ} (hJh : Jᴴ = J) (hJ : J * J = 1)
    (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) (K : ι → Matrix n n ℂ)
    (hΦ : ∀ X, Φ X = ∑ a, K a * X * (K a)ᴴ) :
    0 ≤ oddChoiMass J Φ := by
  rw [oddChoiMass_eq_sum_hsSq_odd hJh hJ Φ K hΦ]
  exact Complex.zero_le_real.mpr (Finset.sum_nonneg fun a _ => hsSq_nonneg _)

theorem oddProj_mul_choi_kraus (J : Matrix n n ℂ) (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ)
    (K : ι → Matrix n n ℂ) (hΦ : ∀ X, Φ X = ∑ a, K a * X * (K a)ᴴ) :
    oddProj J * choi Φ = ∑ a, vecMulVec (vecOp (gradeOdd J (K a))) (star (vecOp (K a))) := by
  rw [choi_congr (Ψ := krausLin K) (fun X => by rw [hΦ, krausLin_apply]), choi_krausLin,
    Matrix.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.mul_vecMulVec, oddProj_mulVec]

/-- **`eq:odd-choi-zero`**: for a Kraus family of `Φ`, the odd Choi mass vanishes iff the
range of the Choi matrix lies in the grading-even operators (`P_odd J_Φ = 0`, equivalently
`P_odd (J_Φ v) = 0` for every `v`), iff every Kraus direction commutes with `J`. -/
theorem oddChoiMass_eq_zero_iff {J : Matrix n n ℂ} (hJh : Jᴴ = J) (hJ : J * J = 1)
    (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) (K : ι → Matrix n n ℂ)
    (hΦ : ∀ X, Φ X = ∑ a, K a * X * (K a)ᴴ) :
    (oddChoiMass J Φ = 0 ↔ oddProj J * choi Φ = 0) ∧
    (oddProj J * choi Φ = 0 ↔ ∀ v, oddProj J *ᵥ (choi Φ *ᵥ v) = 0) ∧
    (oddChoiMass J Φ = 0 ↔ ∀ a, K a * J = J * K a) := by
  have hcomm : oddChoiMass J Φ = 0 ↔ ∀ a, K a * J = J * K a := by
    rw [oddChoiMass_eq_sum_hsSq_odd hJh hJ Φ K hΦ, Complex.ofReal_eq_zero,
      Finset.sum_eq_zero_iff_of_nonneg (fun a _ => hsSq_nonneg _)]
    simp only [Finset.mem_univ, true_implies, hsSq_eq_zero_iff, gradeOdd_eq_zero_iff hJ]
  have hrange : oddProj J * choi Φ = 0 ↔ ∀ v, oddProj J *ᵥ (choi Φ *ᵥ v) = 0 := by
    constructor
    · intro h v; rw [Matrix.mulVec_mulVec, h, Matrix.zero_mulVec]
    · intro h
      ext p q
      have := congrFun (h (Pi.single q 1)) p
      rwa [Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at this
  refine ⟨?_, hrange, hcomm⟩
  constructor
  · intro h0
    have hc := hcomm.mp h0
    rw [oddProj_mul_choi_kraus J Φ K hΦ]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [(gradeOdd_eq_zero_iff hJ (K a)).mpr (hc a)]
    ext p q
    rw [vecMulVec_apply]
    simp [vecOp]
  · intro h
    rw [oddChoiMass, h, Matrix.trace_zero]

end Kraus

/-- **`eq:odd-choi-two-sign`**: with `d± = Tr P± ≠ 0` and `ρ± = P±/d±`,
`μ_J(Φ) = d₊ Tr[P₋Φ(ρ₊)] + d₋ Tr[P₊Φ(ρ₋)]`, for every linear `Φ`. -/
theorem oddChoiMass_two_sign (J : Matrix n n ℂ) (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ)
    (hdp : (ActiveOddLift.gradingPlus J).trace ≠ 0)
    (hdm : (ActiveOddLift.gradingMinus J).trace ≠ 0) :
    oddChoiMass J Φ =
      (ActiveOddLift.gradingPlus J).trace * (ActiveOddLift.gradingMinus J *
          Φ (((ActiveOddLift.gradingPlus J).trace)⁻¹ • ActiveOddLift.gradingPlus J)).trace
      + (ActiveOddLift.gradingMinus J).trace * (ActiveOddLift.gradingPlus J *
          Φ (((ActiveOddLift.gradingMinus J).trace)⁻¹ • ActiveOddLift.gradingMinus J)).trace := by
  rw [oddChoiMass_eq_activeCrossSignMass, ActiveOddLift.activeCrossSignMass, map_smul, map_smul,
    Matrix.mul_smul, Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul,
    smul_eq_mul, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hdp, mul_inv_cancel₀ hdm, one_mul,
    one_mul]

/-- **`thm:odd-choi-occurrence`** (packaged).  For a grading `J` (`Jᴴ = J`, `J² = 1`,
`P± = (1 ± J)/2`) and a map `Φ` with a finite Kraus family `K`:
(i) `μ_J(Φ) = ∑‖(K_α)_odd‖²` (so the latter is Kraus independent),
(ii) `μ_J(Φ) = Tr[P₋Φ(P₊)] + Tr[P₊Φ(P₋)]`,
(iii) `μ_J(Φ) = ∑(‖P₋K_αP₊‖² + ‖P₊K_αP₋‖²)`,
(iv) `μ_J(Φ) = 0 ⟺ P_odd J_Φ = 0` (Choi range grading even) `⟺ [K_α, J] = 0 ∀α`,
(v) the two-sign formula when `d± = Tr P± ≠ 0`. -/
theorem odd_choi_occurrence {ι : Type*} [Fintype ι] {J : Matrix n n ℂ} (hJh : Jᴴ = J)
    (hJ : J * J = 1) (Φ : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ) (K : ι → Matrix n n ℂ)
    (hΦ : ∀ X, Φ X = ∑ a, K a * X * (K a)ᴴ) :
    (∀ {κ : Type} [Fintype κ] (K' : κ → Matrix n n ℂ),
        (∀ X, Φ X = ∑ b, K' b * X * (K' b)ᴴ) →
        oddChoiMass J Φ = ((∑ b, hsSq (gradeOdd J (K' b)) : ℝ) : ℂ)) ∧
    oddChoiMass J Φ = ((∑ a, hsSq (gradeOdd J (K a)) : ℝ) : ℂ) ∧
    oddChoiMass J Φ = ActiveOddLift.activeCrossSignMass J Φ ∧
    oddChoiMass J Φ = ((∑ a, (hsSq (ActiveOddLift.gradingMinus J * K a *
        ActiveOddLift.gradingPlus J) + hsSq (ActiveOddLift.gradingPlus J * K a *
        ActiveOddLift.gradingMinus J)) : ℝ) : ℂ) ∧
    (oddChoiMass J Φ = 0 ↔ oddProj J * choi Φ = 0) ∧
    (oddChoiMass J Φ = 0 ↔ ∀ a, K a * J = J * K a) ∧
    ((ActiveOddLift.gradingPlus J).trace ≠ 0 → (ActiveOddLift.gradingMinus J).trace ≠ 0 →
      oddChoiMass J Φ =
        (ActiveOddLift.gradingPlus J).trace * (ActiveOddLift.gradingMinus J *
          Φ (((ActiveOddLift.gradingPlus J).trace)⁻¹ • ActiveOddLift.gradingPlus J)).trace
        + (ActiveOddLift.gradingMinus J).trace * (ActiveOddLift.gradingPlus J *
          Φ (((ActiveOddLift.gradingMinus J).trace)⁻¹ • ActiveOddLift.gradingMinus J)).trace) :=
  ⟨fun K' hK' => oddChoiMass_eq_sum_hsSq_odd hJh hJ Φ K' hK',
    oddChoiMass_eq_sum_hsSq_odd hJh hJ Φ K hΦ,
    oddChoiMass_eq_activeCrossSignMass J Φ,
    oddChoiMass_eq_sum_hsSq_corners hJh hJ Φ K hΦ,
    (oddChoiMass_eq_zero_iff hJh hJ Φ K hΦ).1,
    (oddChoiMass_eq_zero_iff hJh hJ Φ K hΦ).2.2,
    fun hdp hdm => oddChoiMass_two_sign J Φ hdp hdm⟩

end OddChoiOccurrence
end RenewalGeometry
