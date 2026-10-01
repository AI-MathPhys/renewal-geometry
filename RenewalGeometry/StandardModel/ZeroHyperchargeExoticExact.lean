/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.StandardModel.CanonicalChiralProjectorsExact
import RenewalGeometry.StandardModel.FaithfulSMQuotientExact

/-!
# Hypercharge support can miss a gauge-charged exotic (`cth:zero-hypercharge-exotic`)

`cth:zero-hypercharge-exotic` of the spacetime–gauge duality manuscript.  To a passing target
packet (`CanonicalChiralProjectors.Inventory` with `P_gch = P_SM`, target weights `y_f ≠ 0`) on
`𝒦 = ℂ^ι` we adjoin the pair of weak adjoint triplets `(1,3)_0`, one in each physical chirality,
on `ℂ³ ⊗ ℂ²` (index `Fin 3 × Bool`): the new carrier is `ℂ^{ι ⊕ (Fin 3 × Bool)}` with
`X'_j = X_j ⊕ (A_j ⊗ I)`, `Y' = Y ⊕ 0`, `Γ' = Γ ⊕ (I ⊗ diag(+1,−1))` (`extendedCarrier`,
`extendedInventory`).

* `extended_intertwiners`: every target intertwiner of the extended carrier is the embedding
  of a target intertwiner of the packet, so all multiplicities `n_{f,±}` (hence every linear
  anomaly row) and every nonzero-hypercharge projector `P_{f,±}` are unchanged;
* `exotic_chiral_traces_vanish`: every local chiral trace `Tr(Γ_E w)` of a word in the exotic
  generators vanishes (the two chiralities cancel; `Y` vanishes on the pair);
* `exotic_invisible_and_charged`: the pair lies in `Ker Y` but is orthogonal to the
  gauge-trivial sector and inside `P_gch`;
* `zero_hypercharge_exotic`: `Δ_inv^F = Tr(P_gch − P_SM) = 6` and `rank (P_gch − P_SM) = 6`, and
  `rank P_{0Y}^{nt} = 6` for the zero-hypercharge projector with the gauge-trivial part removed
  (`eq:zero-hypercharge-exotic-gap`); `exists_exotic_carrier` exhibits such a carrier;
* `adjointGen`: the weak adjoint generators `(J_a)_{bc} = −i ε_{abc}`, Hermitian
  (`adjointGen_herm`), realizing `ad(σ_a/2)` on the Pauli basis (`adjointGen_ad`) and with no
  common kernel (`adjointGen_noKernel`); `weakAdjointFamily_*` place them on three weak
  generator indices;
* `z6_acts_trivially_on_adjoint`: every element of the common kernel `ℤ₆` of
  `prop:faithful-SM-quotient` acts trivially in the weak adjoint representation (the colour and
  abelian factors act trivially by charge assignment `(1,3)_0`), so the exotic pair is a
  representation of the same quotient.

Renderings disclosed: the exotic weak generators are an abstract Hermitian family `A_j` with no
common kernel (instantiated by the adjoint generators on three weak indices); `P_{0Y}` is any
orthogonal projector whose fixed vectors are exactly `Ker Y'`.
-/

open Matrix
open scoped Kronecker ComplexOrder

namespace RenewalGeometry
namespace ZeroHyperchargeExotic

open CanonicalChiralProjectors

set_option linter.unusedSectionVars false

/-! ### Block embeddings -/

section Blocks

variable (ι E : Type*) [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]

/-- The inclusion of the packet `ℂ^ι → ℂ^{ι ⊕ E}`. -/
def J0 : Matrix (ι ⊕ E) ι ℂ := Matrix.fromRows 1 0
/-- The inclusion of the exotic block `ℂ^E → ℂ^{ι ⊕ E}`. -/
def K0 : Matrix (ι ⊕ E) E ℂ := Matrix.fromRows 0 1

theorem J0_isom : (J0 ι E)ᴴ * J0 ι E = 1 := by
  simp [J0, conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromRows]

theorem K0_isom : (K0 ι E)ᴴ * K0 ι E = 1 := by
  simp [K0, conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromRows]

theorem J0_K0 : (J0 ι E)ᴴ * K0 ι E = 0 := by
  simp [J0, K0, conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromRows]

theorem K0_J0 : (K0 ι E)ᴴ * J0 ι E = 0 := by
  simp [J0, K0, conjTranspose_fromRows_eq_fromCols_conjTranspose, fromCols_mul_fromRows]

theorem J0_K0_complete : J0 ι E * (J0 ι E)ᴴ + K0 ι E * (K0 ι E)ᴴ = 1 := by
  simp only [J0, K0, conjTranspose_fromRows_eq_fromCols_conjTranspose, fromRows_mul_fromCols,
    conjTranspose_one, conjTranspose_zero, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul,
    fromBlocks_add]
  simp

variable {ι E}

/-- The block-diagonal operator `a ⊕ e`. -/
def bd (a : Matrix ι ι ℂ) (e : Matrix E E ℂ) : Matrix (ι ⊕ E) (ι ⊕ E) ℂ :=
  J0 ι E * a * (J0 ι E)ᴴ + K0 ι E * e * (K0 ι E)ᴴ

theorem bd_mul (a b : Matrix ι ι ℂ) (e f : Matrix E E ℂ) :
    bd a e * bd b f = bd (a * b) (e * f) := by
  simp only [bd, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (J0 ι E)ᴴ (J0 ι E), J0_isom, ← Matrix.mul_assoc (J0 ι E)ᴴ (K0 ι E),
    J0_K0, ← Matrix.mul_assoc (K0 ι E)ᴴ (J0 ι E), K0_J0, ← Matrix.mul_assoc (K0 ι E)ᴴ (K0 ι E),
    K0_isom]
  simp only [Matrix.one_mul, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]

theorem bd_conjTranspose (a : Matrix ι ι ℂ) (e : Matrix E E ℂ) :
    (bd a e)ᴴ = bd aᴴ eᴴ := by
  simp only [bd, conjTranspose_add, conjTranspose_mul, conjTranspose_conjTranspose,
    Matrix.mul_assoc]

theorem bd_one : bd (1 : Matrix ι ι ℂ) (1 : Matrix E E ℂ) = 1 := by
  simp only [bd, Matrix.mul_one]; exact J0_K0_complete ι E

theorem bd_mul_J0 (a : Matrix ι ι ℂ) (e : Matrix E E ℂ) : bd a e * J0 ι E = J0 ι E * a := by
  simp only [bd, Matrix.add_mul, Matrix.mul_assoc, J0_isom, K0_J0, Matrix.mul_one,
    Matrix.mul_zero, add_zero]

theorem bd_mul_K0 (a : Matrix ι ι ℂ) (e : Matrix E E ℂ) : bd a e * K0 ι E = K0 ι E * e := by
  simp only [bd, Matrix.add_mul, Matrix.mul_assoc, J0_K0, K0_isom, Matrix.mul_one,
    Matrix.mul_zero, zero_add]

theorem J0H_mul_bd (a : Matrix ι ι ℂ) (e : Matrix E E ℂ) :
    (J0 ι E)ᴴ * bd a e = a * (J0 ι E)ᴴ := by
  simp only [bd, Matrix.mul_add, ← Matrix.mul_assoc, J0_isom, J0_K0, Matrix.one_mul,
    Matrix.zero_mul, add_zero]

theorem K0H_mul_bd (a : Matrix ι ι ℂ) (e : Matrix E E ℂ) :
    (K0 ι E)ᴴ * bd a e = e * (K0 ι E)ᴴ := by
  simp only [bd, Matrix.mul_add, ← Matrix.mul_assoc, K0_J0, K0_isom, Matrix.one_mul,
    Matrix.zero_mul, zero_add]

theorem trace_bd (a : Matrix ι ι ℂ) (e : Matrix E E ℂ) :
    (bd a e).trace = a.trace + e.trace := by
  rw [bd, Matrix.trace_add, Matrix.trace_mul_comm, ← Matrix.mul_assoc, J0_isom, Matrix.one_mul,
    Matrix.trace_mul_comm, ← Matrix.mul_assoc, K0_isom, Matrix.one_mul]

/-- Every vector splits as `J0 u + K0 v`. -/
theorem split_vec (x : ι ⊕ E → ℂ) :
    x = J0 ι E *ᵥ ((J0 ι E)ᴴ *ᵥ x) + K0 ι E *ᵥ ((K0 ι E)ᴴ *ᵥ x) := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, J0_K0_complete,
    Matrix.one_mulVec]

end Blocks

/-! ### Uniqueness of orthogonal projectors -/

/-- Two orthogonal projectors with the same fixed vectors coincide. -/
theorem projector_eq_of_fix {m : Type*} [Fintype m] [DecidableEq m] {P Q : Matrix m m ℂ}
    (hP : P * P = P) (hPH : Pᴴ = P) (hQ : Q * Q = Q) (hQH : Qᴴ = Q)
    (h : ∀ x, P *ᵥ x = x ↔ Q *ᵥ x = x) : P = Q := by
  have hQP : Q * P = P := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    simp only [Matrix.toLin'_apply]
    rw [← Matrix.mulVec_mulVec]
    exact (h (P *ᵥ v)).1 (by rw [Matrix.mulVec_mulVec, hP])
  have hPQ : P * Q = Q := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    simp only [Matrix.toLin'_apply]
    rw [← Matrix.mulVec_mulVec]
    exact (h (Q *ᵥ v)).2 (by rw [Matrix.mulVec_mulVec, hQ])
  have := congrArg Matrix.conjTranspose hQP
  rw [conjTranspose_mul, hPH, hQH, hPQ] at this
  exact this.symm

/-! ### The exotic block -/

/-- The exotic carrier index: a weak triplet in each chirality. -/
abbrev ExoticIdx := Fin 3 × Bool

/-- The chirality grading on the pair: `I ⊗ diag(+1, −1)`. -/
def exoticGrading : Matrix ExoticIdx ExoticIdx ℂ :=
  (1 : Matrix (Fin 3) (Fin 3) ℂ) ⊗ₖ Matrix.diagonal sgn

theorem diagonal_sgn_herm : (Matrix.diagonal sgn)ᴴ = Matrix.diagonal sgn := by
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext b
  exact star_sgn b

theorem diagonal_sgn_sq : Matrix.diagonal sgn * Matrix.diagonal sgn = 1 := by
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext b
  cases b <;> simp [sgn]

theorem exoticGrading_herm : exoticGradingᴴ = exoticGrading := by
  rw [exoticGrading, conjTranspose_kronecker, conjTranspose_one, diagonal_sgn_herm]

theorem exoticGrading_sq : exoticGrading * exoticGrading = 1 := by
  rw [exoticGrading, ← mul_kronecker_mul, Matrix.one_mul, diagonal_sgn_sq, one_kronecker_one]

theorem exoticGrading_comm (M : Matrix (Fin 3) (Fin 3) ℂ) :
    exoticGrading * (M ⊗ₖ (1 : Matrix Bool Bool ℂ)) = (M ⊗ₖ 1) * exoticGrading := by
  rw [exoticGrading, ← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one,
    Matrix.one_mul, Matrix.mul_one]

/-- **The two chiralities cancel every local chiral trace**: `Tr(Γ_E (M ⊗ I)) = 0`. -/
theorem trace_exoticGrading_mul (M : Matrix (Fin 3) (Fin 3) ℂ) :
    (exoticGrading * (M ⊗ₖ (1 : Matrix Bool Bool ℂ))).trace = 0 := by
  rw [exoticGrading, ← mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one, trace_kronecker]
  simp [Matrix.trace, sgn]

/-! ### The extended carrier and inventory -/

variable {ι J : Type*} [Fintype ι] [DecidableEq ι] [Fintype J]

/-- The exotic generators `A_j ⊗ I` on the pair. -/
def exoticGen (A : J → Matrix (Fin 3) (Fin 3) ℂ) (j : J) : Matrix ExoticIdx ExoticIdx ℂ :=
  A j ⊗ₖ (1 : Matrix Bool Bool ℂ)

/-- **Exotic local anomaly terms vanish**: for every word in the exotic generators, the chiral
trace `Tr(Γ_E w)` is zero (and `Y` vanishes on the pair, killing every abelian term). -/
theorem exotic_chiral_traces_vanish (A : J → Matrix (Fin 3) (Fin 3) ℂ) (w : List J) :
    (exoticGrading * (w.map (exoticGen A)).prod).trace = 0 := by
  have : (w.map (exoticGen A)).prod = (w.map A).prod ⊗ₖ (1 : Matrix Bool Bool ℂ) := by
    induction w with
    | nil => simp
    | cons j w ih =>
      rw [List.map_cons, List.prod_cons, ih, exoticGen, ← mul_kronecker_mul, Matrix.mul_one,
        List.map_cons, List.prod_cons]
  rw [this, trace_exoticGrading_mul]

/-- The extended carrier `𝒦 ⊕ (ℂ³ ⊗ ℂ²)` with the exotic pair `(1,3)_0`, chiralities `±`. -/
def extendedCarrier (G : GaugeCarrier ι J) (A : J → Matrix (Fin 3) (Fin 3) ℂ)
    (hA : ∀ j, (A j)ᴴ = A j) : GaugeCarrier (ι ⊕ ExoticIdx) J where
  X j := bd (G.X j) (exoticGen A j)
  Y := bd G.Y 0
  Γ := bd G.Γ exoticGrading
  X_herm j := by
    rw [bd_conjTranspose, G.X_herm, exoticGen, conjTranspose_kronecker, hA, conjTranspose_one]
  Y_herm := by rw [bd_conjTranspose, G.Y_herm, conjTranspose_zero]
  Γ_herm := by rw [bd_conjTranspose, G.Γ_herm, exoticGrading_herm]
  Γ_sq := by rw [bd_mul, G.Γ_sq, exoticGrading_sq, bd_one]
  Γ_comm_X j := by rw [bd_mul, bd_mul, G.Γ_comm_X, exoticGen, exoticGrading_comm]
  Γ_comm_Y := by rw [bd_mul, bd_mul, G.Γ_comm_Y, Matrix.mul_zero, Matrix.zero_mul]

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Target intertwiners of the extended carrier** (`y_f ≠ 0`): `S' ∈ 𝓘'_{f,ε}` iff
`S' = J0 ι ExoticIdx S` with `S ∈ 𝓘_{f,ε}`. -/
theorem extended_intertwiners (G : GaugeCarrier ι J) (A : J → Matrix (Fin 3) (Fin 3) ℂ)
    (hA : ∀ j, (A j)ᴴ = A j) (τ : TargetType J V) (hy : τ.y ≠ 0) (ε : ℂ)
    (S' : Matrix (ι ⊕ ExoticIdx) V ℂ) :
    S' ∈ intertwiners (extendedCarrier G A hA) τ ε ↔
      (J0 ι ExoticIdx)ᴴ * S' ∈ intertwiners G τ ε ∧
        S' = J0 ι ExoticIdx * ((J0 ι ExoticIdx)ᴴ * S') := by
  rw [mem_intertwiners_iff, mem_intertwiners_iff]
  simp only [extendedCarrier]
  constructor
  · rintro ⟨h1, h2, h3⟩
    have hK : (K0 ι ExoticIdx)ᴴ * S' = 0 := by
      have := congrArg (fun Z => (K0 ι ExoticIdx)ᴴ * Z) h2
      simp only [← Matrix.mul_assoc, K0H_mul_bd, Matrix.zero_mul, Matrix.mul_smul] at this
      exact (smul_eq_zero.1 this.symm).resolve_left (by exact_mod_cast hy)
    have hS : S' = J0 ι ExoticIdx * ((J0 ι ExoticIdx)ᴴ * S') := by
      conv_lhs => rw [← Matrix.one_mul S', ← J0_K0_complete ι ExoticIdx]
      rw [Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc (K0 ι ExoticIdx), hK, Matrix.mul_zero, add_zero]
    refine ⟨⟨fun j => ?_, ?_, ?_⟩, hS⟩
    · have := congrArg (fun Z => (J0 ι ExoticIdx)ᴴ * Z) (h1 j)
      simp only [← Matrix.mul_assoc, J0H_mul_bd] at this
      rw [Matrix.mul_assoc] at this
      rw [this]
    · have := congrArg (fun Z => (J0 ι ExoticIdx)ᴴ * Z) h2
      simp only [← Matrix.mul_assoc, J0H_mul_bd, Matrix.mul_smul] at this
      rw [Matrix.mul_assoc] at this
      exact this
    · have := congrArg (fun Z => (J0 ι ExoticIdx)ᴴ * Z) h3
      simp only [← Matrix.mul_assoc, J0H_mul_bd, Matrix.mul_smul] at this
      rw [Matrix.mul_assoc] at this
      exact this
  · rintro ⟨⟨h1, h2, h3⟩, hS⟩
    generalize (J0 ι ExoticIdx)ᴴ * S' = S at h1 h2 h3 hS
    subst hS
    refine ⟨fun j => ?_, ?_, ?_⟩
    · rw [← Matrix.mul_assoc, bd_mul_J0, Matrix.mul_assoc, h1, Matrix.mul_assoc]
    · rw [← Matrix.mul_assoc, bd_mul_J0, Matrix.mul_assoc, h2, Matrix.mul_smul]
    · rw [← Matrix.mul_assoc, bd_mul_J0, Matrix.mul_assoc, h3, Matrix.mul_smul]

/-- The embedded orthonormal basis is an orthonormal basis of the extended intertwiner space. -/
theorem extended_onBasis (G : GaugeCarrier ι J) (A : J → Matrix (Fin 3) (Fin 3) ℂ)
    (hA : ∀ j, (A j)ᴴ = A j) (τ : TargetType J V) (hy : τ.y ≠ 0) (ε : ℂ) {n : ℕ}
    {T : Fin n → Matrix ι V ℂ} (hT : IsONBasis G τ ε T) :
    IsONBasis (extendedCarrier G A hA) τ ε fun a => J0 ι ExoticIdx * T a := by
  have hJJ : ∀ S : Matrix ι V ℂ, (J0 ι ExoticIdx)ᴴ * (J0 ι ExoticIdx * S) = S := fun S => by
    rw [← Matrix.mul_assoc, J0_isom, Matrix.one_mul]
  have hmem : ∀ S, S ∈ intertwiners G τ ε →
      J0 ι ExoticIdx * S ∈ intertwiners (extendedCarrier G A hA) τ ε := by
    intro S hS
    rw [extended_intertwiners G A hA τ hy ε, hJJ]
    exact ⟨hS, rfl⟩
  refine ⟨fun a => hmem _ (hT.mem a), fun a b => ?_, ?_⟩
  · rw [multInner, conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (J0 ι ExoticIdx)ᴴ,
      J0_isom,
      Matrix.one_mul]
    exact hT.orth a b
  · apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨a, rfl⟩
      exact hmem _ (hT.mem a)
    · intro S' hS'
      obtain ⟨hS, hSe⟩ := (extended_intertwiners G A hA τ hy ε S').1 hS'
      rw [← hT.span] at hS
      rw [hSe]
      have hlin : ∀ S ∈ Submodule.span ℂ (Set.range T),
          J0 ι ExoticIdx * S ∈ Submodule.span ℂ (Set.range fun a => J0 ι ExoticIdx * T a) := by
        intro S hS
        induction hS using Submodule.span_induction with
        | mem x hx =>
          obtain ⟨a, rfl⟩ := hx
          exact Submodule.subset_span ⟨a, rfl⟩
        | zero => rw [Matrix.mul_zero]; exact Submodule.zero_mem _
        | add x y _ _ hx hy => rw [Matrix.mul_add]; exact Submodule.add_mem _ hx hy
        | smul c x _ hx => rw [Matrix.mul_smul]; exact Submodule.smul_mem _ c hx
      exact hlin _ hS

variable {𝓕 : Type*} [Fintype 𝓕] [DecidableEq 𝓕] {Vf : 𝓕 → Type*} [∀ f, Fintype (Vf f)]
  [∀ f, DecidableEq (Vf f)]

/-- No common kernel for the exotic generators `A_j ⊗ I`. -/
theorem exoticGen_noKernel (A : J → Matrix (Fin 3) (Fin 3) ℂ)
    (hker : ∀ w : Fin 3 → ℂ, (∀ j, A j *ᵥ w = 0) → w = 0) (v : ExoticIdx → ℂ)
    (hv : ∀ j, exoticGen A j *ᵥ v = 0) : v = 0 := by
  have hb : ∀ b : Bool, (fun k => v (k, b)) = 0 := by
    intro b
    apply hker
    intro j
    ext k
    have := congrFun (hv j) (k, b)
    simp only [exoticGen, Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply,
      Fintype.sum_prod_type, Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, Pi.zero_apply] at this
    simpa [Matrix.mulVec, dotProduct] using this
  ext ⟨k, b⟩
  exact congrFun (hb b) k

/-- The extended inventory: the same targets, embedded orthonormal bases and the embedded
gauge-trivial projector. -/
def extendedInventory {G : GaugeCarrier ι J} (D : Inventory G Vf)
    (A : J → Matrix (Fin 3) (Fin 3) ℂ) (hA : ∀ j, (A j)ᴴ = A j)
    (hker : ∀ w : Fin 3 → ℂ, (∀ j, A j *ᵥ w = 0) → w = 0) (hy : ∀ f, (D.τ f).y ≠ 0) :
    Inventory (extendedCarrier G A hA) Vf where
  τ := D.τ
  εp := D.εp
  n := D.n
  T f b a := J0 ι ExoticIdx * D.T f b a
  onb f b := extended_onBasis G A hA (D.τ f) (hy f) (sgn b) (D.onb f b)
  nonempty := D.nonempty
  ineq := D.ineq
  nontriv := D.nontriv
  P0 := bd D.P0 0
  P0_idem := by rw [bd_mul, D.P0_idem, Matrix.mul_zero]
  P0_herm := by rw [bd_conjTranspose, D.P0_herm, conjTranspose_zero]
  P0_fix x := by
    simp only [extendedCarrier]
    obtain ⟨u, v, rfl⟩ : ∃ u v, x = J0 ι ExoticIdx *ᵥ u + K0 ι ExoticIdx *ᵥ v :=
      ⟨_, _, split_vec x⟩
    have hJu : ∀ (a : Matrix ι ι ℂ) (e : Matrix ExoticIdx ExoticIdx ℂ),
        bd a e *ᵥ (J0 ι ExoticIdx *ᵥ u + K0 ι ExoticIdx *ᵥ v) =
          J0 ι ExoticIdx *ᵥ (a *ᵥ u) + K0 ι ExoticIdx *ᵥ (e *ᵥ v) := by
      intro a e
      rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, bd_mul_J0, bd_mul_K0,
        ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    have hdec : ∀ p p' q q', J0 ι ExoticIdx *ᵥ p + K0 ι ExoticIdx *ᵥ q =
        J0 ι ExoticIdx *ᵥ p' + K0 ι ExoticIdx *ᵥ q' ↔ p = p' ∧ q = q' := by
      intro p p' q q'
      constructor
      · intro h
        have h1 := congrArg (fun z => (J0 ι ExoticIdx)ᴴ *ᵥ z) h
        have h2 := congrArg (fun z => (K0 ι ExoticIdx)ᴴ *ᵥ z) h
        simp only [Matrix.mulVec_add, Matrix.mulVec_mulVec, J0_isom, J0_K0, K0_J0, K0_isom,
          Matrix.one_mulVec, Matrix.zero_mulVec, add_zero, zero_add] at h1 h2
        exact ⟨h1, h2⟩
      · rintro ⟨rfl, rfl⟩
        rfl
    have hzero : ∀ p q, J0 ι ExoticIdx *ᵥ p + K0 ι ExoticIdx *ᵥ q = 0 ↔ p = 0 ∧ q = 0 := by
      intro p q
      have := hdec p 0 q 0
      rwa [Matrix.mulVec_zero, Matrix.mulVec_zero, add_zero] at this
    simp only [hJu, Matrix.zero_mulVec, hdec, hzero, D.P0_fix u]
    constructor
    · rintro ⟨⟨hX, hY⟩, hv⟩
      refine ⟨fun j => ⟨hX j, ?_⟩, hY, trivial⟩
      rw [← hv, Matrix.mulVec_zero]
    · rintro ⟨hXE, hY, -⟩
      exact ⟨⟨fun j => (hXE j).1, hY⟩, (exoticGen_noKernel A hker v fun j => (hXE j).2).symm⟩

section Main

variable {G : GaugeCarrier ι J} (D : Inventory G Vf) (A : J → Matrix (Fin 3) (Fin 3) ℂ)
  (hA : ∀ j, (A j)ᴴ = A j) (hker : ∀ w : Fin 3 → ℂ, (∀ j, A j *ᵥ w = 0) → w = 0)
  (hy : ∀ f, (D.τ f).y ≠ 0)

theorem bd_sum_left {κ : Type*} (s : Finset κ) (a : κ → Matrix ι ι ℂ) :
    bd (E := ExoticIdx) (∑ k ∈ s, a k) 0 = ∑ k ∈ s, bd (a k) 0 := by
  simp only [bd, Matrix.mul_zero, Matrix.zero_mul, add_zero, Matrix.mul_sum, Matrix.sum_mul]

theorem bd_sub (a b : Matrix ι ι ℂ) (e f : Matrix ExoticIdx ExoticIdx ℂ) :
    bd (a - b) (e - f) = bd a e - bd b f := by
  simp only [bd, Matrix.mul_sub, Matrix.sub_mul]
  abel

theorem bd_add (a b : Matrix ι ι ℂ) (e f : Matrix ExoticIdx ExoticIdx ℂ) :
    bd (a + b) (e + f) = bd a e + bd b f := by
  simp only [bd, Matrix.mul_add, Matrix.add_mul]
  abel

/-- **Nonzero-hypercharge projectors are unchanged**: `P'_{f,±} = P_{f,±} ⊕ 0`. -/
theorem extended_P (f : 𝓕) (b : Bool) :
    (extendedInventory D A hA hker hy).P f b = bd (D.P f b) 0 := by
  show projector (fun a => J0 ι ExoticIdx * D.T f b a) = bd (projector (D.T f b)) 0
  simp only [projector, bd, conjTranspose_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero,
    Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]

theorem extended_Psm : (extendedInventory D A hA hker hy).Psm = bd D.Psm 0 := by
  simp only [Inventory.Psm, extended_P]
  rw [bd_sum_left]
  rfl

theorem extended_Pmir : (extendedInventory D A hA hker hy).Pmir = bd D.Pmir 0 := by
  simp only [Inventory.Pmir, extended_P]
  rw [bd_sum_left]
  rfl

theorem extended_Pgch : (extendedInventory D A hA hker hy).Pgch = bd D.Pgch 1 := by
  simp only [Inventory.Pgch, extendedInventory]
  rw [← bd_one, ← bd_sub, sub_zero]

include hker hy in
/-- **Multiplicities are unchanged**: `dim 𝓘'_{f,±} = dim 𝓘_{f,±} = n_{f,±}`, so every linear
anomaly row is unchanged. -/
theorem extended_multiplicities (f : 𝓕) (b : Bool) :
    Module.finrank ℂ (intertwiners (extendedCarrier G A hA) (D.τ f) (sgn b)) =
      Module.finrank ℂ (intertwiners G (D.τ f) (sgn b)) := by
  haveI := D.nonempty f
  have h1 := finrank_intertwiners ((extendedInventory D A hA hker hy).onb f b)
  have h2 := finrank_intertwiners (D.onb f b)
  exact h1.trans h2.symm

/-- **The pair is invisible to `supp Y`** but orthogonal to the gauge-trivial sector and inside
the gauge-charged projector. -/
theorem exotic_invisible_and_charged :
    (extendedCarrier G A hA).Y * K0 ι ExoticIdx = 0 ∧
    (extendedInventory D A hA hker hy).P0 * K0 ι ExoticIdx = 0 ∧
    (extendedInventory D A hA hker hy).Pgch * K0 ι ExoticIdx = K0 ι ExoticIdx := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [extendedCarrier]; rw [bd_mul_K0, Matrix.mul_zero]
  · simp only [extendedInventory]; rw [bd_mul_K0, Matrix.mul_zero]
  · rw [extended_Pgch, bd_mul_K0, Matrix.mul_one]

include hy in
/-- A target projector kills `Ker Y` (`y_f ≠ 0`). -/
theorem P_mulVec_of_Y (f : 𝓕) (b : Bool) (u : ι → ℂ) (hu : G.Y *ᵥ u = 0) :
    D.P f b *ᵥ u = 0 := by
  have hzero : ∀ a, (D.T f b a)ᴴ *ᵥ u = 0 := by
    intro a
    have hT := (mem_intertwiners_iff G (D.τ f) (sgn b) _).1 ((D.onb f b).mem a)
    have h2 : ((D.τ f).y : ℂ) • (D.T f b a)ᴴ = (D.T f b a)ᴴ * G.Y := by
      have := congrArg Matrix.conjTranspose hT.2.1
      rw [conjTranspose_mul, G.Y_herm, conjTranspose_smul, Complex.star_def,
        Complex.conj_ofReal] at this
      exact this.symm
    have : ((D.τ f).y : ℂ) • ((D.T f b a)ᴴ *ᵥ u) = 0 := by
      rw [← Matrix.smul_mulVec, h2, ← Matrix.mulVec_mulVec, hu, Matrix.mulVec_zero]
    exact (smul_eq_zero.1 this).resolve_left (by exact_mod_cast hy f)
  simp only [Inventory.P, projector, Matrix.sum_mulVec, ← Matrix.mulVec_mulVec, hzero,
    Matrix.mulVec_zero, Finset.sum_const_zero]

theorem card_exoticIdx : Fintype.card ExoticIdx = 6 := by
  simp [ExoticIdx]

/-- **`cth:zero-hypercharge-exotic`** (`eq:zero-hypercharge-exotic-gap`).  Adjoin to a passing
target packet (`P_gch = P_SM`, all target weights `y_f ≠ 0`) the pair of weak adjoint triplets
`(1,3)_0` of opposite chirality.  Then every target multiplicity and every nonzero-hypercharge
projector is unchanged, every exotic local chiral trace vanishes, the pair lies in `Ker Y`, and
`Δ_inv^F = Tr(P_gch − P_SM) = 6 = rank(P_gch − P_SM)`; moreover for the zero-hypercharge
projector `P_{0Y}` (any orthogonal projector whose fixed vectors are `Ker Y`),
`rank P_{0Y}^{nt} = rank(P_{0Y} − P_0) = 6`. -/
theorem zero_hypercharge_exotic (hpass : D.Pgch = D.Psm) :
    (∀ f b, Module.finrank ℂ (intertwiners (extendedCarrier G A hA) (D.τ f) (sgn b)) =
      Module.finrank ℂ (intertwiners G (D.τ f) (sgn b))) ∧
    (∀ f b, (extendedInventory D A hA hker hy).P f b = bd (D.P f b) 0) ∧
    (∀ w : List J, (exoticGrading * (w.map (exoticGen A)).prod).trace = 0) ∧
    (extendedCarrier G A hA).Y * K0 ι ExoticIdx = 0 ∧
    ((extendedInventory D A hA hker hy).Pgch - (extendedInventory D A hA hker hy).Psm).trace
      = 6 ∧
    ((extendedInventory D A hA hker hy).Pgch -
      (extendedInventory D A hA hker hy).Psm).rank = 6 ∧
    ∀ Q : Matrix (ι ⊕ ExoticIdx) (ι ⊕ ExoticIdx) ℂ, Q * Q = Q → Qᴴ = Q →
      (∀ x, Q *ᵥ x = x ↔ (extendedCarrier G A hA).Y *ᵥ x = 0) →
      (Q - (extendedInventory D A hA hker hy).P0).rank = 6 := by
  have hres : (extendedInventory D A hA hker hy).Pgch - (extendedInventory D A hA hker hy).Psm =
      bd 0 1 := by
    rw [extended_Pgch, extended_Psm, ← bd_sub, hpass, sub_self, sub_zero]
  have hbd01 : (bd (ι := ι) (E := ExoticIdx) 0 1) * bd 0 1 = bd 0 1 := by
    rw [bd_mul, Matrix.mul_zero, Matrix.mul_one]
  have htr : (bd (ι := ι) (E := ExoticIdx) 0 1).trace = 6 := by
    rw [trace_bd, Matrix.trace_zero, Matrix.trace_one, card_exoticIdx, zero_add]
    norm_num
  have hrank : (bd (ι := ι) (E := ExoticIdx) 0 1).rank = 6 := by
    have := rank_eq_trace_of_idem _ hbd01
    rw [htr] at this
    exact_mod_cast this
  refine ⟨extended_multiplicities D A hA hker hy, extended_P D A hA hker hy,
    exotic_chiral_traces_vanish A, (exotic_invisible_and_charged D A hA hker hy).1,
    by rw [hres, htr], by rw [hres, hrank], ?_⟩
  intro Q hQ hQH hQfix
  have hQeq : Q = bd D.P0 1 := by
    refine projector_eq_of_fix hQ hQH ?_ ?_ ?_
    · rw [bd_mul, D.P0_idem, Matrix.mul_one]
    · rw [bd_conjTranspose, D.P0_herm, conjTranspose_one]
    · intro x
      rw [hQfix]
      obtain ⟨u, v, rfl⟩ : ∃ u v, x = J0 ι ExoticIdx *ᵥ u + K0 ι ExoticIdx *ᵥ v :=
        ⟨_, _, split_vec x⟩
      have hJu : ∀ (a : Matrix ι ι ℂ) (e : Matrix ExoticIdx ExoticIdx ℂ),
          bd a e *ᵥ (J0 ι ExoticIdx *ᵥ u + K0 ι ExoticIdx *ᵥ v) =
            J0 ι ExoticIdx *ᵥ (a *ᵥ u) + K0 ι ExoticIdx *ᵥ (e *ᵥ v) := by
        intro a e
        rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, bd_mul_J0, bd_mul_K0,
          ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      have hdec : ∀ p p' q q', J0 ι ExoticIdx *ᵥ p + K0 ι ExoticIdx *ᵥ q =
          J0 ι ExoticIdx *ᵥ p' + K0 ι ExoticIdx *ᵥ q' ↔ p = p' ∧ q = q' := by
        intro p p' q q'
        constructor
        · intro h
          have h1 := congrArg (fun z => (J0 ι ExoticIdx)ᴴ *ᵥ z) h
          have h2 := congrArg (fun z => (K0 ι ExoticIdx)ᴴ *ᵥ z) h
          simp only [Matrix.mulVec_add, Matrix.mulVec_mulVec, J0_isom, J0_K0, K0_J0, K0_isom,
            Matrix.one_mulVec, Matrix.zero_mulVec, add_zero, zero_add] at h1 h2
          exact ⟨h1, h2⟩
        · rintro ⟨rfl, rfl⟩
          rfl
      simp only [extendedCarrier, hJu, Matrix.zero_mulVec, Matrix.one_mulVec]
      rw [hdec]
      have hz : J0 ι ExoticIdx *ᵥ (G.Y *ᵥ u) + K0 ι ExoticIdx *ᵥ 0 = 0 ↔ G.Y *ᵥ u = 0 := by
        rw [Matrix.mulVec_zero, add_zero]
        constructor
        · intro h
          have := congrArg (fun z => (J0 ι ExoticIdx)ᴴ *ᵥ z) h
          simpa only [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, J0_isom, Matrix.one_mul,
            Matrix.mulVec_zero] using this
        · intro h
          rw [h, Matrix.mulVec_zero]
      rw [hz]
      simp only [and_true]
      constructor
      swap
      · intro h
        exact ((D.P0_fix u).1 h).2
      · intro hYu
        have hsm : D.Psm *ᵥ u = 0 := by
          simp only [Inventory.Psm, Matrix.sum_mulVec, P_mulVec_of_Y D hy _ _ u hYu,
            Finset.sum_const_zero]
        have : D.Pgch *ᵥ u = 0 := by rw [hpass, hsm]
        rw [Inventory.Pgch, Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at this
        exact this.symm
  rw [hQeq]
  show (bd D.P0 1 - bd D.P0 0).rank = 6
  rw [← bd_sub, sub_self, sub_zero, hrank]

end Main

/-! ### The weak adjoint triplet -/

/-- The weak adjoint generators `(J_a)_{bc} = −i ε_{abc}`. -/
def adjointGen : Fin 3 → Matrix (Fin 3) (Fin 3) ℂ :=
  ![!![0, 0, 0; 0, 0, -Complex.I; 0, Complex.I, 0],
    !![0, 0, Complex.I; 0, 0, 0; -Complex.I, 0, 0],
    !![0, -Complex.I, 0; Complex.I, 0, 0; 0, 0, 0]]

/-- The Pauli matrices `σ_1, σ_2, σ_3`. -/
def pauli : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ :=
  ![!![0, 1; 1, 0], !![0, -Complex.I; Complex.I, 0], !![1, 0; 0, -1]]

theorem adjointGen_herm (a : Fin 3) : (adjointGen a)ᴴ = adjointGen a := by
  fin_cases a <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp [adjointGen]

/-- `J_a` is the matrix of `ad(σ_a/2)` in the Pauli basis:
`[σ_a/2, σ_b] = ∑_c (J_a)_{cb} σ_c`. -/
theorem adjointGen_ad (a b : Fin 3) :
    (1 / 2 : ℂ) • (pauli a * pauli b - pauli b * pauli a) =
      ∑ c, adjointGen a c b • pauli c := by
  fin_cases a <;> fin_cases b <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [adjointGen, pauli, Fin.sum_univ_three, Matrix.mul_apply, Fin.sum_univ_two] <;> ring_nf

/-- The adjoint generators have no common kernel (irreducibility of the triplet). -/
theorem adjointGen_noKernel (w : Fin 3 → ℂ) (hw : ∀ a, adjointGen a *ᵥ w = 0) : w = 0 := by
  have h0 := hw 0
  have h1 := hw 1
  have e1 := congrFun h0 1
  have e2 := congrFun h0 2
  have e0 := congrFun h1 2
  simp [adjointGen, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at e1 e2 e0
  ext k
  fin_cases k <;> simp_all

/-- The weak adjoint family on three weak generator indices `wk : Fin 3 ↪ J`. -/
def weakAdjointFamily {J : Type*} [DecidableEq J] (wk : Fin 3 → J) (j : J) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  ∑ a, if wk a = j then adjointGen a else 0

theorem weakAdjointFamily_apply {J : Type*} [DecidableEq J] {wk : Fin 3 → J}
    (hwk : Function.Injective wk) (a : Fin 3) : weakAdjointFamily wk (wk a) = adjointGen a := by
  rw [weakAdjointFamily, Finset.sum_eq_single a (fun c _ hc => by rw [if_neg (hwk.ne hc)])
    (by simp), if_pos rfl]

theorem weakAdjointFamily_herm {J : Type*} [DecidableEq J] (wk : Fin 3 → J) (j : J) :
    (weakAdjointFamily wk j)ᴴ = weakAdjointFamily wk j := by
  simp only [weakAdjointFamily, conjTranspose_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs
  · exact adjointGen_herm a
  · exact conjTranspose_zero

theorem weakAdjointFamily_noKernel {J : Type*} [DecidableEq J] {wk : Fin 3 → J}
    (hwk : Function.Injective wk) (w : Fin 3 → ℂ)
    (hw : ∀ j, weakAdjointFamily wk j *ᵥ w = 0) : w = 0 :=
  adjointGen_noKernel w fun a => by rw [← weakAdjointFamily_apply hwk a]; exact hw (wk a)

/-! ### Descent to the `ℤ₆` quotient -/

/-- **The exotic pair is a representation of the same `ℤ₆` quotient**: every element of the
common kernel `K ≅ ℤ₆` of `prop:faithful-SM-quotient` has scalar weak component, hence acts
trivially in the weak adjoint representation `M ↦ g₂ M g₂^*`; the colour factor and the abelian
factor act trivially on `(1,3)_0` by its charge assignment. -/
theorem z6_acts_trivially_on_adjoint (x : SMGaugeCover)
    (hx : x ∈ FaithfulSMQuotient.commonKernel) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    x.1.2.1 * M * (x.1.2.1)ᴴ = M ∧ ((x.2 : ℂ) ^ (0 : ℤ)) = 1 := by
  refine ⟨?_, by simp⟩
  have hL : FaithfulSMQuotient.repL x = 1 := (FaithfulSMQuotient.mem_commonKernel.1 hx).2.2.2.1
  simp only [FaithfulSMQuotient.repL, FaithfulSMQuotient.charged_apply,
    FaithfulSMQuotient.weak_apply] at hL
  have hz : ((x.2 : ℂ) ^ (-3 : ℤ)) ≠ 0 := zpow_ne_zero _ (Circle.coe_ne_zero _)
  set c : ℂ := ((x.2 : ℂ) ^ (-3 : ℤ))⁻¹
  have hg : x.1.2.1 = c • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [← hL, smul_smul, inv_mul_cancel₀ hz, one_smul]
  have hu : x.1.2.1 * (x.1.2.1)ᴴ = 1 := by
    have := x.1.2.2
    rw [Matrix.mem_specialUnitaryGroup_iff, Matrix.mem_unitaryGroup_iff] at this
    exact this.1
  rw [hg] at hu ⊢
  rw [conjTranspose_smul, conjTranspose_one, smul_mul_smul, Matrix.one_mul] at hu
  rw [conjTranspose_smul, conjTranspose_one, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul,
    Matrix.mul_one, smul_smul]
  have hcc : c * star c = 1 := by
    have := congrFun (congrFun hu 0) 0
    simpa using this
  rw [mul_comm, hcc, one_smul]

/-! ### Existence -/

/-- The trivial passing packet on the zero carrier with no targets (witness of non-vacuity). -/
def trivialCarrier : GaugeCarrier Empty (Fin 3) where
  X _ := 0
  Y := 0
  Γ := 1
  X_herm _ := conjTranspose_zero
  Y_herm := conjTranspose_zero
  Γ_herm := conjTranspose_one
  Γ_sq := Matrix.mul_one 1
  Γ_comm_X _ := by simp
  Γ_comm_Y := by simp

/-- **There are finite fermion carriers** with a passing packet whose exotic extension has
`Δ_inv^F = 6`: the extension of the trivial packet by the weak adjoint pair. -/
theorem exists_exotic_carrier :
    ∃ (D : Inventory trivialCarrier (fun _ : Empty => Unit)) (hy : ∀ f, (D.τ f).y ≠ 0),
      D.Pgch = D.Psm ∧
      ((extendedInventory D adjointGen adjointGen_herm adjointGen_noKernel hy).Pgch -
        (extendedInventory D adjointGen adjointGen_herm adjointGen_noKernel hy).Psm).trace = 6 := by
  let D : Inventory trivialCarrier (fun _ : Empty => Unit) :=
    { τ := fun f => f.elim
      εp := fun f => f.elim
      n := fun f => f.elim
      T := fun f => f.elim
      onb := fun f => f.elim
      nonempty := fun f => f.elim
      ineq := fun f => f.elim
      nontriv := fun f => f.elim
      P0 := 0
      P0_idem := Matrix.mul_zero 0
      P0_herm := conjTranspose_zero
      P0_fix := fun x => ⟨fun _ => ⟨fun _ => funext fun i => i.elim, funext fun i => i.elim⟩,
        fun _ => funext fun i => i.elim⟩ }
  have hy : ∀ f, (D.τ f).y ≠ 0 := fun f => f.elim
  have hpass : D.Pgch = D.Psm := Subsingleton.elim _ _
  exact ⟨D, hy, hpass, (zero_hypercharge_exotic D adjointGen adjointGen_herm adjointGen_noKernel
    hy hpass).2.2.2.2.1⟩

end ZeroHyperchargeExotic
end RenewalGeometry
