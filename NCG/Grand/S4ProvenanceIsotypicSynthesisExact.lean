/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.TetrahedralProvenanceIsotypicLocalization
import NCG.Grand.CharacterHankelSectorSaturation
import NCG.Grand.GeneralRandomScanTensorGap
import NCG.Grand.AtlasIsoperimetry
import NCG.Grand.FiniteCPMemoryParameterCompactness

/-!
# Exact S4 provenance isotypic synthesis

Exact completion of `cor:S4-provenance-isotypic` on the complete five-isotype
`S₄` carrier:

* the
  Schur-zero lemmas for the trivial, `[22]`, `[211]`, and sign isotypes
  prove that every equivariant tetrahedral provenance synthesis lands in the
  standard block in the unique form `p ⊗ I_[31]`; the provenance projector is
  derived from the synthesis as `(YY*)/‖p‖²`, so isotype-killing is a theorem
  rather than a construction.
-/

open Matrix
open scoped Kronecker

namespace NCG

/-! ### `cor:S4-provenance-isotypic`:
Symmetry localization of a tetrahedral provenance source -/

/-- The trivial `S₄` isotype on the adjacent-transposition generators. -/
def trivialS4Gen : StandardS4Generator → Matrix (Fin 1) (Fin 1) ℂ :=
  fun _ => 1

/-- The sign `S₄` isotype: every adjacent transposition acts by `-1`. -/
def signS4Gen : StandardS4Generator → Matrix (Fin 1) (Fin 1) ℂ :=
  fun _ => -1

/-- The two-dimensional `[22]` isotype.  It factors through
`S₄/V₄ ≅ S₃`; the transpositions `(01)` and `(23)` are congruent modulo the
Klein subgroup and share the image `s`, while `(12)` maps to `t`, in the
standard two-dimensional reflection realization of `S₃`. -/
def s22S4Gen : StandardS4Generator → Matrix (Fin 2) (Fin 2) ℂ
  | .swap01 => !![0, 1; 1, 0]
  | .swap12 => !![1, 0; -1, -1]
  | .swap23 => !![0, 1; 1, 0]

/-- The three-dimensional `[211]` isotype: standard tensor sign. -/
def s211S4Gen : StandardS4Generator → Matrix (Fin 3) (Fin 3) ℂ :=
  fun q => -standardS4Carrier q

/-- Schur zero map: no nonzero intertwiner from the standard carrier into the
trivial isotype. -/
theorem trivialS4_intertwiner_zero (Z : Matrix (Fin 1) (Fin 3) ℂ)
    (hZ : ∀ q, trivialS4Gen q * Z = Z * standardS4Carrier q) : Z = 0 := by
  have h01 := congrFun (congrFun (hZ .swap01) (0 : Fin 1)) (0 : Fin 3)
  have h12 := congrFun (congrFun (hZ .swap12) (0 : Fin 1)) (1 : Fin 3)
  have h23 := congrFun (congrFun (hZ .swap23) (0 : Fin 1)) (2 : Fin 3)
  simp [trivialS4Gen, standardS4Carrier, Matrix.mul_apply,
    Fin.sum_univ_succ] at h01 h12 h23
  have h2 : Z 0 2 = 0 := by linear_combination h23 / 2
  have h1 : Z 0 1 = 0 := by linear_combination h12 + h2
  have h0 : Z 0 0 = 0 := by linear_combination h01 + h1
  ext i j
  fin_cases i <;> fin_cases j <;>
    first
      | exact h0
      | exact h1
      | exact h2

/-- Schur zero map: no nonzero intertwiner from the standard carrier into the
sign isotype. -/
theorem signS4_intertwiner_zero (Z : Matrix (Fin 1) (Fin 3) ℂ)
    (hZ : ∀ q, signS4Gen q * Z = Z * standardS4Carrier q) : Z = 0 := by
  have h01 := congrFun (congrFun (hZ .swap01) (0 : Fin 1)) (0 : Fin 3)
  have h12 := congrFun (congrFun (hZ .swap12) (0 : Fin 1)) (1 : Fin 3)
  have h23 := congrFun (congrFun (hZ .swap23) (0 : Fin 1)) (2 : Fin 3)
  simp [signS4Gen, standardS4Carrier, Matrix.mul_apply,
    Fin.sum_univ_succ] at h01 h12 h23
  have h2 : Z 0 2 = 0 := by linear_combination h23 / 2
  have h1 : Z 0 1 = 0 := by linear_combination -h12 - h2
  have h0 : Z 0 0 = 0 := by linear_combination -h01 - h1
  ext i j
  fin_cases i <;> fin_cases j <;>
    first
      | exact h0
      | exact h1
      | exact h2

/-- Schur zero map: no nonzero intertwiner from the standard carrier into the
`[22]` isotype. -/
theorem s22S4_intertwiner_zero (Z : Matrix (Fin 2) (Fin 3) ℂ)
    (hZ : ∀ q, s22S4Gen q * Z = Z * standardS4Carrier q) : Z = 0 := by
  have e1 := congrFun (congrFun (hZ .swap01) (0 : Fin 2)) (0 : Fin 3)
  have e2 := congrFun (congrFun (hZ .swap01) (0 : Fin 2)) (1 : Fin 3)
  have e3 := congrFun (congrFun (hZ .swap01) (0 : Fin 2)) (2 : Fin 3)
  have e4 := congrFun (congrFun (hZ .swap23) (0 : Fin 2)) (0 : Fin 3)
  have e5 := congrFun (congrFun (hZ .swap23) (0 : Fin 2)) (2 : Fin 3)
  have e6 := congrFun (congrFun (hZ .swap12) (1 : Fin 2)) (0 : Fin 3)
  simp [s22S4Gen, standardS4Carrier, Matrix.mul_apply,
    Fin.sum_univ_succ] at e1 e2 e3 e4 e5 e6
  -- e1 : Z 1 0 = Z 0 1 ; e2 : Z 1 1 = Z 0 0 ; e3 : Z 1 2 = Z 0 2
  -- e4 : Z 1 0 = Z 0 0 - Z 0 2 ; e5 : Z 1 2 = -Z 0 2
  -- e6 : -Z 0 0 - Z 1 0 = Z 1 0
  have h02 : Z 0 2 = 0 := by linear_combination (e3 - e5) / 2
  have h12 : Z 1 2 = 0 := by linear_combination e3 + h02
  have h10 : Z 1 0 = Z 0 0 := by linear_combination e4 - h02
  have h00 : Z 0 0 = 0 := by
    linear_combination (-1 / 3 : ℂ) * e6 - (2 / 3 : ℂ) * h10
  have h01 : Z 0 1 = 0 := by linear_combination -e1 + h10 + h00
  have h11 : Z 1 1 = 0 := by linear_combination e2 + h00
  have h10' : Z 1 0 = 0 := by linear_combination h10 + h00
  ext i j
  fin_cases i <;> fin_cases j <;>
    first
      | exact h00
      | exact h01
      | exact h02
      | exact h10'
      | exact h11
      | exact h12

/-- Schur zero map: no nonzero intertwiner from the standard carrier into the
`[211]` isotype. -/
theorem s211S4_intertwiner_zero (Z : Matrix (Fin 3) (Fin 3) ℂ)
    (hZ : ∀ q, s211S4Gen q * Z = Z * standardS4Carrier q) : Z = 0 := by
  have a1 := congrFun (congrFun (hZ .swap01) (0 : Fin 3)) (0 : Fin 3)
  have a2 := congrFun (congrFun (hZ .swap01) (0 : Fin 3)) (1 : Fin 3)
  have a3 := congrFun (congrFun (hZ .swap01) (0 : Fin 3)) (2 : Fin 3)
  have a5 := congrFun (congrFun (hZ .swap01) (2 : Fin 3)) (2 : Fin 3)
  have b1 := congrFun (congrFun (hZ .swap12) (0 : Fin 3)) (0 : Fin 3)
  have b2 := congrFun (congrFun (hZ .swap12) (0 : Fin 3)) (1 : Fin 3)
  have b3 := congrFun (congrFun (hZ .swap12) (1 : Fin 3)) (0 : Fin 3)
  have b4 := congrFun (congrFun (hZ .swap12) (1 : Fin 3)) (1 : Fin 3)
  have c1 := congrFun (congrFun (hZ .swap23) (0 : Fin 3)) (0 : Fin 3)
  simp [s211S4Gen, standardS4Carrier, Matrix.mul_apply,
    Fin.sum_univ_succ] at a1 a2 a3 a5 b1 b2 b3 b4 c1
  -- a1 : -Z 1 0 = Z 0 1 ; a2 : -Z 1 1 = Z 0 0 ; a3 : -Z 1 2 = Z 0 2
  -- a5 : -Z 2 2 = Z 2 2 ; b1 : -Z 0 0 = Z 0 0 ; b2 : -Z 0 1 = Z 0 2
  -- b3 : -Z 2 0 = Z 1 0 ; b4 : -Z 2 1 = Z 1 2
  -- c1 : -Z 0 0 = Z 0 0 - Z 0 2
  have h00 : Z 0 0 = 0 := by linear_combination -b1 / 2
  have h11 : Z 1 1 = 0 := by linear_combination -a2 - h00
  have h22 : Z 2 2 = 0 := by linear_combination -a5 / 2
  have h02 : Z 0 2 = 0 := by linear_combination -c1 - 2 * h00
  have h01 : Z 0 1 = 0 := by linear_combination -b2 - h02
  have h10 : Z 1 0 = 0 := by linear_combination -a1 - h01
  have h12 : Z 1 2 = 0 := by linear_combination -a3 - h02
  have h21 : Z 2 1 = 0 := by linear_combination -b4 - h12
  have h20 : Z 2 0 = 0 := by linear_combination -b3 - h10
  ext i j
  fin_cases i <;> fin_cases j <;>
    first
      | exact h00
      | exact h01
      | exact h02
      | exact h10
      | exact h11
      | exact h12
      | exact h20
      | exact h21
      | exact h22

/-- The complete connected `S₄`-covariant carrier: multiplicity spaces tensor
each of the five irreducible isotypes, with the standard block `m₃₁ ⊗ [31]`
split off as the second summand. -/
abbrev S4IsotypicCarrier (mt m22 m211 ms m31 : Type*) : Type _ :=
  ((mt × Fin 1) ⊕ ((m22 × Fin 2) ⊕ ((m211 × Fin 3) ⊕ (ms × Fin 1)))) ⊕
    (m31 × Fin 3)

variable {mt m22 m211 ms m31 : Type*}
  [Fintype mt] [Fintype m22] [Fintype m211] [Fintype ms] [Fintype m31]
  [DecidableEq mt] [DecidableEq m22] [DecidableEq m211] [DecidableEq ms]
  [DecidableEq m31]

/-- The block-diagonal isotypic `S₄` action on the complete carrier: every
isotype acts on its own block, amplified by the identity on its multiplicity
space. -/
def s4IsotypicAction (q : StandardS4Generator) :
    Matrix (S4IsotypicCarrier mt m22 m211 ms m31)
      (S4IsotypicCarrier mt m22 m211 ms m31) ℂ :=
  Matrix.fromBlocks
    (Matrix.fromBlocks ((1 : Matrix mt mt ℂ) ⊗ₖ trivialS4Gen q) 0 0
      (Matrix.fromBlocks ((1 : Matrix m22 m22 ℂ) ⊗ₖ s22S4Gen q) 0 0
        (Matrix.fromBlocks ((1 : Matrix m211 m211 ℂ) ⊗ₖ s211S4Gen q) 0 0
          ((1 : Matrix ms ms ℂ) ⊗ₖ signS4Gen q))))
    0 0 ((1 : Matrix m31 m31 ℂ) ⊗ₖ standardS4Carrier q)

/-- Row entry of a multiplicity-amplified block times a tall matrix. -/
theorem kron_one_mul_row_apply {m d F : Type*} [Fintype m] [Fintype d]
    [DecidableEq m] (ρ : Matrix d d ℂ) (W : Matrix (m × d) F ℂ)
    (a : m) (i : d) (j : F) :
    (((1 : Matrix m m ℂ) ⊗ₖ ρ) * W) (a, i) j =
      ∑ i', ρ i i' * W (a, i') j := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp [Matrix.kroneckerMap_apply, Matrix.one_apply, ite_mul,
    Finset.sum_ite_eq]

/-- Left-block row entries of a block-diagonal matrix times a tall matrix. -/
theorem fromBlocks_diag_mul_apply_inl {α β F : Type*} [Fintype α] [Fintype β]
    (A : Matrix α α ℂ) (D : Matrix β β ℂ) (Y : Matrix (α ⊕ β) F ℂ)
    (a : α) (j : F) :
    (Matrix.fromBlocks A 0 0 D * Y) (Sum.inl a) j =
      ∑ a', A a a' * Y (Sum.inl a') j := by
  rw [Matrix.mul_apply, Fintype.sum_sum_type]
  simp

/-- Right-block row entries of a block-diagonal matrix times a tall matrix. -/
theorem fromBlocks_diag_mul_apply_inr {α β F : Type*} [Fintype α] [Fintype β]
    (A : Matrix α α ℂ) (D : Matrix β β ℂ) (Y : Matrix (α ⊕ β) F ℂ)
    (b : β) (j : F) :
    (Matrix.fromBlocks A 0 0 D * Y) (Sum.inr b) j =
      ∑ b', D b b' * Y (Sum.inr b') j := by
  rw [Matrix.mul_apply, Fintype.sum_sum_type]
  simp

section S4Blocks

variable (Y : Matrix (S4IsotypicCarrier mt m22 m211 ms m31) (Fin 3) ℂ)

/-- Trivial-isotype block of a synthesis into the complete carrier. -/
def s4TrivBlock (a : mt) : Matrix (Fin 1) (Fin 3) ℂ :=
  fun i j => Y (Sum.inl (Sum.inl (a, i))) j

/-- `[22]`-isotype block of a synthesis into the complete carrier. -/
def s4B22Block (a : m22) : Matrix (Fin 2) (Fin 3) ℂ :=
  fun i j => Y (Sum.inl (Sum.inr (Sum.inl (a, i)))) j

/-- `[211]`-isotype block of a synthesis into the complete carrier. -/
def s4B211Block (a : m211) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => Y (Sum.inl (Sum.inr (Sum.inr (Sum.inl (a, i))))) j

/-- Sign-isotype block of a synthesis into the complete carrier. -/
def s4SgnBlock (a : ms) : Matrix (Fin 1) (Fin 3) ℂ :=
  fun i j => Y (Sum.inl (Sum.inr (Sum.inr (Sum.inr (a, i))))) j

/-- Standard-isotype block of a synthesis into the complete carrier. -/
def s4StdBlock (a : m31) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => Y (Sum.inr (a, i)) j

end S4Blocks

/-- The purely standard synthesis `p ⊗ I_[31]`, embedded in the complete
carrier with zero components in every inequivalent isotype. -/
def standardIsotypicSynthesis (p : m31 → ℂ) :
    Matrix (S4IsotypicCarrier mt m22 m211 ms m31) (Fin 3) ℂ :=
  fun r j =>
    match r with
    | Sum.inr (a, i) => if i = j then p a else 0
    | Sum.inl _ => 0

section S4Rows

variable (q : StandardS4Generator)
  (Y : Matrix (S4IsotypicCarrier mt m22 m211 ms m31) (Fin 3) ℂ)

/-- Row entries of the isotypic action in the trivial block. -/
theorem s4IsotypicAction_mul_apply_triv (a : mt) (i : Fin 1) (j : Fin 3) :
    (s4IsotypicAction q * Y) (Sum.inl (Sum.inl (a, i))) j =
      ∑ i', trivialS4Gen q i i' * Y (Sum.inl (Sum.inl (a, i'))) j := by
  simp [s4IsotypicAction, Matrix.mul_apply, Fintype.sum_sum_type,
    Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.one_apply,
    ite_mul, Finset.sum_ite_eq]

/-- Row entries of the isotypic action in the `[22]` block. -/
theorem s4IsotypicAction_mul_apply_22 (a : m22) (i : Fin 2) (j : Fin 3) :
    (s4IsotypicAction q * Y) (Sum.inl (Sum.inr (Sum.inl (a, i)))) j =
      ∑ i', s22S4Gen q i i' * Y (Sum.inl (Sum.inr (Sum.inl (a, i')))) j := by
  simp [s4IsotypicAction, Matrix.mul_apply, Fintype.sum_sum_type,
    Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.one_apply,
    ite_mul, Finset.sum_ite_eq]

/-- Row entries of the isotypic action in the `[211]` block. -/
theorem s4IsotypicAction_mul_apply_211 (a : m211) (i : Fin 3) (j : Fin 3) :
    (s4IsotypicAction q * Y) (Sum.inl (Sum.inr (Sum.inr (Sum.inl (a, i)))))
        j =
      ∑ i', s211S4Gen q i i' *
        Y (Sum.inl (Sum.inr (Sum.inr (Sum.inl (a, i'))))) j := by
  simp [s4IsotypicAction, Matrix.mul_apply, Fintype.sum_sum_type,
    Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.one_apply,
    ite_mul, Finset.sum_ite_eq]

/-- Row entries of the isotypic action in the sign block. -/
theorem s4IsotypicAction_mul_apply_sgn (a : ms) (i : Fin 1) (j : Fin 3) :
    (s4IsotypicAction q * Y) (Sum.inl (Sum.inr (Sum.inr (Sum.inr (a, i)))))
        j =
      ∑ i', signS4Gen q i i' *
        Y (Sum.inl (Sum.inr (Sum.inr (Sum.inr (a, i'))))) j := by
  simp [s4IsotypicAction, Matrix.mul_apply, Fintype.sum_sum_type,
    Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.one_apply,
    ite_mul, Finset.sum_ite_eq]

/-- Row entries of the isotypic action in the standard block. -/
theorem s4IsotypicAction_mul_apply_std (a : m31) (i : Fin 3) (j : Fin 3) :
    (s4IsotypicAction q * Y) (Sum.inr (a, i)) j =
      ∑ i', standardS4Carrier q i i' * Y (Sum.inr (a, i')) j := by
  simp [s4IsotypicAction, Matrix.mul_apply, Fintype.sum_sum_type,
    Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.one_apply,
    ite_mul, Finset.sum_ite_eq]

end S4Rows

/-- Blockwise equivariance extracted from full-carrier equivariance. -/
theorem s4IsotypicAction_equivariance_blocks
    (Y : Matrix (S4IsotypicCarrier mt m22 m211 ms m31) (Fin 3) ℂ)
    (hY : ∀ q, s4IsotypicAction q * Y = Y * standardS4Carrier q) :
    (∀ q a, trivialS4Gen q * s4TrivBlock Y a =
        s4TrivBlock Y a * standardS4Carrier q) ∧
    (∀ q a, s22S4Gen q * s4B22Block Y a =
        s4B22Block Y a * standardS4Carrier q) ∧
    (∀ q a, s211S4Gen q * s4B211Block Y a =
        s4B211Block Y a * standardS4Carrier q) ∧
    (∀ q a, signS4Gen q * s4SgnBlock Y a =
        s4SgnBlock Y a * standardS4Carrier q) ∧
    (∀ q a, standardS4Carrier q * s4StdBlock Y a =
        s4StdBlock Y a * standardS4Carrier q) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro q a
    ext i j
    have h := congrFun (congrFun (hY q) (Sum.inl (Sum.inl (a, i)))) j
    rw [s4IsotypicAction_mul_apply_triv] at h
    rw [Matrix.mul_apply, Matrix.mul_apply]
    exact h
  · intro q a
    ext i j
    have h := congrFun (congrFun (hY q)
      (Sum.inl (Sum.inr (Sum.inl (a, i))))) j
    rw [s4IsotypicAction_mul_apply_22] at h
    rw [Matrix.mul_apply, Matrix.mul_apply]
    exact h
  · intro q a
    ext i j
    have h := congrFun (congrFun (hY q)
      (Sum.inl (Sum.inr (Sum.inr (Sum.inl (a, i)))))) j
    rw [s4IsotypicAction_mul_apply_211] at h
    rw [Matrix.mul_apply, Matrix.mul_apply]
    exact h
  · intro q a
    ext i j
    have h := congrFun (congrFun (hY q)
      (Sum.inl (Sum.inr (Sum.inr (Sum.inr (a, i)))))) j
    rw [s4IsotypicAction_mul_apply_sgn] at h
    rw [Matrix.mul_apply, Matrix.mul_apply]
    exact h
  · intro q a
    ext i j
    have h := congrFun (congrFun (hY q) (Sum.inr (a, i))) j
    rw [s4IsotypicAction_mul_apply_std] at h
    rw [Matrix.mul_apply, Matrix.mul_apply]
    exact h

/-- `cor:S4-provenance-isotypic`, synthesis clause: every equivariant
tetrahedral provenance synthesis into the complete five-isotype carrier
vanishes on the trivial, `[22]`, `[211]`, and sign isotypes and is the unique
standard-block synthesis `p ⊗ I_[31]`. -/
theorem s4_provenance_synthesis_unique
    (Y : Matrix (S4IsotypicCarrier mt m22 m211 ms m31) (Fin 3) ℂ)
    (hY : ∀ q, s4IsotypicAction q * Y = Y * standardS4Carrier q) :
    ∃! p : m31 → ℂ, Y = standardIsotypicSynthesis p := by
  obtain ⟨htriv, h22, h211, hsgn, hstd⟩ :=
    s4IsotypicAction_equivariance_blocks Y hY
  have htriv0 : ∀ a, s4TrivBlock Y a = 0 :=
    fun a => trivialS4_intertwiner_zero _ (fun q => htriv q a)
  have h220 : ∀ a, s4B22Block Y a = 0 :=
    fun a => s22S4_intertwiner_zero _ (fun q => h22 q a)
  have h2110 : ∀ a, s4B211Block Y a = 0 :=
    fun a => s211S4_intertwiner_zero _ (fun q => h211 q a)
  have hsgn0 : ∀ a, s4SgnBlock Y a = 0 :=
    fun a => signS4_intertwiner_zero _ (fun q => hsgn q a)
  have hstdc : ∀ a, ∃! c : ℂ,
      s4StdBlock Y a = c • (1 : Matrix (Fin 3) (Fin 3) ℂ) :=
    fun a => standardS4Carrier_commutant_is_scalar _ (fun q => hstd q a)
  refine ⟨fun a => Y (Sum.inr (a, 0)) 0, ?_, ?_⟩
  · ext r j
    match r with
    | Sum.inl (Sum.inl (a, i)) =>
        exact congrFun (congrFun (htriv0 a) i) j
    | Sum.inl (Sum.inr (Sum.inl (a, i))) =>
        exact congrFun (congrFun (h220 a) i) j
    | Sum.inl (Sum.inr (Sum.inr (Sum.inl (a, i)))) =>
        exact congrFun (congrFun (h2110 a) i) j
    | Sum.inl (Sum.inr (Sum.inr (Sum.inr (a, i)))) =>
        exact congrFun (congrFun (hsgn0 a) i) j
    | Sum.inr (a, i) =>
        obtain ⟨c, hc, -⟩ := hstdc a
        have hcv : Y (Sum.inr (a, 0)) 0 = c := by
          have h00 := congrFun (congrFun hc 0) 0
          simpa [s4StdBlock, Matrix.one_apply] using h00
        have hij := congrFun (congrFun hc i) j
        simp only [s4StdBlock] at hij
        rw [hij]
        simp [standardIsotypicSynthesis, hcv, Matrix.one_apply]
  · intro p hp
    funext a
    have h := congrFun (congrFun hp (Sum.inr (a, 0))) 0
    simpa [standardIsotypicSynthesis] using h

end NCG
