/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Sharp five-slot determinant-mode floor

`thm:determinant-arity-floor` of the spacetime–gauge duality paper.

A native finite carrier has a basis graded by **central weights** `(a, b) ∈ ℤ²`: the
defining weights are `(1, 0)` on the colour carrier `C ≅ ℂ³`, `(0, 1)` on the weak
carrier `W₂ ≅ ℂ²`, and `(0, 0)` on a neutral sector `N` (`singleWeight`).  The centre
of `U(3) × U(2)` with angles `(α, β)` acts on a basis vector of weight `(a, b)` by
`e^{i(aα + bβ)}` (`torusAction`), hence by conjugation on the matrix unit `E_{ij}` of the
endomorphism algebra by the difference weight `w i − w j` (`torusAction_conj_single`).
The **central-weight support of the endomorphism algebra** is therefore the set of
differences `w i − w j` (`endWeightSupport`), and on a diagonal `k`-fold tensor carrier
the basis weights are the slot sums (`tensorWeight`).

* `endWeightSupport_single_subset`: the single-system support contains only
  `(0,0), ±(1,0), ±(0,1), ±(1,−1)` (`singleEndList`; with equality when the neutral
  sector is nonempty, `endWeightSupport_single_eq`), so it does not contain the
  determinant-incidence weight `(−3, −2)` (`det_weight_not_mem_single`);
* `det_weight_not_mem_tensor`: on a `k`-fold tensor carrier every basis weight `(a, b)`
  has `a, b ≥ 0` and `a + b ≤ k` (`tensorWeight_single_bounds`), so `(−3, −2)` is absent
  for `k < 5`;
* `det_weight_mem_tensor_five`: at `k = 5` the basis line `C ⊗ C ⊗ C ⊗ W₂ ⊗ W₂` has
  weight `(3, 2)` (the weight of the alternating line `det C · det W₂` inside it), and a
  rank-one map from it to a neutral line has weight `(−3, −2)`, which is present;
* `determinant_arity_floor`: the assembled theorem.

Scoped hypotheses: the neutral sector `N` is an arbitrary type; the `k = 5` witness needs
a neutral line, i.e. `[Nonempty N]`, exactly as the manuscript's proof ("a rank-one map
from that line to a neutral line").  The weight bookkeeping is stated combinatorially on
the graded basis; the lemma `torusAction_conj_single` records that this is the actual
central character of the matrix units under the diagonal torus action.
-/

open Matrix

namespace RenewalGeometry
namespace DeterminantArity

/-! ### The diagonal torus action and the weight of a matrix unit -/

section Torus

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The central character `e^{i(aα+bβ)}` of the weight `(a, b)` at angles `(α, β)`. -/
noncomputable def centralChar (w : ℤ × ℤ) (α β : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((w.1 : ℂ) * α + (w.2 : ℂ) * β))

theorem centralChar_mul (w w' : ℤ × ℤ) (α β : ℝ) :
    centralChar w α β * centralChar w' α β = centralChar (w + w') α β := by
  unfold centralChar
  rw [← Complex.exp_add]
  congr 1
  simp only [Prod.fst_add, Prod.snd_add]
  push_cast
  ring

theorem centralChar_zero (α β : ℝ) : centralChar 0 α β = 1 := by
  simp [centralChar]

/-- The diagonal action of the centre with angles `(α, β)` on a carrier with basis
weights `w`: the basis vector `i` of weight `w i` is multiplied by `e^{i(aα+bβ)}`. -/
noncomputable def torusAction (w : ι → ℤ × ℤ) (α β : ℝ) : Matrix ι ι ℂ :=
  Matrix.diagonal fun i => centralChar (w i) α β

/-- The torus action at `(α, β)` and `(−α, −β)` are mutually inverse. -/
theorem torusAction_mul_neg (w : ι → ℤ × ℤ) (α β : ℝ) :
    torusAction w α β * torusAction w (-α) (-β) = 1 := by
  unfold torusAction
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  ext i
  unfold centralChar
  rw [← Complex.exp_add]
  convert Complex.exp_zero using 2
  push_cast
  ring

/-- **The weight of a matrix unit.**  Conjugating `E_{ij}` by the torus action multiplies
it by the central character of the difference weight `w i − w j`: the central-weight
support of the endomorphism algebra is the set of differences `w i − w j`. -/
theorem torusAction_conj_single (w : ι → ℤ × ℤ) (α β : ℝ) (i j : ι) :
    torusAction w α β * Matrix.single i j (1 : ℂ) * torusAction w (-α) (-β) =
      centralChar (w i - w j) α β • Matrix.single i j (1 : ℂ) := by
  ext a b
  unfold torusAction
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply, Matrix.single_apply]
  by_cases h : i = a ∧ j = b
  · obtain ⟨rfl, rfl⟩ := h
    simp only [and_self, ite_true, mul_one, smul_eq_mul]
    unfold centralChar
    rw [← Complex.exp_add]
    congr 1
    simp only [Prod.fst_sub, Prod.snd_sub]
    push_cast
    ring
  · simp [h]

end Torus

/-! ### Weight combinatorics -/

/-- The central-weight support of the endomorphism algebra of a carrier with basis
weights `w`: all target-minus-source differences `w i − w j`. -/
def endWeightSupport {ι : Type*} (w : ι → ℤ × ℤ) : Set (ℤ × ℤ) :=
  {c | ∃ i j, w i - w j = c}

/-- The single-system carrier `C ⊕ W₂ ⊕ N`: colour `ℂ³`, weak `ℂ²`, neutral sector `N`. -/
abbrev SingleCarrier (N : Type*) := Fin 3 ⊕ (Fin 2 ⊕ N)

/-- The defining central weights `(1,0)` on `C`, `(0,1)` on `W₂`, `(0,0)` on `N`. -/
def singleWeight (N : Type*) : SingleCarrier N → ℤ × ℤ
  | Sum.inl _ => (1, 0)
  | Sum.inr (Sum.inl _) => (0, 1)
  | Sum.inr (Sum.inr _) => (0, 0)

/-- The list `(0,0), ±(1,0), ±(0,1), ±(1,−1)` of the theorem. -/
def singleEndList : Set (ℤ × ℤ) :=
  {(0, 0), (1, 0), (-1, 0), (0, 1), (0, -1), (1, -1), (-1, 1)}

/-- The determinant-incidence weight `(−3, −2)` (the weight of `det C^{-1} det W₂^{-1}`). -/
def detWeight : ℤ × ℤ := (-3, -2)

theorem singleWeight_cases {N : Type*} (x : SingleCarrier N) :
    singleWeight N x = (1, 0) ∨ singleWeight N x = (0, 1) ∨ singleWeight N x = (0, 0) := by
  rcases x with a | a | a <;> simp [singleWeight]

/-- **Single-system support.**  The central-weight support of the single-system
endomorphism algebra contains only `(0,0), ±(1,0), ±(0,1), ±(1,−1)`. -/
theorem endWeightSupport_single_subset (N : Type*) :
    endWeightSupport (singleWeight N) ⊆ singleEndList := by
  rintro c ⟨i, j, rfl⟩
  rcases singleWeight_cases i with hi | hi | hi <;>
    rcases singleWeight_cases j with hj | hj | hj <;>
    simp [hi, hj, singleEndList, Prod.ext_iff]

/-- With a nonempty neutral sector the single-system support is exactly the list. -/
theorem endWeightSupport_single_eq (N : Type*) [Nonempty N] :
    endWeightSupport (singleWeight N) = singleEndList := by
  refine le_antisymm (endWeightSupport_single_subset N) ?_
  obtain ⟨n⟩ := ‹Nonempty N›
  intro c hc
  simp only [singleEndList, Set.mem_insert_iff, Set.mem_singleton_iff] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨Sum.inl 0, Sum.inl 0, by simp [singleWeight, Prod.ext_iff]⟩
  · exact ⟨Sum.inl 0, Sum.inr (Sum.inr n), by simp [singleWeight, Prod.ext_iff]⟩
  · exact ⟨Sum.inr (Sum.inr n), Sum.inl 0, by simp [singleWeight, Prod.ext_iff]⟩
  · exact ⟨Sum.inr (Sum.inl 0), Sum.inr (Sum.inr n), by simp [singleWeight, Prod.ext_iff]⟩
  · exact ⟨Sum.inr (Sum.inr n), Sum.inr (Sum.inl 0), by simp [singleWeight, Prod.ext_iff]⟩
  · exact ⟨Sum.inl 0, Sum.inr (Sum.inl 0), by simp [singleWeight, Prod.ext_iff]⟩
  · exact ⟨Sum.inr (Sum.inl 0), Sum.inl 0, by simp [singleWeight, Prod.ext_iff]⟩

/-- The determinant-incidence weight is not in the single-system support. -/
theorem det_weight_not_mem_single (N : Type*) :
    detWeight ∉ endWeightSupport (singleWeight N) := by
  intro h
  have := endWeightSupport_single_subset N h
  simp [singleEndList, detWeight] at this

/-- The basis weights of the diagonal `k`-fold tensor carrier: slot sums. -/
def tensorWeight {ι : Type*} (w : ι → ℤ × ℤ) (k : ℕ) : (Fin k → ι) → ℤ × ℤ :=
  fun f => ∑ s, w (f s)

theorem singleWeight_bounds {N : Type*} (x : SingleCarrier N) :
    0 ≤ (singleWeight N x).1 ∧ 0 ≤ (singleWeight N x).2 ∧
      (singleWeight N x).1 + (singleWeight N x).2 ≤ 1 := by
  rcases x with a | a | a <;> simp [singleWeight]

/-- On the `k`-fold tensor carrier every basis weight `(a, b)` has `a, b ≥ 0` and
`a + b ≤ k`. -/
theorem tensorWeight_single_bounds (N : Type*) (k : ℕ) (f : Fin k → SingleCarrier N) :
    0 ≤ (tensorWeight (singleWeight N) k f).1 ∧ 0 ≤ (tensorWeight (singleWeight N) k f).2 ∧
      (tensorWeight (singleWeight N) k f).1 + (tensorWeight (singleWeight N) k f).2 ≤ k := by
  unfold tensorWeight
  rw [Prod.fst_sum, Prod.snd_sum, ← Finset.sum_add_distrib]
  refine ⟨Finset.sum_nonneg fun s _ => (singleWeight_bounds (f s)).1,
    Finset.sum_nonneg fun s _ => (singleWeight_bounds (f s)).2.1, ?_⟩
  calc ∑ s, ((singleWeight N (f s)).1 + (singleWeight N (f s)).2)
      ≤ ∑ _s : Fin k, (1 : ℤ) := Finset.sum_le_sum fun s _ => (singleWeight_bounds (f s)).2.2
    _ = k := by simp

/-- **Absence below five slots.**  On a `k`-fold tensor carrier with `k < 5`, the
determinant-incidence weight `(−3, −2)` is not in the central-weight support of the
endomorphism algebra: a target-minus-source weight with total charge `−5` cannot occur. -/
theorem det_weight_not_mem_tensor (N : Type*) {k : ℕ} (hk : k < 5) :
    detWeight ∉ endWeightSupport (tensorWeight (singleWeight N) k) := by
  rintro ⟨f, g, hfg⟩
  obtain ⟨hf1, hf2, hf⟩ := tensorWeight_single_bounds N k f
  obtain ⟨hg1, hg2, hg⟩ := tensorWeight_single_bounds N k g
  rw [detWeight, Prod.ext_iff, Prod.fst_sub, Prod.snd_sub] at hfg
  omega

/-- The five-slot basis line `C ⊗ C ⊗ C ⊗ W₂ ⊗ W₂` (the carrier of the alternating line
`det C · det W₂`). -/
def detLineSlot (N : Type*) : Fin 5 → SingleCarrier N :=
  ![Sum.inl 0, Sum.inl 0, Sum.inl 0, Sum.inr (Sum.inl 0), Sum.inr (Sum.inl 0)]

/-- The five-slot determinant line has weight `(3, 2)`. -/
theorem tensorWeight_detLineSlot (N : Type*) :
    tensorWeight (singleWeight N) 5 (detLineSlot N) = (3, 2) := by
  simp [tensorWeight, detLineSlot, Fin.sum_univ_five, singleWeight]

/-- A neutral five-slot line has weight `(0, 0)`. -/
theorem tensorWeight_neutral (N : Type*) (n : N) :
    tensorWeight (singleWeight N) 5 (fun _ => Sum.inr (Sum.inr n)) = (0, 0) := by
  simp [tensorWeight, singleWeight]

/-- **Presence at five slots.**  A rank-one map from the determinant line to a neutral
line has weight `(0,0) − (3,2) = (−3, −2)`, so the determinant-incidence weight is in the
central-weight support of the five-fold endomorphism algebra. -/
theorem det_weight_mem_tensor_five (N : Type*) [Nonempty N] :
    detWeight ∈ endWeightSupport (tensorWeight (singleWeight N) 5) := by
  obtain ⟨n⟩ := ‹Nonempty N›
  refine ⟨fun _ => Sum.inr (Sum.inr n), detLineSlot N, ?_⟩
  rw [tensorWeight_neutral, tensorWeight_detLineSlot]
  decide

/-- **`thm:determinant-arity-floor`** (sharp five-slot determinant-mode floor).  The
central-weight support of the single-system endomorphism algebra contains only
`(0,0), ±(1,0), ±(0,1), ±(1,−1)` and therefore not the determinant-incidence weight
`(−3, −2)`; on a diagonal `k`-fold tensor carrier this weight is absent for `k < 5` and
present for `k = 5`. -/
theorem determinant_arity_floor (N : Type*) [Nonempty N] :
    endWeightSupport (singleWeight N) ⊆ singleEndList ∧
      detWeight ∉ endWeightSupport (singleWeight N) ∧
      (∀ k : ℕ, k < 5 → detWeight ∉ endWeightSupport (tensorWeight (singleWeight N) k)) ∧
      detWeight ∈ endWeightSupport (tensorWeight (singleWeight N) 5) :=
  ⟨endWeightSupport_single_subset N, det_weight_not_mem_single N,
    fun _ hk => det_weight_not_mem_tensor N hk, det_weight_mem_tensor_five N⟩

/-- The presence at `k = 5` is realised by an actual matrix unit: conjugating the
rank-one map `E_{g, f}` from the determinant line `f` to a neutral line `g` by the torus
action multiplies it by the character of `(−3, −2)`. -/
theorem det_weight_matrix_unit (N : Type*) [Fintype N] [DecidableEq N] (n : N) (α β : ℝ) :
    torusAction (tensorWeight (singleWeight N) 5) α β *
        Matrix.single (fun _ : Fin 5 => Sum.inr (Sum.inr n)) (detLineSlot N) (1 : ℂ) *
        torusAction (tensorWeight (singleWeight N) 5) (-α) (-β) =
      centralChar detWeight α β •
        Matrix.single (fun _ : Fin 5 => Sum.inr (Sum.inr n)) (detLineSlot N) (1 : ℂ) := by
  rw [torusAction_conj_single, tensorWeight_neutral, tensorWeight_detLineSlot]
  have h : ((0 : ℤ), (0 : ℤ)) - (3, 2) = detWeight := by decide
  rw [h]

end DeterminantArity
end RenewalGeometry
