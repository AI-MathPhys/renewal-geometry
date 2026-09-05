/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# SMST commutants: support-polar loading, the multiplicity
  quiver, and the massless alternatives
  (`thm:SMST-support-polar-commutant`,
  `thm:SMST-quiver-commutant`, `cor:SMST-graph-massless`,
  Gran-Tensor manuscript)

* `commutant_polynomial_calculus`: the no-extra-loading core of
  the boxed commutant equalities — anything commuting with an
  incidence datum commutes with every polynomial functional
  calculus output of it, so support projections, support
  metrics, and polar data add no finite loading;
* `commutant_support_gram`: in particular the support Gram
  `F*F` stays in the bicommutant of `{F, F*}`;
* `quiver_certificate`: the boxed quiver-form kernel — the
  Hilbert–Schmidt weight `tr(K*K)` of a commutator block
  vanishes iff the block intertwines exactly (`K = 0`), so the
  first positive quiver eigenvalue certifies the absence of
  additional flavour/generation endomorphisms;
* `quiver_form_kernel`: the summed form — the full nonnegative
  commutator ledger vanishes iff every block intertwines;
* `massless_limit`: the constant-rank branch limit
  `α_m → -Im Tr(D†dD)` as `m ↓ 0` (each singular-value factor
  `a/(s + m²) → a/s` continuously);
* `zero_mode_dichotomy`: the boxed full-rank alternative — a
  square incidence map either has `det D ≠ 0` (flat massless
  connection after the determinant phase) or carries an explicit
  zero mode, the exact remaining local obstruction.

Rendering disclosed: the von Neumann bicommutant identifications
`𝓜 = (𝓞^sup)'` and `C*(𝓢,T)' ≅ End 𝔔` as algebra isomorphisms,
the Hilbert–Schmidt basis expansion of the ambient commutator
form, and the determinant-line curvature statement
`(det ker D)* ⊗ det coker D` are the manuscript's
operator-algebra and line-bundle layers; the functional-calculus
closure, the exact kernel certificates, the scalar limit, and
the rank dichotomy are proved here.
-/

open Matrix Polynomial

namespace NCG

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n]

/-- Functional-calculus closure of the commutant: `X` commuting
with `M` commutes with every polynomial in `M` — support data
add no finite loading. -/
theorem commutant_polynomial_calculus (X M : Matrix n n ℂ)
    (h : Commute X M) (p : Polynomial ℂ) :
    Commute X (Polynomial.aeval M p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add]
    exact hp.add_right hq
  | monomial k a =>
    rw [Polynomial.aeval_monomial]
    have hsc : Commute X (algebraMap ℂ (Matrix n n ℂ) a) :=
      (Algebra.commutes a X).symm
    exact hsc.mul_right (h.pow_right k)

omit [DecidableEq n] in
/-- The support Gram stays in the commutant closure: commuting
with `F` and `F*` gives commuting with `F*F`. -/
theorem commutant_support_gram (X F : Matrix n n ℂ)
    (hF : Commute X F) (hFH : Commute X Fᴴ) :
    Commute X (Fᴴ * F) :=
  hFH.mul_right hF

omit [DecidableEq n] in
open scoped ComplexOrder in
/-- Boxed quiver certificate: the Hilbert–Schmidt weight of a
commutator block vanishes iff the block intertwines exactly. -/
theorem quiver_certificate (K : Matrix n m ℂ) :
    (Kᴴ * K).trace = 0 ↔ K = 0 :=
  Matrix.trace_conjTranspose_mul_self_eq_zero_iff

omit [DecidableEq n] in
/-- Summed quiver-form kernel: the full nonnegative commutator
ledger vanishes iff every block intertwines. -/
theorem quiver_form_kernel {J : Type*} [Fintype J]
    (K : J → Matrix n m ℂ) (f : J → ℝ) (hf : ∀ j, 0 ≤ f j)
    (hrep : ∀ j, ((K j)ᴴ * K j).trace = (f j : ℂ)) :
    (∑ j, f j = 0) ↔ ∀ j, K j = 0 := by
  rw [Finset.sum_eq_zero_iff_of_nonneg
    (fun j _ => hf j)]
  constructor
  · intro hz j
    have : ((K j)ᴴ * K j).trace = 0 := by
      rw [hrep j, hz j (Finset.mem_univ j)]
      norm_num
    exact (quiver_certificate (K j)).mp this
  · intro hz j _
    have : ((f j : ℝ) : ℂ) = 0 := by
      rw [← hrep j, hz j]
      simp
    exact_mod_cast this

/-! ## Exact multiplicity-quiver block calculation -/

/-- Squared Hilbert--Schmidt norm, written entrywise. -/
noncomputable def quiverHSSq {a b : Type*} [Fintype a] [Fintype b]
    (A : Matrix a b ℂ) : ℝ :=
  ∑ i, ∑ j, Complex.normSq (A i j)

/-- Reassemble a block from its coefficients in the canonical
Hilbert--Schmidt orthonormal matrix-unit basis of `B(Vₐ,V_b)`. -/
def quiverAssemble {Va Vb Na Nb : Type*}
    (B : Vb → Va → Matrix Nb Na ℂ) :
    Matrix (Vb × Nb) (Va × Na) ℂ :=
  fun x y => B x.1 y.1 x.2 y.2

/-- The residual multiplicity operator on one central block. -/
def quiverResidual {V N : Type*} [DecidableEq V]
    (X : Matrix N N ℂ) : Matrix (V × N) (V × N) ℂ :=
  fun i j => if i.1 = j.1 then X i.2 j.2 else 0

/-- Explicit rectangular matrix composition.  Naming it avoids an
ambiguity with the repository's `CStarMatrix` multiplication
instance when the source and target index types differ. -/
def quiverMatMul {a b c : Type*} [Fintype b]
    (A : Matrix a b ℂ) (B : Matrix b c ℂ) : Matrix a c ℂ :=
  fun i k => ∑ j, A i j * B j k

/-- The block of the ambient commutator is precisely the assembly of
the quiver-arrow intertwining defects. -/
theorem quiver_commutator_block_expansion
    {Va Vb Na Nb : Type*}
    [Fintype Va] [Fintype Vb] [Fintype Na] [Fintype Nb]
    [DecidableEq Va] [DecidableEq Vb]
    (B : Vb → Va → Matrix Nb Na ℂ)
    (Xa : Matrix Na Na ℂ) (Xb : Matrix Nb Nb ℂ) :
    quiverMatMul (quiverResidual Xb) (quiverAssemble B)
        - quiverMatMul (quiverAssemble B) (quiverResidual Xa)
      = quiverAssemble (fun vb va => Xb * B vb va - B vb va * Xa) := by
  ext ⟨vb, nb⟩ ⟨va, na⟩
  simp only [quiverMatMul, quiverResidual, quiverAssemble,
    Matrix.sub_apply]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp only [ite_mul, mul_ite, zero_mul, mul_zero]
  simp
  rw [Matrix.mul_apply, Matrix.mul_apply]

/-- Orthogonality of matrix units gives the exact Hilbert--Schmidt
Parseval identity for a reconstructed quiver block. -/
theorem quiver_hs_assemble
    {Va Vb Na Nb : Type*}
    [Fintype Va] [Fintype Vb] [Fintype Na] [Fintype Nb]
    (B : Vb → Va → Matrix Nb Na ℂ) :
    quiverHSSq (quiverAssemble B)
      = ∑ vb, ∑ va, quiverHSSq (B vb va) := by
  simp only [quiverHSSq, quiverAssemble]
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  congr 1
  funext vb
  rw [Finset.sum_comm]

/-- The entrywise Hilbert--Schmidt square is nonnegative. -/
theorem quiverHSSq_nonneg
    {a b : Type*} [Fintype a] [Fintype b]
    (A : Matrix a b ℂ) : 0 ≤ quiverHSSq A := by
  unfold quiverHSSq
  exact Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _

/-- The Hilbert--Schmidt square detects the zero matrix. -/
theorem quiverHSSq_eq_zero_iff
    {a b : Type*} [Fintype a] [Fintype b]
    (A : Matrix a b ℂ) : quiverHSSq A = 0 ↔ A = 0 := by
  constructor
  · intro h
    have hi := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => Finset.sum_nonneg fun j _ =>
        Complex.normSq_nonneg (A i j))).mp h
    ext i j
    have hj := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => Complex.normSq_nonneg (A i j))).mp
        (hi i (Finset.mem_univ i))
    exact Complex.normSq_eq_zero.mp (hj j (Finset.mem_univ j))
  · rintro rfl
    simp [quiverHSSq]

/-- A reconstructed block commutes with the residual family iff every
multiplicity coefficient is a quiver intertwiner. -/
theorem quiver_block_commutes_iff
    {Va Vb Na Nb : Type*}
    [Fintype Va] [Fintype Vb] [Fintype Na] [Fintype Nb]
    [DecidableEq Va] [DecidableEq Vb]
    [Nonempty Na] [Nonempty Nb]
    (B : Vb → Va → Matrix Nb Na ℂ)
    (Xa : Matrix Na Na ℂ) (Xb : Matrix Nb Nb ℂ) :
    quiverMatMul (quiverResidual Xb) (quiverAssemble B)
        = quiverMatMul (quiverAssemble B) (quiverResidual Xa)
      ↔ ∀ vb va, Xb * B vb va = B vb va * Xa := by
  rw [← sub_eq_zero]
  rw [quiver_commutator_block_expansion]
  constructor
  · intro h vb va
    ext nb na
    have he := congrFun (congrFun h (vb, nb)) (va, na)
    exact sub_eq_zero.mp (by simpa [quiverAssemble] using he)
  · intro h
    ext ⟨vb, nb⟩ ⟨va, na⟩
    simp [quiverAssemble, h vb va]

/-- Exact Hilbert--Schmidt expansion of the ambient commutator form
restricted to the residual commutant. -/
theorem quiver_commutator_hs_expansion
    {Va Vb Na Nb : Type*}
    [Fintype Va] [Fintype Vb] [Fintype Na] [Fintype Nb]
    [DecidableEq Va] [DecidableEq Vb]
    (B : Vb → Va → Matrix Nb Na ℂ)
    (Xa : Matrix Na Na ℂ) (Xb : Matrix Nb Nb ℂ) :
    quiverHSSq (quiverMatMul (quiverResidual Xb) (quiverAssemble B)
        - quiverMatMul (quiverAssemble B) (quiverResidual Xa))
      = ∑ vb, ∑ va,
          quiverHSSq (Xb * B vb va - B vb va * Xa) := by
  rw [quiver_commutator_block_expansion, quiver_hs_assemble]

/-- The full finite quiver commutator form has kernel exactly the
endomorphism algebra of the multiplicity quiver.  The positive scalar
`volume` is the manuscript's `dim 𝓜_X` normalization. -/
theorem quiver_commutator_form_kernel
    {J Va Vb Na Nb : Type*}
    [Fintype J] [Fintype Va] [Fintype Vb] [Fintype Na] [Fintype Nb]
    (B : J → Vb → Va → Matrix Nb Na ℂ)
    (Xa : Matrix Na Na ℂ) (Xb : Matrix Nb Nb ℂ)
    (volume : ℝ) (hvolume : 0 < volume) :
    (volume⁻¹ * ∑ j, ∑ vb, ∑ va,
        quiverHSSq (Xb * B j vb va - B j vb va * Xa) = 0)
      ↔ ∀ j vb va, Xb * B j vb va = B j vb va * Xa := by
  have hv : volume⁻¹ ≠ 0 := inv_ne_zero (ne_of_gt hvolume)
  rw [mul_eq_zero]
  simp only [hv, false_or]
  constructor
  · intro h j vb va
    have hj := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => Finset.sum_nonneg fun vb _ =>
        Finset.sum_nonneg fun va _ => quiverHSSq_nonneg _)).mp h
    have hb := (Finset.sum_eq_zero_iff_of_nonneg
      (fun vb _ => Finset.sum_nonneg fun va _ =>
        quiverHSSq_nonneg _)).mp (hj j (Finset.mem_univ j))
    have ha := (Finset.sum_eq_zero_iff_of_nonneg
      (fun va _ => quiverHSSq_nonneg
        (Xb * B j vb va - B j vb va * Xa))).mp
          (hb vb (Finset.mem_univ vb))
    exact sub_eq_zero.mp ((quiverHSSq_eq_zero_iff _).mp
      (ha va (Finset.mem_univ va)))
  · intro h
    apply Finset.sum_eq_zero
    intro j _
    apply Finset.sum_eq_zero
    intro vb _
    apply Finset.sum_eq_zero
    intro va _
    rw [h j vb va, sub_self]
    simp [quiverHSSq]

/-! ## Arbitrary finite typed multiplicity quivers -/

/-- A residual family is in the commutant of every reconstructed
typed arrow exactly when it is an endomorphism of the multiplicity
quiver.  This is the global, dependent-type form of
`C*(S,T)' ≅ End Q`; after the canonical central decomposition the
map is literally the identity on the family `X`. -/
theorem finite_typed_quiver_commutant_iff_endomorphism
    {A J : Type*} [Fintype J]
    (V N : A → Type*) [∀ a, Fintype (V a)] [∀ a, Fintype (N a)]
    [∀ a, DecidableEq (V a)] [∀ a, Nonempty (N a)]
    (src dst : J → A)
    (B : ∀ j, V (dst j) → V (src j) →
      Matrix (N (dst j)) (N (src j)) ℂ)
    (X : ∀ a, Matrix (N a) (N a) ℂ) :
    (∀ j,
      quiverMatMul (quiverResidual (X (dst j))) (quiverAssemble (B j))
        = quiverMatMul (quiverAssemble (B j))
            (quiverResidual (X (src j))))
      ↔ ∀ j vb va,
          X (dst j) * B j vb va = B j vb va * X (src j) := by
  constructor
  · intro h j
    exact (quiver_block_commutes_iff
      (B j) (X (src j)) (X (dst j))).mp (h j)
  · intro h j
    exact (quiver_block_commutes_iff
      (B j) (X (src j)) (X (dst j))).mpr (h j)

/-- The normalized ambient Hilbert--Schmidt commutator form of an
arbitrary finite typed multiplicity quiver is the sum of the
coefficientwise arrow defects displayed in the manuscript. -/
theorem finite_typed_quiver_hs_expansion
    {A J : Type*} [Fintype J]
    (V N : A → Type*) [∀ a, Fintype (V a)] [∀ a, Fintype (N a)]
    [∀ a, DecidableEq (V a)]
    (src dst : J → A)
    (B : ∀ j, V (dst j) → V (src j) →
      Matrix (N (dst j)) (N (src j)) ℂ)
    (X : ∀ a, Matrix (N a) (N a) ℂ)
    (volume : ℝ) :
    volume⁻¹ * ∑ j,
      quiverHSSq
        (quiverMatMul (quiverResidual (X (dst j)))
            (quiverAssemble (B j))
          - quiverMatMul (quiverAssemble (B j))
              (quiverResidual (X (src j))))
      = volume⁻¹ * ∑ j, ∑ vb, ∑ va,
          quiverHSSq
            (X (dst j) * B j vb va - B j vb va * X (src j)) := by
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  exact quiver_commutator_hs_expansion
    (B j) (X (src j)) (X (dst j))

/-- Consequently the kernel of the normalized finite typed-quiver
form is exactly `End Q`. -/
theorem finite_typed_quiver_form_kernel
    {A J : Type*} [Fintype J]
    (V N : A → Type*) [∀ a, Fintype (V a)] [∀ a, Fintype (N a)]
    (src dst : J → A)
    (B : ∀ j, V (dst j) → V (src j) →
      Matrix (N (dst j)) (N (src j)) ℂ)
    (X : ∀ a, Matrix (N a) (N a) ℂ)
    (volume : ℝ) (hvolume : 0 < volume) :
    (volume⁻¹ * ∑ j, ∑ vb, ∑ va,
        quiverHSSq
          (X (dst j) * B j vb va - B j vb va * X (src j)) = 0)
      ↔ ∀ j vb va,
          X (dst j) * B j vb va = B j vb va * X (src j) := by
  have hv : volume⁻¹ ≠ 0 := inv_ne_zero (ne_of_gt hvolume)
  rw [mul_eq_zero]
  simp only [hv, false_or]
  constructor
  · intro h j vb va
    have hj := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => Finset.sum_nonneg fun vb _ =>
        Finset.sum_nonneg fun va _ => quiverHSSq_nonneg _)).mp h
    have hb := (Finset.sum_eq_zero_iff_of_nonneg
      (fun vb _ => Finset.sum_nonneg fun va _ =>
        quiverHSSq_nonneg _)).mp (hj j (Finset.mem_univ j))
    have ha := (Finset.sum_eq_zero_iff_of_nonneg
      (fun va _ => quiverHSSq_nonneg _)).mp
        (hb vb (Finset.mem_univ vb))
    exact sub_eq_zero.mp ((quiverHSSq_eq_zero_iff _).mp
      (ha va (Finset.mem_univ va)))
  · intro h
    apply Finset.sum_eq_zero
    intro j _
    apply Finset.sum_eq_zero
    intro vb _
    apply Finset.sum_eq_zero
    intro va _
    rw [h j vb va, sub_self]
    simp [quiverHSSq]

/-- Constant-rank massless limit: each singular-value factor of
`α_m` converges continuously as `m ↓ 0`. -/
theorem massless_limit (a s : ℝ) (hs : 0 < s) :
    Filter.Tendsto (fun μ : ℝ => a / (s + μ ^ 2))
      (nhds 0) (nhds (a / s)) := by
  have hc : Continuous fun μ : ℝ => a / (s + μ ^ 2) := by
    refine continuous_const.div (by fun_prop) fun μ => ?_
    positivity
  simpa using hc.tendsto 0

/-- Boxed full-rank alternative: a square incidence map either
has `det D ≠ 0` or carries an explicit zero mode. -/
theorem zero_mode_dichotomy (D : Matrix n n ℂ) :
    D.det ≠ 0 ∨ ∃ v ≠ 0, D.mulVec v = 0 := by
  by_cases h : D.det = 0
  · exact Or.inr (Matrix.exists_mulVec_eq_zero_iff.mpr h)
  · exact Or.inl h

end NCG
