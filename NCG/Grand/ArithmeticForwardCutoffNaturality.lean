/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ForwardCornerCompression
import NCG.Grand.ArForwardGeneration
import NCG.Grand.ArFiniteEuler
import NCG.Grand.ArithmeticDerivedHistories

/-!
# Exact naturality of forward arithmetic histories under record cutoff

This file completes `thm:ar-record-cutoff`.  It constructs the literal unital
algebra homomorphism from the forward chronology algebra at cutoff `Y` to the
one at cutoff `X`, proves that its underlying map is the manuscript's corner
compression, and applies it to the zeta history, its terminating inverse, its
terminating logarithm, commutators, arbitrary diagonal histories, and finite
forward words.  The generic diagonal statement simultaneously covers the
character, affine, Mellin, heat, window, and factor-depth histories.
-/

open Matrix

namespace NCG
namespace ArithmeticForwardCutoffNaturality

/-- The canonical embedding of endpoint indices under `X ≤ Y`. -/
def endpointEmbedding {X Y : ℕ} (hXY : X ≤ Y) : Fin X → Fin Y :=
  fun i => ⟨i, lt_of_lt_of_le i.isLt hXY⟩

theorem cornerJ_apply_embedding {X Y : ℕ} (hXY : X ≤ Y)
    (j : Fin Y) (i : Fin X) :
    cornerJ X Y j i = if j = endpointEmbedding hXY i then 1 else 0 := by
  simp only [cornerJ, Matrix.of_apply]
  by_cases hval : (j : ℕ) = (i : ℕ)
  · rw [if_pos hval, if_pos]
    exact Fin.ext hval
  · rw [if_neg hval, if_neg]
    intro h
    exact hval (congrArg Fin.val h)

theorem cornerJ_conjTranspose_mul_apply {X Y : ℕ} (hXY : X ≤ Y)
    (A : Matrix (Fin Y) (Fin Y) ℂ) (i : Fin X) (j : Fin Y) :
    ((cornerJ X Y)ᴴ * A) i j = A (endpointEmbedding hXY i) j := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (endpointEmbedding hXY i)]
  · simp [cornerJ_apply_embedding hXY]
  · intro k _ hk
    simp [cornerJ_apply_embedding hXY, hk]
  · intro hk
    exact absurd (Finset.mem_univ _) hk

theorem mul_cornerJ_apply {R : Type*} {X Y : ℕ} (hXY : X ≤ Y)
    (A : Matrix R (Fin Y) ℂ) (i : R) (j : Fin X) :
    (A * cornerJ X Y) i j = A i (endpointEmbedding hXY j) := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (endpointEmbedding hXY j)]
  · simp [cornerJ_apply_embedding hXY]
  · intro k _ hk
    simp [cornerJ_apply_embedding hXY, hk]
  · intro hk
    exact absurd (Finset.mem_univ _) hk

theorem cornerCompression_apply {X Y : ℕ} (hXY : X ≤ Y)
    (A : Matrix (Fin Y) (Fin Y) ℂ) (i j : Fin X) :
    ((cornerJ X Y)ᴴ * A * cornerJ X Y) i j =
      A (endpointEmbedding hXY i) (endpointEmbedding hXY j) := by
  rw [mul_cornerJ_apply hXY ((cornerJ X Y)ᴴ * A) i j,
    cornerJ_conjTranspose_mul_apply hXY]

/-- The range projector of the endpoint inclusion is the diagonal projector
onto the old endpoint coordinates. -/
theorem cornerProjector_apply {X Y : ℕ} (hXY : X ≤ Y)
    (i j : Fin Y) :
    (cornerJ X Y * (cornerJ X Y)ᴴ) i j =
      if (i : ℕ) < X ∧ i = j then 1 else 0 := by
  rw [Matrix.mul_apply]
  by_cases hi : (i : ℕ) < X
  · let iX : Fin X := ⟨i, hi⟩
    have hiemb : endpointEmbedding hXY iX = i := Fin.ext rfl
    rw [Finset.sum_eq_single iX]
    · simp only [Matrix.conjTranspose_apply,
        cornerJ_apply_embedding hXY, hiemb, if_pos, star_one, mul_one]
      by_cases hij : i = j
      · subst j
        simp [hi]
      · simp [hi, hij, Ne.symm hij]
    · intro k _ hk
      have hik : i ≠ endpointEmbedding hXY k := by
        intro heq
        apply hk
        apply Fin.ext
        simpa [iX, endpointEmbedding] using (congrArg Fin.val heq).symm
      simp [Matrix.conjTranspose_apply, cornerJ_apply_embedding hXY, hik]
    · intro hk
      exact absurd (Finset.mem_univ _) hk
  · rw [if_neg (fun h => hi h.1)]
    apply Finset.sum_eq_zero
    intro k _
    have hik : i ≠ endpointEmbedding hXY k := by
      intro heq
      apply hi
      rw [congrArg Fin.val heq]
      exact k.isLt
    simp [cornerJ_apply_embedding hXY, hik]

/-- Corner compression of a forward matrix is again forward. -/
theorem cornerCompression_mem_forwardAlg {X Y : ℕ} (hXY : X ≤ Y)
    (A : forwardAlg Y) :
    (cornerJ X Y)ᴴ * (A : Matrix (Fin Y) (Fin Y) ℂ) * cornerJ X Y ∈
      forwardAlg X := by
  intro j i hji
  rw [cornerCompression_apply hXY]
  exact A.property _ _ hji

/-- A forward matrix has no old-output/new-input block, exactly the condition
needed for multiplicativity of corner compression. -/
theorem forwardAlg_corner_condition {X Y : ℕ} (hXY : X ≤ Y)
    (A : forwardAlg Y) :
    (cornerJ X Y)ᴴ * (A : Matrix (Fin Y) (Fin Y) ℂ) =
      (cornerJ X Y)ᴴ * (A : Matrix (Fin Y) (Fin Y) ℂ) *
        (cornerJ X Y * (cornerJ X Y)ᴴ) := by
  ext i j
  rw [cornerJ_conjTranspose_mul_apply hXY]
  simp only [Matrix.mul_assoc]
  rw [cornerJ_conjTranspose_mul_apply hXY]
  change (A : Matrix (Fin Y) (Fin Y) ℂ)
      (endpointEmbedding hXY i) j =
    ∑ k, (A : Matrix (Fin Y) (Fin Y) ℂ)
      (endpointEmbedding hXY i) k *
        (cornerJ X Y * (cornerJ X Y)ᴴ) k j
  by_cases hj : (j : ℕ) < X
  · let jX : Fin X := ⟨j, hj⟩
    have hjemb : endpointEmbedding hXY jX = j := Fin.ext rfl
    rw [Finset.sum_eq_single j]
    · simp [cornerProjector_apply hXY, hj]
    · intro k _ hk
      simp [cornerProjector_apply hXY, hk]
    · intro hk
      exact absurd (Finset.mem_univ _) hk
  · have hlt : (endpointEmbedding hXY i : ℕ) < (j : ℕ) := by
      simp only [endpointEmbedding]
      omega
    rw [A.property _ _ hlt]
    symm
    apply Finset.sum_eq_zero
    intro k _
    rw [cornerProjector_apply hXY]
    split_ifs with hk
    · have : (j : ℕ) < X := by
        rw [← hk.2]
        exact hk.1
      exact (hj this).elim
    · simp

/-- The manuscript compression `π_XY` as an actual unital complex algebra
homomorphism between the two forward chronology algebras. -/
def forwardCutoffAlgHom {X Y : ℕ} (hXY : X ≤ Y) :
    forwardAlg Y →ₐ[ℂ] forwardAlg X where
  toFun A := ⟨(cornerJ X Y)ᴴ * (A : Matrix (Fin Y) (Fin Y) ℂ) * cornerJ X Y,
    cornerCompression_mem_forwardAlg hXY A⟩
  map_one' := by
    apply Subtype.ext
    exact (forward_corner_compression_hom (cornerJ X Y)
      (cornerJ_isometry hXY)).1
  map_mul' A B := by
    apply Subtype.ext
    exact (forward_corner_compression_hom (cornerJ X Y)
      (cornerJ_isometry hXY)).2.1 A B
        (forwardAlg_corner_condition hXY A)
  map_zero' := by
    apply Subtype.ext
    simp
  map_add' A B := by
    apply Subtype.ext
    exact (forward_corner_compression_hom (cornerJ X Y)
      (cornerJ_isometry hXY)).2.2.1 A B
  commutes' c := by
    apply Subtype.ext
    change (cornerJ X Y)ᴴ *
        (algebraMap ℂ (Matrix (Fin Y) (Fin Y) ℂ) c) *
        cornerJ X Y =
      algebraMap ℂ (Matrix (Fin X) (Fin X) ℂ) c
    rw [show algebraMap ℂ (Matrix (Fin Y) (Fin Y) ℂ) c =
        c • (1 : Matrix (Fin Y) (Fin Y) ℂ) by
          simp [Algebra.smul_def],
      show algebraMap ℂ (Matrix (Fin X) (Fin X) ℂ) c =
        c • (1 : Matrix (Fin X) (Fin X) ℂ) by
          simp [Algebra.smul_def]]
    rw [(forward_corner_compression_hom (cornerJ X Y)
      (cornerJ_isometry hXY)).2.2.2]
    rw [(forward_corner_compression_hom (cornerJ X Y)
      (cornerJ_isometry hXY)).1]

@[simp] theorem forwardCutoffAlgHom_apply {X Y : ℕ} (hXY : X ≤ Y)
    (A : forwardAlg Y) :
    ((forwardCutoffAlgHom hXY A : forwardAlg X) :
        Matrix (Fin X) (Fin X) ℂ) =
      (cornerJ X Y)ᴴ * (A : Matrix (Fin Y) (Fin Y) ℂ) * cornerJ X Y := rfl

/-- Multiplication histories are forward triangular. -/
theorem peanoL_mem_forwardAlg (X a : ℕ) : peanoL X a ∈ forwardAlg X := by
  intro j i hji
  simp only [peanoL, Matrix.of_apply]
  rw [if_neg]
  intro heq
  have ha : 1 ≤ a := by
    by_contra h
    have : a = 0 := by omega
    subst a
    simp at heq
  have := Nat.le_mul_of_pos_left ((i : ℕ) + 1) ha
  omega

theorem zetaX_mem_forwardAlg (X : ℕ) : zetaX X ∈ forwardAlg X := by
  exact fun j i hji => (zeta_incidence (X := X)).2.2.2.1 j i hji

theorem diagFn_mem_forwardAlg (X : ℕ) (f : ℕ → ℂ) :
    diagFn X f ∈ forwardAlg X := by
  intro j i hji
  exact Matrix.diagonal_apply_ne _ (by omega)

theorem logZop_mem_forwardAlg (X : ℕ) : logZop X ∈ forwardAlg X := by
  unfold logZop
  apply sum_mem
  intro n _
  exact (forwardAlg X).smul_mem (peanoL_mem_forwardAlg X n) _

/-- The terminating inverse polynomial for the unipotent zeta history. -/
def zetaInversePolynomial (X : ℕ) : Matrix (Fin X) (Fin X) ℂ :=
  ∑ k ∈ Finset.range X, (-(zetaX X - 1)) ^ k

theorem zetaInversePolynomial_mem_forwardAlg (X : ℕ) :
    zetaInversePolynomial X ∈ forwardAlg X := by
  unfold zetaInversePolynomial
  apply sum_mem
  intro k _
  apply pow_mem
  exact neg_mem (sub_mem (zetaX_mem_forwardAlg X) (one_mem _))

theorem zetaInversePolynomial_isInverse (X : ℕ) :
    zetaX X * zetaInversePolynomial X = 1 ∧
      zetaInversePolynomial X * zetaX X = 1 := by
  have hnil : (-(zetaX X - 1)) ^ X = 0 := by
    rw [neg_pow, (zeta_incidence (X := X)).2.2.2.2, mul_zero]
  have h := (ar_finite_euler (X := X + 1) (by omega)).1
    (-(zetaX X - 1)) X hnil
  simpa [zetaInversePolynomial] using h

theorem peanoL_zero_of_cutoff_lt {X a : ℕ} (hXa : X < a) :
    peanoL X a = 0 := by
  ext j i
  simp only [peanoL, Matrix.of_apply, Matrix.zero_apply]
  rw [if_neg]
  intro heq
  have ha : a ≤ a * ((i : ℕ) + 1) :=
    Nat.le_mul_of_pos_right a (by omega)
  omega

/-- Every endpoint-diagonal history is exactly cutoff natural. -/
theorem diagFn_cutoff {X Y : ℕ} (hXY : X ≤ Y) (f : ℕ → ℂ) :
    (cornerJ X Y)ᴴ * diagFn Y f * cornerJ X Y = diagFn X f := by
  ext i j
  rw [cornerCompression_apply hXY]
  simp [diagFn, endpointEmbedding, Matrix.diagonal_apply, Fin.ext_iff]

/-- The zeta incidence history is exactly cutoff natural. -/
theorem zetaX_cutoff {X Y : ℕ} (hXY : X ≤ Y) :
    (cornerJ X Y)ᴴ * zetaX Y * cornerJ X Y = zetaX X := by
  simpa [zetaX] using corner_compress hXY
    (fun j i => if i + 1 ∣ j + 1 then (1 : ℂ) else 0)

/-- The terminating logarithm history is exactly cutoff natural. -/
theorem logZop_cutoff {X Y : ℕ} (hXY : X ≤ Y) :
    (cornerJ X Y)ᴴ * logZop Y * cornerJ X Y = logZop X := by
  rw [logZop, Matrix.mul_sum, Matrix.sum_mul]
  have hsub : Finset.Icc 2 X ⊆ Finset.Icc 2 Y := by
    intro n hn
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn).1,
      le_trans (Finset.mem_Icc.mp hn).2 hXY⟩
  rw [← Finset.sum_subset hsub]
  · apply Finset.sum_congr rfl
    intro n hn
    rw [Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    exact (record_cutoff hXY n).2.2
  · intro n hnY hnX
    have hnlt : X < n := by
      have hn2 := (Finset.mem_Icc.mp hnY).1
      by_contra h
      exact hnX (Finset.mem_Icc.mpr ⟨hn2, by omega⟩)
    rw [Matrix.mul_smul, Matrix.smul_mul,
      (record_cutoff hXY n).2.2, peanoL_zero_of_cutoff_lt hnlt,
      smul_zero]

/-- The terminating inverse of zeta is exactly cutoff natural. -/
theorem zetaInversePolynomial_cutoff {X Y : ℕ} (hXY : X ≤ Y) :
    (cornerJ X Y)ᴴ * zetaInversePolynomial Y * cornerJ X Y =
      zetaInversePolynomial X := by
  let ZY : forwardAlg Y := ⟨zetaX Y, zetaX_mem_forwardAlg Y⟩
  let IY : forwardAlg Y :=
    ⟨zetaInversePolynomial Y, zetaInversePolynomial_mem_forwardAlg Y⟩
  let ZX : forwardAlg X := ⟨zetaX X, zetaX_mem_forwardAlg X⟩
  let IX : forwardAlg X :=
    ⟨zetaInversePolynomial X, zetaInversePolynomial_mem_forwardAlg X⟩
  have hmapZ : forwardCutoffAlgHom hXY ZY = ZX := by
    apply Subtype.ext
    exact zetaX_cutoff hXY
  have hleft : ZX * forwardCutoffAlgHom hXY IY = 1 := by
    rw [← hmapZ, ← map_mul]
    rw [show ZY * IY = 1 by
      apply Subtype.ext
      exact (zetaInversePolynomial_isInverse Y).1]
    exact map_one (forwardCutoffAlgHom hXY)
  have hIXright : IX * ZX = 1 := by
    apply Subtype.ext
    exact (zetaInversePolynomial_isInverse X).2
  have heq : forwardCutoffAlgHom hXY IY = IX := by
    calc
      forwardCutoffAlgHom hXY IY = 1 * forwardCutoffAlgHom hXY IY := by simp
      _ = (IX * ZX) * forwardCutoffAlgHom hXY IY := by rw [hIXright]
      _ = IX * (ZX * forwardCutoffAlgHom hXY IY) := by rw [mul_assoc]
      _ = IX := by rw [hleft, mul_one]
  exact congrArg Subtype.val heq

/-- The logarithmic commutator is exactly cutoff natural. -/
theorem countLog_logZop_commutator_cutoff {X Y : ℕ} (hXY : X ≤ Y) :
    (cornerJ X Y)ᴴ *
        (countLog Y * logZop Y - logZop Y * countLog Y) *
        cornerJ X Y =
      countLog X * logZop X - logZop X * countLog X := by
  let HY : forwardAlg Y :=
    ⟨countLog Y, diagFn_mem_forwardAlg Y _⟩
  let LY : forwardAlg Y := ⟨logZop Y, logZop_mem_forwardAlg Y⟩
  have hH : forwardCutoffAlgHom hXY HY =
      ⟨countLog X, diagFn_mem_forwardAlg X _⟩ := by
    apply Subtype.ext
    exact diagFn_cutoff hXY _
  have hL : forwardCutoffAlgHom hXY LY =
      ⟨logZop X, logZop_mem_forwardAlg X⟩ := by
    apply Subtype.ext
    exact logZop_cutoff hXY
  change ((forwardCutoffAlgHom hXY (HY * LY - LY * HY) : forwardAlg X) :
      Matrix (Fin X) (Fin X) ℂ) = _
  rw [map_sub, map_mul, map_mul, hH, hL]
  rfl

/-- Complete exact arithmetic-cutoff packet: the algebra map, the three
record generators, zeta/inverse/logarithm/commutator, arbitrary diagonal
functional histories, and arbitrary finite forward words. -/
theorem forward_arithmetic_cutoff_naturality {X Y : ℕ} (hXY : X ≤ Y) :
    (forwardCutoffAlgHom hXY (1 : forwardAlg Y) = 1) ∧
    ((cornerJ X Y)ᴴ * recS Y * cornerJ X Y = recS X) ∧
    ((cornerJ X Y)ᴴ * countN Y * cornerJ X Y = countN X) ∧
    (∀ a, (cornerJ X Y)ᴴ * peanoL Y a * cornerJ X Y = peanoL X a) ∧
    ((cornerJ X Y)ᴴ * zetaX Y * cornerJ X Y = zetaX X) ∧
    ((cornerJ X Y)ᴴ * zetaInversePolynomial Y * cornerJ X Y =
      zetaInversePolynomial X) ∧
    ((cornerJ X Y)ᴴ * logZop Y * cornerJ X Y = logZop X) ∧
    ((cornerJ X Y)ᴴ *
        (countLog Y * logZop Y - logZop Y * countLog Y) * cornerJ X Y =
      countLog X * logZop X - logZop X * countLog X) ∧
    (∀ f, (cornerJ X Y)ᴴ * diagFn Y f * cornerJ X Y = diagFn X f) ∧
    (∀ l : List (forwardAlg Y),
      forwardCutoffAlgHom hXY l.prod =
        (l.map (forwardCutoffAlgHom hXY)).prod) := by
  refine ⟨map_one _, (record_cutoff hXY 1).1, ?_, ?_,
    zetaX_cutoff hXY, zetaInversePolynomial_cutoff hXY,
    logZop_cutoff hXY, countLog_logZop_commutator_cutoff hXY,
    diagFn_cutoff hXY, ?_⟩
  · change (cornerJ X Y)ᴴ *
        diagFn Y (fun n => (n : ℂ)) * cornerJ X Y =
      diagFn X (fun n => (n : ℂ))
    exact diagFn_cutoff hXY (fun n => (n : ℂ))
  · intro a
    exact (record_cutoff hXY a).2.2
  · intro l
    exact map_list_prod (forwardCutoffAlgHom hXY) l

end ArithmeticForwardCutoffNaturality
end NCG
