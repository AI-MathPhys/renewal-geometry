/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Upstream.PointerAlgebra

/-!
# The interaction-complete stable-pointer dissipator

Clauses (i)–(iii) of Theorem `thm:stable-pointer-selection`
(`manuscripts/renewal_emergence/renewal_emergence.tex`) at the generator level, in the
finite-dimensional matrix model.

For a family `A : m → Matrix E E ℂ` of self-adjoint monitoring
generators, the stable-pointer dissipator is

`ℒ(X) = −½ ∑_j [A_j, [A_j, X]]`  (`dissipator`).

* `dissipator_orthogonal_invariant` — clause (i): `ℒ` is unchanged
  under a real orthogonal change of the generating family;
* `dissipator_one`, `trace_dissipator`, `hsInner_dissipator_symm` —
  clause (ii) at the generator level: `ℒ(1) = 0` (unitality),
  `Tr ℒ(X) = 0` (trace preservation), and Hilbert–Schmidt
  self-adjointness `⟪ℒX, Y⟫₂ = ⟪X, ℒY⟫₂`;
* `hsInner_dissipator_self` — the dissipation identity
  `−⟪X, ℒX⟫₂ = ½ ∑_j ‖[A_j, X]‖₂²`;
* `dissipator_eq_zero_iff` — clause (iii) at the generator level:
  `ℒX = 0` iff `X` commutes with every generator;
* `dissipator_eq_zero_iff_mem_stable` — when the generators span the
  coefficient algebra's self-adjoint part (with the identity), the
  fixed points are exactly the nondemolition stable algebra
  `ℱ_E = 𝒞_E(ℋ)'`.

The semigroup packaging of clauses (ii)/(iv) — `D_t = e^{tℒ}` is a
norm-continuous UCP semigroup converging to the trace-preserving
conditional expectation onto `ℱ_E` — is the finite-dimensional
spectral calculus of the self-adjoint negative-semidefinite `ℒ` and
is not formalized here.
-/

namespace NCG.Upstream

open Matrix

variable {E : Type*} [Fintype E] [DecidableEq E]

/-- The commutator. -/
def comm (A X : Matrix E E ℂ) : Matrix E E ℂ := A * X - X * A

theorem comm_one (A : Matrix E E ℂ) : comm A 1 = 0 := by
  simp [comm]

omit [DecidableEq E] in
theorem comm_smul_right (A : Matrix E E ℂ) (c : ℂ)
    (X : Matrix E E ℂ) : comm A (c • X) = c • comm A X := by
  simp [comm, smul_sub]

omit [DecidableEq E] in
theorem comm_smul_left (c : ℂ) (A X : Matrix E E ℂ) :
    comm (c • A) X = c • comm A X := by
  simp [comm, smul_sub]

omit [DecidableEq E] in
theorem comm_sum_left {m : Type*} (s : Finset m)
    (A : m → Matrix E E ℂ) (X : Matrix E E ℂ) :
    comm (∑ j ∈ s, A j) X = ∑ j ∈ s, comm (A j) X := by
  simp [comm, Finset.sum_mul, Finset.mul_sum, Finset.sum_sub_distrib]

omit [DecidableEq E] in
theorem comm_sum_right {m : Type*} (s : Finset m)
    (A : Matrix E E ℂ) (X : m → Matrix E E ℂ) :
    comm A (∑ j ∈ s, X j) = ∑ j ∈ s, comm A (X j) := by
  simp [comm, Finset.sum_mul, Finset.mul_sum, Finset.sum_sub_distrib]

omit [DecidableEq E] in
/-- The commutator with a Hermitian generator anti-commutes with the
adjoint: `[A, X]ᴴ = −[A, Xᴴ]`. -/
theorem comm_conjTranspose {A : Matrix E E ℂ} (hA : Aᴴ = A)
    (X : Matrix E E ℂ) : (comm A X)ᴴ = -(comm A Xᴴ) := by
  simp [comm, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hA]

omit [DecidableEq E] in
/-- Trace adjointness of the commutator:
`Tr([A,W]·Y) = −Tr(W·[A,Y])`. -/
theorem trace_comm_mul (A W Y : Matrix E E ℂ) :
    (comm A W * Y).trace = -(W * comm A Y).trace := by
  simp only [comm, Matrix.sub_mul, Matrix.mul_sub]
  rw [Matrix.trace_sub, Matrix.trace_sub]
  have h1 : ((A * W) * Y).trace = (W * (Y * A)).trace := by
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  have h2 : ((W * A) * Y).trace = (W * (A * Y)).trace := by
    rw [Matrix.mul_assoc]
  rw [h1, h2]
  ring

/-- **The stable-pointer dissipator**
`ℒ(X) = −½ ∑_j [A_j, [A_j, X]]`. -/
noncomputable def dissipator {m : Type*} [Fintype m]
    (A : m → Matrix E E ℂ) (X : Matrix E E ℂ) : Matrix E E ℂ :=
  (-(1 / 2) : ℂ) • ∑ j, comm (A j) (comm (A j) X)

omit [DecidableEq E] in
/-- **Theorem `thm:stable-pointer-selection` (i)**: the dissipator is
independent of the chosen real orthonormal generating family — a
real orthogonal recombination leaves it unchanged. -/
theorem dissipator_orthogonal_invariant {m : Type*} [Fintype m]
    [DecidableEq m] (A B : m → Matrix E E ℂ) (O : m → m → ℝ)
    (horth : ∀ i j, ∑ k, O k i * O k j = if i = j then (1 : ℝ) else 0)
    (hB : ∀ k, B k = ∑ j, ((O k j : ℝ) : ℂ) • A j)
    (X : Matrix E E ℂ) :
    dissipator B X = dissipator A X := by
  unfold dissipator
  congr 1
  have hkey : ∀ k, comm (B k) (comm (B k) X)
      = ∑ i, ∑ j, (((O k i : ℝ) : ℂ) * ((O k j : ℝ) : ℂ))
          • comm (A i) (comm (A j) X) := by
    intro k
    rw [hB k]
    have hinner : comm (∑ j, ((O k j : ℝ) : ℂ) • A j) X
        = ∑ j, ((O k j : ℝ) : ℂ) • comm (A j) X := by
      rw [comm_sum_left]
      exact Finset.sum_congr rfl fun j _ => comm_smul_left _ _ _
    rw [hinner, comm_sum_left]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [comm_smul_left, comm_sum_right, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [comm_smul_right, smul_smul]
  rw [Finset.sum_congr rfl fun k _ => hkey k]
  rw [Finset.sum_comm]
  have hswap : ∀ i, ∑ k, ∑ j, (((O k i : ℝ) : ℂ) * ((O k j : ℝ) : ℂ))
      • comm (A i) (comm (A j) X)
      = ∑ j, (((∑ k, O k i * O k j : ℝ)) : ℂ)
          • comm (A i) (comm (A j) X) := by
    intro i
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_smul]
    congr 1
    push_cast
    rfl
  rw [Finset.sum_congr rfl fun i _ => hswap i]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · rw [horth i i, if_pos rfl]
    push_cast
    rw [one_smul]
  · intro j _ hj
    rw [horth i j, if_neg (Ne.symm hj)]
    push_cast
    rw [zero_smul]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- **Clause (ii), unitality of the generator**: `ℒ(1) = 0`. -/
theorem dissipator_one {m : Type*} [Fintype m]
    (A : m → Matrix E E ℂ) : dissipator A (1 : Matrix E E ℂ) = 0 := by
  unfold dissipator
  rw [Finset.sum_eq_zero fun j _ => by rw [comm_one]; simp [comm]]
  rw [smul_zero]

omit [DecidableEq E] in
/-- **Clause (ii), trace preservation of the generator**:
`Tr ℒ(X) = 0`. -/
theorem trace_dissipator {m : Type*} [Fintype m]
    (A : m → Matrix E E ℂ) (X : Matrix E E ℂ) :
    (dissipator A X).trace = 0 := by
  classical
  unfold dissipator
  rw [Matrix.trace_smul, Matrix.trace_sum]
  have h1 : ∀ j, (comm (A j) (comm (A j) X)).trace = 0 := by
    intro j
    have h2 := trace_comm_mul (A j) (comm (A j) X) 1
    rw [Matrix.mul_one, comm_one] at h2
    simpa using h2
  rw [Finset.sum_congr rfl fun j _ => h1 j]
  simp

omit [DecidableEq E] in
theorem comm_neg_right (A X : Matrix E E ℂ) :
    comm A (-X) = -comm A X := by
  simp only [comm, Matrix.mul_neg, Matrix.neg_mul]
  abel

omit [DecidableEq E] in
/-- The double commutator with a Hermitian generator commutes with
the adjoint. -/
theorem comm_comm_conjTranspose {A : Matrix E E ℂ} (hA : Aᴴ = A)
    (X : Matrix E E ℂ) :
    (comm A (comm A X))ᴴ = comm A (comm A Xᴴ) := by
  rw [comm_conjTranspose hA, comm_conjTranspose hA, comm_neg_right,
    neg_neg]

omit [DecidableEq E] in
/-- Double adjointness under the trace pairing:
`Tr(Xᴴ · [A,[A,Y]]) = Tr([A,[A,Xᴴᴴ… ]])` — the workhorse identity
`Tr(W · [A,[A,Y]]) = Tr([A,[A,W]] · Y)`. -/
theorem trace_mul_comm_comm (A W Y : Matrix E E ℂ) :
    (W * comm A (comm A Y)).trace
      = (comm A (comm A W) * Y).trace := by
  have h1 : (W * comm A (comm A Y)).trace
      = -(comm A W * comm A Y).trace := by
    rw [trace_comm_mul A W (comm A Y), neg_neg]
  have h3 : (comm A (comm A W) * Y).trace
      = -(comm A W * comm A Y).trace := by
    have h4 := trace_comm_mul A (comm A W) Y
    rw [h4]
  rw [h1, h3]

omit [DecidableEq E] in
/-- **Clause (ii), Hilbert–Schmidt self-adjointness**: for Hermitian
generators, `Tr((ℒX)ᴴ Y) = Tr(Xᴴ ℒY)`. -/
theorem hsInner_dissipator_symm {m : Type*} [Fintype m]
    {A : m → Matrix E E ℂ} (hA : ∀ j, (A j)ᴴ = A j)
    (X Y : Matrix E E ℂ) :
    ((dissipator A X)ᴴ * Y).trace = (Xᴴ * dissipator A Y).trace := by
  unfold dissipator
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sum]
  have hc : (star (-(1 / 2) : ℂ)) = -(1 / 2) := by
    rw [Complex.star_def, map_neg, map_div₀, map_one, map_ofNat]
  rw [hc]
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul,
    Matrix.trace_smul]
  congr 1
  rw [Matrix.sum_mul, Matrix.mul_sum, Matrix.trace_sum,
    Matrix.trace_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [comm_comm_conjTranspose (hA j)]
  exact (trace_mul_comm_comm (A j) Xᴴ Y).symm

omit [DecidableEq E] in
/-- **The dissipation identity**:
`Tr(Xᴴ ℒX) = −½ ∑_j Tr([A_j,X]ᴴ [A_j,X])`. -/
theorem hsInner_dissipator_self {m : Type*} [Fintype m]
    {A : m → Matrix E E ℂ} (hA : ∀ j, (A j)ᴴ = A j)
    (X : Matrix E E ℂ) :
    (Xᴴ * dissipator A X).trace
      = -(1 / 2) * ∑ j, ((comm (A j) X)ᴴ * comm (A j) X).trace := by
  unfold dissipator
  rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  congr 1
  rw [Matrix.mul_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 : (Xᴴ * comm (A j) (comm (A j) X)).trace
      = -(comm (A j) Xᴴ * comm (A j) X).trace := by
    rw [trace_comm_mul (A j) Xᴴ (comm (A j) X), neg_neg]
  have h3 : comm (A j) Xᴴ = -((comm (A j) X)ᴴ) := by
    rw [comm_conjTranspose (hA j), neg_neg]
  rw [h1, h3, Matrix.neg_mul, Matrix.trace_neg, neg_neg]

omit [DecidableEq E] in
/-- The Frobenius pairing detects vanishing:
`Tr(CᴴC) = 0 → C = 0`. -/
theorem eq_zero_of_trace_conjTranspose_mul_self
    {C : Matrix E E ℂ} (h : (Cᴴ * C).trace = 0) : C = 0 := by
  have h1 : (Cᴴ * C).trace
      = ((∑ d : E, ∑ i : E, Complex.normSq (C i d) : ℝ) : ℂ) := by
    rw [Matrix.trace]
    push_cast
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Matrix.diag_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.conjTranspose_apply, Complex.star_def]
    rw [← Complex.normSq_eq_conj_mul_self]
  rw [h1] at h
  have h2 : (∑ d : E, ∑ i : E, Complex.normSq (C i d) : ℝ) = 0 := by
    exact_mod_cast h
  have h3 : ∀ d ∈ Finset.univ, ∀ i ∈ Finset.univ,
      Complex.normSq (C i d) = 0 := by
    intro d hd
    have h4 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun d _ => Finset.sum_nonneg fun i _ =>
        Complex.normSq_nonneg _)).mp h2 d hd
    intro i hi
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => Complex.normSq_nonneg _)).mp h4 i hi
  ext i d
  have h5 := h3 d (Finset.mem_univ d) i (Finset.mem_univ i)
  simpa [Complex.normSq_eq_zero] using h5

omit [DecidableEq E] in
/-- **Theorem `thm:stable-pointer-selection` (iii), generator
level**: the dissipator kills `X` exactly when `X` commutes with
every monitoring generator. -/
theorem dissipator_eq_zero_iff {m : Type*} [Fintype m]
    {A : m → Matrix E E ℂ} (hA : ∀ j, (A j)ᴴ = A j)
    (X : Matrix E E ℂ) :
    dissipator A X = 0 ↔ ∀ j, comm (A j) X = 0 := by
  constructor
  · intro h
    have h1 : (Xᴴ * dissipator A X).trace = 0 := by
      rw [h, Matrix.mul_zero, Matrix.trace_zero]
    rw [hsInner_dissipator_self hA] at h1
    have h2 : ∑ j, ((comm (A j) X)ᴴ * comm (A j) X).trace = 0 := by
      have h3 : (-(1 / 2) : ℂ) ≠ 0 := by norm_num
      exact (mul_eq_zero.mp h1).resolve_left h3
    -- pass to real Frobenius norms
    have h4 : ∀ j, ((comm (A j) X)ᴴ * comm (A j) X).trace
        = ((∑ d : E, ∑ i : E,
            Complex.normSq (comm (A j) X i d) : ℝ) : ℂ) := by
      intro j
      rw [Matrix.trace]
      push_cast
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [Matrix.diag_apply, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Matrix.conjTranspose_apply, Complex.star_def,
        ← Complex.normSq_eq_conj_mul_self]
    rw [Finset.sum_congr rfl fun j _ => h4 j] at h2
    have h5 : (∑ j, (∑ d : E, ∑ i : E,
        Complex.normSq (comm (A j) X i d) : ℝ)) = 0 := by
      exact_mod_cast h2
    intro j
    have h6 := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => Finset.sum_nonneg fun d _ =>
        Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _)).mp h5
      j (Finset.mem_univ j)
    refine eq_zero_of_trace_conjTranspose_mul_self ?_
    rw [Matrix.trace]
    rw [show (0 : ℂ) = ((0 : ℝ) : ℂ) from by norm_num, ← h6]
    push_cast
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Matrix.diag_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.conjTranspose_apply, Complex.star_def,
      ← Complex.normSq_eq_conj_mul_self]
  · intro h
    unfold dissipator
    rw [Finset.sum_eq_zero fun j _ => by rw [h j]; simp [comm]]
    rw [smul_zero]

/-- **Theorem `thm:stable-pointer-selection` (iii)**: when the
monitoring generators together with the identity span the coefficient
algebra's slices, the fixed points of the dissipator are exactly the
nondemolition stable algebra `ℱ_E = 𝒞_E(ℋ)'`. -/
theorem dissipator_eq_zero_iff_mem_stable
    {P ι m : Type*} [Finite P] [Fintype m]
    (H : ι → Matrix (P × E) (P × E) ℂ) (hH : ∀ ν, (H ν)ᴴ = H ν)
    {A : m → Matrix E E ℂ} (hA : ∀ j, (A j)ᴴ = A j)
    (hmem : ∀ j, A j ∈ coeffAlgebra (P := P) H)
    (hgen : ∀ (ν : ι) (a b : P), ∃ (c : ℂ) (f : m → ℂ),
      slice a b (H ν) = c • 1 + ∑ j, f j • A j)
    (X : Matrix E E ℂ) :
    dissipator A X = 0 ↔ X ∈ stableAlgebra (P := P) H := by
  classical
  cases nonempty_fintype P
  rw [dissipator_eq_zero_iff hA,
    mem_stableAlgebra_iff (P := P) H hH]
  constructor
  · intro h ν
    rw [commute_onePE_iff_slice]
    intro a b
    have hcommA : ∀ j, X * A j = A j * X := by
      intro j
      have h2 : A j * X - X * A j = 0 := h j
      exact (sub_eq_zero.mp h2).symm
    obtain ⟨c, f, hcf⟩ := hgen ν a b
    rw [hcf, Matrix.mul_add, Matrix.add_mul]
    congr 1
    · rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
        Matrix.one_mul]
    · rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.mul_smul, Matrix.smul_mul, hcommA j]
  · intro h j
    have h3 : X ∈ stableAlgebra (P := P) H :=
      (mem_stableAlgebra_iff (P := P) H hH X).mpr h
    rw [stableAlgebra, Subalgebra.mem_centralizer_iff] at h3
    have h4 : A j * X = X * A j := h3 (A j) (hmem j)
    rw [comm, h4, sub_self]

end NCG.Upstream
