/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Typed singlet–adjoint covariance decomposition
  (`thm:SM-typed-occurrence-RN`, Gran-Tensor manuscript)

The remaining boxed clause of the typed Radon–Nikodym
reduction: every positive `SU(4)`-covariant typed
occurrence covariance on `M₄(ℂ) ⊗ ℂ⁸` has the unique form

  `ℚ_typ = P_𝟏 ⊗ G_Φ + (1/15) P_𝟏𝟓 ⊗ G_Ω`,

with `G_Φ, G_Ω ⪰ 0` — conjugation on `M₄(ℂ)` is the
multiplicity-free representation `𝟏 ⊕ 𝟏𝟓` and Schur's
lemma gives the block form and its uniqueness.

The Schur step is carried out with explicitly chosen
unitaries only: the diagonal fourth-root units `dU i`
separate the matrix-unit weight lines, the permutation
matrices act transitively on them and on the diagonal
sector, and one rational Pythagorean rotation
`R = [[3/5,4/5],[−4/5,3/5]] ⊕ I₂` ties the off-diagonal
eigenvalue to the diagonal one — no Haar integration and
no irrational entries anywhere.

* `equivariant_endo_scalar`: every conjugation-equivariant
  linear endomorphism of `M₄(ℂ)` is
  `α P_𝟏 + β P_𝟏𝟓`.
* `sm_typed_occurrence_su4_covariance`: the boxed
  decomposition with `G_Φ, G_Ω ⪰ 0` and uniqueness, for
  every positive covariance on the eight-dimensional
  typed carrier.
-/

open Matrix
open scoped ComplexOrder

namespace NCG
namespace TypedSU4

/-- The `4×4` complex matrices carrying the conjugation
representation. -/
abbrev M4 : Type := Matrix (Fin 4) (Fin 4) ℂ

/-- Diagonal fourth-root unit: `i` in slot `k = i`, `1`
elsewhere. -/
noncomputable def dval (i k : Fin 4) : ℂ :=
  if k = i then Complex.I else 1

/-- The diagonal unitary `dU i`. -/
noncomputable def dU (i : Fin 4) : M4 :=
  Matrix.diagonal (dval i)

private theorem dval_mul_star_self (i k : Fin 4) :
    dval i k * star (dval i k) = 1 := by
  unfold dval
  by_cases hk : k = i
  · rw [if_pos hk, Complex.star_def, Complex.conj_I]
    ring_nf
    rw [Complex.I_sq]
    ring
  · rw [if_neg hk]
    simp

private theorem dU_unitary (i : Fin 4) :
    (dU i)ᴴ * dU i = 1 := by
  unfold dU
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  rw [show (fun k => star (dval i) k * dval i k)
      = fun _ => (1 : ℂ) from funext fun k => by
    rw [Pi.star_apply, mul_comm]
    exact dval_mul_star_self i k]
  exact Matrix.diagonal_one

private theorem diag_conj_entry (d : Fin 4 → ℂ) (X : M4)
    (p q : Fin 4) :
    (Matrix.diagonal d * X * (Matrix.diagonal d)ᴴ) p q
      = d p * X p q * star (d q) := by
  rw [Matrix.diagonal_conjTranspose, Matrix.mul_diagonal,
    Matrix.diagonal_mul, Pi.star_apply]

private theorem dU_conj_single (i a b : Fin 4) :
    dU i * Matrix.single a b (1 : ℂ) * (dU i)ᴴ
      = (dval i a * star (dval i b)) •
        Matrix.single a b (1 : ℂ) := by
  unfold dU
  ext p q
  rw [diag_conj_entry, Matrix.smul_apply,
    Matrix.single_apply]
  by_cases hpq : a = p ∧ b = q
  · rw [if_pos hpq]
    obtain ⟨h1, h2⟩ := hpq
    rw [← h1, ← h2, smul_eq_mul]
    ring
  · rw [if_neg hpq, smul_zero, mul_zero, zero_mul]

private theorem dU_conj_diagonal (i : Fin 4) (g : Fin 4 → ℂ) :
    dU i * Matrix.diagonal g * (dU i)ᴴ = Matrix.diagonal g := by
  unfold dU
  ext p q
  rw [diag_conj_entry, Matrix.diagonal_apply]
  by_cases h : p = q
  · rw [if_pos h, h]
    calc dval i q * g q * star (dval i q)
        = g q * (dval i q * star (dval i q)) := by ring
      _ = g q := by rw [dval_mul_star_self, mul_one]
  · rw [if_neg h, mul_zero, zero_mul]

/-- Permutation matrix `P σ` with `(P σ) p q = 1 ↔ p = σ q`. -/
def permMat (σ : Equiv.Perm (Fin 4)) : M4 :=
  Matrix.of fun p q => if p = σ q then 1 else 0

private theorem permMat_mul_apply (σ : Equiv.Perm (Fin 4))
    (X : M4) (p q : Fin 4) :
    (permMat σ * X) p q = X (σ.symm p) q := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (σ.symm p) (fun r _ hr => by
      rw [show permMat σ p r = 0 from if_neg (fun h => by
        apply hr
        rw [← Equiv.symm_apply_apply σ r, ← h]), zero_mul])
    (fun h => absurd (Finset.mem_univ _) h)]
  rw [show permMat σ p (σ.symm p) = 1 from
    if_pos (Equiv.apply_symm_apply σ p).symm, one_mul]

private theorem mul_permMat_apply (σ : Equiv.Perm (Fin 4))
    (X : M4) (p q : Fin 4) :
    (X * permMat σ) p q = X p (σ q) := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (σ q) (fun r _ hr => by
      rw [show permMat σ r q = 0 from if_neg hr, mul_zero])
    (fun h => absurd (Finset.mem_univ _) h)]
  rw [show permMat σ (σ q) q = 1 from if_pos rfl, mul_one]

private theorem permMat_conjTranspose (σ : Equiv.Perm (Fin 4)) :
    (permMat σ)ᴴ = permMat σ.symm := by
  ext p q
  rw [Matrix.conjTranspose_apply]
  unfold permMat
  rw [Matrix.of_apply, Matrix.of_apply]
  by_cases h : q = σ p
  · rw [if_pos h, if_pos (by rw [h, Equiv.symm_apply_apply])]
    exact star_one ℂ
  · rw [if_neg h, if_neg (fun hc => h (by
      rw [hc, Equiv.apply_symm_apply])), star_zero]

private theorem permMat_unitary (σ : Equiv.Perm (Fin 4)) :
    (permMat σ)ᴴ * permMat σ = 1 := by
  rw [permMat_conjTranspose]
  ext p q
  rw [permMat_mul_apply, Equiv.symm_symm]
  unfold permMat
  rw [Matrix.of_apply, Matrix.one_apply]
  by_cases h : p = q
  · rw [if_pos (congrArg σ h), if_pos h]
  · rw [if_neg (fun hc => h (σ.injective hc)), if_neg h]

private theorem permMat_conj_apply (σ : Equiv.Perm (Fin 4))
    (X : M4) (p q : Fin 4) :
    (permMat σ * X * (permMat σ)ᴴ) p q
      = X (σ.symm p) (σ.symm q) := by
  rw [permMat_conjTranspose, mul_permMat_apply,
    permMat_mul_apply]

private theorem permMat_conj_single (σ : Equiv.Perm (Fin 4))
    (a b : Fin 4) :
    permMat σ * Matrix.single a b (1 : ℂ) * (permMat σ)ᴴ
      = Matrix.single (σ a) (σ b) (1 : ℂ) := by
  ext p q
  rw [permMat_conj_apply, Matrix.single_apply,
    Matrix.single_apply]
  by_cases h : a = σ.symm p ∧ b = σ.symm q
  · rw [if_pos h, if_pos ⟨by rw [h.1, Equiv.apply_symm_apply],
      by rw [h.2, Equiv.apply_symm_apply]⟩]
  · rw [if_neg h, if_neg (fun hc => h ⟨by
      rw [← hc.1, Equiv.symm_apply_apply], by
      rw [← hc.2, Equiv.symm_apply_apply]⟩)]

/-- The rational Pythagorean rotation
`R = [[3/5,4/5],[−4/5,3/5]] ⊕ I₂`. -/
noncomputable def pythR : M4 :=
  !![3/5, 4/5, 0, 0;
     -(4/5), 3/5, 0, 0;
     0, 0, 1, 0;
     0, 0, 0, 1]

private theorem pythR_unitary : pythRᴴ * pythR = 1 := by
  ext p q
  rw [Matrix.mul_apply, Fin.sum_univ_four]
  fin_cases p <;> fin_cases q <;>
    simp [pythR, Matrix.conjTranspose_apply,
      Matrix.cons_val] <;> norm_num [Complex.ext_iff]

/-- `Ad_R (E₀₀ − E₁₁) = −(7/25)(E₀₀−E₁₁) − (24/25)(E₀₁+E₁₀)`:
the rational rotation mixes the diagonal and off-diagonal
sectors. -/
private theorem pythR_conj_diag :
    pythR * (Matrix.single 0 0 (1 : ℂ)
        - Matrix.single 1 1 (1 : ℂ)) * pythRᴴ
      = (-(7/25) : ℂ) • (Matrix.single 0 0 (1 : ℂ)
          - Matrix.single 1 1 (1 : ℂ))
        + (-(24/25) : ℂ) • (Matrix.single 0 1 (1 : ℂ)
          + Matrix.single 1 0 (1 : ℂ)) := by
  ext p q
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_apply, Fin.sum_univ_four]
  fin_cases p <;> fin_cases q <;>
    simp [pythR, Matrix.conjTranspose_apply,
      Matrix.cons_val] <;> norm_num [Complex.ext_iff]

section EquivariantEndo

/-- Conjugation equivariance under every unitary. -/
def Equivariant (T : M4 →ₗ[ℂ] M4) : Prop :=
  ∀ U : M4, Uᴴ * U = 1 → ∀ X, T (U * X * Uᴴ) = U * T X * Uᴴ

variable (T : M4 →ₗ[ℂ] M4)

private theorem resolve_factor {c x : ℂ} (hc : c ≠ 0)
    (h : c * x = 0) : x = 0 :=
  (mul_eq_zero.mp h).resolve_left hc

private theorem factor_eq (hT : Equivariant T) (i a b k l : Fin 4) :
    (dval i a * star (dval i b) - dval i k * star (dval i l))
      * T (Matrix.single a b 1) k l = 0 := by
  have h := hT (dU i) (dU_unitary i) (Matrix.single a b 1)
  rw [dU_conj_single, map_smul] at h
  have he := congrFun (congrFun h k) l
  rw [Matrix.smul_apply, smul_eq_mul] at he
  rw [show dU i = Matrix.diagonal (dval i) from rfl,
    diag_conj_entry] at he
  linear_combination he

private theorem offdiag_kill (hT : Equivariant T) {a b : Fin 4}
    (hab : a ≠ b) (k l : Fin 4) (hkl : ¬(a = k ∧ b = l)) :
    T (Matrix.single a b 1) k l = 0 := by
  by_cases hk : a = k
  · have hl : b ≠ l := fun h => hkl ⟨hk, h⟩
    have hf := factor_eq T hT b a b k l
    rw [show dval b a = 1 from if_neg hab] at hf
    rw [show dval b b = Complex.I from if_pos rfl] at hf
    rw [show dval b k = 1 from by
      rw [← hk]; exact if_neg hab] at hf
    rw [show dval b l = 1 from
      if_neg (fun h => hl h.symm)] at hf
    rw [star_one, Complex.star_def, Complex.conj_I] at hf
    refine resolve_factor ?_ (by linear_combination hf :
      ((-Complex.I) - 1) * T (Matrix.single a b 1) k l = 0)
    intro h
    have := congrArg Complex.re h
    simp at this
  · have hf := factor_eq T hT a a b k l
    rw [show dval a a = Complex.I from if_pos rfl] at hf
    rw [show dval a b = 1 from
      if_neg (fun h => hab h.symm)] at hf
    rw [show dval a k = 1 from
      if_neg (fun h => hk h.symm)] at hf
    by_cases hl : l = a
    · rw [show dval a l = Complex.I from by
        rw [hl]; exact if_pos rfl] at hf
      rw [star_one, Complex.star_def, Complex.conj_I] at hf
      refine resolve_factor ?_ (by linear_combination hf :
        (2 * Complex.I) * T (Matrix.single a b 1) k l = 0)
      intro h
      have := congrArg Complex.im h
      simp at this
    · rw [show dval a l = 1 from if_neg hl] at hf
      rw [star_one] at hf
      refine resolve_factor ?_ (by linear_combination hf :
        (Complex.I - 1) * T (Matrix.single a b 1) k l = 0)
      intro h
      have := congrArg Complex.im h
      simp at this

private theorem diag_offdiag_kill (hT : Equivariant T)
    (g : Fin 4 → ℂ) (k l : Fin 4) (hkl : k ≠ l) :
    T (Matrix.diagonal g) k l = 0 := by
  have h := hT (dU k) (dU_unitary k) (Matrix.diagonal g)
  rw [dU_conj_diagonal] at h
  have he := congrFun (congrFun h k) l
  rw [show dU k = Matrix.diagonal (dval k) from rfl,
    diag_conj_entry] at he
  rw [show dval k k = Complex.I from if_pos rfl] at he
  rw [show dval k l = 1 from
    if_neg (fun h' => hkl h'.symm)] at he
  rw [star_one, mul_one] at he
  refine resolve_factor ?_ (by linear_combination he :
    (1 - Complex.I) * T (Matrix.diagonal g) k l = 0)
  intro h
  have := congrArg Complex.im h
  simp at this

private theorem perm_transport (hT : Equivariant T)
    (σ : Equiv.Perm (Fin 4)) (a b : Fin 4) :
    T (Matrix.single (σ a) (σ b) 1)
      = permMat σ * T (Matrix.single a b 1) * (permMat σ)ᴴ := by
  have h := hT (permMat σ) (permMat_unitary σ)
    (Matrix.single a b 1)
  rw [permMat_conj_single] at h
  exact h

/-- The common off-diagonal eigenvalue. -/
noncomputable def tval : ℂ := T (Matrix.single 0 1 1) 0 1

private theorem offdiag_eigen (hT : Equivariant T)
    {a b : Fin 4} (hab : a ≠ b) :
    T (Matrix.single a b 1)
      = (T (Matrix.single a b 1) a b) •
        Matrix.single a b (1 : ℂ) := by
  ext k l
  rw [Matrix.smul_apply, Matrix.single_apply]
  by_cases hkl : a = k ∧ b = l
  · rw [if_pos hkl, ← hkl.1, ← hkl.2, smul_eq_mul, mul_one]
  · rw [if_neg hkl, smul_zero]
    exact offdiag_kill T hT hab k l hkl

private theorem exists_perm_pair {a b : Fin 4} (hab : a ≠ b) :
    ∃ σ : Equiv.Perm (Fin 4), σ 0 = a ∧ σ 1 = b := by
  have hb'a : (Equiv.swap 0 a) 1 ≠ a := by
    by_cases h1a : (1 : Fin 4) = a
    · rw [← h1a, Equiv.swap_apply_right]
      decide
    · rw [Equiv.swap_apply_of_ne_of_ne (by decide) h1a]
      exact h1a
  refine ⟨(Equiv.swap ((Equiv.swap 0 a) 1) b)
    * (Equiv.swap 0 a), ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne (Ne.symm hb'a) hab]
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]

private theorem offdiag_eigen_all (hT : Equivariant T)
    {a b : Fin 4} (hab : a ≠ b) :
    T (Matrix.single a b 1)
      = tval T • Matrix.single a b (1 : ℂ) := by
  obtain ⟨σ, hσ0, hσ1⟩ := exists_perm_pair hab
  rw [← hσ0, ← hσ1, perm_transport T hT,
    offdiag_eigen T hT (by decide : (0 : Fin 4) ≠ 1)]
  rw [Matrix.mul_smul, Matrix.smul_mul, permMat_conj_single]
  rfl

/-- The diagonal difference `E_aa − E_bb`. -/
noncomputable def Dm (a b : Fin 4) : M4 :=
  Matrix.single a a 1 - Matrix.single b b 1

private theorem Dm_diagonal (a b : Fin 4) :
    Dm a b = Matrix.diagonal
      (fun k => (if a = k then (1 : ℂ) else 0)
        - (if b = k then 1 else 0)) := by
  ext p q
  rw [Dm, Matrix.sub_apply, Matrix.single_apply,
    Matrix.single_apply, Matrix.diagonal_apply]
  by_cases h : p = q
  · subst h
    rw [if_pos rfl]
    by_cases ha : a = p
    · rw [if_pos ⟨ha, ha⟩, if_pos ha]
      by_cases hb : b = p
      · rw [if_pos ⟨hb, hb⟩, if_pos hb]
      · rw [if_neg (fun hc => hb hc.1), if_neg hb]
    · rw [if_neg (fun hc => ha hc.1), if_neg ha]
      by_cases hb : b = p
      · rw [if_pos ⟨hb, hb⟩, if_pos hb]
      · rw [if_neg (fun hc => hb hc.1), if_neg hb]
  · rw [if_neg h]
    rw [if_neg (fun hc : a = p ∧ a = q => h (hc.1 ▸ hc.2 ▸ rfl)),
      if_neg (fun hc : b = p ∧ b = q => h (hc.1 ▸ hc.2 ▸ rfl))]
    ring

private theorem Dm_apply (a b p q : Fin 4) :
    Dm a b p q = (if a = p ∧ a = q then (1 : ℂ) else 0)
      - (if b = p ∧ b = q then 1 else 0) := by
  rw [Dm, Matrix.sub_apply, Matrix.single_apply,
    Matrix.single_apply]

private theorem permMat_conj_Dm (σ : Equiv.Perm (Fin 4))
    (a b : Fin 4) :
    permMat σ * Dm a b * (permMat σ)ᴴ = Dm (σ a) (σ b) := by
  rw [Dm, Dm, Matrix.mul_sub, Matrix.sub_mul,
    permMat_conj_single, permMat_conj_single]

private theorem diag_eigen_01 (hT : Equivariant T) :
    T (Dm 0 1) = (T (Dm 0 1) 0 0) • Dm 0 1 := by
  have hdiag : ∀ k l : Fin 4, k ≠ l → T (Dm 0 1) k l = 0 := by
    intro k l hkl
    rw [Dm_diagonal]
    exact diag_offdiag_kill T hT _ k l hkl
  have hDm : permMat (Equiv.swap 0 1) * Dm 0 1
      * (permMat (Equiv.swap 0 1))ᴴ = -(Dm 0 1) := by
    rw [permMat_conj_Dm, Equiv.swap_apply_left,
      Equiv.swap_apply_right, Dm, Dm]
    abel
  have h := hT (permMat (Equiv.swap 0 1))
    (permMat_unitary _) (Dm 0 1)
  rw [hDm, map_neg] at h
  have hentry : ∀ p q : Fin 4, -(T (Dm 0 1) p q)
      = T (Dm 0 1) ((Equiv.swap 0 1).symm p)
          ((Equiv.swap 0 1).symm q) := by
    intro p q
    have he := congrFun (congrFun h p) q
    rw [Matrix.neg_apply, permMat_conj_apply] at he
    exact he
  have h11 : T (Dm 0 1) 1 1 = -(T (Dm 0 1) 0 0) := by
    have he := hentry 1 1
    rw [Equiv.symm_swap, Equiv.swap_apply_right] at he
    linear_combination -he
  have h22 : T (Dm 0 1) 2 2 = 0 := by
    have he := hentry 2 2
    rw [Equiv.symm_swap, Equiv.swap_apply_of_ne_of_ne
      (by decide) (by decide)] at he
    linear_combination (-(1/2) : ℂ) * he
  have h33 : T (Dm 0 1) 3 3 = 0 := by
    have he := hentry 3 3
    rw [Equiv.symm_swap, Equiv.swap_apply_of_ne_of_ne
      (by decide) (by decide)] at he
    linear_combination (-(1/2) : ℂ) * he
  ext p q
  rw [Matrix.smul_apply, Dm_apply]
  by_cases hpq : p = q
  · subst hpq
    fin_cases p
    · norm_num
    · norm_num [h11]
    · norm_num
      exact h22
    · norm_num
      exact h33
  · rw [hdiag p q hpq]
    rw [if_neg (fun hc : (0 : Fin 4) = p ∧ (0 : Fin 4) = q =>
        hpq (hc.1 ▸ hc.2 ▸ rfl)),
      if_neg (fun hc : (1 : Fin 4) = p ∧ (1 : Fin 4) = q =>
        hpq (hc.1 ▸ hc.2 ▸ rfl))]
    simp

private theorem diag_eigen_eq_t (hT : Equivariant T) :
    T (Dm 0 1) = tval T • Dm 0 1 := by
  have hμ := diag_eigen_01 T hT
  set μ : ℂ := T (Dm 0 1) 0 0 with hμdef
  have hconj : pythR * Dm 0 1 * pythRᴴ
      = (-(7/25) : ℂ) • Dm 0 1
        + (-(24/25) : ℂ) • (Matrix.single 0 1 (1 : ℂ)
          + Matrix.single 1 0 (1 : ℂ)) := by
    rw [Dm]
    exact pythR_conj_diag
  have h := hT pythR pythR_unitary (Dm 0 1)
  rw [hconj, map_add, map_smul, map_smul, map_add] at h
  rw [offdiag_eigen_all T hT (by decide : (0 : Fin 4) ≠ 1),
    offdiag_eigen_all T hT (by decide : (1 : Fin 4) ≠ 0),
    hμ] at h
  have hrhs : pythR * (μ • Dm 0 1) * pythRᴴ
      = μ • ((-(7/25) : ℂ) • Dm 0 1
        + (-(24/25) : ℂ) • (Matrix.single 0 1 (1 : ℂ)
          + Matrix.single 1 0 (1 : ℂ))) := by
    rw [Matrix.mul_smul, Matrix.smul_mul, hconj]
  rw [hrhs] at h
  have hE : ((-(24/25) : ℂ) * (tval T - μ)) •
      (Matrix.single 0 1 (1 : ℂ) + Matrix.single 1 0 (1 : ℂ))
      = (0 : M4) := by
    linear_combination (norm := module) h
  have hval := congrFun (congrFun hE 0) 1
  rw [Matrix.smul_apply, Matrix.add_apply,
    Matrix.single_apply, Matrix.single_apply,
    if_pos ⟨rfl, rfl⟩,
    if_neg (by decide : ¬((1 : Fin 4) = 0 ∧ (0 : Fin 4) = 1)),
    Matrix.zero_apply, smul_eq_mul] at hval
  have h0 : (-(24/25) : ℂ) * (tval T - μ) = 0 := by
    linear_combination hval
  have ht := (mul_eq_zero.mp h0).resolve_left (by norm_num)
  rw [hμ, sub_eq_zero.mp ht]

private theorem diag_eigen_all (hT : Equivariant T)
    {a b : Fin 4} (hab : a ≠ b) :
    T (Dm a b) = tval T • Dm a b := by
  obtain ⟨σ, hσ0, hσ1⟩ := exists_perm_pair hab
  have h := hT (permMat σ) (permMat_unitary σ) (Dm 0 1)
  rw [permMat_conj_Dm, hσ0, hσ1, diag_eigen_eq_t T hT] at h
  rw [h, Matrix.mul_smul, Matrix.smul_mul, permMat_conj_Dm,
    hσ0, hσ1]

private theorem T_one_scalar (hT : Equivariant T) :
    T 1 = (T 1 0 0) • (1 : M4) := by
  have hdiag : ∀ k l : Fin 4, k ≠ l → T 1 k l = 0 := by
    intro k l hkl
    rw [show (1 : M4) = Matrix.diagonal (fun _ => 1) from
      Matrix.diagonal_one.symm]
    exact diag_offdiag_kill T hT _ k l hkl
  have hperm : ∀ (σ : Equiv.Perm (Fin 4)) (p : Fin 4),
      T 1 p p = T 1 (σ.symm p) (σ.symm p) := by
    intro σ p
    have h := hT (permMat σ) (permMat_unitary σ) 1
    have hP1 : permMat σ * (1 : M4) * (permMat σ)ᴴ = 1 := by
      rw [Matrix.mul_one]
      exact mul_eq_one_comm.mp (permMat_unitary σ)
    rw [hP1] at h
    have := congrFun (congrFun h p) p
    rw [permMat_conj_apply] at this
    exact this
  have hdiageq : ∀ p : Fin 4, T 1 p p = T 1 0 0 := by
    intro p
    by_cases hp : p = 0
    · rw [hp]
    · have := hperm (Equiv.swap 0 p) p
      rwa [show (Equiv.swap 0 p).symm p = 0 from by
        rw [Equiv.symm_swap, Equiv.swap_apply_right]] at this
  ext p q
  rw [Matrix.smul_apply, Matrix.one_apply]
  by_cases hpq : p = q
  · rw [if_pos hpq, smul_eq_mul, mul_one, ← hpq, hdiageq]
  · rw [if_neg hpq, smul_zero]
    exact hdiag p q hpq

private theorem matrix_expand4 (X : M4) :
    X = ∑ a, ∑ b, X a b • Matrix.single a b (1 : ℂ) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  refine Finset.sum_congr rfl fun a _ =>
    Finset.sum_congr rfl fun b _ => ?_
  rw [Matrix.smul_single, smul_eq_mul, mul_one]

private theorem single_diag_decomp (a : Fin 4) :
    Matrix.single a a (1 : ℂ)
      = (1/4 : ℂ) • (1 : M4)
        + (1/4 : ℂ) • ∑ k ∈ Finset.univ.erase a, Dm a k := by
  have hsum : ∑ k ∈ Finset.univ.erase a, Dm a k
      = (3 : ℂ) • Matrix.single a a 1
        - ∑ k ∈ Finset.univ.erase a,
            Matrix.single k k (1 : ℂ) := by
    unfold Dm
    rw [Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_erase_of_mem (Finset.mem_univ a),
      Finset.card_univ, Fintype.card_fin]
    congr 1
    rw [show (4 - 1 : ℕ) = 3 from rfl,
      ← Nat.cast_smul_eq_nsmul ℂ]
    norm_num
  rw [hsum]
  have hone : (1 : M4) = ∑ k, Matrix.single k k (1 : ℂ) := by
    ext p q
    rw [Matrix.one_apply, Matrix.sum_apply]
    by_cases hpq : p = q
    · rw [if_pos hpq]
      rw [Finset.sum_eq_single p (fun k _ hk => by
          rw [Matrix.single_apply,
            if_neg (fun hc => hk hc.1)])
        (fun h => absurd (Finset.mem_univ p) h)]
      rw [Matrix.single_apply, if_pos ⟨rfl, hpq⟩]
    · rw [if_neg hpq]
      refine (Finset.sum_eq_zero fun k _ => ?_).symm
      rw [Matrix.single_apply]
      rw [if_neg (fun hc => hpq ((hc.1.symm.trans hc.2)))]
  have hsplit : ∑ k, Matrix.single k k (1 : ℂ)
      = Matrix.single a a 1
        + ∑ k ∈ Finset.univ.erase a,
            Matrix.single k k (1 : ℂ) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a)]
  rw [hone, hsplit]
  module

/-- The block map `α P_𝟏 + β P_𝟏𝟓` as a linear map. -/
noncomputable def blockMap (α β : ℂ) : M4 →ₗ[ℂ] M4 where
  toFun X := (α * (X.trace / 4)) • (1 : M4)
    + β • (X - (X.trace / 4) • 1)
  map_add' X Y := by
    rw [Matrix.trace_add]
    module
  map_smul' c X := by
    rw [RingHom.id_apply, Matrix.trace_smul, smul_eq_mul]
    module

private theorem blockMap_apply (α β : ℂ) (X : M4) :
    blockMap α β X = (α * (X.trace / 4)) • (1 : M4)
      + β • (X - (X.trace / 4) • 1) := rfl

private theorem Dm_sum_erase (a : Fin 4) :
    ∑ k ∈ Finset.univ.erase a, Dm a k
      = (4 : ℂ) • Matrix.single a a (1 : ℂ) - 1 := by
  have hdec := single_diag_decomp a
  linear_combination (norm := module) (-4 : ℂ) • hdec

private theorem blockMap_single (T : M4 →ₗ[ℂ] M4)
    (hT : Equivariant T) (a b : Fin 4) :
    T (Matrix.single a b 1)
      = blockMap (T 1 0 0) (tval T) (Matrix.single a b 1) := by
  rw [blockMap_apply]
  by_cases hab : a = b
  · subst hab
    rw [Matrix.trace_single_eq_same]
    set c : ℂ := T 1 0 0 with hc
    have hT1 : T 1 = c • 1 := T_one_scalar T hT
    rw [show Matrix.single a a (1 : ℂ)
        = (1/4 : ℂ) • (1 : M4)
          + (1/4 : ℂ) • ∑ k ∈ Finset.univ.erase a, Dm a k
      from single_diag_decomp a, map_add, map_smul,
      map_smul, map_sum, hT1]
    rw [Finset.sum_congr rfl fun k hk =>
      diag_eigen_all T hT
        (fun h => (Finset.mem_erase.mp hk).1 h.symm)]
    rw [← Finset.smul_sum, Dm_sum_erase]
    module
  · rw [Matrix.trace_single_eq_of_ne a b 1 hab,
      offdiag_eigen_all T hT hab]
    module

/-- Every conjugation-equivariant endomorphism of `M₄(ℂ)`
is `α P_𝟏 + β P_𝟏𝟓`: Schur for the multiplicity-free
`𝟏 ⊕ 𝟏𝟓` conjugation representation, by explicitly chosen
rational unitaries. -/
theorem equivariant_endo_scalar (hT : Equivariant T) :
    ∀ X : M4, T X = ((T 1 0 0) * (X.trace / 4)) • (1 : M4)
      + tval T • (X - (X.trace / 4) • 1) := by
  intro X
  rw [← blockMap_apply]
  calc T X
      = T (∑ a, ∑ b, X a b • Matrix.single a b 1) := by
        rw [← matrix_expand4]
    _ = ∑ a, ∑ b, X a b • T (Matrix.single a b 1) := by
        simp only [map_sum, map_smul]
    _ = ∑ a, ∑ b, X a b •
          blockMap (T 1 0 0) (tval T) (Matrix.single a b 1) := by
        refine Finset.sum_congr rfl fun a _ =>
          Finset.sum_congr rfl fun b _ => ?_
        rw [blockMap_single T hT]
    _ = blockMap (T 1 0 0) (tval T)
          (∑ a, ∑ b, X a b • Matrix.single a b 1) := by
        simp only [map_sum, map_smul]
    _ = blockMap (T 1 0 0) (tval T) X := by
        rw [← matrix_expand4]

end EquivariantEndo

section Covariance

/-- The eight-dimensional typed carrier tensored with
`M₄(ℂ)`, modelled as `M₄`-valued tuples. -/
abbrev Carrier : Type := Fin 8 → M4

private theorem form_im_zero {M : Matrix (Fin 8) (Fin 8) ℂ}
    (h : ∀ c, 0 ≤ star c ⬝ᵥ (M *ᵥ c)) (c : Fin 8 → ℂ) :
    (star c ⬝ᵥ (M *ᵥ c)).im = 0 := by
  have := h c
  rw [Complex.le_def] at this
  rw [← this.2, Complex.zero_im]

private theorem entry_form (M : Matrix (Fin 8) (Fin 8) ℂ)
    (i j : Fin 8) :
    star (Pi.single i (1 : ℂ)) ⬝ᵥ (M *ᵥ Pi.single j 1)
      = M i j := by
  rw [dotProduct]
  rw [Finset.sum_eq_single i (fun k _ hk => by
      rw [Pi.star_apply, Pi.single_eq_of_ne hk, star_zero,
        zero_mul])
    (fun h => absurd (Finset.mem_univ i) h)]
  rw [Pi.star_apply, Pi.single_eq_same, star_one, one_mul]
  rw [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single j (fun k _ hk => by
      rw [Pi.single_eq_of_ne hk, mul_zero])
    (fun h => absurd (Finset.mem_univ j) h)]
  rw [Pi.single_eq_same, mul_one]

private theorem hermitian_of_form_nonneg
    {M : Matrix (Fin 8) (Fin 8) ℂ}
    (h : ∀ c, 0 ≤ star c ⬝ᵥ (M *ᵥ c)) : M.IsHermitian := by
  have hbilin : ∀ x y : Fin 8 → ℂ,
      star (x + y) ⬝ᵥ (M *ᵥ (x + y))
        = star x ⬝ᵥ (M *ᵥ x) + star y ⬝ᵥ (M *ᵥ y)
          + (star x ⬝ᵥ (M *ᵥ y) + star y ⬝ᵥ (M *ᵥ x)) := by
    intro x y
    rw [Matrix.mulVec_add, star_add, add_dotProduct,
      dotProduct_add, dotProduct_add]
    ring
  have hbilinI : ∀ x y : Fin 8 → ℂ,
      star (x + Complex.I • y) ⬝ᵥ
          (M *ᵥ (x + Complex.I • y))
        = star x ⬝ᵥ (M *ᵥ x) + star y ⬝ᵥ (M *ᵥ y)
          + (Complex.I * (star x ⬝ᵥ (M *ᵥ y))
            - Complex.I * (star y ⬝ᵥ (M *ᵥ x))) := by
    intro x y
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, star_add,
      star_smul, add_dotProduct, smul_dotProduct,
      dotProduct_add, dotProduct_add, dotProduct_smul,
      dotProduct_smul, Complex.star_def, Complex.conj_I]
    simp only [smul_eq_mul]
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [Matrix.IsHermitian]
  ext i j
  rw [Matrix.conjTranspose_apply]
  have ha := entry_form M j i
  have hb := entry_form M i j
  have h1 := form_im_zero h (Pi.single j (1 : ℂ)
    + Pi.single i 1)
  rw [hbilin, ha, hb] at h1
  have h2 := form_im_zero h (Pi.single j (1 : ℂ)
    + Complex.I • Pi.single i 1)
  rw [hbilinI, ha, hb] at h2
  have hjj := form_im_zero h (Pi.single j (1 : ℂ))
  have hii := form_im_zero h (Pi.single i (1 : ℂ))
  rw [show star (Pi.single j (1 : ℂ)) ⬝ᵥ
      (M *ᵥ Pi.single j 1) = M j j from entry_form M j j]
    at hjj
  rw [show star (Pi.single i (1 : ℂ)) ⬝ᵥ
      (M *ᵥ Pi.single i 1) = M i i from entry_form M i i]
    at hii
  simp only [Complex.add_im, Complex.sub_im,
    Complex.mul_im, Complex.I_re, Complex.I_im] at h1 h2
  rw [entry_form M j j, entry_form M i i] at h1 h2
  rw [hjj, hii] at h1 h2
  apply Complex.ext
  · simp only [Complex.star_def, Complex.conj_re]
    linarith
  · simp only [Complex.star_def, Complex.conj_im]
    linarith

/-- The delta tuple supported in slot `s`. -/
def dvec (s : Fin 8) (X : M4) : Carrier :=
  fun r => if r = s then X else 0

private theorem dvec_add (s : Fin 8) (X Y : M4) :
    dvec s (X + Y) = dvec s X + dvec s Y := by
  funext r
  unfold dvec
  rw [Pi.add_apply]
  by_cases h : r = s
  · rw [if_pos h, if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, if_neg h, add_zero]

private theorem dvec_smul (s : Fin 8) (c : ℂ) (X : M4) :
    dvec s (c • X) = c • dvec s X := by
  funext r
  unfold dvec
  rw [Pi.smul_apply]
  by_cases h : r = s
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, smul_zero]

private theorem dvec_sum (v : Carrier) :
    ∑ s, dvec s (v s) = v := by
  funext r
  rw [Finset.sum_apply]
  unfold dvec
  rw [Finset.sum_eq_single r (fun s _ hs => by
      rw [if_neg (fun h => hs h.symm)])
    (fun h => absurd (Finset.mem_univ r) h)]
  rw [if_pos rfl]

/-- The `(t,s)` matrix slice of a covariance operator. -/
noncomputable def sliceMap
    (Q : Carrier →ₗ[ℂ] Carrier) (t s : Fin 8) :
    M4 →ₗ[ℂ] M4 where
  toFun X := Q (dvec s X) t
  map_add' X Y := by
    rw [dvec_add, map_add]
    rfl
  map_smul' c X := by
    rw [RingHom.id_apply, dvec_smul, map_smul]
    rfl

/-- Covariance of the operator under simultaneous
conjugation on every `M₄` slot. -/
def CovariantQ (Q : Carrier →ₗ[ℂ] Carrier) : Prop :=
  ∀ U : M4, Uᴴ * U = 1 → ∀ v : Carrier,
    Q (fun r => U * v r * Uᴴ) = fun r => U * Q v r * Uᴴ

private theorem sliceMap_equivariant
    (Q : Carrier →ₗ[ℂ] Carrier) (hcov : CovariantQ Q)
    (t s : Fin 8) : Equivariant (sliceMap Q t s) := by
  intro U hU X
  have h := hcov U hU (dvec s X)
  have harg : (fun r => U * dvec s X r * Uᴴ)
      = dvec s (U * X * Uᴴ) := by
    funext r
    unfold dvec
    by_cases hr : r = s
    · rw [if_pos hr, if_pos hr]
    · rw [if_neg hr, if_neg hr, Matrix.mul_zero,
        Matrix.zero_mul]
  rw [harg] at h
  exact congrFun h t

/-- The singlet block entry. -/
noncomputable def gPhi (Q : Carrier →ₗ[ℂ] Carrier) :
    Matrix (Fin 8) (Fin 8) ℂ :=
  Matrix.of fun t s => sliceMap Q t s 1 0 0

/-- The adjoint block entry (with the manuscript's `1/15`
normalization). -/
noncomputable def gOmega (Q : Carrier →ₗ[ℂ] Carrier) :
    Matrix (Fin 8) (Fin 8) ℂ :=
  Matrix.of fun t s => 15 * tval (sliceMap Q t s)

private theorem trace_one4 : (1 : M4).trace = 4 := by
  rw [Matrix.trace_one]
  norm_num

private theorem slice_one (Q : Carrier →ₗ[ℂ] Carrier)
    (hcov : CovariantQ Q) (t s : Fin 8) :
    sliceMap Q t s 1 = gPhi Q t s • (1 : M4) := by
  rw [equivariant_endo_scalar _ (sliceMap_equivariant Q hcov t s) 1,
    trace_one4]
  rw [show (4 : ℂ) / 4 = 1 from by norm_num, mul_one,
    one_smul, sub_self, smul_zero, add_zero]
  rfl

private theorem slice_E01 (Q : Carrier →ₗ[ℂ] Carrier)
    (hcov : CovariantQ Q) (t s : Fin 8) :
    sliceMap Q t s (Matrix.single 0 1 1)
      = ((1/15 : ℂ) * gOmega Q t s) •
        Matrix.single 0 1 (1 : ℂ) := by
  rw [equivariant_endo_scalar _ (sliceMap_equivariant Q hcov t s)
    (Matrix.single 0 1 1),
    Matrix.trace_single_eq_of_ne 0 1 1 (by decide)]
  rw [show (0 : ℂ) / 4 = 0 from by norm_num, mul_zero,
    zero_smul, sub_zero, zero_add]
  rw [show (1/15 : ℂ) * gOmega Q t s = tval (sliceMap Q t s)
    from by
      rw [show gOmega Q t s = 15 * tval (sliceMap Q t s)
        from rfl]
      ring]

/-- The boxed decomposition formula. -/
theorem covariance_form (Q : Carrier →ₗ[ℂ] Carrier)
    (hcov : CovariantQ Q) (v : Carrier) (t : Fin 8) :
    Q v t = ∑ s, (gPhi Q t s * ((v s).trace / 4)) • (1 : M4)
      + ∑ s, ((1/15 : ℂ) * gOmega Q t s) •
          (v s - ((v s).trace / 4) • 1) := by
  have hexp : Q v t = ∑ s, sliceMap Q t s (v s) := by
    conv_lhs => rw [← dvec_sum v]
    rw [map_sum, Finset.sum_apply]
    rfl
  rw [hexp, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [equivariant_endo_scalar _
    (sliceMap_equivariant Q hcov t s) (v s)]
  rw [show sliceMap Q t s 1 0 0 = gPhi Q t s from rfl,
    show tval (sliceMap Q t s)
        = (1/15 : ℂ) * gOmega Q t s from by
      rw [show gOmega Q t s = 15 * tval (sliceMap Q t s)
        from rfl]
      ring]

private theorem slice_expand (Q : Carrier →ₗ[ℂ] Carrier)
    (v : Carrier) (t : Fin 8) :
    Q v t = ∑ s, sliceMap Q t s (v s) := by
  conv_lhs => rw [← dvec_sum v]
  rw [map_sum, Finset.sum_apply]
  rfl

private theorem le_of_four_smul {x : ℂ} (c : ℝ) (hc : 0 < c)
    (h : 0 ≤ (c : ℂ) * x) : 0 ≤ x := by
  rw [Complex.le_def] at h ⊢
  rw [Complex.zero_re, Complex.zero_im] at h ⊢
  have hre : ((c : ℂ) * x).re = c * x.re := by
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have him : ((c : ℂ) * x).im = c * x.im := by
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [hre, him] at h
  constructor
  · nlinarith [h.1]
  · have hx := (mul_eq_zero.mp h.2.symm).resolve_left hc.ne'
    exact hx.symm

/-- **Positivity of the singlet block** `G_Φ ⪰ 0`. -/
theorem gPhi_posSemidef (Q : Carrier →ₗ[ℂ] Carrier)
    (hcov : CovariantQ Q)
    (hpos : ∀ v : Carrier, 0 ≤ ∑ t, ((v t)ᴴ * Q v t).trace) :
    (gPhi Q).PosSemidef := by
  have hform : ∀ c : Fin 8 → ℂ,
      0 ≤ star c ⬝ᵥ ((gPhi Q) *ᵥ c) := by
    intro c
    have hQ : ∀ t, Q (fun r => c r • (1 : M4)) t
        = (∑ s, gPhi Q t s * c s) • (1 : M4) := by
      intro t
      rw [slice_expand]
      rw [Finset.sum_congr rfl fun s _ => by
        rw [map_smul, slice_one Q hcov, smul_smul,
          mul_comm (c s) _]]
      rw [← Finset.sum_smul]
    have hsum : ∑ t, (((fun r => c r • (1 : M4)) t)ᴴ *
        Q (fun r => c r • (1 : M4)) t).trace
        = (4 : ℂ) * (star c ⬝ᵥ ((gPhi Q) *ᵥ c)) := by
      rw [Finset.sum_congr rfl fun t _ => by
        rw [hQ t, Matrix.conjTranspose_smul,
          Matrix.conjTranspose_one, Matrix.smul_mul,
          Matrix.mul_smul, Matrix.one_mul, smul_smul,
          Matrix.trace_smul, trace_one4, smul_eq_mul]]
      rw [dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [Matrix.mulVec, dotProduct, Pi.star_apply]
      ring
    have h4 := hpos (fun r => c r • (1 : M4))
    rw [hsum] at h4
    exact le_of_four_smul 4 (by norm_num)
      (by exact_mod_cast h4)
  exact Matrix.posSemidef_iff_dotProduct_mulVec.mpr
    ⟨hermitian_of_form_nonneg hform, hform⟩

private theorem single01_conjTranspose :
    ((Matrix.single 0 1 (1 : ℂ) : M4))ᴴ
      = (Matrix.single 1 0 1 : M4) := by
  ext p q
  rw [Matrix.conjTranspose_apply, Matrix.single_apply,
    Matrix.single_apply]
  split_ifs with h1 h2 h2
  · exact star_one ℂ
  · exact absurd ⟨h1.2, h1.1⟩ h2
  · exact absurd ⟨h2.2, h2.1⟩ h1
  · exact star_zero ℂ

/-- **Positivity of the adjoint block** `G_Ω ⪰ 0`. -/
theorem gOmega_posSemidef (Q : Carrier →ₗ[ℂ] Carrier)
    (hcov : CovariantQ Q)
    (hpos : ∀ v : Carrier, 0 ≤ ∑ t, ((v t)ᴴ * Q v t).trace) :
    (gOmega Q).PosSemidef := by
  have hform : ∀ c : Fin 8 → ℂ,
      0 ≤ star c ⬝ᵥ ((gOmega Q) *ᵥ c) := by
    intro c
    have hQ : ∀ t, Q (fun r => c r • Matrix.single 0 1 1) t
        = ((1/15 : ℂ) * ∑ s, gOmega Q t s * c s) •
          Matrix.single 0 1 (1 : ℂ) := by
      intro t
      rw [slice_expand]
      rw [Finset.sum_congr rfl fun s _ => by
        rw [map_smul, slice_E01 Q hcov, smul_smul,
          show c s * ((1/15 : ℂ) * gOmega Q t s)
            = (1/15 : ℂ) * (gOmega Q t s * c s) from by ring]]
      rw [← Finset.sum_smul, ← Finset.mul_sum]
    have htr : ∀ z w : ℂ,
        ((z • (Matrix.single 0 1 (1 : ℂ) : M4))ᴴ *
          (w • (Matrix.single 0 1 (1 : ℂ) : M4))).trace
        = star z * w := by
      intro z w
      rw [Matrix.conjTranspose_smul, single01_conjTranspose,
        Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        Matrix.single_mul_single_same, mul_one,
        Matrix.trace_smul, Matrix.trace_single_eq_same,
        smul_eq_mul, mul_one]
    have hterm : ∀ t : Fin 8,
        (((fun r => c r • Matrix.single 0 1 (1 : ℂ)) t)ᴴ *
          Q (fun r => c r • Matrix.single 0 1 1) t).trace
        = star (c t) *
            ((1/15 : ℂ) * ∑ s, gOmega Q t s * c s) := by
      intro t
      rw [hQ t]
      beta_reduce
      exact htr (c t) _
    have hsum : ∑ t, (((fun r => c r • Matrix.single 0 1
        (1 : ℂ)) t)ᴴ *
        Q (fun r => c r • Matrix.single 0 1 1) t).trace
        = ((1/15 : ℂ)) * (star c ⬝ᵥ ((gOmega Q) *ᵥ c)) := by
      rw [Finset.sum_congr rfl fun t _ => hterm t]
      rw [dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [Matrix.mulVec, dotProduct, Pi.star_apply]
      ring
    have h15 := hpos (fun r => c r • Matrix.single 0 1 1)
    rw [hsum] at h15
    refine le_of_four_smul (1/15) (by norm_num) ?_
    rw [show (((1/15 : ℝ)) : ℂ) = (1/15 : ℂ) from by
      norm_num]
    exact h15
  exact Matrix.posSemidef_iff_dotProduct_mulVec.mpr
    ⟨hermitian_of_form_nonneg hform, hform⟩

/-- **`thm:SM-typed-occurrence-RN`, boxed singlet–adjoint
decomposition**: every positive `SU(4)`-covariant typed
occurrence covariance has the unique form
`ℚ = P_𝟏 ⊗ G_Φ + (1/15) P_𝟏𝟓 ⊗ G_Ω` with
`G_Φ, G_Ω ⪰ 0`. -/
theorem sm_typed_occurrence_su4_covariance
    (Q : Carrier →ₗ[ℂ] Carrier) (hcov : CovariantQ Q)
    (hpos : ∀ v : Carrier, 0 ≤ ∑ t, ((v t)ᴴ * Q v t).trace) :
    (gPhi Q).PosSemidef ∧ (gOmega Q).PosSemidef
    ∧ (∀ (v : Carrier) (t : Fin 8), Q v t
        = ∑ s, (gPhi Q t s * ((v s).trace / 4)) • (1 : M4)
          + ∑ s, ((1/15 : ℂ) * gOmega Q t s) •
              (v s - ((v s).trace / 4) • 1))
    ∧ ∀ G1 G2 : Matrix (Fin 8) (Fin 8) ℂ,
        (∀ (v : Carrier) (t : Fin 8), Q v t
          = ∑ s, (G1 t s * ((v s).trace / 4)) • (1 : M4)
            + ∑ s, ((1/15 : ℂ) * G2 t s) •
                (v s - ((v s).trace / 4) • 1))
        → G1 = gPhi Q ∧ G2 = gOmega Q := by
  refine ⟨gPhi_posSemidef Q hcov hpos,
    gOmega_posSemidef Q hcov hpos,
    covariance_form Q hcov, ?_⟩
  intro G1 G2 hF
  have hdvec_ne : ∀ (s' s : Fin 8) (X : M4), s ≠ s' →
      dvec s' X s = 0 := by
    intro s' s X hs
    unfold dvec
    rw [if_neg hs]
  have hdvec_eq : ∀ (s' : Fin 8) (X : M4),
      dvec s' X s' = X := by
    intro s' X
    unfold dvec
    rw [if_pos rfl]
  have hG1 : G1 = gPhi Q := by
    ext t s'
    have hL : Q (dvec s' (1 : M4)) t = gPhi Q t s' • 1 := by
      rw [show Q (dvec s' (1 : M4)) t
        = sliceMap Q t s' 1 from rfl, slice_one Q hcov]
    have hR := hF (dvec s' 1) t
    rw [hL] at hR
    rw [Finset.sum_eq_single s' (fun s _ hs => by
        rw [hdvec_ne s' s 1 hs, Matrix.trace_zero]
        simp)
      (fun h => absurd (Finset.mem_univ s') h)] at hR
    rw [Finset.sum_eq_single s' (fun s _ hs => by
        rw [hdvec_ne s' s 1 hs, Matrix.trace_zero]
        simp)
      (fun h => absurd (Finset.mem_univ s') h)] at hR
    rw [hdvec_eq s' 1, trace_one4] at hR
    rw [show (4 : ℂ) / 4 = 1 from by norm_num, mul_one,
      one_smul, sub_self, smul_zero, add_zero] at hR
    have hcoef := congrFun (congrFun hR 0) 0
    rw [Matrix.smul_apply, Matrix.smul_apply,
      Matrix.one_apply_eq, smul_eq_mul, smul_eq_mul,
      mul_one, mul_one] at hcoef
    exact hcoef.symm
  have hG2 : G2 = gOmega Q := by
    ext t s'
    have hL : Q (dvec s' (Matrix.single 0 1 (1 : ℂ))) t
        = ((1/15 : ℂ) * gOmega Q t s') •
          Matrix.single 0 1 (1 : ℂ) := by
      rw [show Q (dvec s' (Matrix.single 0 1 (1 : ℂ))) t
        = sliceMap Q t s' (Matrix.single 0 1 1) from rfl,
        slice_E01 Q hcov]
    have hR := hF (dvec s' (Matrix.single 0 1 1)) t
    rw [hL] at hR
    rw [Finset.sum_eq_zero (fun s (_ : s ∈ Finset.univ) => by
      by_cases hs : s = s'
      · rw [hs, hdvec_eq s' (Matrix.single 0 1 1),
          Matrix.trace_single_eq_of_ne 0 1 1 (by decide)]
        simp
      · rw [hdvec_ne s' s (Matrix.single 0 1 1) hs,
          Matrix.trace_zero]
        simp)] at hR
    rw [Finset.sum_eq_single s' (fun s _ hs => by
        rw [hdvec_ne s' s (Matrix.single 0 1 1) hs,
          Matrix.trace_zero]
        simp)
      (fun h => absurd (Finset.mem_univ s') h)] at hR
    rw [hdvec_eq s' (Matrix.single 0 1 1),
      Matrix.trace_single_eq_of_ne 0 1 1 (by decide)] at hR
    rw [show (0 : ℂ) / 4 = 0 from by norm_num, zero_smul,
      sub_zero, zero_add] at hR
    have hcoef := congrFun (congrFun hR 0) 1
    rw [Matrix.smul_apply, Matrix.smul_apply,
      Matrix.single_apply, if_pos ⟨rfl, rfl⟩, smul_eq_mul,
      smul_eq_mul, mul_one, mul_one] at hcoef
    have := mul_left_cancel₀
      (by norm_num : (1/15 : ℂ) ≠ 0) hcoef
    exact this.symm
  exact ⟨hG1, hG2⟩

end Covariance

end TypedSU4
end NCG
