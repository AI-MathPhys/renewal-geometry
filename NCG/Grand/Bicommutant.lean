/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.JointSourceUniversality

/-!
# Finite von Neumann double commutant
  (multiplier library #2 of the Gran-Tensor hard tier)

* `double_commutant`: for a unital `*`-closed subalgebra
  `A ⊆ M_n(ℂ)`, every matrix commuting with the commutant of
  `A` lies in `A` (`A'' = A`) — proved exactly by the
  vec-amplification argument: the amplified algebra `{a ⊗ I}`
  has commutant the block-in-`A'` matrices; the explicit Gram
  projection `P = V(VᴴV)⁻¹Vᴴ` onto `W = vec(A)` (built from a
  chosen basis of `A`) lies in that commutant by
  `*`-invariance of `W`; and
  `vec T = (T⊗I)·vec 1 = P(T⊗I)·vec 1 ∈ W`.
-/

open Matrix
open scoped Kronecker ComplexOrder

namespace NCG

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The commutant of a set of matrices. -/
def matCommutant (S : Set (Matrix n n ℂ)) :
    Set (Matrix n n ℂ) :=
  {T | ∀ a ∈ S, T * a = a * T}

private def vecF (b : Matrix n n ℂ) : n × n → ℂ :=
  fun p => b p.1 p.2

private lemma amp_mulVec_vecF (a b : Matrix n n ℂ) :
    (a ⊗ₖ (1 : Matrix n n ℂ)) *ᵥ vecF b = vecF (a * b) := by
  funext p
  simp only [vecF, Matrix.mulVec, dotProduct,
    Matrix.kroneckerMap_apply, Fintype.sum_prod_type]
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun j' _ => ?_
  rw [Finset.sum_eq_single p.2]
  · rw [Matrix.one_apply_eq, mul_one]
  · intro k' _ hk'
    rw [Matrix.one_apply_ne (Ne.symm hk'), mul_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

private lemma amp_entry (a : Matrix n n ℂ)
    (B : Matrix (n × n) (n × n) ℂ) (j : n) (k : n) (j' : n)
    (k' : n) :
    ((a ⊗ₖ (1 : Matrix n n ℂ)) * B) (j, k) (j', k')
      = ∑ l, a j l * B (l, k) (j', k') := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_eq_single k]
  · rw [Matrix.kroneckerMap_apply, Matrix.one_apply_eq,
      mul_one]
  · intro m _ hm
    rw [Matrix.kroneckerMap_apply,
      Matrix.one_apply_ne (Ne.symm hm), mul_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

private lemma entry_amp (a : Matrix n n ℂ)
    (B : Matrix (n × n) (n × n) ℂ) (j : n) (k : n) (j' : n)
    (k' : n) :
    (B * (a ⊗ₖ (1 : Matrix n n ℂ))) (j, k) (j', k')
      = ∑ l, B (j, k) (l, k') * a l j' := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_eq_single k']
  · rw [Matrix.kroneckerMap_apply, Matrix.one_apply_eq,
      mul_one]
  · intro m _ hm
    rw [Matrix.kroneckerMap_apply, Matrix.one_apply_ne hm,
      mul_zero, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **Finite double commutant**: a matrix commuting with the
commutant of a unital `*`-closed subalgebra lies in the
subalgebra. -/
theorem double_commutant (A : Subalgebra ℂ (Matrix n n ℂ))
    (hstar : ∀ a ∈ A, aᴴ ∈ A) (T : Matrix n n ℂ)
    (hT : ∀ b ∈ matCommutant (A : Set (Matrix n n ℂ)),
      T * b = b * T) :
    T ∈ A := by
  classical
  -- basis of A
  let ι := Module.Free.ChooseBasisIndex ℂ A.toSubmodule
  let bas : Module.Basis ι ℂ A.toSubmodule :=
    Module.Free.chooseBasis ℂ A.toSubmodule
  -- synthesis matrix with columns vec(bas i)
  let V : Matrix (n × n) ι ℂ :=
    Matrix.of fun p i => (bas i : Matrix n n ℂ) p.1 p.2
  -- column combinations are vecs of A-elements
  have hVmul : ∀ x : ι → ℂ,
      V *ᵥ x = vecF (∑ i, x i • (bas i : Matrix n n ℂ)) := by
    intro x
    funext p
    simp only [V, vecF, Matrix.mulVec, dotProduct,
      Matrix.of_apply, Matrix.sum_apply, Matrix.smul_apply,
      smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  -- injectivity of the synthesis
  have hVinj : ∀ x : ι → ℂ, V *ᵥ x = 0 → x = 0 := by
    intro x hx
    have hmat : ∑ i, x i • (bas i : Matrix n n ℂ) = 0 := by
      ext j k
      have := congrFun (hVmul x ▸ hx) (j, k)
      simpa [vecF] using this
    have hsub : ∑ i, x i • bas i = (0 : A.toSubmodule) := by
      apply Subtype.ext
      push_cast
      simpa using hmat
    have hli := Fintype.linearIndependent_iff.mp
      bas.linearIndependent x (by simpa using hsub)
    funext i
    exact hli i
  -- the Gram matrix is positive definite
  have hGH : (Vᴴ * V)ᴴ = Vᴴ * V := by
    rw [Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  have hG : (Vᴴ * V).PosDef := by
    refine Matrix.PosDef.of_dotProduct_mulVec_pos hGH ?_
    intro x hx
    have hgram := gram_realization_inner V x x
    rw [← hgram]
    have hVx : V *ᵥ x ≠ 0 := by
      intro h0
      exact hx (hVinj x h0)
    exact dotProduct_star_self_pos_iff.mpr hVx
  haveI := hG.isUnit.invertible
  -- coefficient matrices of left multiplication
  have hcoef : ∀ a ∈ A, ∃ C : Matrix ι ι ℂ,
      (a ⊗ₖ (1 : Matrix n n ℂ)) * V = V * C := by
    intro a ha
    refine ⟨Matrix.of fun k i =>
      bas.repr ⟨a * (bas i : Matrix n n ℂ),
        A.mul_mem ha (bas i).2⟩ k, ?_⟩
    ext p i
    have hcol : ((a ⊗ₖ (1 : Matrix n n ℂ)) * V) p i
        = ((a ⊗ₖ (1 : Matrix n n ℂ))
            *ᵥ fun q => V q i) p := by
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    rw [hcol]
    have hVi : (fun q => V q i)
        = vecF (bas i : Matrix n n ℂ) := rfl
    rw [hVi, amp_mulVec_vecF]
    -- RHS: (V * C) p i = Σ_k (bas k) p.1 p.2 * repr k
    have hexpand : (a * (bas i : Matrix n n ℂ))
        = ∑ k, (bas.repr ⟨a * (bas i : Matrix n n ℂ),
            A.mul_mem ha (bas i).2⟩ k)
          • (bas k : Matrix n n ℂ) := by
      have h := bas.sum_repr ⟨a * (bas i : Matrix n n ℂ),
        A.mul_mem ha (bas i).2⟩
      have h2 := congrArg
        (Subtype.val : A.toSubmodule → Matrix n n ℂ) h
      push_cast at h2
      simpa using h2.symm
    rw [show ((V * Matrix.of fun k i' =>
        bas.repr ⟨a * (bas i' : Matrix n n ℂ),
          A.mul_mem ha (bas i').2⟩ k) p i)
      = ∑ k, (bas k : Matrix n n ℂ) p.1 p.2
          * bas.repr ⟨a * (bas i : Matrix n n ℂ),
              A.mul_mem ha (bas i).2⟩ k from by
      simp [Matrix.mul_apply, V]]
    rw [vecF]
    conv_lhs => rw [hexpand]
    simp only [Matrix.sum_apply, Matrix.smul_apply,
      smul_eq_mul]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  -- the Gram projection commutes with the amplified algebra
  set G := Vᴴ * V with hGdef
  set P := V * G⁻¹ * Vᴴ with hPdef
  have hamp_star : ∀ a ∈ A,
      (a ⊗ₖ (1 : Matrix n n ℂ))ᴴ
        = aᴴ ⊗ₖ (1 : Matrix n n ℂ) := by
    intro a _
    rw [Matrix.conjTranspose_kronecker,
      Matrix.conjTranspose_one]
  have hPcomm : ∀ a ∈ A,
      (a ⊗ₖ (1 : Matrix n n ℂ)) * P
        = P * (a ⊗ₖ (1 : Matrix n n ℂ)) := by
    intro a ha
    obtain ⟨Ca, hCa⟩ := hcoef a ha
    obtain ⟨Cs, hCs⟩ := hcoef aᴴ (hstar a ha)
    -- Gram transfer: G * Ca = Csᴴ * G
    have hGc : G * Ca = Csᴴ * G := by
      have h1 : Vᴴ * ((a ⊗ₖ (1 : Matrix n n ℂ)) * V)
          = G * Ca := by
        rw [hCa, hGdef]
        simp only [Matrix.mul_assoc]
      have h2 : Vᴴ * ((a ⊗ₖ (1 : Matrix n n ℂ)) * V)
          = Csᴴ * G := by
        rw [show Vᴴ * ((a ⊗ₖ (1 : Matrix n n ℂ)) * V)
            = ((aᴴ ⊗ₖ (1 : Matrix n n ℂ)) * V)ᴴ * V from by
          rw [Matrix.conjTranspose_mul,
            Matrix.conjTranspose_kronecker,
            Matrix.conjTranspose_conjTranspose,
            Matrix.conjTranspose_one]
          simp only [Matrix.mul_assoc]]
        rw [hCs, Matrix.conjTranspose_mul, hGdef]
        simp only [Matrix.mul_assoc]
      rw [← h1, h2]
    have hCaG : Ca * G⁻¹ = G⁻¹ * Csᴴ := by
      have h : G⁻¹ * (G * Ca) * G⁻¹
          = G⁻¹ * (Csᴴ * G) * G⁻¹ := by rw [hGc]
      rw [show G⁻¹ * (G * Ca) * G⁻¹
          = (G⁻¹ * G) * (Ca * G⁻¹) from by
        simp only [Matrix.mul_assoc],
        Matrix.inv_mul_of_invertible, Matrix.one_mul] at h
      rw [show G⁻¹ * (Csᴴ * G) * G⁻¹
          = G⁻¹ * Csᴴ * (G * G⁻¹) from by
        simp only [Matrix.mul_assoc],
        Matrix.mul_inv_of_invertible, Matrix.mul_one] at h
      exact h
    calc (a ⊗ₖ (1 : Matrix n n ℂ)) * P
        = ((a ⊗ₖ (1 : Matrix n n ℂ)) * V) * G⁻¹ * Vᴴ := by
          rw [hPdef]
          simp only [Matrix.mul_assoc]
      _ = V * (Ca * G⁻¹) * Vᴴ := by
          rw [hCa]
          simp only [Matrix.mul_assoc]
      _ = V * (G⁻¹ * Csᴴ) * Vᴴ := by rw [hCaG]
      _ = V * G⁻¹ * ((aᴴ ⊗ₖ (1 : Matrix n n ℂ)) * V)ᴴ := by
          rw [hCs, Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
      _ = P * (a ⊗ₖ (1 : Matrix n n ℂ)) := by
          rw [Matrix.conjTranspose_mul, hamp_star aᴴ
            (hstar a ha),
            Matrix.conjTranspose_conjTranspose, hPdef]
          simp only [Matrix.mul_assoc]
  -- P * V = V
  have hPV : P * V = V := by
    rw [hPdef]
    calc V * G⁻¹ * Vᴴ * V = V * (G⁻¹ * G) := by
          rw [hGdef]
          simp only [Matrix.mul_assoc]
      _ = V := by
          rw [Matrix.inv_mul_of_invertible, Matrix.mul_one]
  -- the blocks of P lie in the commutant of A
  have hPblocks : ∀ k k' : n,
      (Matrix.of fun j j' => P (j, k) (j', k'))
        ∈ matCommutant (A : Set (Matrix n n ℂ)) := by
    intro k k' a ha
    ext j j'
    have h := Matrix.ext_iff.mpr (hPcomm a ha) (j, k) (j', k')
    rw [amp_entry, entry_amp] at h
    simp only [Matrix.mul_apply, Matrix.of_apply]
    exact h.symm
  -- T ⊗ 1 commutes with P
  have hTP : (T ⊗ₖ (1 : Matrix n n ℂ)) * P
      = P * (T ⊗ₖ (1 : Matrix n n ℂ)) := by
    ext p q
    obtain ⟨j, k⟩ := p
    obtain ⟨j', k'⟩ := q
    rw [amp_entry, entry_amp]
    have hcomm := hT _ (hPblocks k k')
    have h := Matrix.ext_iff.mpr hcomm j j'
    simpa [Matrix.mul_apply, Matrix.of_apply] using h
  -- vec 1 lies in the column space
  obtain ⟨y, hy⟩ : ∃ y : ι → ℂ,
      V *ᵥ y = vecF (1 : Matrix n n ℂ) := by
    refine ⟨fun i => bas.repr ⟨1, A.one_mem⟩ i, ?_⟩
    rw [hVmul]
    congr 1
    have h := bas.sum_repr ⟨1, A.one_mem⟩
    have h2 := congrArg
      (Subtype.val : A.toSubmodule → Matrix n n ℂ) h
    push_cast at h2
    simpa using h2
  have hPfix : P *ᵥ vecF (1 : Matrix n n ℂ)
      = vecF (1 : Matrix n n ℂ) := by
    rw [← hy, Matrix.mulVec_mulVec, hPV]
  -- vec T is P-fixed, hence in the column space
  have hvecT : vecF T = P *ᵥ vecF T := by
    calc vecF T
        = (T ⊗ₖ (1 : Matrix n n ℂ)) *ᵥ vecF 1 := by
          rw [amp_mulVec_vecF, Matrix.mul_one]
      _ = (T ⊗ₖ (1 : Matrix n n ℂ))
            *ᵥ (P *ᵥ vecF 1) := by rw [hPfix]
      _ = ((T ⊗ₖ (1 : Matrix n n ℂ)) * P) *ᵥ vecF 1 := by
          rw [Matrix.mulVec_mulVec]
      _ = (P * (T ⊗ₖ (1 : Matrix n n ℂ))) *ᵥ vecF 1 := by
          rw [hTP]
      _ = P *ᵥ vecF T := by
          rw [← Matrix.mulVec_mulVec, amp_mulVec_vecF,
            Matrix.mul_one]
  set z := (G⁻¹ * Vᴴ) *ᵥ vecF T with hzdef
  have hVz : V *ᵥ z = vecF T := by
    rw [hzdef, Matrix.mulVec_mulVec, ← Matrix.mul_assoc,
      ← hPdef, ← hvecT]
  have hTsum : T = ∑ i, z i • (bas i : Matrix n n ℂ) := by
    have h := (hVmul z).symm.trans hVz
    ext j k
    have h2 := congrFun h (j, k)
    simpa [vecF] using h2.symm
  rw [hTsum]
  exact sum_mem fun i _ =>
    A.smul_mem (bas i).2 (z i)

end NCG
