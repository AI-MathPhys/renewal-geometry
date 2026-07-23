/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Canonical reduction of the global standing conditions

Covers `prop:canonical-condition-reductions` from
`manuscripts/lorentzian_emergence/lorentzian_emergence.tex` (Appendix: logical status of the hypotheses):

* **(a)** `stationary_supported_on_terminal`: every stationary law of
  a finite Markov branch kernel is supported on **terminal** strongly
  connected components — if `π x > 0` and `y` is reachable from `x`
  through positive-probability steps, then `π y > 0` and `x` is
  reachable back from `y`.  Hence all recurrent constructions may be
  performed on one selected terminal component.

* **(b)** `action_kernel_quotient_faithful`: quotienting a group
  action by its kernel makes it faithful (the induced map on the
  quotient is injective); and `matrix_algEquiv_inner`
  (**Skolem–Noether** for full matrix algebras, proved from scratch
  via matrix units): every algebra automorphism of `M_n(K)` over a
  field is inner, `φ(a) = S a S⁻¹`.

* **(c)** is the radical-quotient reduction: quotienting the
  projective label space by `rad ω` yields a nondegenerate
  alternating space and hence the canonical primitive matrix factor.
  This part is already formalized:
  `NCG.PrimitiveQuotient`, `NCG.inducedForm_isAlt`,
  `NCG.inducedForm_separating` (`NCG/Dimension/PrimitiveReduction`),
  centrality of radical implementers
  `NCG.radical_iff_central` (`NCG/Algebra/RadicalCentre`), and the
  block/dimension count of `NCG/Algebra/FactorBlocks`.
-/

namespace NCG

open Matrix

/-! ## (a) Stationary laws live on terminal components -/

section Terminal

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- One positive-probability transition. -/
def stepRel (P : S → S → ℝ) (x y : S) : Prop := 0 < P x y

/-- Reachability through positive-probability steps. -/
def Reaches (P : S → S → ℝ) : S → S → Prop :=
  Relation.ReflTransGen (stepRel P)

/-- The support of a stationary law is closed under one positive
step. -/
theorem support_step {P : S → S → ℝ} (hP0 : ∀ a b, 0 ≤ P a b)
    {π : S → ℝ} (hπ0 : ∀ a, 0 ≤ π a)
    (hπ : ∀ b, ∑ a, π a * P a b = π b)
    {x y : S} (hx : 0 < π x) (hxy : stepRel P x y) : 0 < π y := by
  have h1 : π x * P x y ≤ ∑ a, π a * P a y :=
    Finset.single_le_sum
      (fun a _ => mul_nonneg (hπ0 a) (hP0 a y)) (Finset.mem_univ x)
  rw [hπ y] at h1
  exact lt_of_lt_of_le (mul_pos hx hxy) h1

/-- The support of a stationary law is closed under reachability. -/
theorem support_reaches {P : S → S → ℝ} (hP0 : ∀ a b, 0 ≤ P a b)
    {π : S → ℝ} (hπ0 : ∀ a, 0 ≤ π a)
    (hπ : ∀ b, ∑ a, π a * P a b = π b)
    {x y : S} (hx : 0 < π x) (hxy : Reaches P x y) : 0 < π y := by
  induction hxy with
  | refl => exact hx
  | tail _ hstep ih => exact support_step hP0 hπ0 hπ ih hstep

/-- **Proposition `prop:canonical-condition-reductions` (a)**: a
stationary law of a row-stochastic kernel is supported on terminal
strongly connected components: everything reachable from the support
carries positive mass **and can return**. -/
theorem stationary_supported_on_terminal {P : S → S → ℝ}
    (hP0 : ∀ a b, 0 ≤ P a b) (hrow : ∀ a, ∑ b, P a b = 1)
    {π : S → ℝ} (hπ0 : ∀ a, 0 ≤ π a)
    (hπ : ∀ b, ∑ a, π a * P a b = π b)
    {x y : S} (hx : 0 < π x) (hxy : Reaches P x y) :
    0 < π y ∧ Reaches P y x := by
  classical
  refine ⟨support_reaches hP0 hπ0 hπ hx hxy, ?_⟩
  by_contra hyx
  -- R: the states reachable from y; x ∉ R.
  set R : Finset S :=
    Finset.univ.filter (fun z => Reaches P y z) with hR
  have hyR : y ∈ R := by
    rw [hR, Finset.mem_filter]
    exact ⟨Finset.mem_univ y, Relation.ReflTransGen.refl⟩
  have hxR : x ∉ R := by
    rw [hR, Finset.mem_filter]
    intro h
    exact hyx h.2
  have hclosed : ∀ a ∈ R, ∀ z, 0 < P a z → z ∈ R := by
    intro a ha z hz
    rw [hR, Finset.mem_filter] at ha ⊢
    exact ⟨Finset.mem_univ z, ha.2.tail hz⟩
  -- rows of members of R put full mass inside R
  have hfull : ∀ a ∈ R, ∑ z ∈ R, P a z = 1 := by
    intro a ha
    have hsplit := Finset.sum_filter_add_sum_filter_not
      Finset.univ (fun z => Reaches P y z) (fun z => P a z)
    have hzero : ∑ z ∈ Finset.univ.filter
        (fun z => ¬ Reaches P y z), P a z = 0 := by
      refine Finset.sum_eq_zero fun z hz => ?_
      rw [Finset.mem_filter] at hz
      by_contra hne
      have hpos : 0 < P a z :=
        lt_of_le_of_ne (hP0 a z) (Ne.symm hne)
      have := hclosed a ha z hpos
      rw [hR, Finset.mem_filter] at this
      exact hz.2 this.2
    rw [hzero, add_zero] at hsplit
    rw [hR]
    rw [hsplit, hrow a]
  -- mass conservation over R
  have hmassR : (∑ z ∈ R, π z)
      = ∑ a, π a * ∑ z ∈ R, P a z := by
    have h1 : (∑ z ∈ R, π z) = ∑ z ∈ R, ∑ a, π a * P a z :=
      Finset.sum_congr rfl fun z _ => (hπ z).symm
    rw [h1, Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => (Finset.mul_sum _ _ _).symm
  have hsplitA := Finset.sum_filter_add_sum_filter_not
    Finset.univ (fun z => Reaches P y z)
    (fun a => π a * ∑ z ∈ R, P a z)
  have hinR : (∑ a ∈ Finset.univ.filter (fun z => Reaches P y z),
      π a * ∑ z ∈ R, P a z) = ∑ a ∈ R, π a := by
    refine Finset.sum_congr (by rw [hR]) fun a ha => ?_
    rw [hfull a ha, mul_one]
  -- the leakage into R from outside is zero
  have hleak : (∑ a ∈ Finset.univ.filter
      (fun z => ¬ Reaches P y z), π a * ∑ z ∈ R, P a z) = 0 := by
    have h2 := hsplitA
    rw [hinR] at h2
    rw [← hmassR] at h2
    linarith [h2]
  -- each outside term vanishes
  have hterm : ∀ a, ¬ Reaches P y a → π a * (∑ z ∈ R, P a z) = 0 := by
    intro a ha
    have hnn : ∀ b ∈ Finset.univ.filter
        (fun z => ¬ Reaches P y z),
        0 ≤ π b * ∑ z ∈ R, P b z := by
      intro b _
      exact mul_nonneg (hπ0 b)
        (Finset.sum_nonneg fun z _ => hP0 b z)
    have hmem : a ∈ Finset.univ.filter
        (fun z => ¬ Reaches P y z) := by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ a, ha⟩
    exact (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hleak a hmem
  -- outside the reach of y, no positive-mass state can step into R
  have hnostep : ∀ a, ¬ Reaches P y a → 0 < π a →
      ∀ z ∈ R, P a z = 0 := by
    intro a ha hπa z hzR
    have h3 := hterm a ha
    rcases mul_eq_zero.mp h3 with h | h
    · exact absurd h hπa.ne'
    · exact (Finset.sum_eq_zero_iff_of_nonneg
        fun b _ => hP0 a b).mp h z hzR
  -- propagate "positive mass and outside the reach of y" along paths
  have hkeystep : ∀ {a b : S},
      (0 < π a ∧ ¬ Reaches P y a) → stepRel P a b →
      (0 < π b ∧ ¬ Reaches P y b) := by
    intro a b hab hstepab
    refine ⟨support_step hP0 hπ0 hπ hab.1 hstepab, ?_⟩
    intro hyb
    have hbR : b ∈ R := by
      rw [hR, Finset.mem_filter]
      exact ⟨Finset.mem_univ b, hyb⟩
    exact hstepab.ne' (hnostep a hab.2 hab.1 b hbR)
  have hinv : ∀ c : S, Reaches P x c → (0 < π c ∧ ¬ Reaches P y c) := by
    intro c hxc
    induction hxc with
    | refl => exact ⟨hx, hyx⟩
    | tail hp hstepab ih => exact hkeystep ih hstepab
  exact (hinv y hxy).2 Relation.ReflTransGen.refl

end Terminal

/-! ## (b) Faithfulness after quotienting the kernel, and
Skolem–Noether -/

section Faithful

/-- **Proposition `prop:canonical-condition-reductions` (b),
faithfulness**: quotienting a (stabiliser) action by its kernel makes
it faithful — the induced homomorphism on the quotient is
injective. -/
theorem action_kernel_quotient_faithful {K M : Type*} [Group K]
    [Group M] (φ : K →* M) :
    Function.Injective (QuotientGroup.kerLift φ) :=
  QuotientGroup.kerLift_injective φ

end Faithful

section SkolemNoether

variable {K : Type*} [Field K] {n : ℕ}

/-- **Proposition `prop:canonical-condition-reductions` (b),
inner automorphisms — Skolem–Noether for `M_n(K)`**: every algebra
automorphism of a full matrix algebra over a field is inner.  Proved
from scratch via matrix units: `f_{ij} := φ(E_{ij})` satisfy the same
relations, a vector `w` with `f₀₀ w = w ≠ 0` produces the invertible
intertwiner `S` with columns `f_{j0} w`, and an explicit left inverse
is exhibited. -/
theorem matrix_algEquiv_inner (hn : 0 < n)
    (φ : Matrix (Fin n) (Fin n) K ≃ₐ[K] Matrix (Fin n) (Fin n) K) :
    ∃ S : Matrix (Fin n) (Fin n) K, IsUnit S ∧
      ∀ a, φ a = S * a * S⁻¹ := by
  classical
  haveI : NeZero n := ⟨hn.ne'⟩
  set f : Fin n → Fin n → Matrix (Fin n) (Fin n) K :=
    fun i j => φ (Matrix.single i j 1) with hf
  -- the transported matrix-unit relations
  have hff : ∀ i j k l, f i j * f k l
      = if j = k then f i l else 0 := by
    intro i j k l
    rcases eq_or_ne j k with rfl | hjk
    · rw [if_pos rfl]
      simp only [hf]
      rw [← map_mul, Matrix.single_mul_single_same, one_mul]
    · rw [if_neg hjk]
      simp only [hf]
      rw [← map_mul, Matrix.single_mul_single_of_ne (h := hjk),
        map_zero]
  -- a vector fixed by f₀₀ with a nonzero coordinate
  have hE00 : (Matrix.single 0 0 1 : Matrix (Fin n) (Fin n) K) ≠ 0 := by
    intro h
    have h2 := congrFun (congrFun h 0) 0
    rw [Matrix.single_apply_same] at h2
    exact one_ne_zero h2
  have hf00ne : f 0 0 ≠ 0 := by
    intro h
    have h2 : φ (Matrix.single 0 0 1 : Matrix (Fin n) (Fin n) K) = φ 0 := by
      rw [map_zero]
      exact h
    exact hE00 (φ.injective h2)
  have hex : ∃ i j, f 0 0 i j ≠ 0 := by
    by_contra hall
    refine hf00ne (Matrix.ext fun i j => ?_)
    rw [Matrix.zero_apply]
    by_contra hij
    exact hall ⟨i, j, hij⟩
  obtain ⟨i₁, j₁, hentry⟩ := hex
  set w : Fin n → K := f 0 0 *ᵥ Pi.single j₁ 1 with hw
  have hidem : f 0 0 * f 0 0 = f 0 0 := by
    have h3 := hff 0 0 0 0
    rwa [if_pos rfl] at h3
  have hfw : f 0 0 *ᵥ w = w := by
    rw [hw, Matrix.mulVec_mulVec, hidem]
  have hwne : w i₁ ≠ 0 := by
    have h4 : w i₁ = f 0 0 i₁ j₁ := by
      rw [hw]
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [h4]
    exact hentry
  -- the intertwiner and its explicit left inverse
  set Smat : Matrix (Fin n) (Fin n) K :=
    Matrix.of (fun i j => (f j 0 *ᵥ w) i) with hS
  set Tmat : Matrix (Fin n) (Fin n) K :=
    Matrix.of (fun k j => (w i₁)⁻¹ * f 0 k i₁ j) with hT
  -- commutation with the matrix units
  have hcommE : ∀ k l, f k l * Smat
      = Smat * Matrix.single k l 1 := by
    intro k l
    ext i j
    rw [Matrix.mul_apply, Matrix.mul_apply]
    have hR : (∑ m, Smat i m * Matrix.single k l (1 : K) m j)
        = if l = j then Smat i k else 0 := by
      rcases eq_or_ne l j with rfl | hlj
      · rw [if_pos rfl]
        rw [Finset.sum_eq_single k]
        · rw [Matrix.single_apply_same, mul_one]
        · intro m _ hmk
          rw [Matrix.single_apply_of_row_ne (Ne.symm hmk), mul_zero]
        · intro habs
          exact absurd (Finset.mem_univ k) habs
      · rw [if_neg hlj]
        refine Finset.sum_eq_zero fun m _ => ?_
        rw [Matrix.single_apply_of_col_ne _ _ hlj, mul_zero]
    rw [hR]
    have hL : (∑ m, f k l i m * Smat m j)
        = ((f k l * f j 0) *ᵥ w) i := by
      rw [← Matrix.mulVec_mulVec]
      simp [hS, Matrix.mulVec, dotProduct, Matrix.of_apply]
    rw [hL, hff k l j 0]
    rcases eq_or_ne l j with rfl | hlj
    · rw [if_pos rfl, if_pos rfl]
      rfl
    · rw [if_neg hlj, if_neg hlj, Matrix.zero_mulVec]
      rfl
  -- the left inverse
  have hTS : Tmat * Smat = 1 := by
    ext k l
    rw [Matrix.mul_apply, Matrix.one_apply]
    have h5 : (∑ j, Tmat k j * Smat j l)
        = (w i₁)⁻¹ * (((f 0 k * f l 0) *ᵥ w) i₁) := by
      rw [← Matrix.mulVec_mulVec]
      simp [hT, hS, Matrix.mulVec, dotProduct, Matrix.of_apply,
        Finset.mul_sum, mul_assoc]
    rw [h5, hff 0 k l 0]
    rcases eq_or_ne k l with rfl | hkl
    · rw [if_pos rfl, if_pos rfl, hfw]
      exact inv_mul_cancel₀ hwne
    · rw [if_neg hkl, if_neg hkl, Matrix.zero_mulVec]
      simp
  have hST : Smat * Tmat = 1 := by
    rwa [mul_eq_one_comm] at hTS
  have hSunit : IsUnit Smat := ⟨⟨Smat, Tmat, hST, hTS⟩, rfl⟩
  -- linear extension of the commutation
  have hcomm : ∀ a, φ a * Smat = Smat * a := by
    intro a
    have ha : a = ∑ i, ∑ j, Matrix.single i j (a i j) :=
      Matrix.matrix_eq_sum_single a
    have h1 : φ a * Smat = ∑ i, ∑ j,
        φ (Matrix.single i j (a i j)) * Smat := by
      conv_lhs => rw [ha]
      rw [map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_sum, Finset.sum_mul]
    have h2 : Smat * a = ∑ i, ∑ j,
        Smat * Matrix.single i j (a i j) := by
      conv_lhs => rw [ha]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
    rw [h1, h2]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    have hsmul : Matrix.single i j (a i j)
        = (a i j) • Matrix.single i j (1 : K) := by
      rw [Matrix.smul_single, smul_eq_mul, mul_one]
    rw [hsmul, map_smul, smul_mul_assoc, mul_smul_comm, hcommE i j]
  -- conclusion
  refine ⟨Smat, hSunit, fun a => ?_⟩
  have hSS : Smat * Smat⁻¹ = 1 :=
    Matrix.mul_nonsing_inv Smat
      ((Matrix.isUnit_iff_isUnit_det Smat).mp hSunit)
  calc φ a = φ a * (Smat * Smat⁻¹) := by rw [hSS, mul_one]
    _ = φ a * Smat * Smat⁻¹ := by rw [mul_assoc]
    _ = Smat * a * Smat⁻¹ := by rw [hcomm a]

end SkolemNoether

end NCG
