/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.Gravity.RelationalSchedulerADM
import NCG.Krein.FundamentalSymmetry

/-!
# Positive geometry and Krein signature are distinct layers
  (`lem:supp-positive-krein-distinct`, emergent-spacetime manuscript)

* `RenewalGeometry.wordGram_positive` — the word Gram
  `𝕂(v, w) = τ(v* w)` of any word family for a positive functional `τ`
  (`τ(a* a) ≥ 0`) is positive: `Σ c̄_v c_w 𝕂(v, w) = τ(a* a) ≥ 0`;
* `RenewalGeometry.wordGram_adjoin_positive` — it remains positive after
  adjoining one further word (the protected orientation record), and the
  old block is unchanged;
* `RenewalGeometry.rootBracket_quadForm`, `rootBracket_nonneg` — every
  positive combination `Σ c_a r_a r_aᵀ` (`c_a ≥ 0`) of the spatial root
  dyadics has quadratic form `Σ c_a (r_a·v)²` and hence no negative direction;
* `RenewalGeometry.eq_one_of_involution_nonneg` — a real involution
  `S² = 1` with nonnegative quadratic form is `S = 1`: no positive form can
  serve as a nontrivial sign involution;
* `RenewalGeometry.kreinForm_indefinite` — the Krein form `[u, v]_J = ⟪u, Jv⟫`
  is positive on the `+1` eigenspace and negative on the `−1` eigenspace, so
  it is indefinite as soon as both are nonzero;
* `RenewalGeometry.positive_krein_distinct_layers` — the bundled lemma. -/

open Matrix NCG
open scoped ComplexInnerProductSpace

namespace RenewalGeometry

section WordGram

variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

/-- The word Gram kernel `𝕂(v, w) = τ(v* w)` of a word family `w`
(`thm:supp-word-flatness`). -/
def wordGram (τ : A →ₗ[ℂ] ℂ) {ι : Type*} (w : ι → A) (i j : ι) : ℂ :=
  τ (star (w i) * w j)

/-- The Gram quadratic form is `τ(a* a)` for `a = Σ c_w w`
(`lem:supp-positive-krein-distinct`, positivity of the word Gram). -/
theorem wordGram_quadForm (τ : A →ₗ[ℂ] ℂ) {ι : Type*} [Fintype ι]
    (w : ι → A) (c : ι → ℂ) :
    (∑ i, ∑ j, star (c i) * c j * wordGram τ w i j)
      = τ (star (∑ i, c i • w i) * ∑ j, c j • w j) := by
  rw [star_sum, Finset.sum_mul_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [wordGram, star_smul, smul_mul_smul_comm, map_smul, smul_eq_mul]

/-- **`lem:supp-positive-krein-distinct`, positive layer**: the word Gram of
any word family for a positive functional is positive semidefinite. -/
theorem wordGram_positive (τ : A →ₗ[ℂ] ℂ)
    (hτ : ∀ a : A, 0 ≤ (τ (star a * a)).re)
    {ι : Type*} [Fintype ι] (w : ι → A) (c : ι → ℂ) :
    0 ≤ (∑ i, ∑ j, star (c i) * c j * wordGram τ w i j).re := by
  rw [wordGram_quadForm]
  exact hτ _

/-- **`lem:supp-positive-krein-distinct`**: adjoining the protected
orientation record `θ` to the word family keeps the Gram hierarchy positive,
and the old block is unchanged. -/
theorem wordGram_adjoin_positive (τ : A →ₗ[ℂ] ℂ)
    (hτ : ∀ a : A, 0 ≤ (τ (star a * a)).re)
    {ι : Type*} [Fintype ι] (w : ι → A) (θ : A) :
    (∀ c : ι ⊕ Unit → ℂ,
      0 ≤ (∑ i, ∑ j, star (c i) * c j
        * wordGram τ (Sum.elim w (fun _ : Unit => θ)) i j).re)
    ∧ ∀ i j : ι, wordGram τ (Sum.elim w (fun _ : Unit => θ)) (Sum.inl i) (Sum.inl j)
        = wordGram τ w i j :=
  ⟨fun c => wordGram_positive τ hτ _ c, fun _ _ => rfl⟩

end WordGram

section Bracket

/-- The quadratic form of a combination of dyadics:
`vᵀ (Σ c_a r_a r_aᵀ) v = Σ c_a (r_a · v)²`. -/
theorem rootBracket_quadForm {m n : Type*} [Fintype m] [Fintype n]
    (r : m → n → ℝ) (c : m → ℝ) (v : n → ℝ) :
    v ⬝ᵥ ((∑ a, c a • vecMulVec (r a) (r a)) *ᵥ v)
      = ∑ a, c a * (r a ⬝ᵥ v) ^ 2 := by
  rw [Matrix.sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.smul_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul,
    dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul,
    dotProduct_comm v (r a)]
  ring

/-- **`lem:supp-positive-krein-distinct`, spatial layer**: a nonnegative
combination of the root dyadics has no negative direction. -/
theorem rootBracket_nonneg {m n : Type*} [Fintype m] [Fintype n]
    (r : m → n → ℝ) (c : m → ℝ) (hc : ∀ a, 0 ≤ c a) (v : n → ℝ) :
    0 ≤ v ⬝ᵥ ((∑ a, c a • vecMulVec (r a) (r a)) *ᵥ v) := by
  rw [rootBracket_quadForm]
  exact Finset.sum_nonneg fun a _ => mul_nonneg (hc a) (sq_nonneg _)

/-- A real involution `S² = 1` whose quadratic form is nonnegative is the
identity: positive data cannot supply a nontrivial sign involution
(`lem:supp-positive-krein-distinct`, real-matrix form of
`NCG.IsFundamentalSymmetry.eq_one_of_krein_nonneg`). -/
theorem eq_one_of_involution_nonneg {n : Type*} [Fintype n] [DecidableEq n]
    (S : Matrix n n ℝ) (hS : S * S = 1)
    (hpos : ∀ v : n → ℝ, 0 ≤ v ⬝ᵥ (S *ᵥ v)) : S = 1 := by
  -- every vector is fixed by `S`
  have hfix : ∀ v : n → ℝ, S *ᵥ v = v := by
    intro v
    set z : n → ℝ := v - S *ᵥ v with hz
    have hSz : S *ᵥ z = -z := by
      rw [hz, Matrix.mulVec_sub, Matrix.mulVec_mulVec, hS, Matrix.one_mulVec]
      abel
    have h := hpos z
    rw [hSz, dotProduct_neg] at h
    have hzz : z ⬝ᵥ z = 0 := by
      have h0 : 0 ≤ z ⬝ᵥ z :=
        Finset.sum_nonneg fun i _ => mul_self_nonneg (z i)
      linarith
    have hz0 : z = 0 := dotProduct_self_eq_zero.mp hzz
    rw [hz] at hz0
    exact (sub_eq_zero.mp hz0).symm
  ext i j
  have h := congrFun (hfix (Pi.single j 1)) i
  rw [Matrix.mulVec_single_one] at h
  simp only [Matrix.col_apply] at h
  rw [h, Matrix.one_apply, Pi.single_apply]

end Bracket

section Krein

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **`lem:supp-positive-krein-distinct`, signed layer**: the Krein form is
positive on the `+1` eigenspace of `J` and negative on the `−1` eigenspace,
hence indefinite whenever both are nonzero (`eq:supp-krein-splitting`,
`eq:supp-krein-form`). -/
theorem kreinForm_indefinite (J : H →L[ℂ] H) {u v : H}
    (hu : J u = u) (hu0 : u ≠ 0) (hv : J v = -v) (hv0 : v ≠ 0) :
    0 < (kreinForm J u u).re ∧ (kreinForm J v v).re < 0 := by
  have hnu : 0 < ‖u‖ := norm_pos_iff.mpr hu0
  have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  constructor
  · rw [kreinForm_def, hu, inner_self_eq_norm_sq_to_K,
      RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_pow, Complex.ofReal_re]
    positivity
  · rw [kreinForm_def, hv, inner_neg_right, inner_self_eq_norm_sq_to_K,
      RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_pow, Complex.neg_re,
      Complex.ofReal_re]
    have : 0 < ‖v‖ ^ 2 := by positivity
    linarith

end Krein

/-- **Lemma `lem:supp-positive-krein-distinct`**: the positive word-Gram
hierarchy stays positive after adjoining the protected orientation record;
every positive combination of the spatial `A₃` root dyadics has no negative
direction and cannot serve as a nontrivial sign involution; the indefinite
sign is carried entirely by the Krein involution `J`, whose form is positive
on the `+1` and negative on the `−1` eigenspace — hence the Lorentzian
signature of the principal symbol (which needs a negative direction) requires
the signed layer in addition to the `A₃` bracket. -/
theorem positive_krein_distinct_layers
    {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
    (τ : A →ₗ[ℂ] ℂ) (hτ : ∀ a : A, 0 ≤ (τ (star a * a)).re)
    {ι : Type*} [Fintype ι] (w : ι → A) (θ : A)
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (J : H →L[ℂ] H) (hJ : IsFundamentalSymmetry J) :
    -- the word Gram, with the orientation record adjoined, is positive
    ((∀ c : ι ⊕ Unit → ℂ,
        0 ≤ (∑ i, ∑ j, star (c i) * c j
          * wordGram τ (Sum.elim w (fun _ : Unit => θ)) i j).re)
      ∧ ∀ i j : ι,
        wordGram τ (Sum.elim w (fun _ : Unit => θ)) (Sum.inl i) (Sum.inl j)
          = wordGram τ w i j)
    -- every positive root bracket has no negative direction …
    ∧ (∀ c : Fin 6 → ℝ, (∀ a, 0 < c a) →
        ¬ ∃ v : Fin 3 → ℝ,
          v ⬝ᵥ ((∑ a, c a • vecMulVec (a3SchedulerRoot a)
            (a3SchedulerRoot a)) *ᵥ v) < 0)
    -- … and cannot replace the Krein involution: as an involution it is `1`
    ∧ (∀ c : Fin 6 → ℝ, (∀ a, 0 < c a) →
        (∑ a, c a • vecMulVec (a3SchedulerRoot a) (a3SchedulerRoot a))
          * (∑ a, c a • vecMulVec (a3SchedulerRoot a) (a3SchedulerRoot a))
          = 1 →
        (∑ a, c a • vecMulVec (a3SchedulerRoot a) (a3SchedulerRoot a)) = 1)
    -- the sign is carried by `J`: indefinite when both eigenspaces are nonzero
    ∧ (∀ u v : H, J u = u → u ≠ 0 → J v = -v → v ≠ 0 →
        0 < (kreinForm J u u).re ∧ (kreinForm J v v).re < 0)
    -- and a positive Krein form forces the trivial involution
    ∧ ((∀ x : H, 0 ≤ (kreinForm J x x).re) → J = 1) := by
  refine ⟨wordGram_adjoin_positive τ hτ w θ, ?_, ?_, ?_, ?_⟩
  · intro c hc ⟨v, hv⟩
    have := rootBracket_nonneg a3SchedulerRoot c (fun a => le_of_lt (hc a)) v
    linarith
  · intro c hc hinv
    exact eq_one_of_involution_nonneg _ hinv
      (rootBracket_nonneg a3SchedulerRoot c (fun a => le_of_lt (hc a)))
  · intro u v hu hu0 hv hv0
    exact kreinForm_indefinite J hu hu0 hv hv0
  · intro hpos
    exact hJ.eq_one_of_krein_nonneg hpos

end RenewalGeometry
-- AXIOMCHECK
#print axioms RenewalGeometry.positive_krein_distinct_layers
#print axioms RenewalGeometry.wordGram_positive
#print axioms RenewalGeometry.wordGram_adjoin_positive
#print axioms RenewalGeometry.rootBracket_nonneg
#print axioms RenewalGeometry.eq_one_of_involution_nonneg
#print axioms RenewalGeometry.kreinForm_indefinite
