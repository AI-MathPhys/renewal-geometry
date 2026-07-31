/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Matter.QutritMUB

/-!
# Relative revisions and the canonical Bell pointer
  (`thm:v5-relative-revision`, `cor:v5-bell-dephasing`,
   SM_emergence)

For the projective qutrit implementers `W_{ab}`, the relative
revisions `𝒲_{ab} = conj(W_{ab}) ⊗ W_{ab}` on the doubled system:

* `relRev_mul` — `𝒲_a𝒲_b = 𝒲_{a+b}`: the scalar cocycle cancels
  between the conjugate and plain slots (an honest `𝔽₃²`
  representation);
* `relRev_bell` — the vectorized Weyl words are joint eigenvectors:
  `𝒲_{ab}|ℬ_{cd}⟩ = ω^{bc-ad}|ℬ_{cd}⟩` (the generalized Bell
  basis);
* `bellProj` / `bellProj_relRev` — the Bell projections are the
  Fourier character sums of the relative revisions;
* `relRev_twirl_eq_pinch` — source-local Bell dephasing: the
  uniform `𝒲`-twirl equals the pinching by the Bell projections,
  `(1/9)Σ_a 𝒲_a A 𝒲_a† = Σ_b Π_b A Π_b`.
-/

namespace NCG

open Matrix

open scoped Kronecker

noncomputable section

/-- The relative revision `𝒲_{ab} = conj(W_{ab}) ⊗ W_{ab}`. -/
def relRev (a b : ℕ) :
    Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  ((qW a b).map (starRingEnd ℂ)) ⊗ₖ qW a b

lemma map_conj_smul (c : ℂ) (M : Matrix (Fin 3) (Fin 3) ℂ) :
    (c • M).map (starRingEnd ℂ)
      = (starRingEnd ℂ) c • M.map (starRingEnd ℂ) := by
  ext i j
  simp [Matrix.map_apply]

lemma conj_pow_mul_self (e : ℕ) :
    (starRingEnd ℂ) (qOmega ^ e) * qOmega ^ e = 1 := by
  rw [map_pow, qOmega_conj, ← pow_mul, ← pow_add,
    show 2 * e + e = 3 * e by ring, qOmega_pow_mod,
    Nat.mul_mod_right, pow_zero]

/-- `thm:v5-relative-revision` (character): `𝒲_a𝒲_b = 𝒲_{a+b}` —
the two scalar cocycles cancel in the tensor product. -/
theorem relRev_mul (a b c d : ℕ) :
    relRev a b * relRev c d = relRev (a + c) (b + d) := by
  rw [relRev, relRev, relRev, ← Matrix.mul_kronecker_mul,
    ← Matrix.map_mul, qW_mul, map_conj_smul,
    Matrix.smul_kronecker, Matrix.kronecker_smul, smul_smul,
    conj_pow_mul_self, one_smul]

lemma qW_conjTranspose_eq_sq (a b : ℕ) :
    (qW a b)ᴴ = qW a b ^ 2 := by
  rw [qW_conjTranspose, qW_pow_two]

/-- The relative revisions only depend on the labels mod `3`. -/
lemma relRev_mod (a b : ℕ) :
    relRev a b = relRev (a % 3) (b % 3) := by
  rw [relRev, relRev, qW_mod]

/-- `𝒲_{ab}† = 𝒲_{2a,2b} = 𝒲_{-(a,b)}`: the relative revisions
are a unitary representation. -/
lemma relRev_conjTranspose (a b : ℕ) :
    (relRev a b)ᴴ = relRev (2 * a) (2 * b) := by
  rw [relRev, Matrix.conjTranspose_kronecker, relRev]
  have h1 : ((qW a b).map (starRingEnd ℂ))ᴴ
      = ((qW a b)ᴴ).map (starRingEnd ℂ) := by
    ext i j
    simp [Matrix.conjTranspose_apply, Matrix.map_apply]
  rw [h1, qW_conjTranspose, map_conj_smul, Matrix.smul_kronecker,
    Matrix.kronecker_smul, smul_smul, conj_pow_mul_self, one_smul]

/-- `thm:v5-relative-revision` (Bell eigenvalue): the vectorized
Weyl words are joint eigenvectors of every relative revision,
`𝒲_{ab}·vec(W_{cd}) = ω^{bc+2ad}·vec(W_{cd})`. -/
theorem relRev_bell (a b c d : ℕ) :
    relRev a b *ᵥ Matrix.vec (qW c d)
      = qOmega ^ ((b * c + 2 * a * d) % 3)
          • Matrix.vec (qW c d) := by
  rw [relRev, Matrix.kronecker_mulVec_vec]
  have hT : ((qW a b).map (starRingEnd ℂ))ᵀ = (qW a b)ᴴ := by
    ext i j
    simp [Matrix.conjTranspose_apply, Matrix.map_apply]
  rw [hT, qW_conjTranspose_eq_sq, qW_conj_word, Matrix.vec_smul,
    qW_mod c d]

/-- The relative revisions indexed by `𝔽₃²`. -/
def relRevF (q : Fin 3 × Fin 3) :
    Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  relRev (q.1 : ℕ) (q.2 : ℕ)

/-- Negation on `𝔽₃²` labels. -/
def negF (q : Fin 3 × Fin 3) : Fin 3 × Fin 3 :=
  (⟨2 * (q.1 : ℕ) % 3, Nat.mod_lt _ (by norm_num)⟩,
   ⟨2 * (q.2 : ℕ) % 3, Nat.mod_lt _ (by norm_num)⟩)

lemma relRevF_conjTranspose (q : Fin 3 × Fin 3) :
    (relRevF q)ᴴ = relRevF (negF q) := by
  rw [relRevF, relRev_conjTranspose, relRev_mod, relRevF, negF]

/-- `cor:v5-bell-dephasing` (Fourier form): the Bell projections
as character sums of the relative revisions. -/
def bellProj (p : Fin 3 × Fin 3) :
    Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  (9 : ℂ)⁻¹ • ∑ q : Fin 3 × Fin 3,
    qOmega ^ (2 * ((q.2 : ℕ) * (p.1 : ℕ)
      + 2 * (q.1 : ℕ) * (p.2 : ℕ))) • relRevF q

lemma char_sum_fin (c : ℕ) :
    ∑ t : Fin 3, qOmega ^ ((t : ℕ) * c)
      = if c % 3 = 0 then 3 else 0 := by
  rw [Fin.sum_univ_three]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, zero_mul,
    pow_zero, one_mul]
  by_cases h : c % 3 = 0
  · rw [if_pos h, qOmega_pow_mod c, h, qOmega_pow_mod (2 * c),
      show 2 * c % 3 = 0 by omega, pow_zero]
    norm_num
  · rw [if_neg h]
    linear_combination qOmega_sum_of_not_dvd (m := c) (by omega)

lemma bell_char_sum (v w : ℕ) :
    ∑ p : Fin 3 × Fin 3,
        qOmega ^ ((p.1 : ℕ) * v + (p.2 : ℕ) * w)
      = if v % 3 = 0 ∧ w % 3 = 0 then 9 else 0 := by
  rw [Fintype.sum_prod_type]
  simp_rw [pow_add]
  rw [← Finset.sum_mul_sum, char_sum_fin, char_sum_fin]
  by_cases hv : v % 3 = 0 <;> by_cases hw : w % 3 = 0
  · rw [if_pos hv, if_pos hw, if_pos ⟨hv, hw⟩]
    norm_num
  · simp [hv, hw]
  · simp [hv, hw]
  · simp [hv, hw]

lemma sum_smul_mul_sum (f g : Fin 3 × Fin 3 → ℂ)
    (A : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) :
    (∑ q : Fin 3 × Fin 3, f q • relRevF q) * A
        * (∑ q' : Fin 3 × Fin 3, g q' • relRevF q')
      = ∑ q : Fin 3 × Fin 3, ∑ q' : Fin 3 × Fin 3,
          (f q * g q') • (relRevF q * A * relRevF q') := by
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro q _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q' _
  rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul]

lemma delta_collapse (q : Fin 3 × Fin 3)
    (F : Fin 3 × Fin 3 → Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) :
    (∑ q' : Fin 3 × Fin 3,
      (if (2 * ((q.2 : ℕ) + (q'.2 : ℕ))) % 3 = 0
          ∧ (4 * ((q.1 : ℕ) + (q'.1 : ℕ))) % 3 = 0
        then (9 : ℂ) else 0) • F q')
      = (9 : ℂ) • F (negF q) := by
  rw [Finset.sum_eq_single (negF q)]
  · rw [show ((negF q).2 : ℕ) = 2 * (q.2 : ℕ) % 3 from rfl,
      show ((negF q).1 : ℕ) = 2 * (q.1 : ℕ) % 3 from rfl, if_pos]
    constructor
    · have := q.2.isLt
      omega
    · have := q.1.isLt
      omega
  · intro q' _ hq'
    rw [if_neg, zero_smul]
    rintro ⟨h1, h2⟩
    apply hq'
    have hb1 := q.1.isLt
    have hb2 := q.2.isLt
    have hb1' := q'.1.isLt
    have hb2' := q'.2.isLt
    have e1 : (q'.1 : ℕ) = 2 * (q.1 : ℕ) % 3 := by omega
    have e2 : (q'.2 : ℕ) = 2 * (q.2 : ℕ) % 3 := by omega
    exact Prod.ext (Fin.ext e1) (Fin.ext e2)
  · intro hmem
    exact absurd (Finset.mem_univ _) hmem

/-- `cor:v5-bell-dephasing`: the uniform relative-revision twirl
equals the pinching by the Bell projections. -/
theorem relRev_twirl_eq_pinch
    (A : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ) :
    (9 : ℂ)⁻¹ • ∑ q : Fin 3 × Fin 3,
        relRevF q * A * (relRevF q)ᴴ
      = ∑ p : Fin 3 × Fin 3, bellProj p * A * bellProj p := by
  have hexp : ∀ p : Fin 3 × Fin 3,
      bellProj p * A * bellProj p
        = (81 : ℂ)⁻¹ • ∑ q : Fin 3 × Fin 3, ∑ q' : Fin 3 × Fin 3,
            qOmega ^ (((p.1 : ℕ) * (2 * ((q.2 : ℕ) + (q'.2 : ℕ)))
                + (p.2 : ℕ) * (4 * ((q.1 : ℕ) + (q'.1 : ℕ)))))
              • (relRevF q * A * relRevF q') := by
    intro p
    rw [bellProj, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.smul_mul, smul_smul,
      show (9 : ℂ)⁻¹ * (9 : ℂ)⁻¹ = (81 : ℂ)⁻¹ by norm_num,
      sum_smul_mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro q _
    apply Finset.sum_congr rfl
    intro q' _
    rw [← pow_add,
      show 2 * ((q.2 : ℕ) * (p.1 : ℕ) + 2 * (q.1 : ℕ) * (p.2 : ℕ))
          + 2 * ((q'.2 : ℕ) * (p.1 : ℕ)
            + 2 * (q'.1 : ℕ) * (p.2 : ℕ))
        = (p.1 : ℕ) * (2 * ((q.2 : ℕ) + (q'.2 : ℕ)))
          + (p.2 : ℕ) * (4 * ((q.1 : ℕ) + (q'.1 : ℕ))) by ring]
  have hrhs : ∑ p : Fin 3 × Fin 3, bellProj p * A * bellProj p
      = (9 : ℂ)⁻¹ • ∑ q : Fin 3 × Fin 3,
          relRevF q * A * relRevF (negF q) :=
    calc ∑ p : Fin 3 × Fin 3, bellProj p * A * bellProj p
        = (81 : ℂ)⁻¹ • ∑ p : Fin 3 × Fin 3,
            ∑ q : Fin 3 × Fin 3, ∑ q' : Fin 3 × Fin 3,
              qOmega ^ (((p.1 : ℕ)
                    * (2 * ((q.2 : ℕ) + (q'.2 : ℕ)))
                  + (p.2 : ℕ)
                    * (4 * ((q.1 : ℕ) + (q'.1 : ℕ)))))
                • (relRevF q * A * relRevF q') := by
          rw [Finset.smul_sum]
          exact Finset.sum_congr rfl fun p _ => hexp p
      _ = (81 : ℂ)⁻¹ • ∑ q : Fin 3 × Fin 3,
            ∑ q' : Fin 3 × Fin 3,
              (∑ p : Fin 3 × Fin 3,
                qOmega ^ (((p.1 : ℕ)
                      * (2 * ((q.2 : ℕ) + (q'.2 : ℕ)))
                    + (p.2 : ℕ)
                      * (4 * ((q.1 : ℕ) + (q'.1 : ℕ))))))
                • (relRevF q * A * relRevF q') := by
          apply congrArg
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro q _
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro q' _
          rw [← Finset.sum_smul]
      _ = (81 : ℂ)⁻¹ • ∑ q : Fin 3 × Fin 3,
            ∑ q' : Fin 3 × Fin 3,
              (if (2 * ((q.2 : ℕ) + (q'.2 : ℕ))) % 3 = 0
                  ∧ (4 * ((q.1 : ℕ) + (q'.1 : ℕ))) % 3 = 0
                then (9 : ℂ) else 0)
                • (relRevF q * A * relRevF q') := by
          apply congrArg
          apply Finset.sum_congr rfl
          intro q _
          apply Finset.sum_congr rfl
          intro q' _
          rw [bell_char_sum]
      _ = (81 : ℂ)⁻¹ • ∑ q : Fin 3 × Fin 3,
            (9 : ℂ) • (relRevF q * A * relRevF (negF q)) := by
          apply congrArg
          apply Finset.sum_congr rfl
          intro q _
          exact delta_collapse q _
      _ = (9 : ℂ)⁻¹ • ∑ q : Fin 3 × Fin 3,
            relRevF q * A * relRevF (negF q) := by
          rw [← Finset.smul_sum, smul_smul]
          norm_num
  rw [hrhs]
  apply congrArg
  apply Finset.sum_congr rfl
  intro q _
  rw [relRevF_conjTranspose]

end

end NCG
