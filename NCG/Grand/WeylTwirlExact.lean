/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.RelEntropyKronExact
import NCG.Grand.StinespringDilationExact

/-!
# The Weyl twirl: the partial trace as an average of unitary conjugations

Step (D3) of the finite Uhlmann-monotonicity programme for
`thm:accepted-Petz-sufficiency`: the environment partial trace is the
`d²`-fold average of the Weyl (clock-and-shift) unitary conjugations,

`(1/d²) ∑_{s,t} (W_{st} ⊗ 1) X (W_{st} ⊗ 1)^* = (1/d) 1 ⊗ Tr_env X`.

Together with the proved ancilla identity (D2), unitary invariance (D1)
and the Stinespring reduction (D5), this reduces the entire
data-processing inequality to joint convexity of the relative entropy at
the Weyl family.

* `weyl`: the clock-and-shift unitaries on `ZMod d`;
* `stdAddChar_sum_eq`: character orthogonality;
* `weyl_twirl`: the boxed twirl identity;
* `relEntropy_envTrace_le_of_jointConvexity`: partial-trace monotonicity
  from the joint-convexity interface.
-/

open Matrix Unitary Finset Kronecker
open scoped ComplexOrder

namespace NCG
namespace Petz

open NCG.QRE

variable {m : Type*} [Fintype m] [DecidableEq m]
variable {d : ℕ} [NeZero d]

/-! ### Character helpers -/

theorem stdAddChar_sum_eq (c : ZMod d) :
    ∑ t : ZMod d, ZMod.stdAddChar (t * c) =
      if c = 0 then (d : ℂ) else 0 := by
  split_ifs with hc
  · subst hc
    simp only [mul_zero, AddChar.map_zero_eq_one]
    rw [Finset.sum_const, Finset.card_univ, ZMod.card]
    simp
  · have hne : (ZMod.stdAddChar (N := d)).mulShift c ≠ 1 :=
      ZMod.isPrimitive_stdAddChar d hc
    have h := AddChar.sum_eq_zero_of_ne_one hne
    simp only [AddChar.mulShift_apply] at h
    rw [← h]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [mul_comm]

theorem stdAddChar_star_mul_self (x : ZMod d) :
    star (ZMod.stdAddChar x) * ZMod.stdAddChar x = 1 := by
  have hn : ‖ZMod.stdAddChar (N := d) x‖ = 1 := by
    rw [ZMod.stdAddChar_apply]
    exact Circle.norm_coe _
  rw [Complex.star_def, mul_comm, Complex.mul_conj]
  norm_cast
  rw [Complex.normSq_eq_norm_sq, hn]
  norm_num

theorem stdAddChar_ne_zero (x : ZMod d) : ZMod.stdAddChar x ≠ 0 := by
  intro h
  have := stdAddChar_star_mul_self x
  rw [h, mul_zero] at this
  exact zero_ne_one this

theorem stdAddChar_star (x : ZMod d) :
    star (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  have h1 : ZMod.stdAddChar (-x) * ZMod.stdAddChar x = 1 := by
    rw [← AddChar.map_add_eq_mul]
    simp
  have h2 := stdAddChar_star_mul_self x
  exact mul_right_cancel₀ (stdAddChar_ne_zero x) (h2.trans h1.symm)

/-! ### The Weyl unitaries -/

/-- The clock-and-shift (Weyl) unitary `W_{st} : e_k ↦ χ(tk) e_{k+s}`. -/
noncomputable def weyl (d : ℕ) [NeZero d] (s t : ZMod d) :
    Matrix (ZMod d) (ZMod d) ℂ :=
  Matrix.of fun i k => if i = k + s then ZMod.stdAddChar (t * k) else 0

theorem weyl_star_mul_self (s t : ZMod d) :
    star (weyl d s t) * weyl d s t = 1 := by
  ext k l
  rw [Matrix.mul_apply]
  simp only [Matrix.star_apply, weyl, Matrix.of_apply]
  by_cases hkl : k = l
  · subst hkl
    rw [Matrix.one_apply_eq, Finset.sum_eq_single (k + s)]
    · have h := stdAddChar_star_mul_self (d := d) (t * k)
      simpa using h
    · intro i _ hi
      rw [if_neg hi, star_zero, zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [Matrix.one_apply_ne hkl]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases h1 : i = k + s
    · have h2 : ¬ i = l + s := by
        intro h2
        exact hkl (by
          have := h1.symm.trans h2
          exact add_right_cancel this)
      rw [if_neg h2, mul_zero]
    · rw [if_neg h1, star_zero, zero_mul]

theorem weyl_mul_star_self (s t : ZMod d) :
    weyl d s t * star (weyl d s t) = 1 :=
  mul_eq_one_comm.mp (weyl_star_mul_self s t)

omit [Fintype m] in
/-- The kron entry of a Weyl-with-identity operator. -/
theorem weylKron_apply (s t : ZMod d) (p q : ZMod d × m) :
    (weyl d s t ⊗ₖ (1 : Matrix m m ℂ)) p q =
      if p.1 = q.1 + s ∧ p.2 = q.2
        then ZMod.stdAddChar (t * q.1) else 0 := by
  rcases p with ⟨i, a⟩
  rcases q with ⟨k, c⟩
  rw [Matrix.kronecker_apply]
  simp only [weyl, Matrix.of_apply, Matrix.one_apply]
  split_ifs <;> simp_all

theorem weylKron_star_mul_self (s t : ZMod d) :
    star (weyl d s t ⊗ₖ (1 : Matrix m m ℂ)) *
      (weyl d s t ⊗ₖ (1 : Matrix m m ℂ)) = 1 := by
  have h : (weyl d s t ⊗ₖ (1 : Matrix m m ℂ))ᴴ *
      (weyl d s t ⊗ₖ (1 : Matrix m m ℂ)) = 1 := by
    have hk : (weyl d s t ⊗ₖ (1 : Matrix m m ℂ))ᴴ =
        (weyl d s t)ᴴ ⊗ₖ (1 : Matrix m m ℂ)ᴴ := by
      ext ⟨i, a⟩ ⟨j, b⟩
      simp only [Matrix.conjTranspose_apply, Matrix.kronecker_apply,
        star_mul']
    rw [hk, ← Matrix.mul_kronecker_mul, Matrix.conjTranspose_one,
      Matrix.one_mul]
    rw [show (weyl d s t)ᴴ * weyl d s t = 1 from by
      rw [← Matrix.star_eq_conjTranspose]
      exact weyl_star_mul_self s t]
    exact Matrix.one_kronecker_one
  rw [Matrix.star_eq_conjTranspose]
  exact h

/-- The Weyl-with-identity operators as unitary elements. -/
noncomputable def weylKronUnitary (s t : ZMod d) :
    unitary (Matrix (ZMod d × m) (ZMod d × m) ℂ) :=
  ⟨weyl d s t ⊗ₖ (1 : Matrix m m ℂ),
    weylKron_star_mul_self s t,
    mul_eq_one_comm.mp (weylKron_star_mul_self s t)⟩

/-- Conjugation by a Weyl-with-identity unitary. -/
noncomputable def weylConj (s t : ZMod d)
    (X : Matrix (ZMod d × m) (ZMod d × m) ℂ) :
    Matrix (ZMod d × m) (ZMod d × m) ℂ :=
  (weyl d s t ⊗ₖ (1 : Matrix m m ℂ)) * X *
    star (weyl d s t ⊗ₖ (1 : Matrix m m ℂ))

theorem weylConj_isHermitian (s t : ZMod d)
    {X : Matrix (ZMod d × m) (ZMod d × m) ℂ} (hX : X.IsHermitian) :
    (weylConj s t X).IsHermitian := by
  unfold weylConj Matrix.IsHermitian
  rw [← Matrix.star_eq_conjTranspose, star_mul, star_mul, star_star]
  rw [show star X = X from hX.eq]
  rw [Matrix.mul_assoc]

set_option maxHeartbeats 3200000 in -- character-orthogonality collapse
/-- **The Weyl twirl**: the environment partial trace is the `d²`-fold
average of the Weyl unitary conjugations. -/
theorem weyl_twirl (X : Matrix (ZMod d × m) (ZMod d × m) ℂ) :
    (((d : ℝ) ^ 2)⁻¹ • ∑ s : ZMod d, ∑ t : ZMod d, weylConj s t X) =
      ((d : ℝ))⁻¹ • ((1 : Matrix (ZMod d) (ZMod d) ℂ) ⊗ₖ envTrace X) := by
  have hd0 : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  ext ⟨i, a⟩ ⟨j, b⟩
  have hentry : ∀ s t : ZMod d,
      weylConj s t X (i, a) (j, b) =
        ZMod.stdAddChar (t * (i - j)) * X (i - s, a) (j - s, b) := by
    intro s t
    unfold weylConj
    have hAX : ∀ r, ((weyl d s t ⊗ₖ (1 : Matrix m m ℂ)) * X) (i, a) r =
        ZMod.stdAddChar (t * (i - s)) * X (i - s, a) r := by
      intro r
      rw [Matrix.mul_apply, Finset.sum_eq_single ((i - s, a) : ZMod d × m)]
      · rw [weylKron_apply]
        rw [if_pos ⟨by rw [sub_add_cancel], rfl⟩]
      · intro w _ hw
        rw [weylKron_apply, if_neg, zero_mul]
        intro hcond
        apply hw
        rcases w with ⟨w1, w2⟩
        obtain ⟨h1, h2⟩ := hcond
        simp only at h1 h2
        subst h2
        have hw1 : w1 = i - s := eq_sub_of_add_eq h1.symm
        rw [hw1]
      · intro habs
        exact absurd (Finset.mem_univ _) habs
    rw [Matrix.mul_apply, Finset.sum_eq_single ((j - s, b) : ZMod d × m)]
    · rw [hAX, Matrix.star_apply, weylKron_apply]
      rw [if_pos ⟨by rw [sub_add_cancel], rfl⟩]
      rw [stdAddChar_star]
      have hphase : ZMod.stdAddChar (t * (i - s)) *
          ZMod.stdAddChar (-(t * (j - s))) =
          ZMod.stdAddChar (t * (i - j)) := by
        rw [← AddChar.map_add_eq_mul]
        congr 1
        ring
      calc ZMod.stdAddChar (t * (i - s)) * X (i - s, a) (j - s, b) *
            ZMod.stdAddChar (-(t * (j - s)))
          = ZMod.stdAddChar (t * (i - s)) *
              ZMod.stdAddChar (-(t * (j - s))) *
              X (i - s, a) (j - s, b) := by ring
        _ = ZMod.stdAddChar (t * (i - j)) * X (i - s, a) (j - s, b) := by
            rw [hphase]
    · intro r _ hr
      rw [Matrix.star_apply, weylKron_apply, if_neg, star_zero, mul_zero]
      intro hcond
      apply hr
      rcases r with ⟨r1, r2⟩
      obtain ⟨h1, h2⟩ := hcond
      simp only at h1 h2
      subst h2
      have hr1 : r1 = j - s := eq_sub_of_add_eq h1.symm
      rw [hr1]
    · intro habs
      exact absurd (Finset.mem_univ _) habs
  rw [Matrix.smul_apply, Matrix.smul_apply, Matrix.sum_apply]
  simp only [Matrix.sum_apply, hentry]
  have hsum_t : ∀ s : ZMod d,
      ∑ t : ZMod d, ZMod.stdAddChar (t * (i - j)) *
        X (i - s, a) (j - s, b) =
      (if i - j = 0 then (d : ℂ) else 0) * X (i - s, a) (j - s, b) := by
    intro s
    rw [← Finset.sum_mul, stdAddChar_sum_eq]
  simp only [hsum_t]
  rw [Matrix.kronecker_apply, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij
    simp only [sub_self, if_true]
    have hre : ∑ s : ZMod d, (d : ℂ) * X (i - s, a) (i - s, b) =
        (d : ℂ) * ∑ k : ZMod d, X (k, a) (k, b) := by
      rw [← Finset.mul_sum]
      congr 1
      exact Fintype.sum_equiv (Equiv.subLeft i)
        (fun s => X (i - s, a) (i - s, b)) (fun k => X (k, a) (k, b))
        (fun s => rfl)
    rw [hre]
    have henv : envTrace X a b = ∑ k : ZMod d, X (k, a) (k, b) := rfl
    rw [← henv, Complex.real_smul, Complex.real_smul]
    push_cast
    field_simp
  · have hij0 : ¬ i - j = 0 := sub_ne_zero_of_ne hij
    simp only [if_neg hij0, if_neg hij, zero_mul, Finset.sum_const_zero,
      smul_zero]

/-- **Partial-trace monotonicity from the joint-convexity interface**: joint
convexity of the relative entropy at the Weyl family, together with the
proved twirl identity, ancilla transport and unitary invariance, gives
monotonicity under the environment partial trace. -/
theorem relEntropy_envTrace_le_of_jointConvexity
    {X Y : Matrix (ZMod d × m) (ZMod d × m) ℂ}
    (hX : X.IsHermitian) (hY : Y.IsHermitian)
    (hEX : (envTrace X).PosSemidef) (hEY : (envTrace Y).PosDef)
    (havgX : (((d : ℝ) ^ 2)⁻¹ •
      ∑ s : ZMod d, ∑ t : ZMod d, weylConj s t X).IsHermitian)
    (havgY : (((d : ℝ) ^ 2)⁻¹ •
      ∑ s : ZMod d, ∑ t : ZMod d, weylConj s t Y).IsHermitian)
    (h1X : (((d : ℝ))⁻¹ •
      ((1 : Matrix (ZMod d) (ZMod d) ℂ) ⊗ₖ envTrace X)).IsHermitian)
    (h1Y : (((d : ℝ))⁻¹ •
      ((1 : Matrix (ZMod d) (ZMod d) ℂ) ⊗ₖ envTrace Y)).IsHermitian)
    (hjc : relEntropy havgX havgY ≤ ((d : ℝ) ^ 2)⁻¹ *
      ∑ s : ZMod d, ∑ t : ZMod d,
        relEntropy (weylConj_isHermitian s t hX)
          (weylConj_isHermitian s t hY)) :
    relEntropy hEX.1 hEY.1 ≤ relEntropy hX hY := by
  have hdpos : (0 : ℝ) < (d : ℝ) :=
    Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne d))
  have hL : relEntropy havgX havgY = relEntropy h1X h1Y :=
    relEntropy_congr (weyl_twirl X) (weyl_twirl Y) havgX havgY h1X h1Y
  have hK : relEntropy h1X h1Y =
      (((d : ℝ))⁻¹ * Fintype.card (ZMod d)) * relEntropy hEX.1 hEY.1 :=
    relEntropy_smul_kron_one hEX hEY (inv_pos.mpr hdpos) h1X h1Y
  have hcard : (((d : ℝ))⁻¹ * (Fintype.card (ZMod d) : ℝ)) = 1 := by
    rw [ZMod.card]
    field_simp
  have hR : ∀ s t : ZMod d,
      relEntropy (weylConj_isHermitian s t hX)
        (weylConj_isHermitian s t hY) = relEntropy hX hY := by
    intro s t
    exact relEntropy_unitary hX hY (weylKronUnitary s t)
      (weylConj_isHermitian s t hX) (weylConj_isHermitian s t hY)
  rw [hL, hK, hcard, one_mul] at hjc
  refine hjc.trans (le_of_eq ?_)
  simp only [hR, Finset.sum_const, Finset.card_univ, ZMod.card,
    nsmul_eq_mul]
  field_simp

end Petz
end NCG
