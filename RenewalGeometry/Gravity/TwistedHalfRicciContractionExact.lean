/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Twisted half-Ricci contraction (`lem:half-ricci`, Einstein–SM action closure)

Purely algebraic content of the lemma.  A *Clifford frame* is a finite family of
generators `c_a` in an associative real algebra together with signs `ε_a = ±1`
satisfying `c_a c_b + c_b c_a = -2 η_{ab}`, `η_{ab} = ε_a δ_{ab}`.  For a curvature
array `R_{abcd}` that is antisymmetric in each index pair and satisfies the first
Bianchi identity `R_{abcd} + R_{acdb} + R_{adbc} = 0`, the spinor curvature
`R^S_{ab} = ¼ Σ_{c,d} ε_c ε_d R_{abcd} c_c c_d` contracts as

  `Σ_b ε_b c_b R^S_{ba} = ½ Σ_b ε_b Ric_{ab} c_b`,   `Ric_{ab} = Σ_c ε_c R_{cacb}`

(`half_ricci_contraction`), and the twisted curvature
`R^∇_{ab} = R^S_{ab} + ρ(F_{ab})` contracts with the additional term
`Σ_b ε_b c_b ρ(F_{ba})` (`twisted_half_ricci_contraction`, **`eq:half-ricci`**).

The proof is the triple-product rearrangement
`c_b c_c c_d = c_c c_d c_b + 2η_{bd} c_c − 2η_{bc} c_d` applied cyclically together with
the Bianchi identity; no normal-frame choice is needed because the statement is
pointwise algebraic.  What the paper's lemma says beyond this — that `R_{abcd}` is the
Riemann tensor of the torsion-free spin connection and `ρ(F)` the gauge curvature acting
on the twisting factor — is the geometric identification, which the lemma itself takes
as its conventions.
-/

namespace RenewalGeometry.TwistedHalfRicci

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {A : Type*} [Ring A] [Algebra ℝ A]

/-- A Clifford frame: generators `c_a` with signature signs `ε_a = ±1` and the
relation `c_a c_b + c_b c_a = -2 η_{ab}`, `η_{ab} = ε_a δ_{ab}` (`lem:half-ricci`
conventions). -/
structure CliffordFrame (ι A : Type*) [DecidableEq ι] [Ring A] [Algebra ℝ A] where
  /-- the Clifford generators -/
  c : ι → A
  /-- the signature signs -/
  ε : ι → ℝ
  /-- `ε_a = ±1` -/
  sign_sq : ∀ a, ε a ^ 2 = 1
  /-- `c_a c_b + c_b c_a = -2 ε_a δ_{ab}` -/
  anticomm : ∀ a b, c a * c b + c b * c a =
    ((-2 : ℝ) * (if a = b then ε a else 0)) • (1 : A)

variable (Fr : CliffordFrame ι A)

/-- The metric `η_{ab} = ε_a δ_{ab}`. -/
def CliffordFrame.η (a b : ι) : ℝ := if a = b then Fr.ε a else 0

/-- The spinor curvature `R^S_{ab} = ¼ Σ_{c,d} ε_c ε_d R_{abcd} c_c c_d`. -/
noncomputable def spinorCurvature (R : ι → ι → ι → ι → ℝ) (a b : ι) : A :=
  (1 / 4 : ℝ) • ∑ c, ∑ d, (Fr.ε c * Fr.ε d * R a b c d) • (Fr.c c * Fr.c d)

/-- The twisted curvature `R^∇_{ab} = R^S_{ab} + ρ(F_{ab})`. -/
noncomputable def twistedCurvature (R : ι → ι → ι → ι → ℝ) (ρF : ι → ι → A) (a b : ι) : A :=
  spinorCurvature Fr R a b + ρF a b

/-- The Ricci contraction `Ric_{ab} = Σ_c ε_c R_{cabc} = R^c{}_{abc}`.  This is the
Ricci sign convention for which the paper's identity holds with the stated Clifford
sign `c_a c_b + c_b c_a = -2η_{ab}`; with the opposite contraction
`R^c{}_{acb} = Σ_c ε_c R_{cacb}` the right side of `eq:half-ricci` acquires a minus sign
(`half_ricci_contraction_opposite`). -/
def ricciOf (ε : ι → ℝ) (R : ι → ι → ι → ι → ℝ) (a b : ι) : ℝ :=
  ∑ c, ε c * R c a b c

/-- The opposite-sign Ricci convention `Σ_c ε_c R_{cacb} = R^c{}_{acb}`. -/
def ricciOpposite (ε : ι → ℝ) (R : ι → ι → ι → ι → ℝ) (a b : ι) : ℝ :=
  ∑ c, ε c * R c a c b

/-- The triple sum `Σ_{b,c,d} ε_b ε_c ε_d S_{bcd} c_b c_c c_d`. -/
noncomputable def tripleSum (S : ι → ι → ι → ℝ) : A :=
  ∑ b, ∑ c, ∑ d, (Fr.ε b * Fr.ε c * Fr.ε d * S b c d) • (Fr.c b * Fr.c c * Fr.c d)

/-- The basic rearrangement
`c_b c_c c_d = c_c c_d c_b + 2η_{bd} c_c − 2η_{bc} c_d`. -/
theorem triple_comm (b c d : ι) :
    Fr.c b * Fr.c c * Fr.c d =
      Fr.c c * Fr.c d * Fr.c b + (2 * Fr.η b d) • Fr.c c - (2 * Fr.η b c) • Fr.c d := by
  have h1 : Fr.c b * Fr.c c = ((-2 : ℝ) * Fr.η b c) • (1 : A) - Fr.c c * Fr.c b := by
    rw [eq_sub_iff_add_eq, Fr.anticomm b c]; rfl
  have h2 : Fr.c b * Fr.c d = ((-2 : ℝ) * Fr.η b d) • (1 : A) - Fr.c d * Fr.c b := by
    rw [eq_sub_iff_add_eq, Fr.anticomm b d]; rfl
  calc Fr.c b * Fr.c c * Fr.c d
      = (((-2 : ℝ) * Fr.η b c) • (1 : A) - Fr.c c * Fr.c b) * Fr.c d := by rw [h1]
    _ = ((-2 : ℝ) * Fr.η b c) • Fr.c d - Fr.c c * (Fr.c b * Fr.c d) := by
        rw [sub_mul, smul_mul_assoc, one_mul, mul_assoc]
    _ = ((-2 : ℝ) * Fr.η b c) • Fr.c d
          - Fr.c c * (((-2 : ℝ) * Fr.η b d) • (1 : A) - Fr.c d * Fr.c b) := by rw [h2]
    _ = Fr.c c * Fr.c d * Fr.c b + (2 * Fr.η b d) • Fr.c c - (2 * Fr.η b c) • Fr.c d := by
        rw [mul_sub, mul_smul_comm, mul_one, ← mul_assoc]
        have e1 : ((-2 : ℝ) * Fr.η b c) • Fr.c d = -((2 * Fr.η b c) • Fr.c d) := by
          rw [← neg_smul]; congr 1; ring
        have e2 : ((-2 : ℝ) * Fr.η b d) • Fr.c c = -((2 * Fr.η b d) • Fr.c c) := by
          rw [← neg_smul]; congr 1; ring
        rw [e1, e2]; abel

/-- Linearity of the triple sum. -/
theorem tripleSum_add (S S' : ι → ι → ι → ℝ) :
    tripleSum Fr (fun b c d => S b c d + S' b c d) = tripleSum Fr S + tripleSum Fr S' := by
  simp only [tripleSum, mul_add, add_smul, Finset.sum_add_distrib]

/-- The cyclic rearrangement of the triple sum: moving the first generator to the
last position produces the two `η`-contractions. -/
theorem tripleSum_cyclic (S : ι → ι → ι → ℝ) :
    tripleSum Fr S = tripleSum Fr (fun b c d => S d b c)
      + (2 : ℝ) • ∑ b, ∑ c, (Fr.ε b * Fr.ε c * S b c b) • Fr.c c
      - (2 : ℝ) • ∑ b, ∑ d, (Fr.ε b * Fr.ε d * S b b d) • Fr.c d := by
  have hsplit : tripleSum Fr S =
      (∑ b, ∑ c, ∑ d, (Fr.ε b * Fr.ε c * Fr.ε d * S b c d) • (Fr.c c * Fr.c d * Fr.c b))
      + (∑ b, ∑ c, ∑ d, (Fr.ε b * Fr.ε c * Fr.ε d * S b c d) • ((2 * Fr.η b d) • Fr.c c))
      - (∑ b, ∑ c, ∑ d, (Fr.ε b * Fr.ε c * Fr.ε d * S b c d) • ((2 * Fr.η b c) • Fr.c d)) := by
    unfold tripleSum
    simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
      Finset.sum_congr rfl fun d _ => ?_
    rw [triple_comm Fr b c d, smul_sub, smul_add]
  have hcyc : (∑ b, ∑ c, ∑ d, (Fr.ε b * Fr.ε c * Fr.ε d * S b c d) • (Fr.c c * Fr.c d * Fr.c b))
      = tripleSum Fr (fun b c d => S d b c) := by
    unfold tripleSum
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun b _ => ?_
    congr 1; ring
  have hbd : (∑ b, ∑ c, ∑ d, (Fr.ε b * Fr.ε c * Fr.ε d * S b c d) • ((2 * Fr.η b d) • Fr.c c))
      = (2 : ℝ) • ∑ b, ∑ c, (Fr.ε b * Fr.ε c * S b c b) • Fr.c c := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [CliffordFrame.η, smul_smul, mul_ite, mul_zero, ite_smul, zero_smul,
      smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    congr 1
    have := Fr.sign_sq b
    linear_combination (2 * Fr.ε c * S b c b * Fr.ε b) * this
  have hbc : (∑ b, ∑ c, ∑ d, (Fr.ε b * Fr.ε c * Fr.ε d * S b c d) • ((2 * Fr.η b c) • Fr.c d))
      = (2 : ℝ) • ∑ b, ∑ d, (Fr.ε b * Fr.ε d * S b b d) • Fr.c d := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_comm, Finset.smul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    simp only [CliffordFrame.η, smul_smul, mul_ite, mul_zero, ite_smul, zero_smul,
      smul_ite, smul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    congr 1
    have := Fr.sign_sq b
    linear_combination (2 * Fr.ε d * S b b d * Fr.ε b) * this
  rw [hsplit, hcyc, hbd, hbc]

/-- The contraction `Σ_b ε_b c_b R^S_{ba}` equals `¼` of the triple sum with
`S_{bcd} = R_{bacd}`. -/
theorem contraction_eq_tripleSum (R : ι → ι → ι → ι → ℝ) (a : ι) :
    ∑ b, Fr.ε b • (Fr.c b * spinorCurvature Fr R b a)
      = (1 / 4 : ℝ) • tripleSum Fr (fun b c d => R b a c d) := by
  unfold spinorCurvature tripleSum
  simp only [Finset.smul_sum, Finset.mul_sum, mul_smul_comm, smul_smul, ← mul_assoc]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ =>
    Finset.sum_congr rfl fun d _ => ?_
  congr 1; ring

/-- **`lem:half-ricci`, untwisted part.**  For a curvature array antisymmetric in
both index pairs and satisfying the first Bianchi identity,
`Σ_b ε_b c_b R^S_{ba} = ½ Σ_b ε_b Ric_{ab} c_b`. -/
theorem half_ricci_contraction (R : ι → ι → ι → ι → ℝ)
    (hR₁ : ∀ a b c d, R a b d c = -R a b c d)
    (hR₂ : ∀ a b c d, R b a c d = -R a b c d)
    (hBianchi : ∀ a b c d, R a b c d + R a c d b + R a d b c = 0) (a : ι) :
    ∑ b, Fr.ε b • (Fr.c b * spinorCurvature Fr R b a)
      = (1 / 2 : ℝ) • ∑ b, (Fr.ε b * ricciOf Fr.ε R a b) • Fr.c b := by
  set Q : A := ∑ b, (Fr.ε b * ricciOf Fr.ε R a b) • Fr.c b with hQ
  set T₀ := tripleSum Fr (fun b c d => R b a c d) with hT₀
  set T₁ := tripleSum Fr (fun b c d => R d a b c) with hT₁
  set T₂ := tripleSum Fr (fun b c d => R c a d b) with hT₂
  -- the two contractions appearing in the cyclic rearrangements
  have hQ₁ : (∑ b, ∑ c, (Fr.ε b * Fr.ε c * R b a c b) • Fr.c c) = Q := by
    rw [hQ, Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [ricciOf, Finset.mul_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun b _ => ?_
    congr 1; ring
  have hQ₂ : (∑ b, ∑ d, (Fr.ε b * Fr.ε d * R b a b d) • Fr.c d) = -Q := by
    rw [hQ, ← Finset.sum_neg_distrib, Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [ricciOf, Finset.mul_sum, Finset.sum_smul, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← neg_smul]; congr 1
    linear_combination (Fr.ε b * Fr.ε d) * hR₁ b a d b
  have hZ₁ : (∑ b, ∑ d, (Fr.ε b * Fr.ε d * R d a b b) • Fr.c d) = 0 := by
    refine Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun d _ => ?_
    have : R d a b b = 0 := by have := hR₁ d a b b; linarith
    rw [this]; simp
  have hZ₂ : (∑ b, ∑ c, (Fr.ε b * Fr.ε c * R c a b b) • Fr.c c) = 0 := by
    refine Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun c _ => ?_
    have : R c a b b = 0 := by have := hR₁ c a b b; linarith
    rw [this]; simp
  -- the three cyclic rearrangements
  have e₀ : T₀ = T₁ + (2 : ℝ) • Q - (2 : ℝ) • (-Q) := by
    rw [hT₀, tripleSum_cyclic, hQ₁, hQ₂]
  have e₁ : T₁ = T₂ + (2 : ℝ) • (-Q) - (2 : ℝ) • (0 : A) := by
    rw [hT₁, tripleSum_cyclic]
    have h1 : (∑ b, ∑ c, (Fr.ε b * Fr.ε c * R b a b c) • Fr.c c) = -Q := by
      rw [hQ, ← Finset.sum_neg_distrib, Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [ricciOf, Finset.mul_sum, Finset.sum_smul, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [← neg_smul]; congr 1
      linear_combination (Fr.ε b * Fr.ε c) * hR₁ b a c b
    rw [h1, hZ₁]
  have e₂ : T₂ = T₀ + (2 : ℝ) • (0 : A) - (2 : ℝ) • Q := by
    rw [hT₂, tripleSum_cyclic]
    have h1 : (∑ b, ∑ d, (Fr.ε b * Fr.ε d * R b a d b) • Fr.c d) = Q := by
      rw [hQ, Finset.sum_comm]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [ricciOf, Finset.mul_sum, Finset.sum_smul]
      refine Finset.sum_congr rfl fun b _ => ?_
      congr 1; ring
    rw [h1, hZ₂]
  -- the Bianchi identity in the needed form
  have hsum : T₀ + T₁ + T₂ = 0 := by
    rw [hT₀, hT₁, hT₂, ← tripleSum_add, ← tripleSum_add]
    have : (fun b c d => R b a c d + R d a b c + R c a d b) = fun _ _ _ => (0 : ℝ) := by
      funext b c d
      have h := hBianchi a b c d
      linear_combination hR₂ a b c d + hR₂ a d b c + hR₂ a c d b - h
    rw [this]
    simp [tripleSum]
  have hT : T₀ = (2 : ℝ) • Q := by
    have h3 : (3 : ℝ) • T₀ = (6 : ℝ) • Q := by
      linear_combination (norm := module) hsum + (2 : ℝ) • e₀ + e₁
    have h := congrArg (fun x => (1 / 3 : ℝ) • x) h3
    simp only [smul_smul] at h
    norm_num at h
    exact h
  rw [contraction_eq_tripleSum, ← hT₀, hT, smul_smul]
  norm_num

/-- The same contraction in the opposite Ricci convention `R^c{}_{acb}`: the right side
of `eq:half-ricci` changes sign. -/
theorem half_ricci_contraction_opposite (R : ι → ι → ι → ι → ℝ)
    (hR₁ : ∀ a b c d, R a b d c = -R a b c d)
    (hR₂ : ∀ a b c d, R b a c d = -R a b c d)
    (hBianchi : ∀ a b c d, R a b c d + R a c d b + R a d b c = 0) (a : ι) :
    ∑ b, Fr.ε b • (Fr.c b * spinorCurvature Fr R b a)
      = -((1 / 2 : ℝ) • ∑ b, (Fr.ε b * ricciOpposite Fr.ε R a b) • Fr.c b) := by
  rw [half_ricci_contraction Fr R hR₁ hR₂ hBianchi a, ← smul_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← neg_smul]; congr 1
  rw [ricciOf, ricciOpposite, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  linear_combination (Fr.ε b * Fr.ε c) * hR₁ c a b c

/-- **`lem:half-ricci` (`eq:half-ricci`).**  With the twisted curvature
`R^∇_{ab} = R^S_{ab} + ρ(F_{ab})`,
`Σ_b ε_b c_b R^∇_{ba} = ½ Σ_b ε_b Ric_{ab} c_b + Σ_b ε_b c_b ρ(F_{ba})`. -/
theorem twisted_half_ricci_contraction (R : ι → ι → ι → ι → ℝ) (ρF : ι → ι → A)
    (hR₁ : ∀ a b c d, R a b d c = -R a b c d)
    (hR₂ : ∀ a b c d, R b a c d = -R a b c d)
    (hBianchi : ∀ a b c d, R a b c d + R a c d b + R a d b c = 0) (a : ι) :
    ∑ b, Fr.ε b • (Fr.c b * twistedCurvature Fr R ρF b a)
      = (1 / 2 : ℝ) • (∑ b, (Fr.ε b * ricciOf Fr.ε R a b) • Fr.c b)
        + ∑ b, Fr.ε b • (Fr.c b * ρF b a) := by
  rw [← half_ricci_contraction Fr R hR₁ hR₂ hBianchi a, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [twistedCurvature, mul_add, smul_add]

end RenewalGeometry.TwistedHalfRicci
