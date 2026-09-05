/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Type-lifted protection and the type–age predictive quotient
  (`thm:type-absent-protection`, `thm:type-age-quotient`,
   SM_emergence)

* `dressedTerm` / `dressed_term_lifted` — when the edge transition
  factors as `P̃ = ι·π`, every term of the dressed renewal
  (Neumann) series with arbitrary age-diagonal insertions lies in
  the type-lifted subspace `ι(ℂ^V)·π`;
* `type_absent_protection` / `type_absent_protection_sum` — a
  carrier character orthogonal to the type lift therefore has
  identically zero self-energy term by term, hence to all orders;
* `residual_law_separates_ages` — the conditional residual-life
  law `r ↦ q(a+r)/S(a)` distinguishes ages under strictly
  age-dependent hazards;
* `type_age_quotient` — two pasts have the same predictive law iff
  they share current type and elapsed age: the predictive quotient
  is `{(x, a)}` (the history component is provably ignored).

The identification of the age-diagonal insertions and the mark-law
separation are the declared model inputs (hypotheses `A`, `hmark`,
`hstrict`).
-/

namespace NCG

open Matrix

variable {E V : Type*} [Fintype E] [Fintype V]

/-- Terms of the dressed renewal (Neumann) series for a factored
edge transition `P̃ = ι·π`, with arbitrary age-diagonal renewal
insertions `A k` between consecutive transitions. -/
noncomputable def dressedTerm (iota : Matrix E V ℂ)
    (pi : Matrix V E ℂ) (A : ℕ → Matrix E E ℂ) : ℕ → Matrix E E ℂ
  | 0 => iota * pi
  | k + 1 => dressedTerm iota pi A k * (A k * (iota * pi))

/-- Every dressed Neumann term lies in the type-lifted subspace:
`P̃·A₀·P̃⋯P̃ = ι·B·π` for some type-space matrix `B`. -/
theorem dressed_term_lifted (iota : Matrix E V ℂ)
    (pi : Matrix V E ℂ) (A : ℕ → Matrix E E ℂ) :
    ∀ k, ∃ B : Matrix V V ℂ,
      dressedTerm iota pi A k = iota * B * pi := by
  letI : DecidableEq V := Classical.decEq V
  intro k
  induction k with
  | zero => exact ⟨1, by simp [dressedTerm]⟩
  | succ k ih =>
      obtain ⟨B, hB⟩ := ih
      refine ⟨B * pi * A k * iota, ?_⟩
      rw [dressedTerm, hB]
      simp only [Matrix.mul_assoc]

/-- `thm:type-absent-protection` (term by term): a carrier
character orthogonal to the type lift has vanishing self-energy in
every dressed Neumann order. -/
theorem type_absent_protection (iota : Matrix E V ℂ)
    (pi : Matrix V E ℂ) (A : ℕ → Matrix E E ℂ) (chi : E → ℂ)
    (hchi : Matrix.vecMul (star chi) iota = 0) :
    ∀ k, star chi ⬝ᵥ (dressedTerm iota pi A k).mulVec chi = 0 := by
  intro k
  obtain ⟨B, hB⟩ := dressed_term_lifted iota pi A k
  rw [hB, Matrix.mul_assoc, Matrix.dotProduct_mulVec,
    ← Matrix.vecMul_vecMul, hchi, Matrix.zero_vecMul,
    zero_dotProduct]

/-- `thm:type-absent-protection` (all orders): every finite partial
sum of the dressed series, with arbitrary scalar coefficients, has
vanishing character self-energy. -/
theorem type_absent_protection_sum (iota : Matrix E V ℂ)
    (pi : Matrix V E ℂ) (A : ℕ → Matrix E E ℂ) (chi : E → ℂ)
    (hchi : Matrix.vecMul (star chi) iota = 0) (c : ℕ → ℂ)
    (N : ℕ) :
    star chi ⬝ᵥ (∑ k ∈ Finset.range N,
      c k • dressedTerm iota pi A k).mulVec chi = 0 := by
  rw [Matrix.sum_mulVec, dotProduct_sum]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [Matrix.smul_mulVec, dotProduct_smul,
    type_absent_protection iota pi A chi hchi k, smul_zero]

/-- Strictly age-dependent hazards separate ages: equality of the
conditional residual-life laws `r ↦ q(a+r)/S(a)` forces equal
elapsed ages. -/
theorem residual_law_separates_ages (q S : ℕ → ℝ)
    (hS : ∀ a, S a ≠ 0)
    (hstrict : ∀ a b : ℕ, a < b →
      q (a + 1) * S b ≠ q (b + 1) * S a)
    {a b : ℕ}
    (h : (fun r => q (a + r) / S a) = fun r => q (b + r) / S b) :
    a = b := by
  have h1 : q (a + 1) / S a = q (b + 1) / S b := congrFun h 1
  rw [div_eq_div_iff (hS a) (hS b)] at h1
  rcases lt_trichotomy a b with hab | heq | hba
  · exact absurd h1 (hstrict a b hab)
  · exact heq
  · exact absurd h1.symm (hstrict b a hba)

/-- The (type, age) future law of a Markov-renewal past: the type
mark law paired with the conditional residual-life law. -/
noncomputable def typeAgeFutureLaw {V M : Type*} (d : V → ℕ)
    (q S : ℕ → ℕ → ℝ) (mark : V → M → ℝ) (x : V) (a : ℕ) :
    (M → ℝ) × (ℕ → ℝ) :=
  (mark x, fun r => q (d x) (a + r) / S (d x) a)

/-- `thm:type-age-quotient`: for the Markov-renewal process, two
pasts have the same future law iff they share current type and
elapsed age — the predictive quotient is `{(x, a)}`.  The history
component `H` of a past is provably ignored. -/
theorem type_age_quotient {H V M : Type*} (d : V → ℕ)
    (q S : ℕ → ℕ → ℝ) (mark : V → M → ℝ)
    (hS : ∀ n a, S n a ≠ 0)
    (hstrict : ∀ n, ∀ a b : ℕ, a < b →
      q n (a + 1) * S n b ≠ q n (b + 1) * S n a)
    (hmark : Function.Injective mark)
    (p p' : H × V × ℕ) :
    typeAgeFutureLaw d q S mark p.2.1 p.2.2
        = typeAgeFutureLaw d q S mark p'.2.1 p'.2.2
      ↔ p.2 = p'.2 := by
  obtain ⟨hist, x, a⟩ := p
  obtain ⟨hist', x', a'⟩ := p'
  constructor
  · intro h
    have hm : mark x = mark x' :=
      congrArg Prod.fst h
    have hx : x = x' := hmark hm
    subst hx
    have hr : (fun r => q (d x) (a + r) / S (d x) a)
        = fun r => q (d x) (a' + r) / S (d x) a' :=
      congrArg Prod.snd h
    have ha : a = a' :=
      residual_law_separates_ages (q (d x)) (S (d x))
        (hS (d x)) (hstrict (d x)) hr
    rw [ha]
  · intro h
    have hx : x = x' := congrArg Prod.fst h
    have ha : a = a' := congrArg Prod.snd h
    rw [hx, ha]

end NCG
