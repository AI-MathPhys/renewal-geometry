/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.StandardModel.ReciprocalReturnMassExact

/-!
# The finite reciprocal-return criterion: the route bank

Completes `thm:reciprocal-return` of the spacetime–gauge duality paper on top of
`ReciprocalReturnMassExact` (mass identity, (ii) ⇔ (iii), finite-horizon (iv)).

The **declared route bank** is encoded as words (lists) in the letters acting on the
carrier `T ⊕ E ⊕ H_priv`, `E = V ⊗ N`:

* `entry g` — `A_g = (v_g ⊗ I) A : T → E`, and its adjoint `entryAdj g`;
* `exit g` — `B_g^* = B^* (v_g^* ⊗ I) : E → H_priv`, and its adjoint `exitAdj g`;
* `dyn` — the mediator dynamics `D = I_V ⊗ h : E → E` (self-adjoint);
* `localT X`, `localH Y` — arbitrary operations inside `T` and inside `H_priv`
  (the represented private support words live here).

A word acts by composition (`wordAct`, rightmost letter first); it *has a colour
bridge* when its `H_priv ← T` corner is nonzero (`HasBridge`).

* `word_hasBridge`: the returned word `r_{g,k}` is the bank word
  `B_1^* D^k A_g` of `k + 2` letters, so (ii) ⇒ (i) with the witness length `≤ n + 1`;
* `partialGram_pow_mul_eq_zero_all`: Cayley–Hamilton extends clause (iv) from the
  horizon `k < n = dim N` to all `k`;
* `word_eq_zero_all`: at horizon `n = dim N`, `m_ret = 0` forces `r_{g,k} = 0` for
  **every** `k`;
* `reducingSubspace`, `reducingSubspace_invariant`: the explicit subspace
  `T ⊕ 𝒦 ⊕ 0` (with `𝒦 = ⋂_{g,k} Ker B^*(v_g^* ⊗ h^k)`, which contains
  `V ⊗ Ran W_A`), invariant under every letter — the letter set is closed under
  adjoints, so this is a reducing subspace — containing `T` and annihilated by the
  `H_priv` coordinate;
* `no_bridge_of_mass_eq_zero`: (i) fails when `m_ret = 0`, for every word of the bank;
* `reciprocal_return_criterion`: **the theorem** — the boxed identity, `m_ret ≥ 0`,
  the equivalence of (i), (ii), (iii), (iv), the reducing subspace, and the
  witness-length bound `n + 1`.

Scoped hypotheses as in `ReciprocalReturnMassExact`: finite index types, `V` nonempty,
irreducibility in the Schur (scalar-commutant) form, `h` self-adjoint, horizon
`n = Fintype.card N`.
-/

open Matrix Kronecker
open scoped ComplexOrder

namespace RenewalGeometry
namespace ReciprocalReturnBank

open ReciprocalReturn ReciprocalReturnMass

noncomputable section

section Letters

variable (V N T H : Type*)

/-- The letters of the declared route bank on `T ⊕ (V ⊗ N) ⊕ H_priv`. -/
inductive Letter (T H G : Type*)
  /-- `A_g = (v_g ⊗ I) A : T → E`. -/
  | entry (g : G)
  /-- `A_g^* : E → T`. -/
  | entryAdj (g : G)
  /-- `B_g^* = B^* (v_g^* ⊗ I) : E → H_priv`. -/
  | exit (g : G)
  /-- `B_g : H_priv → E`. -/
  | exitAdj (g : G)
  /-- `D = I_V ⊗ h : E → E`. -/
  | dyn
  /-- An operation inside `T`. -/
  | localT (X : Matrix T T ℂ)
  /-- An operation inside `H_priv` (e.g. a represented private support word). -/
  | localH (Y : Matrix H H ℂ)

/-- The carrier `T ⊕ E ⊕ H_priv` as triples of coordinate vectors. -/
abbrev Carrier := (T → ℂ) × ((V × N) → ℂ) × (H → ℂ)

end Letters

variable {V N T H G : Type*} [Fintype V] [Fintype N] [Fintype T] [Fintype H] [Fintype G]
  [DecidableEq V] [DecidableEq N] [DecidableEq T] [Group G]

variable (v : G → Matrix V V ℂ) (h : Matrix N N ℂ) (A : Matrix (V × N) T ℂ)
  (B : Matrix (V × N) H ℂ)

/-- The action of one letter on the carrier. -/
def letterAct : Letter T H G → Carrier V N T H → Carrier V N T H
  | .entry g, x => (0, (v g ⊗ₖ (1 : Matrix N N ℂ)) *ᵥ (A *ᵥ x.1), 0)
  | .entryAdj g, x => (Aᴴ *ᵥ (((v g)ᴴ ⊗ₖ (1 : Matrix N N ℂ)) *ᵥ x.2.1), 0, 0)
  | .exit g, x => (0, 0, Bᴴ *ᵥ (((v g)ᴴ ⊗ₖ (1 : Matrix N N ℂ)) *ᵥ x.2.1))
  | .exitAdj g, x => (0, (v g ⊗ₖ (1 : Matrix N N ℂ)) *ᵥ (B *ᵥ x.2.2), 0)
  | .dyn, x => (0, ((1 : Matrix V V ℂ) ⊗ₖ h) *ᵥ x.2.1, 0)
  | .localT X, x => (X *ᵥ x.1, 0, 0)
  | .localH Y, x => (0, 0, Y *ᵥ x.2.2)

/-- The action of a word (rightmost letter first). -/
def wordAct : List (Letter T H G) → Carrier V N T H → Carrier V N T H
  | [], x => x
  | l :: w, x => letterAct v h A B l (wordAct w x)

/-- A word of the bank has a nonzero `H_priv ← T` corner. -/
def HasBridge (w : List (Letter T H G)) : Prop :=
  ∃ t : T → ℂ, (wordAct v h A B w (t, 0, 0)).2.2 ≠ 0

theorem wordAct_append (w₁ w₂ : List (Letter T H G)) (x : Carrier V N T H) :
    wordAct v h A B (w₁ ++ w₂) x = wordAct v h A B w₁ (wordAct v h A B w₂ x) := by
  induction w₁ with
  | nil => rfl
  | cons l w ih => simp [wordAct, ih]

/-! ### (ii) ⇒ (i): the returned words are bank words of length `k + 2` -/

theorem one_kronecker_pow (k : ℕ) :
    ((1 : Matrix V V ℂ) ⊗ₖ h) ^ k = (1 : Matrix V V ℂ) ⊗ₖ (h ^ k) := by
  induction k with
  | zero => simp [Matrix.one_kronecker_one]
  | succ k ih => rw [pow_succ, ih, ← Matrix.mul_kronecker_mul, Matrix.one_mul, pow_succ]

theorem wordAct_replicate_dyn (k : ℕ) (e : (V × N) → ℂ) :
    wordAct v h A B (List.replicate k .dyn) (0, e, 0) =
      (0, ((1 : Matrix V V ℂ) ⊗ₖ (h ^ k)) *ᵥ e, 0) := by
  induction k with
  | zero => simp [wordAct, Matrix.one_kronecker_one]
  | succ k ih =>
    rw [List.replicate_succ, wordAct, ih]
    simp only [letterAct, Matrix.mulVec_mulVec]
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul, pow_succ']

/-- The returned word `r_{g,k}` is the `H_priv ← T` corner of the bank word
`B_1^* D^k A_g` (`k + 2` letters). -/
theorem wordAct_returnWord (hone : v 1 = 1) (g : G) (k : ℕ) (t : T → ℂ) :
    wordAct v h A B (.exit 1 :: (List.replicate k .dyn ++ [.entry g])) (t, 0, 0) =
      (0, 0, word v h A B g k *ᵥ t) := by
  rw [wordAct, wordAct_append]
  simp only [wordAct, letterAct]
  rw [wordAct_replicate_dyn]
  simp only [letterAct, Matrix.mulVec_mulVec, hone, Matrix.conjTranspose_one,
    Matrix.one_kronecker_one, Matrix.one_mul]
  simp only [← Matrix.mul_assoc]
  rw [Matrix.mul_assoc Bᴴ, ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one, word]

/-- **(ii) ⇒ (i)** with the length bound: a nonzero returned word `r_{g,k}` gives a bank
word with a colour bridge and `k + 2` letters. -/
theorem word_hasBridge (hone : v 1 = 1) (g : G) (k : ℕ) (hw : word v h A B g k ≠ 0) :
    HasBridge v h A B (.exit 1 :: (List.replicate k .dyn ++ [.entry g])) ∧
      (.exit 1 :: (List.replicate k .dyn ++ [.entry g]) :
        List (Letter T H G)).length = k + 2 := by
  refine ⟨?_, by simp⟩
  by_contra hall
  unfold HasBridge at hall
  push_neg at hall
  apply hw
  ext i j
  have := congrFun (hall (Pi.single j 1)) i
  rw [wordAct_returnWord v h A B hone, Matrix.mulVec_single_one] at this
  simpa using this

/-! ### Cayley–Hamilton: clause (iv) beyond the horizon -/

/-- If `ρ_B h^k ρ_A = 0` for all `k < dim N`, then for all `k`. -/
theorem partialGram_pow_mul_eq_zero_all
    (hall : ∀ k : Fin (Fintype.card N), partialGram B * h ^ (k : ℕ) * partialGram A = 0) :
    ∀ k : ℕ, partialGram B * h ^ k * partialGram A = 0 := by
  intro k
  rcases isEmpty_or_nonempty N with hN | hN
  · exact Subsingleton.elim _ _
  have hdeg : (Polynomial.X ^ k %ₘ h.charpoly).natDegree < Fintype.card N := by
    have h1 := Polynomial.natDegree_modByMonic_lt (Polynomial.X ^ k) (Matrix.charpoly_monic h)
      (by
        intro hc
        have := Matrix.charpoly_natDegree_eq_dim h
        rw [hc, Polynomial.natDegree_one] at this
        exact (Fintype.card_pos (α := N)).ne this)
    rwa [Matrix.charpoly_natDegree_eq_dim] at h1
  rw [Matrix.pow_eq_aeval_mod_charpoly, Polynomial.aeval_eq_sum_range' hdeg, Matrix.mul_sum,
    Matrix.sum_mul]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [Matrix.mul_smul, Matrix.smul_mul, hall ⟨i, hi⟩, smul_zero]

/-- At horizon `n = dim N`, vanishing mass forces every returned word to vanish, at
every `k ∈ ℕ`. -/
theorem word_eq_zero_all [Nonempty V]
    (hmul : ∀ g g', v (g * g') = v g * v g') (hone : v 1 = 1)
    (hunit : ∀ g, (v g)ᴴ * v g = 1)
    (hirr : ∀ X : Matrix V V ℂ, (∀ g, X * v g = v g * X) → ∃ c : ℂ, X = c • 1)
    (hh : hᴴ = h) (hmass : mass v h A B (Fintype.card N) = 0) :
    ∀ (g : G) (k : ℕ), word v h A B g k = 0 := by
  intro g k
  have hall := partialGram_pow_mul_eq_zero_all h A B
    ((mass_eq_zero_iff v h A B hmul hone hunit hirr hh _).mp hmass)
  have hk : mass v h A B (k + 1) = 0 :=
    (mass_eq_zero_iff v h A B hmul hone hunit hirr hh (k + 1)).mpr fun j => hall j
  by_contra hne
  have := (mass_pos_iff v h A B (k + 1)).mpr ⟨g, ⟨k, Nat.lt_succ_self k⟩, hne⟩
  rw [hk] at this
  exact lt_irrefl _ this

/-! ### The reducing subspace -/

/-- `𝒦 = ⋂_{g, k} Ker (B^* (v_g^* ⊗ h^k)) ⊆ E`: the mediator vectors from which no
return word reaches `H_priv`.  It contains `V ⊗ Ran W_A` when the return words vanish. -/
def mediatorKer : Submodule ℂ ((V × N) → ℂ) :=
  ⨅ (g : G) (k : ℕ), LinearMap.ker (Bᴴ * ((v g)ᴴ ⊗ₖ (h ^ k))).mulVecLin

theorem mem_mediatorKer {e : (V × N) → ℂ} :
    e ∈ mediatorKer v h B ↔
      ∀ (g : G) (k : ℕ), Bᴴ *ᵥ (((v g)ᴴ ⊗ₖ (h ^ k)) *ᵥ e) = 0 := by
  simp only [mediatorKer, Submodule.mem_iInf, LinearMap.mem_ker, Matrix.mulVecLin_apply,
    Matrix.mulVec_mulVec]

/-- The explicit subspace `T ⊕ 𝒦 ⊕ 0` of the carrier. -/
def reducingSubspace : Submodule ℂ (Carrier V N T H) :=
  Submodule.prod ⊤ (Submodule.prod (mediatorKer v h B) ⊥)

theorem mem_reducingSubspace {x : Carrier V N T H} :
    x ∈ reducingSubspace v h B ↔ x.2.1 ∈ mediatorKer v h B ∧ x.2.2 = 0 := by
  simp [reducingSubspace, Submodule.mem_prod]

/-- `T` lies in the reducing subspace. -/
theorem T_mem_reducingSubspace (t : T → ℂ) :
    ((t, 0, 0) : Carrier V N T H) ∈ reducingSubspace v h B := by
  rw [mem_reducingSubspace]
  exact ⟨Submodule.zero_mem _, rfl⟩

/-- **Invariance of the reducing subspace** under every letter of the bank (hence under
every letter's adjoint, the letter set being adjoint-closed), provided all returned
words vanish. -/
theorem reducingSubspace_invariant
    (hmul : ∀ g g', v (g * g') = v g * v g') (hone : v 1 = 1)
    (hunit : ∀ g, (v g)ᴴ * v g = 1)
    (hzero : ∀ (g : G) (k : ℕ), word v h A B g k = 0)
    (l : Letter T H G) (x : Carrier V N T H) (hx : x ∈ reducingSubspace v h B) :
    letterAct v h A B l x ∈ reducingSubspace v h B := by
  rw [mem_reducingSubspace] at hx ⊢
  obtain ⟨hE, hH⟩ := hx
  rw [mem_mediatorKer] at hE
  cases l with
  | entry g₀ =>
    refine ⟨?_, rfl⟩
    rw [mem_mediatorKer]
    intro g k
    simp only [letterAct, Matrix.mulVec_mulVec]
    simp only [← Matrix.mul_assoc]
    rw [Matrix.mul_assoc Bᴴ, ← Matrix.mul_kronecker_mul, Matrix.mul_one,
      conjTranspose_eq_inv v hmul hone hunit, ← hmul]
    have hw := hzero (g⁻¹ * g₀) k
    rw [word] at hw
    rw [hw, Matrix.zero_mulVec]
  | entryAdj g₀ =>
    exact ⟨Submodule.zero_mem _, rfl⟩
  | exit g₀ =>
    refine ⟨Submodule.zero_mem _, ?_⟩
    have := hE g₀ 0
    rw [pow_zero] at this
    simpa [letterAct] using this
  | exitAdj g₀ =>
    refine ⟨?_, rfl⟩
    simp only [letterAct, hH, Matrix.mulVec_zero]
    exact Submodule.zero_mem _
  | dyn =>
    refine ⟨?_, rfl⟩
    rw [mem_mediatorKer]
    intro g k
    simp only [letterAct, Matrix.mulVec_mulVec]
    rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, ← pow_succ, ← Matrix.mulVec_mulVec]
    exact hE g (k + 1)
  | localT X =>
    exact ⟨Submodule.zero_mem _, rfl⟩
  | localH Y =>
    refine ⟨Submodule.zero_mem _, ?_⟩
    simp [letterAct, hH]

theorem wordAct_mem_reducingSubspace
    (hmul : ∀ g g', v (g * g') = v g * v g') (hone : v 1 = 1)
    (hunit : ∀ g, (v g)ᴴ * v g = 1)
    (hzero : ∀ (g : G) (k : ℕ), word v h A B g k = 0)
    (w : List (Letter T H G)) (x : Carrier V N T H) (hx : x ∈ reducingSubspace v h B) :
    wordAct v h A B w x ∈ reducingSubspace v h B := by
  induction w with
  | nil => exact hx
  | cons l w ih => exact reducingSubspace_invariant v h A B hmul hone hunit hzero l _ ih

/-- **(i) fails when the return words vanish**: no word of the bank has a colour
bridge. -/
theorem no_bridge_of_word_eq_zero
    (hmul : ∀ g g', v (g * g') = v g * v g') (hone : v 1 = 1)
    (hunit : ∀ g, (v g)ᴴ * v g = 1)
    (hzero : ∀ (g : G) (k : ℕ), word v h A B g k = 0)
    (w : List (Letter T H G)) : ¬ HasBridge v h A B w := by
  rintro ⟨t, ht⟩
  apply ht
  exact ((mem_reducingSubspace v h B).mp
    (wordAct_mem_reducingSubspace v h A B hmul hone hunit hzero w _
      (T_mem_reducingSubspace v h B t))).2

/-- **(i) fails when `m_ret = 0`** at horizon `n = dim N`. -/
theorem no_bridge_of_mass_eq_zero [Nonempty V]
    (hmul : ∀ g g', v (g * g') = v g * v g') (hone : v 1 = 1)
    (hunit : ∀ g, (v g)ᴴ * v g = 1)
    (hirr : ∀ X : Matrix V V ℂ, (∀ g, X * v g = v g * X) → ∃ c : ℂ, X = c • 1)
    (hh : hᴴ = h) (hmass : mass v h A B (Fintype.card N) = 0)
    (w : List (Letter T H G)) : ¬ HasBridge v h A B w :=
  no_bridge_of_word_eq_zero v h A B hmul hone hunit
    (word_eq_zero_all v h A B hmul hone hunit hirr hh hmass) w

/-! ### The theorem -/

/-- **`thm:reciprocal-return` (finite reciprocal-return criterion)**, at horizon
`n = dim N`.  With `m_ret = |G|⁻¹ ∑_g ∑_{k<n} ‖r_{g,k}‖²_HS`:

1. the boxed identity `m_ret = d⁻¹ Tr(ρ_B W_A)` and `m_ret ≥ 0`;
2. (i) some bank word has a nonzero `H_priv ← T` corner ⇔ (ii) some `r_{g,k} ≠ 0`
   (`k < n`) ⇔ (iii) `m_ret > 0` ⇔ (iv) `Ran ρ_B` is not orthogonal to the
   `h`-cyclic space of `Ran ρ_A` (`∃ k, ρ_B h^k ρ_A ≠ 0`, equivalently with `k < n`);
3. if these fail, the explicit subspace `T ⊕ 𝒦 ⊕ 0` is invariant under every letter
   (and adjoint) of the bank, contains `T` and is annihilated by the `H_priv` coordinate;
4. if they hold, a witness word has at most `n + 1` letters. -/
theorem reciprocal_return_criterion [Nonempty V]
    (hmul : ∀ g g', v (g * g') = v g * v g') (hone : v 1 = 1)
    (hunit : ∀ g, (v g)ᴴ * v g = 1)
    (hirr : ∀ X : Matrix V V ℂ, (∀ g, X * v g = v g * X) → ∃ c : ℂ, X = c • 1)
    (hh : hᴴ = h) :
    let n := Fintype.card N
    ((mass v h A B n : ℂ) =
        (Fintype.card V : ℂ)⁻¹ * (partialGram B * returnWeight h A n).trace ∧
      0 ≤ mass v h A B n) ∧
    ((∃ w : List (Letter T H G), HasBridge v h A B w) ↔
        ∃ g : G, ∃ k : Fin n, word v h A B g k ≠ 0) ∧
    ((∃ g : G, ∃ k : Fin n, word v h A B g k ≠ 0) ↔ 0 < mass v h A B n) ∧
    (0 < mass v h A B n ↔ ∃ k : ℕ, partialGram B * h ^ k * partialGram A ≠ 0) ∧
    ((∃ k : ℕ, partialGram B * h ^ k * partialGram A ≠ 0) ↔
        ∃ k : Fin n, partialGram B * h ^ (k : ℕ) * partialGram A ≠ 0) ∧
    (mass v h A B n = 0 →
      (∀ t : T → ℂ, ((t, 0, 0) : Carrier V N T H) ∈ reducingSubspace v h B) ∧
      (∀ x : Carrier V N T H, x ∈ reducingSubspace v h B → x.2.2 = 0) ∧
      (∀ (l : Letter T H G) (x : Carrier V N T H), x ∈ reducingSubspace v h B →
        letterAct v h A B l x ∈ reducingSubspace v h B)) ∧
    (0 < mass v h A B n →
      ∃ w : List (Letter T H G), HasBridge v h A B w ∧ w.length ≤ n + 1) := by
  intro n
  have hpos := mass_pos_iff v h A B n
  have hzero_iff := mass_eq_zero_iff v h A B hmul hone hunit hirr hh n
  have hnn := mass_nonneg v h A B n
  have hiv : 0 < mass v h A B n ↔ ∃ k : Fin n, partialGram B * h ^ (k : ℕ) * partialGram A ≠ 0 := by
    rw [lt_iff_le_and_ne, and_iff_right hnn, ne_comm, Ne, hzero_iff]
    push_neg
    rfl
  refine ⟨⟨mass_eq v h A B hmul hone hunit hirr hh n, hnn⟩, ?_, hpos.symm, ?_, ?_, ?_, ?_⟩
  · constructor
    · rintro ⟨w, hw⟩
      by_contra hno
      have hm : mass v h A B n = 0 := by
        by_contra hne
        exact hno (hpos.mp (lt_of_le_of_ne hnn (Ne.symm hne)))
      exact no_bridge_of_mass_eq_zero v h A B hmul hone hunit hirr hh hm w hw
    · rintro ⟨g, k, hk⟩
      exact ⟨_, (word_hasBridge v h A B hone g k hk).1⟩
  · rw [hiv]
    constructor
    · rintro ⟨k, hk⟩; exact ⟨k, hk⟩
    · rintro ⟨k, hk⟩
      by_contra hall
      push_neg at hall
      exact hk (partialGram_pow_mul_eq_zero_all h A B (fun j => hall j) k)
  · constructor
    · rintro ⟨k, hk⟩
      by_contra hall
      push_neg at hall
      exact hk (partialGram_pow_mul_eq_zero_all h A B (fun j => hall j) k)
    · rintro ⟨k, hk⟩; exact ⟨k, hk⟩
  · intro hm
    have hz := word_eq_zero_all v h A B hmul hone hunit hirr hh hm
    exact ⟨T_mem_reducingSubspace v h B,
      fun x hx => ((mem_reducingSubspace v h B).mp hx).2,
      fun l x hx => reducingSubspace_invariant v h A B hmul hone hunit hz l x hx⟩
  · intro hm
    obtain ⟨g, k, hk⟩ := hpos.mp hm
    obtain ⟨hb, hl⟩ := word_hasBridge v h A B hone g k hk
    exact ⟨_, hb, by rw [hl]; omega⟩

end

end ReciprocalReturnBank
end RenewalGeometry
