/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# The canonical arithmetic record chain
  (`thm:ar-Peano-multiplication`, `thm:ar-record-margins`,
   `cth:ar-unrecorded-no-go`, `cor:ar-canonical-coalescence`,
   and the boxed shift relations of `thm:ar-record-algebra`,
   Gran-Tensor manuscript)

On the cutoff record carrier `ℂ^X` (endpoint `n = i + 1` at
coordinate `i : Fin X`):

* `recS` is the chronological successor (`S e_n = e_{n+1}`,
  overflow to zero) and `peanoL a` the truncated multiplication
  history (`L_a e_b = e_{ab}` when `ab ≤ X`, else `0`);
* `recS_relations`: the boxed shift algebra — `SᴴS = I - P_X`,
  `SSᴴ = I - P_1`, and `[N, S] = S` for the count operator
  `N = diag(n)`;
* `record_ladder` / `record_margins`: the count ladder
  `S^{n-1}e_1 = e_n` and the boxed identity chronology Gram —
  the ladder states are orthonormal, so the terminal-Read
  matrix is `I_X` and every innovation margin is one;
* `peano_product`: the boxed product law `L_aL_b = L_{ab}` for
  `a, b ≥ 1` — the overflow-to-zero truncation composes
  exactly, so multiplication is a finite successor-word
  construction, not an independently supplied table;
* `unrecorded_no_go`: the record-discarded core can have
  history algebra `ℂ`, which contains no `X`-endpoint successor
  corner for `X ≥ 2` (dimension obstruction);
* `canonical_coalescence`: an identity endpoint Gram gives
  `Ker 𝒞 = Ker J` unconditionally, with one noncollapsing
  source line per retained endpoint.

Rendering disclosed: the `C*(S) = M_X(ℂ)` generation clause of
the record-algebra theorem is the matrix-unit generation
argument (tracked separately with that record); the
identification of the ladder Reads with the physical terminal
instruments is the record framework's bookkeeping.
-/

open Matrix

namespace NCG

variable {X : ℕ}

/-- The chronological successor `S e_n = e_{n+1}` (overflow to
zero): entries `S_{j,i} = 1` iff `j = i + 1`. -/
def recS (X : ℕ) : Matrix (Fin X) (Fin X) ℂ :=
  Matrix.of fun (j i : Fin X) =>
    if (j : ℕ) = (i : ℕ) + 1 then 1 else 0

/-- The truncated Peano multiplication history
`L_a e_b = e_{ab}` when `ab ≤ X`, else `0` (endpoints are
`1`-based: coordinate `i` carries endpoint `i + 1`). -/
def peanoL (X a : ℕ) : Matrix (Fin X) (Fin X) ℂ :=
  Matrix.of fun (j i : Fin X) =>
    if (j : ℕ) + 1 = a * ((i : ℕ) + 1) then 1 else 0

/-- Boxed product law: `L_aL_b = L_{ab}` for `a, b ≥ 1` — the
overflow-to-zero truncation composes exactly, so multiplication
is a finite successor-word construction. -/
theorem peano_product (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    peanoL X a * peanoL X b = peanoL X (a * b) := by
  ext j i
  rw [Matrix.mul_apply]
  have hterm : ∀ k ∈ Finset.univ,
      peanoL X a j k * peanoL X b k i
        = if (k : ℕ) + 1 = b * ((i : ℕ) + 1)
            ∧ (j : ℕ) + 1 = a * ((k : ℕ) + 1)
          then (1 : ℂ) else 0 := by
    intro k _
    simp only [peanoL, Matrix.of_apply]
    by_cases h1 : (j : ℕ) + 1 = a * ((k : ℕ) + 1) <;>
      by_cases h2 : (k : ℕ) + 1 = b * ((i : ℕ) + 1) <;>
      simp [h1, h2]
  rw [Finset.sum_congr rfl hterm]
  simp only [peanoL, Matrix.of_apply]
  by_cases htar : (j : ℕ) + 1 = a * b * ((i : ℕ) + 1)
  · rw [if_pos htar]
    have hble : b * ((i : ℕ) + 1) ≤ X := by
      nlinarith [j.isLt]
    have hkey : b * ((i : ℕ) + 1) - 1 < X := by omega
    have hassoc : a * (b * ((i : ℕ) + 1))
        = a * b * ((i : ℕ) + 1) := by ring
    have hval : (⟨b * ((i : ℕ) + 1) - 1, hkey⟩ : Fin X).val
        = b * ((i : ℕ) + 1) - 1 := rfl
    rw [Finset.sum_eq_single (⟨b * ((i : ℕ) + 1) - 1, hkey⟩
        : Fin X)
      (fun k _ hk => by
        rw [if_neg]
        rintro ⟨h2, -⟩
        exact hk (Fin.ext (by omega)))
      (fun habs => absurd (Finset.mem_univ _) habs)]
    have hpos : 0 < b * ((i : ℕ) + 1) :=
      Nat.mul_pos hb (by omega)
    have hcol : ((⟨b * ((i : ℕ) + 1) - 1, hkey⟩ : Fin X) : ℕ)
        + 1 = b * ((i : ℕ) + 1) := by omega
    rw [if_pos]
    refine ⟨by omega, ?_⟩
    rw [hcol, hassoc]
    exact htar
  · rw [if_neg htar]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [if_neg]
    rintro ⟨h2, h1⟩
    apply htar
    rw [h1, h2]
    ring

/-- The boxed shift relations of the record algebra:
`SᴴS = I - P_X`, `SSᴴ = I - P_1`, and `[N, S] = S` for the
count operator `N = diag(n)`. -/
theorem recS_relations (hX : 1 ≤ X) :
    ((recS X)ᴴ * recS X
        = 1 - Matrix.of (fun (j i : Fin X) =>
            if (j : ℕ) = X - 1 ∧ (i : ℕ) = X - 1
            then (1 : ℂ) else 0))
    ∧ (recS X * (recS X)ᴴ
        = 1 - Matrix.of (fun (j i : Fin X) =>
            if (j : ℕ) = 0 ∧ (i : ℕ) = 0 then (1 : ℂ) else 0))
    ∧ ((Matrix.diagonal fun i : Fin X => ((i : ℕ) + 1 : ℂ))
          * recS X
        - recS X * (Matrix.diagonal fun i : Fin X =>
            ((i : ℕ) + 1 : ℂ))
      = recS X) := by
  refine ⟨?_, ?_, ?_⟩
  · ext j i
    rw [Matrix.mul_apply]
    have hterm : ∀ k ∈ Finset.univ,
        (recS X)ᴴ j k * recS X k i
          = if (k : ℕ) = (j : ℕ) + 1 ∧ (k : ℕ) = (i : ℕ) + 1
            then (1 : ℂ) else 0 := by
      intro k _
      simp only [Matrix.conjTranspose_apply, recS,
        Matrix.of_apply]
      by_cases h1 : (k : ℕ) = (j : ℕ) + 1 <;>
        by_cases h2 : (k : ℕ) = (i : ℕ) + 1 <;>
        simp [h1, h2]
    rw [Finset.sum_congr rfl hterm]
    rw [Matrix.sub_apply, Matrix.of_apply, Matrix.one_apply]
    by_cases hij : (j : ℕ) = (i : ℕ)
    · by_cases hlast : (j : ℕ) = X - 1
      · rw [Finset.sum_eq_zero fun k _ => by
          rw [if_neg]
          rintro ⟨h1, -⟩
          have := k.isLt
          omega]
        rw [if_pos (Fin.ext hij), if_pos ⟨hlast, hij ▸ hlast⟩]
        norm_num
      · have hlt : (j : ℕ) + 1 < X := by
          have := j.isLt
          omega
        rw [Finset.sum_eq_single (⟨(j : ℕ) + 1, hlt⟩ : Fin X)
          (fun k _ hk => by
            rw [if_neg]
            rintro ⟨h1, -⟩
            exact hk (Fin.ext h1))
          (fun habs => absurd (Finset.mem_univ _) habs)]
        rw [if_pos ⟨rfl, by simp [hij]⟩,
          if_pos (Fin.ext hij), if_neg (by omega)]
        norm_num
    · rw [Finset.sum_eq_zero fun k _ => by
        rw [if_neg]
        rintro ⟨h1, h2⟩
        exact hij (by omega)]
      rw [if_neg (fun h => hij (congrArg Fin.val h)),
        if_neg (by omega)]
      norm_num
  · ext j i
    rw [Matrix.mul_apply]
    have hterm : ∀ k ∈ Finset.univ,
        recS X j k * (recS X)ᴴ k i
          = if (j : ℕ) = (k : ℕ) + 1 ∧ (i : ℕ) = (k : ℕ) + 1
            then (1 : ℂ) else 0 := by
      intro k _
      simp only [Matrix.conjTranspose_apply, recS,
        Matrix.of_apply]
      by_cases h1 : (j : ℕ) = (k : ℕ) + 1 <;>
        by_cases h2 : (i : ℕ) = (k : ℕ) + 1 <;>
        simp [h1, h2]
    rw [Finset.sum_congr rfl hterm]
    rw [Matrix.sub_apply, Matrix.of_apply, Matrix.one_apply]
    by_cases hij : (j : ℕ) = (i : ℕ)
    · by_cases hfirst : (j : ℕ) = 0
      · rw [Finset.sum_eq_zero fun k _ => by
          rw [if_neg]
          rintro ⟨h1, -⟩
          omega]
        rw [if_pos (Fin.ext hij), if_pos ⟨hfirst, hij ▸ hfirst⟩]
        norm_num
      · have hlt : (j : ℕ) - 1 < X := by
          have := j.isLt
          omega
        have hval : ((⟨(j : ℕ) - 1, hlt⟩ : Fin X) : ℕ)
            = (j : ℕ) - 1 := rfl
        rw [Finset.sum_eq_single (⟨(j : ℕ) - 1, hlt⟩ : Fin X)
          (fun k _ hk => by
            rw [if_neg]
            rintro ⟨h1, -⟩
            exact hk (Fin.ext (by omega)))
          (fun habs => absurd (Finset.mem_univ _) habs)]
        rw [if_pos ⟨by omega, by omega⟩,
          if_pos (Fin.ext hij), if_neg (by omega)]
        norm_num
    · rw [Finset.sum_eq_zero fun k _ => by
        rw [if_neg]
        rintro ⟨h1, h2⟩
        exact hij (by omega)]
      rw [if_neg (fun h => hij (congrArg Fin.val h)),
        if_neg (by omega)]
      norm_num
  · ext j i
    rw [Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply]
    have ht1 : ∀ k ∈ Finset.univ,
        Matrix.diagonal (fun i : Fin X => ((i : ℕ) + 1 : ℂ)) j k
            * recS X k i
          = if k = j then ((j : ℕ) + 1 : ℂ) * recS X j i
            else 0 := by
      intro k _
      by_cases hk : k = j
      · subst hk
        rw [Matrix.diagonal_apply_eq, if_pos rfl]
      · rw [Matrix.diagonal_apply_ne _ fun h => hk h.symm,
          zero_mul, if_neg hk]
    have ht2 : ∀ k ∈ Finset.univ,
        recS X j k * Matrix.diagonal
            (fun i : Fin X => ((i : ℕ) + 1 : ℂ)) k i
          = if k = i then recS X j i * ((i : ℕ) + 1 : ℂ)
            else 0 := by
      intro k _
      by_cases hk : k = i
      · subst hk
        rw [Matrix.diagonal_apply_eq, if_pos rfl]
      · rw [Matrix.diagonal_apply_ne _ hk, mul_zero,
          if_neg hk]
    rw [Finset.sum_congr rfl ht1, Finset.sum_congr rfl ht2]
    rw [Finset.sum_ite_eq' Finset.univ j
      (fun _ => ((j : ℕ) + 1 : ℂ) * recS X j i)]
    rw [Finset.sum_ite_eq' Finset.univ i
      (fun _ => recS X j i * ((i : ℕ) + 1 : ℂ))]
    simp only [Finset.mem_univ, if_true]
    simp only [recS, Matrix.of_apply]
    by_cases hji : (j : ℕ) = (i : ℕ) + 1
    · rw [if_pos hji]
      push_cast [hji]
      ring
    · rw [if_neg hji]
      ring

/-- The count ladder `S^{k}e_1 = e_{k+1}` (`ℕ`-indexed). -/
theorem record_ladder (hX : 1 ≤ X) (k : ℕ) (hk : k < X) :
    (recS X) ^ k *ᵥ (Pi.single (⟨0, by omega⟩ : Fin X) 1)
      = Pi.single (⟨k, hk⟩ : Fin X) 1 := by
  induction k with
  | zero =>
    rw [pow_zero, Matrix.one_mulVec]
  | succ j ih =>
    have hj : j < X := by omega
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih hj]
    funext m
    rw [Matrix.mulVec, dotProduct]
    have hterm : ∀ k' ∈ Finset.univ,
        recS X m k' * (Pi.single (⟨j, hj⟩ : Fin X) 1
            : Fin X → ℂ) k'
          = if k' = (⟨j, hj⟩ : Fin X)
            then recS X m ⟨j, hj⟩ else 0 := by
      intro k' _
      by_cases hk' : k' = (⟨j, hj⟩ : Fin X) <;>
        simp [hk']
    rw [Finset.sum_congr rfl hterm]
    rw [Finset.sum_ite_eq' Finset.univ (⟨j, hj⟩ : Fin X)
      (fun _ => recS X m ⟨j, hj⟩)]
    simp only [Finset.mem_univ, if_true]
    simp only [recS, Matrix.of_apply, Pi.single_apply]
    by_cases hm : (m : ℕ) = j + 1
    · rw [if_pos (by simpa using hm),
        if_pos (Fin.ext (by simpa using hm))]
    · rw [if_neg (by simpa using hm), if_neg fun h =>
        hm (by simpa using congrArg Fin.val h)]

/-- The boxed identity chronology Gram: the ladder states are
orthonormal, so the terminal-Read matrix
`[⟨e_i, S^{j-1}e_1⟩]_{ij}` is `I_X` and every innovation margin
is one. -/
theorem record_margins (hX : 1 ≤ X) (i j : Fin X) :
    star (Pi.single i (1 : ℂ)) ⬝ᵥ
        ((recS X) ^ (j : ℕ) *ᵥ
          (Pi.single (⟨0, by omega⟩ : Fin X) 1))
      = if i = j then 1 else 0 := by
  have hlad := record_ladder hX (j : ℕ) j.isLt
  rw [show (⟨(j : ℕ), j.isLt⟩ : Fin X) = j from
    Fin.ext rfl] at hlad
  rw [hlad, dotProduct]
  have hterm : ∀ k ∈ Finset.univ,
      star (Pi.single i (1 : ℂ) : Fin X → ℂ) k
          * (Pi.single j 1 : Fin X → ℂ) k
        = if k = i ∧ k = j then (1 : ℂ) else 0 := by
    intro k _
    by_cases h1 : k = i <;> by_cases h2 : k = j <;>
      simp [h1, h2, Pi.single_apply]
  rw [Finset.sum_congr rfl hterm]
  by_cases hij : i = j
  · subst hij
    rw [Finset.sum_eq_single i
      (fun k _ hk => if_neg fun h => hk h.1)
      (fun habs => absurd (Finset.mem_univ _) habs)]
    simp
  · rw [Finset.sum_eq_zero fun k _ => by
      rw [if_neg]
      rintro ⟨h1, h2⟩
      exact hij (h1.symm.trans h2)]
    rw [if_neg hij]

/-- `cth:ar-unrecorded-no-go`: a record-discarded core can have
history algebra `ℂ`, which contains no `X`-endpoint successor
corner for `X ≥ 2` — dimension obstruction. -/
theorem unrecorded_no_go (hX : 2 ≤ X) :
    ¬∃ f : Matrix (Fin X) (Fin X) ℂ →ₗ[ℂ] ℂ,
      Function.Injective f := by
  rintro ⟨f, hf⟩
  have hle := LinearMap.finrank_le_finrank_of_injective hf
  rw [Module.finrank_self] at hle
  have hdim : Module.finrank ℂ (Matrix (Fin X) (Fin X) ℂ)
      = X * X := by
    rw [Module.finrank_matrix]
    simp
  rw [hdim] at hle
  nlinarith

/-- `cor:ar-canonical-coalescence`: an identity endpoint Gram
gives `Ker 𝒞 = Ker J` unconditionally, with one noncollapsing
source line per retained endpoint. -/
theorem canonical_coalescence {t : Type*} [Fintype t]
    [DecidableEq t]
    (J : Matrix (Fin X) t ℂ) (hGram : Jᴴ * J = 1) :
    (∀ x : t → ℂ, J *ᵥ x = 0 ↔ x = 0)
    ∧ ∀ C : Matrix (Fin X) t ℂ, C = J →
      ∀ x, C *ᵥ x = 0 ↔ J *ᵥ x = 0 := by
  constructor
  · intro x
    constructor
    · intro h0
      have h2 : (Jᴴ * J) *ᵥ x = x := by
        rw [hGram, Matrix.one_mulVec]
      rw [← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero] at h2
      exact h2.symm
    · intro h
      rw [h, Matrix.mulVec_zero]
  · rintro C rfl x
    rfl

end NCG
