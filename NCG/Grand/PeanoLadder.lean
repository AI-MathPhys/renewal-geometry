/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.RecordGeneration
import NCG.Grand.GrandFactorObstruction

/-!
# Peano partial isometries, count rigidity, and naturality
  (`cor:ar-Peano-projections`, `thm:ar-count-rigidity`,
   `thm:ar-Peano-naturality`, Gran-Tensor manuscript)

* `peano_projections`: every truncated Peano history `L_a` is a
  partial isometry — `L_a*L_a` is the endpoint projection onto
  the surviving domain (`a(i+1) ≤ X`, i.e. `b ≤ X/a`), `L_aL_a*`
  is the projection onto the multiples of `a`, and
  `L_a L_a* L_a = L_a`; all nonzero deterministic multiplication
  edges have coefficient one;
* `count_rigidity`: the count history is the unique operator
  fixing the anchor and satisfying `[D, S] = S`;
* `count_peano_covariance`: the boxed covariance
  `N L_a = a·L_a N` and its additive logarithmic form
  `[log N, L_a] = (log a)·L_a`;
* `peano_naturality`: a chronology unitary commuting with the
  record shift automatically commutes with the count operator
  and with every Peano history (via `C*(S) = M_X`), and a
  source-fixing chronology self-isomorphism is the identity.

Rendering disclosed: the two-realization naturality statement
reduces to the same-carrier statement proved here by composing
with any fixed identification; the uniqueness clause for the
logarithmic generator `K` is the manuscript's remaining
bookkeeping.
-/

open Matrix

namespace NCG

private lemma diag_mul_apply {X : ℕ} (d : Fin X → ℂ)
    (M : Matrix (Fin X) (Fin X) ℂ) (j i : Fin X) :
    (Matrix.diagonal d * M) j i = d j * M j i := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single j
    (fun k _ hk => by
      rw [Matrix.diagonal_apply_ne _ (fun h => hk h.symm),
        zero_mul])
    (fun habs => absurd (Finset.mem_univ _) habs)]
  rw [Matrix.diagonal_apply_eq]

private lemma mul_diag_apply {X : ℕ} (d : Fin X → ℂ)
    (M : Matrix (Fin X) (Fin X) ℂ) (j i : Fin X) :
    (M * Matrix.diagonal d) j i = M j i * d i := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single i
    (fun k _ hk => by
      rw [Matrix.diagonal_apply_ne _ hk, mul_zero])
    (fun habs => absurd (Finset.mem_univ _) habs)]
  rw [Matrix.diagonal_apply_eq]

/-- `cor:ar-Peano-projections`: each Peano history is a partial
isometry with the displayed domain and range projections. -/
theorem peano_projections {X : ℕ} (a : ℕ) (ha : 1 ≤ a) :
    ((peanoL X a)ᴴ * peanoL X a
      = Matrix.of fun (j i : Fin X) =>
          if j = i ∧ a * ((i : ℕ) + 1) ≤ X then 1 else 0)
    ∧ (peanoL X a * (peanoL X a)ᴴ
      = Matrix.of fun (j i : Fin X) =>
          if j = i ∧ a ∣ ((j : ℕ) + 1) then 1 else 0)
    ∧ peanoL X a * ((peanoL X a)ᴴ * peanoL X a)
      = peanoL X a := by
  have hdom : (peanoL X a)ᴴ * peanoL X a
      = Matrix.of fun (j i : Fin X) =>
          if j = i ∧ a * ((i : ℕ) + 1) ≤ X then 1 else 0 := by
    ext j i
    rw [Matrix.mul_apply, Matrix.of_apply]
    rw [Finset.sum_congr rfl (fun k _ => show
        (peanoL X a)ᴴ j k * peanoL X a k i
          = if (k : ℕ) + 1 = a * ((j : ℕ) + 1)
              ∧ (k : ℕ) + 1 = a * ((i : ℕ) + 1)
            then 1 else 0 from by
      rw [Matrix.conjTranspose_apply, peanoL, Matrix.of_apply,
        Matrix.of_apply]
      by_cases h1 : (k : ℕ) + 1 = a * ((j : ℕ) + 1) <;>
        by_cases h2 : (k : ℕ) + 1 = a * ((i : ℕ) + 1) <;>
        simp [h1, h2])]
    by_cases hji : j = i
    · subst hji
      by_cases hle : a * ((j : ℕ) + 1) ≤ X
      · have hp : 0 < a * ((j : ℕ) + 1) :=
          Nat.mul_pos (by omega) (Nat.succ_pos _)
        have hkX : a * ((j : ℕ) + 1) - 1 < X := by omega
        rw [Finset.sum_eq_single
          (⟨a * ((j : ℕ) + 1) - 1, hkX⟩ : Fin X)
          (fun k _ hk => by
            rw [if_neg]
            intro hand
            apply hk
            apply Fin.ext
            have hval : ((⟨a * ((j : ℕ) + 1) - 1, hkX⟩
                : Fin X) : ℕ) = a * ((j : ℕ) + 1) - 1 := rfl
            rw [hval]
            have h2 := hand.2
            omega)
          (fun habs => absurd (Finset.mem_univ _) habs)]
        have hval : ((⟨a * ((j : ℕ) + 1) - 1, hkX⟩
            : Fin X) : ℕ) = a * ((j : ℕ) + 1) - 1 := rfl
        rw [if_pos ⟨by rw [hval]; omega, by rw [hval]; omega⟩,
          if_pos ⟨rfl, hle⟩]
      · rw [Finset.sum_eq_zero (fun k _ => by
          rw [if_neg]
          intro hand
          have h2 := hand.2
          have hkl := k.isLt
          omega)]
        rw [if_neg (fun hand => hle hand.2)]
    · rw [Finset.sum_eq_zero (fun k _ => by
        rw [if_neg]
        intro hand
        have h1 := hand.1
        have h2 := hand.2
        have heq : a * ((j : ℕ) + 1) = a * ((i : ℕ) + 1) := by
          omega
        have := Nat.eq_of_mul_eq_mul_left
          (show 0 < a by omega) heq
        exact hji (Fin.ext (by omega)))]
      rw [if_neg (fun hand => hji hand.1)]
  refine ⟨hdom, ?_, ?_⟩
  · ext j i
    rw [Matrix.mul_apply, Matrix.of_apply]
    rw [Finset.sum_congr rfl (fun k _ => show
        peanoL X a j k * (peanoL X a)ᴴ k i
          = if (j : ℕ) + 1 = a * ((k : ℕ) + 1)
              ∧ (i : ℕ) + 1 = a * ((k : ℕ) + 1)
            then 1 else 0 from by
      rw [Matrix.conjTranspose_apply, peanoL, Matrix.of_apply,
        Matrix.of_apply]
      by_cases h1 : (j : ℕ) + 1 = a * ((k : ℕ) + 1) <;>
        by_cases h2 : (i : ℕ) + 1 = a * ((k : ℕ) + 1) <;>
        simp [h1, h2])]
    by_cases hji : j = i
    · subst hji
      by_cases hdvd : a ∣ ((j : ℕ) + 1)
      · obtain ⟨c, hc⟩ := hdvd
        have hc1 : 1 ≤ c := by
          rcases Nat.eq_zero_or_pos c with rfl | h1
          · rw [mul_zero] at hc
            omega
          · exact h1
        have hcle : c ≤ a * c := by
          have h := Nat.mul_le_mul ha (le_refl c)
          rwa [one_mul] at h
        have hjX := j.isLt
        have hcX : c - 1 < X := by omega
        rw [Finset.sum_eq_single (⟨c - 1, hcX⟩ : Fin X)
          (fun k _ hk => by
            rw [if_neg]
            intro hand
            apply hk
            apply Fin.ext
            have hval : ((⟨c - 1, hcX⟩ : Fin X) : ℕ)
                = c - 1 := rfl
            rw [hval]
            have hcancel := Nat.eq_of_mul_eq_mul_left
              (show 0 < a by omega) (hand.1.symm.trans hc)
            omega)
          (fun habs => absurd (Finset.mem_univ _) habs)]
        have hval : ((⟨c - 1, hcX⟩ : Fin X) : ℕ) = c - 1 := rfl
        have harg : ((⟨c - 1, hcX⟩ : Fin X) : ℕ) + 1 = c := by
          rw [hval]
          omega
        rw [if_pos ⟨by rw [harg]; exact hc, by rw [harg]; exact hc⟩,
          if_pos ⟨rfl, ⟨c, hc⟩⟩]
      · rw [Finset.sum_eq_zero (fun k _ => by
          rw [if_neg]
          intro hand
          exact hdvd ⟨(k : ℕ) + 1, hand.1⟩)]
        rw [if_neg (fun hand => hdvd hand.2)]
    · rw [Finset.sum_eq_zero (fun k _ => by
        rw [if_neg]
        intro hand
        have h1 := hand.1
        have h2 := hand.2
        exact hji (Fin.ext (by omega)))]
      rw [if_neg (fun hand => hji hand.1)]
  · rw [hdom]
    ext j i
    rw [Matrix.mul_apply, peanoL, Matrix.of_apply]
    rw [Finset.sum_eq_single i
      (fun k _ hk => by
        rw [show Matrix.of (fun (j i : Fin X) =>
            if j = i ∧ a * ((i : ℕ) + 1) ≤ X
            then (1 : ℂ) else 0) k i = 0 from by
          rw [Matrix.of_apply, if_neg (fun hand => hk hand.1)],
          mul_zero])
      (fun habs => absurd (Finset.mem_univ _) habs)]
    rw [Matrix.of_apply, Matrix.of_apply]
    by_cases hc : (j : ℕ) + 1 = a * ((i : ℕ) + 1)
    · have hle : a * ((i : ℕ) + 1) ≤ X := by
        have := j.isLt
        omega
      rw [if_pos hc,
        if_pos (show i = i ∧ a * ((i : ℕ) + 1) ≤ X
          from ⟨rfl, hle⟩), mul_one]
    · rw [if_neg hc, zero_mul]

/-- The shift moves a ladder basis vector one step up. -/
lemma recS_mulVec_single {X m : ℕ} (hm : m < X)
    (hm1 : m + 1 < X) :
    recS X *ᵥ Pi.single (⟨m, hm⟩ : Fin X) (1 : ℂ)
      = Pi.single (⟨m + 1, hm1⟩ : Fin X) 1 := by
  funext j
  rw [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single (⟨m, hm⟩ : Fin X)
    (fun k _ hk => by
      rw [Pi.single_apply, if_neg hk, mul_zero])
    (fun habs => absurd (Finset.mem_univ _) habs)]
  rw [Pi.single_apply, if_pos rfl, mul_one]
  rw [recS, Matrix.of_apply, Pi.single_apply]
  have hval : ((⟨m, hm⟩ : Fin X) : ℕ) = m := rfl
  rw [hval]
  by_cases hj : (j : ℕ) = m + 1
  · rw [if_pos hj, if_pos (Fin.ext hj)]
  · rw [if_neg hj, if_neg (fun h => hj (by rw [h]))]

/-- Applying a matrix to a basis vector extracts its column. -/
lemma mulVec_single_col {X : ℕ}
    (D : Matrix (Fin X) (Fin X) ℂ) (i j : Fin X) :
    (D *ᵥ Pi.single i (1 : ℂ)) j = D j i := by
  rw [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single i
    (fun k _ hk => by
      rw [Pi.single_apply, if_neg hk, mul_zero])
    (fun habs => absurd (Finset.mem_univ _) habs)]
  rw [Pi.single_apply, if_pos rfl, mul_one]

/-- `thm:ar-count-rigidity`, uniqueness clause: the count
history is the unique operator fixing the anchor with
`[D, S] = S`. -/
theorem count_rigidity {X : ℕ} (hX : 0 < X)
    (D : Matrix (Fin X) (Fin X) ℂ)
    (hanchor : D *ᵥ Pi.single (⟨0, hX⟩ : Fin X) 1
      = Pi.single (⟨0, hX⟩ : Fin X) 1)
    (hcomm : D * recS X - recS X * D = recS X) :
    D = Matrix.diagonal (fun i : Fin X => ((i : ℕ) + 1 : ℂ)) := by
  have hDS : D * recS X = recS X * D + recS X := by
    rw [sub_eq_iff_eq_add] at hcomm
    rw [hcomm]
    abel
  have hcols : ∀ (m : ℕ) (hm : m < X),
      D *ᵥ Pi.single (⟨m, hm⟩ : Fin X) 1
        = (((m : ℕ) : ℂ) + 1) • Pi.single (⟨m, hm⟩ : Fin X) 1 := by
    intro m
    induction m with
    | zero =>
      intro hm
      rw [show (((0 : ℕ) : ℂ) + 1) = 1 from by norm_num,
        one_smul]
      exact hanchor
    | succ m ih =>
      intro hm1
      have hm : m < X := Nat.lt_of_succ_lt hm1
      have hstep : (D * recS X)
            *ᵥ Pi.single (⟨m, hm⟩ : Fin X) (1 : ℂ)
          = (recS X * D + recS X)
            *ᵥ Pi.single (⟨m, hm⟩ : Fin X) (1 : ℂ) := by
        rw [hDS]
      rw [← Matrix.mulVec_mulVec, Matrix.add_mulVec,
        recS_mulVec_single hm hm1, ← Matrix.mulVec_mulVec,
        ih hm, Matrix.mulVec_smul,
        recS_mulVec_single hm hm1] at hstep
      rw [hstep, show ((((m + 1 : ℕ)) : ℂ) + 1)
          = ((((m : ℕ)) : ℂ) + 1) + 1 from by push_cast; ring]
      module
  ext j i
  have hc := hcols (i : ℕ) i.isLt
  rw [Fin.eta] at hc
  have hji := congrFun hc j
  rw [mulVec_single_col] at hji
  rw [hji, Matrix.diagonal_apply, Pi.smul_apply,
    Pi.single_apply, smul_eq_mul]
  by_cases hd : j = i
  · rw [if_pos hd, if_pos hd, mul_one]
    rw [hd]
  · rw [if_neg hd, if_neg hd, mul_zero]

/-- `thm:ar-count-rigidity`, boxed displays: the count–Peano
covariance `N L_a = a·L_a N` and its additive logarithmic form
`[log N, L_a] = (log a)·L_a`. -/
theorem count_peano_covariance {X : ℕ} (a : ℕ) (ha : 1 ≤ a) :
    (Matrix.diagonal (fun i : Fin X => ((i : ℕ) + 1 : ℂ))
        * peanoL X a
      = (a : ℂ) • (peanoL X a
        * Matrix.diagonal (fun i : Fin X => ((i : ℕ) + 1 : ℂ))))
    ∧ (Matrix.diagonal
          (fun i : Fin X => (Real.log ((i : ℕ) + 1) : ℂ))
        * peanoL X a
      - peanoL X a * Matrix.diagonal
          (fun i : Fin X => (Real.log ((i : ℕ) + 1) : ℂ))
      = (Real.log a : ℂ) • peanoL X a) := by
  constructor
  · ext j i
    rw [diag_mul_apply, Matrix.smul_apply, mul_diag_apply,
      peanoL, Matrix.of_apply, smul_eq_mul]
    by_cases hc : (j : ℕ) + 1 = a * ((i : ℕ) + 1)
    · rw [if_pos hc, mul_one, one_mul]
      exact_mod_cast hc
    · rw [if_neg hc, mul_zero, zero_mul, mul_zero]
  · ext j i
    rw [Matrix.sub_apply, diag_mul_apply, mul_diag_apply,
      Matrix.smul_apply, peanoL, Matrix.of_apply, smul_eq_mul]
    by_cases hc : (j : ℕ) + 1 = a * ((i : ℕ) + 1)
    · rw [if_pos hc, mul_one, one_mul, mul_one]
      have hlogs : Real.log ((j : ℕ) + 1)
          = Real.log a + Real.log ((i : ℕ) + 1) := by
        rw [show (((j : ℕ) : ℝ) + 1)
            = (a : ℝ) * (((i : ℕ) : ℝ) + 1) from by
          exact_mod_cast hc]
        rw [Real.log_mul
          (Nat.cast_ne_zero.mpr (by omega))
          (by positivity)]
      rw [hlogs]
      push_cast
      ring
    · rw [if_neg hc, mul_zero, zero_mul, mul_zero, sub_zero]

/-- `thm:ar-Peano-naturality`: a chronology unitary commuting
with the record shift automatically commutes with the count
operator and every Peano history, and a source-fixing
chronology self-isomorphism is the identity. -/
theorem peano_naturality {X : ℕ} (hX : 0 < X)
    (U : Matrix (Fin X) (Fin X) ℂ)
    (hUl : Uᴴ * U = 1) (hUr : U * Uᴴ = 1)
    (hS : U * recS X = recS X * U) :
    (U * Matrix.diagonal (fun i : Fin X => ((i : ℕ) + 1 : ℂ))
      = Matrix.diagonal (fun i : Fin X => ((i : ℕ) + 1 : ℂ)) * U)
    ∧ (∀ a : ℕ, U * peanoL X a = peanoL X a * U)
    ∧ (U *ᵥ Pi.single (⟨0, hX⟩ : Fin X) 1
        = Pi.single (⟨0, hX⟩ : Fin X) 1 → U = 1) := by
  have hstar : ∀ M : Matrix (Fin X) (Fin X) ℂ,
      U * M = M * U → U * Mᴴ = Mᴴ * U := by
    intro M h
    have h1 := congrArg Matrix.conjTranspose h
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
      at h1
    calc U * Mᴴ = U * Mᴴ * (Uᴴ * U) := by
          rw [hUl, Matrix.mul_one]
      _ = U * (Mᴴ * Uᴴ) * U := by simp only [Matrix.mul_assoc]
      _ = U * (Uᴴ * Mᴴ) * U := by rw [← h1]
      _ = (U * Uᴴ) * (Mᴴ * U) := by simp only [Matrix.mul_assoc]
      _ = Mᴴ * U := by rw [hUr, Matrix.one_mul]
  have htop : ∀ M : Matrix (Fin X) (Fin X) ℂ,
      U * M = M * U := by
    intro M
    have hM : M ∈ StarAlgebra.adjoin ℂ
        ({recS X} : Set (Matrix (Fin X) (Fin X) ℂ)) := by
      rw [record_generation hX]
      trivial
    induction hM using StarAlgebra.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact hS
    | algebraMap c =>
      rw [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul,
        Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
    | add x y hx hy ihx ihy =>
      rw [Matrix.mul_add, Matrix.add_mul, ihx, ihy]
    | mul x y hx hy ihx ihy =>
      calc U * (x * y) = (U * x) * y := by
            rw [Matrix.mul_assoc]
        _ = x * (U * y) := by rw [ihx, Matrix.mul_assoc]
        _ = (x * y) * U := by rw [ihy, ← Matrix.mul_assoc]
    | star x hx ihx => exact hstar x ihx
  refine ⟨htop _, fun a => htop _, ?_⟩
  intro hanchor
  haveI : Nonempty (Fin X) := ⟨⟨0, hX⟩⟩
  obtain ⟨c, hc⟩ := central_scalar U
    (fun M => (htop M).symm)
  rw [hc, Matrix.smul_mulVec, Matrix.one_mulVec] at hanchor
  have h0 := congrFun hanchor (⟨0, hX⟩ : Fin X)
  simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul,
    mul_one] at h0
  rw [hc, h0, one_smul]

end NCG
