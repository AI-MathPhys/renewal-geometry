/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SqrtPolar

/-!
# Canonical occurrence Choi source
  (`thm:SM-occurrence-Choi-source`, Gran-Tensor manuscript)

* `occurrence_choi_source`:
  (1) the matrix-unit Choi matrix of a Kraus-form map
      `Φ(X) = Σ_α V_αXV_αᴴ` is the explicit positive sum of
      dyads `J = Σ_α w_αw_αᴴ` (with `w_α(a,b) = (V_α)_{b,a}`),
      hence the boxed `J ⪰ 0`;
  (2) the boxed canonical minimal Gram factor `Γ = √J`:
      `ΓᴴΓ = J`, `Γ ⪰ 0`, and any positive square factor
      equals it (uniqueness of the positive root);
  (3) the boxed reconstruction: any operator family with the
      hermitian-basis completeness relation
      `Σ_α (F_α)_{ij}(F_α)_{kl} = δ_{il}δ_{jk}` reconstructs
      the matrix-unit Choi sum:
      `Σ_α F_αᵀ ⊗ Φ(F_α) = Σ_{ij} E_ijᵀ ⊗ Φ(E_ji)` — sixteen
      differentiated hermitian outputs reconstruct the complete
      untyped occurrence.

Rendering disclosed: the source-fixing-unitary uniqueness of
general minimal factors is the proved Gram-uniqueness layer of
the joint-source records; the support identification
`ℰ^min = supp J` is `sqrt_mulVec_eq_zero_iff` (`ker √J = ker
J`) from the sqrt library.
-/

open Matrix
open scoped Kronecker ComplexOrder MatrixOrder

-- `CFC.sqrt` mentions the matrix CFC instance (which needs
-- `DecidableEq`) in every statement; the linter cannot see it.
set_option linter.unusedDecidableInType false

namespace NCG

/-- `thm:SM-occurrence-Choi-source`. -/
theorem occurrence_choi_source {d : Type*} [Fintype d]
    [DecidableEq d] :
    -- (1) Kraus Choi positivity, as an explicit dyad sum
    (∀ {ι : Type} [Fintype ι] (V : ι → Matrix d d ℂ),
      (∑ i : d, ∑ j : d,
          Matrix.single i j (1 : ℂ)
            ⊗ₖ (∑ α, V α * Matrix.single i j (1 : ℂ)
                * (V α)ᴴ))
        = ∑ α, Matrix.vecMulVec
            (fun p : d × d => V α p.2 p.1)
            (star fun p : d × d => V α p.2 p.1)
      ∧ (∑ i : d, ∑ j : d,
          Matrix.single i j (1 : ℂ)
            ⊗ₖ (∑ α, V α * Matrix.single i j (1 : ℂ)
                * (V α)ᴴ)).PosSemidef)
    -- (2) the canonical positive Gram factor
    ∧ (∀ J : Matrix (d × d) (d × d) ℂ, J.PosSemidef →
        (CFC.sqrt J)ᴴ * CFC.sqrt J = J
        ∧ (CFC.sqrt J).PosSemidef
        ∧ ∀ Γ : Matrix (d × d) (d × d) ℂ, Γ.PosSemidef →
            Γ * Γ = J → Γ = CFC.sqrt J)
    -- (3) basis-independent reconstruction
    ∧ (∀ {ι : Type} [Fintype ι] (F : ι → Matrix d d ℂ)
        (Φ : Matrix d d ℂ →ₗ[ℂ] Matrix d d ℂ),
        (∀ i j k l : d, ∑ α, F α i j * F α k l
          = if i = l ∧ j = k then 1 else 0) →
        ∑ α, (F α)ᵀ ⊗ₖ Φ (F α)
          = ∑ i : d, ∑ j : d,
              (Matrix.single i j (1 : ℂ))ᵀ
                ⊗ₖ Φ (Matrix.single j i (1 : ℂ))) := by
  -- per-term Choi collapse: the (p,q) entry of
  -- Σᵢⱼ Eᵢⱼ ⊗ (V Eᵢⱼ Vᴴ) is V p.2 p.1 · conj (V q.2 q.1)
  have hentry : ∀ (V : Matrix d d ℂ) (p q : d × d),
      ∑ i : d, ∑ j : d,
          Matrix.single i j (1 : ℂ) p.1 q.1
            * (V * Matrix.single i j (1 : ℂ) * Vᴴ) p.2 q.2
        = V p.2 p.1 * star (V q.2 q.1) := by
    intro V p q
    rw [Finset.sum_eq_single p.1]
    · rw [Finset.sum_eq_single q.1]
      · rw [Matrix.single_apply, if_pos ⟨rfl, rfl⟩, one_mul]
        rw [Matrix.mul_apply]
        rw [Finset.sum_eq_single q.1]
        · rw [Matrix.mul_apply]
          rw [Finset.sum_eq_single p.1]
          · rw [Matrix.single_apply, if_pos ⟨rfl, rfl⟩,
              mul_one, Matrix.conjTranspose_apply]
          · intro s _ hs
            rw [Matrix.single_apply,
              if_neg (fun hand => hs hand.1.symm), mul_zero]
          · intro hs
            exact absurd (Finset.mem_univ _) hs
        · intro t _ ht
          rw [Matrix.mul_apply]
          rw [Finset.sum_eq_zero fun s _ => ?_, zero_mul]
          rw [Matrix.single_apply,
            if_neg (fun hand => ht hand.2.symm), mul_zero]
        · intro ht
          exact absurd (Finset.mem_univ _) ht
      · intro b _ hb
        rw [Matrix.single_apply,
          if_neg (fun hand => hb hand.2), zero_mul]
      · intro hb
        exact absurd (Finset.mem_univ _) hb
    · intro a _ ha
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [Matrix.single_apply,
        if_neg (fun hand => ha hand.1), zero_mul]
    · intro ha
      exact absurd (Finset.mem_univ _) ha
  refine ⟨?_, ?_, ?_⟩
  · intro ι _ V
    have heq : (∑ i : d, ∑ j : d,
          Matrix.single i j (1 : ℂ)
            ⊗ₖ (∑ α, V α * Matrix.single i j (1 : ℂ)
                * (V α)ᴴ))
        = ∑ α, Matrix.vecMulVec
            (fun p : d × d => V α p.2 p.1)
            (star fun p : d × d => V α p.2 p.1) := by
      ext p q
      simp only [Matrix.sum_apply, Matrix.kroneckerMap_apply,
        Matrix.vecMulVec_apply, Pi.star_apply,
        Finset.mul_sum]
      exact Eq.trans
        (Eq.trans
          (Finset.sum_congr rfl fun i _ => Finset.sum_comm)
          Finset.sum_comm)
        (Finset.sum_congr rfl fun α _ => hentry (V α) p q)
    refine ⟨heq, ?_⟩
    rw [heq]
    exact Finset.sum_induction _ _
      (fun a b ha hb => ha.add hb) Matrix.PosSemidef.zero
      (fun α _ => Matrix.posSemidef_vecMulVec_self_star _)
  · intro J hJ
    refine ⟨?_, sqrt_posSemidef J, ?_⟩
    · rw [sqrt_isHermitian, sqrt_mul_self_eq J hJ]
    · intro Γ hΓ hΓ2
      exact (sqrt_unique' hΓ hΓ2).symm
  · intro ι _ F Φ hcomp
    ext p q
    simp only [Matrix.sum_apply, Matrix.kroneckerMap_apply,
      Matrix.transpose_apply]
    -- expand Φ(F α) over matrix units
    have hexpand : ∀ α : ι, Φ (F α) p.2 q.2
        = ∑ i : d, ∑ j : d,
            F α i j * Φ (Matrix.single i j (1 : ℂ)) p.2 q.2 := by
      intro α
      have hbasis : F α = ∑ i : d, ∑ j : d,
          F α i j • Matrix.single i j (1 : ℂ) := by
        ext a b
        simp only [Matrix.sum_apply, Matrix.smul_apply,
          Matrix.single_apply, smul_eq_mul, mul_ite, mul_one,
          mul_zero]
        rw [Finset.sum_eq_single a]
        · rw [Finset.sum_eq_single b]
          · rw [if_pos ⟨rfl, rfl⟩]
          · intro e _ he
            rw [if_neg (fun hand => he hand.2)]
          · intro he
            exact absurd (Finset.mem_univ _) he
        · intro e _ he
          refine Finset.sum_eq_zero fun e' _ => ?_
          rw [if_neg (fun hand => he hand.1)]
        · intro he
          exact absurd (Finset.mem_univ _) he
      conv_lhs => rw [hbasis]
      rw [map_sum]
      simp only [map_sum, map_smul, Matrix.sum_apply,
        Matrix.smul_apply, smul_eq_mul]
    rw [Finset.sum_congr rfl fun α _ => by rw [hexpand α]]
    -- interchange and collapse by completeness
    rw [show ∑ α, F α q.1 p.1
          * (∑ i : d, ∑ j : d,
              F α i j * Φ (Matrix.single i j (1 : ℂ)) p.2 q.2)
        = ∑ i : d, ∑ j : d,
            (∑ α, F α q.1 p.1 * F α i j)
              * Φ (Matrix.single i j (1 : ℂ)) p.2 q.2 from by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun α _ => by ring]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hcomp q.1 p.1 i j, Matrix.single_apply]
    congr 1
    exact if_congr (and_congr eq_comm eq_comm) rfl rfl

end NCG
