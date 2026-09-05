/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Grand-Tensor order, quotient, and compatibility toolkit
  (`cor:block-CS`, `thm:core-loading-transfer`,
   `thm:cutoff-compatibility`, `prop:ar-joint-source-quotient`,
   `thm:ar-endpoint-coalescence`, `prop:zero-loading-relations`,
   Gran-Tensor manuscript)

* `block_cauchy_schwarz`: for source-factored blocks
  `T_{αβ} = S_αᴴS_β` the boxed inequality
  `|⟨p, T_{αβ}q⟩|² ≤ ⟨p, T_{αα}p⟩·⟨q, T_{ββ}q⟩`;
* `core_loading_transfer`: the boxed Loewner sandwich —
  `G ⪰ gD` and `BᴴDB ⪰ bE` give `BᴴGB ⪰ gb·E`; the kernel
  inclusion `Ker B ⊆ Ker BᴴGB`; and the upper sandwich
  `BᴴGB ⪯ c·BᴴB` under the displayed scalar bound `G ⪯ c·I`;
* `cutoff_compatibility`: isometric word-embedding congruence —
  a compatible synthesis `V_X = V_Y∘I` gives `K_X = IᴴK_YI`;
* `joint_source_quotient`: `Ker Σλ_rC_rᴴC_r = ⋂ Ker C_r` for
  positive weights — the smallest common source quotient;
* `endpoint_coalescence`: a positive-definite endpoint Gram
  forces `Ker(K·J) = Ker J` — one source coordinate per
  retained numerical endpoint;
* `zero_loading_relations`: for a positive-definite energy the
  loading residual vanishes exactly when every relation value
  vanishes.

Rendering disclosed: the Gram factorization `T_{αβ} = S_αᴴS_β`
is the Grand-Tensor block structure (`G ⪰ 0` factored through
any square root); the identification of the abstract endpoint
pairing with the Gaussian-kernel Gram is the manuscript's
bookkeeping.
-/

open Matrix
open scoped ComplexOrder

namespace NCG

/-- `cor:block-CS`: Cauchy–Schwarz for source-factored Grand
Tensor blocks. -/
theorem block_cauchy_schwarz {m p q : Type*} [Fintype m]
    [Fintype p] [Fintype q]
    (S1 : Matrix m p ℂ) (S2 : Matrix m q ℂ)
    (x : p → ℂ) (y : q → ℂ) :
    ‖star x ⬝ᵥ ((S1ᴴ * S2) *ᵥ y)‖ ^ 2
      ≤ (star x ⬝ᵥ ((S1ᴴ * S1) *ᵥ x)).re
        * (star y ⬝ᵥ ((S2ᴴ * S2) *ᵥ y)).re := by
  have hform12 : star x ⬝ᵥ ((S1ᴴ * S2) *ᵥ y)
      = star (S1 *ᵥ x) ⬝ᵥ (S2 *ᵥ y) := by
    rw [← Matrix.mulVec_mulVec, dotProduct_mulVec,
      Matrix.star_mulVec]
  have hform11 : star x ⬝ᵥ ((S1ᴴ * S1) *ᵥ x)
      = star (S1 *ᵥ x) ⬝ᵥ (S1 *ᵥ x) := by
    rw [← Matrix.mulVec_mulVec, dotProduct_mulVec,
      Matrix.star_mulVec]
  have hform22 : star y ⬝ᵥ ((S2ᴴ * S2) *ᵥ y)
      = star (S2 *ᵥ y) ⬝ᵥ (S2 *ᵥ y) := by
    rw [← Matrix.mulVec_mulVec, dotProduct_mulVec,
      Matrix.star_mulVec]
  rw [hform12, hform11, hform22]
  set u := S1 *ᵥ x with hu
  set v := S2 *ᵥ y with hv
  have hre : ∀ w : m → ℂ, (star w ⬝ᵥ w).re
      = ∑ i, ‖w i‖ ^ 2 := by
    intro w
    rw [dotProduct, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.star_apply, Complex.star_def, mul_comm,
      Complex.mul_conj, Complex.ofReal_re,
      Complex.normSq_eq_norm_sq]
  have hb : ‖star u ⬝ᵥ v‖ ≤ ∑ i, ‖u i‖ * ‖v i‖ := by
    rw [dotProduct]
    refine le_trans (norm_sum_le _ _) ?_
    refine Finset.sum_le_sum fun i _ => ?_
    rw [norm_mul, Pi.star_apply, norm_star]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => ‖u i‖) (fun i => ‖v i‖)
  have hnn : (0:ℝ) ≤ ∑ i, ‖u i‖ * ‖v i‖ :=
    Finset.sum_nonneg fun i _ =>
      mul_nonneg (norm_nonneg _) (norm_nonneg _)
  rw [hre, hre]
  calc ‖star u ⬝ᵥ v‖ ^ 2
      ≤ (∑ i, ‖u i‖ * ‖v i‖) ^ 2 := by
        nlinarith [hb, norm_nonneg (star u ⬝ᵥ v)]
    _ ≤ (∑ i, ‖u i‖ ^ 2) * (∑ i, ‖v i‖ ^ 2) := hcs

/-- `thm:core-loading-transfer`: the boxed Loewner sandwich, the
kernel inclusion, and the displayed upper bound. -/
theorem core_loading_transfer {u p : Type*} [Fintype u]
    [DecidableEq u] [Fintype p]
    (G D : Matrix u u ℂ) (B : Matrix u p ℂ)
    (E : Matrix p p ℂ) (g b c : ℝ)
    (hg : 0 ≤ g) (_hb : 0 ≤ b)
    (hGD : (G - g • D).PosSemidef)
    (hDE : (Bᴴ * D * B - b • E).PosSemidef)
    (hGc : (c • (1 : Matrix u u ℂ) - G).PosSemidef) :
    (Bᴴ * G * B - (g * b) • E).PosSemidef
    ∧ (∀ x : p → ℂ, B *ᵥ x = 0 → (Bᴴ * G * B) *ᵥ x = 0)
    ∧ (c • (Bᴴ * B) - Bᴴ * G * B).PosSemidef := by
  refine ⟨?_, ?_, ?_⟩
  · have h1 : (Bᴴ * (G - g • D) * B).PosSemidef :=
      hGD.conjTranspose_mul_mul_same B
    have h2 : (g • (Bᴴ * D * B - b • E)).PosSemidef :=
      hDE.smul hg
    have hsum := h1.add h2
    have hexp : Bᴴ * (G - g • D) * B
          + g • (Bᴴ * D * B - b • E)
        = Bᴴ * G * B - (g * b) • E := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
        Matrix.smul_mul, smul_sub, smul_smul]
      abel
    rwa [hexp] at hsum
  · intro x hx
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hx,
      Matrix.mulVec_zero, Matrix.mulVec_zero]
  · have h := hGc.conjTranspose_mul_mul_same B
    have hexp : Bᴴ * (c • (1 : Matrix u u ℂ) - G) * B
        = c • (Bᴴ * B) - Bᴴ * G * B := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
        Matrix.smul_mul, Matrix.mul_one]
    rwa [hexp] at h

/-- `thm:cutoff-compatibility`: a compatible word synthesis
`V_X = V_Y ∘ I` gives the boxed congruence `K_X = IᴴK_YI` at
every level, hence for the primitive port compression. -/
theorem cutoff_compatibility {wX wY m : Type*}
    [Fintype wY] [Fintype m]
    (VY : Matrix m wY ℂ) (I : Matrix wY wX ℂ) :
    (VY * I)ᴴ * (VY * I) = Iᴴ * (VYᴴ * VY) * I := by
  rw [Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

/-- `prop:ar-joint-source-quotient`: the kernel of the weighted
joint Gram is the intersection of the port kernels. -/
theorem joint_source_quotient {e m : Type*} [Fintype e]
    [Fintype m] {r : ℕ}
    (C : Fin r → Matrix m e ℂ) (lam : Fin r → ℝ)
    (hlam : ∀ i, 0 < lam i) (x : e → ℂ) :
    (∑ i, (lam i : ℂ) • ((C i)ᴴ * C i)) *ᵥ x = 0
      ↔ ∀ i, C i *ᵥ x = 0 := by
  have hform : ∀ i, star x ⬝ᵥ (((C i)ᴴ * C i) *ᵥ x)
      = star (C i *ᵥ x) ⬝ᵥ (C i *ᵥ x) := by
    intro i
    rw [← Matrix.mulVec_mulVec, dotProduct_mulVec,
      Matrix.star_mulVec]
  have hsq : ∀ (v : m → ℂ), star v ⬝ᵥ v
      = ((∑ j, Complex.normSq (v j) : ℝ) : ℂ) := by
    intro v
    rw [dotProduct]
    push_cast
    exact Finset.sum_congr rfl fun j _ => by
      rw [Pi.star_apply, Complex.star_def, mul_comm,
        Complex.mul_conj]
  constructor
  · intro h0 i
    have hpair : star x ⬝ᵥ ((∑ i, (lam i : ℂ)
        • ((C i)ᴴ * C i)) *ᵥ x) = 0 := by
      rw [h0, dotProduct_zero]
    rw [Matrix.sum_mulVec] at hpair
    rw [dotProduct_sum] at hpair
    rw [Finset.sum_congr rfl (fun j _ => by
      rw [Matrix.smul_mulVec, dotProduct_smul,
        hform j, hsq, smul_eq_mul])] at hpair
    rw [show (∑ j, ((lam j : ℂ))
          * ((∑ k, Complex.normSq ((C j *ᵥ x) k) : ℝ) : ℂ))
        = (((∑ j, lam j * ∑ k, Complex.normSq ((C j *ᵥ x) k))
            : ℝ) : ℂ) from by push_cast; rfl] at hpair
    have hreal : (∑ j, lam j
        * ∑ k, Complex.normSq ((C j *ᵥ x) k)) = 0 := by
      exact_mod_cast hpair
    have hterm : ∀ j ∈ Finset.univ, (0:ℝ) ≤ lam j
        * ∑ k, Complex.normSq ((C j *ᵥ x) k) := by
      intro j _
      exact mul_nonneg (hlam j).le
        (Finset.sum_nonneg fun k _ => Complex.normSq_nonneg _)
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg
      hterm).mp hreal i (Finset.mem_univ i)
    have hsum0 : (∑ k, Complex.normSq ((C i *ᵥ x) k)) = 0 := by
      rcases mul_eq_zero.mp hzero with h | h
      · exact absurd h (hlam i).ne'
      · exact h
    funext k
    have := (Finset.sum_eq_zero_iff_of_nonneg
      (fun k _ => Complex.normSq_nonneg ((C i *ᵥ x) k))).mp
      hsum0 k (Finset.mem_univ k)
    exact Complex.normSq_eq_zero.mp this
  · intro h
    rw [Matrix.sum_mulVec]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Matrix.smul_mulVec, ← Matrix.mulVec_mulVec,
      h i, Matrix.mulVec_zero, smul_zero]

/-- `thm:ar-endpoint-coalescence`: a positive-definite endpoint
Gram forces `Ker(K·J) = Ker J`. -/
theorem endpoint_coalescence {m e p : Type*} [Fintype m]
    [Fintype e] [Fintype p]
    (K : Matrix m e ℂ) (J : Matrix e p ℂ)
    (hGram : (Kᴴ * K).PosDef) (x : p → ℂ) :
    (K * J) *ᵥ x = 0 ↔ J *ᵥ x = 0 := by
  constructor
  · intro h0
    by_contra hne
    have hpos := hGram.dotProduct_mulVec_pos hne
    rw [← Matrix.mulVec_mulVec, dotProduct_mulVec,
      ← Matrix.star_mulVec, Matrix.mulVec_mulVec, h0,
      dotProduct_zero] at hpos
    exact lt_irrefl 0 hpos
  · intro h
    rw [← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]

/-- `prop:zero-loading-relations`: for a positive-definite
energy the loading residual vanishes exactly when every relation
value vanishes. -/
theorem zero_loading_relations {ι E : Type*} [Zero E]
    (s : Finset ι) (p : ι → E) (q : E → ℝ)
    (hnn : ∀ v, 0 ≤ q v) (hdef : ∀ v, q v = 0 → v = 0)
    (hq0 : q 0 = 0) :
    (∑ r ∈ s, q (p r)) = 0 ↔ ∀ r ∈ s, p r = 0 := by
  constructor
  · intro h0 r hr
    exact hdef _ ((Finset.sum_eq_zero_iff_of_nonneg
      fun j _ => hnn (p j)).mp h0 r hr)
  · intro h
    refine Finset.sum_eq_zero fun r hr => ?_
    rw [h r hr, hq0]

end NCG
