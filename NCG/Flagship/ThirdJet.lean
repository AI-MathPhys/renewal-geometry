/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Exact third-Store-jet determinant and quantitative loading
  (`cor:single-writer-third-jet-master`, flagship manuscript)

For the sequential three-control history
`U_E(t) = e^{-itA}e^{-itB}e^{-itC}` with writer letters
`A = W(Ee₁), B = W(Ee₂), C = W(Ee₃)` in a complex Banach algebra
and the pseudoscalar trace `a_E(t) = τ(𝒥₃U_E(t))` (any continuous
linear functional `τ`; the manuscript's normalized `4×4` trace
against `𝒥₃` is the instance `τ = τ₄(𝒥₃·)` under the scoped
`Matrix` operator norm), we prove with genuine real derivatives
of the exponentials:

* the boxed jet identity `a_E(0) = a_E'(0) = a_E''(0) = 0` and
  `a_E'''(0) = 6·χ_W det E` (`single_writer_third_jet`);
* the boxed quantitative loading `|χ_W| ≥ g_*^{3/2}` from the
  frame bound `G_W ⪰ g_*I₃` and `|χ_W|² = det G_W`
  (`single_writer_loading`, by the eigenvalue route).

The finitely many Clifford-trace facts of the parent
single-writer theorem enter as displayed hypotheses (disclosed —
the parent record `thm:single-writer-clifford-master` is a
separate ledger item): squares are scalar, the pseudoscalar
functional kills degrees `0, 1, 2`, and the parent box
`iτ(𝒥₃ABC) = χ_W det E` names the constant.  The derivative
computation — the content of the corollary — is fully proved.
-/

open Matrix NormedSpace

namespace NCG

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸]
  [CompleteSpace 𝔸]

/-- The generic three-block insertion word
`e^{-itA}·M·e^{-itB}·N·e^{-itC}·P`. -/
noncomputable def jetT (A B C M N P : 𝔸) (t : ℝ) : 𝔸 :=
  exp (t • ((-Complex.I) • A))
    * (M * (exp (t • ((-Complex.I) • B))
      * (N * (exp (t • ((-Complex.I) • C)) * P))))

/-- Derivative of the insertion word: one letter enters each
block. -/
lemma jetT_hasDerivAt (A B C M N P : 𝔸) (t : ℝ) :
    HasDerivAt (jetT A B C M N P)
      (jetT A B C ((-Complex.I) • A * M) N P t
        + jetT A B C M ((-Complex.I) • B * N) P t
        + jetT A B C M N ((-Complex.I) • C * P) t) t := by
  have hC := (hasDerivAt_exp_smul_const
    ((-Complex.I) • C) t).mul_const P
  have hCN := hC.const_mul N
  have hB := (hasDerivAt_exp_smul_const
    ((-Complex.I) • B) t).mul hCN
  have hBM := hB.const_mul M
  have hA := (hasDerivAt_exp_smul_const
    ((-Complex.I) • A) t).mul hBM
  convert hA using 1
  · funext u
    simp only [jetT, Pi.mul_apply]
  · simp only [jetT, Pi.mul_apply]
    noncomm_ring

omit [CompleteSpace 𝔸] in
/-- Value of the insertion word at time zero. -/
lemma jetT_zero (A B C M N P : 𝔸) :
    jetT A B C M N P 0 = M * (N * P) := by
  simp [jetT, exp_zero]

omit [CompleteSpace 𝔸] in
/-- Pseudoscalar-functional derivative transfer. -/
lemma tau_jet_hasDerivAt (τ : 𝔸 →L[ℂ] ℂ) (J : 𝔸)
    {F : ℝ → 𝔸} {X : 𝔸} {t : ℝ} (h : HasDerivAt F X t) :
    HasDerivAt (fun u => τ (J * F u)) (τ (J * X)) t :=
  ((τ.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
    (h.const_mul J) :)

/-- `cor:single-writer-third-jet-master`, boxed jet identity:
`a_E(0) = a_E'(0) = a_E''(0) = 0` and `a_E'''(0) = 6χ_W det E`,
from the displayed Clifford-trace facts of the parent theorem. -/
theorem single_writer_third_jet (τ : 𝔸 →L[ℂ] ℂ)
    (J A B C : 𝔸) (aa bb cc κ : ℂ)
    (hA2 : A * A = aa • 1) (hB2 : B * B = bb • 1)
    (hC2 : C * C = cc • 1)
    (h0 : τ J = 0)
    (h1A : τ (J * A) = 0) (h1B : τ (J * B) = 0)
    (h1C : τ (J * C) = 0)
    (h2AB : τ (J * (A * B)) = 0) (h2AC : τ (J * (A * C)) = 0)
    (h2BC : τ (J * (B * C)) = 0)
    (hbox : Complex.I * τ (J * (A * (B * C))) = κ) :
    (fun t : ℝ => τ (J * jetT A B C 1 1 1 t)) 0 = 0
    ∧ deriv (fun t : ℝ => τ (J * jetT A B C 1 1 1 t)) 0 = 0
    ∧ deriv (deriv
        (fun t : ℝ => τ (J * jetT A B C 1 1 1 t))) 0 = 0
    ∧ deriv (deriv (deriv
        (fun t : ℝ => τ (J * jetT A B C 1 1 1 t)))) 0
      = 6 * κ := by
  have hda1 : deriv (fun t : ℝ => τ (J * jetT A B C 1 1 1 t))
      = fun t => τ (J *
          (jetT A B C ((-Complex.I) • A * 1) 1 1 t
            + jetT A B C 1 ((-Complex.I) • B * 1) 1 t
            + jetT A B C 1 1 ((-Complex.I) • C * 1) t)) :=
    funext fun t => (tau_jet_hasDerivAt τ J
      (jetT_hasDerivAt A B C 1 1 1 t)).deriv
  have hda2 : deriv (deriv
      (fun t : ℝ => τ (J * jetT A B C 1 1 1 t)))
      = fun t => τ (J *
          ((jetT A B C
              ((-Complex.I) • A * ((-Complex.I) • A * 1)) 1 1 t
            + jetT A B C ((-Complex.I) • A * 1)
                ((-Complex.I) • B * 1) 1 t
            + jetT A B C ((-Complex.I) • A * 1) 1
                ((-Complex.I) • C * 1) t)
          + (jetT A B C ((-Complex.I) • A * 1)
                ((-Complex.I) • B * 1) 1 t
            + jetT A B C 1
                ((-Complex.I) • B * ((-Complex.I) • B * 1)) 1 t
            + jetT A B C 1 ((-Complex.I) • B * 1)
                ((-Complex.I) • C * 1) t)
          + (jetT A B C ((-Complex.I) • A * 1) 1
                ((-Complex.I) • C * 1) t
            + jetT A B C 1 ((-Complex.I) • B * 1)
                ((-Complex.I) • C * 1) t
            + jetT A B C 1 1
                ((-Complex.I) • C * ((-Complex.I) • C * 1))
                t))) := by
    rw [hda1]
    exact funext fun t => (tau_jet_hasDerivAt τ J
      (((jetT_hasDerivAt A B C ((-Complex.I) • A * 1) 1 1 t).add
        (jetT_hasDerivAt A B C 1 ((-Complex.I) • B * 1) 1 t)).add
        (jetT_hasDerivAt A B C 1 1
          ((-Complex.I) • C * 1) t))).deriv
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [jetT_zero, h0]
  · rw [hda1]
    simp only [jetT_zero, one_mul, mul_one, mul_add, map_add,
      mul_smul_comm, map_smul]
    simp [h1A, h1B, h1C]
  · rw [hda2]
    simp only [jetT_zero, one_mul, mul_one, mul_add, map_add,
      smul_mul_assoc, mul_smul_comm, map_smul, hA2, hB2, hC2,
      smul_smul]
    simp [h0, h2AB, h2AC, h2BC]
  · rw [hda2]
    have c1 := jetT_hasDerivAt A B C
      ((-Complex.I) • A * ((-Complex.I) • A * 1)) 1 1 0
    have c2 := jetT_hasDerivAt A B C ((-Complex.I) • A * 1)
      ((-Complex.I) • B * 1) 1 0
    have c3 := jetT_hasDerivAt A B C ((-Complex.I) • A * 1) 1
      ((-Complex.I) • C * 1) 0
    have c4 := jetT_hasDerivAt A B C ((-Complex.I) • A * 1)
      ((-Complex.I) • B * 1) 1 0
    have c5 := jetT_hasDerivAt A B C 1
      ((-Complex.I) • B * ((-Complex.I) • B * 1)) 1 0
    have c6 := jetT_hasDerivAt A B C 1 ((-Complex.I) • B * 1)
      ((-Complex.I) • C * 1) 0
    have c7 := jetT_hasDerivAt A B C ((-Complex.I) • A * 1) 1
      ((-Complex.I) • C * 1) 0
    have c8 := jetT_hasDerivAt A B C 1 ((-Complex.I) • B * 1)
      ((-Complex.I) • C * 1) 0
    have c9 := jetT_hasDerivAt A B C 1 1
      ((-Complex.I) • C * ((-Complex.I) • C * 1)) 0
    have g1 := (c1.add c2).add c3
    have g2 := (c4.add c5).add c6
    have g3 := (c7.add c8).add c9
    refine ((tau_jet_hasDerivAt τ J
      ((g1.add g2).add g3)).deriv).trans ?_
    simp only [jetT_zero, one_mul, mul_one, mul_add, map_add,
      smul_mul_assoc, mul_smul_comm, map_smul, hA2, hB2, hC2,
      smul_smul]
    simp only [h1A, h1B, h1C, smul_eq_mul, mul_zero, add_zero,
      zero_add]
    rw [← hbox]
    ring_nf
    rw [show (Complex.I : ℂ) ^ 3 = -Complex.I from by
      rw [pow_succ, Complex.I_sq]; ring]
    ring

/-- `cor:single-writer-third-jet-master`, boxed quantitative
loading: `G_W ⪰ g_*I₃` and `|χ_W|² = det G_W` give
`|χ_W| ≥ g_*^{3/2}`. -/
theorem single_writer_loading (G : Matrix (Fin 3) (Fin 3) ℝ)
    (g : ℝ) (hg : 0 ≤ g) (hG : G.IsHermitian)
    (hbound : (G - g • 1).PosSemidef)
    (χ : ℂ) (hdet : ‖χ‖ ^ 2 = G.det) :
    Real.sqrt (g ^ 3) ≤ ‖χ‖ := by
  have hev : ∀ i, g ≤ hG.eigenvalues i := by
    intro i
    have h1 := hbound.dotProduct_mulVec_nonneg
      ⇑(hG.eigenvectorBasis i)
    have h2 : (G - g • 1) *ᵥ ⇑(hG.eigenvectorBasis i)
        = (hG.eigenvalues i - g) • ⇑(hG.eigenvectorBasis i) := by
      rw [Matrix.sub_mulVec, hG.mulVec_eigenvectorBasis,
        Matrix.smul_mulVec, Matrix.one_mulVec, sub_smul]
    rw [h2, dotProduct_smul] at h1
    have h3 : star ⇑(hG.eigenvectorBasis i)
        ⬝ᵥ ⇑(hG.eigenvectorBasis i) = 1 := by
      rw [dotProduct_comm,
        ← EuclideanSpace.inner_eq_star_dotProduct,
        @inner_self_eq_norm_sq_to_K ℝ,
        hG.eigenvectorBasis.orthonormal.1 i]
      norm_num
    rw [h3, smul_eq_mul, mul_one] at h1
    linarith
  have hdet3 : g ^ 3 ≤ G.det := by
    rw [hG.det_eq_prod_eigenvalues]
    calc (g : ℝ) ^ 3 = ∏ _i : Fin 3, g := by
          simp [Finset.prod_const]
      _ ≤ ∏ i, hG.eigenvalues i :=
          Finset.prod_le_prod (fun i _ => hg) (fun i _ => hev i)
  calc Real.sqrt (g ^ 3) ≤ Real.sqrt (G.det) :=
        Real.sqrt_le_sqrt hdet3
    _ = ‖χ‖ := by
        rw [← hdet]
        exact Real.sqrt_sq (norm_nonneg χ)

end NCG
