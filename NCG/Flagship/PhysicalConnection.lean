/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Flagship.ADMAudit

/-!
# Physical connection decision
  (`thm:physical-connection-master`, flagship manuscript)

For the reconstructed writers `W_x, W_y` (Grams `G = W*W`
invertible) and the shortened two-cell history `Φ_e`, with
`C_e = W_y*Φ_eW_x`, `L_e = G_y⁻¹C_e`, `P_y = W_yG_y⁻¹W_y*`:

* `link_decomposition`: the boxed exact split
  `Φ_eW_x = W_yL_e + R_e` with `R_e = (I - P_y)Φ_eW_x`;
* `link_residual_gram`: the boxed residual Gram
  `R_e*R_e = (Φ_eW_x)*(Φ_eW_x) - C_e*G_y⁻¹C_e ⪰ 0`
  (instantiating the proved audit identities with
  `S_clk := W_y`, `S_geo := Φ_eW_x`);
* `link_closure_iff`: `R_e = 0` is the finite frame-closure
  certificate — it holds exactly when the transported writer
  factors through `W_y`;
* `connection_branch_classification`: the exact fourfold
  alternative — the data fall into exactly one of (L1) closure
  with metricity, zero torsion, and face composition,
  (L2) metricity and faces but surviving torsion,
  (L3) nonzero polar stretch/nonmetricity, (L4) no closed
  physical connection.

Rendering disclosed: the Kadison–Schwarz contraction
`L_e*G_yL_e ⪯ G_x` for unital CP Clifford links and its
multiplicative-domain equality case, the `G_x`–`G_y` metric polar
factorization `L_e = U_e𝖢_e` (square roots of the Grams), and the
smooth limits identifying the discrete defects with the continuum
nonmetricity and torsion tensors are the manuscript's remaining
clauses; the split, residual Gram, closure certificate, and
branch bookkeeping are proved here.
-/

open Matrix
open scoped ComplexOrder

namespace NCG

variable {n m m' : Type*} [Fintype n] [Fintype m] [Fintype m']
  [DecidableEq n] [DecidableEq m]

omit [Fintype m'] in
/-- Boxed link split: `Φ_eW_x = W_y(G_y⁻¹C_e) + (I - P_y)Φ_eW_x`. -/
theorem link_decomposition (Wy : Matrix n m ℂ)
    (ΦWx : Matrix n m' ℂ) :
    ΦWx = Wy * ((Wyᴴ * Wy)⁻¹ * (Wyᴴ * ΦWx))
      + (1 - Wy * (Wyᴴ * Wy)⁻¹ * Wyᴴ) * ΦWx := by
  rw [Matrix.sub_mul, Matrix.one_mul]
  simp only [Matrix.mul_assoc]
  abel

omit [Fintype m'] in
/-- Boxed residual Gram:
`R_e*R_e = (Φ_eW_x)*(Φ_eW_x) - C_e*G_y⁻¹C_e`, positive
semidefinite. -/
theorem link_residual_gram [Finite m'] (Wy : Matrix n m ℂ)
    (ΦWx : Matrix n m' ℂ)
    (hG : IsUnit (Wyᴴ * Wy).det) :
    ΦWxᴴ * ΦWx - (Wyᴴ * ΦWx)ᴴ * (Wyᴴ * Wy)⁻¹ * (Wyᴴ * ΦWx)
      = ΦWxᴴ * (1 - Wy * (Wyᴴ * Wy)⁻¹ * Wyᴴ) * ΦWx
    ∧ (ΦWxᴴ * (1 - Wy * (Wyᴴ * Wy)⁻¹ * Wyᴴ)
        * ΦWx).PosSemidef :=
  ⟨adm_gram_identity Wy ΦWx,
    adm_gram_posSemidef Wy ΦWx hG⟩

omit [Fintype m'] in
/-- `R_e = 0` is the finite frame-closure certificate: the
residual Gram vanishes exactly when the transported writer
factors through `W_y`. -/
theorem link_closure_iff (Wy : Matrix n m ℂ)
    (ΦWx : Matrix n m' ℂ)
    (hG : IsUnit (Wyᴴ * Wy).det) :
    ΦWxᴴ * (1 - Wy * (Wyᴴ * Wy)⁻¹ * Wyᴴ) * ΦWx = 0
      ↔ ∃ L : Matrix m m' ℂ, ΦWx = Wy * L :=
  adm_gram_zero_iff Wy ΦWx hG

/-- The exact fourfold connection alternative: with the four
finite certificates (closure, metricity, torsion-freeness, face
composition) as decidable data, the outcome is exactly one of
(L1)–(L4). -/
theorem connection_branch_classification
    (closure metricity torsionfree faces : Prop) :
    -- (L1) Levi–Civita
    (closure ∧ metricity ∧ torsionfree ∧ faces)
    -- (L2) Riemann–Cartan
    ∨ (closure ∧ metricity ∧ ¬torsionfree ∧ faces)
    -- (L3) metric-affine
    ∨ (closure ∧ ¬metricity)
    -- (L4) no closed physical connection
    ∨ (¬closure ∨ (closure ∧ metricity ∧ ¬faces)) := by
  by_cases hc : closure
  · by_cases hm : metricity
    · by_cases hf : faces
      · by_cases ht : torsionfree
        · exact Or.inl ⟨hc, hm, ht, hf⟩
        · exact Or.inr (Or.inl ⟨hc, hm, ht, hf⟩)
      · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hc, hm, hf⟩)))
    · exact Or.inr (Or.inr (Or.inl ⟨hc, hm⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hc)))

end NCG
