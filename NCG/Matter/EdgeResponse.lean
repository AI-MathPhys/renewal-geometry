/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Matter.EdgePOVM

/-!
# Edge-line generation algebra and the response isomorphism
  (`prop:edge-M3`, `thm:response-isomorphism`,
   `cor:conductance-completeness`, SM_emergence)

For the explicit `K₄` harmonic edge frame of `NCG.Matter.EdgePOVM`:

* `edge_M3` — the six edge projectors `P_e = 2·G₀^{-1/2}r_er_eᵀG₀^{-1/2}`
  have trivial commutant: any matrix commuting with all six is
  scalar (so the generated unital `*`-algebra is `M₃(ℂ)` by
  Burnside);
* `edge_response_iso` — the six rank-one forms `r_er_eᵀ` are
  linearly independent and span the symmetric `3×3` matrices; the
  whitened trace of `𝓡(z)` is `(Σz)/2`, so centered scores map to
  traceless operators;
* `edge_response_bounds` — the transported Hilbert–Schmidt metric
  satisfies `⅛‖z‖² ≤ ‖𝓡(z)‖²_HS ≤ ¼‖z‖²` on centered scores
  (exact sum-of-squares certificates);
* `edge_response_whitened` — the HS norm transports through any
  symmetric whitening `S·G₀·S = 1`.
-/

namespace NCG

open Matrix

noncomputable section

/-- The complex edge rows. -/
def edgeRowC : Fin 6 → Fin 3 → ℂ
  | 0 => ![1, 0, 0]
  | 1 => ![0, 1, 0]
  | 2 => ![-1, -1, 0]
  | 3 => ![0, 0, 1]
  | 4 => ![1, 0, -1]
  | 5 => ![0, 1, 1]

/-- The complex rank-one edge forms `r_e r_eᵀ`. -/
def edgeRC (e : Fin 6) : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.vecMulVec (edgeRowC e) (edgeRowC e)

/-- The complex Gram matrix. -/
def edgeGramC : Matrix (Fin 3) (Fin 3) ℂ :=
  !![3, 1, -1; 1, 3, 1; -1, 1, 3]

/-- The complex inverse Gram matrix. -/
def edgeGramCinv : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1/2, -(1/4), 1/4; -(1/4), 1/2, -(1/4); 1/4, -(1/4), 1/2]

lemma edgeGramC_mul_inv : edgeGramC * edgeGramCinv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [edgeGramC, edgeGramCinv, Matrix.mul_apply,
      Fin.sum_univ_three, Matrix.one_apply, Fin.ext_iff,
      Matrix.cons_val_two, Matrix.vecTail, Matrix.vecHead]

lemma edgeGramC_inv_mul : edgeGramCinv * edgeGramC = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [edgeGramC, edgeGramCinv, Matrix.mul_apply,
      Fin.sum_univ_three, Matrix.one_apply, Fin.ext_iff,
      Matrix.cons_val_two, Matrix.vecTail, Matrix.vecHead]

/-- `E₁₁ + E₂₂ + E₃₃ = 1` from the three coordinate edges. -/
lemma edgeRC_one : edgeRC 0 + edgeRC 1 + edgeRC 3 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [edgeRC, edgeRowC, Matrix.vecMulVec_apply,
      Matrix.one_apply, Fin.ext_iff]

lemma edgeRC_sym12 : edgeRC 2 - edgeRC 0 - edgeRC 1
    = !![0, 1, 0; 1, 0, 0; 0, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [edgeRC, edgeRowC, Matrix.vecMulVec_apply,
      Matrix.cons_val_two, Matrix.vecTail, Matrix.vecHead]

lemma edgeRC_sym13 : edgeRC 0 + edgeRC 3 - edgeRC 4
    = !![0, 0, 1; 0, 0, 0; 1, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [edgeRC, edgeRowC, Matrix.vecMulVec_apply,
      Matrix.cons_val_two, Matrix.vecTail, Matrix.vecHead]

lemma edgeRC_sym23 : edgeRC 5 - edgeRC 1 - edgeRC 3
    = !![0, 0, 0; 0, 0, 1; 0, 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [edgeRC, edgeRowC, Matrix.vecMulVec_apply,
      Matrix.cons_val_two, Matrix.vecTail, Matrix.vecHead]

/-- Commuting with the diagonal units and two symmetric
off-diagonal units forces a scalar. -/
lemma commute_sym_scalar (X : Matrix (Fin 3) (Fin 3) ℂ)
    (h11 : X * !![1, 0, 0; 0, 0, 0; 0, 0, 0]
      = !![1, 0, 0; 0, 0, 0; 0, 0, 0] * X)
    (h22 : X * !![0, 0, 0; 0, 1, 0; 0, 0, 0]
      = !![0, 0, 0; 0, 1, 0; 0, 0, 0] * X)
    (h12 : X * !![0, 1, 0; 1, 0, 0; 0, 0, 0]
      = !![0, 1, 0; 1, 0, 0; 0, 0, 0] * X)
    (h23 : X * !![0, 0, 0; 0, 0, 1; 0, 1, 0]
      = !![0, 0, 0; 0, 0, 1; 0, 1, 0] * X) :
    X = X 0 0 • 1 := by
  have e := fun {M : Matrix (Fin 3) (Fin 3) ℂ}
    (h : X * M = M * X) (i j : Fin 3) => Matrix.ext_iff.mpr h i j
  have a1 := e h11 0 1
  have a2 := e h11 0 2
  have a3 := e h11 1 0
  have a4 := e h11 2 0
  have a5 := e h22 1 2
  have a6 := e h22 2 1
  have a7 := e h12 0 1
  have a8 := e h23 1 2
  norm_num [Matrix.mul_apply, Fin.sum_univ_three,
    Matrix.cons_val_two, Matrix.vecTail,
    Matrix.vecHead] at a1 a2 a3 a4 a5 a6 a7 a8
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.smul_apply, Matrix.one_apply, Fin.ext_iff,
      Fin.reduceFinMk, Fin.isValue, smul_eq_mul] <;>
    norm_num <;>
    first
      | linear_combination - a1
      | linear_combination - a2
      | linear_combination a3
      | linear_combination a4
      | linear_combination - a5
      | linear_combination a6
      | linear_combination - a7
      | linear_combination - a7 - a8

/-- `prop:edge-M3`: the six whitened edge projectors have trivial
commutant — any matrix commuting with all `P_e` is scalar. -/
theorem edge_M3 (S : Matrix (Fin 3) (Fin 3) ℂ)
    (hS : S * edgeGramC * S = 1)
    (X : Matrix (Fin 3) (Fin 3) ℂ)
    (hX : ∀ e : Fin 6, X * ((2 : ℂ) • (S * edgeRC e * S))
      = ((2 : ℂ) • (S * edgeRC e * S)) * X) :
    ∃ c : ℂ, X = c • 1 := by
  have hST : S * (edgeGramC * S) = 1 := by
    rw [← Matrix.mul_assoc]
    exact hS
  have hTS : (edgeGramC * S) * S = 1 :=
    mul_eq_one_comm.mp hST
  set T : Matrix (Fin 3) (Fin 3) ℂ := edgeGramC * S with hT
  have hSS : S * S = edgeGramCinv := by
    calc S * S
        = (edgeGramCinv * edgeGramC) * (S * S) := by
          rw [edgeGramC_inv_mul, one_mul]
      _ = edgeGramCinv * (T * S) := by
          rw [hT]
          noncomm_ring
      _ = edgeGramCinv := by rw [hTS, mul_one]
  set X' : Matrix (Fin 3) (Fin 3) ℂ := T * X * S with hX'def
  -- transported commutation with the rational family R_e·G₀⁻¹
  have hX' : ∀ e : Fin 6,
      X' * (edgeRC e * edgeGramCinv)
        = (edgeRC e * edgeGramCinv) * X' := by
    intro e
    have he := hX e
    have hcore : X * (S * edgeRC e * S)
        = (S * edgeRC e * S) * X := by
      have e1 : X * ((2 : ℂ) • (S * edgeRC e * S))
          = (2 : ℂ) • (X * (S * edgeRC e * S)) := by
        rw [Matrix.mul_smul]
      have e2 : ((2 : ℂ) • (S * edgeRC e * S)) * X
          = (2 : ℂ) • ((S * edgeRC e * S) * X) := by
        rw [Matrix.smul_mul]
      have h2 : (2 : ℂ) • (X * (S * edgeRC e * S))
          = (2 : ℂ) • ((S * edgeRC e * S) * X) := by
        rw [← e1, ← e2]
        exact he
      exact smul_right_injective
        (Matrix (Fin 3) (Fin 3) ℂ) (two_ne_zero (α := ℂ)) h2
    calc X' * (edgeRC e * edgeGramCinv)
        = T * (X * (S * edgeRC e * S)) * S := by
          rw [hX'def, ← hSS]
          noncomm_ring
      _ = T * ((S * edgeRC e * S) * X) * S := by rw [hcore]
      _ = ((T * S) * edgeRC e) * (S * X * S) := by noncomm_ring
      _ = edgeRC e * (S * X * S) := by rw [hTS, one_mul]
      _ = (edgeRC e * edgeGramCinv) * X' := by
          rw [hX'def, ← hSS]
          calc edgeRC e * (S * X * S)
              = edgeRC e * S * (S * T) * X * S := by
                rw [hST]
                noncomm_ring
            _ = (edgeRC e * (S * S)) * (T * X * S) := by
                noncomm_ring
  -- commutation with G₀⁻¹ via the identity combination
  have h1inv : X' * edgeGramCinv = edgeGramCinv * X' := by
    have h0 := hX' 0
    have h1 := hX' 1
    have h3 := hX' 3
    have hsum : X' * ((edgeRC 0 + edgeRC 1 + edgeRC 3)
          * edgeGramCinv)
        = ((edgeRC 0 + edgeRC 1 + edgeRC 3) * edgeGramCinv)
          * X' := by
      rw [Matrix.add_mul, Matrix.add_mul, Matrix.mul_add,
        Matrix.mul_add, Matrix.add_mul, Matrix.add_mul, h0, h1, h3]
    rwa [edgeRC_one, one_mul] at hsum
  -- commutation with each rank-one form
  have hRe : ∀ e : Fin 6, X' * edgeRC e = edgeRC e * X' := by
    intro e
    have h := hX' e
    have expand : X' * (edgeRC e * edgeGramCinv) * edgeGramC
        = X' * edgeRC e := by
      calc X' * (edgeRC e * edgeGramCinv) * edgeGramC
          = X' * (edgeRC e * (edgeGramCinv * edgeGramC)) := by
            noncomm_ring
        _ = X' * edgeRC e := by
            rw [edgeGramC_inv_mul, Matrix.mul_one]
    have expand2 : (edgeRC e * edgeGramCinv) * X' * edgeGramC
        = edgeRC e * X' := by
      calc (edgeRC e * edgeGramCinv) * X' * edgeGramC
          = edgeRC e * ((edgeGramCinv * X') * edgeGramC) := by
            noncomm_ring
        _ = edgeRC e * ((X' * edgeGramCinv) * edgeGramC) := by
            rw [h1inv]
        _ = edgeRC e * (X' * (edgeGramCinv * edgeGramC)) := by
            noncomm_ring
        _ = edgeRC e * X' := by
            rw [edgeGramC_inv_mul, Matrix.mul_one]
    rw [← expand, ← expand2, h]
  -- the four symmetric commutations
  have hE11 : edgeRC 0 = !![1, 0, 0; 0, 0, 0; 0, 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [edgeRC, edgeRowC, Matrix.vecMulVec_apply]
  have hE22 : edgeRC 1 = !![0, 0, 0; 0, 1, 0; 0, 0, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [edgeRC, edgeRowC, Matrix.vecMulVec_apply]
  have h12 : X' * !![0, 1, 0; 1, 0, 0; 0, 0, 0]
      = !![0, 1, 0; 1, 0, 0; 0, 0, 0] * X' := by
    rw [← edgeRC_sym12, Matrix.mul_sub, Matrix.mul_sub,
      Matrix.sub_mul, Matrix.sub_mul, hRe 2, hRe 0, hRe 1]
  have h23 : X' * !![0, 0, 0; 0, 0, 1; 0, 1, 0]
      = !![0, 0, 0; 0, 0, 1; 0, 1, 0] * X' := by
    rw [← edgeRC_sym23, Matrix.mul_sub, Matrix.mul_sub,
      Matrix.sub_mul, Matrix.sub_mul, hRe 5, hRe 1, hRe 3]
  have hscalar := commute_sym_scalar X'
    (hE11 ▸ hRe 0) (hE22 ▸ hRe 1) h12 h23
  obtain ⟨c, hc⟩ : ∃ c : ℂ, X' = c • 1 := ⟨X' 0 0, hscalar⟩
  refine ⟨c, ?_⟩
  calc X = (S * T) * (X * (S * T)) := by
        rw [hST, one_mul, mul_one]
    _ = S * (T * X * S) * T := by noncomm_ring
    _ = S * (c • (1 : Matrix (Fin 3) (Fin 3) ℂ)) * T := by
        rw [← hX'def, hc]
    _ = c • (S * T) := by
        rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
    _ = c • 1 := by rw [hST]

/-- The score-to-symmetric-form map `M(z) = Σ_e z_e·r_er_eᵀ`. -/
def edgeSym (z : Fin 6 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  ∑ e, z e • Matrix.vecMulVec (edgeRow e) (edgeRow e)

lemma edgeSym_entries (z : Fin 6 → ℝ) :
    edgeSym z = !![z 0 + z 2 + z 4, z 2, -(z 4);
                   z 2, z 1 + z 2 + z 5, z 5;
                   -(z 4), z 5, z 3 + z 4 + z 5] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [edgeSym, edgeRow, Matrix.sum_apply,
      Matrix.vecMulVec_apply, Fin.sum_univ_six,
      Matrix.cons_val_two, Matrix.vecTail, Matrix.vecHead]

/-- `thm:response-isomorphism`: the six rank-one edge forms are
independent, span the symmetric matrices, and the whitened trace
of the response is `(Σz)/2` (centered scores ↦ traceless). -/
theorem edge_response_iso :
    (∀ z : Fin 6 → ℝ, edgeSym z = 0 → z = 0)
    ∧ (∀ M : Matrix (Fin 3) (Fin 3) ℝ, Mᵀ = M →
        ∃ z : Fin 6 → ℝ, edgeSym z = M)
    ∧ (∀ z : Fin 6 → ℝ,
        (edgeSym z * edgeGramInv).trace = (∑ e, z e) / 2) := by
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    rw [edgeSym_entries] at hz
    have h := fun i j => Matrix.ext_iff.mpr hz i j
    have h00 := h 0 0
    have h01 := h 0 1
    have h02 := h 0 2
    have h11 := h 1 1
    have h12 := h 1 2
    have h22 := h 2 2
    norm_num [Matrix.cons_val_two, Matrix.vecTail,
      Matrix.vecHead] at h00 h01 h02 h11 h12 h22
    funext e
    fin_cases e <;> simp <;> linarith
  · intro M hM
    have hs := fun i j => Matrix.ext_iff.mpr hM i j
    have s01 := hs 0 1
    have s02 := hs 0 2
    have s12 := hs 1 2
    simp only [Matrix.transpose_apply] at s01 s02 s12
    set v : Fin 6 → ℝ := ![M 0 0 - M 0 1 + M 0 2,
      M 1 1 - M 0 1 - M 1 2, M 0 1, M 2 2 + M 0 2 - M 1 2,
      -(M 0 2), M 1 2] with hv
    refine ⟨v, ?_⟩
    have v0 : v 0 = M 0 0 - M 0 1 + M 0 2 := rfl
    have v1 : v 1 = M 1 1 - M 0 1 - M 1 2 := rfl
    have v2 : v 2 = M 0 1 := rfl
    have v3 : v 3 = M 2 2 + M 0 2 - M 1 2 := rfl
    have v4 : v 4 = -(M 0 2) := rfl
    have v5 : v 5 = M 1 2 := rfl
    rw [edgeSym_entries, v0, v1, v2, v3, v4, v5]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.cons_val_two, Matrix.vecTail,
        Matrix.vecHead] <;>
      first
        | linarith
        | (simp only [show ((⟨2, by omega⟩ : Fin 3)) = (2 : Fin 3)
              from rfl] <;>
           linarith)
  · intro z
    rw [edgeSym_entries, edgeGramInv, Fin.sum_univ_six]
    rw [Matrix.trace_fin_three]
    norm_num [Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.cons_val_two, Matrix.vecTail, Matrix.vecHead]
    ring

/-- `thm:response-isomorphism` (metric bounds): the transported
Hilbert–Schmidt metric satisfies `⅛‖z‖² ≤ ‖𝓡(z)‖² ≤ ¼‖z‖²` on
centered scores (exact sum-of-squares certificates). -/
theorem edge_response_bounds (z : Fin 6 → ℝ)
    (hz : ∑ e, z e = 0) :
    (1 / 8) * (∑ e, z e ^ 2)
      ≤ ((edgeSym z * edgeGramInv)
          * (edgeSym z * edgeGramInv)).trace
    ∧ ((edgeSym z * edgeGramInv)
        * (edgeSym z * edgeGramInv)).trace
      ≤ (1 / 4) * (∑ e, z e ^ 2) := by
  rw [Fin.sum_univ_six] at hz
  rw [edgeSym_entries, edgeGramInv, Fin.sum_univ_six,
    Matrix.trace_fin_three]
  norm_num [Matrix.mul_apply, Fin.sum_univ_three,
    Matrix.cons_val_two, Matrix.vecTail, Matrix.vecHead]
  constructor
  · nlinarith [sq_nonneg (z 0 - z 5), sq_nonneg (z 1 - z 4),
      sq_nonneg (z 2 - z 3), hz,
      sq_nonneg (z 0 + z 1 + z 2 + z 3 + z 4 + z 5)]
  · nlinarith [sq_nonneg (z 0 + z 5), sq_nonneg (z 1 + z 4),
      sq_nonneg (z 2 + z 3), hz,
      sq_nonneg (z 0 + z 1 + z 2 + z 3 + z 4 + z 5)]

/-- The HS norm transports through any symmetric whitening
`S·G₀·S = 1`. -/
theorem edge_response_whitened (S : Matrix (Fin 3) (Fin 3) ℝ)
    (hS : S * edgeGram * S = 1) (M : Matrix (Fin 3) (Fin 3) ℝ) :
    ((S * M * S) * (S * M * S)).trace
      = ((M * edgeGramInv) * (M * edgeGramInv)).trace := by
  have hST : S * (edgeGram * S) = 1 := by
    rw [← Matrix.mul_assoc]
    exact hS
  have hTS : (edgeGram * S) * S = 1 := mul_eq_one_comm.mp hST
  have hSS : S * S = edgeGramInv := by
    calc S * S
        = (edgeGramInv * edgeGram) * (S * S) := by
          rw [mul_eq_one_comm.mp edge_gram_mul_inv, one_mul]
      _ = edgeGramInv * ((edgeGram * S) * S) := by noncomm_ring
      _ = edgeGramInv := by rw [hTS, mul_one]
  calc ((S * M * S) * (S * M * S)).trace
      = (S * (M * S * S * M * S)).trace := by
        rw [show (S * M * S) * (S * M * S)
          = S * (M * S * S * M * S) from by noncomm_ring]
    _ = ((M * S * S * M * S) * S).trace :=
        Matrix.trace_mul_comm _ _
    _ = ((M * edgeGramInv) * (M * edgeGramInv)).trace := by
        rw [show (M * S * S * M * S) * S
          = (M * (S * S)) * (M * (S * S)) from by noncomm_ring,
          hSS]

/-- `cor:conductance-completeness`: the common direction supplies
the identity trace and centered scores supply every traceless
symmetric response. -/
theorem conductance_completeness :
    (∀ M : Matrix (Fin 3) (Fin 3) ℝ, Mᵀ = M →
        ∃ z : Fin 6 → ℝ, edgeSym z = M)
    ∧ (∀ z : Fin 6 → ℝ, (∑ e, z e) = 0 →
        (edgeSym z * edgeGramInv).trace = 0) := by
  refine ⟨edge_response_iso.2.1, ?_⟩
  intro z hz
  rw [edge_response_iso.2.2 z, hz, zero_div]

end

end NCG
