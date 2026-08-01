/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Exact `1+2` stabilizer decomposition and port frame
  (`thm:stabilizer-port-frame`, SM manuscript)

On the six oriented edges `(01,02,03,12,13,23)` of `K₄`, the
harmonic projector `pcyc` (the explicit rational `6×6` matrix of
the manuscript) is a Hermitian idempotent of trace `3`.  The
unnormalized face circulation `h' = (0,0,0,1,-1,1)` (with
`h = h'/√3`) is harmonic, and both generators of the stabilizer
`S₃` of vertex `0` (the signed edge permutations `u12`, `u23`) act
on it by `-1`: the line `ℂh'` carries the sign representation.
The complementary projector `pW2 = pcyc - (1/3)·h'h'*` is a
Hermitian idempotent of trace `2` commuting with the stabilizer
action — the standard two-dimensional summand `W₂`, giving the
boxed `H¹(K₄;ℂ)|_{S₃} ≅ sgn ⊕ W₂` in projector form.

The three incident projections `q0j = pcyc e_{0j}` satisfy
`port01 + port02 + port03 = 0`, the Gram numbers `⟪q0j,q0j⟫ = 1/2`,
`⟪q0j,q0k⟫ = -1/4` `(j ≠ k)`, are permuted by the stabilizer, and
obey the boxed frame identity

  `Σ_j q0j q0j* = (3/4)·pW2`.

Irreducibility of `W₂` as an abstract `S₃`-module is not needed:
the frame identity is verified directly rather than through Schur's
lemma (interpretive prose).
-/

open Matrix

namespace NCG

/-- The harmonic projector on the six oriented edges of `K₄`,
uniform edge metric. -/
noncomputable def pcyc : Matrix (Fin 6) (Fin 6) ℂ :=
  !![1/2, -1/4, -1/4, 1/4, 1/4, 0;
     -1/4, 1/2, -1/4, -1/4, 0, 1/4;
     -1/4, -1/4, 1/2, 0, -1/4, -1/4;
     1/4, -1/4, 0, 1/2, -1/4, 1/4;
     1/4, 0, -1/4, -1/4, 1/2, -1/4;
     0, 1/4, -1/4, 1/4, -1/4, 1/2]

/-- The unnormalized face circulation `h' = √3·h` opposite the
fixed vertex. -/
def faceSign : Fin 6 → ℂ := ![0, 0, 0, 1, -1, 1]

/-- The incident projection `port01 = pcyc e_{01}`. -/
noncomputable def port01 : Fin 6 → ℂ := ![1/2, -1/4, -1/4, 1/4, 1/4, 0]

/-- The incident projection `port02 = pcyc e_{02}`. -/
noncomputable def port02 : Fin 6 → ℂ := ![-1/4, 1/2, -1/4, -1/4, 0, 1/4]

/-- The incident projection `port03 = pcyc e_{03}`. -/
noncomputable def port03 : Fin 6 → ℂ := ![-1/4, -1/4, 1/2, 0, -1/4, -1/4]

/-- The signed edge action of the stabilizer transposition
`(1 2)`. -/
def u12 : Matrix (Fin 6) (Fin 6) ℂ :=
  !![0, 1, 0, 0, 0, 0;
     1, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0;
     0, 0, 0, -1, 0, 0;
     0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 1, 0]

/-- The signed edge action of the stabilizer transposition
`(2 3)`. -/
def u23 : Matrix (Fin 6) (Fin 6) ℂ :=
  !![1, 0, 0, 0, 0, 0;
     0, 0, 1, 0, 0, 0;
     0, 1, 0, 0, 0, 0;
     0, 0, 0, 0, 1, 0;
     0, 0, 0, 1, 0, 0;
     0, 0, 0, 0, 0, -1]

/-- The projector onto the standard two-dimensional summand:
`pW2 = pcyc - (1/3)·h'h'*`. -/
noncomputable def pW2 : Matrix (Fin 6) (Fin 6) ℂ :=
  pcyc - (1/3 : ℂ) • vecMulVec faceSign (star faceSign)

/-- The face circulation has real entries. -/
lemma star_faceSign : star faceSign = faceSign := by
  funext i
  fin_cases i <;> simp [faceSign]

/-- The ports have real entries. -/
lemma star_ports :
    star port01 = port01 ∧ star port02 = port02 ∧ star port03 = port03 := by
  refine ⟨?_, ?_, ?_⟩ <;> funext i <;>
    fin_cases i <;> simp [port01, port02, port03]

/-- `pW2` with the star evaluated: the entries are real. -/
lemma pW2_real :
    pW2 = pcyc - (1/3 : ℂ) • vecMulVec faceSign faceSign := by
  rw [pW2, star_faceSign]

/-- The explicit entries of `pW2`. -/
lemma pW2_explicit :
    pW2 = !![1/2, -1/4, -1/4, 1/4, 1/4, 0;
             -1/4, 1/2, -1/4, -1/4, 0, 1/4;
             -1/4, -1/4, 1/2, 0, -1/4, -1/4;
             1/4, -1/4, 0, 1/6, 1/12, -1/12;
             1/4, 0, -1/4, 1/12, 1/6, 1/12;
             0, 1/4, -1/4, -1/12, 1/12, 1/6] := by
  rw [pW2_real]
  ext i j
  rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.vecMulVec_apply]
  fin_cases i <;> fin_cases j <;>
    simp [pcyc, faceSign] <;> norm_num

/-- `pcyc` is idempotent. -/
lemma pcyc_idem : pcyc * pcyc = pcyc := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pcyc, Matrix.mul_apply, Fin.sum_univ_six] <;> norm_num

/-- `pcyc` is Hermitian: an orthogonal projector. -/
lemma pcyc_herm : pcycᴴ = pcyc := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pcyc, Matrix.conjTranspose_apply]

/-- `pcyc` has trace `3 = b₁(K₄)`: the harmonic space is
three-dimensional. -/
lemma pcyc_trace : pcyc.trace = 3 := by
  simp [pcyc, Matrix.trace, Matrix.diag, Fin.sum_univ_six]
  norm_num

/-- The three ports are the harmonic projections of the three
coordinate edges at vertex `0`. -/
lemma port_eq :
    pcyc *ᵥ Pi.single (0 : Fin 6) 1 = port01
      ∧ pcyc *ᵥ Pi.single (1 : Fin 6) 1 = port02
      ∧ pcyc *ᵥ Pi.single (2 : Fin 6) 1 = port03 := by
  refine ⟨?_, ?_, ?_⟩ <;> funext i <;>
    fin_cases i <;>
      simp [pcyc, port01, port02, port03, Matrix.mulVec, dotProduct,
        Pi.single_apply]

/-- The face circulation is harmonic. -/
lemma harmonic_faceSign : pcyc *ᵥ faceSign = faceSign := by
  funext i
  fin_cases i <;>
    simp [pcyc, faceSign, Matrix.mulVec, dotProduct,
      Fin.sum_univ_six] <;> norm_num

/-- The stabilizer generators are involutions. -/
lemma stabilizer_invol : u12 * u12 = 1 ∧ u23 * u23 = 1 := by
  constructor <;> ext i j <;>
    fin_cases i <;> fin_cases j <;>
      simp [u12, u23, Matrix.mul_apply, Fin.sum_univ_six]

/-- Both stabilizer generators act by `-1` on the face
circulation: `ℂh'` is the sign representation. -/
lemma sign_rep :
    u12 *ᵥ faceSign = -faceSign ∧ u23 *ᵥ faceSign = -faceSign := by
  constructor <;> funext i <;>
    fin_cases i <;>
      simp [u12, u23, faceSign, Matrix.mulVec, dotProduct,
        Fin.sum_univ_six]

/-- The harmonic projector is stabilizer-equivariant. -/
lemma pcyc_equivariant :
    u12 * pcyc = pcyc * u12 ∧ u23 * pcyc = pcyc * u23 := by
  constructor <;> ext i j <;>
    fin_cases i <;> fin_cases j <;>
      simp [u12, u23, pcyc, Matrix.mul_apply, Fin.sum_univ_six] <;>
        norm_num

/-- The three incident ports sum to zero. -/
lemma port_sum : port01 + port02 + port03 = 0 := by
  funext i
  fin_cases i <;>
    simp [port01, port02, port03] <;> norm_num

/-- The Gram numbers: `⟪q0j,q0j⟫ = 1/2` and
`⟪q0j,q0k⟫ = -1/4` for `j ≠ k`. -/
lemma port_gram :
    (star port01 ⬝ᵥ port01 = 1/2 ∧ star port02 ⬝ᵥ port02 = 1/2
      ∧ star port03 ⬝ᵥ port03 = 1/2)
    ∧ (star port01 ⬝ᵥ port02 = -(1/4) ∧ star port01 ⬝ᵥ port03 = -(1/4)
      ∧ star port02 ⬝ᵥ port03 = -(1/4)) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩ <;>
    simp [port01, port02, port03, dotProduct, Fin.sum_univ_six, map_ofNat] <;>
      norm_num

/-- The stabilizer permutes the port frame. -/
lemma port_covariant :
    (u12 *ᵥ port01 = port02 ∧ u12 *ᵥ port02 = port01 ∧ u12 *ᵥ port03 = port03)
    ∧ (u23 *ᵥ port01 = port01 ∧ u23 *ᵥ port02 = port03 ∧ u23 *ᵥ port03 = port02) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩ <;> funext i <;>
    fin_cases i <;>
      simp [u12, u23, port01, port02, port03, Matrix.mulVec, dotProduct,
        Fin.sum_univ_six] <;> norm_num

/-- `pW2` is a Hermitian idempotent annihilating the sign line,
of trace `2`: the complementary standard summand `W₂` in the
`1+2` decomposition. -/
lemma pW2_projector :
    pW2 * pW2 = pW2 ∧ pW2ᴴ = pW2 ∧ pW2 *ᵥ faceSign = 0
      ∧ pW2.trace = 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [pW2_explicit]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_six] <;> norm_num
  · rw [pW2_explicit]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.conjTranspose_apply]
  · rw [pW2_explicit]
    funext i
    fin_cases i <;>
      simp [faceSign, Matrix.mulVec, dotProduct,
        Fin.sum_univ_six] <;> norm_num
  · rw [pW2_explicit]
    simp [Matrix.trace, Matrix.diag, Fin.sum_univ_six]
    norm_num

/-- `thm:stabilizer-port-frame`, boxed frame identity: the frame
operator of the three incident ports is `(3/4)·P_{W₂}`. -/
theorem stabilizer_port_frame :
    vecMulVec port01 (star port01) + vecMulVec port02 (star port02)
        + vecMulVec port03 (star port03)
      = (3/4 : ℂ) • pW2 := by
  rw [star_ports.1, star_ports.2.1, star_ports.2.2, pW2_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [port01, port02, port03] <;> norm_num

end NCG
