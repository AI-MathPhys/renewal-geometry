/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.ThreeCylinderActionResponseExact

/-!
# Cylinder descent: polar isometries and orthogonal innovations

Machinery for `thm:global-cylinder-descent` (G2) and (G6), addressing the
fidelity-audit gaps: the polar isometries of the square-root supports are
**constructed** (not assumed), their defining intertwining equation, support
normalization, uniqueness on the support, and **strict composition** are
proved; and the orthogonal innovation decomposition of (G6) is likewise
constructed canonically, with the boxed compressed-Gram identity derived.

* `sqrtM_sq`: the spectral square root squares back to a PSD matrix;
* `restricted`: the compressed correlation `R_m = J^* R_n J` (G1 display);
* `polarIso` (G2): `W_{n/m} = R_n^{1/2} J R_m^{†/2}`, with
  - `polarIso_intertwines`: `W_{n/m} R_m^{1/2} = R_n^{1/2} J`,
  - `polarIso_gram`: `W^* W = Q_m` — an isometry on the support of `R_m`,
  - `polarIso_mul_supportProj`: `W` is supported on `Ran R_m`,
  - `polarIso_unique`: any solution of the intertwining equation agrees with
    `W` on the support,
  - `polarIso_comp`: **strict composition** `W_{n/m} W_{m/p} = W_{n/p}`;
* (G6) `restrictedWriter` / `innovationWriter`: the canonical restriction
  `S_m = I^* S_n j` and innovation `η = S_n j − I S_m`, with
  - `innovation_orth`: `η ⊥ I·H_m` (`I^* η = 0`),
  - `innovation_gram`: the boxed identity
    `j_a^* G_{ab,n} j_b = G_{ab,m} + η_a^* η_b`,
  - `exact_compression_iff`: exact joint-source compression is precisely the
    zero-innovation branch.
-/

open Matrix Finset
open scoped ComplexOrder MatrixOrder

namespace NCG
namespace CylinderDescent

open NCG.GeometricThresholdBank NCG.SourceCoercivityInfluence
open NCG.ThreeCylinderActionResponse

variable {dn dm dp : ℕ}

/-! ### Square-root calculus supplements -/

theorem sqrtM_posSemidef {d : ℕ} {M : Matrix (Fin d) (Fin d) ℂ}
    (hM : M.IsHermitian) : (sqrtM hM).PosSemidef := by
  unfold sqrtM
  refine spectralFunction_posSemidef hM _ fun i => ?_
  split_ifs with hl
  · exact Real.sqrt_nonneg _
  · exact le_rfl

theorem sqrtM_isHermitian {d : ℕ} {M : Matrix (Fin d) (Fin d) ℂ}
    (hM : M.IsHermitian) : (sqrtM hM).IsHermitian :=
  (sqrtM_posSemidef hM).1

/-- The spectral square root of a PSD matrix squares back to it. -/
theorem sqrtM_sq {d : ℕ} {M : Matrix (Fin d) (Fin d) ℂ} (hM : M.PosSemidef) :
    sqrtM hM.1 * sqrtM hM.1 = M := by
  have hid := spectralFunction_id hM.1
  unfold sqrtM
  rw [spectralFunction_mul]
  calc spectralFunction hM.1
        (fun l => (if 0 < l then Real.sqrt l else 0) * if 0 < l then Real.sqrt l else 0)
      = spectralFunction hM.1 id := by
        refine spectralFunction_congr hM.1 fun i => ?_
        have hnn := hM.eigenvalues_nonneg i
        simp only [id]
        split_ifs with hl
        · exact Real.mul_self_sqrt hl.le
        · have h0 : hM.1.eigenvalues i = 0 := le_antisymm (not_lt.mp hl) hnn
          rw [h0]; ring
    _ = M := hid

/-- A rectangular factor is supported on the support of its Gram: if
`X^* X = B` then `X Q_B = X`. -/
theorem mul_supportProj_of_gram {a b : ℕ} (X : Matrix (Fin a) (Fin b) ℂ)
    {B : Matrix (Fin b) (Fin b) ℂ} (hB : B.PosSemidef) (hXB : Xᴴ * X = B) :
    X * supportProj hB.1 = X := by
  subst hXB
  exact mul_supportProj_self X

/-! ### (G1)–(G2): the compressed correlation and its polar isometry -/

variable (Rn : Matrix (Fin dn) (Fin dn) ℂ) (J : Matrix (Fin dn) (Fin dm) ℂ)

/-- The compressed old-prefix correlation `R_m = J^* R_n J` (the G1 display). -/
def restricted : Matrix (Fin dm) (Fin dm) ℂ := Jᴴ * Rn * J

/-- The compression is the Gram of `R_n^{1/2} J`. -/
theorem restricted_eq_gram (hRn : Rn.PosSemidef) :
    restricted Rn J = (sqrtM hRn.1 * J)ᴴ * (sqrtM hRn.1 * J) := by
  unfold restricted
  rw [Matrix.conjTranspose_mul, (sqrtM_isHermitian hRn.1).eq]
  have hs : sqrtM hRn.1 * (sqrtM hRn.1 * J) = Rn * J := by
    rw [← Matrix.mul_assoc, sqrtM_sq hRn]
  rw [Matrix.mul_assoc, ← hs, ← Matrix.mul_assoc]

theorem restricted_posSemidef (hRn : Rn.PosSemidef) :
    (restricted Rn J).PosSemidef := by
  rw [restricted_eq_gram Rn J hRn]
  exact posSemidef_conjTranspose_mul_self _

/-- Compression composes: `(J K)^* R_n (J K) = K^* (J^* R_n J) K`. -/
theorem restricted_comp (K : Matrix (Fin dm) (Fin dp) ℂ) :
    restricted (restricted Rn J) K = restricted Rn (J * K) := by
  unfold restricted
  rw [Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

/-- **(G2), existence**: the canonical polar isometry
`W_{n/m} = R_n^{1/2} J R_m^{†/2}`. -/
noncomputable def polarIso (hRn : Rn.PosSemidef) : Matrix (Fin dn) (Fin dm) ℂ :=
  sqrtM hRn.1 * J * invSqrt (restricted_posSemidef Rn J hRn).1

/-- **(G2), the defining intertwining**: `W_{n/m} R_m^{1/2} = R_n^{1/2} J`. -/
theorem polarIso_intertwines (hRn : Rn.PosSemidef) :
    polarIso Rn J hRn * sqrtM (restricted_posSemidef Rn J hRn).1
      = sqrtM hRn.1 * J := by
  unfold polarIso
  rw [Matrix.mul_assoc, invSqrt_mul_sqrtM]
  exact mul_supportProj_of_gram (sqrtM hRn.1 * J) (restricted_posSemidef Rn J hRn)
    (restricted_eq_gram Rn J hRn).symm

/-- **(G2), isometry on the support**: `W^* W = Q_m`. -/
theorem polarIso_gram (hRn : Rn.PosSemidef) :
    (polarIso Rn J hRn)ᴴ * polarIso Rn J hRn
      = supportProj (restricted_posSemidef Rn J hRn).1 := by
  have key := invSqrt_mul_self_mul_invSqrt (restricted_posSemidef Rn J hRn)
  have hmid : ∀ X : Matrix (Fin dm) (Fin dm) ℂ,
      Jᴴ * (sqrtM hRn.1 * (sqrtM hRn.1 * (J * X))) = restricted Rn J * X := by
    intro X
    have h1 : restricted Rn J = Jᴴ * sqrtM hRn.1 * (sqrtM hRn.1 * J) := by
      rw [restricted_eq_gram Rn J hRn, Matrix.conjTranspose_mul,
        (sqrtM_isHermitian hRn.1).eq]
    rw [h1]
    simp only [Matrix.mul_assoc]
  unfold polarIso
  simp only [Matrix.conjTranspose_mul, (invSqrt_isHermitian
    (restricted_posSemidef Rn J hRn).1).eq, (sqrtM_isHermitian hRn.1).eq]
  simp only [Matrix.mul_assoc]
  rw [hmid (invSqrt (restricted_posSemidef Rn J hRn).1), ← Matrix.mul_assoc]
  exact key

/-- `W` is supported on the range of `R_m`. -/
theorem polarIso_mul_supportProj (hRn : Rn.PosSemidef) :
    polarIso Rn J hRn * supportProj (restricted_posSemidef Rn J hRn).1
      = polarIso Rn J hRn := by
  unfold polarIso
  rw [Matrix.mul_assoc, invSqrt_mul_supportProj]

/-- **(G2), uniqueness on the support**: any solution of the intertwining
equation agrees with the canonical polar isometry on the support of `R_m`. -/
theorem polarIso_unique (hRn : Rn.PosSemidef) {W : Matrix (Fin dn) (Fin dm) ℂ}
    (hW : W * sqrtM (restricted_posSemidef Rn J hRn).1 = sqrtM hRn.1 * J) :
    W * supportProj (restricted_posSemidef Rn J hRn).1 = polarIso Rn J hRn := by
  unfold polarIso
  rw [← sqrtM_mul_invSqrt (restricted_posSemidef Rn J hRn).1, ← Matrix.mul_assoc,
    hW]

/-- Transport of the inverse square root along an equality of matrices. -/
theorem invSqrt_congr {a : ℕ} {B B' : Matrix (Fin a) (Fin a) ℂ} (h : B = B')
    (hB : B.IsHermitian) (hB' : B'.IsHermitian) : invSqrt hB = invSqrt hB' := by
  subst h
  rfl

/-- **(G2), strict composition**: `W_{n/m} W_{m/p} = W_{n/p}` — the polar
isometries compose exactly, so the support-completed process algebras form a
raw directed system with no independently assumed prefix-exact family. -/
theorem polarIso_comp (hRn : Rn.PosSemidef) (K : Matrix (Fin dm) (Fin dp) ℂ) :
    polarIso Rn J hRn
        * polarIso (restricted Rn J) K (restricted_posSemidef Rn J hRn)
      = polarIso Rn (J * K) hRn := by
  have hAJP : sqrtM hRn.1 * J * supportProj (restricted_posSemidef Rn J hRn).1
      = sqrtM hRn.1 * J :=
    mul_supportProj_of_gram (sqrtM hRn.1 * J) (restricted_posSemidef Rn J hRn)
      (restricted_eq_gram Rn J hRn).symm
  unfold polarIso
  rw [invSqrt_congr (restricted_comp Rn J K)
    (restricted_posSemidef (restricted Rn J) K (restricted_posSemidef Rn J hRn)).1
    (restricted_posSemidef Rn (J * K) hRn).1]
  simp only [← Matrix.mul_assoc]
  rw [Matrix.mul_assoc (sqrtM hRn.1 * J)
    (invSqrt (restricted_posSemidef Rn J hRn).1)
    (sqrtM (restricted_posSemidef Rn J hRn).1)]
  rw [invSqrt_mul_sqrtM, hAJP]

/-! ### (G6): the orthogonal innovation decomposition -/

variable {hn hm qa qb : ℕ}

/-- The canonical restricted writer `S_m = I^* S_n j`. -/
def restrictedWriter (I : Matrix (Fin hn) (Fin hm) ℂ)
    (Sn : Matrix (Fin hn) (Fin qa) ℂ) (j : Matrix (Fin qa) (Fin qb) ℂ) :
    Matrix (Fin hm) (Fin qb) ℂ := Iᴴ * Sn * j

/-- The orthogonal innovation `η = S_n j − I S_m`. -/
def innovationWriter (I : Matrix (Fin hn) (Fin hm) ℂ)
    (Sn : Matrix (Fin hn) (Fin qa) ℂ) (j : Matrix (Fin qa) (Fin qb) ℂ) :
    Matrix (Fin hn) (Fin qb) ℂ := Sn * j - I * restrictedWriter I Sn j

/-- The defining decomposition `S_n j = I S_m + η`. -/
theorem writer_decomposition (I : Matrix (Fin hn) (Fin hm) ℂ)
    (Sn : Matrix (Fin hn) (Fin qa) ℂ) (j : Matrix (Fin qa) (Fin qb) ℂ) :
    Sn * j = I * restrictedWriter I Sn j + innovationWriter I Sn j := by
  unfold innovationWriter
  abel

/-- **(G6), orthogonality**: `η ⊥ I·H_m`, i.e. `I^* η = 0`, for an isometric
support-completed embedding `I`. -/
theorem innovation_orth (I : Matrix (Fin hn) (Fin hm) ℂ)
    (Sn : Matrix (Fin hn) (Fin qa) ℂ) (j : Matrix (Fin qa) (Fin qb) ℂ)
    (hI : Iᴴ * I = 1) : Iᴴ * innovationWriter I Sn j = 0 := by
  unfold innovationWriter restrictedWriter
  rw [Matrix.mul_sub, ← Matrix.mul_assoc Iᴴ I _, hI, Matrix.one_mul]
  simp only [Matrix.mul_assoc]
  exact sub_self _

/-- **(G6), the boxed compressed-Gram identity**:
`j_a^* G_{ab,n} j_b = G_{ab,m} + η_a^* η_b`. -/
theorem innovation_gram (I : Matrix (Fin hn) (Fin hm) ℂ)
    (Sn : Matrix (Fin hn) (Fin qa) ℂ) (Tn : Matrix (Fin hn) (Fin qb) ℂ)
    {qc qd : ℕ} (ja : Matrix (Fin qa) (Fin qc) ℂ)
    (jb : Matrix (Fin qb) (Fin qd) ℂ) (hI : Iᴴ * I = 1) :
    jaᴴ * (Snᴴ * Tn) * jb
      = (restrictedWriter I Sn ja)ᴴ * restrictedWriter I Tn jb
        + (innovationWriter I Sn ja)ᴴ * innovationWriter I Tn jb := by
  have hoa := innovation_orth I Sn ja hI
  have hob := innovation_orth I Tn jb hI
  have h1 : (I * restrictedWriter I Sn ja)ᴴ * (I * restrictedWriter I Tn jb)
      = (restrictedWriter I Sn ja)ᴴ * restrictedWriter I Tn jb := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Iᴴ I _,
      hI, Matrix.one_mul]
  have h2 : (I * restrictedWriter I Sn ja)ᴴ * innovationWriter I Tn jb = 0 := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, hob, Matrix.mul_zero]
  have h3 : (innovationWriter I Sn ja)ᴴ * (I * restrictedWriter I Tn jb) = 0 := by
    have hIa : (innovationWriter I Sn ja)ᴴ * I = 0 := by
      have hc := congrArg Matrix.conjTranspose hoa
      rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        Matrix.conjTranspose_zero] at hc
    rw [← Matrix.mul_assoc, hIa, Matrix.zero_mul]
  calc jaᴴ * (Snᴴ * Tn) * jb
      = (Sn * ja)ᴴ * (Tn * jb) := by
        rw [Matrix.conjTranspose_mul]
        simp only [Matrix.mul_assoc]
    _ = (I * restrictedWriter I Sn ja + innovationWriter I Sn ja)ᴴ
          * (I * restrictedWriter I Tn jb + innovationWriter I Tn jb) := by
        rw [← writer_decomposition, ← writer_decomposition]
    _ = (restrictedWriter I Sn ja)ᴴ * restrictedWriter I Tn jb
          + (innovationWriter I Sn ja)ᴴ * innovationWriter I Tn jb := by
        rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add,
          Matrix.mul_add, h1, h2, h3, add_zero, zero_add]

/-- **(G6), the exact-compression branch**: the compressed Gram reproduces the
old Gram exactly when the innovation vanishes. -/
theorem exact_compression_iff (I : Matrix (Fin hn) (Fin hm) ℂ)
    (Sn : Matrix (Fin hn) (Fin qa) ℂ) {qc : ℕ}
    (j : Matrix (Fin qa) (Fin qc) ℂ) (hI : Iᴴ * I = 1) :
    innovationWriter I Sn j = 0 ↔
      jᴴ * (Snᴴ * Sn) * j
        = (restrictedWriter I Sn j)ᴴ * restrictedWriter I Sn j := by
  constructor
  · intro h
    rw [innovation_gram I Sn Sn j j hI, h, Matrix.conjTranspose_zero,
      Matrix.mul_zero, add_zero]
  · intro h
    have hg := innovation_gram I Sn Sn j j hI
    rw [h] at hg
    have h0 : (innovationWriter I Sn j)ᴴ * innovationWriter I Sn j = 0 := by
      have hc := congrArg
        (fun M => M - (restrictedWriter I Sn j)ᴴ * restrictedWriter I Sn j) hg.symm
      simpa using hc
    exact Matrix.conjTranspose_mul_self_eq_zero.mp h0

end CylinderDescent
end NCG
