/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.EasyExact01
import NCG.Grand.TraceExpDerivative

/-!
# Easy exact records, batch 02 (Gran-Tensor manuscript)

Exact formalizations of the following manuscript records:

* `thm:RPESM-complete-mixed-short` — the complete mixed sector–quantum Gram
  (RTH.M1–RTH.M6): positivity of the block Gram, the pseudoinverse Schur
  positivity criterion, the completion-of-the-square identity, the canonical
  entrance short `Y = Y∥ + Y⊥` with its four Gram identities, the follower
  criterion, the normalized orthogonal occurrence from a positive eigenvector
  of `R⊥`, the exact source-mass trace split, and the two-dimensional
  witness showing that the diagonal Grams `(S,R)` do not determine ancestry.
* `cth:RPESM-invariant-scalar-no-ray` — no `SU(2)`-fixed ray in the
  fundamental representation on `ℂ²`, hence no equivariant map from a
  trivial scalar record to `ℙ(W_H)`.
* `prop:RPESM-no-infrared-axis` — the fixed spatial carrier
  `(ℤ/(4·2^N)ℤ)³` is finite with cardinality `(4·2^N)³`, and every
  increasing sequence of subsets at fixed `N` stabilizes after finitely
  many steps.
* `cth:RPESM-root-no-infrared-window` — for every `q > 0` and every finite
  periodic carrier, an explicit positive translation-invariant Gaussian
  current law (a genuine `multivariateGaussian` probability measure) whose
  Fourier symbol satisfies `Ĉ(0) = q/2`, `Ĉ(k) = 0` for `k ≠ 0`, hence
  `K̂(0) = 0` and `K̂(k) = q` (WB.29); and a second positive law with
  `Ĉ(0) = q/2`, `Ĉ(k⋆) = q` at one chosen nonzero mode, hence
  `K̂(k⋆) = -q`.
* `thm:SMOS-charge-flux-short` — the simultaneous charge–flux short
  (QSF.6–QSF.8): the orthogonal three-way defect-Gram decomposition, the
  range criterion `ℂ_R^{QΦ} = 0 ↔ Ran Y ⊆ Ran N + Ran Z`, the kernel and
  rank description of the residual, and the exact Gauss landing of the
  charge row modulo nuisance and screening writers.
* `cth:SMOS-finite-translation-no-spectrum` — the kernels `F₁(t) = e^{-t}`
  and `F₂(t) = a e^{-t/2} + (1-a) e^{-2t}` agree at `t = 0, 1`, are both
  completely monotone Laplace kernels of strictly positive finite spectral
  weights, have distinct energy supports and gaps, and differ at `t = 2`.
* `thm:SMQG-balanced-crossing-sign` — the balanced-slab correspondence
  (HX.9–HX.11): `Q_{m,H} ≻ 0`, the exact cross block
  `P = ½[(mI-H)⁻¹ - (mI+H)⁻¹] = H(m²I-H²)⁻¹` of its inverse, the identical
  inertia of `P` and `H` on the common eigenbasis, and `P ⪰ 0 ↔ H ⪰ 0`.
* `cth:SMST-three-record-incidence` — the three-state witness (HIT.17):
  the one-bath Hamiltonian transports to the constant `(ρ+c)I₂` under any
  ground-line transport, the actual tangent vanishes, while `W = QM_xQ` is
  traceless with `‖W‖²_HS = 2/3` and `‖𝒯_{β,h}(W)‖²_HS = a²/3`, giving the
  exact squared mismatch `1/12` at `β = 1`.
* `thm:SMST-Duhamel-Pythagoras` — the Duhamel variance/absorption/birth
  split (DHI.12–DHI.15): `𝕍 = Y*(I-P_A)Y`, `𝔸 = Y*P_N Y`,
  `ℝ_Duh = Y*(I-P_{(A,F)})Y` with `P_{(A,F)} = P_A + P_N`, positivity of
  all three, the exact Pythagoras `𝕍 = 𝔸 + ℝ_Duh`, and the mutually
  exclusive three-branch trichotomy.
* `thm:SMST-mixed-clock-packet` — the exact `3m+3` mixed-clock packet
  (DMC.10–DMC.15): packet cardinality, the reconstruction identities
  `𝖳 = B*Y^{(m)}`, `𝖴 = (Y^{(m)})*Y^{(m)}` by semigroup grouping, the
  supported Schur residual `𝖱 = (Y^{(m)})*(I-P^B)Y^{(m)} ⪰ 0`, the
  endpoint-debit identity `D_end = 𝖪_{2m} - 2𝖪_m + 𝖪_0`, and the
  five-matrix reconstruction `U, G = E - D*S†D, C = T^F - D*S†T` with
  `𝖱 = U - T*S†T - C*G†C`.

Rendering conventions are described in the docstring of each section.
-/

open Matrix Finset
open NCG.SourceCoercivityInfluence NCG.GeometricThresholdBank NCG.PsdBlockSchur
open scoped ComplexOrder

-- decidability/fintype instances enter only through the spectral support calculus in proofs
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace NCG

/-! ### Shared column-range projection toolkit

For a finite matrix `M : k × e`, the Gram `S = MᴴM` is PSD, and the
spectral Moore–Penrose data of `S` produce the orthogonal projection
`colProj M = M S† Mᴴ` onto the column range of `M`.  These lemmas serve
records RTH.M, QSF, DHI and DMC below. -/

section GramProj

variable {k e : Type*} [Fintype k] [Fintype e] [DecidableEq e]

/-- A matrix absorbs the support projection of its own Gram:
`M · 1_{(0,∞)}(MᴴM) = M`. -/
theorem mul_supportProj_gram (M : Matrix k e ℂ) :
    M * supportProj (posSemidef_conjTranspose_mul_self M).1 = M := by
  have hS := posSemidef_conjTranspose_mul_self M
  set Q := supportProj hS.1 with hQdef
  have hQH : Q.IsHermitian := (supportProj_posSemidef hS.1).1
  have hSQ : (Mᴴ * M) * ((1 : Matrix e e ℂ) - Q) = 0 := mul_one_sub_supportProj hS
  have hzero : (M * ((1 : Matrix e e ℂ) - Q))ᴴ * (M * ((1 : Matrix e e ℂ) - Q)) = 0 := by
    have h1H : ((1 : Matrix e e ℂ) - Q)ᴴ = (1 : Matrix e e ℂ) - Q := by
      rw [conjTranspose_sub, conjTranspose_one, hQH.eq]
    calc (M * ((1 : Matrix e e ℂ) - Q))ᴴ * (M * ((1 : Matrix e e ℂ) - Q))
        = ((1 : Matrix e e ℂ) - Q)ᴴ * ((Mᴴ * M) * ((1 : Matrix e e ℂ) - Q)) := by
          rw [conjTranspose_mul]
          simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hSQ, Matrix.mul_zero]
  have hMQ : M * ((1 : Matrix e e ℂ) - Q) = 0 := conjTranspose_mul_self_eq_zero.mp hzero
  rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at hMQ
  exact hMQ.symm

/-- The support projection of the Gram absorbs on the left of `Mᴴ`. -/
theorem supportProj_gram_mul (M : Matrix k e ℂ) :
    supportProj (posSemidef_conjTranspose_mul_self M).1 * Mᴴ = Mᴴ := by
  have h := congrArg conjTranspose (mul_supportProj_gram M)
  rwa [conjTranspose_mul, (supportProj_posSemidef
    (posSemidef_conjTranspose_mul_self M).1).1.eq] at h

/-- The orthogonal projection `colProj M = M (MᴴM)† Mᴴ` onto `Ran M`. -/
noncomputable def colProj (M : Matrix k e ℂ) : Matrix k k ℂ :=
  M * pinv (posSemidef_conjTranspose_mul_self M).1 * Mᴴ

/-- `colProj M` is Hermitian. -/
theorem colProj_isHermitian (M : Matrix k e ℂ) : (colProj M).IsHermitian := by
  unfold colProj
  change (M * pinv _ * Mᴴ)ᴴ = _
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
    (pinv_isHermitian (posSemidef_conjTranspose_mul_self M).1).eq, Matrix.mul_assoc]

/-- `colProj M` fixes the columns of `M`. -/
theorem colProj_mul_self (M : Matrix k e ℂ) : colProj M * M = M := by
  unfold colProj
  simp only [Matrix.mul_assoc]
  rw [← supportProj_eq_pinv_mul, mul_supportProj_gram]

/-- `Mᴴ` absorbs `colProj M` on the right. -/
theorem conjTranspose_mul_colProj (M : Matrix k e ℂ) : Mᴴ * colProj M = Mᴴ := by
  have h := congrArg conjTranspose (colProj_mul_self M)
  rwa [conjTranspose_mul, (colProj_isHermitian M).eq] at h

/-- `colProj M` is idempotent. -/
theorem colProj_idem (M : Matrix k e ℂ) : colProj M * colProj M = colProj M := by
  have hS := posSemidef_conjTranspose_mul_self M
  have hQp : supportProj hS.1 * pinv hS.1 = pinv hS.1 := by
    rw [supportProj_eq_pinv_mul, pinv_mul_self_mul_pinv]
  unfold colProj
  calc M * pinv hS.1 * Mᴴ * (M * pinv hS.1 * Mᴴ)
      = M * (pinv hS.1 * (Mᴴ * M) * (pinv hS.1 * Mᴴ)) := by
        simp only [Matrix.mul_assoc]
    _ = M * (supportProj hS.1 * (pinv hS.1 * Mᴴ)) := by rw [← supportProj_eq_pinv_mul]
    _ = M * (supportProj hS.1 * pinv hS.1 * Mᴴ) := by simp only [Matrix.mul_assoc]
    _ = M * pinv hS.1 * Mᴴ := by rw [hQp]; simp only [Matrix.mul_assoc]

/-- `1 - colProj M` is Hermitian. -/
theorem one_sub_colProj_isHermitian [DecidableEq k] (M : Matrix k e ℂ) :
    ((1 : Matrix k k ℂ) - colProj M).IsHermitian := by
  change ((1 : Matrix k k ℂ) - colProj M)ᴴ = _
  rw [conjTranspose_sub, conjTranspose_one, (colProj_isHermitian M).eq]

/-- `1 - colProj M` is idempotent. -/
theorem one_sub_colProj_idem [DecidableEq k] (M : Matrix k e ℂ) :
    ((1 : Matrix k k ℂ) - colProj M) * ((1 : Matrix k k ℂ) - colProj M)
      = (1 : Matrix k k ℂ) - colProj M := by
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_one, colProj_idem]
  abel

/-- The compressed Gram `Yᴴ (1 - colProj M) Y` in explicit Gram form. -/
theorem one_sub_colProj_gram [DecidableEq k] {f : Type*} (M : Matrix k e ℂ)
    (Y : Matrix k f ℂ) :
    Yᴴ * ((1 : Matrix k k ℂ) - colProj M) * Y
      = (((1 : Matrix k k ℂ) - colProj M) * Y)ᴴ * (((1 : Matrix k k ℂ) - colProj M) * Y) := by
  calc Yᴴ * ((1 : Matrix k k ℂ) - colProj M) * Y
      = Yᴴ * (((1 : Matrix k k ℂ) - colProj M) * ((1 : Matrix k k ℂ) - colProj M)) * Y := by
        rw [one_sub_colProj_idem]
    _ = (((1 : Matrix k k ℂ) - colProj M) * Y)ᴴ * (((1 : Matrix k k ℂ) - colProj M) * Y) := by
        rw [conjTranspose_mul, (one_sub_colProj_isHermitian M).eq]
        simp only [Matrix.mul_assoc]

/-- The compressed Gram `Yᴴ (1 - colProj M) Y` is PSD. -/
theorem one_sub_colProj_gram_posSemidef [DecidableEq k] {f : Type*} [Fintype f]
    (M : Matrix k e ℂ) (Y : Matrix k f ℂ) :
    (Yᴴ * ((1 : Matrix k k ℂ) - colProj M) * Y).PosSemidef := by
  rw [one_sub_colProj_gram]
  exact posSemidef_conjTranspose_mul_self _

/-- The Schur residual of a synthesis pair against a source bank:
`YᴴY - (MᴴY)ᴴ (MᴴM)† (MᴴY) = Yᴴ(1 - colProj M)Y`. -/
theorem schur_residual_eq [DecidableEq k] {f : Type*} (M : Matrix k e ℂ)
    (Y : Matrix k f ℂ) :
    Yᴴ * Y - (Mᴴ * Y)ᴴ * pinv (posSemidef_conjTranspose_mul_self M).1 * (Mᴴ * Y)
      = Yᴴ * ((1 : Matrix k k ℂ) - colProj M) * Y := by
  rw [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_one, colProj]
  simp only [Matrix.mul_assoc]

/-- The compressed Gram `Yᴴ colProj M Y` in explicit Gram form. -/
theorem colProj_gram {f : Type*} (M : Matrix k e ℂ) (Y : Matrix k f ℂ) :
    Yᴴ * colProj M * Y = (colProj M * Y)ᴴ * (colProj M * Y) := by
  calc Yᴴ * colProj M * Y
      = Yᴴ * (colProj M * colProj M) * Y := by rw [colProj_idem]
    _ = (colProj M * Y)ᴴ * (colProj M * Y) := by
        rw [conjTranspose_mul, (colProj_isHermitian M).eq]
        simp only [Matrix.mul_assoc]

/-- The compressed Gram `Yᴴ colProj M Y` is PSD. -/
theorem colProj_gram_posSemidef {f : Type*} [Fintype f] (M : Matrix k e ℂ)
    (Y : Matrix k f ℂ) :
    (Yᴴ * colProj M * Y).PosSemidef := by
  rw [colProj_gram]
  exact posSemidef_conjTranspose_mul_self _

/-- The range condition `(MᴴM)(MᴴM)†(MᴴY) = MᴴY` holds automatically for
Gram data derived from a common carrier. -/
theorem gram_range_condition {f : Type*} (M : Matrix k e ℂ) (Y : Matrix k f ℂ) :
    Mᴴ * M * pinv (posSemidef_conjTranspose_mul_self M).1 * (Mᴴ * Y) = Mᴴ * Y := by
  rw [mul_pinv_eq_supportProj, ← Matrix.mul_assoc, supportProj_gram_mul]

/-- A left annihilator of `M` annihilates `colProj M`. -/
theorem mul_colProj_eq_zero {q : Type*} {X : Matrix q k ℂ} {M : Matrix k e ℂ}
    (h : X * M = 0) : X * colProj M = 0 := by
  unfold colProj
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h, Matrix.zero_mul, Matrix.zero_mul]

/-- A right annihilator of `Mᴴ` is annihilated by `colProj M`. -/
theorem colProj_mul_eq_zero {q : Type*} {M : Matrix k e ℂ} {X : Matrix k q ℂ}
    (h : Mᴴ * X = 0) : colProj M * X = 0 := by
  unfold colProj
  rw [Matrix.mul_assoc, Matrix.mul_assoc, h, Matrix.mul_zero, Matrix.mul_zero]

/-- Congruence for the spectral pseudo-inverse: equal matrices have equal
pseudo-inverses. -/
theorem pinv_congr {n : Type*} [Fintype n] [DecidableEq n] {A B : Matrix n n ℂ}
    (h : A = B) (hA : A.IsHermitian) (hB : B.IsHermitian) : pinv hA = pinv hB := by
  subst h
  rfl

/-- The spectral pseudo-inverse of the identity is the identity. -/
theorem pinv_one {n : Type*} [Fintype n] [DecidableEq n]
    (h : (1 : Matrix n n ℂ).IsHermitian) : pinv h = 1 := by
  have hQ : supportProj h = 1 := by
    have h1 := mul_supportProj (B := (1 : Matrix n n ℂ)) Matrix.PosSemidef.one
    rwa [Matrix.one_mul] at h1
  have h2 := supportProj_eq_pinv_mul h
  rw [Matrix.mul_one] at h2
  rw [← h2, hQ]

end GramProj

/-! ### `thm:RPESM-complete-mixed-short` — Complete mixed sector–quantum Gram

Rendering: the saturated primitive-sector synthesis `B : E_B → ℋ_Q` and the
physical quantum half-source `Y : E_Q → ℋ_Q` are finite complex matrices on
a common finite carrier, as in the manuscript's finite conditioned card.
`S†` is the spectral Moore–Penrose inverse (`pinv`), `‖S^{1/2}w‖²` uses the
spectral square root `psdSqrt`; the iff (RTH.M2) is stated for arbitrary
finite matrices with `S = S* ⪰ 0` and `R = R*` (Hermitianity of `R` is
forced by the block matrix being Hermitian).  The final ancestry witness is
the manuscript's `B(1) = e₁`, `Y⁽¹⁾(1) = e₁`, `Y⁽²⁾(1) = e₂`. -/

section MixedShort

namespace MixedShort

variable {hq eb eQ : Type*} [Fintype hq] [Fintype eb] [Fintype eQ]
  [DecidableEq hq] [DecidableEq eb]

omit [DecidableEq hq] [DecidableEq eb] in
/-- **(RTH.M1)**: the complete mixed Gram `𝔾_{B,Y}` is positive
semidefinite. -/
theorem gram_posSemidef (B : Matrix hq eb ℂ) (Y : Matrix hq eQ ℂ) :
    (fromBlocks (Bᴴ * B) (Bᴴ * Y) (Bᴴ * Y)ᴴ (Yᴴ * Y)).PosSemidef := by
  have hfact : fromBlocks (Bᴴ * B) (Bᴴ * Y) (Bᴴ * Y)ᴴ (Yᴴ * Y)
      = (fromCols B Y)ᴴ * fromCols B Y := by
    rw [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul_fromCols]
    congr 1
    rw [conjTranspose_mul, conjTranspose_conjTranspose]
  rw [hfact]
  exact posSemidef_conjTranspose_mul_self _

/-- **(RTH.M2)**: for arbitrary finite matrices with `S = S* ⪰ 0` and
`R = R*`, positivity of the block Gram is equivalent to the range condition
`(I - SS†)T = 0` together with `R⊥ = R - T*S†T ⪰ 0`. -/
theorem mixed_short_iff {S : Matrix eb eb ℂ} (hS : S.PosSemidef)
    (T : Matrix eb eQ ℂ) {R : Matrix eQ eQ ℂ} (hR : R.IsHermitian) :
    (fromBlocks S T Tᴴ R).PosSemidef ↔
      ((1 : Matrix eb eb ℂ) - S * pinv hS.1) * T = 0 ∧
        (R - Tᴴ * pinv hS.1 * T).PosSemidef := by
  rw [posSemidef_block_iff hS T R hR]
  constructor
  · rintro ⟨hrange, hres⟩
    refine ⟨?_, hres⟩
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero]
    exact hrange.symm
  · rintro ⟨hrange, hres⟩
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at hrange
    exact ⟨hrange.symm, hres⟩

omit [DecidableEq hq] in
/-- **(RTH.M3)**: the exact completion of the square: the block quadratic
form is `‖S^{1/2}(x + S†Ty)‖² + ⟨y, R⊥ y⟩`. -/
theorem entrance_pythagoras (B : Matrix hq eb ℂ) (Y : Matrix hq eQ ℂ)
    (x : eb → ℂ) (y : eQ → ℂ) :
    star (Sum.elim x y) ⬝ᵥ
        (fromBlocks (Bᴴ * B) (Bᴴ * Y) (Bᴴ * Y)ᴴ (Yᴴ * Y) *ᵥ Sum.elim x y)
      = ((∑ i, ‖(psdSqrt (posSemidef_conjTranspose_mul_self B).1 *ᵥ
            (x + pinv (posSemidef_conjTranspose_mul_self B).1 *ᵥ ((Bᴴ * Y) *ᵥ y))) i‖ ^ 2
          : ℝ) : ℂ)
        + star y ⬝ᵥ ((Yᴴ * Y - (Bᴴ * Y)ᴴ * pinv (posSemidef_conjTranspose_mul_self B).1
            * (Bᴴ * Y)) *ᵥ y) := by
  have hS := posSemidef_conjTranspose_mul_self B
  have hrange : Bᴴ * B * pinv hS.1 * (Bᴴ * Y) = Bᴴ * Y := gram_range_condition B Y
  have hsq := completion_of_square hS (Bᴴ * Y) (Yᴴ * Y) hrange x y
  rw [hsq]
  congr 1
  set w := x + pinv hS.1 *ᵥ ((Bᴴ * Y) *ᵥ y) with hw
  have hsqrtH : (psdSqrt hS.1).IsHermitian := (psdSqrt_posSemidef hS.1).1
  calc star w ⬝ᵥ ((Bᴴ * B) *ᵥ w)
      = star w ⬝ᵥ ((psdSqrt hS.1 * psdSqrt hS.1) *ᵥ w) := by rw [psdSqrt_mul_self hS]
    _ = star w ⬝ᵥ (psdSqrt hS.1 *ᵥ (psdSqrt hS.1 *ᵥ w)) := by rw [mulVec_mulVec]
    _ = star (psdSqrt hS.1 *ᵥ w) ⬝ᵥ (psdSqrt hS.1 *ᵥ w) := by
        rw [adjoint_dot (psdSqrt hS.1) w, hsqrtH.eq]
    _ = ((∑ i, ‖(psdSqrt hS.1 *ᵥ w) i‖ ^ 2 : ℝ) : ℂ) := star_dot_self_eq_sum_sq _

omit [DecidableEq hq] in
/-- **(RTH.M4/M5)**: `P_B` is the orthogonal projection onto `Ran B`
(Hermitian, idempotent, fixes `B`, with columns in the range of `B`). -/
theorem entrance_projection (B : Matrix hq eb ℂ) :
    (colProj B).IsHermitian ∧ colProj B * colProj B = colProj B ∧
      colProj B * B = B ∧ ∀ v : hq → ℂ, ∃ u : eb → ℂ, colProj B *ᵥ v = B *ᵥ u :=
  ⟨colProj_isHermitian B, colProj_idem B, colProj_mul_self B, fun v =>
    ⟨(pinv (posSemidef_conjTranspose_mul_self B).1 * Bᴴ) *ᵥ v, by
      rw [colProj, Matrix.mul_assoc, ← mulVec_mulVec]⟩⟩

omit [Fintype eQ] [DecidableEq hq] in
/-- **(RTH.M4)**: the canonical follower `Y∥ = B C⋆ = P_B Y` with
`C⋆ = S†T`. -/
theorem parallel_eq (B : Matrix hq eb ℂ) (Y : Matrix hq eQ ℂ) :
    B * (pinv (posSemidef_conjTranspose_mul_self B).1 * (Bᴴ * Y)) = colProj B * Y := by
  rw [colProj]
  simp only [Matrix.mul_assoc]

omit [Fintype eQ] in
/-- **(RTH.M5)**: the exact entrance split `Y = Y∥ + Y⊥`. -/
theorem entrance_split (B : Matrix hq eb ℂ) (Y : Matrix hq eQ ℂ) :
    Y = colProj B * Y + ((1 : Matrix hq hq ℂ) - colProj B) * Y := by
  rw [Matrix.sub_mul, Matrix.one_mul]
  abel

omit [Fintype eQ] [DecidableEq hq] in
/-- **(RTH.M5)**: the follower Gram `Y∥ᴴ Y∥ = T*S†T`. -/
theorem parallel_gram (B : Matrix hq eb ℂ) (Y : Matrix hq eQ ℂ) :
    (colProj B * Y)ᴴ * (colProj B * Y)
      = (Bᴴ * Y)ᴴ * pinv (posSemidef_conjTranspose_mul_self B).1 * (Bᴴ * Y) := by
  have hS := posSemidef_conjTranspose_mul_self B
  rw [← colProj_gram, colProj, conjTranspose_mul, conjTranspose_conjTranspose]
  calc Yᴴ * (B * pinv hS.1 * Bᴴ) * Y
      = Yᴴ * B * (pinv hS.1 * (Bᴴ * B) * pinv hS.1) * (Bᴴ * Y) := by
        rw [pinv_mul_self_mul_pinv]
        simp only [Matrix.mul_assoc]
    _ = Yᴴ * B * pinv hS.1 * (Bᴴ * Y) := by rw [pinv_mul_self_mul_pinv]
    _ = _ := by simp only [Matrix.mul_assoc]

omit [Fintype eQ] in
/-- **(RTH.M5)**: the orthogonal occurrence Gram `Y⊥ᴴ Y⊥ = R⊥`. -/
theorem perp_gram (B : Matrix hq eb ℂ) (Y : Matrix hq eQ ℂ) :
    (((1 : Matrix hq hq ℂ) - colProj B) * Y)ᴴ * (((1 : Matrix hq hq ℂ) - colProj B) * Y)
      = Yᴴ * Y - (Bᴴ * Y)ᴴ * pinv (posSemidef_conjTranspose_mul_self B).1 * (Bᴴ * Y) := by
  rw [schur_residual_eq, one_sub_colProj_gram]

omit [Fintype eQ] in
/-- **(RTH.M5)**: the cross Gram vanishes: `Y∥ᴴ Y⊥ = 0`. -/
theorem cross_gram_zero (B : Matrix hq eb ℂ) (Y : Matrix hq eQ ℂ) :
    (colProj B * Y)ᴴ * (((1 : Matrix hq hq ℂ) - colProj B) * Y) = 0 := by
  rw [conjTranspose_mul, (colProj_isHermitian B).eq]
  have hkey : colProj B * ((1 : Matrix hq hq ℂ) - colProj B) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, colProj_idem, sub_self]
  calc Yᴴ * colProj B * (((1 : Matrix hq hq ℂ) - colProj B) * Y)
      = Yᴴ * (colProj B * ((1 : Matrix hq hq ℂ) - colProj B)) * Y := by
        simp only [Matrix.mul_assoc]
    _ = 0 := by rw [hkey, Matrix.mul_zero, Matrix.zero_mul]

omit [DecidableEq hq] in
/-- **(RTH.M6)**: the exact source-mass split
`Tr R = Tr(T*S†T) + Tr R⊥`. -/
theorem trace_split (B : Matrix hq eb ℂ) (Y : Matrix hq eQ ℂ) :
    (Yᴴ * Y).trace
      = ((Bᴴ * Y)ᴴ * pinv (posSemidef_conjTranspose_mul_self B).1 * (Bᴴ * Y)).trace
        + (Yᴴ * Y - (Bᴴ * Y)ᴴ * pinv (posSemidef_conjTranspose_mul_self B).1
            * (Bᴴ * Y)).trace := by
  rw [trace_sub]
  all_goals ring

omit [Fintype eQ] in
/-- The follower criterion: `R⊥ = 0` exactly when the quantum half-source
is a deterministic follower of the saturated primitive range. -/
theorem follower_iff (B : Matrix hq eb ℂ) (Y : Matrix hq eQ ℂ) :
    Yᴴ * Y - (Bᴴ * Y)ᴴ * pinv (posSemidef_conjTranspose_mul_self B).1 * (Bᴴ * Y) = 0 ↔
      Y = colProj B * Y := by
  rw [← perp_gram, conjTranspose_mul_self_eq_zero, Matrix.sub_mul, Matrix.one_mul,
    sub_eq_zero]

/-- Every unit eigenvector `u` of `R⊥` with eigenvalue `λ > 0` yields the
normalized occurrence `λ^{-1/2} Y⊥ u`, orthogonal to the primitive range. -/
theorem orthogonal_occurrence (B : Matrix hq eb ℂ) (Y : Matrix hq eQ ℂ)
    {u : eQ → ℂ} {lam : ℝ} (hlam : 0 < lam) (hu : star u ⬝ᵥ u = 1)
    (heig : (Yᴴ * Y - (Bᴴ * Y)ᴴ * pinv (posSemidef_conjTranspose_mul_self B).1
        * (Bᴴ * Y)) *ᵥ u = (lam : ℂ) • u) :
    star ((((Real.sqrt lam)⁻¹ : ℝ) : ℂ) • ((((1 : Matrix hq hq ℂ) - colProj B) * Y) *ᵥ u)) ⬝ᵥ
        ((((Real.sqrt lam)⁻¹ : ℝ) : ℂ) • ((((1 : Matrix hq hq ℂ) - colProj B) * Y) *ᵥ u)) = 1
      ∧ ∀ v : eb → ℂ,
        star (B *ᵥ v) ⬝ᵥ
          ((((Real.sqrt lam)⁻¹ : ℝ) : ℂ) •
            ((((1 : Matrix hq hq ℂ) - colProj B) * Y) *ᵥ u)) = 0 := by
  set M := ((1 : Matrix hq hq ℂ) - colProj B) * Y with hM
  have hMu : star (M *ᵥ u) ⬝ᵥ (M *ᵥ u) = (lam : ℂ) := by
    calc star (M *ᵥ u) ⬝ᵥ (M *ᵥ u)
        = star ((Mᴴ)ᴴ *ᵥ u) ⬝ᵥ (M *ᵥ u) := by rw [conjTranspose_conjTranspose]
      _ = star u ⬝ᵥ (Mᴴ *ᵥ (M *ᵥ u)) := (adjoint_dot Mᴴ u (M *ᵥ u)).symm
      _ = star u ⬝ᵥ ((Mᴴ * M) *ᵥ u) := by rw [mulVec_mulVec]
      _ = star u ⬝ᵥ ((lam : ℂ) • u) := by rw [hM, perp_gram, heig]
      _ = (lam : ℂ) * (star u ⬝ᵥ u) := by rw [dotProduct_smul, smul_eq_mul]
      _ = (lam : ℂ) := by rw [hu, mul_one]
  have hBperp : Bᴴ * M = 0 := by
    have hfix : Bᴴ * ((1 : Matrix hq hq ℂ) - colProj B) = 0 := by
      rw [Matrix.mul_sub, Matrix.mul_one, conjTranspose_mul_colProj, sub_self]
    rw [hM, ← Matrix.mul_assoc, hfix, Matrix.zero_mul]
  constructor
  · rw [star_smul, smul_dotProduct, dotProduct_smul, hMu, smul_eq_mul, smul_eq_mul,
      Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
    norm_cast
    rw [← mul_assoc, ← mul_inv, Real.mul_self_sqrt hlam.le, inv_mul_cancel₀ hlam.ne']
  · intro v
    have h := adjoint_dot Bᴴ v ((((Real.sqrt lam)⁻¹ : ℝ) : ℂ) • (M *ᵥ u))
    rw [conjTranspose_conjTranspose] at h
    rw [← h, mulVec_smul, mulVec_mulVec, hBperp, zero_mulVec, smul_zero, dotProduct_zero]

/-- The manuscript witness synthesis `B(1) = e₁`. -/
def wB : Matrix (Fin 2) (Fin 1) ℂ := !![1; 0]

/-- The follower witness half-source `Y⁽¹⁾(1) = e₁`. -/
def wY1 : Matrix (Fin 2) (Fin 1) ℂ := !![1; 0]

/-- The orthogonal witness half-source `Y⁽²⁾(1) = e₂`. -/
def wY2 : Matrix (Fin 2) (Fin 1) ℂ := !![0; 1]

/-- The diagonal Grams `(S,R)` do not determine ancestry: both witnesses
have `S = R = 1`, but the entrance residual `R⊥` is `0` for `Y⁽¹⁾` and `1`
for `Y⁽²⁾`. -/
theorem ancestry_not_determined :
    wBᴴ * wB = 1 ∧ wY1ᴴ * wY1 = 1 ∧ wY2ᴴ * wY2 = 1 ∧
      wY1ᴴ * wY1 - (wBᴴ * wY1)ᴴ * pinv (posSemidef_conjTranspose_mul_self wB).1
          * (wBᴴ * wY1) = 0 ∧
      wY2ᴴ * wY2 - (wBᴴ * wY2)ᴴ * pinv (posSemidef_conjTranspose_mul_self wB).1
          * (wBᴴ * wY2) = 1 := by
  have hS : wBᴴ * wB = 1 := by
    ext i j
    fin_cases i; fin_cases j
    simp [wB, Matrix.mul_apply, Fin.sum_univ_two]
  have hpinv : pinv (posSemidef_conjTranspose_mul_self wB).1 = 1 := by
    rw [pinv_congr hS (posSemidef_conjTranspose_mul_self wB).1 Matrix.isHermitian_one,
      pinv_one]
  have hT1 : wBᴴ * wY1 = 1 := by
    ext i j
    fin_cases i; fin_cases j
    simp [wB, wY1, Matrix.mul_apply, Fin.sum_univ_two]
  have hT2 : wBᴴ * wY2 = 0 := by
    ext i j
    fin_cases i; fin_cases j
    simp [wB, wY2, Matrix.mul_apply, Fin.sum_univ_two]
  have hR1 : wY1ᴴ * wY1 = 1 := by
    ext i j
    fin_cases i; fin_cases j
    simp [wY1, Matrix.mul_apply, Fin.sum_univ_two]
  have hR2 : wY2ᴴ * wY2 = 1 := by
    ext i j
    fin_cases i; fin_cases j
    simp [wY2, Matrix.mul_apply, Fin.sum_univ_two]
  refine ⟨hS, hR1, hR2, ?_, ?_⟩
  · rw [hR1, hT1, hpinv]
    simp
  · rw [hR2, hT2, hpinv]
    simp

end MixedShort

end MixedShort

/-! ### `cth:RPESM-invariant-scalar-no-ray` — No invariant Higgs ray

Rendering: `W_H = ℂ²` carries the fundamental representation of
`SU(2) = Matrix.specialUnitaryGroup (Fin 2) ℂ` by `mulVec`; a point of
`ℙ(W_H)` is a nonzero vector up to scalar, so an `SU(2)`-equivariant map
from a trivial (one-point or trivially acted) scalar record is exactly a
nonzero `v` with `U v ∥ v` for every `U ∈ SU(2)`.  Nonexistence is proved
from the two explicit special unitaries `diag(i,-i)` and the rotation
`[[0,-1],[1,0]]`. -/

section HiggsRay

namespace HiggsRay

/-- The special unitary rotation witness `[[0,-1],[1,0]]`. -/
def rotU : Matrix (Fin 2) (Fin 2) ℂ := !![0, -1; 1, 0]

/-- The special unitary diagonal witness `diag(i, -i)`. -/
def diagU : Matrix (Fin 2) (Fin 2) ℂ := !![Complex.I, 0; 0, -Complex.I]

set_option linter.unusedSimpArgs false in -- shared entry simp list across `fin_cases` branches
/-- The rotation witness lies in `SU(2)`. -/
theorem rotU_mem : rotU ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  constructor
  · rw [Matrix.mem_unitaryGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rotU, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, star_eq_conjTranspose,
        Matrix.conjTranspose_apply]
  · rw [Matrix.det_fin_two]
    simp [rotU]

set_option linter.unusedSimpArgs false in -- shared entry simp list across `fin_cases` branches
/-- The diagonal witness lies in `SU(2)`. -/
theorem diagU_mem : diagU ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  constructor
  · rw [Matrix.mem_unitaryGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [diagU, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply,
        star_eq_conjTranspose, Matrix.conjTranspose_apply, Complex.ext_iff]
  · rw [Matrix.det_fin_two]
    simp [diagU, Complex.ext_iff]

/-- **No `SU(2)`-fixed Higgs ray**: no nonzero `v ∈ ℂ²` spans a line
preserved by every special unitary. -/
theorem no_invariant_ray :
    ¬ ∃ v : Fin 2 → ℂ, v ≠ 0 ∧
      ∀ U : Matrix (Fin 2) (Fin 2) ℂ, U ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ →
        ∃ c : ℂ, U *ᵥ v = c • v := by
  rintro ⟨v, hv, hfix⟩
  obtain ⟨c2, hc2⟩ := hfix diagU diagU_mem
  obtain ⟨c1, hc1⟩ := hfix rotU rotU_mem
  have hd0 : Complex.I * v 0 = c2 * v 0 := by
    have := congrFun hc2 0
    simpa [diagU, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have hd1 : -(Complex.I * v 1) = c2 * v 1 := by
    have := congrFun hc2 1
    simpa [diagU, Matrix.mulVec, dotProduct, Fin.sum_univ_two, neg_mul] using this
  have hr0 : -(v 1) = c1 * v 0 := by
    have := congrFun hc1 0
    simpa [rotU, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have hr1 : v 0 = c1 * v 1 := by
    have := congrFun hc1 1
    simpa [rotU, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  by_cases h0 : v 0 = 0
  · -- then `v 1 ≠ 0`, but the rotation sends `e₂` off the line
    have h1 : v 1 ≠ 0 := by
      intro h1
      apply hv
      funext i
      fin_cases i
      · exact h0
      · exact h1
    have : v 1 = 0 := by
      have hc10 : c1 = 0 := by
        have := hr1
        rw [h0] at this
        rcases mul_eq_zero.mp this.symm with h | h
        · exact h
        · exact absurd h h1
      have := hr0
      rw [hc10, zero_mul, neg_eq_zero] at this
      exact this
    exact h1 this
  · -- then `c₂ = i` forces `v 1 = 0`, and the rotation kills `v 0`
    have hc2I : c2 = Complex.I := (mul_right_cancel₀ h0 hd0.symm)
    have h1 : v 1 = 0 := by
      rw [hc2I] at hd1
      have h2 : (2 * Complex.I) * v 1 = 0 := by linear_combination -hd1
      rcases mul_eq_zero.mp h2 with h | h
      · exact absurd h (mul_ne_zero two_ne_zero Complex.I_ne_zero)
      · exact h
    apply h0
    rw [hr1, h1, mul_zero]

/-- **`cth:RPESM-invariant-scalar-no-ray`**: there is no `SU(2)`-equivariant
map from a trivial scalar record to `ℙ(W_H)`: no assignment of a ray to the
points of a (nonempty) trivially-acted record can be gauge covariant. -/
theorem no_equivariant_scalar_ray (X : Type*) [Nonempty X] :
    ¬ ∃ f : X → (Fin 2 → ℂ), (∀ x, f x ≠ 0) ∧
      ∀ U : Matrix (Fin 2) (Fin 2) ℂ, U ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ →
        ∀ x : X, ∃ c : ℂ, U *ᵥ f x = c • f x := by
  rintro ⟨f, hnz, hequiv⟩
  exact no_invariant_ray
    ⟨f (Classical.arbitrary X), hnz _, fun U hU => hequiv U hU _⟩

end HiggsRay

end HiggsRay

/-! ### `prop:RPESM-no-infrared-axis` — Ultraviolet refinement is not volume

Rendering: at cutoff `N` the selected spatial carrier is the fixed finite
torus `(ℤ/(4·2^N)ℤ)³`; we prove its cardinality `(4·2^N)³` and that every
increasing (monotone) sequence of subsets of any finite carrier stabilizes
after finitely many steps — the manuscript's two mathematical claims.  The
conclusion that the projective history contains no independent volume
parameter is the manuscript's prose reading of this stabilization. -/

section UVAxis

namespace UVAxis

/-- Any increasing sequence of subsets of a finite carrier stabilizes after
finitely many steps. -/
theorem monotone_stabilizes {α : Type*} [Finite α] (A : ℕ → Set α)
    (hA : Monotone A) : ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → A n = A n₀ := by
  classical
  have := Fintype.ofFinite α
  set idx : α → ℕ := fun x => if hx : ∃ n, x ∈ A n then Nat.find hx else 0 with hidx
  refine ⟨Finset.univ.sup idx, fun n hn => Set.Subset.antisymm (fun x hx => ?_)
    (hA hn)⟩
  have hex : ∃ m, x ∈ A m := ⟨n, hx⟩
  have hmem : x ∈ A (Nat.find hex) := Nat.find_spec hex
  have hle : idx x ≤ Finset.univ.sup idx := Finset.le_sup (Finset.mem_univ x)
  have hidxx : idx x = Nat.find hex := by rw [hidx]; exact dite_eq_left hex
  exact hA (hidxx ▸ hle) hmem

/-- The selected spatial carrier at cutoff `N` is finite with cardinality
`(4·2^N)³` — one fixed physical torus, with no volume axis. -/
theorem card_carrier (N : ℕ) :
    Nat.card (Fin 3 → ZMod (4 * 2 ^ N)) = (4 * 2 ^ N) ^ 3 := by
  have : NeZero (4 * 2 ^ N) := ⟨by positivity⟩
  rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]

/-- **`prop:RPESM-no-infrared-axis`**: on the carrier `(ℤ/(4·2^N)ℤ)³` at
fixed cutoff `N`, any increasing sequence of subsets stabilizes after
finitely many steps; there is no independent `R → ∞` volume axis inside
the projective ultraviolet thread. -/
theorem no_infrared_axis (N : ℕ) (A : ℕ → Set (Fin 3 → ZMod (4 * 2 ^ N)))
    (hA : Monotone A) : ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → A n = A n₀ := by
  have : NeZero (4 * 2 ^ N) := ⟨by positivity⟩
  exact monotone_stabilizes A hA

end UVAxis

end UVAxis

/-! ### `cth:SMOS-finite-translation-no-spectrum` — Finite translation samples

Rendering: the two Laplace kernels are `F₁(t) = e^{-t}` and
`F₂(t) = a e^{-t/2} + (1-a) e^{-2t}` with the manuscript weight
`a = (e^{-1} - e^{-2})/(e^{-1/2} - e^{-2})`.  We prove: agreement at
`t = 0, 1`; strict positivity of both spectral weight systems
(`0 < a < 1`), which exhibits both kernels as Laplace transforms of
strictly positive finite spectral measures; complete monotonicity
`0 ≤ (-1)^n F^{(n)}(t)` of both kernels; the distinct energy supports
`{1}` versus `{1/2, 2}` and distinct gaps `1` versus `1/2`; and the
strict disagreement `F₁(2) < F₂(2)` — a finite panel does not determine
the spectrum. -/

section LaplacePanel

namespace LaplacePanel

/-- The manuscript mixture weight `a = (e⁻¹ - e⁻²)/(e^{-1/2} - e⁻²)`. -/
noncomputable def mixA : ℝ :=
  (Real.exp (-1) - Real.exp (-2)) / (Real.exp (-(1 / 2)) - Real.exp (-2))

/-- The one-line kernel `F₁(t) = e^{-t}`. -/
noncomputable def F1 (t : ℝ) : ℝ := Real.exp (-t)

/-- The two-line kernel `F₂(t) = a e^{-t/2} + (1-a) e^{-2t}`. -/
noncomputable def F2 (t : ℝ) : ℝ :=
  mixA * Real.exp (-(t / 2)) + (1 - mixA) * Real.exp (-(2 * t))

/-- The spectral denominator is positive. -/
theorem denom_pos : 0 < Real.exp (-(1 / 2)) - Real.exp (-2) :=
  sub_pos.mpr (Real.exp_lt_exp.mpr (by norm_num))

/-- The mixture weight is strictly positive. -/
theorem mixA_pos : 0 < mixA :=
  div_pos (sub_pos.mpr (Real.exp_lt_exp.mpr (by norm_num))) denom_pos

/-- The mixture weight is strictly below one. -/
theorem mixA_lt_one : mixA < 1 := by
  rw [mixA, div_lt_one denom_pos]
  have := Real.exp_lt_exp.mpr (show (-1 : ℝ) < -(1 / 2) by norm_num)
  linarith

/-- The defining identity of the mixture weight. -/
theorem mixA_spec :
    mixA * (Real.exp (-(1 / 2)) - Real.exp (-2)) = Real.exp (-1) - Real.exp (-2) :=
  div_mul_cancel₀ _ denom_pos.ne'

/-- The kernels agree at `t = 0`. -/
theorem agree_zero : F1 0 = F2 0 := by
  unfold F1 F2
  norm_num

/-- The kernels agree at `t = 1`. -/
theorem agree_one : F1 1 = F2 1 := by
  unfold F1 F2
  have h := mixA_spec
  norm_num
  linarith

/-- The exponential line `t ↦ e^{-ct}` has derivative `-c e^{-ct}`. -/
theorem hasDerivAt_exp_neg (c t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.exp (-(c * s))) (Real.exp (-(c * t)) * (-c)) t := by
  have h1 : HasDerivAt (fun s : ℝ => -(c * s)) (-c) t := by
    have h2 : HasDerivAt (fun s : ℝ => -c * s) (-c) t := by
      simpa using (hasDerivAt_id t).const_mul (-c)
    have h3 : (fun s : ℝ => -c * s) = fun s : ℝ => -(c * s) := by
      funext s
      ring
    rwa [h3] at h2
  exact (Real.hasDerivAt_exp _).comp t h1

/-- Iterated derivatives of a positive combination of two exponential
lines. -/
theorem iteratedDeriv_mix (al be c d : ℝ) (n : ℕ) :
    iteratedDeriv n
        (fun t : ℝ => al * Real.exp (-(c * t)) + be * Real.exp (-(d * t)))
      = fun t : ℝ => al * ((-c) ^ n * Real.exp (-(c * t)))
          + be * ((-d) ^ n * Real.exp (-(d * t))) := by
  induction n with
  | zero => funext t; simp
  | succ n ih =>
      rw [iteratedDeriv_succ, ih]
      funext t
      have h : HasDerivAt
          (fun t : ℝ => al * ((-c) ^ n * Real.exp (-(c * t)))
            + be * ((-d) ^ n * Real.exp (-(d * t))))
          (al * ((-c) ^ n * (Real.exp (-(c * t)) * (-c)))
            + be * ((-d) ^ n * (Real.exp (-(d * t)) * (-d)))) t := by
        exact (((hasDerivAt_exp_neg c t).const_mul ((-c) ^ n)).const_mul al).add
          (((hasDerivAt_exp_neg d t).const_mul ((-d) ^ n)).const_mul be)
      rw [h.deriv]
      ring

/-- The single-line kernel in two-line form (with zero second weight). -/
theorem F1_eq : F1 = fun t : ℝ => 1 * Real.exp (-(1 * t)) + 0 * Real.exp (-(2 * t)) := by
  funext t
  unfold F1
  rw [one_mul, zero_mul, add_zero, one_mul]

/-- The two-line kernel in normal form. -/
theorem F2_eq :
    F2 = fun t : ℝ => mixA * Real.exp (-(1 / 2 * t)) + (1 - mixA) * Real.exp (-(2 * t)) := by
  funext t
  unfold F2
  rw [show -(t / 2) = -(1 / 2 * t) by ring]

/-- Sign cancellation `(-1)ⁿ (-c)ⁿ = cⁿ`. -/
theorem neg_one_pow_mul_neg_pow (c : ℝ) (n : ℕ) : (-1 : ℝ) ^ n * (-c) ^ n = c ^ n := by
  rw [← mul_pow]
  norm_num

/-- **Complete monotonicity of `F₁`**: `0 ≤ (-1)ⁿ F₁⁽ⁿ⁾(t)`. -/
theorem F1_completely_monotone (n : ℕ) (t : ℝ) : 0 ≤ (-1 : ℝ) ^ n * iteratedDeriv n F1 t := by
  rw [F1_eq, iteratedDeriv_mix]
  have h1 := neg_one_pow_mul_neg_pow 1 n
  have key : (-1 : ℝ) ^ n * (1 * ((-1) ^ n * Real.exp (-(1 * t)))
      + 0 * ((-2) ^ n * Real.exp (-(2 * t))))
      = Real.exp (-(1 * t)) := by
    linear_combination Real.exp (-(1 * t)) * h1
  rw [key]
  exact (Real.exp_pos (-(1 * t))).le

/-- **Complete monotonicity of `F₂`**: `0 ≤ (-1)ⁿ F₂⁽ⁿ⁾(t)`. -/
theorem F2_completely_monotone (n : ℕ) (t : ℝ) : 0 ≤ (-1 : ℝ) ^ n * iteratedDeriv n F2 t := by
  rw [F2_eq, iteratedDeriv_mix]
  have h1 := neg_one_pow_mul_neg_pow (1 / 2) n
  have h2 := neg_one_pow_mul_neg_pow 2 n
  have key : (-1 : ℝ) ^ n * (mixA * ((-(1 / 2)) ^ n * Real.exp (-(1 / 2 * t)))
      + (1 - mixA) * ((-2) ^ n * Real.exp (-(2 * t))))
      = mixA * ((1 / 2 : ℝ) ^ n * Real.exp (-(1 / 2 * t)))
        + (1 - mixA) * ((2 : ℝ) ^ n * Real.exp (-(2 * t))) := by
    linear_combination (mixA * Real.exp (-(1 / 2 * t))) * h1
      + ((1 - mixA) * Real.exp (-(2 * t))) * h2
  rw [key]
  have ha := mixA_pos
  have hb := mixA_lt_one
  have p1 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ n * Real.exp (-(1 / 2 * t)) := by positivity
  have p2 : (0 : ℝ) ≤ (2 : ℝ) ^ n * Real.exp (-(2 * t)) := by positivity
  have hb' : (0 : ℝ) ≤ 1 - mixA := by linarith
  exact add_nonneg (mul_nonneg ha.le p1) (mul_nonneg hb' p2)

/-- The spectral weight system of `F₁`: mass `1` at energy `1`. -/
noncomputable def w1 : ℝ → ℝ := fun lam => if lam = 1 then 1 else 0

/-- The spectral weight system of `F₂`: mass `a` at `1/2` and `1-a`
at `2`. -/
noncomputable def w2 : ℝ → ℝ := fun lam =>
  if lam = 1 / 2 then mixA else if lam = 2 then 1 - mixA else 0

/-- `F₁` is the Laplace transform of its strictly positive one-point
spectral weight. -/
theorem F1_spectral (t : ℝ) :
    F1 t = ∑ lam ∈ ({1} : Finset ℝ), w1 lam * Real.exp (-(lam * t)) := by
  rw [Finset.sum_singleton]
  unfold F1 w1
  norm_num

/-- `F₂` is the Laplace transform of its strictly positive two-point
spectral weight. -/
theorem F2_spectral (t : ℝ) :
    F2 t = ∑ lam ∈ ({1 / 2, 2} : Finset ℝ), w2 lam * Real.exp (-(lam * t)) := by
  rw [Finset.sum_insert (by norm_num), Finset.sum_singleton]
  have h1 : w2 (1 / 2) = mixA := by norm_num [w2]
  have h2 : w2 2 = 1 - mixA := by norm_num [w2]
  rw [h1, h2]
  unfold F2
  rw [show -(t / 2) = -(1 / 2 * t) by ring]

/-- Both weight systems are strictly positive on their supports. -/
theorem weights_pos :
    (∀ lam ∈ ({1} : Finset ℝ), 0 < w1 lam) ∧
      ∀ lam ∈ ({1 / 2, 2} : Finset ℝ), 0 < w2 lam := by
  constructor
  · intro lam hlam
    rw [Finset.mem_singleton] at hlam
    simp [w1, hlam]
  · intro lam hlam
    rcases Finset.mem_insert.mp hlam with h | h
    · simp only [w2, h]
      norm_num [mixA_pos]
    · rw [Finset.mem_singleton] at h
      simp only [w2, h]
      norm_num [mixA_lt_one]

/-- The energy support of `F₁` is `{1}`. -/
theorem support_w1 : Function.support w1 = {1} := by
  ext lam
  simp [w1, Function.mem_support]

/-- The energy support of `F₂` is `{1/2, 2}`. -/
theorem support_w2 : Function.support w2 = {1 / 2, 2} := by
  have ha : mixA ≠ 0 := mixA_pos.ne'
  have hb : 1 - mixA ≠ 0 := by have := mixA_lt_one; intro h; linarith
  ext lam
  constructor
  · intro hmem
    rw [Function.mem_support] at hmem
    by_cases h1 : lam = 1 / 2
    · exact Or.inl h1
    · by_cases h2 : lam = 2
      · exact Or.inr h2
      · refine absurd ?_ hmem
        change (if lam = 1 / 2 then mixA else if lam = 2 then 1 - mixA else 0) = 0
        rw [ite_eq_right h1, ite_eq_right h2]
  · intro hmem
    rw [Function.mem_support]
    rcases hmem with h | h
    · subst h
      change (if (1 / 2 : ℝ) = 1 / 2 then mixA else if (1 / 2 : ℝ) = 2 then 1 - mixA else 0) ≠ 0
      rw [ite_eq_left rfl]
      exact ha
    · rw [Set.mem_singleton_iff] at h
      subst h
      have h12 : (2 : ℝ) ≠ 1 / 2 := by norm_num
      change (if (2 : ℝ) = 1 / 2 then mixA else if (2 : ℝ) = 2 then 1 - mixA else 0) ≠ 0
      rw [ite_eq_right h12, ite_eq_left rfl]
      exact hb

/-- **The energy supports differ**. -/
theorem supports_differ : Function.support w1 ≠ Function.support w2 := by
  rw [support_w1, support_w2]
  intro h
  have h2 : (2 : ℝ) ∈ ({1} : Set ℝ) := by
    rw [h]
    right
    rfl
  rw [Set.mem_singleton_iff] at h2
  norm_num at h2

/-- **The spectral gaps differ**: `inf supp = 1` for `F₁` and `1/2`
for `F₂`. -/
theorem gaps_differ :
    sInf (Function.support w1) = 1 ∧ sInf (Function.support w2) = 1 / 2 := by
  constructor
  · rw [support_w1, csInf_singleton]
  · rw [support_w2, csInf_pair]
    exact inf_eq_left.mpr (by norm_num)

/-- **The kernels themselves differ**: strict Cauchy–Schwarz defect at the
held-out sample `t = 2`. -/
theorem strict_gap_at_two : F1 2 < F2 2 := by
  set u := Real.exp (-(1 / 2 : ℝ)) with hu
  set w := Real.exp (-(2 : ℝ)) with hw
  have hmix : mixA * u + (1 - mixA) * w = Real.exp (-(1 : ℝ)) := by
    have h := agree_one
    unfold F1 F2 at h
    rw [show -(1 / 2 : ℝ) = -((1 : ℝ) / 2) by norm_num, show -(2 * (1 : ℝ)) = -(2 : ℝ)
      by norm_num] at h
    rw [hu, hw]
    linarith
  have hkey : F2 2 - F1 2 = mixA * (1 - mixA) * (u - w) ^ 2 := by
    have h1 : Real.exp (-(2 / 2 : ℝ)) = u * u := by
      rw [hu, ← Real.exp_add]
      norm_num
    have h4 : Real.exp (-(2 * 2 : ℝ)) = w * w := by
      rw [hw, ← Real.exp_add]
      norm_num
    have h2 : Real.exp (-(2 : ℝ))
        = (mixA * u + (1 - mixA) * w) * (mixA * u + (1 - mixA) * w) := by
      rw [hmix, ← Real.exp_add]
      norm_num
    unfold F1 F2
    rw [h1, h4, h2]
    ring
  have hne : w < u := Real.exp_lt_exp.mpr (by norm_num)
  have hpos : 0 < mixA * (1 - mixA) * (u - w) ^ 2 := by
    have h1 := mixA_pos
    have h2 := mixA_lt_one
    have h3 : (0 : ℝ) < (u - w) ^ 2 := pow_pos (sub_pos.mpr hne) 2
    have h4 : (0 : ℝ) < 1 - mixA := by linarith
    positivity
  linarith

end LaplacePanel

end LaplacePanel

/-! ### `thm:SMQG-balanced-crossing-sign` — Balanced-slab sign correspondence

Rendering: `H = H^*` on a finite `r`-dimensional carrier, and the manuscript
hypothesis `m > ‖H‖_op` is rendered in its equivalent spectral form
`|λᵢ(H)| < m` for every eigenvalue (for Hermitian `H` the operator norm is
the largest `|λᵢ|`).  `(mI ± H)⁻¹` and `(m²I - H²)⁻¹` are the actual matrix
inverses (`Matrix.inv`), identified with their spectral-calculus forms; the
inertia statement is rendered on the common orthonormal eigenbasis, giving
the eigenvalue correspondence `P eᵢ = λᵢ/(m²-λᵢ²) eᵢ`, the pointwise sign
equivalences, and the equality of the three inertia counts. -/

section CrossSign

namespace CrossSign

variable {r : Type*} [Fintype r] [DecidableEq r]

/-- A spectral function with strictly positive values on the spectrum is
positive definite. -/
theorem spectralFunction_posDef {S : Matrix r r ℂ} (hS : S.IsHermitian) (f : ℝ → ℝ)
    (hf : ∀ i, 0 < f (hS.eigenvalues i)) : (spectralFunction hS f).PosDef := by
  have hpsd := spectralFunction_posSemidef hS f fun i => (hf i).le
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hpsd.1 fun x hx => ?_
  rcases lt_or_eq_of_le (hpsd.dotProduct_mulVec_nonneg x) with h | h
  · exact h
  · exfalso
    apply hx
    have hker : spectralFunction hS f *ᵥ x = 0 :=
      (hpsd.dotProduct_mulVec_zero_iff x).mp h.symm
    have hone : spectralFunction hS (fun l => (f l)⁻¹) * spectralFunction hS f = 1 := by
      rw [spectralFunction_mul]
      calc spectralFunction hS (fun l => (f l)⁻¹ * f l)
          = spectralFunction hS (fun _ => 1) :=
            spectralFunction_congr hS fun i => inv_mul_cancel₀ (hf i).ne'
        _ = 1 := by rw [spectralFunction_const, Complex.ofReal_one, one_smul]
    calc x = (1 : Matrix r r ℂ) *ᵥ x := (one_mulVec x).symm
      _ = (spectralFunction hS (fun l => (f l)⁻¹) * spectralFunction hS f) *ᵥ x := by
          rw [hone]
      _ = spectralFunction hS (fun l => (f l)⁻¹) *ᵥ (spectralFunction hS f *ᵥ x) :=
          (mulVec_mulVec _ _ _).symm
      _ = 0 := by rw [hker, mulVec_zero]

/-- A spectral function acts on the orthonormal eigenbasis by its scalar
values. -/
theorem spectralFunction_mulVec_eigenvectorBasis {S : Matrix r r ℂ} (hS : S.IsHermitian)
    (f : ℝ → ℝ) (i : r) :
    spectralFunction hS f *ᵥ ⇑(hS.eigenvectorBasis i)
      = ((f (hS.eigenvalues i) : ℝ) : ℂ) • ⇑(hS.eigenvectorBasis i) := by
  set U := (hS.eigenvectorUnitary : Matrix r r ℂ) with hU
  have hUU : star U * U = 1 := UnitaryGroup.star_mul_self hS.eigenvectorUnitary
  have hcol : ⇑(hS.eigenvectorBasis i) = U *ᵥ Pi.single i 1 :=
    (hS.eigenvectorUnitary_mulVec i).symm
  rw [hcol]
  unfold spectralFunction
  rw [Unitary.conjStarAlgAut_apply]
  calc (U * diagonal (RCLike.ofReal ∘ fun j => f (hS.eigenvalues j)) * star U)
        *ᵥ (U *ᵥ Pi.single i 1)
      = (U * diagonal (RCLike.ofReal ∘ fun j => f (hS.eigenvalues j)) * (star U * U))
        *ᵥ Pi.single i 1 := by
        rw [mulVec_mulVec]
        simp only [Matrix.mul_assoc]
    _ = (U * diagonal (RCLike.ofReal ∘ fun j => f (hS.eigenvalues j))) *ᵥ Pi.single i 1 := by
        rw [hUU, Matrix.mul_one]
    _ = U *ᵥ (diagonal (RCLike.ofReal ∘ fun j => f (hS.eigenvalues j)) *ᵥ Pi.single i 1) :=
        (mulVec_mulVec _ _ _).symm
    _ = U *ᵥ (((f (hS.eigenvalues i) : ℝ) : ℂ) • Pi.single i 1) := by
        congr 1
        funext j
        by_cases hij : j = i
        · subst hij
          simp [Matrix.mulVec_diagonal]
        · simp [Matrix.mulVec_diagonal, Pi.single_eq_of_ne hij]
    _ = ((f (hS.eigenvalues i) : ℝ) : ℂ) • (U *ᵥ Pi.single i 1) := mulVec_smul _ _ _

/-- The eigenbasis columns are orthonormal. -/
theorem eigenvectorBasis_orthonormal {S : Matrix r r ℂ} (hS : S.IsHermitian) (i j : r) :
    star ⇑(hS.eigenvectorBasis i) ⬝ᵥ ⇑(hS.eigenvectorBasis j)
      = if i = j then 1 else 0 := by
  have hUU : star (hS.eigenvectorUnitary : Matrix r r ℂ) * hS.eigenvectorUnitary = 1 :=
    UnitaryGroup.star_mul_self hS.eigenvectorUnitary
  calc star ⇑(hS.eigenvectorBasis i) ⬝ᵥ ⇑(hS.eigenvectorBasis j)
      = (star (hS.eigenvectorUnitary : Matrix r r ℂ) * hS.eigenvectorUnitary) i j := by
        rw [Matrix.mul_apply]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Matrix.star_apply, hS.eigenvectorUnitary_apply, hS.eigenvectorUnitary_apply]
        rfl
    _ = (1 : Matrix r r ℂ) i j := by rw [hUU]
    _ = if i = j then 1 else 0 := Matrix.one_apply

variable {H : Matrix r r ℂ}

/-- The balanced slab `Q_{m,H}` (HX.9). -/
def slab (H : Matrix r r ℂ) (m : ℝ) : Matrix (r ⊕ r) (r ⊕ r) ℂ :=
  fromBlocks ((m : ℂ) • 1) (-H) (-H) ((m : ℂ) • 1)

/-- The balanced cross block `P_{m,H} = H(m²I - H²)⁻¹` in spectral form. -/
noncomputable def crossBlock (hH : H.IsHermitian) (m : ℝ) : Matrix r r ℂ :=
  spectralFunction hH (fun l => l / (m ^ 2 - l ^ 2))

/-- The balanced diagonal block `m(m²I - H²)⁻¹` in spectral form. -/
noncomputable def diagBlock (hH : H.IsHermitian) (m : ℝ) : Matrix r r ℂ :=
  spectralFunction hH (fun l => m / (m ^ 2 - l ^ 2))

/-- The strict slab window `m² - λᵢ² > 0`. -/
theorem window_pos (hH : H.IsHermitian) {m : ℝ} (hm : ∀ i, |hH.eigenvalues i| < m) (i : r) :
    0 < m ^ 2 - hH.eigenvalues i ^ 2 := by
  have h := abs_lt.mp (hm i)
  nlinarith [h.1, h.2]

/-- The quadratic form of the balanced slab splits into the two shifted
Hermitian forms. -/
theorem slab_form (hH : H.IsHermitian) (m : ℝ) (x y : r → ℂ) :
    star (Sum.elim x y) ⬝ᵥ (slab H m *ᵥ Sum.elim x y)
      = ((1 / 2 : ℝ) : ℂ) * (star (x + y) ⬝ᵥ ((((m : ℂ) • 1 - H)) *ᵥ (x + y))
          + star (x - y) ⬝ᵥ ((((m : ℂ) • 1 + H)) *ᵥ (x - y))) := by
  have hBH : (-H)ᴴ = -H := by rw [conjTranspose_neg, hH.eq]
  have hb : slab H m = fromBlocks ((m : ℂ) • 1) (-H) (-H)ᴴ ((m : ℂ) • 1) := by
    unfold slab
    rw [hBH]
  rw [hb, block_form, hBH]
  simp only [mulVec_add, mulVec_sub, sub_mulVec, add_mulVec, star_add, star_sub,
    add_dotProduct, sub_dotProduct, dotProduct_add, dotProduct_sub, Matrix.smul_mulVec,
    one_mulVec, dotProduct_smul, smul_eq_mul, neg_mulVec, dotProduct_neg,
    Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  ring

/-- The shifted matrix `mI - H` in spectral form. -/
theorem smul_one_sub_spectral (hH : H.IsHermitian) (m : ℝ) :
    (m : ℂ) • 1 - H = spectralFunction hH (fun l => m - l) :=
  smul_one_sub_eq_spectral hH m

/-- The shifted matrix `mI + H` in spectral form. -/
theorem smul_one_add_spectral (hH : H.IsHermitian) (m : ℝ) :
    (m : ℂ) • 1 + H = spectralFunction hH (fun l => m + l) := by
  have h := spectralFunction_add hH (fun _ => m) id
  rw [spectralFunction_id, spectralFunction_const] at h
  exact h.symm

/-- **(HX.9)**: the balanced slab is positive definite. -/
theorem slab_posDef (hH : H.IsHermitian) {m : ℝ} (hm : ∀ i, |hH.eigenvalues i| < m) :
    (slab H m).PosDef := by
  have hmm : ((m : ℂ) • 1 - H).PosDef := by
    rw [smul_one_sub_spectral hH m]
    refine spectralFunction_posDef hH _ fun i => ?_
    have := abs_lt.mp (hm i)
    linarith [this.2]
  have hmp : ((m : ℂ) • 1 + H).PosDef := by
    rw [smul_one_add_spectral hH m]
    refine spectralFunction_posDef hH _ fun i => ?_
    have := abs_lt.mp (hm i)
    linarith [this.1]
  have hherm : (slab H m).IsHermitian := by
    have hBH : (-H)ᴴ = -H := by rw [conjTranspose_neg, hH.eq]
    have hd : ((m : ℂ) • (1 : Matrix r r ℂ)).IsHermitian := by
      change ((m : ℂ) • (1 : Matrix r r ℂ))ᴴ = _
      rw [conjTranspose_smul, conjTranspose_one, Complex.star_def, Complex.conj_ofReal]
    have hb : slab H m = fromBlocks ((m : ℂ) • 1) (-H) (-H)ᴴ ((m : ℂ) • 1) := by
      unfold slab
      rw [hBH]
    rw [hb]
    exact Matrix.IsHermitian.fromBlocks hd rfl hd
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hherm fun z hz => ?_
  set x := z ∘ Sum.inl with hx
  set y := z ∘ Sum.inr with hy
  have hzelim : z = Sum.elim x y := (Sum.elim_comp_inl_inr z).symm
  have hne : x + y ≠ 0 ∨ x - y ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hz
    have h1 : x = 0 := by
      funext i
      have ha := congrFun hcon.1 i
      have hb := congrFun hcon.2 i
      rw [Pi.add_apply, Pi.zero_apply] at ha
      rw [Pi.sub_apply, Pi.zero_apply] at hb
      have h2 : (2 : ℂ) * x i = 0 := by linear_combination ha + hb
      rcases mul_eq_zero.mp h2 with h | h
      · norm_num at h
      · exact h
    have h2 : y = 0 := by
      funext i
      have ha := congrFun hcon.1 i
      rw [Pi.add_apply, Pi.zero_apply] at ha
      have hx0 := congrFun h1 i
      rw [Pi.zero_apply] at hx0
      rw [hx0, zero_add] at ha
      exact ha
    rw [hzelim, h1, h2]
    funext i
    cases i <;> rfl
  rw [hzelim, slab_form hH m x y]
  have hform : ∀ w : r → ℂ, (star w ⬝ᵥ (((m : ℂ) • 1 - H) *ᵥ w)).im = 0 ∧
      0 ≤ (star w ⬝ᵥ (((m : ℂ) • 1 - H) *ᵥ w)).re := by
    intro w
    constructor
    · have := hermitian_form_ofReal hmm.1 w
      rw [this]
      exact Complex.ofReal_im _
    · exact re_form_nonneg hmm.posSemidef w
  have hform' : ∀ w : r → ℂ, (star w ⬝ᵥ (((m : ℂ) • 1 + H) *ᵥ w)).im = 0 ∧
      0 ≤ (star w ⬝ᵥ (((m : ℂ) • 1 + H) *ᵥ w)).re := by
    intro w
    constructor
    · have := hermitian_form_ofReal hmp.1 w
      rw [this]
      exact Complex.ofReal_im _
    · exact re_form_nonneg hmp.posSemidef w
  have hstrict : 0 < (star (x + y) ⬝ᵥ (((m : ℂ) • 1 - H) *ᵥ (x + y))).re
      + (star (x - y) ⬝ᵥ (((m : ℂ) • 1 + H) *ᵥ (x - y))).re := by
    rcases hne with h | h
    · have := re_form_pos hmm h
      have := (hform' (x - y)).2
      linarith
    · have := re_form_pos hmp h
      have := (hform (x + y)).2
      linarith
  rw [Complex.lt_def]
  constructor
  · rw [Complex.zero_re, Complex.mul_re, Complex.add_re, Complex.add_im,
      (hform (x + y)).1, (hform' (x - y)).1, Complex.ofReal_re, Complex.ofReal_im]
    linarith
  · rw [Complex.zero_im, Complex.mul_im, Complex.add_re, Complex.add_im,
      (hform (x + y)).1, (hform' (x - y)).1, Complex.ofReal_re, Complex.ofReal_im]
    ring

/-- `(mI - H)⁻¹` is the spectral resolvent. -/
theorem inv_smul_one_sub (hH : H.IsHermitian) {m : ℝ} (hm : ∀ i, |hH.eigenvalues i| < m) :
    ((m : ℂ) • 1 - H)⁻¹ = spectralFunction hH (fun l => (m - l)⁻¹) := by
  refine Matrix.inv_eq_right_inv ?_
  rw [smul_one_sub_spectral hH m, spectralFunction_mul]
  calc spectralFunction hH (fun l => (m - l) * (m - l)⁻¹)
      = spectralFunction hH (fun _ => 1) := by
        refine spectralFunction_congr hH fun i => mul_inv_cancel₀ ?_
        have := abs_lt.mp (hm i)
        intro hcon
        have : hH.eigenvalues i = m := by linarith [sub_eq_zero.mp hcon]
        linarith [this ▸ (abs_lt.mp (hm i)).2]
    _ = 1 := by rw [spectralFunction_const, Complex.ofReal_one, one_smul]

/-- `(mI + H)⁻¹` is the spectral resolvent. -/
theorem inv_smul_one_add (hH : H.IsHermitian) {m : ℝ} (hm : ∀ i, |hH.eigenvalues i| < m) :
    ((m : ℂ) • 1 + H)⁻¹ = spectralFunction hH (fun l => (m + l)⁻¹) := by
  refine Matrix.inv_eq_right_inv ?_
  rw [smul_one_add_spectral hH m, spectralFunction_mul]
  calc spectralFunction hH (fun l => (m + l) * (m + l)⁻¹)
      = spectralFunction hH (fun _ => 1) := by
        refine spectralFunction_congr hH fun i => mul_inv_cancel₀ ?_
        have h := abs_lt.mp (hm i)
        intro hcon
        have : hH.eigenvalues i = -m := by linarith [add_eq_zero_iff_eq_neg.mp hcon]
        rw [this] at h
        linarith [h.1]
    _ = 1 := by rw [spectralFunction_const, Complex.ofReal_one, one_smul]

/-- `(m²I - H²)⁻¹` is the spectral resolvent of the squared window. -/
theorem inv_sq_window (hH : H.IsHermitian) {m : ℝ} (hm : ∀ i, |hH.eigenvalues i| < m) :
    (((m ^ 2 : ℝ) : ℂ) • 1 - H * H)⁻¹
      = spectralFunction hH (fun l => (m ^ 2 - l ^ 2)⁻¹) := by
  have hsq : ((m ^ 2 : ℝ) : ℂ) • 1 - H * H
      = spectralFunction hH (fun l => m ^ 2 - l ^ 2) := by
    have hHH : H * H = spectralFunction hH (fun l => l * l) := by
      have h := spectralFunction_mul hH id id
      rw [spectralFunction_id] at h
      exact h
    have h := spectralFunction_sub hH (fun _ => m ^ 2) (fun l => l * l)
    rw [spectralFunction_const] at h
    rw [hHH, ← h]
    refine spectralFunction_congr hH fun i => ?_
    ring
  refine Matrix.inv_eq_right_inv ?_
  rw [hsq, spectralFunction_mul]
  calc spectralFunction hH (fun l => (m ^ 2 - l ^ 2) * (m ^ 2 - l ^ 2)⁻¹)
      = spectralFunction hH (fun _ => 1) :=
        spectralFunction_congr hH fun i => mul_inv_cancel₀ (window_pos hH hm i).ne'
    _ = 1 := by rw [spectralFunction_const, Complex.ofReal_one, one_smul]

/-- **(HX.10), first form**: the cross block is the balanced resolvent
difference `½[(mI-H)⁻¹ - (mI+H)⁻¹]`. -/
theorem crossBlock_eq_resolvent_difference (hH : H.IsHermitian) {m : ℝ}
    (hm : ∀ i, |hH.eigenvalues i| < m) :
    crossBlock hH m
      = ((1 / 2 : ℝ) : ℂ) • (((m : ℂ) • 1 - H)⁻¹ - ((m : ℂ) • 1 + H)⁻¹) := by
  rw [inv_smul_one_sub hH hm, inv_smul_one_add hH hm, ← spectralFunction_sub,
    ← spectralFunction_smul]
  refine spectralFunction_congr hH fun i => ?_
  have hw := window_pos hH hm i
  have h := abs_lt.mp (hm i)
  have h1 : m - hH.eigenvalues i ≠ 0 := by intro hcon; nlinarith [sub_eq_zero.mp hcon]
  have h2 : m + hH.eigenvalues i ≠ 0 := by
    intro hcon
    nlinarith [add_eq_zero_iff_eq_neg.mp hcon]
  field_simp
  ring

/-- **(HX.10), second form**: the cross block is `H(m²I - H²)⁻¹`. -/
theorem crossBlock_eq_window_quotient (hH : H.IsHermitian) {m : ℝ}
    (hm : ∀ i, |hH.eigenvalues i| < m) :
    crossBlock hH m = H * (((m ^ 2 : ℝ) : ℂ) • 1 - H * H)⁻¹ := by
  rw [inv_sq_window hH hm]
  have h := spectralFunction_mul hH id (fun l => (m ^ 2 - l ^ 2)⁻¹)
  rw [spectralFunction_id] at h
  rw [h]
  exact spectralFunction_congr hH fun i => div_eq_mul_inv _ _

/-- **(HX.10)**: the slab inverse in closed block form. -/
theorem slab_mul_inverse (hH : H.IsHermitian) {m : ℝ}
    (hm : ∀ i, |hH.eigenvalues i| < m) :
    slab H m * fromBlocks (diagBlock hH m) (crossBlock hH m)
        (crossBlock hH m) (diagBlock hH m) = 1 := by
  unfold slab diagBlock crossBlock
  rw [fromBlocks_multiply]
  have hid : ∀ g : ℝ → ℝ, (m : ℂ) • (1 : Matrix r r ℂ) * spectralFunction hH g
      = spectralFunction hH (fun l => m * g l) := by
    intro g
    rw [Matrix.smul_mul, Matrix.one_mul, ← spectralFunction_smul]
  have hHmul : ∀ g : ℝ → ℝ, H * spectralFunction hH g
      = spectralFunction hH (fun l => l * g l) := by
    intro g
    have h := spectralFunction_mul hH id g
    rw [spectralFunction_id] at h
    exact h
  have hdiagone : spectralFunction hH (fun l => m * (m / (m ^ 2 - l ^ 2)))
      + -H * spectralFunction hH (fun l => l / (m ^ 2 - l ^ 2)) = 1 := by
    rw [Matrix.neg_mul, hHmul, ← sub_eq_add_neg, ← spectralFunction_sub]
    calc spectralFunction hH
          (fun l => m * (m / (m ^ 2 - l ^ 2)) - l * (l / (m ^ 2 - l ^ 2)))
        = spectralFunction hH (fun _ => 1) := by
          refine spectralFunction_congr hH fun i => ?_
          have hw := (window_pos hH hm i).ne'
          field_simp
      _ = 1 := by rw [spectralFunction_const, Complex.ofReal_one, one_smul]
  have hcrosszero : spectralFunction hH (fun l => m * (l / (m ^ 2 - l ^ 2)))
      + -H * spectralFunction hH (fun l => m / (m ^ 2 - l ^ 2)) = 0 := by
    rw [Matrix.neg_mul, hHmul, ← sub_eq_add_neg, ← spectralFunction_sub]
    calc spectralFunction hH
          (fun l => m * (l / (m ^ 2 - l ^ 2)) - l * (m / (m ^ 2 - l ^ 2)))
        = spectralFunction hH (fun _ => 0) := by
          refine spectralFunction_congr hH fun i => ?_
          ring
      _ = 0 := by rw [spectralFunction_const, Complex.ofReal_zero, zero_smul]
  have h21 : -H * spectralFunction hH (fun l => m / (m ^ 2 - l ^ 2))
      + spectralFunction hH (fun l => m * (l / (m ^ 2 - l ^ 2))) = 0 := by
    rw [add_comm]
    exact hcrosszero
  have h22 : -H * spectralFunction hH (fun l => l / (m ^ 2 - l ^ 2))
      + spectralFunction hH (fun l => m * (m / (m ^ 2 - l ^ 2))) = 1 := by
    rw [add_comm]
    exact hdiagone
  rw [hid, hid, hdiagone, hcrosszero, h21, h22]
  exact fromBlocks_one

/-- **(HX.10)**: the direct cross block of the slab inverse is exactly
`P_{m,H}`. -/
theorem slab_inv_cross (hH : H.IsHermitian) {m : ℝ}
    (hm : ∀ i, |hH.eigenvalues i| < m) :
    (slab H m)⁻¹.toBlocks₁₂ = crossBlock hH m := by
  rw [Matrix.inv_eq_right_inv (slab_mul_inverse hH hm), Matrix.toBlocks_fromBlocks₁₂]

/-- The common eigenbasis action: `H eᵢ = λᵢ eᵢ` and
`P eᵢ = λᵢ/(m²-λᵢ²) eᵢ`. -/
theorem simultaneous_eigenbasis (hH : H.IsHermitian) (m : ℝ) (i : r) :
    H *ᵥ ⇑(hH.eigenvectorBasis i) = hH.eigenvalues i • ⇑(hH.eigenvectorBasis i) ∧
      crossBlock hH m *ᵥ ⇑(hH.eigenvectorBasis i)
        = ((hH.eigenvalues i / (m ^ 2 - hH.eigenvalues i ^ 2) : ℝ) : ℂ) •
            ⇑(hH.eigenvectorBasis i) :=
  ⟨hH.mulVec_eigenvectorBasis i, spectralFunction_mulVec_eigenvectorBasis hH _ i⟩

/-- **(HX.11), pointwise form**: the cross eigenvalues carry exactly the
signs of the `H` eigenvalues. -/
theorem inertia_signs (hH : H.IsHermitian) {m : ℝ}
    (hm : ∀ i, |hH.eigenvalues i| < m) (i : r) :
    (0 < hH.eigenvalues i / (m ^ 2 - hH.eigenvalues i ^ 2) ↔ 0 < hH.eigenvalues i) ∧
      (hH.eigenvalues i / (m ^ 2 - hH.eigenvalues i ^ 2) < 0 ↔ hH.eigenvalues i < 0) ∧
      (hH.eigenvalues i / (m ^ 2 - hH.eigenvalues i ^ 2) = 0 ↔ hH.eigenvalues i = 0) := by
  have hw := window_pos hH hm i
  refine ⟨⟨fun h => ?_, fun h => div_pos h hw⟩,
    ⟨fun h => ?_, fun h => div_neg_of_neg_of_pos h hw⟩,
    ⟨fun h => ?_, fun h => by rw [h, zero_div]⟩⟩
  · by_contra hcon
    push Not at hcon
    have : hH.eigenvalues i / (m ^ 2 - hH.eigenvalues i ^ 2) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hcon hw.le
    linarith
  · by_contra hcon
    push Not at hcon
    have : 0 ≤ hH.eigenvalues i / (m ^ 2 - hH.eigenvalues i ^ 2) := div_nonneg hcon hw.le
    linarith
  · rcases div_eq_zero_iff.mp h with h' | h'
    · exact h'
    · exact absurd h' hw.ne'

/-- **(HX.11), inertia counts**: `P` and `H` have identical positive,
negative, and zero inertia on the common eigenbasis. -/
theorem inertia_counts (hH : H.IsHermitian) {m : ℝ}
    (hm : ∀ i, |hH.eigenvalues i| < m) :
    (Finset.univ.filter fun i =>
        0 < hH.eigenvalues i / (m ^ 2 - hH.eigenvalues i ^ 2)).card
        = (Finset.univ.filter fun i => 0 < hH.eigenvalues i).card ∧
      (Finset.univ.filter fun i =>
        hH.eigenvalues i / (m ^ 2 - hH.eigenvalues i ^ 2) < 0).card
        = (Finset.univ.filter fun i => hH.eigenvalues i < 0).card ∧
      (Finset.univ.filter fun i =>
        hH.eigenvalues i / (m ^ 2 - hH.eigenvalues i ^ 2) = 0).card
        = (Finset.univ.filter fun i => hH.eigenvalues i = 0).card := by
  refine ⟨?_, ?_, ?_⟩ <;>
    · congr 1
      refine Finset.filter_congr fun i _ => ?_
      first
      | exact (inertia_signs hH hm i).1
      | exact (inertia_signs hH hm i).2.1
      | exact (inertia_signs hH hm i).2.2

/-- **(HX.11)**: `P_{m,H} ⪰ 0 ↔ H ⪰ 0`. -/
theorem crossBlock_posSemidef_iff (hH : H.IsHermitian) {m : ℝ}
    (hm : ∀ i, |hH.eigenvalues i| < m) :
    (crossBlock hH m).PosSemidef ↔ H.PosSemidef := by
  constructor
  · intro hP
    have heig : ∀ i, 0 ≤ hH.eigenvalues i := by
      intro i
      have hval := spectralFunction_mulVec_eigenvectorBasis hH
        (fun l => l / (m ^ 2 - l ^ 2)) i
      have hform := re_form_nonneg hP ⇑(hH.eigenvectorBasis i)
      rw [crossBlock] at hform
      rw [hval, dotProduct_smul, star_dot_self_eigenvectorBasis hH i, smul_eq_mul,
        Complex.ofReal_one, mul_one] at hform
      rw [Complex.ofReal_re] at hform
      by_contra hcon
      push Not at hcon
      have := ((inertia_signs hH hm i).2.1).mpr hcon
      linarith
    rw [← spectralFunction_id hH]
    exact spectralFunction_posSemidef hH id heig
  · intro hHpsd
    unfold crossBlock
    refine spectralFunction_posSemidef hH _ fun i => ?_
    exact div_nonneg (hHpsd.eigenvalues_nonneg i) (window_pos hH hm i).le

end CrossSign

end CrossSign

/-! ### `thm:SMOS-charge-flux-short` — Simultaneous charge–flux short

Rendering: the stacked whitened defect synthesis `Y_R : E_Q → 𝒦`, the
trivial-response synthesis `N_R` and the physical screening synthesis `Z_R`
are finite matrices on a common carrier.  Following the manuscript, the
screening range is orthogonalized after the trivial range:
`P_N = colProj N` and `P_Z = colProj ((1-P_N)Z)`.  QSF.6 is the orthogonal
three-way decomposition with all three summands PSD; QSF.7 is
`ℂ^{QΦ} = 0 ↔ Ran Y ⊆ Ran N + Ran Z` with the range inclusion rendered as
`Y = NU + ZV` (one simultaneous coefficient pair — the manuscript's
same-nuisance/same-screening discipline); the kernel and rank clauses
describe the polar range of the residual; QSF.8 lands the represented
charge row on Gauss flux plus screening modulo the retained improvement
class. -/

section ChargeFlux

namespace ChargeFlux

variable {k eQ en ez : Type*} [Fintype k] [Fintype eQ] [Fintype en] [Fintype ez]
  [DecidableEq k] [DecidableEq en] [DecidableEq ez]

/-- The orthogonalized screening synthesis `(1 - P_N) Z`. -/
noncomputable def screenRes (N : Matrix k en ℂ) (Z : Matrix k ez ℂ) : Matrix k ez ℂ :=
  ((1 : Matrix k k ℂ) - colProj N) * Z

/-- The trivial and screening projections have orthogonal ranges. -/
theorem proj_orthogonal (N : Matrix k en ℂ) (Z : Matrix k ez ℂ) :
    colProj N * colProj (screenRes N Z) = 0 ∧
      colProj (screenRes N Z) * colProj N = 0 := by
  have hNZ : colProj N * screenRes N Z = 0 := by
    unfold screenRes
    rw [← Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_one, colProj_idem, sub_self,
      Matrix.zero_mul]
  have h1 : colProj N * colProj (screenRes N Z) = 0 := mul_colProj_eq_zero hNZ
  refine ⟨h1, ?_⟩
  have h2 := congrArg conjTranspose h1
  rwa [conjTranspose_mul, (colProj_isHermitian N).eq,
    (colProj_isHermitian (screenRes N Z)).eq, conjTranspose_zero] at h2

/-- The joint defect projector `1 - P_N - P_Z` is Hermitian. -/
theorem joint_isHermitian (N : Matrix k en ℂ) (Z : Matrix k ez ℂ) :
    ((1 : Matrix k k ℂ) - colProj N - colProj (screenRes N Z)).IsHermitian := by
  change ((1 : Matrix k k ℂ) - colProj N - colProj (screenRes N Z))ᴴ = _
  rw [conjTranspose_sub, conjTranspose_sub, conjTranspose_one, (colProj_isHermitian N).eq,
    (colProj_isHermitian (screenRes N Z)).eq]

/-- The joint defect projector `1 - P_N - P_Z` is idempotent. -/
theorem joint_idem (N : Matrix k en ℂ) (Z : Matrix k ez ℂ) :
    ((1 : Matrix k k ℂ) - colProj N - colProj (screenRes N Z))
        * ((1 : Matrix k k ℂ) - colProj N - colProj (screenRes N Z))
      = (1 : Matrix k k ℂ) - colProj N - colProj (screenRes N Z) := by
  obtain ⟨h1, h2⟩ := proj_orthogonal N Z
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul,
    colProj_idem, h1, h2]
  abel

omit [Fintype eQ] in
/-- The residual Gram `ℂ^{QΦ} = Yᴴ(1 - P_N - P_Z)Y` in explicit Gram form. -/
theorem residual_gram (Y : Matrix k eQ ℂ) (N : Matrix k en ℂ) (Z : Matrix k ez ℂ) :
    Yᴴ * ((1 : Matrix k k ℂ) - colProj N - colProj (screenRes N Z)) * Y
      = (((1 : Matrix k k ℂ) - colProj N - colProj (screenRes N Z)) * Y)ᴴ
        * (((1 : Matrix k k ℂ) - colProj N - colProj (screenRes N Z)) * Y) := by
  calc Yᴴ * ((1 : Matrix k k ℂ) - colProj N - colProj (screenRes N Z)) * Y
      = Yᴴ * (((1 : Matrix k k ℂ) - colProj N - colProj (screenRes N Z))
          * ((1 : Matrix k k ℂ) - colProj N - colProj (screenRes N Z))) * Y := by
        rw [joint_idem]
    _ = (((1 : Matrix k k ℂ) - colProj N - colProj (screenRes N Z)) * Y)ᴴ
        * (((1 : Matrix k k ℂ) - colProj N - colProj (screenRes N Z)) * Y) := by
        rw [conjTranspose_mul, (joint_isHermitian N Z).eq]
        simp only [Matrix.mul_assoc]

/-- **(QSF.6)**: the complete defect Gram decomposes orthogonally into
trivial, screening, and missing charge/flux pieces, each PSD. -/
theorem defect_decomposition (Y : Matrix k eQ ℂ) (N : Matrix k en ℂ)
    (Z : Matrix k ez ℂ) :
    Yᴴ * Y
      = Yᴴ * colProj N * Y + Yᴴ * colProj (screenRes N Z) * Y
        + Yᴴ * ((1 : Matrix k k ℂ) - colProj N - colProj (screenRes N Z)) * Y ∧
      (Yᴴ * colProj N * Y).PosSemidef ∧
      (Yᴴ * colProj (screenRes N Z) * Y).PosSemidef ∧
      (Yᴴ * ((1 : Matrix k k ℂ) - colProj N - colProj (screenRes N Z)) * Y).PosSemidef := by
  refine ⟨?_, colProj_gram_posSemidef N Y, colProj_gram_posSemidef (screenRes N Z) Y, ?_⟩
  · simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
    abel
  · rw [residual_gram]
    exact posSemidef_conjTranspose_mul_self _

/-- The joint projector annihilates the trivial synthesis. -/
theorem joint_mul_triv (N : Matrix k en ℂ) (Z : Matrix k ez ℂ) :
    ((1 : Matrix k k ℂ) - colProj N - colProj (screenRes N Z)) * N = 0 := by
  have hZN : (screenRes N Z)ᴴ * N = 0 := by
    unfold screenRes
    rw [conjTranspose_mul, (one_sub_colProj_isHermitian N).eq, Matrix.mul_assoc,
      Matrix.sub_mul, Matrix.one_mul, colProj_mul_self, sub_self, Matrix.mul_zero]
  have hPZN : colProj (screenRes N Z) * N = 0 := by
    unfold colProj
    rw [Matrix.mul_assoc, Matrix.mul_assoc, hZN, Matrix.mul_zero, Matrix.mul_zero]
  rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, colProj_mul_self, hPZN, sub_self,
    sub_zero]

/-- The joint projector annihilates the screening synthesis. -/
theorem joint_mul_screen (N : Matrix k en ℂ) (Z : Matrix k ez ℂ) :
    ((1 : Matrix k k ℂ) - colProj N - colProj (screenRes N Z)) * Z = 0 := by
  have hPZZ : colProj (screenRes N Z) * Z = screenRes N Z := by
    have hZeq : colProj (screenRes N Z) * Z
        = colProj (screenRes N Z) * screenRes N Z
          + colProj (screenRes N Z) * (colProj N * Z) := by
      rw [← Matrix.mul_add]
      congr 1
      unfold screenRes
      rw [Matrix.sub_mul, Matrix.one_mul]
      abel
    rw [hZeq, colProj_mul_self, ← Matrix.mul_assoc, (proj_orthogonal N Z).2,
      Matrix.zero_mul, add_zero]
  rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, hPZZ]
  unfold screenRes
  rw [Matrix.sub_mul, Matrix.one_mul]
  abel

omit [Fintype eQ] in
/-- **(QSF.7)**: the missing charge/flux Gram vanishes exactly when the
defect range lands inside `Ran N + Ran Z` with one simultaneous
nuisance/screening coefficient pair. -/
theorem gauss_landing_iff (Y : Matrix k eQ ℂ) (N : Matrix k en ℂ) (Z : Matrix k ez ℂ) :
    Yᴴ * ((1 : Matrix k k ℂ) - colProj N - colProj (screenRes N Z)) * Y = 0 ↔
      ∃ (U : Matrix en eQ ℂ) (V : Matrix ez eQ ℂ), Y = N * U + Z * V := by
  constructor
  · intro h0
    rw [residual_gram, conjTranspose_mul_self_eq_zero] at h0
    have hsplit : Y = colProj N * Y + colProj (screenRes N Z) * Y := by
      have h1 : Y - colProj N * Y - colProj (screenRes N Z) * Y = 0 := by
        rw [← h0]
        simp only [Matrix.sub_mul, Matrix.one_mul]
      calc Y = Y - colProj N * Y - colProj (screenRes N Z) * Y
            + (colProj N * Y + colProj (screenRes N Z) * Y) := by abel
        _ = colProj N * Y + colProj (screenRes N Z) * Y := by rw [h1, zero_add]
    set g := pinv (posSemidef_conjTranspose_mul_self (screenRes N Z)).1
      * ((screenRes N Z)ᴴ * Y) with hg
    have hPZY : colProj (screenRes N Z) * Y = screenRes N Z * g := by
      rw [hg, colProj]
      simp only [Matrix.mul_assoc]
    have hZres : screenRes N Z * g
        = Z * g - N * (pinv (posSemidef_conjTranspose_mul_self N).1 * (Nᴴ * (Z * g))) := by
      unfold screenRes
      rw [Matrix.sub_mul, Matrix.one_mul, colProj]
      simp only [Matrix.sub_mul, Matrix.mul_assoc]
    have hPNY : colProj N * Y
        = N * (pinv (posSemidef_conjTranspose_mul_self N).1 * (Nᴴ * Y)) := by
      rw [colProj]
      simp only [Matrix.mul_assoc]
    refine ⟨pinv (posSemidef_conjTranspose_mul_self N).1 * (Nᴴ * Y)
      - pinv (posSemidef_conjTranspose_mul_self N).1 * (Nᴴ * (Z * g)), g, ?_⟩
    rw [Matrix.mul_sub]
    calc Y = colProj N * Y + colProj (screenRes N Z) * Y := hsplit
      _ = N * (pinv (posSemidef_conjTranspose_mul_self N).1 * (Nᴴ * Y))
          + (Z * g - N * (pinv (posSemidef_conjTranspose_mul_self N).1
            * (Nᴴ * (Z * g)))) := by rw [hPNY, hPZY, hZres]
      _ = N * (pinv (posSemidef_conjTranspose_mul_self N).1 * (Nᴴ * Y))
          - N * (pinv (posSemidef_conjTranspose_mul_self N).1 * (Nᴴ * (Z * g)))
          + Z * g := by abel
  · rintro ⟨U, V, rfl⟩
    have hkill : ((1 : Matrix k k ℂ) - colProj N - colProj (screenRes N Z))
        * (N * U + Z * V) = 0 := by
      rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, joint_mul_triv,
        joint_mul_screen, Matrix.zero_mul, Matrix.zero_mul, add_zero]
    rw [Matrix.mul_assoc, hkill, Matrix.mul_zero]

/-- The kernel of the residual Gram is exactly the preimage of
`Ran N + Ran Z` — the polar support of the missing direction. -/
theorem residual_kernel (Y : Matrix k eQ ℂ) (N : Matrix k en ℂ) (Z : Matrix k ez ℂ)
    (y : eQ → ℂ) :
    (Yᴴ * ((1 : Matrix k k ℂ) - colProj N - colProj (screenRes N Z)) * Y) *ᵥ y = 0 ↔
      (((1 : Matrix k k ℂ) - colProj N - colProj (screenRes N Z)) * Y) *ᵥ y = 0 := by
  constructor
  · intro h
    have hform : star ((((1 : Matrix k k ℂ) - colProj N - colProj (screenRes N Z)) * Y) *ᵥ y)
        ⬝ᵥ ((((1 : Matrix k k ℂ) - colProj N - colProj (screenRes N Z)) * Y) *ᵥ y) = 0 := by
      set M := ((1 : Matrix k k ℂ) - colProj N - colProj (screenRes N Z)) * Y with hMdef
      calc star (M *ᵥ y) ⬝ᵥ (M *ᵥ y)
          = star ((Mᴴ)ᴴ *ᵥ y) ⬝ᵥ (M *ᵥ y) := by rw [conjTranspose_conjTranspose]
        _ = star y ⬝ᵥ (Mᴴ *ᵥ (M *ᵥ y)) := (adjoint_dot Mᴴ y (M *ᵥ y)).symm
        _ = star y ⬝ᵥ ((Mᴴ * M) *ᵥ y) := by rw [mulVec_mulVec]
        _ = 0 := by rw [hMdef, ← residual_gram, h, dotProduct_zero]
    exact dotProduct_star_self_eq_zero.mp hform
  · intro h
    rw [residual_gram, ← mulVec_mulVec, h, mulVec_zero]

/-- The rank of the residual Gram is the number of missing charge/flux
directions. -/
theorem residual_rank (Y : Matrix k eQ ℂ) (N : Matrix k en ℂ) (Z : Matrix k ez ℂ) :
    (Yᴴ * ((1 : Matrix k k ℂ) - colProj N - colProj (screenRes N Z)) * Y).rank
      = (((1 : Matrix k k ℂ) - colProj N - colProj (screenRes N Z)) * Y).rank := by
  rw [residual_gram, Matrix.rank_conjTranspose_mul_self]

/-- **(QSF.8)**: on the branch with vanishing residual, the represented
charge row lands exactly on Gauss flux, Gauss source, and screening
modulo the retained trivial responses. -/
theorem charge_landing (Y : Matrix k eQ ℂ) (N : Matrix k en ℂ) (Z : Matrix k ez ℂ)
    (hC : Yᴴ * ((1 : Matrix k k ℂ) - colProj N - colProj (screenRes N Z)) * Y = 0)
    (qm phi gs scr : k → ℂ) (w : eQ → ℂ)
    (hrow : qm - phi - gs - scr = Y *ᵥ w) :
    ∃ (u : en → ℂ) (v : ez → ℂ), qm = phi + gs + scr + N *ᵥ u + Z *ᵥ v := by
  obtain ⟨U, V, hUV⟩ := (gauss_landing_iff Y N Z).mp hC
  refine ⟨U *ᵥ w, V *ᵥ w, ?_⟩
  have hq : qm = phi + gs + scr + Y *ᵥ w := by
    rw [← hrow]
    abel
  rw [hq, hUV, add_mulVec, mulVec_mulVec, mulVec_mulVec]
  abel

end ChargeFlux

end ChargeFlux

/-! ### `thm:SMST-Duhamel-Pythagoras` — Duhamel variance, absorption, birth

Rendering: the five-matrix packet of `def:SMST-Duhamel-five-matrix` is
generated from the action synthesis `A`, the Duhamel target `Y` and the
auxiliary primitive synthesis `F` on one finite fibre carrier:
`S = A*A`, `T = A*Y`, `U = Y*Y`, `P_A = AS†A*`, `N = (I-P_A)F`, `G = N*N`,
`C = N*Y`, exactly (DHI.10–DHI.11).  The joint projection `P_{(A,F)}` is
the column-range projection of the concatenated synthesis `(A,F)`, and the
identity `P_{(A,F)} = P_A + P_N` is proved, giving (DHI.13)–(DHI.15) with
the mutually exclusive trichotomy. -/

section DuhamelPyth

namespace DuhamelPyth

variable {k ea ee ef : Type*} [Fintype k] [Fintype ea] [Fintype ee] [Fintype ef]
  [DecidableEq k] [DecidableEq ea] [DecidableEq ef]

/-- The auxiliary primitive innovation `N = (I - P_A)F` (DHI.11). -/
noncomputable def auxN (A : Matrix k ea ℂ) (F : Matrix k ef ℂ) : Matrix k ef ℂ :=
  ((1 : Matrix k k ℂ) - colProj A) * F

/-- The Duhamel variance `𝕍 = U - T*S†T` (DHI.12). -/
noncomputable def variance (A : Matrix k ea ℂ) (Y : Matrix k ee ℂ) : Matrix ee ee ℂ :=
  Yᴴ * Y - (Aᴴ * Y)ᴴ * pinv (posSemidef_conjTranspose_mul_self A).1 * (Aᴴ * Y)

/-- The prior absorption `𝔸 = C*G†C` (DHI.12). -/
noncomputable def absorption (A : Matrix k ea ℂ) (F : Matrix k ef ℂ)
    (Y : Matrix k ee ℂ) : Matrix ee ee ℂ :=
  ((auxN A F)ᴴ * Y)ᴴ * pinv (posSemidef_conjTranspose_mul_self (auxN A F)).1
    * ((auxN A F)ᴴ * Y)

/-- The final Duhamel residual `ℝ_Duh = 𝕍 - 𝔸` (DHI.12). -/
noncomputable def residualDuh (A : Matrix k ea ℂ) (F : Matrix k ef ℂ)
    (Y : Matrix k ee ℂ) : Matrix ee ee ℂ :=
  variance A Y - absorption A F Y

omit [Fintype ee] in
/-- **(DHI.14a)**: `𝕍 = Y*(I - P_A)Y`. -/
theorem variance_eq (A : Matrix k ea ℂ) (Y : Matrix k ee ℂ) :
    variance A Y = Yᴴ * ((1 : Matrix k k ℂ) - colProj A) * Y :=
  schur_residual_eq A Y

omit [Fintype ee] in
/-- **(DHI.14b)**: `𝔸 = Y*P_N Y`. -/
theorem absorption_eq (A : Matrix k ea ℂ) (F : Matrix k ef ℂ) (Y : Matrix k ee ℂ) :
    absorption A F Y = Yᴴ * colProj (auxN A F) * Y := by
  unfold absorption colProj
  rw [conjTranspose_mul, conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]

/-- The joint range projection is the sum of the action and innovation
projections: `P_{(A,F)} = P_A + P_N`. -/
theorem joint_proj_eq (A : Matrix k ea ℂ) (F : Matrix k ef ℂ) :
    colProj (fromCols A F) = colProj A + colProj (auxN A F) := by
  set N := auxN A F with hN
  set P := colProj A + colProj N with hP
  set P' := colProj (fromCols A F) with hP'
  have hNA : Nᴴ * A = 0 := by
    rw [hN]
    unfold auxN
    rw [conjTranspose_mul, (one_sub_colProj_isHermitian A).eq, Matrix.mul_assoc,
      Matrix.sub_mul, Matrix.one_mul, colProj_mul_self, sub_self, Matrix.mul_zero]
  have hPNA : colProj N * A = 0 := by
    unfold colProj
    rw [Matrix.mul_assoc, Matrix.mul_assoc, hNA, Matrix.mul_zero, Matrix.mul_zero]
  have horth : colProj A * colProj N = 0 := by
    have hAN : colProj A * N = 0 := by
      rw [hN]
      unfold auxN
      rw [← Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_one, colProj_idem, sub_self,
        Matrix.zero_mul]
    exact mul_colProj_eq_zero hAN
  have hPA : P * A = A := by
    rw [hP, Matrix.add_mul, colProj_mul_self, hPNA, add_zero]
  have hPNF : colProj N * F = N := by
    have hsplit : F = N + colProj A * F := by
      rw [hN]
      unfold auxN
      rw [Matrix.sub_mul, Matrix.one_mul]
      abel
    conv_lhs => rw [hsplit]
    rw [Matrix.mul_add, colProj_mul_self]
    have : colProj N * (colProj A * F) = 0 := by
      rw [← Matrix.mul_assoc]
      have h2 := congrArg conjTranspose horth
      rw [conjTranspose_mul, (colProj_isHermitian A).eq, (colProj_isHermitian N).eq,
        conjTranspose_zero] at h2
      rw [h2, Matrix.zero_mul]
    rw [this, add_zero]
  have hPF : P * F = F := by
    rw [hP, Matrix.add_mul, hPNF]
    rw [hN]
    unfold auxN
    rw [Matrix.sub_mul, Matrix.one_mul]
    abel
  have hPB : P * fromCols A F = fromCols A F := by
    rw [Matrix.mul_fromCols, hPA, hPF]
  have hP'B : P' * A = A ∧ P' * F = F := by
    have h := colProj_mul_self (fromCols A F)
    rw [Matrix.mul_fromCols] at h
    exact (Matrix.fromCols_ext_iff _ _ _ _).mp h
  have hPP' : P * P' = P' := by
    rw [hP', colProj, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPB]
  have hP'P : P' * P = P := by
    have h1 : P' * colProj A = colProj A := by
      unfold colProj
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hP'B.1]
    have hP'N : P' * N = N := by
      calc P' * N = P' * F - P' * (colProj A * F) := by
            rw [hN]
            unfold auxN
            rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub]
        _ = F - colProj A * F := by rw [hP'B.2, ← Matrix.mul_assoc, h1]
        _ = N := by
            rw [hN]
            unfold auxN
            rw [Matrix.sub_mul, Matrix.one_mul]
    have h2 : P' * colProj N = colProj N := by
      unfold colProj
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hP'N]
    rw [hP, Matrix.mul_add, h1, h2]
  have hPh : P.IsHermitian := by
    rw [hP]
    change (colProj A + colProj N)ᴴ = _
    rw [conjTranspose_add, (colProj_isHermitian A).eq, (colProj_isHermitian N).eq]
  have h := congrArg conjTranspose hP'P
  rw [conjTranspose_mul, hPh.eq, (colProj_isHermitian (fromCols A F)).eq] at h
  exact hPP'.symm.trans h

omit [Fintype ee] in
/-- **(DHI.14c)**: `ℝ_Duh = Y*(I - P_{(A,F)})Y`. -/
theorem residual_eq (A : Matrix k ea ℂ) (F : Matrix k ef ℂ) (Y : Matrix k ee ℂ) :
    residualDuh A F Y = Yᴴ * ((1 : Matrix k k ℂ) - colProj (fromCols A F)) * Y := by
  unfold residualDuh
  rw [variance_eq, absorption_eq, joint_proj_eq]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_add, Matrix.add_mul]
  abel

/-- **(DHI.13)**: positivity of the variance, the absorption, and the
final residual, with the exact Pythagoras `𝕍 = 𝔸 + ℝ_Duh`. -/
theorem duhamel_pythagoras (A : Matrix k ea ℂ) (F : Matrix k ef ℂ) (Y : Matrix k ee ℂ) :
    (variance A Y).PosSemidef ∧ (absorption A F Y).PosSemidef ∧
      (residualDuh A F Y).PosSemidef ∧
      variance A Y = absorption A F Y + residualDuh A F Y := by
  refine ⟨?_, ?_, ?_, by unfold residualDuh; abel⟩
  · rw [variance_eq]
    exact one_sub_colProj_gram_posSemidef A Y
  · rw [absorption_eq]
    exact colProj_gram_posSemidef (auxN A F) Y
  · rw [residual_eq]
    exact one_sub_colProj_gram_posSemidef (fromCols A F) Y

omit [Fintype ee] in
/-- Right-clock reduction absorbs everything: a vanishing Duhamel variance
forces a vanishing final residual. -/
theorem residual_zero_of_variance_zero (A : Matrix k ea ℂ) (F : Matrix k ef ℂ)
    (Y : Matrix k ee ℂ) (hV : variance A Y = 0) : residualDuh A F Y = 0 := by
  have hM : ((1 : Matrix k k ℂ) - colProj A) * Y = 0 := by
    rw [variance_eq, one_sub_colProj_gram] at hV
    exact conjTranspose_mul_self_eq_zero.mp hV
  have hC : (auxN A F)ᴴ * Y = 0 := by
    unfold auxN
    rw [conjTranspose_mul, (one_sub_colProj_isHermitian A).eq, Matrix.mul_assoc, hM,
      Matrix.mul_zero]
  have hA0 : absorption A F Y = 0 := by
    unfold absorption
    rw [hC, conjTranspose_zero, Matrix.zero_mul, Matrix.zero_mul]
  unfold residualDuh
  rw [hV, hA0, sub_zero]

/-- **(DHI.15)**: every fibre lies in exactly one of the three branches
(right-clock reduction, prior-primitive absorption, unabsorbed dynamic
birth). -/
theorem branch_trichotomy (A : Matrix k ea ℂ) (F : Matrix k ef ℂ) (Y : Matrix k ee ℂ) :
    ((variance A Y = 0 ∧ residualDuh A F Y = 0) ∨
        (variance A Y ≠ 0 ∧ residualDuh A F Y = 0) ∨ residualDuh A F Y ≠ 0) ∧
      ¬(variance A Y = 0 ∧ residualDuh A F Y ≠ 0) := by
  constructor
  · by_cases hV : variance A Y = 0
    · exact Or.inl ⟨hV, residual_zero_of_variance_zero A F Y hV⟩
    · by_cases hR : residualDuh A F Y = 0
      · exact Or.inr (Or.inl ⟨hV, hR⟩)
      · exact Or.inr (Or.inr hR)
  · rintro ⟨hV, hR⟩
    exact hR (residual_zero_of_variance_zero A F Y hV)

end DuhamelPyth

end DuhamelPyth

/-! ### `thm:SMST-mixed-clock-packet` — Exact `3m+3` mixed-clock packet

Rendering: on one left-energy fibre, the right Hamiltonian `H = H^*` acts on
a finite carrier and its split semigroup `e^{sH}` is the spectral-calculus
exponential `semi`, identified with the power-series matrix exponential
(`semi_eq_exp`).  `Q_{λ,j} = e^{-(a-jh)λ}e^{-jhH}`, the trapezoid weights
`ω`, the packet banks `𝖢_j = B^*Q_jV`, `𝖪_n = V^*e^{-(2a-nh)λ}e^{-nhH}V`
and `γ_{m,n} = ∑_{i+j=n}ω_iω_j` are the manuscript's (DMC.4, DMC.8, DMC.9);
`B = (A,F)` is the concatenated prior primitive fibre.  The theorems give
the packet cardinality `3m+3`, the reconstruction identities (DMC.12), the
supported Schur residual (DMC.13), the endpoint-debit identity (DMC.14)
under the calibration `m·h = a`, and the five-matrix reconstruction
(DMC.15) via the `P_{(A,F)} = P_A + P_N` split of the Duhamel record. -/

section ClockPacket

namespace ClockPacket

variable {k ea ef ev : Type*} [Fintype k] [Fintype ea] [Fintype ef] [Fintype ev]
  [DecidableEq k] [DecidableEq ea] [DecidableEq ef] [DecidableEq ev]
  {H : Matrix k k ℂ}

/-- The split right semigroup `e^{sH}` by Hermitian spectral calculus. -/
noncomputable def semi (hH : H.IsHermitian) (s : ℝ) : Matrix k k ℂ :=
  spectralFunction hH (fun l => Real.exp (s * l))

/-- The semigroup law `e^{sH}e^{tH} = e^{(s+t)H}`. -/
theorem semi_mul (hH : H.IsHermitian) (s t : ℝ) :
    semi hH s * semi hH t = semi hH (s + t) := by
  unfold semi
  rw [spectralFunction_mul]
  refine spectralFunction_congr hH fun i => ?_
  rw [← Real.exp_add]
  ring_nf

/-- `e^{0·H} = 1`. -/
theorem semi_zero (hH : H.IsHermitian) : semi hH 0 = 1 := by
  unfold semi
  calc spectralFunction hH (fun l => Real.exp (0 * l))
      = spectralFunction hH (fun _ => 1) :=
        spectralFunction_congr hH fun i => by rw [zero_mul, Real.exp_zero]
    _ = 1 := by rw [spectralFunction_const, Complex.ofReal_one, one_smul]

/-- The split semigroup is PSD, hence Hermitian. -/
theorem semi_posSemidef (hH : H.IsHermitian) (s : ℝ) : (semi hH s).PosSemidef :=
  spectralFunction_posSemidef hH _ fun _ => (Real.exp_pos _).le

/-- The spectral semigroup is the power-series matrix exponential:
`semi s = exp(sH)`. -/
theorem semi_eq_exp (hH : H.IsHermitian) (s : ℝ) :
    semi hH s = NormedSpace.exp (s • H) := by
  set U := (hH.eigenvectorUnitary : Matrix k k ℂ) with hUdef
  have hUU' : U * Uᴴ = 1 :=
    mul_eq_one_comm.mp (UnitaryGroup.star_mul_self hH.eigenvectorUnitary)
  have hspec : H = U * diagonal (fun i => (hH.eigenvalues i : ℂ)) * Uᴴ := by
    have h := hH.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    exact h
  have hsmul : s • H = U * diagonal (fun i => ((s * hH.eigenvalues i : ℝ) : ℂ)) * Uᴴ := by
    conv_lhs => rw [hspec]
    rw [← Matrix.smul_mul, ← Matrix.mul_smul]
    congr 2
    funext i j
    by_cases hij : i = j
    · subst hij
      simp only [Matrix.smul_apply, Matrix.diagonal_apply_eq]
      rw [Complex.real_smul, Complex.ofReal_mul]
    · simp only [Matrix.smul_apply, Matrix.diagonal_apply_ne _ hij, smul_zero]
  have hUnit : IsUnit U :=
    (Matrix.isUnit_iff_isUnit_det U).mpr (Matrix.isUnit_det_of_right_inverse hUU')
  have hUinv : U⁻¹ = Uᴴ := Matrix.inv_eq_right_inv hUU'
  rw [hsmul, ← hUinv, Matrix.exp_conj _ _ hUnit, Matrix.exp_diagonal, hUinv]
  have hpi : NormedSpace.exp (fun i => ((s * hH.eigenvalues i : ℝ) : ℂ))
      = fun i => Complex.exp ((s * hH.eigenvalues i : ℝ) : ℂ) := by
    funext i
    exact (Pi.coe_exp _ i).trans (congrFun Complex.exp_eq_exp_ℂ _).symm
  rw [hpi]
  unfold semi spectralFunction
  rw [Unitary.conjStarAlgAut_apply]
  have hfun : (RCLike.ofReal ∘ fun i => (fun l => Real.exp (s * l)) (hH.eigenvalues i))
      = fun i => Complex.exp ((s * hH.eigenvalues i : ℝ) : ℂ) := by
    funext i
    exact Complex.ofReal_exp _
  rw [hfun, Matrix.star_eq_conjTranspose]

/-- The trapezoid weights `ω₀ = ω_m = 1/2`, `ω_j = 1` otherwise (DMC.3). -/
noncomputable def omega (m j : ℕ) : ℝ := if j = 0 ∨ j = m then 1 / 2 else 1

/-- The split-clock factor `Q_{λ,j} = e^{-(a-jh)λ} e^{-jhH}` (DMC.4). -/
noncomputable def clockQ (hH : H.IsHermitian) (lam a h : ℝ) (j : ℕ) : Matrix k k ℂ :=
  ((Real.exp (-((a - (j : ℝ) * h) * lam)) : ℝ) : ℂ) • semi hH (-((j : ℝ) * h))

/-- The finite quadrature target `Y^{(m)} = -h ∑ ω_j Q_j V` (DMC.4). -/
noncomputable def quadY (hH : H.IsHermitian) (lam a h : ℝ) (m : ℕ)
    (V : Matrix k ev ℂ) : Matrix k ev ℂ :=
  -∑ j ∈ Finset.range (m + 1), ((h * omega m j : ℝ) : ℂ) • (clockQ hH lam a h j * V)

/-- The mixed bank `𝖢_{λ,j} = B^*Q_{λ,j}V` (DMC.8). -/
noncomputable def bankC (hH : H.IsHermitian) (lam a h : ℝ) (A : Matrix k ea ℂ)
    (F : Matrix k ef ℂ) (V : Matrix k ev ℂ) (j : ℕ) : Matrix (ea ⊕ ef) ev ℂ :=
  (fromCols A F)ᴴ * (clockQ hH lam a h j * V)

/-- The kinetic bank `𝖪_{λ,n} = V^*e^{-(2a-nh)λ}e^{-nhH}V` (DMC.8). -/
noncomputable def bankK (hH : H.IsHermitian) (lam a h : ℝ) (V : Matrix k ev ℂ)
    (n : ℕ) : Matrix ev ev ℂ :=
  Vᴴ * (((Real.exp (-((2 * a - (n : ℝ) * h) * lam)) : ℝ) : ℂ) • semi hH (-((n : ℝ) * h))) * V

/-- The convolved trapezoid weights `γ_{m,n} = ∑_{i+j=n} ω_iω_j` (DMC.9). -/
noncomputable def gammaW (m n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
    if i + j = n then omega m i * omega m j else 0

/-- The reconstructed mixed moment `𝖳 = -h∑ω_j𝖢_j` (DMC.11). -/
noncomputable def packT (hH : H.IsHermitian) (lam a h : ℝ) (m : ℕ) (A : Matrix k ea ℂ)
    (F : Matrix k ef ℂ) (V : Matrix k ev ℂ) : Matrix (ea ⊕ ef) ev ℂ :=
  -∑ j ∈ Finset.range (m + 1), ((h * omega m j : ℝ) : ℂ) • bankC hH lam a h A F V j

/-- The reconstructed target Gram `𝖴 = h²∑γ_{m,n}𝖪_n` (DMC.11). -/
noncomputable def packU (hH : H.IsHermitian) (lam a h : ℝ) (m : ℕ)
    (V : Matrix k ev ℂ) : Matrix ev ev ℂ :=
  ∑ n ∈ Finset.range (2 * m + 1), ((h ^ 2 * gammaW m n : ℝ) : ℂ) • bankK hH lam a h V n

/-- **(DMC.10)**: the packet `(𝖲; (𝖢_j)_{j≤m}; (𝖪_n)_{n≤2m})` contains
exactly `3m+3` finite matrices. -/
theorem packet_card (m : ℕ) :
    Fintype.card (Unit ⊕ Fin (m + 1) ⊕ Fin (2 * m + 1)) = 3 * m + 3 := by
  simp only [Fintype.card_sum, Fintype.card_unit, Fintype.card_fin]
  omega

omit [Fintype ea] [Fintype ef] [Fintype ev] [DecidableEq ea] [DecidableEq ef]
  [DecidableEq ev] in
/-- **(DMC.12), first identity**: `𝖳 = B^*Y^{(m)}`. -/
theorem packT_eq (hH : H.IsHermitian) (lam a h : ℝ) (m : ℕ) (A : Matrix k ea ℂ)
    (F : Matrix k ef ℂ) (V : Matrix k ev ℂ) :
    packT hH lam a h m A F V = (fromCols A F)ᴴ * quadY hH lam a h m V := by
  unfold packT quadY bankC
  rw [Matrix.mul_neg, Matrix.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.mul_smul]

/-- The clock factors compose adjointly into the kinetic kernel:
`Q_i^*Q_j = e^{-(2a-(i+j)h)λ}e^{-(i+j)hH}`. -/
theorem clockQ_adjoint_mul (hH : H.IsHermitian) (lam a h : ℝ) (i j : ℕ) :
    (clockQ hH lam a h i)ᴴ * clockQ hH lam a h j
      = ((Real.exp (-((2 * a - ((i + j : ℕ) : ℝ) * h) * lam)) : ℝ) : ℂ)
        • semi hH (-(((i + j : ℕ) : ℝ) * h)) := by
  unfold clockQ
  rw [conjTranspose_smul, (semi_posSemidef hH _).1.eq, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, semi_mul]
  have hcoef : star ((Real.exp (-((a - (i : ℝ) * h) * lam)) : ℝ) : ℂ)
        * ((Real.exp (-((a - (j : ℝ) * h) * lam)) : ℝ) : ℂ)
      = ((Real.exp (-((2 * a - ((i + j : ℕ) : ℝ) * h) * lam)) : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, ← Real.exp_add]
    push_cast
    ring_nf
  have harg : -((i : ℝ) * h) + -((j : ℝ) * h) = -(((i + j : ℕ) : ℝ) * h) := by
    push_cast
    ring
  rw [hcoef, harg]

omit [Fintype ev] [DecidableEq ev] in
/-- Scalar regrouping of the double quadrature sum by total clock index. -/
theorem regroup_smul (m : ℕ) (c : ℕ → ℝ) (f : ℕ → Matrix ev ev ℂ) :
    ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
        ((c i * c j : ℝ) : ℂ) • f (i + j)
      = ∑ n ∈ Finset.range (2 * m + 1),
          ((∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
            if i + j = n then c i * c j else 0 : ℝ) : ℂ) • f n := by
  rw [eq_comm]
  calc ∑ n ∈ Finset.range (2 * m + 1),
        ((∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
          if i + j = n then c i * c j else 0 : ℝ) : ℂ) • f n
      = ∑ n ∈ Finset.range (2 * m + 1), ∑ i ∈ Finset.range (m + 1),
          ∑ j ∈ Finset.range (m + 1),
            if i + j = n then ((c i * c j : ℝ) : ℂ) • f n else 0 := by
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [Complex.ofReal_sum, Finset.sum_smul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Complex.ofReal_sum, Finset.sum_smul]
        refine Finset.sum_congr rfl fun j _ => ?_
        split_ifs
        · rfl
        · rw [Complex.ofReal_zero, zero_smul]
    _ = ∑ i ∈ Finset.range (m + 1), ∑ n ∈ Finset.range (2 * m + 1),
          ∑ j ∈ Finset.range (m + 1),
            if i + j = n then ((c i * c j : ℝ) : ℂ) • f n else 0 := Finset.sum_comm
    _ = ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
          ∑ n ∈ Finset.range (2 * m + 1),
            if i + j = n then ((c i * c j : ℝ) : ℂ) • f n else 0 :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
          ((c i * c j : ℝ) : ℂ) • f (i + j) := by
        refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
        rw [Finset.mem_range] at hi hj
        have hmem : i + j ∈ Finset.range (2 * m + 1) := Finset.mem_range.mpr (by omega)
        rw [Finset.sum_ite_eq, ite_eq_left hmem]

omit [Fintype ev] [DecidableEq ev] in
/-- **(DMC.12), second identity**: `𝖴 = (Y^{(m)})^*Y^{(m)}` by the
commuting-semigroup regrouping. -/
theorem packU_eq (hH : H.IsHermitian) (lam a h : ℝ) (m : ℕ) (V : Matrix k ev ℂ) :
    packU hH lam a h m V = (quadY hH lam a h m V)ᴴ * quadY hH lam a h m V := by
  have hterm : ∀ i j : ℕ,
      (((h * omega m i : ℝ) : ℂ) • (clockQ hH lam a h i * V))ᴴ
          * (((h * omega m j : ℝ) : ℂ) • (clockQ hH lam a h j * V))
        = (((h * omega m i) * (h * omega m j) : ℝ) : ℂ) • bankK hH lam a h V (i + j) := by
    intro i j
    rw [conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, ← Complex.ofReal_mul]
    congr 1
    unfold bankK
    rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (clockQ hH lam a h i)ᴴ,
      clockQ_adjoint_mul hH lam a h i j]
    simp only [Matrix.mul_assoc, Matrix.smul_mul, Matrix.mul_smul]
  calc packU hH lam a h m V
      = ∑ i ∈ Finset.range (m + 1), ∑ j ∈ Finset.range (m + 1),
          (((h * omega m i) * (h * omega m j) : ℝ) : ℂ) • bankK hH lam a h V (i + j) := by
        rw [regroup_smul m (fun j => h * omega m j) (bankK hH lam a h V)]
        unfold packU
        refine Finset.sum_congr rfl fun n _ => ?_
        congr 2
        unfold gammaW
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [mul_ite, mul_zero]
        split_ifs
        · ring
        · rfl
    _ = (quadY hH lam a h m V)ᴴ * quadY hH lam a h m V := by
        unfold quadY
        rw [conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg,
          conjTranspose_sum, Matrix.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Matrix.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        exact (hterm i j).symm

omit [DecidableEq ev] in
/-- **(DMC.13)**: the supported Schur residual of the packet is the
compressed Gram `(Y^{(m)})^*(I - P^B)Y^{(m)} ⪰ 0`. -/
theorem packet_residual (hH : H.IsHermitian) (lam a h : ℝ) (m : ℕ) (A : Matrix k ea ℂ)
    (F : Matrix k ef ℂ) (V : Matrix k ev ℂ) :
    packU hH lam a h m V
        - (packT hH lam a h m A F V)ᴴ
          * pinv (posSemidef_conjTranspose_mul_self (fromCols A F)).1
          * packT hH lam a h m A F V
      = (quadY hH lam a h m V)ᴴ
          * ((1 : Matrix k k ℂ) - colProj (fromCols A F)) * quadY hH lam a h m V ∧
      (packU hH lam a h m V
        - (packT hH lam a h m A F V)ᴴ
          * pinv (posSemidef_conjTranspose_mul_self (fromCols A F)).1
          * packT hH lam a h m A F V).PosSemidef := by
  have heq : packU hH lam a h m V
      - (packT hH lam a h m A F V)ᴴ
        * pinv (posSemidef_conjTranspose_mul_self (fromCols A F)).1
        * packT hH lam a h m A F V
      = (quadY hH lam a h m V)ᴴ
        * ((1 : Matrix k k ℂ) - colProj (fromCols A F)) * quadY hH lam a h m V := by
    rw [packT_eq, packU_eq]
    exact schur_residual_eq (fromCols A F) (quadY hH lam a h m V)
  refine ⟨heq, ?_⟩
  rw [heq]
  exact one_sub_colProj_gram_posSemidef (fromCols A F) (quadY hH lam a h m V)

/-- The endpoint debit `D_end = V^*(e^{-aH} - e^{-aλ})²V` (DMC.5). -/
noncomputable def endDebit (hH : H.IsHermitian) (lam a : ℝ) (V : Matrix k ev ℂ) :
    Matrix ev ev ℂ :=
  Vᴴ * ((semi hH (-a) - ((Real.exp (-(a * lam)) : ℝ) : ℂ) • 1)
    * (semi hH (-a) - ((Real.exp (-(a * lam)) : ℝ) : ℂ) • 1)) * V

omit [DecidableEq ev] in
/-- The endpoint debit is PSD. -/
theorem endDebit_posSemidef (hH : H.IsHermitian) (lam a : ℝ) (V : Matrix k ev ℂ) :
    (endDebit hH lam a V).PosSemidef := by
  set X := semi hH (-a) - ((Real.exp (-(a * lam)) : ℝ) : ℂ) • 1 with hX
  have hXh : Xᴴ = X := by
    rw [hX, conjTranspose_sub, (semi_posSemidef hH _).1.eq, conjTranspose_smul,
      conjTranspose_one, Complex.star_def, Complex.conj_ofReal]
  have hgram : endDebit hH lam a V = (X * V)ᴴ * (X * V) := by
    unfold endDebit
    rw [← hX, conjTranspose_mul, hXh]
    simp only [Matrix.mul_assoc]
  rw [hgram]
  exact posSemidef_conjTranspose_mul_self _

omit [Fintype ev] [DecidableEq ev] in
/-- **(DMC.14)**: under the clock calibration `m·h = a`, the endpoint debit
is already contained in the `𝖪` bank: `D_end = 𝖪_{2m} - 2𝖪_m + 𝖪_0`. -/
theorem endDebit_eq_bank (hH : H.IsHermitian) (lam a h : ℝ) (m : ℕ)
    (V : Matrix k ev ℂ) (hmh : (m : ℝ) * h = a) :
    endDebit hH lam a V
      = bankK hH lam a h V (2 * m) - (2 : ℂ) • bankK hH lam a h V m
        + bankK hH lam a h V 0 := by
  have h2m : ((2 * m : ℕ) : ℝ) * h = 2 * a := by
    push_cast
    linear_combination 2 * hmh
  have hb2m : bankK hH lam a h V (2 * m) = Vᴴ * semi hH (-(2 * a)) * V := by
    unfold bankK
    rw [show -((2 * a - ((2 * m : ℕ) : ℝ) * h) * lam) = -(0 * lam) by rw [h2m]; ring,
      show -(((2 * m : ℕ) : ℝ) * h) = -(2 * a) by rw [h2m]]
    norm_num
  have hbm : bankK hH lam a h V m
      = ((Real.exp (-(a * lam)) : ℝ) : ℂ) • (Vᴴ * semi hH (-a) * V) := by
    unfold bankK
    rw [show -((2 * a - (m : ℝ) * h) * lam) = -(a * lam) by rw [hmh]; ring,
      show -((m : ℝ) * h) = -a by rw [hmh]]
    simp only [Matrix.mul_smul, Matrix.smul_mul]
  have hb0 : bankK hH lam a h V 0
      = ((Real.exp (-(2 * a * lam)) : ℝ) : ℂ) • (Vᴴ * V) := by
    unfold bankK
    rw [show -((2 * a - ((0 : ℕ) : ℝ) * h) * lam) = -(2 * a * lam) by push_cast; ring,
      show -(((0 : ℕ) : ℝ) * h) = 0 by push_cast; ring, semi_zero]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
  have hXX : semi hH (-a) * semi hH (-a) = semi hH (-(2 * a)) := by
    rw [semi_mul]
    congr 1
    ring
  have hcc : ((Real.exp (-(a * lam)) : ℝ) : ℂ) * ((Real.exp (-(a * lam)) : ℝ) : ℂ)
      = ((Real.exp (-(2 * a * lam)) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    ring_nf
  have hsq : (semi hH (-a) - ((Real.exp (-(a * lam)) : ℝ) : ℂ) • 1)
      * (semi hH (-a) - ((Real.exp (-(a * lam)) : ℝ) : ℂ) • 1)
      = semi hH (-(2 * a))
        - ((Real.exp (-(a * lam)) : ℝ) : ℂ) • semi hH (-a)
        - ((Real.exp (-(a * lam)) : ℝ) : ℂ) • semi hH (-a)
        + ((Real.exp (-(2 * a * lam)) : ℝ) : ℂ) • (1 : Matrix k k ℂ) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_one, Matrix.one_mul, smul_sub, smul_smul, hXX, hcc]
    abel
  rw [hb2m, hbm, hb0]
  unfold endDebit
  rw [hsq]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, two_smul]
  abel

omit [Fintype ea] [Fintype ef] [DecidableEq k] [DecidableEq ea] [DecidableEq ef] in
/-- **(DMC.15), block decomposition**: `𝖲 = [[S, D], [D^*, E]]` with
`S = A^*A`, `D = A^*F`, `E = F^*F`. -/
theorem gram_block (A : Matrix k ea ℂ) (F : Matrix k ef ℂ) :
    (fromCols A F)ᴴ * fromCols A F
      = fromBlocks (Aᴴ * A) (Aᴴ * F) ((Aᴴ * F)ᴴ) (Fᴴ * F) := by
  rw [conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul_fromCols]
  congr 1
  rw [conjTranspose_mul, conjTranspose_conjTranspose]

omit [Fintype ea] [Fintype ef] [Fintype ev] [DecidableEq ea] [DecidableEq ef]
  [DecidableEq ev] in
/-- **(DMC.15), row decomposition**: `𝖳 = (T; T^F)` with `T = A^*Y^{(m)}`,
`T^F = F^*Y^{(m)}`. -/
theorem packT_block (hH : H.IsHermitian) (lam a h : ℝ) (m : ℕ) (A : Matrix k ea ℂ)
    (F : Matrix k ef ℂ) (V : Matrix k ev ℂ) :
    packT hH lam a h m A F V
      = fromRows (Aᴴ * quadY hH lam a h m V) (Fᴴ * quadY hH lam a h m V) := by
  rw [packT_eq, conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul]

omit [Fintype ef] [DecidableEq ef] in
/-- **(DMC.15), Schur reconstruction of `G`**: `N^*N = E - D^*S†D`. -/
theorem auxG_eq (A : Matrix k ea ℂ) (F : Matrix k ef ℂ) :
    (DuhamelPyth.auxN A F)ᴴ * DuhamelPyth.auxN A F
      = Fᴴ * F - (Aᴴ * F)ᴴ * pinv (posSemidef_conjTranspose_mul_self A).1 * (Aᴴ * F) := by
  calc (DuhamelPyth.auxN A F)ᴴ * DuhamelPyth.auxN A F
      = Fᴴ * ((1 : Matrix k k ℂ) - colProj A) * F := by
        unfold DuhamelPyth.auxN
        exact (one_sub_colProj_gram A F).symm
    _ = Fᴴ * F - (Aᴴ * F)ᴴ * pinv (posSemidef_conjTranspose_mul_self A).1 * (Aᴴ * F) :=
        (schur_residual_eq A F).symm

omit [Fintype ef] [Fintype ev] [DecidableEq ef] [DecidableEq ev] in
/-- **(DMC.15), Schur reconstruction of `C`**: `N^*Y^{(m)} = T^F - D^*S†T`. -/
theorem auxC_eq (A : Matrix k ea ℂ) (F : Matrix k ef ℂ) (Y : Matrix k ev ℂ) :
    (DuhamelPyth.auxN A F)ᴴ * Y
      = Fᴴ * Y - (Aᴴ * F)ᴴ * pinv (posSemidef_conjTranspose_mul_self A).1 * (Aᴴ * Y) := by
  unfold DuhamelPyth.auxN
  rw [conjTranspose_mul, (one_sub_colProj_isHermitian A).eq, Matrix.mul_sub,
    Matrix.mul_one, Matrix.sub_mul]
  congr 1
  rw [conjTranspose_mul, conjTranspose_conjTranspose, colProj]
  simp only [Matrix.mul_assoc]

omit [DecidableEq ev] in
/-- **(DMC.15), final identity**: the packet residual (DMC.13) is exactly
the inherited five-matrix residual `U - T^*S†T - C^*G†C`. -/
theorem five_matrix_residual (hH : H.IsHermitian) (lam a h : ℝ) (m : ℕ)
    (A : Matrix k ea ℂ) (F : Matrix k ef ℂ) (V : Matrix k ev ℂ) :
    packU hH lam a h m V
        - (packT hH lam a h m A F V)ᴴ
          * pinv (posSemidef_conjTranspose_mul_self (fromCols A F)).1
          * packT hH lam a h m A F V
      = (quadY hH lam a h m V)ᴴ * quadY hH lam a h m V
          - (Aᴴ * quadY hH lam a h m V)ᴴ
            * pinv (posSemidef_conjTranspose_mul_self A).1 * (Aᴴ * quadY hH lam a h m V)
          - ((DuhamelPyth.auxN A F)ᴴ * quadY hH lam a h m V)ᴴ
            * pinv (posSemidef_conjTranspose_mul_self (DuhamelPyth.auxN A F)).1
            * ((DuhamelPyth.auxN A F)ᴴ * quadY hH lam a h m V) := by
  rw [(packet_residual hH lam a h m A F V).1, ← DuhamelPyth.residual_eq]
  unfold DuhamelPyth.residualDuh DuhamelPyth.variance DuhamelPyth.absorption
  rfl

end ClockPacket

end ClockPacket

/-! ### `cth:SMST-three-record-incidence` — Multiplication writer ≠ tangent

Rendering: `Ω = {-1,0,1}` is `Fin 3` with record values `x = (-1,0,1)`;
`μ_t(x) ∝ e^{-tx}` is the exponential deformation (HIT.1), `s_t = √μ_t`,
`R_t = |s_t⟩⟨s_t|`, and with one full heat bath the single conditional
projection is `P_{1,t} = R_t` (conditioning on the empty complement), so
the kinetic Hamiltonian (HIT.2) is `𝖧_t = ρ(I-R_t) + c(I-R_t)`.  A
ground-line transport is any unitary `W` with `W^*R_tW = R_0` (the
manuscript's (HIT.5) solution is one; the compression is
connection-independent): an explicit Householder transport is constructed,
and under every such transport the centered compressed Hamiltonian is the
constant `(ρ+c)`-multiple of `Q_0`, hence the actual tangent and Gibbs-root
derivative vanish.  On the two-dimensional carrier `Ran Q₀` (explicit
orthonormal columns `J`), `W = QM_xQ` restricts to a traceless operator
with `‖W‖²_HS = 2/3`, and the artificial Gibbs tangent (HIT.12) applied to
it has `‖𝒯_{β,h}(W)‖²_HS = a²/3` with `a = β/2` — exactly `1/12` at
`β = 1` (HIT.17). -/

section ThreeRec

namespace ThreeRec

/-- The record values `x = (-1, 0, 1)` on `Ω = Fin 3`. -/
def xv : Fin 3 → ℝ := ![-1, 0, 1]

/-- The unnormalized deformation weight `e^{-tx}`. -/
noncomputable def zpart (t : ℝ) : ℝ := ∑ i, Real.exp (-(t * xv i))

/-- The deformed law `μ_t(x) = e^{-tx}/Z_t` (HIT.1). -/
noncomputable def mu (t : ℝ) (i : Fin 3) : ℝ := Real.exp (-(t * xv i)) / zpart t

/-- The half-density `s_t = √μ_t`. -/
noncomputable def sroot (t : ℝ) (i : Fin 3) : ℝ := Real.sqrt (mu t i)

/-- The complex half-density vector. -/
noncomputable def csroot (t : ℝ) : Fin 3 → ℂ := fun i => ((sroot t i : ℝ) : ℂ)

/-- The ground-line projection `R_t = |s_t⟩⟨s_t|`. -/
noncomputable def rmat (t : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  vecMulVec (csroot t) (csroot t)

/-- The one-bath kinetic Hamiltonian `𝖧_t = ρ(I-R_t) + c(I-P_{1,t})` with
`P_{1,t} = R_t` (HIT.2). -/
noncomputable def hham (rho cc t : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  ((rho : ℝ) : ℂ) • ((1 : Matrix (Fin 3) (Fin 3) ℂ) - rmat t)
    + ((cc : ℝ) : ℂ) • ((1 : Matrix (Fin 3) (Fin 3) ℂ) - rmat t)

/-- The partition weight is positive. -/
theorem zpart_pos (t : ℝ) : 0 < zpart t :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) ⟨0, Finset.mem_univ 0⟩

/-- The deformed law is a probability vector. -/
theorem mu_sum (t : ℝ) : ∑ i, mu t i = 1 := by
  unfold mu
  rw [← Finset.sum_div]
  change zpart t / zpart t = 1
  rw [div_self (zpart_pos t).ne']

/-- The law is nonnegative. -/
theorem mu_nonneg (t : ℝ) (i : Fin 3) : 0 ≤ mu t i :=
  div_nonneg (Real.exp_pos _).le (zpart_pos t).le

/-- The half-density squares back to the law. -/
theorem sq_sroot (t : ℝ) (i : Fin 3) : sroot t i * sroot t i = mu t i :=
  Real.mul_self_sqrt (mu_nonneg t i)

/-- The real half-density is a unit vector. -/
theorem sroot_sum_sq (t : ℝ) : ∑ i, sroot t i * sroot t i = 1 := by
  calc ∑ i, sroot t i * sroot t i = ∑ i, mu t i :=
        Finset.sum_congr rfl fun i _ => sq_sroot t i
    _ = 1 := mu_sum t

/-- The complex half-density is a unit vector. -/
theorem csroot_sum_sq (t : ℝ) : ∑ i, csroot t i * csroot t i = 1 := by
  unfold csroot
  calc ∑ i, ((sroot t i : ℝ) : ℂ) * ((sroot t i : ℝ) : ℂ)
      = ((∑ i, sroot t i * sroot t i : ℝ) : ℂ) := by
        rw [Complex.ofReal_sum]
        exact Finset.sum_congr rfl fun i _ => (Complex.ofReal_mul _ _).symm
    _ = 1 := by rw [sroot_sum_sq, Complex.ofReal_one]

/-- The ground-line projection is Hermitian. -/
theorem rmat_isHermitian (t : ℝ) : (rmat t).IsHermitian := by
  change (rmat t)ᴴ = rmat t
  ext i j
  rw [conjTranspose_apply]
  unfold rmat csroot
  rw [vecMulVec_apply, vecMulVec_apply, ← Complex.ofReal_mul, ← Complex.ofReal_mul,
    Complex.star_def, Complex.conj_ofReal]
  rw [mul_comm]

/-- The ground-line projection is idempotent. -/
theorem rmat_idem (t : ℝ) : rmat t * rmat t = rmat t := by
  ext i j
  unfold rmat
  rw [Matrix.mul_apply, vecMulVec_apply]
  calc ∑ l, vecMulVec (csroot t) (csroot t) i l * vecMulVec (csroot t) (csroot t) l j
      = ∑ l, csroot t i * csroot t j * (csroot t l * csroot t l) := by
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [vecMulVec_apply, vecMulVec_apply]
        ring
    _ = csroot t i * csroot t j * ∑ l, csroot t l * csroot t l := by
        rw [← Finset.mul_sum]
    _ = csroot t i * csroot t j := by rw [csroot_sum_sq, mul_one]

/-- The one-bath Hamiltonian is the single line `(ρ+c)(I - R_t)`. -/
theorem hham_line (rho cc t : ℝ) :
    hham rho cc t
      = ((rho + cc : ℝ) : ℂ) • ((1 : Matrix (Fin 3) (Fin 3) ℂ) - rmat t) := by
  unfold hham
  rw [← add_smul, Complex.ofReal_add]

/-- Left multiplication into a rank-one bra–ket. -/
theorem mul_vecMulVec (M : Matrix (Fin 3) (Fin 3) ℂ) (u v : Fin 3 → ℂ) :
    M * vecMulVec u v = vecMulVec (M *ᵥ u) v := by
  ext i j
  rw [Matrix.mul_apply, vecMulVec_apply, Matrix.mulVec, dotProduct, Finset.sum_mul]
  exact Finset.sum_congr rfl fun l _ => by rw [vecMulVec_apply]; ring

/-- Right multiplication out of a rank-one bra–ket. -/
theorem vecMulVec_mul (u v : Fin 3 → ℂ) (M : Matrix (Fin 3) (Fin 3) ℂ) :
    vecMulVec u v * M = vecMulVec u (Mᵀ *ᵥ v) := by
  ext i j
  rw [Matrix.mul_apply, vecMulVec_apply, Matrix.mulVec, dotProduct, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by
    rw [vecMulVec_apply, Matrix.transpose_apply]
    ring

/-- **Ground-line transport exists**: an explicit Householder unitary
carries `R_t` back to `R_0`. -/
theorem exists_transport (t : ℝ) :
    ∃ W : Matrix (Fin 3) (Fin 3) ℂ,
      Wᴴ * W = 1 ∧ W * Wᴴ = 1 ∧ Wᴴ * rmat t * W = rmat 0 := by
  by_cases hst : csroot t = csroot 0
  · refine ⟨1, by simp, by simp, ?_⟩
    rw [conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
    unfold rmat
    rw [hst]
  · -- Householder reflection through `s_t - s_0`
    set w : Fin 3 → ℝ := fun i => sroot t i - sroot 0 i with hw
    set nw : ℝ := ∑ i, w i * w i with hnw
    set d : ℝ := ∑ i, sroot 0 i * sroot t i with hd
    set cw : Fin 3 → ℂ := fun i => ((w i : ℝ) : ℂ) with hcw
    have hwsum : ∀ s' : ℝ, (∑ i, w i * sroot s' i)
        = ∑ i, sroot t i * sroot s' i - ∑ i, sroot 0 i * sroot s' i := by
      intro s'
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by rw [hw]; ring
    have hnw_eq : nw = 2 - 2 * d := by
      rw [hnw]
      have hexp : ∀ i, w i * w i
          = sroot t i * sroot t i - 2 * (sroot 0 i * sroot t i)
            + sroot 0 i * sroot 0 i := by
        intro i
        rw [hw]
        ring
      rw [Finset.sum_congr rfl fun i _ => hexp i]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        sroot_sum_sq, sroot_sum_sq, hd]
      ring
    have hnw_pos : 0 < nw := by
      obtain ⟨i0, hi0⟩ : ∃ i, w i ≠ 0 := by
        by_contra hcon
        push Not at hcon
        apply hst
        funext i
        have h1 := hcon i
        rw [hw] at h1
        have h2 : sroot t i = sroot 0 i := by
          have := sub_eq_zero.mp h1
          linarith [this]
        unfold csroot
        rw [h2]
      rw [hnw]
      exact Finset.sum_pos' (fun i _ => mul_self_nonneg (w i))
        ⟨i0, Finset.mem_univ i0, mul_self_pos.mpr hi0⟩
    have hd_lt : d < 1 := by
      have := hnw_eq
      linarith [hnw_pos, this]
    -- the reflection
    set W : Matrix (Fin 3) (Fin 3) ℂ :=
      1 - ((2 / nw : ℝ) : ℂ) • vecMulVec cw cw with hWdef
    have hcw_sum : ∑ l, cw l * cw l = ((nw : ℝ) : ℂ) := by
      rw [hnw, Complex.ofReal_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      simp only [hcw]
      push_cast
      ring
    have hP2 : vecMulVec cw cw * vecMulVec cw cw = ((nw : ℝ) : ℂ) • vecMulVec cw cw := by
      ext i j
      rw [Matrix.mul_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
      calc ∑ l, vecMulVec cw cw i l * vecMulVec cw cw l j
          = ∑ l, cw i * cw j * (cw l * cw l) := by
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [vecMulVec_apply, vecMulVec_apply]
            ring
        _ = cw i * cw j * ∑ l, cw l * cw l := by rw [← Finset.mul_sum]
        _ = ((nw : ℝ) : ℂ) * (cw i * cw j) := by rw [hcw_sum]; ring
    have hstar : ∀ l, star (cw l) = cw l := by
      intro l
      simp only [hcw, Complex.star_def, Complex.conj_ofReal]
    have hPherm : (vecMulVec cw cw)ᴴ = vecMulVec cw cw := by
      ext i j
      rw [conjTranspose_apply, vecMulVec_apply, vecMulVec_apply, star_mul', hstar, hstar]
      ring
    have hWherm : Wᴴ = W := by
      rw [hWdef, conjTranspose_sub, conjTranspose_one, conjTranspose_smul, hPherm,
        Complex.star_def, Complex.conj_ofReal]
    have hWW : W * W = 1 := by
      have hcoef : ((2 / nw : ℝ) : ℂ) + ((2 / nw : ℝ) : ℂ)
          - ((2 / nw : ℝ) : ℂ) * ((2 / nw : ℝ) : ℂ) * ((nw : ℝ) : ℂ) = 0 := by
        push_cast
        field_simp
        all_goals ring
      have hexp : W * W
          = 1 - (((2 / nw : ℝ) : ℂ) + ((2 / nw : ℝ) : ℂ)
              - ((2 / nw : ℝ) : ℂ) * ((2 / nw : ℝ) : ℂ) * ((nw : ℝ) : ℂ))
            • vecMulVec cw cw := by
        rw [hWdef]
        simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.one_mul,
          Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_sub, hP2, add_smul, sub_smul,
          mul_assoc]
        abel
      rw [hexp, hcoef, zero_smul, sub_zero]
    have hwdot : ∑ l, w l * sroot t l = 1 - d := by
      rw [hwsum t, sroot_sum_sq]
    have hPv : vecMulVec cw cw *ᵥ csroot t = ((1 - d : ℝ) : ℂ) • cw := by
      funext i
      rw [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
      calc ∑ l, vecMulVec cw cw i l * csroot t l
          = ∑ l, cw i * (cw l * csroot t l) := by
            refine Finset.sum_congr rfl fun l _ => ?_
            rw [vecMulVec_apply]
            ring
        _ = cw i * ∑ l, cw l * csroot t l := by rw [← Finset.mul_sum]
        _ = cw i * ((1 - d : ℝ) : ℂ) := by
            congr 1
            calc ∑ l, cw l * csroot t l
                = ((∑ l, w l * sroot t l : ℝ) : ℂ) := by
                  rw [Complex.ofReal_sum]
                  refine Finset.sum_congr rfl fun l _ => ?_
                  simp only [hcw]
                  unfold csroot
                  push_cast
                  ring
            _ = ((1 - d : ℝ) : ℂ) := by rw [hwdot]
        _ = ((1 - d : ℝ) : ℂ) * cw i := by ring
    have hWs : W *ᵥ csroot t = csroot 0 := by
      rw [hWdef, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, hPv, smul_smul]
      have hcoef2 : ((2 / nw : ℝ) : ℂ) * ((1 - d : ℝ) : ℂ) = 1 := by
        have hd1 : (2 - 2 * d : ℝ) ≠ 0 := by intro h; nlinarith [hd_lt]
        rw [hnw_eq, ← Complex.ofReal_mul,
          show (2 / (2 - 2 * d) * (1 - d) : ℝ) = 1 from by
            rw [div_mul_eq_mul_div, div_eq_one_iff_eq hd1]
            ring,
          Complex.ofReal_one]
      rw [hcoef2, one_smul]
      funext i
      rw [Pi.sub_apply]
      simp only [hcw, hw]
      unfold csroot
      push_cast
      ring
    have hPT : (vecMulVec cw cw)ᵀ = vecMulVec cw cw := by
      ext i j
      rw [Matrix.transpose_apply, vecMulVec_apply, vecMulVec_apply]
      ring
    have hWT : Wᵀ = W := by
      rw [hWdef, Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul, hPT]
    refine ⟨W, ?_, ?_, ?_⟩
    · rw [hWherm, hWW]
    · rw [hWherm, hWW]
    · rw [hWherm]
      unfold rmat
      rw [mul_vecMulVec, hWs, vecMulVec_mul, hWT, hWs]

/-- **The transported centered Hamiltonian is constant**: under every
ground-line transport the compression is `(ρ+c)Q₀` at every `t`. -/
theorem transported_constant (rho cc t : ℝ) (W : Matrix (Fin 3) (Fin 3) ℂ)
    (hW : Wᴴ * W = 1) (hWR : Wᴴ * rmat t * W = rmat 0) :
    ((1 : Matrix (Fin 3) (Fin 3) ℂ) - rmat 0) * (Wᴴ * hham rho cc t * W)
        * ((1 : Matrix (Fin 3) (Fin 3) ℂ) - rmat 0)
      = ((rho + cc : ℝ) : ℂ) • ((1 : Matrix (Fin 3) (Fin 3) ℂ) - rmat 0) := by
  have hcomp : Wᴴ * hham rho cc t * W
      = ((rho + cc : ℝ) : ℂ) • ((1 : Matrix (Fin 3) (Fin 3) ℂ) - rmat 0) := by
    rw [hham_line, Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, hW]
    congr 1
  have hQ : ((1 : Matrix (Fin 3) (Fin 3) ℂ) - rmat 0)
      * ((1 : Matrix (Fin 3) (Fin 3) ℂ) - rmat 0)
      = (1 : Matrix (Fin 3) (Fin 3) ℂ) - rmat 0 := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, rmat_idem]
    abel
  rw [hcomp, Matrix.mul_smul, Matrix.smul_mul, hQ, hQ]

/-- **The actual tangent and Gibbs-root derivative vanish**: along any
family of ground-line transports the compressed Hamiltonian has zero
derivative in every entry. -/
theorem transported_tangent_zero (rho cc : ℝ) (Wfam : ℝ → Matrix (Fin 3) (Fin 3) ℂ)
    (hW : ∀ t, (Wfam t)ᴴ * Wfam t = 1)
    (hWR : ∀ t, (Wfam t)ᴴ * rmat t * Wfam t = rmat 0) (i j : Fin 3) :
    HasDerivAt (fun t : ℝ =>
      (((1 : Matrix (Fin 3) (Fin 3) ℂ) - rmat 0) * ((Wfam t)ᴴ * hham rho cc t * Wfam t)
        * ((1 : Matrix (Fin 3) (Fin 3) ℂ) - rmat 0)) i j) 0 0 := by
  have hconst : (fun t : ℝ =>
      (((1 : Matrix (Fin 3) (Fin 3) ℂ) - rmat 0) * ((Wfam t)ᴴ * hham rho cc t * Wfam t)
        * ((1 : Matrix (Fin 3) (Fin 3) ℂ) - rmat 0)) i j)
      = fun _ : ℝ =>
        (((rho + cc : ℝ) : ℂ) • ((1 : Matrix (Fin 3) (Fin 3) ℂ) - rmat 0)) i j := by
    funext t
    rw [transported_constant rho cc t (Wfam t) (hW t) (hWR t)]
  rw [hconst]
  exact hasDerivAt_const _ _

/-! #### The two-dimensional centered carrier and the inserted writer -/

/-- Multiplication by the record values, `M_x`. -/
noncomputable def mx : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.diagonal (fun i => ((xv i : ℝ) : ℂ))

/-- `√2`. -/
noncomputable def r2 : ℝ := Real.sqrt 2

/-- `√3`. -/
noncomputable def r3 : ℝ := Real.sqrt 3

/-- `√6`. -/
noncomputable def r6 : ℝ := Real.sqrt 6

/-- `√2·√2 = 2`. -/
theorem r2_sq : r2 * r2 = 2 := Real.mul_self_sqrt (by norm_num)

/-- `√3·√3 = 3`. -/
theorem r3_sq : r3 * r3 = 3 := Real.mul_self_sqrt (by norm_num)

/-- `√6·√6 = 6`. -/
theorem r6_sq : r6 * r6 = 6 := Real.mul_self_sqrt (by norm_num)

/-- `√2 ≠ 0`. -/
theorem r2_ne : r2 ≠ 0 := by
  intro h
  have := r2_sq
  rw [h] at this
  norm_num at this

/-- `√3 ≠ 0`. -/
theorem r3_ne : r3 ≠ 0 := by
  intro h
  have := r3_sq
  rw [h] at this
  norm_num at this

/-- `√6 ≠ 0`. -/
theorem r6_ne : r6 ≠ 0 := by
  intro h
  have := r6_sq
  rw [h] at this
  norm_num at this

/-- `√2·√6 = 2√3`. -/
theorem r2_mul_r6 : r2 * r6 = 2 * r3 := by
  unfold r2 r3 r6
  rw [show (2 : ℝ) = Real.sqrt 4 from by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)],
    ← Real.sqrt_mul (by norm_num) 6, ← Real.sqrt_mul (by norm_num) 3]
  norm_num

/-- The uniform partition weight `Z₀ = 3`. -/
theorem zpart_zero : zpart 0 = 3 := by
  unfold zpart
  rw [Fin.sum_univ_three]
  norm_num

/-- The uniform law `μ₀ = 1/3`. -/
theorem mu_zero (i : Fin 3) : mu 0 i = 1 / 3 := by
  unfold mu
  rw [zpart_zero]
  norm_num

/-- The uniform half-density `s₀ = 1/√3`. -/
theorem sroot_zero (i : Fin 3) : sroot 0 i = r3⁻¹ := by
  unfold sroot
  rw [mu_zero, show (1 / 3 : ℝ) = 3⁻¹ by norm_num, Real.sqrt_inv]
  rfl

/-- The uniform ground line `R₀ = (1/3)𝟙𝟙^*`. -/
theorem rmat_zero : rmat 0 = Matrix.of fun _ _ => ((3⁻¹ : ℝ) : ℂ) := by
  ext i j
  unfold rmat csroot
  rw [vecMulVec_apply, sroot_zero, sroot_zero, ← Complex.ofReal_mul, Matrix.of_apply]
  congr 1
  rw [← mul_inv, r3_sq]

/-- The explicit orthonormal columns of the centered carrier `Ran Q₀`. -/
noncomputable def jmat : Matrix (Fin 3) (Fin 2) ℂ :=
  !![((r2⁻¹ : ℝ) : ℂ), ((r6⁻¹ : ℝ) : ℂ);
     0, ((-(2 * r6⁻¹) : ℝ) : ℂ);
     ((-r2⁻¹ : ℝ) : ℂ), ((r6⁻¹ : ℝ) : ℂ)]

/-- The inverted square-root products in `ℂ`. -/
theorem c2_inv : ((r2 : ℝ) : ℂ)⁻¹ * ((r2 : ℝ) : ℂ)⁻¹ = 2⁻¹ := by
  rw [← mul_inv, ← Complex.ofReal_mul, r2_sq]
  norm_num

/-- The inverted square-root products in `ℂ`. -/
theorem c6_inv : ((r6 : ℝ) : ℂ)⁻¹ * ((r6 : ℝ) : ℂ)⁻¹ = 6⁻¹ := by
  rw [← mul_inv, ← Complex.ofReal_mul, r6_sq]
  norm_num

/-- The inverted square-root products in `ℂ`. -/
theorem c3_inv : ((r3 : ℝ) : ℂ)⁻¹ * ((r3 : ℝ) : ℂ)⁻¹ = 3⁻¹ := by
  rw [← mul_inv, ← Complex.ofReal_mul, r3_sq]
  norm_num

/-- The mixed square-root product in `ℂ`. -/
theorem c26_inv : ((r2 : ℝ) : ℂ)⁻¹ * ((r6 : ℝ) : ℂ)⁻¹ = 2⁻¹ * ((r3 : ℝ) : ℂ)⁻¹ := by
  rw [← mul_inv, ← Complex.ofReal_mul, r2_mul_r6, Complex.ofReal_mul, mul_inv]
  norm_num

set_option linter.unusedSimpArgs false in
set_option linter.flexible false in -- shared entry simp closer across `fin_cases` branches
/-- The carrier columns are orthonormal: `J^*J = 1₂`. -/
theorem jmat_gram : jmatᴴ * jmat = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    · simp [jmat, Matrix.mul_apply, Fin.sum_univ_three, Complex.star_def,
        Complex.conj_ofReal, Matrix.one_apply, map_ofNat]
      all_goals
        first
        | ring1
        | linear_combination (2 : ℂ) * c2_inv
        | linear_combination (6 : ℂ) * c6_inv

set_option linter.unusedSimpArgs false in
set_option linter.flexible false in -- shared entry simp closer across `fin_cases` branches
/-- The carrier columns span exactly `Ran Q₀`: `JJ^* = 1 - R₀`. -/
theorem jmat_proj : jmat * jmatᴴ = 1 - rmat 0 := by
  rw [rmat_zero]
  ext a b
  fin_cases a <;> fin_cases b <;>
    · simp [jmat, Matrix.mul_apply, Fin.sum_univ_two, Complex.star_def,
        Complex.conj_ofReal, Matrix.one_apply, map_ofNat, Matrix.sub_apply]
      all_goals
        first
        | ring1
        | linear_combination c2_inv + c6_inv
        | linear_combination (-2 : ℂ) * c6_inv
        | linear_combination c6_inv - c2_inv
        | linear_combination (4 : ℂ) * c6_inv
        | linear_combination c2_inv - c6_inv
        | linear_combination (2 : ℂ) * c6_inv

/-- The compressed writer passes through the carrier:
`J^*(QM_xQ)J = J^*M_xJ`. -/
theorem compress_eq :
    jmatᴴ * (((1 : Matrix (Fin 3) (Fin 3) ℂ) - rmat 0) * mx
        * ((1 : Matrix (Fin 3) (Fin 3) ℂ) - rmat 0)) * jmat
      = jmatᴴ * mx * jmat := by
  rw [← jmat_proj]
  calc jmatᴴ * (jmat * jmatᴴ * mx * (jmat * jmatᴴ)) * jmat
      = jmatᴴ * jmat * (jmatᴴ * mx * jmat) * (jmatᴴ * jmat) := by
        simp only [Matrix.mul_assoc]
    _ = jmatᴴ * mx * jmat := by
        rw [jmat_gram, Matrix.one_mul, Matrix.mul_one]

set_option linter.unusedSimpArgs false in
set_option linter.flexible false in -- shared entry simp closer across `fin_cases` branches
/-- The restricted writer in closed form: `J^*M_xJ = -(1/√3)·σ_x`. -/
theorem writer_matrix :
    jmatᴴ * mx * jmat = ((-r3⁻¹ : ℝ) : ℂ) • !![(0 : ℂ), 1; 1, 0] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    · simp [jmat, mx, xv, Matrix.mul_apply, Fin.sum_univ_three, Complex.star_def,
        Complex.conj_ofReal, map_ofNat]
      all_goals
        first
        | ring1
        | linear_combination (-2 : ℂ) * c26_inv

set_option linter.unusedSimpArgs false in -- shared entry simp list across `fin_cases` branches
/-- The Pauli swap squares to the identity. -/
theorem swap_mul_swap :
    (!![(0 : ℂ), 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ) * !![(0 : ℂ), 1; 1, 0] = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

set_option linter.unusedSimpArgs false in -- shared entry simp list across `fin_cases` branches
/-- The Pauli swap is Hermitian. -/
theorem swap_conjTranspose :
    (!![(0 : ℂ), 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℂ)ᴴ = !![(0 : ℂ), 1; 1, 0] := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.conjTranspose_apply]

/-- The compression of the constant transported Hamiltonian to the carrier
is the constant `(ρ+c)I₂` — the manuscript's centered Hamiltonian. -/
theorem restricted_hamiltonian (rho cc : ℝ) :
    jmatᴴ * (((rho + cc : ℝ) : ℂ) • ((1 : Matrix (Fin 3) (Fin 3) ℂ) - rmat 0)) * jmat
      = ((rho + cc : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [Matrix.mul_smul, Matrix.smul_mul, ← jmat_proj]
  congr 1
  calc jmatᴴ * (jmat * jmatᴴ) * jmat
      = (jmatᴴ * jmat) * (jmatᴴ * jmat) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [jmat_gram, Matrix.one_mul]

/-- **The restricted writer is traceless** (HIT.17, first clause). -/
theorem writer_traceless :
    (jmatᴴ * (((1 : Matrix (Fin 3) (Fin 3) ℂ) - rmat 0) * mx
        * ((1 : Matrix (Fin 3) (Fin 3) ℂ) - rmat 0)) * jmat).trace = 0 := by
  rw [compress_eq, writer_matrix, trace_smul, Matrix.trace_fin_two]
  simp

/-- **The restricted writer has `‖W‖²_HS = 2/3`** (HIT.17, second clause). -/
theorem writer_hs_norm :
    ((jmatᴴ * (((1 : Matrix (Fin 3) (Fin 3) ℂ) - rmat 0) * mx
          * ((1 : Matrix (Fin 3) (Fin 3) ℂ) - rmat 0)) * jmat)ᴴ
        * (jmatᴴ * (((1 : Matrix (Fin 3) (Fin 3) ℂ) - rmat 0) * mx
          * ((1 : Matrix (Fin 3) (Fin 3) ℂ) - rmat 0)) * jmat)).trace
      = ((2 / 3 : ℝ) : ℂ) := by
  rw [compress_eq, writer_matrix, conjTranspose_smul, swap_conjTranspose, Matrix.smul_mul,
    Matrix.mul_smul, swap_mul_swap, smul_smul, trace_smul, trace_one, Fintype.card_fin,
    Complex.star_def, Complex.conj_ofReal, smul_eq_mul]
  push_cast
  linear_combination (2 : ℂ) * c3_inv

/-! #### The artificial Gibbs tangent `𝒯_{β,h}` on the constant carrier -/

/-- `exp(z·1) = e^z·1` for scalar matrices. -/
theorem exp_smul_one {n : Type*} [Fintype n] [DecidableEq n] (z : ℂ) :
    NormedSpace.exp (z • (1 : Matrix n n ℂ)) = Complex.exp z • (1 : Matrix n n ℂ) := by
  have h1 : z • (1 : Matrix n n ℂ) = Matrix.diagonal (fun _ => z) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij]
  rw [h1, Matrix.exp_diagonal]
  have h2 : NormedSpace.exp (fun _ : n => z) = fun _ : n => Complex.exp z := by
    funext i
    exact (Pi.coe_exp _ i).trans (congrFun Complex.exp_eq_exp_ℂ z).symm
  rw [h2]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp
  · simp [hij]

/-- The scalar Gibbs semigroup `e^{c·1₂}` of the constant carrier
Hamiltonian. -/
noncomputable def gibbsExp (c : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  NormedSpace.exp (((c : ℝ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))

/-- The Gibbs normalizer `Z_β = Tr e^{-βh}` (HIT.12). -/
noncomputable def gibbsZ (beta eps : ℝ) : ℂ := (gibbsExp (-(beta * eps))).trace

/-- The Gibbs state `ϱ_β = e^{-βh}/Z_β` (HIT.12). -/
noncomputable def gibbsRho (beta eps : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (gibbsZ beta eps)⁻¹ • gibbsExp (-(beta * eps))

/-- The artificial Gibbs tangent
`𝒯_{β,h}(X) = -Z^{-1/2}∫₀^{β/2} e^{-(β/2-t)h}(X - Tr(ϱX)I)e^{-th} dt`
(HIT.12) on the constant carrier `h = εI₂`. -/
noncomputable def duhamelT (beta eps : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun i j =>
    -((((Real.sqrt ((gibbsZ beta eps).re))⁻¹ : ℝ) : ℂ) *
      ∫ t in (0 : ℝ)..(beta / 2),
        (gibbsExp (-((beta / 2 - t) * eps))
          * (X - (gibbsRho beta eps * X).trace • (1 : Matrix (Fin 2) (Fin 2) ℂ))
          * gibbsExp (-(t * eps))) i j)

/-- The scalar Gibbs semigroup in closed form. -/
theorem gibbsExp_eq (c : ℝ) : gibbsExp c = ((Real.exp c : ℝ) : ℂ) • 1 := by
  unfold gibbsExp
  rw [exp_smul_one, Complex.ofReal_exp]

/-- The Gibbs normalizer in closed form. -/
theorem gibbsZ_eq (beta eps : ℝ) :
    gibbsZ beta eps = ((2 * Real.exp (-(beta * eps)) : ℝ) : ℂ) := by
  unfold gibbsZ
  rw [gibbsExp_eq, trace_smul, trace_one, Fintype.card_fin, smul_eq_mul]
  push_cast
  ring

/-- The real part of the Gibbs normalizer. -/
theorem gibbsZ_re (beta eps : ℝ) :
    (gibbsZ beta eps).re = 2 * Real.exp (-(beta * eps)) := by
  rw [gibbsZ_eq, Complex.ofReal_re]

/-- The Gibbs state of the constant carrier Hamiltonian is `I₂/2`. -/
theorem gibbsRho_eq (beta eps : ℝ) : gibbsRho beta eps = (2 : ℂ)⁻¹ • 1 := by
  unfold gibbsRho
  rw [gibbsZ_eq, gibbsExp_eq, smul_smul]
  congr 1
  have he : ((Real.exp (-(beta * eps)) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'
  rw [Complex.ofReal_mul, mul_inv, mul_assoc, inv_mul_cancel₀ he, mul_one]
  norm_num

/-- The Gibbs expectation of the writer. -/
theorem trace_rho_mul (beta eps : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    (gibbsRho beta eps * X).trace = (2 : ℂ)⁻¹ * X.trace := by
  rw [gibbsRho_eq, Matrix.smul_mul, Matrix.one_mul, trace_smul, smul_eq_mul]

/-- The full artificial-tangent coefficient
`-Z^{-1/2}·(β/2)·e^{-βε/2}`. -/
noncomputable def tangentCoef (beta eps : ℝ) : ℝ :=
  -((Real.sqrt (2 * Real.exp (-(beta * eps))))⁻¹ * (beta / 2)
    * Real.exp (-(beta / 2 * eps)))

/-- **The tangent collapse**: on the constant carrier the Duhamel integral
collapses to the centered scalar multiple `𝒯(X) = γ(X - (TrX/2)I)`. -/
theorem duhamelT_scalar (beta eps : ℝ) (X : Matrix (Fin 2) (Fin 2) ℂ) :
    duhamelT beta eps X
      = ((tangentCoef beta eps : ℝ) : ℂ)
        • (X - ((2 : ℂ)⁻¹ * X.trace) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
  have hint : ∀ t : ℝ, gibbsExp (-((beta / 2 - t) * eps))
        * (X - (gibbsRho beta eps * X).trace • (1 : Matrix (Fin 2) (Fin 2) ℂ))
        * gibbsExp (-(t * eps))
      = ((Real.exp (-(beta / 2 * eps)) : ℝ) : ℂ)
        • (X - ((2 : ℂ)⁻¹ * X.trace) • (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
    intro t
    simp only [gibbsExp_eq, trace_rho_mul, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, smul_smul]
    congr 1
    rw [← Complex.ofReal_mul, ← Real.exp_add,
      show -(t * eps) + -((beta / 2 - t) * eps) = -(beta / 2 * eps) from by ring]
  ext i j
  simp only [duhamelT, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  have hfun : (fun t : ℝ => (gibbsExp (-((beta / 2 - t) * eps))
      * (X - (gibbsRho beta eps * X).trace • (1 : Matrix (Fin 2) (Fin 2) ℂ))
      * gibbsExp (-(t * eps))) i j)
      = fun _ : ℝ => (((Real.exp (-(beta / 2 * eps)) : ℝ) : ℂ)
        • (X - ((2 : ℂ)⁻¹ * X.trace) • (1 : Matrix (Fin 2) (Fin 2) ℂ))) i j := by
    funext t
    rw [hint t]
  rw [hfun, intervalIntegral.integral_const, sub_zero, gibbsZ_re, Matrix.smul_apply,
    smul_eq_mul, Complex.real_smul]
  unfold tangentCoef
  push_cast
  ring

/-- **(HIT.17)**: the artificial Gibbs tangent of the restricted writer has
`‖𝒯_{β,h}(W)‖²_HS = a²/3` with `a = β/2` — the squared mismatch against the
vanishing actual tangent. -/
theorem gibbs_mismatch (beta eps : ℝ) :
    ((duhamelT beta eps (jmatᴴ * (((1 : Matrix (Fin 3) (Fin 3) ℂ) - rmat 0) * mx
          * ((1 : Matrix (Fin 3) (Fin 3) ℂ) - rmat 0)) * jmat))ᴴ
        * duhamelT beta eps (jmatᴴ * (((1 : Matrix (Fin 3) (Fin 3) ℂ) - rmat 0) * mx
          * ((1 : Matrix (Fin 3) (Fin 3) ℂ) - rmat 0)) * jmat)).trace
      = (((beta / 2) ^ 2 / 3 : ℝ) : ℂ) := by
  have hX := compress_eq.trans writer_matrix
  rw [hX, duhamelT_scalar]
  have htr : ((((-r3⁻¹ : ℝ) : ℂ) • !![(0 : ℂ), 1; 1, 0]).trace) = 0 := by
    rw [trace_smul, Matrix.trace_fin_two]
    simp
  rw [htr, mul_zero, zero_smul, sub_zero, smul_smul, ← Complex.ofReal_mul,
    conjTranspose_smul, swap_conjTranspose, Complex.star_def, Complex.conj_ofReal,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, swap_mul_swap, trace_smul, trace_one,
    Fintype.card_fin, smul_eq_mul]
  have hE : Real.exp (-(beta / 2 * eps)) * Real.exp (-(beta / 2 * eps))
      = Real.exp (-(beta * eps)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hs : Real.sqrt (2 * Real.exp (-(beta * eps)))
      * Real.sqrt (2 * Real.exp (-(beta * eps))) = 2 * Real.exp (-(beta * eps)) :=
    Real.mul_self_sqrt (by positivity)
  have e3 : (r3⁻¹ * r3⁻¹ : ℝ) = 3⁻¹ := by rw [← mul_inv, r3_sq]
  have hsinv : (Real.sqrt (2 * Real.exp (-(beta * eps))))⁻¹
      * (Real.sqrt (2 * Real.exp (-(beta * eps))))⁻¹
      = (2 * Real.exp (-(beta * eps)))⁻¹ := by
    rw [← mul_inv, hs]
  have hfinal : (tangentCoef beta eps * -r3⁻¹) * (tangentCoef beta eps * -r3⁻¹) * 2
      = (beta / 2) ^ 2 / 3 := by
    calc (tangentCoef beta eps * -r3⁻¹) * (tangentCoef beta eps * -r3⁻¹) * 2
        = ((Real.sqrt (2 * Real.exp (-(beta * eps))))⁻¹
            * (Real.sqrt (2 * Real.exp (-(beta * eps))))⁻¹)
          * (Real.exp (-(beta / 2 * eps)) * Real.exp (-(beta / 2 * eps)))
          * (r3⁻¹ * r3⁻¹) * ((beta / 2) * (beta / 2)) * 2 := by
          unfold tangentCoef
          ring
      _ = (2 * Real.exp (-(beta * eps)))⁻¹ * Real.exp (-(beta * eps)) * 3⁻¹
          * ((beta / 2) * (beta / 2)) * 2 := by rw [hsinv, hE, e3]
      _ = (beta / 2) ^ 2 / 3 := by
          have hEne := (Real.exp_pos (-(beta * eps))).ne'
          field_simp
  exact_mod_cast congrArg Complex.ofReal hfinal

/-- **At `β = 1` the squared mismatch is exactly `1/12`** (HIT.17). -/
theorem gibbs_mismatch_beta_one (eps : ℝ) :
    ((duhamelT 1 eps (jmatᴴ * (((1 : Matrix (Fin 3) (Fin 3) ℂ) - rmat 0) * mx
          * ((1 : Matrix (Fin 3) (Fin 3) ℂ) - rmat 0)) * jmat))ᴴ
        * duhamelT 1 eps (jmatᴴ * (((1 : Matrix (Fin 3) (Fin 3) ℂ) - rmat 0) * mx
          * ((1 : Matrix (Fin 3) (Fin 3) ℂ) - rmat 0)) * jmat)).trace
      = ((1 / 12 : ℝ) : ℂ) := by
  rw [gibbs_mismatch]
  norm_num

end ThreeRec

end ThreeRec

/-! ### `cth:RPESM-root-no-infrared-window` — No kinetic window from a root

Rendering: a periodic coarse torus is a finite additive group `C` of
currents (the concrete tori `(ℤ/Lℤ)^d` are instances, and a nonzero coarse
momentum is exhibited on every such torus with `d ≥ 1`, `L ≥ 2`); coarse
momenta `k` are the additive characters `ψ` of `C`, with `e^{-ik·c}`
realized as `ψ(c)`.  A positive translation-invariant Gaussian current law
is an actual `multivariateGaussian` probability measure with PSD
translation-invariant covariance, and the Fourier symbol is the
manuscript's (WB.27): `Ĉ(ψ) = N⁻¹·E|∑_c ψ(c) b_c|²`, with
`K̂(ψ) = q - 2Ĉ(ψ)`.  The first countermodel (`flatCov`) has `Ĉ(0) = q/2`
(the exact root identity `K̂(0) = 0`) and `Ĉ(ψ) = 0`, `K̂(ψ) = q` for every
nonzero mode (WB.29); the second (`modeCov`) additionally has `Ĉ(ψ⋆) = q`
and `K̂(ψ⋆) = -q` at one chosen nonzero mode. -/

section RootWindow

namespace RootWindow

open MeasureTheory ProbabilityTheory

variable {C : Type*} [AddCommGroup C] [Fintype C] [DecidableEq C]

/-- The Fourier current symbol `Ĉ(ψ) = N⁻¹ E|∑_c ψ(c) b_c|²` (WB.27). -/
noncomputable def currentSymbol (P : Measure (EuclideanSpace ℝ C))
    (ψ : AddChar C ℂ) : ℝ :=
  (Fintype.card C : ℝ)⁻¹ * ∫ b, Complex.normSq (∑ c, ψ c * ((b c : ℝ) : ℂ)) ∂P

/-- The kinetic symbol `K̂(ψ) = q - 2Ĉ(ψ)` (WB.27). -/
noncomputable def kineticSymbol (q : ℝ) (P : Measure (EuclideanSpace ℝ C))
    (ψ : AddChar C ℂ) : ℝ :=
  q - 2 * currentSymbol P ψ

/-- The flat (zero-mode only) covariance `q/(2N)` (first countermodel). -/
noncomputable def flatCov (q : ℝ) : Matrix C C ℝ :=
  Matrix.of fun _ _ => q / (2 * (Fintype.card C : ℝ))

/-- The conjugacy-corrected weight of the retuned mode. -/
noncomputable def modeWeight (q : ℝ) (ψs : AddChar C ℂ) : ℝ :=
  if ψs + ψs = 0 then q else 2 * q

/-- The mode-retuned covariance (second countermodel). -/
noncomputable def modeCov (q : ℝ) (ψs : AddChar C ℂ) : Matrix C C ℝ :=
  Matrix.of fun c c' => q / (2 * (Fintype.card C : ℝ))
    + modeWeight q ψs / (Fintype.card C : ℝ) * (ψs (c - c')).re

omit [DecidableEq C] in
/-- The carrier volume is positive. -/
theorem cardC_pos : (0 : ℝ) < (Fintype.card C : ℝ) := by
  have : Nonempty C := ⟨0⟩
  exact_mod_cast Fintype.card_pos

omit [DecidableEq C] in
/-- Characters split over differences: `ψ(c-c') = ψ(c)·conj ψ(c')`. -/
theorem char_sub (φ : AddChar C ℂ) (c c' : C) :
    φ (c - c') = φ c * (starRingEnd ℂ) (φ c') := by
  rw [sub_eq_add_neg, AddChar.map_add_eq_mul, AddChar.map_neg_eq_conj]

omit [DecidableEq C] in
/-- The full character sum on a nonzero mode vanishes. -/
theorem char_sum_ne (φ : AddChar C ℂ) (h : φ ≠ 0) : ∑ c, φ c = 0 :=
  AddChar.sum_eq_zero_iff_ne_zero.mpr h

omit [DecidableEq C] in
/-- The full character sum on the zero mode is the carrier volume. -/
theorem char_sum_zero : ∑ c, (0 : AddChar C ℂ) c = (Fintype.card C : ℂ) := by
  simp [AddChar.zero_apply]

omit [DecidableEq C] in
/-- The paired character sum factorizes through the full sums. -/
theorem char_pair_sum (φ : AddChar C ℂ) :
    ∑ c, ∑ c', φ c * (starRingEnd ℂ) (φ c')
      = (∑ c, φ c) * (starRingEnd ℂ) (∑ c', φ c') := by
  rw [map_sum, Finset.sum_mul_sum]

omit [AddCommGroup C] [DecidableEq C] in
/-- Constants pull out of the double carrier sum. -/
theorem double_sum_pull (k : ℝ) (F : C → C → ℝ) :
    ∑ c : C, ∑ c' : C, k * F c c' = k * ∑ c : C, ∑ c' : C, F c c' := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ => (Finset.mul_sum _ _ _).symm

omit [AddCommGroup C] [DecidableEq C] in
/-- The paired weighted sum factorizes through the full sums. -/
theorem weighted_pair_sum (g : C → ℂ) :
    ∑ c : C, ∑ c' : C, g c * (starRingEnd ℂ) (g c')
      = (∑ c : C, g c) * (starRingEnd ℂ) (∑ c' : C, g c') := by
  rw [map_sum, Finset.sum_mul_sum]

omit [DecidableEq C] in
/-- The paired real character sum takes only the values `N·N` and `0`. -/
theorem char_re_pair_sum (φ : AddChar C ℂ) [Decidable (φ = 0)] :
    ∑ c : C, ∑ c' : C, (φ c * (starRingEnd ℂ) (φ c')).re
      = if φ = 0 then (Fintype.card C : ℝ) * (Fintype.card C : ℝ) else 0 := by
  have h1 : ∀ c : C, ∑ c' : C, (φ c * (starRingEnd ℂ) (φ c')).re
      = (∑ c' : C, φ c * (starRingEnd ℂ) (φ c')).re :=
    fun c => (Complex.re_sum _ _).symm
  rw [Finset.sum_congr rfl fun c _ => h1 c, ← Complex.re_sum, weighted_pair_sum]
  by_cases hφ : φ = 0
  · subst hφ
    rw [char_sum_zero, ite_eq_left rfl, map_natCast]
    norm_cast
  · rw [char_sum_ne φ hφ, zero_mul, ite_eq_right hφ, Complex.zero_re]

omit [DecidableEq C] in
/-- The flat covariance is translation invariant. -/
theorem flatCov_shift (q : ℝ) (t c c' : C) :
    flatCov (C := C) q (c + t) (c' + t) = flatCov (C := C) q c c' := rfl

omit [DecidableEq C] in
/-- The mode covariance is translation invariant. -/
theorem modeCov_shift (q : ℝ) (ψs : AddChar C ℂ) (t c c' : C) :
    modeCov q ψs (c + t) (c' + t) = modeCov q ψs c c' := by
  unfold modeCov
  rw [Matrix.of_apply, Matrix.of_apply, add_sub_add_right_eq_sub]

omit [AddCommGroup C] [DecidableEq C] in
/-- The flat covariance is symmetric. -/
theorem flatCov_isHermitian (q : ℝ) : (flatCov (C := C) q).IsHermitian := by
  change (flatCov (C := C) q)ᴴ = flatCov (C := C) q
  ext i j
  rfl

omit [DecidableEq C] in
/-- The flat covariance is PSD. -/
theorem flatCov_posSemidef (q : ℝ) (hq : 0 ≤ q) : (flatCov (C := C) q).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (flatCov_isHermitian q) fun x => ?_
  have hdouble : star x ⬝ᵥ (flatCov (C := C) q *ᵥ x)
      = ∑ c, ∑ c', q / (2 * (Fintype.card C : ℝ)) * (x c * x c') := by
    rw [dotProduct]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c' _ => ?_
    simp only [flatCov, Matrix.of_apply, Pi.star_apply, star_trivial]
    ring
  have hss : ∑ c : C, ∑ c' : C, x c * x c' = (∑ c, x c) * (∑ c, x c) := by
    rw [Finset.sum_mul_sum]
  rw [hdouble, double_sum_pull, hss]
  have hN : (0 : ℝ) < (Fintype.card C : ℝ) := cardC_pos
  have hx := mul_self_nonneg (∑ c, x c)
  positivity

omit [DecidableEq C] in
/-- The mode covariance is symmetric. -/
theorem modeCov_isHermitian (q : ℝ) (ψs : AddChar C ℂ) :
    (modeCov (C := C) q ψs).IsHermitian := by
  change (modeCov (C := C) q ψs)ᴴ = modeCov (C := C) q ψs
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.of_apply, modeCov, star_trivial]
  congr 2
  rw [char_sub, char_sub, ← Complex.conj_re (ψs i * (starRingEnd ℂ) (ψs j)), map_mul,
    Complex.conj_conj, mul_comm]

omit [DecidableEq C] in
/-- The mode covariance is PSD. -/
theorem modeCov_posSemidef (q : ℝ) (hq : 0 ≤ q) (ψs : AddChar C ℂ) :
    (modeCov (C := C) q ψs).PosSemidef := by
  have hw : 0 ≤ modeWeight q ψs := by
    unfold modeWeight
    split_ifs
    · exact hq
    · linarith
  have hN : (0 : ℝ) < (Fintype.card C : ℝ) := cardC_pos
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (modeCov_isHermitian q ψs)
    fun x => ?_
  have hterm : ∀ c c', x c * x c' * (ψs (c - c')).re
      = ((ψs c * ((x c : ℝ) : ℂ))
          * (starRingEnd ℂ) (ψs c' * ((x c' : ℝ) : ℂ))).re := by
    intro c c'
    rw [char_sub]
    simp only [map_mul, Complex.conj_ofReal, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
    ring
  have hkey : ∑ c, ∑ c', x c * x c' * (ψs (c - c')).re
      = Complex.normSq (∑ c, ψs c * ((x c : ℝ) : ℂ)) := by
    calc ∑ c, ∑ c', x c * x c' * (ψs (c - c')).re
        = ∑ c, ∑ c', ((ψs c * ((x c : ℝ) : ℂ))
            * (starRingEnd ℂ) (ψs c' * ((x c' : ℝ) : ℂ))).re :=
          Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun c' _ => hterm c c'
      _ = ((∑ c, ψs c * ((x c : ℝ) : ℂ))
          * (starRingEnd ℂ) (∑ c', ψs c' * ((x c' : ℝ) : ℂ))).re := by
          rw [Finset.sum_congr rfl fun c (_ : c ∈ Finset.univ) => (Complex.re_sum _ _).symm,
            ← Complex.re_sum, weighted_pair_sum]
      _ = Complex.normSq (∑ c, ψs c * ((x c : ℝ) : ℂ)) := by
          rw [Complex.mul_conj, Complex.ofReal_re]
  have hdouble : star x ⬝ᵥ (modeCov (C := C) q ψs *ᵥ x)
      = ∑ c, ∑ c', (q / (2 * (Fintype.card C : ℝ)) * (x c * x c')
          + modeWeight q ψs / (Fintype.card C : ℝ)
            * (x c * x c' * (ψs (c - c')).re)) := by
    rw [dotProduct]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c' _ => ?_
    simp only [modeCov, Matrix.of_apply, Pi.star_apply, star_trivial]
    ring
  have hsq : ∑ c, ∑ c', q / (2 * (Fintype.card C : ℝ)) * (x c * x c')
      = q / (2 * (Fintype.card C : ℝ)) * ((∑ c, x c) * (∑ c, x c)) := by
    rw [double_sum_pull]
    congr 1
    rw [Finset.sum_mul_sum]
  rw [hdouble, Finset.sum_congr rfl fun c (_ : c ∈ Finset.univ) => Finset.sum_add_distrib,
    Finset.sum_add_distrib, hsq, double_sum_pull, hkey]
  have h1 := mul_self_nonneg (∑ c, x c)
  have h2 := Complex.normSq_nonneg (∑ c, ψs c * ((x c : ℝ) : ℂ))
  positivity

/-! #### Second moments of the multivariate Gaussian law -/

omit [AddCommGroup C] in
/-- Coordinate evaluations of the Gaussian current law are square
integrable. -/
theorem eval_memLp (S : Matrix C C ℝ) (c0 : C) :
    MemLp (fun b : EuclideanSpace ℝ C => b c0) 2
      (multivariateGaussian (0 : EuclideanSpace ℝ C) S) := by
  have h := ProbabilityTheory.IsGaussian.memLp_two_id
    (μ := multivariateGaussian (0 : EuclideanSpace ℝ C) S)
  have h2 := (EuclideanSpace.proj (𝕜 := ℝ) c0).comp_memLp' h
  simpa [Function.comp] using h2

omit [AddCommGroup C] in
/-- The Gaussian current law is centered coordinatewise. -/
theorem eval_mean (S : Matrix C C ℝ) (c0 : C) :
    ∫ b, b c0 ∂(multivariateGaussian (0 : EuclideanSpace ℝ C) S) = 0 := by
  have hint : Integrable (id : EuclideanSpace ℝ C → EuclideanSpace ℝ C)
      (multivariateGaussian (0 : EuclideanSpace ℝ C) S) :=
    ProbabilityTheory.IsGaussian.integrable_id
  have h := ContinuousLinearMap.integral_comp_comm (EuclideanSpace.proj (𝕜 := ℝ) c0) hint
  simp only [id_eq] at h
  rw [integral_id_multivariateGaussian] at h
  simpa using h

omit [AddCommGroup C] in
/-- **The covariance identification**: the second moments of the Gaussian
current law are exactly the covariance entries. -/
theorem eval_second_moment (S : Matrix C C ℝ) (hS : S.PosSemidef) (c c' : C) :
    ∫ b, b c * b c' ∂(multivariateGaussian (0 : EuclideanSpace ℝ C) S) = S c c' := by
  set P := multivariateGaussian (0 : EuclideanSpace ℝ C) S with hP
  have h1 := covariance_eval_multivariateGaussian (μ := (0 : EuclideanSpace ℝ C)) hS c c'
  have h2 := covariance_eq_sub (X := fun b : EuclideanSpace ℝ C => b c)
    (Y := fun b : EuclideanSpace ℝ C => b c') (μ := P)
    (eval_memLp S c) (eval_memLp S c')
  calc ∫ b, b c * b c' ∂P
      = ∫ b, ((fun b : EuclideanSpace ℝ C => b c) * fun b : EuclideanSpace ℝ C => b c') b
        ∂P := rfl
    _ = cov[fun b : EuclideanSpace ℝ C => b c, fun b : EuclideanSpace ℝ C => b c'; P]
        + (∫ b, b c ∂P) * (∫ b, b c' ∂P) := by
        rw [h2]
        ring
    _ = S c c' := by
        rw [hP, eval_mean, eval_mean, h1]
        ring

omit [AddCommGroup C] in
/-- Linear reads of the Gaussian current law are square integrable. -/
theorem linear_memLp (S : Matrix C C ℝ) (w : C → ℝ) :
    MemLp (fun b : EuclideanSpace ℝ C => ∑ c, w c * b c) 2
      (multivariateGaussian (0 : EuclideanSpace ℝ C) S) := by
  refine memLp_finsetSum Finset.univ fun c _ => ?_
  exact (eval_memLp S c).const_mul (w c)

omit [AddCommGroup C] in
/-- Second moments of linear reads. -/
theorem linear_second_moment (S : Matrix C C ℝ) (hS : S.PosSemidef) (w : C → ℝ) :
    ∫ b, (∑ c, w c * b c) * (∑ c, w c * b c)
        ∂(multivariateGaussian (0 : EuclideanSpace ℝ C) S)
      = ∑ c, ∑ c', w c * w c' * S c c' := by
  set P := multivariateGaussian (0 : EuclideanSpace ℝ C) S with hP
  have hint : ∀ c c' : C,
      Integrable (fun b : EuclideanSpace ℝ C => w c * w c' * (b c * b c')) P := by
    intro c c'
    exact ((eval_memLp S c).integrable_mul (eval_memLp S c')).const_mul _
  have hterm : ∀ b : EuclideanSpace ℝ C, (∑ c, w c * b c) * (∑ c, w c * b c)
      = ∑ c, ∑ c', w c * w c' * (b c * b c') := by
    intro b
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun c' _ => by ring
  simp only [hterm]
  rw [integral_finsetSum _ fun c _ => integrable_finsetSum _ fun c' _ => hint c c']
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [integral_finsetSum _ fun c' _ => hint c c']
  refine Finset.sum_congr rfl fun c' _ => ?_
  rw [MeasureTheory.integral_const_mul, eval_second_moment S hS c c']

/-- **The symbol via the covariance**: the WB.27 expectation of the
Gaussian current law is the Fourier symbol of its covariance kernel. -/
theorem currentSymbol_eq (S : Matrix C C ℝ) (hS : S.PosSemidef) (ψ : AddChar C ℂ) :
    currentSymbol (multivariateGaussian (0 : EuclideanSpace ℝ C) S) ψ
      = (Fintype.card C : ℝ)⁻¹
        * ∑ c, ∑ c', (ψ c * (starRingEnd ℂ) (ψ c')).re * S c c' := by
  set P := multivariateGaussian (0 : EuclideanSpace ℝ C) S with hP
  unfold currentSymbol
  congr 1
  have hexpand : ∀ b : EuclideanSpace ℝ C,
      Complex.normSq (∑ c, ψ c * ((b c : ℝ) : ℂ))
        = (∑ c, (ψ c).re * b c) * (∑ c, (ψ c).re * b c)
          + (∑ c, (ψ c).im * b c) * (∑ c, (ψ c).im * b c) := by
    intro b
    rw [Complex.normSq_apply, Complex.re_sum, Complex.im_sum]
    congr 2 <;>
      · refine Finset.sum_congr rfl fun c _ => ?_
        simp [Complex.mul_re, Complex.mul_im]
  calc ∫ b, Complex.normSq (∑ c, ψ c * ((b c : ℝ) : ℂ)) ∂P
      = ∫ b, ((∑ c, (ψ c).re * b c) * (∑ c, (ψ c).re * b c)
          + (∑ c, (ψ c).im * b c) * (∑ c, (ψ c).im * b c)) ∂P := by
        simp only [hexpand]
    _ = (∫ b, (∑ c, (ψ c).re * b c) * (∑ c, (ψ c).re * b c) ∂P)
        + ∫ b, (∑ c, (ψ c).im * b c) * (∑ c, (ψ c).im * b c) ∂P := by
        refine MeasureTheory.integral_add ?_ ?_
        · exact (linear_memLp S _).integrable_mul (linear_memLp S _)
        · exact (linear_memLp S _).integrable_mul (linear_memLp S _)
    _ = (∑ c, ∑ c', (ψ c).re * (ψ c').re * S c c')
        + ∑ c, ∑ c', (ψ c).im * (ψ c').im * S c c' := by
        rw [hP, linear_second_moment S hS, linear_second_moment S hS]
    _ = ∑ c, ∑ c', (ψ c * (starRingEnd ℂ) (ψ c')).re * S c c' := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun c' _ => ?_
        simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
        ring

/-! #### The two countermodel symbols -/

/-- The flat law satisfies the exact root identity `Ĉ(0) = q/2`. -/
theorem flat_symbol_zero (q : ℝ) (hq : 0 ≤ q) :
    currentSymbol (multivariateGaussian (0 : EuclideanSpace ℝ C) (flatCov q)) 0
      = q / 2 := by
  classical
  rw [currentSymbol_eq _ (flatCov_posSemidef q hq)]
  have hN : (0 : ℝ) < (Fintype.card C : ℝ) := cardC_pos
  have h1 : ∀ c c' : C,
      ((0 : AddChar C ℂ) c * (starRingEnd ℂ) ((0 : AddChar C ℂ) c')).re
        * flatCov (C := C) q c c'
      = q / (2 * (Fintype.card C : ℝ)) * (((0 : AddChar C ℂ) c
          * (starRingEnd ℂ) ((0 : AddChar C ℂ) c')).re) := by
    intro c c'
    simp only [flatCov, Matrix.of_apply]
    ring
  rw [Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun c' _ => h1 c c',
    double_sum_pull, char_re_pair_sum, ite_eq_left rfl]
  field_simp

/-- The flat law carries no nonzero mode: `Ĉ(ψ) = 0` for `ψ ≠ 0`. -/
theorem flat_symbol_ne (q : ℝ) (hq : 0 ≤ q) (ψ : AddChar C ℂ) (hψ : ψ ≠ 0) :
    currentSymbol (multivariateGaussian (0 : EuclideanSpace ℝ C) (flatCov q)) ψ = 0 := by
  classical
  rw [currentSymbol_eq _ (flatCov_posSemidef q hq)]
  have h1 : ∀ c c' : C, (ψ c * (starRingEnd ℂ) (ψ c')).re * flatCov (C := C) q c c'
      = q / (2 * (Fintype.card C : ℝ)) * ((ψ c * (starRingEnd ℂ) (ψ c')).re) := by
    intro c c'
    simp only [flatCov, Matrix.of_apply]
    ring
  rw [Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun c' _ => h1 c c',
    double_sum_pull, char_re_pair_sum, ite_eq_right hψ, mul_zero, mul_zero]

/-- The universal real-part product identity used to split the retuned
mode. -/
theorem re_mul_re (a b : ℂ) :
    a.re * b.re = ((a * b).re + (a * (starRingEnd ℂ) b).re) / 2 := by
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

open Classical in
/-- **The complete symbol of the retuned law**, over every mode. -/
theorem mode_symbol (q : ℝ) (hq : 0 ≤ q) (ψs ψ : AddChar C ℂ) :
    currentSymbol (multivariateGaussian (0 : EuclideanSpace ℝ C) (modeCov q ψs)) ψ
      = (if ψ = 0 then q / 2 else 0)
        + modeWeight q ψs / 2
          * ((if ψ + ψs = 0 then 1 else 0) + (if ψ = ψs then 1 else 0)) := by
  have hN : (0 : ℝ) < (Fintype.card C : ℝ) := cardC_pos
  rw [currentSymbol_eq _ (modeCov_posSemidef q hq ψs)]
  have hre : ∀ c c' : C, (ψ c * (starRingEnd ℂ) (ψ c')).re * (ψs (c - c')).re
      = (((ψ + ψs) c * (starRingEnd ℂ) ((ψ + ψs) c')).re
        + ((ψ - ψs) c * (starRingEnd ℂ) ((ψ - ψs) c')).re) / 2 := by
    intro c c'
    rw [char_sub, re_mul_re]
    have e1 : ψ c * (starRingEnd ℂ) (ψ c') * (ψs c * (starRingEnd ℂ) (ψs c'))
        = (ψ + ψs) c * (starRingEnd ℂ) ((ψ + ψs) c') := by
      rw [AddChar.add_apply, AddChar.add_apply]
      simp only [map_mul]
      ring
    have e2 : ψ c * (starRingEnd ℂ) (ψ c')
          * (starRingEnd ℂ) (ψs c * (starRingEnd ℂ) (ψs c'))
        = (ψ - ψs) c * (starRingEnd ℂ) ((ψ - ψs) c') := by
      rw [AddChar.sub_apply, AddChar.sub_apply, AddChar.map_neg_eq_conj,
        AddChar.map_neg_eq_conj]
      simp only [map_mul, Complex.conj_conj]
      ring
    rw [e1, e2]
  have hsplit : ∀ c c' : C,
      (ψ c * (starRingEnd ℂ) (ψ c')).re * modeCov (C := C) q ψs c c'
      = q / (2 * (Fintype.card C : ℝ)) * (ψ c * (starRingEnd ℂ) (ψ c')).re
        + modeWeight q ψs / (Fintype.card C : ℝ)
          * ((ψ c * (starRingEnd ℂ) (ψ c')).re * (ψs (c - c')).re) := by
    intro c c'
    simp only [modeCov, Matrix.of_apply]
    ring
  have hmode : ∑ c : C, ∑ c' : C, (ψ c * (starRingEnd ℂ) (ψ c')).re * (ψs (c - c')).re
      = ((if ψ + ψs = 0 then (Fintype.card C : ℝ) * (Fintype.card C : ℝ) else 0)
        + (if ψ - ψs = 0 then (Fintype.card C : ℝ) * (Fintype.card C : ℝ) else 0)) / 2 := by
    calc ∑ c : C, ∑ c' : C, (ψ c * (starRingEnd ℂ) (ψ c')).re * (ψs (c - c')).re
        = ∑ c : C, ∑ c' : C,
            ((((ψ + ψs) c * (starRingEnd ℂ) ((ψ + ψs) c')).re
              + ((ψ - ψs) c * (starRingEnd ℂ) ((ψ - ψs) c')).re) / 2) :=
          Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun c' _ => hre c c'
      _ = (∑ c : C, ∑ c' : C, (((ψ + ψs) c * (starRingEnd ℂ) ((ψ + ψs) c')).re
            + ((ψ - ψs) c * (starRingEnd ℂ) ((ψ - ψs) c')).re)) / 2 := by
          rw [eq_comm, Finset.sum_div]
          exact Finset.sum_congr rfl fun c _ => Finset.sum_div _ _ _
      _ = ((if ψ + ψs = 0 then (Fintype.card C : ℝ) * (Fintype.card C : ℝ) else 0)
          + (if ψ - ψs = 0 then (Fintype.card C : ℝ) * (Fintype.card C : ℝ) else 0)) / 2 := by
          rw [Finset.sum_congr rfl fun c (_ : c ∈ Finset.univ) => Finset.sum_add_distrib,
            Finset.sum_add_distrib, char_re_pair_sum, char_re_pair_sum]
  have hsum : ∑ c : C, ∑ c' : C,
      (ψ c * (starRingEnd ℂ) (ψ c')).re * modeCov (C := C) q ψs c c'
      = q / (2 * (Fintype.card C : ℝ))
          * (if ψ = 0 then (Fintype.card C : ℝ) * (Fintype.card C : ℝ) else 0)
        + modeWeight q ψs / (Fintype.card C : ℝ)
          * (((if ψ + ψs = 0 then (Fintype.card C : ℝ) * (Fintype.card C : ℝ) else 0)
            + (if ψ - ψs = 0 then (Fintype.card C : ℝ) * (Fintype.card C : ℝ) else 0))
            / 2) := by
    rw [Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun c' _ => hsplit c c',
      Finset.sum_congr rfl fun c (_ : c ∈ Finset.univ) => Finset.sum_add_distrib,
      Finset.sum_add_distrib, double_sum_pull, double_sum_pull, char_re_pair_sum, hmode]
  rw [hsum]
  have hite : (if ψ - ψs = 0 then (Fintype.card C : ℝ) * (Fintype.card C : ℝ) else 0)
      = if ψ = ψs then (Fintype.card C : ℝ) * (Fintype.card C : ℝ) else 0 := by
    by_cases h : ψ = ψs
    · simp [h]
    · have h' : ¬(ψ - ψs = 0) := fun hc => h (sub_eq_zero.mp hc)
      rw [ite_eq_right h', ite_eq_right h]
  rw [hite]
  split_ifs <;> field_simp
  all_goals ring

/-- The retuned law keeps the exact root identity: `Ĉ(0) = q/2`. -/
theorem mode_symbol_zero (q : ℝ) (hq : 0 ≤ q) (ψs : AddChar C ℂ) (hs : ψs ≠ 0) :
    currentSymbol (multivariateGaussian (0 : EuclideanSpace ℝ C) (modeCov q ψs)) 0
      = q / 2 := by
  classical
  rw [mode_symbol q hq ψs 0]
  have h1 : ¬((0 : AddChar C ℂ) + ψs = 0) := by
    rw [zero_add]
    exact hs
  have h2 : ¬((0 : AddChar C ℂ) = ψs) := fun h => hs h.symm
  rw [ite_eq_left rfl, ite_eq_right h1, ite_eq_right h2]
  ring

/-- The retuned law carries the mode: `Ĉ(ψ⋆) = q`. -/
theorem mode_symbol_at_mode (q : ℝ) (hq : 0 ≤ q) (ψs : AddChar C ℂ) (hs : ψs ≠ 0) :
    currentSymbol (multivariateGaussian (0 : EuclideanSpace ℝ C) (modeCov q ψs)) ψs
      = q := by
  classical
  rw [mode_symbol q hq ψs ψs, ite_eq_right hs, ite_eq_left rfl]
  unfold modeWeight
  by_cases h2 : ψs + ψs = 0
  · rw [ite_eq_left h2, ite_eq_left h2]
    ring
  · rw [ite_eq_right h2, ite_eq_right h2]
    ring

/-- **`cth:RPESM-root-no-infrared-window`, first countermodel (WB.29)**:
for every `q > 0` and every finite periodic carrier, the flat Gaussian
current law is a positive (PSD, translation-invariant) probability law
satisfying the exact root identity `Ĉ(0) = q/2`, `K̂(0) = 0`, with
`Ĉ(k) = 0` and `K̂(k) = q` on every nonzero mode: a global coherent soft
variable and no macroscopic kinetic field. -/
theorem root_no_infrared_window (q : ℝ) (hq : 0 < q) :
    (flatCov (C := C) q).PosSemidef ∧
      (∀ t c c' : C, flatCov (C := C) q (c + t) (c' + t) = flatCov (C := C) q c c') ∧
      IsProbabilityMeasure (multivariateGaussian (0 : EuclideanSpace ℝ C) (flatCov q)) ∧
      currentSymbol (multivariateGaussian (0 : EuclideanSpace ℝ C) (flatCov q)) 0
        = q / 2 ∧
      kineticSymbol q (multivariateGaussian (0 : EuclideanSpace ℝ C) (flatCov q)) 0 = 0 ∧
      (∀ ψ : AddChar C ℂ, ψ ≠ 0 →
        currentSymbol (multivariateGaussian (0 : EuclideanSpace ℝ C) (flatCov q)) ψ = 0) ∧
      ∀ ψ : AddChar C ℂ, ψ ≠ 0 →
        kineticSymbol q (multivariateGaussian (0 : EuclideanSpace ℝ C) (flatCov q)) ψ
          = q := by
  refine ⟨flatCov_posSemidef q hq.le, fun t c c' => flatCov_shift q t c c',
    inferInstance, flat_symbol_zero q hq.le, ?_, fun ψ hψ => flat_symbol_ne q hq.le ψ hψ,
    fun ψ hψ => ?_⟩
  · unfold kineticSymbol
    rw [flat_symbol_zero q hq.le]
    ring
  · unfold kineticSymbol
    rw [flat_symbol_ne q hq.le ψ hψ]
    ring

/-- **`cth:RPESM-root-no-infrared-window`, second countermodel**: retuning
one nonzero mode keeps the root identity but produces `Ĉ(k⋆) = q` and
`K̂(k⋆) = -q` — zero-mode retuning neither creates a kinetic window nor
excludes a modulated instability. -/
theorem mode_retuning_instability (q : ℝ) (hq : 0 < q) (ψs : AddChar C ℂ)
    (hs : ψs ≠ 0) :
    (modeCov (C := C) q ψs).PosSemidef ∧
      (∀ t c c' : C, modeCov (C := C) q ψs (c + t) (c' + t) = modeCov q ψs c c') ∧
      IsProbabilityMeasure
        (multivariateGaussian (0 : EuclideanSpace ℝ C) (modeCov q ψs)) ∧
      currentSymbol (multivariateGaussian (0 : EuclideanSpace ℝ C) (modeCov q ψs)) 0
        = q / 2 ∧
      currentSymbol (multivariateGaussian (0 : EuclideanSpace ℝ C) (modeCov q ψs)) ψs
        = q ∧
      kineticSymbol q (multivariateGaussian (0 : EuclideanSpace ℝ C) (modeCov q ψs)) ψs
        = -q := by
  refine ⟨modeCov_posSemidef q hq.le ψs, fun t c c' => modeCov_shift q ψs t c c',
    inferInstance, mode_symbol_zero q hq.le ψs hs, mode_symbol_at_mode q hq.le ψs hs, ?_⟩
  unfold kineticSymbol
  rw [mode_symbol_at_mode q hq.le ψs hs]
  ring

end RootWindow

/-- **Every genuine periodic coarse torus carries a nonzero mode**: on
`(ℤ/Lℤ)^d` with `d ≥ 1` and `L ≥ 2` there is a nontrivial coarse
momentum, so the second countermodel is realized on every such torus. -/
theorem RootWindow.torus_nontrivial_mode (d L : ℕ) (hd : 0 < d) (hL : 2 ≤ L) :
    ∃ ψ : AddChar (Fin d → ZMod L) ℂ, ψ ≠ 0 := by
  have hL0 : NeZero L := ⟨by omega⟩
  have hfact : Fact (1 < L) := ⟨by omega⟩
  have hζ := Complex.isPrimitiveRoot_exp L (by omega)
  have hζL : Complex.exp (2 * Real.pi * Complex.I / L) ^ L = 1 := hζ.pow_eq_one
  set ψ0 := AddChar.zmodChar L hζL with hψ0
  set i0 : Fin d := ⟨0, hd⟩ with hi0
  refine ⟨ψ0.compAddMonoidHom (Pi.evalAddMonoidHom (fun _ : Fin d => ZMod L) i0), ?_⟩
  rw [AddChar.ne_zero_iff]
  refine ⟨Pi.single i0 1, ?_⟩
  rw [AddChar.compAddMonoidHom_apply]
  have hf : Pi.evalAddMonoidHom (fun _ : Fin d => ZMod L) i0 (Pi.single i0 1)
      = (1 : ZMod L) := by
    simp [Pi.evalAddMonoidHom]
  rw [hf, hψ0, AddChar.zmodChar_apply, ZMod.val_one, pow_one]
  exact hζ.ne_one (by omega)

end RootWindow

end NCG

