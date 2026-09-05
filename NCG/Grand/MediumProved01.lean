/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import NCG.Grand.EasyExact01
import NCG.Grand.ClosedRangeMoorePenrose
import NCG.Upstream.SemigroupLimit

/-!
# Medium exact records, batch 01 (Gran-Tensor manuscript)

Exact formalizations of the following manuscript records:

* `cor:GT-Hodge-return-debit` — the Hodge-screen returning-memory compiler
  (ST.10): along a chain of determining quotients, each refined by a
  high-Hodge complement, the summed debit `D_n = D_n^old + κ_n⁻¹ X_n` is an
  admissible source debit whenever `C_high,n ⪰ κ_n I`,
  `L_high,n^* L_high,n ⪯ T_n^* X_n T_n` and `D_n^old` bounds the retained
  old/low form mismatch; summability of `‖D_n^old‖ + κ_n⁻¹‖X_n‖` below
  `λ_min(K_0)` preserves a uniform source reserve.
* `cth:GT-static-projectivity-no-clock` — the 2D Ornstein–Uhlenbeck
  counterexample (ET.21–ET.22): a projective static marginal with exact
  traced response `s_{a,b} = 2ab/(a+b)` and non-invariant fine semigroup.
* `thm:GT-source-renewal-lifetime` — the operator-valued renewal lifetime
  and exact mesh projectivity (LT.11–LT.18).
* `prop:GT-joint-tangent-stabilizer` — the joint-tangent route stabilizer
  (JT.1–JT.4) with the strictly finer marginal-stabilizer witness.
* `thm:GT-dynamic-source-ancestry` — the static-to-dynamic source short
  and cutoff transport (LT.26–LT.31).
* `thm:GT-temporal-Schur-dynamic-source` — the temporal Schur compiler and
  dual dynamic-birth certificate (DYN.1–DYN.6).
* `prop:GT-dynamic-source-transport-rectangle` — the primitive-orbit
  Duhamel identity and four-cutoff dynamic rectangle (DYN.7–DYN.10).
* `thm:GT-cofinal-dynamic-source` — cofinal dynamic-source landing under
  temporal exhaustion (DYN.11–DYN.12) with the minimal realization.
* `thm:GT-source-metric-horizon` — metric-covariant horizon control and
  invariant zero atom (SMET.14–SMET.19), including the Tikhonov compiler.
* `thm:GT-source-metric-depth` — coefficient-invariant source depth and
  the block-Jacobi chain (SMET.20–SMET.24).

Rendering conventions are described in the docstring of each section.
-/

open Matrix Finset
open NCG.SourceCoercivityInfluence NCG.GeometricThresholdBank NCG.PsdBlockSchur
open scoped ComplexOrder

-- decidability/fintype instances enter only through the spectral support calculus in proofs
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace NCG

/-! ### `cor:GT-Hodge-return-debit`

Rendering: after quotienting the exact nulls and promoting into the
determining head every low-Hodge direction whose coupling is not supported
by the old source analysis, each fine quotient `𝓗_{n+1}` splits
orthogonally into the retained head and the high-Hodge complement.  The
splitting is rendered by a pair of isometric inclusion syntheses
`J_n : 𝓗_n → 𝓗_{n+1}` (head) and `W_n : Y_n → 𝓗_{n+1}` (high-Hodge
complement) with `J_n J_n^* + W_n W_n^* = I`; the fine blocks are
`A₀₀ = J^* A_+ J`, `L = W^* A_+ J`, `C_high = W^* A_+ W`, the retraction
is `R_n = J_n^*`, and the transported source analysis satisfies
`T_{n+1} W_n = 0` (the complement is not supported by the source) and
`T_{n+1} J_n = U_n T_n` (ST.3).  We prove (ST.10): under
`C_high,n ⪰ κ_n I`, `L_n^* L_n ⪯ T_n^* X_n T_n` and the retained
old/low-mismatch bound `A₀₀ₙ ⪰ A_n - T_n^* D_n^old T_n`, the summed debit
`D_n = D_n^old + κ_n⁻¹ X_n` is admissible in the sense of (ST.4), and the
uniform reserve of `thm:GT-source-short-cutoff-transport` (ST.7) survives
with the manuscript constant
`λ_min(K₀) - ∑ₙ (‖D_n^old‖ + κ_n⁻¹‖X_n‖)`, with `λ_min`/`‖·‖` rendered as
the extreme eigenvalues `hermLamMin`/`hermLamMax` exactly as in the
ST.5–ST.9 layer of `EasyExact00`. -/

section HodgeReturnDebit

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A Loewner ceiling bounds `hermLamMax` from above. -/
theorem hermLamMax_le_of_loewner {n : Type*} [Fintype n] [DecidableEq n]
    [Nonempty n] {M : Matrix n n ℂ} (hM : M.IsHermitian) {c : ℝ}
    (h : ((c : ℂ) • 1 - M).PosSemidef) : hermLamMax hM ≤ c :=
  ciSup_le (eigenvalues_le_of_loewner hM h)

/-- `hermLamMax` depends only on the underlying matrix. -/
theorem hermLamMax_congr {n : Type*} [Fintype n] [DecidableEq n]
    {M N : Matrix n n ℂ}
    (h : M = N) (hM : M.IsHermitian) (hN : N.IsHermitian) :
    hermLamMax hM = hermLamMax hN := by
  subst h
  rfl

/-- A real nonnegative multiple of a PSD matrix is PSD. -/
theorem posSemidef_real_smul {n : Type*} [Fintype n] {X : Matrix n n ℂ}
    (hX : X.PosSemidef) {c : ℝ} (hc : 0 ≤ c) :
    ((c : ℂ) • X).PosSemidef := by
  refine posSemidef_of_re_form ?_ fun x => ?_
  · rw [Matrix.IsHermitian, conjTranspose_smul, hX.1.eq, Complex.star_def,
      Complex.conj_ofReal]
  · rw [smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul]
    exact mul_nonneg hc (re_form_nonneg hX x)

/-- A Hermitian matrix with a strictly positive Loewner floor is positive
definite. -/
theorem posDef_of_kappa_floor {y : Type*} [Fintype y] [DecidableEq y]
    {C : Matrix y y ℂ} (hCh : C.IsHermitian) {κ : ℝ} (hκ : 0 < κ)
    (hfloor : (C - (κ : ℂ) • 1).PosSemidef) : C.PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hCh fun x hx => ?_
  have h1 := re_form_nonneg hfloor x
  rw [sub_mulVec, dotProduct_sub, smul_mulVec, one_mulVec, dotProduct_smul] at h1
  simp only [Complex.sub_re, smul_eq_mul, Complex.re_ofReal_mul] at h1
  have h2 : (star x ⬝ᵥ x).re = ∑ i, ‖x i‖ ^ 2 := by
    rw [star_dot_self_eq_sum_sq, Complex.ofReal_re]
  have h3 : 0 < (star x ⬝ᵥ x).re := by
    rw [h2]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
    have hlt : (0 : ℝ) < ‖x i‖ ^ 2 := by positivity
    exact lt_of_lt_of_le hlt (Finset.single_le_sum
      (f := fun j => ‖x j‖ ^ 2) (fun j _ => by positivity) (mem_univ i))
  have h4 : 0 < (star x ⬝ᵥ (C *ᵥ x)).re := by nlinarith
  rw [hermitian_form_ofReal hCh x]
  exact_mod_cast h4

/-- Mixed transport of a sesquilinear pairing through two rectangular
syntheses. -/
theorem mixed_form_move {m k l : Type*} [Fintype m] [Fintype k] [Fintype l]
    (P : Matrix m k ℂ) (A : Matrix m m ℂ) (Q : Matrix m l ℂ)
    (x : k → ℂ) (y : l → ℂ) :
    star x ⬝ᵥ ((Pᴴ * A * Q) *ᵥ y) = star (P *ᵥ x) ⬝ᵥ (A *ᵥ (Q *ᵥ y)) := by
  rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, adjoint_dot,
    conjTranspose_conjTranspose, Matrix.mulVec_mulVec]

/-- Block expansion of a Hermitian fine form along an orthogonal
head/high-Hodge splitting `J J^* + W W^* = I`. -/
theorem split_form_eq_block {hsp hsp' y : Type*} [Fintype hsp] [Fintype hsp']
    [DecidableEq hsp'] [Fintype y] (Afine : Matrix hsp' hsp' ℂ)
    (hAfh : Afine.IsHermitian) (J : Matrix hsp' hsp ℂ) (W : Matrix hsp' y ℂ)
    (hcomp : J * Jᴴ + W * Wᴴ = 1) (u : hsp' → ℂ) :
    star u ⬝ᵥ (Afine *ᵥ u)
      = star (Sum.elim (Jᴴ *ᵥ u) (Wᴴ *ᵥ u)) ⬝ᵥ
          (fromBlocks (Jᴴ * Afine * J) ((Wᴴ * Afine * J)ᴴ)
            (Wᴴ * Afine * J) (Wᴴ * Afine * W)
            *ᵥ Sum.elim (Jᴴ *ᵥ u) (Wᴴ *ᵥ u)) := by
  have hLH : (Wᴴ * Afine * J)ᴴ = Jᴴ * Afine * W := by
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, hAfh.eq,
      Matrix.mul_assoc]
  have hLH' : (Jᴴ * Afine * W)ᴴ = Wᴴ * Afine * J := by
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, hAfh.eq,
      Matrix.mul_assoc]
  have hblocks : fromBlocks (Jᴴ * Afine * J) ((Wᴴ * Afine * J)ᴴ)
        (Wᴴ * Afine * J) (Wᴴ * Afine * W)
      = fromBlocks (Jᴴ * Afine * J) (Jᴴ * Afine * W)
        ((Jᴴ * Afine * W)ᴴ) (Wᴴ * Afine * W) := by
    rw [hLH, hLH']
  rw [hblocks, block_form (Jᴴ * Afine * J) (Jᴴ * Afine * W) (Wᴴ * Afine * W)
    (Jᴴ *ᵥ u) (Wᴴ *ᵥ u), hLH']
  rw [mixed_form_move J Afine J, mixed_form_move J Afine W,
    mixed_form_move W Afine J, mixed_form_move W Afine W]
  have hu : u = J *ᵥ (Jᴴ *ᵥ u) + W *ᵥ (Wᴴ *ᵥ u) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, hcomp,
      Matrix.one_mulVec]
  conv_lhs => rw [hu]
  rw [star_add, add_dotProduct, mulVec_add, dotProduct_add, dotProduct_add]
  ring

/-- **(ST.10, admissibility)** The Hodge-screen debit `D = D^old + κ⁻¹X` is
an admissible source debit: the packet debit inequality (ST.4) holds in
Loewner form for the head retraction `R = J^*` and the transported source
analysis, with the debit conjugated into the fine source frame by `U`. -/
theorem hodge_debit_admissible {hsp hsp' y : Type*} [Fintype hsp]
    [Fintype hsp'] [DecidableEq hsp'] [Fintype y] [DecidableEq y]
    (Afine : Matrix hsp' hsp' ℂ) (Acoarse : Matrix hsp hsp ℂ)
    (J : Matrix hsp' hsp ℂ) (W : Matrix hsp' y ℂ)
    (T : Matrix ι hsp ℂ) (Tfine : Matrix ι hsp' ℂ) (U : Matrix ι ι ℂ)
    (Dold X : Matrix ι ι ℂ) (κ : ℝ)
    (hAfh : Afine.IsHermitian) (hAc : Acoarse.PosDef)
    (hcomp : J * Jᴴ + W * Wᴴ = 1)
    (hTW : Tfine * W = 0) (hTJ : Tfine * J = U * T)
    (hUu : Uᴴ * U = 1) (hκ : 0 < κ)
    (hCfl : (Wᴴ * Afine * W - (κ : ℂ) • 1).PosSemidef)
    (hDold : Dold.PosSemidef) (hX : X.PosSemidef)
    (hL : (Tᴴ * X * T - (Wᴴ * Afine * J)ᴴ * (Wᴴ * Afine * J)).PosSemidef)
    (hold : (Jᴴ * Afine * J - (Acoarse - Tᴴ * Dold * T)).PosSemidef) :
    (Afine + Tfineᴴ * (U * (Dold + ((κ⁻¹ : ℝ) : ℂ) • X) * Uᴴ) * Tfine
      - J * Acoarse * Jᴴ).PosSemidef := by
  have hA00h : (Jᴴ * Afine * J).IsHermitian :=
    isHermitian_conjTranspose_mul_mul J hAfh
  have hCh : (Wᴴ * Afine * W).IsHermitian :=
    isHermitian_conjTranspose_mul_mul W hAfh
  have hCpd : (Wᴴ * Afine * W).PosDef := posDef_of_kappa_floor hCh hκ hCfl
  have hXinv : (((κ⁻¹ : ℝ) : ℂ) • X).PosSemidef :=
    posSemidef_real_smul hX (inv_nonneg.mpr hκ.le)
  have hD0psd : (Dold + ((κ⁻¹ : ℝ) : ℂ) • X).PosSemidef := hDold.add hXinv
  -- the two Feshbach sufficiency clauses
  have h2 := feshbach_kappa_debit (Wᴴ * Afine * J) T hCpd hκ hCfl hX.1 hL
  have hpoint := feshbach_debit_admissible (Jᴴ * Afine * J) (Wᴴ * Afine * J)
    T hA00h hCpd hAc hDold hXinv hold h2
  -- the transported source analysis in matrix form
  have hTfine_eq : Tfine = U * T * Jᴴ := by
    calc Tfine = Tfine * (J * Jᴴ) + Tfine * (W * Wᴴ) := by
          rw [← Matrix.mul_add, hcomp, Matrix.mul_one]
      _ = U * T * Jᴴ + 0 := by
          rw [← Matrix.mul_assoc, hTJ, ← Matrix.mul_assoc, hTW,
            Matrix.zero_mul]
      _ = U * T * Jᴴ := add_zero _
  -- the conjugated debit form in the coarse source frame
  have hmat : Tfineᴴ * (U * (Dold + ((κ⁻¹ : ℝ) : ℂ) • X) * Uᴴ) * Tfine
      = (T * Jᴴ)ᴴ * (Dold + ((κ⁻¹ : ℝ) : ℂ) • X) * (T * Jᴴ) := by
    rw [hTfine_eq]
    simp only [conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᴴ U, hUu, Matrix.one_mul,
      ← Matrix.mul_assoc Uᴴ U, hUu, Matrix.one_mul]
  -- assemble the Loewner packet form
  have hDpackh : (U * (Dold + ((κ⁻¹ : ℝ) : ℂ) • X) * Uᴴ).IsHermitian :=
    isHermitian_mul_mul_conjTranspose U hD0psd.1
  refine posSemidef_of_re_form ?_ fun u => ?_
  · exact (hAfh.add (isHermitian_conjTranspose_mul_mul Tfine hDpackh)).sub
      (isHermitian_mul_mul_conjTranspose J hAc.1)
  · have hpt := hpoint (Jᴴ *ᵥ u) (Wᴴ *ᵥ u)
    -- fine form as block form
    have hfine := split_form_eq_block Afine hAfh J W hcomp u
    -- the conjugated debit form equals the coarse-frame debit form
    have hdebit_eq : star u ⬝ᵥ ((Tfineᴴ
          * (U * (Dold + ((κ⁻¹ : ℝ) : ℂ) • X) * Uᴴ) * Tfine) *ᵥ u)
        = star (T *ᵥ (Jᴴ *ᵥ u)) ⬝ᵥ ((Dold + ((κ⁻¹ : ℝ) : ℂ) • X)
          *ᵥ (T *ᵥ (Jᴴ *ᵥ u))) := by
      rw [hmat, conj_form_move (T * Jᴴ) (Dold + ((κ⁻¹ : ℝ) : ℂ) • X) u,
        ← Matrix.mulVec_mulVec]
    -- the retracted coarse form
    have hcoarse_eq : star u ⬝ᵥ ((J * Acoarse * Jᴴ) *ᵥ u)
        = star (Jᴴ *ᵥ u) ⬝ᵥ (Acoarse *ᵥ (Jᴴ *ᵥ u)) := by
      have h := mixed_form_move Jᴴ Acoarse Jᴴ u u
      rw [conjTranspose_conjTranspose] at h
      rw [h]
    rw [sub_mulVec, add_mulVec, dotProduct_sub, dotProduct_add]
    simp only [Complex.add_re, Complex.sub_re]
    rw [hdebit_eq, hcoarse_eq]
    have hfre := congrArg Complex.re hfine
    rw [hfre]
    linarith

/-- `hermLamMax` is invariant under a unitary change of source frame. -/
theorem hermLamMax_unitary_conj {n : Type*} [Fintype n] [DecidableEq n]
    [Nonempty n] {D : Matrix n n ℂ} (hD : D.IsHermitian) {U : Matrix n n ℂ}
    (hU : Uᴴ * U = 1) (hUu : U * Uᴴ = 1)
    (hUD : (U * D * Uᴴ).IsHermitian) :
    hermLamMax hUD = hermLamMax hD := by
  have key : ∀ (V : Matrix n n ℂ), V * Vᴴ = 1 →
      ∀ (N : Matrix n n ℂ) (hN : N.IsHermitian) (hVN : (V * N * Vᴴ).IsHermitian),
      hermLamMax hVN ≤ hermLamMax hN := by
    intro V hWV N hN hVN
    refine hermLamMax_le_of_loewner _ ?_
    have hceil := (hermLamMax_ceiling hN).mul_mul_conjTranspose_same V
    have heq : V * ((hermLamMax hN : ℂ) • 1 - N) * Vᴴ
        = (hermLamMax hN : ℂ) • 1 - V * N * Vᴴ := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one,
        Matrix.smul_mul, hWV]
    rwa [heq] at hceil
  refine le_antisymm (key U hUu D hD hUD) ?_
  have heq : Uᴴ * (U * D * Uᴴ) * Uᴴᴴ = D := by
    rw [conjTranspose_conjTranspose, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      hU, Matrix.one_mul, Matrix.mul_assoc, hU, Matrix.mul_one]
  have hDalt : (Uᴴ * (U * D * Uᴴ) * Uᴴᴴ).IsHermitian := by
    rw [heq]; exact hD
  have h2 := key Uᴴ (by rwa [conjTranspose_conjTranspose])
    (U * D * Uᴴ) hUD hDalt
  rwa [hermLamMax_congr heq hDalt hD] at h2

/-- **(ST.10, norm ceiling)** The conjugated Hodge-screen debit obeys
`‖D_n‖ ≤ ‖D_n^old‖ + κ_n⁻¹ ‖X_n‖` in the `hermLamMax` rendering. -/
theorem hodge_debit_norm_le [Nonempty ι] {U Dold X : Matrix ι ι ℂ} {κ : ℝ}
    (hUu : Uᴴ * U = 1) (hUu' : U * Uᴴ = 1) (hκ : 0 < κ)
    (hDold : Dold.PosSemidef) (hX : X.PosSemidef)
    (hpack : (U * (Dold + ((κ⁻¹ : ℝ) : ℂ) • X) * Uᴴ).IsHermitian) :
    hermLamMax hpack ≤ hermLamMax hDold.1 + κ⁻¹ * hermLamMax hX.1 := by
  rw [hermLamMax_unitary_conj
    (hDold.add (posSemidef_real_smul hX (inv_nonneg.mpr hκ.le))).1
    hUu hUu' hpack]
  refine hermLamMax_le_of_loewner _ ?_
  have h1 := hermLamMax_ceiling hDold.1
  have h2 : (((κ⁻¹ * hermLamMax hX.1 : ℝ) : ℂ) • (1 : Matrix ι ι ℂ)
      - ((κ⁻¹ : ℝ) : ℂ) • X).PosSemidef := by
    have h3 := posSemidef_real_smul (X := (hermLamMax hX.1 : ℂ) • 1 - X)
      (hermLamMax_ceiling hX.1) (inv_nonneg.mpr hκ.le)
    have heq : ((κ⁻¹ : ℝ) : ℂ) • ((hermLamMax hX.1 : ℂ) • (1 : Matrix ι ι ℂ)
          - X)
        = ((κ⁻¹ * hermLamMax hX.1 : ℝ) : ℂ) • (1 : Matrix ι ι ℂ)
          - ((κ⁻¹ : ℝ) : ℂ) • X := by
      rw [smul_sub, smul_smul]
      norm_cast
    rwa [heq] at h3
  have hsum := h1.add h2
  have heq2 : (hermLamMax hDold.1 : ℂ) • (1 : Matrix ι ι ℂ) - Dold
      + (((κ⁻¹ * hermLamMax hX.1 : ℝ) : ℂ) • (1 : Matrix ι ι ℂ)
        - ((κ⁻¹ : ℝ) : ℂ) • X)
      = ((hermLamMax hDold.1 + κ⁻¹ * hermLamMax hX.1 : ℝ) : ℂ) • 1
        - (Dold + ((κ⁻¹ : ℝ) : ℂ) • X) := by
    have hcast : ((hermLamMax hDold.1 + κ⁻¹ * hermLamMax hX.1 : ℝ) : ℂ)
        = (hermLamMax hDold.1 : ℂ) + ((κ⁻¹ * hermLamMax hX.1 : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hcast, add_smul]
    abel
  rwa [heq2] at hsum

/-- **`cor:GT-Hodge-return-debit`** (ST.10 and the uniform reserve).  Along
a Hodge-screen chain of determining quotients — orthogonal head/high-Hodge
splittings `J_n J_n^* + W_n W_n^* = I`, source analyses not supported on
the high-Hodge complement, unitary source-frame transports `U_n`, and
variational source shorts `K_n` (ST.1) — suppose at every cutoff
`C_high,n ⪰ κ_n I` with `κ_n > 0`, `L_n^* L_n ⪯ T_n^* X_n T_n`, and that
`D_n^old` bounds the retained old/low form mismatch
(`A₀₀ₙ ⪰ A_n - T_n^* D_n^old T_n`).  Then every summed debit
`D_n = D_n^old + κ_n⁻¹ X_n` is admissible, and if
`∑_n (‖D_n^old‖ + κ_n⁻¹‖X_n‖) < λ_min(K_0)` the chain keeps the uniform
source reserve
`λ_min(K_N) ≥ λ_min(K_0) - ∑_n (‖D_n^old‖ + κ_n⁻¹‖X_n‖) > 0` for every
`N`, even when `κ_n ↓ 0` and the global form gap collapses (no lower bound
on the fine forms outside the determining quotients is used). -/
theorem hodge_return_debit_reserve [Nonempty ι]
    {Hsp : ℕ → Type} {Yh : ℕ → Type} [∀ n, Fintype (Hsp n)]
    [∀ n, DecidableEq (Hsp n)] [∀ n, Fintype (Yh n)]
    [∀ n, DecidableEq (Yh n)]
    (A : ∀ n, Matrix (Hsp n) (Hsp n) ℂ)
    (J : ∀ n, Matrix (Hsp (n + 1)) (Hsp n) ℂ)
    (W : ∀ n, Matrix (Hsp (n + 1)) (Yh n) ℂ)
    (T : ∀ n, Matrix ι (Hsp n) ℂ) (U : ℕ → Matrix ι ι ℂ)
    (Dold X : ℕ → Matrix ι ι ℂ) (κ : ℕ → ℝ) (K : ℕ → Matrix ι ι ℂ)
    (hKh : ∀ n, (K n).IsHermitian)
    (hKvar : ∀ n (s : ι → ℂ),
      IsLeast {r : ℝ | ∃ u, T n *ᵥ u = s ∧ r = (star u ⬝ᵥ (A n *ᵥ u)).re}
        ((star s ⬝ᵥ (K n *ᵥ s)).re))
    (hA : ∀ n, (A n).PosDef)
    (hcomp : ∀ n, J n * (J n)ᴴ + W n * (W n)ᴴ = 1)
    (hTW : ∀ n, T (n + 1) * W n = 0)
    (hTJ : ∀ n, T (n + 1) * J n = U n * T n)
    (hU : ∀ n, (U n)ᴴ * U n = 1) (hUu : ∀ n, U n * (U n)ᴴ = 1)
    (hκ : ∀ n, 0 < κ n)
    (hCfl : ∀ n, ((W n)ᴴ * A (n + 1) * W n - (κ n : ℂ) • 1).PosSemidef)
    (hDold : ∀ n, (Dold n).PosSemidef) (hX : ∀ n, (X n).PosSemidef)
    (hL : ∀ n, ((T n)ᴴ * X n * T n
      - ((W n)ᴴ * A (n + 1) * J n)ᴴ * ((W n)ᴴ * A (n + 1) * J n)).PosSemidef)
    (hold : ∀ n, ((J n)ᴴ * A (n + 1) * J n
      - (A n - (T n)ᴴ * Dold n * T n)).PosSemidef)
    (hsum : Summable fun n => hermLamMax (hDold n).1
      + (κ n)⁻¹ * hermLamMax (hX n).1)
    (hlt : (∑' n, (hermLamMax (hDold n).1 + (κ n)⁻¹ * hermLamMax (hX n).1))
      < hermLamMin (hKh 0)) :
    (∀ n, (A (n + 1) + (T (n + 1))ᴴ
        * (U n * (Dold n + (((κ n)⁻¹ : ℝ) : ℂ) • X n) * (U n)ᴴ) * T (n + 1)
      - ((J n)ᴴ)ᴴ * A n * (J n)ᴴ).PosSemidef) ∧
    0 < hermLamMin (hKh 0)
      - ∑' n, (hermLamMax (hDold n).1 + (κ n)⁻¹ * hermLamMax (hX n).1) ∧
    ∀ N, hermLamMin (hKh 0)
        - ∑' n, (hermLamMax (hDold n).1 + (κ n)⁻¹ * hermLamMax (hX n).1)
      ≤ hermLamMin (hKh N) := by
  -- the conjugated packet debits and their positivity
  set D : ℕ → Matrix ι ι ℂ :=
    fun n => U n * (Dold n + (((κ n)⁻¹ : ℝ) : ℂ) • X n) * (U n)ᴴ with hDdef
  have hDpsd : ∀ n, (D n).PosSemidef := fun n =>
    ((hDold n).add (posSemidef_real_smul (hX n)
      (inv_nonneg.mpr (hκ n).le))).mul_mul_conjTranspose_same (U n)
  -- ST.10 admissibility at every cutoff
  have hdebit : ∀ n, (A (n + 1) + (T (n + 1))ᴴ * D n * T (n + 1)
      - ((J n)ᴴ)ᴴ * A n * (J n)ᴴ).PosSemidef := by
    intro n
    have h := hodge_debit_admissible (A (n + 1)) (A n) (J n) (W n) (T n)
      (T (n + 1)) (U n) (Dold n) (X n) (κ n) (hA (n + 1)).1 (hA n)
      (hcomp n) (hTW n) (hTJ n) (hU n) (hκ n) (hCfl n) (hDold n) (hX n)
      (hL n) (hold n)
    rwa [conjTranspose_conjTranspose]
  refine ⟨hdebit, ?_⟩
  -- ST.3 for the head retraction `R_n = J_n^*`
  have hRT : ∀ n, T n * (J n)ᴴ = (U n)ᴴ * T (n + 1) := by
    intro n
    have hTf : T (n + 1) = U n * T n * (J n)ᴴ := by
      calc T (n + 1)
          = T (n + 1) * (J n * (J n)ᴴ) + T (n + 1) * (W n * (W n)ᴴ) := by
            rw [← Matrix.mul_add, hcomp n, Matrix.mul_one]
        _ = U n * T n * (J n)ᴴ + 0 := by
            rw [← Matrix.mul_assoc, hTJ n, ← Matrix.mul_assoc, hTW n,
              Matrix.zero_mul]
        _ = U n * T n * (J n)ᴴ := add_zero _
    rw [hTf, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hU n, Matrix.one_mul]
  -- summability comparison for the actual debit norms
  have hbound : ∀ n, hermLamMax (hDpsd n).1
      ≤ hermLamMax (hDold n).1 + (κ n)⁻¹ * hermLamMax (hX n).1 := fun n =>
    hodge_debit_norm_le (hU n) (hUu n) (hκ n) (hDold n) (hX n) (hDpsd n).1
  have hnn : ∀ n, 0 ≤ hermLamMax (hDpsd n).1 := fun n =>
    hermLamMax_nonneg (hDpsd n)
  have hsumD : Summable fun n => hermLamMax (hDpsd n).1 :=
    Summable.of_nonneg_of_le hnn hbound hsum
  have htsum_le : (∑' n, hermLamMax (hDpsd n).1)
      ≤ ∑' n, (hermLamMax (hDold n).1 + (κ n)⁻¹ * hermLamMax (hX n).1) :=
    hsumD.tsum_le_tsum hbound hsum
  have hltD : (∑' n, hermLamMax (hDpsd n).1) < hermLamMin (hKh 0) :=
    lt_of_le_of_lt htsum_le hlt
  -- the transported uniform reserve (ST.7)
  have hres := short_transport_uniform_reserve A T K (fun n => (J n)ᴴ) U D
    hKh hDpsd hKvar hRT hdebit hUu hsumD hltD
  refine ⟨?_, fun N => ?_⟩
  · linarith [hres.1, htsum_le]
  · have h2 := hres.2 N
    linarith [htsum_le]

end HodgeReturnDebit

/-! ### `cth:GT-static-projectivity-no-clock`

Rendering: the fine generators (ET.21) are the genuine two-dimensional
Ornstein–Uhlenbeck differential operators
`𝓛_{a,b} = a(-∂₁² + x₁∂₁) + b(-∂₂² + x₂∂₂)`, rendered on the slicewise
differentiable functions through `deriv` in each coordinate; they are
restricted to their invariant linear span (the degree-one Hermite layer,
the triage-sanctioned finite carrier).  The ground state is the genuine
standard Gaussian product measure on `ℝ²`, and the `L²(μ)` pairing of two
linear observables is proved to be the Euclidean pairing of their
coefficients (Gaussian Plancherel in degree one).  The record then proves:
(i) the static marginal of `y = (x₁+x₂)/√2` is the standard Gaussian for
every `(a, b)`; (ii) on the rotated frame `(y, y⊥)` the generator acts by
the 2×2 block `[[(a+b)/2, (a-b)/2], [(a-b)/2, (a+b)/2]]` and the exact
traced linear response — the ET.15 Schur complement of that block — is
`s_{a,b} = 2ab/(a+b)` (ET.22); (iii) the Green form of the response,
`⟨y, 𝓛⁻¹ y⟩⁻¹`, agrees; (iv) for `a ≠ b`, the coefficient semigroup orbit
of `y` (grounded as the solution of `d/ds u = -𝓛 u`) leaves the functions
of `y` at every positive time. -/

section StaticProjectivityNoClock

open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- The slicewise first-coordinate derivative. -/
noncomputable def ouD1 (f : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun p => deriv (fun s => f (s, p.2)) p.1

/-- The slicewise second-coordinate derivative. -/
noncomputable def ouD2 (f : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ :=
  fun p => deriv (fun s => f (p.1, s)) p.2

/-- **(ET.21)** The two-dimensional Ornstein–Uhlenbeck generator
`𝓛_{a,b} = a(-∂₁² + x₁∂₁) + b(-∂₂² + x₂∂₂)`. -/
noncomputable def ouGen (a b : ℝ) (f : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ := fun p =>
  a * (-(ouD1 (ouD1 f) p) + p.1 * ouD1 f p)
    + b * (-(ouD2 (ouD2 f) p) + p.2 * ouD2 f p)

/-- The linear observable with coefficient vector `c`. -/
def linF (c : ℝ × ℝ) : ℝ × ℝ → ℝ := fun p => c.1 * p.1 + c.2 * p.2

/-- First slicewise derivative of a linear observable. -/
theorem ouD1_linF (c : ℝ × ℝ) : ouD1 (linF c) = fun _ => c.1 := by
  funext p
  have h : HasDerivAt (fun s => c.1 * s + c.2 * p.2) (c.1 * 1) p.1 :=
    ((hasDerivAt_id p.1).const_mul c.1).add_const (c.2 * p.2)
  change deriv (fun s => linF c (s, p.2)) p.1 = c.1
  simp only [linF]
  rw [h.deriv, mul_one]

/-- Second slicewise derivative of a linear observable. -/
theorem ouD2_linF (c : ℝ × ℝ) : ouD2 (linF c) = fun _ => c.2 := by
  funext p
  have h : HasDerivAt (fun s => c.1 * p.1 + c.2 * s) (c.2 * 1) p.2 :=
    ((hasDerivAt_id p.2).const_mul c.2).const_add (c.1 * p.1)
  change deriv (fun s => linF c (p.1, s)) p.2 = c.2
  simp only [linF]
  rw [h.deriv, mul_one]

/-- The generator preserves the linear span and acts on coefficients by
`diag(a, b)`: `𝓛_{a,b} (c₁x₁ + c₂x₂) = a c₁ x₁ + b c₂ x₂`. -/
theorem ouGen_linF (a b : ℝ) (c : ℝ × ℝ) :
    ouGen a b (linF c) = linF (a * c.1, b * c.2) := by
  funext p
  have hd1 : ouD1 (ouD1 (linF c)) p = 0 := by
    rw [ouD1_linF]
    simp [ouD1]
  have hd2 : ouD2 (ouD2 (linF c)) p = 0 := by
    rw [ouD2_linF]
    simp [ouD2]
  have h1 : ouD1 (linF c) p = c.1 := by rw [ouD1_linF]
  have h2 : ouD2 (linF c) p = c.2 := by rw [ouD2_linF]
  unfold ouGen
  rw [hd1, hd2, h1, h2]
  unfold linF
  ring

/-- The standard Gaussian ground measure on `ℝ²`. -/
noncomputable def gauss2 : Measure (ℝ × ℝ) :=
  (gaussianReal 0 1).prod (gaussianReal 0 1)

/-- Unfolding lemma for the ground measure. -/
theorem gauss2_def : gauss2 = (gaussianReal 0 1).prod (gaussianReal 0 1) := rfl

/-- The second moment of the standard Gaussian. -/
theorem gauss_second_moment : ∫ x, x * x ∂gaussianReal (0 : ℝ) 1 = 1 := by
  have hm : MemLp (fun x : ℝ => x) 2 (gaussianReal 0 1) := memLp_id_gaussianReal 2
  have hs := variance_eq_sub (μ := gaussianReal 0 1) (X := fun x : ℝ => x) hm
  have hv : variance (fun x : ℝ => x) (gaussianReal 0 1) = ((1 : ℝ≥0) : ℝ) :=
    variance_fun_id_gaussianReal
  have hmean : (∫ x, x ∂gaussianReal (0 : ℝ) 1) = 0 := integral_id_gaussianReal
  have hpow : ∫ x, x * x ∂gaussianReal (0 : ℝ) 1
      = ∫ x, ((fun y : ℝ => y) ^ 2) x ∂gaussianReal (0 : ℝ) 1 := by
    congr 1
    funext x
    simp [pow_two]
  rw [hpow]
  rw [hs, hmean] at hv
  simp only [NNReal.coe_one] at hv
  linarith

/-- **Gaussian Plancherel in degree one**: the `L²(μ)` pairing of two
linear observables is the Euclidean pairing of their coefficients. -/
theorem gauss2_linF_inner (c d : ℝ × ℝ) :
    ∫ p, linF c p * linF d p ∂gauss2 = c.1 * d.1 + c.2 * d.2 := by
  have hx : Integrable (fun x : ℝ => x) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal 2).integrable one_le_two
  have hxx : Integrable (fun x : ℝ => x * x) (gaussianReal 0 1) := by
    have h := (memLp_id_gaussianReal (μ := 0) (v := 1) 2).integrable_sq
    simpa [pow_two] using h
  have hone : Integrable (fun _ : ℝ => (1 : ℝ)) (gaussianReal 0 1) :=
    integrable_const 1
  -- the four product integrals
  have h11 : ∫ p : ℝ × ℝ, p.1 * p.1 ∂gauss2 = 1 := by
    have h := integral_prod_mul (μ := gaussianReal 0 1) (ν := gaussianReal 0 1)
      (f := fun x : ℝ => x * x) (g := fun _ : ℝ => (1 : ℝ))
    simp only [mul_one] at h
    rw [gauss2_def, h, gauss_second_moment]
    simp
  have h22 : ∫ p : ℝ × ℝ, p.2 * p.2 ∂gauss2 = 1 := by
    have h := integral_prod_mul (μ := gaussianReal 0 1) (ν := gaussianReal 0 1)
      (f := fun _ : ℝ => (1 : ℝ)) (g := fun x : ℝ => x * x)
    simp only [one_mul] at h
    rw [gauss2_def, h, gauss_second_moment]
    simp
  have h12 : ∫ p : ℝ × ℝ, p.1 * p.2 ∂gauss2 = 0 := by
    have h := integral_prod_mul (μ := gaussianReal 0 1) (ν := gaussianReal 0 1)
      (f := fun x : ℝ => x) (g := fun x : ℝ => x)
    rw [gauss2_def, h, integral_id_gaussianReal]
    simp
  have h21 : ∫ p : ℝ × ℝ, p.2 * p.1 ∂gauss2 = 0 := by
    calc ∫ p : ℝ × ℝ, p.2 * p.1 ∂gauss2
        = ∫ p : ℝ × ℝ, p.1 * p.2 ∂gauss2 := by
          congr 1
          funext p
          exact mul_comm _ _
      _ = 0 := h12
  -- integrability of the four product terms over the product measure
  have i11 : Integrable (fun p : ℝ × ℝ => p.1 * p.1) gauss2 := by
    have h := hxx.mul_prod hone
    simp only [mul_one] at h
    rw [gauss2_def]
    exact h
  have i22 : Integrable (fun p : ℝ × ℝ => p.2 * p.2) gauss2 := by
    have h := hone.mul_prod hxx
    simp only [one_mul] at h
    rw [gauss2_def]
    exact h
  have i12 : Integrable (fun p : ℝ × ℝ => p.1 * p.2) gauss2 := by
    rw [gauss2_def]
    exact hx.mul_prod hx
  have i21 : Integrable (fun p : ℝ × ℝ => p.2 * p.1) gauss2 := by
    have h : (fun p : ℝ × ℝ => p.2 * p.1) = fun p : ℝ × ℝ => p.1 * p.2 := by
      funext p
      exact mul_comm _ _
    rw [h]
    exact i12
  -- expand the bilinear pairing and split the integral
  have hexp : (fun p : ℝ × ℝ => linF c p * linF d p)
      = fun p : ℝ × ℝ => c.1 * d.1 * (p.1 * p.1) + c.1 * d.2 * (p.1 * p.2)
        + (c.2 * d.1 * (p.2 * p.1) + c.2 * d.2 * (p.2 * p.2)) := by
    funext p
    unfold linF
    ring
  have e1 : ∫ p : ℝ × ℝ, (c.1 * d.1 * (p.1 * p.1) + c.1 * d.2 * (p.1 * p.2)
        + (c.2 * d.1 * (p.2 * p.1) + c.2 * d.2 * (p.2 * p.2))) ∂gauss2
      = (∫ p : ℝ × ℝ, (c.1 * d.1 * (p.1 * p.1)
          + c.1 * d.2 * (p.1 * p.2)) ∂gauss2)
        + ∫ p : ℝ × ℝ, (c.2 * d.1 * (p.2 * p.1)
          + c.2 * d.2 * (p.2 * p.2)) ∂gauss2 :=
    integral_add ((i11.const_mul _).add (i12.const_mul _))
      ((i21.const_mul _).add (i22.const_mul _))
  have e2 : ∫ p : ℝ × ℝ, (c.1 * d.1 * (p.1 * p.1)
        + c.1 * d.2 * (p.1 * p.2)) ∂gauss2
      = (∫ p : ℝ × ℝ, c.1 * d.1 * (p.1 * p.1) ∂gauss2)
        + ∫ p : ℝ × ℝ, c.1 * d.2 * (p.1 * p.2) ∂gauss2 :=
    integral_add (i11.const_mul _) (i12.const_mul _)
  have e3 : ∫ p : ℝ × ℝ, (c.2 * d.1 * (p.2 * p.1)
        + c.2 * d.2 * (p.2 * p.2)) ∂gauss2
      = (∫ p : ℝ × ℝ, c.2 * d.1 * (p.2 * p.1) ∂gauss2)
        + ∫ p : ℝ × ℝ, c.2 * d.2 * (p.2 * p.2) ∂gauss2 :=
    integral_add (i21.const_mul _) (i22.const_mul _)
  rw [hexp, e1, e2, e3, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_const_mul, h11, h12, h21, h22]
  ring

/-- The observable `y = (x₁ + x₂)/√2`. -/
noncomputable def ymap : ℝ × ℝ → ℝ := fun p => (p.1 + p.2) / Real.sqrt 2

/-- **(exact projectivity)** The static marginal of `y` is the standard
Gaussian — for every clock pair `(a, b)`, since the ground measure does
not depend on it. -/
theorem static_marginal_eq : gauss2.map ymap = gaussianReal 0 1 := by
  have hconv : gauss2.map (fun p : ℝ × ℝ => p.1 + p.2)
      = gaussianReal 0 1 ∗ gaussianReal 0 1 := rfl
  have hcomp : ymap = (fun x : ℝ => x / Real.sqrt 2)
      ∘ (fun p : ℝ × ℝ => p.1 + p.2) := rfl
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop), hconv,
    gaussianReal_conv_gaussianReal, gaussianReal_map_div_const]
  have hmean : ((0 : ℝ) + 0) / Real.sqrt 2 = 0 := by norm_num
  have hvar : ((1 : ℝ≥0) + 1) / (NNReal.mk (Real.sqrt 2 ^ 2) (sq_nonneg _))
      = 1 := by
    have hs : NNReal.mk (Real.sqrt 2 ^ 2) (sq_nonneg _) = 2 := by
      ext
      rw [NNReal.coe_mk, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    rw [hs]
    norm_num
  rw [hmean, hvar]

/-- The unit coefficient vector of `y`. -/
noncomputable def yvec : ℝ × ℝ := ((Real.sqrt 2)⁻¹, (Real.sqrt 2)⁻¹)

/-- The unit coefficient vector of `y⊥ = (x₁ - x₂)/√2`. -/
noncomputable def yperp : ℝ × ℝ := ((Real.sqrt 2)⁻¹, -(Real.sqrt 2)⁻¹)

/-- The generator on the rotated frame, `y`-row: retained block `(a+b)/2`,
coupling `(a-b)/2`. -/
theorem ouGen_yvec (a b : ℝ) :
    ouGen a b (linF yvec)
      = fun p => (a + b) / 2 * linF yvec p + (a - b) / 2 * linF yperp p := by
  rw [ouGen_linF]
  funext p
  unfold linF yvec yperp
  ring

/-- The generator on the rotated frame, `y⊥`-row: coupling `(a-b)/2`,
hidden block `(a+b)/2`. -/
theorem ouGen_yperp (a b : ℝ) :
    ouGen a b (linF yperp)
      = fun p => (a - b) / 2 * linF yvec p + (a + b) / 2 * linF yperp p := by
  rw [ouGen_linF]
  funext p
  unfold linF yvec yperp
  ring

/-- The exact traced linear response: the ET.15 Schur complement of the
rotated `2×2` generator block onto the retained `y`-direction. -/
noncomputable def tracedResponse (a b : ℝ) : ℝ :=
  (a + b) / 2 - ((a - b) / 2) ^ 2 / ((a + b) / 2)

/-- **(ET.22)** `s_{a,b} = 2ab/(a+b)`. -/
theorem tracedResponse_eq (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    tracedResponse a b = 2 * a * b / (a + b) := by
  unfold tracedResponse
  have hab : a + b ≠ 0 := by positivity
  field_simp
  ring

/-- The coefficient vector of the Green observable `𝓛⁻¹ y`. -/
noncomputable def greenVec (a b : ℝ) : ℝ × ℝ :=
  ((Real.sqrt 2)⁻¹ / a, (Real.sqrt 2)⁻¹ / b)

/-- The Green observable inverts the clock: `𝓛_{a,b}(𝓛⁻¹y) = y`. -/
theorem ouGen_greenVec (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) :
    ouGen a b (linF (greenVec a b)) = linF yvec := by
  rw [ouGen_linF]
  change linF (a * ((Real.sqrt 2)⁻¹ / a), b * ((Real.sqrt 2)⁻¹ / b))
    = linF ((Real.sqrt 2)⁻¹, (Real.sqrt 2)⁻¹)
  have h1 : a * ((Real.sqrt 2)⁻¹ / a) = (Real.sqrt 2)⁻¹ := by field_simp
  have h2 : b * ((Real.sqrt 2)⁻¹ / b) = (Real.sqrt 2)⁻¹ := by field_simp
  rw [h1, h2]

/-- **(ET.17, Green form)** The Gaussian pairing `⟨y, 𝓛⁻¹y⟩` is
`(a+b)/(2ab)`. -/
theorem green_pairing (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∫ p, linF (greenVec a b) p * linF yvec p ∂gauss2 = (a + b) / (2 * a * b) := by
  rw [gauss2_linF_inner]
  unfold greenVec yvec
  have hs : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = 2⁻¹ := by
    rw [← mul_inv]
    congr 1
    exact Real.mul_self_sqrt (by norm_num)
  have ha' : a ≠ 0 := ha.ne'
  have hb' : b ≠ 0 := hb.ne'
  field_simp
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
    Real.sqrt_nonneg 2, hs]

/-- The inverse Green pairing recovers the traced response (ET.17/ET.22). -/
theorem green_inverse (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ((a + b) / (2 * a * b))⁻¹ = tracedResponse a b := by
  rw [tracedResponse_eq a b ha hb]
  have hab : a + b ≠ 0 := by positivity
  field_simp

/-- The coefficient flow of the fine semigroup `e^{-t𝓛_{a,b}}` on the
linear span. -/
noncomputable def ouFlow (a b t : ℝ) (c : ℝ × ℝ) : ℝ × ℝ :=
  (Real.exp (-a * t) * c.1, Real.exp (-b * t) * c.2)

/-- The flow starts at the identity. -/
theorem ouFlow_zero (a b : ℝ) (c : ℝ × ℝ) : ouFlow a b 0 c = c := by
  unfold ouFlow
  simp

/-- The flow is the genuine semigroup orbit: it solves `d/ds u = -𝓛 u`
pointwise on the linear span. -/
theorem ouFlow_hasDerivAt (a b t : ℝ) (c : ℝ × ℝ) (p : ℝ × ℝ) :
    HasDerivAt (fun s => linF (ouFlow a b s c) p)
      (-(ouGen a b (linF (ouFlow a b t c)) p)) t := by
  have h1 : HasDerivAt (fun s : ℝ => -a * s) (-a) t := by
    simpa using (hasDerivAt_id t).const_mul (-a)
  have h2 : HasDerivAt (fun s : ℝ => -b * s) (-b) t := by
    simpa using (hasDerivAt_id t).const_mul (-b)
  have he1 : HasDerivAt (fun s => Real.exp (-a * s))
      (Real.exp (-a * t) * (-a)) t := h1.exp
  have he2 : HasDerivAt (fun s => Real.exp (-b * s))
      (Real.exp (-b * t) * (-b)) t := h2.exp
  have hsum := ((he1.mul_const (c.1 * p.1))).fun_add
    ((he2.mul_const (c.2 * p.2)))
  have hfun : (fun s => Real.exp (-a * s) * (c.1 * p.1)
        + Real.exp (-b * s) * (c.2 * p.2))
      = fun s => linF (ouFlow a b s c) p := by
    funext s
    unfold linF ouFlow
    ring
  rw [hfun] at hsum
  have hval : -(ouGen a b (linF (ouFlow a b t c)) p)
      = Real.exp (-a * t) * -a * (c.1 * p.1)
        + Real.exp (-b * t) * -b * (c.2 * p.2) := by
    rw [ouGen_linF]
    simp only [linF, ouFlow]
    ring
  rw [hval]
  exact hsum

/-- **(no clock)** For `a ≠ b` the fine semigroup moves `y` out of the
functions of `y` at every positive time: the flowed observable is not a
multiple of `y`. -/
theorem ouFlow_not_function_of_y (a b t : ℝ) (hab : a ≠ b) (ht : 0 < t) :
    ¬∃ r : ℝ, linF (ouFlow a b t yvec) = fun p => r * ymap p := by
  rintro ⟨r, hr⟩
  have hs2 : Real.sqrt 2 ≠ 0 := by positivity
  have h1' : Real.exp (-a * t) = r := by
    have h := congrFun hr (Real.sqrt 2, 0)
    simp only [linF, ouFlow, yvec, ymap] at h
    rw [mul_zero, add_zero, mul_assoc, inv_mul_cancel₀ hs2, mul_one,
      add_zero, div_self hs2, mul_one] at h
    exact h
  have h2' : Real.exp (-b * t) = r := by
    have h := congrFun hr (0, Real.sqrt 2)
    simp only [linF, ouFlow, yvec, ymap] at h
    rw [mul_zero, zero_add, mul_assoc, inv_mul_cancel₀ hs2, mul_one,
      zero_add, div_self hs2, mul_one] at h
    exact h
  have hexp : Real.exp (-a * t) = Real.exp (-b * t) := by rw [h1', h2']
  refine hab ?_
  have h := Real.exp_eq_exp.mp hexp
  have hmul : a * t = b * t := by linarith
  exact mul_right_cancel₀ ht.ne' hmul

/-- **`cth:GT-static-projectivity-no-clock`** (ET.21–ET.22, bundled).
For every clock pair `a, b > 0`: the static marginal of `y = (x₁+x₂)/√2`
is the standard Gaussian (independent of `(a, b)`); the exact traced
linear response — the Schur complement of the rotated generator block onto
the retained `y` direction — is `s_{a,b} = 2ab/(a+b)`, agreeing with the
inverse Green pairing `⟨y, 𝓛⁻¹y⟩⁻¹`; and when `a ≠ b` the functions of
`y` are not invariant under the fine semigroup at any positive time.  An
exactly projective equilibrium family may therefore carry inequivalent
local clocks and nonzero returning memory. -/
theorem static_projectivity_no_clock (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    gauss2.map ymap = gaussianReal 0 1
    ∧ tracedResponse a b = 2 * a * b / (a + b)
    ∧ ouGen a b (linF (greenVec a b)) = linF yvec
    ∧ (∫ p, linF (greenVec a b) p * linF yvec p ∂gauss2)⁻¹
        = tracedResponse a b
    ∧ (a ≠ b → ∀ t : ℝ, 0 < t →
        ¬∃ r : ℝ, linF (ouFlow a b t yvec) = fun p => r * ymap p) :=
  ⟨static_marginal_eq, tracedResponse_eq a b ha hb,
    ouGen_greenVec a b ha.ne' hb.ne',
    by rw [green_pairing a b ha hb]; exact green_inverse a b ha hb,
    fun hab t ht => ouFlow_not_function_of_y a b t hab ht⟩

end StaticProjectivityNoClock

/-! ### Shared semigroup-cyclic layer for the dynamic-source records

The reflected Hamiltonian `H = H^* ⪰ 0` acts on a finite-dimensional
complex Hilbert carrier `V`; finite source syntheses are continuous linear
maps from finite-dimensional coefficient spaces.  This section builds the
heat semigroup `e^{-tH}`, the spans of finite time banks, the
semigroup-cyclic carrier `𝓒_H(B)` (LT.26), and the projection calculus
used by records `thm:GT-dynamic-source-ancestry`,
`thm:GT-temporal-Schur-dynamic-source` and
`prop:GT-dynamic-source-transport-rectangle`. -/

section DynamicSourceCluster

open ContinuousLinearMap Submodule Filter Topology Upstream
open scoped InnerProduct ComplexInnerProductSpace

variable {V E E' : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [FiniteDimensional ℂ E']

/-- The heat semigroup `e^{-tH}` of a (not necessarily self-adjoint)
generator, as the Banach-algebra exponential. -/
noncomputable def expH (H : V →L[ℂ] V) (t : ℝ) : V →L[ℂ] V :=
  NormedSpace.exp ((-t) • H)

/-- `e^{-0·H} = I`. -/
theorem expH_zero (H : V →L[ℂ] V) : expH H 0 = 1 := by
  unfold expH
  rw [neg_zero, zero_smul]
  exact NormedSpace.exp_zero

/-- The semigroup law `e^{-sH} e^{-tH} = e^{-(s+t)H}`. -/
theorem expH_mul (H : V →L[ℂ] V) (s t : ℝ) :
    expH H s * expH H t = expH H (s + t) := by
  unfold expH
  rw [show (-(s + t) : ℝ) = -s + -t by ring]
  exact (exp_smul_semigroup H (-s) (-t)).symm

/-- The semigroup commutes with its generator. -/
theorem expH_commute (H : V →L[ℂ] V) (t : ℝ) :
    Commute H (expH H t) :=
  ((Commute.refl H).smul_right (-t)).exp_right

/-- Any operator commuting with the generator commutes with the
semigroup. -/
theorem expH_commute_of_commute {H P : V →L[ℂ] V} (h : Commute P H)
    (t : ℝ) : Commute P (expH H t) :=
  (h.smul_right (-t)).exp_right

/-- Adjoint of the heat semigroup of a self-adjoint generator. -/
theorem expH_adjoint {H : V →L[ℂ] V} (hH : IsSelfAdjoint H) (t : ℝ) :
    (expH H t)† = expH H t := by
  have h := NormedSpace.star_exp ((-t) • H)
  have hstar : star ((-t) • H) = (-t) • H := by
    rw [star_smul, star_trivial, hH.star_eq]
  rw [hstar] at h
  calc (expH H t)† = star (expH H t) := (star_eq_adjoint _).symm
    _ = expH H t := by
        unfold expH
        exact h

/-- Real-parameter derivative of the heat semigroup:
`d/dt e^{-tH} = -(e^{-tH} H)`. -/
theorem expH_hasDerivAt (H : V →L[ℂ] V) (t : ℝ) :
    HasDerivAt (fun s => expH H s) (-(expH H t * H)) t := by
  have hg : HasDerivAt (fun u : ℝ => NormedSpace.exp (u • H))
      (NormedSpace.exp ((-t) • H) * H) (-t) :=
    hasDerivAt_exp_smul_const (𝕂 := ℝ) H (-t)
  have hf : HasDerivAt (fun s : ℝ => -s) (-1 : ℝ) t := hasDerivAt_neg t
  have hcomp := HasDerivAt.scomp t hg hf
  have hval : ((-1 : ℝ) • (NormedSpace.exp ((-t) • H) * H))
      = -(expH H t * H) := by
    unfold expH
    rw [neg_one_smul]
  rw [hval] at hcomp
  exact hcomp

/-- The heat semigroup is continuous in time. -/
theorem expH_continuous (H : V →L[ℂ] V) :
    Continuous fun t : ℝ => expH H t :=
  continuous_iff_continuousAt.mpr fun t =>
    (expH_hasDerivAt H t).continuousAt

/-- Orbit continuity `t ↦ e^{-tH} x`. -/
theorem expH_apply_continuous (H : V →L[ℂ] V) (x : V) :
    Continuous fun t : ℝ => expH H t x := by
  exact (isBoundedBilinearMap_apply.continuous.comp
    ((expH_continuous H).prodMk continuous_const))

/-- The span of the semigroup translates of the source range over a set
of times. -/
noncomputable def bankSpan (H : V →L[ℂ] V) (B : E →L[ℂ] V)
    (D : Set ℝ) : Submodule ℂ V :=
  Submodule.span ℂ {v | ∃ t ∈ D, ∃ u : E, v = expH H t (B u)}

/-- **(LT.26)** The semigroup-cyclic carrier
`𝓒_H(B) = span{e^{-tH} B u : t ≥ 0}` (closed, since the carrier is
finite-dimensional). -/
noncomputable def cyc (H : V →L[ℂ] V) (B : E →L[ℂ] V) : Submodule ℂ V :=
  bankSpan H B (Set.Ici 0)

omit [FiniteDimensional ℂ E] in
/-- Bank spans are monotone in the time bank. -/
theorem bankSpan_mono (H : V →L[ℂ] V) (B : E →L[ℂ] V) {D₁ D₂ : Set ℝ}
    (h : D₁ ⊆ D₂) : bankSpan H B D₁ ≤ bankSpan H B D₂ := by
  apply Submodule.span_mono
  rintro v ⟨t, ht, u, rfl⟩
  exact ⟨t, h ht, u, rfl⟩

omit [FiniteDimensional ℂ E] in
/-- Generators belong to the bank span. -/
theorem expH_apply_mem_bankSpan (H : V →L[ℂ] V) (B : E →L[ℂ] V)
    {D : Set ℝ} {t : ℝ} (ht : t ∈ D) (u : E) :
    expH H t (B u) ∈ bankSpan H B D :=
  Submodule.subset_span ⟨t, ht, u, rfl⟩

omit [FiniteDimensional ℂ E] in
/-- A bank containing time zero spans the source range. -/
theorem range_le_bankSpan (H : V →L[ℂ] V) (B : E →L[ℂ] V) {D : Set ℝ}
    (h0 : (0 : ℝ) ∈ D) : B.range ≤ bankSpan H B D := by
  rintro v ⟨u, rfl⟩
  have h := expH_apply_mem_bankSpan H B h0 u
  rwa [expH_zero, one_apply_eq_self] at h

omit [FiniteDimensional ℂ E] in
/-- Slope-closure of a bank span: at a time that clusters inside the
bank, the generator maps the semigroup orbit into the bank span. -/
theorem generator_apply_mem_bankSpan (H : V →L[ℂ] V) (B : E →L[ℂ] V)
    {D : Set ℝ} {t₀ : ℝ} (ht₀ : t₀ ∈ D)
    (hcl : (𝓝[D \ {t₀}] t₀).NeBot) (u : E) :
    H (expH H t₀ (B u)) ∈ bankSpan H B D := by
  set S := bankSpan H B D with hS
  have hclosed : IsClosed (S : Set V) := S.closed_of_finiteDimensional
  set f : ℝ → V := fun s => expH H s (B u) with hf
  -- the orbit derivative at `t₀`
  have hderiv : HasDerivAt f (-(H (expH H t₀ (B u)))) t₀ := by
    have hL := (((ContinuousLinearMap.apply ℂ V (B u)).restrictScalars
      ℝ).hasFDerivAt (x := expH H t₀)).comp_hasDerivAt t₀
      (expH_hasDerivAt H t₀)
    have hval : ((ContinuousLinearMap.apply ℂ V (B u)).restrictScalars ℝ)
        (-(expH H t₀ * H)) = -(H (expH H t₀ (B u))) := by
      have hc := (expH_commute H t₀).eq
      calc ((ContinuousLinearMap.apply ℂ V (B u)).restrictScalars ℝ)
            (-(expH H t₀ * H))
          = -((expH H t₀ * H) (B u)) := rfl
        _ = -((H * expH H t₀) (B u)) := by rw [← hc]
        _ = -(H (expH H t₀ (B u))) := rfl
    rw [hval] at hL
    exact hL
  -- slopes over the bank lie in the span
  have hslope : ∀ s ∈ D \ {t₀}, slope f t₀ s ∈ S := by
    rintro s ⟨hsD, -⟩
    have h1 : f s ∈ S := expH_apply_mem_bankSpan H B hsD u
    have h2 : f t₀ ∈ S := expH_apply_mem_bankSpan H B ht₀ u
    have h3 : f s - f t₀ ∈ S := S.sub_mem h1 h2
    have h4 : slope f t₀ s = (((s - t₀)⁻¹ : ℝ) : ℂ) • (f s - f t₀) := by
      rw [slope_def_module]
      rw [← algebraMap_smul ℂ ((s - t₀)⁻¹ : ℝ) (f s - f t₀)]
      rfl
    rw [h4]
    exact S.smul_mem _ h3
  have htend : Tendsto (slope f t₀) (𝓝[D \ {t₀}] t₀)
      (𝓝 (-(H (expH H t₀ (B u))))) := by
    have h := (hasDerivAt_iff_tendsto_slope).mp hderiv
    exact h.mono_left (nhdsWithin_mono t₀ (by
      intro s hs
      exact hs.2))
  have hmem : -(H (expH H t₀ (B u))) ∈ S := by
    refine hclosed.mem_of_tendsto htend ?_
    exact eventually_nhdsWithin_of_forall hslope
  have := S.neg_mem hmem
  rwa [neg_neg] at this

omit [FiniteDimensional ℂ V] in
/-- Real multiples stay in a complex submodule. -/
theorem real_smul_mem (S : Submodule ℂ V) {v : V} (hv : v ∈ S) (r : ℝ) :
    r • v ∈ S := by
  rw [← algebraMap_smul ℂ r v]
  exact S.smul_mem _ hv

/-- The Krylov span of the source range under the generator. -/
noncomputable def krylovSpan (H : V →L[ℂ] V) (B : E →L[ℂ] V) :
    Submodule ℂ V :=
  Submodule.span ℂ {v | ∃ (n : ℕ) (u : E), v = (H ^ n) (B u)}

omit [FiniteDimensional ℂ E] in
/-- The generator maps the cyclic carrier into itself. -/
theorem generator_maps_cyc (H : V →L[ℂ] V) (B : E →L[ℂ] V) {v : V}
    (hv : v ∈ cyc H B) : H v ∈ cyc H B := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨t, ht, u, rfl⟩ := hv
    have hne : (𝓝[Set.Ici (0 : ℝ) \ {t}] t).NeBot := by
      refine Filter.neBot_of_le (f := 𝓝[Set.Ioi t] t) ?_
      refine nhdsWithin_mono t fun s hs => ?_
      have hts : t < s := hs
      exact ⟨Set.mem_Ici.mpr (le_trans (Set.mem_Ici.mp ht) hts.le),
        fun heq => absurd (Set.mem_singleton_iff.mp heq).symm hts.ne⟩
    exact generator_apply_mem_bankSpan H B ht hne u
  | zero =>
    rw [map_zero]
    exact (cyc H B).zero_mem
  | add x y _ _ hx hy =>
    rw [map_add]
    exact (cyc H B).add_mem hx hy
  | smul c x _ hx =>
    rw [map_smul]
    exact (cyc H B).smul_mem c hx

omit [FiniteDimensional ℂ E] in
/-- The Krylov span is contained in the cyclic carrier. -/
theorem krylovSpan_le_cyc (H : V →L[ℂ] V) (B : E →L[ℂ] V) :
    krylovSpan H B ≤ cyc H B := by
  refine Submodule.span_le.mpr ?_
  rintro v ⟨n, u, rfl⟩
  induction n with
  | zero =>
    have h0 : (H ^ 0) (B u) = B u := by
      rw [pow_zero]
      rfl
    rw [h0]
    exact range_le_bankSpan H B (Set.mem_Ici.mpr le_rfl) ⟨u, rfl⟩
  | succ n ih =>
    have h : (H ^ (n + 1)) (B u) = H ((H ^ n) (B u)) := by
      rw [pow_succ']
      rfl
    rw [h]
    exact generator_maps_cyc H B ih

omit [FiniteDimensional ℂ E] in
/-- The cyclic carrier is contained in the Krylov span (exponential
series). -/
theorem cyc_le_krylovSpan (H : V →L[ℂ] V) (B : E →L[ℂ] V) :
    cyc H B ≤ krylovSpan H B := by
  refine Submodule.span_le.mpr ?_
  rintro v ⟨t, -, u, rfl⟩
  have hser := exp_apply_tsum ((-t) • H) (B u)
  change NormedSpace.exp ((-t) • H) (B u) ∈ krylovSpan H B
  rw [hser]
  refine tsum_mem (krylovSpan H B).closed_of_finiteDimensional fun n => ?_
  have hpow : (((-t) • H) ^ n) (B u) = (-t) ^ n • ((H ^ n) (B u)) := by
    rw [smul_pow]
    rfl
  rw [hpow]
  refine (krylovSpan H B).smul_mem _ ?_
  refine real_smul_mem _ ?_ _
  exact Submodule.subset_span
    (show (H ^ n) (B u)
        ∈ {v | ∃ (n : ℕ) (u : E), v = (H ^ n) (B u)} from ⟨n, u, rfl⟩)

omit [FiniteDimensional ℂ E] in
/-- The cyclic carrier is exactly the Krylov span. -/
theorem cyc_eq_krylovSpan (H : V →L[ℂ] V) (B : E →L[ℂ] V) :
    cyc H B = krylovSpan H B :=
  le_antisymm (cyc_le_krylovSpan H B) (krylovSpan_le_cyc H B)

omit [FiniteDimensional ℂ E] in
/-- A bank that is dense in the positive half-line spans the whole
cyclic carrier. -/
theorem bankSpan_eq_cyc_of_dense (H : V →L[ℂ] V) (B : E →L[ℂ] V)
    {D : Set ℝ} (hD : D ⊆ Set.Ici 0)
    (hdense : Set.Ici (0 : ℝ) ⊆ closure D) :
    bankSpan H B D = cyc H B := by
  refine le_antisymm (bankSpan_mono H B hD) (Submodule.span_le.mpr ?_)
  rintro v ⟨t, ht, u, rfl⟩
  have hne : (𝓝[D] t).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.mp (hdense ht)
  have htend : Tendsto (fun s => expH H s (B u)) (𝓝[D] t)
      (𝓝 (expH H t (B u))) :=
    ((expH_apply_continuous H (B u)).tendsto t).mono_left nhdsWithin_le_nhds
  exact (bankSpan H B D).closed_of_finiteDimensional.mem_of_tendsto htend
    (eventually_nhdsWithin_of_forall fun s hs =>
      expH_apply_mem_bankSpan H B hs u)

omit [FiniteDimensional ℂ E] in
/-- The orthogonal complement of the cyclic carrier is invariant under a
self-adjoint generator. -/
theorem generator_maps_cyc_orth {H : V →L[ℂ] V} (hH : IsSelfAdjoint H)
    (B : E →L[ℂ] V) {v : V} (hv : v ∈ (cyc H B)ᗮ) : H v ∈ (cyc H B)ᗮ := by
  intro c hc
  have h1 : ⟪H c, v⟫ = 0 := hv (H c) (generator_maps_cyc H B hc)
  calc ⟪c, H v⟫ = ⟪(H†) c, v⟫ :=
        (ContinuousLinearMap.adjoint_inner_left H v c).symm
    _ = ⟪H c, v⟫ := by rw [hH.adjoint_eq]
    _ = 0 := h1

/-- An operator preserving a submodule and its orthogonal complement
commutes with the orthogonal projection. -/
theorem starProjection_comm_of_invariant {K : Submodule ℂ V}
    (T : V →L[ℂ] V) (hK : ∀ v ∈ K, T v ∈ K) (hK' : ∀ v ∈ Kᗮ, T v ∈ Kᗮ) :
    K.starProjection ∘L T = T ∘L K.starProjection := by
  ext x
  have hdec : x = K.starProjection x + (x - K.starProjection x) := by abel
  have hmem1 : T (K.starProjection x) ∈ K :=
    hK _ (K.starProjection_apply_mem x)
  have hmem2 : T (x - K.starProjection x) ∈ Kᗮ :=
    hK' _ (K.sub_starProjection_mem_orthogonal x)
  calc K.starProjection (T x)
      = K.starProjection (T (K.starProjection x)
          + T (x - K.starProjection x)) := by
        rw [← map_add]
        congr 1
        rw [← hdec]
    _ = K.starProjection (T (K.starProjection x))
          + K.starProjection (T (x - K.starProjection x)) := map_add _ _ _
    _ = T (K.starProjection x) + 0 := by
        rw [K.starProjection_eq_self_iff.mpr hmem1,
          K.starProjection_apply_eq_zero_iff.mpr hmem2]
    _ = T (K.starProjection x) := add_zero _

/-- Positivity of the compression of an orthogonal projection by a
target synthesis: `Y^* P_K Y ⪰ 0`. -/
theorem compressed_starProjection_isPositive (K : Submodule ℂ V)
    (Y : E' →L[ℂ] V) :
    ((Y†) ∘L K.starProjection ∘L Y).IsPositive := by
  have hP : K.starProjection = K.starProjection ∘L K.starProjection := by
    ext x
    exact (K.starProjection_eq_self_iff.mpr (K.starProjection_apply_mem x)).symm
  have hfact : (Y†) ∘L K.starProjection ∘L Y
      = (K.starProjection ∘L Y)† ∘L (K.starProjection ∘L Y) := by
    rw [ContinuousLinearMap.adjoint_comp,
      isSelfAdjoint_iff'.mp (isSelfAdjoint_starProjection K)]
    rw [ContinuousLinearMap.comp_assoc]
    congr 1
    rw [← ContinuousLinearMap.comp_assoc, ← hP]
  rw [hfact]
  exact ContinuousLinearMap.isPositive_adjoint_comp_self _

/-- The real diagonal pairing of an orthogonal projection is the squared
projected norm. -/
theorem re_inner_starProjection_self (K : Submodule ℂ V) (v : V) :
    (⟪K.starProjection v, v⟫).re = ‖K.starProjection v‖ ^ 2 := by
  have horth : ⟪K.starProjection v, v - K.starProjection v⟫ = 0 :=
    (Submodule.mem_orthogonal _ _).mp
      (K.sub_starProjection_mem_orthogonal v) _
      (K.starProjection_apply_mem v)
  have hsplit : ⟪K.starProjection v, v⟫
      = ⟪K.starProjection v, K.starProjection v⟫ := by
    calc ⟪K.starProjection v, v⟫
        = ⟪K.starProjection v, K.starProjection v
            + (v - K.starProjection v)⟫ := by
          congr 1
          abel
      _ = ⟪K.starProjection v, K.starProjection v⟫
            + ⟪K.starProjection v, v - K.starProjection v⟫ :=
          inner_add_right _ _ _
      _ = ⟪K.starProjection v, K.starProjection v⟫ := by
          rw [horth, add_zero]
  rw [hsplit]
  exact cre_inner_self _

/-- The diagonal pairing of a compressed projection is the squared
projected amplitude. -/
theorem re_inner_compressed_starProjection (K : Submodule ℂ V)
    (Y : E' →L[ℂ] V) (x : E') :
    (⟪((Y†) ∘L K.starProjection ∘L Y) x, x⟫).re
      = ‖K.starProjection (Y x)‖ ^ 2 := by
  have h1 : ⟪((Y†) ∘L K.starProjection ∘L Y) x, x⟫
      = ⟪K.starProjection (Y x), Y x⟫ := by
    calc ⟪((Y†) ∘L K.starProjection ∘L Y) x, x⟫
        = ⟪(Y†) (K.starProjection (Y x)), x⟫ := rfl
      _ = ⟪K.starProjection (Y x), Y x⟫ :=
          ContinuousLinearMap.adjoint_inner_left _ _ _
  rw [h1]
  exact re_inner_starProjection_self K (Y x)

/-- Loewner monotonicity of compressed projections along nested
subspaces: `Y^*(P_W - P_U)Y ⪰ 0` for `U ≤ W`. -/
theorem compressed_starProjection_diff_isPositive {U W : Submodule ℂ V}
    (h : U ≤ W) (Y : E' →L[ℂ] V) :
    ((Y†) ∘L W.starProjection ∘L Y
      - (Y†) ∘L U.starProjection ∘L Y).IsPositive := by
  constructor
  · have hW := (compressed_starProjection_isPositive W Y).isSymmetric
    have hU := (compressed_starProjection_isPositive U Y).isSymmetric
    intro x y
    simp only [ContinuousLinearMap.toLinearMap_sub, LinearMap.sub_apply]
    rw [inner_sub_left, inner_sub_right, hW x y, hU x y]
  · intro x
    have hval : ContinuousLinearMap.reApplyInnerSelf
        ((Y†) ∘L W.starProjection ∘L Y
          - (Y†) ∘L U.starProjection ∘L Y) x
        = ‖W.starProjection (Y x)‖ ^ 2 - ‖U.starProjection (Y x)‖ ^ 2 := by
      unfold ContinuousLinearMap.reApplyInnerSelf
      rw [RCLike.re_to_complex, _root_.sub_apply,
        inner_sub_left, Complex.sub_re,
        re_inner_compressed_starProjection W Y x,
        re_inner_compressed_starProjection U Y x]
    rw [hval]
    have hle : U.starProjection (Y x)
        = U.starProjection (W.starProjection (Y x)) := by
      have h2 := congrArg (fun T : V →L[ℂ] V => T (Y x))
        (Submodule.starProjection_comp_starProjection_of_le h)
      exact h2.symm
    have hnorm : ‖U.starProjection (Y x)‖ ≤ ‖W.starProjection (Y x)‖ := by
      rw [hle]
      exact U.norm_starProjection_apply_le _
    have h0 : (0 : ℝ) ≤ ‖U.starProjection (Y x)‖ := norm_nonneg _
    nlinarith

/-! ### `thm:GT-dynamic-source-ancestry`

Rendering (LT.26–LT.31): finite source syntheses `B : E_B → 𝓗`,
`Y : E_Q → 𝓗` for one reflected Hamiltonian `H = H^* ⪰ 0` on a
finite-dimensional Hilbert carrier (the repo's rendering of the reflected
OS quotient); `𝓒_H(B)` is the semigroup-cyclic span, closed since the
carrier is finite-dimensional; finite time banks are `Finset ℝ` and
nested dense banks are increasing sequences of banks whose union is dense
in `[0, ∞)`; Loewner comparisons are `IsPositive` of differences; the
operator-norm convergence (LT.29) is proved through the exact finite-rank
stabilization of the nested bank spans.  The cofinal-limit and dichotomy
clauses of the closing paragraph are rendered by
`dynamic_residual_cofinal_unique` (route-independence of the limit) and
`dynamic_source_dichotomy` (zero, or a positive block certified in
`𝓒_H(B)^⊥`), with the summable-transport bookkeeping carried by the exact
telescoped identity (LT.31)/(DYN.10). -/

/-- **(LT.26)** The source-cyclic projection `P_H^B`. -/
noncomputable def cycProj (H : V →L[ℂ] V) (B : E →L[ℂ] V) : V →L[ℂ] V :=
  (cyc H B).starProjection

/-- The projection `P_B` onto the source range. -/
noncomputable def rangeProj (B : E →L[ℂ] V) : V →L[ℂ] V :=
  B.range.starProjection

/-- The entrance residual `R_ent = Y^*(I - P_B)Y` (LT.27). -/
noncomputable def dynRent (B : E →L[ℂ] V) (Y : E' →L[ℂ] V) : E' →L[ℂ] E' :=
  (Y†) ∘L (1 - rangeProj B) ∘L Y

/-- The promotion residual `R_prom = Y^*(P_H^B - P_B)Y` (LT.28). -/
noncomputable def dynRprom (H : V →L[ℂ] V) (B : E →L[ℂ] V)
    (Y : E' →L[ℂ] V) : E' →L[ℂ] E' :=
  (Y†) ∘L (cycProj H B - rangeProj B) ∘L Y

/-- The dynamic residual `R_dyn = Y^*(I - P_H^B)Y` (LT.28). -/
noncomputable def dynRdyn (H : V →L[ℂ] V) (B : E →L[ℂ] V)
    (Y : E' →L[ℂ] V) : E' →L[ℂ] E' :=
  (Y†) ∘L (1 - cycProj H B) ∘L Y

omit [FiniteDimensional ℂ E] in
/-- **(LT.26, reduction)** The cyclic carrier reduces a self-adjoint
generator: it is invariant together with its orthogonal complement, and
the cyclic projection commutes with `H`. -/
theorem cyc_reduces {H : V →L[ℂ] V} (hH : IsSelfAdjoint H)
    (B : E →L[ℂ] V) :
    (∀ v ∈ cyc H B, H v ∈ cyc H B)
    ∧ (∀ v ∈ (cyc H B)ᗮ, H v ∈ (cyc H B)ᗮ)
    ∧ cycProj H B ∘L H = H ∘L cycProj H B :=
  ⟨fun _ hv => generator_maps_cyc H B hv,
    fun _ hv => generator_maps_cyc_orth hH B hv,
    starProjection_comm_of_invariant H (fun _ hv => generator_maps_cyc H B hv)
      (fun _ hv => generator_maps_cyc_orth hH B hv)⟩

/-- Distribution of a compressed operator sum. -/
theorem compress_add (Y : E' →L[ℂ] V) (A C : V →L[ℂ] V) :
    (Y†) ∘L (A + C) ∘L Y = (Y†) ∘L A ∘L Y + (Y†) ∘L C ∘L Y := by
  ext x
  simp [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]

/-- Distribution of a compressed operator difference. -/
theorem compress_sub (Y : E' →L[ℂ] V) (A C : V →L[ℂ] V) :
    (Y†) ∘L (A - C) ∘L Y = (Y†) ∘L A ∘L Y - (Y†) ∘L C ∘L Y := by
  ext x
  simp [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]

/-- **(LT.27–LT.28)** The exact entrance Pythagoras
`R_ent = R_prom + R_dyn` with both parts positive. -/
theorem dynamic_source_ancestry_split (H : V →L[ℂ] V) (B : E →L[ℂ] V)
    (Y : E' →L[ℂ] V) :
    dynRent B Y = dynRprom H B Y + dynRdyn H B Y
    ∧ (dynRprom H B Y).IsPositive ∧ (dynRdyn H B Y).IsPositive := by
  refine ⟨?_, ?_, ?_⟩
  · have hsplit : (1 : V →L[ℂ] V) - rangeProj B
        = (cycProj H B - rangeProj B) + (1 - cycProj H B) := by abel
    rw [dynRent, hsplit, compress_add]
    rfl
  · have hle : B.range ≤ cyc H B :=
      range_le_bankSpan H B (Set.mem_Ici.mpr le_rfl)
    have h := compressed_starProjection_diff_isPositive hle Y
    have heq : (Y†) ∘L (cyc H B).starProjection ∘L Y
          - (Y†) ∘L B.range.starProjection ∘L Y
        = dynRprom H B Y := by
      rw [dynRprom, cycProj, rangeProj, compress_sub]
    rwa [heq] at h
  · have h := compressed_starProjection_isPositive (cyc H B)ᗮ Y
    have heq : (Y†) ∘L ((cyc H B)ᗮ).starProjection ∘L Y = dynRdyn H B Y := by
      rw [dynRdyn, cycProj, Submodule.starProjection_orthogonal']
    rwa [heq] at h

/-- Orthogonal projections of equal submodules agree. -/
theorem starProjection_congr {K L : Submodule ℂ V} (h : K = L) :
    K.starProjection = L.starProjection := by
  subst h
  rfl

/-- The residual of a finite time bank,
`R_𝐭 = Y^*(I - P_𝐭)Y` with `P_𝐭` the projection onto the span of the
translates `e^{-tH} Ran B`, `t ∈ 𝐭`. -/
noncomputable def bankResidual (H : V →L[ℂ] V) (B : E →L[ℂ] V)
    (Y : E' →L[ℂ] V) (bk : Finset ℝ) : E' →L[ℂ] E' :=
  (Y†) ∘L (1 - (bankSpan H B (bk : Set ℝ)).starProjection) ∘L Y

omit [FiniteDimensional ℂ E] in
/-- Nested bank spans stabilize at the full cyclic carrier once the union
of the banks is dense in `[0, ∞)`. -/
theorem bankSpan_stabilizes (H : V →L[ℂ] V) (B : E →L[ℂ] V)
    (bk : ℕ → Finset ℝ)
    (hpos : ∀ m, ∀ t ∈ bk m, (0 : ℝ) ≤ t)
    (hnested : ∀ m, bk m ⊆ bk (m + 1))
    (hdense : Set.Ici (0 : ℝ) ⊆ closure (⋃ m, (bk m : Set ℝ))) :
    ∃ M, ∀ m, M ≤ m → bankSpan H B (bk m : Set ℝ) = cyc H B := by
  have hmono : Monotone fun m => bankSpan H B (bk m : Set ℝ) :=
    monotone_nat_of_le_succ fun m => bankSpan_mono H B
      (Finset.coe_subset.mpr (hnested m))
  have hmono' : Monotone fun m => (bk m : Set ℝ) :=
    monotone_nat_of_le_succ fun m => Finset.coe_subset.mpr (hnested m)
  obtain ⟨M, hM⟩ := monotone_stabilizes_iff_noetherian.mpr inferInstance
    ⟨fun m => bankSpan H B (bk m : Set ℝ), hmono⟩
  refine ⟨M, fun m hm => ?_⟩
  have hMm : bankSpan H B (bk M : Set ℝ) = bankSpan H B (bk m : Set ℝ) :=
    hM m hm
  -- the stabilized span is the span of the union
  have hcup : bankSpan H B (⋃ m, (bk m : Set ℝ))
      = bankSpan H B (bk M : Set ℝ) := by
    refine le_antisymm ?_ (bankSpan_mono H B (Set.subset_iUnion (fun m => ((bk m : Set ℝ))) M))
    refine Submodule.span_le.mpr ?_
    rintro v ⟨t, ht, u, rfl⟩
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp ht
    have hkM : (bk k : Set ℝ) ⊆ bk (max k M) := hmono' (le_max_left k M)
    have hmem := expH_apply_mem_bankSpan H B (hkM hk) u
    have heq : bankSpan H B (bk M : Set ℝ)
        = bankSpan H B (bk (max k M) : Set ℝ) := hM (max k M) (le_max_right k M)
    rw [← heq] at hmem
    exact hmem
  -- the union is dense, so the stabilized span is the cyclic carrier
  have hsub : (⋃ m, (bk m : Set ℝ)) ⊆ Set.Ici 0 := by
    rintro s hs
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hs
    exact Set.mem_Ici.mpr (hpos k s hk)
  have hcyc := bankSpan_eq_cyc_of_dense H B hsub hdense
  rw [← hMm, ← hcup, hcyc]

/-- **(LT.29)** Along nested dense time banks containing zero the bank
residuals decrease in Loewner order below the entrance residual and
converge in operator norm — indeed stabilize — at the dynamic residual:
`R_ent ⪰ R_{𝐭⁽¹⁾} ⪰ ⋯ → R_dyn`. -/
theorem dynamic_source_bank_residuals (H : V →L[ℂ] V) (B : E →L[ℂ] V)
    (Y : E' →L[ℂ] V) (bk : ℕ → Finset ℝ)
    (h0 : ∀ m, (0 : ℝ) ∈ bk m)
    (hpos : ∀ m, ∀ t ∈ bk m, (0 : ℝ) ≤ t)
    (hnested : ∀ m, bk m ⊆ bk (m + 1))
    (hdense : Set.Ici (0 : ℝ) ⊆ closure (⋃ m, (bk m : Set ℝ))) :
    (∀ m, (dynRent B Y - bankResidual H B Y (bk m)).IsPositive)
    ∧ (∀ m, (bankResidual H B Y (bk m)
        - bankResidual H B Y (bk (m + 1))).IsPositive)
    ∧ (∀ m, (bankResidual H B Y (bk m) - dynRdyn H B Y).IsPositive)
    ∧ Tendsto (fun m => bankResidual H B Y (bk m)) atTop
        (𝓝 (dynRdyn H B Y)) := by
  refine ⟨fun m => ?_, fun m => ?_, fun m => ?_, ?_⟩
  · -- `R_ent ⪰ R_𝐭`: the bank span contains the source range
    have hle : B.range ≤ bankSpan H B (bk m : Set ℝ) :=
      range_le_bankSpan H B (by exact_mod_cast h0 m)
    have h := compressed_starProjection_diff_isPositive hle Y
    have heq : dynRent B Y - bankResidual H B Y (bk m)
        = (Y†) ∘L (bankSpan H B (bk m : Set ℝ)).starProjection ∘L Y
          - (Y†) ∘L B.range.starProjection ∘L Y := by
      rw [dynRent, bankResidual, rangeProj, compress_sub, compress_sub]
      abel
    rwa [← heq] at h
  · -- monotone decrease along nested banks
    have hle : bankSpan H B (bk m : Set ℝ)
        ≤ bankSpan H B (bk (m + 1) : Set ℝ) :=
      bankSpan_mono H B (Finset.coe_subset.mpr (hnested m))
    have h := compressed_starProjection_diff_isPositive hle Y
    have heq : bankResidual H B Y (bk m) - bankResidual H B Y (bk (m + 1))
        = (Y†) ∘L (bankSpan H B (bk (m + 1) : Set ℝ)).starProjection ∘L Y
          - (Y†) ∘L (bankSpan H B (bk m : Set ℝ)).starProjection ∘L Y := by
      rw [bankResidual, bankResidual, compress_sub, compress_sub]
      abel
    rwa [← heq] at h
  · -- every bank residual dominates the dynamic residual
    have hsub : (bk m : Set ℝ) ⊆ Set.Ici 0 := fun t ht =>
      Set.mem_Ici.mpr (hpos m t ht)
    have hle : bankSpan H B (bk m : Set ℝ) ≤ cyc H B :=
      bankSpan_mono H B hsub
    have h := compressed_starProjection_diff_isPositive hle Y
    have heq : bankResidual H B Y (bk m) - dynRdyn H B Y
        = (Y†) ∘L (cyc H B).starProjection ∘L Y
          - (Y†) ∘L (bankSpan H B (bk m : Set ℝ)).starProjection ∘L Y := by
      rw [bankResidual, dynRdyn, cycProj, compress_sub, compress_sub]
      abel
    rwa [← heq] at h
  · -- exact stabilization gives operator-norm convergence
    obtain ⟨M, hM⟩ := bankSpan_stabilizes H B bk hpos hnested hdense
    refine tendsto_atTop_of_eventually_const (i₀ := M) fun m hm => ?_
    rw [bankResidual, starProjection_congr (hM m hm), dynRdyn, cycProj]

/-- **(LT.30)** After the complete cyclic short the residual is orthogonal
to the primitive follower at every delay:
`B^* e^{-tH}(I - P_H^B) Y = 0` and `(P_H^B Y)^* e^{-tH}(I - P_H^B) Y = 0`
(for every real delay `t`; the manuscript uses `t ≥ 0`). -/
theorem cyc_short_delay_orthogonality {H : V →L[ℂ] V}
    (hH : IsSelfAdjoint H) (B : E →L[ℂ] V) (Y : E' →L[ℂ] V) (t : ℝ) :
    (B†) ∘L expH H t ∘L ((1 - cycProj H B) ∘L Y) = 0
    ∧ ((cycProj H B ∘L Y)†) ∘L expH H t ∘L ((1 - cycProj H B) ∘L Y) = 0 := by
  have hcommP : Commute (cycProj H B) H := (cyc_reduces hH B).2.2
  have hcommE : Commute (1 - cycProj H B) (expH H t) :=
    (Commute.one_left (expH H t)).sub_left (expH_commute_of_commute hcommP t)
  -- the semigroup preserves the residual complement
  have hswap : ∀ w : V, expH H t ((1 - cycProj H B) w)
      = (1 - cycProj H B) (expH H t w) := by
    intro w
    have h := congrArg (fun A : V →L[ℂ] V => A w) hcommE.eq
    exact h.symm
  -- the residual complement is killed by `P` and lands in `𝓒ᗮ`
  have hkill : ∀ w : V, cycProj H B ((1 - cycProj H B) w) = 0 := by
    intro w
    have h1 : (1 - cycProj H B) w = w - cycProj H B w := by
      rw [_root_.sub_apply, one_apply_eq_self]
    rw [h1, cycProj, map_sub,
      (cyc H B).starProjection_eq_self_iff.mpr
        ((cyc H B).starProjection_apply_mem w), sub_self]
  have hmemOrth : ∀ w : V, (1 - cycProj H B) w ∈ (cyc H B)ᗮ := by
    intro w
    have h1 : (1 - cycProj H B) w = w - cycProj H B w := by
      rw [_root_.sub_apply, one_apply_eq_self]
    rw [h1, cycProj]
    exact (cyc H B).sub_starProjection_mem_orthogonal w
  constructor
  · ext x
    have h0 : ((B†) ∘L expH H t ∘L ((1 - cycProj H B) ∘L Y)) x
        = (B†) (expH H t ((1 - cycProj H B) (Y x))) := rfl
    rw [h0, hswap]
    have hz : (1 - cycProj H B) (expH H t (Y x)) ∈ (cyc H B)ᗮ :=
      hmemOrth _
    have hinner : ⟪(B†) ((1 - cycProj H B) (expH H t (Y x))),
        (B†) ((1 - cycProj H B) (expH H t (Y x)))⟫ = 0 := by
      rw [ContinuousLinearMap.adjoint_inner_left]
      have hmem : B ((B†) ((1 - cycProj H B) (expH H t (Y x)))) ∈ cyc H B :=
        range_le_bankSpan H B (Set.mem_Ici.mpr le_rfl) ⟨_, rfl⟩
      exact inner_eq_zero_symm.mp
        ((Submodule.mem_orthogonal _ _).mp hz _ hmem)
    have := inner_self_eq_zero.mp hinner
    rw [this]
    rfl
  · -- `(P Y)^*` factorization and the kill identity
    have hPYadj : (cycProj H B ∘L Y)† = (Y†) ∘L cycProj H B := by
      rw [ContinuousLinearMap.adjoint_comp]
      congr 1
      rw [cycProj]
      exact isSelfAdjoint_iff'.mp (isSelfAdjoint_starProjection _)
    rw [hPYadj]
    ext x
    have h0 : (((Y†) ∘L cycProj H B) ∘L expH H t
        ∘L ((1 - cycProj H B) ∘L Y)) x
        = (Y†) (cycProj H B (expH H t ((1 - cycProj H B) (Y x)))) := rfl
    rw [h0, hswap, hkill, map_zero]
    rfl

section TransportAlgebra

variable {V₁ V₂ V₃ V₄ F₁ F₂ F₃ F₄ : Type*}
  [NormedAddCommGroup V₁] [NormedSpace ℂ V₁]
  [NormedAddCommGroup V₂] [NormedSpace ℂ V₂]
  [NormedAddCommGroup V₃] [NormedSpace ℂ V₃]
  [NormedAddCommGroup V₄] [NormedSpace ℂ V₄]
  [NormedAddCommGroup F₁] [NormedSpace ℂ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℂ F₂]
  [NormedAddCommGroup F₃] [NormedSpace ℂ F₃]
  [NormedAddCommGroup F₄] [NormedSpace ℂ F₄]

/-- **(LT.31)/(DYN.9)** The exact one-step transport identity for the
residual writers: `r₂ V - T r₁ = (I - P₂) A^Y - 𝕮^cyc Y₁` with
`A^Y = Y₂ V - T Y₁` and `𝕮^cyc = P₂ T - T P₁`. -/
theorem transport_residual_identity (P₁ : V₁ →L[ℂ] V₁) (P₂ : V₂ →L[ℂ] V₂)
    (T : V₁ →L[ℂ] V₂) (Vc : F₁ →L[ℂ] F₂) (Y₁ : F₁ →L[ℂ] V₁)
    (Y₂ : F₂ →L[ℂ] V₂) :
    ((1 - P₂) ∘L Y₂) ∘L Vc - T ∘L ((1 - P₁) ∘L Y₁)
      = (1 - P₂) ∘L (Y₂ ∘L Vc - T ∘L Y₁) - (P₂ ∘L T - T ∘L P₁) ∘L Y₁ := by
  ext x
  simp only [ContinuousLinearMap.comp_apply, _root_.sub_apply, map_sub,
    one_apply_eq_self]
  abel

/-- **(DYN.10)** The exact four-cutoff dynamic rectangle: with
`D_i = r_{i+1} V_i - T_i r_i`, three adjacent steps telescope to
`r₄V₃V₂V₁ - T₃T₂T₁r₁ = D₃V₂V₁ + T₃D₂V₁ + T₃T₂D₁`. -/
theorem transport_rectangle
    (T₁ : V₁ →L[ℂ] V₂) (T₂ : V₂ →L[ℂ] V₃) (T₃ : V₃ →L[ℂ] V₄)
    (Vc₁ : F₁ →L[ℂ] F₂) (Vc₂ : F₂ →L[ℂ] F₃) (Vc₃ : F₃ →L[ℂ] F₄)
    (r₁ : F₁ →L[ℂ] V₁) (r₂ : F₂ →L[ℂ] V₂) (r₃ : F₃ →L[ℂ] V₃)
    (r₄ : F₄ →L[ℂ] V₄) :
    r₄ ∘L Vc₃ ∘L Vc₂ ∘L Vc₁ - T₃ ∘L T₂ ∘L T₁ ∘L r₁
      = (r₄ ∘L Vc₃ - T₃ ∘L r₃) ∘L Vc₂ ∘L Vc₁
        + T₃ ∘L (r₃ ∘L Vc₂ - T₂ ∘L r₂) ∘L Vc₁
        + T₃ ∘L T₂ ∘L (r₂ ∘L Vc₁ - T₁ ∘L r₁) := by
  ext x
  simp only [ContinuousLinearMap.comp_apply, _root_.sub_apply,
    _root_.add_apply, map_sub]
  abel

end TransportAlgebra

/-- **(record 5, closing clause; DYN.11 route independence)** A convergent
sequence of residual Grams has a unique limit, agreeing along every
cofinal route. -/
theorem dynamic_residual_cofinal_unique {F : Type*} [NormedAddCommGroup F]
    (R : ℕ → F) {L₁ L₂ : F} (φ : ℕ → ℕ) (hφ : Tendsto φ atTop atTop)
    (h₁ : Tendsto R atTop (𝓝 L₁)) (h₂ : Tendsto (R ∘ φ) atTop (𝓝 L₂)) :
    L₁ = L₂ :=
  tendsto_nhds_unique (h₁.comp hφ) h₂

omit [FiniteDimensional ℂ E] in
/-- **(record 5, closing dichotomy)** On the stable transported support
the dynamic residual is either zero — a complete dynamic follower — or it
has a positive block certified by a unit vector in `𝓒_H(B)^⊥`: a nonzero
compressed rank-one lower bound below `R_dyn`. -/
theorem dynamic_source_dichotomy (H : V →L[ℂ] V) (B : E →L[ℂ] V)
    (Y : E' →L[ℂ] V) :
    dynRdyn H B Y = 0
    ∨ ∃ w : V, w ∈ (cyc H B)ᗮ ∧ ‖w‖ = 1 ∧
        (dynRdyn H B Y
          - (Y†) ∘L (Submodule.span ℂ {w}).starProjection ∘L Y).IsPositive ∧
        (Y†) ∘L (Submodule.span ℂ {w}).starProjection ∘L Y ≠ 0 := by
  by_cases hzero : ∀ u : E', (1 - cycProj H B) (Y u) = 0
  · left
    ext u
    have h0 : dynRdyn H B Y u = (Y†) ((1 - cycProj H B) (Y u)) := rfl
    rw [h0, hzero u, map_zero]
    rfl
  · right
    push Not at hzero
    obtain ⟨u, hu⟩ := hzero
    set v : V := (1 - cycProj H B) (Y u) with hv
    have hvOrth : v ∈ (cyc H B)ᗮ := by
      have h1 : v = Y u - cycProj H B (Y u) := by
        rw [hv, _root_.sub_apply, one_apply_eq_self]
      rw [h1, cycProj]
      exact (cyc H B).sub_starProjection_mem_orthogonal (Y u)
    have hvnorm : (0 : ℝ) < ‖v‖ := norm_pos_iff.mpr hu
    set w : V := ((‖v‖⁻¹ : ℝ) : ℂ) • v with hw
    have hwOrth : w ∈ (cyc H B)ᗮ := Submodule.smul_mem _ _ hvOrth
    have hwnorm : ‖w‖ = 1 := by
      rw [hw, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hvnorm), inv_mul_cancel₀ hvnorm.ne']
    have hspan : Submodule.span ℂ {w} ≤ (cyc H B)ᗮ := by
      rw [Submodule.span_singleton_le_iff_mem]
      exact hwOrth
    refine ⟨w, hwOrth, hwnorm, ?_, ?_⟩
    · have h := compressed_starProjection_diff_isPositive hspan Y
      have heq : dynRdyn H B Y
            - (Y†) ∘L (Submodule.span ℂ {w}).starProjection ∘L Y
          = (Y†) ∘L ((cyc H B)ᗮ).starProjection ∘L Y
            - (Y†) ∘L (Submodule.span ℂ {w}).starProjection ∘L Y := by
        rw [dynRdyn, cycProj, Submodule.starProjection_orthogonal']
      rwa [← heq] at h
    · -- the certified block is nonzero: it sees the direction `u`
      intro hzero'
      have hinner : (⟪((Y†) ∘L (Submodule.span ℂ {w}).starProjection ∘L Y) u,
          u⟫).re = ‖(Submodule.span ℂ {w}).starProjection (Y u)‖ ^ 2 :=
        re_inner_compressed_starProjection _ Y u
      rw [hzero'] at hinner
      have hzero2 : ‖(Submodule.span ℂ {w}).starProjection (Y u)‖ ^ 2 = 0 := by
        rw [← hinner]
        simp
      have hPzero : (Submodule.span ℂ {w}).starProjection (Y u) = 0 := by
        have h3 : ‖(Submodule.span ℂ {w}).starProjection (Y u)‖ = 0 :=
          (pow_eq_zero_iff two_ne_zero).mp hzero2
        exact norm_eq_zero.mp h3
      have hproj : (Submodule.span ℂ {w}).starProjection (Y u)
          = ⟪w, Y u⟫ • w :=
        Submodule.starProjection_unit_singleton (𝕜 := ℂ) hwnorm (Y u)
      rw [hproj] at hPzero
      have hwne : w ≠ 0 := by
        intro h0
        rw [h0, norm_zero] at hwnorm
        exact one_ne_zero hwnorm.symm
      have hscal : ⟪w, Y u⟫ = 0 := by
        rcases smul_eq_zero.mp hPzero with h | h
        · exact h
        · exact absurd h hwne
      -- but the pairing is `‖v‖ ≠ 0`
      have hvYu : ⟪v, Y u⟫ = ((‖v‖ : ℝ) : ℂ) ^ 2 := by
        have hsplit : Y u = cycProj H B (Y u) + v := by
          rw [hv, _root_.sub_apply, one_apply_eq_self]
          abel
        have hPmem : cycProj H B (Y u) ∈ cyc H B := by
          rw [cycProj]
          exact (cyc H B).starProjection_apply_mem _
        have h1 : ⟪v, cycProj H B (Y u)⟫ = 0 :=
          inner_eq_zero_symm.mp
            ((Submodule.mem_orthogonal _ _).mp hvOrth _ hPmem)
        rw [hsplit, inner_add_right, h1, zero_add]
        exact inner_self_eq_norm_sq_to_K v
      have hne : ⟪w, Y u⟫ ≠ 0 := by
        rw [hw, inner_smul_left, hvYu, Complex.conj_ofReal]
        apply mul_ne_zero
        · exact_mod_cast inv_ne_zero hvnorm.ne'
        · exact pow_ne_zero 2 (by exact_mod_cast hvnorm.ne')
      exact hne hscal

/-! ### `thm:GT-temporal-Schur-dynamic-source`

Rendering (DYN.1–DYN.6): a finite bank is a family `t : Fin (m+1) → ℝ` of
nonnegative times; the temporal synthesis `𝖶_𝐭` acts on the ℓ²-product
coefficient space `PiLp 2 (fun _ => E_B)`; `G_𝐭 = 𝖶^*𝖶` and `C_𝐭 = 𝖶^*Y`
with the displayed block entries proved as component identities
(`B^*e^{-(t_j+t_k)H}B` and `B^*e^{-t_jH}Y`); `G_𝐭^†` is the repo's
closed-range Moore–Penrose `gramPinv`; the Loewner decrease and norm
convergence along nested dense banks is `dynamic_source_bank_residuals`
together with the range identification `bankW_range`; the four follower
criteria (F1)–(F4) are the iff bundle `temporal_follower_criteria` (with
(F3) attained exactly, at zero error); the dual certificate (DYN.6) is
`dual_dynamic_birth_certificate`. -/

section TemporalSchur

variable {m : ℕ}

/-- **(DYN.1)** The temporal synthesis
`𝖶_𝐭(u₀, …, u_m) = ∑ⱼ e^{-t_jH} B uⱼ` on the ℓ² coefficient bank. -/
noncomputable def bankW (H : V →L[ℂ] V) (B : E →L[ℂ] V)
    (t : Fin (m + 1) → ℝ) : PiLp 2 (fun _ : Fin (m + 1) => E) →L[ℂ] V :=
  ∑ j, (expH H (t j) ∘L B) ∘L PiLp.proj 2 (fun _ : Fin (m + 1) => E) j

omit [FiniteDimensional ℂ E] in
/-- Application formula for the temporal synthesis. -/
theorem bankW_apply (H : V →L[ℂ] V) (B : E →L[ℂ] V)
    (t : Fin (m + 1) → ℝ) (u : PiLp 2 (fun _ : Fin (m + 1) => E)) :
    bankW H B t u = ∑ j, expH H (t j) (B (u j)) := by
  rw [bankW, _root_.sum_apply]
  exact Finset.sum_congr rfl fun j _ => rfl

omit [FiniteDimensional ℂ E] in
/-- The temporal synthesis on a single-coordinate coefficient. -/
theorem bankW_single (H : V →L[ℂ] V) (B : E →L[ℂ] V)
    (t : Fin (m + 1) → ℝ) (j : Fin (m + 1)) (u : E) :
    bankW H B t (PiLp.single 2 j u) = expH H (t j) (B u) := by
  rw [bankW_apply]
  rw [Finset.sum_eq_single j]
  · rw [PiLp.single_eq_same]
  · intro k _ hk
    rw [PiLp.single_eq_of_ne 2 hk, map_zero, map_zero]
  · intro h
    exact absurd (Finset.mem_univ j) h

omit [FiniteDimensional ℂ E] in
/-- The range of the temporal synthesis is the span of the bank
translates of the source range. -/
theorem bankW_range (H : V →L[ℂ] V) (B : E →L[ℂ] V)
    (t : Fin (m + 1) → ℝ) :
    (bankW H B t).range = bankSpan H B (Set.range t) := by
  apply le_antisymm
  · rintro v ⟨u, rfl⟩
    change bankW H B t u ∈ bankSpan H B (Set.range t)
    rw [bankW_apply]
    exact Submodule.sum_mem _ fun j _ =>
      expH_apply_mem_bankSpan H B (Set.mem_range_self j) (u j)
  · refine Submodule.span_le.mpr ?_
    rintro v ⟨s, ⟨j, rfl⟩, u, rfl⟩
    exact LinearMap.mem_range.mpr ⟨PiLp.single 2 j u, bankW_single H B t j u⟩

/-- Component formula for the adjoint of the temporal synthesis:
`(𝖶^* v)_j = B^* e^{-t_jH} v` (DYN.2, row form). -/
theorem bankW_adjoint_apply {H : V →L[ℂ] V} (hH : IsSelfAdjoint H)
    (B : E →L[ℂ] V) (t : Fin (m + 1) → ℝ) (v : V) (j : Fin (m + 1)) :
    ((bankW H B t)†) v j = (B†) (expH H (t j) v) := by
  have key : ∀ e : E, ⟪e, ((bankW H B t)†) v j⟫
      = ⟪e, (B†) (expH H (t j) v)⟫ := by
    intro e
    have h1 : ⟪PiLp.single 2 j e, ((bankW H B t)†) v⟫
        = ⟪e, ((bankW H B t)†) v j⟫ := by
      rw [PiLp.inner_apply]
      rw [Finset.sum_eq_single j]
      · rw [PiLp.single_eq_same]
      · intro k _ hk
        rw [PiLp.single_eq_of_ne 2 hk, inner_zero_left]
      · intro h
        exact absurd (Finset.mem_univ j) h
    have h2 : ⟪PiLp.single 2 j e, ((bankW H B t)†) v⟫
        = ⟪bankW H B t (PiLp.single 2 j e), v⟫ :=
      ContinuousLinearMap.adjoint_inner_right _ _ _
    have h3 : ⟪bankW H B t (PiLp.single 2 j e), v⟫
        = ⟪e, (B†) (expH H (t j) v)⟫ := by
      rw [bankW_single]
      calc ⟪expH H (t j) (B e), v⟫
          = ⟪B e, ((expH H (t j))†) v⟫ := by
            rw [← ContinuousLinearMap.adjoint_inner_right]
        _ = ⟪B e, expH H (t j) v⟫ := by rw [expH_adjoint hH]
        _ = ⟪e, (B†) (expH H (t j) v)⟫ := by
            rw [← ContinuousLinearMap.adjoint_inner_right]
    rw [← h1, h2, h3]
  exact ext_inner_left ℂ key

/-- **(DYN.2, Gram block)** The temporal Gram has the exact delayed
entries `(G_𝐭 u)_j = ∑ₖ B^* e^{-(t_j+t_k)H} B uₖ`. -/
theorem bankGram_apply {H : V →L[ℂ] V} (hH : IsSelfAdjoint H)
    (B : E →L[ℂ] V) (t : Fin (m + 1) → ℝ)
    (u : PiLp 2 (fun _ : Fin (m + 1) => E)) (j : Fin (m + 1)) :
    ClosedRangeMoorePenrose.gram (bankW H B t) u j
      = ∑ k, ((B†) ∘L expH H (t j + t k) ∘L B) (u k) := by
  have h0 : ClosedRangeMoorePenrose.gram (bankW H B t) u
      = ((bankW H B t)†) (bankW H B t u) := rfl
  rw [h0, bankW_adjoint_apply hH B t _ j, bankW_apply, map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h1 : expH H (t j) (expH H (t k) (B (u k)))
      = expH H (t j + t k) (B (u k)) := by
    have h2 := congrArg (fun A : V →L[ℂ] V => A (B (u k)))
      (expH_mul H (t j) (t k))
    exact h2
  rw [h1]
  rfl

omit [FiniteDimensional ℂ E'] in
/-- **(DYN.2, cross block)** The temporal cross Gram has the exact
delayed entries `(C_𝐭 x)_j = B^* e^{-t_jH} Y x`. -/
theorem bankCross_apply {H : V →L[ℂ] V} (hH : IsSelfAdjoint H)
    (B : E →L[ℂ] V) (Y : E' →L[ℂ] V) (t : Fin (m + 1) → ℝ) (x : E')
    (j : Fin (m + 1)) :
    (((bankW H B t)†) ∘L Y) x j = ((B†) ∘L expH H (t j) ∘L Y) x :=
  bankW_adjoint_apply hH B t (Y x) j

/-- The range of a finite-dimensional synthesis is closed. -/
theorem bankW_range_isClosed (H : V →L[ℂ] V) (B : E →L[ℂ] V)
    (t : Fin (m + 1) → ℝ) : IsClosed ((bankW H B t).range : Set V) :=
  (bankW H B t).range.closed_of_finiteDimensional

/-- **(DYN.3)** `P_𝐭 = 𝖶_𝐭 G_𝐭^† 𝖶_𝐭^*` is the orthogonal projection onto
the finite temporal follower range. -/
theorem bank_projection_formula (H : V →L[ℂ] V) (B : E →L[ℂ] V)
    (t : Fin (m + 1) → ℝ) :
    bankW H B t
        ∘L ClosedRangeMoorePenrose.gramPinv (bankW H B t)
          (bankW_range_isClosed H B t)
        ∘L ((bankW H B t)†)
      = ((bankW H B t).range).starProjection := by
  set W := bankW H B t with hW
  set hcl := bankW_range_isClosed H B t
  have h1 : W ∘L ClosedRangeMoorePenrose.gramPinv W hcl ∘L (W†)
      = (W ∘L ClosedRangeMoorePenrose.pinv W hcl)
        ∘L ((W ∘L ClosedRangeMoorePenrose.pinv W hcl)†) := by
    rw [ClosedRangeMoorePenrose.gramPinv, ContinuousLinearMap.adjoint_comp]
    simp only [ContinuousLinearMap.comp_assoc]
  rw [h1, ClosedRangeMoorePenrose.comp_pinv W hcl]
  rw [isSelfAdjoint_iff'.mp (isSelfAdjoint_starProjection W.range)]
  ext v
  change W.range.starProjection (W.range.starProjection v)
    = W.range.starProjection v
  exact W.range.starProjection_eq_self_iff.mpr
    (W.range.starProjection_apply_mem v)

/-- **(DYN.4)** The temporal Schur compiler: the finite bank residual is
the pseudoinverse Schur complement,
`R_𝐭 = Y^*(I - P_𝐭)Y = R - C_𝐭^* G_𝐭^† C_𝐭 ⪰ 0` with `R = Y^*Y`. -/
theorem bank_residual_schur (H : V →L[ℂ] V) (B : E →L[ℂ] V)
    (Y : E' →L[ℂ] V) (t : Fin (m + 1) → ℝ) :
    (Y†) ∘L (1 - ((bankW H B t).range).starProjection) ∘L Y
        = (Y†) ∘L Y
          - ((((bankW H B t)†) ∘L Y)†)
            ∘L ClosedRangeMoorePenrose.gramPinv (bankW H B t)
              (bankW_range_isClosed H B t)
            ∘L (((bankW H B t)†) ∘L Y)
    ∧ ((Y†) ∘L (1 - ((bankW H B t).range).starProjection) ∘L Y).IsPositive := by
  set W := bankW H B t with hW
  set hcl := bankW_range_isClosed H B t
  constructor
  · have hcross := ClosedRangeMoorePenrose.gramPinv_comp_crossGram W Y hcl
    have h1 : ((((W†) ∘L Y)†)
          ∘L ClosedRangeMoorePenrose.gramPinv W hcl ∘L ((W†) ∘L Y))
        = (Y†) ∘L W.range.starProjection ∘L Y := by
      rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint]
      calc ((Y†) ∘L W)
            ∘L ClosedRangeMoorePenrose.gramPinv W hcl ∘L ((W†) ∘L Y)
          = (Y†) ∘L W
            ∘L (ClosedRangeMoorePenrose.gramPinv W hcl ∘L ((W†) ∘L Y)) := by
            rw [ContinuousLinearMap.comp_assoc]
        _ = (Y†) ∘L W ∘L (ClosedRangeMoorePenrose.pinv W hcl ∘L Y) := by
            rw [hcross]
        _ = (Y†) ∘L (W ∘L ClosedRangeMoorePenrose.pinv W hcl) ∘L Y := by
            rw [ContinuousLinearMap.comp_assoc]
        _ = (Y†) ∘L W.range.starProjection ∘L Y := by
            rw [ClosedRangeMoorePenrose.comp_pinv W hcl]
    rw [h1, compress_sub]
    have h2 : (Y†) ∘L (1 : V →L[ℂ] V) ∘L Y = (Y†) ∘L Y := by
      rw [ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp]
    rw [h2]
  · have h := compressed_starProjection_isPositive (W.range)ᗮ Y
    rwa [Submodule.starProjection_orthogonal'] at h

end TemporalSchur

omit [FiniteDimensional ℂ E] in
/-- **(F1 ↔ F2)** The dynamic residual vanishes exactly when the quantum
range lies in the semigroup-cyclic carrier. -/
theorem follower_iff_range_le (H : V →L[ℂ] V) (B : E →L[ℂ] V)
    (Y : E' →L[ℂ] V) :
    dynRdyn H B Y = 0 ↔ Y.range ≤ cyc H B := by
  constructor
  · intro h v hv
    obtain ⟨u, rfl⟩ := hv
    change Y u ∈ cyc H B
    have h1 : (⟪dynRdyn H B Y u, u⟫).re
        = ‖((cyc H B)ᗮ).starProjection (Y u)‖ ^ 2 := by
      have h2 := re_inner_compressed_starProjection ((cyc H B)ᗮ) Y u
      have h3 : dynRdyn H B Y
          = (Y†) ∘L ((cyc H B)ᗮ).starProjection ∘L Y := by
        rw [dynRdyn, cycProj, Submodule.starProjection_orthogonal']
      rw [h3]
      exact h2
    rw [h] at h1
    have h4 : ‖((cyc H B)ᗮ).starProjection (Y u)‖ ^ 2 = 0 := by
      rw [← h1]
      simp
    have h5 : ((cyc H B)ᗮ).starProjection (Y u) = 0 :=
      norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h4)
    have h6 := (Submodule.starProjection_apply_eq_zero_iff
      (K := (cyc H B)ᗮ)).mp h5
    rwa [Submodule.orthogonal_orthogonal] at h6
  · intro h
    ext u
    have h0 : dynRdyn H B Y u = (Y†) ((1 - cycProj H B) (Y u)) := rfl
    have h1 : (1 - cycProj H B) (Y u) = 0 := by
      have h2 : Y u ∈ cyc H B := h ⟨u, rfl⟩
      have h3 : (1 - cycProj H B) (Y u) = Y u - cycProj H B (Y u) := by
        rw [_root_.sub_apply, one_apply_eq_self]
      rw [h3, cycProj, (cyc H B).starProjection_eq_self_iff.mpr h2, sub_self]
    rw [h0, h1, map_zero]
    rfl

omit [FiniteDimensional ℂ E] in
/-- **(F2 → F3, exact form)** A quantum synthesis inside the cyclic
carrier is exactly a finite combination `Y = ∑ⱼ e^{-t_jH} B D_j` of
delayed source writers. -/
theorem follower_exact_representation (H : V →L[ℂ] V) (B : E →L[ℂ] V)
    (Y : E' →L[ℂ] V) (h : Y.range ≤ cyc H B) :
    ∃ (N : ℕ) (ts : Fin N → ℝ) (D : Fin N → (E' →L[ℂ] E)),
      (∀ j, 0 ≤ ts j) ∧ Y = ∑ j, expH H (ts j) ∘L B ∘L D j := by
  classical
  set n := Module.finrank ℂ E' with hn
  set b : Module.Basis (Fin n) ℂ E' := Module.finBasis ℂ E' with hb
  have hrep : ∀ i : Fin n, ∃ (k : ℕ) (c : Fin k → ℂ)
      (ts : Fin k → ℝ) (us : Fin k → E),
      (∀ l, 0 ≤ ts l)
      ∧ Y (b i) = ∑ l, c l • expH H (ts l) (B (us l)) := by
    intro i
    have hmem : Y (b i) ∈ cyc H B := h ⟨b i, rfl⟩
    rw [cyc, bankSpan] at hmem
    obtain ⟨k, c, g, hsum⟩ := mem_span_set'.mp hmem
    choose ts hts us hval using fun l : Fin k => (g l).2
    refine ⟨k, c, ts, us, fun l => Set.mem_Ici.mp (hts l), ?_⟩
    rw [← hsum]
    exact Finset.sum_congr rfl fun l _ => by rw [hval l]
  choose k c ts us hts hval using hrep
  -- assemble the rank-one coefficient writers over the total index
  set D : (Σ i : Fin n, Fin (k i)) → (E' →L[ℂ] E) := fun p =>
    LinearMap.toContinuousLinearMap
      ((b.coord p.1).smulRight (c p.1 p.2 • us p.1 p.2)) with hD
  have hY : Y = ∑ p : Σ i : Fin n, Fin (k i),
      expH H (ts p.1 p.2) ∘L B ∘L D p := by
    apply ContinuousLinearMap.coe_injective
    apply Module.Basis.ext b
    intro i
    change Y (b i) = (∑ p : Σ i : Fin n, Fin (k i),
      expH H (ts p.1 p.2) ∘L B ∘L D p) (b i)
    have hsum2 : (∑ p : Σ i' : Fin n, Fin (k i'),
        expH H (ts p.1 p.2) ∘L B ∘L D p) (b i)
        = ∑ i' : Fin n, ∑ l : Fin (k i'),
          expH H (ts i' l) (B (D ⟨i', l⟩ (b i))) := by
      rw [_root_.sum_apply, ← Finset.univ_sigma_univ, Finset.sum_sigma]
      rfl
    have hcoord : ∀ i' : Fin n, b.coord i' (b i)
        = if i = i' then (1 : ℂ) else 0 := by
      intro i'
      rw [Module.Basis.coord_apply, Module.Basis.repr_self,
        Finsupp.single_apply]
    have hterm0 : ∀ (i' : Fin n) (l : Fin (k i')), i' ≠ i →
        expH H (ts i' l) (B (D ⟨i', l⟩ (b i))) = 0 := by
      intro i' l hne
      have hval0 : D ⟨i', l⟩ (b i) = 0 := by
        have h1 : D ⟨i', l⟩ (b i)
            = b.coord i' (b i) • (c i' l • us i' l) := rfl
        have hif : (if i = i' then (1 : ℂ) else 0) = 0 := by
          simp only [ite_eq_right_iff]
          intro h
          exact absurd h.symm hne
        rw [h1, hcoord i', hif, zero_smul]
      rw [hval0, map_zero, map_zero]
    have hterm1 : ∀ l : Fin (k i),
        expH H (ts i l) (B (D ⟨i, l⟩ (b i)))
        = c i l • expH H (ts i l) (B (us i l)) := by
      intro l
      have h1 : D ⟨i, l⟩ (b i) = b.coord i (b i) • (c i l • us i l) := rfl
      have hif : (if i = i then (1 : ℂ) else 0) = 1 := by simp
      rw [h1, hcoord i, hif, one_smul, map_smul, map_smul]
    rw [hsum2, Finset.sum_eq_single i
      (fun i' _ hne => Finset.sum_eq_zero fun l _ => hterm0 i' l hne)
      (fun h => absurd (Finset.mem_univ i) h)]
    rw [Finset.sum_congr rfl fun l _ => hterm1 l]
    exact hval i
  refine ⟨Fintype.card (Σ i : Fin n, Fin (k i)),
    fun j => ts ((Fintype.equivFin _).symm j).1 ((Fintype.equivFin _).symm j).2,
    fun j => D ((Fintype.equivFin _).symm j), fun j => hts _ _, ?_⟩
  rw [hY]
  exact Fintype.sum_equiv (Fintype.equivFin _) _ _ fun p =>
    congrArg (fun q : (Σ i : Fin n, Fin (k i)) =>
        expH H (ts q.1 q.2) ∘L B ∘L D q)
      (Equiv.symm_apply_apply (Fintype.equivFin _) p).symm

omit [FiniteDimensional ℂ E] in
omit [FiniteDimensional ℂ E'] in
/-- The delayed source writers annihilate the cyclic complement:
`(I - P_H^B)(e^{-tH} B D) = 0` for `t ≥ 0`. -/
theorem residual_kills_delayed_writer (H : V →L[ℂ] V) (B : E →L[ℂ] V)
    {t : ℝ} (ht : 0 ≤ t) (D : E' →L[ℂ] E) :
    (1 - cycProj H B) ∘L (expH H t ∘L B ∘L D) = 0 := by
  ext x
  have hmem : expH H t (B (D x)) ∈ cyc H B :=
    expH_apply_mem_bankSpan H B (Set.mem_Ici.mpr ht) (D x)
  have h0 : ((1 - cycProj H B) ∘L (expH H t ∘L B ∘L D)) x
      = expH H t (B (D x)) - cycProj H B (expH H t (B (D x))) := by
    have h1 : ((1 - cycProj H B) ∘L (expH H t ∘L B ∘L D)) x
        = (1 - cycProj H B) (expH H t (B (D x))) := rfl
    rw [h1, _root_.sub_apply, one_apply_eq_self]
  rw [h0, cycProj, (cyc H B).starProjection_eq_self_iff.mpr hmem, sub_self]
  rfl

omit [FiniteDimensional ℂ E] in
/-- **(F3 → F1)** Uniform approximation by finitely many delayed source
writers forces the dynamic residual to vanish. -/
theorem follower_of_approximation (H : V →L[ℂ] V) (B : E →L[ℂ] V)
    (Y : E' →L[ℂ] V)
    (h : ∀ ε > (0 : ℝ), ∃ (N : ℕ) (ts : Fin N → ℝ)
      (D : Fin N → (E' →L[ℂ] E)), (∀ j, 0 ≤ ts j)
      ∧ ‖Y - ∑ j, expH H (ts j) ∘L B ∘L D j‖ < ε) :
    dynRdyn H B Y = 0 := by
  have hkey : ∀ ε > (0 : ℝ), ‖(1 - cycProj H B) ∘L Y‖ ≤ ε := by
    intro ε hε
    obtain ⟨N, ts, D, hts, hnorm⟩ := h ε hε
    have hkill : (1 - cycProj H B) ∘L (∑ j, expH H (ts j) ∘L B ∘L D j)
        = 0 := by
      ext x
      have h1 : ((1 - cycProj H B)
          ∘L (∑ j, expH H (ts j) ∘L B ∘L D j)) x
          = (1 - cycProj H B) ((∑ j, expH H (ts j) ∘L B ∘L D j) x) := rfl
      rw [h1, _root_.sum_apply, map_sum]
      have h2 : ∀ j ∈ Finset.univ,
          (1 - cycProj H B) ((expH H (ts j) ∘L B ∘L D j) x) = 0 := by
        intro j _
        exact congrArg (fun A : E' →L[ℂ] V => A x)
          (residual_kills_delayed_writer H B (hts j) (D j))
      rw [Finset.sum_eq_zero h2]
      rfl
    have hfactor : (1 - cycProj H B) ∘L Y
        = (1 - cycProj H B) ∘L (Y - ∑ j, expH H (ts j) ∘L B ∘L D j) := by
      rw [ContinuousLinearMap.comp_sub, hkill, sub_zero]
    have hPnorm : ‖(1 : V →L[ℂ] V) - cycProj H B‖ ≤ 1 := by
      have horth := Submodule.starProjection_orthogonal' (cyc H B)
      rw [cycProj, ← horth]
      exact ((cyc H B)ᗮ).starProjection_norm_le
    have hbound : ‖(1 - cycProj H B) ∘L Y‖
        ≤ ‖Y - ∑ j, expH H (ts j) ∘L B ∘L D j‖ := by
      rw [hfactor]
      calc ‖(1 - cycProj H B)
            ∘L (Y - ∑ j, expH H (ts j) ∘L B ∘L D j)‖
          ≤ ‖(1 : V →L[ℂ] V) - cycProj H B‖
            * ‖Y - ∑ j, expH H (ts j) ∘L B ∘L D j‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ 1 * ‖Y - ∑ j, expH H (ts j) ∘L B ∘L D j‖ :=
          mul_le_mul_of_nonneg_right hPnorm (norm_nonneg _)
        _ = ‖Y - ∑ j, expH H (ts j) ∘L B ∘L D j‖ := one_mul _
    exact le_trans hbound hnorm.le
  have h0 : ‖(1 - cycProj H B) ∘L Y‖ = 0 := by
    by_contra hne
    have hpos : 0 < ‖(1 - cycProj H B) ∘L Y‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
    have := hkey (‖(1 - cycProj H B) ∘L Y‖ / 2) (by positivity)
    linarith
  have hzero : (1 - cycProj H B) ∘L Y = 0 := norm_eq_zero.mp h0
  rw [show dynRdyn H B Y = (Y†) ∘L ((1 - cycProj H B) ∘L Y) from rfl,
    hzero, ContinuousLinearMap.comp_zero]

/-- **(F1 ↔ F4)** For every nested dense zero-containing bank family, the
bank residuals tend to zero exactly when the dynamic residual vanishes —
one bank family suffices, and then every bank family complies. -/
theorem follower_iff_bank_tendsto_zero (H : V →L[ℂ] V) (B : E →L[ℂ] V)
    (Y : E' →L[ℂ] V) (bk : ℕ → Finset ℝ)
    (h0 : ∀ m, (0 : ℝ) ∈ bk m)
    (hpos : ∀ m, ∀ t ∈ bk m, (0 : ℝ) ≤ t)
    (hnested : ∀ m, bk m ⊆ bk (m + 1))
    (hdense : Set.Ici (0 : ℝ) ⊆ closure (⋃ m, (bk m : Set ℝ))) :
    Tendsto (fun m => bankResidual H B Y (bk m)) atTop (𝓝 0)
      ↔ dynRdyn H B Y = 0 := by
  have htend := (dynamic_source_bank_residuals H B Y bk h0 hpos hnested
    hdense).2.2.2
  constructor
  · intro hzero
    exact tendsto_nhds_unique htend hzero
  · intro hzero
    rwa [hzero] at htend

omit [FiniteDimensional ℂ E] in
/-- **(DYN.6)** The dual dynamic-birth certificate: a source-visible
isometry into the cyclic complement gives the rigorous two-sided Loewner
bracket `0 ⪯ Y^* Z Z^* Y ⪯ R_dyn`. -/
theorem dual_dynamic_birth_certificate {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    (H : V →L[ℂ] V) (B : E →L[ℂ] V) (Y : E' →L[ℂ] V) (Z : F →L[ℂ] V)
    (hZ : (Z†) ∘L Z = 1) (hrange : Z.range ≤ (cyc H B)ᗮ) :
    ((Y†) ∘L (Z ∘L (Z†)) ∘L Y).IsPositive
    ∧ (dynRdyn H B Y - (Y†) ∘L (Z ∘L (Z†)) ∘L Y).IsPositive := by
  have hZZ : Z ∘L (Z†) = (Z.range).starProjection := by
    ext x
    symm
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    · exact ⟨(Z†) x, rfl⟩
    · intro w hw
      obtain ⟨v, rfl⟩ := hw
      change ⟪x - Z ((Z†) x), Z v⟫ = 0
      rw [inner_sub_left]
      have h1 : ⟪Z ((Z†) x), Z v⟫ = ⟪(Z†) x, (Z†) (Z v)⟫ := by
        rw [← ContinuousLinearMap.adjoint_inner_right]
      have h2 : (Z†) (Z v) = v :=
        congrArg (fun A : F →L[ℂ] F => A v) hZ
      have h3 : ⟪x, Z v⟫ = ⟪(Z†) x, v⟫ :=
        (ContinuousLinearMap.adjoint_inner_left Z v x).symm
      rw [h1, h2, h3, sub_self]
  constructor
  · rw [hZZ]
    exact compressed_starProjection_isPositive _ Y
  · rw [hZZ]
    have h := compressed_starProjection_diff_isPositive hrange Y
    have heq : dynRdyn H B Y - (Y†) ∘L (Z.range).starProjection ∘L Y
        = (Y†) ∘L ((cyc H B)ᗮ).starProjection ∘L Y
          - (Y†) ∘L (Z.range).starProjection ∘L Y := by
      rw [dynRdyn, cycProj, Submodule.starProjection_orthogonal']
    rwa [← heq] at h

/-- **`thm:GT-temporal-Schur-dynamic-source`** (follower criteria bundle):
(F1) `R_dyn = 0`, (F2) `Y(E_Q) ⊆ 𝓒_H(B)`, (F3) approximation (attained
exactly) by finitely many delayed source writers (DYN.5), and (F4) decay
of the residuals of one — hence every — nested dense bank, are
equivalent. -/
theorem temporal_follower_criteria (H : V →L[ℂ] V) (B : E →L[ℂ] V)
    (Y : E' →L[ℂ] V) :
    (dynRdyn H B Y = 0 ↔ Y.range ≤ cyc H B)
    ∧ (dynRdyn H B Y = 0 ↔ ∀ ε > (0 : ℝ), ∃ (N : ℕ) (ts : Fin N → ℝ)
        (D : Fin N → (E' →L[ℂ] E)), (∀ j, 0 ≤ ts j)
        ∧ ‖Y - ∑ j, expH H (ts j) ∘L B ∘L D j‖ < ε)
    ∧ (∀ bk : ℕ → Finset ℝ, (∀ m, (0 : ℝ) ∈ bk m)
        → (∀ m, ∀ t ∈ bk m, (0 : ℝ) ≤ t) → (∀ m, bk m ⊆ bk (m + 1))
        → Set.Ici (0 : ℝ) ⊆ closure (⋃ m, (bk m : Set ℝ))
        → (Tendsto (fun m => bankResidual H B Y (bk m)) atTop (𝓝 0)
          ↔ dynRdyn H B Y = 0)) := by
  refine ⟨follower_iff_range_le H B Y, ⟨?_, follower_of_approximation H B Y⟩,
    fun bk h0 hpos hnested hdense =>
      follower_iff_bank_tendsto_zero H B Y bk h0 hpos hnested hdense⟩
  intro hzero ε hε
  obtain ⟨N, ts, D, hts, hexact⟩ := follower_exact_representation H B Y
    ((follower_iff_range_le H B Y).mp hzero)
  refine ⟨N, ts, D, hts, ?_⟩
  rw [← hexact]
  simpa using hε

/-! ### `prop:GT-dynamic-source-transport-rectangle`

Rendering (DYN.7–DYN.10): the primitive-orbit Duhamel identity (DYN.8) is
proved on the finite-dimensional carriers (every vector is in the common
invariant source graph core) with the genuine Bochner interval integral of
the operator-valued integrand; (DYN.9) is `transport_residual_identity`
(= LT.31) instantiated at the cyclic projections; (DYN.10) is the exact
telescoped rectangle `transport_rectangle`. -/

section DuhamelRectangle

variable {V₂ : Type*} [NormedAddCommGroup V₂] [InnerProductSpace ℂ V₂]
  [FiniteDimensional ℂ V₂]

omit [FiniteDimensional ℂ E] in
/-- Time-continuity of a two-sided semigroup sandwich. -/
theorem duhamel_integrand_continuous (H₁ : V →L[ℂ] V) (H₂ : V₂ →L[ℂ] V₂)
    (R : V →L[ℂ] V₂) (B₁ : E →L[ℂ] V) (t : ℝ) :
    Continuous fun s : ℝ =>
      expH H₂ (t - s) ∘L R ∘L expH H₁ s ∘L B₁ := by
  have h1 : Continuous fun s : ℝ => expH H₂ (t - s) :=
    (expH_continuous H₂).comp (continuous_const.sub continuous_id)
  have h2 : Continuous fun s : ℝ => expH H₁ s ∘L B₁ :=
    (isBoundedBilinearMap_comp.continuous.comp
      ((expH_continuous H₁).prodMk continuous_const))
  have h3 : Continuous fun s : ℝ => R ∘L (expH H₁ s ∘L B₁) :=
    (isBoundedBilinearMap_comp.continuous.comp
      (continuous_const.prodMk h2))
  exact isBoundedBilinearMap_comp.continuous.comp (h1.prodMk h3)

/-- Real-parameter product rule for a time-dependent composition of
operator families over `ℂ`. -/
theorem hasDerivAt_clm_comp_bilinear {G₁ G₂ G₃ : Type*}
    [NormedAddCommGroup G₁] [NormedSpace ℂ G₁]
    [NormedAddCommGroup G₂] [NormedSpace ℂ G₂]
    [NormedAddCommGroup G₃] [NormedSpace ℂ G₃]
    {f : ℝ → G₂ →L[ℂ] G₃} {g : ℝ → G₁ →L[ℂ] G₂}
    {f' : G₂ →L[ℂ] G₃} {g' : G₁ →L[ℂ] G₂} {s : ℝ}
    (hf : HasDerivAt f f' s) (hg : HasDerivAt g g' s) :
    HasDerivAt (fun s => (f s) ∘L (g s)) (f' ∘L g s + f s ∘L g') s := by
  have hb : IsBoundedBilinearMap ℂ
      (fun p : (G₂ →L[ℂ] G₃) × (G₁ →L[ℂ] G₂) => p.1.comp p.2) :=
    isBoundedBilinearMap_comp
  have hcurve : HasDerivAt (fun s => (f s, g s)) (f', g') s := hf.prodMk hg
  have hfd := (hb.hasFDerivAt (f s, g s)).restrictScalars (𝕜 := ℝ)
  have hcomp := hfd.comp_hasDerivAt s hcurve
  have hval : ((hb.deriv (f s, g s)).restrictScalars ℝ) ((f', g'))
      = f' ∘L g s + f s ∘L g' := by
    have h1 : ((hb.deriv (f s, g s)).restrictScalars ℝ) ((f', g'))
        = (f s).comp g' + f'.comp (g s) := rfl
    rw [h1, add_comm]
  rw [hval] at hcomp
  exact hcomp

omit [FiniteDimensional ℂ E] in
/-- The derivative of the Duhamel sandwich
`Φ(s) = e^{-(t-s)H₂} T e^{-sH₁} B₁`. -/
theorem duhamel_sandwich_hasDerivAt (H₁ : V →L[ℂ] V) (H₂ : V₂ →L[ℂ] V₂)
    (T : V →L[ℂ] V₂) (B₁ : E →L[ℂ] V) (t s : ℝ) :
    HasDerivAt (fun s : ℝ => expH H₂ (t - s) ∘L T ∘L expH H₁ s ∘L B₁)
      (expH H₂ (t - s) ∘L (H₂ ∘L T - T ∘L H₁) ∘L expH H₁ s ∘L B₁) s := by
  -- derivative of the left factor
  have hg2 : HasDerivAt (fun s : ℝ => expH H₂ (t - s))
      (expH H₂ (t - s) * H₂) s := by
    have hout := expH_hasDerivAt H₂ (t - s)
    have hin : HasDerivAt (fun s : ℝ => t - s) (-1 : ℝ) s :=
      (hasDerivAt_id s).const_sub t
    have hcomp := HasDerivAt.scomp s hout hin
    have hval : ((-1 : ℝ) • -(expH H₂ (t - s) * H₂))
        = expH H₂ (t - s) * H₂ := by
      rw [neg_one_smul, neg_neg]
    rwa [hval] at hcomp
  -- derivative of the inner right factor
  have hg1 : HasDerivAt (fun s : ℝ => expH H₁ s ∘L B₁)
      ((-(expH H₁ s * H₁)) ∘L B₁) s := by
    have h := hasDerivAt_clm_comp_bilinear (expH_hasDerivAt H₁ s)
      (hasDerivAt_const (𝕜 := ℝ) (x := s) B₁)
    have hval : (-(expH H₁ s * H₁)) ∘L B₁ + expH H₁ s ∘L 0
        = (-(expH H₁ s * H₁)) ∘L B₁ := by
      rw [ContinuousLinearMap.comp_zero, add_zero]
    rwa [hval] at h
  -- derivative of the full right factor
  have hgr : HasDerivAt (fun s : ℝ => T ∘L (expH H₁ s ∘L B₁))
      (T ∘L ((-(expH H₁ s * H₁)) ∘L B₁)) s := by
    have h := hasDerivAt_clm_comp_bilinear
      (hasDerivAt_const (𝕜 := ℝ) (x := s) T) hg1
    have hval : (0 : V →L[ℂ] V₂) ∘L (expH H₁ s ∘L B₁)
          + T ∘L ((-(expH H₁ s * H₁)) ∘L B₁)
        = T ∘L ((-(expH H₁ s * H₁)) ∘L B₁) := by
      rw [ContinuousLinearMap.zero_comp, zero_add]
    rwa [hval] at h
  -- full product rule
  have hprod := hasDerivAt_clm_comp_bilinear hg2 hgr
  have hval : (expH H₂ (t - s) * H₂) ∘L (T ∘L (expH H₁ s ∘L B₁))
        + expH H₂ (t - s) ∘L (T ∘L ((-(expH H₁ s * H₁)) ∘L B₁))
      = expH H₂ (t - s) ∘L (H₂ ∘L T - T ∘L H₁) ∘L expH H₁ s ∘L B₁ := by
    ext x
    have hcomm := congrArg (fun A : V →L[ℂ] V => A (B₁ x))
      (expH_commute H₁ s).eq
    simp only [ContinuousLinearMap.comp_apply, mul_apply_eq_comp,
      _root_.add_apply, _root_.neg_apply, _root_.sub_apply,
      map_sub, map_neg] at hcomm ⊢
    rw [show expH H₁ s (H₁ (B₁ x)) = H₁ (expH H₁ s (B₁ x)) from hcomm.symm]
    abel
  rw [hval] at hprod
  exact hprod

omit [FiniteDimensional ℂ E] [FiniteDimensional ℂ E'] in
/-- **(DYN.8)** The primitive-orbit Duhamel identity: with
`A^B = B₂U - TB₁` and `𝕽^H = H₂T - TH₁`,
`e^{-tH₂}B₂U - Te^{-tH₁}B₁ = e^{-tH₂}A^B - ∫₀ᵗ e^{-(t-s)H₂} 𝕽^H e^{-sH₁} B₁ ds`. -/
theorem primitive_orbit_duhamel (H₁ : V →L[ℂ] V) (H₂ : V₂ →L[ℂ] V₂)
    (T : V →L[ℂ] V₂) (B₁ : E →L[ℂ] V) (B₂ : E' →L[ℂ] V₂) (U : E →L[ℂ] E')
    (t : ℝ) :
    expH H₂ t ∘L B₂ ∘L U - T ∘L (expH H₁ t ∘L B₁)
      = expH H₂ t ∘L (B₂ ∘L U - T ∘L B₁)
        - ∫ s in (0 : ℝ)..t,
            expH H₂ (t - s) ∘L (H₂ ∘L T - T ∘L H₁) ∘L expH H₁ s ∘L B₁ := by
  have hFTC : (∫ s in (0 : ℝ)..t,
        expH H₂ (t - s) ∘L (H₂ ∘L T - T ∘L H₁) ∘L expH H₁ s ∘L B₁)
      = (expH H₂ (t - t) ∘L T ∘L expH H₁ t ∘L B₁)
        - (expH H₂ (t - 0) ∘L T ∘L expH H₁ 0 ∘L B₁) := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun s : ℝ => expH H₂ (t - s) ∘L T ∘L expH H₁ s ∘L B₁)
      (fun s _ => duhamel_sandwich_hasDerivAt H₁ H₂ T B₁ t s) ?_
    exact (duhamel_integrand_continuous H₁ H₂ (H₂ ∘L T - T ∘L H₁) B₁
      t).intervalIntegrable 0 t
  rw [hFTC]
  have h1 : expH H₂ (t - t) ∘L T ∘L expH H₁ t ∘L B₁
      = T ∘L (expH H₁ t ∘L B₁) := by
    rw [sub_self, expH_zero, ContinuousLinearMap.one_def,
      ContinuousLinearMap.id_comp]
  have h2 : expH H₂ (t - 0) ∘L T ∘L expH H₁ 0 ∘L B₁
      = expH H₂ t ∘L T ∘L B₁ := by
    rw [sub_zero, expH_zero, ContinuousLinearMap.one_def,
      ContinuousLinearMap.id_comp]
  rw [h1, h2]
  have h3 : expH H₂ t ∘L (B₂ ∘L U - T ∘L B₁)
      = expH H₂ t ∘L B₂ ∘L U - expH H₂ t ∘L T ∘L B₁ := by
    rw [ContinuousLinearMap.comp_sub, ← ContinuousLinearMap.comp_assoc]
  rw [h3]
  abel

end DuhamelRectangle

end DynamicSourceCluster

/-! ### `thm:GT-source-renewal-lifetime`

Rendering (LT.11–LT.18): the reflected Hamiltonian is a PSD Hermitian
matrix `H` on the finite determining quotient (the triage-sanctioned
finite spectral rendering), `X` an isometric source synthesis.  The
transfer operators are `spectralFunction` heat kernels; first-loss
operators, infinite renewal sums (`HasSum` over `ℕ`), the operator-valued
lifetime measure (a genuine countably additive PSD-matrix-valued set
function built from the exponential-mixture measures
`(volume.restrict (Ioi 0)).withDensity (l·e^{-ls})` with the `{∞}` atom
`X^*P_{ker H}X` carried separately), the survival tails, the extended
`ℝ≥0∞`-valued moment (LT.15) with its `Γ(p+1)X^*H^{-p}X` value on
atom-free directions and value `⊤` on directions carrying a zero-energy
atom, the Laplace transform (LT.16, the `{∞}` endpoint contributing
`e^{-z·∞} = 0`), the exact histogram and mesh-halving identities (LT.17),
and the zero-mass Green bracket (LT.18).  Uniqueness in (LT.13) is the
scalarized statement that a finite Borel measure supported on `[0, ∞)`
with the survival tails (LT.14) is the scalarized lifetime measure. -/

section RenewalLifetime

open MeasureTheory
open scoped NNReal ENNReal

variable {n E : Type*} [Fintype n] [DecidableEq n] [Fintype E] [DecidableEq E]

/-- The heat kernel `e^{-tH}` of a PSD Hermitian matrix. -/
noncomputable def heatK {H : Matrix n n ℂ} (hH : H.PosSemidef) (t : ℝ) :
    Matrix n n ℂ :=
  spectralFunction hH.1 fun l => Real.exp (-(t * l))

/-- The kernel projection `P_{ker H} = 1_{\{0\}}(H)`. -/
noncomputable def kerProj {H : Matrix n n ℂ} (hH : H.PosSemidef) :
    Matrix n n ℂ :=
  spectralFunction hH.1 fun l => if l = 0 then 1 else 0

/-- The index-basis spectral projections of a Hermitian matrix. -/
noncomputable def idxProj {H : Matrix n n ℂ} (hH : H.IsHermitian) (i : n) :
    Matrix n n ℂ :=
  Unitary.conjStarAlgAut ℂ _ hH.eigenvectorUnitary
    (Matrix.diagonal (Pi.single i 1))

/-- Every spectral function is the weighted sum of the index
projections. -/
theorem spectralFunction_eq_sum_idxProj {H : Matrix n n ℂ}
    (hH : H.IsHermitian) (f : ℝ → ℝ) :
    spectralFunction hH f
      = ∑ i, ((f (hH.eigenvalues i) : ℝ) : ℂ) • idxProj hH i := by
  unfold spectralFunction idxProj
  have hterm : ∀ i : n, ((f (hH.eigenvalues i) : ℝ) : ℂ)
      • Unitary.conjStarAlgAut ℂ _ hH.eigenvectorUnitary
        (Matrix.diagonal (Pi.single i 1))
      = Unitary.conjStarAlgAut ℂ _ hH.eigenvectorUnitary
        (((f (hH.eigenvalues i) : ℝ) : ℂ)
          • Matrix.diagonal (Pi.single i 1)) := fun i =>
    (map_smul _ _ _).symm
  rw [Finset.sum_congr rfl fun i _ => hterm i, ← map_sum]
  congr 1
  have h1 : ∀ i : n, ((f (hH.eigenvalues i) : ℝ) : ℂ)
      • Matrix.diagonal (Pi.single i (1 : ℂ))
      = Matrix.diagonal (Pi.single i ((f (hH.eigenvalues i) : ℝ) : ℂ)) := by
    intro i
    ext j l
    by_cases hjl : j = l
    · subst hjl
      by_cases hji : j = i
      · subst hji
        simp
      · simp [Pi.single_eq_of_ne hji]
    · simp [Matrix.diagonal_apply_ne _ hjl]
  rw [Finset.sum_congr rfl fun i _ => h1 i]
  ext j l
  rw [Matrix.sum_apply]
  by_cases hjl : j = l
  · subst hjl
    simp only [Matrix.diagonal_apply_eq]
    rw [Finset.sum_pi_single]
    simp
  · simp [Matrix.diagonal_apply_ne _ hjl]

/-- The index projections are PSD. -/
theorem idxProj_posSemidef {H : Matrix n n ℂ} (hH : H.IsHermitian) (i : n) :
    (idxProj hH i).PosSemidef := by
  unfold idxProj
  rw [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose]
  refine Matrix.PosSemidef.mul_mul_conjTranspose_same ?_ _
  rw [Matrix.posSemidef_diagonal_iff]
  intro j
  by_cases h : j = i
  · subst h
    rw [Pi.single_eq_same]
    exact zero_le_one
  · rw [Pi.single_eq_of_ne h]

/-- The index projections sum to the identity. -/
theorem sum_idxProj {H : Matrix n n ℂ} (hH : H.IsHermitian) :
    ∑ i, idxProj hH i = 1 := by
  have h := spectralFunction_eq_sum_idxProj hH fun _ => 1
  rw [spectralFunction_const hH 1] at h
  simp only [Complex.ofReal_one, one_smul] at h ⊢
  rw [← h]

/-- The constant-one spectral function is the identity. -/
theorem spectralFunction_one {H : Matrix n n ℂ} (hH : H.IsHermitian) :
    spectralFunction hH (fun _ => 1) = 1 := by
  rw [spectralFunction_const hH 1]
  simp

/-- Powers of a spectral function. -/
theorem spectralFunction_pow {H : Matrix n n ℂ} (hH : H.IsHermitian)
    (f : ℝ → ℝ) (m : ℕ) :
    spectralFunction hH f ^ m = spectralFunction hH (fun l => f l ^ m) := by
  induction m with
  | zero =>
    rw [pow_zero]
    have h := spectralFunction_one hH
    rw [← h]
    exact (spectralFunction_congr hH fun i => by rw [pow_zero]).symm
  | succ m ih =>
    rw [pow_succ, ih, spectralFunction_mul]
    exact spectralFunction_congr hH fun i => by rw [pow_succ]

omit [DecidableEq n] [DecidableEq E] in
/-- Compression by an arbitrary synthesis preserves positivity. -/
theorem compressed_posSemidef {M : Matrix n n ℂ} (hM : M.PosSemidef)
    (X : Matrix n E ℂ) : (Xᴴ * M * X).PosSemidef := by
  have h := hM.mul_mul_conjTranspose_same Xᴴ
  rwa [Matrix.conjTranspose_conjTranspose] at h

/-- The source-compressed spectral weights `X^* E_i X`. -/
noncomputable def srcWeight {H : Matrix n n ℂ} (hH : H.IsHermitian)
    (X : Matrix n E ℂ) (i : n) : Matrix E E ℂ :=
  Xᴴ * idxProj hH i * X

omit [DecidableEq E] in
/-- The compressed spectral weights are PSD. -/
theorem srcWeight_posSemidef {H : Matrix n n ℂ} (hH : H.IsHermitian)
    (X : Matrix n E ℂ) (i : n) : (srcWeight hH X i).PosSemidef :=
  compressed_posSemidef (idxProj_posSemidef hH i) X

omit [Fintype E] [DecidableEq E] in
/-- Compression of a spectral function as a weighted sum of the source
weights. -/
theorem compressed_spectral_eq_sum {H : Matrix n n ℂ} (hH : H.IsHermitian)
    (X : Matrix n E ℂ) (f : ℝ → ℝ) :
    Xᴴ * spectralFunction hH f * X
      = ∑ i, ((f (hH.eigenvalues i) : ℝ) : ℂ) • srcWeight hH X i := by
  rw [spectralFunction_eq_sum_idxProj hH f, Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mul_smul, Matrix.smul_mul]
  rfl

omit [Fintype E] [DecidableEq E] in
/-- Master renewal-summation lemma: pointwise `HasSum` of the spectral
symbols (or vanishing of the source weight) gives `HasSum` of the
compressed spectral functions. -/
theorem compressed_spectral_hasSum {H : Matrix n n ℂ} (hH : H.IsHermitian)
    (X : Matrix n E ℂ) (f : ℕ → ℝ → ℝ) (g : ℝ → ℝ)
    (hi : ∀ i, HasSum (fun m => f m (hH.eigenvalues i))
      (g (hH.eigenvalues i)) ∨ srcWeight hH X i = 0) :
    HasSum (fun m => Xᴴ * spectralFunction hH (f m) * X)
      (Xᴴ * spectralFunction hH g * X) := by
  have hterm : ∀ m, Xᴴ * spectralFunction hH (f m) * X
      = ∑ i, ((f m (hH.eigenvalues i) : ℝ) : ℂ) • srcWeight hH X i :=
    fun m => compressed_spectral_eq_sum hH X (f m)
  have htarget := compressed_spectral_eq_sum hH X g
  rw [htarget]
  have hfun : (fun m => Xᴴ * spectralFunction hH (f m) * X)
      = fun m => ∑ i, ((f m (hH.eigenvalues i) : ℝ) : ℂ) • srcWeight hH X i := by
    funext m
    exact hterm m
  rw [hfun]
  refine hasSum_sum fun i _ => ?_
  rcases hi i with h | h
  · have hc : HasSum (fun m => ((f m (hH.eigenvalues i) : ℝ) : ℂ))
        ((g (hH.eigenvalues i) : ℝ) : ℂ) := by
      have := Complex.ofRealCLM.hasSum h
      exact this
    exact hc.smul_const (srcWeight hH X i)
  · rw [h]
    have hz : (fun m => ((f m (hH.eigenvalues i) : ℝ) : ℂ)
        • (0 : Matrix E E ℂ)) = fun _ => 0 := by
      funext m
      rw [smul_zero]
    rw [hz]
    have hz2 : ((g (hH.eigenvalues i) : ℝ) : ℂ) • (0 : Matrix E E ℂ) = 0 :=
      smul_zero _
    rw [hz2]
    exact hasSum_zero

omit [DecidableEq n] [Fintype E] [DecidableEq E] in
/-- Compression distributes over operator differences. -/
theorem compressed_sub (X : Matrix n E ℂ) (A C : Matrix n n ℂ) :
    Xᴴ * (A - C) * X = Xᴴ * A * X - Xᴴ * C * X := by
  rw [Matrix.mul_sub, Matrix.sub_mul]

/-- The delayed transfer bank `M_{h,m} = X^* e^{-mhH} X` (LT.1). -/
noncomputable def transferM {H : Matrix n n ℂ} (hH : H.PosSemidef)
    (X : Matrix n E ℂ) (h : ℝ) (m : ℕ) : Matrix E E ℂ :=
  Xᴴ * heatK hH (m * h) * X

/-- **(LT.11)** The first-loss operators
`𝖯_{h,m} = M_{h,m} - M_{h,m+1}`. -/
noncomputable def firstLoss {H : Matrix n n ℂ} (hH : H.PosSemidef)
    (X : Matrix n E ℂ) (h : ℝ) (m : ℕ) : Matrix E E ℂ :=
  transferM hH X h m - transferM hH X h (m + 1)

/-- **(LT.11)** The escape atom `𝖯_{h,∞} = X^* P_{ker H} X`. -/
noncomputable def lifeAtom {H : Matrix n n ℂ} (hH : H.PosSemidef)
    (X : Matrix n E ℂ) : Matrix E E ℂ :=
  Xᴴ * kerProj hH * X

omit [Fintype E] [DecidableEq E] in
/-- The transfer bank as a compressed spectral function. -/
theorem transferM_eq_spectral {H : Matrix n n ℂ} (hH : H.PosSemidef)
    (X : Matrix n E ℂ) (h : ℝ) (m : ℕ) :
    transferM hH X h m
      = Xᴴ * spectralFunction hH.1 (fun l => Real.exp (-(m * h * l))) * X :=
  rfl

omit [Fintype E] [DecidableEq E] in
/-- The first-loss operators as compressed spectral functions. -/
theorem firstLoss_eq_spectral {H : Matrix n n ℂ} (hH : H.PosSemidef)
    (X : Matrix n E ℂ) (h : ℝ) (m : ℕ) :
    firstLoss hH X h m
      = Xᴴ * spectralFunction hH.1 (fun l =>
          Real.exp (-(m * h * l)) - Real.exp (-((m + 1) * h * l))) * X := by
  rw [firstLoss, transferM_eq_spectral, transferM_eq_spectral,
    ← compressed_sub, spectralFunction_sub]
  push_cast
  rfl

omit [Fintype E] [DecidableEq E] in
/-- **(LT.11, product display)**
`𝖯_{h,m} = X^* T_h^m (I - T_h) X`. -/
theorem firstLoss_eq_transfer_product {H : Matrix n n ℂ}
    (hH : H.PosSemidef) (X : Matrix n E ℂ) (h : ℝ) (m : ℕ) :
    firstLoss hH X h m
      = Xᴴ * (heatK hH h ^ m * (1 - heatK hH h)) * X := by
  rw [firstLoss_eq_spectral]
  congr 1
  congr 1
  rw [heatK, spectralFunction_pow]
  have hone : (1 : Matrix n n ℂ) = spectralFunction hH.1 fun _ => 1 :=
    (spectralFunction_one hH.1).symm
  rw [hone, ← spectralFunction_sub, spectralFunction_mul]
  refine spectralFunction_congr hH.1 fun i => ?_
  rw [← Real.exp_nat_mul]
  have h1 : -((m : ℝ) + 1) * h * hH.1.eigenvalues i
      = (m : ℝ) * (-(h * hH.1.eigenvalues i)) + -(h * hH.1.eigenvalues i) := by
    ring
  have h2 : -((m : ℝ)) * h * hH.1.eigenvalues i
      = (m : ℝ) * -(h * hH.1.eigenvalues i) := by
    ring
  rw [show (-(↑m * h * hH.1.eigenvalues i)) = (m : ℝ) * -(h * hH.1.eigenvalues i)
      from by ring,
    show (-((↑m + 1) * h * hH.1.eigenvalues i))
      = (m : ℝ) * (-(h * hH.1.eigenvalues i)) + -(h * hH.1.eigenvalues i)
      from by ring,
    Real.exp_add]
  ring

omit [DecidableEq E] in
/-- **(LT.11, positivity)** `𝖯_{h,m} ⪰ 0` for `h ≥ 0`. -/
theorem firstLoss_posSemidef {H : Matrix n n ℂ} (hH : H.PosSemidef)
    (X : Matrix n E ℂ) {h : ℝ} (hh : 0 ≤ h) (m : ℕ) :
    (firstLoss hH X h m).PosSemidef := by
  rw [firstLoss_eq_spectral]
  refine compressed_posSemidef (spectralFunction_posSemidef hH.1 _
    fun i => ?_) X
  have hev := hH.eigenvalues_nonneg i
  have h1 : (m : ℝ) * h * hH.1.eigenvalues i
      ≤ ((m : ℝ) + 1) * h * hH.1.eigenvalues i := by
    have : (0 : ℝ) ≤ h * hH.1.eigenvalues i := mul_nonneg hh hev
    nlinarith
  have h2 := Real.exp_le_exp.mpr (neg_le_neg h1)
  linarith

omit [DecidableEq E] in
/-- The escape atom is PSD. -/
theorem lifeAtom_posSemidef {H : Matrix n n ℂ} (hH : H.PosSemidef)
    (X : Matrix n E ℂ) : (lifeAtom hH X).PosSemidef := by
  refine compressed_posSemidef (spectralFunction_posSemidef hH.1 _
    fun i => ?_) X
  split_ifs <;> norm_num

omit [Fintype E] in
/-- **(LT.12, completeness)** The first-loss law is complete:
`∑_{m≥0} 𝖯_{h,m} + 𝖯_{h,∞} = I_E` for `h > 0` and isometric `X`. -/
theorem renewal_law_complete {H : Matrix n n ℂ} (hH : H.PosSemidef)
    {X : Matrix n E ℂ} (hX : Xᴴ * X = 1) {h : ℝ} (hh : 0 < h) :
    HasSum (fun m => firstLoss hH X h m) (1 - lifeAtom hH X) := by
  have hfun : (fun m => firstLoss hH X h m) = fun m : ℕ =>
      Xᴴ * spectralFunction hH.1 (fun l =>
        Real.exp (-(m * h * l)) - Real.exp (-((m + 1) * h * l))) * X := by
    funext m
    exact firstLoss_eq_spectral hH X h m
  rw [hfun]
  have hhyp : ∀ i, HasSum (fun m : ℕ =>
      Real.exp (-(m * h * hH.1.eigenvalues i))
        - Real.exp (-((m + 1) * h * hH.1.eigenvalues i)))
      ((fun l => if l = 0 then (0 : ℝ) else 1) (hH.1.eigenvalues i))
      ∨ srcWeight hH.1 X i = 0 := by
    intro i
    left
    set l := hH.1.eigenvalues i with hl
    have hev : 0 ≤ l := hH.eigenvalues_nonneg i
    by_cases hzero : l = 0
    · rw [hzero]
      have hz : (fun m : ℕ => Real.exp (-(m * h * 0))
          - Real.exp (-((m + 1) * h * 0))) = fun _ => (0 : ℝ) := by
        funext m
        norm_num
      rw [hz]
      simp
    · have hpos : 0 < l := lt_of_le_of_ne hev (Ne.symm hzero)
      have hr1 : Real.exp (-(h * l)) < 1 := by
        rw [Real.exp_lt_one_iff]
        have hhl : 0 < h * l := mul_pos hh hpos
        linarith
      have hr0 : 0 ≤ Real.exp (-(h * l)) := (Real.exp_pos _).le
      have hgeom := hasSum_geometric_of_lt_one hr0 hr1
      have hmul := hgeom.mul_right (1 - Real.exp (-(h * l)))
      have hval : (1 - Real.exp (-(h * l)))⁻¹ * (1 - Real.exp (-(h * l)))
          = 1 := inv_mul_cancel₀ (by linarith)
      rw [hval] at hmul
      have hshape : (fun m : ℕ => Real.exp (-(h * l)) ^ m
          * (1 - Real.exp (-(h * l))))
          = fun m : ℕ => Real.exp (-(m * h * l))
            - Real.exp (-((m + 1) * h * l)) := by
        funext m
        rw [← Real.exp_nat_mul, mul_sub, mul_one, ← Real.exp_add]
        rw [show (m : ℝ) * -(h * l) = -(m * h * l) from by ring]
        rw [show (-(m * h * l) + -(h * l)) = -(((m : ℝ) + 1) * h * l)
          from by ring]
      rw [hshape] at hmul
      rw [show ((fun l => if l = 0 then (0 : ℝ) else 1) l) = 1
        from by simp [hzero]]
      exact hmul
  have hmain := compressed_spectral_hasSum hH.1 X
    (f := fun m l => Real.exp (-(m * h * l)) - Real.exp (-((m + 1) * h * l)))
    (g := fun l => if l = 0 then 0 else 1) hhyp
  have htarget : Xᴴ * spectralFunction hH.1 (fun l =>
      if l = 0 then 0 else 1) * X = 1 - lifeAtom hH X := by
    have hsplit : spectralFunction hH.1 (fun l => if l = 0 then (0 : ℝ) else 1)
        = spectralFunction hH.1 (fun _ => 1) - kerProj hH := by
      rw [kerProj, ← spectralFunction_sub]
      refine spectralFunction_congr hH.1 fun i => ?_
      split_ifs <;> ring
    rw [hsplit, spectralFunction_one, compressed_sub, lifeAtom]
    congr 1
    rw [Matrix.mul_one, hX]
  rwa [htarget] at hmain

omit [Fintype E] [DecidableEq E] in
/-- **(LT.12, renewal tails)** Every delayed Gram is the escape atom plus
its renewal tail: `M_{h,m} = 𝖯_{h,∞} + ∑_{j≥m} 𝖯_{h,j}` (for `h > 0`). -/
theorem renewal_tail_complete {H : Matrix n n ℂ} (hH : H.PosSemidef)
    (X : Matrix n E ℂ) {h : ℝ} (hh : 0 < h) (m : ℕ) :
    HasSum (fun j => firstLoss hH X h (m + j))
      (transferM hH X h m - lifeAtom hH X) := by
  have hfun : (fun j => firstLoss hH X h (m + j)) = fun j : ℕ =>
      Xᴴ * spectralFunction hH.1 (fun l =>
        Real.exp (-((m + j) * h * l))
          - Real.exp (-((m + j + 1) * h * l))) * X := by
    funext j
    have hstep := firstLoss_eq_spectral hH X h (m + j)
    rw [hstep]
    congr 1
    congr 1
    refine spectralFunction_congr hH.1 fun i => ?_
    push_cast
    ring_nf
  rw [hfun]
  have hhyp : ∀ i, HasSum (fun j : ℕ =>
      Real.exp (-((m + j) * h * hH.1.eigenvalues i))
        - Real.exp (-((m + j + 1) * h * hH.1.eigenvalues i)))
      ((fun l => Real.exp (-(m * h * l)) - (if l = 0 then (1 : ℝ) else 0))
        (hH.1.eigenvalues i))
      ∨ srcWeight hH.1 X i = 0 := by
    intro i
    left
    set l := hH.1.eigenvalues i with hl
    have hev : 0 ≤ l := hH.eigenvalues_nonneg i
    by_cases hzero : l = 0
    · rw [hzero]
      have hz : (fun j : ℕ => Real.exp (-((m + j) * h * 0))
          - Real.exp (-((m + j + 1) * h * 0))) = fun _ => (0 : ℝ) := by
        funext j
        norm_num
      rw [hz]
      rw [show ((fun l => Real.exp (-(m * h * l))
          - (if l = 0 then (1 : ℝ) else 0)) 0) = 0 from by norm_num]
      exact hasSum_zero
    · have hpos : 0 < l := lt_of_le_of_ne hev (Ne.symm hzero)
      have hr1 : Real.exp (-(h * l)) < 1 := by
        rw [Real.exp_lt_one_iff]
        have hhl : 0 < h * l := mul_pos hh hpos
        linarith
      have hr0 : 0 ≤ Real.exp (-(h * l)) := (Real.exp_pos _).le
      have hgeom := hasSum_geometric_of_lt_one hr0 hr1
      have hmul := hgeom.mul_right
        (Real.exp (-(m * h * l)) * (1 - Real.exp (-(h * l))))
      have hval : (1 - Real.exp (-(h * l)))⁻¹
          * (Real.exp (-(m * h * l)) * (1 - Real.exp (-(h * l))))
          = Real.exp (-(m * h * l)) := by
        have hne : (1 : ℝ) - Real.exp (-(h * l)) ≠ 0 := by linarith
        field_simp
      rw [hval] at hmul
      have hshape : (fun j : ℕ => Real.exp (-(h * l)) ^ j
          * (Real.exp (-(m * h * l)) * (1 - Real.exp (-(h * l)))))
          = fun j : ℕ => Real.exp (-((m + j) * h * l))
            - Real.exp (-((m + j + 1) * h * l)) := by
        funext j
        rw [← Real.exp_nat_mul]
        have e1 : Real.exp ((j : ℝ) * -(h * l)) * Real.exp (-(m * h * l))
            = Real.exp (-(((m : ℝ) + j) * h * l)) := by
          rw [← Real.exp_add]
          congr 1
          ring
        have e2 : Real.exp ((j : ℝ) * -(h * l))
              * (Real.exp (-(m * h * l)) * Real.exp (-(h * l)))
            = Real.exp (-(((m : ℝ) + j + 1) * h * l)) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
        calc Real.exp ((j : ℝ) * -(h * l))
              * (Real.exp (-(m * h * l)) * (1 - Real.exp (-(h * l))))
            = Real.exp ((j : ℝ) * -(h * l)) * Real.exp (-(m * h * l))
              - Real.exp ((j : ℝ) * -(h * l))
                * (Real.exp (-(m * h * l)) * Real.exp (-(h * l))) := by
              ring
          _ = Real.exp (-(((m : ℝ) + j) * h * l))
              - Real.exp (-(((m : ℝ) + j + 1) * h * l)) := by
              rw [e1, e2]
      rw [hshape] at hmul
      rw [show ((fun l => Real.exp (-(m * h * l))
          - (if l = 0 then (1 : ℝ) else 0)) l) = Real.exp (-(m * h * l))
        from by simp [hzero]]
      exact hmul
  have hmain := compressed_spectral_hasSum hH.1 X
    (f := fun j l => Real.exp (-((m + j) * h * l))
      - Real.exp (-((m + j + 1) * h * l)))
    (g := fun l => Real.exp (-(m * h * l)) - (if l = 0 then 1 else 0)) hhyp
  have htarget : Xᴴ * spectralFunction hH.1 (fun l =>
      Real.exp (-(m * h * l)) - (if l = 0 then 1 else 0)) * X
      = transferM hH X h m - lifeAtom hH X := by
    rw [show (fun l => Real.exp (-(m * h * l)) - (if l = 0 then (1 : ℝ) else 0))
        = fun l => (fun l => Real.exp (-((m : ℝ) * h * l))) l
          - (fun l => if l = 0 then (1 : ℝ) else 0) l from rfl,
      spectralFunction_sub, compressed_sub]
    rfl
  rwa [htarget] at hmain

/-- The exponential lifetime component of rate `l` (LT.13): the measure
`λ e^{-λ s} ds` on `(0, ∞)` (the zero measure at rate `0`). -/
noncomputable def expLife (l : ℝ) : Measure ℝ :=
  (volume.restrict (Set.Ioi 0)).withDensity
    fun s => ENNReal.ofReal (l * Real.exp (-(l * s)))

/-- Evaluation of the exponential component on a measurable set. -/
theorem expLife_apply (l : ℝ) {A : Set ℝ} (hA : MeasurableSet A) :
    expLife l A
      = ∫⁻ s in A ∩ Set.Ioi 0, ENNReal.ofReal (l * Real.exp (-(l * s))) := by
  rw [expLife, withDensity_apply _ hA, Measure.restrict_restrict hA]

/-- The exponential component of a nonnegative rate on a tail `[t, ∞)`,
`t ≥ 0`, has mass `e^{-lt}` (`0` at rate `0`). -/
theorem expLife_tail {l : ℝ} (hl : 0 ≤ l) {t : ℝ} (ht : 0 ≤ t) :
    expLife l (Set.Ici t)
      = ENNReal.ofReal (if l = 0 then 0 else Real.exp (-(l * t))) := by
  by_cases hzero : l = 0
  · subst hzero
    rw [expLife]
    have hd : (fun s : ℝ => ENNReal.ofReal (0 * Real.exp (-(0 * s))))
        = (0 : ℝ → ℝ≥0∞) := by
      funext s
      norm_num
    rw [hd, withDensity_zero]
    simp
  · have hlpos : 0 < l := lt_of_le_of_ne hl (Ne.symm hzero)
    rw [expLife_apply l measurableSet_Ici]
    have hae : (Set.Ici t ∩ Set.Ioi 0 : Set ℝ) =ᵐ[volume] Set.Ioi t := by
      rw [MeasureTheory.ae_eq_set]
      constructor
      · refine measure_mono_null ?_ (measure_singleton t)
        rintro s ⟨⟨hs1, _⟩, hs2⟩
        have hst : s = t := le_antisymm (not_lt.mp hs2) hs1
        exact hst ▸ rfl
      · have h2 : (Set.Ioi t : Set ℝ) \ (Set.Ici t ∩ Set.Ioi 0) = ∅ := by
          ext s
          constructor
          · rintro ⟨hs, hns⟩
            have hts : t < s := hs
            exact absurd (Set.mem_inter (Set.mem_Ici.mpr hts.le)
              (Set.mem_Ioi.mpr (lt_of_le_of_lt ht hts))) hns
          · intro h
            exact absurd h (Set.notMem_empty s)
        rw [h2]
        exact measure_empty
    rw [setLIntegral_congr hae]
    have hshape : (fun s => Real.exp (-(l * s))) = fun s => Real.exp (-l * s) := by
      funext s
      ring_nf
    have hInt : MeasureTheory.IntegrableOn
        (fun s => l * Real.exp (-(l * s))) (Set.Ioi t) := by
      have h0 := exp_neg_integrableOn_Ioi t hlpos
      rw [← hshape] at h0
      exact h0.const_mul l
    have hnn : (0 : ℝ → ℝ) ≤ᵐ[volume.restrict (Set.Ioi t)]
        fun s => l * Real.exp (-(l * s)) := by
      refine Filter.Eventually.of_forall fun s => ?_
      have := Real.exp_pos (-(l * s))
      positivity
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt hnn]
    congr 1
    rw [MeasureTheory.integral_const_mul]
    have hval : ∫ s in Set.Ioi t, Real.exp (-(l * s))
        = Real.exp (-(l * t)) / l := by
      rw [hshape, integral_exp_mul_Ioi (by linarith : -l < 0) t]
      rw [show (-l * t) = -(l * t) from by ring]
      field_simp
    rw [hval]
    rw [show (if l = 0 then (0 : ℝ) else Real.exp (-(l * t)))
      = Real.exp (-(l * t)) from by simp [hzero]]
    field_simp

/-- The exponential component is a (sub-probability) finite measure. -/
theorem expLife_finite {l : ℝ} (hl : 0 ≤ l) (A : Set ℝ) :
    expLife l A ≤ 1 := by
  have h1 : expLife l A ≤ expLife l Set.univ := measure_mono (Set.subset_univ A)
  have h2 : (Set.univ : Set ℝ) = Set.Ici (0 : ℝ) ∪ Set.Iio 0 := by
    ext s
    simp only [Set.mem_univ, Set.mem_union, Set.mem_Ici, Set.mem_Iio,
      true_iff]
    exact le_or_gt 0 s
  have h3 : expLife l (Set.Iio 0) = 0 := by
    rw [expLife_apply l measurableSet_Iio]
    have hempty : (Set.Iio 0 ∩ Set.Ioi 0 : Set ℝ) = ∅ := by
      ext s
      simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioi,
        Set.mem_empty_iff_false, iff_false, not_and]
      intro h1 h2
      exact absurd h2 (not_lt.mpr h1.le)
    rw [hempty]
    simp
  have h4 : expLife l Set.univ ≤ expLife l (Set.Ici 0) + expLife l (Set.Iio 0) := by
    rw [h2]
    exact measure_union_le _ _
  rw [h3, add_zero, expLife_tail hl le_rfl] at h4
  refine le_trans h1 (le_trans h4 ?_)
  split_ifs with hzero
  · simp
  · rw [mul_zero, neg_zero, Real.exp_zero]
    simp

/-- **(LT.13)** The operator-valued lifetime measure (finite part): the
exponential mixture `∫ λe^{-λs} ds ν(dλ)` of the source spectral
measure. -/
noncomputable def lifeMeasure {H : Matrix n n ℂ} (hH : H.PosSemidef)
    (X : Matrix n E ℂ) (A : Set ℝ) : Matrix E E ℂ :=
  ∑ i, (((expLife (hH.1.eigenvalues i)) A).toReal : ℂ)
    • srcWeight hH.1 X i

omit [DecidableEq E] in
/-- The lifetime measure is PSD on every set. -/
theorem lifeMeasure_posSemidef {H : Matrix n n ℂ} (hH : H.PosSemidef)
    (X : Matrix n E ℂ) (A : Set ℝ) : (lifeMeasure hH X A).PosSemidef := by
  refine Matrix.posSemidef_sum _ fun i _ => ?_
  exact posSemidef_real_smul (srcWeight_posSemidef hH.1 X i)
    ENNReal.toReal_nonneg

omit [Fintype E] [DecidableEq E] in
/-- Assembly of pointwise scalar `HasSum`s into the weighted source
expansion. -/
theorem srcWeight_hasSum {H : Matrix n n ℂ} (hH : H.IsHermitian)
    (X : Matrix n E ℂ) {c : ℕ → n → ℝ} {d : n → ℝ}
    (h : ∀ i, HasSum (fun k => c k i) (d i)) :
    HasSum (fun k => ∑ i, ((c k i : ℝ) : ℂ) • srcWeight hH X i)
      (∑ i, ((d i : ℝ) : ℂ) • srcWeight hH X i) := by
  refine hasSum_sum fun i _ => ?_
  exact (Complex.ofRealCLM.hasSum (h i)).smul_const (srcWeight hH X i)

omit [Fintype E] [DecidableEq E] in
/-- **(LT.13, countable additivity)** The lifetime measure is countably
additive: for pairwise disjoint measurable bins the bin masses sum to the
mass of the union. -/
theorem lifeMeasure_hasSum_iUnion {H : Matrix n n ℂ} (hH : H.PosSemidef)
    (X : Matrix n E ℂ) (A : ℕ → Set ℝ) (hmeas : ∀ k, MeasurableSet (A k))
    (hdisj : Pairwise (Function.onFun Disjoint A)) :
    HasSum (fun k => lifeMeasure hH X (A k))
      (lifeMeasure hH X (⋃ k, A k)) := by
  refine srcWeight_hasSum hH.1 X fun i => ?_
  set μ := expLife (hH.1.eigenvalues i) with hμ
  have hl : 0 ≤ hH.1.eigenvalues i := hH.eigenvalues_nonneg i
  have hfin : ∀ B : Set ℝ, μ B ≠ ⊤ := fun B =>
    (lt_of_le_of_lt (expLife_finite hl B) ENNReal.one_lt_top).ne
  have htsum : ∑' k, μ (A k) = μ (⋃ k, A k) :=
    (measure_iUnion hdisj hmeas).symm
  have hsummable : Summable fun k => (μ (A k)).toReal :=
    ENNReal.summable_toReal (htsum ▸ hfin _)
  refine hsummable.hasSum_iff.mpr ?_
  rw [← htsum]
  exact (ENNReal.tsum_toReal_eq fun k => hfin (A k)).symm

/-- Total mass of the exponential component. -/
theorem expLife_univ {l : ℝ} (hl : 0 ≤ l) :
    expLife l Set.univ = ENNReal.ofReal (if l = 0 then 0 else 1) := by
  have h2 : (Set.univ : Set ℝ) = Set.Ici (0 : ℝ) ∪ Set.Iio 0 := by
    ext s
    simp only [Set.mem_univ, Set.mem_union, Set.mem_Ici, Set.mem_Iio,
      true_iff]
    exact le_or_gt 0 s
  have h3 : expLife l (Set.Iio 0) = 0 := by
    rw [expLife_apply l measurableSet_Iio]
    have hempty : (Set.Iio 0 ∩ Set.Ioi 0 : Set ℝ) = ∅ := by
      ext s
      simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioi,
        Set.mem_empty_iff_false, iff_false, not_and]
      intro h1 h2
      exact absurd h2 (not_lt.mpr h1.le)
    rw [hempty]
    simp
  have h4 : expLife l Set.univ = expLife l (Set.Ici 0) + expLife l (Set.Iio 0) := by
    rw [h2]
    refine measure_union ?_ measurableSet_Iio
    refine Set.disjoint_left.mpr fun s hs1 hs2 => ?_
    have h1 : (0 : ℝ) ≤ s := hs1
    have h2 : s < 0 := hs2
    linarith
  rw [h4, h3, add_zero, expLife_tail hl le_rfl]
  congr 1
  split_ifs with hzero
  · rfl
  · rw [mul_zero, neg_zero, Real.exp_zero]

omit [Fintype E] [DecidableEq E] in
/-- Sum of the source weights: `∑ᵢ X^* E_i X = X^* X`. -/
theorem sum_srcWeight {H : Matrix n n ℂ} (hH : H.IsHermitian)
    (X : Matrix n E ℂ) : ∑ i, srcWeight hH X i = Xᴴ * X := by
  have h := sum_idxProj hH
  calc ∑ i, srcWeight hH X i = Xᴴ * (∑ i, idxProj hH i) * X := by
        rw [Matrix.mul_sum, Matrix.sum_mul]
        rfl
    _ = Xᴴ * X := by rw [h, Matrix.mul_one]

omit [Fintype E] [DecidableEq E] in
/-- The escape atom as a weighted source expansion. -/
theorem lifeAtom_eq_sum {H : Matrix n n ℂ} (hH : H.PosSemidef)
    (X : Matrix n E ℂ) :
    lifeAtom hH X = ∑ i, (((if hH.1.eigenvalues i = 0 then (1 : ℝ) else 0)
      : ℝ) : ℂ) • srcWeight hH.1 X i :=
  compressed_spectral_eq_sum hH.1 X _

omit [Fintype E] in
/-- **(LT.12/LT.13, total mass)** The lifetime law is an operator-valued
probability law: `Λ([0,∞)) + Λ({∞}) = I_E`. -/
theorem lifeMeasure_total {H : Matrix n n ℂ} (hH : H.PosSemidef)
    {X : Matrix n E ℂ} (hX : Xᴴ * X = 1) :
    lifeMeasure hH X Set.univ + lifeAtom hH X = 1 := by
  rw [lifeMeasure, lifeAtom_eq_sum, ← Finset.sum_add_distrib]
  have hterm : ∀ i : n, (((expLife (hH.1.eigenvalues i)) Set.univ).toReal : ℂ)
        • srcWeight hH.1 X i
      + (((if hH.1.eigenvalues i = 0 then (1 : ℝ) else 0) : ℝ) : ℂ)
        • srcWeight hH.1 X i
      = srcWeight hH.1 X i := by
    intro i
    have hl : 0 ≤ hH.1.eigenvalues i := hH.eigenvalues_nonneg i
    rw [expLife_univ hl, ENNReal.toReal_ofReal (by split_ifs <;> norm_num)]
    rw [← add_smul]
    have hval : (((if hH.1.eigenvalues i = 0 then (0 : ℝ) else 1) : ℝ) : ℂ)
        + (((if hH.1.eigenvalues i = 0 then (1 : ℝ) else 0) : ℝ) : ℂ)
        = 1 := by
      split_ifs <;> norm_num
    rw [hval, one_smul]
  rw [Finset.sum_congr rfl fun i _ => hterm i, sum_srcWeight, hX]

omit [Fintype E] [DecidableEq E] in
/-- **(LT.14)** The survival identity `Λ([t,∞]) = X^* e^{-tH} X`:
finite tail plus the `{∞}` atom. -/
theorem lifeMeasure_tail {H : Matrix n n ℂ} (hH : H.PosSemidef)
    (X : Matrix n E ℂ) {t : ℝ} (ht : 0 ≤ t) :
    lifeMeasure hH X (Set.Ici t) + lifeAtom hH X
      = Xᴴ * heatK hH t * X := by
  rw [lifeMeasure, lifeAtom_eq_sum, ← Finset.sum_add_distrib, heatK,
    compressed_spectral_eq_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hl : 0 ≤ hH.1.eigenvalues i := hH.eigenvalues_nonneg i
  rw [expLife_tail hl ht, ENNReal.toReal_ofReal (by split_ifs <;> positivity)]
  rw [← add_smul]
  congr 1
  by_cases hzero : hH.1.eigenvalues i = 0
  · rw [hzero]
    norm_num
  · rw [show (if hH.1.eigenvalues i = 0 then (0 : ℝ)
        else Real.exp (-(hH.1.eigenvalues i * t)))
      = Real.exp (-(hH.1.eigenvalues i * t)) from by simp [hzero]]
    rw [show (if hH.1.eigenvalues i = 0 then (1 : ℝ) else 0) = 0
      from by simp [hzero]]
    push_cast
    rw [add_zero, mul_comm]

omit [DecidableEq n] [Fintype E] [DecidableEq E] in
/-- Compression distributes over operator sums. -/
theorem compressed_add (X : Matrix n E ℂ) (A C : Matrix n n ℂ) :
    Xᴴ * (A + C) * X = Xᴴ * A * X + Xᴴ * C * X := by
  rw [Matrix.mul_add, Matrix.add_mul]

/-- The exponential component of a bin `[a, b)`, `0 ≤ a ≤ b`, is the
difference of the tails. -/
theorem expLife_Ico {l : ℝ} (hl : 0 ≤ l) {a b : ℝ} (hab : a ≤ b) :
    expLife l (Set.Ico a b)
      = expLife l (Set.Ici a) - expLife l (Set.Ici b) := by
  have hsub : Set.Ici b ⊆ Set.Ici a := Set.Ici_subset_Ici.mpr hab
  have hdiff : Set.Ico a b = Set.Ici a \ Set.Ici b := by
    ext s
    simp only [Set.mem_Ico, Set.mem_sdiff, Set.mem_Ici, not_le]
  have hfin : expLife l (Set.Ici b) ≠ ⊤ :=
    (lt_of_le_of_lt (expLife_finite hl _) ENNReal.one_lt_top).ne
  rw [hdiff, measure_sdiff hsub measurableSet_Ici.nullMeasurableSet hfin]

omit [Fintype E] [DecidableEq E] in
/-- **(LT.17, exact histogram)** The discrete first-loss law is the
histogram of the continuum lifetime:
`𝖯_{h,m} = Λ([mh, (m+1)h))` for `h ≥ 0`. -/
theorem lifetime_histogram {H : Matrix n n ℂ} (hH : H.PosSemidef)
    (X : Matrix n E ℂ) {h : ℝ} (hh : 0 ≤ h) (m : ℕ) :
    firstLoss hH X h m
      = lifeMeasure hH X (Set.Ico ((m : ℝ) * h) (((m : ℝ) + 1) * h)) := by
  rw [firstLoss_eq_spectral, compressed_spectral_eq_sum, lifeMeasure]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine congrArg (fun r : ℝ => (r : ℂ) • srcWeight hH.1 X i) ?_
  set l := hH.1.eigenvalues i with hldef
  have hl : 0 ≤ l := hH.eigenvalues_nonneg i
  have hmh : (0 : ℝ) ≤ (m : ℝ) * h := by positivity
  have hmm : (m : ℝ) * h ≤ ((m : ℝ) + 1) * h := by nlinarith
  rw [expLife_Ico hl hmm, expLife_tail hl hmh,
    expLife_tail hl (le_trans hmh hmm)]
  by_cases hzero : l = 0
  · rw [hzero]
    norm_num
  · rw [show (if l = 0 then (0 : ℝ) else Real.exp (-(l * ((m : ℝ) * h))))
      = Real.exp (-(l * ((m : ℝ) * h))) from by simp [hzero]]
    rw [show (if l = 0 then (0 : ℝ)
        else Real.exp (-(l * (((m : ℝ) + 1) * h))))
      = Real.exp (-(l * (((m : ℝ) + 1) * h))) from by simp [hzero]]
    have hexp_le : Real.exp (-(l * (((m : ℝ) + 1) * h)))
        ≤ Real.exp (-(l * ((m : ℝ) * h))) :=
      Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left hmm hl))
    rw [← ENNReal.ofReal_sub _ (Real.exp_pos _).le,
      ENNReal.toReal_ofReal (by linarith)]
    have g1 : -((m : ℝ) * h * l) = -(l * ((m : ℝ) * h)) := by ring
    have g2 : -(((m : ℝ) + 1) * h * l) = -(l * (((m : ℝ) + 1) * h)) := by
      ring
    rw [g1, g2]

omit [Fintype E] [DecidableEq E] in
/-- **(LT.17, mesh halving)** Time-mesh refinement creates no source
birth: `𝖯_{h,m} = 𝖯_{h/2,2m} + 𝖯_{h/2,2m+1}`. -/
theorem lifetime_mesh_halving {H : Matrix n n ℂ} (hH : H.PosSemidef)
    (X : Matrix n E ℂ) (h : ℝ) (m : ℕ) :
    firstLoss hH X h m
      = firstLoss hH X (h / 2) (2 * m) + firstLoss hH X (h / 2) (2 * m + 1) := by
  rw [firstLoss_eq_spectral, firstLoss_eq_spectral, firstLoss_eq_spectral,
    ← compressed_add, ← spectralFunction_add]
  congr 1
  congr 1
  refine spectralFunction_congr hH.1 fun i => ?_
  set l := hH.1.eigenvalues i
  have e1 : -((2 * m : ℕ) : ℝ) * (h / 2) * l = -((m : ℝ) * h * l) := by
    push_cast
    ring
  have e2 : -(((2 * m : ℕ) : ℝ) + 1) * (h / 2) * l
      = -(((m : ℝ) + 1 / 2) * h * l) := by
    push_cast
    ring
  have e3 : -(((2 * m + 1 : ℕ) : ℝ)) * (h / 2) * l
      = -(((m : ℝ) + 1 / 2) * h * l) := by
    push_cast
    ring
  have e4 : -((((2 * m + 1 : ℕ) : ℝ)) + 1) * (h / 2) * l
      = -(((m : ℝ) + 1) * h * l) := by
    push_cast
    ring
  rw [show (-(((2 * m : ℕ) : ℝ) * (h / 2) * l)) = -((m : ℝ) * h * l)
      from by push_cast; ring,
    show (-((((2 * m : ℕ) : ℝ) + 1) * (h / 2) * l))
      = -(((m : ℝ) + 1 / 2) * h * l) from by push_cast; ring,
    show (-((((2 * m + 1 : ℕ) : ℝ)) * (h / 2) * l))
      = -(((m : ℝ) + 1 / 2) * h * l) from by push_cast; ring,
    show (-(((((2 * m + 1 : ℕ) : ℝ)) + 1) * (h / 2) * l))
      = -(((m : ℝ) + 1) * h * l) from by push_cast; ring]
  ring

/-- The Bochner integral of an observable against an exponential
lifetime component of nonnegative rate. -/
theorem expLife_integral {l : ℝ} (hl : 0 ≤ l) (g : ℝ → ℝ) :
    ∫ s, g s ∂(expLife l)
      = ∫ s in Set.Ioi 0, (l * Real.exp (-(l * s))) * g s := by
  rw [expLife, integral_withDensity_eq_integral_toReal_smul
    (by fun_prop) (Filter.Eventually.of_forall fun s => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  have hnn : 0 ≤ l * Real.exp (-(l * s)) := by positivity
  change (ENNReal.ofReal (l * Real.exp (-(l * s)))).toReal • g s
    = l * Real.exp (-(l * s)) * g s
  rw [ENNReal.toReal_ofReal hnn, smul_eq_mul]

/-- The Laplace transform of an exponential lifetime component:
`∫ e^{-zs} λe^{-λs} ds = λ/(λ+z)` for `λ ≥ 0`, `z > 0`. -/
theorem expLife_laplace {l : ℝ} (hl : 0 ≤ l) {z : ℝ} (hz : 0 < z) :
    ∫ s, Real.exp (-(z * s)) ∂(expLife l) = l / (l + z) := by
  rw [expLife_integral hl]
  have hcongr : ∀ s : ℝ, (l * Real.exp (-(l * s))) * Real.exp (-(z * s))
      = l * Real.exp (-(l + z) * s) := by
    intro s
    rw [mul_assoc, ← Real.exp_add,
      show (-(l * s) + -(z * s)) = -(l + z) * s from by ring]
  rw [integral_congr_ae (Filter.Eventually.of_forall fun s => hcongr s),
    MeasureTheory.integral_const_mul,
    integral_exp_mul_Ioi (by linarith : -(l + z) < 0) 0]
  rw [mul_zero, Real.exp_zero]
  have hne : l + z ≠ 0 := by linarith
  field_simp

omit [Fintype E] in
/-- **(LT.16)** The Laplace transform of the lifetime law:
`Λ̂(z) = I_E - z X^*(H+zI)^{-1}X` for `z > 0` (the `{∞}` atom contributes
`e^{-z·∞} = 0`, so the transform is the exponential-mixture integral). -/
theorem lifetime_laplace {H : Matrix n n ℂ} (hH : H.PosSemidef)
    {X : Matrix n E ℂ} (hX : Xᴴ * X = 1) {z : ℝ} (hz : 0 < z) :
    ∑ i, ((∫ s, Real.exp (-(z * s))
        ∂(expLife (hH.1.eigenvalues i)) : ℝ) : ℂ) • srcWeight hH.1 X i
      = 1 - (z : ℂ) • (Xᴴ * (H + (z : ℂ) • 1)⁻¹ * X) := by
  -- the shifted resolvent by spectral calculus
  have hshift : H + (z : ℂ) • 1
      = spectralFunction hH.1 (fun l => l + z) := by
    have h1 := spectralFunction_add hH.1 id (fun _ => z)
    rw [spectralFunction_id, spectralFunction_const] at h1
    exact h1.symm
  have hinv : (H + (z : ℂ) • 1)⁻¹
      = spectralFunction hH.1 (fun l => (l + z)⁻¹) := by
    have hleft : spectralFunction hH.1 (fun l => (l + z)⁻¹)
        * (H + (z : ℂ) • 1) = 1 := by
      rw [hshift, spectralFunction_mul]
      have hcongr : spectralFunction hH.1 (fun l => (l + z)⁻¹ * (l + z))
          = spectralFunction hH.1 (fun _ => 1) := by
        refine spectralFunction_congr hH.1 fun i => ?_
        have hpos : 0 < hH.1.eigenvalues i + z :=
          add_pos_of_nonneg_of_pos (hH.eigenvalues_nonneg i) hz
        change (hH.1.eigenvalues i + z)⁻¹ * (hH.1.eigenvalues i + z) = 1
        exact inv_mul_cancel₀ hpos.ne'
      rw [hcongr, spectralFunction_one]
    exact Matrix.inv_eq_left_inv hleft
  -- the right-hand side as a compressed spectral function
  have hRHS : 1 - (z : ℂ) • (Xᴴ * (H + (z : ℂ) • 1)⁻¹ * X)
      = ∑ i, (((hH.1.eigenvalues i / (hH.1.eigenvalues i + z)) : ℝ) : ℂ)
        • srcWeight hH.1 X i := by
    have h1 : (z : ℂ) • (Xᴴ * (H + (z : ℂ) • 1)⁻¹ * X)
        = Xᴴ * spectralFunction hH.1 (fun l => z * (l + z)⁻¹) * X := by
      rw [hinv, spectralFunction_smul hH.1 z (fun l => (l + z)⁻¹),
        Matrix.mul_smul, Matrix.smul_mul]
    have h2 : (1 : Matrix E E ℂ)
        = Xᴴ * spectralFunction hH.1 (fun _ => 1) * X := by
      rw [spectralFunction_one, Matrix.mul_one, hX]
    rw [h1, h2, ← compressed_sub, ← spectralFunction_sub]
    have h3 : spectralFunction hH.1 (fun l => 1 - z * (l + z)⁻¹)
        = spectralFunction hH.1 (fun l => l / (l + z)) := by
      refine spectralFunction_congr hH.1 fun i => ?_
      have hpos : 0 < hH.1.eigenvalues i + z :=
        add_pos_of_nonneg_of_pos (hH.eigenvalues_nonneg i) hz
      change 1 - z * (hH.1.eigenvalues i + z)⁻¹
        = hH.1.eigenvalues i / (hH.1.eigenvalues i + z)
      field_simp
      ring
    rw [h3, compressed_spectral_eq_sum]
  rw [hRHS]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [expLife_laplace (hH.eigenvalues_nonneg i) hz]

omit [DecidableEq E] in
/-- When the source carries no zero-energy atom, every zero-energy source
weight vanishes. -/
theorem lifeAtom_free_srcWeight {H : Matrix n n ℂ} (hH : H.PosSemidef)
    (X : Matrix n E ℂ) (hker : lifeAtom hH X = 0) :
    ∀ i, hH.1.eigenvalues i = 0 → srcWeight hH.1 X i = 0 := by
  intro i₀ hi₀
  have hzero : ∑ i, (((if hH.1.eigenvalues i = 0 then (1 : ℝ) else 0)
      : ℝ) : ℂ) • srcWeight hH.1 X i = 0 :=
    (lifeAtom_eq_sum hH X).symm.trans hker
  have hforms : ∀ x : E → ℂ,
      (star x ⬝ᵥ (srcWeight hH.1 X i₀ *ᵥ x)).re = 0 := by
    intro x
    have hterm : ∀ i : n, (star x ⬝ᵥ
        (((((if hH.1.eigenvalues i = 0 then (1 : ℝ) else 0) : ℝ) : ℂ)
          • srcWeight hH.1 X i) *ᵥ x)).re
        = (if hH.1.eigenvalues i = 0 then (1 : ℝ) else 0)
          * (star x ⬝ᵥ (srcWeight hH.1 X i *ᵥ x)).re := by
      intro i
      rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
        Complex.re_ofReal_mul]
    have h0 : (star x ⬝ᵥ ((∑ i, (((if hH.1.eigenvalues i = 0
          then (1 : ℝ) else 0) : ℝ) : ℂ) • srcWeight hH.1 X i) *ᵥ x)).re
        = (star x ⬝ᵥ ((0 : Matrix E E ℂ) *ᵥ x)).re :=
      congrArg (fun M : Matrix E E ℂ => (star x ⬝ᵥ (M *ᵥ x)).re) hzero
    rw [Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum,
      Finset.sum_congr rfl fun i _ => hterm i, Matrix.zero_mulVec,
      dotProduct_zero] at h0
    have hnn : ∀ i ∈ Finset.univ, 0 ≤ (if hH.1.eigenvalues i = 0
        then (1 : ℝ) else 0) * (star x ⬝ᵥ (srcWeight hH.1 X i *ᵥ x)).re := by
      intro i _
      refine mul_nonneg (by split_ifs <;> norm_num) ?_
      exact re_form_nonneg (srcWeight_posSemidef hH.1 X i) x
    have h0' : ∑ i, (if hH.1.eigenvalues i = 0 then (1 : ℝ) else 0)
        * (star x ⬝ᵥ (srcWeight hH.1 X i *ᵥ x)).re = 0 := by
      rw [h0]
      rfl
    have heach := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h0'
    have h1 := heach i₀ (Finset.mem_univ i₀)
    rw [hi₀] at h1
    simp only [ite_true] at h1
    linarith [h1]
  refine hermitian_eq_of_re_forms (srcWeight_posSemidef hH.1 X i₀).1
    ?_ fun x => ?_
  · exact Matrix.isHermitian_zero
  · rw [hforms x, Matrix.zero_mulVec, dotProduct_zero]
    rfl

/-- The scalar zero-mass Green bracket:
`0 ≤ 1/λ - h e^{-hλ}/(1-e^{-hλ}) ≤ h` for `λ, h > 0`. -/
theorem green_gap_bounds {l h : ℝ} (hl : 0 < l) (hh : 0 < h) :
    0 ≤ l⁻¹ - h * Real.exp (-(h * l)) / (1 - Real.exp (-(h * l)))
    ∧ l⁻¹ - h * Real.exp (-(h * l)) / (1 - Real.exp (-(h * l))) ≤ h := by
  set u : ℝ := h * l with hu
  have hupos : 0 < u := mul_pos hh hl
  set r : ℝ := Real.exp (-u) with hr
  have hrpos : 0 < r := Real.exp_pos _
  have hr1 : r < 1 := by
    rw [hr, Real.exp_lt_one_iff]
    linarith
  have h1mr : 0 < 1 - r := by linarith
  have hprod : r * Real.exp u = 1 := by
    rw [hr, ← Real.exp_add]
    simp
  have hkey := Real.add_one_le_exp u
  -- `u r ≤ 1 - r` and `1 - r ≤ u`
  have hineq1 : u * r ≤ 1 - r := by
    have h2 : (u + 1) * r ≤ Real.exp u * r :=
      mul_le_mul_of_nonneg_right hkey hrpos.le
    have h3 : Real.exp u * r = 1 := by rw [mul_comm]; exact hprod
    nlinarith
  have hineq2 : 1 - r ≤ u := by
    have hkey2 := Real.add_one_le_exp (-u)
    rw [← hr] at hkey2
    linarith
  constructor
  · rw [sub_nonneg, div_le_iff₀ h1mr]
    rw [inv_mul_eq_div, le_div_iff₀ hl]
    calc h * r * l = u * r := by rw [hu]; ring
      _ ≤ 1 - r := hineq1
  · have hstep : l⁻¹ ≤ h * r / (1 - r) + h := by
      have hsum : h * r / (1 - r) + h = h / (1 - r) := by
        field_simp
        ring
      rw [hsum, le_div_iff₀ h1mr, inv_mul_eq_div, div_le_iff₀ hl]
      calc 1 - r ≤ u := hineq2
        _ = h * l := hu
    linarith

/-- The spectral symbol of the discrete zero-mass Green response,
`h e^{-hλ}/(1 - e^{-hλ})` off the kernel. -/
noncomputable def greenSym (h : ℝ) : ℝ → ℝ := fun l =>
  if l = 0 then 0 else h * Real.exp (-(h * l)) / (1 - Real.exp (-(h * l)))

omit [DecidableEq E] in
/-- **(LT.18, first identity, left side)** The scaled renewal series
`h ∑_{m≥1} M_{h,m}` sums to the discrete Green matrix. -/
theorem renewal_green_hasSum_transfer {H : Matrix n n ℂ}
    (hH : H.PosSemidef) (X : Matrix n E ℂ) {h : ℝ} (hh : 0 < h)
    (hker : lifeAtom hH X = 0) :
    HasSum (fun m : ℕ => ((h : ℝ) : ℂ) • transferM hH X h (m + 1))
      (Xᴴ * spectralFunction hH.1 (greenSym h) * X) := by
  have hfun : (fun m : ℕ => ((h : ℝ) : ℂ) • transferM hH X h (m + 1))
      = fun m : ℕ => Xᴴ * spectralFunction hH.1
        (fun l => h * Real.exp (-(((m + 1 : ℕ) : ℝ) * h * l))) * X := by
    funext m
    rw [transferM_eq_spectral]
    rw [show ((h : ℝ) : ℂ) • (Xᴴ * spectralFunction hH.1
          (fun l => Real.exp (-(((m + 1 : ℕ) : ℝ) * h * l))) * X)
        = Xᴴ * (((h : ℝ) : ℂ) • spectralFunction hH.1
          (fun l => Real.exp (-(((m + 1 : ℕ) : ℝ) * h * l)))) * X from by
      rw [Matrix.mul_smul, Matrix.smul_mul]]
    rw [← spectralFunction_smul hH.1 h]
  rw [hfun]
  refine compressed_spectral_hasSum hH.1 X
    (f := fun m l => h * Real.exp (-(((m + 1 : ℕ) : ℝ) * h * l)))
    (g := greenSym h) fun i => ?_
  set l := hH.1.eigenvalues i with hldef
  have hev : 0 ≤ l := hH.eigenvalues_nonneg i
  by_cases hzero : l = 0
  · right
    exact lifeAtom_free_srcWeight hH X hker i hzero
  · left
    have hpos : 0 < l := lt_of_le_of_ne hev (Ne.symm hzero)
    set r : ℝ := Real.exp (-(h * l)) with hrdef
    have hr0 : 0 ≤ r := (Real.exp_pos _).le
    have hr1 : r < 1 := by
      rw [hrdef, Real.exp_lt_one_iff]
      nlinarith
    have hgeom := (hasSum_geometric_of_lt_one hr0 hr1).mul_left (h * r)
    have hshape : (fun m : ℕ => h * r * r ^ m)
        = fun m : ℕ => h * Real.exp (-(((m + 1 : ℕ) : ℝ) * h * l)) := by
      funext m
      rw [hrdef, ← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
      congr 2
      push_cast
      ring
    rw [hshape] at hgeom
    have hval : h * r * (1 - r)⁻¹ = greenSym h l := by
      simp only [greenSym]
      rw [show (if l = 0 then (0 : ℝ)
          else h * Real.exp (-(h * l)) / (1 - Real.exp (-(h * l))))
        = h * r / (1 - r) from by rw [← hrdef]; simp [hzero]]
      rw [div_eq_mul_inv]
    rw [hval] at hgeom
    exact hgeom

omit [Fintype E] [DecidableEq E] in
/-- **(LT.18, first identity, right side)** The mean renewal series
`h ∑_j j 𝖯_{h,j}` sums to the same discrete Green matrix. -/
theorem renewal_green_hasSum_firstLoss {H : Matrix n n ℂ}
    (hH : H.PosSemidef) (X : Matrix n E ℂ) {h : ℝ} (hh : 0 < h) :
    HasSum (fun j : ℕ => ((((j : ℝ) * h) : ℝ) : ℂ) • firstLoss hH X h j)
      (Xᴴ * spectralFunction hH.1 (greenSym h) * X) := by
  have hfun : (fun j : ℕ => ((((j : ℝ) * h) : ℝ) : ℂ) • firstLoss hH X h j)
      = fun j : ℕ => Xᴴ * spectralFunction hH.1
        (fun l => ((j : ℝ) * h) * (Real.exp (-((j : ℕ) * h * l))
          - Real.exp (-(((j : ℝ) + 1) * h * l)))) * X := by
    funext j
    rw [firstLoss_eq_spectral]
    rw [show ((((j : ℝ) * h) : ℝ) : ℂ) • (Xᴴ * spectralFunction hH.1
          (fun l => Real.exp (-((j : ℕ) * h * l))
            - Real.exp (-(((j : ℝ) + 1) * h * l))) * X)
        = Xᴴ * ((((j : ℝ) * h : ℝ) : ℂ) • spectralFunction hH.1
          (fun l => Real.exp (-((j : ℕ) * h * l))
            - Real.exp (-(((j : ℝ) + 1) * h * l)))) * X from by
      rw [Matrix.mul_smul, Matrix.smul_mul]]
    rw [← spectralFunction_smul hH.1 ((j : ℝ) * h)]
  rw [hfun]
  refine compressed_spectral_hasSum hH.1 X
    (f := fun j l => ((j : ℝ) * h) * (Real.exp (-((j : ℕ) * h * l))
      - Real.exp (-(((j : ℝ) + 1) * h * l))))
    (g := greenSym h) fun i => ?_
  left
  set l := hH.1.eigenvalues i with hldef
  have hev : 0 ≤ l := hH.eigenvalues_nonneg i
  by_cases hzero : l = 0
  · have hz : (fun j : ℕ => ((j : ℝ) * h) * (Real.exp (-((j : ℕ) * h * l))
        - Real.exp (-(((j : ℝ) + 1) * h * l)))) = fun _ => 0 := by
      funext j
      rw [hzero]
      norm_num
    rw [hz]
    rw [show greenSym h l = 0 from by rw [hzero]; simp [greenSym]]
    exact hasSum_zero
  · have hpos : 0 < l := lt_of_le_of_ne hev (Ne.symm hzero)
    set r : ℝ := Real.exp (-(h * l)) with hrdef
    have hr0 : 0 < r := Real.exp_pos _
    have hr1 : r < 1 := by
      rw [hrdef, Real.exp_lt_one_iff]
      nlinarith
    have hnorm : ‖r‖ < 1 := by
      rw [Real.norm_eq_abs, abs_of_pos hr0]
      exact hr1
    have hgeom := (hasSum_coe_mul_geometric_of_norm_lt_one hnorm).mul_left
      (h * (1 - r))
    have hshape : (fun j : ℕ => h * (1 - r) * ((j : ℝ) * r ^ j))
        = fun j : ℕ => ((j : ℝ) * h) * (Real.exp (-((j : ℕ) * h * l))
          - Real.exp (-(((j : ℝ) + 1) * h * l))) := by
      funext j
      have e1 : Real.exp (-((j : ℕ) * h * l)) = r ^ j := by
        rw [hrdef, ← Real.exp_nat_mul]
        congr 1
        ring
      have e2 : Real.exp (-(((j : ℝ) + 1) * h * l)) = r ^ j * r := by
        rw [hrdef, ← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        ring
      rw [e1, e2]
      ring
    rw [hshape] at hgeom
    have hval : h * (1 - r) * (r / (1 - r) ^ 2) = greenSym h l := by
      simp only [greenSym]
      rw [show (if l = 0 then (0 : ℝ)
          else h * Real.exp (-(h * l)) / (1 - Real.exp (-(h * l))))
        = h * r / (1 - r) from by rw [← hrdef]; simp [hzero]]
      have hne : (1 : ℝ) - r ≠ 0 := by linarith
      field_simp
    rw [hval] at hgeom
    exact hgeom

/-- **(LT.18, Green bracket)** The zero-mass Green response brackets the
discrete Green matrix:
`0 ⪯ X^*H^{-1}X - h∑_{m≥1}M_{h,m} ⪯ hI_E` (with `H^{-1}` the spectral
Moore–Penrose inverse; the compressed bracket needs no zero-atom
hypothesis since both symbols vanish on the kernel). -/
theorem renewal_green_bracket {H : Matrix n n ℂ} (hH : H.PosSemidef)
    {X : Matrix n E ℂ} (hX : Xᴴ * X = 1) {h : ℝ} (hh : 0 < h) :
    (Xᴴ * pinv hH.1 * X
      - Xᴴ * spectralFunction hH.1 (greenSym h) * X).PosSemidef
    ∧ (((h : ℝ) : ℂ) • (1 : Matrix E E ℂ)
      - (Xᴴ * pinv hH.1 * X
        - Xᴴ * spectralFunction hH.1 (greenSym h) * X)).PosSemidef := by
  have hgap : ∀ i : n, 0 ≤ (fun l => (if 0 < l then l⁻¹ else 0)
      - greenSym h l) (hH.1.eigenvalues i)
      ∧ (fun l => (if 0 < l then l⁻¹ else 0) - greenSym h l)
        (hH.1.eigenvalues i) ≤ h := by
    intro i
    set l := hH.1.eigenvalues i with hldef
    have hev : 0 ≤ l := hH.eigenvalues_nonneg i
    by_cases hzero : l = 0
    · rw [hzero]
      constructor
      · rw [show ((fun l => (if 0 < l then l⁻¹ else 0) - greenSym h l) 0)
          = 0 from by simp [greenSym]]
      · rw [show ((fun l => (if 0 < l then l⁻¹ else 0) - greenSym h l) 0)
          = 0 from by simp [greenSym]]
        exact hh.le
    · have hpos : 0 < l := lt_of_le_of_ne hev (Ne.symm hzero)
      have hbounds := green_gap_bounds hpos hh
      constructor
      · rw [show ((fun l => (if 0 < l then l⁻¹ else 0) - greenSym h l) l)
            = l⁻¹ - h * Real.exp (-(h * l)) / (1 - Real.exp (-(h * l)))
          from by simp [greenSym, hzero, hpos]]
        exact hbounds.1
      · rw [show ((fun l => (if 0 < l then l⁻¹ else 0) - greenSym h l) l)
            = l⁻¹ - h * Real.exp (-(h * l)) / (1 - Real.exp (-(h * l)))
          from by simp [greenSym, hzero, hpos]]
        exact hbounds.2
  have hgapEq : Xᴴ * pinv hH.1 * X
      - Xᴴ * spectralFunction hH.1 (greenSym h) * X
      = Xᴴ * spectralFunction hH.1 (fun l => (if 0 < l then l⁻¹ else 0)
        - greenSym h l) * X := by
    rw [spectralFunction_sub, compressed_sub]
    rfl
  constructor
  · rw [hgapEq]
    exact compressed_posSemidef (spectralFunction_posSemidef hH.1 _
      fun i => (hgap i).1) X
  · rw [hgapEq]
    have hone : ((h : ℝ) : ℂ) • (1 : Matrix E E ℂ)
        = Xᴴ * spectralFunction hH.1 (fun _ => h) * X := by
      rw [spectralFunction_const, Matrix.mul_smul, Matrix.smul_mul,
        Matrix.mul_one, hX]
    have hfinal : ((h : ℝ) : ℂ) • (1 : Matrix E E ℂ)
        - Xᴴ * spectralFunction hH.1
          (fun l => (if 0 < l then l⁻¹ else 0) - greenSym h l) * X
        = Xᴴ * spectralFunction hH.1
          (fun l => h - ((if 0 < l then l⁻¹ else 0) - greenSym h l)) * X := by
      rw [hone, ← compressed_sub, ← spectralFunction_sub]
    rw [hfinal]
    exact compressed_posSemidef (spectralFunction_posSemidef hH.1
      (fun l => h - ((if 0 < l then l⁻¹ else 0) - greenSym h l))
      fun i => sub_nonneg.mpr (hgap i).2) X

/-- The zero-rate exponential component is the zero measure. -/
theorem expLife_zero : expLife 0 = 0 := by
  rw [expLife]
  have hd : (fun s : ℝ => ENNReal.ofReal (0 * Real.exp (-(0 * s))))
      = (0 : ℝ → ℝ≥0∞) := by
    funext s
    norm_num
  rw [hd, withDensity_zero]

/-- Integrability of the lifetime-moment integrand. -/
theorem lifeMoment_integrableOn {l : ℝ} (hl : 0 < l) {p : ℝ} (hp : 0 < p) :
    MeasureTheory.IntegrableOn
      (fun s => (l * Real.exp (-(l * s))) * s ^ p) (Set.Ioi 0) := by
  have h0 := integrableOn_rpow_mul_exp_neg_mul_rpow
    (by linarith : (-1 : ℝ) < p) one_pos hl
  have h1 : MeasureTheory.IntegrableOn
      (fun x : ℝ => x ^ p * Real.exp (-l * x)) (Set.Ioi 0) := by
    refine h0.congr_fun (fun x hx => ?_) measurableSet_Ioi
    change x ^ p * Real.exp (-l * x ^ (1 : ℝ)) = x ^ p * Real.exp (-l * x)
    rw [Real.rpow_one]
  have h2 : MeasureTheory.IntegrableOn
      (fun x : ℝ => l * (x ^ p * Real.exp (-l * x))) (Set.Ioi 0) :=
    h1.const_mul l
  refine h2.congr_fun (fun x (hx : x ∈ Set.Ioi 0) => ?_) measurableSet_Ioi
  rw [show (-(l * x)) = -l * x from by ring]
  ring

/-- The `p`-th moment of an exponential lifetime component:
`∫ s^p λe^{-λs} ds = Γ(p+1) λ^{-p}`. -/
theorem expLife_moment {l : ℝ} (hl : 0 < l) {p : ℝ} (hp : 0 < p) :
    ∫ s, s ^ p ∂(expLife l) = Real.Gamma (p + 1) * l ^ (-p) := by
  rw [expLife_integral hl.le]
  have hshape : Set.EqOn (fun s => (l * Real.exp (-(l * s))) * s ^ p)
      (fun s => l * (s ^ ((p + 1) - 1) * Real.exp (-(l * s))))
      (Set.Ioi 0) := by
    intro s _
    rw [show (p + 1) - 1 = p from by ring]
    ring
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hshape,
    MeasureTheory.integral_const_mul,
    Real.integral_rpow_mul_exp_neg_mul_Ioi (by linarith : (0 : ℝ) < p + 1)
      hl]
  have hlp : (0 : ℝ) < l ^ p := Real.rpow_pos_of_pos hl p
  have h1 : (1 / l) ^ (p + 1) = (l ^ (p + 1))⁻¹ := by
    rw [one_div, Real.inv_rpow hl.le]
  have h2 : l ^ (p + 1) = l ^ p * l := by
    rw [Real.rpow_add hl, Real.rpow_one]
  have h3 : l ^ (-p) = (l ^ p)⁻¹ := Real.rpow_neg hl.le p
  rw [h1, h2, h3]
  field_simp

/-- The extended `[0,∞]`-valued `p`-th moment of an exponential
component. -/
theorem expLife_lintegral_moment {l : ℝ} (hl : 0 < l) {p : ℝ}
    (hp : 0 < p) :
    ∫⁻ s, ENNReal.ofReal (s ^ p) ∂(expLife l)
      = ENNReal.ofReal (Real.Gamma (p + 1) * l ^ (-p)) := by
  have hmeas : Measurable fun s : ℝ => ENNReal.ofReal (s ^ p) := by
    fun_prop
  rw [expLife, lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) hmeas]
  simp only [Pi.mul_apply]
  have hshape : ∀ s : ℝ,
      ENNReal.ofReal (l * Real.exp (-(l * s))) * ENNReal.ofReal (s ^ p)
      = ENNReal.ofReal ((l * Real.exp (-(l * s))) * s ^ p) := by
    intro s
    exact (ENNReal.ofReal_mul (by positivity)).symm
  rw [lintegral_congr fun s => hshape s]
  have hnn : (0 : ℝ → ℝ) ≤ᵐ[volume.restrict (Set.Ioi 0)]
      fun s => (l * Real.exp (-(l * s))) * s ^ p := by
    refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr ?_
    refine Filter.Eventually.of_forall fun s hs => ?_
    have hs0 : (0 : ℝ) < s := hs
    have h1 : (0 : ℝ) ≤ s ^ p := Real.rpow_nonneg hs0.le p
    have h2 : (0 : ℝ) < Real.exp (-(l * s)) := Real.exp_pos _
    positivity
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    (lifeMoment_integrableOn hl hp) hnn]
  congr 1
  have h := expLife_moment hl hp
  rw [expLife_integral hl.le] at h
  exact h

omit [Fintype E] [DecidableEq E] in
/-- **(LT.15, exponential-mixture form)** The finite-part `p`-th moment of
the lifetime law is `Γ(p+1) X^* H^{-p} X` (spectral pseudo-power). -/
theorem lifetime_moment {H : Matrix n n ℂ} (hH : H.PosSemidef)
    (X : Matrix n E ℂ) {p : ℝ} (hp : 0 < p) :
    ∑ i, ((∫ s, s ^ p ∂(expLife (hH.1.eigenvalues i)) : ℝ) : ℂ)
        • srcWeight hH.1 X i
      = ((Real.Gamma (p + 1) : ℝ) : ℂ)
        • (Xᴴ * spectralFunction hH.1
          (fun l => if 0 < l then l ^ (-p) else 0) * X) := by
  rw [show ((Real.Gamma (p + 1) : ℝ) : ℂ)
        • (Xᴴ * spectralFunction hH.1
          (fun l => if 0 < l then l ^ (-p) else 0) * X)
      = Xᴴ * spectralFunction hH.1
        (fun l => Real.Gamma (p + 1) * (if 0 < l then l ^ (-p) else 0)) * X
    from by
      rw [spectralFunction_smul, Matrix.mul_smul, Matrix.smul_mul]]
  rw [compressed_spectral_eq_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine congrArg (fun r : ℝ => (r : ℂ) • srcWeight hH.1 X i) ?_
  set l := hH.1.eigenvalues i with hldef
  have hev : 0 ≤ l := hH.eigenvalues_nonneg i
  by_cases hzero : l = 0
  · rw [hzero, expLife_zero]
    simp
  · have hpos : 0 < l := lt_of_le_of_ne hev (Ne.symm hzero)
    rw [expLife_moment hpos hp]
    rw [show (if 0 < l then l ^ (-p) else 0) = l ^ (-p)
      from by simp [hpos]]

/-- The exponential components put no mass on the negative axis. -/
theorem expLife_Iio (l : ℝ) : expLife l (Set.Iio 0) = 0 := by
  rw [expLife_apply l measurableSet_Iio]
  have hempty : (Set.Iio 0 ∩ Set.Ioi 0 : Set ℝ) = ∅ := by
    ext s
    simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioi,
      Set.mem_empty_iff_false, iff_false, not_and]
    intro h1 h2
    exact absurd h2 (not_lt.mpr h1.le)
  rw [hempty]
  simp

/-- The scalarized lifetime measure along a source direction `c`
(LT.13, uniqueness carrier). -/
noncomputable def lifeScal {H : Matrix n n ℂ} (hH : H.PosSemidef)
    (X : Matrix n E ℂ) (c : E → ℂ) : Measure ℝ :=
  ∑ i, (ENNReal.ofReal ((star c ⬝ᵥ (srcWeight hH.1 X i *ᵥ c)).re))
    • expLife (hH.1.eigenvalues i)

omit [DecidableEq E] in
/-- The scalarized lifetime measure computes the diagonal pairing of the
operator-valued lifetime measure. -/
theorem lifeScal_apply {H : Matrix n n ℂ} (hH : H.PosSemidef)
    (X : Matrix n E ℂ) (c : E → ℂ) (A : Set ℝ) :
    (lifeScal hH X c A).toReal
      = (star c ⬝ᵥ (lifeMeasure hH X A *ᵥ c)).re := by
  rw [lifeScal, Measure.finsetSum_apply]
  have hterm : ∀ i : n,
      ((ENNReal.ofReal ((star c ⬝ᵥ (srcWeight hH.1 X i *ᵥ c)).re))
        • expLife (hH.1.eigenvalues i)) A
      = ENNReal.ofReal ((star c ⬝ᵥ (srcWeight hH.1 X i *ᵥ c)).re)
        * expLife (hH.1.eigenvalues i) A := fun i => rfl
  rw [Finset.sum_congr rfl fun i _ => hterm i]
  have hfin : ∀ i ∈ Finset.univ,
      ENNReal.ofReal ((star c ⬝ᵥ (srcWeight hH.1 X i *ᵥ c)).re)
        * expLife (hH.1.eigenvalues i) A ≠ ⊤ := by
    intro i _
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
    exact (lt_of_le_of_lt (expLife_finite (hH.eigenvalues_nonneg i) A)
      ENNReal.one_lt_top).ne
  rw [ENNReal.toReal_sum hfin]
  -- expand the matrix pairing
  rw [lifeMeasure, Matrix.sum_mulVec, dotProduct_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (re_form_nonneg (srcWeight_posSemidef hH.1 X i) c)]
  rw [show ((((expLife (hH.1.eigenvalues i)) A).toReal : ℂ)
        • srcWeight hH.1 X i) *ᵥ c
      = ((expLife (hH.1.eigenvalues i) A).toReal : ℂ)
        • (srcWeight hH.1 X i *ᵥ c) from by rw [Matrix.smul_mulVec]]
  rw [dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul]
  ring

omit [DecidableEq E] in
/-- The scalarized lifetime measure is finite. -/
theorem lifeScal_isFiniteMeasure {H : Matrix n n ℂ} (hH : H.PosSemidef)
    (X : Matrix n E ℂ) (c : E → ℂ) :
    IsFiniteMeasure (lifeScal hH X c) := by
  constructor
  rw [lifeScal, Measure.finsetSum_apply]
  refine ENNReal.sum_lt_top.mpr fun i _ => ?_
  have h1 : ((ENNReal.ofReal ((star c ⬝ᵥ (srcWeight hH.1 X i *ᵥ c)).re))
      • expLife (hH.1.eigenvalues i)) Set.univ
      = ENNReal.ofReal ((star c ⬝ᵥ (srcWeight hH.1 X i *ᵥ c)).re)
        * expLife (hH.1.eigenvalues i) Set.univ := rfl
  rw [h1]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (lt_of_le_of_lt (expLife_finite (hH.eigenvalues_nonneg i) _)
      ENNReal.one_lt_top)

omit [DecidableEq E] in
/-- The scalarized lifetime measure puts no mass on the negative axis. -/
theorem lifeScal_Iio {H : Matrix n n ℂ} (hH : H.PosSemidef)
    (X : Matrix n E ℂ) (c : E → ℂ) : lifeScal hH X c (Set.Iio 0) = 0 := by
  rw [lifeScal, Measure.finsetSum_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  have h1 : ((ENNReal.ofReal ((star c ⬝ᵥ (srcWeight hH.1 X i *ᵥ c)).re))
      • expLife (hH.1.eigenvalues i)) (Set.Iio 0)
      = ENNReal.ofReal ((star c ⬝ᵥ (srcWeight hH.1 X i *ᵥ c)).re)
        * expLife (hH.1.eigenvalues i) (Set.Iio 0) := rfl
  rw [h1, expLife_Iio, mul_zero]

omit [DecidableEq E] in
/-- **(LT.13, uniqueness, scalarized)** A finite Borel measure supported
on `[0, ∞)` whose survival tails agree with those of the lifetime law
along a direction `c` is the scalarized lifetime measure. -/
theorem lifeScal_unique {H : Matrix n n ℂ} (hH : H.PosSemidef)
    (X : Matrix n E ℂ) (c : E → ℂ) (κ : Measure ℝ) [IsFiniteMeasure κ]
    (hsupp : κ (Set.Iio 0) = 0)
    (htail : ∀ t : ℝ, 0 ≤ t →
      κ (Set.Ici t) = lifeScal hH X c (Set.Ici t)) :
    κ = lifeScal hH X c := by
  have hIci : ∀ (μ : Measure ℝ), μ (Set.Iio 0) = 0 → ∀ t : ℝ, t < 0 →
      μ (Set.Ici t) = μ (Set.Ici 0) := by
    intro μ hμ t ht
    have hsplit : Set.Ici t = Set.Ici (0 : ℝ) ∪ Set.Ico t 0 := by
      ext s
      simp only [Set.mem_Ici, Set.mem_union, Set.mem_Ico]
      constructor
      · intro hs
        rcases le_or_gt 0 s with h | h
        · exact Or.inl h
        · exact Or.inr ⟨hs, h⟩
      · rintro (h | ⟨h1, _⟩)
        · linarith
        · exact h1
    rw [hsplit, measure_union ?_ measurableSet_Ico]
    · have hzero : μ (Set.Ico t 0) = 0 :=
        measure_mono_null (fun s hs => hs.2) hμ
      rw [hzero, add_zero]
    · refine Set.disjoint_left.mpr fun s hs1 hs2 => ?_
      have h1 : (0 : ℝ) ≤ s := hs1
      exact absurd hs2.2 (not_lt.mpr h1)
  refine MeasureTheory.Measure.ext_of_Ici κ (lifeScal hH X c) fun a => ?_
  rcases le_or_gt 0 a with ha | ha
  · exact htail a ha
  · rw [hIci κ hsupp a ha, hIci (lifeScal hH X c)
      (lifeScal_Iio hH X c) a ha]
    exact htail 0 le_rfl

/-- The extended `[0,∞]`-valued `p`-th lifetime moment along a source
direction: the finite-part lower integral plus `∞ · Λ({∞})`. -/
noncomputable def extMoment {H : Matrix n n ℂ} (hH : H.PosSemidef)
    (X : Matrix n E ℂ) (p : ℝ) (c : E → ℂ) : ℝ≥0∞ :=
  (∫⁻ s, ENNReal.ofReal (s ^ p) ∂(lifeScal hH X c))
    + ⊤ * ENNReal.ofReal ((star c ⬝ᵥ (lifeAtom hH X *ᵥ c)).re)

omit [DecidableEq E] in
/-- **(LT.15, extended form, atom-free direction)** On directions with no
zero-energy atom the extended moment is the finite Gamma value
`Γ(p+1)⟨c, X^*H^{-p}X c⟩`. -/
theorem extMoment_atom_free {H : Matrix n n ℂ} (hH : H.PosSemidef)
    (X : Matrix n E ℂ) {p : ℝ} (hp : 0 < p) (c : E → ℂ)
    (hatom : (star c ⬝ᵥ (lifeAtom hH X *ᵥ c)).re = 0) :
    extMoment hH X p c = ENNReal.ofReal (Real.Gamma (p + 1)
      * (star c ⬝ᵥ ((Xᴴ * spectralFunction hH.1
        (fun l => if 0 < l then l ^ (-p) else 0) * X) *ᵥ c)).re) := by
  rw [extMoment, hatom, ENNReal.ofReal_zero, mul_zero, add_zero]
  rw [lifeScal, MeasureTheory.lintegral_finsetSum_measure]
  have hterm : ∀ i : n,
      ∫⁻ s, ENNReal.ofReal (s ^ p)
        ∂((ENNReal.ofReal ((star c ⬝ᵥ (srcWeight hH.1 X i *ᵥ c)).re))
          • expLife (hH.1.eigenvalues i))
      = ENNReal.ofReal ((star c ⬝ᵥ (srcWeight hH.1 X i *ᵥ c)).re
        * (Real.Gamma (p + 1)
          * (if 0 < hH.1.eigenvalues i then hH.1.eigenvalues i ^ (-p)
            else 0))) := by
    intro i
    rw [MeasureTheory.lintegral_smul_measure, smul_eq_mul]
    have hev : 0 ≤ hH.1.eigenvalues i := hH.eigenvalues_nonneg i
    by_cases hzero : hH.1.eigenvalues i = 0
    · rw [hzero, expLife_zero, MeasureTheory.lintegral_zero_measure,
        mul_zero]
      rw [show (if (0 : ℝ) < 0 then (0 : ℝ) ^ (-p) else 0) = 0
        from by norm_num]
      rw [mul_zero, mul_zero, ENNReal.ofReal_zero]
    · have hpos : 0 < hH.1.eigenvalues i :=
        lt_of_le_of_ne hev (Ne.symm hzero)
      rw [expLife_lintegral_moment hpos hp]
      rw [show (if 0 < hH.1.eigenvalues i
          then hH.1.eigenvalues i ^ (-p) else 0)
        = hH.1.eigenvalues i ^ (-p) from by simp [hpos]]
      rw [← ENNReal.ofReal_mul
        (re_form_nonneg (srcWeight_posSemidef hH.1 X i) c)]
  rw [Finset.sum_congr rfl fun i _ => hterm i]
  rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => ?_]
  · congr 1
    -- expand the matrix pairing
    rw [compressed_spectral_eq_sum, Matrix.sum_mulVec, dotProduct_sum,
      Complex.re_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show ((((if 0 < hH.1.eigenvalues i
            then hH.1.eigenvalues i ^ (-p) else 0) : ℝ) : ℂ)
          • srcWeight hH.1 X i) *ᵥ c
        = (((if 0 < hH.1.eigenvalues i
            then hH.1.eigenvalues i ^ (-p) else 0) : ℝ) : ℂ)
          • (srcWeight hH.1 X i *ᵥ c) from by rw [Matrix.smul_mulVec]]
    rw [dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul]
    ring
  · refine mul_nonneg (re_form_nonneg (srcWeight_posSemidef hH.1 X i) c) ?_
    refine mul_nonneg (Real.Gamma_pos_of_pos (by linarith)).le ?_
    split_ifs with hposi
    · exact Real.rpow_nonneg hposi.le _
    · exact le_rfl

omit [DecidableEq E] in
/-- **(LT.15, extended form, atom direction)** On a source direction that
carries a zero-energy atom the extended `p`-th moment is `∞`. -/
theorem extMoment_atom_top {H : Matrix n n ℂ} (hH : H.PosSemidef)
    (X : Matrix n E ℂ) (p : ℝ) (c : E → ℂ)
    (hatom : 0 < (star c ⬝ᵥ (lifeAtom hH X *ᵥ c)).re) :
    extMoment hH X p c = ⊤ := by
  rw [extMoment]
  have h1 : ENNReal.ofReal ((star c ⬝ᵥ (lifeAtom hH X *ᵥ c)).re) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hatom).ne'
  rw [ENNReal.top_mul h1, add_top]

end RenewalLifetime

/-! ### `thm:GT-cofinal-dynamic-source`

Rendering: the prose hypotheses (C1)–(C5) are rendered by their exact
quantitative content at the point of use: the per-bank convergence of the
residual Grams delivered by (C2) is the hypothesis `hbank`, the uniform
temporal-tail sandwich (DYN.11) is the Loewner hypothesis `hsandwich`
with `ε_m ↓ 0`, and the transported-defect/direct-route agreement of (C4)
is carried by the exact rectangle `transport_rectangle` (DYN.10).  The
conclusions: existence and cofinal-route uniqueness of the operator-norm
limit `R_dyn,∞ ⪰ 0`; the spectral floor (DYN.12) on the support
projection (rendered, for the PSD limit, as the orthogonal projection
onto `(ker R)ᗮ = Ran R`, which is `1_{(0,∞)}(R)`); the lower block from a
transported isometry (`dual_dynamic_birth_certificate`, DYN.6); the
delayed orthogonality of the residual kernel to the primitive follower
carrier (`cyc_short_delay_orthogonality`, LT.30); and the unitary
uniqueness of minimal source-cyclic realizations of a delayed kernel
(`minimal_cyclic_realization_unique`). -/

section CofinalDynamicSource

open ContinuousLinearMap Submodule Filter Topology Upstream
open scoped InnerProduct ComplexInnerProductSpace

variable {V E E' : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [FiniteDimensional ℂ E']

omit [FiniteDimensional ℂ E] in
/-- Cauchy–Schwarz for the semi-inner product of a positive operator
(real-part version). -/
theorem isPositive_re_inner_sq_le {A : E →L[ℂ] E} (hA : A.IsPositive)
    (x y : E) :
    ((⟪A x, y⟫).re) ^ 2 ≤ (⟪A x, x⟫).re * (⟪A y, y⟫).re := by
  have hquad : ∀ t : ℝ, 0 ≤ (⟪A y, y⟫).re * (t * t)
      + (2 * (⟪A x, y⟫).re) * t + (⟪A x, x⟫).re := by
    intro t
    have h0 := hA.2 (x + (t : ℂ) • y)
    have h1 : ContinuousLinearMap.reApplyInnerSelf A (x + (t : ℂ) • y)
        = (⟪A y, y⟫).re * (t * t) + (2 * (⟪A x, y⟫).re) * t
          + (⟪A x, x⟫).re := by
      unfold ContinuousLinearMap.reApplyInnerSelf
      rw [RCLike.re_to_complex, map_add, map_smul, inner_add_left,
        inner_add_right, inner_add_right]
      simp only [inner_smul_left, inner_smul_right, Complex.conj_ofReal]
      have hsym : ⟪A y, x⟫ = starRingEnd ℂ ⟪A x, y⟫ := by
        have h := hA.isSymmetric y x
        calc ⟪A y, x⟫ = ⟪y, A x⟫ := h
          _ = starRingEnd ℂ ⟪A x, y⟫ := by rw [← inner_conj_symm]
      rw [hsym]
      simp only [Complex.add_re, Complex.mul_re, Complex.conj_re,
        Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
      ring
    rw [h1] at h0
    exact h0
  have hdisc := discrim_le_zero hquad
  rw [discrim] at hdisc
  nlinarith [hdisc]

omit [FiniteDimensional ℂ E] in
/-- A positive operator dominated by `ε I` has norm at most `ε`. -/
theorem isPositive_norm_le_of_le_smul_one {A : E →L[ℂ] E} {ε : ℝ}
    (hε : 0 ≤ ε) (hA : A.IsPositive)
    (hle : (((ε : ℝ) : ℂ) • (1 : E →L[ℂ] E) - A).IsPositive) :
    ‖A‖ ≤ ε := by
  refine ContinuousLinearMap.opNorm_le_bound A hε fun x => ?_
  have hbound : ∀ z : E, (⟪A z, z⟫).re ≤ ε * ‖z‖ ^ 2 := by
    intro z
    have h0 := hle.2 z
    unfold ContinuousLinearMap.reApplyInnerSelf at h0
    rw [RCLike.re_to_complex] at h0
    have h1 : (((ε : ℝ) : ℂ) • (1 : E →L[ℂ] E) - A) z
        = ((ε : ℝ) : ℂ) • z - A z := by
      rw [_root_.sub_apply, _root_.smul_apply, one_apply_eq_self]
    rw [h1, inner_sub_left, inner_smul_left] at h0
    simp only [Complex.sub_re, Complex.mul_re, Complex.conj_re,
      Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im] at h0
    have h2 := cre_inner_self z
    nlinarith [h2]
  have hCS := isPositive_re_inner_sq_le hA x (A x)
  have h3 : (⟪A x, A x⟫).re = ‖A x‖ ^ 2 := cre_inner_self (A x)
  have h4 : (⟪A (A x), A x⟫).re ≤ ε * ‖A x‖ ^ 2 := hbound (A x)
  have h5 : (⟪A x, x⟫).re ≤ ε * ‖x‖ ^ 2 := hbound x
  have hCSre : (⟪A x, A x⟫).re ^ 2
      ≤ (⟪A x, x⟫).re * (⟪A (A x), A x⟫).re := by
    have hswap := isPositive_re_inner_sq_le hA x (A x)
    calc (⟪A x, A x⟫).re ^ 2 = ((⟪A x, A x⟫).re) ^ 2 := rfl
      _ ≤ (⟪A x, x⟫).re * (⟪A (A x), A x⟫).re := hswap
  have hsq2 : ‖A x‖ ^ 2 * ‖A x‖ ^ 2 ≤ (ε * ‖x‖) ^ 2 * ‖A x‖ ^ 2 := by
    have hnn1 : 0 ≤ (⟪A x, x⟫).re := hA.2 x
    have hnn2 : 0 ≤ (⟪A (A x), A x⟫).re := hA.2 (A x)
    rw [h3] at hCSre
    nlinarith [norm_nonneg (A x), norm_nonneg x]
  by_cases hzero : ‖A x‖ = 0
  · rw [hzero]
    positivity
  · have hpos : 0 < ‖A x‖ ^ 2 := by positivity
    have hsq3 : ‖A x‖ ^ 2 ≤ (ε * ‖x‖) ^ 2 :=
      le_of_mul_le_mul_right (by nlinarith) hpos
    calc ‖A x‖ = Real.sqrt (‖A x‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt ((ε * ‖x‖) ^ 2) := Real.sqrt_le_sqrt hsq3
      _ = ε * ‖x‖ := Real.sqrt_sq (by positivity)

/-- **(record 8, landing)** Under the uniform temporal-tail sandwich
(DYN.11) and the per-bank convergence supplied by (C2), the transported
residual Grams converge in operator norm to a unique positive limit,
independently of the cofinal route. -/
theorem cofinal_residual_landing
    (Rbank : ℕ → ℕ → (E →L[ℂ] E)) (Rdyn : ℕ → (E →L[ℂ] E))
    (Rlim : ℕ → (E →L[ℂ] E)) (ε : ℕ → ℝ)
    (hεnn : ∀ m, 0 ≤ ε m) (hε : Tendsto ε atTop (𝓝 0))
    (hsandwichPos : ∀ n m, (Rbank n m - Rdyn n).IsPositive)
    (hsandwich : ∀ n m, (((ε m : ℝ) : ℂ) • (1 : E →L[ℂ] E)
      - (Rbank n m - Rdyn n)).IsPositive)
    (hbank : ∀ m, Tendsto (fun n => Rbank n m) atTop (𝓝 (Rlim m))) :
    ∃ Rinf : E →L[ℂ] E,
      Tendsto (fun n => Rdyn n) atTop (𝓝 Rinf)
      ∧ ((∀ n, (Rdyn n).IsPositive) → Rinf.IsPositive)
      ∧ ∀ (φ : ℕ → ℕ), Tendsto φ atTop atTop → ∀ L,
          Tendsto (fun k => Rdyn (φ k)) atTop (𝓝 L) → L = Rinf := by
  -- the residual sequence is uniformly Cauchy against the banks
  have hnorm : ∀ n m, ‖Rbank n m - Rdyn n‖ ≤ ε m := fun n m =>
    isPositive_norm_le_of_le_smul_one (hεnn m) (hsandwichPos n m)
      (hsandwich n m)
  have hcauchy : CauchySeq fun n => Rdyn n := by
    rw [Metric.cauchySeq_iff]
    intro δ hδ
    obtain ⟨m₀, hm₀⟩ := (Metric.tendsto_atTop.mp hε) (δ / 4) (by linarith)
    have hεsmall : ε m₀ < δ / 4 := by
      have := hm₀ m₀ le_rfl
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (hεnn m₀)] at this
      exact this
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hbank m₀) (δ / 4)
      (by linarith)
    refine ⟨N, fun p hp q hq => ?_⟩
    have h1 := hN p hp
    have h2 := hN q hq
    rw [dist_eq_norm] at h1 h2 ⊢
    have hexp : Rdyn p - Rdyn q
        = (Rdyn p - Rbank p m₀) + (Rbank p m₀ - Rbank q m₀)
          + (Rbank q m₀ - Rdyn q) := by
      abel
    have hb1 : ‖Rdyn p - Rbank p m₀‖ ≤ ε m₀ := by
      rw [norm_sub_rev]
      exact hnorm p m₀
    have hb3 : ‖Rbank q m₀ - Rdyn q‖ ≤ ε m₀ := hnorm q m₀
    have hb2 : ‖Rbank p m₀ - Rbank q m₀‖ < δ / 2 := by
      have hx : Rbank p m₀ - Rbank q m₀
          = (Rbank p m₀ - Rlim m₀) - (Rbank q m₀ - Rlim m₀) := by
        abel
      rw [hx]
      calc ‖(Rbank p m₀ - Rlim m₀) - (Rbank q m₀ - Rlim m₀)‖
          ≤ ‖Rbank p m₀ - Rlim m₀‖ + ‖Rbank q m₀ - Rlim m₀‖ :=
            norm_sub_le _ _
        _ < δ / 4 + δ / 4 := by
            have hh1 : ‖Rbank p m₀ - Rlim m₀‖ < δ / 4 := by
              have := hN p hp
              rwa [dist_eq_norm] at this
            have hh2 : ‖Rbank q m₀ - Rlim m₀‖ < δ / 4 := by
              have := hN q hq
              rwa [dist_eq_norm] at this
            linarith
        _ = δ / 2 := by ring
    calc ‖Rdyn p - Rdyn q‖
        ≤ ‖Rdyn p - Rbank p m₀‖ + ‖Rbank p m₀ - Rbank q m₀‖
          + ‖Rbank q m₀ - Rdyn q‖ := by
          rw [hexp]
          exact norm_add₃_le
      _ < ε m₀ + δ / 2 + ε m₀ := by
          have := hb1
          have := hb3
          linarith
      _ < δ := by linarith
  obtain ⟨Rinf, hRinf⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨Rinf, hRinf, ?_, ?_⟩
  · -- positivity of the limit
    intro hpos
    constructor
    · intro x y
      have h1 : Tendsto (fun n => ⟪Rdyn n x, y⟫) atTop (𝓝 ⟪Rinf x, y⟫) := by
        have hx : Tendsto (fun n => Rdyn n x) atTop (𝓝 (Rinf x)) := by
          exact (isBoundedBilinearMap_apply.continuous.tendsto _).comp
            (hRinf.prodMk_nhds tendsto_const_nhds)
        exact ((continuous_inner.tendsto _).comp
          (hx.prodMk_nhds tendsto_const_nhds))
      have h2 : Tendsto (fun n => ⟪x, Rdyn n y⟫) atTop (𝓝 ⟪x, Rinf y⟫) := by
        have hy : Tendsto (fun n => Rdyn n y) atTop (𝓝 (Rinf y)) := by
          exact (isBoundedBilinearMap_apply.continuous.tendsto _).comp
            (hRinf.prodMk_nhds tendsto_const_nhds)
        exact ((continuous_inner.tendsto _).comp
          (tendsto_const_nhds.prodMk_nhds hy))
      have heq : ∀ n, ⟪Rdyn n x, y⟫ = ⟪x, Rdyn n y⟫ := fun n =>
        (hpos n).isSymmetric x y
      exact tendsto_nhds_unique (h1.congr fun n => heq n) h2
    · intro x
      have h1 : Tendsto (fun n =>
          ContinuousLinearMap.reApplyInnerSelf (Rdyn n) x) atTop
          (𝓝 (ContinuousLinearMap.reApplyInnerSelf Rinf x)) := by
        have hx : Tendsto (fun n => Rdyn n x) atTop (𝓝 (Rinf x)) :=
          (isBoundedBilinearMap_apply.continuous.tendsto _).comp
            (hRinf.prodMk_nhds tendsto_const_nhds)
        have h2 : Tendsto (fun n => ⟪Rdyn n x, x⟫) atTop
            (𝓝 ⟪Rinf x, x⟫) :=
          (continuous_inner.tendsto _).comp
            (hx.prodMk_nhds tendsto_const_nhds)
        exact (Complex.continuous_re.tendsto _).comp h2
      exact le_of_tendsto_of_tendsto tendsto_const_nhds h1
        (Filter.Eventually.of_forall fun n => (hpos n).2 x)
  · -- cofinal route independence
    intro φ hφ L hL
    exact tendsto_nhds_unique hL (hRinf.comp hφ)

omit [FiniteDimensional ℂ E] in
/-- A positive operator with vanishing diagonal pairing at a vector kills
that vector. -/
theorem isPositive_apply_eq_zero_of_re_inner {R : E →L[ℂ] E}
    (hR : R.IsPositive) {z : E} (hz : (⟪R z, z⟫).re = 0) : R z = 0 := by
  have hCS := isPositive_re_inner_sq_le hR z (R z)
  have h3 : (⟪R z, R z⟫).re = ‖R z‖ ^ 2 := cre_inner_self (R z)
  rw [hz, h3, zero_mul] at hCS
  have h4 : ‖R z‖ ^ 2 = 0 := by nlinarith [sq_nonneg (‖R z‖ ^ 2)]
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg (R z)])

/-- **(DYN.12)** A nonzero positive residual has a strictly positive
least eigenvalue on its support: `R ⪰ r_* P_*` with `r_* > 0` and `P_*`
the orthogonal projection onto `(ker R)ᗮ` (the spectral projection
`1_{(0,∞)}(R)` of the PSD limit). -/
theorem dynamic_source_spectral_floor {R : E →L[ℂ] E}
    (hR : R.IsPositive) (hne : R ≠ 0) :
    ∃ r : ℝ, 0 < r ∧
      (R - ((r : ℝ) : ℂ)
        • ((LinearMap.ker (R : E →ₗ[ℂ] E))ᗮ).starProjection).IsPositive := by
  set K : Submodule ℂ E := (LinearMap.ker (R : E →ₗ[ℂ] E))ᗮ with hK
  have hKorth : Kᗮ = LinearMap.ker (R : E →ₗ[ℂ] E) := by
    rw [hK, Submodule.orthogonal_orthogonal]
  -- the support is nontrivial
  have hKne : K ≠ ⊥ := by
    intro hbot
    refine hne ?_
    ext x
    have hx : x ∈ LinearMap.ker (R : E →ₗ[ℂ] E) := by
      rw [← hKorth, hbot, Submodule.bot_orthogonal_eq_top]
      trivial
    exact hx
  -- the compact unit sphere of the support
  set f : E → ℝ := fun z => (⟪R z, z⟫).re with hf
  set S : Set E := (K : Set E) ∩ Metric.sphere 0 1 with hS
  have hScompact : IsCompact S :=
    IsCompact.inter_left (isCompact_sphere 0 1) K.closed_of_finiteDimensional
  have hSne : S.Nonempty := by
    obtain ⟨v, hv, hvne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hKne
    have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hvne
    refine ⟨((‖v‖⁻¹ : ℝ) : ℂ) • v, K.smul_mem _ hv, ?_⟩
    simp only [Metric.mem_sphere, dist_zero_right]
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hvpos), inv_mul_cancel₀ hvpos.ne']
  have hcont : ContinuousOn f S := by
    refine Continuous.continuousOn ?_
    exact Complex.continuous_re.comp
      (continuous_inner.comp (R.continuous.prodMk continuous_id))
  obtain ⟨z₀, hz₀S, hmin⟩ := hScompact.exists_isMinOn hSne hcont
  set r : ℝ := f z₀ with hr
  have hz₀K : z₀ ∈ K := hz₀S.1
  have hz₀norm : ‖z₀‖ = 1 := by
    have h := hz₀S.2
    simpa [Metric.mem_sphere, dist_zero_right] using h
  have hrnn : 0 ≤ r := by
    have h := hR.2 z₀
    unfold ContinuousLinearMap.reApplyInnerSelf at h
    rwa [RCLike.re_to_complex] at h
  have hrpos : 0 < r := by
    rcases lt_or_eq_of_le hrnn with h | h
    · exact h
    · exfalso
      have hz : R z₀ = 0 := isPositive_apply_eq_zero_of_re_inner hR h.symm
      have hker : z₀ ∈ LinearMap.ker (R : E →ₗ[ℂ] E) := hz
      have hinner : ⟪z₀, z₀⟫ = 0 := by
        have h2 : z₀ ∈ Kᗮ := by
          rw [hKorth]
          exact hker
        exact (Submodule.mem_orthogonal K z₀).mp h2 z₀ hz₀K
      have hzero : z₀ = 0 := inner_self_eq_zero.mp hinner
      rw [hzero, norm_zero] at hz₀norm
      exact zero_ne_one hz₀norm
  refine ⟨r, hrpos, ?_, ?_⟩
  · -- symmetric part
    intro x y
    have h1 : ⟪R x, y⟫ = ⟪x, R y⟫ := hR.isSymmetric x y
    have h2 : ⟪K.starProjection x, y⟫ = ⟪x, K.starProjection y⟫ :=
      K.starProjection_isSymmetric x y
    have h3 : ∀ w : E, (R - ((r : ℝ) : ℂ) • K.starProjection) w
        = R w - ((r : ℝ) : ℂ) • K.starProjection w := fun w => rfl
    change ⟪(R - ((r : ℝ) : ℂ) • K.starProjection) x, y⟫
      = ⟪x, (R - ((r : ℝ) : ℂ) • K.starProjection) y⟫
    rw [h3, h3, inner_sub_left, inner_sub_right, inner_smul_left,
      inner_smul_right, h1, h2, Complex.conj_ofReal]
  · -- positivity
    intro x
    unfold ContinuousLinearMap.reApplyInnerSelf
    rw [RCLike.re_to_complex]
    have happ : (R - ((r : ℝ) : ℂ) • K.starProjection) x
        = R x - ((r : ℝ) : ℂ) • K.starProjection x := rfl
    rw [happ, inner_sub_left, inner_smul_left, Complex.conj_ofReal]
    set u : E := K.starProjection x with hu
    have hproj : (⟪u, x⟫).re = ‖u‖ ^ 2 := re_inner_starProjection_self K x
    have hxu : x - u ∈ Kᗮ := K.sub_starProjection_mem_orthogonal x
    have hRxu : R (x - u) = 0 := by
      have h := hxu
      rw [hKorth] at h
      exact h
    have hRx : R x = R u := by
      have h := map_sub R x u
      rw [hRxu] at h
      exact (sub_eq_zero.mp h.symm)
    have hcross : ⟪R u, x - u⟫ = 0 := by
      have h := hR.isSymmetric u (x - u)
      calc ⟪R u, x - u⟫ = ⟪u, R (x - u)⟫ := h
        _ = 0 := by rw [hRxu, inner_zero_right]
    have hsplit : ⟪R x, x⟫ = ⟪R u, u⟫ := by
      calc ⟪R x, x⟫ = ⟪R u, u + (x - u)⟫ := by
            rw [hRx]
            congr 1
            abel
        _ = ⟪R u, u⟫ + ⟪R u, x - u⟫ := inner_add_right _ _ _
        _ = ⟪R u, u⟫ := by rw [hcross, add_zero]
    have hfloor : r * ‖u‖ ^ 2 ≤ (⟪R u, u⟫).re := by
      by_cases huz : u = 0
      · rw [huz]
        simp
      · have hupos : 0 < ‖u‖ := norm_pos_iff.mpr huz
        have humem : u ∈ K := K.starProjection_apply_mem x
        set w : E := ((‖u‖⁻¹ : ℝ) : ℂ) • u with hw
        have hwS : w ∈ S := by
          refine ⟨K.smul_mem _ humem, ?_⟩
          simp only [Metric.mem_sphere, dist_zero_right]
          rw [hw, norm_smul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (inv_pos.mpr hupos), inv_mul_cancel₀ hupos.ne']
        have hminw : r ≤ f w := hmin hwS
        have hscale : f w = ‖u‖⁻¹ * (‖u‖⁻¹ * (⟪R u, u⟫).re) := by
          rw [hf]
          simp only
          rw [hw, map_smul, inner_smul_left, inner_smul_right,
            Complex.conj_ofReal, Complex.re_ofReal_mul,
            Complex.re_ofReal_mul]
        rw [hscale] at hminw
        have h1 : r * (‖u‖ * ‖u‖)
            ≤ (‖u‖⁻¹ * (‖u‖⁻¹ * (⟪R u, u⟫).re)) * (‖u‖ * ‖u‖) :=
          mul_le_mul_of_nonneg_right hminw (by positivity)
        have h2 : (‖u‖⁻¹ * (‖u‖⁻¹ * (⟪R u, u⟫).re)) * (‖u‖ * ‖u‖)
            = (⟪R u, u⟫).re := by
          field_simp
        rw [pow_two]
        linarith
    have hfin : (⟪R x, x⟫).re = (⟪R u, u⟫).re := by rw [hsplit]
    rw [Complex.sub_re, hfin, Complex.re_ofReal_mul, hproj]
    linarith

section MinimalRealization

variable {V₂ : Type*} [NormedAddCommGroup V₂] [InnerProductSpace ℂ V₂]
  [FiniteDimensional ℂ V₂]

/-- **(record 8, closing clause)** Unitary uniqueness of minimal
source-cyclic realizations: two source-cyclic realizations of one delayed
kernel `t ↦ J^* e^{-tH} J` (`t ≥ 0`) are intertwined by a unitary
identifying the source syntheses and the semigroups. -/
theorem minimal_cyclic_realization_unique
    {H₁ : V →L[ℂ] V} {H₂ : V₂ →L[ℂ] V₂}
    (hH₁ : IsSelfAdjoint H₁) (hH₂ : IsSelfAdjoint H₂)
    (J₁ : E' →L[ℂ] V) (J₂ : E' →L[ℂ] V₂)
    (hmin₁ : cyc H₁ J₁ = ⊤) (hmin₂ : cyc H₂ J₂ = ⊤)
    (hkernel : ∀ t : ℝ, 0 ≤ t →
      (J₁†) ∘L expH H₁ t ∘L J₁ = (J₂†) ∘L expH H₂ t ∘L J₂) :
    ∃ U : V ≃ₗᵢ[ℂ] V₂,
      (∀ u : E', U (J₁ u) = J₂ u)
      ∧ ∀ t : ℝ, 0 ≤ t → ∀ v : V, U (expH H₁ t v) = expH H₂ t (U v) := by
  classical
  -- Gram matching of the semigroup generators
  have hgram : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → ∀ u v : E',
      ⟪expH H₁ s (J₁ u), expH H₁ t (J₁ v)⟫
        = ⟪expH H₂ s (J₂ u), expH H₂ t (J₂ v)⟫ := by
    intro s t hs ht u v
    have hL : ⟪expH H₁ s (J₁ u), expH H₁ t (J₁ v)⟫
        = ⟪u, ((J₁†) ∘L expH H₁ (s + t) ∘L J₁) v⟫ := by
      have h1 := ContinuousLinearMap.adjoint_inner_left (expH H₁ s)
        (expH H₁ t (J₁ v)) (J₁ u)
      rw [expH_adjoint hH₁] at h1
      have h2 : expH H₁ s (expH H₁ t (J₁ v)) = expH H₁ (s + t) (J₁ v) :=
        congrArg (fun A : V →L[ℂ] V => A (J₁ v)) (expH_mul H₁ s t)
      have h3 := ContinuousLinearMap.adjoint_inner_right J₁
        u (expH H₁ (s + t) (J₁ v))
      rw [h1, h2, ← h3]
      rfl
    have hRr : ⟪expH H₂ s (J₂ u), expH H₂ t (J₂ v)⟫
        = ⟪u, ((J₂†) ∘L expH H₂ (s + t) ∘L J₂) v⟫ := by
      have h1 := ContinuousLinearMap.adjoint_inner_left (expH H₂ s)
        (expH H₂ t (J₂ v)) (J₂ u)
      rw [expH_adjoint hH₂] at h1
      have h2 : expH H₂ s (expH H₂ t (J₂ v)) = expH H₂ (s + t) (J₂ v) :=
        congrArg (fun A : V₂ →L[ℂ] V₂ => A (J₂ v)) (expH_mul H₂ s t)
      have h3 := ContinuousLinearMap.adjoint_inner_right J₂
        u (expH H₂ (s + t) (J₂ v))
      rw [h1, h2, ← h3]
      rfl
    rw [hL, hRr, hkernel (s + t) (by linarith)]
  -- represent a basis of the first carrier in the generators
  set n := Module.finrank ℂ V with hn
  set b : Module.Basis (Fin n) ℂ V := Module.finBasis ℂ V with hb
  have hrep : ∀ j : Fin n, ∃ (k : ℕ) (c : Fin k → ℂ)
      (ts : Fin k → ℝ) (us : Fin k → E'),
      (∀ l, 0 ≤ ts l)
      ∧ b j = ∑ l, c l • expH H₁ (ts l) (J₁ (us l)) := by
    intro j
    have hmem : b j ∈ cyc H₁ J₁ := by
      rw [hmin₁]
      trivial
    rw [cyc, bankSpan] at hmem
    obtain ⟨k, c, g, hsum⟩ := mem_span_set'.mp hmem
    choose ts hts us hval using fun l : Fin k => (g l).2
    refine ⟨k, c, ts, us, fun l => Set.mem_Ici.mp (hts l), ?_⟩
    rw [← hsum]
    exact (Finset.sum_congr rfl fun l _ => by rw [hval l]).symm
  choose k c ts us hts hval using hrep
  -- the transported linear map
  set L : V →ₗ[ℂ] V₂ := Module.Basis.constr b ℂ
    (fun j => ∑ l, c j l • expH H₂ (ts j l) (J₂ (us j l))) with hL
  have hLb : ∀ j : Fin n,
      L (b j) = ∑ l, c j l • expH H₂ (ts j l) (J₂ (us j l)) := fun j =>
    Module.Basis.constr_basis b ℂ _ j
  -- the transported functional identity on generators
  have hbasisfun : ∀ (t : ℝ), 0 ≤ t → ∀ (v : E') (j : Fin n),
      ⟪expH H₂ t (J₂ v), L (b j)⟫ = ⟪expH H₁ t (J₁ v), b j⟫ := by
    intro t ht v j
    rw [hLb j, hval j, inner_sum, inner_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [inner_smul_right, inner_smul_right,
      hgram t (ts j l) ht (hts j l) v (us j l)]
  have hfun : ∀ (t : ℝ), 0 ≤ t → ∀ (v : E') (x : V),
      ⟪expH H₂ t (J₂ v), L x⟫ = ⟪expH H₁ t (J₁ v), x⟫ := by
    intro t ht v x
    calc ⟪expH H₂ t (J₂ v), L x⟫
        = ⟪expH H₂ t (J₂ v), L (∑ j, b.repr x j • b j)⟫ := by
          rw [Module.Basis.sum_repr]
      _ = ∑ j, b.repr x j * ⟪expH H₂ t (J₂ v), L (b j)⟫ := by
          rw [map_sum, inner_sum]
          exact Finset.sum_congr rfl fun j _ => by
            rw [map_smul, inner_smul_right]
      _ = ∑ j, b.repr x j * ⟪expH H₁ t (J₁ v), b j⟫ :=
          Finset.sum_congr rfl fun j _ => by rw [hbasisfun t ht v j]
      _ = ⟪expH H₁ t (J₁ v), ∑ j, b.repr x j • b j⟫ := by
          rw [inner_sum]
          exact Finset.sum_congr rfl fun j _ => by rw [inner_smul_right]
      _ = ⟪expH H₁ t (J₁ v), x⟫ := by rw [Module.Basis.sum_repr]
  have hfun' : ∀ (t : ℝ), 0 ≤ t → ∀ (v : E') (x : V),
      ⟪L x, expH H₂ t (J₂ v)⟫ = ⟪x, expH H₁ t (J₁ v)⟫ := by
    intro t ht v x
    calc ⟪L x, expH H₂ t (J₂ v)⟫
        = starRingEnd ℂ ⟪expH H₂ t (J₂ v), L x⟫ := by
          rw [inner_conj_symm]
      _ = starRingEnd ℂ ⟪expH H₁ t (J₁ v), x⟫ := by rw [hfun t ht v x]
      _ = ⟪x, expH H₁ t (J₁ v)⟫ := by rw [inner_conj_symm]
  -- the map transports every generator
  have hLgen : ∀ (t : ℝ), 0 ≤ t → ∀ u : E',
      L (expH H₁ t (J₁ u)) = expH H₂ t (J₂ u) := by
    intro t ht u
    have hdiff : ∀ w : V₂, ⟪w, L (expH H₁ t (J₁ u))
        - expH H₂ t (J₂ u)⟫ = 0 := by
      intro w
      have hw : w ∈ cyc H₂ J₂ := by
        rw [hmin₂]
        trivial
      induction hw using Submodule.span_induction with
      | mem w hwmem =>
        obtain ⟨s, hs, v, rfl⟩ := hwmem
        rw [inner_sub_right, hfun s hs v (expH H₁ t (J₁ u)),
          hgram s t hs ht v u, sub_self]
      | zero => rw [inner_zero_left]
      | add w₁ w₂ _ _ h₁ h₂ => rw [inner_add_left, h₁, h₂, add_zero]
      | smul a w _ hw' => rw [inner_smul_left, hw', mul_zero]
    have h0 := ext_inner_left ℂ (x := L (expH H₁ t (J₁ u))
      - expH H₂ t (J₂ u)) (y := 0) fun w => by
      rw [hdiff w, inner_zero_right]
    exact sub_eq_zero.mp h0
  -- isometry
  have hLinner : ∀ x y : V, ⟪L x, L y⟫ = ⟪x, y⟫ := by
    intro x y
    calc ⟪L x, L y⟫ = ⟪L x, L (∑ j, b.repr y j • b j)⟫ := by
          rw [Module.Basis.sum_repr]
      _ = ∑ j, b.repr y j * ⟪L x, L (b j)⟫ := by
          rw [map_sum, inner_sum]
          exact Finset.sum_congr rfl fun j _ => by
            rw [map_smul, inner_smul_right]
      _ = ∑ j, b.repr y j * ⟪x, b j⟫ := by
          refine Finset.sum_congr rfl fun j _ => ?_
          congr 1
          calc ⟪L x, L (b j)⟫
              = ⟪L x, ∑ l, c j l • expH H₂ (ts j l) (J₂ (us j l))⟫ := by
                rw [hLb j]
            _ = ∑ l, c j l
                * ⟪L x, expH H₂ (ts j l) (J₂ (us j l))⟫ := by
                rw [inner_sum]
                exact Finset.sum_congr rfl fun l _ => by
                  rw [inner_smul_right]
            _ = ∑ l, c j l
                * ⟪x, expH H₁ (ts j l) (J₁ (us j l))⟫ :=
                Finset.sum_congr rfl fun l _ => by
                  rw [hfun' (ts j l) (hts j l) (us j l) x]
            _ = ⟪x, ∑ l, c j l • expH H₁ (ts j l) (J₁ (us j l))⟫ := by
                rw [inner_sum]
                exact (Finset.sum_congr rfl fun l _ => by
                  rw [inner_smul_right]).symm
            _ = ⟪x, b j⟫ := by rw [← hval j]
      _ = ⟪x, ∑ j, b.repr y j • b j⟫ := by
          rw [inner_sum]
          exact (Finset.sum_congr rfl fun j _ => by
            rw [inner_smul_right]).symm
      _ = ⟪x, y⟫ := by rw [Module.Basis.sum_repr]
  have hLnorm : ∀ x : V, ‖L x‖ = ‖x‖ := by
    intro x
    have h1 : ‖L x‖ ^ 2 = ‖x‖ ^ 2 := by
      rw [← cre_inner_self (L x), ← cre_inner_self x, hLinner x x]
    have h2 := norm_nonneg (L x)
    have h3 := norm_nonneg x
    nlinarith
  set Liso : V →ₗᵢ[ℂ] V₂ := ⟨L, hLnorm⟩ with hLiso
  -- surjectivity from cyclicity of the second realization
  have hsurj : Function.Surjective Liso := by
    have hrange : cyc H₂ J₂ ≤ LinearMap.range L := by
      refine Submodule.span_le.mpr ?_
      rintro w ⟨t, ht, u, rfl⟩
      exact ⟨expH H₁ t (J₁ u), hLgen t ht u⟩
    intro w
    have hw : w ∈ LinearMap.range L := hrange (by rw [hmin₂]; trivial)
    obtain ⟨x, hx⟩ := hw
    exact ⟨x, hx⟩
  set U : V ≃ₗᵢ[ℂ] V₂ := LinearIsometryEquiv.ofSurjective Liso hsurj
    with hU
  have hUapp : ∀ x : V, U x = L x := fun x => rfl
  refine ⟨U, fun u => ?_, ?_⟩
  · rw [hUapp]
    have h := hLgen 0 le_rfl u
    rw [expH_zero, expH_zero, one_apply_eq_self, one_apply_eq_self] at h
    exact h
  · intro t ht v
    rw [hUapp, hUapp]
    -- extend the generator intertwining by linearity
    have hv : v ∈ cyc H₁ J₁ := by
      rw [hmin₁]
      trivial
    induction hv using Submodule.span_induction with
    | mem w hwmem =>
      obtain ⟨s, hs, u, rfl⟩ := hwmem
      have h1 : expH H₁ t (expH H₁ s (J₁ u))
          = expH H₁ (t + s) (J₁ u) :=
        congrArg (fun A : V →L[ℂ] V => A (J₁ u)) (expH_mul H₁ t s)
      have h2 : expH H₂ t (expH H₂ s (J₂ u))
          = expH H₂ (t + s) (J₂ u) :=
        congrArg (fun A : V₂ →L[ℂ] V₂ => A (J₂ u)) (expH_mul H₂ t s)
      rw [h1, hLgen (t + s) (add_nonneg ht (Set.mem_Ici.mp hs)) u,
        hLgen s (Set.mem_Ici.mp hs) u, h2]
    | zero =>
      simp only [map_zero]
    | add w₁ w₂ _ _ h₁ h₂ =>
      simp only [map_add]
      rw [h₁, h₂]
    | smul a w _ h₁ =>
      simp only [map_smul]
      rw [h₁]

end MinimalRealization

end CofinalDynamicSource

/-! ### `prop:GT-joint-tangent-stabilizer`

Rendering (JT.1–JT.4): joint source measures are countably additive
`Matrix E E ℂ`-valued vector measures on the joint carrier
`(0, ∞) × K`, `K` a compact metric momentum window, that are PSD on every
measurable set; the holonomy relation (JT.1) is conjugation of the vector
measure; (JT.3) is the equivalence between equality of the two routes and
membership of the holonomy in the stabilizer; (JT.4) produces, from any
Borel witness of stabilizer failure, a compactly supported continuous
test `f ∈ C_c((0,∞) × K, ℝ)` and a unit direction `c` whose scalarized
lifetime measures (genuine Borel measures) are separated by `f` — via the
Riesz–Markov uniqueness of regular measures against `C_c`.  The final
strictness clause is the explicit two-atom witness
`joint_stabilizer_strictly_finer`. -/

section JointTangentStabilizer

open MeasureTheory
open scoped ENNReal CompactlySupported

variable {K : Type} [MetricSpace K] [CompactSpace K]
  [MeasurableSpace K] [BorelSpace K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The joint route carrier `(0, ∞) × K`. -/
abbrev jointCarrier (K : Type) [MetricSpace K] : Type :=
  ↥(Set.Ioi (0 : ℝ)) × K

/-- The positive half-line is locally compact. -/
instance : LocallyCompactSpace ↥(Set.Ioi (0 : ℝ)) :=
  isOpen_Ioi.locallyCompactSpace

/-- The conjugated (direct-route) joint source measure
`A ↦ 𝕳^* μ(A) 𝕳` (JT.1). -/
noncomputable def conjVM (μ : VectorMeasure (jointCarrier K) (Matrix ι ι ℂ))
    (U : Matrix ι ι ℂ) : VectorMeasure (jointCarrier K) (Matrix ι ι ℂ) :=
  μ.mapRange (AddMonoidHom.mk' (fun M => Uᴴ * M * U) fun M N => by
    rw [Matrix.mul_add, Matrix.add_mul])
    (by
      have h1 : Continuous fun M : Matrix ι ι ℂ => Uᴴ * M * U := by
        refine continuous_pi fun i => continuous_pi fun j => ?_
        have h2 : (fun M : Matrix ι ι ℂ => (Uᴴ * M * U) i j)
            = fun M => ∑ a, (∑ b, Uᴴ i b * M b a) * U a j := rfl
        rw [h2]
        refine continuous_finsetSum _ fun a _ => Continuous.mul ?_
          continuous_const
        refine continuous_finsetSum _ fun b _ => Continuous.mul
          continuous_const ?_
        exact (continuous_apply a).comp (continuous_apply b)
      exact h1)

omit [CompactSpace K] [BorelSpace K] [DecidableEq ι] in
/-- Value of the conjugated joint measure. -/
theorem conjVM_apply (μ : VectorMeasure (jointCarrier K) (Matrix ι ι ℂ))
    (U : Matrix ι ι ℂ) (A : Set (jointCarrier K)) :
    conjVM μ U A = Uᴴ * μ A * U :=
  VectorMeasure.mapRange_apply _ _

omit [CompactSpace K] [BorelSpace K] [DecidableEq ι] in
/-- **(JT.3)** The staged and direct routes define the same labelled
joint source exactly when the holonomy lies in the joint stabilizer. -/
theorem joint_tangent_stabilizer_iff
    (μ : VectorMeasure (jointCarrier K) (Matrix ι ι ℂ))
    (U : Matrix ι ι ℂ) :
    conjVM μ U = μ
      ↔ ∀ A : Set (jointCarrier K), MeasurableSet A
          → Uᴴ * μ A * U = μ A := by
  constructor
  · intro h A _
    rw [← conjVM_apply μ U A, h]
  · intro h
    refine VectorMeasure.ext fun A hA => ?_
    rw [conjVM_apply μ U A, h A hA]

/-- The scalarized joint source measure along a direction `c`: a genuine
Borel measure on the joint carrier. -/
noncomputable def vmScal (μ : VectorMeasure (jointCarrier K) (Matrix ι ι ℂ))
    (hpos : ∀ A : Set (jointCarrier K), MeasurableSet A → (μ A).PosSemidef)
    (c : ι → ℂ) : Measure (jointCarrier K) :=
  Measure.ofMeasurable
    (fun A _ => ENNReal.ofReal ((star c ⬝ᵥ (μ A *ᵥ c)).re))
    (by
      rw [VectorMeasure.empty]
      simp)
    (by
      intro f hmeas hdisj
      have hs := μ.m_iUnion hmeas hdisj
      have hφ : Continuous fun M : Matrix ι ι ℂ =>
          (star c ⬝ᵥ (M *ᵥ c)).re := by
        refine Complex.continuous_re.comp ?_
        have h2 : (fun M : Matrix ι ι ℂ => star c ⬝ᵥ (M *ᵥ c))
            = fun M => ∑ i, star c i * ∑ j, M i j * c j := rfl
        rw [h2]
        refine continuous_finsetSum _ fun i _ => Continuous.mul
          continuous_const ?_
        refine continuous_finsetSum _ fun j _ => Continuous.mul ?_
          continuous_const
        exact (continuous_apply j).comp (continuous_apply i)
      have hsum : HasSum (fun i => (star c ⬝ᵥ (μ (f i) *ᵥ c)).re)
          ((star c ⬝ᵥ (μ (⋃ i, f i) *ᵥ c)).re) := by
        have hmap := hs.map
          (AddMonoidHom.mk' (fun M : Matrix ι ι ℂ =>
            (star c ⬝ᵥ (M *ᵥ c)).re) fun M N => by
            rw [Matrix.add_mulVec, dotProduct_add, Complex.add_re]) hφ
        exact hmap
      rw [show ENNReal.ofReal ((star c ⬝ᵥ (μ (⋃ i, f i) *ᵥ c)).re)
          = ENNReal.ofReal (∑' i, (star c ⬝ᵥ (μ (f i) *ᵥ c)).re)
        from by rw [hsum.tsum_eq]]
      exact ENNReal.ofReal_tsum_of_nonneg
        (fun i => re_form_nonneg (hpos (f i) (hmeas i)) c) hsum.summable)

omit [CompactSpace K] [BorelSpace K] [DecidableEq ι] in
/-- Value of the scalarized joint source measure. -/
theorem vmScal_apply (μ : VectorMeasure (jointCarrier K) (Matrix ι ι ℂ))
    (hpos : ∀ A : Set (jointCarrier K), MeasurableSet A → (μ A).PosSemidef)
    (c : ι → ℂ) {A : Set (jointCarrier K)} (hA : MeasurableSet A) :
    vmScal μ hpos c A = ENNReal.ofReal ((star c ⬝ᵥ (μ A *ᵥ c)).re) :=
  Measure.ofMeasurable_apply A hA

/-- The scalarized joint source measures are finite. -/
instance vmScal_isFiniteMeasure
    (μ : VectorMeasure (jointCarrier K) (Matrix ι ι ℂ))
    (hpos : ∀ A : Set (jointCarrier K), MeasurableSet A → (μ A).PosSemidef)
    (c : ι → ℂ) : IsFiniteMeasure (vmScal μ hpos c) := by
  constructor
  rw [vmScal_apply μ hpos c MeasurableSet.univ]
  exact ENNReal.ofReal_lt_top

omit [CompactSpace K] [BorelSpace K] [DecidableEq ι] in
/-- Conjugation by a holonomy preserves positivity. -/
theorem conjVM_pos {μ : VectorMeasure (jointCarrier K) (Matrix ι ι ℂ)}
    (hpos : ∀ A : Set (jointCarrier K), MeasurableSet A → (μ A).PosSemidef)
    (U : Matrix ι ι ℂ) :
    ∀ A : Set (jointCarrier K), MeasurableSet A
      → ((conjVM μ U) A).PosSemidef := by
  intro A hA
  rw [conjVM_apply]
  exact compressed_posSemidef (hpos A hA) U

omit [DecidableEq ι] in
/-- **(JT.4)** If the holonomy fails the joint stabilizer, a compactly
supported continuous test and a unit source direction separate the two
scalarized routes. -/
theorem joint_tangent_separating_test
    (μ : VectorMeasure (jointCarrier K) (Matrix ι ι ℂ))
    (hpos : ∀ A : Set (jointCarrier K), MeasurableSet A → (μ A).PosSemidef)
    (U : Matrix ι ι ℂ) (hfail : ¬ conjVM μ U = μ) :
    ∃ (f : C_c(jointCarrier K, ℝ)) (c : ι → ℂ),
      star c ⬝ᵥ c = 1
      ∧ (∫ z, f z ∂(vmScal (conjVM μ U) (conjVM_pos hpos U) c))
        ≠ ∫ z, f z ∂(vmScal μ hpos c) := by
  classical
  -- a Borel witness of stabilizer failure
  have h1 : ¬ ∀ A : Set (jointCarrier K), MeasurableSet A
      → Uᴴ * μ A * U = μ A := fun h =>
    hfail ((joint_tangent_stabilizer_iff μ U).mpr h)
  push Not at h1
  obtain ⟨A₀, hA₀, hne⟩ := h1
  -- a separating direction, by polarization of the Hermitian forms
  have hconjpos := conjVM_pos hpos U A₀ hA₀
  rw [conjVM_apply] at hconjpos
  have h2 : ¬ ∀ c₀ : ι → ℂ,
      (star c₀ ⬝ᵥ ((Uᴴ * μ A₀ * U) *ᵥ c₀)).re
        = (star c₀ ⬝ᵥ (μ A₀ *ᵥ c₀)).re := by
    intro h
    exact hne (hermitian_eq_of_re_forms hconjpos.1 (hpos A₀ hA₀).1 h)
  push Not at h2
  obtain ⟨c₀, hc₀⟩ := h2
  have hc₀ne : c₀ ≠ 0 := by
    intro h0
    refine hc₀ ?_
    rw [h0]
    simp
  -- normalize the direction
  have hsq : star c₀ ⬝ᵥ c₀ = ((∑ i, ‖c₀ i‖ ^ 2 : ℝ) : ℂ) :=
    star_dot_self_eq_sum_sq c₀
  have hsum_pos : 0 < ∑ i, ‖c₀ i‖ ^ 2 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hc₀ne
    have hlt : (0 : ℝ) < ‖c₀ i‖ ^ 2 := by positivity
    exact lt_of_lt_of_le hlt (Finset.single_le_sum
      (f := fun j => ‖c₀ j‖ ^ 2) (fun j _ => by positivity)
      (Finset.mem_univ i))
  set r : ℝ := Real.sqrt (∑ i, ‖c₀ i‖ ^ 2) with hr
  have hrpos : 0 < r := Real.sqrt_pos.mpr hsum_pos
  set c : ι → ℂ := ((r⁻¹ : ℝ) : ℂ) • c₀ with hc
  have hrr : r * r = ∑ i, ‖c₀ i‖ ^ 2 := Real.mul_self_sqrt hsum_pos.le
  have hcunit : star c ⬝ᵥ c = 1 := by
    rw [hc, star_smul, smul_dotProduct, dotProduct_smul, hsq]
    rw [show star (((r⁻¹ : ℝ) : ℂ)) = ((r⁻¹ : ℝ) : ℂ) from by
      rw [Complex.star_def, Complex.conj_ofReal]]
    rw [smul_eq_mul, smul_eq_mul, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
    rw [show r⁻¹ * (r⁻¹ * ∑ i, ‖c₀ i‖ ^ 2) = 1 from by
      rw [← hrr]
      field_simp]
    exact Complex.ofReal_one
  -- the scaled forms keep the separation
  have hscale : ∀ M : Matrix ι ι ℂ,
      (star c ⬝ᵥ (M *ᵥ c)).re
        = r⁻¹ * (r⁻¹ * (star c₀ ⬝ᵥ (M *ᵥ c₀)).re) := by
    intro M
    rw [hc, star_smul, smul_dotProduct, Matrix.mulVec_smul, dotProduct_smul]
    rw [show star (((r⁻¹ : ℝ) : ℂ)) = ((r⁻¹ : ℝ) : ℂ) from by
      rw [Complex.star_def, Complex.conj_ofReal]]
    rw [smul_eq_mul, smul_eq_mul, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  have hformne : (star c ⬝ᵥ ((Uᴴ * μ A₀ * U) *ᵥ c)).re
      ≠ (star c ⬝ᵥ (μ A₀ *ᵥ c)).re := by
    rw [hscale, hscale]
    intro heq
    refine hc₀ ?_
    have hrne : r⁻¹ ≠ 0 := inv_ne_zero hrpos.ne'
    have h1 := mul_left_cancel₀ hrne heq
    exact mul_left_cancel₀ hrne h1
  -- the scalarized measures differ at the witness set
  have hmeasne : vmScal (conjVM μ U) (conjVM_pos hpos U) c A₀
      ≠ vmScal μ hpos c A₀ := by
    rw [vmScal_apply _ _ _ hA₀, vmScal_apply _ _ _ hA₀, conjVM_apply]
    intro heq
    refine hformne ?_
    refine (ENNReal.ofReal_eq_ofReal_iff ?_ ?_).mp heq
    · exact re_form_nonneg hconjpos c
    · exact re_form_nonneg (hpos A₀ hA₀) c
  -- separate by a compactly supported continuous test
  by_contra hall
  push Not at hall
  have hint : ∀ f : C_c(jointCarrier K, ℝ),
      (∫ z, f z ∂(vmScal (conjVM μ U) (conjVM_pos hpos U) c))
        = ∫ z, f z ∂(vmScal μ hpos c) := by
    intro f
    have h := hall f c
    by_contra hne'
    exact hne' (by
      by_contra hne''
      exact absurd hcunit (by
        intro hcu
        exact hne'' (by
          have := h hcu
          exact this)))
  have hext : vmScal (conjVM μ U) (conjVM_pos hpos U) c = vmScal μ hpos c :=
    MeasureTheory.Measure.ext_of_integral_eq_on_compactlySupported hint
  exact hmeasne (by rw [hext])

/-- A finite scalar route with a fixed matrix weight, as an
operator-valued measure. -/
noncomputable def smulVM (ν : Measure (jointCarrier K)) [IsFiniteMeasure ν]
    (P : Matrix (Fin 2) (Fin 2) ℂ) :
    VectorMeasure (jointCarrier K) (Matrix (Fin 2) (Fin 2) ℂ) :=
  ν.toSignedMeasure.mapRange
    (AddMonoidHom.mk' (fun r : ℝ => (r : ℂ) • P) fun a b => by
      push_cast
      rw [add_smul])
    (Complex.continuous_ofReal.smul continuous_const)

omit [CompactSpace K] [BorelSpace K] in
/-- Value of a weighted scalar route. -/
theorem smulVM_apply (ν : Measure (jointCarrier K)) [IsFiniteMeasure ν]
    (P : Matrix (Fin 2) (Fin 2) ℂ) {A : Set (jointCarrier K)}
    (hA : MeasurableSet A) :
    smulVM ν P A = (((ν A).toReal : ℝ) : ℂ) • P := by
  have h0 : smulVM ν P A = (((ν.toSignedMeasure A : ℝ)) : ℂ) • P := rfl
  rw [h0, MeasureTheory.Measure.toSignedMeasure_apply_measurable hA,
    MeasureTheory.measureReal_def]

/-- **(final clause)** The stabilizer of the energy marginal can be
strictly larger than the joint stabilizer: an explicit two-atom joint
source whose energy marginal is invariant under the swap holonomy while
the joint source is not. -/
theorem joint_stabilizer_strictly_finer {q₁ q₂ : K} (hq : q₁ ≠ q₂) :
    ∃ (μ : VectorMeasure (jointCarrier K) (Matrix (Fin 2) (Fin 2) ℂ))
      (U : Matrix (Fin 2) (Fin 2) ℂ),
      (∀ A : Set (jointCarrier K), MeasurableSet A → (μ A).PosSemidef)
      ∧ Uᴴ * U = 1
      ∧ (∀ B : Set ↥(Set.Ioi (0 : ℝ)), MeasurableSet B →
          Uᴴ * (μ.map Prod.fst) B * U = (μ.map Prod.fst) B)
      ∧ ¬ (∀ A : Set (jointCarrier K), MeasurableSet A →
          Uᴴ * μ A * U = μ A) := by
  classical
  set one : ↥(Set.Ioi (0 : ℝ)) := ⟨1, by norm_num⟩ with hone
  set z₁ : jointCarrier K := (one, q₁) with hz₁
  set z₂ : jointCarrier K := (one, q₂) with hz₂
  set P₁ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 0] with hP₁
  set P₂ : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; 0, 1] with hP₂
  set U : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0] with hU
  set μ := smulVM (Measure.dirac z₁) P₁ + smulVM (Measure.dirac z₂) P₂
    with hμ
  have hz₁₂ : z₁ ≠ z₂ := by
    intro h
    exact hq (congrArg Prod.snd h)
  -- value of the two-atom source
  have hμval : ∀ A : Set (jointCarrier K), MeasurableSet A →
      μ A = (if z₁ ∈ A then (1 : ℂ) else 0) • P₁
        + (if z₂ ∈ A then (1 : ℂ) else 0) • P₂ := by
    intro A hA
    rw [hμ, _root_.add_apply, smulVM_apply _ _ hA,
      smulVM_apply _ _ hA]
    congr 1
    · congr 1
      rw [Measure.dirac_apply' _ hA]
      by_cases h : z₁ ∈ A
      · rw [Set.indicator_of_mem h]
        simp [h]
      · rw [Set.indicator_of_notMem h]
        simp [h]
    · congr 1
      rw [Measure.dirac_apply' _ hA]
      by_cases h : z₂ ∈ A
      · rw [Set.indicator_of_mem h]
        simp [h]
      · rw [Set.indicator_of_notMem h]
        simp [h]
  -- positivity of the weights
  have hP₁psd : P₁.PosSemidef := by
    have h1 : P₁ᴴ * P₁ = P₁ := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [hP₁, Matrix.mul_apply, Fin.sum_univ_two]
    rw [← h1]
    exact Matrix.posSemidef_conjTranspose_mul_self P₁
  have hP₂psd : P₂.PosSemidef := by
    have h1 : P₂ᴴ * P₂ = P₂ := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [hP₂, Matrix.mul_apply, Fin.sum_univ_two]
    rw [← h1]
    exact Matrix.posSemidef_conjTranspose_mul_self P₂
  have hind_nonneg : ∀ (z : jointCarrier K) (A : Set (jointCarrier K))
      (P : Matrix (Fin 2) (Fin 2) ℂ), P.PosSemidef →
      ((if z ∈ A then (1 : ℂ) else 0) • P).PosSemidef := by
    intro z A P hP
    split_ifs
    · rw [one_smul]
      exact hP
    · rw [zero_smul]
      exact Matrix.PosSemidef.zero
  have hUU : Uᴴ * U = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hU, Matrix.mul_apply, Fin.sum_univ_two]
  have hP12 : P₁ + P₂ = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hP₁, hP₂]
  refine ⟨μ, U, ?_, hUU, ?_, ?_⟩
  · intro A hA
    rw [hμval A hA]
    exact (hind_nonneg z₁ A P₁ hP₁psd).add (hind_nonneg z₂ A P₂ hP₂psd)
  · intro B hB
    have hpre : MeasurableSet (Prod.fst ⁻¹' B : Set (jointCarrier K)) :=
      measurable_fst hB
    have hgoal : μ (Prod.fst ⁻¹' B)
        = (if one ∈ B then (1 : ℂ) else 0) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
        := by
      rw [hμval _ hpre]
      by_cases hone_mem : one ∈ B
      · have h1 : z₁ ∈ Prod.fst ⁻¹' B := hone_mem
        have h2 : z₂ ∈ Prod.fst ⁻¹' B := hone_mem
        simp only [h1, h2, hone_mem, ite_true, one_smul]
        rw [hP12]
      · have h1 : z₁ ∉ Prod.fst ⁻¹' B := hone_mem
        have h2 : z₂ ∉ Prod.fst ⁻¹' B := hone_mem
        simp [h1, h2, hone_mem]
    rw [VectorMeasure.map_apply _ measurable_fst hB, hgoal,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hUU]
  · intro hall
    have hsing : MeasurableSet ({z₁} : Set (jointCarrier K)) :=
      measurableSet_singleton z₁
    have hμz : μ {z₁} = P₁ := by
      have h1 : z₁ ∈ ({z₁} : Set (jointCarrier K)) := rfl
      have h2 : z₂ ∉ ({z₁} : Set (jointCarrier K)) := fun h =>
        hz₁₂ (Set.mem_singleton_iff.mp h).symm
      rw [hμval _ hsing]
      simp [h1, h2]
    have h1 := hall {z₁} hsing
    rw [hμz] at h1
    have h2 : (Uᴴ * P₁ * U) 1 1 = P₁ 1 1 :=
      congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 1 1) h1
    have h3 : (Uᴴ * P₁ * U) 1 1 = 1 := by
      simp [hU, hP₁, Matrix.mul_apply, Fin.sum_univ_two]
    have h4 : P₁ 1 1 = 0 := by simp [hP₁]
    rw [h3, h4] at h2
    exact one_ne_zero h2

end JointTangentStabilizer

/-! ### `thm:GT-source-metric-depth`

Rendering (SMET.20–SMET.24): the depth filtration `𝓜_r`, its orthogonal
layers `𝓝_r`, and the depth writers `D_r = P_r H^r P_B` are built from
the physical source range `S = Ran P_B` on the finite-dimensional carrier
(where every domain condition of the manuscript holds automatically); the
short-time laws (SMET.21–SMET.22) are exact `IsBigO` expansions along
`𝓝[>] 0` with the displayed leading coefficient
`T^{2r+1}/((r!)²(2r+1))`; block-tridiagonality (SMET.23) is stated with
the manuscript's `𝓝_{-1} = 0` convention (truncated subtraction);
(SMET.24) gives `Ran A_r = 𝓝_{r+1}` (as the exact image of the layer
below), the monotone layer dimensions, and the exact chain product
`D_r = A_{r-1} ⋯ A_0` on the source range. -/

section SourceMetricDepth

open ContinuousLinearMap Submodule Filter Topology Upstream
open scoped InnerProduct ComplexInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteDimensional ℂ V]

/-- **(SMET.20)** The depth filtration `𝓜_r = ∑_{k≤r} Ran(H^k P_B)`,
generated recursively by the clock. -/
noncomputable def depthM (H : V →L[ℂ] V) (S : Submodule ℂ V) :
    ℕ → Submodule ℂ V
  | 0 => S
  | r + 1 => depthM H S r ⊔ Submodule.map (H : V →ₗ[ℂ] V) (depthM H S r)

/-- **(SMET.20)** The depth layers `𝓝_r = 𝓜_r ⊖ 𝓜_{r-1}`. -/
noncomputable def depthN (H : V →L[ℂ] V) (S : Submodule ℂ V) :
    ℕ → Submodule ℂ V
  | 0 => S
  | r + 1 => depthM H S (r + 1) ⊓ (depthM H S r)ᗮ

variable {H : V →L[ℂ] V} {S : Submodule ℂ V}

omit [FiniteDimensional ℂ V] in
/-- The filtration is increasing. -/
theorem depthM_le_succ (r : ℕ) : depthM H S r ≤ depthM H S (r + 1) :=
  le_sup_left

omit [FiniteDimensional ℂ V] in
/-- The filtration is monotone. -/
theorem depthM_mono : Monotone (depthM H S) :=
  monotone_nat_of_le_succ depthM_le_succ

omit [FiniteDimensional ℂ V] in
/-- The clock advances the filtration one step. -/
theorem map_depthM_le (r : ℕ) :
    Submodule.map (H : V →ₗ[ℂ] V) (depthM H S r) ≤ depthM H S (r + 1) :=
  le_sup_right

omit [FiniteDimensional ℂ V] in
/-- Layers sit inside the filtration. -/
theorem depthN_le_depthM (r : ℕ) : depthN H S r ≤ depthM H S r := by
  cases r with
  | zero => exact le_rfl
  | succ r => exact inf_le_left

omit [FiniteDimensional ℂ V] in
/-- Layers are orthogonal to the previous filtration stage. -/
theorem depthN_succ_le_orthogonal (r : ℕ) :
    depthN H S (r + 1) ≤ (depthM H S r)ᗮ :=
  inf_le_right

/-- **(SMET.20, splitting)** `𝓜_{r+1} = 𝓜_r ⊔ 𝓝_{r+1}`, the exact
orthogonal layer decomposition. -/
theorem depthM_succ_eq_sup (r : ℕ) :
    depthM H S (r + 1) = depthM H S r ⊔ depthN H S (r + 1) := by
  refine le_antisymm ?_ (sup_le (depthM_le_succ r) (depthN_le_depthM (r + 1)))
  intro x hx
  have hdec : x = (depthM H S r).starProjection x
      + (x - (depthM H S r).starProjection x) := by abel
  refine Submodule.mem_sup.mpr ⟨(depthM H S r).starProjection x,
    (depthM H S r).starProjection_apply_mem x,
    x - (depthM H S r).starProjection x, ?_, hdec.symm⟩
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  · exact Submodule.sub_mem _ hx
      (depthM_le_succ r ((depthM H S r).starProjection_apply_mem x))
  · exact (depthM H S r).sub_starProjection_mem_orthogonal x
omit [FiniteDimensional ℂ V] in
/-- Orthogonal splitting extraction: a vector of `A ⊔ B` with `B ⊥ A`
that is orthogonal to `A` lies in `B`. -/
theorem mem_right_of_orthogonal {A B : Submodule ℂ V} (hAB : B ≤ Aᗮ)
    {x : V} (hx : x ∈ A ⊔ B) (hperp : ∀ y ∈ A, ⟪y, x⟫ = 0) : x ∈ B := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
  have hab : ⟪a, b⟫ = 0 :=
    (Submodule.mem_orthogonal A b).mp (hAB hb) a ha
  have haa : ⟪a, a⟫ = 0 := by
    have h1 : ⟪a, a + b⟫ = 0 := hperp a ha
    rw [inner_add_right, hab, add_zero] at h1
    exact h1
  have ha0 : a = 0 := inner_self_eq_zero.mp haa
  rw [ha0, zero_add]
  exact hb

/-- **(SMET.23)** The Hamiltonian is block tridiagonal on the depth
decomposition: `H 𝓝_r ⊆ 𝓝_{r-1} ⊕ 𝓝_r ⊕ 𝓝_{r+1}` (with `𝓝_{-1} = 0`
absorbed by the truncated index). -/
theorem depth_tridiagonal (hH : IsSelfAdjoint H) (r : ℕ) :
    ∀ x ∈ depthN H S r,
      H x ∈ depthN H S (r - 1) ⊔ depthN H S r ⊔ depthN H S (r + 1) := by
  intro x hx
  have hxM : x ∈ depthM H S r := depthN_le_depthM r hx
  have hHx : H x ∈ depthM H S (r + 1) :=
    map_depthM_le r ⟨x, hxM, rfl⟩
  match r with
  | 0 =>
    -- `H 𝓝_0 ⊆ 𝓜_1 = 𝓝_0 ⊔ 𝓝_1`
    rw [depthM_succ_eq_sup 0] at hHx
    have h1 : depthM H S 0 ⊔ depthN H S 1
        ≤ depthN H S 0 ⊔ depthN H S 0 ⊔ depthN H S 1 := by
      refine sup_le ?_ ?_
      · exact le_trans le_sup_right le_sup_left
      · exact le_sup_right
    exact h1 hHx
  | 1 =>
    -- `H 𝓝_1 ⊆ 𝓜_2 = 𝓝_0 ⊔ 𝓝_1 ⊔ 𝓝_2`
    rw [depthM_succ_eq_sup 1, depthM_succ_eq_sup 0] at hHx
    have h1 : depthM H S 0 ⊔ depthN H S 1 ⊔ depthN H S 2
        ≤ depthN H S 0 ⊔ depthN H S 1 ⊔ depthN H S 2 := le_rfl
    exact h1 hHx
  | (s + 2) =>
    -- orthogonality to `𝓜_{s-1}`… here `𝓜_s`
    have hperp : ∀ y ∈ depthM H S s, ⟪y, H x⟫ = 0 := by
      intro y hy
      have h1 : H y ∈ depthM H S (s + 1) := map_depthM_le s ⟨y, hy, rfl⟩
      have h2 : ⟪H y, x⟫ = 0 := by
        have h3 := depthN_succ_le_orthogonal (s + 1) hx
        exact (Submodule.mem_orthogonal (depthM H S (s + 1)) x).mp h3 _ h1
      calc ⟪y, H x⟫ = ⟪(H†) y, x⟫ :=
            (ContinuousLinearMap.adjoint_inner_left H x y).symm
        _ = ⟪H y, x⟫ := by rw [hH.adjoint_eq]
        _ = 0 := h2
    have hsup : depthM H S (s + 3)
        = depthM H S s ⊔ (depthN H S (s + 1) ⊔ depthN H S (s + 2)
          ⊔ depthN H S (s + 3)) := by
      rw [depthM_succ_eq_sup (s + 2), depthM_succ_eq_sup (s + 1),
        depthM_succ_eq_sup s, sup_assoc, sup_assoc]
      congr 1
      exact (sup_assoc _ _ _).symm
    have hB_le : depthN H S (s + 1) ⊔ depthN H S (s + 2)
        ⊔ depthN H S (s + 3) ≤ (depthM H S s)ᗮ := by
      refine sup_le (sup_le ?_ ?_) ?_
      · exact depthN_succ_le_orthogonal s
      · exact le_trans (depthN_succ_le_orthogonal (s + 1))
          (Submodule.orthogonal_le (depthM_mono (by omega)))
      · exact le_trans (depthN_succ_le_orthogonal (s + 2))
          (Submodule.orthogonal_le (depthM_mono (by omega)))
    have hHx' : H x ∈ depthM H S s ⊔ (depthN H S (s + 1)
        ⊔ depthN H S (s + 2) ⊔ depthN H S (s + 3)) := by
      rw [← hsup]
      exact hHx
    have hmem := mem_right_of_orthogonal hB_le hHx' hperp
    have hfinal : depthN H S (s + 1) ⊔ depthN H S (s + 2)
        ⊔ depthN H S (s + 3)
        ≤ depthN H S (s + 2 - 1) ⊔ depthN H S (s + 2)
          ⊔ depthN H S (s + 2 + 1) := le_rfl
    exact hfinal hmem

omit [FiniteDimensional ℂ V] in
/-- Clock powers of the source range stay inside the filtration. -/
theorem pow_map_le_depthM (k : ℕ) :
    Submodule.map ((H : V →ₗ[ℂ] V) ^ k) S ≤ depthM H S k := by
  induction k with
  | zero =>
    rw [pow_zero, Module.End.one_eq_id, Submodule.map_id]
    exact le_rfl
  | succ k ih =>
    have h1 : ((H : V →ₗ[ℂ] V) ^ (k + 1)) = (H : V →ₗ[ℂ] V)
        ∘ₗ ((H : V →ₗ[ℂ] V) ^ k) := by
      rw [pow_succ']
      rfl
    rw [h1, Submodule.map_comp]
    exact le_trans (Submodule.map_mono ih) (map_depthM_le k)

omit [FiniteDimensional ℂ V] in
/-- Coerced linear-map powers of the clock agree pointwise with the
operator powers. -/
theorem pow_apply_coe (r : ℕ) (x : V) :
    ((H : V →ₗ[ℂ] V) ^ r) x = (H ^ r) x := by
  induction r generalizing x with
  | zero => rfl
  | succ r ih =>
    have h1 : ((H : V →ₗ[ℂ] V) ^ (r + 1)) x
        = ((H : V →ₗ[ℂ] V) ^ r) (H x) := by
      rw [pow_succ]
      rfl
    have h2 : (H ^ (r + 1)) x = (H ^ r) (H x) := by
      rw [pow_succ]
      rfl
    rw [h1, h2, ih]

omit [FiniteDimensional ℂ V] in
/-- **(SMET.20, display)** The recursive filtration is the manuscript sum
`𝓜_r = ∑_{k≤r} Ran(H^k P_B)`. -/
theorem depthM_eq_iSup (r : ℕ) :
    depthM H S r = ⨆ k : Fin (r + 1),
      Submodule.map ((H : V →ₗ[ℂ] V) ^ (k : ℕ)) S := by
  induction r with
  | zero =>
    refine le_antisymm ?_ (iSup_le fun k => ?_)
    · have h0 : depthM H S 0 = Submodule.map ((H : V →ₗ[ℂ] V) ^ 0) S := by
        rw [pow_zero, Module.End.one_eq_id, Submodule.map_id]
        rfl
      rw [h0]
      exact le_iSup (fun k : Fin 1 =>
        Submodule.map ((H : V →ₗ[ℂ] V) ^ (k : ℕ)) S) 0
    · have hk : (k : ℕ) = 0 := by omega
      rw [hk]
      exact pow_map_le_depthM 0
  | succ r ih =>
    refine le_antisymm ?_ (iSup_le fun k => ?_)
    · refine sup_le ?_ ?_
      · refine le_trans (le_of_eq ih) (iSup_le fun k => ?_)
        exact le_iSup (fun k : Fin (r + 2) =>
          Submodule.map ((H : V →ₗ[ℂ] V) ^ (k : ℕ)) S) k.castSucc
      · rw [ih, Submodule.map_iSup]
        refine iSup_le fun k => ?_
        rw [← Submodule.map_comp]
        have h1 : (H : V →ₗ[ℂ] V) ∘ₗ ((H : V →ₗ[ℂ] V) ^ (k : ℕ))
            = (H : V →ₗ[ℂ] V) ^ ((k : ℕ) + 1) := by
          rw [pow_succ']
          rfl
        rw [h1]
        exact le_iSup (fun k : Fin (r + 2) =>
          Submodule.map ((H : V →ₗ[ℂ] V) ^ (k : ℕ)) S) k.succ
    · exact le_trans (pow_map_le_depthM (k : ℕ))
        (depthM_mono (by omega))

/-- The block-Jacobi couplings `A_r = P_{r+1} H P_r` (SMET.24). -/
noncomputable def depthA (H : V →L[ℂ] V) (S : Submodule ℂ V) (r : ℕ) :
    V →L[ℂ] V :=
  (depthN H S (r + 1)).starProjection ∘L H
    ∘L (depthN H S r).starProjection

/-- The depth writers `D_r = P_r H^r P_B` (SMET.20). -/
noncomputable def depthD (H : V →L[ℂ] V) (S : Submodule ℂ V) (r : ℕ) :
    V →L[ℂ] V :=
  (depthN H S r).starProjection ∘L (H ^ r) ∘L S.starProjection

/-- The filtration advances by the image of the top layer:
`𝓜_{r+1} = 𝓜_r + H 𝓝_r`. -/
theorem depthM_succ_eq_sup_map_N (r : ℕ) :
    depthM H S (r + 1)
      = depthM H S r ⊔ Submodule.map (H : V →ₗ[ℂ] V) (depthN H S r) := by
  refine le_antisymm ?_ (sup_le (depthM_le_succ r)
    (le_trans (Submodule.map_mono (depthN_le_depthM r)) (map_depthM_le r)))
  have hmapN : Submodule.map (H : V →ₗ[ℂ] V) (depthM H S r)
      ≤ depthM H S r ⊔ Submodule.map (H : V →ₗ[ℂ] V) (depthN H S r) := by
    cases r with
    | zero =>
      exact le_trans (le_of_eq rfl) le_sup_right
    | succ t =>
      rw [depthM_succ_eq_sup t, Submodule.map_sup]
      refine sup_le ?_ le_sup_right
      exact le_trans (map_depthM_le t)
        (le_trans (le_of_eq (depthM_succ_eq_sup t)) le_sup_left)
  exact sup_le le_sup_left hmapN

/-- Membership in the previous filtration stage kills the layer
projection above it. -/
theorem starProjection_depthN_eq_zero {r : ℕ} {m : V}
    (hm : m ∈ depthM H S r) :
    (depthN H S (r + 1)).starProjection m = 0 := by
  rw [Submodule.starProjection_apply_eq_zero_iff]
  intro n hn
  exact inner_eq_zero_symm.mp
    ((Submodule.mem_orthogonal _ _).mp (depthN_succ_le_orthogonal r hn) m hm)

/-- **(SMET.24, onto)** The coupling maps the layer onto the next layer:
`Ran A_r = 𝓝_{r+1}`, exactly as the image of `𝓝_r`. -/
theorem depthA_range (r : ℕ) :
    LinearMap.range (depthA H S r : V →ₗ[ℂ] V) = depthN H S (r + 1)
    ∧ Submodule.map (depthA H S r : V →ₗ[ℂ] V) (depthN H S r)
      = depthN H S (r + 1) := by
  have hsub : ∀ x : V, depthA H S r x ∈ depthN H S (r + 1) := fun x =>
    (depthN H S (r + 1)).starProjection_apply_mem _
  have honto : ∀ z ∈ depthN H S (r + 1), ∃ n ∈ depthN H S r,
      depthA H S r n = z := by
    intro z hz
    have hzM : z ∈ depthM H S (r + 1) := depthN_le_depthM (r + 1) hz
    rw [depthM_succ_eq_sup_map_N r] at hzM
    obtain ⟨m, hm, w, hw, rfl⟩ := Submodule.mem_sup.mp hzM
    obtain ⟨n, hn, rfl⟩ := hw
    refine ⟨n, hn, ?_⟩
    have h1 : depthA H S r n
        = (depthN H S (r + 1)).starProjection (H n) := by
      have h2 : (depthN H S r).starProjection n = n :=
        (depthN H S r).starProjection_eq_self_iff.mpr hn
      calc depthA H S r n
          = (depthN H S (r + 1)).starProjection
            (H ((depthN H S r).starProjection n)) := rfl
        _ = (depthN H S (r + 1)).starProjection (H n) := by rw [h2]
    rw [h1]
    have h3 : (depthN H S (r + 1)).starProjection (m + H n) = m + H n :=
      (depthN H S (r + 1)).starProjection_eq_self_iff.mpr hz
    have h4 : (depthN H S (r + 1)).starProjection (m + H n)
        = (depthN H S (r + 1)).starProjection m
          + (depthN H S (r + 1)).starProjection (H n) := map_add _ _ _
    rw [starProjection_depthN_eq_zero hm, zero_add] at h4
    rw [← h4, h3]
    rfl
  constructor
  · refine le_antisymm ?_ ?_
    · rintro z ⟨x, rfl⟩
      exact hsub x
    · intro z hz
      obtain ⟨n, _, hn2⟩ := honto z hz
      exact ⟨n, hn2⟩
  · refine le_antisymm ?_ ?_
    · rintro z ⟨n, _, rfl⟩
      exact hsub n
    · intro z hz
      obtain ⟨n, hn1, hn2⟩ := honto z hz
      exact ⟨n, hn1, hn2⟩

/-- **(SMET.24, monotone dimensions)**
`dim 𝓝_{r+1} ≤ dim 𝓝_r`. -/
theorem depthN_finrank_antitone (r : ℕ) :
    Module.finrank ℂ (depthN H S (r + 1))
      ≤ Module.finrank ℂ (depthN H S r) := by
  rw [← (depthA_range (H := H) (S := S) r).2]
  exact Submodule.finrank_map_le _ _

/-- The residual of a filtration vector below the top layer is killed one
clock step later. -/
theorem starProjection_clock_residual {r : ℕ} {m : V}
    (hm : m ∈ depthM H S r) :
    (depthN H S (r + 1)).starProjection
      (H (m - (depthN H S r).starProjection m)) = 0 := by
  cases r with
  | zero =>
    have hself : (depthN H S 0).starProjection m = m :=
      (depthN H S 0).starProjection_eq_self_iff.mpr hm
    rw [hself, sub_self, map_zero, map_zero]
  | succ t =>
    have hmem : m - (depthN H S (t + 1)).starProjection m
        ∈ depthM H S t := by
      rw [depthM_succ_eq_sup t] at hm
      obtain ⟨m', hm', n, hn, rfl⟩ := Submodule.mem_sup.mp hm
      have h1 : (depthN H S (t + 1)).starProjection (m' + n)
          = (depthN H S (t + 1)).starProjection m'
            + (depthN H S (t + 1)).starProjection n := map_add _ _ _
      rw [starProjection_depthN_eq_zero hm', zero_add,
        (depthN H S (t + 1)).starProjection_eq_self_iff.mpr hn] at h1
      rw [h1]
      have h2 : m' + n - n = m' := by abel
      rw [h2]
      exact hm'
    have h3 : H (m - (depthN H S (t + 1)).starProjection m)
        ∈ depthM H S (t + 1) := map_depthM_le t ⟨_, hmem, rfl⟩
    exact starProjection_depthN_eq_zero h3

/-- The ordered chain product `A_{r-1} ⋯ A_0` (anchored at
`D_0 = P_B`). -/
noncomputable def depthAprod (H : V →L[ℂ] V) (S : Submodule ℂ V) :
    ℕ → (V →L[ℂ] V)
  | 0 => (depthN H S 0).starProjection
  | r + 1 => depthA H S r ∘L depthAprod H S r

/-- **(SMET.24, chain product)** The depth writers are the exact ordered
products of the block-Jacobi couplings: `D_r = A_{r-1} ⋯ A_0`. -/
theorem depthD_eq_chain (r : ℕ) :
    depthD H S r = depthAprod H S r := by
  induction r with
  | zero =>
    ext x
    have h1 : depthD H S 0 x
        = (depthN H S 0).starProjection (S.starProjection x) := by
      have h0 : depthD H S 0 x = (depthN H S 0).starProjection
          ((H ^ 0) (S.starProjection x)) := rfl
      rw [h0, pow_zero, one_apply_eq_self]
    rw [h1]
    have h2 : S.starProjection x ∈ depthN H S 0 :=
      S.starProjection_apply_mem x
    rw [(depthN H S 0).starProjection_eq_self_iff.mpr h2]
    rfl
  | succ r ih =>
    have hstep : depthD H S (r + 1) = depthA H S r ∘L depthD H S r := by
      ext x
      have hL : depthD H S (r + 1) x = (depthN H S (r + 1)).starProjection
          (H ((H ^ r) (S.starProjection x))) := by
        have h0 : depthD H S (r + 1) x
            = (depthN H S (r + 1)).starProjection
              ((H ^ (r + 1)) (S.starProjection x)) := rfl
        rw [h0]
        congr 1
        have h1 : (H ^ (r + 1)) (S.starProjection x)
            = H ((H ^ r) (S.starProjection x)) := by
          rw [pow_succ']
          rfl
        rw [h1]
      have hR : (depthA H S r ∘L depthD H S r) x
          = (depthN H S (r + 1)).starProjection
            (H ((depthN H S r).starProjection
              ((H ^ r) (S.starProjection x)))) := by
        have h0 : (depthA H S r ∘L depthD H S r) x
            = (depthN H S (r + 1)).starProjection
              (H ((depthN H S r).starProjection
                ((depthN H S r).starProjection
                  ((H ^ r) (S.starProjection x))))) := rfl
        rw [h0, (depthN H S r).starProjection_eq_self_iff.mpr
          ((depthN H S r).starProjection_apply_mem _)]
      rw [hL, hR]
      set m : V := (H ^ r) (S.starProjection x) with hm
      have hmM : m ∈ depthM H S r := by
        refine pow_map_le_depthM r ⟨S.starProjection x,
          S.starProjection_apply_mem x, ?_⟩
        rw [hm]
        exact pow_apply_coe r (S.starProjection x)
      have hres := starProjection_clock_residual (H := H) (S := S) hmM
      have hsplit : H m = H (m - (depthN H S r).starProjection m)
          + H ((depthN H S r).starProjection m) := by
        rw [← map_add]
        congr 1
        abel
      rw [hsplit, map_add, hres, zero_add]
    rw [hstep, ih]
    rfl

/-! ### SMET.21/22: short-time Gramian asymptotics at fixed depth -/

/-- The exponential-tail constant `C_H = ∑_m ‖H‖^m/m!` controlling all
short-time remainders. -/
noncomputable def expTailC (H : V →L[ℂ] V) : ℝ :=
  ∑' m : ℕ, ‖H‖ ^ m / (m.factorial : ℝ)

omit [FiniteDimensional ℂ V] in
/-- The tail constant is nonnegative. -/
theorem expTailC_nonneg (H : V →L[ℂ] V) : 0 ≤ expTailC H :=
  tsum_nonneg fun m => div_nonneg (pow_nonneg (norm_nonneg H) m)
    (Nat.cast_nonneg _)

omit [FiniteDimensional ℂ V] in
/-- Shifted exponential tails are controlled by the full series. -/
theorem expTail_shift_le (H : V →L[ℂ] V) (k : ℕ) :
    ∑' i : ℕ, ‖H‖ ^ (i + k) / ((i + k).factorial : ℝ) ≤ expTailC H := by
  have hb := Real.summable_pow_div_factorial ‖H‖
  have hsplit := hb.sum_add_tsum_nat_add k
  have hpos : 0 ≤ ∑ i ∈ Finset.range k, ‖H‖ ^ i / (i.factorial : ℝ) :=
    Finset.sum_nonneg fun i _ =>
      div_nonneg (pow_nonneg (norm_nonneg _) _) (Nat.cast_nonneg _)
  calc ∑' i : ℕ, ‖H‖ ^ (i + k) / ((i + k).factorial : ℝ)
      ≤ (∑ i ∈ Finset.range k, ‖H‖ ^ i / (i.factorial : ℝ))
        + ∑' i : ℕ, ‖H‖ ^ (i + k) / ((i + k).factorial : ℝ) :=
        le_add_of_nonneg_left hpos
    _ = expTailC H := hsplit

omit [FiniteDimensional ℂ V] in
/-- Complex factorial-inverse scaling of a real scaling is the real
Taylor-coefficient scaling. -/
theorem factorial_smul_real {n : ℕ} {a : ℝ} (v : V) :
    (n.factorial⁻¹ : ℂ) • (a • v) = (a / (n.factorial : ℝ)) • v := by
  rw [← Complex.coe_smul a v, smul_smul,
    ← Complex.coe_smul (a / (n.factorial : ℝ)) v]
  congr 1
  push_cast
  ring

/-- Depth blocks strictly below the writer's level annihilate the
source: `P_r H^k P_B = 0` for `k < r`. -/
theorem depth_writer_lt_vanish {k r : ℕ} (hk : k < r) :
    (depthN H S r).starProjection ∘L (H ^ k) ∘L S.starProjection = 0 := by
  cases r with
  | zero => exact absurd hk (Nat.not_lt_zero k)
  | succ s =>
    ext x
    have hmem : (H ^ k) (S.starProjection x) ∈ depthM H S s := by
      refine depthM_mono (show k ≤ s by omega) ?_
      refine pow_map_le_depthM k ⟨S.starProjection x,
        S.starProjection_apply_mem x, ?_⟩
      exact pow_apply_coe k (S.starProjection x)
    calc ((depthN H S (s + 1)).starProjection ∘L (H ^ k)
          ∘L S.starProjection) x
        = (depthN H S (s + 1)).starProjection
          ((H ^ k) (S.starProjection x)) := rfl
      _ = 0 := starProjection_depthN_eq_zero hmem
      _ = (0 : V →L[ℂ] V) x := rfl

set_option maxHeartbeats 1600000 in -- long tsum-tail estimate chain
/-- **(SMET.21/22, flow Taylor)** Short-time expansion of the depth-block
flow: `‖P_r e^{-tH} P_B − ((−t)^r/r!) D_r‖ ≤ C_H t^{r+1}` on `[0,1]`. -/
theorem depth_flow_taylor (r : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖(depthN H S r).starProjection ∘L expH H t ∘L S.starProjection
      - ((-t) ^ r / (r.factorial : ℝ)) • depthD H S r‖
      ≤ expTailC H * t ^ (r + 1) := by
  refine ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (expTailC_nonneg H) (pow_nonneg ht0 _)) ?_
  intro x
  set Pr := (depthN H S r).starProjection with hPrdef
  set y := S.starProjection x with hydef
  have hsum1 : Summable fun n : ℕ =>
      (n.factorial⁻¹ : ℂ) • ((((-t) • H) ^ n) y) := by
    have h2 := (NormedSpace.expSeries_summable' (𝕂 := ℂ) ((-t) • H)).map
      (ContinuousLinearMap.apply ℂ V y).toLinearMap.toAddMonoidHom
      (ContinuousLinearMap.apply ℂ V y).continuous
    exact h2.congr fun n => rfl
  have hsum2 : Summable fun n : ℕ =>
      (n.factorial⁻¹ : ℂ) • Pr ((((-t) • H) ^ n) y) := by
    have h2 := hsum1.map Pr.toLinearMap.toAddMonoidHom Pr.continuous
    exact h2.congr fun n => map_smul Pr _ _
  have happ : (Pr ∘L expH H t ∘L S.starProjection) x
      = ∑' n : ℕ, (n.factorial⁻¹ : ℂ) • Pr ((((-t) • H) ^ n) y) := by
    have h1 : (Pr ∘L expH H t ∘L S.starProjection) x
        = Pr (NormedSpace.exp ((-t) • H) y) := rfl
    rw [h1, Upstream.exp_apply_tsum ((-t) • H) y, Pr.map_tsum hsum1]
    exact tsum_congr fun n => map_smul Pr _ _
  have hsplit := hsum2.sum_add_tsum_nat_add (r + 1)
  have hzero : ∀ n ∈ Finset.range (r + 1), n ≠ r →
      (n.factorial⁻¹ : ℂ) • Pr ((((-t) • H) ^ n) y) = 0 := by
    intro n hn hne
    have hnr : n < r := by
      have := Finset.mem_range.mp hn
      omega
    have h3 : Pr ((H ^ n) y) = 0 := by
      have h5 := depth_writer_lt_vanish (H := H) (S := S) hnr
      calc Pr ((H ^ n) y)
          = ((depthN H S r).starProjection ∘L (H ^ n)
            ∘L S.starProjection) x := rfl
        _ = (0 : V →L[ℂ] V) x := by rw [h5]
        _ = 0 := rfl
    have h6 : (((-t) • H) ^ n) y = (-t) ^ n • ((H ^ n) y) := by
      rw [smul_pow, _root_.smul_apply]
    rw [h6, Pr.map_smul_of_tower, h3, smul_zero, smul_zero]
  have hfin : ∑ n ∈ Finset.range (r + 1),
      (n.factorial⁻¹ : ℂ) • Pr ((((-t) • H) ^ n) y)
      = ((-t) ^ r / (r.factorial : ℝ)) • depthD H S r x := by
    rw [Finset.sum_eq_single_of_mem r
      (Finset.self_mem_range_succ r) hzero]
    have h6 : (((-t) • H) ^ r) y = (-t) ^ r • ((H ^ r) y) := by
      rw [smul_pow, _root_.smul_apply]
    have h7 : Pr ((H ^ r) y) = depthD H S r x := rfl
    rw [h6, Pr.map_smul_of_tower, h7, factorial_smul_real]
  have h8 : (∑' i : ℕ, ((i + (r + 1)).factorial⁻¹ : ℂ)
        • Pr ((((-t) • H) ^ (i + (r + 1))) y))
      = (∑' n : ℕ, (n.factorial⁻¹ : ℂ) • Pr ((((-t) • H) ^ n) y))
        - ∑ n ∈ Finset.range (r + 1),
            (n.factorial⁻¹ : ℂ) • Pr ((((-t) • H) ^ n) y) := by
    rw [eq_sub_iff_add_eq, add_comm]
    exact hsplit
  have hdiff : ((Pr ∘L expH H t ∘L S.starProjection)
        - ((-t) ^ r / (r.factorial : ℝ)) • depthD H S r) x
      = ∑' i : ℕ, ((i + (r + 1)).factorial⁻¹ : ℂ)
          • Pr ((((-t) • H) ^ (i + (r + 1))) y) := by
    rw [_root_.sub_apply, _root_.smul_apply, happ, ← hfin, h8]
  have hbnd : ∀ i : ℕ,
      ‖((i + (r + 1)).factorial⁻¹ : ℂ)
        • Pr ((((-t) • H) ^ (i + (r + 1))) y)‖
      ≤ t ^ (r + 1) * ‖x‖
        * (‖H‖ ^ (i + (r + 1)) / ((i + (r + 1)).factorial : ℝ)) := by
    intro i
    have hyx : ‖y‖ ≤ ‖x‖ := by
      calc ‖y‖ ≤ ‖S.starProjection‖ * ‖x‖ :=
            ContinuousLinearMap.le_opNorm _ x
        _ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right
            (Submodule.starProjection_norm_le S) (norm_nonneg x)
        _ = ‖x‖ := one_mul _
    have hPry : ‖Pr ((((-t) • H) ^ (i + (r + 1))) y)‖
        ≤ ‖(((-t) • H) ^ (i + (r + 1))) y‖ := by
      calc ‖Pr ((((-t) • H) ^ (i + (r + 1))) y)‖
          ≤ ‖Pr‖ * ‖(((-t) • H) ^ (i + (r + 1))) y‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ 1 * ‖(((-t) • H) ^ (i + (r + 1))) y‖ :=
            mul_le_mul_of_nonneg_right
              (Submodule.starProjection_norm_le _) (norm_nonneg _)
        _ = ‖(((-t) • H) ^ (i + (r + 1))) y‖ := one_mul _
    have hApow : ‖(((-t) • H) ^ (i + (r + 1))) y‖
        ≤ (t * ‖H‖) ^ (i + (r + 1)) * ‖x‖ := by
      have hA : ‖(-t) • H‖ = t * ‖H‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg ht0]
      calc ‖(((-t) • H) ^ (i + (r + 1))) y‖
          ≤ ‖((-t) • H) ^ (i + (r + 1))‖ * ‖y‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ ‖(-t) • H‖ ^ (i + (r + 1)) * ‖x‖ :=
            mul_le_mul (norm_pow_le' _ (by omega)) hyx (norm_nonneg _)
              (pow_nonneg (norm_nonneg _) _)
        _ = (t * ‖H‖) ^ (i + (r + 1)) * ‖x‖ := by rw [hA]
    have hfac : ‖((i + (r + 1)).factorial⁻¹ : ℂ)‖
        = ((i + (r + 1)).factorial : ℝ)⁻¹ := by
      rw [norm_inv, Complex.norm_natCast]
    calc ‖((i + (r + 1)).factorial⁻¹ : ℂ)
          • Pr ((((-t) • H) ^ (i + (r + 1))) y)‖
        = ‖((i + (r + 1)).factorial⁻¹ : ℂ)‖
          * ‖Pr ((((-t) • H) ^ (i + (r + 1))) y)‖ := norm_smul _ _
      _ ≤ ((i + (r + 1)).factorial : ℝ)⁻¹
          * ((t * ‖H‖) ^ (i + (r + 1)) * ‖x‖) := by
          rw [hfac]
          exact mul_le_mul_of_nonneg_left (le_trans hPry hApow)
            (inv_nonneg.mpr (Nat.cast_nonneg _))
      _ = t ^ (i + (r + 1)) * (‖x‖ * (‖H‖ ^ (i + (r + 1))
          / ((i + (r + 1)).factorial : ℝ))) := by
          rw [mul_pow]
          ring
      _ ≤ t ^ (r + 1) * (‖x‖ * (‖H‖ ^ (i + (r + 1))
          / ((i + (r + 1)).factorial : ℝ))) := by
          refine mul_le_mul_of_nonneg_right
            (pow_le_pow_of_le_one ht0 ht1 (by omega)) ?_
          exact mul_nonneg (norm_nonneg _)
            (div_nonneg (pow_nonneg (norm_nonneg _) _) (Nat.cast_nonneg _))
      _ = t ^ (r + 1) * ‖x‖ * (‖H‖ ^ (i + (r + 1))
          / ((i + (r + 1)).factorial : ℝ)) := by ring
  have hbsum : Summable fun i : ℕ =>
      ‖H‖ ^ (i + (r + 1)) / ((i + (r + 1)).factorial : ℝ) :=
    (summable_nat_add_iff (r + 1)).mpr
      (Real.summable_pow_div_factorial ‖H‖)
  have hcsum : Summable fun i : ℕ => t ^ (r + 1) * ‖x‖
      * (‖H‖ ^ (i + (r + 1)) / ((i + (r + 1)).factorial : ℝ)) :=
    hbsum.mul_left _
  have hgn : Summable fun i : ℕ =>
      ‖((i + (r + 1)).factorial⁻¹ : ℂ)
        • Pr ((((-t) • H) ^ (i + (r + 1))) y)‖ :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg _) hbnd hcsum
  have htail : ‖∑' i : ℕ, ((i + (r + 1)).factorial⁻¹ : ℂ)
        • Pr ((((-t) • H) ^ (i + (r + 1))) y)‖
      ≤ expTailC H * t ^ (r + 1) * ‖x‖ := by
    calc ‖∑' i : ℕ, ((i + (r + 1)).factorial⁻¹ : ℂ)
          • Pr ((((-t) • H) ^ (i + (r + 1))) y)‖
        ≤ ∑' i : ℕ, ‖((i + (r + 1)).factorial⁻¹ : ℂ)
            • Pr ((((-t) • H) ^ (i + (r + 1))) y)‖ :=
          norm_tsum_le_tsum_norm hgn
      _ ≤ ∑' i : ℕ, t ^ (r + 1) * ‖x‖
          * (‖H‖ ^ (i + (r + 1)) / ((i + (r + 1)).factorial : ℝ)) :=
          hgn.tsum_le_tsum hbnd hcsum
      _ = t ^ (r + 1) * ‖x‖
          * ∑' i : ℕ, ‖H‖ ^ (i + (r + 1))
            / ((i + (r + 1)).factorial : ℝ) := tsum_mul_left
      _ ≤ t ^ (r + 1) * ‖x‖ * expTailC H := by
          refine mul_le_mul_of_nonneg_left (expTail_shift_le H (r + 1)) ?_
          exact mul_nonneg (pow_nonneg ht0 _) (norm_nonneg x)
      _ = expTailC H * t ^ (r + 1) * ‖x‖ := by ring
  rw [hdiff]
  exact htail

/-- Real scalings pass through the adjoint. -/
theorem adjoint_real_smul (c : ℝ) (A : V →L[ℂ] V) :
    (c • A)† = c • A† := by
  rw [← ContinuousLinearMap.star_eq_adjoint,
    ← ContinuousLinearMap.star_eq_adjoint, star_smul, star_trivial]

/-- Compressed-sandwich cross-term decomposition:
`A Σ A† − B Σ B† = (A−B) Σ A† + B Σ (A−B)†`. -/
theorem sandwich_cross (A B Sig : V →L[ℂ] V) :
    A ∘L Sig ∘L A† - B ∘L Sig ∘L B†
      = (A - B) ∘L Sig ∘L A† + B ∘L Sig ∘L (A - B)† := by
  have hadj : (A - B)† = A† - B† := by
    rw [← ContinuousLinearMap.star_eq_adjoint,
      ← ContinuousLinearMap.star_eq_adjoint,
      ← ContinuousLinearMap.star_eq_adjoint]
    exact star_sub A B
  rw [hadj, ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub,
    ContinuousLinearMap.comp_sub]
  abel

/-- Real-scaled sandwich squares pull the scalar out quadratically. -/
theorem smul_sandwich_sq (c : ℝ) (D Sig : V →L[ℂ] V) :
    (c • D) ∘L Sig ∘L (c • D)† = (c ^ 2) • (D ∘L Sig ∘L D†) := by
  rw [adjoint_real_smul]
  ext x
  have h1 : ((c • D) ∘L Sig ∘L (c • D†)) x
      = c • D (Sig (c • ((D†) x))) := rfl
  have h2 : ((c ^ 2) • (D ∘L Sig ∘L D†)) x
      = (c ^ 2) • D (Sig ((D†) x)) := rfl
  rw [h1, h2, Sig.map_smul_of_tower, D.map_smul_of_tower, smul_smul,
    pow_two]

/-- Source-supported metric kernels compress through the depth
projection into the flow blocks. -/
theorem depth_compress_eq (Sig : V →L[ℂ] V)
    (hSig : Sig = S.starProjection ∘L Sig ∘L S.starProjection)
    (r : ℕ) (t : ℝ) :
    (depthN H S r).starProjection ∘L (expH H t ∘L Sig ∘L (expH H t)†)
        ∘L (depthN H S r).starProjection
      = ((depthN H S r).starProjection ∘L expH H t ∘L S.starProjection)
          ∘L Sig
          ∘L ((depthN H S r).starProjection ∘L expH H t
            ∘L S.starProjection)† := by
  conv_lhs => rw [hSig]
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    isSelfAdjoint_iff'.mp (isSelfAdjoint_starProjection (depthN H S r)),
    isSelfAdjoint_iff'.mp (isSelfAdjoint_starProjection S)]
  ext x
  rfl

/-- Cross-term estimate for the compressed flow sandwich on `[0,1]`. -/
theorem depth_sandwich_bound (Sig : V →L[ℂ] V) (r : ℕ)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖((depthN H S r).starProjection ∘L expH H t ∘L S.starProjection)
        ∘L Sig
        ∘L ((depthN H S r).starProjection ∘L expH H t
          ∘L S.starProjection)†
      - (((-t) ^ r / (r.factorial : ℝ)) ^ 2)
        • (depthD H S r ∘L Sig ∘L (depthD H S r)†)‖
    ≤ (expTailC H * ‖Sig‖ * (‖depthD H S r‖ + expTailC H)
        + ‖depthD H S r‖ * ‖Sig‖ * expTailC H) * t ^ (2 * r + 1) := by
  have hE := depth_flow_taylor (H := H) (S := S) r ht0 ht1
  set D := depthD H S r with hD
  set F := (depthN H S r).starProjection ∘L expH H t ∘L S.starProjection
    with hF
  set c := (-t) ^ r / (r.factorial : ℝ) with hc
  have hcabs : |c| ≤ t ^ r := by
    rw [hc, abs_div, abs_pow, abs_neg, abs_of_nonneg ht0,
      abs_of_nonneg (Nat.cast_nonneg r.factorial)]
    have h2 : (1 : ℝ) ≤ (r.factorial : ℝ) := by
      exact_mod_cast r.factorial_pos
    rw [div_le_iff₀ (by exact_mod_cast r.factorial_pos :
      (0:ℝ) < (r.factorial : ℝ))]
    nlinarith [pow_nonneg ht0 r]
  have hsmulD : ‖c • D‖ ≤ ‖D‖ * t ^ r := by
    rw [norm_smul, Real.norm_eq_abs]
    calc |c| * ‖D‖ ≤ t ^ r * ‖D‖ :=
          mul_le_mul_of_nonneg_right hcabs (norm_nonneg _)
      _ = ‖D‖ * t ^ r := mul_comm _ _
  have hFsplit : F = c • D + (F - c • D) := by abel
  have hnormF : ‖F‖ ≤ (‖D‖ + expTailC H) * t ^ r := by
    have h1 : ‖F‖ ≤ ‖c • D‖ + ‖F - c • D‖ := by
      conv_lhs => rw [hFsplit]
      exact norm_add_le _ _
    have h3 : ‖F - c • D‖ ≤ expTailC H * t ^ r := by
      refine le_trans hE ?_
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one ht0 ht1 (by omega)) (expTailC_nonneg H)
    calc ‖F‖ ≤ ‖c • D‖ + ‖F - c • D‖ := h1
      _ ≤ ‖D‖ * t ^ r + expTailC H * t ^ r := add_le_add hsmulD h3
      _ = (‖D‖ + expTailC H) * t ^ r := by ring
  have hkey : F ∘L Sig ∘L F† - c ^ 2 • (D ∘L Sig ∘L D†)
      = (F - c • D) ∘L Sig ∘L F† + (c • D) ∘L Sig ∘L (F - c • D)† := by
    have h1 := sandwich_cross F (c • D) Sig
    rw [smul_sandwich_sq] at h1
    exact h1
  rw [hkey]
  have hstarE : ‖(F - c • D)†‖ = ‖F - c • D‖ :=
    ContinuousLinearMap.adjoint.norm_map _
  have hstarF : ‖F†‖ = ‖F‖ := ContinuousLinearMap.adjoint.norm_map _
  have hb1 : ‖(F - c • D) ∘L Sig ∘L F†‖
      ≤ (expTailC H * t ^ (r + 1))
        * (‖Sig‖ * ((‖D‖ + expTailC H) * t ^ r)) := by
    calc ‖(F - c • D) ∘L Sig ∘L F†‖
        ≤ ‖F - c • D‖ * ‖Sig ∘L F†‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖F - c • D‖ * (‖Sig‖ * ‖F†‖) :=
          mul_le_mul_of_nonneg_left
            (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
      _ ≤ (expTailC H * t ^ (r + 1))
          * (‖Sig‖ * ((‖D‖ + expTailC H) * t ^ r)) := by
          refine mul_le_mul hE ?_ ?_ ?_
          · rw [hstarF]
            exact mul_le_mul_of_nonneg_left hnormF (norm_nonneg _)
          · exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
          · exact mul_nonneg (expTailC_nonneg H) (pow_nonneg ht0 _)
  have hb2 : ‖(c • D) ∘L Sig ∘L (F - c • D)†‖
      ≤ (‖D‖ * t ^ r) * (‖Sig‖ * (expTailC H * t ^ (r + 1))) := by
    calc ‖(c • D) ∘L Sig ∘L (F - c • D)†‖
        ≤ ‖c • D‖ * ‖Sig ∘L (F - c • D)†‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖c • D‖ * (‖Sig‖ * ‖(F - c • D)†‖) :=
          mul_le_mul_of_nonneg_left
            (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
      _ ≤ (‖D‖ * t ^ r) * (‖Sig‖ * (expTailC H * t ^ (r + 1))) := by
          refine mul_le_mul hsmulD ?_ ?_ ?_
          · rw [hstarE]
            exact mul_le_mul_of_nonneg_left hE (norm_nonneg _)
          · exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
          · exact mul_nonneg (norm_nonneg _) (pow_nonneg ht0 _)
  have hpow2 : t ^ (r + 1) * t ^ r = t ^ (2 * r + 1) := by
    rw [← pow_add]
    congr 1
    omega
  calc ‖(F - c • D) ∘L Sig ∘L F† + (c • D) ∘L Sig ∘L (F - c • D)†‖
      ≤ ‖(F - c • D) ∘L Sig ∘L F†‖
        + ‖(c • D) ∘L Sig ∘L (F - c • D)†‖ := norm_add_le _ _
    _ ≤ (expTailC H * t ^ (r + 1))
          * (‖Sig‖ * ((‖D‖ + expTailC H) * t ^ r))
        + (‖D‖ * t ^ r) * (‖Sig‖ * (expTailC H * t ^ (r + 1))) :=
        add_le_add hb1 hb2
    _ = (expTailC H * ‖Sig‖ * (‖D‖ + expTailC H)
        + ‖D‖ * ‖Sig‖ * expTailC H) * (t ^ (r + 1) * t ^ r) := by ring
    _ = (expTailC H * ‖Sig‖ * (‖D‖ + expTailC H)
        + ‖D‖ * ‖Sig‖ * expTailC H) * t ^ (2 * r + 1) := by rw [hpow2]

/-- **(SMET.16, rendered)** The metric horizon Gramian
`𝒲_{T;B,M} = ∫₀ᵀ e^{-tH} Σ_{B,M} (e^{-tH})^* dt`; for self-adjoint `H`
this is the manuscript form, and the normalized horizon `Ŵ_{T,B}` is
the case `Σ = P_B`. -/
noncomputable def gramW (H Sig : V →L[ℂ] V) (T : ℝ) : V →L[ℂ] V :=
  ∫ t in (0:ℝ)..T, expH H t ∘L Sig ∘L (expH H t)†

/-- Time-continuity of the Gramian integrand. -/
theorem gramW_integrand_continuous (H Sig : V →L[ℂ] V) :
    Continuous fun t : ℝ => expH H t ∘L Sig ∘L (expH H t)† := by
  have h1 : Continuous fun t : ℝ => (expH H t)† :=
    ContinuousLinearMap.adjoint.continuous.comp (expH_continuous H)
  have h2 : Continuous fun t : ℝ => Sig ∘L (expH H t)† :=
    isBoundedBilinearMap_comp.continuous.comp (continuous_const.prodMk h1)
  exact isBoundedBilinearMap_comp.continuous.comp
    ((expH_continuous H).prodMk h2)

/-- Fixed two-sided compressions commute with operator-valued interval
integrals. -/
theorem compress_intervalIntegral (A B : V →L[ℂ] V)
    {f : ℝ → V →L[ℂ] V} {a b : ℝ}
    (hf : IntervalIntegrable f MeasureTheory.volume a b) :
    A ∘L (∫ t in a..b, f t) ∘L B = ∫ t in a..b, A ∘L f t ∘L B := by
  let Phi : (V →L[ℂ] V) →ₗ[ℂ] (V →L[ℂ] V) :=
    { toFun := fun X => A ∘L X ∘L B
      map_add' := fun X Y => by
        rw [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]
      map_smul' := fun cx X => by
        rw [RingHom.id_apply, ContinuousLinearMap.smul_comp,
          ContinuousLinearMap.comp_smul] }
  have h := (LinearMap.toContinuousLinearMap Phi).intervalIntegral_comp_comm
    hf
  calc A ∘L (∫ t in a..b, f t) ∘L B
      = LinearMap.toContinuousLinearMap Phi (∫ t in a..b, f t) := rfl
    _ = ∫ t in a..b, LinearMap.toContinuousLinearMap Phi (f t) := h.symm
    _ = ∫ t in a..b, A ∘L f t ∘L B :=
        intervalIntegral.integral_congr fun t _ => rfl

/-- **(SMET.21)** Short-time depth-block asymptotics of the metric
horizon Gramian: for any source-supported metric kernel
`Σ = P_B Σ P_B`, as `T ↓ 0`,
`P_r 𝒲_{T;B,M} P_r = (T^{2r+1}/((r!)^2(2r+1))) D_r Σ D_r^* + O(T^{2r+2})`. -/
theorem source_metric_depth_gramian (Sig : V →L[ℂ] V)
    (hSig : Sig = S.starProjection ∘L Sig ∘L S.starProjection) (r : ℕ) :
    (fun T : ℝ =>
        (depthN H S r).starProjection ∘L gramW H Sig T
            ∘L (depthN H S r).starProjection
          - (T ^ (2 * r + 1)
              / ((r.factorial : ℝ) ^ 2 * (2 * (r : ℝ) + 1)))
            • (depthD H S r ∘L Sig ∘L (depthD H S r)†))
      =O[𝓝[>] (0 : ℝ)] fun T : ℝ => T ^ (2 * r + 2) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨expTailC H * ‖Sig‖ * (‖depthD H S r‖ + expTailC H)
    + ‖depthD H S r‖ * ‖Sig‖ * expTailC H, ?_⟩
  filter_upwards [Ioc_mem_nhdsGT (show (0:ℝ) < 1 from zero_lt_one)]
    with T hT
  obtain ⟨hT0, hT1⟩ := hT
  have hCnn : (0 : ℝ)
      ≤ expTailC H * ‖Sig‖ * (‖depthD H S r‖ + expTailC H)
        + ‖depthD H S r‖ * ‖Sig‖ * expTailC H := by
    have h1 := expTailC_nonneg H
    have h2 : (0:ℝ) ≤ ‖Sig‖ := norm_nonneg _
    have h3 : (0:ℝ) ≤ ‖depthD H S r‖ := norm_nonneg _
    exact add_nonneg (mul_nonneg (mul_nonneg h1 h2) (add_nonneg h3 h1))
      (mul_nonneg (mul_nonneg h3 h2) h1)
  have hccont : Continuous fun t : ℝ =>
      (depthN H S r).starProjection
        ∘L (expH H t ∘L Sig ∘L (expH H t)†)
        ∘L (depthN H S r).starProjection := by
    have h2 : Continuous fun t : ℝ =>
        (expH H t ∘L Sig ∘L (expH H t)†)
          ∘L (depthN H S r).starProjection :=
      isBoundedBilinearMap_comp.continuous.comp
        ((gramW_integrand_continuous H Sig).prodMk continuous_const)
    exact isBoundedBilinearMap_comp.continuous.comp
      (continuous_const.prodMk h2)
  have hint1 : IntervalIntegrable (fun t : ℝ =>
      (depthN H S r).starProjection
        ∘L (expH H t ∘L Sig ∘L (expH H t)†)
        ∘L (depthN H S r).starProjection)
      MeasureTheory.volume 0 T := hccont.intervalIntegrable 0 T
  have hint2 : IntervalIntegrable (fun t : ℝ =>
      (((-t) ^ r / (r.factorial : ℝ)) ^ 2)
        • (depthD H S r ∘L Sig ∘L (depthD H S r)†))
      MeasureTheory.volume 0 T := by
    have h3 : Continuous fun t : ℝ =>
        (((-t) ^ r / (r.factorial : ℝ)) ^ 2) :=
      ((continuous_neg.pow r).div_const _).pow 2
    exact (h3.smul continuous_const).intervalIntegrable 0 T
  have hgwdef : gramW H Sig T
      = ∫ t in (0:ℝ)..T, expH H t ∘L Sig ∘L (expH H t)† := rfl
  have hPrW : (depthN H S r).starProjection ∘L gramW H Sig T
      ∘L (depthN H S r).starProjection
      = ∫ t in (0:ℝ)..T, (depthN H S r).starProjection
          ∘L (expH H t ∘L Sig ∘L (expH H t)†)
          ∘L (depthN H S r).starProjection := by
    rw [hgwdef]
    exact compress_intervalIntegral _ _
      ((gramW_integrand_continuous H Sig).intervalIntegrable 0 T)
  have hcoef : (∫ t in (0:ℝ)..T, (((-t) ^ r / (r.factorial : ℝ)) ^ 2))
      = T ^ (2 * r + 1)
        / ((r.factorial : ℝ) ^ 2 * (2 * (r : ℝ) + 1)) := by
    have h1 : Set.EqOn
        (fun t : ℝ => (((-t) ^ r / (r.factorial : ℝ)) ^ 2))
        (fun t : ℝ => ((r.factorial : ℝ) ^ 2)⁻¹ * t ^ (2 * r))
        (Set.uIcc (0:ℝ) T) := by
      intro t _
      have h2 : ((-t) ^ r) ^ 2 = t ^ (2 * r) := by
        rw [← pow_mul]
        rw [show (-t) ^ (r * 2) = t ^ (r * 2) from
          Even.neg_pow ⟨r, by ring⟩ t]
        congr 1
        omega
      calc (((-t) ^ r / (r.factorial : ℝ)) ^ 2)
          = ((-t) ^ r) ^ 2 / (r.factorial : ℝ) ^ 2 := by rw [div_pow]
        _ = ((r.factorial : ℝ) ^ 2)⁻¹ * t ^ (2 * r) := by
            rw [h2, div_eq_inv_mul]
    rw [intervalIntegral.integral_congr h1,
      intervalIntegral.integral_const_mul, integral_pow]
    have hne1 : ((r.factorial : ℝ)) ≠ 0 := by
      exact_mod_cast r.factorial_ne_zero
    have hne2 : (2 * (r : ℝ) + 1) ≠ 0 := by positivity
    rw [zero_pow (by omega : 2 * r + 1 ≠ 0)]
    push_cast
    field_simp
    ring
  have hcoefK : (T ^ (2 * r + 1)
        / ((r.factorial : ℝ) ^ 2 * (2 * (r : ℝ) + 1)))
      • (depthD H S r ∘L Sig ∘L (depthD H S r)†)
      = ∫ t in (0:ℝ)..T, (((-t) ^ r / (r.factorial : ℝ)) ^ 2)
          • (depthD H S r ∘L Sig ∘L (depthD H S r)†) := by
    rw [intervalIntegral.integral_smul_const, hcoef]
  have hmain0 : (depthN H S r).starProjection ∘L gramW H Sig T
        ∘L (depthN H S r).starProjection
      - (T ^ (2 * r + 1)
          / ((r.factorial : ℝ) ^ 2 * (2 * (r : ℝ) + 1)))
        • (depthD H S r ∘L Sig ∘L (depthD H S r)†)
      = ∫ t in (0:ℝ)..T,
          ((depthN H S r).starProjection
              ∘L (expH H t ∘L Sig ∘L (expH H t)†)
              ∘L (depthN H S r).starProjection
            - (((-t) ^ r / (r.factorial : ℝ)) ^ 2)
              • (depthD H S r ∘L Sig ∘L (depthD H S r)†)) := by
    rw [hPrW, hcoefK, ← intervalIntegral.integral_sub hint1 hint2]
  have hbound : ∀ t ∈ Set.uIoc (0:ℝ) T,
      ‖(depthN H S r).starProjection
          ∘L (expH H t ∘L Sig ∘L (expH H t)†)
          ∘L (depthN H S r).starProjection
        - (((-t) ^ r / (r.factorial : ℝ)) ^ 2)
          • (depthD H S r ∘L Sig ∘L (depthD H S r)†)‖
      ≤ (expTailC H * ‖Sig‖ * (‖depthD H S r‖ + expTailC H)
          + ‖depthD H S r‖ * ‖Sig‖ * expTailC H) * T ^ (2 * r + 1) := by
    intro t ht
    rw [Set.uIoc_of_le (le_of_lt hT0)] at ht
    have h6 := depth_sandwich_bound (H := H) (S := S) Sig r
      (le_of_lt ht.1) (le_trans ht.2 hT1)
    rw [← depth_compress_eq Sig hSig r t] at h6
    refine le_trans h6 ?_
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (le_of_lt ht.1) ht.2 _) hCnn
  have h8 := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [← hmain0] at h8
  have hfinal : ‖(depthN H S r).starProjection ∘L gramW H Sig T
        ∘L (depthN H S r).starProjection
      - (T ^ (2 * r + 1)
          / ((r.factorial : ℝ) ^ 2 * (2 * (r : ℝ) + 1)))
        • (depthD H S r ∘L Sig ∘L (depthD H S r)†)‖
      ≤ (expTailC H * ‖Sig‖ * (‖depthD H S r‖ + expTailC H)
          + ‖depthD H S r‖ * ‖Sig‖ * expTailC H)
        * ‖T ^ (2 * r + 2)‖ := by
    refine le_trans h8 (le_of_eq ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (le_of_lt hT0) _),
      sub_zero, abs_of_pos hT0, mul_assoc, ← pow_succ,
      show 2 * r + 1 + 1 = 2 * r + 2 from by omega]
  exact hfinal

/-- **(SMET.22)** Short-time depth-block asymptotics of the normalized
horizon Gramian `Ŵ_{T,B} = ∫₀ᵀ e^{-tH} P_B (e^{-tH})^* dt`:
`P_r Ŵ_{T,B} P_r = (T^{2r+1}/((r!)^2(2r+1))) D_r D_r^* + O(T^{2r+2})`
as `T ↓ 0`. -/
theorem source_metric_depth_normalized (r : ℕ) :
    (fun T : ℝ =>
        (depthN H S r).starProjection ∘L gramW H S.starProjection T
            ∘L (depthN H S r).starProjection
          - (T ^ (2 * r + 1)
              / ((r.factorial : ℝ) ^ 2 * (2 * (r : ℝ) + 1)))
            • (depthD H S r ∘L (depthD H S r)†))
      =O[𝓝[>] (0 : ℝ)] fun T : ℝ => T ^ (2 * r + 2) := by
  have hidem : S.starProjection ∘L S.starProjection
      = S.starProjection := by
    ext x
    change S.starProjection (S.starProjection x) = S.starProjection x
    exact Submodule.starProjection_eq_self_iff.mpr
      (S.starProjection_apply_mem x)
  have hproj : S.starProjection
      = S.starProjection ∘L S.starProjection ∘L S.starProjection := by
    rw [hidem, hidem]
  have h1 := source_metric_depth_gramian (H := H) (S := S)
    S.starProjection hproj r
  have h2 : depthD H S r ∘L S.starProjection ∘L (depthD H S r)†
      = depthD H S r ∘L (depthD H S r)† := by
    have h3 : depthD H S r ∘L S.starProjection = depthD H S r := by
      have h4 : depthD H S r ∘L S.starProjection
          = (depthN H S r).starProjection ∘L (H ^ r)
            ∘L (S.starProjection ∘L S.starProjection) := by
        ext x
        rfl
      rw [h4, hidem]
      rfl
    rw [← ContinuousLinearMap.comp_assoc, h3]
  rw [h2] at h1
  exact h1

end SourceMetricDepth

section SourceMetricHorizon

open ContinuousLinearMap Submodule Filter Topology Upstream

open scoped InnerProduct ComplexInnerProductSpace

variable {V E E' G : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [FiniteDimensional ℂ E']
  [NormedAddCommGroup G] [InnerProductSpace ℂ G] [FiniteDimensional ℂ G]

/-! ### Record 9 toolkit: operator-valued interval integrals -/

/-- A nonnegative continuous function with vanishing horizon integral
vanishes inside the horizon (fundamental theorem of calculus). -/
theorem interior_zero_of_integral_zero {g : ℝ → ℝ} (hg : Continuous g)
    (hnn : ∀ s : ℝ, 0 ≤ g s) {T : ℝ}
    (hzero : (∫ s in (0:ℝ)..T, g s) = 0) {t : ℝ}
    (ht : t ∈ Set.Ioo 0 T) : g t = 0 := by
  have hGzero : ∀ s ∈ Set.Icc (0:ℝ) T, (∫ u in (0:ℝ)..s, g u) = 0 := by
    intro s hs
    have h1 : 0 ≤ ∫ u in (0:ℝ)..s, g u :=
      intervalIntegral.integral_nonneg hs.1 fun u _ => hnn u
    have h2 : 0 ≤ ∫ u in s..T, g u :=
      intervalIntegral.integral_nonneg hs.2 fun u _ => hnn u
    have h3 : (∫ u in (0:ℝ)..s, g u) + ∫ u in s..T, g u = 0 := by
      rw [intervalIntegral.integral_add_adjacent_intervals
        (hg.intervalIntegrable 0 s) (hg.intervalIntegrable s T), hzero]
    linarith
  have hd : HasDerivAt (fun s => ∫ u in (0:ℝ)..s, g u) (g t) t :=
    intervalIntegral.integral_hasDerivAt_right
      (hg.intervalIntegrable 0 t)
      (hg.stronglyMeasurableAtFilter MeasureTheory.volume (𝓝 t))
      hg.continuousAt
  have hev : (fun s => ∫ u in (0:ℝ)..s, g u) =ᶠ[𝓝 t] fun _ => (0:ℝ) := by
    refine Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds ht) ?_
    intro s hs
    exact hGzero s (Set.mem_Icc.mpr ⟨le_of_lt hs.1, le_of_lt hs.2⟩)
  have hd0 : HasDerivAt (fun s => ∫ u in (0:ℝ)..s, g u) 0 t :=
    (hasDerivAt_const t (0:ℝ)).congr_of_eventuallyEq hev
  exact hd.unique hd0

/-- The adjoint as a real-linear isometry of the operator algebra. -/
noncomputable def adjointRealIsometry :
    (G →L[ℂ] G) →ₗᵢ[ℝ] (G →L[ℂ] G) where
  toLinearMap :=
    { toFun := fun A => A†
      map_add' := fun A B => by
        rw [← ContinuousLinearMap.star_eq_adjoint,
          ← ContinuousLinearMap.star_eq_adjoint,
          ← ContinuousLinearMap.star_eq_adjoint]
        exact star_add A B
      map_smul' := fun c A => by
        rw [RingHom.id_apply]
        exact adjoint_real_smul c A }
  norm_map' := fun A => ContinuousLinearMap.adjoint.norm_map A

/-- Pointwise adjoints pass through operator-valued interval
integrals. -/
theorem intervalIntegral_adjoint (f : ℝ → G →L[ℂ] G) (a b : ℝ) :
    (∫ t in a..b, (f t)†) = (∫ t in a..b, f t)† := by
  have h := (adjointRealIsometry (G := G)).intervalIntegral_comp_comm
    (a := a) (b := b) (μ := MeasureTheory.volume) f
  calc (∫ t in a..b, (f t)†)
      = ∫ t in a..b, adjointRealIsometry (f t) :=
        intervalIntegral.integral_congr fun t _ => rfl
    _ = adjointRealIsometry (∫ t in a..b, f t) := h
    _ = (∫ t in a..b, f t)† := rfl

/-- Pointwise self-adjointness passes to interval integrals. -/
theorem intervalIntegral_isSelfAdjoint {f : ℝ → G →L[ℂ] G} {a b : ℝ}
    (hsym : ∀ t, IsSelfAdjoint (f t)) :
    IsSelfAdjoint (∫ t in a..b, f t) := by
  rw [isSelfAdjoint_iff', ← intervalIntegral_adjoint f]
  exact intervalIntegral.integral_congr fun t _ =>
    isSelfAdjoint_iff'.mp (hsym t)

/-- Inner pairings pass through operator-valued interval integrals. -/
theorem intervalIntegral_inner_apply {f : ℝ → G →L[ℂ] G} {a b : ℝ}
    (hf : IntervalIntegrable f MeasureTheory.volume a b) (x y : G) :
    (⟪y, (∫ t in a..b, f t) x⟫ : ℂ) = ∫ t in a..b, (⟪y, f t x⟫ : ℂ) := by
  have h := ((innerSL ℂ y).comp
    (ContinuousLinearMap.apply ℂ G x)).intervalIntegral_comp_comm hf
  calc (⟪y, (∫ t in a..b, f t) x⟫ : ℂ)
      = ((innerSL ℂ y).comp (ContinuousLinearMap.apply ℂ G x))
          (∫ t in a..b, f t) := rfl
    _ = ∫ t in a..b, ((innerSL ℂ y).comp
          (ContinuousLinearMap.apply ℂ G x)) (f t) := h.symm
    _ = ∫ t in a..b, (⟪y, f t x⟫ : ℂ) :=
        intervalIntegral.integral_congr fun t _ => rfl

/-- Real diagonal weights of an operator-valued interval integral. -/
theorem intervalIntegral_re_inner_apply {f : ℝ → G →L[ℂ] G} {a b : ℝ}
    (hf : IntervalIntegrable f MeasureTheory.volume a b) (x : G) :
    (∫ t in a..b, ((⟪x, f t x⟫ : ℂ)).re)
      = ((⟪x, (∫ t in a..b, f t) x⟫ : ℂ)).re := by
  have h4 : IntervalIntegrable (fun t => (⟪x, f t x⟫ : ℂ))
      MeasureTheory.volume a b :=
    ⟨((innerSL ℂ x).comp
        (ContinuousLinearMap.apply ℂ G x)).integrable_comp hf.1,
      ((innerSL ℂ x).comp
        (ContinuousLinearMap.apply ℂ G x)).integrable_comp hf.2⟩
  calc (∫ t in a..b, ((⟪x, f t x⟫ : ℂ)).re)
      = ∫ t in a..b, RCLike.re (⟪x, f t x⟫ : ℂ) :=
        intervalIntegral.integral_congr fun t _ =>
          (RCLike.re_to_complex).symm
    _ = RCLike.re (∫ t in a..b, (⟪x, f t x⟫ : ℂ)) :=
        intervalIntegral.intervalIntegral_re h4
    _ = ((∫ t in a..b, (⟪x, f t x⟫ : ℂ))).re := RCLike.re_to_complex
    _ = ((⟪x, (∫ t in a..b, f t) x⟫ : ℂ)).re := by
        rw [intervalIntegral_inner_apply hf x x]

omit [FiniteDimensional ℂ G] in
/-- Diagonal weights of positive operators are nonnegative (right-slot
form). -/
theorem isPositive_re_inner_right_nonneg {A : G →L[ℂ] G}
    (hA : A.IsPositive) (x : G) : 0 ≤ ((⟪x, A x⟫ : ℂ)).re := by
  have h3 := hA.2 x
  have h4 : ContinuousLinearMap.reApplyInnerSelf A x
      = ((⟪A x, x⟫ : ℂ)).re := by
    unfold ContinuousLinearMap.reApplyInnerSelf
    rw [RCLike.re_to_complex]
  rw [h4] at h3
  rw [← inner_conj_symm, Complex.conj_re]
  exact h3

/-- Pointwise positivity passes to interval integrals over ordered
horizons. -/
theorem intervalIntegral_isPositive {f : ℝ → G →L[ℂ] G} {a b : ℝ}
    (hab : a ≤ b) (hf : IntervalIntegrable f MeasureTheory.volume a b)
    (hpos : ∀ t, (f t).IsPositive) :
    (∫ t in a..b, f t).IsPositive := by
  refine ContinuousLinearMap.isPositive_def'.mpr
    ⟨intervalIntegral_isSelfAdjoint fun t => (hpos t).isSelfAdjoint, ?_⟩
  intro x
  have h1 : 0 ≤ ((⟪x, (∫ t in a..b, f t) x⟫ : ℂ)).re := by
    rw [← intervalIntegral_re_inner_apply hf x]
    exact intervalIntegral.integral_nonneg hab fun u _ =>
      isPositive_re_inner_right_nonneg (hpos u) x
  have h2 : ContinuousLinearMap.reApplyInnerSelf (∫ t in a..b, f t) x
      = ((⟪(∫ t in a..b, f t) x, x⟫ : ℂ)).re := by
    unfold ContinuousLinearMap.reApplyInnerSelf
    rw [RCLike.re_to_complex]
  rw [h2, ← inner_conj_symm, Complex.conj_re]
  exact h1

/-- Fixed compositions on both sides commute with operator-valued
interval integrals. -/
theorem compress_intervalIntegral₂ {G₁ G₂ : Type*}
    [NormedAddCommGroup G₁] [NormedSpace ℂ G₁] [CompleteSpace G₁]
    [NormedAddCommGroup G₂] [NormedSpace ℂ G₂]
    (A : G →L[ℂ] G₁) (Bc : G₂ →L[ℂ] G) {f : ℝ → G →L[ℂ] G} {a b : ℝ}
    (hf : IntervalIntegrable f MeasureTheory.volume a b) :
    A ∘L (∫ t in a..b, f t) ∘L Bc = ∫ t in a..b, A ∘L f t ∘L Bc := by
  let Phi : (G →L[ℂ] G) →ₗ[ℂ] (G₂ →L[ℂ] G₁) :=
    { toFun := fun X => A ∘L X ∘L Bc
      map_add' := fun X Y => by
        rw [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]
      map_smul' := fun cx X => by
        rw [RingHom.id_apply, ContinuousLinearMap.smul_comp,
          ContinuousLinearMap.comp_smul] }
  have h := (LinearMap.toContinuousLinearMap Phi).intervalIntegral_comp_comm
    hf
  calc A ∘L (∫ t in a..b, f t) ∘L Bc
      = LinearMap.toContinuousLinearMap Phi (∫ t in a..b, f t) := rfl
    _ = ∫ t in a..b, LinearMap.toContinuousLinearMap Phi (f t) := h.symm
    _ = ∫ t in a..b, A ∘L f t ∘L Bc :=
        intervalIntegral.integral_congr fun t _ => rfl

/-! ### Record 9: any positive horizon spans the cyclic carrier -/

/-- Interior horizon times cluster inside the horizon bank. -/
theorem horizon_cluster {T t : ℝ} (ht : t ∈ Set.Ioo 0 T) :
    (𝓝[Set.Ioo 0 T \ {t}] t).NeBot := by
  have h1 : t ∈ closure (Set.Ioo 0 t) := by
    rw [closure_Ioo (ne_of_lt ht.1)]
    exact Set.mem_Icc.mpr ⟨le_of_lt ht.1, le_rfl⟩
  have h2 : (𝓝[Set.Ioo 0 t] t).NeBot :=
    mem_closure_iff_nhdsWithin_neBot.mp h1
  refine Filter.neBot_of_le (f := 𝓝[Set.Ioo 0 t] t) ?_
  refine nhdsWithin_mono t ?_
  intro s hs
  exact ⟨⟨hs.1, lt_trans hs.2 ht.2⟩, fun heq =>
    absurd (Set.mem_singleton_iff.mp heq) (ne_of_lt hs.2)⟩

omit [FiniteDimensional ℂ E] in
/-- The generator preserves horizon bank spans. -/
theorem generator_maps_horizon {T : ℝ} (H : V →L[ℂ] V) (B : E →L[ℂ] V)
    {v : V} (hv : v ∈ bankSpan H B (Set.Ioo 0 T)) :
    H v ∈ bankSpan H B (Set.Ioo 0 T) := by
  induction hv using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨t, ht, u, rfl⟩ := hw
    exact generator_apply_mem_bankSpan H B ht (horizon_cluster ht) u
  | zero =>
    rw [map_zero]
    exact (bankSpan H B (Set.Ioo 0 T)).zero_mem
  | add x y _ _ hx hy =>
    rw [map_add]
    exact (bankSpan H B (Set.Ioo 0 T)).add_mem hx hy
  | smul c x _ hx =>
    rw [map_smul]
    exact (bankSpan H B (Set.Ioo 0 T)).smul_mem c hx

omit [FiniteDimensional ℂ E] in
/-- The source range is the zero-time limit of the horizon bank. -/
theorem range_le_horizon_bankSpan {T : ℝ} (hT : 0 < T) (H : V →L[ℂ] V)
    (B : E →L[ℂ] V) :
    B.range ≤ bankSpan H B (Set.Ioo 0 T) := by
  rintro v ⟨u, rfl⟩
  have hne : (𝓝[Set.Ioo 0 T] (0:ℝ)).NeBot := by
    refine mem_closure_iff_nhdsWithin_neBot.mp ?_
    rw [closure_Ioo (ne_of_lt hT)]
    exact Set.mem_Icc.mpr ⟨le_rfl, le_of_lt hT⟩
  have hlim : Tendsto (fun s : ℝ => expH H s (B u)) (𝓝[Set.Ioo 0 T] 0)
      (𝓝 (B u)) := by
    have h0 : Tendsto (fun s : ℝ => expH H s (B u)) (𝓝 0)
        (𝓝 (expH H 0 (B u))) := (expH_apply_continuous H (B u)).tendsto 0
    have h1 : expH H 0 (B u) = B u := by
      rw [expH_zero, one_apply_eq_self]
    rw [h1] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  exact (bankSpan H B
    (Set.Ioo 0 T)).closed_of_finiteDimensional.mem_of_tendsto hlim
    (eventually_nhdsWithin_of_forall fun s hs =>
      expH_apply_mem_bankSpan H B hs u)

omit [FiniteDimensional ℂ E] in
/-- **(SMET.14, span form)** Every positive horizon spans the full
cyclic carrier: `span{e^{-tH}Bu : 0 < t < T} = 𝓒_H(B)`. -/
theorem horizon_bankSpan_eq_cyc {T : ℝ} (hT : 0 < T) (H : V →L[ℂ] V)
    (B : E →L[ℂ] V) : bankSpan H B (Set.Ioo 0 T) = cyc H B := by
  refine le_antisymm (bankSpan_mono H B fun s hs => le_of_lt hs.1) ?_
  rw [cyc_eq_krylovSpan]
  refine Submodule.span_le.mpr ?_
  rintro v ⟨n, u, rfl⟩
  induction n with
  | zero =>
    have h0 : (H ^ 0) (B u) = B u := by
      rw [pow_zero]
      rfl
    rw [h0]
    exact range_le_horizon_bankSpan hT H B ⟨u, rfl⟩
  | succ n ih =>
    have h : (H ^ (n + 1)) (B u) = H ((H ^ n) (B u)) := by
      rw [pow_succ']
      rfl
    rw [h]
    exact generator_maps_horizon H B ih

omit [FiniteDimensional ℂ E] in
/-- The heat semigroup preserves the cyclic carrier at nonnegative
times. -/
theorem expH_maps_cyc (H : V →L[ℂ] V) (B : E →L[ℂ] V) {t : ℝ}
    (ht : 0 ≤ t) {v : V} (hv : v ∈ cyc H B) : expH H t v ∈ cyc H B := by
  induction hv using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨s, hs, u, rfl⟩ := hw
    have h1 : expH H t (expH H s (B u)) = expH H (t + s) (B u) := by
      have h2 := expH_mul H t s
      calc expH H t (expH H s (B u))
          = (expH H t * expH H s) (B u) := rfl
        _ = expH H (t + s) (B u) := by rw [h2]
    rw [h1]
    exact expH_apply_mem_bankSpan H B
      (Set.mem_Ici.mpr (add_nonneg ht (Set.mem_Ici.mp hs))) u
  | zero =>
    rw [map_zero]
    exact (cyc H B).zero_mem
  | add x y _ _ hx hy =>
    rw [map_add]
    exact (cyc H B).add_mem hx hy
  | smul c x _ hx =>
    rw [map_smul]
    exact (cyc H B).smul_mem c hx

/-! ### Record 9: the metric source kernel `Σ_{B,M} = B M^† B^*` -/

/-- The adjoint annihilates exactly the range complement. -/
theorem adjoint_apply_eq_zero_iff (B : E →L[ℂ] V) (x : V) :
    (B†) x = 0 ↔ x ∈ (B.range)ᗮ := by
  rw [ContinuousLinearMap.orthogonal_range]
  exact Iff.symm LinearMap.mem_ker

/-- Range–kernel duality for self-adjoint operators in finite
dimension. -/
theorem range_eq_ker_orthogonal {M : E →L[ℂ] E} (hM : IsSelfAdjoint M) :
    M.range = (M.ker)ᗮ := by
  have h1 : (M.range)ᗮ = M.ker := by
    rw [ContinuousLinearMap.orthogonal_range, hM.adjoint_eq]
  calc M.range = ((M.range)ᗮ)ᗮ := (Submodule.orthogonal_orthogonal _).symm
    _ = (M.ker)ᗮ := by rw [h1]

/-- An operator ignores the kernel component of its argument. -/
theorem apply_starProjection_ker_orthogonal (M : E →L[ℂ] E) (w : E) :
    M ((M.ker)ᗮ.starProjection w) = M w := by
  have h1 : w - (M.ker)ᗮ.starProjection w ∈ M.ker := by
    have h2 := (M.ker)ᗮ.sub_starProjection_mem_orthogonal w
    rwa [Submodule.orthogonal_orthogonal] at h2
  have h3 : M (w - (M.ker)ᗮ.starProjection w) = 0 := LinearMap.mem_ker.mp h1
  rw [map_sub, sub_eq_zero] at h3
  exact h3.symm

/-- Null-cost consistency lets the source map absorb the metric support
projection. -/
theorem null_cost_absorb {B : E →L[ℂ] V} {M : E →L[ℂ] E}
    (hM : IsSelfAdjoint M) (hnc : (B†).range ≤ M.range) :
    B ∘L (M.ker)ᗮ.starProjection = B := by
  ext u
  have h1 : u - (M.ker)ᗮ.starProjection u ∈ M.ker := by
    have h2 := (M.ker)ᗮ.sub_starProjection_mem_orthogonal u
    rwa [Submodule.orthogonal_orthogonal] at h2
  have h3 : B (u - (M.ker)ᗮ.starProjection u) = 0 := by
    have h4 : ∀ x : V, (⟪B (u - (M.ker)ᗮ.starProjection u), x⟫ : ℂ) = 0 := by
      intro x
      have h5 : (B†) x ∈ M.range := hnc ⟨x, rfl⟩
      rw [range_eq_ker_orthogonal hM] at h5
      calc (⟪B (u - (M.ker)ᗮ.starProjection u), x⟫ : ℂ)
          = ⟪u - (M.ker)ᗮ.starProjection u, (B†) x⟫ :=
            (ContinuousLinearMap.adjoint_inner_right B _ x).symm
        _ = 0 := (Submodule.mem_orthogonal _ _).mp h5 _ h1
    exact inner_self_eq_zero.mp (h4 (B (u - (M.ker)ᗮ.starProjection u)))
  have h8 : B u - B ((M.ker)ᗮ.starProjection u) = 0 := by
    rw [← map_sub]
    exact h3
  calc (B ∘L (M.ker)ᗮ.starProjection) u
      = B ((M.ker)ᗮ.starProjection u) := rfl
    _ = B u := (sub_eq_zero.mp h8).symm

/-- The finite-dimensional Moore–Penrose inverse of an endomorphism. -/
noncomputable def fdPinv (M : E →L[ℂ] E) : E →L[ℂ] E :=
  ClosedRangeMoorePenrose.pinv M (M.range).closed_of_finiteDimensional

/-- The Penrose kernel-complement identity for `fdPinv`. -/
theorem fdPinv_apply (M : E →L[ℂ] E) (x : E) :
    fdPinv M (M x) = (M.ker)ᗮ.starProjection x :=
  ClosedRangeMoorePenrose.pinv_apply M _ x

/-- The Penrose range-projection identity for `fdPinv`. -/
theorem comp_fdPinv (M : E →L[ℂ] E) :
    M ∘L fdPinv M = M.range.starProjection :=
  ClosedRangeMoorePenrose.comp_pinv M _

/-- `fdPinv` takes values in the kernel complement. -/
theorem fdPinv_mem_ker_orthogonal (M : E →L[ℂ] E) (y : E) :
    fdPinv M y ∈ (M.ker)ᗮ :=
  ClosedRangeMoorePenrose.pinv_mem_ker_orthogonal M _ y

/-- `fdPinv` absorbs the range projection. -/
theorem fdPinv_comp_rangeProjection (M : E →L[ℂ] E) :
    fdPinv M ∘L M.range.starProjection = fdPinv M :=
  ClosedRangeMoorePenrose.pinv_comp_rangeProjection M _

/-- `fdPinv` after the operator is the support projection. -/
theorem fdPinv_comp (M : E →L[ℂ] E) :
    fdPinv M ∘L M = (M.ker)ᗮ.starProjection :=
  ClosedRangeMoorePenrose.pinv_comp M _

/-- The Moore–Penrose inverse of a self-adjoint operator is
self-adjoint. -/
theorem fdPinv_isSelfAdjoint {M : E →L[ℂ] E} (hM : IsSelfAdjoint M) :
    IsSelfAdjoint (fdPinv M) := by
  have hcore : ∀ α β : E,
      (⟪fdPinv M (M α), M β⟫ : ℂ) = ⟪M α, fdPinv M (M β)⟫ := by
    intro α β
    rw [fdPinv_apply, fdPinv_apply]
    calc (⟪(M.ker)ᗮ.starProjection α, M β⟫ : ℂ)
        = ⟪(M†) ((M.ker)ᗮ.starProjection α), β⟫ := by
          rw [ContinuousLinearMap.adjoint_inner_left]
      _ = ⟪M ((M.ker)ᗮ.starProjection α), β⟫ := by rw [hM.adjoint_eq]
      _ = ⟪M α, β⟫ := by rw [apply_starProjection_ker_orthogonal]
      _ = ⟪α, (M†) β⟫ :=
          (ContinuousLinearMap.adjoint_inner_right M α β).symm
      _ = ⟪α, M β⟫ := by rw [hM.adjoint_eq]
      _ = ⟪α, M ((M.ker)ᗮ.starProjection β)⟫ := by
          rw [apply_starProjection_ker_orthogonal]
      _ = ⟪α, (M†) ((M.ker)ᗮ.starProjection β)⟫ := by rw [hM.adjoint_eq]
      _ = ⟪M α, (M.ker)ᗮ.starProjection β⟫ :=
          ContinuousLinearMap.adjoint_inner_right M α _
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  have hxy : ∀ z : E, fdPinv M z = fdPinv M (M.range.starProjection z) := by
    intro z
    have h1 : (fdPinv M ∘L M.range.starProjection) z = fdPinv M z := by
      rw [fdPinv_comp_rangeProjection]
    exact h1.symm
  obtain ⟨α, hα0⟩ := M.range.starProjection_apply_mem x
  obtain ⟨β, hβ0⟩ := M.range.starProjection_apply_mem y
  have hα : M α = M.range.starProjection x := hα0
  have hβ : M β = M.range.starProjection y := hβ0
  have hQx : fdPinv M (M.range.starProjection x) ∈ M.range :=
    (range_eq_ker_orthogonal hM).ge (fdPinv_mem_ker_orthogonal M _)
  have hQy : fdPinv M (M.range.starProjection y) ∈ M.range :=
    (range_eq_ker_orthogonal hM).ge (fdPinv_mem_ker_orthogonal M _)
  calc (⟪fdPinv M x, y⟫ : ℂ)
      = ⟪fdPinv M (M.range.starProjection x), y⟫ := by rw [← hxy x]
    _ = ⟪fdPinv M (M.range.starProjection x),
          M.range.starProjection y⟫ := by
        have hy2 : y - M.range.starProjection y ∈ (M.range)ᗮ :=
          M.range.sub_starProjection_mem_orthogonal y
        have h0 : (⟪fdPinv M (M.range.starProjection x),
            y - M.range.starProjection y⟫ : ℂ) = 0 :=
          (Submodule.mem_orthogonal (M.range) _).mp hy2 _ hQx
        have hsplit : (⟪fdPinv M (M.range.starProjection x), y⟫ : ℂ)
            = ⟪fdPinv M (M.range.starProjection x),
                M.range.starProjection y⟫
              + ⟪fdPinv M (M.range.starProjection x),
                  y - M.range.starProjection y⟫ := by
          rw [← inner_add_right]
          congr 1
          abel
        rw [hsplit, h0, add_zero]
    _ = ⟪M α, fdPinv M (M β)⟫ := by
        rw [← hα, ← hβ]
        exact hcore α β
    _ = ⟪M.range.starProjection x,
          fdPinv M (M.range.starProjection y)⟫ := by rw [hα, hβ]
    _ = ⟪x, fdPinv M (M.range.starProjection y)⟫ := by
        have hx2 : x - M.range.starProjection x ∈ (M.range)ᗮ :=
          M.range.sub_starProjection_mem_orthogonal x
        have h0 : (⟪x - M.range.starProjection x,
            fdPinv M (M.range.starProjection y)⟫ : ℂ) = 0 :=
          (Submodule.mem_orthogonal' _ _).mp hx2 _ hQy
        have hsplit : (⟪x, fdPinv M (M.range.starProjection y)⟫ : ℂ)
            = ⟪M.range.starProjection x,
                fdPinv M (M.range.starProjection y)⟫
              + ⟪x - M.range.starProjection x,
                  fdPinv M (M.range.starProjection y)⟫ := by
          rw [← inner_add_left]
          congr 1
          abel
        rw [hsplit, h0, add_zero]
    _ = ⟪x, fdPinv M y⟫ := by rw [← hxy y]

/-- **(SMET.11 input)** The metric source kernel
`Σ_{B,M} = B M^† B^*`. -/
noncomputable def sigmaBM (B : E →L[ℂ] V) (M : E →L[ℂ] E) : V →L[ℂ] V :=
  B ∘L fdPinv M ∘L (B†)

/-- The metric source kernel is positive. -/
theorem sigmaBM_isPositive {B : E →L[ℂ] V} {M : E →L[ℂ] E}
    (hM : M.IsPositive) (hnc : (B†).range ≤ M.range) :
    (sigmaBM B M).IsPositive := by
  constructor
  · rw [← ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
    refine isSelfAdjoint_iff'.mpr ?_
    calc (sigmaBM B M)†
        = ((fdPinv M ∘L (B†))†) ∘L (B†) := by
          rw [sigmaBM, ContinuousLinearMap.adjoint_comp]
    _ = (((B†)†) ∘L (fdPinv M)†) ∘L (B†) := by
          rw [ContinuousLinearMap.adjoint_comp]
    _ = ((B ∘L (fdPinv M)†)) ∘L (B†) := by
          rw [ContinuousLinearMap.adjoint_adjoint]
    _ = (B ∘L fdPinv M) ∘L (B†) := by
          rw [(fdPinv_isSelfAdjoint hM.isSelfAdjoint).adjoint_eq]
    _ = sigmaBM B M := by
          rw [ContinuousLinearMap.comp_assoc]
          rfl
  · intro x
    obtain ⟨w, hw0⟩ := hnc (⟨x, rfl⟩ : (B†) x ∈ (B†).range)
    have hw : M w = (B†) x := hw0
    have h3 : ContinuousLinearMap.reApplyInnerSelf (sigmaBM B M) x
        = ((⟪sigmaBM B M x, x⟫ : ℂ)).re := by
      unfold ContinuousLinearMap.reApplyInnerSelf
      rw [RCLike.re_to_complex]
    rw [h3]
    have h5 : (⟪sigmaBM B M x, x⟫ : ℂ)
        = ⟪fdPinv M ((B†) x), (B†) x⟫ :=
      (ContinuousLinearMap.adjoint_inner_right B _ x).symm
    rw [h5, ← hw, fdPinv_apply,
      ← apply_starProjection_ker_orthogonal M w]
    have h6 : ((⟪(M.ker)ᗮ.starProjection w,
        M ((M.ker)ᗮ.starProjection w)⟫ : ℂ)).re
        = ContinuousLinearMap.reApplyInnerSelf M
          ((M.ker)ᗮ.starProjection w) := by
      unfold ContinuousLinearMap.reApplyInnerSelf
      rw [RCLike.re_to_complex, ← inner_conj_symm, Complex.conj_re]
    rw [h6]
    exact hM.2 _

/-- **(SMET.5, kernel form)** The metric source kernel annihilates
exactly what the adjoint source annihilates. -/
theorem sigmaBM_apply_eq_zero_iff {B : E →L[ℂ] V} {M : E →L[ℂ] E}
    (hM : M.IsPositive) (hnc : (B†).range ≤ M.range) (x : V) :
    sigmaBM B M x = 0 ↔ (B†) x = 0 := by
  constructor
  · intro h
    obtain ⟨w, hw0⟩ := hnc (⟨x, rfl⟩ : (B†) x ∈ (B†).range)
    have hw : M w = (B†) x := hw0
    have h1 : ((⟪sigmaBM B M x, x⟫ : ℂ)).re = 0 := by
      rw [h, inner_zero_left]
      exact Complex.zero_re
    have h5 : (⟪sigmaBM B M x, x⟫ : ℂ)
        = ⟪fdPinv M ((B†) x), (B†) x⟫ :=
      (ContinuousLinearMap.adjoint_inner_right B _ x).symm
    rw [h5, ← hw, fdPinv_apply,
      ← apply_starProjection_ker_orthogonal M w] at h1
    have h6 : ((⟪M ((M.ker)ᗮ.starProjection w),
        (M.ker)ᗮ.starProjection w⟫ : ℂ)).re = 0 := by
      rw [← inner_conj_symm, Complex.conj_re]
      exact h1
    have h7 : M ((M.ker)ᗮ.starProjection w) = 0 :=
      isPositive_apply_eq_zero_of_re_inner hM h6
    have h8 : M w = 0 := by
      rw [← apply_starProjection_ker_orthogonal M w]
      exact h7
    rw [← hw, h8]
  · intro h
    have h1 : sigmaBM B M x = B (fdPinv M ((B†) x)) := rfl
    rw [h1, h, map_zero, map_zero]

/-! ### Record 9: horizon Gramians and their common support (SMET.14/15) -/

/-- **(SMET.11)** The physical horizon Gramian `𝒲_{T;B,M}`. -/
noncomputable def horW (H : V →L[ℂ] V) (B : E →L[ℂ] V) (M : E →L[ℂ] E)
    (T : ℝ) : V →L[ℂ] V :=
  gramW H (sigmaBM B M) T

/-- **(SMET.12)** The range-normalized horizon Gramian `Ŵ_{T,B}`. -/
noncomputable def horWhat (H : V →L[ℂ] V) (B : E →L[ℂ] V) (T : ℝ) :
    V →L[ℂ] V :=
  gramW H (rangeProj B) T

/-- The range projection annihilates exactly what the adjoint source
annihilates. -/
theorem rangeProj_apply_eq_zero_iff (B : E →L[ℂ] V) (x : V) :
    rangeProj B x = 0 ↔ (B†) x = 0 := by
  rw [adjoint_apply_eq_zero_iff B x]
  exact Submodule.starProjection_apply_eq_zero_iff (K := B.range)

/-- The range projection is positive. -/
theorem rangeProj_isPositive (B : E →L[ℂ] V) : (rangeProj B).IsPositive :=
  ContinuousLinearMap.IsPositive.of_isStarProjection
    (isStarProjection_starProjection)

/-- Horizon Gramians of positive kernels are positive. -/
theorem gramW_isPositive {H Sig : V →L[ℂ] V} (hSig : Sig.IsPositive)
    {T : ℝ} (hT : 0 ≤ T) : (gramW H Sig T).IsPositive := by
  have hint := (gramW_integrand_continuous H Sig).intervalIntegrable
    (μ := MeasureTheory.volume) 0 T
  exact intervalIntegral_isPositive hT hint fun t =>
    hSig.conj_adjoint (expH H t)

/-- **(SMET.14, kernel form)** The horizon Gramian of a source-matched
positive kernel annihilates exactly the anti-cyclic directions. -/
theorem gramW_ker_eq {H Sig : V →L[ℂ] V} (hH : IsSelfAdjoint H)
    (hSig : Sig.IsPositive) (B : E →L[ℂ] V)
    (hker : ∀ x : V, Sig x = 0 ↔ (B†) x = 0)
    {T : ℝ} (hT : 0 < T) :
    (gramW H Sig T).ker = (cyc H B)ᗮ := by
  have hint : IntervalIntegrable
      (fun t => expH H t ∘L Sig ∘L (expH H t)†)
      MeasureTheory.volume 0 T :=
    (gramW_integrand_continuous H Sig).intervalIntegrable 0 T
  ext x
  constructor
  · intro hx
    have hWx : gramW H Sig T x = 0 := LinearMap.mem_ker.mp hx
    have hgc : Continuous fun s : ℝ =>
        ((⟪x, (expH H s ∘L Sig ∘L (expH H s)†) x⟫ : ℂ)).re := by
      refine Complex.continuous_re.comp ?_
      refine Continuous.inner continuous_const ?_
      exact isBoundedBilinearMap_apply.continuous.comp
        ((gramW_integrand_continuous H Sig).prodMk continuous_const)
    have hgnn : ∀ s : ℝ,
        0 ≤ ((⟪x, (expH H s ∘L Sig ∘L (expH H s)†) x⟫ : ℂ)).re :=
      fun s => isPositive_re_inner_right_nonneg
        (hSig.conj_adjoint (expH H s)) x
    have h7 : (∫ t in (0:ℝ)..T,
        ((⟪x, (expH H t ∘L Sig ∘L (expH H t)†) x⟫ : ℂ)).re) = 0 := by
      rw [intervalIntegral_re_inner_apply hint x]
      have h8 : (∫ t in (0:ℝ)..T, expH H t ∘L Sig ∘L (expH H t)†) x = 0 :=
        hWx
      rw [h8, inner_zero_right]
      exact Complex.zero_re
    have h9 : ∀ t ∈ Set.Ioo (0:ℝ) T, Sig (expH H t x) = 0 := by
      intro t ht
      have h10 := interior_zero_of_integral_zero hgc hgnn h7 ht
      have h11 : (⟪x, (expH H t ∘L Sig ∘L (expH H t)†) x⟫ : ℂ)
          = ⟪((expH H t)†) x, Sig (((expH H t)†) x)⟫ := by
        have h12 : (expH H t ∘L Sig ∘L (expH H t)†) x
            = expH H t (Sig (((expH H t)†) x)) := rfl
        rw [h12]
        exact (ContinuousLinearMap.adjoint_inner_left (expH H t) _ x).symm
      have h13 : ((⟪((expH H t)†) x, Sig (((expH H t)†) x)⟫ : ℂ)).re = 0 := by
        rw [← h11]
        exact h10
      have h14 : ((⟪Sig (((expH H t)†) x), ((expH H t)†) x⟫ : ℂ)).re = 0 := by
        rw [← inner_conj_symm, Complex.conj_re]
        exact h13
      have h15 : Sig (((expH H t)†) x) = 0 :=
        isPositive_apply_eq_zero_of_re_inner hSig h14
      rwa [expH_adjoint hH t] at h15
    have h16 : ∀ t ∈ Set.Ioo (0:ℝ) T, ∀ u : E,
        (⟪expH H t (B u), x⟫ : ℂ) = 0 := by
      intro t ht u
      have h17 : (B†) (expH H t x) = 0 := (hker _).mp (h9 t ht)
      have h18 : expH H t x ∈ (B.range)ᗮ :=
        (adjoint_apply_eq_zero_iff B _).mp h17
      have h19 : (⟪B u, expH H t x⟫ : ℂ) = 0 :=
        (Submodule.mem_orthogonal _ _).mp h18 (B u) ⟨u, rfl⟩
      calc (⟪expH H t (B u), x⟫ : ℂ)
          = ⟪B u, ((expH H t)†) x⟫ :=
            (ContinuousLinearMap.adjoint_inner_right
              (expH H t) (B u) x).symm
        _ = ⟪B u, expH H t x⟫ := by rw [expH_adjoint hH t]
        _ = 0 := h19
    rw [← horizon_bankSpan_eq_cyc hT H B, Submodule.mem_orthogonal]
    intro v hv
    induction hv using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨t, ht, u, rfl⟩ := hw
      exact h16 t ht u
    | zero => exact inner_zero_left x
    | add a bb _ _ ha hb =>
      rw [inner_add_left, ha, hb, add_zero]
    | smul c a _ ha =>
      rw [inner_smul_left, ha, mul_zero]
  · intro hx
    rw [LinearMap.mem_ker]
    have h20 : ∀ t ∈ Set.uIcc (0:ℝ) T,
        (expH H t ∘L Sig ∘L (expH H t)†) x = 0 := by
      intro t ht
      rw [Set.uIcc_of_le (le_of_lt hT)] at ht
      have ht0 : 0 ≤ t := ht.1
      have h21 : expH H t x ∈ (cyc H B)ᗮ := by
        rw [Submodule.mem_orthogonal] at hx ⊢
        intro v hv
        calc (⟪v, expH H t x⟫ : ℂ)
            = ⟪((expH H t)†) v, x⟫ :=
              (ContinuousLinearMap.adjoint_inner_left (expH H t) x v).symm
          _ = ⟪expH H t v, x⟫ := by rw [expH_adjoint hH t]
          _ = 0 := hx _ (expH_maps_cyc H B ht0 hv)
      have h22 : (B†) (((expH H t)†) x) = 0 := by
        rw [expH_adjoint hH t, adjoint_apply_eq_zero_iff]
        have h23 : B.range ≤ cyc H B :=
          range_le_bankSpan H B (Set.mem_Ici.mpr le_rfl)
        exact Submodule.orthogonal_le h23 h21
      have h24 : Sig (((expH H t)†) x) = 0 := (hker _).mpr h22
      have h25 : (expH H t ∘L Sig ∘L (expH H t)†) x
          = expH H t (Sig (((expH H t)†) x)) := rfl
      rw [h25, h24, map_zero]
    have h26 : gramW H Sig T x
        = ∫ t in (0:ℝ)..T, (expH H t ∘L Sig ∘L (expH H t)†) x :=
      ContinuousLinearMap.intervalIntegral_apply hint x
    change gramW H Sig T x = 0
    rw [h26]
    have h27 : Set.EqOn (fun t => (expH H t ∘L Sig ∘L (expH H t)†) x)
        (fun _ => (0:V)) (Set.uIcc (0:ℝ) T) := fun t ht => h20 t ht
    rw [intervalIntegral.integral_congr h27, intervalIntegral.integral_zero]

/-- **(SMET.14, range form)** The horizon Gramian of a source-matched
positive kernel has exactly the cyclic carrier as range. -/
theorem gramW_range_eq {H Sig : V →L[ℂ] V} (hH : IsSelfAdjoint H)
    (hSig : Sig.IsPositive) (B : E →L[ℂ] V)
    (hker : ∀ x : V, Sig x = 0 ↔ (B†) x = 0)
    {T : ℝ} (hT : 0 < T) :
    (gramW H Sig T).range = cyc H B := by
  rw [range_eq_ker_orthogonal
      (gramW_isPositive hSig (le_of_lt hT)).isSelfAdjoint,
    gramW_ker_eq hH hSig B hker hT, Submodule.orthogonal_orthogonal]

/-- **(SMET.14)** Metric-covariant horizon support: for every
null-cost-consistent packet and every `T > 0`, both horizon Gramians
are supported exactly on the source-cyclic carrier
`supp 𝒲_{T;B,M} = supp Ŵ_{T,B} = P_H^B`. -/
theorem source_metric_horizon_support (H : V →L[ℂ] V) (B : E →L[ℂ] V)
    (M : E →L[ℂ] E) (hH : IsSelfAdjoint H) (hM : M.IsPositive)
    (hnc : (B†).range ≤ M.range) {T : ℝ} (hT : 0 < T) :
    (horW H B M T).range = cyc H B ∧ (horWhat H B T).range = cyc H B ∧
    (horW H B M T).ker = (cyc H B)ᗮ ∧
    (horWhat H B T).ker = (cyc H B)ᗮ :=
  ⟨gramW_range_eq hH (sigmaBM_isPositive hM hnc) B
      (sigmaBM_apply_eq_zero_iff hM hnc) hT,
    gramW_range_eq hH (rangeProj_isPositive B) B
      (rangeProj_apply_eq_zero_iff B) hT,
    gramW_ker_eq hH (sigmaBM_isPositive hM hnc) B
      (sigmaBM_apply_eq_zero_iff hM hnc) hT,
    gramW_ker_eq hH (rangeProj_isPositive B) B
      (rangeProj_apply_eq_zero_iff B) hT⟩

/-- **(SMET.15)** Invariant zero atom: the zero spectral projection of
either horizon Gramian compresses through the target synthesis to the
dynamic residual `R_dyn`. -/
theorem source_metric_horizon_zero_atom (H : V →L[ℂ] V) (B : E →L[ℂ] V)
    (M : E →L[ℂ] E) (Y : E' →L[ℂ] V) (hH : IsSelfAdjoint H)
    (hM : M.IsPositive) (hnc : (B†).range ≤ M.range) {T : ℝ}
    (hT : 0 < T) :
    (Y†) ∘L ((horW H B M T).ker).starProjection ∘L Y = dynRdyn H B Y ∧
    (Y†) ∘L ((horWhat H B T).ker).starProjection ∘L Y
      = dynRdyn H B Y := by
  obtain ⟨-, -, hk1, hk2⟩ :=
    source_metric_horizon_support H B M hH hM hnc hT
  constructor
  · rw [starProjection_congr hk1, Submodule.starProjection_orthogonal']
    rfl
  · rw [starProjection_congr hk2, Submodule.starProjection_orthogonal']
    rfl

/-! ### Record 9 toolkit: rectangular integral transport and shifted inverses

The Tikhonov clauses (SMET.16–SMET.19) need three further layers: fixed
rectangular factors and adjoints passing through operator-valued interval
integrals, the `Ring.inverse` calculus of the shifted horizon `W + εI`
(self-adjointness, positivity, Loewner anti-monotonicity by the
Cauchy–Schwarz trick), and the finite spectral resolution of the horizon
Gramian. -/

/-- A fixed right rectangular factor passes out of an operator-valued
interval integral. -/
theorem intervalIntegral_comp_const {G₁ G₂ G₄ : Type*}
    [NormedAddCommGroup G₁] [NormedSpace ℂ G₁]
    [NormedAddCommGroup G₂] [NormedSpace ℂ G₂] [CompleteSpace G₂]
    [NormedAddCommGroup G₄] [NormedSpace ℂ G₄]
    {f : ℝ → G₁ →L[ℂ] G₂} {a b : ℝ}
    (hf : IntervalIntegrable f MeasureTheory.volume a b)
    (C : G₄ →L[ℂ] G₁) :
    (∫ t in a..b, f t) ∘L C = ∫ t in a..b, f t ∘L C := by
  have h := ((ContinuousLinearMap.compL ℂ G₄ G₁ G₂).flip
    C).intervalIntegral_comp_comm hf
  calc (∫ t in a..b, f t) ∘L C
      = ((ContinuousLinearMap.compL ℂ G₄ G₁ G₂).flip C)
          (∫ t in a..b, f t) := rfl
    _ = ∫ t in a..b, ((ContinuousLinearMap.compL ℂ G₄ G₁ G₂).flip C)
          (f t) := h.symm
    _ = ∫ t in a..b, f t ∘L C :=
        intervalIntegral.integral_congr fun t _ => rfl

/-- Fixed rectangular factors pass out of operator-valued interval
integrals on both sides. -/
theorem compress_intervalIntegral_rect {G₁ G₂ G₃ G₄ : Type*}
    [NormedAddCommGroup G₁] [NormedSpace ℂ G₁]
    [NormedAddCommGroup G₂] [NormedSpace ℂ G₂] [CompleteSpace G₂]
    [NormedAddCommGroup G₃] [NormedSpace ℂ G₃] [CompleteSpace G₃]
    [NormedAddCommGroup G₄] [NormedSpace ℂ G₄]
    (A : G₂ →L[ℂ] G₃) (C : G₄ →L[ℂ] G₁) {f : ℝ → G₁ →L[ℂ] G₂} {a b : ℝ}
    (hf : IntervalIntegrable f MeasureTheory.volume a b) :
    A ∘L (∫ t in a..b, f t) ∘L C = ∫ t in a..b, A ∘L f t ∘L C := by
  have h := (((ContinuousLinearMap.compL ℂ G₄ G₂ G₃) A).comp
    ((ContinuousLinearMap.compL ℂ G₄ G₁ G₂).flip C)).intervalIntegral_comp_comm hf
  calc A ∘L (∫ t in a..b, f t) ∘L C
      = (((ContinuousLinearMap.compL ℂ G₄ G₂ G₃) A).comp
          ((ContinuousLinearMap.compL ℂ G₄ G₁ G₂).flip C))
          (∫ t in a..b, f t) := rfl
    _ = ∫ t in a..b, (((ContinuousLinearMap.compL ℂ G₄ G₂ G₃) A).comp
          ((ContinuousLinearMap.compL ℂ G₄ G₁ G₂).flip C)) (f t) := h.symm
    _ = ∫ t in a..b, A ∘L f t ∘L C :=
        intervalIntegral.integral_congr fun t _ => rfl

/-- The rectangular adjoint as a real-linear isometry of operator
spaces. -/
noncomputable def adjointRealIsometryRect (G₁ G₂ : Type*)
    [NormedAddCommGroup G₁] [InnerProductSpace ℂ G₁]
    [FiniteDimensional ℂ G₁] [NormedAddCommGroup G₂]
    [InnerProductSpace ℂ G₂] [FiniteDimensional ℂ G₂] :
    (G₁ →L[ℂ] G₂) →ₗᵢ[ℝ] (G₂ →L[ℂ] G₁) where
  toLinearMap :=
    { toFun := fun A => A†
      map_add' := fun A B => map_add ContinuousLinearMap.adjoint A B
      map_smul' := fun c A => by
        rw [RingHom.id_apply]
        have h1 : c • A = ((c : ℝ) : ℂ) • A := by
          rw [← smul_one_smul ℂ c A, Complex.real_smul, mul_one]
        have h2 : c • (A†) = ((c : ℝ) : ℂ) • (A†) := by
          rw [← smul_one_smul ℂ c (A†), Complex.real_smul, mul_one]
        rw [h1, h2, map_smulₛₗ ContinuousLinearMap.adjoint]
        congr 1
        exact Complex.conj_ofReal c }
  norm_map' := fun A => ContinuousLinearMap.adjoint.norm_map A

/-- Rectangular pointwise adjoints pass through operator-valued interval
integrals. -/
theorem intervalIntegral_adjoint_rect {G₁ G₂ : Type*}
    [NormedAddCommGroup G₁] [InnerProductSpace ℂ G₁]
    [FiniteDimensional ℂ G₁] [NormedAddCommGroup G₂]
    [InnerProductSpace ℂ G₂] [FiniteDimensional ℂ G₂]
    (f : ℝ → G₁ →L[ℂ] G₂) (a b : ℝ) :
    (∫ t in a..b, (f t)†) = (∫ t in a..b, f t)† := by
  have h := (adjointRealIsometryRect G₁ G₂).intervalIntegral_comp_comm
    (a := a) (b := b) (μ := MeasureTheory.volume) f
  calc (∫ t in a..b, (f t)†)
      = ∫ t in a..b, adjointRealIsometryRect G₁ G₂ (f t) :=
        intervalIntegral.integral_congr fun t _ => rfl
    _ = adjointRealIsometryRect G₁ G₂ (∫ t in a..b, f t) := h
    _ = (∫ t in a..b, f t)† := rfl

omit [FiniteDimensional ℂ G] in
/-- Composition form of `Ring.mul_inverse_cancel`. -/
theorem comp_ringInverse [CompleteSpace G] {A : G →L[ℂ] G}
    (hU : IsUnit A) : A ∘L Ring.inverse A = 1 := by
  have h := Ring.mul_inverse_cancel A hU
  rwa [ContinuousLinearMap.mul_def] at h

omit [FiniteDimensional ℂ G] in
/-- Composition form of `Ring.inverse_mul_cancel`. -/
theorem ringInverse_comp [CompleteSpace G] {A : G →L[ℂ] G}
    (hU : IsUnit A) : Ring.inverse A ∘L A = 1 := by
  have h := Ring.inverse_mul_cancel A hU
  rwa [ContinuousLinearMap.mul_def] at h

/-- The `Ring.inverse` of a self-adjoint unit is self-adjoint. -/
theorem ringInverse_isSelfAdjoint {A : G →L[ℂ] G} (hA : IsSelfAdjoint A)
    (hU : IsUnit A) : IsSelfAdjoint (Ring.inverse A) := by
  have h1 : (Ring.inverse A)† ∘L A = 1 := by
    have h2 := congrArg (fun X : G →L[ℂ] G => X†) (comp_ringInverse hU)
    simp only [ContinuousLinearMap.adjoint_comp] at h2
    rw [hA.adjoint_eq] at h2
    rwa [ContinuousLinearMap.adjoint_one] at h2
  rw [isSelfAdjoint_iff']
  calc (Ring.inverse A)†
      = (Ring.inverse A)† ∘L (A ∘L Ring.inverse A) := by
        rw [comp_ringInverse hU, ContinuousLinearMap.one_def,
          ContinuousLinearMap.comp_id]
    _ = ((Ring.inverse A)† ∘L A) ∘L Ring.inverse A := by
        rw [ContinuousLinearMap.comp_assoc]
    _ = Ring.inverse A := by
        rw [h1, ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp]

/-- The `Ring.inverse` of a positive unit is positive. -/
theorem ringInverse_isPositive {A : G →L[ℂ] G} (hA : A.IsPositive)
    (hU : IsUnit A) : (Ring.inverse A).IsPositive := by
  refine ContinuousLinearMap.isPositive_def'.mpr
    ⟨ringInverse_isSelfAdjoint hA.isSelfAdjoint hU, fun x => ?_⟩
  have hx : A (Ring.inverse A x) = x := by
    have h := comp_ringInverse hU
    calc A (Ring.inverse A x) = (A ∘L Ring.inverse A) x := rfl
      _ = x := by rw [h]; rfl
  have h4 : ContinuousLinearMap.reApplyInnerSelf (Ring.inverse A) x
      = ((⟪Ring.inverse A x, x⟫ : ℂ)).re := by
    unfold ContinuousLinearMap.reApplyInnerSelf
    rw [RCLike.re_to_complex]
  have h5 : (⟪Ring.inverse A x, x⟫ : ℂ)
      = ⟪Ring.inverse A x, A (Ring.inverse A x)⟫ :=
    congrArg (fun w => (⟪Ring.inverse A x, w⟫ : ℂ)) hx.symm
  have h6 := hA.2 (Ring.inverse A x)
  have h7 : ContinuousLinearMap.reApplyInnerSelf A (Ring.inverse A x)
      = ((⟪A (Ring.inverse A x), Ring.inverse A x⟫ : ℂ)).re := by
    unfold ContinuousLinearMap.reApplyInnerSelf
    rw [RCLike.re_to_complex]
  rw [h7] at h6
  rw [h4, h5, ← inner_conj_symm, Complex.conj_re]
  exact h6

/-- Loewner inversion: `A ⪯ C` with both positive units forces
`C⁻¹ ⪯ A⁻¹` (Cauchy–Schwarz through the `A`-form). -/
theorem ringInverse_antitone {A C : G →L[ℂ] G} (hA : A.IsPositive)
    (hC : C.IsPositive) (hUA : IsUnit A) (hUC : IsUnit C)
    (hle : (C - A).IsPositive) :
    (Ring.inverse A - Ring.inverse C).IsPositive := by
  have hRA := ringInverse_isPositive hA hUA
  have hRC := ringInverse_isPositive hC hUC
  refine ContinuousLinearMap.isPositive_def'.mpr
    ⟨hRA.isSelfAdjoint.sub hRC.isSelfAdjoint, fun x => ?_⟩
  set u := Ring.inverse C x with hu
  set w := Ring.inverse A x with hw
  have hxC : C u = x := by
    have h := comp_ringInverse hUC
    calc C u = (C ∘L Ring.inverse C) x := rfl
      _ = x := by rw [h]; rfl
  have hxA : A w = x := by
    have h := comp_ringInverse hUA
    calc A w = (A ∘L Ring.inverse A) x := rfl
      _ = x := by rw [h]; rfl
  -- the three re-pairings
  have hL0 : 0 ≤ (⟪u, x⟫ : ℂ).re := by
    have h := hRC.2 x
    have h7 : ContinuousLinearMap.reApplyInnerSelf (Ring.inverse C) x
        = ((⟪u, x⟫ : ℂ)).re := by
      unfold ContinuousLinearMap.reApplyInnerSelf
      rw [RCLike.re_to_complex]
    rwa [h7] at h
  have hR0 : 0 ≤ (⟪w, x⟫ : ℂ).re := by
    have h := hRA.2 x
    have h7 : ContinuousLinearMap.reApplyInnerSelf (Ring.inverse A) x
        = ((⟪w, x⟫ : ℂ)).re := by
      unfold ContinuousLinearMap.reApplyInnerSelf
      rw [RCLike.re_to_complex]
    rwa [h7] at h
  -- Cauchy–Schwarz for the A-form at (w, u)
  have hCS := isPositive_re_inner_sq_le hA w u
  have hAwu : ((⟪A w, u⟫ : ℂ)).re = (⟪u, x⟫ : ℂ).re := by
    rw [hxA, ← inner_conj_symm, Complex.conj_re]
  have hAww : ((⟪A w, w⟫ : ℂ)).re = (⟪w, x⟫ : ℂ).re := by
    rw [hxA, ← inner_conj_symm, Complex.conj_re]
  -- A ⪯ C on the diagonal at u
  have hAuu_le : ((⟪A u, u⟫ : ℂ)).re ≤ (⟪u, x⟫ : ℂ).re := by
    have h := hle.2 u
    have h7 : ContinuousLinearMap.reApplyInnerSelf (C - A) u
        = ((⟪(C - A) u, u⟫ : ℂ)).re := by
      unfold ContinuousLinearMap.reApplyInnerSelf
      rw [RCLike.re_to_complex]
    rw [h7] at h
    have h8 : (C - A) u = C u - A u := by
      rw [_root_.sub_apply]
    rw [h8, inner_sub_left, hxC] at h
    have h9 : ((⟪x, u⟫ : ℂ)).re = (⟪u, x⟫ : ℂ).re := by
      rw [← inner_conj_symm, Complex.conj_re]
    simp only [Complex.sub_re] at h
    linarith [h, h9]
  have hAuu0 : 0 ≤ ((⟪A u, u⟫ : ℂ)).re := by
    have h := hA.2 u
    have h7 : ContinuousLinearMap.reApplyInnerSelf A u
        = ((⟪A u, u⟫ : ℂ)).re := by
      unfold ContinuousLinearMap.reApplyInnerSelf
      rw [RCLike.re_to_complex]
    rwa [h7] at h
  -- assemble: L² ≤ R·L with L,R ≥ 0 gives L ≤ R
  have hkey : (⟪u, x⟫ : ℂ).re ^ 2
      ≤ (⟪w, x⟫ : ℂ).re * (⟪u, x⟫ : ℂ).re := by
    calc (⟪u, x⟫ : ℂ).re ^ 2 = ((⟪A w, u⟫ : ℂ)).re ^ 2 := by rw [hAwu]
      _ ≤ ((⟪A w, w⟫ : ℂ)).re * ((⟪A u, u⟫ : ℂ)).re := hCS
      _ ≤ (⟪w, x⟫ : ℂ).re * (⟪u, x⟫ : ℂ).re := by
          rw [hAww]
          exact mul_le_mul_of_nonneg_left hAuu_le hR0
  have hLR : (⟪u, x⟫ : ℂ).re ≤ (⟪w, x⟫ : ℂ).re := by
    rcases eq_or_lt_of_le hL0 with h0 | h0
    · rw [← h0]; exact hR0
    · nlinarith [hkey]
  -- conclude
  have h7 : ContinuousLinearMap.reApplyInnerSelf
      (Ring.inverse A - Ring.inverse C) x
      = ((⟪(Ring.inverse A - Ring.inverse C) x, x⟫ : ℂ)).re := by
    unfold ContinuousLinearMap.reApplyInnerSelf
    rw [RCLike.re_to_complex]
  rw [h7]
  have h8 : (Ring.inverse A - Ring.inverse C) x = w - u := by
    rw [_root_.sub_apply]
  rw [h8, inner_sub_left]
  simp only [Complex.sub_re]
  linarith [hLR]

omit [FiniteDimensional ℂ G] in
/-- A nonzero scalar multiple of a unit is a unit, with the matching
inverse witness. -/
theorem smul_unit_mul_smul_ringInverse [CompleteSpace G] {c : ℂ}
    (hc : c ≠ 0) {D : G →L[ℂ] G} (hU : IsUnit D) :
    (c • D) * (c⁻¹ • Ring.inverse D) = 1
    ∧ (c⁻¹ • Ring.inverse D) * (c • D) = 1 := by
  constructor
  · rw [smul_mul_assoc, mul_smul_comm, smul_smul, mul_inv_cancel₀ hc,
      Ring.mul_inverse_cancel D hU, one_smul]
  · rw [smul_mul_assoc, mul_smul_comm, smul_smul, inv_mul_cancel₀ hc,
      Ring.inverse_mul_cancel D hU, one_smul]

omit [FiniteDimensional ℂ G] in
/-- A nonzero scalar multiple of a unit is a unit. -/
theorem isUnit_smul_unit [CompleteSpace G] {c : ℂ} (hc : c ≠ 0)
    {D : G →L[ℂ] G} (hU : IsUnit D) : IsUnit (c • D) :=
  ⟨⟨c • D, c⁻¹ • Ring.inverse D,
    (smul_unit_mul_smul_ringInverse hc hU).1,
    (smul_unit_mul_smul_ringInverse hc hU).2⟩, rfl⟩

omit [FiniteDimensional ℂ G] in
/-- `Ring.inverse` scales inversely under nonzero scalars. -/
theorem ringInverse_smul [CompleteSpace G] {c : ℂ} (hc : c ≠ 0)
    {D : G →L[ℂ] G} (hU : IsUnit D) :
    Ring.inverse (c • D) = c⁻¹ • Ring.inverse D := by
  have hcU := isUnit_smul_unit hc hU
  have h1 : Ring.inverse (c • D) * (c • D) = 1 :=
    Ring.inverse_mul_cancel _ hcU
  calc Ring.inverse (c • D)
      = Ring.inverse (c • D) * ((c • D) * (c⁻¹ • Ring.inverse D)) := by
        rw [(smul_unit_mul_smul_ringInverse hc hU).1, mul_one]
    _ = (Ring.inverse (c • D) * (c • D)) * (c⁻¹ • Ring.inverse D) := by
        rw [mul_assoc]
    _ = c⁻¹ • Ring.inverse D := by rw [h1, one_mul]

/-! ### Record 9: finite spectral resolution of the horizon Gramian -/

/-- Finite spectral resolution of a positive operator: an orthonormal
eigenbasis with nonnegative eigenvalues. -/
theorem isPositive_spectral_resolution {W : V →L[ℂ] V}
    (hW : W.IsPositive) :
    ∃ (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ V) (μ : Fin n → ℝ),
      (∀ i, 0 ≤ μ i) ∧ ∀ i, W (b i) = ((μ i : ℝ) : ℂ) • b i := by
  have hsym : (W : V →ₗ[ℂ] V).IsSymmetric := hW.isSymmetric
  refine ⟨Module.finrank ℂ V, hsym.eigenvectorBasis rfl,
    hsym.eigenvalues rfl, fun i => ?_, fun i => ?_⟩
  · have heig := hsym.apply_eigenvectorBasis rfl i
    have hpos := hW.2 (hsym.eigenvectorBasis rfl i)
    have h7 : ContinuousLinearMap.reApplyInnerSelf W
        (hsym.eigenvectorBasis rfl i)
        = ((⟪W (hsym.eigenvectorBasis rfl i),
            hsym.eigenvectorBasis rfl i⟫ : ℂ)).re := by
      unfold ContinuousLinearMap.reApplyInnerSelf
      rw [RCLike.re_to_complex]
    rw [h7] at hpos
    have h8 : W (hsym.eigenvectorBasis rfl i)
        = ((hsym.eigenvalues rfl i : ℝ) : ℂ) • hsym.eigenvectorBasis rfl i :=
      heig
    rw [h8, inner_smul_left, Complex.conj_ofReal] at hpos
    have h9 : (⟪hsym.eigenvectorBasis rfl i,
        hsym.eigenvectorBasis rfl i⟫ : ℂ) = 1 := by
      have hnorm : ‖hsym.eigenvectorBasis rfl i‖ = 1 :=
        (hsym.eigenvectorBasis rfl).orthonormal.1 i
      rw [inner_self_eq_norm_sq_to_K, hnorm]
      norm_num
    rw [h9, mul_one, Complex.ofReal_re] at hpos
    exact hpos
  · exact hsym.apply_eigenvectorBasis rfl i

omit [FiniteDimensional ℂ V] in
/-- The span projection of a unit vector is the rank-one atom
`x ↦ ⟪b, x⟫ b`. -/
theorem starProjection_unit_singleton {v : V} (hv : ‖v‖ = 1) (w : V) :
    (ℂ ∙ v).starProjection w = (⟪v, w⟫ : ℂ) • v := by
  rw [Submodule.starProjection_singleton, hv]
  norm_num

/-- **(SMET.17, spectral inverse)** On an eigenresolution
`W b_i = μ_i b_i` of a self-adjoint `W`, the shift `W + ε` is a unit and
`ε (W + ε)⁻¹ = ∑_i (ε/(μ_i + ε)) P_{b_i}`. -/
theorem shift_ringInverse_spectral {W : V →L[ℂ] V}
    (hWsa : IsSelfAdjoint W) {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ V)
    (μ : Fin n → ℝ) (heig : ∀ i, W (b i) = ((μ i : ℝ) : ℂ) • b i)
    {ε : ℝ} (hμε : ∀ i, μ i + ε ≠ 0) :
    IsUnit (W + ((ε : ℝ) : ℂ) • 1)
    ∧ ((ε : ℝ) : ℂ) • Ring.inverse (W + ((ε : ℝ) : ℂ) • 1)
      = ∑ i, (((ε / (μ i + ε) : ℝ)) : ℂ) • (ℂ ∙ (b i)).starProjection := by
  set A : V →L[ℂ] V := W + ((ε : ℝ) : ℂ) • 1 with hAdef
  set S : V →L[ℂ] V :=
    ∑ i, ((((μ i + ε)⁻¹ : ℝ)) : ℂ) • (ℂ ∙ (b i)).starProjection with hSdef
  have hunit : ∀ i, ‖b i‖ = 1 := fun i => b.orthonormal.1 i
  have hAb : ∀ i, A (b i) = (((μ i + ε : ℝ)) : ℂ) • b i := by
    intro i
    have h1 : A (b i) = W (b i) + ((ε : ℝ) : ℂ) • b i := by
      rw [hAdef]
      rw [_root_.add_apply, _root_.smul_apply, one_apply_eq_self]
    rw [h1, heig i, ← add_smul, ← Complex.ofReal_add]
  have hSapply : ∀ x : V, S x
      = ∑ i, ((((μ i + ε)⁻¹ : ℝ)) : ℂ) • ((⟪b i, x⟫ : ℂ) • b i) := by
    intro x
    rw [hSdef, _root_.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [_root_.smul_apply, starProjection_unit_singleton (hunit i)]
  have hAS : ∀ x : V, A (S x) = x := by
    intro x
    rw [hSapply, map_sum]
    have hterm : ∀ i : Fin n,
        A (((((μ i + ε)⁻¹ : ℝ)) : ℂ) • ((⟪b i, x⟫ : ℂ) • b i))
          = (⟪b i, x⟫ : ℂ) • b i := by
      intro i
      rw [map_smul, map_smul, hAb i, smul_comm ((⟪b i, x⟫ : ℂ)),
        smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ (hμε i),
        Complex.ofReal_one, one_smul]
    rw [Finset.sum_congr rfl fun i _ => hterm i]
    exact b.sum_repr' x
  have hSA : ∀ x : V, S (A x) = x := by
    intro x
    rw [hSapply]
    have hinner : ∀ i : Fin n,
        (⟪b i, A x⟫ : ℂ) = (((μ i + ε : ℝ)) : ℂ) * ⟪b i, x⟫ := by
      intro i
      have h1 : (⟪b i, A x⟫ : ℂ) = ⟪A (b i), x⟫ := by
        have hAsa : IsSelfAdjoint A := by
          rw [hAdef]
          refine hWsa.add ?_
          rw [IsSelfAdjoint, star_smul, star_one, Complex.star_def,
            Complex.conj_ofReal]
        calc (⟪b i, A x⟫ : ℂ) = ⟪(A†) (b i), x⟫ := by
              rw [ContinuousLinearMap.adjoint_inner_left]
          _ = ⟪A (b i), x⟫ := by rw [hAsa.adjoint_eq]
      rw [h1, hAb i, inner_smul_left, Complex.conj_ofReal]
    have hterm : ∀ i : Fin n,
        ((((μ i + ε)⁻¹ : ℝ)) : ℂ) • ((⟪b i, A x⟫ : ℂ) • b i)
          = (⟪b i, x⟫ : ℂ) • b i := by
      intro i
      rw [hinner i, smul_smul, ← mul_assoc, ← Complex.ofReal_mul,
        inv_mul_cancel₀ (hμε i), Complex.ofReal_one, one_mul]
    rw [Finset.sum_congr rfl fun i _ => hterm i]
    exact b.sum_repr' x
  have hASc : A * S = 1 := by
    ext x
    change A (S x) = x
    exact hAS x
  have hSAc : S * A = 1 := by
    ext x
    change S (A x) = x
    exact hSA x
  have hU : IsUnit A := ⟨⟨A, S, hASc, hSAc⟩, rfl⟩
  refine ⟨hU, ?_⟩
  have hRS : Ring.inverse A = S := by
    have h3 : Ring.inverse A * A = 1 := Ring.inverse_mul_cancel A hU
    calc Ring.inverse A = Ring.inverse A * (A * S) := by rw [hASc, mul_one]
      _ = (Ring.inverse A * A) * S := by rw [mul_assoc]
      _ = S := by rw [h3, one_mul]
  rw [hRS, hSdef, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul, ← Complex.ofReal_mul, ← div_eq_mul_inv]

/-- On a self-adjoint operator with eigenresolution, the kernel
projection is the sum of the zero-mode atoms. -/
theorem ker_starProjection_spectral {W : V →L[ℂ] V}
    (hWsa : IsSelfAdjoint W) {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ V)
    (μ : Fin n → ℝ) (heig : ∀ i, W (b i) = ((μ i : ℝ) : ℂ) • b i) :
    (W.ker).starProjection
      = ∑ i ∈ Finset.univ.filter (fun i => μ i = 0),
          (ℂ ∙ (b i)).starProjection := by
  have hunit : ∀ i, ‖b i‖ = 1 := fun i => b.orthonormal.1 i
  ext x
  have hRHS : (∑ i ∈ Finset.univ.filter (fun i => μ i = 0),
      (ℂ ∙ (b i)).starProjection) x
      = ∑ i ∈ Finset.univ.filter (fun i => μ i = 0),
          (⟪b i, x⟫ : ℂ) • b i := by
    rw [_root_.sum_apply]
    exact Finset.sum_congr rfl fun i _ =>
      starProjection_unit_singleton (hunit i) x
  rw [hRHS]
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · -- membership in the kernel
    rw [LinearMap.mem_ker]
    have h1 : W (∑ i ∈ Finset.univ.filter (fun i => μ i = 0),
        (⟪b i, x⟫ : ℂ) • b i)
        = ∑ i ∈ Finset.univ.filter (fun i => μ i = 0),
            (⟪b i, x⟫ : ℂ) • W (b i) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_smul]
    have h2 : ∀ i ∈ Finset.univ.filter (fun i => μ i = 0),
        (⟪b i, x⟫ : ℂ) • W (b i) = 0 := by
      intro i hi
      have hμi : μ i = 0 := (Finset.mem_filter.mp hi).2
      rw [heig i, hμi, Complex.ofReal_zero, zero_smul, smul_zero]
    have h3 : W (∑ i ∈ Finset.univ.filter (fun i => μ i = 0),
        (⟪b i, x⟫ : ℂ) • b i) = 0 := by
      rw [h1, Finset.sum_eq_zero h2]
    exact h3
  · -- orthogonality to the kernel
    intro w hw
    have hWw : W w = 0 := LinearMap.mem_ker.mp hw
    have hbw : ∀ i : Fin n, μ i ≠ 0 → (⟪b i, w⟫ : ℂ) = 0 := by
      intro i hne
      have h1 : (⟪W (b i), w⟫ : ℂ) = 0 := by
        calc (⟪W (b i), w⟫ : ℂ) = ⟪b i, (W†) w⟫ := by
              rw [ContinuousLinearMap.adjoint_inner_right]
          _ = ⟪b i, W w⟫ := by rw [hWsa.adjoint_eq]
          _ = 0 := by rw [hWw, inner_zero_right]
      rw [heig i, inner_smul_left, Complex.conj_ofReal] at h1
      rcases mul_eq_zero.mp h1 with h2 | h2
      · exact absurd (Complex.ofReal_eq_zero.mp h2) hne
      · exact h2
    have hx : x = (∑ i ∈ Finset.univ.filter (fun i => μ i = 0),
          (⟪b i, x⟫ : ℂ) • b i)
        + ∑ i ∈ Finset.univ.filter (fun i => ¬ μ i = 0),
            (⟪b i, x⟫ : ℂ) • b i := by
      rw [Finset.sum_filter_add_sum_filter_not Finset.univ
        (fun i => μ i = 0) (fun i => (⟪b i, x⟫ : ℂ) • b i)]
      exact (b.sum_repr' x).symm
    have hsplit : x - ∑ i ∈ Finset.univ.filter (fun i => μ i = 0),
        (⟪b i, x⟫ : ℂ) • b i
        = ∑ i ∈ Finset.univ.filter (fun i => ¬ μ i = 0),
            (⟪b i, x⟫ : ℂ) • b i :=
      sub_eq_of_eq_add' hx
    rw [hsplit, sum_inner]
    refine Finset.sum_eq_zero fun i hi => ?_
    have hne : ¬ μ i = 0 := (Finset.mem_filter.mp hi).2
    rw [inner_smul_left, hbw i hne, mul_zero]

/-- The `ε`-shift of a positive operator is a unit for every `ε > 0`. -/
theorem shift_isUnit {W : V →L[ℂ] V} (hW : W.IsPositive) {ε : ℝ}
    (hε : 0 < ε) : IsUnit (W + ((ε : ℝ) : ℂ) • 1) := by
  obtain ⟨n, b, μ, hμ, heig⟩ := isPositive_spectral_resolution hW
  exact (shift_ringInverse_spectral hW.isSelfAdjoint b μ heig
    (fun i => ne_of_gt (add_pos_of_nonneg_of_pos (hμ i) hε))).1

omit [FiniteDimensional ℂ V] in
/-- The `ε`-shift of a positive operator is positive. -/
theorem shift_isPositive {W : V →L[ℂ] V} (hW : W.IsPositive) {ε : ℝ}
    (hε : 0 ≤ ε) : (W + ((ε : ℝ) : ℂ) • 1).IsPositive :=
  hW.add (ContinuousLinearMap.isPositive_one.smul_of_nonneg
    (Complex.zero_le_real.mpr hε))

/-! ### Record 9: the Tikhonov compiler (SMET.16–SMET.17) -/

/-- **(SMET.16, source action)** The synthesized source action
`∫₀ᵀ e^{-tH} B u(t) dt` of an operator-valued control. -/
noncomputable def ctrlSyn (H : V →L[ℂ] V) (B : E →L[ℂ] V) (T : ℝ)
    (u : ℝ → (E' →L[ℂ] E)) : E' →L[ℂ] V :=
  ∫ t in (0:ℝ)..T, (expH H t ∘L B) ∘L u t

/-- **(SMET.16)** The operator-valued Tikhonov source functional
`𝒥_{T,ε}^M(u) = (Y - ∫₀ᵀ e^{-tH}Bu)^*(Y - ∫₀ᵀ e^{-tH}Bu)
+ ε ∫₀ᵀ u^* M u`. -/
noncomputable def tikCost (H : V →L[ℂ] V) (B : E →L[ℂ] V)
    (M : E →L[ℂ] E) (T ε : ℝ) (Y : E' →L[ℂ] V)
    (u : ℝ → (E' →L[ℂ] E)) : E' →L[ℂ] E' :=
  ((Y - ctrlSyn H B T u)†) ∘L (Y - ctrlSyn H B T u)
    + ((ε : ℝ) : ℂ) • ∫ t in (0:ℝ)..T, ((u t)†) ∘L M ∘L u t

/-- The Tikhonov residual `R_{T,ε} = ε Y^*(W + ε)⁻¹ Y` (`Ring.inverse`
carries a junk value on non-units; the shift is a unit whenever `W ⪰ 0`
and `ε > 0`, by `shift_isUnit`). -/
noncomputable def tikRes (W : V →L[ℂ] V) (ε : ℝ) (Y : E' →L[ℂ] V) :
    E' →L[ℂ] E' :=
  (Y†) ∘L (((ε : ℝ) : ℂ) • Ring.inverse (W + ((ε : ℝ) : ℂ) • 1)) ∘L Y

/-- Compressed operator sums distribute over finite sums. -/
theorem compress_finset_sum {ι : Type*} (Y : E' →L[ℂ] V) (s : Finset ι)
    (f : ι → V →L[ℂ] V) :
    (Y†) ∘L (∑ i ∈ s, f i) ∘L Y = ∑ i ∈ s, (Y†) ∘L f i ∘L Y := by
  induction s using Finset.cons_induction with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, ContinuousLinearMap.zero_comp,
      ContinuousLinearMap.comp_zero]
  | cons a s ha ih =>
    rw [Finset.sum_cons, Finset.sum_cons, compress_add, ih]

/-- Compressions commute with scalar multiples. -/
theorem compress_smul (Y : E' →L[ℂ] V) (c : ℂ) (A : V →L[ℂ] V) :
    (Y†) ∘L (c • A) ∘L Y = c • ((Y†) ∘L A ∘L Y) := by
  rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]

omit [FiniteDimensional ℂ E'] in
/-- Finite sums of positive operators are positive. -/
theorem isPositive_finset_sum {ι : Type*} (s : Finset ι)
    (f : ι → E' →L[ℂ] E') (hf : ∀ i ∈ s, (f i).IsPositive) :
    (∑ i ∈ s, f i).IsPositive := by
  induction s using Finset.cons_induction with
  | empty =>
    rw [Finset.sum_empty]
    exact ContinuousLinearMap.isPositive_zero
  | cons a s ha ih =>
    rw [Finset.sum_cons]
    exact (hf a (Finset.mem_cons.mpr (Or.inl rfl))).add
      (ih fun i hi => hf i (Finset.mem_cons.mpr (Or.inr hi)))

/-- **(SMET.17)** The spectral form of the Tikhonov residual: the horizon
Gramian `𝒲_{T;B,M}` has a finite spectral resolution `(b, μ)` with
`μ ⪰ 0`, and for every `ε > 0` the Tikhonov residual is the invariant
zero atom plus the strictly positive spectral atoms weighted by
`ε/(λ+ε)`:
`R_{T,ε}^M = R_dyn + ∑_{μ_i>0} (ε/(μ_i+ε)) · Y^*P_{b_i}Y`
(the finite rendering of
`R_{T,ε}^M = R_dyn + ∫_{(0,∞)} ε/(λ+ε) Λ_T^{Y,M}(dλ)`). -/
theorem source_metric_horizon_tikhonov_spectral (H : V →L[ℂ] V)
    (B : E →L[ℂ] V) (M : E →L[ℂ] E) (Y : E' →L[ℂ] V)
    (hH : IsSelfAdjoint H) (hM : M.IsPositive)
    (hnc : ((B†)).range ≤ M.range) {T : ℝ} (hT : 0 < T) :
    ∃ (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ V) (μ : Fin n → ℝ),
      (∀ i, 0 ≤ μ i)
      ∧ (∀ i, horW H B M T (b i) = ((μ i : ℝ) : ℂ) • b i)
      ∧ ∀ ε : ℝ, 0 < ε →
          tikRes (horW H B M T) ε Y
            = dynRdyn H B Y
              + ∑ i ∈ Finset.univ.filter (fun i => 0 < μ i),
                  (((ε / (μ i + ε) : ℝ)) : ℂ)
                    • ((Y†) ∘L (ℂ ∙ (b i)).starProjection ∘L Y) := by
  have hWpos : (horW H B M T).IsPositive :=
    gramW_isPositive (sigmaBM_isPositive hM hnc) hT.le
  obtain ⟨n, b, μ, hμ, heig⟩ := isPositive_spectral_resolution hWpos
  refine ⟨n, b, μ, hμ, heig, fun ε hε => ?_⟩
  have hne : ∀ i, μ i + ε ≠ 0 := fun i =>
    ne_of_gt (add_pos_of_nonneg_of_pos (hμ i) hε)
  have hspec := (shift_ringInverse_spectral hWpos.isSelfAdjoint b μ heig
    hne).2
  have hcomp : tikRes (horW H B M T) ε Y
      = ∑ i, (((ε / (μ i + ε) : ℝ)) : ℂ)
          • ((Y†) ∘L (ℂ ∙ (b i)).starProjection ∘L Y) := by
    calc tikRes (horW H B M T) ε Y
        = (Y†) ∘L (((ε : ℝ) : ℂ)
            • Ring.inverse (horW H B M T + ((ε : ℝ) : ℂ) • 1)) ∘L Y := rfl
      _ = (Y†) ∘L (∑ i, (((ε / (μ i + ε) : ℝ)) : ℂ)
            • (ℂ ∙ (b i)).starProjection) ∘L Y := by rw [hspec]
      _ = ∑ i, (Y†) ∘L ((((ε / (μ i + ε) : ℝ)) : ℂ)
            • (ℂ ∙ (b i)).starProjection) ∘L Y :=
          compress_finset_sum Y Finset.univ _
      _ = ∑ i, (((ε / (μ i + ε) : ℝ)) : ℂ)
            • ((Y†) ∘L (ℂ ∙ (b i)).starProjection ∘L Y) :=
          Finset.sum_congr rfl fun i _ => compress_smul Y _ _
  rw [hcomp,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => 0 < μ i)
      (fun i => (((ε / (μ i + ε) : ℝ)) : ℂ)
        • ((Y†) ∘L (ℂ ∙ (b i)).starProjection ∘L Y)),
    add_comm]
  congr 1
  -- the non-strict filter carries exactly the zero modes and sums to R_dyn
  have hz : ∀ i ∈ Finset.univ.filter (fun i => ¬ 0 < μ i),
      (((ε / (μ i + ε) : ℝ)) : ℂ)
          • ((Y†) ∘L (ℂ ∙ (b i)).starProjection ∘L Y)
        = (Y†) ∘L (ℂ ∙ (b i)).starProjection ∘L Y := by
    intro i hi
    have hμi : μ i = 0 :=
      le_antisymm (not_lt.mp (Finset.mem_filter.mp hi).2) (hμ i)
    rw [hμi, zero_add, div_self (ne_of_gt hε), Complex.ofReal_one, one_smul]
  rw [Finset.sum_congr rfl hz]
  have hfe : Finset.univ.filter (fun i => ¬ 0 < μ i)
      = Finset.univ.filter (fun i => μ i = 0) := by
    refine Finset.filter_congr fun i _ => ?_
    constructor
    · intro h
      exact le_antisymm (not_lt.mp h) (hμ i)
    · intro h
      rw [h]
      exact lt_irrefl 0
  rw [hfe, ← compress_finset_sum Y _ (fun i => (ℂ ∙ (b i)).starProjection),
    ← ker_starProjection_spectral hWpos.isSelfAdjoint b μ heig]
  exact (source_metric_horizon_zero_atom H B M Y hH hM hnc hT).1

/-- **(SMET.17, Loewner decrease)** The Tikhonov residual is
Loewner-antitone as `ε ↓ 0`. -/
theorem source_metric_horizon_tikhonov_antitone (H : V →L[ℂ] V)
    (B : E →L[ℂ] V) (M : E →L[ℂ] E) (Y : E' →L[ℂ] V)
    (hH : IsSelfAdjoint H) (hM : M.IsPositive)
    (hnc : ((B†)).range ≤ M.range) {T : ℝ} (hT : 0 < T) {ε₁ ε₂ : ℝ}
    (h1 : 0 < ε₁) (h12 : ε₁ ≤ ε₂) :
    (tikRes (horW H B M T) ε₂ Y - tikRes (horW H B M T) ε₁ Y).IsPositive
    := by
  obtain ⟨n, b, μ, hμ, -, hform⟩ :=
    source_metric_horizon_tikhonov_spectral H B M Y hH hM hnc hT
  have h2 : 0 < ε₂ := lt_of_lt_of_le h1 h12
  rw [hform ε₂ h2, hform ε₁ h1, add_sub_add_left_eq_sub,
    ← Finset.sum_sub_distrib]
  refine isPositive_finset_sum _ _ fun i hi => ?_
  have hμi : 0 < μ i := (Finset.mem_filter.mp hi).2
  rw [← sub_smul, ← Complex.ofReal_sub]
  refine ContinuousLinearMap.IsPositive.smul_of_nonneg
    (compressed_starProjection_isPositive _ Y) ?_
  rw [Complex.zero_le_real, sub_nonneg,
    div_le_div_iff₀ (add_pos hμi h1) (add_pos hμi h2)]
  nlinarith [hμi.le, h1.le]

/-- **(SMET.17, `ε ↓ 0` landing)** `R_{T,ε}^M → R_dyn` in operator norm
as `ε ↓ 0`: the finite positive leverage collapses onto the invariant
zero atom. -/
theorem source_metric_horizon_tikhonov_limit (H : V →L[ℂ] V)
    (B : E →L[ℂ] V) (M : E →L[ℂ] E) (Y : E' →L[ℂ] V)
    (hH : IsSelfAdjoint H) (hM : M.IsPositive)
    (hnc : ((B†)).range ≤ M.range) {T : ℝ} (hT : 0 < T) :
    Tendsto (fun ε : ℝ => tikRes (horW H B M T) ε Y) (𝓝[>] (0:ℝ))
      (𝓝 (dynRdyn H B Y)) := by
  obtain ⟨n, b, μ, hμ, -, hform⟩ :=
    source_metric_horizon_tikhonov_spectral H B M Y hH hM hnc hT
  have hev : (fun ε : ℝ => tikRes (horW H B M T) ε Y)
      =ᶠ[𝓝[>] (0:ℝ)]
      fun ε => dynRdyn H B Y
        + ∑ i ∈ Finset.univ.filter (fun i => 0 < μ i),
            (((ε / (μ i + ε) : ℝ)) : ℂ)
              • ((Y†) ∘L (ℂ ∙ (b i)).starProjection ∘L Y) :=
    Filter.eventuallyEq_of_mem self_mem_nhdsWithin fun ε hε =>
      hform ε hε
  refine Filter.Tendsto.congr' hev.symm ?_
  have hzero : Tendsto
      (fun ε : ℝ => ∑ i ∈ Finset.univ.filter (fun i => 0 < μ i),
        (((ε / (μ i + ε) : ℝ)) : ℂ)
          • ((Y†) ∘L (ℂ ∙ (b i)).starProjection ∘L Y))
      (𝓝[>] (0:ℝ))
      (𝓝 (∑ _i ∈ Finset.univ.filter (fun i => 0 < μ i),
        (0 : E' →L[ℂ] E'))) := by
    refine tendsto_finsetSum _ fun i hi => ?_
    have hμi : 0 < μ i := (Finset.mem_filter.mp hi).2
    have hden : Tendsto (fun ε : ℝ => μ i + ε) (𝓝 (0:ℝ))
        (𝓝 (μ i + 0)) := tendsto_const_nhds.add tendsto_id
    rw [add_zero] at hden
    have hdiv : Tendsto (fun ε : ℝ => ε / (μ i + ε)) (𝓝 (0:ℝ))
        (𝓝 (0 / μ i)) := Tendsto.div tendsto_id hden (ne_of_gt hμi)
    rw [zero_div] at hdiv
    have hcast : Tendsto (fun ε : ℝ => (((ε / (μ i + ε) : ℝ)) : ℂ))
        (𝓝 (0:ℝ)) (𝓝 ((0:ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto (0:ℝ)).comp hdiv
    rw [Complex.ofReal_zero] at hcast
    have hsmul := hcast.smul_const
      ((Y†) ∘L (ℂ ∙ (b i)).starProjection ∘L Y)
    rw [zero_smul] at hsmul
    exact hsmul.mono_left nhdsWithin_le_nhds
  rw [Finset.sum_const_zero] at hzero
  have hfin := (tendsto_const_nhds
    (x := dynRdyn H B Y) (f := 𝓝[>] (0:ℝ))).add hzero
  rwa [add_zero] at hfin

/-- Real scalars pass through rectangular adjoints. -/
theorem adjoint_real_smul_rect {G₁ G₂ : Type*} [NormedAddCommGroup G₁]
    [InnerProductSpace ℂ G₁] [FiniteDimensional ℂ G₁]
    [NormedAddCommGroup G₂] [InnerProductSpace ℂ G₂]
    [FiniteDimensional ℂ G₂] (c : ℝ) (A : G₁ →L[ℂ] G₂) :
    (((c : ℝ) : ℂ) • A)† = ((c : ℝ) : ℂ) • (A†) := by
  rw [map_smulₛₗ ContinuousLinearMap.adjoint]
  congr 1
  exact Complex.conj_ofReal c

omit [FiniteDimensional ℂ E] [FiniteDimensional ℂ E'] in
/-- Continuity of the delayed-writer control integrand. -/
theorem ctrl_integrand_continuous (H : V →L[ℂ] V) (B : E →L[ℂ] V)
    {u : ℝ → E' →L[ℂ] E} (hu : Continuous u) :
    Continuous fun t => (expH H t ∘L B) ∘L u t := by
  have h1 : Continuous fun t : ℝ => expH H t ∘L B :=
    isBoundedBilinearMap_comp.continuous.comp
      ((expH_continuous H).prodMk continuous_const)
  exact isBoundedBilinearMap_comp.continuous.comp (h1.prodMk hu)

/-- Continuity of the metric energy integrand. -/
theorem energy_integrand_continuous (M : E →L[ℂ] E)
    {u v : ℝ → E' →L[ℂ] E} (hu : Continuous u) (hv : Continuous v) :
    Continuous fun t => ((u t)†) ∘L M ∘L v t := by
  have h1 : Continuous fun t => (u t)† :=
    ContinuousLinearMap.adjoint.continuous.comp hu
  have h2 : Continuous fun t => M ∘L v t :=
    isBoundedBilinearMap_comp.continuous.comp (continuous_const.prodMk hv)
  exact isBoundedBilinearMap_comp.continuous.comp (h1.prodMk h2)

set_option maxHeartbeats 1000000 in
-- the completing-the-square algebra of the Tikhonov minimum forces heavy
-- operator-valued interval-integral unification; the default budget is
-- too small
/-- **`thm:GT-source-metric-horizon`** (SMET.16): the operator-valued
minimum of the Tikhonov source functional over continuous operator-valued
controls is the Tikhonov residual `R_{T,ε}^M = ε Y^*(𝒲_{T;B,M}+ε)⁻¹Y`:
every control pays at least `R_{T,ε}^M` in Loewner order, and the bound
is attained by an explicit continuous control with values in `(Ker M)ᗮ`
(so minimization descends to the quotient modulo `Ker M`-valued
controls, the finite rendering of "controls modulo `L²((0,T);Ker M)`"). -/
theorem source_metric_horizon_tikhonov_min (H : V →L[ℂ] V)
    (B : E →L[ℂ] V) (M : E →L[ℂ] E) (Y : E' →L[ℂ] V)
    (hH : IsSelfAdjoint H) (hM : M.IsPositive)
    (hnc : ((B†)).range ≤ M.range) {T ε : ℝ} (hT : 0 < T) (hε : 0 < ε) :
    (∀ u : ℝ → (E' →L[ℂ] E), Continuous u →
        (tikCost H B M T ε Y u - tikRes (horW H B M T) ε Y).IsPositive)
    ∧ ∃ u₀ : ℝ → (E' →L[ℂ] E), Continuous u₀
        ∧ (∀ t x, u₀ t x ∈ ((M.ker)ᗮ : Submodule ℂ E))
        ∧ tikCost H B M T ε Y u₀ = tikRes (horW H B M T) ε Y := by
  set W : V →L[ℂ] V := horW H B M T with hWdef
  have hWpos : W.IsPositive :=
    gramW_isPositive (sigmaBM_isPositive hM hnc) hT.le
  have hU : IsUnit (W + ((ε : ℝ) : ℂ) • 1) := shift_isUnit hWpos hε
  set R : V →L[ℂ] V := Ring.inverse (W + ((ε : ℝ) : ℂ) • 1) with hRdef
  have hAR : (W + ((ε : ℝ) : ℂ) • 1) ∘L R = 1 := comp_ringInverse hU
  have hAsa : IsSelfAdjoint (W + ((ε : ℝ) : ℂ) • 1) := by
    refine hWpos.isSelfAdjoint.add ?_
    rw [IsSelfAdjoint, star_smul, star_one, Complex.star_def,
      Complex.conj_ofReal]
  have hRsa : IsSelfAdjoint R := ringInverse_isSelfAdjoint hAsa hU
  set RY : E' →L[ℂ] V := R ∘L Y with hRYdef
  have hproj : M.range.starProjection ∘L (B†) = (B†) := by
    ext x
    exact M.range.starProjection_eq_self_iff.mpr (hnc ⟨x, rfl⟩)
  set u₀ : ℝ → (E' →L[ℂ] E) :=
    fun t => fdPinv M ∘L ((B†) ∘L (expH H t ∘L RY)) with hu₀def
  have hu₀cont : Continuous u₀ := by
    have h1 : Continuous fun t : ℝ => expH H t ∘L RY :=
      isBoundedBilinearMap_comp.continuous.comp
        ((expH_continuous H).prodMk continuous_const)
    have h2 : Continuous fun t : ℝ => (B†) ∘L (expH H t ∘L RY) :=
      isBoundedBilinearMap_comp.continuous.comp
        (continuous_const.prodMk h1)
    rw [hu₀def]
    exact isBoundedBilinearMap_comp.continuous.comp
      (continuous_const.prodMk h2)
  have habs : ∀ t : ℝ, M ∘L u₀ t = (B†) ∘L (expH H t ∘L RY) := by
    intro t
    simp only [hu₀def]
    rw [← ContinuousLinearMap.comp_assoc, comp_fdPinv,
      ← ContinuousLinearMap.comp_assoc, hproj]
  have hKu₀ : ∀ t : ℝ, (expH H t ∘L B) ∘L u₀ t
      = (expH H t ∘L sigmaBM B M ∘L (expH H t)†) ∘L RY := by
    intro t
    rw [expH_adjoint hH]
    simp only [hu₀def, sigmaBM, ContinuousLinearMap.comp_assoc]
  have hgramint : IntervalIntegrable
      (fun t => expH H t ∘L sigmaBM B M ∘L (expH H t)†)
      MeasureTheory.volume 0 T :=
    (gramW_integrand_continuous H (sigmaBM B M)).intervalIntegrable 0 T
  have hLu₀ : ctrlSyn H B T u₀ = W ∘L RY := by
    have h1 : ctrlSyn H B T u₀
        = ∫ t in (0:ℝ)..T,
            (expH H t ∘L sigmaBM B M ∘L (expH H t)†) ∘L RY :=
      intervalIntegral.integral_congr fun t _ => hKu₀ t
    rw [h1, ← intervalIntegral_comp_const hgramint RY]
    rfl
  have hY : Y = (W ∘L RY) + ((ε : ℝ) : ℂ) • RY := by
    have h1 : ((W + ((ε : ℝ) : ℂ) • 1) ∘L R) ∘L Y = Y := by
      rw [hAR, ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp]
    calc Y = ((W + ((ε : ℝ) : ℂ) • 1) ∘L R) ∘L Y := h1.symm
      _ = (W + ((ε : ℝ) : ℂ) • 1) ∘L RY := by
          rw [ContinuousLinearMap.comp_assoc, ← hRYdef]
      _ = (W ∘L RY) + ((ε : ℝ) : ℂ) • RY := by
          rw [ContinuousLinearMap.add_comp, ContinuousLinearMap.smul_comp,
            ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp]
  have hres : Y - ctrlSyn H B T u₀ = ((ε : ℝ) : ℂ) • RY := by
    rw [hLu₀]
    calc Y - W ∘L RY
        = ((W ∘L RY) + ((ε : ℝ) : ℂ) • RY) - W ∘L RY := by rw [← hY]
      _ = ((ε : ℝ) : ℂ) • RY := add_sub_cancel_left _ _
  have hEint : ∀ t : ℝ, ((u₀ t)†) ∘L M ∘L u₀ t
      = (RY†) ∘L (expH H t ∘L sigmaBM B M ∘L (expH H t)†) ∘L RY := by
    intro t
    have h1 : ((u₀ t)†) ∘L M ∘L u₀ t
        = ((u₀ t)†) ∘L ((B†) ∘L (expH H t ∘L RY)) := by
      rw [habs t]
    rw [h1, expH_adjoint hH]
    simp only [hu₀def, ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint,
      (fdPinv_isSelfAdjoint hM.isSelfAdjoint).adjoint_eq,
      expH_adjoint hH, sigmaBM, ContinuousLinearMap.comp_assoc]
  have hEn : (∫ t in (0:ℝ)..T, ((u₀ t)†) ∘L M ∘L u₀ t)
      = (RY†) ∘L W ∘L RY := by
    rw [intervalIntegral.integral_congr fun t _ => hEint t,
      ← compress_intervalIntegral_rect (RY†) RY hgramint]
    rfl
  have htik : tikRes W ε Y
      = (Y†) ∘L (((ε : ℝ) : ℂ) • R) ∘L Y := rfl
  have hRWR : R ∘L (W ∘L R) = R - ((ε : ℝ) : ℂ) • (R ∘L R) := by
    have h1 : R ∘L ((W + ((ε : ℝ) : ℂ) • 1) ∘L R) = R := by
      rw [hAR, ContinuousLinearMap.one_def, ContinuousLinearMap.comp_id]
    have h2 : (W + ((ε : ℝ) : ℂ) • 1) ∘L R
        = W ∘L R + ((ε : ℝ) : ℂ) • R := by
      rw [ContinuousLinearMap.add_comp, ContinuousLinearMap.smul_comp,
        ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp]
    rw [h2, ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_smul]
      at h1
    exact eq_sub_of_add_eq h1
  have hRYadj : RY† = (Y†) ∘L R := by
    rw [hRYdef, ContinuousLinearMap.adjoint_comp, hRsa.adjoint_eq]
  have hval : tikCost H B M T ε Y u₀ = tikRes W ε Y := by
    have hc0 : tikCost H B M T ε Y u₀
        = ((Y - ctrlSyn H B T u₀)†) ∘L (Y - ctrlSyn H B T u₀)
          + ((ε : ℝ) : ℂ)
            • ∫ t in (0:ℝ)..T, ((u₀ t)†) ∘L M ∘L u₀ t := rfl
    rw [hc0, hres, hEn, htik, adjoint_real_smul_rect,
      ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul,
      smul_smul]
    have h3 : RY† ∘L RY = (Y†) ∘L (R ∘L R) ∘L Y := by
      rw [hRYadj, hRYdef]
      simp only [ContinuousLinearMap.comp_assoc]
    have h4 : RY† ∘L W ∘L RY = (Y†) ∘L (R ∘L (W ∘L R)) ∘L Y := by
      rw [hRYadj, hRYdef]
      simp only [ContinuousLinearMap.comp_assoc]
    rw [h3, h4, ← compress_smul Y (((ε : ℝ) : ℂ) * ((ε : ℝ) : ℂ))
        (R ∘L R),
      ← compress_smul Y ((ε : ℝ) : ℂ) (R ∘L (W ∘L R)), ← compress_add]
    have hop : (((ε : ℝ) : ℂ) * ((ε : ℝ) : ℂ)) • (R ∘L R)
        + ((ε : ℝ) : ℂ) • (R ∘L (W ∘L R)) = ((ε : ℝ) : ℂ) • R := by
      rw [hRWR, smul_sub, smul_smul]
      abel
    rw [hop]
  have hcross : ∀ v : ℝ → (E' →L[ℂ] E), Continuous v →
      ((ctrlSyn H B T v)†) ∘L (Y - ctrlSyn H B T u₀)
        = ((ε : ℝ) : ℂ)
          • ∫ t in (0:ℝ)..T, ((v t)†) ∘L M ∘L u₀ t := by
    intro v hv
    rw [hres, ContinuousLinearMap.comp_smul]
    congr 1
    have hadj2 : (ctrlSyn H B T v)†
        = ∫ t in (0:ℝ)..T, ((v t)†) ∘L ((B†) ∘L expH H t) := by
      have h5 : (ctrlSyn H B T v)†
          = (∫ t in (0:ℝ)..T, (expH H t ∘L B) ∘L v t)† := rfl
      rw [h5, ← intervalIntegral_adjoint_rect]
      refine intervalIntegral.integral_congr fun t _ => ?_
      rw [ContinuousLinearMap.adjoint_comp,
        ContinuousLinearMap.adjoint_comp, expH_adjoint hH]
    have hint_adj : IntervalIntegrable
        (fun t => ((v t)†) ∘L ((B†) ∘L expH H t))
        MeasureTheory.volume 0 T := by
      have h7 : Continuous fun t => (v t)† :=
        ContinuousLinearMap.adjoint.continuous.comp hv
      have h8 : Continuous fun t : ℝ => (B†) ∘L expH H t :=
        isBoundedBilinearMap_comp.continuous.comp
          (continuous_const.prodMk (expH_continuous H))
      exact (isBoundedBilinearMap_comp.continuous.comp
        (h7.prodMk h8)).intervalIntegrable 0 T
    rw [hadj2, intervalIntegral_comp_const hint_adj RY]
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [habs t]
    simp only [ContinuousLinearMap.comp_assoc]
  have hcross' : ∀ v : ℝ → (E' →L[ℂ] E), Continuous v →
      ((Y - ctrlSyn H B T u₀)†) ∘L ctrlSyn H B T v
        = ((ε : ℝ) : ℂ)
          • ∫ t in (0:ℝ)..T, ((u₀ t)†) ∘L M ∘L v t := by
    intro v hv
    have h3 : (∫ t in (0:ℝ)..T, (((v t)†) ∘L M ∘L u₀ t)†)
        = ∫ t in (0:ℝ)..T, ((u₀ t)†) ∘L M ∘L v t :=
      intervalIntegral.integral_congr fun t _ => by
        rw [ContinuousLinearMap.adjoint_comp,
          ContinuousLinearMap.adjoint_comp,
          ContinuousLinearMap.adjoint_adjoint,
          hM.isSelfAdjoint.adjoint_eq]
        simp only [ContinuousLinearMap.comp_assoc]
    calc ((Y - ctrlSyn H B T u₀)†) ∘L ctrlSyn H B T v
        = (((ctrlSyn H B T v)†) ∘L (Y - ctrlSyn H B T u₀))† := by
          rw [ContinuousLinearMap.adjoint_comp,
            ContinuousLinearMap.adjoint_adjoint]
      _ = (((ε : ℝ) : ℂ)
            • ∫ t in (0:ℝ)..T, ((v t)†) ∘L M ∘L u₀ t)† := by
          rw [hcross v hv]
      _ = ((ε : ℝ) : ℂ)
            • (∫ t in (0:ℝ)..T, ((v t)†) ∘L M ∘L u₀ t)† :=
          adjoint_real_smul_rect ε _
      _ = ((ε : ℝ) : ℂ)
            • ∫ t in (0:ℝ)..T, (((v t)†) ∘L M ∘L u₀ t)† := by
          rw [intervalIntegral_adjoint_rect]
      _ = ((ε : ℝ) : ℂ)
            • ∫ t in (0:ℝ)..T, ((u₀ t)†) ∘L M ∘L v t := by
          rw [h3]
  refine ⟨fun u hu => ?_,
    ⟨u₀, hu₀cont, fun t x => ?_, hval⟩⟩
  swap
  · -- values of the optimal control lie in the metric support
    simp only [hu₀def]
    exact fdPinv_mem_ker_orthogonal M _
  · set v : ℝ → (E' →L[ℂ] E) := fun t => u t - u₀ t with hvdef
    have hvcont : Continuous v := by
      rw [hvdef]
      exact hu.sub hu₀cont
    have hu_eq : ∀ t, u t = u₀ t + v t := by
      intro t
      simp only [hvdef]
      abel
    have hint_u₀ : IntervalIntegrable
        (fun t => (expH H t ∘L B) ∘L u₀ t) MeasureTheory.volume 0 T :=
      (ctrl_integrand_continuous H B hu₀cont).intervalIntegrable 0 T
    have hint_v : IntervalIntegrable
        (fun t => (expH H t ∘L B) ∘L v t) MeasureTheory.volume 0 T :=
      (ctrl_integrand_continuous H B hvcont).intervalIntegrable 0 T
    have hE00 : IntervalIntegrable
        (fun t => ((u₀ t)†) ∘L M ∘L u₀ t) MeasureTheory.volume 0 T :=
      (energy_integrand_continuous M hu₀cont hu₀cont).intervalIntegrable
        0 T
    have hE0v : IntervalIntegrable
        (fun t => ((u₀ t)†) ∘L M ∘L v t) MeasureTheory.volume 0 T :=
      (energy_integrand_continuous M hu₀cont hvcont).intervalIntegrable
        0 T
    have hEv0 : IntervalIntegrable
        (fun t => ((v t)†) ∘L M ∘L u₀ t) MeasureTheory.volume 0 T :=
      (energy_integrand_continuous M hvcont hu₀cont).intervalIntegrable
        0 T
    have hEvv : IntervalIntegrable
        (fun t => ((v t)†) ∘L M ∘L v t) MeasureTheory.volume 0 T :=
      (energy_integrand_continuous M hvcont hvcont).intervalIntegrable
        0 T
    have hLsplit : ctrlSyn H B T u
        = ctrlSyn H B T u₀ + ctrlSyn H B T v := by
      have h1 : ctrlSyn H B T u
          = ∫ t in (0:ℝ)..T, ((expH H t ∘L B) ∘L u₀ t
              + (expH H t ∘L B) ∘L v t) :=
        intervalIntegral.integral_congr fun t _ => by
          rw [hu_eq t, ContinuousLinearMap.comp_add]
      rw [h1, intervalIntegral.integral_add hint_u₀ hint_v]
      rfl
    have hEsplit : (∫ t in (0:ℝ)..T, ((u t)†) ∘L M ∘L u t)
        = (∫ t in (0:ℝ)..T, ((u₀ t)†) ∘L M ∘L u₀ t)
          + (∫ t in (0:ℝ)..T, ((u₀ t)†) ∘L M ∘L v t)
          + ((∫ t in (0:ℝ)..T, ((v t)†) ∘L M ∘L u₀ t)
            + ∫ t in (0:ℝ)..T, ((v t)†) ∘L M ∘L v t) := by
      have h1 : (∫ t in (0:ℝ)..T, ((u t)†) ∘L M ∘L u t)
          = ∫ t in (0:ℝ)..T, (((u₀ t)†) ∘L M ∘L u₀ t
              + ((u₀ t)†) ∘L M ∘L v t
              + ((((v t)†) ∘L M ∘L u₀ t)
                + ((v t)†) ∘L M ∘L v t)) :=
        intervalIntegral.integral_congr fun t _ => by
          rw [hu_eq t]
          simp only [map_add ContinuousLinearMap.adjoint,
            ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]
          abel
      rw [h1, intervalIntegral.integral_add (hE00.add hE0v)
        (hEv0.add hEvv), intervalIntegral.integral_add hE00 hE0v,
        intervalIntegral.integral_add hEv0 hEvv]
    have hsq : ((Y - ctrlSyn H B T u)†) ∘L (Y - ctrlSyn H B T u)
        = ((Y - ctrlSyn H B T u₀)†) ∘L (Y - ctrlSyn H B T u₀)
          - ((Y - ctrlSyn H B T u₀)†) ∘L ctrlSyn H B T v
          - ((ctrlSyn H B T v)†) ∘L (Y - ctrlSyn H B T u₀)
          + ((ctrlSyn H B T v)†) ∘L ctrlSyn H B T v := by
      have h1 : Y - ctrlSyn H B T u
          = (Y - ctrlSyn H B T u₀) - ctrlSyn H B T v := by
        rw [hLsplit]
        abel
      rw [h1, map_sub ContinuousLinearMap.adjoint]
      ext z
      simp only [ContinuousLinearMap.comp_apply, _root_.sub_apply,
        _root_.add_apply, map_sub]
      abel
    have hdecomp : tikCost H B M T ε Y u
        = tikCost H B M T ε Y u₀
          + (((ctrlSyn H B T v)†) ∘L ctrlSyn H B T v
            + ((ε : ℝ) : ℂ)
              • ∫ t in (0:ℝ)..T, ((v t)†) ∘L M ∘L v t) := by
      have hc1 : tikCost H B M T ε Y u
          = ((Y - ctrlSyn H B T u)†) ∘L (Y - ctrlSyn H B T u)
            + ((ε : ℝ) : ℂ)
              • ∫ t in (0:ℝ)..T, ((u t)†) ∘L M ∘L u t := rfl
      have hc0 : tikCost H B M T ε Y u₀
          = ((Y - ctrlSyn H B T u₀)†) ∘L (Y - ctrlSyn H B T u₀)
            + ((ε : ℝ) : ℂ)
              • ∫ t in (0:ℝ)..T, ((u₀ t)†) ∘L M ∘L u₀ t := rfl
      rw [hc1, hc0, hsq, hEsplit, smul_add, smul_add, smul_add,
        ← hcross v hvcont, ← hcross' v hvcont]
      abel
    rw [hdecomp, hval, add_sub_cancel_left]
    refine (ContinuousLinearMap.isPositive_adjoint_comp_self _).add ?_
    refine ContinuousLinearMap.IsPositive.smul_of_nonneg ?_
      (Complex.zero_le_real.mpr hε.le)
    exact intervalIntegral_isPositive hT.le
      ((energy_integrand_continuous M hvcont hvcont).intervalIntegrable
        0 T)
      (fun t => hM.adjoint_conj (v t))

/-! ### Record 9: SMET.18–SMET.19, the transported reserve window -/

/-- Horizon Gramians are additive in the source kernel (difference
form). -/
theorem gramW_sub (H : V →L[ℂ] V) (S₁ S₂ : V →L[ℂ] V) (T : ℝ) :
    gramW H S₁ T - gramW H S₂ T = gramW H (S₁ - S₂) T := by
  have h1 : IntervalIntegrable (fun t => expH H t ∘L S₁ ∘L (expH H t)†)
      MeasureTheory.volume 0 T :=
    (gramW_integrand_continuous H S₁).intervalIntegrable 0 T
  have h2 : IntervalIntegrable (fun t => expH H t ∘L S₂ ∘L (expH H t)†)
      MeasureTheory.volume 0 T :=
    (gramW_integrand_continuous H S₂).intervalIntegrable 0 T
  calc gramW H S₁ T - gramW H S₂ T
      = (∫ t in (0:ℝ)..T, expH H t ∘L S₁ ∘L (expH H t)†)
        - ∫ t in (0:ℝ)..T, expH H t ∘L S₂ ∘L (expH H t)† := rfl
    _ = ∫ t in (0:ℝ)..T, (expH H t ∘L S₁ ∘L (expH H t)†
          - expH H t ∘L S₂ ∘L (expH H t)†) :=
        (intervalIntegral.integral_sub h1 h2).symm
    _ = gramW H (S₁ - S₂) T :=
        intervalIntegral.integral_congr fun t _ => by
          rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub]

/-- Horizon Gramians scale with the source kernel. -/
theorem gramW_smul (H : V →L[ℂ] V) (S : V →L[ℂ] V) (c : ℂ) (T : ℝ) :
    c • gramW H S T = gramW H (c • S) T := by
  calc c • gramW H S T
      = c • ∫ t in (0:ℝ)..T, expH H t ∘L S ∘L (expH H t)† := rfl
    _ = ∫ t in (0:ℝ)..T, c • (expH H t ∘L S ∘L (expH H t)†) :=
        (intervalIntegral.integral_smul c _).symm
    _ = gramW H (c • S) T :=
        intervalIntegral.integral_congr fun t _ => by
          rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]

/-- **(SMET.18)** The reserve window transports to the complete horizon:
`g₋ Ŵ_{T,B} ⪯ 𝒲_{T;B,M} ⪯ g₊ Ŵ_{T,B}` whenever
`g₋ P_B ⪯ Σ_{B,M} ⪯ g₊ P_B`. -/
theorem source_metric_horizon_window (H : V →L[ℂ] V) (B : E →L[ℂ] V)
    (M : E →L[ℂ] E) {gm gp : ℝ}
    (hlow : (sigmaBM B M - ((gm : ℝ) : ℂ) • rangeProj B).IsPositive)
    (hhigh : (((gp : ℝ) : ℂ) • rangeProj B - sigmaBM B M).IsPositive)
    {T : ℝ} (hT : 0 ≤ T) :
    (horW H B M T - ((gm : ℝ) : ℂ) • horWhat H B T).IsPositive
    ∧ (((gp : ℝ) : ℂ) • horWhat H B T - horW H B M T).IsPositive := by
  constructor
  · have h1 : horW H B M T - ((gm : ℝ) : ℂ) • horWhat H B T
        = gramW H (sigmaBM B M - ((gm : ℝ) : ℂ) • rangeProj B) T := by
      rw [horW, horWhat, gramW_smul, gramW_sub]
    rw [h1]
    exact gramW_isPositive hlow hT
  · have h1 : ((gp : ℝ) : ℂ) • horWhat H B T - horW H B M T
        = gramW H (((gp : ℝ) : ℂ) • rangeProj B - sigmaBM B M) T := by
      rw [horW, horWhat, gramW_smul, gramW_sub]
    rw [h1]
    exact gramW_isPositive hhigh hT

/-- **(SMET.19)** The Tikhonov comparison through the reserve window:
`R̂_{T,ε/g₊} ⪯ R_{T,ε}^M ⪯ R̂_{T,ε/g₋}` — finite positive leverage and
minimum source action depend on the range geometry only through the
reserve window. -/
theorem source_metric_horizon_tikhonov_window (H : V →L[ℂ] V)
    (B : E →L[ℂ] V) (M : E →L[ℂ] E) (Y : E' →L[ℂ] V)
    (hM : M.IsPositive) (hnc : ((B†)).range ≤ M.range)
    {gm gp : ℝ} (hgm : 0 < gm) (hgp : 0 < gp)
    (hlow : (sigmaBM B M - ((gm : ℝ) : ℂ) • rangeProj B).IsPositive)
    (hhigh : (((gp : ℝ) : ℂ) • rangeProj B - sigmaBM B M).IsPositive)
    {T ε : ℝ} (hT : 0 < T) (hε : 0 < ε) :
    (tikRes (horW H B M T) ε Y
      - tikRes (horWhat H B T) (ε / gp) Y).IsPositive
    ∧ (tikRes (horWhat H B T) (ε / gm) Y
      - tikRes (horW H B M T) ε Y).IsPositive := by
  have hWpos : (horW H B M T).IsPositive :=
    gramW_isPositive (sigmaBM_isPositive hM hnc) hT.le
  have hWhpos : (horWhat H B T).IsPositive :=
    gramW_isPositive (rangeProj_isPositive B) hT.le
  have hApos : (horW H B M T + ((ε : ℝ) : ℂ) • 1).IsPositive :=
    shift_isPositive hWpos hε.le
  have hUA : IsUnit (horW H B M T + ((ε : ℝ) : ℂ) • 1) :=
    shift_isUnit hWpos hε
  constructor
  · -- upper route: 𝒲 + ε ⪯ g₊ (Ŵ + ε/g₊) forces the lower Tikhonov bound
    have hδ : 0 < ε / gp := div_pos hε hgp
    have hDpos : (horWhat H B T + ((ε / gp : ℝ) : ℂ) • 1).IsPositive :=
      shift_isPositive hWhpos hδ.le
    have hUD : IsUnit (horWhat H B T + ((ε / gp : ℝ) : ℂ) • 1) :=
      shift_isUnit hWhpos hδ
    have hgpc : ((gp : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hgp.ne'
    have hCpos : (((gp : ℝ) : ℂ)
        • (horWhat H B T + ((ε / gp : ℝ) : ℂ) • 1)).IsPositive :=
      hDpos.smul_of_nonneg (Complex.zero_le_real.mpr hgp.le)
    have hUC : IsUnit (((gp : ℝ) : ℂ)
        • (horWhat H B T + ((ε / gp : ℝ) : ℂ) • 1)) :=
      isUnit_smul_unit hgpc hUD
    have harith : gp * (ε / gp) = ε := by field_simp
    have hCeq : ((gp : ℝ) : ℂ)
        • (horWhat H B T + ((ε / gp : ℝ) : ℂ) • 1)
        = ((gp : ℝ) : ℂ) • horWhat H B T + ((ε : ℝ) : ℂ) • 1 := by
      rw [smul_add, smul_smul, ← Complex.ofReal_mul, harith]
    have hCA : (((gp : ℝ) : ℂ)
        • (horWhat H B T + ((ε / gp : ℝ) : ℂ) • 1)
        - (horW H B M T + ((ε : ℝ) : ℂ) • 1)).IsPositive := by
      rw [hCeq]
      have h2 : ((gp : ℝ) : ℂ) • horWhat H B T + ((ε : ℝ) : ℂ) • 1
          - (horW H B M T + ((ε : ℝ) : ℂ) • 1)
          = ((gp : ℝ) : ℂ) • horWhat H B T - horW H B M T := by
        abel
      rw [h2]
      exact (source_metric_horizon_window H B M hlow hhigh hT.le).2
    have hinv := ringInverse_antitone hApos hCpos hUA hUC hCA
    have hsc : ((ε : ℝ) : ℂ) • Ring.inverse (((gp : ℝ) : ℂ)
        • (horWhat H B T + ((ε / gp : ℝ) : ℂ) • 1))
        = ((ε / gp : ℝ) : ℂ)
          • Ring.inverse (horWhat H B T + ((ε / gp : ℝ) : ℂ) • 1) := by
      rw [ringInverse_smul hgpc hUD, smul_smul, ← Complex.ofReal_inv,
        ← Complex.ofReal_mul, ← div_eq_mul_inv]
    have hkey : ContinuousLinearMap.IsPositive
        (((ε : ℝ) : ℂ)
          • Ring.inverse (horW H B M T + ((ε : ℝ) : ℂ) • 1)
          - ((ε / gp : ℝ) : ℂ)
            • Ring.inverse (horWhat H B T + ((ε / gp : ℝ) : ℂ) • 1)) := by
      rw [← hsc, ← smul_sub]
      exact hinv.smul_of_nonneg (Complex.zero_le_real.mpr hε.le)
    have ht1 : tikRes (horW H B M T) ε Y
        = (Y†) ∘L (((ε : ℝ) : ℂ)
            • Ring.inverse (horW H B M T + ((ε : ℝ) : ℂ) • 1)) ∘L Y :=
      rfl
    have ht2 : tikRes (horWhat H B T) (ε / gp) Y
        = (Y†) ∘L (((ε / gp : ℝ) : ℂ)
            • Ring.inverse (horWhat H B T
              + ((ε / gp : ℝ) : ℂ) • 1)) ∘L Y := rfl
    rw [ht1, ht2, ← compress_sub]
    exact hkey.adjoint_conj Y
  · -- lower route: g₋ (Ŵ + ε/g₋) ⪯ 𝒲 + ε forces the upper Tikhonov bound
    have hδ : 0 < ε / gm := div_pos hε hgm
    have hDpos : (horWhat H B T + ((ε / gm : ℝ) : ℂ) • 1).IsPositive :=
      shift_isPositive hWhpos hδ.le
    have hUD : IsUnit (horWhat H B T + ((ε / gm : ℝ) : ℂ) • 1) :=
      shift_isUnit hWhpos hδ
    have hgmc : ((gm : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hgm.ne'
    have hCpos : (((gm : ℝ) : ℂ)
        • (horWhat H B T + ((ε / gm : ℝ) : ℂ) • 1)).IsPositive :=
      hDpos.smul_of_nonneg (Complex.zero_le_real.mpr hgm.le)
    have hUC : IsUnit (((gm : ℝ) : ℂ)
        • (horWhat H B T + ((ε / gm : ℝ) : ℂ) • 1)) :=
      isUnit_smul_unit hgmc hUD
    have harith : gm * (ε / gm) = ε := by field_simp
    have hCeq : ((gm : ℝ) : ℂ)
        • (horWhat H B T + ((ε / gm : ℝ) : ℂ) • 1)
        = ((gm : ℝ) : ℂ) • horWhat H B T + ((ε : ℝ) : ℂ) • 1 := by
      rw [smul_add, smul_smul, ← Complex.ofReal_mul, harith]
    have hAC : ((horW H B M T + ((ε : ℝ) : ℂ) • 1)
        - ((gm : ℝ) : ℂ)
          • (horWhat H B T + ((ε / gm : ℝ) : ℂ) • 1)).IsPositive := by
      rw [hCeq]
      have h2 : horW H B M T + ((ε : ℝ) : ℂ) • 1
          - (((gm : ℝ) : ℂ) • horWhat H B T + ((ε : ℝ) : ℂ) • 1)
          = horW H B M T - ((gm : ℝ) : ℂ) • horWhat H B T := by
        abel
      rw [h2]
      exact (source_metric_horizon_window H B M hlow hhigh hT.le).1
    have hinv := ringInverse_antitone hCpos hApos hUC hUA hAC
    have hsc : ((ε : ℝ) : ℂ) • Ring.inverse (((gm : ℝ) : ℂ)
        • (horWhat H B T + ((ε / gm : ℝ) : ℂ) • 1))
        = ((ε / gm : ℝ) : ℂ)
          • Ring.inverse (horWhat H B T + ((ε / gm : ℝ) : ℂ) • 1) := by
      rw [ringInverse_smul hgmc hUD, smul_smul, ← Complex.ofReal_inv,
        ← Complex.ofReal_mul, ← div_eq_mul_inv]
    have hkey : ContinuousLinearMap.IsPositive
        (((ε / gm : ℝ) : ℂ)
          • Ring.inverse (horWhat H B T + ((ε / gm : ℝ) : ℂ) • 1)
          - ((ε : ℝ) : ℂ)
            • Ring.inverse (horW H B M T + ((ε : ℝ) : ℂ) • 1)) := by
      rw [← hsc, ← smul_sub]
      exact hinv.smul_of_nonneg (Complex.zero_le_real.mpr hε.le)
    have ht1 : tikRes (horW H B M T) ε Y
        = (Y†) ∘L (((ε : ℝ) : ℂ)
            • Ring.inverse (horW H B M T + ((ε : ℝ) : ℂ) • 1)) ∘L Y :=
      rfl
    have ht2 : tikRes (horWhat H B T) (ε / gm) Y
        = (Y†) ∘L (((ε / gm : ℝ) : ℂ)
            • Ring.inverse (horWhat H B T
              + ((ε / gm : ℝ) : ℂ) • 1)) ∘L Y := rfl
    rw [ht1, ht2, ← compress_sub]
    exact hkey.adjoint_conj Y

end SourceMetricHorizon

end NCG
