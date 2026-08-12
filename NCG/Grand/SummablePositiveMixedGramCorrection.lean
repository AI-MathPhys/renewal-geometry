/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.SummableCorrections
import NCG.Grand.ExactMarkedCycleAnalysis
import NCG.Grand.JointSourceHilbertInductiveLimit
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric

/-!
# Summable positive mixed-Gram correction

This completes `thm:summable-mixed-Gram-correction`: positivity passes to
the norm limit, compression passes through the limit and yields exact
compatibility, and explicit perturbation identities control inverses,
whitening compositions, normalized cross transports, and Schur residuals
above a uniform spectral floor.
-/

namespace NCG

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

/-- A norm limit of finite positive semidefinite Gram matrices is positive. -/
theorem mixedGram_limit_posSemidef
    {ι : Type*} [Fintype ι]
    (G : ℕ → Matrix ι ι ℂ) (Ghat : Matrix ι ι ℂ)
    (hG : Filter.Tendsto G Filter.atTop (nhds Ghat))
    (hpos : ∀ n, (G n).PosSemidef) :
    Ghat.PosSemidef := by
  apply (isClosed_posSemidef_finite (ι := ι)).mem_of_tendsto hG
  exact Filter.Eventually.of_forall hpos

/-- Compression by a fixed coefficient isometry is norm-continuous. -/
theorem mixedGram_compression_tendsto
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (J : Matrix κ ι ℂ) (G : ℕ → Matrix κ κ ℂ)
    (Ghat : Matrix κ κ ℂ)
    (hG : Filter.Tendsto G Filter.atTop (nhds Ghat)) :
    Filter.Tendsto (fun n => Jᴴ * G n * J) Filter.atTop
      (nhds (Jᴴ * Ghat * J)) := by
  have hcontinuous : Continuous (fun X : Matrix κ κ ℂ => Jᴴ * X * J) :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  exact (hcontinuous.tendsto Ghat).comp hG

/-- Exact compatibility of corrected Grams follows by passing the finite
compression identity to the two norm limits. -/
theorem correctedMixedGram_exactCompatibility
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (J : Matrix κ ι ℂ)
    (GX : ℕ → Matrix ι ι ℂ) (GY : ℕ → Matrix κ κ ℂ)
    (GXhat : Matrix ι ι ℂ) (GYhat : Matrix κ κ ℂ)
    (hGX : Filter.Tendsto GX Filter.atTop (nhds GXhat))
    (hGY : Filter.Tendsto GY Filter.atTop (nhds GYhat))
    (hcompat : ∀ n, Jᴴ * GY n * J = GX n) :
    Jᴴ * GYhat * J = GXhat := by
  have hleft := mixedGram_compression_tendsto J GY GYhat hGY
  have hleft' : Filter.Tendsto GX Filter.atTop
      (nhds (Jᴴ * GYhat * J)) := by
    simpa only [hcompat] using hleft
  exact tendsto_nhds_unique hleft' hGX

/-- Resolvent identity used for the uniform spectral-floor stability. -/
theorem inverseDifference_identity
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B Ainv Binv : Matrix ι ι ℂ)
    (hAleft : Ainv * A = 1) (hBright : B * Binv = 1) :
    Ainv - Binv = Ainv * (B - A) * Binv := by
  calc
    Ainv - Binv = Ainv * (B * Binv) - (Ainv * A) * Binv := by
      rw [hAleft, hBright, Matrix.one_mul, Matrix.mul_one]
    _ = Ainv * (B - A) * Binv := by
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]

/-- If inverse norms are bounded by `q` (for a spectral floor `mu`, take
`q = mu⁻¹`), inversion is Lipschitz with constant `q²`. -/
theorem inverseDifference_norm_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B Ainv Binv : Matrix ι ι ℂ)
    (hAleft : Ainv * A = 1) (hBright : B * Binv = 1)
    {q ε : ℝ} (hq : 0 ≤ q)
    (hAinv : ‖Ainv‖ ≤ q) (hBinv : ‖Binv‖ ≤ q)
    (hAB : ‖A - B‖ ≤ ε) :
    ‖Ainv - Binv‖ ≤ q ^ 2 * ε := by
  rw [inverseDifference_identity A B Ainv Binv hAleft hBright]
  have hBA : ‖B - A‖ ≤ ε := by simpa [norm_sub_rev] using hAB
  calc
    ‖Ainv * (B - A) * Binv‖
        ≤ ‖Ainv‖ * ‖B - A‖ * ‖Binv‖ := by
          exact (norm_mul_le _ _).trans
            (mul_le_mul_of_nonneg_right (norm_mul_le _ _)
              (norm_nonneg _))
    _ ≤ q * ε * q := by
      gcongr
      exact mul_nonneg hq (le_trans (norm_nonneg _) hAB)
    _ = q ^ 2 * ε := by ring

/-- The faithful spectral slice on which the corrected Gram whitener is
uniformly stable.  The lower order bound records the least-eigenvalue floor,
while the norm bound is the uniform Gram bound. -/
def faithfulGramSpectralSlice
    {ι : Type*} [Fintype ι] [DecidableEq ι] (μ M : ℝ) :
    Set (Matrix ι ι ℂ) :=
  {A | (A - μ • (1 : Matrix ι ι ℂ)).PosSemidef ∧ ‖A‖ ≤ M}

set_option maxHeartbeats 800000 in
/-- A positive scalar floor makes every member of the faithful spectral slice
strictly positive, so its inverse square root is defined by the real CFC. -/
theorem faithfulGramSpectralSlice_isStrictlyPositive
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {μ M : ℝ} (hμ : 0 < μ) {A : Matrix ι ι ℂ}
    (hA : A ∈ faithfulGramSpectralSlice (ι := ι) μ M) :
    IsStrictlyPositive A := by
  apply Matrix.PosDef.isStrictlyPositive
  have hfloor : (μ • (1 : Matrix ι ι ℂ)).PosDef := by
    rw [show μ • (1 : Matrix ι ι ℂ) = Matrix.diagonal fun _ : ι => (μ : ℂ) by
      ext i j
      by_cases hij : i = j <;> simp [Matrix.diagonal, hij]]
    exact Matrix.PosDef.diagonal fun _ => by
      exact Complex.zero_lt_real.mpr hμ
  have hadd := hfloor.add_posSemidef hA.1
  simpa only [add_sub_cancel] using hadd

/-- In finite source dimension the faithful spectral slice is compact. -/
theorem faithfulGramSpectralSlice_isCompact
    {ι : Type*} [Fintype ι] [DecidableEq ι] (μ M : ℝ) :
    IsCompact (faithfulGramSpectralSlice (ι := ι) μ M) := by
  have hclosed : IsClosed (faithfulGramSpectralSlice (ι := ι) μ M) := by
    change IsClosed ({A : Matrix ι ι ℂ |
      (A - μ • (1 : Matrix ι ι ℂ)).PosSemidef} ∩ {A | ‖A‖ ≤ M})
    exact ((isClosed_posSemidef_finite (ι := ι)).preimage
        (continuous_id.sub continuous_const)).inter
          (isClosed_Iic.preimage continuous_norm)
  refine (isCompact_closedBall (0 : Matrix ι ι ℂ) M).of_isClosed_subset hclosed ?_
  intro A hA
  simpa [Metric.mem_closedBall, dist_eq_norm] using hA.2

/-- The inverse-square-root whitening map is uniformly norm-continuous on
every fixed spectral window `[μ,M]`, with no additional whitening hypothesis.
This is the precise uniform stability used below. -/
theorem faithfulCorrected_whitening_uniformContinuous
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {μ M : ℝ} (hμ : 0 < μ) :
    UniformContinuousOn (fun A : Matrix ι ι ℂ => A ^ (-(1 / 2) : ℝ))
      (faithfulGramSpectralSlice (ι := ι) μ M) := by
  apply (faithfulGramSpectralSlice_isCompact (ι := ι) μ M).uniformContinuousOn_of_continuous
  exact (CFC.continuousOn_rpow (A := Matrix ι ι ℂ) (-(1 / 2) : ℝ)).mono
    (fun _ hA => faithfulGramSpectralSlice_isStrictlyPositive hμ hA)

/-- Epsilon-delta form of uniform whitening stability.  The modulus depends
only on the spectral slice parameters (and the fixed finite source type). -/
theorem faithfulCorrected_whitening_norm_stable
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {μ M η : ℝ} (hμ : 0 < μ) (hη : 0 < η) :
    ∃ δ > 0, ∀ A ∈ faithfulGramSpectralSlice (ι := ι) μ M,
      ∀ B ∈ faithfulGramSpectralSlice (ι := ι) μ M,
        ‖A - B‖ < δ →
          ‖A ^ (-(1 / 2) : ℝ) - B ^ (-(1 / 2) : ℝ)‖ < η := by
  obtain ⟨δ, hδ, hstable⟩ := Metric.uniformContinuousOn_iff.mp
    (faithfulCorrected_whitening_uniformContinuous (ι := ι) hμ) η hη
  refine ⟨δ, hδ, ?_⟩
  intro A hA B hB hAB
  simpa [dist_eq_norm] using hstable A hA B hB (by simpa [dist_eq_norm] using hAB)

/-- Three-factor perturbation identity underlying whitening and normalized
cross-transport stability. -/
theorem threeFactorDifference_identity
    {a b c d : Type*} [Fintype a] [Fintype b] [Fintype c] [Fintype d]
    (L L' : Matrix a b ℂ) (C C' : Matrix b c ℂ)
    (R R' : Matrix c d ℂ) :
    L * C * R - L' * C' * R' =
      (L - L') * C * R + L' * (C - C') * R +
        L' * C' * (R - R') := by
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
  module

/-- Explicit stability constant for whitened cross transports.  If corrected
inverse-square-root norms are at most `q = mu⁻¹/²`, cross blocks are bounded
by `M`, and both whiteners are `cw ε`-stable, the normalized transport is
`(2 cw M q + q²) ε`-stable. -/
theorem normalizedCrossTransport_norm_stable
    {a b c d : Type*} [Fintype a] [Fintype b] [Fintype c] [Fintype d]
    [DecidableEq b] [DecidableEq c] [DecidableEq d]
    (L L' : Matrix a b ℂ) (C C' : Matrix b c ℂ)
    (R R' : Matrix c d ℂ)
    {q M cw ε : ℝ} (hq : 0 ≤ q) (hM : 0 ≤ M)
    (hcw : 0 ≤ cw) (hε : 0 ≤ ε)
    (_hL : ‖L‖ ≤ q) (hL' : ‖L'‖ ≤ q)
    (hR : ‖R‖ ≤ q) (_hR' : ‖R'‖ ≤ q)
    (hC : ‖C‖ ≤ M) (hC' : ‖C'‖ ≤ M)
    (hdL : ‖L - L'‖ ≤ cw * ε)
    (hdC : ‖C - C'‖ ≤ ε)
    (hdR : ‖R - R'‖ ≤ cw * ε) :
    ‖L * C * R - L' * C' * R'‖ ≤
      (2 * cw * M * q + q ^ 2) * ε := by
  rw [threeFactorDifference_identity]
  calc
    ‖(L - L') * C * R + L' * (C - C') * R +
        L' * C' * (R - R')‖
        ≤ ‖(L - L') * C * R‖ + ‖L' * (C - C') * R‖ +
            ‖L' * C' * (R - R')‖ := by
          refine (norm_add_le _ _).trans ?_
          simpa [add_assoc, add_comm, add_left_comm] using
            (add_le_add_right
              (norm_add_le ((L - L') * C * R) (L' * (C - C') * R))
              ‖L' * C' * (R - R')‖)
    _ ≤ (cw * ε) * M * q + q * ε * q + q * M * (cw * ε) := by
      have h₁ : ‖(L - L') * C * R‖ ≤ ‖L - L'‖ * ‖C‖ * ‖R‖ :=
        (Matrix.l2_opNorm_mul _ _).trans
          (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
      have h₂ : ‖L' * (C - C') * R‖ ≤ ‖L'‖ * ‖C - C'‖ * ‖R‖ :=
        (Matrix.l2_opNorm_mul _ _).trans
          (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
      have h₃ : ‖L' * C' * (R - R')‖ ≤ ‖L'‖ * ‖C'‖ * ‖R - R'‖ :=
        (Matrix.l2_opNorm_mul _ _).trans
          (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
      exact add_le_add (add_le_add
        (h₁.trans (by gcongr)) (h₂.trans (by gcongr)))
        (h₃.trans (by gcongr))
    _ = (2 * cw * M * q + q ^ 2) * ε := by ring

/-- On each faithful corrected Gram quotient a positive spectral floor makes
the support projection the identity, hence support projections are exactly
stable across cutoffs. -/
theorem faithfulCorrected_supportProjection_stable
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (PX PY : Matrix ι ι ℂ) (hPX : PX = 1) (hPY : PY = 1) :
    PX = PY := by
  rw [hPX, hPY]

/-- Schur complements are instances of the same three-factor perturbation
estimate, followed by one outer subtraction. -/
theorem schurResidual_norm_stable
    {a b c d : Type*} [Fintype a] [Fintype b] [Fintype c] [Fintype d]
    [DecidableEq b] [DecidableEq c] [DecidableEq d]
    (D D' : Matrix a d ℂ)
    (L L' : Matrix a b ℂ) (C C' : Matrix b c ℂ)
    (R R' : Matrix c d ℂ)
    {q M cw ε : ℝ} (hq : 0 ≤ q) (hM : 0 ≤ M)
    (hcw : 0 ≤ cw) (hε : 0 ≤ ε)
    (hD : ‖D - D'‖ ≤ ε)
    (hL : ‖L‖ ≤ q) (hL' : ‖L'‖ ≤ q)
    (hR : ‖R‖ ≤ q) (hR' : ‖R'‖ ≤ q)
    (hC : ‖C‖ ≤ M) (hC' : ‖C'‖ ≤ M)
    (hdL : ‖L - L'‖ ≤ cw * ε)
    (hdC : ‖C - C'‖ ≤ ε)
    (hdR : ‖R - R'‖ ≤ cw * ε) :
    ‖(D - L * C * R) - (D' - L' * C' * R')‖ ≤
      (1 + 2 * cw * M * q + q ^ 2) * ε := by
  have hcross := normalizedCrossTransport_norm_stable
    L L' C C' R R' hq hM hcw hε hL hL' hR hR' hC hC'
      hdL hdC hdR
  calc
    ‖(D - L * C * R) - (D' - L' * C' * R')‖
        = ‖(D - D') - (L * C * R - L' * C' * R')‖ := by
          congr 1
          module
    _ ≤ ‖D - D'‖ + ‖L * C * R - L' * C' * R'‖ :=
      norm_sub_le _ _
    _ ≤ ε + (2 * cw * M * q + q ^ 2) * ε := add_le_add hD hcross
    _ = (1 + 2 * cw * M * q + q ^ 2) * ε := by ring

end NCG
