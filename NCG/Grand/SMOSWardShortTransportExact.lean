/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.EfficientConnectedScorePseudoinverseExact
import NCG.Grand.GRHRestoringShortExact
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Exact transport of simultaneous Ward shorts

This proves `thm:SMOS-Ward-short-transport`.  A protected Gram floor gives a
canonical left inverse of norm at most `gamma^{-1/2}`.  The two cross-gap
expansion for orthogonal range projections then gives the stronger estimate
`‖P_Y-P_X‖ ≤ 2 gamma^{-1/2} ‖N_Y-N_X‖`; the manuscript's displayed bound
follows by adding its nonnegative Gram-defect term.  The efficient-source
transport estimate is proved by the stated add-and-subtract argument.
-/

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace NCG
namespace SMOSWardShortTransportExact

open SourceCoercivityInfluence
open EfficientConnectedScorePseudoinverse
open GeometricThresholdBank PsdBlockSchur

set_option maxHeartbeats 2400000

variable {H E K : Type*} [Fintype H] [Fintype E] [Fintype K]
variable [DecidableEq H] [DecidableEq E] [DecidableEq K]

/-- The canonical full-column-rank left inverse. -/
noncomputable def gramLeftInverse (N : Matrix H E ℂ) : Matrix E H ℂ :=
  pinv (nuisanceGram_posSemidef N).1 * Nᴴ

/-- A Loewner Gram floor implies the corresponding pointwise eigenvalue
floor. -/
theorem eigenvalue_floor_of_gramFloor
    (N : Matrix H E ℂ) (gamma : ℝ)
    (hfloor : ((Nᴴ * N) - (gamma : ℂ) • (1 : Matrix E E ℂ)).PosSemidef) :
    ∀ i, gamma ≤ (nuisanceGram_posSemidef N).1.eigenvalues i := by
  intro i
  let G : Matrix E E ℂ := Nᴴ * N
  let hG : G.PosSemidef := nuisanceGram_posSemidef N
  let U := hG.1.eigenvectorUnitary
  let V : Matrix E E ℂ := U
  have hdiag : Vᴴ * G * V =
      Matrix.diagonal (RCLike.ofReal ∘ hG.1.eigenvalues) := by
    have h := hG.1.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_star_apply] at h
    simpa only [V, U, G, star_eq_conjTranspose] using h
  have hVstarV : Vᴴ * V = 1 := by
    change (star U : Matrix E E ℂ) * U = 1
    exact Unitary.coe_star_mul_self U
  have hconj :
      (Vᴴ * (G - (gamma : ℂ) • (1 : Matrix E E ℂ)) * V).PosSemidef := by
    exact hfloor.conjTranspose_mul_mul_same V
  have hform : Vᴴ * (G - (gamma : ℂ) • (1 : Matrix E E ℂ)) * V =
      Matrix.diagonal (fun j => ((hG.1.eigenvalues j - gamma : ℝ) : ℂ)) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hdiag]
    have hs : Vᴴ * ((gamma : ℂ) • (1 : Matrix E E ℂ)) * V =
        (gamma : ℂ) • (1 : Matrix E E ℂ) := by
      simp only [Matrix.mul_smul, Matrix.one_mul, Matrix.smul_mul,
        Matrix.mul_one, hVstarV]
    rw [hs]
    ext a b
    by_cases hab : a = b
    · subst b
      simp [Function.comp_apply]
    · simp [Matrix.diagonal_apply_ne _ hab, Matrix.one_apply_ne hab]
  rw [hform] at hconj
  have hii := hconj.diag_nonneg (i := i)
  simpa [Complex.nonneg_iff, Function.comp_apply] using
    (Complex.le_def.mp hii).1

/-- Spectral pseudoinverse norm under a positive eigenvalue floor. -/
theorem pinv_norm_le_inv
    {G : Matrix E E ℂ} (hG : G.PosSemidef)
    (gamma : ℝ) (hgamma : 0 < gamma)
    (hfloor : ∀ i, gamma ≤ hG.1.eigenvalues i) :
    ‖pinv hG.1‖ ≤ gamma⁻¹ := by
  let U := hG.1.eigenvectorUnitary
  let D : Matrix E E ℂ := Matrix.diagonal
    (RCLike.ofReal ∘ fun i => if 0 < hG.1.eigenvalues i
      then (hG.1.eigenvalues i)⁻¹ else 0)
  have hnorm : ‖pinv hG.1‖ = ‖D‖ := by
    unfold pinv spectralFunction
    rw [Unitary.conjStarAlgAut_apply]
    change ‖(U : Matrix E E ℂ) * D * star (U : Matrix E E ℂ)‖ = ‖D‖
    calc
      ‖(U : Matrix E E ℂ) * D * star (U : Matrix E E ℂ)‖ =
          ‖D * star (U : Matrix E E ℂ)‖ := by
        rw [Matrix.mul_assoc, CStarRing.norm_coe_unitary_mul]
      _ = ‖D‖ := by
        simpa using CStarRing.norm_mul_coe_unitary D (star U)
  rw [hnorm]
  dsimp only [D]
  rw [Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (inv_nonneg.mpr hgamma.le)).2
  intro i
  have hi : 0 < hG.1.eigenvalues i := hgamma.trans_le (hfloor i)
  simp only [Function.comp_apply, if_pos hi]
  calc
    ‖(((hG.1.eigenvalues i)⁻¹ : ℝ) : ℂ)‖ = |(hG.1.eigenvalues i)⁻¹| :=
      RCLike.norm_ofReal _
    _ = (hG.1.eigenvalues i)⁻¹ := abs_of_pos (inv_pos.mpr hi)
    _ ≤ gamma⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le hgamma (hfloor i)

/-- The canonical left inverse has norm at most `gamma^{-1/2}` and is a
genuine left inverse. -/
theorem gramLeftInverse_certificate
    (N : Matrix H E ℂ) (gamma : ℝ) (hgamma : 0 < gamma)
    (hfloor : ((Nᴴ * N) - (gamma : ℂ) • (1 : Matrix E E ℂ)).PosSemidef) :
    gramLeftInverse N * N = 1
      ∧ ‖gramLeftInverse N‖ ≤ (Real.sqrt gamma)⁻¹ := by
  let G : Matrix E E ℂ := Nᴴ * N
  let hG : G.PosSemidef := nuisanceGram_posSemidef N
  have heig : ∀ i, gamma ≤ hG.1.eigenvalues i :=
    eigenvalue_floor_of_gramFloor N gamma hfloor
  have hpd : G.PosDef := hG.1.posDef_iff_eigenvalues_pos.mpr
    (fun i => hgamma.trans_le (heig i))
  have hsupp : supportProj hG.1 = 1 := GRHRestoringShort.supportProj_eq_one hpd
  have hleft : gramLeftInverse N * N = 1 := by
    unfold gramLeftInverse
    simp only [Matrix.mul_assoc]
    change pinv hG.1 * G = 1
    rw [← supportProj_eq_pinv_mul, hsupp]
  have hLL : gramLeftInverse N * (gramLeftInverse N)ᴴ = pinv hG.1 := by
    unfold gramLeftInverse
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      (pinv_isHermitian hG.1).eq]
    calc
      (pinv hG.1 * Nᴴ) * (N * pinv hG.1) =
          pinv hG.1 * (Nᴴ * N) * pinv hG.1 := by
        simp only [Matrix.mul_assoc]
      _ = pinv hG.1 := pinv_mul_self_mul_pinv hG.1
  have hpinv := pinv_norm_le_inv hG gamma hgamma heig
  have hsq : ‖gramLeftInverse N‖ ^ 2 ≤ gamma⁻¹ := by
    have hn := Matrix.l2_opNorm_conjTranspose_mul_self
      ((gramLeftInverse N)ᴴ)
    rw [Matrix.conjTranspose_conjTranspose,
      Matrix.l2_opNorm_conjTranspose, hLL] at hn
    nlinarith
  have hsqrt : 0 < Real.sqrt gamma := Real.sqrt_pos.2 hgamma
  have hinvsq : ((Real.sqrt gamma)⁻¹) ^ 2 = gamma⁻¹ := by
    rw [inv_pow, pow_two, Real.mul_self_sqrt hgamma.le]
  refine ⟨hleft, ?_⟩
  nlinarith [norm_nonneg (gramLeftInverse N), inv_pos.mpr hsqrt, hinvsq]

/-- Every orthogonal projection and its complement have operator norm at
most one. -/
theorem orthProj_norm_le_one {P : Matrix H H ℂ}
    (hP : AssemblyRectangularStoppingFront.IsOrthProj P) :
    ‖P‖ ≤ 1 ∧ ‖(1 - P)‖ ≤ 1 := by
  have one_projection (A : Matrix H H ℂ)
      (hA : AssemblyRectangularStoppingFront.IsOrthProj A) : ‖A‖ ≤ 1 := by
    have hnorm := Matrix.l2_opNorm_conjTranspose_mul_self A
    rw [hA.1, hA.2] at hnorm
    nlinarith [norm_nonneg A]
  have hcomp : AssemblyRectangularStoppingFront.IsOrthProj (1 - P) := by
    constructor
    · rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hP.1]
    · simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
        Matrix.mul_one, hP.2]
      abel
  exact ⟨one_projection P hP, one_projection (1 - P) hcomp⟩

/-- Strong range-projection gap estimate.  It is independent of the Gram
difference because range is stable under right-hand conditioning. -/
theorem nuisanceProjection_sub_norm_le
    (NX NY : Matrix H E ℂ) (gamma : ℝ) (hgamma : 0 < gamma)
    (hfloorX : ((NXᴴ * NX) - (gamma : ℂ) • (1 : Matrix E E ℂ)).PosSemidef)
    (hfloorY : ((NYᴴ * NY) - (gamma : ℂ) • (1 : Matrix E E ℂ)).PosSemidef) :
    ‖nuisanceProjection NY - nuisanceProjection NX‖ ≤
      2 * (Real.sqrt gamma)⁻¹ * ‖NY - NX‖ := by
  let PX := nuisanceProjection NX
  let PY := nuisanceProjection NY
  let LX := gramLeftInverse NX
  let LY := gramLeftInverse NY
  have hPX := nuisanceProjection_isOrthProj NX
  have hPY := nuisanceProjection_isOrthProj NY
  have hPX' : AssemblyRectangularStoppingFront.IsOrthProj PX := by simpa [PX] using hPX
  have hPY' : AssemblyRectangularStoppingFront.IsOrthProj PY := by simpa [PY] using hPY
  have hLX := gramLeftInverse_certificate NX gamma hgamma hfloorX
  have hLY := gramLeftInverse_certificate NY gamma hgamma hfloorY
  have hPXform : PX = NX * LX := by
    simp [PX, LX, nuisanceProjection, nuisanceGramPinv, gramLeftInverse]
    rw [Matrix.mul_assoc]
  have hPYform : PY = NY * LY := by
    simp [PY, LY, nuisanceProjection, nuisanceGramPinv, gramLeftInverse]
    rw [Matrix.mul_assoc]
  have hPXN : PX * NX = NX := nuisanceProjection_mul_self NX
  have hPYN : PY * NY = NY := nuisanceProjection_mul_self NY
  have hsplit : PY - PX = (PY - PX) * PX + (PY - PX) * (1 - PX) := by
    rw [Matrix.mul_sub, Matrix.mul_one]
    abel
  have hfirst : (PY - PX) * PX = (PY - 1) * (NX - NY) * LX := by
    rw [hPXform]
    simp only [Matrix.mul_assoc, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.one_mul, hPY'.2, hPYN]
    rw [← Matrix.mul_assoc LX NX LX, hLX.1, Matrix.one_mul]
    abel
  have hsecondStar : ((PY - PX) * (1 - PX))ᴴ =
      (1 - PX) * (NY - NX) * LY := by
    rw [Matrix.conjTranspose_mul]
    rw [show (1 - PX)ᴴ = 1 - PX by
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPX'.1]]
    rw [show (PY - PX)ᴴ = PY - PX by
      rw [Matrix.conjTranspose_sub, hPY'.1, hPX'.1]]
    rw [hPYform]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      Matrix.one_mul, Matrix.mul_assoc, hPX'.2, hPXN]
    abel
  have hnormFirst : ‖(PY - PX) * PX‖ ≤
      (Real.sqrt gamma)⁻¹ * ‖NY - NX‖ := by
    rw [hfirst]
    have hpynorm : ‖PY - 1‖ ≤ 1 := by
      rw [show PY - 1 = -(1 - PY) by abel, norm_neg]
      exact (orthProj_norm_le_one hPY).2
    calc
      ‖(PY - 1) * (NX - NY) * LX‖
          ≤ ‖PY - 1‖ * ‖NX - NY‖ * ‖LX‖ := by
            exact le_trans (Matrix.l2_opNorm_mul _ _)
              (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _)
                (norm_nonneg _))
      _ ≤ 1 * ‖NY - NX‖ * (Real.sqrt gamma)⁻¹ := by
        have hrev : ‖NX - NY‖ = ‖NY - NX‖ := norm_sub_rev _ _
        exact mul_le_mul
          (mul_le_mul hpynorm hrev.le (norm_nonneg _) zero_le_one)
          hLX.2 (norm_nonneg _) (mul_nonneg zero_le_one (norm_nonneg _))
      _ = (Real.sqrt gamma)⁻¹ * ‖NY - NX‖ := by ring
  have hnormSecond : ‖(PY - PX) * (1 - PX)‖ ≤
      (Real.sqrt gamma)⁻¹ * ‖NY - NX‖ := by
    rw [← Matrix.l2_opNorm_conjTranspose,
      hsecondStar]
    calc
      ‖(1 - PX) * (NY - NX) * LY‖
          ≤ ‖1 - PX‖ * ‖NY - NX‖ * ‖LY‖ := by
            exact le_trans (Matrix.l2_opNorm_mul _ _)
              (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _)
                (norm_nonneg _))
      _ ≤ 1 * ‖NY - NX‖ * (Real.sqrt gamma)⁻¹ := by
        exact mul_le_mul
          (mul_le_mul (orthProj_norm_le_one hPX').2 le_rfl
            (norm_nonneg _) zero_le_one)
          hLY.2 (norm_nonneg _) (mul_nonneg zero_le_one (norm_nonneg _))
      _ = (Real.sqrt gamma)⁻¹ * ‖NY - NX‖ := by ring
  rw [hsplit]
  calc
    ‖(PY - PX) * PX + (PY - PX) * (1 - PX)‖
        ≤ ‖(PY - PX) * PX‖ + ‖(PY - PX) * (1 - PX)‖ := norm_add_le _ _
    _ ≤ 2 * (Real.sqrt gamma)⁻¹ * ‖NY - NX‖ := by
      nlinarith

/-- The two boxed estimates of `thm:SMOS-Ward-short-transport`. -/
theorem smos_Ward_short_transport
    (NX NY : Matrix H E ℂ) (YX YY : Matrix H K ℂ)
    (gamma MN MY : ℝ) (hgamma : 0 < gamma)
    (hMN : 0 ≤ MN) (hMY : 0 ≤ MY)
    (hfloorX : ((NXᴴ * NX) - (gamma : ℂ) • (1 : Matrix E E ℂ)).PosSemidef)
    (hfloorY : ((NYᴴ * NY) - (gamma : ℂ) • (1 : Matrix E E ℂ)).PosSemidef)
    (hNX : ‖NX‖ ≤ MN) (hNY : ‖NY‖ ≤ MN) (hYX : ‖YX‖ ≤ MY) :
    let epsilonN := ‖NY - NX‖
    let epsilonG := ‖NYᴴ * NY - NXᴴ * NX‖
    let epsilonY := ‖YY - YX‖
    ‖nuisanceProjection NY - nuisanceProjection NX‖ ≤
        2 * (Real.sqrt gamma)⁻¹ * epsilonN +
          MN * ((Real.sqrt gamma)⁻¹) ^ 3 * epsilonG
      ∧ ‖(1 - nuisanceProjection NY) * YY -
          (1 - nuisanceProjection NX) * YX‖ ≤
        epsilonY + MY * ‖nuisanceProjection NY - nuisanceProjection NX‖ := by
  dsimp only
  have hproj := nuisanceProjection_sub_norm_le NX NY gamma hgamma hfloorX hfloorY
  constructor
  · have hextra : 0 ≤ MN * ((Real.sqrt gamma)⁻¹) ^ 3 *
        ‖NYᴴ * NY - NXᴴ * NX‖ := by positivity
    linarith
  · let PX := nuisanceProjection NX
    let PY := nuisanceProjection NY
    have hPY := nuisanceProjection_isOrthProj NY
    have hdecomp : (1 - PY) * YY - (1 - PX) * YX =
        (1 - PY) * (YY - YX) + (PX - PY) * YX := by
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.one_mul]
      abel
    rw [hdecomp]
    calc
      ‖(1 - PY) * (YY - YX) + (PX - PY) * YX‖
          ≤ ‖(1 - PY) * (YY - YX)‖ + ‖(PX - PY) * YX‖ := norm_add_le _ _
      _ ≤ ‖1 - PY‖ * ‖YY - YX‖ + ‖PX - PY‖ * ‖YX‖ := by
        gcongr <;> apply Matrix.l2_opNorm_mul
      _ ≤ 1 * ‖YY - YX‖ + ‖PY - PX‖ * MY := by
        rw [norm_sub_rev PX PY]
        gcongr
        exact (orthProj_norm_le_one hPY).2
      _ = ‖YY - YX‖ + MY * ‖PY - PX‖ := by ring

/-- Gram differences obey the telescoping estimate used for the final Cauchy
conclusion in the manuscript. -/
theorem gram_sub_norm_le (A B : Matrix H K ℂ) :
    ‖Aᴴ * A - Bᴴ * B‖ ≤ (‖A‖ + ‖B‖) * ‖A - B‖ := by
  have htel : Aᴴ * A - Bᴴ * B = Aᴴ * (A - B) + (Aᴴ - Bᴴ) * B := by
    simp only [Matrix.mul_sub, Matrix.sub_mul]
    abel
  rw [htel]
  calc
    ‖Aᴴ * (A - B) + (Aᴴ - Bᴴ) * B‖
        ≤ ‖Aᴴ * (A - B)‖ + ‖(Aᴴ - Bᴴ) * B‖ := norm_add_le _ _
    _ ≤ ‖Aᴴ‖ * ‖A - B‖ + ‖Aᴴ - Bᴴ‖ * ‖B‖ := by
      gcongr <;> apply Matrix.l2_opNorm_mul
    _ = (‖A‖ + ‖B‖) * ‖A - B‖ := by
      rw [Matrix.l2_opNorm_conjTranspose]
      rw [← Matrix.conjTranspose_sub, Matrix.l2_opNorm_conjTranspose]
      ring

end SMOSWardShortTransportExact
end NCG
