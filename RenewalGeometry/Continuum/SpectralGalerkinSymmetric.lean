/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Continuum.SpectralGalerkinMidpoint

/-!
# Spectral Galerkin generators of constant-coefficient symmetric hyperbolic systems

A concrete instance (non-vacuity) of the abstract energy hypothesis of
`Continuum/SpectralGalerkinMidpoint.lean` for `thm:generated-dynamics` (Einstein–Standard-Model
action-closure manuscript): the Fourier–Galerkin truncation of a symmetric hyperbolic system
`U_t = Σ_j A^j ∂_j U + b U` on `𝕋^d` with constant Hermitian `A^j ∈ ℂ^{m×m}` and `b ∈ ℂ`.  On a finite
mode set `S ⊂ ℤ^d` (e.g. the box `|n|_∞ ≤ N`) the state is the coefficient vector
`(Û(n))_{n ∈ S} ∈ ℂ^{m × S}` (Euclidean norm = `L²` norm; for constant coefficients the weights
`W_q(n)^{1/2}` commute with the generator, so the same computation is the `H^q` one) and the
generator is the block-diagonal matrix `i ⊕_n (Σ_j 2π n_j A^j) + b`.

* `symb_isHermitian`, `genMat`, `genL`.
* **`re_inner_genL`**: `Re ⟪G_S v, v⟫ = Re(b) ‖v‖²` for every mode set `S`: the principal part is
  skew-adjoint (Hermitian symbol times `i`), so the energy constant `K = max(0, Re b)` is independent
  of the cutoff, while `‖G_S‖` grows with the frequencies in `S` (the CFL constant).
* **`const_sym_midpoint`**: for every cutoff, the implicit-midpoint recursion of
  `SpectralGalerkin.midpoint_recursion` exists on `[0, T]` with the cutoff-independent bound
  `‖U^j‖ ≤ R` under the CFL condition `τ ‖G_S‖ < 2`.
-/

open Matrix WithLp

namespace RenewalGeometry.SpectralGalerkin.ConstSym

noncomputable section

variable {d m : ℕ}

/-- The Fourier symbol `Σ_j 2π n_j A^j` (so that `Σ_j A^j ∂_j e_n = i symb(n) e_n`). -/
def symb (A : Fin d → Matrix (Fin m) (Fin m) ℂ) (n : Fin d → ℤ) : Matrix (Fin m) (Fin m) ℂ :=
  ∑ j, (((2 * Real.pi * n j : ℝ) : ℂ)) • A j

theorem symb_isHermitian {A : Fin d → Matrix (Fin m) (Fin m) ℂ} (hA : ∀ j, (A j).IsHermitian)
    (n : Fin d → ℤ) : (symb A n).IsHermitian := by
  unfold symb
  refine Finset.sum_induction _ IsHermitian (fun _ _ h1 h2 => h1.add h2) isHermitian_zero
    fun j _ => (hA j).smul ?_
  rw [isSelfAdjoint_iff, Complex.star_def, Complex.conj_ofReal]

/-- The Galerkin generator on the mode set `S`: `i ⊕_{n ∈ S} symb(n) + b`. -/
def genMat (A : Fin d → Matrix (Fin m) (Fin m) ℂ) (b : ℂ) (S : Finset (Fin d → ℤ)) :
    Matrix (Fin m × S) (Fin m × S) ℂ :=
  Complex.I • blockDiagonal (fun n : S => symb A n.1) + b • 1

/-- The generator as a continuous linear map on `ℂ^{m × S}`. -/
def genL (A : Fin d → Matrix (Fin m) (Fin m) ℂ) (b : ℂ) (S : Finset (Fin d → ℤ)) :
    EuclideanSpace ℂ (Fin m × S) →L[ℂ] EuclideanSpace ℂ (Fin m × S) :=
  toEuclideanCLM (n := Fin m × S) (𝕜 := ℂ) (genMat A b S)

/-- **The energy identity of the symmetric Galerkin generator**: `Re ⟪G_S v, v⟫ = Re(b) ‖v‖²`,
for every mode set `S`. -/
theorem re_inner_genL {A : Fin d → Matrix (Fin m) (Fin m) ℂ} (hA : ∀ j, (A j).IsHermitian)
    (b : ℂ) (S : Finset (Fin d → ℤ)) (v : EuclideanSpace ℂ (Fin m × S)) :
    RCLike.re (inner ℂ (genL A b S v) v) = b.re * ‖v‖ ^ 2 := by
  set H := blockDiagonal (fun n : S => symb A n.1) with hH
  have hHerm : H.IsHermitian := isHermitian_blockDiagonal_iff.mpr fun n => symb_isHermitian hA n.1
  have him := hHerm.im_star_dotProduct_mulVec_self (ofLp v)
  have hvv : inner ℂ v v = star (ofLp v) ⬝ᵥ ofLp v := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  have hre : (star (ofLp v) ⬝ᵥ ofLp v).re = ‖v‖ ^ 2 := by
    rw [← hvv]; exact inner_self_eq_norm_sq (𝕜 := ℂ) v
  have him0 : (star (ofLp v) ⬝ᵥ ofLp v).im = 0 := by
    rw [← hvv]; exact inner_self_im (𝕜 := ℂ) v
  rw [inner_re_symm, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  simp only [genL, ofLp_toEuclideanCLM, genMat, add_mulVec, smul_mulVec, one_mulVec,
    dotProduct_add, dotProduct_smul, smul_eq_mul]
  rw [← hH]
  have him' : (star (ofLp v) ⬝ᵥ H *ᵥ ofLp v).im = 0 := by simpa using him
  simp only [RCLike.re_to_complex, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    him', hre, him0]
  ring

/-- The energy bound in the form of the abstract hypothesis, `K = max(0, Re b)`. -/
theorem re_inner_genL_le {A : Fin d → Matrix (Fin m) (Fin m) ℂ} (hA : ∀ j, (A j).IsHermitian)
    (b : ℂ) (S : Finset (Fin d → ℤ)) (v : EuclideanSpace ℂ (Fin m × S)) :
    RCLike.re (inner ℂ (genL A b S v) v) ≤ max 0 b.re * (1 + ‖v‖ ^ 2) := by
  rw [re_inner_genL hA]
  have h1 : b.re ≤ max 0 b.re := le_max_right _ _
  have h0 : 0 ≤ max 0 b.re := le_max_left _ _
  have := sq_nonneg ‖v‖
  nlinarith

/-- The real inner product structure of `ℂ^{m × S}` (`⟪x, y⟫_ℝ = Re ⟪x, y⟫_ℂ`). -/
local instance instRealInner (ι : Type*) [Fintype ι] :
    InnerProductSpace ℝ (EuclideanSpace ℂ ι) :=
  InnerProductSpace.rclikeToReal ℂ _

/-- **The implicit-midpoint recursion for the symmetric Galerkin system**, with a bound independent
of the cutoff: for every finite mode set `S`, under the CFL condition `τ ‖G_S‖ < 2`,
`τ ‖G_S‖ 2R ≤ R` and `τ max(0, Re b) ≤ 1/2`, and data with
`e^{4 max(0, Re b) T}(1 + ‖U⁰‖²) ≤ 1 + R²`, the recursion `U^{j+1} = U^j + τ G_S((U^j + U^{j+1})/2)`
exists for `jτ ≤ T` with `‖U^j‖ ≤ R`. -/
theorem const_sym_midpoint {A : Fin d → Matrix (Fin m) (Fin m) ℂ} (hA : ∀ j, (A j).IsHermitian)
    (b : ℂ) (S : Finset (Fin d → ℤ)) {τ R T : ℝ} (hτ : 0 ≤ τ) (hR : 0 ≤ R)
    (hcfl : τ * ‖genL A b S‖ < 2) (hτM : τ * (‖genL A b S‖ * (2 * R)) ≤ R)
    (hτK : τ * max 0 b.re ≤ 1 / 2) {U₀ : EuclideanSpace ℂ (Fin m × S)}
    (h0 : Real.exp (4 * max 0 b.re * T) * (1 + ‖U₀‖ ^ 2) ≤ 1 + R ^ 2) :
    ∃ U : ℕ → EuclideanSpace ℂ (Fin m × S), U 0 = U₀ ∧ ∀ j : ℕ, (j : ℝ) * τ ≤ T →
      ‖U j‖ ≤ R ∧ (((j : ℝ) + 1) * τ ≤ T →
        U (j + 1) = U j + τ • genL A b S (mid (U j) (U (j + 1)))) := by
  have hG : ∀ w w' : EuclideanSpace ℂ (Fin m × S),
      ‖genL A b S w - genL A b S w'‖ ≤ ‖genL A b S‖ * ‖w - w'‖ := fun w w' => by
    rw [← map_sub]; exact (genL A b S).le_opNorm _
  obtain ⟨U, hU0, hU⟩ := midpoint_recursion (G := fun w => genL A b S w) (M := ‖genL A b S‖ * (2 * R))
    (L := ‖genL A b S‖) (K := max 0 b.re) hτ (by positivity) (norm_nonneg _) (le_max_left _ _) hR
    (fun w hw => ((genL A b S).le_opNorm w).trans (mul_le_mul_of_nonneg_left hw (norm_nonneg _)))
    (fun w w' _ _ => hG w w')
    (fun w _ => by
      have := re_inner_genL_le hA b S w
      simpa [real_inner_eq_re_inner] using this)
    hτM hcfl hτK h0
  exact ⟨U, hU0, fun j hj => ⟨(hU j hj).1, fun hj1 => ((hU j hj).2.2 hj1).1⟩⟩

end

end RenewalGeometry.SpectralGalerkin.ConstSym
