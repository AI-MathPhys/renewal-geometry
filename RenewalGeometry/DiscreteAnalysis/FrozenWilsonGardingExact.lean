/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import RenewalGeometry.DiscreteAnalysis.LatticeTorusPlancherel
import RenewalGeometry.DiscreteAnalysis.FrozenWilsonSymbolExact

/-!
# Frozen discrete Gårding estimate on the lattice torus

Paper `predictive_spectral_geometry`, label `thm:supp-general-Wilson-ellipticity`, the
frozen-coefficient case of the uniform graph estimate `eq:supp-general-Garding`.

On the periodic lattice torus `(ℤ/nℤ)^d` (mesh `h`), the constant-coefficient doubled Wilson
operator `D̃ = ½ Σ_j (M_{ĉ^j} P_j + P_j M_{ĉ^j}) + ϖ Γ_⊥ W` (`frozenWilson`) is diagonalised by the
discrete Fourier transform of `LatticeTorusPlancherel`: on the mode `ℓ` it acts by the frozen
symbol `q_h(θ_ℓ)` with `θ_ℓ = 2πℓ/n` (`dftVec_frozenWilson`), and the forward differences
`h⁻¹(S_j - I)` act by `h⁻¹(e^{iθ_j} - 1)` (`dftVec_forwardDifference`).  Since the symbol is
Hermitian with `q² = scalar · I` (`frozenSymbol_sq`) and the scalar dominates
`ℓ_h(θ) = 2h⁻² Σ_j (1 - cos θ_j) = Σ_j |h⁻¹(e^{iθ_j} - 1)|²` (`frozenSymbolScalar_bounds`),
Parseval gives the **frozen Gårding estimate**

`Σ_j ‖h⁻¹(S_j - I) u‖_h² ≤ min(λ, ϖ²)⁻¹ ‖D̃ u‖_h²`, hence
`‖u‖_{1,h}² ≤ max(1, min(λ, ϖ²)⁻¹) (‖D̃ u‖_h² + ‖u‖_h²)` (`h1NormSq_le`, `eq:discrete-H1-norm`),

uniformly in the mesh and cutoff-free.  The variable-coefficient estimate (partition of unity,
`eq:local-cutoff-commutator`, absorption of the modulus of continuity) is not treated here.
-/

open Finset Matrix ZMod ComplexConjugate
open RenewalGeometry.LatticeTorusPlancherel RenewalGeometry.FrozenWilsonSymbol

namespace RenewalGeometry.FrozenWilsonGarding

variable {d n N : ℕ} [NeZero n]

/-- Sections of the lattice torus with values in the doubled spin module `ℂ^N`. -/
abbrev TorusSection (d n N : ℕ) := Grid d n → (Fin N → ℂ)

/-! ### The frozen operators on the torus -/

/-- The symmetric difference `P_j = (S_j - S_j^*) / (2ih)`. -/
noncomputable def symmetricDifference (h : ℝ) (j : Fin d) (u : TorusSection d n N) :
    TorusSection d n N :=
  fun x => (2 * Complex.I * (h : ℂ))⁻¹ • (shift j u x - shiftAdj j u x)

/-- The Wilson term `W = (1/2h) Σ_j (2 - S_j - S_j^*)`. -/
noncomputable def wilsonTerm (h : ℝ) (u : TorusSection d n N) : TorusSection d n N :=
  fun x => (2 * (h : ℂ))⁻¹ • ∑ j, ((2 : ℂ) • u x - shift j u x - shiftAdj j u x)

/-- Pointwise multiplication by a constant matrix. -/
def matMul (M : Matrix (Fin N) (Fin N) ℂ) (u : TorusSection d n N) : TorusSection d n N :=
  fun x => M *ᵥ u x

/-- The frozen doubled Wilson operator `½ Σ_j (M_{ĉ^j} P_j + P_j M_{ĉ^j}) + ϖ Γ_⊥ W` on the torus. -/
noncomputable def frozenWilson (h ϖ : ℝ) (c : Fin d → Matrix (Fin N) (Fin N) ℂ)
    (Γ : Matrix (Fin N) (Fin N) ℂ) (u : TorusSection d n N) : TorusSection d n N :=
  fun x => (2 : ℂ)⁻¹ • ∑ j, (matMul (c j) (symmetricDifference h j u) x +
      symmetricDifference h j (matMul (c j) u) x) +
    (ϖ : ℂ) • matMul Γ (wilsonTerm h u) x

/-- The forward difference `h⁻¹ (S_j - I)`. -/
noncomputable def forwardDifference (h : ℝ) (j : Fin d) (u : TorusSection d n N) :
    TorusSection d n N :=
  fun x => (h : ℂ)⁻¹ • (shift j u x - u x)

/-- The discrete `ℓ²` norm squared with cell weight `h^d`. -/
noncomputable def gridNormSq (h : ℝ) (u : TorusSection d n N) : ℝ :=
  h ^ d * ∑ x, euclNormSq (u x)

/-- The discrete `H¹` norm squared of `eq:discrete-H1-norm`:
`‖u‖²_{1,h} = ‖u‖_h² + Σ_j ‖h⁻¹(S_j - I)u‖_h²`. -/
noncomputable def h1NormSq (h : ℝ) (u : TorusSection d n N) : ℝ :=
  gridNormSq h u + ∑ j, gridNormSq h (forwardDifference h j u)

/-- The Brillouin angle `θ_ℓ = 2π ℓ / n` of the mode `ℓ`. -/
noncomputable def angle (ℓ : Grid d n) : Fin d → ℝ := fun j => 2 * Real.pi * ((ℓ j).val : ℝ) / n

/-! ### Characters as exponentials -/

theorem stdAddChar_eq_exp (a : ZMod n) :
    stdAddChar a = Complex.exp (Complex.I * ((2 * Real.pi * (a.val : ℝ) / n : ℝ) : ℂ)) := by
  conv_lhs => rw [← ZMod.natCast_zmod_val a]
  rw [← Int.cast_natCast, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  ring

theorem conj_exp_I_mul (θ : ℝ) :
    conj (Complex.exp (Complex.I * (θ : ℂ))) = Complex.exp (-(Complex.I * (θ : ℂ))) := by
  rw [← Complex.exp_conj]
  congr 1
  simp [Complex.conj_ofReal]

theorem stdAddChar_angle (ℓ : Grid d n) (j : Fin d) :
    stdAddChar (ℓ j) = Complex.exp (Complex.I * ((angle ℓ j : ℝ) : ℂ)) :=
  stdAddChar_eq_exp (ℓ j)

/-- `|e^{iθ} - 1|² = 2(1 - cos θ)`. -/
theorem norm_exp_I_mul_sub_one_sq (θ : ℝ) :
    ‖Complex.exp (Complex.I * (θ : ℂ)) - 1‖ ^ 2 = 2 * (1 - Real.cos θ) := by
  rw [mul_comm, Complex.exp_mul_I, Complex.sq_norm, ← Complex.ofReal_sin, ← Complex.ofReal_cos]
  have : (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I - 1 =
      ((Real.cos θ - 1 : ℝ) : ℂ) + ((Real.sin θ : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.normSq_add_mul_I]
  nlinarith [Real.sin_sq_add_cos_sq θ]

/-! ### Fourier multipliers -/

theorem dftVec_symmetricDifference (h : ℝ) (hh : h ≠ 0) (j : Fin d) (u : TorusSection d n N)
    (ℓ : Grid d n) :
    dftVec (symmetricDifference h j u) ℓ =
      ((Real.sin (angle ℓ j) / h : ℝ) : ℂ) • dftVec u ℓ := by
  have hsub : symmetricDifference h j u =
      (2 * Complex.I * (h : ℂ))⁻¹ • (shift j u - shiftAdj j u) := by
    funext x; rfl
  rw [hsub, dftVec_smul, dftVec_sub, dftVec_shift, dftVec_shiftAdj, ← sub_smul, smul_smul,
    stdAddChar_angle, conj_exp_I_mul, exp_sub_exp_neg]
  congr 1
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have hh' : (h : ℂ) ≠ 0 := by exact_mod_cast hh
  push_cast
  field_simp

theorem dftVec_wilsonTerm (h : ℝ) (u : TorusSection d n N) (ℓ : Grid d n) :
    dftVec (wilsonTerm h u) ℓ = ((wilsonScalar (angle ℓ) / h : ℝ) : ℂ) • dftVec u ℓ := by
  have hsub : wilsonTerm h u = (2 * (h : ℂ))⁻¹ •
      fun x => ∑ j, ((2 : ℂ) • u x - shift j u x - shiftAdj j u x) := by
    funext x; rfl
  rw [hsub, dftVec_smul, dftVec_sum]
  have hterm : ∀ j : Fin d, dftVec (fun x => (2 : ℂ) • u x - shift j u x - shiftAdj j u x) ℓ =
      (2 * ((1 - Real.cos (angle ℓ j) : ℝ) : ℂ)) • dftVec u ℓ := by
    intro j
    have : (fun x => (2 : ℂ) • u x - shift j u x - shiftAdj j u x) =
        (2 : ℂ) • u - shift j u - shiftAdj j u := by funext x; rfl
    rw [this, dftVec_sub, dftVec_sub, dftVec_smul, dftVec_shift, dftVec_shiftAdj, ← sub_smul,
      ← sub_smul, stdAddChar_angle, conj_exp_I_mul, two_sub_exp_sub_exp_neg]
  simp only [hterm, ← Finset.sum_smul, smul_smul]
  congr 1
  simp only [← Finset.mul_sum, wilsonScalar]
  push_cast
  rcases eq_or_ne h 0 with h0 | h0
  · simp [h0]
  · field_simp

theorem dftVec_matMul' (M : Matrix (Fin N) (Fin N) ℂ) (u : TorusSection d n N) (ℓ : Grid d n) :
    dftVec (matMul M u) ℓ = M *ᵥ dftVec u ℓ :=
  dftVec_matMul M u ℓ

/-- **The frozen Wilson operator is the Fourier multiplier by the frozen symbol.** -/
theorem dftVec_frozenWilson (h ϖ : ℝ) (hh : h ≠ 0) (c : Fin d → Matrix (Fin N) (Fin N) ℂ)
    (Γ : Matrix (Fin N) (Fin N) ℂ) (u : TorusSection d n N) (ℓ : Grid d n) :
    dftVec (frozenWilson h ϖ c Γ u) ℓ = frozenSymbol h ϖ c Γ (angle ℓ) *ᵥ dftVec u ℓ := by
  have hsub : frozenWilson h ϖ c Γ u =
      (2 : ℂ)⁻¹ • (fun x => ∑ j, (matMul (c j) (symmetricDifference h j u) x +
        symmetricDifference h j (matMul (c j) u) x)) +
      (ϖ : ℂ) • matMul Γ (wilsonTerm h u) := by
    funext x; rfl
  rw [hsub, dftVec_add, dftVec_smul, dftVec_smul, dftVec_sum, dftVec_matMul', dftVec_wilsonTerm]
  have hterm : ∀ j : Fin d, dftVec (fun x => matMul (c j) (symmetricDifference h j u) x +
      symmetricDifference h j (matMul (c j) u) x) ℓ =
      (2 : ℂ) • (((Real.sin (angle ℓ j) / h : ℝ) : ℂ) • (c j *ᵥ dftVec u ℓ)) := by
    intro j
    have : (fun x => matMul (c j) (symmetricDifference h j u) x +
        symmetricDifference h j (matMul (c j) u) x) =
        matMul (c j) (symmetricDifference h j u) + symmetricDifference h j (matMul (c j) u) := by
      funext x; rfl
    rw [this, dftVec_add, dftVec_matMul', dftVec_symmetricDifference h hh,
      dftVec_symmetricDifference h hh, dftVec_matMul', Matrix.mulVec_smul, two_smul]
  simp only [hterm]
  unfold frozenSymbol
  simp only [Matrix.mulVec_smul, Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.sum_mulVec,
    Finset.smul_sum, smul_add, smul_smul]
  have hh' : (h : ℂ) ≠ 0 := by exact_mod_cast hh
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    push_cast
    field_simp
  · congr 1
    push_cast
    field_simp
    try ring

theorem dftVec_forwardDifference (h : ℝ) (j : Fin d) (u : TorusSection d n N) (ℓ : Grid d n) :
    dftVec (forwardDifference h j u) ℓ =
      ((h : ℂ)⁻¹ * (Complex.exp (Complex.I * ((angle ℓ j : ℝ) : ℂ)) - 1)) • dftVec u ℓ := by
  have hsub : forwardDifference h j u = (h : ℂ)⁻¹ • (shift j u - u) := by funext x; rfl
  rw [hsub, dftVec_smul, dftVec_sub, dftVec_shift, stdAddChar_angle, mul_smul, sub_smul,
    one_smul]

/-! ### Norms of multipliers -/

/-- `‖q v‖² = s ‖v‖²` for a Hermitian matrix with `q² = s I`. -/
theorem euclNormSq_mulVec_eq (q : Matrix (Fin N) (Fin N) ℂ) (hq : qᴴ = q) (s : ℝ)
    (hs : q * q = ((s : ℝ) : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ)) (v : Fin N → ℂ) :
    euclNormSq (q *ᵥ v) = s * euclNormSq v := by
  have key : ∀ w : Fin N → ℂ, ((euclNormSq w : ℝ) : ℂ) = star w ⬝ᵥ w := by
    intro w
    simp only [euclNormSq, dotProduct, Pi.star_apply, Complex.star_def]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Complex.ofReal_pow, Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
  apply Complex.ofReal_injective
  push_cast
  rw [key, key, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, hq, hs, smul_mulVec,
    one_mulVec, dotProduct_smul, smul_eq_mul]

/-- The frozen symbol is Hermitian when the Clifford coefficients and `Γ_⊥` are. -/
theorem frozenSymbol_conjTranspose (h ϖ : ℝ) (c : Fin d → Matrix (Fin N) (Fin N) ℂ)
    (Γ : Matrix (Fin N) (Fin N) ℂ) (hherm : ∀ j, (c j)ᴴ = c j) (hΓ : Γᴴ = Γ) (θ : Fin d → ℝ) :
    (frozenSymbol h ϖ c Γ θ)ᴴ = frozenSymbol h ϖ c Γ θ := by
  unfold frozenSymbol
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_sum,
    Complex.star_def, map_inv₀, Complex.conj_ofReal, hherm, hΓ]

/-! ### The frozen Gårding estimate -/

theorem sum_euclNormSq_eq (u : TorusSection d n N) :
    ∑ x, euclNormSq (u x) = (n : ℝ) ^ d * ∑ ℓ, euclNormSq (dftVec u ℓ) := by
  have hn : ((n : ℝ) ^ d) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne n))
  rw [sum_euclNormSq_dftVec, ← mul_assoc, mul_inv_cancel₀ hn, one_mul]

/-- **Forward differences in Fourier space**:
`Σ_j ‖h⁻¹(S_j - I) u‖_h² = h^d n^d Σ_ℓ ℓ_h(θ_ℓ) |û(ℓ)|²` with `ℓ_h(θ) = 2h⁻² s(θ)`. -/
theorem sum_gridNormSq_forwardDifference (h : ℝ) (hh : 0 < h) (u : TorusSection d n N) :
    ∑ j, gridNormSq h (forwardDifference h j u) =
      h ^ d * (n : ℝ) ^ d * ∑ ℓ, (2 * (h ^ 2)⁻¹ * wilsonScalar (angle ℓ)) *
        euclNormSq (dftVec u ℓ) := by
  have hmode : ∀ (j : Fin d) (ℓ : Grid d n), euclNormSq (dftVec (forwardDifference h j u) ℓ) =
      ((h ^ 2)⁻¹ * (2 * (1 - Real.cos (angle ℓ j)))) * euclNormSq (dftVec u ℓ) := by
    intro j ℓ
    rw [dftVec_forwardDifference, euclNormSq_smul, norm_mul, mul_pow, norm_inv,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hh, inv_pow, norm_exp_I_mul_sub_one_sq]
  calc ∑ j, gridNormSq h (forwardDifference h j u)
      = ∑ j, h ^ d * ((n : ℝ) ^ d * ∑ ℓ, ((h ^ 2)⁻¹ * (2 * (1 - Real.cos (angle ℓ j)))) *
          euclNormSq (dftVec u ℓ)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [gridNormSq, sum_euclNormSq_eq]
        congr 2
        exact Finset.sum_congr rfl fun ℓ _ => hmode j ℓ
    _ = h ^ d * ((n : ℝ) ^ d * ∑ j, ∑ ℓ, ((h ^ 2)⁻¹ * (2 * (1 - Real.cos (angle ℓ j)))) *
          euclNormSq (dftVec u ℓ)) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum]
    _ = h ^ d * (n : ℝ) ^ d * ∑ ℓ, (2 * (h ^ 2)⁻¹ * wilsonScalar (angle ℓ)) *
          euclNormSq (dftVec u ℓ) := by
        rw [Finset.sum_comm, mul_assoc]
        congr 2
        refine Finset.sum_congr rfl fun ℓ _ => ?_
        rw [← Finset.sum_mul, wilsonScalar, Finset.mul_sum]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        ring

/-- **The frozen operator in Fourier space**:
`‖D̃ u‖_h² = h^d n^d Σ_ℓ scalar(θ_ℓ) |û(ℓ)|²` (Hermitian Clifford data). -/
theorem gridNormSq_frozenWilson (h ϖ : ℝ) (hh : h ≠ 0) (c : Fin d → Matrix (Fin N) (Fin N) ℂ)
    (Γ : Matrix (Fin N) (Fin N) ℂ) (g : Matrix (Fin d) (Fin d) ℝ) (hc : DoubledCliffordData c Γ g)
    (hherm : ∀ j, (c j)ᴴ = c j) (hΓ : Γᴴ = Γ) (u : TorusSection d n N) :
    gridNormSq h (frozenWilson h ϖ c Γ u) =
      h ^ d * (n : ℝ) ^ d * ∑ ℓ, frozenSymbolScalar h ϖ g (angle ℓ) * euclNormSq (dftVec u ℓ) := by
  have hmode : ∀ ℓ : Grid d n, euclNormSq (dftVec (frozenWilson h ϖ c Γ u) ℓ) =
      frozenSymbolScalar h ϖ g (angle ℓ) * euclNormSq (dftVec u ℓ) := by
    intro ℓ
    rw [dftVec_frozenWilson h ϖ hh]
    exact euclNormSq_mulVec_eq _ (frozenSymbol_conjTranspose h ϖ c Γ hherm hΓ _) _
      (frozenSymbol_sq h ϖ c Γ g hc _) _
  rw [gridNormSq, sum_euclNormSq_eq, ← mul_assoc]
  congr 1
  exact Finset.sum_congr rfl fun ℓ _ => hmode ℓ

/-- **Frozen Gårding estimate** (`eq:supp-general-Garding`, constant coefficients): for
Hermitian Clifford data with `λ|ξ|² ≤ ξᵀ g ξ ≤ Λ|ξ|²`, `λ > 0`, `ϖ ≠ 0`,
`Σ_j ‖h⁻¹(S_j - I) u‖_h² ≤ min(λ, ϖ²)⁻¹ ‖D̃ u‖_h²`, uniformly in `h` and `n`. -/
theorem sum_gridNormSq_forwardDifference_le (h ϖ lam Lam : ℝ) (hh : 0 < h) (hlam : 0 < lam)
    (hϖ : ϖ ≠ 0) (hLam : 0 ≤ Lam) (c : Fin d → Matrix (Fin N) (Fin N) ℂ)
    (Γ : Matrix (Fin N) (Fin N) ℂ) (g : Matrix (Fin d) (Fin d) ℝ) (hc : DoubledCliffordData c Γ g)
    (hherm : ∀ j, (c j)ᴴ = c j) (hΓ : Γᴴ = Γ)
    (hlow : ∀ ξ : Fin d → ℝ, lam * ∑ j, ξ j ^ 2 ≤ ∑ j, ∑ k, g j k * (ξ j * ξ k))
    (hup : ∀ ξ : Fin d → ℝ, ∑ j, ∑ k, g j k * (ξ j * ξ k) ≤ Lam * ∑ j, ξ j ^ 2)
    (u : TorusSection d n N) :
    ∑ j, gridNormSq h (forwardDifference h j u) ≤
      (min lam (ϖ ^ 2))⁻¹ * gridNormSq h (frozenWilson h ϖ c Γ u) := by
  have hmin : 0 < min lam (ϖ ^ 2) := lt_min hlam (by positivity)
  have hcoef : 0 ≤ h ^ d * (n : ℝ) ^ d := by positivity
  rw [sum_gridNormSq_forwardDifference h hh, gridNormSq_frozenWilson h ϖ hh.ne' c Γ g hc hherm hΓ]
  calc h ^ d * (n : ℝ) ^ d * ∑ ℓ, (2 * (h ^ 2)⁻¹ * wilsonScalar (angle ℓ)) *
        euclNormSq (dftVec u ℓ)
      ≤ h ^ d * (n : ℝ) ^ d * ∑ ℓ, (min lam (ϖ ^ 2))⁻¹ *
        (frozenSymbolScalar h ϖ g (angle ℓ) * euclNormSq (dftVec u ℓ)) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun ℓ _ => ?_) hcoef
        have hb := (frozenSymbolScalar_bounds h ϖ lam Lam hh.ne' hlam.le hLam g hlow hup
          (angle ℓ)).1
        rw [← mul_assoc]
        refine mul_le_mul_of_nonneg_right ?_ (euclNormSq_nonneg _)
        rw [← div_eq_inv_mul, le_div_iff₀ hmin, mul_comm _ (min lam (ϖ ^ 2))]
        exact hb
    _ = (min lam (ϖ ^ 2))⁻¹ * (h ^ d * (n : ℝ) ^ d * ∑ ℓ, frozenSymbolScalar h ϖ g (angle ℓ) *
        euclNormSq (dftVec u ℓ)) := by
        rw [← Finset.mul_sum]
        ring

/-- **`eq:supp-general-Garding`, frozen case**: `‖u‖²_{1,h} ≤ C (‖D̃ u‖_h² + ‖u‖_h²)` with
`C = max 1 (min(λ, ϖ²)⁻¹)`, cutoff-independent and uniform in the mesh. -/
theorem h1NormSq_le (h ϖ lam Lam : ℝ) (hh : 0 < h) (hlam : 0 < lam)
    (hϖ : ϖ ≠ 0) (hLam : 0 ≤ Lam) (c : Fin d → Matrix (Fin N) (Fin N) ℂ)
    (Γ : Matrix (Fin N) (Fin N) ℂ) (g : Matrix (Fin d) (Fin d) ℝ) (hc : DoubledCliffordData c Γ g)
    (hherm : ∀ j, (c j)ᴴ = c j) (hΓ : Γᴴ = Γ)
    (hlow : ∀ ξ : Fin d → ℝ, lam * ∑ j, ξ j ^ 2 ≤ ∑ j, ∑ k, g j k * (ξ j * ξ k))
    (hup : ∀ ξ : Fin d → ℝ, ∑ j, ∑ k, g j k * (ξ j * ξ k) ≤ Lam * ∑ j, ξ j ^ 2)
    (u : TorusSection d n N) :
    h1NormSq h u ≤ max 1 (min lam (ϖ ^ 2))⁻¹ *
      (gridNormSq h (frozenWilson h ϖ c Γ u) + gridNormSq h u) := by
  have h1 := sum_gridNormSq_forwardDifference_le h ϖ lam Lam hh hlam hϖ hLam c Γ g hc hherm hΓ
    hlow hup u
  have hD : 0 ≤ gridNormSq h (frozenWilson h ϖ c Γ u) :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => euclNormSq_nonneg _)
  have hu : 0 ≤ gridNormSq h u :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => euclNormSq_nonneg _)
  have hm1 : (1 : ℝ) ≤ max 1 (min lam (ϖ ^ 2))⁻¹ := le_max_left _ _
  have hm2 : (min lam (ϖ ^ 2))⁻¹ ≤ max 1 (min lam (ϖ ^ 2))⁻¹ := le_max_right _ _
  unfold h1NormSq
  calc gridNormSq h u + ∑ j, gridNormSq h (forwardDifference h j u)
      ≤ gridNormSq h u + (min lam (ϖ ^ 2))⁻¹ * gridNormSq h (frozenWilson h ϖ c Γ u) := by
        linarith
    _ ≤ max 1 (min lam (ϖ ^ 2))⁻¹ * gridNormSq h u +
        max 1 (min lam (ϖ ^ 2))⁻¹ * gridNormSq h (frozenWilson h ϖ c Γ u) := by
        gcongr
        · linarith [mul_le_mul_of_nonneg_right hm1 hu]
    _ = max 1 (min lam (ϖ ^ 2))⁻¹ *
        (gridNormSq h (frozenWilson h ϖ c Γ u) + gridNormSq h u) := by ring

end RenewalGeometry.FrozenWilsonGarding
