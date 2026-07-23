/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Frame universality of the nondegenerate flat endpoint

**Theorem `thm:frame-universality`** (repairing the earlier empty
citation): the dilation `U_M ψ(y) = (det V_M)^{1/2} ψ(V_M y)` is
unitary and conjugates the anisotropic Dirac Hamiltonian to the
isotropic one.  The two substantive steps of the manuscript's proof
are formalized here:

* **unitarity** (`NCG.dilation_lintegral_normSq`): the change of
  variables `x = V y` with the Jacobian factor `|det V|` preserves the
  squared-norm integral — for *every* measurable spinor amplitude,
  with no integrability hypothesis, via the Lebesgue `lintegral` and
  Mathlib's `Measure.map (toLin' M) volume = |det M|⁻¹ • volume`;
* **symbol conjugation** (`NCG.dilation_symbol_conjugation`): the
  chain-rule/symmetry identity `A^k (V_M)_{jk} = κ A^k M^{kj}` — the
  anisotropic symbol at `ξ` equals the isotropic symbol at the dual
  covector `V_Mᵀ ξ`.

The extension of the conjugation identity from the common core to the
operator closures (essential self-adjointness) is the remaining noted
step.
-/

namespace NCG

open MeasureTheory Matrix

/-- **Theorem `thm:frame-universality` (unitarity)**: the dilation
with Jacobian normalisation preserves the squared-norm integral:

`∫ |det V| · ‖ψ(V y)‖² dy = ∫ ‖ψ(x)‖² dx`

for every measurable `ψ` — the operator
`U_V ψ = (det V)^{1/2}·(ψ ∘ V)` is an isometry of `L²(ℝ^d)`. -/
theorem dilation_lintegral_normSq {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℝ) (hM : M.det ≠ 0)
    (ψ : (Fin d → ℝ) → ℂ) (hψ : Measurable ψ) :
    ∫⁻ y, ENNReal.ofReal |M.det|
        * ENNReal.ofReal (‖ψ (Matrix.toLin' M y)‖ ^ 2)
      = ∫⁻ x, ENNReal.ofReal (‖ψ x‖ ^ 2) := by
  have hmeaslin : Measurable (Matrix.toLin' M) :=
    (LinearMap.continuous_of_finiteDimensional _).measurable
  have hnorm : Measurable fun x => ENNReal.ofReal (‖ψ x‖ ^ 2) :=
    ENNReal.measurable_ofReal.comp ((hψ.norm).pow_const 2)
  calc ∫⁻ y, ENNReal.ofReal |M.det|
        * ENNReal.ofReal (‖ψ (Matrix.toLin' M y)‖ ^ 2)
      = ENNReal.ofReal |M.det|
        * ∫⁻ y, ENNReal.ofReal (‖ψ (Matrix.toLin' M y)‖ ^ 2) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal |M.det|
        * ∫⁻ x, ENNReal.ofReal (‖ψ x‖ ^ 2)
            ∂(Measure.map (Matrix.toLin' M) volume) := by
        rw [← lintegral_map hnorm hmeaslin]
    _ = ENNReal.ofReal |M.det| * (ENNReal.ofReal |M.det|⁻¹
        * ∫⁻ x, ENNReal.ofReal (‖ψ x‖ ^ 2)) := by
        rw [Real.map_matrix_volume_pi_eq_smul_volume_pi hM,
          lintegral_smul_measure, smul_eq_mul, abs_inv]
    _ = ∫⁻ x, ENNReal.ofReal (‖ψ x‖ ^ 2) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (abs_nonneg _),
          ← abs_inv, ← abs_mul, mul_inv_cancel₀ hM, abs_one,
          ENNReal.ofReal_one, one_mul]

/-- **Theorem `thm:frame-universality` (symbol conjugation)**: for a
*symmetric* second-moment matrix `M`, the anisotropic symbol at `ξ`
is the isotropic symbol at the dual covector `η = κ·Mᵀξ = κ·Mξ`:

`Σᵢ κ·(Mξ)ᵢ · Aᵢ = Σᵢ (Vᵀξ)ᵢ · Aᵢ`, `V = κM`

— the manuscript's chain-rule step `A^k (V_M)_{jk} = κ A^k M^{kj}`. -/
theorem dilation_symbol_conjugation {d : ℕ} {Alg : Type*}
    [AddCommGroup Alg] [Module ℝ Alg]
    (M : Matrix (Fin d) (Fin d) ℝ) (hsym : M.IsSymm) (κ : ℝ)
    (A : Fin d → Alg) (ξ : Fin d → ℝ) :
    ∑ i, (κ * M.mulVec ξ i) • A i
      = ∑ i, ((κ • M)ᵀ.mulVec ξ i) • A i := by
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  rw [Matrix.transpose_smul, hsym.eq]
  show κ * M.mulVec ξ i = ((κ • M).mulVec ξ) i
  rw [Matrix.smul_mulVec]
  simp

end NCG
