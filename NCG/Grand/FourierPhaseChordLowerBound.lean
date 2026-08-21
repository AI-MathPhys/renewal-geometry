/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.ChannelEstimates
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Lower bounds for discrete Fourier phase chords

Jordan's sine inequality gives a linear lower bound for the unit-circle chord
throughout the Nyquist interval.  This is the scalar coercivity input for
uniform high-frequency resolvent tails of periodic difference operators.
-/

namespace NCG

/-- A unit-circle chord controls its angle linearly on `[-π, π]`. -/
theorem complexPhaseChord_lower {theta : ℝ}
    (htheta : |theta| ≤ Real.pi) :
    2 / Real.pi * |theta| ≤
      ‖Complex.exp (Complex.I * theta) - 1‖ := by
  have hhalf : |theta / 2| ≤ Real.pi / 2 := by
    rw [abs_div]
    norm_num
    exact div_le_div_of_nonneg_right htheta (by norm_num)
  have hs := Real.mul_abs_le_abs_sin hhalf
  rw [Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [Real.norm_eq_abs, abs_mul]
  norm_num [abs_div] at hs ⊢
  calc
    2 / Real.pi * |theta| = 2 * (|theta| / Real.pi) := by ring
    _ ≤ 2 * |Real.sin (theta / 2)| :=
      mul_le_mul_of_nonneg_left hs (by norm_num)

/-- On the Nyquist band, the forward-difference phase has a mesh-uniform
linear lower bound in the Fourier mode. -/
theorem inverseMesh_mul_complexPhaseChord_lower
    (h k : ℝ) (hh : 0 < h)
    (hNyquist : |2 * Real.pi * h * k| ≤ Real.pi) :
    4 * |k| ≤ h⁻¹ *
      ‖Complex.exp (Complex.I *
        ((2 * Real.pi * h * k : ℝ) : ℂ)) - 1‖ := by
  have hchord := complexPhaseChord_lower hNyquist
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hhne : h ≠ 0 := ne_of_gt hh
  have habs : |2 * Real.pi * h * k| = 2 * Real.pi * h * |k| := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos hh]
    norm_num
  have hscaled := mul_le_mul_of_nonneg_left hchord (inv_nonneg.mpr hh.le)
  rw [habs] at hscaled
  calc
    4 * |k| = h⁻¹ * (2 / Real.pi * (2 * Real.pi * h * |k|)) := by
      field_simp
      ring
    _ ≤ h⁻¹ *
        ‖Complex.exp (Complex.I *
          ((2 * Real.pi * h * k : ℝ) : ℂ)) - 1‖ := hscaled

/-- Reverse-triangle form used to subtract a bounded connection
perturbation from the Fourier phase chord. -/
theorem norm_sub_lower_of_phaseChord
    {E : Type*} [NormedAddCommGroup E]
    (phase connection reference : E) :
    ‖phase - reference‖ - ‖connection - reference‖ ≤ ‖phase - connection‖ := by
  have htri : ‖phase - reference‖ ≤
      ‖phase - connection‖ + ‖connection - reference‖ := by
    have hsplit : phase - reference =
        (phase - connection) + (connection - reference) := by abel
    rw [hsplit]
    exact norm_add_le _ _
  linarith

/-- Quantitative scalar covariant-symbol lower bound.  The connection term is
controlled by the Banach-algebra exponential-minus-one estimate. -/
theorem inverseMesh_mul_scalarCovariantSymbol_lower
    (h k a : ℝ) (hh : 0 < h)
    (hNyquist : |2 * Real.pi * h * k| ≤ Real.pi) :
    4 * |k| - |a| * Real.exp (h * |a|) ≤
      h⁻¹ * ‖Complex.exp (Complex.I *
          ((2 * Real.pi * h * k : ℝ) : ℂ)) -
        Complex.exp ((-(h * a) : ℝ) : ℂ)‖ := by
  let phase : ℂ := Complex.exp (Complex.I *
    ((2 * Real.pi * h * k : ℝ) : ℂ))
  let connection : ℂ := Complex.exp ((-(h * a) : ℝ) : ℂ)
  have hphase : 4 * |k| ≤ h⁻¹ * ‖phase - 1‖ := by
    simpa only [phase] using
      inverseMesh_mul_complexPhaseChord_lower h k hh hNyquist
  have hconnection := ChannelEstimates.exp_sub_one_bound
    ((-(h * a) : ℝ) : ℂ)
  have hconnectionNorm : ‖((-(h * a) : ℝ) : ℂ)‖ = h * |a| := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_mul, abs_of_pos hh]
  rw [hconnectionNorm] at hconnection
  have hreverse := norm_sub_lower_of_phaseChord phase connection (1 : ℂ)
  have hscaleReverse :=
    mul_le_mul_of_nonneg_left hreverse (inv_nonneg.mpr hh.le)
  have hconnScaled : h⁻¹ * ‖connection - 1‖ ≤
      |a| * Real.exp (h * |a|) := by
    calc
      h⁻¹ * ‖connection - 1‖ ≤
          h⁻¹ * (h * |a| * Real.exp (h * |a|)) :=
        mul_le_mul_of_nonneg_left (by
          simpa only [connection, Complex.exp_eq_exp_ℂ] using hconnection)
          (inv_nonneg.mpr hh.le)
      _ = |a| * Real.exp (h * |a|) := by
        field_simp [ne_of_gt hh]
  have hscaleReverse' :
      h⁻¹ * ‖phase - 1‖ - h⁻¹ * ‖connection - 1‖ ≤
        h⁻¹ * ‖phase - connection‖ := by
    simpa only [mul_sub] using hscaleReverse
  dsimp only [phase, connection] at hscaleReverse ⊢
  nlinarith [hscaleReverse']

/-- Banach-algebra covariant-symbol lower bound.  It applies in particular to
matrix fibres represented as continuous endomorphisms with the operator norm;
no commutativity between the connection generator and other directions is
required. -/
theorem inverseMesh_mul_banachCovariantSymbol_lower
    {A : Type} [NormedRing A] [NormOneClass A]
    [NormedAlgebra ℝ A] [NormedAlgebra ℂ A] [CompleteSpace A]
    (h k : ℝ) (B : A) (hh : 0 < h)
    (hNyquist : |2 * Real.pi * h * k| ≤ Real.pi) :
    4 * |k| - ‖B‖ * Real.exp (h * ‖B‖) ≤
      h⁻¹ * ‖(Complex.exp (Complex.I *
          ((2 * Real.pi * h * k : ℝ) : ℂ)) • (1 : A)) -
        NormedSpace.exp (((-h : ℝ) : ℂ) • B)‖ := by
  let z : ℂ := Complex.exp (Complex.I *
    ((2 * Real.pi * h * k : ℝ) : ℂ))
  let phase : A := z • (1 : A)
  let connection : A := NormedSpace.exp (((-h : ℝ) : ℂ) • B)
  have hphaseNorm : ‖phase - 1‖ = ‖z - 1‖ := by
    calc
      ‖phase - 1‖ = ‖(z - 1) • (1 : A)‖ := by
        simp only [phase, sub_smul, one_smul]
      _ = ‖z - 1‖ * ‖(1 : A)‖ := norm_smul _ _
      _ = ‖z - 1‖ := by rw [norm_one, mul_one]
  have hphase : 4 * |k| ≤ h⁻¹ * ‖phase - 1‖ := by
    rw [hphaseNorm]
    simpa only [z] using
      inverseMesh_mul_complexPhaseChord_lower h k hh hNyquist
  have hconnection := ChannelEstimates.exp_sub_one_bound (((-h : ℝ) : ℂ) • B)
  have hconnectionNorm : ‖((-h : ℝ) : ℂ) • B‖ = h * ‖B‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos hh]
  rw [hconnectionNorm] at hconnection
  have hreverse := norm_sub_lower_of_phaseChord phase connection (1 : A)
  have hscaleReverse :=
    mul_le_mul_of_nonneg_left hreverse (inv_nonneg.mpr hh.le)
  have hconnScaled : h⁻¹ * ‖connection - 1‖ ≤
      ‖B‖ * Real.exp (h * ‖B‖) := by
    calc
      h⁻¹ * ‖connection - 1‖ ≤
          h⁻¹ * (h * ‖B‖ * Real.exp (h * ‖B‖)) :=
        mul_le_mul_of_nonneg_left (by
          simpa only [connection] using hconnection)
          (inv_nonneg.mpr hh.le)
      _ = ‖B‖ * Real.exp (h * ‖B‖) := by
        field_simp [ne_of_gt hh]
  have hscaleReverse' :
      h⁻¹ * ‖phase - 1‖ - h⁻¹ * ‖connection - 1‖ ≤
        h⁻¹ * ‖phase - connection‖ := by
    simpa only [mul_sub] using hscaleReverse
  dsimp only [phase, connection, z] at hscaleReverse ⊢
  nlinarith [hscaleReverse']
/-- Vectorwise covariant-symbol coercivity.  Unlike a lower bound on the
operator norm, this controls the symbol on every fibre vector and therefore
feeds directly into the positive symbol `D†D`. -/
theorem inverseMesh_mul_covariantSymbol_apply_lower
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [Nontrivial E]
    (h k : ℝ) (B : E →L[ℂ] E) (v : E) (hh : 0 < h)
    (hNyquist : |2 * Real.pi * h * k| ≤ Real.pi) :
    (4 * |k| - ‖B‖ * Real.exp (h * ‖B‖)) * ‖v‖ ≤
      h⁻¹ * ‖((Complex.exp (Complex.I *
          ((2 * Real.pi * h * k : ℝ) : ℂ)) •
            (1 : E →L[ℂ] E)) -
        NormedSpace.exp (((-h : ℝ) : ℂ) • B)) v‖ := by
  let z : ℂ := Complex.exp (Complex.I *
    ((2 * Real.pi * h * k : ℝ) : ℂ))
  let phase : E →L[ℂ] E := z • (1 : E →L[ℂ] E)
  let connection : E →L[ℂ] E :=
    NormedSpace.exp (((-h : ℝ) : ℂ) • B)
  have hphaseScalar : 4 * |k| ≤ h⁻¹ * ‖z - 1‖ := by
    simpa only [z] using
      inverseMesh_mul_complexPhaseChord_lower h k hh hNyquist
  have hphaseApply : ‖(phase - 1) v‖ = ‖z - 1‖ * ‖v‖ := by
    have happly : (phase - 1) v = (z - 1) • v := by
      simp only [phase, sub_apply, smul_apply, sub_smul, one_smul]
      change z • v - v = z • v - v
      rfl
    rw [happly, norm_smul]
  have hphaseVector : 4 * |k| * ‖v‖ ≤
      h⁻¹ * ‖(phase - 1) v‖ := by
    rw [hphaseApply]
    nlinarith [mul_le_mul_of_nonneg_right hphaseScalar (norm_nonneg v)]
  have hconnection := ChannelEstimates.exp_sub_one_bound
    (((-h : ℝ) : ℂ) • B)
  have hconnectionNorm :
      ‖((-h : ℝ) : ℂ) • B‖ = h * ‖B‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_neg, abs_of_pos hh]
  rw [hconnectionNorm] at hconnection
  have hconnectionApply : ‖(connection - 1) v‖ ≤
      h * ‖B‖ * Real.exp (h * ‖B‖) * ‖v‖ := by
    calc
      ‖(connection - 1) v‖ ≤ ‖connection - 1‖ * ‖v‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ (h * ‖B‖ * Real.exp (h * ‖B‖)) * ‖v‖ :=
        mul_le_mul_of_nonneg_right (by
          simpa only [connection] using hconnection) (norm_nonneg v)
  have hreverse := norm_sub_lower_of_phaseChord
    (phase v) (connection v) v
  have hphaseDiff : phase v - v = (phase - 1) v := by
    change phase v - v = phase v - (1 : E →L[ℂ] E) v
    rfl
  have hconnectionDiff : connection v - v = (connection - 1) v := by
    change connection v - v = connection v - (1 : E →L[ℂ] E) v
    rfl
  have hdiff : phase v - connection v = (phase - connection) v := by
    simp only [sub_apply]
  rw [hphaseDiff, hconnectionDiff, hdiff] at hreverse
  have hscaleReverse :=
    mul_le_mul_of_nonneg_left hreverse (inv_nonneg.mpr hh.le)
  have hconnectionScaled : h⁻¹ * ‖(connection - 1) v‖ ≤
      ‖B‖ * Real.exp (h * ‖B‖) * ‖v‖ := by
    calc
      h⁻¹ * ‖(connection - 1) v‖ ≤
          h⁻¹ * (h * ‖B‖ * Real.exp (h * ‖B‖) * ‖v‖) :=
        mul_le_mul_of_nonneg_left hconnectionApply (inv_nonneg.mpr hh.le)
      _ = ‖B‖ * Real.exp (h * ‖B‖) * ‖v‖ := by
        field_simp [ne_of_gt hh]
  have hscaleReverse' :
      h⁻¹ * ‖(phase - 1) v‖ - h⁻¹ * ‖(connection - 1) v‖ ≤
        h⁻¹ * ‖(phase - connection) v‖ := by
    simpa only [mul_sub] using hscaleReverse
  dsimp only [phase, connection, z] at hscaleReverse' ⊢
  nlinarith



/-- Squared energy form of `inverseMesh_mul_covariantSymbol_apply_lower`.
This is the direction-wise lower bound entering the positive Fourier symbol
`D†D`. -/
theorem covariantSymbol_apply_energy_lower
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [Nontrivial E]
    (h k : ℝ) (B : E →L[ℂ] E) (v : E) (hh : 0 < h)
    (hNyquist : |2 * Real.pi * h * k| ≤ Real.pi)
    (hmode : ‖B‖ * Real.exp (h * ‖B‖) ≤ 4 * |k|) :
    (4 * |k| - ‖B‖ * Real.exp (h * ‖B‖)) ^ 2 * ‖v‖ ^ 2 ≤
      (h⁻¹ * ‖((Complex.exp (Complex.I *
          ((2 * Real.pi * h * k : ℝ) : ℂ)) •
            (1 : E →L[ℂ] E)) -
        NormedSpace.exp (((-h : ℝ) : ℂ) • B)) v‖) ^ 2 := by
  have hlower := inverseMesh_mul_covariantSymbol_apply_lower
    h k B v hh hNyquist
  let lhs : ℝ :=
    (4 * |k| - ‖B‖ * Real.exp (h * ‖B‖)) * ‖v‖
  let rhs : ℝ := h⁻¹ * ‖((Complex.exp (Complex.I *
      ((2 * Real.pi * h * k : ℝ) : ℂ)) •
        (1 : E →L[ℂ] E)) -
      NormedSpace.exp (((-h : ℝ) : ℂ) • B)) v‖
  have hlhs : 0 ≤ lhs :=
    mul_nonneg (sub_nonneg.mpr hmode) (norm_nonneg v)
  have hrhs : 0 ≤ rhs :=
    mul_nonneg (inv_nonneg.mpr hh.le) (norm_nonneg _)
  have hsq : lhs ^ 2 ≤ rhs ^ 2 := by nlinarith
  dsimp only [lhs, rhs] at hsq
  nlinarith


/-- Sum of the squared directional covariant Fourier symbols on a fibre
vector. -/
noncomputable def covariantSymbolTotalEnergy
    {d : Type*} [Fintype d]
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (h : ℝ) (k : d → ℝ) (B : d → E →L[ℂ] E) (v : E) : ℝ :=
  ∑ j, (h⁻¹ * ‖((Complex.exp (Complex.I *
      ((2 * Real.pi * h * k j : ℝ) : ℂ)) •
        (1 : E →L[ℂ] E)) -
      NormedSpace.exp (((-h : ℝ) : ℂ) • B j)) v‖) ^ 2

/-- A high coordinate controls the full positive covariant-symbol energy.
This is the finite-dimensional Fourier-symbol form of the quadratic tail
bound used in the norm-resolvent argument. -/
theorem covariantSymbolTotalEnergy_lower_of_coordinate
    {d : Type*} [Fintype d]
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [Nontrivial E]
    (h : ℝ) (k : d → ℝ) (B : d → E →L[ℂ] E) (v : E)
    (j : d) (hh : 0 < h)
    (hNyquist : |2 * Real.pi * h * k j| ≤ Real.pi)
    (hmode : ‖B j‖ * Real.exp (h * ‖B j‖) ≤ 4 * |k j|) :
    (4 * |k j| - ‖B j‖ * Real.exp (h * ‖B j‖)) ^ 2 * ‖v‖ ^ 2 ≤
      covariantSymbolTotalEnergy h k B v := by
  classical
  have hj := covariantSymbol_apply_energy_lower
    h (k j) (B j) v hh hNyquist hmode
  calc
    (4 * |k j| - ‖B j‖ * Real.exp (h * ‖B j‖)) ^ 2 * ‖v‖ ^ 2 ≤
        (h⁻¹ * ‖((Complex.exp (Complex.I *
          ((2 * Real.pi * h * k j : ℝ) : ℂ)) •
            (1 : E →L[ℂ] E)) -
          NormedSpace.exp (((-h : ℝ) : ℂ) • B j)) v‖) ^ 2 := hj
    _ ≤ ∑ i, (h⁻¹ * ‖((Complex.exp (Complex.I *
          ((2 * Real.pi * h * k i : ℝ) : ℂ)) •
            (1 : E →L[ℂ] E)) -
          NormedSpace.exp (((-h : ℝ) : ℂ) • B i)) v‖) ^ 2 := by
      exact Finset.single_le_sum
        (fun i _ => sq_nonneg (h⁻¹ * ‖((Complex.exp (Complex.I *
          ((2 * Real.pi * h * k i : ℝ) : ℂ)) •
            (1 : E →L[ℂ] E)) -
          NormedSpace.exp (((-h : ℝ) : ℂ) • B i)) v‖))
        (Finset.mem_univ j)
    _ = covariantSymbolTotalEnergy h k B v := rfl

end NCG
