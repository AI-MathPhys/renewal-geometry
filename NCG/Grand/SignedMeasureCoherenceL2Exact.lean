/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.VectorMeasure.WithDensityVec
import Mathlib.MeasureTheory.VectorMeasure.Integral

/-!
# Signed-measure coherent/counterflow decomposition in L²

This file supplies the general signed-measure layer of
`thm:GT-coherent-counterflow`.  The Radon--Nikodym derivative of a finite
signed measure with respect to its Jordan total variation is proved to take
the values `±1` almost everywhere.  From this polar identity we derive the
constant orthogonal projection and its exact squared L² residual.
-/

open MeasureTheory
open scoped ENNReal

namespace NCG
namespace SignedMeasureCoherenceL2Exact

variable {α : Type*} [MeasurableSpace α]

noncomputable instance totalVariation_isFinite (s : SignedMeasure α) :
    IsFiniteMeasure s.totalVariation := by
  rw [SignedMeasure.totalVariation]
  infer_instance

noncomputable def totalMass (s : SignedMeasure α) : ℝ :=
  s.totalVariation.real Set.univ

noncomputable def signedMass (s : SignedMeasure α) : ℝ :=
  s Set.univ

noncomputable def coherentCoefficient (s : SignedMeasure α) : ℝ :=
  signedMass s / totalMass s

noncomputable def counterflowWeight (s : SignedMeasure α) : ℝ :=
  (totalMass s ^ 2 - signedMass s ^ 2) / (2 * totalMass s)

/-- The coherent signed measure `(S/T)|μ|`. -/
noncomputable def coherentMeasure (s : SignedMeasure α) : SignedMeasure α :=
  coherentCoefficient s • s.totalVariation.toSignedMeasure

/-- The signed counterflow residual `μ - (S/T)|μ|`. -/
noncomputable def counterflowMeasure (s : SignedMeasure α) : SignedMeasure α :=
  s - coherentMeasure s

/-- The polar RN density of a signed measure has modulus one almost
everywhere with respect to total variation. -/
theorem ae_sq_rnDeriv_totalVariation (s : SignedMeasure α) :
    ∀ᵐ x ∂s.totalVariation,
      s.rnDeriv s.totalVariation x ^ 2 = 1 := by
  let p := s.toJordanDecomposition.posPart
  let n := s.toJordanDecomposition.negPart
  have hpn : p ⟂ₘ n := s.toJordanDecomposition.mutuallySingular
  have hp1 : p.rnDeriv (p + n) =ᵐ[p] fun _ => 1 :=
    (Measure.rnDeriv_add_right_of_mutuallySingular (μ := p) hpn).trans
      (Measure.rnDeriv_self p)
  have hn1 : n.rnDeriv (p + n) =ᵐ[n] fun _ => 1 := by
    simpa [add_comm] using
      (Measure.rnDeriv_add_right_of_mutuallySingular (μ := n) hpn.symm).trans
        (Measure.rnDeriv_self n)
  have hn_ac : n ≪ p + n := Measure.AbsolutelyContinuous.rfl.add_right' p
  have hp_ac : p ≪ p + n := Measure.AbsolutelyContinuous.rfl.add_right n
  have hp0 : p.rnDeriv (p + n) =ᵐ[n] 0 :=
    Measure.rnDeriv_eq_zero_of_mutuallySingular hpn hn_ac
  have hn0 : n.rnDeriv (p + n) =ᵐ[p] 0 :=
    Measure.rnDeriv_eq_zero_of_mutuallySingular hpn.symm hp_ac
  rw [SignedMeasure.totalVariation, ae_add_measure_iff]
  constructor
  · rw [SignedMeasure.rnDeriv_def]
    filter_upwards [hp1, hn0] with x hpx hnx
    simp [p, n, hpx, hnx]
  · rw [SignedMeasure.rnDeriv_def]
    filter_upwards [hp0, hn1] with x hpx hnx
    simp [p, n, hpx, hnx]

/-- The signed total mass is the integral of the polar RN density. -/
theorem integral_rnDeriv_totalVariation (s : SignedMeasure α) :
    ∫ x, s.rnDeriv s.totalVariation x ∂s.totalVariation = signedMass s := by
  have hac : s ≪ᵥ s.totalVariation.toENNRealVectorMeasure := by
    rw [SignedMeasure.absolutelyContinuous_ennreal_iff]
    simpa using (Measure.AbsolutelyContinuous.rfl :
      s.totalVariation ≪ s.totalVariation)
  have hrep := SignedMeasure.withDensityᵥ_rnDeriv_eq s s.totalVariation hac
  have hu := congrArg (fun q : SignedMeasure α => q Set.univ) hrep
  rw [MeasureTheory.withDensityᵥ_apply
    (SignedMeasure.integrable_rnDeriv s s.totalVariation) MeasurableSet.univ] at hu
  simpa [signedMass] using hu

/-- The polar density has squared L² norm equal to total variation mass. -/
theorem integral_sq_rnDeriv_totalVariation (s : SignedMeasure α) :
    ∫ x, s.rnDeriv s.totalVariation x ^ 2 ∂s.totalVariation = totalMass s := by
  rw [totalMass]
  calc
    (∫ x, s.rnDeriv s.totalVariation x ^ 2 ∂s.totalVariation)
        = ∫ _x, (1 : ℝ) ∂s.totalVariation :=
          integral_congr_ae (ae_sq_rnDeriv_totalVariation s)
    _ = s.totalVariation.real Set.univ := by simp

/-- The residual from the constant projection has zero mean. -/
theorem integral_rnDeriv_sub_coherentCoefficient
    (s : SignedMeasure α) (hT : totalMass s ≠ 0) :
    ∫ x, (s.rnDeriv s.totalVariation x - coherentCoefficient s)
        ∂s.totalVariation = 0 := by
  rw [integral_sub (SignedMeasure.integrable_rnDeriv s s.totalVariation)
    (integrable_const _)]
  rw [integral_rnDeriv_totalVariation]
  simp only [integral_const, smul_eq_mul]
  unfold coherentCoefficient
  change signedMass s -
    s.totalVariation.real Set.univ * (signedMass s / totalMass s) = 0
  rw [show s.totalVariation.real Set.univ = totalMass s from rfl]
  field_simp
  ring

/-- Exact L² Pythagorean identity:
`‖dμ/d|μ| - S/T‖²₂ = (T²-S²)/T = 2 κ_cf`. -/
theorem integral_sq_sub_coherentCoefficient
    (s : SignedMeasure α) (hT : totalMass s ≠ 0) :
    ∫ x, (s.rnDeriv s.totalVariation x - coherentCoefficient s) ^ 2
        ∂s.totalVariation = 2 * counterflowWeight s := by
  let h := s.rnDeriv s.totalVariation
  let c := coherentCoefficient s
  have hh : Integrable h s.totalVariation :=
    SignedMeasure.integrable_rnDeriv s s.totalVariation
  have hsq : Integrable (fun x => h x ^ 2) s.totalVariation := by
    apply Integrable.congr (integrable_const (1 : ℝ))
    filter_upwards [ae_sq_rnDeriv_totalVariation s] with x hx
    exact hx.symm
  have hlin : Integrable (fun x => 2 * c * h x) s.totalVariation :=
    hh.const_mul _
  have hconst : Integrable (fun _ : α => c ^ 2) s.totalVariation :=
    integrable_const _
  have hadd :
      (∫ x, (h x ^ 2 - 2 * c * h x + c ^ 2) ∂s.totalVariation) =
        (∫ x, (h x ^ 2 - 2 * c * h x) ∂s.totalVariation) +
          ∫ _x : α, c ^ 2 ∂s.totalVariation :=
    integral_add (hsq.sub hlin) hconst
  have hsub :
      (∫ x, (h x ^ 2 - 2 * c * h x) ∂s.totalVariation) =
        (∫ x, h x ^ 2 ∂s.totalVariation) -
          ∫ x, 2 * c * h x ∂s.totalVariation :=
    integral_sub hsq hlin
  have hmul :
      (∫ x, 2 * c * h x ∂s.totalVariation) =
        2 * c * ∫ x, h x ∂s.totalVariation := by
    exact integral_const_mul (μ := s.totalVariation) (2 * c) h
  have hcst :
      (∫ _x : α, c ^ 2 ∂s.totalVariation) = c ^ 2 * totalMass s := by
    simp only [integral_const, smul_eq_mul]
    rw [totalMass]
    ring
  calc
    (∫ x, (h x - c) ^ 2 ∂s.totalVariation)
        = ∫ x, (h x ^ 2 - 2 * c * h x + c ^ 2) ∂s.totalVariation := by
          apply integral_congr_ae
          filter_upwards with x
          ring
    _ = (∫ x, h x ^ 2 ∂s.totalVariation) -
          2 * c * (∫ x, h x ∂s.totalVariation) +
          c ^ 2 * totalMass s := by
          rw [hadd, hsub, hmul, hcst]
    _ = totalMass s - 2 * c * signedMass s + c ^ 2 * totalMass s := by
          rw [show (∫ x, h x ^ 2 ∂s.totalVariation) = totalMass s from
            integral_sq_rnDeriv_totalVariation s,
            show (∫ x, h x ∂s.totalVariation) = signedMass s from
              integral_rnDeriv_totalVariation s]
    _ = 2 * counterflowWeight s := by
          unfold c coherentCoefficient counterflowWeight
          field_simp
          ring

/-- The coherent part is literally the constant-density signed measure. -/
theorem withDensityᵥ_const_coherentCoefficient (s : SignedMeasure α) :
    s.totalVariation.withDensityᵥ (fun _ : α => coherentCoefficient s) =
      coherentMeasure s := by
  ext A hA
  rw [MeasureTheory.withDensityᵥ_apply (integrable_const _) hA]
  simp only [integral_const, smul_eq_mul]
  rw [measureReal_restrict_apply_univ]
  rw [coherentMeasure, _root_.smul_apply,
    Measure.toSignedMeasure_apply_measurable hA]
  ring

/-- The counterflow is the signed measure whose density is the orthogonal
residual `dμ/d|μ| - S/T`. -/
theorem counterflowMeasure_eq_withDensityᵥ (s : SignedMeasure α) :
    counterflowMeasure s =
      s.totalVariation.withDensityᵥ
        (fun x => s.rnDeriv s.totalVariation x - coherentCoefficient s) := by
  have hac : s ≪ᵥ s.totalVariation.toENNRealVectorMeasure := by
    rw [SignedMeasure.absolutelyContinuous_ennreal_iff]
    rw [VectorMeasure.ennrealToMeasure_toENNRealVectorMeasure]
  have hrep := SignedMeasure.withDensityᵥ_rnDeriv_eq s s.totalVariation hac
  let h := s.rnDeriv s.totalVariation
  let c := coherentCoefficient s
  have hh : Integrable h s.totalVariation :=
    SignedMeasure.integrable_rnDeriv s s.totalVariation
  have hc : Integrable (fun _ : α => c) s.totalVariation := integrable_const _
  ext A hA
  have hsA := congrArg (fun q : SignedMeasure α => q A) hrep
  rw [MeasureTheory.withDensityᵥ_apply hh hA] at hsA
  rw [counterflowMeasure, _root_.sub_apply, coherentMeasure,
    _root_.smul_apply, Measure.toSignedMeasure_apply_measurable hA]
  change s A - c • s.totalVariation.real A =
    (s.totalVariation.withDensityᵥ (h - fun _ : α => c)) A
  rw [MeasureTheory.withDensityᵥ_apply (hh.sub hc) hA,
    show ∫ x in A, (h - fun _ : α => c) x ∂s.totalVariation =
        ∫ x in A, (h x - c) ∂s.totalVariation by rfl]
  rw [integral_sub hh.integrableOn hc.integrableOn]
  rw [← hsA]
  simp only [integral_const, smul_eq_mul]
  rw [measureReal_restrict_apply_univ]
  ring

/-- Total mass in terms of the two genuine Jordan parts. -/
theorem totalMass_eq_jordan_sum (s : SignedMeasure α) :
    totalMass s =
      s.toJordanDecomposition.posPart.real Set.univ +
        s.toJordanDecomposition.negPart.real Set.univ := by
  rw [totalMass, SignedMeasure.totalVariation]
  rw [measureReal_add_apply]

/-- Signed mass in terms of the two genuine Jordan parts. -/
theorem signedMass_eq_jordan_sub (s : SignedMeasure α) :
    signedMass s =
      s.toJordanDecomposition.posPart.real Set.univ -
        s.toJordanDecomposition.negPart.real Set.univ := by
  have hu := congrArg (fun q : SignedMeasure α => q Set.univ)
    (SignedMeasure.toSignedMeasure_toJordanDecomposition s)
  rw [JordanDecomposition.toSignedMeasure,
    Measure.toSignedMeasure_sub_apply MeasurableSet.univ] at hu
  simpa [signedMass] using hu.symm

/-- The projection coefficient lies in `[-1,1]`. -/
theorem coherentCoefficient_mem_Icc (s : SignedMeasure α)
    (hT : 0 < totalMass s) : coherentCoefficient s ∈ Set.Icc (-1) 1 := by
  have hp : 0 ≤ s.toJordanDecomposition.posPart.real Set.univ := measureReal_nonneg
  have hn : 0 ≤ s.toJordanDecomposition.negPart.real Set.univ := measureReal_nonneg
  have hreprT := totalMass_eq_jordan_sum s
  have hreprS := signedMass_eq_jordan_sub s
  constructor
  · rw [coherentCoefficient, le_div_iff₀ hT]
    linarith
  · rw [coherentCoefficient, div_le_iff₀ hT]
    linarith

/-- The explicit Jordan pair of the counterflow.  The positive carrier of
`μ` is scaled by `1-S/T`, and its negative carrier by `1+S/T`. -/
noncomputable def counterflowJordan (s : SignedMeasure α) : JordanDecomposition α where
  posPart := (1 - coherentCoefficient s).toNNReal •
    s.toJordanDecomposition.posPart
  negPart := (1 + coherentCoefficient s).toNNReal •
    s.toJordanDecomposition.negPart
  mutuallySingular :=
    Measure.MutuallySingular.smul_nnreal _
      (Measure.MutuallySingular.smul_nnreal _
        s.toJordanDecomposition.mutuallySingular.symm).symm

/-- The explicit pair above is the actual Jordan decomposition of the
counterflow signed measure. -/
theorem counterflowMeasure_eq_counterflowJordan (s : SignedMeasure α)
    (hT : 0 < totalMass s) :
    counterflowMeasure s = (counterflowJordan s).toSignedMeasure := by
  let c := coherentCoefficient s
  have hc := coherentCoefficient_mem_Icc s hT
  have ha : 0 ≤ 1 - c := by exact sub_nonneg.mpr hc.2
  have hb : 0 ≤ 1 + c := by linarith [hc.1]
  ext A hA
  have hsA := congrArg (fun q : SignedMeasure α => q A)
    (SignedMeasure.toSignedMeasure_toJordanDecomposition s)
  rw [JordanDecomposition.toSignedMeasure,
    Measure.toSignedMeasure_sub_apply hA] at hsA
  rw [counterflowMeasure, _root_.sub_apply, coherentMeasure,
    _root_.smul_apply, Measure.toSignedMeasure_apply_measurable hA,
    SignedMeasure.totalVariation, measureReal_add_apply,
    JordanDecomposition.toSignedMeasure,
    Measure.toSignedMeasure_sub_apply hA]
  rw [← hsA]
  change
    (s.toJordanDecomposition.posPart.real A -
        s.toJordanDecomposition.negPart.real A) -
      c * (s.toJordanDecomposition.posPart.real A +
        s.toJordanDecomposition.negPart.real A) =
      (((1 - c).toNNReal • s.toJordanDecomposition.posPart).real A -
        ((1 + c).toNNReal • s.toJordanDecomposition.negPart).real A)
  rw [measureReal_nnreal_smul_apply, measureReal_nnreal_smul_apply,
    Real.coe_toNNReal _ ha, Real.coe_toNNReal _ hb]
  ring

/-- Consequently Mathlib's canonical Jordan decomposition is exactly the
scaled original positive/negative pair. -/
theorem counterflow_toJordanDecomposition (s : SignedMeasure α)
    (hT : 0 < totalMass s) :
    (counterflowMeasure s).toJordanDecomposition = counterflowJordan s :=
  SignedMeasure.toJordanDecomposition_eq (counterflowMeasure_eq_counterflowJordan s hT)

theorem jordan_pos_mass (s : SignedMeasure α) :
    s.toJordanDecomposition.posPart.real Set.univ =
      (totalMass s + signedMass s) / 2 := by
  have hT := totalMass_eq_jordan_sum s
  have hS := signedMass_eq_jordan_sub s
  linarith

theorem jordan_neg_mass (s : SignedMeasure α) :
    s.toJordanDecomposition.negPart.real Set.univ =
      (totalMass s - signedMass s) / 2 := by
  have hT := totalMass_eq_jordan_sum s
  have hS := signedMass_eq_jordan_sub s
  linarith

/-- The positive Jordan mass of the counterflow is exactly `κ_cf`. -/
theorem counterflow_pos_mass (s : SignedMeasure α) (hT : 0 < totalMass s) :
    (counterflowMeasure s).toJordanDecomposition.posPart.real Set.univ =
      counterflowWeight s := by
  rw [counterflow_toJordanDecomposition s hT]
  change (((1 - coherentCoefficient s).toNNReal •
    s.toJordanDecomposition.posPart).real Set.univ) = counterflowWeight s
  have hc := coherentCoefficient_mem_Icc s hT
  have ha : 0 ≤ 1 - coherentCoefficient s := sub_nonneg.mpr hc.2
  rw [measureReal_nnreal_smul_apply, Real.coe_toNNReal _ ha, jordan_pos_mass]
  unfold coherentCoefficient counterflowWeight
  field_simp
  ring

/-- The negative Jordan mass of the counterflow is exactly `κ_cf`. -/
theorem counterflow_neg_mass (s : SignedMeasure α) (hT : 0 < totalMass s) :
    (counterflowMeasure s).toJordanDecomposition.negPart.real Set.univ =
      counterflowWeight s := by
  rw [counterflow_toJordanDecomposition s hT]
  change (((1 + coherentCoefficient s).toNNReal •
    s.toJordanDecomposition.negPart).real Set.univ) = counterflowWeight s
  have hc := coherentCoefficient_mem_Icc s hT
  have hb : 0 ≤ 1 + coherentCoefficient s := by linarith [hc.1]
  rw [measureReal_nnreal_smul_apply, Real.coe_toNNReal _ hb, jordan_neg_mass]
  unfold coherentCoefficient counterflowWeight
  field_simp
  ring

/-- The normalized positive Jordan part `P⁺`. -/
noncomputable def normalizedCounterflowPos (s : SignedMeasure α) : Measure α :=
  (counterflowWeight s)⁻¹.toNNReal •
    (counterflowMeasure s).toJordanDecomposition.posPart

/-- The normalized negative Jordan part `P⁻`. -/
noncomputable def normalizedCounterflowNeg (s : SignedMeasure α) : Measure α :=
  (counterflowWeight s)⁻¹.toNNReal •
    (counterflowMeasure s).toJordanDecomposition.negPart

theorem totalMass_pos_of_counterflowWeight_pos (s : SignedMeasure α)
    (hk : 0 < counterflowWeight s) : 0 < totalMass s := by
  have hT0 : 0 ≤ totalMass s := by
    rw [totalMass_eq_jordan_sum]
    positivity
  rcases hT0.eq_or_lt with hzero | hpos
  · exfalso
    unfold counterflowWeight at hk
    rw [← hzero] at hk
    norm_num at hk
  · exact hpos

noncomputable instance normalizedCounterflowPos_isFinite (s : SignedMeasure α) :
    IsFiniteMeasure (normalizedCounterflowPos s) := by
  rw [normalizedCounterflowPos]
  infer_instance

noncomputable instance normalizedCounterflowNeg_isFinite (s : SignedMeasure α) :
    IsFiniteMeasure (normalizedCounterflowNeg s) := by
  rw [normalizedCounterflowNeg]
  infer_instance

theorem normalizedCounterflowPos_mass_one (s : SignedMeasure α)
    (hk : 0 < counterflowWeight s) :
    (normalizedCounterflowPos s).real Set.univ = 1 := by
  rw [normalizedCounterflowPos, measureReal_nnreal_smul_apply,
    Real.coe_toNNReal _ (inv_nonneg.mpr hk.le)]
  rw [counterflow_pos_mass s (totalMass_pos_of_counterflowWeight_pos s hk)]
  field_simp

theorem normalizedCounterflowNeg_mass_one (s : SignedMeasure α)
    (hk : 0 < counterflowWeight s) :
    (normalizedCounterflowNeg s).real Set.univ = 1 := by
  rw [normalizedCounterflowNeg, measureReal_nnreal_smul_apply,
    Real.coe_toNNReal _ (inv_nonneg.mpr hk.le)]
  rw [counterflow_neg_mass s (totalMass_pos_of_counterflowWeight_pos s hk)]
  field_simp

/-- The first boxed identity of (SC.2), using the actual normalized Jordan
parts of the general signed counterflow measure. -/
theorem counterflowMeasure_eq_weight_smul_normalizedJordan (s : SignedMeasure α)
    (hk : 0 < counterflowWeight s) :
    counterflowMeasure s = counterflowWeight s •
      ((normalizedCounterflowPos s).toSignedMeasure -
        (normalizedCounterflowNeg s).toSignedMeasure) := by
  let q := counterflowMeasure s
  have hrec := SignedMeasure.toSignedMeasure_toJordanDecomposition q
  calc
    counterflowMeasure s =
        q.toJordanDecomposition.posPart.toSignedMeasure -
          q.toJordanDecomposition.negPart.toSignedMeasure := by
      change q = _
      simpa [JordanDecomposition.toSignedMeasure] using hrec.symm
    _ = counterflowWeight s •
        ((normalizedCounterflowPos s).toSignedMeasure -
          (normalizedCounterflowNeg s).toSignedMeasure) := by
      ext A hA
      rw [Measure.toSignedMeasure_sub_apply hA, _root_.smul_apply,
        _root_.sub_apply, Measure.toSignedMeasure_apply_measurable hA,
        Measure.toSignedMeasure_apply_measurable hA]
      unfold normalizedCounterflowPos normalizedCounterflowNeg
      rw [measureReal_nnreal_smul_apply, measureReal_nnreal_smul_apply,
        Real.coe_toNNReal _ (inv_nonneg.mpr hk.le)]
      change q.toJordanDecomposition.posPart.real A -
          q.toJordanDecomposition.negPart.real A =
        counterflowWeight s *
          ((counterflowWeight s)⁻¹ * q.toJordanDecomposition.posPart.real A -
            (counterflowWeight s)⁻¹ * q.toJordanDecomposition.negPart.real A)
      field_simp

/-- Orthogonality of the residual to every constant function.  Together with
the zero-mean theorem, this is the literal Hilbert-space characterization of
the constant orthogonal projection in `L²(|μ|)`. -/
theorem residual_orthogonal_to_constants (s : SignedMeasure α)
    (hT : 0 < totalMass s) (a : ℝ) :
    ∫ x, (s.rnDeriv s.totalVariation x - coherentCoefficient s) * a
      ∂s.totalVariation = 0 := by
  have hr : Integrable
      (fun x => s.rnDeriv s.totalVariation x - coherentCoefficient s)
      s.totalVariation :=
    (SignedMeasure.integrable_rnDeriv s s.totalVariation).sub (integrable_const _)
  rw [integral_mul_const a _]
  rw [integral_rnDeriv_sub_coherentCoefficient s hT.ne']
  simp

/-- The observable identity (SC.3) for every integrable real observable. -/
theorem observable_coherent_counterflow (s : SignedMeasure α)
    (hk : 0 < counterflowWeight s) (f : α → ℝ)
    (hTV : Integrable f s.totalVariation)
    (hP : Integrable f (normalizedCounterflowPos s))
    (hN : Integrable f (normalizedCounterflowNeg s)) :
    (∫ᵛ x, f x ∂<•s) =
      signedMass s * ((∫ x, f x ∂s.totalVariation) / totalMass s) +
        counterflowWeight s *
          ((∫ x, f x ∂normalizedCounterflowPos s) -
            ∫ x, f x ∂normalizedCounterflowNeg s) := by
  let Pp := normalizedCounterflowPos s
  let Pn := normalizedCounterflowNeg s
  have hPvec : Pp.toSignedMeasure.Integrable f := by
    simpa [VectorMeasure.Integrable] using hP
  have hNvec : Pn.toSignedMeasure.Integrable f := by
    simpa [VectorMeasure.Integrable] using hN
  have hTVvec : s.totalVariation.toSignedMeasure.Integrable f := by
    simpa [VectorMeasure.Integrable] using hTV
  have hcfvec : (counterflowMeasure s).Integrable f := by
    rw [counterflowMeasure_eq_weight_smul_normalizedJordan s hk]
    exact (hPvec.sub_vectorMeasure hNvec).smul_vectorMeasure _
  have hcohvec : (coherentMeasure s).Integrable f := by
    rw [coherentMeasure]
    exact hTVvec.smul_vectorMeasure _
  have hsdecomp : s = coherentMeasure s + counterflowMeasure s := by
    unfold counterflowMeasure
    abel
  have hT := totalMass_pos_of_counterflowWeight_pos s hk
  change (∫ᵛ x, f x ∂<•s) =
    signedMass s * ((∫ x, f x ∂s.totalVariation) / totalMass s) +
      counterflowWeight s * ((∫ x, f x ∂Pp) - ∫ x, f x ∂Pn)
  calc
    (∫ᵛ x, f x ∂<•s) =
        ∫ᵛ x, f x ∂<•(coherentMeasure s + counterflowMeasure s) :=
      congrArg (fun q : SignedMeasure α => ∫ᵛ x, f x ∂<•q) hsdecomp
    _ = (∫ᵛ x, f x ∂<•coherentMeasure s) +
          ∫ᵛ x, f x ∂<•counterflowMeasure s :=
      VectorMeasure.integral_add_vectorMeasure hcohvec hcfvec
    _ = coherentCoefficient s * (∫ x, f x ∂s.totalVariation) +
          ∫ᵛ x, f x ∂<•counterflowMeasure s := by
      rw [coherentMeasure, VectorMeasure.integral_smul_vectorMeasure,
        VectorMeasure.integral_toSignedMeasure]
      rfl
    _ = coherentCoefficient s * (∫ x, f x ∂s.totalVariation) +
          counterflowWeight s *
            (∫ᵛ x, f x ∂<•(Pp.toSignedMeasure - Pn.toSignedMeasure)) := by
      rw [counterflowMeasure_eq_weight_smul_normalizedJordan s hk,
        VectorMeasure.integral_smul_vectorMeasure]
      rfl
    _ = coherentCoefficient s * (∫ x, f x ∂s.totalVariation) +
          counterflowWeight s * ((∫ x, f x ∂Pp) - ∫ x, f x ∂Pn) := by
      rw [VectorMeasure.integral_sub_vectorMeasure hPvec hNvec,
        VectorMeasure.integral_toSignedMeasure,
        VectorMeasure.integral_toSignedMeasure]
    _ = signedMass s * ((∫ x, f x ∂s.totalVariation) / totalMass s) +
          counterflowWeight s * ((∫ x, f x ∂Pp) - ∫ x, f x ∂Pn) := by
      unfold coherentCoefficient
      field_simp

end SignedMeasureCoherenceL2Exact
end NCG
