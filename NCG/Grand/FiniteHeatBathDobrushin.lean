/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.DobrushinInfluencePoissonTail

/-!
# Finite heat-bath oscillation compiler

This is the operator layer of `thm:SMFS-Dobrushin-gap`.  Local update maps
with Dobrushin single-site oscillation bounds are averaged into one discrete
heat-bath step, and the exact matrix controlling its oscillation vector is
computed.  The final scalar lemma converts approximate tensorization into the
claimed Poincare gap.
-/

open scoped BigOperators

noncomputable section

namespace NCG
namespace FiniteHeatBathDobrushin

theorem seminorm_finset_sum_le
    {F ι : Type*} [SeminormedAddCommGroup F] [NormedSpace ℝ F]
    (p : Seminorm ℝ F) (s : Finset ι) (f : ι → F) :
    p (∑ i ∈ s, f i) ≤ ∑ i ∈ s, p (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      exact (map_add_le_add p _ _).trans (add_le_add_right ih _)

/-- The average of all single-site update maps. -/
def averageUpdate
    {F ι : Type*} [Fintype ι] [SeminormedAddCommGroup F]
    [NormedSpace ℝ F] (update : ι → F →ₗ[ℝ] F) : F →ₗ[ℝ] F :=
  ((Fintype.card ι : ℝ)⁻¹) • ∑ i, update i

/-- The discrete influence matrix of the averaged update:
`(1-1/m)I + C/m`. -/
def averagedInfluence
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  fun j l =>
    (if j = l then ((Fintype.card ι : ℝ) - 1) /
      Fintype.card ι else 0) + C j l / Fintype.card ι

section MatrixOperatorNorm

open scoped Matrix.Norms.Operator
set_option backward.isDefEq.respectTransparency false

/-- The coordinatewise exponential series used by the finite-kernel layer is
the corresponding entry of mathlib's matrix exponential. -/
theorem exponentialEntry_eq_exp_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (i j : ι) :
    Matrix.exponentialEntry A i j = NormedSpace.exp A i j := by
  unfold Matrix.exponentialEntry
  rw [show NormedSpace.exp A =
      ∑' n : ℕ, ((n.factorial : ℝ)⁻¹) • A ^ n from
    congrFun (NormedSpace.exp_eq_tsum ℝ) A]
  have hs : Summable (fun n : ℕ => ((n.factorial : ℝ)⁻¹) • A ^ n) :=
    NormedSpace.expSeries_summable' (𝕂 := ℝ) A
  rw [tsum_apply hs, tsum_apply ((Pi.summable.mp hs) i)]
  apply tsum_congr
  intro n
  simp [one_div]

end MatrixOperatorNorm

/-- Exponentiating a scalar multiple of the matrix identity gives the scalar
exponential times the identity. -/
theorem exp_smul_matrix_one
    {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ℝ) :
    NormedSpace.exp (a • (1 : Matrix ι ι ℝ)) =
      Real.exp a • (1 : Matrix ι ι ℝ) := by
  rw [Matrix.smul_one_eq_diagonal, Matrix.exp_diagonal,
    Matrix.smul_one_eq_diagonal]
  congr 1
  funext i
  rw [Pi.coe_exp]
  exact (congrFun Real.exp_eq_exp_ℝ a).symm

/-- Scaling the random-scan influence by the total scan rate separates its
idle identity part from the genuine Dobrushin influence. -/
theorem card_smul_averagedInfluence
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (C : Matrix ι ι ℝ) (s : ℝ) :
    ((Fintype.card ι : ℝ) * s) • averagedInfluence C =
      (((Fintype.card ι : ℝ) - 1) * s) • (1 : Matrix ι ι ℝ) +
        s • C := by
  classical
  ext j i
  have hm0 : (Fintype.card ι : ℝ) ≠ 0 := by positivity
  change
    ((Fintype.card ι : ℝ) * s) *
        ((if j = i then ((Fintype.card ι : ℝ) - 1) /
          Fintype.card ι else 0) + C j i / Fintype.card ι) =
      (((Fintype.card ι : ℝ) - 1) * s) *
          (if j = i then 1 else 0) + s * C j i
  by_cases hji : j = i
  · subst i
    simp
    field_simp [hm0]
  · simp [hji]
    field_simp [hm0]

/-- Poissonizing one uniformly random single-site update at total rate `m`
removes the idle part of the random scan exactly.  This is the matrix identity
`e^{-ms} e^{ms((1-1/m)I+C/m)} = e^{-s} e^{sC}`. -/
theorem uniformized_averagedInfluence_exp
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (C : Matrix ι ι ℝ) (s : ℝ) :
    Real.exp (-((Fintype.card ι : ℝ) * s)) •
        NormedSpace.exp (((Fintype.card ι : ℝ) * s) • averagedInfluence C) =
      Real.exp (-s) • NormedSpace.exp (s • C) := by
  rw [card_smul_averagedInfluence]
  have hcomm :
      Commute
        ((((Fintype.card ι : ℝ) - 1) * s) • (1 : Matrix ι ι ℝ))
        (s • C) :=
    (Commute.one_left (s • C)).smul_left
      (((Fintype.card ι : ℝ) - 1) * s)
  rw [Matrix.exp_add_of_commute _ _ hcomm, exp_smul_matrix_one]
  rw [smul_mul_assoc, one_mul, smul_smul]
  have hscalar :
      Real.exp (-((Fintype.card ι : ℝ) * s)) *
          Real.exp (((Fintype.card ι : ℝ) - 1) * s) =
        Real.exp (-s) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hscalar]

/-- Entrywise physical-rate version of
`uniformized_averagedInfluence_exp`: running the averaged random scan at total
rate `|ι| * ρ` gives exactly the Dobrushin kernel at rate `ρ`. -/
theorem dobrushinKernelEntry_averagedInfluence
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (C : Matrix ι ι ℝ) (ρ t : ℝ) (j i : ι) :
    DobrushinInfluencePoissonTail.dobrushinKernelEntry
        (averagedInfluence C) 1
        ((Fintype.card ι : ℝ) * ρ * t) j i =
      DobrushinInfluencePoissonTail.dobrushinKernelEntry C ρ t j i := by
  unfold DobrushinInfluencePoissonTail.dobrushinKernelEntry
  rw [DobrushinInfluencePoissonTail.influenceExponentialEntry_eq_exponentialEntry_smul,
    DobrushinInfluencePoissonTail.influenceExponentialEntry_eq_exponentialEntry_smul,
    exponentialEntry_eq_exp_apply, exponentialEntry_eq_exp_apply]
  have hmatrix := congrArg (fun M : Matrix ι ι ℝ => M j i)
    (uniformized_averagedInfluence_exp C (ρ * t))
  simpa [mul_assoc] using hmatrix

theorem averagedInfluence_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (C : Matrix ι ι ℝ) (hC : ∀ j l, 0 ≤ C j l) :
    ∀ j l, 0 ≤ averagedInfluence C j l := by
  intro j l
  have hm : (0 : ℝ) < Fintype.card ι := by positivity
  have hm1 : (1 : ℝ) ≤ Fintype.card ι := by
    exact_mod_cast Fintype.card_pos
  unfold averagedInfluence
  by_cases hjl : j = l
  · rw [if_pos hjl]
    exact add_nonneg (div_nonneg (sub_nonneg.mpr hm1) hm.le)
      (div_nonneg (hC j l) hm.le)
  · rw [if_neg hjl, zero_add]
    exact div_nonneg (hC j l) hm.le

/-- If the original influence has column sums at most one, then so does the
random-scan influence `(1-1/m)I + C/m`. -/
theorem averagedInfluence_columnSum_le_one
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (C : Matrix ι ι ℝ) (hcol : ∀ i, ∑ j, C j i ≤ 1) :
    ∀ i, ∑ j, averagedInfluence C j i ≤ 1 := by
  classical
  intro i
  have hm : (0 : ℝ) < Fintype.card ι := by positivity
  have hm0 : (Fintype.card ι : ℝ) ≠ 0 := ne_of_gt hm
  unfold averagedInfluence
  rw [Finset.sum_add_distrib]
  have hdiag :
      (∑ j, if j = i then
          ((Fintype.card ι : ℝ) - 1) / Fintype.card ι else 0) =
        ((Fintype.card ι : ℝ) - 1) / Fintype.card ι := by
    simp
  rw [hdiag, ← Finset.sum_div]
  calc
    ((Fintype.card ι : ℝ) - 1) / Fintype.card ι +
        (∑ j, C j i) / Fintype.card ι ≤
      ((Fintype.card ι : ℝ) - 1) / Fintype.card ι +
        1 / Fintype.card ι :=
      add_le_add_right (div_le_div_of_nonneg_right (hcol i) hm.le) _
    _ = 1 := by
      field_simp [hm0]
      ring

/-- Averaging local heat-bath updates produces exactly the Dobrushin
one-step influence matrix. -/
theorem averageUpdate_oscillation
    {F ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [SeminormedAddCommGroup F] [NormedSpace ℝ F]
    (update : ι → F →ₗ[ℝ] F) (osc : ι → Seminorm ℝ F)
    (C : Matrix ι ι ℝ)
    (hsame : ∀ j f, osc j (update j f) ≤ ∑ l, C j l * osc l f)
    (hother : ∀ i j f, i ≠ j → osc j (update i f) ≤ osc j f) :
    ∀ j f,
      osc j (averageUpdate update f) ≤
        (Fintype.card ι : ℝ)⁻¹ *
          ((∑ l, C j l * osc l f) +
            ((Fintype.card ι : ℝ) - 1) * osc j f) := by
  intro j f
  let m : ℝ := Fintype.card ι
  have hm : 0 < m := by dsimp [m]; positivity
  have hsum :
      osc j (∑ i, update i f) ≤
        ∑ i, osc j (update i f) := by
    simpa using seminorm_finset_sum_le (osc j) Finset.univ
      (fun i => update i f)
  have hlocal :
      (∑ i, osc j (update i f)) ≤
        (∑ l, C j l * osc l f) + (m - 1) * osc j f := by
    calc
      (∑ i, osc j (update i f)) =
          osc j (update j f) + ∑ i ∈ Finset.univ.erase j,
            osc j (update i f) := by
              rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j), add_comm]
      _ ≤ (∑ l, C j l * osc l f) +
          ∑ _i ∈ Finset.univ.erase j, osc j f := by
            apply add_le_add (hsame j f)
            apply Finset.sum_le_sum
            intro i hi
            exact hother i j f (Finset.ne_of_mem_erase hi)
      _ = (∑ l, C j l * osc l f) + (m - 1) * osc j f := by
            have hcard : (Finset.univ.erase j).card = Fintype.card ι - 1 := by
              rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ]
            rw [Finset.sum_const, nsmul_eq_mul, hcard]
            have hcardPos : 0 < Fintype.card ι := Fintype.card_pos
            rw [Nat.cast_sub (Nat.succ_le_iff.mpr hcardPos)]
            dsimp [m]
            norm_num
  have hscaled :
      osc j (averageUpdate update f) ≤
        m⁻¹ * ((∑ l, C j l * osc l f) + (m - 1) * osc j f) := by
    unfold averageUpdate
    rw [LinearMap.smul_apply, map_smul_eq_mul, LinearMap.sum_apply]
    have habs : ‖m⁻¹‖ = m⁻¹ := by
      rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hm)]
    rw [habs]
    exact mul_le_mul_of_nonneg_left (hsum.trans hlocal) (inv_nonneg.mpr hm.le)
  exact hscaled

/-- Matrix form of `averageUpdate_oscillation`: the random-scan update is
controlled by `(1-1/m)I + C/m` exactly. -/
theorem averageUpdate_oscillation_averagedInfluence
    {F ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [SeminormedAddCommGroup F] [NormedSpace ℝ F]
    (update : ι → F →ₗ[ℝ] F) (osc : ι → Seminorm ℝ F)
    (C : Matrix ι ι ℝ)
    (hsame : ∀ j f, osc j (update j f) ≤ ∑ l, C j l * osc l f)
    (hother : ∀ i j f, i ≠ j → osc j (update i f) ≤ osc j f) :
    ∀ j f,
      osc j (averageUpdate update f) ≤
        ∑ l, averagedInfluence C j l * osc l f := by
  classical
  intro j f
  have hm : (0 : ℝ) < Fintype.card ι := by positivity
  have hbase := averageUpdate_oscillation update osc C hsame hother j f
  calc
    osc j (averageUpdate update f) ≤
        (Fintype.card ι : ℝ)⁻¹ *
          ((∑ l, C j l * osc l f) +
            ((Fintype.card ι : ℝ) - 1) * osc j f) := hbase
    _ = ∑ l, averagedInfluence C j l * osc l f := by
      unfold averagedInfluence
      simp_rw [add_mul]
      rw [Finset.sum_add_distrib]
      have hdiag :
          (∑ l, (if j = l then
            ((Fintype.card ι : ℝ) - 1) / Fintype.card ι else 0) *
              osc l f) =
            (((Fintype.card ι : ℝ) - 1) / Fintype.card ι) * osc j f := by
        simp
      rw [hdiag]
      have hm0 : (Fintype.card ι : ℝ) ≠ 0 := ne_of_gt hm
      have hsumdiv :
          (∑ l, C j l / Fintype.card ι * osc l f) =
            (Fintype.card ι : ℝ)⁻¹ * ∑ l, C j l * osc l f := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro l _
        field_simp [hm0]
      rw [hsumdiv]
      field_simp [hm0]
      ring

/-- Heat-bath form of the one-step compiler.  Updating block `i` kills its
own oscillation and can add `C j i * δ_i(f)` to every other block `j` while
preserving the pre-existing `j`-oscillation. -/
theorem averageUpdate_oscillation_of_leakage
    {F ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [SeminormedAddCommGroup F] [NormedSpace ℝ F]
    (update : ι → F →ₗ[ℝ] F) (osc : ι → Seminorm ℝ F)
    (C : Matrix ι ι ℝ)
    (hdiag : ∀ j, C j j = 0)
    (hself : ∀ j f, osc j (update j f) = 0)
    (hleak : ∀ i j f, i ≠ j →
      osc j (update i f) ≤ osc j f + C j i * osc i f) :
    ∀ j f,
      osc j (averageUpdate update f) ≤
        ∑ i, averagedInfluence C j i * osc i f := by
  classical
  intro j f
  let m : ℝ := Fintype.card ι
  have hm : 0 < m := by dsimp [m]; positivity
  have hsum :
      osc j (∑ i, update i f) ≤ ∑ i, osc j (update i f) := by
    simpa using seminorm_finset_sum_le (osc j) Finset.univ
      (fun i => update i f)
  have herase :
      (∑ i ∈ Finset.univ.erase j, C j i * osc i f) =
        ∑ i, C j i * osc i f := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)]
    simp [hdiag]
  have hcard : (Finset.univ.erase j).card = Fintype.card ι - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ]
  have hlocal :
      (∑ i, osc j (update i f)) ≤
        (∑ i, C j i * osc i f) + (m - 1) * osc j f := by
    calc
      (∑ i, osc j (update i f)) =
          osc j (update j f) +
            ∑ i ∈ Finset.univ.erase j, osc j (update i f) := by
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j), add_comm]
      _ = ∑ i ∈ Finset.univ.erase j, osc j (update i f) := by
        rw [hself, zero_add]
      _ ≤ ∑ i ∈ Finset.univ.erase j,
          (osc j f + C j i * osc i f) := by
        apply Finset.sum_le_sum
        intro i hi
        exact hleak i j f (Finset.ne_of_mem_erase hi)
      _ = (∑ i, C j i * osc i f) + (m - 1) * osc j f := by
        rw [Finset.sum_add_distrib, herase]
        rw [Finset.sum_const, nsmul_eq_mul, hcard]
        have hcardPos : 0 < Fintype.card ι := Fintype.card_pos
        rw [Nat.cast_sub (Nat.succ_le_iff.mpr hcardPos)]
        dsimp [m]
        ring
  have hscaled :
      osc j (averageUpdate update f) ≤
        m⁻¹ * ((∑ i, C j i * osc i f) + (m - 1) * osc j f) := by
    unfold averageUpdate
    rw [LinearMap.smul_apply, map_smul_eq_mul, LinearMap.sum_apply]
    have habs : ‖m⁻¹‖ = m⁻¹ := by
      rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hm)]
    rw [habs]
    exact mul_le_mul_of_nonneg_left (hsum.trans hlocal) (inv_nonneg.mpr hm.le)
  calc
    osc j (averageUpdate update f) ≤
        m⁻¹ * ((∑ i, C j i * osc i f) + (m - 1) * osc j f) := hscaled
    _ = ∑ i, averagedInfluence C j i * osc i f := by
      dsimp [m]
      unfold averagedInfluence
      simp_rw [add_mul]
      rw [Finset.sum_add_distrib]
      have hdiagSum :
          (∑ i, (if j = i then
            ((Fintype.card ι : ℝ) - 1) / Fintype.card ι else 0) *
              osc i f) =
            (((Fintype.card ι : ℝ) - 1) / Fintype.card ι) * osc j f := by
        simp
      rw [hdiagSum]
      have hm0 : (Fintype.card ι : ℝ) ≠ 0 := by positivity
      have hsumdiv :
          (∑ i, C j i / Fintype.card ι * osc i f) =
            (Fintype.card ι : ℝ)⁻¹ * ∑ i, C j i * osc i f := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        field_simp [hm0]
      rw [hsumdiv]
      field_simp [hm0]
      ring

/-- A one-step componentwise seminorm bound iterates with the corresponding
matrix powers.  This is the discrete-time core of the Dobrushin semigroup
estimate. -/
theorem iterate_oscillation_le_matrixPower
    {F ι : Type*} [Fintype ι] [DecidableEq ι]
    [SeminormedAddCommGroup F] [NormedSpace ℝ F]
    (T : F →ₗ[ℝ] F) (osc : ι → Seminorm ℝ F) (A : Matrix ι ι ℝ)
    (hA : ∀ j i, 0 ≤ A j i)
    (hstep : ∀ j f, osc j (T f) ≤ ∑ i, A j i * osc i f) :
    ∀ n j f, osc j ((T ^ n) f) ≤ ∑ i, (A ^ n) j i * osc i f := by
  classical
  intro n
  induction n with
  | zero =>
      intro j f
      simp [Matrix.one_apply]
  | succ n ih =>
      intro j f
      have hpowNonneg :=
        DobrushinInfluencePoissonTail.influence_power_nonneg A hA
      calc
        osc j ((T ^ (n + 1)) f) = osc j ((T ^ n) (T f)) := by
          rw [pow_succ]
          rfl
        _ ≤ ∑ k, (A ^ n) j k * osc k (T f) := ih j (T f)
        _ ≤ ∑ k, (A ^ n) j k * (∑ i, A k i * osc i f) := by
          apply Finset.sum_le_sum
          intro k _
          exact mul_le_mul_of_nonneg_left (hstep k f) (hpowNonneg n j k)
        _ = ∑ i, (A ^ (n + 1)) j i * osc i f := by
          rw [pow_succ]
          simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro k _
          ring

/-- A continuous seminorm of an absolutely convergent series is at most the
sum of the termwise seminorms. -/
theorem seminorm_tsum_le_tsum
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (p : Seminorm ℝ F) (hp : Continuous (p : F → ℝ)) (f : ℕ → F)
    (hf : Summable f) (hpf : Summable fun n => p (f n)) :
    p (∑' n, f n) ≤ ∑' n, p (f n) := by
  apply le_of_tendsto_of_tendsto'
    (hp.tendsto _ |>.comp hf.hasSum.tendsto_sum_nat)
    hpf.hasSum.tendsto_sum_nat
  intro n
  simpa using seminorm_finset_sum_le p (Finset.range n) f

/-- The uniformized continuous-time update obtained by a Poisson number of
applications of the discrete update `T`. -/
noncomputable def poissonizedUpdate
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : F →ₗ[ℝ] F) (s : ℝ) (f : F) : F :=
  Real.exp (-s) • ∑' n : ℕ, (s ^ n / n.factorial) • (T ^ n) f

/-- Discrete Dobrushin domination passes through uniformization: the
Poissonized update is controlled componentwise by
`exp(-s) exp(sA)`.  The two summability hypotheses are automatic for bounded
maps on the finite-dimensional field spaces used in the manuscript. -/
theorem poissonizedUpdate_oscillation_le_dobrushinKernel
    {F ι : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : F →ₗ[ℝ] F) (osc : ι → Seminorm ℝ F) (A : Matrix ι ι ℝ)
    (hA : ∀ j i, 0 ≤ A j i)
    (hstep : ∀ j f, osc j (T f) ≤ ∑ i, A j i * osc i f)
    (hosc : ∀ j, Continuous (osc j : F → ℝ))
    (s : ℝ) (hs : 0 ≤ s) (f : F)
    (hFsum : Summable fun n : ℕ =>
      (s ^ n / n.factorial) • (T ^ n) f)
    (hRsum : ∀ j, Summable fun n : ℕ =>
      ∑ i, (s ^ n / n.factorial) * (A ^ n) j i * osc i f)
    (hEntrySum : ∀ j i, Summable fun n : ℕ =>
      ((s ^ n / n.factorial) * (A ^ n) j i) * osc i f) :
    ∀ j,
      osc j (poissonizedUpdate T s f) ≤
        ∑ i,
          DobrushinInfluencePoissonTail.dobrushinKernelEntry A 1 s j i *
            osc i f := by
  classical
  intro j
  let u : ℕ → F := fun n => (s ^ n / n.factorial) • (T ^ n) f
  let r : ℕ → ℝ := fun n =>
    ∑ i, (s ^ n / n.factorial) * (A ^ n) j i * osc i f
  have hcoef (n : ℕ) : 0 ≤ s ^ n / (n.factorial : ℝ) := by positivity
  have hterm (n : ℕ) : osc j (u n) ≤ r n := by
    dsimp only [u, r]
    rw [map_smul_eq_mul, Real.norm_eq_abs, abs_of_nonneg (hcoef n)]
    calc
      (s ^ n / n.factorial) * osc j ((T ^ n) f) ≤
          (s ^ n / n.factorial) *
            (∑ i, (A ^ n) j i * osc i f) :=
        mul_le_mul_of_nonneg_left
          (iterate_oscillation_le_matrixPower T osc A hA hstep n j f)
          (hcoef n)
      _ = ∑ i, (s ^ n / n.factorial) * (A ^ n) j i * osc i f := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
  have hOscSum : Summable fun n => osc j (u n) := by
    exact Summable.of_nonneg_of_le (fun n => apply_nonneg (osc j) (u n))
      hterm (hRsum j)
  have hseriesBound : osc j (∑' n, u n) ≤ ∑' n, r n :=
    (seminorm_tsum_le_tsum (osc j) (hosc j) u hFsum hOscSum).trans
      (hOscSum.tsum_le_tsum hterm (hRsum j))
  unfold poissonizedUpdate
  rw [map_smul_eq_mul, Real.norm_eq_abs,
    abs_of_nonneg (Real.exp_nonneg (-s))]
  calc
    Real.exp (-s) * osc j (∑' n, u n) ≤
        Real.exp (-s) * ∑' n, r n :=
      mul_le_mul_of_nonneg_left hseriesBound (Real.exp_nonneg _)
    _ = Real.exp (-s) *
        ∑ i, (∑' n : ℕ,
          ((s ^ n / n.factorial) * (A ^ n) j i) * osc i f) := by
      rw [Summable.tsum_finsetSum (fun i _ => hEntrySum j i)]
    _ = ∑ i,
        DobrushinInfluencePoissonTail.dobrushinKernelEntry A 1 s j i *
          osc i f := by
      unfold DobrushinInfluencePoissonTail.dobrushinKernelEntry
      rw [one_mul]
      unfold OperationalLightConeExponential.influenceExponentialEntry
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [tsum_mul_right]
      ring

/-- A nonnegative influence matrix with a uniform column bound has absolutely
convergent entrywise exponential series. -/
theorem influenceEntrySeries_summable
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (α s : ℝ)
    (hA : ∀ j i, 0 ≤ A j i) (hα : 0 ≤ α) (hs : 0 ≤ s)
    (hcol : ∀ i, ∑ j, A j i ≤ α) (j i : ι) :
    Summable fun n : ℕ => (s ^ n / n.factorial) * (A ^ n) j i := by
  let term : ℕ → ℝ := fun n => (s ^ n / n.factorial) * (A ^ n) j i
  let major : ℕ → ℝ := fun n => (s * α) ^ n / n.factorial
  have hpow0 := DobrushinInfluencePoissonTail.influence_power_nonneg A hA
  have hpowBound :=
    DobrushinInfluencePoissonTail.influence_power_le_columnBound
      A α hA hα hcol
  have hterm0 : ∀ n, 0 ≤ term n := fun n =>
    mul_nonneg (by positivity) (hpow0 n j i)
  have htermMajor : ∀ n, term n ≤ major n := by
    intro n
    dsimp only [term, major]
    calc
      (s ^ n / n.factorial) * (A ^ n) j i ≤
          (s ^ n / n.factorial) * α ^ n :=
        mul_le_mul_of_nonneg_left (hpowBound n j i) (by positivity)
      _ = (s * α) ^ n / n.factorial := by rw [mul_pow]; ring
  exact Summable.of_nonneg_of_le hterm0 htermMajor
    (Real.summable_pow_div_factorial _)

/-- On a finite-dimensional normed field space, the exponential series of
every linear endomorphism converges absolutely on every vector. -/
theorem poissonSeries_summable_of_finiteDimensional
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] (T : F →ₗ[ℝ] F) (s : ℝ) (f : F) :
    Summable fun n : ℕ => (s ^ n / n.factorial) • (T ^ n) f := by
  let Tc : F →L[ℝ] F := Module.End.toContinuousLinearMap F T
  have hpowApply (n : ℕ) : (Tc ^ n) f = (T ^ n) f := by
    have hpow := map_pow (Module.End.toContinuousLinearMap F) T n
    exact congrArg (fun S : F →L[ℝ] F => S f) hpow.symm
  have hnormPow (n : ℕ) : ‖Tc ^ n‖ ≤ ‖Tc‖ ^ n := by
    cases n with
    | zero =>
        change ‖(1 : F →L[ℝ] F)‖ ≤ 1
        rw [ContinuousLinearMap.one_def]
        exact ContinuousLinearMap.norm_id_le
    | succ n => exact norm_pow_le' Tc (Nat.succ_pos n)
  have hbound (n : ℕ) :
      ‖(s ^ n / n.factorial) • (T ^ n) f‖ ≤
        ‖f‖ * ((|s| * ‖Tc‖) ^ n / n.factorial) := by
    have hcoefnorm : ‖s ^ n / (n.factorial : ℝ)‖ =
        |s| ^ n / n.factorial := by
      simp [Real.norm_eq_abs, abs_div, abs_pow]
    rw [norm_smul, hcoefnorm]
    have hcoef : 0 ≤ |s| ^ n / (n.factorial : ℝ) := by positivity
    calc
      (|s| ^ n / n.factorial) * ‖(T ^ n) f‖ =
          (|s| ^ n / n.factorial) * ‖(Tc ^ n) f‖ := by rw [hpowApply]
      _ ≤ (|s| ^ n / n.factorial) * (‖Tc ^ n‖ * ‖f‖) :=
        mul_le_mul_of_nonneg_left ((Tc ^ n).le_opNorm f) hcoef
      _ ≤ (|s| ^ n / n.factorial) * (‖Tc‖ ^ n * ‖f‖) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (hnormPow n) (norm_nonneg f)) hcoef
      _ = ‖f‖ * ((|s| * ‖Tc‖) ^ n / n.factorial) := by
        rw [mul_pow]
        ring
  exact Summable.of_norm_bounded
    ((Real.summable_pow_div_factorial (|s| * ‖Tc‖)).mul_left ‖f‖) hbound

/-- Column control supplies all scalar convergence premises of
`poissonizedUpdate_oscillation_le_dobrushinKernel`. -/
theorem poissonizedUpdate_oscillation_le_dobrushinKernel_of_columnBound
    {F ι : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : F →ₗ[ℝ] F) (osc : ι → Seminorm ℝ F) (A : Matrix ι ι ℝ)
    (α : ℝ) (hA : ∀ j i, 0 ≤ A j i) (hα : 0 ≤ α)
    (hcol : ∀ i, ∑ j, A j i ≤ α)
    (hstep : ∀ j f, osc j (T f) ≤ ∑ i, A j i * osc i f)
    (hosc : ∀ j, Continuous (osc j : F → ℝ))
    (s : ℝ) (hs : 0 ≤ s) (f : F)
    (hFsum : Summable fun n : ℕ =>
      (s ^ n / n.factorial) • (T ^ n) f) :
    ∀ j,
      osc j (poissonizedUpdate T s f) ≤
        ∑ i,
          DobrushinInfluencePoissonTail.dobrushinKernelEntry A 1 s j i *
            osc i f := by
  classical
  have hEntry (j i : ι) : Summable fun n : ℕ =>
      ((s ^ n / n.factorial) * (A ^ n) j i) * osc i f :=
    (influenceEntrySeries_summable A α s hA hα hs hcol j i).mul_right _
  have hR (j : ι) : Summable fun n : ℕ =>
      ∑ i, (s ^ n / n.factorial) * (A ^ n) j i * osc i f := by
    refine ⟨∑ i, ∑' n : ℕ,
      ((s ^ n / n.factorial) * (A ^ n) j i) * osc i f, hasSum_sum ?_⟩
    intro i _
    exact (hEntry j i).hasSum
  exact poissonizedUpdate_oscillation_le_dobrushinKernel
    T osc A hA hstep hosc s hs f hFsum hR hEntry

/-- Fully automatic finite-dimensional version of the uniformized Dobrushin
semigroup estimate. -/
theorem finiteDimensional_poissonizedUpdate_oscillation
    {F ι : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (T : F →ₗ[ℝ] F) (osc : ι → Seminorm ℝ F) (A : Matrix ι ι ℝ)
    (α : ℝ) (hA : ∀ j i, 0 ≤ A j i) (hα : 0 ≤ α)
    (hcol : ∀ i, ∑ j, A j i ≤ α)
    (hstep : ∀ j f, osc j (T f) ≤ ∑ i, A j i * osc i f)
    (hosc : ∀ j, Continuous (osc j : F → ℝ))
    (s : ℝ) (hs : 0 ≤ s) (f : F) :
    ∀ j,
      osc j (poissonizedUpdate T s f) ≤
        ∑ i,
          DobrushinInfluencePoissonTail.dobrushinKernelEntry A 1 s j i *
            osc i f := by
  exact poissonizedUpdate_oscillation_le_dobrushinKernel_of_columnBound
    T osc A α hA hα hcol hstep hosc s hs f
      (poissonSeries_summable_of_finiteDimensional T s f)

/-- Fully normalized finite-dimensional random-scan Dobrushin compiler.
Single-site updates with influence `C`, Poissonized at total rate
`|ι| * ρ`, are controlled by the manuscript kernel
`exp(-ρt(I-C))` entry by entry. -/
theorem finiteDimensional_randomScan_oscillation
    {F ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (update : ι → F →ₗ[ℝ] F) (osc : ι → Seminorm ℝ F)
    (C : Matrix ι ι ℝ)
    (hC : ∀ j i, 0 ≤ C j i)
    (hcol : ∀ i, ∑ j, C j i ≤ 1)
    (hdiag : ∀ j, C j j = 0)
    (hself : ∀ j f, osc j (update j f) = 0)
    (hleak : ∀ i j f, i ≠ j →
      osc j (update i f) ≤ osc j f + C j i * osc i f)
    (hosc : ∀ j, Continuous (osc j : F → ℝ))
    (ρ t : ℝ) (hρ : 0 ≤ ρ) (ht : 0 ≤ t) (f : F) :
    ∀ j,
      osc j (poissonizedUpdate (averageUpdate update)
          ((Fintype.card ι : ℝ) * ρ * t) f) ≤
        ∑ i,
          DobrushinInfluencePoissonTail.dobrushinKernelEntry C ρ t j i *
            osc i f := by
  classical
  intro j
  have hs : 0 ≤ (Fintype.card ι : ℝ) * ρ * t :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hρ) ht
  have hbound := finiteDimensional_poissonizedUpdate_oscillation
    (averageUpdate update) osc (averagedInfluence C) 1
    (averagedInfluence_nonneg C hC) (by positivity)
    (averagedInfluence_columnSum_le_one C hcol)
    (averageUpdate_oscillation_of_leakage update osc C hdiag hself hleak)
    hosc ((Fintype.card ι : ℝ) * ρ * t) hs f j
  calc
    osc j (poissonizedUpdate (averageUpdate update)
        ((Fintype.card ι : ℝ) * ρ * t) f) ≤
      ∑ i,
        DobrushinInfluencePoissonTail.dobrushinKernelEntry
            (averagedInfluence C) 1
            ((Fintype.card ι : ℝ) * ρ * t) j i * osc i f := hbound
    _ = ∑ i,
        DobrushinInfluencePoissonTail.dobrushinKernelEntry C ρ t j i *
          osc i f := by
      apply Finset.sum_congr rfl
      intro i _
      rw [dobrushinKernelEntry_averagedInfluence]

/-- Once approximate tensorization is available, the heat-bath Dirichlet
identity yields the claimed gap by exact scalar algebra. -/
theorem heatBath_gap_of_approximateTensorization
    (energy localVariance variance ρ α : ℝ)
    (hρ : 0 ≤ ρ) (hvar : 0 ≤ variance)
    (henergy : energy = ρ * localVariance)
    (hAT : (1 - α) * variance ≤ localVariance) :
    ρ * (1 - α) * variance ≤ energy := by
  calc
    ρ * (1 - α) * variance = ρ * ((1 - α) * variance) := by ring
    _ ≤ ρ * localVariance := mul_le_mul_of_nonneg_left hAT hρ
    _ = energy := henergy.symm

end FiniteHeatBathDobrushin
end NCG
