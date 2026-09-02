/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteHeatBathDobrushin
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# From Dobrushin influence decay to a finite spectral gap

This file supplies the remaining abstract bridge in
`thm:SMFS-Dobrushin-gap`.  On the mean-zero finite field space, a separating
family of block oscillation seminorms turns one-step Dobrushin decay into a
lower bound for every eigenvalue of the positive self-adjoint heat-bath
operator.  Parseval then gives the Poincare inequality.

The argument is deliberately independent of coordinates and of a particular
Gibbs parametrization.  The concrete random-scan compiler provides `P` and
`K`; reversibility provides positivity and symmetry of `A`.
-/

open scoped BigOperators RealInnerProductSpace

noncomputable section

namespace NCG

namespace FiniteHeatBathDobrushin

/-- The Poissonized update acts on an eigenvector by the expected scalar
semigroup factor.  This discharges the generator/semigroup compatibility used
by the spectral-gap bridge. -/
theorem poissonizedUpdate_eigenvector
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : F →ₗ[ℝ] F) (v : F) (θ s : ℝ) (hTv : T v = θ • v) :
    poissonizedUpdate T s v = Real.exp (s * (θ - 1)) • v := by
  have hpow : ∀ n : ℕ, (T ^ n) v = θ ^ n • v := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ]
        change (T ^ n) (T v) = _
        rw [hTv, map_smul, ih, pow_succ]
        simp [smul_smul, mul_comm]
  unfold poissonizedUpdate
  simp_rw [hpow, smul_smul]
  have hseries :
      HasSum (fun n : ℕ => ((s * θ) ^ n / n.factorial) • v)
        (NormedSpace.exp (s * θ) • v) :=
    (NormedSpace.expSeries_div_hasSum_exp (s * θ)).smul_const v
  have hterm (n : ℕ) :
      (s ^ n / (n.factorial : ℝ) * θ ^ n) • v =
        ((s * θ) ^ n / n.factorial) • v := by
    congr 1
    rw [mul_pow]
    ring
  simp_rw [hterm]
  rw [hseries.tsum_eq, smul_smul]
  rw [show NormedSpace.exp (s * θ) = Real.exp (s * θ) from
    (congrFun Real.exp_eq_exp_ℝ (s * θ)).symm]
  rw [← Real.exp_add]
  congr 1
  ring

/-- The positive random-scan generator `ρ |I| (I-T)`. -/
def heatBathPositiveGenerator
    {F ι : Type*} [Fintype ι] [SeminormedAddCommGroup F]
    [NormedSpace ℝ F] (update : ι → F →ₗ[ℝ] F) (ρ : ℝ) : F →ₗ[ℝ] F :=
  ((Fintype.card ι : ℝ) * ρ) •
    (LinearMap.id - averageUpdate update)

/-- An orthogonal conditional expectation has positive complement. -/
theorem id_sub_isPositive_of_symmetric_idempotent
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (K : F →ₗ[ℝ] F) (hsym : K.IsSymmetric) (hidem : K * K = K) :
    (LinearMap.id - K).IsPositive := by
  refine ⟨LinearMap.IsSymmetric.id.sub hsym, ?_⟩
  intro x
  have horth : inner ℝ (x - K x) (K x) = 0 := by
    rw [inner_sub_left, hsym]
    have happ := congrArg (fun T : F →ₗ[ℝ] F => T x) hidem
    change K (K x) = K x at happ
    rw [happ, sub_self]
  have hsplit : x = (x - K x) + K x := by abel
  change 0 ≤ inner ℝ (x - K x) x
  have heq : inner ℝ (x - K x) x =
      inner ℝ (x - K x) ((x - K x) + K x) :=
    congrArg (fun y => inner ℝ (x - K x) y) hsplit
  rw [heq, inner_add_right, horth, add_zero]
  exact real_inner_self_nonneg

/-- The normalized random-scan generator is the scan-rate multiple of the
sum of the positive single-site complements. -/
theorem heatBathPositiveGenerator_eq_sum
    {F ι : Type*} [Fintype ι] [Nonempty ι]
    [SeminormedAddCommGroup F] [NormedSpace ℝ F]
    (update : ι → F →ₗ[ℝ] F) (ρ : ℝ) :
    heatBathPositiveGenerator update ρ =
      ρ • ∑ i, (LinearMap.id - update i) := by
  classical
  ext f
  have hm0 : (Fintype.card ι : ℝ) ≠ 0 := by positivity
  simp [heatBathPositiveGenerator, averageUpdate, Finset.smul_sum,
    smul_sub, Finset.sum_sub_distrib, hm0]
  have hscale :
      (Fintype.card ι : ℝ) * ρ * (Fintype.card ι : ℝ)⁻¹ = ρ := by
    field_simp [hm0]
  simp only [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  rw [hscale]
  ring

/-- Reversible single-site conditional expectations make the heat-bath
generator positive self-adjoint. -/
theorem heatBathPositiveGenerator_isPositive
    {F ι : Type*} [Fintype ι] [Nonempty ι]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (update : ι → F →ₗ[ℝ] F) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hsym : ∀ i, (update i).IsSymmetric)
    (hidem : ∀ i, update i * update i = update i) :
    (heatBathPositiveGenerator update ρ).IsPositive := by
  rw [heatBathPositiveGenerator_eq_sum]
  apply LinearMap.IsPositive.smul_of_nonneg
  · exact LinearMap.isPositive_sum Finset.univ fun i _ =>
      id_sub_isPositive_of_symmetric_idempotent (update i) (hsym i) (hidem i)
  · exact hρ

/-- For positive scan rate, the Poissonized random scan is definitionally the
time-one semigroup of `heatBathPositiveGenerator` on every spectral mode. -/
theorem poissonizedUpdate_eigenvectorBasis_heatBathPositiveGenerator
    {F ι : Type*} [Fintype ι] [Nonempty ι]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F]
    (update : ι → F →ₗ[ℝ] F) (ρ : ℝ) (hρ : 0 < ρ)
    (hA : (heatBathPositiveGenerator update ρ).IsSymmetric)
    {n : ℕ} (hn : Module.finrank ℝ F = n) (i : Fin n) :
    poissonizedUpdate (averageUpdate update)
        ((Fintype.card ι : ℝ) * ρ)
        (hA.eigenvectorBasis hn i) =
      Real.exp (-(hA.eigenvalues hn i)) • hA.eigenvectorBasis hn i := by
  let rate : ℝ := (Fintype.card ι : ℝ) * ρ
  let v : F := hA.eigenvectorBasis hn i
  let eig : ℝ := hA.eigenvalues hn i
  have hrate : 0 < rate := mul_pos (by positivity) hρ
  have heq := hA.apply_eigenvectorBasis hn i
  have heq' : rate • (v - averageUpdate update v) = eig • v := by
    simpa [heatBathPositiveGenerator, rate, v, eig,
      LinearMap.sub_apply] using heq
  have hscaled := congrArg (fun w : F => rate⁻¹ • w) heq'
  have hdiff : v - averageUpdate update v = (rate⁻¹ * eig) • v := by
    simpa [smul_smul, hrate.ne'] using hscaled
  have hTv : averageUpdate update v = (1 - rate⁻¹ * eig) • v := by
    have hvdecomp : v = (rate⁻¹ * eig) • v + averageUpdate update v :=
      (sub_eq_iff_eq_add).mp hdiff
    calc
      averageUpdate update v = v - (rate⁻¹ * eig) • v := by
        apply (eq_sub_iff_add_eq).2
        simpa [add_comm] using hvdecomp.symm
      _ = (1 - rate⁻¹ * eig) • v := by
        rw [sub_smul, one_smul]
  have hmode := poissonizedUpdate_eigenvector
    (averageUpdate update) v (1 - rate⁻¹ * eig) rate hTv
  have hexponent : rate * (1 - rate⁻¹ * eig - 1) = -eig := by
    field_simp [hrate.ne']
    ring
  rw [hexponent] at hmode
  simpa [rate, v, eig] using hmode

end FiniteHeatBathDobrushin

namespace DobrushinInfluencePoissonTail

open OperationalLightConeExponential

/-- A Dobrushin column bound propagates sharply to every matrix power. -/
theorem influence_power_columnSum_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℝ) (α : ℝ)
    (hC : ∀ j i, 0 ≤ C j i) (hα : 0 ≤ α)
    (hcol : ∀ i, ∑ j, C j i ≤ α) :
    ∀ n i, ∑ j, (C ^ n) j i ≤ α ^ n := by
  classical
  intro n
  induction n with
  | zero =>
      intro i
      simp [Matrix.one_apply]
  | succ n ih =>
      intro i
      have hpow := influence_power_nonneg C hC n
      rw [pow_succ]
      simp_rw [Matrix.mul_apply]
      rw [Finset.sum_comm]
      calc
        ∑ l, ∑ j, (C ^ n) j l * C l i =
            ∑ l, (∑ j, (C ^ n) j l) * C l i := by
          apply Finset.sum_congr rfl
          intro l _
          rw [Finset.sum_mul]
        _ ≤ ∑ l, α ^ n * C l i := by
          apply Finset.sum_le_sum
          intro l _
          exact mul_le_mul_of_nonneg_right (ih l) (hC l i)
        _ = α ^ n * ∑ l, C l i := by rw [Finset.mul_sum]
        _ ≤ α ^ n * α :=
          mul_le_mul_of_nonneg_left (hcol i) (pow_nonneg hα n)
        _ = α ^ (n + 1) := by rw [pow_succ]

/-- The total mass in each column of the influence exponential is bounded by
the scalar exponential of the Dobrushin column norm. -/
theorem influenceExponential_columnSum_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℝ) (α s : ℝ)
    (hC : ∀ j i, 0 ≤ C j i) (hα : 0 ≤ α) (hs : 0 ≤ s)
    (hcol : ∀ i, ∑ j, C j i ≤ α) (i : ι) :
    ∑ j, influenceExponentialEntry C s j i ≤ Real.exp (s * α) := by
  classical
  let term : ℕ → ℝ := fun n =>
    ∑ j, (s ^ n / n.factorial) * (C ^ n) j i
  let major : ℕ → ℝ := fun n => (s * α) ^ n / n.factorial
  have hentry (j : ι) : Summable fun n : ℕ =>
      (s ^ n / n.factorial) * (C ^ n) j i :=
    FiniteHeatBathDobrushin.influenceEntrySeries_summable
      C α s hC hα hs hcol j i
  have hswap :
      (∑ j, ∑' n : ℕ, (s ^ n / n.factorial) * (C ^ n) j i) =
        ∑' n : ℕ, term n := by
    exact (hasSum_sum fun j (_hj : j ∈ (Finset.univ : Finset ι)) =>
      (hentry j).hasSum).tsum_eq.symm
  have hterm0 (n : ℕ) : 0 ≤ term n := by
    exact Finset.sum_nonneg fun j _ =>
      mul_nonneg (by positivity) (influence_power_nonneg C hC n j i)
  have htermMajor (n : ℕ) : term n ≤ major n := by
    dsimp only [term, major]
    rw [← Finset.mul_sum]
    calc
      (s ^ n / n.factorial) * ∑ j, (C ^ n) j i ≤
          (s ^ n / n.factorial) * α ^ n :=
        mul_le_mul_of_nonneg_left
          (influence_power_columnSum_le C α hC hα hcol n i) (by positivity)
      _ = (s * α) ^ n / n.factorial := by rw [mul_pow]; ring
  have htermSum : Summable term :=
    Summable.of_nonneg_of_le hterm0 htermMajor
      (Real.summable_pow_div_factorial _)
  have hmajorSum : ∑' n : ℕ, major n = Real.exp (s * α) := by
    rw [show Real.exp (s * α) = NormedSpace.exp (s * α) from
      congrFun Real.exp_eq_exp_ℝ (s * α)]
    exact (NormedSpace.expSeries_div_hasSum_exp (s * α)).tsum_eq
  unfold influenceExponentialEntry
  rw [hswap]
  rw [← hmajorSum]
  exact htermSum.tsum_le_tsum htermMajor
    (Real.summable_pow_div_factorial _)

/-- The uniformized Dobrushin kernel has column mass at most
`exp (-ρ t (1-α))`. -/
theorem dobrushinKernel_columnSum_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℝ) (α ρ t : ℝ)
    (hC : ∀ j i, 0 ≤ C j i) (hα : 0 ≤ α)
    (hρ : 0 ≤ ρ) (ht : 0 ≤ t)
    (hcol : ∀ i, ∑ j, C j i ≤ α) (i : ι) :
    ∑ j, dobrushinKernelEntry C ρ t j i ≤
      Real.exp (-(ρ * t * (1 - α))) := by
  unfold dobrushinKernelEntry
  rw [← Finset.mul_sum]
  calc
    Real.exp (-(ρ * t)) * ∑ j, influenceExponentialEntry C (ρ * t) j i ≤
        Real.exp (-(ρ * t)) * Real.exp ((ρ * t) * α) :=
      mul_le_mul_of_nonneg_left
        (influenceExponential_columnSum_le C α (ρ * t) hC hα
          (mul_nonneg hρ ht) hcol i) (Real.exp_nonneg _)
    _ = Real.exp (-(ρ * t * (1 - α))) := by
      rw [← Real.exp_add]
      congr 1
      ring

end DobrushinInfluencePoissonTail

namespace DobrushinSpectralGapBridge

variable {F ι : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [Fintype ι]

/-- A separating finite family of seminorms has strictly positive total
oscillation on every nonzero vector. -/
theorem sum_seminorm_pos_of_ne_zero (osc : ι → Seminorm ℝ F)
    (hsep : ∀ f, (∀ j, osc j f = 0) → f = 0) {f : F} (hf : f ≠ 0) :
    0 < ∑ j, osc j f := by
  have hnonneg : 0 ≤ ∑ j, osc j f :=
    Finset.sum_nonneg fun j _ => apply_nonneg (osc j) f
  refine lt_of_le_of_ne hnonneg ?_
  intro hzero
  apply hf
  apply hsep f
  intro j
  have hjnonneg : 0 ≤ osc j f := apply_nonneg (osc j) f
  have hjle : osc j f ≤ ∑ k, osc k f :=
    Finset.single_le_sum (fun k _ => apply_nonneg (osc k) f)
      (Finset.mem_univ j)
  exact le_antisymm (by simpa [hzero] using hjle) hjnonneg

/-- If a positive self-adjoint finite operator has a time-one semigroup whose
block oscillations are dominated by a nonnegative kernel with column mass
`exp (-γ)`, then every eigenvalue is at least `γ`. -/
theorem eigenvalue_ge_of_dobrushin_decay
    (A : F →ₗ[ℝ] F) (P : F → F) (hA : A.IsSymmetric)
    (osc : ι → Seminorm ℝ F) (K : Matrix ι ι ℝ) (γ : ℝ)
    (hcol : ∀ i, ∑ j, K j i ≤ Real.exp (-γ))
    (hsep : ∀ f, (∀ j, osc j f = 0) → f = 0)
    (hcontract : ∀ j f, osc j (P f) ≤ ∑ i, K j i * osc i f)
    {n : ℕ} (hn : Module.finrank ℝ F = n)
    (hPeigen : ∀ i : Fin n,
      P (hA.eigenvectorBasis hn i) =
        Real.exp (-(hA.eigenvalues hn i)) • hA.eigenvectorBasis hn i)
    (i : Fin n) :
    γ ≤ hA.eigenvalues hn i := by
  classical
  let b := hA.eigenvectorBasis hn
  let eig := hA.eigenvalues hn i
  let S : ℝ := ∑ j, osc j (b i)
  have hbi : b i ≠ 0 := by
    exact b.orthonormal.ne_zero i
  have hS : 0 < S := sum_seminorm_pos_of_ne_zero osc hsep hbi
  have hsumContract :
      ∑ j, osc j (P (b i)) ≤ Real.exp (-γ) * S := by
    calc
      ∑ j, osc j (P (b i)) ≤
          ∑ j, ∑ k, K j k * osc k (b i) :=
        Finset.sum_le_sum fun j _ => hcontract j (b i)
      _ = ∑ k, (∑ j, K j k) * osc k (b i) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.sum_mul]
      _ ≤ ∑ k, Real.exp (-γ) * osc k (b i) := by
        apply Finset.sum_le_sum
        intro k _
        exact mul_le_mul_of_nonneg_right (hcol k) (apply_nonneg _ _)
      _ = Real.exp (-γ) * S := by rw [Finset.mul_sum]
  have hleft :
      ∑ j, osc j (P (b i)) = Real.exp (-eig) * S := by
    rw [hPeigen i]
    simp [map_smul_eq_mul, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), eig, S, b, Finset.mul_sum]
  rw [hleft] at hsumContract
  have hexp : Real.exp (-eig) ≤ Real.exp (-γ) :=
    le_of_mul_le_mul_right hsumContract hS
  exact neg_le_neg_iff.mp (Real.exp_le_exp.mp hexp)

/-- **Dobrushin spectral-gap bridge.** Under the hypotheses above, positivity
and the finite spectral theorem upgrade the influence decay to the full
quadratic-form Poincare inequality `γ ‖f‖² ≤ ⟪Af,f⟫`. -/
theorem spectral_gap_of_dobrushin_decay
    (A : F →ₗ[ℝ] F) (P : F → F)
    (hA : A.IsSymmetric) (_hpos : A.IsPositive)
    (osc : ι → Seminorm ℝ F) (K : Matrix ι ι ℝ) (γ : ℝ)
    (hcol : ∀ i, ∑ j, K j i ≤ Real.exp (-γ))
    (hsep : ∀ f, (∀ j, osc j f = 0) → f = 0)
    (hcontract : ∀ j f, osc j (P f) ≤ ∑ i, K j i * osc i f)
    {n : ℕ} (hn : Module.finrank ℝ F = n)
    (hPeigen : ∀ i : Fin n,
      P (hA.eigenvectorBasis hn i) =
        Real.exp (-(hA.eigenvalues hn i)) • hA.eigenvectorBasis hn i) :
    ∀ f : F, γ * ‖f‖ ^ 2 ≤ inner ℝ (A f) f := by
  classical
  intro f
  let b := hA.eigenvectorBasis hn
  have heig (i : Fin n) : γ ≤ hA.eigenvalues hn i :=
    eigenvalue_ge_of_dobrushin_decay A P hA osc K γ hcol hsep
      hcontract hn hPeigen i
  have hAf :
      A f = ∑ i : Fin n,
        (hA.eigenvalues hn i * inner ℝ (b i) f) • b i := by
    conv_lhs => rw [← b.sum_repr' f]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul, hA.apply_eigenvectorBasis hn]
    simp [b, smul_smul, mul_comm]
  rw [hAf, sum_inner]
  simp_rw [inner_smul_left]
  rw [← b.sum_sq_inner_right f]
  calc
    γ * ∑ i : Fin n, inner ℝ (b i) f ^ 2 =
        ∑ i : Fin n, γ * inner ℝ (b i) f ^ 2 := by rw [Finset.mul_sum]
    _ ≤ ∑ i : Fin n,
        hA.eigenvalues hn i * inner ℝ (b i) f ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_right (heig i) (sq_nonneg _)
    _ = ∑ i : Fin n,
        hA.eigenvalues hn i * inner ℝ (b i) f * inner ℝ (b i) f := by
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- **Finite reversible heat-bath gap.** This is the direct FS.21--FS.24
compiler on the mean-zero field space.  The final hypothesis says that the
Poissonized random scan is the time-one semigroup of the positive
self-adjoint generator `A`; for finite conditional expectations this is the
standard generator identity `A = ρ ∑ i (I-Kᵢ)`. -/
theorem finiteHeatBath_gap_of_dobrushin
    [DecidableEq ι] [Nonempty ι]
    (update : ι → F →ₗ[ℝ] F) (osc : ι → Seminorm ℝ F)
    (C : Matrix ι ι ℝ) (α ρ : ℝ)
    (hC : ∀ j i, 0 ≤ C j i)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hcol : ∀ i, ∑ j, C j i ≤ α)
    (hdiag : ∀ j, C j j = 0)
    (hself : ∀ j f, osc j (update j f) = 0)
    (hleak : ∀ i j f, i ≠ j →
      osc j (update i f) ≤ osc j f + C j i * osc i f)
    (hosc : ∀ j, Continuous (osc j : F → ℝ))
    (hρ : 0 ≤ ρ)
    (A : F →ₗ[ℝ] F) (hA : A.IsSymmetric) (hApos : A.IsPositive)
    (hsep : ∀ f, (∀ j, osc j f = 0) → f = 0)
    {n : ℕ} (hn : Module.finrank ℝ F = n)
    (hsemigroup : ∀ i : Fin n,
      FiniteHeatBathDobrushin.poissonizedUpdate
          (FiniteHeatBathDobrushin.averageUpdate update)
          ((Fintype.card ι : ℝ) * ρ)
          (hA.eigenvectorBasis hn i) =
        Real.exp (-(hA.eigenvalues hn i)) • hA.eigenvectorBasis hn i) :
    ∀ f : F, ρ * (1 - α) * ‖f‖ ^ 2 ≤ inner ℝ (A f) f := by
  classical
  let P : F → F := fun f =>
    FiniteHeatBathDobrushin.poissonizedUpdate
      (FiniteHeatBathDobrushin.averageUpdate update)
      ((Fintype.card ι : ℝ) * ρ) f
  let K : Matrix ι ι ℝ := fun j i =>
    DobrushinInfluencePoissonTail.dobrushinKernelEntry C ρ 1 j i
  have hcolOne : ∀ i, ∑ j, C j i ≤ 1 := fun i => (hcol i).trans hα1
  have hcontract : ∀ j f, osc j (P f) ≤ ∑ i, K j i * osc i f := by
    intro j f
    simpa [P, K, mul_assoc] using
      FiniteHeatBathDobrushin.finiteDimensional_randomScan_oscillation
      update osc C hC hcolOne hdiag hself hleak hosc ρ 1 hρ
      (by norm_num) f j
  have hKcol : ∀ i, ∑ j, K j i ≤ Real.exp (-(ρ * (1 - α))) := by
    intro i
    simpa [K, mul_assoc] using
      DobrushinInfluencePoissonTail.dobrushinKernel_columnSum_le
        C α ρ 1 hC hα0 hρ (by norm_num) hcol i
  apply spectral_gap_of_dobrushin_decay A P hA hApos osc K
    (ρ * (1 - α)) hKcol hsep hcontract hn
  intro i
  exact hsemigroup i

/-- **FS.24 from the actual reversible heat-bath data.** On the mean-zero
finite observable space, reversible idempotent conditional expectations and
the protected Dobrushin column margin imply the regulator-uniform field gap.
No approximate-tensorization inequality is assumed: it is replaced by the
equivalent finite spectral argument above. -/
theorem finiteReversibleHeatBath_gap_of_dobrushin
    [DecidableEq ι] [Nonempty ι]
    (update : ι → F →ₗ[ℝ] F) (osc : ι → Seminorm ℝ F)
    (C : Matrix ι ι ℝ) (α ρ : ℝ)
    (hC : ∀ j i, 0 ≤ C j i)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hcol : ∀ i, ∑ j, C j i ≤ α)
    (hdiag : ∀ j, C j j = 0)
    (hself : ∀ j f, osc j (update j f) = 0)
    (hleak : ∀ i j f, i ≠ j →
      osc j (update i f) ≤ osc j f + C j i * osc i f)
    (hosc : ∀ j, Continuous (osc j : F → ℝ))
    (hρ : 0 < ρ)
    (hsym : ∀ i, (update i).IsSymmetric)
    (hidem : ∀ i, update i * update i = update i)
    (hsep : ∀ f, (∀ j, osc j f = 0) → f = 0) :
    ∀ f : F,
      ρ * (1 - α) * ‖f‖ ^ 2 ≤
        inner ℝ (FiniteHeatBathDobrushin.heatBathPositiveGenerator
          update ρ f) f := by
  let A := FiniteHeatBathDobrushin.heatBathPositiveGenerator update ρ
  have hApos : A.IsPositive :=
    FiniteHeatBathDobrushin.heatBathPositiveGenerator_isPositive
      update ρ hρ.le hsym hidem
  have hA : A.IsSymmetric := hApos.isSymmetric
  apply finiteHeatBath_gap_of_dobrushin update osc C α ρ hC hα0 hα1
    hcol hdiag hself hleak hosc hρ.le A hA hApos hsep rfl
  intro i
  exact FiniteHeatBathDobrushin.poissonizedUpdate_eigenvectorBasis_heatBathPositiveGenerator
      update ρ hρ hA rfl i

/-- Exact FS.22 interface.  The manuscript's stronger cross-block estimate
implies the leakage form used by the random-scan compiler. -/
theorem finiteReversibleHeatBath_gap_of_manuscriptDobrushin
    [DecidableEq ι] [Nonempty ι]
    (update : ι → F →ₗ[ℝ] F) (osc : ι → Seminorm ℝ F)
    (C : Matrix ι ι ℝ) (α ρ : ℝ)
    (hC : ∀ j i, 0 ≤ C j i)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hcol : ∀ i, ∑ j, C j i ≤ α)
    (hdiag : ∀ j, C j j = 0)
    (hself : ∀ j f, osc j (update j f) = 0)
    (hFS22 : ∀ i j f, i ≠ j →
      osc j (update i f) ≤ C j i * osc i f)
    (hosc : ∀ j, Continuous (osc j : F → ℝ))
    (hρ : 0 < ρ)
    (hsym : ∀ i, (update i).IsSymmetric)
    (hidem : ∀ i, update i * update i = update i)
    (hsep : ∀ f, (∀ j, osc j f = 0) → f = 0) :
    ∀ f : F,
      ρ * (1 - α) * ‖f‖ ^ 2 ≤
        inner ℝ (FiniteHeatBathDobrushin.heatBathPositiveGenerator
          update ρ f) f := by
  apply finiteReversibleHeatBath_gap_of_dobrushin update osc C α ρ hC
    hα0 hα1 hcol hdiag hself
  · intro i j f hij
    exact (hFS22 i j f hij).trans
      (le_add_of_nonneg_left (apply_nonneg (osc j) f))
  · exact hosc
  · exact hρ
  · exact hsym
  · exact hidem
  · exact hsep

end DobrushinSpectralGapBridge
end NCG
