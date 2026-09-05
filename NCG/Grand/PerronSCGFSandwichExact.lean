/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteMarkovHeatKernel

/-!
# SCGF asymptotics from a Perron sandwich

This replaces the former exact-scalar toy limit by the genuine asymptotic
statement used after Perron--Frobenius: any positive exponential moment trapped
between two positive constant multiples of `exp(T ψ)` has scaled logarithm
converging to `ψ`.
-/

open Filter Topology

noncomputable section

namespace NCG.PerronSCGFSandwich

open scoped BigOperators

variable {S : Type*} [Fintype S] [DecidableEq S]

/-! ## Generator eigenvectors and their exponential semigroup -/

section RealSemigroup

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable [CompleteSpace V]

/-- The Banach-algebra exponential of a real continuous endomorphism acts on
a vector by the termwise exponential series. -/
theorem real_exp_apply_tsum (A : V →L[ℝ] V) (x : V) :
    NormedSpace.exp A x =
      ∑' n : ℕ, ((n.factorial : ℝ)⁻¹) • ((A ^ n) x) := by
  have hexpA : NormedSpace.exp A =
      ∑' n : ℕ, ((n.factorial : ℝ)⁻¹) • A ^ n :=
    congrFun (NormedSpace.exp_eq_tsum ℝ) A
  have hsummable : Summable fun n : ℕ =>
      ((n.factorial : ℝ)⁻¹) • A ^ n :=
    NormedSpace.expSeries_summable' (𝕂 := ℝ) A
  have heval : (∑' n : ℕ, ((n.factorial : ℝ)⁻¹) • A ^ n) x =
      ∑' n : ℕ, (((n.factorial : ℝ)⁻¹) • A ^ n) x :=
    (ContinuousLinearMap.apply ℝ V x).map_tsum hsummable
  rw [hexpA, heval]
  exact tsum_congr fun n => by rw [_root_.smul_apply]

/-- A real generator eigenvector is an eigenvector of its exponential, with
the scalar eigenvalue exponentiated. -/
theorem real_exp_apply_eigen {A : V →L[ℝ] V} {x : V} {c : ℝ}
    (h : A x = c • x) :
    NormedSpace.exp A x = Real.exp c • x := by
  have hpow : ∀ n : ℕ, (A ^ n) x = c ^ n • x := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, pow_succ]
      have h1 : (A ^ n * A) x = (A ^ n) (A x) := rfl
      rw [h1, h, map_smul, ih, smul_smul, mul_comm]
  rw [real_exp_apply_tsum]
  have hterm : ∀ n : ℕ, ((n.factorial : ℝ)⁻¹) • ((A ^ n) x) =
      ((n.factorial : ℝ)⁻¹ * c ^ n) • x := by
    intro n
    rw [hpow n, smul_smul]
  rw [tsum_congr hterm]
  have hsc : Summable fun n : ℕ =>
      (n.factorial : ℝ)⁻¹ * c ^ n := by
    have hseries := NormedSpace.expSeries_summable' (𝕂 := ℝ) c
    simpa [smul_eq_mul] using hseries
  have hsumSmul :
      (∑' n : ℕ, ((n.factorial : ℝ)⁻¹ * c ^ n) • x) =
        (∑' n : ℕ, (n.factorial : ℝ)⁻¹ * c ^ n) • x :=
    ((ContinuousLinearMap.toSpanSingleton ℝ x).map_tsum hsc).symm
  rw [hsumSmul]
  congr 1
  rw [Real.exp_eq_exp_ℝ, congrFun (NormedSpace.exp_eq_tsum ℝ) c]
  apply tsum_congr
  intro n
  simp [smul_eq_mul]

/-- Real-time generator propagation: `A r = ψ r` implies
`exp(t A) r = exp(t ψ) r`. -/
theorem real_exp_smul_eigen {A : V →L[ℝ] V} {r : V} {psi : ℝ}
    (heigen : A r = psi • r) (t : ℝ) :
    NormedSpace.exp (t • A) r = Real.exp (t * psi) • r := by
  apply real_exp_apply_eigen
  rw [_root_.smul_apply, heigen, smul_smul]

end RealSemigroup

/-- A matrix kernel represents the exponential semigroup of a real finite
generator when its multiplication agrees with the continuous-operator
exponential on every vector. -/
def RepresentsExponentialSemigroup
    (kernel : ℝ → Matrix S S ℝ) (generator : (S → ℝ) →L[ℝ] (S → ℝ)) : Prop :=
  ∀ t f, Matrix.mulVec (kernel t) f = NormedSpace.exp (t • generator) f

/-- The exponential action on a Perron vector is derived from the generator
eigen-equation, rather than supplied independently. -/
theorem semigroup_perron_eigen_of_generator
    (kernel : ℝ → Matrix S S ℝ)
    (generator : (S → ℝ) →L[ℝ] (S → ℝ))
    (r : S → ℝ) (psi : ℝ)
    (hrep : RepresentsExponentialSemigroup kernel generator)
    (heigen : generator r = psi • r) :
    ∀ t : ℝ, Matrix.mulVec (kernel t) r = Real.exp (t * psi) • r := by
  intro t
  rw [hrep]
  exact real_exp_smul_eigen heigen t


/-- The finite-state moment obtained by applying a positive kernel to a
terminal weight and averaging against an initial weight. -/
noncomputable def perronMoment
    (kernel : ℝ → Matrix S S ℝ) (p f : S → ℝ) (T : ℝ) : ℝ :=
  ∑ i, p i * Matrix.mulVec (kernel T) f i

/-- Positivity of the kernel transports a coordinatewise comparison with a
positive Perron vector into the two-sided exponential estimate needed for the
SCGF limit.  This is the finite-dimensional Perron comparison principle behind
the Feynman--Kac asymptotic. -/
theorem perron_sandwich_of_positive_kernel
    (kernel : ℝ → Matrix S S ℝ) (p r f : S → ℝ) (psi a b : ℝ)
    (hp : ∀ i, 0 ≤ p i)
    (ha : 0 < a) (hb : 0 < b)
    (hcompare : ∀ i, a * r i ≤ f i ∧ f i ≤ b * r i)
    (hpositive : ∀ T, 0 < T → Matrix.EntrywiseNonnegative (kernel T))
    (heigen : ∀ T, 0 < T →
      Matrix.mulVec (kernel T) r = Real.exp (T * psi) • r)
    (hpair : 0 < ∑ i, p i * r i) :
    ∀ T, 0 < T →
      (a * ∑ i, p i * r i) * Real.exp (T * psi) ≤
          perronMoment kernel p f T ∧
        perronMoment kernel p f T ≤
          (b * ∑ i, p i * r i) * Real.exp (T * psi) := by
  intro T hT
  have hmono (u v : S → ℝ) (huv : ∀ i, u i ≤ v i) (x : S) :
      Matrix.mulVec (kernel T) u x ≤ Matrix.mulVec (kernel T) v x := by
    simp only [Matrix.mulVec, dotProduct]
    exact Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (huv i) (hpositive T hT x i)
  have hlower (i : S) :
      a * Matrix.mulVec (kernel T) r i ≤ Matrix.mulVec (kernel T) f i := by
    calc
      a * Matrix.mulVec (kernel T) r i =
          Matrix.mulVec (kernel T) (a • r) i := by
            rw [Matrix.mulVec_smul]
            rfl
      _ ≤ Matrix.mulVec (kernel T) f i :=
        hmono (a • r) f (fun j => by simpa using (hcompare j).1) i
  have hupper (i : S) :
      Matrix.mulVec (kernel T) f i ≤ b * Matrix.mulVec (kernel T) r i := by
    calc
      Matrix.mulVec (kernel T) f i ≤
          Matrix.mulVec (kernel T) (b • r) i :=
        hmono f (b • r) (fun j => by simpa using (hcompare j).2) i
      _ = b * Matrix.mulVec (kernel T) r i := by
        rw [Matrix.mulVec_smul]
        rfl
  have heigen_app (i : S) :
      Matrix.mulVec (kernel T) r i = Real.exp (T * psi) * r i := by
    have h := congrFun (heigen T hT) i
    simpa using h
  constructor
  · calc
      (a * ∑ i, p i * r i) * Real.exp (T * psi) =
          (a * Real.exp (T * psi)) * ∑ i, p i * r i := by ring
      _ = ∑ i, (a * Real.exp (T * psi)) * (p i * r i) := by
        rw [Finset.mul_sum]
      _ =
          ∑ i, p i * (a * (Real.exp (T * psi) * r i)) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = ∑ i, p i * (a * Matrix.mulVec (kernel T) r i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [heigen_app]
      _ ≤ ∑ i, p i * Matrix.mulVec (kernel T) f i :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hlower i) (hp i)
      _ = perronMoment kernel p f T := rfl
  · calc
      perronMoment kernel p f T =
          ∑ i, p i * Matrix.mulVec (kernel T) f i := rfl
      _ ≤ ∑ i, p i * (b * Matrix.mulVec (kernel T) r i) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hupper i) (hp i)
      _ = ∑ i, p i * (b * (Real.exp (T * psi) * r i)) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [heigen_app]
      _ = ∑ i, (b * Real.exp (T * psi)) * (p i * r i) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = (b * Real.exp (T * psi)) * ∑ i, p i * r i := by
        rw [Finset.mul_sum]
      _ = (b * ∑ i, p i * r i) * Real.exp (T * psi) := by ring

/-- Canonical lower comparison constant for the all-ones terminal vector. -/
noncomputable def canonicalLower (r : S → ℝ) : ℝ :=
  (∑ i, r i)⁻¹

/-- Canonical upper comparison constant for the all-ones terminal vector. -/
noncomputable def canonicalUpper (r : S → ℝ) : ℝ :=
  ∑ i, (r i)⁻¹

/-- On a finite nonempty state space, every strictly positive vector is
uniformly comparable with the all-ones vector.  The displayed constants avoid
any appeal to an abstract minimum or maximum. -/
theorem canonical_compare_one [Nonempty S]
    (r : S → ℝ) (hr : ∀ i, 0 < r i) :
    0 < canonicalLower r ∧ 0 < canonicalUpper r ∧
      ∀ i, canonicalLower r * r i ≤ 1 ∧ 1 ≤ canonicalUpper r * r i := by
  classical
  let i0 : S := Classical.choice inferInstance
  have hsum : 0 < ∑ i, r i := by
    exact Finset.sum_pos' (fun i _ => (hr i).le)
      ⟨i0, Finset.mem_univ i0, hr i0⟩
  have hinvsum : 0 < ∑ i, (r i)⁻¹ := by
    exact Finset.sum_pos' (fun i _ => (inv_pos.mpr (hr i)).le)
      ⟨i0, Finset.mem_univ i0, inv_pos.mpr (hr i0)⟩
  refine ⟨inv_pos.mpr hsum, hinvsum, ?_⟩
  intro i
  constructor
  · have hri : r i ≤ ∑ j, r j :=
      Finset.single_le_sum (fun j _ => (hr j).le) (Finset.mem_univ i)
    calc
      canonicalLower r * r i = (∑ j, r j)⁻¹ * r i := rfl
      _ ≤ (∑ j, r j)⁻¹ * ∑ j, r j :=
        mul_le_mul_of_nonneg_left hri (inv_nonneg.mpr hsum.le)
      _ = 1 := inv_mul_cancel₀ hsum.ne'
  · have hi : (r i)⁻¹ ≤ ∑ j, (r j)⁻¹ :=
      Finset.single_le_sum
        (fun j _ => (inv_pos.mpr (hr j)).le) (Finset.mem_univ i)
    calc
      1 = (r i)⁻¹ * r i := (inv_mul_cancel₀ (hr i).ne').symm
      _ ≤ (∑ j, (r j)⁻¹) * r i :=
        mul_le_mul_of_nonneg_right hi (hr i).le
      _ = canonicalUpper r * r i := rfl

/-- A two-sided Perron bound, rather than an assumed exact scalar formula,
implies the SCGF limit. -/
theorem tendsto_scaled_log_of_perron_sandwich
    (moment : ℝ → ℝ) (lower upper psi : ℝ)
    (hlower : 0 < lower) (hupper : 0 < upper)
    (hsandwich : ∀ T, 0 < T →
      lower * Real.exp (T * psi) ≤ moment T ∧
        moment T ≤ upper * Real.exp (T * psi)) :
    Tendsto (fun T : ℝ ↦ Real.log (moment T) / T) atTop (𝓝 psi) := by
  have hlowerLimit : Tendsto (fun T : ℝ ↦ psi + Real.log lower / T)
      atTop (𝓝 psi) := by
    simpa only [id_eq, add_zero] using tendsto_const_nhds.add
      (tendsto_const_nhds.div_atTop
        (tendsto_id : Tendsto (fun T : ℝ ↦ T) atTop atTop))
  have hupperLimit : Tendsto (fun T : ℝ ↦ psi + Real.log upper / T)
      atTop (𝓝 psi) := by
    simpa only [id_eq, add_zero] using tendsto_const_nhds.add
      (tendsto_const_nhds.div_atTop
        (tendsto_id : Tendsto (fun T : ℝ ↦ T) atTop atTop))
  apply hlowerLimit.squeeze' hupperLimit
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    have hmoment : 0 < moment T :=
      lt_of_lt_of_le (mul_pos hlower (Real.exp_pos _)) (hsandwich T hT).1
    have hlog := Real.log_le_log (mul_pos hlower (Real.exp_pos _))
      (hsandwich T hT).1
    rw [Real.log_mul hlower.ne' (Real.exp_ne_zero _), Real.log_exp] at hlog
    have hdiv := (div_le_div_iff_of_pos_right hT).2 hlog
    calc
      psi + Real.log lower / T =
          (Real.log lower + T * psi) / T := by field_simp; ring
      _ ≤ Real.log (moment T) / T := hdiv
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    have hmoment : 0 < moment T :=
      lt_of_lt_of_le (mul_pos hlower (Real.exp_pos _)) (hsandwich T hT).1
    have hlog := Real.log_le_log hmoment (hsandwich T hT).2
    rw [Real.log_mul hupper.ne' (Real.exp_ne_zero _), Real.log_exp] at hlog
    have hdiv := (div_le_div_iff_of_pos_right hT).2 hlog
    calc
      Real.log (moment T) / T ≤
          (Real.log upper + T * psi) / T := hdiv
      _ = psi + Real.log upper / T := by field_simp; ring

/-- A positive finite kernel with a Perron eigenvector has the expected SCGF
limit for every terminal weight uniformly comparable with that vector. -/
theorem tendsto_scaled_log_perronMoment
    (kernel : ℝ → Matrix S S ℝ) (p r f : S → ℝ) (psi a b : ℝ)
    (hp : ∀ i, 0 ≤ p i)
    (ha : 0 < a) (hb : 0 < b)
    (hcompare : ∀ i, a * r i ≤ f i ∧ f i ≤ b * r i)
    (hpositive : ∀ T, 0 < T → Matrix.EntrywiseNonnegative (kernel T))
    (heigen : ∀ T, 0 < T →
      Matrix.mulVec (kernel T) r = Real.exp (T * psi) • r)
    (hpair : 0 < ∑ i, p i * r i) :
    Tendsto (fun T : ℝ ↦ Real.log (perronMoment kernel p f T) / T)
      atTop (𝓝 psi) := by
  apply tendsto_scaled_log_of_perron_sandwich
      (perronMoment kernel p f) (a * ∑ i, p i * r i)
      (b * ∑ i, p i * r i) psi
  · exact mul_pos ha hpair
  · exact mul_pos hb hpair
  · exact perron_sandwich_of_positive_kernel kernel p r f psi a b hp ha hb
      hcompare hpositive heigen hpair

/-- Direct finite-state SCGF theorem for the Feynman--Kac terminal vector
`1`: strict positivity of the Perron vector supplies all comparison constants
automatically. -/
theorem tendsto_scaled_log_perronMoment_one [Nonempty S]
    (kernel : ℝ → Matrix S S ℝ) (p r : S → ℝ) (psi : ℝ)
    (hp : ∀ i, 0 ≤ p i) (hr : ∀ i, 0 < r i)
    (hpositive : ∀ T, 0 < T → Matrix.EntrywiseNonnegative (kernel T))
    (heigen : ∀ T, 0 < T →
      Matrix.mulVec (kernel T) r = Real.exp (T * psi) • r)
    (hpair : 0 < ∑ i, p i * r i) :
    Tendsto
      (fun T : ℝ ↦
        Real.log (perronMoment kernel p (fun _ => 1) T) / T)
      atTop (𝓝 psi) := by
  obtain ⟨hlower, hupper, hcompare⟩ := canonical_compare_one r hr
  exact tendsto_scaled_log_perronMoment kernel p r (fun _ => 1) psi
    (canonicalLower r) (canonicalUpper r) hp hlower hupper hcompare
    hpositive heigen hpair

/-- Direct SCGF convergence from a positive exponential kernel and the
generator Perron equation.  The semigroup eigenvector hypothesis of
`tendsto_scaled_log_perronMoment_one` is discharged automatically. -/
theorem tendsto_scaled_log_perronMoment_one_of_generator [Nonempty S]
    (kernel : ℝ → Matrix S S ℝ)
    (generator : (S → ℝ) →L[ℝ] (S → ℝ))
    (p r : S → ℝ) (psi : ℝ)
    (hp : ∀ i, 0 ≤ p i) (hr : ∀ i, 0 < r i)
    (hpositive : ∀ T, 0 < T → Matrix.EntrywiseNonnegative (kernel T))
    (hrep : RepresentsExponentialSemigroup kernel generator)
    (heigen : generator r = psi • r)
    (hpair : 0 < ∑ i, p i * r i) :
    Tendsto
      (fun T : ℝ ↦
        Real.log (perronMoment kernel p (fun _ => 1) T) / T)
      atTop (𝓝 psi) := by
  exact tendsto_scaled_log_perronMoment_one kernel p r psi hp hr hpositive
    (fun T _ => semigroup_perron_eigen_of_generator
      kernel generator r psi hrep heigen T)
    hpair

end NCG.PerronSCGFSandwich
