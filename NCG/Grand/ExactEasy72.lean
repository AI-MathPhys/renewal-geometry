import NCG.Grand.SummableCorrections
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Exact EASY 72: weighted summable correction of metric arrows

Unlike the earlier abstract telescoping theorem, this file constructs the
actual chain cocycle, proves the transported defect identity, retains
positivity in the norm limit, and proves exact metric congruence at the limit.
-/

open Matrix Filter
open scoped ComplexOrder MatrixOrder Norms.L2Operator

namespace NCG

set_option maxHeartbeats 800000

/-- The finite-dimensional PSD cone is closed under norm convergence. -/
theorem posSemidef_of_tendsto
    {E : Type} [Fintype E] [DecidableEq E]
    (A : ℕ → Matrix E E ℂ) (L : Matrix E E ℂ)
    (hA : ∀ n, (A n).PosSemidef)
    (hlim : Tendsto A atTop (nhds L)) : L.PosSemidef := by
  refine ⟨?_, ?_⟩
  · have hct : Tendsto (fun n => (A n)ᴴ) atTop (nhds Lᴴ) :=
      (continuous_id.matrix_conjTranspose.tendsto L).comp hlim
    have hsame : Tendsto (fun n => (A n)ᴴ) atTop (nhds L) :=
      hlim.congr' (Eventually.of_forall fun n => (hA n).isHermitian.symm)
    exact tendsto_nhds_unique hct hsame
  · intro x
    let q : Matrix E E ℂ → ℂ := fun M =>
      ∑ i ∈ x.support, ∑ j ∈ x.support,
        star (x i) * M i j * x j
    have hq : Continuous q := by
      dsimp [q]
      fun_prop
    have hqlim : Tendsto (fun n => q (A n)) atTop (nhds (q L)) :=
      (hq.tendsto L).comp hlim
    have hqnonneg : ∀ n, 0 ≤ q (A n) := by
      intro n
      simpa [q, Finsupp.sum] using (hA n).2 x
    have hqL : 0 ≤ q L := isClosed_Ici.mem_of_tendsto hqlim
      (Eventually.of_forall hqnonneg)
    simpa [q, Finsupp.sum] using hqL

/-- Ordered transport from level `m` through `k` arrows. -/
def metricChainTransport {E : Type} [Fintype E] [DecidableEq E]
    (Z : ℕ → Matrix E E ℂ) (m : ℕ) : ℕ → Matrix E E ℂ
  | 0 => 1
  | k + 1 => Z (m + k) * metricChainTransport Z m k

@[simp] theorem metricChainTransport_zero
    {E : Type} [Fintype E] [DecidableEq E]
    (Z : ℕ → Matrix E E ℂ) (m : ℕ) :
    metricChainTransport Z m 0 = 1 := rfl

/-- Removing the first arrow from a chain transport. -/
theorem metricChainTransport_succ_shift
    {E : Type} [Fintype E] [DecidableEq E]
    (Z : ℕ → Matrix E E ℂ) (m k : ℕ) :
    metricChainTransport Z m (k + 1)
      = metricChainTransport Z (m + 1) k * Z m := by
  induction k with
  | zero =>
      change Z m * 1 = 1 * Z m
      simp
  | succ k ih =>
      change Z (m + (k + 1)) * metricChainTransport Z m (k + 1)
        = Z (m + 1 + k) * metricChainTransport Z (m + 1) k * Z m
      rw [ih]
      simp only [Matrix.mul_assoc]
      congr 2
      omega

/-- The metric at level `m+k`, transported back to level `m`. -/
def transportedMetric {E : Type} [Fintype E] [DecidableEq E]
    (Z G : ℕ → Matrix E E ℂ) (m k : ℕ) : Matrix E E ℂ :=
  let T := metricChainTransport Z m k
  Tᴴ * G (m + k) * T

/-- Consecutive transported metrics differ by the transported one-step defect. -/
theorem transportedMetric_succ_sub
    {E : Type} [Fintype E] [DecidableEq E]
    (Z G : ℕ → Matrix E E ℂ) (m k : ℕ) :
    transportedMetric Z G m (k + 1) - transportedMetric Z G m k
      = let T := metricChainTransport Z m k
        Tᴴ * ((Z (m + k))ᴴ * G (m + k + 1) * Z (m + k)
          - G (m + k)) * T := by
  simp only [transportedMetric, metricChainTransport,
    Matrix.conjTranspose_mul]
  have hidx : m + (k + 1) = m + k + 1 := by omega
  rw [hidx]
  noncomm_ring

/-- The exact transport weight `‖Z_{n/m}‖²` bounds the transported defect. -/
theorem transportedMetric_defect_bound
    {E : Type} [Fintype E] [DecidableEq E]
    (Z G : ℕ → Matrix E E ℂ) (m k : ℕ) :
    ‖transportedMetric Z G m (k + 1) - transportedMetric Z G m k‖
      ≤ ‖metricChainTransport Z m k‖ ^ 2
        * ‖(Z (m + k))ᴴ * G (m + k + 1) * Z (m + k) - G (m + k)‖ := by
  rw [transportedMetric_succ_sub]
  let T := metricChainTransport Z m k
  let D := (Z (m + k))ᴴ * G (m + k + 1) * Z (m + k) - G (m + k)
  have hnormT : ‖Tᴴ‖ = ‖T‖ := Matrix.l2_opNorm_conjTranspose T
  calc
    ‖Tᴴ * D * T‖ ≤ ‖Tᴴ * D‖ * ‖T‖ := norm_mul_le _ _
    _ ≤ (‖Tᴴ‖ * ‖D‖) * ‖T‖ :=
      mul_le_mul_of_nonneg_right (norm_mul_le Tᴴ D) (norm_nonneg _)
    _ = (‖T‖ * ‖D‖) * ‖T‖ := by
      rw [hnormT]
    _ = ‖T‖ ^ 2 * ‖D‖ := by ring

/-- `thm:summable-metric-correction`, exact cocycle form. -/
theorem summable_metric_correction_exact
    {E : Type} [Fintype E] [DecidableEq E]
    (Z G : ℕ → Matrix E E ℂ) (hG : ∀ n, (G n).PosSemidef)
    (hsum : ∀ m, Summable fun k : ℕ =>
      ‖metricChainTransport Z m k‖ ^ 2
        * ‖(Z (m + k))ᴴ * G (m + k + 1) * Z (m + k) - G (m + k)‖) :
    ∃ Ghat : ℕ → Matrix E E ℂ,
      (∀ m, Tendsto (transportedMetric Z G m) atTop (nhds (Ghat m)))
      ∧ (∀ m, (Ghat m).PosSemidef)
      ∧ (∀ m, (Z m)ᴴ * Ghat (m + 1) * Z m = Ghat m)
      ∧ (∀ m, ‖Ghat m - G m‖ ≤ ∑' k : ℕ,
        ‖metricChainTransport Z m k‖ ^ 2
          * ‖(Z (m + k))ᴴ * G (m + k + 1) * Z (m + k) - G (m + k)‖) := by
  let d : ℕ → ℕ → ℝ := fun m k =>
    ‖metricChainTransport Z m k‖ ^ 2
      * ‖(Z (m + k))ᴴ * G (m + k + 1) * Z (m + k) - G (m + k)‖
  have hex : ∀ m, ∃ L : Matrix E E ℂ,
      Tendsto (transportedMetric Z G m) atTop (nhds L)
      ∧ ∀ r : ℕ, ‖L - transportedMetric Z G m r‖
        ≤ ∑' k : ℕ, d m (k + r) := by
    intro m
    exact summable_defect_limit (transportedMetric Z G m) (d m)
      (hsum m) (fun k => transportedMetric_defect_bound Z G m k)
  choose Ghat hlim hbound using hex
  refine ⟨Ghat, hlim, ?_, ?_, ?_⟩
  · intro m
    have htransportPSD : ∀ k, (transportedMetric Z G m k).PosSemidef := by
      intro k
      exact (hG (m + k)).conjTranspose_mul_mul_same
        (metricChainTransport Z m k)
    exact posSemidef_of_tendsto (transportedMetric Z G m) (Ghat m)
      htransportPSD (hlim m)
  · intro m
    have hmetricShift : ∀ k,
        transportedMetric Z G m (k + 1)
          = (Z m)ᴴ * transportedMetric Z G (m + 1) k * Z m := by
      intro k
      simp only [transportedMetric, metricChainTransport_succ_shift]
      rw [Matrix.conjTranspose_mul]
      have hidx : m + (k + 1) = m + 1 + k := by omega
      rw [hidx]
      noncomm_ring
    have hleft : Tendsto (fun k => transportedMetric Z G m (k + 1))
        atTop (nhds (Ghat m)) :=
      (hlim m).comp (tendsto_add_atTop_nat 1)
    have hc : Continuous (fun M : Matrix E E ℂ => (Z m)ᴴ * M * Z m) :=
      (continuous_const.mul continuous_id).mul continuous_const
    have hright : Tendsto
        (fun k => (Z m)ᴴ * transportedMetric Z G (m + 1) k * Z m)
        atTop (nhds ((Z m)ᴴ * Ghat (m + 1) * Z m)) :=
      (hc.tendsto _).comp (hlim (m + 1))
    exact tendsto_nhds_unique (hleft.congr' <|
      Eventually.of_forall hmetricShift) hright |>.symm
  · intro m
    have hb := hbound m 0
    simpa [transportedMetric, d] using hb

/-- Amplifying weights are essential: an unweighted geometric error is
summable, while multiplication by the squared transport growth makes every
weighted term equal to one. -/
theorem unweighted_metric_errors_do_not_suffice :
    Summable (fun n : ℕ => (1 / 4 : ℝ) ^ n)
      ∧ ¬ Summable (fun n : ℕ => (4 : ℝ) ^ n * (1 / 4 : ℝ) ^ n) := by
  constructor
  · exact summable_geometric_of_norm_lt_one (by norm_num)
  · have hone : (fun n : ℕ => (4 : ℝ) ^ n * (1 / 4 : ℝ) ^ n)
        = fun _ : ℕ => (1 : ℝ) := by
      funext n
      rw [← mul_pow]
      norm_num
    rw [hone, summable_const_iff]
    norm_num

end NCG
