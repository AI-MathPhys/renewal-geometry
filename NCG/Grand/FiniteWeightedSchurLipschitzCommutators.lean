/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.FiniteWeightedSchurNorm

/-!
# Weighted Schur control of Lipschitz similarities and commutators

Finite scalar-block versions of `lem:GTLOC-Schur-Lipschitz` and
`thm:GTLOC-commutator-hierarchy`.  The operator norm is the genuine Euclidean
`ℓ²` norm from `FiniteWeightedSchurNorm`; no entrywise surrogate is used.
-/

open Matrix Finset

namespace NCG
namespace FiniteWeightedSchurLipschitzCommutators

open FiniteWeightedSchurNorm

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] [Nonempty Λ]

/-- The only metric property needed by the similarity and commutator bounds. -/
def OneLipschitz (d : Λ → Λ → ℝ) (φ : Λ → ℝ) : Prop :=
  ∀ x y, |φ x - φ y| ≤ d x y

/-- Entry formula for conjugation by
`W_{a,φ} = diag (exp (a φ(x)))`. -/
noncomputable def weightedConjugate (a : ℝ) (φ : Λ → ℝ)
    (T : Matrix Λ Λ ℂ) : Matrix Λ Λ ℂ :=
  fun x y => (Real.exp (a * (φ x - φ y)) : ℂ) * T x y

theorem weightedConjugate_entry_norm (a : ℝ) (φ : Λ → ℝ)
    (T : Matrix Λ Λ ℂ) (x y : Λ) :
    ‖weightedConjugate a φ T x y‖ =
      Real.exp (a * (φ x - φ y)) * ‖T x y‖ := by
  simp [weightedConjugate, norm_mul, Real.norm_eq_abs, abs_of_pos]

/-- Pointwise form of Schur-to-Lipschitz domination: every admissible
similarity has operator norm at most the weighted Schur norm. -/
theorem opNorm_weightedConjugate_le_schurNorm
    (μ : ℝ) (hμ : 0 ≤ μ) (d : Λ → Λ → ℝ) (hd : ∀ x y, 0 ≤ d x y)
    (T : Matrix Λ Λ ℂ) (φ : Λ → ℝ) (hφ : OneLipschitz d φ)
    (a : ℝ) (ha : |a| ≤ μ) :
    opNorm (weightedConjugate a φ T) ≤ schurNorm μ d T := by
  have hexp : ∀ x y,
      Real.exp (a * (φ x - φ y)) ≤ Real.exp (μ * d x y) := by
    intro x y
    apply Real.exp_le_exp.mpr
    calc
      a * (φ x - φ y) ≤ |a * (φ x - φ y)| := le_abs_self _
      _ = |a| * |φ x - φ y| := abs_mul _ _
      _ ≤ μ * d x y := mul_le_mul ha (hφ x y) (abs_nonneg _) hμ
  apply opNorm_le_max_rowCol (weightedConjugate a φ T)
      (schurNorm μ d T) (schurNorm μ d T)
  · intro x
    calc
      ∑ y, ‖weightedConjugate a φ T x y‖
          ≤ ∑ y, Real.exp (μ * d x y) * ‖T x y‖ := by
            apply Finset.sum_le_sum
            intro y hy
            rw [weightedConjugate_entry_norm]
            exact mul_le_mul_of_nonneg_right (hexp x y) (norm_nonneg _)
      _ = schurRow μ d T x := rfl
      _ ≤ schurNorm μ d T := schurRow_le_schurNorm μ d T x
  · intro y
    calc
      ∑ x, ‖weightedConjugate a φ T x y‖
          ≤ ∑ x, Real.exp (μ * d x y) * ‖T x y‖ := by
            apply Finset.sum_le_sum
            intro x hx
            rw [weightedConjugate_entry_norm]
            exact mul_le_mul_of_nonneg_right (hexp x y) (norm_nonneg _)
      _ = schurCol μ d T y := rfl
      _ ≤ schurNorm μ d T := schurCol_le_schurNorm μ d T y
  · exact schurNorm_nonneg μ d T
  · exact schurNorm_nonneg μ d T

/-- The manuscript's Lipschitz-weight similarity norm, as the supremum of
the genuine operator norms of all admissible similarities. -/
noncomputable def lipschitzSimilarityNorm
    (μ : ℝ) (d : Λ → Λ → ℝ) (T : Matrix Λ Λ ℂ) : ℝ :=
  sSup {r : ℝ | ∃ (φ : Λ → ℝ) (a : ℝ),
    OneLipschitz d φ ∧ |a| ≤ μ ∧ r = opNorm (weightedConjugate a φ T)}

/-- **Schur-to-Lipschitz domination**, in the literal supremum norm. -/
theorem lipschitzSimilarityNorm_le_schurNorm
    (μ : ℝ) (hμ : 0 ≤ μ) (d : Λ → Λ → ℝ) (hd : ∀ x y, 0 ≤ d x y)
    (T : Matrix Λ Λ ℂ) :
    lipschitzSimilarityNorm μ d T ≤ schurNorm μ d T := by
  apply csSup_le
  · refine ⟨opNorm T, ?_⟩
    refine ⟨fun _ => 0, 0, ?_, by simpa using hμ, ?_⟩
    · intro x y
      simpa using hd x y
    · simp [weightedConjugate]
  · intro r hr
    obtain ⟨φ, a, hφ, ha, rfl⟩ := hr
    exact opNorm_weightedConjugate_le_schurNorm μ hμ d hd T φ hφ a ha

theorem opNorm_weightedConjugate_le_lipschitzSimilarityNorm
    (μ : ℝ) (hμ : 0 ≤ μ) (d : Λ → Λ → ℝ) (hd : ∀ x y, 0 ≤ d x y)
    (T : Matrix Λ Λ ℂ) (φ : Λ → ℝ) (hφ : OneLipschitz d φ)
    (a : ℝ) (ha : |a| ≤ μ) :
    opNorm (weightedConjugate a φ T) ≤ lipschitzSimilarityNorm μ d T := by
  apply le_csSup
  · refine ⟨schurNorm μ d T, ?_⟩
    intro r hr
    obtain ⟨ψ, b, hψ, hb, rfl⟩ := hr
    exact opNorm_weightedConjugate_le_schurNorm μ hμ d hd T ψ hψ b hb
  · exact ⟨φ, a, hφ, ha, rfl⟩

/-- Matrix compression to rows in `X` and columns in `Y`. -/
def subsetCompression (X Y : Set Λ) (T : Matrix Λ Λ ℂ) : Matrix Λ Λ ℂ :=
  fun x y => if x ∈ X ∧ y ∈ Y then T x y else 0

/-- Off-diagonal similarity estimate from any Lipschitz separator that is zero
on `Y` and at least `δ` on `X`.  Taking `φ(x)=dist(x,Y)` gives the manuscript's
`exp(-μ d(X,Y))` estimate. -/
theorem opNorm_subsetCompression_le_exp_neg_mul_lipschitzSimilarityNorm
    (μ : ℝ) (hμ : 0 ≤ μ) (d : Λ → Λ → ℝ) (hd : ∀ x y, 0 ≤ d x y)
    (T : Matrix Λ Λ ℂ) (X Y : Set Λ) (φ : Λ → ℝ)
    (hφ : OneLipschitz d φ) (hφY : ∀ y ∈ Y, φ y = 0)
    (δ : ℝ) (hδ : ∀ x ∈ X, δ ≤ φ x) :
    opNorm (subsetCompression X Y T) ≤
      Real.exp (-μ * δ) * lipschitzSimilarityNorm μ d T := by
  let L : Matrix Λ Λ ℂ := Matrix.diagonal fun x =>
    if x ∈ X then (Real.exp (-μ * φ x) : ℂ) else 0
  let R : Matrix Λ Λ ℂ := Matrix.diagonal fun y => if y ∈ Y then 1 else 0
  have hfactor : subsetCompression X Y T =
      L * weightedConjugate μ φ T * R := by
    ext x y
    simp only [L, R, subsetCompression, Matrix.mul_apply]
    rw [Finset.sum_eq_single x, Finset.sum_eq_single y]
    · by_cases hx : x ∈ X <;> by_cases hy : y ∈ Y
      · simp [hx, hy, weightedConjugate, hφY y hy]
        rw [← Complex.ofReal_exp, ← Complex.ofReal_exp, ← Complex.ofReal_mul,
          ← Real.exp_add]
        simp
      · simp [hx, hy]
      · simp [hx]
      · simp [hx]
    · intro b hb hbx
      simp [Matrix.diagonal_apply, hbx]
    · simp
    · intro b hb hby
      simp [Matrix.diagonal_apply, hby]
    · simp
  have hL : opNorm L ≤ Real.exp (-μ * δ) := by
    unfold opNorm L
    rw [Matrix.l2_opNorm_toEuclideanCLM, Matrix.l2_opNorm_diagonal]
    refine (pi_norm_le_iff_of_nonneg (Real.exp_pos _).le).2 fun x => ?_
    by_cases hx : x ∈ X
    · simp only [hx, if_true, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (by
        have := hδ x hx
        nlinarith)
    · simp [hx, (Real.exp_pos _).le]
  have hR : opNorm R ≤ 1 := by
    unfold opNorm R
    rw [Matrix.l2_opNorm_toEuclideanCLM, Matrix.l2_opNorm_diagonal]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun y => ?_
    by_cases hy : y ∈ Y <;> simp [hy]
  rw [hfactor]
  calc
    opNorm (L * weightedConjugate μ φ T * R)
        ≤ opNorm L * opNorm (weightedConjugate μ φ T) * opNorm R := by
          exact le_trans (opNorm_mul_le _ _)
            (mul_le_mul_of_nonneg_right (opNorm_mul_le _ _) (opNorm_nonneg R))
    _ ≤ Real.exp (-μ * δ) * lipschitzSimilarityNorm μ d T * 1 := by
      gcongr
      · exact opNorm_nonneg (weightedConjugate μ φ T)
      · exact opNorm_weightedConjugate_le_lipschitzSimilarityNorm
          μ hμ d hd T φ hφ μ (by simpa using hμ)
      · exact opNorm_nonneg L
    _ = Real.exp (-μ * δ) * lipschitzSimilarityNorm μ d T := mul_one _

section MetricOffDiagonal

variable [PseudoMetricSpace Λ]

/-- Distance between finite subsets, expressed as the infimum of the
point-to-set distances over the first subset. -/
noncomputable def finiteSubsetDistance (X Y : Set Λ) : ℝ :=
  sInf (Metric.infDist (s := Y) '' X)

/-- The exact manuscript off-diagonal estimate obtained with the canonical
separator `φ(x)=dist(x,Y)`. -/
theorem opNorm_subsetCompression_le_exp_neg_setDistance
    (μ : ℝ) (hμ : 0 ≤ μ) (T : Matrix Λ Λ ℂ)
    (X Y : Set Λ) (hX : X.Nonempty) :
    opNorm (subsetCompression X Y T) ≤
      Real.exp (-μ * finiteSubsetDistance X Y) *
        lipschitzSimilarityNorm μ dist T := by
  let φ : Λ → ℝ := fun x => Metric.infDist x Y
  have hφ : OneLipschitz dist φ := by
    intro x y
    have h := (Metric.lipschitz_infDist_pt Y).dist_le_mul x y
    simpa [φ, Real.dist_eq] using h
  have hφY : ∀ y ∈ Y, φ y = 0 := by
    intro y hy
    exact Metric.infDist_zero_of_mem hy
  have hbdd : BddBelow (Metric.infDist (s := Y) '' X) := by
    refine ⟨0, ?_⟩
    intro z hz
    obtain ⟨x, hx, rfl⟩ := hz
    exact Metric.infDist_nonneg
  have hδ : ∀ x ∈ X, finiteSubsetDistance X Y ≤ φ x := by
    intro x hx
    exact csInf_le hbdd ⟨x, hx, rfl⟩
  exact opNorm_subsetCompression_le_exp_neg_mul_lipschitzSimilarityNorm
    μ hμ dist (fun _ _ => dist_nonneg) T X Y φ hφ hφY
      (finiteSubsetDistance X Y) hδ

end MetricOffDiagonal

/-- Diagonal multiplication by a real coordinate. -/
noncomputable def coordinateMultiplier (f : Λ → ℝ) : Matrix Λ Λ ℂ :=
  Matrix.diagonal fun x => (f x : ℂ)

/-- Iterated commutator `ad_{M_f}^n(T)`. -/
noncomputable def iteratedCoordinateCommutator (f : Λ → ℝ) :
    ℕ → Matrix Λ Λ ℂ → Matrix Λ Λ ℂ
  | 0, T => T
  | n + 1, T =>
      coordinateMultiplier f * iteratedCoordinateCommutator f n T -
        iteratedCoordinateCommutator f n T * coordinateMultiplier f

/-- Exact block formula for the commutator hierarchy. -/
theorem iteratedCoordinateCommutator_apply (f : Λ → ℝ) (n : ℕ)
    (T : Matrix Λ Λ ℂ) (x y : Λ) :
    iteratedCoordinateCommutator f n T x y =
      ((f x - f y) ^ n : ℝ) * T x y := by
  induction n with
  | zero => simp [iteratedCoordinateCommutator]
  | succ n ih =>
      simp only [iteratedCoordinateCommutator, Matrix.sub_apply,
        Matrix.mul_apply, coordinateMultiplier]
      rw [Finset.sum_eq_single x, Finset.sum_eq_single y]
      · simp [ih, pow_succ]
        push_cast
        ring
      · intro b hb hbx
        simp [Matrix.diagonal_apply, hbx]
      · simp
      · intro b hb hby
        simp [Matrix.diagonal_apply, hby]
      · simp

/-- The elementary exponential majorant used in the hierarchy:
`r^n ≤ n! μ⁻ⁿ exp(μr)`. -/
theorem pow_le_factorial_div_pow_mul_exp {μ r : ℝ} (hμ : 0 < μ)
    (hr : 0 ≤ r) (n : ℕ) :
    r ^ n ≤ (n ! : ℝ) / μ ^ n * Real.exp (μ * r) := by
  have hseries := Real.pow_div_factorial_le_exp (mul_nonneg hμ.le hr) n
  have hfac : (0 : ℝ) < (n ! : ℕ) := by positivity
  have hbase : (μ * r) ^ n ≤ (n ! : ℝ) * Real.exp (μ * r) := by
    exact (div_le_iff₀ hfac).mp (by simpa using hseries)
  have hpow : 0 < μ ^ n := pow_pos hμ n
  apply (le_div_iff₀ hpow).mp
  rw [mul_assoc, mul_comm (r ^ n), ← mul_pow]
  calc
    (μ * r) ^ n ≤ (n ! : ℝ) * Real.exp (μ * r) := hbase
    _ = ((n ! : ℝ) / μ ^ n * Real.exp (μ * r)) * μ ^ n := by
      field_simp
      ring

/-- **Lipschitz commutator hierarchy**:
`‖ad_{M_f}^n(T)‖ ≤ n! μ⁻ⁿ ‖T‖_{μ,Sch}`. -/
theorem opNorm_iteratedCoordinateCommutator_le
    (μ : ℝ) (hμ : 0 < μ) (d : Λ → Λ → ℝ)
    (T : Matrix Λ Λ ℂ) (f : Λ → ℝ) (hf : OneLipschitz d f)
    (n : ℕ) :
    opNorm (iteratedCoordinateCommutator f n T) ≤
      (n ! : ℝ) / μ ^ n * schurNorm μ d T := by
  let C : ℝ := (n ! : ℝ) / μ ^ n
  have hC : 0 ≤ C := div_nonneg (by positivity) (pow_nonneg hμ.le n)
  have hentry : ∀ x y,
      ‖iteratedCoordinateCommutator f n T x y‖ ≤
        C * (Real.exp (μ * d x y) * ‖T x y‖) := by
    intro x y
    rw [iteratedCoordinateCommutator_apply, norm_mul]
    norm_num only [Complex.norm_real, Real.norm_eq_abs, abs_pow]
    have hdxy : 0 ≤ d x y := le_trans (abs_nonneg _) (hf x y)
    have hpow := pow_le_factorial_div_pow_mul_exp hμ (abs_nonneg (f x - f y)) n
    have hexp : Real.exp (μ * |f x - f y|) ≤ Real.exp (μ * d x y) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hf x y) hμ.le)
    have hscalar : |f x - f y| ^ n ≤ C * Real.exp (μ * d x y) :=
      le_trans hpow (mul_le_mul_of_nonneg_left hexp hC)
    exact mul_le_mul_of_nonneg_right hscalar (norm_nonneg _)
  apply opNorm_le_max_rowCol (iteratedCoordinateCommutator f n T)
      (C * schurNorm μ d T) (C * schurNorm μ d T)
  · intro x
    calc
      ∑ y, ‖iteratedCoordinateCommutator f n T x y‖
          ≤ ∑ y, C * (Real.exp (μ * d x y) * ‖T x y‖) :=
            Finset.sum_le_sum fun y _ => hentry x y
      _ = C * schurRow μ d T x := by rw [Finset.mul_sum]
      _ ≤ C * schurNorm μ d T :=
        mul_le_mul_of_nonneg_left (schurRow_le_schurNorm μ d T x) hC
  · intro y
    calc
      ∑ x, ‖iteratedCoordinateCommutator f n T x y‖
          ≤ ∑ x, C * (Real.exp (μ * d x y) * ‖T x y‖) :=
            Finset.sum_le_sum fun x _ => hentry x y
      _ = C * schurCol μ d T y := by rw [Finset.mul_sum]
      _ ≤ C * schurNorm μ d T :=
        mul_le_mul_of_nonneg_left (schurCol_le_schurNorm μ d T y) hC
  · exact mul_nonneg hC (schurNorm_nonneg μ d T)
  · exact mul_nonneg hC (schurNorm_nonneg μ d T)

end FiniteWeightedSchurLipschitzCommutators
end NCG
