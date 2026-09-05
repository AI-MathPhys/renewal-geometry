/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.InformationGeometry
import NCG.Grand.PrimitiveConditionalScoreGeometry
import NCG.Grand.FiniteGibbsActionGap
import NCG.Grand.ScoreContinuum

/-!
# Exact primitive information geometry

This module completes the multivariate and quantitative clauses of
`thm:primitive-information-geometry`.  It isolates a finite three-coordinate
Fisher matrix, proves a local window from entrywise continuity at the exact
positive baseline Gram, and records the exact FTC consequences for expectation
coordinates and Bregman divergence.
-/

open Finset Matrix Filter Topology

namespace NCG

/-- Squared Euclidean norm in the physical three-score coordinates. -/
def physicalScoreNormSq (v : Fin 3 → ℝ) : ℝ :=
  v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2

/-- Real baseline physical Fisher Gram. -/
noncomputable def primitivePhysicalGram : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.diagonal ![176 / 225, 1, 1]

/-- Quadratic form of a real three-coordinate Fisher matrix. -/
noncomputable def fisherQuadratic
    (G : Matrix (Fin 3) (Fin 3) ℝ) (v : Fin 3 → ℝ) : ℝ :=
  v ⬝ᵥ G.mulVec v

theorem primitivePhysicalGram_quadratic (v : Fin 3 → ℝ) :
    fisherQuadratic primitivePhysicalGram v =
      176 / 225 * v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
  simp [fisherQuadratic, primitivePhysicalGram, dotProduct, Matrix.mulVec,
    Fin.sum_univ_three]
  ring

theorem primitivePhysicalGram_window (v : Fin 3 → ℝ) :
    176 / 225 * physicalScoreNormSq v ≤
      fisherQuadratic primitivePhysicalGram v ∧
    fisherQuadratic primitivePhysicalGram v ≤ physicalScoreNormSq v := by
  rw [primitivePhysicalGram_quadratic]
  unfold physicalScoreNormSq
  constructor <;> nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]

/-- A uniform entrywise perturbation estimate for three-dimensional
quadratic forms. -/
theorem finThree_quadratic_perturbation
    (E : Matrix (Fin 3) (Fin 3) ℝ) (δ : ℝ)
    (hδ : 0 ≤ δ) (hE : ∀ i j, |E i j| ≤ δ)
    (v : Fin 3 → ℝ) :
    |fisherQuadratic E v| ≤ 3 * δ * physicalScoreNormSq v := by
  have h00 := hE 0 0
  have h01 := hE 0 1
  have h02 := hE 0 2
  have h10 := hE 1 0
  have h11 := hE 1 1
  have h12 := hE 1 2
  have h20 := hE 2 0
  have h21 := hE 2 1
  have h22 := hE 2 2
  unfold fisherQuadratic physicalScoreNormSq
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_three]
  calc
    |v 0 * (E 0 0 * v 0 + E 0 1 * v 1 + E 0 2 * v 2) +
        v 1 * (E 1 0 * v 0 + E 1 1 * v 1 + E 1 2 * v 2) +
        v 2 * (E 2 0 * v 0 + E 2 1 * v 1 + E 2 2 * v 2)|
        ≤ δ * (|v 0| + |v 1| + |v 2|) ^ 2 := by
          rw [sq]
          have hmul (i j : Fin 3) : |v i * (E i j * v j)| ≤
              δ * (|v i| * |v j|) := by
            rw [abs_mul, abs_mul]
            calc
              |v i| * (|E i j| * |v j|)
                  ≤ |v i| * (δ * |v j|) := by
                    gcongr
                    exact hE i j
              _ = δ * (|v i| * |v j|) := by ring
          calc
            _ ≤ |v 0 * (E 0 0 * v 0)| + |v 0 * (E 0 1 * v 1)| +
                |v 0 * (E 0 2 * v 2)| + |v 1 * (E 1 0 * v 0)| +
                |v 1 * (E 1 1 * v 1)| + |v 1 * (E 1 2 * v 2)| +
                |v 2 * (E 2 0 * v 0)| + |v 2 * (E 2 1 * v 1)| +
                |v 2 * (E 2 2 * v 2)| := by
                  let a₀ := v 0 * (E 0 0 * v 0)
                  let a₁ := v 0 * (E 0 1 * v 1)
                  let a₂ := v 0 * (E 0 2 * v 2)
                  let b₀ := v 1 * (E 1 0 * v 0)
                  let b₁ := v 1 * (E 1 1 * v 1)
                  let b₂ := v 1 * (E 1 2 * v 2)
                  let c₀ := v 2 * (E 2 0 * v 0)
                  let c₁ := v 2 * (E 2 1 * v 1)
                  let c₂ := v 2 * (E 2 2 * v 2)
                  have hexpand :
                      v 0 * (E 0 0 * v 0 + E 0 1 * v 1 + E 0 2 * v 2) +
                          v 1 * (E 1 0 * v 0 + E 1 1 * v 1 + E 1 2 * v 2) +
                          v 2 * (E 2 0 * v 0 + E 2 1 * v 1 + E 2 2 * v 2) =
                        (a₀ + a₁ + a₂) + (b₀ + b₁ + b₂) +
                          (c₀ + c₁ + c₂) := by
                    dsimp [a₀, a₁, a₂, b₀, b₁, b₂, c₀, c₁, c₂]
                    ring
                  rw [hexpand]
                  change |(a₀ + a₁ + a₂) + (b₀ + b₁ + b₂) +
                    (c₀ + c₁ + c₂)| ≤ _
                  calc
                    _ ≤ |a₀ + a₁ + a₂| + |b₀ + b₁ + b₂| +
                        |c₀ + c₁ + c₂| := by
                          exact (abs_add_le _ _).trans <| by
                            gcongr
                            exact abs_add_le _ _
                    _ ≤ (|a₀| + |a₁| + |a₂|) +
                        (|b₀| + |b₁| + |b₂|) +
                        (|c₀| + |c₁| + |c₂|) := by
                          gcongr <;> exact (abs_add_le _ _).trans <| by
                            gcongr
                            exact abs_add_le _ _
                    _ = _ := by ring
            _ ≤ δ * (|v 0| * |v 0|) + δ * (|v 0| * |v 1|) +
                δ * (|v 0| * |v 2|) + δ * (|v 1| * |v 0|) +
                δ * (|v 1| * |v 1|) + δ * (|v 1| * |v 2|) +
                δ * (|v 2| * |v 0|) + δ * (|v 2| * |v 1|) +
                δ * (|v 2| * |v 2|) := by
                  gcongr <;> apply hmul
            _ = δ * ((|v 0| + |v 1| + |v 2|) *
                (|v 0| + |v 1| + |v 2|)) := by ring
    _ ≤ 3 * δ * (v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2) := by
      have hs : (|v 0| + |v 1| + |v 2|) ^ 2 ≤
          3 * (v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2) := by
        nlinarith [sq_nonneg (|v 0| - |v 1|),
          sq_nonneg (|v 0| - |v 2|), sq_nonneg (|v 1| - |v 2|),
          sq_abs (v 0), sq_abs (v 1), sq_abs (v 2)]
      nlinarith

/-- Entrywise continuity at the exact positive physical Gram yields a genuine
Fisher window on a nontrivial parameter ball. -/
theorem continuousFisher_exists_window
    (G : (Fin 3 → ℝ) → Matrix (Fin 3) (Fin 3) ℝ)
    (hG0 : G 0 = primitivePhysicalGram)
    (hcont : ContinuousAt G 0) :
    ∃ r > 0, ∀ θ, ‖θ‖ < r → ∀ v,
      88 / 225 * physicalScoreNormSq v ≤ fisherQuadratic (G θ) v ∧
      fisherQuadratic (G θ) v ≤ 2 * physicalScoreNormSq v := by
  let δ : ℝ := 22 / 225
  have hδ : 0 < δ := by norm_num [δ]
  have hentry : ∀ i j : Fin 3, ContinuousAt (fun θ => G θ i j) 0 :=
    fun i j => (continuous_apply j).continuousAt.comp
      ((continuous_apply i).continuousAt.comp hcont)
  have hall : ∀ i j : Fin 3, ∀ᶠ θ in nhds 0,
      |G θ i j - primitivePhysicalGram i j| < δ := by
    intro i j
    have ht := (hentry i j).tendsto
    rw [hG0] at ht
    exact (Metric.tendsto_nhds.mp ht δ hδ)
  have hevent : ∀ᶠ θ in nhds 0, ∀ i j : Fin 3,
      |G θ i j - primitivePhysicalGram i j| < δ := by
    filter_upwards [hall 0 0, hall 0 1, hall 0 2,
      hall 1 0, hall 1 1, hall 1 2, hall 2 0, hall 2 1, hall 2 2] with θ
      h00 h01 h02 h10 h11 h12 h20 h21 h22
    intro i j
    fin_cases i <;> fin_cases j <;> assumption
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hevent
  refine ⟨r, hr, ?_⟩
  intro θ hθ v
  have hθball : θ ∈ Metric.ball (0 : Fin 3 → ℝ) r := by
    simpa [Metric.mem_ball, dist_eq_norm] using hθ
  have hdiff : ∀ i j, |(G θ - primitivePhysicalGram) i j| ≤ δ := by
    intro i j
    exact (hball hθball i j).le
  have hpert := finThree_quadratic_perturbation
    (G θ - primitivePhysicalGram) δ hδ.le hdiff v
  have hbase := primitivePhysicalGram_window v
  have hadd : fisherQuadratic (G θ - primitivePhysicalGram) v =
      fisherQuadratic (G θ) v - fisherQuadratic primitivePhysicalGram v := by
    simp [fisherQuadratic, Matrix.sub_mulVec, dotProduct_sub]
  rw [hadd] at hpert
  have habs := abs_le.mp hpert
  have hsum : 0 ≤ physicalScoreNormSq v := by
    unfold physicalScoreNormSq
    positivity
  have hδval : 3 * δ = 66 / 225 := by norm_num [δ]
  constructor
  · calc
      88 / 225 * physicalScoreNormSq v
          ≤ (176 / 225 - 3 * δ) * physicalScoreNormSq v := by
              rw [hδval]
              gcongr
              norm_num
      _ ≤ fisherQuadratic primitivePhysicalGram v -
          3 * δ * physicalScoreNormSq v := by
            nlinarith [hbase.1]
      _ ≤ fisherQuadratic (G θ) v := by linarith [habs.1]
  · calc
      fisherQuadratic (G θ) v
          ≤ fisherQuadratic primitivePhysicalGram v +
            3 * δ * physicalScoreNormSq v := by linarith [habs.2]
      _ ≤ (1 + 3 * δ) * physicalScoreNormSq v := by
            nlinarith [hbase.2]
      _ ≤ 2 * physicalScoreNormSq v := by
            rw [hδval]
            nlinarith

/-- Physical score triple `(η, ζ, ε)`. -/
noncomputable def primitivePhysicalScore : Fin 3 → Fin 5 → ℝ
  | 0 => fun a => Real.sqrt (176 / 225) *
      (Real.sqrt (3 / 8) * scoreUH a + Real.sqrt (5 / 8) * scoreUP a)
  | 1 => fun a => Real.sqrt (5 / 8) * scoreUH a -
      Real.sqrt (3 / 8) * scoreUP a
  | 2 => scoreUE

/-- Stationary weight of a current-phase row. -/
noncomputable def primitiveRowWeight : Fin 2 → ℝ := ![5 / 11, 6 / 11]

/-- Unconditional stationary law corresponding to a conditional row. -/
noncomputable def primitiveTiltedWeight (θ : Fin 3 → ℝ) (a : Fin 5) : ℝ :=
  primitiveRowWeight (primitiveCurrentPhase a) *
    primitiveFiniteExponentialProbability primitivePhysicalScore θ a

/-- Expectation coordinates of the physical score triple. -/
noncomputable def primitiveExpectation (θ : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i => ∑ a, primitiveTiltedWeight θ a * primitivePhysicalScore i a

/-- Row-conditional score mean. -/
noncomputable def primitiveRowScoreMean (θ : Fin 3 → ℝ)
    (x : Fin 2) (i : Fin 3) : ℝ :=
  ∑ a, if primitiveCurrentPhase a = x then
    primitiveFiniteExponentialProbability primitivePhysicalScore θ a *
      primitivePhysicalScore i a else 0

/-- Fisher covariance matrix of the finite conditional exponential family. -/
noncomputable def primitiveFisher (θ : Fin 3 → ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => ∑ a, primitiveTiltedWeight θ a *
    primitivePhysicalScore i a *
    (primitivePhysicalScore j a -
      primitiveRowScoreMean θ (primitiveCurrentPhase a) j)

theorem primitivePhysicalScore_rowCentered (i : Fin 3) :
    PrimitiveRowCentered (primitivePhysicalScore i) := by
  rcases primitiveRowCentered_scoreBank with ⟨hH, hP, hE⟩
  fin_cases i
  · constructor
    · dsimp [primitivePhysicalScore, PrimitiveRowCentered]
      rw [show (1 / 5 : ℝ) *
          (Real.sqrt (176 / 225) * (Real.sqrt (3 / 8) * scoreUH 0 +
            Real.sqrt (5 / 8) * scoreUP 0)) +
          4 / 5 * (Real.sqrt (176 / 225) *
            (Real.sqrt (3 / 8) * scoreUH 1 + Real.sqrt (5 / 8) * scoreUP 1)) =
          Real.sqrt (176 / 225) * Real.sqrt (3 / 8) *
              ((1 / 5 : ℝ) * scoreUH 0 + 4 / 5 * scoreUH 1) +
            Real.sqrt (176 / 225) * Real.sqrt (5 / 8) *
              ((1 / 5 : ℝ) * scoreUP 0 + 4 / 5 * scoreUP 1) by ring]
      rw [show (1 / 5 : ℝ) * scoreUH 0 + 4 / 5 * scoreUH 1 = 0 by
        exact hH.1]
      simp [scoreUP]
    · dsimp [primitivePhysicalScore, PrimitiveRowCentered]
      rw [show (1 / 3 : ℝ) *
          (Real.sqrt (176 / 225) * (Real.sqrt (3 / 8) * scoreUH 2 +
            Real.sqrt (5 / 8) * scoreUP 2)) +
          1 / 3 * (Real.sqrt (176 / 225) *
            (Real.sqrt (3 / 8) * scoreUH 3 + Real.sqrt (5 / 8) * scoreUP 3)) +
          1 / 3 * (Real.sqrt (176 / 225) *
            (Real.sqrt (3 / 8) * scoreUH 4 + Real.sqrt (5 / 8) * scoreUP 4)) =
          Real.sqrt (176 / 225) * Real.sqrt (3 / 8) *
              ((1 / 3 : ℝ) * scoreUH 2 + 1 / 3 * scoreUH 3 + 1 / 3 * scoreUH 4) +
            Real.sqrt (176 / 225) * Real.sqrt (5 / 8) *
              ((1 / 3 : ℝ) * scoreUP 2 + 1 / 3 * scoreUP 3 + 1 / 3 * scoreUP 4) by ring]
      rw [show (1 / 3 : ℝ) * scoreUP 2 + 1 / 3 * scoreUP 3 +
          1 / 3 * scoreUP 4 = 0 by exact hP.2]
      simp [scoreUH]
  · constructor
    · dsimp [primitivePhysicalScore, PrimitiveRowCentered]
      rw [show (1 / 5 : ℝ) *
          (Real.sqrt (5 / 8) * scoreUH 0 - Real.sqrt (3 / 8) * scoreUP 0) +
          4 / 5 * (Real.sqrt (5 / 8) * scoreUH 1 - Real.sqrt (3 / 8) * scoreUP 1) =
          Real.sqrt (5 / 8) * ((1 / 5 : ℝ) * scoreUH 0 + 4 / 5 * scoreUH 1) -
            Real.sqrt (3 / 8) * ((1 / 5 : ℝ) * scoreUP 0 + 4 / 5 * scoreUP 1) by ring]
      rw [show (1 / 5 : ℝ) * scoreUH 0 + 4 / 5 * scoreUH 1 = 0 by
        exact hH.1]
      simp [scoreUP]
    · dsimp [primitivePhysicalScore, PrimitiveRowCentered]
      rw [show (1 / 3 : ℝ) *
          (Real.sqrt (5 / 8) * scoreUH 2 - Real.sqrt (3 / 8) * scoreUP 2) +
          1 / 3 * (Real.sqrt (5 / 8) * scoreUH 3 - Real.sqrt (3 / 8) * scoreUP 3) +
          1 / 3 * (Real.sqrt (5 / 8) * scoreUH 4 - Real.sqrt (3 / 8) * scoreUP 4) =
          Real.sqrt (5 / 8) * ((1 / 3 : ℝ) * scoreUH 2 + 1 / 3 * scoreUH 3 + 1 / 3 * scoreUH 4) -
            Real.sqrt (3 / 8) * ((1 / 3 : ℝ) * scoreUP 2 + 1 / 3 * scoreUP 3 + 1 / 3 * scoreUP 4) by ring]
      rw [show (1 / 3 : ℝ) * scoreUP 2 + 1 / 3 * scoreUP 3 +
          1 / 3 * scoreUP 4 = 0 by exact hP.2]
      simp [scoreUH]
  · exact hE

/-- Zero tilt recovers the baseline conditional probability exactly. -/
theorem primitiveFiniteExponentialProbability_zero (a : Fin 5) :
    primitiveFiniteExponentialProbability primitivePhysicalScore 0 a =
      primitiveConditionalProbability a := by
  fin_cases a <;>
    norm_num [primitiveFiniteExponentialProbability,
      primitiveExponentialProbability, primitiveConditionalProbability,
      primitiveRowPartition, primitiveCurrentPhase, primitivePhysicalScore]

/-- At the primitive parameter the row-conditional physical-score means
vanish. -/
theorem primitiveRowScoreMean_zero (x : Fin 2) (i : Fin 3) :
    primitiveRowScoreMean 0 x i = 0 := by
  have hi := primitivePhysicalScore_rowCentered i
  fin_cases x
  · simpa [primitiveRowScoreMean, Fin.sum_univ_five,
      primitiveCurrentPhase, primitiveFiniteExponentialProbability_zero,
      primitiveConditionalProbability] using hi.1
  · simpa [primitiveRowScoreMean, Fin.sum_univ_five,
      primitiveCurrentPhase, primitiveFiniteExponentialProbability_zero,
      primitiveConditionalProbability] using hi.2

/-- The stationary tilted weight at zero is the manuscript's exact outcome
weight `μ`. -/
theorem primitiveTiltedWeight_zero (a : Fin 5) :
    primitiveTiltedWeight 0 a = scoreMu a := by
  fin_cases a <;>
    norm_num [primitiveTiltedWeight, primitiveRowWeight,
      primitiveFiniteExponentialProbability, primitiveExponentialProbability,
      primitiveConditionalProbability, primitiveRowPartition,
      primitiveCurrentPhase, scoreMu, primitivePhysicalScore]

theorem scoreIP_const_mul_left (c : ℝ) (f g : Fin 5 → ℝ) :
    scoreIP (fun a => c * f a) g = c * scoreIP f g := by
  simp [scoreIP, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem scoreIP_add_left (f g h : Fin 5 → ℝ) :
    scoreIP (fun a => f a + g a) h = scoreIP f h + scoreIP g h := by
  simp [scoreIP, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem scoreIP_sub_left (f g h : Fin 5 → ℝ) :
    scoreIP (fun a => f a - g a) h = scoreIP f h - scoreIP g h := by
  simp [scoreIP, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem scoreIP_comm (f g : Fin 5 → ℝ) : scoreIP f g = scoreIP g f := by
  unfold scoreIP
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem scoreIP_const_mul_right (c : ℝ) (f g : Fin 5 → ℝ) :
    scoreIP f (fun a => c * g a) = c * scoreIP f g := by
  rw [scoreIP_comm, scoreIP_const_mul_left, scoreIP_comm]

/-- The Fisher matrix at the primitive law is exactly the physical score
Gram computed by the score-bank theorem. -/
theorem primitiveFisher_zero_eq_physicalGram :
    primitiveFisher 0 = primitivePhysicalGram := by
  rcases primitive_score_bank with ⟨horth, _, hrot, heta, _⟩
  ext i j
  have hreduce (p q : Fin 3) : primitiveFisher 0 p q =
      scoreIP (primitivePhysicalScore p) (primitivePhysicalScore q) := by
    simp [primitiveFisher, primitiveRowScoreMean_zero,
      primitiveTiltedWeight_zero, scoreIP]
  rw [hreduce]
  fin_cases i <;> fin_cases j
  · simpa [primitivePhysicalScore, primitivePhysicalGram] using heta
  · change scoreIP
      (fun a => Real.sqrt (176 / 225) *
        (Real.sqrt (3 / 8) * scoreUH a + Real.sqrt (5 / 8) * scoreUP a))
      (fun a => Real.sqrt (5 / 8) * scoreUH a -
        Real.sqrt (3 / 8) * scoreUP a) = 0
    rw [scoreIP_const_mul_left, hrot.2.2, mul_zero]
  · change scoreIP
      (fun a => Real.sqrt (176 / 225) *
        (Real.sqrt (3 / 8) * scoreUH a + Real.sqrt (5 / 8) * scoreUP a))
      scoreUE = 0
    rw [scoreIP_const_mul_left, scoreIP_add_left,
      scoreIP_const_mul_left, scoreIP_const_mul_left,
      horth.2.2.2.2.1, horth.2.2.2.2.2]
    ring
  · change scoreIP
      (fun a => Real.sqrt (5 / 8) * scoreUH a -
        Real.sqrt (3 / 8) * scoreUP a)
      (fun a => Real.sqrt (176 / 225) *
        (Real.sqrt (3 / 8) * scoreUH a + Real.sqrt (5 / 8) * scoreUP a)) = 0
    rw [scoreIP_comm, scoreIP_const_mul_left, hrot.2.2, mul_zero]
  · simpa [primitivePhysicalScore, primitivePhysicalGram] using hrot.2.1
  · change scoreIP
      (fun a => Real.sqrt (5 / 8) * scoreUH a -
        Real.sqrt (3 / 8) * scoreUP a) scoreUE = 0
    rw [scoreIP_sub_left, scoreIP_const_mul_left, scoreIP_const_mul_left,
      horth.2.2.2.2.1, horth.2.2.2.2.2]
    ring
  · change scoreIP scoreUE
      (fun a => Real.sqrt (176 / 225) *
        (Real.sqrt (3 / 8) * scoreUH a + Real.sqrt (5 / 8) * scoreUP a)) = 0
    rw [scoreIP_comm, scoreIP_const_mul_left, scoreIP_add_left,
      scoreIP_const_mul_left, scoreIP_const_mul_left,
      horth.2.2.2.2.1, horth.2.2.2.2.2]
    ring
  · change scoreIP scoreUE
      (fun a => Real.sqrt (5 / 8) * scoreUH a -
        Real.sqrt (3 / 8) * scoreUP a) = 0
    rw [scoreIP_comm, scoreIP_sub_left, scoreIP_const_mul_left,
      scoreIP_const_mul_left, horth.2.2.2.2.1, horth.2.2.2.2.2]
    ring
  · simpa [primitivePhysicalScore, primitivePhysicalGram] using horth.2.2.1

/-- Each tilted conditional probability is continuous; strict positivity of
the row partition supplies the nonvanishing denominator. -/
theorem primitiveFiniteExponentialProbability_continuous (a : Fin 5) :
    Continuous (fun θ : Fin 3 → ℝ =>
      primitiveFiniteExponentialProbability primitivePhysicalScore θ a) := by
  unfold primitiveFiniteExponentialProbability primitiveExponentialProbability
  have hpartition (x : Fin 2) : Continuous (fun θ : Fin 3 → ℝ =>
      primitiveRowPartition
        (fun b => ∑ j, θ j * primitivePhysicalScore j b) 1 x) := by
    fin_cases x <;> simp [primitiveRowPartition] <;> fun_prop
  apply Continuous.div
  · fun_prop
  · exact hpartition (primitiveCurrentPhase a)
  · intro θ
    exact (primitiveRowPartition_pos
      (fun b => ∑ j, θ j * primitivePhysicalScore j b) 1
      (primitiveCurrentPhase a)).ne'

/-- Every entry of the finite Fisher covariance is continuous in the
parameter. -/
theorem primitiveFisher_continuous : Continuous primitiveFisher := by
  have hp (a : Fin 5) := primitiveFiniteExponentialProbability_continuous a
  have hmean (x : Fin 2) (i : Fin 3) :
      Continuous (fun θ => primitiveRowScoreMean θ x i) := by
    unfold primitiveRowScoreMean
    exact continuous_finsetSum _ fun a _ => by
      split_ifs <;> fun_prop
  unfold primitiveFisher primitiveTiltedWeight
  exact continuous_matrix fun i j => continuous_finsetSum _ fun a _ => by
    fun_prop

/-- Concrete local Fisher window for the primitive exponential family. -/
theorem primitiveFisher_exists_window :
    ∃ r > 0, ∀ θ, ‖θ‖ < r → ∀ v,
      88 / 225 * physicalScoreNormSq v ≤ fisherQuadratic (primitiveFisher θ) v ∧
      fisherQuadratic (primitiveFisher θ) v ≤ 2 * physicalScoreNormSq v :=
  continuousFisher_exists_window primitiveFisher
    primitiveFisher_zero_eq_physicalGram primitiveFisher_continuous.continuousAt

/-! ## The conditional KL action and its entropy Hessian -/

/-- Positive, normalized conditional branch laws on the two primitive rows. -/
structure PrimitiveConditionalLaw where
  probability : Fin 5 → ℝ
  positive : ∀ a, 0 < probability a
  rowH : probability 0 + probability 1 = 1
  rowP : probability 2 + probability 3 + probability 4 = 1

@[ext]
theorem PrimitiveConditionalLaw.extensionality
    {q p : PrimitiveConditionalLaw} (h : q.probability = p.probability) : q = p := by
  cases q
  cases p
  cases h
  rfl

/-- The primitive conditional law as an element of the fixed-support simplex. -/
noncomputable def primitiveConditionalLaw : PrimitiveConditionalLaw where
  probability := primitiveConditionalProbability
  positive := by
    intro a
    fin_cases a <;> norm_num [primitiveConditionalProbability]
  rowH := by norm_num [primitiveConditionalProbability]
  rowP := by
    norm_num [primitiveConditionalProbability, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_four]

/-- The row-weighted conditional relative-entropy action from the manuscript. -/
noncomputable def primitiveConditionalAction (q : PrimitiveConditionalLaw) : ℝ :=
  ∑ a, primitiveRowWeight (primitiveCurrentPhase a) * q.probability a *
    Real.log (q.probability a / primitiveConditionalProbability a)

/-- Passing from conditional rows to their stationary unconditional law. -/
noncomputable def stationaryBranchLaw (q : PrimitiveConditionalLaw) : Fin 5 → ℝ :=
  fun a => primitiveRowWeight (primitiveCurrentPhase a) * q.probability a

theorem stationaryBranchLaw_pos (q : PrimitiveConditionalLaw) (a : Fin 5) :
    0 < stationaryBranchLaw q a := by
  fin_cases a <;> dsimp [stationaryBranchLaw, primitiveRowWeight,
    primitiveCurrentPhase] <;> exact mul_pos (by norm_num) (q.positive _)

theorem stationaryBranchLaw_sum (q : PrimitiveConditionalLaw) :
    ∑ a, stationaryBranchLaw q a = 1 := by
  simp [stationaryBranchLaw, Fin.sum_univ_five, primitiveRowWeight,
    primitiveCurrentPhase]
  linarith [q.rowH, q.rowP]

theorem scoreMu_pos (a : Fin 5) : 0 < scoreMu a := by
  fin_cases a <;> norm_num [scoreMu]

theorem scoreMu_sum : ∑ a, scoreMu a = 1 := by
  norm_num [scoreMu, Fin.sum_univ_five, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four]

theorem stationaryBranchLaw_primitive :
    stationaryBranchLaw primitiveConditionalLaw = scoreMu := by
  funext a
  fin_cases a <;> norm_num [stationaryBranchLaw, primitiveConditionalLaw,
    primitiveRowWeight, primitiveCurrentPhase, primitiveConditionalProbability,
    scoreMu]

/-- The conditional action is exactly ordinary KL after stationary row
weighting. -/
theorem primitiveConditionalAction_eq_finiteKL (q : PrimitiveConditionalLaw) :
    primitiveConditionalAction q = finiteKL (stationaryBranchLaw q) scoreMu := by
  rw [← stationaryBranchLaw_primitive]
  unfold primitiveConditionalAction finiteKL stationaryBranchLaw
  change ∑ a, primitiveRowWeight (primitiveCurrentPhase a) * q.probability a *
      Real.log (q.probability a / primitiveConditionalProbability a) =
    ∑ a, primitiveRowWeight (primitiveCurrentPhase a) * q.probability a *
      Real.log
        ((primitiveRowWeight (primitiveCurrentPhase a) * q.probability a) /
          (primitiveRowWeight (primitiveCurrentPhase a) *
            primitiveConditionalProbability a))
  apply Finset.sum_congr rfl
  intro a _
  have hw : primitiveRowWeight (primitiveCurrentPhase a) ≠ 0 := by
    fin_cases a <;> norm_num [primitiveRowWeight, primitiveCurrentPhase]
  have hratio :
      (primitiveRowWeight (primitiveCurrentPhase a) * q.probability a) /
          (primitiveRowWeight (primitiveCurrentPhase a) *
            primitiveConditionalProbability a) =
        q.probability a / primitiveConditionalProbability a := by
    field_simp [hw]
  rw [hratio]

/-- The primitive law is the unique minimizer of the conditional information
action. -/
theorem primitiveConditionalAction_unique_minimizer (q : PrimitiveConditionalLaw) :
    0 ≤ primitiveConditionalAction q ∧
      (primitiveConditionalAction q = 0 ↔ q = primitiveConditionalLaw) := by
  rw [primitiveConditionalAction_eq_finiteKL]
  have hkl := finiteKL_nonneg_eq_iff (stationaryBranchLaw q) scoreMu
    (stationaryBranchLaw_pos q) scoreMu_pos (stationaryBranchLaw_sum q) scoreMu_sum
  constructor
  · exact hkl.1
  · rw [hkl.2]
    constructor
    · intro h
      apply PrimitiveConditionalLaw.extensionality
      funext a
      have ha := congrFun h a
      fin_cases a <;>
        simp [stationaryBranchLaw, primitiveConditionalLaw, primitiveRowWeight,
          primitiveCurrentPhase, primitiveConditionalProbability, scoreMu] at ha ⊢ <;>
        linarith
    · intro h
      subst q
      exact stationaryBranchLaw_primitive

/-- Polarized entropy Hessian at the primitive conditional law.  This is the
finite second-variation formula `Σₓ πₓ Σₐ uₐvₐ/p₀ₐ`. -/
noncomputable def primitiveActionHessian (u v : Fin 5 → ℝ) : ℝ :=
  ∑ a, primitiveRowWeight (primitiveCurrentPhase a) *
    (u a * v a / primitiveConditionalProbability a)

/-- Row-centred score tangents have entropy Hessian equal to their stationary
`L²(μ)` Gram pairing. -/
theorem primitiveActionHessian_score_tangents
    (s u : Fin 5 → ℝ) :
    primitiveActionHessian
      (fun a => primitiveConditionalProbability a * s a)
      (fun a => primitiveConditionalProbability a * u a) = scoreIP s u := by
  unfold primitiveActionHessian scoreIP
  apply Finset.sum_congr rfl
  intro a _
  fin_cases a <;>
    norm_num [primitiveConditionalProbability, primitiveRowWeight,
      primitiveCurrentPhase, scoreMu] <;> ring

/-- Consequently the physical-coordinate entropy Hessian is exactly `G₀`. -/
theorem primitiveActionHessian_physical_eq_G0 (i j : Fin 3) :
    primitiveActionHessian
      (fun a => primitiveConditionalProbability a * primitivePhysicalScore i a)
      (fun a => primitiveConditionalProbability a * primitivePhysicalScore j a) =
      primitivePhysicalGram i j := by
  rw [primitiveActionHessian_score_tangents]
  have h := congrFun (congrFun primitiveFisher_zero_eq_physicalGram i) j
  simpa [primitiveFisher, primitiveRowScoreMean_zero,
    primitiveTiltedWeight_zero, scoreIP] using h

/-! ## Log partition and the exact multivariate Bregman identity -/

/-- Physical score pairing with a parameter vector. -/
noncomputable def primitiveScorePairing (θ : Fin 3 → ℝ) (a : Fin 5) : ℝ :=
  ∑ i, θ i * primitivePhysicalScore i a

/-- Stationary log-partition of the two conditional rows. -/
noncomputable def primitiveLogPartition (θ : Fin 3 → ℝ) : ℝ :=
  ∑ x, primitiveRowWeight x *
    Real.log (primitiveRowPartition (primitiveScorePairing θ) 1 x)

/-- Conditional KL between two members of the primitive tilted family. -/
noncomputable def primitiveTiltedKL (θ φ : Fin 3 → ℝ) : ℝ :=
  ∑ a, primitiveTiltedWeight θ a *
    Real.log
      (primitiveFiniteExponentialProbability primitivePhysicalScore θ a /
        primitiveFiniteExponentialProbability primitivePhysicalScore φ a)

theorem primitiveTiltedProbability_pos (θ : Fin 3 → ℝ) (a : Fin 5) :
    0 < primitiveFiniteExponentialProbability primitivePhysicalScore θ a := by
  unfold primitiveFiniteExponentialProbability primitiveExponentialProbability
  exact div_pos (mul_pos (by
    fin_cases a <;> norm_num [primitiveConditionalProbability]) (Real.exp_pos _))
    (primitiveRowPartition_pos _ _ _)

theorem primitiveTiltedWeight_sum (θ : Fin 3 → ℝ) :
    ∑ a, primitiveTiltedWeight θ a = 1 := by
  have hn := primitiveFiniteExponentialProbability_normalized
    primitivePhysicalScore θ
  simp [primitiveTiltedWeight, primitiveRowWeight, primitiveCurrentPhase,
    Fin.sum_univ_five]
  linarith [hn.1, hn.2]

theorem primitiveTiltedWeight_row_logPartition (θ ψ : Fin 3 → ℝ) :
    ∑ a, primitiveTiltedWeight θ a *
        Real.log (primitiveRowPartition (primitiveScorePairing ψ) 1
          (primitiveCurrentPhase a)) = primitiveLogPartition ψ := by
  have hn := primitiveFiniteExponentialProbability_normalized
    primitivePhysicalScore θ
  simp [primitiveTiltedWeight, primitiveLogPartition, primitiveRowWeight,
    primitiveCurrentPhase, Fin.sum_univ_five]
  have hH := congrArg
    (fun z => (5 / 11 : ℝ) * z *
      Real.log (primitiveRowPartition (primitiveScorePairing ψ) 1 0)) hn.1
  have hP := congrArg
    (fun z => (6 / 11 : ℝ) * z *
      Real.log (primitiveRowPartition (primitiveScorePairing ψ) 1 1)) hn.2
  ring_nf at hH hP ⊢
  linarith

theorem primitiveTilted_log_ratio (θ φ : Fin 3 → ℝ) (a : Fin 5) :
    Real.log
        (primitiveFiniteExponentialProbability primitivePhysicalScore θ a /
          primitiveFiniteExponentialProbability primitivePhysicalScore φ a) =
      primitiveScorePairing θ a - primitiveScorePairing φ a +
        Real.log (primitiveRowPartition (primitiveScorePairing φ) 1
          (primitiveCurrentPhase a)) -
        Real.log (primitiveRowPartition (primitiveScorePairing θ) 1
          (primitiveCurrentPhase a)) := by
  have hpθ := primitiveTiltedProbability_pos θ a
  have hpφ := primitiveTiltedProbability_pos φ a
  rw [Real.log_div hpθ.ne' hpφ.ne']
  unfold primitiveFiniteExponentialProbability primitiveExponentialProbability
  rw [Real.log_div
      (mul_pos (by fin_cases a <;> norm_num [primitiveConditionalProbability])
        (Real.exp_pos _)).ne'
      (primitiveRowPartition_pos _ _ _).ne',
    Real.log_div
      (mul_pos (by fin_cases a <;> norm_num [primitiveConditionalProbability])
        (Real.exp_pos _)).ne'
      (primitiveRowPartition_pos _ _ _).ne',
    Real.log_mul
      (by fin_cases a <;> norm_num [primitiveConditionalProbability])
      (Real.exp_pos _).ne',
    Real.log_mul
      (by fin_cases a <;> norm_num [primitiveConditionalProbability])
      (Real.exp_pos _).ne', Real.log_exp, Real.log_exp]
  unfold primitiveScorePairing
  ring

/-- The physical expectation pairing is the finite dot product with `m(θ)`. -/
theorem primitiveExpectation_pairing (θ v : Fin 3 → ℝ) :
    ∑ a, primitiveTiltedWeight θ a * primitiveScorePairing v a =
      v ⬝ᵥ primitiveExpectation θ := by
  unfold primitiveScorePairing primitiveExpectation dotProduct
  calc
    ∑ a, primitiveTiltedWeight θ a *
        ∑ i, v i * primitivePhysicalScore i a =
      ∑ a, ∑ i, primitiveTiltedWeight θ a *
        (v i * primitivePhysicalScore i a) := by
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.mul_sum]
    _ = ∑ i, ∑ a, primitiveTiltedWeight θ a *
        (v i * primitivePhysicalScore i a) := Finset.sum_comm
    _ = ∑ i, v i * ∑ a, primitiveTiltedWeight θ a *
        primitivePhysicalScore i a := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro a _
          ring

/-- Exact conditional relative entropy equals the Bregman divergence of the
stationary log partition. -/
theorem primitiveTiltedKL_eq_bregman (θ φ : Fin 3 → ℝ) :
    primitiveTiltedKL θ φ =
      primitiveLogPartition φ - primitiveLogPartition θ -
        (φ - θ) ⬝ᵥ primitiveExpectation θ := by
  unfold primitiveTiltedKL
  calc
    ∑ a, primitiveTiltedWeight θ a *
        Real.log
          (primitiveFiniteExponentialProbability primitivePhysicalScore θ a /
            primitiveFiniteExponentialProbability primitivePhysicalScore φ a) =
      ∑ a, primitiveTiltedWeight θ a *
        (primitiveScorePairing θ a - primitiveScorePairing φ a) +
      ∑ a, primitiveTiltedWeight θ a *
        Real.log (primitiveRowPartition (primitiveScorePairing φ) 1
          (primitiveCurrentPhase a)) -
      ∑ a, primitiveTiltedWeight θ a *
        Real.log (primitiveRowPartition (primitiveScorePairing θ) 1
          (primitiveCurrentPhase a)) := by
        rw [show (∑ a, primitiveTiltedWeight θ a *
              (primitiveScorePairing θ a - primitiveScorePairing φ a)) +
            (∑ a, primitiveTiltedWeight θ a *
              Real.log (primitiveRowPartition (primitiveScorePairing φ) 1
                (primitiveCurrentPhase a))) -
            (∑ a, primitiveTiltedWeight θ a *
              Real.log (primitiveRowPartition (primitiveScorePairing θ) 1
                (primitiveCurrentPhase a))) =
            (∑ a, primitiveTiltedWeight θ a *
              (primitiveScorePairing θ a - primitiveScorePairing φ a)) +
            ((∑ a, primitiveTiltedWeight θ a *
              Real.log (primitiveRowPartition (primitiveScorePairing φ) 1
                (primitiveCurrentPhase a))) -
            (∑ a, primitiveTiltedWeight θ a *
              Real.log (primitiveRowPartition (primitiveScorePairing θ) 1
                (primitiveCurrentPhase a)))) by ring,
          ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro a _
        rw [primitiveTilted_log_ratio]
        ring
    _ = primitiveLogPartition φ - primitiveLogPartition θ -
        (φ - θ) ⬝ᵥ primitiveExpectation θ := by
      rw [primitiveTiltedWeight_row_logPartition θ φ,
        primitiveTiltedWeight_row_logPartition θ θ]
      rw [show ∑ a, primitiveTiltedWeight θ a *
          (primitiveScorePairing θ a - primitiveScorePairing φ a) =
          -((φ - θ) ⬝ᵥ primitiveExpectation θ) by
        rw [← primitiveExpectation_pairing]
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro a _
        unfold primitiveScorePairing
        simp only [Pi.sub_apply]
        rw [show (∑ x, (φ x - θ x) * primitivePhysicalScore x a) =
            (∑ x, φ x * primitivePhysicalScore x a) -
              (∑ x, θ x * primitivePhysicalScore x a) by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro x _
          ring]
        ring]
      ring

/-! ## Directional calculus of the finite family -/

/-- Affine parameter line, written explicitly to avoid scalar-action
coercions in one-variable calculus. -/
def primitiveParameterLine (θ v : Fin 3 → ℝ) (t : ℝ) : Fin 3 → ℝ :=
  fun i => θ i + t * v i

theorem primitiveScorePairing_parameterLine (θ v : Fin 3 → ℝ) (a : Fin 5) (t : ℝ) :
    primitiveScorePairing (primitiveParameterLine θ v t) a =
      primitiveScorePairing θ a + t * primitiveScorePairing v a := by
  unfold primitiveScorePairing primitiveParameterLine
  rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem primitiveScorePairing_line_hasDerivAt
    (θ v : Fin 3 → ℝ) (a : Fin 5) (t : ℝ) :
    HasDerivAt (fun y => primitiveScorePairing (primitiveParameterLine θ v y) a)
      (primitiveScorePairing v a) t := by
  rw [show (fun y => primitiveScorePairing (primitiveParameterLine θ v y) a) =
      fun y => primitiveScorePairing θ a + y * primitiveScorePairing v a by
    funext y
    exact primitiveScorePairing_parameterLine θ v a y]
  simpa [id_eq] using
    (((hasDerivAt_id t).mul_const (primitiveScorePairing v a)).const_add
      (primitiveScorePairing θ a))

theorem primitiveRowPartition_eq_sum (f : Fin 5 → ℝ) (x : Fin 2) :
    primitiveRowPartition f 1 x =
      ∑ a, if primitiveCurrentPhase a = x then
        primitiveConditionalProbability a * Real.exp (f a) else 0 := by
  fin_cases x <;>
    simp [primitiveRowPartition, primitiveCurrentPhase,
      primitiveConditionalProbability, Fin.sum_univ_five]

noncomputable def primitiveRowDirectionalMoment
    (θ v : Fin 3 → ℝ) (x : Fin 2) : ℝ :=
  ∑ a, if primitiveCurrentPhase a = x then
    primitiveConditionalProbability a *
      Real.exp (primitiveScorePairing θ a) * primitiveScorePairing v a else 0

theorem primitiveRowPartition_line_hasDerivAt
    (θ v : Fin 3 → ℝ) (x : Fin 2) (t : ℝ) :
    HasDerivAt
      (fun y => primitiveRowPartition
        (primitiveScorePairing (primitiveParameterLine θ v y)) 1 x)
      (primitiveRowDirectionalMoment (primitiveParameterLine θ v t) v x) t := by
  simp_rw [primitiveRowPartition_eq_sum]
  unfold primitiveRowDirectionalMoment
  apply HasDerivAt.fun_sum
  intro a _
  split_ifs with h
  · simpa only [Function.comp_apply, mul_assoc] using
      ((Real.hasDerivAt_exp _).comp t
      (primitiveScorePairing_line_hasDerivAt θ v a t)).const_mul
        (primitiveConditionalProbability a)
  · exact hasDerivAt_const t 0

theorem primitiveRowDirectionalMoment_div_partition
    (θ v : Fin 3 → ℝ) (x : Fin 2) :
    primitiveRowDirectionalMoment θ v x /
        primitiveRowPartition (primitiveScorePairing θ) 1 x =
      ∑ i, v i * primitiveRowScoreMean θ x i := by
  unfold primitiveRowDirectionalMoment primitiveRowScoreMean
  rw [show (∑ i, v i * ∑ a,
        if primitiveCurrentPhase a = x then
          primitiveFiniteExponentialProbability primitivePhysicalScore θ a *
            primitivePhysicalScore i a else 0) =
      ∑ a, ∑ i, v i *
        (if primitiveCurrentPhase a = x then
          primitiveFiniteExponentialProbability primitivePhysicalScore θ a *
            primitivePhysicalScore i a else 0) by
    calc
      _ = ∑ i, ∑ a, v i *
          (if primitiveCurrentPhase a = x then
            primitiveFiniteExponentialProbability primitivePhysicalScore θ a *
              primitivePhysicalScore i a else 0) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
      _ = _ := Finset.sum_comm]
  calc
    (∑ a, if primitiveCurrentPhase a = x then
        primitiveConditionalProbability a * Real.exp (primitiveScorePairing θ a) *
          primitiveScorePairing v a else 0) /
        primitiveRowPartition (primitiveScorePairing θ) 1 x =
      ∑ a, if primitiveCurrentPhase a = x then
        (primitiveConditionalProbability a * Real.exp (primitiveScorePairing θ a) /
          primitiveRowPartition (primitiveScorePairing θ) 1 x) *
          primitiveScorePairing v a else 0 := by
            rw [Finset.sum_div]
            apply Finset.sum_congr rfl
            intro a _
            split_ifs <;> ring
    _ = ∑ a, ∑ i, v i *
        (if primitiveCurrentPhase a = x then
          primitiveFiniteExponentialProbability primitivePhysicalScore θ a *
            primitivePhysicalScore i a else 0) := by
          apply Finset.sum_congr rfl
          intro a _
          split_ifs with h
          · unfold primitiveFiniteExponentialProbability primitiveExponentialProbability
            rw [h]
            simp only [one_mul]
            change _ = ∑ i, v i *
              (primitiveConditionalProbability a * Real.exp (primitiveScorePairing θ a) /
                primitiveRowPartition (primitiveScorePairing θ) 1 x *
                  primitivePhysicalScore i a)
            unfold primitiveScorePairing
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            ring
          · simp
    _ = _ := rfl

theorem primitiveTiltedProbability_line_hasDerivAt
    (θ v : Fin 3 → ℝ) (a : Fin 5) (t : ℝ) :
    HasDerivAt
      (fun y => primitiveFiniteExponentialProbability primitivePhysicalScore
        (primitiveParameterLine θ v y) a)
      (primitiveFiniteExponentialProbability primitivePhysicalScore
          (primitiveParameterLine θ v t) a *
        (primitiveScorePairing v a -
          ∑ i, v i * primitiveRowScoreMean (primitiveParameterLine θ v t)
            (primitiveCurrentPhase a) i)) t := by
  let ξ := primitiveParameterLine θ v t
  have hnum : HasDerivAt
      (fun y => primitiveConditionalProbability a *
        Real.exp (primitiveScorePairing (primitiveParameterLine θ v y) a))
      (primitiveConditionalProbability a * Real.exp (primitiveScorePairing ξ a) *
        primitiveScorePairing v a) t := by
    simpa only [Function.comp_apply, mul_assoc] using
      ((Real.hasDerivAt_exp _).comp t
      (primitiveScorePairing_line_hasDerivAt θ v a t)).const_mul
        (primitiveConditionalProbability a)
  have hden := primitiveRowPartition_line_hasDerivAt θ v
    (primitiveCurrentPhase a) t
  have hden_ne := (primitiveRowPartition_pos (primitiveScorePairing ξ) 1
    (primitiveCurrentPhase a)).ne'
  have hquot := hnum.div hden hden_ne
  rw [show (fun y => primitiveFiniteExponentialProbability primitivePhysicalScore
      (primitiveParameterLine θ v y) a) =
      (fun y => (primitiveConditionalProbability a *
        Real.exp (primitiveScorePairing (primitiveParameterLine θ v y) a)) /
        primitiveRowPartition
          (primitiveScorePairing (primitiveParameterLine θ v y)) 1
          (primitiveCurrentPhase a)) by
    funext y
    unfold primitiveFiniteExponentialProbability primitiveExponentialProbability
    simp only [one_mul]
    rfl]
  apply hquot.congr_deriv
  have hm := primitiveRowDirectionalMoment_div_partition ξ v
    (primitiveCurrentPhase a)
  dsimp [ξ] at hm hden_ne ⊢
  rw [← hm]
  rw [show primitiveFiniteExponentialProbability primitivePhysicalScore
      (primitiveParameterLine θ v t) a =
      primitiveConditionalProbability a *
        Real.exp (primitiveScorePairing (primitiveParameterLine θ v t) a) /
          primitiveRowPartition
            (primitiveScorePairing (primitiveParameterLine θ v t)) 1
              (primitiveCurrentPhase a) by
    unfold primitiveFiniteExponentialProbability primitiveExponentialProbability
    simp only [one_mul]
    rfl]
  field_simp [hden_ne]

theorem primitiveExpectation_line_hasDerivAt
    (θ v : Fin 3 → ℝ) (i : Fin 3) (t : ℝ) :
    HasDerivAt (fun y => primitiveExpectation (primitiveParameterLine θ v y) i)
      ((primitiveFisher (primitiveParameterLine θ v t)).mulVec v i) t := by
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun a _ =>
    (primitiveTiltedProbability_line_hasDerivAt θ v a t).const_mul
      (primitiveRowWeight (primitiveCurrentPhase a) * primitivePhysicalScore i a))
  have hfun : (fun y : ℝ =>
      primitiveExpectation (primitiveParameterLine θ v y) i) =
      fun y : ℝ => ∑ a,
        primitiveRowWeight (primitiveCurrentPhase a) * primitivePhysicalScore i a *
          primitiveFiniteExponentialProbability primitivePhysicalScore
            (primitiveParameterLine θ v y) a := by
    funext y
    unfold primitiveExpectation primitiveTiltedWeight
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [hfun]
  apply hsum.congr_deriv
  unfold primitiveFisher Matrix.mulVec dotProduct primitiveTiltedWeight
  calc
    ∑ a, primitiveRowWeight (primitiveCurrentPhase a) * primitivePhysicalScore i a *
        (primitiveFiniteExponentialProbability primitivePhysicalScore
          (primitiveParameterLine θ v t) a *
          (primitiveScorePairing v a - ∑ j, v j *
            primitiveRowScoreMean (primitiveParameterLine θ v t)
              (primitiveCurrentPhase a) j)) =
      ∑ a, ∑ j, primitiveRowWeight (primitiveCurrentPhase a) *
        primitiveFiniteExponentialProbability primitivePhysicalScore
          (primitiveParameterLine θ v t) a * primitivePhysicalScore i a *
        (primitivePhysicalScore j a -
          primitiveRowScoreMean (primitiveParameterLine θ v t)
            (primitiveCurrentPhase a) j) * v j := by
          apply Finset.sum_congr rfl
          intro a _
          unfold primitiveScorePairing
          rw [show (∑ k, v k * primitivePhysicalScore k a) -
                (∑ k, v k * primitiveRowScoreMean (primitiveParameterLine θ v t)
                  (primitiveCurrentPhase a) k) =
              ∑ k, v k * (primitivePhysicalScore k a -
                primitiveRowScoreMean (primitiveParameterLine θ v t)
                  (primitiveCurrentPhase a) k) by
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro k _
            ring]
          rw [Finset.mul_sum]
          rw [show primitiveRowWeight (primitiveCurrentPhase a) *
                primitivePhysicalScore i a *
                ∑ j, primitiveFiniteExponentialProbability primitivePhysicalScore
                    (primitiveParameterLine θ v t) a *
                  (v j * (primitivePhysicalScore j a -
                    primitiveRowScoreMean (primitiveParameterLine θ v t)
                      (primitiveCurrentPhase a) j)) =
              ∑ j, primitiveRowWeight (primitiveCurrentPhase a) *
                primitivePhysicalScore i a *
                (primitiveFiniteExponentialProbability primitivePhysicalScore
                  (primitiveParameterLine θ v t) a *
                  (v j * (primitivePhysicalScore j a -
                    primitiveRowScoreMean (primitiveParameterLine θ v t)
                      (primitiveCurrentPhase a) j))) by
            rw [Finset.mul_sum]]
          apply Finset.sum_congr rfl
          intro j _
          ring
    _ = ∑ j, ∑ a, primitiveRowWeight (primitiveCurrentPhase a) *
        primitiveFiniteExponentialProbability primitivePhysicalScore
          (primitiveParameterLine θ v t) a * primitivePhysicalScore i a *
        (primitivePhysicalScore j a -
          primitiveRowScoreMean (primitiveParameterLine θ v t)
            (primitiveCurrentPhase a) j) * v j := Finset.sum_comm
    _ = ∑ j, (∑ a, primitiveRowWeight (primitiveCurrentPhase a) *
        primitiveFiniteExponentialProbability primitivePhysicalScore
          (primitiveParameterLine θ v t) a * primitivePhysicalScore i a *
        (primitivePhysicalScore j a -
          primitiveRowScoreMean (primitiveParameterLine θ v t)
            (primitiveCurrentPhase a) j)) * v j := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.sum_mul]

/-! ## Closed-ball window and fundamental theorem of calculus -/

/-- The local Fisher estimate on a closed ball, obtained by shrinking the
open continuity radius. -/
theorem primitiveFisher_exists_closedBall_window :
    ∃ r > 0, ∀ θ, ‖θ‖ ≤ r → ∀ v,
      88 / 225 * physicalScoreNormSq v ≤ fisherQuadratic (primitiveFisher θ) v ∧
      fisherQuadratic (primitiveFisher θ) v ≤ 2 * physicalScoreNormSq v := by
  obtain ⟨ρ, hρ, hwindow⟩ := primitiveFisher_exists_window
  refine ⟨ρ / 2, by positivity, ?_⟩
  intro θ hθ v
  apply hwindow θ
  linarith

theorem primitiveParameterLine_zero (θ v : Fin 3 → ℝ) :
    primitiveParameterLine θ v 0 = θ := by
  funext i
  simp [primitiveParameterLine]

theorem primitiveParameterLine_one (θ φ : Fin 3 → ℝ) :
    primitiveParameterLine φ (θ - φ) 1 = θ := by
  funext i
  simp [primitiveParameterLine]

/-- Coordinatewise FTC identity `m(θ)-m(φ)=∫G(φ+t(θ-φ))(θ-φ)dt`. -/
theorem primitiveExpectation_sub_eq_integral (θ φ : Fin 3 → ℝ) (i : Fin 3) :
    primitiveExpectation θ i - primitiveExpectation φ i =
      ∫ t in (0 : ℝ)..1,
        (primitiveFisher (primitiveParameterLine φ (θ - φ) t)).mulVec
          (θ - φ) i := by
  let v := θ - φ
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun y => primitiveExpectation (primitiveParameterLine φ v y) i)
        ((primitiveFisher (primitiveParameterLine φ v t)).mulVec v i) t :=
    fun t _ => primitiveExpectation_line_hasDerivAt φ v i t
  have hint : IntervalIntegrable
      (fun t => (primitiveFisher (primitiveParameterLine φ v t)).mulVec v i)
      MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    unfold Matrix.mulVec dotProduct
    have hline : Continuous (primitiveParameterLine φ v) := by
      apply continuous_pi
      intro k
      simp [primitiveParameterLine]
      fun_prop
    apply continuous_finsetSum
    intro j _
    exact (((continuous_apply j).comp
      ((continuous_apply i).comp
        (primitiveFisher_continuous.comp hline))).mul continuous_const)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  dsimp [v] at hftc ⊢
  rw [primitiveParameterLine_one, primitiveParameterLine_zero] at hftc
  exact hftc.symm

/-- A line segment between two points of a norm ball stays in that ball. -/
theorem primitiveParameterLine_norm_le {r : ℝ} {θ φ : Fin 3 → ℝ}
    (hθ : ‖θ‖ ≤ r) (hφ : ‖φ‖ ≤ r) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖primitiveParameterLine φ (θ - φ) t‖ ≤ r := by
  have hline : primitiveParameterLine φ (θ - φ) t =
      (1 - t) • φ + t • θ := by
    funext i
    simp [primitiveParameterLine]
    ring
  rw [hline]
  calc
    ‖(1 - t) • φ + t • θ‖ ≤ ‖(1 - t) • φ‖ + ‖t • θ‖ := norm_add_le _ _
    _ = (1 - t) * ‖φ‖ + t * ‖θ‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr ht1), abs_of_nonneg ht0]
    _ ≤ (1 - t) * r + t * r := by gcongr
    _ = r := by ring

/-- The derivative of the stationary log partition along a parameter line is
the expectation pairing. -/
theorem primitiveLogPartition_line_hasDerivAt
    (θ v : Fin 3 → ℝ) (t : ℝ) :
    HasDerivAt (fun y => primitiveLogPartition (primitiveParameterLine θ v y))
      (v ⬝ᵥ primitiveExpectation (primitiveParameterLine θ v t)) t := by
  unfold primitiveLogPartition
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun x _ =>
    (((Real.hasDerivAt_log
      (primitiveRowPartition_pos
        (primitiveScorePairing (primitiveParameterLine θ v t)) 1 x).ne').comp t
      (primitiveRowPartition_line_hasDerivAt θ v x t)).const_mul
        (primitiveRowWeight x)))
  apply hsum.congr_deriv
  rw [← primitiveExpectation_pairing]
  unfold primitiveRowDirectionalMoment
  calc
    ∑ x, primitiveRowWeight x *
        ((primitiveRowPartition
          (primitiveScorePairing (primitiveParameterLine θ v t)) 1 x)⁻¹ *
          ∑ a, if primitiveCurrentPhase a = x then
            primitiveConditionalProbability a *
              Real.exp (primitiveScorePairing (primitiveParameterLine θ v t) a) *
              primitiveScorePairing v a else 0) =
      ∑ x, ∑ a, if primitiveCurrentPhase a = x then
        primitiveRowWeight x *
          (primitiveConditionalProbability a *
            Real.exp (primitiveScorePairing (primitiveParameterLine θ v t) a) /
            primitiveRowPartition
              (primitiveScorePairing (primitiveParameterLine θ v t)) 1 x) *
          primitiveScorePairing v a else 0 := by
            apply Finset.sum_congr rfl
            intro x _
            rw [show primitiveRowWeight x *
                  ((primitiveRowPartition
                    (primitiveScorePairing (primitiveParameterLine θ v t)) 1 x)⁻¹ *
                    ∑ a, if primitiveCurrentPhase a = x then
                      primitiveConditionalProbability a *
                        Real.exp (primitiveScorePairing
                          (primitiveParameterLine θ v t) a) *
                        primitiveScorePairing v a else 0) =
                ∑ a, primitiveRowWeight x *
                  ((primitiveRowPartition
                    (primitiveScorePairing (primitiveParameterLine θ v t)) 1 x)⁻¹ *
                    (if primitiveCurrentPhase a = x then
                      primitiveConditionalProbability a *
                        Real.exp (primitiveScorePairing
                          (primitiveParameterLine θ v t) a) *
                        primitiveScorePairing v a else 0)) by
              rw [Finset.mul_sum, Finset.mul_sum]]
            apply Finset.sum_congr rfl
            intro a _
            split_ifs <;> ring
    _ = ∑ a, ∑ x, if primitiveCurrentPhase a = x then
        primitiveRowWeight x *
          (primitiveConditionalProbability a *
            Real.exp (primitiveScorePairing (primitiveParameterLine θ v t) a) /
            primitiveRowPartition
              (primitiveScorePairing (primitiveParameterLine θ v t)) 1 x) *
          primitiveScorePairing v a else 0 := Finset.sum_comm
    _ = ∑ a, primitiveRowWeight (primitiveCurrentPhase a) *
        primitiveFiniteExponentialProbability primitivePhysicalScore
          (primitiveParameterLine θ v t) a * primitiveScorePairing v a := by
          apply Finset.sum_congr rfl
          intro a _
          rw [Finset.sum_eq_single (primitiveCurrentPhase a)]
          unfold primitiveFiniteExponentialProbability primitiveExponentialProbability
          simp only [one_mul]
          rfl
          · intro b _ hb
            simp [Ne.symm hb]
          · simp

/-- Along a parameter segment, the derivative of the expectation pairing is
the Fisher quadratic form. -/
theorem primitiveExpectationPairing_line_hasDerivAt
    (θ v : Fin 3 → ℝ) (t : ℝ) :
    HasDerivAt
      (fun y => v ⬝ᵥ primitiveExpectation (primitiveParameterLine θ v y))
      (fisherQuadratic (primitiveFisher (primitiveParameterLine θ v t)) v) t := by
  unfold dotProduct fisherQuadratic
  exact HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    (primitiveExpectation_line_hasDerivAt θ v i t).const_mul (v i))

/-- Derivative of the segmentwise Bregman remainder. -/
theorem primitiveBregmanSegment_line_hasDerivAt
    (θ v : Fin 3 → ℝ) (t : ℝ) :
    HasDerivAt
      (fun y => primitiveLogPartition (primitiveParameterLine θ v y) -
        primitiveLogPartition θ - y * (v ⬝ᵥ primitiveExpectation θ))
      (v ⬝ᵥ primitiveExpectation (primitiveParameterLine θ v t) -
        v ⬝ᵥ primitiveExpectation θ) t := by
  have h := ((primitiveLogPartition_line_hasDerivAt θ v t).sub_const
    (primitiveLogPartition θ)).sub
      ((hasDerivAt_id t).mul_const (v ⬝ᵥ primitiveExpectation θ))
  have heq : (fun y =>
      primitiveLogPartition (primitiveParameterLine θ v y) -
        primitiveLogPartition θ - y * (v ⬝ᵥ primitiveExpectation θ)) =
      ((fun y => primitiveLogPartition (primitiveParameterLine θ v y) -
        primitiveLogPartition θ) -
        fun y => y * (v ⬝ᵥ primitiveExpectation θ)) := rfl
  rw [heq]
  exact h.congr_deriv (by simp)

/-- The Bregman divergence is the iterated integral of the Fisher quadratic
form along the joining segment. -/
theorem primitiveTiltedKL_eq_iteratedIntegral (θ φ : Fin 3 → ℝ) :
    primitiveTiltedKL θ φ =
      ∫ t in (0 : ℝ)..1, ∫ s in (0 : ℝ)..t,
        fisherQuadratic
          (primitiveFisher (primitiveParameterLine θ (φ - θ) s)) (φ - θ) := by
  let v := φ - θ
  let B : ℝ → ℝ := fun t =>
    primitiveLogPartition (primitiveParameterLine θ v t) -
      primitiveLogPartition θ - t * (v ⬝ᵥ primitiveExpectation θ)
  let H : ℝ → ℝ := fun t =>
    v ⬝ᵥ primitiveExpectation (primitiveParameterLine θ v t) -
      v ⬝ᵥ primitiveExpectation θ
  have hBderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt B (H t) t := by
    intro t _
    exact primitiveBregmanSegment_line_hasDerivAt θ v t
  have hHint : IntervalIntegrable H MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    have hexpect : Continuous primitiveExpectation := by
      unfold primitiveExpectation primitiveTiltedWeight
      apply continuous_pi
      intro i
      exact continuous_finsetSum _ fun a _ => by
        exact (continuous_const.mul
          (primitiveFiniteExponentialProbability_continuous a)).mul continuous_const
    unfold H dotProduct
    apply Continuous.sub
    · apply continuous_finsetSum
      intro i _
      have hline : Continuous (primitiveParameterLine θ v) := by
        apply continuous_pi
        intro k
        simp [primitiveParameterLine]
        fun_prop
      exact continuous_const.mul
        ((continuous_apply i).comp (hexpect.comp hline))
    · exact continuous_const
  have hBftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hBderiv hHint
  have hHftc (t : ℝ) : H t =
      ∫ s in (0 : ℝ)..t,
        fisherQuadratic (primitiveFisher (primitiveParameterLine θ v s)) v := by
    have hder : ∀ s ∈ Set.uIcc (0 : ℝ) t,
        HasDerivAt
          (fun y => v ⬝ᵥ primitiveExpectation (primitiveParameterLine θ v y))
          (fisherQuadratic (primitiveFisher (primitiveParameterLine θ v s)) v) s :=
      fun s _ => primitiveExpectationPairing_line_hasDerivAt θ v s
    have hint : IntervalIntegrable
        (fun s => fisherQuadratic (primitiveFisher (primitiveParameterLine θ v s)) v)
        MeasureTheory.volume 0 t := by
      apply Continuous.intervalIntegrable
      unfold fisherQuadratic dotProduct Matrix.mulVec
      apply continuous_finsetSum
      intro i _
      apply Continuous.mul continuous_const
      apply continuous_finsetSum
      intro j _
      have hline : Continuous (primitiveParameterLine θ v) := by
        apply continuous_pi
        intro k
        simp [primitiveParameterLine]
        fun_prop
      exact (((continuous_apply j).comp
        ((continuous_apply i).comp
          (primitiveFisher_continuous.comp hline))).mul continuous_const)
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hder hint
    unfold H
    rw [primitiveParameterLine_zero] at hftc
    exact hftc.symm
  rw [primitiveTiltedKL_eq_bregman]
  have hline1 : primitiveParameterLine θ v 1 = φ := by
    dsimp [v]
    exact primitiveParameterLine_one φ θ
  have hB0 : B 0 = 0 := by simp [B, primitiveParameterLine_zero]
  have hB1 : B 1 = primitiveLogPartition φ - primitiveLogPartition θ -
      (φ - θ) ⬝ᵥ primitiveExpectation θ := by
    simp [B, v, hline1]
  rw [hB0, hB1] at hBftc
  have hBftc' : primitiveLogPartition φ - primitiveLogPartition θ -
      (φ - θ) ⬝ᵥ primitiveExpectation θ = ∫ t in (0 : ℝ)..1, H t := by
    linarith [hBftc]
  rw [hBftc']
  apply intervalIntegral.integral_congr
  intro t _
  exact hHftc t

/-- Continuity of a Fisher quadratic form along an affine parameter line. -/
theorem primitiveFisherQuadratic_line_continuous
    (θ v w : Fin 3 → ℝ) : Continuous (fun t =>
      fisherQuadratic (primitiveFisher (primitiveParameterLine θ v t)) w) := by
  have hline : Continuous (primitiveParameterLine θ v) := by
    apply continuous_pi
    intro k
    simp [primitiveParameterLine]
    fun_prop
  unfold fisherQuadratic dotProduct Matrix.mulVec
  apply continuous_finsetSum
  intro i _
  apply Continuous.mul continuous_const
  apply continuous_finsetSum
  intro j _
  exact (((continuous_apply j).comp
    ((continuous_apply i).comp
      (primitiveFisher_continuous.comp hline))).mul continuous_const)

/-- Certified local information geometry in the squared Euclidean physical
score norm.  The Fisher, strong-monotonicity, and KL clauses share the exact
constants `88/225` and `2`. -/
theorem primitive_information_geometry_quantitative :
    ∃ r > 0, ∀ θ φ, ‖θ‖ ≤ r → ‖φ‖ ≤ r →
      let v := θ - φ
      (88 / 225 * physicalScoreNormSq v ≤
          v ⬝ᵥ (primitiveExpectation θ - primitiveExpectation φ)) ∧
      (v ⬝ᵥ (primitiveExpectation θ - primitiveExpectation φ) ≤
          2 * physicalScoreNormSq v) ∧
      (44 / 225 * physicalScoreNormSq v ≤ primitiveTiltedKL θ φ) ∧
      (primitiveTiltedKL θ φ ≤ physicalScoreNormSq v) := by
  obtain ⟨r, hr, hwindow⟩ := primitiveFisher_exists_closedBall_window
  refine ⟨r, hr, ?_⟩
  intro θ φ hθ hφ
  dsimp only
  let v := θ - φ
  have hline (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
      ‖primitiveParameterLine φ v t‖ ≤ r := by
    exact primitiveParameterLine_norm_le hθ hφ ht0 ht1
  have hq (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
      88 / 225 * physicalScoreNormSq v ≤
          fisherQuadratic (primitiveFisher (primitiveParameterLine φ v t)) v ∧
      fisherQuadratic (primitiveFisher (primitiveParameterLine φ v t)) v ≤
          2 * physicalScoreNormSq v :=
    hwindow _ (hline t ht0 ht1) v
  have hpair : v ⬝ᵥ (primitiveExpectation θ - primitiveExpectation φ) =
      ∫ t in (0 : ℝ)..1,
        fisherQuadratic (primitiveFisher (primitiveParameterLine φ v t)) v := by
    unfold dotProduct
    calc
      ∑ i, v i * (primitiveExpectation θ - primitiveExpectation φ) i =
        ∑ i, v i * (primitiveExpectation θ i - primitiveExpectation φ i) := by
          apply Finset.sum_congr rfl
          intro i _
          rfl
      _ = ∑ i, v i * ∫ t in (0 : ℝ)..1,
          (primitiveFisher (primitiveParameterLine φ v t)).mulVec v i := by
            apply Finset.sum_congr rfl
            intro i _
            rw [primitiveExpectation_sub_eq_integral]
      _ = ∫ t in (0 : ℝ)..1,
          ∑ i, v i * (primitiveFisher (primitiveParameterLine φ v t)).mulVec v i := by
            rw [intervalIntegral.integral_finsetSum]
            · apply Finset.sum_congr rfl
              intro i _
              rw [intervalIntegral.integral_const_mul]
            · intro i _
              apply Continuous.intervalIntegrable
              apply Continuous.mul continuous_const
              unfold Matrix.mulVec dotProduct
              apply continuous_finsetSum
              intro j _
              have hlineCont : Continuous (primitiveParameterLine φ v) := by
                apply continuous_pi
                intro k
                simp [primitiveParameterLine]
                fun_prop
              exact (((continuous_apply j).comp
                ((continuous_apply i).comp
                  (primitiveFisher_continuous.comp hlineCont))).mul continuous_const)
      _ = _ := rfl
  have hpairLower : 88 / 225 * physicalScoreNormSq v ≤
      v ⬝ᵥ (primitiveExpectation θ - primitiveExpectation φ) := by
    rw [hpair]
    have hconst : ∫ _t in (0 : ℝ)..1,
        88 / 225 * physicalScoreNormSq v = 88 / 225 * physicalScoreNormSq v := by
      simp
    rw [← hconst]
    apply intervalIntegral.integral_mono_on zero_le_one
    · exact intervalIntegrable_const
    · exact (primitiveFisherQuadratic_line_continuous φ v v).intervalIntegrable
        (μ := MeasureTheory.volume) 0 1
    · intro t ht
      exact (hq t ht.1 ht.2).1
  have hpairUpper : v ⬝ᵥ (primitiveExpectation θ - primitiveExpectation φ) ≤
      2 * physicalScoreNormSq v := by
    rw [hpair]
    have hconst : ∫ _t in (0 : ℝ)..1,
        2 * physicalScoreNormSq v = 2 * physicalScoreNormSq v := by simp
    rw [← hconst]
    apply intervalIntegral.integral_mono_on zero_le_one
    · exact (primitiveFisherQuadratic_line_continuous φ v v).intervalIntegrable
        (μ := MeasureTheory.volume) 0 1
    · exact intervalIntegrable_const
    · intro t ht
      exact (hq t ht.1 ht.2).2
  have hKL := primitiveTiltedKL_eq_iteratedIntegral θ φ
  have hlineKL (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
      ‖primitiveParameterLine θ (φ - θ) s‖ ≤ r :=
    primitiveParameterLine_norm_le hφ hθ hs0 hs1
  have hqKL (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :=
    hwindow _ (hlineKL s hs0 hs1) (φ - θ)
  have hnormsym : physicalScoreNormSq (φ - θ) = physicalScoreNormSq v := by
    unfold physicalScoreNormSq v
    simp only [Pi.sub_apply]
    ring
  have hKLLower : 44 / 225 * physicalScoreNormSq v ≤ primitiveTiltedKL θ φ := by
    rw [hKL]
    have hinner (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
        t * (88 / 225 * physicalScoreNormSq v) ≤
          ∫ s in (0 : ℝ)..t,
            fisherQuadratic
              (primitiveFisher (primitiveParameterLine θ (φ - θ) s)) (φ - θ) := by
      have hconst : ∫ _s in (0 : ℝ)..t,
          88 / 225 * physicalScoreNormSq v =
          t * (88 / 225 * physicalScoreNormSq v) := by
        simp [intervalIntegral.integral_const]
        ring
      rw [← hconst]
      apply intervalIntegral.integral_mono_on ht0
      · exact intervalIntegrable_const
      · exact (primitiveFisherQuadratic_line_continuous θ (φ - θ) (φ - θ)).intervalIntegrable
          (μ := MeasureTheory.volume) 0 t
      · intro s hs
        rw [← hnormsym]
        exact (hqKL s hs.1 (hs.2.trans ht1)).1
    have hout : ∫ t in (0 : ℝ)..1,
        t * (88 / 225 * physicalScoreNormSq v) ≤
        ∫ t in (0 : ℝ)..1, ∫ s in (0 : ℝ)..t,
          fisherQuadratic
            (primitiveFisher (primitiveParameterLine θ (φ - θ) s)) (φ - θ) := by
      apply intervalIntegral.integral_mono_on zero_le_one
      · apply Continuous.intervalIntegrable
        fun_prop
      · exact (intervalIntegral.differentiable_integral_of_continuous
          (a := (0 : ℝ))
          (primitiveFisherQuadratic_line_continuous θ (φ - θ) (φ - θ))).continuous.intervalIntegrable
            (μ := MeasureTheory.volume) 0 1
      · intro t ht
        exact hinner t ht.1 ht.2
    norm_num at hout ⊢
    linarith
  refine ⟨hpairLower, hpairUpper, hKLLower, ?_⟩
  rw [hKL]
  have hinnerUpper (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
      (∫ s in (0 : ℝ)..t,
          fisherQuadratic
            (primitiveFisher (primitiveParameterLine θ (φ - θ) s)) (φ - θ)) ≤
        t * (2 * physicalScoreNormSq v) := by
    have hconst : ∫ _s in (0 : ℝ)..t,
        2 * physicalScoreNormSq v = t * (2 * physicalScoreNormSq v) := by
      simp [intervalIntegral.integral_const]
      ring
    rw [← hconst]
    apply intervalIntegral.integral_mono_on ht0
    · exact (primitiveFisherQuadratic_line_continuous θ (φ - θ) (φ - θ)).intervalIntegrable
        (μ := MeasureTheory.volume) 0 t
    · exact intervalIntegrable_const
    · intro s hs
      rw [← hnormsym]
      exact (hqKL s hs.1 (hs.2.trans ht1)).2
  have hout : (∫ t in (0 : ℝ)..1, ∫ s in (0 : ℝ)..t,
        fisherQuadratic
          (primitiveFisher (primitiveParameterLine θ (φ - θ) s)) (φ - θ)) ≤
      ∫ t in (0 : ℝ)..1, t * (2 * physicalScoreNormSq v) := by
    apply intervalIntegral.integral_mono_on zero_le_one
    · exact (intervalIntegral.differentiable_integral_of_continuous
        (a := (0 : ℝ))
        (primitiveFisherQuadratic_line_continuous θ (φ - θ) (φ - θ))).continuous.intervalIntegrable
          (μ := MeasureTheory.volume) 0 1
    · apply Continuous.intervalIntegrable
      fun_prop
    · intro t ht
      exact hinnerUpper t ht.1 ht.2
  norm_num at hout ⊢
  linarith

/-- Euclidean norm of a physical coordinate vector. -/
noncomputable def physicalScoreNorm (v : Fin 3 → ℝ) : ℝ :=
  Real.sqrt (physicalScoreNormSq v)

theorem physicalScoreNorm_nonneg (v : Fin 3 → ℝ) : 0 ≤ physicalScoreNorm v :=
  Real.sqrt_nonneg _

theorem physicalScoreNorm_sq (v : Fin 3 → ℝ) :
    physicalScoreNorm v ^ 2 = physicalScoreNormSq v := by
  unfold physicalScoreNorm
  exact Real.sq_sqrt (by
    unfold physicalScoreNormSq
    positivity)

theorem physicalScoreNorm_cauchy (u v : Fin 3 → ℝ) :
    u ⬝ᵥ v ≤ physicalScoreNorm u * physicalScoreNorm v := by
  unfold dotProduct physicalScoreNorm physicalScoreNormSq
  simp only [Fin.sum_univ_three]
  simpa only [Fin.sum_univ_three] using
    Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin 3)) u v

/-- Strong monotonicity upgrades to the manuscript's lower bi-Lipschitz
bound in the Euclidean physical-score norm. -/
theorem primitiveExpectation_biLipschitz_lower :
    ∃ r > 0, ∀ θ φ, ‖θ‖ ≤ r → ‖φ‖ ≤ r →
      88 / 225 * physicalScoreNorm (θ - φ) ≤
        physicalScoreNorm (primitiveExpectation θ - primitiveExpectation φ) := by
  obtain ⟨r, hr, hq⟩ := primitive_information_geometry_quantitative
  refine ⟨r, hr, ?_⟩
  intro θ φ hθ hφ
  have hmono := (hq θ φ hθ hφ).1
  have hcauchy := physicalScoreNorm_cauchy (θ - φ)
    (primitiveExpectation θ - primitiveExpectation φ)
  by_cases hz : physicalScoreNorm (θ - φ) = 0
  · simp [hz, physicalScoreNorm_nonneg]
  · have hpos : 0 < physicalScoreNorm (θ - φ) :=
      lt_of_le_of_ne (physicalScoreNorm_nonneg _) (Ne.symm hz)
    rw [← physicalScoreNorm_sq] at hmono
    nlinarith

theorem piNorm_le_physicalScoreNorm (v : Fin 3 → ℝ) :
    ‖v‖ ≤ physicalScoreNorm v := by
  rw [pi_norm_le_iff_of_nonneg (physicalScoreNorm_nonneg v)]
  intro i
  have hi : v i ^ 2 ≤ physicalScoreNormSq v := by
    rw [show physicalScoreNormSq v = ∑ j, v j ^ 2 by
      simp [physicalScoreNormSq, Fin.sum_univ_three]]
    exact Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i)
  rw [← physicalScoreNorm_sq] at hi
  exact (sq_le_sq₀ (norm_nonneg _) (physicalScoreNorm_nonneg _)).mp (by
    simpa [Real.norm_eq_abs, sq_abs] using hi)

theorem physicalScoreNorm_le_two_piNorm (v : Fin 3 → ℝ) :
    physicalScoreNorm v ≤ 2 * ‖v‖ := by
  have hi (i : Fin 3) : |v i| ≤ ‖v‖ := by
    simpa [Real.norm_eq_abs] using norm_le_pi_norm v i
  have hs : physicalScoreNormSq v ≤ 3 * ‖v‖ ^ 2 := by
    unfold physicalScoreNormSq
    nlinarith [sq_le_sq₀ (abs_nonneg (v 0)) (norm_nonneg v) |>.mpr (hi 0),
      sq_le_sq₀ (abs_nonneg (v 1)) (norm_nonneg v) |>.mpr (hi 1),
      sq_le_sq₀ (abs_nonneg (v 2)) (norm_nonneg v) |>.mpr (hi 2),
      sq_abs (v 0), sq_abs (v 1), sq_abs (v 2)]
  have hsq := physicalScoreNorm_sq v
  nlinarith [physicalScoreNorm_nonneg v, norm_nonneg v]

/-- Continuity at the primitive Gram also gives a local uniform entry bound. -/
theorem primitiveFisher_exists_entry_bound :
    ∃ r > 0, ∀ θ, ‖θ‖ ≤ r → ∀ i j, |primitiveFisher θ i j| ≤ 2 := by
  have hentry : ∀ i j : Fin 3, ContinuousAt (fun θ => primitiveFisher θ i j) 0 :=
    fun i j => (continuous_apply j).continuousAt.comp
      ((continuous_apply i).continuousAt.comp primitiveFisher_continuous.continuousAt)
  have hall : ∀ i j : Fin 3, ∀ᶠ θ in nhds 0,
      |primitiveFisher θ i j - primitivePhysicalGram i j| < 1 := by
    intro i j
    have ht := (hentry i j).tendsto
    rw [primitiveFisher_zero_eq_physicalGram] at ht
    exact Metric.tendsto_nhds.mp ht 1 (by norm_num)
  have hevent : ∀ᶠ θ in nhds 0, ∀ i j : Fin 3,
      |primitiveFisher θ i j - primitivePhysicalGram i j| < 1 := by
    filter_upwards [hall 0 0, hall 0 1, hall 0 2,
      hall 1 0, hall 1 1, hall 1 2, hall 2 0, hall 2 1, hall 2 2] with θ
      h00 h01 h02 h10 h11 h12 h20 h21 h22
    intro i j
    fin_cases i <;> fin_cases j <;> assumption
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.mp hevent
  refine ⟨ρ / 2, by positivity, ?_⟩
  intro θ hθ i j
  have hmem : θ ∈ Metric.ball (0 : Fin 3 → ℝ) ρ := by
    simp [Metric.mem_ball, dist_eq_norm]
    linarith
  have hd := (hball hmem i j).le
  have hbase : |primitivePhysicalGram i j| ≤ 1 := by
    fin_cases i <;> fin_cases j <;>
      norm_num [primitivePhysicalGram, Matrix.diagonal]
  calc
    |primitiveFisher θ i j| =
        |(primitiveFisher θ i j - primitivePhysicalGram i j) +
          primitivePhysicalGram i j| := by ring_nf
    _ ≤ |primitiveFisher θ i j - primitivePhysicalGram i j| +
        |primitivePhysicalGram i j| := abs_add_le _ _
    _ ≤ 2 := by linarith

/-- Upper Lipschitz estimate for expectation coordinates in the parameter
sup norm. -/
theorem primitiveExpectation_lipschitz_upper :
    ∃ r > 0, ∀ θ φ, ‖θ‖ ≤ r → ‖φ‖ ≤ r →
      ‖primitiveExpectation θ - primitiveExpectation φ‖ ≤ 6 * ‖θ - φ‖ := by
  obtain ⟨r, hr, hentry⟩ := primitiveFisher_exists_entry_bound
  refine ⟨r, hr, ?_⟩
  intro θ φ hθ hφ
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  rw [Real.norm_eq_abs]
  change |primitiveExpectation θ i - primitiveExpectation φ i| ≤ _
  rw [primitiveExpectation_sub_eq_integral]
  calc
    |∫ t in (0 : ℝ)..1,
        (primitiveFisher (primitiveParameterLine φ (θ - φ) t)).mulVec
          (θ - φ) i| ≤
      ∫ t in (0 : ℝ)..1,
        |(primitiveFisher (primitiveParameterLine φ (θ - φ) t)).mulVec
          (θ - φ) i| := intervalIntegral.abs_integral_le_integral_abs zero_le_one
    _ ≤ ∫ _t in (0 : ℝ)..1, 6 * ‖θ - φ‖ := by
      apply intervalIntegral.integral_mono_on zero_le_one
      · apply Continuous.intervalIntegrable
        apply Continuous.abs
        unfold Matrix.mulVec dotProduct
        apply continuous_finsetSum
        intro j _
        have hlineCont : Continuous (primitiveParameterLine φ (θ - φ)) := by
          apply continuous_pi
          intro k
          simp [primitiveParameterLine]
          fun_prop
        exact (((continuous_apply j).comp
          ((continuous_apply i).comp
            (primitiveFisher_continuous.comp hlineCont))).mul continuous_const)
      · exact intervalIntegrable_const
      · intro t ht
        unfold Matrix.mulVec dotProduct
        calc
          |∑ j, primitiveFisher (primitiveParameterLine φ (θ - φ) t) i j *
              (θ - φ) j| ≤
            ∑ j, |primitiveFisher (primitiveParameterLine φ (θ - φ) t) i j *
              (θ - φ) j| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _j : Fin 3, 2 * ‖θ - φ‖ := by
            apply Finset.sum_le_sum
            intro j _
            rw [abs_mul]
            gcongr
            · exact hentry _ (primitiveParameterLine_norm_le hθ hφ ht.1 ht.2) i j
            · simpa [Real.norm_eq_abs] using norm_le_pi_norm (θ - φ) j
          _ = 6 * ‖θ - φ‖ := by simp [Fin.sum_univ_three]; ring
    _ = 6 * ‖θ - φ‖ := by simp

/-- A single manuscript-style local information-geometry package in the
parameter sup norm, with `g₋ = 44/225` and `g₊ = 6`. -/
theorem primitive_information_geometry_common_window :
    ∃ r > 0, ∀ θ φ, ‖θ‖ ≤ r → ‖φ‖ ≤ r →
      let v := θ - φ
      (44 / 225 * physicalScoreNormSq v ≤
          fisherQuadratic (primitiveFisher θ) v) ∧
      (fisherQuadratic (primitiveFisher θ) v ≤
          6 * physicalScoreNormSq v) ∧
      (44 / 225 * ‖v‖ ≤ ‖primitiveExpectation θ - primitiveExpectation φ‖) ∧
      (‖primitiveExpectation θ - primitiveExpectation φ‖ ≤ 6 * ‖v‖) ∧
      (22 / 225 * ‖v‖ ^ 2 ≤ primitiveTiltedKL θ φ) ∧
      (primitiveTiltedKL θ φ ≤ 3 * ‖v‖ ^ 2) := by
  obtain ⟨r₀, hr₀, hwin⟩ := primitiveFisher_exists_closedBall_window
  obtain ⟨r₁, hr₁, hq⟩ := primitive_information_geometry_quantitative
  obtain ⟨r₂, hr₂, hlower⟩ := primitiveExpectation_biLipschitz_lower
  obtain ⟨r₃, hr₃, hupper⟩ := primitiveExpectation_lipschitz_upper
  let r := min r₀ (min r₁ (min r₂ r₃))
  refine ⟨r, by dsimp [r]; positivity, ?_⟩
  intro θ φ hθ hφ
  have hθ0 : ‖θ‖ ≤ r₀ := hθ.trans (min_le_left _ _)
  have hθ1 : ‖θ‖ ≤ r₁ :=
    hθ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hφ1 : ‖φ‖ ≤ r₁ :=
    hφ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hθ2 : ‖θ‖ ≤ r₂ :=
    hθ.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have hφ2 : ‖φ‖ ≤ r₂ :=
    hφ.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have hθ3 : ‖θ‖ ≤ r₃ :=
    hθ.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))
  have hφ3 : ‖φ‖ ≤ r₃ :=
    hφ.trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))
  let v := θ - φ
  have hquant := hq θ φ hθ1 hφ1
  have hlow := hlower θ φ hθ2 hφ2
  have hupp := hupper θ φ hθ3 hφ3
  have hw := hwin θ hθ0 v
  have hpi := piNorm_le_physicalScoreNorm v
  have hphys := physicalScoreNorm_le_two_piNorm
    (primitiveExpectation θ - primitiveExpectation φ)
  have hsum : physicalScoreNormSq v ≤ 3 * ‖v‖ ^ 2 := by
    have hi (i : Fin 3) : |v i| ≤ ‖v‖ := by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm v i
    unfold physicalScoreNormSq
    nlinarith [sq_le_sq₀ (abs_nonneg (v 0)) (norm_nonneg v) |>.mpr (hi 0),
      sq_le_sq₀ (abs_nonneg (v 1)) (norm_nonneg v) |>.mpr (hi 1),
      sq_le_sq₀ (abs_nonneg (v 2)) (norm_nonneg v) |>.mpr (hi 2),
      sq_abs (v 0), sq_abs (v 1), sq_abs (v 2)]
  dsimp only
  refine ⟨by linarith [hw.1], by linarith [hw.2], ?_⟩
  refine ⟨?_, hupp, ?_, ?_⟩
  · nlinarith [hlow, hphys]
  · have hsquare : ‖v‖ ^ 2 ≤ physicalScoreNormSq v := by
      rw [← physicalScoreNorm_sq]
      nlinarith [hpi, norm_nonneg v, physicalScoreNorm_nonneg v]
    nlinarith [hquant.2.2.1]
  · nlinarith [hquant.2.2.2, hsum]

end NCG
