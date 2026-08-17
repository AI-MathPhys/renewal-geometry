/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import NCG.Grand.VaryingHilbertMosco
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Strong convergence from a dense source family

Uniformly Lipschitz operator families on varying Hilbert spaces converge strongly once they
converge on compatible lifts of a dense source set.  The contrapositive localizes failure to one
dense source and one fixed positive discrepancy margin, exactly as required by the primitive-word
test in the Mosco--resolvent theorem.
-/

open Filter Topology Set

noncomputable section

namespace NCG.VaryingHilbert.System

universe u v w v' w'

variable {K : Type u} [RCLike K]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace K H]
variable {Hn : ℕ → Type w}
variable [∀ n, NormedAddCommGroup (Hn n)] [∀ n, InnerProductSpace K (Hn n)]
variable {G : Type v'} [NormedAddCommGroup G] [InnerProductSpace K G]
variable {Gn : ℕ → Type w'}
variable [∀ n, NormedAddCommGroup (Gn n)] [∀ n, InnerProductSpace K (Gn n)]

variable (J : System (K := K) (H := H) (Hn := Hn))
variable (L : System (K := K) (H := G) (Hn := Gn))

/-- A uniformly Lipschitz family is determined, for varying-space strong convergence, by its
values on compatible lifts of any dense subset of the limit Hilbert space. -/
theorem strongOperatorConverges_of_dense_sources
    (Tn : ∀ n, Hn n →L[K] Gn n) (T : H →L[K] G)
    (D : Set H) (hD : Dense D)
    (source : H → ∀ n, Hn n)
    (hsource : ∀ d ∈ D, J.StronglyConverges (source d) d)
    (C : ℝ) (hC : 0 ≤ C)
    (hLip : ∀ n (x y : Hn n),
      dist (L.embedding n (Tn n x)) (L.embedding n (Tn n y)) ≤
        C * dist (J.embedding n x) (J.embedding n y))
    (hconv : ∀ d ∈ D,
      L.StronglyConverges (fun n ↦ Tn n (source d n)) (T d)) :
    J.StrongOperatorConverges L Tn T := by
  intro x xlim hx
  rw [StronglyConverges, Metric.tendsto_atTop]
  intro ε hε
  let B : ℝ := C + ‖T‖ + 1
  have hB : 0 < B := by
    dsimp [B]
    positivity
  let δ : ℝ := ε / (12 * B)
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  obtain ⟨d, hdD, hdx⟩ := hD.exists_dist_lt xlim hδ
  have hinputDist :
      Tendsto
        (fun n ↦ dist (J.embedding n (x n))
          (J.embedding n (source d n))) atTop
        (𝓝 (dist xlim d)) :=
    hx.dist (hsource d hdD)
  have hinputClose : ∀ᶠ n in atTop,
      dist (J.embedding n (x n)) (J.embedding n (source d n)) < 2 * δ := by
    have hnear : Iio (2 * δ) ∈ 𝓝 (dist xlim d) := by
      apply Iio_mem_nhds
      linarith
    filter_upwards [hinputDist.eventually hnear] with n hn
    exact hn
  have hsourceClose : ∀ᶠ n in atTop,
      dist (L.embedding n (Tn n (source d n))) (T d) < ε / 3 := by
    have hout := hconv d hdD
    filter_upwards [hout.eventually
      (Metric.ball_mem_nhds (T d) (by positivity : 0 < ε / 3))] with n hn
    simpa [Metric.mem_ball] using hn
  have hCd : C * (2 * δ) ≤ ε / 6 := by
    have hCB : C ≤ B := by
      dsimp [B]
      linarith [norm_nonneg T]
    calc
      C * (2 * δ) ≤ B * (2 * δ) := by gcongr
      _ = ε / 6 := by
        dsimp [δ]
        field_simp <;> ring
  have hTd : dist (T d) (T xlim) ≤ ε / 12 := by
    calc
      dist (T d) (T xlim) = ‖T (d - xlim)‖ := by
        simp [dist_eq_norm]
      _ ≤ ‖T‖ * ‖d - xlim‖ := T.le_opNorm (d - xlim)
      _ = ‖T‖ * dist d xlim := by rw [dist_eq_norm]
      _ ≤ ‖T‖ * δ := by
        exact mul_le_mul_of_nonneg_left
          (le_of_lt (by simpa [dist_comm] using hdx)) (norm_nonneg T)
      _ ≤ B * δ := by
        gcongr
        · dsimp [B]
          linarith
      _ = ε / 12 := by
        dsimp [δ]
        field_simp
  apply eventually_atTop.mp
  filter_upwards [hinputClose, hsourceClose] with n hnInput hnSource
  calc
    dist (L.embedding n (Tn n (x n))) (T xlim) ≤
        dist (L.embedding n (Tn n (x n)))
            (L.embedding n (Tn n (source d n))) +
          dist (L.embedding n (Tn n (source d n))) (T d) +
          dist (T d) (T xlim) :=
      dist_triangle4 _ _ _ _
    _ ≤ C * dist (J.embedding n (x n))
          (J.embedding n (source d n)) + ε / 3 + ε / 12 := by
      gcongr
      exact hLip n (x n) (source d n)
    _ ≤ C * (2 * δ) + ε / 3 + ε / 12 := by
      gcongr
    _ ≤ ε / 6 + ε / 3 + ε / 12 := by gcongr
    _ < ε := by linarith


/-- The dense-source criterion specialized to a uniform operator-norm bound.  In particular,
families of resolvent contractions may take `C = 1`. -/
theorem strongOperatorConverges_of_dense_sources_of_uniform_opNorm
    (Tn : ∀ n, Hn n →L[K] Gn n) (T : H →L[K] G)
    (D : Set H) (hD : Dense D)
    (source : H → ∀ n, Hn n)
    (hsource : ∀ d ∈ D, J.StronglyConverges (source d) d)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ n, ‖Tn n‖ ≤ C)
    (hconv : ∀ d ∈ D,
      L.StronglyConverges (fun n ↦ Tn n (source d n)) (T d)) :
    J.StrongOperatorConverges L Tn T := by
  apply strongOperatorConverges_of_dense_sources J L Tn T D hD source
    hsource C hC
  · intro n x y
    calc
      dist (L.embedding n (Tn n x)) (L.embedding n (Tn n y)) =
          ‖Tn n (x - y)‖ := by
        rw [dist_eq_norm, ← map_sub, LinearIsometry.norm_map, map_sub]
      _ ≤ ‖Tn n‖ * ‖x - y‖ := (Tn n).le_opNorm (x - y)
      _ ≤ C * ‖x - y‖ := by
        gcongr
        exact hbound n
      _ = C * dist (J.embedding n x) (J.embedding n y) := by
        congr 1
        rw [dist_eq_norm, ← map_sub, LinearIsometry.norm_map]
  · exact hconv

/-- If the full strong-operator convergence fails under the dense-source extension hypotheses,
then it already fails on one member of the chosen dense source set. -/
theorem exists_bad_dense_source_of_not_strongOperatorConverges
    (Tn : ∀ n, Hn n →L[K] Gn n) (T : H →L[K] G)
    (D : Set H) (hD : Dense D)
    (source : H → ∀ n, Hn n)
    (hsource : ∀ d ∈ D, J.StronglyConverges (source d) d)
    (C : ℝ) (hC : 0 ≤ C)
    (hLip : ∀ n (x y : Hn n),
      dist (L.embedding n (Tn n x)) (L.embedding n (Tn n y)) ≤
        C * dist (J.embedding n x) (J.embedding n y))
    (hfail : ¬ J.StrongOperatorConverges L Tn T) :
    ∃ d ∈ D,
      ¬ L.StronglyConverges (fun n ↦ Tn n (source d n)) (T d) := by
  by_contra hbad
  push Not at hbad
  exact hfail (strongOperatorConverges_of_dense_sources J L Tn T D hD source
    hsource C hC hLip hbad)

/-- Nonconvergence in a metric target supplies a fixed discrepancy margin at arbitrarily late
indices. -/
theorem exists_cofinal_discrepancy_of_not_tendsto
    {X : Type*} [PseudoMetricSpace X] (f : ℕ → X) (a : X)
    (hfail : ¬ Tendsto f atTop (𝓝 a)) :
    ∃ ε > 0, ∀ N, ∃ n ≥ N, ε ≤ dist (f n) a := by
  rw [Metric.tendsto_atTop] at hfail
  push Not at hfail
  obtain ⟨ε, hε, hlate⟩ := hfail
  exact ⟨ε, hε, fun N ↦ by
    obtain ⟨n, hn, hdist⟩ := hlate N
    exact ⟨n, hn, hdist⟩⟩

/-- Failure of varying-space strong operator convergence is witnessed by one dense source, one
positive margin, and discrepancies at cofinally many cutoff stages. -/
theorem denseSource_discrepancy_of_not_strongOperatorConverges
    (Tn : ∀ n, Hn n →L[K] Gn n) (T : H →L[K] G)
    (D : Set H) (hD : Dense D)
    (source : H → ∀ n, Hn n)
    (hsource : ∀ d ∈ D, J.StronglyConverges (source d) d)
    (C : ℝ) (hC : 0 ≤ C)
    (hLip : ∀ n (x y : Hn n),
      dist (L.embedding n (Tn n x)) (L.embedding n (Tn n y)) ≤
        C * dist (J.embedding n x) (J.embedding n y))
    (hfail : ¬ J.StrongOperatorConverges L Tn T) :
    ∃ d ∈ D, ∃ ε > 0, ∀ N, ∃ n ≥ N,
      ε ≤ dist (L.embedding n (Tn n (source d n))) (T d) := by
  obtain ⟨d, hdD, hd⟩ := exists_bad_dense_source_of_not_strongOperatorConverges
    J L Tn T D hD source hsource C hC hLip hfail
  obtain ⟨ε, hε, hlate⟩ := exists_cofinal_discrepancy_of_not_tendsto
    (fun n ↦ L.embedding n (Tn n (source d n))) (T d) hd
  exact ⟨d, hdD, ε, hε, hlate⟩

end NCG.VaryingHilbert.System
