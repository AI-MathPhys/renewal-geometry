/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib

/-!
# Transported-screen version of connection compactness
(`prop:supp-connection-screens`, emergent-spacetime manuscript)

Let `Ω_X ∈ L²(0,T;𝓗)` be uniformly bounded, let `P_{X,R}` and `P_R` be time-independent
operators on `𝓗` (acting pointwise in time on `L²(0,T;𝓗)`, `ContinuousLinearMap.compLp`)
with `‖P_{X,R} - P_R‖_op → 0` as `X → ∞` for every `R`, with uniformly vanishing screen
tails (`eq:supp-connection-screen-tail`), and such that the coefficients of `P_R Ω_X` in a
fixed finite family of vectors spanning the range form a relatively compact family in
`L²(0,T)`.  Then `{Ω_X}` is relatively compact in `L²(0,T;𝓗)`.

* `TransportedScreenCompactness.totallyBounded_of_totallyBounded_approx` — a set uniformly
  approximable to every accuracy by totally bounded sets is totally bounded.
* `TransportedScreenCompactness.totallyBounded_range_of_screens` — the abstract mechanism:
  screen differences vanishing outside finitely many indices, uniformly small tails and
  totally bounded screened families.
* `TransportedScreenCompactness.compLp_sub_norm_le` — time-independent operators act on
  `Lp` with the operator-norm bound for differences.
* `TransportedScreenCompactness.totallyBounded_of_coefficients` — relatively compact
  coefficients in a fixed finite family of vectors make the reconstructed family totally
  bounded.
* `TransportedScreenCompactness.transportedScreen_relativelyCompact` — the proposition on
  `Lp 𝓗 p μ` for any measure and `1 ≤ p`, indices `X` in any type with the cofinite filter;
  `TransportedScreenCompactness.connectionScreens_L2` — the manuscript's case
  `L²(0,T;𝓗)`, `𝓗` a Hilbert space, cutoffs `X ∈ ℕ` tending to infinity.
-/

open Filter Topology MeasureTheory

noncomputable section

namespace RenewalGeometry

namespace TransportedScreenCompactness

/-- A set uniformly approximable to every accuracy by totally bounded sets is totally
bounded. -/
theorem totallyBounded_of_totallyBounded_approx {E : Type*} [PseudoMetricSpace E] {U : Set E}
    (happrox : ∀ ε > 0, ∃ C : Set E, TotallyBounded C ∧ ∀ y ∈ U, ∃ z ∈ C, dist y z < ε) :
    TotallyBounded U := by
  rw [Metric.totallyBounded_iff]
  intro ε hε
  obtain ⟨C, hC, hUC⟩ := happrox (ε / 2) (by positivity)
  obtain ⟨t, ht, hcover⟩ := Metric.totallyBounded_iff.mp hC (ε / 2) (by positivity)
  refine ⟨t, ht, ?_⟩
  intro y hy
  obtain ⟨c, hcC, hyc⟩ := hUC y hy
  obtain ⟨z, hzt, hcz⟩ : ∃ z ∈ t, dist c z < ε / 2 := by
    simpa only [Set.mem_iUnion, exists_prop, Metric.mem_ball] using hcover hcC
  refine Set.mem_iUnion.2 ⟨z, Set.mem_iUnion.2 ⟨hzt, ?_⟩⟩
  rw [Metric.mem_ball]
  calc
    dist y z ≤ dist y c + dist c z := dist_triangle y c z
    _ < ε / 2 + ε / 2 := add_lt_add hyc hcz
    _ = ε := by ring

/-- The abstract transported-screen mechanism: if, for every screen level `R`, the screen
differences `Q_{X,R} Ω_X - Q_R Ω_X` are small outside finitely many indices, the screen tails
`Ω_X - Q_{X,R} Ω_X` are uniformly small for some `R`, and every screened family
`{Q_R Ω_X}_X` is totally bounded, then `{Ω_X}` is totally bounded. -/
theorem totallyBounded_range_of_screens {ι E : Type*} [SeminormedAddCommGroup E]
    (Ω : ι → E) (Q : ι → ℕ → E → E) (Q0 : ℕ → E → E)
    (hdiff : ∀ R, ∀ ε > 0, ∀ᶠ X in cofinite, ‖Q X R (Ω X) - Q0 R (Ω X)‖ < ε)
    (htail : ∀ ε > 0, ∃ R, ∀ X, ‖Ω X - Q X R (Ω X)‖ < ε)
    (hscreen : ∀ R, TotallyBounded (Set.range fun X => Q0 R (Ω X))) :
    TotallyBounded (Set.range Ω) := by
  apply totallyBounded_of_totallyBounded_approx
  intro ε hε
  obtain ⟨R, hR⟩ := htail (ε / 2) (by positivity)
  have hS : {X | ¬ ‖Q X R (Ω X) - Q0 R (Ω X)‖ < ε / 2}.Finite :=
    Filter.eventually_cofinite.mp (hdiff R (ε / 2) (by positivity))
  refine ⟨(Set.range fun X => Q0 R (Ω X)) ∪ Ω '' {X | ¬ ‖Q X R (Ω X) - Q0 R (Ω X)‖ < ε / 2},
    (hscreen R).union (hS.image Ω).totallyBounded, ?_⟩
  rintro _ ⟨X, rfl⟩
  by_cases hX : ‖Q X R (Ω X) - Q0 R (Ω X)‖ < ε / 2
  · refine ⟨Q0 R (Ω X), Or.inl ⟨X, rfl⟩, ?_⟩
    rw [dist_eq_norm]
    calc
      ‖Ω X - Q0 R (Ω X)‖ ≤ ‖Ω X - Q X R (Ω X)‖ + ‖Q X R (Ω X) - Q0 R (Ω X)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add (hR X) hX
      _ = ε := by ring
  · exact ⟨Ω X, Or.inr ⟨X, hX, rfl⟩, by simpa using hε⟩

section Lp

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ENNReal} [Fact (1 ≤ p)]
variable {𝕜 : Type*} [RCLike 𝕜] {H : Type*} [NormedAddCommGroup H] [NormedSpace 𝕜 H]

omit [Fact (1 ≤ p)] in
/-- Time-independent operators act on `Lp` with the operator-norm bound for differences. -/
theorem compLp_sub_norm_le (P P0 : H →L[𝕜] H) (f : Lp H p μ) :
    ‖P.compLp f - P0.compLp f‖ ≤ ‖P - P0‖ * ‖f‖ := by
  have h := ContinuousLinearMap.add_compLp (μ := μ) (p := p) P0 (P - P0) f
  rw [add_sub_cancel] at h
  rw [h, add_sub_cancel_left]
  exact ContinuousLinearMap.norm_compLp_le _ _

/-- Relatively compact coefficient families in a fixed finite family of vectors make the
reconstructed family `∑ᵢ cᵢ(X) eᵢ` totally bounded. -/
theorem totallyBounded_of_coefficients {ι : Type*} {n : ℕ} (e : Fin n → H)
    (c : ι → Fin n → Lp 𝕜 p μ) (F : ι → Lp H p μ)
    (hrec : ∀ X, F X = ∑ i, (ContinuousLinearMap.toSpanSingleton 𝕜 (e i)).compLp (c X i))
    (hc : ∀ i, IsCompact (closure (Set.range fun X => c X i))) :
    TotallyBounded (Set.range F) := by
  let K : Set (Fin n → Lp 𝕜 p μ) := Set.univ.pi fun i => closure (Set.range fun X => c X i)
  have hK : IsCompact K := isCompact_univ_pi hc
  let Φ : (Fin n → Lp 𝕜 p μ) → Lp H p μ := fun v =>
    ∑ i, (ContinuousLinearMap.toSpanSingleton 𝕜 (e i)).compLpL p μ (v i)
  have hΦ : Continuous Φ :=
    continuous_finsetSum _ fun i _ =>
      ((ContinuousLinearMap.toSpanSingleton 𝕜 (e i)).compLpL p μ).continuous.comp
        (continuous_apply i)
  refine (hK.image hΦ).totallyBounded.subset ?_
  rintro _ ⟨X, rfl⟩
  refine ⟨c X, fun i _ => subset_closure ⟨X, rfl⟩, ?_⟩
  rw [hrec X]
  rfl

/-- **`prop:supp-connection-screens`** on `Lp 𝓗 p μ`.  Let `Ω_X` be uniformly bounded, let
`P_{X,R}`, `P_R` be time-independent operators on `𝓗` with `‖P_{X,R} - P_R‖_op → 0` as
`X → ∞` (cofinite filter) for every `R`, let the screen tails
`‖(I - P_{X,R}) Ω_X‖` tend to `0` uniformly in `X` as `R → ∞`
(`eq:supp-connection-screen-tail`), and let `P_R Ω_X = ∑ᵢ cᵢ(R,X) eᵢ(R)` with each coefficient
family `{cᵢ(R,X)}_X` relatively compact in `Lp 𝕜 p μ`.  Then `{Ω_X}` is relatively compact. -/
theorem transportedScreen_relativelyCompact [CompleteSpace H] {ι : Type*}
    (Ω : ι → Lp H p μ) (B : ℝ) (hB : ∀ X, ‖Ω X‖ ≤ B)
    (P : ι → ℕ → H →L[𝕜] H) (P0 : ℕ → H →L[𝕜] H)
    (hop : ∀ R, Tendsto (fun X => ‖P X R - P0 R‖) cofinite (𝓝 0))
    (htail : ∀ ε > 0, ∀ᶠ R in atTop, ∀ X, ‖Ω X - (P X R).compLp (Ω X)‖ < ε)
    (n : ℕ → ℕ) (e : ∀ R, Fin (n R) → H) (c : ∀ R, ι → Fin (n R) → Lp 𝕜 p μ)
    (hrec : ∀ R X, (P0 R).compLp (Ω X)
      = ∑ i, (ContinuousLinearMap.toSpanSingleton 𝕜 (e R i)).compLp (c R X i))
    (hc : ∀ R i, IsCompact (closure (Set.range fun X => c R X i))) :
    IsCompact (closure (Set.range Ω)) := by
  have htb : TotallyBounded (Set.range Ω) := by
    refine totallyBounded_range_of_screens Ω (fun X R f => (P X R).compLp f)
      (fun R f => (P0 R).compLp f) ?_ ?_ ?_
    · intro R ε hε
      set B' : ℝ := max B 0 + 1 with hB'
      have hB'pos : 0 < B' := by positivity
      have hδ : (0 : ℝ) < ε / B' := div_pos hε hB'pos
      filter_upwards [(hop R).eventually (eventually_lt_nhds hδ)] with X hX
      calc
        ‖(P X R).compLp (Ω X) - (P0 R).compLp (Ω X)‖ ≤ ‖P X R - P0 R‖ * ‖Ω X‖ :=
          compLp_sub_norm_le _ _ _
        _ ≤ ‖P X R - P0 R‖ * B' := by
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          linarith [hB X, le_max_left B 0]
        _ < ε / B' * B' := mul_lt_mul_of_pos_right hX hB'pos
        _ = ε := div_mul_cancel₀ ε hB'pos.ne'
    · intro ε hε
      exact (htail ε hε).exists
    · intro R
      exact totallyBounded_of_coefficients (e R) (c R) _ (hrec R) (hc R)
  exact htb.closure.isCompact_of_isClosed isClosed_closure

/-- **`prop:supp-connection-screens`**, the manuscript's setting: `L²(0,T;𝓗)` with `𝓗` a
Hilbert space, cutoffs `X ∈ ℕ` tending to infinity, coefficients in `L²(0,T)`. -/
theorem connectionScreens_L2 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    [CompleteSpace H] (T : ℝ)
    (Ω : ℕ → Lp H 2 (volume.restrict (Set.Ioc (0 : ℝ) T))) (B : ℝ) (hB : ∀ X, ‖Ω X‖ ≤ B)
    (P : ℕ → ℕ → H →L[𝕜] H) (P0 : ℕ → H →L[𝕜] H)
    (hop : ∀ R, Tendsto (fun X => ‖P X R - P0 R‖) atTop (𝓝 0))
    (htail : ∀ ε > 0, ∀ᶠ R in atTop, ∀ X, ‖Ω X - (P X R).compLp (Ω X)‖ < ε)
    (n : ℕ → ℕ) (e : ∀ R, Fin (n R) → H)
    (c : ∀ R, ℕ → Fin (n R) → Lp 𝕜 2 (volume.restrict (Set.Ioc (0 : ℝ) T)))
    (hrec : ∀ R X, (P0 R).compLp (Ω X)
      = ∑ i, (ContinuousLinearMap.toSpanSingleton 𝕜 (e R i)).compLp (c R X i))
    (hc : ∀ R i, IsCompact (closure (Set.range fun X => c R X i))) :
    IsCompact (closure (Set.range Ω)) := by
  refine transportedScreen_relativelyCompact Ω B hB P P0 ?_ htail n e c hrec hc
  intro R
  rw [Nat.cofinite_eq_atTop]
  exact hop R

end Lp

end TransportedScreenCompactness

end RenewalGeometry
