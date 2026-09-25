/-
Copyright (c) 2026 Aurélien Pélissier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aurélien Pélissier
-/
import Mathlib
import RenewalGeometry.Action.AcceptedBregmanStationarityExact

/-!
# Cutoff-aware stationarity on the determining test core
  (`prop:supp-physical-test-stationarity`, `eq:main-test-lift-budget`,
  `eq:main-physical-stationarity`, `eq:supp-scaled-test-gap`;
  emergent-spacetime manuscript)

Three layers, matching the three claims of the proposition.

1. **The quantitative physical-test estimate** `eq:main-physical-stationarity`
   at one cutoff (`BregmanStationarity.physical_test_stationarity`).  On the
   determining-field chart `E` of `AcceptedBregmanStationarityExact` (Fisher
   potential `Ψ`, common action `𝒜`, accepted kernel `K` with stationary law
   `ν`), let `G θ` be the positive Gram of the chart with `G ⪰ m I`, and let
   `v θ = v_{X,K}(k; θ)` be the represented lift of a fixed physical test with
   the budget `‖v θ‖²_{G θ} ≤ B²` (`eq:main-test-lift-budget`, the supremum
   over the support encoded as a bound at every field value).  Then
   `𝔼_ν |δ𝒜[v]|² = ∫ ⟪∇𝒜 θ, v θ⟫² dν ≤ B² C_X Δ̄_Ψ` with the boxed constant
   `C_X = C_{Ψ,𝒜,η}` of `integral_stationarity_form_le`: duality for the
   positive `G` pairing (`|⟪∇𝒜, v⟫|² ≤ ‖∇𝒜‖²_{G⁻¹} ‖v‖²_G ≤ m⁻¹‖∇𝒜‖² B²`)
   followed by `thm:supp-action-stationarity`.
2. **Mean-square convergence** on a countable determining core
   (`tendsto_meanSquare_of_scaled_gap`): if `B_{X,K}(k)² C_X Δ̄_{Ψ,X} → 0`
   (`eq:supp-scaled-test-gap`) for each core test, the mean squares of the
   first variations tend to zero.
3. **The almost-sure diagonal subsequence under a common coupling**
   (`exists_subseq_ae_tendsto_of_meanSquare`,
   `exists_subseq_ae_tendsto_of_integral_sq_le`): on one measure space
   carrying all cutoff variables `Y X m` (cutoff `X`, core test `m`) with
   second moments dominated by `b X m → 0`, there is a strictly increasing
   sequence of cutoffs `φ` along which, almost surely, every `Y (φ j) m → 0`.
   The proof is the manuscript's: choose `φ j` with `b (φ j) m ≤ 2⁻ʲ` for
   `m ≤ j`, sum the expected squared residuals (Tonelli:
   `lintegral_tsum`), conclude the sum is finite almost surely
   (`ae_lt_top'`), so the residuals tend to zero, and intersect over the
   countable core (`ae_all_iff`).  No independence between cutoffs is used.

`physical_test_stationarity_core` bundles (2) and (3).  Not formalised (a
remark in the manuscript's proof, not part of the statement): the extension
from the core to all determining tests by uniform continuity.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped RealInnerProductSpace ENNReal

namespace RenewalGeometry

/-! ## Layer 1: the physical-test estimate at one cutoff -/

namespace BregmanStationarity

variable {E : Type} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- Duality for the positive `G` pairing: with `G ⪰ m I` and the budget
`⟪v, G v⟫ ≤ b`, `|⟪g, v⟫|² ≤ m⁻¹ ‖g‖² b`. -/
theorem inner_sq_le_of_gram_budget {m b : ℝ} (hm : 0 < m)
    (G : E →L[ℝ] E) (hG : ∀ x, m * ‖x‖ ^ 2 ≤ ⟪x, G x⟫)
    (g v : E) (hv : ⟪v, G v⟫ ≤ b) :
    ⟪g, v⟫ ^ 2 ≤ m⁻¹ * ‖g‖ ^ 2 * b := by
  have h1 : ⟪g, v⟫ ^ 2 ≤ ‖g‖ ^ 2 * ‖v‖ ^ 2 := by
    have := abs_real_inner_le_norm g v
    have h0 : 0 ≤ ‖g‖ * ‖v‖ := by positivity
    calc ⟪g, v⟫ ^ 2 = |⟪g, v⟫| ^ 2 := (sq_abs _).symm
      _ ≤ (‖g‖ * ‖v‖) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
      _ = ‖g‖ ^ 2 * ‖v‖ ^ 2 := by ring
  have h2 : ‖v‖ ^ 2 ≤ m⁻¹ * b := by
    have := hG v
    rw [le_inv_mul_iff₀ hm]
    linarith
  calc ⟪g, v⟫ ^ 2 ≤ ‖g‖ ^ 2 * ‖v‖ ^ 2 := h1
    _ ≤ ‖g‖ ^ 2 * (m⁻¹ * b) := mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
    _ = m⁻¹ * ‖g‖ ^ 2 * b := by ring

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {Ψ 𝒜 : E → ℝ} {gΨ g𝒜 : E → E} {η m M L lam : ℝ}
  {ystar : E → E} {K : Kernel E E} {ν : Measure E}
  [IsProbabilityMeasure ν] [IsMarkovKernel K]

/-- **`eq:main-physical-stationarity`** (`prop:supp-physical-test-stationarity`,
first claim).  Under the chart hypotheses of `thm:supp-action-stationarity`
(`integral_stationarity_form_le`), with the positive chart Gram `G ⪰ m I`
and a represented test lift `v` with budget `⟪v θ, G θ (v θ)⟫ ≤ B²`
(`eq:main-test-lift-budget`, `b = B²`), the mean square of the represented
first variation `δ𝒜[v] = ⟪∇𝒜 θ, v θ⟫` is bounded by `b · C_X · Δ̄_Ψ`. -/
theorem physical_test_stationarity
    (hΨg : ∀ x, HasGradientAt Ψ (gΨ x) x)
    (hΨgc : Continuous gΨ)
    (h𝒜g : ∀ x, HasGradientAt 𝒜 (g𝒜 x) x)
    (h𝒜gc : Continuous g𝒜)
    (hη : 0 < η) (hm : 0 < m) (hM : 0 < M) (hL : 0 ≤ L)
    (hlam : 0 ≤ lam)
    (hΨlo : ∀ a b : E,
      m * ‖a - b‖ ^ 2 ≤ ⟪gΨ a - gΨ b, a - b⟫)
    (hΨup : ∀ a b : E,
      ⟪gΨ a - gΨ b, a - b⟫ ≤ M * ‖a - b‖ ^ 2)
    (hΨlip : ∀ a b : E, ‖gΨ a - gΨ b‖ ≤ M * ‖a - b‖)
    (h𝒜up : ∀ a b : E, ⟪g𝒜 a - g𝒜 b, a - b⟫
      ≤ L * ⟪gΨ a - gΨ b, a - b⟫)
    (h𝒜lip : ∀ a b : E,
      ‖g𝒜 a - g𝒜 b‖ ≤ max lam L * M * ‖a - b‖)
    (hmin : ∀ θ z, prox Ψ 𝒜 gΨ η θ (ystar θ)
      ≤ prox Ψ 𝒜 gΨ η θ z)
    (hstat : K ∘ₘ ν = ν)
    (hi𝒜 : Integrable 𝒜 ν)
    (higap : Integrable (fun p : E × E =>
      gap Ψ 𝒜 gΨ η ystar p.1 p.2) (ν ⊗ₘ K))
    -- the positive chart Gram `G_X(θ) ⪰ m I`
    (G : E → E →L[ℝ] E) (hG : ∀ θ x, m * ‖x‖ ^ 2 ≤ ⟪x, G θ x⟫)
    -- the represented test lift and its budget `B_{X,K}(k)² = b`
    (v : E → E) (hv : AEStronglyMeasurable (fun θ => ⟪g𝒜 θ, v θ⟫) ν)
    {b : ℝ} (hb : 0 < b) (hbudget : ∀ θ, ⟪v θ, G θ (v θ)⟫ ≤ b) :
    ∫ θ, ⟪g𝒜 θ, v θ⟫ ^ 2 ∂ν
      ≤ b * ((4 * ((η⁻¹ + L) * M) / m
          + 4 * M ^ 2 * (1 + η * max lam L) ^ 2
            / (m ^ 2 * η))
        * ∫ p, gap Ψ 𝒜 gΨ η ystar p.1 p.2
            ∂(ν ⊗ₘ K)) := by
  set S : E → ℝ := fun θ => b⁻¹ * ⟪g𝒜 θ, v θ⟫ ^ 2 with hS
  have hS0 : ∀ θ, 0 ≤ S θ := fun θ => by
    simp only [hS]; positivity
  have hSle : ∀ θ, S θ ≤ m⁻¹ * ‖g𝒜 θ‖ ^ 2 := by
    intro θ
    simp only [hS]
    have h := inner_sq_le_of_gram_budget hm (G θ) (hG θ) (g𝒜 θ) (v θ) (hbudget θ)
    calc b⁻¹ * ⟪g𝒜 θ, v θ⟫ ^ 2 ≤ b⁻¹ * (m⁻¹ * ‖g𝒜 θ‖ ^ 2 * b) :=
          mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hb.le)
      _ = m⁻¹ * ‖g𝒜 θ‖ ^ 2 := by field_simp
  have hSm : AEStronglyMeasurable S ν :=
    ((hv.aemeasurable.pow_const 2).const_mul b⁻¹).aestronglyMeasurable
  have hbase := integral_stationarity_form_le hΨg hΨgc h𝒜g h𝒜gc hη hm hM hL hlam hΨlo hΨup
    hΨlip h𝒜up h𝒜lip hmin hstat hi𝒜 higap S hS0 hSle hSm
  have hint : ∫ θ, ⟪g𝒜 θ, v θ⟫ ^ 2 ∂ν = b * ∫ θ, S θ ∂ν := by
    rw [← integral_const_mul]
    congr 1
    funext θ
    simp only [hS]
    field_simp
  rw [hint]
  exact mul_le_mul_of_nonneg_left hbase hb.le

end BregmanStationarity

/-! ## Layer 2: mean-square convergence on the core -/

/-- `prop:supp-physical-test-stationarity`, second claim: if the mean squares
`E X m` of the represented first variations are dominated by the scaled
test gaps `b X m = B_{X,K}(k_m)² C_X Δ̄_{Ψ,X}` and these tend to zero along
the cutoffs (`eq:supp-scaled-test-gap`), the first variations converge to
zero in mean square for every core test `m`. -/
theorem tendsto_meanSquare_of_scaled_gap {ι κ : Type*} {l : Filter ι}
    (E b : ι → κ → ℝ) (hE0 : ∀ X m, 0 ≤ E X m) (hEb : ∀ X m, E X m ≤ b X m)
    (hb : ∀ m, Tendsto (fun X => b X m) l (𝓝 0)) :
    ∀ m, Tendsto (fun X => E X m) l (𝓝 0) := fun m =>
  squeeze_zero (fun X => hE0 X m) (fun X => hEb X m) (hb m)

/-! ## Layer 3: the almost-sure diagonal subsequence -/

/-- Diagonal selection of cutoffs: if `b X m → 0` as `X → ∞` for every core
index `m`, there is a strictly increasing sequence of cutoffs `φ` with
`b (φ j) m ≤ (1/2)^j` for all `m ≤ j`. -/
theorem exists_strictMono_diagonal (b : ℕ → ℕ → ℝ)
    (hb : ∀ m, Tendsto (fun X => b X m) atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ j m, m ≤ j → b (φ j) m ≤ (1 / 2 : ℝ) ^ j := by
  have hN : ∀ j : ℕ, ∃ N : ℕ, ∀ X, N ≤ X → ∀ m ∈ Finset.range (j + 1),
      b X m ≤ (1 / 2 : ℝ) ^ j := by
    intro j
    have hpos : (0 : ℝ) < (1 / 2) ^ j := by positivity
    have hev : ∀ᶠ X in atTop, ∀ m ∈ Finset.range (j + 1), b X m ≤ (1 / 2 : ℝ) ^ j := by
      rw [Filter.eventually_all_finset]
      intro m _
      exact (hb m).eventually (eventually_le_nhds hpos)
    exact Filter.eventually_atTop.mp hev
  choose N hNspec using hN
  let φ : ℕ → ℕ := fun j => Nat.rec (N 0) (fun k φk => max (φk + 1) (N (k + 1))) j
  have hφ0 : φ 0 = N 0 := rfl
  have hφsucc : ∀ k, φ (k + 1) = max (φ k + 1) (N (k + 1)) := fun k => rfl
  have hmono : StrictMono φ := by
    apply strictMono_nat_of_lt_succ
    intro k
    rw [hφsucc]
    exact lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_left _ _)
  have hφN : ∀ j, N j ≤ φ j := by
    intro j
    cases j with
    | zero => rw [hφ0]
    | succ k => rw [hφsucc]; exact le_max_right _ _
  refine ⟨φ, hmono, fun j m hm => ?_⟩
  exact hNspec j (φ j) (hφN j) m (Finset.mem_range.mpr (Nat.lt_succ_of_le hm))

/-- A real sequence whose squares, viewed in `ℝ≥0∞`, tend to zero tends to
zero. -/
theorem tendsto_zero_of_tendsto_ofReal_sq (y : ℕ → ℝ)
    (h : Tendsto (fun j => ENNReal.ofReal (y j ^ 2)) atTop (𝓝 0)) :
    Tendsto y atTop (𝓝 0) := by
  have h1 : Tendsto (fun j => (ENNReal.ofReal (y j ^ 2)).toReal) atTop (𝓝 ((0 : ℝ≥0∞).toReal)) :=
    (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  have h2 : Tendsto (fun j => y j ^ 2) atTop (𝓝 0) := by
    simp only [ENNReal.toReal_zero] at h1
    refine h1.congr fun j => ?_
    exact ENNReal.toReal_ofReal (sq_nonneg _)
  have h3 : Tendsto (fun j => Real.sqrt (y j ^ 2)) atTop (𝓝 (Real.sqrt 0)) :=
    (Real.continuous_sqrt.tendsto 0).comp h2
  rw [Real.sqrt_zero] at h3
  rw [tendsto_zero_iff_abs_tendsto_zero]
  refine h3.congr fun j => ?_
  exact Real.sqrt_sq_eq_abs _

/-- **`prop:supp-physical-test-stationarity`, third claim** (common coupling):
on one measure space `Ω` carrying the represented first variations `Y X m`
of every cutoff `X` and core test `m`, if the expected squared residuals are
dominated by `b X m` with `b X m → 0` for each `m`, there is a deterministic
strictly increasing sequence of cutoffs `φ` along which, almost surely,
every core first variation `Y (φ j) m` tends to zero.  No independence
between cutoffs is used. -/
theorem exists_subseq_ae_tendsto_of_meanSquare {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Y : ℕ → ℕ → Ω → ℝ) (hY : ∀ X m, AEMeasurable (Y X m) μ)
    (b : ℕ → ℕ → ℝ)
    (hb : ∀ X m, ∫⁻ ω, ENNReal.ofReal (Y X m ω ^ 2) ∂μ ≤ ENNReal.ofReal (b X m))
    (hlim : ∀ m, Tendsto (fun X => b X m) atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ᵐ ω ∂μ, ∀ m, Tendsto (fun j => Y (φ j) m ω) atTop (𝓝 0) := by
  obtain ⟨φ, hφ, hdiag⟩ := exists_strictMono_diagonal b hlim
  refine ⟨φ, hφ, ?_⟩
  rw [ae_all_iff]
  intro m
  -- the shifted sequence `j ↦ Y (φ (j + m)) m` has summable second moments
  set f : ℕ → Ω → ℝ≥0∞ := fun j ω => ENNReal.ofReal (Y (φ (j + m)) m ω ^ 2) with hf
  have hfm : ∀ j, AEMeasurable (f j) μ := fun j =>
    ENNReal.measurable_ofReal.comp_aemeasurable ((hY _ _).pow_const 2)
  have hgeom : Summable (fun j : ℕ => (1 / 2 : ℝ) ^ j) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hsum : ∫⁻ ω, ∑' j, f j ω ∂μ ≠ ∞ := by
    rw [lintegral_tsum hfm]
    have hle : ∑' j, ∫⁻ ω, f j ω ∂μ ≤ ∑' j, ENNReal.ofReal ((1 / 2 : ℝ) ^ j) := by
      refine ENNReal.tsum_le_tsum fun j => ?_
      refine (hb _ _).trans (ENNReal.ofReal_le_ofReal ?_)
      refine (hdiag (j + m) m (Nat.le_add_left m j)).trans ?_
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_add_right j m)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) hgeom] at hle
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  have hae : ∀ᵐ ω ∂μ, ∑' j, f j ω < ∞ :=
    ae_lt_top' (AEMeasurable.tsum hfm) hsum
  filter_upwards [hae] with ω hω
  have h1 : Tendsto (fun j => f j ω) atTop (𝓝 0) :=
    ENNReal.tendsto_atTop_zero_of_tsum_ne_top hω.ne
  have h2 : Tendsto (fun j => Y (φ (j + m)) m ω) atTop (𝓝 0) :=
    tendsto_zero_of_tendsto_ofReal_sq _ h1
  exact (tendsto_add_atTop_iff_nat m).mp h2

/-- The Bochner-integral form of the almost-sure diagonal subsequence: the
mean-square bounds `∫ (Y X m)² dμ ≤ b X m` of `eq:main-physical-stationarity`
(with integrable squares) give the deterministic subsequence of cutoffs. -/
theorem exists_subseq_ae_tendsto_of_integral_sq_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Y : ℕ → ℕ → Ω → ℝ)
    (hY : ∀ X m, Integrable (fun ω => Y X m ω ^ 2) μ)
    (hYm : ∀ X m, AEMeasurable (Y X m) μ)
    (b : ℕ → ℕ → ℝ) (hb : ∀ X m, ∫ ω, Y X m ω ^ 2 ∂μ ≤ b X m)
    (hlim : ∀ m, Tendsto (fun X => b X m) atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ᵐ ω ∂μ, ∀ m, Tendsto (fun j => Y (φ j) m ω) atTop (𝓝 0) := by
  refine exists_subseq_ae_tendsto_of_meanSquare μ Y hYm b (fun X m => ?_) hlim
  rw [← ofReal_integral_eq_lintegral_ofReal (hY X m)
    (Filter.Eventually.of_forall fun ω => sq_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (hb X m)

/-- `prop:supp-physical-test-stationarity`, claims two and three bundled: on
a common coupling `(Ω, μ)` of the cutoffs, mean-square bounds
`∫ (Y X m)² dμ ≤ b X m` by the scaled test gaps `b X m → 0`
(`eq:supp-scaled-test-gap`) give mean-square convergence of every core first
variation and a deterministic subsequence of cutoffs along which all of them
vanish almost surely. -/
theorem physical_test_stationarity_core {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Y : ℕ → ℕ → Ω → ℝ)
    (hY : ∀ X m, Integrable (fun ω => Y X m ω ^ 2) μ)
    (hYm : ∀ X m, AEMeasurable (Y X m) μ)
    (b : ℕ → ℕ → ℝ) (hb : ∀ X m, ∫ ω, Y X m ω ^ 2 ∂μ ≤ b X m)
    (hlim : ∀ m, Tendsto (fun X => b X m) atTop (𝓝 0)) :
    (∀ m, Tendsto (fun X => ∫ ω, Y X m ω ^ 2 ∂μ) atTop (𝓝 0)) ∧
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ᵐ ω ∂μ, ∀ m, Tendsto (fun j => Y (φ j) m ω) atTop (𝓝 0) :=
  ⟨tendsto_meanSquare_of_scaled_gap (fun X m => ∫ ω, Y X m ω ^ 2 ∂μ) b
      (fun _ _ => integral_nonneg fun _ => sq_nonneg _) hb hlim,
    exists_subseq_ae_tendsto_of_integral_sq_le μ Y hY hYm b hb hlim⟩

end RenewalGeometry
